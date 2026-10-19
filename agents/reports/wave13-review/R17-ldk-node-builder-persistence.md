# R17 — LDK Node builder, config, persistence, data store, and restart
**Status:** read-only review
**Pins:** LDK Node `fa123fed131e27ecc420b77fa7086fcf1ddaebb8`, LDK Server `c17dc11dde38f88c53457039ddf30c6b90a63ba2`

All LDK paths in this report are relative to `/tmp/opencode/ldk-refs/` unless written out in full.

## 1. Scope and current Lean surface

This lane asks what the Lean tree actually proves about LDK Node's builder/load
policy, configuration gates, persisted state, data-store publication order, and
restart. It does not propose a Rust/Lean refinement or a crash-atomic filesystem
model.

The current Lean persistence surface is **one root-imported but uncatalogued
module**:

- `LnLean/Proofs/PhaseC3/PersistenceRecovery.lean` is imported by
  `LnLean.lean:134` and `LnLean/Proofs/All.lean:29`.
- It is **not** one of the 51 catalog rows in `docs/THEOREM-INDEX.md` (51
  `LN-*` rows counted) and has no row in `docs/TRACEABILITY.md` (also 51 rows).
  The closest catalog row is `LN-PR-005` at `docs/THEOREM-INDEX.md:66` and
  `docs/TRACEABILITY.md:45`, which covers
  `LnLean.Protocol.Peer.reestablish_no_rollback`, not persistence recovery.
- It is **not** in `AxiomAudit.auditedTheorems`: the list begins at
  `LnLean/Proofs/PhaseC3/AxiomAudit.lean:579` and has 435 entries
  (`AxiomAudit.lean:1018`); a search for `PersistenceRecovery` in that file
  returns no match.
- The only prose claim I found is `docs/PHASE-C3-LANES.md:23`:
  “persisted channel recovery preserves counters and ready state.”
- The catalog-gate counts are from `docs/OPEN-ISSUES.md:18-20`:
  51/51 rows proved, 294 targets, 435 audited theorems. Those counts do not
  imply persistence coverage.

The actual Lean claim surface is narrow:

| Area | Lean declaration | What it really says |
|---|---|---|
| Persisted projection | `Persisted` at `PersistenceRecovery.lean:118-126` | only `localCommitmentNumber`, `remoteCommitmentNumber`, `htlcs`, and `ready : Bool` |
| Projection/restore | `Persisted.ofChannelRecord` at `:132-136`; `Snapshot` at `:155-159`; `restoreChannel` at `:185-189`; `restoreRecord` at `:196-197` | restore overwrites counters/HTLCs, but leaves phase, balances, endpoints, funding data, and other live fields alone; `ready` is only enough to keep or drop a live message |
| Consistency | `Consistent` at `:202-203` | equality with the projection of a particular live channel/record pair |
| Replay | `applyMsg` at `:305-314`; `replay` at `:317-318`; `restore_replay_suffix` at `:395-399` | only four message families have a persisted effect: `commitment_signed`, `revoke_and_ack`, `channelReady`, and the three HTLC messages |
| Recovery point | `RecoveryPoint` at `:443-448`; `replays_full_history` at `:455-459` | atomic snapshot is a **structure field**, and recovery only replays the suffix over a projection |
| “No rollback” | `recovery_no_rollback_suffix` at `:430-437`; `recovery_no_rollback_committed` at `:495-503`; `recovery_no_rollback_reestablish` at `:577-585` | these are monotonicity results over reachable states/inbox replay, not general proofs that an older snapshot cannot be restored |
| Staleness | `Stale` at `:506-508`; `stale_snapshot_rolls_back` at `:513-517` | `Stale` names a later reachable state with a larger local counter, but the theorem only returns the witness from `Stale`; it never applies `s.restoreChannel` to that later state |
| Ready retention | `recovery_retains_channelReady` at `:591-598` | assumes the live record already has `lastChannelReady = some m`; the snapshot stores only a Boolean |
| Negative result | `inconsistent_snapshot_rolls_back` at `:618-631` | exhibits an arbitrary inconsistent snapshot with a smaller counter, not a formerly consistent snapshot restored over a later state |
| Conditional lock-in | `ready_snapshot_reaches_normal` at `:661-667` | takes the `ready → phase = awaitingLockin` bridge as an explicit hypothesis |

The module's own “What is NOT modelled” list (`PersistenceRecovery.lean:79-96`)
already excludes crash atomicity, on-disk format/integrity, fsync, watchtowers,
L1 recovery, timers, and retransmission scheduling. That boundary is useful, but
the prose claim at `docs/PHASE-C3-LANES.md:23` and the names
`recovery_no_rollback_committed` / `stale_snapshot_rolls_back` invite a stronger
reading than the declarations support.

## 2. LDK datapoints (with `file:line`)

### 2.1 Builder load policy: missing state and corrupt state are different

LDK Node does not have one global “read or default” policy. The builder maps
stores to different outcomes:

- Missing node metrics become defaults, but any other metrics read error fails:
  `ldk-node/src/builder.rs:1606-1615`.
- Payment, forwarding-stats, pending-payment, channel-tx-facts, and address-pool
  I/O errors fail the build: `builder.rs:1618-1633`, `:1636-1640`,
  `:1918-1929`, `:1932-1947`, `:1950-1955`. The address-pool decoder is the
  exception noted below: it degrades only a decode failure, not an I/O error.
- Channel monitors: `NotFound` becomes an empty monitor set; any other error is
  `BuildError::ReadFailed`: `builder.rs:2024-2033`.
- Network graph: `NotFound` creates a fresh graph; other errors fail:
  `builder.rs:2053-2060`.
- Scorer: `NotFound` creates defaults; other errors fail:
  `builder.rs:2100-2110`. External pathfinding scores ignore `NotFound` and
  fail on other errors: `builder.rs:2115-2126`.
- Channel manager: `NotFound` means “We're starting a fresh node”
  (`builder.rs:2164-2170`, `:2196-2214`), while a present but unreadable
  manager is `BuildError::ReadFailed` (`builder.rs:2189-2193`).
- Event queue and peer store: `NotFound` creates a fresh queue/store; other
  errors fail: `builder.rs:2469-2490`.
- The dedicated regression test
  `channel_manager_read_failure_fails_build` expects `BuildError::ReadFailed`
  rather than a silent fresh node: `builder.rs:2766-2780`.

The observable policy is therefore **fresh only for a missing key or a missing
whole store; fail closed for corrupt/unreadable critical state**. Address-pool
decode is an explicit exception: `read_address_pool` degrades a corrupt record
to an empty pool because it is reconstructible
(`ldk-node/src/wallet/persist.rs:251-276`).

### 2.2 Wallet/network mismatch is a distinct build failure

The wallet loader calls `check_network(config.network)` and maps a loaded
network mismatch to `BuildError::NetworkMismatch`
(`builder.rs:1770-1795`). This is not a generic `ReadFailed`; it is an identity
compatibility check on persisted wallet state.

### 2.3 Config announce gate

`may_announce_channel` requires **both** a node alias and at least one
non-empty listening-address list: `ldk-node/src/config.rs:549-559`. The default
`UserConfig` then disables `announce_for_forwarding` and forces announced-channel
preference when the gate is not met: `config.rs:561-580`. The default storage
directory is `/tmp/ldk_node` (`config.rs:130-131`), but this review treats paths
as configuration data, not as a persistence theorem.

### 2.4 DataStore: per-object persist-before-publish, with in-process reader lock

`DataStore` explicitly documents that writers hold the write guard across the
store write and the subsequent in-memory update, so readers never observe a
store-ahead-of-memory window: `ldk-node/src/data_store.rs:303-309`.
`insert` persists before inserting into the cache (`:347-353`);
`mutate_with` persists before replacing the cached object (`:458-470`).
The failure tests prove memory does not move when persistence fails:
`data_store.rs:1296-1364`. `readers_wait_for_in_flight_writes` blocks a reader
while a write is parked after the store write (`:1047-1085`). This is a useful
**per-object, in-process** ordering contract. It is not a cross-store atomicity
or fsync guarantee.

### 2.5 PeerStore and EventQueue are memory-first, not persist-first

- `PeerStore::add_peer` inserts into the in-memory map, encodes the map, then
  persists: `ldk-node/src/peer_store.rs:45-55`. A failed write therefore leaves
  memory ahead of disk.
- `remove_peer` persists first and removes from memory only after success:
  `peer_store.rs:58-68`.
- `list_peers`/`get_peer` are synchronous and explicitly warn that callers may
  observe changes that are still being persisted: `peer_store.rs:71-85`.
- `EventQueue::add_event` pushes onto the in-memory queue and then persists:
  `ldk-node/src/event.rs:437-449`.
- `event_handled` pops from memory and then persists: `event.rs:461-473`.
  A failed persist therefore leaves memory ahead of disk (or, on a later
  restart, the old event still present).

There is no single global “persist then publish” invariant across the stores in
LDK Node.

### 2.6 Wallet sub-changesets are deliberately non-atomic; address pool is advisory

`KVStoreWalletPersister` writes BDK sub-changesets individually in the order
`indexer`, `tx_graph`, `local_chain`; the comment records that this is
non-atomic and explains the ordering rationale:
`ldk-node/src/wallet/persist.rs:167-196`. The address-pool record is explicitly
advisory, may briefly lead the persisted indexer, and is re-derived after
drops: `wallet/persist.rs:30-35`, `:231-248`. A corrupt address-pool record
degrades to an empty pool rather than failing startup: `:251-276`.

### 2.7 Filesystem and server backends: migration/refusal is outside the Lean model

- The filesystem store auto-migrates v1 to v2 through a temporary directory,
  rename, and parent-directory fsync: `ldk-node/src/io/fs_store.rs:18-60`.
  It also has explicit crash-recovery decisions for an interrupted migration:
  `fs_store.rs:72-102`.
- LDK Server separates network directories
  (`ldk-server/ldk-server/src/main.rs:108-114`), refuses SQLite↔Postgres
  storage migration by detecting the old backend’s file/lock
  (`main.rs:780-809`), and persists a Postgres lock file (`main.rs:811-820`).
- Server entropy is loaded from a mnemonic file or generated once and written
  with restrictive permissions: `ldk-server/ldk-server/src/util/entropy.rs:23-48`.

These are real backend/migration semantics, but not part of the current Lean
projection.

## 3. Gap matrix

| Behavior | Lean status | LDK evidence | Gap / counterexample | Priority |
|---|---|---|---|---|
| Builder distinguishes missing critical state from corrupt critical state | **missing** | `builder.rs:1606-1615`, `:2024-2033`, `:2164-2214`, `:2469-2490`, `:2766-2780` | No builder/load model. `RecoveryPoint` starts from a snapshot already in hand, so it cannot express “missing → fresh” versus “corrupt → fail closed.” | P1 |
| Wallet network mismatch is a distinct build failure | **missing** | `builder.rs:1770-1795` | No persisted wallet/network identity in Lean; no `NetworkMismatch` outcome. | P2 |
| Announce gate requires alias + listening addresses | **missing** | `config.rs:549-559`, `:561-580` | No `Config`/announce model; default user-config policy is not represented. | P2 |
| Persisted snapshot includes counters, HTLCs, and ready Bool only | **partial / lossy** | `PersistenceRecovery.lean:118-126`, `:185-197`; real manager/monitor persistence `builder.rs:2002-2033`, `:2173-2227` | `restoreChannel` leaves balance, phase, endpoints, funding, and keys at “live” values; a snapshot alone cannot reconstruct them. `Persisted` is not an injective image of `Channel`. | P1 |
| Ready Bool retains retransmission | **partial** | `PersistenceRecovery.lean:155-159`, `:196-197`, `:591-598`; `Peer.lean:91-99`, `:105-121` | The theorem keeps a **live** `lastChannelReady` message (`hm`); there are no wire bytes in the snapshot. Two different retained messages project to the same snapshot. | P1 |
| Atomic snapshot / stale snapshot rollback | **partial / misleading** | `PersistenceRecovery.lean:443-448`, `:495-503`, `:506-517`, `:618-631`; `data_store.rs:303-309`, `:347-353` | `RecoveryPoint.consistent` is an explicit assumption, not crash atomicity. `stale_snapshot_rolls_back` only unpacks `Stale.2`; it never shows restoring the stale snapshot over the later state. `recovery_no_rollback_committed` is reachability monotonicity with `Consistent b r`. | P1 |
| Per-object write-then-publish ordering | **missing** | `data_store.rs:303-309`, `:347-353`, `:458-470`, `:1047-1085`, `:1296-1364` | No store semantics in Lean; no theorem that failed persistence leaves memory unchanged or that readers wait for in-flight writes. | P2 |
| Global persist-before-publish across stores | **contradicted by LDK** | `peer_store.rs:45-55`, `:71-85`; `event.rs:437-449`, `:461-473`; `wallet/persist.rs:167-196` | Peer add and event add/handled mutate memory before persistence; wallet sub-changesets are non-atomic. Any model assuming one global atomic publish order would be false. | P1 |
| Restart/on-disk format, fsync, backend migration | **external** | `io/fs_store.rs:18-60`, `:72-102`; `ldk-server/src/main.rs:780-820`; module boundary `PersistenceRecovery.lean:79-96` | Not modelled and not safely derivable from the current projection. FS/Postgres migration, directory fsync, and lock-file policy remain external. | external |
| Wallet/BDK and monitor persistence details | **external** | `wallet/persist.rs:30-35`, `:167-196`; `builder.rs:2002-2033` | BDK changeset ordering and LDK monitor persistence are separate surfaces; R04/R08 own them. R17 should not duplicate them. | external |

The matrix deliberately distinguishes “the Lean theorem is true” from “the Lean
theorem proves the LDK behavior its name suggests.” `recovery_no_rollback_committed`
and `stale_snapshot_rolls_back` are true, but they do not establish the stale
restore case. `inconsistent_snapshot_rolls_back` is a genuine negative result,
but it is not that case either.

## 4. Proposed targets

The first three targets are corrections/negative results in the existing
module and are the safest immediate work. Targets 4–7 require a small new
policy/store module; they should not be mixed into `PersistenceRecovery.lean`
without updating that module's stated scope. Each target is additive; none
requires deleting or weakening an existing theorem.

### T1 — Make stale-snapshot rollback a theorem about restore

- **Lean name:** `LnLean.Proofs.PhaseC3.PersistenceRecovery.stale_snapshot_restore_rolls_back`
- **Statement shape:**
  ```lean
  theorem stale_snapshot_restore_rolls_back
      {s : Snapshot} {c : Channel} {r : ChannelRecord}
      (hs : s.Stale c r) :
      ∃ c', Reachable c c' ∧
        (s.restoreChannel c').localCommitmentNumber <
          c'.localCommitmentNumber
  ```
- **Hypotheses:** `hs : s.Stale c r`. `Stale` already contains
  `s.Consistent c r` and a reachable later `c'` with
  `c'.localCommitmentNumber > s.localCommitmentNumber`
  (`PersistenceRecovery.lean:506-508`).
- **Non-vacuity witness:** take `c := sampleChannel`,
  `s := Snapshot.ofChannelRecord c r`, and
  `c' := { c with localCommitmentNumber := c.localCommitmentNumber + 1 }`.
  `Step.revokeAndAck c (by rfl)` gives `Reachable c c'`
  (`LnLean/Channel/State.lean:111-113`), and `restoreChannel` gives local
  counter `0 < 1`. `sampleChannel` is available at
  `LnLean/Proofs/Protocol/ChannelReestablishProps.lean:508-522`.
- **Why faithful:** it applies `restoreChannel` to the later state, which is
  exactly the operation the current theorem omits. It does not assume the
  snapshot is latest; it proves that a formerly valid but stale snapshot
  actually rolls the later channel back.
- **Fidelity risk:** low. It uses only existing definitions and no new
  durability assumption.
- **Feasibility:** very high; a short proof by unpacking `Stale` and rewriting
  through `Consistent`.
- **Priority:** P1.
- **Model extension / external assumption:** no model extension and no external
  assumption; this is a correction in the existing module. This is the top
  target.

### T2 — Expose that the ready flag cannot reconstruct a ready message

- **Lean name:** `LnLean.Proofs.PhaseC3.PersistenceRecovery.snapshot_ready_projection_not_injective`
- **Statement shape:**
  ```lean
  theorem snapshot_ready_projection_not_injective :
      ∃ (c : Channel) (r₁ r₂ : ChannelRecord) (m₁ m₂ : Msg),
        r₁.lastChannelReady = some m₁ ∧
        r₂.lastChannelReady = some m₂ ∧
        m₁.kind = MsgKind.channelReady ∧
        m₂.kind = MsgKind.channelReady ∧
        m₁ ≠ m₂ ∧
        Snapshot.ofChannelRecord c r₁ = Snapshot.ofChannelRecord c r₂
  ```
- **Hypotheses:** none.
- **Non-vacuity witness:** use the same `sampleChannel`/record, with
  `r₁.lastChannelReady` and `r₂.lastChannelReady` set to two distinct
  `Msg.channelReady` payloads (for example, identical fields except
  `shortChannelIdAlias := none` versus `some 1`). Both project to
  `ready := true`, so the snapshots are equal.
- **Why faithful:** `Snapshot.ready` is a `Bool` and
  `Persisted.ofChannelRecord` sets it from `r.lastChannelReady.isSome`
  (`PersistenceRecovery.lean:132-136`, `:155-159`). `restoreRecord` can only
  keep a **live** message, not recover one (`:196-197`). This target makes the
  live-message hypothesis in `recovery_retains_channelReady` explicit.
- **Fidelity risk:** low, provided the witness uses actual `channelReady`
  messages rather than arbitrary `Msg` constructors. The model's
  `ChannelRecord` does not enforce the message kind, so the statement is only
  as strong as that record; the witness stays within the intended kind.
- **Feasibility:** high; two records and a projection equality.
- **Priority:** P1.
- **Model extension / external assumption:** no model extension and no external
  assumption; this is a negative result in the existing module. It does **not**
  replace `recovery_retains_channelReady`; it explains why that theorem needs
  `hm` and a live record.

### T3 — Expose that the snapshot projection omits balances and phase

- **Lean name:** `LnLean.Proofs.PhaseC3.PersistenceRecovery.snapshot_projection_not_injective_balance`
- **Statement shape:**
  ```lean
  theorem snapshot_projection_not_injective_balance :
      ∃ (c₁ c₂ : Channel) (r : ChannelRecord),
        c₁ ≠ c₂ ∧
        c₁.balance ≠ c₂.balance ∧
        Snapshot.ofChannelRecord c₁ r = Snapshot.ofChannelRecord c₂ r
  ```
- **Hypotheses:** none.
- **Non-vacuity witness:** two copies of `sampleChannel` with the same
  counters/HTLCs/phase but different `Balance` values (for example local
  balance `0` versus `1`). The projection ignores `balance`.
- **Why faithful:** `Persisted`/`Snapshot` contain only counters, HTLCs, and
  `ready` (`PersistenceRecovery.lean:118-126`, `:155-159`); `restoreChannel`
  explicitly leaves balances and phase at live values (`:182-189`). Real LDK
  Node persists a channel manager and channel monitors
  (`builder.rs:2002-2033`, `:2173-2227`), not just this projection. The theorem
  records that the Lean snapshot is not a complete restart image.
- **Fidelity risk:** medium. The module intentionally excludes static channel
  data, and a future design may recover balances elsewhere; the theorem should
  therefore be read as a boundary result, not as a claim that LDK fails to
  persist balances.
- **Feasibility:** high.
- **Priority:** P1.
- **Model extension / external assumption:** no model extension for this
  negative result; the only external assumption is that a real restart obtains
  balances/phase from another source. Any positive “snapshot preserves
  balances” extension is a larger model change and should be a separate target.

### T4 — Model the critical load policy as fail closed on corruption

- **Lean name:** `LnLean.Proofs.PhaseC3.NodePersistencePolicy.critical_load_corrupt_fails_closed`
- **Statement shape:**
  ```lean
  inductive LoadResult (α : Type) where
    | missing
    | corrupt
    | loaded (a : α)

  inductive BuildOutcome (α : Type) where
    | fresh
    | restored (a : α)
    | failed

  def loadCritical {α : Type} : LoadResult α → BuildOutcome α
    | .missing => .fresh
    | .corrupt => .failed
    | .loaded a => .restored a

  theorem critical_load_corrupt_fails_closed
      {α : Type} (r : LoadResult α) (h : r = .corrupt) :
      loadCritical r = .failed
  ```
- **Hypotheses:** `r = .corrupt`; the type is instantiated at the critical
  channel-manager/monitor state, not at the advisory address pool.
- **Non-vacuity witness:** `r := .corrupt`; the LDK witness is the
  `channel_manager_read_failure_fails_build` test
  (`builder.rs:2766-2780`). The missing-state branch has the concrete
  “starting a fresh node” witness at `builder.rs:2196-2214`.
- **Why faithful:** LDK Node distinguishes missing keys (fresh) from unreadable
  critical state (`BuildError::ReadFailed`) for the channel manager, monitors,
  graph, payment store, event queue, and peer store. The abstraction collapses
  the per-store table into two policy classes, which is the main fidelity cost.
- **Fidelity risk:** medium; it models policy shape, not the full builder.
- **Feasibility:** medium. A small inductive model is enough; a full builder
  model is not.
- **Priority:** P2.
- **Model extension / external assumption:** model extension. Actual disk
  corruption detection and backend behavior remain external assumptions.

### T5 — State the per-object write-then-publish contract

- **Lean name:** `LnLean.Proofs.PhaseC3.NodePersistencePolicy.data_store_persist_before_publish`
- **Statement shape:**
  ```lean
  structure StoreImage (α : Type) where
    memory : Option α
    disk : Option α

  def writeThenPublish {α : Type} (img : StoreImage α) (x : α)
      (ok : Bool) : StoreImage α :=
    if ok then { memory := some x, disk := some x } else img

  theorem data_store_persist_before_publish
      {α : Type} (img : StoreImage α) (x : α) :
      writeThenPublish img x false = img ∧
      (writeThenPublish img x true).memory = some x ∧
      (writeThenPublish img x true).disk = some x
  ```
- **Hypotheses:** none beyond the abstract image and success flag.
- **Non-vacuity witness:** `img` with old memory/disk values and `ok := false`;
  the result is exactly `img`. For `ok := true`, both layers hold `x`.
- **Why faithful:** this is the order documented and tested for `DataStore`
  (`data_store.rs:303-309`, `:347-353`, `:1296-1364`). It does not model the
  reader lock or real KV-store durability; those remain assumptions.
- **Fidelity risk:** medium–high if presented as the whole LDK store semantics.
  It is a contract fragment only.
- **Feasibility:** high.
- **Priority:** P2.
- **Model extension / external assumption:** model extension with explicit
  external residuals: in-process reader locking and fsync are not proved.

### T6 — Preserve the memory-first counterexample for peer/event stores

- **Lean name:** `LnLean.Proofs.PhaseC3.NodePersistencePolicy.memory_first_can_leave_memory_ahead`
- **Statement shape:**
  ```lean
  def publishThenWrite {α : Type} (img : StoreImage α) (x : α)
      (ok : Bool) : StoreImage α :=
    if ok then { memory := some x, disk := some x }
    else { img with memory := some x }

  theorem memory_first_can_leave_memory_ahead {α : Type} :
      ∃ (img : StoreImage α) (x : α),
        img.memory = none ∧
        (publishThenWrite img x false).memory = some x ∧
        (publishThenWrite img x false).disk = img.disk
  ```
- **Hypotheses:** none.
- **Non-vacuity witness:** choose `img` with `memory = none` and `disk = none`
  and any `x`; the failure branch writes `x` to memory and leaves disk
  unchanged.
- **Why faithful:** `PeerStore::add_peer` inserts into memory before
  `persist_peers` (`peer_store.rs:45-55`), and `EventQueue::add_event` /
  `event_handled` change the in-memory queue before `persist_queue`
  (`event.rs:437-449`, `:461-473`). The theorem is deliberately a
  counterexample to a **global** persist-before-publish assumption, not a claim
  that every LDK store behaves this way (`remove_peer` is persist-first).
- **Fidelity risk:** medium; a single `publishThenWrite` abstraction does not
  capture per-store differences. It should be accompanied by the concrete
  evidence table above.
- **Feasibility:** high.
- **Priority:** P1.
- **Model extension / external assumption:** model extension/counterexample.
  No safety theorem should depend on a global atomic-publish premise without
  this boundary being explicit; actual per-store Rust behavior remains the
  external source of truth.

### T7 — Model the announce gate

- **Lean name:** `LnLean.Proofs.PhaseC3.NodePersistencePolicy.announce_requires_alias_and_listening`
- **Statement shape:**
  ```lean
  def mayAnnounce (alias : Option String) (listening : List String) : Bool :=
    alias.isSome && !listening.isEmpty

  theorem announce_requires_alias_and_listening
      (alias : Option String) (listening : List String) :
      mayAnnounce alias listening = true ↔
        alias.isSome = true ∧ listening.isEmpty = false
  ```
- **Hypotheses:** none.
- **Non-vacuity witness:** all four combinations: `(some "n", ["a"])`,
  `(some "n", [])`, `(none, ["a"])`, `(none, [])`. Only the first is `true`.
- **Why faithful:** it is a direct abstraction of `may_announce_channel`
  (`config.rs:549-559`) and captures the observable precondition. The
  subsequent `default_user_config` effects (`config.rs:561-580`) are not part of
  this target.
- **Fidelity risk:** low for the gate; the policy effects on forwarding and
  forced announcement preference remain unmodelled.
- **Feasibility:** high.
- **Priority:** P2.
- **Model extension / external assumption:** model extension; LDK config code
  is the external source of truth, and the default-user-config effects are not
  assumed by this target.

## 5. Assumptions, counterexamples, and non-vacuity risks

### Existing results that must be preserved

1. **`inconsistent_snapshot_rolls_back`** (`PersistenceRecovery.lean:618-631`)
   must stay. It is the witness that an arbitrary inconsistent snapshot can
   carry a smaller counter. It is not a stale-but-once-valid snapshot.
2. **`stale_snapshot_rolls_back`** (`:513-517`) must not be deleted or silently
   re-described as a rollback theorem. It is currently definitionally
   `Stale.2`; T1 adds the missing restore step. Keeping the old theorem is fine
   if its docstring says it only extracts the later-state witness.
3. **`recovery_no_rollback_committed`** (`:495-503`) must not be weakened or
   renamed into an unconditional “old snapshot cannot be restored” claim. As
   stated, `hcons : s.Consistent b r` makes it a monotonicity corollary. A
   corrected comment should say so; a new “latest prefix” hypothesis, if added,
   must be explicit.
4. **`recovery_retains_channelReady`** (`:591-598`) must keep `hm` and the live
   `r`. T2 shows the snapshot alone cannot supply the message; do not replace
   `hm` with a `ready = true` hypothesis.
5. **`ready_snapshot_reaches_normal`** (`:661-667`) must keep its bridge
   hypothesis. Turning it into an unconditional phase transition would hide the
   missing `Msg.channelReady → ProtocolEvent.fundingLocked` bridge.

### New non-vacuity witnesses

- T1 uses a real `Step.revokeAndAck` transition and a formerly valid snapshot.
- T2 uses two distinct `channelReady` payloads with identical projection.
- T3 uses two channels differing only in balance.
- T4's concrete witness is a failing channel-manager read that returns
  `BuildError::ReadFailed`.
- T5/T6 use explicit memory/disk images with a failed write.
- T7 uses all four alias/listening combinations.

### Hidden-assumption risks to flag

- **Atomic snapshot vs real crash atomicity.** `RecoveryPoint.consistent` is a
  *hypothesis* (`:443-448`); the module does not prove that a filesystem or
  KV-store write is atomic. Any prose that says “recovery is crash-safe” would
  hide this.
- **Live record vs persisted record.** `restoreRecord` keeps a live
  `lastChannelReady` when `ready` is true (`:196-197`). On a real restart there
  is no live record unless the builder loaded one. T2 should be cited whenever
  this is discussed.
- **Projection completeness.** `restoreChannel` leaves phase and balances at
  live values (`:182-189`). This is safe as a projection theorem, but not a
  claim that a restart reconstructs a usable channel from the snapshot alone.
- **Global store atomicity.** The `DataStore` contract is per-object; peer and
  event stores are memory-first, and wallet sub-changesets are non-atomic.
  A future theorem must not assume one global publish order merely because
  `DataStore` has a mutation lock.
- **No real backend semantics.** FS migration, fsync, SQLite/Postgres
  selection/refusal, monitor serialization, and wallet persistence are all
  outside the model. They should be labelled external, not “covered” by a
  similarly named theorem.

### Weakening prohibition

None of T1–T7 weakens an existing theorem. T1 strengthens the stale case; T2,
T3, and T6 are negative results; T4, T5, and T7 are additive. If a future
extension adds `balance` or `readyMessage` to `Snapshot`, it must add a new
projection/version rather than silently changing the existing fields, and it
must keep the existing counterexamples and the `Consistent` hypothesis explicit.

## 6. Wave-13 recommendation

**Recommendation: implement a narrow P1 “honesty/correction” lane, not a broad
restart-proof lane.**

- **Implement now (safe, small):** T1, T2, and T3 in
  `PersistenceRecovery.lean`. T1 is the top target. These are additive,
  compile-local, and directly repair the misleading stale/ready/projection
  claims.
- **Implement as a separate policy slice:** T4 (P2), T5 (P2), T6 (P1), and T7
  (P2) in a new `NodePersistencePolicy` module if the parent wants the
  builder/store behavior represented. T6's memory-first counterexample is the
  highest-value part of that group. Do not put builder/config policy into
  `PersistenceRecovery.lean` without changing that module's stated scope.
- **Treat as external:** real LDK monitor persistence and watchtower/backup
  (R08), event/background processing (R18), wallet/BDK persistence and
  sub-changeset ordering (R04), filesystem/Postgres migration, fsync, storage
  locks, entropy/mnemonic handling, and actual Rust data-store concurrency.
- **Do not claim:** that the current snapshot is a full restart image, that
  `ready : Bool` reconstructs a `channel_ready` message, that
  `RecoveryPoint.consistent` proves crash atomicity, or that LDK Node has a
  single global persist-before-publish order.

**Gate for the lane:** T1–T3 must compile without `sorry`; existing theorem
statements and `inconsistent_snapshot_rolls_back` stay intact; any catalog or
`AxiomAudit` addition happens only after the target is stable. T4–T7 should not
be merged into the catalog until their abstraction boundaries are documented.
This is a safe implementation lane for wave 13/14 **only at the correction/
boundary level**. Full LDK builder/restart fidelity is an external engineering
and human-review barrier, not a theorem-only task.

## 7. Evidence and commands

**Pins verified:**

```sh
git -C /tmp/opencode/ldk-refs/ldk-node rev-parse HEAD
# fa123fed131e27ecc420b77fa7086fcf1ddaebb8
git -C /tmp/opencode/ldk-refs/ldk-server rev-parse HEAD
# c17dc11dde38f88c53457039ddf30c6b90a63ba2
git rev-parse --short HEAD
# f7f0628
```

**Read-only inspection commands (no builds, no cargo tests, no network):**

```sh
rg -n "PersistenceRecovery|persistenc|recovery_no_rollback|stale_snapshot|inconsistent_snapshot|ready_snapshot" \
  docs/THEOREM-INDEX.md docs/TRACEABILITY.md docs/PHASE-C3-LANES.md \
  LnLean/Proofs/AxiomAudit.lean LnLean.lean LnLean/Proofs/All.lean
rg -n "PersistenceRecovery|stale_snapshot|inconsistent_snapshot|restore_replay|recovery_retains" \
  -g '*.lean' .
rg -c '^\| `LN-' docs/THEOREM-INDEX.md
rg -c '^\| `LN-' docs/TRACEABILITY.md
sed -n '1,691p' LnLean/Proofs/PhaseC3/PersistenceRecovery.lean
nl -ba LnLean/Channel/Types.lean | sed -n '157,176p'
nl -ba LnLean/Channel/State.lean | sed -n '80,155p'
nl -ba LnLean/Protocol/Peer.lean | sed -n '87,136p'
nl -ba LnLean/Proofs/Liveness.lean | sed -n '565,600p'
nl -ba LnLean/Proofs/PhaseC3/AxiomAudit.lean | sed -n '575,585p;1014,1018p'
```

**LDK files inspected (read-only):**

- `ldk-node/src/builder.rs` — build/load/restart policy, network mismatch.
- `ldk-node/src/config.rs` — defaults and announce gate.
- `ldk-node/src/data_store.rs` — mutation lock, persist-before-cache, tests.
- `ldk-node/src/peer_store.rs` — memory-first add, persist-first remove, readers.
- `ldk-node/src/event.rs` — memory-first add/handled.
- `ldk-node/src/wallet/persist.rs` — advisory address pool, sub-changeset order.
- `ldk-node/src/io/fs_store.rs` — v1→v2 migration, fsync, crash recovery.
- `ldk-server/ldk-server/src/main.rs` — network dirs, storage-migration refusal, Postgres lock.
- `ldk-server/ldk-server/src/util/entropy.rs` — mnemonic load/generate.

**Scope compliance:** only this report was written. No Lean, docs, scripts,
tests, vendor, catalog, branch, commit, or remote state was modified. No full
build and no network-fetching test was run.
