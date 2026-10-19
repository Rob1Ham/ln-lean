# R08 — Close, force-close, revocation, watchtowers, and backup
**Status:** read-only review
**Pins:** LDK Node `fa123fed131e27ecc420b77fa7086fcf1ddaebb8`, LDK Server `c17dc11dde38f88c53457039ddf30c6b90a63ba2`

## 1. Scope and current Lean surface

This lane reviews cooperative close, force close, revoked-commitment
punishment, watchtower behavior, and monitor/backup recovery.  The current
catalog is 51/51 `proved` (294 targets, 314 build jobs, 435 audited
theorems); that status says the named theorems are proved, not that the
English behavior is covered.  The relevant claim surface is:

| Catalog row | Exact Lean target | What the target literally states | Scope note |
|---|---|---|---|
| `LN-HT-005` | `LnLean.Security.revoked_commitment_is_old` (`Security/Invariants.lean:269`) | If `commitmentNumber < currentCommitment`, the two numbers are unequal. | Definitional consequence of `<`; no store, secret, key, or script. |
| `LN-HT-006` | `LnLean.Security.breach_penalty_spends_both` (`Security/Invariants.lean:299`) | A `Breach.Punishable` record contains `SpendsBoth {old,0} {old,1}` as a conjunct. | A projection of the record's own predicate; no transaction serialization, witness, or revocation key. |
| `LN-SEC-005` | `LnLean.Proofs.Liveness.penalty_economical` (`Proofs/Liveness.lean:763`) | Under `FeeScheduleBounded env rMax` and a break-even penalty, the penalty is economical at the effective and every scheduled rate. | Conditional fee-schedule theorem; not a claim about close timing or output coverage. |
| `LN-SEC-006` | `LnLean.Proofs.Liveness.watchtower_bridge` (`Proofs/Liveness.lean:717`) | A watchtower report at the breach height, a `BreachResponse`, and an L1 bridge imply punishment and tower liveness. | Requires `wt.reports c c.breachHeight` and a complete `BreachResponse`; `wt.live` alone is insufficient. |
| `LN-L1-004` | `ToLocalScriptTargets.toLocalScriptFull_carries_csv_and_revocationKey` and the interpreter bridges | The full BOLT 3 `to_local` script carries the CSV delay and revocation key, and the delayed/revocation branches execute through the vendored interpreter under explicit EC/context hypotheses. | Strong script-level coverage for `to_local`; no theorem connects it to `PenaltyTx`, `RevokedCommitment`, or `BreachResponse`. |

Additional, non-catalog surfaces used by this lane:

* `LnLean.Channel.Revocation` defines `Shachain`
  (`Revocation.lean:151`), `RevocationScheme` (`:194`), `RevocationStore`
  (`:258`), `isRevoked` (`:275`), and `provideSecret` (`:281`).  The store is
  a `Fin 49 → Option (Nat × PerCommitmentSecret)` field plus `minSeen`.
* `LnLean.Proofs.Channel.RevocationProps` proves `isRevoked` is the initial
  segment `[0, minSeen)` (`:198`), store monotonicity (`:229`), and the
  “49 slots” facts (`:218`).  The latter are list-length facts, not a
  storage/reconstruction theorem.
* `LnLean.Channel.Penalty` defines `RevokedCommitment` (`Penalty.lean:68`),
  the exactly-two-input `PenaltyTx` (`:94`), `penaltySpendsBoth` (`:116`),
  `timelyL1Confirmation` (`:126`), and `penaltyValid` (`:141`).
* `LnLean.Proofs.Channel.BreachProps` adds `HoldsRevocationSecret`
  (`:99`), `BreachConfirmed` (`:107`), `HonestPunishable` (`:114`), the
  two-field `Watchtower` (`:134`), `Detectable` (`:145`), and the
  statement-only `PenaltyHtlcCoverage` (`:177`).
* `LnLean.Proofs.PhaseC3.WatchtowerBreach` defines
  `DetectionBeforeDeadline` (`:78`), `BridgeAcceptance` (`:90`), the
  `WatchtowerBreachRemedy` record (`:103`), and
  `watchtowerBreach_end_to_end` (`:254`).
  `WatchtowerLiveness.eventually_detected_and_penalized` (`:228`) adds
  fairness/timer hypotheses and exposes the same external detection and
  acceptance assumptions.
* `LnLean.Proofs.WaveE.E35` proves the positive bridge
  (`waveE_e35_watchtower_bridge`, `:198`) and the negative
  `waveE_e35_live_watchtower_alone_does_not_punish` (`:367`) using
  `silentWatchtower` (`:299`).
* `LnLean.Proofs.PhaseC3.CloseConservation` proves cooperative and
  unilateral value arithmetic (`cooperativeClose_conserved`, `:224`;
  `unilateralClose_conserved`, `:269`) and proves the contest delay is
  value-irrelevant (`contestDelay_totalOutputValue`, `:323`).
* `LnLean.Proofs.PhaseC3.PersistenceRecovery` persists only counters, the
  HTLC set, and the `ready` flag (`Persisted`, `:118`; `Snapshot`, `:155`);
  its consistency precondition is explicit (`Consistent`, `:202`).
* `LnLean.Channel.State` has one `shutdown` transition (`:123`) and one
  `closingSigned` transition (`:126`); there is no force-close event or
  transition constructor.

The key negative facts are already visible in the module documentation:
the 49-slot placement/reconstruction algorithm is not proved
(`Revocation.lean:45-53`), HTLC-output penalties are only a statement
(`Penalty.lean:45-53`, `BreachProps.lean:170-181`), the watchtower has no
live→report direction (`BreachProps.lean:134-142`), and persistence
is exactly counters, HTLCs, and the ready flag (`PersistenceRecovery.lean:118-130`);
it explicitly excludes fsync, watchtowers, and L1 recovery (`:79-96`) and has
no fields for monitors, revocation secrets, on-chain claims, or event queues.

## 2. LDK datapoints (with `file:line`)

All citations are from the pinned clones listed above.  No cargo test or
network fetch was run.

| Area | LDK evidence | Observed behavior |
|---|---|---|
| Cooperative vs force close APIs | LDK Node `src/lib.rs:2239-2257` (`close_channel`), `:2261-2269` (`force_close_channel`), `:2271-2316` (`close_channel_internal`), `:2286` (`force_close_broadcasting_latest_txn`) | Cooperative close is attempted first; force close broadcasts the latest commitment. The docstring warns that force-close funds are time-locked and more expensive. |
| Server close RPCs | LDK Server `ldk-server/src/api/close_channel.rs:23-48` | `CloseChannel` and `ForceCloseChannel` are thin RPC mappings to `Node::close_channel` / `Node::force_close_channel`; the optional force-close reason is passed through. |
| Close lifecycle event | LDK Node `src/event.rs:295-306` (`ChannelClosed`), `:2153-2259` (handler) | The event carries `channel_id`, `user_channel_id`, `counterparty_node_id`, and `reason`. The handler resolves splice rounds, retains a force-closed peer through one recovery reconnect (`:2204-2248`), removes other peers, and retries on queue failure with `ReplayEvent`. |
| Spendable outputs after close | LDK Node `src/event.rs:1682-1725` (`SpendableOutputs`) | Closing/penalty outputs are handed to the output sweeper and recorded per channel; the sweeper must track them durably. |
| Revoked-output claim balance | LDK Node `src/balance.rs:205-217` (`CounterpartyRevokedOutputClaimable`), LDK Server `ldk-server/src/util/proto_adapter.rs:444-457` | The node exposes a balance for outputs it can claim after a counterparty revoked close, before on-chain maturity/confirmation. |
| Monitor persistence and load | LDK Node `src/builder.rs:2013-2028` (`read_all_channel_monitors_with_updates`), `:2040-2050` (`ChainMonitor::new_async_beta`), `:2220-2228` (`load_existing_monitor`); `src/lib.rs:388-398` | `ChannelMonitor` state is read from the KV store, loaded into the `ChainMonitor`, and each restored monitor is synced before peers or events can act on stale confirmations. |
| Durable object mutation | LDK Node `src/data_store.rs:436-468` (`mutate`/`mutate_with`); `src/io/fs_store.rs:44-58` | A single object read/transform/write is serialized under a mutation lock, and the filesystem migration path fsyncs renames. This is per-object atomicity, not a multi-object transaction. |
| Remote persistence caveat | LDK Node `src/builder.rs:816-819` | VSS/remote persistence is alpha and experimental; unrecoverable persistence failures may panic after retries. |
| Anchor trust and force-close avoidance | LDK Node `src/config.rs:453-471` (`trusted_peers_no_reserve`), `:815-819` (`force_close_avoidance_max_fee_satoshis`) | Anchors may be left to a trusted peer to broadcast; cooperative close has a fee-avoidance budget before force close. |
| Backup and restore | LDK Server `docs/operations.md:49-66`, `docs/configuration.md:252-274` | Backups are `keys_mnemonic` **plus** `ldk_node_data.sqlite` or PostgreSQL; both files are required to recover channel funds. The docs warn not to restore onto two running nodes simultaneously. |
| Cooperative close retry | LDK Server `e2e-tests/src/lib.rs:1062-1094` | A cooperative close is retried for up to five seconds because the last HTLC's asynchronous monitor update can briefly block shutdown. |
| Force-close claims and restart | LDK Server `e2e-tests/src/lib.rs:1246-1285`; `e2e-tests/tests/postgres.rs:331-410` | After force close, claims are observed as `ClaimableAwaitingConfirmations`; PostgreSQL-backed monitors are restored while outputs are still timelocked and the claims survive restart. |
| Close reason/initiator lifecycle | LDK Server `e2e-tests/tests/e2e.rs:881-1050` | The lifecycle test distinguishes `HolderForceClosed` from `CounterpartyForceClosed` and reports local/remote closure initiators; cooperative close is a separate lifecycle. |
| Watchtower surface | `rg -i 'watchtower|watch_tower'` over both pinned trees (excluding `.git`) | No matches. LDK Node/Server expose no watchtower registration, persistence, or server API; recovery relies on persistent monitors and the documented backup pair. This does not prove rust-lightning cannot be used with an external tower. |

## 3. Gap matrix

| Behavior | Lean status | LDK evidence | Gap / counterexample | Priority |
|---|---|---|---|---|
| Cooperative close value conservation (two outputs + negotiated fee) | **partially covered** | `docs/operations.md:49-66`; BOLT 2 `02-peer-protocol.md:2411-2415` | `cooperativeClose_conserved` (`CloseConservation.lean:224`) proves the arithmetic only under `fee ≤ funderBalance`. It does not model dust trimming, output scripts, fee negotiation, or the HTLC-empty precondition; `cooperativeClose` can pay a sub-dust output because it is pure `Nat` subtraction. | P1 |
| Cooperative close state/message legality (`shutdown`, `closing_signed`, no pending HTLC/update, duplicate shutdown, `scriptpubkey`) | **partially covered** | BOLT 2 `02-peer-protocol.md:2136-2185`; LDK close retry `e2e-tests/src/lib.rs:1062-1094` | `Step.shutdown` (`State.lean:123`) is legal from any `normal` channel regardless of `htlcs`; `Step.closingSigned` (`:126`) completes immediately from `shuttingDown`. There is no `scriptpubkey` check, no duplicate-shutdown check, and no pending-`revoke_and_ack` guard. | P1 |
| Force close as a protocol transition and state | **missing** | LDK Node `src/lib.rs:2261-2269`, `:2286`; LDK Server `close_channel.rs:37-48` | `ProtocolEvent` (`State.lean:67`) has no force-close constructor; `Step` (`:86`) reaches `closed` only through cooperative `closingSigned`. `unilateralClose_conserved` is a construction-level arithmetic theorem, not a close transition. | P1 |
| Force-close reason, initiator, peer retention, event replay | **missing** | LDK Node `src/event.rs:295-306`, `:2153-2259`; LDK Server `e2e-tests/tests/e2e.rs:1002-1050` | The Lean model has no close reason, initiator, `ChannelClosed` event, peer-retention phase, or `ReplayEvent` retry. It therefore cannot state “force close retains the peer for one reconnect” or “cooperative and counterparty closes differ in reason.” | P2 |
| Revoked-state detection by commitment number and store | **partially covered** | BOLT 5 `05-onchain.md:510-529`; LDK `balance.rs:205-217` | `breachDetected` is only `number < currentNumber` (`Penalty.lean:90`). `BreachConfirmed` (`BreachProps.lean:107`) adds `isRevoked st number`, but `isRevoked` is only `number < minSeen` (`Revocation.lean:275`); no theorem ties `minSeen` to the channel's current number except the explicit hypothesis `st.minSeen = c.currentNumber` (`BreachProps.lean:190`). | P1 |
| Per-commitment secret store, shachain placement, and reconstruction | **partially covered** | BOLT 3 `03-transactions.md:828-870` | `slots` is never read by any theorem; `provideSecret` writes only slot 0 (`Revocation.lean:281-289`) and accepts any in-range secret. `storage_slots_fixed` (`Revocation.lean:316`) and `storage_slots_le_49` (`RevocationProps.lean:218`) only compute the length of `List.finRange 49`; they do not constrain `slots`. A bogus 32-byte secret at index `i` still sets `minSeen = i+1`, so `isRevoked` reports every lower index as revoked. | P1 |
| Revocation key / old-output binding | **partially covered** | BOLT 3 `03-transactions.md:799-826`, `:113-130`; BOLT 5 `05-onchain.md:517-547` | `RevokedCommitment` (`Penalty.lean:68`) has no old-output script, revocation key, or `toSelfDelay`; `penaltyValid`'s key conjunct (`:141-149`) is the abstract `RevocationScheme.consistent` equality and does not bind the witness to the old commitment's script. `HoldsRevocationSecret` (`BreachProps.lean:99`) repairs the secret side, but is not part of `penaltyValid` or `punishable`. | P1 |
| Penalty transaction outputs and HTLC coverage | **partially covered** | BOLT 5 `05-onchain.md:517-547`; BOLT 3 `03-transactions.md:792-797`, `:136-146` | `PenaltyTx` has exactly two inputs (`Penalty.lean:94-99`), and `penaltyTx_no_third_input` (`BreachProps.lean:449`) proves it cannot spend a third outpoint. `PenaltyHtlcCoverage` (`:177`) is statement-only. The model also describes `to_remote` as a revoked output; BOLT 3 says the non-anchor `to_remote` is a plain P2WPKH to the holder and “should not be handed to a watchtower” (`03-transactions.md:792-797`). The theorem `breach_penalty_spends_both` only asserts spend membership, so it is not itself false, but the module's “both with the revocation key” reading is contradicted. | P1 |
| Penalty timeliness and contest-delay semantics | **partially covered** | BOLT 3 `03-transactions.md:113-130`; BOLT 5 `05-onchain.md:510-582` | `timelyL1Confirmation` uses an arbitrary `window` (`Penalty.lean:126-128`); `DetectionBeforeDeadline` uses `breachHeight + window` for both observation and confirmation (`WatchtowerBreach.lean:78-87`). `contestDelay` is proved value-irrelevant (`CloseConservation.lean:323`) but never tied to the old commitment's `toSelfDelay` or to the penalty window. | P1 |
| Watchtower report → liveness and punishment | **partially covered** | No watchtower API in LDK Node/Server; external service | `Watchtower` has only `live`, `reports`, and `reports_live` (`BreachProps.lean:134-142`). `watchtower_bridge` needs both `wt.reports c c.breachHeight` and a full `BreachResponse` (penalty tx + confirmation) (`Liveness.lean:717-724`), so it does not derive punishment from a live tower. `waveE_e35_live_watchtower_alone_does_not_punish` (`E35.lean:367`) is the preserved counterexample. | P2 |
| Watchtower registration, secret custody, persistence, broadcast | **missing** | No LDK Node/Server surface; external tower contract | No registration set, no persisted tower state, no secret-copy obligation, no broadcast/retry, and no proof that a registered live tower reports. `WatchtowerLiveness.eventually_detected_and_penalized` assumes `s.tower.live` and `TimelyAcceptance` (`:228-245`) rather than deriving them. | P2 |
| Monitor/backup persistence and recovery | **missing** | LDK Node `builder.rs:2013-2050`, `:2220-2228`; `lib.rs:388-398`; LDK Server `docs/operations.md:49-66`, `postgres.rs:331-410` | `PersistenceRecovery` persists only counters, HTLCs, and `ready` (`:118-130`); it explicitly excludes fsync, watchtowers, and L1 recovery (`:79-96`) and has no fields for monitors, revoked secrets, on-chain claims, or event queues. There is no model of monitor load/sync, claim maturity, or the mnemonic+DB backup pair. | P1 |
| Crash atomicity and no-rollback across the full state | **partially covered** | LDK Node `data_store.rs:436-468`, `fs_store.rs:44-58`; VSS caveat `builder.rs:816-819` | Recovery theorems are conditional on `Snapshot.Consistent` (`:202`); `inconsistent_snapshot_rolls_back` (`:618`) and `stale_snapshot_rolls_back` (`:513`) are preserved. No theorem covers multi-object atomicity, fsync, DB transaction boundaries, remote VSS, or restore-to-two-nodes. | P1 |
| Spendable-output/event-queue recovery after close | **missing** | LDK Node `event.rs:1682-1725`, `:2153-2259`; LDK Server `e2e-tests/src/lib.rs:1246-1285` | No Lean state for pending sweeps, claim maturity, or the event queue; `BreachResponse` assumes the penalty is already confirmed. The model has no analogue of `ReplayEvent` or `ClaimableAwaitingConfirmations`. | P2 |

## 4. Proposed targets

The following are additive targets.  None should be implemented by
weakening an existing hypothesis or by turning an external assumption into
a field that makes the conclusion definitional.

### T1. `LnLean.Channel.Revocation.provideSecret_preserves_validFor` (P1, model extension)

**Statement shape.**

```lean
def RevocationStore.ValidFor (sh : Shachain) (st : RevocationStore) : Prop :=
  ∀ (k : Fin SECRET_STORAGE_SLOTS) (idx : Nat) (s : PerCommitmentSecret),
    st.slots k = some (idx, s) → s = sh.derive idx

theorem provideSecret_preserves_validFor
    (sh : Shachain) (st : RevocationStore) (hst : ValidFor sh st)
    (idx : Nat) (hidx : idx < COMMITMENT_SECRET_COUNT)
    (s : PerCommitmentSecret) (hsecret : s = sh.derive idx) :
    ValidFor sh (provideSecret st idx s hidx)
```

**Hypotheses.** The store is already sound for `sh`; the supplied secret is
the shachain secret of `idx`; `idx` is in the BOLT 3 range.  The theorem
must also expose `stored_secret_eq_shachain` as the immediate corollary for
every occupied slot.

**Non-vacuity.** `ValidFor sh emptyStore` holds because every slot is
`none`; `ValidFor sh (provideSecret emptyStore idx (sh.derive idx) hidx)`
holds by the theorem.  A concrete `Shachain` witness can reuse the existing
`exists_shachain_of_derivation` (`RevocationProps.lean:285`).

**Why faithful.** BOLT 3 requires the 49 stored `(secret,index)` pairs to be
the shachain values (`03-transactions.md:860-870`).  This target makes the
store's contents answer to that requirement without pretending to implement
the bit-flip/SHA-256 reconstruction.

**Fidelity risk / feasibility.** Low fidelity risk; easy.  It does **not**
prove that every `i < minSeen` has a reconstructible secret, and it does not
change `isRevoked`.  Keep that completeness obligation separate.

### T2. `LnLean.Proofs.Channel.PenaltyProps.confirm_before_toSelfDelay` (P1, model extension)

**Statement shape.**

Add a defaulted field `toSelfDelay : Blocks := 0` to `RevokedCommitment`
(preserving existing named-field literals), plus a bridge
`RevokedCommitment.ofCommitment` that sets `toSelfDelay := c.contestDelay`.
Then:

```lean
theorem confirm_before_toSelfDelay
    (scheme : RevocationScheme) (c : RevokedCommitment) (p : PenaltyTx)
    (w : PenaltyWitness) (confirm : Height)
    (hv : penaltyValid scheme c p w confirm c.toSelfDelay) :
    confirm < c.breachHeight + c.toSelfDelay

theorem arbitrary_window_admits_late_penalty
    (c : RevokedCommitment) (window : Blocks)
    (h : c.toSelfDelay < window) :
    ∃ confirm : Height,
      timelyL1Confirmation c.breachHeight confirm window ∧
      c.breachHeight + c.toSelfDelay ≤ confirm
```

**Hypotheses.** For the positive form, the penalty uses the old
commitment's own `toSelfDelay` as its window.  For the counterexample,
`window : Blocks` is strictly larger than the CSV delay.

**Non-vacuity.** The concrete `buildCommitment ... 144` witness from
`concrete_unilateral_close_conserved` (`CloseConservation.lean:457-467`)
supplies a positive delay through the `RevokedCommitment.ofCommitment`
bridge; `confirm := breachHeight + 144` is the late-penalty witness when
`window = 145`.

**Why faithful.** BOLT 3 puts `to_self_delay` on the breacher's `to_local`
output (`03-transactions.md:113-130`); after that delay the breacher can
spend.  A “timely” penalty after the CSV delay is not timely in the
protocol sense.  The counterexample exposes the current model's arbitrary
`window` rather than hiding it.

**Fidelity risk / feasibility.** Medium: the orientation of `toSelfDelay`
and the anchor/zero-fee variants must be stated explicitly.  Easy-to-medium
proof; no existing theorem is weakened because the positive theorem is
stated at the sharper window.

### T3. `LnLean.Channel.Close.ForceClose` and `forceCloseStep_conserved` (P1, model extension)

**Statement shape.**

```lean
inductive ForceCloseReason
  | holderRequested | counterpartyBroadcast | revokedCommitment | timeout | other

structure ForceClose where
  commitment : Commitment
  reason : ForceCloseReason
  broadcastHeight : Height

def ForceCloseStep (c : Channel) (fc : ForceClose) (c' : Channel) : Prop :=
  c' = { c with phase := ChannelPhase.closed } ∧
  fc.commitment.commitmentNumber = c.localCommitmentNumber

theorem forceCloseStep_closes
    (c c' : Channel) (fc : ForceClose) (h : ForceCloseStep c fc c') :
    c'.phase = ChannelPhase.closed

theorem forceCloseStep_conserved
    (c c' : Channel) (fc : ForceClose) (h : ForceCloseStep c fc c')
    (hc : CommitmentConserved fc.commitment) :
    fc.commitment.totalOutputValue + fc.commitment.feeSat =
      fc.commitment.fundingValueSat

theorem forceCloseStep_current_not_breach
    (c c' : Channel) (fc : ForceClose) (h : ForceCloseStep c fc c') :
    ¬ fc.commitment.commitmentNumber < c.localCommitmentNumber
```

**Hypotheses.** `CommitmentConserved` for the broadcast commitment; the
force-close commitment number equals the current local commitment number.
`forceCloseStep_conserved` is a lift of `unilateralClose_conserved`; it does
not re-prove the arithmetic.

**Non-vacuity.** Instantiate `fc.commitment` with the concrete
`buildCommitment Direction.local 0 100000 1000 60000 [...] 144 false`
witness already used at `CloseConservation.lean:457-467`; its number is the
current number, so `breachDetected` is false.

**Why faithful.** LDK's force close broadcasts the latest commitment
(`lib.rs:2261-2269`, `:2286`); a force close of the current state is not a
breach.  This is the transition-level counterpart of the existing
construction-level `unilateralClose_conserved`.

**Fidelity risk / feasibility.** Medium: the current `Channel` has no
per-party orientation beyond `localCommitmentNumber`; the target should
either document that orientation or parameterize it.  The phase set
`normal ∨ shuttingDown` is deliberately minimal; widening it to
`awaitingLockin` is a separate decision.  Do not add a
`ProtocolEvent.forceClose` constructor to the core `Step` without checking
all exhaustive case proofs; a separate `ForceCloseStep` is the safe path.

### T4. `LnLean.Channel.Penalty.PenaltyCoverage` (P1/P2, model extension)

**Statement shape.**

```lean
inductive RevokedOutputKind
  | toLocal | htlcOffered | htlcReceived

structure RevokedOutput where
  outpoint : OutPoint
  value : BtcAmount
  kind : RevokedOutputKind
  revocationKey : RevocationKey

structure PenaltyPlan where
  outputs : List RevokedOutput
  inputs : List OutPoint
  sweep : TxOut
  fee : BtcAmount
  covers : ∀ o ∈ outputs, o.outpoint ∈ inputs
  sweep_eq :
    sweep.value = (outputs.map (fun o => o.value)).sum - fee

theorem penaltyPlan_covers_revoked_outputs
    (p : PenaltyPlan) (o : RevokedOutput) (ho : o ∈ p.outputs) :
    o.outpoint ∈ p.inputs

theorem penaltyPlan_kind_cases (o : RevokedOutput) :
    o.kind = .toLocal ∨ o.kind = .htlcOffered ∨ o.kind = .htlcReceived
```

**Hypotheses.** A `PenaltyPlan` is a list of genuinely revocation-locked
outputs (`to_local` and HTLC outputs), each with its own revocation key and
value; the sweep is the sum minus the fee.  `to_remote` is deliberately not
in `RevokedOutput` (there is no `toRemote` constructor); it is a holder
output, not a revocation output.

**Non-vacuity.** A plan with one `toLocal` and one `htlcOffered` output has
a two-element input list and a non-zero sum; it is disjoint from the
existing two-input `PenaltyTx` case.  The existing
`penaltyTx_no_third_input` (`BreachProps.lean:449`) is retained as the
counterexample showing the current `PenaltyTx` cannot be the full plan.

**Why faithful.** BOLT 5 requires resolving the remote main output and the
revoked HTLC outputs (`05-onchain.md:517-547`); BOLT 3 explicitly says a
transaction with only a `to_remote` output “does not need any enforcement”
and should not be handed to a watchtower (`03-transactions.md:792-797`).
This target fixes the current model's overstatement without claiming that
one transaction always resolves every output (the same BOLT 5 section
allows separate penalty transactions under pinning/`security_delay`).

**Fidelity risk / feasibility.** High fidelity risk if stated as “one tx
covers all outputs.”  State only “a plan covers the listed outputs” and keep
the multi-tx policy explicit.  Medium-hard: new list-valued structures and
a bridge from the existing `PenaltyTx` special case.

### T5. `LnLean.Proofs.PhaseC3.CloseConservation.shutdown_allows_pending_htlcs` and `GuardedCooperativeClose` (P1, model extension)

**Statement shape.**

```lean
theorem shutdown_allows_pending_htlcs
    (c : Channel) (hphase : c.phase = ChannelPhase.normal)
    (hhtlc : c.htlcs ≠ []) :
    ∃ c', Step c ProtocolEvent.shutdown c' ∧ c'.htlcs = c.htlcs

structure GuardedCooperativeClose (c : Channel) : Prop where
  noHtlcs : c.htlcs = []

theorem guardedCooperativeClose_no_htlcs
    (c : Channel) (h : GuardedCooperativeClose c) : c.htlcs = []
```

**Hypotheses.** The counterexample needs a non-empty HTLC list and a
`normal` channel; the guarded predicate records the HTLC-empty part of the
BOLT 2 quiescence condition.  Pending updates and a pending `revoke_and_ack`
are not representable in the current `Channel`; adding those fields is a
separate model change, not something this guard silently assumes.

**Non-vacuity.** `{ c with htlcs := [] }` satisfies
`GuardedCooperativeClose`; a channel with one `HTLCState.offered` entry
satisfies the counterexample.

**Why faithful.** BOLT 2 forbids `shutdown` while updates are pending and
requires the channel to be empty of HTLCs before closing negotiation
(`02-peer-protocol.md:2136-2185`, `:2411-2415`).  The counterexample makes
the current gap explicit instead of silently strengthening `Step.shutdown`.

**Fidelity risk / feasibility.** Low fidelity risk; easy.  Do not add the
HTLC guard to the existing `Step.shutdown` constructor in wave 13:
`Liveness.lean:222` and `:642` construct shutdown from arbitrary normal
states.  Add a guarded layer or update every call site with a reviewed
diff.

### T6. `LnLean.Proofs.PhaseC3.WatchtowerService.TowerContract` (P2, external assumption + model extension)

**Statement shape.**

```lean
structure TowerContract (sh : Shachain) (wt : Watchtower) where
  registered : RevokedCommitment → Prop
  holdsSecret : ∀ c, registered c → ∃ w, HoldsRevocationSecret sh c w
  liveReporting :
    wt.live → ∀ c, registered c → ∃ h, wt.reports c h

structure TowerSnapshot where
  registrations : List (Nat × PerCommitmentSecret)

def TowerSnapshot.ofState (ts : TowerSnapshot) : TowerSnapshot := ts
def TowerSnapshot.restore (s : TowerSnapshot) : TowerSnapshot := s

theorem registration_survives_restore (s : TowerSnapshot) :
    s.restore.registrations = s.registrations

theorem registered_live_reports
    (tc : TowerContract sh wt) (c : RevokedCommitment)
    (hlive : wt.live) (hc : tc.registered c) :
    ∃ h, wt.reports c h
```

**Hypotheses.** `liveReporting` is the named external service contract:
a live tower with a registration eventually reports.  It is not derived
from `Watchtower.live`; the existing `silentWatchtower` remains a valid
counterexample to the unconditional reading.

**Non-vacuity.** A tower that registers one commitment and reports at
`breachHeight` satisfies the contract; `silentWatchtower` does not satisfy
`liveReporting`, so `waveE_e35_live_watchtower_alone_does_not_punish`
(`E35.lean:367`) still holds.

**Why faithful.** The current model has no registration, secret custody,
persistence, or broadcast.  This target models only the durable registration
part and states the liveness/delivery contract explicitly.  LDK Node/Server
have no watchtower surface, so the operational tower remains external.

**Fidelity risk / feasibility.** High: `liveReporting` is an assumption, not
a theorem.  Medium: the snapshot/restore part is easy; the contract part is
specification-only.  Do not add `live → reports` as a field of the existing
`Watchtower`; that would hide the assumption and invalidate the retained
counterexample.

### T7. `LnLean.Proofs.PhaseC3.PersistenceRecovery.FullSnapshot` (P2, model extension + external durability)

**Statement shape.**

```lean
structure MonitorSnapshot where
  channelId : ChannelId
  latestUpdateId : Nat
  revokedSecrets : RevocationStore
  claimable : List OutPoint

structure FullSnapshot where
  channel : Snapshot
  monitors : List MonitorSnapshot
  claims : List OutPoint
  events : List ProtocolEvent

def FullConsistent (fs : FullSnapshot) (c : Channel)
    (r : ChannelRecord) (ms : List MonitorSnapshot) : Prop :=
  fs.channel.Consistent c r ∧ fs.monitors = ms ∧
  fs.claims = ms.bind (fun m => m.claimable)

theorem fullSnapshot_restore_preserves_claims
    (fs : FullSnapshot) (c : Channel) (r : ChannelRecord)
    (ms : List MonitorSnapshot) (h : FullConsistent fs c r ms)
    (o : OutPoint) (ho : o ∈ ms.bind (fun m => m.claimable)) :
    o ∈ fs.claims

theorem stale_full_snapshot_rolls_back :
    ∃ (fs : FullSnapshot) (c : Channel) (r : ChannelRecord)
      (ms : List MonitorSnapshot),
      ¬ FullConsistent fs c r ms ∧
      fs.channel.localCommitmentNumber < c.localCommitmentNumber
```

**Hypotheses.** `FullConsistent` is an explicit atomic-snapshot relation
covering the channel projection, monitor list, revoked secrets, claims, and
event queue.  Durability is an external `AtomicPersist` premise, not a Lean
field claimed to be true of a filesystem.

**Non-vacuity.** A full snapshot with one monitor and one claimable outpoint
satisfies the positive theorem; the existing
`inconsistent_snapshot_rolls_back` (`PersistenceRecovery.lean:618`) is the
channel-only special case of the stale-snapshot counterexample.

**Why faithful.** LDK loads `ChannelMonitor` state and syncs it before
events (`builder.rs:2013-2050`, `lib.rs:388-398`); the server backup pair is
mnemonic + sqlite/Postgres (`docs/operations.md:49-66`).  The current Lean
snapshot excludes exactly the monitor/claim/event state that the LDK
restart test exercises (`postgres.rs:331-410`).

**Fidelity risk / feasibility.** High: per-object atomicity in
`data_store.rs:436-468` is not a multi-object transaction, and VSS is
explicitly experimental (`builder.rs:816-819`).  Medium-hard: new snapshot
layer; do not claim real fsync/DB durability.  Keep the existing
`Consistent` and stale-snapshot counterexamples.

## 5. Assumptions, counterexamples, and non-vacuity risks

### Preserved counterexamples and witnesses

* `storage_slots_fixed` (`Revocation.lean:316-319`) and
  `storage_slots_le_49` (`RevocationProps.lean:218-221`) are list-length
  facts about `List.finRange 49`; they do not constrain `RevocationStore.slots`.
  They must not be cited as evidence for a 49-slot storage bound.
* `provideSecret` (`Revocation.lean:281-289`) accepts any in-range
  `PerCommitmentSecret` and writes only slot 0.  A witness with
  `st = emptyStore`, `idx = 5`, and an arbitrary 32-byte `s ≠ sh.derive 5`
  yields `isRevoked (provideSecret st 5 s) i` for every `i ≤ 5`, even though
  the shachain secret is not known.  `BreachConfirmed` (`BreachProps.lean:107`)
  uses only that `minSeen` test, so it inherits the counterexample.
* `penaltyValid_key` (`Penalty.lean:195-199`) is the
  `RevocationScheme.consistent` equality, which is total in the scheme; it
  does not say `w.secret = revocationSecret sh c.number`.  Only
  `HonestPunishable` / `HoldsRevocationSecret` add that premise, and they are
  not part of the catalog's `LN-HT-006`.
* `breach_penalty_spends_both` (`Invariants.lean:299-303`) is a projection
  of `Breach.Punishable`; `revoked_commitment_is_old` (`:269-272`) is
  `Nat.ne_of_lt`.  Neither is a BOLT 5 coverage theorem.
* `penaltyTx_no_third_input` (`BreachProps.lean:449-461`) is the retained
  proof that the current two-input `PenaltyTx` cannot cover an HTLC output.
  `PenaltyHtlcCoverage` (`:177-186`) is a statement, not a proved obligation.
* `silentWatchtower` (`E35.lean:299-304`) is live and never reports;
  `waveE_e35_silent_watchtower_never_reports` (`:334`) and
  `waveE_e35_live_watchtower_alone_does_not_punish` (`:367`) must remain.
* `not_timely_at_deadline` (`BreachProps.lean:384`) and
  `no_punishable_after_window` (`:398`) preserve the half-open window
  `[breach, breach + window)`.  Do not replace `<` with `≤`.
* `inconsistent_snapshot_rolls_back` (`PersistenceRecovery.lean:618-635`)
  and `stale_snapshot_rolls_back` (`:513-518`) preserve the failure modes
  of torn and stale snapshots.  Do not make `Consistent` automatic.
* The positive concrete witnesses `concrete_cooperative_close_conserved`
  and `concrete_unilateral_close_conserved` (`CloseConservation.lean:446-467`)
  keep the arithmetic targets non-vacuous.
* `window_pos` (`WatchtowerBreach.lean:143-150`,
  `WatchtowerLiveness.lean:109-115`) keeps the contest window positive;
  any T2 replacement must retain an equivalent positivity/non-degeneracy
  lemma.

### Proposals that must not be accepted as stated

1. **Do not redefine `Watchtower.live` to imply `reports`.**  That would
   hide the central external assumption and invalidate
   `silentWatchtower`.  T6 keeps `liveReporting` as an explicit contract.
2. **Do not set `toSelfDelay := 0` or drop the `window ≤ toSelfDelay`
   premise.**  That makes T2 vacuous and re-admits penalties that confirm
   after the breacher's CSV spend.  A defaulted `toSelfDelay := 0` is only a
   source-compatibility device: every positive instantiation must supply the
   real old-commitment delay, and the existing `RevokedCommitment` literals
   (for example `sampleBreach` and `d34Commitment`) must be audited rather
   than silently left at the default.
3. **Do not strengthen `penaltySpendsBoth` to “both outputs are
   revocation-locked.”**  BOLT 3 `03-transactions.md:136-146` says the
   non-anchor `to_remote` is a plain P2WPKH to the holder; only the
   breacher's `to_local` and HTLC outputs carry the revocation branch.
4. **Do not add an HTLC guard to `Step.shutdown` and then claim existing
   reachability/liveness results are unchanged.**  `Liveness.lean:222` and
   `:642` use unguarded `Step.shutdown`; add `GuardedCooperativeClose` or
   update every call site in a reviewed diff.
5. **Do not claim `PersistenceRecovery` covers monitor/backup recovery.**
   Its snapshot is exactly counters, HTLCs, and `ready` (`:118-130`), and its
   docstring (`:79-96`) excludes fsync, watchtowers, and L1 recovery; there
   are no fields for monitors, revoked secrets, on-chain claims, or events.
6. **Do not treat `storage_slots_fixed` or `storage_slots_le_49` as a
   storage bound.**  They are `List.finRange` length computations; T1 is the
   actual store-content obligation.
7. **Do not derive watchtower punishment from `wt.live`.**  The only
   available direction is `reports → live` (`BreachProps.lean:140`);
   `watchtower_bridge` needs a report and a `BreachResponse`.

## 6. Wave-13 recommendation

**Recommendation: implement a narrow, additive P1 subset; defer the rest;
treat operational watchtower/backup guarantees as external.**

Safe wave-13 implementation lane:

1. **T1** store-content validity (`ValidFor` + `provideSecret` preservation)
   is additive, small, and directly removes the bogus-secret counterexample
   from the store layer without touching `isRevoked`.
2. **T2** contest-delay binding is additive (defaulted field + bridge +
   sharper timeliness theorem) and adds the late-penalty counterexample.
3. **T3** `ForceClose`/`ForceCloseStep` is a separate relation, so it does
   not destabilize the 435-theorem `Step` surface.
4. **T5** `shutdown_allows_pending_htlcs` plus `GuardedCooperativeClose`
   exposes the missing BOLT 2 guard without changing the existing
   `Step.shutdown` constructor.

Defer to wave 14 or a dedicated close lane:

* **T4** full per-output/HTLC penalty coverage: needs a list-valued
  transaction model and an explicit multi-transaction/pinning policy.
  Start only as a specification with no claim that one transaction covers
  every output.
* **T6** watchtower registration/persistence: the LDK Node/Server trees have
  no watchtower surface; the contract is operational and the liveness field
  is an external assumption.
* **T7** full monitor/backup snapshot: the durability semantics are external
  to Lean, and the current per-object store atomicity is not a multi-object
  transaction.

External/human barriers (not wave-13 implementation targets):

* real watchtower deployment, registration, secret custody, and broadcast;
* real filesystem/DB fsync and transactional backup semantics;
* VSS/remote persistence (explicitly alpha/experimental in LDK Node);
* backup/restore drills and the “do not restore onto two running nodes”
  operational warning (`docs/operations.md:65-66`);
* concrete secp256k1 verification and script execution for the penalty
  transaction (the existing `LN-L1-004` coverage is for `to_local`, not for
  `PenaltyTx`).

Do **not** claim end-to-end force-close/watchtower/backup fidelity in
wave 13.  The catalog remains 51/51 proved only at the literal statements
in §1.

## 7. Evidence and commands

Read-only inspection only.  No Lean build, no cargo test, no network fetch,
and no edit outside this report.

```sh
# Pin verification
git -C /tmp/opencode/ldk-refs/ldk-node rev-parse HEAD
# fa123fed131e27ecc420b77fa7086fcf1ddaebb8
git -C /tmp/opencode/ldk-refs/ldk-server rev-parse HEAD
# c17dc11dde38f88c53457039ddf30c6b90a63ba2

# Lean claim surface
rg -n "revoked_commitment_is_old|breach_penalty_spends_both|watchtower_bridge|penalty_economical" LnLean
rg -n "structure Shachain|structure RevocationScheme|structure RevocationStore|def provideSecret|def isRevoked|storage_slots" LnLean/Channel/Revocation.lean LnLean/Proofs/Channel/RevocationProps.lean
rg -n "structure RevokedCommitment|structure PenaltyTx|def penaltyValid|def timelyL1Confirmation" LnLean/Channel/Penalty.lean
rg -n "structure Watchtower|def Detectable|def BreachConfirmed|def HoldsRevocationSecret|def PenaltyHtlcCoverage" LnLean/Proofs/Channel/BreachProps.lean
rg -n "structure WatchtowerBreachRemedy|structure DetectionBeforeDeadline|structure BridgeAcceptance|watchtowerBreach_end_to_end" LnLean/Proofs/PhaseC3/WatchtowerBreach.lean
rg -n "eventually_detected_and_penalized|not_penalized_implies_assumption_failure" LnLean/Proofs/PhaseC3/WatchtowerLiveness.lean
rg -n "silentWatchtower|live_watchtower_alone_does_not_punish" LnLean/Proofs/WaveE/E35.lean
rg -n "structure Persisted|structure Snapshot|def Consistent|recovery_no_rollback_committed|inconsistent_snapshot_rolls_back" LnLean/Proofs/PhaseC3/PersistenceRecovery.lean
rg -n "cooperativeClose_conserved|unilateralClose_conserved|contestDelay_totalOutputValue" LnLean/Proofs/PhaseC3/CloseConservation.lean
rg -n "inductive ProtocolEvent|inductive Step|Step.shutdown|Step.closingSigned" LnLean/Channel/State.lean

# LDK behavior
sed -n '2239,2316p' /tmp/opencode/ldk-refs/ldk-node/src/lib.rs
sed -n '2153,2259p' /tmp/opencode/ldk-refs/ldk-node/src/event.rs
sed -n '1682,1725p' /tmp/opencode/ldk-refs/ldk-node/src/event.rs
sed -n '205,217p' /tmp/opencode/ldk-refs/ldk-node/src/balance.rs
sed -n '2013,2050p' /tmp/opencode/ldk-refs/ldk-node/src/builder.rs
sed -n '2220,2228p' /tmp/opencode/ldk-refs/ldk-node/src/builder.rs
sed -n '388,398p' /tmp/opencode/ldk-refs/ldk-node/src/lib.rs
sed -n '436,468p' /tmp/opencode/ldk-refs/ldk-node/src/data_store.rs
sed -n '44,58p' /tmp/opencode/ldk-refs/ldk-node/src/io/fs_store.rs
sed -n '23,48p' /tmp/opencode/ldk-refs/ldk-server/ldk-server/src/api/close_channel.rs
sed -n '49,66p' /tmp/opencode/ldk-refs/ldk-server/docs/operations.md
sed -n '252,274p' /tmp/opencode/ldk-refs/ldk-server/docs/configuration.md
sed -n '1062,1094p' /tmp/opencode/ldk-refs/ldk-server/e2e-tests/src/lib.rs
sed -n '1246,1285p' /tmp/opencode/ldk-refs/ldk-server/e2e-tests/src/lib.rs
sed -n '881,1050p' /tmp/opencode/ldk-refs/ldk-server/e2e-tests/tests/e2e.rs
sed -n '331,410p' /tmp/opencode/ldk-refs/ldk-server/e2e-tests/tests/postgres.rs

# No watchtower surface in the pinned trees
rg -i -n "watchtower|watch_tower" /tmp/opencode/ldk-refs/ldk-node /tmp/opencode/ldk-refs/ldk-server
# (no output)

# BOLT anchors
rg -n "Closing Initiation|shutdown|closing_signed" refs/bolts/02-peer-protocol.md
rg -n "Revoked Transaction Close Handling|to_local|to_remote|revocationpubkey|Efficient Per-commitment" refs/bolts/03-transactions.md refs/bolts/05-onchain.md
```

**Evidence limits.**  The report is source inspection, not mechanized
checking.  The positive targets in §4 are proposals; none has been added to
the tree.  The counterexamples in §5 are stated as proof sketches or
immediate consequences of the cited definitions; they were not run through
Lean in this review.
