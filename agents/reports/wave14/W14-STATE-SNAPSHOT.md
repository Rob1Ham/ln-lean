# W14-STATE-SNAPSHOT — consumer-facing stale-snapshot restore theorems

**Lane:** W14-STATE-SNAPSHOT (Wave 14)
**Worktree:** `/home/ubuntu/ln-lean-waveh`
**Branch:** `wave-14/16`
**Base:** `a331b71`
**Status:** complete; scoped build green.

## 1. Scope

Add a consumer-facing stale-snapshot restore theorem on top of
`LnLean.Proofs.PhaseC3.PersistenceRecovery` **without changing** `Stale`,
`Snapshot.restore`, `Snapshot.restoreChannel`, or
`stale_snapshot_rolls_back`. The lane also supplied a concrete non-vacuity
witness and an axiom audit.

The added module is intentionally additive. Existing declarations, statements,
and docstrings in `PersistenceRecovery.lean` are untouched.

## 2. Owned files

Only these files were created or modified:

- `LnLean/Proofs/Wave14/SnapshotRestoreConsumer.lean`
- `agents/reports/wave14/W14-STATE-SNAPSHOT.md`

No shared file, root import, audit file, catalog file, script, docs file, or
other lane's report was edited. `git status --short` shows only the new
`LnLean/Proofs/Wave14/` directory and the new
`agents/reports/wave14/` report (plus the pre-existing untracked
`agents/swarm/WAVE-14.md` that this lane did not touch).

## 3. Headline declarations and exact statements

All declarations live in namespace
`LnLean.Proofs.Wave14.SnapshotRestoreConsumer` and import
`LnLean.Proofs.PhaseC3.PersistenceRecovery`.

```lean
theorem stale_snapshot_restore_loses_update {s : Snapshot} {c : Channel}
    {r : ChannelRecord} (h : Stale s c r) :
    ∃ c' : Channel, Reachable c c' ∧
      s.restore.localCommitmentNumber < c'.localCommitmentNumber
```

```lean
theorem stale_snapshot_not_latest {s : Snapshot} {c : Channel}
    {r : ChannelRecord} (h : Stale s c r) :
    ¬ (∀ c' : Channel, Reachable c c' →
        c'.localCommitmentNumber ≤ s.restore.localCommitmentNumber)
```

Supporting consumer theorem (the live-channel form):

```lean
theorem stale_snapshot_restoreChannel_loses_update {s : Snapshot} {c : Channel}
    {r : ChannelRecord} (h : Stale s c r) :
    ∃ c' : Channel, Reachable c c' ∧
      (s.restoreChannel c).localCommitmentNumber < c'.localCommitmentNumber
```

The two headline theorems apply `Snapshot.restore` in the conclusion. They do
not merely return `Stale`'s existential: they transport it through the
definitional equation `s.restore.localCommitmentNumber = s.localCommitmentNumber`
(and likewise for `restoreChannel`). The negative theorem converts the same
fact into the failure of a latest-prefix selector.

## 4. Concrete non-vacuity witness

Witness definitions (all fully evaluated, no hypotheses):

- `witnessSnapshot` — `Snapshot` with `localCommitmentNumber = 3`,
  `remoteCommitmentNumber = 0`, `htlcs = []`, `ready = false`.
- `witnessChannel` — `LnLean.Proofs.Protocol.sampleChannel` with
  `localCommitmentNumber := 3`; phase is `normal`.
- `witnessRecord` — `ChannelRecord` with `ReestablishFields.initial` and no
  retained outbound messages.
- `witnessLater` — `witnessChannel` with `localCommitmentNumber := 5`.

Witness theorems:

- `witness_consistent : witnessSnapshot.Consistent witnessChannel witnessRecord`
  — closes by `rfl`.
- `witness_reachable : Reachable witnessChannel witnessLater` — two lifecycle
  `Step.revokeAndAck` steps take the counter from 3 to 4 to 5.
- `witness_stale : Stale witnessSnapshot witnessChannel witnessRecord` — uses
  the reachable later state at 5.
- `witness_restore_eq : witnessSnapshot.restore.localCommitmentNumber = 3` —
  `rfl`.
- `witness_restore_strictly_below :
  witnessSnapshot.restore.localCommitmentNumber <
    witnessLater.localCommitmentNumber` — `3 < 5`.
- `witness_loses_update` — instantiates the headline existential with
  `witnessLater`.
- `witness_not_latest` — instantiates the negative latest-prefix theorem with
  the same witness.

This is a snapshot at the intermediate counter 3, a reachable state at counter
5, and a restore result at 3, strictly below 5. `Stale` is therefore
inhabited, and both headline theorems are applied non-vacuously.

## 5. Build command and result

```sh
cd /home/ubuntu/ln-lean-waveh
export PATH=/dev/shm/btc/elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
LEAN_NUM_THREADS=1 flock -w 3600 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Proofs.Wave14.SnapshotRestoreConsumer
```

Result:

```text
ℹ [141/141] Built LnLean.Proofs.Wave14.SnapshotRestoreConsumer (668ms)
Build completed successfully (141 jobs).
```

There are no `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, or
`@[implemented_by]` uses in the module. The only warnings in the build log are
pre-existing deprecation warnings from `LnLean/Proofs/Routing/GossipProps.lean`
and unrelated to this module.

## 6. `#print axioms` output

The module itself runs the following commands; the build printed:

```text
info: LnLean/Proofs/Wave14/SnapshotRestoreConsumer.lean:185:0:
  'LnLean.Proofs.Wave14.SnapshotRestoreConsumer.stale_snapshot_restore_loses_update'
  depends on axioms: [propext]
info: LnLean/Proofs/Wave14/SnapshotRestoreConsumer.lean:186:0:
  'LnLean.Proofs.Wave14.SnapshotRestoreConsumer.stale_snapshot_not_latest'
  depends on axioms: [propext]
info: LnLean/Proofs/Wave14/SnapshotRestoreConsumer.lean:187:0:
  'LnLean.Proofs.Wave14.SnapshotRestoreConsumer.stale_snapshot_restoreChannel_loses_update'
  depends on axioms: [propext]
info: LnLean/Proofs/Wave14/SnapshotRestoreConsumer.lean:188:0:
  'LnLean.Proofs.Wave14.SnapshotRestoreConsumer.witness_stale'
  depends on axioms: [propext]
info: LnLean/Proofs/Wave14/SnapshotRestoreConsumer.lean:189:0:
  'LnLean.Proofs.Wave14.SnapshotRestoreConsumer.witness_loses_update'
  depends on axioms: [propext]
info: LnLean/Proofs/Wave14/SnapshotRestoreConsumer.lean:190:0:
  'LnLean.Proofs.Wave14.SnapshotRestoreConsumer.witness_not_latest'
  depends on axioms: [propext]
```

All six declarations depend only on `propext`, which is within the allowed
`propext` / `Quot.sound` / `Classical.choice` set.

## 7. Review gap closed or narrowed

**G17 / R32 §4 T7 (stale snapshot restore) — narrowed.** The original gap was
that `stale_snapshot_rolls_back` returns `h.2` and never applies `restore`, so
no theorem connected a stale snapshot to a restore result or to a
latest-prefix selector. This lane now provides:

- a named theorem whose conclusion is explicitly about
  `Snapshot.restore.localCommitmentNumber` and a reachable later state;
- a companion theorem for `Snapshot.restoreChannel` (the live-channel consumer
  path);
- a negative "not latest" theorem that a latest-prefix selector consumer can
  cite directly;
- a concrete 3 → 5 witness proving the statements are not vacuous.

**What remains narrow/external:**

- The value is consumer discipline, not new mathematics. Both headline
  statements are immediate consequences of `Stale`'s second conjunct plus the
  definitional projection of `restore`; they are not an independent safety
  result.
- Neither theorem proves durability, atomic snapshot writes, fsync ordering, or
  that a real persistence implementation ever selects the latest snapshot.
  `RecoveryPoint.consistent` remains an explicit atomic-snapshot hypothesis,
  and `RecoveryPoint.replays_full_history` remains the positive recovery result
  under that assumption.
- The witness uses two `revoke_and_ack` lifecycle steps without an intervening
  `commitment_signed`. That is the existing `Step` model's transition; this lane
  does not claim it is wire-legal. `ChannelReestablishProps` already records the
  corresponding model gap.

## 8. Shared-file changes for the integrator (stated, not applied)

The integrator may need to:

1. **Root import:** add `import LnLean.Proofs.Wave14.SnapshotRestoreConsumer`
   to the Wave 14 aggregator / regenerate the root with
   `scripts/regen-root.sh`. This lane did not edit `LnLean.lean` or any
   aggregator.
2. **Axiom audit registry:** if Wave 14 headlines are enrolled in
   `LnLean/Proofs/PhaseC3/AxiomAudit.lean`, add the six theorem names
   (`stale_snapshot_restore_loses_update`, `stale_snapshot_not_latest`,
   `stale_snapshot_restoreChannel_loses_update`, `witness_stale`,
   `witness_loses_update`, `witness_not_latest`) and matching `#print axioms`
   lines. The expected result is `[propext]` for each.
3. **Catalog/docs wording:** consider a catalog/`docs/OPEN-ISSUES.md` row that
   points `REV-06` at the new restore-facing theorem and records that the
   latest-prefix selector is still not implemented in production.
4. **Docstring correction (recommended, not applied):** `stale_snapshot_rolls_back`
   currently says "A stale but consistent snapshot would roll the counter
   back"; it would be more precise as "A stale but consistent snapshot can
   carry a counter below a reachable later state; this is not a theorem about
   `Snapshot.restore`." This lane did not alter the existing docstring, per
   the ownership contract.

## 9. Ownership confirmation

No shared or other-lane file was edited. Only the two owned paths listed in
§2 were written. No `git add`, `git commit`, `git push`, `git switch`, or other
Git write command was run. No network command was run. The scoped build was
the only build invoked, under the shared lock.
