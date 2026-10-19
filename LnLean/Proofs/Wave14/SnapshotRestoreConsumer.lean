import LnLean.Proofs.PhaseC3.PersistenceRecovery

/-!
# LnLean.Proofs.Wave14.SnapshotRestoreConsumer

## English claim

This module is a **consumer-facing** restatement of the stale-snapshot warning
in `LnLean.Proofs.PhaseC3.PersistenceRecovery`.  The existing module defines
`Stale s c r` as "`s` is consistent with `c`, and some state `c'` reachable
from `c` has a strictly larger local commitment counter", but its theorem
`stale_snapshot_rolls_back` only returns the second conjunct of that
definition.  It never mentions `Snapshot.restore`, so a reader could take the
name to mean that the *restore operation* has been shown to roll back.  It has
not: the rollback is an arithmetic fact about the snapshot's counter, and the
consumer has to connect it to `restore`.

This module closes that consumer gap additively:

1. `stale_snapshot_restore_loses_update` applies `Snapshot.restore` and
   exhibits a reachable later state whose local commitment counter is strictly
   above the restored counter.
2. `stale_snapshot_not_latest` states the equivalent negative form: the
   restored snapshot is not a latest-prefix selector.
3. `stale_snapshot_restoreChannel_loses_update` repeats the first result for
   `Snapshot.restoreChannel`, which is what a consumer restoring a live
   `Channel` actually calls.
4. A concrete witness (`witnessSnapshot` at local counter 3,
   `witnessChannel` at local counter 3, and `witnessLater` at counter 5,
   reachable by two `revoke_and_ack` steps) shows that neither `Stale` nor the
   restore theorem is vacuous.  `witness_stale`, `witness_restore_strictly_below`,
   `witness_loses_update`, and `witness_not_latest` are fully evaluated.

## What this module does and does not prove

* It does **not** change `Stale`, `Snapshot.restore`, `Snapshot.restoreChannel`,
  or `stale_snapshot_rolls_back`.  It is additive.
* It does **not** prove durability, atomic snapshot writes, fsync ordering, or
  that a particular persistence implementation ever takes the latest snapshot.
  Those remain external assumptions; `RecoveryPoint.consistent` is still the
  atomic-snapshot hypothesis, and `RecoveryPoint.replays_full_history` is still
  the positive recovery result under it.
* The value of the headline theorems is **consumer discipline**, not new
  mathematics: both are immediate consequences of `Stale`'s second conjunct
  plus the definitional equation `s.restore.localCommitmentNumber =
  s.localCommitmentNumber`.  They exist so a downstream consumer cites a named
  restore theorem instead of re-deriving the projection, and so the stale-case
  warning cannot be mistaken for a rollback theorem about `restore`.
* The witness uses two `revoke_and_ack` steps, which the lifecycle `Step`
  permits from a normal-phase channel.  That is the model's transition, not a
  claim that two acknowledgements without an intervening
  `commitment_signed` are wire-legal; `ChannelReestablishProps` already records
  that modelling gap.
-/

namespace LnLean.Proofs.Wave14.SnapshotRestoreConsumer

set_option autoImplicit false

open LnLean
open LnLean.Channel
open LnLean.Protocol (ChannelRecord ReestablishFields)
open LnLean.Proofs.PhaseC3

/-! ## 1. Restore-facing consequences of `Stale` -/

/-- **A stale snapshot's restore loses a reachable update.**  If `s` is stale
with respect to `c`, then restoring `s` and comparing its local commitment
counter with a reachable later state `c'` leaves the restored counter strictly
below `c'`.  The conclusion is about `s.restore`, not about `s` alone. -/
theorem stale_snapshot_restore_loses_update {s : Snapshot} {c : Channel}
    {r : ChannelRecord} (h : Stale s c r) :
    ∃ c' : Channel, Reachable c c' ∧
      s.restore.localCommitmentNumber < c'.localCommitmentNumber := by
  obtain ⟨_, c', hreach, hgt⟩ := h
  exact ⟨c', hreach, by simpa [Snapshot.restore] using hgt⟩

/-- **A stale snapshot's restore is not the latest state.**  No restored stale
snapshot dominates every state reachable from the snapshot point.  This is the
negative form a "latest-prefix selector" consumer needs: `Stale` is exactly a
counterexample to that selector. -/
theorem stale_snapshot_not_latest {s : Snapshot} {c : Channel}
    {r : ChannelRecord} (h : Stale s c r) :
    ¬ (∀ c' : Channel, Reachable c c' →
        c'.localCommitmentNumber ≤ s.restore.localCommitmentNumber) := by
  obtain ⟨_, c', hreach, hgt⟩ := h
  have hlt : s.restore.localCommitmentNumber < c'.localCommitmentNumber := by
    simpa [Snapshot.restore] using hgt
  intro hlatest
  exact (Nat.not_lt.mpr (hlatest c' hreach)) hlt

/-- **The same loss when restoring into a live channel.**  A consumer that
calls `Snapshot.restoreChannel` instead of reading `Snapshot.restore` gets the
same counter: the restored channel's local commitment number is strictly below
the reachable later state's. -/
theorem stale_snapshot_restoreChannel_loses_update {s : Snapshot} {c : Channel}
    {r : ChannelRecord} (h : Stale s c r) :
    ∃ c' : Channel, Reachable c c' ∧
      (s.restoreChannel c).localCommitmentNumber < c'.localCommitmentNumber := by
  obtain ⟨_, c', hreach, hgt⟩ := h
  exact ⟨c', hreach, by simpa [Snapshot.restoreChannel] using hgt⟩

/-! ## 2. Concrete non-vacuity witness

The witness is a normal-phase channel at local counter 3 with an empty HTLC
set, its persisted record, a snapshot taken at that same point, and a later
state at local counter 5 reached by two `revoke_and_ack` lifecycle steps. -/

/-- Snapshot taken at the intermediate local commitment counter 3. -/
def witnessSnapshot : Snapshot where
  localCommitmentNumber := 3
  remoteCommitmentNumber := 0
  htlcs := []
  ready := false

/-- Live channel at the same point as `witnessSnapshot`. -/
def witnessChannel : Channel :=
  { LnLean.Proofs.Protocol.sampleChannel with
      localCommitmentNumber := 3 }

/-- Peer record paired with `witnessChannel`.  It retains no outbound
messages, so its persisted ready flag is `false`, matching
`witnessSnapshot.ready`. -/
def witnessRecord : ChannelRecord where
  channelId := witnessChannel.channelId
  reestablish := ReestablishFields.initial

/-- A later state reachable from `witnessChannel` with local counter 5. -/
def witnessLater : Channel :=
  { witnessChannel with localCommitmentNumber := 5 }

/-- The witness snapshot is consistent with the witness channel and record. -/
theorem witness_consistent :
    witnessSnapshot.Consistent witnessChannel witnessRecord := by
  rfl

/-- The later state is reachable from the witness channel: two lifecycle
`revoke_and_ack` steps take the local counter from 3 to 5. -/
theorem witness_reachable : Reachable witnessChannel witnessLater := by
  have h1 : Step witnessChannel ProtocolEvent.revokeAndAck
      { witnessChannel with localCommitmentNumber := 4 } := by
    simpa [witnessChannel] using
      (Step.revokeAndAck witnessChannel
        (by simp [witnessChannel, LnLean.Proofs.Protocol.sampleChannel]))
  have h2 : Step { witnessChannel with localCommitmentNumber := 4 }
      ProtocolEvent.revokeAndAck witnessLater := by
    simpa [witnessLater] using
      (Step.revokeAndAck { witnessChannel with localCommitmentNumber := 4 }
        (by simp [witnessChannel, LnLean.Proofs.Protocol.sampleChannel]))
  exact Reachable.step (Reachable.of_step h1) h2

/-- The witness is genuinely stale: the snapshot at 3 misses the reachable
state at 5. -/
theorem witness_stale : Stale witnessSnapshot witnessChannel witnessRecord := by
  refine ⟨witness_consistent, witnessLater, witness_reachable, ?_⟩
  simp [witnessSnapshot, witnessLater]

/-- Restoring the witness snapshot yields exactly the snapshot counter 3. -/
theorem witness_restore_eq :
    witnessSnapshot.restore.localCommitmentNumber = 3 := rfl

/-- The restored witness counter is strictly below the reachable later state. -/
theorem witness_restore_strictly_below :
    witnessSnapshot.restore.localCommitmentNumber <
      witnessLater.localCommitmentNumber := by
  simp [witnessSnapshot, witnessLater, Snapshot.restore]

/-- The headline restore theorem applies non-vacuously, with `witnessLater` as
the explicit later state. -/
theorem witness_loses_update :
    ∃ c' : Channel, Reachable witnessChannel c' ∧
      witnessSnapshot.restore.localCommitmentNumber < c'.localCommitmentNumber := by
  exact ⟨witnessLater, witness_reachable, witness_restore_strictly_below⟩

/-- The negative latest-prefix theorem applies non-vacuously to the witness:
the restored counter 3 does not dominate the reachable counter 5. -/
theorem witness_not_latest :
    ¬ (∀ c' : Channel, Reachable witnessChannel c' →
        c'.localCommitmentNumber ≤
          witnessSnapshot.restore.localCommitmentNumber) :=
  stale_snapshot_not_latest witness_stale

/-! ## 3. Axiom audit -/

#print axioms stale_snapshot_restore_loses_update
#print axioms stale_snapshot_not_latest
#print axioms stale_snapshot_restoreChannel_loses_update
#print axioms witness_stale
#print axioms witness_loses_update
#print axioms witness_not_latest

end LnLean.Proofs.Wave14.SnapshotRestoreConsumer
