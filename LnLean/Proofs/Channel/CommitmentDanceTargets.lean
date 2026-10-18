import LnLean.Channel.Revocation
import LnLean.Channel.State
import LnLean.Proofs.Channel.StateTransitionTargets
import LnLean.Proofs.WaveE.E37

/-!
# LnLean.Proofs.Channel.CommitmentDanceTargets

English claim (obligation `MODEL-03` / `MODEL-02`).  BOLT 2 §3 pairs
`commitment_signed` and `revoke_and_ack` into one commitment round
(`refs/bolts/02-peer-protocol.md:3097-3249`).  The lifecycle relation
`LnLean.Channel.Step` records both messages but deliberately does not relate
their counters, and the wave-5 `UpdateStep` layer records the HTLC messages
without the round that commits them.  This module proves the reachable-state
invariants of the additive ordered layer `LnLean.Channel.DanceStep`:

1. **Round window.**  Every non-reflexive `DanceReachable` target satisfies
   `DanceOrdered`: `local ≤ remote ≤ local + 1`.  The guards are load-bearing:
   an unguarded `Step` permits two consecutive `commitment_signed` messages
   (`unguarded_double_commitmentSigned_breaks_ordering`) or a
   `revoke_and_ack` before any `commitment_signed`
   (`unguarded_revokeAndAck_from_idle_breaks_ordering`).
2. **No stale commitment.**  A commitment number that is revoked (below the
   local watermark) is never the current local or remote commitment of a
   reachable ordered state (`danceReachable_revoked_never_current`), and the
   remote commitment being signed is not already revoked
   (`commitmentSigned_source_remote_not_revoked`).  The unguarded lifecycle
   relation can sign a revoked commitment
   (`unguarded_step_signs_revoked_commitment`).
3. **Revocation ordering.**  Local and remote counters are monotone along a
   dance trace, `revoke_and_ack` strictly advances the local counter and
   revokes exactly the previous local commitment, and the induced
   `RevocationStore` view agrees with `CommitmentRevoked`.
4. **Balance and ledger preservation.**  A dance step changes only the two
   commitment counters, so it preserves the balance, the HTLC list, the
   funding value, E37's ledger value, and `ReserveInvariant`; the results lift
   to `DanceReachable`.
5. **Compatibility.**  Every dance trace is also a `Reachable` trace and an
   `UpdateReachable` trace, so the wave-5 conservation and reserve theorems
   apply verbatim.  The wave-5 unguarded-add counterexample is re-exported
   unchanged.

The dance is kept as a separate event and relation.  Folding it into
`ProtocolEvent`/`Step` would require changing the *unguarded* lifecycle
constructors and would break the exhaustive `step?` matcher and every
`Step`-shaped balance/HTLC preservation theorem; the exact migration list is
in `agents/reports/swarm6/S6-MODEL-DANCE.md`.

BOLT anchors.
* BOLT 2 §3 `commitment_signed` (`02-peer-protocol.md:3097-3205`) and
  `revoke_and_ack` (`:3206-3249`).
* BOLT 2 `AwaitingRemoteRevoke`: a second `commitment_signed` is held until
  the peer's `revoke_and_ack` arrives
  (`lightning/src/ln/channel.rs:773-776` at pinned `fe49009`).
* BOLT 3 per-commitment secret ordering
  (`refs/bolts/03-transactions.md:828-860`) is used only through the
  `RevocationStore` watermark; the concrete shachain remains abstract.

What is NOT modelled.
* The pending-update queue drained by a round.  `DanceStep` changes counters
  only; `UpdateStep` changes balances/HTLCs only, and the two are not composed
  into a single `channel_reestablish`-aware pipeline here.
* Signatures, per-commitment points, and the wire payload of
  `commitment_signed` (`CommitmentSigned` in `LnLean.Protocol.Messages`).
* The BOLT 3 `2^48` counter bound.  `danceStore` takes it as an explicit
  hypothesis because the `Channel` record does not enforce it.
-/

namespace LnLean.Proofs.Channel.CommitmentDanceTargets

set_option autoImplicit false

open LnLean
open LnLean.Channel
open LnLean.Proofs.Channel
  (localReserveSat remoteReserveSat ReserveInvariant)
open LnLean.Proofs.Channel.StateTransitionTargets

/-! ## Successor projections

Both dance successors touch exactly one counter.  These `rfl` lemmas are the
whole of the balance/HTLC preservation argument. -/

@[simp] theorem signRemoteCommitment_balance (c : Channel) :
    (signRemoteCommitment c).balance = c.balance := rfl

@[simp] theorem signRemoteCommitment_htlcs (c : Channel) :
    (signRemoteCommitment c).htlcs = c.htlcs := rfl

@[simp] theorem signRemoteCommitment_funding (c : Channel) :
    (signRemoteCommitment c).funding = c.funding := rfl

@[simp] theorem signRemoteCommitment_fundingValue (c : Channel) :
    (signRemoteCommitment c).fundingValue = c.fundingValue := rfl

@[simp] theorem signRemoteCommitment_phase (c : Channel) :
    (signRemoteCommitment c).phase = c.phase := rfl

@[simp] theorem signRemoteCommitment_localCommitmentNumber (c : Channel) :
    (signRemoteCommitment c).localCommitmentNumber = c.localCommitmentNumber := rfl

@[simp] theorem signRemoteCommitment_remoteCommitmentNumber (c : Channel) :
    (signRemoteCommitment c).remoteCommitmentNumber =
      c.remoteCommitmentNumber + 1 := rfl

@[simp] theorem revokeLocalCommitment_balance (c : Channel) :
    (revokeLocalCommitment c).balance = c.balance := rfl

@[simp] theorem revokeLocalCommitment_htlcs (c : Channel) :
    (revokeLocalCommitment c).htlcs = c.htlcs := rfl

@[simp] theorem revokeLocalCommitment_funding (c : Channel) :
    (revokeLocalCommitment c).funding = c.funding := rfl

@[simp] theorem revokeLocalCommitment_fundingValue (c : Channel) :
    (revokeLocalCommitment c).fundingValue = c.fundingValue := rfl

@[simp] theorem revokeLocalCommitment_phase (c : Channel) :
    (revokeLocalCommitment c).phase = c.phase := rfl

@[simp] theorem revokeLocalCommitment_localCommitmentNumber (c : Channel) :
    (revokeLocalCommitment c).localCommitmentNumber =
      c.localCommitmentNumber + 1 := rfl

@[simp] theorem revokeLocalCommitment_remoteCommitmentNumber (c : Channel) :
    (revokeLocalCommitment c).remoteCommitmentNumber =
      c.remoteCommitmentNumber := rfl

/-! ## Guard extraction -/

/-- A `commitment_signed` transition starts a round: no round is in flight. -/
theorem danceStep_commitmentSigned_requires_idle {c c' : Channel}
    (h : DanceStep c .commitmentSigned c') :
    c.remoteCommitmentNumber = c.localCommitmentNumber := by
  cases h
  assumption

/-- A `revoke_and_ack` transition closes a round: exactly one signature is
outstanding. -/
theorem danceStep_revokeAndAck_requires_pending {c c' : Channel}
    (h : DanceStep c .revokeAndAck c') :
    c.remoteCommitmentNumber = c.localCommitmentNumber + 1 := by
  cases h
  assumption

/-- The target of `commitment_signed` is the named successor. -/
theorem danceStep_commitmentSigned_target {c c' : Channel}
    (h : DanceStep c .commitmentSigned c') : c' = signRemoteCommitment c := by
  cases h
  rfl

/-- The target of `revoke_and_ack` is the named successor. -/
theorem danceStep_revokeAndAck_target {c c' : Channel}
    (h : DanceStep c .revokeAndAck c') : c' = revokeLocalCommitment c := by
  cases h
  rfl

/-- The two guards are mutually exclusive: a state with a round in flight has
no `commitment_signed`, and an idle state has no `revoke_and_ack`.  This is the
local form of the alternation invariant. -/
theorem no_commitmentSigned_with_round_in_flight {c c' : Channel}
    (hpending : c.remoteCommitmentNumber = c.localCommitmentNumber + 1) :
    ¬ DanceStep c .commitmentSigned c' := by
  intro h
  have hidle := danceStep_commitmentSigned_requires_idle h
  omega

theorem no_revokeAndAck_without_commitmentSigned {c c' : Channel}
    (hidle : c.remoteCommitmentNumber = c.localCommitmentNumber) :
    ¬ DanceStep c .revokeAndAck c' := by
  intro h
  have hpending := danceStep_revokeAndAck_requires_pending h
  omega

/-! ## The round window -/

/-- The gap between the two counters after a `commitment_signed` from an idle
state is exactly one. -/
theorem commitmentGap_signRemoteCommitment_of_idle {c : Channel}
    (hidle : c.remoteCommitmentNumber = c.localCommitmentNumber) :
    commitmentGap (signRemoteCommitment c) = 1 := by
  simp only [commitmentGap, signRemoteCommitment]
  omega

/-- The gap after the matching `revoke_and_ack` is zero. -/
theorem commitmentGap_revokeLocalCommitment_of_pending {c : Channel}
    (hpending : c.remoteCommitmentNumber = c.localCommitmentNumber + 1) :
    commitmentGap (revokeLocalCommitment c) = 0 := by
  simp only [commitmentGap, revokeLocalCommitment]
  omega

/-- Every dance source is already inside the round window.  The guards are
equal to (not merely implied by) the idle/pending conditions, so this is the
strongest statement available. -/
theorem danceStep_source_ordered {c c' : Channel} {e : DanceEvent}
    (h : DanceStep c e c') : DanceOrdered c := by
  cases h with
  | commitmentSigned _ hidle =>
      unfold DanceOrdered
      omega
  | revokeAndAck _ hpending =>
      unfold DanceOrdered
      omega

/-- Every dance target is inside the round window.  No initial-state
hypothesis is needed: the guards force the source window. -/
theorem danceStep_ordered {c c' : Channel} {e : DanceEvent}
    (h : DanceStep c e c') : DanceOrdered c' := by
  cases h with
  | commitmentSigned _ hidle =>
      refine ⟨?_, ?_⟩ <;> simp [signRemoteCommitment] <;> omega
  | revokeAndAck _ hpending =>
      refine ⟨?_, ?_⟩ <;> simp [revokeLocalCommitment] <;> omega

/-- **Reachable round window.**  Every non-reflexive dance-reachable state is
ordered.  At `refl` the source may be arbitrary, which is why the disjunction
is necessary. -/
theorem danceReachable_ordered_or_eq {a b : Channel} (h : DanceReachable a b) :
    a = b ∨ DanceOrdered b := by
  induction h with
  | refl => exact Or.inl rfl
  | step _ hs _ => exact Or.inr (danceStep_ordered hs)

/-- The non-reflexive form used by consumers. -/
theorem danceReachable_ordered {a b : Channel} (h : DanceReachable a b)
    (hne : a ≠ b) : DanceOrdered b :=
  (danceReachable_ordered_or_eq h).resolve_left hne

/-! ## Counter ordering and revocation -/

/-- The local commitment counter is monotone along one dance step. -/
theorem danceStep_local_le {c c' : Channel} {e : DanceEvent}
    (h : DanceStep c e c') :
    c.localCommitmentNumber ≤ c'.localCommitmentNumber := by
  cases h <;> simp [signRemoteCommitment, revokeLocalCommitment] <;> omega

/-- The remote commitment counter is monotone along one dance step. -/
theorem danceStep_remote_le {c c' : Channel} {e : DanceEvent}
    (h : DanceStep c e c') :
    c.remoteCommitmentNumber ≤ c'.remoteCommitmentNumber := by
  cases h <;> simp [signRemoteCommitment, revokeLocalCommitment] <;> omega

/-- `commitment_signed` strictly advances the remote counter. -/
theorem danceStep_commitmentSigned_remote_strict {c c' : Channel}
    (h : DanceStep c .commitmentSigned c') :
    c.remoteCommitmentNumber < c'.remoteCommitmentNumber := by
  cases h
  simp [signRemoteCommitment]

/-- `revoke_and_ack` strictly advances the local counter. -/
theorem danceStep_revokeAndAck_local_strict {c c' : Channel}
    (h : DanceStep c .revokeAndAck c') :
    c.localCommitmentNumber < c'.localCommitmentNumber := by
  cases h
  simp [revokeLocalCommitment]

/-- Revocation is monotone: a revoked commitment number stays revoked. -/
theorem commitmentRevoked_mono {c c' : Channel} {e : DanceEvent}
    (h : DanceStep c e c') {i : Nat} (hr : CommitmentRevoked c i) :
    CommitmentRevoked c' i := by
  unfold CommitmentRevoked at *
  have := danceStep_local_le h
  omega

/-- The current local commitment is never revoked. -/
theorem commitmentRevoked_current_local (c : Channel) :
    ¬ CommitmentRevoked c c.localCommitmentNumber := by
  unfold CommitmentRevoked
  omega

/-- In an ordered state the current remote commitment is never revoked either:
the revocation watermark is at most the remote counter.  This is the `no stale
commitment` invariant. -/
theorem commitmentRevoked_current_remote {c : Channel} (ho : DanceOrdered c) :
    ¬ CommitmentRevoked c c.remoteCommitmentNumber := by
  rcases ho with ⟨hl, hr⟩
  unfold CommitmentRevoked
  omega

/-- `revoke_and_ack` revokes exactly the previous local commitment. -/
theorem revokeAndAck_revokes_previous {c c' : Channel}
    (h : DanceStep c .revokeAndAck c') :
    CommitmentRevoked c' c.localCommitmentNumber := by
  unfold CommitmentRevoked
  have := danceStep_revokeAndAck_local_strict h
  omega

/-- The remote commitment being signed is not already revoked.  The unguarded
`Step.commitmentSigned` has no such guarantee; see
`unguarded_step_signs_revoked_commitment`. -/
theorem commitmentSigned_source_remote_not_revoked {c c' : Channel}
    (h : DanceStep c .commitmentSigned c') :
    ¬ CommitmentRevoked c c.remoteCommitmentNumber := by
  intro hr
  have hidle := danceStep_commitmentSigned_requires_idle h
  unfold CommitmentRevoked at hr
  omega

/-- Local counter monotonicity along a dance trace. -/
theorem danceReachable_local_le {a b : Channel} (h : DanceReachable a b) :
    a.localCommitmentNumber ≤ b.localCommitmentNumber := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ hs ih => exact Nat.le_trans ih (danceStep_local_le hs)

/-- Remote counter monotonicity along a dance trace. -/
theorem danceReachable_remote_le {a b : Channel} (h : DanceReachable a b) :
    a.remoteCommitmentNumber ≤ b.remoteCommitmentNumber := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ hs ih => exact Nat.le_trans ih (danceStep_remote_le hs)

/-- Revocation monotonicity along a dance trace. -/
theorem danceReachable_revoked_mono {a b : Channel} (h : DanceReachable a b)
    {i : Nat} (hr : CommitmentRevoked a i) : CommitmentRevoked b i := by
  induction h with
  | refl => exact hr
  | step _ hs ih => exact commitmentRevoked_mono hs ih

/-- **No stale commitment along a trace.**  A number revoked at the start is
never the current local or remote commitment of a non-reflexive ordered
target. -/
theorem danceReachable_revoked_never_current {a b : Channel}
    (h : DanceReachable a b) (hne : a ≠ b) {i : Nat}
    (hr : CommitmentRevoked a i) :
    i ≠ b.localCommitmentNumber ∧ i ≠ b.remoteCommitmentNumber := by
  have hb : CommitmentRevoked b i := danceReachable_revoked_mono h hr
  have ho : DanceOrdered b := danceReachable_ordered h hne
  rcases ho with ⟨hl, _hr⟩
  unfold CommitmentRevoked at hb
  constructor <;> omega

/-- **No stale current commitment.**  Neither current commitment number of a
non-reflexive ordered target is below the revocation watermark. -/
theorem danceReachable_current_not_revoked {a b : Channel}
    (h : DanceReachable a b) (hne : a ≠ b) :
    ¬ CommitmentRevoked b b.localCommitmentNumber ∧
      ¬ CommitmentRevoked b b.remoteCommitmentNumber := by
  have ho : DanceOrdered b := danceReachable_ordered h hne
  exact ⟨commitmentRevoked_current_local b, commitmentRevoked_current_remote ho⟩

/-- A complete round advances both counters by exactly one and closes the
window: the pre-round commitment becomes revoked and the two counters agree
again. -/
theorem dance_round_closes {c c₁ c₂ : Channel}
    (h₁ : DanceStep c .commitmentSigned c₁)
    (h₂ : DanceStep c₁ .revokeAndAck c₂) :
    c₂.localCommitmentNumber = c.localCommitmentNumber + 1 ∧
      c₂.remoteCommitmentNumber = c.remoteCommitmentNumber + 1 ∧
      c₂.remoteCommitmentNumber = c₂.localCommitmentNumber ∧
      CommitmentRevoked c₂ c.localCommitmentNumber := by
  cases h₁ with
  | commitmentSigned _ hidle =>
      cases h₂ with
      | revokeAndAck _ hpending =>
          refine ⟨rfl, rfl, ?_, ?_⟩
          · simp [signRemoteCommitment, revokeLocalCommitment]
            omega
          · unfold CommitmentRevoked
            simp [signRemoteCommitment, revokeLocalCommitment]

/-! ## Balance, ledger, and reserve preservation -/

/-- A dance step changes neither balance. -/
theorem danceStep_balance_eq {c c' : Channel} {e : DanceEvent}
    (h : DanceStep c e c') : c'.balance = c.balance := by
  cases h <;> rfl

/-- A dance step changes no HTLC. -/
theorem danceStep_htlcs_eq {c c' : Channel} {e : DanceEvent}
    (h : DanceStep c e c') : c'.htlcs = c.htlcs := by
  cases h <;> rfl

/-- A dance step preserves the pending HTLC bucket. -/
theorem danceStep_pendingHtlcValueOf {c c' : Channel} {e : DanceEvent}
    (h : DanceStep c e c') :
    pendingHtlcValueOf c' = pendingHtlcValueOf c := by
  rw [pendingHtlcValueOf_eq_listPending, pendingHtlcValueOf_eq_listPending,
    danceStep_htlcs_eq h]

/-- A dance step preserves the funding value. -/
theorem danceStep_fundingValue_eq {c c' : Channel} {e : DanceEvent}
    (h : DanceStep c e c') : c'.fundingValue = c.fundingValue := by
  cases h <;> rfl

/-- A dance step preserves E37's ledger value. -/
theorem danceStep_ledgerValue {c c' : Channel} {e : DanceEvent}
    (h : DanceStep c e c') (fee : Msat) :
    LnLean.Proofs.WaveE.E37.ledgerValue c' fee =
      LnLean.Proofs.WaveE.E37.ledgerValue c fee := by
  rw [LnLean.Proofs.Channel.StateTransitionTargets.ledgerValue_eq,
    LnLean.Proofs.Channel.StateTransitionTargets.ledgerValue_eq]
  simp [pendingHtlcValueOf, danceStep_balance_eq h, danceStep_htlcs_eq h]

/-- **Ledger conservation of one dance step**, in the funding-value form used
by the wave-5 update layer. -/
theorem danceStep_preserves_ledger {c c' : Channel} {e : DanceEvent}
    (h : DanceStep c e c') (fee : Msat)
    (hled : LnLean.Proofs.WaveE.E37.ledgerValue c fee = c.fundingValue.val) :
    LnLean.Proofs.WaveE.E37.ledgerValue c' fee = c'.fundingValue.val := by
  rw [danceStep_ledgerValue h fee, danceStep_fundingValue_eq h]
  exact hled

/-- A dance step preserves `ReserveInvariant`: neither balance nor either
reserve parameter changes. -/
theorem danceStep_preserves_reserve {c c' : Channel} {e : DanceEvent}
    (h : DanceStep c e c') (hres : ReserveInvariant c) :
    ReserveInvariant c' := by
  rcases hres with ⟨hl, hr⟩
  cases h <;>
    simpa [ReserveInvariant, localReserveSat, remoteReserveSat,
      reserveSatisfied, Balance.localSat, Balance.remoteSat,
      signRemoteCommitment, revokeLocalCommitment] using And.intro hl hr

/-- Ledger conservation along a dance trace. -/
theorem danceReachable_preserves_ledger {a b : Channel}
    (h : DanceReachable a b) (fee : Msat)
    (hled : LnLean.Proofs.WaveE.E37.ledgerValue a fee = a.fundingValue.val) :
    LnLean.Proofs.WaveE.E37.ledgerValue b fee = b.fundingValue.val := by
  induction h with
  | refl => exact hled
  | step _ hs ih => exact danceStep_preserves_ledger hs fee ih

/-- Reserve preservation along a dance trace. -/
theorem danceReachable_preserves_reserve {a b : Channel}
    (h : DanceReachable a b) (hres : ReserveInvariant a) :
    ReserveInvariant b := by
  induction h with
  | refl => exact hres
  | step _ hs ih => exact danceStep_preserves_reserve hs ih

/-! ## Compatibility with the lifecycle and update layers -/

/-- Every dance step is an `UpdateStep` lifecycle step. -/
theorem danceStep_toUpdateStep {hashFn : ByteArray → ByteArray}
    {c c' : Channel} {e : DanceEvent} (h : DanceStep c e c') :
    UpdateStep hashFn c (.lifecycle e.toProtocolEvent) c' :=
  UpdateStep.lifecycle (DanceStep.toStep h)

/-- Every dance trace is an `UpdateReachable` trace, so the wave-5 ledger and
reserve theorems apply verbatim. -/
theorem danceReachable_toUpdateReachable {hashFn : ByteArray → ByteArray}
    {a b : Channel} (h : DanceReachable a b) :
    UpdateReachable hashFn a b := by
  induction h with
  | refl => exact UpdateReachable.refl a
  | step _ hs ih => exact UpdateReachable.step ih (danceStep_toUpdateStep hs)

/-- Every dance trace is a lifecycle `Reachable` trace. -/
theorem danceReachable_toReachable {a b : Channel} (h : DanceReachable a b) :
    Reachable a b := by
  induction h with
  | refl => exact Reachable.refl a
  | step _ hs ih => exact Reachable.step ih (DanceStep.toStep hs)

/-- The wave-5 update-layer ledger theorem transported to dance traces. -/
theorem danceReachable_preserves_ledger_via_update
    {hashFn : ByteArray → ByteArray} {a b : Channel}
    (h : DanceReachable a b) (fee : Msat)
    (hled : LnLean.Proofs.WaveE.E37.ledgerValue a fee = a.fundingValue.val) :
    LnLean.Proofs.WaveE.E37.ledgerValue b fee = b.fundingValue.val :=
  LnLean.Proofs.Channel.StateTransitionTargets.updateReachable_preserves_ledger
    (danceReachable_toUpdateReachable (hashFn := hashFn) h) fee hled

/-- The wave-5 update-layer reserve theorem transported to dance traces. -/
theorem danceReachable_preserves_reserve_via_update
    {hashFn : ByteArray → ByteArray} {a b : Channel}
    (h : DanceReachable a b) (hres : ReserveInvariant a) :
    ReserveInvariant b :=
  LnLean.Proofs.Channel.StateTransitionTargets.updateReachable_preserves_reserve
    (danceReachable_toUpdateReachable (hashFn := hashFn) h) hres

/-! ## Revocation-store view -/

/-- The revocation store induced by a channel: every commitment number below
the local counter is revoked.  The BOLT 3 `2^48` bound is an explicit
hypothesis because `Channel` does not enforce it. -/
def danceStore (c : Channel)
    (hbound : c.localCommitmentNumber ≤ COMMITMENT_SECRET_COUNT) :
    RevocationStore where
  minSeen := c.localCommitmentNumber
  slots := fun _ => none
  minSeen_bound := hbound

@[simp] theorem danceStore_minSeen (c : Channel)
    (hbound : c.localCommitmentNumber ≤ COMMITMENT_SECRET_COUNT) :
    (danceStore c hbound).minSeen = c.localCommitmentNumber := rfl

/-- The dance predicate and the `RevocationStore` watermark agree exactly. -/
theorem danceStore_isRevoked_iff (c : Channel)
    (hbound : c.localCommitmentNumber ≤ COMMITMENT_SECRET_COUNT) (i : Nat) :
    LnLean.Channel.isRevoked (danceStore c hbound) i ↔ CommitmentRevoked c i :=
  Iff.rfl

/-- After a `revoke_and_ack`, the previous local commitment is revoked in the
`RevocationStore` view. -/
theorem danceStore_revoke_previous {c c' : Channel}
    (h : DanceStep c .revokeAndAck c')
    (hbound : c'.localCommitmentNumber ≤ COMMITMENT_SECRET_COUNT) :
    LnLean.Channel.isRevoked (danceStore c' hbound) c.localCommitmentNumber := by
  simpa [danceStore, LnLean.Channel.isRevoked, CommitmentRevoked] using
    revokeAndAck_revokes_previous h

/-- Every revoked index is inside the BOLT 3 secret range. -/
theorem danceStore_revoked_index_bound (c : Channel)
    (hbound : c.localCommitmentNumber ≤ COMMITMENT_SECRET_COUNT) {i : Nat}
    (hr : LnLean.Channel.isRevoked (danceStore c hbound) i) :
    i < COMMITMENT_SECRET_COUNT :=
  LnLean.Channel.isRevoked_index_bound _ hr

/-! ## Non-vacuity and retained counterexamples -/

/-- **Non-vacuity.**  A concrete two-round dance from a normal channel:
`commitment_signed`, `revoke_and_ack`, `commitment_signed`, `revoke_and_ack`.
The final state is ordered with both counters 2, commitments 0 and 1 are
revoked, and the ledger is preserved. -/
theorem dance_two_rounds_witness :
    ∃ (c c₁ c₂ c₃ c₄ : Channel),
      DanceReachable c c₄ ∧
        DanceStep c .commitmentSigned c₁ ∧
          DanceStep c₁ .revokeAndAck c₂ ∧
            DanceStep c₂ .commitmentSigned c₃ ∧
              DanceStep c₃ .revokeAndAck c₄ ∧
                DanceOrdered c₄ ∧
                  c₄.localCommitmentNumber = 2 ∧
                    c₄.remoteCommitmentNumber = 2 ∧
                      CommitmentRevoked c₄ 0 ∧
                        CommitmentRevoked c₄ 1 ∧
                          LnLean.Proofs.WaveE.E37.ledgerValue c₄ ⟨0⟩ =
                            c₄.fundingValue.val := by
  let c := LnLean.Proofs.WaveE.E37.testChannel 1000 1000 2000 0 1 1000
  let c₁ := signRemoteCommitment c
  let c₂ := revokeLocalCommitment c₁
  let c₃ := signRemoteCommitment c₂
  let c₄ := revokeLocalCommitment c₃
  have hphase : c.phase = ChannelPhase.normal := by
    simp [c, LnLean.Proofs.WaveE.E37.testChannel]
  have hidle₁ : c.remoteCommitmentNumber = c.localCommitmentNumber := by
    simp [c, LnLean.Proofs.WaveE.E37.testChannel]
  have h₁ : DanceStep c .commitmentSigned c₁ :=
    DanceStep.commitmentSigned c hphase hidle₁
  have hpending₁ : c₁.remoteCommitmentNumber = c₁.localCommitmentNumber + 1 := by
    simp [c₁, signRemoteCommitment, c, LnLean.Proofs.WaveE.E37.testChannel]
  have hphase₁ : c₁.phase = ChannelPhase.normal := by
    simp [c₁, signRemoteCommitment, c, LnLean.Proofs.WaveE.E37.testChannel]
  have h₂ : DanceStep c₁ .revokeAndAck c₂ :=
    DanceStep.revokeAndAck c₁ hphase₁ hpending₁
  have hidle₂ : c₂.remoteCommitmentNumber = c₂.localCommitmentNumber := by
    simp [c₂, c₁, revokeLocalCommitment, signRemoteCommitment, c,
      LnLean.Proofs.WaveE.E37.testChannel]
  have hphase₂ : c₂.phase = ChannelPhase.normal := by
    simp [c₂, c₁, revokeLocalCommitment, signRemoteCommitment, c,
      LnLean.Proofs.WaveE.E37.testChannel]
  have h₃ : DanceStep c₂ .commitmentSigned c₃ :=
    DanceStep.commitmentSigned c₂ hphase₂ hidle₂
  have hpending₃ : c₃.remoteCommitmentNumber = c₃.localCommitmentNumber + 1 := by
    simp [c₃, c₂, c₁, signRemoteCommitment, revokeLocalCommitment, c,
      LnLean.Proofs.WaveE.E37.testChannel]
  have hphase₃ : c₃.phase = ChannelPhase.normal := by
    simp [c₃, c₂, c₁, signRemoteCommitment, revokeLocalCommitment, c,
      LnLean.Proofs.WaveE.E37.testChannel]
  have h₄ : DanceStep c₃ .revokeAndAck c₄ :=
    DanceStep.revokeAndAck c₃ hphase₃ hpending₃
  have hr₁₂ : DanceReachable c c₂ :=
    DanceReachable.step (DanceReachable.step (DanceReachable.refl c) h₁) h₂
  have hr₃ : DanceReachable c c₃ := DanceReachable.step hr₁₂ h₃
  have hr : DanceReachable c c₄ := DanceReachable.step hr₃ h₄
  have hled : LnLean.Proofs.WaveE.E37.ledgerValue c ⟨0⟩ = c.fundingValue.val := by
    simp [c, LnLean.Proofs.WaveE.E37.testChannel,
      LnLean.Proofs.WaveE.E37.ledgerValue,
      LnLean.Proofs.WaveE.E37.pendingValue]
  refine ⟨c, c₁, c₂, c₃, c₄, hr, h₁, h₂, h₃, h₄, danceStep_ordered h₄,
    ?_, ?_, ?_, ?_, ?_⟩
  · simp [c₄, c₃, c₂, c₁, signRemoteCommitment, revokeLocalCommitment, c,
      LnLean.Proofs.WaveE.E37.testChannel]
  · simp [c₄, c₃, c₂, c₁, signRemoteCommitment, revokeLocalCommitment, c,
      LnLean.Proofs.WaveE.E37.testChannel]
  · unfold CommitmentRevoked
    simp [c₄, c₃, c₂, c₁, signRemoteCommitment, revokeLocalCommitment, c,
      LnLean.Proofs.WaveE.E37.testChannel]
  · unfold CommitmentRevoked
    simp [c₄, c₃, c₂, c₁, signRemoteCommitment, revokeLocalCommitment, c,
      LnLean.Proofs.WaveE.E37.testChannel]
  · exact danceReachable_preserves_ledger hr ⟨0⟩ hled

/-- **The wave-5 unguarded-add counterexample is retained.**  This is the
exact `StateTransitionTargets.unguarded_add_ledger_counterexample`, re-exported
so a consumer of the dance layer still sees that `AffordableAdd` is
load-bearing. -/
theorem unguarded_add_ledger_counterexample_retained :
    ∃ (c : Channel) (dir : Direction) (amount : Msat) (ph : PaymentHash)
        (cltv : Height) (fee : Msat),
      LnLean.Proofs.WaveE.E37.ledgerValue c fee = c.fundingValue.val ∧
        ¬ AffordableAdd c dir amount cltv ∧
          LnLean.Proofs.WaveE.E37.ledgerValue
              (updateAddHtlc c dir amount ph cltv) fee ≠
            (updateAddHtlc c dir amount ph cltv).fundingValue.val :=
  LnLean.Proofs.Channel.StateTransitionTargets.unguarded_add_ledger_counterexample

/-- **The unguarded lifecycle relation breaks the round window.**  Two
consecutive `Step.commitmentSigned` messages are legal from a normal channel,
although the second has a round already in flight.  The dance guard
(`no_commitmentSigned_with_round_in_flight`) is therefore not vacuous. -/
theorem unguarded_double_commitmentSigned_breaks_ordering :
    ∃ (c c₁ c₂ : Channel),
      Step c .commitmentSigned c₁ ∧
        Step c₁ .commitmentSigned c₂ ∧ ¬ DanceOrdered c₂ := by
  let c := LnLean.Proofs.WaveE.E37.testChannel 1000 1000 2000 0 1 1000
  let c₁ := signRemoteCommitment c
  let c₂ := signRemoteCommitment c₁
  have h₁ : Step c .commitmentSigned c₁ := Step.commitmentSigned c rfl
  have h₂ : Step c₁ .commitmentSigned c₂ := Step.commitmentSigned c₁ rfl
  refine ⟨c, c₁, c₂, h₁, h₂, ?_⟩
  unfold DanceOrdered
  simp [c₂, c₁, signRemoteCommitment, c,
    LnLean.Proofs.WaveE.E37.testChannel]

/-- **The unguarded lifecycle relation breaks revocation ordering.**  A
`Step.revokeAndAck` is legal from an idle channel, before any
`commitment_signed`, and leaves the local counter ahead of the remote one. -/
theorem unguarded_revokeAndAck_from_idle_breaks_ordering :
    ∃ (c c' : Channel), Step c .revokeAndAck c' ∧ ¬ DanceOrdered c' := by
  let c := LnLean.Proofs.WaveE.E37.testChannel 1000 1000 2000 0 1 1000
  let c' := revokeLocalCommitment c
  have h : Step c .revokeAndAck c' := Step.revokeAndAck c rfl
  refine ⟨c, c', h, ?_⟩
  unfold DanceOrdered
  simp [c', revokeLocalCommitment, c,
    LnLean.Proofs.WaveE.E37.testChannel]

/-- **The unguarded lifecycle relation can sign a revoked commitment.**  After
an unguarded `revoke_and_ack` the local watermark is 1 while the remote
counter is still 0; a subsequent `commitment_signed` signs remote commitment
number 0, which the watermark already marks revoked.  In the dance layer this
state is unreachable: `revoke_and_ack` requires a round in flight, and
`commitmentSigned_source_remote_not_revoked` rules the signature out. -/
theorem unguarded_step_signs_revoked_commitment :
    ∃ (c c₁ c₂ : Channel),
      Step c .revokeAndAck c₁ ∧
        Step c₁ .commitmentSigned c₂ ∧
          CommitmentRevoked c₂ c₁.remoteCommitmentNumber := by
  let c := LnLean.Proofs.WaveE.E37.testChannel 1000 1000 2000 0 1 1000
  let c₁ := revokeLocalCommitment c
  let c₂ := signRemoteCommitment c₁
  have h₁ : Step c .revokeAndAck c₁ := Step.revokeAndAck c rfl
  have h₂ : Step c₁ .commitmentSigned c₂ := Step.commitmentSigned c₁ rfl
  refine ⟨c, c₁, c₂, h₁, h₂, ?_⟩
  unfold CommitmentRevoked
  simp [c₂, c₁, signRemoteCommitment, revokeLocalCommitment, c,
    LnLean.Proofs.WaveE.E37.testChannel]

end LnLean.Proofs.Channel.CommitmentDanceTargets
