import LnLean.Channel.State
import LnLean.Proofs.Channel.StateMachineProps
import LnLean.Proofs.Channel.StateTransitionTargets
import LnLean.Proofs.Channel.CommitmentDanceTargets
import LnLean.Proofs.WaveE.E37

/-!
# LnLean.Proofs.Channel.ProtocolEventFoldTargets

English claim (obligations `MODEL-02` / `MODEL-03`).  Wave 5 added the HTLC
update messages as the additive relation `UpdateStep`; wave 6 added the ordered
`commitment_signed` / `revoke_and_ack` round as the additive relation
`DanceStep`.  Both layers were kept outside `ProtocolEvent`/`Step` because the
lifecycle relation is deliberately balance-, HTLC-, and phase-preserving, and
because the executable `step?` scheduler in `LnLean.Proofs.Liveness` matches
`ProtocolEvent` exhaustively.

This module supplies the *fold* in the only form that keeps the existing
theorems and counterexamples true:

1. **`GuardedStep` is the fold of the dance into the lifecycle relation.**
   It is `Step` with the two round constructors replaced by their BOLT 2
   ordered forms.  The exact characterization is
   `guardedStep_iff_step_and_guards`: a guarded step is a `Step` whose
   `commitment_signed` source is idle and whose `revoke_and_ack` source has
   one signature outstanding.  On every non-round message the two relations
   agree (`guardedStep_ofStep_iff`).
2. **`DanceStep` is exactly the round fragment of the fold**
   (`danceStep_iff_guardedStep`, `guardedStep_commitmentSigned_iff_danceStep`,
   `guardedStep_revokeAndAck_iff_danceStep`).  The additive dance layer is
   therefore not a second semantics: it is the guarded fragment of the
   existing lifecycle fold.
3. **`GuardedUpdateStep` is the single folded update relation.**
   Its `lifecycle` constructor embeds `GuardedStep`, and its three HTLC
   constructors are exactly `UpdateStep`'s.  It is a subrelation of
   `UpdateStep` (`guardedUpdateStep_toUpdateStep`), so every wave-5 ledger and
   reserve theorem applies unchanged.
4. **The fold carries the round window.**  Along any `GuardedUpdateReachable`
   trace that starts `DanceOrdered`, every state stays `DanceOrdered`; the
   current commitments are never revoked.  The unguarded `UpdateStep` cannot
   have this invariant because its `lifecycle` constructor embeds all of
   `Step`, including two consecutive `commitment_signed` messages.
5. **The literal folds are refuted, not assumed away.**
   `literal_round_fold_refuted` and `literal_revoke_fold_refuted` prove that
   `Step` itself cannot carry the dance guards (the wave-6 counterexamples
   would become false, and
   `LnLean.Proofs.Protocol.ChannelReestablishProps.reachable_counters_inconsistent`
   depends on the unguarded revoke).  `fold_cannot_both_preserve_balance_and_carry_add`
   proves that no relation can both preserve the balance invariant that D14,
   `LiquidityProps`, and `F03` rely on and carry an affordable
   `update_add_htlc`.  Those two results are the exact reason the fold is
   realized as a *subrelation* rather than by editing the constructors of
   `Step`.

All counterexamples are retained and re-exported.  Nothing in this module
changes `ProtocolEvent`, `Step`, `UpdateStep`, `DanceStep`, or any downstream
file; the exact patch that would be needed to make the fold literal is
recorded in `agents/reports/swarm7/S7-MODEL-FOLD.md`.

BOLT anchors.
* BOLT 2 §3 `commitment_signed` (`02-peer-protocol.md:3097-3205`),
  `revoke_and_ack` (`:3206-3249`), and the `AwaitingRemoteRevoke` hold
  (`lightning/src/ln/channel.rs:773-776` at pinned `fe49009`).
* BOLT 2 §3 `update_add_htlc` (`:2739-2831`),
  `update_fulfill_htlc` (`:2913-2930`), `update_fail_htlc` (`:2944-2960`).

What is NOT modelled.
* The pending-update queue drained by a commitment round.  The folded relation
  composes the *message effects*; it does not model which updates a given
  `commitment_signed` commits.
* Signatures, per-commitment points, and the wire payloads.
* Per-commitment-secret derivation.  `CommitmentRevoked` remains the local
  watermark used by waves 5-6.
* The `2^48` counter bound; no arithmetic wrap-around is modelled.
-/

namespace LnLean.Proofs.Channel.ProtocolEventFoldTargets

set_option autoImplicit false

open LnLean
open LnLean.Channel

/-! ## 1. `Step` shadow lemmas

`Step` is untouched by this lane, so these are direct inductions over the ten
existing constructors.  They are the invariants the fold has to preserve and
the ones a literal `update_add_htlc` constructor would break. -/

/-- No lifecycle step changes the balance. -/
theorem step_balance_eq {c c' : Channel} {e : ProtocolEvent}
    (h : Step c e c') : c'.balance = c.balance := by
  cases h <;> rfl

/-- No lifecycle step changes the HTLC list. -/
theorem step_htlcs_eq {c c' : Channel} {e : ProtocolEvent}
    (h : Step c e c') : c'.htlcs = c.htlcs := by
  cases h <;> rfl

/-- No lifecycle step changes the funding value. -/
theorem step_fundingValue_eq {c c' : Channel} {e : ProtocolEvent}
    (h : Step c e c') : c'.fundingValue = c.fundingValue := by
  cases h <;> rfl

/-! ## 2. The folded lifecycle relation

`GuardedStep` is defined in `LnLean.Channel.State`.  The lemmas below make it
usable as a conservative extension of `Step`. -/

/-- The fold is a subrelation of the existing lifecycle relation: nothing is
added to the message semantics, only a guard is removed from two
transitions. -/
theorem guardedStep_toStep {c c' : Channel} {e : ProtocolEvent}
    (h : GuardedStep c e c') : Step c e c' := by
  cases h with
  | ofStep hs _ _ => exact hs
  | commitmentSigned hphase _ => exact Step.commitmentSigned c hphase
  | revokeAndAck hphase _ => exact Step.revokeAndAck c hphase

/-- **Exact characterization of the fold.**  A guarded step is exactly a
lifecycle step whose `commitment_signed` starts an idle round and whose
`revoke_and_ack` closes a round with one signature outstanding.  The two
implications are vacuous on every other message. -/
theorem guardedStep_iff_step_and_guards {c c' : Channel} {e : ProtocolEvent} :
    GuardedStep c e c' ↔
      Step c e c' ∧
        (e = ProtocolEvent.commitmentSigned →
          c.remoteCommitmentNumber = c.localCommitmentNumber) ∧
        (e = ProtocolEvent.revokeAndAck →
          c.remoteCommitmentNumber = c.localCommitmentNumber + 1) := by
  constructor
  · intro h
    cases h with
    | ofStep hs hcs hra =>
        exact ⟨hs, ⟨fun he => absurd he hcs, fun he => absurd he hra⟩⟩
    | commitmentSigned hphase hidle =>
        exact ⟨Step.commitmentSigned c hphase,
          ⟨fun _ => hidle, fun he => (by cases he)⟩⟩
    | revokeAndAck hphase hpending =>
        exact ⟨Step.revokeAndAck c hphase,
          ⟨fun he => (by cases he), fun _ => hpending⟩⟩
  · rintro ⟨hs, hcs, hra⟩
    by_cases he : e = ProtocolEvent.commitmentSigned
    · subst he
      cases hs with
      | commitmentSigned hphase =>
          exact GuardedStep.commitmentSigned c hphase (hcs rfl)
    · by_cases hra' : e = ProtocolEvent.revokeAndAck
      · subst hra'
        cases hs with
        | revokeAndAck hphase =>
            exact GuardedStep.revokeAndAck c hphase (hra rfl)
      · exact GuardedStep.ofStep hs he hra'

/-- On a non-round message the fold and `Step` coincide.  This is the
conservativity direction consumers need when they migrate a lifecycle
theorem. -/
theorem guardedStep_ofStep_iff {c c' : Channel} {e : ProtocolEvent}
    (hcs : e ≠ ProtocolEvent.commitmentSigned)
    (hra : e ≠ ProtocolEvent.revokeAndAck) :
    GuardedStep c e c' ↔ Step c e c' := by
  constructor
  · exact guardedStep_toStep
  · intro h
    exact GuardedStep.ofStep h hcs hra

/-- The fold is deterministic, because `Step` is. -/
theorem guardedStep_deterministic {c c₁ c₂ : Channel} {e : ProtocolEvent}
    (h₁ : GuardedStep c e c₁) (h₂ : GuardedStep c e c₂) : c₁ = c₂ :=
  LnLean.Channel.step_deterministic (guardedStep_toStep h₁) (guardedStep_toStep h₂)

/-- A folded step preserves the balance. -/
theorem guardedStep_balance_eq {c c' : Channel} {e : ProtocolEvent}
    (h : GuardedStep c e c') : c'.balance = c.balance :=
  step_balance_eq (guardedStep_toStep h)

/-- A folded step preserves the HTLC list. -/
theorem guardedStep_htlcs_eq {c c' : Channel} {e : ProtocolEvent}
    (h : GuardedStep c e c') : c'.htlcs = c.htlcs :=
  step_htlcs_eq (guardedStep_toStep h)

/-- A folded step preserves the funding value. -/
theorem guardedStep_fundingValue_eq {c c' : Channel} {e : ProtocolEvent}
    (h : GuardedStep c e c') : c'.fundingValue = c.fundingValue :=
  step_fundingValue_eq (guardedStep_toStep h)

/-- A folded step preserves the ledger equation of E37. -/
theorem guardedStep_preserves_ledger {c c' : Channel} {e : ProtocolEvent}
    (h : GuardedStep c e c') (fee : Msat)
    (hled : LnLean.Proofs.WaveE.E37.ledgerValue c fee = c.fundingValue.val) :
    LnLean.Proofs.WaveE.E37.ledgerValue c' fee = c'.fundingValue.val :=
  LnLean.Proofs.Channel.StateTransitionTargets.updateStep_preserves_ledger
    (hashFn := fun b : ByteArray => b)
    (UpdateStep.lifecycle (guardedStep_toStep h)) fee hled

/-- A folded step preserves `ReserveInvariant`. -/
theorem guardedStep_preserves_reserve {c c' : Channel} {e : ProtocolEvent}
    (h : GuardedStep c e c')
    (hres : LnLean.Proofs.Channel.ReserveInvariant c) :
    LnLean.Proofs.Channel.ReserveInvariant c' :=
  LnLean.Proofs.Channel.StateTransitionTargets.updateStep_preserves_reserve
    (hashFn := fun b : ByteArray => b)
    (UpdateStep.lifecycle (guardedStep_toStep h)) hres

/-! ## 3. `DanceStep` is the round fragment of the fold -/

/-- Every dance step is a guarded lifecycle step. -/
theorem danceStep_toGuardedStep {c c' : Channel} {e : DanceEvent}
    (h : DanceStep c e c') : GuardedStep c e.toProtocolEvent c' := by
  cases h with
  | commitmentSigned hphase hidle =>
      exact GuardedStep.commitmentSigned c hphase hidle
  | revokeAndAck hphase hpending =>
      exact GuardedStep.revokeAndAck c hphase hpending

/-- The `commitment_signed` fragments agree exactly. -/
theorem guardedStep_commitmentSigned_iff_danceStep {c c' : Channel} :
    GuardedStep c ProtocolEvent.commitmentSigned c' ↔
      DanceStep c DanceEvent.commitmentSigned c' := by
  constructor
  · intro h
    cases h with
    | ofStep _ hcs _ => exact absurd rfl hcs
    | commitmentSigned hphase hidle =>
        exact DanceStep.commitmentSigned c hphase hidle
  · intro h
    cases h with
    | commitmentSigned hphase hidle =>
        exact GuardedStep.commitmentSigned c hphase hidle

/-- The `revoke_and_ack` fragments agree exactly. -/
theorem guardedStep_revokeAndAck_iff_danceStep {c c' : Channel} :
    GuardedStep c ProtocolEvent.revokeAndAck c' ↔
      DanceStep c DanceEvent.revokeAndAck c' := by
  constructor
  · intro h
    cases h with
    | ofStep _ _ hra => exact absurd rfl hra
    | revokeAndAck hphase hpending =>
        exact DanceStep.revokeAndAck c hphase hpending
  · intro h
    cases h with
    | revokeAndAck hphase hpending =>
        exact GuardedStep.revokeAndAck c hphase hpending

/-- The dance relation is exactly the guarded lifecycle fragment on the two
round messages.  The additive wave-6 layer is therefore a refinement of the
fold, not a second message semantics. -/
theorem danceStep_iff_guardedStep {c c' : Channel} {e : DanceEvent} :
    DanceStep c e c' ↔ GuardedStep c e.toProtocolEvent c' := by
  constructor
  · exact danceStep_toGuardedStep
  · intro h
    cases e with
    | commitmentSigned =>
        exact (guardedStep_commitmentSigned_iff_danceStep (c := c) (c' := c')).mp h
    | revokeAndAck =>
        exact (guardedStep_revokeAndAck_iff_danceStep (c := c) (c' := c')).mp h

/-- The guard of the folded `commitment_signed` is the idle condition. -/
theorem guardedStep_commitmentSigned_requires_idle {c c' : Channel}
    (h : GuardedStep c ProtocolEvent.commitmentSigned c') :
    c.remoteCommitmentNumber = c.localCommitmentNumber := by
  have hd := guardedStep_commitmentSigned_iff_danceStep.mp h
  cases hd with
  | commitmentSigned _ hidle => exact hidle

/-- The guard of the folded `revoke_and_ack` is the pending condition. -/
theorem guardedStep_revokeAndAck_requires_pending {c c' : Channel}
    (h : GuardedStep c ProtocolEvent.revokeAndAck c') :
    c.remoteCommitmentNumber = c.localCommitmentNumber + 1 := by
  have hd := guardedStep_revokeAndAck_iff_danceStep.mp h
  cases hd with
  | revokeAndAck _ hpending => exact hpending

/-- No folded `commitment_signed` starts a second round while one is in
flight. -/
theorem no_guarded_commitmentSigned_with_round_in_flight {c c' : Channel}
    (hpending : c.remoteCommitmentNumber = c.localCommitmentNumber + 1) :
    ¬ GuardedStep c ProtocolEvent.commitmentSigned c' := by
  intro h
  have hidle := guardedStep_commitmentSigned_requires_idle h
  omega

/-- No folded `revoke_and_ack` closes a round that was never opened. -/
theorem no_guarded_revokeAndAck_without_commitmentSigned {c c' : Channel}
    (hidle : c.remoteCommitmentNumber = c.localCommitmentNumber) :
    ¬ GuardedStep c ProtocolEvent.revokeAndAck c' := by
  intro h
  have hpending := guardedStep_revokeAndAck_requires_pending h
  omega

/-! ## 4. The round window is an invariant of the fold

`Step` permits an arbitrary counter pair; `GuardedStep` restricts only the two
round events.  Since every other lifecycle message leaves both counters alone,
an ordered source stays ordered. -/

/-- Every folded step preserves the ordered round window. -/
theorem guardedStep_preserves_ordered {c c' : Channel} {e : ProtocolEvent}
    (h : GuardedStep c e c') (ho : DanceOrdered c) : DanceOrdered c' := by
  cases h with
  | ofStep hs hcs hra =>
      have hl : c'.localCommitmentNumber = c.localCommitmentNumber :=
        LnLean.Channel.step_local_eq_of_ne_revokeAndAck hs hra
      have hr : c'.remoteCommitmentNumber = c.remoteCommitmentNumber :=
        LnLean.Channel.step_remote_eq_of_ne_commitmentSigned hs hcs
      unfold DanceOrdered at *
      omega
  | commitmentSigned _ hidle =>
      unfold DanceOrdered at *
      simp [signRemoteCommitment]
      omega
  | revokeAndAck _ hpending =>
      unfold DanceOrdered at *
      simp [revokeLocalCommitment]
      omega

/-- Every folded lifecycle trace preserves the ordered round window. -/
theorem guardedReachable_preserves_ordered {a b : Channel}
    (h : GuardedReachable a b) : DanceOrdered a → DanceOrdered b := by
  induction h with
  | refl => exact id
  | step _ hs ih => exact fun ho => guardedStep_preserves_ordered hs (ih ho)

/-- Every dance-reachable pair is a folded lifecycle trace. -/
theorem danceReachable_toGuardedReachable {a b : Channel}
    (h : DanceReachable a b) : GuardedReachable a b := by
  induction h with
  | refl => exact GuardedReachable.refl a
  | step _ hs ih => exact GuardedReachable.step ih (danceStep_toGuardedStep hs)

/-- Every folded lifecycle trace is a lifecycle trace. -/
theorem guardedReachable_toReachable {a b : Channel}
    (h : GuardedReachable a b) : Reachable a b := by
  induction h with
  | refl => exact Reachable.refl a
  | step _ hs ih => exact Reachable.step ih (guardedStep_toStep hs)

/-- Folded lifecycle traces compose. -/
theorem guardedReachable_trans {a b c : Channel}
    (hab : GuardedReachable a b) (hbc : GuardedReachable b c) :
    GuardedReachable a c := by
  induction hbc with
  | refl => exact hab
  | step _ hs ih => exact GuardedReachable.step ih hs

/-- A single folded step is a folded trace. -/
theorem guardedReachable_of_guardedStep {a b : Channel} {e : ProtocolEvent}
    (h : GuardedStep a e b) : GuardedReachable a b :=
  GuardedReachable.step (GuardedReachable.refl a) h

/-- Ledger conservation along a folded lifecycle trace. -/
theorem guardedReachable_preserves_ledger {a b : Channel}
    (h : GuardedReachable a b) (fee : Msat)
    (hled : LnLean.Proofs.WaveE.E37.ledgerValue a fee = a.fundingValue.val) :
    LnLean.Proofs.WaveE.E37.ledgerValue b fee = b.fundingValue.val := by
  induction h with
  | refl => exact hled
  | step _ hs ih => exact guardedStep_preserves_ledger hs fee ih

/-- Reserve preservation along a folded lifecycle trace. -/
theorem guardedReachable_preserves_reserve {a b : Channel}
    (h : GuardedReachable a b)
    (hres : LnLean.Proofs.Channel.ReserveInvariant a) :
    LnLean.Proofs.Channel.ReserveInvariant b := by
  induction h with
  | refl => exact hres
  | step _ hs ih => exact guardedStep_preserves_reserve hs ih

/-! ## 5. Successor counter projections used by the fold

The three HTLC successors change balances and HTLC states but never the
commitment counters or the phase.  These projections are the whole reason the
round window survives an update trace. -/

@[simp] theorem updateAddHtlc_localCommitmentNumber (c : Channel)
    (dir : Direction) (amount : Msat) (ph : PaymentHash) (cltv : Height) :
    (updateAddHtlc c dir amount ph cltv).localCommitmentNumber =
      c.localCommitmentNumber := rfl

@[simp] theorem updateAddHtlc_remoteCommitmentNumber (c : Channel)
    (dir : Direction) (amount : Msat) (ph : PaymentHash) (cltv : Height) :
    (updateAddHtlc c dir amount ph cltv).remoteCommitmentNumber =
      c.remoteCommitmentNumber := rfl

@[simp] theorem failHtlcAt_localCommitmentNumber (c : Channel) (i : Nat) :
    (failHtlcAt c i).localCommitmentNumber = c.localCommitmentNumber := by
  unfold failHtlcAt
  split <;> rfl

@[simp] theorem failHtlcAt_remoteCommitmentNumber (c : Channel) (i : Nat) :
    (failHtlcAt c i).remoteCommitmentNumber = c.remoteCommitmentNumber := by
  unfold failHtlcAt
  split <;> rfl

@[simp] theorem fulfillHtlcAt_localCommitmentNumber (c : Channel) (i : Nat) :
    (fulfillHtlcAt c i).localCommitmentNumber = c.localCommitmentNumber := by
  unfold fulfillHtlcAt
  split <;> rfl

@[simp] theorem fulfillHtlcAt_remoteCommitmentNumber (c : Channel) (i : Nat) :
    (fulfillHtlcAt c i).remoteCommitmentNumber = c.remoteCommitmentNumber := by
  unfold fulfillHtlcAt
  split <;> rfl

/-! ## 6. The folded update relation

`GuardedUpdateStep` is the single relation over `UpdateEvent`: guarded
lifecycle messages plus the three HTLC messages. -/

/-- The folded update relation is a subrelation of the wave-5 update relation.
Every existing ledger, reserve, guard-extraction, and determinism theorem
therefore applies to it unchanged. -/
theorem guardedUpdateStep_toUpdateStep {hashFn : ByteArray → ByteArray}
    {c c' : Channel} {e : UpdateEvent} (h : GuardedUpdateStep hashFn c e c') :
    UpdateStep hashFn c e c' := by
  cases h with
  | lifecycle hs => exact UpdateStep.lifecycle (guardedStep_toStep hs)
  | update_add_htlc hphase dir amount ph cltv haff =>
      exact UpdateStep.update_add_htlc c hphase dir amount ph cltv haff
  | update_fulfill_htlc hphase i hh p hi hpending hpre =>
      exact UpdateStep.update_fulfill_htlc c hphase i hh p hi hpending hpre
  | update_fail_htlc hphase i hh hi hpending =>
      exact UpdateStep.update_fail_htlc c hphase i hh hi hpending

/-- The lifecycle fragment of the fold is exactly the guarded lifecycle
relation. -/
theorem guardedUpdateStep_lifecycle_iff {hashFn : ByteArray → ByteArray}
    {c c' : Channel} {e : ProtocolEvent} :
    GuardedUpdateStep hashFn c (.lifecycle e) c' ↔ GuardedStep c e c' := by
  constructor
  · intro h
    cases h with
    | lifecycle hs => exact hs
  · intro h
    exact GuardedUpdateStep.lifecycle h

/-- The folded update relation is deterministic. -/
theorem guardedUpdateStep_deterministic {hashFn : ByteArray → ByteArray}
    {c c₁ c₂ : Channel} {e : UpdateEvent}
    (h₁ : GuardedUpdateStep hashFn c e c₁) (h₂ : GuardedUpdateStep hashFn c e c₂) :
    c₁ = c₂ :=
  LnLean.Proofs.Channel.StateTransitionTargets.updateStep_deterministic
    (guardedUpdateStep_toUpdateStep h₁) (guardedUpdateStep_toUpdateStep h₂)

/-- An `update_add_htlc` transition of the fold carries `AffordableAdd`. -/
theorem guardedUpdateStep_add_affordable {hashFn : ByteArray → ByteArray}
    {c c' : Channel} {dir : Direction} {amount : Msat} {ph : PaymentHash}
    {cltv : Height}
    (h : GuardedUpdateStep hashFn c (.addHtlc dir amount ph cltv) c') :
    AffordableAdd c dir amount cltv := by
  cases h with
  | update_add_htlc _ _ _ _ _ haff => exact haff

/-- A folded `update_add_htlc` leaves both commitment counters alone. -/
theorem guardedUpdateStep_add_counters {hashFn : ByteArray → ByteArray}
    {c c' : Channel} {dir : Direction} {amount : Msat} {ph : PaymentHash}
    {cltv : Height}
    (h : GuardedUpdateStep hashFn c (.addHtlc dir amount ph cltv) c') :
    c'.localCommitmentNumber = c.localCommitmentNumber ∧
      c'.remoteCommitmentNumber = c.remoteCommitmentNumber :=
  LnLean.Proofs.Channel.StateTransitionTargets.updateStep_add_counters
    (guardedUpdateStep_toUpdateStep h)

/-- A folded update step preserves the ordered round window. -/
theorem guardedUpdateStep_preserves_ordered {hashFn : ByteArray → ByteArray}
    {c c' : Channel} {e : UpdateEvent} (h : GuardedUpdateStep hashFn c e c')
    (ho : DanceOrdered c) : DanceOrdered c' := by
  cases h with
  | lifecycle hs => exact guardedStep_preserves_ordered hs ho
  | update_add_htlc _ _ _ _ _ _ => simpa [DanceOrdered] using ho
  | update_fulfill_htlc _ _ _ _ _ _ _ => simpa [DanceOrdered] using ho
  | update_fail_htlc _ _ _ _ _ => simpa [DanceOrdered] using ho

/-- A folded update step preserves the E37 ledger equation. -/
theorem guardedUpdateStep_preserves_ledger {hashFn : ByteArray → ByteArray}
    {c c' : Channel} {e : UpdateEvent} (h : GuardedUpdateStep hashFn c e c')
    (fee : Msat)
    (hled : LnLean.Proofs.WaveE.E37.ledgerValue c fee = c.fundingValue.val) :
    LnLean.Proofs.WaveE.E37.ledgerValue c' fee = c'.fundingValue.val :=
  LnLean.Proofs.Channel.StateTransitionTargets.updateStep_preserves_ledger
    (guardedUpdateStep_toUpdateStep h) fee hled

/-- A folded update step preserves `ReserveInvariant`. -/
theorem guardedUpdateStep_preserves_reserve {hashFn : ByteArray → ByteArray}
    {c c' : Channel} {e : UpdateEvent} (h : GuardedUpdateStep hashFn c e c')
    (hres : LnLean.Proofs.Channel.ReserveInvariant c) :
    LnLean.Proofs.Channel.ReserveInvariant c' :=
  LnLean.Proofs.Channel.StateTransitionTargets.updateStep_preserves_reserve
    (guardedUpdateStep_toUpdateStep h) hres

/-- Every folded update trace is a wave-5 update trace. -/
theorem guardedUpdateReachable_toUpdateReachable {hashFn : ByteArray → ByteArray}
    {a b : Channel} (h : GuardedUpdateReachable hashFn a b) :
    UpdateReachable hashFn a b := by
  induction h with
  | refl => exact UpdateReachable.refl a
  | step _ hs ih => exact UpdateReachable.step ih (guardedUpdateStep_toUpdateStep hs)

/-- Folded update traces compose. -/
theorem guardedUpdateReachable_trans {hashFn : ByteArray → ByteArray}
    {a b c : Channel} (hab : GuardedUpdateReachable hashFn a b)
    (hbc : GuardedUpdateReachable hashFn b c) :
    GuardedUpdateReachable hashFn a c := by
  induction hbc with
  | refl => exact hab
  | step _ hs ih => exact GuardedUpdateReachable.step ih hs

/-- **The folded relation carries the round window along traces.**  This is
the invariant the unguarded `UpdateStep` cannot have: its `lifecycle`
constructor embeds both unguarded round messages. -/
theorem guardedUpdateReachable_preserves_ordered {hashFn : ByteArray → ByteArray}
    {a b : Channel} (h : GuardedUpdateReachable hashFn a b) :
    DanceOrdered a → DanceOrdered b := by
  induction h with
  | refl => exact id
  | step _ hs ih => exact fun ho => guardedUpdateStep_preserves_ordered hs (ih ho)

/-- Along a non-reflexive folded update trace from an ordered state, neither
current commitment is revoked.  Compare
`DanceStep`'s `danceReachable_current_not_revoked`; the fold lifts the same
statement across HTLC updates, which leave the counters alone. -/
theorem guardedUpdateReachable_current_not_revoked {hashFn : ByteArray → ByteArray}
    {a b : Channel} (h : GuardedUpdateReachable hashFn a b)
    (ho : DanceOrdered a) (_hne : a ≠ b) :
    ¬ CommitmentRevoked b b.localCommitmentNumber ∧
      ¬ CommitmentRevoked b b.remoteCommitmentNumber := by
  have hb : DanceOrdered b := guardedUpdateReachable_preserves_ordered h ho
  exact ⟨LnLean.Proofs.Channel.CommitmentDanceTargets.commitmentRevoked_current_local b,
    LnLean.Proofs.Channel.CommitmentDanceTargets.commitmentRevoked_current_remote hb⟩

/-- Ledger conservation along a folded update trace. -/
theorem guardedUpdateReachable_preserves_ledger {hashFn : ByteArray → ByteArray}
    {a b : Channel} (h : GuardedUpdateReachable hashFn a b) (fee : Msat)
    (hled : LnLean.Proofs.WaveE.E37.ledgerValue a fee = a.fundingValue.val) :
    LnLean.Proofs.WaveE.E37.ledgerValue b fee = b.fundingValue.val := by
  induction h with
  | refl => exact hled
  | step _ hs ih => exact guardedUpdateStep_preserves_ledger hs fee ih

/-- Reserve preservation along a folded update trace. -/
theorem guardedUpdateReachable_preserves_reserve {hashFn : ByteArray → ByteArray}
    {a b : Channel} (h : GuardedUpdateReachable hashFn a b)
    (hres : LnLean.Proofs.Channel.ReserveInvariant a) :
    LnLean.Proofs.Channel.ReserveInvariant b := by
  induction h with
  | refl => exact hres
  | step _ hs ih => exact guardedUpdateStep_preserves_reserve hs ih

/-! ## 7. Non-vacuity

The fold is inhabited by the same concrete witnesses as the additive layers:
a two-round dance and an affordable local add that preserves the ledger. -/

/-- **Two folded rounds.**  The wave-6 two-round witness is a folded lifecycle
trace: both commitment messages are `GuardedStep`s, the final state is
ordered, and both earlier commitments are revoked. -/
theorem guarded_two_rounds_witness :
    ∃ (c c₁ c₂ c₃ c₄ : Channel),
      GuardedReachable c c₄ ∧
        GuardedStep c ProtocolEvent.commitmentSigned c₁ ∧
          GuardedStep c₁ ProtocolEvent.revokeAndAck c₂ ∧
            GuardedStep c₂ ProtocolEvent.commitmentSigned c₃ ∧
              GuardedStep c₃ ProtocolEvent.revokeAndAck c₄ ∧
                DanceOrdered c₄ ∧
                  c₄.localCommitmentNumber = 2 ∧
                    c₄.remoteCommitmentNumber = 2 ∧
                      CommitmentRevoked c₄ 0 ∧ CommitmentRevoked c₄ 1 := by
  obtain ⟨c, c₁, c₂, c₃, c₄, hr, h₁, h₂, h₃, h₄, ho, hl, hr', hr0, hr1, _⟩ :=
    LnLean.Proofs.Channel.CommitmentDanceTargets.dance_two_rounds_witness
  exact ⟨c, c₁, c₂, c₃, c₄, danceReachable_toGuardedReachable hr,
    danceStep_toGuardedStep h₁, danceStep_toGuardedStep h₂,
    danceStep_toGuardedStep h₃, danceStep_toGuardedStep h₄,
    ho, hl, hr', hr0, hr1⟩

/-- **An affordable add inside the fold.**  A 500-msat local HTLC from the
ordered test channel is a folded update step, both endpoints stay ordered, and
the E37 ledger equation is preserved. -/
theorem guarded_update_add_witness :
    ∃ (c c' : Channel) (e : UpdateEvent) (fee : Msat),
      GuardedUpdateStep (fun b : ByteArray => b) c e c' ∧
        DanceOrdered c ∧ DanceOrdered c' ∧
          LnLean.Proofs.WaveE.E37.ledgerValue c fee = c.fundingValue.val ∧
            LnLean.Proofs.WaveE.E37.ledgerValue c' fee = c'.fundingValue.val := by
  let c := LnLean.Proofs.WaveE.E37.testChannel 1000 1000 2000 0 1 1000
  let amount : Msat := ⟨500⟩
  let fee : Msat := ⟨0⟩
  have haff : AffordableAdd c .local amount 0 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [c, LnLean.Proofs.WaveE.E37.testChannel, amount,
        MAX_CLTV_EXPIRY, offeredBalance, offeringReserveSat, receiverParams,
        pendingHtlcValueOf]
  have hphase : c.phase = ChannelPhase.normal := by
    simp [c, LnLean.Proofs.WaveE.E37.testChannel]
  have hstep :
      GuardedUpdateStep (fun b : ByteArray => b) c
        (.addHtlc .local amount ⟨ByteArray.empty⟩ 0)
        (updateAddHtlc c .local amount ⟨ByteArray.empty⟩ 0) :=
    GuardedUpdateStep.update_add_htlc c hphase .local amount ⟨ByteArray.empty⟩ 0 haff
  have ho : DanceOrdered c := by
    unfold DanceOrdered
    simp [c, LnLean.Proofs.WaveE.E37.testChannel]
  have hled : LnLean.Proofs.WaveE.E37.ledgerValue c fee = c.fundingValue.val := by
    simp [c, LnLean.Proofs.WaveE.E37.testChannel, fee,
      LnLean.Proofs.WaveE.E37.ledgerValue, LnLean.Proofs.WaveE.E37.pendingValue]
  exact ⟨c, _, _, fee, hstep, ho, guardedUpdateStep_preserves_ordered hstep ho, hled,
    guardedUpdateStep_preserves_ledger hstep fee hled⟩

/-! ## 8. Why the literal folds are impossible

The two results below are the mechanized form of the migration analysis.  They
are not scope caveats: they say that the requested *literal* edit of `Step`
would make existing counterexamples false, and that no single relation can
both carry an affordable add and keep the balance invariant that
`LiquidityProps`, `F03`, and `D14` rely on. -/

/-- A concrete non-idle `commitment_signed` source: after one legal
`commitment_signed`, the successor has `remote = local + 1` and is still in
the `normal` phase, so the unguarded relation signs it again. -/
theorem step_commitmentSigned_unguarded_witness :
    ∃ (c c' : Channel), Step c ProtocolEvent.commitmentSigned c' ∧
      c.remoteCommitmentNumber ≠ c.localCommitmentNumber := by
  let c₀ := LnLean.Proofs.WaveE.E37.testChannel 1000 1000 2000 0 1 1000
  let c := signRemoteCommitment c₀
  refine ⟨c, signRemoteCommitment c, Step.commitmentSigned c ?_, ?_⟩
  · simp [c, signRemoteCommitment, c₀, LnLean.Proofs.WaveE.E37.testChannel]
  · simp [c, signRemoteCommitment, c₀, LnLean.Proofs.WaveE.E37.testChannel]

/-- **The dance guard cannot be folded into `Step` as a theorem.**  If every
legal `commitment_signed` started an idle round, the wave-6 counterexample
`unguarded_double_commitmentSigned_breaks_ordering` would be false.  The
direction of the fold is therefore `Step ⊇ GuardedStep`, never equality. -/
theorem literal_round_fold_refuted :
    ¬ (∀ (c c' : Channel), Step c ProtocolEvent.commitmentSigned c' →
        c.remoteCommitmentNumber = c.localCommitmentNumber) := by
  intro h
  obtain ⟨c, c', hs, hne⟩ := step_commitmentSigned_unguarded_witness
  exact hne (h c c' hs)

/-- **The revocation guard cannot be folded into `Step` either.**
`LnLean.Proofs.Protocol.ChannelReestablishProps.reachable_counters_inconsistent`
performs two consecutive unguarded `revoke_and_ack`s from an idle channel; a
pending-only `revokeAndAck` constructor would make that counterexample false. -/
theorem literal_revoke_fold_refuted :
    ¬ (∀ (c c' : Channel), Step c ProtocolEvent.revokeAndAck c' →
        c.remoteCommitmentNumber = c.localCommitmentNumber + 1) := by
  intro h
  let c := LnLean.Proofs.WaveE.E37.testChannel 1000 1000 2000 0 1 1000
  have hs : Step c ProtocolEvent.revokeAndAck (revokeLocalCommitment c) :=
    Step.revokeAndAck c (by simp [c, LnLean.Proofs.WaveE.E37.testChannel])
  have hpending := h c (revokeLocalCommitment c) hs
  simp [c, LnLean.Proofs.WaveE.E37.testChannel] at hpending

/-- An affordable add changes the balance. -/
theorem affordable_add_changes_balance :
    ∃ (c : Channel) (dir : Direction) (amount : Msat) (ph : PaymentHash)
        (cltv : Height),
      AffordableAdd c dir amount cltv ∧
        (updateAddHtlc c dir amount ph cltv).balance ≠ c.balance := by
  let c := LnLean.Proofs.WaveE.E37.testChannel 1000 1000 2000 0 1 1000
  let amount : Msat := ⟨500⟩
  refine ⟨c, .local, amount, ⟨ByteArray.empty⟩, 0, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [c, LnLean.Proofs.WaveE.E37.testChannel, amount,
        MAX_CLTV_EXPIRY, offeredBalance, offeringReserveSat, receiverParams,
        pendingHtlcValueOf]
  · intro h
    have hb := congrArg (fun b : Balance => b.localBalance.val) h
    simp [c, LnLean.Proofs.WaveE.E37.testChannel, amount, updateAddHtlc] at hb

/-- An affordable add changes the HTLC list. -/
theorem affordable_add_changes_htlcs :
    ∃ (c : Channel) (dir : Direction) (amount : Msat) (ph : PaymentHash)
        (cltv : Height),
      AffordableAdd c dir amount cltv ∧
        (updateAddHtlc c dir amount ph cltv).htlcs ≠ c.htlcs := by
  let c := LnLean.Proofs.WaveE.E37.testChannel 1000 1000 2000 0 1 1000
  let amount : Msat := ⟨500⟩
  refine ⟨c, .local, amount, ⟨ByteArray.empty⟩, 0, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [c, LnLean.Proofs.WaveE.E37.testChannel, amount,
        MAX_CLTV_EXPIRY, offeredBalance, offeringReserveSat, receiverParams,
        pendingHtlcValueOf]
  · intro h
    have hb := congrArg List.length h
    simp [c, LnLean.Proofs.WaveE.E37.testChannel, amount, updateAddHtlc] at hb

/-- **No relation can both carry an affordable add and preserve balances.**
This is the exact conflict with `LiquidityProps.step_preserves_balance`,
`D14.waveD_d14_step_balance`, and the balance half of
`F03.step_preserves_ledgerBalanced`: a `Step`-shaped fold that accepted
`update_add_htlc` would have to drop those statements.  The additive
`UpdateStep`/`GuardedUpdateStep` layer keeps them by remaining a separate
relation over the *same* `Channel` record. -/
theorem fold_cannot_both_preserve_balance_and_carry_add
    (R : Channel → UpdateEvent → Channel → Prop) :
    ¬ ((∀ {c c' : Channel} {e : UpdateEvent}, R c e c' →
          c'.balance = c.balance) ∧
        (∀ {c : Channel} {dir : Direction} {amount : Msat}
            {ph : PaymentHash} {cltv : Height},
          AffordableAdd c dir amount cltv →
            R c (.addHtlc dir amount ph cltv)
              (updateAddHtlc c dir amount ph cltv))) := by
  rintro ⟨hbal, hadd⟩
  obtain ⟨c, dir, amount, ph, cltv, haff, hne⟩ := affordable_add_changes_balance
  exact hne (hbal (hadd haff))

/-- The HTLC-list form of the same conflict, against
`D14.waveD_d14_step_htlcs`, `F03.step_htlcs_eq`, and
`LivenessDelivery.step_htlcs_eq`. -/
theorem fold_cannot_both_preserve_htlcs_and_carry_add
    (R : Channel → UpdateEvent → Channel → Prop) :
    ¬ ((∀ {c c' : Channel} {e : UpdateEvent}, R c e c' →
          c'.htlcs = c.htlcs) ∧
        (∀ {c : Channel} {dir : Direction} {amount : Msat}
            {ph : PaymentHash} {cltv : Height},
          AffordableAdd c dir amount cltv →
            R c (.addHtlc dir amount ph cltv)
              (updateAddHtlc c dir amount ph cltv))) := by
  rintro ⟨hhtlcs, hadd⟩
  obtain ⟨c, dir, amount, ph, cltv, haff, hne⟩ := affordable_add_changes_htlcs
  exact hne (hhtlcs (hadd haff))

/-! ## 9. Retained counterexamples

Every wave-5 and wave-6 counterexample is re-exported unchanged.  The fold is
a subrelation, so none of them is affected. -/

/-- The wave-5 unguarded-add ledger counterexample, unchanged. -/
theorem unguarded_add_ledger_counterexample_retained :
    ∃ (c : Channel) (dir : Direction) (amount : Msat) (ph : PaymentHash)
        (cltv : Height) (fee : Msat),
      LnLean.Proofs.WaveE.E37.ledgerValue c fee = c.fundingValue.val ∧
        ¬ AffordableAdd c dir amount cltv ∧
          LnLean.Proofs.WaveE.E37.ledgerValue
              (updateAddHtlc c dir amount ph cltv) fee ≠
            (updateAddHtlc c dir amount ph cltv).fundingValue.val :=
  LnLean.Proofs.Channel.StateTransitionTargets.unguarded_add_ledger_counterexample

/-- The wave-6 double-sign counterexample, unchanged. -/
theorem unguarded_double_commitmentSigned_breaks_ordering_retained :
    ∃ (c c₁ c₂ : Channel),
      Step c ProtocolEvent.commitmentSigned c₁ ∧
        Step c₁ ProtocolEvent.commitmentSigned c₂ ∧ ¬ DanceOrdered c₂ :=
  LnLean.Proofs.Channel.CommitmentDanceTargets.unguarded_double_commitmentSigned_breaks_ordering

/-- The wave-6 idle-revoke counterexample, unchanged. -/
theorem unguarded_revokeAndAck_from_idle_breaks_ordering_retained :
    ∃ (c c' : Channel), Step c ProtocolEvent.revokeAndAck c' ∧ ¬ DanceOrdered c' :=
  LnLean.Proofs.Channel.CommitmentDanceTargets.unguarded_revokeAndAck_from_idle_breaks_ordering

/-- The wave-6 stale-signing counterexample, unchanged. -/
theorem unguarded_step_signs_revoked_commitment_retained :
    ∃ (c c₁ c₂ : Channel),
      Step c ProtocolEvent.revokeAndAck c₁ ∧
        Step c₁ ProtocolEvent.commitmentSigned c₂ ∧
          CommitmentRevoked c₂ c₁.remoteCommitmentNumber :=
  LnLean.Proofs.Channel.CommitmentDanceTargets.unguarded_step_signs_revoked_commitment

/-- The folded relation excludes the double-sign interleaving: after one
guarded `commitment_signed`, no second one is legal.  The exclusion is what
makes the retained counterexample a *counterexample about `Step`* rather than a
counterexample about the fold. -/
theorem guarded_no_double_commitmentSigned {c c₁ c₂ : Channel}
    (h₁ : GuardedStep c ProtocolEvent.commitmentSigned c₁)
    (h₂ : GuardedStep c₁ ProtocolEvent.commitmentSigned c₂) : False := by
  have hidle : c₁.remoteCommitmentNumber = c₁.localCommitmentNumber :=
    guardedStep_commitmentSigned_requires_idle h₂
  have hc₁ : c₁ = signRemoteCommitment c :=
    LnLean.Proofs.Channel.CommitmentDanceTargets.danceStep_commitmentSigned_target
      (guardedStep_commitmentSigned_iff_danceStep.mp h₁)
  rw [hc₁] at hidle
  simp [signRemoteCommitment] at hidle
  have hidle₀ : c.remoteCommitmentNumber = c.localCommitmentNumber :=
    guardedStep_commitmentSigned_requires_idle h₁
  omega

end LnLean.Proofs.Channel.ProtocolEventFoldTargets
