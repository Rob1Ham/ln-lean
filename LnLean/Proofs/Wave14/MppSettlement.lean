import LnLean.Proofs.Payment.MPPProps
import LnLean.Security.Invariants

/-!
# LnLean.Proofs.Wave14.MppSettlement

English claim.  BOLT 4 `basic_mpp` completes an HTLC set when the set is
non-empty and the sum of its parts is **at least** the advertised
`total_msat` (`refs/bolts/04-onion-routing.md:383-385`).  The existing wave-A
carrier is narrower: `LnLean.Payment.mppComplete` requires the sum to be
**exactly** `plan.target`, and `LnLean.Security.MppPayment.settle` uses the
same exact equality.  This module adds the lower-bound completion and
settlement layer while leaving both existing carriers unchanged.

## What is added, and what is deliberately unchanged

* `LnLean.Payment.MPPProps.mppCompleteGe` already exists in
  `LnLean/Proofs/Payment/MPPProps.lean` (around line 686), together with
  `mppComplete_implies_completeGe`.  This module **does not redefine or
  duplicate** either declaration; it imports and builds on them.
* `SumGe` is the payment-level analogue of `mppCompleteGe`: a non-empty part
  list whose `MppPayment.partsSum` is at least `m.total`.
* `settleGe` is the additive lower-bound settlement function.  It returns the
  accepted payment exactly when `SumGe` holds, and `none` otherwise.
* `Fulfilled` is the model's fulfilment flag: `accepted = true`, matching
  BOLT 4's "fulfil all HTLCs of the set" final-node conclusion.
* `planToPayment` maps an `MPPPlan` to the economy-only `MppPayment` record
  (`parts := amounts`, `target := total`), and
  `planToPayment_sumGe_iff` proves that the payment-level predicate is exactly
  `mppCompleteGe` on the source plan.

`mppComplete`, `MppPayment.settle`, and `MppPayment.settle_requires_sum` are
**not** changed.  Their exact-sum behaviour is not false; it is strictly
narrower than BOLT 4.  The overpay witness below exhibits a protocol-valid
settlement that the old exact path rejects, and the underpay witness exhibits
the lower bound's rejection direction.  Both behaviours are retained as
permanent counterexamples.

## Boundary (do not overclaim)

This is a settlement-predicate layer over the existing economy-only records.
It does **not** model or prove:

* onion construction, route selection, per-part fees, or the `mpp_timeout`
  60-second collection window;
* payment-secret derivation/encryption, preimage soundness, or a cryptographic
  hash property; `MPPPlan` still carries only the opaque secret and hash;
* per-HTLC identity across parts (`channel_id`, `htlc_id`), so duplicate
  detection remains whole-record equality in `MPPProps`;
* mixed `total_msat` values across parts (the plan carries one `total`);
* receiver persistence, event publication, or cross-process admission;
* that a valid `settleGe` result is eventually reached in a live network.
  `settleGe` is an admission/settlement decision on a supplied value, not a
  liveness theorem.

BOLT 4 anchor (pinned BOLTs commit
`1aadb719b4007c4cea0ba6e36b08c4fb53788dee`):
`refs/bolts/04-onion-routing.md:383-385` states that the set's total
`amt_to_forward` is at least `total_msat`, and the final node fails all parts
while the total is below that bound.
-/

namespace LnLean.Proofs.Wave14.MppSettlement

set_option autoImplicit false

open LnLean
open LnLean.Payment
open LnLean.Security

/-! ## Lower-bound completion and settlement -/

/-- Payment-level lower-bound completion: a non-empty set of parts whose sum is
at least the advertised total.  This is the `MppPayment` analogue of the
existing plan-level `MPPProps.mppCompleteGe`; the non-emptiness conjunct is
kept so the predicate matches that carrier and BOLT 4's HTLC-set shape.
`abbrev` (rather than `def`) keeps the conjunction reducible for `decide` on
the concrete witnesses. -/
abbrev SumGe (m : MppPayment) : Prop :=
  m.parts ≠ [] ∧ m.total.val ≤ m.partsSum

/-- The model's fulfilment flag: the receiver accepted (and therefore
fulfilled) the HTLC set.  This is the conclusion BOLT 4 draws once the set
total reaches `total_msat`. -/
def Fulfilled (m : MppPayment) : Prop :=
  m.accepted = true

/-- Lower-bound settlement.  Unlike the retained exact `MppPayment.settle`, a
payment whose parts exceed the advertised total is accepted and marked
`accepted := true`.  A payment that is empty or under the total is rejected
with `none`. -/
def settleGe (m : MppPayment) : Option MppPayment :=
  if SumGe m then some { m with accepted := true } else none

/-- `settleGe` succeeds exactly on the lower-bound predicate. -/
theorem settleGe_iff_sumGe (m : MppPayment) :
    SumGe m ↔ ∃ m', settleGe m = some m' := by
  constructor
  · intro h
    refine ⟨{ m with accepted := true }, ?_⟩
    unfold settleGe
    rw [ite_eq_left h]
  · rintro ⟨m', h⟩
    unfold settleGe at h
    by_cases hg : SumGe m
    · exact hg
    · rw [ite_eq_right hg] at h
      cases h

/-- Any result of `settleGe` is fulfilled and preserves the payment's parts and
advertised total.  Only the `accepted` flag changes. -/
theorem settleGe_fulfils {m m' : MppPayment} (h : settleGe m = some m') :
    Fulfilled m' ∧ m'.parts = m.parts ∧ m'.total = m.total := by
  unfold settleGe at h
  by_cases hg : SumGe m
  · rw [ite_eq_left hg] at h
    injection h with hm
    subst m'
    exact ⟨rfl, rfl, rfl⟩
  · rw [ite_eq_right hg] at h
    cases h

/-- Exact completion implies lower-bound completion once the set is non-empty.
The exact `MppPayment.SumOK` predicate alone permits the empty/zero value,
which BOLT 4 does not treat as an HTLC set; `hne` supplies the set shape. -/
theorem sumOK_imp_sumGe {m : MppPayment} (h : m.SumOK) (hne : m.parts ≠ []) :
    SumGe m := by
  refine ⟨hne, ?_⟩
  unfold MppPayment.SumOK at h
  omega

/-- **Exact settlement implies lower-bound settlement.**  The retained exact
`MppPayment.settle` result yields a successful `settleGe` result with the same
parts and total. -/
theorem exact_settle_implies_ge_settle (m m' : MppPayment)
    (h : m.settle = some m') (hne : m.parts ≠ []) :
    ∃ m'', settleGe m = some m'' ∧ Fulfilled m'' := by
  have hsum : m.SumOK := MppPayment.settle_requires_sum m m' h
  have hge : SumGe m := sumOK_imp_sumGe hsum hne
  exact ⟨{ m with accepted := true }, by simp [settleGe, hge], rfl⟩

/-! ## Plan-to-payment bridge -/

/-- Project a plan onto the economy-only payment record used by
`MppPayment.settle`: the part amounts become the payment's part list, and the
plan target becomes the advertised total. -/
def planToPayment (plan : MPPPlan) : MppPayment :=
  { parts := plan.parts.map (fun p => p.amount)
    total := plan.target
    accepted := false }

/-- The projected payment's sum is the plan's `sumParts`. -/
theorem planToPayment_partsSum (plan : MPPPlan) :
    (planToPayment plan).partsSum = sumParts plan.parts := by
  unfold planToPayment MppPayment.partsSum
  induction plan.parts with
  | nil => rfl
  | cons p ps ih =>
      simp only [List.map_cons, List.sum_cons, sumParts]
      rw [ih]

/-- The payment-level lower bound on the projection is exactly the existing
plan-level `MPPProps.mppCompleteGe`.  This is the semantic link that lets the
new settlement layer reuse the existing plan predicate instead of restating
it. -/
theorem planToPayment_sumGe_iff (plan : MPPPlan) :
    SumGe (planToPayment plan) ↔ LnLean.Payment.MPPProps.mppCompleteGe plan := by
  unfold SumGe LnLean.Payment.MPPProps.mppCompleteGe
  rw [planToPayment_partsSum]
  constructor
  · rintro ⟨hne, hle⟩
    refine ⟨?_, hle⟩
    intro hp
    exact hne (by simp [planToPayment, hp])
  · rintro ⟨hne, hle⟩
    refine ⟨?_, hle⟩
    intro hmap
    exact hne (List.map_eq_nil_iff.mp hmap)

/-- **Exact completion implies lower-bound settlement.**  If a plan is
`mppComplete`, then it is `mppCompleteGe` (the existing theorem
`mppComplete_implies_completeGe`) and the projected payment produces a
fulfilled `settleGe` result. -/
theorem exact_completion_implies_ge_settlement (plan : MPPPlan)
    (h : mppComplete plan) :
    LnLean.Payment.MPPProps.mppCompleteGe plan ∧
      ∃ m', settleGe (planToPayment plan) = some m' ∧ Fulfilled m' := by
  have hge : LnLean.Payment.MPPProps.mppCompleteGe plan :=
    LnLean.Payment.MPPProps.mppComplete_implies_completeGe h
  have hsum : SumGe (planToPayment plan) :=
    (planToPayment_sumGe_iff plan).mpr hge
  exact ⟨hge, ⟨{ planToPayment plan with accepted := true },
    by simp [settleGe, hsum], rfl⟩⟩

/-! ## Concrete witnesses -/

/-- Overpay witness from R32 G08: one part of 120 msat against a 100 msat
advertised total. -/
def overpayPayment : MppPayment :=
  { parts := [⟨120⟩], total := ⟨100⟩, accepted := false }

/-- The fulfilled form of the overpay witness. -/
def overpayFulfilled : MppPayment :=
  { overpayPayment with accepted := true }

/-- Underpay witness: one part of 40 msat against a 100 msat advertised
total. -/
def underpayPayment : MppPayment :=
  { parts := [⟨40⟩], total := ⟨100⟩, accepted := false }

/-- The same overpay case at the plan level, so the existing `mppCompleteGe`
carrier is exercised directly. -/
def overpayPlan : MPPPlan :=
  { paymentHash := ⟨ByteArray.empty⟩
    paymentSecret := ⟨ByteArray.empty⟩
    target := ⟨100⟩
    parts := [{ channel := ⟨0, 0, 0⟩, amount := ⟨120⟩, cltv := 0 }] }

/-- An exactly completing plan (60 + 40 = 100) used to exercise the
exact-to-lower-bound theorems without a hypothesis-only proof. -/
def exactPlan : MPPPlan :=
  { paymentHash := ⟨ByteArray.empty⟩
    paymentSecret := ⟨ByteArray.empty⟩
    target := ⟨100⟩
    parts := [{ channel := ⟨0, 0, 0⟩, amount := ⟨60⟩, cltv := 0 },
      { channel := ⟨0, 0, 1⟩, amount := ⟨40⟩, cltv := 0 }] }

/-- The overpay payment satisfies the lower bound. -/
theorem overpay_ge_completes : SumGe overpayPayment := by
  unfold SumGe
  decide

/-- The retained exact settlement rejects the overpay payment. -/
theorem overpay_exact_rejected :
    ¬ overpayPayment.SumOK ∧ overpayPayment.settle = none := by
  constructor
  · unfold MppPayment.SumOK MppPayment.partsSum
    decide
  · unfold MppPayment.settle
    decide

/-- **Overpay separation.**  The protocol-permitted overpay case completes
under `SumGe` but is rejected by the retained exact `SumOK`/`settle`. -/
theorem overpay_completes_ge_not_exact :
    SumGe overpayPayment ∧ ¬ overpayPayment.SumOK ∧
      overpayPayment.settle = none :=
  ⟨overpay_ge_completes, overpay_exact_rejected⟩

/-- The overpay witness produces a concrete fulfilled `settleGe` result, not
merely an existential supplied by a hypothesis. -/
theorem overpay_settleGe_fulfilled :
    settleGe overpayPayment = some overpayFulfilled ∧
      Fulfilled overpayFulfilled := by
  constructor
  · simp [settleGe, overpay_ge_completes, overpayFulfilled]
  · rfl

/-- **Underpay rejection.**  A set below `total_msat` is rejected by the lower
bound and by both settlement paths. -/
theorem underpay_rejected :
    ¬ SumGe underpayPayment ∧ underpayPayment.settle = none ∧
      settleGe underpayPayment = none := by
  refine ⟨?_, ?_, ?_⟩
  · unfold SumGe
    decide
  · unfold MppPayment.settle
    decide
  · unfold settleGe SumGe
    decide

/-- The existing plan-level predicate accepts the overpay plan, while the
retained exact `mppComplete` rejects it. -/
theorem overpayPlan_ge_not_exact :
    LnLean.Payment.MPPProps.mppCompleteGe overpayPlan ∧
      ¬ mppComplete overpayPlan := by
  constructor
  · unfold LnLean.Payment.MPPProps.mppCompleteGe
    decide
  · unfold mppComplete
    decide

/-- The plan projection of the overpay witness is literally the payment-level
overpay witness. -/
theorem planToPayment_overpayPlan : planToPayment overpayPlan = overpayPayment :=
  rfl

/-- The exact plan completes in the retained sense. -/
theorem exactPlan_complete : mppComplete exactPlan := by
  unfold mppComplete
  decide

/-- The exact plan yields a fulfilled lower-bound settlement through the
general exact-implies-`≥` theorem.  This is the non-vacuity witness for
`exact_completion_implies_ge_settlement`. -/
theorem exactPlan_settlesGe :
    ∃ m', settleGe (planToPayment exactPlan) = some m' ∧ Fulfilled m' :=
  (exact_completion_implies_ge_settlement exactPlan exactPlan_complete).2

/-! ## Axiom audit of the headline theorems -/

#print axioms settleGe_iff_sumGe
#print axioms settleGe_fulfils
#print axioms sumOK_imp_sumGe
#print axioms exact_settle_implies_ge_settle
#print axioms planToPayment_sumGe_iff
#print axioms exact_completion_implies_ge_settlement
#print axioms overpay_completes_ge_not_exact
#print axioms overpay_settleGe_fulfilled
#print axioms underpay_rejected
#print axioms overpayPlan_ge_not_exact
#print axioms exactPlan_settlesGe

end LnLean.Proofs.Wave14.MppSettlement
