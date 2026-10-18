import LnLean.Payment.MPP
import LnLean.Payment.Invoice
import LnLean.Proofs.Payment.MPPProps

/-!
# LnLean.Proofs.ModelHardening.F14

Running-total invariant for multi-part payments (parent obligation `LN-PM-MPP`,
traceability row `LN-PM-005`).

English claim (from `docs/OBLIGATIONS-GENERATED.md`): "During MPP collection,
each additional part keeps the running total at or below `total_msat`."

The claim is **not** an unconditional preservation law.  A part whose amount is
individually at most `total_msat` can still push the running total over the
advertised total: collecting 60 msat and then another 60 msat against
`total_msat = 100` is accepted by the per-part amount check but leaves a
running total of 120.  The exact invariant and the exact admission guard are
defined below.  `runningTotalBound_add` proves preservation under the guard,
`runningTotalBound_add_iff` proves the guard is necessary and sufficient, and
`overTotal_counterexample` mechanically refutes the unconditional form, which
is kept with a `sorry` next to the `LN-WF-F14` marker.

BOLT 4 §Basic Multi-Part Payments: all HTLCs in a set share `payment_hash`;
`total_msat` is the advertised total; the recipient must not fulfil any HTLC
of the set while the collected total is below `total_msat`.  LDK accumulates
parts in `lightning/src/ln/inbound_payment.rs` / `onion_payment.rs`; the guard
that keeps the running total inside the advertised total is the arithmetic
condition `amount_msat ≤ total_msat - collected_msat`.

Not modelled here: fee arithmetic, the collection timeout, and the decision to
overpay.  The model stores amounts as `Nat`, so no overflow side condition is
needed; over-total is the only arithmetic failure mode.
-/

namespace LnLean.Proofs.ModelHardening.F14

open LnLean
open LnLean.Payment

set_option autoImplicit false

/-! ## The invariant and the admission guard -/

/-- Running-total bound: the parts collected so far sum to at most the
advertised total `target` (BOLT 4 `total_msat`).  This is the invariant a
recipient maintains while an MPP HTLC set is being assembled. -/
def RunningTotalBound (target : Msat) (collected : List MPPPart) : Prop :=
  sumParts collected ≤ target.val

/-- Admission guard for one more part: its amount fits in the budget that is
still unallocated, `target - collected`.  This is the arithmetic form of
"the running total stays at or below `total_msat` for the next step". -/
def PartFits (target : Msat) (collected : List MPPPart) (p : MPPPart) : Prop :=
  p.amount.val ≤ target.val - sumParts collected

/-- The empty collection satisfies the invariant for every advertised
total. -/
@[simp] theorem runningTotalBound_nil (target : Msat) :
    RunningTotalBound target ([] : List MPPPart) := by
  unfold RunningTotalBound
  simp

/-- Under the invariant, the admission guard is exactly the statement that
adding the part keeps the (arithmetic) total within `target`. -/
theorem partFits_iff_add_le {target : Msat} {collected : List MPPPart}
    {p : MPPPart} (hinv : RunningTotalBound target collected) :
    PartFits target collected p ↔
      sumParts collected + p.amount.val ≤ target.val := by
  unfold PartFits RunningTotalBound at *
  omega

/-! ## Preservation under the standard guard -/

/-- **Each added part preserves the running-total bound** provided it fits in
the remaining budget.  This is the guarded form of `LN-PM-005`. -/
theorem runningTotalBound_add {target : Msat} {collected : List MPPPart}
    {p : MPPPart} (hinv : RunningTotalBound target collected)
    (hfit : PartFits target collected p) :
    RunningTotalBound target (p :: collected) := by
  unfold RunningTotalBound at hinv ⊢
  unfold PartFits at hfit
  simp only [sumParts_cons]
  omega

/-- **The guard is necessary and sufficient.**  For a collection already
inside the bound, adding one more part preserves the invariant exactly when
the part fits the remaining budget.  No weaker per-part check suffices; see
`overTotal_counterexample`. -/
theorem runningTotalBound_add_iff {target : Msat} {collected : List MPPPart}
    {p : MPPPart} (hinv : RunningTotalBound target collected) :
    RunningTotalBound target (p :: collected) ↔
      PartFits target collected p := by
  constructor
  · intro h
    rw [partFits_iff_add_le hinv]
    unfold RunningTotalBound at h
    simp only [sumParts_cons] at h
    omega
  · exact runningTotalBound_add hinv

/-- A whole batch of parts may be admitted at once when its total fits the
remaining budget.  This is the fold-level form of the invariant. -/
theorem runningTotalBound_append {target : Msat} {collected extra : List MPPPart}
    (hinv : RunningTotalBound target collected)
    (hfit : sumParts extra ≤ target.val - sumParts collected) :
    RunningTotalBound target (extra ++ collected) := by
  unfold RunningTotalBound at *
  rw [sumParts_append]
  omega

/-- The invariant is monotone in the advertised total. -/
theorem runningTotalBound_mono {target target' : Msat}
    (hle : target.val ≤ target'.val) {collected : List MPPPart}
    (h : RunningTotalBound target collected) :
    RunningTotalBound target' collected := by
  unfold RunningTotalBound at *
  omega

/-- Every complete plan satisfies the running-total bound.  Completeness is
the terminal state of a collection that respected the invariant. -/
theorem runningTotalBound_of_mppComplete {plan : MPPPlan}
    (h : mppComplete plan) :
    RunningTotalBound plan.target plan.parts := by
  unfold RunningTotalBound
  exact Nat.le_of_eq h.2

/-- Converse bridge: a non-empty collection that is inside the bound and that
has reached at least `total_msat` is complete in the exact-sum sense.  This is
the model-level form of BOLT 4's `collected ≥ total_msat` completion rule. -/
theorem mppComplete_of_runningTotalBound_of_ge {plan : MPPPlan}
    (hne : plan.parts ≠ [])
    (hinv : RunningTotalBound plan.target plan.parts)
    (hge : plan.target.val ≤ sumParts plan.parts) :
    mppComplete plan :=
  ⟨hne, Nat.le_antisymm hinv hge⟩

/-- Once the collected total equals the advertised total, no positive part can
pass the admission guard.  The collection is closed. -/
theorem not_partFits_of_sum_eq_target {target : Msat}
    {collected : List MPPPart} {p : MPPPart}
    (hsum : sumParts collected = target.val) (hpos : 0 < p.amount.val) :
    ¬ PartFits target collected p := by
  unfold PartFits
  rw [hsum]
  omega

/-- A positive part strictly increases the running total. -/
theorem sumParts_cons_lt_of_pos (p : MPPPart) (ps : List MPPPart)
    (hpos : 0 < p.amount.val) :
    sumParts ps < sumParts (p :: ps) := by
  simp only [sumParts_cons]
  omega

/-- Once the running total is over `target`, adding more parts can never
restore the invariant: over-total is an absorbing state. -/
theorem not_runningTotalBound_cons_of_over {target : Msat}
    {collected : List MPPPart} {p : MPPPart}
    (hover : target.val < sumParts collected) :
    ¬ RunningTotalBound target (p :: collected) := by
  unfold RunningTotalBound
  simp only [sumParts_cons]
  omega

/-! ## The faithful unconditional statement

This is the obligation as stated, with no guard.  It is false; the refutation
is `overTotal_counterexample`, and the guarded replacement is
`runningTotalBound_add`. -/

/-- `LN-PM-005` in its unconditional form: every additional part preserves the
running-total bound.  False as stated; see `overTotal_counterexample`. -/
theorem waveF_f14_running_total_bound (plan : MPPPlan)
    (collected : List MPPPart) (p : MPPPart)
    (hinv : RunningTotalBound plan.target collected) :
    RunningTotalBound plan.target (p :: collected) := by
  -- The per-part amount check is weaker than the remaining-budget guard:
  -- collecting 60 then 60 against a total of 100 overruns the total.
  -- OBLIGATION: LN-WF-F14
  sorry

/-! ## Mechanized over-total counterexample -/

/-- A part on channel `(0, 0, 0)` with the default final CLTV; only the amount
varies. -/
def demoPart (amount : Nat) : MPPPart where
  channel := ⟨0, 0, 0⟩
  amount := ⟨amount⟩
  cltv := DEFAULT_MIN_FINAL_CLTV

/-- A plan with an empty collection and the given advertised total. -/
def demoPlan (target : Nat) : MPPPlan where
  paymentHash := ⟨ByteArray.empty⟩
  paymentSecret := ⟨ByteArray.empty⟩
  target := ⟨target⟩
  parts := []

/-- The concrete over-total plan: `total_msat = 100`, two parts of 60 msat. -/
def overTotalPlan : MPPPlan :=
  { demoPlan 100 with parts := [demoPart 60, demoPart 60] }

/-- The running total of `overTotalPlan` is 120 msat. -/
theorem overTotalPlan_sum :
    sumParts overTotalPlan.parts = 120 := by
  simp [overTotalPlan, demoPlan, sumParts, demoPart]

/-- The advertised total of `overTotalPlan` is 100 msat. -/
theorem overTotalPlan_target : overTotalPlan.target.val = 100 := rfl

/-- Two parts of 60 msat sum to 120 msat, which exceeds the advertised total
of 100 msat. -/
theorem overTotal_sum_exceeds_target :
    ¬ sumParts [demoPart 60, demoPart 60] ≤ 100 := by
  simp only [sumParts, demoPart]
  omega

/-- **Mechanized refutation.**  The unconditional preservation law fails for
an over-total part even though the invariant held after the first part. -/
theorem overTotal_counterexample :
    ¬ (∀ (plan : MPPPlan) (collected : List MPPPart) (p : MPPPart),
        RunningTotalBound plan.target collected →
          RunningTotalBound plan.target (p :: collected)) := by
  intro h
  have h0 : RunningTotalBound overTotalPlan.target ([] : List MPPPart) :=
    runningTotalBound_nil _
  have h1 : RunningTotalBound overTotalPlan.target [demoPart 60] :=
    h overTotalPlan [] (demoPart 60) h0
  have h2 : RunningTotalBound overTotalPlan.target
      [demoPart 60, demoPart 60] :=
    h overTotalPlan [demoPart 60] (demoPart 60) h1
  exact overTotal_sum_exceeds_target (by
    simpa [RunningTotalBound, overTotalPlan_target] using h2)

/-- Each individual part of the counterexample plan passes the naive per-part
target check `amount ≤ total_msat`. -/
theorem overTotal_each_part_within_target :
    ∀ p ∈ overTotalPlan.parts, p.amount.val ≤ overTotalPlan.target.val := by
  intro p hp
  simp [overTotalPlan, demoPlan] at hp
  subst p
  simp [demoPart, overTotalPlan_target]

/-- The second part is rejected by the exact remaining-budget guard, which is
why the guarded theorem does not apply to this collection. -/
theorem overTotal_second_part_guard_fails :
    ¬ PartFits overTotalPlan.target [demoPart 60] (demoPart 60) := by
  unfold PartFits
  have hsum : sumParts [demoPart 60] = 60 := by
    simp [sumParts, demoPart]
  rw [hsum, overTotalPlan_target]
  simp only [demoPart]
  omega

/-- The over-total plan violates the invariant and is therefore not a
complete MPP plan under the model's exact-sum definition. -/
theorem overTotal_not_runningTotalBound :
    ¬ RunningTotalBound overTotalPlan.target overTotalPlan.parts := by
  intro h
  unfold RunningTotalBound at h
  rw [overTotalPlan_sum, overTotalPlan_target] at h
  omega

/-- The over-total plan is not complete. -/
theorem overTotal_not_complete : ¬ mppComplete overTotalPlan := by
  intro h
  exact overTotal_not_runningTotalBound
    (runningTotalBound_of_mppComplete h)

end LnLean.Proofs.ModelHardening.F14
