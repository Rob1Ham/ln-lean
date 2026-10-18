import LnLean.Payment.HTLC
import LnLean.Payment.Invoice
import LnLean.Payment.Laws
import LnLean.Payment.MPP

/-!
# D30 — Running MPP total stays at or below `total_msat`

English claim (catalog `LN-PM-005`).  During MPP collection, each additional
part keeps the running total at or below the invoice's `total_msat`.

Model reading.  An `MPPPlan` names the target `total_msat` and the complete
list of parts.  `mppComplete` is the plan invariant: at least one part and
`sumParts plan.parts = plan.target.val` (the exact-sum form used by the model;
BOLT 4 allows `sum ≥ total_msat` and the overpay variant is the separate
obligation `LN-PAY-MPP-OVERPAY`).  A collection state is any sub-multiset
`collected <+ plan.parts` of the plan's parts; the running total is
`sumParts collected`, and the arrival-ordered running total after `n` parts is
`sumParts (plan.parts.take n)`.

What is proved:

* `waveD_d30_sumParts_sublist` — summing a sub-multiset never exceeds summing
  the whole list, because part amounts are natural numbers (non-negative).
* `waveD_d30_collected_set_bound` — under `mppComplete`, the running total of
  **any** sub-multiset of the parts is at most the target.  This covers parts
  arriving out of order, not just prefixes.
* `waveD_d30_add_part_preserves_bound` — the "each additional part" form: if
  `collected ++ [next]` is still a sub-multiset of the plan, the new running
  total is at most the target.
* `waveD_d30_add_part_within_remaining` — a stronger budget form: the next
  part's amount fits in the remaining budget `target - sumParts collected`.
* `waveD_d30_running_total_bound` — the prefix/running-total form for every
  `n`; `waveD_d30_running_total_mono` shows the running total is monotone and
  `waveD_d30_running_total_succ` shows how one arriving part increments it.
* `waveD_d30_running_total_complete` — after all parts have arrived the running
  total is exactly the target.
* `waveD_d30_unconditional_counterexample` — without the completeness
  invariant the claim is false: a one-part plan with amount 5 and target 3 has
  running total 5 above its target.  `waveD_d30_counterexample_not_complete`
  records that this plan fails `mppComplete`, so the conditional hypothesis is
  not removable by accident.

The conditional hypothesis `mppComplete plan` is the honest one: the model has
no accumulator state or per-add acceptance rule, so the bound is a property of
collections drawn from a complete HTLC set, not of an arbitrary `MPPPlan`.

BOLT anchors (pinned commit 1aadb719b4007c4cea0ba6e36b08c4fb53788dee).
* `refs/bolts/04-onion-routing.md:350-410` MPP HTLC-set rules and
  `total_msat` consistency.
* `refs/bolts/04-onion-routing.md:1528-1545` final-node amount checks.

LDK anchors (commit fe4900930c6bd5786ec4203274d7cf312776a5a6).
* `lightning/src/ln/onion_payment.rs:857` accumulated MPP value check.
* `lightning/src/ln/outbound_payment.rs:949` `check_merge`
  (`total_mpp_amount_msat` agreement across parts).
-/

namespace LnLean.Proofs.WaveD.D30

open LnLean.Payment
open List

set_option autoImplicit false

-- OBLIGATION: LN-WD-D30

/-! ## Summing sub-multisets -/

/-- Summing a sub-multiset of the parts never exceeds the sum over the whole
list.  `List.Sublist` keeps multiplicity, so a part counted twice is not
confused with a single occurrence. -/
theorem waveD_d30_sumParts_sublist {collected all : List MPPPart}
    (h : collected <+ all) : sumParts collected ≤ sumParts all := by
  induction h with
  | slnil => simp
  | cons q _ ih =>
      simp only [sumParts_cons]
      omega
  | cons_cons q _ ih =>
      simp only [sumParts_cons]
      omega

/-- During collection the parts observed so far form a sub-multiset of the
plan's parts.  If the plan is complete, the running total is at most
`total_msat`; this is independent of arrival order. -/
theorem waveD_d30_collected_set_bound {plan : MPPPlan}
    (hplan : mppComplete plan) {collected : List MPPPart}
    (hsub : collected <+ plan.parts) :
    sumParts collected ≤ plan.target.val := by
  have hle := waveD_d30_sumParts_sublist hsub
  rw [mppComplete_sum_eq_target hplan] at hle
  exact hle

/-- Adding one more part to an already-collected sub-multiset keeps the
running total at or below `total_msat`.  This is the literal "each additional
part" claim, stated for an arbitrary arrival order. -/
theorem waveD_d30_add_part_preserves_bound {plan : MPPPlan}
    (hplan : mppComplete plan) {collected : List MPPPart} {next : MPPPart}
    (hsub : collected ++ [next] <+ plan.parts) :
    sumParts (collected ++ [next]) ≤ plan.target.val :=
  waveD_d30_collected_set_bound hplan hsub

/-- Budget form of the step law: the next part's amount is at most the
remaining budget before it arrives.  This is the arithmetic content of the
per-add check that LDK performs against `total_msat`. -/
theorem waveD_d30_add_part_within_remaining {plan : MPPPlan}
    (hplan : mppComplete plan) {collected : List MPPPart} {next : MPPPart}
    (hsub : collected ++ [next] <+ plan.parts) :
    next.amount.val ≤ plan.target.val - sumParts collected := by
  have hnew := waveD_d30_add_part_preserves_bound hplan hsub
  have hsum : sumParts (collected ++ [next]) =
      sumParts collected + next.amount.val := by
    rw [sumParts_append]
    simp [sumParts]
  omega

/-! ## Arrival-ordered running total -/

/-- The running total after the first `n` parts have arrived. -/
def runningTotal (plan : MPPPlan) (n : Nat) : Nat :=
  sumParts (plan.parts.take n)

/-- The running total after every prefix of the collection is at or below
`total_msat`. -/
theorem waveD_d30_running_total_bound {plan : MPPPlan}
    (hplan : mppComplete plan) (n : Nat) :
    runningTotal plan n ≤ plan.target.val := by
  unfold runningTotal
  exact waveD_d30_collected_set_bound hplan (List.take_sublist n plan.parts)

/-- The running total is monotone in the number of collected parts. -/
theorem waveD_d30_running_total_mono (plan : MPPPlan) {m n : Nat}
    (hmn : m ≤ n) : runningTotal plan m ≤ runningTotal plan n := by
  unfold runningTotal
  have hsub : (plan.parts.take n).take m <+ plan.parts.take n :=
    List.take_sublist m (plan.parts.take n)
  have hle := waveD_d30_sumParts_sublist hsub
  have ht : (plan.parts.take n).take m = plan.parts.take m := by
    rw [List.take_take, Nat.min_eq_left hmn]
  rwa [ht] at hle

/-- One part arriving adds exactly its amount to the running total. -/
theorem waveD_d30_running_total_succ (plan : MPPPlan) {n : Nat}
    (hn : n < plan.parts.length) :
    runningTotal plan (n + 1) =
      runningTotal plan n + (plan.parts[n]'hn).amount.val := by
  unfold runningTotal
  rw [List.take_add_one]
  have hget : plan.parts[n]? = some (plan.parts[n]'hn) :=
    List.getElem?_eq_getElem hn
  rw [hget]
  rw [sumParts_append]
  simp [sumParts]

/-- Once every part has arrived the running total is exactly `total_msat`,
not merely bounded by it. -/
theorem waveD_d30_running_total_complete {plan : MPPPlan}
    (hplan : mppComplete plan) :
    runningTotal plan plan.parts.length = plan.target.val := by
  unfold runningTotal
  rw [List.take_length, mppComplete_sum_eq_target hplan]

/-! ## Why the completeness hypothesis is needed -/

/-- A plan whose single part (5 msat) already exceeds its target (3 msat). -/
def badPlan : MPPPlan where
  paymentHash := ⟨ByteArray.empty⟩
  paymentSecret := ⟨ByteArray.empty⟩
  target := ⟨3⟩
  parts := [{ channel := ⟨0, 0, 0⟩, amount := ⟨5⟩, cltv := 0 }]

/-- The unconditional claim "every plan's running total is at most its target"
is false: the target need not be consistent with the parts. -/
theorem waveD_d30_unconditional_counterexample :
    ¬ (∀ plan : MPPPlan, sumParts plan.parts ≤ plan.target.val) := by
  intro h
  have hbad := h badPlan
  simp [badPlan, sumParts] at hbad

/-- The counterexample plan is not `mppComplete`, so the hypothesis in the
positive theorems cannot be dropped: it is exactly the consistency condition
that rules this plan out. -/
theorem waveD_d30_counterexample_not_complete :
    ¬ mppComplete badPlan := by
  intro h
  have hsum := h.2
  simp [badPlan, sumParts] at hsum

end LnLean.Proofs.WaveD.D30
