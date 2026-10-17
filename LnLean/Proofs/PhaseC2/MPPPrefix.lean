import LnLean.Payment.MPP

/-!
# LnLean.Proofs.PhaseC2.MPPPrefix

English claim.  For the BOLT 4 `basic_mpp` model in `LnLean.Payment.MPP`:

1. **Prefix sums are monotone.**  Every prefix of a plan's part list has a
   total no larger than the total of the whole list; under `mppComplete` every
   prefix total is therefore at most the plan target.
2. **A part never exceeds the total.**  Each part amount is at most the sum of
   the plan's parts (and hence at most the target of a complete plan).
3. **Completeness is exactly non-emptiness plus the sum law.**  `mppComplete`
   is definitionally equivalent to "the part list is non-empty and the parts
   sum to the target".  Without the non-emptiness conjunct the unrestricted
   equivalence is false: the empty plan with target zero has sum zero but is
   not complete.  The strongest true conditional form requires the non-empty
   hypothesis and is stated below.
4. **Atomic outcomes.**  The all-success and all-failure outcome lists
   positionally aligned with a plan's parts both satisfy `mppAtomic`; no mixed
   outcome is possible.
5. **Secret binding.**  The modelled binding hypothesis is
   `MPPPlan.bindsSecret plan s`, i.e. `plan.paymentSecret = s`.  Under it the
   secret is unique (transitivity of equality), and `paymentSecretBinding`
   equals the secret's byte string.  No cryptographic uniqueness or
   derivation of the secret is claimed here.

BOLT sections.
* BOLT 4 "Basic Multi-Part Payments": all HTLCs of a set share one
  `payment_hash`, one `payment_secret`, and one advertised `total_msat`; the
  final node fulfils all parts or none
  (`refs/bolts/04-onion-routing.md:349-410`).
* BOLT 4 "Final Payload" (`payment_data` with `payment_secret` and
  `total_msat`) and the final-node amount checks
  (`refs/bolts/04-onion-routing.md:204-220`, `:1528-1545`).
* BOLT 2 `update_add_htlc` carries `amount_msat`, `payment_hash`, and
  `cltv_expiry` per part (`refs/bolts/02-peer-protocol.md:2772-2790`).
* BOLT 9 feature bits 14/15 (`payment_secret`) and 16/17 (`basic_mpp`)
  (`refs/bolts/09-features.md:42-43`).

rust-lightning anchors (commit
`fe4900930c6bd5786ec4203274d7cf312776a5a6`).
* `lightning/src/ln/outbound_payment.rs:949` `check_merge`: all parts must
  agree on `payment_secret`, `payment_metadata`, and
  `total_mpp_amount_msat`.
* `lightning/src/ln/inbound_payment.rs:391` `verify`: the incoming
  `FinalOnionHopData` is checked against the registered secret/hash.
* `lightning/src/ln/onion_payment.rs:329` `FinalOnionHopData { payment_secret,
  total_msat }`, the per-part payload abstracted here.

Not modelled.
* Onion construction, route selection, fee arithmetic, and retry policy.
* The 60-second MPP collection window (`mpp_timeout`) and liveness.  The
  atomicity results are safety statements over already observed outcomes.
* BOLT 4's lower-bound completion (`sum ≥ total_msat`).  `mppComplete` is the
  exact-sum special case, flagged in the scaffold as the obligation
  `LN-PAY-MPP-OVERPAY`.
* Cryptographic derivation or encryption of the payment secret; only the
  opaque 32-byte field and its equality binding are modelled.
* The identity of an HTLC across parts (`channel_id`, `htlc_id`); `MPPPart`
  has only `(channel, amount, cltv)`.
-/

namespace LnLean.Proofs.PhaseC2

set_option autoImplicit false

open LnLean
open LnLean.Payment

namespace MPPPrefix

/-! ## 1. Prefix sums -/

/-- Every prefix of a part list has a total at most the total of the list. -/
theorem sumParts_take_le (ps : List MPPPart) (n : Nat) :
    sumParts (ps.take n) ≤ sumParts ps := by
  induction ps generalizing n with
  | nil => simp [sumParts]
  | cons p ps ih =>
      cases n with
      | zero => simp [sumParts]
      | succ k =>
          simp only [List.take_succ_cons, sumParts_cons]
          have h := ih k
          omega

/-- Extending a prefix by one part never decreases the running total. -/
theorem sumParts_take_succ_ge (ps : List MPPPart) (n : Nat) :
    sumParts (ps.take n) ≤ sumParts (ps.take (n + 1)) := by
  induction ps generalizing n with
  | nil => simp
  | cons p ps ih =>
      cases n with
      | zero => simp [sumParts]
      | succ k =>
          simp only [List.take_succ_cons, sumParts_cons]
          have h := ih k
          omega

/-- **Prefix-sum monotonicity.**  Longer prefixes have larger or equal
running totals. -/
theorem sumParts_take_mono (ps : List MPPPart) {m n : Nat} (h : m ≤ n) :
    sumParts (ps.take m) ≤ sumParts (ps.take n) := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => exact Nat.le_trans ih (sumParts_take_succ_ge ps _)

/-- Plan-level prefix bound: a prefix of `plan.parts` never exceeds the raw
plan total. -/
theorem plan_prefix_le_total (plan : MPPPlan) (n : Nat) :
    sumParts (plan.parts.take n) ≤ sumParts plan.parts :=
  sumParts_take_le plan.parts n

/-- Plan-level prefix monotonicity for `MPPPlan.parts`. -/
theorem plan_prefix_mono (plan : MPPPlan) {m n : Nat} (h : m ≤ n) :
    sumParts (plan.parts.take m) ≤ sumParts (plan.parts.take n) :=
  sumParts_take_mono plan.parts h

/-- Under completeness, every prefix of the plan's parts is at most the
target. -/
theorem plan_prefix_le_target {plan : MPPPlan} (h : mppComplete plan) (n : Nat) :
    sumParts (plan.parts.take n) ≤ plan.target.val := by
  have hle := plan_prefix_le_total plan n
  rw [h.2] at hle
  exact hle

/-! ## 2. No part exceeds the total -/

/-- Every part amount is at most the sum of all part amounts. -/
theorem part_amount_le_total (plan : MPPPlan) {p : MPPPart}
    (hp : p ∈ plan.parts) : p.amount.val ≤ sumParts plan.parts :=
  MPPPart.amount_le_sumParts hp

/-- In a complete plan no part amount exceeds the target. -/
theorem part_amount_le_target {plan : MPPPlan} (h : mppComplete plan)
    {p : MPPPart} (hp : p ∈ plan.parts) : p.amount.val ≤ plan.target.val := by
  have hle := part_amount_le_total plan hp
  rw [h.2] at hle
  exact hle

/-! ## 3. Completeness versus the sum law -/

/-- `mppComplete` is exactly the conjunction of non-emptiness and the exact
sum law. -/
theorem mppComplete_iff_nonempty_and_sum (plan : MPPPlan) :
    mppComplete plan ↔
      plan.parts ≠ [] ∧ sumParts plan.parts = plan.target.val :=
  Iff.rfl

/-- **Strongest unconditional form of the sum-law equivalence.**  When the
part list is known to be non-empty, completeness is equivalent to the parts
summing exactly to the target. -/
theorem mppComplete_iff_sum_eq_of_nonempty {plan : MPPPlan}
    (hne : plan.parts ≠ []) :
    mppComplete plan ↔ sumParts plan.parts = plan.target.val :=
  ⟨fun h => h.2, fun hsum => ⟨hne, hsum⟩⟩

/-- The non-emptiness hypothesis cannot be dropped.  The empty plan with
target zero has `sumParts [] = 0 = target`, but it is not `mppComplete`
because BOLT 4 requires a non-empty HTLC set. -/
theorem mppComplete_sum_eq_unrestricted_false :
    ¬ (∀ plan : MPPPlan,
        mppComplete plan ↔ sumParts plan.parts = plan.target.val) := by
  intro h
  let plan : MPPPlan :=
    { paymentHash := PaymentHash.mk ByteArray.empty
      paymentSecret := PaymentSecret.mk ByteArray.empty
      target := Msat.mk 0
      parts := [] }
  have hsum : sumParts plan.parts = plan.target.val := rfl
  have hcomplete : mppComplete plan := (h plan).mpr hsum
  exact hcomplete.1 rfl

/-! ## 4. Atomic all-success and all-failure outcome lists -/

/-- The outcome list in which every part succeeds, positionally aligned with
`plan.parts`. -/
def allSucceededOutcomes (plan : MPPPlan) : List PaymentState :=
  plan.parts.map (fun _ => PaymentState.succeeded)

/-- The outcome list in which every part fails, positionally aligned with
`plan.parts`. -/
def allFailedOutcomes (plan : MPPPlan) : List PaymentState :=
  plan.parts.map (fun _ => PaymentState.failed)

/-- A helper: a correctly aligned outcome list whose entries all equal one
terminal outcome is atomic. -/
theorem mppAtomic_of_all_eq {plan : MPPPlan} {outcomes : List PaymentState}
    (hlen : outcomes.length = plan.parts.length) {o : PaymentState}
    (ho : o = PaymentState.succeeded ∨ o = PaymentState.failed)
    (hall : ∀ s ∈ outcomes, s = o) : mppAtomic plan outcomes := by
  refine ⟨hlen, ?_⟩
  rcases ho with rfl | rfl
  · exact Or.inl hall
  · exact Or.inr hall

/-- **All-success atomicity.**  The all-success outcome list is atomic. -/
theorem mppAtomic_allSucceeded (plan : MPPPlan) :
    mppAtomic plan (allSucceededOutcomes plan) := by
  unfold allSucceededOutcomes
  refine mppAtomic_of_all_eq ?_ (Or.inl rfl) ?_
  · simp
  · intro s hs
    rcases List.mem_map.mp hs with ⟨p, _hp, rfl⟩
    rfl

/-- **All-failure atomicity.**  The all-failure outcome list is atomic. -/
theorem mppAtomic_allFailed (plan : MPPPlan) :
    mppAtomic plan (allFailedOutcomes plan) := by
  unfold allFailedOutcomes
  refine mppAtomic_of_all_eq ?_ (Or.inr rfl) ?_
  · simp
  · intro s hs
    rcases List.mem_map.mp hs with ⟨p, _hp, rfl⟩
    rfl

/-! ## 5. Explicit payment-secret binding hypothesis -/

/-- The binding hypothesis is definitionally equality of the plan's secret
with the expected secret `s`. -/
theorem bindsSecret_iff (plan : MPPPlan) (s : PaymentSecret) :
    plan.bindsSecret s ↔ plan.paymentSecret = s :=
  Iff.rfl

/-- Every plan binds its own secret (`rfl`). -/
theorem bindsSecret_self (plan : MPPPlan) :
    plan.bindsSecret plan.paymentSecret :=
  rfl

/-- **Uniqueness under the binding hypothesis.**  If a plan binds `s` and also
binds `t`, then `s = t`.  This is the only secret-uniqueness fact claimed: it
is equality of the modelled field, not cryptographic unforgeability. -/
theorem secret_unique_of_binds {plan : MPPPlan} {s t : PaymentSecret}
    (hs : plan.bindsSecret s) (ht : plan.bindsSecret t) : s = t :=
  MPPPlan.bindsSecret_unique hs ht

/-- Under the binding hypothesis the modelled secret byte-string equals the
expected secret's bytes. -/
theorem binding_eq_of_binds {plan : MPPPlan} {s : PaymentSecret}
    (hs : plan.bindsSecret s) :
    paymentSecretBinding plan = s.bytes := by
  unfold paymentSecretBinding
  rw [hs]

/-- The distribution invariant `MPPPlan.allPartsShareSecret` holds for every
plan: every secret accepted by the plan is the plan's own secret.  This is
vacuous by construction and records that parts need no separate secret field
in the model. -/
theorem allPartsShareSecret_holds (plan : MPPPlan) :
    plan.allPartsShareSecret := by
  intro s hs
  exact hs

end MPPPrefix

end LnLean.Proofs.PhaseC2
