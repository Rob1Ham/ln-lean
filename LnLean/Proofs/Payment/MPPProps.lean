import LnLean.Payment.MPP
import LnLean.Payment.HTLC

/-!
# LnLean.Proofs.Payment.MPPProps

English claim.  A BOLT 4 `basic_mpp` HTLC set is a list of parts collected
under one payment hash, one payment secret, and one `total_msat`.  This module
states and proves the payment-level laws of the wave-A MPP model:

1. **Sum law.**  If `mppComplete plan` holds, the sum of the part amounts is
   exactly `plan.target`.
2. **Per-part bound.**  In a complete plan no part exceeds the target, and a
   plan containing a positive part has a positive target.
3. **Shared hash and secret.**  `MPPPlan` carries exactly one `paymentHash`
   and one `paymentSecret`; every part observed against the plan (a
   `WirePart` satisfying `WirePart.matches`) therefore has the same hash and
   the same secret.  Merging two plans (`Mergeable`, the model of LDK
   `check_merge`) forces the merged parts to agree on both fields.
4. **Atomicity.**  `settleParts` settles every part of a pending session with
   one outcome.  From an all-pending session the result satisfies the exact
   all-or-nothing predicate `AllOrNothing`: every part succeeded, or every
   part failed.  A mixed outcome is impossible, and the predicate is stable
   under later settlement attempts.
5. **Duplicates.**  The list concatenation `sumParts` counts literal
   duplicates twice; the protocol collector `addParts` keys on the whole
   `MPPPart` record and is idempotent.  Re-adding a present part adds nothing,
   the collected total never exceeds the raw total, and for a `Nodup` list
   the collected total equals the raw total.  Full-record keying is *not*
   enough to collapse same-channel/same-CLTV parts whose amounts differ; the
   model has no `htlc_id`, so that gap is stated explicitly
   (`sameKey_distinctAmount_both_counted`).
6. **Settlement idempotence.**  Settling a part (or the session containing it)
   that is already settled is a no-op, and terminal sessions absorb any later
   settlement request.

BOLT sections.
* BOLT 4 "Basic Multi-Part Payments" (`refs/bolts/04-onion-routing.md:349`):
  all HTLCs in a set use the same `payment_hash`; the writer sets `total_msat`
  and the set's `amt_to_forward` total is at least `total_msat`; the final node
  adds the HTLC to the set for that hash, requires `payment_secret`, fulfils
  all HTLCs of the set or none, and MUST NOT fulfil any while the total is
  below `total_msat`.
* BOLT 4 "Payload for the Last Node" (`payment_data` `payment_secret`,
  `total_msat`): `refs/bolts/04-onion-routing.md:204-220`.
* BOLT 4 final-node checks (`min_final_cltv_expiry_delta`, amount and secret):
  `refs/bolts/04-onion-routing.md:328-345` and `:1528-1550`.
* BOLT 2 "Adding an HTLC: `update_add_htlc`" carries `amount_msat`,
  `payment_hash`, and `cltv_expiry` per part:
  `refs/bolts/02-peer-protocol.md:2772-2795`.  BOLT 2 does not carry a payment
  secret; the secret is a BOLT 4/BOLT 11 object.
* BOLT 11 `p` (payment hash) and `s` (payment secret), and BOLT 9 feature bits
  14/15 (`payment_secret`) and 16/17 (`basic_mpp`).

rust-lightning anchors (commit `fe4900930c6bd5786ec4203274d7cf312776a5a6`).
* `lightning/src/ln/outbound_payment.rs:948` `check_merge`: all parts of a set
  must agree on `payment_secret`, `payment_metadata`, and
  `total_mpp_amount_msat` (`:951-955`).
* `lightning/src/ln/outbound_payment.rs:137` `Retryable::total_msat`
  (the set's advertised total) and `:285` the `total_msat` accessor.
* `lightning/src/ln/inbound_payment.rs:391` `verify`: the incoming
  `FinalOnionHopData` is checked against the registered payment secret/hash.
* `lightning/src/ln/inbound_payment.rs:506` the final node fails an HTLC whose
  `payment_data.total_msat` is below the registered minimum.
* `lightning/src/ln/onion_payment.rs:329` `FinalOnionHopData { payment_secret,
  total_msat }`, the per-part payload this module abstracts.

Explicitly NOT modelled.
* Onion construction, route selection, fee arithmetic, and retry policy.
  A part is an `MPPPart`/`PaymentPart` value with an amount and a CLTV.
* The 60-second `mpp_timeout` collection window and liveness: this module
  proves safety ("never a mixed outcome"), not eventual settlement.
* `mppComplete` requires an exact sum.  BOLT 4 allows a set total
  `≥ total_msat`; the exact form is the conservative special case.  The
  overpay variant (`LN-PAY-MPP-OVERPAY`) needs a link to the BOLT 11 invoice
  amount, which `MPPPlan` does not carry.
* `payment_secret` derivation/encryption (LDK `construct_payment_secret`) and
  preimage soundness.  Only the opaque 32-byte secret and the opaque payment
  hash are modelled; `PaymentSession.settle` does not check a preimage.
* The identity of an HTLC across parts (`channel_id`, `htlc_id`).  `MPPPart`
  has only `(channel, amount, cltv)`, so duplicate detection here is
  whole-record equality, strictly weaker than LDK's per-HTLC bookkeeping.
* Fees, `htlc_minimum_msat`, and channel liquidity bounds.
-/

namespace LnLean.Payment

set_option autoImplicit false

open LnLean

namespace MPPProps

/-! ## 1. Sums, completeness, and target bounds -/

/-- A list of parts sums to zero exactly when every part amount is zero.
This is the arithmetic form of "no part is silently lost from the set". -/
theorem sumParts_eq_zero_iff (ps : List MPPPart) :
    sumParts ps = 0 ↔ ∀ p ∈ ps, p.amount.val = 0 := by
  induction ps with
  | nil => simp
  | cons q qs ih =>
      rw [sumParts_cons]
      constructor
      · intro h p hp
        rcases List.mem_cons.mp hp with rfl | hmem
        · omega
        · have hq : q.amount.val = 0 := by omega
          have hqs : sumParts qs = 0 := by omega
          exact (ih.mp hqs) p hmem
      · intro h
        have hq : q.amount.val = 0 := h q (by simp)
        have hqs : sumParts qs = 0 := ih.mpr (fun p hp => h p (by simp [hp]))
        omega

/-- A positive part makes the total positive. -/
theorem sumParts_pos_of_mem_pos {ps : List MPPPart} {p : MPPPart}
    (hp : p ∈ ps) (hpos : 0 < p.amount.val) : 0 < sumParts ps := by
  have hle := MPPPart.amount_le_sumParts hp
  omega

/-- **Sum law.**  A complete MPP plan's parts sum exactly to the target. -/
theorem mppComplete_sum_eq_target {plan : MPPPlan} (h : mppComplete plan) :
    sumParts plan.parts = plan.target.val :=
  h.2

/-- A complete plan is non-empty (BOLT 4: an HTLC set needs at least one
HTLC). -/
theorem mppComplete_nonempty {plan : MPPPlan} (h : mppComplete plan) :
    plan.parts ≠ [] :=
  h.1

/-- **Per-part bound.**  No part of a complete plan exceeds the target. -/
theorem mppComplete_no_part_exceeds_target {plan : MPPPlan}
    (h : mppComplete plan) {p : MPPPart} (hp : p ∈ plan.parts) :
    p.amount.val ≤ plan.target.val := by
  have hle := MPPPart.amount_le_sumParts hp
  rw [mppComplete_sum_eq_target h] at hle
  exact hle

/-- A complete plan with a positive part has a positive target.  The
correction matters: a plan consisting only of zero-amount parts is complete
with `target = 0`, so "`mppComplete` implies a positive target" is false. -/
theorem mppComplete_target_pos_of_pos_part {plan : MPPPlan}
    (h : mppComplete plan) {p : MPPPart} (hp : p ∈ plan.parts)
    (hpos : 0 < p.amount.val) : 0 < plan.target.val := by
  have hpos' := sumParts_pos_of_mem_pos hp hpos
  rw [mppComplete_sum_eq_target h] at hpos'
  exact hpos'

/-! ## 2. Structural well-formedness (BOLT 4 final-node checks) -/

/-- The structural checks a recipient applies to an MPP plan: non-emptiness,
the exact-sum condition, and the final-CLTV floor.  The hash and secret are
plan-level fields, so "all parts agree" is not a field here; see
`WirePart.matches` for the externally observed form. -/
structure WellFormed (plan : MPPPlan) : Prop where
  nonempty : plan.parts ≠ []
  exactSum : sumParts plan.parts = plan.target.val
  cltvFloor : ∀ p ∈ plan.parts, plan.minFinalCltv ≤ p.cltv

/-- Well-formedness implies `mppComplete`. -/
theorem wellFormed_complete {plan : MPPPlan} (h : WellFormed plan) :
    mppComplete plan :=
  ⟨h.nonempty, h.exactSum⟩

/-- Every part of a well-formed plan respects the invoice's
`min_final_cltv_expiry_delta` (BOLT 4 final-node CLTV check). -/
theorem wellFormed_cltvFloor {plan : MPPPlan} (h : WellFormed plan)
    {p : MPPPart} (hp : p ∈ plan.parts) : plan.minFinalCltv ≤ p.cltv :=
  h.cltvFloor p hp

/-- The per-part target bound also follows from well-formedness. -/
theorem wellFormed_no_part_exceeds_target {plan : MPPPlan} (h : WellFormed plan)
    {p : MPPPart} (hp : p ∈ plan.parts) : p.amount.val ≤ plan.target.val :=
  mppComplete_no_part_exceeds_target (wellFormed_complete h) hp

/-! ## 3. Duplicate parts and the collecting fold

`sumParts` is a plain list sum: a literal duplicate contributes twice.  The
protocol's collector below adds a part only when the exact `MPPPart` record is
absent, mirroring "add the HTLC to the HTLC set" (BOLT 4) and LDK's
per-part bookkeeping.  Its laws are the model-level statement that duplicate
parts do not double-count. -/

/-- Boolean membership for `MPPPart`, using the derived `DecidableEq`.
Written explicitly because the scaffold does not register a `LawfulBEq`
instance for `MPPPart`, so `List.contains` is unavailable for proofs. -/
def containsPart : List MPPPart → MPPPart → Bool
  | [], _ => false
  | q :: qs, p => if q = p then true else containsPart qs p

/-- Boolean membership agrees with `List.Mem`. -/
theorem containsPart_iff (ps : List MPPPart) (p : MPPPart) :
    containsPart ps p = true ↔ p ∈ ps := by
  induction ps with
  | nil => simp [containsPart]
  | cons q qs ih =>
      rw [containsPart]
      by_cases h : q = p
      · subst h
        simp
      · have hp : p ≠ q := fun hpq => h hpq.symm
        simp only [h, ite_false, ih, List.mem_cons, hp, false_or]

/-- Add a part to a collected set unless the identical part is already
present. -/
def addPart (ps : List MPPPart) (p : MPPPart) : List MPPPart :=
  if containsPart ps p then ps else p :: ps

/-- **Re-adding a present part adds nothing.**  This is the core
no-double-count law for an already collected part. -/
theorem sumParts_addPart_of_mem {ps : List MPPPart} {p : MPPPart}
    (h : p ∈ ps) : sumParts (addPart ps p) = sumParts ps := by
  have hc : containsPart ps p = true := (containsPart_iff ps p).mpr h
  simp [addPart, hc]

/-- A genuinely new part adds exactly its amount. -/
theorem sumParts_addPart_of_not_mem {ps : List MPPPart} {p : MPPPart}
    (h : p ∉ ps) : sumParts (addPart ps p) = p.amount.val + sumParts ps := by
  have hc : containsPart ps p = false := by
    cases hb : containsPart ps p
    · rfl
    · exact absurd ((containsPart_iff ps p).mp hb) h
  simp [addPart, hc]

/-- The collector is idempotent on the same part. -/
theorem addPart_idem (ps : List MPPPart) (p : MPPPart) :
    addPart (addPart ps p) p = addPart ps p := by
  by_cases h : p ∈ ps
  · have hc : containsPart ps p = true := (containsPart_iff ps p).mpr h
    simp [addPart, hc]
  · have hc : containsPart ps p = false := by
      cases hb : containsPart ps p
      · rfl
      · exact absurd ((containsPart_iff ps p).mp hb) h
    have h1 : addPart ps p = p :: ps := by simp [addPart, hc]
    rw [h1]
    have hc' : containsPart (p :: ps) p = true :=
      (containsPart_iff _ _).mpr (List.mem_cons_self ..)
    simp [addPart, hc']

/-- Collect a list of parts into a duplicate-free set, in the order in which
new parts are first seen (most recent first). -/
def addParts (ps : List MPPPart) : List MPPPart :=
  ps.foldl addPart []

/-- Membership in the result of one `addPart` step: the new element is
present, and membership in the accumulator is unchanged. -/
theorem mem_addPart {acc : List MPPPart} {q p : MPPPart} :
    p ∈ addPart acc q ↔ p = q ∨ p ∈ acc := by
  unfold addPart
  by_cases hq : q ∈ acc
  · have hc : containsPart acc q = true := (containsPart_iff acc q).mpr hq
    rw [ite_eq_left hc]
    exact ⟨Or.inr, fun h => h.elim (fun hpq => hpq ▸ hq) id⟩
  · have hc : containsPart acc q ≠ true := fun h => hq ((containsPart_iff acc q).mp h)
    rw [ite_eq_right hc]
    exact List.mem_cons

/-- Membership in a fold of `addPart`: the collected list contains exactly
the elements of the accumulator together with the elements of the input. -/
theorem mem_foldl_addPart (ps acc : List MPPPart) (p : MPPPart) :
    p ∈ ps.foldl addPart acc ↔ p ∈ acc ∨ p ∈ ps := by
  induction ps generalizing acc with
  | nil => simp
  | cons q qs ih =>
      rw [List.foldl_cons, ih, mem_addPart]
      constructor
      · intro h
        rcases h with (hpq | hp) | hq
        · exact Or.inr (by simp [hpq])
        · exact Or.inl hp
        · exact Or.inr (by simp [hq])
      · intro h
        rcases h with hp | hpq
        · exact Or.inl (Or.inr hp)
        · rcases List.mem_cons.mp hpq with hpq | hq
          · exact Or.inl (Or.inl hpq)
          · exact Or.inr hq

/-- The collected list is duplicate-free whenever the accumulator is. -/
theorem nodup_foldl_addPart (ps acc : List MPPPart) (hacc : acc.Nodup) :
    (ps.foldl addPart acc).Nodup := by
  induction ps generalizing acc with
  | nil => exact hacc
  | cons q qs ih =>
      rw [List.foldl_cons]
      apply ih
      unfold addPart
      by_cases hq : q ∈ acc
      · have hc : containsPart acc q = true := (containsPart_iff acc q).mpr hq
        rw [ite_eq_left hc]
        exact hacc
      · have hc : containsPart acc q ≠ true := fun h => hq ((containsPart_iff acc q).mp h)
        rw [ite_eq_right hc]
        exact List.nodup_cons.mpr ⟨hq, hacc⟩

/-- The collector always returns a duplicate-free list. -/
theorem nodup_addParts (ps : List MPPPart) : (addParts ps).Nodup :=
  nodup_foldl_addPart ps [] (by simp)

/-- The collected list has exactly the membership of the raw list: collecting
removes duplicates but never drops a distinct part. -/
theorem mem_addParts (ps : List MPPPart) (p : MPPPart) :
    p ∈ addParts ps ↔ p ∈ ps := by
  unfold addParts
  rw [mem_foldl_addPart]
  simp

/-- The collected total never exceeds the raw list total: duplicate handling
can only remove amount, never invent it. -/
theorem sumParts_addParts_le_aux (ps acc : List MPPPart) :
    sumParts (ps.foldl addPart acc) ≤ sumParts acc + sumParts ps := by
  induction ps generalizing acc with
  | nil => simp
  | cons p ps ih =>
      have h1 : sumParts (addPart acc p) ≤ p.amount.val + sumParts acc := by
        by_cases h : p ∈ acc
        · rw [sumParts_addPart_of_mem h]; omega
        · rw [sumParts_addPart_of_not_mem h]; omega
      have h2 := ih (addPart acc p)
      simp only [List.foldl_cons] at h2 ⊢
      simp only [sumParts_cons]
      omega

/-- **Duplicates do not inflate the collected total.** -/
theorem sumParts_addParts_le_sumParts (ps : List MPPPart) :
    sumParts (addParts ps) ≤ sumParts ps := by
  have h := sumParts_addParts_le_aux ps []
  simpa [addParts] using h

/-- Auxiliary form of `sumParts_addParts_of_nodup`: when the accumulator is
disjoint from the remaining list and that list is duplicate-free, the fold
just prepends, so the sum is the sum of both pieces. -/
theorem sumParts_foldl_addPart_of_disjoint (ps acc : List MPPPart)
    (hdisj : ∀ p ∈ acc, p ∉ ps) (hnd : ps.Nodup) :
    sumParts (ps.foldl addPart acc) = sumParts acc + sumParts ps := by
  induction ps generalizing acc with
  | nil => simp
  | cons p ps ih =>
      rw [List.nodup_cons] at hnd
      obtain ⟨hp_notin, hnd_ps⟩ := hnd
      have hp_notacc : p ∉ acc := fun hpacc => (hdisj p hpacc) (List.mem_cons_self ..)
      have hc : containsPart acc p = false := by
        cases hb : containsPart acc p
        · rfl
        · exact absurd ((containsPart_iff acc p).mp hb) hp_notacc
      have hstep : addPart acc p = p :: acc := by simp [addPart, hc]
      have hdisj' : ∀ q ∈ p :: acc, q ∉ ps := by
        intro q hq
        rcases List.mem_cons.mp hq with rfl | hqacc
        · exact hp_notin
        · exact fun hqps => hdisj q hqacc (List.mem_cons_of_mem p hqps)
      rw [List.foldl_cons, hstep, ih (p :: acc) hdisj' hnd_ps]
      simp only [sumParts_cons]
      omega

/-- **For a duplicate-free plan the collector preserves the exact total.**
Hence the exact-sum `mppComplete` law and the distinct-part law coincide on
the intended (duplicate-free) HTLC set. -/
theorem sumParts_addParts_of_nodup (ps : List MPPPart) (hnd : ps.Nodup) :
    sumParts (addParts ps) = sumParts ps := by
  have h := sumParts_foldl_addPart_of_disjoint ps [] (by simp) hnd
  simpa [addParts] using h

/-- Completeness stated over the duplicate-free collection. -/
def mppCompleteDistinct (plan : MPPPlan) : Prop :=
  plan.parts ≠ [] ∧ sumParts (addParts plan.parts) = plan.target.val

/-- A complete duplicate-free plan is also complete over its collected
(distinct) parts. -/
theorem mppComplete_distinct_of_nodup {plan : MPPPlan} (h : mppComplete plan)
    (hnd : plan.parts.Nodup) : mppCompleteDistinct plan :=
  ⟨h.1, by rw [sumParts_addParts_of_nodup plan.parts hnd, mppComplete_sum_eq_target h]⟩

/-- Two parts with the same outgoing channel and CLTV but different amounts
are different records and are both retained by `addParts`.  This records the
model gap: without an `htlc_id`, whole-record equality cannot detect all
protocol-level duplicates. -/
theorem sameKey_distinctAmount_both_counted (p q : MPPPart)
    (_hchannel : p.channel = q.channel) (_hcltv : p.cltv = q.cltv)
    (hamount : p.amount ≠ q.amount) :
    p ∈ addParts [p, q] ∧ q ∈ addParts [p, q] ∧
      sumParts [p, q] = p.amount.val + q.amount.val := by
  have hpq : p ≠ q := by
    intro hpq
    exact hamount (congrArg MPPPart.amount hpq)
  have hqp : q ≠ p := fun h => hpq h.symm
  have h1 : addParts [p, q] = [q, p] := by
    simp [addParts, addPart, containsPart, hpq]
  refine ⟨?_, ?_, by simp [sumParts]⟩
  · rw [h1]; simp
  · rw [h1]; simp

/-! ## 4. Settlement: per-part idempotence and set atomicity -/

/-- Settle one part.  A terminal part is absorbing, mirroring
`PaymentSession.settle` at the session level. -/
def settlePart (p : PaymentPart) (outcome : PaymentState) : PaymentPart :=
  if p.state = .pending then { p with state := outcome } else p

/-- **Settling an already-settled part is idempotent**, for every requested
outcome. -/
theorem settlePart_idempotent (p : PaymentPart) (outcome : PaymentState) :
    settlePart (settlePart p outcome) outcome = settlePart p outcome := by
  unfold settlePart
  by_cases hp : p.state = .pending
  · by_cases ho : outcome = .pending
    · simp [hp, ho]
    · simp [hp, ho]
  · simp [hp]

/-- Settle the whole session atomically: the session state and every pending
part move to the same outcome.  A terminal session is left untouched. -/
def settleParts (s : PaymentSession) (outcome : PaymentState) : PaymentSession :=
  if s.state = .pending then
    { s with state := outcome, parts := s.parts.map (fun p => settlePart p outcome) }
  else s

/-- On a pending session, `settleParts` installs the requested session
state. -/
theorem settleParts_state_pending {s : PaymentSession} {outcome : PaymentState}
    (hs : s.state = .pending) : (settleParts s outcome).state = outcome := by
  simp [settleParts, hs]

/-- On a pending session, `settleParts` settles every part with the same
outcome. -/
theorem settleParts_parts_pending {s : PaymentSession} {outcome : PaymentState}
    (hs : s.state = .pending) :
    (settleParts s outcome).parts = s.parts.map (fun p => settlePart p outcome) := by
  simp [settleParts, hs]

/-- A terminal session absorbs any settlement attempt, parts included. -/
theorem settleParts_terminal {s : PaymentSession} {outcome : PaymentState}
    (hs : s.state.isTerminal) : settleParts s outcome = s := by
  have hne := PaymentState.not_pending_of_terminal hs
  simp [settleParts, hne]

/-- Every part of the session is still pending. -/
def AllPending (s : PaymentSession) : Prop :=
  ∀ p ∈ s.parts, p.state = .pending

/-- **The exact all-or-nothing predicate over the model's part set**: either
every part has succeeded, or every part has failed.  There is no third case
and no mixed outcome. -/
def AllOrNothing (s : PaymentSession) : Prop :=
  (∀ p ∈ s.parts, p.state = .succeeded) ∨
  (∀ p ∈ s.parts, p.state = .failed)

/-- After settling an all-pending session, every part carries the common
outcome. -/
theorem settleParts_all_state (s : PaymentSession) (outcome : PaymentState)
    (hsp : s.state = .pending) (hp : AllPending s) :
    ∀ p ∈ (settleParts s outcome).parts, p.state = outcome := by
  intro p hmem
  rw [settleParts_parts_pending hsp] at hmem
  rcases List.mem_map.mp hmem with ⟨q, hq, rfl⟩
  have hqstate : q.state = .pending := hp q hq
  unfold settlePart
  simp [hqstate]

/-- **Atomic success**: settling an all-pending set fulfils every part. -/
theorem settleParts_allOrNothing_succeeded (s : PaymentSession)
    (hsp : s.state = .pending) (hp : AllPending s) :
    AllOrNothing (settleParts s .succeeded) :=
  Or.inl (settleParts_all_state s .succeeded hsp hp)

/-- **Atomic failure**: settling an all-pending set fails every part. -/
theorem settleParts_allOrNothing_failed (s : PaymentSession)
    (hsp : s.state = .pending) (hp : AllPending s) :
    AllOrNothing (settleParts s .failed) :=
  Or.inr (settleParts_all_state s .failed hsp hp)

/-- **No mixed outcome.**  A part that succeeded and a part that failed
cannot both belong to an all-or-nothing set. -/
theorem allOrNothing_no_mixed {s : PaymentSession} (h : AllOrNothing s)
    {p q : PaymentPart} (hp : p ∈ s.parts) (hq : q ∈ s.parts)
    (hps : p.state = .succeeded) (hqf : q.state = .failed) : False := by
  rcases h with h | h
  · rw [h q hq] at hqf
    cases hqf
  · rw [h p hp] at hps
    cases hps

/-- Atomicity is stable: once a session's parts are all-or-nothing, no later
settlement attempt (with any outcome) can produce a mixed set. -/
theorem allOrNothing_settleParts_stable {s : PaymentSession} (h : AllOrNothing s)
    (outcome : PaymentState) : AllOrNothing (settleParts s outcome) := by
  by_cases hsp : s.state = .pending
  · rcases h with h | h
    · left
      intro p hmem
      rw [settleParts_parts_pending hsp] at hmem
      rcases List.mem_map.mp hmem with ⟨q, hq, rfl⟩
      have hqsucc : q.state = .succeeded := h q hq
      unfold settlePart
      simp [hqsucc]
    · right
      intro p hmem
      rw [settleParts_parts_pending hsp] at hmem
      rcases List.mem_map.mp hmem with ⟨q, hq, rfl⟩
      have hqfail : q.state = .failed := h q hq
      unfold settlePart
      simp [hqfail]
  · have hterm : s.state.isTerminal := by
      cases hs : s.state with
      | pending => exact absurd hs hsp
      | succeeded => simp [PaymentState.isTerminal]
      | failed => simp [PaymentState.isTerminal]
    rw [settleParts_terminal hterm]
    exact h

/-- The full session settlement is idempotent: settling twice with the same
outcome equals settling once, so re-settling an already-settled session
(parts included) changes nothing. -/
theorem settleParts_idempotent (s : PaymentSession) (outcome : PaymentState) :
    settleParts (settleParts s outcome) outcome = settleParts s outcome := by
  unfold settleParts
  by_cases hsp : s.state = .pending
  · by_cases ho : outcome = .pending
    · subst ho
      simp [hsp, List.map_map, settlePart_idempotent]
    · simp [hsp, ho]
  · simp [hsp]

/-- The session's payment hash is untouched by settlement. -/
theorem settleParts_paymentHash (s : PaymentSession) (outcome : PaymentState) :
    (settleParts s outcome).paymentHash = s.paymentHash := by
  by_cases hsp : s.state = .pending
  · simp [settleParts, hsp]
  · simp [settleParts, hsp]

/-- Settlement preserves the number of parts: no part is dropped. -/
theorem settleParts_parts_length (s : PaymentSession) (outcome : PaymentState) :
    (settleParts s outcome).parts.length = s.parts.length := by
  by_cases hsp : s.state = .pending
  · simp [settleParts, hsp]
  · simp [settleParts, hsp]

/-! ## 5. Shared payment hash and payment secret

`MPPPlan` stores the hash and the secret once, at plan level.  Every part is
therefore bound to the same values *by construction*.  For parts observed on
the wire, whose fields are not checked by the type, the binding is the
predicate `WirePart.matches`; the theorems below are the conditional form. -/

/-- A part as observed on the wire: BOLT 2 `update_add_htlc` fields plus the
BOLT 4 per-part `payment_hash`/`payment_secret` that must match the set. -/
structure WirePart where
  channel : ShortChannelId
  amount : Msat
  cltv : Height
  paymentHash : PaymentHash
  paymentSecret : PaymentSecret
deriving Repr, DecidableEq

/-- An observed part is accepted into `plan`'s HTLC set when it carries the
plan's hash and secret and does not exceed the plan's target.  This is the
conjunction of the BOLT 4 set checks and the BOLT 4 amount check. -/
def WirePart.matches (w : WirePart) (plan : MPPPlan) : Prop :=
  w.paymentHash = plan.paymentHash ∧
    w.paymentSecret = plan.paymentSecret ∧
    w.amount.val ≤ plan.target.val

/-- **Shared payment hash.**  Any two parts accepted into the same plan carry
the same payment hash (BOLT 4: "MUST use the same `payment_hash` on all HTLCs
in the set"). -/
theorem WirePart.matches_hash {w₁ w₂ : WirePart} {plan : MPPPlan}
    (h₁ : w₁.matches plan) (h₂ : w₂.matches plan) :
    w₁.paymentHash = w₂.paymentHash :=
  h₁.1.trans h₂.1.symm

/-- **Shared payment secret.**  Any two parts accepted into the same plan
carry the same payment secret (BOLT 4 final node: `payment_secret` must match;
LDK `check_merge` rejects a part whose secret differs). -/
theorem WirePart.matches_secret {w₁ w₂ : WirePart} {plan : MPPPlan}
    (h₁ : w₁.matches plan) (h₂ : w₂.matches plan) :
    w₁.paymentSecret = w₂.paymentSecret :=
  h₁.2.1.trans h₂.2.1.symm

/-- An accepted part's secret binding equals the plan's byte-string binding. -/
theorem WirePart.matches_binding {w : WirePart} {plan : MPPPlan}
    (h : w.matches plan) :
    w.paymentSecret.bytes = paymentSecretBinding plan := by
  unfold paymentSecretBinding
  rw [h.2.1]

/-- Every part of a plan, lifted to the wire view with the plan's own hash and
secret, is accepted by that plan (given the per-part amount bound). -/
def WirePart.ofPart (plan : MPPPlan) (p : MPPPart) : WirePart :=
  { channel := p.channel
    amount := p.amount
    cltv := p.cltv
    paymentHash := plan.paymentHash
    paymentSecret := plan.paymentSecret }

/-- The lifted view satisfies `matches` under the per-part target bound. -/
theorem WirePart.ofPart_matches (plan : MPPPlan) (p : MPPPart)
    (hp : p.amount.val ≤ plan.target.val) : (WirePart.ofPart plan p).matches plan :=
  ⟨rfl, rfl, hp⟩

/-- All lifted parts of one plan share the hash by construction (`rfl`). -/
theorem WirePart.ofPart_hash_eq (plan : MPPPlan) (p q : MPPPart) :
    (WirePart.ofPart plan p).paymentHash = (WirePart.ofPart plan q).paymentHash :=
  rfl

/-- All lifted parts of one plan share the secret by construction (`rfl`). -/
theorem WirePart.ofPart_secret_eq (plan : MPPPlan) (p q : MPPPart) :
    (WirePart.ofPart plan p).paymentSecret = (WirePart.ofPart plan q).paymentSecret :=
  rfl

/-- The merge condition of LDK `check_merge`: two plans may join one HTLC set
only when they agree on the payment hash, the payment secret, and the
advertised total. -/
def Mergeable (a b : MPPPlan) : Prop :=
  a.paymentHash = b.paymentHash ∧
    a.paymentSecret = b.paymentSecret ∧
      a.target = b.target

/-- **Merged parts share hash and secret.**  This is the plan-level form of
`check_merge`: the conjunction of the three equality checks is exactly what
makes the joined set a single BOLT 4 HTLC set. -/
theorem mergeable_parts_share {a b : MPPPlan} (h : Mergeable a b)
    {p q : MPPPart} (_hp : p ∈ a.parts) (_hq : q ∈ b.parts) :
    a.paymentHash = b.paymentHash ∧ a.paymentSecret = b.paymentSecret :=
  ⟨h.1, h.2.1⟩

/-- A mergeable pair advertises the same target, so the per-part bound is
preserved across the join. -/
theorem mergeable_target_eq {a b : MPPPlan} (h : Mergeable a b) :
    a.target = b.target :=
  h.2.2

/-! ## 6. Bridge to the wave-A atomicity predicate -/

/-- The outcome sequence of a session, positionally aligned with its parts. -/
def outcomeList (s : PaymentSession) : List PaymentState :=
  s.parts.map (fun p => p.state)

/-- `AllOrNothing` is exactly the "all success or all failure" disjunction
over the session's outcome sequence. -/
theorem allOrNothing_iff_outcomeList {s : PaymentSession} :
    AllOrNothing s ↔
      ((∀ o ∈ outcomeList s, o = .succeeded) ∨
        (∀ o ∈ outcomeList s, o = .failed)) := by
  unfold AllOrNothing outcomeList
  constructor
  · rintro (h | h)
    · left
      intro o ho
      rcases List.mem_map.mp ho with ⟨p, hp, rfl⟩
      exact h p hp
    · right
      intro o ho
      rcases List.mem_map.mp ho with ⟨p, hp, rfl⟩
      exact h p hp
  · rintro (h | h)
    · left
      intro p hp
      exact h p.state (List.mem_map_of_mem hp)
    · right
      intro p hp
      exact h p.state (List.mem_map_of_mem hp)

/-- The wave-A `mppAtomic` predicate is the same all-or-nothing condition,
once the outcome list is aligned with the plan's parts.  This connects the
plan-level definition in `LnLean.Payment.MPP` to the session-level predicate
used for settlement. -/
theorem mppAtomic_iff_allOutcomes (plan : MPPPlan) (outcomes : List PaymentState)
    (hlen : outcomes.length = plan.parts.length) :
    mppAtomic plan outcomes ↔
      ((∀ o ∈ outcomes, o = .succeeded) ∨
        (∀ o ∈ outcomes, o = .failed)) := by
  unfold mppAtomic
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨hlen, h⟩

/-- BOLT 4's actual completion condition is a lower bound
(`total ≥ total_msat`); `mppComplete` is the exact-sum special case.  This
records the implication the model supports and keeps the overpay variant as
the open obligation `LN-PAY-MPP-OVERPAY`. -/
def mppCompleteGe (plan : MPPPlan) : Prop :=
  plan.parts ≠ [] ∧ plan.target.val ≤ sumParts plan.parts

/-- Exact completeness implies lower-bound completeness. -/
theorem mppComplete_implies_completeGe {plan : MPPPlan} (h : mppComplete plan) :
    mppCompleteGe plan :=
  ⟨h.1, by rw [mppComplete_sum_eq_target h]; exact Nat.le_refl _⟩

/-- Order independence of the plain sum: permuting parts does not change the
total.  Proved by induction on the permutation derivation. -/
theorem sumParts_perm {ps qs : List MPPPart} (h : ps.Perm qs) :
    sumParts ps = sumParts qs := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp [sumParts, ih]
  | swap x y l => simp [sumParts]; omega
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- The collected (duplicate-free) total depends only on the multiset of
parts, not on their arrival order.  Proof: the collector preserves membership
(`mem_addParts`) and produces duplicate-free lists (`nodup_addParts`); two
duplicate-free lists with the same elements are permutations
(`List.perm_ext_iff_of_nodup`), and `sumParts` is permutation invariant
(`sumParts_perm`). -/
theorem sumParts_addParts_perm {ps qs : List MPPPart} (h : ps.Perm qs) :
    sumParts (addParts ps) = sumParts (addParts qs) := by
  have hperm : (addParts ps).Perm (addParts qs) :=
    (List.perm_ext_iff_of_nodup (nodup_addParts ps) (nodup_addParts qs)).mpr
      (fun a => by rw [mem_addParts, mem_addParts]; exact h.mem_iff)
  exact sumParts_perm hperm

end MPPProps

end LnLean.Payment
