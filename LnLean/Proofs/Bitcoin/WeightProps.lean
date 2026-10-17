import LnLean.Bitcoin.Laws
import LnLean.Bitcoin.Seam
import LnLean.Basic.Core

/-!
# LnLean.Proofs.Bitcoin.WeightProps

English claim.  The BOLT 3 expected commitment-transaction weight is
`724 + 172 * k` without `option_anchors` and `1124 + 172 * k` with it, where
`k` is the number of HTLC outputs that survive dust trimming.  The weight is
therefore strictly increasing in `k`, adding one untrimmed HTLC never lowers
it, and both constants are positive.  The fee for that weight is the model's
ceiling fee `(feerate_per_kw * weight + 999) / 1000` millisatoshis, which is
monotone in both the feerate and the weight, and dominates the BOLT 3
round-down fee.  The fee in satoshis is bounded by the funding value only
under an explicit *fee-budget* hypothesis; a well-formed funding value alone
does not imply it (a high feerate makes the fee arbitrarily large), and a
concrete counterexample is proved below.

This module also checks the Appendix A byte decomposition of the same
constants: `4 * (non-witness bytes) + 224` witness weight, with 125
non-witness bytes without anchors and 225 with anchors, plus 43 non-witness
bytes per HTLC output.

BOLT sections.
* BOLT 3 §4 "Fees" (`refs/bolts/03-transactions.md:464-556` at BOLT commit
  `1aadb719b4007c4cea0ba6e36b08c4fb53788dee`): expected-weight table at
  `:491-498`, base-fee algorithm at `:517-524` ("Start with `weight` = 724
  (1124 if `option_anchors` applies) ... add 172 ... multiply
  `feerate_per_kw` by `weight`, divide by 1000, rounding down"), worked
  example at `:526-556` (`weight` 1068 and fee 5340 satoshis).
* BOLT 3 Appendix A "Expected Weight of the Commitment Transaction"
  (`:973-1086`): `500 + 172 * num-htlc-outputs` non-witness weight without
  anchors (`900 + ...` with anchors) plus 224 witness weight, and
  `tx_out: 172 + 43 * num-htlc-outputs` bytes.

rust-lightning anchors at `fe4900930c6bd5786ec4203274d7cf312776a5a6`.
* `lightning/src/ln/chan_utils.rs:274-277`
  (`COMMITMENT_TX_WEIGHT_PER_HTLC: u64 = 172`).
* `lightning/src/ln/chan_utils.rs:279-284` (`commitment_tx_base_weight`,
  `COMMITMENT_TX_BASE_WEIGHT = 724`,
  `COMMITMENT_TX_BASE_ANCHOR_WEIGHT = 1124`).
* `lightning/src/ln/chan_utils.rs:286-294` (`commit_tx_fee_sat`: multiply
  the feerate by the weight and divide by 1000, floor).

What is explicitly NOT modelled.
* Transaction serialization.  `Bitcoin.Data.Tx` has no weight function, so
  the byte decomposition below is arithmetic on BOLT 3's stated byte counts,
  not a proof about a serialized `Tx`.  Actual weight may differ from the
  expected weight (signature-length and CompactSize effects); BOLT 3 uses
  the expected weight as the fee basis.
* Dust trimming decisions.  `k` is the number of *untrimmed* outputs; this
  module does not compute which HTLCs are trimmed (that needs the dust-limit
  and second-stage-fee model in `LnLean.Channel.Fee` / BOLT 3 §5).
* HTLC-timeout/HTLC-success weights (663/703, 666/706 with anchors) and
  `zero_fee_commitments` / `shared_anchor`.
* The channel layer: `LnLean.Channel.Commitment.commitmentWeight` is not
  imported here because this module's wave-A import set is restricted to
  `LnLean.Bitcoin.Laws`, `LnLean.Bitcoin.Seam`, and `LnLean.Basic.Core`.  The
  local `commitmentWeight` uses the same argument order and formula; a
  checked cross-module equality is left to the channel proof modules
  (recorded in `agents/reports/B04.md`).
* BOLT 2's funding-balance / `update_fee` affordability checks.  The
  fee-budget hypothesis below is taken as an explicit premise, not derived
  from well-formedness of the funding output.
-/

namespace LnLean.Proofs.Bitcoin

set_option autoImplicit false

open LnLean

/-! ## BOLT 3 weight constants -/

/-- Expected commitment base weight: 724 without anchors, 1124 with
`option_anchors` (BOLT 3 `03-transactions.md:493-494,521`; LDK
`chan_utils.rs:281-283`). -/
def baseWeight (anchors : Bool) : Nat :=
  if anchors then 1124 else 724

/-- Weight added by one untrimmed HTLC output: 172 (BOLT 3
`03-transactions.md:522-523`; LDK `chan_utils.rs:275`). -/
def htlcWeight : Nat := 172

/-- Expected commitment weight as a function of the number of untrimmed HTLC
outputs.  Same formula and argument order as
`LnLean.Channel.Commitment.commitmentWeight`. -/
def commitmentWeight (anchors : Bool) (numHtlcs : Nat) : Weight :=
  ⟨baseWeight anchors + htlcWeight * numHtlcs⟩

/-- Non-witness serialized size used by BOLT 3 Appendix A: 125 bytes without
anchors, 225 bytes with anchors (before HTLC outputs). -/
def nonWitnessBytes (anchors : Bool) : Nat :=
  if anchors then 225 else 125

/-- Witness weight used by BOLT 3 Appendix A: 224 weight units. -/
def witnessWeight : Nat := 224

/-- Non-witness bytes added per untrimmed HTLC output (BOLT 3 Appendix A,
`tx_out: 172 + 43 * num-htlc-outputs` bytes). -/
def htlcNonWitnessBytes : Nat := 43

/-- The Appendix A construction reconstructed from bytes: four weight units
per non-witness byte plus the witness weight. -/
def weightFromBytes (anchors : Bool) (numHtlcs : Nat) : Nat :=
  4 * (nonWitnessBytes anchors + htlcNonWitnessBytes * numHtlcs) + witnessWeight

/-! ## Constants agree with the L1 seam -/

/-- `baseWeight false` is the 724 constant exported by
`LnLean.Bitcoin.commitmentBaseWeight`. -/
theorem baseWeight_noAnchors :
    baseWeight false = LnLean.Bitcoin.commitmentBaseWeight.val := rfl

/-- `baseWeight true` is the BOLT 3 anchor variant, 1124. -/
theorem baseWeight_anchors : baseWeight true = 1124 := rfl

/-- The per-HTLC increment is exactly the seam's `htlcOfferedWeight`. -/
theorem htlcWeight_eq_offered :
    htlcWeight = LnLean.Bitcoin.htlcOfferedWeight.val := rfl

/-- The per-HTLC increment is exactly the seam's `htlcReceivedWeight`. -/
theorem htlcWeight_eq_received :
    htlcWeight = LnLean.Bitcoin.htlcReceivedWeight.val := rfl

/-- The offered and received HTLC increments are the same constant; BOLT 3
charges 172 for either output kind. -/
theorem htlcOffered_eq_htlcReceived :
    LnLean.Bitcoin.htlcOfferedWeight = LnLean.Bitcoin.htlcReceivedWeight := rfl

/-! ## The weight formula -/

/-- Unfolding law for the weight. -/
theorem commitmentWeight_val (anchors : Bool) (numHtlcs : Nat) :
    (commitmentWeight anchors numHtlcs).val =
      baseWeight anchors + htlcWeight * numHtlcs := rfl

/-- The closed BOLT 3 form: base plus 172 per untrimmed HTLC. -/
theorem commitmentWeight_bolt3_formula (anchors : Bool) (numHtlcs : Nat) :
    (commitmentWeight anchors numHtlcs).val =
      (if anchors then 1124 else 724) + 172 * numHtlcs := rfl

/-- A commitment with no untrimmed HTLCs has exactly the base weight. -/
theorem commitmentWeight_zero (anchors : Bool) :
    commitmentWeight anchors 0 = ⟨baseWeight anchors⟩ := by
  simp [commitmentWeight]

/-- Each additional untrimmed HTLC adds exactly 172 weight units. -/
theorem commitmentWeight_succ (anchors : Bool) (numHtlcs : Nat) :
    (commitmentWeight anchors (numHtlcs + 1)).val =
      (commitmentWeight anchors numHtlcs).val + htlcWeight := by
  simp [commitmentWeight, Nat.mul_succ]
  omega

/-- Weight is monotone in the number of untrimmed HTLCs. -/
theorem commitmentWeight_mono (anchors : Bool) {n m : Nat} (h : n ≤ m) :
    (commitmentWeight anchors n).val ≤ (commitmentWeight anchors m).val := by
  show baseWeight anchors + htlcWeight * n ≤ baseWeight anchors + htlcWeight * m
  exact Nat.add_le_add_left (Nat.mul_le_mul_left htlcWeight h) _

/-- Weight is strictly increasing in the number of untrimmed HTLCs. -/
theorem commitmentWeight_strictMono (anchors : Bool) {n m : Nat} (h : n < m) :
    (commitmentWeight anchors n).val < (commitmentWeight anchors m).val := by
  show baseWeight anchors + htlcWeight * n < baseWeight anchors + htlcWeight * m
  exact Nat.add_lt_add_left
    (Nat.mul_lt_mul_of_pos_left h (by decide : 0 < htlcWeight)) _

/-- Adding an HTLC never decreases the commitment weight. -/
theorem commitmentWeight_add_htlc_ge (anchors : Bool) (numHtlcs : Nat) :
    (commitmentWeight anchors numHtlcs).val ≤
      (commitmentWeight anchors (numHtlcs + 1)).val :=
  commitmentWeight_mono anchors (Nat.le_succ numHtlcs)

/-- Both variants have strictly positive weight, even with zero HTLCs. -/
theorem commitmentWeight_pos (anchors : Bool) (numHtlcs : Nat) :
    0 < (commitmentWeight anchors numHtlcs).val := by
  unfold commitmentWeight baseWeight htlcWeight
  cases anchors <;> simp <;> omega

/-- Turning on `option_anchors` adds exactly 400 weight units: two 330-sat
anchor outputs at 4 weight units per byte plus the `to_local`/`to_remote`
script difference, as fixed by BOLT 3's 1124 versus 724 constants. -/
theorem commitmentWeight_anchor_delta (numHtlcs : Nat) :
    (commitmentWeight true numHtlcs).val =
      (commitmentWeight false numHtlcs).val + 400 := by
  simp [commitmentWeight, baseWeight]
  omega

/-- The two BOLT 3 worked-example weights agree: two untrimmed HTLCs give
1068 without anchors and 1468 with anchors (`03-transactions.md:535-549`). -/
theorem commitmentWeight_two_htlcs :
    (commitmentWeight false 2).val = 1068 ∧
      (commitmentWeight true 2).val = 1468 := by
  decide

/-! ## Appendix A byte decomposition -/

/-- The Appendix A byte construction yields exactly the BOLT 3 base weight:
`4 * 125 + 224 = 724` and `4 * 225 + 224 = 1124`. -/
theorem weightFromBytes_eq_commitmentWeight (anchors : Bool) (numHtlcs : Nat) :
    (commitmentWeight anchors numHtlcs).val =
      weightFromBytes anchors numHtlcs := by
  unfold commitmentWeight baseWeight htlcWeight weightFromBytes nonWitnessBytes
    htlcNonWitnessBytes witnessWeight
  cases anchors <;> simp <;> omega

/-! ## Trimming-aware weight -/

/-- Weight computed from a list of HTLC outputs tagged with whether they
survive trimming (`true` = untrimmed).  Trimmed outputs contribute neither an
output nor weight, matching BOLT 3 `:522-523`. -/
def weightOfFlags (anchors : Bool) (flags : List Bool) : Weight :=
  ⟨baseWeight anchors + htlcWeight * flags.count true⟩

/-- The flag-based weight is the closed-form weight at the untrimmed count. -/
theorem weightOfFlags_val (anchors : Bool) (flags : List Bool) :
    (weightOfFlags anchors flags).val =
      (commitmentWeight anchors (flags.count true)).val := rfl

/-- An empty output list gives the base weight. -/
theorem weightOfFlags_nil (anchors : Bool) :
    weightOfFlags anchors [] = ⟨baseWeight anchors⟩ := by
  simp [weightOfFlags]

/-- Adding an untrimmed HTLC output adds 172 to the flag-based weight. -/
theorem weightOfFlags_cons_untrimmed (anchors : Bool) (flags : List Bool) :
    (weightOfFlags anchors (true :: flags)).val =
      (weightOfFlags anchors flags).val + htlcWeight := by
  simp [weightOfFlags, Nat.mul_succ, Nat.add_comm, Nat.add_assoc]

/-- Adding a trimmed HTLC output does not change the weight. -/
theorem weightOfFlags_cons_trimmed (anchors : Bool) (flags : List Bool) :
    weightOfFlags anchors (false :: flags) = weightOfFlags anchors flags := by
  simp [weightOfFlags]

/-! ## Fees -/

/-- The model's ceiling fee (`LnLean.FeeRate.fee` in `Basic.Core`).  The
mission's phrase "ceil(feerate * weight / 1000)" refers to this function. -/
def commitmentFee (r : FeeRate) (w : Weight) : Msat :=
  FeeRate.fee r w

/-- BOLT 3's round-down fee, restated locally so the two rounding conventions
can be compared without importing `LnLean.Channel.Fee`. -/
def floorFee (r : FeeRate) (w : Weight) : Msat :=
  ⟨r.msatPerKw * w.val / 1000⟩

/-- The commitment fee in satoshis, rounded up (fees are paid in whole
satoshis from a `to_local`/`to_remote` output). -/
def commitmentFeeSat (r : FeeRate) (w : Weight) : Nat :=
  (commitmentFee r w).toSatCeil

/-- The commitment fee in satoshis, rounded down; the conservative quantity
used for the funding bound below. -/
def commitmentFeeSatFloor (r : FeeRate) (w : Weight) : Nat :=
  (commitmentFee r w).val / 1000

/-- Unfolding law for the ceiling fee. -/
theorem commitmentFee_val (r : FeeRate) (w : Weight) :
    (commitmentFee r w).val = (r.msatPerKw * w.val + 999) / 1000 := rfl

/-- The ceiling fee is `ceilDiv` of the feerate-weight product. -/
theorem commitmentFee_eq_ceilDiv (r : FeeRate) (w : Weight) :
    (commitmentFee r w).val = ceilDiv (r.msatPerKw * w.val) 1000 := by
  simp [commitmentFee, FeeRate.fee, ceilDiv]

/-- The fee is non-negative. -/
theorem commitmentFee_nonneg (r : FeeRate) (w : Weight) :
    0 ≤ (commitmentFee r w).val :=
  Nat.zero_le _

/-- The fee is monotone in the feerate. -/
theorem commitmentFee_mono_rate {r₁ r₂ : FeeRate}
    (h : r₁.msatPerKw ≤ r₂.msatPerKw) (w : Weight) :
    (commitmentFee r₁ w).val ≤ (commitmentFee r₂ w).val := by
  unfold commitmentFee FeeRate.fee
  exact Nat.div_le_div_right
    (Nat.add_le_add_right (Nat.mul_le_mul_right w.val h) 999)

/-- The fee is monotone in the weight. -/
theorem commitmentFee_mono_weight (r : FeeRate) {w₁ w₂ : Weight}
    (h : w₁.val ≤ w₂.val) :
    (commitmentFee r w₁).val ≤ (commitmentFee r w₂).val := by
  unfold commitmentFee FeeRate.fee
  exact Nat.div_le_div_right
    (Nat.add_le_add_right (Nat.mul_le_mul_left r.msatPerKw h) 999)

/-- The fee is monotone in both arguments simultaneously. -/
theorem commitmentFee_mono {r₁ r₂ : FeeRate} {w₁ w₂ : Weight}
    (hr : r₁.msatPerKw ≤ r₂.msatPerKw) (hw : w₁.val ≤ w₂.val) :
    (commitmentFee r₁ w₁).val ≤ (commitmentFee r₂ w₂).val :=
  Nat.le_trans (commitmentFee_mono_rate hr w₁)
    (commitmentFee_mono_weight r₂ hw)

/-- The fee never decreases when untrimmed HTLCs are added: this combines
weight monotonicity with fee monotonicity in the weight. -/
theorem commitmentFee_mono_htlcs (r : FeeRate) (anchors : Bool) {n m : Nat}
    (h : n ≤ m) :
    (commitmentFee r (commitmentWeight anchors n)).val ≤
      (commitmentFee r (commitmentWeight anchors m)).val :=
  commitmentFee_mono_weight r (commitmentWeight_mono anchors h)

/-- A zero-weight transaction pays no fee. -/
theorem commitmentFee_zero_weight (r : FeeRate) :
    commitmentFee r ⟨0⟩ = Msat.zero := by
  simp [commitmentFee, FeeRate.fee, Msat.zero]

/-- BOLT 3's round-down fee is never larger than the model's ceiling fee. -/
theorem floorFee_le_commitmentFee (r : FeeRate) (w : Weight) :
    (floorFee r w).val ≤ (commitmentFee r w).val := by
  unfold floorFee commitmentFee FeeRate.fee
  exact Nat.div_le_div_right (Nat.le_add_right _ 999)

/-- The BOLT 3 worked example at feerate 5000 sat/kw (5_000_000 msat/kw) and
a 2-HTLC commitment of weight 1068 requires 5_340_000 msat, i.e. 5340
satoshis (`03-transactions.md:553`). -/
theorem bolt3_example_fee :
    (commitmentFee ⟨5000000⟩ (commitmentWeight false 2)).val = 5340000 ∧
      (commitmentFee ⟨5000000⟩ (commitmentWeight false 2)).toSatFloor = 5340 := by
  decide

/-! ## Fee affordability is conditional -/

/-- Fee budget in millisatoshis: the feerate-weight product plus the rounding
term fits into `fundingSat * 10^6` msat.  This is the explicit well-formedness
hypothesis under which the fee cannot exceed the funding value. -/
def FeeBudget (r : FeeRate) (w : Weight) (fundingSat : Nat) : Prop :=
  r.msatPerKw * w.val + 999 ≤ fundingSat * 1000000

/-- Under a `FeeBudget`, the ceiling fee in millisatoshis does not exceed the
funding value in millisatoshis. -/
theorem commitmentFee_le_funding_msat (r : FeeRate) (w : Weight)
    (fundingSat : Nat) (h : FeeBudget r w fundingSat) :
    (commitmentFee r w).val ≤ fundingSat * 1000 := by
  unfold commitmentFee FeeRate.fee
  rw [Nat.div_le_iff_le_mul_add_pred (by decide : 0 < 1000)]
  unfold FeeBudget at h
  omega

/-- Under a `FeeBudget`, the fee rounded down to satoshis does not exceed the
funding value in satoshis.  This is the precise form of "the commitment fee
cannot exceed the funding value" that the current model supports. -/
theorem commitmentFeeSatFloor_le_funding (r : FeeRate) (w : Weight)
    (fundingSat : Nat) (h : FeeBudget r w fundingSat) :
    commitmentFeeSatFloor r w ≤ fundingSat := by
  unfold commitmentFeeSatFloor
  have hfee := commitmentFee_le_funding_msat r w fundingSat h
  calc
    (commitmentFee r w).val / 1000 ≤ (fundingSat * 1000) / 1000 :=
      Nat.div_le_div_right hfee
    _ = fundingSat := by
      rw [Nat.mul_comm fundingSat 1000]
      exact Nat.mul_div_right fundingSat (by decide : 0 < 1000)

/-- Under a `FeeBudget`, the fee rounded up to satoshis also does not exceed
the funding value, because `ceil(ceil(a/1000)/1000) = ceil(a/10^6)` stays
below the same bound. -/
theorem commitmentFeeSat_le_funding (r : FeeRate) (w : Weight)
    (fundingSat : Nat) (h : FeeBudget r w fundingSat) :
    commitmentFeeSat r w ≤ fundingSat := by
  unfold commitmentFeeSat Msat.toSatCeil Msat.MSAT_PER_SAT
  have hsub : (commitmentFee r w).val + 1000 - 1 = (commitmentFee r w).val + 999 := by
    omega
  rw [hsub]
  rw [Nat.div_le_iff_le_mul_add_pred (by decide : 0 < 1000)]
  have hfee := commitmentFee_le_funding_msat r w fundingSat h
  omega

/-- Well-formedness of the funding value alone does not bound the fee: a
funding output of 1000 satoshis is inside `MoneyRange` (and so
`FundingParams.WellFormed` allows it), while the 724-weight fee at
`feerate_per_kw = 10^9` msat/kw is 724_000 satoshis.  Hence the fee bound
needs `FeeBudget`, not just a well-formed `FundingParams`. -/
theorem fee_not_bounded_by_funding_wellformedness :
    ∃ (r : FeeRate) (w : Weight) (fundingSat : Nat),
      0 ≤ fundingSat ∧ fundingSat ≤ 21000000 * 100000000 ∧
        commitmentFeeSatFloor r w > fundingSat := by
  refine ⟨⟨1000000000⟩, commitmentWeight false 0, 1000, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide

end LnLean.Proofs.Bitcoin
