import LnLean.Basic.Core
import LnLean.Channel.Fee
import LnLean.Channel.Commitment

/-!
# LnLean.Proofs.Channel.FeeProps

English claim.  This module isolates the arithmetic laws behind BOLT 3's
commitment fee:

* `feeForWeight r w` is the floored product `r.msatPerKw * w.val / 1000`;
  it is non-negative, bounded above by the product, monotone in both
  arguments, and strictly increases when the product grows by at least 1000.
* The model predicate `feeSufficient r w paid` is exactly the ordinary
  "paid fee is at least the required fee" comparison on `Msat` values.
* A `checkedFeeUpdate` applies `updateFee` only when the new rate's required
  fee is covered by the fee actually paid.  If the new rate is at least the
  old one, the old required fee is covered as well.
* The concrete commitment fee `commitmentFee r c` is definitionally the fee
  computed from `c.weight` and `r`.
* Deducting a fee from an output or from the local balance can change dust
  and reserve outcomes.  Lowering (or keeping) the fee preserves checks that
  already hold; raising it need not.  The module proves the monotone case and
  records an explicit counterexample for the non-monotone direction.
* Under the commitment conservation equation
  `totalOutputValue + feeSat = fundingValueSat`, the fee cannot exceed the
  funding value.

BOLT sections.
* BOLT 3 §4 `Fees`, `Fee Calculation` (`03-transactions.md:466-527`), in
  particular the base-fee rule at `:517-524`: start with weight 724 (1124
  with `option_anchors`), add 172 per untrimmed HTLC, multiply
  `feerate_per_kw` by the weight and divide by 1000 rounding down.
* BOLT 3 §4 `Fee Payment` (`03-transactions.md:558-580`): the base fee is
  extracted from the funder's amount.
* BOLT 3 §5 `Dust Limits` (`03-transactions.md:583-620`) and the trimming
  threshold at `:725-727`.
* BOLT 2 §3 `Updating Fees: update_fee`
  (`02-peer-protocol.md:3250-3310`): `update_fee` is a replacement, and the
  receiving node checks that the sender can afford the new fee rate on the
  current commitment transaction without violating the reserve.

rust-lightning anchors at `fe4900930c6bd5786ec4203274d7cf312776a5a6`.
* `lightning/src/ln/chan_utils.rs:275-288`
  (`COMMITMENT_TX_WEIGHT_PER_HTLC = 172`, base weights 724/1124).
* `lightning/src/ln/chan_utils.rs:289-298` (`commit_tx_fee_sat`: multiply
  the feerate by the base weight plus 172 per HTLC, divide by 1000).
* `lightning/src/ln/chan_utils.rs:1713-1740`
  (`CommitmentTransaction::new`, which stores `feerate_per_kw`).
* `lightning/src/ln/channel.rs:5916-5950` (`validate_update_fee`: subtract
  the holder-selected reserve and reject an unaffordable new feerate).
* `lightning/src/ln/channel.rs:6047-6120` (`can_send_update_fee`: the
  sender-side reserve and dust-exposure checks before proposing a feerate).

What is NOT modelled.
* `zero_fee_commitments`, the `shared_anchor` output, and anchor
  child-pays-for-parent fee bumping.
* The difference between the *required* base fee and the *actual* on-chain
  fee after trimmed outputs and below-dust funder outputs (BOLT 3
  `03-transactions.md:558-580`); `commitmentFee` is the required base fee.
* Fee estimation (BOLT 5), RBF, package relay, and mempool policy.
* The policy bound `max_dust_htlc_exposure_msat`, channel-type feature
  negotiation, and the race between an in-flight `update_fee` and new
  HTLCs.  The affordability check is represented by a predicate, not by
  message scheduling.
* Bitcoin Core's concrete `getdustthreshold`; the dust limit is the
  negotiated `dust_limit_satoshis` parameter.
-/

namespace LnLean.Channel

set_option autoImplicit false

open LnLean

/-! ## Floor fee: bounds and strict monotonicity -/

/-- The floored fee is below the exact product. -/
theorem feeForWeight_le_rate_mul_weight (r : FeeRate) (w : Weight) :
    (feeForWeight r w).val ≤ r.msatPerKw * w.val := by
  unfold feeForWeight
  exact Nat.div_le_self _ _

/-- The floored fee is the largest whole number of 1000-msat units that
does not exceed the exact product. -/
theorem feeForWeight_mul_1000_le (r : FeeRate) (w : Weight) :
    (feeForWeight r w).val * 1000 ≤ r.msatPerKw * w.val := by
  unfold feeForWeight
  exact Nat.div_mul_le_self _ _

/-- If the exact products differ by at least 1000 msat, the floored fees are
strictly ordered.  This is the quantitative form of "a higher feerate cannot
lower the fee": it also excludes the trivial floor collision. -/
theorem feeForWeight_strict_mono_rate {r₁ r₂ : FeeRate} (w : Weight)
    (h : r₁.msatPerKw * w.val + 1000 ≤ r₂.msatPerKw * w.val) :
    (feeForWeight r₁ w).val < (feeForWeight r₂ w).val := by
  unfold feeForWeight
  have hb : r₂.msatPerKw * w.val <
      ((r₂.msatPerKw * w.val) / 1000) * 1000 + 1000 := by
    have hmod := Nat.mod_lt (r₂.msatPerKw * w.val) (by decide : 0 < 1000)
    have hdiv := Nat.div_add_mod (r₂.msatPerKw * w.val) 1000
    omega
  have hlt : r₁.msatPerKw * w.val <
      ((r₂.msatPerKw * w.val) / 1000) * 1000 := by omega
  exact (Nat.div_lt_iff_lt_mul (by decide : 0 < 1000)).mpr hlt

/-! ## `feeSufficient` versus the `fee >= required` predicate -/

/-- The ordinary comparison "the paid fee is at least the required fee" on
`Msat` values.  `Msat` has no `LE` instance, so the comparison is on `val`. -/
def feeAtLeast (paid required : Msat) : Prop :=
  required.val ≤ paid.val

/-- `feeSufficient` is exactly the model's `fee >= required` predicate. -/
theorem feeSufficient_iff_feeAtLeast (r : FeeRate) (w : Weight) (paid : Msat) :
    feeSufficient r w paid ↔ feeAtLeast paid (feeForWeight r w) :=
  Iff.rfl

/-- The required fee is never negative, hence any non-negative paid amount
satisfies a zero required fee. -/
theorem feeSufficient_of_required_zero {r : FeeRate} {w : Weight} {paid : Msat}
    (h : (feeForWeight r w).val = 0) : feeSufficient r w paid := by
  unfold feeSufficient
  omega

/-! ## A checked `update_fee` -/

/-- Apply an `update_fee` only when the fee actually paid covers the fee
required by the new feerate and the commitment weight.  The check is the one
BOLT 2 §3 describes as the receiver's affordability check, specialised to
the fee component. -/
def checkedFeeUpdate (p : ChannelParams) (r : FeeRate) (w : Weight)
    (paid : Msat) : Option ChannelParams :=
  if (feeForWeight r w).val ≤ paid.val then some (updateFee p r) else none

/-- A successful checked update is exactly a passing sufficiency check plus
the parameter replacement. -/
theorem checkedFeeUpdate_some_iff {p p' : ChannelParams} {r : FeeRate}
    {w : Weight} {paid : Msat} :
    checkedFeeUpdate p r w paid = some p' ↔
      feeSufficient r w paid ∧ p' = updateFee p r := by
  unfold checkedFeeUpdate feeSufficient
  by_cases h : (feeForWeight r w).val ≤ paid.val <;> simp [h, eq_comm]

/-- A successful checked update installs the requested feerate. -/
theorem checkedFeeUpdate_rate {p p' : ChannelParams} {r : FeeRate}
    {w : Weight} {paid : Msat}
    (h : checkedFeeUpdate p r w paid = some p') : p'.feerate = r := by
  rcases (checkedFeeUpdate_some_iff.mp h) with ⟨_, rfl⟩
  rfl

/-- After a successful checked update, the paid fee still covers the fee
required at the installed rate.  This is the direct "never lowers the fee
below the required amount" statement. -/
theorem checkedFeeUpdate_sufficient {p p' : ChannelParams} {r : FeeRate}
    {w : Weight} {paid : Msat}
    (h : checkedFeeUpdate p r w paid = some p') :
    feeSufficient p'.feerate w paid := by
  rcases (checkedFeeUpdate_some_iff.mp h) with ⟨hpass, rfl⟩
  simpa [updateFee] using hpass

/-- If a checked update does not decrease the feerate, the paid fee also
covers the requirement of the *old* params.  Hence the update cannot lower
the paid fee below either the old or the new required amount. -/
theorem checkedFeeUpdate_old_rate {p p' : ChannelParams} {r : FeeRate}
    {w : Weight} {paid : Msat}
    (hrate : p.feerate.msatPerKw ≤ r.msatPerKw)
    (h : checkedFeeUpdate p r w paid = some p') :
    feeSufficient p.feerate w paid := by
  rcases (checkedFeeUpdate_some_iff.mp h) with ⟨hpass, rfl⟩
  exact feeSufficient_rate_mono hrate (by simpa [updateFee] using hpass)

/-- Numeric form of `checkedFeeUpdate_old_rate`: the old required fee is at
most the paid amount. -/
theorem checkedFeeUpdate_required_ge {p p' : ChannelParams} {r : FeeRate}
    {w : Weight} {paid : Msat}
    (hrate : p.feerate.msatPerKw ≤ r.msatPerKw)
    (h : checkedFeeUpdate p r w paid = some p') :
    (feeForWeight p.feerate w).val ≤ paid.val :=
  checkedFeeUpdate_old_rate hrate h

/-! ## The commitment fee is the fee of its weight and feerate -/

/-- The concrete commitment fee is definitionally `feeForWeight` at the
commitment's own weight. -/
theorem commitmentFee_eq_feeForWeight (r : FeeRate) (c : Commitment) :
    commitmentFee r c = feeForWeight r c.weight :=
  rfl

/-- Expanding `Commitment.weight`, the commitment fee is the BOLT 3 base
weight plus 172 per HTLC, multiplied by the feerate and floored. -/
theorem commitmentFee_eq_feeForWeight_weight (r : FeeRate) (c : Commitment) :
    commitmentFee r c =
      feeForWeight r (commitmentWeight c.anchorOutputs c.htlcs.length) :=
  rfl

/-- For a zero-HTLC commitment the fee reduces to the base weight only. -/
theorem commitmentFee_zeroHtlc (holder : Direction) (number funding toLocal
    fee contestDelay : Nat) (anchors : Bool) (r : FeeRate) :
    (commitmentFee r
      (zeroHtlcCommitment holder number funding toLocal fee contestDelay
        anchors)).val =
      r.msatPerKw * commitmentBaseWeight anchors / 1000 := by
  cases anchors <;>
    simp [commitmentFee, Commitment.weight, commitmentWeight,
      zeroHtlcCommitment, commitmentBaseWeight, commitmentHtlcWeight,
      feeForWeight]

/-! ## Dust after paying a fee -/

/-- An output value after a satoshi fee has been deducted.  Nat subtraction
truncates, but the theorems below carry the explicit `fee ≤ amount`
hypothesis where the distinction matters. -/
def outputAfterFee (amountSat feeSat : Nat) : Nat :=
  amountSat - feeSat

/-- Under `fee ≤ amount`, "the post-fee output is not dust" is exactly the
arithmetic inequality `dustLimit + fee ≤ amount`. -/
theorem not_isDust_outputAfterFee_iff {dustLimit amountSat feeSat : Nat}
    (h : feeSat ≤ amountSat) :
    ¬ isDust dustLimit (outputAfterFee amountSat feeSat) ↔
      dustLimit + feeSat ≤ amountSat := by
  unfold isDust outputAfterFee
  omega

/-- Lowering (or keeping) the fee preserves an output that was not dust. -/
theorem dustAfterFee_mono {dustLimit amountSat feeOld feeNew : Nat}
    (h : ¬ isDust dustLimit (outputAfterFee amountSat feeOld))
    (hle : feeNew ≤ feeOld) :
    ¬ isDust dustLimit (outputAfterFee amountSat feeNew) := by
  unfold isDust outputAfterFee at *
  omega

/-- Raising the fee can turn a non-dust output into dust.  This is precisely
why BOLT 3's dust check must be re-run for the new feerate. -/
theorem dust_not_preserved_by_fee_increase :
    ¬ isDust 100 (outputAfterFee 1000 0) ∧
      isDust 100 (outputAfterFee 1000 950) := by
  unfold isDust outputAfterFee
  decide

/-! ## Reserve after paying a fee -/

/-- The local balance still meets its reserve after a satoshi fee has been
deducted. -/
def reserveSatisfiedAfterFee (b : Balance) (reserveSat feeSat : Nat) : Prop :=
  reserveSat ≤ b.localSat - feeSat

/-- Under `fee ≤ localSat`, the post-fee reserve check is the arithmetic
inequality `reserve + fee ≤ localSat`. -/
theorem reserveSatisfiedAfterFee_iff {b : Balance} {reserveSat feeSat : Nat}
    (h : feeSat ≤ b.localSat) :
    reserveSatisfiedAfterFee b reserveSat feeSat ↔
      reserveSat + feeSat ≤ b.localSat :=
  Nat.le_sub_iff_add_le h

/-- Lowering (or keeping) the fee preserves a reserve that was met after the
old fee. -/
theorem reserveSatisfiedAfterFee_mono {b : Balance} {reserveSat feeOld
    feeNew : Nat}
    (h : reserveSatisfiedAfterFee b reserveSat feeOld)
    (hle : feeNew ≤ feeOld) :
    reserveSatisfiedAfterFee b reserveSat feeNew := by
  unfold reserveSatisfiedAfterFee at *
  omega

/-- Raising the fee can push the local balance below its reserve. -/
theorem reserve_not_preserved_by_fee_increase :
    reserveSatisfiedAfterFee ⟨Msat.ofSat 1000, Msat.zero⟩ 100 0 ∧
      ¬ reserveSatisfiedAfterFee ⟨Msat.ofSat 1000, Msat.zero⟩ 100 950 := by
  unfold reserveSatisfiedAfterFee Balance.localSat Msat.ofSat Msat.toSatFloor
    Msat.MSAT_PER_SAT Msat.zero
  decide

/-! ## Combining the dust and reserve checks -/

/-- Both post-fee checks hold for one output value and one local balance. -/
def feeUpdateChecksOk (b : Balance) (dustLimit amountSat reserveSat
    feeSat : Nat) : Prop :=
  ¬ isDust dustLimit (outputAfterFee amountSat feeSat) ∧
    reserveSatisfiedAfterFee b reserveSat feeSat

/-- Exact arithmetic characterisation of the combined checks, under the two
no-truncation hypotheses. -/
theorem feeUpdateChecksOk_iff {b : Balance} {dustLimit amountSat reserveSat
    feeSat : Nat} (hamount : feeSat ≤ amountSat) (hbal : feeSat ≤ b.localSat) :
    feeUpdateChecksOk b dustLimit amountSat reserveSat feeSat ↔
      dustLimit + feeSat ≤ amountSat ∧
        reserveSat + feeSat ≤ b.localSat := by
  unfold feeUpdateChecksOk
  rw [not_isDust_outputAfterFee_iff hamount, reserveSatisfiedAfterFee_iff hbal]

/-- A fee update that passes both checks and does not increase the fee keeps
passing both checks: dust and reserve outcomes are preserved in the
fee-decreasing direction. -/
theorem feeUpdateChecksOk_mono {b : Balance} {dustLimit amountSat reserveSat
    feeOld feeNew : Nat}
    (h : feeUpdateChecksOk b dustLimit amountSat reserveSat feeOld)
    (hle : feeNew ≤ feeOld) :
    feeUpdateChecksOk b dustLimit amountSat reserveSat feeNew :=
  ⟨dustAfterFee_mono h.1 hle, reserveSatisfiedAfterFee_mono h.2 hle⟩

/-! ## Fee versus funding value -/

/-- The commitment conservation equation of `docs/ARCHITECTURE.md` §4.3:
outputs plus the fee equal the funding value. -/
def CommitmentConserves (c : Commitment) : Prop :=
  c.totalOutputValue + c.feeSat = c.fundingValueSat

/-- The zero-HTLC construction of `LnLean.Channel.Commitment` satisfies
conservation whenever the fee, the holder output, and the anchors fit inside
the funding value. -/
theorem zeroHtlcCommitment_conserves (holder : Direction) (number funding
    toLocal fee contestDelay : Nat) (anchors : Bool)
    (h : fee + toLocal + (if anchors then 2 * anchorOutputSat else 0) ≤ funding) :
    CommitmentConserves
      (zeroHtlcCommitment holder number funding toLocal fee contestDelay anchors) := by
  cases anchors <;>
    simp [CommitmentConserves, Commitment.totalOutputValue,
      Commitment.htlcOutputValue, Commitment.anchorOutputValue, htlcOutputsValue,
      zeroHtlcCommitment, anchorOutputSat] at *
  · omega
  · omega

/-- Under conservation, the fee cannot exceed the funding value. -/
theorem fee_le_funding_of_conserves (c : Commitment)
    (h : CommitmentConserves c) : c.feeSat ≤ c.fundingValueSat := by
  unfold CommitmentConserves at h
  omega

/-- If the fee actually recorded on the commitment covers the required fee,
then the required fee is bounded by the funding value as well. -/
theorem commitmentFee_le_funding_of_conserves (r : FeeRate) (c : Commitment)
    (hcons : CommitmentConserves c)
    (hpaid : (commitmentFee r c).val ≤ c.feeSat) :
    (commitmentFee r c).val ≤ c.fundingValueSat :=
  Nat.le_trans hpaid (fee_le_funding_of_conserves c hcons)

/-- Well-formedness for this module: conservation plus the requirement that
the fee field is exactly the feerate-derived commitment fee. -/
def CommitmentFeeWellFormed (r : FeeRate) (c : Commitment) : Prop :=
  CommitmentConserves c ∧ c.feeSat = (commitmentFee r c).val

/-- Under well-formedness the required commitment fee is at most the funding
value. -/
theorem commitmentFee_le_funding_of_wellFormed (r : FeeRate) (c : Commitment)
    (h : CommitmentFeeWellFormed r c) :
    (commitmentFee r c).val ≤ c.fundingValueSat := by
  rcases h with ⟨hcons, hfee⟩
  have hle := fee_le_funding_of_conserves c hcons
  omega

end LnLean.Channel
