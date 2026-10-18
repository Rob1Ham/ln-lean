import LnLean.Channel.Commitment
import LnLean.Channel.Fee
import LnLean.Channel.HTLC
import LnLean.Proofs.WaveD.D12

/-!
# Commitment integration targets: second-stage fee, dust trimming, and the legacy view

Open issues `CH-01` and `CH-02` record two gaps between the rich commitment
model (`CommitmentTx` in `LnLean.Channel.Commitment`) and the legacy consumers
of `Commitment.commitmentOutputs`:

* `CH-01`: the rich model is not the legacy consumer path.  The legacy output
  function emits a fixed group order and applies no BOLT 3 dust filter, so D12
  refutes the unconditional ordering/trimming reading
  (`LnLean.Proofs.WaveD.D12.waveD_d12_output_ordering_fails`).
* `CH-02`: the second-stage (HTLC-timeout / HTLC-success) fee is only a pair of
  ambient `Nat` parameters.  Nothing computes it from the feerate, and the
  legacy output list has no place to record the fee that a net HTLC output
  withholds.

This module is additive.  It does not touch `LnLean.Channel.Commitment` and it
keeps every D12 refutation visible.  It supplies:

1. the BOLT 3 second-stage fee as a function of the negotiated feerate and
   `option_anchors` (`htlcTimeoutFeeSat`, `htlcSuccessFeeSat`,
   `secondStageFeeAt`), plus the per-output fee view
   (`htlcFeeOf`, `secondStageFeeTotal`, `grossHtlcValue`);
2. the net/gross record projections (`legacyHtlcOutput`, `netHtlcOutput`) and
   the exact relation between the model's net HTLC output value and the BOLT 3
   trimming threshold `dust_limit + second_stage_fee`;
3. a legacy output view of the rich model, `legacyOutputs tx =
   tx.outputs.map CommitmentTxOutput.toCommitmentOutput`, with

   * `legacyOutputs_perm_commitmentOutputs`: under a zero dust limit and
     non-zero `to_local`/`to_remote`, the sorted rich output list projects to a
     **permutation** of `tx.commitment.commitmentOutputs` (the strongest true
     relation, since the rich list is sorted and the legacy list is not);
   * `legacyOutputs_values_sorted`: the legacy projection of the sorted rich
     list is value-sorted (ordering preservation);
   * `legacyOutputs_sum_add_trimmedValue`: the projected sum plus the value
     removed by BOLT 3 trimming is exactly `totalOutputValue` (trimming
     preservation), and at dust limit zero the sum is exactly
     `totalOutputValue` with no extra hypotheses;
   * `dust_trimming_not_perm`: the zero-dust and non-zero-output hypotheses are
     necessary; a below-dust HTLC changes the output set;
4. two explicit BOLT 3 constructions from `HTLCRecord`s,
   `legacyCommitmentOfRecords` and `bolt3CommitmentOfRecords`, with exact
   conservation theorems.  The BOLT 3 construction proves that the effective
   fee is `base fee + withheld second-stage fees + trimmed gross value`, which
   is precisely the accounting that the current `Commitment` record cannot
   express (it has no gross amount and no effective-fee field);
5. `bolt3CommitmentOfRecords_conservation` and
   `richOutputs_refine_legacyCommitment`, the end-to-end conditional
   refinement from a rich `CommitmentTx` to the legacy commitment outputs at
   zero dust, zero second-stage fees, and the BOLT 3 balance equation.

BOLT anchors.
* BOLT 3 §Trimmed Outputs (`refs/bolts/03-transactions.md:305-354`): the
  HTLC output is omitted when `amount - htlc_fee < dust_limit_satoshis`;
  equality is kept; the trimmed value is added to the fee.
* BOLT 3 §Fee Calculation (`refs/bolts/03-transactions.md:464-535`): the
  HTLC-timeout weight is 663 and the HTLC-success weight is 703 without
  anchors; with `option_anchors` both HTLC transactions have fee zero.
* BOLT 3 §Offered HTLC Outputs / §Received HTLC Outputs
  (`refs/bolts/03-transactions.md:199-304`): a surviving HTLC output is a
  second-stage output whose value is the protocol amount net of the
  direction-dependent second-stage fee.
* rust-lightning `lightning/src/ln/chan_utils.rs:919-941`
  (`build_htlc_output` subtracts the second-stage fee) and `:1958-1975`
  (`build_htlc_outputs` uses `to_bitcoin_amount` for the commitment output).
  The two conventions differ by exactly the withheld second-stage fee; this
  module makes the difference explicit instead of hiding it.

What is NOT modelled (scope caveats).
* Script execution, signature checking, witnesses, sighash, and the actual
  BOLT 3 script templates.  Only output values, kinds, CLTV keys, and the
  script bytes already carried by `CommitmentTx` are used.
* `option_anchors` second-stage fees are modelled as zero, as BOLT 3
  prescribes.  Anchor *presence* remains the existing
  "both anchors iff `anchorOutputs`" convention; the single-anchor exception
  is out of scope (as in `CommitmentTx.outputs_spec`).
* `zero_fee_commitments` (BOLT 3 `shared_anchor`), fee bumping, and the
  CPFP economics of anchors.
* `CommitmentHTLCOutput.amountSat` is taken to be the net value, i.e. the
  value the model emits.  `grossHtlcValue` recovers the pre-fee amount by
  adding the withheld fee back.  A BOLT-3-exact commitment output value (gross
  amount on the commitment, fee paid by the second-stage transaction) would
  require a new `Commitment` field; §6 of the lane report records the exact
  patch.  No claim is made that the current net-value convention is
  consensus-faithful.
* The refinement is a `List.Perm`, not equality: the rich model sorts and the
  legacy function does not.  D12's counterexample is retained and restated
  here as `legacy_ordering_refuted`.
-/

namespace LnLean.Proofs.Channel.CommitmentIntegration

set_option autoImplicit false

open LnLean
open LnLean.Channel

/-! ## 1. The BOLT 3 second-stage fee -/

/-- BOLT 3 §4 expected weight of an HTLC-timeout transaction without anchors. -/
def htlcTimeoutWeight : Weight := ⟨663⟩

/-- BOLT 3 §4 expected weight of an HTLC-success transaction without anchors. -/
def htlcSuccessWeight : Weight := ⟨703⟩

theorem htlcTimeoutWeight_val : htlcTimeoutWeight.val = 663 := rfl

theorem htlcSuccessWeight_val : htlcSuccessWeight.val = 703 := rfl

/-- BOLT 3 HTLC-timeout fee in satoshis: `feerate_per_kw * 663 / 1000`,
rounded down, and **zero** when `option_anchors` is negotiated. -/
def htlcTimeoutFeeSat (anchors : Bool) (r : FeeRate) : Nat :=
  if anchors then 0 else (feeForWeight r htlcTimeoutWeight).val

/-- BOLT 3 HTLC-success fee in satoshis: `feerate_per_kw * 703 / 1000`,
rounded down, and **zero** when `option_anchors` is negotiated. -/
def htlcSuccessFeeSat (anchors : Bool) (r : FeeRate) : Nat :=
  if anchors then 0 else (feeForWeight r htlcSuccessWeight).val

theorem htlcTimeoutFeeSat_value (r : FeeRate) :
    htlcTimeoutFeeSat false r = r.msatPerKw * 663 / 1000 := rfl

theorem htlcSuccessFeeSat_value (r : FeeRate) :
    htlcSuccessFeeSat false r = r.msatPerKw * 703 / 1000 := rfl

theorem htlcTimeoutFeeSat_anchors (r : FeeRate) :
    htlcTimeoutFeeSat true r = 0 := rfl

theorem htlcSuccessFeeSat_anchors (r : FeeRate) :
    htlcSuccessFeeSat true r = 0 := rfl

/-- The direction-indexed second-stage fee at the negotiated feerate.  From
our point of view an offered HTLC (`Direction.local`) is an HTLC-timeout
transaction and a received HTLC (`Direction.remote`) is an HTLC-success
transaction. -/
def secondStageFeeAt (anchors : Bool) (r : FeeRate) (dir : Direction) : Nat :=
  secondStageFee dir (htlcTimeoutFeeSat anchors r) (htlcSuccessFeeSat anchors r)

theorem secondStageFeeAt_local (anchors : Bool) (r : FeeRate) :
    secondStageFeeAt anchors r .local = htlcTimeoutFeeSat anchors r := rfl

theorem secondStageFeeAt_remote (anchors : Bool) (r : FeeRate) :
    secondStageFeeAt anchors r .remote = htlcSuccessFeeSat anchors r := rfl

/-- With `option_anchors`, BOLT 3's second-stage transactions pay no fee, so
the withheld second-stage fee is zero for both directions. -/
theorem secondStageFeeAt_anchors (r : FeeRate) (dir : Direction) :
    secondStageFeeAt true r dir = 0 := by
  cases dir <;> rfl

/-- Without anchors the second-stage fee is exactly the BOLT 3 floor-divided
fee for the direction's transaction. -/
theorem secondStageFeeAt_noAnchors (r : FeeRate) (dir : Direction) :
    secondStageFeeAt false r dir =
      (if dir = .local then r.msatPerKw * 663 / 1000
        else r.msatPerKw * 703 / 1000) := by
  cases dir <;> rfl

/-! ## 2. Per-output second-stage fee view -/

/-- The second-stage fee withheld from one commitment HTLC output.  The fee
depends only on the output's direction, not on its amount. -/
def htlcFeeOf (timeoutFeeSat successFeeSat : Nat) (h : CommitmentHTLCOutput) : Nat :=
  secondStageFee h.direction timeoutFeeSat successFeeSat

theorem htlcFeeOf_local (t s : Nat) (h : CommitmentHTLCOutput) (hd : h.direction = .local) :
    htlcFeeOf t s h = t := by
  simp [htlcFeeOf, hd, secondStageFee]

theorem htlcFeeOf_remote (t s : Nat) (h : CommitmentHTLCOutput) (hd : h.direction = .remote) :
    htlcFeeOf t s h = s := by
  simp [htlcFeeOf, hd, secondStageFee]

/-- Total second-stage fee withheld from a list of HTLC outputs. -/
def secondStageFeeTotal (timeoutFeeSat successFeeSat : Nat)
    (hs : List CommitmentHTLCOutput) : Nat :=
  (hs.map (htlcFeeOf timeoutFeeSat successFeeSat)).sum

theorem secondStageFeeTotal_nil (t s : Nat) :
    secondStageFeeTotal t s [] = 0 := rfl

theorem secondStageFeeTotal_cons (t s : Nat) (h : CommitmentHTLCOutput)
    (hs : List CommitmentHTLCOutput) :
    secondStageFeeTotal t s (h :: hs) =
      htlcFeeOf t s h + secondStageFeeTotal t s hs := rfl

theorem secondStageFeeTotal_append (t s : Nat) (xs ys : List CommitmentHTLCOutput) :
    secondStageFeeTotal t s (xs ++ ys) =
      secondStageFeeTotal t s xs + secondStageFeeTotal t s ys := by
  induction xs with
  | nil => simp [secondStageFeeTotal]
  | cons h tl _ =>
      simp [secondStageFeeTotal, Nat.add_assoc]

/-- The gross (pre-second-stage-fee) value of a commitment HTLC output.  This
is the value BOLT 3 denominates the HTLC output in; `htlcFeeOf` is withheld
from it. -/
def grossHtlcValue (timeoutFeeSat successFeeSat : Nat)
    (h : CommitmentHTLCOutput) : Nat :=
  h.amountSat + htlcFeeOf timeoutFeeSat successFeeSat h

theorem grossHtlcValue_eq (t s : Nat) (h : CommitmentHTLCOutput) :
    grossHtlcValue t s h = h.amountSat + htlcFeeOf t s h := rfl

/-- If the net HTLC value plus its withheld fee is the gross amount, then the
gross value definition is the original amount. -/
theorem grossHtlcValue_eq_of_net_add_fee {g : Nat} (t s : Nat)
    (h : CommitmentHTLCOutput) (hgross : h.amountSat + htlcFeeOf t s h = g) :
    grossHtlcValue t s h = g := hgross

/-- The total gross HTLC amount of a record list. -/
def grossTotal (hs : List HTLCRecord) : Nat :=
  (hs.map (fun h => Msat.toSatFloor h.amountMsat)).sum

/-! ## 3. Net and legacy projections of an HTLC record -/

/-- The legacy projection: the whole-satoshi amount, with no second-stage fee
deducted.  This is the convention a legacy consumer uses when it builds
`Commitment.htlcs` directly from `HTLCRecord.amountMsat`. -/
def legacyHtlcOutput (h : HTLCRecord) : CommitmentHTLCOutput :=
  { direction := h.direction
    amountSat := Msat.toSatFloor h.amountMsat
    cltvExpiry := h.cltvExpiry
    state := h.state }

/-- The rich (net) projection: the amount minus the direction-dependent
second-stage fee, exactly the value that `CommitmentTx.htlcOutput` emits when
the output survives trimming. -/
def netHtlcOutput (timeoutFeeSat successFeeSat : Nat) (h : HTLCRecord) :
    CommitmentHTLCOutput :=
  { direction := h.direction
    amountSat := htlcOutputValue h timeoutFeeSat successFeeSat
    cltvExpiry := h.cltvExpiry
    state := h.state }

theorem legacyHtlcOutput_amountSat (h : HTLCRecord) :
    (legacyHtlcOutput h).amountSat = Msat.toSatFloor h.amountMsat := rfl

theorem legacyHtlcOutput_direction (h : HTLCRecord) :
    (legacyHtlcOutput h).direction = h.direction := rfl

theorem legacyHtlcOutput_cltvExpiry (h : HTLCRecord) :
    (legacyHtlcOutput h).cltvExpiry = h.cltvExpiry := rfl

theorem netHtlcOutput_amountSat (t s : Nat) (h : HTLCRecord) :
    (netHtlcOutput t s h).amountSat = htlcOutputValue h t s := rfl

theorem netHtlcOutput_direction (t s : Nat) (h : HTLCRecord) :
    (netHtlcOutput t s h).direction = h.direction := rfl

theorem netHtlcOutput_cltvExpiry (t s : Nat) (h : HTLCRecord) :
    (netHtlcOutput t s h).cltvExpiry = h.cltvExpiry := rfl

/-- The fee view of the net projection is the record's direction fee. -/
theorem htlcFeeOf_netHtlcOutput (t s : Nat) (h : HTLCRecord) :
    htlcFeeOf t s (netHtlcOutput t s h) = secondStageFee h.direction t s := rfl

/-- At zero second-stage fees the net projection is the legacy projection. -/
theorem netHtlcOutput_eq_legacy_of_zero (h : HTLCRecord) :
    netHtlcOutput 0 0 h = legacyHtlcOutput h := by
  rcases h with ⟨id, dir, amt, ph, cltv, st⟩
  cases dir <;> rfl

/-- Net value plus withheld second-stage fee is the legacy (gross) value,
provided the fee is covered by the whole-satoshi amount. -/
theorem netHtlcOutput_add_fee (t s : Nat) (h : HTLCRecord)
    (hfee : secondStageFee h.direction t s ≤ Msat.toSatFloor h.amountMsat) :
    (netHtlcOutput t s h).amountSat + htlcFeeOf t s (netHtlcOutput t s h) =
      (legacyHtlcOutput h).amountSat := by
  simpa [netHtlcOutput, legacyHtlcOutput, htlcFeeOf] using
    htlcOutputValue_add_secondStageFee h t s hfee

/-- Mapping the legacy projection to output values is the gross total. -/
theorem htlcOutputsValue_map_legacy (hs : List HTLCRecord) :
    htlcOutputsValue (hs.map legacyHtlcOutput) = grossTotal hs := by
  unfold grossTotal
  induction hs with
  | nil => rfl
  | cons h tl ih =>
      simp [htlcOutputsValue, legacyHtlcOutput, ih]

/-- The exact gap between the legacy (gross) HTLC group and the rich (net)
group, before any dust trimming: the difference is exactly the withheld
second-stage fees.  This is the algebraic content of `CH-02`. -/
theorem htlcGroup_legacy_eq_net_add_fees (t s : Nat) (hs : List HTLCRecord)
    (hfees : ∀ h ∈ hs, secondStageFee h.direction t s ≤ Msat.toSatFloor h.amountMsat) :
    htlcOutputsValue (hs.map legacyHtlcOutput) =
      htlcOutputsValue (hs.map (netHtlcOutput t s)) +
        secondStageFeeTotal t s (hs.map (netHtlcOutput t s)) := by
  induction hs with
  | nil => rfl
  | cons h tl ih =>
      have hfee := hfees h (by simp)
      have htl : ∀ x ∈ tl,
          secondStageFee x.direction t s ≤ Msat.toSatFloor x.amountMsat :=
        fun x hx => hfees x (by simp [hx])
      have hih := ih htl
      have hnet := netHtlcOutput_add_fee t s h hfee
      simp only [List.map_cons, htlcOutputsValue, List.sum_cons,
        secondStageFeeTotal] at hih ⊢
      omega

/-- With no second-stage fee the legacy and net HTLC groups have the same
value.  This is the hypothesis under which the legacy reading is sound. -/
theorem htlcGroup_legacy_eq_net_of_zeroFee (hs : List HTLCRecord) :
    htlcOutputsValue (hs.map legacyHtlcOutput) =
      htlcOutputsValue (hs.map (netHtlcOutput 0 0)) := by
  induction hs with
  | nil => rfl
  | cons h tl ih =>
      rw [List.map_cons, List.map_cons, netHtlcOutput_eq_legacy_of_zero h,
        htlcOutputsValue, htlcOutputsValue, ih]

/-! ## 4. The trimming threshold in gross terms -/

/-- BOLT 3's HTLC trimming threshold on the *gross* amount: the owner's dust
limit plus the direction's second-stage fee. -/
def htlcDustThreshold (dustLimitSat timeoutFeeSat successFeeSat : Nat)
    (h : CommitmentHTLCOutput) : Nat :=
  dustLimitSat + htlcFeeOf timeoutFeeSat successFeeSat h

theorem htlcDustThreshold_eq (d t s : Nat) (h : CommitmentHTLCOutput) :
    htlcDustThreshold d t s h = d + htlcFeeOf t s h := rfl

/-- A positive dust limit is all that is needed to rewrite the saturating
subtraction of the net value as the gross threshold. -/
theorem net_value_lt_dust_iff_threshold {h : HTLCRecord} {d t s : Nat}
    (hd : 0 < d) :
    htlcOutputValue h t s < d ↔
      Msat.toSatFloor h.amountMsat < d + secondStageFee h.direction t s := by
  unfold htlcOutputValue
  omega

/-- Likewise for "not dust": the rich test `dust ≤ net` is exactly the BOLT 3
test `dust + second_stage_fee ≤ gross`. -/
theorem net_value_ge_dust_iff_threshold {h : HTLCRecord} {d t s : Nat}
    (hd : 0 < d) :
    d ≤ htlcOutputValue h t s ↔
      d + secondStageFee h.direction t s ≤ Msat.toSatFloor h.amountMsat := by
  unfold htlcOutputValue
  omega

/-- The model's record-level dust test, restated in gross terms. -/
theorem isDustHTLC_iff_gross_lt_threshold {h : HTLCRecord} {d t s : Nat}
    (hd : 0 < d) :
    isDustHTLC h d t s = true ↔
      Msat.toSatFloor h.amountMsat < d + secondStageFee h.direction t s := by
  rw [isDust_iff]
  exact net_value_lt_dust_iff_threshold (h := h) (d := d) (t := t) (s := s) hd

/-- The record-level "has output" test, restated in gross terms.  Equality
with the threshold is kept, not trimmed. -/
theorem hasOutput_iff_threshold {h : HTLCRecord} {d t s : Nat} (hd : 0 < d) :
    hasOutput h d t s = true ↔
      d + secondStageFee h.direction t s ≤ Msat.toSatFloor h.amountMsat := by
  rw [hasOutput_iff]
  exact net_value_ge_dust_iff_threshold (h := h) (d := d) (t := t) (s := s) hd

/-- The rich `CommitmentTx` trims the net projection of a record exactly when
the gross amount is below the BOLT 3 threshold.  This connects
`CommitmentTx.htlcOutput` to `isDustHTLC` through the second-stage fee. -/
theorem htlcOutput_net_none_iff (tx : CommitmentTx) (h : HTLCRecord) (t s : Nat)
    (hd : 0 < tx.dustLimitSat) :
    tx.htlcOutput (netHtlcOutput t s h) = none ↔
      Msat.toSatFloor h.amountMsat <
        tx.dustLimitSat + secondStageFee h.direction t s := by
  have hiff := net_value_lt_dust_iff_threshold
    (h := h) (d := tx.dustLimitSat) (t := t) (s := s) hd
  unfold CommitmentTx.htlcOutput
  by_cases hle : tx.dustLimitSat ≤ (netHtlcOutput t s h).amountSat
  · have hnot : ¬ (netHtlcOutput t s h).amountSat < tx.dustLimitSat :=
      Nat.not_lt.mpr hle
    have hnot' : ¬ Msat.toSatFloor h.amountMsat <
        tx.dustLimitSat + secondStageFee h.direction t s := by
      intro hlt
      exact hnot (hiff.mpr hlt)
    simp [hle, hnot']
  · have hlt : (netHtlcOutput t s h).amountSat < tx.dustLimitSat :=
      Nat.lt_of_not_le hle
    have hgross := hiff.mp hlt
    simp [hle, hgross]

/-! ## 5. The trim view over a record list -/

/-- The records whose commitment output survives BOLT 3's dust test. -/
def survivingRecords (dustLimitSat timeoutFeeSat successFeeSat : Nat)
    (hs : List HTLCRecord) : List HTLCRecord :=
  hs.filter (fun h => hasOutput h dustLimitSat timeoutFeeSat successFeeSat)

/-- The records whose commitment output is trimmed. -/
def trimmedRecords (dustLimitSat timeoutFeeSat successFeeSat : Nat)
    (hs : List HTLCRecord) : List HTLCRecord :=
  hs.filter (fun h => isDustHTLC h dustLimitSat timeoutFeeSat successFeeSat)

/-- The rich HTLC output group: surviving records projected to their net
values. -/
def survivingNetOutputs (dustLimitSat timeoutFeeSat successFeeSat : Nat)
    (hs : List HTLCRecord) : List CommitmentHTLCOutput :=
  (survivingRecords dustLimitSat timeoutFeeSat successFeeSat hs).map
    (netHtlcOutput timeoutFeeSat successFeeSat)

/-- The value of the surviving net HTLC outputs. -/
def survivorNetTotal (dustLimitSat timeoutFeeSat successFeeSat : Nat)
    (hs : List HTLCRecord) : Nat :=
  htlcOutputsValue (survivingNetOutputs dustLimitSat timeoutFeeSat successFeeSat hs)

/-- The second-stage fees withheld from the surviving HTLC outputs. -/
def survivorFeeTotal (dustLimitSat timeoutFeeSat successFeeSat : Nat)
    (hs : List HTLCRecord) : Nat :=
  ((survivingRecords dustLimitSat timeoutFeeSat successFeeSat hs).map
    (fun h => secondStageFee h.direction timeoutFeeSat successFeeSat)).sum

/-- The gross value of the trimmed HTLC records.  BOLT 3 adds this value to
the commitment transaction fee. -/
def trimmedGrossTotal (dustLimitSat timeoutFeeSat successFeeSat : Nat)
    (hs : List HTLCRecord) : Nat :=
  ((trimmedRecords dustLimitSat timeoutFeeSat successFeeSat hs).map
    (fun h => Msat.toSatFloor h.amountMsat)).sum

/-- At dust limit zero and zero second-stage fees every record survives
trimming. -/
theorem survivingRecords_zero (hs : List HTLCRecord) :
    survivingRecords 0 0 0 hs = hs := by
  refine List.filter_eq_self.mpr ?_
  intro h _
  cases h.direction <;>
    simp [hasOutput, isDustHTLC, htlcOutputValue, secondStageFee]

/-- At dust limit zero and zero second-stage fees the surviving net outputs
are exactly the legacy projection of the records. -/
theorem survivingNetOutputs_zero (hs : List HTLCRecord) :
    survivingNetOutputs 0 0 0 hs = hs.map legacyHtlcOutput := by
  unfold survivingNetOutputs
  rw [survivingRecords_zero]
  exact List.map_congr_left (fun h _ => netHtlcOutput_eq_legacy_of_zero h)

/-- **Second-stage-fee / trimming partition.**  Every gross HTLC amount is
either paid to a surviving net output, withheld as that output's second-stage
fee, or trimmed and therefore added to the commitment fee.  This is the exact
value accounting that `CH-02` asks for, over an arbitrary record list. -/
theorem grossTotal_eq_partition (d t s : Nat) (hd : 0 < d) (hs : List HTLCRecord) :
    grossTotal hs =
      survivorNetTotal d t s hs + survivorFeeTotal d t s hs +
        trimmedGrossTotal d t s hs := by
  induction hs with
  | nil => rfl
  | cons h tl ih =>
      unfold grossTotal survivorNetTotal survivorFeeTotal trimmedGrossTotal
        survivingNetOutputs survivingRecords trimmedRecords at *
      by_cases hout : hasOutput h d t s = true
      · have hdust : isDustHTLC h d t s = false := by
          unfold hasOutput at hout
          cases hb : isDustHTLC h d t s <;> simp [hb] at hout ⊢
        have hfee := secondStageFee_le_of_not_dust d t s hd hdust
        have hnet := htlcOutputValue_add_secondStageFee h t s hfee
        have hneg : ¬ (isDustHTLC h d t s = true) := by rw [hdust]; simp
        simp only [List.filter_cons]
        rw [ite_eq_left hout, ite_eq_right hneg]
        simp only [List.map_cons, List.sum_cons, htlcOutputsValue]
        have hi : (netHtlcOutput t s h).amountSat = htlcOutputValue h t s := rfl
        omega
      · have hdust : isDustHTLC h d t s = true := by
          unfold hasOutput at hout
          cases hb : isDustHTLC h d t s <;> simp [hb] at hout ⊢
        simp only [List.filter_cons]
        rw [ite_eq_right hout, ite_eq_left hdust]
        simp only [List.map_cons, List.sum_cons]
        omega

/-! ## 6. The legacy output view of the rich model -/

/-- The kind/value projection preserves the satoshi value on every non-anchor
kind.  The two anchor kinds deliberately project to the fixed BOLT 3 anchor
value `anchorOutputSat`, so value preservation only holds for outputs that the
model actually constructed as anchors. -/
theorem toCommitmentOutput_value_of_nonAnchor (o : CommitmentTxOutput)
    (hl : o.kind ≠ .localAnchor) (hr : o.kind ≠ .remoteAnchor) :
    (o.toCommitmentOutput).value = o.valueSat := by
  rcases o with ⟨k, v, s, c⟩
  cases k <;> simp_all [CommitmentTxOutput.toCommitmentOutput, CommitmentOutput.value]

/-- For every output that the rich model actually emits, the legacy projection
preserves the satoshi value.  Anchor outputs are emitted with
`valueSat = anchorOutputSat`, exactly the value that the legacy anchor
constructors carry. -/
theorem outputs_toCommitmentOutput_value_eq (tx : CommitmentTx)
    {o : CommitmentTxOutput} (ho : o ∈ tx.outputs) :
    (o.toCommitmentOutput).value = o.valueSat := by
  rw [CommitmentTx.mem_outputs_iff, CommitmentTx.mem_outputsUnsorted_iff] at ho
  rcases ho with h | h | h | h | h
  · rw [CommitmentTx.mem_toLocalOutput_iff] at h
    rw [h.2]; rfl
  · rw [CommitmentTx.mem_toRemoteOutput_iff] at h
    rw [h.2]; rfl
  · rw [List.mem_filterMap] at h
    obtain ⟨a, _, ha⟩ := h
    rw [CommitmentTx.mem_htlcOutput_iff] at ha
    rw [ha.2]; rfl
  · unfold CommitmentTx.localAnchorOutput at h
    by_cases ha : tx.commitment.anchorOutputs
    · simp [ha] at h
      rw [h]; rfl
    · simp [ha] at h
  · unfold CommitmentTx.remoteAnchorOutput at h
    by_cases ha : tx.commitment.anchorOutputs
    · simp [ha] at h
      rw [h]; rfl
    · simp [ha] at h

/-- The legacy view of a rich commitment transaction: the sorted rich output
list, projected onto the legacy `CommitmentOutput` type. -/
def legacyOutputs (tx : CommitmentTx) : List CommitmentOutput :=
  tx.outputs.map CommitmentTxOutput.toCommitmentOutput

/-- The value removed by BOLT 3 trimming: below-dust `to_local`,
`to_remote`, and HTLC outputs.  Anchors are never trimmed. -/
def trimmedValue (tx : CommitmentTx) : Nat :=
  (if tx.dustLimitSat ≤ tx.commitment.toLocalSat then 0
    else tx.commitment.toLocalSat) +
  (if tx.dustLimitSat ≤ tx.commitment.toRemoteSat then 0
    else tx.commitment.toRemoteSat) +
  (tx.commitment.htlcs.map (fun h =>
    if tx.dustLimitSat ≤ h.amountSat then 0 else h.amountSat)).sum

/-- The value sum of the HTLC group of `outputsUnsorted` is the per-record
kept/trimmed split.  The split keeps a zero for every trimmed HTLC, whereas
`filterMap` omits the record entirely; the two agree after summing. -/
theorem filterMap_htlc_valueSat_sum (tx : CommitmentTx)
    (hs : List CommitmentHTLCOutput) :
    ((hs.filterMap tx.htlcOutput).map (fun o => o.valueSat)).sum =
      (hs.map (fun h =>
        if tx.dustLimitSat ≤ h.amountSat then h.amountSat else 0)).sum := by
  induction hs with
  | nil => rfl
  | cons h tl ih =>
      by_cases hd : tx.dustLimitSat ≤ h.amountSat
      · simp [CommitmentTx.htlcOutput, hd, CommitmentTxOutput.htlc, ih]
      · simp [CommitmentTx.htlcOutput, hd, ih]

/-- Pointwise value split of a kept/trimmed partition. -/
theorem kept_trimmed_value_split (d : Nat) (hs : List CommitmentHTLCOutput) :
    (hs.map (fun h => if d ≤ h.amountSat then h.amountSat else 0)).sum +
      (hs.map (fun h => if d ≤ h.amountSat then 0 else h.amountSat)).sum =
    (hs.map (fun h => h.amountSat)).sum := by
  induction hs with
  | nil => rfl
  | cons h tl ih =>
      by_cases hd : d ≤ h.amountSat <;> simp [hd] <;> omega

/-- **Trimming preservation, pre-sort.**  The projected value of the trimmed
construction plus the value it removes is exactly the commitment's
`totalOutputValue`.  Sorting does not change the sum, so the same statement
holds for `tx.outputs`. -/
theorem outputsUnsorted_value_sum_add_trimmedValue (tx : CommitmentTx) :
    ((tx.outputsUnsorted.map CommitmentTxOutput.toCommitmentOutput).map
        CommitmentOutput.value).sum + trimmedValue tx =
      tx.commitment.totalOutputValue := by
  have hloc :
      (((tx.toLocalOutput.toList).map CommitmentTxOutput.toCommitmentOutput).map
          CommitmentOutput.value).sum =
        (if tx.dustLimitSat ≤ tx.commitment.toLocalSat then
          tx.commitment.toLocalSat else 0) := by
    unfold CommitmentTx.toLocalOutput
    by_cases h : tx.dustLimitSat ≤ tx.commitment.toLocalSat <;>
      simp [h, CommitmentTxOutput.toLocal, CommitmentTxOutput.toCommitmentOutput,
        CommitmentOutput.value]
  have hrem :
      (((tx.toRemoteOutput.toList).map CommitmentTxOutput.toCommitmentOutput).map
          CommitmentOutput.value).sum =
        (if tx.dustLimitSat ≤ tx.commitment.toRemoteSat then
          tx.commitment.toRemoteSat else 0) := by
    unfold CommitmentTx.toRemoteOutput
    by_cases h : tx.dustLimitSat ≤ tx.commitment.toRemoteSat <;>
      simp [h, CommitmentTxOutput.toRemote, CommitmentTxOutput.toCommitmentOutput,
        CommitmentOutput.value]
  have hhtlc :
      (((tx.commitment.htlcs.filterMap tx.htlcOutput).map
          CommitmentTxOutput.toCommitmentOutput).map CommitmentOutput.value).sum =
        (tx.commitment.htlcs.map (fun h =>
          if tx.dustLimitSat ≤ h.amountSat then h.amountSat else 0)).sum := by
    rw [List.map_map]
    have hcongr : ∀ o ∈ tx.commitment.htlcs.filterMap tx.htlcOutput,
        (CommitmentOutput.value ∘ CommitmentTxOutput.toCommitmentOutput) o = o.valueSat := by
      intro o ho
      rw [List.mem_filterMap] at ho
      obtain ⟨h, _, hh⟩ := ho
      rw [CommitmentTx.mem_htlcOutput_iff] at hh
      rw [hh.2]
      rfl
    have hmap : List.map
          (CommitmentOutput.value ∘ CommitmentTxOutput.toCommitmentOutput)
          (tx.commitment.htlcs.filterMap tx.htlcOutput) =
        List.map (fun o => o.valueSat)
          (tx.commitment.htlcs.filterMap tx.htlcOutput) :=
      List.map_congr_left hcongr
    rw [hmap]
    exact filterMap_htlc_valueSat_sum tx tx.commitment.htlcs
  have hanch_local :
      (((tx.localAnchorOutput.toList.map
          CommitmentTxOutput.toCommitmentOutput).map CommitmentOutput.value).sum) =
        (if tx.commitment.anchorOutputs then anchorOutputSat else 0) := by
    unfold CommitmentTx.localAnchorOutput
    by_cases ha : tx.commitment.anchorOutputs <;>
      simp [ha, CommitmentTxOutput.localAnchor,
        CommitmentTxOutput.toCommitmentOutput, CommitmentOutput.value,
        anchorOutputSat]
  have hanch_remote :
      (((tx.remoteAnchorOutput.toList.map
          CommitmentTxOutput.toCommitmentOutput).map CommitmentOutput.value).sum) =
        (if tx.commitment.anchorOutputs then anchorOutputSat else 0) := by
    unfold CommitmentTx.remoteAnchorOutput
    by_cases ha : tx.commitment.anchorOutputs <;>
      simp [ha, CommitmentTxOutput.remoteAnchor,
        CommitmentTxOutput.toCommitmentOutput, CommitmentOutput.value,
        anchorOutputSat]
  unfold CommitmentTx.outputsUnsorted trimmedValue Commitment.totalOutputValue
    Commitment.htlcOutputValue Commitment.anchorOutputValue
  simp only [List.map_append, List.sum_append]
  have hanch_two :
      (if tx.commitment.anchorOutputs then 2 * anchorOutputSat else 0) =
        2 * (if tx.commitment.anchorOutputs then anchorOutputSat else 0) := by
    by_cases ha : tx.commitment.anchorOutputs <;> simp [ha]
  have hloc_split :
      (if tx.dustLimitSat ≤ tx.commitment.toLocalSat then
          tx.commitment.toLocalSat else 0) +
        (if tx.dustLimitSat ≤ tx.commitment.toLocalSat then 0
          else tx.commitment.toLocalSat) = tx.commitment.toLocalSat := by
    by_cases h : tx.dustLimitSat ≤ tx.commitment.toLocalSat <;> simp [h]
  have hrem_split :
      (if tx.dustLimitSat ≤ tx.commitment.toRemoteSat then
          tx.commitment.toRemoteSat else 0) +
        (if tx.dustLimitSat ≤ tx.commitment.toRemoteSat then 0
          else tx.commitment.toRemoteSat) = tx.commitment.toRemoteSat := by
    by_cases h : tx.dustLimitSat ≤ tx.commitment.toRemoteSat <;> simp [h]
  have hsum : htlcOutputsValue tx.commitment.htlcs =
      (tx.commitment.htlcs.map (fun h => h.amountSat)).sum :=
    Commitment.htlcOutputValue_eq_sum tx.commitment
  have hsplit := kept_trimmed_value_split tx.dustLimitSat tx.commitment.htlcs
  omega

/-- **Trimming preservation.**  The legacy projection of the sorted rich list
plus the trimmed value is the commitment's total output value. -/
theorem legacyOutputs_sum_add_trimmedValue (tx : CommitmentTx) :
    ((legacyOutputs tx).map CommitmentOutput.value |>.sum) + trimmedValue tx =
      tx.commitment.totalOutputValue := by
  have hperm : List.Perm ((legacyOutputs tx).map CommitmentOutput.value)
      ((tx.outputsUnsorted.map CommitmentTxOutput.toCommitmentOutput).map
        CommitmentOutput.value) := by
    unfold legacyOutputs
    exact ((tx.outputs_perm.map CommitmentTxOutput.toCommitmentOutput).map
      CommitmentOutput.value)
  have hsum := hperm.sum_nat
  rw [hsum]
  exact outputsUnsorted_value_sum_add_trimmedValue tx

/-- At a zero dust limit nothing is trimmed: only zero-valued non-HTLC
outputs are omitted, and they contribute zero. -/
theorem trimmedValue_eq_zero_of_dust_zero (tx : CommitmentTx)
    (hdust : tx.dustLimitSat = 0) :
    trimmedValue tx = 0 := by
  unfold trimmedValue
  simp only [hdust, Nat.zero_le, ite_true]
  induction tx.commitment.htlcs with
  | nil => rfl
  | cons h tl ih => simp [ih]

/-- **Legacy projection value sum at zero dust.**  With a zero dust limit the
legacy projection of the rich output list pays exactly `totalOutputValue`, for
*every* commitment record.  No non-zero-output hypothesis is needed because an
omitted zero-valued output contributes zero. -/
theorem legacyOutputs_sum_eq_totalOutputValue (tx : CommitmentTx)
    (hdust : tx.dustLimitSat = 0) :
    ((legacyOutputs tx).map CommitmentOutput.value |>.sum) =
      tx.commitment.totalOutputValue := by
  have h := legacyOutputs_sum_add_trimmedValue tx
  rw [trimmedValue_eq_zero_of_dust_zero tx hdust] at h
  omega

/-- **Ordering preservation.**  The legacy projection of the sorted rich
output list is nondecreasing in value.  Sorting is therefore not lost when a
legacy consumer reads values off the rich model. -/
theorem legacyOutputs_values_sorted (tx : CommitmentTx) :
    ((legacyOutputs tx).map CommitmentOutput.value).Pairwise (· ≤ ·) := by
  unfold legacyOutputs
  rw [List.map_map]
  have hcongr : ∀ o ∈ tx.outputs,
      (CommitmentOutput.value ∘ CommitmentTxOutput.toCommitmentOutput) o = o.valueSat :=
    fun o ho => outputs_toCommitmentOutput_value_eq tx ho
  have hmap : List.map
        (CommitmentOutput.value ∘ CommitmentTxOutput.toCommitmentOutput) tx.outputs =
      List.map (fun o => o.valueSat) tx.outputs :=
    List.map_congr_left hcongr
  rw [hmap]
  exact tx.outputs_values_sorted

/-- **The strongest true relation to the legacy view.**  Under a zero dust
limit and non-zero `to_local`/`to_remote`, the sorted rich output list
projects to a **permutation** of `Commitment.commitmentOutputs`.

Equality of lists is false in general: the rich list is sorted and the legacy
list is not (D12), and at a zero dust limit the rich model still emits a
zero-valued `to_local`/`to_remote` where the legacy function omits it.  A
permutation is exactly the on-chain-equivalent relation: same multiset of
outputs, canonical order supplied by the rich model. -/
theorem legacyOutputs_perm_commitmentOutputs (tx : CommitmentTx)
    (hdust : tx.dustLimitSat = 0)
    (hl : tx.commitment.toLocalSat ≠ 0)
    (hr : tx.commitment.toRemoteSat ≠ 0) :
    (legacyOutputs tx).Perm tx.commitment.commitmentOutputs := by
  unfold legacyOutputs
  have h := tx.outputs_perm.map CommitmentTxOutput.toCommitmentOutput
  rw [CommitmentTx.map_toCommitmentOutput_outputsUnsorted tx hdust hl hr] at h
  exact h

/-- Even without the non-zero-output hypotheses, the sums agree at zero dust:
the legacy reading is value-faithful, but not multiset-faithful when a zero
output is present. -/
theorem legacyOutputs_sum_eq_commitmentOutputs_sum (tx : CommitmentTx)
    (hdust : tx.dustLimitSat = 0) :
    ((legacyOutputs tx).map CommitmentOutput.value |>.sum) =
      (tx.commitment.commitmentOutputs.map CommitmentOutput.value).sum := by
  rw [legacyOutputs_sum_eq_totalOutputValue tx hdust,
    Commitment.commitmentOutputs_sum_eq_totalOutputValue]

/-! ## 7. The hypotheses are necessary: trimming changes the output set -/

/-- Demo record: one offered HTLC of 500 satoshis (500000 msat). -/
def dustDemoRecord : HTLCRecord :=
  { id := 0
    direction := .local
    amountMsat := ⟨500000⟩
    paymentHash := ⟨ByteArray.empty⟩
    cltvExpiry := 0
    state := .offered }

/-- A commitment transaction whose only non-anchor output is a 500-satoshi
HTLC, with the owner's dust limit set to 1000 satoshis. -/
def dustDemoTx : CommitmentTx :=
  { commitment :=
      { holder := .local
        commitmentNumber := 0
        fundingValueSat := 500
        toLocalSat := 0
        toRemoteSat := 0
        htlcs := [legacyHtlcOutput dustDemoRecord]
        feeSat := 0
        contestDelay := 0
        anchorOutputs := false }
    dustLimitSat := 1000
    toLocalScript := ⟨[]⟩
    toRemoteScript := ⟨[]⟩
    localAnchorScript := ⟨[]⟩
    remoteAnchorScript := ⟨[]⟩
    htlcScript := fun _ => ⟨[]⟩ }

theorem dustDemoRecord_amountSat :
    (legacyHtlcOutput dustDemoRecord).amountSat = 500 := rfl

theorem dustDemoTx_htlcOutput_none :
    dustDemoTx.htlcOutput (legacyHtlcOutput dustDemoRecord) = none := by
  unfold CommitmentTx.htlcOutput
  rw [dustDemoRecord_amountSat]
  rw [ite_eq_right (by decide)]

theorem dustDemoTx_toLocalOutput_none : dustDemoTx.toLocalOutput = none := by
  unfold CommitmentTx.toLocalOutput
  rw [ite_eq_right (by decide)]

theorem dustDemoTx_toRemoteOutput_none : dustDemoTx.toRemoteOutput = none := by
  unfold CommitmentTx.toRemoteOutput
  rw [ite_eq_right (by decide)]

theorem dustDemoTx_localAnchorOutput_none : dustDemoTx.localAnchorOutput = none := by
  unfold CommitmentTx.localAnchorOutput
  rw [ite_eq_right (by decide)]

theorem dustDemoTx_remoteAnchorOutput_none : dustDemoTx.remoteAnchorOutput = none := by
  unfold CommitmentTx.remoteAnchorOutput
  rw [ite_eq_right (by decide)]

theorem dustDemoTx_htlcs_filterMap :
    dustDemoTx.commitment.htlcs.filterMap dustDemoTx.htlcOutput = [] := by
  rw [show dustDemoTx.commitment.htlcs = [legacyHtlcOutput dustDemoRecord] from rfl,
    List.filterMap_cons]
  rw [show dustDemoTx.htlcOutput (legacyHtlcOutput dustDemoRecord) = none from
    dustDemoTx_htlcOutput_none]
  rfl

theorem dustDemoTx_outputs : dustDemoTx.outputs = [] := by
  unfold CommitmentTx.outputs CommitmentTx.outputsUnsorted
  rw [dustDemoTx_toLocalOutput_none, dustDemoTx_toRemoteOutput_none,
    dustDemoTx_htlcs_filterMap, dustDemoTx_localAnchorOutput_none,
    dustDemoTx_remoteAnchorOutput_none]
  simp [sortOutputs, List.mergeSort_nil]

theorem dustDemoTx_commitmentOutputs :
    dustDemoTx.commitment.commitmentOutputs =
      [CommitmentOutput.htlc .local 500] := by
  unfold Commitment.commitmentOutputs
  rw [show dustDemoTx.commitment.htlcs =
      [legacyHtlcOutput dustDemoRecord] from rfl]
  simp only [List.map_cons, List.map_nil]
  rw [show (legacyHtlcOutput dustDemoRecord).direction = .local from rfl,
      show (legacyHtlcOutput dustDemoRecord).amountSat = 500 from
        dustDemoRecord_amountSat]
  simp [dustDemoTx]

/-- **The zero-dust hypothesis in `legacyOutputs_perm_commitmentOutputs` is
necessary.**  A 500-satoshi HTLC under a 1000-satoshi dust limit is trimmed by
the rich model but still emitted by the legacy function, so the two output
lists do not even have the same multiset.  This is the integration gap D12
describes, now visible through the rich/legacy view. -/
theorem dust_trimming_not_perm :
    ¬ (legacyOutputs dustDemoTx).Perm dustDemoTx.commitment.commitmentOutputs := by
  unfold legacyOutputs
  rw [dustDemoTx_outputs, dustDemoTx_commitmentOutputs]
  intro h
  have hlen := h.length_eq
  simp at hlen

/-- D12's unconditional ordering refutation is retained: no
`Commitment.commitmentOutputs`-level ordering theorem can be claimed. -/
theorem legacy_ordering_refuted :
    ¬ (∀ c : Commitment,
        (c.commitmentOutputs.map CommitmentOutput.value).Pairwise (· ≤ ·)) :=
  LnLean.Proofs.WaveD.D12.waveD_d12_output_ordering_fails

/-- D12's zero-valued HTLC counterexample is retained: the legacy function
emits a zero-valued HTLC output, so it applies no dust filter of its own. -/
theorem legacy_zero_value_htlc_emitted :
    CommitmentOutput.htlc .local 0 ∈
      LnLean.Proofs.WaveD.D12.zeroValueHtlcCommitment.commitmentOutputs :=
  LnLean.Proofs.WaveD.D12.waveD_d12_zero_value_htlc_emitted

/-! ## 8. Explicit constructions and the second-stage-fee accounting -/

/-- The total anchor value emitted by the model, local to this module so the
construction does not depend on proof-layer modules. -/
def anchorTotal (anchors : Bool) : Nat :=
  if anchors then 2 * anchorOutputSat else 0

theorem anchorTotal_eq_if (anchors : Bool) :
    anchorTotal anchors = (if anchors then 2 * anchorOutputSat else 0) := rfl

theorem anchorTotal_eq_anchorOutputValue (c : Commitment) :
    c.anchorOutputValue = anchorTotal c.anchorOutputs := rfl

/-- The legacy commitment built directly from HTLC records: gross amounts,
no second-stage fee withheld, and the funder's residual output reduced by the
whole pending HTLC value. -/
def legacyCommitmentOfRecords (holder : Direction) (number funding fee toLocal
    contestDelay : Nat) (anchors : Bool) (hs : List HTLCRecord) : Commitment :=
  { holder := holder
    commitmentNumber := number
    fundingValueSat := funding
    toLocalSat := toLocal
    toRemoteSat := funding - fee - toLocal - grossTotal hs - anchorTotal anchors
    htlcs := hs.map legacyHtlcOutput
    feeSat := fee
    contestDelay := contestDelay
    anchorOutputs := anchors }

/-- The rich net commitment: only surviving HTLCs become outputs, each at its
net (post-second-stage-fee) value, and the funder's residual output is reduced
by the survivors' net value only.  This is the D47 "pre-trimmed" convention:
the trimmed value stays in the funder's output. -/
def netCommitmentOfRecords (holder : Direction) (number funding fee toLocal
    contestDelay : Nat) (anchors : Bool) (d t s : Nat)
    (hs : List HTLCRecord) : Commitment :=
  { holder := holder
    commitmentNumber := number
    fundingValueSat := funding
    toLocalSat := toLocal
    toRemoteSat := funding - fee - toLocal - survivorNetTotal d t s hs -
      anchorTotal anchors
    htlcs := survivingNetOutputs d t s hs
    feeSat := fee
    contestDelay := contestDelay
    anchorOutputs := anchors }

/-- The BOLT 3 construction: only surviving HTLCs become (net) outputs, while
the funder's residual output is reduced by the **whole** pending HTLC value.
The trimmed gross value and the withheld second-stage fees therefore become
available as fee. -/
def bolt3CommitmentOfRecords (holder : Direction) (number funding fee toLocal
    contestDelay : Nat) (anchors : Bool) (d t s : Nat)
    (hs : List HTLCRecord) : Commitment :=
  { holder := holder
    commitmentNumber := number
    fundingValueSat := funding
    toLocalSat := toLocal
    toRemoteSat := funding - fee - toLocal - grossTotal hs - anchorTotal anchors
    htlcs := survivingNetOutputs d t s hs
    feeSat := fee
    contestDelay := contestDelay
    anchorOutputs := anchors }

/-- **Exact conservation of the legacy construction.**  If the base fee, the
broadcaster's output, the whole gross HTLC value, and the anchors fit in the
funding value, then the emitted outputs plus the fee reconstruct it. -/
theorem legacyCommitmentOfRecords_conservation (holder : Direction) (number
    funding fee toLocal contestDelay : Nat) (anchors : Bool)
    (hs : List HTLCRecord)
    (hfit : fee + toLocal + grossTotal hs + anchorTotal anchors ≤ funding) :
    (legacyCommitmentOfRecords holder number funding fee toLocal contestDelay
        anchors hs).totalOutputValue + fee = funding := by
  unfold legacyCommitmentOfRecords Commitment.totalOutputValue
    Commitment.htlcOutputValue Commitment.anchorOutputValue
  rw [htlcOutputsValue_map_legacy]
  rw [anchorTotal_eq_if] at hfit ⊢
  dsimp only
  omega

/-- **Exact conservation of the rich net construction** under its own
no-underflow condition.  The trimmed value remains in the funder's output, so
the base fee alone reconciles the ledger. -/
theorem netCommitmentOfRecords_conservation (holder : Direction) (number funding
    fee toLocal contestDelay : Nat) (anchors : Bool) (d t s : Nat)
    (hs : List HTLCRecord)
    (hfit : fee + toLocal + survivorNetTotal d t s hs + anchorTotal anchors ≤ funding) :
    (netCommitmentOfRecords holder number funding fee toLocal contestDelay
        anchors d t s hs).totalOutputValue + fee = funding := by
  unfold netCommitmentOfRecords Commitment.totalOutputValue
    Commitment.htlcOutputValue Commitment.anchorOutputValue
  unfold survivorNetTotal at hfit ⊢
  rw [anchorTotal_eq_if] at hfit ⊢
  dsimp only
  omega

/-- **BOLT 3 second-stage-fee accounting.**  For the BOLT 3 construction the
emitted outputs plus the base fee plus the withheld second-stage fees plus the
trimmed gross value reconstruct the funding value.  Equivalently, the
effective fee `funding - totalOutputValue` is
`base fee + withheld second-stage fees + trimmed gross value`. -/
theorem bolt3CommitmentOfRecords_conservation (holder : Direction) (number
    funding fee toLocal contestDelay : Nat) (anchors : Bool) (d t s : Nat)
    (hs : List HTLCRecord) (hd : 0 < d)
    (hfit : fee + toLocal + grossTotal hs + anchorTotal anchors ≤ funding) :
    (bolt3CommitmentOfRecords holder number funding fee toLocal contestDelay
        anchors d t s hs).totalOutputValue + fee +
        survivorFeeTotal d t s hs + trimmedGrossTotal d t s hs = funding := by
  have hpart := grossTotal_eq_partition d t s hd hs
  unfold survivorNetTotal at hpart
  unfold bolt3CommitmentOfRecords Commitment.totalOutputValue
    Commitment.htlcOutputValue Commitment.anchorOutputValue
  rw [anchorTotal_eq_if] at hfit ⊢
  dsimp only
  omega

/-- The zero-fee, zero-dust case of the BOLT 3 construction is exactly the
legacy commitment. -/
theorem bolt3CommitmentOfRecords_zero_eq_legacy (holder : Direction) (number
    funding fee toLocal contestDelay : Nat) (anchors : Bool)
    (hs : List HTLCRecord) :
    bolt3CommitmentOfRecords holder number funding fee toLocal contestDelay
        anchors 0 0 0 hs =
      legacyCommitmentOfRecords holder number funding fee toLocal contestDelay
        anchors hs := by
  unfold bolt3CommitmentOfRecords legacyCommitmentOfRecords
  rw [survivingNetOutputs_zero]

/-- The rich net commitment at zero dust and zero second-stage fees is exactly
the legacy commitment built from the same records. -/
theorem netCommitmentOfRecords_zero_eq_legacy (holder : Direction) (number
    funding fee toLocal contestDelay : Nat) (anchors : Bool)
    (hs : List HTLCRecord) :
    netCommitmentOfRecords holder number funding fee toLocal contestDelay
        anchors 0 0 0 hs =
      legacyCommitmentOfRecords holder number funding fee toLocal contestDelay
        anchors hs := by
  unfold netCommitmentOfRecords legacyCommitmentOfRecords
  have hsurv : survivorNetTotal 0 0 0 hs = grossTotal hs := by
    unfold survivorNetTotal
    rw [survivingNetOutputs_zero, htlcOutputsValue_map_legacy]
  rw [survivingNetOutputs_zero, hsurv]

/-- **End-to-end refinement at zero dust and zero second-stage fees.**  If a
rich `CommitmentTx` carries the net construction of a record list at zero
fees, and its dust limit is zero, then its sorted output list projects to a
permutation of the legacy commitment built from the same records.  The
remaining premises `hl`/`hr` are exactly the non-zero outputs that the legacy
function would omit but the rich model emits (with value zero). -/
theorem richOutputs_refine_legacyCommitment (tx : CommitmentTx) (holder : Direction)
    (number funding fee toLocal contestDelay : Nat) (anchors : Bool)
    (hs : List HTLCRecord)
    (hcommit : tx.commitment =
      netCommitmentOfRecords holder number funding fee toLocal contestDelay
        anchors 0 0 0 hs)
    (hdust : tx.dustLimitSat = 0)
    (hl : tx.commitment.toLocalSat ≠ 0)
    (hr : tx.commitment.toRemoteSat ≠ 0) :
    (legacyOutputs tx).Perm
      (legacyCommitmentOfRecords holder number funding fee toLocal contestDelay
        anchors hs).commitmentOutputs := by
  have hl' : tx.commitment.toLocalSat ≠ 0 := by simpa [hcommit] using hl
  have hr' : tx.commitment.toRemoteSat ≠ 0 := by simpa [hcommit] using hr
  have h := legacyOutputs_perm_commitmentOutputs tx hdust hl' hr'
  simpa [hcommit, netCommitmentOfRecords_zero_eq_legacy] using h

end LnLean.Proofs.Channel.CommitmentIntegration
