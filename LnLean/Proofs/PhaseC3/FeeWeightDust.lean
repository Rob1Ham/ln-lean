import LnLean

/-!
# LnLean.Proofs.PhaseC3.FeeWeightDust

English claim.  Suppose a commitment carries a fee that covers the BOLT 3
requirement `feerate_per_kw * weight / 1000` at its own weight, every HTLC it
still carries has survived the BOLT 3 dust test, and its output values plus
the fee fit inside the funding value.  Then

* every emitted output has a non-negative value and a value at most the
  funding value,
* the sum of all output values is at most the funding value,
* the required commitment fee is at most the funding value,
* the commitment weight is exactly `base + 172 * (number of HTLC outputs)`,
  with base `724` without anchors and `1124` with anchors, and
* the weight (hence the required fee) is monotone in the number of HTLC
  outputs; adding one surviving HTLC raises the weight by exactly `172`.

Trimming dust HTLCs can only lower the total output value, the weight, and
the required fee, so the same bounds hold for the trimmed commitment.  The
feerate and dust preconditions are named exactly: `FeeCoversWeight` is the
floored inequality on the commitment's own weight, and `CommitmentBudget`
records `∀ h ∈ c.htlcs, ¬ isDust dustLimitSat h.amountSat` together with the
value equation `totalOutputValue + feeSat ≤ fundingValueSat`.

BOLT sections.
* BOLT 3 §2 `Commitment Transaction` (`03-transactions.md:83-353`), trimming
  of HTLC outputs at `:305-354`, anchors at `:148-198`.
* BOLT 3 §4 `Fees` (`03-transactions.md:464-576`): expected weights
  `724 + 172 * htlcs` and `1124 + 172 * htlcs` at `:490-502`, floor-divided
  base fee at `:518-523`.
* BOLT 3 §5 `Dust Limits` (`03-transactions.md:583-620`): equality with the
  dust limit is not dust, which is why `isDust` is a strict inequality.

rust-lightning anchors at `fe4900930c6bd5786ec4203274d7cf312776a5a6`.
* `lightning/src/ln/chan_utils.rs:275-298`
  (`COMMITMENT_TX_WEIGHT_PER_HTLC = 172`, base weights, `commit_tx_fee_sat`).
* `lightning/src/sign/tx_builder.rs:997-1097` (HTLC dust test, funder
  subtraction, output trimming).
* `lightning/src/ln/chan_utils.rs:1887-1945`
  (`insert_non_htlc_outputs`, zero-valued output trimming and anchors).

What is explicitly NOT modelled.
* Bitcoin Core relay dust thresholds; the dust limit is the negotiated
  `dust_limit_satoshis` parameter, supplied to this module as `dustLimitSat`.
* The distinction between the HTLC-timeout and HTLC-success second-stage
  fees.  A `CommitmentHTLCOutput.amountSat` is treated as the value already
  net of that fee, so the trimming threshold here is the dust limit itself;
  for the gross-amount convention of `Commitment.addHtlc` pass
  `dust_limit_satoshis + htlc_tx_fee`.
* Anchors beyond their fixed `2 * 330` satoshi value, the single-anchor
  exception, `shared_anchor`, and child-pays-for-parent fee bumping.
* Output sorting (BIP 69+CLTV), witnesses, and the obscured commitment
  number; this module is purely about values, weights, and fees.
-/

namespace LnLean.Proofs.PhaseC3

namespace FeeWeightDust

open LnLean
open LnLean.Channel

set_option autoImplicit false

/-! ## Weight as a function of the HTLC-output count -/

/-- The commitment weight is the BOLT 3 base weight plus `172` per HTLC
output actually present.  The count is taken from the output list, so it
agrees with `Commitment.htlcs.length` even after trimming. -/
theorem commitment_weight_eq_base_add_htlcOutputCount (c : Commitment) :
    c.weight.val =
      commitmentBaseWeight c.anchorOutputs +
        commitmentHtlcWeight * htlcOutputCount c.commitmentOutputs := by
  unfold Commitment.weight
  rw [commitmentWeight_val, Commitment.htlcOutputCount_commitmentOutputs]

/-- Strict monotonicity of the weight in the raw HTLC count. -/
theorem commitmentWeight_lt_of_lt (anchors : Bool) {n m : Nat} (h : n < m) :
    (commitmentWeight anchors n).val < (commitmentWeight anchors m).val := by
  rw [commitmentWeight_val, commitmentWeight_val]
  have hk : 0 < commitmentHtlcWeight := by decide
  have hmul := Nat.mul_lt_mul_of_pos_left h hk
  omega

/-- Weight is monotone in the number of HTLC outputs of two commitments with
the same anchor setting. -/
theorem commitment_weight_le_of_htlcOutputCount_le {c c' : Commitment}
    (ha : c.anchorOutputs = c'.anchorOutputs)
    (h : htlcOutputCount c.commitmentOutputs ≤
      htlcOutputCount c'.commitmentOutputs) :
    c.weight.val ≤ c'.weight.val := by
  rw [commitment_weight_eq_base_add_htlcOutputCount c,
    commitment_weight_eq_base_add_htlcOutputCount c', ha]
  have := Nat.mul_le_mul_left commitmentHtlcWeight h
  omega

/-- Weight is strictly monotone in the number of HTLC outputs. -/
theorem commitment_weight_lt_of_htlcOutputCount_lt {c c' : Commitment}
    (ha : c.anchorOutputs = c'.anchorOutputs)
    (h : htlcOutputCount c.commitmentOutputs <
      htlcOutputCount c'.commitmentOutputs) :
    c.weight.val < c'.weight.val := by
  rw [commitment_weight_eq_base_add_htlcOutputCount c,
    commitment_weight_eq_base_add_htlcOutputCount c', ha]
  have hk : 0 < commitmentHtlcWeight := by decide
  have := Nat.mul_lt_mul_of_pos_left h hk
  omega

/-- The required fee is monotone in the number of HTLC outputs at a fixed
feerate.  The floor can make the step non-strict. -/
theorem commitmentFee_le_of_htlcOutputCount_le (r : FeeRate) {c c' : Commitment}
    (ha : c.anchorOutputs = c'.anchorOutputs)
    (h : htlcOutputCount c.commitmentOutputs ≤
      htlcOutputCount c'.commitmentOutputs) :
    (commitmentFee r c).val ≤ (commitmentFee r c').val := by
  unfold commitmentFee
  exact feeForWeight_mono_weight r
    (commitment_weight_le_of_htlcOutputCount_le ha h)

/-- Both weight and required fee are monotone in the HTLC-output count. -/
theorem commitment_weight_fee_mono_htlcOutputCount (r : FeeRate)
    {c c' : Commitment} (ha : c.anchorOutputs = c'.anchorOutputs)
    (h : htlcOutputCount c.commitmentOutputs ≤
      htlcOutputCount c'.commitmentOutputs) :
    c.weight.val ≤ c'.weight.val ∧
      (commitmentFee r c).val ≤ (commitmentFee r c').val :=
  ⟨commitment_weight_le_of_htlcOutputCount_le ha h,
    commitmentFee_le_of_htlcOutputCount_le r ha h⟩

/-! ## The feerate precondition, exactly -/

/-- The commitment fee covers the BOLT 3 floored requirement at the
commitment's own weight: `feerate_per_kw * weight / 1000 ≤ feeSat`.
This is the exact "fee is at least `feeRate * weight`" precondition used by
this module; `commitmentFee` is definitionally `feeForWeight r c.weight`. -/
def FeeCoversWeight (r : FeeRate) (c : Commitment) : Prop :=
  (feeForWeight r c.weight).val ≤ c.feeSat

/-- The predicate is exactly "the required commitment fee is covered". -/
theorem feeCoversWeight_iff_commitmentFee (r : FeeRate) (c : Commitment) :
    FeeCoversWeight r c ↔ (commitmentFee r c).val ≤ c.feeSat :=
  Iff.rfl

/-- Exact product form of the floored precondition: `x / 1000 ≤ f` iff
`x ≤ f * 1000 + 999`. -/
theorem feeCoversWeight_mul_le (r : FeeRate) (c : Commitment)
    (h : FeeCoversWeight r c) :
    r.msatPerKw * c.weight.val ≤ c.feeSat * 1000 + 999 := by
  unfold FeeCoversWeight feeForWeight at h
  exact (Nat.div_le_iff_le_mul (by decide : 0 < 1000)).mp h

/-- A raw product bound `feerate * weight ≤ fee * 1000` implies the floored
precondition. -/
theorem feeCoversWeight_of_mul_le (r : FeeRate) (c : Commitment)
    (h : r.msatPerKw * c.weight.val ≤ c.feeSat * 1000) :
    FeeCoversWeight r c := by
  unfold FeeCoversWeight feeForWeight
  exact (Nat.div_le_iff_le_mul (by decide : 0 < 1000)).mpr (by omega)

/-- Lowering the feerate preserves fee coverage. -/
theorem feeCoversWeight_of_rate_le {r r' : FeeRate} (c : Commitment)
    (hr : r.msatPerKw ≤ r'.msatPerKw) (h : FeeCoversWeight r' c) :
    FeeCoversWeight r c :=
  Nat.le_trans (feeForWeight_mono_rate hr c.weight) h

/-- Lowering the weight preserves fee coverage when the recorded fee is
unchanged (as it is under trimming or when paying out of the same fee). -/
theorem feeCoversWeight_of_weight_le (r : FeeRate) {c c' : Commitment}
    (hfeefix : c.feeSat = c'.feeSat)
    (hle : c.weight.val ≤ c'.weight.val) (h : FeeCoversWeight r c') :
    FeeCoversWeight r c := by
  unfold FeeCoversWeight at *
  rw [hfeefix]
  exact Nat.le_trans (feeForWeight_mono_weight r hle) h

/-- Under fee coverage, the required fee cannot exceed the funding value once
the value equation holds. -/
theorem commitment_requiredFee_le_funding (r : FeeRate) (c : Commitment)
    (hfee : FeeCoversWeight r c)
    (hbound : c.totalOutputValue + c.feeSat ≤ c.fundingValueSat) :
    (commitmentFee r c).val ≤ c.fundingValueSat := by
  have h1 : (commitmentFee r c).val ≤ c.feeSat := hfee
  omega

/-! ## Dust trimming -/

/-- One HTLC output survives the BOLT 3 dust test when its value is at least
the threshold.  Equality is not dust (BOLT 3 §5). -/
def htlcKept (dustLimitSat : Nat) (h : CommitmentHTLCOutput) : Bool :=
  decide (dustLimitSat ≤ h.amountSat)

/-- Drop every HTLC output below the dust limit.  For a
`CommitmentHTLCOutput` whose `amountSat` is already net of the second-stage
fee, `dustLimitSat` is `dust_limit_satoshis`; for the gross-amount convention
of `Commitment.addHtlc` it is `dust_limit_satoshis + htlc_tx_fee`. -/
def trimDust (dustLimitSat : Nat)
    (hs : List CommitmentHTLCOutput) : List CommitmentHTLCOutput :=
  hs.filter (htlcKept dustLimitSat)

theorem mem_trimDust {dustLimitSat : Nat} {hs : List CommitmentHTLCOutput}
    {h : CommitmentHTLCOutput} :
    h ∈ trimDust dustLimitSat hs ↔
      h ∈ hs ∧ ¬ isDust dustLimitSat h.amountSat := by
  unfold trimDust htlcKept isDust
  rw [List.mem_filter]
  constructor
  · rintro ⟨hm, hk⟩
    refine ⟨hm, ?_⟩
    have hge : dustLimitSat ≤ h.amountSat := of_decide_eq_true hk
    omega
  · rintro ⟨hm, hnd⟩
    exact ⟨hm, decide_eq_true (by omega)⟩

theorem trimDust_length_le (dustLimitSat : Nat)
    (hs : List CommitmentHTLCOutput) :
    (trimDust dustLimitSat hs).length ≤ hs.length :=
  List.length_filter_le _ _

theorem trimDust_sublist (dustLimitSat : Nat)
    (hs : List CommitmentHTLCOutput) :
    (trimDust dustLimitSat hs).Sublist hs :=
  List.filter_sublist

theorem trimDust_idem (dustLimitSat : Nat)
    (hs : List CommitmentHTLCOutput) :
    trimDust dustLimitSat (trimDust dustLimitSat hs) =
      trimDust dustLimitSat hs := by
  unfold trimDust
  rw [List.filter_eq_self]
  intro h hh
  exact (List.mem_filter.mp hh).2

/-- If every HTLC already survives the dust test, trimming is the identity. -/
theorem trimDust_eq_self_of_all {dustLimitSat : Nat}
    {hs : List CommitmentHTLCOutput}
    (h : ∀ x ∈ hs, ¬ isDust dustLimitSat x.amountSat) :
    trimDust dustLimitSat hs = hs := by
  unfold trimDust
  rw [List.filter_eq_self]
  intro x hx
  exact decide_eq_true (by
    have := h x hx
    unfold isDust at this
    omega)

/-- Every surviving HTLC meets the dust limit. -/
theorem trimDust_all_ge (dustLimitSat : Nat)
    (hs : List CommitmentHTLCOutput) :
    ∀ h ∈ trimDust dustLimitSat hs, dustLimitSat ≤ h.amountSat := by
  intro h hh
  have hnd := (mem_trimDust.mp hh).2
  unfold isDust at hnd
  omega

/-- Generic list fact: a filter is strictly shorter whenever some element
fails the predicate. -/
theorem length_filter_lt_of_exists_false {α : Type} (p : α → Bool) :
    ∀ {l : List α}, (∃ x ∈ l, p x = false) →
      (l.filter p).length < l.length
  | [], h => by
      rcases h with ⟨_, hx, _⟩
      simp at hx
  | x :: xs, h => by
      rcases h with ⟨y, hy, hyf⟩
      by_cases hx : p x = true
      · rw [List.filter_cons_of_pos hx]
        simp only [List.length_cons]
        rcases List.mem_cons.mp hy with rfl | hy'
        · rw [hx] at hyf
          exact absurd hyf (by simp)
        · have ih := length_filter_lt_of_exists_false p
            (l := xs) ⟨y, hy', hyf⟩
          omega
      · rw [List.filter_cons_of_neg hx]
        simp only [List.length_cons]
        have hle := List.length_filter_le p xs
        omega

/-- Trimming is strict in length whenever some HTLC is dust. -/
theorem trimDust_length_lt_of_dust (dustLimitSat : Nat) {hs : List CommitmentHTLCOutput}
    (hd : ∃ h ∈ hs, isDust dustLimitSat h.amountSat) :
    (trimDust dustLimitSat hs).length < hs.length := by
  have hf : ∃ h ∈ hs, htlcKept dustLimitSat h = false := by
    rcases hd with ⟨h, hh, hdust⟩
    refine ⟨h, hh, ?_⟩
    simp only [htlcKept, isDust] at hdust ⊢
    rw [decide_eq_false_iff_not]
    omega
  exact length_filter_lt_of_exists_false (htlcKept dustLimitSat) hf

/-- A filtered HTLC list has no larger total value than the raw list. -/
theorem htlcOutputsValue_filter_le (dustLimitSat : Nat)
    (hs : List CommitmentHTLCOutput) :
    htlcOutputsValue (hs.filter (htlcKept dustLimitSat)) ≤
      htlcOutputsValue hs := by
  induction hs with
  | nil => simp [htlcOutputsValue]
  | cons h t ih =>
      by_cases hk : htlcKept dustLimitSat h = true
      · rw [List.filter_cons_of_pos hk]
        simp only [htlcOutputsValue]
        omega
      · rw [List.filter_cons_of_neg hk]
        simp only [htlcOutputsValue]
        omega

/-- The HTLC value of a trimmed list is at most the value of the raw list. -/
theorem htlcOutputsValue_trimDust_le (dustLimitSat : Nat)
    (hs : List CommitmentHTLCOutput) :
    htlcOutputsValue (trimDust dustLimitSat hs) ≤ htlcOutputsValue hs :=
  htlcOutputsValue_filter_le dustLimitSat hs

/-- The trimmed commitment record. -/
def Commitment.trimmed (c : Commitment) (dustLimitSat : Nat) : Commitment :=
  { c with htlcs := trimDust dustLimitSat c.htlcs }

theorem Commitment.trimmed_htlcs (c : Commitment) (dustLimitSat : Nat) :
    (Commitment.trimmed c dustLimitSat).htlcs =
      trimDust dustLimitSat c.htlcs := rfl

theorem Commitment.trimmed_weight_le (c : Commitment) (dustLimitSat : Nat) :
    (Commitment.trimmed c dustLimitSat).weight.val ≤ c.weight.val := by
  unfold Commitment.trimmed Commitment.weight
  exact commitmentWeight_mono_htlcs c.anchorOutputs
    (trimDust_length_le dustLimitSat c.htlcs)

theorem Commitment.trimmed_commitmentFee_le (r : FeeRate) (c : Commitment)
    (dustLimitSat : Nat) :
    (commitmentFee r (Commitment.trimmed c dustLimitSat)).val ≤
      (commitmentFee r c).val := by
  unfold commitmentFee
  exact feeForWeight_mono_weight r (Commitment.trimmed_weight_le c dustLimitSat)

theorem Commitment.trimmed_totalOutputValue_le (c : Commitment)
    (dustLimitSat : Nat) :
    (Commitment.trimmed c dustLimitSat).totalOutputValue ≤
      c.totalOutputValue := by
  unfold Commitment.trimmed Commitment.totalOutputValue
    Commitment.htlcOutputValue Commitment.anchorOutputValue
  have h := htlcOutputsValue_trimDust_le dustLimitSat c.htlcs
  by_cases ha : c.anchorOutputs <;> simp [ha] <;> omega

theorem Commitment.trimmed_dust_free (c : Commitment) (dustLimitSat : Nat) :
    ∀ h ∈ (Commitment.trimmed c dustLimitSat).htlcs,
      ¬ isDust dustLimitSat h.amountSat := by
  intro h hh
  exact (mem_trimDust.mp hh).2

theorem Commitment.trimmed_length_lt_of_dust (c : Commitment)
    (dustLimitSat : Nat)
    (hd : ∃ h ∈ c.htlcs, isDust dustLimitSat h.amountSat) :
    (Commitment.trimmed c dustLimitSat).htlcs.length < c.htlcs.length := by
  exact trimDust_length_lt_of_dust dustLimitSat hd

theorem Commitment.trimmed_weight_lt_of_dust (c : Commitment)
    (dustLimitSat : Nat)
    (hd : ∃ h ∈ c.htlcs, isDust dustLimitSat h.amountSat) :
    (Commitment.trimmed c dustLimitSat).weight.val < c.weight.val := by
  have hlen := trimDust_length_lt_of_dust dustLimitSat hd
  unfold Commitment.trimmed Commitment.weight
  exact commitmentWeight_lt_of_lt c.anchorOutputs hlen

/-- Fee coverage survives trimming: the required fee of the trimmed
commitment is no larger than that of the original. -/
theorem feeCoversWeight_trimmed (r : FeeRate) (c : Commitment)
    (dustLimitSat : Nat) (h : FeeCoversWeight r c) :
    FeeCoversWeight r (Commitment.trimmed c dustLimitSat) :=
  feeCoversWeight_of_weight_le (r := r) (c := Commitment.trimmed c dustLimitSat)
    (c' := c) rfl (Commitment.trimmed_weight_le c dustLimitSat) h

/-- Trimming dust lowers the weight, the required fee, and the total output
value, and leaves only non-dust HTLCs. -/
theorem commitment_trim_bounds (r : FeeRate) (dustLimitSat : Nat)
    (c : Commitment) :
    (Commitment.trimmed c dustLimitSat).weight.val ≤ c.weight.val ∧
      (commitmentFee r (Commitment.trimmed c dustLimitSat)).val ≤
        (commitmentFee r c).val ∧
      (Commitment.trimmed c dustLimitSat).totalOutputValue ≤
        c.totalOutputValue ∧
      (∀ h ∈ (Commitment.trimmed c dustLimitSat).htlcs,
        ¬ isDust dustLimitSat h.amountSat) :=
  ⟨Commitment.trimmed_weight_le c dustLimitSat,
    Commitment.trimmed_commitmentFee_le r c dustLimitSat,
    Commitment.trimmed_totalOutputValue_le c dustLimitSat,
    Commitment.trimmed_dust_free c dustLimitSat⟩

/-! ## Output-value bounds -/

theorem value_le_outputsValue (l : List CommitmentOutput)
    (o : CommitmentOutput) (ho : o ∈ l) : o.value ≤ outputsValue l := by
  induction l with
  | nil => simp at ho
  | cons x xs ih =>
      rw [show outputsValue (x :: xs) = x.value + outputsValue xs from rfl]
      rcases List.mem_cons.mp ho with rfl | hmem
      · omega
      · have := ih hmem
        omega

/-- Each emitted output is worth at most the total output value. -/
theorem commitment_output_value_le_totalOutputValue (c : Commitment)
    (o : CommitmentOutput) (ho : o ∈ c.commitmentOutputs) :
    o.value ≤ c.totalOutputValue := by
  have h := value_le_outputsValue c.commitmentOutputs o ho
  rwa [Commitment.outputsValue_commitmentOutputs] at h

/-- Every emitted output value is non-negative.  `CommitmentOutput.value` is
a `Nat`, so this records that no output is truncated or negative. -/
theorem commitment_outputs_nonnegative (c : Commitment) :
    ∀ o ∈ c.commitmentOutputs, 0 ≤ o.value := by
  intro o _
  exact Nat.zero_le _

theorem commitment_totalOutputValue_le_funding (c : Commitment)
    (h : c.totalOutputValue + c.feeSat ≤ c.fundingValueSat) :
    c.totalOutputValue ≤ c.fundingValueSat := by
  omega

/-- Each output value is bounded by the funding value under the value
equation. -/
theorem commitment_output_value_le_funding (c : Commitment)
    (h : c.totalOutputValue + c.feeSat ≤ c.fundingValueSat)
    (o : CommitmentOutput) (ho : o ∈ c.commitmentOutputs) :
    o.value ≤ c.fundingValueSat := by
  have h1 := commitment_output_value_le_totalOutputValue c o ho
  have h2 : c.totalOutputValue ≤ c.fundingValueSat := by omega
  omega

/-- The same bound from the exact conservation equation. -/
theorem commitment_totalOutputValue_le_funding_of_conserves (c : Commitment)
    (h : CommitmentConserves c) :
    c.totalOutputValue ≤ c.fundingValueSat := by
  unfold CommitmentConserves at h
  omega

/-! ## The bundled precondition -/

/-- The exact hypotheses of this module.

* `feeCovers`: the recorded fee covers `feerate_per_kw * weight / 1000` at
  the commitment's own weight.
* `dustTrimmed`: every HTLC still carried is at or above the dust limit
  (a birth certificate for the BOLT 3 trimming step).
* `valueBounded`: outputs plus the fee fit inside the funding value; this is
  what `buildCommitment` produces from its residual `to_remote`. -/
structure CommitmentBudget (r : FeeRate) (dustLimitSat : Nat)
    (c : Commitment) : Prop where
  feeCovers : FeeCoversWeight r c
  dustTrimmed : ∀ h ∈ c.htlcs, ¬ isDust dustLimitSat h.amountSat
  valueBounded : c.totalOutputValue + c.feeSat ≤ c.fundingValueSat

/-- Build a budget from the conservation equation of
`LnLean.Proofs.Channel.FeeProps`. -/
theorem CommitmentBudget.of_conserves (r : FeeRate) (dustLimitSat : Nat)
    (c : Commitment) (hfee : FeeCoversWeight r c)
    (hdust : ∀ h ∈ c.htlcs, ¬ isDust dustLimitSat h.amountSat)
    (hcons : CommitmentConserves c) : CommitmentBudget r dustLimitSat c := by
  refine ⟨hfee, hdust, ?_⟩
  unfold CommitmentConserves at hcons
  omega

/-- Trimming dust preserves a budget. -/
theorem CommitmentBudget.trimmed (r : FeeRate) (dustLimitSat : Nat)
    (c : Commitment) (h : CommitmentBudget r dustLimitSat c) :
    CommitmentBudget r dustLimitSat (Commitment.trimmed c dustLimitSat) := by
  refine ⟨feeCoversWeight_trimmed r c dustLimitSat h.feeCovers,
    Commitment.trimmed_dust_free c dustLimitSat, ?_⟩
  have hle := Commitment.trimmed_totalOutputValue_le c dustLimitSat
  have hb := h.valueBounded
  have hf : (Commitment.trimmed c dustLimitSat).feeSat = c.feeSat := rfl
  have hfv : (Commitment.trimmed c dustLimitSat).fundingValueSat =
    c.fundingValueSat := rfl
  rw [hf, hfv]
  omega

/-- The main composed statement: non-negative output values, the total output
value within the funding value, the exact weight/HTLC-output relation, the
required-fee bound, and the dust precondition. -/
theorem feeWeightDust_bounds (r : FeeRate) (dustLimitSat : Nat)
    (c : Commitment) (h : CommitmentBudget r dustLimitSat c) :
    (∀ o ∈ c.commitmentOutputs, 0 ≤ o.value) ∧
      (∀ o ∈ c.commitmentOutputs, o.value ≤ c.fundingValueSat) ∧
      c.totalOutputValue ≤ c.fundingValueSat ∧
      (commitmentFee r c).val ≤ c.fundingValueSat ∧
      c.weight.val =
        commitmentBaseWeight c.anchorOutputs +
          commitmentHtlcWeight * htlcOutputCount c.commitmentOutputs ∧
      (∀ x ∈ c.htlcs, ¬ isDust dustLimitSat x.amountSat) :=
  ⟨commitment_outputs_nonnegative c,
    fun o ho => commitment_output_value_le_funding c h.valueBounded o ho,
    commitment_totalOutputValue_le_funding c h.valueBounded,
    commitment_requiredFee_le_funding r c h.feeCovers h.valueBounded,
    commitment_weight_eq_base_add_htlcOutputCount c,
    h.dustTrimmed⟩

/-! ## The BOLT 3 residual construction -/

/-- A commitment built from the BOLT 3 residual satisfies the budget whenever
the residual does not underflow and the fee covers the required amount at the
constructed weight. -/
theorem CommitmentBudget.of_buildCommitment
    (holder : Direction) (number funding fee toLocal : Nat)
    (htlcs : List CommitmentHTLCOutput) (contestDelay : Nat) (anchors : Bool)
    (r : FeeRate) (dustLimitSat : Nat)
    (hres : fee + toLocal + htlcOutputsValue htlcs +
      commitmentAnchorTotal anchors ≤ funding)
    (hfee : FeeCoversWeight r
      (buildCommitment holder number funding fee toLocal htlcs contestDelay anchors))
    (hdust : ∀ h ∈ htlcs, ¬ isDust dustLimitSat h.amountSat) :
    CommitmentBudget r dustLimitSat
      (buildCommitment holder number funding fee toLocal htlcs contestDelay anchors) := by
  refine ⟨hfee, hdust, ?_⟩
  have hcons := buildCommitment_conservation holder number funding fee toLocal
    htlcs contestDelay anchors hres
  rw [Commitment.outputsValue_commitmentOutputs] at hcons
  have hfv :
      (buildCommitment holder number funding fee toLocal htlcs contestDelay
        anchors).fundingValueSat = funding := rfl
  have hf :
      (buildCommitment holder number funding fee toLocal htlcs contestDelay
        anchors).feeSat = fee := rfl
  rw [hfv, hf]
  omega

/-- Construction with dust trimming: raw HTLCs are trimmed first, then the
commitment is built from the survivors.  The feerate precondition is stated
on the trimmed weight, exactly as BOLT 3 computes it after trimming. -/
theorem buildCommitment_trimmed_budget
    (holder : Direction) (number funding fee toLocal : Nat)
    (raw : List CommitmentHTLCOutput) (contestDelay : Nat) (anchors : Bool)
    (r : FeeRate) (dustLimitSat : Nat)
    (hres : fee + toLocal +
        htlcOutputsValue (trimDust dustLimitSat raw) +
        commitmentAnchorTotal anchors ≤ funding)
    (hfee : (feeForWeight r
        (commitmentWeight anchors
          (trimDust dustLimitSat raw).length)).val ≤ fee) :
    let c := buildCommitment holder number funding fee toLocal
      (trimDust dustLimitSat raw) contestDelay anchors
    CommitmentBudget r dustLimitSat c := by
  intro c
  refine ⟨?_, ?_, ?_⟩
  · show (feeForWeight r c.weight).val ≤ c.feeSat
    have hw : c.weight =
        commitmentWeight anchors (trimDust dustLimitSat raw).length := rfl
    have hf : c.feeSat = fee := rfl
    rw [hw, hf]
    exact hfee
  · intro h hh
    have hge := trimDust_all_ge dustLimitSat raw h hh
    unfold isDust
    omega
  · have hcons := buildCommitment_conservation holder number funding fee toLocal
      (trimDust dustLimitSat raw) contestDelay anchors hres
    rw [Commitment.outputsValue_commitmentOutputs] at hcons
    have hfv : c.fundingValueSat = funding := rfl
    have hf : c.feeSat = fee := rfl
    rw [hfv, hf]
    change (buildCommitment holder number funding fee toLocal
      (trimDust dustLimitSat raw) contestDelay anchors).totalOutputValue +
        fee ≤ funding
    omega

/-- Direct output-bound corollary of the trimmed construction.  The bounds do
not need the feerate hypothesis: a non-negative fee and the residual value
equation suffice. -/
theorem buildCommitment_trimmed_bounds
    (holder : Direction) (number funding fee toLocal : Nat)
    (raw : List CommitmentHTLCOutput) (contestDelay : Nat) (anchors : Bool)
    (dustLimitSat : Nat)
    (hres : fee + toLocal +
        htlcOutputsValue (trimDust dustLimitSat raw) +
        commitmentAnchorTotal anchors ≤ funding) :
    let c := buildCommitment holder number funding fee toLocal
      (trimDust dustLimitSat raw) contestDelay anchors
    (∀ o ∈ c.commitmentOutputs, 0 ≤ o.value) ∧
      (∀ o ∈ c.commitmentOutputs, o.value ≤ funding) ∧
      c.totalOutputValue ≤ funding := by
  intro c
  have hcons := buildCommitment_conservation holder number funding fee toLocal
    (trimDust dustLimitSat raw) contestDelay anchors hres
  rw [Commitment.outputsValue_commitmentOutputs] at hcons
  have hfv : c.fundingValueSat = funding := rfl
  have hf : c.feeSat = fee := rfl
  have hle : c.totalOutputValue + c.feeSat ≤ c.fundingValueSat := by
    rw [hf, hfv]
    change (buildCommitment holder number funding fee toLocal
      (trimDust dustLimitSat raw) contestDelay anchors).totalOutputValue +
        fee ≤ funding
    omega
  exact ⟨commitment_outputs_nonnegative c,
    fun o ho => by
      have := commitment_output_value_le_funding c hle o ho
      simpa [hfv] using this,
    by
      have := commitment_totalOutputValue_le_funding c hle
      simpa [hfv] using this⟩

/-! ## Bridge to the HTLCRecord dust laws of `LnLean.Channel.HTLCLaws` -/

/-- The HTLCRecord dust test is the `isDust` predicate of
`LnLean.Channel.Fee` applied to `htlcOutputValue`. -/
theorem isDustHTLC_iff_isDust (h : HTLCRecord) (dustLimitSat timeoutFeeSat
    successFeeSat : Nat) :
    isDustHTLC h dustLimitSat timeoutFeeSat successFeeSat = true ↔
      isDust dustLimitSat (htlcOutputValue h timeoutFeeSat successFeeSat) := by
  unfold isDustHTLC isDust
  exact decide_eq_true_iff

/-- A dust HTLC carries a value strictly below the dust limit
(re-exported from `LnLean.Channel.HTLCLaws`). -/
theorem dust_htlc_value_lt (h : HTLCRecord) (dustLimitSat timeoutFeeSat
    successFeeSat : Nat)
    (hd : isDustHTLC h dustLimitSat timeoutFeeSat successFeeSat = true) :
    htlcOutputValue h timeoutFeeSat successFeeSat < dustLimitSat :=
  dust_value_lt h dustLimitSat timeoutFeeSat successFeeSat hd

/-- A surviving HTLC carries at least the dust limit (re-exported from
`LnLean.Channel.HTLCLaws`). -/
theorem nonDust_htlc_value_ge (h : HTLCRecord) (dustLimitSat timeoutFeeSat
    successFeeSat : Nat)
    (hd : isDustHTLC h dustLimitSat timeoutFeeSat successFeeSat = false) :
    dustLimitSat ≤ htlcOutputValue h timeoutFeeSat successFeeSat :=
  nonDust_value_ge h dustLimitSat timeoutFeeSat successFeeSat hd

/-- A dust HTLC has no commitment output (re-exported from
`LnLean.Channel.HTLCLaws`); this is the trimming step that `trimDust`
implements at the `CommitmentHTLCOutput` level. -/
theorem dust_htlc_no_output (h : HTLCRecord) (dustLimitSat timeoutFeeSat
    successFeeSat : Nat)
    (hd : isDustHTLC h dustLimitSat timeoutFeeSat successFeeSat = true) :
    hasOutput h dustLimitSat timeoutFeeSat successFeeSat = false :=
  dust_no_output h dustLimitSat timeoutFeeSat successFeeSat hd

end FeeWeightDust

end LnLean.Proofs.PhaseC3
