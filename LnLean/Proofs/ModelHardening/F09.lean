import LnLean.Channel.Commitment
import LnLean.Channel.HTLC
import LnLean.Channel.Fee
import LnLean.Channel.Types

/-!
# Wave F / F09 — Dust trimming and fee accounting

Parent obligation: `LN-CH-DUST`.

BOLT 3 §2 (`Trimmed Outputs`, `03-transactions.md:305-354`) says that an
output whose value is below the owner's `dust_limit_satoshis` is not
created, and that the value of the trimmed output is added to the
commitment transaction fee.  This module makes that accounting link
explicit for the model.

What the model already has:

* `Commitment.commitmentOutputs` (`LnLean.Channel.Commitment`) removes a
  `to_local`/`to_remote` output exactly when its value is zero.  It does
  **not** consult `dustLimitSat`, so its trimming is byte-for-byte the
  dust rule with limit 1 (`F09.trimmedValue 1`).
* `Commitment.totalOutputValue` sums the record's fields, and
  `Commitment.feeSat` is an independent field.  No constructor, transition,
  or `commitmentOutputs` case adds a trimmed value to `feeSat`.

The gap this file exposes: if the real dust limit is applied to the
candidate outputs, `Commitment.feeSat` is short by exactly the dropped
value.  The reusable repair is the predicate `dustFeeAccounted`, and the
main theorem is conditional on it.  The unconditional (false) form is kept
below with one `sorry` and a mechanized counterexample.

BOLT anchors: `refs/bolts/03-transactions.md:305-354` (trimmed outputs and
"the value of the output is added to the fee"), `:464-576` (fee
calculation), `:583-620` (dust limits).

What is NOT modelled here: the exact second-stage HTLC fee and the net
`amount - htlc_fee < dust_limit` test live in the HTLC workstream
(`isDustHTLC`); this module works at the commitment-output value level.
-/

namespace LnLean.Proofs.ModelHardening.F09

open LnLean
open LnLean.Channel

set_option autoImplicit false

/-! ## Output-list value -/

/-- Total satoshi value of a list of commitment outputs. -/
def outputValue : List CommitmentOutput → Nat
  | [] => 0
  | o :: t => o.value + outputValue t

theorem outputValue_append (l₁ l₂ : List CommitmentOutput) :
    outputValue (l₁ ++ l₂) = outputValue l₁ + outputValue l₂ := by
  induction l₁ with
  | nil => simp [outputValue]
  | cons o t ih => simp [outputValue, ih, Nat.add_assoc]

/-- The HTLC outputs contribute exactly `Commitment.htlcOutputValue`. -/
theorem outputValue_htlc_map (c : Commitment) :
    outputValue (c.htlcs.map (fun h => CommitmentOutput.htlc h.direction h.amountSat)) =
      c.htlcOutputValue := by
  unfold Commitment.htlcOutputValue htlcOutputsValue
  induction c.htlcs with
  | nil => rfl
  | cons h t ih =>
      simp only [List.map, outputValue, CommitmentOutput.value, ih]
      cases t <;> rfl

/-! ## Candidate outputs before dust trimming -/

/-- The outputs of a commitment before the dust limit is applied: the two
non-HTLC outputs and one output per HTLC record.  Zero-valued entries are
kept here on purpose; they contribute zero to every sum and the trimming
predicates below are the only place that removes them.  Anchors are handled
separately because BOLT 3 adds them at the fixed 330 satoshis. -/
def candidateOutputs (c : Commitment) : List CommitmentOutput :=
  [CommitmentOutput.toLocal c.toLocalSat,
   CommitmentOutput.toRemote c.toRemoteSat] ++
    c.htlcs.map (fun h => CommitmentOutput.htlc h.direction h.amountSat)

/-- Total value of the candidate outputs. -/
def candidateValue (c : Commitment) : Nat :=
  outputValue (candidateOutputs c)

/-- Candidate value in terms of the model's own fields. -/
theorem candidateValue_eq (c : Commitment) :
    candidateValue c = c.toLocalSat + c.toRemoteSat + c.htlcOutputValue := by
  unfold candidateValue candidateOutputs
  rw [outputValue_append]
  simp [outputValue, outputValue_htlc_map, CommitmentOutput.value]

/-- The anchor part of a commitment: two 330-sat outputs. -/
def anchorValue (c : Commitment) : Nat :=
  if c.anchorOutputs then 2 * anchorOutputSat else 0

/-- `Commitment.totalOutputValue` is the candidate value plus the anchors. -/
theorem totalOutputValue_eq_candidateValue_add_anchorValue (c : Commitment) :
    c.totalOutputValue = candidateValue c + anchorValue c := by
  unfold Commitment.totalOutputValue Commitment.anchorOutputValue anchorValue
  rw [candidateValue_eq]

/-! ## Dust trimming -/

/-- Keep an output exactly when its value is at least the dust limit.
Equality with the limit is not dust (BOLT 3 uses a strict inequality). -/
def keepOutput (dust : Nat) (o : CommitmentOutput) : Option CommitmentOutput :=
  if o.value < dust then none else some o

/-- Record an output as trimmed exactly when its value is below the dust
limit.  Trimmed outputs are not silently discarded: they are the bucket that
must be credited to the fee. -/
def dropDustOutput (dust : Nat) (o : CommitmentOutput) : Option CommitmentOutput :=
  if o.value < dust then some o else none

/-- The commitment outputs that survive the dust limit. -/
def dustOutputs (dust : Nat) (c : Commitment) : List CommitmentOutput :=
  (candidateOutputs c).filterMap (keepOutput dust)

/-- The outputs removed by the dust limit; their value is what must move to
the fee. -/
def dustDroppedOutputs (dust : Nat) (c : Commitment) : List CommitmentOutput :=
  (candidateOutputs c).filterMap (dropDustOutput dust)

/-- Value of the kept (non-dust) outputs. -/
def trimmedValue (dust : Nat) (c : Commitment) : Nat :=
  outputValue (dustOutputs dust c)

/-- Value of the trimmed-away outputs: the size of the missing fee credit. -/
def droppedValue (dust : Nat) (c : Commitment) : Nat :=
  outputValue (dustDroppedOutputs dust c)

theorem mem_dustOutputs {dust : Nat} {c : Commitment} {o : CommitmentOutput} :
    o ∈ dustOutputs dust c ↔ o ∈ candidateOutputs c ∧ ¬ o.value < dust := by
  unfold dustOutputs
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨a, ha, hk⟩
    unfold keepOutput at hk
    split at hk
    · simp at hk
    · rename_i hge
      simp only [Option.some.injEq] at hk
      subst hk
      exact ⟨ha, hge⟩
  · rintro ⟨ha, hge⟩
    exact ⟨o, ha, by simp [keepOutput, hge]⟩

theorem mem_dustDroppedOutputs {dust : Nat} {c : Commitment}
    {o : CommitmentOutput} :
    o ∈ dustDroppedOutputs dust c ↔
      o ∈ candidateOutputs c ∧ o.value < dust := by
  unfold dustDroppedOutputs
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨a, ha, hk⟩
    unfold dropDustOutput at hk
    split at hk
    · rename_i hlt
      simp only [Option.some.injEq] at hk
      subst hk
      exact ⟨ha, hlt⟩
    · simp at hk
  · rintro ⟨ha, hlt⟩
    exact ⟨o, ha, by simp [dropDustOutput, hlt]⟩

/-- A kept output is never dust. -/
theorem dustOutputs_not_dust (dust : Nat) (c : Commitment) :
    ∀ o, o ∈ dustOutputs dust c → ¬ o.value < dust := by
  intro o ho
  exact ((mem_dustOutputs (dust := dust) (c := c) (o := o)).1 ho).2

/-- Every dropped output is strictly below the dust limit. -/
theorem dustDroppedOutputs_are_dust (dust : Nat) (c : Commitment) :
    ∀ o, o ∈ dustDroppedOutputs dust c → o.value < dust := by
  intro o ho
  exact ((mem_dustDroppedOutputs (dust := dust) (c := c) (o := o)).1 ho).2

/-- Every candidate output is either kept or recorded as trimmed. -/
theorem candidateOutputs_kept_or_dropped (dust : Nat) (c : Commitment) :
    ∀ o, o ∈ candidateOutputs c →
      o ∈ dustOutputs dust c ∨ o ∈ dustDroppedOutputs dust c := by
  intro o ho
  by_cases h : o.value < dust
  · exact Or.inr ((mem_dustDroppedOutputs (dust := dust) (c := c) (o := o)).2 ⟨ho, h⟩)
  · exact Or.inl ((mem_dustOutputs (dust := dust) (c := c) (o := o)).2 ⟨ho, h⟩)

/-! ## Trimming cannot increase output value -/

/-- Kept plus dropped value is exactly the pre-trim value: dust trimming
moves value, it does not create or destroy it at the output-list level. -/
theorem outputValue_filterMap_keep_drop (dust : Nat) :
    ∀ l : List CommitmentOutput,
      outputValue (l.filterMap (keepOutput dust)) +
        outputValue (l.filterMap (dropDustOutput dust)) = outputValue l := by
  intro l
  induction l with
  | nil => rfl
  | cons o t ih =>
      by_cases h : o.value < dust
      · simp [List.filterMap, keepOutput, dropDustOutput, h, outputValue]
        omega
      · simp [List.filterMap, keepOutput, dropDustOutput, h, outputValue]
        omega

/-- Exact decomposition of the pre-trim value. -/
theorem trimmedValue_add_droppedValue (dust : Nat) (c : Commitment) :
    trimmedValue dust c + droppedValue dust c = candidateValue c := by
  unfold trimmedValue droppedValue candidateValue dustOutputs dustDroppedOutputs
  exact outputValue_filterMap_keep_drop dust (candidateOutputs c)

/-- **Dust trimming cannot increase output value.**  The kept value is at
most the value of the candidate outputs. -/
theorem trimmedValue_le_candidateValue (dust : Nat) (c : Commitment) :
    trimmedValue dust c ≤ candidateValue c := by
  have h := trimmedValue_add_droppedValue dust c
  omega

/-- Trimming is strictly deflationary when it removes a positive value. -/
theorem trimmedValue_lt_candidateValue_of_dropped {dust : Nat} {c : Commitment}
    (h : 0 < droppedValue dust c) :
    trimmedValue dust c < candidateValue c := by
  have hsplit := trimmedValue_add_droppedValue dust c
  omega

/-- A list none of whose elements is dust has zero dropped value. -/
theorem outputValue_filterMap_drop_eq_zero_of_all {dust : Nat}
    (l : List CommitmentOutput)
    (h : ∀ o ∈ l, ¬ o.value < dust) :
    outputValue (l.filterMap (dropDustOutput dust)) = 0 := by
  induction l with
  | nil => rfl
  | cons o t ih =>
      have ho : ¬ o.value < dust := h o (by simp)
      have ht : ∀ x ∈ t, ¬ x.value < dust := fun x hx => h x (by simp [hx])
      have hit : outputValue (t.filterMap (dropDustOutput dust)) = 0 := ih ht
      simp [List.filterMap, dropDustOutput, ho, hit]

/-- If nothing is dust, trimming changes no output value. -/
theorem trimmedValue_eq_candidateValue_of_no_dust {dust : Nat} {c : Commitment}
    (h : ∀ o, o ∈ candidateOutputs c → ¬ o.value < dust) :
    trimmedValue dust c = candidateValue c := by
  have hsplit := trimmedValue_add_droppedValue dust c
  have hzero : droppedValue dust c = 0 := by
    unfold droppedValue dustDroppedOutputs
    exact outputValue_filterMap_drop_eq_zero_of_all (candidateOutputs c) h
  omega

/-! ## The model's zero-trimming is the dust rule with limit 1 -/

/-- Dropping at limit 1 removes only zero-valued outputs, hence contributes
no value. -/
theorem outputValue_filterMap_drop_one (l : List CommitmentOutput) :
    outputValue (l.filterMap (dropDustOutput 1)) = 0 := by
  induction l with
  | nil => rfl
  | cons o t ih =>
      by_cases h : o.value < 1
      · have hv : o.value = 0 := by omega
        simp [List.filterMap, dropDustOutput, outputValue, hv, ih]
      · simp [List.filterMap, dropDustOutput, h, ih]

/-- Dropping at limit 1 removes only zero-valued outputs, hence contributes
no value. -/
theorem droppedValue_one (c : Commitment) : droppedValue 1 c = 0 := by
  unfold droppedValue dustDroppedOutputs
  exact outputValue_filterMap_drop_one (candidateOutputs c)

/-- The model's zero trimming keeps all pre-trim value. -/
theorem trimmedValue_one_eq_candidateValue (c : Commitment) :
    trimmedValue 1 c = candidateValue c := by
  have hsplit := trimmedValue_add_droppedValue 1 c
  have hzero := droppedValue_one c
  omega

/-- Value of a zero-or-singleton `to_local` group. -/
theorem outputValue_toLocal_if (v : Nat) :
    outputValue (if v = 0 then [] else [CommitmentOutput.toLocal v]) = v := by
  by_cases h : v = 0
  · simp [h, outputValue]
  · simp [h, outputValue, CommitmentOutput.value]

/-- Value of a zero-or-singleton `to_remote` group. -/
theorem outputValue_toRemote_if (v : Nat) :
    outputValue (if v = 0 then [] else [CommitmentOutput.toRemote v]) = v := by
  by_cases h : v = 0
  · simp [h, outputValue]
  · simp [h, outputValue, CommitmentOutput.value]

/-- Value of the two 330-satoshi anchor outputs. -/
theorem outputValue_anchors_if (b : Bool) :
    outputValue (if b then [CommitmentOutput.localAnchor, CommitmentOutput.remoteAnchor]
      else []) = (if b then 2 * anchorOutputSat else 0) := by
  cases b <;> simp [outputValue, CommitmentOutput.value, anchorOutputSat]

/-- Value of the model's actual output list, in terms of the record fields. -/
theorem outputValue_commitmentOutputs (c : Commitment) :
    outputValue c.commitmentOutputs =
      c.toLocalSat + c.toRemoteSat + c.htlcOutputValue + c.anchorOutputValue := by
  unfold Commitment.commitmentOutputs Commitment.anchorOutputValue
  simp only [outputValue_append]
  rw [outputValue_htlc_map, outputValue_toLocal_if, outputValue_toRemote_if,
    outputValue_anchors_if]

/-- **The model's zero trimming is value-exact.**  This is the model-level
form of "trimming cannot increase output value": `commitmentOutputs` removes
only zero-valued `to_local`/`to_remote` outputs, so its value equals
`totalOutputValue`. -/
theorem commitmentOutputs_value_eq_totalOutputValue (c : Commitment) :
    outputValue c.commitmentOutputs = c.totalOutputValue := by
  rw [outputValue_commitmentOutputs]
  rfl

/-- The model's trimming is the dust rule with limit 1, up to the anchor
outputs which are fixed at 330 satoshis each. -/
theorem commitmentOutputs_value_eq_trim_one (c : Commitment) :
    outputValue c.commitmentOutputs = trimmedValue 1 c + anchorValue c := by
  rw [commitmentOutputs_value_eq_totalOutputValue,
    totalOutputValue_eq_candidateValue_add_anchorValue]
  rw [trimmedValue_one_eq_candidateValue]

/-- At the real BOLT 3 dust limit the model's `commitmentOutputs` does not
trim: a 500-sat output below the 546-sat P2WPKH dust limit is still emitted.
This is the structural reason the fee link is missing. -/
theorem model_keeps_subdust_output :
    ∃ c : Commitment,
      isDust DUST_LIMIT_P2WPKH c.toRemoteSat ∧
        CommitmentOutput.toRemote c.toRemoteSat ∈ c.commitmentOutputs := by
  refine ⟨{ holder := .local
            commitmentNumber := 0
            fundingValueSat := 1000
            toLocalSat := 500
            toRemoteSat := 500
            htlcs := []
            feeSat := 0
            contestDelay := 0
            anchorOutputs := false }, ?_, ?_⟩
  · show (500 : Nat) < 546
    decide
  · simp [Commitment.commitmentOutputs]

/-! ## Fee accounting -/

/-- The fee a trimmed commitment must report: the base fee plus all value
removed by the dust limit (BOLT 3 §2 adds trimmed output value to the fee). -/
def requiredFee (dust baseFee : Nat) (c : Commitment) : Nat :=
  baseFee + droppedValue dust c

/-- **The missing accounting predicate.**  The commitment's reported fee is
exactly the required fee: base fee plus the value removed by the dust limit.
BOLT 3 §2 requires this credit; the model's `Commitment.feeSat` is an
independent field, so the predicate must be supplied by whoever constructs or
validates the commitment. -/
def dustFeeAccounted (dust baseFee : Nat) (c : Commitment) : Prop :=
  c.feeSat = requiredFee dust baseFee c

/-- An accounted commitment pays at least the base fee. -/
theorem baseFee_le_fee_of_dustFeeAccounted {dust baseFee : Nat} {c : Commitment}
    (h : dustFeeAccounted dust baseFee c) : baseFee ≤ c.feeSat := by
  unfold dustFeeAccounted requiredFee at h
  omega

/-- Under the credit, the trimmed value is fully paid for: kept outputs plus
the reported fee equal the pre-trim outputs plus the base fee.  This is the
unconditional accounting identity once `dustFeeAccounted` holds. -/
theorem trimmedValue_add_fee_of_dustFeeAccounted {dust baseFee : Nat}
    {c : Commitment} (h : dustFeeAccounted dust baseFee c) :
    trimmedValue dust c + c.feeSat = candidateValue c + baseFee := by
  unfold dustFeeAccounted requiredFee at h
  have hsplit := trimmedValue_add_droppedValue dust c
  omega

/-- **Trimming conserves value exactly when the fee is credited with the
trimmed amount.**  With the required fee `baseFee + droppedValue`, the
post-trim outputs plus fee plus anchors equal the funding value.  This is the
positive accounting theorem; it has no missing hypothesis. -/
theorem conservation_with_requiredFee {dust baseFee : Nat} {c : Commitment}
    (hgross : c.totalOutputValue + baseFee = c.fundingValueSat) :
    trimmedValue dust c + requiredFee dust baseFee c + anchorValue c =
      c.fundingValueSat := by
  unfold requiredFee
  have htot := totalOutputValue_eq_candidateValue_add_anchorValue c
  have hsplit := trimmedValue_add_droppedValue dust c
  omega

/-- **Main conditional theorem: conservation after dust trimming.**  If the
pre-trim commitment conserves value with the base fee and the reported fee
credits every trimmed output, then the trimmed commitment conserves value
with its reported fee.  This is the strongest unconditional-in-the-model
form: both extra hypotheses are explicit. -/
theorem conservation_of_dustFeeAccounted {dust baseFee : Nat} {c : Commitment}
    (hgross : c.totalOutputValue + baseFee = c.fundingValueSat)
    (hacc : dustFeeAccounted dust baseFee c) :
    trimmedValue dust c + c.feeSat + anchorValue c = c.fundingValueSat := by
  have hreq := conservation_with_requiredFee (dust := dust) (baseFee := baseFee) hgross
  unfold dustFeeAccounted at hacc
  omega

/-- **Exact missing link.**  Post-trim conservation holds *iff* the reported
fee includes the value trimmed away.  The forward direction is the model's
gap: conservation silently forces `dustFeeAccounted`, and the model never
establishes it. -/
theorem conservation_iff_dustFeeAccounted {dust baseFee : Nat} {c : Commitment}
    (hgross : c.totalOutputValue + baseFee = c.fundingValueSat) :
    (trimmedValue dust c + c.feeSat + anchorValue c = c.fundingValueSat) ↔
      dustFeeAccounted dust baseFee c := by
  constructor
  · intro hcon
    have hreq := conservation_with_requiredFee (dust := dust) (baseFee := baseFee) hgross
    unfold dustFeeAccounted
    omega
  · intro hacc
    exact conservation_of_dustFeeAccounted hgross hacc

/-! ## The missing link, mechanized -/

/-- A concrete pre-trim commitment that conserves value with a zero base
fee: two 500-sat outputs and 1000 sat of funding. -/
def counterexampleCommitment : Commitment :=
  { holder := .local
    commitmentNumber := 0
    fundingValueSat := 1000
    toLocalSat := 500
    toRemoteSat := 500
    htlcs := []
    feeSat := 0
    contestDelay := 0
    anchorOutputs := false }

theorem counterexample_gross_conservation :
    counterexampleCommitment.totalOutputValue + counterexampleCommitment.feeSat =
      counterexampleCommitment.fundingValueSat := by
  decide

/-- At the 546-sat dust limit both 500-sat outputs are trimmed, but the model
fee stays 0, so the trimmed commitment accounts for none of the 1000 sat. -/
theorem counterexample_trimmed_not_conserved :
    trimmedValue DUST_LIMIT_P2WPKH counterexampleCommitment +
        counterexampleCommitment.feeSat +
        anchorValue counterexampleCommitment ≠
      counterexampleCommitment.fundingValueSat := by
  decide

/-- **The unconditional claim is false.**  Dust trimming alone (with the
commitment's unchanged `feeSat`) does not preserve conservation; the value of
the trimmed outputs must be credited to the fee. -/
theorem dust_trim_preserves_conservation_counterexample :
    ¬ (∀ (dust : Nat) (c : Commitment),
        c.totalOutputValue + c.feeSat = c.fundingValueSat →
          trimmedValue dust c + c.feeSat + anchorValue c = c.fundingValueSat) := by
  intro hall
  exact counterexample_trimmed_not_conserved
    (hall DUST_LIMIT_P2WPKH counterexampleCommitment counterexample_gross_conservation)

/-- **Faithful unconditional claim (false as stated).**  BOLT 3 says the
value of a trimmed output is added to the commitment fee, so one might expect
that applying the dust limit to a conserving commitment preserves the
conservation equation with the commitment's reported `feeSat`.  It does not:
`Commitment.feeSat` is never updated by the model, and
`dust_trim_preserves_conservation_counterexample` is the mechanized
counterexample (two 500-sat outputs at the 546-sat limit).  The corrected
statement is `conservation_of_dustFeeAccounted`, which adds the explicit
credit hypothesis `dustFeeAccounted`. -/
theorem dust_trim_preserves_conservation (dust : Nat) (c : Commitment)
    (hgross : c.totalOutputValue + c.feeSat = c.fundingValueSat) :
    trimmedValue dust c + c.feeSat + anchorValue c = c.fundingValueSat := by
  -- OBLIGATION: LN-WF-F09 the model has no operation that adds the dust
  -- value to `Commitment.feeSat`; the missing bridge is `dustFeeAccounted`.
  sorry

end LnLean.Proofs.ModelHardening.F09
