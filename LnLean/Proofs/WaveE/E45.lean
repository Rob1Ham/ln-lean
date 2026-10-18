import LnLean.Channel.Commitment
import LnLean.Channel.HTLC
import LnLean.Channel.Types
import LnLean.Proofs.Channel.CommitmentTxProps
import LnLean.Bitcoin.ScriptTemplates

/-!
# E45 — commitment output nonnegativity

**Catalog.** `LN-CH-002` (BOLT 3 §Commitment Transaction Outputs), Lean target
named by the catalog: `LnLean.Channel.Commitment.outputs_nonnegative`.

**What is proved.**

* Every output value emitted by `LnLean.Channel.Commitment.commitmentOutputs`
  is nonnegative, both as a `Nat` and after coercion to `Int`.  This is
  unconditional: the model stores output values in `Nat`
  (`CommitmentOutput.value : CommitmentOutput → Nat`, and the record fields
  `toLocalSat`, `toRemoteSat`, `CommitmentHTLCOutput.amountSat` are `Nat`), so a
  negative output cannot be represented at all.
* The sum of the emitted output values equals `Commitment.totalOutputValue`,
  which connects the nonnegativity statement to the value actually paid by the
  output list (rather than to a separately defined arithmetic expression).
  The sum is therefore nonnegative as well.
* The two anchor outputs are positive (`330` satoshis each).

**Missing assumption exposed.**  The L1-facing script-template representation
`LnLean.Bitcoin.CommitmentOutput` stores `value : BtcAmount` and
`BtcAmount = Bitcoin.Data.Amount = Int`.  For that representation
nonnegativity is *not* structural: `commitmentOutputs` copies
`CommitmentParams.toLocalValue` / `toRemoteValue` unchanged, and those fields
are signed.  The module proves the conditional form
(`0 ≤ p.toLocalValue` and `0 ≤ p.toRemoteValue`) and a mechanized
counterexample showing that the unconditional form is false.  The channel
record itself needs no such hypotheses; the missing invariant belongs to the
signed template layer, not to `LnLean.Channel.Commitment`.

No `sorry` is used.
-/

namespace LnLean.Proofs.WaveE.E45

set_option autoImplicit false

open LnLean
open LnLean.Channel

-- OBLIGATION: LN-WE-E45

/-! ## The channel commitment-output model -/

/-- Every value produced by `CommitmentOutput.value` is nonnegative when read
as a mathematical integer.  The model's field type is `Nat`, so this is a
statement about the encoding rather than about a side condition. -/
theorem waveE_e45_output_value_nonneg (o : CommitmentOutput) :
    0 ≤ (o.value : Int) := by
  cases o <;> simp [CommitmentOutput.value, anchorOutputSat] <;> omega

/-- The same statement in the model's own type: `CommitmentOutput.value` is a
natural number. -/
theorem waveE_e45_output_value_nat_nonneg (o : CommitmentOutput) :
    0 ≤ o.value :=
  Nat.zero_le _

/-- Every output in the list built by `Commitment.commitmentOutputs` has a
nonnegative value.  This is the direct reading of the catalog claim for the
channel commitment model. -/
theorem waveE_e45_commitmentOutputs_value_nonneg (c : Commitment) :
    ∀ o ∈ c.commitmentOutputs, 0 ≤ (o.value : Int) := by
  intro o _
  exact waveE_e45_output_value_nonneg o

/-- The value paid by the emitted output list is exactly
`Commitment.totalOutputValue`.  Zero-valued `to_local`/`to_remote` outputs are
omitted from the list but contribute zero, so the identity has no trimming
side condition. -/
theorem waveE_e45_commitmentOutputs_sum_eq_total (c : Commitment) :
    (c.commitmentOutputs.map CommitmentOutput.value).sum = c.totalOutputValue :=
  Commitment.outputsValue_commitmentOutputs c

/-- The sum of the values of all emitted commitment outputs is nonnegative. -/
theorem waveE_e45_commitmentOutputs_sum_nonneg (c : Commitment) :
    0 ≤ (((c.commitmentOutputs.map CommitmentOutput.value).sum : Nat) : Int) := by
  omega

/-- `Commitment.totalOutputValue` is nonnegative. -/
theorem waveE_e45_totalOutputValue_nonneg (c : Commitment) :
    0 ≤ (c.totalOutputValue : Int) := by
  rw [← waveE_e45_commitmentOutputs_sum_eq_total c]
  omega

/-- The two anchor outputs are strictly positive, not merely nonnegative. -/
theorem waveE_e45_anchor_outputs_pos :
    0 < (CommitmentOutput.localAnchor.value : Int) ∧
      0 < (CommitmentOutput.remoteAnchor.value : Int) := by
  constructor <;> simp [CommitmentOutput.value, anchorOutputSat]

/-! ## The signed L1-facing template model -/

/-- The template model's `to_local` and `to_remote` values are copied from
caller-supplied signed amounts.  Nonnegativity there is conditional on those
amounts being in range; the anchors are fixed at `330`. -/
theorem waveE_e45_script_commitmentOutputs_nonneg
    (p : LnLean.Bitcoin.CommitmentParams)
    (hLocal : 0 ≤ p.toLocalValue) (hRemote : 0 ≤ p.toRemoteValue) :
    ∀ o ∈ LnLean.Bitcoin.commitmentOutputs p, 0 ≤ o.value := by
  intro o ho
  simp only [LnLean.Bitcoin.commitmentOutputs, List.mem_cons,
    List.not_mem_nil, or_false] at ho
  rcases ho with h | h | h | h <;> subst h
  · exact hLocal
  · exact hRemote
  · simp [LnLean.Bitcoin.anchorValue]
  · simp [LnLean.Bitcoin.anchorValue]

/-- Parameters with a negative `to_local` value.  This is well-typed because
the template model's `BtcAmount` is signed, and it is what the missing
nonnegativity/range invariant must exclude. -/
def negativeScriptParams : LnLean.Bitcoin.CommitmentParams where
  revocationKey := ⟨ByteArray.empty⟩
  delayedPaymentKey := ⟨ByteArray.empty⟩
  remotePaymentKey := ⟨ByteArray.empty⟩
  localFundingKey := ⟨ByteArray.empty⟩
  remoteFundingKey := ⟨ByteArray.empty⟩
  toSelfDelay := 0
  toLocalValue := -1
  toRemoteValue := 0
  toLocalWitnessScriptHash := ByteArray.empty
  toRemoteWitnessScriptHash := ByteArray.empty
  localAnchorWitnessScriptHash := ByteArray.empty
  remoteAnchorWitnessScriptHash := ByteArray.empty

/-- The first output of the negative-parameter template list. -/
def negativeScriptOutput : LnLean.Bitcoin.CommitmentOutput where
  kind := .toLocal
  value := -1
  scriptPubKey := LnLean.Bitcoin.toLocalScriptPubKey ByteArray.empty

/-- Mechanized counterexample: in the signed template representation the
unconditional nonnegativity claim is false.  The missing hypothesis is exactly
`0 ≤ CommitmentParams.toLocalValue` (and symmetrically for `toRemoteValue`). -/
theorem waveE_e45_script_outputs_unconditional_false :
    ∃ (p : LnLean.Bitcoin.CommitmentParams)
      (o : LnLean.Bitcoin.CommitmentOutput),
        o ∈ LnLean.Bitcoin.commitmentOutputs p ∧ o.value < 0 := by
  refine ⟨negativeScriptParams, negativeScriptOutput, ?_, ?_⟩
  · simp [negativeScriptOutput, negativeScriptParams,
      LnLean.Bitcoin.commitmentOutputs]
  · simp [negativeScriptOutput]

end LnLean.Proofs.WaveE.E45
