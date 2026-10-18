/-
# H33 — Anchor witness serialization and the corrected commitment weight (L1-04)

**Catalog issue.** `L1-04` (P1): "Anchor weight has an 8 WU spec/serialization
gap".  `LnLean.Proofs.Bitcoin.WeightTargets` proves
`weightTargetsSerializedWeight true k + 8 = 1124 + 172 * k`, but its witness
weight `224` is an assumed BOLT 3 component size: `Bitcoin.Data.Tx` parses the
witness and does not serialize it, so the witness half of the accounting was
never derived from bytes.

**What this module does.**

1. **Witness serialization model.**  `serWitnessStack` and `serWitnessSection`
   implement the consensus witness serialization: the segwit marker/flag
   (`0x00 0x01`), a CompactSize stack-item count per input, and a CompactSize
   length prefix per stack item.  `bolt3FundingWitness` is BOLT 3's assumed
   2-of-2 funding witness `⟨∅, sig_alice, sig_bob, multi_sig⟩` with 73-byte
   maximum-DER signatures and the 71-byte `multi_sig` script.
2. **The 224 is derived, not assumed.**  `bolt3FundingWitness_size` proves the
   stack serializes to `222` bytes (`1 + (1+0) + (1+73) + (1+73) + (1+71)`)
   and `bolt3WitnessSection_size` proves the full section is `2 + 222 = 224`
   bytes, matching `weightTargetsWitnessWeight` by `rfl`.
3. **The anchor variant does not change the funding witness.**  A commitment
   transaction has exactly one input, the funding input; both
   `to_local_anchor` / `to_remote_anchor` outputs are spent by *child*
   transactions.  `commitment_witness_weight_anchors` proves the witness
   component is `224` with and without `option_anchors`, and the anchor spend
   witnesses (`anchor_owner_spend_witness_size = 75`,
   `anchor_sweep_witness_size = 1`,
   `anchor_witness_script_item_size = 42`) are proved not to enter the
   commitment weight.
4. **The corrected literal weight.**  `commitmentTx_serialized_weight_anchors`
   proves the fully serialized (base + witness) anchor commitment with
   `k` untrimmed HTLC outputs weighs exactly `1116 + 172 * k`, and the
   non-anchor one exactly `724 + 172 * k`.
5. **The retained `+8 WU` gap.**  `anchor_gap_retained` proves
   `1116 + 172*k + 8 = 1124 + 172*k`; `gap_witness_independent` proves that for
   *any* witness weight `w`, `4*223 + w + 8 = 4*225 + w`.  The gap therefore
   cannot be explained by witness bytes at all: it is exactly the two extra
   bytes of Appendix A's `count_tx_out: 3 byte` line (`anchor_gap_is_output_count`).
6. **The literal claim is refuted and the sharp conditional theorem.**
   `anchor_literal_weight_neq_fee_basis` keeps the counterexample
   `1116 + 172*k ≠ 1124 + 172*k`, and `appendixA_eq_fee_basis_iff` proves the
   exact condition: the Appendix A construction equals `1124 + 172*k` iff the
   output-count field is **three** bytes.  For a four-output commitment the
   actual CompactSize count is one byte, so the equality is unreachable;
   `anchor_fee_basis_requires_large_output_count` shows it would need
   `0xfd ≤ 4 + k`, i.e. at least 253 outputs.
7. **The exact BOLT 3 fee-basis interpretation.**  `bolt3FeeMsat` /
   `bolt3FeeSat` are BOLT 3 §4's
   `floor(feerate_per_kw * weight / 1000)`, bridged to the existing
   `LnLean.Proofs.Bitcoin.floorFee` by `bolt3FeeMsat_eq_floorFee`.  BOLT 3's
   base fee is a function of the **negotiated spec constant** `1124`, not of
   the serialized weight, so `bolt3_fee_basis_ge_literal` proves the fee is
   never underpaid and `bolt3_fee_overcharge_le` bounds the overcharge by
   `ceil(8 * feerate / 1000)`.  At BOLT 3's own example feerate of 5000 sat/kw
   the overcharge is exactly `40` satoshis
   (`bolt3_fee_basis_strictly_greater_example`), so the 8 WU gap is
   fee-relevant and cannot be dropped silently.

**Textual basis.** BOLT 3 pinned at `1aadb719b4007c4cea0ba6e36b08c4fb53788dee`:
§4 "Fees" `:464-556` (the expected-weight assumptions at `:487-490`, the
`724`/`1124` fee basis at `:491-498`, the base-fee rule at `:517-524`, the
worked 5000 sat/kw example at `:526-556`) and Appendix A `:973-1086`
(`witness: 222` bytes, `witness_header: 2` bytes,
`commitment_transaction (option_anchors): 225 + 43 * num-htlc-outputs`, and
the `count_tx_out: 3 byte` line).

The BOLT 3 text is internally inconsistent here.  Its fee section assumes
"There are a small number of outputs (thus 1 byte to count them)" (`:489`)
while its anchor Appendix A table says `count_tx_out: 3 byte` (`:1066`).  With
the stated one-byte count the anchor base would be `223` bytes
(`892` non-witness weight) and the total `1116`, not `1124`.  This module keeps
both facts: the fee basis `1124` is the spec's negotiated constant, and the
literal four-output serialization is `1116`.

**Scope.**  The 73-byte signature and 71-byte `multi_sig` lengths are BOLT 3's
maximum-DER / fixed-script assumptions, supplied as explicit size hypotheses;
signature-length variability itself is not modelled.  The model covers
`4 + k < 0xfd` outputs, so the output-count prefix is one byte (the ≥ 253-output
case is handled only through the conditional `appendixA_eq_fee_basis_iff`, and
the ≥ 65536-output five-byte prefix is not modelled).  Untrimmed HTLC outputs
are assumed, as in `WeightTargets`.  No new primitive assumptions are
introduced.

No `sorry`, no `axiom`, no `native_decide`, no `unsafe`.
-/

import LnLean.Proofs.Bitcoin.WeightTargets
import LnLean.Proofs.Bitcoin.WeightProps
import LnLean.Proofs.Bitcoin.ScriptProps

namespace LnLean.Proofs.WaveH.H33

set_option autoImplicit false

open Bitcoin.Data
open LnLean
open LnLean.Proofs.Bitcoin

/-! ## 1. Segwit witness serialization -/

/-- BOLT 3's assumed maximum DER signature length: 73 bytes
(`03-transactions.md:1006`). -/
def maxDerSigBytes : Nat := 73

/-- BOLT 3's `multi_sig` 2-of-2 witness-script length: 71 bytes
(`03-transactions.md:1000`). -/
def fundingWitnessScriptBytes : Nat := 71

/-- The segwit witness header: marker byte `0x00` and flag byte `0x01`
(`03-transactions.md:1038`).  These two bytes are witness, so they cost one
weight unit each. -/
def witnessHeaderBytes : Nat := 2

/-- Consensus serialization of one input's witness stack: a CompactSize item
count, then each item as a CompactSize length followed by its bytes. -/
def serWitnessStack (ws : WitnessStack) : ByteArray :=
  compactSizeEnc ws.length ++
    ws.foldl (fun acc item => acc ++ compactSizeEnc item.size ++ item)
      ByteArray.empty

/-- Consensus serialization of a transaction's witness section.  An empty
witness list serializes to nothing (legacy form); otherwise the section is the
marker/flag header followed by one stack per input. -/
def serWitnessSection (witness : List WitnessStack) : ByteArray :=
  match witness with
  | [] => ByteArray.empty
  | _ =>
      serU8 0x00 ++ serU8 0x01 ++
        witness.foldl (fun acc ws => acc ++ serWitnessStack ws) ByteArray.empty

/-- The BOLT 3 funding-input witness stack: empty element, Alice's signature,
Bob's signature, and the 71-byte `multi_sig` witness script
(`03-transactions.md:1002-1012`). -/
def bolt3FundingWitness (sigA sigB script : ByteArray) : WitnessStack :=
  [ByteArray.empty, sigA, sigB, script]

/-- The commitment witness does not depend on `option_anchors`: the only input
is the funding input, and the anchor outputs are spent by child transactions. -/
def commitmentWitnessStack (_anchors : Bool) (sigA sigB script : ByteArray) :
    WitnessStack :=
  bolt3FundingWitness sigA sigB script

theorem witnessHeaderBytes_eq : witnessHeaderBytes = 2 := rfl

theorem maxDerSigBytes_eq : maxDerSigBytes = 73 := rfl

theorem fundingWitnessScriptBytes_eq : fundingWitnessScriptBytes = 71 := rfl

/-! ## 2. Sizes of the witness components -/

/-- Folding the stack-item serializer adds the per-item serialized sizes. -/
theorem foldl_serWitnessStack_size (init : ByteArray) (ws : WitnessStack) :
    (ws.foldl (fun acc item => acc ++ compactSizeEnc item.size ++ item)
        init).size =
      init.size +
        (ws.map (fun item => (compactSizeEnc item.size).size + item.size)).sum := by
  induction ws generalizing init with
  | nil => simp
  | cons x xs ih =>
      rw [List.foldl_cons, ih]
      simp [ByteArray.size_append, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm]

/-- Exact serialized size of a witness stack: the CompactSize item count plus
each item's CompactSize length prefix and payload. -/
theorem serWitnessStack_size (ws : WitnessStack) :
    (serWitnessStack ws).size =
      (compactSizeEnc ws.length).size +
        (ws.map (fun item => (compactSizeEnc item.size).size + item.size)).sum := by
  simp [serWitnessStack, foldl_serWitnessStack_size]

/-- BOLT 3's funding witness serializes to `222` bytes:
`1 + (1 + 0) + (1 + 73) + (1 + 73) + (1 + 71)`. -/
theorem bolt3FundingWitness_size (sigA sigB script : ByteArray)
    (hA : sigA.size = maxDerSigBytes) (hB : sigB.size = maxDerSigBytes)
    (hS : script.size = fundingWitnessScriptBytes) :
    (serWitnessStack (bolt3FundingWitness sigA sigB script)).size = 222 := by
  rw [serWitnessStack_size]
  simp [bolt3FundingWitness, hA, hB, hS, maxDerSigBytes,
    fundingWitnessScriptBytes, compactSizeEnc, serU8]

/-- The witness section of a one-input transaction is the header plus the
input's stack. -/
theorem serWitnessSection_singleton_size (ws : WitnessStack) :
    (serWitnessSection [ws]).size =
      witnessHeaderBytes + (serWitnessStack ws).size := by
  simp [serWitnessSection, witnessHeaderBytes, serU8, ByteArray.size_append]

/-- **Derived witness weight.**  The BOLT 3 funding witness section serializes
to `224` bytes, so the `224` in `WeightTargets` is a theorem, not an
assumption. -/
theorem bolt3WitnessSection_size (sigA sigB script : ByteArray)
    (hA : sigA.size = maxDerSigBytes) (hB : sigB.size = maxDerSigBytes)
    (hS : script.size = fundingWitnessScriptBytes) :
    (serWitnessSection [bolt3FundingWitness sigA sigB script]).size = 224 := by
  rw [serWitnessSection_singleton_size,
    bolt3FundingWitness_size sigA sigB script hA hB hS]
  rfl

/-- The derived witness size is exactly the constant used by
`WeightTargets`. -/
theorem bolt3WitnessSection_size_eq_targets (sigA sigB script : ByteArray)
    (hA : sigA.size = maxDerSigBytes) (hB : sigB.size = maxDerSigBytes)
    (hS : script.size = fundingWitnessScriptBytes) :
    (serWitnessSection [bolt3FundingWitness sigA sigB script]).size =
      weightTargetsWitnessWeight := by
  rw [bolt3WitnessSection_size sigA sigB script hA hB hS]
  rfl

/-- BOLT 3's witness accounting, component by component: the `2`-byte
marker/flag header plus the `222`-byte funding witness is the `224` weight
units assumed by `WeightTargets`. -/
theorem bolt3_witness_weight_decomposition :
    witnessHeaderBytes + 222 = weightTargetsWitnessWeight := rfl

/-- The commitment witness weight is `224` with `option_anchors`. -/
theorem commitment_witness_weight_anchors (sigA sigB script : ByteArray)
    (hA : sigA.size = maxDerSigBytes) (hB : sigB.size = maxDerSigBytes)
    (hS : script.size = fundingWitnessScriptBytes) :
    (serWitnessSection
        [commitmentWitnessStack true sigA sigB script]).size = 224 :=
  bolt3WitnessSection_size sigA sigB script hA hB hS

/-- The commitment witness weight is `224` without `option_anchors`. -/
theorem commitment_witness_weight_noAnchors (sigA sigB script : ByteArray)
    (hA : sigA.size = maxDerSigBytes) (hB : sigB.size = maxDerSigBytes)
    (hS : script.size = fundingWitnessScriptBytes) :
    (serWitnessSection
        [commitmentWitnessStack false sigA sigB script]).size = 224 :=
  bolt3WitnessSection_size sigA sigB script hA hB hS

/-- The two negotiated variants have the *same* commitment witness bytes. -/
theorem commitmentWitnessStack_anchors_independent (a b : Bool)
    (sigA sigB script : ByteArray) :
    commitmentWitnessStack a sigA sigB script =
      commitmentWitnessStack b sigA sigB script := rfl

/-! ## 3. Anchor spend witnesses are outside the commitment transaction -/

/-- Owner spend of an anchor output: a single signature item. -/
def anchorOwnerSpendWitness (sig : ByteArray) : WitnessStack := [sig]

/-- Anyone-can-spend sweep of an anchor after 16 blocks: an empty witness. -/
def anchorSweepWitness : WitnessStack := []

/-- The owner anchor-spend witness serializes to `1 + (1 + 73) = 75` bytes. -/
theorem anchor_owner_spend_witness_size (sig : ByteArray)
    (h : sig.size = maxDerSigBytes) :
    (serWitnessStack (anchorOwnerSpendWitness sig)).size = 75 := by
  rw [serWitnessStack_size]
  simp [anchorOwnerSpendWitness, maxDerSigBytes] at h ⊢
  rw [h]
  simp [compactSizeEnc, serU8]

/-- The anyone-can-spend anchor sweep witness serializes to `1` byte. -/
theorem anchor_sweep_witness_size :
    (serWitnessStack anchorSweepWitness).size = 1 := by
  simp [anchorSweepWitness, serWitnessStack, compactSizeEnc, serU8]

/-- The 40-byte keyed-anchor witness script becomes a `1 + (1 + 40) = 42`-byte
witness item. -/
theorem anchor_witness_script_item_size (fundingKey : PubKey)
    (h : fundingKey.bytes.size = 33) :
    (serWitnessStack
        [(LnLean.Bitcoin.anchorWitnessScript fundingKey).bytes]).size = 42 := by
  have hscript :
      (LnLean.Bitcoin.anchorWitnessScript fundingKey).bytes.size = 40 :=
    LnLean.Proofs.Bitcoin.ScriptProps.anchorWitnessScript_size_40 fundingKey h
  rw [serWitnessStack_size]
  simp [hscript, compactSizeEnc, serU8]

/-- An anchor spend witness is a one-item stack, so it is never the four-item
commitment funding witness.  Child-transaction anchor witnesses therefore
cannot appear in the commitment transaction's witness section. -/
theorem anchor_spend_witness_not_commitment_witness (sig sigA sigB script :
    ByteArray) :
    anchorOwnerSpendWitness sig ≠ bolt3FundingWitness sigA sigB script := by
  intro h
  have hlen := congrArg List.length h
  simp [anchorOwnerSpendWitness, bolt3FundingWitness] at hlen

/-- The commitment witness section is literally the same byte string in both
negotiated variants; `option_anchors` changes outputs, never the funding
witness. -/
theorem commitment_witness_section_anchors_independent (a b : Bool)
    (sigA sigB script : ByteArray) :
    serWitnessSection [commitmentWitnessStack a sigA sigB script] =
      serWitnessSection [commitmentWitnessStack b sigA sigB script] := rfl

/-! ## 4. The fully serialized commitment transaction -/

/-- Attach the BOLT 3 funding witness to a transaction. -/
def withFundingWitness (tx : Tx) (sigA sigB script : ByteArray) : Tx :=
  { tx with witness := [bolt3FundingWitness sigA sigB script] }

/-- The base serializer ignores the witness, so attaching the funding witness
does not change the txid-relevant bytes. -/
theorem serTx_withFundingWitness (tx : Tx) (sigA sigB script : ByteArray) :
    serTx (withFundingWitness tx sigA sigB script) = serTx tx := rfl

/-- The commitment transaction attached to a funding witness has exactly one
input and one witness stack, the funding stack. -/
theorem withFundingWitness_witness_lists_inputs (tx : Tx)
    (sigA sigB script : ByteArray) :
    (withFundingWitness tx sigA sigB script).witness =
        [bolt3FundingWitness sigA sigB script] ∧
      (withFundingWitness tx sigA sigB script).witness.length = 1 := by
  exact ⟨rfl, rfl⟩

/-- The witness section of a transaction carrying the BOLT 3 funding witness
is `224` bytes. -/
theorem withFundingWitness_witnessSection_size (tx : Tx)
    (sigA sigB script : ByteArray) (hA : sigA.size = maxDerSigBytes)
    (hB : sigB.size = maxDerSigBytes)
    (hS : script.size = fundingWitnessScriptBytes) :
    (serWitnessSection (withFundingWitness tx sigA sigB script).witness).size =
      224 := by
  simp only [withFundingWitness]
  exact bolt3WitnessSection_size sigA sigB script hA hB hS

/-- Consensus weight: non-witness bytes cost four weight units, witness bytes
cost one. -/
def serializedTxWeight (tx : Tx) : Nat :=
  4 * (serTx tx).size + (serWitnessSection tx.witness).size

/-- Weight expressed from the two serialized components. -/
theorem serializedTxWeight_eq_components (tx : Tx) :
    serializedTxWeight tx =
      4 * (serTx tx).size + (serWitnessSection tx.witness).size := rfl

/-- **Corrected commitment weight, serialized.**  For any untrimmed HTLC output
list with fewer than `253` total outputs, the anchor commitment transaction
with the BOLT 3 funding witness attached weighs `1116 + 172 * k` and the
non-anchor one weighs `724 + 172 * k`.  Both are stated against the existing
`weightTargetsSerializedWeight`, whose witness constant is now derived rather
than assumed. -/
theorem commitmentTx_serialized_weight (anchors : Bool)
    (fundingTxid : ByteArray) (hhash : fundingTxid.size = 32)
    (toLocalValue toRemoteValue : Amount)
    (toLocalWitnessScriptHash remotePaymentKeyHash160
      remoteWitnessScriptHash localAnchorWitnessScriptHash
      remoteAnchorWitnessScriptHash : ByteArray)
    (htlcWitnessScriptHashes : List ByteArray)
    (sigA sigB script : ByteArray)
    (htl : toLocalWitnessScriptHash.size = 32)
    (htr : remotePaymentKeyHash160.size = 20)
    (htrw : remoteWitnessScriptHash.size = 32)
    (hla : localAnchorWitnessScriptHash.size = 32)
    (hra : remoteAnchorWitnessScriptHash.size = 32)
    (hhtlcs : ∀ x ∈ htlcWitnessScriptHashes, x.size = 32)
    (hA : sigA.size = maxDerSigBytes) (hB : sigB.size = maxDerSigBytes)
    (hS : script.size = fundingWitnessScriptBytes)
    (hcount : (weightTargetsBaseTxOuts anchors toLocalValue toRemoteValue
        toLocalWitnessScriptHash remotePaymentKeyHash160
        remoteWitnessScriptHash localAnchorWitnessScriptHash
        remoteAnchorWitnessScriptHash).length
      + htlcWitnessScriptHashes.length < 0xfd) :
    serializedTxWeight
        (withFundingWitness
          (weightTargetsCommitmentTx anchors fundingTxid toLocalValue
            toRemoteValue toLocalWitnessScriptHash remotePaymentKeyHash160
            remoteWitnessScriptHash localAnchorWitnessScriptHash
            remoteAnchorWitnessScriptHash htlcWitnessScriptHashes)
          sigA sigB script) =
      weightTargetsSerializedWeight anchors htlcWitnessScriptHashes.length := by
  unfold serializedTxWeight
  rw [serTx_withFundingWitness]
  rw [weightTargets_commitmentTx_serSize anchors fundingTxid hhash toLocalValue
    toRemoteValue toLocalWitnessScriptHash remotePaymentKeyHash160
    remoteWitnessScriptHash localAnchorWitnessScriptHash
    remoteAnchorWitnessScriptHash htlcWitnessScriptHashes htl htr htrw hla hra
    hhtlcs hcount]
  rw [withFundingWitness_witnessSection_size _ sigA sigB script hA hB hS]
  rfl

/-- **Literal anchor weight.**  The fully serialized anchor commitment with `k`
untrimmed HTLCs weighs `1116 + 172 * k`, eight weight units below BOLT 3's
`1124 + 172 * k` fee basis. -/
theorem commitmentTx_serialized_weight_anchors
    (fundingTxid : ByteArray) (hhash : fundingTxid.size = 32)
    (toLocalValue toRemoteValue : Amount)
    (toLocalWitnessScriptHash remotePaymentKeyHash160
      remoteWitnessScriptHash localAnchorWitnessScriptHash
      remoteAnchorWitnessScriptHash : ByteArray)
    (htlcWitnessScriptHashes : List ByteArray)
    (sigA sigB script : ByteArray)
    (htl : toLocalWitnessScriptHash.size = 32)
    (htr : remotePaymentKeyHash160.size = 20)
    (htrw : remoteWitnessScriptHash.size = 32)
    (hla : localAnchorWitnessScriptHash.size = 32)
    (hra : remoteAnchorWitnessScriptHash.size = 32)
    (hhtlcs : ∀ x ∈ htlcWitnessScriptHashes, x.size = 32)
    (hA : sigA.size = maxDerSigBytes) (hB : sigB.size = maxDerSigBytes)
    (hS : script.size = fundingWitnessScriptBytes)
    (hcount : (weightTargetsBaseTxOuts true toLocalValue toRemoteValue
        toLocalWitnessScriptHash remotePaymentKeyHash160
        remoteWitnessScriptHash localAnchorWitnessScriptHash
        remoteAnchorWitnessScriptHash).length
      + htlcWitnessScriptHashes.length < 0xfd) :
    serializedTxWeight
        (withFundingWitness
          (weightTargetsCommitmentTx true fundingTxid toLocalValue
            toRemoteValue toLocalWitnessScriptHash remotePaymentKeyHash160
            remoteWitnessScriptHash localAnchorWitnessScriptHash
            remoteAnchorWitnessScriptHash htlcWitnessScriptHashes)
          sigA sigB script) =
      1116 + 172 * htlcWitnessScriptHashes.length := by
  rw [commitmentTx_serialized_weight true fundingTxid hhash toLocalValue
    toRemoteValue toLocalWitnessScriptHash remotePaymentKeyHash160
    remoteWitnessScriptHash localAnchorWitnessScriptHash
    remoteAnchorWitnessScriptHash htlcWitnessScriptHashes sigA sigB script
    htl htr htrw hla hra hhtlcs hA hB hS hcount]
  exact weightTargets_serializedWeight_true _

/-- **Literal non-anchor weight.**  The fully serialized non-anchor commitment
weighs exactly BOLT 3's `724 + 172 * k`, so the `+8` gap is anchor-specific. -/
theorem commitmentTx_serialized_weight_noAnchors
    (fundingTxid : ByteArray) (hhash : fundingTxid.size = 32)
    (toLocalValue toRemoteValue : Amount)
    (toLocalWitnessScriptHash remotePaymentKeyHash160
      remoteWitnessScriptHash localAnchorWitnessScriptHash
      remoteAnchorWitnessScriptHash : ByteArray)
    (htlcWitnessScriptHashes : List ByteArray)
    (sigA sigB script : ByteArray)
    (htl : toLocalWitnessScriptHash.size = 32)
    (htr : remotePaymentKeyHash160.size = 20)
    (htrw : remoteWitnessScriptHash.size = 32)
    (hla : localAnchorWitnessScriptHash.size = 32)
    (hra : remoteAnchorWitnessScriptHash.size = 32)
    (hhtlcs : ∀ x ∈ htlcWitnessScriptHashes, x.size = 32)
    (hA : sigA.size = maxDerSigBytes) (hB : sigB.size = maxDerSigBytes)
    (hS : script.size = fundingWitnessScriptBytes)
    (hcount : (weightTargetsBaseTxOuts false toLocalValue toRemoteValue
        toLocalWitnessScriptHash remotePaymentKeyHash160
        remoteWitnessScriptHash localAnchorWitnessScriptHash
        remoteAnchorWitnessScriptHash).length
      + htlcWitnessScriptHashes.length < 0xfd) :
    serializedTxWeight
        (withFundingWitness
          (weightTargetsCommitmentTx false fundingTxid toLocalValue
            toRemoteValue toLocalWitnessScriptHash remotePaymentKeyHash160
            remoteWitnessScriptHash localAnchorWitnessScriptHash
            remoteAnchorWitnessScriptHash htlcWitnessScriptHashes)
          sigA sigB script) =
      724 + 172 * htlcWitnessScriptHashes.length := by
  rw [commitmentTx_serialized_weight false fundingTxid hhash toLocalValue
    toRemoteValue toLocalWitnessScriptHash remotePaymentKeyHash160
    remoteWitnessScriptHash localAnchorWitnessScriptHash
    remoteAnchorWitnessScriptHash htlcWitnessScriptHashes sigA sigB script
    htl htr htrw hla hra hhtlcs hA hB hS hcount]
  exact weightTargets_serializedWeight_false _

/-! ## 5. The retained `+8 WU` gap -/

/-- The literal anchor weight as a function of the untrimmed HTLC count. -/
def anchorLiteralWeight (k : Nat) : Nat := 1116 + 172 * k

/-- BOLT 3's negotiated fee basis (`03-transactions.md:493-494,521`). -/
def boltFeeBasisWeight (anchors : Bool) (k : Nat) : Nat :=
  weightTargetsBoltWeight anchors k

/-- The literal anchor weight is `1116 + 172 * k`. -/
theorem anchorLiteralWeight_eq (k : Nat) :
    anchorLiteralWeight k = 1116 + 172 * k := rfl

/-- The fee basis is `1124 + 172 * k` with anchors. -/
theorem boltFeeBasisWeight_anchors (k : Nat) :
    boltFeeBasisWeight true k = 1124 + 172 * k :=
  weightTargets_boltWeight_true k

/-- The fee basis is `724 + 172 * k` without anchors. -/
theorem boltFeeBasisWeight_noAnchors (k : Nat) :
    boltFeeBasisWeight false k = 724 + 172 * k :=
  weightTargets_boltWeight_false k

/-- **Retained `+8 WU` gap.**  The literal anchor weight plus eight weight
units is exactly BOLT 3's fee basis. -/
theorem anchor_gap_retained (k : Nat) :
    anchorLiteralWeight k + 8 = boltFeeBasisWeight true k := by
  rw [anchorLiteralWeight_eq, boltFeeBasisWeight_anchors]
  omega

/-- The gap is nine weight units minus one: the literal weight is strictly
below the fee basis. -/
theorem anchor_literal_weight_lt_fee_basis (k : Nat) :
    anchorLiteralWeight k < boltFeeBasisWeight true k := by
  rw [anchorLiteralWeight_eq, boltFeeBasisWeight_anchors]
  omega

/-- The anchor weight minus the non-anchor weight is `392`, not BOLT 3's `400`:
`400 - 8`.  The missing eight is the same output-count slack. -/
theorem anchor_literal_delta_noAnchors (k : Nat) :
    anchorLiteralWeight k = (724 + 172 * k) + 392 := by
  rw [anchorLiteralWeight_eq]
  omega

/-- **The gap is not witness bytes.**  For *any* witness weight `w`, adding
eight weight units to the `223`-byte anchor base serialization gives the
`225`-byte Appendix A count.  Witness bytes appear identically on both sides. -/
theorem gap_witness_independent (w k : Nat) :
    4 * (weightTargetsSerializedBaseBytes true + 43 * k) + w + 8 =
      4 * (weightTargetsBoltAppendixABytes true + 43 * k) + w := by
  rw [weightTargets_serializedBaseBytes_anchors,
    weightTargets_boltAppendixABytes_anchors]
  omega

/-- **The gap is exactly the two extra `count_tx_out` bytes.**  The
non-witness byte gap is `2`, and at four weight units per byte that is the
`8` weight units of `anchor_gap_retained`. -/
theorem anchor_gap_is_output_count (k : Nat) :
    weightTargetsBoltAppendixABytes true =
        weightTargetsSerializedBaseBytes true + 2 ∧
      weightTargetsBoltAppendixABytes false =
        weightTargetsSerializedBaseBytes false ∧
      4 * (weightTargetsSerializedBaseBytes true + 43 * k) + 224 + 8 =
        4 * (weightTargetsBoltAppendixABytes true + 43 * k) + 224 := by
  refine ⟨weightTargets_anchor_byte_gap, weightTargets_noAnchors_byte_agreement, ?_⟩
  rw [weightTargets_serializedBaseBytes_anchors,
    weightTargets_boltAppendixABytes_anchors]
  omega

/-! ## 6. The counterexample and the sharp conditional theorem -/

/-- **The literal claim is false.**  The anchor weight is never the fee basis;
the eight-weight-unit gap is retained for every HTLC count. -/
theorem anchor_literal_weight_neq_fee_basis (k : Nat) :
    anchorLiteralWeight k ≠ boltFeeBasisWeight true k := by
  rw [anchorLiteralWeight_eq, boltFeeBasisWeight_anchors]
  omega

/-- The universally quantified literal claim is refuted. -/
theorem anchor_literal_weight_claim_refuted :
    ¬ (∀ k : Nat, anchorLiteralWeight k = 1124 + 172 * k) := by
  intro h
  have h0 := h 0
  rw [anchorLiteralWeight_eq] at h0
  omega

/-- The channel layer's `1124 + 172 * k` is the negotiated fee basis, not the
literal serialized weight; the two differ for every `k`. -/
theorem channel_anchor_constant_is_fee_basis (k : Nat) :
    (LnLean.Channel.commitmentWeight true k).val = boltFeeBasisWeight true k ∧
      (LnLean.Channel.commitmentWeight true k).val ≠ anchorLiteralWeight k := by
  refine ⟨?_, ?_⟩
  · rw [LnLean.Channel.commitmentWeight_val, boltFeeBasisWeight_anchors]
    simp [LnLean.Channel.commitmentBaseWeight, LnLean.Channel.commitmentHtlcWeight]
  · have hc : (LnLean.Channel.commitmentWeight true k).val = 1124 + 172 * k := by
      rw [LnLean.Channel.commitmentWeight_val]
      simp [LnLean.Channel.commitmentBaseWeight,
        LnLean.Channel.commitmentHtlcWeight]
    rw [hc, anchorLiteralWeight_eq]
    omega

/-- The Appendix A anchor construction with an explicit output-count width
`countBytes`.  Everything except the count field is fixed. -/
def appendixAWeightWithCountBytes (countBytes k : Nat) : Nat :=
  4 * (weightTargetsFieldBytes + countBytes + weightTargetsBaseOutputBytes true
      + weightTargetsHtlcOutputBytes * k) + weightTargetsWitnessWeight

/-- Closed form: `1112 + 4 * countBytes + 172 * k`. -/
theorem appendixAWeightWithCountBytes_eq (countBytes k : Nat) :
    appendixAWeightWithCountBytes countBytes k =
      1112 + 4 * countBytes + 172 * k := by
  simp [appendixAWeightWithCountBytes, weightTargetsFieldBytes,
    weightTargetsBaseOutputBytes, weightTargetsToLocalOutputBytes,
    weightTargetsToRemoteOutputBytes, weightTargetsAnchorOutputBytes,
    weightTargetsHtlcOutputBytes, weightTargetsWitnessWeight]
  omega

/-- **Sharp conditional theorem.**  The Appendix A anchor construction equals
BOLT 3's `1124 + 172 * k` fee basis **iff** the output-count field occupies
three bytes.  No other field can close the gap. -/
theorem appendixA_eq_fee_basis_iff (countBytes k : Nat) :
    appendixAWeightWithCountBytes countBytes k = boltFeeBasisWeight true k ↔
      countBytes = 3 := by
  rw [appendixAWeightWithCountBytes_eq, boltFeeBasisWeight_anchors]
  omega

/-- The literal one-byte-count weight (`1116 + 172 * k`) is the
`countBytes = 1` instance. -/
theorem appendixA_one_byte_count_eq_literal (k : Nat) :
    appendixAWeightWithCountBytes 1 k = anchorLiteralWeight k := by
  rw [appendixAWeightWithCountBytes_eq, anchorLiteralWeight_eq]

/-- A CompactSize of size `3` carries a value of at least `0xfd`. -/
theorem compactSize_size_three_ge (n : Nat)
    (h : (compactSizeEnc n).size = 3) : 0xfd ≤ n := by
  by_cases hlt : n < 0xfd
  · have h1 : (compactSizeEnc n).size = 1 :=
      weightTargets_compactSizeEnc_size n hlt
    omega
  · omega

/-- For fewer than `0xfd` outputs, the output count is one byte. -/
theorem compactSize_size_one_of_lt (n : Nat) (h : n < 0xfd) :
    (compactSizeEnc n).size = 1 :=
  weightTargets_compactSizeEnc_size n h

/-- **The fee basis is reachable only with at least 253 outputs.**  If the
literal Appendix A weight of a `4 + k`-output anchor commitment equals the
`1124 + 172 * k` fee basis, then the output count must need three bytes, hence
`0xfd ≤ 4 + k`.  A four-output commitment cannot satisfy this. -/
theorem anchor_fee_basis_requires_large_output_count (k : Nat)
    (h : appendixAWeightWithCountBytes (compactSizeEnc (4 + k)).size k =
      boltFeeBasisWeight true k) :
    0xfd ≤ 4 + k := by
  have h3 : (compactSizeEnc (4 + k)).size = 3 :=
    (appendixA_eq_fee_basis_iff (compactSizeEnc (4 + k)).size k).mp h
  exact compactSize_size_three_ge (4 + k) h3

/-- A concrete three-byte count: `253 = 0xfd` needs the `0xfd` form. -/
theorem compactSizeEnc_253_size : (compactSizeEnc 253).size = 3 := by
  decide

/-- Non-vacuity of the conditional: at `k = 249` (253 outputs) the Appendix A
construction really does equal the fee basis. -/
theorem appendixA_matches_basis_at_253_outputs :
    appendixAWeightWithCountBytes (compactSizeEnc (4 + 249)).size 249 =
      boltFeeBasisWeight true 249 := by
  rw [appendixA_eq_fee_basis_iff]
  rw [show 4 + 249 = 253 by omega, compactSizeEnc_253_size]

/-- Conversely, at `k = 0` (a four-output commitment) the count is one byte, so
the literal weight is `1116` and the fee basis is unreachable. -/
theorem anchor_four_outputs_count_one_byte :
    (compactSizeEnc (4 + 0)).size = 1 := by
  rw [show 4 + 0 = 4 by omega]
  exact compactSize_size_one_of_lt 4 (by decide)

/-! ## 7. The exact BOLT 3 fee-basis interpretation -/

/-- BOLT 3 §4's fee in millisatoshis: multiply the weight by
`feerate_per_kw` and divide by 1000, rounding down (`:517-524`). -/
def bolt3FeeMsat (r : FeeRate) (w : Nat) : Nat := r.msatPerKw * w / 1000

/-- BOLT 3's fee in whole satoshis (the model's weight is in weight units and
the feerate in msat/kw, so a second floor by 1000 converts msat to sat). -/
def bolt3FeeSat (r : FeeRate) (w : Nat) : Nat := bolt3FeeMsat r w / 1000

/-- The BOLT 3 fee is exactly the existing `floorFee` at the given weight. -/
theorem bolt3FeeMsat_eq_floorFee (r : FeeRate) (w : Nat) :
    bolt3FeeMsat r w = (floorFee r ⟨w⟩).val := rfl

/-- The BOLT 3 fee is monotone in the weight. -/
theorem bolt3FeeMsat_mono_weight (r : FeeRate) {a b : Nat} (h : a ≤ b) :
    bolt3FeeMsat r a ≤ bolt3FeeMsat r b := by
  unfold bolt3FeeMsat
  exact Nat.div_le_div_right (Nat.mul_le_mul_left r.msatPerKw h)

/-- **Fee-basis interpretation (safety direction).**  BOLT 3 charges the fee on
the negotiated `1124 + 172 * k` basis, which is at least the literal weight, so
the funder never under-pays relative to the serialized transaction. -/
theorem bolt3_fee_basis_ge_literal (r : FeeRate) (k : Nat) :
    bolt3FeeMsat r (anchorLiteralWeight k) ≤
      bolt3FeeMsat r (boltFeeBasisWeight true k) :=
  bolt3FeeMsat_mono_weight r (Nat.le_of_lt (anchor_literal_weight_lt_fee_basis k))

/-- **Overcharge bound.**  The fee difference caused by the eight-weight-unit
gap is at most `ceil(8 * feerate_per_kw / 1000)` millisatoshis. -/
theorem bolt3_fee_overcharge_le (r : FeeRate) (w : Nat) :
    bolt3FeeMsat r (w + 8) ≤
      bolt3FeeMsat r w + (8 * r.msatPerKw + 999) / 1000 := by
  unfold bolt3FeeMsat
  rw [Nat.mul_add]
  rw [Nat.div_le_iff_le_mul_add_pred (by decide : 0 < 1000)]
  generalize hxdef : r.msatPerKw * w = x
  have hx := Nat.div_add_mod x 1000
  have hy := Nat.div_add_mod (8 * r.msatPerKw + 999) 1000
  have hxr : x % 1000 < 1000 := Nat.mod_lt _ (by decide)
  have hyr : (8 * r.msatPerKw + 999) % 1000 < 1000 := Nat.mod_lt _ (by decide)
  omega

/-- The overcharge bound instantiated at the anchor gap: the fee on the
`1124 + 172 * k` basis exceeds the literal fee by at most
`ceil(8 * feerate / 1000)`. -/
theorem bolt3_anchor_overcharge_le (r : FeeRate) (k : Nat) :
    bolt3FeeMsat r (boltFeeBasisWeight true k) ≤
      bolt3FeeMsat r (anchorLiteralWeight k) +
        (8 * r.msatPerKw + 999) / 1000 := by
  rw [anchorLiteralWeight_eq, boltFeeBasisWeight_anchors]
  simpa [show 1116 + 172 * k + 8 = 1124 + 172 * k by omega] using
    bolt3_fee_overcharge_le r (1116 + 172 * k)

/-- At a zero feerate both conventions pay nothing, so the gap is not a fixed
fee discrepancy. -/
theorem bolt3_fee_basis_equal_at_zero_rate (k : Nat) :
    bolt3FeeSat ⟨0⟩ (anchorLiteralWeight k) =
      bolt3FeeSat ⟨0⟩ (boltFeeBasisWeight true k) := by
  simp [bolt3FeeSat, bolt3FeeMsat]

/-- At BOLT 3's worked-example feerate of 5000 sat/kw
(`feerate_per_kw = 5_000_000` msat/kw) the literal zero-HTLC anchor weight pays
`5580` satoshis and the fee basis pays `5620` satoshis. -/
theorem bolt3_example_rate_anchor_fees :
    bolt3FeeSat ⟨5000000⟩ (anchorLiteralWeight 0) = 5580 ∧
      bolt3FeeSat ⟨5000000⟩ (boltFeeBasisWeight true 0) = 5620 := by
  refine ⟨?_, ?_⟩
  · rw [anchorLiteralWeight_eq]
    decide
  · rw [boltFeeBasisWeight_anchors]
    decide

/-- **The 8 WU gap is fee-relevant.**  At the BOLT 3 example feerate the
negotiated fee basis overcharges the literal serialized transaction by exactly
40 satoshis, so the gap cannot be dismissed as weight-only bookkeeping. -/
theorem bolt3_fee_basis_strictly_greater_example :
    bolt3FeeSat ⟨5000000⟩ (anchorLiteralWeight 0) <
      bolt3FeeSat ⟨5000000⟩ (boltFeeBasisWeight true 0) := by
  rw [bolt3_example_rate_anchor_fees.1, bolt3_example_rate_anchor_fees.2]
  decide

/-- There is a feerate at which charging on the fee basis and charging on the
literal weight give different satoshi fees. -/
theorem bolt3_fee_basis_not_literal_fee :
    ∃ r : FeeRate,
      bolt3FeeSat r (anchorLiteralWeight 0) <
        bolt3FeeSat r (boltFeeBasisWeight true 0) :=
  ⟨⟨5000000⟩, bolt3_fee_basis_strictly_greater_example⟩

/-- **The exact interpretation.**  BOLT 3's base fee is computed from the
negotiated spec constant `1124` (the fee basis), which is a strict upper bound
on the four-output anchor serialization; the difference is exactly the two
extra `count_tx_out` bytes and is paid as a safety margin at every feerate. -/
theorem bolt3_fee_basis_interpretation (k : Nat) :
    (LnLean.Channel.commitmentBaseWeight true = 1124) ∧
      (boltFeeBasisWeight true k = 1124 + 172 * k) ∧
      (anchorLiteralWeight k + 8 = boltFeeBasisWeight true k) ∧
      anchorLiteralWeight k < boltFeeBasisWeight true k ∧
      (∀ r : FeeRate,
        bolt3FeeMsat r (anchorLiteralWeight k) ≤
          bolt3FeeMsat r (boltFeeBasisWeight true k)) := by
  refine ⟨rfl, boltFeeBasisWeight_anchors k, anchor_gap_retained k,
    anchor_literal_weight_lt_fee_basis k, ?_⟩
  intro r
  exact bolt3_fee_basis_ge_literal r k

/-! ## 8. Headline bundle -/

/-- **H33 headline target (L1-04).**  The anchor witness is serialized (not
assumed): the funding witness section is `224` bytes in both variants, the
literal anchor commitment weight is `1116 + 172 * k`, the retained gap to the
BOLT 3 fee basis `1124 + 172 * k` is exactly `8` WU, the literal equality claim
is refuted, the equality holds only for a three-byte output count (unreachable
for four outputs), and the fee basis is interpreted as the negotiated
upper-bound fee convention. -/
theorem h33_anchor_weight_target (sigA sigB script : ByteArray)
    (hA : sigA.size = maxDerSigBytes) (hB : sigB.size = maxDerSigBytes)
    (hS : script.size = fundingWitnessScriptBytes) :
    (serWitnessStack (bolt3FundingWitness sigA sigB script)).size = 222 ∧
      (serWitnessSection [bolt3FundingWitness sigA sigB script]).size = 224 ∧
      (serWitnessSection
          [commitmentWitnessStack true sigA sigB script]).size = 224 ∧
      (serWitnessSection
          [commitmentWitnessStack false sigA sigB script]).size = 224 ∧
      (∀ k : Nat, anchorLiteralWeight k + 8 = boltFeeBasisWeight true k) ∧
      (∀ k : Nat, anchorLiteralWeight k ≠ boltFeeBasisWeight true k) ∧
      (∀ countBytes k : Nat,
        appendixAWeightWithCountBytes countBytes k = boltFeeBasisWeight true k ↔
          countBytes = 3) ∧
      (∀ k : Nat, anchorLiteralWeight k < boltFeeBasisWeight true k) := by
  refine ⟨bolt3FundingWitness_size sigA sigB script hA hB hS,
    bolt3WitnessSection_size sigA sigB script hA hB hS,
    commitment_witness_weight_anchors sigA sigB script hA hB hS,
    commitment_witness_weight_noAnchors sigA sigB script hA hB hS,
    anchor_gap_retained, anchor_literal_weight_neq_fee_basis,
    appendixA_eq_fee_basis_iff, anchor_literal_weight_lt_fee_basis⟩

end LnLean.Proofs.WaveH.H33
