import Bitcoin.Data.Tx
import LnLean.Bitcoin.Seam
import LnLean.Bitcoin.ScriptTemplates
import LnLean.Channel.Commitment

/-!
# LnLean.Proofs.Bitcoin.WeightTargets

English claim (catalog `LN-L1-006`).  The commitment base weight is the BOLT 3
constant `724` before HTLC outputs, and the anchor variant is `1124`.  Each
untrimmed HTLC output adds `172`.

This module ties the two constants in the model

* `LnLean.Bitcoin.commitmentBaseWeight` (the seam's `⟨724⟩`), and
* `LnLean.Channel.commitmentBaseWeight anchors` (`724`/`1124`)

to a commitment-transaction weight model built from BOLT 3 Appendix A's byte
accounting, and, for the non-anchor variant, to the actual base serialization
of a `Bitcoin.Data.Tx` assembled from the model's own script builders.

## The accounting model

BOLT 3 Appendix A
(`refs/bolts/03-transactions.md:973-1086`, pinned commit
`1aadb719b4007c4cea0ba6e36b08c4fb53788dee`) gives:

* `to_local` P2WSH output: `8 + 1 + 34 = 43` bytes,
* `to_remote` P2WPKH output (no anchors): `8 + 1 + 22 = 31` bytes,
* `to_remote` P2WSH output (anchors): `8 + 1 + 34 = 43` bytes,
* each keyed anchor output: `8 + 1 + 34 = 43` bytes,
* each HTLC output: `8 + 1 + 34 = 43` bytes,
* funding input: `41` bytes,
* version `4`, input count `1`, output count `1`, locktime `4`,
* witness weight `2` (marker/flag) `+ 222` (funding-input witness) `= 224`.

Without anchors the non-witness part is therefore
`4 + 1 + 41 + 1 + (43 + 31) + 4 = 125` bytes, so
`4 * 125 + 224 = 724`.  With anchors it is
`4 + 1 + 41 + 3 + (43 + 43 + 43 + 43) + 4 = 225` bytes, so
`4 * 225 + 224 = 1124`.  Every additional untrimmed HTLC output contributes
`43` non-witness bytes, i.e. `4 * 43 = 172` weight units.

## The exact model bridge, and what is missing

`weightTargetsCommitmentTx` assembles a real `Bitcoin.Data.Tx` from the
model's P2WSH/P2WPKH builders and proves its base serialization size for an
arbitrary list of untrimmed HTLC output scripts:

* no anchors: `125 + 43 * k` bytes, hence exactly `724 + 172 * k` weight;
* anchors: `223 + 43 * k` bytes, hence `1116 + 172 * k` weight.

The anchor model serialization is **two bytes smaller** than the `225` in
BOLT 3 Appendix A.  The difference is visible in the pinned BOLT text: the
anchor table lists `count_tx_out: 3 byte`, whereas a four-output transaction
has a one-byte CompactSize output count.  The model deliberately does not
invent two padding bytes; instead it proves the exact gap

`4 * 223 + 224 + 8 = 4 * 225 + 224`, i.e. `1116 + 8 = 1124`.

Consequently `1124` is the BOLT 3 negotiated fee-basis constant (and an upper
bound on the four-output base serialization), not the literal weight of the
serialized four-output anchor transaction.  This is the one missing bridge:
the spec's anchor byte table has a two-byte field that the model's serializer
does not produce.  No claim is made that `1124` is a lower bound on every
anchor commitment record.

The serialization theorem assumes fewer than `253` total outputs, so the
CompactSize output count is one byte.  This covers the usual channel sizes; for
more than roughly 249 untrimmed HTLCs the count prefix grows to three bytes
and BOLT 3's `172`-per-HTLC formula omits the extra two bytes.  That varint
growth is another expected-weight approximation, not modelled here.

The remaining unmodelled pieces are the same as in
`LnLean.Proofs.WaveD.D44`: `Bitcoin.Data.Tx` parses but does not serialize the
witness, so the `224` witness weight is BOLT 3's assumed component size
(two 73-byte maximum-DER signatures plus the 71-byte 2-of-2 witness script);
ECDSA signature length is not modelled; script hashes are parameters with the
standard 32-byte SHA256 / 20-byte HASH160 shapes; and `htlcs` are assumed
already untrimmed.  Dust trimming and the BOLT 3 second-stage fee test are
owned by `LnLean.Channel.Fee` and `LnLean.Proofs.WaveD.D12`.

No `sorry`, no axioms beyond Lean's standard `propext`/`Quot.sound`/
`Classical.choice` (none are used below).
-/

namespace LnLean.Proofs.Bitcoin

set_option autoImplicit false

open Bitcoin.Data
open LnLean

/-! ## BOLT 3 constants and the closed weight formula -/

/-- BOLT 3 base weight before HTLC outputs: `724` without `option_anchors`,
`1124` with it (`03-transactions.md:491-498`). -/
def weightTargetsBaseWeight (anchors : Bool) : Nat :=
  if anchors then 1124 else 724

/-- Weight added by one untrimmed HTLC output: `172` (`4 * 43`). -/
def weightTargetsHtlcWeight : Nat := 172

/-- BOLT 3 expected commitment weight including `numHtlcs` untrimmed HTLC
outputs. -/
def weightTargetsBoltWeight (anchors : Bool) (numHtlcs : Nat) : Nat :=
  weightTargetsBaseWeight anchors + weightTargetsHtlcWeight * numHtlcs

/-- The non-anchor base constant is exactly `724`. -/
theorem commitmentBaseWeight_eq_724 :
    LnLean.Bitcoin.commitmentBaseWeight.val = 724 := rfl

/-- The anchor base constant is exactly `1124`. -/
theorem commitmentBaseWeight_anchors_eq_1124 :
    LnLean.Channel.commitmentBaseWeight true = 1124 :=
  LnLean.Channel.commitmentBaseWeight_anchors

/-- The seam's base constant and the channel layer's non-anchor constant agree
as natural numbers. -/
theorem commitmentBaseWeight_noAnchors_eq_channel :
    LnLean.Bitcoin.commitmentBaseWeight.val =
      LnLean.Channel.commitmentBaseWeight false := rfl

/-- Both base constants, and both closed per-HTLC formulas, in one exact
target.  This is the theorem-shaped replacement for the catalog row's
definition target `LnLean.Bitcoin.commitmentBaseWeight`. -/
theorem commitmentBaseWeight_target :
    LnLean.Bitcoin.commitmentBaseWeight.val = 724 ∧
      LnLean.Channel.commitmentBaseWeight false = 724 ∧
        LnLean.Channel.commitmentBaseWeight true = 1124 ∧
          (∀ n : Nat,
            (LnLean.Channel.commitmentWeight false n).val = 724 + 172 * n) ∧
            (∀ n : Nat,
              (LnLean.Channel.commitmentWeight true n).val = 1124 + 172 * n) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · intro n
    rw [LnLean.Channel.commitmentWeight_val]
    simp [LnLean.Channel.commitmentBaseWeight, LnLean.Channel.commitmentHtlcWeight]
  · intro n
    rw [LnLean.Channel.commitmentWeight_val]
    simp [LnLean.Channel.commitmentBaseWeight, LnLean.Channel.commitmentHtlcWeight]

/-- The BOLT 3 base weight is the zero-HTLC instance of the closed formula. -/
theorem weightTargets_baseWeight_eq_zero_htlcs (anchors : Bool) :
    weightTargetsBaseWeight anchors = weightTargetsBoltWeight anchors 0 := by
  cases anchors <;> rfl

/-- The seam constant is the channel layer's non-anchor zero-HTLC weight. -/
theorem weightTargets_seam_base_eq_zero_htlcs :
    LnLean.Bitcoin.commitmentBaseWeight.val =
      (LnLean.Channel.commitmentWeight false 0).val := by
  simp [LnLean.Channel.commitmentWeight, LnLean.Channel.commitmentBaseWeight,
    LnLean.Bitcoin.commitmentBaseWeight]

/-- With anchors the zero-HTLC channel weight is `1124`. -/
theorem weightTargets_channel_base_anchors :
    (LnLean.Channel.commitmentWeight true 0).val = 1124 := by
  simp [LnLean.Channel.commitmentWeight, LnLean.Channel.commitmentBaseWeight]

/-! ## Appendix A byte accounting -/

/-- Fixed-width field bytes before HTLC outputs, excluding the CompactSize
output count: version `4`, input count `1`, funding input `41`, locktime `4`.
The output count and the output bytes are added separately. -/
def weightTargetsFieldBytes : Nat := 4 + 1 + 41 + 4

/-- `to_local` P2WSH output bytes: value `8` + CompactSize length `1` +
script `34` = `43`. -/
def weightTargetsToLocalOutputBytes : Nat := 43

/-- `to_remote` output bytes: P2WPKH `31` without anchors, P2WSH `43` with
anchors. -/
def weightTargetsToRemoteOutputBytes (anchors : Bool) : Nat :=
  if anchors then 43 else 31

/-- One keyed anchor output: `8 + 1 + 34 = 43` bytes. -/
def weightTargetsAnchorOutputBytes : Nat := 43

/-- One untrimmed HTLC output: `8 + 1 + 34 = 43` bytes. -/
def weightTargetsHtlcOutputBytes : Nat := 43

/-- Base output bytes before HTLC outputs: `to_local`, `to_remote`, and (with
anchors) the two keyed anchors. -/
def weightTargetsBaseOutputBytes (anchors : Bool) : Nat :=
  weightTargetsToLocalOutputBytes + weightTargetsToRemoteOutputBytes anchors
    + (if anchors then 2 * weightTargetsAnchorOutputBytes else 0)

/-- Actual base non-witness serialization size of the model transaction: one
CompactSize output-count byte. -/
def weightTargetsSerializedBaseBytes (anchors : Bool) : Nat :=
  weightTargetsFieldBytes + 1 + weightTargetsBaseOutputBytes anchors

/-- The output-count field as printed in BOLT 3 Appendix A.  The anchor table
says `3 byte` for a four-output transaction; the non-anchor table says
`1 byte`. -/
def weightTargetsBoltCountTxOutBytes (anchors : Bool) : Nat :=
  if anchors then 3 else 1

/-- BOLT 3 Appendix A's non-witness byte count before HTLC outputs. -/
def weightTargetsBoltAppendixABytes (anchors : Bool) : Nat :=
  weightTargetsFieldBytes + weightTargetsBoltCountTxOutBytes anchors
    + weightTargetsBaseOutputBytes anchors

/-- BOLT 3's assumed witness weight: marker/flag `2` plus the `222`-byte
funding-input witness. -/
def weightTargetsWitnessWeight : Nat := 224

/-- Weight computed from the **actual** model serialization: four weight units
per non-witness byte plus the assumed witness weight. -/
def weightTargetsSerializedWeight (anchors : Bool) (numHtlcs : Nat) : Nat :=
  4 * (weightTargetsSerializedBaseBytes anchors
    + weightTargetsHtlcOutputBytes * numHtlcs) + weightTargetsWitnessWeight

/-- Weight computed from BOLT 3 Appendix A's stated byte counts. -/
def weightTargetsAppendixAWeight (anchors : Bool) (numHtlcs : Nat) : Nat :=
  4 * (weightTargetsBoltAppendixABytes anchors
    + weightTargetsHtlcOutputBytes * numHtlcs) + weightTargetsWitnessWeight

/-! ## The arithmetic facts behind the constants -/

/-- Non-anchor base output bytes: `43 + 31 = 74`. -/
theorem weightTargets_baseOutputBytes_noAnchors :
    weightTargetsBaseOutputBytes false = 74 := rfl

/-- Anchor base output bytes: `43 + 43 + 2 * 43 = 172`. -/
theorem weightTargets_baseOutputBytes_anchors :
    weightTargetsBaseOutputBytes true = 172 := rfl

/-- Actual non-anchor base serialization: `4 + 1 + 41 + 1 + 74 + 4 = 125`. -/
theorem weightTargets_serializedBaseBytes_noAnchors :
    weightTargetsSerializedBaseBytes false = 125 := rfl

/-- Actual anchor base serialization: `4 + 1 + 41 + 1 + 172 + 4 = 223`. -/
theorem weightTargets_serializedBaseBytes_anchors :
    weightTargetsSerializedBaseBytes true = 223 := rfl

/-- BOLT 3 Appendix A's non-anchor count: `125` non-witness bytes. -/
theorem weightTargets_boltAppendixABytes_noAnchors :
    weightTargetsBoltAppendixABytes false = 125 := rfl

/-- BOLT 3 Appendix A's anchor count: `225` non-witness bytes. -/
theorem weightTargets_boltAppendixABytes_anchors :
    weightTargetsBoltAppendixABytes true = 225 := rfl

/-- The entire anchor difference in Appendix A is the two-byte output-count
field: `225 = 223 + 2`.  The actual model serializer emits one output-count
byte for four outputs. -/
theorem weightTargets_anchor_byte_gap :
    weightTargetsBoltAppendixABytes true =
      weightTargetsSerializedBaseBytes true + 2 := rfl

/-- Without anchors, Appendix A and the model serializer agree byte-for-byte. -/
theorem weightTargets_noAnchors_byte_agreement :
    weightTargetsBoltAppendixABytes false =
      weightTargetsSerializedBaseBytes false := rfl

/-- The weight computed from Appendix A is exactly the BOLT 3 closed
formula. -/
theorem weightTargets_appendixAWeight_eq_boltWeight (anchors : Bool)
    (numHtlcs : Nat) :
    weightTargetsAppendixAWeight anchors numHtlcs =
      weightTargetsBoltWeight anchors numHtlcs := by
  cases anchors <;>
    simp [weightTargetsAppendixAWeight, weightTargetsBoltWeight,
      weightTargetsBaseWeight, weightTargetsHtlcWeight,
      weightTargetsBoltAppendixABytes, weightTargetsBoltCountTxOutBytes,
      weightTargetsFieldBytes, weightTargetsBaseOutputBytes,
      weightTargetsToLocalOutputBytes, weightTargetsToRemoteOutputBytes,
      weightTargetsAnchorOutputBytes, weightTargetsHtlcOutputBytes,
      weightTargetsWitnessWeight] <;>
    omega

/-- Non-anchor closed formula: `724 + 172 * k`. -/
theorem weightTargets_boltWeight_false (k : Nat) :
    weightTargetsBoltWeight false k = 724 + 172 * k := by
  simp [weightTargetsBoltWeight, weightTargetsBaseWeight,
    weightTargetsHtlcWeight]

/-- Anchor closed formula: `1124 + 172 * k`. -/
theorem weightTargets_boltWeight_true (k : Nat) :
    weightTargetsBoltWeight true k = 1124 + 172 * k := by
  simp [weightTargetsBoltWeight, weightTargetsBaseWeight,
    weightTargetsHtlcWeight]

/-- The BOLT 3 base weight is the zero-HTLC instance of the Appendix A weight
model. -/
theorem weightTargets_baseWeight_eq_appendixA_zero (anchors : Bool) :
    weightTargetsBaseWeight anchors = weightTargetsAppendixAWeight anchors 0 := by
  rw [weightTargets_appendixAWeight_eq_boltWeight]
  exact (weightTargets_baseWeight_eq_zero_htlcs anchors).symm

/-- The seam's `724` is the zero-HTLC Appendix A weight model without
anchors. -/
theorem commitmentBaseWeight_eq_model :
    LnLean.Bitcoin.commitmentBaseWeight.val =
      weightTargetsAppendixAWeight false 0 := by
  change weightTargetsBaseWeight false = weightTargetsAppendixAWeight false 0
  exact weightTargets_baseWeight_eq_appendixA_zero false

/-- The channel layer's `1124` is the zero-HTLC Appendix A weight model with
anchors. -/
theorem commitmentBaseWeight_anchors_eq_model :
    LnLean.Channel.commitmentBaseWeight true =
      weightTargetsAppendixAWeight true 0 := by
  change weightTargetsBaseWeight true = weightTargetsAppendixAWeight true 0
  exact weightTargets_baseWeight_eq_appendixA_zero true

/-- **Model-level target.**  The two BOLT 3 base constants are the zero-HTLC
instances of the commitment-transaction weight model, and the model's per-HTLC
increments are `172` in both variants.  This is the faithful theorem-shaped
replacement for the catalog row's definition target. -/
theorem commitmentBaseWeight_model_target :
    LnLean.Bitcoin.commitmentBaseWeight.val =
        weightTargetsAppendixAWeight false 0 ∧
      LnLean.Channel.commitmentBaseWeight true =
        weightTargetsAppendixAWeight true 0 ∧
      (∀ k : Nat, weightTargetsAppendixAWeight false k = 724 + 172 * k) ∧
      (∀ k : Nat, weightTargetsAppendixAWeight true k = 1124 + 172 * k) := by
  refine ⟨commitmentBaseWeight_eq_model,
    commitmentBaseWeight_anchors_eq_model, ?_, ?_⟩
  · intro k
    rw [weightTargets_appendixAWeight_eq_boltWeight,
      weightTargets_boltWeight_false]
  · intro k
    rw [weightTargets_appendixAWeight_eq_boltWeight,
      weightTargets_boltWeight_true]

/-- Non-anchor actual serialization weight: exactly `724 + 172 * k`. -/
theorem weightTargets_serializedWeight_false (k : Nat) :
    weightTargetsSerializedWeight false k = 724 + 172 * k := by
  simp [weightTargetsSerializedWeight, weightTargetsSerializedBaseBytes,
    weightTargetsFieldBytes, weightTargetsBaseOutputBytes,
    weightTargetsToLocalOutputBytes, weightTargetsToRemoteOutputBytes,
    weightTargetsHtlcOutputBytes, weightTargetsWitnessWeight] <;>
  omega

/-- Anchor actual serialization weight: `1116 + 172 * k`, eight weight units
below the BOLT 3 fee-basis constant. -/
theorem weightTargets_serializedWeight_true (k : Nat) :
    weightTargetsSerializedWeight true k = 1116 + 172 * k := by
  simp [weightTargetsSerializedWeight, weightTargetsSerializedBaseBytes,
    weightTargetsFieldBytes, weightTargetsBaseOutputBytes,
    weightTargetsToLocalOutputBytes, weightTargetsToRemoteOutputBytes,
    weightTargetsAnchorOutputBytes, weightTargetsHtlcOutputBytes,
    weightTargetsWitnessWeight] <;>
  omega

/-- The exact anchor gap: the actual serialization weight plus `8` weight
units (the two-byte BOLT Appendix A output-count difference at four weight
units per byte) is the BOLT 3 `1124` fee basis. -/
theorem weightTargets_serializedWeight_anchor_gap (k : Nat) :
    weightTargetsSerializedWeight true k + 8 =
      weightTargetsBoltWeight true k := by
  rw [weightTargets_serializedWeight_true, weightTargets_boltWeight_true]
  omega

/-- The BOLT 3 anchor constant is an upper bound on the actual four-output
base serialization weight. -/
theorem weightTargets_serializedWeight_true_le_bolt (k : Nat) :
    weightTargetsSerializedWeight true k ≤ weightTargetsBoltWeight true k := by
  rw [weightTargets_serializedWeight_true, weightTargets_boltWeight_true]
  omega

/-- The per-HTLC increment is exactly four weight units per 43-byte output:
`172 = 4 * 43`. -/
theorem weightTargets_htlcWeight_eq_serialized :
    weightTargetsHtlcWeight = 4 * weightTargetsHtlcOutputBytes := rfl

/-- Adding one untrimmed HTLC output adds exactly `172` to the BOLT 3 weight,
for either base variant. -/
theorem weightTargets_boltWeight_succ (anchors : Bool) (k : Nat) :
    weightTargetsBoltWeight anchors (k + 1) =
      weightTargetsBoltWeight anchors k + weightTargetsHtlcWeight := by
  simp [weightTargetsBoltWeight, Nat.mul_succ, Nat.add_assoc]

/-- Adding one untrimmed HTLC output adds exactly `172` to the actual
non-anchor serialization weight. -/
theorem weightTargets_serializedWeight_succ_false (k : Nat) :
    weightTargetsSerializedWeight false (k + 1) =
      weightTargetsSerializedWeight false k + 172 := by
  rw [weightTargets_serializedWeight_false, weightTargets_serializedWeight_false,
    Nat.mul_succ]
  omega

/-! ## Actual transaction serialization model -/

/-- `to_local` P2WSH output. -/
def weightTargetsToLocalTxOut (value : Amount) (witnessScriptHash : ByteArray) :
    TxOut :=
  ⟨value, LnLean.Bitcoin.toLocalScriptPubKey witnessScriptHash⟩

/-- `to_remote` output: P2WPKH without anchors, P2WSH with anchors. -/
def weightTargetsToRemoteTxOut (anchors : Bool) (value : Amount)
    (paymentKeyHash160 witnessScriptHash : ByteArray) : TxOut :=
  if anchors then
    ⟨value, LnLean.Bitcoin.toRemoteScriptPubKey witnessScriptHash⟩
  else
    ⟨value, LnLean.Bitcoin.toRemoteP2WPKHScriptPubKey paymentKeyHash160⟩

/-- A keyed anchor output carrying the BOLT 3 constant `330` satoshis. -/
def weightTargetsAnchorTxOut (witnessScriptHash : ByteArray) : TxOut :=
  ⟨LnLean.Bitcoin.anchorValue,
    LnLean.Bitcoin.anchorScriptPubKey witnessScriptHash⟩

/-- An untrimmed HTLC output, P2WSH over the supplied HTLC witness-script
hash.  The offered/received script distinction does not change the output
size, so one constructor suffices for the weight model. -/
def weightTargetsHtlcTxOut (witnessScriptHash : ByteArray) : TxOut :=
  ⟨0, LnLean.Bitcoin.p2wsh witnessScriptHash⟩

/-- The base outputs of a zero-HTLC commitment, in BOLT 3 Appendix A order:
`to_remote`, `to_local`, then the two keyed anchors when negotiated. -/
def weightTargetsBaseTxOuts (anchors : Bool)
    (toLocalValue toRemoteValue : Amount)
    (toLocalWitnessScriptHash remotePaymentKeyHash160
      remoteWitnessScriptHash localAnchorWitnessScriptHash
      remoteAnchorWitnessScriptHash : ByteArray) : List TxOut :=
  [ weightTargetsToRemoteTxOut anchors toRemoteValue
      remotePaymentKeyHash160 remoteWitnessScriptHash,
    weightTargetsToLocalTxOut toLocalValue toLocalWitnessScriptHash ] ++
    (if anchors then
      [ weightTargetsAnchorTxOut localAnchorWitnessScriptHash,
        weightTargetsAnchorTxOut remoteAnchorWitnessScriptHash ]
    else [])

/-- A commitment transaction assembled from the model's script builders.
`htlcWitnessScriptHashes` are the untrimmed HTLC outputs; the witness is kept
empty because `Bitcoin.Data.Tx` does not serialize it. -/
def weightTargetsCommitmentTx (anchors : Bool) (fundingTxid : ByteArray)
    (toLocalValue toRemoteValue : Amount)
    (toLocalWitnessScriptHash remotePaymentKeyHash160
      remoteWitnessScriptHash localAnchorWitnessScriptHash
      remoteAnchorWitnessScriptHash : ByteArray)
    (htlcWitnessScriptHashes : List ByteArray) : Tx :=
  { version := 2
    vin := [{ prevout := ⟨fundingTxid, 0⟩
              scriptSig := ⟨ByteArray.empty⟩
              sequence := 0 }]
    vout := weightTargetsBaseTxOuts anchors toLocalValue toRemoteValue
        toLocalWitnessScriptHash remotePaymentKeyHash160
        remoteWitnessScriptHash localAnchorWitnessScriptHash
        remoteAnchorWitnessScriptHash
      ++ htlcWitnessScriptHashes.map weightTargetsHtlcTxOut
    locktime := 0
    witness := [] }

/-! ## Size lemmas for the model serializers -/

/-- `serU32` always emits 4 bytes. -/
theorem weightTargets_serU32_size (x : UInt32) : (serU32 x).size = 4 := by
  simp [serU32]

/-- `serU64` always emits 8 bytes. -/
theorem weightTargets_serU64_size (x : UInt64) : (serU64 x).size = 8 := by
  simp [serU64]

/-- A CompactSize below `0xfd` occupies one byte. -/
theorem weightTargets_compactSizeEnc_size (n : Nat) (h : n < 0xfd) :
    (compactSizeEnc n).size = 1 := by
  simp [compactSizeEnc, h, serU8]

/-- A `TxOut` with a 34-byte P2WSH script serializes to 43 bytes. -/
theorem weightTargets_serTxOut_p2wsh_size (value : Amount)
    (witnessScriptHash : ByteArray) (h : witnessScriptHash.size = 32) :
    (serTxOut ⟨value, LnLean.Bitcoin.p2wsh witnessScriptHash⟩).size = 43 := by
  simp [serTxOut, serU64, compactSizeEnc, serU8, LnLean.Bitcoin.p2wsh_size,
    h]

/-- A `TxOut` with a 22-byte P2WPKH script serializes to 31 bytes. -/
theorem weightTargets_serTxOut_p2wpkh_size (value : Amount)
    (paymentKeyHash160 : ByteArray) (h : paymentKeyHash160.size = 20) :
    (serTxOut ⟨value, LnLean.Bitcoin.p2wpkh paymentKeyHash160⟩).size = 31 := by
  simp [serTxOut, serU64, compactSizeEnc, serU8,
    LnLean.Bitcoin.p2wpkh_size, h]

/-- The funding input serializes to 41 bytes. -/
theorem weightTargets_serTxIn_size (fundingTxid : ByteArray)
    (h : fundingTxid.size = 32) :
    (serTxIn { prevout := ⟨fundingTxid, 0⟩
               scriptSig := ⟨ByteArray.empty⟩
               sequence := 0 }).size = 41 := by
  simp [serTxIn, serU32, compactSizeEnc, serU8, h]

/-- Folding the output serializer over a list adds the sum of the individual
serialized sizes. -/
theorem weightTargets_foldl_serTxOut_size (init : ByteArray)
    (outs : List TxOut) :
    (outs.foldl (fun acc o => acc ++ serTxOut o) init).size =
      init.size + (outs.map (fun o => (serTxOut o).size)).sum := by
  induction outs generalizing init with
  | nil => simp
  | cons o rest ih =>
      rw [List.foldl_cons, ih]
      simp [Nat.add_assoc]

/-- Folding the input serializer over a one-element list yields 41 bytes. -/
theorem weightTargets_foldl_serTxIn_size (fundingTxid : ByteArray)
    (h : fundingTxid.size = 32) :
    ([{ prevout := ⟨fundingTxid, 0⟩
        scriptSig := ⟨ByteArray.empty⟩
        sequence := 0 }].foldl
      (fun acc i => acc ++ serTxIn i) ByteArray.empty).size = 41 := by
  simp [weightTargets_serTxIn_size fundingTxid h]

/-- The base output list serializes to exactly the Appendix A output bytes. -/
theorem weightTargets_baseTxOuts_serSum (anchors : Bool)
    (toLocalValue toRemoteValue : Amount)
    (toLocalWitnessScriptHash remotePaymentKeyHash160
      remoteWitnessScriptHash localAnchorWitnessScriptHash
      remoteAnchorWitnessScriptHash : ByteArray)
    (htl : toLocalWitnessScriptHash.size = 32)
    (htr : remotePaymentKeyHash160.size = 20)
    (htrw : remoteWitnessScriptHash.size = 32)
    (hla : localAnchorWitnessScriptHash.size = 32)
    (hra : remoteAnchorWitnessScriptHash.size = 32) :
    ((weightTargetsBaseTxOuts anchors toLocalValue toRemoteValue
        toLocalWitnessScriptHash remotePaymentKeyHash160
        remoteWitnessScriptHash localAnchorWitnessScriptHash
        remoteAnchorWitnessScriptHash).map
      (fun o => (serTxOut o).size)).sum =
      weightTargetsBaseOutputBytes anchors := by
  cases anchors
  · simp [weightTargetsBaseTxOuts, weightTargetsBaseOutputBytes,
      weightTargetsToLocalOutputBytes, weightTargetsToRemoteOutputBytes,
      weightTargetsToLocalTxOut, weightTargetsToRemoteTxOut,
      LnLean.Bitcoin.toLocalScriptPubKey,
      LnLean.Bitcoin.toRemoteP2WPKHScriptPubKey,
      weightTargets_serTxOut_p2wsh_size, weightTargets_serTxOut_p2wpkh_size,
      htl, htr]
  · simp [weightTargetsBaseTxOuts, weightTargetsBaseOutputBytes,
      weightTargetsToLocalOutputBytes, weightTargetsToRemoteOutputBytes,
      weightTargetsAnchorOutputBytes,
      weightTargetsToLocalTxOut, weightTargetsToRemoteTxOut,
      weightTargetsAnchorTxOut,
      LnLean.Bitcoin.toLocalScriptPubKey,
      LnLean.Bitcoin.toRemoteScriptPubKey,
      LnLean.Bitcoin.anchorScriptPubKey,
      weightTargets_serTxOut_p2wsh_size,
      htl, htrw, hla, hra]

/-- The HTLC output list serializes to `43` bytes per output. -/
theorem weightTargets_htlcTxOuts_serSum (hashes : List ByteArray)
    (h : ∀ x ∈ hashes, x.size = 32) :
    ((hashes.map weightTargetsHtlcTxOut).map
      (fun o => (serTxOut o).size)).sum =
      43 * hashes.length := by
  induction hashes with
  | nil => rfl
  | cons x rest ih =>
      have hx : x.size = 32 := h x (by simp)
      have hrest : ∀ y ∈ rest, y.size = 32 := fun y hy => h y (by simp [hy])
      simp only [List.map_cons, List.sum_cons, weightTargetsHtlcTxOut,
        weightTargets_serTxOut_p2wsh_size (0 : Amount) x hx]
      rw [ih hrest]
      simp [Nat.mul_succ]
      omega

/-! ## Exact serialization-size theorem -/

/-- **Base serialization theorem.**  For any untrimmed HTLC output list, the
model's commitment transaction serializes to `125 + 43 * k` bytes without
anchors and `223 + 43 * k` bytes with anchors.  The anchor count is two bytes
below BOLT 3 Appendix A's `225 + 43 * k`; see
`weightTargets_anchor_byte_gap`. -/
theorem weightTargets_commitmentTx_serSize (anchors : Bool)
    (fundingTxid : ByteArray) (hhash : fundingTxid.size = 32)
    (toLocalValue toRemoteValue : Amount)
    (toLocalWitnessScriptHash remotePaymentKeyHash160
      remoteWitnessScriptHash localAnchorWitnessScriptHash
      remoteAnchorWitnessScriptHash : ByteArray)
    (htlcWitnessScriptHashes : List ByteArray)
    (htl : toLocalWitnessScriptHash.size = 32)
    (htr : remotePaymentKeyHash160.size = 20)
    (htrw : remoteWitnessScriptHash.size = 32)
    (hla : localAnchorWitnessScriptHash.size = 32)
    (hra : remoteAnchorWitnessScriptHash.size = 32)
    (hhtlcs : ∀ x ∈ htlcWitnessScriptHashes, x.size = 32)
    (hcount : (weightTargetsBaseTxOuts anchors toLocalValue toRemoteValue
        toLocalWitnessScriptHash remotePaymentKeyHash160
        remoteWitnessScriptHash localAnchorWitnessScriptHash
        remoteAnchorWitnessScriptHash).length
      + htlcWitnessScriptHashes.length < 0xfd) :
    (serTx (weightTargetsCommitmentTx anchors fundingTxid toLocalValue
      toRemoteValue toLocalWitnessScriptHash remotePaymentKeyHash160
      remoteWitnessScriptHash localAnchorWitnessScriptHash
      remoteAnchorWitnessScriptHash htlcWitnessScriptHashes)).size =
      weightTargetsSerializedBaseBytes anchors
        + 43 * htlcWitnessScriptHashes.length := by
  have hbase := weightTargets_baseTxOuts_serSum anchors toLocalValue
    toRemoteValue toLocalWitnessScriptHash remotePaymentKeyHash160
    remoteWitnessScriptHash localAnchorWitnessScriptHash
    remoteAnchorWitnessScriptHash htl htr htrw hla hra
  have hhtlcs := weightTargets_htlcTxOuts_serSum htlcWitnessScriptHashes hhtlcs
  have houtlen :
      (weightTargetsBaseTxOuts anchors toLocalValue toRemoteValue
          toLocalWitnessScriptHash remotePaymentKeyHash160
          remoteWitnessScriptHash localAnchorWitnessScriptHash
          remoteAnchorWitnessScriptHash).length
        + htlcWitnessScriptHashes.length < 0xfd := hcount
  unfold weightTargetsCommitmentTx
  simp only [serTx, List.length_cons, List.length_nil, List.foldl_cons,
    List.foldl_nil, ByteArray.size_append, ByteArray.size_empty]
  rw [weightTargets_foldl_serTxOut_size]
  rw [List.map_append, List.sum_append]
  rw [hbase, hhtlcs]
  rw [weightTargets_serTxIn_size fundingTxid hhash]
  rw [weightTargets_compactSizeEnc_size _ (by omega)]
  rw [weightTargets_serU32_size, weightTargets_serU32_size]
  rw [List.length_append, List.length_map]
  rw [weightTargets_compactSizeEnc_size _ houtlen]
  cases anchors
  · rw [weightTargets_serializedBaseBytes_noAnchors,
      weightTargets_baseOutputBytes_noAnchors]
    simp
    omega
  · rw [weightTargets_serializedBaseBytes_anchors,
      weightTargets_baseOutputBytes_anchors]
    simp
    omega

/-- **Weight theorem from the actual serializer.**  The model transaction's
weight (base serialization times four plus BOLT 3's assumed `224` witness
weight) is `724 + 172 * k` without anchors and `1116 + 172 * k` with
anchors. -/
theorem weightTargets_commitmentTx_weight (anchors : Bool)
    (fundingTxid : ByteArray) (hhash : fundingTxid.size = 32)
    (toLocalValue toRemoteValue : Amount)
    (toLocalWitnessScriptHash remotePaymentKeyHash160
      remoteWitnessScriptHash localAnchorWitnessScriptHash
      remoteAnchorWitnessScriptHash : ByteArray)
    (htlcWitnessScriptHashes : List ByteArray)
    (htl : toLocalWitnessScriptHash.size = 32)
    (htr : remotePaymentKeyHash160.size = 20)
    (htrw : remoteWitnessScriptHash.size = 32)
    (hla : localAnchorWitnessScriptHash.size = 32)
    (hra : remoteAnchorWitnessScriptHash.size = 32)
    (hhtlcs : ∀ x ∈ htlcWitnessScriptHashes, x.size = 32)
    (hcount : (weightTargetsBaseTxOuts anchors toLocalValue toRemoteValue
        toLocalWitnessScriptHash remotePaymentKeyHash160
        remoteWitnessScriptHash localAnchorWitnessScriptHash
        remoteAnchorWitnessScriptHash).length
      + htlcWitnessScriptHashes.length < 0xfd) :
    4 * (serTx (weightTargetsCommitmentTx anchors fundingTxid toLocalValue
      toRemoteValue toLocalWitnessScriptHash remotePaymentKeyHash160
      remoteWitnessScriptHash localAnchorWitnessScriptHash
      remoteAnchorWitnessScriptHash htlcWitnessScriptHashes)).size
        + weightTargetsWitnessWeight =
      weightTargetsSerializedWeight anchors htlcWitnessScriptHashes.length := by
  rw [weightTargets_commitmentTx_serSize anchors fundingTxid hhash toLocalValue
    toRemoteValue toLocalWitnessScriptHash remotePaymentKeyHash160
    remoteWitnessScriptHash localAnchorWitnessScriptHash
    remoteAnchorWitnessScriptHash htlcWitnessScriptHashes htl htr htrw hla hra
    hhtlcs hcount]
  rfl

/-- Non-anchor fully serialized weight: exactly the seam's `724` plus `172`
per untrimmed HTLC output, for any such HTLC script list. -/
theorem weightTargets_commitmentTx_weight_noAnchors
    (fundingTxid : ByteArray) (hhash : fundingTxid.size = 32)
    (toLocalValue toRemoteValue : Amount)
    (toLocalWitnessScriptHash remotePaymentKeyHash160
      remoteWitnessScriptHash localAnchorWitnessScriptHash
      remoteAnchorWitnessScriptHash : ByteArray)
    (htlcWitnessScriptHashes : List ByteArray)
    (htl : toLocalWitnessScriptHash.size = 32)
    (htr : remotePaymentKeyHash160.size = 20)
    (htrw : remoteWitnessScriptHash.size = 32)
    (hla : localAnchorWitnessScriptHash.size = 32)
    (hra : remoteAnchorWitnessScriptHash.size = 32)
    (hhtlcs : ∀ x ∈ htlcWitnessScriptHashes, x.size = 32)
    (hcount : (weightTargetsBaseTxOuts false toLocalValue toRemoteValue
        toLocalWitnessScriptHash remotePaymentKeyHash160
        remoteWitnessScriptHash localAnchorWitnessScriptHash
        remoteAnchorWitnessScriptHash).length
      + htlcWitnessScriptHashes.length < 0xfd) :
    4 * (serTx (weightTargetsCommitmentTx false fundingTxid toLocalValue
      toRemoteValue toLocalWitnessScriptHash remotePaymentKeyHash160
      remoteWitnessScriptHash localAnchorWitnessScriptHash
      remoteAnchorWitnessScriptHash htlcWitnessScriptHashes)).size
        + weightTargetsWitnessWeight =
      LnLean.Bitcoin.commitmentBaseWeight.val
        + 172 * htlcWitnessScriptHashes.length := by
  rw [weightTargets_commitmentTx_weight false fundingTxid hhash toLocalValue
    toRemoteValue toLocalWitnessScriptHash remotePaymentKeyHash160
    remoteWitnessScriptHash localAnchorWitnessScriptHash
    remoteAnchorWitnessScriptHash htlcWitnessScriptHashes htl htr htrw hla hra
    hhtlcs hcount]
  rw [weightTargets_serializedWeight_false, commitmentBaseWeight_eq_724]

/-- Anchor fully serialized weight: `1116 + 172 * k`, which is the BOLT 3
`1124 + 172 * k` fee basis minus the exact eight-weight-unit Appendix A
output-count gap. -/
theorem weightTargets_commitmentTx_weight_anchors
    (fundingTxid : ByteArray) (hhash : fundingTxid.size = 32)
    (toLocalValue toRemoteValue : Amount)
    (toLocalWitnessScriptHash remotePaymentKeyHash160
      remoteWitnessScriptHash localAnchorWitnessScriptHash
      remoteAnchorWitnessScriptHash : ByteArray)
    (htlcWitnessScriptHashes : List ByteArray)
    (htl : toLocalWitnessScriptHash.size = 32)
    (htr : remotePaymentKeyHash160.size = 20)
    (htrw : remoteWitnessScriptHash.size = 32)
    (hla : localAnchorWitnessScriptHash.size = 32)
    (hra : remoteAnchorWitnessScriptHash.size = 32)
    (hhtlcs : ∀ x ∈ htlcWitnessScriptHashes, x.size = 32)
    (hcount : (weightTargetsBaseTxOuts true toLocalValue toRemoteValue
        toLocalWitnessScriptHash remotePaymentKeyHash160
        remoteWitnessScriptHash localAnchorWitnessScriptHash
        remoteAnchorWitnessScriptHash).length
      + htlcWitnessScriptHashes.length < 0xfd) :
    4 * (serTx (weightTargetsCommitmentTx true fundingTxid toLocalValue
      toRemoteValue toLocalWitnessScriptHash remotePaymentKeyHash160
      remoteWitnessScriptHash localAnchorWitnessScriptHash
      remoteAnchorWitnessScriptHash htlcWitnessScriptHashes)).size
        + weightTargetsWitnessWeight =
      1116 + 172 * htlcWitnessScriptHashes.length := by
  rw [weightTargets_commitmentTx_weight true fundingTxid hhash toLocalValue
    toRemoteValue toLocalWitnessScriptHash remotePaymentKeyHash160
    remoteWitnessScriptHash localAnchorWitnessScriptHash
    remoteAnchorWitnessScriptHash htlcWitnessScriptHashes htl htr htrw hla hra
    hhtlcs hcount]
  exact weightTargets_serializedWeight_true _

/-- The channel layer and the serialization model agree on the non-anchor
closed formula. -/
theorem weightTargets_channel_eq_serialized_false (k : Nat) :
    (LnLean.Channel.commitmentWeight false k).val =
      weightTargetsSerializedWeight false k := by
  rw [weightTargets_serializedWeight_false]
  rw [LnLean.Channel.commitmentWeight_val]
  simp [LnLean.Channel.commitmentBaseWeight, LnLean.Channel.commitmentHtlcWeight]

/-- The channel layer's anchor formula equals BOLT 3's Appendix A fee basis,
not the model's literal serialization (which is eight weight units smaller). -/
theorem weightTargets_channel_eq_appendixA_true (k : Nat) :
    (LnLean.Channel.commitmentWeight true k).val =
      weightTargetsAppendixAWeight true k := by
  rw [weightTargets_appendixAWeight_eq_boltWeight, weightTargets_boltWeight_true]
  rw [LnLean.Channel.commitmentWeight_val]
  simp [LnLean.Channel.commitmentBaseWeight, LnLean.Channel.commitmentHtlcWeight]

end LnLean.Proofs.Bitcoin
