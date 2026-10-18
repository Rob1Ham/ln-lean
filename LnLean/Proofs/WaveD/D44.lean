import LnLean.Bitcoin.ScriptTemplates
import LnLean.Channel.Commitment
import LnLean.Channel.Types
import LnLean.Proofs.Bitcoin.WeightProps

/-!
# LnLean.Proofs.WaveD.D44

English claim (catalog `LN-L1-006`, task D44).  The commitment base weight
constant `724` decomposes into the non-witness *field* bytes, the *CompactSize
varint* prefixes, and the *scriptPubKey* bytes of the two base commitment
outputs, plus the assumed witness weight.  This module writes that
decomposition as named constants, proves the sum, and grounds each non-witness
component in the model's serializers and script builders.

BOLT 3 Appendix A (`refs/bolts/03-transactions.md:973-1086`, BOLT commit
`1aadb719b4007c4cea0ba6e36b08c4fb53788dee`) gives the base (zero-HTLC)
non-anchor commitment transaction as 125 non-witness bytes and 224 witness
weight units, i.e. `4 * 125 + 224 = 724`.  The 125 bytes split as follows.

| component | bytes | weight | source |
| --- | --- | --- | --- |
| version (4), prevout hash (32), prevout index (4), sequence (4), two output values (8 + 8), locktime (4) | 64 | 256 | `Bitcoin.Data.serU32` / `serU64` |
| CompactSize: input count, empty scriptSig length, output count, to_local script length, to_remote script length | 5 | 20 | `Bitcoin.Data.compactSizeEnc` |
| scriptPubKeys: `to_local` P2WSH (2 + 32), `to_remote` P2WPKH (2 + 20) | 56 | 224 | `LnLean.Bitcoin.toLocalScriptPubKey` / `toRemoteP2WPKHScriptPubKey` |
| **non-witness subtotal** | **125** | **500** | |
| witness: 2-byte marker/flag + 222-byte funding-input witness | 56 | 224 | **assumed**, see below |
| **total** | | **724** | |

The 64 field bytes are proved from the L1 serializers (`serU32` is 4 bytes,
`serU64` is 8); the 5 varint bytes are proved from `compactSizeEnc` (`< 0xfd`
encodes in one byte); the 56 script bytes are proved from the model's P2WSH and
P2WPKH builders (`p2wsh_size`, `p2wpkh_size`).  `waveD_d44_baseCommitmentTx`
assembles those pieces into an actual `Bitcoin.Data.Tx`, and
`waveD_d44_baseCommitmentTx_serSize` proves that its base serialization is
exactly 125 bytes, so the field/varint/script split is a theorem about the
model's own serializer, not merely arithmetic on BOLT's table.

What is assumed, not proved.  The model (`Bitcoin.Data.Tx`) parses a witness
but exposes no witness serializer, and ECDSA signature lengths are variable.
The witness term is therefore an *assumed component size*: BOLT 3 Appendix A's
`witness: 222 bytes` (1 count + 1 nil length + (1 + 73) sig_alice +
(1 + 73) sig_bob + (1 + 71) witness script), plus the 2-byte segwit
marker/flag, totalling 224.  The 71-byte 2-of-2 multisig witness script is the
size proved in `LnLean.Bitcoin.FundingParams.witnessScript_size`; the 73-byte
signature is BOLT 3's maximum-DER assumption, not a model fact.

Scope.  The 724 constant is the base weight *before* HTLC outputs and assumes
both commitment outputs are emitted.  Trimming a zero-valued `to_local` or
`to_remote` output would make the actual serialization smaller, but BOLT 3
still fees the negotiated 724 constant; this module proves the constant, not a
lower bound on every possible commitment record.  Anchors (1124) are the other
BOLT 3 constant and are not the target here.

No `sorry`; the only added hypotheses are the wire-size hypotheses
`fundingTxid.size = 32`, `witnessScriptHash.size = 32`, and
`paymentKeyHash160.size = 20`, which are the standard shapes of a txid,
SHA256 output, and HASH160 output.
-/

namespace LnLean.Proofs.WaveD.D44

set_option autoImplicit false

open Bitcoin.Data
open LnLean

-- OBLIGATION: LN-WD-D44

/-! ## Field bytes (fixed-width non-witness fields) -/

/-- `nVersion` field: 4 bytes (`serU32`). -/
def versionFieldBytes : Nat := 4

/-- Funding outpoint hash: 32 bytes. -/
def prevoutHashBytes : Nat := 32

/-- Funding outpoint index: 4 bytes (`serU32`). -/
def prevoutIndexBytes : Nat := 4

/-- Input `nSequence`: 4 bytes (`serU32`). -/
def sequenceFieldBytes : Nat := 4

/-- One output value: 8 bytes (`serU64`). -/
def outputValueBytes : Nat := 8

/-- `nLockTime`: 4 bytes (`serU32`). -/
def locktimeFieldBytes : Nat := 4

/-- Fixed-width field bytes of the base commitment transaction: version,
funding prevout (hash + index), sequence, the two output values, locktime.
`4 + 32 + 4 + 4 + 8 + 8 + 4 = 64`. -/
def fieldBytes : Nat :=
  versionFieldBytes + prevoutHashBytes + prevoutIndexBytes + sequenceFieldBytes
    + outputValueBytes + outputValueBytes + locktimeFieldBytes

/-! ## CompactSize varint bytes -/

/-- A one-byte CompactSize count prefix (input/output counts less than `0xfd`). -/
def countVarintBytes : Nat := 1

/-- A one-byte CompactSize length prefix (script lengths less than `0xfd`). -/
def lengthVarintBytes : Nat := 1

/-- Varint bytes of the base commitment transaction: input count, empty
scriptSig length, output count, `to_local` script length, and `to_remote`
script length.  `1 + 1 + 1 + 1 + 1 = 5`. -/
def varintBytes : Nat :=
  countVarintBytes + lengthVarintBytes + countVarintBytes
    + lengthVarintBytes + lengthVarintBytes

/-! ## Script bytes -/

/-- `to_local` scriptPubKey: P2WSH `OP_0 <32-byte program>` = 2 + 32 bytes. -/
def p2wshScriptBytes : Nat := 2 + 32

/-- `to_remote` scriptPubKey (no anchors): P2WPKH `OP_0 <20-byte hash>` =
2 + 20 bytes. -/
def p2wpkhScriptBytes : Nat := 2 + 20

/-- ScriptPubKey bytes of the two base commitment outputs: 34 + 22 = 56. -/
def scriptBytes : Nat := p2wshScriptBytes + p2wpkhScriptBytes

/-! ## Non-witness and witness totals -/

/-- Non-witness serialized bytes of the base commitment transaction: 125. -/
def nonWitnessBytes : Nat := fieldBytes + varintBytes + scriptBytes

/-- Weight of the field bytes: 4 weight units per byte. -/
def fieldWeight : Nat := 4 * fieldBytes

/-- Weight of the varint bytes: 4 weight units per byte. -/
def varintWeight : Nat := 4 * varintBytes

/-- Weight of the scriptPubKey bytes: 4 weight units per byte. -/
def scriptWeight : Nat := 4 * scriptBytes

/-- Non-witness weight: 500. -/
def nonWitnessWeight : Nat := 4 * nonWitnessBytes

/-- Segwit marker/flag bytes, charged 1 weight unit each. -/
def witnessHeaderBytes : Nat := 2

/-- BOLT 3's assumed signature size: a 72-byte DER signature plus the 1-byte
sighash type.  Actual ECDSA signatures are 71-73 bytes; the model does not
serialize them. -/
def signatureBytes : Nat := 73

/-- The 2-of-2 funding witness script: 1 (OP_2) + 34 + 34 + 1 (OP_2) +
1 (OP_CHECKMULTISIG) = 71 bytes.  See
`LnLean.Bitcoin.FundingParams.witnessScript_size`. -/
def fundingWitnessScriptBytes : Nat := 71

/-- Assumed serialized funding-input witness: 1 count + 1 nil length +
(1 + 73) sig_alice + (1 + 73) sig_bob + (1 + 71) witness script = 222. -/
def fundingWitnessBytes : Nat :=
  1 + 1 + (1 + signatureBytes) + (1 + signatureBytes)
    + (1 + fundingWitnessScriptBytes)

/-- Assumed witness bytes of the base commitment transaction:
2 marker/flag + 222 funding witness = 224. -/
def witnessBytes : Nat := witnessHeaderBytes + fundingWitnessBytes

/-- Assumed witness weight (witness bytes count 1 weight unit each). -/
def witnessWeight : Nat := witnessBytes

/-- The reconstructed base weight: 724. -/
def totalBaseWeight : Nat := nonWitnessWeight + witnessWeight

/-! ## The arithmetic decomposition -/

/-- The fixed-width fields contribute 64 bytes: version 4, prevout 36,
sequence 4, two values 16, locktime 4. -/
theorem waveD_d44_fieldBytes_eq : fieldBytes = 64 := rfl

/-- The CompactSize prefixes contribute 5 bytes, one per prefix. -/
theorem waveD_d44_varintBytes_eq : varintBytes = 5 := rfl

/-- The two scriptPubKeys contribute 56 bytes: P2WSH 34 + P2WPKH 22. -/
theorem waveD_d44_scriptBytes_eq : scriptBytes = 56 := rfl

/-- Field, varint, and script bytes sum to BOLT 3's 125 non-witness bytes. -/
theorem waveD_d44_nonWitnessBytes_eq : nonWitnessBytes = 125 := rfl

/-- The assumed witness part is 224 bytes: 2 marker/flag + 222 witness. -/
theorem waveD_d44_witnessBytes_eq : witnessBytes = 224 := rfl

/-- Witness inner decomposition: 222 bytes = 1 + 1 + (1 + 73) + (1 + 73) +
(1 + 71). -/
theorem waveD_d44_fundingWitnessBytes_eq : fundingWitnessBytes = 222 := rfl

/-- Weight of the field component is 256. -/
theorem waveD_d44_fieldWeight_eq : fieldWeight = 256 := rfl

/-- Weight of the varint component is 20. -/
theorem waveD_d44_varintWeight_eq : varintWeight = 20 := rfl

/-- Weight of the script component is 224. -/
theorem waveD_d44_scriptWeight_eq : scriptWeight = 224 := rfl

/-- Non-witness weight is 500 = `4 * 125`. -/
theorem waveD_d44_nonWitnessWeight_eq : nonWitnessWeight = 500 := rfl

/-- The four weight components: field 256, varint 20, script 224, assumed
witness 224. -/
theorem waveD_d44_weight_components :
    fieldWeight = 256 ∧ varintWeight = 20 ∧ scriptWeight = 224 ∧
      witnessWeight = 224 := by
  decide

/-- **Main decomposition.**  The model's commitment base weight `724` is the
sum of the field, varint, and script weights plus the assumed witness
weight: `256 + 20 + 224 + 224 = 724`. -/
theorem waveD_d44_base_weight_eq_components :
    LnLean.Bitcoin.commitmentBaseWeight.val =
      fieldWeight + varintWeight + scriptWeight + witnessWeight := by
  decide

/-- The same decomposition, stated with `nonWitnessWeight` isolated:
`724 = 500 + 224`. -/
theorem waveD_d44_base_weight_eq_nonWitness_add_witness :
    LnLean.Bitcoin.commitmentBaseWeight.val =
      nonWitnessWeight + witnessWeight := by
  decide

/-- The reconstructed total is exactly the BOLT 3 constant 724. -/
theorem waveD_d44_totalBaseWeight_eq :
    totalBaseWeight = LnLean.Bitcoin.commitmentBaseWeight.val := by
  decide

/-- The channel layer's non-anchor base weight is the same 724. -/
theorem waveD_d44_channel_base_weight :
    LnLean.Channel.commitmentBaseWeight false = 724 :=
  LnLean.Channel.commitmentBaseWeight_noAnchors

/-- The decomposition agrees with the wave-A coarse Appendix A model
`LnLean.Proofs.Bitcoin.weightFromBytes false 0 = 4 * 125 + 224`. -/
theorem waveD_d44_eq_weightProps :
    LnLean.Bitcoin.commitmentBaseWeight.val =
      LnLean.Proofs.Bitcoin.weightFromBytes false 0 := by
  decide

/-! ## Grounding the field bytes in the L1 serializers -/

/-- `serU32` always emits exactly 4 bytes. -/
theorem waveD_d44_serU32_size (x : UInt32) : (serU32 x).size = 4 := by
  simp [serU32]

/-- `serU64` always emits exactly 8 bytes. -/
theorem waveD_d44_serU64_size (x : UInt64) : (serU64 x).size = 8 := by
  simp [serU64]

/-- `serU8` emits exactly 1 byte. -/
theorem waveD_d44_serU8_size (x : UInt8) : (serU8 x).size = 1 := by
  simp [serU8]

/-- A CompactSize value below `0xfd` encodes as a single byte. -/
theorem waveD_d44_compactSizeEnc_size_lt_253 (n : Nat) (h : n < 0xfd) :
    (compactSizeEnc n).size = 1 := by
  simp [compactSizeEnc, h, serU8]

/-! ## Grounding the varint bytes in `compactSizeEnc` -/

/-- Every CompactSize prefix used by the base commitment transaction is one
byte: input count 1, empty scriptSig length 0, output count 2, `to_local`
script length 34, `to_remote` script length 22. -/
theorem waveD_d44_varint_component_sizes :
    (compactSizeEnc 1).size = 1 ∧ (compactSizeEnc 0).size = 1 ∧
      (compactSizeEnc 2).size = 1 ∧ (compactSizeEnc 34).size = 1 ∧
        (compactSizeEnc 22).size = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [compactSizeEnc, serU8]

/-- The five varint prefixes of the base commitment transaction together
occupy exactly `varintBytes = 5` bytes. -/
theorem waveD_d44_varint_total :
    (compactSizeEnc 1).size + (compactSizeEnc 0).size +
        (compactSizeEnc 2).size + (compactSizeEnc 34).size +
          (compactSizeEnc 22).size = varintBytes := by
  simp [compactSizeEnc, serU8, varintBytes, countVarintBytes, lengthVarintBytes]

/-! ## Grounding the script bytes in the model's script builders -/

/-- The model's `to_local` P2WSH scriptPubKey is 34 bytes for a 32-byte
witness-script hash. -/
theorem waveD_d44_toLocalScriptPubKey_size (h : ByteArray) (hh : h.size = 32) :
    (LnLean.Bitcoin.toLocalScriptPubKey h).bytes.size = p2wshScriptBytes := by
  simpa [p2wshScriptBytes, LnLean.Bitcoin.toLocalScriptPubKey]
    using LnLean.Bitcoin.p2wsh_size h hh

/-- The model's non-anchor `to_remote` P2WPKH scriptPubKey is 22 bytes for a
20-byte HASH160. -/
theorem waveD_d44_toRemoteScriptPubKey_size (h : ByteArray) (hh : h.size = 20) :
    (LnLean.Bitcoin.toRemoteP2WPKHScriptPubKey h).bytes.size = p2wpkhScriptBytes := by
  simpa [p2wpkhScriptBytes, LnLean.Bitcoin.toRemoteP2WPKHScriptPubKey]
    using LnLean.Bitcoin.p2wpkh_size h hh

/-- The script component `56 = 34 + 22` is exactly the sum of the sizes of the
model's actual `to_local` and `to_remote` scripts. -/
theorem waveD_d44_scriptBytes_eq_model
    (toLocalWitnessScriptHash remotePaymentKeyHash160 : ByteArray)
    (htl : toLocalWitnessScriptHash.size = 32)
    (htr : remotePaymentKeyHash160.size = 20) :
    scriptBytes =
      (LnLean.Bitcoin.toLocalScriptPubKey toLocalWitnessScriptHash).bytes.size +
        (LnLean.Bitcoin.toRemoteP2WPKHScriptPubKey remotePaymentKeyHash160).bytes.size := by
  rw [waveD_d44_toLocalScriptPubKey_size _ htl,
    waveD_d44_toRemoteScriptPubKey_size _ htr]
  rfl

/-! ## The model transaction and its serialized size -/

/-- The base (zero-HTLC, non-anchor) commitment transaction assembled from the
model's script builders: version 2, one funding input, `to_remote` P2WPKH and
`to_local` P2WSH outputs (BOLT 3 ordering), locktime 0, empty witness. -/
def waveD_d44_baseCommitmentTx (fundingTxid : ByteArray)
    (toLocalValue toRemoteValue : Amount)
    (toLocalWitnessScriptHash remotePaymentKeyHash160 : ByteArray) : Tx :=
  { version := 2
    vin := [{ prevout := ⟨fundingTxid, 0⟩
              scriptSig := ⟨ByteArray.empty⟩
              sequence := 0 }]
    vout := [{ value := toRemoteValue
               scriptPubKey := LnLean.Bitcoin.toRemoteP2WPKHScriptPubKey remotePaymentKeyHash160 },
             { value := toLocalValue
               scriptPubKey := LnLean.Bitcoin.toLocalScriptPubKey toLocalWitnessScriptHash }]
    locktime := 0
    witness := [] }

/-- **Serialized-size theorem.**  The model's base commitment transaction
serializes to exactly `nonWitnessBytes = 125` bytes under the standard
32/32/20-byte hash shapes. -/
theorem waveD_d44_baseCommitmentTx_serSize
    (fundingTxid : ByteArray) (hhash : fundingTxid.size = 32)
    (toLocalValue toRemoteValue : Amount)
    (toLocalWitnessScriptHash remotePaymentKeyHash160 : ByteArray)
    (htl : toLocalWitnessScriptHash.size = 32)
    (htr : remotePaymentKeyHash160.size = 20) :
    (serTx (waveD_d44_baseCommitmentTx fundingTxid toLocalValue toRemoteValue
      toLocalWitnessScriptHash remotePaymentKeyHash160)).size = nonWitnessBytes := by
  simp only [waveD_d44_baseCommitmentTx, serTx, List.length_cons, List.length_nil,
    List.foldl_cons, List.foldl_nil, ByteArray.size_append, ByteArray.size_empty]
  simp [serTxIn, serTxOut, compactSizeEnc, serU8, serU32, serU64, hhash, htl, htr,
    LnLean.Bitcoin.toLocalScriptPubKey, LnLean.Bitcoin.toRemoteP2WPKHScriptPubKey,
    LnLean.Bitcoin.p2wsh_size, LnLean.Bitcoin.p2wpkh_size,
    nonWitnessBytes, fieldBytes, varintBytes, scriptBytes,
    versionFieldBytes, prevoutHashBytes, prevoutIndexBytes, sequenceFieldBytes,
    outputValueBytes, locktimeFieldBytes, countVarintBytes, lengthVarintBytes,
    p2wshScriptBytes, p2wpkhScriptBytes]

/-- The serialized size is exactly the field + varint + script decomposition
of the model transaction. -/
theorem waveD_d44_baseCommitmentTx_serSize_components
    (fundingTxid : ByteArray) (hhash : fundingTxid.size = 32)
    (toLocalValue toRemoteValue : Amount)
    (toLocalWitnessScriptHash remotePaymentKeyHash160 : ByteArray)
    (htl : toLocalWitnessScriptHash.size = 32)
    (htr : remotePaymentKeyHash160.size = 20) :
    (serTx (waveD_d44_baseCommitmentTx fundingTxid toLocalValue toRemoteValue
        toLocalWitnessScriptHash remotePaymentKeyHash160)).size =
      fieldBytes + varintBytes + scriptBytes := by
  rw [waveD_d44_baseCommitmentTx_serSize fundingTxid hhash toLocalValue
    toRemoteValue toLocalWitnessScriptHash remotePaymentKeyHash160 htl htr]
  rfl

/-- The non-witness weight `500` is exactly four times the serialized size of
the model's base commitment transaction. -/
theorem waveD_d44_nonWitnessWeight_eq_serSize
    (fundingTxid : ByteArray) (hhash : fundingTxid.size = 32)
    (toLocalValue toRemoteValue : Amount)
    (toLocalWitnessScriptHash remotePaymentKeyHash160 : ByteArray)
    (htl : toLocalWitnessScriptHash.size = 32)
    (htr : remotePaymentKeyHash160.size = 20) :
    nonWitnessWeight =
      4 * (serTx (waveD_d44_baseCommitmentTx fundingTxid toLocalValue
        toRemoteValue toLocalWitnessScriptHash remotePaymentKeyHash160)).size := by
  rw [waveD_d44_baseCommitmentTx_serSize fundingTxid hhash toLocalValue
    toRemoteValue toLocalWitnessScriptHash remotePaymentKeyHash160 htl htr]
  rfl

/-- **Full model form of the target.**  For any base commitment transaction
built from the model's scripts with standard hash sizes, the BOLT 3 base
weight is four times its non-witness serialization plus the assumed 224 weight
units of witness data: `4 * 125 + 224 = 724`. -/
theorem waveD_d44_base_weight_eq_serSize_add_witness
    (fundingTxid : ByteArray) (hhash : fundingTxid.size = 32)
    (toLocalValue toRemoteValue : Amount)
    (toLocalWitnessScriptHash remotePaymentKeyHash160 : ByteArray)
    (htl : toLocalWitnessScriptHash.size = 32)
    (htr : remotePaymentKeyHash160.size = 20) :
    LnLean.Bitcoin.commitmentBaseWeight.val =
      4 * (serTx (waveD_d44_baseCommitmentTx fundingTxid toLocalValue
        toRemoteValue toLocalWitnessScriptHash remotePaymentKeyHash160)).size
        + witnessBytes := by
  rw [waveD_d44_baseCommitmentTx_serSize fundingTxid hhash toLocalValue
    toRemoteValue toLocalWitnessScriptHash remotePaymentKeyHash160 htl htr]
  decide

end LnLean.Proofs.WaveD.D44
