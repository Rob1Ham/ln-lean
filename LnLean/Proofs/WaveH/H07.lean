/-
# H07 — HTLC-wire BIP 143 preimage and vendored byte equality (PR-05, PR-02)

**Catalog issues.**

* `PR-05` (P1): the BOLT 3 sighash preimage was proved byte-equal to the
  vendored `Bitcoin.SigHash.bip143MsgL` for the *commitment* wire only
  (`commitmentBip143Preimage_eq_bip143MsgL`, `SighashTargets` §13.3).  The
  `HtlcWire` (second-stage HTLC transaction) instantiation was still missing.
* `PR-02` (P1): the wire record must carry enough data for a wire-only sighash
  construction.  `HtlcWire.toTx` is the exact single-input/single-output
  transaction, so the preimage can be derived from it rather than supplied.

## Result of this module

1. `htlcBip143Preimage h scriptCode ht amountSat` is the exact-wire BIP 143
   preimage of the HTLC transaction `h.toTx` at input index `0`, obtained from
   `Bip143Preimage.ofTx`.  The HTLC wire has exactly one input, so no input
   index is left to the caller.
2. Field projections: the preimage `version`, outpoint txid, outpoint index,
   `sequence`, `locktime`, `scriptCode`, `amountSat` and `sighashType` are
   exactly the wire fields (the outpoint txid stays in consensus-internal
   order, never reversed; the index and every integer are little-endian in
   `preimageBytes`).
3. `htlcBip143Preimage_eq_bip143MsgL`: for **every** `HtlcWire`, scriptCode,
   hash type and spent amount, the preimage bytes are literally the list
   produced by the vendored `Bitcoin.SigHash.bip143MsgL h.toTx 0 ...`.
4. Sizes: the three sub-hashes are always 32 bytes; under
   `HtlcWire.WellFormed` the outpoint txid is 32 bytes and the full preimage
   is `156 + CompactSize(scriptCode.size) + scriptCode.size` bytes (179 for a
   22-byte scriptCode, 191 for 34 bytes, 412 for 253 bytes).
5. A decidable byte-level vector (`SIGHASH_NONE|ANYONECANPAY`, `ht = 0x82`,
   where all three sub-hashes are the BIP 143 zero vector) pins the layout:
   the outpoint slice, the CompactSize scriptCode prefix and the amount slice
   are checked against the vendored encoder.  The vector's scriptCode is an
   opaque 34-byte placeholder; see the scope note.

## Hypotheses / scope

* **No well-formedness premise is needed for the field and byte-equality
  theorems.**  They hold for every `HtlcWire` and every `scriptCode :
  ByteArray`.  `HtlcWire.WellFormed` is used only for the length corollary,
  because the outpoint txid length is a wire-domain fact, not a serialization
  fact.
* **`scriptCode` is an explicit parameter, not synthesized here.**  For a
  P2WSH HTLC output it is the BOLT 3 HTLC witness script (offered/received),
  which lane H08 synthesizes.  This module makes no claim that a particular
  byte string is a valid BOLT 3 script.
* **`amountSat` is the value of the *spent* HTLC output**, i.e. an output of
  the commitment transaction.  It is deliberately a parameter:
  `HtlcWire.valueSat` is the value of the *produced* second-stage output, not
  the amount being spent, so identifying them would be unsound.
* `ht` is the SIGHASH type.  BOLT 3 uses `SIGHASH_ALL` (`0x01`); this module
  proves the equality for all `ht`, and the BIP 143 omission behaviour
  (`ANYONECANPAY`/`NONE`/`SINGLE`) is already mechanized in
  `LnLean.Bitcoin.Sighash`.
* The hash function is the vendored seam SHA-256 (`Bitcoin.SigHash.dshaL`);
  collision resistance (C1) is not used and no digest injectivity is claimed.
  In particular this module proves preimage-byte equality, not signature
  binding.

## Anchors

* BIP 143 §3–6 (`refs/bolts/03-transactions.md:75-83`, `:113-135`): the
  ten-field witness-v0 preimage; the outpoint txid is 32 bytes in internal
  byte order.
* BOLT 3 §"HTLC Outputs" (`refs/bolts/03-transactions.md`): the second-stage
  HTLC transaction spends exactly one HTLC output at index `0`, so the
  signing input index is `0`.
* Model: `LnLean/Proofs/Channel/SighashTargets.lean` §12.1 (`HtlcWire`,
  `HtlcWire.toTx`, `Bip143Preimage`, `Bip143Preimage.ofTx`) and §13.3
  (`preimageBytes_eq_bip143MsgL_ofTx`); `LnLean/Bitcoin/Sighash.lean`
  (`bip143MsgL`, `hashPrevoutsOf`, `hashSequenceOf`, `hashOutputsOf`).
-/

import LnLean.Proofs.Channel.SighashTargets

namespace LnLean.Proofs.WaveH.H07

set_option autoImplicit false
set_option maxRecDepth 10000

open Bitcoin.Data
open Bitcoin.Serialization
open LnLean.Proofs.Channel.SighashTargets

/-! ## 1. The wire is exactly one input at index `0` -/

/-- The HTLC wire transaction has a single input, the commitment outpoint. -/
theorem HtlcWire.toTx_vin (h : HtlcWire) :
    h.toTx.vin =
      [{ prevout := ⟨h.commitmentTxid, h.commitmentOutputIndex⟩,
         scriptSig := Script.empty, sequence := h.sequence }] := rfl

/-- The HTLC wire transaction has exactly one input, so index `0` is in range. -/
theorem HtlcWire.toTx_vin_length (h : HtlcWire) : h.toTx.vin.length = 1 := rfl

/-- The single input of the wire transaction. -/
theorem HtlcWire.toTx_vin_getD_zero (h : HtlcWire) :
    h.toTx.vin.getD 0 LnLean.Bitcoin.Sighash.dummyTxIn =
      { prevout := ⟨h.commitmentTxid, h.commitmentOutputIndex⟩,
        scriptSig := Script.empty, sequence := h.sequence } := by
  rw [HtlcWire.toTx_vin]
  rfl

/-- There is no out-of-range input: the BIP 143 out-of-range guard of
`LnLean.Bitcoin.Sighash.sighashWitnessV0` never fires for `HtlcWire` at
index `0`. -/
theorem HtlcWire.vin_length_not_le_zero (h : HtlcWire) :
    ¬ h.toTx.vin.length ≤ 0 := by
  rw [HtlcWire.toTx_vin_length]
  decide

/-! ## 2. The HTLC-wire BIP 143 preimage -/

/-- **The exact-wire BIP 143 preimage of the HTLC transaction.**  Input index
`0` is fixed because `HtlcWire.toTx` has exactly one input.  `scriptCode` is
the BOLT 3 HTLC witness script (supplied by the caller; see scope note) and
`amountSat` is the value of the spent HTLC output, not `h.valueSat`. -/
def htlcBip143Preimage (h : HtlcWire) (scriptCode : ByteArray) (ht : UInt32)
    (amountSat : UInt64) : Bip143Preimage :=
  Bip143Preimage.ofTx h.toTx 0 scriptCode ht amountSat

/-! ## 3. Field projections -/

/-- The preimage `version` is the wire transaction version. -/
@[simp] theorem htlcBip143Preimage_version (h : HtlcWire)
    (scriptCode : ByteArray) (ht : UInt32) (amountSat : UInt64) :
    (htlcBip143Preimage h scriptCode ht amountSat).version = h.version := by
  simp [htlcBip143Preimage, Bip143Preimage.ofTx, HtlcWire.toTx]

/-- The preimage outpoint txid is the commitment transaction id, in
consensus-internal byte order (never reversed). -/
@[simp] theorem htlcBip143Preimage_outpointTxid (h : HtlcWire)
    (scriptCode : ByteArray) (ht : UInt32) (amountSat : UInt64) :
    (htlcBip143Preimage h scriptCode ht amountSat).outpointTxid =
      h.commitmentTxid := by
  simp [htlcBip143Preimage, Bip143Preimage.ofTx, HtlcWire.toTx]

/-- The preimage outpoint index is the wire commitment output index. -/
@[simp] theorem htlcBip143Preimage_outpointIndex (h : HtlcWire)
    (scriptCode : ByteArray) (ht : UInt32) (amountSat : UInt64) :
    (htlcBip143Preimage h scriptCode ht amountSat).outpointIndex =
      h.commitmentOutputIndex := by
  simp [htlcBip143Preimage, Bip143Preimage.ofTx, HtlcWire.toTx]

/-- The preimage `nSequence` is the wire sequence. -/
@[simp] theorem htlcBip143Preimage_sequence (h : HtlcWire)
    (scriptCode : ByteArray) (ht : UInt32) (amountSat : UInt64) :
    (htlcBip143Preimage h scriptCode ht amountSat).sequence = h.sequence := by
  simp [htlcBip143Preimage, Bip143Preimage.ofTx, HtlcWire.toTx]

/-- The preimage `nLockTime` is the wire locktime. -/
@[simp] theorem htlcBip143Preimage_locktime (h : HtlcWire)
    (scriptCode : ByteArray) (ht : UInt32) (amountSat : UInt64) :
    (htlcBip143Preimage h scriptCode ht amountSat).locktime = h.locktime := by
  simp [htlcBip143Preimage, Bip143Preimage.ofTx, HtlcWire.toTx]

/-- The preimage scriptCode is exactly the supplied scriptCode. -/
@[simp] theorem htlcBip143Preimage_scriptCode (h : HtlcWire)
    (scriptCode : ByteArray) (ht : UInt32) (amountSat : UInt64) :
    (htlcBip143Preimage h scriptCode ht amountSat).scriptCode = scriptCode := by
  simp [htlcBip143Preimage, Bip143Preimage.ofTx]

/-- The preimage amount is the supplied spent-output value. -/
@[simp] theorem htlcBip143Preimage_amountSat (h : HtlcWire)
    (scriptCode : ByteArray) (ht : UInt32) (amountSat : UInt64) :
    (htlcBip143Preimage h scriptCode ht amountSat).amountSat = amountSat := by
  simp [htlcBip143Preimage, Bip143Preimage.ofTx]

/-- The preimage sighash type is the supplied hash type. -/
@[simp] theorem htlcBip143Preimage_sighashType (h : HtlcWire)
    (scriptCode : ByteArray) (ht : UInt32) (amountSat : UInt64) :
    (htlcBip143Preimage h scriptCode ht amountSat).sighashType = ht := by
  simp [htlcBip143Preimage, Bip143Preimage.ofTx]

/-- The three BIP 143 sub-hashes are the transaction-derived ones. -/
theorem htlcBip143Preimage_subhashes (h : HtlcWire)
    (scriptCode : ByteArray) (ht : UInt32) (amountSat : UInt64) :
    (htlcBip143Preimage h scriptCode ht amountSat).hashPrevouts =
        LnLean.Bitcoin.Sighash.hashPrevoutsOf h.toTx ht ∧
    (htlcBip143Preimage h scriptCode ht amountSat).hashSequence =
        LnLean.Bitcoin.Sighash.hashSequenceOf h.toTx ht ∧
    (htlcBip143Preimage h scriptCode ht amountSat).hashOutputs =
        LnLean.Bitcoin.Sighash.hashOutputsOf h.toTx 0 ht := by
  exact ⟨rfl, rfl, rfl⟩

/-- **Wire-field conjunction.**  The preimage fields that are determined by the
wire are exactly the wire fields.  The remaining two fields are the explicit
scriptCode and spent amount parameters. -/
theorem htlcBip143Preimage_wire_fields (h : HtlcWire)
    (scriptCode : ByteArray) (ht : UInt32) (amountSat : UInt64) :
    (htlcBip143Preimage h scriptCode ht amountSat).version = h.version ∧
    (htlcBip143Preimage h scriptCode ht amountSat).outpointTxid =
      h.commitmentTxid ∧
    (htlcBip143Preimage h scriptCode ht amountSat).outpointIndex =
      h.commitmentOutputIndex ∧
    (htlcBip143Preimage h scriptCode ht amountSat).sequence = h.sequence ∧
    (htlcBip143Preimage h scriptCode ht amountSat).locktime = h.locktime ∧
    (htlcBip143Preimage h scriptCode ht amountSat).scriptCode = scriptCode ∧
    (htlcBip143Preimage h scriptCode ht amountSat).amountSat = amountSat ∧
    (htlcBip143Preimage h scriptCode ht amountSat).sighashType = ht := by
  simp

/-! ## 4. Byte equality with the vendored BIP 143 encoder -/

/-- **Byte equality with `Bitcoin.SigHash.bip143MsgL`.**  For every HTLC wire,
scriptCode, hash type and spent amount, the model preimage bytes are literally
the vendored BIP 143 preimage of `h.toTx` at input `0`.  No well-formedness
premise is required: the equality is about serialization, not about the wire
domain. -/
theorem htlcBip143Preimage_eq_bip143MsgL (h : HtlcWire)
    (scriptCode : ByteArray) (ht : UInt32) (amountSat : UInt64) :
    bL (htlcBip143Preimage h scriptCode ht amountSat).preimageBytes =
      Bitcoin.SigHash.bip143MsgL h.toTx 0 (bL scriptCode) ht
        (amountSat.toNat : Int) :=
  Bip143Preimage.preimageBytes_eq_bip143MsgL_ofTx h.toTx 0 scriptCode ht amountSat

/-- The same equality against the model encoder
`LnLean.Bitcoin.Sighash.encode`. -/
theorem htlcBip143Preimage_eq_encode (h : HtlcWire)
    (scriptCode : ByteArray) (ht : UInt32) (amountSat : UInt64) :
    bL (htlcBip143Preimage h scriptCode ht amountSat).preimageBytes =
      bL (LnLean.Bitcoin.Sighash.encode
        (htlcBip143Preimage h scriptCode ht amountSat).toPreimage) :=
  Bip143Preimage.preimageBytes_eq_encode _

/-- `ByteArray`-level form against the model encoder. -/
theorem htlcBip143Preimage_eq_encode_bytes (h : HtlcWire)
    (scriptCode : ByteArray) (ht : UInt32) (amountSat : UInt64) :
    (htlcBip143Preimage h scriptCode ht amountSat).preimageBytes =
      LnLean.Bitcoin.Sighash.encode
        (htlcBip143Preimage h scriptCode ht amountSat).toPreimage :=
  Bip143Preimage.preimageBytes_eq_encode_bytes _

/-- The bridged model preimage is `ofTx` of the wire transaction at index `0`. -/
theorem htlcBip143Preimage_toPreimage (h : HtlcWire)
    (scriptCode : ByteArray) (ht : UInt32) (amountSat : UInt64) :
    (htlcBip143Preimage h scriptCode ht amountSat).toPreimage =
      LnLean.Bitcoin.Sighash.ofTx h.toTx 0 scriptCode ht
        (amountSat.toNat : Int) :=
  Bip143Preimage.toPreimage_ofTx h.toTx 0 scriptCode ht amountSat

/-! ## 5. Sizes -/

/-- The three BIP 143 sub-hashes are always 32 bytes, for every hash type. -/
theorem htlcBip143Preimage_hash_sizes (h : HtlcWire) (scriptCode : ByteArray)
    (ht : UInt32) (amountSat : UInt64) :
    (htlcBip143Preimage h scriptCode ht amountSat).hashPrevouts.size = 32 ∧
    (htlcBip143Preimage h scriptCode ht amountSat).hashSequence.size = 32 ∧
    (htlcBip143Preimage h scriptCode ht amountSat).hashOutputs.size = 32 := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [htlcBip143Preimage, Bip143Preimage.ofTx,
      LnLean.Bitcoin.Sighash.hashPrevoutsOf, LnLean.Bitcoin.Sighash.dsha]
    split <;> simp [LnLean.Bitcoin.Sighash.zeroHash_size,
      Bitcoin.Crypto.Seam.sha256d_size]
  · simp only [htlcBip143Preimage, Bip143Preimage.ofTx,
      LnLean.Bitcoin.Sighash.hashSequenceOf, LnLean.Bitcoin.Sighash.dsha]
    split <;> simp [LnLean.Bitcoin.Sighash.zeroHash_size,
      Bitcoin.Crypto.Seam.sha256d_size]
  · simp only [htlcBip143Preimage, Bip143Preimage.ofTx,
      LnLean.Bitcoin.Sighash.hashOutputsOf, LnLean.Bitcoin.Sighash.dsha]
    repeat' split
    all_goals simp [LnLean.Bitcoin.Sighash.zeroHash_size,
      Bitcoin.Crypto.Seam.sha256d_size]

/-- Under `HtlcWire.WellFormed` the preimage outpoint txid is 32 bytes. -/
theorem htlcBip143Preimage_outpointTxid_size (h : HtlcWire)
    (hw : h.WellFormed) (scriptCode : ByteArray) (ht : UInt32)
    (amountSat : UInt64) :
    (htlcBip143Preimage h scriptCode ht amountSat).outpointTxid.size = 32 := by
  rw [htlcBip143Preimage_outpointTxid]
  exact hw.1

/-- Preimage length: `156 + CompactSize(scriptCode.size) + scriptCode.size`
bytes.  This is 179 for a 22-byte scriptCode and 191 for 34 bytes. -/
theorem htlcBip143Preimage_preimageBytes_size (h : HtlcWire)
    (hw : h.WellFormed) (scriptCode : ByteArray) (ht : UInt32)
    (amountSat : UInt64) :
    (htlcBip143Preimage h scriptCode ht amountSat).preimageBytes.size =
      156 + compactSizeWidth scriptCode.size + scriptCode.size := by
  obtain ⟨hp, hq, ho⟩ := htlcBip143Preimage_hash_sizes h scriptCode ht amountSat
  exact Bip143Preimage.preimageBytes_size _ hp hq
    (htlcBip143Preimage_outpointTxid_size h hw scriptCode ht amountSat) ho

/-! ## 6. Decidable byte-level vector -/

/-- Opaque 34-byte scriptCode placeholder.  The vector checks layout, not
BOLT 3 script semantics (lane H08 synthesizes the real HTLC scripts). -/
def vectorHtlcScriptCode : ByteArray :=
  byteList (List.replicate 34 0x77)

def vectorHtlcWire : HtlcWire :=
  { version := 2
    commitmentTxid := hash32 0x66
    commitmentOutputIndex := 1
    sequence := 0xffffffff
    valueSat := 5000
    scriptPubKey := byteList [0x00, 0x14] ++
      byteList (List.replicate 20 0x55)
    locktime := 0 }

/-- `SIGHASH_NONE | ANYONECANPAY`, so all three sub-hashes are the BIP 143
zero vector and the layout is decidable without hashing. -/
def vectorHtlcPreimage : Bip143Preimage :=
  htlcBip143Preimage vectorHtlcWire vectorHtlcScriptCode 0x82 7000

theorem vectorHtlcPreimage_size :
    (bL vectorHtlcPreimage.preimageBytes).length = 191 := by
  decide

/-- Outpoint slice: 32-byte commitment txid in internal order (never
reversed), then the 4-byte little-endian commitment output index `1`. -/
theorem vectorHtlcPreimage_outpoint_bytes :
    ((bL vectorHtlcPreimage.preimageBytes).drop 68).take 36 =
      List.replicate 32 0x66 ++ [0x01, 0x00, 0x00, 0x00] := by
  decide

/-- scriptCode slice: one-byte CompactSize `0x22 = 34`, then the scriptCode. -/
theorem vectorHtlcPreimage_scriptCode_prefix :
    ((bL vectorHtlcPreimage.preimageBytes).drop 104).take 3 =
      [0x22, 0x77, 0x77] := by
  decide

/-- Amount slice: `7000 = 0x1b58` little-endian, 8 bytes. -/
theorem vectorHtlcPreimage_amount_bytes :
    ((bL vectorHtlcPreimage.preimageBytes).drop 139).take 8 =
      [0x58, 0x1b, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] := by
  decide

/-- The vendored encoder produces the same 191-byte length on the vector. -/
theorem vectorHtlcPreimage_vendor_size :
    (Bitcoin.SigHash.bip143MsgL vectorHtlcWire.toTx 0
      (bL vectorHtlcScriptCode) 0x82 7000).length = 191 := by
  decide

/-- The general theorem instantiates on the vector. -/
theorem vectorHtlcPreimage_vendor :
    bL vectorHtlcPreimage.preimageBytes =
      Bitcoin.SigHash.bip143MsgL vectorHtlcWire.toTx 0
        (bL vectorHtlcScriptCode) 0x82 7000 :=
  htlcBip143Preimage_eq_bip143MsgL vectorHtlcWire vectorHtlcScriptCode 0x82 7000

end LnLean.Proofs.WaveH.H07
