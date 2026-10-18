import Bitcoin.Data.Basic
import Bitcoin.Data.Tx
import Bitcoin.Serialization.Interface
import Bitcoin.SigHash.Interface
import LnLean.Bitcoin.Seam

/-!
# BIP 143 witness-v0 preimage model (funding and `to_local`)

This module gives the Lightning L1 model an explicit, byte-level BIP 143
witness-v0 sighash construction.  It is the wave-6 (lane `S6-L1-SIGHASH`)
companion of `LnLean.Bitcoin.Seam`: the seam fixes the funding and `to_local`
witness scripts, and this module fixes the digest that a witness-v0 signature
commits to.

## What is modelled

The ten BIP 143 fields, in consensus order, are represented by the record
`Preimage`:

```text
nVersion       (4-byte LE)
hashPrevouts   (32 bytes)
hashSequence   (32 bytes)
outpoint       (32-byte LE txid + 4-byte LE index)
scriptCode     (CompactSize length + bytes)
amount         (8-byte LE)
nSequence      (4-byte LE)
hashOutputs    (32 bytes)
nLockTime      (4-byte LE)
hashType       (4-byte LE)
```

`encode` serializes those fields from scratch with this module's own
`serU32LE` / `serU64LE` / `compactSize` / `serOutpoint` / `serTxOut`
functions; `ofTx` computes the fields from a `Bitcoin.Data.Tx`, an input
index, a scriptCode, a hashtype and the spent amount.  `digest` is the
double-SHA-256 of the preimage, and `sighashWitnessV0` adds BIP 143's
out-of-range input guard (zero digest).

The model is *proved byte-equal* to the vendored BIP 143 implementation
`Bitcoin.SigHash.signatureHashBip143Impl` (which is itself the vendored
`SignatureHash(WITNESS_V0)` transliteration): see
`sighashWitnessV0_eq_vendorImpl` and `sighashWitnessV0_eq_interface`.
Because the vendored code is exact, the serialization itself is not a
structural approximation: every byte above is the consensus byte.

## What is not proved here

* The double-SHA-256 primitive is the vendored seam hash
  (`Bitcoin.Crypto.Seam.sha256d`), not an independent implementation.  Hash
  equality is therefore definitional; collision resistance is assumption C1
  and signature unforgeability is assumption C3, neither used here.
* The model does not prove that `tx` is a valid or confirmable transaction,
  and it does not prove that the spent output value (`amount`) is the value
  of the outpoint.  Those are context hypotheses at the bridge site.
* BIP 143 deliberately does **not** commit every transaction field.  Under
  ANYONECANPAY it commits only the signing input's outpoint/sequence; under
  NONE/SINGLE it zeroes `hashSequence` and/or `hashOutputs`.  Those omissions
  are mechanized in `sighashWitnessV0_withVin_acp` and the `*_eq_zero`
  lemmas rather than hidden.

Anchors: BIP 143 §3–6, `refs/bolts/03-transactions.md:75-83` and
`:113-135` (funding and `to_local` outputs), Core
`src/script/interpreter.cpp` `SignatureHash(WITNESS_V0)`.
-/

namespace LnLean.Bitcoin.Sighash

set_option autoImplicit false

open Bitcoin.Data

/-! ## Byte serializers

These are the model's own serializers.  Each is proved equal to the
corresponding vendored list serializer, so the preimage below is exact and
not a structural tuple. -/

/-- 4-byte little-endian unsigned integer. -/
def serU32LE (x : UInt32) : ByteArray :=
  ByteArray.mk #[x.toUInt8, (x >>> 8).toUInt8, (x >>> 16).toUInt8,
    (x >>> 24).toUInt8]

/-- 8-byte little-endian unsigned integer. -/
def serU64LE (x : UInt64) : ByteArray :=
  ByteArray.mk #[x.toUInt8, (x >>> 8).toUInt8, (x >>> 16).toUInt8,
    (x >>> 24).toUInt8, (x >>> 32).toUInt8, (x >>> 40).toUInt8,
    (x >>> 48).toUInt8, (x >>> 56).toUInt8]

/-- Canonical CompactSize (the vendored general serializer, which this
module uses as a primitive and not as a sighash construction). -/
def compactSize (n : Nat) : ByteArray :=
  compactSizeEnc n

/-- `COutPoint` wire form: 32-byte txid then 4-byte LE index. -/
def serOutpoint (o : OutPoint) : ByteArray :=
  o.hash ++ serU32LE o.n

/-- `CTxOut` wire form: 8-byte LE amount, CompactSize script length, script. -/
def serTxOut (o : TxOut) : ByteArray :=
  serU64LE (UInt64.ofInt o.value) ++ compactSize o.scriptPubKey.bytes.size ++
    o.scriptPubKey.bytes

/-- The 32-byte zero vector used by BIP 143's zero sub-hashes.  This is the
vendored constant `Bitcoin.SigHash.zeroHashL`, viewed as `ByteArray`. -/
def zeroHash : ByteArray :=
  Bitcoin.Serialization.bytesOfList Bitcoin.SigHash.zeroHashL

/-- Double SHA-256 through the vendored seam hash floor.  For a concrete
witness-v0 digest this is `SHA256d(preimage)`; the two nested calls are the
seam's `sha256d`, not a local re-implementation. -/
def dsha (b : ByteArray) : ByteArray := Bitcoin.Crypto.Seam.sha256d b

/-! ## Serializer agreement with the vendored BIP 143 serializers -/

theorem bL_serU32LE (x : UInt32) :
    Bitcoin.Serialization.bL (serU32LE x) = Bitcoin.SigHash.serU32L x := rfl

theorem bL_serU64LE (x : UInt64) :
    Bitcoin.Serialization.bL (serU64LE x) = Bitcoin.SigHash.serU64L x := rfl

theorem bL_compactSize (n : Nat) :
    Bitcoin.Serialization.bL (compactSize n) =
      Bitcoin.Serialization.encCSL n :=
  Bitcoin.Serialization.bL_compactSizeEnc n

theorem bL_serOutpoint (o : OutPoint) :
    Bitcoin.Serialization.bL (serOutpoint o) =
      Bitcoin.SigHash.serOutpointL o := by
  simp [serOutpoint, Bitcoin.SigHash.serOutpointL, bL_serU32LE]

theorem bL_serTxOut (o : TxOut) :
    Bitcoin.Serialization.bL (serTxOut o) = Bitcoin.SigHash.serTxOutL o := by
  simp [serTxOut, Bitcoin.SigHash.serTxOutL, Bitcoin.SigHash.serAmountL,
    bL_serU64LE, bL_compactSize]

theorem bL_zeroHash :
    Bitcoin.Serialization.bL zeroHash = Bitcoin.SigHash.zeroHashL := by
  simp [zeroHash]

theorem zeroHash_size : zeroHash.size = 32 := by
  simp [zeroHash, Bitcoin.SigHash.zeroHashL, Bitcoin.Serialization.bytesOfList]

theorem bL_dsha (b : ByteArray) :
    Bitcoin.Serialization.bL (Bitcoin.SigHash.dshaL (Bitcoin.Serialization.bL b)) =
      Bitcoin.Serialization.bL (dsha b) := by
  unfold Bitcoin.SigHash.dshaL dsha
  rw [Bitcoin.Serialization.bytesOfList_bL]

/-- The length of the list view is the byte length.  This is the bridge
needed for the CompactSize scriptCode prefix. -/
theorem length_bL (b : ByteArray) :
    (Bitcoin.Serialization.bL b).length = b.size := rfl

/-- A left fold that appends a list-valued function is the list `flatMap`.
Used to identify the model's `foldl`-built sub-hash inputs with the vendored
list folds. -/
theorem foldl_append_nil_aux {α : Type} (xs : List α) (g : α → List UInt8)
    (acc : List UInt8) :
    xs.foldl (fun a x => a ++ g x) acc = acc ++ xs.flatMap g := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, ih]
    simp [List.flatMap_cons, List.append_assoc]

theorem foldl_append_nil {α : Type} (xs : List α) (g : α → List UInt8) :
    xs.foldl (fun acc x => acc ++ g x) [] = xs.flatMap g := by
  simpa using foldl_append_nil_aux xs g []

theorem bL_fold_serOutpoint (ins : List TxIn) :
    Bitcoin.Serialization.bL
        (ins.foldl (fun acc i => acc ++ serOutpoint i.prevout)
          ByteArray.empty) =
      ins.flatMap (fun i => Bitcoin.SigHash.serOutpointL i.prevout) := by
  rw [Bitcoin.Serialization.bL_foldl_append]
  simp [bL_serOutpoint]

theorem bL_fold_serU32 (ins : List TxIn) :
    Bitcoin.Serialization.bL
        (ins.foldl (fun acc i => acc ++ serU32LE i.sequence)
          ByteArray.empty) =
      ins.flatMap (fun i => Bitcoin.SigHash.serU32L i.sequence) := by
  rw [Bitcoin.Serialization.bL_foldl_append]
  simp [bL_serU32LE]

theorem bL_fold_serTxOut (outs : List TxOut) :
    Bitcoin.Serialization.bL
        (outs.foldl (fun acc o => acc ++ serTxOut o) ByteArray.empty) =
      outs.flatMap (fun o => Bitcoin.SigHash.serTxOutL o) := by
  rw [Bitcoin.Serialization.bL_foldl_append]
  simp [bL_serTxOut]

/-! ## The three BIP 143 sub-hashes (§3–5) -/

/-- `hashPrevouts`: zero under ANYONECANPAY, otherwise double-SHA-256 of all
outpoints in input order. -/
def hashPrevoutsOf (tx : Tx) (ht : UInt32) : ByteArray :=
  if Bitcoin.SigHash.htAcp ht then zeroHash
  else dsha (tx.vin.foldl (fun acc i => acc ++ serOutpoint i.prevout)
    ByteArray.empty)

/-- `hashSequence`: zero under ANYONECANPAY, SINGLE or NONE, otherwise
double-SHA-256 of all input sequences in input order. -/
def hashSequenceOf (tx : Tx) (ht : UInt32) : ByteArray :=
  if Bitcoin.SigHash.htAcp ht ∨
      Bitcoin.SigHash.htBase ht = Bitcoin.SigHash.HtBase.singleHt ∨
      Bitcoin.SigHash.htBase ht = Bitcoin.SigHash.HtBase.noneHt then
    zeroHash
  else dsha (tx.vin.foldl (fun acc i => acc ++ serU32LE i.sequence)
    ByteArray.empty)

/-- `hashOutputs`: SINGLE commits the output at `nIn` (zero out of range),
NONE is zero, ALL commits all outputs. -/
def hashOutputsOf (tx : Tx) (nIn : Nat) (ht : UInt32) : ByteArray :=
  match Bitcoin.SigHash.htBase ht with
  | .singleHt =>
      if nIn < tx.vout.length then
        dsha (serTxOut (tx.vout.getD nIn ⟨0, Script.empty⟩))
      else zeroHash
  | .noneHt => zeroHash
  | .all =>
      dsha (tx.vout.foldl (fun acc o => acc ++ serTxOut o) ByteArray.empty)

/-! ### Sub-hash laws: zero cases (the documented omissions) -/

theorem hashPrevoutsOf_eq_zero_of_acp (tx : Tx) (ht : UInt32)
    (h : Bitcoin.SigHash.htAcp ht = true) :
    hashPrevoutsOf tx ht = zeroHash := by
  simp [hashPrevoutsOf, h]

theorem hashSequenceOf_eq_zero_of_acp (tx : Tx) (ht : UInt32)
    (h : Bitcoin.SigHash.htAcp ht = true) :
    hashSequenceOf tx ht = zeroHash := by
  simp [hashSequenceOf, h]

theorem hashSequenceOf_eq_zero_of_single (tx : Tx) (ht : UInt32)
    (h : Bitcoin.SigHash.htBase ht = Bitcoin.SigHash.HtBase.singleHt) :
    hashSequenceOf tx ht = zeroHash := by
  simp [hashSequenceOf, h]

theorem hashSequenceOf_eq_zero_of_none (tx : Tx) (ht : UInt32)
    (h : Bitcoin.SigHash.htBase ht = Bitcoin.SigHash.HtBase.noneHt) :
    hashSequenceOf tx ht = zeroHash := by
  simp [hashSequenceOf, h]

theorem hashOutputsOf_eq_zero_of_none (tx : Tx) (nIn : Nat) (ht : UInt32)
    (h : Bitcoin.SigHash.htBase ht = Bitcoin.SigHash.HtBase.noneHt) :
    hashOutputsOf tx nIn ht = zeroHash := by
  simp [hashOutputsOf, h]

theorem hashOutputsOf_eq_zero_of_single_oor (tx : Tx) (nIn : Nat) (ht : UInt32)
    (h : Bitcoin.SigHash.htBase ht = Bitcoin.SigHash.HtBase.singleHt)
    (ho : tx.vout.length ≤ nIn) :
    hashOutputsOf tx nIn ht = zeroHash := by
  simp [hashOutputsOf, h, Nat.not_lt.mpr ho]

/-! ### Sub-hash agreement with the vendored implementation -/

theorem bL_hashPrevoutsOf (tx : Tx) (ht : UInt32) :
    Bitcoin.Serialization.bL (hashPrevoutsOf tx ht) =
      Bitcoin.SigHash.hashPrevoutsL tx ht := by
  unfold hashPrevoutsOf Bitcoin.SigHash.hashPrevoutsL
  by_cases h : Bitcoin.SigHash.htAcp ht = true
  · simp [h, bL_zeroHash]
  · rw [if_neg h, if_neg h]
    have hfold : Bitcoin.Serialization.bL
        (tx.vin.foldl (fun acc i => acc ++ serOutpoint i.prevout)
          ByteArray.empty) =
        tx.vin.foldl (fun acc i => acc ++ Bitcoin.SigHash.serOutpointL i.prevout)
          [] := by
      rw [bL_fold_serOutpoint, foldl_append_nil]
    have hd := (bL_dsha
      (tx.vin.foldl (fun acc i => acc ++ serOutpoint i.prevout) ByteArray.empty)).symm
    rw [hfold] at hd
    exact hd

theorem bL_hashSequenceOf (tx : Tx) (ht : UInt32) :
    Bitcoin.Serialization.bL (hashSequenceOf tx ht) =
      Bitcoin.SigHash.hashSequenceL tx ht := by
  unfold hashSequenceOf Bitcoin.SigHash.hashSequenceL
  by_cases h : Bitcoin.SigHash.htAcp ht ∨
      Bitcoin.SigHash.htBase ht = Bitcoin.SigHash.HtBase.singleHt ∨
      Bitcoin.SigHash.htBase ht = Bitcoin.SigHash.HtBase.noneHt
  · simp [h, bL_zeroHash]
  · rw [if_neg h, if_neg h]
    have hfold : Bitcoin.Serialization.bL
        (tx.vin.foldl (fun acc i => acc ++ serU32LE i.sequence)
          ByteArray.empty) =
        tx.vin.foldl (fun acc i => acc ++ Bitcoin.SigHash.serU32L i.sequence) [] := by
      rw [bL_fold_serU32, foldl_append_nil]
    have hd := (bL_dsha
      (tx.vin.foldl (fun acc i => acc ++ serU32LE i.sequence) ByteArray.empty)).symm
    rw [hfold] at hd
    exact hd

theorem bL_hashOutputsOf (tx : Tx) (nIn : Nat) (ht : UInt32) :
    Bitcoin.Serialization.bL (hashOutputsOf tx nIn ht) =
      Bitcoin.SigHash.hashOutputsL tx nIn ht := by
  unfold hashOutputsOf Bitcoin.SigHash.hashOutputsL
  cases hb : Bitcoin.SigHash.htBase ht with
  | singleHt =>
      dsimp only
      by_cases hin : nIn < tx.vout.length
      · rw [if_pos hin, if_pos hin]
        have hfold : Bitcoin.Serialization.bL
            (serTxOut (tx.vout.getD nIn ⟨0, Script.empty⟩)) =
            Bitcoin.SigHash.serTxOutL (tx.vout.getD nIn ⟨0, Script.empty⟩) :=
          bL_serTxOut _
        have hd := (bL_dsha
          (serTxOut (tx.vout.getD nIn ⟨0, Script.empty⟩))).symm
        rw [hfold] at hd
        exact hd
      · rw [if_neg hin, if_neg hin]
        exact bL_zeroHash
  | noneHt =>
      dsimp only
      exact bL_zeroHash
  | all =>
      dsimp only
      have hfold : Bitcoin.Serialization.bL
          (tx.vout.foldl (fun acc o => acc ++ serTxOut o) ByteArray.empty) =
          tx.vout.foldl (fun acc o => acc ++ Bitcoin.SigHash.serTxOutL o) [] := by
        rw [bL_fold_serTxOut, foldl_append_nil]
      have hd := (bL_dsha
        (tx.vout.foldl (fun acc o => acc ++ serTxOut o) ByteArray.empty)).symm
      rw [hfold] at hd
      exact hd

/-! ## The ten-field preimage -/

/-- The BIP 143 witness-v0 preimage fields, in consensus order. -/
structure Preimage where
  version : UInt32
  hashPrevouts : ByteArray
  hashSequence : ByteArray
  outpoint : OutPoint
  scriptCode : ByteArray
  amount : Amount
  sequence : UInt32
  hashOutputs : ByteArray
  lockTime : UInt32
  hashType : UInt32
deriving Repr

/-- The witness-v0 `SignatureHash` preimage byte string:
`version ‖ hashPrevouts ‖ hashSequence ‖ outpoint ‖ scriptCode ‖ amount ‖
nSequence ‖ hashOutputs ‖ nLockTime ‖ hashtype`. -/
def encode (p : Preimage) : ByteArray :=
  serU32LE p.version ++
    p.hashPrevouts ++
    p.hashSequence ++
    serOutpoint p.outpoint ++
    compactSize p.scriptCode.size ++ p.scriptCode ++
    serU64LE (UInt64.ofInt p.amount) ++
    serU32LE p.sequence ++
    p.hashOutputs ++
    serU32LE p.lockTime ++
    serU32LE p.hashType

/-- Inhabitant used by the vendored `getD` for an out-of-range input index.
Its sequence is `0`, matching `Bitcoin.SigHash.bip143MsgL`. -/
def dummyTxIn : TxIn := ⟨OutPoint.null, Script.empty, 0⟩

/-- Compute the ten preimage fields from a transaction, input index,
scriptCode, hashtype and spent amount.  The `nIn`-th input supplies the
outpoint and `nSequence`; `hashPrevouts` / `hashSequence` / `hashOutputs`
come from the three BIP 143 sub-hash rules. -/
def ofTx (tx : Tx) (nIn : Nat) (scriptCode : ByteArray) (ht : UInt32)
    (amount : Amount) : Preimage :=
  { version := tx.version.toUInt32
    hashPrevouts := hashPrevoutsOf tx ht
    hashSequence := hashSequenceOf tx ht
    outpoint := (tx.vin.getD nIn dummyTxIn).prevout
    scriptCode := scriptCode
    amount := amount
    sequence := (tx.vin.getD nIn dummyTxIn).sequence
    hashOutputs := hashOutputsOf tx nIn ht
    lockTime := tx.locktime
    hashType := ht }

/-- The digest is the double-SHA-256 of the preimage. -/
def digest (p : Preimage) : ByteArray := dsha (encode p)

/-- BIP 143 witness-v0 sighash.  For an in-range input this is
`SHA256d(encode (ofTx ...))`; for an out-of-range index it is BIP 143's
zero digest (Core's `assert`-guarded case, totalized). -/
def sighashWitnessV0 (tx : Tx) (nIn : Nat) (scriptCode : ByteArray)
    (ht : UInt32) (amount : Amount) : ByteArray :=
  if tx.vin.length ≤ nIn then zeroHash else digest (ofTx tx nIn scriptCode ht amount)

/-! ### Field projections: what the preimage commits to -/

@[simp] theorem ofTx_version (tx : Tx) (nIn : Nat) (scriptCode : ByteArray)
    (ht : UInt32) (amount : Amount) :
    (ofTx tx nIn scriptCode ht amount).version = tx.version.toUInt32 := rfl

@[simp] theorem ofTx_hashPrevouts (tx : Tx) (nIn : Nat) (scriptCode : ByteArray)
    (ht : UInt32) (amount : Amount) :
    (ofTx tx nIn scriptCode ht amount).hashPrevouts = hashPrevoutsOf tx ht := rfl

@[simp] theorem ofTx_hashSequence (tx : Tx) (nIn : Nat) (scriptCode : ByteArray)
    (ht : UInt32) (amount : Amount) :
    (ofTx tx nIn scriptCode ht amount).hashSequence = hashSequenceOf tx ht := rfl

@[simp] theorem ofTx_outpoint (tx : Tx) (nIn : Nat) (scriptCode : ByteArray)
    (ht : UInt32) (amount : Amount) :
    (ofTx tx nIn scriptCode ht amount).outpoint =
      (tx.vin.getD nIn dummyTxIn).prevout := rfl

@[simp] theorem ofTx_scriptCode (tx : Tx) (nIn : Nat) (scriptCode : ByteArray)
    (ht : UInt32) (amount : Amount) :
    (ofTx tx nIn scriptCode ht amount).scriptCode = scriptCode := rfl

@[simp] theorem ofTx_amount (tx : Tx) (nIn : Nat) (scriptCode : ByteArray)
    (ht : UInt32) (amount : Amount) :
    (ofTx tx nIn scriptCode ht amount).amount = amount := rfl

@[simp] theorem ofTx_sequence (tx : Tx) (nIn : Nat) (scriptCode : ByteArray)
    (ht : UInt32) (amount : Amount) :
    (ofTx tx nIn scriptCode ht amount).sequence =
      (tx.vin.getD nIn dummyTxIn).sequence := rfl

@[simp] theorem ofTx_hashOutputs (tx : Tx) (nIn : Nat) (scriptCode : ByteArray)
    (ht : UInt32) (amount : Amount) :
    (ofTx tx nIn scriptCode ht amount).hashOutputs = hashOutputsOf tx nIn ht := rfl

@[simp] theorem ofTx_lockTime (tx : Tx) (nIn : Nat) (scriptCode : ByteArray)
    (ht : UInt32) (amount : Amount) :
    (ofTx tx nIn scriptCode ht amount).lockTime = tx.locktime := rfl

@[simp] theorem ofTx_hashType (tx : Tx) (nIn : Nat) (scriptCode : ByteArray)
    (ht : UInt32) (amount : Amount) :
    (ofTx tx nIn scriptCode ht amount).hashType = ht := rfl

/-! ## Byte-exact agreement with the vendored BIP 143 preimage and digest -/

theorem bL_encode_ofTx (tx : Tx) (nIn : Nat) (scriptCode : ByteArray)
    (ht : UInt32) (amount : Amount) :
    Bitcoin.Serialization.bL (encode (ofTx tx nIn scriptCode ht amount)) =
      Bitcoin.SigHash.bip143MsgL tx nIn (Bitcoin.Serialization.bL scriptCode)
        ht amount := by
  simp [encode, ofTx, dummyTxIn, Bitcoin.SigHash.bip143MsgL, bL_serU32LE,
    bL_serU64LE, bL_compactSize, bL_serOutpoint, bL_hashPrevoutsOf,
    bL_hashSequenceOf, bL_hashOutputsOf, length_bL,
    Bitcoin.SigHash.serAmountL]

/-- **Strongest exact refinement for an arbitrary model preimage.**  If a
`Preimage` records the same version, BIP 143 sub-hashes, outpoint, sequence,
locktime and amount as a transaction — the sub-hashes compared at the vendored
list level, where they are computed — then `encode` is byte-equal to the
vendored `bip143MsgL`.  These field-agreement hypotheses are the complete
missing context for literal equality; in particular `ofTx` discharges them by
construction (`bL_encode_ofTx`). -/
theorem bL_encode_eq_bip143MsgL (p : Preimage) (tx : Tx) (nIn : Nat)
    (amount : Amount)
    (hversion : p.version = tx.version.toUInt32)
    (hprev : Bitcoin.Serialization.bL p.hashPrevouts =
      Bitcoin.SigHash.hashPrevoutsL tx p.hashType)
    (hseq : Bitcoin.Serialization.bL p.hashSequence =
      Bitcoin.SigHash.hashSequenceL tx p.hashType)
    (houtpoint : p.outpoint = (tx.vin.getD nIn dummyTxIn).prevout)
    (hseq2 : p.sequence = (tx.vin.getD nIn dummyTxIn).sequence)
    (hout : Bitcoin.Serialization.bL p.hashOutputs =
      Bitcoin.SigHash.hashOutputsL tx nIn p.hashType)
    (hlock : p.lockTime = tx.locktime)
    (hamount : p.amount = amount) :
    Bitcoin.Serialization.bL (encode p) =
      Bitcoin.SigHash.bip143MsgL tx nIn
        (Bitcoin.Serialization.bL p.scriptCode) p.hashType amount := by
  simp only [encode, Bitcoin.SigHash.bip143MsgL]
  rw [hversion, houtpoint, hseq2, hlock, hamount]
  simp [dummyTxIn, Bitcoin.Serialization.bL_append, bL_serU32LE, bL_serU64LE,
    bL_compactSize, bL_serOutpoint, length_bL, Bitcoin.SigHash.serAmountL,
    hprev, hseq, hout]

theorem sighashWitnessV0_eq_vendorImpl (tx : Tx) (nIn : Nat)
    (scriptCode : ByteArray) (ht : UInt32) (amount : Amount) :
    sighashWitnessV0 tx nIn scriptCode ht amount =
      Bitcoin.SigHash.signatureHashBip143Impl tx nIn
        (Bitcoin.Serialization.bL scriptCode) ht amount := by
  unfold sighashWitnessV0 Bitcoin.SigHash.signatureHashBip143Impl
  by_cases h : tx.vin.length ≤ nIn
  · simp [h, zeroHash]
  · rw [if_neg h, if_neg h]
    rw [digest]
    apply Bitcoin.Serialization.bL_inj
    rw [(bL_dsha (encode (ofTx tx nIn scriptCode ht amount))).symm,
      bL_encode_ofTx]

/-- The model digest is exactly the vendored interface-level
`signatureHashBip143`, i.e. the BIP 143 `SignatureHash(WITNESS_V0)` used by
the vendored checker wiring. -/
theorem sighashWitnessV0_eq_interface (tx : Tx) (nIn : Nat)
    (scriptCode : ByteArray) (ht : UInt32) (amount : Amount) :
    sighashWitnessV0 tx nIn scriptCode ht amount =
      Bitcoin.SigHash.signatureHashBip143 tx nIn ⟨scriptCode⟩ ht amount := by
  rw [sighashWitnessV0_eq_vendorImpl]
  rfl

theorem sighashWitnessV0_size (tx : Tx) (nIn : Nat) (scriptCode : ByteArray)
    (ht : UInt32) (amount : Amount) :
    (sighashWitnessV0 tx nIn scriptCode ht amount).size = 32 := by
  unfold sighashWitnessV0 digest dsha
  split
  · exact zeroHash_size
  · exact Bitcoin.Crypto.Seam.sha256d_size _

/-- The digest is a function of the preimage; changing any committed field
changes the preimage (digest-level injectivity is not claimed and would need
C1). -/
theorem digest_eq_of_encode_eq (p q : Preimage) (h : encode p = encode q) :
    digest p = digest q := by
  simp [digest, h]

/-! ## The documented BIP 143 omissions (mechanized)

Under ANYONECANPAY, both `hashPrevouts` and `hashSequence` are zero, so the
preimage — and therefore the digest — does not depend on any other input's
outpoint or sequence.  This is a consensus property, not a modelling gap,
but it is recorded here so that no caller reads the digest as a commitment
to the whole transaction. -/

/-- Replace the input list of a transaction, keeping every other field. -/
def withVin (tx : Tx) (vin : List TxIn) : Tx := { tx with vin := vin }

theorem ofTx_withVin_acp (tx : Tx) (vin' : List TxIn) (nIn : Nat)
    (scriptCode : ByteArray) (ht : UInt32) (amount : Amount)
    (hacp : Bitcoin.SigHash.htAcp ht = true)
    (_hlen : vin'.length = tx.vin.length)
    (hinput : vin'.getD nIn dummyTxIn = tx.vin.getD nIn dummyTxIn) :
    ofTx (withVin tx vin') nIn scriptCode ht amount =
      ofTx tx nIn scriptCode ht amount := by
  unfold ofTx withVin
  dsimp only
  rw [hinput]
  simp [hashPrevoutsOf, hashSequenceOf, hashOutputsOf, hacp]

/-- **ANYONECANPAY omission.**  With the ACP bit set, replacing every input
other than the signing input (same length, same `nIn` outpoint/sequence)
leaves the witness-v0 digest unchanged.  In particular the digest does not
commit to other inputs' prevouts or `nSequence` values. -/
theorem sighashWitnessV0_withVin_acp (tx : Tx) (vin' : List TxIn) (nIn : Nat)
    (scriptCode : ByteArray) (ht : UInt32) (amount : Amount)
    (hacp : Bitcoin.SigHash.htAcp ht = true)
    (hlen : vin'.length = tx.vin.length)
    (hinput : vin'.getD nIn dummyTxIn = tx.vin.getD nIn dummyTxIn) :
    sighashWitnessV0 (withVin tx vin') nIn scriptCode ht amount =
      sighashWitnessV0 tx nIn scriptCode ht amount := by
  unfold sighashWitnessV0
  have hlen' : (withVin tx vin').vin.length = tx.vin.length := by
    simp [withVin, hlen]
  by_cases h : tx.vin.length ≤ nIn
  · have h' : (withVin tx vin').vin.length ≤ nIn := by omega
    simp [h, h', zeroHash]
  · have h' : ¬ (withVin tx vin').vin.length ≤ nIn := by omega
    rw [if_neg h', if_neg h]
    exact congrArg digest
      (ofTx_withVin_acp tx vin' nIn scriptCode ht amount hacp hlen hinput)

/-- Without ANYONECANPAY the preimage carries the full prevout fold as its
`hashPrevouts` field (definitional projection).  This is the complementary
fact to `sighashWitnessV0_withVin_acp`: the omission theorem above is
genuinely conditional on the ACP bit, and the non-ACP field is the fold, not
a zero constant.  No injectivity of SHA-256 is claimed. -/
theorem hashPrevoutsOf_of_acp_false (tx : Tx) (ht : UInt32)
    (h : Bitcoin.SigHash.htAcp ht = false) :
    hashPrevoutsOf tx ht =
      dsha (tx.vin.foldl (fun acc i => acc ++ serOutpoint i.prevout)
        ByteArray.empty) := by
  simp [hashPrevoutsOf, h]

end LnLean.Bitcoin.Sighash
