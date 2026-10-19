/-
# HTLC second-stage BIP 143 preimage targets (`PR-05`, `PR-02`)

This module closes the remaining `PR-05` instantiation: the exact-wire BIP 143
preimage of wave 7 (`LnLean/Proofs/Channel/SighashTargets.lean` §12–§13) is
instantiated for the modelled second-stage HTLC transaction `HtlcWire`, and the
HTLC-success / HTLC-timeout `scriptCode` is synthesized from the existing
faithful BOLT 3 templates in `LnLean/Bitcoin/ScriptTemplates.lean`.

## Result

1. `htlcBip143Preimage h scriptCode ht amountSat` is
   `Bip143Preimage.ofTx h.toTx 0 scriptCode ht amountSat`, i.e. the exact-wire
   preimage of the modelled HTLC-timeout / HTLC-success transaction (one input,
   one output, version 2, `nLockTime` 0 or `cltv_expiry`, `nSequence` 0 or 1).
2. `htlcBip143Preimage_eq_bip143MsgL` proves the requested byte equality

   ```text
   bL (htlcBip143Preimage h scriptCode ht amount).preimageBytes
     = Bitcoin.SigHash.bip143MsgL h.toTx 0 (bL scriptCode) ht amount
   ```

   for **every** `HtlcWire`, `scriptCode`, hashtype and amount.  The proof is the
   wave-7 transaction-derived theorem `preimageBytes_eq_bip143MsgL_ofTx`; no
   field is assumed.  `htlcBip143Preimage_toPreimage` is the
   `Bip143Preimage.ofTx`/`toPreimage` bridge to the model `Preimage`.
3. `htlcBip143Preimage_digest_eq_sighashWitnessV0` transfers the byte equality
   to the digest: the model digest of the bridged preimage is the vendored
   `signatureHashBip143Impl` of the same HTLC transaction.
4. `htlc_arbitrary_preimage_field_agreement` retains the arbitrary-preimage
   form: for an arbitrary `Bip143Preimage` the same vendor equality holds under
   exactly the eight field-agreement hypotheses of
   `LnLean.Bitcoin.Sighash.bL_encode_eq_bip143MsgL` (version, the three
   sub-hashes, outpoint, `nSequence`, `nLockTime`, amount).  Nothing is hidden.
5. `HtlcSpend` records the BOLT 3 second-stage context (commitment outpoint,
   anchor flag, revocation-key HASH160 image, payment-hash HASH160 image, both
   HTLC keys, `cltv_expiry`, gross HTLC value, second-stage fee and the output
   script).  `successWire`/`timeoutWire` build the BOLT 3 transaction skeleton;
   `successScriptCode`/`timeoutScriptCode` are exactly
   `receivedHtlcWitnessScript` / `offeredHtlcWitnessScript`, i.e. the witness
   script of the spent HTLC output, which is BIP 143's P2WSH `scriptCode`
   (no `FindAndDelete`, no `OP_CODESEPARATOR` removal, CompactSize-prefixed by
   the preimage serializer).  Exact sizes are 143 and 136 bytes for 20-byte
   digest images and 33-byte keys, and both satisfy the vendored
   `witnessScriptSizeOk`.
6. `Seam.htlcBranchScript` is proved **not** faithful: it starts with
   `OP_IF OP_HASH160`, whereas both BOLT 3 HTLC witness scripts start with
   `OP_DUP OP_HASH160`, and the second-stage output witness script starts with
   `OP_IF <33-byte-push>`.  It also collapses `cltv = 0` and `cltv = 256` to
   the same script (`Height.toUInt8` truncates), so it cannot be a CScriptNum
   CLTV branch.  The exact missing-script condition is therefore stated and the
   `scriptCode` remains an explicit parameter of the main theorem.
7. Display-order txid conversion is explicit: `reverseBytes` / `displayTxid` /
   `internalTxid`, involution, and the byte slice of the preimage at offset 68
   proved equal to the **internal-order** commitment txid.  If a caller holds
   the RPC/display hex txid, it must apply `internalTxid` (one byte reversal)
   before assigning `HtlcWire.commitmentTxid`; the preimage and the vendored
   encoder insert the field verbatim, never reversed.

## Anchors

* BOLT 3 §"Offered HTLC Outputs" (`refs/bolts/03-transactions.md:199-251`),
  §"Received HTLC Outputs" (`:251-303`), §"HTLC-Timeout and HTLC-Success
  Transactions" (`:355-384`).
* BIP 143 §"Signature Hash" and Core `src/script/interpreter.cpp`
  `SignatureHash(WITNESS_V0)` (`:1633-1670`): P2WSH `scriptCode` is the witness
  script itself, serialized with its CompactSize length.
* Vendor: `Bitcoin.SigHash.bip143MsgL`, `signatureHashBip143Impl`,
  `witnessScriptSizeOk` (`vendor/btc-lean-core/Bitcoin/SigHash/Digest.lean`).
* Model: `LnLean.Proofs.Channel.SighashTargets` (`HtlcWire`,
  `Bip143Preimage`), `LnLean.Bitcoin.ScriptTemplates`
  (`offeredHtlcWitnessScript`, `receivedHtlcWitnessScript`),
  `LnLean.Bitcoin.Seam` (`htlcBranchScript`, `toLocalScriptFull`).

## What is not proved

* The outpoint txid is not derived from a full commitment transaction here: the
  caller supplies `commitmentTxid`.  When it is the txid of a
  `CommitmentWire`, that is `SHA256d` of the witness-free commitment bytes
  (§12/§13); the txid itself is not recomputed in this module.
* `revocationKeyHash160` and `paymentHash160` are explicit 20-byte images of
  `RIPEMD160(SHA256(revocationpubkey))` / `RIPEMD160(payment_hash)`.  The model
  has no RIPEMD160 bridge (`PrimitiveModel.hash160` is the abstract HASH160), so
  the image relation is a context hypothesis, not a computed value.
* `cltv_expiry` uses the scaffold's fixed four-byte little-endian push
  (`pushScriptNum32`), not minimal `CScriptNum`.  This is the existing
  `ScriptTemplates` limitation; the size 143 is the fixed-width size.
* The `HtlcSpend` convenience instantiation uses the **anchor-variant** HTLC
  witness scripts of `ScriptTemplates` (the only BOLT 3 HTLC templates in the
  tree); non-anchor HTLC witness scripts are not synthesized.  The generic
  `htlcBip143Preimage_eq_bip143MsgL` theorem is independent of that choice: it
  holds for every `scriptCode` byte string.
* The second-stage output `scriptPubKey` (P2WSH over the BOLT 3
  `OP_IF <revocationpubkey> OP_ELSE <to_self_delay> ... OP_CHECKSIG` witness
  script, i.e. `toLocalScriptFull`) is an explicit wire field.  Its 34-byte
  P2WSH shape is proved under the hypothesis that its program is
  `SHA256(scriptCode)`.
* No consensus/validity claim: signatures, amounts, fees, transaction
  confirmation and P2WSH execution are outside this module.
-/

import LnLean.Proofs.Channel.SighashTargets
import LnLean.Proofs.Bitcoin.ScriptProps

namespace LnLean.Proofs.Channel.HtlcPreimageTargets

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open LnLean
open LnLean.Channel
open LnLean.Bitcoin
open LnLean.Proofs.Channel.SighashTargets
open Bitcoin.Data
open Bitcoin.Serialization

/-! ## 1. The exact HTLC second-stage preimage -/

/-- The BIP 143 witness-v0 preimage of the modelled HTLC-timeout / HTLC-success
transaction.  `HtlcWire.toTx` has exactly one input, so the signing input index
is `0`; the wire's outpoint index (`commitmentOutputIndex`) selects the spent
commitment HTLC output. -/
def htlcBip143Preimage (h : HtlcWire) (scriptCode : ByteArray) (ht : UInt32)
    (amountSat : UInt64) : Bip143Preimage :=
  Bip143Preimage.ofTx h.toTx 0 scriptCode ht amountSat

/-- The preimage bridge to the model `LnLean.Bitcoin.Sighash.Preimage`. -/
theorem htlcBip143Preimage_toPreimage (h : HtlcWire) (scriptCode : ByteArray)
    (ht : UInt32) (amountSat : UInt64) :
    (htlcBip143Preimage h scriptCode ht amountSat).toPreimage =
      LnLean.Bitcoin.Sighash.ofTx h.toTx 0 scriptCode ht
        (amountSat.toNat : Int) :=
  Bip143Preimage.toPreimage_ofTx h.toTx 0 scriptCode ht amountSat

/-- Version field of the HTLC preimage. -/
@[simp] theorem htlcBip143Preimage_version (h : HtlcWire) (scriptCode : ByteArray)
    (ht : UInt32) (amountSat : UInt64) :
    (htlcBip143Preimage h scriptCode ht amountSat).version = h.version := rfl

/-- Outpoint txid field: the commitment txid in consensus-internal byte order. -/
@[simp] theorem htlcBip143Preimage_outpointTxid (h : HtlcWire)
    (scriptCode : ByteArray) (ht : UInt32) (amountSat : UInt64) :
    (htlcBip143Preimage h scriptCode ht amountSat).outpointTxid =
      h.commitmentTxid := rfl

/-- Outpoint index field: the index of the spent commitment HTLC output. -/
@[simp] theorem htlcBip143Preimage_outpointIndex (h : HtlcWire)
    (scriptCode : ByteArray) (ht : UInt32) (amountSat : UInt64) :
    (htlcBip143Preimage h scriptCode ht amountSat).outpointIndex =
      h.commitmentOutputIndex := rfl

/-- `nSequence` field of the HTLC preimage. -/
@[simp] theorem htlcBip143Preimage_sequence (h : HtlcWire) (scriptCode : ByteArray)
    (ht : UInt32) (amountSat : UInt64) :
    (htlcBip143Preimage h scriptCode ht amountSat).sequence = h.sequence := rfl

/-- `nLockTime` field of the HTLC preimage. -/
@[simp] theorem htlcBip143Preimage_locktime (h : HtlcWire) (scriptCode : ByteArray)
    (ht : UInt32) (amountSat : UInt64) :
    (htlcBip143Preimage h scriptCode ht amountSat).locktime = h.locktime := rfl

/-- Spent amount field (the gross HTLC value carried by the commitment output). -/
@[simp] theorem htlcBip143Preimage_amountSat (h : HtlcWire) (scriptCode : ByteArray)
    (ht : UInt32) (amountSat : UInt64) :
    (htlcBip143Preimage h scriptCode ht amountSat).amountSat = amountSat := rfl

/-- Sighash-type field. -/
@[simp] theorem htlcBip143Preimage_sighashType (h : HtlcWire) (scriptCode : ByteArray)
    (ht : UInt32) (amountSat : UInt64) :
    (htlcBip143Preimage h scriptCode ht amountSat).sighashType = ht := rfl

/-- The wire outpoint, sequence, locktime, version and amount are exactly the
preimage fields: no display-order reversal is inserted, and the preimage is a
function of the exact modelled transaction. -/
theorem htlcBip143Preimage_wire_fields (h : HtlcWire) (scriptCode : ByteArray)
    (ht : UInt32) (amountSat : UInt64) :
    (htlcBip143Preimage h scriptCode ht amountSat).version = h.version ∧
    (htlcBip143Preimage h scriptCode ht amountSat).outpointTxid =
      h.commitmentTxid ∧
    (htlcBip143Preimage h scriptCode ht amountSat).outpointIndex =
      h.commitmentOutputIndex ∧
    (htlcBip143Preimage h scriptCode ht amountSat).sequence = h.sequence ∧
    (htlcBip143Preimage h scriptCode ht amountSat).locktime = h.locktime ∧
    (htlcBip143Preimage h scriptCode ht amountSat).amountSat = amountSat ∧
    (htlcBip143Preimage h scriptCode ht amountSat).sighashType = ht := by
  simp

/-- **Target byte equality.**  The exact-wire HTLC preimage is byte-equal to
the vendored BIP 143 preimage of the modelled HTLC transaction, at the list
level where the vendor encoder computes.  The amount is lifted to the signed
`Amount` exactly as in `Bip143Preimage.ofTx`. -/
theorem htlcBip143Preimage_eq_bip143MsgL (h : HtlcWire) (scriptCode : ByteArray)
    (ht : UInt32) (amountSat : UInt64) :
    bL (htlcBip143Preimage h scriptCode ht amountSat).preimageBytes =
      Bitcoin.SigHash.bip143MsgL h.toTx 0 (bL scriptCode) ht
        (amountSat.toNat : Int) :=
  Bip143Preimage.preimageBytes_eq_bip143MsgL_ofTx h.toTx 0 scriptCode ht amountSat

/-- `ByteArray`-level form against the model encoder. -/
theorem htlcBip143Preimage_bytes_eq_encode (h : HtlcWire) (scriptCode : ByteArray)
    (ht : UInt32) (amountSat : UInt64) :
    (htlcBip143Preimage h scriptCode ht amountSat).preimageBytes =
      LnLean.Bitcoin.Sighash.encode
        (LnLean.Bitcoin.Sighash.ofTx h.toTx 0 scriptCode ht
          (amountSat.toNat : Int)) :=
  Bip143Preimage.preimageBytes_eq_encode_ofTx h.toTx 0 scriptCode ht amountSat

/-- The model digest of the bridged HTLC preimage is exactly the vendored
`signatureHashBip143Impl` of the same HTLC transaction.  The signing input is
in range by construction (`HtlcWire.toTx` has one input). -/
theorem htlcBip143Preimage_digest_eq_sighashWitnessV0 (h : HtlcWire)
    (scriptCode : ByteArray) (ht : UInt32) (amountSat : UInt64) :
    LnLean.Bitcoin.Sighash.digest
        (htlcBip143Preimage h scriptCode ht amountSat).toPreimage =
      Bitcoin.SigHash.signatureHashBip143Impl h.toTx 0 (bL scriptCode) ht
        (amountSat.toNat : Int) := by
  rw [htlcBip143Preimage_toPreimage]
  exact Bip143Preimage.digest_eq_sighashWitnessV0_ofTx h.toTx 0 scriptCode ht
    amountSat (by simp [HtlcWire.toTx])

/-! ### 1.1 The arbitrary-preimage field-agreement form (retained) -/

/-- **Arbitrary-preimage refinement retained.**  For an arbitrary exact-wire
preimage `p`, literal equality to the vendored encoder of the modelled HTLC
transaction holds under the eight field-agreement hypotheses of
`LnLean.Bitcoin.Sighash.bL_encode_eq_bip143MsgL`.  These are exactly the
transaction context the preimage must record; `htlcBip143Preimage` discharges
all of them by construction. -/
theorem htlc_arbitrary_preimage_field_agreement (p : Bip143Preimage) (h : HtlcWire)
    (amount : Bitcoin.Data.Amount)
    (hversion : p.version = h.version)
    (hprev : bL p.hashPrevouts =
      Bitcoin.SigHash.hashPrevoutsL h.toTx p.sighashType)
    (hseq : bL p.hashSequence =
      Bitcoin.SigHash.hashSequenceL h.toTx p.sighashType)
    (houtpoint : p.outpointTxid = h.commitmentTxid ∧
      p.outpointIndex = h.commitmentOutputIndex)
    (hseq2 : p.sequence = h.sequence)
    (hout : bL p.hashOutputs =
      Bitcoin.SigHash.hashOutputsL h.toTx 0 p.sighashType)
    (hlock : p.locktime = h.locktime)
    (hamount : (p.amountSat.toNat : Int) = amount) :
    bL p.preimageBytes =
      Bitcoin.SigHash.bip143MsgL h.toTx 0 (bL p.scriptCode) p.sighashType amount := by
  rw [Bip143Preimage.preimageBytes_eq_encode]
  refine LnLean.Bitcoin.Sighash.bL_encode_eq_bip143MsgL p.toPreimage h.toTx 0 amount
    hversion hprev hseq ?_ hseq2 hout hlock hamount
  rw [Bip143Preimage.toPreimage, HtlcWire.toTx]
  simp [houtpoint.1, houtpoint.2]

/-! ## 2. Display-order txid conversion -/

/-- Byte reversal of a `ByteArray` (the BIP 143 / `uint256::GetHex` display
conversion).  Consensus-internal txids are inserted into the preimage verbatim;
RPC/display hex is their byte reverse. -/
def reverseBytes (b : ByteArray) : ByteArray :=
  byteList (bL b).reverse

@[simp] theorem bL_byteList (l : List UInt8) : bL (byteList l) = l := by
  simp [byteList, Bitcoin.Serialization.bL]

@[simp] theorem bL_reverseBytes (b : ByteArray) :
    bL (reverseBytes b) = (bL b).reverse := by
  simp [reverseBytes]

theorem reverseBytes_size (b : ByteArray) :
    (reverseBytes b).size = b.size := by
  have h := congrArg List.length (bL_reverseBytes b)
  simpa [Bitcoin.Serialization.bL] using h

theorem reverseBytes_involutive (b : ByteArray) :
    reverseBytes (reverseBytes b) = b := by
  apply Bitcoin.Serialization.bL_inj
  simp

/-- The display-order (RPC hex) txid of a consensus-internal txid. -/
def displayTxid (internal : ByteArray) : ByteArray := reverseBytes internal

/-- Conversion from a display-order txid to the consensus-internal form used by
the preimage. -/
def internalTxid (display : ByteArray) : ByteArray := reverseBytes display

theorem internalTxid_displayTxid (internal : ByteArray) :
    internalTxid (displayTxid internal) = internal :=
  reverseBytes_involutive internal

theorem displayTxid_internalTxid (display : ByteArray) :
    displayTxid (internalTxid display) = display :=
  reverseBytes_involutive display

theorem displayTxid_size (internal : ByteArray) :
    (displayTxid internal).size = internal.size :=
  reverseBytes_size internal

theorem internalTxid_size (display : ByteArray) :
    (internalTxid display).size = display.size :=
  reverseBytes_size display

/-! ### 2.1 The preimage field at byte offset 68 is the internal-order txid -/

/-- Drop/take arithmetic on a right-associated five-part byte list: the field
after a 4-byte version, two 32-byte sub-hashes and a 32-byte outpoint starts at
offset 68. -/
theorem drop68_take32_of_parts {α : Type} (a b c d rest : List α)
    (ha : a.length = 4) (hb : b.length = 32) (hc : c.length = 32)
    (hd : d.length = 32) :
    ((a ++ b ++ c ++ d ++ rest).drop 68).take 32 = d := by
  rw [List.drop_append_of_le_length (by simp [ha, hb, hc, hd] <;> omega)]
  rw [show (68 : Nat) = ((a ++ b) ++ c).length by simp [ha, hb, hc] <;> omega]
  rw [List.drop_append_length]
  rw [show (32 : Nat) = d.length by omega, List.take_left]

/-- The 4-byte outpoint index falls at offset 100. -/
theorem drop100_take4_of_parts {α : Type} (a b c d e rest : List α)
    (ha : a.length = 4) (hb : b.length = 32) (hc : c.length = 32)
    (hd : d.length = 32) (he : e.length = 4) :
    ((a ++ b ++ c ++ d ++ e ++ rest).drop 100).take 4 = e := by
  rw [List.drop_append_of_le_length (by simp [ha, hb, hc, hd, he] <;> omega)]
  rw [show (100 : Nat) = (((a ++ b) ++ c) ++ d).length by
    simp [ha, hb, hc, hd] <;> omega]
  rw [List.drop_append_length]
  rw [show (4 : Nat) = e.length by omega, List.take_left]

/-- The preimage field is the 32-byte txid inserted verbatim. -/
theorem preimageBytes_drop68_take32 (p : Bip143Preimage)
    (hp : p.hashPrevouts.size = 32) (hq : p.hashSequence.size = 32)
    (ho : p.outpointTxid.size = 32) :
    ((bL p.preimageBytes).drop 68).take 32 = bL p.outpointTxid := by
  rw [Bip143Preimage.preimageBytes_fields]
  simpa only [List.append_assoc] using
    drop68_take32_of_parts (Bitcoin.SigHash.serU32L p.version)
    (bL p.hashPrevouts) (bL p.hashSequence) (bL p.outpointTxid)
    (Bitcoin.SigHash.serU32L p.outpointIndex ++
      Bitcoin.Serialization.encCSL p.scriptCode.size ++ bL p.scriptCode ++
      Bitcoin.SigHash.serU64L p.amountSat ++
      Bitcoin.SigHash.serU32L p.sequence ++ bL p.hashOutputs ++
      Bitcoin.SigHash.serU32L p.locktime ++ Bitcoin.SigHash.serU32L p.sighashType)
    (by simp [Bitcoin.SigHash.serU32L])
    (by rw [LnLean.Bitcoin.Sighash.length_bL]; exact hp)
    (by rw [LnLean.Bitcoin.Sighash.length_bL]; exact hq)
    (by rw [LnLean.Bitcoin.Sighash.length_bL]; exact ho)

/-- The 4-byte outpoint index at offset 100, little-endian. -/
theorem preimageBytes_drop100_take4 (p : Bip143Preimage)
    (hp : p.hashPrevouts.size = 32) (hq : p.hashSequence.size = 32)
    (ho : p.outpointTxid.size = 32) :
    ((bL p.preimageBytes).drop 100).take 4 =
      Bitcoin.SigHash.serU32L p.outpointIndex := by
  rw [Bip143Preimage.preimageBytes_fields]
  simpa only [List.append_assoc] using
    drop100_take4_of_parts (Bitcoin.SigHash.serU32L p.version)
    (bL p.hashPrevouts) (bL p.hashSequence) (bL p.outpointTxid)
    (Bitcoin.SigHash.serU32L p.outpointIndex)
    (Bitcoin.Serialization.encCSL p.scriptCode.size ++ bL p.scriptCode ++
      Bitcoin.SigHash.serU64L p.amountSat ++
      Bitcoin.SigHash.serU32L p.sequence ++ bL p.hashOutputs ++
      Bitcoin.SigHash.serU32L p.locktime ++ Bitcoin.SigHash.serU32L p.sighashType)
    (by simp [Bitcoin.SigHash.serU32L])
    (by rw [LnLean.Bitcoin.Sighash.length_bL]; exact hp)
    (by rw [LnLean.Bitcoin.Sighash.length_bL]; exact hq)
    (by rw [LnLean.Bitcoin.Sighash.length_bL]; exact ho)
    (by simp [Bitcoin.SigHash.serU32L])

/-- The three BIP 143 sub-hash fields of an `ofTx`-derived preimage are 32 bytes
(vendored sub-hash or the zero hash). -/
theorem hashPrevoutsOf_size (tx : Bitcoin.Data.Tx) (ht : UInt32) :
    (LnLean.Bitcoin.Sighash.hashPrevoutsOf tx ht).size = 32 := by
  unfold LnLean.Bitcoin.Sighash.hashPrevoutsOf
  split
  · exact LnLean.Bitcoin.Sighash.zeroHash_size
  · exact Bitcoin.Crypto.Seam.sha256d_size _

theorem hashSequenceOf_size (tx : Bitcoin.Data.Tx) (ht : UInt32) :
    (LnLean.Bitcoin.Sighash.hashSequenceOf tx ht).size = 32 := by
  unfold LnLean.Bitcoin.Sighash.hashSequenceOf
  split
  · exact LnLean.Bitcoin.Sighash.zeroHash_size
  · exact Bitcoin.Crypto.Seam.sha256d_size _

theorem hashOutputsOf_size (tx : Bitcoin.Data.Tx) (nIn : Nat) (ht : UInt32) :
    (LnLean.Bitcoin.Sighash.hashOutputsOf tx nIn ht).size = 32 := by
  unfold LnLean.Bitcoin.Sighash.hashOutputsOf
  split
  · split
    · exact Bitcoin.Crypto.Seam.sha256d_size _
    · exact LnLean.Bitcoin.Sighash.zeroHash_size
  · exact LnLean.Bitcoin.Sighash.zeroHash_size
  · exact Bitcoin.Crypto.Seam.sha256d_size _

/-- The HTLC preimage's 32-byte outpoint field at offset 68 is the internal
order commitment txid (never reversed). -/
theorem htlcBip143Preimage_outpoint_bytes (h : HtlcWire) (scriptCode : ByteArray)
    (ht : UInt32) (amountSat : UInt64) (htx : h.commitmentTxid.size = 32) :
    ((bL (htlcBip143Preimage h scriptCode ht amountSat).preimageBytes).drop 68).take
        32 = bL h.commitmentTxid := by
  rw [preimageBytes_drop68_take32 _ (hashPrevoutsOf_size _ _)
    (hashSequenceOf_size _ _) (by simp [htlcBip143Preimage, Bip143Preimage.ofTx,
      HtlcWire.toTx, htx])]
  simp [htlcBip143Preimage, Bip143Preimage.ofTx, HtlcWire.toTx]

/-- The 4-byte outpoint index field at offset 100 is the wire index in
little-endian. -/
theorem htlcBip143Preimage_outpointIndex_bytes (h : HtlcWire)
    (scriptCode : ByteArray) (ht : UInt32) (amountSat : UInt64)
    (htx : h.commitmentTxid.size = 32) :
    ((bL (htlcBip143Preimage h scriptCode ht amountSat).preimageBytes).drop
        100).take 4 = Bitcoin.SigHash.serU32L h.commitmentOutputIndex := by
  rw [preimageBytes_drop100_take4 _ (hashPrevoutsOf_size _ _)
    (hashSequenceOf_size _ _) (by simp [htlcBip143Preimage, Bip143Preimage.ofTx,
      HtlcWire.toTx, htx])]
  simp [htlcBip143Preimage, Bip143Preimage.ofTx, HtlcWire.toTx]

/-- The **same** slice of the vendored encoder.  This is the byte-order tie
between the model preimage and `Bitcoin.SigHash.bip143MsgL`. -/
theorem htlcBip143MsgL_outpoint_bytes (h : HtlcWire) (scriptCode : ByteArray)
    (ht : UInt32) (amountSat : UInt64) (htx : h.commitmentTxid.size = 32) :
    ((Bitcoin.SigHash.bip143MsgL h.toTx 0 (bL scriptCode) ht
        (amountSat.toNat : Int)).drop 68).take 32 = bL h.commitmentTxid := by
  rw [← htlcBip143Preimage_eq_bip143MsgL]
  exact htlcBip143Preimage_outpoint_bytes h scriptCode ht amountSat htx

/-- **Display-order conversion.**  If a caller holds the RPC/display-order txid
`hexTxid` of the commitment transaction, the preimage's outpoint field is its
byte reverse.  Equivalently, the internal-order field must be
`internalTxid hexTxid`, not `hexTxid`. -/
theorem htlcBip143Preimage_outpoint_of_display_txid (h : HtlcWire)
    (scriptCode : ByteArray) (ht : UInt32) (amountSat : UInt64)
    (hexTxid : ByteArray) (hsize : hexTxid.size = 32)
    (hdisplay : h.commitmentTxid = displayTxid hexTxid) :
    ((bL (htlcBip143Preimage h scriptCode ht amountSat).preimageBytes).drop 68).take
        32 = (bL hexTxid).reverse := by
  rw [htlcBip143Preimage_outpoint_bytes h scriptCode ht amountSat]
  · simp [hdisplay, displayTxid, bL_reverseBytes]
  · rw [hdisplay, displayTxid, reverseBytes_size, hsize]

/-- An asymmetric 32-byte value witnesses that display conversion is not the
identity. -/
def vectorAsymmetricTxid : ByteArray :=
  byteList ([0x01] ++ List.replicate 30 0x00 ++ [0x02])

theorem vectorAsymmetricTxid_size : vectorAsymmetricTxid.size = 32 := by
  decide

theorem displayTxid_not_identity_witness :
    displayTxid vectorAsymmetricTxid ≠ vectorAsymmetricTxid := by
  decide

/-! ## 3. BOLT 3 HTLC-success / HTLC-timeout `scriptCode` synthesis -/

/-- The BOLT 3 second-stage context.  `successWire` is the HTLC-success
transaction (spends a *received* HTLC output), `timeoutWire` the HTLC-timeout
transaction (spends an *offered* HTLC output). -/
structure HtlcSpend where
  /-- Internal-order txid of the commitment transaction. -/
  commitmentTxid : ByteArray
  /-- Index of the spent HTLC output in that commitment transaction. -/
  commitmentOutputIndex : UInt32
  /-- `option_anchors`: selects `nSequence = 1` instead of `0`.  The
  synthesized scriptCode uses the anchor-variant templates either way. -/
  anchorOutputs : Bool
  /-- 20-byte `RIPEMD160(SHA256(revocationpubkey))` image. -/
  revocationKeyHash160 : ByteArray
  /-- 20-byte `RIPEMD160(payment_hash)` image. -/
  paymentHash160 : ByteArray
  /-- `remote_htlcpubkey` (33-byte compressed key). -/
  remoteHtlcKey : PubKey
  /-- `local_htlcpubkey` (33-byte compressed key). -/
  localHtlcKey : PubKey
  /-- `cltv_expiry` (`u32` in BOLT 2). -/
  cltvExpiry : UInt32
  /-- Gross value of the spent commitment HTLC output (`amount_msat / 1000`). -/
  amountSat : UInt64
  /-- Second-stage fee withheld from the HTLC value. -/
  secondStageFeeSat : Nat
  /-- `scriptPubKey` of the HTLC-timeout/success output (P2WSH over the
  second-stage witness script, `toLocalScriptFull` shape). -/
  outputScriptPubKey : ByteArray
deriving Repr

/-- Well-formedness of the scriptCode synthesis inputs: 32-byte txid, 20-byte
hash images, 33-byte keys, and a fee not exceeding the HTLC value. -/
def HtlcSpend.WellFormed (s : HtlcSpend) : Prop :=
  s.commitmentTxid.size = 32 ∧
  s.revocationKeyHash160.size = 20 ∧
  s.paymentHash160.size = 20 ∧
  s.remoteHtlcKey.bytes.size = 33 ∧
  s.localHtlcKey.bytes.size = 33 ∧
  s.secondStageFeeSat ≤ s.amountSat.toNat

/-- `nSequence`: 1 with `option_anchors`, 0 otherwise (BOLT 3 :363). -/
def HtlcSpend.sequence (s : HtlcSpend) : UInt32 :=
  if s.anchorOutputs then 1 else 0

/-- Value paid by the second-stage output: gross HTLC value minus the
second-stage fee. -/
def HtlcSpend.paidValueSat (s : HtlcSpend) : UInt64 :=
  UInt64.ofNat (s.amountSat.toNat - s.secondStageFeeSat)

/-- The HTLC-success transaction skeleton: version 2, one input (the received
HTLC output), one output, `nLockTime = 0`. -/
def HtlcSpend.successWire (s : HtlcSpend) : HtlcWire :=
  { version := 2
    commitmentTxid := s.commitmentTxid
    commitmentOutputIndex := s.commitmentOutputIndex
    sequence := s.sequence
    valueSat := s.paidValueSat
    scriptPubKey := s.outputScriptPubKey
    locktime := 0 }

/-- The HTLC-timeout transaction skeleton: version 2, one input (the offered
HTLC output), one output, `nLockTime = cltv_expiry`. -/
def HtlcSpend.timeoutWire (s : HtlcSpend) : HtlcWire :=
  { s.successWire with locktime := s.cltvExpiry }

/-- P2WSH `scriptCode` of an HTLC-success spend: the witness script of the
**received** HTLC output (BOLT 3 :251-290). -/
def HtlcSpend.successScriptCode (s : HtlcSpend) : ByteArray :=
  (receivedHtlcWitnessScript s.revocationKeyHash160 s.paymentHash160
    s.remoteHtlcKey s.localHtlcKey s.cltvExpiry.toNat).bytes

/-- P2WSH `scriptCode` of an HTLC-timeout spend: the witness script of the
**offered** HTLC output (BOLT 3 :199-236). -/
def HtlcSpend.timeoutScriptCode (s : HtlcSpend) : ByteArray :=
  (offeredHtlcWitnessScript s.revocationKeyHash160 s.paymentHash160
    s.remoteHtlcKey s.localHtlcKey).bytes

/-- The HTLC-success preimage. -/
def HtlcSpend.successPreimage (s : HtlcSpend) (ht : UInt32) : Bip143Preimage :=
  htlcBip143Preimage s.successWire s.successScriptCode ht s.amountSat

/-- The HTLC-timeout preimage. -/
def HtlcSpend.timeoutPreimage (s : HtlcSpend) (ht : UInt32) : Bip143Preimage :=
  htlcBip143Preimage s.timeoutWire s.timeoutScriptCode ht s.amountSat

/-! ### 3.1 Wire-shape theorems -/

theorem HtlcSpend.sequence_eq_one_of_anchor (s : HtlcSpend)
    (h : s.anchorOutputs = true) : s.sequence = 1 := by
  simp [HtlcSpend.sequence, h]

theorem HtlcSpend.sequence_eq_zero_of_no_anchor (s : HtlcSpend)
    (h : s.anchorOutputs = false) : s.sequence = 0 := by
  simp [HtlcSpend.sequence, h]

theorem HtlcSpend.successWire_version (s : HtlcSpend) :
    s.successWire.version = 2 := rfl

theorem HtlcSpend.successWire_locktime (s : HtlcSpend) :
    s.successWire.locktime = 0 := rfl

theorem HtlcSpend.timeoutWire_version (s : HtlcSpend) :
    s.timeoutWire.version = 2 := rfl

theorem HtlcSpend.timeoutWire_locktime (s : HtlcSpend) :
    s.timeoutWire.locktime = s.cltvExpiry := rfl

theorem HtlcSpend.successWire_sequence (s : HtlcSpend) :
    s.successWire.sequence = s.sequence := rfl

theorem HtlcSpend.timeoutWire_sequence (s : HtlcSpend) :
    s.timeoutWire.sequence = s.sequence := rfl

theorem HtlcSpend.successWire_vin_length (s : HtlcSpend) :
    s.successWire.toTx.vin.length = 1 := rfl

theorem HtlcSpend.successWire_vout_length (s : HtlcSpend) :
    s.successWire.toTx.vout.length = 1 := rfl

theorem HtlcSpend.timeoutWire_vin_length (s : HtlcSpend) :
    s.timeoutWire.toTx.vin.length = 1 := rfl

/-- The two transactions are the same skeleton except for the BOLT 3
`nLockTime`: 0 for success, `cltv_expiry` for timeout. -/
theorem HtlcSpend.timeoutWire_locktime_ne_success (s : HtlcSpend)
    (h : s.cltvExpiry ≠ 0) :
    s.timeoutWire.locktime ≠ s.successWire.locktime := by
  simp [HtlcSpend.timeoutWire, HtlcSpend.successWire, h]

/-- The success `scriptCode` is exactly the received-HTLC witness script. -/
theorem HtlcSpend.successScriptCode_is_received (s : HtlcSpend) :
    s.successScriptCode =
      (receivedHtlcWitnessScript s.revocationKeyHash160 s.paymentHash160
        s.remoteHtlcKey s.localHtlcKey s.cltvExpiry.toNat).bytes := rfl

/-- The timeout `scriptCode` is exactly the offered-HTLC witness script. -/
theorem HtlcSpend.timeoutScriptCode_is_offered (s : HtlcSpend) :
    s.timeoutScriptCode =
      (offeredHtlcWitnessScript s.revocationKeyHash160 s.paymentHash160
        s.remoteHtlcKey s.localHtlcKey).bytes := rfl

/-! ### 3.2 scriptCode sizes and BIP 143's 10,000-byte rule -/

theorem HtlcSpend.successScriptCode_size (s : HtlcSpend) (hw : s.WellFormed) :
    s.successScriptCode.size = 143 := by
  obtain ⟨_, hr, hp, hk1, hk2, _⟩ := hw
  simpa [HtlcSpend.successScriptCode] using
    LnLean.Proofs.Bitcoin.ScriptProps.receivedHtlcWitnessScript_size
      s.revocationKeyHash160 s.paymentHash160 s.remoteHtlcKey s.localHtlcKey
      s.cltvExpiry.toNat hr hp hk1 hk2

theorem HtlcSpend.timeoutScriptCode_size (s : HtlcSpend) (hw : s.WellFormed) :
    s.timeoutScriptCode.size = 136 := by
  obtain ⟨_, hr, hp, hk1, hk2, _⟩ := hw
  simpa [HtlcSpend.timeoutScriptCode] using
    LnLean.Proofs.Bitcoin.ScriptProps.offeredHtlcWitnessScript_size
      s.revocationKeyHash160 s.paymentHash160 s.remoteHtlcKey s.localHtlcKey
      hr hp hk1 hk2

theorem HtlcSpend.successScriptCode_size_ok (s : HtlcSpend) (hw : s.WellFormed) :
    Bitcoin.SigHash.witnessScriptSizeOk (bL s.successScriptCode) = true := by
  have h := HtlcSpend.successScriptCode_size s hw
  have hlen : (bL s.successScriptCode).length = 143 := by
    simpa [Bitcoin.Serialization.bL] using h
  simp [Bitcoin.SigHash.witnessScriptSizeOk, hlen]

theorem HtlcSpend.timeoutScriptCode_size_ok (s : HtlcSpend) (hw : s.WellFormed) :
    Bitcoin.SigHash.witnessScriptSizeOk (bL s.timeoutScriptCode) = true := by
  have h := HtlcSpend.timeoutScriptCode_size s hw
  have hlen : (bL s.timeoutScriptCode).length = 136 := by
    simpa [Bitcoin.Serialization.bL] using h
  simp [Bitcoin.SigHash.witnessScriptSizeOk, hlen]

/-! ### 3.3 The exact target for the synthesized scriptCode -/

theorem HtlcSpend.successPreimage_eq_bip143MsgL (s : HtlcSpend) (ht : UInt32) :
    bL (s.successPreimage ht).preimageBytes =
      Bitcoin.SigHash.bip143MsgL s.successWire.toTx 0 (bL s.successScriptCode) ht
        (s.amountSat.toNat : Int) :=
  htlcBip143Preimage_eq_bip143MsgL s.successWire s.successScriptCode ht s.amountSat

theorem HtlcSpend.timeoutPreimage_eq_bip143MsgL (s : HtlcSpend) (ht : UInt32) :
    bL (s.timeoutPreimage ht).preimageBytes =
      Bitcoin.SigHash.bip143MsgL s.timeoutWire.toTx 0 (bL s.timeoutScriptCode) ht
        (s.amountSat.toNat : Int) :=
  htlcBip143Preimage_eq_bip143MsgL s.timeoutWire s.timeoutScriptCode ht s.amountSat

theorem HtlcSpend.successPreimage_digest_eq_sighashWitnessV0 (s : HtlcSpend)
    (ht : UInt32) :
    LnLean.Bitcoin.Sighash.digest (s.successPreimage ht).toPreimage =
      Bitcoin.SigHash.signatureHashBip143Impl s.successWire.toTx 0
        (bL s.successScriptCode) ht (s.amountSat.toNat : Int) :=
  htlcBip143Preimage_digest_eq_sighashWitnessV0 s.successWire s.successScriptCode ht
    s.amountSat

theorem HtlcSpend.timeoutPreimage_digest_eq_sighashWitnessV0 (s : HtlcSpend)
    (ht : UInt32) :
    LnLean.Bitcoin.Sighash.digest (s.timeoutPreimage ht).toPreimage =
      Bitcoin.SigHash.signatureHashBip143Impl s.timeoutWire.toTx 0
        (bL s.timeoutScriptCode) ht (s.amountSat.toNat : Int) :=
  htlcBip143Preimage_digest_eq_sighashWitnessV0 s.timeoutWire s.timeoutScriptCode ht
    s.amountSat

/-- The general size formula for an arbitrary HTLC wire. -/
theorem htlcBip143Preimage_size (h : HtlcWire) (scriptCode : ByteArray)
    (ht : UInt32) (amountSat : UInt64) (htx : h.commitmentTxid.size = 32) :
    (htlcBip143Preimage h scriptCode ht amountSat).preimageBytes.size =
      156 + compactSizeWidth scriptCode.size + scriptCode.size := by
  have hp : (htlcBip143Preimage h scriptCode ht amountSat).hashPrevouts.size = 32 := by
    simp [htlcBip143Preimage, Bip143Preimage.ofTx]
    exact hashPrevoutsOf_size h.toTx ht
  have hq : (htlcBip143Preimage h scriptCode ht amountSat).hashSequence.size = 32 := by
    simp [htlcBip143Preimage, Bip143Preimage.ofTx]
    exact hashSequenceOf_size h.toTx ht
  have ho : (htlcBip143Preimage h scriptCode ht amountSat).outpointTxid.size = 32 := by
    simp [htlcBip143Preimage, Bip143Preimage.ofTx, HtlcWire.toTx, htx]
  have hh : (htlcBip143Preimage h scriptCode ht amountSat).hashOutputs.size = 32 := by
    simp [htlcBip143Preimage, Bip143Preimage.ofTx]
    exact hashOutputsOf_size h.toTx 0 ht
  exact Bip143Preimage.preimageBytes_size _ hp hq ho hh

/-- Exact preimage byte length for the HTLC-success wire (the 143-byte received
script is below `0xfd`, so its CompactSize prefix is one byte). -/
theorem HtlcSpend.successPreimage_size (s : HtlcSpend) (hw : s.WellFormed)
    (ht : UInt32) :
    (s.successPreimage ht).preimageBytes.size = 300 := by
  have htx := hw.1
  have h := htlcBip143Preimage_size s.successWire s.successScriptCode ht s.amountSat
    (by simpa [HtlcSpend.successWire] using htx)
  change (htlcBip143Preimage s.successWire s.successScriptCode ht s.amountSat).preimageBytes.size = 300
  rw [h, HtlcSpend.successScriptCode_size s hw]
  decide

/-- Exact preimage byte length for the HTLC-timeout wire (the 136-byte offered
script is below `0xfd`, so its CompactSize prefix is one byte). -/
theorem HtlcSpend.timeoutPreimage_size (s : HtlcSpend) (hw : s.WellFormed)
    (ht : UInt32) :
    (s.timeoutPreimage ht).preimageBytes.size = 293 := by
  have htx := hw.1
  have h := htlcBip143Preimage_size s.timeoutWire s.timeoutScriptCode ht s.amountSat
    (by simpa [HtlcSpend.timeoutWire, HtlcSpend.successWire] using htx)
  change (htlcBip143Preimage s.timeoutWire s.timeoutScriptCode ht s.amountSat).preimageBytes.size = 293
  rw [h, HtlcSpend.timeoutScriptCode_size s hw]
  decide

/-! ### 3.4 The second-stage output is a P2WSH over the second-stage witness script -/

/-- If the second-stage output's program is `SHA256(scriptCode)`, its
`scriptPubKey` is the 34-byte BIP 141 P2WSH form.  The hash image itself is an
explicit `PrimitiveModel`/`sha256` hypothesis: no hash is recomputed here. -/
theorem HtlcSpend.successOutput_is_p2wsh (s : HtlcSpend)
    (M : LnLean.Crypto.PrimitiveModel)
    (hout : s.outputScriptPubKey =
      (p2wsh (M.sha256 s.successScriptCode)).bytes) :
    s.outputScriptPubKey.size = 34 := by
  rw [hout]
  exact p2wsh_size _ (M.sha256_size _)

/-- The same for the HTLC-timeout output. -/
theorem HtlcSpend.timeoutOutput_is_p2wsh (s : HtlcSpend)
    (M : LnLean.Crypto.PrimitiveModel)
    (hout : s.outputScriptPubKey =
      (p2wsh (M.sha256 s.timeoutScriptCode)).bytes) :
    s.outputScriptPubKey.size = 34 := by
  rw [hout]
  exact p2wsh_size _ (M.sha256_size _)

/-! ## 4. `htlcBranchScript` is not a faithful BOLT 3 HTLC script -/

/-- The Seam stub starts `OP_IF OP_HASH160`. -/
theorem htlcBranchScript_take2 (ph : PaymentHash) (cltv : Height) (pk : PubKey) :
    (bL (htlcBranchScript ph cltv pk).bytes).take 2 = [OP_IF, OP_HASH160] := by
  unfold htlcBranchScript pushData
  simp only [bL_append, bL_push, bL_empty, List.nil_append, List.cons_append,
    List.take_succ_cons, List.take_zero]

/-- The BOLT 3 offered-HTLC witness script starts `OP_DUP OP_HASH160`. -/
theorem offeredHtlcWitnessScript_take2 (revocationKeyHash160 paymentHash160 : ByteArray)
    (remoteHtlcKey localHtlcKey : PubKey) :
    (bL (offeredHtlcWitnessScript revocationKeyHash160 paymentHash160
        remoteHtlcKey localHtlcKey).bytes).take 2 = [OP_DUP, OP_HASH160] := by
  unfold offeredHtlcWitnessScript
  simp only [bL_append, bL_push, bL_empty, List.nil_append, List.cons_append,
    List.take_succ_cons, List.take_zero]

/-- The BOLT 3 received-HTLC witness script starts `OP_DUP OP_HASH160`. -/
theorem receivedHtlcWitnessScript_take2 (revocationKeyHash160 paymentHash160 : ByteArray)
    (remoteHtlcKey localHtlcKey : PubKey) (cltvExpiry : Height) :
    (bL (receivedHtlcWitnessScript revocationKeyHash160 paymentHash160
        remoteHtlcKey localHtlcKey cltvExpiry).bytes).take 2 =
      [OP_DUP, OP_HASH160] := by
  unfold receivedHtlcWitnessScript
  simp only [bL_append, bL_push, bL_empty, List.nil_append, List.cons_append,
    List.take_succ_cons, List.take_zero]

/-- The BOLT 3 second-stage output witness script (`to_local` shape) starts
`OP_IF <33-byte push>`. -/
theorem toLocalScriptFull_take2 (revocationKey delayedPaymentKey : PubKey)
    (toSelfDelay : Blocks) (hr : revocationKey.bytes.size = 33) :
    (bL (toLocalScriptFull revocationKey delayedPaymentKey toSelfDelay).bytes).take
        2 = [OP_IF, 0x21] := by
  unfold toLocalScriptFull pushData
  rw [hr]
  simp only [bL_append, bL_push, bL_empty, List.nil_append, List.cons_append,
    List.take_succ_cons, List.take_zero]
  decide

/-- **Negative 1.**  The Seam stub is not the offered-HTLC witness script, so it
cannot be the HTLC-timeout `scriptCode`. -/
theorem htlcBranchScript_ne_offeredHtlcWitnessScript (ph : PaymentHash)
    (cltv : Height) (pk : PubKey) (revocationKeyHash160 paymentHash160 : ByteArray)
    (remoteHtlcKey localHtlcKey : PubKey) :
    (htlcBranchScript ph cltv pk).bytes ≠
      (offeredHtlcWitnessScript revocationKeyHash160 paymentHash160
        remoteHtlcKey localHtlcKey).bytes := by
  intro heq
  have h2 := congrArg (fun b : ByteArray => (bL b).take 2) heq
  rw [htlcBranchScript_take2, offeredHtlcWitnessScript_take2] at h2
  exact absurd h2 (by decide)

/-- **Negative 2.**  The Seam stub is not the received-HTLC witness script, so
it cannot be the HTLC-success `scriptCode`. -/
theorem htlcBranchScript_ne_receivedHtlcWitnessScript (ph : PaymentHash)
    (cltv : Height) (pk : PubKey) (revocationKeyHash160 paymentHash160 : ByteArray)
    (remoteHtlcKey localHtlcKey : PubKey) (cltvExpiry : Height) :
    (htlcBranchScript ph cltv pk).bytes ≠
      (receivedHtlcWitnessScript revocationKeyHash160 paymentHash160
        remoteHtlcKey localHtlcKey cltvExpiry).bytes := by
  intro heq
  have h2 := congrArg (fun b : ByteArray => (bL b).take 2) heq
  rw [htlcBranchScript_take2, receivedHtlcWitnessScript_take2] at h2
  exact absurd h2 (by decide)

/-- **Negative 3.**  The Seam stub is not the BOLT 3 second-stage output witness
script either (`OP_IF <revocationpubkey>`), so it is not an output script for
the HTLC-timeout/HTLC-success transaction. -/
theorem htlcBranchScript_ne_toLocalScriptFull (ph : PaymentHash) (cltv : Height)
    (pk revocationKey delayedPaymentKey : PubKey) (toSelfDelay : Blocks)
    (hr : revocationKey.bytes.size = 33) :
    (htlcBranchScript ph cltv pk).bytes ≠
      (toLocalScriptFull revocationKey delayedPaymentKey toSelfDelay).bytes := by
  intro heq
  have h2 := congrArg (fun b : ByteArray => (bL b).take 2) heq
  rw [htlcBranchScript_take2, toLocalScriptFull_take2 revocationKey delayedPaymentKey
    toSelfDelay hr] at h2
  exact absurd h2 (by decide)

/-- **Negative 4.**  The stub's CLTV push is `pushData #[cltv.toUInt8]`, which
collapses `cltv = 0` and `cltv = 256` (and every pair congruent modulo 256) to
the same script.  It therefore cannot encode BOLT 3's `CScriptNum` CLTV value. -/
theorem htlcBranchScript_cltv_not_injective (ph : PaymentHash) (pk : PubKey) :
    htlcBranchScript ph 0 pk = htlcBranchScript ph 256 pk := by
  simp [htlcBranchScript]

/-! ## 5. A ready-to-use HTLC-success / HTLC-timeout vector -/

/-- 20-byte hash image. -/
def hash20 (b : UInt8) : ByteArray := byteList (List.replicate 20 b)

def vectorHtlcCommitmentTxid : ByteArray :=
  byteList ([0x01] ++ List.replicate 30 0x00 ++ [0x02])

def vectorRevocationHash160 : ByteArray := hash20 0x55

def vectorPaymentHash160 : ByteArray := hash20 0x66

def vectorRemoteHtlcKey : PubKey :=
  ⟨byteList ([0x02] ++ List.replicate 32 0x77)⟩

def vectorLocalHtlcKey : PubKey :=
  ⟨byteList ([0x03] ++ List.replicate 32 0x88)⟩

def vectorHtlcSpend : HtlcSpend :=
  { commitmentTxid := vectorHtlcCommitmentTxid
    commitmentOutputIndex := 1
    anchorOutputs := true
    revocationKeyHash160 := vectorRevocationHash160
    paymentHash160 := vectorPaymentHash160
    remoteHtlcKey := vectorRemoteHtlcKey
    localHtlcKey := vectorLocalHtlcKey
    cltvExpiry := 500000
    amountSat := 7000
    secondStageFeeSat := 3515
    outputScriptPubKey := byteList [0x00, 0x20] ++ hash32 0x99 }

theorem vectorHtlcSpend_wellFormed : vectorHtlcSpend.WellFormed := by
  unfold HtlcSpend.WellFormed
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem vectorHtlcSpend_successScriptCode_size :
    vectorHtlcSpend.successScriptCode.size = 143 :=
  HtlcSpend.successScriptCode_size _ vectorHtlcSpend_wellFormed

theorem vectorHtlcSpend_timeoutScriptCode_size :
    vectorHtlcSpend.timeoutScriptCode.size = 136 :=
  HtlcSpend.timeoutScriptCode_size _ vectorHtlcSpend_wellFormed

theorem vectorHtlcSpend_successPreimage_size :
    (vectorHtlcSpend.successPreimage 0x82).preimageBytes.size = 300 :=
  HtlcSpend.successPreimage_size _ vectorHtlcSpend_wellFormed 0x82

theorem vectorHtlcSpend_timeoutPreimage_size :
    (vectorHtlcSpend.timeoutPreimage 0x82).preimageBytes.size = 293 :=
  HtlcSpend.timeoutPreimage_size _ vectorHtlcSpend_wellFormed 0x82

/-! `SIGHASH_NONE|ANYONECANPAY` (`0x82`) makes all three sub-hashes the BIP 143
zero vector, so the kernel `decide` checks byte order and field boundaries
without evaluating SHA-256 (the same device as the wave-7 commitment vector). -/

theorem vectorHtlcSpend_success_bytes_layout :
    ((bL (vectorHtlcSpend.successPreimage 0x82).preimageBytes).take 4 =
        [0x02, 0x00, 0x00, 0x00]) ∧
    ((bL (vectorHtlcSpend.successPreimage 0x82).preimageBytes).drop 68).take 32 =
        bL vectorHtlcCommitmentTxid ∧
    ((bL (vectorHtlcSpend.successPreimage 0x82).preimageBytes).drop 100).take 4 =
        [0x01, 0x00, 0x00, 0x00] ∧
    ((bL (vectorHtlcSpend.successPreimage 0x82).preimageBytes).drop 104).take 1 =
        [0x8f] ∧
    ((bL (vectorHtlcSpend.successPreimage 0x82).preimageBytes).drop 248).take 8 =
        [0x58, 0x1b, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] ∧
    ((bL (vectorHtlcSpend.successPreimage 0x82).preimageBytes).drop 256).take 4 =
        [0x01, 0x00, 0x00, 0x00] ∧
    ((bL (vectorHtlcSpend.successPreimage 0x82).preimageBytes).drop 292).take 4 =
        [0x00, 0x00, 0x00, 0x00] ∧
    ((bL (vectorHtlcSpend.successPreimage 0x82).preimageBytes).drop 296).take 4 =
        [0x82, 0x00, 0x00, 0x00] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem vectorHtlcSpend_timeout_bytes_layout :
    ((bL (vectorHtlcSpend.timeoutPreimage 0x82).preimageBytes).take 4 =
        [0x02, 0x00, 0x00, 0x00]) ∧
    ((bL (vectorHtlcSpend.timeoutPreimage 0x82).preimageBytes).drop 68).take 32 =
        bL vectorHtlcCommitmentTxid ∧
    ((bL (vectorHtlcSpend.timeoutPreimage 0x82).preimageBytes).drop 100).take 4 =
        [0x01, 0x00, 0x00, 0x00] ∧
    ((bL (vectorHtlcSpend.timeoutPreimage 0x82).preimageBytes).drop 104).take 1 =
        [0x88] ∧
    ((bL (vectorHtlcSpend.timeoutPreimage 0x82).preimageBytes).drop 241).take 8 =
        [0x58, 0x1b, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] ∧
    ((bL (vectorHtlcSpend.timeoutPreimage 0x82).preimageBytes).drop 249).take 4 =
        [0x01, 0x00, 0x00, 0x00] ∧
    ((bL (vectorHtlcSpend.timeoutPreimage 0x82).preimageBytes).drop 285).take 4 =
        [0x20, 0xa1, 0x07, 0x00] ∧
    ((bL (vectorHtlcSpend.timeoutPreimage 0x82).preimageBytes).drop 289).take 4 =
        [0x82, 0x00, 0x00, 0x00] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- The success vector's `scriptCode` slice is exactly the synthesized 143-byte
received-HTLC witness script (including its `OP_DUP OP_HASH160` prefix). -/
theorem vectorHtlcSpend_successScriptCode_slice :
    ((bL (vectorHtlcSpend.successPreimage 0x82).preimageBytes).drop 105).take
        143 = bL vectorHtlcSpend.successScriptCode := by
  decide

/-- The timeout vector's `scriptCode` slice is exactly the synthesized 136-byte
offered-HTLC witness script. -/
theorem vectorHtlcSpend_timeoutScriptCode_slice :
    ((bL (vectorHtlcSpend.timeoutPreimage 0x82).preimageBytes).drop 105).take
        136 = bL vectorHtlcSpend.timeoutScriptCode := by
  decide

/-- The vendor encoder produces the same scriptCode slice for the success
vector. -/
theorem vectorHtlcSpend_success_vendor_scriptCode_slice :
    ((Bitcoin.SigHash.bip143MsgL vectorHtlcSpend.successWire.toTx 0
        (bL vectorHtlcSpend.successScriptCode) 0x82
        (vectorHtlcSpend.amountSat.toNat : Int)).drop 105).take 143 =
      bL vectorHtlcSpend.successScriptCode := by
  rw [← HtlcSpend.successPreimage_eq_bip143MsgL]
  exact vectorHtlcSpend_successScriptCode_slice

/-- The vendor encoder produces the same scriptCode slice for the timeout
vector. -/
theorem vectorHtlcSpend_timeout_vendor_scriptCode_slice :
    ((Bitcoin.SigHash.bip143MsgL vectorHtlcSpend.timeoutWire.toTx 0
        (bL vectorHtlcSpend.timeoutScriptCode) 0x82
        (vectorHtlcSpend.amountSat.toNat : Int)).drop 105).take 136 =
      bL vectorHtlcSpend.timeoutScriptCode := by
  rw [← HtlcSpend.timeoutPreimage_eq_bip143MsgL]
  exact vectorHtlcSpend_timeoutScriptCode_slice

/-- The display-order conversion on the vector is a genuine reversal: the
commitment txid is not palindromic. -/
theorem vectorHtlcSpend_commitmentTxid_not_palindromic :
    displayTxid vectorHtlcCommitmentTxid ≠ vectorHtlcCommitmentTxid := by
  decide

/-- The preimage's outpoint field is the internal order, while the display form
is the reversed vector. -/
theorem vectorHtlcSpend_outpoint_display :
    ((bL (vectorHtlcSpend.successPreimage 0x82).preimageBytes).drop 68).take 32 =
        (bL (displayTxid vectorHtlcCommitmentTxid)).reverse ∧
      ((bL (vectorHtlcSpend.successPreimage 0x82).preimageBytes).drop 68).take 32 =
        bL vectorHtlcCommitmentTxid := by
  refine ⟨?_, ?_⟩ <;> decide

/-! ## 6. Summary -/

/-- Bundled summary of the target: field agreement, vendor byte equality, the
`toPreimage` bridge, and the synthesized scriptCode sizes.  This theorem has no
hypotheses beyond well-formedness of the script inputs. -/
theorem htlc_preimage_target_summary (s : HtlcSpend) (hw : s.WellFormed)
    (ht : UInt32) :
    (bL (s.successPreimage ht).preimageBytes =
        Bitcoin.SigHash.bip143MsgL s.successWire.toTx 0
          (bL s.successScriptCode) ht (s.amountSat.toNat : Int) ∧
      bL (s.timeoutPreimage ht).preimageBytes =
        Bitcoin.SigHash.bip143MsgL s.timeoutWire.toTx 0
          (bL s.timeoutScriptCode) ht (s.amountSat.toNat : Int) ∧
      (s.successPreimage ht).toPreimage =
        LnLean.Bitcoin.Sighash.ofTx s.successWire.toTx 0 s.successScriptCode ht
          (s.amountSat.toNat : Int) ∧
      s.successScriptCode.size = 143 ∧
      s.timeoutScriptCode.size = 136 ∧
      s.successWire.locktime = 0 ∧
      s.timeoutWire.locktime = s.cltvExpiry) :=
  ⟨HtlcSpend.successPreimage_eq_bip143MsgL s ht,
    HtlcSpend.timeoutPreimage_eq_bip143MsgL s ht,
    htlcBip143Preimage_toPreimage s.successWire s.successScriptCode ht s.amountSat,
    HtlcSpend.successScriptCode_size s hw,
    HtlcSpend.timeoutScriptCode_size s hw,
    rfl, rfl⟩

end LnLean.Proofs.Channel.HtlcPreimageTargets
