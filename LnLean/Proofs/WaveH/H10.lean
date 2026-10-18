/-
# H10 — Display-order txid conversion for the BIP 143 funding outpoint
(PR-05, PR-02)

**Catalog issues.**

* `PR-05` (P1): the BIP 143 preimage byte-equality work fixed the outpoint
  txid as the "consensus-internal" 32 bytes and explicitly refused to reverse
  it, but the model had no definition of the *display-order* txid and no
  theorem connecting the two orders.  This made the byte-order convention an
  unstated assumption at the funding/channel-id boundary.
* `PR-02` (P1): the wire record must carry enough data for a wire-only
  sighash construction.  The funding outpoint is one of those wire fields, so
  the byte-order convention is part of the wire semantics, not presentation
  sugar.

## Result of this module

1. `reverseBytes` reverses the bytes of a `ByteArray`.  It is proved to
   preserve size, to be an involution (`reverseBytes_reverseBytes`), to be
   injective, and to commute with the proof-facing list view `bL`
   (`bL (reverseBytes b) = (bL b).reverse`).
2. The exact domain is stated as the subtype `TxidBytes = { b // b.size = 32 }`.
   `displayToInternal` and `internalToDisplay` are mutually inverse maps on
   this subtype; `displayToInternal` is a bijection and every internal txid
   has a unique display form.  The reversal is total on all `ByteArray`s but
   is only *interpreted* as a txid conversion on the 32-byte subtype.
3. `displayOutpointTxid p := reverseBytes p.outpointTxid`, and
   the preimage's outpoint hash is proved equal to the reversed display form
   (`Bip143Preimage.toPreimage_outpoint_hash_eq_reverse_display`).
4. For every `CommitmentWire` and every display-order byte string `d`, the
   internal txid used by `commitmentBip143Preimage` is exactly
   `reverseBytes d` if and only if the wire's `fundingTxid` is `reverseBytes d`
   (`commitmentBip143Preimage_outpointTxid_eq_reverse_display_iff`).  The
   display form computed back from the preimage equals the wire's display
   form (`commitmentBip143Preimage_displayOutpointTxid_eq`).
5. The same bridge for `HtlcWire` at the fixed input index `0`
   (`HtlcWire.preimage_outpointTxid_eq_reverse_display`), since
   `HtlcWire.toTx` has exactly one input.
6. A concrete 32-byte vector taken from BOLT 3 Appendix A/C: the funding
   transaction's *display* txid `8984484a580b825b9972d7adb15050b3ab624ccd731946b3eeddb92f4e7ef6be`
   and its *internal* form `bef67e4e2fb9ddeeb3461973cd4c62abb35050b1add772995b820b584a488489`.
   The latter is exactly the `txin[0]` outpoint bytes of the BOLT 3 Appendix C
   commitment transaction.  `decide` proves the two vectors are reverses, both
   are 32 bytes, and they are not equal.  The commitment-wire preimage built
   from the internal vector is then proved to carry `reverseBytes` of the
   display vector, and *not* the display vector itself.

## Scope

* The reversal is a byte permutation, not a hash.  This module does **not**
  recompute `SHA256d(funding tx)` in Lean: the concrete vector is the
  published BOLT 3 test-vector pair, and only the byte-order relation between
  its two forms is mechanized.  No collision-resistance or txid-uniqueness
  assumption is used.
* The model convention is fixed by BIP 143 and BOLT 3: the wire
  `fundingTxid`, `CommitmentWire.fundingTxid`, `HtlcWire.commitmentTxid`, and
  `Bip143Preimage.outpointTxid` are the raw 32 bytes in **internal** order;
  the display form is their reversal.  The theorems quantify over an
  arbitrary `display : ByteArray`, so they do not bake in any particular
  external hex encoding (checksum, grouping, or prefix).
* This module is additive and does not edit `SighashTargets`; see the report
  for the exact shared-file integration patch (`reverseBytes` and the
  `TxidBytes` bijection are candidates for `LnLean/Bitcoin/Sighash.lean` or
  `LnLean/Basic/Core.lean`).

## Anchors

* BOLT 3 Appendix A: funding transaction and its displayed `txid`
  (`refs/bolts/03-transactions.md:1230-1262`); the funding transaction's
  single input stores the internal order of the spent outpoint.
* BOLT 3 Appendix C: `output commit_tx` starts with
  `txin[0]` outpoint `bef67e4e...8489`, the internal form of the Appendix A
  funding txid (`refs/bolts/03-transactions.md:1355-1365`).
* BIP 143 §3–6: the sighash preimage's outpoint is the raw 32-byte txid
  followed by the 4-byte little-endian index.
* Model: `LnLean/Proofs/Channel/SighashTargets.lean` (`Bip143Preimage`,
  `Bip143Preimage.ofTx`, `CommitmentWire`, `HtlcWire`,
  `commitmentBip143Preimage_wire_fields`), `LnLean/Bitcoin/Sighash.lean`
  (`Preimage.outpoint`, `serOutpoint`).
-/

import LnLean.Proofs.Channel.SighashTargets

namespace LnLean.Proofs.WaveH.H10

set_option autoImplicit false
set_option maxRecDepth 10000

open Bitcoin.Data
open Bitcoin.Serialization
open LnLean.Proofs.Channel.SighashTargets

/-! ## 1. Byte reversal -/

/-- Reverse the byte order of a `ByteArray`.  This is the raw byte
permutation behind Bitcoin's display-order txid convention: the internal
(consensus/wire) form is reversed to obtain the form shown by explorers. -/
def reverseBytes (b : ByteArray) : ByteArray :=
  ⟨b.data.reverse⟩

/-- Reversal preserves the number of bytes. -/
@[simp] theorem reverseBytes_size (b : ByteArray) :
    (reverseBytes b).size = b.size := by
  rcases b with ⟨data⟩
  exact Array.size_reverse (xs := data)

/-- Reversal commutes with the proof-facing list view: the list of the
reversed bytes is the reverse of the original list. -/
theorem bL_reverseBytes (b : ByteArray) :
    bL (reverseBytes b) = (bL b).reverse := by
  simp [reverseBytes, Bitcoin.Serialization.bL]

/-- Reversal is an involution: reversing twice returns the original bytes.
This is the theorem that makes the display/internal conversion invertible. -/
theorem reverseBytes_involutive (b : ByteArray) :
    reverseBytes (reverseBytes b) = b := by
  apply bL_inj
  rw [bL_reverseBytes, bL_reverseBytes]
  simp

/-- Reversal is injective (equivalently, a bijection on every fixed length). -/
theorem reverseBytes_injective : Function.Injective reverseBytes := by
  intro a b h
  have h' := congrArg reverseBytes h
  simpa [reverseBytes_involutive] using h'

/-- The list-level form of the conversion, useful for concrete vectors. -/
theorem reverseBytes_bytesOfList (l : List UInt8) :
    reverseBytes (bytesOfList l) = bytesOfList l.reverse := by
  apply bL_inj
  rw [bL_reverseBytes]
  simp [bytesOfList, bL]

/-! ## 2. The exact domain: 32-byte txids

The `reverseBytes` function is total, but a Bitcoin txid is exactly 32 bytes.
The subtype below is the precise domain on which the display/internal
conversion is claimed to be a bijection. -/

/-- The txid domain: exactly 32 bytes. -/
def IsTxidBytes (b : ByteArray) : Prop :=
  b.size = 32

/-- Reversal preserves the txid domain and reflects membership in it. -/
theorem reverseBytes_isTxidBytes_iff (b : ByteArray) :
    IsTxidBytes (reverseBytes b) ↔ IsTxidBytes b := by
  simp [IsTxidBytes, reverseBytes_size]

/-- Forward preservation of the txid domain. -/
theorem reverseBytes_isTxidBytes {b : ByteArray} (h : IsTxidBytes b) :
    IsTxidBytes (reverseBytes b) :=
  (reverseBytes_isTxidBytes_iff b).2 h

/-- The 32-byte txid subtype.  This is the exact domain of the conversion. -/
abbrev TxidBytes : Type :=
  { b : ByteArray // IsTxidBytes b }

namespace TxidBytes

/-- Display order to internal order: reverse the bytes. -/
def displayToInternal (d : TxidBytes) : TxidBytes :=
  ⟨reverseBytes d.1, reverseBytes_isTxidBytes d.2⟩

/-- Internal order to display order: reverse the bytes. -/
def internalToDisplay (i : TxidBytes) : TxidBytes :=
  ⟨reverseBytes i.1, reverseBytes_isTxidBytes i.2⟩

/-- Converting display → internal → display is the identity. -/
@[simp] theorem internalToDisplay_displayToInternal (d : TxidBytes) :
    internalToDisplay (displayToInternal d) = d := by
  apply Subtype.ext
  exact reverseBytes_involutive d.1

/-- Converting internal → display → internal is the identity. -/
@[simp] theorem displayToInternal_internalToDisplay (i : TxidBytes) :
    displayToInternal (internalToDisplay i) = i := by
  apply Subtype.ext
  exact reverseBytes_involutive i.1

/-- The display → internal map is injective. -/
theorem displayToInternal_injective :
    Function.Injective displayToInternal := by
  intro a b h
  have h' := congrArg internalToDisplay h
  simpa using h'

/-- The display → internal map is surjective: every internal txid has a
display preimage (namely its own reversal). -/
theorem displayToInternal_surjective :
    Function.Surjective displayToInternal := by
  intro i
  exact ⟨internalToDisplay i, displayToInternal_internalToDisplay i⟩

/-- **Bijection on the exact 32-byte domain** (injectivity and surjectivity,
stated separately because core Lean has no `Function.Bijective`). -/
theorem displayToInternal_bijective :
    Function.Injective displayToInternal ∧
      Function.Surjective displayToInternal :=
  ⟨displayToInternal_injective, displayToInternal_surjective⟩

/-- Every internal txid has a **unique** display form. -/
theorem exists_display_of_internal (i : TxidBytes) :
    ∃ d : TxidBytes, displayToInternal d = i ∧
      ∀ d' : TxidBytes, displayToInternal d' = i → d' = d := by
  refine ⟨internalToDisplay i, displayToInternal_internalToDisplay i, ?_⟩
  intro d hd
  have h' := congrArg internalToDisplay hd
  simpa using h'

end TxidBytes

/-- The same domain fact at the `ByteArray` level: reversal maps 32-byte
arrays to 32-byte arrays, is injective there, and is onto there. -/
theorem reverseBytes_maps_txidBytes :
    (∀ b : ByteArray, IsTxidBytes b → IsTxidBytes (reverseBytes b)) ∧
    (∀ a : ByteArray, IsTxidBytes a → ∀ b : ByteArray, IsTxidBytes b →
      reverseBytes a = reverseBytes b → a = b) ∧
    (∀ b : ByteArray, IsTxidBytes b →
      ∃ a : ByteArray, IsTxidBytes a ∧ reverseBytes a = b) := by
  refine ⟨?_, ?_, ?_⟩
  · intro b hb
    exact reverseBytes_isTxidBytes hb
  · intro a _ b _ h
    exact reverseBytes_injective h
  · intro b hb
    exact ⟨reverseBytes b, reverseBytes_isTxidBytes hb, reverseBytes_involutive b⟩

/-! ## 3. The BIP 143 preimage carries the internal order

`Bip143Preimage.outpointTxid` is inserted verbatim into the preimage; the
display form is its reversal.  The bridge is stated both on the record and on
the transaction-derived constructor `Bip143Preimage.ofTx`. -/

/-- The display-order form of a preimage's outpoint txid. -/
def displayOutpointTxid (p : Bip143Preimage) : ByteArray :=
  reverseBytes p.outpointTxid

/-- Definitional unfolding of `displayOutpointTxid`. -/
theorem displayOutpointTxid_eq (p : Bip143Preimage) :
    displayOutpointTxid p = reverseBytes p.outpointTxid := rfl

/-- The internal outpoint txid is the reversal of the display form.  This is
the direction used by the BIP 143 encoder: it inserts `outpointTxid` verbatim. -/
theorem outpointTxid_eq_reverse_displayOutpointTxid (p : Bip143Preimage) :
    p.outpointTxid = reverseBytes (displayOutpointTxid p) := by
  simp [displayOutpointTxid, reverseBytes_involutive]

/-- The bridged sighash-model preimage keeps the same internal outpoint hash. -/
theorem toPreimage_outpoint_hash (p : Bip143Preimage) :
    p.toPreimage.outpoint.hash = p.outpointTxid := rfl

/-- The outpoint hash of the bridged sighash-model preimage is the reverse of
the display form. -/
theorem toPreimage_outpoint_hash_eq_reverse_display (p : Bip143Preimage) :
    p.toPreimage.outpoint.hash = reverseBytes (displayOutpointTxid p) := by
  rw [toPreimage_outpoint_hash, outpointTxid_eq_reverse_displayOutpointTxid]

/-- For a transaction-derived preimage, the outpoint txid is the input's raw
prevout hash, which is `reverseBytes display` exactly when the raw hash is. -/
theorem ofTx_outpointTxid_eq_reverse_display
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (scriptCode : ByteArray) (ht : UInt32)
    (amountSat : UInt64) (display : ByteArray)
    (h : (tx.vin.getD nIn LnLean.Bitcoin.Sighash.dummyTxIn).prevout.hash =
      reverseBytes display) :
    (Bip143Preimage.ofTx tx nIn scriptCode ht amountSat).outpointTxid =
      reverseBytes display := by
  simpa [Bip143Preimage.ofTx, List.getD] using h

/-- Iff form of `ofTx_outpointTxid_eq_reverse_display`: the preimage's
outpoint is the reversal of the display form iff the input's raw hash is. -/
theorem ofTx_outpointTxid_eq_reverse_display_iff
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (scriptCode : ByteArray) (ht : UInt32)
    (amountSat : UInt64) (display : ByteArray) :
    (Bip143Preimage.ofTx tx nIn scriptCode ht amountSat).outpointTxid =
        reverseBytes display ↔
      (tx.vin.getD nIn LnLean.Bitcoin.Sighash.dummyTxIn).prevout.hash =
        reverseBytes display := by
  simp [Bip143Preimage.ofTx]

/-! ## 4. Funding-wire instances -/

/-- The display-order form of the commitment wire's funding txid. -/
def fundingTxidDisplay (w : CommitmentWire) : ByteArray :=
  reverseBytes w.fundingTxid

/-- The wire `fundingTxid` is the internal order, i.e. the reversal of the
display form. -/
theorem fundingTxid_eq_reverse_fundingTxidDisplay (w : CommitmentWire) :
    w.fundingTxid = reverseBytes (fundingTxidDisplay w) := by
  simp [fundingTxidDisplay, reverseBytes_involutive]

/-- **The BIP 143 funding outpoint uses the internal order.**  For any display
byte string `d`, `commitmentBip143Preimage` carries it reversed iff the wire's
`fundingTxid` is that reversed value.  No well-formedness premise is needed:
the statement is a field projection plus the byte reversal. -/
theorem commitmentBip143Preimage_outpointTxid_eq_reverse_display_iff
    (w : CommitmentWire) (scriptCode : ByteArray) (ht : UInt32)
    (amountSat : UInt64) (display : ByteArray) :
    (commitmentBip143Preimage w scriptCode ht amountSat).outpointTxid =
        reverseBytes display ↔
      w.fundingTxid = reverseBytes display := by
  have hf := (commitmentBip143Preimage_wire_fields w scriptCode ht amountSat).2.1
  constructor
  · intro h
    exact hf.symm.trans h
  · intro h
    exact hf.trans h

/-- Forward direction of the iff, convenient for rewriting. -/
theorem commitmentBip143Preimage_outpointTxid_eq_reverse_display
    (w : CommitmentWire) (scriptCode : ByteArray) (ht : UInt32)
    (amountSat : UInt64) (display : ByteArray)
    (h : w.fundingTxid = reverseBytes display) :
    (commitmentBip143Preimage w scriptCode ht amountSat).outpointTxid =
      reverseBytes display :=
  (commitmentBip143Preimage_outpointTxid_eq_reverse_display_iff
    w scriptCode ht amountSat display).2 h

/-- If the display form is a 32-byte txid, the preimage's outpoint is also in
the exact txid domain. -/
theorem commitmentBip143Preimage_outpointTxid_isTxidBytes
    (w : CommitmentWire) (scriptCode : ByteArray) (ht : UInt32)
    (amountSat : UInt64) (display : ByteArray)
    (h : w.fundingTxid = reverseBytes display)
    (hsize : IsTxidBytes display) :
    IsTxidBytes
      (commitmentBip143Preimage w scriptCode ht amountSat).outpointTxid := by
  rw [commitmentBip143Preimage_outpointTxid_eq_reverse_display
    w scriptCode ht amountSat display h]
  exact reverseBytes_isTxidBytes hsize

/-- The preimage's outpoint is the reversal of the wire's display txid. -/
theorem commitmentBip143Preimage_outpointTxid_eq_reverse_fundingTxidDisplay
    (w : CommitmentWire) (scriptCode : ByteArray) (ht : UInt32)
    (amountSat : UInt64) :
    (commitmentBip143Preimage w scriptCode ht amountSat).outpointTxid =
      reverseBytes (fundingTxidDisplay w) := by
  rw [(commitmentBip143Preimage_wire_fields w scriptCode ht amountSat).2.1]
  exact fundingTxid_eq_reverse_fundingTxidDisplay w

/-- The display form computed back from the preimage equals the wire's display
form.  This is the inverse direction of the same bridge. -/
theorem commitmentBip143Preimage_displayOutpointTxid_eq
    (w : CommitmentWire) (scriptCode : ByteArray) (ht : UInt32)
    (amountSat : UInt64) :
    displayOutpointTxid (commitmentBip143Preimage w scriptCode ht amountSat) =
      fundingTxidDisplay w := by
  simp [displayOutpointTxid, fundingTxidDisplay,
    (commitmentBip143Preimage_wire_fields w scriptCode ht amountSat).2.1]

/-- The display-order form of the HTLC wire's commitment txid. -/
def commitmentTxidDisplay (h : HtlcWire) : ByteArray :=
  reverseBytes h.commitmentTxid

/-- The HTLC wire's `commitmentTxid` is the internal order. -/
theorem commitmentTxid_eq_reverse_commitmentTxidDisplay (h : HtlcWire) :
    h.commitmentTxid = reverseBytes (commitmentTxidDisplay h) := by
  simp [commitmentTxidDisplay, reverseBytes_involutive]

/-- **The HTLC-wire BIP 143 outpoint uses the internal order.**  `HtlcWire.toTx`
has exactly one input, so index `0` is the signing input.  For any display
byte string `d`, the preimage of the HTLC transaction carries `reverseBytes d`
iff the wire's `commitmentTxid` is `reverseBytes d`. -/
theorem htlcWirePreimage_outpointTxid_eq_reverse_display_iff
    (h : HtlcWire) (scriptCode : ByteArray) (ht : UInt32)
    (amountSat : UInt64) (display : ByteArray) :
    (Bip143Preimage.ofTx h.toTx 0 scriptCode ht amountSat).outpointTxid =
        reverseBytes display ↔
      h.commitmentTxid = reverseBytes display := by
  simp [Bip143Preimage.ofTx, HtlcWire.toTx]

/-- Forward direction of the HTLC-wire iff. -/
theorem htlcWirePreimage_outpointTxid_eq_reverse_display
    (h : HtlcWire) (scriptCode : ByteArray) (ht : UInt32)
    (amountSat : UInt64) (display : ByteArray)
    (hd : h.commitmentTxid = reverseBytes display) :
    (Bip143Preimage.ofTx h.toTx 0 scriptCode ht amountSat).outpointTxid =
      reverseBytes display :=
  (htlcWirePreimage_outpointTxid_eq_reverse_display_iff
    h scriptCode ht amountSat display).2 hd

/-- If the display form is a 32-byte txid, the HTLC preimage's outpoint is
also in the exact txid domain. -/
theorem htlcWirePreimage_outpointTxid_isTxidBytes
    (h : HtlcWire) (scriptCode : ByteArray) (ht : UInt32)
    (amountSat : UInt64) (display : ByteArray)
    (hd : h.commitmentTxid = reverseBytes display)
    (hsize : IsTxidBytes display) :
    IsTxidBytes
      (Bip143Preimage.ofTx h.toTx 0 scriptCode ht amountSat).outpointTxid := by
  rw [htlcWirePreimage_outpointTxid_eq_reverse_display
    h scriptCode ht amountSat display hd]
  exact reverseBytes_isTxidBytes hsize

/-- The HTLC preimage's outpoint is the reversal of the wire's display txid. -/
theorem htlcWirePreimage_outpointTxid_eq_reverse_commitmentTxidDisplay
    (h : HtlcWire) (scriptCode : ByteArray) (ht : UInt32)
    (amountSat : UInt64) :
    (Bip143Preimage.ofTx h.toTx 0 scriptCode ht amountSat).outpointTxid =
      reverseBytes (commitmentTxidDisplay h) :=
  htlcWirePreimage_outpointTxid_eq_reverse_display h scriptCode ht amountSat
    (commitmentTxidDisplay h) (commitmentTxid_eq_reverse_commitmentTxidDisplay h)

/-! ## 5. Concrete 32-byte BOLT 3 vector

BOLT 3 Appendix A publishes the funding transaction's txid in display order.
Appendix C's commitment transaction then spends it with the raw bytes in
internal order.  Both 32-byte lists are reproduced verbatim below. -/

/-- The BOLT 3 Appendix A funding txid in **display** order:
`8984484a580b825b9972d7adb15050b3ab624ccd731946b3eeddb92f4e7ef6be`. -/
def bolt3FundingTxidDisplay : ByteArray :=
  byteList [0x89, 0x84, 0x48, 0x4a, 0x58, 0x0b, 0x82, 0x5b,
            0x99, 0x72, 0xd7, 0xad, 0xb1, 0x50, 0x50, 0xb3,
            0xab, 0x62, 0x4c, 0xcd, 0x73, 0x19, 0x46, 0xb3,
            0xee, 0xdd, 0xb9, 0x2f, 0x4e, 0x7e, 0xf6, 0xbe]

/-- The same funding txid in **internal** order, i.e. the bytes that appear in
`txin[0]` of the BOLT 3 Appendix C commitment transaction. -/
def bolt3FundingTxidInternal : ByteArray :=
  byteList [0xbe, 0xf6, 0x7e, 0x4e, 0x2f, 0xb9, 0xdd, 0xee,
            0xb3, 0x46, 0x19, 0x73, 0xcd, 0x4c, 0x62, 0xab,
            0xb3, 0x50, 0x50, 0xb1, 0xad, 0xd7, 0x72, 0x99,
            0x5b, 0x82, 0x0b, 0x58, 0x4a, 0x48, 0x84, 0x89]

/-- The display vector is 32 bytes. -/
theorem bolt3FundingTxidDisplay_size : bolt3FundingTxidDisplay.size = 32 := by
  decide

/-- The internal vector is 32 bytes. -/
theorem bolt3FundingTxidInternal_size : bolt3FundingTxidInternal.size = 32 := by
  decide

/-- The BOLT 3 internal txid is exactly the reversal of the display txid. -/
theorem bolt3FundingTxidInternal_eq_reverse_display :
    bolt3FundingTxidInternal = reverseBytes bolt3FundingTxidDisplay := by
  apply bL_inj
  rw [bL_reverseBytes]
  simp [bolt3FundingTxidInternal, bolt3FundingTxidDisplay, byteList, bL]

/-- Conversely, the display txid is the reversal of the internal txid. -/
theorem bolt3FundingTxidDisplay_eq_reverse_internal :
    bolt3FundingTxidDisplay = reverseBytes bolt3FundingTxidInternal := by
  apply bL_inj
  rw [bL_reverseBytes]
  simp [bolt3FundingTxidDisplay, bolt3FundingTxidInternal, byteList, bL]

/-- The list-level reversal statement for the concrete vector. -/
theorem bolt3FundingTxid_bL_reverse :
    bL bolt3FundingTxidInternal = (bL bolt3FundingTxidDisplay).reverse := by
  decide

/-- The two orders are genuinely different on this vector, so the reversal is
not a no-op (non-vacuity of the conversion). -/
theorem bolt3FundingTxidDisplay_ne_internal :
    bolt3FundingTxidDisplay ≠ bolt3FundingTxidInternal := by
  decide

/-- The display and internal vectors are both in the exact txid domain. -/
theorem bolt3FundingTxidDisplay_isTxidBytes :
    IsTxidBytes bolt3FundingTxidDisplay :=
  bolt3FundingTxidDisplay_size

/-- The internal vector is in the exact txid domain. -/
theorem bolt3FundingTxidInternal_isTxidBytes :
    IsTxidBytes bolt3FundingTxidInternal :=
  bolt3FundingTxidInternal_size

/-- The concrete display/internal pair as a subtype bijection instance. -/
theorem bolt3FundingTxid_displayToInternal :
    TxidBytes.displayToInternal
        ⟨bolt3FundingTxidDisplay, bolt3FundingTxidDisplay_isTxidBytes⟩ =
      ⟨bolt3FundingTxidInternal, bolt3FundingTxidInternal_isTxidBytes⟩ := by
  apply Subtype.ext
  exact bolt3FundingTxidInternal_eq_reverse_display.symm

/-- A commitment wire whose funding txid is the BOLT 3 internal vector.  The
remaining fields are arbitrary; the theorem below is about the outpoint only. -/
def bolt3FundingWire : CommitmentWire where
  version := 2
  fundingTxid := bolt3FundingTxidInternal
  fundingOutputIndex := 0
  sequence := 0xfffffffe
  outputs := []
  locktime := 0

/-- A placeholder scriptCode; the outpoint theorem is independent of it. -/
def bolt3ScriptCode : ByteArray :=
  byteList [0x51]

/-- The BOLT 3 commitment-wire preimage carries the internal txid (= reverse of
the display form). -/
theorem bolt3FundingPreimage_outpointTxid_eq_reverse_display :
    (commitmentBip143Preimage bolt3FundingWire bolt3ScriptCode 1 10000000).outpointTxid =
      reverseBytes bolt3FundingTxidDisplay := by
  rw [← bolt3FundingTxidInternal_eq_reverse_display]
  exact (commitmentBip143Preimage_wire_fields
    bolt3FundingWire bolt3ScriptCode 1 10000000).2.1

/-- The same preimage carries exactly the internal vector. -/
theorem bolt3FundingPreimage_outpointTxid_eq_internal :
    (commitmentBip143Preimage bolt3FundingWire bolt3ScriptCode 1 10000000).outpointTxid =
      bolt3FundingTxidInternal :=
  (commitmentBip143Preimage_wire_fields
    bolt3FundingWire bolt3ScriptCode 1 10000000).2.1

/-- The preimage's outpoint is **not** the display vector: on this vector the
two orders differ, so a silent display-order insertion would be observable. -/
theorem bolt3FundingPreimage_outpointTxid_ne_display :
    (commitmentBip143Preimage bolt3FundingWire bolt3ScriptCode 1 10000000).outpointTxid ≠
      bolt3FundingTxidDisplay := by
  rw [bolt3FundingPreimage_outpointTxid_eq_internal]
  exact bolt3FundingTxidDisplay_ne_internal.symm

/-- The display form computed back from the preimage is the BOLT 3 display
txid. -/
theorem bolt3FundingPreimage_displayOutpointTxid :
    displayOutpointTxid
        (commitmentBip143Preimage bolt3FundingWire bolt3ScriptCode 1 10000000) =
      bolt3FundingTxidDisplay := by
  rw [displayOutpointTxid,
    bolt3FundingPreimage_outpointTxid_eq_internal,
    bolt3FundingTxidInternal_eq_reverse_display,
    reverseBytes_involutive]

/-- The concrete BOLT 3 commitment-wire preimage has a 32-byte outpoint. -/
theorem bolt3FundingPreimage_outpointTxid_size :
    (commitmentBip143Preimage bolt3FundingWire bolt3ScriptCode 1 10000000).outpointTxid.size =
      32 := by
  rw [bolt3FundingPreimage_outpointTxid_eq_internal]
  exact bolt3FundingTxidInternal_size

end LnLean.Proofs.WaveH.H10
