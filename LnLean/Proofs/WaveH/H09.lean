/-
# H09 — HTLC-wire preimage digest equals the vendored BIP 143 implementation
(PR-05, PR-02)

**Catalog issues.**

* `PR-05` (P1): wave 7 proved byte equality between a BOLT 3 preimage and the
  vendored BIP 143 encoder for the *commitment* wire
  (`commitmentBip143Preimage_eq_bip143MsgL`) and lane H07 lifted it to the
  `HtlcWire` at the preimage level (`htlcBip143Preimage_eq_bip143MsgL`).  The
  missing step was the *digest*: the preimage bytes are only useful if the
  double-SHA-256 the signer consumes is the vendored
  `Bitcoin.SigHash.signatureHashBip143Impl` of the wire transaction.
* `PR-02` (P1): the `HtlcWire` record must carry enough data for a wire-only
  sighash construction.  `HtlcWire.toTx` is an exact single-input /
  single-output transaction, so `nIn = 0` is the only in-range signing index.

## Result of this module

1. `htlcBip143Preimage_digest_eq_signatureHashBip143Impl`: for every
   `HtlcWire`, `scriptCode`, hash type and spent amount, the digest of the H07
   preimage is **literally** the vendored
   `Bitcoin.SigHash.signatureHashBip143Impl h.toTx 0 (bL scriptCode) ht
   (amountSat.toNat : Int)`.
2. `htlcBip143Preimage_digest_eq_interface`: the same digest is the
   interface-level `Bitcoin.SigHash.signatureHashBip143 h.toTx 0 ⟨scriptCode⟩
   ht amount`, i.e. the value wired into the vendored checker.
3. `htlcBip143Preimage_digest_eq_dshaL`: the digest is the vendored
   double-SHA-256 of exactly `preimageBytes`, with no re-encoding.
4. Guarded/out-of-range behaviour, for **all** input indices:
   `htlc_sighashWitnessV0_eq_vendorImpl` (the model and the vendored
   implementation totalize the `assert(nIn < vin.size())` guard identically),
   `htlc_signatureHashBip143Impl_eq_zero_of_one_le` and
   `htlc_sighashWitnessV0_eq_zero_of_one_le` (every index `≥ 1` is
   out-of-range and yields the 32-byte zero digest), and
   `htlc_guard_never_fires` (index `0` is always in range because the HTLC
   transaction has exactly one input).
5. A concrete **179-byte** preimage vector (`vectorHtlcPreimage179`) with
   `SIGHASH_NONE|ANYONECANPAY` (`0x82`, so all three sub-hashes are the BIP 143
   zero vector and the layout is decidable without hashing).  The preimage
   bytes and the vendored `bip143MsgL` bytes are both pinned to the same
   explicit 179-entry list, and the digest is `dshaL` of that list
   (`vectorHtlcPreimage179_digest_eq_vendor`,
   `vectorHtlcPreimage179_digest_bytes`).
6. Explicit premise bridges: the scriptCode length premise against BIP 143's
   `witnessScriptSizeOk` (10,000 bytes), the non-negativity and `< 2^64` facts
   for the spent `amountSat`, its `serAmountL` agreement, and an instance at
   BOLT 3's `SIGHASH_ALL` (`0x01`).

## Hypotheses / scope

* `htlcBip143Preimage` is **imported from lane H07**; it is definitionally
  `Bip143Preimage.ofTx h.toTx 0 scriptCode ht amountSat`.  If H07 is dropped,
  the exact fallback is to copy H07's four-line definition into this module;
  every theorem below only uses that definition (no H07-specific lemma).
* `scriptCode` is an explicit parameter.  For a P2WSH HTLC output it is the
  BOLT 3 offered/received HTLC witness script, whose synthesis is lane H08.
  This module makes no claim that a particular byte string is a valid BOLT 3
  script; it proves the digest for every byte string and additionally records
  the 10,000-byte witness-script premise.
* `amountSat` is the value of the **spent HTLC output** (an output of the
  commitment transaction), not `HtlcWire.valueSat` (the produced second-stage
  output).  Keeping them distinct is deliberate; identifying them would be
  unsound.  The model only ever passes the non-negative `amountSat.toNat`
  (`htlc_amount_nonneg`), matching BIP 143's `amount ≥ 0` precondition.
* `ht` is the SIGHASH type; BOLT 3 uses `SIGHASH_ALL` (`0x01`).  All theorems
  are proved for every `ht`, and the BIP 143 omission behaviour is already
  mechanized in `LnLean.Bitcoin.Sighash`.
* The hash is the vendored seam SHA-256 (`Bitcoin.SigHash.dshaL`); collision
  resistance (C1) is not used and no digest injectivity is claimed.
* No well-formedness premise is required for the field/byte/digest equalities.
  `HtlcWire.WellFormed` is only needed for the outpoint length and hence the
  `156 + CompactSize + scriptCode.size` size formula (already proved in H07).

## Anchors

* BIP 143 §3–6: ten-field witness-v0 preimage and double-SHA-256 digest;
  out-of-range `nIn` is `assert`-guarded in Core (`interpreter.cpp:1609-1687`).
* BOLT 3 "HTLC Outputs": the second-stage HTLC transaction spends exactly one
  HTLC output, so the signing input index is `0` and `SIGHASH_ALL` is used.
* Model: `LnLean/Proofs/Channel/SighashTargets.lean` §12.1/§13,
  `LnLean/Bitcoin/Sighash.lean`, `LnLean/Proofs/WaveH/H07.lean`.
-/

import LnLean.Proofs.WaveH.H07

namespace LnLean.Proofs.WaveH.H09

set_option autoImplicit false
set_option maxRecDepth 10000

open Bitcoin.Data
open Bitcoin.Serialization
open LnLean.Proofs.Channel.SighashTargets
open LnLean.Proofs.WaveH.H07

/-! ## 1. Digest equality with the vendored BIP 143 implementation -/

/-- The HTLC-wire preimage digest is the model digest of the H07 preimage,
i.e. the double-SHA-256 of exactly `preimageBytes` (no re-encoding). -/
theorem htlcBip143Preimage_digest_eq_dshaL (h : HtlcWire)
    (scriptCode : ByteArray) (ht : UInt32) (amountSat : UInt64) :
    LnLean.Bitcoin.Sighash.digest
        (htlcBip143Preimage h scriptCode ht amountSat).toPreimage =
      Bitcoin.SigHash.dshaL
        (bL (htlcBip143Preimage h scriptCode ht amountSat).preimageBytes) :=
  Bip143Preimage.toPreimage_digest_eq_dshaL _

/-- The model witness-v0 sighash of the wire transaction at index `0`
agrees with the digest of the H07 preimage.  Index `0` is in range because
`HtlcWire.toTx` has exactly one input. -/
theorem htlcBip143Preimage_digest_eq_sighashWitnessV0 (h : HtlcWire)
    (scriptCode : ByteArray) (ht : UInt32) (amountSat : UInt64) :
    LnLean.Bitcoin.Sighash.digest
        (htlcBip143Preimage h scriptCode ht amountSat).toPreimage =
      LnLean.Bitcoin.Sighash.sighashWitnessV0 h.toTx 0 scriptCode ht
        (amountSat.toNat : Int) := by
  have hguard : ¬ h.toTx.vin.length ≤ 0 := by
    rw [HtlcWire.toTx_vin_length]
    decide
  simp [LnLean.Bitcoin.Sighash.sighashWitnessV0, hguard,
    htlcBip143Preimage_toPreimage]

/-- **Main theorem (PR-05).**  The digest of the HTLC-wire BIP 143 preimage is
literally the vendored `Bitcoin.SigHash.signatureHashBip143Impl` of the wire
transaction at the single signing input.  The scriptCode, spent amount and
hash type remain explicit parameters. -/
theorem htlcBip143Preimage_digest_eq_signatureHashBip143Impl (h : HtlcWire)
    (scriptCode : ByteArray) (ht : UInt32) (amountSat : UInt64) :
    LnLean.Bitcoin.Sighash.digest
        (htlcBip143Preimage h scriptCode ht amountSat).toPreimage =
      Bitcoin.SigHash.signatureHashBip143Impl h.toTx 0 (bL scriptCode) ht
        (amountSat.toNat : Int) := by
  have hin : 0 < h.toTx.vin.length := by
    rw [HtlcWire.toTx_vin_length]
    decide
  simpa [htlcBip143Preimage] using
    Bip143Preimage.digest_eq_sighashWitnessV0_ofTx h.toTx 0 scriptCode ht
      amountSat hin

/-- Interface-level form: the digest is the vendored
`Bitcoin.SigHash.signatureHashBip143` value (`Script` wrapper) consumed by the
checker wiring. -/
theorem htlcBip143Preimage_digest_eq_interface (h : HtlcWire)
    (scriptCode : ByteArray) (ht : UInt32) (amountSat : UInt64) :
    LnLean.Bitcoin.Sighash.digest
        (htlcBip143Preimage h scriptCode ht amountSat).toPreimage =
      Bitcoin.SigHash.signatureHashBip143 h.toTx 0 ⟨scriptCode⟩ ht
        (amountSat.toNat : Int) := by
  rw [htlcBip143Preimage_digest_eq_signatureHashBip143Impl]
  rfl

/-- BOLT 3's signing hash type is `SIGHASH_ALL` (`0x01`); this is the concrete
instance of the main theorem that a BOLT 3 HTLC signature uses. -/
theorem htlcBip143Preimage_digest_eq_vendor_sighashAll (h : HtlcWire)
    (scriptCode : ByteArray) (amountSat : UInt64) :
    LnLean.Bitcoin.Sighash.digest
        (htlcBip143Preimage h scriptCode 0x01 amountSat).toPreimage =
      Bitcoin.SigHash.signatureHashBip143Impl h.toTx 0 (bL scriptCode) 0x01
        (amountSat.toNat : Int) :=
  htlcBip143Preimage_digest_eq_signatureHashBip143Impl h scriptCode 0x01
    amountSat

/-! ## 2. Guarded / out-of-range behaviour

`HtlcWire.toTx` has exactly one input.  The BIP 143 guard
`tx.vin.length ≤ nIn` in both the model (`sighashWitnessV0`) and the vendored
implementation (`signatureHashBip143Impl`) therefore fires exactly for
`nIn ≥ 1`, where both return the 32-byte zero digest. -/

/-- Index `0` is always in range: the guard never fires on the HTLC path. -/
theorem htlc_guard_never_fires (h : HtlcWire) :
    ¬ h.toTx.vin.length ≤ 0 := by
  rw [HtlcWire.toTx_vin_length]
  decide

/-- The guard fires exactly for the out-of-range indices `nIn ≥ 1`. -/
theorem htlc_guard_iff (h : HtlcWire) (nIn : Nat) :
    h.toTx.vin.length ≤ nIn ↔ 1 ≤ nIn := by
  rw [HtlcWire.toTx_vin_length]

/-- The vendored implementation's guarded branch is the 32-byte zero vector. -/
theorem htlc_signatureHashBip143Impl_eq_zero_of_guard (h : HtlcWire)
    (nIn : Nat) (scriptCode : ByteArray) (ht : UInt32) (amountSat : UInt64)
    (hguard : h.toTx.vin.length ≤ nIn) :
    Bitcoin.SigHash.signatureHashBip143Impl h.toTx nIn (bL scriptCode) ht
        (amountSat.toNat : Int) =
      LnLean.Bitcoin.Sighash.zeroHash := by
  simp [Bitcoin.SigHash.signatureHashBip143Impl, hguard,
    LnLean.Bitcoin.Sighash.zeroHash]

/-- **Out-of-range HTLC indices.**  Every `nIn ≥ 1` is out of range for the
single-input HTLC transaction, so the vendored digest is the zero vector. -/
theorem htlc_signatureHashBip143Impl_eq_zero_of_one_le (h : HtlcWire)
    (nIn : Nat) (hn : 1 ≤ nIn) (scriptCode : ByteArray) (ht : UInt32)
    (amountSat : UInt64) :
    Bitcoin.SigHash.signatureHashBip143Impl h.toTx nIn (bL scriptCode) ht
        (amountSat.toNat : Int) =
      LnLean.Bitcoin.Sighash.zeroHash :=
  htlc_signatureHashBip143Impl_eq_zero_of_guard h nIn scriptCode ht amountSat
    ((htlc_guard_iff h nIn).mpr hn)

/-- The model sighash totalizes the same guard to the zero vector. -/
theorem htlc_sighashWitnessV0_eq_zero_of_one_le (h : HtlcWire)
    (nIn : Nat) (hn : 1 ≤ nIn) (scriptCode : ByteArray) (ht : UInt32)
    (amountSat : UInt64) :
    LnLean.Bitcoin.Sighash.sighashWitnessV0 h.toTx nIn scriptCode ht
        (amountSat.toNat : Int) =
      LnLean.Bitcoin.Sighash.zeroHash := by
  have hguard : h.toTx.vin.length ≤ nIn := (htlc_guard_iff h nIn).mpr hn
  simp [LnLean.Bitcoin.Sighash.sighashWitnessV0, hguard]

/-- **Guard agreement for every input index.**  The model and the vendored
implementation agree at `nIn = 0` (digest) and at every out-of-range index
(zero digest). -/
theorem htlc_sighashWitnessV0_eq_vendorImpl (h : HtlcWire) (nIn : Nat)
    (scriptCode : ByteArray) (ht : UInt32) (amountSat : UInt64) :
    LnLean.Bitcoin.Sighash.sighashWitnessV0 h.toTx nIn scriptCode ht
        (amountSat.toNat : Int) =
      Bitcoin.SigHash.signatureHashBip143Impl h.toTx nIn (bL scriptCode) ht
        (amountSat.toNat : Int) :=
  LnLean.Bitcoin.Sighash.sighashWitnessV0_eq_vendorImpl h.toTx nIn scriptCode
    ht (amountSat.toNat : Int)

/-- At the in-range signing index the vendored implementation takes its
unguarded branch, i.e. the digest is the vendored double-SHA-256 of
`bip143MsgL` of the wire transaction. -/
theorem htlc_signatureHashBip143Impl_eq_dshaL_bip143MsgL (h : HtlcWire)
    (scriptCode : ByteArray) (ht : UInt32) (amountSat : UInt64) :
    Bitcoin.SigHash.signatureHashBip143Impl h.toTx 0 (bL scriptCode) ht
        (amountSat.toNat : Int) =
      Bitcoin.SigHash.dshaL
        (Bitcoin.SigHash.bip143MsgL h.toTx 0 (bL scriptCode) ht
          (amountSat.toNat : Int)) := by
  have hguard : ¬ h.toTx.vin.length ≤ 0 := htlc_guard_never_fires h
  simp [Bitcoin.SigHash.signatureHashBip143Impl, hguard]

/-! ## 3. Sizes -/

/-- The vendored HTLC-wire digest is always 32 bytes, including on the guarded
branch. -/
theorem htlc_signatureHashBip143Impl_size (h : HtlcWire) (nIn : Nat)
    (scriptCode : ByteArray) (ht : UInt32) (amountSat : UInt64) :
    (Bitcoin.SigHash.signatureHashBip143Impl h.toTx nIn (bL scriptCode) ht
      (amountSat.toNat : Int)).size = 32 := by
  unfold Bitcoin.SigHash.signatureHashBip143Impl
  split
  · simpa [LnLean.Bitcoin.Sighash.zeroHash] using
      LnLean.Bitcoin.Sighash.zeroHash_size
  · exact Bitcoin.Crypto.Seam.sha256d_size _

/-- The model HTLC-wire digest is 32 bytes. -/
theorem htlc_digest_size (h : HtlcWire) (scriptCode : ByteArray) (ht : UInt32)
    (amountSat : UInt64) :
    (LnLean.Bitcoin.Sighash.digest
      (htlcBip143Preimage h scriptCode ht amountSat).toPreimage).size = 32 := by
  rw [htlcBip143Preimage_digest_eq_signatureHashBip143Impl]
  exact htlc_signatureHashBip143Impl_size h 0 scriptCode ht amountSat

/-! ## 4. Explicit scriptCode / amount / sighash-type premises -/

/-- BIP 143's witness-script size premise (10,000 bytes), stated on the
explicit `scriptCode` parameter. -/
theorem htlc_witnessScriptSizeOk_iff (scriptCode : ByteArray) :
    Bitcoin.SigHash.witnessScriptSizeOk (bL scriptCode) = true ↔
      scriptCode.size ≤ 10000 := by
  by_cases h : scriptCode.size ≤ 10000 <;>
    simp [Bitcoin.SigHash.witnessScriptSizeOk,
      LnLean.Bitcoin.Sighash.length_bL, h]

/-- The spent amount as passed to the vendored encoder is non-negative; this
is BIP 143's `amount ≥ 0` precondition (`SWT-055`), discharged by the
`UInt64` parameter. -/
theorem htlc_amount_nonneg (amountSat : UInt64) :
    (0 : Int) ≤ (amountSat.toNat : Int) :=
  Int.natCast_nonneg _

/-- The spent amount is inside the unsigned 64-bit envelope. -/
theorem htlc_amount_lt_two_pow_64 (amountSat : UInt64) :
    (amountSat.toNat : Int) < (2 : Int) ^ 64 := by
  exact_mod_cast amountSat.toNat_lt

/-- The vendored `serAmountL` of the passed amount is exactly the unsigned
8-byte little-endian serialization of `amountSat`: no sign extension and no
value change. -/
theorem htlc_serAmountL_amount (amountSat : UInt64) :
    Bitcoin.SigHash.serAmountL (amountSat.toNat : Int) =
      Bitcoin.SigHash.serU64L amountSat := by
  rw [Bitcoin.SigHash.serAmountL]
  simpa using serU64L_ofNat_toNat amountSat

/-- `SIGHASH_ALL` (`0x01`) is the omission-free class: neither ANYONECANPAY nor
NONE/SINGLE zeroes a sub-hash, so all three sub-hashes are transaction folds.
This records that the `ht` premise in the main theorem is not doing hidden
work on the BOLT 3 default path. -/
theorem htlc_sighashAll_subhashes (h : HtlcWire) (scriptCode : ByteArray)
    (amountSat : UInt64) :
    (htlcBip143Preimage h scriptCode 0x01 amountSat).hashPrevouts =
        LnLean.Bitcoin.Sighash.dsha
          (h.toTx.vin.foldl
            (fun acc i => acc ++ LnLean.Bitcoin.Sighash.serOutpoint i.prevout)
            ByteArray.empty) ∧
    (htlcBip143Preimage h scriptCode 0x01 amountSat).hashSequence =
        LnLean.Bitcoin.Sighash.dsha
          (h.toTx.vin.foldl
            (fun acc i => acc ++ LnLean.Bitcoin.Sighash.serU32LE i.sequence)
            ByteArray.empty) ∧
    (htlcBip143Preimage h scriptCode 0x01 amountSat).hashOutputs =
        LnLean.Bitcoin.Sighash.dsha
          (h.toTx.vout.foldl
            (fun acc o => acc ++ LnLean.Bitcoin.Sighash.serTxOut o)
            ByteArray.empty) := by
  have hbase : Bitcoin.SigHash.htBase (0x01 : UInt32) =
      Bitcoin.SigHash.HtBase.all := by decide
  have hacp : Bitcoin.SigHash.htAcp (0x01 : UInt32) = false := by decide
  refine ⟨?_, ?_, ?_⟩
  · simp [htlcBip143Preimage, Bip143Preimage.ofTx,
      LnLean.Bitcoin.Sighash.hashPrevoutsOf, hacp]
  · simp [htlcBip143Preimage, Bip143Preimage.ofTx,
      LnLean.Bitcoin.Sighash.hashSequenceOf, hbase, hacp]
  · simp [htlcBip143Preimage, Bip143Preimage.ofTx,
      LnLean.Bitcoin.Sighash.hashOutputsOf, hbase]

/-! ## 5. Concrete 179-byte vector

A 22-byte scriptCode (`0x00 0x14 ‖ 20 bytes`) gives the canonical
`156 + 1 + 22 = 179`-byte BIP 143 preimage.  `ht = 0x82`
(`SIGHASH_NONE | ANYONECANPAY`) makes all three sub-hashes the BIP 143 zero
vector, so both the model preimage and the vendored `bip143MsgL` are decidable
byte-for-byte: no hashing is needed to check the layout.
`amountSat = 7000 = 0x1b58` is the spent HTLC output value. -/

/-- A 22-byte scriptCode placeholder.  Its length is what pins the 179-byte
preimage size; the bytes are opaque (lane H08 synthesizes the real BOLT 3 HTLC
scripts). -/
def vectorHtlcScriptCode179 : ByteArray :=
  byteList [0x00, 0x14] ++ byteList (List.replicate 20 0x44)

theorem vectorHtlcScriptCode179_size : vectorHtlcScriptCode179.size = 22 := by
  decide

/-- The concrete HTLC wire: one input spending commitment output `1`. -/
def vectorHtlcWire179 : HtlcWire :=
  { version := 2
    commitmentTxid := hash32 0x66
    commitmentOutputIndex := 1
    sequence := 0xffffffff
    valueSat := 5000
    scriptPubKey := byteList [0x00, 0x14] ++
      byteList (List.replicate 20 0x55)
    locktime := 0 }

/-- The 179-byte HTLC preimage vector. -/
def vectorHtlcPreimage179 : Bip143Preimage :=
  htlcBip143Preimage vectorHtlcWire179 vectorHtlcScriptCode179 0x82 7000

/-- The exact 179 consensus bytes of the vector. -/
theorem vectorHtlcPreimage179_bytes :
    bL vectorHtlcPreimage179.preimageBytes =
      [0x02, 0x00, 0x00, 0x00] ++
      List.replicate 32 0x00 ++
      List.replicate 32 0x00 ++
      List.replicate 32 0x66 ++
      [0x01, 0x00, 0x00, 0x00, 0x16, 0x00, 0x14] ++
      List.replicate 20 0x44 ++
      [0x58, 0x1b, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] ++
      [0xff, 0xff, 0xff, 0xff] ++
      List.replicate 32 0x00 ++
      [0x00, 0x00, 0x00, 0x00, 0x82, 0x00, 0x00, 0x00] := by
  decide

theorem vectorHtlcPreimage179_size :
    (bL vectorHtlcPreimage179.preimageBytes).length = 179 := by
  decide

/-- The vendored encoder produces exactly the same 179 bytes on the vector. -/
theorem vectorHtlcPreimage179_vendor_bytes :
    Bitcoin.SigHash.bip143MsgL vectorHtlcWire179.toTx 0
        (bL vectorHtlcScriptCode179) 0x82 7000 =
      [0x02, 0x00, 0x00, 0x00] ++
      List.replicate 32 0x00 ++
      List.replicate 32 0x00 ++
      List.replicate 32 0x66 ++
      [0x01, 0x00, 0x00, 0x00, 0x16, 0x00, 0x14] ++
      List.replicate 20 0x44 ++
      [0x58, 0x1b, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] ++
      [0xff, 0xff, 0xff, 0xff] ++
      List.replicate 32 0x00 ++
      [0x00, 0x00, 0x00, 0x00, 0x82, 0x00, 0x00, 0x00] := by
  decide

/-- Outpoint slice at byte 68: commitment txid in internal order (never
reversed), then the 4-byte little-endian output index `1`. -/
theorem vectorHtlcPreimage179_outpoint_bytes :
    ((bL vectorHtlcPreimage179.preimageBytes).drop 68).take 36 =
      List.replicate 32 0x66 ++ [0x01, 0x00, 0x00, 0x00] := by
  decide

/-- scriptCode slice at byte 104: one-byte CompactSize `0x16 = 22`. -/
theorem vectorHtlcPreimage179_scriptCode_prefix :
    ((bL vectorHtlcPreimage179.preimageBytes).drop 104).take 3 =
      [0x16, 0x00, 0x14] := by
  decide

/-- Amount slice at byte 127: `7000 = 0x1b58` in 8-byte little-endian. -/
theorem vectorHtlcPreimage179_amount_bytes :
    ((bL vectorHtlcPreimage179.preimageBytes).drop 127).take 8 =
      [0x58, 0x1b, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] := by
  decide

/-- The general theorem instantiates on the concrete vector. -/
theorem vectorHtlcPreimage179_digest_eq_vendor :
    LnLean.Bitcoin.Sighash.digest vectorHtlcPreimage179.toPreimage =
      Bitcoin.SigHash.signatureHashBip143Impl vectorHtlcWire179.toTx 0
        (bL vectorHtlcScriptCode179) 0x82 7000 :=
  htlcBip143Preimage_digest_eq_signatureHashBip143Impl vectorHtlcWire179
    vectorHtlcScriptCode179 0x82 7000

/-- The vector digest is the vendored double-SHA-256 of the **explicit**
179-byte list, so the concrete digest is pinned without computing the hash. -/
theorem vectorHtlcPreimage179_digest_bytes :
    LnLean.Bitcoin.Sighash.digest vectorHtlcPreimage179.toPreimage =
      Bitcoin.SigHash.dshaL
        ([0x02, 0x00, 0x00, 0x00] ++
         List.replicate 32 0x00 ++
         List.replicate 32 0x00 ++
         List.replicate 32 0x66 ++
         [0x01, 0x00, 0x00, 0x00, 0x16, 0x00, 0x14] ++
         List.replicate 20 0x44 ++
         [0x58, 0x1b, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] ++
         [0xff, 0xff, 0xff, 0xff] ++
         List.replicate 32 0x00 ++
         [0x00, 0x00, 0x00, 0x00, 0x82, 0x00, 0x00, 0x00]) := by
  rw [Bip143Preimage.toPreimage_digest_eq_dshaL, vectorHtlcPreimage179_bytes]

/-- The vector digest has the consensus 32-byte size. -/
theorem vectorHtlcPreimage179_digest_size :
    (LnLean.Bitcoin.Sighash.digest vectorHtlcPreimage179.toPreimage).size = 32 :=
  htlc_digest_size vectorHtlcWire179 vectorHtlcScriptCode179 0x82 7000

/-- The vector is in the HTLC wire domain (32-byte outpoint, in-range value and
script), so the 179-byte size formula applies. -/
theorem vectorHtlcWire179_wellFormed : vectorHtlcWire179.WellFormed := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- The 179-byte size also follows from the general size formula under the
wire-domain premise. -/
theorem vectorHtlcPreimage179_size_of_wire :
    vectorHtlcPreimage179.preimageBytes.size =
      156 + compactSizeWidth vectorHtlcScriptCode179.size +
        vectorHtlcScriptCode179.size :=
  htlcBip143Preimage_preimageBytes_size vectorHtlcWire179
    vectorHtlcWire179_wellFormed vectorHtlcScriptCode179 0x82 7000

end LnLean.Proofs.WaveH.H09
