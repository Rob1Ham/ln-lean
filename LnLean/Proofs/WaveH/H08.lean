/-
# Wave 8 lane H08 — BOLT 3 HTLC witness scripts, scriptCode synthesis, and the
HTLC BIP 143 preimage (`PR-05`, `PR-02`)

**English claim.**  The second-stage HTLC transaction (HTLC-timeout or
HTLC-success) spends one offered or received HTLC output of a BOLT 3
commitment transaction.  That output is a version-0 P2WSH whose witness
script is the BOLT 3 "offered HTLC" / "received HTLC" script.  For a version-0
P2WSH spend, BIP 143 defines the `scriptCode` of the signature hash to be the
*witness script itself* (CompactSize-prefixed in the preimage, no
`OP_CODESEPARATOR` truncation).  This lane synthesizes those two witness
scripts as exact byte strings, proves their sizes and byte layout, and
instantiates the lane-H07 HTLC preimage with the synthesized `scriptCode`.

## Result

1. `HtlcScriptView` records the BOLT 3 HTLC-script parameters explicitly:
   the revocation public key and its `HASH160`, the remote and local HTLC
   public keys, the 32-byte payment hash and its `HASH160`, and the CLTV
   expiry.  `HashesMatch` names the C2 (`HASH160 = RIPEMD160(SHA256(·))`)
   bridge; it is a predicate, never an axiom.
2. `offeredWitnessScript`, `offeredWitnessScriptAnchors`,
   `receivedWitnessScript`, and `receivedWitnessScriptAnchors` are the four
   BOLT 3 witness scripts: the offered script carries the hash lock and the
   `OP_NOTIF`/`OP_CHECKMULTISIG` timeout branch, the received script carries
   the hash lock and the `<cltv_expiry> OP_CLTV OP_DROP` timeout branch.  The
   `...Anchors` variants append BOLT 3's `OP_1 OP_CSV OP_DROP`.
3. `scriptNumLen` / `pushScriptNum` give the *minimal* little-endian
   `CScriptNum` push used for `<cltv_expiry>` (one to four operand bytes on
   the CLTV domain, plus a sign byte only when needed).  The push value is
   proved equal to the expiry (`pushValue_pushScriptNum`) and the encoding is
   injective on the CLTV domain (`pushScriptNum_inj`).
4. Exact sizes: offered `133`, offered with anchors `136`,
   received `135 + (pushScriptNum cltv).size` (so `139` for a three-byte
   operand and `140` for the four-byte operand that BOLT 3's Appendix A weight
   table assumes), received with anchors `138 + (pushScriptNum cltv).size`.
5. Byte layout: `bL_offeredWitnessScript` and `bL_receivedWitnessScript`
   give the full left-to-right byte string, and the field slices
   (`..._paymentHash_slice`, `..._revocationHash_slice`, `..._localKey_slice`,
   `..._cltv_slice`) show that the revocation-key hash, the payment-hash
   branch, the two HTLC keys and the CLTV operand occur at fixed offsets with
   fixed lengths.  Equality of two synthesized scriptCodes therefore fixes
   each of those fields (`..._paymentHash_inj`, `..._cltv_inj`).
6. `htlcBip143Preimage` is the lane-H07 HTLC preimage: a `Bip143Preimage` for
   `HtlcWire.toTx` at input index `0` with the supplied `scriptCode`.  Its
   wire fields (version, outpoint, index, sequence, locktime), `scriptCode`
   and `amountSat` are proved by projection, and its `preimageBytes` are
   byte-equal to the vendored `Bitcoin.SigHash.bip143MsgL`
   (`htlcBip143Preimage_eq_bip143MsgL`).  `htlcWirePreimage` instantiates it
   with `witnessScript side anchors s`.  Because `HtlcWire.toTx` has exactly
   one input, the digest is also equal to the vendored
   `signatureHashBip143Impl` with no out-of-range guard
   (`htlcWirePreimage_digest_eq_vendorImpl`); the standalone guarded
   vector/digest lane is H09.
7. Preimage sizes: `156 + CompactSize(scriptCode.size) + scriptCode.size`,
   i.e. `290` (offered), `293` (offered, anchors), `296`/`297` (received with
   a three- or four-byte CLTV operand), `299`/`300` (received, anchors).

## Scope

* The scripts are byte-exact BOLT 3 templates.  `HASH160` and `SHA256` are
  supplied as parameters (`HashesMatch`, `htlcScriptPubKey`); C2/C1 are the
  documented assumptions, not proved here.
* `offered`/`received` are relative to the commitment owner's view, matching
  BOLT 3's output names.  The model does not decide which party holds which
  key; that is a construction-site choice.
* The BOLT 3 `to_local`-style contest delay is not part of the HTLC script,
  except through the anchor variant's one-block `OP_CSV`.
* The CLTV encoding is the consensus-minimal `CScriptNum` push.  BOLT 3's
  Appendix A weight table budgets four operand bytes; that is the
  `2^23 ≤ cltv < 2^31` case here (`140` bytes).  Realistic current heights
  use three operand bytes (`139` bytes); both are proved.
* The digest equality here is the unguarded, in-range case for the one-input
  `HtlcWire`.  Wire transaction serialization/parsing and the out-of-range
  behavior are lanes H09/H11.
* No accumulator/`OP_CODESEPARATOR` cases are modelled: the BOLT 3 HTLC
  scripts contain no `OP_CODESEPARATOR`, so `scriptCode` is the full witness
  script.

## Anchors

* BOLT 3 §"Offered HTLC Outputs" (`refs/bolts/03-transactions.md:199-250`) and
  §"Received HTLC Outputs" (`:251-304`): the two witness-script templates and
  the `option_anchors` `1 OP_CHECKSEQUENCEVERIFY OP_DROP` suffix.
* BOLT 3 §"HTLC-Timeout and HTLC-Success Transactions" (`:355-385`): the
  second-stage transaction spends the matching HTLC output; locktime is
  `cltv_expiry` for timeout and `0` for success.
* BOLT 3 Appendix A (`:1086-1180`): `offered_htlc_script: 133` bytes,
  `accepted_htlc_script: 140` bytes, `+3` with `option_anchors`.
* BIP 143 §"SignatureHash" (`scriptCode` of a P2WSH spend is the witness
  script).
* `refs/rust-lightning/lightning/src/ln/chan_utils.rs:761-835`
  (`get_htlc_redeemscript_with_explicit_keys`).
* Model: `LnLean/Proofs/Channel/SighashTargets.lean` (`HtlcWire`,
  `Bip143Preimage`, `compactSizeWidth`), `LnLean/Bitcoin/Sighash.lean`
  (`Preimage`, `encode`, `bip143MsgL` bridge).
-/

import LnLean.Proofs.Channel.SighashTargets
import LnLean.Proofs.WaveH.H07

namespace LnLean.Proofs.WaveH.H08

set_option autoImplicit false
set_option maxHeartbeats 1000000

open LnLean
open LnLean.Bitcoin
open Bitcoin.Data
open Bitcoin.Serialization
open LnLean.Proofs.Channel.SighashTargets

/-! ## 0. Byte-length bridges -/

/-- The length of the list view is the byte length. -/
@[simp] theorem bL_length (b : ByteArray) : (bL b).length = b.size :=
  LnLean.Bitcoin.Sighash.length_bL b

/-- The byte-array size of `bytesOfList` is the list length. -/
@[simp] theorem bytesOfList_size (l : List UInt8) : (bytesOfList l).size = l.length := by
  simp [bytesOfList, List.size_toByteArray]

/-! ## 1. Minimal little-endian script numbers -/

/-- Little-endian operand of `width` bytes: byte `i` is
`(n / 256^i) % 256`.  For the minimal width this is the unsigned magnitude of
`n`. -/
def leOperand (width n : Nat) : ByteArray :=
  bytesOfList ((List.range width).map (fun i => ((n / 256 ^ i) % 256).toUInt8))

theorem leOperand_size (width n : Nat) : (leOperand width n).size = width := by
  simp [leOperand]

/-- Value of a little-endian byte string. -/
def leVal : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * leVal bs

/-- The value of a concatenation: the second piece is shifted by
`256 ^ length` of the first. -/
theorem leVal_append (a b : List UInt8) :
    leVal (a ++ b) = leVal a + 256 ^ a.length * leVal b := by
  induction a with
  | nil => simp [leVal]
  | cons x xs ih =>
      simp only [List.cons_append, leVal, ih, List.length_cons]
      rw [Nat.pow_succ, Nat.mul_add, Nat.mul_assoc (256 ^ xs.length) 256 (leVal b),
        Nat.mul_left_comm (256 ^ xs.length) 256 (leVal b)]
      omega

theorem leVal_singleton (x : UInt8) : leVal [x] = x.toNat := by
  simp [leVal]

/-- `n % (a * b) = n % a + a * ((n / a) % b)`: the low digit plus the shifted
quotient digit. -/
theorem mod_mul_right_eq (n a b : Nat) :
    n % (a * b) = n % a + a * ((n / a) % b) := by
  rw [← Nat.mod_add_div (n % (a * b)) a]
  rw [Nat.mod_mul_right_mod n a b, Nat.mod_mul_right_div_self n a b]

/-- `leOperand` reads back as `n` modulo the width's capacity. -/
theorem leVal_range_map (width n : Nat) :
    leVal ((List.range width).map (fun i => ((n / 256 ^ i) % 256).toUInt8)) =
      n % 256 ^ width := by
  induction width with
  | zero => simp [leVal, Nat.mod_one]
  | succ w ih =>
      rw [List.range_succ, List.map_append, leVal_append, ih]
      simp only [List.length_map, List.length_range, List.map_singleton,
        leVal_singleton]
      rw [Nat.pow_succ, mod_mul_right_eq n (256 ^ w) 256]
      have hdigit : ((n / 256 ^ w) % 256).toUInt8.toNat = (n / 256 ^ w) % 256 := by
        rw [Nat.toUInt8_eq]
        exact UInt8.toNat_ofNat_of_lt (Nat.mod_lt _ (by decide))
      rw [hdigit]

theorem leVal_leOperand (width n : Nat) :
    leVal (bL (leOperand width n)) = n % 256 ^ width := by
  simpa [leOperand] using leVal_range_map width n

/-- Minimal `CScriptNum` operand length of `n`: the smallest `k` with
`n < 2^(8k-1)`, i.e. one to four bytes on the CLTV domain `n < 2^31`, and a
five-byte fallback outside that domain (not claimed minimal). -/
def scriptNumLen (n : Nat) : Nat :=
  if n = 0 then 0
  else if n < 0x80 then 1
  else if n < 0x8000 then 2
  else if n < 0x800000 then 3
  else if n < 0x80000000 then 4
  else 5

/-- The minimal little-endian script-number operand. -/
def scriptNumOperand (n : Nat) : ByteArray := leOperand (scriptNumLen n) n

/-- The minimal push of the script number: `pushData` of the operand. -/
def pushScriptNum (n : Nat) : ByteArray := pushData (scriptNumOperand n)

/-- The unsigned integer encoded by a push's operand bytes. -/
def pushValue (p : ByteArray) : Nat := leVal (bL p).tail

theorem scriptNumLen_eq_one (n : Nat) (h0 : n ≠ 0) (h1 : n < 0x80) :
    scriptNumLen n = 1 := by
  unfold scriptNumLen
  simp [h0, h1]

theorem scriptNumLen_eq_two (n : Nat) (h1 : 0x80 ≤ n) (h2 : n < 0x8000) :
    scriptNumLen n = 2 := by
  unfold scriptNumLen
  have h0 : n ≠ 0 := by omega
  have h1' : ¬ n < 0x80 := by omega
  simp [h0, h1', h2]

theorem scriptNumLen_eq_three (n : Nat) (h2 : 0x8000 ≤ n) (h3 : n < 0x800000) :
    scriptNumLen n = 3 := by
  unfold scriptNumLen
  have h0 : n ≠ 0 := by omega
  have h1 : ¬ n < 0x80 := by omega
  have h2' : ¬ n < 0x8000 := by omega
  simp [h0, h1, h2', h3]

theorem scriptNumLen_eq_four (n : Nat) (h3 : 0x800000 ≤ n)
    (h4 : n < 0x80000000) : scriptNumLen n = 4 := by
  unfold scriptNumLen
  have h0 : n ≠ 0 := by omega
  have h1 : ¬ n < 0x80 := by omega
  have h2 : ¬ n < 0x8000 := by omega
  have h3' : ¬ n < 0x800000 := by omega
  simp [h0, h1, h2, h3', h4]

theorem scriptNumOperand_size (n : Nat) :
    (scriptNumOperand n).size = scriptNumLen n :=
  leOperand_size _ _

theorem pushScriptNum_size (n : Nat) :
    (pushScriptNum n).size = scriptNumLen n + 1 := by
  simp [pushScriptNum, scriptNumOperand, leOperand_size, pushData]
  omega

/-- The push operand is inside the width's capacity on the CLTV domain. -/
theorem lt_pow_scriptNumLen (n : Nat) (h : n < 0x80000000) :
    n < 256 ^ scriptNumLen n := by
  unfold scriptNumLen
  by_cases h0 : n = 0
  · simp [h0]
  · by_cases h1 : n < 0x80
    · simp [h0, h1]
      omega
    · by_cases h2 : n < 0x8000
      · simp [h0, h1, h2]
        omega
      · by_cases h3 : n < 0x800000
        · simp [h0, h1, h2, h3]
          omega
        · by_cases h4 : n < 0x80000000
          · simp [h0, h1, h2, h3, h4]
            omega
          · omega

/-- **The push encodes the expiry.**  On the CLTV domain the operand reads
back as the integer supplied. -/
theorem pushValue_pushScriptNum (n : Nat) (h : n < 0x80000000) :
    pushValue (pushScriptNum n) = n := by
  have hcap := lt_pow_scriptNumLen n h
  simp [pushValue, pushScriptNum, pushData, scriptNumOperand, leVal_leOperand,
    Nat.mod_eq_of_lt hcap]

/-- The minimal script-number push is injective on the CLTV domain. -/
theorem pushScriptNum_inj {c₁ c₂ : Nat} (h₁ : c₁ < 0x80000000)
    (h₂ : c₂ < 0x80000000) (h : pushScriptNum c₁ = pushScriptNum c₂) :
    c₁ = c₂ := by
  have v₁ := pushValue_pushScriptNum c₁ h₁
  have v₂ := pushValue_pushScriptNum c₂ h₂
  rw [h] at v₁
  exact v₁.symm.trans v₂

/-! ## 2. The BOLT 3 HTLC script parameters -/

/-- The explicit parameters of a BOLT 3 offered/received HTLC witness script.

* `revocationPubKey` / `revocationKeyHash160`: the revocation key and
  `HASH160(revocationpubkey)` in the outer `OP_DUP OP_HASH160 ... OP_EQUAL`
  branch.
* `remoteHtlcPubKey`, `localHtlcPubKey`: the two 33-byte HTLC keys.
* `paymentHash` / `paymentHash160`: the 32-byte hash lock and
  `HASH160(payment_hash)` in the hash-lock branch.
* `cltvExpiry`: the absolute CLTV expiry of the received HTLC timeout branch
  (the offered script's expiry is the *transaction* locktime instead). -/
structure HtlcScriptView where
  revocationPubKey : PubKey
  revocationKeyHash160 : ByteArray
  remoteHtlcPubKey : PubKey
  localHtlcPubKey : PubKey
  paymentHash : PaymentHash
  paymentHash160 : ByteArray
  cltvExpiry : Nat
deriving Repr, BEq

namespace HtlcScriptView

/-- Wire-domain sizes of the explicit parameters. -/
def WellFormed (s : HtlcScriptView) : Prop :=
  s.revocationPubKey.bytes.size = 33 ∧
  s.revocationKeyHash160.size = 20 ∧
  s.remoteHtlcPubKey.bytes.size = 33 ∧
  s.localHtlcPubKey.bytes.size = 33 ∧
  s.paymentHash.bytes.size = 32 ∧
  s.paymentHash160.size = 20

/-- **C2 bridge (explicit hypothesis, never an axiom).**  `HASH160` of the
revocation key and of the 32-byte payment hash produce the script's 20-byte
hash fields. -/
def HashesMatch (hash160 : ByteArray → ByteArray) (s : HtlcScriptView) : Prop :=
  s.revocationKeyHash160 = hash160 s.revocationPubKey.bytes ∧
  s.paymentHash160 = hash160 s.paymentHash.bytes

end HtlcScriptView

/-! ## 3. The four BOLT 3 HTLC witness scripts -/

/-- Shared head of both HTLC scripts:
`OP_DUP OP_HASH160 <HASH160(revocationpubkey)> OP_EQUAL OP_IF OP_CHECKSIG
OP_ELSE <remote_htlcpubkey> OP_SWAP OP_SIZE 32 OP_EQUAL`. -/
def htlcScriptIntro (s : HtlcScriptView) : ByteArray :=
  bytesOfList [0x76, 0xa9] ++ pushData s.revocationKeyHash160 ++
    bytesOfList [0x87, 0x63, 0xac, 0x67] ++
    pushData s.remoteHtlcPubKey.bytes ++
    bytesOfList [0x7c, 0x82, 0x01, 0x20, 0x87]

/-- **Offered HTLC witness script** (no `option_anchors`), BOLT 3
`:199-231`:

```text
OP_DUP OP_HASH160 <HASH160(revocationpubkey)> OP_EQUAL
OP_IF OP_CHECKSIG
OP_ELSE <remote_htlcpubkey> OP_SWAP OP_SIZE 32 OP_EQUAL
  OP_NOTIF OP_DROP 2 OP_SWAP <local_htlcpubkey> 2 OP_CHECKMULTISIG
  OP_ELSE OP_HASH160 <HASH160(payment_hash)> OP_EQUALVERIFY OP_CHECKSIG
  OP_ENDIF
OP_ENDIF
```

The timeout branch does not carry the CLTV expiry: BOLT 3 puts `cltv_expiry`
in the HTLC-timeout transaction's `nLockTime`. -/
def offeredWitnessScript (s : HtlcScriptView) : ByteArray :=
  htlcScriptIntro s ++
    bytesOfList [0x64, 0x75, 0x52, 0x7c] ++ pushData s.localHtlcPubKey.bytes ++
    bytesOfList [0x52, 0xae, 0x67, 0xa9] ++ pushData s.paymentHash160 ++
    bytesOfList [0x88, 0xac, 0x68, 0x68]

/-- Offered HTLC witness script with `option_anchors`: the same script with
`OP_1 OP_CHECKSEQUENCEVERIFY OP_DROP` appended before the outer `OP_ENDIF`
(BOLT 3 `:233-245`). -/
def offeredWitnessScriptAnchors (s : HtlcScriptView) : ByteArray :=
  htlcScriptIntro s ++
    bytesOfList [0x64, 0x75, 0x52, 0x7c] ++ pushData s.localHtlcPubKey.bytes ++
    bytesOfList [0x52, 0xae, 0x67, 0xa9] ++ pushData s.paymentHash160 ++
    bytesOfList [0x88, 0xac, 0x68, 0x51, 0xb2, 0x75, 0x68]

/-- **Received HTLC witness script** (no `option_anchors`), BOLT 3
`:251-283`:

```text
OP_DUP OP_HASH160 <HASH160(revocationpubkey)> OP_EQUAL
OP_IF OP_CHECKSIG
OP_ELSE <remote_htlcpubkey> OP_SWAP OP_SIZE 32 OP_EQUAL
  OP_IF OP_HASH160 <HASH160(payment_hash)> OP_EQUALVERIFY
        2 OP_SWAP <local_htlcpubkey> 2 OP_CHECKMULTISIG
  OP_ELSE OP_DROP <cltv_expiry> OP_CHECKLOCKTIMEVERIFY OP_DROP OP_CHECKSIG
  OP_ENDIF
OP_ENDIF
``` -/
def receivedWitnessScript (s : HtlcScriptView) : ByteArray :=
  htlcScriptIntro s ++
    bytesOfList [0x63, 0xa9] ++ pushData s.paymentHash160 ++
    bytesOfList [0x88, 0x52, 0x7c] ++ pushData s.localHtlcPubKey.bytes ++
    bytesOfList [0x52, 0xae, 0x67, 0x75] ++ pushScriptNum s.cltvExpiry ++
    bytesOfList [0xb1, 0x75, 0xac, 0x68, 0x68]

/-- Received HTLC witness script with `option_anchors` (BOLT 3 `:285-297`). -/
def receivedWitnessScriptAnchors (s : HtlcScriptView) : ByteArray :=
  htlcScriptIntro s ++
    bytesOfList [0x63, 0xa9] ++ pushData s.paymentHash160 ++
    bytesOfList [0x88, 0x52, 0x7c] ++ pushData s.localHtlcPubKey.bytes ++
    bytesOfList [0x52, 0xae, 0x67, 0x75] ++ pushScriptNum s.cltvExpiry ++
    bytesOfList [0xb1, 0x75, 0xac, 0x68, 0x51, 0xb2, 0x75, 0x68]

/-- Which HTLC output the second-stage transaction spends. -/
inductive HtlcSide where
  | offered
  | received
deriving Repr, DecidableEq, BEq

/-- The BOLT 3 witness script for the spent HTLC output. -/
def witnessScript : HtlcSide → Bool → HtlcScriptView → ByteArray
  | .offered, false, s => offeredWitnessScript s
  | .offered, true, s => offeredWitnessScriptAnchors s
  | .received, false, s => receivedWitnessScript s
  | .received, true, s => receivedWitnessScriptAnchors s

/-- **The BIP 143 `scriptCode` of the second-stage HTLC spend.**  For a
version-0 P2WSH input the `scriptCode` is the witness script, serialized with
a CompactSize length prefix by `Bip143Preimage`.  The BOLT 3 HTLC scripts
contain no `OP_CODESEPARATOR`, so there is no truncation. -/
def scriptCode (side : HtlcSide) (anchors : Bool) (s : HtlcScriptView) :
    ByteArray :=
  witnessScript side anchors s

theorem scriptCode_eq_witnessScript (side : HtlcSide) (anchors : Bool)
    (s : HtlcScriptView) :
    scriptCode side anchors s = witnessScript side anchors s := rfl

/-! ## 4. Sizes -/

theorem htlcScriptIntro_size (s : HtlcScriptView) (hw : s.WellFormed) :
    (htlcScriptIntro s).size = 66 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hw
  simp [htlcScriptIntro, pushData, h1, h2, h3, h4, h5, h6]

/-- Offered HTLC witness script size: `2 + 21 + 4 + 34 + 5 + 4 + 34 + 4 + 21 +
4 = 133`, the BOLT 3 Appendix A value. -/
theorem offeredWitnessScript_size (s : HtlcScriptView) (hw : s.WellFormed) :
    (offeredWitnessScript s).size = 133 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hw
  simp [offeredWitnessScript, htlcScriptIntro, pushData, h1, h2, h3, h4, h5, h6]

/-- Offered HTLC witness script size with `option_anchors`: `133 + 3 = 136`. -/
theorem offeredWitnessScriptAnchors_size (s : HtlcScriptView)
    (hw : s.WellFormed) : (offeredWitnessScriptAnchors s).size = 136 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hw
  simp [offeredWitnessScriptAnchors, htlcScriptIntro, pushData, h1, h2, h3, h4,
    h5, h6]

/-- Received HTLC witness script size: `135` fixed bytes plus the CLTV push
(one length prefix byte plus the minimal operand). -/
theorem receivedWitnessScript_size (s : HtlcScriptView) (hw : s.WellFormed) :
    (receivedWitnessScript s).size = 135 + (pushScriptNum s.cltvExpiry).size := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hw
  simp [receivedWitnessScript, htlcScriptIntro, pushData, h1, h2, h3, h4, h5,
    h6, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
  omega

/-- Received HTLC witness script size with `option_anchors`. -/
theorem receivedWitnessScriptAnchors_size (s : HtlcScriptView)
    (hw : s.WellFormed) :
    (receivedWitnessScriptAnchors s).size =
      138 + (pushScriptNum s.cltvExpiry).size := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hw
  simp [receivedWitnessScriptAnchors, htlcScriptIntro, pushData, h1, h2, h3, h4,
    h5, h6, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
  omega

/-- A three-byte CLTV operand (`2^15 ≤ cltv < 2^23`) gives the 139-byte
received script: the shape of every realistic current block height. -/
theorem receivedWitnessScript_size_of_three (s : HtlcScriptView)
    (hw : s.WellFormed) (h2 : 0x8000 ≤ s.cltvExpiry)
    (h3 : s.cltvExpiry < 0x800000) :
    (receivedWitnessScript s).size = 139 := by
  rw [receivedWitnessScript_size s hw, pushScriptNum_size,
    scriptNumLen_eq_three s.cltvExpiry h2 h3]

/-- A four-byte CLTV operand (`2^23 ≤ cltv < 2^31`) gives the 140-byte
received script, the size BOLT 3's Appendix A weight table budgets. -/
theorem receivedWitnessScript_size_of_four (s : HtlcScriptView)
    (hw : s.WellFormed) (h3 : 0x800000 ≤ s.cltvExpiry)
    (h4 : s.cltvExpiry < 0x80000000) :
    (receivedWitnessScript s).size = 140 := by
  rw [receivedWitnessScript_size s hw, pushScriptNum_size,
    scriptNumLen_eq_four s.cltvExpiry h3 h4]

/-- The anchor variant of the four-byte received script is 143 bytes, the
BOLT 3 Appendix A anchor value. -/
theorem receivedWitnessScriptAnchors_size_of_four (s : HtlcScriptView)
    (hw : s.WellFormed) (h3 : 0x800000 ≤ s.cltvExpiry)
    (h4 : s.cltvExpiry < 0x80000000) :
    (receivedWitnessScriptAnchors s).size = 143 := by
  rw [receivedWitnessScriptAnchors_size s hw, pushScriptNum_size,
    scriptNumLen_eq_four s.cltvExpiry h3 h4]

/-- `witnessScript` size, by side and anchor variant. -/
theorem witnessScript_size_offered (s : HtlcScriptView) (hw : s.WellFormed) :
    (witnessScript .offered false s).size = 133 :=
  offeredWitnessScript_size s hw

theorem witnessScript_size_offered_anchors (s : HtlcScriptView)
    (hw : s.WellFormed) : (witnessScript .offered true s).size = 136 :=
  offeredWitnessScriptAnchors_size s hw

theorem witnessScript_size_received (s : HtlcScriptView) (hw : s.WellFormed) :
    (witnessScript .received false s).size =
      135 + (pushScriptNum s.cltvExpiry).size :=
  receivedWitnessScript_size s hw

theorem witnessScript_size_received_anchors (s : HtlcScriptView)
    (hw : s.WellFormed) :
    (witnessScript .received true s).size =
      138 + (pushScriptNum s.cltvExpiry).size :=
  receivedWitnessScriptAnchors_size s hw

/-- The offered script does not read the CLTV expiry at all. -/
theorem offeredWitnessScript_ignores_cltv (s : HtlcScriptView) (c : Nat) :
    offeredWitnessScript { s with cltvExpiry := c } = offeredWitnessScript s :=
  rfl

theorem bL_offeredWitnessScript (s : HtlcScriptView) (hw : s.WellFormed) :
    bL (offeredWitnessScript s) =
      [0x76, 0xa9] ++ [0x14] ++ bL s.revocationKeyHash160 ++
        [0x87, 0x63, 0xac, 0x67] ++ [0x21] ++ bL s.remoteHtlcPubKey.bytes ++
        [0x7c, 0x82, 0x01, 0x20, 0x87, 0x64, 0x75, 0x52, 0x7c] ++
        [0x21] ++ bL s.localHtlcPubKey.bytes ++
        [0x52, 0xae, 0x67, 0xa9] ++ [0x14] ++ bL s.paymentHash160 ++
        [0x88, 0xac, 0x68, 0x68] := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hw
  simp [offeredWitnessScript, htlcScriptIntro, pushData, h1, h2, h3, h4, h5, h6]

theorem bL_receivedWitnessScript (s : HtlcScriptView) (hw : s.WellFormed) :
    bL (receivedWitnessScript s) =
      [0x76, 0xa9] ++ [0x14] ++ bL s.revocationKeyHash160 ++
        [0x87, 0x63, 0xac, 0x67] ++ [0x21] ++ bL s.remoteHtlcPubKey.bytes ++
        [0x7c, 0x82, 0x01, 0x20, 0x87, 0x63, 0xa9] ++
        [0x14] ++ bL s.paymentHash160 ++
        [0x88, 0x52, 0x7c, 0x21] ++ bL s.localHtlcPubKey.bytes ++
        [0x52, 0xae, 0x67, 0x75] ++ bL (pushScriptNum s.cltvExpiry) ++
        [0xb1, 0x75, 0xac, 0x68, 0x68] := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hw
  simp [receivedWitnessScript, htlcScriptIntro, pushData, h1, h2, h3, h4, h5, h6]

/-! ## 5. Fixed offsets: the scriptCode determines each explicit field -/

/-- Drop `A.length` and take `B.length` in `A ++ B ++ C`. -/
theorem drop_take_middle (A B C : List UInt8) :
    ((A ++ B ++ C).drop A.length).take B.length = B := by
  rw [List.append_assoc, List.drop_append_length, List.take_append_length]

theorem offeredWitnessScript_paymentHash_slice (s : HtlcScriptView)
    (hw : s.WellFormed) :
    ((bL (offeredWitnessScript s)).drop 109).take 20 = bL s.paymentHash160 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hw
  rw [bL_offeredWitnessScript s ⟨h1, h2, h3, h4, h5, h6⟩]
  let A : List UInt8 :=
    [0x76, 0xa9] ++ [0x14] ++ bL s.revocationKeyHash160 ++
      [0x87, 0x63, 0xac, 0x67] ++ [0x21] ++ bL s.remoteHtlcPubKey.bytes ++
      [0x7c, 0x82, 0x01, 0x20, 0x87, 0x64, 0x75, 0x52, 0x7c] ++
      [0x21] ++ bL s.localHtlcPubKey.bytes ++
      [0x52, 0xae, 0x67, 0xa9] ++ [0x14]
  let C : List UInt8 := [0x88, 0xac, 0x68, 0x68]
  have hP : A.length = 109 := by
    dsimp only [A]
    simp [h1, h2, h3, h4, h5, h6]
  have hB : (bL s.paymentHash160).length = 20 := by simp [h6]
  have key := drop_take_middle A (bL s.paymentHash160) C
  rw [hP] at key
  rw [hB] at key
  simpa [A, C] using key

theorem offeredWitnessScript_revocationHash_slice (s : HtlcScriptView)
    (hw : s.WellFormed) :
    ((bL (offeredWitnessScript s)).drop 3).take 20 = bL s.revocationKeyHash160 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hw
  rw [bL_offeredWitnessScript s ⟨h1, h2, h3, h4, h5, h6⟩]
  let A : List UInt8 := [0x76, 0xa9] ++ [0x14]
  let C : List UInt8 :=
    [0x87, 0x63, 0xac, 0x67] ++ [0x21] ++ bL s.remoteHtlcPubKey.bytes ++
      [0x7c, 0x82, 0x01, 0x20, 0x87, 0x64, 0x75, 0x52, 0x7c] ++
      [0x21] ++ bL s.localHtlcPubKey.bytes ++
      [0x52, 0xae, 0x67, 0xa9] ++ [0x14] ++ bL s.paymentHash160 ++
      [0x88, 0xac, 0x68, 0x68]
  have hP : A.length = 3 := by dsimp only [A]; simp
  have hB : (bL s.revocationKeyHash160).length = 20 := by simp [h2]
  have key := drop_take_middle A (bL s.revocationKeyHash160) C
  rw [hP] at key
  rw [hB] at key
  simpa [A, C] using key

/-- The offered script's local HTLC public key occupies bytes `71..103`. -/
theorem offeredWitnessScript_localKey_slice (s : HtlcScriptView)
    (hw : s.WellFormed) :
    ((bL (offeredWitnessScript s)).drop 71).take 33 =
      bL s.localHtlcPubKey.bytes := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hw
  rw [bL_offeredWitnessScript s ⟨h1, h2, h3, h4, h5, h6⟩]
  let A : List UInt8 :=
    [0x76, 0xa9] ++ [0x14] ++ bL s.revocationKeyHash160 ++
      [0x87, 0x63, 0xac, 0x67] ++ [0x21] ++ bL s.remoteHtlcPubKey.bytes ++
      [0x7c, 0x82, 0x01, 0x20, 0x87, 0x64, 0x75, 0x52, 0x7c] ++ [0x21]
  let C : List UInt8 :=
    [0x52, 0xae, 0x67, 0xa9] ++ [0x14] ++ bL s.paymentHash160 ++
      [0x88, 0xac, 0x68, 0x68]
  have hP : A.length = 71 := by
    dsimp only [A]
    simp [h1, h2, h3, h4, h5, h6]
  have hB : (bL s.localHtlcPubKey.bytes).length = 33 := by simp [h4]
  have key := drop_take_middle A (bL s.localHtlcPubKey.bytes) C
  rw [hP] at key
  rw [hB] at key
  simpa [A, C] using key

theorem receivedWitnessScript_paymentHash_slice (s : HtlcScriptView)
    (hw : s.WellFormed) :
    ((bL (receivedWitnessScript s)).drop 69).take 20 = bL s.paymentHash160 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hw
  rw [bL_receivedWitnessScript s ⟨h1, h2, h3, h4, h5, h6⟩]
  let A : List UInt8 :=
    [0x76, 0xa9] ++ [0x14] ++ bL s.revocationKeyHash160 ++
      [0x87, 0x63, 0xac, 0x67] ++ [0x21] ++ bL s.remoteHtlcPubKey.bytes ++
      [0x7c, 0x82, 0x01, 0x20, 0x87, 0x63, 0xa9] ++ [0x14]
  let C : List UInt8 :=
    [0x88, 0x52, 0x7c, 0x21] ++ bL s.localHtlcPubKey.bytes ++
      [0x52, 0xae, 0x67, 0x75] ++ bL (pushScriptNum s.cltvExpiry) ++
      [0xb1, 0x75, 0xac, 0x68, 0x68]
  have hP : A.length = 69 := by
    dsimp only [A]
    simp [h1, h2, h3, h4, h5, h6]
  have hB : (bL s.paymentHash160).length = 20 := by simp [h6]
  have key := drop_take_middle A (bL s.paymentHash160) C
  rw [hP] at key
  rw [hB] at key
  simpa [A, C] using key

/-- The received script's local HTLC public key occupies bytes `93..125`. -/
theorem receivedWitnessScript_localKey_slice (s : HtlcScriptView)
    (hw : s.WellFormed) :
    ((bL (receivedWitnessScript s)).drop 93).take 33 =
      bL s.localHtlcPubKey.bytes := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hw
  rw [bL_receivedWitnessScript s ⟨h1, h2, h3, h4, h5, h6⟩]
  let A : List UInt8 :=
    [0x76, 0xa9] ++ [0x14] ++ bL s.revocationKeyHash160 ++
      [0x87, 0x63, 0xac, 0x67] ++ [0x21] ++ bL s.remoteHtlcPubKey.bytes ++
      [0x7c, 0x82, 0x01, 0x20, 0x87, 0x63, 0xa9] ++ [0x14] ++
      bL s.paymentHash160 ++ [0x88, 0x52, 0x7c, 0x21]
  let C : List UInt8 :=
    [0x52, 0xae, 0x67, 0x75] ++ bL (pushScriptNum s.cltvExpiry) ++
      [0xb1, 0x75, 0xac, 0x68, 0x68]
  have hP : A.length = 93 := by
    dsimp only [A]
    simp [h1, h2, h3, h4, h5, h6]
  have hB : (bL s.localHtlcPubKey.bytes).length = 33 := by simp [h4]
  have key := drop_take_middle A (bL s.localHtlcPubKey.bytes) C
  rw [hP] at key
  rw [hB] at key
  simpa [A, C] using key

theorem receivedWitnessScript_cltv_slice (s : HtlcScriptView)
    (hw : s.WellFormed) :
    ((bL (receivedWitnessScript s)).drop 130).take
        (bL (pushScriptNum s.cltvExpiry)).length =
      bL (pushScriptNum s.cltvExpiry) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hw
  rw [bL_receivedWitnessScript s ⟨h1, h2, h3, h4, h5, h6⟩]
  let A : List UInt8 :=
    [0x76, 0xa9] ++ [0x14] ++ bL s.revocationKeyHash160 ++
      [0x87, 0x63, 0xac, 0x67] ++ [0x21] ++ bL s.remoteHtlcPubKey.bytes ++
      [0x7c, 0x82, 0x01, 0x20, 0x87, 0x63, 0xa9] ++ [0x14] ++
      bL s.paymentHash160 ++ [0x88, 0x52, 0x7c, 0x21] ++
      bL s.localHtlcPubKey.bytes ++ [0x52, 0xae, 0x67, 0x75]
  let C : List UInt8 := [0xb1, 0x75, 0xac, 0x68, 0x68]
  have hP : A.length = 130 := by
    dsimp only [A]
    simp [h1, h2, h3, h4, h5, h6]
  have key := drop_take_middle A (bL (pushScriptNum s.cltvExpiry)) C
  rw [hP] at key
  simpa [A, C] using key

/-- **The offered scriptCode determines the payment-hash branch.** -/
theorem offeredWitnessScript_paymentHash_inj (s₁ s₂ : HtlcScriptView)
    (h₁ : s₁.WellFormed) (h₂ : s₂.WellFormed)
    (h : offeredWitnessScript s₁ = offeredWitnessScript s₂) :
    s₁.paymentHash160 = s₂.paymentHash160 := by
  have hb : bL (offeredWitnessScript s₁) = bL (offeredWitnessScript s₂) :=
    congrArg bL h
  have hs₁ := offeredWitnessScript_paymentHash_slice s₁ h₁
  have hs₂ := offeredWitnessScript_paymentHash_slice s₂ h₂
  rw [hb] at hs₁
  have : bL s₁.paymentHash160 = bL s₂.paymentHash160 := hs₁.symm.trans hs₂
  exact bL_inj this

/-- **The received scriptCode determines the payment-hash branch.** -/
theorem receivedWitnessScript_paymentHash_inj (s₁ s₂ : HtlcScriptView)
    (h₁ : s₁.WellFormed) (h₂ : s₂.WellFormed)
    (h : receivedWitnessScript s₁ = receivedWitnessScript s₂) :
    s₁.paymentHash160 = s₂.paymentHash160 := by
  have hb : bL (receivedWitnessScript s₁) = bL (receivedWitnessScript s₂) :=
    congrArg bL h
  have hs₁ := receivedWitnessScript_paymentHash_slice s₁ h₁
  have hs₂ := receivedWitnessScript_paymentHash_slice s₂ h₂
  rw [hb] at hs₁
  have : bL s₁.paymentHash160 = bL s₂.paymentHash160 := hs₁.symm.trans hs₂
  exact bL_inj this

/-- **The offered scriptCode determines the revocation-key hash.** -/
theorem offeredWitnessScript_revocationHash_inj (s₁ s₂ : HtlcScriptView)
    (h₁ : s₁.WellFormed) (h₂ : s₂.WellFormed)
    (h : offeredWitnessScript s₁ = offeredWitnessScript s₂) :
    s₁.revocationKeyHash160 = s₂.revocationKeyHash160 := by
  have hb : bL (offeredWitnessScript s₁) = bL (offeredWitnessScript s₂) :=
    congrArg bL h
  have hs₁ := offeredWitnessScript_revocationHash_slice s₁ h₁
  have hs₂ := offeredWitnessScript_revocationHash_slice s₂ h₂
  rw [hb] at hs₁
  have : bL s₁.revocationKeyHash160 = bL s₂.revocationKeyHash160 :=
    hs₁.symm.trans hs₂
  exact bL_inj this

/-- **The received scriptCode determines the CLTV push bytes.** -/
theorem receivedWitnessScript_cltvPush_inj (s₁ s₂ : HtlcScriptView)
    (h₁ : s₁.WellFormed) (h₂ : s₂.WellFormed)
    (h : receivedWitnessScript s₁ = receivedWitnessScript s₂) :
    pushScriptNum s₁.cltvExpiry = pushScriptNum s₂.cltvExpiry := by
  have hb : bL (receivedWitnessScript s₁) = bL (receivedWitnessScript s₂) :=
    congrArg bL h
  have hs₁ := receivedWitnessScript_cltv_slice s₁ h₁
  have hs₂ := receivedWitnessScript_cltv_slice s₂ h₂
  rw [hb] at hs₁
  have hlen : (bL (pushScriptNum s₁.cltvExpiry)).length =
      (bL (pushScriptNum s₂.cltvExpiry)).length := by
    have hs : (receivedWitnessScript s₁).size = (receivedWitnessScript s₂).size := by
      rw [h]
    rw [receivedWitnessScript_size s₁ h₁, receivedWitnessScript_size s₂ h₂] at hs
    have hsz : (pushScriptNum s₁.cltvExpiry).size =
        (pushScriptNum s₂.cltvExpiry).size := by omega
    simpa [bL_length] using hsz
  have hlist : bL (pushScriptNum s₁.cltvExpiry) =
      bL (pushScriptNum s₂.cltvExpiry) := by
    rw [← hs₁, ← hs₂, hlen]
  exact bL_inj hlist

/-- **The received scriptCode determines the CLTV expiry** on the CLTV
domain. -/
theorem receivedWitnessScript_cltv_inj (s₁ s₂ : HtlcScriptView)
    (h₁ : s₁.WellFormed) (h₂ : s₂.WellFormed)
    (hc₁ : s₁.cltvExpiry < 0x80000000) (hc₂ : s₂.cltvExpiry < 0x80000000)
    (h : receivedWitnessScript s₁ = receivedWitnessScript s₂) :
    s₁.cltvExpiry = s₂.cltvExpiry :=
  pushScriptNum_inj hc₁ hc₂ (receivedWitnessScript_cltvPush_inj s₁ s₂ h₁ h₂ h)

/-! ## 6. The P2WSH output committed to by the scriptCode -/

/-- The version-0 P2WSH output script whose witness script is the synthesized
HTLC script.  `sha256` is a parameter: C1 is an assumption. -/
def htlcScriptPubKey (sha256 : ByteArray → ByteArray) (side : HtlcSide)
    (anchors : Bool) (s : HtlcScriptView) : Bitcoin.Data.Script :=
  p2wsh (sha256 (scriptCode side anchors s))

/-- The P2WSH output is 34 bytes whenever the supplied hash is 32 bytes. -/
theorem htlcScriptPubKey_size (sha256 : ByteArray → ByteArray)
    (side : HtlcSide) (anchors : Bool) (s : HtlcScriptView)
    (h : (sha256 (scriptCode side anchors s)).size = 32) :
    (htlcScriptPubKey sha256 side anchors s).bytes.size = 34 :=
  p2wsh_size _ h

/-- The wire transaction spends an output committed to exactly the synthesized
scriptCode.  This is the bridge between `HtlcWire.scriptPubKey` (the spent
output) and the `scriptCode` this lane puts into the preimage. -/
def SpendsScriptCode (sha256 : ByteArray → ByteArray) (w : HtlcWire)
    (side : HtlcSide) (anchors : Bool) (s : HtlcScriptView) : Prop :=
  w.scriptPubKey = (htlcScriptPubKey sha256 side anchors s).bytes

theorem spendsScriptCode_bytes (sha256 : ByteArray → ByteArray) (w : HtlcWire)
    (side : HtlcSide) (anchors : Bool) (s : HtlcScriptView)
    (h : SpendsScriptCode sha256 w side anchors s) :
    w.scriptPubKey =
      (ByteArray.empty.push OP_0).push 0x20 ++
        sha256 (scriptCode side anchors s) := by
  rw [SpendsScriptCode] at h
  rw [h]
  rfl

/-! ## 7. The HTLC BIP 143 preimage (lane H07 bridge) -/

/-- **The HTLC BIP 143 preimage.**  `HtlcWire` is the exact one-input,
one-output second-stage transaction, so the signing input is always index `0`
and the spent amount is the wire's output value.  This is lane H07's
`htlcBip143Preimage` at `amountSat = w.valueSat`; the two are definitionally
equal (`htlcBip143Preimage_eq_H07`). -/
def htlcBip143Preimage (w : HtlcWire) (scriptCodeBytes : ByteArray)
    (sighashType : UInt32) : Bip143Preimage :=
  Bip143Preimage.ofTx w.toTx 0 scriptCodeBytes sighashType w.valueSat

/-- The definition unfolds to the `ofTx` form. -/
theorem htlcBip143Preimage_eq_ofTx (w : HtlcWire) (scriptCodeBytes : ByteArray)
    (sighashType : UInt32) :
    htlcBip143Preimage w scriptCodeBytes sighashType =
      Bip143Preimage.ofTx w.toTx 0 scriptCodeBytes sighashType w.valueSat := rfl

/-- **Exact bridge to lane H07.**  H07 exposes the four-argument
`H07.htlcBip143Preimage h sc ht amountSat`; instantiating `amountSat` with the
wire's output value gives this lane's preimage by definitional equality. -/
theorem htlcBip143Preimage_eq_H07 (w : HtlcWire) (scriptCodeBytes : ByteArray)
    (sighashType : UInt32) :
    htlcBip143Preimage w scriptCodeBytes sighashType =
      LnLean.Proofs.WaveH.H07.htlcBip143Preimage w scriptCodeBytes sighashType
        w.valueSat := rfl

/-- The wire fields of the preimage are exactly the wire transaction's. -/
theorem htlcBip143Preimage_wire_fields (w : HtlcWire)
    (scriptCodeBytes : ByteArray) (sighashType : UInt32) :
    (htlcBip143Preimage w scriptCodeBytes sighashType).version = w.version ∧
    (htlcBip143Preimage w scriptCodeBytes sighashType).outpointTxid =
      w.commitmentTxid ∧
    (htlcBip143Preimage w scriptCodeBytes sighashType).outpointIndex =
      w.commitmentOutputIndex ∧
    (htlcBip143Preimage w scriptCodeBytes sighashType).sequence = w.sequence ∧
    (htlcBip143Preimage w scriptCodeBytes sighashType).locktime = w.locktime := by
  simp [htlcBip143Preimage, Bip143Preimage.ofTx, HtlcWire.toTx,
    LnLean.Bitcoin.Sighash.dummyTxIn]

/-- The preimage's scriptCode field is exactly the supplied script code. -/
theorem htlcBip143Preimage_scriptCode (w : HtlcWire)
    (scriptCodeBytes : ByteArray) (sighashType : UInt32) :
    (htlcBip143Preimage w scriptCodeBytes sighashType).scriptCode =
      scriptCodeBytes := rfl

/-- The preimage commits to the wire output value (the spent HTLC amount). -/
theorem htlcBip143Preimage_amountSat (w : HtlcWire)
    (scriptCodeBytes : ByteArray) (sighashType : UInt32) :
    (htlcBip143Preimage w scriptCodeBytes sighashType).amountSat = w.valueSat := rfl

/-- **Byte equality with the vendored BIP 143 encoder** for the HTLC wire. -/
theorem htlcBip143Preimage_eq_bip143MsgL (w : HtlcWire)
    (scriptCodeBytes : ByteArray) (sighashType : UInt32) :
    bL (htlcBip143Preimage w scriptCodeBytes sighashType).preimageBytes =
      Bitcoin.SigHash.bip143MsgL w.toTx 0 (bL scriptCodeBytes) sighashType
        (w.valueSat.toNat : Int) := by
  simpa [htlcBip143Preimage] using
    Bip143Preimage.preimageBytes_eq_bip143MsgL_ofTx w.toTx 0 scriptCodeBytes
      sighashType w.valueSat

/-- **The preimage instantiated with the synthesized scriptCode.** -/
def htlcWirePreimage (w : HtlcWire) (side : HtlcSide) (anchors : Bool)
    (s : HtlcScriptView) (sighashType : UInt32) : Bip143Preimage :=
  htlcBip143Preimage w (scriptCode side anchors s) sighashType

/-- **The instantiated preimage is H07's preimage at the synthesized
scriptCode and the wire amount.** -/
theorem htlcWirePreimage_eq_H07 (w : HtlcWire) (side : HtlcSide)
    (anchors : Bool) (s : HtlcScriptView) (sighashType : UInt32) :
    htlcWirePreimage w side anchors s sighashType =
      LnLean.Proofs.WaveH.H07.htlcBip143Preimage w
        (scriptCode side anchors s) sighashType w.valueSat := rfl

theorem htlcWirePreimage_scriptCode (w : HtlcWire) (side : HtlcSide)
    (anchors : Bool) (s : HtlcScriptView) (sighashType : UInt32) :
    (htlcWirePreimage w side anchors s sighashType).scriptCode =
      witnessScript side anchors s := rfl

theorem htlcWirePreimage_eq_bip143MsgL (w : HtlcWire) (side : HtlcSide)
    (anchors : Bool) (s : HtlcScriptView) (sighashType : UInt32) :
    bL (htlcWirePreimage w side anchors s sighashType).preimageBytes =
      Bitcoin.SigHash.bip143MsgL w.toTx 0 (bL (witnessScript side anchors s))
        sighashType (w.valueSat.toNat : Int) :=
  htlcBip143Preimage_eq_bip143MsgL w _ sighashType

/-! ## 8. Preimage size and digest -/

theorem htlcWire_toTx_vin_length (w : HtlcWire) : w.toTx.vin.length = 1 := rfl

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

theorem htlcWirePreimage_preimageBytes_size (w : HtlcWire) (side : HtlcSide)
    (anchors : Bool) (s : HtlcScriptView) (sighashType : UInt32)
    (hw : w.WellFormed) :
    (htlcWirePreimage w side anchors s sighashType).preimageBytes.size =
      156 + compactSizeWidth (witnessScript side anchors s).size +
        (witnessScript side anchors s).size := by
  obtain ⟨htxid, hspk, hval⟩ := hw
  let p := Bip143Preimage.ofTx w.toTx 0 (witnessScript side anchors s)
    sighashType w.valueSat
  have hp : p.hashPrevouts.size = 32 := by
    dsimp only [p, Bip143Preimage.ofTx]
    exact hashPrevoutsOf_size w.toTx sighashType
  have hq : p.hashSequence.size = 32 := by
    dsimp only [p, Bip143Preimage.ofTx]
    exact hashSequenceOf_size w.toTx sighashType
  have ho : p.outpointTxid.size = 32 := by
    dsimp only [p, Bip143Preimage.ofTx]
    simp [HtlcWire.toTx, htxid]
  have hh : p.hashOutputs.size = 32 := by
    dsimp only [p, Bip143Preimage.ofTx]
    exact hashOutputsOf_size w.toTx 0 sighashType
  have hmain := Bip143Preimage.preimageBytes_size p hp hq ho hh
  simpa [p, htlcWirePreimage, htlcBip143Preimage, scriptCode, Bip143Preimage.ofTx] using hmain

/-- Offered second-stage preimage with `SIGHASH_ALL`: 290 bytes. -/
theorem htlcWirePreimage_size_offered (w : HtlcWire) (s : HtlcScriptView)
    (sighashType : UInt32) (hw : w.WellFormed) (hs : s.WellFormed) :
    (htlcWirePreimage w .offered false s sighashType).preimageBytes.size = 290 := by
  rw [htlcWirePreimage_preimageBytes_size w .offered false s sighashType hw,
    witnessScript_size_offered s hs]
  simp [compactSizeWidth]

/-- Offered second-stage preimage with anchors: 293 bytes. -/
theorem htlcWirePreimage_size_offered_anchors (w : HtlcWire)
    (s : HtlcScriptView) (sighashType : UInt32) (hw : w.WellFormed)
    (hs : s.WellFormed) :
    (htlcWirePreimage w .offered true s sighashType).preimageBytes.size = 293 := by
  rw [htlcWirePreimage_preimageBytes_size w .offered true s sighashType hw,
    witnessScript_size_offered_anchors s hs]
  simp [compactSizeWidth]

/-- Received second-stage preimage with a three-byte CLTV operand: 296
bytes. -/
theorem htlcWirePreimage_size_received_three (w : HtlcWire)
    (s : HtlcScriptView) (sighashType : UInt32) (hw : w.WellFormed)
    (hs : s.WellFormed) (h2 : 0x8000 ≤ s.cltvExpiry)
    (h3 : s.cltvExpiry < 0x800000) :
    (htlcWirePreimage w .received false s sighashType).preimageBytes.size = 296 := by
  rw [htlcWirePreimage_preimageBytes_size w .received false s sighashType hw]
  change 156 + compactSizeWidth (receivedWitnessScript s).size + (receivedWitnessScript s).size = 296
  rw [receivedWitnessScript_size_of_three s hs h2 h3]
  simp [compactSizeWidth]

/-- Received second-stage preimage with a four-byte CLTV operand (the BOLT 3
weight-table case): 297 bytes. -/
theorem htlcWirePreimage_size_received_four (w : HtlcWire)
    (s : HtlcScriptView) (sighashType : UInt32) (hw : w.WellFormed)
    (hs : s.WellFormed) (h3 : 0x800000 ≤ s.cltvExpiry)
    (h4 : s.cltvExpiry < 0x80000000) :
    (htlcWirePreimage w .received false s sighashType).preimageBytes.size = 297 := by
  rw [htlcWirePreimage_preimageBytes_size w .received false s sighashType hw]
  change 156 + compactSizeWidth (receivedWitnessScript s).size + (receivedWitnessScript s).size = 297
  rw [receivedWitnessScript_size_of_four s hs h3 h4]
  simp [compactSizeWidth]

/-- Received second-stage preimage with anchors and a four-byte CLTV operand:
300 bytes. -/
theorem htlcWirePreimage_size_received_anchors_four (w : HtlcWire)
    (s : HtlcScriptView) (sighashType : UInt32) (hw : w.WellFormed)
    (hs : s.WellFormed) (h3 : 0x800000 ≤ s.cltvExpiry)
    (h4 : s.cltvExpiry < 0x80000000) :
    (htlcWirePreimage w .received true s sighashType).preimageBytes.size = 300 := by
  rw [htlcWirePreimage_preimageBytes_size w .received true s sighashType hw]
  change 156 + compactSizeWidth (receivedWitnessScriptAnchors s).size + (receivedWitnessScriptAnchors s).size = 300
  rw [receivedWitnessScriptAnchors_size_of_four s hs h3 h4]
  simp [compactSizeWidth]

/-- **Digest against the vendored implementation.**  `HtlcWire.toTx` has one
input, so index `0` is always in range and the vendored
`signatureHashBip143Impl` is the model digest of the instantiated preimage.
The standalone vector/out-of-range lane is H09. -/
theorem htlcWirePreimage_digest_eq_vendorImpl (w : HtlcWire) (side : HtlcSide)
    (anchors : Bool) (s : HtlcScriptView) (sighashType : UInt32) :
    LnLean.Bitcoin.Sighash.digest
        (htlcWirePreimage w side anchors s sighashType).toPreimage =
      Bitcoin.SigHash.signatureHashBip143Impl w.toTx 0
        (bL (witnessScript side anchors s)) sighashType
        (w.valueSat.toNat : Int) := by
  have hlt : 0 < w.toTx.vin.length := by
    rw [htlcWire_toTx_vin_length w]
    decide
  change LnLean.Bitcoin.Sighash.digest
      (Bip143Preimage.ofTx w.toTx 0 (scriptCode side anchors s) sighashType
        w.valueSat).toPreimage =
    Bitcoin.SigHash.signatureHashBip143Impl w.toTx 0
      (bL (scriptCode side anchors s)) sighashType (w.valueSat.toNat : Int)
  exact Bip143Preimage.digest_eq_sighashWitnessV0_ofTx w.toTx 0
    (scriptCode side anchors s) sighashType w.valueSat hlt

theorem htlcWirePreimage_digest_size (w : HtlcWire) (side : HtlcSide)
    (anchors : Bool) (s : HtlcScriptView) (sighashType : UInt32) :
    (LnLean.Bitcoin.Sighash.digest
      (htlcWirePreimage w side anchors s sighashType).toPreimage).size = 32 := by
  unfold LnLean.Bitcoin.Sighash.digest LnLean.Bitcoin.Sighash.dsha
  exact Bitcoin.Crypto.Seam.sha256d_size _

/-! ## 9. Concrete vectors -/

/-- `n` repetitions of a byte. -/
def rep (n : Nat) (b : UInt8) : ByteArray := bytesOfList (List.replicate n b)

/-- A concrete HTLC script view with a three-byte CLTV operand
(`cltv_expiry = 500000 < 2^23`). -/
def vectorScript : HtlcScriptView :=
  { revocationPubKey := ⟨rep 33 0x02⟩
    revocationKeyHash160 := rep 20 0x11
    remoteHtlcPubKey := ⟨rep 33 0x03⟩
    localHtlcPubKey := ⟨rep 33 0x04⟩
    paymentHash := ⟨rep 32 0x05⟩
    paymentHash160 := rep 20 0x44
    cltvExpiry := 500000 }

/-- The same script view with a four-byte CLTV operand
(`cltv_expiry = 9000000 ≥ 2^23`). -/
def vectorScriptFour : HtlcScriptView :=
  { vectorScript with cltvExpiry := 9000000 }

theorem vectorScript_wellFormed : vectorScript.WellFormed := by
  simp [HtlcScriptView.WellFormed, vectorScript, rep]

theorem vectorScriptFour_wellFormed : vectorScriptFour.WellFormed := by
  simp [HtlcScriptView.WellFormed, vectorScriptFour, vectorScript, rep]

theorem vectorScript_cltv_three : 0x8000 ≤ vectorScript.cltvExpiry ∧
    vectorScript.cltvExpiry < 0x800000 := by
  decide

theorem vectorScriptFour_cltv_four : 0x800000 ≤ vectorScriptFour.cltvExpiry ∧
    vectorScriptFour.cltvExpiry < 0x80000000 := by
  decide

theorem vectorScript_push_bytes :
    bL (pushScriptNum vectorScript.cltvExpiry) =
      [0x03, 0x20, 0xa1, 0x07] := by
  decide

theorem vectorScriptFour_push_bytes :
    bL (pushScriptNum vectorScriptFour.cltvExpiry) =
      [0x04, 0x40, 0x54, 0x89, 0x00] := by
  decide

theorem vectorOffered_script_size :
    (offeredWitnessScript vectorScript).size = 133 :=
  offeredWitnessScript_size _ vectorScript_wellFormed

theorem vectorReceived_script_size :
    (receivedWitnessScript vectorScript).size = 139 :=
  receivedWitnessScript_size_of_three _ vectorScript_wellFormed
    vectorScript_cltv_three.1 vectorScript_cltv_three.2

theorem vectorReceivedFour_script_size :
    (receivedWitnessScript vectorScriptFour).size = 140 :=
  receivedWitnessScript_size_of_four _ vectorScriptFour_wellFormed
    vectorScriptFour_cltv_four.1 vectorScriptFour_cltv_four.2

set_option maxRecDepth 10000 in
/-- The offered witness script as an exact byte string. -/
theorem vectorOffered_script_bytes :
    bL (offeredWitnessScript vectorScript) =
      [0x76, 0xa9, 0x14] ++ List.replicate 20 0x11 ++
      [0x87, 0x63, 0xac, 0x67, 0x21] ++ List.replicate 33 0x03 ++
      [0x7c, 0x82, 0x01, 0x20, 0x87, 0x64, 0x75, 0x52, 0x7c, 0x21] ++
      List.replicate 33 0x04 ++
      [0x52, 0xae, 0x67, 0xa9, 0x14] ++ List.replicate 20 0x44 ++
      [0x88, 0xac, 0x68, 0x68] := by
  rw [bL_offeredWitnessScript vectorScript vectorScript_wellFormed]
  simp [vectorScript, rep]

set_option maxRecDepth 10000 in
/-- The received witness script (three-byte CLTV operand) as an exact byte
string.  `0x04` is the one-byte CompactSize/`pushData` length of the
three-byte little-endian `500000 = 0x07A120`. -/
theorem vectorReceived_script_bytes :
    bL (receivedWitnessScript vectorScript) =
      [0x76, 0xa9, 0x14] ++ List.replicate 20 0x11 ++
      [0x87, 0x63, 0xac, 0x67, 0x21] ++ List.replicate 33 0x03 ++
      [0x7c, 0x82, 0x01, 0x20, 0x87, 0x63, 0xa9, 0x14] ++
      List.replicate 20 0x44 ++
      [0x88, 0x52, 0x7c, 0x21] ++ List.replicate 33 0x04 ++
      [0x52, 0xae, 0x67, 0x75, 0x03, 0x20, 0xa1, 0x07, 0xb1, 0x75, 0xac] ++
      [0x68, 0x68] := by
  rw [bL_receivedWitnessScript vectorScript vectorScript_wellFormed,
    vectorScript_push_bytes]
  simp [vectorScript, rep]

set_option maxRecDepth 10000 in
/-- The fixed-offset slices of the offered script: revocation-key hash at byte
`3`, remote HTLC key at `28`, local HTLC key at `72`, payment-hash branch at
`109`. -/
theorem vectorOffered_slices :
    ((bL (offeredWitnessScript vectorScript)).drop 3).take 20 =
        List.replicate 20 0x11 ∧
      ((bL (offeredWitnessScript vectorScript)).drop 28).take 33 =
        List.replicate 33 0x03 ∧
      ((bL (offeredWitnessScript vectorScript)).drop 71).take 33 =
        List.replicate 33 0x04 ∧
      ((bL (offeredWitnessScript vectorScript)).drop 109).take 20 =
        List.replicate 20 0x44 := by
  rw [vectorOffered_script_bytes]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

set_option maxRecDepth 10000 in
/-- The fixed-offset slices of the received script: payment-hash branch at
`69` and the CLTV operand at `131`. -/
theorem vectorReceived_slices :
    ((bL (receivedWitnessScript vectorScript)).drop 69).take 20 =
        List.replicate 20 0x44 ∧
      ((bL (receivedWitnessScript vectorScript)).drop 131).take 3 =
        [0x20, 0xa1, 0x07] := by
  rw [vectorReceived_script_bytes]
  refine ⟨?_, ?_⟩ <;> decide

/-- A concrete one-input HTLC wire (the HTLC-success shape: sequence `1`,
locktime `0`). -/
def vectorHtlcWire : HtlcWire :=
  { version := 2
    commitmentTxid := rep 32 0x66
    commitmentOutputIndex := 0
    sequence := 1
    valueSat := 100000
    scriptPubKey := (ByteArray.empty.push OP_0).push 0x20 ++ rep 32 0x77
    locktime := 0 }

theorem vectorHtlcWire_wellFormed : vectorHtlcWire.WellFormed := by
  simp [HtlcWire.WellFormed, vectorHtlcWire, rep, Bitcoin.Serialization.MAX_SIZE]

theorem vectorOfferedPreimage_size :
    (htlcWirePreimage vectorHtlcWire .offered false vectorScript 1).preimageBytes.size
      = 290 :=
  htlcWirePreimage_size_offered _ _ 1 vectorHtlcWire_wellFormed
    vectorScript_wellFormed

theorem vectorReceivedPreimage_size :
    (htlcWirePreimage vectorHtlcWire .received false vectorScript 1).preimageBytes.size
      = 296 :=
  htlcWirePreimage_size_received_three _ _ 1 vectorHtlcWire_wellFormed
    vectorScript_wellFormed vectorScript_cltv_three.1 vectorScript_cltv_three.2

theorem vectorReceivedFourPreimage_size :
    (htlcWirePreimage vectorHtlcWire .received false vectorScriptFour 1).preimageBytes.size
      = 297 :=
  htlcWirePreimage_size_received_four _ _ 1 vectorHtlcWire_wellFormed
    vectorScriptFour_wellFormed vectorScriptFour_cltv_four.1
    vectorScriptFour_cltv_four.2

/-- The offered second-stage preimage is byte-equal to the vendored encoder on
the concrete wire. -/
theorem vectorOfferedPreimage_eq_vendor :
    bL (htlcWirePreimage vectorHtlcWire .offered false vectorScript 1).preimageBytes =
      Bitcoin.SigHash.bip143MsgL vectorHtlcWire.toTx 0
        (bL (offeredWitnessScript vectorScript)) 1
        (vectorHtlcWire.valueSat.toNat : Int) :=
  htlcWirePreimage_eq_bip143MsgL _ _ _ _ 1

/-! ## 10. Summary -/

/-- Bundled faithful reading of the lane.

1. Both BOLT 3 HTLC witness scripts are byte-exact templates with the BOLT 3
   sizes (133 offered, 140 received with a four-byte CLTV operand, +3 with
   anchors) and the received size is `135 + pushSize` in general.
2. The four explicit fields (revocation-key hash, payment-hash branch, local
   HTLC key, CLTV push) occur at fixed offsets; scriptCode equality fixes the
   payment-hash branch and, on the CLTV domain, the expiry.
3. The HTLC BIP 143 preimage instantiates the H07 preimage with the
   synthesized scriptCode; its bytes equal the vendored `bip143MsgL` and its
   digest equals the vendored `signatureHashBip143Impl` at index `0`.
4. Preimage sizes are 290 (offered), 296/297 (received, three/four-byte CLTV
   operand), 293/299/300 in the anchor variants. -/
theorem htlc_scriptCode_summary :
    (∀ (s : HtlcScriptView), s.WellFormed → (offeredWitnessScript s).size = 133) ∧
      (∀ (s : HtlcScriptView), s.WellFormed →
        (offeredWitnessScriptAnchors s).size = 136) ∧
      (∀ (s : HtlcScriptView), s.WellFormed →
        (receivedWitnessScript s).size = 135 + (pushScriptNum s.cltvExpiry).size) ∧
      (∀ (s : HtlcScriptView), s.WellFormed → 0x8000 ≤ s.cltvExpiry →
        s.cltvExpiry < 0x800000 → (receivedWitnessScript s).size = 139) ∧
      (∀ (s : HtlcScriptView), s.WellFormed → 0x800000 ≤ s.cltvExpiry →
        s.cltvExpiry < 0x80000000 → (receivedWitnessScript s).size = 140) ∧
      (∀ (s₁ s₂ : HtlcScriptView), s₁.WellFormed → s₂.WellFormed →
        offeredWitnessScript s₁ = offeredWitnessScript s₂ →
        s₁.paymentHash160 = s₂.paymentHash160) ∧
      (∀ (s₁ s₂ : HtlcScriptView), s₁.WellFormed → s₂.WellFormed →
        s₁.cltvExpiry < 0x80000000 → s₂.cltvExpiry < 0x80000000 →
        receivedWitnessScript s₁ = receivedWitnessScript s₂ →
        s₁.cltvExpiry = s₂.cltvExpiry) ∧
      (∀ (w : HtlcWire) (s : HtlcScriptView) (ht : UInt32),
        bL (htlcWirePreimage w .offered false s ht).preimageBytes =
          Bitcoin.SigHash.bip143MsgL w.toTx 0 (bL (offeredWitnessScript s)) ht
            (w.valueSat.toNat : Int)) ∧
      (∀ (w : HtlcWire) (side : HtlcSide) (anchors : Bool)
        (s : HtlcScriptView) (ht : UInt32),
        LnLean.Bitcoin.Sighash.digest
            (htlcWirePreimage w side anchors s ht).toPreimage =
          Bitcoin.SigHash.signatureHashBip143Impl w.toTx 0
            (bL (witnessScript side anchors s)) ht (w.valueSat.toNat : Int)) ∧
      (∀ (w : HtlcWire) (s : HtlcScriptView) (ht : UInt32),
        w.WellFormed → s.WellFormed →
        (htlcWirePreimage w .offered false s ht).preimageBytes.size = 290) ∧
      (∀ (w : HtlcWire) (s : HtlcScriptView) (ht : UInt32),
        w.WellFormed → s.WellFormed → 0x800000 ≤ s.cltvExpiry →
        s.cltvExpiry < 0x80000000 →
        (htlcWirePreimage w .received false s ht).preimageBytes.size = 297) :=
  ⟨offeredWitnessScript_size, offeredWitnessScriptAnchors_size,
    receivedWitnessScript_size, receivedWitnessScript_size_of_three,
    receivedWitnessScript_size_of_four, offeredWitnessScript_paymentHash_inj,
    receivedWitnessScript_cltv_inj,
    fun w s ht => htlcWirePreimage_eq_bip143MsgL w .offered false s ht,
    fun w side anchors s ht =>
      htlcWirePreimage_digest_eq_vendorImpl w side anchors s ht,
    htlcWirePreimage_size_offered, htlcWirePreimage_size_received_four⟩

end LnLean.Proofs.WaveH.H08
