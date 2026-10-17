/-
# BIP 340 Schnorr / BIP 341 taproot verification seam

**English claim.**  This module states the BOLT-level laws of the Schnorr and
taproot seam that the Lightning channel model relies on:

1. a BIP 340 signature is a 64-byte object (`SchnorrSig.Valid` is exactly
   `bytes.size = 64`) and a BIP 340 public key is a 32-byte x-only object,
   which the model embeds into its 33-byte compressed `PubKey` carrier;
2. Schnorr verification is a deterministic function of `(key, message,
   signature)`: it consumes no auxiliary randomness (BIP 340 `aux_rand` is a
   *signing* input only), so repeating a verification cannot change its
   result;
3. message binding and unforgeability are *conditional*: they are derived
   only from the `schnorr_eufCma` field of `PrimitiveModel`, surfaced as
   `AssumesEufCma`.  A concrete two-message forgery refutes that field, and
   the always-accepting verifier satisfies every format law while failing
   EUF-CMA, so no unconditional unforgeability claim is made;
4. the BIP 341 taproot output commitment is a function of the internal key
   and the optional 32-byte script-tree root through the `TapTweak` tagged
   hash; equal commitments determine equal internal keys and equal roots
   (injectivity is conditional on the model's `PreimageResistant` hash field);
5. key-path and script-path spends are separated by distinct sighash
   domains.  **Correction to the brief:** BIP 341 uses one tag,
   `"TapSighash"`, for both; the separation is the `ext_flag` byte
   (`0x00` key path, `0x01` script path, followed by the tapleaf hash for
   script path), not two literal tagged hashes.  The model below uses a
   single tag and the `0x00`/`0x01` domain prefixes; distinctness of the
   resulting digests is proved, not assumed.

**BOLT sections.**  `refs/bolts/bolt-simple-taproot.md` (Extension BOLT XX,
Simple Taproot Channels): §Pay-To-Taproot-Outputs (`OP_1 <taproot_output_key>`,
32-byte x-only key, `TapTweak` derivation, `tagged_hash` definition),
§Taproot Key Path Spends (64-byte signature under `SIGHASH_DEFAULT`),
§Taproot Script Path Spends (control block carries the internal key and the
inclusion proof), and §Simple Taproot Channel Commitment Outputs
(`to_local_output_key`, `to_remote_output_key`).  BOLT 1 §Fundamental Types
declares the 64-byte `bip340sig`.  Note that at the pinned BOLT commit BOLT 3
(`03-transactions.md`) contains **no** taproot section; the taproot channel
text lives in the draft `bolt-simple-taproot.md`, so the brief's "BOLT 3
taproot" is cited there.  BOLT 3 is the pre-taproot commitment framework and
is not used for any taproot statement here.

**rust-lightning anchors (commit fe49009).**
* `lightning/src/util/ser.rs:684` — `impl_array!(64, u8)` for
  `schnorr::Signature`.
* `lightning/src/util/ser.rs:1272-1282` — `Writeable`/`Readable` for
  `schnorr::Signature` over a 64-byte array (`SCHNORR_SIGNATURE_SIZE`).
* `lightning/src/ln/interactivetxs.rs:810-836` — P2TR key-path spend: a
  32-byte x-only key is read from the previous `scriptPubKey`, the taproot
  sighash is computed, and `verify_schnorr` is called.
* `lightning/src/util/anchor_channel_reserves.rs:79-94` — a P2TR key-path
  input carries a 64-byte Schnorr signature and a P2TR output is
  `OP_1 OP_PUSH32 <32-byte key>` (34-byte script).
* `lightning/src/offers/merkle.rs:27` and `:223-240` — tagged-hash
  construction `SHA256(SHA256(tag) || SHA256(tag) || msg)` used for Schnorr
  signature calculation and verification.
* `lightning/src/sign/mod.rs:979-992` — signing interface over a `TaggedHash`
  digest with a `schnorr::Signature` result.
* The tap-tweak *computation* is delegated by LDK to `rust-bitcoin`
  (`TweakedPublicKey`, e.g. `lightning/src/offers/invoice.rs:2563`); it is not
  present in the pinned tree.  The tweak law is therefore anchored to BOLT
  (`bolt-simple-taproot.md:126-140`) and to the call sites that consume an
  already-tweaked key.

**Not modelled.**
* SHA-256 compression and concrete digest values; secp256k1 group arithmetic,
  point addition `P + t*G`, x-only encoding, and the output-key y-parity
  (`bolt-simple-taproot.md:132-134`).
* The BIP 341 `SigMsg`/`TapSighash` preimage in full (prevouts, amounts,
  scriptPubKeys, annex, `spend_type`, `key_version`, `codesep_pos`, input
  index).  Only the `ext_flag` domain separation and a tapleaf commitment
  are modelled, as opaque byte strings.
* Tapscript tree construction, branch hashing, control-block parsing and
  inclusion-proof checking.
* 65-byte `SIGHASH_ALL` key-path signatures: the model fixes the wire format
  at 64 bytes (`SIGHASH_DEFAULT`), so a 65-byte signature is provably
  invalid here.
* MuSig2 aggregation, key generation, signing, side channels, adaptor
  signatures, and any computational reduction.  `schnorr_eufCma` remains a
  `Prop` field; this file never proves it.
* The model's `taprootOutputKey` is a 32-byte *hash commitment* to
  `(internal key, root)`, standing in for the x-only encoding of the curve
  point.  It is not the curve point and no group law is claimed for it.
-/

import LnLean.Crypto.Sig
import LnLean.Crypto.Model
import LnLean.Basic.Core

namespace LnLean.Proofs.Crypto

set_option autoImplicit false

open LnLean
open LnLean.Crypto

/-! ## 1. Wire formats: 64-byte signature, 32-byte x-only key -/

/-- A BIP 340 x-only public key.  BIP 340 and
`bolt-simple-taproot.md:122-124` define it as a 32-byte encoding.  The
ambient model's `PubKey` is a 33-byte compressed key, so this type is the
proof-layer bridge; a later wave should move it next to `PubKey`. -/
structure XOnlyPubKey where
  bytes : ByteArray
deriving Repr, BEq

/-- An x-only key is valid exactly when it is 32 bytes. -/
def XOnlyPubKey.Valid (k : XOnlyPubKey) : Prop := k.bytes.size = 32

/-- Embed a 32-byte x-only key into the model's compressed-key carrier by
prefixing the even-y tag `0x02`.  This is the only way to feed a BIP 340 key
to `PrimitiveModel.schnorrVerify`, whose signature is fixed at `PubKey`. -/
def XOnlyPubKey.toPubKey (k : XOnlyPubKey) : PubKey :=
  ⟨(ByteArray.empty.push (0x02 : UInt8)) ++ k.bytes⟩

theorem xOnlyKey_valid_iff (k : XOnlyPubKey) : k.Valid ↔ k.bytes.size = 32 :=
  Iff.rfl

/-- A 32-byte x-only key embeds as a valid 33-byte compressed key. -/
theorem toPubKey_valid (k : XOnlyPubKey) (h : k.Valid) : (k.toPubKey).Valid := by
  unfold XOnlyPubKey.toPubKey PubKey.Valid
  rw [ByteArray.size_append]
  have h1 : (ByteArray.empty.push (0x02 : UInt8)).size = 1 := rfl
  rw [h1]
  unfold XOnlyPubKey.Valid at h
  omega

/-- The embedding is injective: the `0x02` prefix can be cancelled. -/
theorem toPubKey_injective {k₁ k₂ : XOnlyPubKey}
    (h : k₁.toPubKey = k₂.toPubKey) : k₁ = k₂ := by
  have hb : (ByteArray.empty.push (0x02 : UInt8)) ++ k₁.bytes =
      (ByteArray.empty.push (0x02 : UInt8)) ++ k₂.bytes :=
    congrArg PubKey.bytes h
  have hbytes : k₁.bytes = k₂.bytes := append_left_cancel hb
  rcases k₁ with ⟨b₁⟩
  rcases k₂ with ⟨b₂⟩
  simpa using hbytes

/-- The all-zero 32-byte string is a well-formed x-only key carrier. -/
def exampleXOnlyKey : XOnlyPubKey :=
  ⟨ByteArray.mk (List.replicate 32 (0 : UInt8)).toArray⟩

theorem exampleXOnlyKey_valid : exampleXOnlyKey.Valid := rfl

/-- The all-zero 64-byte string is a well-formed BIP 340 signature carrier. -/
def exampleSig : SchnorrSig :=
  ⟨ByteArray.mk (List.replicate 64 (0 : UInt8)).toArray⟩

theorem exampleSig_valid : exampleSig.Valid := rfl

/-- `SchnorrSig.Valid` is exactly the 64-byte wire constraint of BOLT 1
`bip340sig` and `lightning/src/util/ser.rs:684`. -/
theorem schnorrSig_valid_iff (s : SchnorrSig) : s.Valid ↔ s.bytes.size = 64 :=
  Iff.rfl

/-- A 65-byte signature carrier is invalid: the model wire format is
`SIGHASH_DEFAULT` only.  The 65-byte `SIGHASH_ALL` variant of
`bolt-simple-taproot.md:205-207` is not representable. -/
theorem sig65_not_valid :
    ¬ (⟨ByteArray.mk (List.replicate 65 (0 : UInt8)).toArray⟩ : SchnorrSig).Valid := by
  intro h
  unfold SchnorrSig.Valid at h
  have hs : (⟨ByteArray.mk (List.replicate 65 (0 : UInt8)).toArray⟩ :
      SchnorrSig).bytes.size = 65 := rfl
  omega

/-! ## 2. Deterministic verification and conditional unforgeability -/

/-- BIP 340 verification ignores auxiliary randomness (that input exists only
for signing).  The model makes this explicit as a function that takes an aux
string and drops it. -/
def verifyWithAux (M : PrimitiveModel) (_aux : ByteArray) (pk : PubKey)
    (msg : ByteArray) (sig : SchnorrSig) : Bool :=
  M.schnorrVerify pk msg sig

/-- Verification is deterministic: the aux input cannot influence the result. -/
theorem verification_aux_independent (M : PrimitiveModel) (a b : ByteArray)
    (pk : PubKey) (msg : ByteArray) (sig : SchnorrSig) :
    verifyWithAux M a pk msg sig = verifyWithAux M b pk msg sig := rfl

/-- Schnorr verification through the x-only embedding. -/
def schnorrVerifyXOnly (M : PrimitiveModel) (k : XOnlyPubKey)
    (msg : ByteArray) (sig : SchnorrSig) : Bool :=
  M.schnorrVerify k.toPubKey msg sig

/-- **Message binding.**  Conditional on `AssumesEufCma`, a signature accepted
for one message cannot be accepted for another under the same key.  This is
the only place the Schnorr assumption is consumed. -/
theorem schnorr_message_bound (M : PrimitiveModel) (h : AssumesEufCma M)
    {pk : PubKey} {m₁ m₂ : ByteArray} {sig : SchnorrSig}
    (h₁ : M.schnorrVerify pk m₁ sig = true)
    (h₂ : M.schnorrVerify pk m₂ sig = true) : m₁ = m₂ :=
  h.2 pk m₁ m₂ sig h₁ h₂

/-- Message binding in the x-only key representation. -/
theorem schnorrVerifyXOnly_message_bound (M : PrimitiveModel)
    (h : AssumesEufCma M) {k : XOnlyPubKey} {m₁ m₂ : ByteArray}
    {sig : SchnorrSig}
    (h₁ : schnorrVerifyXOnly M k m₁ sig = true)
    (h₂ : schnorrVerifyXOnly M k m₂ sig = true) : m₁ = m₂ :=
  h.2 k.toPubKey m₁ m₂ sig h₁ h₂

/-- **A forgery refutes the assumption.**  Exhibiting one signature that
verifies for two distinct messages proves that the model's EUF-CMA field is
false.  This is the contrapositive direction: unforgeability is a hypothesis,
never a theorem about the format. -/
theorem forgery_refutes_eufCma (M : PrimitiveModel) {pk : PubKey}
    {m₁ m₂ : ByteArray} {sig : SchnorrSig} (hne : m₁ ≠ m₂)
    (h₁ : M.schnorrVerify pk m₁ sig = true)
    (h₂ : M.schnorrVerify pk m₂ sig = true) :
    ¬ EufCma M.schnorrVerify := by
  intro h
  exact hne (h pk m₁ m₂ sig h₁ h₂)

/-- The always-accepting verifier satisfies every formatting law but is not
EUF-CMA.  Hence the 64-byte/32-byte wire laws alone cannot establish
unforgeability; the `schnorr_eufCma` field is substantive. -/
theorem acceptsAll_not_eufCma :
    ¬ EufCma (fun (_ : PubKey) (_ : ByteArray) (_ : SchnorrSig) => true) := by
  intro h
  have hm : (ByteArray.empty : ByteArray) = ByteArray.mk #[0] :=
    h ⟨ByteArray.empty⟩ ByteArray.empty (ByteArray.mk #[0]) ⟨ByteArray.empty⟩
      rfl rfl
  have hs : ByteArray.empty.size = (ByteArray.mk #[0]).size :=
    congrArg ByteArray.size hm
  have h0 : ByteArray.empty.size = 0 := rfl
  have h1 : (ByteArray.mk #[0]).size = 1 := rfl
  rw [h0, h1] at hs
  omega

/-! ## 3. BIP 340 tagged hashes and the BIP 341 tap tweak -/

/-- `"TapTweak"` (ASCII), the BIP 341 tweak tag
(`bolt-simple-taproot.md:129`). -/
def tapTweakTag : ByteArray :=
  ByteArray.mk #[0x54, 0x61, 0x70, 0x54, 0x77, 0x65, 0x65, 0x6b]

/-- `"TapSighash"` (ASCII), the BIP 341 signature-hash tag. -/
def tapSighashTag : ByteArray :=
  ByteArray.mk #[0x54, 0x61, 0x70, 0x53, 0x69, 0x67, 0x68, 0x61, 0x73, 0x68]

theorem tapTweakTag_size : tapTweakTag.size = 8 := rfl

theorem tapSighashTag_size : tapSighashTag.size = 10 := rfl

/-- The two BIP 341 tags are distinct byte strings. -/
theorem tapTweakTag_ne_tapSighashTag : tapTweakTag ≠ tapSighashTag := by
  intro h
  have hs : tapTweakTag.size = tapSighashTag.size := congrArg ByteArray.size h
  rw [tapTweakTag_size, tapSighashTag_size] at hs
  omega

/-- BIP 340 tagged hash:
`tagged_hash(tag, msg) = SHA256(SHA256(tag) || SHA256(tag) || msg)`
(`bolt-simple-taproot.md:137-141`). -/
def taggedHash (M : PrimitiveModel) (tag msg : ByteArray) : ByteArray :=
  M.sha256 (M.sha256 tag ++ M.sha256 tag ++ msg)

theorem taggedHash_size (M : PrimitiveModel) (tag msg : ByteArray) :
    (taggedHash M tag msg).size = 32 :=
  M.sha256_size _

/-- A script-tree root is absent (BIP 86-style key-only output) or a 32-byte
BIP 341 root.  The BOLT draft leaves the root optional at
`bolt-simple-taproot.md:126-130` and `:188-191`. -/
def MerkleRootValid : Option ByteArray → Prop
  | none => True
  | some r => r.size = 32

/-- The bytes appended for the optional root: nothing, or the 32-byte root. -/
def rootBytes : Option ByteArray → ByteArray
  | none => ByteArray.empty
  | some r => r

@[simp] theorem rootBytes_none : rootBytes none = ByteArray.empty := rfl

@[simp] theorem rootBytes_some (r : ByteArray) : rootBytes (some r) = r := rfl

/-- Cancellation on the left when the two right suffixes have equal length:
`a ++ b = c ++ d` with `b.size = d.size` gives `a = c`.  This is the
length-aware companion of `Crypto.append_right_cancel`, needed because the
taproot preimage concatenates a key with an optional root. -/
theorem append_inj_of_size_eq {a b c d : ByteArray}
    (h : a ++ b = c ++ d) (hb : b.size = d.size) : a = c := by
  have hd : (a ++ b).data.toList = (c ++ d).data.toList :=
    congrArg (fun x : ByteArray => x.data.toList) h
  simp only [ByteArray.toList_data_append] at hd
  have hlen : b.data.toList.length = d.data.toList.length := by
    simpa using hb
  have h1 := (List.append_inj' hd hlen).1
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simpa using h1

/-- The suffix half of `append_inj_of_size_eq`. -/
theorem append_inj_of_size_eq' {a b c d : ByteArray}
    (h : a ++ b = c ++ d) (hb : b.size = d.size) : b = d := by
  have hd : (a ++ b).data.toList = (c ++ d).data.toList :=
    congrArg (fun x : ByteArray => x.data.toList) h
  simp only [ByteArray.toList_data_append] at hd
  have hlen : b.data.toList.length = d.data.toList.length := by
    simpa using hb
  have h2 := (List.append_inj' hd hlen).2
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simpa using h2

/-- The BIP 341 tap tweak digest
`t = tagged_hash("TapTweak", internal_key || script_root)`
(`bolt-simple-taproot.md:129`).  This is the value that commits to the
internal key and the merkle root. -/
def tapTweak (M : PrimitiveModel) (internal : XOnlyPubKey)
    (root : Option ByteArray) : ByteArray :=
  taggedHash M tapTweakTag (internal.bytes ++ rootBytes root)

theorem tapTweak_size (M : PrimitiveModel) (internal : XOnlyPubKey)
    (root : Option ByteArray) : (tapTweak M internal root).size = 32 :=
  taggedHash_size M tapTweakTag _

/-- Model-level taproot output-key commitment.  BIP 341's real key is the
x-only encoding of `P + t*G` (`bolt-simple-taproot.md:129`); the model has no
group law, so it identifies the output key with the tweak digest `t`, which is
the 32-byte value binding `(internal key, root)`. -/
def taprootOutputKey (M : PrimitiveModel) (internal : XOnlyPubKey)
    (root : Option ByteArray) : ByteArray :=
  tapTweak M internal root

theorem taprootOutputKey_size (M : PrimitiveModel) (internal : XOnlyPubKey)
    (root : Option ByteArray) : (taprootOutputKey M internal root).size = 32 :=
  tapTweak_size M internal root

/-- Equal taproot commitments give equal hash arguments.  Used by the three
binding lemmas below. -/
theorem taprootOutputKey_arg_eq (M : PrimitiveModel)
    (hH : PreimageResistant M.sha256) {i₁ i₂ : XOnlyPubKey}
    {r₁ r₂ : Option ByteArray}
    (heq : taprootOutputKey M i₁ r₁ = taprootOutputKey M i₂ r₂) :
    i₁.bytes ++ rootBytes r₁ = i₂.bytes ++ rootBytes r₂ := by
  unfold taprootOutputKey tapTweak taggedHash at heq
  exact append_left_cancel (hH _ _ heq)

/-- **Root binding.**  With the internal key fixed, two valid 32-byte merkle
roots that produce the same output commitment are equal.  Conditional on the
model's `PreimageResistant` hash field (C1's idealised injectivity; the
tagged-hash preimage is longer than 32 bytes, so the narrower
`CollisionResistant` field does not apply). -/
theorem taprootOutputKey_binds_merkleRoot (M : PrimitiveModel)
    (hH : PreimageResistant M.sha256) {internal : XOnlyPubKey}
    {r₁ r₂ : ByteArray} (_h₁ : r₁.size = 32) (_h₂ : r₂.size = 32)
    (heq : taprootOutputKey M internal (some r₁) =
      taprootOutputKey M internal (some r₂)) : r₁ = r₂ := by
  have harg := taprootOutputKey_arg_eq M hH heq
  simp only [rootBytes_some] at harg
  exact append_left_cancel harg

/-- **Internal-key binding.**  With the script-tree root fixed, two valid
x-only keys with the same output commitment are equal. -/
theorem taprootOutputKey_binds_internal (M : PrimitiveModel)
    (hH : PreimageResistant M.sha256) {i₁ i₂ : XOnlyPubKey}
    (h₁ : i₁.Valid) (h₂ : i₂.Valid) {root : Option ByteArray}
    (heq : taprootOutputKey M i₁ root = taprootOutputKey M i₂ root) :
    i₁ = i₂ := by
  have harg := taprootOutputKey_arg_eq M hH heq
  have hbytes : i₁.bytes = i₂.bytes := append_right_cancel harg
  rcases i₁ with ⟨b₁⟩
  rcases i₂ with ⟨b₂⟩
  simpa using hbytes

/-- A key-only output (no script root) cannot collide with a script-tree
output: the hash inputs have different lengths. -/
theorem taprootOutputKey_none_ne_some (M : PrimitiveModel)
    (hH : PreimageResistant M.sha256) {i₁ i₂ : XOnlyPubKey}
    (h₁ : i₁.Valid) (h₂ : i₂.Valid) {r : ByteArray} (hr : r.size = 32) :
    taprootOutputKey M i₁ none ≠ taprootOutputKey M i₂ (some r) := by
  intro heq
  have harg := taprootOutputKey_arg_eq M hH heq
  simp only [rootBytes_none, rootBytes_some, ByteArray.append_empty] at harg
  have hs : i₁.bytes.size = (i₂.bytes ++ r).size := congrArg ByteArray.size harg
  rw [ByteArray.size_append] at hs
  unfold XOnlyPubKey.Valid at h₁ h₂
  rw [h₁, h₂, hr] at hs
  omega

/-- **Pair binding (capstone).**  A valid taproot output commitment determines
both the internal key and the optional script-tree root.  This combines the
three lemmas above and is the formal content of "the output key commits to the
internal key and merkle root". -/
theorem taprootOutputKey_pair_injective (M : PrimitiveModel)
    (hH : PreimageResistant M.sha256) {i₁ i₂ : XOnlyPubKey}
    {r₁ r₂ : Option ByteArray} (hi₁ : i₁.Valid) (hi₂ : i₂.Valid)
    (hr₁ : MerkleRootValid r₁) (hr₂ : MerkleRootValid r₂)
    (heq : taprootOutputKey M i₁ r₁ = taprootOutputKey M i₂ r₂) :
    i₁ = i₂ ∧ r₁ = r₂ := by
  cases r₁ with
  | none =>
    cases r₂ with
    | none =>
      exact ⟨taprootOutputKey_binds_internal M hH hi₁ hi₂ heq, rfl⟩
    | some b =>
      have hb : b.size = 32 := hr₂
      exact absurd heq (taprootOutputKey_none_ne_some M hH hi₁ hi₂ hb)
  | some a =>
    cases r₂ with
    | none =>
      have ha : a.size = 32 := hr₁
      exact absurd heq.symm (taprootOutputKey_none_ne_some M hH hi₂ hi₁ ha)
    | some b =>
      have ha : a.size = 32 := hr₁
      have hb : b.size = 32 := hr₂
      have h12 : i₁.bytes ++ a = i₂.bytes ++ b := by
        simpa only [rootBytes_some] using taprootOutputKey_arg_eq M hH heq
      have hbytes : i₁.bytes = i₂.bytes :=
        append_inj_of_size_eq h12 (by rw [ha, hb])
      have hroot : a = b :=
        append_inj_of_size_eq' h12 (by rw [ha, hb])
      rcases i₁ with ⟨b₁⟩
      rcases i₂ with ⟨b₂⟩
      exact ⟨by simpa using hbytes, by rw [hroot]⟩

/-! ## 4. Key-path / script-path domain separation -/

/-- BIP 341 sighash preimage for a key path spend: `ext_flag = 0`
(`bolt-simple-taproot.md:200-210`).  Every other `SigMsg` field is abstracted
into the opaque `msg`. -/
def keyPathPreimage (msg : ByteArray) : ByteArray :=
  (ByteArray.empty.push (0x00 : UInt8)) ++ msg

/-- BIP 341 sighash preimage for a script path spend: `ext_flag = 1`, then
the message and the revealed tapleaf hash
(`bolt-simple-taproot.md:221-237`).  The tree path and control block are not
modelled. -/
def scriptPathPreimage (msg leaf : ByteArray) : ByteArray :=
  (ByteArray.empty.push (0x01 : UInt8)) ++ msg ++ leaf

/-- The key-path and script-path sighash preimages differ in their first byte
for every message and leaf.  This is the structural core of the domain
separation; it is a checked finite fact about the two byte prefixes, not a
hash assumption. -/
theorem keyPathPreimage_ne_scriptPathPreimage (msg leaf : ByteArray) :
    keyPathPreimage msg ≠ scriptPathPreimage msg leaf := by
  intro h
  have hd : (keyPathPreimage msg).data.toList =
      (scriptPathPreimage msg leaf).data.toList :=
    congrArg (fun x : ByteArray => x.data.toList) h
  simp [keyPathPreimage, scriptPathPreimage] at hd

/-- BIP 341 taproot sighash digest over a preimage. -/
def tapSighash (M : PrimitiveModel) (preimage : ByteArray) : ByteArray :=
  taggedHash M tapSighashTag preimage

def keyPathDigest (M : PrimitiveModel) (msg : ByteArray) : ByteArray :=
  tapSighash M (keyPathPreimage msg)

def scriptPathDigest (M : PrimitiveModel) (msg leaf : ByteArray) : ByteArray :=
  tapSighash M (scriptPathPreimage msg leaf)

/-- **Domain separation.**  The key-path and script-path digests are distinct
for the same untagged message.  Conditional on hash injectivity; the first-byte
difference alone does not make SHA-256 outputs differ. -/
theorem keyPathDigest_ne_scriptPathDigest (M : PrimitiveModel)
    (hH : PreimageResistant M.sha256) (msg leaf : ByteArray) :
    keyPathDigest M msg ≠ scriptPathDigest M msg leaf := by
  intro h
  unfold keyPathDigest scriptPathDigest tapSighash taggedHash at h
  have hpre : keyPathPreimage msg = scriptPathPreimage msg leaf :=
    append_left_cancel (hH _ _ h)
  exact keyPathPreimage_ne_scriptPathPreimage msg leaf hpre

/-- A script-path digest binds the revealed tapleaf: equal digests for the
same message imply equal leaf bytes. -/
theorem scriptPathDigest_binds_leaf (M : PrimitiveModel)
    (hH : PreimageResistant M.sha256) {msg leaf₁ leaf₂ : ByteArray}
    (heq : scriptPathDigest M msg leaf₁ = scriptPathDigest M msg leaf₂) :
    leaf₁ = leaf₂ := by
  unfold scriptPathDigest tapSighash taggedHash at heq
  have hpre : scriptPathPreimage msg leaf₁ = scriptPathPreimage msg leaf₂ :=
    append_left_cancel (hH _ _ heq)
  exact append_left_cancel hpre

/-- BIP 340 verification for a key-path spend: the key is the tweaked output
key, the message is the key-path sighash digest. -/
def verifyKeyPath (M : PrimitiveModel) (outputKey : XOnlyPubKey)
    (msg : ByteArray) (sig : SchnorrSig) : Bool :=
  M.schnorrVerify outputKey.toPubKey (keyPathDigest M msg) sig

/-- BIP 340 verification for a script-path spend: the key is the same tweaked
output key, the message is the script-path sighash digest including the leaf. -/
def verifyScriptPath (M : PrimitiveModel) (outputKey : XOnlyPubKey)
    (msg leaf : ByteArray) (sig : SchnorrSig) : Bool :=
  M.schnorrVerify outputKey.toPubKey (scriptPathDigest M msg leaf) sig

/-- **No cross-path replay.**  Conditional on hash injectivity and
`AssumesEufCma`, one signature cannot verify both as a key-path and as a
script-path spend for the same untagged message (for any leaf).  This is the
taproot analogue of `Crypto.Sig.verifyFunding_not_verifyCommitment`. -/
theorem keyPath_not_scriptPath (M : PrimitiveModel)
    (hH : PreimageResistant M.sha256) (hE : AssumesEufCma M)
    {outputKey : XOnlyPubKey} {msg leaf : ByteArray} {sig : SchnorrSig}
    (hk : verifyKeyPath M outputKey msg sig = true)
    (hs : verifyScriptPath M outputKey msg leaf sig = true) : False := by
  have hd : keyPathDigest M msg = scriptPathDigest M msg leaf :=
    hE.2 outputKey.toPubKey _ _ sig hk hs
  exact keyPathDigest_ne_scriptPathDigest M hH msg leaf hd

end LnLean.Proofs.Crypto
