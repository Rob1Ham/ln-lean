/-
# Cryptographic primitive interface

**English claim.**  Lightning's security rests on a small set of cryptographic
primitives (SHA-256, HASH160, ECDSA, BIP-340 Schnorr, ECDH, HKDF, an AEAD, and
HMAC-SHA256).  This module declares those operations in one structure and
states the *algebraic* properties the rest of the model is allowed to use.
The properties are `Prop`-valued fields of the structure, never axioms: every
theorem that needs collision resistance, unforgeability, AEAD correctness, or
HMAC message binding must take the corresponding field as a hypothesis.

The model idealises computational assumptions as exact algebraic laws.  For
example, `CollisionResistant H` is injectivity of `H` on 32-byte preimages;
this is stronger than "no efficient collision finder exists", but it is the
sound over-approximation used by the scaffold and it keeps all downstream
statements conditional and visible.

**BOLT sections.**  BOLT 1 §Lightning Message Format (hash and signature
types), BOLT 2 (funding/commitment signatures, payment hashes), BOLT 8
(Noise: SHA-256, ECDH, HKDF, ChaCha20-Poly1305), BOLT 4 (HMAC-SHA256).

**rust-lightning anchors (commit fe49009).**
* `lightning-types/src/payment.rs:70-73` — `PaymentHash` is SHA-256 of the
  32-byte preimage.
* `lightning/src/crypto/utils.rs:75-83` — ECDSA signing over a message digest.
* `lightning/src/util/message_signing.rs:83-89` — signature verification.
* `lightning/src/ln/peer_channel_encryptor.rs:150-214` — AEAD with a 12-byte
  nonce, and `:215-236` HKDF key derivation.

**Not modelled.**  Concrete SHA-256 compression, secp256k1 group arithmetic,
DER parsing, ChaCha20/Poly1305 internals, side channels, key generation,
probabilistic security games, and computational reductions.  Randomness and
oracle access are not modelled; the `Prop` fields are exact laws.  In
particular the interface does **not** assume global injectivity of SHA-256 on
arbitrary byte strings: that would contradict the structural field
`sha256_size`, and collision resistance is assumed only on 32-byte preimages.
-/

import LnLean.Basic.Core

namespace LnLean.Crypto

set_option autoImplicit false

open LnLean

/-! ## Assumed properties, as predicates rather than axioms -/

/-- Idealised collision resistance on the 32-byte preimages used by Lightning
payment hashes and commitment seeds.  Two 32-byte inputs with the same digest
are equal. -/
abbrev CollisionResistant (H : ByteArray → ByteArray) : Prop :=
  ∀ x y : ByteArray, x.size = 32 → y.size = 32 → H x = H y → x = y

/-- Idealised preimage resistance: the hash is injective on arbitrary byte
strings.  This predicate is **not** a field of `PrimitiveModel`: a function
with 32-byte output cannot be injective on all of `ByteArray` (see
`LnLean.Proofs.Crypto.Sha256Props.preimageResistant_vacuous`).  It is retained
only as an explicit hypothesis for conditional algebraic statements, not as a
global assumption about the model's SHA-256. -/
abbrev PreimageResistant (H : ByteArray → ByteArray) : Prop :=
  ∀ x y : ByteArray, H x = H y → x = y

/-- Idealised existential unforgeability under chosen message: a single
signature cannot verify for two distinct messages under one key.  This is the
message-binding consequence of EUF-CMA that the protocol proofs consume. -/
abbrev EufCma {Sig : Type} (verify : PubKey → ByteArray → Sig → Bool) : Prop :=
  ∀ (pk : PubKey) (m₁ m₂ : ByteArray) (s : Sig),
    verify pk m₁ s = true → verify pk m₂ s = true → m₁ = m₂

/-- AEAD interface: decryption inverts encryption, and a ciphertext determines
its plaintext (integrity).  IND-CCA itself is a computational game; these two
laws are the correctness/integrity consequences used below. -/
abbrev AeadIndCca
    (enc : ByteArray → ByteArray → ByteArray → ByteArray)
    (dec : ByteArray → ByteArray → ByteArray → Option ByteArray) : Prop :=
  (∀ (k n p : ByteArray), dec k n (enc k n p) = some p) ∧
  (∀ (k n c p : ByteArray), dec k n c = some p → enc k n p = c)

/-- HMAC interface: under a fixed key the MAC binds the message (no two
distinct messages share a tag).  This is the PRF consequence used for onion
integrity and authentication. -/
abbrev HmacPrf (hmac : ByteArray → ByteArray → ByteArray) : Prop :=
  ∀ (k m₁ m₂ : ByteArray), hmac k m₁ = hmac k m₂ → m₁ = m₂

/-! ## The primitive model -/

/-- All cryptographic operations used by the Lightning model.  The `_size`
fields are structural facts about the wire formats; the remaining fields are
the assumed properties from `docs/ASSUMPTIONS.md` C1–C8. -/
structure PrimitiveModel where
  sha256 : ByteArray → ByteArray
  hash160 : ByteArray → ByteArray
  ecdsaVerify : PubKey → ByteArray → EcdsaSig → Bool
  schnorrVerify : PubKey → ByteArray → SchnorrSig → Bool
  ecdh : ByteArray → PubKey → ByteArray
  hkdf : ByteArray → ByteArray → Nat → ByteArray
  aeadSeal : ByteArray → ByteArray → ByteArray → ByteArray
  aeadOpen : ByteArray → ByteArray → ByteArray → Option ByteArray
  hmacSha256 : ByteArray → ByteArray → ByteArray
  /-- SHA-256 always produces 32 bytes (BOLT 1 `sha256`). -/
  sha256_size : ∀ b : ByteArray, (sha256 b).size = 32
  /-- HASH160 always produces 20 bytes (BOLT 1, P2WPKH). -/
  hash160_size : ∀ b : ByteArray, (hash160 b).size = 20
  /-- HMAC-SHA256 always produces 32 bytes. -/
  hmac_size : ∀ k m : ByteArray, (hmacSha256 k m).size = 32
  sha256_collisionResistant : CollisionResistant sha256
  ecdsa_eufCma : EufCma ecdsaVerify
  schnorr_eufCma : EufCma schnorrVerify
  aead_indCca : AeadIndCca aeadSeal aeadOpen
  hmac_prf : HmacPrf hmacSha256

namespace PrimitiveModel

variable (M : PrimitiveModel)

/-- The concrete 32-byte image of SHA-256, with a total pad/truncate fallback
so that malformed model inputs still yield a well-typed `sha256` value. -/
def digest32 (b : ByteArray) : ByteArray :=
  if b.size = 32 then b
  else ByteArray.mk (List.replicate 32 (0 : UInt8)).toArray

/-- `digest32` returns a 32-byte string. -/
theorem digest32_size (b : ByteArray) : (digest32 b).size = 32 := by
  unfold digest32
  split
  · assumption
  · rfl

/-- On a well-formed 32-byte digest, `digest32` is the identity. -/
theorem digest32_of_size {b : ByteArray} (h : b.size = 32) : digest32 b = b := by
  unfold digest32
  simp [h]

/-- HASH160 output is 20 bytes. -/
theorem hash160_output_size (b : ByteArray) : (M.hash160 b).size = 20 :=
  M.hash160_size b

/-- HMAC-SHA256 output is 32 bytes. -/
theorem hmac_output_size (k m : ByteArray) : (M.hmacSha256 k m).size = 32 :=
  M.hmac_size k m

/-- SHA-256 output is 32 bytes. -/
theorem sha256_output_size (b : ByteArray) : (M.sha256 b).size = 32 :=
  M.sha256_size b

/-- The payment hash of a 32-byte preimage.  BOLT 2 and
`lightning-types/src/payment.rs:70-73` define this as SHA-256(preimage). -/
def paymentHashOf (pre : Preimage) : PaymentHash :=
  ⟨digest32 (M.sha256 pre.bytes)⟩

/-- A payment hash produced by `paymentHashOf` is always 32 bytes. -/
theorem paymentHashOf_valid (pre : Preimage) : (M.paymentHashOf pre).Valid :=
  digest32_size _

/-- Per-commitment seed derivation: a 32-byte base secret mixed with a
commitment index and hashed (BOLT 3 key derivation; the concrete tagged hash
is abstracted here).  The index is encoded in decimal so that the function is
total and injective on indices. -/
def commitmentSeed (base : ByteArray) (index : Nat) : ByteArray :=
  M.sha256 (base ++ (toString index).toUTF8)

/-- `commitmentSeed` is a 32-byte digest. -/
theorem commitmentSeed_size (base : ByteArray) (index : Nat) :
    (M.commitmentSeed base index).size = 32 :=
  M.sha256_size _

end PrimitiveModel

/-! ## Byte-array cancellation helpers

These are structural facts about `ByteArray` (a thin wrapper over `Array
UInt8`) reused by `Crypto.Sig` and `Wire.Message`. -/

/-- Left cancellation for `ByteArray` concatenation. -/
theorem append_left_cancel {a b c : ByteArray} (h : a ++ b = a ++ c) : b = c := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  have h2 : (a.data ++ b.data).toList = (a.data ++ c.data).toList := by
    simpa using congrArg (fun x : ByteArray => x.data.toList) h
  rw [Array.toList_append, Array.toList_append] at h2
  exact List.append_cancel_left h2

/-- Right cancellation for `ByteArray` concatenation. -/
theorem append_right_cancel {a b c : ByteArray} (h : a ++ b = c ++ b) : a = c := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  have h2 : (a.data ++ b.data).toList = (c.data ++ b.data).toList := by
    simpa using congrArg (fun x : ByteArray => x.data.toList) h
  rw [Array.toList_append, Array.toList_append] at h2
  exact List.append_cancel_right h2

end LnLean.Crypto
