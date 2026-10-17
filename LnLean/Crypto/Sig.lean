/-
# Lightning signature verification and domain separation

**English claim.**  Lightning signs three different kinds of protocol data:
the funding transaction, commitment transactions, and the mutual-close
transaction.  Each signature is verified over a *tagged* message so that a
signature produced for one domain cannot be replayed as a signature for
another.  Under the model's EUF-CMA field, a verified signature is bound to
exactly one message, and distinct tags therefore separate the domains.

**BOLT sections.**  BOLT 2 §The `funding_signed` Message, §The
`commitment_signed` Message, §Legacy Closing Negotiation: `closing_signed`;
BOLT 3 (signature hashes).  BOLT 1 defines the 64-byte `signature` wire type.

**rust-lightning anchors (commit fe49009).**
* `lightning/src/crypto/utils.rs:75-83` — ECDSA signing over a message digest.
* `lightning/src/util/message_signing.rs:83-89` — signature verification.
* `lightning/src/ln/chan_utils.rs:600-660` — commitment key derivation and
  the keys used by funding/commitment signatures.
* `lightning/src/ln/msgs.rs:3213` — `commitment_signed`;
  `:3227` — `funding_created`; `:3234` — `funding_signed`;
  `:3185` — `closing_signed`.

**Not modelled.**  BIP-340 tagged-hash byte layouts, DER encoding, low-S
normalisation, sighash computation over BOLT 3 transactions, key derivation
from basepoints, and multi-signature aggregation.  The tags below are compact
stand-ins that make the domain-separation statement explicit; they are not the
wire bytes of any BOLT message.
-/

import LnLean.Crypto.Model

namespace LnLean.Crypto

set_option autoImplicit false

open LnLean

/-! ## Domain-separation tags -/

/-- Funding-transaction signature domain ("fund"). -/
def fundingTag : ByteArray := ByteArray.mk #[0x66, 0x75, 0x6e, 0x64]

/-- Commitment-transaction signature domain ("commit"). -/
def commitmentTag : ByteArray := ByteArray.mk #[0x63, 0x6f, 0x6d, 0x6d, 0x69, 0x74]

/-- Mutual-close signature domain ("close"). -/
def closeTag : ByteArray := ByteArray.mk #[0x63, 0x6c, 0x6f, 0x73, 0x65]

theorem fundingTag_size : fundingTag.size = 4 := rfl
theorem commitmentTag_size : commitmentTag.size = 6 := rfl
theorem closeTag_size : closeTag.size = 5 := rfl

/-- The three protocol domains have distinct tags. -/
theorem fundingTag_ne_commitmentTag : fundingTag ≠ commitmentTag := by
  intro h
  have hs : fundingTag.size = commitmentTag.size := congrArg ByteArray.size h
  rw [fundingTag_size, commitmentTag_size] at hs
  omega

theorem fundingTag_ne_closeTag : fundingTag ≠ closeTag := by
  intro h
  have hs : fundingTag.size = closeTag.size := congrArg ByteArray.size h
  rw [fundingTag_size, closeTag_size] at hs
  omega

theorem commitmentTag_ne_closeTag : commitmentTag ≠ closeTag := by
  intro h
  have hs : commitmentTag.size = closeTag.size := congrArg ByteArray.size h
  rw [commitmentTag_size, closeTag_size] at hs
  omega

/-! ## The three verification functions -/

/-- Verify a funding-transaction signature over a tagged message. -/
def verifyFunding (M : PrimitiveModel) (pk : PubKey) (msg : ByteArray)
    (sig : EcdsaSig) : Bool :=
  M.ecdsaVerify pk (fundingTag ++ msg) sig

/-- Verify a commitment-transaction signature over a tagged message. -/
def verifyCommitment (M : PrimitiveModel) (pk : PubKey) (msg : ByteArray)
    (sig : EcdsaSig) : Bool :=
  M.ecdsaVerify pk (commitmentTag ++ msg) sig

/-- Verify a mutual-close signature over a tagged message. -/
def verifyClose (M : PrimitiveModel) (pk : PubKey) (msg : ByteArray)
    (sig : EcdsaSig) : Bool :=
  M.ecdsaVerify pk (closeTag ++ msg) sig

/-! ## Conditional signature theorems -/

/-- The model's two EUF-CMA assumption fields, as one predicate. -/
abbrev AssumesEufCma (M : PrimitiveModel) : Prop :=
  EufCma M.ecdsaVerify ∧ EufCma M.schnorrVerify

/-- Every `PrimitiveModel` carries proofs of its two EUF-CMA fields. -/
theorem assumesEufCma_of_model (M : PrimitiveModel) : AssumesEufCma M :=
  ⟨M.ecdsa_eufCma, M.schnorr_eufCma⟩

/-- ECDSA message binding from the combined assumption. -/
theorem assumesEufCma_ecdsa (M : PrimitiveModel) (h : AssumesEufCma M) :
    EufCma M.ecdsaVerify := h.1

/-- Schnorr message binding from the combined assumption. -/
theorem assumesEufCma_schnorr (M : PrimitiveModel) (h : AssumesEufCma M) :
    EufCma M.schnorrVerify := h.2

/-- A verified funding signature determines the untagged message. -/
theorem verifyFunding_message_bound (M : PrimitiveModel)
    (h : EufCma M.ecdsaVerify) {pk : PubKey} {msg₁ msg₂ : ByteArray}
    {sig : EcdsaSig}
    (h₁ : verifyFunding M pk msg₁ sig = true)
    (h₂ : verifyFunding M pk msg₂ sig = true) : msg₁ = msg₂ := by
  have ht : fundingTag ++ msg₁ = fundingTag ++ msg₂ := h pk _ _ sig h₁ h₂
  exact append_left_cancel ht

/-- A verified commitment signature determines the untagged message. -/
theorem verifyCommitment_message_bound (M : PrimitiveModel)
    (h : EufCma M.ecdsaVerify) {pk : PubKey} {msg₁ msg₂ : ByteArray}
    {sig : EcdsaSig}
    (h₁ : verifyCommitment M pk msg₁ sig = true)
    (h₂ : verifyCommitment M pk msg₂ sig = true) : msg₁ = msg₂ := by
  have ht : commitmentTag ++ msg₁ = commitmentTag ++ msg₂ := h pk _ _ sig h₁ h₂
  exact append_left_cancel ht

/-- A verified close signature determines the untagged message. -/
theorem verifyClose_message_bound (M : PrimitiveModel)
    (h : EufCma M.ecdsaVerify) {pk : PubKey} {msg₁ msg₂ : ByteArray}
    {sig : EcdsaSig}
    (h₁ : verifyClose M pk msg₁ sig = true)
    (h₂ : verifyClose M pk msg₂ sig = true) : msg₁ = msg₂ := by
  have ht : closeTag ++ msg₁ = closeTag ++ msg₂ := h pk _ _ sig h₁ h₂
  exact append_left_cancel ht

/-- **Domain separation, funding vs commitment.**  One signature cannot verify
as both a funding and a commitment signature for the same untagged message. -/
theorem verifyFunding_not_verifyCommitment (M : PrimitiveModel)
    (h : EufCma M.ecdsaVerify) {pk : PubKey} {msg : ByteArray}
    {sig : EcdsaSig}
    (hf : verifyFunding M pk msg sig = true)
    (hc : verifyCommitment M pk msg sig = true) : False := by
  have ht : fundingTag ++ msg = commitmentTag ++ msg := h pk _ _ sig hf hc
  exact fundingTag_ne_commitmentTag (append_right_cancel ht)

/-- **Domain separation, funding vs close.** -/
theorem verifyFunding_not_verifyClose (M : PrimitiveModel)
    (h : EufCma M.ecdsaVerify) {pk : PubKey} {msg : ByteArray}
    {sig : EcdsaSig}
    (hf : verifyFunding M pk msg sig = true)
    (hc : verifyClose M pk msg sig = true) : False := by
  have ht : fundingTag ++ msg = closeTag ++ msg := h pk _ _ sig hf hc
  exact fundingTag_ne_closeTag (append_right_cancel ht)

/-- **Domain separation, commitment vs close.** -/
theorem verifyCommitment_not_verifyClose (M : PrimitiveModel)
    (h : EufCma M.ecdsaVerify) {pk : PubKey} {msg : ByteArray}
    {sig : EcdsaSig}
    (hf : verifyCommitment M pk msg sig = true)
    (hc : verifyClose M pk msg sig = true) : False := by
  have ht : commitmentTag ++ msg = closeTag ++ msg := h pk _ _ sig hf hc
  exact commitmentTag_ne_closeTag (append_right_cancel ht)

end LnLean.Crypto
