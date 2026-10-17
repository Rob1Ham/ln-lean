/-
# ECDSA verification seam: determinism, domain tags, wire shapes

**English claim.**  The three Lightning signature domains (funding,
commitment, mutual close) are verified by three total, deterministic
`Bool`-valued predicates that differ only in a fixed domain tag.  The tags
are pairwise distinct, and are in fact *prefix-free*, so no message pair can
make a funding-tagged byte string equal a commitment- or close-tagged one.
Consequently, under the model's `AssumesEufCma` field, a signature that
verifies in one domain cannot verify in another for any choice of messages:
domain separation does not depend on the untagged message being equal.

On the wire, a signature is either the BOLT 1 64-byte compact encoding or a
71--73-byte BOLT 3 witness encoding (DER body plus one sighash byte).  The
module defines the parser predicate `derEnvelope` / `wireSigOK` that the model
lacks, proves that acceptance pins the length to exactly those shapes, and
gates each verification predicate on it (`verifyFundingChecked` etc.), so a
malformed-length signature is rejected before `ecdsaVerify` is consulted.

Finally, the module records two limits of the assumption.  `EufCma` binds a
signature to a *message* under a fixed key; it does **not** bind it to a key,
and it is not automatic for an arbitrary `Bool`-valued verifier.  The
key-change statement is therefore proved only under an explicit, additional
`KeyBinding` hypothesis, and no unforgeability claim is made.

**BOLT sections.**  BOLT 1 §Lightning Message Format (`signature`: a 64-byte
ECDSA signature); BOLT 2 §The `funding_created` Message, §The `funding_signed`
Message, §The `commitment_signed` Message, §Legacy Closing Negotiation:
`closing_signed`; BOLT 3 §Transaction Weight (DER signatures vary in size; 71
bytes budgeted per witness signature) and §Appendix B (signatures are sent in
compact encoding; the sighash byte is not transmitted).

**rust-lightning anchors (commit fe49009).**
* `lightning/src/crypto/utils.rs:75-83` — RFC6979 ECDSA signing over a
  message digest, used by every channel signature.
* `lightning/src/util/message_signing.rs:83-89` — `verify` returns `false`
  on any recovery/parse error, i.e. verification is a total `Bool` predicate.
* `lightning/src/ln/chan_utils.rs:1446-1452` — `get_sighash_all` for a
  commitment transaction (P2WSH `SighashCache`), and `:1456-1461`
  `sign_counterparty_commitment`; `:1465-1471` `sign_holder_commitment`.
* `lightning/src/ln/chan_utils.rs:1587-1593` — the closing transaction's
  `get_sighash_all`; `:1598-1604` its `sign`.
* `lightning/src/ln/chan_utils.rs:1050` — the funding input witness pushes
  `BitcoinSignature::sighash_all(funding_sig)`; `:961` does the same for
  HTLC-success witnesses.  This is where the 64-byte compact signature becomes
  a DER-plus-sighash script signature.
* `lightning/src/ln/chan_utils.rs:2244-2265` —
  `get_commitment_transaction_number_obscure_factor`, the commitment-specific
  mixing that makes the signed digest depend on channel state.

**Explicitly not modelled.**  secp256k1 group arithmetic, RFC6979 nonces,
low-S normalisation, scalar range checks (`1 ≤ r,s < n`), the full DER body
(two INTEGERs with canonical minimal encodings), conversion between compact
and DER encodings, BIP 143 sighash preimages, transaction construction, key
derivation from basepoints, and any proof of EUF-CMA.  The domain tags below
are the wave-A model's compact stand-ins for three distinct BOLT 3 sighash
digests; they are not wire bytes of any BOLT message.  `EufCma` is an
idealised message-binding law supplied as a field of `PrimitiveModel`, not a
reduction from a cryptographic game.
-/

import LnLean.Crypto.Sig
import LnLean.Crypto.Model
import LnLean.Basic.Core

namespace LnLean.Crypto

set_option autoImplicit false

open LnLean

/-! ## 1. Determinism and the definitional seam

The three predicates are definitions, not relations: they are total functions
of `(model, key, message, signature)`.  The following `rfl` lemma makes the
tag position explicit and is the only "determinism" content the model can
have; a `Bool` function is deterministic by construction. -/

/-- **Definitional seam.**  Each verification predicate is the model's single
ECDSA verifier applied to the domain tag concatenated with the untagged
message.  This is a checked (`rfl`) statement that the key, message, and tag
are exactly the arguments, and that verification has no hidden state. -/
theorem verify_definitions (M : PrimitiveModel) (pk : PubKey) (msg : ByteArray)
    (sig : EcdsaSig) :
    verifyFunding M pk msg sig = M.ecdsaVerify pk (fundingTag ++ msg) sig ∧
    verifyCommitment M pk msg sig =
      M.ecdsaVerify pk (commitmentTag ++ msg) sig ∧
    verifyClose M pk msg sig = M.ecdsaVerify pk (closeTag ++ msg) sig :=
  ⟨rfl, rfl, rfl⟩

/-- The verification predicates are `Bool`-valued: every call is either
`true` or `false`, so a caller that inspects the result decides the predicate
exactly once. -/
theorem verifyFunding_bool_cases (M : PrimitiveModel) (pk : PubKey)
    (msg : ByteArray) (sig : EcdsaSig) :
    verifyFunding M pk msg sig = true ∨ verifyFunding M pk msg sig = false := by
  cases verifyFunding M pk msg sig <;> simp

/-- **The three tags are pairwise distinct.**  This bundles the wave-A
`Crypto.Sig` size arguments into the statement the seam needs. -/
theorem tags_pairwise_distinct :
    fundingTag ≠ commitmentTag ∧ fundingTag ≠ closeTag ∧
      commitmentTag ≠ closeTag :=
  ⟨fundingTag_ne_commitmentTag, fundingTag_ne_closeTag,
    commitmentTag_ne_closeTag⟩

/-! ## 2. The tags are prefix-free, not merely distinct

The wave-A module proves that one signature cannot verify in two domains for
the *same* untagged message.  For a real seam we need the stronger fact: no
choice of untagged messages can align two differently tagged byte strings.
That follows because no tag is a prefix of another, which is a structural
property of the byte literals. -/

/-- List-level prefix lemma: if `a ++ x = b ++ y` and `a` is no longer than
`b`, then `b` decomposes as `a ++ z`.  This is the combinatorial core of
prefix-freeness. -/
private theorem list_append_eq_append_of_length_le {α : Type} {a b x y : List α}
    (h : a ++ x = b ++ y) (hab : a.length ≤ b.length) : ∃ z, b = a ++ z := by
  induction a generalizing b with
  | nil => exact ⟨b, by simp⟩
  | cons p ps ih =>
      cases b with
      | nil => simp at hab
      | cons q qs =>
          simp only [List.cons_append, List.cons.injEq] at h
          obtain ⟨rfl, hrest⟩ := h
          have hab' : ps.length ≤ qs.length := by simpa using hab
          obtain ⟨z, hz⟩ := ih hrest hab'
          exact ⟨z, by simp [hz]⟩

/-- **Funding and commitment domains never collide.**  For *arbitrary* pairs
of untagged messages, the two tagged byte strings differ. -/
theorem fundingTag_commitmentTag_prefixFree (m₁ m₂ : ByteArray) :
    fundingTag ++ m₁ ≠ commitmentTag ++ m₂ := by
  intro h
  have hlist : fundingTag.data.toList ++ m₁.data.toList =
      commitmentTag.data.toList ++ m₂.data.toList := by
    simpa [Array.toList_append] using
      congrArg (fun b : ByteArray => b.data.toList) h
  have hlen : fundingTag.data.toList.length ≤ commitmentTag.data.toList.length := by
    decide
  obtain ⟨z, hz⟩ := list_append_eq_append_of_length_le hlist hlen
  have hf : fundingTag.data.toList = [0x66, 0x75, 0x6e, 0x64] := by decide
  have hc : commitmentTag.data.toList = [0x63, 0x6f, 0x6d, 0x6d, 0x69, 0x74] := by
    decide
  rw [hf, hc] at hz
  have h1 := congrArg (List.take 1) hz
  simp at h1

/-- **Commitment and close domains never collide.** -/
theorem commitmentTag_closeTag_prefixFree (m₁ m₂ : ByteArray) :
    commitmentTag ++ m₁ ≠ closeTag ++ m₂ := by
  intro h
  -- The close tag is the shorter one, so orient the equality with it first.
  have h' : closeTag ++ m₂ = commitmentTag ++ m₁ := h.symm
  have hlist : closeTag.data.toList ++ m₂.data.toList =
      commitmentTag.data.toList ++ m₁.data.toList := by
    simpa [Array.toList_append] using
      congrArg (fun b : ByteArray => b.data.toList) h'
  have hlen : closeTag.data.toList.length ≤ commitmentTag.data.toList.length := by
    decide
  obtain ⟨z, hz⟩ := list_append_eq_append_of_length_le hlist hlen
  have hc : commitmentTag.data.toList = [0x63, 0x6f, 0x6d, 0x6d, 0x69, 0x74] := by
    decide
  have hd : closeTag.data.toList = [0x63, 0x6c, 0x6f, 0x73, 0x65] := by decide
  rw [hc, hd] at hz
  have h1 := congrArg (List.take 2) hz
  simp at h1

/-- **Funding and close domains never collide.** -/
theorem fundingTag_closeTag_prefixFree (m₁ m₂ : ByteArray) :
    fundingTag ++ m₁ ≠ closeTag ++ m₂ := by
  intro h
  have hlist : fundingTag.data.toList ++ m₁.data.toList =
      closeTag.data.toList ++ m₂.data.toList := by
    simpa [Array.toList_append] using
      congrArg (fun b : ByteArray => b.data.toList) h
  have hlen : fundingTag.data.toList.length ≤ closeTag.data.toList.length := by
    decide
  obtain ⟨z, hz⟩ := list_append_eq_append_of_length_le hlist hlen
  have hf : fundingTag.data.toList = [0x66, 0x75, 0x6e, 0x64] := by decide
  have hd : closeTag.data.toList = [0x63, 0x6c, 0x6f, 0x73, 0x65] := by decide
  rw [hf, hd] at hz
  have h1 := congrArg (List.take 1) hz
  simp at h1

/-- Tagging is injective in the message: equal tagged strings force equal
untagged messages.  This is the structural message-binding half that does not
need any cryptographic assumption. -/
theorem fundingTag_message_injective {m₁ m₂ : ByteArray}
    (h : fundingTag ++ m₁ = fundingTag ++ m₂) : m₁ = m₂ :=
  append_left_cancel h

/-- Tagging is injective in the message for the commitment domain. -/
theorem commitmentTag_message_injective {m₁ m₂ : ByteArray}
    (h : commitmentTag ++ m₁ = commitmentTag ++ m₂) : m₁ = m₂ :=
  append_left_cancel h

/-- Tagging is injective in the message for the close domain. -/
theorem closeTag_message_injective {m₁ m₂ : ByteArray}
    (h : closeTag ++ m₁ = closeTag ++ m₂) : m₁ = m₂ :=
  append_left_cancel h

/-! ## 3. The signature representation parser

BOLT 1 transmits a compact 64-byte signature; BOLT 3 witness stacks carry a
DER body plus a sighash byte, budgeted at 71 bytes and at most 73 (BOLT 3
§Transaction Weight).  The wave-A model has no parser, so this module defines
one as a total `Bool` predicate.  Only the envelope is checked: the
`SEQUENCE` tag, the declared content length, and the leading INTEGER tag.
The DER body itself is an explicit obligation. -/

/-- Byte lookup on a `ByteArray`, total in the index. -/
def byteAt (b : ByteArray) (i : Nat) : Option UInt8 :=
  b.data[i]?

/-- All-zero test vector of a given length. -/
def zeros (n : Nat) : ByteArray :=
  ByteArray.mk (List.replicate n (0 : UInt8)).toArray

/-- The DER envelope of a BOLT 3 witness signature: `0x30 <len> 0x02 ...`,
with the declared length equal to `size - 3` because one trailing byte is the
sighash type.  Length must be 71--73 bytes. -/
def derEnvelope (b : ByteArray) : Bool :=
  decide (71 ≤ b.size) &&
    (decide (b.size ≤ 73) &&
      ((byteAt b 0 == some 0x30) &&
        ((byteAt b 1 == some (UInt8.ofNat (b.size - 3))) &&
          (byteAt b 2 == some 0x02))))

/-- The model's wire-signature predicate: the compact 64-byte form or a
71--73-byte DER envelope. -/
def wireSigOK (b : ByteArray) : Bool :=
  (b.size == 64) || derEnvelope b

/-- Envelope acceptance implies the BOLT 3 witness-size window. -/
theorem derEnvelope_size {b : ByteArray} (h : derEnvelope b = true) :
    71 ≤ b.size ∧ b.size ≤ 73 := by
  unfold derEnvelope at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hlo, h⟩ := h
  rw [Bool.and_eq_true] at h
  obtain ⟨hhi, _⟩ := h
  rw [decide_eq_true_eq] at hlo hhi
  exact ⟨hlo, hhi⟩

/-- Envelope acceptance exposes the three parsed header bytes. -/
theorem derEnvelope_header {b : ByteArray} (h : derEnvelope b = true) :
    byteAt b 0 = some 0x30 ∧
      byteAt b 1 = some (UInt8.ofNat (b.size - 3)) ∧
      byteAt b 2 = some 0x02 := by
  unfold derEnvelope at h
  rw [Bool.and_eq_true] at h
  obtain ⟨_, h⟩ := h
  rw [Bool.and_eq_true] at h
  obtain ⟨_, h⟩ := h
  rw [Bool.and_eq_true] at h
  obtain ⟨h0, h⟩ := h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  exact ⟨(beq_iff_eq).mp h0, (beq_iff_eq).mp h1, (beq_iff_eq).mp h2⟩

/-- **Parser characterisation.**  A signature is accepted exactly when it is
the 64-byte compact form or passes the DER envelope predicate. -/
theorem wireSigOK_iff {b : ByteArray} :
    wireSigOK b = true ↔ b.size = 64 ∨ derEnvelope b = true := by
  unfold wireSigOK
  rw [Bool.or_eq_true]
  constructor
  · rintro (h | h)
    · exact Or.inl ((beq_iff_eq).mp h)
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl ((beq_iff_eq).mpr h)
    · exact Or.inr h

/-- **Only two wire shapes are accepted.**  Every accepted representation is
either 64 bytes or lies in 71--73 bytes; 65--70 and 74+ are rejected. -/
theorem wireSigOK_size {b : ByteArray} (h : wireSigOK b = true) :
    b.size = 64 ∨ (71 ≤ b.size ∧ b.size ≤ 73) := by
  rcases (wireSigOK_iff).mp h with hc | hd
  · exact Or.inl hc
  · exact Or.inr (derEnvelope_size hd)

/-- Compact 64-byte signatures are accepted (BOLT 1 wire type). -/
theorem wireSigOK_accepts_compact64 : wireSigOK (zeros 64) = true := by decide

/-- A well-formed 71-byte witness signature (33-byte `r`, 31-byte `s`, one
sighash byte) is accepted; the parser is not vacuous. -/
def derSig71 : ByteArray :=
  ByteArray.mk
    ((0x30 :: 0x44 :: 0x02 :: 0x21 ::
        (List.replicate 33 (0 : UInt8) ++
          (0x02 :: 0x1f ::
            (List.replicate 31 (0 : UInt8) ++ [0x01])))).toArray)

/-- The 71-byte test vector passes the envelope parser. -/
theorem derEnvelope_accepts_derSig71 : derEnvelope derSig71 = true := by decide

/-- The 71-byte test vector passes the wire predicate. -/
theorem wireSigOK_accepts_derSig71 : wireSigOK derSig71 = true := by decide

/-- 70 bytes are rejected: a DER body without the sighash byte is not a BOLT 3
witness signature. -/
theorem wireSigOK_rejects_70 : wireSigOK (zeros 70) = false := by decide

/-- 65 bytes are rejected. -/
theorem wireSigOK_rejects_65 : wireSigOK (zeros 65) = false := by decide

/-- 74 bytes are rejected: above the BOLT 3 maximum of 73. -/
theorem wireSigOK_rejects_74 : wireSigOK (zeros 74) = false := by decide

/-- The parser also rejects a 71-byte string that is not DER-shaped, so
acceptance is not merely a length test. -/
theorem wireSigOK_rejects_71_nonDER : wireSigOK (zeros 71) = false := by decide

/-! ## 4. Gating verification on the parser

The wave-A `verifyFunding` does not look at the representation, since
`ecdsaVerify` is opaque.  The checked predicates below make the parser a
precondition, which is the strongest form the model can express: a malformed
signature is rejected without consulting the primitive. -/

/-- Funding verification with the wire representation checked first. -/
def verifyFundingChecked (M : PrimitiveModel) (pk : PubKey) (msg : ByteArray)
    (sig : EcdsaSig) : Bool :=
  wireSigOK sig.bytes && verifyFunding M pk msg sig

/-- Commitment verification with the wire representation checked first. -/
def verifyCommitmentChecked (M : PrimitiveModel) (pk : PubKey) (msg : ByteArray)
    (sig : EcdsaSig) : Bool :=
  wireSigOK sig.bytes && verifyCommitment M pk msg sig

/-- Close verification with the wire representation checked first. -/
def verifyCloseChecked (M : PrimitiveModel) (pk : PubKey) (msg : ByteArray)
    (sig : EcdsaSig) : Bool :=
  wireSigOK sig.bytes && verifyClose M pk msg sig

/-- The gated predicate accepts exactly when the parser accepts and the
tagged signature verifies. -/
theorem verifyFundingChecked_iff (M : PrimitiveModel) (pk : PubKey)
    (msg : ByteArray) (sig : EcdsaSig) :
    verifyFundingChecked M pk msg sig = true ↔
      wireSigOK sig.bytes = true ∧ verifyFunding M pk msg sig = true := by
  unfold verifyFundingChecked
  rw [Bool.and_eq_true]

/-- Gated acceptance implies the representation passed the parser. -/
theorem verifyFundingChecked_requires_wire (M : PrimitiveModel) (pk : PubKey)
    (msg : ByteArray) (sig : EcdsaSig)
    (h : verifyFundingChecked M pk msg sig = true) : wireSigOK sig.bytes = true :=
  ((verifyFundingChecked_iff M pk msg sig).mp h).1

/-- Gated acceptance implies the underlying ECDSA verification succeeded. -/
theorem verifyFundingChecked_sound (M : PrimitiveModel) (pk : PubKey)
    (msg : ByteArray) (sig : EcdsaSig)
    (h : verifyFundingChecked M pk msg sig = true) :
    verifyFunding M pk msg sig = true :=
  ((verifyFundingChecked_iff M pk msg sig).mp h).2

/-- **Malformed representations never verify.**  A 70-byte signature is
rejected for every model, key, and message, without any cryptographic
assumption. -/
theorem verifyFundingChecked_rejects_70 (M : PrimitiveModel) (pk : PubKey)
    (msg : ByteArray) :
    verifyFundingChecked M pk msg ⟨zeros 70⟩ = false := by
  have h : wireSigOK (⟨zeros 70⟩ : EcdsaSig).bytes = false := wireSigOK_rejects_70
  simp [verifyFundingChecked, h]

/-- The same rejection holds for the commitment domain. -/
theorem verifyCommitmentChecked_rejects_70 (M : PrimitiveModel) (pk : PubKey)
    (msg : ByteArray) :
    verifyCommitmentChecked M pk msg ⟨zeros 70⟩ = false := by
  have h : wireSigOK (⟨zeros 70⟩ : EcdsaSig).bytes = false := wireSigOK_rejects_70
  simp [verifyCommitmentChecked, h]

/-! ## 5. Conditional domain separation

Everything in this section takes the model's `AssumesEufCma` field as an
explicit hypothesis.  Nothing here asserts unforgeability; the conclusions are
conditional message-binding facts. -/

/-- **No funding-to-commitment reuse.**  A signature verifying as a funding
signature and as a commitment signature would identify two prefix-free tagged
strings, for any pair of untagged messages. -/
theorem no_cross_domain_reuse_funding_commitment (M : PrimitiveModel)
    (h : AssumesEufCma M) {pk : PubKey} {msg₁ msg₂ : ByteArray}
    {sig : EcdsaSig} (hf : verifyFunding M pk msg₁ sig = true)
    (hc : verifyCommitment M pk msg₂ sig = true) : False := by
  have ht : fundingTag ++ msg₁ = commitmentTag ++ msg₂ :=
    (assumesEufCma_ecdsa M h) pk _ _ sig hf hc
  exact fundingTag_commitmentTag_prefixFree msg₁ msg₂ ht

/-- **No commitment-to-close reuse.** -/
theorem no_cross_domain_reuse_commitment_close (M : PrimitiveModel)
    (h : AssumesEufCma M) {pk : PubKey} {msg₁ msg₂ : ByteArray}
    {sig : EcdsaSig} (hc : verifyCommitment M pk msg₁ sig = true)
    (hcl : verifyClose M pk msg₂ sig = true) : False := by
  have ht : commitmentTag ++ msg₁ = closeTag ++ msg₂ :=
    (assumesEufCma_ecdsa M h) pk _ _ sig hc hcl
  exact commitmentTag_closeTag_prefixFree msg₁ msg₂ ht

/-- **No funding-to-close reuse.** -/
theorem no_cross_domain_reuse_funding_close (M : PrimitiveModel)
    (h : AssumesEufCma M) {pk : PubKey} {msg₁ msg₂ : ByteArray}
    {sig : EcdsaSig} (hf : verifyFunding M pk msg₁ sig = true)
    (hcl : verifyClose M pk msg₂ sig = true) : False := by
  have ht : fundingTag ++ msg₁ = closeTag ++ msg₂ :=
    (assumesEufCma_ecdsa M h) pk _ _ sig hf hcl
  exact fundingTag_closeTag_prefixFree msg₁ msg₂ ht

/-- **Reuse fails, not merely "does not succeed".**  Given a funding signature
for one message, the same signature is *false* in the commitment domain under
the same key, for every message. -/
theorem verifyCommitment_eq_false_of_verifyFunding (M : PrimitiveModel)
    (h : AssumesEufCma M) {pk : PubKey} {msg₁ msg₂ : ByteArray}
    {sig : EcdsaSig} (hf : verifyFunding M pk msg₁ sig = true) :
    verifyCommitment M pk msg₂ sig = false := by
  cases hc : verifyCommitment M pk msg₂ sig with
  | false => rfl
  | true =>
      exact (no_cross_domain_reuse_funding_commitment M h hf hc).elim

/-- **Reuse fails for the close domain as well.** -/
theorem verifyClose_eq_false_of_verifyFunding (M : PrimitiveModel)
    (h : AssumesEufCma M) {pk : PubKey} {msg₁ msg₂ : ByteArray}
    {sig : EcdsaSig} (hf : verifyFunding M pk msg₁ sig = true) :
    verifyClose M pk msg₂ sig = false := by
  cases hcl : verifyClose M pk msg₂ sig with
  | false => rfl
  | true =>
      exact (no_cross_domain_reuse_funding_close M h hf hcl).elim

/-- **A changed message cannot reuse a signature.**  Within one domain, a
signature valid for `msg₁` cannot also be valid for a distinct `msg₂`. -/
theorem verifyFunding_distinct_messages (M : PrimitiveModel)
    (h : EufCma M.ecdsaVerify) {pk : PubKey} {msg₁ msg₂ : ByteArray}
    {sig : EcdsaSig} (hne : msg₁ ≠ msg₂) :
    ¬ (verifyFunding M pk msg₁ sig = true ∧
        verifyFunding M pk msg₂ sig = true) := by
  rintro ⟨h1, h2⟩
  exact hne (verifyFunding_message_bound M h h1 h2)

/-! ## 6. Key changes need an extra assumption

`EufCma` as defined in `Crypto.Model` quantifies the key but only binds the
message: a verifier may accept the same signature for the same message under
two different keys.  The key-change theorem is therefore stated under an
explicit `KeyBinding` hypothesis, and the separation results below show that
this hypothesis is not a consequence of `EufCma`. -/

/-- Explicit key binding: success under two keys for one message and one
signature forces the keys to be equal.  This is *not* the `EufCma` field. -/
def KeyBinding {Sig : Type} (verify : PubKey → ByteArray → Sig → Bool) : Prop :=
  ∀ (pk₁ pk₂ : PubKey) (m : ByteArray) (s : Sig),
    verify pk₁ m s = true → verify pk₂ m s = true → pk₁ = pk₂

/-- **A changed key changes the claim, conditionally.**  Under the extra
`KeyBinding` hypothesis, a funding signature cannot verify under two keys for
the same message. -/
theorem verifyFunding_key_change_bound (M : PrimitiveModel)
    (h : KeyBinding M.ecdsaVerify) {pk₁ pk₂ : PubKey} {msg : ByteArray}
    {sig : EcdsaSig} (h₁ : verifyFunding M pk₁ msg sig = true)
    (h₂ : verifyFunding M pk₂ msg sig = true) : pk₁ = pk₂ :=
  h pk₁ pk₂ (fundingTag ++ msg) sig h₁ h₂

/-- The all-accepting verifier: a `Bool`-valued function that ignores its
arguments. -/
def acceptAllVerify : PubKey → ByteArray → EcdsaSig → Bool :=
  fun _ _ _ => true

/-- **`AssumesEufCma` is not vacuous.**  The all-accepting verifier satisfies
no message binding, so the field carries real content and must be assumed. -/
theorem eufCma_not_automatic : ¬ EufCma acceptAllVerify := by
  intro h
  have hEq : (ByteArray.empty : ByteArray) = ByteArray.mk #[0x00] :=
    h ⟨ByteArray.empty⟩ ByteArray.empty (ByteArray.mk #[0x00])
      ⟨ByteArray.empty⟩ rfl rfl
  have hs : ByteArray.empty.size = (ByteArray.mk #[0x00]).size :=
    congrArg ByteArray.size hEq
  exact absurd hs (by decide)

/-- No `Bool`-valued verifier is automatically `EufCma`. -/
theorem not_all_verify_eufCma :
    ¬ (∀ verify : PubKey → ByteArray → EcdsaSig → Bool, EufCma verify) :=
  fun h => eufCma_not_automatic (h acceptAllVerify)

/-- A verifier that accepts a single fixed message and ignores the key. -/
def singleMessageVerify (m₀ : ByteArray) : PubKey → ByteArray → EcdsaSig → Bool :=
  fun _ m _ => decide (m = m₀)

/-- The single-message verifier is `EufCma`: two accepted messages are both
`m₀`. -/
theorem eufCma_singleMessage (m₀ : ByteArray) :
    EufCma (singleMessageVerify m₀) := by
  intro pk m₁ m₂ s h₁ h₂
  simp only [singleMessageVerify, decide_eq_true_eq] at h₁ h₂
  rw [h₁, h₂]

/-- **`EufCma` does not imply key binding.**  The single-message verifier is
`EufCma` and accepts under two distinct public keys, so key binding must be an
independent hypothesis. -/
theorem eufCma_not_keyBinding :
    ¬ KeyBinding (singleMessageVerify ByteArray.empty) := by
  intro h
  have hEq : (⟨ByteArray.empty⟩ : PubKey) = ⟨ByteArray.mk #[0x00]⟩ :=
    h ⟨ByteArray.empty⟩ ⟨ByteArray.mk #[0x00]⟩ ByteArray.empty ⟨ByteArray.empty⟩
      (by decide) (by decide)
  have hs : (⟨ByteArray.empty⟩ : PubKey).bytes.size =
      (⟨ByteArray.mk #[0x00]⟩ : PubKey).bytes.size :=
    congrArg (fun p : PubKey => p.bytes.size) hEq
  exact absurd hs (by decide)

/-! ## 7. The full DER body: explicit obligations

The envelope predicate above checks only the `SEQUENCE` tag, the declared
length, and the leading `INTEGER` tag.  A real DER decoder additionally
checks both INTEGER headers, their lengths, and the absence of trailing
bytes.  `derFullOK` writes that shape down so the gap is formal rather than
prose; its byte-arithmetic lemmas are the module's open obligations. -/

/-- Full structural DER shape: `30 <len> 02 <rLen> r 02 <sLen> s <sighash>`
with both INTEGER lengths positive and the declared length consistent with
the total size.  One trailing byte (the sighash type) is required by the
BOLT 3 witness encoding. -/
def derFullOK (b : ByteArray) : Bool :=
  (byteAt b 0 == some 0x30) &&
  (byteAt b 1 == some (UInt8.ofNat (b.size - 3))) &&
  (byteAt b 2 == some 0x02) &&
  (match byteAt b 3 with
   | some rLen =>
       decide (1 ≤ rLen.toNat) &&
       (byteAt b (4 + rLen.toNat) == some 0x02) &&
       (match byteAt b (5 + rLen.toNat) with
        | some sLen =>
            decide (1 ≤ sLen.toNat) &&
            decide (rLen.toNat + sLen.toNat + 7 = b.size)
        | none => false)
   | none => false)

/-- The 71-byte test vector also passes the full structural parser. -/
theorem derFullOK_accepts_derSig71 : derFullOK derSig71 = true := by decide

/-- **Obligation.**  A string accepted by the full DER parser, and inside the
BOLT 3 witness-size window, is accepted by the envelope-based wire predicate.
This is the soundness direction of the parser refinement; it is true by the
shape of `derFullOK` and the pending work is the byte-offset arithmetic. -/
theorem derFullOK_imp_wireSigOK (b : ByteArray) (h : derFullOK b = true)
    (hlo : 71 ≤ b.size) (hhi : b.size ≤ 73) : wireSigOK b = true := by
  -- OBLIGATION: LN-ECDSA-001 full DER body acceptance implies the envelope predicate within 71--73 bytes
  sorry

/-- **Obligation.**  A full DER parse determines the two INTEGER lengths, and
they partition the byte string: `size = 7 + rLen + sLen` (two INTEGER tags,
both lengths, the `SEQUENCE` header, and one sighash byte). -/
theorem derFullOK_length_exact (b : ByteArray) (h : derFullOK b = true) :
    ∃ rLen sLen : Nat, b.size = 7 + rLen + sLen := by
  -- OBLIGATION: LN-ECDSA-002 a full DER parse fixes the two INTEGER lengths and their sum plus the sighash byte
  sorry

/-- The `SEQUENCE` length byte of the 71-byte test vector is `0x44 = 68`,
i.e. `size - 3`: one byte is the sighash type, which is outside the DER body. -/
theorem derSig71_length_byte : byteAt derSig71 1 = some 0x44 := by decide

/-- **Compact acceptance is length-only.**  Every 64-byte string passes
`wireSigOK`, including an all-zero `r`/`s`; scalar-range validation is
delegated entirely to the opaque `ecdsaVerify`.  This records the modelling
gap as a checked fact rather than a claim of validity. -/
theorem wireSigOK_accepts_any_64 (b : ByteArray) (h : b.size = 64) :
    wireSigOK b = true :=
  (wireSigOK_iff).mpr (Or.inl h)

end LnLean.Crypto
