/-
# Retarget candidates for the crypto catalog rows LN-CR-001/002/003

The three rows currently name primitive model *fields* rather than theorem
declarations:

* `LN-CR-001` names `LnLean.Crypto.Hash.sha256`;
* `LN-CR-002` names `LnLean.Crypto.Sig.ecdsaVerify`;
* `LN-CR-003` names `LnLean.Crypto.Hash.hmacSha256`.

`sha256`, `ecdsaVerify`, and `hmacSha256` are fields of `PrimitiveModel`; the
namespaces `LnLean.Crypto.Hash` and `LnLean.Crypto.Sig` contain no declarations
with those exact names.  The rows therefore cannot be promoted as written.  This
module states the strongest faithful standalone contracts available from the
current model, without strengthening an assumption, adding an axiom, or
asserting a false global cryptographic claim.

**LN-CR-001.**  The English claim has a structural half and a conditional half.
`PrimitiveModel.paymentHashOf` is definitionally `digest32 (M.sha256 pre.bytes)`,
and `sha256_size` makes `digest32` the identity on every digest, so a
constructed payment hash is literally a SHA-256 image with no assumption.  The
commitment half — a payment hash determines at most one valid 32-byte preimage
— is conditional on C1, the model's 32-byte-domain `CollisionResistant
M.sha256`.  It is not the false global claim that SHA-256 is injective on all
byte strings (`PreimageResistant` is refuted by
`LnLean.Proofs.Crypto.Sha256Props.preimageResistant_vacuous`).  Nor is every
arbitrary `PaymentHash` value an output: `PaymentHash` is a bare byte-array
wrapper and the protocol well-formedness predicate does not check the range
(see `LnLean.Proofs.WaveD.D05.waveD_d05_wellFormed_message_with_non_output_hash`).

**LN-CR-002.**  C3 (`EufCma M.ecdsaVerify`) is exactly message binding for one
key and one signature.  The faithful consequence is that a verified
commitment-domain signature determines a unique untagged message and cannot be
replayed in the funding or close domain.  It is *not* the unconditional claim
that an honestly produced counterparty signature is accepted: `PrimitiveModel`
has no signing operation and no signing-correctness law, so that direction
needs the explicit `SigningCompleteness` hypothesis isolated in
`LnLean.Proofs.WaveE.E06`.  C3 also does not bind a signature to a key; key
attribution needs the separate `KeyBinding` hypothesis (and E06 proves C3 does
not imply it).

**LN-CR-003.**  C8 is a finite-execution admission, not a global PRF statement.
`HmacBindsOn M.hmacSha256 mu msgs` binds equal tags on the finite message list
of one onion execution, and is satisfiable whenever those messages have
pairwise distinct tags.  The global form `HmacPrf M.hmacSha256` is refuted for
every fixed key by `LnLean.Proofs.WaveD.D07.hmacPrf_vacuous`.  The faithful
contract therefore combines the structural 32-byte tag width with finite
`HmacBindsOn` message binding.

**BOLT sections.**  BOLT 1 §Fundamental Types (32-byte `sha256` and
`signature` wire types), BOLT 2 §Adding an HTLC and §Removing an HTLC,
BOLT 3 §Commitment Transaction Construction, and BOLT 4 §Packet Structure and
§Onion Decryption.

**Not modelled.**  Concrete SHA-256 compression, secp256k1 group arithmetic,
ECDSA signing, DER encoding, BOLT 3 sighash serialisation, BIP-340 tagged
hashing, the Sphinx key schedule, and computational security games.  All
statements below are exact algebraic consequences of the model's explicit
fields or of their named conditional hypotheses.
-/

import LnLean.Crypto.Hash
import LnLean.Crypto.Model
import LnLean.Crypto.Sig
import LnLean.Proofs.WaveD.D07

set_option autoImplicit false

namespace LnLean.Crypto.Hash

open LnLean
open LnLean.Crypto

/-! ## LN-CR-001: SHA-256 output-ness and C1-conditional commitment -/

/-- **Payment-hash contract under C1.**  This packages the two faithful halves
of "payment hashes are SHA-256 outputs":

1. every canonical payment hash is exactly the SHA-256 image of its preimage,
   with no cryptographic hypothesis;
2. every hash lock opened by a preimage is in the range of `M.sha256`;
3. two valid 32-byte preimages that open the same payment hash are equal;
4. two valid 32-byte preimages with the same canonical payment hash are equal.

Parts 3 and 4 are conditional on C1 (`CollisionResistant M.sha256`).  The
statement deliberately does not quantify over an arbitrary `PaymentHash`, since
the model does not put the range check in `wellFormed`. -/
theorem paymentHash_sha256_contract (M : PrimitiveModel)
    (hc : CollisionResistant M.sha256) :
    (∀ pre : Preimage, (M.paymentHashOf pre).bytes = M.sha256 pre.bytes) ∧
    (∀ {ph : PaymentHash} {pre : Preimage},
      opensTo M ph pre → ∃ b : ByteArray, M.sha256 b = ph.bytes) ∧
    (∀ {ph : PaymentHash} {p q : Preimage},
      opensTo M ph p → opensTo M ph q →
      p.Valid → q.Valid → p = q) ∧
    (∀ {p q : Preimage},
      p.Valid → q.Valid →
      M.paymentHashOf p = M.paymentHashOf q → p = q) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro pre
    unfold PrimitiveModel.paymentHashOf
    simp [PrimitiveModel.digest32_of_size (M.sha256_size pre.bytes)]
  · intro ph pre hopen
    refine ⟨pre.bytes, ?_⟩
    unfold opensTo at hopen
    rw [PrimitiveModel.digest32_of_size (M.sha256_size pre.bytes)] at hopen
    exact hopen
  · intro ph p q hp hq hpv hqv
    exact preimage_unique M hc hp hq hpv hqv
  · intro p q hp hq hph
    exact paymentHash_commits M hc hp hq hph

/-- **Standalone C1-conditional preimage uniqueness.**  A payment hash has at
most one valid 32-byte preimage.  This is the commitment content consumed by
BOLT 2's `update_fulfill_htlc` check. -/
theorem paymentHash_opensTo_unique (M : PrimitiveModel)
    (hc : CollisionResistant M.sha256) {ph : PaymentHash} {p q : Preimage}
    (hp : opensTo M ph p) (hq : opensTo M ph q)
    (hpv : p.Valid) (hqv : q.Valid) : p = q :=
  preimage_unique M hc hp hq hpv hqv

/-- **Contrapositive commitment form.**  Distinct valid preimages have distinct
canonical payment hashes under C1.  This is the direction an HTLC sender uses
to prevent one payment hash from committing to two secrets. -/
theorem paymentHash_sha256_distinct (M : PrimitiveModel)
    (hc : CollisionResistant M.sha256) {p q : Preimage}
    (hp : p.Valid) (hq : q.Valid) (hne : p ≠ q) :
    M.paymentHashOf p ≠ M.paymentHashOf q := by
  intro hph
  exact hne (paymentHash_commits M hc hp hq hph)

end LnLean.Crypto.Hash

namespace LnLean.Crypto.Sig

open LnLean
open LnLean.Crypto

/-! ## LN-CR-002: C3-conditional commitment-signature binding -/

/-- **Commitment-signature contract under C3.**  For a fixed public key and
signature, acceptance in the commitment domain:

1. determines the untagged message uniquely (C3 message binding);
2. is incompatible with acceptance of the same signature and untagged message
   in the funding domain;
3. is incompatible with acceptance of the same signature and untagged message
   in the close domain.

The public key is a parameter: at the channel level it is instantiated with the
counterparty funding key (`LnLean.Proofs.WaveE.E06.counterpartyFundingKey`).
The statement does not assert the converse "every honest signature verifies";
that needs a signing function and a correctness law, neither of which is a field
of `PrimitiveModel` (see `WaveE.E06.SigningCompleteness`).  It also does not
attribute acceptance to the counterparty rather than an arbitrary key; that
needs `WaveE.E06.KeyBinding`, which C3 does not imply. -/
theorem commitmentSig_contract (M : PrimitiveModel)
    (h : EufCma M.ecdsaVerify) (pk : PubKey) (sig : EcdsaSig) :
    (∀ {m₁ m₂ : ByteArray},
      verifyCommitment M pk m₁ sig = true →
      verifyCommitment M pk m₂ sig = true → m₁ = m₂) ∧
    (∀ {m : ByteArray},
      verifyCommitment M pk m sig = true →
      verifyFunding M pk m sig = false) ∧
    (∀ {m : ByteArray},
      verifyCommitment M pk m sig = true →
      verifyClose M pk m sig = false) := by
  refine ⟨?_, ?_, ?_⟩
  · intro m₁ m₂ h₁ h₂
    exact verifyCommitment_message_bound M h h₁ h₂
  · intro m hc
    cases hf : verifyFunding M pk m sig with
    | false => rfl
    | true => exact (verifyFunding_not_verifyCommitment M h hf hc).elim
  · intro m hc
    cases hclose : verifyClose M pk m sig with
    | false => rfl
    | true => exact (verifyCommitment_not_verifyClose M h hc hclose).elim

/-- **Standalone C3-conditional commitment message binding.**  One signature
cannot verify for two distinct untagged messages under the same public key in
the commitment domain. -/
theorem commitmentSig_binds_message (M : PrimitiveModel)
    (h : EufCma M.ecdsaVerify) {pk : PubKey} {m₁ m₂ : ByteArray}
    {sig : EcdsaSig}
    (h₁ : verifyCommitment M pk m₁ sig = true)
    (h₂ : verifyCommitment M pk m₂ sig = true) : m₁ = m₂ :=
  verifyCommitment_message_bound M h h₁ h₂

end LnLean.Crypto.Sig

namespace LnLean.Crypto.Hash

open LnLean
open LnLean.Crypto
open LnLean.Proofs.WaveD.D07

/-! ## LN-CR-003: HMAC-SHA256 tag width and finite C8 binding -/

/-- **Onion HMAC contract.**  For one onion execution, the BOLT 4 tag is a
32-byte HMAC-SHA256 value, and under the finite-execution C8 admission
`HmacBindsOn M.hmacSha256 mu msgs` an authentic tag determines the
`hop_payloads` value uniquely among the messages of that execution (with the
associated data held fixed).

This is deliberately not a global claim that `M.hmacSha256 mu` is injective on
all byte strings.  That claim is false for every fixed key of a 32-byte-output
HMAC; `LnLean.Proofs.WaveD.D07.hmacPrf_vacuous` proves the negation of
`HmacPrf`. -/
theorem onionHmacTag_size_and_bindsOn (M : PrimitiveModel)
    {mu : ByteArray} {msgs : List ByteArray}
    (hb : HmacBindsOn M.hmacSha256 mu msgs)
    (hopPayloads associatedData : ByteArray)
    (hmem : hopPayloads ++ associatedData ∈ msgs) :
    (onionHmacTag M mu hopPayloads associatedData).size = 32 ∧
    (∀ hopPayloads' : ByteArray,
      hopPayloads' ++ associatedData ∈ msgs →
      onionHmacTag M mu hopPayloads' associatedData =
        onionHmacTag M mu hopPayloads associatedData →
      hopPayloads' = hopPayloads) := by
  refine ⟨waveD_d07_onionHmacTag_size_eq_32 M mu hopPayloads associatedData, ?_⟩
  intro hopPayloads' hmem' htag
  apply waveD_d07_onionHmacTag_payloads_unique M hb hmem' hmem
  exact htag

end LnLean.Crypto.Hash
