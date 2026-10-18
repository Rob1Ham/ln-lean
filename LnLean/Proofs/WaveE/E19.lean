/-
# E19 — `funding_signed` carries a valid signature over the funding transaction

## English claim

BOLT 2 §"The `funding_signed` Message" says that the fundee's
`funding_signed` message carries its signature for the funding transaction;
the funder checks that signature before broadcasting the funding transaction.
LDK's receive-side handler at `lightning/src/ln/channel.rs:2107` is the
corresponding `internal_funding_signed` path.

## What the model provides, and what it does not

The wave-A model has:

* `FundingSigned` with a final `channelId` and an `EcdsaSig`
  (`LnLean.Protocol.Messages`), and `wellFormed` checks only the channel-id
  size and that the signature is at most 73 bytes;
* the funding-signature domain `LnLean.Crypto.verifyFunding`, which applies
  the model's opaque `ecdsaVerify` to `fundingTag ++ fundingTx`;
* `EufCma` as a field of `PrimitiveModel`, i.e. message binding is an
  explicit hypothesis.

The model does **not** have:

* a field in `FundingSigned` that names the funding transaction or its
  digest, so the transaction bytes must be supplied as an explicit
  parameter of the validity predicate below;
* a signing function, a signing discipline, or a verification step in
  `handshakeStep` (`HandshakeEvent.sendFundingSigned` carries no message);
* a `txid` bridge from funding-transaction bytes to `channel_id`.

Consequently the literal unconditional reading ("every `FundingSigned` /
every reachable `funding_signed` event carries a valid signature") is false
in the model.  This module gives:

1. the faithful validity predicate `fundingSignedValid`, which takes the
   verifier model, the funding key, the funding-transaction bytes, and the
   message;
2. its exact characterization, message-binding theorem, and cross-domain
   separation theorem under `EufCma`;
3. an exact characterization of `wellFormed` for `funding_signed`: it checks
   only the channel-id size and the signature length;
4. a mechanized counterexample: for every base primitive model, its
   reject-all-ECDSA variant has a `wellFormed`, wire-shaped
   `funding_signed` message that verifies for no key and no funding
   transaction.  This variant still satisfies the model's `EufCma` field
   (vacuously), so the missing ingredient is a model invariant/signing
   discipline, not the cryptographic assumption.

The obligation marker is next to the counterexample statement.
-/

import LnLean.Protocol.Handshake
import LnLean.Protocol.Laws
import LnLean.Protocol.Messages
import LnLean.Protocol.Peer
import LnLean.Crypto.Model
import LnLean.Crypto.Sig
import LnLean.Proofs.Crypto.EcdsaProps
import LnLean.Proofs.Protocol.HandshakeProps

namespace LnLean.Proofs.WaveE.E19

set_option autoImplicit false

open LnLean
open LnLean.Protocol
open LnLean.Crypto

/-- The funding-domain verification relation for a `funding_signed` message.
`fundingTx` is the byte string of the funding transaction that BOLT 2 says
was signed; it is an explicit parameter because `FundingSigned` has no field
for it. -/
def fundingSignedVerifies (M : PrimitiveModel) (fundingKey : PubKey)
    (fundingTx : ByteArray) (m : FundingSigned) : Prop :=
  verifyFunding M fundingKey fundingTx m.signature = true

/-- Faithful form of "`funding_signed` carries a valid signature over the
funding transaction": the signature has a BOLT wire shape (the checked
predicate from `LnLean.Proofs.Crypto.EcdsaProps`) and verifies in the
funding domain under the given funding key and funding-transaction bytes. -/
def fundingSignedValid (M : PrimitiveModel) (fundingKey : PubKey)
    (fundingTx : ByteArray) (m : FundingSigned) : Prop :=
  verifyFundingChecked M fundingKey fundingTx m.signature = true

/-! ## 1. Characterization and consequences -/

/-- `fundingSignedValid` is exactly wire-shape acceptance plus funding-domain
ECDSA verification.  This is the definitional bridge to the model's
`verifyFunding` predicate. -/
theorem waveE_e19_funding_signed_valid_iff (M : PrimitiveModel)
    (fundingKey : PubKey) (fundingTx : ByteArray) (m : FundingSigned) :
    fundingSignedValid M fundingKey fundingTx m ↔
      wireSigOK m.signature.bytes = true ∧
        fundingSignedVerifies M fundingKey fundingTx m :=
  verifyFundingChecked_iff M fundingKey fundingTx m.signature

/-- Validity passes the BOLT wire-shape parser. -/
theorem waveE_e19_funding_signed_valid_wire (M : PrimitiveModel)
    (fundingKey : PubKey) (fundingTx : ByteArray) (m : FundingSigned)
    (h : fundingSignedValid M fundingKey fundingTx m) :
    wireSigOK m.signature.bytes = true :=
  ((waveE_e19_funding_signed_valid_iff M fundingKey fundingTx m).mp h).1

/-- Validity implies acceptance by the model's funding verifier. -/
theorem waveE_e19_funding_signed_valid_sound (M : PrimitiveModel)
    (fundingKey : PubKey) (fundingTx : ByteArray) (m : FundingSigned)
    (h : fundingSignedValid M fundingKey fundingTx m) :
    fundingSignedVerifies M fundingKey fundingTx m :=
  ((waveE_e19_funding_signed_valid_iff M fundingKey fundingTx m).mp h).2

/-- A valid signature has one of the two BOLT wire shapes: the 64-byte
compact form or a 71--73-byte DER envelope.  In particular its size is at
most 73 bytes. -/
theorem waveE_e19_funding_signed_valid_sig_shape (M : PrimitiveModel)
    (fundingKey : PubKey) (fundingTx : ByteArray) (m : FundingSigned)
    (h : fundingSignedValid M fundingKey fundingTx m) :
    m.signature.bytes.size = 64 ∨
      (71 ≤ m.signature.bytes.size ∧ m.signature.bytes.size ≤ 73) :=
  wireSigOK_size (waveE_e19_funding_signed_valid_wire M fundingKey fundingTx m h)

/-- **Message binding.**  Under the model's ECDSA message-binding assumption,
a fixed key and signature can validate only one funding transaction. -/
theorem waveE_e19_funding_signed_valid_binds_tx (M : PrimitiveModel)
    (hM : EufCma M.ecdsaVerify) {fundingKey : PubKey} {tx₁ tx₂ : ByteArray}
    {m : FundingSigned}
    (h₁ : fundingSignedValid M fundingKey tx₁ m)
    (h₂ : fundingSignedValid M fundingKey tx₂ m) : tx₁ = tx₂ :=
  verifyFunding_message_bound M hM
    (waveE_e19_funding_signed_valid_sound M fundingKey tx₁ m h₁)
    (waveE_e19_funding_signed_valid_sound M fundingKey tx₂ m h₂)

/-- **No reuse as a commitment signature.**  A funding-domain signature
cannot also verify in the commitment domain, even for a different untagged
message.  This is the domain-separation consequence of the same ECDSA
assumption plus the prefix-free `fund` tag. -/
theorem waveE_e19_funding_signed_valid_not_commitment (M : PrimitiveModel)
    (hM : AssumesEufCma M) {fundingKey : PubKey} {fundingTx commitTx : ByteArray}
    {m : FundingSigned}
    (hv : fundingSignedValid M fundingKey fundingTx m)
    (hc : verifyCommitment M fundingKey commitTx m.signature = true) : False :=
  no_cross_domain_reuse_funding_commitment M hM
    (waveE_e19_funding_signed_valid_sound M fundingKey fundingTx m hv) hc

/-- **No reuse as a mutual-close signature.** -/
theorem waveE_e19_funding_signed_valid_not_close (M : PrimitiveModel)
    (hM : AssumesEufCma M) {fundingKey : PubKey} {fundingTx closeTx : ByteArray}
    {m : FundingSigned}
    (hv : fundingSignedValid M fundingKey fundingTx m)
    (hc : verifyClose M fundingKey closeTx m.signature = true) : False :=
  no_cross_domain_reuse_funding_close M hM
    (waveE_e19_funding_signed_valid_sound M fundingKey fundingTx m hv) hc

/-- **Transaction-id form.**  If a caller supplies a txid map `txidOf`, two
valid funding signatures over the same message and key pin the same txid.
The map is a parameter because the model has no SHA-256d / txid bridge. -/
theorem waveE_e19_funding_signed_valid_binds_txid (M : PrimitiveModel)
    (hM : EufCma M.ecdsaVerify) (txidOf : ByteArray → ByteArray)
    {fundingKey : PubKey} {tx₁ tx₂ : ByteArray} {m : FundingSigned}
    (h₁ : fundingSignedValid M fundingKey tx₁ m)
    (h₂ : fundingSignedValid M fundingKey tx₂ m) :
    txidOf tx₁ = txidOf tx₂ := by
  rw [waveE_e19_funding_signed_valid_binds_tx M hM h₁ h₂]

/-! ## 2. What `wellFormed` actually checks for `funding_signed` -/

/-- Exact characterization: a `funding_signed` message is `wellFormed` iff
its channel id is a 32-byte value and its signature is at most 73 bytes.
There is no cryptographic check in `wellFormed`. -/
theorem waveE_e19_funding_signed_wellFormed_iff (m : FundingSigned) :
    wellFormed (.fundingSigned m) ↔
      m.channelId.Valid ∧ m.signature.bytes.size ≤ 73 := by
  constructor
  · rintro ⟨_hlen, hids, hsigs, _hsem⟩
    refine ⟨hids.1 m.channelId rfl, ?_⟩
    exact hsigs m.signature (by simp [signatures])
  · rintro ⟨hid, hsig⟩
    unfold wellFormed idsValid sigsValid semanticOk
    refine ⟨?_, ?_, ?_, trivial⟩
    · simp [msgLength, sigLen]
      omega
    · constructor
      · intro c hc
        have hc' : m.channelId = c := by
          simpa [channelId?] using hc
        rw [← hc']
        exact hid
      · intro p hp
        simp [pubKeys] at hp
    · intro s hs
      simp only [signatures, List.mem_singleton] at hs
      subst hs
      exact hsig

/-- The length half of the characterization, exposed as a corollary. -/
theorem waveE_e19_funding_signed_wellFormed_sig_size (m : FundingSigned)
    (h : wellFormed (.fundingSigned m)) :
    m.signature.bytes.size ≤ 73 :=
  (waveE_e19_funding_signed_wellFormed_iff m).mp h |>.2

/-- The id half of the characterization, exposed as a corollary. -/
theorem waveE_e19_funding_signed_wellFormed_channelId (m : FundingSigned)
    (h : wellFormed (.fundingSigned m)) :
    m.channelId.Valid :=
  (waveE_e19_funding_signed_wellFormed_iff m).mp h |>.1

/-! ## 3. Counterexample: `wellFormed` and wire shape do not imply validity

`FundingSigned` is pure data.  `wellFormed` checks sizes only, and nothing in
`HandshakeState`/`handshakeStep` records the message payload.  The following
variant of any primitive model rejects every ECDSA signature, so even a
64-byte (wire-accepted) signature is not valid for any key or transaction.
The variant still satisfies `EufCma` vacuously. -/

/-- Replace a model's ECDSA verifier by the constant `false`.  `EufCma` for
the constant-false verifier is vacuous, so the structure remains a valid
`PrimitiveModel`. -/
def rejectAllEcdsa (M : PrimitiveModel) : PrimitiveModel where
  sha256 := M.sha256
  hash160 := M.hash160
  ecdsaVerify := fun _ _ _ => false
  schnorrVerify := M.schnorrVerify
  ecdh := M.ecdh
  hkdf := M.hkdf
  aeadSeal := M.aeadSeal
  aeadOpen := M.aeadOpen
  hmacSha256 := M.hmacSha256
  sha256_size := M.sha256_size
  hash160_size := M.hash160_size
  hmac_size := M.hmac_size
  sha256_collisionResistant := M.sha256_collisionResistant
  ecdsa_eufCma := by
    intro _pk _m₁ _m₂ _s h₁ _h₂
    exact absurd h₁ (by simp)
  schnorr_eufCma := M.schnorr_eufCma
  aead_indCca := M.aead_indCca
  hmac_prf := M.hmac_prf

/-- A 64-byte-zero signature passes the BOLT compact-signature parser. -/
def compactZeroSig : EcdsaSig := ⟨zeros 64⟩

/-- A `funding_signed` message with a valid-shaped channel id and the
compact zero signature.  It is well formed and wire-shaped, but carries no
cryptographic evidence at all. -/
def shapeOnlyFundingSigned : FundingSigned where
  channelId := ⟨zeros 32⟩
  signature := compactZeroSig

theorem waveE_e19_shapeOnly_wellFormed :
    wellFormed (.fundingSigned shapeOnlyFundingSigned) := by
  rw [waveE_e19_funding_signed_wellFormed_iff]
  refine ⟨?_, ?_⟩
  · show (zeros 32).size = 32
    decide
  · show (zeros 64).size ≤ 73
    decide

theorem waveE_e19_shapeOnly_wire :
    wireSigOK shapeOnlyFundingSigned.signature.bytes = true := by
  simpa [shapeOnlyFundingSigned, compactZeroSig] using wireSigOK_accepts_compact64

/-- The reject-all model falsifies the unconditional reading of the target:
a `wellFormed`, wire-shaped `funding_signed` message verifies for no key and
no funding transaction.  The model still satisfies the `EufCma` field. -/
theorem waveE_e19_shapeOnly_not_valid (M₀ : PrimitiveModel) :
    ∃ m : FundingSigned,
      wellFormed (.fundingSigned m) ∧
      wireSigOK m.signature.bytes = true ∧
      (∀ (pk : PubKey) (fundingTx : ByteArray),
        ¬ fundingSignedValid (rejectAllEcdsa M₀) pk fundingTx m) ∧
      EufCma (rejectAllEcdsa M₀).ecdsaVerify := by
  refine ⟨shapeOnlyFundingSigned, waveE_e19_shapeOnly_wellFormed,
    waveE_e19_shapeOnly_wire, ?_, (rejectAllEcdsa M₀).ecdsa_eufCma⟩
  intro pk fundingTx h
  -- `verifyFundingChecked` is `wireSigOK && verifyFunding`; the verifier is
  -- constantly false, so the conjunction cannot be true.
  simp [fundingSignedValid, verifyFundingChecked, verifyFunding,
    rejectAllEcdsa] at h

-- OBLIGATION: LN-WE-E19

/-- The literal target as a universal statement over all messages and models:
"every well-formed `funding_signed` carries a signature valid over its
funding transaction".  It is false in the current model (the transaction is
not even recorded in the message), as witnessed by
`waveE_e19_shapeOnly_not_valid`. -/
def fundingSignedAlwaysValid (m : FundingSigned) : Prop :=
  ∀ (M : PrimitiveModel) (fundingKey : PubKey) (fundingTx : ByteArray),
    fundingSignedValid M fundingKey fundingTx m

/-- The unconditional form is refuted by the reject-all model.  A signing
discipline or a `signed_funding_tx`/digest field is missing from the model;
`EufCma` alone does not supply it. -/
theorem waveE_e19_unconditional_form_false (M₀ : PrimitiveModel) :
    ∃ m : FundingSigned,
      wellFormed (.fundingSigned m) ∧ ¬ fundingSignedAlwaysValid m := by
  obtain ⟨m, hwf, _hwire, hnone, _hEuf⟩ := waveE_e19_shapeOnly_not_valid M₀
  refine ⟨m, hwf, ?_⟩
  intro hall
  exact hnone ⟨zeros 33⟩ (zeros 0) (hall (rejectAllEcdsa M₀) ⟨zeros 33⟩ (zeros 0))

/-! ## 4. The handshake transition carries no message payload -/

/-- `sendFundingSigned` is a nullary event.  `HandshakeEvent` has no field of
type `FundingSigned`, and the guard is a predicate on `HandshakeState` only,
so the transition cannot inspect (let alone verify) the signature.  This is
the formal statement of the missing signing discipline. -/
theorem waveE_e19_sendFundingSigned_payload_free (s : HandshakeState) :
    handshakeStep s .sendFundingSigned =
      (if s.canSendFundingSigned then
        some { s with fundingSignedSent := true } else none) := rfl

/-! ## 5. Conditional protocol-level form using the funding exchange -/

/-- If the `funding_signed` channel id is the final id derived from the
`funding_created` outpoint, and the message is valid over the transaction
whose txid that outpoint announces, then every other valid signature for the
same message and key is over a transaction with the same txid.

The `txidOf` parameter is the missing txid bridge; the model deliberately
does not compute BOLT 2's txid/sighash construction. -/
theorem waveE_e19_funding_created_valid_txid_agreement
    (M : PrimitiveModel) (hM : EufCma M.ecdsaVerify)
    (txidOf : ByteArray → ByteArray)
    {fc : FundingCreated} {m : FundingSigned} {fundingTx tx' : ByteArray}
    {fundingKey : PubKey}
    (hid : m.channelId = finalChannelId fc.outpoint)
    (htxid : fc.fundingTxid = txidOf fundingTx)
    (h : fundingSignedValid M fundingKey fundingTx m)
    (h' : fundingSignedValid M fundingKey tx' m) :
    m.channelId.bytes = txidOf tx' := by
  have htx : fundingTx = tx' :=
    waveE_e19_funding_signed_valid_binds_tx M hM h h'
  rw [hid, finalChannelId_bytes]
  simpa [FundingCreated.outpoint, htx] using htxid

end LnLean.Proofs.WaveE.E19
