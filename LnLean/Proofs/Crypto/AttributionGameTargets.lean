/-
# Registration/PoP game over the stored `accept_channel` payload (PR-01, wave 9)

**Catalog issue.**  `PR-01` (P1): `FundingSigningLaw` and `KeyBinding` are
hypotheses, and wave 8's `StoredAccept` records the received
`accept_channel` payload without turning the record into evidence that the
peer controls the advertised `funding_pubkey`.  This module specialises the
registration/proof-of-possession (PoP) game of
`LnLean.Proofs.WaveH.H22` to the actual `StoredAccept` state predicate of
`LnLean.Proofs.Crypto.KeyModelTargets`.

**What the module adds.**

1. `StoredRegistration` is the verifier-side game transcript over a stored
   payload: a `StoredAccept K seed s m` record, a verifier-issued challenge
   transcript `t` bound to `m.temporary_channel_id`, and `PopAccepted` under the
   stored `funding_pubkey`.
2. `register_of_storedRegistration` connects that state-level game to H22's
   executable `register`; a stored registration is exactly a successful
   verifier-side registration.
3. Under the game's extraction obligation `PopSound`, a stored registration
   yields a secret key owned for `m.fundingPubKey`
   (`stored_registration_owns_funding_key`) and the registered signer's funding
   signature attributes to exactly `m.fundingPubKey` under the unchanged
   `KeyBinding` hypothesis
   (`stored_registration_funding_attribution`).  This is the strongest
   attribution contract the symbolic model supports: it consumes the explicit
   generation link (`StoredAccept`), the PoP extraction law (`PopSound`), the
   signature-production hypothesis (`PopProducedBy`), and `KeyBinding`; no one
   of these is derived from `EufCma`.
4. `stored_pop_attribution` is the sharper signature-level form: if the stored
   payload advertises the seed's generated key and the challenge signature is
   exactly the seed's honest signature, then under `KeyBinding` every key that
   accepts that signature is the stored `funding_pubkey`.  The signature
   production hypothesis is explicit, because verification alone does not say
   which secret key produced a signature.
5. **Storage is not possession.**  `stored_payload_not_possession` keeps a
   payload-reachable state with a stored payload and an accepted PoP transcript
   in a full `EufCma` model, yet the same transcript also verifies under a
   second key that key generation cannot produce, and `PopSound` fails.  Thus
   neither storing the payload nor accepting a transcript is a proof of
   possession; the extraction law is the missing premise.
6. **Dropping `KeyBinding` breaks attribution.**  `stored_attribution_fails_without_keyBinding`
   gives a concrete full model and stored payload in which an honest funding
   signature verifies under a second key different from the stored
   `funding_pubkey`, while `KeyBinding` fails.  So the positive contract's
   `KeyBinding` hypothesis is necessary, not decorative.
7. `stored_registration_contract_nonvacuous` gives a concrete witness for the
   positive contract, so it is not vacuous.

**Totality / `FundingSigningLaw` boundary.**  The game uses the domain-scoped
`KeyModel.correctOn` law at the PoP message and at the funding message.  It
does **not** assume `KeyModel.Total` or a total `FundingSigningLaw`: the
totality tension mechanised by
`KeyModelTargets.fundingSigningLaw_sign_injective` remains exactly where it
was.  A deployment that needs completeness on every byte string must discharge
that obligation separately; this module only needs the two protocol domains it
names.  `PopSound` is an exact extraction law, not a computational reduction.

**Not modelled.**  secp256k1 arithmetic, nonce/seed entropy, challenge
freshness (kept as an explicit issue predicate in H22's `PopSoundOn`), transport
authentication, and a probabilistic adversary.  `PopSound` must be supplied by
a deployment; this module proves what follows from it and mechanises what fails
without it.

**BOLT sections.**  BOLT 2 §The `accept_channel` Message (type 33,
`funding_pubkey`, `temporary_channel_id`), §The `funding_created` Message and
§The `funding_signed` Message; BOLT 1 §Lightning Message Format (`signature`).
-/

import LnLean.Proofs.Crypto.AcceptPayloadTargets
import LnLean.Proofs.Crypto.KeyModelTargets
import LnLean.Proofs.WaveH.H21
import LnLean.Proofs.WaveH.H22

namespace LnLean.Proofs.Crypto.AttributionGameTargets

set_option autoImplicit false

open LnLean
open LnLean.Crypto
open LnLean.Crypto.KeyModel
open LnLean.Protocol
open LnLean.Protocol.Handshake
open LnLean.Bitcoin
open LnLean.Proofs.Crypto.KeyModelTargets
open LnLean.Proofs.Crypto.AcceptPayloadTargets

/-- The key-binding contract, re-exported under this module's namespace to
avoid the signature-layer `Crypto.KeyBinding` name.  It is the unchanged
`LnLean.Proofs.WaveE.E06.KeyBinding` definition. -/
abbrev KeyBinding (verify : PubKey → ByteArray → EcdsaSig → Bool) : Prop :=
  LnLean.Proofs.WaveE.E06.KeyBinding verify

/-! ## 1. The stored registration game -/

/-- The PoP transcript of H22, re-exported under this module's namespace.  It
contains the channel binding, the verifier-issued challenge and the signature
over `popTag ++ channelId ++ challenge`. -/
abbrev PopTranscript := LnLean.Proofs.WaveH.H22.PopTranscript

/-- The exact signed PoP message. -/
abbrev popMessage := LnLean.Proofs.WaveH.H22.popMessage

/-- Verification of a PoP transcript under an advertised key. -/
abbrev PopAccepted (M : PrimitiveModel) (pk : PubKey) (t : PopTranscript) : Prop :=
  LnLean.Proofs.WaveH.H22.PopAccepted M pk t

/-- The PoP extraction obligation: every accepted transcript on an issued
challenge yields a secret key that key generation pairs with the advertised
public key.  This is the exact algebraic form of the registration game's
knowledge-soundness requirement. -/
abbrev PopSound (M : PrimitiveModel) (K : KeyModel M) : Prop :=
  LnLean.Proofs.WaveH.H22.PopSound K

/-- An accepted registration over the *stored* handshake payload: the state
stores `m` and advertises the seed's generated key, the verifier-issued
transcript is bound to `m.temporary_channel_id`, and the PoP signature verifies
under `m.funding_pubkey`.  This is a game transcript, not a claim that the
verifier has extracted a secret key. -/
def StoredRegistration (M : PrimitiveModel) (K : KeyModel M)
    (seed : ByteArray) (s : HandshakeState) (m : AcceptChannel)
    (t : PopTranscript) : Prop :=
  StoredAccept K seed s m ∧
    t.channelId = m.temporaryChannelId.bytes ∧
    PopAccepted M m.fundingPubKey t

/-- The stored payload half of a registration. -/
theorem storedRegistration_storedAccept {M : PrimitiveModel} {K : KeyModel M}
    {seed : ByteArray} {s : HandshakeState} {m : AcceptChannel}
    {t : PopTranscript} (h : StoredRegistration M K seed s m t) :
    StoredAccept K seed s m :=
  h.1

/-- The transcript is bound to the accept message's temporary channel id. -/
theorem storedRegistration_channelBound {M : PrimitiveModel} {K : KeyModel M}
    {seed : ByteArray} {s : HandshakeState} {m : AcceptChannel}
    {t : PopTranscript} (h : StoredRegistration M K seed s m t) :
    t.channelId = m.temporaryChannelId.bytes :=
  h.2.1

/-- The PoP signature verifies under the stored funding key. -/
theorem storedRegistration_popAccepted {M : PrimitiveModel} {K : KeyModel M}
    {seed : ByteArray} {s : HandshakeState} {m : AcceptChannel}
    {t : PopTranscript} (h : StoredRegistration M K seed s m t) :
    PopAccepted M m.fundingPubKey t :=
  h.2.2

/-- **State-level registrations are executable registrations.**  The stored
game transcript is exactly the input on which H22's `register` succeeds and
records the same payload/transcript pair. -/
theorem register_of_storedRegistration {M : PrimitiveModel} {K : KeyModel M}
    {seed : ByteArray} {s : HandshakeState} {m : AcceptChannel}
    {t : PopTranscript} (h : StoredRegistration M K seed s m t) :
    LnLean.Proofs.WaveH.H22.register M m t =
      some { accept := m, transcript := t } := by
  rcases h with ⟨_hstore, hchan, hacc⟩
  unfold LnLean.Proofs.WaveH.H22.register
  rw [ite_eq_left hchan]
  rw [ite_eq_left (show M.ecdsaVerify m.fundingPubKey
      (LnLean.Proofs.WaveH.H22.popMessage t) t.signature = true from hacc)]

/-! ## 2. Possession and attribution under the extraction law -/

/-- **A stored registration plus PoP soundness yields an owned secret key.**
The payload alone does not do this; `PopSound` is the knowledge-soundness law
of the registration game. -/
theorem stored_registration_owns_funding_key {M : PrimitiveModel}
    (K : KeyModel M) (hsound : PopSound M K) {seed : ByteArray}
    {s : HandshakeState} {m : AcceptChannel} {t : PopTranscript}
    (h : StoredRegistration M K seed s m t) :
    ∃ sk : SecretKey, K.Owns m.fundingPubKey sk :=
  LnLean.Proofs.WaveH.H22.registered_owns_funding_key K hsound
    (register_of_storedRegistration h)

/-- **Funding-signature attribution from a stored registration.**  Under the
extraction law and the unchanged `KeyBinding` contract, the registered signer's
honest funding signature is accepted under exactly `m.fundingPubKey`.  The
generation link is part of `StoredAccept`; PoP extraction supplies the secret
key; `KeyBinding` supplies key uniqueness. -/
theorem stored_registration_funding_attribution {M : PrimitiveModel}
    (K : KeyModel M) (hsound : PopSound M K)
    (hkb : KeyBinding M.ecdsaVerify) {seed : ByteArray}
    {s : HandshakeState} {m : AcceptChannel} {t : PopTranscript}
    (h : StoredRegistration M K seed s m t) (fundingTx : ByteArray)
    (hdom : K.correctOn (fundingTag ++ fundingTx)) :
    ∃ sk : SecretKey, K.Owns m.fundingPubKey sk ∧
      M.ecdsaVerify m.fundingPubKey (fundingTag ++ fundingTx)
        (K.sign sk (fundingTag ++ fundingTx)) = true ∧
      (∀ pk' : PubKey,
        M.ecdsaVerify pk' (fundingTag ++ fundingTx)
          (K.sign sk (fundingTag ++ fundingTx)) = true →
        pk' = m.fundingPubKey) :=
  LnLean.Proofs.WaveH.H22.registration_funding_attribution K hsound hkb
    (register_of_storedRegistration h) fundingTx hdom

/-- The signature-production hypothesis of the PoP game: the transcript's
signature is exactly the honest signature of `sk` on the PoP message.  This is
strictly stronger than `PopAccepted`, and it is what makes attribution possible
without an extraction oracle. -/
def PopProducedBy {M : PrimitiveModel} (K : KeyModel M) (sk : SecretKey)
    (t : PopTranscript) : Prop :=
  t.signature = K.sign sk (popMessage t)

/-- **The stored PoP transcript establishes possession of the stored key.**
When the challenge signature is the honest signature of the stored seed, the
generated secret key is owned for the stored `funding_pubkey`. -/
theorem stored_pop_provenance_possession {M : PrimitiveModel} (K : KeyModel M)
    {seed : ByteArray} {s : HandshakeState} {m : AcceptChannel}
    (h : StoredAccept K seed s m) {t : PopTranscript}
    (_hprod : PopProducedBy K (K.secretOfSeed seed) t) :
    K.Owns m.fundingPubKey (K.secretOfSeed seed) :=
  ⟨seed, h.2.symm, rfl⟩

/-- **Sharp signature-level attribution.**  If the stored payload advertises
the seed's generated key, the challenge signature is the seed's honest
signature, and signing is correct on the PoP message, then under `KeyBinding`
every key that accepts that signature is the stored `funding_pubkey`. -/
theorem stored_pop_attribution {M : PrimitiveModel} (K : KeyModel M)
    (hkb : KeyBinding M.ecdsaVerify) {seed : ByteArray}
    {s : HandshakeState} {m : AcceptChannel} (h : StoredAccept K seed s m)
    (t : PopTranscript) (hprod : PopProducedBy K (K.secretOfSeed seed) t)
    (hdom : K.correctOn (popMessage t)) {pk' : PubKey}
    (hver : M.ecdsaVerify pk' (popMessage t) t.signature = true) :
    pk' = m.fundingPubKey := by
  have hkey : m.fundingPubKey = K.publicOfSeed seed := h.2
  have hhonest : M.ecdsaVerify m.fundingPubKey (popMessage t)
      (K.sign (K.secretOfSeed seed) (popMessage t)) = true := by
    rw [hkey]
    exact K.verifies_seed seed hdom
  have hver' : M.ecdsaVerify pk' (popMessage t)
      (K.sign (K.secretOfSeed seed) (popMessage t)) = true := by
    have hsig : t.signature =
        K.sign (K.secretOfSeed seed) (popMessage t) := hprod
    simpa [hsig] using hver
  exact hkb pk' m.fundingPubKey (popMessage t)
    (K.sign (K.secretOfSeed seed) (popMessage t)) hver' hhonest

/-- **The stored PoP attribution contract, bundled.**  The stored key is owned
by the seed's secret key, the honest PoP signature verifies under the stored
key on the declared domain, and every accepting key is the stored key.  The
conclusion is conditional on `KeyBinding`; §4 mechanises what fails without
it. -/
theorem stored_pop_attribution_contract {M : PrimitiveModel} (K : KeyModel M)
    (hkb : KeyBinding M.ecdsaVerify) {seed : ByteArray}
    {s : HandshakeState} {m : AcceptChannel} (h : StoredAccept K seed s m)
    (t : PopTranscript) (hprod : PopProducedBy K (K.secretOfSeed seed) t)
    (hdom : K.correctOn (popMessage t)) :
    K.Owns m.fundingPubKey (K.secretOfSeed seed) ∧
      M.ecdsaVerify m.fundingPubKey (popMessage t)
        (K.sign (K.secretOfSeed seed) (popMessage t)) = true ∧
      (∀ pk' : PubKey,
        M.ecdsaVerify pk' (popMessage t)
          (K.sign (K.secretOfSeed seed) (popMessage t)) = true →
        pk' = m.fundingPubKey) := by
  refine ⟨stored_pop_provenance_possession K h (t := t) hprod, ?_, ?_⟩
  · rw [h.2]
    exact K.verifies_seed seed hdom
  · intro pk' hver
    have hsig : t.signature =
        K.sign (K.secretOfSeed seed) (popMessage t) := hprod
    exact stored_pop_attribution K hkb h t hprod hdom (by
      simpa [hsig] using hver)

/-! ## 3. Storage and acceptance are not possession -/

/-- **Storing a payload plus accepting a PoP transcript is not possession.**
There is a full `EufCma` model, a payload-reachable handshake state with a
stored `accept_channel`, and an accepted PoP transcript under the stored key,
yet the same transcript also verifies under a second key that key generation
cannot produce.  `PopSound` fails, and consequently so does `KeyBinding` in this
model.  The registration event is an additional premise; the storage field is
only evidence about the peer's advertised key. -/
theorem stored_payload_not_possession (M₀ : PrimitiveModel) :
    ∃ (M : PrimitiveModel) (K : KeyModel M) (s : HandshakeState)
      (m : AcceptChannel) (seed₁ seed₂ : ByteArray) (t : PopTranscript)
      (pk' : PubKey),
      PayloadReachable s ∧
        StoredAccept K seed₁ s m ∧
        EufCma M.ecdsaVerify ∧
        AdvertisesKey K seed₁ m ∧
        K.publicOfSeed seed₁ ≠ K.publicOfSeed seed₂ ∧
        PopAccepted M m.fundingPubKey t ∧
        PopAccepted M pk' t ∧
        pk' ≠ m.fundingPubKey ∧
        (¬ ∃ sk : SecretKey, K.Owns pk' sk) ∧
        ¬ PopSound M K ∧
        ¬ KeyBinding M.ecdsaVerify := by
  obtain ⟨M, K, m, t, pk', seed₁, seed₂, heuf, hadv, hdistinct, hacc,
    hacc', hpk', hnotown, hnsound⟩ :=
    LnLean.Proofs.WaveH.H22.pop_acceptance_not_possession M₀
  have hnk : ¬ KeyBinding M.ecdsaVerify := by
    intro hkb
    have hEq : m.fundingPubKey = pk' :=
      hkb m.fundingPubKey pk' (popMessage t) t.signature hacc hacc'
    exact hpk' hEq.symm
  let s : HandshakeState := withAccept m
  refine ⟨M, K, s, m, seed₁, seed₂, t, pk', withAccept_payloadReachable m,
    ⟨rfl, hadv⟩, heuf, hadv, hdistinct, hacc, hacc', hpk', hnotown,
    hnsound, hnk⟩

/-- A plainly storage-only corollary: a payload-reachable state can store an
accepted `accept_channel` in a model where the registration extraction law
fails.  Storing the payload does not establish the game's soundness. -/
theorem stored_payload_not_popSound (M₀ : PrimitiveModel) :
    ∃ (M : PrimitiveModel) (K : KeyModel M) (s : HandshakeState)
      (m : AcceptChannel) (seed : ByteArray),
      PayloadReachable s ∧ StoredAccept K seed s m ∧
        EufCma M.ecdsaVerify ∧ ¬ PopSound M K := by
  obtain ⟨M, K, s, m, seed₁, _seed₂, _t, _pk', hreach, hstore, heuf,
    _hadv, _hdistinct, _hacc, _hacc', _hpk', _hnotown, hnsound, _hnk⟩ :=
    stored_payload_not_possession M₀
  exact ⟨M, K, s, m, seed₁, hreach, hstore, heuf, hnsound⟩

/-! ## 4. The counterexample when `KeyBinding` is dropped -/

/-- The two-key verifier of H22 accepts a fixed message under either of two
fixed keys and ignores the signature.  It is `EufCma`, and the same
message/signature is accepted under two distinct keys. -/
abbrev twoKeyVerify := LnLean.Proofs.WaveH.H22.twoKeyVerify

/-- **Without `KeyBinding`, the stored funding key does not attribute.**  There
is a full model with a payload-reachable state that stores an `accept_channel`
advertising `k₀`, and an honest funding signature from the stored seed's secret
key that verifies under *both* `k₀` and a distinct key `k₁`.  The model is
`EufCma`; `KeyBinding` fails.  Hence the `KeyBinding` premise in
`stored_registration_funding_attribution` and `stored_pop_attribution` is
necessary. -/
theorem stored_attribution_fails_without_keyBinding (M₀ : PrimitiveModel) :
    ∃ (M : PrimitiveModel) (K : KeyModel M) (s : HandshakeState)
      (m : AcceptChannel) (seed : ByteArray) (fundingTx : ByteArray)
      (pk' : PubKey),
      PayloadReachable s ∧
        StoredAccept K seed s m ∧
        EufCma M.ecdsaVerify ∧
        K.correctOn (fundingTag ++ fundingTx) ∧
        M.ecdsaVerify m.fundingPubKey (fundingTag ++ fundingTx)
          (K.sign (K.secretOfSeed seed) (fundingTag ++ fundingTx)) = true ∧
        M.ecdsaVerify pk' (fundingTag ++ fundingTx)
          (K.sign (K.secretOfSeed seed) (fundingTag ++ fundingTx)) = true ∧
        pk' ≠ m.fundingPubKey ∧
        ¬ KeyBinding M.ecdsaVerify := by
  let k₀ : PubKey := ⟨ByteArray.empty⟩
  let k₁ : PubKey := ⟨ByteArray.mk #[0x00]⟩
  let d₀ : ByteArray := fundingTag ++ ByteArray.empty
  let M : PrimitiveModel :=
    LnLean.Proofs.WaveH.H22.twoKeyModel M₀ k₀ k₁ d₀
  let K : KeyModel M :=
    LnLean.Proofs.WaveH.H22.twoKeyKeyModel M₀ k₀ k₁ d₀
  let m : AcceptChannel := acceptChannelWithFundingKey k₀
  let s : HandshakeState := withAccept m
  let seed : ByteArray := ByteArray.empty
  let pk' : PubKey := k₁
  let fundingTx : ByteArray := ByteArray.empty
  have hk : k₀ ≠ k₁ := by
    intro h
    have hs : (ByteArray.empty : ByteArray).size =
        (ByteArray.mk #[0x00] : ByteArray).size :=
      congrArg (fun p : PubKey => p.bytes.size) h
    rw [show (ByteArray.empty : ByteArray).size = 0 from rfl,
      show (ByteArray.mk #[0x00] : ByteArray).size = 1 from rfl] at hs
    omega
  have hpk₀ : K.publicOfSeed seed = k₀ := by
    show (LnLean.Proofs.WaveH.H22.twoKeyGenerate k₀ k₁ ByteArray.empty).pubkey = k₀
    simp [LnLean.Proofs.WaveH.H22.twoKeyGenerate]
  have hadv : AdvertisesKey K seed m := by
    show m.fundingPubKey = K.publicOfSeed seed
    rw [show m.fundingPubKey = k₀ from rfl, hpk₀]
  have hdom : K.correctOn (fundingTag ++ fundingTx) := by
    show (fundingTag ++ ByteArray.empty) = d₀
    rfl
  have hsig : K.sign (K.secretOfSeed seed) (fundingTag ++ fundingTx) =
      ⟨zeros 64⟩ := rfl
  have hver₀ : M.ecdsaVerify m.fundingPubKey (fundingTag ++ fundingTx)
      (K.sign (K.secretOfSeed seed) (fundingTag ++ fundingTx)) = true := by
    rw [hsig]
    show LnLean.Proofs.WaveH.H22.twoKeyVerify k₀ k₁ d₀ k₀ d₀ ⟨zeros 64⟩ = true
    simp [LnLean.Proofs.WaveH.H22.twoKeyVerify]
  have hver₁ : M.ecdsaVerify pk' (fundingTag ++ fundingTx)
      (K.sign (K.secretOfSeed seed) (fundingTag ++ fundingTx)) = true := by
    rw [hsig]
    show LnLean.Proofs.WaveH.H22.twoKeyVerify k₀ k₁ d₀ k₁ d₀ ⟨zeros 64⟩ = true
    simp [LnLean.Proofs.WaveH.H22.twoKeyVerify]
  have hpk' : pk' ≠ m.fundingPubKey := by
    intro h
    have hs : (ByteArray.mk #[0x00] : ByteArray).size =
        (ByteArray.empty : ByteArray).size :=
      congrArg (fun p : PubKey => p.bytes.size) h
    rw [show (ByteArray.mk #[0x00] : ByteArray).size = 1 from rfl,
      show (ByteArray.empty : ByteArray).size = 0 from rfl] at hs
    omega
  have hnk : ¬ KeyBinding M.ecdsaVerify := by
    intro hkb
    have h₁ : LnLean.Proofs.WaveH.H22.twoKeyVerify k₀ k₁ d₀ k₀ d₀
        ⟨zeros 64⟩ = true := by
      simp [LnLean.Proofs.WaveH.H22.twoKeyVerify]
    have h₂ : LnLean.Proofs.WaveH.H22.twoKeyVerify k₀ k₁ d₀ k₁ d₀
        ⟨zeros 64⟩ = true := by
      simp [LnLean.Proofs.WaveH.H22.twoKeyVerify]
    exact hk (hkb k₀ k₁ d₀ ⟨zeros 64⟩ h₁ h₂)
  exact ⟨M, K, s, m, seed, ByteArray.empty, pk', withAccept_payloadReachable m,
    ⟨rfl, hadv⟩, M.ecdsa_eufCma, hdom, hver₀, hver₁, hpk', hnk⟩

/-! ## 5. Non-vacuity of the stored registration contract -/

/-- **The positive stored contract is not vacuous.**  There is a concrete C3,
key-binding, PoP-sound model with a payload-reachable stored registration, a
registered funding key, and a funding message on which attribution succeeds. -/
theorem stored_registration_contract_nonvacuous (M₀ : PrimitiveModel)
    (k₀ : PubKey) :
    ∃ (M : PrimitiveModel) (K : KeyModel M) (s : HandshakeState)
      (m : AcceptChannel) (t : PopTranscript) (seed : ByteArray)
      (fundingTx : ByteArray),
      PayloadReachable s ∧ StoredRegistration M K seed s m t ∧
        EufCma M.ecdsaVerify ∧ PopSound M K ∧
        KeyBinding M.ecdsaVerify ∧ AdvertisesKey K seed m ∧
        K.correctOn (fundingTag ++ fundingTx) ∧
        (∀ pk' : PubKey,
          M.ecdsaVerify pk' (fundingTag ++ fundingTx)
            (K.sign (K.secretOfSeed seed) (fundingTag ++ fundingTx)) = true →
          pk' = m.fundingPubKey) := by
  obtain ⟨M, K, a, t, r, fundingTx, heuf, hsound, hkb, hadv, hreg, hdom,
    hattr⟩ :=
    LnLean.Proofs.WaveH.H22.registration_contract_nonvacuous M₀ k₀
  let s : HandshakeState := withAccept a
  have hacc : PopAccepted M a.fundingPubKey t :=
    LnLean.Proofs.WaveH.H22.register_popAccepted hreg
  have hchan : t.channelId = a.temporaryChannelId.bytes :=
    LnLean.Proofs.WaveH.H22.register_channel_bound hreg
  have hsr : StoredRegistration M K ByteArray.empty s a t :=
    ⟨⟨rfl, hadv⟩, hchan, hacc⟩
  exact ⟨M, K, s, a, t, ByteArray.empty, fundingTx,
    withAccept_payloadReachable a, hsr, heuf, hsound, hkb, hadv, hdom, hattr⟩

/-! ## 6. Summary -/

/-- Bundled faithful reading of the stored registration/PoP game:

1. a stored registration is a successful verifier-side registration;
2. `PopSound` plus a stored registration yields an owned secret key;
3. `PopSound` and `KeyBinding` give funding-signature attribution from a stored
   registration;
4. the signature-level stored PoP contract needs explicit signature
   provenance and `KeyBinding`;
5. storage plus PoP acceptance is not possession, and `PopSound` fails in the
   countermodel;
6. without `KeyBinding`, an honest funding signature is accepted under a second
   key different from the stored funding key;
7. the positive contract has a concrete non-vacuous instance. -/
theorem attribution_game_summary :
    (∀ {M : PrimitiveModel} {K : KeyModel M} {seed : ByteArray}
        {s : HandshakeState} {m : AcceptChannel} {t : PopTranscript},
        StoredRegistration M K seed s m t →
        LnLean.Proofs.WaveH.H22.register M m t =
          some { accept := m, transcript := t }) ∧
      (∀ {M : PrimitiveModel} (K : KeyModel M), PopSound M K →
        ∀ {seed : ByteArray} {s : HandshakeState} {m : AcceptChannel}
          {t : PopTranscript}, StoredRegistration M K seed s m t →
          ∃ sk : SecretKey, K.Owns m.fundingPubKey sk) ∧
      (∀ {M : PrimitiveModel} (K : KeyModel M), PopSound M K →
        KeyBinding M.ecdsaVerify →
        ∀ {seed : ByteArray} {s : HandshakeState} {m : AcceptChannel}
          {t : PopTranscript}, StoredRegistration M K seed s m t →
          ∀ fundingTx : ByteArray,
          K.correctOn (fundingTag ++ fundingTx) →
          ∃ sk : SecretKey, K.Owns m.fundingPubKey sk ∧
            M.ecdsaVerify m.fundingPubKey (fundingTag ++ fundingTx)
              (K.sign sk (fundingTag ++ fundingTx)) = true ∧
            (∀ pk' : PubKey,
              M.ecdsaVerify pk' (fundingTag ++ fundingTx)
                (K.sign sk (fundingTag ++ fundingTx)) = true →
              pk' = m.fundingPubKey)) ∧
      (∀ {M : PrimitiveModel} (K : KeyModel M),
        KeyBinding M.ecdsaVerify →
        ∀ {seed : ByteArray} {s : HandshakeState} {m : AcceptChannel},
          StoredAccept K seed s m → ∀ (t : PopTranscript),
          PopProducedBy K (K.secretOfSeed seed) t →
          K.correctOn (popMessage t) →
          ∀ {pk' : PubKey},
            M.ecdsaVerify pk' (popMessage t) t.signature = true →
            pk' = m.fundingPubKey) ∧
      (∀ _M₀ : PrimitiveModel,
        ∃ (M : PrimitiveModel) (K : KeyModel M) (s : HandshakeState)
          (m : AcceptChannel) (seed₁ _seed₂ : ByteArray) (t : PopTranscript)
          (pk' : PubKey),
          PayloadReachable s ∧ StoredAccept K seed₁ s m ∧
            EufCma M.ecdsaVerify ∧ PopAccepted M m.fundingPubKey t ∧
            PopAccepted M pk' t ∧ pk' ≠ m.fundingPubKey ∧
            (¬ ∃ sk : SecretKey, K.Owns pk' sk) ∧ ¬ PopSound M K ∧
            ¬ KeyBinding M.ecdsaVerify) ∧
      (∀ _M₀ : PrimitiveModel,
        ∃ (M : PrimitiveModel) (K : KeyModel M) (s : HandshakeState)
          (m : AcceptChannel) (seed : ByteArray) (fundingTx : ByteArray)
          (pk' : PubKey),
          PayloadReachable s ∧ StoredAccept K seed s m ∧
            EufCma M.ecdsaVerify ∧ K.correctOn (fundingTag ++ fundingTx) ∧
            M.ecdsaVerify m.fundingPubKey (fundingTag ++ fundingTx)
              (K.sign (K.secretOfSeed seed) (fundingTag ++ fundingTx)) = true ∧
            M.ecdsaVerify pk' (fundingTag ++ fundingTx)
              (K.sign (K.secretOfSeed seed) (fundingTag ++ fundingTx)) = true ∧
            pk' ≠ m.fundingPubKey ∧ ¬ KeyBinding M.ecdsaVerify) :=
  ⟨fun h => register_of_storedRegistration h,
    fun K hsound _ _ _ _ h => stored_registration_owns_funding_key K hsound h,
    fun K hsound hkb _ _ _ _ h fundingTx hdom =>
      stored_registration_funding_attribution K hsound hkb h fundingTx hdom,
    fun K hkb _ _ _ h t hprod hdom _ hver =>
      stored_pop_attribution K hkb h t hprod hdom hver,
    fun M₀ => by
      obtain ⟨M, K, s, m, s₁, _s₂, t, pk', hreach, hstore, heuf, _hadv,
        _hdistinct, hacc, hacc', hpk', hnotown, hnsound, hnk⟩ :=
        stored_payload_not_possession M₀
      exact ⟨M, K, s, m, s₁, _s₂, t, pk', hreach, hstore, heuf, hacc,
        hacc', hpk', hnotown, hnsound, hnk⟩,
    fun M₀ => stored_attribution_fails_without_keyBinding M₀⟩

end LnLean.Proofs.Crypto.AttributionGameTargets
