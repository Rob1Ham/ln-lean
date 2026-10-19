/-
# A concrete challenge-response proof-of-possession protocol (PR-01, wave 10)

**Catalog issue.**  `PR-01` (P1): `FundingSigningLaw` and `KeyBinding` are
hypotheses; wave 9 reduced proof-of-possession to the explicit extraction laws
`PopSound`/`PopProducedBy` over the *stored* `accept_channel` payload.  The
challenge encoding was the inherited H22 shape
`popTag ++ temporary_channel_id ++ challenge`, whose split is not injective for
variable-width fields (`H22.popMessage_split_not_injective`), and freshness was
only an informal `Issued` predicate.

**What this module adds.**  A concrete verifier-side challenge-response
protocol over the existing `PrimitiveModel`/`KeyModel`/`Signer` vocabulary:

1. `PopChallenge` is a verifier-issued challenge carrying the channel id and a
   32-byte freshness nonce.  `PopSession` binds a session handle, that
   challenge and the expected (advertised) key; `PopResponse` carries the
   responder's claimed challenge and a signature.
2. `PopChallenge.Valid` is the fixed-width discipline (32-byte channel id and
   32-byte nonce) under which the `channelId ++ nonce` split is recoverable.
   `challengeMessage_injective_of_valid` is a real injectivity theorem, not a
   re-assumption: two valid challenges with the same signed bytes are equal.
3. `accepts` is the session-bound verifier: it recomputes the signed message
   from the *session's* challenge.  `honestResponse` is the signer's response,
   and `advertised_honest_completeness` proves that an honest `Signer` produces
   an accepted response for the advertised `accept_channel.funding_pubkey`
   whenever the key model is correct on the challenge-message domain.
   `storedAccept_honest_registration` turns that into wave 9's
   `StoredRegistration` for a stored payload.
4. **Soundness is derived, not assumed wholesale.**  The weakest law used here
   is `PopKeySoundOn`: every accepted response on an *issued* challenge yields a
   secret key owned for the advertised public key.  It is strictly weaker than
   H22's extraction form: it gives possession but not signature provenance.
   `PopExtractionOn` is the stronger law that additionally identifies the
   signature as an honest signature; it derives H22's `PopSoundOn` on
   well-formed and on all challenges (`popSound_of_extraction`), and it derives
   wave 9's `PopProducedBy`.  `accepted_key_unique` and
   `accepted_funding_attribution` then derive funding-key attribution from the
   *unchanged* `KeyBinding` contract.
5. **The sharp negatives are mechanised.**
   * `unbound_replay_accepts`: a verifier that verifies the response's claimed
     challenge without comparing it to the session challenge accepts an old
     response in a new session.
   * `nonceFree_replay_accepts`: if the nonce is absent from the signed bytes,
     two sessions with different nonces accept the same signature.
   * `binding_fails_without_valid`: without the fixed-width discipline two
     distinct challenges encode the same bytes, so the session-bound verifier
     accepts the same response for both.  This shows `Valid` is necessary for
     `accepts_challenge_bound`.
   * `repeated_challenge_replay`: if the verifier reuses a challenge in a
     second session, the same response is accepted there; freshness
     (`FreshOn`) is exactly the discipline that excludes this.
   * `no_cross_session_replay` is the positive counterpart: under `Valid`,
     `EufCma` and a shared expected key, two sessions with distinct challenges
     cannot both accept one response.
6. **Boundary results.**  `keySound_not_provenance` proves that acceptance plus
   possession does *not* imply that the signature is the honest signature, so
   `PopProducedBy` is genuinely stronger than key soundness.
   `keySound_not_keyBinding` and `keyBinding_completeness_not_keySound`
   (re-exported from H22) show that `EufCma`, `KeyBinding`, and signing
   completeness neither imply one another nor the PoP key-soundness law.
   `protocol_nonvacuous` gives a concrete C3/`KeyBinding`/extraction-sound
   witness with a valid challenge, an honest accepted response, possession of
   the stored funding key and funding attribution.

**What is not claimed.**  No secp256k1 arithmetic, no real signature scheme,
no computational unforgeability, no probability/randomness, and no Noise
transport authentication.  `EufCma` is the algebraic message-binding
consequence of EUF-CMA, `KeyBinding` is key uniqueness for a fixed
signature, and `PopKeySoundOn`/`PopExtractionOn` are exact knowledge-soundness
laws that a deployment must obtain from a real scheme and fresh challenges.
The module does not derive `KeyBinding`; wave 9's `StoredAccept` and the
`FundingSigningLaw` totality caveat are unchanged.  The C3/Noise boundary is:
this protocol authenticates *knowledge of a funding key* over an authenticated
challenge channel, not the peer's transport identity.

**BOLT sections.**  BOLT 2 §The `open_channel` Message and §The
`accept_channel` Message (`funding_pubkey`, `temporary_channel_id`), §The
`funding_created` Message and §The `funding_signed` Message; BOLT 1 §Lightning
Message Format (`signature`); BOLT 8 §Handshake State for the transport channel
that is *not* modelled here.
-/

import LnLean.Proofs.Crypto.AcceptPayloadTargets
import LnLean.Proofs.Crypto.AttributionGameTargets
import LnLean.Proofs.Crypto.KeyModelTargets
import LnLean.Proofs.WaveH.H22
import LnLean.Wire.BigSize

namespace LnLean.Proofs.Crypto.PopProtocolTargets

set_option autoImplicit false

open LnLean
open LnLean.Bitcoin
open LnLean.Crypto
open LnLean.Crypto.KeyModel
open LnLean.Protocol
open LnLean.Protocol.Handshake
open LnLean.Proofs.WaveH.H22
open LnLean.Proofs.Crypto.KeyModelTargets
  (acceptChannelWithFundingKey acceptChannelWithFundingKey_fundingPubKey
   AdvertisesKey StoredAccept
   pinnedModel pinnedKeyModel pinnedVerify pinnedVerify_eufCma
   pinnedVerify_keyBinding)
open LnLean.Proofs.Crypto.AttributionGameTargets
  (StoredRegistration PopProducedBy)

/-- The key-binding contract, re-exported under this module's namespace.  It is
the unchanged `LnLean.Proofs.WaveE.E06.KeyBinding` definition. -/
abbrev KeyBinding (verify : PubKey → ByteArray → EcdsaSig → Bool) : Prop :=
  LnLean.Proofs.WaveE.E06.KeyBinding verify

/-! ## 1. Challenges, sessions, responses and the signed message -/

/-- A verifier-issued proof-of-possession challenge.  `channelId` binds the
`accept_channel.temporary_channel_id`; `nonce` is the freshness value the
verifier chooses for this session. -/
structure PopChallenge where
  /-- The `temporary_channel_id` bytes this challenge is bound to. -/
  channelId : ChannelId
  /-- The verifier-issued freshness nonce. -/
  nonce : ByteArray
deriving Repr, BEq

/-- The fixed-width discipline on a challenge: a valid 32-byte channel id and a
32-byte nonce.  This is what makes the `channelId ++ nonce` split recoverable
and hence the signed message injective. -/
def PopChallenge.Valid (c : PopChallenge) : Prop :=
  c.channelId.Valid ∧ c.nonce.size = 32

/-- A freshness discipline relative to a set/predicate of already used
challenges.  A verifier that issues a `FreshOn Used` challenge has not used it
before. -/
def FreshOn (Used : PopChallenge → Prop) (c : PopChallenge) : Prop :=
  c.Valid ∧ ¬ Used c

/-- A challenge-response session: a session handle, the verifier's challenge,
and the key the verifier expects to see demonstrated. -/
structure PopSession where
  /-- A local session handle, distinct from the nonce. -/
  sessionId : ByteArray
  /-- The verifier-issued challenge. -/
  challenge : PopChallenge
  /-- The advertised key the response must demonstrate. -/
  expectedKey : PubKey
deriving Repr, BEq

/-- The validity of a session is the validity of its challenge. -/
def PopSession.Valid (s : PopSession) : Prop :=
  s.challenge.Valid

/-- A response: the challenge the responder claims to answer (untrusted by the
session-bound verifier) and the signature over the challenge message. -/
structure PopResponse where
  /-- The challenge the responder says it answered. -/
  challenge : PopChallenge
  /-- The signature bytes. -/
  signature : EcdsaSig
deriving Repr, BEq

/-- The exact signed message of a challenge.  The domain tag, the full channel
id and the freshness nonce are covered.  Under `PopChallenge.Valid` the two
field widths are fixed, so this encoding is injective
(`challengeMessage_injective_of_valid`). -/
def challengeMessage (c : PopChallenge) : ByteArray :=
  popTag ++ c.channelId.bytes ++ c.nonce

/-- A session over a fixed key and challenge. -/
def sessionOfKey (pk : PubKey) (c : PopChallenge) : PopSession :=
  { sessionId := c.channelId.bytes, challenge := c, expectedKey := pk }

/-- The challenge a verifier issues for a received `accept_channel`: it is
bound to the message's `temporary_channel_id`. -/
def challengeOfAccept (m : AcceptChannel) (nonce : ByteArray) : PopChallenge :=
  { channelId := m.temporaryChannelId, nonce := nonce }

/-- The session a verifier creates for a received `accept_channel`: the
challenge channel id is the message's `temporary_channel_id`, and the expected
key is its advertised `funding_pubkey`. -/
def sessionOfAccept (m : AcceptChannel) (nonce : ByteArray) : PopSession :=
  { sessionId := m.temporaryChannelId.bytes
    challenge := challengeOfAccept m nonce
    expectedKey := m.fundingPubKey }

/-- The H22 transcript corresponding to a session/response pair.  It exists so
that the new protocol composes with the wave-9 registration game rather than
replacing it. -/
def sessionTranscript (s : PopSession) (r : PopResponse) : PopTranscript :=
  { channelId := s.challenge.channelId.bytes
    challenge := s.challenge.nonce
    signature := r.signature }

/-- The session `accepts` a response when the signature verifies under the
expected key on the message derived from the *session's* challenge.  The
response's own `challenge` field is not trusted. -/
def accepts (M : PrimitiveModel) (s : PopSession) (r : PopResponse) : Prop :=
  M.ecdsaVerify s.expectedKey (challengeMessage s.challenge) r.signature = true

/-- The honest response of a signer: it echoes the challenge and signs the
challenge message with the generated secret key. -/
def honestResponse {M : PrimitiveModel} (K : KeyModel M) (seed : ByteArray)
    (c : PopChallenge) : PopResponse :=
  { challenge := c
    signature := K.sign (K.secretOfSeed seed) (challengeMessage c) }

/-- Explicit signature production: the response signature is exactly the honest
signature of `sk` on `c`.  This is the per-response form of the wave-9
`PopProducedBy` predicate. -/
def producedBy {M : PrimitiveModel} (K : KeyModel M) (sk : SecretKey)
    (c : PopChallenge) (r : PopResponse) : Prop :=
  r.signature = K.sign sk (challengeMessage c)

/-! ## 2. Message injectivity and challenge binding -/

/-- The H22 transcript message is the new challenge message. -/
@[simp] theorem popMessage_sessionTranscript (s : PopSession) (r : PopResponse) :
    popMessage (sessionTranscript s r) = challengeMessage s.challenge := rfl

/-- Byte-list equality implies byte-array equality. -/
private theorem byteArray_eq_of_bytesToList_eq {a b : ByteArray}
    (h : LnLean.Wire.bytesToList a = LnLean.Wire.bytesToList b) : a = b := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simpa [LnLean.Wire.bytesToList] using h

/-- Prefix cancellation when the two prefixes have the same length.  This is
the structural fact that the fixed-width discipline supplies. -/
private theorem append_cancel_of_size {a b c d : ByteArray}
    (h : a ++ b = c ++ d) (hsize : a.size = c.size) :
    a = c ∧ b = d := by
  have hl : LnLean.Wire.bytesToList a ++ LnLean.Wire.bytesToList b =
      LnLean.Wire.bytesToList c ++ LnLean.Wire.bytesToList d := by
    rw [← LnLean.Wire.bytesToList_append,
      ← LnLean.Wire.bytesToList_append, h]
  have hlen : (LnLean.Wire.bytesToList a).length =
      (LnLean.Wire.bytesToList c).length := by
    rw [LnLean.Wire.bytesToList_length, LnLean.Wire.bytesToList_length]
    exact hsize
  have ha : LnLean.Wire.bytesToList a = LnLean.Wire.bytesToList c := by
    have htake : List.take (LnLean.Wire.bytesToList a).length
        (LnLean.Wire.bytesToList a ++ LnLean.Wire.bytesToList b) =
      LnLean.Wire.bytesToList a := List.take_left
    have htake' : List.take (LnLean.Wire.bytesToList a).length
        (LnLean.Wire.bytesToList c ++ LnLean.Wire.bytesToList d) =
      LnLean.Wire.bytesToList c := by
      rw [hlen]
      exact List.take_left
    calc LnLean.Wire.bytesToList a
        = List.take (LnLean.Wire.bytesToList a).length
            (LnLean.Wire.bytesToList a ++ LnLean.Wire.bytesToList b) :=
          htake.symm
      _ = List.take (LnLean.Wire.bytesToList a).length
            (LnLean.Wire.bytesToList c ++ LnLean.Wire.bytesToList d) := by
          rw [hl]
      _ = LnLean.Wire.bytesToList c := htake'
  have hb : LnLean.Wire.bytesToList b = LnLean.Wire.bytesToList d := by
    have h' : LnLean.Wire.bytesToList a ++ LnLean.Wire.bytesToList b =
        LnLean.Wire.bytesToList a ++ LnLean.Wire.bytesToList d := by
      calc LnLean.Wire.bytesToList a ++ LnLean.Wire.bytesToList b
          = LnLean.Wire.bytesToList c ++ LnLean.Wire.bytesToList d := hl
        _ = LnLean.Wire.bytesToList a ++ LnLean.Wire.bytesToList d := by
            rw [ha]
    exact List.append_cancel_left h'
  exact ⟨byteArray_eq_of_bytesToList_eq ha, byteArray_eq_of_bytesToList_eq hb⟩

/-- **The challenge message is injective on valid challenges.**  This is the
real encoding theorem the H22 shape lacked: with a 32-byte channel id and a
32-byte nonce, equal signed bytes force equal challenges.  It is not an
assumption and not a hash-collision hypothesis. -/
theorem challengeMessage_injective_of_valid {c₁ c₂ : PopChallenge}
    (h₁ : c₁.Valid) (h₂ : c₂.Valid)
    (h : challengeMessage c₁ = challengeMessage c₂) : c₁ = c₂ := by
  unfold challengeMessage at h
  rw [ByteArray.append_assoc, ByteArray.append_assoc] at h
  have h' : c₁.channelId.bytes ++ c₁.nonce = c₂.channelId.bytes ++ c₂.nonce :=
    append_left_cancel h
  obtain ⟨hcid, hnonce⟩ := append_cancel_of_size h' (by rw [h₁.1, h₂.1])
  cases c₁ with
  | mk ch₁ n₁ =>
    cases c₂ with
    | mk ch₂ n₂ =>
      simp only [PopChallenge.mk.injEq]
      refine ⟨?_, hnonce⟩
      cases ch₁
      cases ch₂
      simp_all

/-- **A response cannot cross sessions.**  Under `EufCma`, if the same response
is accepted by two sessions that expect the same key, the two challenges are
equal.  The `Valid` hypotheses are needed because the message encoding (not
the hash) must separate the fields. -/
theorem accepts_challenge_bound {M : PrimitiveModel} {s₁ s₂ : PopSession}
    {r : PopResponse} (hs₁ : s₁.Valid) (hs₂ : s₂.Valid)
    (hkey : s₁.expectedKey = s₂.expectedKey)
    (h₁ : accepts M s₁ r) (h₂ : accepts M s₂ r) :
    s₁.challenge = s₂.challenge := by
  have h₂' : M.ecdsaVerify s₁.expectedKey (challengeMessage s₂.challenge)
      r.signature = true := by
    simpa [accepts, hkey] using h₂
  have hmsg : challengeMessage s₁.challenge = challengeMessage s₂.challenge :=
    M.ecdsa_eufCma s₁.expectedKey (challengeMessage s₁.challenge)
      (challengeMessage s₂.challenge) r.signature h₁ h₂'
  exact challengeMessage_injective_of_valid hs₁ hs₂ hmsg

/-- Positive counterpart of the replay negative: distinct challenges on the
same expected key cannot both accept one response. -/
theorem no_cross_session_replay {M : PrimitiveModel} {s₁ s₂ : PopSession}
    {r : PopResponse} (hs₁ : s₁.Valid) (hs₂ : s₂.Valid)
    (hkey : s₁.expectedKey = s₂.expectedKey)
    (hfresh : s₁.challenge ≠ s₂.challenge) :
    ¬ (accepts M s₁ r ∧ accepts M s₂ r) := by
  rintro ⟨h₁, h₂⟩
  exact hfresh (accepts_challenge_bound hs₁ hs₂ hkey h₁ h₂)

/-! ## 3. Honest completeness -/

/-- The honest response is produced by the signer's secret key. -/
theorem honestResponse_producedBy {M : PrimitiveModel} (K : KeyModel M)
    (seed : ByteArray) (c : PopChallenge) :
    producedBy K (K.secretOfSeed seed) c (honestResponse K seed c) :=
  rfl

/-- **Honest completeness.**  On the key model's declared domain, the honest
signer's response is accepted by the session that expects the signer's generated
key. -/
theorem honestResponse_accepts {M : PrimitiveModel} (K : KeyModel M)
    (seed : ByteArray) (c : PopChallenge)
    (hdom : K.correctOn (challengeMessage c)) :
    accepts M (sessionOfKey (K.publicOfSeed seed) c) (honestResponse K seed c) := by
  show M.ecdsaVerify (K.publicOfSeed seed) (challengeMessage c)
    (K.sign (K.secretOfSeed seed) (challengeMessage c)) = true
  exact K.verifies_seed seed hdom

/-- **Honest completeness for the advertised `accept_channel` key.**  The
verifier's session channel id is the message's `temporary_channel_id`, and the
response is accepted exactly under the advertised `funding_pubkey`. -/
theorem advertised_honest_completeness {M : PrimitiveModel} (K : KeyModel M)
    {seed : ByteArray} {m : AcceptChannel} (hadv : AdvertisesKey K seed m)
    (nonce : ByteArray) (hdom : K.correctOn (challengeMessage (challengeOfAccept m nonce))) :
    accepts M (sessionOfAccept m nonce)
      (honestResponse K seed (challengeOfAccept m nonce)) := by
  show M.ecdsaVerify m.fundingPubKey
    (challengeMessage { channelId := m.temporaryChannelId, nonce := nonce })
    (K.sign (K.secretOfSeed seed)
      (challengeMessage { channelId := m.temporaryChannelId, nonce := nonce })) =
        true
  rw [hadv]
  exact K.verifies_seed seed hdom

/-- The honest session/response pair is an H22 `PopTranscript` accepted under the
advertised key. -/
theorem advertised_honest_popAccepted {M : PrimitiveModel} (K : KeyModel M)
    {seed : ByteArray} {m : AcceptChannel} (hadv : AdvertisesKey K seed m)
    (nonce : ByteArray) (hdom : K.correctOn (challengeMessage (challengeOfAccept m nonce))) :
    PopAccepted M m.fundingPubKey
      (sessionTranscript (sessionOfAccept m nonce)
        (honestResponse K seed (challengeOfAccept m nonce))) := by
  show M.ecdsaVerify m.fundingPubKey
    (challengeMessage { channelId := m.temporaryChannelId, nonce := nonce })
    (K.sign (K.secretOfSeed seed)
      (challengeMessage { channelId := m.temporaryChannelId, nonce := nonce })) =
        true
  rw [hadv]
  exact K.verifies_seed seed hdom

/-- The H22 verifier-side registration accepts the honest response. -/
theorem honestResponse_registers {M : PrimitiveModel} (K : KeyModel M)
    {seed : ByteArray} {m : AcceptChannel} (hadv : AdvertisesKey K seed m)
    (nonce : ByteArray) (hdom : K.correctOn (challengeMessage (challengeOfAccept m nonce))) :
    let t := sessionTranscript (sessionOfAccept m nonce)
      (honestResponse K seed (challengeOfAccept m nonce))
    register M m t = some { accept := m, transcript := t } := by
  dsimp only
  let t := sessionTranscript (sessionOfAccept m nonce)
    (honestResponse K seed (challengeOfAccept m nonce))
  have hpop := advertised_honest_popAccepted K hadv nonce hdom
  unfold register
  rw [ite_eq_left (show (sessionTranscript (sessionOfAccept m nonce)
      (honestResponse K seed (challengeOfAccept m nonce))).channelId = m.temporaryChannelId.bytes from rfl)]
  rw [ite_eq_left (show M.ecdsaVerify m.fundingPubKey
      (popMessage (sessionTranscript (sessionOfAccept m nonce)
        (honestResponse K seed (challengeOfAccept m nonce))))
      (sessionTranscript (sessionOfAccept m nonce)
        (honestResponse K seed (challengeOfAccept m nonce))).signature = true from hpop)]

/-- **Honest completeness yields a stored registration.**  If the handshake
state stores an `accept_channel` that advertises the signer's generated key,
the honest response on a fresh nonce is a wave-9 `StoredRegistration`. -/
theorem storedAccept_honest_registration {M : PrimitiveModel} (K : KeyModel M)
    {seed : ByteArray} {s : HandshakeState} {m : AcceptChannel}
    (hstore : StoredAccept K seed s m) (nonce : ByteArray)
    (hdom : K.correctOn (challengeMessage (challengeOfAccept m nonce))) :
    ∃ t : PopTranscript, StoredRegistration M K seed s m t := by
  refine ⟨sessionTranscript (sessionOfAccept m nonce)
    (honestResponse K seed (challengeOfAccept m nonce)), hstore, rfl, ?_⟩
  exact advertised_honest_popAccepted K hstore.2 nonce hdom

/-! ## 4. Soundness laws and what they derive -/

/-- **The weakest faithful PoP key-soundness law.**  Every response accepted on
an issued challenge yields a secret key that key generation pairs with the
advertised public key.  This is strictly weaker than H22's extraction form: it
says *possession*, not "the signature is the honest signature". -/
def PopKeySoundOn (M : PrimitiveModel) (K : KeyModel M)
    (Issued : PopChallenge → Prop) : Prop :=
  ∀ (pk : PubKey) (c : PopChallenge) (sig : EcdsaSig),
    Issued c → M.ecdsaVerify pk (challengeMessage c) sig = true →
    ∃ sk : SecretKey, K.Owns pk sk

/-- **The extraction form.**  Every accepted response on an issued challenge is
the honest signature of a seed that generates the advertised public key.  This
is the exact algebraic knowledge-soundness requirement for the challenge
response; it implies `PopKeySoundOn`. -/
def PopExtractionOn (M : PrimitiveModel) (K : KeyModel M)
    (Issued : PopChallenge → Prop) : Prop :=
  ∀ (pk : PubKey) (c : PopChallenge) (sig : EcdsaSig),
    Issued c → M.ecdsaVerify pk (challengeMessage c) sig = true →
    ∃ seed : ByteArray,
      pk = K.publicOfSeed seed ∧
        sig = K.sign (K.secretOfSeed seed) (challengeMessage c)

/-- Extraction implies key soundness. -/
theorem popKeySoundOn_of_extraction {M : PrimitiveModel} {K : KeyModel M}
    {Issued : PopChallenge → Prop} (h : PopExtractionOn M K Issued) :
    PopKeySoundOn M K Issued := by
  intro pk c sig hiss hacc
  obtain ⟨seed, hpk, _⟩ := h pk c sig hiss hacc
  exact ⟨K.secretOfSeed seed, seed, hpk.symm, rfl⟩

/-- **An accepted session response establishes possession** of the expected
key, under the key-soundness law. -/
theorem accepted_owns {M : PrimitiveModel} {K : KeyModel M}
    {Issued : PopChallenge → Prop} (hsound : PopKeySoundOn M K Issued)
    {s : PopSession} {r : PopResponse} (hiss : Issued s.challenge)
    (hacc : accepts M s r) :
    ∃ sk : SecretKey, K.Owns s.expectedKey sk :=
  hsound s.expectedKey s.challenge r.signature hiss hacc

/-- **An accepted session response has honest provenance**, under extraction:
it identifies the seed and proves the signature is that seed's honest
signature. -/
theorem accepted_provenance {M : PrimitiveModel} {K : KeyModel M}
    {Issued : PopChallenge → Prop} (hext : PopExtractionOn M K Issued)
    {s : PopSession} {r : PopResponse} (hiss : Issued s.challenge)
    (hacc : accepts M s r) :
    ∃ seed : ByteArray,
      s.expectedKey = K.publicOfSeed seed ∧
        producedBy K (K.secretOfSeed seed) s.challenge r :=
  hext s.expectedKey s.challenge r.signature hiss hacc

/-- The new production predicate is the wave-9 `PopProducedBy` on the corresponding
transcript. -/
theorem popProducedBy_iff_producedBy {M : PrimitiveModel} {K : KeyModel M}
    {sk : SecretKey} {s : PopSession} {r : PopResponse} :
    PopProducedBy K sk (sessionTranscript s r) ↔
      producedBy K sk s.challenge r := by
  simp [PopProducedBy, producedBy, sessionTranscript, challengeMessage]

/-- Extraction yields the H22 provenance predicate plus ownership. -/
theorem accepted_popProducedBy {M : PrimitiveModel} {K : KeyModel M}
    {Issued : PopChallenge → Prop} (hext : PopExtractionOn M K Issued)
    {s : PopSession} {r : PopResponse} (hiss : Issued s.challenge)
    (hacc : accepts M s r) :
    ∃ sk : SecretKey,
      K.Owns s.expectedKey sk ∧
        PopProducedBy K sk (sessionTranscript s r) := by
  obtain ⟨seed, hpk, hsig⟩ := accepted_provenance hext hiss hacc
  refine ⟨K.secretOfSeed seed, ?_, ?_⟩
  · exact ⟨seed, hpk.symm, rfl⟩
  · rw [popProducedBy_iff_producedBy]
    exact hsig

/-- Under the unchanged `KeyBinding` contract, any key that accepts the same
session message and signature is the expected key.  This needs no extraction
law; it is exactly key uniqueness for the fixed signature. -/
theorem accepted_key_unique {M : PrimitiveModel} {s : PopSession}
    {r : PopResponse} (hkb : KeyBinding M.ecdsaVerify)
    (hacc : accepts M s r) {pk' : PubKey}
    (hver : M.ecdsaVerify pk' (challengeMessage s.challenge) r.signature = true) :
    pk' = s.expectedKey :=
  hkb pk' s.expectedKey (challengeMessage s.challenge) r.signature hver hacc

/-- **Funding-signature attribution after an accepted PoP response.**  The
accepted response supplies an owned secret key for the expected key; the
unchanged `KeyBinding` contract supplies uniqueness of the funding recipient. -/
theorem accepted_funding_attribution {M : PrimitiveModel} {K : KeyModel M}
    {Issued : PopChallenge → Prop} (hsound : PopKeySoundOn M K Issued)
    (hkb : KeyBinding M.ecdsaVerify) {s : PopSession} {r : PopResponse}
    (hiss : Issued s.challenge) (hacc : accepts M s r)
    (fundingTx : ByteArray) (hdom : K.correctOn (fundingTag ++ fundingTx)) :
    ∃ sk : SecretKey,
      K.Owns s.expectedKey sk ∧
        M.ecdsaVerify s.expectedKey (fundingTag ++ fundingTx)
          (K.sign sk (fundingTag ++ fundingTx)) = true ∧
        (∀ pk' : PubKey,
          M.ecdsaVerify pk' (fundingTag ++ fundingTx)
            (K.sign sk (fundingTag ++ fundingTx)) = true →
          pk' = s.expectedKey) := by
  obtain ⟨sk, hown⟩ := accepted_owns hsound hiss hacc
  have hver := K.owns_verifies hown hdom
  exact ⟨sk, hown, hver,
    fun pk' hpk' => hkb pk' s.expectedKey (fundingTag ++ fundingTx)
      (K.sign sk (fundingTag ++ fundingTx)) hpk' hver⟩

/-- **The new protocol derives H22 `PopSoundOn`.**  Key soundness on issued
challenges implies the wave-9/registration-game soundness law on the
corresponding transcripts. -/
theorem popSoundOn_of_keySoundOn {M : PrimitiveModel} {K : KeyModel M}
    {Issued : PopChallenge → Prop} (h : PopKeySoundOn M K Issued) :
    PopSoundOn K (fun t : PopTranscript =>
      Issued { channelId := ⟨t.channelId⟩, nonce := t.challenge }) := by
  intro pk t hiss hacc
  exact h pk { channelId := ⟨t.channelId⟩, nonce := t.challenge }
    t.signature hiss hacc

/-- In particular, key soundness restricted to valid challenges derives
`PopSoundOn` on the well-formed transcripts (32-byte channel id and nonce). -/
theorem popSoundOn_wellFormed_of_keySoundOn {M : PrimitiveModel}
    {K : KeyModel M}
    (h : PopKeySoundOn M K (fun c => c.Valid)) :
    PopSoundOn K (fun t : PopTranscript =>
      t.channelId.size = 32 ∧ t.challenge.size = 32) := by
  have h' := popSoundOn_of_keySoundOn h
  intro pk t hiss hacc
  exact h' pk t (by
    show ({ channelId := ⟨t.channelId⟩, nonce := t.challenge } : PopChallenge).Valid
    exact hiss) hacc

/-- **The unrestricted form.**  If extraction/key soundness holds on *every*
challenge (the idealised form), then H22's unconditional `PopSound` holds. -/
theorem popSound_of_keySoundOn {M : PrimitiveModel} {K : KeyModel M}
    (h : PopKeySoundOn M K (fun _ => True)) : PopSound K := by
  intro pk t _ hacc
  exact h pk { channelId := ⟨t.channelId⟩, nonce := t.challenge }
    t.signature trivial hacc

/-- The unrestricted `PopSound` is exactly the unrestricted key-soundness law. -/
theorem popSound_iff_keySound {M : PrimitiveModel} (K : KeyModel M) :
    PopSound K ↔ PopKeySoundOn M K (fun _ => True) := by
  refine ⟨?_, popSound_of_keySoundOn⟩
  intro h pk c sig _ hacc
  let t : PopTranscript :=
    { channelId := c.channelId.bytes, challenge := c.nonce, signature := sig }
  exact h pk t trivial hacc

/-- **An accepted fresh session fills the wave-9 stored registration slot.**
The session/response is an H22 transcript, and the state-level registration
predicate of `AttributionGameTargets` holds for it. -/
theorem accepted_stored_registration {M : PrimitiveModel} {K : KeyModel M}
    {seed : ByteArray} {s : HandshakeState} {m : AcceptChannel}
    (hstore : StoredAccept K seed s m) {nonce : ByteArray}
    {r : PopResponse} (hacc : accepts M (sessionOfAccept m nonce) r) :
    StoredRegistration M K seed s m
      (sessionTranscript (sessionOfAccept m nonce) r) :=
  ⟨hstore, rfl, hacc⟩

/-- **The stored-payload attribution contract from an accepted response.**
Derived by constructing the wave-9 stored registration and invoking its
existing conditional attribution theorem; `PopSound` is itself derived from the
key-soundness law rather than assumed. -/
theorem accepted_stored_registration_attribution {M : PrimitiveModel}
    {K : KeyModel M} (hsound : PopKeySoundOn M K (fun _ => True))
    (hkb : KeyBinding M.ecdsaVerify) {seed : ByteArray}
    {s : HandshakeState} {m : AcceptChannel} (hstore : StoredAccept K seed s m)
    {nonce : ByteArray} {r : PopResponse}
    (hacc : accepts M (sessionOfAccept m nonce) r)
    (fundingTx : ByteArray) (hdom : K.correctOn (fundingTag ++ fundingTx)) :
    ∃ sk : SecretKey,
      K.Owns m.fundingPubKey sk ∧
        M.ecdsaVerify m.fundingPubKey (fundingTag ++ fundingTx)
          (K.sign sk (fundingTag ++ fundingTx)) = true ∧
        (∀ pk' : PubKey,
          M.ecdsaVerify pk' (fundingTag ++ fundingTx)
            (K.sign sk (fundingTag ++ fundingTx)) = true →
          pk' = m.fundingPubKey) :=
  LnLean.Proofs.Crypto.AttributionGameTargets.stored_registration_funding_attribution
    K (popSound_of_keySoundOn hsound) hkb
    (accepted_stored_registration hstore hacc) fundingTx hdom

/-! ## 5. What the algebraic model cannot derive -/

/-- `PopKeySoundOn` does not imply signature provenance.  The pinned verifier
accepts any signature on one fixed message under one fixed key, and the pinned
key model signs every message with the all-zero 64-byte signature.  A one-byte
signature is therefore accepted but is not the honest signature of any key
generation pair.  Hence `PopProducedBy`/extraction is strictly stronger than
key soundness. -/
theorem keySound_not_provenance (M₀ : PrimitiveModel) (k₀ : PubKey) :
    ∃ (M : PrimitiveModel) (K : KeyModel M) (c : PopChallenge)
      (sig : EcdsaSig),
      EufCma M.ecdsaVerify ∧
        PopKeySoundOn M K (fun _ => True) ∧
        M.ecdsaVerify k₀ (challengeMessage c) sig = true ∧
        (∀ sk : SecretKey, K.Owns k₀ sk →
          sig ≠ K.sign sk (challengeMessage c)) := by
  let c : PopChallenge :=
    { channelId := ChannelId.zero, nonce := ByteArray.empty }
  let d₀ : ByteArray := challengeMessage c
  let M : PrimitiveModel := pinnedModel M₀ k₀ d₀
  let K : KeyModel M := pinnedKeyModel M₀ k₀ d₀
  let sig : EcdsaSig := ⟨ByteArray.mk #[0x01]⟩
  refine ⟨M, K, c, sig, pinnedVerify_eufCma k₀ d₀, ?_, ?_, ?_⟩
  · intro pk c' sig' _ hacc
    have hpair : pk.bytes = k₀.bytes ∧ challengeMessage c' = d₀ := by
      simpa [M, pinnedModel, pinnedVerify, decide_eq_true_eq,
        Bool.and_eq_true] using hacc
    refine ⟨⟨ByteArray.empty⟩, ByteArray.empty, ?_, rfl⟩
    show k₀ = pk
    exact pubKey_ext hpair.1.symm
  · show pinnedVerify k₀ d₀ k₀ (challengeMessage c) sig = true
    simp [pinnedVerify, d₀]
  · intro sk _ hsig
    have hbytes : sig.bytes = (K.sign sk (challengeMessage c)).bytes :=
      congrArg EcdsaSig.bytes hsig
    have hzero : (K.sign sk (challengeMessage c)).bytes = zeros 64 := rfl
    rw [hzero] at hbytes
    have hne : sig.bytes ≠ zeros 64 := by
      show (ByteArray.mk #[0x01] : ByteArray) ≠ zeros 64
      decide
    exact hne hbytes

/-- `PopKeySoundOn` does not imply `KeyBinding`: H22's two-key model has PoP
soundness but one message/signature verifies under two distinct keys. -/
theorem keySound_not_keyBinding (M₀ : PrimitiveModel) :
    ∃ (M : PrimitiveModel) (K : KeyModel M),
      EufCma M.ecdsaVerify ∧
        PopKeySoundOn M K (fun _ => True) ∧
        ¬ KeyBinding M.ecdsaVerify := by
  obtain ⟨M, K, heuf, hsound, hnk⟩ := popSound_not_keyBinding M₀
  exact ⟨M, K, heuf, (popSound_iff_keySound K).1 hsound, hnk⟩

/-- `EufCma` + `KeyBinding` + total signing completeness do not imply the PoP
key-soundness law.  Re-exported from H22's sharp separation; this module does not
claim the missing knowledge-soundness property. -/
theorem keyBinding_completeness_not_keySound (M₀ : PrimitiveModel) :
    ∃ (M : PrimitiveModel) (K : KeyModel M),
      EufCma M.ecdsaVerify ∧
        KeyBinding M.ecdsaVerify ∧
        (∀ msg : ByteArray, K.correctOn msg) ∧
        ¬ PopKeySoundOn M K (fun _ => True) := by
  obtain ⟨M, K, heuf, hkb, hcomp, hnsound⟩ :=
    keyBinding_completeness_not_popSound M₀
  exact ⟨M, K, heuf, hkb, hcomp,
    fun h => hnsound ((popSound_iff_keySound K).2 h)⟩

/-! ## 6. Sharp negatives: replay and the hypotheses that prevent it -/

/-- The "unbound" verifier: it verifies the responder's claimed challenge and
never compares it with the session challenge. -/
def acceptsClaimed (M : PrimitiveModel) (s : PopSession)
    (r : PopResponse) : Prop :=
  M.ecdsaVerify s.expectedKey (challengeMessage r.challenge) r.signature = true

/-- The "no-nonce" verifier: its signed message omits the freshness nonce. -/
def challengeMessageNoNonce (c : PopChallenge) : ByteArray :=
  popTag ++ c.channelId.bytes

/-- The no-nonce verifier. -/
def acceptsNoNonce (M : PrimitiveModel) (s : PopSession)
    (r : PopResponse) : Prop :=
  M.ecdsaVerify s.expectedKey (challengeMessageNoNonce s.challenge)
    r.signature = true

/-- **Replay when the session challenge is not checked.**  An old response
carrying challenge `c₁` is accepted by a *different* session whose challenge is
`c₂`, because the unbound verifier reads the challenge from the response. -/
theorem unbound_replay_accepts (M₀ : PrimitiveModel) (k₀ : PubKey) :
    ∃ (M : PrimitiveModel) (c₁ c₂ : PopChallenge) (r : PopResponse),
      c₁ ≠ c₂ ∧
        acceptsClaimed M (sessionOfKey k₀ c₁) r ∧
        acceptsClaimed M (sessionOfKey k₀ c₂) r := by
  let c₁ : PopChallenge :=
    { channelId := ChannelId.zero, nonce := ByteArray.empty }
  let c₂ : PopChallenge :=
    { channelId := ChannelId.zero, nonce := ByteArray.mk #[0x00] }
  let M : PrimitiveModel := selfSigModel M₀ k₀
  let r : PopResponse :=
    { challenge := c₁, signature := ⟨challengeMessage c₁⟩ }
  have hne : c₁ ≠ c₂ := by
    intro h
    have hs : c₁.nonce.size = c₂.nonce.size :=
      congrArg (fun c : PopChallenge => c.nonce.size) h
    have h₁s : c₁.nonce.size = 0 := rfl
    have h₂s : c₂.nonce.size = 1 := rfl
    omega
  refine ⟨M, c₁, c₂, r, hne, ?_, ?_⟩
  · show selfSigVerify k₀ k₀ (challengeMessage c₁) r.signature = true
    simp [r, selfSigVerify]
  · show selfSigVerify k₀ k₀ (challengeMessage r.challenge) r.signature = true
    simp [r, selfSigVerify]

/-- **Replay when the nonce is not signed.**  With the same channel id but
distinct nonces, the no-nonce verifier accepts the same response in both
sessions.  The freshness nonce must be part of the signed bytes. -/
theorem nonceFree_replay_accepts (M₀ : PrimitiveModel) (k₀ : PubKey) :
    ∃ (M : PrimitiveModel) (c₁ c₂ : PopChallenge) (r : PopResponse),
      c₁ ≠ c₂ ∧ c₁.channelId = c₂.channelId ∧
        acceptsNoNonce M (sessionOfKey k₀ c₁) r ∧
        acceptsNoNonce M (sessionOfKey k₀ c₂) r := by
  let c₁ : PopChallenge :=
    { channelId := ChannelId.zero, nonce := ByteArray.empty }
  let c₂ : PopChallenge :=
    { channelId := ChannelId.zero, nonce := ByteArray.mk #[0x00] }
  let M : PrimitiveModel := selfSigModel M₀ k₀
  let r : PopResponse :=
    { challenge := c₁, signature := ⟨challengeMessageNoNonce c₁⟩ }
  have hne : c₁ ≠ c₂ := by
    intro h
    have hs : c₁.nonce.size = c₂.nonce.size :=
      congrArg (fun c : PopChallenge => c.nonce.size) h
    have h₁s : c₁.nonce.size = 0 := rfl
    have h₂s : c₂.nonce.size = 1 := rfl
    omega
  refine ⟨M, c₁, c₂, r, hne, rfl, ?_, ?_⟩
  · show selfSigVerify k₀ k₀ (challengeMessageNoNonce c₁) r.signature = true
    simp [r, selfSigVerify]
  · show selfSigVerify k₀ k₀ (challengeMessageNoNonce c₂) r.signature = true
    simp [r, selfSigVerify, challengeMessageNoNonce, c₁, c₂]

/-- **Without the fixed-width discipline the encoding collides.**  The same
`channelId ++ nonce` bytes are obtained from two different splits, exactly as in
H22's split counterexample.  Both challenges fail `Valid`, which is why the
injectivity theorem requires it. -/
theorem challengeMessage_not_injective_without_valid :
    ∃ c₁ c₂ : PopChallenge,
      c₁ ≠ c₂ ∧ ¬ c₁.Valid ∧ ¬ c₂.Valid ∧
        challengeMessage c₁ = challengeMessage c₂ := by
  let c₁ : PopChallenge :=
    { channelId := ⟨ByteArray.mk #[0x61]⟩, nonce := ByteArray.mk #[0x62, 0x63] }
  let c₂ : PopChallenge :=
    { channelId := ⟨ByteArray.mk #[0x61, 0x62]⟩, nonce := ByteArray.mk #[0x63] }
  have hne : c₁ ≠ c₂ := by
    intro h
    have hs : c₁.channelId.bytes.size = c₂.channelId.bytes.size :=
      congrArg (fun c : PopChallenge => c.channelId.bytes.size) h
    have h₁s : c₁.channelId.bytes.size = 1 := rfl
    have h₂s : c₂.channelId.bytes.size = 2 := rfl
    omega
  have hnot₁ : ¬ c₁.Valid := by
    intro hv
    have hs : c₁.channelId.bytes.size = 1 := rfl
    exact absurd (hv.1.symm.trans hs) (by decide)
  have hnot₂ : ¬ c₂.Valid := by
    intro hv
    have hs : c₂.channelId.bytes.size = 2 := rfl
    exact absurd (hv.1.symm.trans hs) (by decide)
  refine ⟨c₁, c₂, hne, hnot₁, hnot₂, ?_⟩
  show popTag ++ ByteArray.mk #[0x61] ++ ByteArray.mk #[0x62, 0x63] =
    popTag ++ ByteArray.mk #[0x61, 0x62] ++ ByteArray.mk #[0x63]
  rw [ByteArray.append_assoc, ByteArray.append_assoc]
  decide

/-- **The session-bound verifier is also attackable without `Valid`.**  Two
non-valid challenges with colliding encodings both accept the same response.
Thus `PopChallenge.Valid` is a necessary hypothesis of
`accepts_challenge_bound`, not a convenience. -/
theorem binding_fails_without_valid (M₀ : PrimitiveModel) (k₀ : PubKey) :
    ∃ (M : PrimitiveModel) (c₁ c₂ : PopChallenge) (r : PopResponse),
      c₁ ≠ c₂ ∧ ¬ c₁.Valid ∧ ¬ c₂.Valid ∧
        accepts M (sessionOfKey k₀ c₁) r ∧
        accepts M (sessionOfKey k₀ c₂) r := by
  obtain ⟨c₁, c₂, hne, hn₁, hn₂, hmsg⟩ :=
    challengeMessage_not_injective_without_valid
  let M : PrimitiveModel := selfSigModel M₀ k₀
  let r : PopResponse := { challenge := c₁, signature := ⟨challengeMessage c₁⟩ }
  refine ⟨M, c₁, c₂, r, hne, hn₁, hn₂, ?_, ?_⟩
  · show selfSigVerify k₀ k₀ (challengeMessage c₁) r.signature = true
    simp [r, selfSigVerify]
  · show selfSigVerify k₀ k₀ (challengeMessage c₂) r.signature = true
    rw [← hmsg]
    simp [r, selfSigVerify]

/-- If two sessions issue the same challenge, the same response is accepted by
both.  Session identity (`sessionId`) does not help; the freshness nonce is the
only separator. -/
theorem replay_of_same_challenge {M : PrimitiveModel} {s₁ s₂ : PopSession}
    {r : PopResponse} (hch : s₁.challenge = s₂.challenge)
    (hkey : s₁.expectedKey = s₂.expectedKey)
    (hacc : accepts M s₁ r) :
    accepts M s₂ r := by
  simpa [accepts, hch, hkey] using hacc

/-- **Replay when a challenge is reused.**  Two distinct sessions with different
session handles but the same challenge both accept one response.  `FreshOn`
is exactly the hypothesis that excludes this situation; the theorem is the
mechanised reason a verifier must never issue a challenge twice. -/
theorem repeated_challenge_replay (M₀ : PrimitiveModel) (k₀ : PubKey) :
    ∃ (M : PrimitiveModel) (s₁ s₂ : PopSession) (r : PopResponse),
      s₁ ≠ s₂ ∧ s₁.sessionId ≠ s₂.sessionId ∧
        s₁.challenge = s₂.challenge ∧ s₁.Valid ∧
        accepts M s₁ r ∧ accepts M s₂ r := by
  let c : PopChallenge :=
    { channelId := ChannelId.zero, nonce := zeros 32 }
  let M : PrimitiveModel := selfSigModel M₀ k₀
  let r : PopResponse := { challenge := c, signature := ⟨challengeMessage c⟩ }
  let s₁ : PopSession :=
    { sessionId := ByteArray.empty, challenge := c, expectedKey := k₀ }
  let s₂ : PopSession :=
    { sessionId := ByteArray.mk #[0x00], challenge := c, expectedKey := k₀ }
  have hne : s₁ ≠ s₂ := by
    intro h
    have hs : s₁.sessionId.size = s₂.sessionId.size :=
      congrArg (fun s : PopSession => s.sessionId.size) h
    have h₁s : s₁.sessionId.size = 0 := rfl
    have h₂s : s₂.sessionId.size = 1 := rfl
    omega
  have hid : s₁.sessionId ≠ s₂.sessionId := by
    intro h
    have hs : s₁.sessionId.size = s₂.sessionId.size :=
      congrArg ByteArray.size h
    have h₁s : s₁.sessionId.size = 0 := rfl
    have h₂s : s₂.sessionId.size = 1 := rfl
    omega
  have hvalid : s₁.Valid := by
    show c.Valid
    refine ⟨?_, ?_⟩
    · show (ChannelId.zero).bytes.size = 32
      rfl
    · show (zeros 32).size = 32
      decide
  refine ⟨M, s₁, s₂, r, hne, hid, rfl, hvalid, ?_, ?_⟩
  · show selfSigVerify k₀ k₀ (challengeMessage c) r.signature = true
    simp [r, selfSigVerify]
  · show selfSigVerify k₀ k₀ (challengeMessage c) r.signature = true
    simp [r, selfSigVerify]

/-! ## 7. Non-vacuity -/

/-- **The positive protocol contract is not vacuous.**  There is a concrete
C3/`KeyBinding` model with an extraction-sound PoP protocol, a valid challenge
bound to an `accept_channel`, an honest accepted response for the advertised
funding key, possession of that key, and funding-signature attribution. -/
theorem protocol_nonvacuous (M₀ : PrimitiveModel) (k₀ : PubKey) :
    ∃ (M : PrimitiveModel) (K : KeyModel M) (m : AcceptChannel)
      (c : PopChallenge) (r : PopResponse) (seed : ByteArray)
      (fundingTx : ByteArray),
      EufCma M.ecdsaVerify ∧ KeyBinding M.ecdsaVerify ∧
        c.Valid ∧ AdvertisesKey K seed m ∧
        c.channelId = m.temporaryChannelId ∧
        accepts M (sessionOfAccept m c.nonce) r ∧
        PopKeySoundOn M K (fun _ => True) ∧
        PopExtractionOn M K (fun _ => True) ∧
        (∃ sk : SecretKey, K.Owns m.fundingPubKey sk) ∧
        K.correctOn (fundingTag ++ fundingTx) ∧
        (∀ pk' : PubKey,
          M.ecdsaVerify pk' (fundingTag ++ fundingTx)
            (K.sign (K.secretOfSeed seed) (fundingTag ++ fundingTx)) = true →
          pk' = m.fundingPubKey) := by
  let M : PrimitiveModel := selfSigModel M₀ k₀
  let K : KeyModel M := selfSigKeyModel M₀ k₀
  let m : AcceptChannel := acceptChannelWithFundingKey k₀
  let c : PopChallenge :=
    { channelId := m.temporaryChannelId, nonce := zeros 32 }
  let seed : ByteArray := ByteArray.empty
  let r : PopResponse := honestResponse K seed c
  have hvalid : c.Valid := by
    refine ⟨?_, ?_⟩
    · show (ChannelId.zero).bytes.size = 32
      rfl
    · show (zeros 32).size = 32
      decide
  have hadv : AdvertisesKey K seed m := by
    show m.fundingPubKey = K.publicOfSeed seed
    rfl
  have hacc : accepts M (sessionOfAccept m c.nonce) r := by
    have hdom : K.correctOn (challengeMessage c) := trivial
    have h := advertised_honest_completeness K hadv c.nonce hdom
    simpa [r, c, challengeOfAccept] using h
  have hext : PopExtractionOn M K (fun _ => True) := by
    intro pk c' sig _ hver
    have hpair : pk.bytes = k₀.bytes ∧ sig.bytes = challengeMessage c' := by
      simpa [M, selfSigModel, selfSigVerify, decide_eq_true_eq,
        Bool.and_eq_true] using hver
    refine ⟨ByteArray.empty, ?_, ?_⟩
    · show pk = K.publicOfSeed ByteArray.empty
      rw [show K.publicOfSeed ByteArray.empty = k₀ from rfl]
      exact pubKey_ext hpair.1
    · show sig = K.sign (K.secretOfSeed ByteArray.empty) (challengeMessage c')
      rw [show K.secretOfSeed ByteArray.empty = ⟨ByteArray.empty⟩ from rfl]
      show sig = ⟨challengeMessage c'⟩
      cases sig
      simpa using hpair.2
  have hsound : PopKeySoundOn M K (fun _ => True) :=
    popKeySoundOn_of_extraction hext
  have hfund : ∀ pk' : PubKey,
      M.ecdsaVerify pk' (fundingTag ++ ByteArray.empty)
        (K.sign (K.secretOfSeed seed) (fundingTag ++ ByteArray.empty)) = true →
      pk' = m.fundingPubKey := by
    intro pk' hver
    have hpair : pk'.bytes = k₀.bytes ∧
        (K.sign (K.secretOfSeed seed) (fundingTag ++ ByteArray.empty)).bytes =
          (fundingTag ++ ByteArray.empty) := by
      simpa [M, K, selfSigModel, selfSigVerify, seed, decide_eq_true_eq,
        Bool.and_eq_true] using hver
    rw [pubKey_ext hpair.1]
    show k₀ = m.fundingPubKey
    exact (acceptChannelWithFundingKey_fundingPubKey k₀).symm
  refine ⟨M, K, m, c, r, seed, ByteArray.empty, M.ecdsa_eufCma,
    selfSigVerify_keyBinding k₀, hvalid, hadv, rfl, hacc, hsound, hext,
    ?_, trivial, hfund⟩
  exact accepted_owns hsound trivial hacc

/-! ## 8. Summary -/

/-- Bundled faithful reading of the concrete PoP protocol:

1. a response accepted by two same-key sessions forces equal challenges
   (`Valid` + `EufCma` + injective encoding);
2. the honest signer's response is accepted for the advertised key;
3. key soundness on issued challenges yields possession, and hence (with
   `KeyBinding`) funding-key attribution;
4. extraction yields wave-9 `PopProducedBy` provenance;
5. an unbound verifier accepts a replayed response across sessions;
6. without `Valid`, the session-bound verifier accepts one response for two
   colliding challenges;
7. possession does not imply honest-signature provenance. -/
theorem pop_protocol_summary :
    (∀ {M : PrimitiveModel} {s₁ s₂ : PopSession} {r : PopResponse},
        s₁.Valid → s₂.Valid → s₁.expectedKey = s₂.expectedKey →
        accepts M s₁ r → accepts M s₂ r →
        s₁.challenge = s₂.challenge) ∧
      (∀ {M : PrimitiveModel} (K : KeyModel M) (seed : ByteArray)
        {m : AcceptChannel}, AdvertisesKey K seed m →
        ∀ (nonce : ByteArray),
          K.correctOn (challengeMessage (challengeOfAccept m nonce)) →
          accepts M (sessionOfAccept m nonce)
            (honestResponse K seed (challengeOfAccept m nonce))) ∧
      (∀ {M : PrimitiveModel} {K : KeyModel M}
        {Issued : PopChallenge → Prop}, PopKeySoundOn M K Issued →
        ∀ {s : PopSession} {r : PopResponse}, Issued s.challenge →
          accepts M s r → ∃ sk : SecretKey, K.Owns s.expectedKey sk) ∧
      (∀ {M : PrimitiveModel} {K : KeyModel M}
        {Issued : PopChallenge → Prop}, PopExtractionOn M K Issued →
        ∀ {s : PopSession} {r : PopResponse}, Issued s.challenge →
          accepts M s r → ∃ sk : SecretKey,
            K.Owns s.expectedKey sk ∧
              PopProducedBy K sk (sessionTranscript s r)) ∧
      (∀ _M₀ : PrimitiveModel, ∀ _k₀ : PubKey,
        ∃ (M : PrimitiveModel) (c₁ c₂ : PopChallenge) (r : PopResponse),
          c₁ ≠ c₂ ∧ acceptsClaimed M (sessionOfKey _k₀ c₁) r ∧
            acceptsClaimed M (sessionOfKey _k₀ c₂) r) ∧
      (∀ _M₀ : PrimitiveModel, ∀ _k₀ : PubKey,
        ∃ (M : PrimitiveModel) (c₁ c₂ : PopChallenge) (r : PopResponse),
          c₁ ≠ c₂ ∧ ¬ c₁.Valid ∧ ¬ c₂.Valid ∧
            accepts M (sessionOfKey _k₀ c₁) r ∧
            accepts M (sessionOfKey _k₀ c₂) r) ∧
      (∀ _M₀ : PrimitiveModel, ∀ _k₀ : PubKey,
        ∃ (M : PrimitiveModel) (K : KeyModel M) (c : PopChallenge)
          (sig : EcdsaSig),
          EufCma M.ecdsaVerify ∧ PopKeySoundOn M K (fun _ => True) ∧
            M.ecdsaVerify _k₀ (challengeMessage c) sig = true ∧
            (∀ sk : SecretKey, K.Owns _k₀ sk →
              sig ≠ K.sign sk (challengeMessage c))) :=
  ⟨fun {_M} {_s₁} {_s₂} {_r} hs₁ hs₂ hkey h₁ h₂ =>
      accepts_challenge_bound hs₁ hs₂ hkey h₁ h₂,
    fun {_M} K _seed {_m} hadv nonce hdom =>
      advertised_honest_completeness K hadv nonce hdom,
    fun {_M} {_K} {_Issued} hsound {_s} {_r} hiss hacc =>
      accepted_owns hsound hiss hacc,
    fun {_M} {_K} {_Issued} hext {_s} {_r} hiss hacc =>
      accepted_popProducedBy hext hiss hacc,
    fun M₀ k₀ => unbound_replay_accepts M₀ k₀,
    fun M₀ k₀ => binding_fails_without_valid M₀ k₀,
    fun M₀ k₀ => keySound_not_provenance M₀ k₀⟩

end LnLean.Proofs.Crypto.PopProtocolTargets
