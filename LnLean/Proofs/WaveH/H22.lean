/-
# H22 — proof-of-possession / registration for `accept_channel.funding_pubkey` (PR-01)

**Catalog issue.**  `PR-01` (P1): `FundingSigningLaw` and `KeyBinding` are
hypotheses.  Wave 7 added the secret-key/key-generation model
(`LnLean.Crypto.KeyModel`) and `KeyModelTargets`, which proves funding-key
attribution *conditional* on the external `AdvertisesKey` link and on
`KeyBinding`, and keeps the mechanised counterexample
`key_generation_not_key_attribution`: key generation + C3 do not attribute a
signature to a key pair.  `docs/OPEN-ISSUES.md` lists the next action as
"model a registration/proof-of-possession game".

**Result of this module.**  A proof-of-possession (PoP) registration model for
the `accept_channel.funding_pubkey` field.

1. `PopTranscript`, `popMessage` and `PopAccepted` model a channel-bound
   challenge `pop`-tagged signature over the registration challenge.  The
   challenge is a verifier-chosen nonce, and the accepted message is
   `popTag ++ temporary_channel_id ++ challenge`.  The concatenation has no
   length prefixes, so the split is not injective
   (`popMessage_split_not_injective`); ownership attribution is unaffected,
   but channel binding additionally requires a length-prefixed challenge or a
   fixed-width channel id.  This is stated as a caveat, not assumed away.
2. `Registration` and `register` model the verifier side: a registration is
   recorded only when the transcript is bound to the accept message's
   `temporary_channel_id` and the signature verifies under the advertised
   `funding_pubkey`.  No registration record is produced otherwise.
3. `PopSoundOn K Issued` is the **missing game** in its exact algebraic form:
   every verifying transcript on a verifier-issued challenge yields a secret
   key that key generation pairs with the advertised public key.  `PopSound`
   is the unrestricted form.
4. **Attribution under the model.**  Under `PopSound`, an accepted
   registration yields an owned secret key for `accept_channel.funding_pubkey`.
   Consequently the previously external `AdvertisesKey` hypothesis is
   *derived*, not assumed: `registered_advertises_generated_key`.  Under the
   unchanged `KeyBinding` hypothesis, every key that accepts the registered
   signer's funding signature is the advertised funding key.  The bundled
   contract is `registration_funding_attribution`.  At the handshake boundary,
   `registered_negotiation_key_owned` shows that the `remoteFundingKey` of the
   opener's `FundingNegotiation` is owned by a generated secret key whenever
   the received `accept_channel` was registered.
5. **The missing game is extraction, and it is not reducible to the available
   properties.**  `owns_of_honest_pop_signature` gives the extraction form:
   a transcript whose signature is the key's honest signature yields the
   secret key.  `keyBinding_completeness_not_popSound` proves the sharp
   negative: C3, `KeyBinding` and completeness on every message do **not**
   imply `PopSound`.  Key binding constrains the key for a fixed signature; it
   does not force an accepted signature to be the key's honest signature.  So
   the missing premise is a knowledge/extraction property of the registration
   signature itself, which a deployment must obtain from the signature
   scheme's knowledge soundness plus a fresh verifier challenge.
6. **Negative results (kept).**
   * `key_generation_not_key_attribution_retained` re-exports the existing
     `KeyModelTargets.key_generation_not_key_attribution` unchanged; it is not
     claimed away.
   * `pop_acceptance_not_possession` shows a transcript can verify under two
     distinct keys, one of which key generation cannot produce; accepting the
     registration is not possession, and `PopSound` fails in that model.
   * `popSound_not_keyBinding` shows PoP soundness does not imply key binding.
   * `keyBinding_completeness_not_popSound` shows key binding plus C3 plus
     completeness do not imply PoP soundness.
   Hence `PopSound` is independent of both C3 and `KeyBinding`, and the
   registration event is an extra premise, not a consequence of the wire field.
7. **Non-vacuity.**  `registration_contract_nonvacuous` gives a concrete
   model, key model, accept payload, transcript, registration record and
   funding message on which C3, `PopSound`, `KeyBinding`, `AdvertisesKey`, the
   registration event and the attribution conclusion all hold.

**What this module does not claim.**  No secp256k1 arithmetic, no DER/RFC 6979
encoding, no randomness or probability.  `PopSound` is an exact extraction law,
not a proved computational reduction: it is the algebraic form of the PoP game
and must be supplied (or instantiated by a concrete, knowledge-sound signature
scheme) by a deployment.  `register` models the verifier accepting a
transcript; it does not model the challenge-generation randomness, session
storage, or the set of used challenges.  The freshness discipline is recorded
as the `Issued` predicate of `PopSoundOn`, not proved.  Signature *provenance*
("this wire signature was produced by that party") is still not tracked; the
model proves key attribution (`KeyBinding`) and key possession (`PopSound`),
which is the strongest pair the symbolic model supports.  The PoP challenge
encoding has no length prefix, so the channel/challenge split is not injective
(`popMessage_split_not_injective`); channel binding therefore needs the
deployment's encoding discipline even though ownership attribution does not.

**BOLT sections.**  BOLT 2 §The `open_channel` Message and §The
`accept_channel` Message (`funding_pubkey`, `temporary_channel_id`), §The
`funding_created` Message and §The `funding_signed` Message.

**rust-lightning anchors (commit fe49009).**
* `lightning/src/ln/msgs.rs:371` — `AcceptChannel` (`funding_pubkey` field);
  `:403` — `FundingCreated`; `:420` — `FundingSigned`.
* `lightning/src/crypto/utils.rs:75-83` — ECDSA signing over a message digest.
* `lightning/src/util/message_signing.rs:83-89` — signature verification.
-/

import LnLean.Crypto.KeyModel
import LnLean.Crypto.Sig
import LnLean.Protocol.Handshake
import LnLean.Proofs.Crypto.EcdsaProps
import LnLean.Proofs.Crypto.KeyModelTargets
import LnLean.Proofs.WaveE.E06

namespace LnLean.Proofs.WaveH.H22

set_option autoImplicit false

open LnLean
open LnLean.Bitcoin
open LnLean.Crypto
open LnLean.Crypto.KeyModel
open LnLean.Protocol
open LnLean.Protocol.Handshake
open LnLean.Proofs.Crypto.KeyModelTargets

/-- The key-binding contract of `KeyModelTargets`, itself the unchanged
`LnLean.Proofs.WaveE.E06` definition.  It is restated here so that the name is
unambiguous with `LnLean.Crypto.KeyBinding` (the signature-layer copy). -/
abbrev KeyBinding (verify : PubKey → ByteArray → EcdsaSig → Bool) : Prop :=
  LnLean.Proofs.WaveE.E06.KeyBinding verify

/-- Public-key extensionality: a public key is its byte string. -/
theorem pubKey_ext {p q : PubKey} (h : p.bytes = q.bytes) : p = q := by
  cases p
  cases q
  simp_all

/-- Size of the empty byte string. -/
theorem size_empty_bytes : (ByteArray.empty : ByteArray).size = 0 := rfl

/-- Size of the one-byte zero string. -/
theorem size_singleton_zero : (ByteArray.mk #[0x00] : ByteArray).size = 1 := rfl

/-- Size of the two-byte witness key. -/
theorem size_pair_bytes : (ByteArray.mk #[0x01, 0x02] : ByteArray).size = 2 := rfl

/-! ## 1. The proof-of-possession transcript -/

/-- Domain-separation tag for the registration/proof-of-possession challenge
("pop").  It is distinct from the funding, commitment and close tags. -/
def popTag : ByteArray := ByteArray.mk #[0x70, 0x6f, 0x70]

theorem popTag_size : popTag.size = 3 := rfl

/-- The PoP domain is separate from the funding-signature domain. -/
theorem popTag_ne_fundingTag : popTag ≠ fundingTag := by
  intro h
  have hs : popTag.size = fundingTag.size := congrArg ByteArray.size h
  rw [popTag_size, fundingTag_size] at hs
  omega

/-- One proof-of-possession transcript: the channel binding, the
verifier-chosen challenge, and the signature over them. -/
structure PopTranscript where
  /-- `accept_channel.temporary_channel_id` bytes this transcript is for. -/
  channelId : ByteArray
  /-- The verifier-issued challenge nonce. -/
  challenge : ByteArray
  /-- The signature over `popMessage`. -/
  signature : EcdsaSig

/-- The exact signed message of a PoP transcript.  The `pop` tag, the channel
id and the challenge are all covered, so changing either field changes the
signed bytes.  The concatenation carries no length prefixes: two different
`(channelId, challenge)` splits can produce the same message
(`popMessage_split_not_injective`), so a deployment must length-prefix the
challenge (or fix the channel-id width) before treating the split as
injective.  Ownership attribution does not depend on that discipline; channel
binding does. -/
def popMessage (t : PopTranscript) : ByteArray :=
  popTag ++ t.channelId ++ t.challenge

/-- **The transcript split is not injective.**  With no length prefixes,
`channelId = "a", challenge = "bc"` and `channelId = "ab", challenge = "c"`
sign the same bytes.  This is a real caveat of the byte-level model, not a
proof of channel binding: a signature for one split is accepted for the other.
The registration contract records the transcript's `channelId` and checks it
against `temporary_channel_id`, so the remaining gap is exactly an encoding
discipline (challenge length prefix or fixed-width channel id). -/
theorem popMessage_split_not_injective :
    ∃ t₁ t₂ : PopTranscript,
      popMessage t₁ = popMessage t₂ ∧ t₁.channelId ≠ t₂.channelId := by
  refine ⟨⟨ByteArray.mk #[0x61], ByteArray.mk #[0x62, 0x63], ⟨zeros 64⟩⟩,
    ⟨ByteArray.mk #[0x61, 0x62], ByteArray.mk #[0x63], ⟨zeros 64⟩⟩, ?_, ?_⟩
  · show popTag ++ ByteArray.mk #[0x61] ++ ByteArray.mk #[0x62, 0x63] =
      popTag ++ ByteArray.mk #[0x61, 0x62] ++ ByteArray.mk #[0x63]
    rw [ByteArray.append_assoc, ByteArray.append_assoc]
    decide
  · intro h
    have hs : (ByteArray.mk #[0x61] : ByteArray).size =
        (ByteArray.mk #[0x61, 0x62] : ByteArray).size :=
      congrArg ByteArray.size h
    rw [show (ByteArray.mk #[0x61] : ByteArray).size = 1 from rfl,
      show (ByteArray.mk #[0x61, 0x62] : ByteArray).size = 2 from rfl] at hs
    omega

/-- The PoP verifier: does `t.signature` verify under `pk` on the transcript's
challenge message?  This is the registration check; it is *not* an ownership
proof by itself (see §5). -/
def PopAccepted (M : PrimitiveModel) (pk : PubKey) (t : PopTranscript) : Prop :=
  M.ecdsaVerify pk (popMessage t) t.signature = true

/-- Acceptance is a property of the signed message only, so a split collision
transfers an accepted transcript to the colliding split. -/
theorem popAccepted_of_popMessage_eq {M : PrimitiveModel} {pk : PubKey}
    {t₁ t₂ : PopTranscript} (hmsg : popMessage t₁ = popMessage t₂)
    (hsig : t₁.signature = t₂.signature)
    (h : PopAccepted M pk t₁) : PopAccepted M pk t₂ := by
  unfold PopAccepted at h ⊢
  rw [hmsg, hsig] at h
  exact h

@[simp] theorem popMessage_mk (channelId challenge : ByteArray)
    (signature : EcdsaSig) :
    popMessage ⟨channelId, challenge, signature⟩ =
      popTag ++ channelId ++ challenge := rfl

/-! ## 2. Verifier-side registration -/

/-- A recorded registration: the received `accept_channel` and the PoP
transcript that was accepted for its `funding_pubkey`. -/
structure Registration where
  /-- The received `accept_channel` whose `funding_pubkey` is registered. -/
  accept : AcceptChannel
  /-- The accepted PoP transcript. -/
  transcript : PopTranscript

/-- Register a received `accept_channel`.  Registration is refused (`none`)
unless the transcript is bound to the message's `temporary_channel_id` and its
signature verifies under the advertised `funding_pubkey`. -/
def register (M : PrimitiveModel) (a : AcceptChannel)
    (t : PopTranscript) : Option Registration :=
  if t.channelId = a.temporaryChannelId.bytes then
    if M.ecdsaVerify a.fundingPubKey (popMessage t) t.signature then
      some { accept := a, transcript := t }
    else none
  else none

/-- Characterisation of a successful registration. -/
theorem register_eq_some_iff {M : PrimitiveModel} {a : AcceptChannel}
    {t : PopTranscript} {r : Registration}
    (h : register M a t = some r) :
    t.channelId = a.temporaryChannelId.bytes ∧
      M.ecdsaVerify a.fundingPubKey (popMessage t) t.signature = true ∧
      r = { accept := a, transcript := t } := by
  unfold register at h
  by_cases hc : t.channelId = a.temporaryChannelId.bytes
  · by_cases hv : M.ecdsaVerify a.fundingPubKey (popMessage t) t.signature = true
    · simp only [hc, hv, ite_true, Option.some.injEq] at h
      exact ⟨hc, hv, h.symm⟩
    · simp [hc, hv] at h
  · simp [hc] at h

/-- A successful registration is bound to the accept message's temporary
channel id. -/
theorem register_channel_bound {M : PrimitiveModel} {a : AcceptChannel}
    {t : PopTranscript} {r : Registration} (h : register M a t = some r) :
    t.channelId = a.temporaryChannelId.bytes :=
  (register_eq_some_iff h).1

/-- A successful registration contains a verifying PoP transcript under the
advertised `funding_pubkey`. -/
theorem register_popAccepted {M : PrimitiveModel} {a : AcceptChannel}
    {t : PopTranscript} {r : Registration} (h : register M a t = some r) :
    PopAccepted M a.fundingPubKey t :=
  (register_eq_some_iff h).2.1

/-- A successful registration records exactly the received accept message. -/
theorem register_recorded_accept {M : PrimitiveModel} {a : AcceptChannel}
    {t : PopTranscript} {r : Registration} (h : register M a t = some r) :
    r.accept = a := by
  rw [(register_eq_some_iff h).2.2]

/-! ## 3. The missing game, stated exactly -/

/-- **The soundness obligation of the registration game, on an issued
challenge set.**  `PopSoundOn K Issued` says: for every public key, every
transcript over a *verifier-issued* challenge that verifies under that key
yields a secret key that key generation pairs with it.  This is the exact
algebraic form of the missing proof-of-possession game; the `Issued` predicate
is where the freshness discipline (verifier-chosen nonce, unused challenge)
lives. -/
def PopSoundOn {M : PrimitiveModel} (K : KeyModel M)
    (Issued : PopTranscript → Prop) : Prop :=
  ∀ (pk : PubKey) (t : PopTranscript), Issued t → PopAccepted M pk t →
    ∃ sk : SecretKey, K.Owns pk sk

/-- The unrestricted soundness obligation (every transcript counts).  It is
the strongest form and is what the positive attribution theorems consume. -/
def PopSound {M : PrimitiveModel} (K : KeyModel M) : Prop :=
  PopSoundOn K (fun _ => True)

/-- Soundness on a larger issued set implies soundness on a smaller one. -/
theorem popSoundOn_mono {M : PrimitiveModel} {K : KeyModel M}
    {Issued₁ Issued₂ : PopTranscript → Prop}
    (hsub : ∀ t : PopTranscript, Issued₁ t → Issued₂ t)
    (h : PopSoundOn K Issued₂) : PopSoundOn K Issued₁ :=
  fun pk t ht hac => h pk t (hsub t ht) hac

/-- Restriction to issued challenges is a weakening of `PopSound`. -/
theorem popSoundOn_of_popSound {M : PrimitiveModel} {K : KeyModel M}
    (h : PopSound K) (Issued : PopTranscript → Prop) :
    PopSoundOn K Issued :=
  popSoundOn_mono (fun _ _ => trivial) h

/-- `PopSound` is exactly `PopSoundOn` with the universal issued set. -/
theorem popSound_iff_popSoundOn_univ {M : PrimitiveModel} (K : KeyModel M) :
    PopSound K ↔ PopSoundOn K (fun _ => True) := Iff.rfl

/-! ## 4. Attribution under the registration model -/

/-- **Registration establishes possession.**  An accepted registration
transcript for `accept_channel.funding_pubkey` yields a secret key owned for
that public key, under the PoP soundness obligation. -/
theorem registration_owns_funding_key {M : PrimitiveModel} (K : KeyModel M)
    (hsound : PopSound K) {a : AcceptChannel} {t : PopTranscript}
    (hacc : PopAccepted M a.fundingPubKey t) :
    ∃ sk : SecretKey, K.Owns a.fundingPubKey sk :=
  hsound a.fundingPubKey t trivial hacc

/-- The registered accept message's funding key is owned. -/
theorem registered_owns_funding_key {M : PrimitiveModel} (K : KeyModel M)
    (hsound : PopSound K) {a : AcceptChannel} {t : PopTranscript}
    {r : Registration} (hreg : register M a t = some r) :
    ∃ sk : SecretKey, K.Owns a.fundingPubKey sk :=
  registration_owns_funding_key K hsound (register_popAccepted hreg)

/-- **The previously external `AdvertisesKey` hypothesis is derived.**  Under
PoP soundness, a registered `accept_channel` advertises a key that some seed
generates.  This is exactly the link `KeyModelTargets` had to assume. -/
theorem registered_advertises_generated_key {M : PrimitiveModel}
    (K : KeyModel M) (hsound : PopSound K) {a : AcceptChannel}
    {t : PopTranscript} {r : Registration} (hreg : register M a t = some r) :
    ∃ seed : ByteArray, AdvertisesKey K seed a := by
  obtain ⟨sk, seed, hpk, _⟩ := registered_owns_funding_key K hsound hreg
  exact ⟨seed, hpk.symm⟩

/-- An owned key signs funding messages correctly on the declared domain. -/
theorem owned_funding_signature_valid {M : PrimitiveModel} (K : KeyModel M)
    {pk : PubKey} {sk : SecretKey} (hown : K.Owns pk sk)
    (fundingTx : ByteArray) (hdom : K.correctOn (fundingTag ++ fundingTx)) :
    M.ecdsaVerify pk (fundingTag ++ fundingTx)
      (K.sign sk (fundingTag ++ fundingTx)) = true :=
  K.owns_verifies hown hdom

/-- **Signature attribution under `KeyBinding`.**  Any key that accepts the
registered signer's funding signature is the advertised funding key.  This is
the unchanged external `KeyBinding` hypothesis; it is not derived here. -/
theorem owned_funding_signature_attribution {M : PrimitiveModel}
    (K : KeyModel M) (hkb : KeyBinding M.ecdsaVerify) {pk : PubKey}
    {sk : SecretKey} (hown : K.Owns pk sk) (fundingTx : ByteArray)
    (hdom : K.correctOn (fundingTag ++ fundingTx)) {pk' : PubKey}
    (hver : M.ecdsaVerify pk' (fundingTag ++ fundingTx)
      (K.sign sk (fundingTag ++ fundingTx)) = true) :
    pk' = pk :=
  hkb pk' pk (fundingTag ++ fundingTx) _
    hver (owned_funding_signature_valid K hown fundingTx hdom)

/-- **The bundled registration/attribution contract.**  Under PoP soundness
and `KeyBinding`, an accepted registration gives:

* a secret key owned for `accept_channel.funding_pubkey`;
* the honest funding signature by that key, which verifies under the advertised
  funding key;
* every key that accepts that signature is the advertised funding key.

The `KeyBinding` half is unchanged from wave 7; the new half is that the
signer's key is *owned*, which the accept payload alone never established. -/
theorem registration_funding_attribution {M : PrimitiveModel}
    (K : KeyModel M) (hsound : PopSound K) (hkb : KeyBinding M.ecdsaVerify)
    {a : AcceptChannel} {t : PopTranscript} {r : Registration}
    (hreg : register M a t = some r) (fundingTx : ByteArray)
    (hdom : K.correctOn (fundingTag ++ fundingTx)) :
    ∃ sk : SecretKey, K.Owns a.fundingPubKey sk ∧
      M.ecdsaVerify a.fundingPubKey (fundingTag ++ fundingTx)
        (K.sign sk (fundingTag ++ fundingTx)) = true ∧
      (∀ pk' : PubKey,
        M.ecdsaVerify pk' (fundingTag ++ fundingTx)
          (K.sign sk (fundingTag ++ fundingTx)) = true →
        pk' = a.fundingPubKey) := by
  obtain ⟨sk, hown⟩ := registered_owns_funding_key K hsound hreg
  exact ⟨sk, hown,
    owned_funding_signature_valid K hown fundingTx hdom,
    fun pk' hver =>
      owned_funding_signature_attribution K hkb hown fundingTx hdom hver⟩

/-! ## 5. What the missing game actually is -/

/-- **Extraction form of PoP soundness.**  If a verifying transcript's
signature is the honest signature of some seed that generates the advertised
key, then that seed's secret key is owned.  This is the extraction warrant a
real proof-of-possession game must supply: acceptance must mean "produced with
the key's secret", not merely "some signature verified". -/
theorem owns_of_honest_pop_signature {M : PrimitiveModel} (K : KeyModel M)
    {pk : PubKey} {t : PopTranscript}
    (h : ∃ seed : ByteArray, pk = K.publicOfSeed seed ∧
      t.signature = K.sign (K.secretOfSeed seed) (popMessage t)) :
    ∃ sk : SecretKey, K.Owns pk sk := by
  obtain ⟨seed, hpk, _⟩ := h
  exact ⟨K.secretOfSeed seed, seed, hpk.symm, rfl⟩

/-- A verifier whose accepted signature is `message || public key`.  It is
injective in the message for a fixed key (C3) and in the key for a fixed
message/signature (key binding). -/
def keyedSigVerify : PubKey → ByteArray → EcdsaSig → Bool :=
  fun pk msg sig => decide (sig.bytes = msg ++ pk.bytes)

theorem keyedSigVerify_eufCma : EufCma keyedSigVerify := by
  intro pk m₁ m₂ s h₁ h₂
  simp only [keyedSigVerify, decide_eq_true_eq] at h₁ h₂
  exact append_right_cancel (h₁.symm.trans h₂)

theorem keyedSigVerify_keyBinding : KeyBinding keyedSigVerify := by
  intro pk₁ pk₂ msg sig h₁ h₂
  simp only [keyedSigVerify, decide_eq_true_eq] at h₁ h₂
  exact pubKey_ext (append_left_cancel (h₁.symm.trans h₂))

/-- Replace a model's ECDSA verifier by `keyedSigVerify`; C3 is re-proved. -/
def keyedSigModel (M₀ : PrimitiveModel) : PrimitiveModel :=
  { M₀ with
    ecdsaVerify := keyedSigVerify
    ecdsa_eufCma := keyedSigVerify_eufCma }

/-- The honest signer for `k₀`: the signature is `message || k₀`, and the
signer is complete on every message. -/
def keyedSigKeyModel (M₀ : PrimitiveModel) (k₀ : PubKey) :
    KeyModel (keyedSigModel M₀) where
  generate _ := { secret := ⟨ByteArray.empty⟩, pubkey := k₀ }
  sign _ msg := ⟨msg ++ k₀.bytes⟩
  correctOn _ := True
  verifies := by
    intro seed msg _
    show keyedSigVerify k₀ msg ⟨msg ++ k₀.bytes⟩ = true
    simp [keyedSigVerify]

/-- **C3 + key binding + signing completeness do not give PoP soundness.**
There is a model whose verifier is C3 and key-binding and whose honest signer is
complete on every message, and yet a transcript with signature
`popTag || k₁` verifies under a key `k₁` that key generation cannot produce.

Key binding constrains the key *for a fixed signature*; it does not force an
accepted signature to be the key's honest signature.  `PopSound` is therefore a
genuinely additional extraction premise, not a consequence of the three
properties already available.  This is the sharp statement of the missing game:
a knowledge/extraction property of the registration signature. -/
theorem keyBinding_completeness_not_popSound (M₀ : PrimitiveModel) :
    ∃ (M : PrimitiveModel) (K : KeyModel M),
      EufCma M.ecdsaVerify ∧ KeyBinding M.ecdsaVerify ∧
        (∀ msg : ByteArray, K.correctOn msg) ∧ ¬ PopSound K := by
  let k₀ : PubKey := ⟨ByteArray.empty⟩
  let k₁ : PubKey := ⟨ByteArray.mk #[0x00]⟩
  let M : PrimitiveModel := keyedSigModel M₀
  let K : KeyModel M := keyedSigKeyModel M₀ k₀
  have hk : k₁ ≠ k₀ := by
    intro h
    have hs : (ByteArray.mk #[0x00] : ByteArray).size =
        (ByteArray.empty : ByteArray).size :=
      congrArg (fun p : PubKey => p.bytes.size) h
    rw [size_singleton_zero, size_empty_bytes] at hs
    omega
  refine ⟨M, K, M.ecdsa_eufCma, keyedSigVerify_keyBinding,
    fun _ => trivial, ?_⟩
  intro hsound
  let t : PopTranscript :=
    { channelId := ByteArray.empty, challenge := ByteArray.empty,
      signature := ⟨popTag ++ k₁.bytes⟩ }
  have hacc : PopAccepted M k₁ t := by
    simp [PopAccepted, M, t, popMessage, keyedSigModel, keyedSigVerify]
  obtain ⟨sk, seed, hpk, _⟩ := hsound k₁ t trivial hacc
  have hk₀ : k₀ = k₁ := by
    simpa [K, keyedSigKeyModel, KeyModel.publicOfSeed] using hpk
  exact hk hk₀.symm

/-! ## 6. Handshake boundary: the negotiation key is owned -/

/-- **The opener's remote funding key is owned after registration.**  When the
opener has a `FundingNegotiation` (it sent `open_channel` and received
`accept_channel`), and the received accept message was registered, the
negotiation's `remoteFundingKey` is owned by a generated secret key.

The registration premise is stated as a function of the received accept
message so that the theorem is independent of how the verifier stores the
record. -/
theorem registered_negotiation_key_owned {M : PrimitiveModel} (K : KeyModel M)
    (hsound : PopSound K) {s : FundingPhase} {n : FundingNegotiation}
    (hn : s.openerNegotiation? = some n)
    (hreg : ∀ a : AcceptChannel, s.acceptReceived = some a →
      ∃ (t : PopTranscript) (r : Registration), register M a t = some r) :
    ∃ sk : SecretKey, K.Owns n.remoteFundingKey sk := by
  obtain ⟨o, a, _ho, ha, _hn, _hlocal, hremote⟩ :=
    fundingPhase_opener_keys hn
  obtain ⟨t, r, hreg'⟩ := hreg a ha
  obtain ⟨sk, hsk⟩ := registered_owns_funding_key K hsound hreg'
  exact ⟨sk, by rw [hremote]; exact hsk⟩

/-! ## 7. The retained counterexample -/

/-- **The wave-7 counterexample is retained unchanged.**  Key generation with
two distinct key pairs, secret-key signing correct on the funding message, and
C3 do **not** give key attribution: the signature of the second key pair
validates under the first key pair's advertised `funding_pubkey`, and the
model fails `KeyBinding`.  This module does not claim it away; the registration
model is an *additional* premise. -/
theorem key_generation_not_key_attribution_retained (M₀ : PrimitiveModel) :
    ∃ (M : PrimitiveModel) (K : KeyModel M) (m : AcceptChannel)
      (seed₁ seed₂ : ByteArray) (fundingTx : ByteArray),
      K.publicOfSeed seed₁ ≠ K.publicOfSeed seed₂ ∧
        K.secretOfSeed seed₁ ≠ K.secretOfSeed seed₂ ∧
        EufCma M.ecdsaVerify ∧
        AdvertisesKey K seed₁ m ∧
        K.correctOn (fundingTag ++ fundingTx) ∧
        M.ecdsaVerify m.fundingPubKey (fundingTag ++ fundingTx)
          (K.sign (K.secretOfSeed seed₂) (fundingTag ++ fundingTx)) = true ∧
        K.sign (K.secretOfSeed seed₁) (fundingTag ++ fundingTx) =
          K.sign (K.secretOfSeed seed₂) (fundingTag ++ fundingTx) ∧
        ¬ KeyBinding M.ecdsaVerify :=
  key_generation_not_key_attribution M₀

/-! ## 8. Negative results: what registration is not -/

/-- The verifier of the counterexample: it accepts exactly `d₀`, ignoring the
key and the signature.  It is C3 but not key-binding. -/
def cheatModel (M₀ : PrimitiveModel) : PrimitiveModel :=
  singleMessageEcdsaModel M₀ popTag

/-- The key model of the counterexample: it generates two distinct pairs
(`seed = empty` and `seed = [0]`), signs every message with the same
all-zero signature, and is complete exactly on `popTag`. -/
def cheatModelKey (M₀ : PrimitiveModel) : KeyModel (cheatModel M₀) :=
  cheatKeyModel M₀ popTag

/-- **Accepting a transcript is not possession.**  There is a full C3 model in
which one PoP transcript verifies under the advertised `funding_pubkey` and
under a *second*, distinct public key that key generation cannot produce.  So
the verification event `PopAccepted` extracts nothing; `PopSound` is the extra
premise, and it fails here.

The second key is chosen with a different byte length so the non-ownership
claim is a width fact, not an arithmetic accident of the toy verifier. -/
theorem pop_acceptance_not_possession (M₀ : PrimitiveModel) :
    ∃ (M : PrimitiveModel) (K : KeyModel M) (m : AcceptChannel)
      (t : PopTranscript) (pk' : PubKey) (seed₁ seed₂ : ByteArray),
      EufCma M.ecdsaVerify ∧
        AdvertisesKey K seed₁ m ∧
        K.publicOfSeed seed₁ ≠ K.publicOfSeed seed₂ ∧
        PopAccepted M m.fundingPubKey t ∧
        PopAccepted M pk' t ∧
        pk' ≠ m.fundingPubKey ∧
        (¬ ∃ sk : SecretKey, K.Owns pk' sk) ∧
        ¬ PopSound K := by
  let M : PrimitiveModel := cheatModel M₀
  let K : KeyModel M := cheatModelKey M₀
  let seed₁ : ByteArray := ByteArray.empty
  let seed₂ : ByteArray := ByteArray.mk #[0x00]
  let m : AcceptChannel := acceptChannelWithFundingKey (K.publicOfSeed seed₁)
  let pk' : PubKey := ⟨ByteArray.mk #[0x01, 0x02]⟩
  let t : PopTranscript :=
    { channelId := ByteArray.empty, challenge := ByteArray.empty,
      signature := ⟨zeros 64⟩ }
  have hpk₁ : K.publicOfSeed seed₁ = ⟨ByteArray.empty⟩ := by
    show (cheatKeyModel M₀ popTag).publicOfSeed ByteArray.empty = _
    exact cheatKeyModel_public_empty M₀ popTag
  have hpk₂ : K.publicOfSeed seed₂ = ⟨ByteArray.mk #[0x00]⟩ := by
    show (cheatKeyModel M₀ popTag).publicOfSeed (ByteArray.mk #[0x00]) = _
    exact cheatKeyModel_public_nonempty M₀ popTag
  have hdistinct : K.publicOfSeed seed₁ ≠ K.publicOfSeed seed₂ := by
    rw [hpk₁, hpk₂]
    intro h
    have hs : (ByteArray.empty : ByteArray).size =
        (ByteArray.mk #[0x00] : ByteArray).size :=
      congrArg (fun p : PubKey => p.bytes.size) h
    rw [size_empty_bytes, size_singleton_zero] at hs
    omega
  have hacc : PopAccepted M m.fundingPubKey t := by
    simp [PopAccepted, M, m, t, popMessage, cheatModel, seed₁,
      singleMessageEcdsaModel, singleMessageVerify]
  have hacc' : PopAccepted M pk' t := by
    simp [PopAccepted, M, pk', t, popMessage, cheatModel,
      singleMessageEcdsaModel, singleMessageVerify]
  have hpk' : pk' ≠ m.fundingPubKey := by
    intro h
    have hs : pk'.bytes.size = m.fundingPubKey.bytes.size :=
      congrArg (fun p : PubKey => p.bytes.size) h
    rw [show m.fundingPubKey = K.publicOfSeed seed₁ from rfl, hpk₁] at hs
    rw [show pk'.bytes.size = 2 from size_pair_bytes, size_empty_bytes] at hs
    omega
  have hgen : ∀ seed : ByteArray,
      (K.publicOfSeed seed).bytes.size = 0 ∨
        (K.publicOfSeed seed).bytes.size = 1 := by
    intro seed
    simp only [K, cheatModelKey, cheatKeyModel, KeyModel.publicOfSeed]
    split
    · left; rfl
    · right; rfl
  have hnotown : ¬ ∃ sk : SecretKey, K.Owns pk' sk := by
    rintro ⟨sk, seed, hseed, _⟩
    have hs : (K.publicOfSeed seed).bytes.size = 2 := by
      simpa [pk', size_pair_bytes] using
        congrArg (fun p : PubKey => p.bytes.size) hseed
    rcases hgen seed with h | h <;> omega
  refine ⟨M, K, m, t, pk', seed₁, seed₂, M.ecdsa_eufCma, ?_, hdistinct,
    hacc, hacc', hpk', hnotown, ?_⟩
  · show m.fundingPubKey = K.publicOfSeed seed₁
    rfl
  · intro hsound
    exact hnotown (hsound pk' t trivial hacc')

/-- Verifier accepting exactly the message `d₀` under either of two fixed
keys.  It is C3, and the same message/signature verifies under two distinct
keys, so it is not key-binding. -/
def twoKeyVerify (k₀ k₁ : PubKey) (d₀ : ByteArray) :
    PubKey → ByteArray → EcdsaSig → Bool :=
  fun pk msg _ =>
    decide (msg = d₀) &&
      (decide (pk.bytes = k₀.bytes) || decide (pk.bytes = k₁.bytes))

theorem twoKeyVerify_eufCma (k₀ k₁ : PubKey) (d₀ : ByteArray) :
    EufCma (twoKeyVerify k₀ k₁ d₀) := by
  intro pk m₁ m₂ s h₁ h₂
  simp only [twoKeyVerify, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq] at h₁ h₂
  rw [h₁.1, h₂.1]

/-- Replace a model's ECDSA verifier by `twoKeyVerify`; C3 is re-proved. -/
def twoKeyModel (M₀ : PrimitiveModel) (k₀ k₁ : PubKey) (d₀ : ByteArray) :
    PrimitiveModel :=
  { M₀ with
    ecdsaVerify := twoKeyVerify k₀ k₁ d₀
    ecdsa_eufCma := twoKeyVerify_eufCma k₀ k₁ d₀ }

/-- Deterministic generation of `k₀` from the empty seed and `k₁` from every
other seed. -/
def twoKeyGenerate (k₀ k₁ : PubKey) (seed : ByteArray) : KeyPair :=
  if seed.size = 0 then
    { secret := ⟨ByteArray.empty⟩, pubkey := k₀ }
  else
    { secret := ⟨ByteArray.mk #[0x00]⟩, pubkey := k₁ }

/-- A key model over `twoKeyVerify` whose two generated public keys are
exactly the two keys the verifier accepts. -/
def twoKeyKeyModel (M₀ : PrimitiveModel) (k₀ k₁ : PubKey) (d₀ : ByteArray) :
    KeyModel (twoKeyModel M₀ k₀ k₁ d₀) where
  generate := twoKeyGenerate k₀ k₁
  sign _ _ := ⟨zeros 64⟩
  correctOn msg := msg = d₀
  verifies := by
    intro seed msg h
    rw [h]
    dsimp only [twoKeyModel]
    unfold twoKeyGenerate
    split <;> simp [twoKeyVerify]

/-- **PoP soundness does not imply key binding.**  There is a C3 model where
`PopSound` holds (every accepted transcript belongs to one of the two generated
key pairs) and yet one message/signature verifies under two distinct public
keys.  So `PopSound` is not `KeyBinding`; both are needed for attribution. -/
theorem popSound_not_keyBinding (M₀ : PrimitiveModel) :
    ∃ (M : PrimitiveModel) (K : KeyModel M),
      EufCma M.ecdsaVerify ∧ PopSound K ∧ ¬ KeyBinding M.ecdsaVerify := by
  let k₀ : PubKey := ⟨ByteArray.empty⟩
  let k₁ : PubKey := ⟨ByteArray.mk #[0x00]⟩
  let M : PrimitiveModel := twoKeyModel M₀ k₀ k₁ popTag
  let K : KeyModel M := twoKeyKeyModel M₀ k₀ k₁ popTag
  have hk : k₀ ≠ k₁ := by
    intro h
    have hs : (ByteArray.empty : ByteArray).size =
        (ByteArray.mk #[0x00] : ByteArray).size :=
      congrArg (fun p : PubKey => p.bytes.size) h
    rw [size_empty_bytes, size_singleton_zero] at hs
    omega
  refine ⟨M, K, M.ecdsa_eufCma, ?_, ?_⟩
  · intro pk t _ hacc
    have hcases : pk.bytes = k₀.bytes ∨ pk.bytes = k₁.bytes := by
      simp only [PopAccepted, M, twoKeyModel, twoKeyVerify, Bool.and_eq_true,
        Bool.or_eq_true, decide_eq_true_eq] at hacc
      exact hacc.2
    rcases hcases with h | h
    · refine ⟨⟨ByteArray.empty⟩, ByteArray.empty, ?_, rfl⟩
      show (twoKeyGenerate k₀ k₁ ByteArray.empty).pubkey = pk
      simp [twoKeyGenerate]
      exact pubKey_ext h.symm
    · refine ⟨⟨ByteArray.mk #[0x00]⟩, ByteArray.mk #[0x00], ?_, rfl⟩
      show (twoKeyGenerate k₀ k₁ (ByteArray.mk #[0x00])).pubkey = pk
      simp [twoKeyGenerate]
      exact pubKey_ext h.symm
  · intro hkb
    have h₁ : twoKeyVerify k₀ k₁ popTag k₀ popTag ⟨zeros 64⟩ = true := by
      simp [twoKeyVerify]
    have h₂ : twoKeyVerify k₀ k₁ popTag k₁ popTag ⟨zeros 64⟩ = true := by
      simp [twoKeyVerify]
    exact hk (hkb k₀ k₁ popTag ⟨zeros 64⟩ h₁ h₂)

/-! ## 9. Non-vacuity of the registration contract -/

/-- Toy verifier for the non-vacuity witness: the signature bytes must equal
the message and the key must be `k₀`.  This is a logical witness for the
registration contract, not an ECDSA implementation. -/
def selfSigVerify (k₀ : PubKey) : PubKey → ByteArray → EcdsaSig → Bool :=
  fun pk msg sig => decide (pk.bytes = k₀.bytes && sig.bytes = msg)

theorem selfSigVerify_eufCma (k₀ : PubKey) : EufCma (selfSigVerify k₀) := by
  intro pk m₁ m₂ s h₁ h₂
  simp only [selfSigVerify, decide_eq_true_eq, Bool.and_eq_true] at h₁ h₂
  exact h₁.2.symm.trans h₂.2

theorem selfSigVerify_keyBinding (k₀ : PubKey) :
    KeyBinding (selfSigVerify k₀) := by
  intro pk₁ pk₂ msg sig h₁ h₂
  simp only [selfSigVerify, decide_eq_true_eq, Bool.and_eq_true] at h₁ h₂
  exact pubKey_ext (h₁.1.trans h₂.1.symm)

def selfSigModel (M₀ : PrimitiveModel) (k₀ : PubKey) : PrimitiveModel :=
  { M₀ with
    ecdsaVerify := selfSigVerify k₀
    ecdsa_eufCma := selfSigVerify_eufCma k₀ }

/-- The key model of the witness: every seed generates `k₀`, the signature is
the message, and the signer is complete on every message. -/
def selfSigKeyModel (M₀ : PrimitiveModel) (k₀ : PubKey) :
    KeyModel (selfSigModel M₀ k₀) where
  generate seed := { secret := ⟨seed⟩, pubkey := k₀ }
  sign _ msg := ⟨msg⟩
  correctOn _ := True
  verifies := by
    intro seed msg _
    show selfSigVerify k₀ k₀ msg ⟨msg⟩ = true
    simp [selfSigVerify]

/-- **The registration contract is not vacuous.**  There is a concrete C3,
key-binding model with PoP soundness, an accepted registration for an
`accept_channel` that advertises a generated funding key, and a funding message
on which the registered signer's signature verifies under exactly the
advertised key. -/
theorem registration_contract_nonvacuous (M₀ : PrimitiveModel) (k₀ : PubKey) :
    ∃ (M : PrimitiveModel) (K : KeyModel M) (a : AcceptChannel)
      (t : PopTranscript) (r : Registration) (fundingTx : ByteArray),
      EufCma M.ecdsaVerify ∧ PopSound K ∧ KeyBinding M.ecdsaVerify ∧
        AdvertisesKey K ByteArray.empty a ∧
        register M a t = some r ∧
        K.correctOn (fundingTag ++ fundingTx) ∧
        (∀ pk' : PubKey,
          M.ecdsaVerify pk' (fundingTag ++ fundingTx)
            (K.sign (K.secretOfSeed ByteArray.empty)
              (fundingTag ++ fundingTx)) = true →
          pk' = a.fundingPubKey) := by
  let M : PrimitiveModel := selfSigModel M₀ k₀
  let K : KeyModel M := selfSigKeyModel M₀ k₀
  let a : AcceptChannel := acceptChannelWithFundingKey k₀
  let cid : ByteArray := a.temporaryChannelId.bytes
  let msg : ByteArray := popTag ++ cid
  let t : PopTranscript :=
    { channelId := cid, challenge := ByteArray.empty, signature := ⟨msg⟩ }
  have hpop : PopSound K := by
    intro pk t _ hacc
    have hpair : pk.bytes = k₀.bytes ∧ t.signature.bytes = popMessage t := by
      simpa [PopAccepted, M, selfSigModel, selfSigVerify] using hacc
    refine ⟨⟨ByteArray.empty⟩, ByteArray.empty, ?_, rfl⟩
    show k₀ = pk
    exact pubKey_ext hpair.1.symm
  have hadv : AdvertisesKey K ByteArray.empty a := by
    show a.fundingPubKey = K.publicOfSeed ByteArray.empty
    rw [show a.fundingPubKey = k₀ from
      acceptChannelWithFundingKey_fundingPubKey k₀]
    show k₀ = K.publicOfSeed ByteArray.empty
    rfl
  have hreg : register M a t = some { accept := a, transcript := t } := by
    show register M a t = some { accept := a, transcript := t }
    simp [register, t, cid, msg, a, M, selfSigModel, selfSigVerify, popMessage]
  have hattr : ∀ pk' : PubKey,
      M.ecdsaVerify pk' (fundingTag ++ ByteArray.empty)
        (K.sign (K.secretOfSeed ByteArray.empty)
          (fundingTag ++ ByteArray.empty)) = true →
      pk' = a.fundingPubKey := by
    intro pk' hver
    have hpair : pk'.bytes = k₀.bytes ∧
        (fundingTag ++ ByteArray.empty) = (fundingTag ++ ByteArray.empty) := by
      simpa [M, selfSigModel, selfSigVerify, K, selfSigKeyModel,
        KeyModel.secretOfSeed] using hver
    calc pk' = k₀ := pubKey_ext hpair.1
      _ = a.fundingPubKey :=
        (acceptChannelWithFundingKey_fundingPubKey k₀).symm
  exact ⟨M, K, a, t, { accept := a, transcript := t }, ByteArray.empty,
    M.ecdsa_eufCma, hpop, selfSigVerify_keyBinding k₀, hadv, hreg, trivial,
    hattr⟩

/-! ## 10. Summary -/

/-- Bundled faithful reading of `PR-01` under the registration model:

1. an accepted registration plus PoP soundness yields an owned secret key for
   the advertised `funding_pubkey`, hence derives `AdvertisesKey`;
2. under `PopSound` and `KeyBinding`, the registered signer's funding signature
   attributes to exactly the advertised funding key;
3. PoP soundness is not implied by C3, `KeyBinding`, or completeness; the
   separation is `keyBinding_completeness_not_popSound`;
4. the wave-7 negative result is retained;
5. the positive contract has a concrete non-vacuous instance. -/
theorem registration_model_summary :
    (∀ (M : PrimitiveModel) (K : KeyModel M) (_hsound : PopSound K)
        (a : AcceptChannel) (t : PopTranscript) (r : Registration),
        register M a t = some r →
        (∃ sk : SecretKey, K.Owns a.fundingPubKey sk) ∧
          (∃ seed : ByteArray, AdvertisesKey K seed a)) ∧
      (∀ (M : PrimitiveModel) (K : KeyModel M) (_hsound : PopSound K)
        (_hkb : KeyBinding M.ecdsaVerify)
        (a : AcceptChannel) (t : PopTranscript) (r : Registration)
        (fundingTx : ByteArray),
        register M a t = some r →
        K.correctOn (fundingTag ++ fundingTx) →
        ∃ sk : SecretKey, K.Owns a.fundingPubKey sk ∧
          M.ecdsaVerify a.fundingPubKey (fundingTag ++ fundingTx)
            (K.sign sk (fundingTag ++ fundingTx)) = true ∧
          (∀ pk' : PubKey,
            M.ecdsaVerify pk' (fundingTag ++ fundingTx)
              (K.sign sk (fundingTag ++ fundingTx)) = true →
            pk' = a.fundingPubKey)) ∧
      (∀ (_M₀ : PrimitiveModel),
        ∃ (M : PrimitiveModel) (K : KeyModel M) (m : AcceptChannel)
          (seed₁ seed₂ : ByteArray) (fundingTx : ByteArray),
          K.publicOfSeed seed₁ ≠ K.publicOfSeed seed₂ ∧
            EufCma M.ecdsaVerify ∧
            AdvertisesKey K seed₁ m ∧
            M.ecdsaVerify m.fundingPubKey (fundingTag ++ fundingTx)
              (K.sign (K.secretOfSeed seed₂) (fundingTag ++ fundingTx)) = true ∧
            ¬ KeyBinding M.ecdsaVerify) ∧
      (∀ (_M₀ : PrimitiveModel) (_k₀ : PubKey),
        ∃ (M : PrimitiveModel) (K : KeyModel M) (a : AcceptChannel)
          (t : PopTranscript) (r : Registration),
          EufCma M.ecdsaVerify ∧ PopSound K ∧ KeyBinding M.ecdsaVerify ∧
            register M a t = some r) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro M K _hsound a t r hreg
    exact ⟨registered_owns_funding_key K _hsound hreg,
      registered_advertises_generated_key K _hsound hreg⟩
  · intro M K _hsound _hkb a t r fundingTx hreg hdom
    exact registration_funding_attribution K _hsound _hkb hreg fundingTx hdom
  · intro _M₀
    obtain ⟨M, K, m, s₁, s₂, tx, hp, _hs, he, ha, _hc, hv, _heq, hnk⟩ :=
      key_generation_not_key_attribution_retained _M₀
    exact ⟨M, K, m, s₁, s₂, tx, hp, he, ha, hv, hnk⟩
  · intro _M₀ _k₀
    obtain ⟨M, K, a, t, r, _tx, he, hpop, hkb, _ha, hreg, _hc, _hattr⟩ :=
      registration_contract_nonvacuous _M₀ _k₀
    exact ⟨M, K, a, t, r, he, hpop, hkb, hreg⟩

end LnLean.Proofs.WaveH.H22
