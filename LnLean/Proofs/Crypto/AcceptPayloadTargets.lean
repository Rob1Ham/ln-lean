/-
# `accept_channel` payload registration and key attribution (PR-01, wave 8)

**Catalog issue.**  Wave 7 (`S7-PR-KEY`) proved conditional funding-signature
attribution from an explicit `AdvertisesKey K seed m` hypothesis, but
`HandshakeState` stored only boolean milestones: the received
`accept_channel` payload was not part of protocol state.  PR-01's remaining
action was to add `acceptChannel?` and connect the stored payload to the key
model, while preserving the negative result that the field alone is not a proof
of possession.

**What this module adds.**

1. `HandshakeState.acceptChannel?` and the payload-carrying receive path
   `handshakeStepRecvAccept` live in `LnLean.Protocol.Handshake`.  The original
   nullary `HandshakeEvent.recvAcceptChannel` and `handshakeStep` are unchanged,
   so every downstream handshake proof and `Peer` match keeps compiling.
2. `PayloadReachable` is the milestone machine extended with payload-carrying
   accept receipts.  A state that has received a payload exposes exactly that
   payload (`acceptChannel?_of_handshakeStepRecvAccept`), the field is present
   exactly when `acceptReceived` is set
   (`payloadReachable_acceptReceived_iff`), every stored payload has an actual
   receive transition as provenance (`payloadReachable_acceptChannel?_provenance`),
   and no later step overwrites it (`payloadReachable_acceptChannel?_stable`).
3. Under the unchanged `LnLean.Proofs.WaveE.E06.KeyBinding`, the stored
   `acceptChannel.funding_pubkey` is the only key that can have produced the
   signer's honest funding signature, when the signer model's `AdvertisesKey`
   hypothesis holds.  The stored payload also exposes the handshake funding
   negotiation's `remoteFundingKey`.
4. **Negative result.**  Payload registration alone is not ownership: wave 7's
   mechanically checked model where the stored `funding_pubkey` is `pk₁` but the
   validating signature was produced by `sk₂` is lifted to a payload-reachable
   handshake state.  C3 (`EufCma`) still holds, and `KeyBinding` still fails.
   Thus the field is registration evidence, not proof of possession.

**Not modelled.**  secp256k1, nonces, seed entropy, proof of possession, a
trusted key-registration directory, and a computational ownership game.  The
`AdvertisesKey` link remains an explicit hypothesis; this module proves what
follows from it and what does not.  C3 is never used to derive `KeyBinding`.

**BOLT sections.**  BOLT 2 §The `accept_channel` Message (type 33,
`funding_pubkey`), §The `funding_created` Message, §The `funding_signed`
Message; BOLT 1 §Lightning Message Format.
-/

import LnLean.Protocol.Handshake
import LnLean.Crypto.KeyModel
import LnLean.Proofs.Crypto.KeyModelTargets

namespace LnLean.Proofs.Crypto.AcceptPayloadTargets

set_option autoImplicit false

open LnLean
open LnLean.Crypto (PrimitiveModel KeyModel SecretKey EufCma fundingTag)
open LnLean.Crypto.KeyModel
open LnLean.Protocol
open LnLean.Bitcoin
open LnLean.Proofs.Crypto.KeyModelTargets

/-! ## 1. Recording and exposing the payload -/

/-- A permitted payload-carrying receive records exactly the payload it
carried and sets the `acceptReceived` milestone. -/
theorem recvAccept_records_exact {s s' : HandshakeState} {a : AcceptChannel}
    (h : handshakeStepRecvAccept s a = some s') :
    s'.acceptChannel? = some a ∧ s'.acceptReceived = true :=
  ⟨acceptChannel?_of_handshakeStepRecvAccept h,
    acceptReceived_of_handshakeStepRecvAccept h⟩

/-- The payload-carrying receive is the original milestone transition followed
by `recordAccept`. -/
theorem recvAccept_underlying_milestone {s s' : HandshakeState}
    {a : AcceptChannel} (h : handshakeStepRecvAccept s a = some s') :
    ∃ s0 : HandshakeState,
      handshakeStep s .recvAcceptChannel = some s0 ∧ s' = s0.recordAccept a :=
  handshakeStepRecvAccept_underlying h

/-- A payload-reachable state that has received a payload exposes exactly that
payload, and that payload has a receive-transition provenance. -/
theorem payloadReachable_acceptPayload_exact {s : HandshakeState}
    {a : AcceptChannel} (h : PayloadReachable s) (ha : s.acceptChannel? = some a) :
    s.acceptReceived = true ∧
      ∃ s0 s1 : HandshakeState,
        PayloadReachable s0 ∧ handshakeStepRecvAccept s0 a = some s1 :=
  ⟨payloadReachable_acceptChannel?_received h ha,
    payloadReachable_acceptChannel?_provenance h a ha⟩

/-- Every payload-reachable state with the receive milestone set has a stored
payload. -/
theorem payloadReachable_acceptPayload_exists {s : HandshakeState}
    (h : PayloadReachable s) (hr : s.acceptReceived = true) :
    ∃ a : AcceptChannel, s.acceptChannel? = some a ∧ s.acceptReceived = true := by
  obtain ⟨a, ha⟩ := payloadReachable_acceptReceived_payload h hr
  exact ⟨a, ha, hr⟩

/-- The send path does not fabricate a peer payload. -/
theorem sendAccept_does_not_record {s s' : HandshakeState}
    (h : handshakeStep s .sendAcceptChannel = some s')
    (h0 : s.acceptChannel? = none) :
    s'.acceptChannel? = none :=
  sent_accept_does_not_store h h0

/-! ## 2. The stored payload and the funding negotiation -/

/-- The funding negotiation exposed by the recorded accept payload, if one has
been received.  It is the same `AcceptChannel.toFundingNegotiation` construction
used by the handshake; the payload is simply read from state. -/
def acceptNegotiation? (s : HandshakeState) (localFundingKey : PubKey)
    (fundingSatoshis : BtcAmount) (pushMsat : Msat)
    (temporaryChannelId : TemporaryChannelId) :
    Option LnLean.Bitcoin.FundingNegotiation :=
  s.acceptChannel?.map (fun a =>
    a.toFundingNegotiation localFundingKey fundingSatoshis pushMsat temporaryChannelId)

/-- The negotiation exposed by a stored payload is exactly the construction
from that payload. -/
@[simp] theorem acceptNegotiation?_eq_some {s : HandshakeState}
    {a : AcceptChannel} (h : s.acceptChannel? = some a)
    (localFundingKey : PubKey) (fundingSatoshis : BtcAmount) (pushMsat : Msat)
    (temporaryChannelId : TemporaryChannelId) :
    acceptNegotiation? s localFundingKey fundingSatoshis pushMsat temporaryChannelId =
      some (a.toFundingNegotiation localFundingKey fundingSatoshis pushMsat
        temporaryChannelId) := by
  simp [acceptNegotiation?, h]

/-- The stored payload's funding key is the negotiation's `remoteFundingKey`. -/
theorem stored_accept_negotiation_remoteFundingKey {s : HandshakeState}
    {a : AcceptChannel} (_h : s.acceptChannel? = some a)
    (localFundingKey : PubKey) (fundingSatoshis : BtcAmount) (pushMsat : Msat)
    (temporaryChannelId : TemporaryChannelId) :
    (a.toFundingNegotiation localFundingKey fundingSatoshis pushMsat
      temporaryChannelId).remoteFundingKey = a.fundingPubKey :=
  AcceptChannel.toFundingNegotiation_remoteFundingKey
    localFundingKey fundingSatoshis pushMsat temporaryChannelId a

/-- Under `AdvertisesKey`, the stored payload's negotiation key is the signer's
generated public key. -/
theorem stored_accept_negotiation_advertisedKey {M : PrimitiveModel}
    (K : KeyModel M) {seed : ByteArray} {s : HandshakeState}
    {a : AcceptChannel} (h : s.acceptChannel? = some a)
    (hadv : AdvertisesKey K seed a) (localFundingKey : PubKey)
    (fundingSatoshis : BtcAmount) (pushMsat : Msat)
    (temporaryChannelId : TemporaryChannelId) :
    (a.toFundingNegotiation localFundingKey fundingSatoshis pushMsat
      temporaryChannelId).remoteFundingKey = K.publicOfSeed seed := by
  rw [stored_accept_negotiation_remoteFundingKey h, hadv]

/-! ## 3. Funding-signature attribution from the stored payload -/

/-- **Attribution from a stored payload.**  Under the unchanged `KeyBinding`,
any key that accepts the signer's funding-domain signature is exactly the
`funding_pubkey` recorded in the handshake state.  The `AdvertisesKey`
hypothesis links that payload to the signer; `KeyBinding` is not derived from
C3. -/
theorem stored_accept_payload_attribution {M : PrimitiveModel} (K : KeyModel M)
    (hkb : KeyBinding M.ecdsaVerify) {s : HandshakeState} {a : AcceptChannel}
    (hstore : s.acceptChannel? = some a) (seed : ByteArray)
    (hadv : AdvertisesKey K seed a) {fundingTx : ByteArray}
    (hdom : K.correctOn (fundingTag ++ fundingTx)) {pk' : PubKey}
    (hver : M.ecdsaVerify pk' (fundingTag ++ fundingTx)
      (K.sign (K.secretOfSeed seed) (fundingTag ++ fundingTx)) = true) :
    pk' = a.fundingPubKey :=
  storedAccept_attribution K hkb ⟨hstore, hadv⟩ hdom hver

/-- The same attribution theorem on a payload-reachable state. -/
theorem reachable_stored_accept_attribution {M : PrimitiveModel}
    (K : KeyModel M) (hkb : KeyBinding M.ecdsaVerify) {s : HandshakeState}
    {a : AcceptChannel} (_hreach : PayloadReachable s)
    (hstore : s.acceptChannel? = some a) (seed : ByteArray)
    (hadv : AdvertisesKey K seed a) {fundingTx : ByteArray}
    (hdom : K.correctOn (fundingTag ++ fundingTx)) {pk' : PubKey}
    (hver : M.ecdsaVerify pk' (fundingTag ++ fundingTx)
      (K.sign (K.secretOfSeed seed) (fundingTag ++ fundingTx)) = true) :
    pk' = a.fundingPubKey :=
  stored_accept_payload_attribution K hkb hstore seed hadv hdom hver

/-! ## 4. Witness states -/

/-- The state after both `init` messages, before any accept payload. -/
def afterInit : HandshakeState :=
  { HandshakeState.initial with initSent := true, initReceived := true }

/-- The state after receiving the accept payload `a`. -/
def withAccept (a : AcceptChannel) : HandshakeState :=
  { afterInit with acceptReceived := true, acceptChannel? := some a }

theorem afterInit_payloadReachable : PayloadReachable afterInit := by
  have h1 : handshakePayloadStep HandshakeState.initial (.plain .sendInit) =
      some { HandshakeState.initial with initSent := true } := by
    simp [handshakePayloadStep, handshakeStep, HandshakeState.canSendInit,
      HandshakeState.initial]
  have h2 : handshakePayloadStep
        { HandshakeState.initial with initSent := true } (.plain .recvInit) =
      some afterInit := by
    simp [handshakePayloadStep, handshakeStep, HandshakeState.canRecvInit,
      HandshakeState.initial, afterInit]
  exact PayloadReachable.step _
    (PayloadReachable.step _ PayloadReachable.initial h1) h2

/-- A state that has received `a` is payload-reachable. -/
theorem withAccept_payloadReachable (a : AcceptChannel) :
    PayloadReachable (withAccept a) := by
  have hguard : afterInit.canRecvAccept := by
    simp [HandshakeState.canRecvAccept, HandshakeState.inited,
      HandshakeState.noReady, afterInit, HandshakeState.initial]
  have hstep : handshakeStep afterInit .recvAcceptChannel =
      some { afterInit with acceptReceived := true } := by
    simp [handshakeStep, hguard]
  have h : handshakeStepRecvAccept afterInit a = some (withAccept a) := by
    simp [handshakeStepRecvAccept, hstep, HandshakeState.recordAccept, withAccept]
  have h' : handshakePayloadStep afterInit (.recvAccept a) = some (withAccept a) := by
    simpa [handshakePayloadStep] using h
  exact PayloadReachable.step _ afterInit_payloadReachable h'

@[simp] theorem withAccept_acceptChannel? (a : AcceptChannel) :
    (withAccept a).acceptChannel? = some a := rfl

@[simp] theorem withAccept_acceptReceived (a : AcceptChannel) :
    (withAccept a).acceptReceived = true := rfl

/-- The witness state records exactly the payload. -/
theorem withAccept_payload_exact (a : AcceptChannel) :
    (withAccept a).acceptChannel? = some a ∧ (withAccept a).acceptReceived = true :=
  ⟨rfl, rfl⟩

/-! ## 5. Negative result: registration is not proof of possession -/

/-- **`accept_channel` payload registration does not prove possession.**  For
every base primitive model there is a payload-reachable handshake state whose
stored `accept_channel.funding_pubkey` is `pk₁`, yet the funding signature that
validates under `pk₁` was produced by the second key pair `(sk₂, pk₂)`, and is
identical to the one `sk₁` produces.  C3 (`EufCma`) holds and `KeyBinding`
fails.  Therefore `acceptChannel?` is registration evidence; attribution still
requires the explicit `KeyBinding` hypothesis (or an equivalent
registration/possession game). -/
theorem acceptPayload_not_proof_of_possession (M₀ : PrimitiveModel) :
    ∃ (M : PrimitiveModel) (K : KeyModel M) (s : HandshakeState)
      (a : AcceptChannel) (seed₁ seed₂ : ByteArray) (fundingTx : ByteArray),
      PayloadReachable s ∧
        s.acceptChannel? = some a ∧
        s.acceptReceived = true ∧
        K.publicOfSeed seed₁ ≠ K.publicOfSeed seed₂ ∧
        K.secretOfSeed seed₁ ≠ K.secretOfSeed seed₂ ∧
        EufCma M.ecdsaVerify ∧
        AdvertisesKey K seed₁ a ∧
        K.correctOn (fundingTag ++ fundingTx) ∧
        M.ecdsaVerify a.fundingPubKey (fundingTag ++ fundingTx)
          (K.sign (K.secretOfSeed seed₂) (fundingTag ++ fundingTx)) = true ∧
        K.sign (K.secretOfSeed seed₁) (fundingTag ++ fundingTx) =
          K.sign (K.secretOfSeed seed₂) (fundingTag ++ fundingTx) ∧
        ¬ KeyBinding M.ecdsaVerify := by
  obtain ⟨M, K, a, seed₁, seed₂, fundingTx, hpk, hsk, heuf, hadv, hdom,
    hver, hsig, hnk⟩ := key_generation_not_key_attribution M₀
  refine ⟨M, K, withAccept a, a, seed₁, seed₂, fundingTx,
    withAccept_payloadReachable a, rfl, rfl, hpk, hsk, heuf, hadv, hdom,
    hver, hsig, hnk⟩

/-! ## 6. Non-vacuity of the positive contract -/

/-- **The positive contract is not vacuous.**  There is a payload-reachable
state, a stored payload, a key model, a `KeyBinding` verifier, and a funding
message for which the stored key is the only accepting key. -/
theorem stored_accept_contract_nonvacuous (M₀ : PrimitiveModel) (k₀ : PubKey) :
    ∃ (M : PrimitiveModel) (K : KeyModel M) (s : HandshakeState)
      (a : AcceptChannel) (seed : ByteArray) (fundingTx : ByteArray),
      PayloadReachable s ∧
        s.acceptChannel? = some a ∧
        s.acceptReceived = true ∧
        EufCma M.ecdsaVerify ∧
        KeyBinding M.ecdsaVerify ∧
        WireShaped K ∧
        AdvertisesKey K seed a ∧
        K.correctOn (fundingTag ++ fundingTx) ∧
        (∀ pk' : PubKey,
          M.ecdsaVerify pk' (fundingTag ++ fundingTx)
            (K.sign (K.secretOfSeed seed) (fundingTag ++ fundingTx)) = true →
          pk' = a.fundingPubKey) := by
  obtain ⟨M, K, a, seed, fundingTx, heuf, hkb, hwire, hadv, hdom, hattr⟩ :=
    attribution_contract_nonvacuous M₀ k₀
  exact ⟨M, K, withAccept a, a, seed, fundingTx,
    withAccept_payloadReachable a, rfl, rfl, heuf, hkb, hwire, hadv, hdom, hattr⟩

/-! ## 7. Summary -/

/-- Bundled faithful reading of the payload/registration bridge:

1. a payload-carrying receive records exactly its payload;
2. a payload-reachable state with the receive milestone set exposes some
   payload;
3. under `KeyBinding` and `AdvertisesKey`, the stored key is the only key that
   can accept the honest funding signature;
4. registration alone does not prove possession (mechanised counterexample). -/
theorem accept_payload_summary :
    (∀ {s s' : HandshakeState} {a : AcceptChannel},
        handshakeStepRecvAccept s a = some s' → s'.acceptChannel? = some a) ∧
      (∀ {s : HandshakeState}, PayloadReachable s → s.acceptReceived = true →
        ∃ a : AcceptChannel, s.acceptChannel? = some a) ∧
      (∀ {M : PrimitiveModel} (K : KeyModel M),
        KeyBinding M.ecdsaVerify →
        ∀ {s : HandshakeState} {a : AcceptChannel},
          s.acceptChannel? = some a →
          ∀ (seed : ByteArray), AdvertisesKey K seed a →
          ∀ {fundingTx : ByteArray}, K.correctOn (fundingTag ++ fundingTx) →
          ∀ {pk' : PubKey},
            M.ecdsaVerify pk' (fundingTag ++ fundingTx)
              (K.sign (K.secretOfSeed seed) (fundingTag ++ fundingTx)) = true →
            pk' = a.fundingPubKey) ∧
      (∀ _M₀ : PrimitiveModel,
        ∃ (M : PrimitiveModel) (K : KeyModel M) (s : HandshakeState)
          (a : AcceptChannel) (seed₁ seed₂ : ByteArray)
          (fundingTx : ByteArray),
          PayloadReachable s ∧
            s.acceptChannel? = some a ∧
            EufCma M.ecdsaVerify ∧
            AdvertisesKey K seed₁ a ∧
            M.ecdsaVerify a.fundingPubKey (fundingTag ++ fundingTx)
              (K.sign (K.secretOfSeed seed₂) (fundingTag ++ fundingTx)) = true ∧
            ¬ KeyBinding M.ecdsaVerify) :=
  ⟨fun h => acceptChannel?_of_handshakeStepRecvAccept h,
    fun h hr => payloadReachable_acceptReceived_payload h hr,
    (by
      intro M K hkb s a ha seed hadv fundingTx hdom pk' hver
      exact stored_accept_payload_attribution K hkb ha seed hadv hdom hver),
    fun M₀ => by
      obtain ⟨M, K, s, a, seed₁, seed₂, fundingTx, hreach, hstore, _hrecv,
        _hpk, _hsk, heuf, hadv, _hdom, hver, _hsig, hnk⟩ :=
        acceptPayload_not_proof_of_possession M₀
      exact ⟨M, K, s, a, seed₁, seed₂, fundingTx, hreach, hstore, heuf, hadv,
        hver, hnk⟩⟩

end LnLean.Proofs.Crypto.AcceptPayloadTargets
