/-
# H21 — stored `accept_channel` payload to key registration (PR-01)

**Catalog issue.**  `PR-01` (P1): `FundingSigningLaw` / `KeyBinding` are
hypotheses and key attribution is conditional.  Wave 7 added
`LnLean.Crypto.KeyModel` and `KeyModelTargets`, whose `AdvertisesKey K seed m`
is the key-registration hypothesis "the peer's `accept_channel.funding_pubkey`
is the public key generated from `seed`".  The remaining gap named in
`docs/OPEN-ISSUES.md` is that `HandshakeState` has no `AcceptChannel` payload,
so `AdvertisesKey` is an external hypothesis about a message the state machine
never stores.

**Result of this module.**

1. `AcceptStore` is an additive extension of the handshake state that stores
   the received `accept_channel` payload.  `StoreEvent` carries the payload, so
   the bare `recvAcceptChannel` milestone cannot advance a store without it.
   `storeStep` is the deterministic transition and `StoreReachable` its
   closure.
2. `storeStep_recvAccept_sets_payload` and
   `storeStep_recvAccept_sets_flag`: a permitted payload receipt both stores the
   message and sets the existing `acceptReceived` flag.
3. `storeStep_payload_preserved`: once stored, the payload is never replaced,
   and `stored_payload_iff_acceptReceived` proves that on reachable stores the
   stored payload exists exactly when the existing flag says the message
   arrived.  This is the state-machine connection the boolean-only
   `HandshakeState` was missing (kept additive; see the integration patch).
4. `stored_accept_key_registration` connects a stored payload to
   `KeyModelTargets.AdvertisesKey`: the stored `funding_pubkey` is the signer's
   generated key, the negotiation's `remoteFundingKey` is that key, and — under
   the explicit transport-attribution premise `AcceptAttributed sender a` — the
   authenticated peer key is the signer's generated key too.
5. `stored_accept_funding_signature_valid` and
   `stored_accept_signature_attribution`: the signer's `fundingTag`-domain
   funding signature verifies under the stored key and under the transport
   identity, and under the unchanged `KeyBinding` contract any accepting key is
   the stored key.  `stored_accept_funding_signed_valid` packages the same
   signature as a wire-shaped, `fundingSignedValid` `funding_signed` record.
6. **Proof-of-possession premise made explicit.**
   `registrationChallenge` / `PossessionProof` model a challenge signature at
   the advertised key.  `possession_binds_responder` shows that, *under
   `KeyBinding`*, the responder key is the advertised key; therefore
   `possession_gives_transport_attribution` *derives* `AcceptAttributed` from a
   PoP transcript instead of assuming it.  `possession_not_attribution_without_keyBinding`
   mechanises the converse boundary: a PoP transcript accepted under two keys
   exists in a `EufCma` model where `KeyBinding` fails, so PoP without key
   binding proves nothing about the responder.
7. **Negative results retained.**
   `same_accept_payload_distinct_senders`: one `accept_channel` payload can be
   attached to two distinct transport identities, so the payload alone does not
   establish who sent it.  `stored_accept_payload_not_signer_attribution` lifts
   the wave-7 `key_generation_not_key_attribution` counterexample to a reachable
   store: with a stored payload, `AdvertisesKey`, key generation, and C3, a
   signature produced by a *different* secret key still verifies under the
   stored key, and `KeyBinding` fails.
8. `stored_accept_registration_nonvacuous` and
   `possession_proof_nonvacuous` give concrete witnesses, so neither contract
   is vacuous.

**BOLT sections.**  BOLT 2 §The `accept_channel` Message (type 33,
`funding_pubkey`) and §The `funding_signed` Message (type 35); BOLT 1
§Lightning Message Format (`signature`).

**Not modelled.**  secp256k1 arithmetic, RFC 6979 nonces, seed entropy, Noise
transport authentication, key ownership, a computational registration game, and
the wire decoder for type 33.  `AcceptAttributed` is an explicit transport
hypothesis (`docs/ASSUMPTIONS.md` §3, §6); `KeyBinding` is the unchanged
wave-E contract and is not derived from C3.  No EUF-CMA or key-attribution
strengthening is assumed beyond `PrimitiveModel.ecdsa_eufCma` and the existing
`KeyBinding` premise.
-/

import LnLean.Proofs.Crypto.KeyModelTargets
import LnLean.Proofs.Bitcoin.FundingAuthTargets

namespace LnLean.Proofs.WaveH.H21

set_option autoImplicit false

open LnLean
open LnLean.Crypto
open LnLean.Crypto.KeyModel
open LnLean.Protocol
open LnLean.Protocol.Handshake
open LnLean.Bitcoin
open LnLean.Proofs.WaveE.E19
open LnLean.Proofs.Crypto.KeyModelTargets
  (AdvertisesKey WireShaped acceptChannelWithFundingKey
   attribution_contract_nonvacuous funding_signature_valid_under_advertised_key
   funding_signature_attribution key_generation_not_key_attribution
   pinnedModel pinnedVerify pinnedVerify_keyBinding singleMessageVerify_not_keyBinding)
open LnLean.Proofs.Bitcoin.FundingAuthTargets

/-! ## 1. A handshake state that stores the received `accept_channel` -/

/-- An additive handshake extension: the ten-milestone boolean state plus the
exact `accept_channel` payload that was received, if any.  The shared
`HandshakeState` is not modified; this is the local model the integration patch
in the lane report would replace. -/
structure AcceptStore where
  /-- The existing BOLT 2 establishment milestones. -/
  handshake : HandshakeState := HandshakeState.initial
  /-- The received `accept_channel` payload, once it has arrived. -/
  acceptChannel : Option AcceptChannel := none
deriving Repr, BEq

namespace AcceptStore

/-- The store before any message has been exchanged. -/
def initial : AcceptStore := {}

/-- On a reachable store the stored payload exists exactly when the existing
`acceptReceived` milestone is set.  This is the state-machine link the
boolean-only `HandshakeState` lacked. -/
def PayloadFlagInv (st : AcceptStore) : Prop :=
  (st.handshake.acceptReceived = true) ↔ (st.acceptChannel.isSome = true)

end AcceptStore

/-- Events of the storing machine.  `recvAccept` is the payload-carrying form of
`recvAcceptChannel`; the bare milestone event is disabled at this layer so that
the flag can never be set without the payload. -/
inductive StoreEvent where
  | handshake (e : HandshakeEvent)
  | recvAccept (a : AcceptChannel)
deriving Repr

/-- One deterministic storing transition.  `none` means the event is not
allowed.  A payload receipt is allowed exactly when the underlying handshake
permits `recvAcceptChannel` and no payload has been stored yet. -/
def storeStep (st : AcceptStore) : StoreEvent → Option AcceptStore
  | .handshake .recvAcceptChannel => none
  | .handshake e =>
      (handshakeStep st.handshake e).map
        (fun s' => { st with handshake := s' })
  | .recvAccept a =>
      match st.acceptChannel with
      | some _ => none
      | none =>
          match handshakeStep st.handshake .recvAcceptChannel with
          | some s' => some { handshake := s', acceptChannel := some a }
          | none => none

/-- Reachable stores: the initial store and every permitted step. -/
inductive StoreReachable : AcceptStore → Prop where
  | initial : StoreReachable AcceptStore.initial
  | step {st st' : AcceptStore} (e : StoreEvent) :
      StoreReachable st → storeStep st e = some st' → StoreReachable st'

/-- The handshake state reached after the three messages `init`, `init`,
`accept_channel`. -/
def acceptReceivedState : HandshakeState where
  initSent := true
  initReceived := true
  acceptReceived := true

/-- A store that has received `a` as its `accept_channel` payload. -/
def receivedStore (a : AcceptChannel) : AcceptStore :=
  { handshake := acceptReceivedState, acceptChannel := some a }

/-! ### 2. Transition facts -/

/-- A non-payload handshake event is the mapped underlying transition and leaves
the stored payload alone. -/
theorem storeStep_handshake_of_ne (st : AcceptStore) {e : HandshakeEvent}
    (he : e ≠ .recvAcceptChannel) :
    storeStep st (.handshake e) =
      (handshakeStep st.handshake e).map
        (fun s' => { st with handshake := s' }) := by
  cases e <;> simp_all [storeStep]

/-- A non-payload handshake step is exactly the underlying handshake step, and
it does not change the stored payload. -/
theorem storeStep_handshake_state {st st' : AcceptStore} {e : HandshakeEvent}
    (he : e ≠ .recvAcceptChannel)
    (h : storeStep st (.handshake e) = some st') :
    handshakeStep st.handshake e = some st'.handshake ∧
      st'.acceptChannel = st.acceptChannel := by
  rw [storeStep_handshake_of_ne st he] at h
  cases hs : handshakeStep st.handshake e with
  | none => simp [hs] at h
  | some s' =>
      simp [hs] at h
      cases h
      exact ⟨rfl, rfl⟩

/-- The bare `recvAcceptChannel` milestone cannot advance a store: the payload
must be supplied through `StoreEvent.recvAccept`. -/
theorem storeStep_handshake_recvAcceptChannel (st : AcceptStore) :
    storeStep st (.handshake .recvAcceptChannel) = none := rfl

/-- Exact characterization of a permitted payload receipt. -/
theorem storeStep_recvAccept_state {st st' : AcceptStore} {a : AcceptChannel}
    (h : storeStep st (.recvAccept a) = some st') :
    ∃ s' : HandshakeState,
      handshakeStep st.handshake .recvAcceptChannel = some s' ∧
        st.acceptChannel = none ∧
        st'.handshake = s' ∧
        st'.acceptChannel = some a := by
  unfold storeStep at h
  cases hc : st.acceptChannel with
  | some b =>
      rw [hc] at h
      simp at h
  | none =>
      rw [hc] at h
      cases hs : handshakeStep st.handshake .recvAcceptChannel with
      | none =>
          rw [hs] at h
          simp at h
      | some s' =>
          rw [hs] at h
          simp at h
          cases h
          exact ⟨s', rfl, rfl, rfl, rfl⟩

/-- A permitted payload receipt stores exactly that payload. -/
theorem storeStep_recvAccept_sets_payload {st st' : AcceptStore}
    {a : AcceptChannel} (h : storeStep st (.recvAccept a) = some st') :
    st'.acceptChannel = some a := by
  obtain ⟨_, _, _, _, hpay⟩ := storeStep_recvAccept_state h
  exact hpay

/-- A permitted payload receipt sets the existing `acceptReceived` milestone. -/
theorem storeStep_recvAccept_sets_flag {st st' : AcceptStore}
    {a : AcceptChannel} (h : storeStep st (.recvAccept a) = some st') :
    st'.handshake.acceptReceived = true := by
  obtain ⟨s', hs, _, hstate, _⟩ := storeStep_recvAccept_state h
  rw [hstate]
  exact acceptReceived_of_recvAcceptChannel hs

/-- A payload receipt requires that no payload was stored before. -/
theorem storeStep_recvAccept_requires_empty {st st' : AcceptStore}
    {a : AcceptChannel} (h : storeStep st (.recvAccept a) = some st') :
    st.acceptChannel = none := by
  obtain ⟨_, _, hnone, _, _⟩ := storeStep_recvAccept_state h
  exact hnone

/-- **The stored payload is immutable.**  No permitted step replaces a payload
that has already been stored. -/
theorem storeStep_payload_preserved {st st' : AcceptStore} {e : StoreEvent}
    {a : AcceptChannel} (h : storeStep st e = some st')
    (hp : st.acceptChannel = some a) : st'.acceptChannel = some a := by
  cases e with
  | handshake he =>
      by_cases hne : he = .recvAcceptChannel
      · simp [storeStep, hne] at h
      · rw [(storeStep_handshake_state hne h).2, hp]
  | recvAccept b =>
      have hnone := storeStep_recvAccept_requires_empty h
      rw [hnone] at hp
      exact absurd hp (by simp)

/-! ### 3. The payload/flag invariant on reachable stores -/

/-- The handshake never changes `acceptReceived` except on `recvAcceptChannel`. -/
theorem handshakeStep_acceptReceived_frame {s s' : HandshakeState}
    {e : HandshakeEvent} (he : e ≠ .recvAcceptChannel)
    (h : handshakeStep s e = some s') :
    s'.acceptReceived = s.acceptReceived := by
  cases e with
  | recvAcceptChannel => exact absurd rfl he
  | sendInit =>
      by_cases hg : s.canSendInit
      · simp only [handshakeStep, ite_eq_left hg] at h
        rw [← Option.some.inj h]
      · simp [handshakeStep, hg] at h
  | recvInit =>
      by_cases hg : s.canRecvInit
      · simp only [handshakeStep, ite_eq_left hg] at h
        rw [← Option.some.inj h]
      · simp [handshakeStep, hg] at h
  | sendAcceptChannel =>
      by_cases hg : s.canSendAccept
      · simp only [handshakeStep, ite_eq_left hg] at h
        rw [← Option.some.inj h]
      · simp [handshakeStep, hg] at h
  | sendFundingCreated =>
      by_cases hg : s.canSendFundingCreated
      · simp only [handshakeStep, ite_eq_left hg] at h
        rw [← Option.some.inj h]
      · simp [handshakeStep, hg] at h
  | recvFundingCreated =>
      by_cases hg : s.canRecvFundingCreated
      · simp only [handshakeStep, ite_eq_left hg] at h
        rw [← Option.some.inj h]
      · simp [handshakeStep, hg] at h
  | sendFundingSigned =>
      by_cases hg : s.canSendFundingSigned
      · simp only [handshakeStep, ite_eq_left hg] at h
        rw [← Option.some.inj h]
      · simp [handshakeStep, hg] at h
  | recvFundingSigned =>
      by_cases hg : s.canRecvFundingSigned
      · simp only [handshakeStep, ite_eq_left hg] at h
        rw [← Option.some.inj h]
      · simp [handshakeStep, hg] at h
  | sendChannelReady =>
      by_cases hg : s.canSendChannelReady
      · simp only [handshakeStep, ite_eq_left hg] at h
        rw [← Option.some.inj h]
      · simp [handshakeStep, hg] at h
  | recvChannelReady =>
      by_cases hg : s.canRecvChannelReady
      · simp only [handshakeStep, ite_eq_left hg] at h
        rw [← Option.some.inj h]
      · simp [handshakeStep, hg] at h

/-- Every reachable store satisfies the payload/flag invariant. -/
theorem storeReachable_payloadFlagInv {st : AcceptStore}
    (hr : StoreReachable st) : st.PayloadFlagInv := by
  induction hr with
  | initial =>
      simp [AcceptStore.PayloadFlagInv, AcceptStore.initial, HandshakeState.initial]
  | step e hr hstep ih =>
      cases e with
      | handshake he =>
          by_cases hne : he = .recvAcceptChannel
          · subst hne
            simp [storeStep] at hstep
          · have hstate := (storeStep_handshake_state hne hstep).1
            have hpay := (storeStep_handshake_state hne hstep).2
            have hflag := handshakeStep_acceptReceived_frame hne hstate
            unfold AcceptStore.PayloadFlagInv
            rw [hflag, hpay]
            exact ih
      | recvAccept a =>
          have hflag := storeStep_recvAccept_sets_flag hstep
          have hpay := storeStep_recvAccept_sets_payload hstep
          unfold AcceptStore.PayloadFlagInv
          rw [hflag, hpay]
          simp

/-- On a reachable store, a stored payload is exactly the existing
`acceptReceived` milestone. -/
theorem stored_payload_iff_acceptReceived {st : AcceptStore}
    (hr : StoreReachable st) :
    st.acceptChannel.isSome = true ↔ st.handshake.acceptReceived = true :=
  (storeReachable_payloadFlagInv hr).symm

/-- A reachable store with a stored payload is non-vacuous. -/
theorem receivedStore_reachable (a : AcceptChannel) :
    StoreReachable (receivedStore a) := by
  let s1 : AcceptStore :=
    { handshake := { initSent := true } }
  let s2 : AcceptStore :=
    { handshake := { initSent := true, initReceived := true } }
  have h1 : storeStep AcceptStore.initial (.handshake .sendInit) = some s1 := by
    simp [storeStep, AcceptStore.initial, s1, handshakeStep,
      HandshakeState.initial, HandshakeState.canSendInit]
  have h2 : storeStep s1 (.handshake .recvInit) = some s2 := by
    simp [storeStep, s1, s2, handshakeStep, HandshakeState.canRecvInit]
  have h3 : storeStep s2 (.recvAccept a) = some (receivedStore a) := by
    simp [storeStep, s2, receivedStore, acceptReceivedState, handshakeStep,
      HandshakeState.canRecvAccept, HandshakeState.inited, HandshakeState.noReady]
  exact StoreReachable.step _ (StoreReachable.step _
    (StoreReachable.step _ StoreReachable.initial h1) h2) h3

/-! ## 4. Transport attribution and the stored key -/

/-- A received `accept_channel` with the transport's claimed sender.  The sender
identity is attached by the receiving transport; it is not a field of the wire
message. -/
structure ReceivedAccept where
  sender : PeerIdentity
  message : AcceptChannel

/-- **Transport attribution for the accept direction.**  The authenticated peer
key is the funding key the peer advertised.  This is an explicit premise, not a
consequence of the message or of C3 (`same_accept_payload_distinct_senders`). -/
def AcceptAttributed (sender : PeerIdentity) (a : AcceptChannel) : Prop :=
  sender.key = a.fundingPubKey

/-- The funding negotiation determined by a stored `accept_channel` payload.
The opener's local choices stay explicit; the peer's key comes from the store. -/
def storedAcceptNegotiation (st : AcceptStore) (localFundingKey : PubKey)
    (fundingSatoshis : BtcAmount) (pushMsat : Msat)
    (temporaryChannelId : TemporaryChannelId) :
    Option LnLean.Bitcoin.FundingNegotiation :=
  st.acceptChannel.map fun a =>
    a.toFundingNegotiation localFundingKey fundingSatoshis pushMsat temporaryChannelId

/-- A stored payload determines the negotiation's remote funding key. -/
theorem stored_accept_negotiation_key {M : PrimitiveModel} (K : KeyModel M)
    (a : AcceptChannel) (seed : ByteArray) (hadv : AdvertisesKey K seed a)
    (localFundingKey : PubKey) (fundingSatoshis : BtcAmount) (pushMsat : Msat)
    (temporaryChannelId : TemporaryChannelId) :
    (a.toFundingNegotiation localFundingKey fundingSatoshis pushMsat
        temporaryChannelId).remoteFundingKey = K.publicOfSeed seed := by
  rw [AcceptChannel.toFundingNegotiation_remoteFundingKey, hadv]

/-- **The stored payload registers the signer's generated key.**  Under
`AdvertisesKey` and the explicit transport-attribution premise, the stored
`funding_pubkey`, the signer's generated key, the authenticated peer key, and
the negotiation's remote funding key are all the same key. -/
theorem stored_accept_key_registration {M : PrimitiveModel} (K : KeyModel M)
    (st : AcceptStore) (a : AcceptChannel) (seed : ByteArray)
    (sender : PeerIdentity) (hstore : st.acceptChannel = some a)
    (hadv : AdvertisesKey K seed a) (hattr : AcceptAttributed sender a) :
    st.acceptChannel.isSome = true ∧
      a.fundingPubKey = K.publicOfSeed seed ∧
      sender.key = K.publicOfSeed seed ∧
      sender.key = a.fundingPubKey ∧
      (∀ (localFundingKey : PubKey) (fundingSatoshis : BtcAmount)
        (pushMsat : Msat) (temporaryChannelId : TemporaryChannelId),
        (a.toFundingNegotiation localFundingKey fundingSatoshis pushMsat
          temporaryChannelId).remoteFundingKey = K.publicOfSeed seed) := by
  refine ⟨?_, hadv, ?_, hattr, ?_⟩
  · rw [hstore]
    rfl
  · rw [hattr, hadv]
  · intro localFundingKey fundingSatoshis pushMsat temporaryChannelId
    exact stored_accept_negotiation_key K a seed hadv _ _ _ _

/-- The transport identity is the stored key (a restatement used below). -/
theorem stored_accept_transport_key {M : PrimitiveModel} (K : KeyModel M)
    (st : AcceptStore) (a : AcceptChannel) (seed : ByteArray)
    (sender : PeerIdentity) (_hstore : st.acceptChannel = some a)
    (hadv : AdvertisesKey K seed a) (hattr : AcceptAttributed sender a) :
    sender.key = K.publicOfSeed seed := by
  rw [hattr, hadv]

/-- **The signer's funding signature verifies under the stored key and under
the transport identity.** -/
theorem stored_accept_funding_signature_valid {M : PrimitiveModel}
    (K : KeyModel M) (st : AcceptStore) (a : AcceptChannel) (seed : ByteArray)
    (sender : PeerIdentity) (_hstore : st.acceptChannel = some a)
    (hadv : AdvertisesKey K seed a) (hattr : AcceptAttributed sender a)
    (fundingTx : ByteArray) (hdom : K.correctOn (fundingTag ++ fundingTx)) :
    M.ecdsaVerify a.fundingPubKey (fundingTag ++ fundingTx)
        (K.sign (K.secretOfSeed seed) (fundingTag ++ fundingTx)) = true ∧
      M.ecdsaVerify sender.key (fundingTag ++ fundingTx)
        (K.sign (K.secretOfSeed seed) (fundingTag ++ fundingTx)) = true := by
  have hvalid :=
    funding_signature_valid_under_advertised_key K a seed hadv fundingTx hdom
  refine ⟨hvalid, ?_⟩
  rw [hattr]
  exact hvalid

/-- **Attribution at the store boundary.**  Under the unchanged `KeyBinding`
contract, every key that accepts the signer's funding signature is the
authenticated peer key, hence the stored `funding_pubkey`.  `KeyBinding` is not
derived from C3. -/
theorem stored_accept_signature_attribution {M : PrimitiveModel}
    (K : KeyModel M) (hkb : KeyBinding M.ecdsaVerify) (st : AcceptStore)
    (a : AcceptChannel) (seed : ByteArray) (sender : PeerIdentity)
    (_hstore : st.acceptChannel = some a) (hadv : AdvertisesKey K seed a)
    (hattr : AcceptAttributed sender a) (fundingTx : ByteArray)
    (hdom : K.correctOn (fundingTag ++ fundingTx)) {pk' : PubKey}
    (hver : M.ecdsaVerify pk' (fundingTag ++ fundingTx)
      (K.sign (K.secretOfSeed seed) (fundingTag ++ fundingTx)) = true) :
    pk' = sender.key := by
  have h := funding_signature_attribution K hkb a seed hadv fundingTx hdom hver
  rw [h, hattr]

/-- **The stored payload yields a valid `funding_signed` record.**  With a
wire-shaped key model, the signer's signature over the funding-tagged
transaction is exactly a `fundingSignedValid` record under the transport
identity. -/
theorem stored_accept_funding_signed_valid {M : PrimitiveModel}
    (K : KeyModel M) (hwire : WireShaped K) (st : AcceptStore)
    (a : AcceptChannel) (seed : ByteArray) (sender : PeerIdentity)
    (_hstore : st.acceptChannel = some a) (hadv : AdvertisesKey K seed a)
    (hattr : AcceptAttributed sender a) (channelId : ChannelId)
    (fundingTx : ByteArray) (hdom : K.correctOn (fundingTag ++ fundingTx)) :
    fundingSignedValid M sender.key fundingTx
      { channelId := channelId
        signature :=
          K.sign (K.secretOfSeed seed) (fundingTag ++ fundingTx) } := by
  rw [waveE_e19_funding_signed_valid_iff]
  constructor
  · exact hwire (K.secretOfSeed seed) (fundingTag ++ fundingTx)
  · show M.ecdsaVerify sender.key (fundingTag ++ fundingTx)
      (K.sign (K.secretOfSeed seed) (fundingTag ++ fundingTx)) = true
    rw [hattr]
    exact funding_signature_valid_under_advertised_key K a seed hadv fundingTx hdom

/-! ## 5. Proof of possession, with the missing game stated exactly -/

/-- Domain tag for the registration challenge.  It is separate from
`fundingTag` so a challenge signature cannot be replayed as a funding
signature (the tags differ, and `PrimitiveModel`'s verifier is opaque). -/
def registrationTag : ByteArray := ByteArray.mk #[0x72, 0x65, 0x67]

/-- The registration challenge for an advertised key: the tagged key bytes. -/
def registrationChallenge (a : AcceptChannel) : ByteArray :=
  registrationTag ++ a.fundingPubKey.bytes

/-- A proof-of-possession transcript: a signature at the advertised
`funding_pubkey` over the registration challenge.  `responder` is the key the
transport claims produced it.  This is a *transcript model*, not a game: it has
no freshness, no challenge sampling, and no adversary. -/
structure PossessionProof (M : PrimitiveModel) (a : AcceptChannel) where
  /-- The key the transport attributes the response to. -/
  responder : PubKey
  /-- The challenge signature. -/
  signature : EcdsaSig
  /-- The advertised key accepts the challenge signature. -/
  verifies : M.ecdsaVerify a.fundingPubKey (registrationChallenge a) signature = true

/-- **The PoP premise needs `KeyBinding` to say anything.**  If the responder
key also accepts the same challenge signature, `KeyBinding` forces it to be the
advertised key.  This is exactly the extra premise a registration game would
have to supply; it is not C3. -/
theorem possession_binds_responder {M : PrimitiveModel}
    (hkb : KeyBinding M.ecdsaVerify) {a : AcceptChannel}
    (p : PossessionProof M a)
    (hresp : M.ecdsaVerify p.responder (registrationChallenge a) p.signature = true) :
    p.responder = a.fundingPubKey :=
  hkb p.responder a.fundingPubKey (registrationChallenge a) p.signature hresp
    p.verifies

/-- A PoP transcript whose responder is the transport identity *derives*
transport attribution.  This is the strongest faithful registration statement
the model supports: it replaces the assumption `AcceptAttributed` by a
challenge response plus `KeyBinding`. -/
theorem possession_gives_transport_attribution {M : PrimitiveModel}
    (K : KeyModel M) (hkb : KeyBinding M.ecdsaVerify) (st : AcceptStore)
    (a : AcceptChannel) (seed : ByteArray) (sender : PeerIdentity)
    (_hstore : st.acceptChannel = some a) (_hadv : AdvertisesKey K seed a)
    (p : PossessionProof M a) (hresponder : p.responder = sender.key)
    (hresp : M.ecdsaVerify p.responder (registrationChallenge a) p.signature = true) :
    AcceptAttributed sender a := by
  unfold AcceptAttributed
  rw [← hresponder]
  exact possession_binds_responder hkb p hresp

/-- The PoP route composes with the stored-key registration contract. -/
theorem stored_accept_registration_of_possession {M : PrimitiveModel}
    (K : KeyModel M) (hkb : KeyBinding M.ecdsaVerify) (st : AcceptStore)
    (a : AcceptChannel) (seed : ByteArray) (sender : PeerIdentity)
    (hstore : st.acceptChannel = some a) (hadv : AdvertisesKey K seed a)
    (p : PossessionProof M a) (hresponder : p.responder = sender.key)
    (hresp : M.ecdsaVerify p.responder (registrationChallenge a) p.signature = true) :
    sender.key = K.publicOfSeed seed ∧
      sender.key = a.fundingPubKey := by
  have hattr := possession_gives_transport_attribution K hkb st a seed sender
    hstore hadv p hresponder hresp
  exact ⟨stored_accept_transport_key K st a seed sender hstore hadv hattr, hattr⟩

/-- **PoP without key binding proves nothing about the responder.**  In a full
`EufCma` model, the single-message verifier accepts a challenge signature under
two distinct keys; the responder is not the advertised key and `KeyBinding`
fails.  The missing premise is exactly `KeyBinding` (or a real registration
game), not more C3. -/
theorem possession_not_attribution_without_keyBinding (M₀ : PrimitiveModel) :
    ∃ (M : PrimitiveModel) (a : AcceptChannel) (p : PossessionProof M a),
      p.responder ≠ a.fundingPubKey ∧
        M.ecdsaVerify p.responder (registrationChallenge a) p.signature = true ∧
        EufCma M.ecdsaVerify ∧
        ¬ KeyBinding M.ecdsaVerify := by
  let k₀ : PubKey := ⟨ByteArray.empty⟩
  let a : AcceptChannel := acceptChannelWithFundingKey k₀
  let d₀ : ByteArray := registrationChallenge a
  let M : PrimitiveModel :=
    LnLean.Protocol.Handshake.singleMessageEcdsaModel M₀ d₀
  let p : PossessionProof M a :=
    { responder := ⟨ByteArray.mk #[0x00]⟩
      signature := ⟨ByteArray.empty⟩
      verifies := by
        show singleMessageVerify d₀ k₀ (registrationChallenge a)
          ⟨ByteArray.empty⟩ = true
        simp [singleMessageVerify, d₀] }
  refine ⟨M, a, p, ?_, ?_, M.ecdsa_eufCma, ?_⟩
  · intro h
    have hb : (ByteArray.mk #[0x00] : ByteArray) = ByteArray.empty :=
      congrArg PubKey.bytes h
    have hsz := congrArg ByteArray.size hb
    have h1 : (ByteArray.mk #[0x00] : ByteArray).size = 1 := rfl
    have h2 : (ByteArray.empty : ByteArray).size = 0 := rfl
    rw [h1, h2] at hsz
    exact absurd hsz (by decide)
  · show singleMessageVerify d₀ (⟨ByteArray.mk #[0x00]⟩ : PubKey)
      (registrationChallenge a) ⟨ByteArray.empty⟩ = true
    simp [singleMessageVerify, d₀]
  · exact singleMessageVerify_not_keyBinding d₀

/-! ## 6. Negative results retained -/

/-- One `accept_channel` payload can be attached to two distinct transport
identities: the wire message carries no sender.  This is why
`AcceptAttributed` is an explicit premise. -/
theorem same_accept_payload_distinct_senders :
    ∃ r₁ r₂ : ReceivedAccept,
      r₁.message = r₂.message ∧ r₁.sender ≠ r₂.sender := by
  let k₀ : PubKey := ⟨ByteArray.empty⟩
  let k₁ : PubKey := ⟨ByteArray.empty.push 0x01⟩
  let a : AcceptChannel := acceptChannelWithFundingKey k₀
  refine ⟨⟨⟨k₀⟩, a⟩, ⟨⟨k₁⟩, a⟩, rfl, ?_⟩
  intro h
  have hk : k₀ = k₁ := congrArg PeerIdentity.key h
  have hb : (ByteArray.empty : ByteArray) = ByteArray.empty.push 0x01 :=
    congrArg PubKey.bytes hk
  have hsz := congrArg ByteArray.size hb
  simp at hsz

/-- **A stored payload plus `AdvertisesKey` plus C3 does not identify the
signer.**  The wave-7 counterexample is lifted to a reachable store: the stored
`funding_pubkey` is `seed₁`'s generated key, but a signature produced from
`seed₂`'s secret key still verifies under it, and `KeyBinding` fails.  Hence the
store records *which key was advertised*, never *who signed*. -/
theorem stored_accept_payload_not_signer_attribution (M₀ : PrimitiveModel) :
    ∃ (M : PrimitiveModel) (K : KeyModel M) (st : AcceptStore)
      (a : AcceptChannel) (seed₁ seed₂ : ByteArray) (fundingTx : ByteArray),
      StoreReachable st ∧
        st.acceptChannel = some a ∧
        AdvertisesKey K seed₁ a ∧
        K.publicOfSeed seed₁ ≠ K.publicOfSeed seed₂ ∧
        EufCma M.ecdsaVerify ∧
        M.ecdsaVerify a.fundingPubKey (fundingTag ++ fundingTx)
          (K.sign (K.secretOfSeed seed₂) (fundingTag ++ fundingTx)) = true ∧
        ¬ KeyBinding M.ecdsaVerify := by
  obtain ⟨M, K, m, s₁, s₂, tx, hp, _hsk, he, ha, _hc, hv, _hsig, hnk⟩ :=
    key_generation_not_key_attribution M₀
  exact ⟨M, K, receivedStore m, m, s₁, s₂, tx, receivedStore_reachable m,
    rfl, ha, hp, he, hv, hnk⟩

/-! ## 7. Non-vacuity -/

/-- **The stored-key registration contract is not vacuous.**  A pinned-key
model realises C3, `KeyBinding`, `AdvertisesKey`, transport attribution, and the
signature conclusion at a reachable store. -/
theorem stored_accept_registration_nonvacuous (M₀ : PrimitiveModel)
    (k₀ : PubKey) :
    ∃ (M : PrimitiveModel) (K : KeyModel M) (st : AcceptStore)
      (a : AcceptChannel) (seed : ByteArray) (sender : PeerIdentity)
      (fundingTx : ByteArray),
      StoreReachable st ∧
        st.acceptChannel = some a ∧
        st.handshake.acceptReceived = true ∧
        EufCma M.ecdsaVerify ∧
        KeyBinding M.ecdsaVerify ∧
        AdvertisesKey K seed a ∧
        AcceptAttributed sender a ∧
        K.correctOn (fundingTag ++ fundingTx) ∧
        M.ecdsaVerify sender.key (fundingTag ++ fundingTx)
          (K.sign (K.secretOfSeed seed) (fundingTag ++ fundingTx)) = true := by
  obtain ⟨M, K, a, seed, tx, he, hkb, _hw, ha, hc, _hattr⟩ :=
    attribution_contract_nonvacuous M₀ k₀
  let sender : PeerIdentity := ⟨a.fundingPubKey⟩
  refine ⟨M, K, receivedStore a, a, seed, sender, tx,
    receivedStore_reachable a, rfl, rfl, he, hkb, ha, rfl, hc, ?_⟩
  simpa [sender] using
    funding_signature_valid_under_advertised_key K a seed ha tx hc

/-- **The PoP route is not vacuous.**  In a pinned-key model there is a
challenge signature at the advertised key whose responder is that key. -/
theorem possession_proof_nonvacuous (M₀ : PrimitiveModel) (k₀ : PubKey) :
    ∃ (M : PrimitiveModel) (a : AcceptChannel) (p : PossessionProof M a),
      KeyBinding M.ecdsaVerify ∧ p.responder = a.fundingPubKey := by
  let a : AcceptChannel := acceptChannelWithFundingKey k₀
  let d₀ : ByteArray := registrationChallenge a
  let M : PrimitiveModel := pinnedModel M₀ k₀ d₀
  let p : PossessionProof M a :=
    { responder := k₀
      signature := ⟨zeros 64⟩
      verifies := by
        show pinnedVerify k₀ d₀ k₀ (registrationChallenge a) ⟨zeros 64⟩ = true
        simp [pinnedVerify, d₀] }
  exact ⟨M, a, p, pinnedVerify_keyBinding k₀ d₀, rfl⟩

/-! ## 8. Summary -/

/-- Bundled faithful reading of `PR-01` at the stored-payload boundary:

1. a stored payload with `AdvertisesKey` and explicit transport attribution
   registers the signer's generated key, and the transport key equals it;
2. under `KeyBinding`, every key accepting the signer's funding signature is the
   transport identity;
3. a PoP transcript under `KeyBinding` *derives* transport attribution;
4. payload equality alone does not establish the sender (mechanised);
5. a stored payload, `AdvertisesKey`, key generation, and C3 do not identify the
   signing secret key without `KeyBinding` (mechanised). -/
theorem stored_accept_registration_summary :
    (∀ (M : PrimitiveModel) (K : KeyModel M) (st : AcceptStore)
        (a : AcceptChannel) (seed : ByteArray) (sender : PeerIdentity),
        st.acceptChannel = some a →
        AdvertisesKey K seed a →
        AcceptAttributed sender a →
        st.acceptChannel.isSome = true ∧
          sender.key = K.publicOfSeed seed ∧
          sender.key = a.fundingPubKey) ∧
      (∀ (M : PrimitiveModel), KeyBinding M.ecdsaVerify →
        ∀ (K : KeyModel M) (st : AcceptStore) (a : AcceptChannel)
          (seed : ByteArray) (sender : PeerIdentity) (fundingTx : ByteArray),
          st.acceptChannel = some a →
          AdvertisesKey K seed a →
          AcceptAttributed sender a →
          K.correctOn (fundingTag ++ fundingTx) →
          ∀ pk' : PubKey,
            M.ecdsaVerify pk' (fundingTag ++ fundingTx)
              (K.sign (K.secretOfSeed seed) (fundingTag ++ fundingTx)) = true →
            pk' = sender.key) ∧
      (∀ (M : PrimitiveModel) (K : KeyModel M), KeyBinding M.ecdsaVerify →
        ∀ (st : AcceptStore) (a : AcceptChannel) (seed : ByteArray)
          (sender : PeerIdentity) (p : PossessionProof M a),
          st.acceptChannel = some a →
          AdvertisesKey K seed a →
          p.responder = sender.key →
          M.ecdsaVerify p.responder (registrationChallenge a) p.signature = true →
          AcceptAttributed sender a) ∧
      (∃ r₁ r₂ : ReceivedAccept,
        r₁.message = r₂.message ∧ r₁.sender ≠ r₂.sender) ∧
      (∀ _M₀ : PrimitiveModel,
        ∃ (M : PrimitiveModel) (K : KeyModel M) (st : AcceptStore)
          (a : AcceptChannel) (seed₁ seed₂ : ByteArray) (fundingTx : ByteArray),
          StoreReachable st ∧
            st.acceptChannel = some a ∧
            AdvertisesKey K seed₁ a ∧
            K.publicOfSeed seed₁ ≠ K.publicOfSeed seed₂ ∧
            EufCma M.ecdsaVerify ∧
            M.ecdsaVerify a.fundingPubKey (fundingTag ++ fundingTx)
              (K.sign (K.secretOfSeed seed₂) (fundingTag ++ fundingTx)) = true ∧
            ¬ KeyBinding M.ecdsaVerify) := by
  refine ⟨?_, ?_, ?_, same_accept_payload_distinct_senders, ?_⟩
  · intro M K st a seed sender hstore hadv hattr
    obtain ⟨hisSome, _, hkey, _⟩ :=
      (stored_accept_key_registration K st a seed sender hstore hadv hattr)
    exact ⟨hisSome, hkey, hattr⟩
  · intro M hkb K st a seed sender fundingTx hstore hadv hattr hdom pk' hver
    exact stored_accept_signature_attribution K hkb st a seed sender hstore hadv
      hattr fundingTx hdom hver
  · intro M K hkb st a seed sender p hstore hadv hresp hver
    exact possession_gives_transport_attribution K hkb st a seed sender hstore
      hadv p hresp hver
  · exact stored_accept_payload_not_signer_attribution

end LnLean.Proofs.WaveH.H21
