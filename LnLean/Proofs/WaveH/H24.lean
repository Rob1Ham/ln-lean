/-
# H24 — `accept_channel` payload equality does not attribute a sender (PR-01)

**Catalog issue.**  `PR-01` (P1): `FundingSigningLaw` and `KeyBinding` are
hypotheses, and wave 7 narrowed the remaining gap to the
`AcceptChannel`/registration or proof-of-possession path.  The wave-7
`FundingAuthTargets` module mechanized the corresponding scope boundary for
`open_channel` (`same_message_distinct_senders`): an `OpenChannel` record has no
sender field, so the record alone cannot authenticate a peer.

**Result of this module.**  The negative result is preserved and strengthened
for the `accept_channel` payload that PR-01 actually consumes:

1. `any_accept_payload_two_senders` — *every* `AcceptChannel` payload can be
   emitted by two distinct transport senders.  This is stronger than an
   existential counterexample: no payload is sender-specific.
2. `same_accept_payload_distinct_senders` and
   `same_accept_wire_message_distinct_senders` — the record-level and the
   wire-`Msg`-level statements of the same fact.  Even the full `Msg`
   constructor (and therefore its type and 270-byte length) is identical for
   the two senders.
3. `no_payload_to_sender_function` — there is no function
   `AcceptChannel → PeerIdentity` that recovers the sender from the payload.
4. `payload_only_test_cannot_attribute` — the same blindness holds for any
   predicate that factors through the payload.  Registration, key ownership,
   and every other payload-restricted test therefore cannot be sender
   attribution.
5. `TransportBound` is stated as the **exact additional premise**:
   `r.sender.key = r.message.fundingPubKey`, i.e. the Noise-authenticated peer
   identity is the `funding_pubkey` advertised by the payload.  It is
   *sufficient* (`transport_bound_attributes_sender`) and *discriminating*
   (`distinct_senders_not_both_transport_bound`): no two distinct senders of
   one payload can both satisfy it.  It is non-vacuous.
6. Registration and proof of possession are shown **not** to substitute for
   the transport premise.  `registration_does_not_attribute` proves that
   `AdvertisesKey` (a payload property) holds equally for both senders;
   `funding_key_pop_does_not_attribute_senders` proves that a valid
   proof-of-possession transcript under `accept_channel.funding_pubkey` is
   compatible with two distinct senders, because the transcript mentions the
   key and challenge, never the peer identity.
7. The composed premise `RegisteredBound` (registration plus a generated
   sender identity) implies `TransportBound` and hence attributes the sender.

**What is not claimed.**  Neither `TransportBound` nor `RegisteredBound` is
derived here.  `TransportBound` is exactly the Noise transport-attribution
assumption of `docs/ASSUMPTIONS.md` §3; `RegisteredBound` additionally consumes
the `AdvertisesKey` registration hypothesis of `KeyModelTargets`.  Actual key
ownership still requires the `KeyBinding`/proof-of-possession contract (C3 is
not a key-binding game; see `KeyModelTargets.key_generation_not_key_attribution`).

**Anchors.**  BOLT 2 §The `accept_channel` Message (type 33): `funding_pubkey`.
BOLT 1 §Lightning Message Format (type/length framing):
`refs/bolts/01-messaging.md`.  `refs/rust-lightning/lightning/src/ln/msgs.rs:371`
(`AcceptChannel`).  BOLT 8 transport authentication is the Noise layer, not a
field of the message (`docs/ASSUMPTIONS.md` §3).

**Existing counterexample.**  `FundingAuthTargets.same_message_distinct_senders`
is imported and re-exported unchanged; this module does not edit that file or
weaken its result.
-/

import LnLean.Protocol.Handshake
import LnLean.Proofs.Bitcoin.FundingAuthTargets
import LnLean.Proofs.Crypto.KeyModelTargets

namespace LnLean.Proofs.WaveH.H24

set_option autoImplicit false

open LnLean
open LnLean.Protocol
open LnLean.Crypto
open LnLean.Proofs.Bitcoin.FundingAuthTargets
open LnLean.Proofs.Crypto.KeyModelTargets

/-! ## 1. A received `accept_channel` and its transport identity -/

/-- An `accept_channel` payload together with the sender identity reported by
the receiving transport.  `AcceptChannel` has no sender field, so this record is
the smallest model in which "who sent it" is even expressible; the identity is
attached by Noise, not carried by the payload. -/
structure ReceivedAccept where
  sender : PeerIdentity
  message : AcceptChannel

/-! ## 2. Two concrete distinct peer identities -/

/-- An empty-byte public key, used only as a concrete distinct identity. -/
def pkZero : PubKey := ⟨ByteArray.empty⟩

/-- The empty-byte key extended by one byte.  Its byte length differs, so it is
a genuinely different identity. -/
def pkOne : PubKey := ⟨ByteArray.empty.push 0x01⟩

theorem pkZero_ne_pkOne : pkZero ≠ pkOne := by
  intro h
  have hb : (ByteArray.empty : ByteArray) = ByteArray.empty.push 0x01 :=
    congrArg PubKey.bytes h
  have hsz := congrArg ByteArray.size hb
  simp at hsz

theorem peerZero_ne_peerOne :
    (⟨pkZero⟩ : PeerIdentity) ≠ ⟨pkOne⟩ := by
  intro h
  exact pkZero_ne_pkOne (congrArg PeerIdentity.key h)

/-! ## 3. The negative result: every payload has two possible senders -/

/-- **Strengthened negative result.**  For *every* `accept_channel` payload there
are two distinct transport senders that emit exactly that payload.  Payload
equality therefore carries no sender information at all, not merely in one
constructed example. -/
theorem any_accept_payload_two_senders (a : AcceptChannel) :
    ∃ r₁ r₂ : ReceivedAccept,
      r₁.message = a ∧ r₂.message = a ∧ r₁.sender ≠ r₂.sender :=
  ⟨⟨⟨pkZero⟩, a⟩, ⟨⟨pkOne⟩, a⟩, rfl, rfl, peerZero_ne_peerOne⟩

/-- **The negative result at the `accept_channel` payload.**  Two senders can
emit the same payload, so payload equality alone does not establish sender
attribution. -/
theorem same_accept_payload_distinct_senders :
    ∃ r₁ r₂ : ReceivedAccept,
      r₁.message = r₂.message ∧ r₁.sender ≠ r₂.sender := by
  obtain ⟨r₁, r₂, h₁, h₂, hne⟩ :=
    any_accept_payload_two_senders (acceptChannelWithFundingKey pkZero)
  exact ⟨r₁, r₂, h₁.trans h₂.symm, hne⟩

/-- **Wire-level strengthening.**  The entire `Msg` value is equal for the two
senders, so message type and the fixed 270-byte `accept_channel` length are
equal too (`Messages.msgLength_acceptChannel`).  A wire-only observer sees one
message. -/
theorem same_accept_wire_message_distinct_senders :
    ∃ r₁ r₂ : ReceivedAccept,
      Msg.acceptChannel r₁.message = Msg.acceptChannel r₂.message ∧
      r₁.sender ≠ r₂.sender := by
  obtain ⟨r₁, r₂, h₁, h₂, hne⟩ :=
    any_accept_payload_two_senders (acceptChannelWithFundingKey pkZero)
  exact ⟨r₁, r₂, by rw [h₁, h₂], hne⟩

/-- **Wire metadata strengthening.**  The fixed `accept_channel` payload length
(`Messages.msgLength_acceptChannel`, 270 bytes) is identical for the two
senders: a wire-only observer has no length or type side channel either. -/
theorem same_accept_wire_length_distinct_senders :
    ∃ r₁ r₂ : ReceivedAccept,
      msgLength (Msg.acceptChannel r₁.message) =
          msgLength (Msg.acceptChannel r₂.message) ∧
        msgLength (Msg.acceptChannel r₁.message) = 270 ∧
        r₁.sender ≠ r₂.sender := by
  obtain ⟨r₁, r₂, h₁, h₂, hne⟩ :=
    any_accept_payload_two_senders (acceptChannelWithFundingKey pkZero)
  exact ⟨r₁, r₂, by rw [h₁, h₂], msgLength_acceptChannel r₁.message, hne⟩

/-- **No payload-to-sender function.**  There is no total decoder from the
`accept_channel` payload to the peer identity that is correct for every
receipt.  This is the precise sense in which attribution information is absent
from the payload rather than merely hard to extract. -/
theorem no_payload_to_sender_function :
    ¬ ∃ f : AcceptChannel → PeerIdentity,
        ∀ r : ReceivedAccept, f r.message = r.sender := by
  rintro ⟨f, hf⟩
  obtain ⟨r₁, r₂, h₁, h₂, hne⟩ :=
    any_accept_payload_two_senders (acceptChannelWithFundingKey pkZero)
  apply hne
  have e₁ : f (acceptChannelWithFundingKey pkZero) = r₁.sender := by
    simpa [h₁] using hf r₁
  have e₂ : f (acceptChannelWithFundingKey pkZero) = r₂.sender := by
    simpa [h₂] using hf r₂
  exact e₁.symm.trans e₂

/-- **Any payload-only test is blind to the sender.**  If a predicate on
receipts is determined by the payload (`hP`), then it cannot separate two
senders of the same payload.  Registration, key-ownership predicates, and
payload checks are all instances. -/
theorem payload_only_test_cannot_attribute (P : ReceivedAccept → Prop)
    (hP : ∀ r₁ r₂ : ReceivedAccept,
      r₁.message = r₂.message → (P r₁ ↔ P r₂)) :
    ∃ r₁ r₂ : ReceivedAccept,
      r₁.message = r₂.message ∧ r₁.sender ≠ r₂.sender ∧ (P r₁ ↔ P r₂) := by
  obtain ⟨r₁, r₂, h₁, h₂, hne⟩ :=
    any_accept_payload_two_senders (acceptChannelWithFundingKey pkZero)
  exact ⟨r₁, r₂, h₁.trans h₂.symm, hne, hP r₁ r₂ (h₁.trans h₂.symm)⟩

/-! ## 4. The exact additional premise: transport identity binding -/

/-- **The exact additional premise for sender attribution.**  The
Noise-authenticated peer identity is the `funding_pubkey` carried by the
`accept_channel` payload.  Nothing in the payload or in the handshake state can
supply this equation; it is the transport-attribution assumption of
`docs/ASSUMPTIONS.md` §3, made explicit at the point of use. -/
def TransportBound (r : ReceivedAccept) : Prop :=
  r.sender.key = r.message.fundingPubKey

/-- Peer identities are determined by their authenticated key.  This is a
one-field structure fact, stated separately so that the counterexample and the
attribution proof share it. -/
theorem peerIdentity_eq_of_key_eq {p q : PeerIdentity} (h : p.key = q.key) :
    p = q := by
  cases p with
  | mk k₁ =>
    cases q with
    | mk k₂ =>
      exact congrArg PeerIdentity.mk h

/-- **Sufficiency.**  Two receipts of the same payload whose senders are both
transport-bound have the same sender.  This is the conditional
attribution theorem the negative result permits. -/
theorem transport_bound_attributes_sender {r₁ r₂ : ReceivedAccept}
    (hmsg : r₁.message = r₂.message)
    (h₁ : TransportBound r₁) (h₂ : TransportBound r₂) :
    r₁.sender = r₂.sender := by
  have hk : r₁.sender.key = r₂.sender.key := by
    calc r₁.sender.key = r₁.message.fundingPubKey := h₁
      _ = r₂.message.fundingPubKey := by rw [hmsg]
      _ = r₂.sender.key := h₂.symm
  exact peerIdentity_eq_of_key_eq hk

/-- **The premise is exactly discriminating.**  No two distinct senders of one
payload can both be transport-bound: the premise is not an artefact of the
particular counterexample, it is the condition that rules the counterexample
out. -/
theorem distinct_senders_not_both_transport_bound {r₁ r₂ : ReceivedAccept}
    (hmsg : r₁.message = r₂.message) (hne : r₁.sender ≠ r₂.sender) :
    ¬ (TransportBound r₁ ∧ TransportBound r₂) := by
  rintro ⟨h₁, h₂⟩
  exact hne (transport_bound_attributes_sender hmsg h₁ h₂)

/-- The transport premise is satisfiable, so the conditional
attribution theorem is not vacuous. -/
theorem transportBound_nonvacuous (a : AcceptChannel) :
    TransportBound ⟨⟨a.fundingPubKey⟩, a⟩ := rfl

/-! ## 5. Registration and proof of possession are not sender attribution -/

/-- **Registration is payload-only and cannot attribute a sender.**  Under the
`KeyModelTargets` registration hypothesis `AdvertisesKey K seed a`, both
distinct senders satisfy the same registration fact, because it is a property of
the shared payload.  Registration binds the key to a seed, not the payload to a
channel. -/
theorem registration_does_not_attribute {M : PrimitiveModel} (K : KeyModel M)
    (seed : ByteArray) (a : AcceptChannel)
    (hreg : AdvertisesKey K seed a) :
    ∃ r₁ r₂ : ReceivedAccept,
      r₁.message = a ∧ r₂.message = a ∧ r₁.sender ≠ r₂.sender ∧
      AdvertisesKey K seed r₁.message ∧
      AdvertisesKey K seed r₂.message := by
  obtain ⟨r₁, r₂, h₁, h₂, hne⟩ := any_accept_payload_two_senders a
  exact ⟨r₁, r₂, h₁, h₂, hne,
    by rw [h₁]; exact hreg,
    by rw [h₂]; exact hreg⟩

/-- An `accept_channel` receipt bundled with a proof-of-possession transcript
for the advertised funding key. -/
structure ReceivedAcceptPop where
  receipt : ReceivedAccept
  challenge : ByteArray
  proof : EcdsaSig

/-- The proof-of-possession predicate: the transcript verifies under the
`funding_pubkey` advertised by the payload. -/
def ProvesFundingKey (M : PrimitiveModel) (p : ReceivedAcceptPop) : Prop :=
  M.ecdsaVerify p.receipt.message.fundingPubKey p.challenge p.proof = true

/-- **Proof of possession attests the key, not the sender.**  A valid
funding-key PoP transcript is compatible with two distinct transport senders of
the same payload: the transcript mentions the key and the challenge, never the
peer identity.  PoP is therefore not a substitute for `TransportBound`. -/
theorem funding_key_pop_does_not_attribute_senders (M : PrimitiveModel)
    (a : AcceptChannel) (challenge : ByteArray) (sig : EcdsaSig)
    (hpop : M.ecdsaVerify a.fundingPubKey challenge sig = true) :
    ∃ p₁ p₂ : ReceivedAcceptPop,
      p₁.receipt.message = a ∧ p₂.receipt.message = a ∧
      p₁.receipt.sender ≠ p₂.receipt.sender ∧
      p₁.challenge = challenge ∧ p₂.challenge = challenge ∧
      p₁.proof = sig ∧ p₂.proof = sig ∧
      ProvesFundingKey M p₁ ∧ ProvesFundingKey M p₂ :=
  ⟨⟨⟨⟨pkZero⟩, a⟩, challenge, sig⟩,
    ⟨⟨⟨pkOne⟩, a⟩, challenge, sig⟩,
    rfl, rfl, peerZero_ne_peerOne, rfl, rfl, rfl, rfl, hpop, hpop⟩

/-- The composed premise: the advertised funding key is registered to a
generated seed, and the transport identity is that same generated key. -/
def RegisteredBound {M : PrimitiveModel} (K : KeyModel M) (seed : ByteArray)
    (r : ReceivedAccept) : Prop :=
  AdvertisesKey K seed r.message ∧ r.sender.key = K.publicOfSeed seed

/-- `RegisteredBound` implies the transport binding, hence attributes. -/
theorem registeredBound_implies_transportBound {M : PrimitiveModel}
    {K : KeyModel M} {seed : ByteArray} {r : ReceivedAccept}
    (h : RegisteredBound K seed r) : TransportBound r := by
  rcases h with ⟨hreg, hid⟩
  exact hid.trans hreg.symm

/-- **Registration plus a generated sender identity attributes the sender.**
This is the precise combination that closes the gap: the payload-only half
(`AdvertisesKey`) is not enough, and the transport half (`sender.key` equals the
generated key) is what gives uniqueness. -/
theorem registeredBound_attributes_sender {M : PrimitiveModel}
    {K : KeyModel M} {seed : ByteArray} {r₁ r₂ : ReceivedAccept}
    (hmsg : r₁.message = r₂.message)
    (h₁ : RegisteredBound K seed r₁) (h₂ : RegisteredBound K seed r₂) :
    r₁.sender = r₂.sender :=
  transport_bound_attributes_sender hmsg
    (registeredBound_implies_transportBound h₁)
    (registeredBound_implies_transportBound h₂)

/-- `RegisteredBound` is satisfiable, so the composed attribution contract is
non-vacuous. -/
theorem registeredBound_nonvacuous {M : PrimitiveModel} (K : KeyModel M)
    (seed : ByteArray) :
    RegisteredBound K seed
      ⟨⟨K.publicOfSeed seed⟩, acceptChannelWithFundingKey (K.publicOfSeed seed)⟩ :=
  ⟨rfl, rfl⟩

/-! ## 6. The existing `open_channel` counterexample is retained -/

/-- The wave-7 `open_channel` counterexample, re-exported unchanged.  This
module adds the `accept_channel` instance; it does not weaken or alter the
existing result. -/
theorem open_channel_counterexample_retained :
    ∃ r₁ r₂ : ReceivedOpen,
      r₁.message = r₂.message ∧ r₁.sender ≠ r₂.sender :=
  same_message_distinct_senders

/-- Both handshake payload types have the same attribution boundary. -/
theorem open_and_accept_payloads_both_unattributed :
    (∃ r₁ r₂ : ReceivedOpen,
        r₁.message = r₂.message ∧ r₁.sender ≠ r₂.sender) ∧
      (∃ r₁ r₂ : ReceivedAccept,
        r₁.message = r₂.message ∧ r₁.sender ≠ r₂.sender) :=
  ⟨same_message_distinct_senders, same_accept_payload_distinct_senders⟩

/-! ## 7. Summary -/

/-- **Headline summary of H24.**  Payload equality is sender-blind (universally,
at the record and wire-message levels, and for any payload-only test); the
transport-identity binding is sufficient and discriminating; registration and
proof of possession alone do not attribute a sender. -/
theorem accept_payload_attribution_summary :
    (∀ a : AcceptChannel, ∃ r₁ r₂ : ReceivedAccept,
        r₁.message = a ∧ r₂.message = a ∧ r₁.sender ≠ r₂.sender) ∧
      (¬ ∃ f : AcceptChannel → PeerIdentity,
          ∀ r : ReceivedAccept, f r.message = r.sender) ∧
      (∀ r₁ r₂ : ReceivedAccept, r₁.message = r₂.message →
        TransportBound r₁ → TransportBound r₂ → r₁.sender = r₂.sender) ∧
      (∀ r₁ r₂ : ReceivedAccept, r₁.message = r₂.message →
        r₁.sender ≠ r₂.sender → ¬ (TransportBound r₁ ∧ TransportBound r₂)) :=
  ⟨any_accept_payload_two_senders,
    no_payload_to_sender_function,
    fun _ _ hmsg h₁ h₂ => transport_bound_attributes_sender hmsg h₁ h₂,
    fun _ _ hmsg hne => distinct_senders_not_both_transport_bound hmsg hne⟩

end LnLean.Proofs.WaveH.H24
