import LnLean.Proofs.Protocol.OpenChannelRoutingTargets

/-!
# Transport authentication above `open_channel` (`L1-03`, wave 10)

**English claim.**  Wave 9 added `OpenChannelEnvelope`, whose `sender` field is
the peer identity the transport claims, and made `EnvelopeAttributed` exactly
the equality of that transport key with the wire's advertised
`funding_pubkey`.  The routing machine then proved that attribution is not an
observable of protocol state and that an unattributed envelope is still routed.
That left the layer above the envelope unspecified: what does a transport
actually authenticate, and what must still be assumed before a delivered type-32
message is `EnvelopeAttributed`?

This module supplies an **additive** transport-authentication layer.  It does
not edit `OpenChannelRoutingTargets.lean`, `Handshake.lean`, `Messages.lean`,
or any core handshake file, and it does not claim to implement Noise or any
real transport.

## What the transport supplies

* `TransportSession` records a session id, a peer key, and an `established`
  flag.  The key is the key the transport says it authenticated for the
  session; the flag is the transport's statement that the session completed
  its authenticated handshake.
* `TransportAuthenticated d` is just `d.session.established = true`.  This is
  the *only* thing the transport is modelled as supplying.
* `AuthenticatedDelivery` pairs a session with the unchanged type-32 wire
  record.  Its `envelope` attaches the session key as `PeerIdentity`, so the
  resulting object is exactly an `OpenChannelEnvelope`.

## What remains an explicit assumption

* `SessionKeyBinding d` is the explicit key-binding law:
  `d.session.peerKey = d.wire.fundingPubKey`.  It says the key authenticated by
  the transport is the same key the opener advertised as its funding key.
  Neither `TransportAuthenticated` nor the wire payload implies it.
* `SessionKeyBindingLaw` is the same law stated for every authenticated
  delivery.  `transport_authenticated_attributed` takes the two hypotheses
  directly; `sessionKeyBindingLaw_attributed` takes the bundled law.
* Key *ownership* is still not modelled.  `Msg.openChannel` carries no
  signature (`wire_carries_no_signature`), so possession of the secret key for
  `funding_pubkey` remains the C3/`PR-01` obligation, not a consequence of
  transport authentication.

## What is proved

Positive:

* `envelopeAttributed_of_sessionKeyBinding` and
  `transport_authenticated_attributed`: authentication plus the key-binding law
  yields `EnvelopeAttributed` for the delivered envelope.
* `authenticated_delivery_reaches_fundingCreated`: the attributed envelope
  composes with the wave-9 route through `accept_channel` and the enabled
  `funding_created` step.
* `authenticated_open_reaches_funding`: the same route also reaches the
  reachable `FundingPhase` and the constructed P2WSH funding output.
* `concrete_authenticated_delivery`: a concrete session/delivery witness, so
  the layer is not vacuous.

Negative (the sharp boundary):

* `transport_auth_not_from_wire`: two authenticated sessions deliver the *same*
  wire; only the one whose session key equals the advertised funding key is
  attributed.
* `unattributed_delivery_exists` and `authenticated_not_bound`: authentication
  does not imply the key-binding law, and a delivered opening can be
  unattributed.
* `no_session_binding_counterexample`: same wire, one delivery satisfies
  `SessionKeyBinding` and the other does not; only the first is attributed.
* `no_wire_sender_function`: there is no function from the wire payload to the
  session key that is correct for every authenticated delivery.
* `not_universal_sessionKeyBinding`: transport authentication alone cannot
  establish the key-binding law for all deliveries.

## Non-vacuity

`concrete_authenticated_delivery` and `concrete_authenticated_route` use
concrete 33-byte keys, a concrete well-formed type-32 wire, a concrete
established session, and the wave-9 concrete route.

## BOLT anchors

* BOLT 1 §"Lightning Message Format" (`refs/bolts/01-messaging.md:43-92`): the
  payload starts with a two-byte type; sender authentication is outside it.
* BOLT 2 §"The `open_channel` Message": `funding_pubkey` is advertised, not
  proved.
* BOLT 8 is the transport specification; this module models only the
  authentication *interface* a transport must expose, not its cryptography.
-/

namespace LnLean.Proofs.Protocol.TransportAuthTargets

set_option autoImplicit false

open LnLean
open LnLean.Protocol
open LnLean.Bitcoin
open LnLean.Proofs.Bitcoin.FundingScriptTargets
open LnLean.Proofs.Bitcoin.FundingAuthTargets
open LnLean.Proofs.Protocol.OpenChannelWireTargets
open LnLean.Proofs.Protocol.OpenChannelRoutingTargets

/-! ## 1. Sessions, deliveries, and the authentication interface -/

/-- A transport session as seen by the receiving endpoint.  `peerKey` is the
key the transport claims to have authenticated; `established` says the
transport completed its authenticated session setup.  No cryptographic
implementation is modelled. -/
structure TransportSession where
  /-- Opaque session identifier (for example a Noise handshake instance). -/
  sessionId : Nat
  /-- The peer key the transport says it authenticated for this session. -/
  peerKey : PubKey
  /-- Whether the transport completed authenticated session setup. -/
  established : Bool
deriving Repr, BEq

/-- A type-32 opening delivered over a particular transport session.  The wire
record is unchanged; provenance lives in `session`, exactly as it lives in the
routing layer's `OpenChannelEnvelope.sender`. -/
structure AuthenticatedDelivery where
  /-- The session over which the message arrived. -/
  session : TransportSession
  /-- The unchanged type-32 payload. -/
  wire : OpenChannelWire
deriving Repr, BEq

namespace AuthenticatedDelivery

/-- The transport envelope obtained by attaching the session key to the wire.
This is the bridge to the wave-9 routing model. -/
def envelope (d : AuthenticatedDelivery) : OpenChannelEnvelope where
  sender := ⟨d.session.peerKey⟩
  wire := d.wire

@[simp] theorem envelope_sender (d : AuthenticatedDelivery) :
    d.envelope.sender = ⟨d.session.peerKey⟩ := rfl

@[simp] theorem envelope_wire (d : AuthenticatedDelivery) :
    d.envelope.wire = d.wire := rfl

@[simp] theorem envelope_key (d : AuthenticatedDelivery) :
    d.envelope.sender.key = d.session.peerKey := rfl

end AuthenticatedDelivery

/-- **What the transport supplies.**  The session is established/authenticated.
This is a Boolean flag about the session, not a statement about the payload. -/
def TransportAuthenticated (d : AuthenticatedDelivery) : Prop :=
  d.session.established = true

/-- The transport flag is independent of the payload: replacing the wire cannot
change whether the session is authenticated. -/
theorem transportAuthenticated_with_wire (d : AuthenticatedDelivery)
    (w : OpenChannelWire) :
    TransportAuthenticated { d with wire := w } ↔ TransportAuthenticated d :=
  Iff.rfl

/-- **What remains an assumption.**  The key authenticated by the transport is
the funding key advertised in the opening payload.  This is the explicit
session/key-binding law; it is neither a definition of authentication nor a
consequence of the wire record. -/
def SessionKeyBinding (d : AuthenticatedDelivery) : Prop :=
  d.session.peerKey = d.wire.fundingPubKey

/-- A transport that satisfies the key-binding law for every authenticated
delivery.  This is the bundled form of `SessionKeyBinding`; the per-delivery
form is used by the counterexamples. -/
structure SessionKeyBindingLaw where
  /-- Every authenticated delivery binds its session key to the advertised
  funding key. -/
  bound : ∀ d : AuthenticatedDelivery,
    TransportAuthenticated d → SessionKeyBinding d

/-- Authentication plus the key-binding law, bundled for composition. -/
structure AuthenticatedBinding (d : AuthenticatedDelivery) : Prop where
  /-- The transport says the session is authenticated. -/
  authenticated : TransportAuthenticated d
  /-- The explicit session/key-binding law. -/
  keyBound : SessionKeyBinding d

/-! ## 2. Positive direction: authenticated delivery is attributed -/

/-- For a delivery built from its session key, attribution is *exactly* the
key-binding law.  This makes the positivity and the negative counterexamples
two sides of the same equation. -/
theorem envelopeAttributed_iff_sessionKeyBinding (d : AuthenticatedDelivery) :
    EnvelopeAttributed d.envelope ↔ SessionKeyBinding d := by
  simp [AuthenticatedDelivery.envelope, SessionKeyBinding]

/-- **Key binding gives envelope attribution.**  If the session key is the wire
funding key, the envelope produced by the transport is `EnvelopeAttributed`.
This is the definitional core of the positive direction. -/
theorem envelopeAttributed_of_sessionKeyBinding (d : AuthenticatedDelivery)
    (hbind : SessionKeyBinding d) :
    EnvelopeAttributed d.envelope :=
  (envelopeAttributed_iff_sessionKeyBinding d).2 hbind

/-- Without the key-binding law the delivery is not attributed.  This is the
general form of the concrete counterexamples below. -/
theorem not_envelopeAttributed_of_not_sessionKeyBinding
    (d : AuthenticatedDelivery) (h : ¬ SessionKeyBinding d) :
    ¬ EnvelopeAttributed d.envelope :=
  fun hattr => h ((envelopeAttributed_iff_sessionKeyBinding d).1 hattr)

/-- **Positive transport-authentication theorem.**  Under
`TransportAuthenticated` and the explicit `SessionKeyBinding` law, a delivered
`open_channel` is `EnvelopeAttributed`.  The authentication flag is recorded in
the statement; attribution itself comes from the explicit key-binding law. -/
theorem transport_authenticated_attributed (d : AuthenticatedDelivery)
    (_hauth : TransportAuthenticated d) (hbind : SessionKeyBinding d) :
    EnvelopeAttributed d.envelope :=
  envelopeAttributed_of_sessionKeyBinding d hbind

/-- Bundled-law form of `transport_authenticated_attributed`. -/
theorem sessionKeyBindingLaw_attributed (law : SessionKeyBindingLaw)
    (d : AuthenticatedDelivery) (hauth : TransportAuthenticated d) :
    EnvelopeAttributed d.envelope :=
  transport_authenticated_attributed d hauth (law.bound d hauth)

/-- Bundled-evidence form of the positive theorem. -/
theorem authenticatedBinding_attributed {d : AuthenticatedDelivery}
    (h : AuthenticatedBinding d) : EnvelopeAttributed d.envelope :=
  transport_authenticated_attributed d h.authenticated h.keyBound

/-- The attributed envelope still carries exactly the original wire. -/
theorem attributed_envelope_wire (d : AuthenticatedDelivery)
    (_h : EnvelopeAttributed d.envelope) :
    d.envelope.wire = d.wire := rfl

/-! ## 3. Composition with the routed opening -> funding witness -/

/-- **Authenticated route reaches `funding_created`.**  An authenticated,
key-bound type-32 delivery is attributed, the wave-9 route reaches
`afterOpenRoute`, the `accept_channel` payload is recorded, and the unchanged
handshake machine enables `funding_created`. -/
theorem authenticated_delivery_reaches_fundingCreated
    (d : AuthenticatedDelivery) (a : AcceptChannel)
    (hauth : TransportAuthenticated d) (hbind : SessionKeyBinding d) :
    EnvelopeAttributed d.envelope ∧
      OpenRouteReachable (afterOpenRoute d.envelope) ∧
      ∃ s1 s2 : HandshakeState,
        handshakeStepRecvAccept (afterOpenRoute d.envelope).peer.handshake a =
            some s1 ∧
          handshakeStep s1 .sendFundingCreated = some s2 ∧
          s1.acceptChannel? = some a ∧
          s2.acceptReceived = true := by
  have hattr := transport_authenticated_attributed d hauth hbind
  obtain ⟨hreach, hsteps⟩ :=
    openRoute_initial_to_fundingCreated d.envelope a
  exact ⟨hattr, hreach, hsteps⟩

/-- **Authenticated route reaches the funding construction.**  The same route
reaches a reachable `FundingPhase` and the P2WSH output is the hash of the
ordered BOLT 3 2-of-2 witness script.  No signature check, key-ownership law,
or hash injectivity is used; those remain outside this layer. -/
theorem authenticated_open_reaches_funding
    (d : AuthenticatedDelivery) (a : AcceptChannel)
    (H : ByteArray → ByteArray)
    (hauth : TransportAuthenticated d) (hbind : SessionKeyBinding d) :
    EnvelopeAttributed d.envelope ∧
      OpenRouteReachable (afterOpenRoute d.envelope) ∧
      FundingReachable (acceptorPhaseAfter d.wire a) ∧
      FundingScriptHashLinked H (d.wire.toFundingParams H a) ∧
      (d.wire.toFundingParams H a).fundingScriptPubKey =
        p2wsh (H (TwoOfTwoScriptBytes
          (d.wire.toFundingNegotiation a).firstFundingKey
          (d.wire.toFundingNegotiation a).secondFundingKey)) := by
  have hattr := transport_authenticated_attributed d hauth hbind
  obtain ⟨hreach, _⟩ := openRoute_initial_to_fundingCreated d.envelope a
  exact ⟨hattr, hreach,
    acceptorPhaseAfter_reachable d.wire a,
    d.wire.toFundingParams_hash_linked H a,
    d.wire.toFundingParams_fundingScriptPubKey_eq_p2wsh_ordered H a⟩

/-- The authenticated route keeps the advertised funding key in the constructed
witness script, by composing the positive attribution theorem with the wave-9
key-in-script result. -/
theorem authenticated_key_in_funding_script
    (d : AuthenticatedDelivery) (a : AcceptChannel)
    (H : ByteArray → ByteArray)
    (hauth : TransportAuthenticated d) (hbind : SessionKeyBinding d) :
    d.session.peerKey = (d.wire.toFundingNegotiation a).localFundingKey ∧
      KeyInScript (d.wire.toFundingParams H a).witnessScript.bytes
        d.session.peerKey :=
  attributed_wire_key_in_script H d.envelope a
    (transport_authenticated_attributed d hauth hbind)

/-! ## 4. Concrete non-vacuous session and delivery -/

private def bytesOf (n : Nat) (b : UInt8) : ByteArray :=
  ByteArray.mk (List.replicate n b).toArray

private theorem bytesOf_size (n : Nat) (b : UInt8) :
    (bytesOf n b).size = n := by
  simp [bytesOf, ByteArray.size]

private def pub33 (b : UInt8) : PubKey := ⟨bytesOf 33 b⟩

private theorem pub33_valid (b : UInt8) : (pub33 b).Valid := by
  simp [PubKey.Valid, pub33, bytesOf_size]

private theorem pub33_zero_ne_one : pub33 0 ≠ pub33 1 := by
  intro h
  have hb : (pub33 0).bytes = (pub33 1).bytes := congrArg PubKey.bytes h
  have h0 : (pub33 0).bytes[0]? = some (0 : UInt8) := by
    simp only [pub33, bytesOf]
    decide
  have h1 : (pub33 1).bytes[0]? = some (1 : UInt8) := by
    simp only [pub33, bytesOf]
    decide
  rw [hb] at h0
  rw [h0] at h1
  exact absurd (Option.some.inj h1) (by decide)

/-- A concrete well-formed type-32 wire record with the given funding key.  All
six public keys are the same key and the temporary channel id is the canonical
32-byte zero id; only `fundingPubKey` matters for the transport boundary. -/
private def demoWire (k : PubKey) : OpenChannelWire where
  temporaryChannelId := ChannelId.zero
  fundingSatoshis := 0
  pushMsat := ⟨0⟩
  dustLimitSatoshis := 0
  maxHtlcValueInFlightMsat := 0
  channelReserveSatoshis := 0
  htlcMinimumMsat := 0
  feeratePerKw := 0
  toSelfDelay := 0
  maxAcceptedHtlcs := 0
  fundingPubKey := k
  revocationBasepoint := k
  paymentBasepoint := k
  delayedPaymentBasepoint := k
  htlcBasepoint := k
  firstPerCommitmentPoint := k
  channelFlags := 0
  shutdownScriptpubkey := ByteArray.empty

private theorem demoWire_wellFormed {k : PubKey} (hk : k.Valid) :
    wellFormed (.openChannel (demoWire k)) := by
  apply wellFormed_openChannel_of
  · exact ChannelId.zero_valid
  · intro p hp
    have hp' : p = k := by
      simpa [demoWire, pubKeys] using hp
    rw [hp']
    exact hk

/-- A concrete session carrying the given key and authentication flag. -/
def demoSession (b : UInt8) (established : Bool) : TransportSession where
  sessionId := 0
  peerKey := pub33 b
  established := established

/-- A concrete delivery of a type-32 opening over a concrete session. -/
def demoDelivery (sessionByte wireByte : UInt8) (established : Bool) :
    AuthenticatedDelivery where
  session := demoSession sessionByte established
  wire := demoWire (pub33 wireByte)

/-- The concrete attributed delivery used by the non-vacuity results. -/
def demoAttributedDelivery : AuthenticatedDelivery :=
  demoDelivery 0 0 true

/-- The concrete unattributed delivery used by the negative results. -/
def demoUnattributedDelivery : AuthenticatedDelivery :=
  demoDelivery 1 0 true

theorem demoAttributedDelivery_authenticated :
    TransportAuthenticated demoAttributedDelivery := rfl

theorem demoAttributedDelivery_bound :
    SessionKeyBinding demoAttributedDelivery := rfl

theorem demoAttributedDelivery_attributed :
    EnvelopeAttributed demoAttributedDelivery.envelope :=
  transport_authenticated_attributed demoAttributedDelivery
    demoAttributedDelivery_authenticated demoAttributedDelivery_bound

theorem demoAttributedDelivery_wellFormed :
    wellFormed (.openChannel demoAttributedDelivery.wire) :=
  demoWire_wellFormed (pub33_valid 0)

/-- **Non-vacuity of the authenticated layer.**  There is a concrete
established session, a concrete well-formed type-32 wire, and a delivery that
simultaneously satisfies `TransportAuthenticated`, `SessionKeyBinding`, and
`EnvelopeAttributed`. -/
theorem concrete_authenticated_delivery :
    ∃ d : AuthenticatedDelivery,
      wellFormed (.openChannel d.wire) ∧
        TransportAuthenticated d ∧
        SessionKeyBinding d ∧
        EnvelopeAttributed d.envelope :=
  ⟨demoAttributedDelivery, demoAttributedDelivery_wellFormed,
    demoAttributedDelivery_authenticated,
    demoAttributedDelivery_bound,
    demoAttributedDelivery_attributed⟩

/-- **Non-vacuity of the full authenticated route.**  The concrete attributed
delivery reaches `funding_created` and the constructed funding output. -/
theorem concrete_authenticated_route (a : AcceptChannel)
    (H : ByteArray → ByteArray) :
    ∃ d : AuthenticatedDelivery,
      TransportAuthenticated d ∧
        SessionKeyBinding d ∧
        EnvelopeAttributed d.envelope ∧
        OpenRouteReachable (afterOpenRoute d.envelope) ∧
        FundingReachable (acceptorPhaseAfter d.wire a) ∧
        FundingScriptHashLinked H (d.wire.toFundingParams H a) := by
  refine ⟨demoAttributedDelivery, demoAttributedDelivery_authenticated,
    demoAttributedDelivery_bound, demoAttributedDelivery_attributed,
    (openRoute_initial_to_fundingCreated demoAttributedDelivery.envelope a).1,
    acceptorPhaseAfter_reachable demoAttributedDelivery.wire a,
    demoAttributedDelivery.wire.toFundingParams_hash_linked H a⟩

/-! ## 5. The sharp negative: the wire does not authenticate the sender -/

/-- Both concrete boundary deliveries are authenticated: the flag is a session
property, not a payload property. -/
theorem demoUnattributedDelivery_authenticated :
    TransportAuthenticated demoUnattributedDelivery := rfl

/-- Authentication alone does not give the key-binding law: the concrete
unattributed delivery is authenticated but its session key differs from the
advertised funding key. -/
theorem authenticated_not_bound :
    ∃ d : AuthenticatedDelivery,
      TransportAuthenticated d ∧ ¬ SessionKeyBinding d := by
  refine ⟨demoUnattributedDelivery, demoUnattributedDelivery_authenticated, ?_⟩
  intro hbind
  have hkey : pub33 1 = pub33 0 := by
    simpa [demoUnattributedDelivery, demoDelivery, demoSession,
      SessionKeyBinding, demoWire] using hbind
  exact pub33_zero_ne_one hkey.symm

/-- **No universal session-key-binding law follows from authentication.**  Even
though every concrete delivery in this model may carry the flag, the flag does
not determine the session key or its relation to the payload. -/
theorem not_universal_sessionKeyBinding :
    ¬ ∀ d : AuthenticatedDelivery,
        TransportAuthenticated d → SessionKeyBinding d := by
  intro hall
  obtain ⟨d, hauth, hnot⟩ := authenticated_not_bound
  exact hnot (hall d hauth)

/-- **An unattributed delivery exists.**  The transport can authenticate a
session whose key is not the funding key advertised by the delivered opening. -/
theorem unattributed_delivery_exists :
    ∃ d : AuthenticatedDelivery,
      TransportAuthenticated d ∧ ¬ EnvelopeAttributed d.envelope := by
  refine ⟨demoUnattributedDelivery, demoUnattributedDelivery_authenticated, ?_⟩
  intro hattr
  have hkey : pub33 1 = pub33 0 := by
    simpa [demoUnattributedDelivery, demoDelivery, demoSession,
      AuthenticatedDelivery.envelope, demoWire] using hattr
  exact pub33_zero_ne_one hkey.symm

/-- **Same wire, two authenticated sessions.**  The type-32 record has no
sender field, so one payload can be delivered by two established sessions with
different keys. -/
theorem wire_payload_does_not_determine_session_key :
    ∃ d₁ d₂ : AuthenticatedDelivery,
      d₁.wire = d₂.wire ∧
        TransportAuthenticated d₁ ∧ TransportAuthenticated d₂ ∧
        d₁.session.peerKey ≠ d₂.session.peerKey := by
  refine ⟨demoAttributedDelivery, demoUnattributedDelivery, rfl, rfl, rfl, ?_⟩
  simpa [demoAttributedDelivery, demoUnattributedDelivery, demoDelivery,
    demoSession] using pub33_zero_ne_one

/-- **`transport_auth_not_from_wire`.**  The same wire is delivered by two
authenticated sessions; only the delivery whose session key equals the
advertised funding key is `EnvelopeAttributed`.  Transport authentication of a
session does not authenticate the sender of a particular payload. -/
theorem transport_auth_not_from_wire :
    ∃ d₁ d₂ : AuthenticatedDelivery,
      d₁.wire = d₂.wire ∧
        TransportAuthenticated d₁ ∧ TransportAuthenticated d₂ ∧
        EnvelopeAttributed d₁.envelope ∧
        ¬ EnvelopeAttributed d₂.envelope := by
  refine ⟨demoAttributedDelivery, demoUnattributedDelivery, rfl, rfl, rfl,
    demoAttributedDelivery_attributed, ?_⟩
  intro hattr
  have hkey : pub33 1 = pub33 0 := by
    simpa [demoUnattributedDelivery, demoDelivery, demoSession,
      AuthenticatedDelivery.envelope, demoWire] using hattr
  exact pub33_zero_ne_one hkey.symm

/-- **The key-binding law is not implied by the wire or by authentication.**
The same wire satisfies `SessionKeyBinding` for one authenticated session and
fails it for another.  This is the `no_session_binding_counterexample`. -/
theorem no_session_binding_counterexample :
    ∃ d₁ d₂ : AuthenticatedDelivery,
      d₁.wire = d₂.wire ∧
        TransportAuthenticated d₁ ∧ TransportAuthenticated d₂ ∧
        SessionKeyBinding d₁ ∧ ¬ SessionKeyBinding d₂ ∧
        EnvelopeAttributed d₁.envelope ∧
        ¬ EnvelopeAttributed d₂.envelope := by
  refine ⟨demoAttributedDelivery, demoUnattributedDelivery, rfl, rfl, rfl,
    demoAttributedDelivery_bound, ?_, demoAttributedDelivery_attributed, ?_⟩
  · intro hbind
    have hkey : pub33 1 = pub33 0 := by
      simpa [demoUnattributedDelivery, demoDelivery, demoSession,
        SessionKeyBinding, demoWire] using hbind
    exact pub33_zero_ne_one hkey.symm
  · intro hattr
    have hkey : pub33 1 = pub33 0 := by
      simpa [demoUnattributedDelivery, demoDelivery, demoSession,
        AuthenticatedDelivery.envelope, demoWire] using hattr
    exact pub33_zero_ne_one hkey.symm

/-- **No sender function of the wire.**  There is no function from the type-32
payload to a session key that is correct for every authenticated delivery.
This is the strongest form of "the wire alone does not authenticate the
sender": the payload is compatible with two keys. -/
theorem no_wire_sender_function :
    ¬ ∃ f : OpenChannelWire → PubKey,
        ∀ d : AuthenticatedDelivery,
          TransportAuthenticated d → f d.wire = d.session.peerKey := by
  rintro ⟨f, hf⟩
  have h1 : f demoAttributedDelivery.wire =
      demoAttributedDelivery.session.peerKey :=
    hf demoAttributedDelivery demoAttributedDelivery_authenticated
  have h2 : f demoUnattributedDelivery.wire =
      demoUnattributedDelivery.session.peerKey :=
    hf demoUnattributedDelivery demoUnattributedDelivery_authenticated
  have hw : demoAttributedDelivery.wire = demoUnattributedDelivery.wire := rfl
  rw [hw] at h1
  have hkey : pub33 0 = pub33 1 := by
    simpa [demoAttributedDelivery, demoUnattributedDelivery, demoDelivery,
      demoSession] using h1.symm.trans h2
  exact pub33_zero_ne_one hkey

/-- No function of the wire alone can decide attribution for all authenticated
deliveries.  This restates the same boundary directly over
`EnvelopeAttributed`. -/
theorem no_wire_attribution_function :
    ¬ ∃ f : OpenChannelWire → Prop,
        ∀ d : AuthenticatedDelivery,
          TransportAuthenticated d →
            (f d.wire ↔ EnvelopeAttributed d.envelope) := by
  rintro ⟨f, hf⟩
  have h1 : f demoAttributedDelivery.wire ↔
      EnvelopeAttributed demoAttributedDelivery.envelope :=
    hf demoAttributedDelivery demoAttributedDelivery_authenticated
  have h2 : f demoUnattributedDelivery.wire ↔
      EnvelopeAttributed demoUnattributedDelivery.envelope :=
    hf demoUnattributedDelivery demoUnattributedDelivery_authenticated
  have hw : demoAttributedDelivery.wire = demoUnattributedDelivery.wire := rfl
  have hfA : f demoUnattributedDelivery.wire := by
    rw [← hw]
    exact h1.2 demoAttributedDelivery_attributed
  have hattr : EnvelopeAttributed demoUnattributedDelivery.envelope :=
    h2.1 hfA
  have hkey : pub33 1 = pub33 0 := by
    simpa [demoUnattributedDelivery, demoDelivery, demoSession,
      AuthenticatedDelivery.envelope, demoWire] using hattr
  exact pub33_zero_ne_one hkey.symm

/-- The opening payload carries no signature: transport authentication is not
proof of possession and does not establish C3/key ownership. -/
theorem authenticated_delivery_no_signature (d : AuthenticatedDelivery) :
    signatures (.openChannel d.wire) = [] :=
  wire_carries_no_signature d.wire

/-- The funding key used by the authenticated delivery is still only an
advertised value.  Any valid key can be placed in the wire, independently of
the session key, so the payload alone never forces key ownership. -/
theorem advertised_key_independent_of_session_key (d : AuthenticatedDelivery)
    {k : PubKey} (hk : k.Valid) :
    ∃ d' : AuthenticatedDelivery,
      d'.session = d.session ∧
        d'.wire.fundingPubKey = k ∧
        wellFormed (.openChannel d'.wire) := by
  refine ⟨{ d with wire := demoWire k }, rfl, rfl, demoWire_wellFormed hk⟩

/-! ## 6. Summary -/

/-- Bundled reading of the transport-authentication layer:

1. authentication plus the explicit key-binding law gives attribution;
2. the attributed delivery composes with the routed opening -> accept ->
   `funding_created` witness and the funding construction;
3. the same wire can arrive over two authenticated sessions with different
   keys, and only one is attributed;
4. no function of the wire determines the session key or attribution;
5. the wire carries no signature, so C3/key ownership is not derived. -/
theorem transport_auth_summary :
    (∀ d : AuthenticatedDelivery,
        TransportAuthenticated d → SessionKeyBinding d →
          EnvelopeAttributed d.envelope) ∧
      (∀ (d : AuthenticatedDelivery) (a : AcceptChannel),
        TransportAuthenticated d → SessionKeyBinding d →
          OpenRouteReachable (afterOpenRoute d.envelope) ∧
            ∃ s1 s2 : HandshakeState,
              handshakeStepRecvAccept
                  (afterOpenRoute d.envelope).peer.handshake a = some s1 ∧
                handshakeStep s1 .sendFundingCreated = some s2 ∧
                s1.acceptChannel? = some a ∧
                s2.acceptReceived = true) ∧
      (∃ d₁ d₂ : AuthenticatedDelivery,
        d₁.wire = d₂.wire ∧
          TransportAuthenticated d₁ ∧ TransportAuthenticated d₂ ∧
          EnvelopeAttributed d₁.envelope ∧
          ¬ EnvelopeAttributed d₂.envelope) ∧
      (∃ d : AuthenticatedDelivery,
        TransportAuthenticated d ∧ ¬ EnvelopeAttributed d.envelope) ∧
      (¬ ∃ f : OpenChannelWire → PubKey,
        ∀ d : AuthenticatedDelivery,
          TransportAuthenticated d → f d.wire = d.session.peerKey) ∧
      (∀ d : AuthenticatedDelivery,
        signatures (.openChannel d.wire) = []) := by
  refine ⟨fun d hauth hbind =>
      transport_authenticated_attributed d hauth hbind, ?_, ?_, ?_, ?_, ?_⟩
  · intro d a hauth hbind
    exact (authenticated_delivery_reaches_fundingCreated d a hauth hbind).2
  · exact transport_auth_not_from_wire
  · exact unattributed_delivery_exists
  · exact no_wire_sender_function
  · exact authenticated_delivery_no_signature

end LnLean.Proofs.Protocol.TransportAuthTargets
