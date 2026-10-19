import LnLean.Proofs.Protocol.OpenChannelWireTargets
import LnLean.Proofs.Bitcoin.FundingAuthTargets

/-!
# `open_channel` transport attribution and handshake routing (`L1-03`, wave 9)

**English claim.**  BOLT 2's type-32 `open_channel` is the first channel
establishment message.  Wave 8 added `Msg.openChannel`, the wire-complete
`OpenChannelWire` record, and the funding projection
`OpenChannelWire.toHandshakeOpenChannel`, and proved that the wire record
reaches the separate `FundingPhase` machine.  It left three boundaries
explicit:

1. the payload carries **no sender identity**, so the transport, not the wire,
   must attribute the message to a peer;
2. `HandshakeState`/`handshakeStep` have **no opening transition** (the v1
   machine absorbs the arrival of `open_channel` into the guard on
   `sendAcceptChannel`), so receiving the wire record is not routed anywhere;
3. `Peer.receive` rejects `open_channel` unless a channel record already
   exists under the temporary channel id — impossible for the opening message.

This module closes the routing *model* additively and proves the strongest
faithful attribution statements, without editing `Messages.lean`,
`Handshake.lean`, or `Peer.lean`.

## What is modelled

* `OpenChannelEnvelope` is the transport-delivered record: the authenticated
  sender identity claimed by the transport (reusing
  `FundingAuthTargets.PeerIdentity`) together with the unchanged type-32 wire
  payload.  The envelope, not the payload, is where provenance lives.
* `EnvelopeAttributed` is the explicit attribution hypothesis: the
  transport-authenticated key is the `funding_pubkey` carried by the wire
  record.  This is exactly `FundingAuthTargets.OpenChannelAttributed` lifted to
  the wire record through `toHandshakeOpenChannel`.
* `OpenRouteState` wraps the **unchanged** `PeerState` and records at most one
  received envelope.  `openRouteStep` has two events: the existing
  `HandshakeEvent`s (`plain`) and `recvOpen`.  The `recvOpen` guard requires a
  connected transport and the exact pre-accept handshake configuration
  (`init` exchanged, no accept/funding/ready milestone moved).  It records the
  envelope and leaves `HandshakeState` unchanged — the honest routing statement
  for a machine whose opening milestone is absorbed by the accept guard.
* `OpenRouteReachable` is the reachability closure.  A received envelope has
  actual receive-step provenance (`openRouteReachable_received?_provenance`),
  cannot be overwritten (`openRouteReachable_received?_stable`), and the
  routing step is gated by `HandshakeState` (`openRouteStep_recvOpen_inited`).
* After routing, the usual `handshakeStepRecvAccept` accepts and records
  `accept_channel`, and `handshakeStep .sendFundingCreated` is enabled.  This
  composes with `OpenChannelWireTargets.acceptorPhaseAfter` to give the
  wire -> `Handshake.OpenChannel` -> funding reachability path.
* `wire_output_determines_key_set` restates the wave-7/8 funding-key binding
  for the wire record.  It takes exactly the finite `CollisionFreeOn H` pair
  admission; `wire_binding_needs_FundingScript_C1` records that the model's
  32-byte C1 does not bind 71-byte funding scripts
  (`c1_32_does_not_bind_funding_witnessScripts`).

## The sharp non-attribution / forgery boundary

No theorem concludes that a wire record authenticates a peer.  The module
mechanizes the negatives:

* `wire_payload_does_not_determine_sender` — one payload, two distinct
  transport senders;
* `same_wire_attributed_and_not` — the *same* payload is attributable to one
  peer and not to another; only the transport envelope distinguishes them;
* `openRouteStep_recvOpen_observed_ignores_sender` and
  `route_outcome_independent_of_attribution` — the routed observable state and
  the funding construction are functions of the wire record alone, so
  attribution cannot be read back from protocol state;
* `unattributed_open_is_routed` — a reachable state routes an unattributed
  envelope: the receive rule does not check the key binding;
* `wellFormed_wire_not_attributed` and
  `hash_link_does_not_imply_attribution` — well-formedness and the funding
  hash link hold for records with an arbitrary (valid) funding key, so neither
  supplies attribution;
* `wire_carries_no_signature` — `Msg.openChannel` contributes no ECDSA
  signature to the message signature list, so the wire gives no
  proof-of-possession evidence.  Key ownership remains the C3/`PR-01`
  obligation.

## Non-vacuity

`afterOpenRoute_reachable` and `openRoute_initial_to_fundingCreated` exhibit a
concrete reachable route from the connected initial state through `open_channel`
and `accept_channel` to `funding_created`.

## BOLT sections

* BOLT 2 §"Channel Establishment v1" (`refs/bolts/02-peer-protocol.md:629-1136`):
  the `open_channel` (32), `accept_channel` (33), `funding_created` (34)
  ordering.
* BOLT 1 §"Lightning Message Format" (`refs/bolts/01-messaging.md:43-92`): the
  two-byte type prefix; no transport authentication is part of the payload.
* BOLT 2 §"The `open_channel` Message": `funding_pubkey` is advertised, not
  proved.
-/

namespace LnLean.Proofs.Protocol.OpenChannelRoutingTargets

set_option autoImplicit false

open LnLean
open LnLean.Protocol
open LnLean.Bitcoin
open LnLean.Proofs.Bitcoin.FundingScriptTargets
open LnLean.Proofs.Bitcoin.FundingAuthTargets
open LnLean.Proofs.Protocol.OpenChannelWireTargets

/-! ## 1. Transport attribution: the envelope, not the payload -/

/-- A type-32 message as delivered by the transport: the authenticated peer
identity the transport attaches, plus the unchanged wire payload.  The payload
has no sender field; this structure is the observable provenance. -/
structure OpenChannelEnvelope where
  /-- The peer identity the transport claims for this delivery. -/
  sender : PeerIdentity
  /-- The type-32 payload exactly as received. -/
  wire : OpenChannelWire

/-- The funding-relevant `Handshake.OpenChannel` projection of the envelope. -/
def OpenChannelEnvelope.open (r : OpenChannelEnvelope) : OpenChannel :=
  r.wire.toHandshakeOpenChannel

@[simp] theorem OpenChannelEnvelope.open_eq (r : OpenChannelEnvelope) :
    r.open = r.wire.toHandshakeOpenChannel := rfl

/-- **Transport attribution for the wire record.**  The transport-authenticated
peer key is the opener's advertised funding key.  This is the explicit
hypothesis of `FundingAuthTargets.attributed_key_in_script`, lifted through
`toHandshakeOpenChannel`; it is not derivable from the payload. -/
def EnvelopeAttributed (r : OpenChannelEnvelope) : Prop :=
  OpenChannelAttributed r.sender r.wire.toHandshakeOpenChannel

/-- Attribution is exactly equality of the transport key and the wire funding
key.  The definition is not hiding a signature check or a key-ownership
assumption. -/
theorem envelopeAttributed_iff (r : OpenChannelEnvelope) :
    EnvelopeAttributed r ↔ r.sender.key = r.wire.fundingPubKey := by
  simp [EnvelopeAttributed, OpenChannelAttributed, OpenChannelWire.toHandshakeOpenChannel]

/-- Attribution for the concrete pair `(sender, wire)`. -/
@[simp] theorem envelopeAttributed_pair (w : OpenChannelWire)
    (i : PeerIdentity) :
    EnvelopeAttributed ⟨i, w⟩ ↔ i.key = w.fundingPubKey := by
  simp [envelopeAttributed_iff]

/-- **Conditional key authentication at the wire layer.**  Under transport
attribution, the authenticated peer key is literally the local funding key of
the joint wire construction and occurs in the constructed witness script.
This is `FundingAuthTargets.attributed_key_in_script` transported through the
wire projection; no additional hypothesis is used. -/
theorem attributed_wire_key_in_script (H : ByteArray → ByteArray)
    (r : OpenChannelEnvelope) (a : AcceptChannel)
    (hattr : EnvelopeAttributed r) :
    r.sender.key = (r.wire.toFundingNegotiation a).localFundingKey ∧
      KeyInScript (r.wire.toFundingParams H a).witnessScript.bytes r.sender.key := by
  have h := attributed_key_in_script H r.sender r.wire.toHandshakeOpenChannel a hattr
  refine ⟨?_, ?_⟩
  · simpa [OpenChannelWire.toFundingNegotiation] using h.1
  · rw [show r.wire.toFundingParams H a =
        OpenChannel.toFundingParams H r.wire.toHandshakeOpenChannel a from rfl]
    exact h.2

/-! ## 2. The wire payload does not carry its sender -/

/-- Distinct 33-byte public keys used only for the boundary witnesses. -/
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

/-- For every key there is a different well-formed (33-byte) key. -/
theorem exists_valid_pubKey_ne (k : PubKey) :
    ∃ k' : PubKey, k'.Valid ∧ k' ≠ k := by
  by_cases h : pub33 0 = k
  · refine ⟨pub33 1, pub33_valid 1, ?_⟩
    rw [← h]
    exact Ne.symm pub33_zero_ne_one
  · exact ⟨pub33 0, pub33_valid 0, h⟩

/-- A well-formed demo wire record with the given funding key.  All six public
keys are the same key, and the temporary channel id is the canonical 32-byte
zero id; only the funding key matters for the boundary results. -/
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

/-- **One payload, two senders.**  The wire record contains no sender field,
so the same type-32 payload can arrive with two distinct transport identities.
Attribution must therefore be supplied by the transport envelope. -/
theorem wire_payload_does_not_determine_sender :
    ∃ r₁ r₂ : OpenChannelEnvelope,
      r₁.wire = r₂.wire ∧ r₁.sender ≠ r₂.sender := by
  refine ⟨⟨⟨pub33 0⟩, demoWire (pub33 0)⟩,
    ⟨⟨pub33 1⟩, demoWire (pub33 0)⟩, rfl, ?_⟩
  intro h
  have hkey : pub33 0 = pub33 1 := by
    have h' : (⟨pub33 0⟩ : PeerIdentity) = ⟨pub33 1⟩ := h
    exact congrArg PeerIdentity.key h'
  exact pub33_zero_ne_one hkey

/-- **The same payload is attributed to one peer and not to another.**  This is
the sharp boundary: the wire payload is compatible with both envelopes, and
only the transport's claimed identity separates them. -/
theorem same_wire_attributed_and_not :
    ∃ r₁ r₂ : OpenChannelEnvelope,
      r₁.wire = r₂.wire ∧ EnvelopeAttributed r₁ ∧ ¬ EnvelopeAttributed r₂ := by
  refine ⟨⟨⟨pub33 0⟩, demoWire (pub33 0)⟩,
    ⟨⟨pub33 1⟩, demoWire (pub33 0)⟩, rfl, ?_, ?_⟩
  · simp [envelopeAttributed_pair, demoWire]
  · intro hattr
    have hkey : pub33 1 = pub33 0 := by
      simpa [demoWire] using
        (envelopeAttributed_pair (demoWire (pub33 0)) ⟨pub33 1⟩).1 hattr
    exact pub33_zero_ne_one hkey.symm

/-- Well-formedness does not imply attribution: for any claimed sender there is
a well-formed type-32 record whose funding key differs from the sender's key. -/
theorem wellFormed_wire_not_attributed (i : PeerIdentity) :
    ∃ w : OpenChannelWire,
      wellFormed (.openChannel w) ∧ ¬ EnvelopeAttributed ⟨i, w⟩ := by
  obtain ⟨k', hk'valid, hk'ne⟩ := exists_valid_pubKey_ne i.key
  refine ⟨demoWire k', demoWire_wellFormed hk'valid, ?_⟩
  intro hattr
  have hkey : i.key = k' :=
    (envelopeAttributed_pair (demoWire k') i).1 hattr
  exact hk'ne hkey.symm

/-- **The funding hash link does not imply attribution.**  The constructed
funding parameters are hash-linked by definition, but the funding key is
arbitrary message data and need not be the transport key. -/
theorem hash_link_does_not_imply_attribution (H : ByteArray → ByteArray)
    (i : PeerIdentity) (a : AcceptChannel) :
    ∃ w : OpenChannelWire,
      wellFormed (.openChannel w) ∧
        FundingScriptHashLinked H (w.toFundingParams H a) ∧
        ¬ EnvelopeAttributed ⟨i, w⟩ := by
  obtain ⟨w, hwf, hnot⟩ := wellFormed_wire_not_attributed i
  exact ⟨w, hwf, w.toFundingParams_hash_linked H a, hnot⟩

/-- `open_channel` contributes no ECDSA signature to the message signature
list.  The wire payload therefore contains no proof-of-possession evidence for
`funding_pubkey`; key ownership is the separate C3/`PR-01` obligation. -/
theorem wire_carries_no_signature (w : OpenChannelWire) :
    signatures (.openChannel w) = [] := rfl

/-- Any valid key can be advertised: wire acceptance never checks possession. -/
theorem any_valid_key_advertisable {k : PubKey} (hk : k.Valid) :
    ∃ w : OpenChannelWire,
      wellFormed (.openChannel w) ∧ w.fundingPubKey = k :=
  ⟨demoWire k, demoWire_wellFormed hk, rfl⟩

/-! ## 3. The additive receive/routing state

`HandshakeState` has no opening field and `handshakeStep` has no `recvOpen`
event.  The following wrapper is the additive model: it does not change the v1
state or transition function, and its `recvOpen` event is gated by the same
handshake configuration that enables the v1 `accept_channel` transition. -/

/-- Additive routing state for the type-32 opening message.  `peer` is the
unchanged `PeerState`; `received?` records at most one transport envelope. -/
structure OpenRouteState where
  /-- The unchanged peer/handshake state. -/
  peer : PeerState
  /-- The opening envelope most recently routed, if any. -/
  received? : Option OpenChannelEnvelope := none

namespace OpenRouteState

/-- The connected initial state.  `PeerState.initial` starts with the transport
`down`; connection setup is an environment precondition in this model (the
transport state is set by the environment, not by a protocol transition), so
the routing machine starts from the connected, pre-`init` state. -/
def initial : OpenRouteState where
  peer := { PeerState.initial with transport := TransportState.up }
  received? := none

/-- The v1 receive guard for the opening message: connected transport, both
`init`s exchanged, and no accept/funding/ready milestone moved.  These are
exactly the handshake conditions that enable the v1 accept transition; the
opening message itself is not a `HandshakeEvent`. -/
abbrev canRecvOpen (s : OpenRouteState) : Prop :=
  s.peer.transport = TransportState.up ∧
    s.peer.handshake.initSent = true ∧
    s.peer.handshake.initReceived = true ∧
    s.peer.handshake.acceptSent = false ∧
    s.peer.handshake.acceptReceived = false ∧
    s.peer.handshake.fundingCreatedSent = false ∧
    s.peer.handshake.fundingCreatedReceived = false ∧
    s.peer.handshake.fundingSignedSent = false ∧
    s.peer.handshake.fundingSignedReceived = false ∧
    s.peer.handshake.channelReadySent = false ∧
    s.peer.handshake.channelReadyReceived = false ∧
    s.received? = none

/-- The transport/protocol-observable projection of the routing state: the peer
state and the received wire record, with the transport's claimed sender
forgotten. -/
def observed (s : OpenRouteState) :
    PeerState × Option OpenChannelWire :=
  (s.peer, s.received?.map (fun r => r.wire))

end OpenRouteState

/-- Routing events: the existing handshake events (`plain`) and the additive
type-32 receive (`recvOpen`).  The `plain` form does **not** include a receive
of `open_channel`; that is exactly the missing transition this lane supplies. -/
inductive OpenRouteEvent where
  | plain (e : HandshakeEvent)
  | recvOpen (r : OpenChannelEnvelope)

/-- One deterministic routing transition.  A `plain` event runs the unchanged
`handshakeStep` behind the unchanged transport gate; `recvOpen` requires
`canRecvOpen` and records the envelope, leaving `HandshakeState` untouched. -/
def openRouteStep (s : OpenRouteState) :
    OpenRouteEvent → Option OpenRouteState
  | .plain e =>
      match s.peer.transport with
      | TransportState.down => none
      | TransportState.up =>
          match handshakeStep s.peer.handshake e with
          | some hs => some { s with peer := { s.peer with handshake := hs } }
          | none => none
  | .recvOpen r =>
      if s.canRecvOpen then some { s with received? := some r } else none

/-- Reachable routing states. -/
inductive OpenRouteReachable : OpenRouteState → Prop where
  | initial : OpenRouteReachable OpenRouteState.initial
  | step {s s' : OpenRouteState} (e : OpenRouteEvent) :
      OpenRouteReachable s → openRouteStep s e = some s' → OpenRouteReachable s'

/-! ### Routing-step laws -/

/-- A `plain` step never changes the recorded envelope. -/
theorem openRouteStep_plain_received? {s s' : OpenRouteState}
    {e : HandshakeEvent} (h : openRouteStep s (.plain e) = some s') :
    s'.received? = s.received? := by
  change (match s.peer.transport with
    | TransportState.down => none
    | TransportState.up =>
        match handshakeStep s.peer.handshake e with
        | some hs => some { s with peer := { s.peer with handshake := hs } }
        | none => none) = some s' at h
  cases ht : s.peer.transport with
  | down => simp [ht] at h
  | up =>
      simp only [ht] at h
      split at h
      · obtain rfl := Option.some.inj h
        rfl
      · simp at h

/-- A `recvOpen` step records exactly the delivered envelope. -/
theorem openRouteStep_recvOpen_received? {s s' : OpenRouteState}
    {r : OpenChannelEnvelope} (h : openRouteStep s (.recvOpen r) = some s') :
    s'.received? = some r := by
  change (if s.canRecvOpen then some { s with received? := some r } else none) =
    some s' at h
  by_cases hg : s.canRecvOpen
  · rw [ite_eq_left hg] at h
    obtain rfl := Option.some.inj h
    rfl
  · rw [ite_eq_right hg] at h
    simp at h

/-- A `recvOpen` step leaves the whole `PeerState` unchanged: it only records
the envelope. -/
theorem openRouteStep_recvOpen_peer {s s' : OpenRouteState}
    {r : OpenChannelEnvelope} (h : openRouteStep s (.recvOpen r) = some s') :
    s'.peer = s.peer := by
  change (if s.canRecvOpen then some { s with received? := some r } else none) =
    some s' at h
  by_cases hg : s.canRecvOpen
  · rw [ite_eq_left hg] at h
    obtain rfl := Option.some.inj h
    rfl
  · rw [ite_eq_right hg] at h
    simp at h

/-- A `recvOpen` step leaves `HandshakeState` unchanged: the opening milestone
is not a v1 handshake event; the accept guard is the v1 routing point. -/
theorem openRouteStep_recvOpen_handshake {s s' : OpenRouteState}
    {r : OpenChannelEnvelope} (h : openRouteStep s (.recvOpen r) = some s') :
    s'.peer.handshake = s.peer.handshake := by
  change (if s.canRecvOpen then some { s with received? := some r } else none) =
    some s' at h
  by_cases hg : s.canRecvOpen
  · rw [ite_eq_left hg] at h
    obtain rfl := Option.some.inj h
    rfl
  · rw [ite_eq_right hg] at h
    simp at h

/-- A successful `recvOpen` implies its guard held. -/
theorem canRecvOpen_of_recvOpen {s s' : OpenRouteState}
    {r : OpenChannelEnvelope} (h : openRouteStep s (.recvOpen r) = some s') :
    s.canRecvOpen := by
  change (if s.canRecvOpen then some { s with received? := some r } else none) =
    some s' at h
  by_cases hg : s.canRecvOpen
  · exact hg
  · rw [ite_eq_right hg] at h
    simp at h

/-- Receiving `open_channel` is gated by both `init` messages: the v1 ordering
is not bypassed. -/
theorem openRouteStep_recvOpen_inited {s s' : OpenRouteState}
    {r : OpenChannelEnvelope} (h : openRouteStep s (.recvOpen r) = some s') :
    s.peer.handshake.initSent = true ∧
      s.peer.handshake.initReceived = true := by
  have hg := canRecvOpen_of_recvOpen h
  exact ⟨hg.2.1, hg.2.2.1⟩

/-- The opening guard contains the v1 accept guard. -/
theorem canSendAccept_of_canRecvOpen {s : OpenRouteState}
    (h : s.canRecvOpen) : s.peer.handshake.canSendAccept := by
  rcases h with ⟨_ht, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, _hr⟩
  simp [HandshakeState.canSendAccept, HandshakeState.inited,
    HandshakeState.noReady, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]

/-- After routing the opening message, the handshake is exactly in the state
where `accept_channel` may be sent. -/
theorem openRouteStep_recvOpen_canSendAccept {s s' : OpenRouteState}
    {r : OpenChannelEnvelope} (h : openRouteStep s (.recvOpen r) = some s') :
    s'.peer.handshake.canSendAccept := by
  rw [openRouteStep_recvOpen_handshake h]
  exact canSendAccept_of_canRecvOpen (canRecvOpen_of_recvOpen h)

/-- After routing the opening message, the handshake is in the state where a
payload-carrying `accept_channel` receive is permitted. -/
theorem openRouteStep_recvOpen_canRecvAccept {s s' : OpenRouteState}
    {r : OpenChannelEnvelope} (h : openRouteStep s (.recvOpen r) = some s') :
    s'.peer.handshake.canRecvAccept := by
  have hsend := openRouteStep_recvOpen_canSendAccept h
  simpa [HandshakeState.canSendAccept, HandshakeState.canRecvAccept] using hsend

/-! ### Provenance and stability -/

/-- **Envelope provenance.**  In a reachable routing state, a recorded envelope
comes from an actual `recvOpen` transition.  The field is not a free-floating
claim and cannot be populated by a `plain` handshake step. -/
theorem openRouteReachable_received?_provenance {s : OpenRouteState}
    (h : OpenRouteReachable s) :
    ∀ {r : OpenChannelEnvelope}, s.received? = some r →
      ∃ s0 s1 : OpenRouteState,
        OpenRouteReachable s0 ∧ openRouteStep s0 (.recvOpen r) = some s1 := by
  induction h with
  | initial =>
      intro r hr
      simp [OpenRouteState.initial] at hr
  | step e hprev hstep ih =>
      intro r hr
      cases e with
      | plain e =>
          have hpres := openRouteStep_plain_received? hstep
          rw [hpres] at hr
          exact ih hr
      | recvOpen r' =>
          have hr' := openRouteStep_recvOpen_received? hstep
          rw [hr'] at hr
          have heq : r' = r := Option.some.inj hr
          subst heq
          exact ⟨_, _, hprev, hstep⟩

/-- **The recorded envelope is stable.**  Once a reachable state has recorded
an opening envelope, no later routing step replaces it; a second `recvOpen` is
blocked by the `received? = none` guard. -/
theorem openRouteReachable_received?_stable {s s' : OpenRouteState}
    (_h : OpenRouteReachable s) {e : OpenRouteEvent}
    (hstep : openRouteStep s e = some s')
    {r : OpenChannelEnvelope} (hr : s.received? = some r) :
    s'.received? = some r := by
  cases e with
  | plain e =>
      rw [openRouteStep_plain_received? hstep, hr]
  | recvOpen r' =>
      have hg : s.canRecvOpen := canRecvOpen_of_recvOpen hstep
      rcases hg with ⟨_ht, _h1, _h2, _h3, _h4, _h5, _h6, _h7, _h8, _h9,
        _h10, hnone⟩
      rw [hnone] at hr
      simp at hr

/-- **Routing is blind to the sender.**  Two envelopes with the same wire but
different transport identities produce the same transport-observable state.
The transport's attribution is not an observable of the routing machine. -/
theorem openRouteStep_recvOpen_observed_ignores_sender
    {s s₁ s₂ : OpenRouteState} {i₁ i₂ : PeerIdentity} {w : OpenChannelWire}
    (h₁ : openRouteStep s (.recvOpen ⟨i₁, w⟩) = some s₁)
    (h₂ : openRouteStep s (.recvOpen ⟨i₂, w⟩) = some s₂) :
    s₁.observed = s₂.observed := by
  have hp₁ := openRouteStep_recvOpen_peer h₁
  have hp₂ := openRouteStep_recvOpen_peer h₂
  have hr₁ := openRouteStep_recvOpen_received? h₁
  have hr₂ := openRouteStep_recvOpen_received? h₂
  simp [OpenRouteState.observed, hp₁, hp₂, hr₁, hr₂]

/-- The same blindness stated for envelopes whose wires are equal but whose
attribution may differ. -/
theorem route_outcome_independent_of_attribution
    {s s₁ s₂ : OpenRouteState} {r₁ r₂ : OpenChannelEnvelope}
    (hw : r₁.wire = r₂.wire)
    (h₁ : openRouteStep s (.recvOpen r₁) = some s₁)
    (h₂ : openRouteStep s (.recvOpen r₂) = some s₂) :
    s₁.observed = s₂.observed := by
  have hp₁ := openRouteStep_recvOpen_peer h₁
  have hp₂ := openRouteStep_recvOpen_peer h₂
  have hr₁ := openRouteStep_recvOpen_received? h₁
  have hr₂ := openRouteStep_recvOpen_received? h₂
  simp [OpenRouteState.observed, hp₁, hp₂, hr₁, hr₂, hw]

/-! ## 4. From the routed opening to the handshake and funding machine -/

/-- After a permitted `sendAcceptChannel` configuration, the payload-carrying
`accept_channel` receive is permitted, and its successor can send
`funding_created`.  This is the handshake-routing half of the path; it is
proved with the unchanged `handshakeStepRecvAccept` and `handshakeStep`. -/
theorem canSendFundingCreated_after_recvAccept {s : HandshakeState}
    (h : s.canSendAccept) (a : AcceptChannel) :
    ({ s with acceptReceived := true, acceptChannel? := some a }).canSendFundingCreated := by
  rcases h with ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5, _h6, h7, h8, h9, h10⟩
  simp [HandshakeState.canSendFundingCreated, HandshakeState.inited,
    HandshakeState.noReady, h1, h2, h3, h4, h5, h7, h8, h9, h10]

/-- **Payload-carrying accept then `funding_created`.**  From any handshake
state with the accept guard, receiving `accept_channel` records its payload and
enables `funding_created`.  No opening-transition patch to `HandshakeState` is
needed: the opening is recorded in `OpenRouteState` and the accept is the v1
routing point. -/
theorem handshake_recvAccept_then_fundingCreated {s : HandshakeState}
    (h : s.canSendAccept) (a : AcceptChannel) :
    ∃ s1 s2 : HandshakeState,
      handshakeStepRecvAccept s a = some s1 ∧
        handshakeStep s1 .sendFundingCreated = some s2 ∧
        s1.acceptChannel? = some a ∧
        s2.acceptReceived = true := by
  let s1 : HandshakeState :=
    { s with acceptReceived := true, acceptChannel? := some a }
  let s2 : HandshakeState := { s1 with fundingCreatedSent := true }
  have hrc : s.canRecvAccept := by
    simpa [HandshakeState.canSendAccept, HandshakeState.canRecvAccept] using h
  have hstep1 : handshakeStep s .recvAcceptChannel =
      some { s with acceptReceived := true } := by
    simp [handshakeStep, hrc]
  have hrec : handshakeStepRecvAccept s a = some s1 := by
    simp [handshakeStepRecvAccept, hstep1, s1, HandshakeState.recordAccept]
  have hguard : s1.canSendFundingCreated := by
    simpa [s1] using canSendFundingCreated_after_recvAccept h a
  have hstep2 : handshakeStep s1 .sendFundingCreated = some s2 := by
    simp [handshakeStep, hguard, s2]
  exact ⟨s1, s2, hrec, hstep2, by simp [s1], by simp [s1, s2]⟩

/-! ### A concrete reachable route -/

/-- The handshake after both `init` messages. -/
def afterInitHandshake : HandshakeState :=
  { HandshakeState.initial with initSent := true, initReceived := true }

/-- The routing state after sending `init` but before receiving the peer's. -/
def afterSendInitRoute : OpenRouteState where
  peer := { PeerState.initial with transport := TransportState.up, handshake := { HandshakeState.initial with initSent := true } }
  received? := none

/-- The connected, post-`init`, pre-accept routing state. -/
def afterInitRoute : OpenRouteState where
  peer := { PeerState.initial with transport := TransportState.up, handshake := afterInitHandshake }
  received? := none

theorem afterInitRoute_reachable : OpenRouteReachable afterInitRoute := by
  have h1 : openRouteStep OpenRouteState.initial (.plain .sendInit) =
      some afterSendInitRoute := by
    simp [openRouteStep, handshakeStep, OpenRouteState.initial,
      afterSendInitRoute, HandshakeState.canSendInit, HandshakeState.initial,
      PeerState.initial]
  have h2 : openRouteStep afterSendInitRoute (.plain .recvInit) =
      some afterInitRoute := by
    simp [openRouteStep, handshakeStep, HandshakeState.canRecvInit,
      afterSendInitRoute, afterInitRoute, afterInitHandshake,
      HandshakeState.initial]
  exact OpenRouteReachable.step _
    (OpenRouteReachable.step _ OpenRouteReachable.initial h1) h2

/-- The routing state after receiving the opening envelope. -/
def afterOpenRoute (r : OpenChannelEnvelope) : OpenRouteState :=
  { afterInitRoute with received? := some r }

theorem afterInitRoute_canRecvOpen : afterInitRoute.canRecvOpen := by
  simp [OpenRouteState.canRecvOpen, afterInitRoute, afterInitHandshake,
    PeerState.initial, HandshakeState.initial]

theorem afterOpenRoute_reachable (r : OpenChannelEnvelope) :
    OpenRouteReachable (afterOpenRoute r) := by
  have hstep : openRouteStep afterInitRoute (.recvOpen r) =
      some (afterOpenRoute r) := by
    change (if afterInitRoute.canRecvOpen then
      some { afterInitRoute with received? := some r } else none) =
        some (afterOpenRoute r)
    rfl
  exact OpenRouteReachable.step _ afterInitRoute_reachable hstep

@[simp] theorem afterOpenRoute_received? (r : OpenChannelEnvelope) :
    (afterOpenRoute r).received? = some r := rfl

theorem afterOpenRoute_canSendAccept (r : OpenChannelEnvelope) :
    (afterOpenRoute r).peer.handshake.canSendAccept := by
  have hsend := canSendAccept_of_canRecvOpen afterInitRoute_canRecvOpen
  simpa [afterOpenRoute] using hsend

theorem afterOpenRoute_canRecvAccept (r : OpenChannelEnvelope) :
    (afterOpenRoute r).peer.handshake.canRecvAccept := by
  have hsend := afterOpenRoute_canSendAccept r
  simpa [HandshakeState.canSendAccept, HandshakeState.canRecvAccept] using hsend

/-- **End-to-end routing witness.**  From the connected initial state, the
type-32 envelope is received, the `accept_channel` payload is recorded, and
`funding_created` is enabled.  The handwritten route is mechanized, so the
routing model is not vacuous. -/
theorem openRoute_initial_to_fundingCreated (r : OpenChannelEnvelope)
    (a : AcceptChannel) :
    OpenRouteReachable (afterOpenRoute r) ∧
      ∃ s1 s2 : HandshakeState,
        handshakeStepRecvAccept (afterOpenRoute r).peer.handshake a = some s1 ∧
          handshakeStep s1 .sendFundingCreated = some s2 ∧
          s1.acceptChannel? = some a ∧
          s2.acceptReceived = true :=
  ⟨afterOpenRoute_reachable r,
    handshake_recvAccept_then_fundingCreated (afterOpenRoute_canSendAccept r) a⟩

/-- **Unattributed openings are routed.**  There is a reachable state whose
recorded envelope is not attributed, so the receive rule does not check the key
binding.  Attribution is an additional transport-layer hypothesis, not a
precondition of the protocol state machine. -/
theorem unattributed_open_is_routed :
    ∃ (s : OpenRouteState) (r : OpenChannelEnvelope),
      OpenRouteReachable s ∧ s.received? = some r ∧ ¬ EnvelopeAttributed r := by
  let r : OpenChannelEnvelope := ⟨⟨pub33 1⟩, demoWire (pub33 0)⟩
  refine ⟨afterOpenRoute r, r, afterOpenRoute_reachable r, rfl, ?_⟩
  intro hattr
  have hkey : pub33 1 = pub33 0 := by
    simpa [r, demoWire] using
      (envelopeAttributed_pair (demoWire (pub33 0)) ⟨pub33 1⟩).1 hattr
  exact pub33_zero_ne_one hkey.symm

/-! ## 5. Wire -> `Handshake.OpenChannel` -> funding reachability -/

/-- The funding phase that has received exactly the wire opening. -/
def receivedPhase (w : OpenChannelWire) : FundingPhase where
  openSent := none
  openReceived := some w.toHandshakeOpenChannel
  acceptSent := none
  acceptReceived := none

/-- Receiving the projected wire opening is a legal one-step funding phase. -/
theorem receivedPhase_reachable (w : OpenChannelWire) :
    FundingReachable (receivedPhase w) := by
  have h : fundingStep FundingPhase.initial
      (.recvOpen w.toHandshakeOpenChannel) = some (receivedPhase w) := by
    simp [fundingStep, FundingPhase.initial, FundingPhase.canRecvOpen, receivedPhase]
  exact FundingReachable.step _ FundingReachable.initial h

@[simp] theorem receivedPhase_openReceived (w : OpenChannelWire) :
    (receivedPhase w).openReceived = some w.toHandshakeOpenChannel := rfl

/-- The routed envelope's stored wire projects to the exact
`Handshake.OpenChannel` record used by the funding machine. -/
theorem routed_wire_projection (r : OpenChannelEnvelope) :
    r.open = r.wire.toHandshakeOpenChannel := rfl

/-- **Wire -> funding phase, from a reachable routed state.**  A reachable
state that has recorded an opening envelope yields a reachable funding phase
recording exactly that envelope's `Handshake.OpenChannel` projection. -/
theorem routed_open_to_funding_phase {s : OpenRouteState}
    (_h : OpenRouteReachable s) {r : OpenChannelEnvelope}
    (_hr : s.received? = some r) :
    FundingReachable (receivedPhase r.wire) ∧
      (receivedPhase r.wire).openReceived =
        some r.wire.toHandshakeOpenChannel :=
  ⟨receivedPhase_reachable r.wire, rfl⟩

/-- **Wire -> `Handshake.OpenChannel` -> funding construction.**  From a
reachable routed state, the wire envelope's projection drives the acceptor
funding phase: the negotiation is available, the hash link holds by
construction, and the funding output is the P2WSH of the ordered BOLT 3 2-of-2
script.  No signature check or sender identity is used. -/
theorem routed_open_to_funding_construction {s : OpenRouteState}
    (_h : OpenRouteReachable s) {r : OpenChannelEnvelope}
    (_hr : s.received? = some r) (H : ByteArray → ByteArray)
    (a : AcceptChannel) :
    FundingReachable (acceptorPhaseAfter r.wire a) ∧
      (acceptorPhaseAfter r.wire a).acceptorNegotiation? =
        some (r.wire.toFundingNegotiation a) ∧
      FundingScriptHashLinked H (r.wire.toFundingParams H a) ∧
      (r.wire.toFundingParams H a).fundingScriptPubKey =
        p2wsh (H (TwoOfTwoScriptBytes
          (r.wire.toFundingNegotiation a).firstFundingKey
          (r.wire.toFundingNegotiation a).secondFundingKey)) :=
  ⟨acceptorPhaseAfter_reachable r.wire a,
    acceptorPhaseAfter_negotiation r.wire a,
    r.wire.toFundingParams_hash_linked H a,
    r.wire.toFundingParams_fundingScriptPubKey_eq_p2wsh_ordered H a⟩

/-- The routed opening coexists with a recorded `accept_channel` and the
`funding_created` milestone: whenever a handshake state permits
`funding_created`, its accept milestone is set and the wire construction's
remote funding key is exactly the recorded `accept_channel.funding_pubkey`.
This is the wave-7/8 boundary theorem transported through the wire projection. -/
theorem routed_open_accept_bound_before_fundingCreated
    {s : OpenRouteState} (_h : OpenRouteReachable s)
    {r : OpenChannelEnvelope} (_hr : s.received? = some r)
    {hs hs' : HandshakeState}
    (hstep : handshakeStep hs .sendFundingCreated = some hs')
    (a : AcceptChannel) (H : ByteArray → ByteArray) :
    hs.acceptReceived = true ∧
      ((r.wire.toFundingNegotiation a).toFundingParams H).remoteFundingKey =
        a.fundingPubKey :=
  acceptKey_bound_before_fundingCreated_wire hstep r.wire a H

/-! ## 6. The finite C1 admission boundary -/

/-- **Wire-level funding-key binding.**  Two complete wire
`open_channel`/`accept_channel` exchanges that produce the same funding output,
under the finite pair admission `CollisionFreeOn H` at the two witness scripts,
agree on the unordered funding-key set.  This is the wave-7/8 result routed
through `toHandshakeOpenChannel`.  It is not a global injectivity claim. -/
theorem wire_output_determines_key_set (H : ByteArray → ByteArray)
    (w₁ : OpenChannelWire) (a₁ : AcceptChannel)
    (w₂ : OpenChannelWire) (a₂ : AcceptChannel)
    (hwf₁ : (w₁.toFundingParams H a₁).WellFormed)
    (hwf₂ : (w₂.toFundingParams H a₂).WellFormed)
    (heq : (w₁.toFundingParams H a₁).fundingScriptPubKey =
      (w₂.toFundingParams H a₂).fundingScriptPubKey)
    (hc1 : CollisionFreeOn H
      (w₁.toFundingParams H a₁).witnessScript.bytes
      (w₂.toFundingParams H a₂).witnessScript.bytes) :
    (w₁.fundingPubKey = w₂.fundingPubKey ∧
        a₁.fundingPubKey = a₂.fundingPubKey) ∨
      (w₁.fundingPubKey = a₂.fundingPubKey ∧
        a₁.fundingPubKey = w₂.fundingPubKey) := by
  have h := openAccept_output_determines_key_set H
    w₁.toHandshakeOpenChannel a₁ w₂.toHandshakeOpenChannel a₂
    (show (OpenChannel.toFundingParams H w₁.toHandshakeOpenChannel a₁).WellFormed
      from hwf₁)
    (show (OpenChannel.toFundingParams H w₂.toHandshakeOpenChannel a₂).WellFormed
      from hwf₂)
    (show (OpenChannel.toFundingParams H w₁.toHandshakeOpenChannel a₁).fundingScriptPubKey =
        (OpenChannel.toFundingParams H w₂.toHandshakeOpenChannel a₂).fundingScriptPubKey
      from heq)
    (show CollisionFreeOn H
        (OpenChannel.toFundingParams H w₁.toHandshakeOpenChannel a₁).witnessScript.bytes
        (OpenChannel.toFundingParams H w₂.toHandshakeOpenChannel a₂).witnessScript.bytes
      from hc1)
  simpa [OpenChannelWire.toHandshakeOpenChannel] using h

/-- **The binding hypothesis cannot be weakened to C1.**  There is a hash with
32-byte output satisfying the model's collision-resistance field that collides
on two distinct 71-byte strings.  This is
`FundingScriptTargets.c1_32_does_not_bind_funding_witnessScripts`, restated at
the wire-routing boundary: `wire_output_determines_key_set` needs the separate
finite `CollisionFreeOn` admission. -/
theorem wire_binding_needs_FundingScript_C1 :
    ∃ H : ByteArray → ByteArray,
      (∀ b : ByteArray, (H b).size = 32) ∧
        LnLean.Crypto.CollisionResistant H ∧
        ∃ x y : ByteArray,
          x.size = 71 ∧ y.size = 71 ∧ x ≠ y ∧ H x = H y :=
  c1_32_does_not_bind_funding_witnessScripts

/-- The funding output is independent of the transport sender: attribution
cannot be read off the constructed output. -/
theorem funding_output_independent_of_sender
    (H : ByteArray → ByteArray) (w : OpenChannelWire)
    (a : AcceptChannel) (i₁ i₂ : PeerIdentity) :
    (⟨i₁, w⟩ : OpenChannelEnvelope).wire.toFundingParams H a =
      (⟨i₂, w⟩ : OpenChannelEnvelope).wire.toFundingParams H a := rfl

/-! ## 7. Existing-API insufficiency (recorded, not patched) -/

/-- The unchanged `Peer.receive` accepts an `open_channel` only when a channel
record already exists under its temporary id; a fresh peer cannot receive the
opening message. -/
theorem peer_receive_openChannel_requires_channel (s : PeerState)
    (w : OpenChannelWire)
    (hf : findChannel s w.temporaryChannelId = none) :
    receive s (.openChannel w) = none :=
  receive_openChannel_requires_channel s w hf

/-- The unchanged `Peer.receive` never records the opening payload, even when
it accepts the message through the channel-record path: `advanceReceived`
ignores `MsgKind.openChannel` and `HandshakeState` is untouched. -/
theorem receive_openChannel_handshake_unchanged {s s' : PeerState}
    {w : OpenChannelWire} (h : receive s (.openChannel w) = some s') :
    s'.handshake = s.handshake := by
  have hup : s.transport = TransportState.up := by
    cases ht : s.transport with
    | down => simp [receive, ht] at h
    | up => rfl
  simp only [receive, hup, receiveEvent?_openChannel] at h
  simp only [LnLean.Protocol.channelId?_openChannel] at h
  split at h
  · obtain rfl := Option.some.inj h
    rfl
  · simp at h

/-- No `HandshakeEvent` corresponds to the opening message in either
direction.  This is why the lane models the receive step additively. -/
theorem no_handshake_event_for_openChannel (w : OpenChannelWire) :
    sendEvent? (.openChannel w) = none ∧
      receiveEvent? (.openChannel w) = none :=
  ⟨sendEvent?_openChannel w, receiveEvent?_openChannel w⟩

/-! ## 8. Summary -/

/-- Bundled faithful reading of the routing/attribution bridge:

1. the envelope projection is exactly the `Handshake.OpenChannel` used by the
   funding machine;
2. receiving the wire opening reaches a funding phase and the full hash-linked
   P2WSH construction;
3. the same payload can be attributed to one peer and not another, and the
   routed observable state ignores the sender;
4. an unattributed opening is still routed, and well-formedness or the funding
   hash link never implies attribution;
5. the wire carries no signature, so possession is not claimed. -/
theorem openChannel_routing_summary :
    (∀ r : OpenChannelEnvelope,
        r.open = r.wire.toHandshakeOpenChannel) ∧
      (∀ w : OpenChannelWire, FundingReachable (receivedPhase w)) ∧
      (∀ (H : ByteArray → ByteArray) (r : OpenChannelEnvelope)
          (a : AcceptChannel),
        FundingReachable (acceptorPhaseAfter r.wire a) ∧
          FundingScriptHashLinked H (r.wire.toFundingParams H a)) ∧
      (∃ r₁ r₂ : OpenChannelEnvelope,
        r₁.wire = r₂.wire ∧ EnvelopeAttributed r₁ ∧ ¬ EnvelopeAttributed r₂) ∧
      (∃ (s : OpenRouteState) (r : OpenChannelEnvelope),
        OpenRouteReachable s ∧ s.received? = some r ∧ ¬ EnvelopeAttributed r) ∧
      (∀ i : PeerIdentity,
        ∃ w : OpenChannelWire,
          wellFormed (.openChannel w) ∧ ¬ EnvelopeAttributed ⟨i, w⟩) ∧
      (∀ w : OpenChannelWire, signatures (.openChannel w) = []) :=
  ⟨fun _r => rfl,
    receivedPhase_reachable,
    fun H r a => ⟨acceptorPhaseAfter_reachable r.wire a,
      r.wire.toFundingParams_hash_linked H a⟩,
    same_wire_attributed_and_not,
    unattributed_open_is_routed,
    wellFormed_wire_not_attributed,
    wire_carries_no_signature⟩

end LnLean.Proofs.Protocol.OpenChannelRoutingTargets
