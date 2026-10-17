import LnLean.Protocol.Handshake

/-!
# LnLean.Protocol.Peer

## English claim

`PeerState` is a peer's protocol state: its claimed identity, the state of the
authenticated transport, the connection's handshake state, and the channels
it knows.  `send` hands a well-scoped message to the transport and advances
the handshake when the message is a handshake message; `receive` consumes an
inbound message and advances the same handshake or a channel's
`channel_reestablish` counters; `resend` returns the last retained copy of a
message of a requested kind, which is what BOLT 2's reestablish/retransmit
rules ask for.

Message loss and reordering are modelled by `LossyLink`, a relation between
an in-flight list, the remaining in-flight list, and the list actually
delivered.  Its `deliver` constructor may select *any* element, so reordering
needs no separate rule; `drop` removes any element; `duplicate` both keeps
and delivers an element.  There is no hidden reliable queue: every delivery
step is an explicit disjunct of the relation.

## BOLT sections

* BOLT 1 §"Connection Handling and Multiplexing"
  (`refs/bolts/01-messaging.md:39-42`): messages are multiplexed over one
  authenticated connection.
* BOLT 1 §"Lightning Message Format"
  (`01-messaging.md:43-92`): type-prefixed messages; no transport-level
  ordering guarantee is assumed by this model.
* BOLT 2 §"Channel Establishment v1"
  (`refs/bolts/02-peer-protocol.md:629-680`): the handshake sequence.
* BOLT 2 §"Message Retransmission"
  (`02-peer-protocol.md:3357-3635`): reconnection, explicit acknowledgements,
  and retransmission of `commitment_signed`, `revoke_and_ack`, `shutdown`
  and `channel_ready`.
* BOLT 1 §"The `ping` and `pong` Messages"
  (`01-messaging.md:422-505`): keep-alive traffic is connection-level and is
  not tied to a channel.

## rust-lightning anchors (commit fe49009)

* `lightning/src/ln/peer_handler.rs:2431` answers a `ping` with a `pong`
  only when `ponglen < 65532`; `:4325` is the "not init" rejection test.
* `lightning/src/ln/channel.rs:13135` builds `channel_reestablish`;
  `:10827` handles an inbound one; `:11119` is the `next_commitment_number`
  special case.
* `lightning/src/ln/channelmanager.rs:13994` dispatches
  `channel_reestablish`; `:14110-14120` sends a defensive response for an
  unknown channel.
* `lightning/src/ln/wire.rs:184` `type_id` and `:452-480` the `Type` trait
  are the reference's typed-message dispatch.

## What is NOT modelled

* **Transport authentication is not claimed.**  `TransportState.up` means
  only that the local protocol layer is willing to exchange messages.  The
  peer's `identity` is a label; binding it to a Noise static key is the
  Noise interface (`docs/ASSUMPTIONS.md` §3), not a theorem here.
* There is no TCP, no Noise handshake, no encryption, no length-prefix
  parser, and no rate limiting.
* `send` does not re-check `wellFormed`; that is the framing layer's job
  (`LnLean.Protocol.Messages.wellFormed`).  It checks transport state and,
  for channel messages, that the channel exists.
* There is no timer, retry counter, or automatic retransmission.  `resend`
  is an explicit operation; BOLT 2's retransmission policy is not scheduled.
* Multiple peers are not modelled; one `PeerState` is one remote peer.
* Ordering within a channel is a protocol responsibility; `LossyLink` does
  not add ordering.  `receive` rejecting an out-of-order handshake message
  is the model's only ordering enforcement.
-/

namespace LnLean.Protocol

set_option autoImplicit false

open LnLean

/-- Whether the local protocol layer may exchange messages.  `up` is *not*
an authentication claim. -/
inductive TransportState where
  | down
  | up
deriving Repr, DecidableEq, BEq, Inhabited

/-- A channel as seen by the peer: its identifier, its reestablish counters,
and the last retained outbound message of each retransmittable kind.  Keeping
explicit named fields (instead of an unbounded queue) makes retransmission
policy reviewable. -/
structure ChannelRecord where
  channelId : ChannelId
  reestablish : ReestablishFields
  lastFundingSigned : Option Msg := none
  lastChannelReady : Option Msg := none
  lastCommitmentSigned : Option Msg := none
  lastRevokeAndAck : Option Msg := none
  lastShutdown : Option Msg := none
deriving Repr

namespace ChannelRecord

/-- Retained outbound message of a given kind, if the protocol requires that
kind to be retransmitted after reconnection. -/
def lastSent (c : ChannelRecord) : MsgKind → Option Msg
  | .fundingSigned => c.lastFundingSigned
  | .channelReady => c.lastChannelReady
  | .commitmentSigned => c.lastCommitmentSigned
  | .revokeAndAck => c.lastRevokeAndAck
  | .shutdown => c.lastShutdown
  | _ => none

/-- Remember an outbound message if it belongs to a retransmittable kind. -/
def recordSent (c : ChannelRecord) (m : Msg) : ChannelRecord :=
  match m.kind with
  | .fundingSigned => { c with lastFundingSigned := some m }
  | .channelReady => { c with lastChannelReady := some m }
  | .commitmentSigned => { c with lastCommitmentSigned := some m }
  | .revokeAndAck => { c with lastRevokeAndAck := some m }
  | .shutdown => { c with lastShutdown := some m }
  | _ => c

/-- Advance the counters that `channel_reestablish` reports when a message is
received.  A `commitment_signed` advances the commitment counter; a
`revoke_and_ack` advances the revocation counter only when it is behind, so
the consistency condition cannot be violated. -/
def advanceReceived (c : ChannelRecord) (m : Msg) : ChannelRecord :=
  match m.kind with
  | .commitmentSigned => { c with reestablish := c.reestablish.afterCommitment }
  | .revokeAndAck =>
      if c.reestablish.nextRevocationNumber < c.reestablish.nextCommitmentNumber then
        { c with reestablish := c.reestablish.afterRevocation }
      else c
  | _ => c

end ChannelRecord

/-- One remote peer's state.  `identity` is a label supplied by the transport
layer; see the module docstring's authentication caveat. -/
structure PeerState where
  identity : PubKey
  transport : TransportState
  handshake : HandshakeState
  channels : List ChannelRecord
deriving Repr

namespace PeerState

/-- A disconnected peer with no channels and a zero identity placeholder. -/
def initial : PeerState where
  identity := ⟨ByteArray.mk ((List.replicate 33 (0 : UInt8)).toArray)⟩
  transport := .down
  handshake := HandshakeState.initial
  channels := []

end PeerState

/-- The handshake event corresponding to sending a message, if it is a
handshake message. -/
def sendEvent? : Msg → Option HandshakeEvent
  | .init _ => some .sendInit
  | .acceptChannel _ => some .sendAcceptChannel
  | .fundingCreated _ => some .sendFundingCreated
  | .fundingSigned _ => some .sendFundingSigned
  | .channelReady _ => some .sendChannelReady
  | _ => none

/-- The handshake event corresponding to receiving a message, if it is a
handshake message. -/
def receiveEvent? : Msg → Option HandshakeEvent
  | .init _ => some .recvInit
  | .acceptChannel _ => some .recvAcceptChannel
  | .fundingCreated _ => some .recvFundingCreated
  | .fundingSigned _ => some .recvFundingSigned
  | .channelReady _ => some .recvChannelReady
  | _ => none

/-- Find a channel by identifier. -/
def findChannel (s : PeerState) (channelId : ChannelId) : Option ChannelRecord :=
  s.channels.find? (fun c => c.channelId == channelId)

/-- Apply a function to one channel, leaving the others unchanged. -/
def updateChannel (s : PeerState) (channelId : ChannelId)
    (f : ChannelRecord → ChannelRecord) : PeerState :=
  { s with
    channels := s.channels.map
      (fun c => if c.channelId == channelId then f c else c) }

/-- Hand a message to the transport.  Returns the updated peer state and the
message actually emitted.  A handshake message is allowed only when
`handshakeStep` permits it; any other channel message requires that the
channel exists.  Connection-level non-handshake messages (`ping`, `pong`)
need neither. -/
def send (s : PeerState) (m : Msg) : Option (PeerState × Msg) :=
  match s.transport with
  | .down => none
  | .up =>
      match sendEvent? m with
      | some e =>
          match handshakeStep s.handshake e with
          | some hs => some ({ s with handshake := hs }, m)
          | none => none
      | none =>
          match channelId? m with
          | none => some (s, m)
          | some cid =>
              match findChannel s cid with
              | some _c => some (updateChannel s cid (fun ch => ch.recordSent m), m)
              | none => none

/-- Consume an inbound message.  Handshake messages move `handshake`;
channel messages may advance the channel's reestablish counters. -/
def receive (s : PeerState) (m : Msg) : Option PeerState :=
  match s.transport with
  | .down => none
  | .up =>
      match receiveEvent? m with
      | some e =>
          match handshakeStep s.handshake e with
          | some hs => some { s with handshake := hs }
          | none => none
      | none =>
          match channelId? m with
          | none => some s
          | some cid =>
              match findChannel s cid with
              | some c => some (updateChannel s cid (fun _ => c.advanceReceived m))
              | none => none

/-- The retained copy of the last message of a given kind, for explicit
retransmission. -/
def resend (s : PeerState) (channelId : ChannelId) (kind : MsgKind) : Option Msg :=
  match findChannel s channelId with
  | some c => c.lastSent kind
  | none => none

/-- Lossy, reordering, duplicating link relation.  `LossyLink inFlight rest
delivered` says that from the in-flight list `inFlight` the link may end with
`rest` still in flight and `delivered` handed to the receiver.  The
`deliver` rule chooses an arbitrary element, which subsumes reordering. -/
inductive LossyLink : List Msg → List Msg → List Msg → Prop where
  | deliver (before after : List Msg) (m : Msg) :
      LossyLink (before ++ m :: after) (before ++ after) [m]
  | drop (before after : List Msg) (m : Msg) :
      LossyLink (before ++ m :: after) (before ++ after) []
  | duplicate (before after : List Msg) (m : Msg) :
      LossyLink (before ++ m :: after) (m :: (before ++ after)) [m]

/-- The link may drop any in-flight message. -/
theorem LossyLink.drop_any (before after : List Msg) (m : Msg) :
    ∃ rest, LossyLink (before ++ m :: after) rest [] :=
  ⟨before ++ after, LossyLink.drop before after m⟩

/-- The link may deliver any in-flight message, regardless of position. -/
theorem LossyLink.deliver_any (before after : List Msg) (m : Msg) :
    ∃ rest, LossyLink (before ++ m :: after) rest [m] :=
  ⟨before ++ after, LossyLink.deliver before after m⟩

/-- The link may duplicate any in-flight message. -/
theorem LossyLink.duplicate_any (before after : List Msg) (m : Msg) :
    ∃ rest, LossyLink (before ++ m :: after) rest [m] :=
  ⟨m :: (before ++ after), LossyLink.duplicate before after m⟩

/-! ## Basic send/receive laws -/

theorem send_down (s : PeerState) (m : Msg) (h : s.transport = .down) :
    send s m = none := by
  simp [send, h]

theorem receive_down (s : PeerState) (m : Msg) (h : s.transport = .down) :
    receive s m = none := by
  simp [receive, h]

/-- A channel-directed non-handshake message cannot be sent when the channel
is unknown. -/
theorem send_channel_requires_channel (s : PeerState) (m : Msg)
    (cid : ChannelId) (he : sendEvent? m = none) (hc : channelId? m = some cid)
    (hf : findChannel s cid = none) : send s m = none := by
  cases ht : s.transport <;> simp [send, ht, he, hc, hf]

/-- A channel-directed non-handshake message cannot be received when the
channel is unknown. -/
theorem receive_channel_requires_channel (s : PeerState) (m : Msg)
    (cid : ChannelId) (he : receiveEvent? m = none) (hc : channelId? m = some cid)
    (hf : findChannel s cid = none) : receive s m = none := by
  cases ht : s.transport <;> simp [receive, ht, he, hc, hf]

theorem resend_of_channel (s : PeerState) (cid : ChannelId) (kind : MsgKind)
    (c : ChannelRecord) (h : findChannel s cid = some c) :
    resend s cid kind = c.lastSent kind := by
  simp [resend, h]

theorem resend_none_of_unknown (s : PeerState) (cid : ChannelId) (kind : MsgKind)
    (h : findChannel s cid = none) : resend s cid kind = none := by
  simp [resend, h]

end LnLean.Protocol
