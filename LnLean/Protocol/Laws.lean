import LnLean.Protocol.Peer

/-!
# LnLean.Protocol.Laws

## English claim

This module collects the proved structural laws of the BOLT 1/2 peer model:

1. `msgType` is injective on message constructors: two messages with the
   same wire type have the same constructor tag.
2. Every wire type is a nonzero 16-bit value; decoding a type returns the
   constructor that produced it, so each message has exactly one wire type.
3. Every message payload has positive length; a `wellFormed` message has
   payload at most 65535 bytes, BOLT 1's framing bound.  A `pong` reply to a
   `ping` whose `num_pong_bytes` is below the BOLT 1 cutoff also fits.
4. In every reachable handshake state, `channel_ready` (sent or received)
   implies `funding_signed` (sent or received), and no non-`init` message
   can have been sent before `init`.
5. `channel_reestablish`'s two counters never decrease along a
   `ReestablishStep`, and consistency (`next_revocation_number ≤
   next_commitment_number`) is preserved.
6. `send` and `receive` require the transport to be up; channel-directed
   messages require a known channel; the lossy link may drop, deliver, or
   duplicate any in-flight message.

## BOLT sections

* BOLT 1 §"Lightning Message Format"
  (`refs/bolts/01-messaging.md:43-92`): the 16-bit type space and the
  65535-byte payload bound.
* BOLT 1 §"The `init` Message" (`01-messaging.md:268-330`): `init` first.
* BOLT 1 §"The `ping` and `pong` Messages" (`01-messaging.md:422-505`):
  `num_pong_bytes < 65532` and the reply length.
* BOLT 2 §"Channel Establishment v1"
  (`refs/bolts/02-peer-protocol.md:629-680`) and §"The `channel_ready`
  Message" (`02-peer-protocol.md:1046-1136`): the handshake order.
* BOLT 2 §"Message Retransmission"
  (`02-peer-protocol.md:3357-3405`, `:3451-3455`): the meaning of
  `next_commitment_number` and `next_revocation_number`.

## rust-lightning anchors (commit fe49009)

* `lightning/src/ln/wire.rs:452-480` (`Type` trait and `type_id`),
  `:494-643` (the type constants used by `wireType`).
* `lightning/src/ln/msgs.rs:111-960` (message struct fields).
* `lightning/src/ln/channel.rs:10827` and `:13135` for the receive/send
  sides of `channel_reestablish`.
* `lightning/src/ln/channelmanager.rs:13994` for dispatch.
* `lightning/src/ln/peer_handler.rs:2431` for the ping/pong cutoff.

## What is NOT modelled

* No authentication theorem: `TransportState.up` is a local willingness
  flag, not evidence that the peer holds a Noise key.
* No liveness theorem: the lossy link may drop every message forever.
* No cryptographic soundness: signatures are only length-checked.
* No claim that the numeric bounds are tight for every implementation; the
  constants come from the BOLT sections cited above.
-/

namespace LnLean.Protocol

set_option autoImplicit false

open LnLean

/-! ## Wire-type laws -/

/-- Constructor tags have distinct wire types. -/
theorem wireType_injective : Function.Injective wireType := by
  intro a b h
  cases a <;> cases b <;> simp [wireType] at h ⊢ <;> omega

/-- `msgType` is injective on constructors, even though it forgets payloads. -/
theorem msgType_kind_injective {m₁ m₂ : Msg} (h : msgType m₁ = msgType m₂) :
    m₁.kind = m₂.kind :=
  wireType_injective h

/-- Every modelled message type is a 16-bit value. -/
theorem msgType_lt_65536 (m : Msg) : msgType m < 65536 := by
  cases m <;> simp [msgType, wireType, Msg.kind] <;> omega

/-- No modelled message uses type zero. -/
theorem msgType_ne_zero (m : Msg) : msgType m ≠ 0 := by
  cases m <;> simp [msgType, wireType, Msg.kind]

/-- Every message has exactly one wire type. -/
theorem unique_wire_type (m : Msg) :
    ∃ t : Nat, msgType m = t ∧ ∀ u : Nat, msgType m = u → u = t :=
  ⟨msgType m, rfl, fun _u hu => hu.symm⟩

/-- Decoding the type of a message returns its constructor.  This is the
encode/decode round trip that makes the wire type unambiguous. -/
theorem kindOfType?_msgType (m : Msg) :
    kindOfType? (msgType m) = some m.kind := by
  cases m <;> rfl

/-! ## Payload-length laws -/

/-- Every message has a non-empty payload. -/
theorem msgLength_pos (m : Msg) : 0 < msgLength m := by
  cases m <;> simp [msgLength, sigLen, sigListLen] <;> omega

/-- A well-formed message fits BOLT 1's two-byte framing bound. -/
theorem msgLength_le_65535 {m : Msg} (h : wellFormed m) :
    msgLength m ≤ 65535 :=
  h.1

/-- A `pong` that answers a well-formed `ping` with the requested number of
ignored bytes also fits the framing bound. -/
theorem pong_reply_bounded (p : Ping) (ignored : ByteArray)
    (hnum : p.numPongBytes < 65532) (hlen : ignored.size = p.numPongBytes) :
    msgLength (.pong ({ ignored := ignored } : Pong)) ≤ 65535 := by
  simp [msgLength, hlen]
  omega

/-- **Corrected claim.**  A `ping` fits the framing bound only when its
`ignored` field is also bounded.  The naive form without `hign` is false: a
`Ping` with `numPongBytes = 0` and `ignored.size = 70000` satisfies the BOLT 1
reply cutoff but has payload `70004 > 65535`.  The BOLT field itself is a
`u16`, which is exactly the missing bound. -/
theorem ping_bounded (p : Ping) (hnum : p.numPongBytes < 65532)
    (hign : p.ignored.size ≤ 65531) :
    msgLength (.ping p) ≤ 65535 := by
  have hnum' : p.numPongBytes < 65532 := hnum
  simp [msgLength]
  omega

/-! ## Handshake-order laws -/

/-- In a reachable handshake state, `channel_ready` cannot precede
`funding_signed`: if either `channel_ready` flag is set, then one of the
`funding_signed` flags is set. -/
theorem channel_ready_not_before_funding_signed {s : HandshakeState}
    (h : Reachable s)
    (hr : s.channelReadySent = true ∨ s.channelReadyReceived = true) :
    s.fundingSignedSent = true ∨ s.fundingSignedReceived = true :=
  (reachable_inv h).1 hr

/-- In a reachable handshake state, no non-`init` message is sent before
`init`. -/
theorem init_sent_before_other {s : HandshakeState} (h : Reachable s)
    (hs : s.sentNonInit = true) : s.initSent = true :=
  (reachable_inv h).2 hs

/-- Reaching BOLT 2 normal operation means both `channel_ready` messages
have been exchanged. -/
theorem ready_implies_both_channel_ready {s : HandshakeState}
    (h : s.ready = true) :
    s.channelReadySent = true ∧ s.channelReadyReceived = true :=
  (HandshakeState.ready_iff s).1 h

/-- The handshake transition function is deterministic. -/
theorem handshakeStep_deterministic {s s' s'' : HandshakeState}
    {e : HandshakeEvent} (h₁ : handshakeStep s e = some s')
    (h₂ : handshakeStep s e = some s'') : s' = s'' := by
  rw [h₁] at h₂
  exact (Option.some.injEq s' s'').mp h₂

/-! ## `channel_reestablish` laws -/

/-- The commitment counter never decreases along a reestablish step. -/
theorem reestablish_commitment_monotone {r r' : ReestablishFields}
    (h : ReestablishStep r r') :
    r.nextCommitmentNumber ≤ r'.nextCommitmentNumber := by
  cases h with
  | commitment _ => exact ReestablishFields.nextCommitment_le_afterCommitment r
  | revocation _ => simp [ReestablishFields.afterRevocation]

/-- The revocation counter never decreases along a reestablish step. -/
theorem reestablish_revocation_monotone {r r' : ReestablishFields}
    (h : ReestablishStep r r') :
    r.nextRevocationNumber ≤ r'.nextRevocationNumber := by
  cases h with
  | commitment _ => simp [ReestablishFields.afterCommitment]
  | revocation _ => exact ReestablishFields.nextRevocation_le_afterRevocation r

/-- Consistency is preserved: a `revoke_and_ack` never gets ahead of the
commitment it acknowledges. -/
theorem reestablish_consistent_step {r r' : ReestablishFields}
    (h : r.consistent) (hs : ReestablishStep r r') : r'.consistent := by
  cases hs with
  | commitment _ => exact ReestablishFields.afterCommitment_consistent h
  | revocation hlt => exact ReestablishFields.afterRevocation_consistent h hlt

/-- The fresh channel state satisfies the consistency condition. -/
theorem reestablish_initial_consistent :
    ReestablishFields.initial.consistent := by
  simp [ReestablishFields.initial, ReestablishFields.consistent]

/-- Receiving a `commitment_signed` strictly advances the commitment
counter. -/
theorem reestablish_commitment_strict (r : ReestablishFields) :
    r.nextCommitmentNumber < r.afterCommitment.nextCommitmentNumber :=
  ReestablishFields.nextCommitment_lt_afterCommitment r

/-- Packing the fields into a message preserves the wire type 136. -/
theorem reestablish_toMsg_type (cid : ChannelId) (r : ReestablishFields) :
    msgType (ReestablishFields.toMsg cid r) = 136 := rfl

/-- Packing the fields into a message preserves the channel identifier. -/
theorem reestablish_toMsg_channelId (cid : ChannelId) (r : ReestablishFields) :
    channelId? (ReestablishFields.toMsg cid r) = some cid := rfl

/-! ## Peer and link laws -/

/-- A successful send requires the transport to be up. -/
theorem send_some_transport_up {s s' : PeerState} {m out : Msg}
    (h : send s m = some (s', out)) : s.transport = .up := by
  cases ht : s.transport with
  | down => simp [send, ht] at h
  | up => rfl

/-- A successful receive requires the transport to be up. -/
theorem receive_some_transport_up {s s' : PeerState} {m : Msg}
    (h : receive s m = some s') : s.transport = .up := by
  cases ht : s.transport with
  | down => simp [receive, ht] at h
  | up => rfl

/-- The lossy link can drop an arbitrary in-flight message. -/
theorem link_can_drop (before after : List Msg) (m : Msg) :
    ∃ rest, LossyLink (before ++ m :: after) rest [] :=
  LossyLink.drop_any before after m

/-- The lossy link can deliver an arbitrary in-flight message, so it can
reorder messages as well as deliver them in order. -/
theorem link_can_deliver (before after : List Msg) (m : Msg) :
    ∃ rest, LossyLink (before ++ m :: after) rest [m] :=
  LossyLink.deliver_any before after m

/-- The lossy link can duplicate an arbitrary in-flight message. -/
theorem link_can_duplicate (before after : List Msg) (m : Msg) :
    ∃ rest, LossyLink (before ++ m :: after) rest [m] :=
  LossyLink.duplicate_any before after m

/-- A retained retransmission copy is returned unchanged by `resend`. -/
theorem resend_returns_retained {s : PeerState} {cid : ChannelId} {kind : MsgKind}
    {c : ChannelRecord} (h : findChannel s cid = some c) :
    resend s cid kind = c.lastSent kind :=
  resend_of_channel s cid kind c h

end LnLean.Protocol
