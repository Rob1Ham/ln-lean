import LnLean.Protocol.Laws
import LnLean.Proofs.Bitcoin.FundingLinkTargets

/-!
# `open_channel` wire coverage and funding-phase projection (`L1-03`)

**English claim.**  BOLT 2's `open_channel` (type 32) is the first channel
establishment message and carries the opener's complete funding offer.  Wave 7
added `Handshake.OpenChannel`, a funding-relevant projection, and the separate
`FundingPhase` machine, but `Messages.lean` still had no `open_channel`
constructor.  This module connects the two layers:

* `Messages.OpenChannelWire` is the full modelled BOLT 2 wire record
  (`chain_hash` omitted, standard 34-byte shutdown script);
* `Msg.openChannel`/`MsgKind.openChannel` give it type 32, a 321-byte model
  payload (287 fixed fields plus the standard 34-byte shutdown script), a
  channel identifier, and six public keys;
* `OpenChannelWire.toHandshakeOpenChannel` projects the wire record onto the
  existing `Handshake.OpenChannel` **without moving or duplicating it**;
* `OpenChannelWire.toFundingNegotiation`/`toFundingParams` are the funding
  construction on the wire record, and are definitionally the wave-7
  construction on the projection;
* `openerPhaseAfter`/`acceptorPhaseAfter` are reachable `FundingPhase` states
  built from the wire record, and the end-to-end theorem equates the two
  negotiations and yields the constructed P2WSH output.

## What is *not* claimed

`open_channel` carries no sender identity and no signature.  Projecting a wire
record onto `Handshake.OpenChannel` does not authenticate the sender; transport
attribution remains the explicit hypothesis in
`LnLean.Proofs.Bitcoin.FundingAuthTargets`.  The 321-byte constant is the
model length: 287 fixed fields plus the standard 34-byte shutdown script.  It
omits `chain_hash` and the TLV header, matching `Messages.msgLength`; the BOLT
2 wire variants are 319/323/355 as documented there.  This module proves the
model constant, not a byte-serialization theorem.
-/

namespace LnLean.Protocol

set_option autoImplicit false

open LnLean
open LnLean.Bitcoin
open LnLean.Proofs.Bitcoin.FundingScriptTargets

namespace OpenChannelWire

/-! ## Projection onto the wave-7 funding record -/

/-- The funding-relevant projection of the wire record.  This is the *only*
bridge to `Handshake.OpenChannel`: the wire record is not a duplicate of the
handshake record, and the handshake record is not moved into `Messages.lean`. -/
def toHandshakeOpenChannel (w : OpenChannelWire) : OpenChannel where
  temporaryChannelId := w.temporaryChannelId
  fundingSatoshis := w.fundingSatoshis
  pushMsat := w.pushMsat
  fundingPubKey := w.fundingPubKey

@[simp] theorem toHandshakeOpenChannel_temporaryChannelId (w : OpenChannelWire) :
    w.toHandshakeOpenChannel.temporaryChannelId = w.temporaryChannelId := rfl

@[simp] theorem toHandshakeOpenChannel_fundingSatoshis (w : OpenChannelWire) :
    w.toHandshakeOpenChannel.fundingSatoshis = w.fundingSatoshis := rfl

@[simp] theorem toHandshakeOpenChannel_pushMsat (w : OpenChannelWire) :
    w.toHandshakeOpenChannel.pushMsat = w.pushMsat := rfl

@[simp] theorem toHandshakeOpenChannel_fundingPubKey (w : OpenChannelWire) :
    w.toHandshakeOpenChannel.fundingPubKey = w.fundingPubKey := rfl

/-- The projection is exactly the four fields that enter the funding
construction; the other wire fields are deliberately forgotten. -/
theorem toHandshakeOpenChannel_eq_iff {w₁ w₂ : OpenChannelWire} :
    w₁.toHandshakeOpenChannel = w₂.toHandshakeOpenChannel ↔
      w₁.temporaryChannelId = w₂.temporaryChannelId ∧
      w₁.fundingSatoshis = w₂.fundingSatoshis ∧
      w₁.pushMsat = w₂.pushMsat ∧
      w₁.fundingPubKey = w₂.fundingPubKey := by
  constructor
  · intro h
    injection h with htid hsat hpush hkey
    exact ⟨htid, hsat, hpush, hkey⟩
  · rintro ⟨htid, hsat, hpush, hkey⟩
    cases w₁
    cases w₂
    simp_all [toHandshakeOpenChannel]

/-- The joint funding negotiation of a wire `open_channel` and an
`accept_channel`, routed through the wave-7 projection. -/
def toFundingNegotiation (w : OpenChannelWire) (a : AcceptChannel) :
    FundingNegotiation :=
  w.toHandshakeOpenChannel.toFundingNegotiation a

/-- The constructed funding parameters of a wire `open_channel` and an
`accept_channel`. -/
def toFundingParams (H : ByteArray → ByteArray) (w : OpenChannelWire)
    (a : AcceptChannel) : FundingParams :=
  w.toFundingNegotiation a |>.toFundingParams H

@[simp] theorem toFundingNegotiation_eq (w : OpenChannelWire) (a : AcceptChannel) :
    w.toFundingNegotiation a =
      w.toHandshakeOpenChannel.toFundingNegotiation a := rfl

@[simp] theorem toFundingParams_eq (H : ByteArray → ByteArray)
    (w : OpenChannelWire) (a : AcceptChannel) :
    w.toFundingParams H a =
      w.toHandshakeOpenChannel.toFundingParams H a := rfl

@[simp] theorem toFundingNegotiation_localFundingKey (w : OpenChannelWire)
    (a : AcceptChannel) :
    (w.toFundingNegotiation a).localFundingKey = w.fundingPubKey := rfl

@[simp] theorem toFundingNegotiation_remoteFundingKey (w : OpenChannelWire)
    (a : AcceptChannel) :
    (w.toFundingNegotiation a).remoteFundingKey = a.fundingPubKey := rfl

@[simp] theorem toFundingNegotiation_fundingSatoshis (w : OpenChannelWire)
    (a : AcceptChannel) :
    (w.toFundingNegotiation a).fundingSatoshis = w.fundingSatoshis := rfl

@[simp] theorem toFundingNegotiation_pushMsat (w : OpenChannelWire)
    (a : AcceptChannel) :
    (w.toFundingNegotiation a).pushMsat = w.pushMsat := rfl

@[simp] theorem toFundingNegotiation_temporaryChannelId (w : OpenChannelWire)
    (a : AcceptChannel) :
    (w.toFundingNegotiation a).temporaryChannelId =
      ⟨w.temporaryChannelId⟩ := rfl

/-- The wire projection does not weaken the wave-7 hash link. -/
theorem toFundingParams_hash_linked (H : ByteArray → ByteArray)
    (w : OpenChannelWire) (a : AcceptChannel) :
    FundingScriptHashLinked H (w.toFundingParams H a) :=
  OpenChannel.toFundingParams_witnessScriptHash H w.toHandshakeOpenChannel a

/-- The funding `scriptPubKey` is the P2WSH wrapper over the computed program. -/
theorem toFundingParams_fundingScriptPubKey (H : ByteArray → ByteArray)
    (w : OpenChannelWire) (a : AcceptChannel) :
    (w.toFundingParams H a).fundingScriptPubKey =
      p2wsh (H (w.toFundingParams H a).witnessScript.bytes) :=
  OpenChannel.toFundingParams_fundingScriptPubKey H w.toHandshakeOpenChannel a

/-- **Ordered end-to-end funding output.**  The output of the complete wire
`open_channel`/`accept_channel` exchange is the P2WSH of the exact ordered
BOLT 3 2-of-2 script, with no hash hypothesis. -/
theorem toFundingParams_fundingScriptPubKey_eq_p2wsh_ordered
    (H : ByteArray → ByteArray) (w : OpenChannelWire) (a : AcceptChannel) :
    (w.toFundingParams H a).fundingScriptPubKey =
      p2wsh (H (TwoOfTwoScriptBytes (w.toFundingNegotiation a).firstFundingKey
        (w.toFundingNegotiation a).secondFundingKey)) :=
  LnLean.Proofs.Bitcoin.FundingLinkTargets.fundingScriptPubKey_eq_p2wsh_ordered H
    (w.toFundingNegotiation a)

/-! ## Phase events -/

/-- The `FundingPhase` event for sending this wire record. -/
def toSendEvent (w : OpenChannelWire) : FundingPhaseEvent :=
  .sendOpen w.toHandshakeOpenChannel

/-- The `FundingPhase` event for receiving this wire record. -/
def toReceiveEvent (w : OpenChannelWire) : FundingPhaseEvent :=
  .recvOpen w.toHandshakeOpenChannel

@[simp] theorem toSendEvent_eq (w : OpenChannelWire) :
    w.toSendEvent = .sendOpen w.toHandshakeOpenChannel := rfl

@[simp] theorem toReceiveEvent_eq (w : OpenChannelWire) :
    w.toReceiveEvent = .recvOpen w.toHandshakeOpenChannel := rfl

end OpenChannelWire

end LnLean.Protocol

namespace LnLean.Proofs.Protocol.OpenChannelWireTargets

set_option autoImplicit false

open LnLean
open LnLean.Protocol
open LnLean.Bitcoin
open LnLean.Proofs.Bitcoin.FundingScriptTargets

/-! ## Type, identity, length, and key laws -/

/-- `open_channel` is BOLT wire type 32. -/
@[simp] theorem msgType_openChannel (w : OpenChannelWire) :
    msgType (.openChannel w) = 32 := rfl

/-- The constructor tag of a wire `open_channel`. -/
@[simp] theorem kind_openChannel (w : OpenChannelWire) :
    Msg.kind (.openChannel w) = .openChannel := rfl

/-- The type-32 decoder returns the `open_channel` constructor. -/
@[simp] theorem kindOfType?_32 :
    kindOfType? 32 = some .openChannel := rfl

/-- Type 32 is the wire type of `MsgKind.openChannel`. -/
@[simp] theorem wireType_openChannel : wireType .openChannel = 32 := rfl

/-- The model payload length of `open_channel` (287 fixed fields plus the
standard 34-byte shutdown script; `chain_hash` and the TLV header omitted). -/
@[simp] theorem msgLength_openChannel (w : OpenChannelWire) :
    msgLength (.openChannel w) = 321 := rfl

/-- `open_channel` carries the opener's temporary channel identifier. -/
@[simp] theorem channelId?_openChannel (w : OpenChannelWire) :
    channelId? (.openChannel w) = some w.temporaryChannelId := rfl

/-- The six public keys of `open_channel`, in BOLT 2 order. -/
theorem pubKeys_openChannel_eq (w : OpenChannelWire) :
    pubKeys (.openChannel w) =
      [w.fundingPubKey, w.revocationBasepoint, w.paymentBasepoint,
       w.delayedPaymentBasepoint, w.htlcBasepoint, w.firstPerCommitmentPoint] := rfl

/-- The key list has exactly six entries. -/
theorem pubKeys_openChannel_length (w : OpenChannelWire) :
    (pubKeys (.openChannel w)).length = 6 := rfl

/-- The six key-membership laws. -/
theorem fundingPubKey_mem_pubKeys (w : OpenChannelWire) :
    w.fundingPubKey ∈ pubKeys (.openChannel w) := by simp [pubKeys]

theorem revocationBasepoint_mem_pubKeys (w : OpenChannelWire) :
    w.revocationBasepoint ∈ pubKeys (.openChannel w) := by simp [pubKeys]

theorem paymentBasepoint_mem_pubKeys (w : OpenChannelWire) :
    w.paymentBasepoint ∈ pubKeys (.openChannel w) := by simp [pubKeys]

theorem delayedPaymentBasepoint_mem_pubKeys (w : OpenChannelWire) :
    w.delayedPaymentBasepoint ∈ pubKeys (.openChannel w) := by simp [pubKeys]

theorem htlcBasepoint_mem_pubKeys (w : OpenChannelWire) :
    w.htlcBasepoint ∈ pubKeys (.openChannel w) := by simp [pubKeys]

theorem firstPerCommitmentPoint_mem_pubKeys (w : OpenChannelWire) :
    w.firstPerCommitmentPoint ∈ pubKeys (.openChannel w) := by simp [pubKeys]

/-- The type-32 message has exactly one wire type and it is nonzero/16-bit;
these are the general `Laws` facts specialized to the new constructor. -/
theorem openChannel_msgType_lt_65536 (w : OpenChannelWire) :
    msgType (.openChannel w) < 65536 := by simp

theorem openChannel_msgType_ne_zero (w : OpenChannelWire) :
    msgType (.openChannel w) ≠ 0 := by simp

/-- The `open_channel` constructor is injective in its payload. -/
theorem openChannel_injective {w₁ w₂ : OpenChannelWire}
    (h : Msg.openChannel w₁ = Msg.openChannel w₂) : w₁ = w₂ := by
  injection h

/-- Decoding the type of an `open_channel` returns its constructor. -/
theorem kindOfType?_msgType_openChannel (w : OpenChannelWire) :
    kindOfType? (msgType (.openChannel w)) = some .openChannel := by simp

/-! ## Well-formedness -/

/-- `open_channel` is well formed exactly when its temporary channel id and
its six public keys have the required wire widths.  The length bound, the
(empty) signature list, and the (trivial) semantic condition are discharged by
the model constants. -/
theorem wellFormed_openChannel_iff (w : OpenChannelWire) :
    wellFormed (.openChannel w) ↔
      w.temporaryChannelId.Valid ∧
        (∀ p ∈ pubKeys (.openChannel w), p.Valid) := by
  simp [wellFormed, idsValid, sigsValid, semanticOk, msgLength, channelId?,
    pubKeys, signatures]

/-- A well-formed `open_channel` has a valid temporary channel id. -/
theorem wellFormed_openChannel_channelId {w : OpenChannelWire}
    (h : wellFormed (.openChannel w)) : w.temporaryChannelId.Valid :=
  (wellFormed_openChannel_iff w).1 h |>.1

/-- Every public key of a well-formed `open_channel` has the 33-byte width. -/
theorem wellFormed_openChannel_pubKey {w : OpenChannelWire}
    (h : wellFormed (.openChannel w)) {p : PubKey}
    (hp : p ∈ pubKeys (.openChannel w)) : p.Valid :=
  (wellFormed_openChannel_iff w).1 h |>.2 p hp

/-- The constructor form of the well-formedness characterization. -/
theorem wellFormed_openChannel_of (w : OpenChannelWire)
    (hid : w.temporaryChannelId.Valid)
    (hkeys : ∀ p ∈ pubKeys (.openChannel w), p.Valid) :
    wellFormed (.openChannel w) :=
  (wellFormed_openChannel_iff w).2 ⟨hid, hkeys⟩

/-- The 321-byte payload is far below BOLT 1's 65535-byte framing bound. -/
theorem openChannel_msgLength_le_65535 (w : OpenChannelWire) :
    msgLength (.openChannel w) ≤ 65535 := by simp

/-- The channel identifier in `open_channel` is the projection's temporary
channel identifier. -/
theorem channelId?_openChannel_eq_projection (w : OpenChannelWire) :
    channelId? (.openChannel w) =
      some w.toHandshakeOpenChannel.temporaryChannelId := rfl

/-! ## Projection laws -/

/-- The projection preserves the wire temporary channel identifier. -/
theorem toHandshakeOpenChannel_channelId (w : OpenChannelWire) :
    w.toHandshakeOpenChannel.temporaryChannelId = w.temporaryChannelId := rfl

/-- The projection preserves the funding value. -/
theorem toHandshakeOpenChannel_fundingSatoshis (w : OpenChannelWire) :
    w.toHandshakeOpenChannel.fundingSatoshis = w.fundingSatoshis := rfl

/-- The projection preserves the push amount. -/
theorem toHandshakeOpenChannel_pushMsat (w : OpenChannelWire) :
    w.toHandshakeOpenChannel.pushMsat = w.pushMsat := rfl

/-- The projection preserves the opener's funding key. -/
theorem toHandshakeOpenChannel_fundingPubKey (w : OpenChannelWire) :
    w.toHandshakeOpenChannel.fundingPubKey = w.fundingPubKey := rfl

/-- The projection is not injective: the wire-only fields are forgotten.
This is the scope boundary of the bridge, mechanized as a pair of distinct
records with the same projection. -/
theorem toHandshakeOpenChannel_not_injective :
    ∃ w₁ w₂ : OpenChannelWire,
      w₁ ≠ w₂ ∧ w₁.toHandshakeOpenChannel = w₂.toHandshakeOpenChannel := by
  let base : OpenChannelWire :=
    { temporaryChannelId := ⟨ByteArray.empty⟩
      fundingSatoshis := 0
      pushMsat := ⟨0⟩
      dustLimitSatoshis := 0
      maxHtlcValueInFlightMsat := 0
      channelReserveSatoshis := 0
      htlcMinimumMsat := 0
      feeratePerKw := 0
      toSelfDelay := 0
      maxAcceptedHtlcs := 0
      fundingPubKey := ⟨ByteArray.empty⟩
      revocationBasepoint := ⟨ByteArray.empty⟩
      paymentBasepoint := ⟨ByteArray.empty⟩
      delayedPaymentBasepoint := ⟨ByteArray.empty⟩
      htlcBasepoint := ⟨ByteArray.empty⟩
      firstPerCommitmentPoint := ⟨ByteArray.empty⟩
      channelFlags := 0
      shutdownScriptpubkey := ByteArray.empty }
  refine ⟨base, { base with feeratePerKw := 1 }, ?_, rfl⟩
  intro h
  have hf : base.feeratePerKw = ({ base with feeratePerKw := 1 }).feeratePerKw := by
    rw [h]
  simp at hf

/-- The wire funding negotiation is exactly the wave-7 projection's
negotiation. -/
theorem toFundingNegotiation_eq_projection (w : OpenChannelWire)
    (a : AcceptChannel) :
    w.toFundingNegotiation a =
      w.toHandshakeOpenChannel.toFundingNegotiation a := rfl

/-- The constructed parameters are exactly the projection's parameters. -/
theorem toFundingParams_eq_projection (H : ByteArray → ByteArray)
    (w : OpenChannelWire) (a : AcceptChannel) :
    w.toFundingParams H a =
      w.toHandshakeOpenChannel.toFundingParams H a := rfl

/-! ## Reachable funding phases built from the wire record -/

/-- The opener's phase after sending the wire `open_channel` and receiving the
accepting reply. -/
def openerPhaseAfter (w : OpenChannelWire) (a : AcceptChannel) : FundingPhase where
  openSent := some w.toHandshakeOpenChannel
  openReceived := none
  acceptSent := none
  acceptReceived := some a

/-- The acceptor's phase after receiving the wire `open_channel` and sending
the accepting reply. -/
def acceptorPhaseAfter (w : OpenChannelWire) (a : AcceptChannel) : FundingPhase where
  openSent := none
  openReceived := some w.toHandshakeOpenChannel
  acceptSent := some a
  acceptReceived := none

/-- Sending the wire `open_channel` then receiving `accept_channel` is a legal
two-step funding phase. -/
theorem openerPhaseAfter_reachable (w : OpenChannelWire) (a : AcceptChannel) :
    FundingReachable (openerPhaseAfter w a) := by
  let s1 : FundingPhase :=
    { openSent := some w.toHandshakeOpenChannel, openReceived := none,
      acceptSent := none, acceptReceived := none }
  have h1 : fundingStep FundingPhase.initial
      (.sendOpen w.toHandshakeOpenChannel) = some s1 := by
    simp [fundingStep, FundingPhase.initial, FundingPhase.canSendOpen, s1]
  have h2 : fundingStep s1 (.recvAccept a) = some (openerPhaseAfter w a) := by
    simp [fundingStep, FundingPhase.canRecvAccept, s1, openerPhaseAfter]
  exact FundingReachable.step _ (FundingReachable.step _
    FundingReachable.initial h1) h2

/-- Receiving the wire `open_channel` then sending `accept_channel` is a legal
two-step funding phase. -/
theorem acceptorPhaseAfter_reachable (w : OpenChannelWire) (a : AcceptChannel) :
    FundingReachable (acceptorPhaseAfter w a) := by
  let s1 : FundingPhase :=
    { openSent := none, openReceived := some w.toHandshakeOpenChannel,
      acceptSent := none, acceptReceived := none }
  have h1 : fundingStep FundingPhase.initial
      (.recvOpen w.toHandshakeOpenChannel) = some s1 := by
    simp [fundingStep, FundingPhase.initial, FundingPhase.canRecvOpen, s1]
  have h2 : fundingStep s1 (.sendAccept a) = some (acceptorPhaseAfter w a) := by
    simp [fundingStep, FundingPhase.canSendAccept, s1, acceptorPhaseAfter]
  exact FundingReachable.step _ (FundingReachable.step _
    FundingReachable.initial h1) h2

/-- The opener's phase reports exactly the wire construction. -/
theorem openerPhaseAfter_negotiation (w : OpenChannelWire) (a : AcceptChannel) :
    (openerPhaseAfter w a).openerNegotiation? =
      some (w.toFundingNegotiation a) := by
  simp [openerPhaseAfter, FundingPhase.openerNegotiation?,
    OpenChannelWire.toFundingNegotiation]

/-- The acceptor's phase reports exactly the wire construction. -/
theorem acceptorPhaseAfter_negotiation (w : OpenChannelWire) (a : AcceptChannel) :
    (acceptorPhaseAfter w a).acceptorNegotiation? =
      some (w.toFundingNegotiation a) := by
  simp [acceptorPhaseAfter, FundingPhase.acceptorNegotiation?,
    OpenChannelWire.toFundingNegotiation]

/-- Both endpoints' phases agree on the funding negotiation built from the
same wire `open_channel` and `accept_channel`. -/
theorem opener_acceptor_negotiation_agree (w : OpenChannelWire)
    (a : AcceptChannel) :
    (openerPhaseAfter w a).openerNegotiation? =
      (acceptorPhaseAfter w a).acceptorNegotiation? := by
  rw [openerPhaseAfter_negotiation, acceptorPhaseAfter_negotiation]

/-- **End-to-end wire target (`L1-03`).**  Starting from a wire
`open_channel` and an `accept_channel`:

1. the opener's phase is reachable and reports the wire construction;
2. the acceptor's phase is reachable and reports the same construction;
3. the constructed parameters satisfy the hash link by construction;
4. the funding output is the P2WSH of the exact ordered BOLT 3 2-of-2 script.

No signature check, sender identity, or hash-injectivity hypothesis appears. -/
theorem openChannelWire_end_to_end (H : ByteArray → ByteArray)
    (w : OpenChannelWire) (a : AcceptChannel) :
    FundingReachable (openerPhaseAfter w a) ∧
    FundingReachable (acceptorPhaseAfter w a) ∧
    (openerPhaseAfter w a).openerNegotiation? = some (w.toFundingNegotiation a) ∧
    (acceptorPhaseAfter w a).acceptorNegotiation? = some (w.toFundingNegotiation a) ∧
    FundingScriptHashLinked H (w.toFundingParams H a) ∧
    (w.toFundingParams H a).fundingScriptPubKey =
      p2wsh (H (TwoOfTwoScriptBytes (w.toFundingNegotiation a).firstFundingKey
        (w.toFundingNegotiation a).secondFundingKey)) :=
  ⟨openerPhaseAfter_reachable w a,
   acceptorPhaseAfter_reachable w a,
   openerPhaseAfter_negotiation w a,
   acceptorPhaseAfter_negotiation w a,
   w.toFundingParams_hash_linked H a,
   w.toFundingParams_fundingScriptPubKey_eq_p2wsh_ordered H a⟩

/-- The same end-to-end target stated as an existential over a reachable
phase, for downstream consumers that only need one side. -/
theorem exists_reachable_phase_reports_wire_negotiation (w : OpenChannelWire)
    (a : AcceptChannel) :
    ∃ s : FundingPhase,
      FundingReachable s ∧
        s.openerNegotiation? = some (w.toFundingNegotiation a) :=
  ⟨openerPhaseAfter w a, openerPhaseAfter_reachable w a,
    openerPhaseAfter_negotiation w a⟩

/-! ## Handshake boundary and peer routing -/

/-- **`open_channel` coverage at the handshake boundary.**  When the existing
v1 handshake permits `funding_created`, the peer's `accept_channel` has already
arrived, and the remote funding key of the wire construction is exactly the
key that message carried.  This is the wave-7 theorem with the wire record
projected through `toHandshakeOpenChannel`. -/
theorem acceptKey_bound_before_fundingCreated_wire
    {s s' : HandshakeState}
    (h : handshakeStep s .sendFundingCreated = some s')
    (w : OpenChannelWire) (a : AcceptChannel) (H : ByteArray → ByteArray) :
    s.acceptReceived = true ∧
      ((w.toFundingNegotiation a).toFundingParams H).remoteFundingKey =
        a.fundingPubKey := by
  simpa [OpenChannelWire.toFundingNegotiation, OpenChannelWire.toFundingParams,
    OpenChannel.toFundingNegotiation] using
    (acceptKey_bound_before_fundingCreated (s := s) (s' := s') h
      w.toHandshakeOpenChannel a H)

/-- `open_channel` is deliberately *not* routed to `handshakeStep`: the ten
milestone v1 machine starts after the opening message. -/
theorem sendEvent?_openChannel (w : OpenChannelWire) :
    sendEvent? (.openChannel w) = none := rfl

/-- Receiving `open_channel` is likewise not a `handshakeStep` event. -/
theorem receiveEvent?_openChannel (w : OpenChannelWire) :
    receiveEvent? (.openChannel w) = none := rfl

/-- Because `open_channel` is a channel-directed non-handshake message, `send`
requires a channel record under its temporary channel id.  A fresh peer with
no such record cannot send it; adding an opening transition is a separate
coordinated change to `HandshakeState`/`handshakeStep`. -/
theorem send_openChannel_requires_channel (s : PeerState) (w : OpenChannelWire)
    (hf : findChannel s w.temporaryChannelId = none) :
    send s (.openChannel w) = none :=
  send_channel_requires_channel s (.openChannel w) w.temporaryChannelId
    (sendEvent?_openChannel w) rfl hf

/-- The receive-side counterpart of `send_openChannel_requires_channel`. -/
theorem receive_openChannel_requires_channel (s : PeerState)
    (w : OpenChannelWire) (hf : findChannel s w.temporaryChannelId = none) :
    receive s (.openChannel w) = none :=
  receive_channel_requires_channel s (.openChannel w) w.temporaryChannelId
    (receiveEvent?_openChannel w) rfl hf

end LnLean.Proofs.Protocol.OpenChannelWireTargets
