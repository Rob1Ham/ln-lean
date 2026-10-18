import LnLean.Protocol.Messages
import LnLean.Bitcoin.Funding

/-!
# LnLean.Protocol.Handshake

## English claim

`HandshakeState` records the ten protocol milestones of BOLT 2 channel
establishment v1 from one endpoint's point of view.  `handshakeStep` is the
deterministic transition function: it refuses every message that would
violate BOLT 1/2 ordering.  In particular `channel_ready` is enabled only
after `funding_signed` has been sent or received, and no message other than
`init` may be sent before `init` has been sent.  `Reachable` is the
reflexive-transitive closure of `handshakeStep`, and the laws in
`LnLean.Protocol.Laws` are proved over it.

The `channel_reestablish` counters are modelled by `ReestablishFields` with
BOLT 2's field names.  A `ReestablishStep` either advances the commitment
counter (receiving a `commitment_signed`) or the revocation counter
(receiving a `revoke_and_ack`), never decreases either counter, and
preserves `next_revocation_number ≤ next_commitment_number`.

## BOLT sections

* BOLT 1 §"The `init` Message" (`refs/bolts/01-messaging.md:268-330`):
  "MUST send `init` as the first Lightning message" and "MUST wait to
  receive `init` before sending any other messages".
* BOLT 2 §"Channel Establishment v1" (`refs/bolts/02-peer-protocol.md:629-680`):
  the message order `open_channel`, `accept_channel`, `funding_created`,
  `funding_signed`, `channel_ready`.
* BOLT 2 §"The `channel_ready` Message"
  (`02-peer-protocol.md:1046-1136`): channel enters normal operation only
  after both `channel_ready` messages.
* BOLT 2 §"Message Retransmission"
  (`02-peer-protocol.md:3357-3405`) for the four mandatory
  `channel_reestablish` fields; `:3451-3455` for the counter meanings.

## rust-lightning anchors (commit fe49009)

* `lightning/src/ln/msgs.rs:111` (`Init`), `:371` (`AcceptChannel`),
  `:403` (`FundingCreated`), `:420` (`FundingSigned`), `:431`
  (`ChannelReady`), `:939` (`ChannelReestablish`).
* `lightning/src/ln/wire.rs:494,518,522,526,530,643` for types
  16, 33, 34, 35, 36, 136.
* `lightning/src/ln/channel.rs:13135` `get_channel_reestablish` builds the
  four fields; `:13163` is the struct literal; `:10827` is the receive-side
  handler.
* `lightning/src/ln/channelmanager.rs:13994` `internal_channel_reestablish`
  dispatches a received `channel_reestablish` to the channel.

## What is NOT modelled

* `open_channel` itself is not a `Msg` constructor.  The environment event
  that would correspond to receiving it is absorbed into the guard on
  `sendAcceptChannel`; this is the scaffold's documented v1 simplification.
* There is no timeout, disconnect, or retry in `handshakeStep`; reconnection
  is represented by `ReestablishFields` and by `Peer.resend`.
* Multiple simultaneous channel negotiations on one transport are not
  represented; `HandshakeState` is the connection's single active
  establishment.
* Feature negotiation (BOLT 9) is not checked; `init` carries opaque feature
  bytes.
* Authentication is not claimed here.  The transport is Noise's
  responsibility (`docs/ASSUMPTIONS.md` §3).
-/

namespace LnLean.Protocol

set_option autoImplicit false

open LnLean

/-! ## Handshake milestones -/

/-- Protocol milestones of BOLT 2 channel establishment v1, from one
endpoint's point of view. -/
structure HandshakeState where
  initSent : Bool := false
  initReceived : Bool := false
  acceptSent : Bool := false
  acceptReceived : Bool := false
  fundingCreatedSent : Bool := false
  fundingCreatedReceived : Bool := false
  fundingSignedSent : Bool := false
  fundingSignedReceived : Bool := false
  channelReadySent : Bool := false
  channelReadyReceived : Bool := false
deriving Repr, DecidableEq, BEq

namespace HandshakeState

/-- The state before any message has been sent or received. -/
def initial : HandshakeState := {}

/-- `true` if a message that must follow `init` has been sent. -/
def sentNonInit (s : HandshakeState) : Bool :=
  s.acceptSent || s.fundingCreatedSent || s.fundingSignedSent || s.channelReadySent

/-- BOLT 2's normal-operation condition: both `channel_ready` messages have
been exchanged.  This is the "ready" bit of the mission's state list. -/
def ready (s : HandshakeState) : Bool :=
  s.channelReadySent && s.channelReadyReceived

/-- The two safety invariants of the handshake:
* `channel_ready` (sent or received) implies `funding_signed` (sent or
  received);
* every non-`init` send implies that `init` has been sent. -/
def Inv (s : HandshakeState) : Prop :=
  ((s.channelReadySent = true ∨ s.channelReadyReceived = true) →
    (s.fundingSignedSent = true ∨ s.fundingSignedReceived = true)) ∧
  (s.sentNonInit = true → s.initSent = true)

theorem initial_inv : initial.Inv := by
  simp [Inv, initial, sentNonInit]

theorem ready_iff (s : HandshakeState) :
    s.ready = true ↔ s.channelReadySent = true ∧ s.channelReadyReceived = true := by
  cases hs : s.channelReadySent <;> cases hr : s.channelReadyReceived <;>
    simp [ready, hs, hr]

/-! ### Positive transition guards

A guard is written as a conjunction of facts that must hold for the event to
be permitted.  Keeping the guards positive makes both the transition
function and its invariant proof direct. -/

/-- No `channel_ready` flag is set yet. -/
abbrev noReady (s : HandshakeState) : Prop :=
  s.channelReadySent = false ∧ s.channelReadyReceived = false

/-- Both `init` messages have been exchanged. -/
abbrev inited (s : HandshakeState) : Prop :=
  s.initSent = true ∧ s.initReceived = true

abbrev canSendInit (s : HandshakeState) : Prop :=
  s.initSent = false ∧ s.acceptSent = false ∧ s.fundingCreatedSent = false ∧
  s.fundingSignedSent = false ∧ s.channelReadySent = false ∧ s.channelReadyReceived = false

abbrev canRecvInit (s : HandshakeState) : Prop :=
  s.initReceived = false ∧ s.channelReadySent = false ∧ s.channelReadyReceived = false

abbrev canSendAccept (s : HandshakeState) : Prop :=
  inited s ∧ noReady s ∧ s.acceptSent = false ∧ s.acceptReceived = false ∧
  s.fundingCreatedSent = false ∧ s.fundingCreatedReceived = false ∧
  s.fundingSignedSent = false ∧ s.fundingSignedReceived = false

abbrev canRecvAccept (s : HandshakeState) : Prop :=
  inited s ∧ noReady s ∧ s.acceptSent = false ∧ s.acceptReceived = false ∧
  s.fundingCreatedSent = false ∧ s.fundingCreatedReceived = false ∧
  s.fundingSignedSent = false ∧ s.fundingSignedReceived = false

abbrev canSendFundingCreated (s : HandshakeState) : Prop :=
  inited s ∧ noReady s ∧ s.acceptSent = false ∧ s.acceptReceived = true ∧
  s.fundingCreatedSent = false ∧ s.fundingCreatedReceived = false ∧
  s.fundingSignedSent = false ∧ s.fundingSignedReceived = false

abbrev canRecvFundingCreated (s : HandshakeState) : Prop :=
  inited s ∧ noReady s ∧ s.acceptSent = true ∧ s.acceptReceived = false ∧
  s.fundingCreatedSent = false ∧ s.fundingCreatedReceived = false ∧
  s.fundingSignedSent = false ∧ s.fundingSignedReceived = false

abbrev canSendFundingSigned (s : HandshakeState) : Prop :=
  inited s ∧ noReady s ∧ s.fundingCreatedReceived = true ∧
  s.fundingSignedSent = false ∧ s.fundingSignedReceived = false

abbrev canRecvFundingSigned (s : HandshakeState) : Prop :=
  inited s ∧ noReady s ∧ s.fundingCreatedSent = true ∧
  s.fundingSignedSent = false ∧ s.fundingSignedReceived = false

abbrev canSendChannelReady (s : HandshakeState) : Prop :=
  inited s ∧ (s.fundingSignedSent = true ∨ s.fundingSignedReceived = true) ∧
  s.channelReadySent = false

abbrev canRecvChannelReady (s : HandshakeState) : Prop :=
  inited s ∧ (s.fundingSignedSent = true ∨ s.fundingSignedReceived = true) ∧
  s.channelReadyReceived = false

end HandshakeState

/-- The protocol events that drive the handshake.  A `send*` event is an
outbound message; a `recv*` event is an inbound message. -/
inductive HandshakeEvent where
  | sendInit
  | recvInit
  | sendAcceptChannel
  | recvAcceptChannel
  | sendFundingCreated
  | recvFundingCreated
  | sendFundingSigned
  | recvFundingSigned
  | sendChannelReady
  | recvChannelReady
deriving Repr, DecidableEq, BEq

/-- One deterministic handshake transition.  `none` means the event is not
allowed in the current state.  Each guard is the corresponding BOLT 1/2
ordering requirement listed in the module docstring. -/
def handshakeStep (s : HandshakeState) (e : HandshakeEvent) : Option HandshakeState :=
  match e with
  | .sendInit =>
      if s.canSendInit then some { s with initSent := true } else none
  | .recvInit =>
      if s.canRecvInit then some { s with initReceived := true } else none
  | .sendAcceptChannel =>
      if s.canSendAccept then some { s with acceptSent := true } else none
  | .recvAcceptChannel =>
      if s.canRecvAccept then some { s with acceptReceived := true } else none
  | .sendFundingCreated =>
      if s.canSendFundingCreated then some { s with fundingCreatedSent := true } else none
  | .recvFundingCreated =>
      if s.canRecvFundingCreated then some { s with fundingCreatedReceived := true } else none
  | .sendFundingSigned =>
      if s.canSendFundingSigned then some { s with fundingSignedSent := true } else none
  | .recvFundingSigned =>
      if s.canRecvFundingSigned then some { s with fundingSignedReceived := true } else none
  | .sendChannelReady =>
      if s.canSendChannelReady then some { s with channelReadySent := true } else none
  | .recvChannelReady =>
      if s.canRecvChannelReady then some { s with channelReadyReceived := true } else none

/-- The relation induced by `handshakeStep`. -/
def HandshakeStep (s s' : HandshakeState) : Prop :=
  ∃ e, handshakeStep s e = some s'

/-- Reachable handshake states: the initial state and every state obtained
by a permitted transition. -/
inductive Reachable : HandshakeState → Prop where
  | initial : Reachable HandshakeState.initial
  | step {s s' : HandshakeState} (e : HandshakeEvent) :
      Reachable s → handshakeStep s e = some s' → Reachable s'

/-- A permitted step preserves the handshake invariants. -/
theorem handshakeStep_inv {s s' : HandshakeState} {e : HandshakeEvent}
    (hinv : s.Inv) (h : handshakeStep s e = some s') : s'.Inv := by
  rcases hinv with ⟨hready, hinit⟩
  cases e with
  | sendInit =>
      by_cases hg : s.canSendInit
      · simp [handshakeStep, hg] at h
        rcases h with ⟨_, hs⟩
        subst hs
        simp_all [HandshakeState.Inv, HandshakeState.sentNonInit, HandshakeState.canSendInit]
      · simp [handshakeStep, hg] at h
  | recvInit =>
      by_cases hg : s.canRecvInit
      · simp [handshakeStep, hg] at h
        rcases h with ⟨_, hs⟩
        subst hs
        simp_all [HandshakeState.Inv, HandshakeState.sentNonInit, HandshakeState.canRecvInit]
      · simp [handshakeStep, hg] at h
  | sendAcceptChannel =>
      by_cases hg : s.canSendAccept
      · simp [handshakeStep, hg] at h
        rcases h with ⟨_, hs⟩
        subst hs
        simp_all [HandshakeState.Inv, HandshakeState.sentNonInit, HandshakeState.canSendAccept]
      · simp [handshakeStep, hg] at h
  | recvAcceptChannel =>
      by_cases hg : s.canRecvAccept
      · simp [handshakeStep, hg] at h
        rcases h with ⟨_, hs⟩
        subst hs
        simp_all [HandshakeState.Inv, HandshakeState.sentNonInit, HandshakeState.canRecvAccept]
      · simp [handshakeStep, hg] at h
  | sendFundingCreated =>
      by_cases hg : s.canSendFundingCreated
      · simp [handshakeStep, hg] at h
        rcases h with ⟨_, hs⟩
        subst hs
        simp_all [HandshakeState.Inv, HandshakeState.sentNonInit, HandshakeState.canSendFundingCreated]
      · simp [handshakeStep, hg] at h
  | recvFundingCreated =>
      by_cases hg : s.canRecvFundingCreated
      · simp [handshakeStep, hg] at h
        rcases h with ⟨_, hs⟩
        subst hs
        simp_all [HandshakeState.Inv, HandshakeState.sentNonInit, HandshakeState.canRecvFundingCreated]
      · simp [handshakeStep, hg] at h
  | sendFundingSigned =>
      by_cases hg : s.canSendFundingSigned
      · simp [handshakeStep, hg] at h
        rcases h with ⟨_, hs⟩
        subst hs
        simp_all [HandshakeState.Inv, HandshakeState.sentNonInit, HandshakeState.canSendFundingSigned]
      · simp [handshakeStep, hg] at h
  | recvFundingSigned =>
      by_cases hg : s.canRecvFundingSigned
      · simp [handshakeStep, hg] at h
        rcases h with ⟨_, hs⟩
        subst hs
        simp_all [HandshakeState.Inv, HandshakeState.sentNonInit, HandshakeState.canRecvFundingSigned]
      · simp [handshakeStep, hg] at h
  | sendChannelReady =>
      by_cases hg : s.canSendChannelReady
      · simp [handshakeStep, hg] at h
        rcases h with ⟨_, hs⟩
        subst hs
        simp_all [HandshakeState.Inv, HandshakeState.sentNonInit, HandshakeState.canSendChannelReady]
      · simp [handshakeStep, hg] at h
  | recvChannelReady =>
      by_cases hg : s.canRecvChannelReady
      · simp [handshakeStep, hg] at h
        rcases h with ⟨_, hs⟩
        subst hs
        simp_all [HandshakeState.Inv, HandshakeState.sentNonInit, HandshakeState.canRecvChannelReady]
      · simp [handshakeStep, hg] at h

/-- Every reachable handshake state satisfies `HandshakeState.Inv`. -/
theorem reachable_inv {s : HandshakeState} (h : Reachable s) : s.Inv := by
  induction h with
  | initial => exact HandshakeState.initial_inv
  | step e _ hstep ih => exact handshakeStep_inv ih hstep

/-! ## Channel reestablish counters -/

/-- BOLT 2 `channel_reestablish` counters, keeping BOLT's field names. -/
structure ReestablishFields where
  nextCommitmentNumber : Nat
  nextRevocationNumber : Nat
  yourLastPerCommitmentSecret : ByteArray
  myCurrentPerCommitmentPoint : PubKey
deriving Repr, BEq

namespace ReestablishFields

/-- A fresh channel: both counters are zero and the secret is all zeroes,
as BOLT 2 requires when `next_revocation_number` is zero. -/
def initial : ReestablishFields where
  nextCommitmentNumber := 0
  nextRevocationNumber := 0
  yourLastPerCommitmentSecret :=
    ByteArray.mk ((List.replicate 32 (0 : UInt8)).toArray)
  myCurrentPerCommitmentPoint :=
    ⟨ByteArray.mk ((List.replicate 33 (0 : UInt8)).toArray)⟩

/-- The counter change caused by receiving one `commitment_signed`: the
number of the next commitment we expect increases by one. -/
def afterCommitment (r : ReestablishFields) : ReestablishFields :=
  { r with nextCommitmentNumber := r.nextCommitmentNumber + 1 }

/-- The counter change caused by receiving one `revoke_and_ack`. -/
def afterRevocation (r : ReestablishFields) : ReestablishFields :=
  { r with nextRevocationNumber := r.nextRevocationNumber + 1 }

/-- BOLT 2's consistency condition: a `revoke_and_ack` cannot be expected
before the corresponding `commitment_signed`. -/
def consistent (r : ReestablishFields) : Prop :=
  r.nextRevocationNumber ≤ r.nextCommitmentNumber

theorem nextCommitment_le_afterCommitment (r : ReestablishFields) :
    r.nextCommitmentNumber ≤ r.afterCommitment.nextCommitmentNumber :=
  Nat.le_succ _

theorem nextCommitment_lt_afterCommitment (r : ReestablishFields) :
    r.nextCommitmentNumber < r.afterCommitment.nextCommitmentNumber :=
  Nat.lt_succ_self _

theorem nextRevocation_le_afterRevocation (r : ReestablishFields) :
    r.nextRevocationNumber ≤ r.afterRevocation.nextRevocationNumber :=
  Nat.le_succ _

theorem nextRevocation_lt_afterRevocation (r : ReestablishFields) :
    r.nextRevocationNumber < r.afterRevocation.nextRevocationNumber :=
  Nat.lt_succ_self _

theorem afterCommitment_consistent {r : ReestablishFields} (h : r.consistent) :
    r.afterCommitment.consistent := by
  simp [consistent, afterCommitment] at h ⊢
  omega

theorem afterRevocation_consistent {r : ReestablishFields} (h : r.consistent)
    (hlt : r.nextRevocationNumber < r.nextCommitmentNumber) :
    r.afterRevocation.consistent := by
  have hc : r.consistent := h
  have hlt' : r.nextRevocationNumber < r.nextCommitmentNumber := hlt
  simp [consistent, afterRevocation] at hc ⊢
  omega

/-- Package the fields into the corresponding wire message. -/
def toMsg (channelId : ChannelId) (r : ReestablishFields) : Msg :=
  .channelReestablish
    { channelId := channelId
      nextCommitmentNumber := r.nextCommitmentNumber
      nextRevocationNumber := r.nextRevocationNumber
      yourLastPerCommitmentSecret := r.yourLastPerCommitmentSecret
      myCurrentPerCommitmentPoint := r.myCurrentPerCommitmentPoint }

end ReestablishFields

/-- A counter-preserving reestablish step.  A step is either the receipt of
a `commitment_signed` (advance the commitment counter; requires the
revocation counter not to be ahead) or of a `revoke_and_ack` (advance the
revocation counter; requires it to be strictly behind). -/
inductive ReestablishStep : ReestablishFields → ReestablishFields → Prop where
  | commitment (r : ReestablishFields) (h : r.consistent) :
      ReestablishStep r r.afterCommitment
  | revocation (r : ReestablishFields)
      (_h : r.nextRevocationNumber < r.nextCommitmentNumber) :
      ReestablishStep r r.afterRevocation

/-! ## Funding data negotiated by the handshake

BOLT 2 fixes the funding output during `open_channel`/`accept_channel`: the
opener proposes `funding_satoshis`, `push_msat`, a temporary channel id, and
its own `funding_pubkey`, and the acceptor replies with its `funding_pubkey`
in `accept_channel`.  This model has no `open_channel` constructor (see the
module docstring), so the opener's fields are represented as local values,
while the acceptor's key is read from the modelled `accept_channel` record.
The resulting `FundingNegotiation` is the handshake input to
`FundingNegotiation.toFundingParams`, which *computes* the P2WSH program from
the BOLT 3 witness script instead of accepting a hash. -/

open LnLean.Bitcoin

/-- The funding negotiation determined by a received `accept_channel`.  The
peer's `funding_pubkey` field becomes `remoteFundingKey`; the remaining fields
are the opener's local choices from `open_channel`. -/
def AcceptChannel.toFundingNegotiation
    (localFundingKey : PubKey) (fundingSatoshis : BtcAmount) (pushMsat : Msat)
    (temporaryChannelId : TemporaryChannelId) (m : AcceptChannel) :
    LnLean.Bitcoin.FundingNegotiation :=
  { fundingSatoshis := fundingSatoshis
    pushMsat := pushMsat
    localFundingKey := localFundingKey
    remoteFundingKey := m.fundingPubKey
    temporaryChannelId := temporaryChannelId }

/-- The remote funding key of the negotiation is exactly the `funding_pubkey`
field the peer sent in `accept_channel`. -/
@[simp] theorem AcceptChannel.toFundingNegotiation_remoteFundingKey
    (localFundingKey : PubKey) (fundingSatoshis : BtcAmount) (pushMsat : Msat)
    (temporaryChannelId : TemporaryChannelId) (m : AcceptChannel) :
    (m.toFundingNegotiation localFundingKey fundingSatoshis pushMsat
      temporaryChannelId).remoteFundingKey = m.fundingPubKey := rfl

/-- The local funding key of the negotiation is the opener's own key. -/
@[simp] theorem AcceptChannel.toFundingNegotiation_localFundingKey
    (localFundingKey : PubKey) (fundingSatoshis : BtcAmount) (pushMsat : Msat)
    (temporaryChannelId : TemporaryChannelId) (m : AcceptChannel) :
    (m.toFundingNegotiation localFundingKey fundingSatoshis pushMsat
      temporaryChannelId).localFundingKey = localFundingKey := rfl

/-- The funding parameters determined by the handshake.  The P2WSH program is
computed as `H` of the BOLT 3 witness script; there is no separate hash
argument to get wrong. -/
def AcceptChannel.toFundingParams (H : ByteArray → ByteArray)
    (localFundingKey : PubKey) (fundingSatoshis : BtcAmount) (pushMsat : Msat)
    (temporaryChannelId : TemporaryChannelId) (m : AcceptChannel) :
    LnLean.Bitcoin.FundingParams :=
  (m.toFundingNegotiation localFundingKey fundingSatoshis pushMsat
    temporaryChannelId).toFundingParams H

/-- The handshake-derived parameters satisfy the hash link by construction. -/
theorem AcceptChannel.toFundingParams_witnessScriptHash
    (H : ByteArray → ByteArray) (localFundingKey : PubKey)
    (fundingSatoshis : BtcAmount) (pushMsat : Msat)
    (temporaryChannelId : TemporaryChannelId) (m : AcceptChannel) :
    (m.toFundingParams H localFundingKey fundingSatoshis pushMsat
        temporaryChannelId).witnessScriptHash =
      H ((m.toFundingParams H localFundingKey fundingSatoshis pushMsat
        temporaryChannelId).witnessScript.bytes) :=
  LnLean.Bitcoin.FundingNegotiation.toFundingParams_witnessScriptHash H _

/-- `funding_created` cannot be sent before `accept_channel` has been
received, so the peer's `funding_pubkey` is available at the point where the
funding output is built. -/
theorem acceptReceived_of_sendFundingCreated {s s' : HandshakeState}
    (h : handshakeStep s .sendFundingCreated = some s') :
    s.acceptReceived = true := by
  by_cases hg : s.canSendFundingCreated
  · exact hg.2.2.2.1
  · simp [handshakeStep, hg] at h

/-- A permitted `accept_channel` receipt records the peer's key exchange: the
successor state has `acceptReceived = true`. -/
theorem acceptReceived_of_recvAcceptChannel {s s' : HandshakeState}
    (h : handshakeStep s .recvAcceptChannel = some s') :
    s'.acceptReceived = true := by
  by_cases hg : s.canRecvAccept
  · simp [handshakeStep, hg] at h
    rcases h with ⟨-, h⟩
    rw [← h]
  · simp [handshakeStep, hg] at h

/-! ## Explicit `open_channel` coverage

The v1 `HandshakeState` machine starts after `init` and absorbs the arrival of
`open_channel` into the guard on `sendAcceptChannel`; `Msg` deliberately has no
`open_channel` constructor.  That simplification hides the opener's funding
fields: without them, the funding script is not determined by the handshake
(see `FundingLinkTargets.acceptChannel_alone_does_not_determine_witnessScript`).

This section adds the missing funding-side coverage *additively*:

* `OpenChannel` is the funding-relevant projection of BOLT 2 `open_channel`
  (type 32): temporary channel id, `funding_satoshis`, `push_msat`, and
  `funding_pubkey`.
* `OpenChannel.toFundingNegotiation` composes it with `accept_channel` to build
  the same `FundingNegotiation` record as before, so the constructed P2WSH hash
  link is unchanged and is not weakened.
* `FundingPhase`/`fundingStep` record the four funding-negotiation messages
  (`open_channel` in both directions, `accept_channel` in both directions) with
  BOLT 2's ordering guards.  The machine is separate from `handshakeStep`:
  no existing state field, event constructor, or theorem is modified.

Authentication is still not claimed at this layer.  `open_channel` carries no
sender identity and no signature; the transport attribution needed to conclude
that a funding key belongs to a peer is an explicit hypothesis (see
`LnLean.Proofs.Bitcoin.FundingAuthTargets`). -/

/-- Funding-relevant projection of BOLT 2 `open_channel` (type 32).  The
remaining fields (`chain_hash`, dust limit, feerate, basepoints, `channel_flags`,
`shutdown_scriptpubkey`) do not enter the funding output and are omitted; the
wire-complete record is reported as an integration patch rather than added
here, because `LnLean.Protocol.Messages` is outside this lane's write set. -/
structure OpenChannel where
  /-- BOLT 2 `temporary_channel_id`. -/
  temporaryChannelId : ChannelId
  /-- BOLT 2 `funding_satoshis`, the L1 output value. -/
  fundingSatoshis : BtcAmount
  /-- BOLT 2 `push_msat`, the opener's initial gift. -/
  pushMsat : Msat
  /-- BOLT 2 `funding_pubkey`, the opener's funding key. -/
  fundingPubKey : PubKey
deriving Repr, BEq

namespace OpenChannel

/-- The funding negotiation determined jointly by the opener's `open_channel`
and the acceptor's `accept_channel`.  The opener supplies the value, push,
temporary channel id, and local funding key; the acceptor supplies the remote
funding key.  As before, the P2WSH program is **not** a field: it is derived by
`toFundingParams`. -/
def toFundingNegotiation (o : OpenChannel) (a : AcceptChannel) :
    LnLean.Bitcoin.FundingNegotiation :=
  { fundingSatoshis := o.fundingSatoshis
    pushMsat := o.pushMsat
    localFundingKey := o.fundingPubKey
    remoteFundingKey := a.fundingPubKey
    temporaryChannelId := ⟨o.temporaryChannelId⟩ }

/-- The funding parameters of a complete `open_channel`/`accept_channel`
exchange.  The program is computed as `H` of the BOLT 3 witness script. -/
def toFundingParams (H : ByteArray → ByteArray) (o : OpenChannel)
    (a : AcceptChannel) : LnLean.Bitcoin.FundingParams :=
  (o.toFundingNegotiation a).toFundingParams H

/-- The local funding key of the joint construction is exactly the
`open_channel.funding_pubkey`. -/
@[simp] theorem toFundingNegotiation_localFundingKey (o : OpenChannel)
    (a : AcceptChannel) :
    (o.toFundingNegotiation a).localFundingKey = o.fundingPubKey := rfl

/-- The remote funding key is exactly the `accept_channel.funding_pubkey`. -/
@[simp] theorem toFundingNegotiation_remoteFundingKey (o : OpenChannel)
    (a : AcceptChannel) :
    (o.toFundingNegotiation a).remoteFundingKey = a.fundingPubKey := rfl

/-- The negotiated value is the opener's `funding_satoshis`. -/
@[simp] theorem toFundingNegotiation_fundingSatoshis (o : OpenChannel)
    (a : AcceptChannel) :
    (o.toFundingNegotiation a).fundingSatoshis = o.fundingSatoshis := rfl

/-- The negotiated push amount is the opener's `push_msat`. -/
@[simp] theorem toFundingNegotiation_pushMsat (o : OpenChannel)
    (a : AcceptChannel) :
    (o.toFundingNegotiation a).pushMsat = o.pushMsat := rfl

/-- The temporary channel id is the opener's. -/
@[simp] theorem toFundingNegotiation_temporaryChannelId (o : OpenChannel)
    (a : AcceptChannel) :
    (o.toFundingNegotiation a).temporaryChannelId =
      ⟨o.temporaryChannelId⟩ := rfl

/-- **No weakening.**  The joint negotiation is definitionally the existing
`AcceptChannel.toFundingNegotiation` with the opener's fields supplied
explicitly.  Every theorem about the accept-only construction therefore
applies unchanged to the joint `open_channel`/`accept_channel` construction. -/
theorem toFundingNegotiation_eq_acceptChannel (o : OpenChannel)
    (a : AcceptChannel) :
    o.toFundingNegotiation a =
      a.toFundingNegotiation o.fundingPubKey o.fundingSatoshis o.pushMsat
        ⟨o.temporaryChannelId⟩ := rfl

/-- The joint construction satisfies the funding hash link by construction,
exactly as the accept-only construction does. -/
theorem toFundingParams_witnessScriptHash (H : ByteArray → ByteArray)
    (o : OpenChannel) (a : AcceptChannel) :
    (o.toFundingParams H a).witnessScriptHash =
      H (o.toFundingParams H a).witnessScript.bytes :=
  LnLean.Bitcoin.FundingNegotiation.toFundingParams_witnessScriptHash H _

/-- The joint construction's `scriptPubKey` is the P2WSH wrapper over the
computed program. -/
theorem toFundingParams_fundingScriptPubKey (H : ByteArray → ByteArray)
    (o : OpenChannel) (a : AcceptChannel) :
    (o.toFundingParams H a).fundingScriptPubKey =
      p2wsh (H (o.toFundingParams H a).witnessScript.bytes) :=
  LnLean.Bitcoin.FundingNegotiation.toFundingParams_fundingScriptPubKey H _

end OpenChannel

/-! ### The funding-negotiation phase

The four-message exchange that fixes the funding keys.  The phase is separate
from `HandshakeState` so that the ten-milestone v1 machine and its laws are
untouched. -/

/-- A two-party funding negotiation from one transport's point of view.  Each
`Option` records the message sent or received in that direction. -/
structure FundingPhase where
  /-- The `open_channel` this endpoint sent. -/
  openSent : Option OpenChannel := none
  /-- The `open_channel` this endpoint received. -/
  openReceived : Option OpenChannel := none
  /-- The `accept_channel` this endpoint sent. -/
  acceptSent : Option AcceptChannel := none
  /-- The `accept_channel` this endpoint received. -/
  acceptReceived : Option AcceptChannel := none
deriving Repr, BEq

namespace FundingPhase

/-- The phase before any funding message has been exchanged. -/
def initial : FundingPhase := {}

/-- `open_channel` is sent once, before any reply is seen. -/
def canSendOpen (s : FundingPhase) : Bool :=
  s.openSent.isNone && s.openReceived.isNone &&
    s.acceptSent.isNone && s.acceptReceived.isNone

/-- `open_channel` is received once, before the acceptor replies. -/
def canRecvOpen (s : FundingPhase) : Bool :=
  s.openReceived.isNone && s.acceptSent.isNone && s.acceptReceived.isNone

/-- The acceptor replies only after receiving `open_channel`, and only once. -/
def canSendAccept (s : FundingPhase) : Bool :=
  s.openReceived.isSome && s.acceptSent.isNone && s.acceptReceived.isNone

/-- The opener accepts a reply only after sending `open_channel`, and only
once. -/
def canRecvAccept (s : FundingPhase) : Bool :=
  s.openSent.isSome && s.acceptReceived.isNone

/-- The opener's view of the negotiation, available once it has sent
`open_channel` and received `accept_channel`. -/
def openerNegotiation? (s : FundingPhase) : Option LnLean.Bitcoin.FundingNegotiation :=
  match s.openSent, s.acceptReceived with
  | some o, some a => some (o.toFundingNegotiation a)
  | _, _ => none

/-- The acceptor's view of the negotiation, available once it has received
`open_channel` and sent `accept_channel`. -/
def acceptorNegotiation? (s : FundingPhase) : Option LnLean.Bitcoin.FundingNegotiation :=
  match s.openReceived, s.acceptSent with
  | some o, some a => some (o.toFundingNegotiation a)
  | _, _ => none

@[simp] theorem openerNegotiation?_initial :
    initial.openerNegotiation? = none := rfl

@[simp] theorem acceptorNegotiation?_initial :
    initial.acceptorNegotiation? = none := rfl

end FundingPhase

/-- Events of the funding-negotiation phase.  Message payloads are carried, so
the phase records the exact funding keys that were exchanged. -/
inductive FundingPhaseEvent where
  | sendOpen (o : OpenChannel)
  | recvOpen (o : OpenChannel)
  | sendAccept (a : AcceptChannel)
  | recvAccept (a : AcceptChannel)
deriving Repr

/-- One deterministic funding-phase transition.  `none` means the message is
not allowed in the current phase. -/
def fundingStep (s : FundingPhase) : FundingPhaseEvent → Option FundingPhase
  | .sendOpen o =>
      if s.canSendOpen then some { s with openSent := some o } else none
  | .recvOpen o =>
      if s.canRecvOpen then some { s with openReceived := some o } else none
  | .sendAccept a =>
      if s.canSendAccept then some { s with acceptSent := some a } else none
  | .recvAccept a =>
      if s.canRecvAccept then some { s with acceptReceived := some a } else none

/-- Reachable funding-negotiation phases. -/
inductive FundingReachable : FundingPhase → Prop where
  | initial : FundingReachable FundingPhase.initial
  | step {s s' : FundingPhase} (e : FundingPhaseEvent) :
      FundingReachable s → fundingStep s e = some s' → FundingReachable s'

/-- A permitted `sendAccept` requires a previously received `open_channel`:
the acceptor cannot reply to a message it has not seen. -/
theorem sendAccept_requires_openReceived {s s' : FundingPhase}
    {a : AcceptChannel} (h : fundingStep s (.sendAccept a) = some s') :
    ∃ o : OpenChannel, s.openReceived = some o := by
  by_cases hg : s.canSendAccept
  · have hg' := hg
    simp only [FundingPhase.canSendAccept, Bool.and_eq_true] at hg'
    exact Option.isSome_iff_exists.mp hg'.1.1
  · simp [fundingStep, hg] at h

/-- A permitted `recvAccept` requires a previously sent `open_channel`. -/
theorem recvAccept_requires_openSent {s s' : FundingPhase}
    {a : AcceptChannel} (h : fundingStep s (.recvAccept a) = some s') :
    ∃ o : OpenChannel, s.openSent = some o := by
  by_cases hg : s.canRecvAccept
  · have hg' := hg
    simp only [FundingPhase.canRecvAccept, Bool.and_eq_true] at hg'
    exact Option.isSome_iff_exists.mp hg'.1
  · simp [fundingStep, hg] at h

/-- The opener's funding key is the one it put in `open_channel`; the peer's is
the one from `accept_channel`.  This is the key-provenance half of
authentication: it identifies *which message* each key came from. -/
theorem fundingPhase_opener_keys {s : FundingPhase}
    {n : LnLean.Bitcoin.FundingNegotiation}
    (h : s.openerNegotiation? = some n) :
    ∃ (o : OpenChannel) (a : AcceptChannel),
      s.openSent = some o ∧ s.acceptReceived = some a ∧
      n = o.toFundingNegotiation a ∧
      n.localFundingKey = o.fundingPubKey ∧
      n.remoteFundingKey = a.fundingPubKey := by
  unfold FundingPhase.openerNegotiation? at h
  cases hs : s.openSent with
  | none => simp [hs] at h
  | some o =>
    cases ha : s.acceptReceived with
    | none => simp [hs, ha] at h
    | some a =>
      simp only [hs, ha] at h
      injection h with hn
      subst hn
      exact ⟨o, a, rfl, rfl, rfl, rfl, rfl⟩

/-- The acceptor's view has the same key provenance. -/
theorem fundingPhase_acceptor_keys {s : FundingPhase}
    {n : LnLean.Bitcoin.FundingNegotiation}
    (h : s.acceptorNegotiation? = some n) :
    ∃ (o : OpenChannel) (a : AcceptChannel),
      s.openReceived = some o ∧ s.acceptSent = some a ∧
      n = o.toFundingNegotiation a ∧
      n.localFundingKey = o.fundingPubKey ∧
      n.remoteFundingKey = a.fundingPubKey := by
  unfold FundingPhase.acceptorNegotiation? at h
  cases hs : s.openReceived with
  | none => simp [hs] at h
  | some o =>
    cases ha : s.acceptSent with
    | none => simp [hs, ha] at h
    | some a =>
      simp only [hs, ha] at h
      injection h with hn
      subst hn
      exact ⟨o, a, rfl, rfl, rfl, rfl, rfl⟩

/-- **`open_channel` coverage at the handshake boundary.**  When the existing
v1 handshake permits `funding_created`, the peer's `accept_channel` has already
arrived, and the remote funding key of the *joint* `open_channel`/
`accept_channel` construction is exactly the key that message carried. -/
theorem acceptKey_bound_before_fundingCreated {s s' : HandshakeState}
    (h : handshakeStep s .sendFundingCreated = some s')
    (o : OpenChannel) (a : AcceptChannel) (H : ByteArray → ByteArray) :
    s.acceptReceived = true ∧
      ((o.toFundingNegotiation a).toFundingParams H).remoteFundingKey =
        a.fundingPubKey :=
  ⟨acceptReceived_of_sendFundingCreated h, rfl⟩

/-- The phase layer is non-vacuous: a complete exchange reaches a state where
both endpoints' negotiations are available. -/
theorem fundingReachable_negotiation_witness :
    ∃ s : FundingPhase,
      FundingReachable s ∧
      s.openerNegotiation?.isSome = true ∧
      s.acceptorNegotiation?.isSome = true := by
  let o : OpenChannel :=
    { temporaryChannelId := ⟨ByteArray.empty⟩
      fundingSatoshis := 0
      pushMsat := ⟨0⟩
      fundingPubKey := ⟨ByteArray.empty⟩ }
  let a : AcceptChannel :=
    { temporaryChannelId := ⟨ByteArray.empty⟩
      dustLimitSatoshis := 0
      maxHtlcValueInFlightMsat := 0
      channelReserveSatoshis := 0
      htlcMinimumMsat := 0
      minimumDepth := 0
      toSelfDelay := 0
      maxAcceptedHtlcs := 0
      fundingPubKey := ⟨ByteArray.empty⟩
      revocationBasepoint := ⟨ByteArray.empty⟩
      paymentBasepoint := ⟨ByteArray.empty⟩
      delayedPaymentBasepoint := ⟨ByteArray.empty⟩
      htlcBasepoint := ⟨ByteArray.empty⟩
      firstPerCommitmentPoint := ⟨ByteArray.empty⟩ }
  let s0 : FundingPhase := FundingPhase.initial
  let s1 : FundingPhase :=
    { openSent := some o, openReceived := none,
      acceptSent := none, acceptReceived := none }
  let s2 : FundingPhase :=
    { openSent := some o, openReceived := some o,
      acceptSent := none, acceptReceived := none }
  let s3 : FundingPhase :=
    { openSent := some o, openReceived := some o,
      acceptSent := some a, acceptReceived := none }
  let s4 : FundingPhase :=
    { openSent := some o, openReceived := some o,
      acceptSent := some a, acceptReceived := some a }
  have h1 : fundingStep s0 (.sendOpen o) = some s1 := by
    simp [fundingStep, s0, s1, FundingPhase.initial, FundingPhase.canSendOpen]
  have h2 : fundingStep s1 (.recvOpen o) = some s2 := by
    simp [fundingStep, s1, s2, FundingPhase.canRecvOpen]
  have h3 : fundingStep s2 (.sendAccept a) = some s3 := by
    simp [fundingStep, s2, s3, FundingPhase.canSendAccept]
  have h4 : fundingStep s3 (.recvAccept a) = some s4 := by
    simp [fundingStep, s3, s4, FundingPhase.canRecvAccept]
  refine ⟨s4, ?_, ?_, ?_⟩
  · exact FundingReachable.step _ (FundingReachable.step _ (FundingReachable.step _
      (FundingReachable.step _ FundingReachable.initial h1) h2) h3) h4
  · simp [s4, FundingPhase.openerNegotiation?]
  · simp [s4, FundingPhase.acceptorNegotiation?]

end LnLean.Protocol
