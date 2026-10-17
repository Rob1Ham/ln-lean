import LnLean.Protocol.Messages

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

end LnLean.Protocol
