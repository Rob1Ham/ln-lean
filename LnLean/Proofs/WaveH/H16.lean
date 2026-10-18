import LnLean.Protocol.Handshake
import LnLean.Proofs.Bitcoin.FundingAuthTargets

/-!
# H16 — `open_channel` payload bridge for the funding phase (`L1-03`)

**English claim.**  The funding-negotiation phase of
`LnLean.Protocol.Handshake` already records the four messages
(`open_channel`/`accept_channel` in both directions) and proves that a
permitted `sendAccept` requires `openReceived`.  What it does not record is the
*wire message* that supplied the opener's funding fields: `FundingPhase` stores
an `OpenChannel`, which is the funding-relevant projection of BOLT 2 type 32.

This module adds an additive, wire-facing layer:

* `OpenChannelMsg` is a local model of the funding-relevant `open_channel`
  payload (type 32).  It carries the temporary channel id, the funding value,
  the push amount, and the opener's `funding_pubkey` — exactly the fields the
  funding construction consumes.  If the wire-complete record from lane `H13`
  (`L1-03`, fixed 313-byte payload with the empty `shutdown_scriptpubkey`)
  is available, its four funding projections instantiate this record through
  `OpenChannelMsg.ofWire`; the bridge below is invariant under that extension.
* `MsgFundingPhase` is the same four-message machine with the two
  `open_channel` slots typed as `OpenChannelMsg` instead of `OpenChannel`.
  `MsgFundingPhase.erase` maps it onto the existing `FundingPhase` by the
  projection `OpenChannelMsg.toOpenChannel`.
* `msgStep` mirrors `fundingStep` with the same BOLT 2 ordering guards.
  `erase_msgStep` proves the simulation square: erasing after a transition is
  the existing `fundingStep` after erasing.  The new layer therefore neither
  strengthens nor weakens the guards.
* `msgStep_sendOpen_exact`, `msgStep_recvOpen_exact`,
  `msgStep_sendAccept_exact`, `msgStep_recvAccept_exact` prove that a
  successful transition stores the *exact* message, preserves the previously
  stored exact message in the other direction, and (for the accept messages)
  still requires the corresponding open message to be present.
* `sendAccept_requires_openReceived` restates the existing guard law at the
  message layer, in both the exact-message and erased-`OpenChannel` forms.
* `MsgTrace` records the event history.  `msgTrace_*_mem` and the
  `OccursBefore` ordering theorems prove that every stored payload occurred as
  an actual event, and that `accept_channel` is preceded in the history by the
  `open_channel` receipt/send it answers.  `msgReachable_*` lift this to
  `MsgReachable`.

## Transport-attribution caveat (retained)

`open_channel` carries no sender field and no signature.  This module therefore
proves *message* provenance, not *peer* attribution: a `ReceivedOpenChannelMsg`
attaches the transport's claimed sender to the payload, and
`msgAttributed_key_in_script` only concludes that the transport-authenticated
key is the script key **under the explicit hypothesis**
`OpenChannelAttributed sender m.toOpenChannel`.  `same_msg_distinct_senders`
mechanizes the negative: one payload is compatible with two distinct claimed
senders, so payload equality alone cannot establish attribution.  Noise
authentication and key ownership remain `PR-01`/C3
(`docs/ASSUMPTIONS.md` §3).

## Anchors

* BOLT 2 §The `open_channel` Message (type 32):
  `temporary_channel_id`, `funding_satoshis`, `push_msat`, `funding_pubkey`.
* BOLT 2 §Channel Establishment v1: `open_channel`, `accept_channel`,
  `funding_created`, `funding_signed`, `channel_ready`, in that order.
* `refs/rust-lightning/lightning/src/ln/msgs.rs:111` and `:371` for the
  message records; `lightning/src/ln/wire.rs:494` for type 33 and
  `:518` for type 34.
-/

namespace LnLean.Proofs.WaveH.H16

set_option autoImplicit false

open LnLean
open LnLean.Protocol
open LnLean.Bitcoin
open LnLean.Proofs.Bitcoin.FundingAuthTargets

/-! ## The local `open_channel` payload -/

/-- Funding-relevant projection of BOLT 2 `open_channel` (type 32).

The wire-complete payload also carries `chain_hash`, the dust/HTLC policy
fields, the commitment feerate, `to_self_delay`, `max_accepted_htlcs`, the four
non-funding basepoints, `first_per_commitment_point`, `channel_flags`, and
`shutdown_scriptpubkey`.  None of those enter the funding output; the
wire-complete record is lane `H13`/`H17` and the `Messages.lean` patch, while
this record is the part the funding phase consumes. -/
structure OpenChannelMsg where
  /-- BOLT 2 `temporary_channel_id`. -/
  temporaryChannelId : ChannelId
  /-- BOLT 2 `funding_satoshis`. -/
  fundingSatoshis : BtcAmount
  /-- BOLT 2 `push_msat`. -/
  pushMsat : Msat
  /-- BOLT 2 `funding_pubkey`. -/
  fundingPubKey : PubKey
deriving Repr, BEq

namespace OpenChannelMsg

/-- The funding-phase view of the message: the existing `OpenChannel` record. -/
def toOpenChannel (m : OpenChannelMsg) : OpenChannel :=
  { temporaryChannelId := m.temporaryChannelId
    fundingSatoshis := m.fundingSatoshis
    pushMsat := m.pushMsat
    fundingPubKey := m.fundingPubKey }

/-- Instantiate the bridge record from any wire-complete `open_channel` record
that exposes the four funding fields.  This is the integration hook for lane
`H13`: the arguments are exactly the four projections, so no wire field is
re-interpreted here. -/
def ofWire (temporaryChannelId : ChannelId) (fundingSatoshis : BtcAmount)
    (pushMsat : Msat) (fundingPubKey : PubKey) : OpenChannelMsg :=
  { temporaryChannelId := temporaryChannelId
    fundingSatoshis := fundingSatoshis
    pushMsat := pushMsat
    fundingPubKey := fundingPubKey }

@[simp] theorem toOpenChannel_temporaryChannelId (m : OpenChannelMsg) :
    m.toOpenChannel.temporaryChannelId = m.temporaryChannelId := rfl

@[simp] theorem toOpenChannel_fundingSatoshis (m : OpenChannelMsg) :
    m.toOpenChannel.fundingSatoshis = m.fundingSatoshis := rfl

@[simp] theorem toOpenChannel_pushMsat (m : OpenChannelMsg) :
    m.toOpenChannel.pushMsat = m.pushMsat := rfl

@[simp] theorem toOpenChannel_fundingPubKey (m : OpenChannelMsg) :
    m.toOpenChannel.fundingPubKey = m.fundingPubKey := rfl

@[simp] theorem ofWire_toOpenChannel (c : ChannelId) (v : BtcAmount)
    (p : Msat) (k : PubKey) :
    (ofWire c v p k).toOpenChannel =
      { temporaryChannelId := c
        fundingSatoshis := v
        pushMsat := p
        fundingPubKey := k } := rfl

/-- The projection loses no funding field: equal projections force equal
messages.  This is what makes the bridge below faithful to the exact payload. -/
theorem toOpenChannel_injective : Function.Injective toOpenChannel := by
  intro m n h
  have h1 : m.temporaryChannelId = n.temporaryChannelId :=
    congrArg (fun o : OpenChannel => o.temporaryChannelId) h
  have h2 : m.fundingSatoshis = n.fundingSatoshis :=
    congrArg (fun o : OpenChannel => o.fundingSatoshis) h
  have h3 : m.pushMsat = n.pushMsat :=
    congrArg (fun o : OpenChannel => o.pushMsat) h
  have h4 : m.fundingPubKey = n.fundingPubKey :=
    congrArg (fun o : OpenChannel => o.fundingPubKey) h
  cases m
  cases n
  simp_all

end OpenChannelMsg

/-! ## The message-typed funding phase -/

/-- The funding-negotiation phase with the exact `open_channel` payloads.  It
mirrors `FundingPhase` field for field; the accept side is unchanged because
`FundingPhase` already stores the full `AcceptChannel`. -/
structure MsgFundingPhase where
  /-- The `open_channel` this endpoint sent, exactly as encoded. -/
  openSent : Option OpenChannelMsg := none
  /-- The `open_channel` this endpoint received, exactly as decoded. -/
  openReceived : Option OpenChannelMsg := none
  /-- The `accept_channel` this endpoint sent. -/
  acceptSent : Option AcceptChannel := none
  /-- The `accept_channel` this endpoint received. -/
  acceptReceived : Option AcceptChannel := none
deriving Repr, BEq

namespace MsgFundingPhase

/-- The phase before any funding message has been exchanged. -/
def initial : MsgFundingPhase := {}

/-- Map the message-typed phase onto the existing `FundingPhase` by the
funding projection.  This is the whole bridge: it is the identity on the
accept slots and `Option.map toOpenChannel` on the open slots. -/
def erase (s : MsgFundingPhase) : FundingPhase :=
  { openSent := s.openSent.map OpenChannelMsg.toOpenChannel
    openReceived := s.openReceived.map OpenChannelMsg.toOpenChannel
    acceptSent := s.acceptSent
    acceptReceived := s.acceptReceived }

@[simp] theorem erase_initial : initial.erase = FundingPhase.initial := rfl

/-- The opener's view of the negotiation, computed from the exact messages. -/
def openerNegotiation? (s : MsgFundingPhase) :
    Option LnLean.Bitcoin.FundingNegotiation :=
  match s.openSent, s.acceptReceived with
  | some m, some a => some (m.toOpenChannel.toFundingNegotiation a)
  | _, _ => none

/-- The acceptor's view of the negotiation, computed from the exact messages. -/
def acceptorNegotiation? (s : MsgFundingPhase) :
    Option LnLean.Bitcoin.FundingNegotiation :=
  match s.openReceived, s.acceptSent with
  | some m, some a => some (m.toOpenChannel.toFundingNegotiation a)
  | _, _ => none

/-- Erasing commutes with the opener's negotiation projection. -/
@[simp] theorem openerNegotiation?_erase (s : MsgFundingPhase) :
    s.erase.openerNegotiation? = s.openerNegotiation? := by
  unfold FundingPhase.openerNegotiation? openerNegotiation? erase
  cases s.openSent <;> cases s.acceptReceived <;> rfl

/-- Erasing commutes with the acceptor's negotiation projection. -/
@[simp] theorem acceptorNegotiation?_erase (s : MsgFundingPhase) :
    s.erase.acceptorNegotiation? = s.acceptorNegotiation? := by
  unfold FundingPhase.acceptorNegotiation? acceptorNegotiation? erase
  cases s.openReceived <;> cases s.acceptSent <;> rfl

/-- Erasing a state after storing a sent `open_channel` is the same as storing
the projected message after erasing. -/
theorem erase_sendOpen (s : MsgFundingPhase) (m : OpenChannelMsg) :
    ({ s with openSent := some m } : MsgFundingPhase).erase =
      { s.erase with openSent := some m.toOpenChannel } := rfl

/-- The same square for a received `open_channel`. -/
theorem erase_recvOpen (s : MsgFundingPhase) (m : OpenChannelMsg) :
    ({ s with openReceived := some m } : MsgFundingPhase).erase =
      { s.erase with openReceived := some m.toOpenChannel } := rfl

/-- The same square for a sent `accept_channel`. -/
theorem erase_sendAccept (s : MsgFundingPhase) (a : AcceptChannel) :
    ({ s with acceptSent := some a } : MsgFundingPhase).erase =
      { s.erase with acceptSent := some a } := rfl

/-- The same square for a received `accept_channel`. -/
theorem erase_recvAccept (s : MsgFundingPhase) (a : AcceptChannel) :
    ({ s with acceptReceived := some a } : MsgFundingPhase).erase =
      { s.erase with acceptReceived := some a } := rfl

/-- `open_channel` is sent once, before any reply is seen. -/
def canSendOpen (s : MsgFundingPhase) : Bool :=
  s.openSent.isNone && s.openReceived.isNone &&
    s.acceptSent.isNone && s.acceptReceived.isNone

/-- `open_channel` is received once, before the acceptor replies. -/
def canRecvOpen (s : MsgFundingPhase) : Bool :=
  s.openReceived.isNone && s.acceptSent.isNone && s.acceptReceived.isNone

/-- The acceptor replies only after receiving `open_channel`, and only once. -/
def canSendAccept (s : MsgFundingPhase) : Bool :=
  s.openReceived.isSome && s.acceptSent.isNone && s.acceptReceived.isNone

/-- The opener accepts a reply only after sending `open_channel`, and only
once. -/
def canRecvAccept (s : MsgFundingPhase) : Bool :=
  s.openSent.isSome && s.acceptReceived.isNone

/-! ### Guard agreement with the existing phase -/

theorem canSendOpen_erase (s : MsgFundingPhase) :
    s.canSendOpen = s.erase.canSendOpen := by
  unfold canSendOpen FundingPhase.canSendOpen erase
  cases s.openSent <;> cases s.openReceived <;>
    cases s.acceptSent <;> cases s.acceptReceived <;> rfl

theorem canRecvOpen_erase (s : MsgFundingPhase) :
    s.canRecvOpen = s.erase.canRecvOpen := by
  unfold canRecvOpen FundingPhase.canRecvOpen erase
  cases s.openReceived <;> cases s.acceptSent <;> cases s.acceptReceived <;> rfl

theorem canSendAccept_erase (s : MsgFundingPhase) :
    s.canSendAccept = s.erase.canSendAccept := by
  unfold canSendAccept FundingPhase.canSendAccept erase
  cases s.openReceived <;> cases s.acceptSent <;> cases s.acceptReceived <;> rfl

theorem canRecvAccept_erase (s : MsgFundingPhase) :
    s.canRecvAccept = s.erase.canRecvAccept := by
  unfold canRecvAccept FundingPhase.canRecvAccept erase
  cases s.openSent <;> cases s.acceptReceived <;> rfl

end MsgFundingPhase

/-! ## The message events and transitions -/

/-- Events of the message-typed funding phase.  The `open_channel` events carry
the exact payload. -/
inductive MsgFundingPhaseEvent where
  | sendOpen (m : OpenChannelMsg)
  | recvOpen (m : OpenChannelMsg)
  | sendAccept (a : AcceptChannel)
  | recvAccept (a : AcceptChannel)
deriving Repr

/-- One deterministic funding-phase transition at the message layer.  `none`
means the message is not allowed in the current phase. -/
def msgStep (s : MsgFundingPhase) :
    MsgFundingPhaseEvent → Option MsgFundingPhase
  | .sendOpen m =>
      if s.canSendOpen then some { s with openSent := some m } else none
  | .recvOpen m =>
      if s.canRecvOpen then some { s with openReceived := some m } else none
  | .sendAccept a =>
      if s.canSendAccept then some { s with acceptSent := some a } else none
  | .recvAccept a =>
      if s.canRecvAccept then some { s with acceptReceived := some a } else none

/-- Erase an event: the same message with the funding projection. -/
def eraseEvent : MsgFundingPhaseEvent → FundingPhaseEvent
  | .sendOpen m => .sendOpen m.toOpenChannel
  | .recvOpen m => .recvOpen m.toOpenChannel
  | .sendAccept a => .sendAccept a
  | .recvAccept a => .recvAccept a

/-! ### Exact carrying and framing -/

/-- **Sent `open_channel` is stored exactly.**  A successful send stores the
exact message and leaves the other three slots untouched. -/
theorem msgStep_sendOpen_exact {s s' : MsgFundingPhase} {m : OpenChannelMsg}
    (h : msgStep s (.sendOpen m) = some s') :
    s'.openSent = some m ∧ s'.openReceived = s.openReceived ∧
      s'.acceptSent = s.acceptSent ∧ s'.acceptReceived = s.acceptReceived := by
  by_cases hg : s.canSendOpen
  · simp [msgStep, hg] at h
    cases h
    simp
  · simp [msgStep, hg] at h

/-- **Received `open_channel` is stored exactly.** -/
theorem msgStep_recvOpen_exact {s s' : MsgFundingPhase} {m : OpenChannelMsg}
    (h : msgStep s (.recvOpen m) = some s') :
    s'.openReceived = some m ∧ s'.openSent = s.openSent ∧
      s'.acceptSent = s.acceptSent ∧ s'.acceptReceived = s.acceptReceived := by
  by_cases hg : s.canRecvOpen
  · simp [msgStep, hg] at h
    cases h
    simp
  · simp [msgStep, hg] at h

/-- **A permitted `sendAccept` carries the exact accept message, preserves the
exact received `open_channel`, and still requires one.**  This is the message
layer's form of `FundingPhase.sendAccept_requires_openReceived`. -/
theorem msgStep_sendAccept_exact {s s' : MsgFundingPhase}
    {a : AcceptChannel} (h : msgStep s (.sendAccept a) = some s') :
    s'.acceptSent = some a ∧ s'.openReceived = s.openReceived ∧
      s'.openSent = s.openSent ∧ s'.acceptReceived = s.acceptReceived ∧
      ∃ m : OpenChannelMsg, s.openReceived = some m := by
  by_cases hg : s.canSendAccept
  · have hg' := hg
    unfold MsgFundingPhase.canSendAccept at hg'
    simp only [Bool.and_eq_true] at hg'
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hg'.1.1
    simp [msgStep, hg] at h
    cases h
    exact ⟨rfl, rfl, rfl, rfl, ⟨m, hm⟩⟩
  · simp [msgStep, hg] at h

/-- **A permitted `recvAccept` carries the exact accept message and preserves
the exact sent `open_channel`.** -/
theorem msgStep_recvAccept_exact {s s' : MsgFundingPhase}
    {a : AcceptChannel} (h : msgStep s (.recvAccept a) = some s') :
    s'.acceptReceived = some a ∧ s'.openSent = s.openSent ∧
      s'.openReceived = s.openReceived ∧ s'.acceptSent = s.acceptSent ∧
      ∃ m : OpenChannelMsg, s.openSent = some m := by
  by_cases hg : s.canRecvAccept
  · have hg' := hg
    unfold MsgFundingPhase.canRecvAccept at hg'
    simp only [Bool.and_eq_true] at hg'
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hg'.1
    simp [msgStep, hg] at h
    cases h
    exact ⟨rfl, rfl, rfl, rfl, ⟨m, hm⟩⟩
  · simp [msgStep, hg] at h

/-- **`sendAccept` still requires `openReceived`, exact-message form.** -/
theorem sendAccept_requires_openReceivedMsg {s s' : MsgFundingPhase}
    {a : AcceptChannel} (h : msgStep s (.sendAccept a) = some s') :
    ∃ m : OpenChannelMsg, s.openReceived = some m :=
  (msgStep_sendAccept_exact h).2.2.2.2

/-- **`sendAccept` still requires `openReceived`, existing-form corollary.**
This is literally the conclusion of
`FundingPhase.sendAccept_requires_openReceived` after erasing. -/
theorem sendAccept_requires_openReceived {s s' : MsgFundingPhase}
    {a : AcceptChannel} (h : msgStep s (.sendAccept a) = some s') :
    ∃ o : OpenChannel, s.erase.openReceived = some o := by
  obtain ⟨m, hm⟩ := sendAccept_requires_openReceivedMsg h
  exact ⟨m.toOpenChannel, by simp [MsgFundingPhase.erase, hm]⟩

/-- **`recvAccept` still requires `openSent`.** -/
theorem recvAccept_requires_openSentMsg {s s' : MsgFundingPhase}
    {a : AcceptChannel} (h : msgStep s (.recvAccept a) = some s') :
    ∃ m : OpenChannelMsg, s.openSent = some m :=
  (msgStep_recvAccept_exact h).2.2.2.2

/-! ### The simulation square -/

/-- **Erasing after a message transition is the existing transition after
erasing.**  The message layer therefore refines the existing phase without
changing any guard or any accept-side behaviour. -/
theorem erase_msgStep (s : MsgFundingPhase) (e : MsgFundingPhaseEvent) :
    (msgStep s e).map MsgFundingPhase.erase =
      fundingStep s.erase (eraseEvent e) := by
  cases e with
  | sendOpen m =>
    by_cases hg : s.canSendOpen
    · have hg' : s.erase.canSendOpen = true := by
        rw [← MsgFundingPhase.canSendOpen_erase]
        exact hg
      simp [msgStep, hg, MsgFundingPhase.erase_sendOpen, eraseEvent, fundingStep, hg']
    · have hgfalse : s.canSendOpen = false := by
        cases h : s.canSendOpen <;> simp_all
      have hg' : s.erase.canSendOpen = false := by
        rw [← MsgFundingPhase.canSendOpen_erase]
        exact hgfalse
      simp [msgStep, hgfalse, eraseEvent, fundingStep, hg']
  | recvOpen m =>
    by_cases hg : s.canRecvOpen
    · have hg' : s.erase.canRecvOpen = true := by
        rw [← MsgFundingPhase.canRecvOpen_erase]
        exact hg
      simp [msgStep, hg, MsgFundingPhase.erase_recvOpen, eraseEvent, fundingStep, hg']
    · have hgfalse : s.canRecvOpen = false := by
        cases h : s.canRecvOpen <;> simp_all
      have hg' : s.erase.canRecvOpen = false := by
        rw [← MsgFundingPhase.canRecvOpen_erase]
        exact hgfalse
      simp [msgStep, hgfalse, eraseEvent, fundingStep, hg']
  | sendAccept a =>
    by_cases hg : s.canSendAccept
    · have hg' : s.erase.canSendAccept = true := by
        rw [← MsgFundingPhase.canSendAccept_erase]
        exact hg
      simp [msgStep, hg, MsgFundingPhase.erase_sendAccept, eraseEvent, fundingStep, hg']
    · have hgfalse : s.canSendAccept = false := by
        cases h : s.canSendAccept <;> simp_all
      have hg' : s.erase.canSendAccept = false := by
        rw [← MsgFundingPhase.canSendAccept_erase]
        exact hgfalse
      simp [msgStep, hgfalse, eraseEvent, fundingStep, hg']
  | recvAccept a =>
    by_cases hg : s.canRecvAccept
    · have hg' : s.erase.canRecvAccept = true := by
        rw [← MsgFundingPhase.canRecvAccept_erase]
        exact hg
      simp [msgStep, hg, MsgFundingPhase.erase_recvAccept, eraseEvent, fundingStep, hg']
    · have hgfalse : s.canRecvAccept = false := by
        cases h : s.canRecvAccept <;> simp_all
      have hg' : s.erase.canRecvAccept = false := by
        rw [← MsgFundingPhase.canRecvAccept_erase]
        exact hgfalse
      simp [msgStep, hgfalse, eraseEvent, fundingStep, hg']

/-- Pointwise form of the simulation square, convenient when only the
transition hypothesis is in scope. -/
theorem erase_msgStep_apply {s s' : MsgFundingPhase} {e : MsgFundingPhaseEvent}
    (h : msgStep s e = some s') :
    (some s').map MsgFundingPhase.erase = fundingStep s.erase (eraseEvent e) := by
  rw [← h]
  exact erase_msgStep s e

/-! ## Reachability, ordering, and provenance -/

/-- Reachable message-typed funding phases. -/
inductive MsgReachable : MsgFundingPhase → Prop where
  | initial : MsgReachable MsgFundingPhase.initial
  | step {s s' : MsgFundingPhase} (e : MsgFundingPhaseEvent) :
      MsgReachable s → msgStep s e = some s' → MsgReachable s'

/-- The message layer is reachable only through the existing phase machine. -/
theorem msgReachable_erase {s : MsgFundingPhase} (h : MsgReachable s) :
    FundingReachable s.erase := by
  induction h with
  | initial =>
    simpa only [MsgFundingPhase.erase_initial] using FundingReachable.initial
  | step e _ hstep ih =>
    have hsq := erase_msgStep_apply hstep
    simp only [Option.map_some] at hsq
    exact FundingReachable.step (eraseEvent e) ih hsq.symm

/-- Ordering invariant: an accept message cannot be present unless the
corresponding open message is present. -/
def OrderingInv (s : MsgFundingPhase) : Prop :=
  (s.acceptSent = none ∨ ∃ m : OpenChannelMsg, s.openReceived = some m) ∧
  (s.acceptReceived = none ∨ ∃ m : OpenChannelMsg, s.openSent = some m)

theorem orderingInv_initial : OrderingInv MsgFundingPhase.initial := by
  simp [OrderingInv, MsgFundingPhase.initial]

/-- Every transition preserves the ordering invariant. -/
theorem orderingInv_step {s s' : MsgFundingPhase}
    {e : MsgFundingPhaseEvent} (h : msgStep s e = some s')
    (hi : OrderingInv s) : OrderingInv s' := by
  cases e with
  | sendOpen m =>
    have hex := msgStep_sendOpen_exact h
    unfold OrderingInv
    rw [hex.2.1, hex.2.2.1, hex.2.2.2]
    exact ⟨hi.1, Or.inr ⟨m, hex.1⟩⟩
  | recvOpen m =>
    have hex := msgStep_recvOpen_exact h
    unfold OrderingInv
    rw [hex.2.1, hex.2.2.1, hex.2.2.2]
    exact ⟨Or.inr ⟨m, hex.1⟩, hi.2⟩
  | sendAccept a =>
    have hex := msgStep_sendAccept_exact h
    unfold OrderingInv
    rw [hex.1, hex.2.1, hex.2.2.1, hex.2.2.2.1]
    exact ⟨Or.inr hex.2.2.2.2, hi.2⟩
  | recvAccept a =>
    have hex := msgStep_recvAccept_exact h
    unfold OrderingInv
    rw [hex.1, hex.2.1, hex.2.2.1, hex.2.2.2.1]
    exact ⟨hi.1, Or.inr hex.2.2.2.2⟩

/-- Reachable states satisfy the ordering invariant. -/
theorem msgReachable_ordering {s : MsgFundingPhase} (h : MsgReachable s) :
    OrderingInv s := by
  induction h with
  | initial => exact orderingInv_initial
  | step e _ hstep ih => exact orderingInv_step hstep ih

/-- **Ordering, reachable-state form.**  A stored `accept_channel` implies the
exact open message it answers is stored. -/
theorem msgReachable_acceptSent_has_openReceived {s : MsgFundingPhase}
    (hr : MsgReachable s) {a : AcceptChannel} (h : s.acceptSent = some a) :
    ∃ m : OpenChannelMsg, s.openReceived = some m := by
  rcases (msgReachable_ordering hr).1 with hnone | hex
  · rw [hnone] at h
    exact absurd h (by simp)
  · exact hex

/-- **Ordering, reachable-state form, opener side.** -/
theorem msgReachable_acceptReceived_has_openSent {s : MsgFundingPhase}
    (hr : MsgReachable s) {a : AcceptChannel} (h : s.acceptReceived = some a) :
    ∃ m : OpenChannelMsg, s.openSent = some m := by
  rcases (msgReachable_ordering hr).2 with hnone | hex
  · rw [hnone] at h
    exact absurd h (by simp)
  · exact hex

/-! ### Event histories -/

/-- A concrete event history for a message-phase state. -/
inductive MsgTrace : MsgFundingPhase → List MsgFundingPhaseEvent → Prop where
  | nil : MsgTrace MsgFundingPhase.initial []
  | snoc {s s' : MsgFundingPhase} {es : List MsgFundingPhaseEvent}
      {e : MsgFundingPhaseEvent} :
      MsgTrace s es → msgStep s e = some s' → MsgTrace s' (es ++ [e])

/-- Every trace ends in a reachable state. -/
theorem msgTrace_reachable {s : MsgFundingPhase}
    {es : List MsgFundingPhaseEvent} (h : MsgTrace s es) : MsgReachable s := by
  induction h with
  | nil => exact MsgReachable.initial
  | snoc _ hstep ih => exact MsgReachable.step _ ih hstep

/-- Every reachable state has a history. -/
theorem msgReachable_has_trace {s : MsgFundingPhase} (h : MsgReachable s) :
    ∃ es : List MsgFundingPhaseEvent, MsgTrace s es := by
  induction h with
  | initial => exact ⟨[], MsgTrace.nil⟩
  | step e _ hstep ih =>
    obtain ⟨es, ht⟩ := ih
    exact ⟨es ++ [e], MsgTrace.snoc ht hstep⟩

/-- A stored sent `open_channel` occurred as a `sendOpen` event. -/
theorem msgTrace_openSent_mem {s : MsgFundingPhase}
    {es : List MsgFundingPhaseEvent} (ht : MsgTrace s es) {m : OpenChannelMsg}
    (h : s.openSent = some m) :
    MsgFundingPhaseEvent.sendOpen m ∈ es := by
  revert h
  induction ht with
  | nil =>
    intro h
    simp [MsgFundingPhase.initial] at h
  | snoc ht hstep ih =>
    rename_i s s' es e
    intro h
    cases e with
    | sendOpen m₀ =>
      have hex := msgStep_sendOpen_exact hstep
      rw [hex.1] at h
      injection h with hm
      subst hm
      exact List.mem_append.mpr (Or.inr (by simp))
    | recvOpen m₀ =>
      have hex := msgStep_recvOpen_exact hstep
      rw [hex.2.1] at h
      exact List.mem_append.mpr (Or.inl (ih h))
    | sendAccept a =>
      have hex := msgStep_sendAccept_exact hstep
      rw [hex.2.2.1] at h
      exact List.mem_append.mpr (Or.inl (ih h))
    | recvAccept a =>
      have hex := msgStep_recvAccept_exact hstep
      rw [hex.2.1] at h
      exact List.mem_append.mpr (Or.inl (ih h))

/-- A stored received `open_channel` occurred as a `recvOpen` event. -/
theorem msgTrace_openReceived_mem {s : MsgFundingPhase}
    {es : List MsgFundingPhaseEvent} (ht : MsgTrace s es) {m : OpenChannelMsg}
    (h : s.openReceived = some m) :
    MsgFundingPhaseEvent.recvOpen m ∈ es := by
  revert h
  induction ht with
  | nil =>
    intro h
    simp [MsgFundingPhase.initial] at h
  | snoc ht hstep ih =>
    rename_i s s' es e
    intro h
    cases e with
    | sendOpen m₀ =>
      have hex := msgStep_sendOpen_exact hstep
      rw [hex.2.1] at h
      exact List.mem_append.mpr (Or.inl (ih h))
    | recvOpen m₀ =>
      have hex := msgStep_recvOpen_exact hstep
      rw [hex.1] at h
      injection h with hm
      subst hm
      exact List.mem_append.mpr (Or.inr (by simp))
    | sendAccept a =>
      have hex := msgStep_sendAccept_exact hstep
      rw [hex.2.1] at h
      exact List.mem_append.mpr (Or.inl (ih h))
    | recvAccept a =>
      have hex := msgStep_recvAccept_exact hstep
      rw [hex.2.2.1] at h
      exact List.mem_append.mpr (Or.inl (ih h))

/-- A stored sent `accept_channel` occurred as a `sendAccept` event. -/
theorem msgTrace_acceptSent_mem {s : MsgFundingPhase}
    {es : List MsgFundingPhaseEvent} (ht : MsgTrace s es) {a : AcceptChannel}
    (h : s.acceptSent = some a) :
    MsgFundingPhaseEvent.sendAccept a ∈ es := by
  revert h
  induction ht with
  | nil =>
    intro h
    simp [MsgFundingPhase.initial] at h
  | snoc ht hstep ih =>
    rename_i s s' es e
    intro h
    cases e with
    | sendOpen m₀ =>
      have hex := msgStep_sendOpen_exact hstep
      rw [hex.2.2.1] at h
      exact List.mem_append.mpr (Or.inl (ih h))
    | recvOpen m₀ =>
      have hex := msgStep_recvOpen_exact hstep
      rw [hex.2.2.1] at h
      exact List.mem_append.mpr (Or.inl (ih h))
    | sendAccept a₀ =>
      have hex := msgStep_sendAccept_exact hstep
      rw [hex.1] at h
      injection h with ha
      subst ha
      exact List.mem_append.mpr (Or.inr (by simp))
    | recvAccept a₀ =>
      have hex := msgStep_recvAccept_exact hstep
      rw [hex.2.2.2.1] at h
      exact List.mem_append.mpr (Or.inl (ih h))

/-- A stored received `accept_channel` occurred as a `recvAccept` event. -/
theorem msgTrace_acceptReceived_mem {s : MsgFundingPhase}
    {es : List MsgFundingPhaseEvent} (ht : MsgTrace s es) {a : AcceptChannel}
    (h : s.acceptReceived = some a) :
    MsgFundingPhaseEvent.recvAccept a ∈ es := by
  revert h
  induction ht with
  | nil =>
    intro h
    simp [MsgFundingPhase.initial] at h
  | snoc ht hstep ih =>
    rename_i s s' es e
    intro h
    cases e with
    | sendOpen m₀ =>
      have hex := msgStep_sendOpen_exact hstep
      rw [hex.2.2.2] at h
      exact List.mem_append.mpr (Or.inl (ih h))
    | recvOpen m₀ =>
      have hex := msgStep_recvOpen_exact hstep
      rw [hex.2.2.2] at h
      exact List.mem_append.mpr (Or.inl (ih h))
    | sendAccept a₀ =>
      have hex := msgStep_sendAccept_exact hstep
      rw [hex.2.2.2.1] at h
      exact List.mem_append.mpr (Or.inl (ih h))
    | recvAccept a₀ =>
      have hex := msgStep_recvAccept_exact hstep
      rw [hex.1] at h
      injection h with ha
      subst ha
      exact List.mem_append.mpr (Or.inr (by simp))

/-! ### Strict event ordering -/

/-- `e₁` occurs strictly before `e₂` in the event history. -/
def OccursBefore (e₁ e₂ : MsgFundingPhaseEvent)
    (es : List MsgFundingPhaseEvent) : Prop :=
  ∃ pre mid post : List MsgFundingPhaseEvent,
    es = pre ++ [e₁] ++ mid ++ [e₂] ++ post

theorem occursBefore_append_right {e₁ e₂ : MsgFundingPhaseEvent}
    {es t : List MsgFundingPhaseEvent} (h : OccursBefore e₁ e₂ es) :
    OccursBefore e₁ e₂ (es ++ t) := by
  obtain ⟨pre, mid, post, rfl⟩ := h
  exact ⟨pre, mid, post ++ t, by simp [List.append_assoc]⟩

/-- Peel a membership decomposition into a strict-before relation when the
later event is appended at the end. -/
theorem occursBefore_of_mem_append_self {e₁ e₂ : MsgFundingPhaseEvent}
    {es : List MsgFundingPhaseEvent} (h : e₁ ∈ es) :
    OccursBefore e₁ e₂ (es ++ [e₂]) := by
  induction es with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨[], xs, [], by simp⟩
    · obtain ⟨pre, mid, post, hpre⟩ := ih h
      exact ⟨x :: pre, mid, post, by simp [hpre]⟩

/-- **Ordering in the history: a sent `accept_channel` is preceded by the
receipt of the `open_channel` it answers.** -/
theorem msgTrace_sendAccept_prior_recvOpen {s : MsgFundingPhase}
    {es : List MsgFundingPhaseEvent} (ht : MsgTrace s es) {a : AcceptChannel}
    (h : MsgFundingPhaseEvent.sendAccept a ∈ es) :
    ∃ m : OpenChannelMsg,
      OccursBefore (MsgFundingPhaseEvent.recvOpen m)
        (MsgFundingPhaseEvent.sendAccept a) es := by
  revert h
  induction ht with
  | nil =>
    intro h
    simp at h
  | snoc ht hstep ih =>
    rename_i s s' es e
    intro h
    cases e with
    | sendOpen m₀ =>
      rw [List.mem_append, List.mem_singleton] at h
      rcases h with h | h
      · obtain ⟨m, hm⟩ := ih h
        exact ⟨m, occursBefore_append_right hm⟩
      · simp at h
    | recvOpen m₀ =>
      rw [List.mem_append, List.mem_singleton] at h
      rcases h with h | h
      · obtain ⟨m, hm⟩ := ih h
        exact ⟨m, occursBefore_append_right hm⟩
      · simp at h
    | sendAccept a₀ =>
      rw [List.mem_append, List.mem_singleton] at h
      rcases h with h | h
      · obtain ⟨m, hm⟩ := ih h
        exact ⟨m, occursBefore_append_right hm⟩
      · injection h with ha
        subst ha
        obtain ⟨m, hm⟩ := sendAccept_requires_openReceivedMsg hstep
        have hmem := msgTrace_openReceived_mem ht hm
        exact ⟨m, occursBefore_of_mem_append_self
          (e₂ := MsgFundingPhaseEvent.sendAccept a) hmem⟩
    | recvAccept a₀ =>
      rw [List.mem_append, List.mem_singleton] at h
      rcases h with h | h
      · obtain ⟨m, hm⟩ := ih h
        exact ⟨m, occursBefore_append_right hm⟩
      · simp at h

/-- **Ordering in the history: a received `accept_channel` is preceded by the
send of the `open_channel` it answers.** -/
theorem msgTrace_recvAccept_prior_sendOpen {s : MsgFundingPhase}
    {es : List MsgFundingPhaseEvent} (ht : MsgTrace s es) {a : AcceptChannel}
    (h : MsgFundingPhaseEvent.recvAccept a ∈ es) :
    ∃ m : OpenChannelMsg,
      OccursBefore (MsgFundingPhaseEvent.sendOpen m)
        (MsgFundingPhaseEvent.recvAccept a) es := by
  revert h
  induction ht with
  | nil =>
    intro h
    simp at h
  | snoc ht hstep ih =>
    rename_i s s' es e
    intro h
    cases e with
    | sendOpen m₀ =>
      rw [List.mem_append, List.mem_singleton] at h
      rcases h with h | h
      · obtain ⟨m, hm⟩ := ih h
        exact ⟨m, occursBefore_append_right hm⟩
      · simp at h
    | recvOpen m₀ =>
      rw [List.mem_append, List.mem_singleton] at h
      rcases h with h | h
      · obtain ⟨m, hm⟩ := ih h
        exact ⟨m, occursBefore_append_right hm⟩
      · simp at h
    | sendAccept a₀ =>
      rw [List.mem_append, List.mem_singleton] at h
      rcases h with h | h
      · obtain ⟨m, hm⟩ := ih h
        exact ⟨m, occursBefore_append_right hm⟩
      · simp at h
    | recvAccept a₀ =>
      rw [List.mem_append, List.mem_singleton] at h
      rcases h with h | h
      · obtain ⟨m, hm⟩ := ih h
        exact ⟨m, occursBefore_append_right hm⟩
      · injection h with ha
        subst ha
        obtain ⟨m, hm⟩ := recvAccept_requires_openSentMsg hstep
        have hmem := msgTrace_openSent_mem ht hm
        exact ⟨m, occursBefore_of_mem_append_self
          (e₂ := MsgFundingPhaseEvent.recvAccept a) hmem⟩

/-- **Exact ordering at the transition.**  If a trace reaches `s` and `s` then
permits `sendAccept a`, the exact message in `s.openReceived` occurred earlier
in the same history and strictly precedes the new accept event. -/
theorem msgTrace_sendAccept_exact_provenance {s s' : MsgFundingPhase}
    {es : List MsgFundingPhaseEvent} (ht : MsgTrace s es)
    {a : AcceptChannel} (h : msgStep s (.sendAccept a) = some s') :
    ∃ m : OpenChannelMsg,
      s.openReceived = some m ∧
      MsgFundingPhaseEvent.recvOpen m ∈ es ∧
      OccursBefore (MsgFundingPhaseEvent.recvOpen m)
        (MsgFundingPhaseEvent.sendAccept a) (es ++ [MsgFundingPhaseEvent.sendAccept a]) := by
  obtain ⟨m, hm⟩ := sendAccept_requires_openReceivedMsg h
  have hmem := msgTrace_openReceived_mem ht hm
  exact ⟨m, hm, hmem, occursBefore_of_mem_append_self hmem⟩

/-- **Exact ordering at the transition, opener side.** -/
theorem msgTrace_recvAccept_exact_provenance {s s' : MsgFundingPhase}
    {es : List MsgFundingPhaseEvent} (ht : MsgTrace s es)
    {a : AcceptChannel} (h : msgStep s (.recvAccept a) = some s') :
    ∃ m : OpenChannelMsg,
      s.openSent = some m ∧
      MsgFundingPhaseEvent.sendOpen m ∈ es ∧
      OccursBefore (MsgFundingPhaseEvent.sendOpen m)
        (MsgFundingPhaseEvent.recvAccept a) (es ++ [MsgFundingPhaseEvent.recvAccept a]) := by
  obtain ⟨m, hm⟩ := recvAccept_requires_openSentMsg h
  have hmem := msgTrace_openSent_mem ht hm
  exact ⟨m, hm, hmem, occursBefore_of_mem_append_self hmem⟩

/-! ### Headline provenance theorems -/

/-- **Strongest history/provenance theorem.**  Every reachable message-phase
state has a concrete event history; every stored payload occurred in that
history as the corresponding event; and every accept message was preceded by
the open message it answers. -/
theorem msgReachable_provenance {s : MsgFundingPhase} (hr : MsgReachable s) :
    ∃ es : List MsgFundingPhaseEvent,
      MsgTrace s es ∧
      (∀ m : OpenChannelMsg,
        s.openSent = some m → MsgFundingPhaseEvent.sendOpen m ∈ es) ∧
      (∀ m : OpenChannelMsg,
        s.openReceived = some m → MsgFundingPhaseEvent.recvOpen m ∈ es) ∧
      (∀ a : AcceptChannel,
        s.acceptSent = some a → MsgFundingPhaseEvent.sendAccept a ∈ es) ∧
      (∀ a : AcceptChannel,
        s.acceptReceived = some a → MsgFundingPhaseEvent.recvAccept a ∈ es) ∧
      (∀ a : AcceptChannel,
        MsgFundingPhaseEvent.sendAccept a ∈ es →
          ∃ m : OpenChannelMsg,
            OccursBefore (MsgFundingPhaseEvent.recvOpen m)
              (MsgFundingPhaseEvent.sendAccept a) es) ∧
      (∀ a : AcceptChannel,
        MsgFundingPhaseEvent.recvAccept a ∈ es →
          ∃ m : OpenChannelMsg,
            OccursBefore (MsgFundingPhaseEvent.sendOpen m)
              (MsgFundingPhaseEvent.recvAccept a) es) := by
  obtain ⟨es, ht⟩ := msgReachable_has_trace hr
  exact ⟨es, ht,
    fun m hm => msgTrace_openSent_mem ht hm,
    fun m hm => msgTrace_openReceived_mem ht hm,
    fun a ha => msgTrace_acceptSent_mem ht ha,
    fun a ha => msgTrace_acceptReceived_mem ht ha,
    fun a ha => msgTrace_sendAccept_prior_recvOpen ht ha,
    fun a ha => msgTrace_recvAccept_prior_sendOpen ht ha⟩

/-- **Exact-message provenance of the opener's negotiation.**  Under
reachability, the negotiation exposed by the opener comes from the exact
`open_channel` it sent and the exact `accept_channel` it received, and both
messages occurred in the history. -/
theorem msgReachable_opener_provenance {s : MsgFundingPhase}
    (hr : MsgReachable s) {n : LnLean.Bitcoin.FundingNegotiation}
    (h : s.openerNegotiation? = some n) :
    ∃ (m : OpenChannelMsg) (a : AcceptChannel)
        (es : List MsgFundingPhaseEvent),
      s.openSent = some m ∧ s.acceptReceived = some a ∧
      n = m.toOpenChannel.toFundingNegotiation a ∧
      n.localFundingKey = m.fundingPubKey ∧
      n.remoteFundingKey = a.fundingPubKey ∧
      MsgTrace s es ∧
      MsgFundingPhaseEvent.sendOpen m ∈ es ∧
      MsgFundingPhaseEvent.recvAccept a ∈ es := by
  unfold MsgFundingPhase.openerNegotiation? at h
  cases hs : s.openSent with
  | none => simp [hs] at h
  | some m =>
    cases ha : s.acceptReceived with
    | none => simp [hs, ha] at h
    | some a =>
      simp only [hs, ha] at h
      injection h with hn
      subst hn
      obtain ⟨es, ht⟩ := msgReachable_has_trace hr
      exact ⟨m, a, es, rfl, rfl, rfl, rfl, rfl, ht,
        msgTrace_openSent_mem ht hs,
        msgTrace_acceptReceived_mem ht ha⟩

/-- **Exact-message provenance of the acceptor's negotiation.** -/
theorem msgReachable_acceptor_provenance {s : MsgFundingPhase}
    (hr : MsgReachable s) {n : LnLean.Bitcoin.FundingNegotiation}
    (h : s.acceptorNegotiation? = some n) :
    ∃ (m : OpenChannelMsg) (a : AcceptChannel)
        (es : List MsgFundingPhaseEvent),
      s.openReceived = some m ∧ s.acceptSent = some a ∧
      n = m.toOpenChannel.toFundingNegotiation a ∧
      n.localFundingKey = m.fundingPubKey ∧
      n.remoteFundingKey = a.fundingPubKey ∧
      MsgTrace s es ∧
      MsgFundingPhaseEvent.recvOpen m ∈ es ∧
      MsgFundingPhaseEvent.sendAccept a ∈ es := by
  unfold MsgFundingPhase.acceptorNegotiation? at h
  cases hs : s.openReceived with
  | none => simp [hs] at h
  | some m =>
    cases ha : s.acceptSent with
    | none => simp [hs, ha] at h
    | some a =>
      simp only [hs, ha] at h
      injection h with hn
      subst hn
      obtain ⟨es, ht⟩ := msgReachable_has_trace hr
      exact ⟨m, a, es, rfl, rfl, rfl, rfl, rfl, ht,
        msgTrace_openReceived_mem ht hs,
        msgTrace_acceptSent_mem ht ha⟩

/-- **Exact payload determined by the existing phase.**  Equal erased phases
and stored received messages force the exact `open_channel` payloads to be
equal: the bridge loses nothing about the message. -/
theorem erase_openReceived_injective {s t : MsgFundingPhase}
    (h : s.erase = t.erase) {m n : OpenChannelMsg}
    (hs : s.openReceived = some m) (ht : t.openReceived = some n) : m = n := by
  have hmap : s.erase.openReceived = t.erase.openReceived := by rw [h]
  simp [MsgFundingPhase.erase, hs, ht] at hmap
  exact OpenChannelMsg.toOpenChannel_injective hmap

/-- The same exactness for the sent `open_channel` payload. -/
theorem erase_openSent_injective {s t : MsgFundingPhase}
    (h : s.erase = t.erase) {m n : OpenChannelMsg}
    (hs : s.openSent = some m) (ht : t.openSent = some n) : m = n := by
  have hmap : s.erase.openSent = t.erase.openSent := by rw [h]
  simp [MsgFundingPhase.erase, hs, ht] at hmap
  exact OpenChannelMsg.toOpenChannel_injective hmap

/-! ## Transport attribution: retained caveat -/

/-- A received `open_channel` with the transport's claimed sender.  The sender
is not part of the wire payload; it is attached by the transport, which is the
layer that must authenticate it. -/
structure ReceivedOpenChannelMsg where
  sender : PeerIdentity
  message : OpenChannelMsg

/-- **Scope boundary, mechanized.**  One exact `open_channel` payload is
compatible with two distinct claimed senders.  Payload equality therefore does
not establish attribution; `msgAttributed_key_in_script` has to take
`OpenChannelAttributed` as an explicit hypothesis. -/
theorem same_msg_distinct_senders :
    ∃ r₁ r₂ : ReceivedOpenChannelMsg,
      r₁.message = r₂.message ∧ r₁.sender ≠ r₂.sender := by
  let k₀ : PubKey := ⟨ByteArray.empty⟩
  let k₁ : PubKey := ⟨ByteArray.empty.push 0x01⟩
  let m : OpenChannelMsg :=
    { temporaryChannelId := ⟨ByteArray.empty⟩
      fundingSatoshis := 0
      pushMsat := ⟨0⟩
      fundingPubKey := k₀ }
  refine ⟨⟨⟨k₀⟩, m⟩, ⟨⟨k₁⟩, m⟩, rfl, ?_⟩
  intro h
  have hk : k₀ = k₁ := congrArg PeerIdentity.key h
  have hb : (ByteArray.empty : ByteArray) = ByteArray.empty.push 0x01 :=
    congrArg PubKey.bytes hk
  have hsz := congrArg ByteArray.size hb
  simp at hsz

/-- **Conditional attribution at the message boundary.**  If the transport
attribution hypothesis identifies the sender with `open_channel.funding_pubkey`,
then that authenticated key is exactly the local funding key of the joint
construction and occurs in the witness script.  This composes
`FundingAuthTargets.attributed_key_in_script` with the message projection; no
signature check is added. -/
theorem msgAttributed_key_in_script (H : ByteArray → ByteArray)
    (sender : PeerIdentity) (m : OpenChannelMsg) (a : AcceptChannel)
    (hattr : OpenChannelAttributed sender m.toOpenChannel) :
    sender.key = (m.toOpenChannel.toFundingNegotiation a).localFundingKey ∧
      KeyInScript
        (m.toOpenChannel.toFundingParams H a).witnessScript.bytes sender.key :=
  attributed_key_in_script H sender m.toOpenChannel a hattr

/-- The same conditional attribution in terms of the wire-record projections:
the authenticated key is the one carried in the `funding_pubkey` field. -/
theorem msgAttributed_key_eq_fundingPubKey
    (sender : PeerIdentity) (m : OpenChannelMsg)
    (hattr : OpenChannelAttributed sender m.toOpenChannel) :
    sender.key = m.fundingPubKey := by
  rw [show m.fundingPubKey = m.toOpenChannel.fundingPubKey from rfl]
  exact hattr

/-! ## Non-vacuity: a complete exchange at the message layer -/

private def demoMsg (key : PubKey) : OpenChannelMsg :=
  { temporaryChannelId := ⟨ByteArray.empty⟩
    fundingSatoshis := 0
    pushMsat := ⟨0⟩
    fundingPubKey := key }

private def demoAccept (remote : PubKey) : AcceptChannel :=
  { temporaryChannelId := ⟨ByteArray.empty⟩
    dustLimitSatoshis := 0
    maxHtlcValueInFlightMsat := 0
    channelReserveSatoshis := 0
    htlcMinimumMsat := 0
    minimumDepth := 0
    toSelfDelay := 0
    maxAcceptedHtlcs := 0
    fundingPubKey := remote
    revocationBasepoint := remote
    paymentBasepoint := remote
    delayedPaymentBasepoint := remote
    htlcBasepoint := remote
    firstPerCommitmentPoint := remote }

/-- **The message layer is non-vacuous.**  A complete
`open_channel`/`accept_channel` exchange is reachable, both endpoints expose the
same negotiation, and the exact sent/received payloads are stored. -/
theorem msgReachable_negotiation_witness :
    ∃ (s : MsgFundingPhase) (m : OpenChannelMsg),
      MsgReachable s ∧
      s.openSent = some m ∧
      s.openReceived = some m ∧
      s.openerNegotiation?.isSome = true ∧
      s.acceptorNegotiation?.isSome = true ∧
      s.openerNegotiation? = s.acceptorNegotiation? := by
  let m : OpenChannelMsg := demoMsg ⟨ByteArray.empty⟩
  let a : AcceptChannel := demoAccept ⟨ByteArray.empty⟩
  let s0 : MsgFundingPhase := MsgFundingPhase.initial
  let s1 : MsgFundingPhase :=
    { openSent := some m, openReceived := none,
      acceptSent := none, acceptReceived := none }
  let s2 : MsgFundingPhase :=
    { openSent := some m, openReceived := some m,
      acceptSent := none, acceptReceived := none }
  let s3 : MsgFundingPhase :=
    { openSent := some m, openReceived := some m,
      acceptSent := some a, acceptReceived := none }
  let s4 : MsgFundingPhase :=
    { openSent := some m, openReceived := some m,
      acceptSent := some a, acceptReceived := some a }
  have h1 : msgStep s0 (.sendOpen m) = some s1 := by
    simp [msgStep, s0, s1, MsgFundingPhase.initial, MsgFundingPhase.canSendOpen]
  have h2 : msgStep s1 (.recvOpen m) = some s2 := by
    simp [msgStep, s1, s2, MsgFundingPhase.canRecvOpen]
  have h3 : msgStep s2 (.sendAccept a) = some s3 := by
    simp [msgStep, s2, s3, MsgFundingPhase.canSendAccept]
  have h4 : msgStep s3 (.recvAccept a) = some s4 := by
    simp [msgStep, s3, s4, MsgFundingPhase.canRecvAccept]
  refine ⟨s4, m, ?_, rfl, rfl, ?_, ?_, ?_⟩
  · exact MsgReachable.step _
      (MsgReachable.step _ (MsgReachable.step _
        (MsgReachable.step _ MsgReachable.initial h1) h2) h3) h4
  · simp [s4, MsgFundingPhase.openerNegotiation?]
  · simp [s4, MsgFundingPhase.acceptorNegotiation?]
  · simp [s4, MsgFundingPhase.openerNegotiation?,
      MsgFundingPhase.acceptorNegotiation?]

end LnLean.Proofs.WaveH.H16
