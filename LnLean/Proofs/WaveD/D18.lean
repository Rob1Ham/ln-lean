import LnLean.Protocol.Handshake
import LnLean.Protocol.Laws
import LnLean.Protocol.Messages
import LnLean.Protocol.Peer
import LnLean.Proofs.Protocol.HandshakeProps

/-!
# D18 — normal operation requires both `channel_ready` messages

## English claim

BOLT 2 §"The `channel_ready` Message" says that a channel enters normal
operation only after **both** endpoints have sent `channel_ready`.  The
wave-A model records this as `HandshakeState.ready s`, defined as
`s.channelReadySent && s.channelReadyReceived`.

This module proves the gate in four complementary forms:

1. **Definitional characterization.**  `ready s = true` iff both flags are
   set; either flag alone is not enough.  This is the content of the catalog
   target `LnLean.Protocol.Handshake.channel_ready_gate`.
2. **Reachability prerequisites.**  In every reachable state, being ready
   implies `funding_signed` (sent or received), an `accept_channel` exchange,
   and both `init` messages.  These use the wave-A ordering invariant plus the
   stronger `OrderInv` from `LnLean.Proofs.Protocol.HandshakeProps`.
3. **Per-step gating.**  A single transition can set at most one of the two
   `channel_ready` flags.  Hence a transition that *newly* makes the channel
   ready must be a `sendChannelReady` or `recvChannelReady` event, and in that
   transition the opposite flag was already true.
4. **Trace gating.**  Along any concrete run (`runEvents`) from
   `HandshakeState.initial` that ends in a ready state, the event list
   contains both a `sendChannelReady` and a `recvChannelReady` event.

The literal phrase "normal operation" is represented by the model's explicit
`ready` predicate.  The peer module does **not** additionally gate update or
commitment messages on `ready` (`LnLean/Protocol/Peer.lean`, `receive`); that
is a documented model boundary, not something this module silently assumes.
See `agents/reports/D18.md`.

## BOLT anchor

* BOLT 2 §"The `channel_ready` Message"
  (`refs/bolts/02-peer-protocol.md:1046-1136`): "the channel is not
  operational until both sides have sent `channel_ready`".
* rust-lightning `lightning/src/ln/channelmanager.rs:17614` (catalog anchor):
  the `channel_ready` handling that moves the channel into normal operation.

## What is NOT modelled

* `ready` is a pair of local flags, not a two-party joint state; the model
  has no second endpoint, so "both" means "sent and received on this
  connection".
* `Peer.receive` accepts channel messages (e.g. `commitment_signed`) without
  consulting `ready`, so the operational-message gate is not enforced at the
  peer layer.
* Timeouts, retransmission, and reconnection are out of scope here.
-/

namespace LnLean.Proofs.WaveD.D18

set_option autoImplicit false

open LnLean LnLean.Protocol

-- OBLIGATION: LN-WD-D18

/-! ## 1. The definitional gate -/

/-- **The catalog gate.**  A channel is in normal operation exactly when both
`channel_ready` messages have been exchanged.  There is no state in which
`ready` holds with only one direction. -/
theorem waveD_d18_ready_iff_both (s : HandshakeState) :
    s.ready = true ↔ s.channelReadySent = true ∧ s.channelReadyReceived = true :=
  HandshakeState.ready_iff s

/-- Normal operation implies the outbound `channel_ready` was sent. -/
theorem waveD_d18_ready_implies_sent {s : HandshakeState} (h : s.ready = true) :
    s.channelReadySent = true :=
  ((HandshakeState.ready_iff s).1 h).1

/-- Normal operation implies the inbound `channel_ready` was received. -/
theorem waveD_d18_ready_implies_received {s : HandshakeState} (h : s.ready = true) :
    s.channelReadyReceived = true :=
  ((HandshakeState.ready_iff s).1 h).2

/-- Both `channel_ready` messages suffice for normal operation. -/
theorem waveD_d18_ready_of_both {s : HandshakeState}
    (hs : s.channelReadySent = true) (hr : s.channelReadyReceived = true) :
    s.ready = true :=
  (HandshakeState.ready_iff s).2 ⟨hs, hr⟩

/-- Sending `channel_ready` alone does not enter normal operation: without
the peer's message the channel is not ready. -/
theorem waveD_d18_not_ready_of_sent_only {s : HandshakeState}
    (hs : s.channelReadySent = true) (hr : s.channelReadyReceived = false) :
    s.ready = false := by
  simp [HandshakeState.ready, hs, hr]

/-- Receiving `channel_ready` alone does not enter normal operation. -/
theorem waveD_d18_not_ready_of_received_only {s : HandshakeState}
    (hr : s.channelReadyReceived = true) (hs : s.channelReadySent = false) :
    s.ready = false := by
  simp [HandshakeState.ready, hr, hs]

/-! ## 2. Reachability prerequisites -/

/-- In a reachable ready state, one of the two `funding_signed` directions has
already happened.  A `channel_ready` cannot precede `funding_signed`. -/
theorem waveD_d18_reachable_ready_implies_fundingSigned {s : HandshakeState}
    (h : Reachable s) (hr : s.ready = true) :
    s.fundingSignedSent = true ∨ s.fundingSignedReceived = true :=
  channel_ready_not_before_funding_signed h (Or.inl (waveD_d18_ready_implies_sent hr))

/-- In a reachable ready state, an `accept_channel` has been sent or received.
This follows the full ordering chain
`ready → funding_signed → funding_created → accept_channel`. -/
theorem waveD_d18_reachable_ready_implies_accept {s : HandshakeState}
    (h : Reachable s) (hr : s.ready = true) :
    s.acceptSent = true ∨ s.acceptReceived = true := by
  have ho := reachable_orderInv h
  rcases waveD_d18_reachable_ready_implies_fundingSigned h hr with hfs | hfs
  · exact Or.inl (ho.2.2.1 (ho.2.2.2.1 hfs))
  · exact Or.inr (ho.2.1 (ho.2.2.2.2.1 hfs))

/-- In a reachable ready state, both `init` messages have been exchanged. -/
theorem waveD_d18_reachable_ready_implies_inited {s : HandshakeState}
    (h : Reachable s) (hr : s.ready = true) :
    s.initSent = true ∧ s.initReceived = true :=
  (reachable_orderInv h).1 (waveD_d18_reachable_ready_implies_accept h hr)

/-! ## 3. Per-step gating

A transition changes at most one of the two flags.  Therefore normal
operation cannot appear from a single non-`channel_ready` event, and when it
does appear it is the *second* `channel_ready` exchange. -/

/-- Only the `sendChannelReady` event can turn the outbound flag from `false`
to `true`. -/
theorem waveD_d18_sent_intro {s s' : HandshakeState} {e : HandshakeEvent}
    (h : handshakeStep s e = some s')
    (hfalse : s.channelReadySent = false) (htrue : s'.channelReadySent = true) :
    e = .sendChannelReady := by
  cases e <;> simp only [handshakeStep] at h <;>
    (try split at h) <;>
    (try rw [Option.some.injEq] at h) <;>
    (try rw [← h] at htrue) <;>
    simp_all

/-- Only the `recvChannelReady` event can turn the inbound flag from `false`
to `true`. -/
theorem waveD_d18_recv_intro {s s' : HandshakeState} {e : HandshakeEvent}
    (h : handshakeStep s e = some s')
    (hfalse : s.channelReadyReceived = false) (htrue : s'.channelReadyReceived = true) :
    e = .recvChannelReady := by
  cases e <;> simp only [handshakeStep] at h <;>
    (try split at h) <;>
    (try rw [Option.some.injEq] at h) <;>
    (try rw [← h] at htrue) <;>
    simp_all

/-- One successful transition sets at most one `channel_ready` flag: a newly
true flag was either already true before the step or is the flag written by
that exact event. -/
theorem waveD_d18_step_ready_flags {s s' : HandshakeState} {e : HandshakeEvent}
    (h : handshakeStep s e = some s') :
    (s'.channelReadySent = true →
        s.channelReadySent = true ∨ e = .sendChannelReady) ∧
    (s'.channelReadyReceived = true →
        s.channelReadyReceived = true ∨ e = .recvChannelReady) := by
  constructor
  · intro hs'
    by_cases hprev : s.channelReadySent = true
    · exact Or.inl hprev
    · have hf : s.channelReadySent = false := by
        cases hb : s.channelReadySent with
        | false => rfl
        | true => simp [hb] at hprev
      exact Or.inr (waveD_d18_sent_intro h hf hs')
  · intro hr'
    by_cases hprev : s.channelReadyReceived = true
    · exact Or.inl hprev
    · have hf : s.channelReadyReceived = false := by
        cases hb : s.channelReadyReceived with
        | false => rfl
        | true => simp [hb] at hprev
      exact Or.inr (waveD_d18_recv_intro h hf hr')

/-- A transition that newly reaches normal operation must be a
`channel_ready` send or receive.  No other handshake event can flip the
`ready` bit. -/
theorem waveD_d18_ready_introduced_only_by_channelReady
    {s s' : HandshakeState} {e : HandshakeEvent}
    (h : handshakeStep s e = some s') (hpre : s.ready = false)
    (hpost : s'.ready = true) :
    e = .sendChannelReady ∨ e = .recvChannelReady := by
  have hb := (HandshakeState.ready_iff s').1 hpost
  rcases (waveD_d18_step_ready_flags h).1 hb.1 with hsent | he
  · rcases (waveD_d18_step_ready_flags h).2 hb.2 with hrecv | he
    · have : s.ready = true := (HandshakeState.ready_iff s).2 ⟨hsent, hrecv⟩
      simp [this] at hpre
    · exact Or.inr he
  · exact Or.inl he

/-- **Entry by sending.**  If a `sendChannelReady` step makes the channel
ready, then the peer's `channel_ready` had already been received and the
local message had not yet been sent. -/
theorem waveD_d18_ready_entry_send {s s' : HandshakeState}
    (h : handshakeStep s .sendChannelReady = some s') (hpost : s'.ready = true) :
    s.channelReadyReceived = true ∧ s.channelReadySent = false := by
  by_cases hg : s.canSendChannelReady
  · simp [handshakeStep, hg] at h
    rcases h with ⟨_, hs⟩
    subst hs
    refine ⟨?_, hg.2.2⟩
    exact ((HandshakeState.ready_iff _).1 hpost).2
  · simp [handshakeStep, hg] at h

/-- **Entry by receiving.**  If a `recvChannelReady` step makes the channel
ready, then the local `channel_ready` had already been sent and the peer's
message was not yet received. -/
theorem waveD_d18_ready_entry_recv {s s' : HandshakeState}
    (h : handshakeStep s .recvChannelReady = some s') (hpost : s'.ready = true) :
    s.channelReadySent = true ∧ s.channelReadyReceived = false := by
  by_cases hg : s.canRecvChannelReady
  · simp [handshakeStep, hg] at h
    rcases h with ⟨_, hs⟩
    subst hs
    refine ⟨?_, hg.2.2⟩
    exact ((HandshakeState.ready_iff _).1 hpost).1
  · simp [handshakeStep, hg] at h

/-! ## 4. Trace gating

`runEvents` executes a concrete list of handshake events.  If the resulting
state is ready, both `channel_ready` events must occur in the list. -/

/-- Execute a list of handshake events, stopping at the first refused event. -/
def runEvents : HandshakeState → List HandshakeEvent → Option HandshakeState
  | s, [] => some s
  | s, e :: es => (handshakeStep s e).bind (fun s' => runEvents s' es)

/-- `Runs es s` means the event list `es` drives `HandshakeState.initial` to
`s`. -/
def Runs (es : List HandshakeEvent) (s : HandshakeState) : Prop :=
  runEvents HandshakeState.initial es = some s

/-- If a run starts with the outbound flag false and ends with it true, then
a `sendChannelReady` event occurs in the run. -/
theorem waveD_d18_sendEvent_mem_of_runEvents {es : List HandshakeEvent}
    {s s' : HandshakeState} (h : runEvents s es = some s')
    (h0 : s.channelReadySent = false) (h1 : s'.channelReadySent = true) :
    HandshakeEvent.sendChannelReady ∈ es := by
  induction es generalizing s with
  | nil =>
      simp [runEvents] at h
      subst h
      simp_all
  | cons e es ih =>
      simp only [runEvents] at h
      cases hstep : handshakeStep s e with
      | none => simp [hstep] at h
      | some s1 =>
          simp [hstep] at h
          by_cases hprev : s1.channelReadySent = true
          · have he : e = .sendChannelReady := waveD_d18_sent_intro hstep h0 hprev
            subst he
            simp
          · have hf : s1.channelReadySent = false := by
              cases hb : s1.channelReadySent with
              | false => rfl
              | true => simp [hb] at hprev
            have hmem : HandshakeEvent.sendChannelReady ∈ es := ih h hf
            simp only [List.mem_cons]
            exact Or.inr hmem

/-- If a run starts with the inbound flag false and ends with it true, then a
`recvChannelReady` event occurs in the run. -/
theorem waveD_d18_recvEvent_mem_of_runEvents {es : List HandshakeEvent}
    {s s' : HandshakeState} (h : runEvents s es = some s')
    (h0 : s.channelReadyReceived = false) (h1 : s'.channelReadyReceived = true) :
    HandshakeEvent.recvChannelReady ∈ es := by
  induction es generalizing s with
  | nil =>
      simp [runEvents] at h
      subst h
      simp_all
  | cons e es ih =>
      simp only [runEvents] at h
      cases hstep : handshakeStep s e with
      | none => simp [hstep] at h
      | some s1 =>
          simp [hstep] at h
          by_cases hprev : s1.channelReadyReceived = true
          · have he : e = .recvChannelReady := waveD_d18_recv_intro hstep h0 hprev
            subst he
            simp
          · have hf : s1.channelReadyReceived = false := by
              cases hb : s1.channelReadyReceived with
              | false => rfl
              | true => simp [hb] at hprev
            have hmem : HandshakeEvent.recvChannelReady ∈ es := ih h hf
            simp only [List.mem_cons]
            exact Or.inr hmem

/-- **Trace form of the gate.**  Any run from the initial state that ends in
normal operation contains both a `sendChannelReady` and a `recvChannelReady`
event.  This is the strongest "both messages are necessary" statement
available in the model: the ready bit cannot be reached with fewer than the
two events. -/
theorem waveD_d18_ready_trace_has_both_events {es : List HandshakeEvent}
    {s : HandshakeState} (h : Runs es s) (hr : s.ready = true) :
    HandshakeEvent.sendChannelReady ∈ es ∧ HandshakeEvent.recvChannelReady ∈ es := by
  refine ⟨?_, ?_⟩
  · exact waveD_d18_sendEvent_mem_of_runEvents h rfl (waveD_d18_ready_implies_sent hr)
  · exact waveD_d18_recvEvent_mem_of_runEvents h rfl (waveD_d18_ready_implies_received hr)

/-! ## 5. Catalog alias

The catalog target is `LnLean.Protocol.Handshake.channel_ready_gate`.  The
model module `LnLean.Protocol.Handshake` cannot be edited in Wave D, so the
target is supplied here, in the model namespace, as the clean iff statement.
-/

end LnLean.Proofs.WaveD.D18

/-! The catalog target lives in the model namespace, next to
`HandshakeState.ready`, so the traceability anchor resolves exactly as
`LnLean.Protocol.Handshake.channel_ready_gate`. -/
namespace LnLean.Protocol.Handshake

/-- **LN-PR-002 / `channel_ready_gate`.**  The channel is in normal operation
only after both `channel_ready` messages: `ready` holds exactly when the
outbound and inbound `channel_ready` flags are both set. -/
theorem channel_ready_gate (s : HandshakeState) :
    s.ready = true ↔ s.channelReadySent = true ∧ s.channelReadyReceived = true :=
  HandshakeState.ready_iff s

end LnLean.Protocol.Handshake
