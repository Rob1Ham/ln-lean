/-
# H20 — the received `accept_channel` payload on a local `HandshakeState`
extension (PR-01)

**Catalog issue.**  `PR-01` (P1): `FundingSigningLaw` and `KeyBinding` are
hypotheses, and `HandshakeState` records only the *boolean* milestone
`acceptReceived`.  The BOLT 2 `accept_channel` message payload itself — in
particular `funding_pubkey` — is not stored anywhere in the handshake state, so
`KeyModelTargets.AdvertisesKey` has to be supplied as an external hypothesis
about a message the state machine never retained.

**Result of this module.**  A *local, additive* extension of `HandshakeState`
carries the received payload, without editing `LnLean/Protocol/Handshake.lean`
or any other shared file:

1. `HandshakeStateExt` wraps the unchanged `HandshakeState` in `base` and adds
   `acceptReceived? : Option AcceptChannel` (default `none`).
2. `ExtEvent` is the extended event type: every base `HandshakeEvent`, plus the
   payload-carrying `recvAccept a`.  The payload-free
   `ofEvent .recvAcceptChannel` form is deliberately **not** enabled, so a state
   can never record `acceptReceived = true` without also recording which
   `accept_channel` payload caused it.
3. `step` is the extension transition.  `step_ofEvent_base` and
   `step_recvAccept_base` prove that its `base` projection is exactly the
   unchanged `handshakeStep`; `step_recvAccept_acceptReceived?` proves that a
   permitted `recvAccept a` sets `acceptReceived? = some a`;
   `step_recvAccept_acceptReceived` re-derives the existing
   `acceptReceived_of_recvAcceptChannel` from the extension.
4. `AcceptLinked s` is the exact relation to the existing boolean flag:
   `s.base.acceptReceived = true ↔ ∃ a, s.acceptReceived? = some a`.  It holds
   at `initial` and is preserved by every extension step, hence at every
   `ReachableExt` state.
5. `ReachableExt` projects to the existing `Reachable` (`reachableExt_base`), so
   every wave-1 handshake law (`Reachable` invariants, `Inv`, …) applies to the
   extension unchanged; `handshakeStep_base` is the one-step form.
6. Preservation: every event other than `recvAccept` leaves `acceptReceived?`
   untouched (`step_ofEvent_acceptReceived?`), and `recvAccept` can fire at most
   once (`recvAccept_unrepeatable`, via the existing `canRecvAccept` guard).
   Consequently any stored payload is *provenanced* to an actual `recvAccept`
   event in the reachable history (`reachableExt_payload_provenance`), and the
   payload present when `funding_created` is permitted is exactly the payload
   that was received (`acceptReceived?_of_sendFundingCreated`).
7. Key-attribution interface: the stored payload's `funding_pubkey` is the
   remote funding key of the handshake negotiation
   (`stored_negotiation_remoteFundingKey`) and, under
   `KeyModelTargets.AdvertisesKey`, the signer's generated key
   (`stored_negotiation_key_eq_generated`).  This is the projection downstream
   lanes (H21–H24) need; it does **not** discharge `AdvertisesKey` itself.
8. Non-vacuity: `witness_reachable` exhibits a concrete `ReachableExt` state
   whose payload is the concrete `witnessAcceptChannel` and whose boolean flag
   is `true`.

**Scope.**  This module models the *state* extension only.  It proves no
transport authentication: `accept_channel` carries no signature and no sender
identity, so the payload is attributable only to "the message this endpoint
received on this transport".  `AdvertisesKey` (wire field = generated key) and
`KeyBinding` (signature attribution) remain explicit hypotheses, exactly as in
`KeyModelTargets`.  The extension is one-shot by construction, matching BOLT 2
channel establishment v1's single active negotiation; reconnection and
retransmission are out of scope, as in the base handshake.

**BOLT sections.**  BOLT 2 §"The `accept_channel` Message"
(`refs/bolts/02-peer-protocol.md`, `funding_pubkey` and the fixed payload
layout) and §"Channel Establishment v1" (`02-peer-protocol.md:629-680`).

**Anchors.**  `lightning/src/ln/msgs.rs:371` (`AcceptChannel`);
`lightning/src/ln/wire.rs:518` (type 33); the receive-side handler in
`lightning/src/ln/channelmanager.rs` stores the message for the channel.
-/

import LnLean.Protocol.Handshake
import LnLean.Proofs.Crypto.KeyModelTargets

namespace LnLean.Proofs.WaveH.H20

set_option autoImplicit false
set_option maxRecDepth 10000

open LnLean
open LnLean.Protocol
open LnLean.Protocol.Handshake
open LnLean.Bitcoin
open LnLean.Crypto

/-! ## 1. The local state extension -/

/-- A local extension of the unchanged `HandshakeState`: the ten boolean
milestones in `base`, plus the exact `accept_channel` payload received, if any.
The extension is additive — no field, event, or theorem of `HandshakeState` is
modified. -/
structure HandshakeStateExt where
  /-- The unchanged wave-1 handshake state. -/
  base : HandshakeState
  /-- The `accept_channel` payload this endpoint received, once. -/
  acceptReceived? : Option AcceptChannel := none
deriving Repr, BEq

namespace HandshakeStateExt

/-- The state before any message has been sent or received: no payload. -/
def initial : HandshakeStateExt := { base := HandshakeState.initial }

/-- **The relation to the existing boolean flag.**  The payload is present
exactly when `HandshakeState.acceptReceived` is set.  This is the invariant that
makes the boolean milestone and the stored message interchangeable downstream. -/
def AcceptLinked (s : HandshakeStateExt) : Prop :=
  s.base.acceptReceived = true ↔ ∃ a : AcceptChannel, s.acceptReceived? = some a

/-- The initial state is linked: neither the flag nor the payload is set. -/
theorem initial_acceptLinked : initial.AcceptLinked := by
  simp [AcceptLinked, initial, HandshakeState.initial]

end HandshakeStateExt

/-! ## 2. Extended events and transitions -/

/-- The extended event type.  Every base `HandshakeEvent` is available; the
`accept_channel` receipt additionally carries the message payload.  There is no
payload-free `ofEvent .recvAcceptChannel`, so the flag cannot be set without the
payload. -/
inductive ExtEvent where
  /-- A base handshake event (all events except the `accept_channel` receipt). -/
  | ofEvent (e : HandshakeEvent)
  /-- The `accept_channel` receipt, carrying the exact payload. -/
  | recvAccept (a : AcceptChannel)
deriving Repr

/-- Lift an optional base successor into the payload-carrying state, keeping
`payload` as the stored message. -/
def lift (_s : HandshakeStateExt) (payload : Option AcceptChannel)
    (o : Option HandshakeState) : Option HandshakeStateExt :=
  o.map fun b => { base := b, acceptReceived? := payload }

/-- One deterministic extension transition.  The base transition is
`handshakeStep` unchanged; the only new behaviour is that `recvAccept a` stores
`some a`. -/
def step (s : HandshakeStateExt) : ExtEvent → Option HandshakeStateExt
  | .ofEvent .recvAcceptChannel => none
  | .ofEvent e => lift s s.acceptReceived? (handshakeStep s.base e)
  | .recvAccept a => lift s (some a) (handshakeStep s.base .recvAcceptChannel)

/-! ### `lift` projections -/

/-- The stored payload of a lifted successor is exactly the payload supplied. -/
theorem lift_acceptReceived? {s : HandshakeStateExt} {payload : Option AcceptChannel}
    {o : Option HandshakeState} {s' : HandshakeStateExt}
    (h : lift s payload o = some s') : s'.acceptReceived? = payload := by
  cases o with
  | none => simp [lift] at h
  | some b =>
      simp only [lift, Option.map_some, Option.some.injEq] at h
      rw [← h]

/-- The base state of a lifted successor is exactly the base successor. -/
theorem lift_base {s : HandshakeStateExt} {payload : Option AcceptChannel}
    {o : Option HandshakeState} {s' : HandshakeStateExt}
    (h : lift s payload o = some s') : o = some s'.base := by
  cases o with
  | none => simp [lift] at h
  | some b =>
      simp only [lift, Option.map_some, Option.some.injEq] at h
      rw [← h]

/-! ### Transitions project to `handshakeStep` -/

/-- The extension transition on a payload-free event is the lifted base
transition.  The hypothesis rules out the payload-free `accept_channel` receipt,
which `step` disables. -/
theorem step_ofEvent {s : HandshakeStateExt} {e : HandshakeEvent}
    (hne : e ≠ .recvAcceptChannel) :
    step s (.ofEvent e) = lift s s.acceptReceived? (handshakeStep s.base e) := by
  cases e <;> simp_all [step]

/-- **Base projection of a payload-free event.**  It is exactly
`handshakeStep`. -/
theorem step_ofEvent_base {s s' : HandshakeStateExt} {e : HandshakeEvent}
    (hne : e ≠ .recvAcceptChannel) (h : step s (.ofEvent e) = some s') :
    handshakeStep s.base e = some s'.base := by
  rw [step_ofEvent hne] at h
  exact lift_base h

/-- **Payload preservation.**  No payload-free event changes the stored
`accept_channel`. -/
theorem step_ofEvent_acceptReceived? {s s' : HandshakeStateExt} {e : HandshakeEvent}
    (hne : e ≠ .recvAcceptChannel) (h : step s (.ofEvent e) = some s') :
    s'.acceptReceived? = s.acceptReceived? := by
  rw [step_ofEvent hne] at h
  exact lift_acceptReceived? h

/-- Base projection of the payload-carrying `accept_channel` receipt. -/
theorem step_recvAccept_base {s s' : HandshakeStateExt} {a : AcceptChannel}
    (h : step s (.recvAccept a) = some s') :
    handshakeStep s.base .recvAcceptChannel = some s'.base :=
  lift_base (s := s) (payload := some a)
    (o := handshakeStep s.base .recvAcceptChannel) (s' := s') h

/-- **`recvAccept` sets the payload.**  A permitted receipt stores exactly the
message it carried. -/
theorem step_recvAccept_acceptReceived? {s s' : HandshakeStateExt} {a : AcceptChannel}
    (h : step s (.recvAccept a) = some s') : s'.acceptReceived? = some a :=
  lift_acceptReceived? (s := s) (payload := some a)
    (o := handshakeStep s.base .recvAcceptChannel) (s' := s') h

/-- **`recvAccept` sets the existing boolean flag**, re-derived through the
extension from the unchanged `acceptReceived_of_recvAcceptChannel`. -/
theorem step_recvAccept_acceptReceived {s s' : HandshakeStateExt} {a : AcceptChannel}
    (h : step s (.recvAccept a) = some s') : s'.base.acceptReceived = true :=
  acceptReceived_of_recvAcceptChannel (step_recvAccept_base h)

/-! ### The boolean flag is untouched by every other event -/

/-- Every base handshake transition other than the `accept_channel` receipt
leaves `acceptReceived` unchanged.  This is a projection/preservation fact about
the unchanged model, proved here without editing it. -/
theorem acceptReceived_handshakeStep_ne {s s' : HandshakeState} {e : HandshakeEvent}
    (hne : e ≠ .recvAcceptChannel) (h : handshakeStep s e = some s') :
    s'.acceptReceived = s.acceptReceived := by
  cases e <;> first
    | exact absurd rfl hne
    | (simp only [handshakeStep] at h
       split at h
       · cases h
         rfl
       · simp_all)

/-! ## 3. Reachability and the linking invariant -/

/-- Reachable extension states: the extension's `initial` state and every
permitted extension transition. -/
inductive ReachableExt : HandshakeStateExt → Prop where
  | initial : ReachableExt HandshakeStateExt.initial
  | step {s s' : HandshakeStateExt} (e : ExtEvent) :
      ReachableExt s → step s e = some s' → ReachableExt s'

/-- **One-step base projection.**  Every extension step is a `HandshakeStep` of
the unchanged machine. -/
theorem handshakeStep_base {s s' : HandshakeStateExt} {e : ExtEvent}
    (h : step s e = some s') : HandshakeStep s.base s'.base := by
  cases e with
  | ofEvent ev =>
      by_cases hne : ev = .recvAcceptChannel
      · rw [hne] at h
        simp [step] at h
      · exact ⟨ev, step_ofEvent_base hne h⟩
  | recvAccept a => exact ⟨.recvAcceptChannel, step_recvAccept_base h⟩

/-- **Reachability projection.**  A reachable extension state projects to a
reachable state of the unchanged v1 machine, so all existing handshake laws
apply. -/
theorem reachableExt_base {s : HandshakeStateExt} (h : ReachableExt s) :
    Reachable s.base := by
  induction h with
  | initial => simpa [HandshakeStateExt.initial] using Reachable.initial
  | step e _ hstep ih =>
      cases e with
      | ofEvent ev =>
          by_cases hne : ev = .recvAcceptChannel
          · rw [hne] at hstep
            simp [step] at hstep
          · exact Reachable.step ev ih (step_ofEvent_base hne hstep)
      | recvAccept a =>
          exact Reachable.step .recvAcceptChannel ih (step_recvAccept_base hstep)

/-- A payload-free step preserves the linking invariant. -/
theorem acceptLinked_step_ofEvent {s s' : HandshakeStateExt} {e : HandshakeEvent}
    (hne : e ≠ .recvAcceptChannel) (hs : s.AcceptLinked)
    (h : step s (.ofEvent e) = some s') : s'.AcceptLinked := by
  have hbase := step_ofEvent_base hne h
  have hpay := step_ofEvent_acceptReceived? hne h
  have hacc := acceptReceived_handshakeStep_ne hne hbase
  unfold HandshakeStateExt.AcceptLinked at hs ⊢
  rw [hpay, hacc]
  exact hs

/-- The `accept_channel` receipt establishes the linking invariant: both the
boolean flag and the payload become set. -/
theorem acceptLinked_step_recvAccept {s s' : HandshakeStateExt} {a : AcceptChannel}
    (h : step s (.recvAccept a) = some s') : s'.AcceptLinked := by
  unfold HandshakeStateExt.AcceptLinked
  rw [step_recvAccept_acceptReceived h, step_recvAccept_acceptReceived? h]
  constructor
  · intro _
    exact ⟨a, rfl⟩
  · intro _
    rfl

/-- **Every reachable extension state links the boolean flag to the payload.** -/
theorem reachableExt_acceptLinked {s : HandshakeStateExt} (h : ReachableExt s) :
    s.AcceptLinked := by
  induction h with
  | initial => exact HandshakeStateExt.initial_acceptLinked
  | step e _ hstep ih =>
      cases e with
      | ofEvent ev =>
          by_cases hne : ev = .recvAcceptChannel
          · rw [hne] at hstep
            simp [step] at hstep
          · exact acceptLinked_step_ofEvent hne ih hstep
      | recvAccept a => exact acceptLinked_step_recvAccept hstep

/-! ## 4. Relating the payload to the boolean flag -/

/-- The linking invariant in its raw form. -/
theorem acceptReceived_iff_acceptReceived? {s : HandshakeStateExt}
    (hs : s.AcceptLinked) :
    s.base.acceptReceived = true ↔ ∃ a : AcceptChannel, s.acceptReceived? = some a :=
  hs

/-- The flag is set exactly when a payload is stored (reachable state). -/
theorem acceptReceived_iff_exists_payload {s : HandshakeStateExt}
    (h : ReachableExt s) :
    s.base.acceptReceived = true ↔ ∃ a : AcceptChannel, s.acceptReceived? = some a :=
  reachableExt_acceptLinked h

/-- If the flag never fired, no payload is stored. -/
theorem acceptReceived?_eq_none_of_flag_false {s : HandshakeStateExt}
    (hs : s.AcceptLinked) (h : s.base.acceptReceived = false) :
    s.acceptReceived? = none := by
  cases hp : s.acceptReceived? with
  | none => rfl
  | some a =>
      have htrue : s.base.acceptReceived = true := hs.2 ⟨a, hp⟩
      rw [h] at htrue
      exact absurd htrue (by simp)

/-- Conversely, a stored payload forces the flag. -/
theorem flag_true_of_acceptReceived? {s : HandshakeStateExt} {a : AcceptChannel}
    (hs : s.AcceptLinked) (h : s.acceptReceived? = some a) :
    s.base.acceptReceived = true :=
  hs.2 ⟨a, h⟩

/-- **A second `accept_channel` receipt is impossible.**  The base guard
`canRecvAccept` requires `acceptReceived = false`, and the first receipt sets it
to `true`. -/
theorem recvAccept_unrepeatable {s s' s'' : HandshakeStateExt} {a b : AcceptChannel}
    (h₁ : step s (.recvAccept a) = some s')
    (h₂ : step s' (.recvAccept b) = some s'') : False := by
  have hflag := step_recvAccept_acceptReceived h₁
  have hnone : step s' (.recvAccept b) = none := by
    have hg : ¬ s'.base.canRecvAccept := by
      intro hc
      have hf : s'.base.acceptReceived = false := hc.2.2.2.1
      rw [hflag] at hf
      exact absurd hf (by simp)
    simp [step, lift, handshakeStep, hg]
  rw [hnone] at h₂
  cases h₂

/-! ## 5. Downstream: the payload that funded the channel -/

/-- **Payload evolution.**  A step either preserves the stored payload or is a
receipt that sets it.  This is the preservation theorem downstream key
attribution consumes: no event can silently rewrite a stored payload. -/
theorem acceptReceived?_step_cases {s s' : HandshakeStateExt} {e : ExtEvent}
    (h : step s e = some s') :
    s'.acceptReceived? = s.acceptReceived? ∨
      ∃ a : AcceptChannel, s'.acceptReceived? = some a := by
  cases e with
  | ofEvent ev =>
      by_cases hne : ev = .recvAcceptChannel
      · rw [hne] at h
        simp [step] at h
      · exact Or.inl (step_ofEvent_acceptReceived? hne h)
  | recvAccept a => exact Or.inr ⟨a, step_recvAccept_acceptReceived? h⟩

/-- **The payload present when `funding_created` is permitted is the received
one.**  The existing `acceptReceived_of_sendFundingCreated` guarantees the flag;
the linking invariant turns it into a stored message, and the step preserves it.
-/
theorem acceptReceived?_of_sendFundingCreated {s s' : HandshakeStateExt}
    (hs : ReachableExt s)
    (h : step s (.ofEvent .sendFundingCreated) = some s') :
    ∃ a : AcceptChannel, s.acceptReceived? = some a ∧ s'.acceptReceived? = some a := by
  have hbase := step_ofEvent_base (by decide) h
  have hflag : s.base.acceptReceived = true :=
    acceptReceived_of_sendFundingCreated hbase
  obtain ⟨a, ha⟩ := (acceptReceived_iff_exists_payload hs).1 hflag
  refine ⟨a, ha, ?_⟩
  rw [step_ofEvent_acceptReceived? (by decide) h]
  exact ha

/-- **Payload provenance.**  Every stored payload at a reachable state was put
there by an actual permitted `recvAccept` event earlier in the reachable
history. -/
theorem reachableExt_payload_provenance {s : HandshakeStateExt}
    (h : ReachableExt s) :
    ∀ {a : AcceptChannel}, s.acceptReceived? = some a →
      ∃ s₀ : HandshakeStateExt, ReachableExt s₀ ∧
        ∃ s₁ : HandshakeStateExt, step s₀ (.recvAccept a) = some s₁ := by
  induction h with
  | initial =>
      intro a ha
      simp [HandshakeStateExt.initial] at ha
  | step e hreach hstep ih =>
      intro a ha
      cases e with
      | recvAccept b =>
          have hb : some b = some a := by
            rw [← step_recvAccept_acceptReceived? hstep]
            exact ha
          injection hb with hba
          subst hba
          exact ⟨_, hreach, _, hstep⟩
      | ofEvent ev =>
          by_cases hne : ev = .recvAcceptChannel
          · rw [hne] at hstep
            simp [step] at hstep
          · rw [step_ofEvent_acceptReceived? hne hstep] at ha
            exact ih ha

/-! ### Key-attribution projections -/

/-- A stored payload is exactly what the negotiation construction consumes:
`accept_channel.funding_pubkey` becomes the remote funding key. -/
theorem stored_payload_negotiation {s : HandshakeStateExt} {a : AcceptChannel}
    (ha : s.acceptReceived? = some a)
    (localFundingKey : PubKey) (fundingSatoshis : BtcAmount) (pushMsat : Msat)
    (temporaryChannelId : TemporaryChannelId) :
    s.acceptReceived? = some a ∧
      (a.toFundingNegotiation localFundingKey fundingSatoshis pushMsat
        temporaryChannelId).remoteFundingKey = a.fundingPubKey :=
  ⟨ha, AcceptChannel.toFundingNegotiation_remoteFundingKey _ _ _ _ _⟩

/-- **Downstream key-attribution interface.**  A reachable state that stores a
payload `a` satisfying the unchanged `KeyModelTargets.AdvertisesKey` hypothesis
has its boolean flag set, and the remote funding key of that payload's
negotiation is the signer's generated key.  This does not discharge
`AdvertisesKey` (see `KeyModelTargets` §4). -/
theorem stored_payload_advertised_key {M : PrimitiveModel} {K : KeyModel M}
    {seed : ByteArray} {s : HandshakeStateExt} {a : AcceptChannel}
    (h : ReachableExt s) (ha : s.acceptReceived? = some a)
    (hadv : LnLean.Proofs.Crypto.KeyModelTargets.AdvertisesKey K seed a)
    (localFundingKey : PubKey) (fundingSatoshis : BtcAmount) (pushMsat : Msat)
    (temporaryChannelId : TemporaryChannelId) :
    s.base.acceptReceived = true ∧
      (a.toFundingNegotiation localFundingKey fundingSatoshis pushMsat
        temporaryChannelId).remoteFundingKey = K.publicOfSeed seed :=
  ⟨flag_true_of_acceptReceived? (reachableExt_acceptLinked h) ha,
    by
      rw [AcceptChannel.toFundingNegotiation_remoteFundingKey]
      exact hadv⟩

/-! ## 6. Non-vacuity -/

/-- A concrete, wire-shaped `accept_channel` payload. -/
def witnessAcceptChannel : AcceptChannel where
  temporaryChannelId := ChannelId.zero
  dustLimitSatoshis := 546
  maxHtlcValueInFlightMsat := 0
  channelReserveSatoshis := 0
  htlcMinimumMsat := 0
  minimumDepth := 1
  toSelfDelay := 144
  maxAcceptedHtlcs := 483
  fundingPubKey := ⟨ByteArray.empty⟩
  revocationBasepoint := ⟨ByteArray.empty⟩
  paymentBasepoint := ⟨ByteArray.empty⟩
  delayedPaymentBasepoint := ⟨ByteArray.empty⟩
  htlcBasepoint := ⟨ByteArray.empty⟩
  firstPerCommitmentPoint := ⟨ByteArray.empty⟩

/-- State after `sendInit`. -/
def witnessAfterSendInit : HandshakeStateExt where
  base := { HandshakeState.initial with initSent := true }

/-- State after `sendInit` and `recvInit`: the `accept_channel` guard holds. -/
def witnessAfterInit : HandshakeStateExt where
  base := { HandshakeState.initial with initSent := true, initReceived := true }

/-- State after receiving `witnessAcceptChannel`. -/
def witnessAfterAccept : HandshakeStateExt where
  base :=
    { HandshakeState.initial with
      initSent := true,
      initReceived := true,
      acceptReceived := true }
  acceptReceived? := some witnessAcceptChannel

theorem witness_sendInit :
    step HandshakeStateExt.initial (.ofEvent .sendInit) = some witnessAfterSendInit := by
  show lift HandshakeStateExt.initial HandshakeStateExt.initial.acceptReceived?
      (handshakeStep HandshakeStateExt.initial.base .sendInit) = some witnessAfterSendInit
  rw [show handshakeStep HandshakeStateExt.initial.base .sendInit =
        some witnessAfterSendInit.base from by rfl]
  rfl

theorem witness_recvInit :
    step witnessAfterSendInit (.ofEvent .recvInit) = some witnessAfterInit := by
  show lift witnessAfterSendInit witnessAfterSendInit.acceptReceived?
      (handshakeStep witnessAfterSendInit.base .recvInit) = some witnessAfterInit
  rw [show handshakeStep witnessAfterSendInit.base .recvInit =
        some witnessAfterInit.base from by rfl]
  rfl

theorem witness_recvAccept :
    step witnessAfterInit (.recvAccept witnessAcceptChannel) = some witnessAfterAccept := by
  show lift witnessAfterInit (some witnessAcceptChannel)
      (handshakeStep witnessAfterInit.base .recvAcceptChannel) = some witnessAfterAccept
  rw [show handshakeStep witnessAfterInit.base .recvAcceptChannel =
        some witnessAfterAccept.base from by rfl]
  rfl

/-- **The extension is non-vacuous.**  A concrete reachable state stores the
concrete payload and has the boolean flag set. -/
theorem witness_reachable :
    ∃ s : HandshakeStateExt,
      ReachableExt s ∧ s.acceptReceived? = some witnessAcceptChannel ∧
        s.base.acceptReceived = true := by
  refine ⟨witnessAfterAccept, ?_, ?_, ?_⟩
  · exact ReachableExt.step _ (ReachableExt.step _ (ReachableExt.step _
      ReachableExt.initial witness_sendInit) witness_recvInit) witness_recvAccept
  · simp [witnessAfterAccept]
  · simp [witnessAfterAccept]

/-! ## 7. Summary -/

/-- Bundled faithfully-scoped reading of the H20 deliverable: a receipt stores
and flags the payload, every reachable state links the flag to the payload,
reachability projects to the unchanged machine, stored payloads are provenanced
to a real receipt, and the model is non-vacuous. -/
theorem accept_payload_model_summary :
    (∀ (s s' : HandshakeStateExt) (a : AcceptChannel),
        step s (.recvAccept a) = some s' →
          s'.acceptReceived? = some a ∧ s'.base.acceptReceived = true) ∧
      (∀ s : HandshakeStateExt, ReachableExt s →
        (s.base.acceptReceived = true ↔ ∃ a, s.acceptReceived? = some a)) ∧
      (∀ s : HandshakeStateExt, ReachableExt s → Reachable s.base) ∧
      (∀ (s : HandshakeStateExt) (a : AcceptChannel), ReachableExt s →
        s.acceptReceived? = some a →
          ∃ s₀ : HandshakeStateExt, ReachableExt s₀ ∧
            ∃ s₁ : HandshakeStateExt, step s₀ (.recvAccept a) = some s₁) ∧
      (∃ s : HandshakeStateExt, ReachableExt s ∧
        s.acceptReceived? = some witnessAcceptChannel ∧
          s.base.acceptReceived = true) :=
  ⟨fun _s _s' _a h => ⟨step_recvAccept_acceptReceived? h, step_recvAccept_acceptReceived h⟩,
    fun s h => acceptReceived_iff_exists_payload (s := s) h,
    fun _s h => reachableExt_base h,
    fun s _a h ha => reachableExt_payload_provenance (s := s) h ha,
    witness_reachable⟩

end LnLean.Proofs.WaveH.H20
