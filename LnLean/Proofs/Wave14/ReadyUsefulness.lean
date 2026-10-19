import LnLean.Proofs.WaveD.D18

/-!
# LnLean.Proofs.Wave14.ReadyUsefulness

Additive **operational-readiness carrier** for the Wave-13 review gap G19
(`REV-06`, R32 §3 G19 and §5.3 item 9).  The existing catalog statement
`LnLean.Protocol.Handshake.channel_ready_gate` is *not* redefined: it remains
the two-flag handshake fact

`ready s = true ↔ s.channelReadySent = true ∧ s.channelReadyReceived = true`.

This module adds the separate carrier `Readiness` and the bundled
`UsableChannel`.  A `Readiness` records the handshake state together with the
operational fields that `channel_ready` alone does **not** determine:

* `confirmations` / `minConfirmations` — explicit funding-confirmation depth;
* `peerConnected` — an explicit peer-connectivity flag;
* `shutdownStarted` — whether the shutdown/closing path has begun;
* `splicePending` — whether a splice is in progress.

`Readiness.usable` is the conjunction of all five conditions.  The two headline
results are:

* `usable_implies_channel_ready_gate` — every `UsableChannel` satisfies the
  existing two-flag gate, and in particular both `channel_ready` flags are set;
* `channel_ready_gate_not_usable` — a concrete `Readiness` with both flags
  true but zero confirmations and a disconnected peer is **not** usable.  The
  stronger form `exists_unusable_extension_of_ready` shows that *every* ready
  handshake state can be extended to an unusable readiness record, so the
  separation is not an artefact of one hand-picked handshake state.

Per-field separation theorems (`ready_zeroConfirmations_not_usable`,
`ready_disconnected_not_usable`, `ready_shutdown_not_usable`,
`ready_splicePending_not_usable`) show that each explicit field is doing work.
`usableChannel_witness` is the positive non-vacuity witness: a fully ready,
confirmed, connected, not-shutting-down, non-splicing channel exists.

## Boundaries

* **`channel_ready_gate` is unchanged.**  This file only imports it and derives
  consequences; no existing predicate, module, or theorem is modified.
* **Confirmation depth is arithmetic, not a chain proof.**  `confirmations` and
  `minConfirmations` are caller-supplied `Nat`s compared with `≤`.  There is no
  Bitcoin chain, SPV proof, reorg model, or zero-confirmation policy here; BOLT
  2's `minimum_depth` negotiation is not modelled.  The value `6` used in the
  witnesses is a concrete witness choice, **not** a claimed protocol constant.
* **Peer connectivity is a `Bool`, not transport authentication.**  It does not
  prove Noise authentication, liveness, or message delivery; see
  `docs/ASSUMPTIONS.md` and `LnLean.Protocol.Handshake` for the transport
  boundary.
* **Shutdown is only a flag.**  BOLT 2 permits `shutdown` before
  `channel_ready` (`refs/bolts/02-peer-protocol.md:2150-2152`), so the ready
  bit pair does not imply "not shutting down".  This module does not model the
  closing handshake.
* **Splice/version readiness is not modelled.**  `splicePending` is only an
  external boolean gate.  Funding mutation, quiescence, dual funding, and
  commitment-version semantics remain out of scope (R32 G16/G26; `Step` never
  changes funding).  A `false` `splicePending` field must not be cited as a
  splice-safety or splice-readiness proof.
* **No peer-layer gate is claimed.**  As documented in
  `LnLean.Proofs.WaveD.D18`, `LnLean.Protocol.Peer.receive` does not consult
  `ready`; `UsableChannel` does not change that model boundary.
-/

namespace LnLean.Proofs.Wave14.ReadyUsefulness

set_option autoImplicit false

open LnLean
open LnLean.Protocol

/-! ## The additive readiness carrier -/

/-- Operational readiness of a channel *after* the handshake.  The
`handshake` field keeps the existing two `channel_ready` flags; the remaining
fields are the independent operational conditions that the flags do not
encode.  `minConfirmations` is explicit so a caller can use the negotiated
BOLT 2 `minimum_depth` value instead of a global constant. -/
structure Readiness where
  /-- The existing BOLT 2 handshake state, including the two flags. -/
  handshake : HandshakeState
  /-- Current funding-transaction confirmation depth. -/
  confirmations : Nat
  /-- Required confirmation depth for the caller's policy. -/
  minConfirmations : Nat
  /-- Whether the peer is currently connected. -/
  peerConnected : Bool
  /-- Whether the shutdown/closing path has begun. -/
  shutdownStarted : Bool
  /-- Whether a splice is in progress.  This is a caller-declared gate only;
  no splice or funding-mutation semantics are modelled. -/
  splicePending : Bool

/-- The explicit confirmation-depth condition. -/
abbrev Readiness.confirmed (r : Readiness) : Prop :=
  r.minConfirmations ≤ r.confirmations

/-- **Operational usability.**  All of the following must hold:

* the handshake is ready (the existing two-flag `channel_ready` gate);
* the funding transaction has reached the caller's required depth;
* the peer is connected;
* no shutdown/closing path has begun;
* no splice is pending.

None of the last four conditions follows from the two `channel_ready` flags. -/
abbrev Readiness.usable (r : Readiness) : Prop :=
  r.handshake.ready = true ∧
    r.confirmed ∧
    r.peerConnected = true ∧
    r.shutdownStarted = false ∧
    r.splicePending = false

/-- A channel bundled with evidence that its `Readiness` fields are usable.
The proof fields are explicit so that a consumer cannot obtain the bundle
without settling each operational condition. -/
structure UsableChannel where
  /-- The underlying readiness record. -/
  readiness : Readiness
  /-- The existing two-flag handshake gate holds. -/
  ready : readiness.handshake.ready = true
  /-- The funding transaction has the required confirmation depth. -/
  confirmed : readiness.confirmed
  /-- The peer is connected. -/
  connected : readiness.peerConnected = true
  /-- No shutdown/closing path has begun. -/
  notShuttingDown : readiness.shutdownStarted = false
  /-- No splice is pending. -/
  noSplicePending : readiness.splicePending = false

/-- The carrier's predicate and its bundled form agree.  This is the bridge
used by consumers that hold a `Readiness` and a set of explicit proofs. -/
theorem UsableChannel.usable (u : UsableChannel) : u.readiness.usable :=
  ⟨u.ready, u.confirmed, u.connected, u.notShuttingDown, u.noSplicePending⟩

/-! ## Positive direction: usability implies the existing gate -/

/-- **Every usable channel satisfies `channel_ready_gate`.**  The proof cites
the existing catalog theorem `LnLean.Protocol.Handshake.channel_ready_gate`
rather than re-deriving a private copy of the two-flag definition, and returns
both the ready bit and the two flags it entails. -/
theorem usable_implies_channel_ready_gate (u : UsableChannel) :
    u.readiness.handshake.ready = true ∧
      (u.readiness.handshake.channelReadySent = true ∧
        u.readiness.handshake.channelReadyReceived = true) := by
  have hgate :=
    LnLean.Protocol.Handshake.channel_ready_gate u.readiness.handshake
  exact ⟨u.ready, hgate.mp u.ready⟩

/-- **Every usable channel has both `channel_ready` flags set.**  This is the
two-flag consequence of the existing gate: `UsableChannel` is strictly stronger
than the catalog fact, not a replacement for it. -/
theorem usable_implies_both_flags (u : UsableChannel) :
    u.readiness.handshake.channelReadySent = true ∧
      u.readiness.handshake.channelReadyReceived = true :=
  (usable_implies_channel_ready_gate u).2

/-! ## Negative direction: the two flags do not imply usability -/

/-- A handshake state whose two `channel_ready` flags are both true.  It is a
concrete post-handshake state for the separation witnesses; the readiness
fields below, not this state, decide usability. -/
def twoFlagHandshake : HandshakeState :=
  { HandshakeState.initial with
      channelReadySent := true
      channelReadyReceived := true }

@[simp] theorem twoFlagHandshake_ready : twoFlagHandshake.ready = true := rfl

/-- A family of readiness records built on the same ready handshake.  Only the
operational fields vary, so each separation theorem isolates one field. -/
def witnessReadiness (confirmations : Nat) (peerConnected : Bool)
    (shutdownStarted : Bool) (splicePending : Bool) : Readiness :=
  { handshake := twoFlagHandshake
    confirmations := confirmations
    minConfirmations := 6
    peerConnected := peerConnected
    shutdownStarted := shutdownStarted
    splicePending := splicePending }

@[simp] theorem witnessReadiness_handshake (confirmations : Nat)
    (peerConnected shutdownStarted splicePending : Bool) :
    (witnessReadiness confirmations peerConnected shutdownStarted
      splicePending).handshake = twoFlagHandshake := rfl

@[simp] theorem witnessReadiness_confirmed_iff (confirmations : Nat)
    (peerConnected shutdownStarted splicePending : Bool) :
    (witnessReadiness confirmations peerConnected shutdownStarted
      splicePending).confirmed ↔ 6 ≤ confirmations :=
  Iff.rfl

/-- **Confirmation depth alone separates readiness from the two flags.**  Both
`channel_ready` flags are true and the peer is connected, but the funding
transaction has zero confirmations against a required depth of six. -/
theorem ready_zeroConfirmations_not_usable :
    ∃ r : Readiness,
      r.handshake.ready = true ∧ ¬ r.confirmed ∧ ¬ r.usable := by
  refine ⟨witnessReadiness 0 true false false, rfl, ?_, ?_⟩
  · decide
  · decide

/-- **Peer connectivity alone separates readiness from the two flags.**  Both
flags are true and the confirmation depth is satisfied, but the peer is
disconnected. -/
theorem ready_disconnected_not_usable :
    ∃ r : Readiness,
      r.handshake.ready = true ∧ r.peerConnected = false ∧ ¬ r.usable := by
  refine ⟨witnessReadiness 6 false false false, rfl, rfl, ?_⟩
  decide

/-- **Shutdown alone separates readiness from the two flags.**  Both flags are
true, the channel is confirmed and connected, but the shutdown path has
started.  BOLT 2 permits `shutdown` before `channel_ready`
(`02-peer-protocol.md:2150-2152`). -/
theorem ready_shutdown_not_usable :
    ∃ r : Readiness,
      r.handshake.ready = true ∧ r.shutdownStarted = true ∧ ¬ r.usable := by
  refine ⟨witnessReadiness 6 true true false, rfl, rfl, ?_⟩
  decide

/-- **A pending splice alone separates readiness from the two flags.**  Both
flags are true, the channel is confirmed and connected, but a splice is
pending.  The flag is a policy gate; this theorem is not a splice-safety
claim. -/
theorem ready_splicePending_not_usable :
    ∃ r : Readiness,
      r.handshake.ready = true ∧ r.splicePending = true ∧ ¬ r.usable := by
  refine ⟨witnessReadiness 6 true false true, rfl, rfl, ?_⟩
  decide

/-- **The headline separation.**  A concrete readiness record has both
`channel_ready` flags true but zero confirmations and a disconnected peer, and
therefore is not usable.  Hence `channel_ready_gate` (the two-flag conjunction)
does not imply `UsableChannel` / operational readiness. -/
theorem channel_ready_gate_not_usable :
    ∃ r : Readiness,
      r.handshake.ready = true ∧
        r.handshake.channelReadySent = true ∧
        r.handshake.channelReadyReceived = true ∧
        r.confirmations = 0 ∧
        r.peerConnected = false ∧
        ¬ r.usable := by
  refine ⟨witnessReadiness 0 false false false, rfl, rfl, rfl, rfl, rfl, ?_⟩
  decide

/-- **The separation is uniform, not one hand-picked handshake.**  For every
handshake state satisfying the two-flag gate, there is a `Readiness` extension
with the same handshake, zero confirmations, and a disconnected peer that is
not usable.  The gate therefore constrains none of the operational fields. -/
theorem exists_unusable_extension_of_ready (s : HandshakeState)
    (h : s.ready = true) :
    ∃ r : Readiness,
      r.handshake = s ∧ r.handshake.ready = true ∧ ¬ r.usable := by
  refine
    ⟨{ handshake := s
       confirmations := 0
       minConfirmations := 6
       peerConnected := false
       shutdownStarted := false
       splicePending := false },
      rfl, h, ?_⟩
  intro hu
  exact absurd hu.2.1 (by simp)

/-! ## Positive non-vacuity witness -/

/-- A fully operational channel: both handshake flags are true, the funding
transaction has six confirmations against a required six, the peer is
connected, no shutdown has begun, and no splice is pending.  This proves that
`UsableChannel` is inhabited and that `usable` is not an always-false
predicate. -/
def usableWitness : UsableChannel where
  readiness := witnessReadiness 6 true false false
  ready := rfl
  confirmed := by decide
  connected := rfl
  notShuttingDown := rfl
  noSplicePending := rfl

/-- The positive witness really is usable under the explicit fields. -/
theorem usableWitness_usable : usableWitness.readiness.usable :=
  usableWitness.usable

/-- The positive witness satisfies the existing two-flag gate.  This applies
`usable_implies_both_flags` to a concrete inhabited `UsableChannel`. -/
theorem usableWitness_both_flags :
    usableWitness.readiness.handshake.channelReadySent = true ∧
      usableWitness.readiness.handshake.channelReadyReceived = true :=
  usable_implies_both_flags usableWitness

/-- **Non-vacuity package.**  There exists a `UsableChannel` whose explicit
fields are all satisfied and whose confirmations equal the required depth. -/
theorem usableChannel_witness :
    ∃ u : UsableChannel,
      u.readiness.handshake.ready = true ∧
        u.readiness.confirmed ∧
        u.readiness.confirmations = 6 ∧
        u.readiness.minConfirmations = 6 ∧
        u.readiness.peerConnected = true ∧
        u.readiness.shutdownStarted = false ∧
        u.readiness.splicePending = false := by
  refine ⟨usableWitness, rfl, ?_, rfl, rfl, rfl, rfl, rfl⟩
  decide

/-! ## Axiom audit -/

#print axioms usable_implies_channel_ready_gate
#print axioms usable_implies_both_flags
#print axioms ready_zeroConfirmations_not_usable
#print axioms ready_disconnected_not_usable
#print axioms ready_shutdown_not_usable
#print axioms ready_splicePending_not_usable
#print axioms channel_ready_gate_not_usable
#print axioms exists_unusable_extension_of_ready
#print axioms usableWitness_usable
#print axioms usableWitness_both_flags
#print axioms usableChannel_witness

end LnLean.Proofs.Wave14.ReadyUsefulness
