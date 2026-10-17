import LnLean.Channel.State
import LnLean.Channel.Types

/-!
# LnLean.Proofs.Channel.StateMachineProps

English claim.  The BOLT 2 channel lifecycle modelled by
`LnLean.Channel.Step` is a monotone, partly deterministic transition
relation:

1. every legal step keeps the phase or advances it by exactly one position in
   the order `negotiating -> awaitingLockin -> normal -> shuttingDown ->
   closed`;
2. `Reachable` is reflexive-transitive and closed under `Step` on either side;
3. the two commitment counters never decrease, never increase by more than
   one in a step, and increase *exactly* on the modelled events
   (`commitmentSigned` for the remote counter, `revokeAndAck` for the local
   counter);
4. no event is legal once the channel is `closed`, and every state reachable
   from a closed channel is the closed channel itself;
5. for a fixed source state and message, `Step` has a unique target
   (determinism), while several distinct messages are legal in the same
   `normal` state (genuine relation, not a function);
6. `funding_locked` (`channel_ready`) requires `awaitingLockin`, but the
   current model does **not** record that `funding_signed` happened; a
   two-event trace `[fundingCreated, fundingLocked]` reaches `normal`
   without `fundingSigned`.  The literal BOLT 2 ordering claim is therefore
   false in this model; the checked theorem below is the corrected claim and
   the gap is recorded in `agents/reports/B10.md`.

BOLT sections.
* BOLT 2 §2 `Channel Establishment v1` (`02-peer-protocol.md:629-1135`):
  `funding_signed` at `:1009`, `channel_ready` at `:1046`, and the message
  sequence diagram at `:661-666`.  BOLT 2 states that after `funding_signed`
  both sides wait for the funding transaction to reach depth and then send
  `channel_ready` (`02-peer-protocol.md:648-655`).
* BOLT 2 §3 `Channel Operations`: `commitment_signed`
  (`02-peer-protocol.md:3097`), `revoke_and_ack` (`:3206`), `update_fee`
  (`:3250`), `shutdown` (`:2136`), and `closing_signed` (`:2411`).
  Note that BOLT 2 permits `shutdown` before `channel_ready`
  (`02-peer-protocol.md:2150-2152`); the wave-A model deliberately enables
  `shutdown` only in the `normal` phase, so the phase-order theorem below is
  a theorem about the model, not a claim that the model is BOLT-complete.

rust-lightning anchors at `fe4900930c6bd5786ec4203274d7cf312776a5a6`.
* `lightning/src/ln/channel.rs:799` (`enum ChannelState`, whose variant order
  encodes the lifecycle order), `:863` (`ShutdownComplete`),
  `:4006-4011` (transition to `AwaitingChannelReady`), `:6767`
  (`ShutdownComplete` assignment), `:6900-6911` (counterparty commitment
  number handling).
* `lightning/src/ln/channel.rs:1552` (`enum ChannelPhase`), `:1546`
  (`struct Channel`), `:773-776` (`AwaitingRemoteRevoke` comment: a second
  `commitment_signed` is held while a revocation is outstanding).
* `lightning/src/ln/channelmanager.rs` dispatches the messages; the handlers
  themselves live in `channel.rs`.

What is NOT modelled.
* The deferred `commitment_signed` queue behind `AwaitingRemoteRevoke`
  (`channel.rs:773-776`).  This module proves that one step advances one
  counter; it does not model several queued updates.
* Per-commitment secrets, signature verification, `channel_reestablish`,
  retransmission, splicing, quiescence, dual funding, and simple close.
* A `fundingSignedSeen` flag.  Because `Channel` has no such field, the
  ordering "`channel_ready` only after `funding_signed`" cannot be stated as
  an invariant of `Step`; it is replaced by the checked counterexample below.
-/

namespace LnLean.Channel

set_option autoImplicit false

open LnLean

/-! ## A concrete witness channel

Several statements below are existential (a relation with more than one legal
message; a trace that reaches `normal` without `funding_signed`).  They need a
concrete `Channel`.  The witness uses empty byte strings and zero amounts;
none of the state-machine laws depends on those fields. -/

/-- Parameters of the witness channel.  The numeric values are ordinary BOLT 2
parameters and are irrelevant to the transition relation. -/
def witnessParams : ChannelParams where
  dustLimitSat := 546
  channelReserveSat := 1000
  toSelfDelay := 144
  maxHtlcValue := ⟨0⟩
  htlcMinimum := ⟨0⟩
  feerate := ⟨253⟩
  anchorOutputs := false

/-- One endpoint of the witness channel. -/
def witnessEndpoint : Endpoint where
  nodeId := ⟨ByteArray.empty⟩
  fundingPubKey := ⟨ByteArray.empty⟩
  paymentBasepoint := ⟨ByteArray.empty⟩
  delayedPaymentBasepoint := ⟨ByteArray.empty⟩
  params := witnessParams

/-- A channel in an arbitrary phase, all other fields fixed. -/
def witnessChannel (phase : ChannelPhase) : Channel where
  channelId := ⟨ByteArray.empty⟩
  funding := ⟨ByteArray.empty, 0⟩
  fundingValue := ⟨0⟩
  localEndpoint := witnessEndpoint
  remoteEndpoint := witnessEndpoint
  phase := phase
  localCommitmentNumber := 0
  remoteCommitmentNumber := 0
  balance := { localBalance := ⟨0⟩, remoteBalance := ⟨0⟩ }
  htlcs := []

@[simp] theorem witnessChannel_phase (p : ChannelPhase) :
    (witnessChannel p).phase = p := rfl

/-! ## Phase order and the finite transition table -/

/-- The finite table of phase pairs that `Step` is allowed to visit.  It is
just the graph of the lifecycle order. -/
inductive AllowedPhaseTransition : ChannelPhase → ChannelPhase → Prop where
  | negotiating_negotiating :
      AllowedPhaseTransition .negotiating .negotiating
  | negotiating_awaitingLockin :
      AllowedPhaseTransition .negotiating .awaitingLockin
  | awaitingLockin_awaitingLockin :
      AllowedPhaseTransition .awaitingLockin .awaitingLockin
  | awaitingLockin_normal :
      AllowedPhaseTransition .awaitingLockin .normal
  | normal_normal :
      AllowedPhaseTransition .normal .normal
  | normal_shuttingDown :
      AllowedPhaseTransition .normal .shuttingDown
  | shuttingDown_closed :
      AllowedPhaseTransition .shuttingDown .closed

/-- Every legal `Step` uses an edge of the finite phase table.  This is the
structural content of "the relation does not skip or reverse phases". -/
theorem step_allowedPhaseTransition {c c' : Channel} {e : ProtocolEvent}
    (h : Step c e c') : AllowedPhaseTransition c.phase c'.phase := by
  cases h with
  | openChannel h =>
      rw [h]
      exact AllowedPhaseTransition.negotiating_negotiating
  | acceptChannel h =>
      rw [h]
      exact AllowedPhaseTransition.negotiating_negotiating
  | fundingCreated h =>
      rw [h]
      exact AllowedPhaseTransition.negotiating_awaitingLockin
  | fundingSigned h =>
      rw [h]
      exact AllowedPhaseTransition.awaitingLockin_awaitingLockin
  | fundingLocked h =>
      rw [h]
      exact AllowedPhaseTransition.awaitingLockin_normal
  | commitmentSigned h =>
      rw [h]
      exact AllowedPhaseTransition.normal_normal
  | revokeAndAck h =>
      rw [h]
      exact AllowedPhaseTransition.normal_normal
  | updateFee h r =>
      rw [h]
      exact AllowedPhaseTransition.normal_normal
  | shutdown h =>
      rw [h]
      exact AllowedPhaseTransition.normal_shuttingDown
  | closingSigned h =>
      rw [h]
      exact AllowedPhaseTransition.shuttingDown_closed

/-- A legal step either keeps the phase rank or advances it by exactly one.
This strengthens `LnLean.Channel.step_phaseRank_le`. -/
theorem step_phaseRank_eq_or_succ {c c' : Channel} {e : ProtocolEvent}
    (h : Step c e c') :
    phaseRank c'.phase = phaseRank c.phase ∨
      phaseRank c'.phase = phaseRank c.phase + 1 := by
  cases h <;> simp_all [phaseRank]

/-- Monotonicity of the phase rank, derived from the exact-step lemma. -/
theorem step_phaseRank_monotone {c c' : Channel} {e : ProtocolEvent}
    (h : Step c e c') : phaseRank c.phase ≤ phaseRank c'.phase := by
  rcases step_phaseRank_eq_or_succ h with h' | h' <;> omega

/-- `Step` preserves the identity fields of the channel: channel id, funding
outpoint, and funding value never change. -/
theorem step_preserves_identity {c c' : Channel} {e : ProtocolEvent}
    (h : Step c e c') :
    c'.channelId = c.channelId ∧ c'.funding = c.funding ∧
      c'.fundingValue = c.fundingValue := by
  cases h <;> exact ⟨rfl, rfl, rfl⟩

/-! ## Determinism and genuine relationality -/

/-- For a fixed source and a fixed message, the target is unique.  This is the
sense in which the model's transition relation is deterministic. -/
theorem step_deterministic {c c₁ c₂ : Channel} {e : ProtocolEvent}
    (h₁ : Step c e c₁) (h₂ : Step c e c₂) : c₁ = c₂ := by
  cases h₁ <;> cases h₂ <;> simp_all

/-- Distinct messages may be legal in the same state.  The witness is a
`normal` channel in which both `commitment_signed` and `revoke_and_ack` (and
`update_fee`, `shutdown`) are enabled.  Hence `Step` is not a function
`Channel -> ProtocolEvent -> Channel`. -/
theorem normal_phase_is_relational :
    ∃ (c c₁ c₂ : Channel) (e₁ e₂ : ProtocolEvent),
      e₁ ≠ e₂ ∧ Step c e₁ c₁ ∧ Step c e₂ c₂ := by
  refine ⟨witnessChannel .normal,
    { witnessChannel .normal with
        remoteCommitmentNumber :=
          (witnessChannel .normal).remoteCommitmentNumber + 1 },
    { witnessChannel .normal with
        localCommitmentNumber :=
          (witnessChannel .normal).localCommitmentNumber + 1 },
    .commitmentSigned, .revokeAndAck, ?_, ?_, ?_⟩
  · decide
  · exact Step.commitmentSigned (witnessChannel .normal) rfl
  · exact Step.revokeAndAck (witnessChannel .normal) rfl

/-! ## Commitment counters -/

/-- `commitment_signed` advances the remote counter and leaves the local one
alone.  BOLT 2: `commitment_signed` contains signatures for the *remote*
commitment transaction (`02-peer-protocol.md:3097`). -/
theorem step_commitmentSigned_counters {c c' : Channel}
    (h : Step c .commitmentSigned c') :
    c'.remoteCommitmentNumber = c.remoteCommitmentNumber + 1 ∧
      c'.localCommitmentNumber = c.localCommitmentNumber := by
  cases h
  exact ⟨rfl, rfl⟩

/-- `revoke_and_ack` advances the local counter and leaves the remote one
alone.  BOLT 2: `revoke_and_ack` lets the sender apply the pending updates to
its own commitment (`02-peer-protocol.md:3206`). -/
theorem step_revokeAndAck_counters {c c' : Channel}
    (h : Step c .revokeAndAck c') :
    c'.localCommitmentNumber = c.localCommitmentNumber + 1 ∧
      c'.remoteCommitmentNumber = c.remoteCommitmentNumber := by
  cases h
  exact ⟨rfl, rfl⟩

/-- Every event other than `commitment_signed` leaves the remote counter
unchanged. -/
theorem step_remote_eq_of_ne_commitmentSigned {c c' : Channel}
    {e : ProtocolEvent} (h : Step c e c')
    (he : e ≠ ProtocolEvent.commitmentSigned) :
    c'.remoteCommitmentNumber = c.remoteCommitmentNumber := by
  cases h <;> simp_all

/-- Every event other than `revoke_and_ack` leaves the local counter
unchanged. -/
theorem step_local_eq_of_ne_revokeAndAck {c c' : Channel}
    {e : ProtocolEvent} (h : Step c e c')
    (he : e ≠ ProtocolEvent.revokeAndAck) :
    c'.localCommitmentNumber = c.localCommitmentNumber := by
  cases h <;> simp_all

/-- The remote counter increments exactly on `commitment_signed`. -/
theorem step_remote_succ_iff {c c' : Channel} {e : ProtocolEvent}
    (h : Step c e c') :
    c'.remoteCommitmentNumber = c.remoteCommitmentNumber + 1 ↔
      e = ProtocolEvent.commitmentSigned := by
  constructor
  · intro hc
    by_cases he : e = ProtocolEvent.commitmentSigned
    · exact he
    · have hsame := step_remote_eq_of_ne_commitmentSigned h he
      omega
  · intro he
    rw [he] at h
    exact (step_commitmentSigned_counters h).1

/-- The local counter increments exactly on `revoke_and_ack`. -/
theorem step_local_succ_iff {c c' : Channel} {e : ProtocolEvent}
    (h : Step c e c') :
    c'.localCommitmentNumber = c.localCommitmentNumber + 1 ↔
      e = ProtocolEvent.revokeAndAck := by
  constructor
  · intro hc
    by_cases he : e = ProtocolEvent.revokeAndAck
    · exact he
    · have hsame := step_local_eq_of_ne_revokeAndAck h he
      omega
  · intro he
    rw [he] at h
    exact (step_revokeAndAck_counters h).1

/-- A single step never advances both counters.  The two counters advance in
different halves of the BOLT 2 commitment round. -/
theorem step_not_both_counters_succ {c c' : Channel} {e : ProtocolEvent}
    (h : Step c e c') :
    ¬ (c'.localCommitmentNumber = c.localCommitmentNumber + 1 ∧
        c'.remoteCommitmentNumber = c.remoteCommitmentNumber + 1) := by
  rintro ⟨hl, hr⟩
  have hle : e = ProtocolEvent.revokeAndAck :=
    (step_local_succ_iff h).mp hl
  have hre : e = ProtocolEvent.commitmentSigned :=
    (step_remote_succ_iff h).mp hr
  rw [hle] at hre
  cases hre

/-- Neither counter can jump by more than one in a step. -/
theorem step_local_le_succ {c c' : Channel} {e : ProtocolEvent}
    (h : Step c e c') :
    c'.localCommitmentNumber ≤ c.localCommitmentNumber + 1 := by
  cases h <;> simp

theorem step_remote_le_succ {c c' : Channel} {e : ProtocolEvent}
    (h : Step c e c') :
    c'.remoteCommitmentNumber ≤ c.remoteCommitmentNumber + 1 := by
  cases h <;> simp

/-! ## Reachability -/

/-- `Reachable` is closed under a `Step` on the left. -/
theorem reachable_step_left {a b c : Channel} {e : ProtocolEvent}
    (h : Step a e b) (hbc : Reachable b c) : Reachable a c := by
  induction hbc with
  | refl => exact Reachable.of_step h
  | step _ hs ih => exact Reachable.step ih hs

/-- `Reachable` is closed under a `Step` on the right; this is the `step`
constructor, recorded as a theorem for symmetry. -/
theorem reachable_step_right {a b c : Channel} {e : ProtocolEvent}
    (hab : Reachable a b) (h : Step b e c) : Reachable a c :=
  Reachable.step hab h

/-- A closed channel has no reachable successor other than itself.  This
upgrades `no_step_from_closed` from one step to the reflexive-transitive
closure. -/
theorem reachable_from_closed_eq {c d : Channel} (h : Reachable c d)
    (hc : c.phase = .closed) : d = c := by
  revert hc
  induction h with
  | refl =>
      intro hc
      rfl
  | step hab hbd ih =>
      intro hc
      have hb := ih hc
      cases hb
      exact absurd hbd (no_step_from_closed _ _ _ hc)

/-! ## Traces and the `funding_signed` ordering gap -/

/-- A labelled path: the list of messages that drives a channel from `a` to
`b`.  `Reachable` forgets the labels, so this auxiliary relation is needed to
state "event `e` occurs before event `e'`". -/
inductive Trace : Channel → List ProtocolEvent → Channel → Prop where
  | nil (c : Channel) : Trace c [] c
  | cons {a b c : Channel} {e : ProtocolEvent} {es : List ProtocolEvent} :
      Step a e b → Trace b es c → Trace a (e :: es) c

/-- A trace can be forgotten to a `Reachable` proof. -/
theorem trace_to_reachable {a b : Channel} {es : List ProtocolEvent}
    (h : Trace a es b) : Reachable a b := by
  induction h with
  | nil => exact Reachable.refl _
  | cons hs _ ih => exact Reachable.trans (Reachable.of_step hs) ih

/-- The model admits a two-event trace from `negotiating` to `normal` that
never mentions `fundingSigned`: `fundingCreated` enters `awaitingLockin`,
and `fundingLocked` immediately enters `normal`. -/
theorem trace_channelReady_without_fundingSigned :
    Trace (witnessChannel .negotiating)
      [.fundingCreated, .fundingLocked]
      { witnessChannel .negotiating with phase := .normal } := by
  refine Trace.cons (Step.fundingCreated _ rfl) ?_
  refine Trace.cons (Step.fundingLocked _ rfl) (Trace.nil _)

/-- `fundingSigned` is not among the labels of the witness trace. -/
theorem fundingSigned_not_mem_channelReady_trace :
    ProtocolEvent.fundingSigned ∉
      ([.fundingCreated, .fundingLocked] : List ProtocolEvent) := by
  simp

/-- Corrected form of "`channel_ready` is unreachable before
`funding_signed`".  In the current model a trace from `negotiating` to
`normal` can omit `fundingSigned`; the ordering premise would need a new
`Channel` field recording that `funding_signed` was seen. -/
theorem channelReady_reachable_without_fundingSigned :
    ∃ (c d : Channel) (es : List ProtocolEvent),
      c.phase = .negotiating ∧ d.phase = .normal ∧
        Trace c es d ∧ ProtocolEvent.fundingSigned ∉ es := by
  refine ⟨witnessChannel .negotiating,
    { witnessChannel .negotiating with phase := .normal },
    [.fundingCreated, .fundingLocked], rfl, rfl,
    trace_channelReady_without_fundingSigned, ?_⟩
  simp

/-- If a trace starts in `negotiating` and ends in `normal`, then it must
contain `fundingLocked`: that is the only constructor of `Step` whose target
phase is `normal` from a lower phase, and the phase rank never decreases.
This is the positive half of the `channel_ready` ordering story. -/
theorem trace_to_normal_contains_fundingLocked {c d : Channel}
    {es : List ProtocolEvent} (ht : Trace c es d)
    (hc : c.phase = .negotiating) (hd : d.phase = .normal) :
    ProtocolEvent.fundingLocked ∈ es := by
  -- OBLIGATION: LN-CH-010 a trace from negotiating to normal contains fundingLocked
  sorry

end LnLean.Channel
