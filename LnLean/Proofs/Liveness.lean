import LnLean.Channel.State
import LnLean.Protocol.Peer
import LnLean.Basic.Core

/-!
# LnLean.Proofs.Liveness

## English claim

This module states the liveness scaffold for a single Lightning channel.  Its
central claims are:

1. **Lock-in.**  A channel in `awaitingLockin` reaches `normal` once the
   `funding_locked` / `channel_ready` event is scheduled and no scheduled
   event is lost (`fair_awaitingLockin_eventually_normal`).
2. **HTLC resolution.**  A pending HTLC has a resolution step (fulfil, fail,
   or timeout) whenever a settlement message is eventually delivered or an
   honest timer observes the CLTV expiry (`pending_htlc_eventually_resolved`).
3. **Reconnect.**  A reconnect cannot erase a retained outbound message:
   any finite sequence of inbound messages leaves the retransmission buffer
   untouched (`reconnect_preserves_channelReady`), and the retained
   `channel_ready` is exactly the message that completes lock-in
   (`reconnect_resend_completes_lockin`).  The reestablish counters can
   always be advanced to a peer's target
   (`reestablish_catches_up`).
4. **Cooperative close.**  `shuttingDown` reaches `closed` in one legal step
   (`shuttingDown_reaches_closed`), and a `normal` channel reaches `closed`
   through `shutdown` then `closing_signed` (`normal_reaches_closed`).
5. **Fairness is necessary.**  An unfair schedule that only ever runs
   `funding_signed` never reaches `normal`
   (`not_eventually_normal_without_fundingLocked`), so the fairness
   hypotheses below are not derivable from the transition relation.

Every temporal claim is conditional on an *explicit* hypothesis:

* `NoLoss c σ` — every prefix of the event schedule `σ` is executable;
* `Fair σ e` — the schedule eventually contains event `e`;
* `HTLCTrigger h` — a settlement message or an honest CLTV timer fires;
* `HonestTimer h tip` — the observed chain tip eventually reaches `h.cltvExpiry`.

None of these is an axiom.  They are parameters of the theorems, so an
instantiation must supply them.  The module contains no `axiom`, `admit`,
`native_decide`, `unsafe`, `@[implemented_by]`, or mathlib import.

## BOLT sections (pinned BOLTs `1aadb71`)

* BOLT 2 §"Channel Establishment v1", `refs/bolts/02-peer-protocol.md:629-1136`;
  in particular §"The `channel_ready` Message", `02-peer-protocol.md:1046-1136`
  ("Once both nodes have sent this, the channel enters normal operating
  mode", `:1048-1049`).
* BOLT 2 §"Channel Close", `02-peer-protocol.md:2046-2531`;
  §"Closing Initiation: `shutdown`", `:2136-2224`;
  §"Legacy Closing Negotiation: `closing_signed`", `:2411-2531`.
* BOLT 2 §"Normal Operation", `02-peer-protocol.md:2532-3351`;
  §"Removing an HTLC", `:2913-3042` (`update_fulfill_htlc` / `update_fail_htlc`).
* BOLT 2 §"Message Retransmission", `02-peer-protocol.md:3352-3635`;
  the `channel_reestablish` counters at `:3415-3500`.

## rust-lightning anchors (pinned commit `fe49009`)

* `lightning/src/ln/channelmanager.rs:13108` `internal_channel_ready` — the
  dispatcher path that takes a channel to normal operation after
  `channel_ready`; `:13140` `internal_channel_ready_with_funded_channel`.
* `lightning/src/ln/channelmanager.rs:13994` `internal_channel_reestablish` —
  reconnect handling; `channel.rs:10826` the per-channel handler and
  `channel.rs:13135` `get_channel_reestablish`, which emits the four BOLT 2
  counters.
* `lightning/src/ln/channelmanager.rs:9540` `timer_tick_occurred` — the
  periodic timer that drives expiry-related work.
* `lightning/src/ln/channelmanager.rs:13182` `internal_shutdown`, `:13295`
  `internal_closing_signed`; `channel.rs:11467` `shutdown`, `:11720`
  `closing_signed`.
* `lightning/src/ln/channelmanager.rs:13421` `internal_update_fulfill_htlc`,
  `:13504` `internal_update_fail_htlc`; `channel.rs:8640`
  `update_fulfill_htlc`, `:8671` `update_fail_htlc`, `:1552`
  `enum ChannelPhase`.

## What is NOT modelled

* **No wall clock and no timers.**  `Scheduler` is an abstract sequence of
  protocol events; `HonestTimer` is a predicate over an uninterpreted
  `tip : Nat → Nat`.  The module proves what follows *if* the timer fires, not
  that it fires.
* **No message-to-event mapping.**  `ProtocolEvent` is the channel-level
  event vocabulary; `Msg` is the peer-level wire vocabulary.  There is no
  function `Msg → ProtocolEvent`, so a `channel_ready` message cannot be
  turned into a `fundingLocked` event inside a proof.  `reconnect_resend_completes_lockin`
  states the two halves (retention and legality) separately.
* **No joint peer/channel transition.**  `PeerState` does not contain a
  `Channel`, and `LnLean.Channel.Step` does not read a `ChannelRecord`.
* **No lossy-link fairness.**  `LossyLink` can drop any message forever; the
  module does not define a fair-lossy scheduler.  `NoLoss` is deliberately
  stronger and is named as a hypothesis.
* **No HTLC event in `Channel.Step`.**  `update_add_htlc` / `update_fulfill_htlc`
  / `update_fail_htlc` do not appear in `ProtocolEvent`; HTLC resolution is
  modelled by the separate relation `Resolves`.  Consequently an HTLC timeout
  is represented as removal (`HTLCState.removed`), because `HTLCState` has no
  distinct `timedOut` tag.
* **No commitment handshake liveness.**  The `AwaitingRemoteRevoke` queue and
  the `commitment_signed`/`revoke_and_ack` round trip are not scheduled in
  wave A; the model only records the events and their counters.
* **No on-chain mechanics.**  Penalty economics (`LN-SEC-005`) and the
  watchtower bridge (`LN-SEC-006`) need `LnLean.Security` / L1 predicates and
  are outside this module's import allowlist.
* No closing-fee negotiation, splicing, dual funding, or multiparty channels.
-/

namespace LnLean.Proofs.Liveness

set_option autoImplicit false

open LnLean
open LnLean.Channel
open LnLean.Protocol (ChannelRecord Msg MsgKind ReestablishFields)

/-! ## 1. Deterministic executor for the step relation

`Step` is a relation, but its target is determined by the event and the source
state.  `step?` is the corresponding partial function.  The two lemmas
`step?_sound` and `step?_complete` prove that it neither invents nor loses
transitions; every later scheduler statement is built on them. -/

/-- Executable counterpart of `Step`.  `none` means the event is illegal in
this state. -/
def step? (c : Channel) (e : ProtocolEvent) : Option Channel :=
  match e with
  | .openChannel =>
      if c.phase = ChannelPhase.negotiating then some c else none
  | .acceptChannel =>
      if c.phase = ChannelPhase.negotiating then some c else none
  | .fundingCreated =>
      if c.phase = ChannelPhase.negotiating then
        some { c with phase := ChannelPhase.awaitingLockin }
      else none
  | .fundingSigned =>
      if c.phase = ChannelPhase.awaitingLockin then some c else none
  | .fundingLocked =>
      if c.phase = ChannelPhase.awaitingLockin then
        some { c with phase := ChannelPhase.normal }
      else none
  | .commitmentSigned =>
      if c.phase = ChannelPhase.normal then
        some { c with remoteCommitmentNumber := c.remoteCommitmentNumber + 1 }
      else none
  | .revokeAndAck =>
      if c.phase = ChannelPhase.normal then
        some { c with localCommitmentNumber := c.localCommitmentNumber + 1 }
      else none
  | .updateFee r =>
      if c.phase = ChannelPhase.normal then
        some { c with localEndpoint :=
          { c.localEndpoint with
            params := { c.localEndpoint.params with feerate := r } } }
      else none
  | .shutdown =>
      if c.phase = ChannelPhase.normal then
        some { c with phase := ChannelPhase.shuttingDown }
      else none
  | .closingSigned =>
      if c.phase = ChannelPhase.shuttingDown then
        some { c with phase := ChannelPhase.closed }
      else none

/-- Every result of `step?` is a legal `Step`. -/
theorem step?_sound {c c' : Channel} {e : ProtocolEvent}
    (h : step? c e = some c') : Step c e c' := by
  cases e with
  | openChannel =>
      by_cases hg : c.phase = ChannelPhase.negotiating
      · simp [step?, hg] at h
        cases h
        exact Step.openChannel c hg
      · simp [step?, hg] at h
  | acceptChannel =>
      by_cases hg : c.phase = ChannelPhase.negotiating
      · simp [step?, hg] at h
        cases h
        exact Step.acceptChannel c hg
      · simp [step?, hg] at h
  | fundingCreated =>
      by_cases hg : c.phase = ChannelPhase.negotiating
      · simp [step?, hg] at h
        cases h
        exact Step.fundingCreated c hg
      · simp [step?, hg] at h
  | fundingSigned =>
      by_cases hg : c.phase = ChannelPhase.awaitingLockin
      · simp [step?, hg] at h
        cases h
        exact Step.fundingSigned c hg
      · simp [step?, hg] at h
  | fundingLocked =>
      by_cases hg : c.phase = ChannelPhase.awaitingLockin
      · simp [step?, hg] at h
        cases h
        exact Step.fundingLocked c hg
      · simp [step?, hg] at h
  | commitmentSigned =>
      by_cases hg : c.phase = ChannelPhase.normal
      · simp [step?, hg] at h
        cases h
        simpa [hg] using Step.commitmentSigned c hg
      · simp [step?, hg] at h
  | revokeAndAck =>
      by_cases hg : c.phase = ChannelPhase.normal
      · simp [step?, hg] at h
        cases h
        simpa [hg] using Step.revokeAndAck c hg
      · simp [step?, hg] at h
  | updateFee r =>
      by_cases hg : c.phase = ChannelPhase.normal
      · simp [step?, hg] at h
        cases h
        simpa [hg] using Step.updateFee c hg r
      · simp [step?, hg] at h
  | shutdown =>
      by_cases hg : c.phase = ChannelPhase.normal
      · simp [step?, hg] at h
        cases h
        exact Step.shutdown c hg
      · simp [step?, hg] at h
  | closingSigned =>
      by_cases hg : c.phase = ChannelPhase.shuttingDown
      · simp [step?, hg] at h
        cases h
        exact Step.closingSigned c hg
      · simp [step?, hg] at h

/-- Every legal `Step` is produced by `step?`. -/
theorem step?_complete {c c' : Channel} {e : ProtocolEvent}
    (h : Step c e c') : step? c e = some c' := by
  cases h with
  | openChannel hg => simp [step?, hg]
  | acceptChannel hg => simp [step?, hg]
  | fundingCreated hg => simp [step?, hg]
  | fundingSigned hg => simp [step?, hg]
  | fundingLocked hg => simp [step?, hg]
  | commitmentSigned hg => simp [step?, hg]
  | revokeAndAck hg => simp [step?, hg]
  | updateFee hg r => simp [step?, hg]
  | shutdown hg => simp [step?, hg]
  | closingSigned hg => simp [step?, hg]

/-- `step?` is a function: it has at most one result. -/
theorem step?_det {c c₁ c₂ : Channel} {e : ProtocolEvent}
    (h₁ : step? c e = some c₁) (h₂ : step? c e = some c₂) : c₁ = c₂ := by
  rw [h₁] at h₂
  cases h₂
  rfl

/-! ## 2. Finite and infinite schedules -/

/-- An infinite event schedule.  It is abstract: nothing forces an event to
occur, which is why every liveness theorem below carries `Fair`. -/
abbrev Scheduler := Nat → ProtocolEvent

/-- Run a finite list of events from a channel. -/
def runList : Channel → List ProtocolEvent → Option Channel
  | c, [] => some c
  | c, e :: es => (step? c e).bind (fun c' => runList c' es)

/-- Every successful finite run is a `Reachable` pair. -/
theorem runList_sound {c c' : Channel} {es : List ProtocolEvent}
    (h : runList c es = some c') : Reachable c c' := by
  induction es generalizing c with
  | nil =>
      simp [runList] at h
      subst h
      exact Reachable.refl c
  | cons e es ih =>
      simp only [runList] at h
      cases hs : step? c e with
      | none => simp [hs] at h
      | some cm =>
          have h' : runList cm es = some c' := by
            simpa [runList, hs] using h
          exact Reachable.trans (Reachable.of_step (step?_sound hs)) (ih h')

/-- A successful run cannot lower the channel's phase rank. -/
theorem runList_phaseRank_le {c c' : Channel} {es : List ProtocolEvent}
    (h : runList c es = some c') :
    phaseRank c.phase ≤ phaseRank c'.phase :=
  Reachable.phaseRank_le (runList_sound h)

/-- Prefix execution of an infinite schedule. -/
def runPrefix (c : Channel) (σ : Scheduler) : Nat → Option Channel
  | 0 => some c
  | n + 1 => (runPrefix c σ n).bind (fun c' => step? c' (σ n))

@[simp] theorem runPrefix_zero (c : Channel) (σ : Scheduler) :
    runPrefix c σ 0 = some c := rfl

theorem runPrefix_succ (c : Channel) (σ : Scheduler) (n : Nat) :
    runPrefix c σ n.succ =
      (runPrefix c σ n).bind (fun c' => step? c' (σ n)) := rfl

/-- No scheduled event is lost: every prefix is executable.  This is the
module's partial-synchrony hypothesis and is never asserted as an axiom. -/
def NoLoss (c : Channel) (σ : Scheduler) : Prop :=
  ∀ n, ∃ cn, runPrefix c σ n = some cn

/-- The schedule eventually contains the event.  This is the module's
fairness hypothesis. -/
def Fair (σ : Scheduler) (e : ProtocolEvent) : Prop :=
  ∃ n, σ n = e

/-- Some finite prefix reaches a state satisfying `P`. -/
def Eventually (c : Channel) (σ : Scheduler) (P : Channel → Prop) : Prop :=
  ∃ n c', runPrefix c σ n = some c' ∧ P c'

/-- There exists a finite legal run from `c` to a state in phase `p`. -/
def ReachesPhase (c : Channel) (p : ChannelPhase) : Prop :=
  ∃ c', Reachable c c' ∧ c'.phase = p

/-! ## 3. Lock-in: `awaitingLockin` to `normal` -/

/-- From `awaitingLockin`, the only legal events are `funding_signed` and
`funding_locked`.  This is what makes the fair-schedule induction below
finite: no event can leave the phase except `funding_locked`. -/
theorem step_event_of_awaitingLockin {c c' : Channel} {e : ProtocolEvent}
    (hs : Step c e c') (hc : c.phase = ChannelPhase.awaitingLockin) :
    e = ProtocolEvent.fundingSigned ∨ e = ProtocolEvent.fundingLocked := by
  cases hs with
  | openChannel h => exact absurd (h.symm.trans hc) (by decide)
  | acceptChannel h => exact absurd (h.symm.trans hc) (by decide)
  | fundingCreated h => exact absurd (h.symm.trans hc) (by decide)
  | fundingSigned h => exact Or.inl rfl
  | fundingLocked h => exact Or.inr rfl
  | commitmentSigned h => exact absurd (h.symm.trans hc) (by decide)
  | revokeAndAck h => exact absurd (h.symm.trans hc) (by decide)
  | updateFee h r => exact absurd (h.symm.trans hc) (by decide)
  | shutdown h => exact absurd (h.symm.trans hc) (by decide)
  | closingSigned h => exact absurd (h.symm.trans hc) (by decide)

/-- Least-occurrence lemma, proved without `Nat.find` (not in core Lean):
if `p` holds somewhere, it holds at a least index.  The bound is the witness
of the existential. -/
theorem exists_first_occurrence (p : Nat → Prop) (n : Nat) (hn : p n) :
    ∃ k, k ≤ n ∧ p k ∧ ∀ j, j < k → ¬ p j := by
  revert hn
  refine Nat.strongRecOn n
    (motive := fun n => p n → ∃ k, k ≤ n ∧ p k ∧ ∀ j, j < k → ¬ p j) ?_
  intro n ih hn
  by_cases hprev : ∃ j, j < n ∧ p j
  · obtain ⟨j, hj, hpj⟩ := hprev
    obtain ⟨k, hk_le, hpk, hkmin⟩ := ih j hj hpj
    exact ⟨k, Nat.le_trans hk_le (Nat.le_of_lt hj), hpk, hkmin⟩
  · exact ⟨n, Nat.le_refl n, hn, fun j hj hpj => hprev ⟨j, hj, hpj⟩⟩

/-- Before the first `funding_locked`, every legal event is `funding_signed`,
so the channel remains in `awaitingLockin`. -/
theorem runPrefix_awaitingLockin_stays {c : Channel} {σ : Scheduler}
    (hnoLoss : NoLoss c σ) (hphase : c.phase = ChannelPhase.awaitingLockin)
    (k : Nat)
    (hnofl : ∀ j, j < k → σ j ≠ ProtocolEvent.fundingLocked) :
    ∃ ck, runPrefix c σ k = some ck ∧
      ck.phase = ChannelPhase.awaitingLockin := by
  induction k with
  | zero => exact ⟨c, rfl, hphase⟩
  | succ k ih =>
      obtain ⟨ck, hk, hck⟩ :=
        ih (fun j hj => hnofl j (Nat.lt_trans hj (Nat.lt_succ_self k)))
      obtain ⟨c', hc'⟩ := hnoLoss k.succ
      have hstep : step? ck (σ k) = some c' := by
        rw [runPrefix_succ, hk] at hc'
        simpa using hc'
      have hs : Step ck (σ k) c' := step?_sound hstep
      have he := step_event_of_awaitingLockin hs hck
      have hnk : σ k ≠ ProtocolEvent.fundingLocked :=
        hnofl k (Nat.lt_succ_self k)
      rcases he with he | he
      · have hcomp : step? ck ProtocolEvent.fundingSigned = some ck :=
          step?_complete (Step.fundingSigned ck hck)
        rw [he] at hstep
        rw [hcomp] at hstep
        cases hstep
        refine ⟨ck, ?_, hck⟩
        rw [runPrefix_succ, hk, he]
        simpa using hcomp
      · exact absurd he hnk

/-- **Lock-in liveness.**  If the channel is in `awaitingLockin`, the
schedule is loss-free, and it eventually runs `funding_locked`, then some
finite prefix reaches `normal`. -/
theorem fair_awaitingLockin_eventually_normal
    (c : Channel) (σ : Scheduler)
    (hphase : c.phase = ChannelPhase.awaitingLockin)
    (hnoLoss : NoLoss c σ)
    (hfair : Fair σ ProtocolEvent.fundingLocked) :
    Eventually c σ (fun c => c.phase = ChannelPhase.normal) := by
  obtain ⟨w, hw⟩ := hfair
  obtain ⟨k, _hkbound, hk, hmin⟩ :=
    exists_first_occurrence (fun n => σ n = ProtocolEvent.fundingLocked) w hw
  obtain ⟨ck, hkrun, hck⟩ :=
    runPrefix_awaitingLockin_stays hnoLoss hphase k hmin
  have hstep : step? ck ProtocolEvent.fundingLocked =
      some { ck with phase := ChannelPhase.normal } :=
    step?_complete (Step.fundingLocked ck hck)
  refine ⟨k.succ, { ck with phase := ChannelPhase.normal }, ?_, rfl⟩
  rw [runPrefix_succ, hkrun, hk]
  simpa using hstep

/-- An existential, fairness-free corollary: from `awaitingLockin` a legal
finite schedule to `normal` exists.  This is the `ReachesPhase` form used by
the closing section. -/
theorem awaitingLockin_reaches_normal (c : Channel)
    (h : c.phase = ChannelPhase.awaitingLockin) :
    ReachesPhase c ChannelPhase.normal :=
  ⟨{ c with phase := ChannelPhase.normal },
    Reachable.of_step (Step.fundingLocked c h), rfl⟩

/-- Fairness is not a theorem: a schedule that only runs `funding_signed`
keeps the channel in `awaitingLockin` forever. -/
theorem fundingSigned_only_stays_awaitingLockin (c : Channel)
    (hphase : c.phase = ChannelPhase.awaitingLockin) (n : Nat) :
    ∃ cn, runPrefix c (fun _ => ProtocolEvent.fundingSigned) n = some cn ∧
      cn.phase = ChannelPhase.awaitingLockin := by
  induction n with
  | zero => exact ⟨c, rfl, hphase⟩
  | succ n ih =>
      obtain ⟨cn, hrun, hphase'⟩ := ih
      have hstep : step? cn ProtocolEvent.fundingSigned = some cn :=
        step?_complete (Step.fundingSigned cn hphase')
      refine ⟨cn, ?_, hphase'⟩
      rw [runPrefix_succ, hrun]
      simpa using hstep

/-- Consequently the unfair schedule never reaches `normal`. -/
theorem not_eventually_normal_without_fundingLocked (c : Channel)
    (hphase : c.phase = ChannelPhase.awaitingLockin) :
    ¬ Eventually c (fun _ => ProtocolEvent.fundingSigned)
        (fun c => c.phase = ChannelPhase.normal) := by
  rintro ⟨n, cn, hrun, hnormal⟩
  obtain ⟨cn', hrun', hphase'⟩ :=
    fundingSigned_only_stays_awaitingLockin c hphase n
  rw [hrun] at hrun'
  cases hrun'
  rw [hphase'] at hnormal
  simp at hnormal

/-! ## 4. HTLC resolution: fulfil, fail, or timeout -/

/-- The three resolution outcomes the channel can express.  `timedOut` is the
on-chain/expiry outcome; because `HTLCState` has no distinct timeout tag, it
is represented by removal from the commitment (`HTLCState.removed`). -/
inductive Resolution where
  | fulfilled
  | failed
  | timedOut
deriving Repr, DecidableEq, BEq

/-- The commitment state produced by a resolution. -/
def Resolution.toState : Resolution → HTLCState
  | .fulfilled => HTLCState.fulfilled
  | .failed => HTLCState.failed
  | .timedOut => HTLCState.removed

/-- One resolution step of a single HTLC.  It is enabled exactly when the
HTLC is still pending (`offered` or `received`); this mirrors the BOLT 2
requirement that only in-flight HTLCs can be settled
(`refs/bolts/02-peer-protocol.md:2913-2960`). -/
inductive Resolves : HTLC → Resolution → HTLC → Prop where
  | mk (h : HTLC) (r : Resolution)
      (hp : h.state = HTLCState.offered ∨ h.state = HTLCState.received) :
      Resolves h r { h with state := r.toState }

/-- A resolution leaves no pending HTLC. -/
theorem resolves_not_pending {h h' : HTLC} {r : Resolution}
    (hr : Resolves h r h') : ¬ h'.isPending := by
  cases hr with
  | mk hp =>
      cases r <;> simp [HTLC.isPending, Resolution.toState]

/-- Every pending HTLC has a resolution step for every outcome. -/
theorem pending_htlc_resolves (h : HTLC) (hp : h.isPending) (r : Resolution) :
    ∃ h', Resolves h r h' ∧ ¬ h'.isPending := by
  have hstate : h.state = HTLCState.offered ∨ h.state = HTLCState.received := by
    simpa [HTLC.isPending] using hp
  exact ⟨{ h with state := r.toState }, Resolves.mk h r hstate,
    resolves_not_pending (Resolves.mk h r hstate)⟩

/-- Why a pending HTLC may be resolved: a settlement message eventually
arrives, or an honest timer observes the CLTV expiry.  This is a *Type*, so
the trigger is data used by the proof, not an axiom. -/
inductive HTLCTrigger (h : HTLC) : Type where
  /-- A delivered `update_fulfill_htlc` or `update_fail_htlc`. -/
  | settled (r : Resolution)
      (hok : r = Resolution.fulfilled ∨ r = Resolution.failed) :
      HTLCTrigger h
  /-- The observed chain tip reaches the HTLC's `cltv_expiry`. -/
  | expired (tip : Nat) (hexp : h.cltvExpiry ≤ tip) : HTLCTrigger h

/-- The resolution selected by a trigger. -/
def HTLCTrigger.resolution {h : HTLC} : HTLCTrigger h → Resolution
  | .settled r _ => r
  | .expired _ _ => Resolution.timedOut

/-- An honest timer: the tip function eventually reaches the expiry.  It is a
predicate, never an axiom. -/
def HonestTimer (h : HTLC) (tip : Nat → Nat) : Prop :=
  ∃ n, h.cltvExpiry ≤ tip n

/-- **HTLC liveness (trigger form).**  Given a pending HTLC and one of the
three triggers, the HTLC has a resolution step and is no longer pending. -/
theorem pending_htlc_eventually_resolved (h : HTLC) (hp : h.isPending)
    (trig : HTLCTrigger h) :
    ∃ h', Resolves h trig.resolution h' ∧ ¬ h'.isPending := by
  cases trig with
  | settled r hok => exact pending_htlc_resolves h hp r
  | expired tip hexp => exact pending_htlc_resolves h hp Resolution.timedOut

/-- **HTLC liveness.**  If either a fulfil/fail settlement is eventually
delivered (`delivered : Resolution → Prop`) or an honest timer eventually
observes the expiry, a pending HTLC resolves.  The two disjuncts are the
module's eventual-delivery and honest-timer assumptions. -/
theorem eventual_delivery_or_timeout_resolves (h : HTLC) (hp : h.isPending)
    (delivered : Resolution → Prop) (tip : Nat → Nat)
    (hcase : (∃ r, delivered r ∧
        (r = Resolution.fulfilled ∨ r = Resolution.failed)) ∨
      HonestTimer h tip) :
    ∃ r h', Resolves h r h' ∧ ¬ h'.isPending := by
  rcases hcase with ⟨r, _hdel, hok⟩ | ⟨n, hn⟩
  · exact ⟨r, pending_htlc_resolves h hp r⟩
  · exact ⟨Resolution.timedOut,
      pending_htlc_resolves h hp Resolution.timedOut⟩

/-! ## 5. Reconnect does not strand a channel -/

/-- The five message kinds BOLT 2 requires a node to retain and retransmit
after `channel_reestablish` (`refs/bolts/02-peer-protocol.md:3352-3635`). -/
def retransmittable : MsgKind → Bool
  | .fundingSigned => true
  | .channelReady => true
  | .commitmentSigned => true
  | .revokeAndAck => true
  | .shutdown => true
  | _ => false

@[simp] theorem retransmittable_channelReady :
    retransmittable MsgKind.channelReady = true := rfl

/-- Retaining an outbound message makes it available for `resend`. -/
theorem recordSent_lastSent (c : ChannelRecord) (m : Msg)
    (h : retransmittable m.kind = true) :
    (c.recordSent m).lastSent m.kind = some m := by
  cases m <;>
    simp [Msg.kind, retransmittable, ChannelRecord.recordSent,
      ChannelRecord.lastSent] at h ⊢

/-- Consuming an inbound message never touches the retransmission buffer:
`advanceReceived` only changes the reestablish counters. -/
theorem advanceReceived_lastSent (c : ChannelRecord) (inbound : Msg)
    (k : MsgKind) :
    (c.advanceReceived inbound).lastSent k = c.lastSent k := by
  cases inbound <;> cases k <;>
    simp [Msg.kind, ChannelRecord.advanceReceived, ChannelRecord.lastSent] <;>
    try (split <;> simp)

/-- A whole reconnect inbox cannot erase a retained outbound message. -/
theorem foldl_advanceReceived_lastSent (c : ChannelRecord) (inbox : List Msg)
    (k : MsgKind) :
    (inbox.foldl ChannelRecord.advanceReceived c).lastSent k = c.lastSent k := by
  induction inbox generalizing c with
  | nil => simp
  | cons m rest ih =>
      simp only [List.foldl_cons]
      rw [ih (ChannelRecord.advanceReceived c m), advanceReceived_lastSent]

/-- **No-strand lemma.**  If the retained message is `channel_ready`, then
after any reconnect inbox it is still the message `resend` returns. -/
theorem reconnect_preserves_channelReady (c : ChannelRecord) (m : Msg)
    (h : c.lastChannelReady = some m) (inbox : List Msg) :
    (inbox.foldl ChannelRecord.advanceReceived c).lastSent
        MsgKind.channelReady = some m := by
  rw [foldl_advanceReceived_lastSent]
  simpa [ChannelRecord.lastSent] using h

/-- **Reconnect completion.**  A retained `channel_ready` survives the
inbound `channel_reestablish` and the corresponding channel event is the
legal `funding_locked` step into `normal`.  The joint
`PeerState`/`Channel` transition that would connect the two halves is not
modelled in wave A; this theorem states exactly the two halves that are. -/
theorem reconnect_resend_completes_lockin (ch : Channel) (rec : ChannelRecord)
    (m : Msg) (inbound : Msg)
    (hphase : ch.phase = ChannelPhase.awaitingLockin)
    (hretained : rec.lastChannelReady = some m) :
    ∃ c', Step ch ProtocolEvent.fundingLocked c' ∧
      c'.phase = ChannelPhase.normal ∧
      (rec.advanceReceived inbound).lastSent MsgKind.channelReady = some m := by
  refine ⟨{ ch with phase := ChannelPhase.normal },
    Step.fundingLocked ch hphase, rfl, ?_⟩
  rw [advanceReceived_lastSent]
  simpa [ChannelRecord.lastSent] using hretained

/-- Advance a reestablish record by `k` commitment updates. -/
def advanceCommitments : Nat → ReestablishFields → ReestablishFields
  | 0, r => r
  | k + 1, r => (advanceCommitments k r).afterCommitment

/-- `k` received `commitment_signed` messages advance the counter by exactly
`k`. -/
theorem advanceCommitments_nextCommitmentNumber (k : Nat)
    (r : ReestablishFields) :
    (advanceCommitments k r).nextCommitmentNumber =
      r.nextCommitmentNumber + k := by
  induction k generalizing r with
  | zero => simp [advanceCommitments]
  | succ k ih =>
      simp only [advanceCommitments, ReestablishFields.afterCommitment]
      rw [ih]
      omega

/-- **Reestablish catches up.**  If the peer is ahead, some finite number of
retransmitted `commitment_signed` messages makes the local counter equal to
the peer's.  Together with `reconnect_preserves_channelReady`, this is the
counter-level content of "a disconnect does not permanently strand the
channel". -/
theorem reestablish_catches_up (r target : ReestablishFields)
    (h : r.nextCommitmentNumber ≤ target.nextCommitmentNumber) :
    ∃ k, (advanceCommitments k r).nextCommitmentNumber =
      target.nextCommitmentNumber := by
  refine ⟨target.nextCommitmentNumber - r.nextCommitmentNumber, ?_⟩
  rw [advanceCommitments_nextCommitmentNumber]
  omega

/-! ## 6. Cooperative close -/

/-- `shuttingDown` closes in one legal `closing_signed` step. -/
theorem shuttingDown_reaches_closed (c : Channel)
    (h : c.phase = ChannelPhase.shuttingDown) :
    ReachesPhase c ChannelPhase.closed :=
  ⟨{ c with phase := ChannelPhase.closed },
    Reachable.of_step (Step.closingSigned c h), rfl⟩

/-- A `normal` channel reaches `closed` via `shutdown` then `closing_signed`. -/
theorem normal_reaches_closed (c : Channel)
    (h : c.phase = ChannelPhase.normal) :
    ReachesPhase c ChannelPhase.closed := by
  let c1 : Channel := { c with phase := ChannelPhase.shuttingDown }
  have hs1 : Step c ProtocolEvent.shutdown c1 := Step.shutdown c h
  have hc1 : c1.phase = ChannelPhase.shuttingDown := rfl
  obtain ⟨c2, hr2, hp2⟩ := shuttingDown_reaches_closed c1 hc1
  exact ⟨c2, Reachable.trans (Reachable.of_step hs1) hr2, hp2⟩

/-- A channel in `awaitingLockin` also reaches `closed` when both parties
cooperate: lock in, then shut down, then sign the close. -/
theorem awaitingLockin_reaches_closed (c : Channel)
    (h : c.phase = ChannelPhase.awaitingLockin) :
    ReachesPhase c ChannelPhase.closed := by
  let c1 : Channel := { c with phase := ChannelPhase.normal }
  have hs1 : Step c ProtocolEvent.fundingLocked c1 :=
    Step.fundingLocked c h
  have hc1 : c1.phase = ChannelPhase.normal := rfl
  obtain ⟨c2, hr2, hp2⟩ := normal_reaches_closed c1 hc1
  exact ⟨c2, Reachable.trans (Reachable.of_step hs1) hr2, hp2⟩

/-- From `negotiating`, the entire lifecycle to `closed` is reachable. -/
theorem negotiating_reaches_closed (c : Channel)
    (h : c.phase = ChannelPhase.negotiating) :
    ReachesPhase c ChannelPhase.closed := by
  let c1 : Channel := { c with phase := ChannelPhase.awaitingLockin }
  have hs1 : Step c ProtocolEvent.fundingCreated c1 :=
    Step.fundingCreated c h
  have hc1 : c1.phase = ChannelPhase.awaitingLockin := rfl
  obtain ⟨c2, hr2, hp2⟩ := awaitingLockin_reaches_closed c1 hc1
  exact ⟨c2, Reachable.trans (Reachable.of_step hs1) hr2, hp2⟩

/-- **Cooperative-close scheduler theorem.**  Once the channel is
`shuttingDown` and no scheduled event is lost, the very first scheduled step
must be `closing_signed` (it is the only legal event in that phase), so some
finite prefix reaches `closed`. -/
theorem noLoss_shuttingDown_eventually_closed (c : Channel) (σ : Scheduler)
    (hphase : c.phase = ChannelPhase.shuttingDown)
    (hnoLoss : NoLoss c σ) :
    Eventually c σ (fun c => c.phase = ChannelPhase.closed) := by
  obtain ⟨c1, h1⟩ := hnoLoss 1
  have hstep : step? c (σ 0) = some c1 := by
    simpa [runPrefix] using h1
  have hs : Step c (σ 0) c1 := step?_sound hstep
  have hclosed : c1.phase = ChannelPhase.closed := by
    generalize he : σ 0 = e at hs
    cases hs <;> simp_all
  exact ⟨1, c1, h1, hclosed⟩

/-! ## 7. Structural facts used by the report -/

theorem phaseRank_closed_eq : phaseRank ChannelPhase.closed = 4 := rfl

theorem retransmittable_five :
    (List.filter retransmittable
      [MsgKind.fundingSigned, MsgKind.channelReady, MsgKind.commitmentSigned,
       MsgKind.revokeAndAck, MsgKind.shutdown, MsgKind.init]).length = 5 := rfl

end LnLean.Proofs.Liveness
