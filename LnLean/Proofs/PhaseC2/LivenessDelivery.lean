import LnLean.Proofs.Liveness
import LnLean.Proofs.Channel.StateMachineProps

/-!
# LnLean.Proofs.PhaseC2.LivenessDelivery

English claim.  This module composes the channel-liveness result with the
HTLC-liveness result:

* under a loss-free, fair scheduler a channel in `awaitingLockin` eventually
  reaches the `normal` phase;
* under an eventual settlement delivery or an honest timer a pending HTLC has
  a resolution step, after which it is no longer pending.

The composed theorem states that, for a pending HTLC that belongs to a channel
in `awaitingLockin`, the two eventualities hold together: some finite prefix of
the schedule reaches `normal` while the HTLC is resolved by a *triggered*
resolution (either a delivered fulfil/fail or an honest CLTV timer).  The
fairness and timer assumptions are explicit parameters, never axioms.

The module also proves the contrapositive: if a pending HTLC is never resolved
by such a triggered resolution, then either the scheduler is not fair for
`funding_locked` or the timer is not honest.

BOLT sections (pinned BOLTs `1aadb71`).
* BOLT 2 §"Channel Establishment v1", `refs/bolts/02-peer-protocol.md:629-1136`;
  the `channel_ready` message at `:1046-1136` enters normal operation.
* BOLT 2 §"Normal Operation", `refs/bolts/02-peer-protocol.md:2532-3351`;
  removing an HTLC with `update_fulfill_htlc` / `update_fail_htlc` at
  `:2913-3042`.

rust-lightning anchors at `fe4900930c6bd5786ec4203274d7cf312776a5a6`.
* `lightning/src/ln/channelmanager.rs:13108` `internal_channel_ready` and
  `:13140` `internal_channel_ready_with_funded_channel` — lock-in dispatch.
* `lightning/src/ln/channelmanager.rs:9540` `timer_tick_occurred` — the timer
  that drives expiry-related work.
* `lightning/src/ln/channelmanager.rs:13421` `internal_update_fulfill_htlc`
  and `:13504` `internal_update_fail_htlc` — settlement dispatch.

What is NOT modelled.
* Wall-clock time and an actual timer.  `HonestTimer` is a predicate over an
  uninterpreted tip function, exactly as in `LnLean.Proofs.Liveness`.
* A joint transition that removes an HTLC from `Channel.htlcs`.  `Step` leaves
  the HTLC list unchanged; resolution is the separate relation `Resolves`.
  The channel-state half and the HTLC-resolution half are therefore composed
  at the level of existential facts over the same fair schedule, not by a
  single joint transition.
* Message-to-event mapping, lossy links, commitment-handshake liveness, and
  on-chain mechanics.  These gaps are inherited from the source module.
-/

namespace LnLean.Proofs.PhaseC2

set_option autoImplicit false

open LnLean
open LnLean.Channel
open LnLean.Proofs.Liveness

/-! ## Structural facts about the channel schedule -/

/-- Every channel step preserves the HTLC list.  In this model HTLC
resolution is expressed by `Resolves` on an `HTLC`, not by a `Step` that
removes an element from `Channel.htlcs`. -/
theorem step_htlcs_eq {c c' : Channel} {e : ProtocolEvent}
    (hs : Step c e c') : c'.htlcs = c.htlcs := by
  cases hs <;> rfl

/-- A successful finite schedule prefix preserves the HTLC list. -/
theorem runPrefix_htlcs {c c' : Channel} {σ : Scheduler} {n : Nat}
    (hrun : runPrefix c σ n = some c') : c'.htlcs = c.htlcs := by
  induction n generalizing c c' with
  | zero =>
      simp only [runPrefix, Option.some.injEq] at hrun
      subst hrun
      rfl
  | succ n ih =>
      rw [runPrefix_succ] at hrun
      cases hstep : runPrefix c σ n with
      | none => simp [hstep] at hrun
      | some cn =>
          simp only [hstep, Option.bind_some] at hrun
          rw [step_htlcs_eq (step?_sound hrun)]
          exact ih hstep

/-- Membership in the channel's HTLC list is preserved along a successful
prefix. -/
theorem runPrefix_mem_htlcs {c c' : Channel} {σ : Scheduler} {n : Nat}
    {h : HTLC} (hrun : runPrefix c σ n = some c')
    (hmem : h ∈ c.htlcs) : h ∈ c'.htlcs := by
  rw [runPrefix_htlcs hrun]
  exact hmem

/-! ## Triggered resolutions -/

/-- A resolution together with the evidence that justifies it: either a
delivered settlement (`fulfilled` or `failed`) or an honest timer for the
HTLC's CLTV expiry (yielding `timedOut`).  The target HTLC is no longer
pending.  This is the HTLC-liveness payload used by the composition. -/
def TriggeredResolution (h : HTLC) (delivered : Resolution → Prop)
    (tip : Nat → Nat) (r : Resolution) (h' : HTLC) : Prop :=
  Resolves h r h' ∧ ¬ h'.isPending ∧
    ((delivered r ∧
        (r = Resolution.fulfilled ∨ r = Resolution.failed)) ∨
      (r = Resolution.timedOut ∧ HonestTimer h tip))

/-- The composed eventual property: along the fair schedule the channel reaches
`normal` while the HTLC is still in its HTLC list and is resolved by a
triggered resolution. -/
def EventuallyResolved (c : Channel) (σ : Scheduler) (h : HTLC)
    (delivered : Resolution → Prop) (tip : Nat → Nat) : Prop :=
  ∃ n c' r h', runPrefix c σ n = some c' ∧
    c'.phase = ChannelPhase.normal ∧ h ∈ c'.htlcs ∧
    TriggeredResolution h delivered tip r h'

/-- **Triggered HTLC resolution.**  A pending HTLC resolves with a witness for
the trigger: a delivered fulfil/fail settlement, or an honest timer that
observes the CLTV expiry. -/
theorem triggered_resolution_of_delivery_or_timer
    {h : HTLC} (hp : h.isPending) (delivered : Resolution → Prop)
    (tip : Nat → Nat)
    (hcase : (∃ r, delivered r ∧
        (r = Resolution.fulfilled ∨ r = Resolution.failed)) ∨
      HonestTimer h tip) :
    ∃ r h', TriggeredResolution h delivered tip r h' := by
  rcases hcase with ⟨r, hdel, hok⟩ | htimer
  · obtain ⟨h', hres, hnp⟩ := pending_htlc_resolves h hp r
    exact ⟨r, h', hres, hnp, Or.inl ⟨hdel, hok⟩⟩
  · obtain ⟨h', hres, hnp⟩ :=
      pending_htlc_resolves h hp Resolution.timedOut
    exact ⟨Resolution.timedOut, h', hres, hnp, Or.inr ⟨rfl, htimer⟩⟩

/-! ## The composition -/

/-- **End-to-end eventual HTLC resolution.**  Suppose a channel starts in
`awaitingLockin`, the scheduler is loss-free and fair for `funding_locked`
(so it eventually reaches `normal`), and the pending HTLC is in the channel's
HTLC list.  If the HTLC has either a delivered fulfil/fail settlement or an
honest timer, then some finite prefix reaches `normal` with the HTLC still in
the channel and resolved by the corresponding trigger.  The fairness and timer
hypotheses are explicit parameters. -/
theorem pending_htlc_eventually_resolved_of_fair_scheduler_and_honest_timer
    (c : Channel) (σ : Scheduler) (h : HTLC)
    (delivered : Resolution → Prop) (tip : Nat → Nat)
    (hphase : c.phase = ChannelPhase.awaitingLockin)
    (hnoLoss : NoLoss c σ)
    (hfair : Fair σ ProtocolEvent.fundingLocked)
    (hmem : h ∈ c.htlcs)
    (hp : h.isPending)
    (hcase : (∃ r, delivered r ∧
        (r = Resolution.fulfilled ∨ r = Resolution.failed)) ∨
      HonestTimer h tip) :
    EventuallyResolved c σ h delivered tip := by
  obtain ⟨n, cn, hrun, hnormal⟩ :=
    fair_awaitingLockin_eventually_normal c σ hphase hnoLoss hfair
  obtain ⟨r, h', htrig⟩ :=
    triggered_resolution_of_delivery_or_timer hp delivered tip hcase
  exact ⟨n, cn, r, h', hrun, hnormal,
    runPrefix_mem_htlcs hrun hmem, htrig⟩

/-- The same composition stated directly over the source HTLC-liveness theorem
`eventual_delivery_or_timeout_resolves`: it returns a resolution without the
trigger witness.  This is the weakest, most reusable form of the composition. -/
theorem pending_htlc_eventually_resolved_of_fair_and_delivery_or_timeout
    (c : Channel) (σ : Scheduler) (h : HTLC)
    (delivered : Resolution → Prop) (tip : Nat → Nat)
    (hphase : c.phase = ChannelPhase.awaitingLockin)
    (hnoLoss : NoLoss c σ)
    (hfair : Fair σ ProtocolEvent.fundingLocked)
    (hmem : h ∈ c.htlcs)
    (hp : h.isPending)
    (hcase : (∃ r, delivered r ∧
        (r = Resolution.fulfilled ∨ r = Resolution.failed)) ∨
      HonestTimer h tip) :
    ∃ n c' r h', runPrefix c σ n = some c' ∧
      c'.phase = ChannelPhase.normal ∧ h ∈ c'.htlcs ∧
      Resolves h r h' ∧ ¬ h'.isPending := by
  obtain ⟨n, cn, hrun, hnormal⟩ :=
    fair_awaitingLockin_eventually_normal c σ hphase hnoLoss hfair
  obtain ⟨r, h', hres, hnp⟩ :=
    eventual_delivery_or_timeout_resolves h hp delivered tip hcase
  exact ⟨n, cn, r, h', hrun, hnormal,
    runPrefix_mem_htlcs hrun hmem, hres, hnp⟩

/-- **Fulfilled or timed out.**  If a fair scheduler reaches `normal` and the
only allowed settlement is a fulfilled delivery, while otherwise the timer is
honest, then the pending HTLC is eventually fulfilled or timed out. -/
theorem pending_htlc_eventually_fulfilled_or_timedout_of_fair_scheduler_and_honest_timer
    (c : Channel) (σ : Scheduler) (h : HTLC)
    (delivered : Resolution → Prop) (tip : Nat → Nat)
    (hphase : c.phase = ChannelPhase.awaitingLockin)
    (hnoLoss : NoLoss c σ)
    (hfair : Fair σ ProtocolEvent.fundingLocked)
    (hmem : h ∈ c.htlcs)
    (hp : h.isPending)
    (hcase : delivered Resolution.fulfilled ∨ HonestTimer h tip) :
    ∃ n c' r h', runPrefix c σ n = some c' ∧
      c'.phase = ChannelPhase.normal ∧ h ∈ c'.htlcs ∧
      Resolves h r h' ∧ ¬ h'.isPending ∧
      (r = Resolution.fulfilled ∨ r = Resolution.timedOut) := by
  obtain ⟨n, cn, hrun, hnormal⟩ :=
    fair_awaitingLockin_eventually_normal c σ hphase hnoLoss hfair
  have hmem' : h ∈ cn.htlcs := runPrefix_mem_htlcs hrun hmem
  rcases hcase with hdel | htimer
  · obtain ⟨h', hres, hnp⟩ :=
      pending_htlc_resolves h hp Resolution.fulfilled
    exact ⟨n, cn, Resolution.fulfilled, h', hrun, hnormal, hmem',
      hres, hnp, Or.inl rfl⟩
  · obtain ⟨h', hres, hnp⟩ :=
      pending_htlc_resolves h hp Resolution.timedOut
    exact ⟨n, cn, Resolution.timedOut, h', hrun, hnormal, hmem',
      hres, hnp, Or.inr rfl⟩

/-- **Honest-timer corollary.**  With no settlement delivery, an honest timer
alone resolves the pending HTLC by timeout. -/
theorem pending_htlc_eventually_timedout_of_fair_scheduler_and_honest_timer
    (c : Channel) (σ : Scheduler) (h : HTLC)
    (tip : Nat → Nat)
    (hphase : c.phase = ChannelPhase.awaitingLockin)
    (hnoLoss : NoLoss c σ)
    (hfair : Fair σ ProtocolEvent.fundingLocked)
    (hmem : h ∈ c.htlcs)
    (hp : h.isPending)
    (_htimer : HonestTimer h tip) :
    ∃ n c' h', runPrefix c σ n = some c' ∧
      c'.phase = ChannelPhase.normal ∧ h ∈ c'.htlcs ∧
      Resolves h Resolution.timedOut h' ∧ ¬ h'.isPending := by
  obtain ⟨n, cn, hrun, hnormal⟩ :=
    fair_awaitingLockin_eventually_normal c σ hphase hnoLoss hfair
  obtain ⟨h', hres, hnp⟩ :=
    pending_htlc_resolves h hp Resolution.timedOut
  exact ⟨n, cn, h', hrun, hnormal,
    runPrefix_mem_htlcs hrun hmem, hres, hnp⟩

/-! ## Contrapositive -/

/-- **Contrapositive.**  If a pending HTLC in a `awaitingLockin` channel is
never resolved by any triggered resolution along the schedule, then either the
scheduler is not fair for `funding_locked` or the timer is not honest.  This is
the contrapositive of
`pending_htlc_eventually_resolved_of_fair_scheduler_and_honest_timer`; the
loss-free and pending hypotheses are fixed side conditions. -/
theorem pending_htlc_never_resolves_implies_unfair_or_dishonest_timer
    (c : Channel) (σ : Scheduler) (h : HTLC)
    (delivered : Resolution → Prop) (tip : Nat → Nat)
    (hphase : c.phase = ChannelPhase.awaitingLockin)
    (hnoLoss : NoLoss c σ)
    (hmem : h ∈ c.htlcs)
    (hp : h.isPending)
    (hnot : ¬ EventuallyResolved c σ h delivered tip) :
    ¬ Fair σ ProtocolEvent.fundingLocked ∨ ¬ HonestTimer h tip := by
  by_cases hfair : Fair σ ProtocolEvent.fundingLocked
  · right
    intro htimer
    exact hnot
      (pending_htlc_eventually_resolved_of_fair_scheduler_and_honest_timer
        c σ h delivered tip hphase hnoLoss hfair hmem hp (Or.inr htimer))
  · exact Or.inl hfair

end LnLean.Proofs.PhaseC2
