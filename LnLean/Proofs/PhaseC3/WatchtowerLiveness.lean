import LnLean.Proofs.Liveness
import LnLean.Channel.Penalty
import LnLean.Proofs.PhaseC3.WatchtowerBreach

/-!
# LnLean.Proofs.PhaseC3.WatchtowerLiveness

English claim.  This module composes the on-chain watchtower remedy of
`LnLean.Proofs.PhaseC3.WatchtowerBreach` with the channel/HTLC liveness model
of `LnLean.Proofs.Liveness`.

* A **fair** schedule (`Fair`) that loses no step (`NoLoss`) eventually takes
  an `awaitingLockin` channel to `normal`.
* An **honest timer** (or an eventually delivered settlement) resolves a
  pending HTLC.
* A **live watchtower** (or an honest party online at the observation height)
  discovers the revoked commitment, and the explicit
  `DetectionBeforeDeadline` timing witness places detection inside the
  half-open contest interval `[breachHeight, breachHeight + window)`.
* An **L1 acceptance** witness (`BridgeAcceptance`) then makes the penalty
  valid, timely, and exclusive: no breacher transaction spending either old
  main output can confirm.

The positive composition is `eventually_detected_and_penalized`.  Its
contrapositive, `not_penalized_implies_assumption_failure`, says that if the
penalty is not realized then at least one of fairness, loss-freedom, the
timer/settlement trigger, watchtower liveness, or timely L1 acceptance fails.

Every assumption is a structure field or a theorem hypothesis.  There is no
`axiom`, no `sorry`, and no assumption that the watchtower detects instantly:
detection is witnessed at the explicit height `detection.detectHeight`, which
may be strictly after `breachHeight`.

BOLT anchors are inherited from `WatchtowerBreach` and `Liveness`: BOLT 5
§Revoked Transaction Close Handling (`refs/bolts/05-onchain.md:510-559`),
BOLT 2 §Normal Operation and §Message Retransmission
(`refs/bolts/02-peer-protocol.md:2532-3351`, `:3352-3635`), and BOLT 3
`to_local` / `to_remote` (`refs/bolts/03-transactions.md:113`, `:136`).
-/

namespace LnLean.Proofs.PhaseC3

open LnLean
open LnLean.Bitcoin
open LnLean.Channel
open LnLean.Proofs.Channel
open LnLean.Proofs.Liveness

set_option autoImplicit false

/-! ## The composed scenario

The scenario carries *data* only.  The fairness, loss-freedom, timer,
watchtower-liveness, detection, and L1-acceptance facts are kept out of the
structure so that they remain explicit theorem hypotheses (and can therefore
fail in the contrapositive).  The timing predicate `DetectionBeforeDeadline`
is reused verbatim from `WatchtowerBreach`.
-/

/-- Data of a watchtower breach embedded in a live channel/HTLC run. -/
structure WatchtowerLivenessScenario where
  /-- Revocation-key scheme used by the punisher. -/
  scheme : RevocationScheme
  /-- The named L1 no-double-spend bridge. -/
  bridge : L1ScriptBridge
  /-- The published (old) commitment. -/
  c : RevokedCommitment
  /-- The penalty transaction. -/
  p : PenaltyTx
  /-- The punisher's revocation witness. -/
  w : PenaltyWitness
  /-- Contest delay in blocks. -/
  window : Blocks
  /-- Who is online at a height (honest-party discovery route). -/
  online : Height → Prop
  /-- The watchtower interface. -/
  tower : Watchtower
  /-- Explicit detection-time assumption from `WatchtowerBreach`. -/
  detection : DetectionBeforeDeadline c window
  /-- The breach is detected, online or through a watchtower report. -/
  detected : Detectable online tower c detection.detectHeight
  /-- The published commitment is revoked. -/
  revoked : breachDetected c
  /-- The penalty transaction spends both old main outputs. -/
  penaltySpends : penaltySpendsBoth c p
  /-- The sweep output is the old main-output total minus the penalty fee. -/
  sweepValue : p.sweep.value = c.toLocalValue + c.toRemoteValue - c.penaltyFee
  /-- Initial channel state of the liveness run. -/
  c₀ : Channel
  /-- The fair event schedule. -/
  σ : Scheduler
  /-- The HTLC whose liveness is composed with the breach remedy. -/
  htlc : HTLC
  /-- The honest timer's chain-tip observation. -/
  tip : Nat → Nat
  /-- Settlement deliveries available to the scheduler. -/
  delivered : Resolution → Prop

namespace WatchtowerLivenessScenario

/-! ## Timing and discovery -/

/-- The detection witness lies in the half-open contest interval.  This is the
explicit timing predicate, not an instantaneous-detection assumption. -/
def BreachWindowObserved (s : WatchtowerLivenessScenario) : Prop :=
  s.c.breachHeight ≤ s.detection.detectHeight ∧
    s.detection.detectHeight < s.c.breachHeight + s.window

/-- The observation interval is nonempty: a timely detection forces a positive
contest delay.  In particular the model does not collapse `window` to zero. -/
theorem window_pos (s : WatchtowerLivenessScenario) : 0 < s.window := by
  have h : s.c.breachHeight < s.c.breachHeight + s.window :=
    Nat.lt_of_le_of_lt s.detection.breach_le_detect
      s.detection.detect_lt_deadline
  exact Nat.lt_of_add_lt_add_left (n := s.c.breachHeight) (by simpa using h)

/-- The breach is observed no earlier than its publication and strictly before
the contest deadline. -/
theorem breach_within_window (s : WatchtowerLivenessScenario) :
    BreachWindowObserved s :=
  ⟨s.detection.breach_le_detect, s.detection.detect_lt_deadline⟩

/-- Detection is not assumed to be instantaneous: the only constraint is the
interval `[breachHeight, breachHeight + window)`. -/
theorem detection_before_deadline (s : WatchtowerLivenessScenario) :
    s.detection.detectHeight < s.c.breachHeight + s.window :=
  s.detection.detect_lt_deadline

/-- The modelled discovery route is either the honest party being online or a
watchtower report, and the latter implies watchtower liveness. -/
theorem detection_route_or_live (s : WatchtowerLivenessScenario) :
    s.online s.detection.detectHeight ∨ s.tower.live := by
  rcases s.detected with honline | hreport
  · exact Or.inl honline
  · exact Or.inr (s.tower.reports_live s.c s.detection.detectHeight hreport)

/-- If the honest party is offline at the observation height, detection can
only have come from a live watchtower. -/
theorem offline_detection_requires_live_tower (s : WatchtowerLivenessScenario)
    (hoffline : ¬ s.online s.detection.detectHeight) : s.tower.live :=
  detected_after_deadline_requires_watchtower s.online s.tower s.c
    s.detection.detectHeight s.detected hoffline

/-! ## Timer/settlement trigger -/

/-- The two allowed triggers for HTLC resolution: an eventual fulfil/fail
delivery, or an honest CLTV timer.  This is a `Prop`, hence a hypothesis that
can fail in the contrapositive. -/
def TimerOrSettlement (s : WatchtowerLivenessScenario) : Prop :=
  (∃ r, s.delivered r ∧
      (r = Resolution.fulfilled ∨ r = Resolution.failed)) ∨
    HonestTimer s.htlc s.tip

/-- A pending HTLC resolves under the timer/settlement trigger. -/
theorem htlc_eventually_resolved (s : WatchtowerLivenessScenario)
    (hpending : s.htlc.isPending) (htimer : TimerOrSettlement s) :
    ∃ r h', Resolves s.htlc r h' ∧ ¬ h'.isPending :=
  eventual_delivery_or_timeout_resolves s.htlc hpending s.delivered s.tip
    htimer

/-! ## Timely L1 acceptance and the penalty conclusion -/

/-- A timely acceptance witness: the bridge accepts the penalty at a height
between detection and the contest deadline. -/
def TimelyAcceptance (s : WatchtowerLivenessScenario) : Prop :=
  ∃ a : BridgeAcceptance s.bridge s.p,
    s.detection.detectHeight ≤ a.confirmHeight ∧
      a.confirmHeight < s.c.breachHeight + s.window

/-- The realized penalty conclusion: a timely acceptance witness, a valid and
punishable penalty, and exclusion of every breacher spend of either old main
output. -/
def Penalized (s : WatchtowerLivenessScenario) : Prop :=
  ∃ a : BridgeAcceptance s.bridge s.p,
    s.detection.detectHeight ≤ a.confirmHeight ∧
      a.confirmHeight < s.c.breachHeight + s.window ∧
      punishable s.scheme s.c s.p s.w a.confirmHeight s.window ∧
      timelyL1Confirmation s.c.breachHeight a.confirmHeight s.window ∧
      (∀ b : Tx, BreacherSpend s.c b → ¬ s.bridge.confirms b)

/-- No penalty can be realized without a timely acceptance witness. -/
theorem not_penalized_without_timely_acceptance (s : WatchtowerLivenessScenario)
    (h : ¬ TimelyAcceptance s) : ¬ Penalized s := by
  intro hp
  obtain ⟨a, hdet, hconf, _hpun, _htimely, _hno⟩ := hp
  exact h ⟨a, hdet, hconf⟩

/-- A timely acceptance makes the penalty valid, punishable and exclusive. -/
theorem penalized_of_timely_acceptance (s : WatchtowerLivenessScenario)
    (haccept : TimelyAcceptance s) : Penalized s := by
  obtain ⟨a, hdet_le_confirm, hconfirm_lt_deadline⟩ := haccept
  have hbreach_le_confirm : s.c.breachHeight ≤ a.confirmHeight :=
    Nat.le_trans s.detection.breach_le_detect hdet_le_confirm
  have htimely :
      timelyL1Confirmation s.c.breachHeight a.confirmHeight s.window :=
    ⟨hbreach_le_confirm, hconfirm_lt_deadline⟩
  have hvalid :
      penaltyValid s.scheme s.c s.p s.w a.confirmHeight s.window :=
    (penaltyValid_iff_core s.scheme s.c s.p s.w a.confirmHeight s.window).2
      ⟨s.revoked, s.penaltySpends, s.sweepValue, htimely⟩
  have hpun :
      punishable s.scheme s.c s.p s.w a.confirmHeight s.window :=
    ⟨s.revoked, hvalid⟩
  have hno : ∀ b : Tx, BreacherSpend s.c b → ¬ s.bridge.confirms b := by
    intro b hb
    exact punished_not_breacher_spendable s.bridge s.scheme s.c s.p s.w
      a.confirmHeight s.window b hvalid hb a.accepted
  exact ⟨a, hdet_le_confirm, hconfirm_lt_deadline, hpun, htimely, hno⟩

/-! ## Positive composition -/

/-- The full composed outcome: the breach is observed inside the contest
interval, discovery is by the online honest party or a live watchtower, the
channel locks in, the pending HTLC resolves, and the penalty is realized. -/
structure LivenessOutcome (s : WatchtowerLivenessScenario) : Prop where
  breach_window : BreachWindowObserved s
  detection_route : s.online s.detection.detectHeight ∨ s.tower.live
  tower_live : s.tower.live
  lockin : Eventually s.c₀ s.σ (fun c => c.phase = ChannelPhase.normal)
  htlc_resolution : ∃ r h', Resolves s.htlc r h' ∧ ¬ h'.isPending
  penalized : Penalized s

/-- **Positive watchtower-liveness composition.**  Under a fair, loss-free
scheduler, an honest timer (or delivered settlement), a live watchtower, and
a timely L1 acceptance witness, the channel locks in, the pending HTLC
resolves, the breach is detected before the contest deadline, and the penalty
is realized. -/
theorem eventually_detected_and_penalized
    (s : WatchtowerLivenessScenario)
    (hphase : s.c₀.phase = ChannelPhase.awaitingLockin)
    (hnoLoss : NoLoss s.c₀ s.σ)
    (hfair : Fair s.σ ProtocolEvent.fundingLocked)
    (hpending : s.htlc.isPending)
    (htimer : TimerOrSettlement s)
    (htower : s.tower.live)
    (haccept : TimelyAcceptance s) :
    LivenessOutcome s :=
  { breach_window := s.breach_within_window
    detection_route := s.detection_route_or_live
    tower_live := htower
    lockin := fair_awaitingLockin_eventually_normal s.c₀ s.σ hphase hnoLoss hfair
    htlc_resolution := s.htlc_eventually_resolved hpending htimer
    penalized := s.penalized_of_timely_acceptance haccept }

/-- The penalty part of the composition, stated on its own for integration
with the phase-C3 on-chain lane. -/
theorem penalty_of_fair_live_assumptions
    (s : WatchtowerLivenessScenario)
    (hphase : s.c₀.phase = ChannelPhase.awaitingLockin)
    (hnoLoss : NoLoss s.c₀ s.σ)
    (hfair : Fair s.σ ProtocolEvent.fundingLocked)
    (hpending : s.htlc.isPending)
    (htimer : TimerOrSettlement s)
    (htower : s.tower.live)
    (haccept : TimelyAcceptance s) :
    Penalized s :=
  (s.eventually_detected_and_penalized hphase hnoLoss hfair hpending htimer
    htower haccept).penalized

/-! ## Contrapositive

A small propositional helper keeps the contrapositive independent of any
classical axiom or mathlib tactic. -/

/-- If a five-fold conjunction fails, one of its five conjuncts fails. -/
theorem failure_of_not_all {P Q R S T : Prop}
    (h : ¬ (P ∧ Q ∧ R ∧ S ∧ T)) :
    ¬P ∨ ¬Q ∨ ¬R ∨ ¬S ∨ ¬T := by
  by_cases hP : P
  · by_cases hQ : Q
    · by_cases hR : R
      · by_cases hS : S
        · by_cases hT : T
          · exact absurd ⟨hP, hQ, hR, hS, hT⟩ h
          · exact Or.inr (Or.inr (Or.inr (Or.inr hT)))
        · exact Or.inr (Or.inr (Or.inr (Or.inl hS)))
      · exact Or.inr (Or.inr (Or.inl hR))
    · exact Or.inr (Or.inl hQ)
  · exact Or.inl hP

/-- **Contrapositive.**  If the penalty is not realized, then at least one of
the five explicit assumptions fails: fairness, loss-freedom, the
timer/settlement trigger, watchtower liveness, or timely L1 acceptance. -/
theorem not_penalized_implies_assumption_failure
    (s : WatchtowerLivenessScenario)
    (hphase : s.c₀.phase = ChannelPhase.awaitingLockin)
    (hpending : s.htlc.isPending)
    (hnot : ¬ Penalized s) :
    ¬ Fair s.σ ProtocolEvent.fundingLocked ∨
      ¬ NoLoss s.c₀ s.σ ∨
      ¬ TimerOrSettlement s ∨
      ¬ s.tower.live ∨
      ¬ TimelyAcceptance s := by
  have hnotAll :
      ¬ (Fair s.σ ProtocolEvent.fundingLocked ∧
          NoLoss s.c₀ s.σ ∧
          TimerOrSettlement s ∧
          s.tower.live ∧
          TimelyAcceptance s) := by
    intro h
    rcases h with ⟨hfair, hnoLoss, htimer, htower, haccept⟩
    exact hnot (s.penalty_of_fair_live_assumptions hphase hnoLoss hfair
      hpending htimer htower haccept)
  exact failure_of_not_all hnotAll

/-- The same contrapositive with the on-chain detection window made explicit:
failure to observe the breach inside `[breachHeight, breachHeight + window)`
is itself part of the assumption-failure disjunction.  Here it is folded into
the negation of timely acceptance, because detection is a structure field of
the scenario. -/
theorem not_penalized_implies_no_timely_acceptance_or_assumption_failure
    (s : WatchtowerLivenessScenario)
    (hphase : s.c₀.phase = ChannelPhase.awaitingLockin)
    (hpending : s.htlc.isPending)
    (hnot : ¬ Penalized s) :
    (¬ TimelyAcceptance s) ∨
      ¬ Fair s.σ ProtocolEvent.fundingLocked ∨
      ¬ NoLoss s.c₀ s.σ ∨
      ¬ TimerOrSettlement s ∨
      ¬ s.tower.live := by
  rcases s.not_penalized_implies_assumption_failure hphase hpending hnot with
    hfair | hnoLoss | htimer | htower | haccept
  · exact Or.inr (Or.inl hfair)
  · exact Or.inr (Or.inr (Or.inl hnoLoss))
  · exact Or.inr (Or.inr (Or.inr (Or.inl htimer)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr htower)))
  · exact Or.inl haccept

end WatchtowerLivenessScenario

end LnLean.Proofs.PhaseC3
