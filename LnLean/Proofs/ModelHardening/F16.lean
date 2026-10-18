import LnLean.Security.Invariants
import LnLean.Security.Model
import LnLean.Proofs.Conservation

/-!
# LnLean.Proofs.ModelHardening.F16

## English claim

Safety and liveness are separated in an asynchronous execution model.

* A **safety** invariant is a state predicate that holds initially and is
  preserved by every transition.  It holds after every finite prefix of every
  schedule, including schedules that never deliver the message that would make
  progress, and including schedules that get stuck on an unavailable step.
  No fairness assumption occurs in the statement.
* A **liveness** claim ("the settlement transition is eventually taken") is
  not a consequence of the transition relation alone.  It needs an explicit
  fairness hypothesis: the scheduler eventually offers the progress label at
  a point where the prefix is executable.  Without it, the drop-all adversary
  (a `NetworkSchedule` whose `delivery` is identically `false`) can stutter
  forever.

The module defines the reusable transition-system and invariant vocabulary,
then instantiates it three times:

1. ledger transitions (`LnLean.Security.Ledger`), where conservation is the
   safety invariant, and an arbitrary `LedgerOp` schedule cannot break it;
2. commitment steps (`LnLean.Proofs.CommitmentConserved`), showing the same
   induction works for the BOLT 3 commitment ledger;
3. a one-message HTLC settlement system, where liveness is proved only under
   the fairness hypothesis and refuted for the drop-all adversary.

## BOLT sections

* BOLT 1 §"Lightning Message Format" — message delivery is asynchronous and
  adversarial.
* BOLT 2 §"Message Retransmission" — retransmission is required precisely
  because delivery is not guaranteed.
* BOLT 2 §"Removing an HTLC" — the `update_fulfill_htlc` /
  `update_fail_htlc` settlement transition is the progress event in the
  concrete liveness instance.
* BOLT 5 §"Revoked Transaction Close Handling" — the on-chain fallback for a
  channel whose off-chain settlement never arrives.

## What is NOT modelled

* No wall clock, no probabilistic scheduler, and no concrete network.  A
  schedule is a function from step indices to transition labels.
* No fairness is derived from the model: every liveness theorem carries the
  fairness hypothesis in its type.
* The settlement state is a two-boolean abstraction of one in-flight HTLC; it
  does not model amounts, preimages, commitment numbers, or retransmission.
* `step?` returns `none` for an unavailable label, so a schedule that selects
  such a label gets stuck.  This is the lossy-link behaviour, not a protocol
  error.
-/

namespace LnLean.Proofs.ModelHardening.F16

open LnLean
open LnLean.Security
open LnLean.Channel
open LnLean.Proofs

set_option autoImplicit false

/-! ## 1. Asynchronous transition systems and invariants -/

/-- A labelled asynchronous transition system.  A schedule picks one label per
step; the transition relation is presented as a partial function because every
protocol transition in the model is deterministic given its label.  A `none`
result means that the label is not enabled in the current state (a dropped or
illegal message). -/
structure AsyncSystem (State Label : Type) where
  /-- The initial state. -/
  start : State
  /-- The transition selected by a label, if the label is enabled. -/
  step? : State → Label → Option State

namespace AsyncSystem

/-- Execution of the first `n` labels of a schedule.  `none` means that some
prefix step was not enabled. -/
def run {State Label : Type} (sys : AsyncSystem State Label)
    (σ : Nat → Label) : Nat → Option State
  | 0 => some sys.start
  | n + 1 => (sys.run σ n).bind (fun s => sys.step? s (σ n))

@[simp] theorem run_zero {State Label : Type} (sys : AsyncSystem State Label)
    (σ : Nat → Label) : sys.run σ 0 = some sys.start := rfl

theorem run_succ {State Label : Type} (sys : AsyncSystem State Label)
    (σ : Nat → Label) (n : Nat) :
    sys.run σ (n + 1) =
      (sys.run σ n).bind (fun s => sys.step? s (σ n)) := rfl

/-- Some finite prefix reaches a state satisfying `Goal`. -/
def Eventually {State Label : Type} (sys : AsyncSystem State Label)
    (σ : Nat → Label) (Goal : State → Prop) : Prop :=
  ∃ n s, sys.run σ n = some s ∧ Goal s

/-- Fairness hypothesis for liveness: the progress label `l` is selected at a
prefix index whose execution is still live.  This is deliberately a
hypothesis, not a theorem about the transition relation. -/
def FairlyScheduled {State Label : Type} (sys : AsyncSystem State Label)
    (σ : Nat → Label) (l : Label) : Prop :=
  ∃ n s, σ n = l ∧ sys.run σ n = some s

end AsyncSystem

/-- A reusable asynchronous transition invariant.  It stores the predicate
together with its initial-state proof and its one-step preservation proof. -/
structure AsyncInvariant {State Label : Type} (sys : AsyncSystem State Label) where
  /-- The state predicate. -/
  pred : State → Prop
  /-- It holds in the initial state. -/
  init : pred sys.start
  /-- It is preserved by every enabled transition. -/
  preserved : ∀ s l s', pred s → sys.step? s l = some s' → pred s'

namespace AsyncInvariant

/-- **Safety by induction, without fairness.**  Every state on every successful
prefix of every schedule satisfies the invariant.  The schedule is universally
quantified; there is no fairness hypothesis anywhere in the type. -/
theorem holds {State Label : Type} {sys : AsyncSystem State Label}
    (inv : AsyncInvariant sys) (σ : Nat → Label) :
    ∀ n s, sys.run σ n = some s → inv.pred s := by
  intro n
  induction n with
  | zero =>
      intro s hrun
      rw [AsyncSystem.run_zero] at hrun
      cases hrun
      exact inv.init
  | succ n ih =>
      intro s hrun
      rw [AsyncSystem.run_succ] at hrun
      cases hn : sys.run σ n with
      | none => simp [hn] at hrun
      | some t =>
          simp only [hn, Option.bind_some] at hrun
          exact inv.preserved t (σ n) s (ih t hn) hrun

/-- Safety in a form that mentions no schedule: all reachable states satisfy
the invariant. -/
theorem safety_without_fairness {State Label : Type}
    {sys : AsyncSystem State Label} (inv : AsyncInvariant sys) :
    ∀ (σ : Nat → Label) (n : Nat) (s : State),
      sys.run σ n = some s → inv.pred s :=
  fun σ => inv.holds σ

/-- **Liveness under an explicit fairness hypothesis.**  If the invariant
implies that either the goal already holds or the progress label `l` is
enabled and leads to the goal, and `l` is fairly scheduled at a live prefix,
then some finite prefix reaches the goal.

The fairness hypothesis is a parameter of the theorem; it is not derivable
from `sys`. -/
theorem eventually_of_fair {State Label : Type}
    {sys : AsyncSystem State Label} (inv : AsyncInvariant sys)
    (σ : Nat → Label) (Goal : State → Prop) (l : Label)
    (hprogress : ∀ s, inv.pred s →
      Goal s ∨ ∃ s', sys.step? s l = some s' ∧ Goal s')
    (hfair : AsyncSystem.FairlyScheduled sys σ l) :
    AsyncSystem.Eventually sys σ Goal := by
  obtain ⟨n, s, hsl, hrun⟩ := hfair
  have hpred : inv.pred s := inv.holds σ n s hrun
  rcases hprogress s hpred with hgoal | ⟨s', hstep, hgoal⟩
  · exact ⟨n, s, hrun, hgoal⟩
  · refine ⟨n + 1, s', ?_, hgoal⟩
    rw [AsyncSystem.run_succ, hrun, hsl]
    simpa using hstep

end AsyncInvariant

/-! ## 2. Safety instances

### 2a. Ledger conservation under an arbitrary operation schedule -/

/-- The asynchronous ledger system: the scheduler chooses a `LedgerOp` at each
step, and an unavailable operation (insufficient balance) stalls the run. -/
def ledgerSystem (l0 : Ledger) : AsyncSystem Ledger LedgerOp where
  start := l0
  step? := fun l op => Ledger.step l op

/-- Conservation is an asynchronous transition invariant of the ledger. -/
def ledgerInvariant (l0 : Ledger) (h0 : l0.Conserves) :
    AsyncInvariant (ledgerSystem l0) where
  pred := Ledger.Conserves
  init := h0
  preserved := by
    intro l op l' hc hstep
    exact Ledger.step_conserves l l' op hc hstep

/-- **Ledger safety without fairness.**  For every operation schedule, every
successful prefix conserves `funding = local + remote + in-flight + fee`.
The theorem applies to unfair schedules (for example, one that repeatedly
selects an unavailable operation) as well as to fair ones. -/
theorem ledger_safety_without_fairness (l0 : Ledger) (h0 : l0.Conserves)
    (σ : Nat → LedgerOp) :
    ∀ n l, (ledgerSystem l0).run σ n = some l → l.Conserves :=
  (ledgerInvariant l0 h0).holds σ

/-! ### 2b. Commitment conservation under asynchronous steps -/

/-- A commitment transition system: every step applies an arbitrary function
to the commitment ledger.  The conservation proof below requires that the
function preserves `CommitmentConserved`, which is the only assumption. -/
def commitmentSystem (start : Commitment) (step : Commitment → Commitment) :
    AsyncSystem Commitment Unit where
  start := start
  step? := fun c _ => some (step c)

/-- Conservation of the BOLT 3 commitment ledger is an asynchronous
transition invariant whenever the step function preserves it. -/
def commitmentInvariant (start : Commitment) (step : Commitment → Commitment)
    (hstart : CommitmentConserved start)
    (hstep : ∀ c, CommitmentConserved c → CommitmentConserved (step c)) :
    AsyncInvariant (commitmentSystem start step) where
  pred := CommitmentConserved
  init := hstart
  preserved := by
    intro c _ c' hc hstep'
    simp only [commitmentSystem, Option.some.injEq] at hstep'
    subst c'
    exact hstep c hc

/-- **Commitment safety without fairness.**  Every prefix of every schedule of
conserving commitment steps keeps the commitment conserving. -/
theorem commitment_safety_without_fairness (start : Commitment)
    (step : Commitment → Commitment) (hstart : CommitmentConserved start)
    (hstep : ∀ c, CommitmentConserved c → CommitmentConserved (step c))
    (σ : Nat → Unit) :
    ∀ n c, (commitmentSystem start step).run σ n = some c →
      CommitmentConserved c :=
  (commitmentInvariant start step hstart hstep).holds σ

/-! ### 2c. The model's `SecurityGame` view of safety -/

/-- The drop-all adversary: no message ever reaches any node.  This is the
canonical adversary used below to show that liveness is not a consequence of
the transition relation. -/
def dropAllSchedule : NetworkSchedule where
  delivery := fun _ _ => false
  partition := fun _ _ => false
  maxDelay := 0
  reorders := true
  dropsMessages := true

/-- The drop-all adversary record, sharing the model's `Adversary` vocabulary. -/
def dropAllAdversary : Adversary where
  schedule := dropAllSchedule
  corruption := .none
  corrupted := []
  reorgDepth := 0
  reorgBudget := 0
  fees := { base := ⟨0⟩, atHeight := fun _ => ⟨0⟩, spikeAt := none }
  learnsPreimages := false
  adaptive := false

/-- A `SecurityGame` over the ledger in which the adversary's schedule chooses
one `LedgerOp` per step.  An unavailable operation is totalised as a stutter,
so the run function is total as required by `SecurityGame`. -/
def ledgerGame (l0 : Ledger) (σ : Nat → LedgerOp) : SecurityGame Ledger where
  adversary := dropAllAdversary
  init := l0
  step := fun l _ n =>
    match Ledger.step l (σ n) with
    | some l' => l'
    | none => l
  bad := fun l => ¬ l.Conserves
  honest := [0, 1]

/-- Every state of a `ledgerGame` run conserves value. -/
theorem ledgerGame_run_conserves (l0 : Ledger) (σ : Nat → LedgerOp)
    (h0 : l0.Conserves) :
    ∀ n, ((ledgerGame l0 σ).run n).Conserves := by
  intro n
  induction n with
  | zero =>
      simpa [SecurityGame.run, ledgerGame] using h0
  | succ n ih =>
      rw [SecurityGame.run_succ]
      dsimp only [ledgerGame]
      split
      · rename_i l' hstep
        exact Ledger.step_conserves _ l' _ ih hstep
      · exact ih

/-- **`Secure` without fairness.**  For every operation schedule, the ledger
game never reaches a non-conserving state.  `Secure` quantifies over all finite
horizons and therefore needs no fairness hypothesis. -/
theorem ledgerGame_secure (l0 : Ledger) (σ : Nat → LedgerOp)
    (h0 : l0.Conserves) : Secure (ledgerGame l0 σ) := by
  intro n
  unfold Winning AdversaryWins
  intro hbad
  exact hbad (ledgerGame_run_conserves l0 σ h0 n)

/-! ## 3. Liveness needs an explicit fairness hypothesis

The parent obligation `LN-SEC-ASYNC` is discharged by the pair of results
below: a conditional liveness theorem and a mechanised drop-all adversary
that refutes the unconditional form. -/

-- OBLIGATION: LN-WF-F16

/-- Abstract state of one in-flight HTLC settlement.  `pending` records that
the settle event has not been taken; `settled` records that it has. -/
structure SettlementState where
  pending : Bool
  settled : Bool
deriving Repr, DecidableEq, BEq

/-- The labels of the settlement system. -/
inductive SettlementLabel where
  /-- Deliver the settlement message and take the HTLC. -/
  | deliver
  /-- No message is delivered at this step (the adversary drops it). -/
  | tick
deriving Repr, DecidableEq, BEq

/-- Initial settlement state: one HTLC is pending and none has settled. -/
def settlementStart : SettlementState :=
  { pending := true, settled := false }

/-- The settlement transition.  `deliver` is enabled exactly while the HTLC is
pending; `tick` is always available and models a dropped message. -/
def settlementStep? : SettlementState → SettlementLabel → Option SettlementState
  | s, .deliver =>
      if s.pending then
        some { s with pending := false, settled := true }
      else
        none
  | s, .tick => some s

/-- The asynchronous settlement system. -/
def settlementSystem : AsyncSystem SettlementState SettlementLabel where
  start := settlementStart
  step? := settlementStep?

/-- Safety invariant: the HTLC value is never silently lost.  It is either
still pending or already settled. -/
def settlementInvariant : AsyncInvariant settlementSystem where
  pred := fun s => s.pending = true ∨ s.settled = true
  init := Or.inl rfl
  preserved := by
    intro s l s' hpred hstep
    cases l with
    | tick =>
        simp only [settlementSystem, settlementStep?, Option.some.injEq] at hstep
        subst s'
        exact hpred
    | deliver =>
        simp only [settlementSystem, settlementStep?] at hstep
        split at hstep
        · rename_i hpending
          cases hstep
          exact Or.inr rfl
        · simp at hstep

/-- **Settlement safety without fairness.**  Every successful prefix of every
schedule keeps the HTLC pending or settled; a dropped message cannot lose it. -/
theorem settlement_safety_without_fairness (σ : Nat → SettlementLabel) :
    ∀ n s, settlementSystem.run σ n = some s →
      s.pending = true ∨ s.settled = true :=
  settlementInvariant.holds σ

/-- **Conditional settlement liveness.**  If the scheduler fairly schedules the
`deliver` label at a live prefix, some finite prefix settles the HTLC.  The
fairness hypothesis is explicit in the type. -/
theorem settlement_live_of_fair (σ : Nat → SettlementLabel)
    (hfair : AsyncSystem.FairlyScheduled settlementSystem σ
      SettlementLabel.deliver) :
    AsyncSystem.Eventually settlementSystem σ (fun s => s.settled = true) := by
  refine settlementInvariant.eventually_of_fair σ
    (fun s => s.settled = true) SettlementLabel.deliver ?_ hfair
  intro s hpred
  rcases hpred with hpending | hsettled
  · refine Or.inr ⟨{ s with pending := false, settled := true }, ?_, rfl⟩
    simp only [settlementSystem, settlementStep?, hpending, ite_true]
  · exact Or.inl hsettled

/-- A scheduler derived from a `NetworkSchedule`: deliver at step `n` exactly
when the adversary allows delivery of message `n` to node `0`; otherwise the
step is a dropped-message tick. -/
def schedulePolicy (ns : NetworkSchedule) (n : Nat) : SettlementLabel :=
  if ns.delivery n 0 then .deliver else .tick

/-- The policy induced by the drop-all schedule is the tick-only scheduler. -/
theorem dropAllSchedule_policy_ticks :
    schedulePolicy dropAllSchedule = fun _ => SettlementLabel.tick := by
  funext n
  simp [schedulePolicy, dropAllSchedule]

/-- The tick-only run never leaves the initial state. -/
theorem tick_only_run (n : Nat) :
    settlementSystem.run (fun _ => SettlementLabel.tick) n =
      some settlementStart := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [AsyncSystem.run_succ, ih]
      rfl

/-- **Drop-all counterexample.**  Under the drop-all adversary the settlement
message is never delivered, so the HTLC never settles.  This is a mechanised
refutation of liveness without fairness. -/
theorem dropAll_never_settles :
    ¬ AsyncSystem.Eventually settlementSystem
        (schedulePolicy dropAllSchedule) (fun s => s.settled = true) := by
  rw [dropAllSchedule_policy_ticks]
  rintro ⟨n, s, hrun, hsettled⟩
  rw [tick_only_run n] at hrun
  cases hrun
  simp [settlementStart] at hsettled

/-- The same counterexample stated with the adversary record from
`LnLean.Security.Model`: the drop-all adversary's schedule never settles. -/
theorem dropAllAdversary_never_settles :
    ¬ AsyncSystem.Eventually settlementSystem
        (schedulePolicy dropAllAdversary.schedule)
        (fun s => s.settled = true) :=
  dropAll_never_settles

/-- **Liveness requires fairness.**  The unconditional statement "every
schedule eventually settles the HTLC" is false; the tick-only schedule is a
counterexample.  Compare `settlement_live_of_fair`, whose fairness hypothesis
rules out exactly this schedule. -/
theorem liveness_requires_fairness :
    ¬ (∀ σ : Nat → SettlementLabel,
        AsyncSystem.Eventually settlementSystem σ (fun s => s.settled = true)) := by
  intro hall
  have htick := hall (fun _ => SettlementLabel.tick)
  exact dropAll_never_settles (by
    rw [dropAllSchedule_policy_ticks]
    exact htick)

/-- The drop-all adversary's schedule indeed delivers nothing. -/
theorem dropAllAdversary_delivers_nothing :
    ∀ i j, dropAllAdversary.schedule.delivery i j = false :=
  fun _ _ => rfl

/-- **Separation summary.**  Safety holds for every schedule, while liveness
holds only under the fairness hypothesis and fails for the drop-all adversary.
This conjunction is the reusable content of `LN-SEC-ASYNC`. -/
theorem safety_fairness_separation (l0 : Ledger) (h0 : l0.Conserves) :
    (∀ (σ : Nat → LedgerOp) (n : Nat) (l : Ledger),
        (ledgerSystem l0).run σ n = some l → l.Conserves) ∧
      (AsyncSystem.FairlyScheduled settlementSystem
          (fun _ => SettlementLabel.deliver) SettlementLabel.deliver →
        AsyncSystem.Eventually settlementSystem
          (fun _ => SettlementLabel.deliver) (fun s => s.settled = true)) ∧
      ¬ AsyncSystem.Eventually settlementSystem
          (schedulePolicy dropAllSchedule) (fun s => s.settled = true) := by
  refine ⟨ledger_safety_without_fairness l0 h0, ?_, dropAll_never_settles⟩
  intro hfair
  exact settlement_live_of_fair _ hfair

end LnLean.Proofs.ModelHardening.F16
