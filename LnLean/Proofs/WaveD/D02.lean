import LnLean.Bitcoin.Funding
import LnLean.Bitcoin.Laws
import LnLean.Bitcoin.ScriptTemplates
import LnLean.Bitcoin.Seam
import LnLean.Channel.Commitment
import LnLean.Channel.HTLC
import LnLean.Security.Model
import LnLean.Security.Invariants

/-!
# LnLean.Proofs.WaveD.D02

**English claim (catalog `LN-L1-003`).**  Channel safety is preserved for
reorgs within the adversary's depth budget, and deep reorgs are a separate
failure mode.

This module makes the claim precise against the wave-A model:

* `LnLean.Security.Adversary.reorgAllowed a r` is definitionally
  `r.depth ≤ a.reorgBudget`; it is only an *allowance*, not a claim that the
  channel survives the reorg.
* An on-chain resolution observed at height `h` with tip `t` has
  `t + 1 - h` confirmations.  A reorg of depth `d` retains the block at `h`
  exactly when `d < confirmationCount t h`, i.e. `h + d ≤ t`.
* A `ChannelReorgState` carries the observed tip, the in-channel ledger, and
  the list of on-chain resolutions the channel relies on.  Its safety
  invariant `Safe a` is (i) `Ledger.Conserves` and (ii) every resolution is
  deeper than *every* reorg the adversary is allowed to perform
  (`a.reorgBudget < confirmationCount s.tip e.height`).

The main positive result is `waveD_d02_safe_preserved`: every allowed reorg
leaves a safe channel state safe, because it evicts none of the resolutions.
The bridge `waveD_d02_safety_preserved_within_anti_reorg_delay` turns the
protocol's anti-reorg assumption `a.reorgBudget < antiReorgDelay` into that
invariant.  Both results are *conditional on the depth bound*: the model's
`reorgAllowed` has no upper bound on `reorgBudget`, and
`waveD_d02_settled_claim_evicted_by_allowed_reorg` exhibits a channel whose
resolutions have the full `ANTI_REORG_DELAY` confirmations and an allowed
reorg that nevertheless evicts one.  `waveD_d02_deep_reorg_separate_failure_mode`
shows that *every* reorg at or beyond that delay breaks some maximally
settled channel, and `waveD_d02_no_finite_confirmation_depth` shows that no
finite confirmation count defeats an unbounded reorg.

BOLT anchor.  BOLT 5 §"HTLC Output Handling" (`05-onchain.md:300-304` and
`:467-471`): the decision to fail an upstream HTLC back "depends on the
possibility of a blockchain reorganization that swaps out the confirmed
commitment transaction"; a reorganization delay is required otherwise.
This is mechanised as `waveD_d02_safeToBackFail` and its two theorems.

LDK anchor.  `lightning/src/chain/channelmonitor.rs:514` documents
`OnchainEventEntry` as the record "used to determine when the on-chain event
can be considered safe from a chain reorganization".
`channelmonitor.rs:347` fixes `ANTI_REORG_DELAY = 6` and states the
library-wide assumption: "If a reorg deeper than this number of blocks
occurs, counterparties may be able to steal funds or claims made by and
balances exposed by a `ChannelMonitor` may be incorrect."  That comment is
the reason the preservation theorem cannot be unconditional, and
`antiReorgDelay` below is the model's copy of the constant.

What is *not* modelled.  `Reorg` in the wave-A model has only a depth, a
`fromHeight`, and opaque replacement-tip bytes; there is no L1 consensus and
no transaction-level spend semantics.  Consequently this file proves
*eviction* of a resolution, not actual theft: the latter would need the L1
transaction and script model (`Bitcoin.Data.*`) plus the channel monitor's
broadcast logic.  The replacement chain's new height is not modelled either,
so survival is evaluated at the observed tip (the model explicitly says only
the depth matters).  The ledger is assumed unchanged by an in-budget reorg;
what changes is which on-chain resolutions remain observable.
-/

namespace LnLean.Proofs.WaveD.D02

open LnLean
open LnLean.Security

set_option autoImplicit false

-- OBLIGATION: LN-WD-D02

/-! ## 1. The anti-reorg delay and confirmation arithmetic -/

/-- LDK's `ANTI_REORG_DELAY` (`channelmonitor.rs:347`): the number of blocks
the channel monitor waits before treating an on-chain resolution as safe
from a reorganisation.  The value is the pinned LDK constant at commit
`fe49009`. -/
abbrev antiReorgDelay : Nat := 6

theorem waveD_d02_antiReorgDelay_eq : antiReorgDelay = 6 := rfl

theorem waveD_d02_antiReorgDelay_pos : 0 < antiReorgDelay := by
  decide

/-- Number of confirmations of the block at height `h` when the observed tip
is `t`.  A block at the tip has one confirmation; the truncated subtraction
gives zero for heights above the tip (not yet observed). -/
abbrev confirmationCount (tip h : Height) : Nat := tip + 1 - h

theorem waveD_d02_confirmations_self (tip : Height) :
    confirmationCount tip tip = 1 := by
  unfold confirmationCount
  omega

theorem waveD_d02_confirmations_mono {tip tip' : Height} (h : tip ≤ tip')
    (height : Height) : confirmationCount tip height ≤ confirmationCount tip' height := by
  unfold confirmationCount
  exact Nat.sub_le_sub_right (Nat.succ_le_succ h) height

/-- A reorg of depth `r.depth` removes the last `r.depth` blocks below the
observed tip.  The block at height `h` is retained exactly when its
confirmation count exceeds the reorg depth. -/
abbrev reorgSurvives (r : Reorg) (tip h : Height) : Prop :=
  r.depth < confirmationCount tip h

/-- The confirmation-count formulation is the same as the height arithmetic:
retention means that the reorg does not reach `h`. -/
theorem waveD_d02_survives_iff {r : Reorg} {tip h : Height} :
    reorgSurvives r tip h ↔ h + r.depth ≤ tip := by
  unfold reorgSurvives confirmationCount
  rw [Nat.lt_sub_iff_add_lt, Nat.add_comm r.depth h, Nat.lt_succ_iff]

/-- A shallower reorg is at least as harmless as a deeper one. -/
theorem waveD_d02_survives_of_le_depth {r r' : Reorg} {tip h : Height}
    (hd : r.depth ≤ r'.depth) (hr : reorgSurvives r' tip h) :
    reorgSurvives r tip h :=
  Nat.lt_of_le_of_lt hd hr

/-! ## 2. On-chain resolutions and the channel reorg state -/

/-- An on-chain event the channel relies on (a funding confirmation, a
commitment spend, or an HTLC claim/fail transaction).  `amount` is the value
whose disposition depends on the event. -/
structure OnchainEvent where
  height : Height
  amount : Msat
deriving Repr

/-- Confirmations accumulated by the event at the observed tip. -/
abbrev OnchainEvent.confirmations (e : OnchainEvent) (tip : Height) : Nat :=
  confirmationCount tip e.height

/-- Does the event's block survive the reorg? -/
abbrev OnchainEvent.survives (e : OnchainEvent) (r : Reorg) (tip : Height) : Prop :=
  reorgSurvives r tip e.height

/-- The event has reached LDK's anti-reorg delay and is treated as settled by
the channel monitor. -/
abbrev OnchainEvent.settled (e : OnchainEvent) (tip : Height) : Prop :=
  antiReorgDelay ≤ e.confirmations tip

/-- The part of a channel that a reorg can affect in this model: the observed
tip, the in-channel ledger, and the on-chain resolutions the channel relies
on.  (`LnLean.Security.ChannelState` is the unrelated wave-A commitment
state machine, hence the distinct name.) -/
structure ChannelReorgState where
  tip : Height
  ledger : Ledger
  resolutions : List OnchainEvent
deriving Repr

/-- Every resolution has reached the anti-reorg delay. -/
def ChannelReorgState.OnchainSafe (s : ChannelReorgState) : Prop :=
  ∀ e ∈ s.resolutions, e.settled s.tip

/-- Every resolution is deeper than every reorg the adversary is allowed to
perform.  This is the budget-relative safety invariant. -/
def ChannelReorgState.OutOfReorgReach (s : ChannelReorgState)
    (a : Adversary) : Prop :=
  ∀ e ∈ s.resolutions, a.reorgBudget < e.confirmations s.tip

/-- Channel safety: value is conserved in the ledger and every on-chain fact
the channel depends on is out of reach of the adversary's reorg budget. -/
def ChannelReorgState.Safe (s : ChannelReorgState) (a : Adversary) : Prop :=
  s.ledger.Conserves ∧ s.OutOfReorgReach a

/-- Apply a reorg: resolutions whose block is no longer on the new chain are
evicted; the surviving observations remain.  The replacement chain's height
is not part of the wave-A `Reorg` record, so the observed tip `s.tip` is kept
for confirmation accounting. -/
def ChannelReorgState.applyReorg (s : ChannelReorgState) (r : Reorg) :
    ChannelReorgState :=
  { s with
    resolutions := s.resolutions.filter (fun e => decide (e.survives r s.tip)) }

theorem waveD_d02_applyReorg_tip (s : ChannelReorgState) (r : Reorg) :
    (s.applyReorg r).tip = s.tip := rfl

theorem waveD_d02_applyReorg_ledger (s : ChannelReorgState) (r : Reorg) :
    (s.applyReorg r).ledger = s.ledger := rfl

/-- The in-channel ledger is not rewritten by a reorg, so conservation is
preserved. -/
theorem waveD_d02_ledger_conserves_after_reorg (s : ChannelReorgState)
    (r : Reorg) (h : s.ledger.Conserves) : (s.applyReorg r).ledger.Conserves := by
  simpa [ChannelReorgState.applyReorg] using h

/-! ## 3. The positive result: allowed reorgs preserve a safe channel -/

/-- A resolution out of the whole reorg budget survives every allowed reorg.
This is the arithmetic core of the preservation theorem. -/
theorem waveD_d02_event_survives {s : ChannelReorgState} {a : Adversary}
    {r : Reorg} {e : OnchainEvent} (he : e ∈ s.resolutions)
    (hreach : s.OutOfReorgReach a) (hallowed : a.reorgAllowed r) :
    e.survives r s.tip := by
  have hbudget : a.reorgBudget < e.confirmations s.tip := hreach e he
  have hdepth : r.depth ≤ a.reorgBudget := hallowed
  exact Nat.lt_of_le_of_lt hdepth hbudget

/-- No resolution is filtered out by an allowed reorg when the channel state
is out of the adversary's reorg reach. -/
theorem waveD_d02_applyReorg_resolutions {s : ChannelReorgState}
    {a : Adversary} {r : Reorg} (hreach : s.OutOfReorgReach a)
    (hallowed : a.reorgAllowed r) :
    (s.applyReorg r).resolutions = s.resolutions := by
  unfold ChannelReorgState.applyReorg
  apply List.filter_eq_self.mpr
  intro e he
  have hsurv : e.survives r s.tip :=
    waveD_d02_event_survives he hreach hallowed
  simp [hsurv]

/-- **Main theorem.**  A channel that conserves value and whose on-chain
resolutions are deeper than every reorg the adversary may perform stays safe
after any allowed reorg. -/
theorem waveD_d02_safe_preserved {s : ChannelReorgState} {a : Adversary}
    {r : Reorg} (hsafe : s.Safe a) (hallowed : a.reorgAllowed r) :
    (s.applyReorg r).Safe a := by
  obtain ⟨hconserves, hreach⟩ := hsafe
  refine ⟨?_, ?_⟩
  · exact waveD_d02_ledger_conserves_after_reorg s r hconserves
  · intro e he
    have hres := waveD_d02_applyReorg_resolutions hreach hallowed
    have he' : e ∈ s.resolutions := by
      rwa [hres] at he
    simpa [ChannelReorgState.applyReorg] using hreach e he'

/-- A settled channel is out of reach of any adversary whose whole budget is
below the anti-reorg delay. -/
theorem waveD_d02_outOfReorgReach_of_settled {s : ChannelReorgState}
    {a : Adversary} (hsettled : s.OnchainSafe)
    (hbudget : a.reorgBudget < antiReorgDelay) : s.OutOfReorgReach a := by
  intro e he
  exact Nat.lt_of_lt_of_le hbudget (hsettled e he)

/-- **The catalog claim, in its true conditional form.**  Under LDK's
library-wide assumption that the adversary's reorg budget is smaller than
`ANTI_REORG_DELAY`, every allowed reorg preserves channel safety. -/
theorem waveD_d02_safety_preserved_within_anti_reorg_delay
    {s : ChannelReorgState} {a : Adversary} {r : Reorg}
    (hconserves : s.ledger.Conserves) (hsettled : s.OnchainSafe)
    (hbudget : a.reorgBudget < antiReorgDelay) (hallowed : a.reorgAllowed r) :
    (s.applyReorg r).Safe a := by
  exact waveD_d02_safe_preserved
    ⟨hconserves, waveD_d02_outOfReorgReach_of_settled hsettled hbudget⟩ hallowed

/-- The event-level form of the same statement: a resolution that has reached
the anti-reorg delay survives every allowed reorg. -/
theorem waveD_d02_settled_survives_allowed {s : ChannelReorgState}
    {a : Adversary} {r : Reorg} {e : OnchainEvent}
    (he : e ∈ s.resolutions) (hsettled : s.OnchainSafe)
    (hbudget : a.reorgBudget < antiReorgDelay) (hallowed : a.reorgAllowed r) :
    e.survives r s.tip :=
  waveD_d02_event_survives he
    (waveD_d02_outOfReorgReach_of_settled hsettled hbudget) hallowed

/-! ## 4. The boundary is tight: a counterexample at the delay -/

/-- A channel with one resolution that has exactly `ANTI_REORG_DELAY = 6`
confirmations at tip 5 (event height 0). -/
abbrev waveD_d02_settledState : ChannelReorgState :=
  { tip := 5
    ledger :=
      { funding := ⟨1000⟩
        localBalance := ⟨600⟩
        remoteBalance := ⟨400⟩
        inFlight := ⟨0⟩
        fee := ⟨0⟩ }
    resolutions := [{ height := 0, amount := ⟨1000⟩ }] }

theorem waveD_d02_settledState_conserves :
    waveD_d02_settledState.ledger.Conserves := by
  unfold Ledger.Conserves Ledger.total waveD_d02_settledState
  decide

theorem waveD_d02_settledState_onchainSafe :
    waveD_d02_settledState.OnchainSafe := by
  intro e he
  simp only [List.mem_singleton] at he
  subst e
  simp [OnchainEvent.settled, OnchainEvent.confirmations, confirmationCount,
    antiReorgDelay]

/-- An adversary record with a prescribed reorg budget and no other
capability. -/
abbrev waveD_d02_reorgAdversary (budget : Nat) : Adversary :=
  { schedule :=
      { delivery := fun _ _ => false
        partition := fun _ _ => false
        maxDelay := 0
        reorders := false
        dropsMessages := true }
    corruption := .none
    corrupted := []
    reorgDepth := budget
    reorgBudget := budget
    fees := { base := ⟨0⟩, atHeight := fun _ => ⟨0⟩, spikeAt := none }
    learnsPreimages := false
    adaptive := false }

/-- A reorg of depth five: inside the anti-reorg delay. -/
abbrev waveD_d02_budgetFiveReorg : Reorg :=
  { fromHeight := 5, depth := 5, newTip := ByteArray.empty }

/-- A reorg of depth six: exactly at the anti-reorg delay. -/
abbrev waveD_d02_budgetSixReorg : Reorg :=
  { fromHeight := 5, depth := 6, newTip := ByteArray.empty }

/-- With budget five the settled channel is out of reach; the same channel is
*not* out of reach of budget six.  This locates the boundary exactly at
`antiReorgDelay`. -/
theorem waveD_d02_budget_boundary :
    waveD_d02_settledState.OutOfReorgReach (waveD_d02_reorgAdversary 5) ∧
      ¬ waveD_d02_settledState.OutOfReorgReach (waveD_d02_reorgAdversary 6) := by
  constructor
  · intro e he
    simp only [List.mem_singleton] at he
    subst e
    simp [OnchainEvent.confirmations, confirmationCount]
  · intro h
    have hbad : (waveD_d02_reorgAdversary 6).reorgBudget <
        (⟨0, ⟨1000⟩⟩ : OnchainEvent).confirmations waveD_d02_settledState.tip :=
      h ⟨0, ⟨1000⟩⟩ (by simp)
    simp [OnchainEvent.confirmations, confirmationCount] at hbad

theorem waveD_d02_settledState_safe_budget_five :
    waveD_d02_settledState.Safe (waveD_d02_reorgAdversary 5) :=
  ⟨waveD_d02_settledState_conserves, waveD_d02_budget_boundary.1⟩

/-- Non-vacuous positive instance: the depth-five reorg preserves the settled
channel under the depth-five adversary. -/
theorem waveD_d02_budget_five_reorg_preserves :
    (waveD_d02_settledState.applyReorg waveD_d02_budgetFiveReorg).Safe
      (waveD_d02_reorgAdversary 5) := by
  apply waveD_d02_safe_preserved waveD_d02_settledState_safe_budget_five
  show waveD_d02_budgetFiveReorg.depth ≤ (waveD_d02_reorgAdversary 5).reorgBudget
  decide

/-- **The unconditional reading is false.**  A channel whose resolution has
the full anti-reorg delay is still evicted by a reorg that the model's
`reorgAllowed` permits, because `reorgBudget` is unbounded in the wave-A
adversary record. -/
theorem waveD_d02_settled_claim_evicted_by_allowed_reorg :
    ∃ (s : ChannelReorgState) (a : Adversary) (r : Reorg) (e : OnchainEvent),
      s.OnchainSafe ∧ e ∈ s.resolutions ∧ a.reorgAllowed r ∧
        ¬ e.survives r s.tip := by
  refine ⟨waveD_d02_settledState, waveD_d02_reorgAdversary 6,
    waveD_d02_budgetSixReorg, ⟨0, ⟨1000⟩⟩, ?_, ?_, ?_, ?_⟩
  · exact waveD_d02_settledState_onchainSafe
  · simp
  · show waveD_d02_budgetSixReorg.depth ≤ (waveD_d02_reorgAdversary 6).reorgBudget
    decide
  · simp [OnchainEvent.survives, reorgSurvives, confirmationCount]

/-! ## 5. Deep reorgs are a separate failure mode -/

/-- No resolution that has exactly the anti-reorg delay survives a reorg at
or beyond that delay. -/
theorem waveD_d02_deep_reorg_evicts_settled {r : Reorg}
    (hdeep : antiReorgDelay ≤ r.depth) {s : ChannelReorgState}
    {e : OnchainEvent} (_he : e ∈ s.resolutions)
    (hconfirmations : e.confirmations s.tip = antiReorgDelay) :
    ¬ e.survives r s.tip := by
  intro hsurvives
  change confirmationCount s.tip e.height = antiReorgDelay at hconfirmations
  unfold OnchainEvent.survives reorgSurvives at hsurvives
  rw [hconfirmations] at hsurvives
  exact Nat.not_lt.mpr hdeep hsurvives

/-- For *every* reorg at or beyond the anti-reorg delay there is a channel
with a fully settled resolution that the reorg evicts.  This is the
mechanised "separate failure mode": the guarantee for in-budget reorgs does
not extend to deeper ones. -/
theorem waveD_d02_deep_reorg_separate_failure_mode (r : Reorg)
    (hdeep : antiReorgDelay ≤ r.depth) :
    ∃ (s : ChannelReorgState) (e : OnchainEvent),
      s.OnchainSafe ∧ e ∈ s.resolutions ∧ ¬ e.survives r s.tip := by
  refine ⟨waveD_d02_settledState, ⟨0, ⟨1000⟩⟩, ?_, ?_, ?_⟩
  · exact waveD_d02_settledState_onchainSafe
  · simp
  · apply waveD_d02_deep_reorg_evicts_settled hdeep
    · simp
    · change confirmationCount 5 0 = antiReorgDelay
      unfold confirmationCount antiReorgDelay
      rfl

/-- No finite confirmation depth defeats an unbounded reorg: for every `c`
there is a reorg of depth `c` and an event with exactly `c` confirmations
that it evicts. -/
theorem waveD_d02_no_finite_confirmation_depth (c : Nat) :
    ∃ (r : Reorg) (tip h : Height),
      confirmationCount tip h = c ∧ ¬ reorgSurvives r tip h := by
  refine ⟨{ fromHeight := c, depth := c, newTip := ByteArray.empty }, c, 1, ?_, ?_⟩
  · show confirmationCount c 1 = c
    unfold confirmationCount
    omega
  · show ¬ c < c + 1 - 1
    omega

/-! ## 6. BOLT 5's reorg delay for back-failing an HTLC -/

/-- BOLT 5 §"HTLC Output Handling": it is safe to fail an upstream HTLC back
only when the on-chain resolution it depends on is deeper than every reorg the
adversary may perform. -/
abbrev waveD_d02_safeToBackFail (a : Adversary) (e : OnchainEvent)
    (tip : Height) : Prop :=
  a.reorgBudget < e.confirmations tip

/-- Safe back-failing survives every allowed reorg. -/
theorem waveD_d02_safeToBackFail_survives {a : Adversary} {e : OnchainEvent}
    {tip : Height} {r : Reorg} (hsafe : waveD_d02_safeToBackFail a e tip)
    (hallowed : a.reorgAllowed r) : e.survives r tip := by
  unfold waveD_d02_safeToBackFail at hsafe
  change a.reorgBudget < confirmationCount tip e.height at hsafe
  unfold OnchainEvent.survives reorgSurvives
  exact Nat.lt_of_le_of_lt hallowed hsafe

/-- Conversely, if the resolution is *not* out of the adversary's reach then
some allowed reorg evicts it; there is no weaker safe rule. -/
theorem waveD_d02_unsafeToBackFail_allowed_eviction {a : Adversary}
    {e : OnchainEvent} {tip : Height}
    (hunsafe : ¬ waveD_d02_safeToBackFail a e tip) :
    ∃ r : Reorg, a.reorgAllowed r ∧ ¬ e.survives r tip := by
  unfold waveD_d02_safeToBackFail at hunsafe
  have hle : e.confirmations tip ≤ a.reorgBudget := Nat.le_of_not_lt hunsafe
  refine ⟨{ fromHeight := tip, depth := (e.confirmations tip), newTip := ByteArray.empty }, ?_, ?_⟩
  · exact hle
  · unfold OnchainEvent.survives reorgSurvives
    exact Nat.lt_irrefl _

end LnLean.Proofs.WaveD.D02
