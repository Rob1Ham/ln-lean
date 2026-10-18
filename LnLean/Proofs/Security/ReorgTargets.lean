import LnLean.Security.Model
import LnLean.Security.Invariants

/-!
# LnLean.Proofs.Security.ReorgTargets

**English claim (catalog `LN-L1-003`).**  Channel safety is preserved for
reorgs within the adversary's depth budget, and deep reorgs are a separate
failure mode.

`LnLean.Security.Adversary.reorgAllowed` is a *definition*
(`r.depth ≤ a.reorgBudget`), so it cannot be the target of the catalog row by
itself.  This module states the missing theorem and keeps every L1 assumption
visible in the type:

1. **Common chain tip.**  Both parties judge the channel relative to the same
   `LnLean.Security.ChainView`: same observed height and same tip hash
   (`SameChain`).  The wave-A model has no block-hash-per-height map and no
   competing-chain object, so this is an explicit *hypothesis*, not something
   derivable inside the model.  `common_tip_needed` proves it is load-bearing:
   observers with different tips can disagree about survival under the same
   reorg.
2. **Common prefix.**  A block at height `h` is outside a reorg of depth `d`
   exactly when `h + d ≤ tip` (`InCommonPrefix`), equivalently when its
   confirmation count exceeds `d` (`reorgSurvives`).  The model has no
   replacement-chain height, so the observed pre-reorg height is used for
   confirmation accounting.
3. **Bounded reorg depth.**  Two forms are proved.  The literal per-reorg
   form assumes every on-chain fact the channel relies on is deeper than the
   *given* reorg (`Observations.OutOfReachOf`).  The budget form assumes the
   stronger invariant that every fact is deeper than the adversary's whole
   budget (`Observations.SafeAt`), which is what makes preservation hold for
   *every* allowed reorg.
4. **Ledger untouched by reorg.**  The in-channel ledger is not rewritten by
   an L1 reorg in this model; only the set of on-chain facts the channel can
   still observe is filtered.  This is why the result is about
   *retention/eviction*, not about post-reorg confirmation depth or theft.

The positive theorem is `reorg_preserves_channel_safety`.  The separate
failure mode is `deep_reorg_separate_failure_mode`: for every reorg at or
beyond `antiReorgDelay`, some fully settled channel loses an on-chain fact.
`safety_not_unconditional` records that the unconditional reading (settled
facts plus `reorgAllowed`, with no depth bound on the budget) is false.

Relationship to `LnLean.Proofs.WaveD.D02`.  D02 proves the same arithmetic on
`ChannelReorgState` with a `tip : Height` field.  This module adds the
`ChainView`/`SameChain` common-tip layer that the catalog sentence needs, and
uses a separate observation record so that it does not depend on the channel
module.  `D02.waveD_d02_safe_preserved` and
`D02.waveD_d02_deep_reorg_separate_failure_mode` remain the provenance for the
retention argument; this file's `toReorgState` section records the intended
correspondence.

What is *not* modelled.  There is no Bitcoin consensus, no block-level common
prefix, no transaction/script spend semantics, and no probabilistic reorg
model.  `Reorg` carries only `fromHeight`, `depth`, and opaque `newTip` bytes.
Consequently the deep-reorg failure proved here is eviction of an observed
resolution; actual theft or double-spend after a deep reorg remains obligation
`LN-CHAIN-REORG` outside this tree.  The constant `antiReorgDelay = 6` is the
BOLT 5 / LDK anti-reorg delay, not a consensus rule.

BOLT anchors.  BOLT 5 §"HTLC Output Handling" (`05-onchain.md:300-304`,
`:467-471`) requires a reorganization delay before back-failing an upstream
HTLC.  LDK anchor: `lightning/src/chain/channelmonitor.rs:347`
(`ANTI_REORG_DELAY = 6`) and `:514` (`OnchainEventEntry`, the record used to
decide when an on-chain event is safe from a reorg).
-/

namespace LnLean.Proofs.Security.ReorgTargets

open LnLean
open LnLean.Security

set_option autoImplicit false

-- OBLIGATION: LN-L1-003

/-! ## 1. The anti-reorg delay and confirmation arithmetic -/

/-- LDK's `ANTI_REORG_DELAY` (`channelmonitor.rs:347`), the BOLT 5 anti-reorg
delay: the number of blocks the channel monitor waits before treating an
on-chain resolution as safe from a reorganisation.  This is a protocol
constant, not a consensus rule. -/
abbrev antiReorgDelay : Nat := 6

/-- Confirmations of the block at height `h` when the observed tip is `t`.
A block at the tip has one confirmation; truncated subtraction gives zero for
heights above the tip. -/
abbrev confirmationCount (tip h : Height) : Nat := tip + 1 - h

/-- A reorg of depth `r.depth` removes the last `r.depth` blocks below the
observed tip.  The block at height `h` is retained exactly when its
confirmation count exceeds the reorg depth. -/
abbrev reorgSurvives (r : Reorg) (tip h : Height) : Prop :=
  r.depth < confirmationCount tip h

/-- Confirmation-count retention is the same as prefix arithmetic: the reorg
does not reach height `h`. -/
theorem survives_iff_prefix {r : Reorg} {tip h : Height} :
    reorgSurvives r tip h ↔ h + r.depth ≤ tip := by
  unfold reorgSurvives confirmationCount
  rw [Nat.lt_sub_iff_add_lt, Nat.add_comm r.depth h, Nat.lt_succ_iff]

/-- The boundary is tight: an event with exactly `c` confirmations is evicted
by a reorg of depth `c`. -/
theorem not_survives_at_depth {c tip h : Height}
    (hconf : confirmationCount tip h = c) :
    ¬ reorgSurvives { fromHeight := tip, depth := c, newTip := ByteArray.empty }
      tip h := by
  unfold reorgSurvives
  rw [hconf]
  exact Nat.lt_irrefl c

/-! ## 2. Chain views, common tip, and common prefix -/

/-- The common-tip hypothesis: two views observe the same chain.  The wave-A
`ChainView` has only a height and a tip hash, so agreement is exactly those two
fields.  This is assumed, not derived: `common_tip_needed` shows that views
which disagree can disagree about survival. -/
def SameChain (v w : ChainView) : Prop :=
  v.height = w.height ∧ v.tip = w.tip

/-- Same-chain agreement is reflexive. -/
theorem sameChain_refl (v : ChainView) : SameChain v v :=
  ⟨rfl, rfl⟩

/-- Same-chain agreement is symmetric. -/
theorem sameChain_symm {v w : ChainView} (h : SameChain v w) : SameChain w v :=
  ⟨h.1.symm, h.2.symm⟩

/-- Same-chain agreement is transitive. -/
theorem sameChain_trans {u v w : ChainView}
    (huv : SameChain u v) (hvw : SameChain v w) : SameChain u w :=
  ⟨huv.1.trans hvw.1, huv.2.trans hvw.2⟩

/-- The common-prefix predicate: the block at height `h` lies at or below the
prefix that a reorg of depth `r.depth` cannot rewrite.  This is the model's
only representation of a common prefix, since `Reorg` records depth but not
the replacement chain. -/
def InCommonPrefix (v : ChainView) (r : Reorg) (h : Height) : Prop :=
  h + r.depth ≤ v.height

/-- Common-prefix arithmetic is exactly the confirmation-count survival
predicate. -/
theorem inCommonPrefix_iff_survives {v : ChainView} {r : Reorg} {h : Height} :
    InCommonPrefix v r h ↔ reorgSurvives r v.height h := by
  rw [survives_iff_prefix]
  rfl

/-- Parties on the same chain view agree on whether a block survives a reorg.
This is what the common-tip hypothesis buys. -/
theorem survives_congr_of_sameChain {v w : ChainView} (h : SameChain v w)
    {r : Reorg} {height : Height} :
    reorgSurvives r v.height height ↔ reorgSurvives r w.height height := by
  rw [h.1]

/-! ## 3. Channel observations and budget-relative safety -/

/-- An on-chain fact the channel relies on: a funding confirmation, a
commitment spend, or an HTLC claim/fail transaction.  `amount` is the value
whose disposition depends on the fact. -/
structure OnchainFact where
  height : Height
  amount : Msat
deriving Repr

/-- Confirmations accumulated by the fact at the observed tip. -/
abbrev OnchainFact.confirmations (e : OnchainFact) (tip : Height) : Nat :=
  confirmationCount tip e.height

/-- Does the fact's block survive the reorg? -/
abbrev OnchainFact.survives (e : OnchainFact) (r : Reorg) (tip : Height) : Prop :=
  reorgSurvives r tip e.height

/-- The fact has reached the anti-reorg delay and is treated as settled. -/
abbrev OnchainFact.settled (e : OnchainFact) (tip : Height) : Prop :=
  antiReorgDelay ≤ e.confirmations tip

/-- The part of a channel that a reorg can affect in this model: the
in-channel ledger plus the on-chain facts the channel relies on.  The chain
view is kept separate because safety is judged relative to an observed tip. -/
structure Observations where
  ledger : Ledger
  facts : List OnchainFact
deriving Repr

/-- Channel safety at a chain view: value is conserved in the ledger and every
on-chain fact the channel relies on is deeper than the adversary's *entire*
reorg budget.  The second clause is the bounded-depth hypothesis; without it
`reorgAllowed` alone says nothing about survival. -/
def Observations.SafeAt (o : Observations) (v : ChainView)
    (a : Adversary) : Prop :=
  o.ledger.Conserves ∧
    ∀ e ∈ o.facts, a.reorgBudget < e.confirmations v.height

/-- On a common chain tip, the two parties' safety judgements coincide.  This
is the positive counterpart of `safety_judgement_needs_common_tip`. -/
theorem safeAt_congr_of_sameChain {o : Observations} {v w : ChainView}
    {a : Adversary} (h : SameChain v w) :
    o.SafeAt v a ↔ o.SafeAt w a := by
  unfold Observations.SafeAt
  rw [h.1]

/-- All on-chain facts have reached the anti-reorg delay at the observed view.
This is the protocol's "settled" predicate, not a safety invariant by itself:
the adversary's budget may still exceed the delay. -/
def Observations.OnchainSafeAt (o : Observations) (v : ChainView) : Prop :=
  ∀ e ∈ o.facts, antiReorgDelay ≤ e.confirmations v.height

/-- Every fact is deeper than one particular reorg.  This is the literal
per-reorg depth bound; it is weaker than `SafeAt`, which bounds the whole
adversary budget. -/
def Observations.OutOfReachOf (o : Observations) (v : ChainView)
    (r : Reorg) : Prop :=
  ∀ e ∈ o.facts, r.depth < e.confirmations v.height

/-- Apply a reorg, judged at the observed tip height: facts whose block does
not survive are evicted; surviving observations remain.  The replacement
chain's height is not modelled, so this updates *retention*, not the
confirmation count of surviving facts. -/
def Observations.applyReorgAt (o : Observations) (tip : Height)
    (r : Reorg) : Observations :=
  { o with facts := o.facts.filter (fun e => decide (e.survives r tip)) }

/-- Retention: the ledger is unchanged and every pre-reorg on-chain fact is
still observed after the reorg. -/
def Retains (o o' : Observations) : Prop :=
  o'.ledger = o.ledger ∧ ∀ e ∈ o.facts, e ∈ o'.facts

/-- The post-reorg ledger is the pre-reorg ledger: an L1 reorg does not rewrite
the in-channel balances in this model. -/
theorem applyReorgAt_ledger_eq (o : Observations) (tip : Height) (r : Reorg) :
    (o.applyReorgAt tip r).ledger = o.ledger :=
  rfl

/-- Membership after applying a reorg: the fact was present before and its
block survives. -/
theorem mem_applyReorgAt {o : Observations} {tip : Height} {r : Reorg}
    {e : OnchainFact} :
    e ∈ (o.applyReorgAt tip r).facts ↔
      e ∈ o.facts ∧ e.survives r tip := by
  simp [Observations.applyReorgAt, List.mem_filter]

/-! ## 4. Positive results: depth-bounded reorgs preserve safety -/

/-- A fact out of reach of the whole budget survives every allowed reorg.
This is the arithmetic core of the preservation theorem. -/
theorem fact_survives_of_safeAt {o : Observations} {v : ChainView}
    {a : Adversary} {r : Reorg} {e : OnchainFact}
    (he : e ∈ o.facts) (hsafe : o.SafeAt v a)
    (hallowed : a.reorgAllowed r) : e.survives r v.height := by
  obtain ⟨_, hbudget⟩ := hsafe
  exact Nat.lt_of_le_of_lt hallowed (hbudget e he)

/-- No fact is filtered out by an allowed reorg when the observation is safe
for the adversary's entire budget. -/
theorem applyReorgAt_facts_eq {o : Observations} {v : ChainView}
    {a : Adversary} {r : Reorg} (hsafe : o.SafeAt v a)
    (hallowed : a.reorgAllowed r) :
    (o.applyReorgAt v.height r).facts = o.facts := by
  unfold Observations.applyReorgAt
  apply List.filter_eq_self.mpr
  intro e he
  have hsurv : e.survives r v.height :=
    fact_survives_of_safeAt he hsafe hallowed
  simp [hsurv]

/-- **Per-reorg depth bound.**  If every on-chain fact is deeper than this
particular reorg, the reorg evicts nothing.  This is the literal "reorg within
the adversary's depth budget" form for one reorg. -/
theorem reorg_retains_of_depth_bound {o : Observations} {v : ChainView}
    {r : Reorg} (hreach : o.OutOfReachOf v r) :
    Retains o (o.applyReorgAt v.height r) := by
  constructor
  · rfl
  · intro e he
    rw [mem_applyReorgAt]
    exact ⟨he, hreach e he⟩

/-- **Budget form at a single view.**  A safe observation retains every fact
after any allowed reorg. -/
theorem reorg_retains {o : Observations} {v : ChainView}
    {a : Adversary} {r : Reorg} (hsafe : o.SafeAt v a)
    (hallowed : a.reorgAllowed r) :
    Retains o (o.applyReorgAt v.height r) := by
  constructor
  · rfl
  · intro e he
    rw [mem_applyReorgAt]
    exact ⟨he, fact_survives_of_safeAt he hsafe hallowed⟩

/-- **The catalog claim, chain-tip form.**  Let two parties observe the same
chain tip (same height and tip hash).  If the channel is safe relative to the
first view — ledger conserves and every on-chain fact is deeper than the
adversary's whole reorg budget — then every reorg the adversary is allowed to
perform both retains every on-chain fact and preserves the same safety,
judged at the second view.  The retention conjunct is load-bearing: `SafeAt`
alone is monotone under dropping facts and would be too weak. -/
theorem reorg_preserves_channel_safety
    {o : Observations} {v w : ChainView} {a : Adversary} {r : Reorg}
    (hsame : SameChain v w)
    (hsafe : o.SafeAt v a)
    (hallowed : a.reorgAllowed r) :
    Retains o (o.applyReorgAt v.height r) ∧
      (o.applyReorgAt v.height r).SafeAt w a := by
  refine ⟨reorg_retains hsafe hallowed, ?_⟩
  obtain ⟨hconserves, hbudget⟩ := hsafe
  constructor
  · exact hconserves
  · intro e he
    rw [mem_applyReorgAt] at he
    have hdeep : a.reorgBudget < e.confirmations v.height :=
      hbudget e he.1
    rw [← hsame.1]
    exact hdeep

/-- **The catalog claim under BOLT 5 / LDK's anti-reorg delay.**  If the
adversary's entire budget is below `antiReorgDelay`, every settled fact is
out of reach, and every allowed reorg preserves channel safety at a common
tip.  This is the closest faithful form of the English sentence: the depth
bound on the *budget* is load-bearing and cannot be dropped. -/
theorem reorg_preserves_channel_safety_within_anti_reorg_delay
    {o : Observations} {v w : ChainView} {a : Adversary} {r : Reorg}
    (hsame : SameChain v w)
    (hconserves : o.ledger.Conserves)
    (hsettled : o.OnchainSafeAt v)
    (hbudget : a.reorgBudget < antiReorgDelay)
    (hallowed : a.reorgAllowed r) :
    Retains o (o.applyReorgAt v.height r) ∧
      (o.applyReorgAt v.height r).SafeAt w a := by
  refine reorg_preserves_channel_safety hsame ⟨hconserves, ?_⟩ hallowed
  intro e he
  exact Nat.lt_of_lt_of_le hbudget (hsettled e he)

/-! ## 5. Non-vacuity: a settled channel survives an in-budget reorg -/

/-- A channel that conserves `1000 msat` and relies on one fully confirmed
funding fact at height zero. -/
def settledObservations : Observations :=
  { ledger :=
      { funding := ⟨1000⟩
        localBalance := ⟨600⟩
        remoteBalance := ⟨400⟩
        inFlight := ⟨0⟩
        fee := ⟨0⟩ }
    facts := [{ height := 0, amount := ⟨1000⟩ }] }

/-- The view with tip height five: the height-zero fact has six
confirmations, exactly `antiReorgDelay`. -/
def settledView : ChainView :=
  { height := 5, tip := ByteArray.mk #[0], lastReorg := none }

/-- An adversary whose entire reorg budget is five blocks and which has no
other capability. -/
def budgetFiveAdversary : Adversary :=
  { schedule :=
      { delivery := fun _ _ => false
        partition := fun _ _ => false
        maxDelay := 0
        reorders := false
        dropsMessages := true }
    corruption := .none
    corrupted := []
    reorgDepth := 5
    reorgBudget := 5
    fees := { base := ⟨0⟩, atHeight := fun _ => ⟨0⟩, spikeAt := none }
    learnsPreimages := false
    adaptive := false }

/-- A depth-five reorg: inside the five-block budget and the six-block delay. -/
def depthFiveReorg : Reorg :=
  { fromHeight := 5, depth := 5, newTip := ByteArray.mk #[1] }

/-- The settled channel is safe for the depth-five adversary. -/
theorem settledObservations_safe :
    settledObservations.SafeAt settledView budgetFiveAdversary := by
  constructor
  · unfold Ledger.Conserves Ledger.total settledObservations
    decide
  · intro e he
    simp only [settledObservations, List.mem_singleton] at he
    subst e
    simp [settledView, budgetFiveAdversary, OnchainFact.confirmations,
      confirmationCount]

/-- Non-vacuous positive instance: the depth-five reorg is allowed for the
depth-five adversary and preserves the settled channel's safety at the common
tip. -/
theorem settled_reorg_preserves :
    Retains settledObservations
        (settledObservations.applyReorgAt settledView.height depthFiveReorg) ∧
      (settledObservations.applyReorgAt settledView.height
        depthFiveReorg).SafeAt settledView budgetFiveAdversary := by
  apply reorg_preserves_channel_safety (sameChain_refl settledView)
    settledObservations_safe
  show depthFiveReorg.depth ≤ budgetFiveAdversary.reorgBudget
  decide

/-- The depth-five reorg also retains the settled fact, so the positive
instance is not vacuous at the level of the fact list. -/
theorem settled_reorg_retains :
    Retains settledObservations
      (settledObservations.applyReorgAt settledView.height depthFiveReorg) := by
  apply reorg_retains settledObservations_safe
  show depthFiveReorg.depth ≤ budgetFiveAdversary.reorgBudget
  decide

/-- The positive instance is not a filter that silently drops everything:
the fact is still present after the reorg. -/
theorem settled_fact_still_present :
    (⟨0, ⟨1000⟩⟩ : OnchainFact) ∈
      (settledObservations.applyReorgAt settledView.height
        depthFiveReorg).facts := by
  rw [mem_applyReorgAt]
  refine ⟨?_, ?_⟩
  · simp [settledObservations]
  · simp [OnchainFact.survives, reorgSurvives, confirmationCount, settledView,
      depthFiveReorg]

/-! ## 6. Deep reorgs are a separate failure mode -/

/-- **Deep-reorg failure.**  For every reorg at or beyond `antiReorgDelay`,
there is a fully settled channel observation that is safe for a depth-five
adversary but loses an on-chain fact to that reorg.  The reorg is *not*
allowed for the depth-five adversary, so this is exactly the boundary: the
in-budget guarantee does not extend past the depth budget. -/
theorem deep_reorg_separate_failure_mode (r : Reorg)
    (hdeep : antiReorgDelay ≤ r.depth) :
    ∃ (v : ChainView) (o : Observations) (e : OnchainFact),
      o.SafeAt v budgetFiveAdversary ∧
        e ∈ o.facts ∧
        e ∉ (o.applyReorgAt v.height r).facts := by
  refine ⟨settledView, settledObservations, ⟨0, ⟨1000⟩⟩,
    settledObservations_safe, ?_, ?_⟩
  · simp [settledObservations]
  · intro hmem
    rw [mem_applyReorgAt] at hmem
    have hsurv : (⟨0, ⟨1000⟩⟩ : OnchainFact).survives r settledView.height :=
      hmem.2
    have hconf :
        (⟨0, ⟨1000⟩⟩ : OnchainFact).confirmations settledView.height =
          antiReorgDelay := by
      simp [settledView, OnchainFact.confirmations, confirmationCount,
        antiReorgDelay]
    change confirmationCount settledView.height 0 = antiReorgDelay at hconf
    unfold OnchainFact.survives reorgSurvives at hsurv
    rw [hconf] at hsurv
    exact Nat.not_lt.mpr hdeep hsurv

/-- The deep reorg in the failure mode is genuinely outside the depth-five
adversary's budget, so the positive theorem is not contradicted. -/
theorem deep_reorg_not_allowed (r : Reorg)
    (hdeep : antiReorgDelay ≤ r.depth) :
    ¬ budgetFiveAdversary.reorgAllowed r := by
  intro h
  have hle : r.depth ≤ 5 := h
  have hdeep' : 6 ≤ r.depth := hdeep
  omega

/-- **The unconditional reading is false.**  "Settled facts plus
`reorgAllowed` preserve the observation" fails without a bound on the
adversary's budget: a depth-six reorg is allowed for a depth-six adversary and
evicts a fact that has exactly the anti-reorg delay's six confirmations. -/
theorem safety_not_unconditional :
    ¬ (∀ (o : Observations) (v : ChainView) (a : Adversary) (r : Reorg),
        o.OnchainSafeAt v → a.reorgAllowed r →
          Retains o (o.applyReorgAt v.height r)) := by
  intro h
  have hret : Retains settledObservations
      (settledObservations.applyReorgAt settledView.height
        { fromHeight := 5, depth := 6, newTip := ByteArray.mk #[2] }) :=
    h settledObservations settledView
      { budgetFiveAdversary with reorgDepth := 6, reorgBudget := 6 }
      { fromHeight := 5, depth := 6, newTip := ByteArray.mk #[2] } ?_ ?_
  · have hmem : (⟨0, ⟨1000⟩⟩ : OnchainFact) ∈
        (settledObservations.applyReorgAt settledView.height
          { fromHeight := 5, depth := 6, newTip := ByteArray.mk #[2] }).facts :=
      hret.2 ⟨0, ⟨1000⟩⟩ (by simp [settledObservations])
    rw [mem_applyReorgAt] at hmem
    simp [OnchainFact.survives, reorgSurvives, confirmationCount,
      settledView] at hmem
  · -- the depth-six adversary still has a settled channel
    intro e he
    simp only [settledObservations, List.mem_singleton] at he
    subst e
    simp [settledView, OnchainFact.confirmations,
      confirmationCount, antiReorgDelay]
  · -- and the depth-six reorg is allowed
    change (6 : Nat) ≤ 6
    decide

/-! ## 7. Common-tip hypothesis is not derivable -/

/-- Without a common tip, two observers can disagree about survival under the
same reorg.  This is why `SameChain` is a hypothesis on the main theorem and
not a lemma: the wave-A model has no consensus rule that identifies the two
views. -/
theorem common_tip_needed :
    ∃ (v w : ChainView) (r : Reorg) (e : OnchainFact),
      ¬ SameChain v w ∧ e.survives r v.height ∧ ¬ e.survives r w.height := by
  refine
    ⟨{ height := 10, tip := ByteArray.mk #[0], lastReorg := none },
     { height := 6, tip := ByteArray.mk #[1], lastReorg := none },
     { fromHeight := 10, depth := 8, newTip := ByteArray.mk #[2] },
     { height := 0, amount := ⟨1000⟩ }, ?_, ?_, ?_⟩
  · intro h
    have hh : (10 : Nat) = 6 := h.1
    exact (by decide : (10 : Nat) ≠ 6) hh
  · simp [OnchainFact.survives, reorgSurvives, confirmationCount]
  · simp [OnchainFact.survives, reorgSurvives, confirmationCount]

/-- **Safety judgements need a common tip.**  A channel that is safe for a
depth-eight adversary at one view can fail the same predicate at another view,
because the fact has fewer confirmations there.  The main theorem's
`SameChain` hypothesis is therefore load-bearing; without it, preservation at
the second party's view is not derivable. -/
theorem safety_judgement_needs_common_tip :
    ∃ (o : Observations) (v w : ChainView) (a : Adversary),
      o.SafeAt v a ∧ ¬ o.SafeAt w a := by
  refine
    ⟨settledObservations,
     { height := 10, tip := ByteArray.mk #[0], lastReorg := none },
     { height := 6, tip := ByteArray.mk #[1], lastReorg := none },
     { budgetFiveAdversary with reorgDepth := 8, reorgBudget := 8 },
     ?_, ?_⟩
  · constructor
    · unfold Ledger.Conserves Ledger.total settledObservations
      decide
    · intro e he
      simp only [settledObservations, List.mem_singleton] at he
      subst e
      simp [OnchainFact.confirmations, confirmationCount]
  · intro hbad
    have hbudget : (8 : Nat) <
        (⟨0, ⟨1000⟩⟩ : OnchainFact).confirmations 6 := hbad.2 ⟨0, ⟨1000⟩⟩ (by
      simp [settledObservations])
    simp [OnchainFact.confirmations, confirmationCount] at hbudget

/-! ## 8. Relationship to `LnLean.Proofs.WaveD.D02`

D02 proves the retention argument on `ChannelReorgState` (a `tip : Height`, a
`ledger`, and a list of `OnchainEvent`s), with the same confirmation
arithmetic.  This module does not import it: D02 sits above
`LnLean.Channel.HTLC`, and the target is kept independent of the channel
module.  The correspondence is:

* `Observations.SafeAt o v a` is D02's `ChannelReorgState.Safe` at
  `tip := v.height`;
* `Observations.applyReorgAt o v.height r` is D02's `applyReorg r` at that
  tip;
* `reorg_preserves_channel_safety` is the `SameChain`-lifted form of
  `D02.waveD_d02_safe_preserved`;
* `deep_reorg_separate_failure_mode` mirrors
  `D02.waveD_d02_deep_reorg_separate_failure_mode` and
  `D02.waveD_d02_settled_claim_evicted_by_allowed_reorg`.

The two modules agree on `antiReorgDelay = 6`, `confirmationCount`,
`reorgSurvives`, and the eviction boundary.  D02 remains the source of the
per-tip argument; this file adds the chain-view/common-tip layer that the
catalog sentence requires. -/

end LnLean.Proofs.Security.ReorgTargets
