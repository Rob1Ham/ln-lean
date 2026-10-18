/-
# H44 — lossless event bounds, the tightness gap, and the exact reduction obligation

**Issues.** `SEC-01` (no end-to-end game-based security proof) and `CR-01` (no
computational reduction).  Base module: `LnLean/Proofs/Security/SecurityGameTargets.lean`
(wave 5, `S5-SEC-LIMITS`; documented in `docs/CRYPTO-LIMITS.md`).

## What the base module leaves open

`AdvantageReduction` is a **specification**: its `tight` field is literally the
accounting inequality `Adv protocol n ≤ Adv primitive n + loss n`, and
`AdvantageReduction.bound` is only the arithmetic consequence of that field.
Two concrete weaknesses follow, and both are mechanised below.

1. **The accounting inequality is not derived from the event simulation.**
   `EventReduction` transfers "no bad state"; it says nothing about the
   advantage sequence.  So `tight` cannot be dropped, and it cannot be proved
   from `map_init`/`map_step`/`win_transport` (`accounting_not_implied_by_event`).
2. **The interface is satisfiable for every advantage sequence** by choosing
   `loss := protocol.value` (`tautologicalReduction`).  The `bound` theorem is
   then a tautology.  What makes the interface contentful is a *negligible*
   loss, and that is exactly what no lemma in the tree provides
   (`not_negligible_one`, `tautological_loss_not_negligible`).

## What this module adds

* §1 a small `Rat` toolkit.  The tree has no mathlib: in particular there is no
  proof that `Negligible` is closed under addition, which `docs/CRYPTO-LIMITS.md`
  §3.1 and §9.5 list as missing.  §1 supplies the arithmetic and §4 proves the
  closure.
* §2 the **event-level indicator advantage** `winAdvantage g` (mass `1` on a bad
  horizon, `0` otherwise).  This is a real `Advantage`, and it is an
  `ExactAdvantage`.  From a bare `EventReduction` we prove the **lossless**
  bound `winAdvantage P ≤ winAdvantage C` with **no `tight` hypothesis**: the
  bound is derived from `map_run` and `win_transport` alone
  (`winAdvantage_mono`).
* §3 an **event cover** `EventCover`: the protocol win event is contained in the
  primitive win event together with an explicit loss event.  From the cover we
  derive the accounting inequality *with the loss event as the loss*
  (`EventCover.bound`), again without assuming tightness.  Every
  `EventReduction` is a cover with the empty loss event
  (`EventReduction.toEventCover`), so this is a strict generalisation.
* §4 `Negligible` is closed under addition and under domination, and every
  eventually-zero sequence is negligible (`negligible_add`, `negligible_of_le`,
  `negligible_of_eventually_zero`).  The constant-one sequence is **not**
  negligible (`not_negligible_one`), so the closure has content.
* §5 the **exact remaining obligation** as a record `ReductionObligation`
  (`accounting`, a negligible primitive advantage, a negligible loss) and the
  theorem that would follow: `Negligible protocol.value`
  (`ReductionObligation.protocol_negligible`).  This is arithmetic plus the two
  negligibility hypotheses; it is **not** a reduction.  The record is shown to
  contain the base `AdvantageReduction` (`ofAdvantageReduction`), and the sharp
  counterexample (`accounting_not_implied_by_event`,
  `tautological_loss_not_negligible`, `exactAdvantage_not_determined`) shows
  that neither field can be removed.
* §6 non-vacuity: a concrete lossless cover (`EventCover.ofSecure`) and a
  concrete negligible-loss instance of the obligation.

## What is still **not** proved (kept explicit)

* There is no probability space, no adversary transformation, no oracle
  simulation, and no efficiency preservation.  `ReductionObligation` is a
  statement of what a game-hopping proof must deliver; its fields are
  hypotheses.
* `AdvantageReduction.tight` in the shared module is still an assumed field.
  Nothing here discharges it; §3 only shows the *event-level* route to an
  accounting inequality, and §2 shows that route costs the loss term.
* `Advantage` is not linked to `Game.Wins` by the shared interface.  §2 links
  them for the indicator advantage; that is one particular advantage functional,
  not a probability semantics.  `exactAdvantage_not_determined` shows that even
  the strongest event link the model can state (`ExactAdvantage`) does not
  determine an advantage sequence, so no accounting inequality follows from
  event security alone.
* The concrete numbers are still `Rat`-valued and literal; `Negligible` here is
  the definition from the base module, with all of its limits (`docs/CRYPTO-LIMITS.md`
  §3.1).

BOLT sections.  BOLT 2 §Commitment Transactions (the protocol game whose bad
event would be a theft/equivocation), BOLT 3 §Sighash (the C3 message domain),
BOLT 4 §Onion Decryption (C8), BOLT 1 §Lightning Message Format (32-byte hashes
and signatures).  No BOLT byte layout is used in this module: the claims are
about the accounting interface, not about wire data.
-/

import LnLean.Proofs.Security.SecurityGameTargets

set_option autoImplicit false

namespace LnLean.Proofs.WaveH.H44

open LnLean.Proofs.Security.Limits

/-! ## 1. A `Rat` toolkit (no mathlib, hence no `ring`/`linarith`) -/

/-- Transitivity of `<` on `Rat` composed with `≤` on the right.  The core
library provides no `Rat.lt_trans`/`Rat.lt_of_lt_of_le`, so the two lemmas are
proved from `Rat.lt_iff_le_and_ne` and `Rat.not_le`. -/
theorem rat_lt_of_lt_of_le {a b c : Rat} (h1 : a < b) (h2 : b ≤ c) : a < c := by
  rw [Rat.lt_iff_le_and_ne]
  refine ⟨Rat.le_trans (Rat.le_of_lt h1) h2, ?_⟩
  intro h
  rw [h] at h1
  exact (Rat.not_le.mpr h1) h2

/-- Transitivity of `<` on `Rat`. -/
theorem rat_lt_trans {a b c : Rat} (h1 : a < b) (h2 : b < c) : a < c :=
  rat_lt_of_lt_of_le h1 (Rat.le_of_lt h2)

/-- The `Nat` cast is additive for `Rat`.  Needed because `Negligible` is
indexed by `Nat` denominators and the closure proof doubles the denominator. -/
theorem rat_natCast_add (m n : Nat) :
    ((m + n : Nat) : Rat) = (m : Rat) + (n : Rat) := by
  apply Rat.ext
  · rw [Rat.add_def, Rat.num_normalize]
    simp only [Rat.num_natCast, Rat.den_natCast, Int.natCast_add,
               Nat.gcd_one_right, Nat.one_mul]
    rw [show ((1 : Nat) : Int) = 1 from rfl]
    simp only [Int.mul_one]
    rw [Int.ediv_one]
  · rw [Rat.add_def, Rat.den_normalize]
    simp only [Rat.den_natCast, Nat.gcd_one_right, Nat.one_mul, Nat.div_one]

/-- `(1 : Rat) + 1 = 2`, by reduction of the normal form. -/
theorem rat_one_add_one : (1 : Rat) + 1 = 2 := by
  apply Rat.ext
  · rw [Rat.add_def, Rat.num_normalize]
    decide
  · rw [Rat.add_def, Rat.den_normalize]
    decide

/-- `(2 : Rat) ≠ 0`. -/
theorem rat_two_ne_zero : (2 : Rat) ≠ 0 := by
  intro h
  have h2 : (2 : Rat).num = (0 : Rat).num := by rw [h]
  simp at h2

/-- A positive natural number casts to a positive rational. -/
theorem rat_natCast_pos {c : Nat} (h : 0 < c) : (0 : Rat) < (c : Rat) := by
  rw [Rat.lt_iff]
  simp only [Rat.num_natCast, Rat.den_natCast, Rat.zero_num, Rat.zero_den]
  omega

/-- `1/c` is positive for a positive natural denominator. -/
theorem rat_inv_pos {c : Nat} (h : 0 < c) : (0 : Rat) < (1 : Rat) / (c : Rat) := by
  rw [Rat.div_def, Rat.one_mul, Rat.inv_pos]
  exact rat_natCast_pos h

/-- `1/c` is non-negative for a positive natural denominator.  This is the bound
shape used by `Negligible`. -/
theorem rat_inv_nonneg {c : Nat} (h : 0 < c) : (0 : Rat) ≤ (1 : Rat) / (c : Rat) :=
  Rat.le_of_lt (rat_inv_pos h)

/-- `2⁻¹ + 2⁻¹ = 1`. -/
theorem rat_half_add_half : (1 : Rat) / 2 + (1 : Rat) / 2 = 1 := by
  calc (1 : Rat) / 2 + (1 : Rat) / 2 = 2⁻¹ + 2⁻¹ := by rw [Rat.div_def, Rat.one_mul]
    _ = (1 + 1) * 2⁻¹ := by rw [Rat.add_mul, Rat.one_mul]
    _ = 2 * 2⁻¹ := by rw [rat_one_add_one]
    _ = 1 := Rat.mul_inv_cancel 2 rat_two_ne_zero

/-- `0 < 1/2`. -/
theorem rat_half_pos : (0 : Rat) < (1 : Rat) / 2 := by
  rw [Rat.div_def, Rat.one_mul, Rat.inv_pos]
  show (0 : Rat) < 2
  decide

/-- `1/2 < 1`. -/
theorem rat_half_lt_one : (1 : Rat) / 2 < 1 := by
  have h := (Rat.add_lt_add_left (c := (1 : Rat) / 2)).mpr rat_half_pos
  rw [Rat.add_zero, rat_half_add_half] at h
  exact h

/-- `¬ 1 ≤ 1/2`. -/
theorem rat_not_one_le_half : ¬ ((1 : Rat) ≤ (1 : Rat) / 2) :=
  Rat.not_le.mpr rat_half_lt_one

/-- `(x + x)⁻¹ + (x + x)⁻¹ = x⁻¹` for `x ≠ 0`.  This is the algebraic core of
the closure of `Negligible` under addition: the doubled denominator halves the
bound. -/
theorem rat_one_add_one_ne_zero : ¬ ((1 : Rat) + 1 = 0) := by
  intro h
  rw [rat_one_add_one] at h
  exact rat_two_ne_zero h

theorem rat_inv_add_inv_add (x : Rat) (hx : x ≠ 0) :
    (x + x)⁻¹ + (x + x)⁻¹ = x⁻¹ := by
  have hxxeq : x + x = (1 + 1) * x := by
    rw [Rat.add_mul, Rat.one_mul]
  have hxx : x + x ≠ 0 := by
    intro h
    have h' : (1 + 1) * x = 0 := by rw [← hxxeq, h]
    rcases Rat.mul_eq_zero.mp h' with h1 | h1
    · exact rat_one_add_one_ne_zero h1
    · exact hx h1
  have hu : (x + x)⁻¹ * (x + x) = 1 := Rat.inv_mul_cancel _ hxx
  have hc : x * x⁻¹ = 1 := Rat.mul_inv_cancel x hx
  have hsum : (x + x) * x⁻¹ = 1 + 1 := by
    rw [Rat.add_mul, hc]
  calc (x + x)⁻¹ + (x + x)⁻¹
      = (x + x)⁻¹ * 1 + (x + x)⁻¹ * 1 := by rw [Rat.mul_one]
    _ = (x + x)⁻¹ * (1 + 1) := by rw [Rat.mul_add]
    _ = (x + x)⁻¹ * ((x + x) * x⁻¹) := by rw [hsum]
    _ = ((x + x)⁻¹ * (x + x)) * x⁻¹ := by rw [Rat.mul_assoc]
    _ = 1 * x⁻¹ := by rw [hu]
    _ = x⁻¹ := Rat.one_mul _

/-! ## 2. Event-level indicator advantages: a lossless bound with no tightness -/

noncomputable section

open Classical

/-- The indicator of an event as a rational mass: `1` when the event holds and
`0` otherwise.  The classical decidability instance is used only to write the
`if`; no computation depends on it. -/
def indicator (p : Prop) : Rat := if p then 1 else 0

theorem indicator_of_pos {p : Prop} (h : p) : indicator p = 1 := by
  simp [indicator, h]

theorem indicator_of_neg {p : Prop} (h : ¬p) : indicator p = 0 := by
  simp [indicator, h]

theorem indicator_nonneg (p : Prop) : 0 ≤ indicator p := by
  by_cases h : p
  · rw [indicator_of_pos h]
    exact (by decide : (0 : Rat) ≤ 1)
  · rw [indicator_of_neg h]
    exact Rat.le_refl

theorem indicator_le_one (p : Prop) : indicator p ≤ 1 := by
  by_cases h : p
  · rw [indicator_of_pos h]
    exact Rat.le_refl
  · rw [indicator_of_neg h]
    exact (by decide : (0 : Rat) ≤ 1)

/-- **The event-level advantage.**  At horizon `n` the value is the indicator of
the bad event `P.Wins n`.  This is the only advantage functional in the tree that
is *defined from the game*; the shared `Advantage` interface has no such link. -/
noncomputable def winAdvantage (g : Game) : Advantage g where
  value := fun n => indicator (g.Wins n)
  nonneg := fun n => indicator_nonneg (g.Wins n)
  le_one := fun n => indicator_le_one (g.Wins n)

/-- Event security forces the indicator advantage to vanish. -/
theorem winAdvantage_zero_of_secure {g : Game} (h : g.Secure) :
    ∀ n : Nat, (winAdvantage g).value n = 0 := by
  intro n
  exact indicator_of_neg (h n)

/-- **The lossless bound.**  An event-level reduction bounds the protocol
indicator advantage by the primitive indicator advantage with **zero loss**.
No `tight` field is assumed: the proof is `map_run` plus `win_transport`. -/
theorem winAdvantage_mono {P C : Game} (R : EventReduction P C) :
    ∀ n : Nat, (winAdvantage P).value n ≤ (winAdvantage C).value n := by
  intro n
  show indicator (P.Wins n) ≤ indicator (C.Wins n)
  by_cases h : P.Wins n
  · have hC : C.Wins n := by
      have hmap : R.map (P.run n) = C.run n := R.map_run n
      have hbad : C.bad (R.map (P.run n)) := R.win_transport (P.run n) h
      rw [hmap] at hbad
      exact hbad
    rw [indicator_of_pos h, indicator_of_pos hC]
    exact Rat.le_refl
  · rw [indicator_of_neg h]
    exact indicator_nonneg (C.Wins n)

/-- The indicator advantage is an `ExactAdvantage`: it is zero on every
event-secure game.  This is a non-vacuity witness for `ExactAdvantage` that is
not the constantly-zero sequence used by the base module. -/
noncomputable def exactWinAdvantage (g : Game) : ExactAdvantage g where
  value := fun n => indicator (g.Wins n)
  nonneg := fun n => indicator_nonneg (g.Wins n)
  le_one := fun n => indicator_le_one (g.Wins n)
  zero_of_secure := fun h => winAdvantage_zero_of_secure h

/-- A game whose bad event always holds.  Used for the sharpness result below. -/
def alwaysBadGame : Game where
  State := Unit
  init := ()
  step := fun s _ => s
  bad := fun _ => True

theorem alwaysBadGame_wins (n : Nat) : alwaysBadGame.Wins n := trivial

theorem alwaysBadGame_not_secure : ¬ alwaysBadGame.Secure := by
  intro h
  exact h 0 trivial

/-- **Sharpness of the event link.**  Even `ExactAdvantage` — the strongest
connection between events and an advantage sequence that the model can state —
does not determine the advantage: on one and the same non-secure game there is an
exact advantage that is identically `1` and one that is identically `0`
(`zero_of_secure` is vacuous because the game is not secure).  Consequently no
accounting inequality can be derived from event security; the `tight` field is
load-bearing. -/
theorem exactAdvantage_not_determined :
    ∃ (A B : ExactAdvantage alwaysBadGame),
      (∀ n : Nat, A.value n = 1) ∧ (∀ n : Nat, B.value n = 0) := by
  refine ⟨exactWinAdvantage alwaysBadGame, ?_, ?_, ?_⟩
  · exact
      { value := fun _ => 0
        nonneg := fun _ => Rat.le_refl
        le_one := fun _ => (by decide : (0 : Rat) ≤ 1)
        zero_of_secure := fun h _ => absurd (h 0 trivial) (by simp) }
  · intro n
    exact indicator_of_pos (alwaysBadGame_wins n)
  · intro n
    rfl

/-! ## 3. Event covers: deriving an accounting inequality without tightness -/

/-- **An event cover.**  The protocol bad event at every horizon is contained in
the primitive bad event or in an explicit loss event.  This is the event-level
statement a game-hopping proof establishes by aborting on the hop's loss event;
it is strictly more general than `EventReduction`, which is the empty loss
event. -/
structure EventCover (P C : Game) where
  /-- The underlying deterministic simulation. -/
  event : EventReduction P C
  /-- The event on which the game hop loses its guarantee. -/
  lossEvent : Nat → Prop
  /-- Every protocol win is a primitive win or a loss event. -/
  cover : ∀ n : Nat, P.Wins n → C.Wins n ∨ lossEvent n

/-- Every event-level reduction is a cover with the empty loss event. -/
noncomputable def eventReductionToCover {P C : Game} (R : EventReduction P C) :
    EventCover P C where
  event := R
  lossEvent := fun _ => False
  cover := fun n h => Or.inl (by
    have hmap : R.map (P.run n) = C.run n := R.map_run n
    have hbad : C.bad (R.map (P.run n)) := R.win_transport (P.run n) h
    rw [hmap] at hbad
    exact hbad)

/-- **The accounting inequality derived from a cover.**  The protocol indicator
advantage is at most the primitive indicator advantage plus the *indicator of
the loss event*.  There is no `tight` hypothesis: the inequality is proved from
`cover` by cases on the protocol and primitive win events. -/
theorem EventCover.bound {P C : Game} (E : EventCover P C) (n : Nat) :
    (winAdvantage P).value n ≤
      (winAdvantage C).value n + indicator (E.lossEvent n) := by
  by_cases hP : P.Wins n
  · rw [show (winAdvantage P).value n = 1 from indicator_of_pos hP]
    rcases E.cover n hP with hC | hL
    · have h0 : (0 : Rat) ≤ indicator (E.lossEvent n) := indicator_nonneg _
      have h := (Rat.add_le_add_left (c := (1 : Rat)) (a := (0 : Rat))
        (b := indicator (E.lossEvent n))).mpr h0
      rw [show (winAdvantage C).value n = 1 from indicator_of_pos hC]
      simpa [Rat.add_zero] using h
    · have h0 : (0 : Rat) ≤ (winAdvantage C).value n := (winAdvantage C).nonneg n
      have h := (Rat.add_le_add_right (a := (0 : Rat)) (b := (winAdvantage C).value n)
        (c := (1 : Rat))).mpr h0
      rw [show indicator (E.lossEvent n) = 1 from indicator_of_pos hL]
      simpa [Rat.zero_add] using h
  · rw [show (winAdvantage P).value n = 0 from indicator_of_neg hP]
    exact Rat.add_nonneg ((winAdvantage C).nonneg n) (indicator_nonneg _)

/-- A cover by a secure primitive game is a lossless cover of the *secure*
case: the primitive indicator advantage vanishes. -/
theorem EventCover.bound_of_secure {P C : Game} (E : EventCover P C) (hC : C.Secure)
    (n : Nat) :
    (winAdvantage P).value n ≤ indicator (E.lossEvent n) := by
  have h := E.bound n
  rw [winAdvantage_zero_of_secure hC n, Rat.zero_add] at h
  exact h

/-! ## 4. `Negligible` is closed under addition (the missing arithmetic) -/

/-- Domination: a sequence bounded pointwise by a negligible sequence is
negligible. -/
theorem negligible_of_le {f g : Nat → Rat} (h : ∀ n : Nat, f n ≤ g n)
    (hg : Negligible g) : Negligible f := by
  intro c hc
  obtain ⟨N, hN⟩ := hg c hc
  exact ⟨N, fun n hn => Rat.le_trans (h n) (hN n hn)⟩

/-- A sequence that is identically zero is negligible. -/
theorem negligible_zero : Negligible (fun _ : Nat => (0 : Rat)) := by
  intro c hc
  exact ⟨0, fun n _ => rat_inv_nonneg hc⟩

/-- Any eventually-zero sequence is negligible. -/
theorem negligible_of_eventually_zero {f : Nat → Rat} (h : ∀ n : Nat, f n = 0) :
    Negligible f := by
  refine negligible_of_le (fun n => ?_) negligible_zero
  rw [h n]
  exact Rat.le_refl

/-- **Closure of `Negligible` under addition.**  `docs/CRYPTO-LIMITS.md` §3.1
and §9.5 record this closure as missing; the proof doubles the denominator
(`c + c`) so that the two `1/(c+c)` bounds sum to `1/c`.  This is the arithmetic
that composes a game-hopping loss with a primitive advantage. -/
theorem negligible_add {f g : Nat → Rat} (hf : Negligible f) (hg : Negligible g) :
    Negligible (fun n => f n + g n) := by
  intro c hc
  have h2c : 0 < c + c := by omega
  obtain ⟨Nf, hfN⟩ := hf (c + c) h2c
  obtain ⟨Ng, hgN⟩ := hg (c + c) h2c
  refine ⟨Nat.max Nf Ng, fun n hn => ?_⟩
  have hfn : f n ≤ (1 : Rat) / ((c + c : Nat) : Rat) :=
    hfN n (Nat.le_trans (Nat.le_max_left _ _) hn)
  have hgn : g n ≤ (1 : Rat) / ((c + c : Nat) : Rat) :=
    hgN n (Nat.le_trans (Nat.le_max_right _ _) hn)
  have hsum : f n + g n ≤
      (1 : Rat) / ((c + c : Nat) : Rat) + (1 : Rat) / ((c + c : Nat) : Rat) :=
    rat_add_le_add hfn hgn
  have hkey : (1 : Rat) / ((c + c : Nat) : Rat) + (1 : Rat) / ((c + c : Nat) : Rat)
      = (1 : Rat) / (c : Rat) := by
    rw [rat_natCast_add]
    simp only [Rat.div_def, Rat.one_mul]
    exact rat_inv_add_inv_add (c : Rat) (Rat.ne_of_gt (rat_natCast_pos hc))
  rw [hkey] at hsum
  exact hsum

/-- The constant-one sequence is **not** negligible.  Together with
`negligible_add` this is the sharp boundary: the closure is not the trivial
statement that every sequence is negligible. -/
theorem not_negligible_one : ¬ Negligible (fun _ : Nat => (1 : Rat)) := by
  intro h
  obtain ⟨N, hN⟩ := h 2 (by omega)
  have hle : (1 : Rat) ≤ (1 : Rat) / (2 : Rat) := hN N (Nat.le_refl N)
  exact rat_not_one_le_half hle

/-! ## 5. The exact remaining reduction obligation -/

/-- **The exact remaining obligation.**  A game-based reduction from `P` to `C`
must deliver, for a fixed advantage semantics:

1. `accounting`: the per-horizon inequality `Adv P ≤ Adv C + loss`;
2. `primitive_negligible`: the primitive advantage is negligible;
3. `loss_negligible`: the loss is negligible.

Items 2 and 3 are what make the interface non-trivial: with an arbitrary `loss`
the inequality can always be satisfied (`tautologicalReduction`,
`tautological_loss_not_negligible`).  Nothing in this tree proves item 1 for any
concrete protocol; the field is a specification of the missing step. -/
structure ReductionObligation (P C : Game) where
  /-- Advantage against the protocol game. -/
  protocol : Advantage P
  /-- Advantage against the primitive game. -/
  primitive : Advantage C
  /-- Reduction loss, per horizon. -/
  loss : Nat → Rat
  /-- The loss is non-negative. -/
  loss_nonneg : ∀ n : Nat, 0 ≤ loss n
  /-- **The missing cryptographic accounting step.** -/
  accounting : ∀ n : Nat, protocol.value n ≤ primitive.value n + loss n
  /-- The primitive advantage is negligible. -/
  primitive_negligible : Negligible primitive.value
  /-- The reduction loss is negligible. -/
  loss_negligible : Negligible loss

/-- **The theorem that would follow.**  Accounting plus two negligible sequences
makes the protocol advantage negligible.  This is the shape stated in
`docs/CRYPTO-LIMITS.md` §8.3, with the missing closure step now proved.  It is
arithmetic: it does not assert that any of the three fields holds. -/
theorem ReductionObligation.protocol_negligible {P C : Game}
    (R : ReductionObligation P C) : Negligible R.protocol.value :=
  negligible_of_le (fun n => R.accounting n)
    (negligible_add R.primitive_negligible R.loss_negligible)

/-- The new obligation record contains the base `AdvantageReduction`: every
accounting reduction whose primitive advantage and loss are negligible is an
instance.  Conversely `ReductionObligation` adds exactly the two negligibility
requirements and drops the event field, which the arithmetic does not use. -/
def ReductionObligation.ofAdvantageReduction {P C : Game} (R : AdvantageReduction P C)
    (hp : Negligible R.primitive.value) (hl : Negligible R.loss) :
    ReductionObligation P C where
  protocol := R.protocol
  primitive := R.primitive
  loss := R.loss
  loss_nonneg := R.loss_nonneg
  accounting := R.tight
  primitive_negligible := hp
  loss_negligible := hl

/-- **The tautological reduction.**  For any event reduction and any two
advantage sequences, `loss := protocol.value` satisfies the accounting
inequality.  The interface is therefore satisfiable for every sequence, and its
`bound` theorem is then a tautology; only negligibility of the loss gives it
content. -/
def tautologicalReduction {P C : Game} (R : EventReduction P C) (protocol : Advantage P)
    (primitive : Advantage C) : AdvantageReduction P C where
  event := R
  protocol := protocol
  primitive := primitive
  loss := protocol.value
  loss_nonneg := protocol.nonneg
  tight := fun n => by
    have h := (Rat.add_le_add_right (a := (0 : Rat)) (b := primitive.value n)
      (c := protocol.value n)).mpr (primitive.nonneg n)
    simpa [Rat.zero_add] using h

/-- The tautological loss is literally the protocol advantage. -/
theorem tautologicalReduction_loss {P C : Game} (R : EventReduction P C)
    (protocol : Advantage P) (primitive : Advantage C) :
    (tautologicalReduction R protocol primitive).loss = protocol.value := rfl

/-- **Sharp counterexample 1.**  The accounting inequality is not implied by the
event simulation.  Take the identity event reduction on `unitGame` and the zero
loss: one advantage is identically `1`, the other identically `0`, both are
valid `Advantage` records, and the bound fails at every horizon.  Hence `tight`
cannot be replaced by `map_init`/`map_step`/`win_transport`. -/
theorem accounting_not_implied_by_event :
    ∃ (_R : EventReduction unitGame unitGame) (A B : Advantage unitGame),
      (∀ n : Nat, A.value n = 1) ∧ (∀ n : Nat, B.value n = 0) ∧
        ¬ (∀ n : Nat, A.value n ≤ B.value n + (0 : Rat)) := by
  refine ⟨identityReduction unitGame,
    constantAdvantage (1 : Rat) (by decide) (by decide),
    constantAdvantage (0 : Rat) (by decide) (by decide), ?_, ?_, ?_⟩
  · intro n
    rfl
  · intro n
    rfl
  · intro h
    have h0 := h 0
    rw [Rat.add_zero] at h0
    exact (by decide : ¬ ((1 : Rat) ≤ 0)) h0

/-- **Sharp counterexample 2.**  The tautological reduction can never be used to
discharge the obligation when the protocol advantage is the constant `1`: its
loss is that constant, which is not negligible.  This is why
`ReductionObligation.loss_negligible` is a real requirement rather than
bookkeeping. -/
theorem tautological_loss_not_negligible (R : EventReduction unitGame unitGame) :
    ¬ Negligible (tautologicalReduction R
        (constantAdvantage (1 : Rat) (by decide) (by decide))
        (constantAdvantage (0 : Rat) (by decide) (by decide))).loss := by
  intro h
  exact not_negligible_one h

/-! ## 6. Non-vacuity -/

/-- A concrete lossless cover: a secure primitive game gives a protocol
indicator advantage of zero against the empty loss event. -/
noncomputable def EventCover.ofSecure {P C : Game} (R : EventReduction P C) (_hC : C.Secure) :
    EventCover P C := eventReductionToCover R

/-- Non-vacuity of the lossless branch: on the event-secure unit game the
indicator advantage is zero and the zero loss is negligible. -/
theorem winAdvantage_unitGame : ∀ n : Nat, (winAdvantage unitGame).value n = 0 :=
  winAdvantage_zero_of_secure unitGame_secure

/-- A concrete, non-vacuous instance of `ReductionObligation`: the unit game
against itself, zero advantage, zero loss.  Every field is discharged, so the
interface (and hence `ReductionObligation.protocol_negligible`) is inhabited. -/
noncomputable def zeroObligation : ReductionObligation unitGame unitGame where
  protocol := (exactWinAdvantage unitGame).toAdvantage
  primitive := (exactWinAdvantage unitGame).toAdvantage
  loss := fun _ => 0
  loss_nonneg := fun _ => Rat.le_refl
  accounting := fun n => by
    rw [Rat.add_zero]
    exact Rat.le_refl
  primitive_negligible := negligible_of_eventually_zero winAdvantage_unitGame
  loss_negligible := negligible_zero

/-- The concrete obligation yields the concrete conclusion. -/
theorem zeroObligation_protocol_negligible : Negligible zeroObligation.protocol.value :=
  zeroObligation.protocol_negligible

/-- **End-to-end event route.**  If the primitive game is event-secure and the
loss event of a cover is negligible, the protocol indicator advantage is
negligible.  No tightness field is assumed: the bound comes from `EventCover.bound`
and the arithmetic from `negligible_add`.  This remains an *event-level*
statement — it bounds one particular advantage functional, not the success
probability of an adversary. -/
theorem eventCover_negligible_of_secure {P C : Game} (E : EventCover P C) (hC : C.Secure)
    (hloss : Negligible (fun n => indicator (E.lossEvent n))) :
    Negligible (winAdvantage P).value := by
  refine negligible_of_le (fun n => ?_)
    (negligible_add (negligible_of_eventually_zero (winAdvantage_zero_of_secure hC)) hloss)
  exact E.bound n

/-- **Non-vacuity of the event route.**  The empty-loss cover of the unit game
instantiates `eventCover_negligible_of_secure`: the loss event is `False`, so its
indicator is the zero sequence, and the conclusion is the (already known) zero
advantage.  This pins the hypotheses of the end-to-end theorem to a concrete
instance rather than leaving them as an uninstantiated implication. -/
theorem eventCover_unit_negligible : Negligible (winAdvantage unitGame).value := by
  refine eventCover_negligible_of_secure
    (eventReductionToCover (identityReduction unitGame)) unitGame_secure ?_
  exact negligible_of_eventually_zero (fun _ => indicator_of_neg (fun h => h))

end

end LnLean.Proofs.WaveH.H44
