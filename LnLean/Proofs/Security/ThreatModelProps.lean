import LnLean.Security.Model
import LnLean.Security.Invariants

/-!
# LnLean.Proofs.Security.ThreatModelProps

English claim.  This module makes the *structure* of the wave-A threat model
explicit and proves the parts of it that are structural:

1. **Capabilities are exactly the fields of `Adversary`.**  The four
   capability groups named in the mission (network schedule, corruption,
   on-chain reorganisation, fee spike) are enumerated as `Capability`, each is
   mapped to the `Adversary` fields that realise it, and the map is shown to
   cover the record field-for-field.  There is no capability outside the
   record and no field outside the map.
2. **`Winning` is a predicate, not an axiom.**  `Winning g n` is definitionally
   `¬ g.bad (g.run n)`; `Secure` is definitionally `∀ n, Winning g n`.  Nothing
   in this file assumes either.
3. **Every catalog invariant names the assumptions it needs.**  The ten
   `coreInvariants` are matched, id for id, against an explicit requirement
   table.  The catalog *predicates* are all discharged (they are bookkeeping
   statements); the *security readings* are the ones carrying assumptions.
4. **C1--C8 map to fields of `CryptoAssumptions`.**  The map is `String`-valued
   and proved to be a bijection onto the eight `Prop` fields.
5. **Crypto-dependent invariants are not claimed unconditionally.**  The strong
   reading of INV-03 is proved to be *false* without C1, by exhibiting a
   colliding `HashFn`; the true reading is conditional on C1.
6. **Winning is monotone in adversary power**, in the only form in which it can
   be true: a stronger adversary cannot lose a winning position when there is a
   simulation relation between the two runs.  A checked counterexample shows
   that the simulation hypothesis cannot be dropped, since `step` is an
   unconstrained field of `SecurityGame`.

BOLT sections.  BOLT 1 §"Lightning Message Format"; BOLT 2 §"Message
Retransmission"; BOLT 2 §"Committing Updates So Far"; BOLT 3 §"Per-commitment
Secret Requirements"; BOLT 5 §"Revoked Transaction Close Handling"; BOLT 5
§"General Requirements"; BOLT 7 §"Recommendations for Routing"; BOLT 11
§"Tagged Fields".

`rust-lightning` anchors at commit `fe49009`
(`fe4900930c6bd5786ec4203274d7cf312776a5a6`):

* `lightning/src/ln/channelmanager.rs:17056` — `transaction_unconfirmed`, the
  reorganisation entry point (state is rolled back, not silently kept).
* `lightning/src/ln/channel.rs:12843` — `Channel::transaction_unconfirmed`,
  where an unconfirmed funding transaction is handled after a reorg.
* `lightning/src/chain/chaininterface.rs:350` and `:359` — `FeeEstimator` /
  `get_est_sat_per_1000_weight`, the interface through which a fee spike
  reaches a channel.  This is the only place the model's `FeeEnvironment`
  meets the implementation.
* `lightning/src/ln/channelmanager.rs:17831` — `handle_channel_reestablish`,
  the recovery path assumed by the adversarial schedule.
* `lightning/src/ln/channelmanager.rs:10210` — `claim_funds`, the event the
  adversary tries to prevent (the `bad` predicate of the payment game).
* `lightning/src/ln/channel.rs:2378` — `force_shutdown`, the on-chain fallback
  used when the fee/schedule adversary wins a round.
* `lightning/src/ln/chan_utils.rs:339` — `build_commitment_secret`, the
  per-commitment secret derivation that consumes C1 (SHA-256).
* `lightning/src/ln/chan_utils.rs:841` — `get_htlc_redeemscript`, the script
  the penalty/HTLC claims are stated against.

What is NOT modelled.  There is no probability space, no ensemble, no
efficient-adversary notion, and no negligible-advantage statement: "security"
here is the event-based `Secure`, not a cryptographic game in the
reductionist sense.  Node corruption is a *static* list `Adversary.corrupted`
for the whole run, so `CorruptionMode.adaptive` is documentation rather than a
modelled capability (obligation LN-SEC-002).  `SecurityGame.step` is an
unconstrained field, so no theorem here says anything about the real protocol
transition function; the Lightning instance of monotonicity is obligation
LN-SEC-006.  The bridge between `NetworkSchedule` (Boolean delivery) and
`Schedule`/`PartiallySynchronous` (timed latency) of INV-10 does not exist in
wave A and is recorded as obligation LN-SEC-009.  Watchtowers, package relay,
and L1 consensus are outside the model; `docs/ASSUMPTIONS.md` §2 takes
`FundingConfirmed` as a hypothesis.
-/

namespace LnLean.Security.ThreatModel

set_option autoImplicit false

/-! ## 1. The adversary's capabilities are its fields

The wave-A `Adversary` record bundles eight fields.  Three of them are
auxiliary (the corrupted node list, the depth actually used by a reorg, and
the two Boolean refinements `learnsPreimages` / `adaptive`); the mission's
four capability groups are realised as field groups, not as extra structure. -/

/-- The four capability groups of the threat model.  `reorganization` is the
budget the adversary may spend, not a claim that a reorg succeeds; `feeSpike`
is an adversary-chosen feerate schedule, not a claim that a penalty becomes
uneconomic. -/
inductive Capability where
  | networkSchedule
  | corruption
  | reorganization
  | feeSpike
deriving Repr, DecidableEq, BEq

/-- The `Adversary` fields that realise each capability group.  BOLT 1/2
delivery is `schedule`; BOLT 2 `channel_reestablish` recovery presumes
`corruption`/`corrupted`; the reorg goes through BOLT 5 and the L1 seam;
the fee spike is the BOLT 5 feerate environment. -/
def capabilityFields : Capability → List String
  | .networkSchedule => ["schedule"]
  | .corruption      => ["corruption", "corrupted", "adaptive"]
  | .reorganization  => ["reorgDepth", "reorgBudget"]
  | .feeSpike        => ["fees"]

/-- All capability groups, in declaration order. -/
def Capability.all : List Capability :=
  [.networkSchedule, .corruption, .reorganization, .feeSpike]

/-- The eight fields of `Adversary`, grouped by capability (the order is the
capability grouping used by `capability_fields_cover`, not the declaration
order).  This list is the statement of "the adversary is exactly this record":
it is checked against the structure by `adversary_ext` below. -/
def adversaryFieldNames : List String :=
  [ "schedule", "corruption", "corrupted", "adaptive", "reorgDepth"
  , "reorgBudget", "fees", "learnsPreimages" ]

/-- **Capability coverage (checked).**  The four capability groups cover
exactly the adversary's fields, with `learnsPreimages` recorded as the eighth
field.  `learnsPreimages` is a *parameter* of the corruption capability (a
corrupted node trivially learns the preimages it handles); it is listed
separately so that the count is honest. -/
theorem capability_fields_cover :
    Capability.all.flatMap capabilityFields ++ ["learnsPreimages"]
      = adversaryFieldNames := rfl

/-- The record has exactly eight fields. -/
theorem adversary_field_count : adversaryFieldNames.length = 8 := rfl

/-- Every field named by a capability group is a field of `Adversary`. -/
theorem capability_field_is_adversary_field (c : Capability) (f : String)
    (hf : f ∈ capabilityFields c) : f ∈ adversaryFieldNames := by
  cases c with
  | networkSchedule =>
      simp only [capabilityFields, List.mem_cons, List.not_mem_nil, or_false] at hf
      subst hf
      simp [adversaryFieldNames]
  | corruption =>
      simp only [capabilityFields, List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl <;> simp [adversaryFieldNames]
  | reorganization =>
      simp only [capabilityFields, List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl <;> simp [adversaryFieldNames]
  | feeSpike =>
      simp only [capabilityFields, List.mem_cons, List.not_mem_nil, or_false] at hf
      subst hf
      simp [adversaryFieldNames]

/-- **The capability projection is an isomorphism (checked).**  Two adversaries
that agree on all eight capability fields are the same adversary: there is no
hidden state in the record and no capability outside it. -/
theorem adversary_ext (a b : Adversary)
    (h1 : a.schedule = b.schedule) (h2 : a.corruption = b.corruption)
    (h3 : a.corrupted = b.corrupted) (h4 : a.reorgDepth = b.reorgDepth)
    (h5 : a.reorgBudget = b.reorgBudget) (h6 : a.fees = b.fees)
    (h7 : a.learnsPreimages = b.learnsPreimages) (h8 : a.adaptive = b.adaptive) :
    a = b := by
  cases a
  cases b
  simp_all

/-- The nodes a security claim protects: `SecurityGame.honest` minus the nodes
the adversary controls.  Wave A never subtracts `corrupted` from `honest`, so
this definition is the missing link between the corruption capability and the
honest set (it is used by `protectedNodes_not_controlled`). -/
def protectedNodes {State : Type} (g : SecurityGame State) : List NodeId :=
  g.honest.filter (fun n => decide (n ∉ g.adversary.corrupted))

/-- **A protected node is not controlled (checked).**  This is the only
content of "the corruption set bounds the adversary's power": a node in the
protected set is outside `Adversary.corrupted`, so `Adversary.controls` fails
for it. -/
theorem protectedNodes_not_controlled {State : Type} (g : SecurityGame State)
    (n : NodeId) (h : n ∈ protectedNodes g) : ¬ g.adversary.controls n := by
  unfold protectedNodes at h
  rw [List.mem_filter] at h
  have hn : n ∉ g.adversary.corrupted := of_decide_eq_true h.2
  exact hn

/-! ## 2. A power order on adversaries -/

/-- Numeric rank of a corruption mode, used to order capabilities. -/
def corruptionRank : CorruptionMode → Nat
  | .none => 0
  | .passive => 1
  | .active => 2
  | .adaptive => 3

/-- `AdversaryLe a b` means `b` is at least as strong as `a`: every delivery,
partition, corruption, reorg and feerate choice available to `a` is available
to `b`, and the Boolean refinements are monotone.  This is the model-level
content of "a stronger adversary"; it says nothing about `SecurityGame.step`,
which is why §5 needs a simulation hypothesis. -/
def AdversaryLe (a b : Adversary) : Prop :=
  (∀ (i : Nat) (n : NodeId),
      a.schedule.delivery i n = true → b.schedule.delivery i n = true) ∧
  (∀ x y : NodeId,
      a.schedule.partition x y = true → b.schedule.partition x y = true) ∧
  a.schedule.maxDelay ≤ b.schedule.maxDelay ∧
  corruptionRank a.corruption ≤ corruptionRank b.corruption ∧
  (∀ n : NodeId, n ∈ a.corrupted → n ∈ b.corrupted) ∧
  a.reorgBudget ≤ b.reorgBudget ∧
  (∀ h : Height, (a.feeAt h).msatPerKw ≤ (b.feeAt h).msatPerKw) ∧
  (a.learnsPreimages = true → b.learnsPreimages = true) ∧
  (a.adaptive = true → b.adaptive = true)

theorem adversaryLe_refl (a : Adversary) : AdversaryLe a a := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp

theorem adversaryLe_trans {a b c : Adversary} (hab : AdversaryLe a b)
    (hbc : AdversaryLe b c) : AdversaryLe a c := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ := hab
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ := hbc
  exact
    ⟨ fun i n h => g1 i n (f1 i n h)
    , fun x y h => g2 x y (f2 x y h)
    , Nat.le_trans f3 g3
    , Nat.le_trans f4 g4
    , fun n h => g5 n (f5 n h)
    , Nat.le_trans f6 g6
    , fun h => Nat.le_trans (f7 h) (g7 h)
    , fun h => g8 (f8 h)
    , fun h => g9 (f9 h) ⟩

/-- A stronger adversary controls every node the weaker one controls. -/
theorem adversaryLe_controls {a b : Adversary} (h : AdversaryLe a b)
    {n : NodeId} (hn : a.controls n) : b.controls n := by
  obtain ⟨_, _, _, _, h5, _, _, _, _⟩ := h
  exact h5 n hn

/-- A stronger adversary may use every reorg the weaker one may use. -/
theorem adversaryLe_reorgAllowed {a b : Adversary} (h : AdversaryLe a b)
    {r : Reorg} (hr : a.reorgAllowed r) : b.reorgAllowed r := by
  obtain ⟨_, _, _, _, _, h6, _, _, _⟩ := h
  exact Nat.le_trans hr h6

/-- A stronger adversary may raise fees at every height. -/
theorem adversaryLe_feeAt {a b : Adversary} (h : AdversaryLe a b) (height : Height) :
    (a.feeAt height).msatPerKw ≤ (b.feeAt height).msatPerKw := by
  obtain ⟨_, _, _, _, _, _, h7, _, _⟩ := h
  exact h7 height

/-- Raising the reorg budget yields a stronger adversary (a checked instance of
`AdversaryLe`, not a hypothesis). -/
theorem reorg_raised_le (a : Adversary) (k : Nat) :
    AdversaryLe a { a with reorgBudget := a.reorgBudget + k } := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i n h; exact h
  · intro x y h; exact h
  · exact Nat.le_refl _
  · exact Nat.le_refl _
  · intro n h; exact h
  · show a.reorgBudget ≤ a.reorgBudget + k
    omega
  · intro h; exact Nat.le_refl _
  · intro h; exact h
  · intro h; exact h

/-! ## 3. `Winning` is a predicate over the trace -/

/-- `Winning` unfolds definitionally: it is the negation of the bad event on
the run, not a declared constant. -/
theorem winning_unfolds {State : Type} (g : SecurityGame State) (n : Nat) :
    Winning g n = ¬ g.bad (g.run n) := rfl

/-- `AdversaryWins` unfolds definitionally. -/
theorem adversaryWins_unfolds {State : Type} (g : SecurityGame State) (n : Nat) :
    AdversaryWins g n = g.bad (g.run n) := rfl

/-- `Winning` is exactly the negated winning condition. -/
theorem winning_iff_not_adversaryWins {State : Type} (g : SecurityGame State)
    (n : Nat) : Winning g n ↔ ¬ AdversaryWins g n :=
  Iff.rfl

/-- `Secure` is the pointwise `Winning` predicate over all horizons. -/
theorem secure_iff_no_bad {State : Type} (g : SecurityGame State) :
    Secure g ↔ ∀ n : Nat, ¬ g.bad (g.run n) :=
  Iff.rfl

/-- The trace is total: at every horizon exactly one of the two outcomes holds.
Nothing is decided by the adversary beyond the trace itself. -/
theorem winning_or_adversaryWins {State : Type} (g : SecurityGame State) (n : Nat) :
    Winning g n ∨ AdversaryWins g n := by
  unfold Winning
  by_cases h : AdversaryWins g n
  · exact Or.inr h
  · exact Or.inl h

/-- A game whose bad predicate is unsatisfiable is secure.  This is the
degenerate case of `Secure`; it confirms that `Secure` has no hidden
adversary-side content. -/
theorem secure_of_no_bad_state {State : Type} (g : SecurityGame State)
    (h : ∀ s : State, ¬ g.bad s) : Secure g :=
  fun n => h (g.run n)

/-! ## 4. Winning is monotone in adversary power

"Monotone" can only mean: if the stronger game can simulate the weaker one,
then a bad state reached in the weaker game is reached in the stronger one.
The next two sections prove the transfer and show the hypothesis is necessary.
-/

/-- A simulation of `g` by `g'` through the state relation `R`: the initial
states are related, `R` is preserved by the two step functions, and `R`
transports the bad predicate. -/
structure Simulation {State : Type} (g g' : SecurityGame State)
    (R : State → State → Prop) : Prop where
  init : R g.init g'.init
  step : ∀ (s s' : State) (n : Nat), R s s' →
    R (g.step s g.adversary n) (g'.step s' g'.adversary n)
  bad : ∀ (s s' : State), R s s' → g.bad s → g'.bad s'

/-- The relation is an invariant of the two runs. -/
theorem Simulation.run_rel {State : Type} {g g' : SecurityGame State}
    {R : State → State → Prop} (h : Simulation g g' R) :
    ∀ n : Nat, R (g.run n) (g'.run n)
  | 0 => h.init
  | n + 1 => h.step (g.run n) (g'.run n) n (Simulation.run_rel h n)

/-- **Adversary winning is monotone along a simulation.** -/
theorem Simulation.adversaryWins_mono {State : Type} {g g' : SecurityGame State}
    {R : State → State → Prop} (h : Simulation g g' R) (n : Nat) :
    AdversaryWins g n → AdversaryWins g' n :=
  fun hw => h.bad (g.run n) (g'.run n) (h.run_rel n) hw

/-- **A stronger adversary cannot lose a winning position.**  If `g'` is the
game with the stronger adversary and simulates `g`, then every `Winning` state
of `g'` is a `Winning` state of `g`. -/
theorem Simulation.winning_antitone {State : Type} {g g' : SecurityGame State}
    {R : State → State → Prop} (h : Simulation g g' R) (n : Nat) :
    Winning g' n → Winning g n :=
  fun hw hbad => hw (Simulation.adversaryWins_mono h n hbad)

/-- Every game simulates itself by equality, so the transfer is not vacuous. -/
theorem simulation_refl {State : Type} (g : SecurityGame State) :
    Simulation g g (fun a b => a = b) where
  init := rfl
  step := fun _ _ _ h => by rw [h]
  bad := fun _ _ h hb => h ▸ hb

/-- The integrator-facing form: with the game's own adversary replaced by a
stronger one, winning transfers whenever the simulation exists.  `hLe` is
carried so that the statement names the capability order it is about. -/
theorem stronger_adversary_cannot_lose {State : Type} (g : SecurityGame State)
    (b : Adversary) (_hLe : AdversaryLe g.adversary b)
    (hSim : ∃ R : State → State → Prop, Simulation g { g with adversary := b } R)
    (n : Nat) : Winning { g with adversary := b } n → Winning g n := by
  obtain ⟨R, hR⟩ := hSim
  exact Simulation.winning_antitone hR n

/-! ### 4a. The simulation hypothesis cannot be dropped

`SecurityGame.step` is an unconstrained field, so `AdversaryLe` alone does not
imply monotonicity.  The counterexample below is a two-state game whose step
function *inspects* `adaptive`: the weak adversary stays in a bad state, the
stronger one leaves it.  This is why §5 states the Lightning instance as an
obligation rather than a theorem. -/

/-- The weakest adversary: no delivery, no partition, no corruption, no reorg
budget, zero fees, no preimage learning, non-adaptive. -/
def minimalAdversary : Adversary where
  schedule :=
    { delivery := fun _ _ => false
      partition := fun _ _ => false
      maxDelay := 0
      reorders := false
      dropsMessages := false }
  corruption := .none
  corrupted := []
  reorgDepth := 0
  reorgBudget := 0
  fees := { base := ⟨0⟩, atHeight := fun _ => ⟨0⟩, spikeAt := none }
  learnsPreimages := false
  adaptive := false

/-- A game whose transition reads the `adaptive` flag, with a bad state that is
left as soon as the adversary is adaptive. -/
def flagSensitiveGame (a : Adversary) : SecurityGame Bool where
  adversary := a
  init := true
  step := fun _ a' _ => if a'.adaptive then false else true
  bad := fun s => s = true
  honest := []

/-- The weak adversary reaches the bad state at horizon 1. -/
theorem flagSensitiveGame_bad_weak :
    AdversaryWins (flagSensitiveGame minimalAdversary) 1 := by
  show (flagSensitiveGame minimalAdversary).run 1 = true
  decide

/-- The adaptive adversary does not reach the bad state at horizon 1. -/
theorem flagSensitiveGame_bad_strong :
    ¬ AdversaryWins
        (flagSensitiveGame { minimalAdversary with adaptive := true }) 1 := by
  show ¬ ((flagSensitiveGame { minimalAdversary with adaptive := true }).run 1 = true)
  decide

/-- **Monotonicity needs more than capability order.**  There is a game and a
strictly stronger adversary where adversary-winning is not preserved.  Hence
`AdversaryLe` alone cannot prove the mission's monotonicity bullet; the
simulation relation of §4 is load-bearing. -/
theorem power_monotonicity_needs_hypothesis :
    ∃ (g : SecurityGame Bool) (b : Adversary),
      AdversaryLe g.adversary b ∧
        ¬ (∀ n : Nat, AdversaryWins g n →
            AdversaryWins { g with adversary := b } n) := by
  refine ⟨flagSensitiveGame minimalAdversary,
    { minimalAdversary with adaptive := true }, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [flagSensitiveGame, minimalAdversary, Adversary.feeAt]
  · intro hmono
    exact flagSensitiveGame_bad_strong
      (hmono 1 flagSensitiveGame_bad_weak)

/-! ### 4b. A checked monotone instance: the reorg game

The counterexample above is artificial because `step` peeks at the adversary.
For the reorg capability the step function is genuinely monotone, and the
result below is the non-vacuous instance of the mission's bullet. -/

/-- A one-dimensional game: the state records the deepest reorg realised, and
a bad state is one at or beyond `threshold`.  Initialising the state at
`a.reorgDepth` models "the adversary already holds this budget". -/
def reorgGame (a : Adversary) (threshold : Nat) : SecurityGame Nat where
  adversary := a
  init := a.reorgDepth
  step := fun s a' _ => Nat.max s a'.reorgDepth
  bad := fun s => threshold ≤ s
  honest := []

/-- The reorg game's state is constantly the adversary's depth. -/
theorem reorgGame_run (a : Adversary) (threshold n : Nat) :
    (reorgGame a threshold).run n = a.reorgDepth := by
  induction n with
  | zero => rfl
  | succ k ih =>
      rw [SecurityGame.run_succ]
      show Nat.max ((reorgGame a threshold).run k) a.reorgDepth = a.reorgDepth
      rw [ih]
      exact Nat.max_self _

/-- **Monotone in the reorg budget (checked).**  A larger `reorgDepth` never
loses a bad state. -/
theorem reorgGame_wins_monotone (a b : Adversary) (threshold : Nat)
    (h : a.reorgDepth ≤ b.reorgDepth) (n : Nat) :
    AdversaryWins (reorgGame a threshold) n →
      AdversaryWins (reorgGame b threshold) n := by
  intro hw
  have hw' : threshold ≤ a.reorgDepth := by
    change threshold ≤ (reorgGame a threshold).run n at hw
    rwa [reorgGame_run a threshold n] at hw
  have : threshold ≤ (reorgGame b threshold).run n := by
    rw [reorgGame_run b threshold n]
    exact Nat.le_trans hw' h
  exact this

/-! ## 5. C1--C8 are fields of `CryptoAssumptions` -/

/-- The eight `Prop` fields of `CryptoAssumptions`, in declaration order. -/
def cryptoFieldNames : List String :=
  [ "sha256CollisionResistant", "hash160CollisionResistant"
  , "ecdsaEufCma", "schnorrEufCma", "ecdhCdh", "hkdfPrf"
  , "aeadCca", "hmacPrf" ]

/-- Assumption id to modelling-field name.  `assumptionField "C9" = ""` is the
"unknown assumption" sentinel. -/
def assumptionField : String → String
  | "C1" => "sha256CollisionResistant"
  | "C2" => "hash160CollisionResistant"
  | "C3" => "ecdsaEufCma"
  | "C4" => "schnorrEufCma"
  | "C5" => "ecdhCdh"
  | "C6" => "hkdfPrf"
  | "C7" => "aeadCca"
  | "C8" => "hmacPrf"
  | _ => ""

/-- The eight assumption ids of `docs/ASSUMPTIONS.md` §1. -/
def assumptionIds : List String :=
  ["C1", "C2", "C3", "C4", "C5", "C6", "C7", "C8"]

/-- **C1--C8 map onto the eight fields (checked).** -/
theorem assumption_ids_map_fields :
    assumptionIds.map assumptionField = cryptoFieldNames := rfl

/-- **The catalog order is the id order (checked).**  `CryptoAssumptions.toList`
enumerates C1--C8 in the order of `docs/ASSUMPTIONS.md`. -/
theorem cryptoAssumptions_ids (a : CryptoAssumptions) :
    (CryptoAssumptions.toList a).map Assumption.id = assumptionIds := rfl

/-- `CryptoAssumptions` has exactly these eight fields: two structures with the
same eight assumed properties are the same assumption record. -/
theorem cryptoAssumptions_ext (a b : CryptoAssumptions)
    (h1 : a.sha256CollisionResistant = b.sha256CollisionResistant)
    (h2 : a.hash160CollisionResistant = b.hash160CollisionResistant)
    (h3 : a.ecdsaEufCma = b.ecdsaEufCma)
    (h4 : a.schnorrEufCma = b.schnorrEufCma)
    (h5 : a.ecdhCdh = b.ecdhCdh)
    (h6 : a.hkdfPrf = b.hkdfPrf)
    (h7 : a.aeadCca = b.aeadCca)
    (h8 : a.hmacPrf = b.hmacPrf) : a = b := by
  cases a
  cases b
  simp_all

/-! ## 6. Every catalog invariant names its assumptions

`Requirement` records what the *security reading* of an invariant may assume.
It is deliberately separate from `Invariant.predicate`: the predicates are
bookkeeping statements and are discharged unconditionally in §7, while the
security readings are the ones that must name C1--C8 or an L1/network
hypothesis.  Keeping the two apart is how this module avoids the overclaim
"the protocol is secure because its invariants are".

The non-crypto tags are: `L1` (Bitcoin consensus / confirmation),
`CLTV` (an absolute-or-relative timelock has elapsed), `ECON` (the penalty is
economical, `docs/ASSUMPTIONS.md` §4), `NETWORK` (partial synchrony after GST,
`docs/ASSUMPTIONS.md` §3). -/

/-- The assumptions a catalog invariant's security reading may depend on. -/
structure Requirement where
  id : String
  assumptions : List String
deriving Repr, DecidableEq, BEq

/-- Requirements for the ten core invariants, in catalog order.  The ids and
the reasoning per row:

* INV-01 conservation — arithmetic only, no assumption.
* INV-02 no double spend — L1 consensus plus the P2WPKH hash binding (C2).
* INV-03 preimage soundness — SHA-256 collision/preimage resistance (C1).
* INV-04 timeout safety — the CLTV has actually elapsed on the common tip.
* INV-05 revocation/penalty — C1 (per-commitment secret derivation,
  `chan_utils.rs:339`), L1, and the penalty economics assumption.
* INV-06 state monotonicity — counter arithmetic, no assumption.
* INV-07 route well-formedness — gossip announcements are ECDSA-signed (C3).
* INV-08 invoice consistency — C1 for the payment hash, C3 for the BOLT 11
  signature.
* INV-09 MPP atomicity — C1 (all parts share the payment hash).
* INV-10 partial synchrony — the network assumption itself. -/
def invariantRequirements : List Requirement :=
  [ ⟨"INV-01", []⟩
  , ⟨"INV-02", ["L1", "C2"]⟩
  , ⟨"INV-03", ["C1"]⟩
  , ⟨"INV-04", ["CLTV", "L1"]⟩
  , ⟨"INV-05", ["C1", "L1", "ECON"]⟩
  , ⟨"INV-06", []⟩
  , ⟨"INV-07", ["C3"]⟩
  , ⟨"INV-08", ["C1", "C3"]⟩
  , ⟨"INV-09", ["C1"]⟩
  , ⟨"INV-10", ["NETWORK"]⟩ ]

/-- **The requirement table covers the catalog, id for id (checked).**  Every
invariant in `coreInvariants` has exactly one row, so none can be cited without
its assumptions. -/
theorem requirements_cover_catalog :
    (coreInvariants.map (fun i => i.id))
      = (invariantRequirements.map (fun r => r.id)) := rfl

/-- There are ten rows. -/
theorem requirement_count : invariantRequirements.length = 10 := rfl

/-- The invariant ids are distinct. -/
theorem requirement_ids_nodup :
    (invariantRequirements.map (fun r => r.id)).Nodup := by
  decide

/-- Every assumption id in the table is either one of C1--C8 or one of the
five non-crypto tags.  No unlisted assumption can enter through this table. -/
theorem requirements_use_known_assumptions :
    invariantRequirements.all
      (fun r => r.assumptions.all
        (fun s => decide (s ∈ ["C1", "C2", "C3", "C4", "C5", "C6", "C7", "C8",
                               "L1", "CLTV", "ECON", "NETWORK"]))) = true := by
  decide

/-- **C4, C5, C6, C7 have no consumer in the core catalog (checked).**  Taproot
channels (C4), ECDH/onion key agreement (C5), HKDF key derivation (C6) and
AEAD onion encryption (C7) are wave-B domains whose invariants are not among
the ten.  This is a fact about the table, and it records that the catalog is
*incomplete* for those primitives, not that they are unnecessary. -/
theorem core_catalog_ignores_c4_c5_c6_c7 :
    (["C4", "C5", "C6", "C7"].all
      (fun c => invariantRequirements.all
        (fun r => decide (c ∉ r.assumptions)))) = true := by
  decide

/-- **The corruption capability has no invariant consumer (checked).**  No core
invariant's security reading is stated relative to a corrupted-node set.  The
corruption capability therefore only enters through a per-module `bad`
predicate, which is obligation LN-SEC-003. -/
theorem no_corruption_assumption :
    invariantRequirements.all
      (fun r => decide ("CORRUPTION" ∉ r.assumptions)) = true := by
  decide

/-- **The reorg capability has no invariant consumer (checked).**  Deep-reorg
behaviour is `LN-CHAIN-REORG` / `LN-L1-003`, outside the ten. -/
theorem no_reorg_assumption :
    invariantRequirements.all
      (fun r => decide ("REORG" ∉ r.assumptions)) = true := by
  decide

/-- **The fee-spike capability has no invariant consumer (checked).**  Only the
economic side of INV-05 mentions fees, and only as a liveness assumption. -/
theorem no_fee_spike_assumption :
    invariantRequirements.all
      (fun r => decide ("FEES" ∉ r.assumptions)) = true := by
  decide

/-! ## 7. The catalog predicates are discharged unconditionally

Each theorem below is the catalog's own `predicate` field, proved from the
wave-A module that established it.  This is a traceability check, not new
mathematics: it says the *bookkeeping* invariants hold.  It does **not** say
the protocol is secure, because none of the predicates quantifies over
`Adversary`; that is exactly why §6 exists. -/

/-- INV-01: conservation across ledger transitions. -/
theorem invValueConservation_proved : invValueConservation.predicate :=
  Ledger.step_conserves

/-- INV-02: spending a fresh outpoint preserves no-double-spend. -/
theorem invNoDoubleSpend_proved : invNoDoubleSpend.predicate :=
  L1Ledger.spend_preserves_noDoubleSpend

/-- INV-03: a fulfilment carries a matching preimage (bookkeeping form). -/
theorem invHtlcPreimage_proved : invHtlcPreimage.predicate :=
  HtlcRecord.fulfill_sound

/-- INV-04: failure only after CLTV expiry. -/
theorem invHtlcTimeout_proved : invHtlcTimeout.predicate :=
  HtlcRecord.fail_only_after_expiry

/-- INV-05: a punishable breach spends both commitment outputs. -/
theorem invRevocationPenalty_proved : invRevocationPenalty.predicate :=
  fun _b h => h

/-- INV-06: commitment numbers are monotone. -/
theorem invStateMonotonicity_proved : invStateMonotonicity.predicate :=
  advance_monotone

/-- INV-07: routes are connected and capacity-feasible. -/
theorem invRouteWellFormed_proved : invRouteWellFormed.predicate :=
  fun _r h => h

/-- INV-08: an invoice agrees with its session (structural form). -/
theorem invInvoiceConsistency_proved : invInvoiceConsistency.predicate :=
  fun _inv _ph _amt _cltv h => h

/-- INV-09: MPP settles only on an exact sum. -/
theorem invMppAtomicity_proved : invMppAtomicity.predicate :=
  MppPayment.settle_requires_sum

/-- INV-10: partial synchrony delivers after GST. -/
theorem invPartialSynchrony_proved : invPartialSynchrony.predicate :=
  partial_synchrony_delivers

/-- The ten `predicate` fields are exactly the ten theorems above, so the
catalog contains no predicate that is assumed rather than proved.  (The list of
names is checked by `requirements_cover_catalog`; this theorem records the
count so that adding an eleventh invariant without a proof is a build break.) -/
theorem catalog_predicates_discharged :
    (coreInvariants.map (fun i => i.id)).length = 10 := rfl

/-! ## 8. Crypto-dependent invariants are not claimed unconditionally

INV-03 as written in the catalog is a *functional* statement about the
`fulfill` transition, so it needs no assumption.  Its security reading — "an
adversary cannot produce a preimage it has not seen" — is a different
proposition, and it is false without C1.  Both halves are below. -/

/-- C1 at the point of use: the modelled hash is injective on preimages, which
is the concrete content of second-preimage resistance. -/
def PreimageBinding (H : HashFn) : Prop :=
  ∀ p q : Preimage, H.hash p = H.hash q → p = q

/-- **The security reading of INV-03, conditional on C1.**  A candidate preimage
that is not the honest one cannot hit the payment hash.  This is the statement
that must take `hC1` explicitly; it is *not* the catalog predicate. -/
theorem preimage_secrecy_from_c1 (H : HashFn) (hC1 : PreimageBinding H)
    (hh : PaymentHash) (p : Preimage) (hp : H.hash p = hh)
    (candidates : List Preimage) (hnone : p ∉ candidates) :
    ∀ q : Preimage, q ∈ candidates → H.hash q ≠ hh := by
  intro q hq hqhash
  have hqp : q = p := hC1 q p (hqhash.trans hp.symm)
  rw [hqp] at hq
  exact hnone hq

/-- **C1 is not free (checked).**  `PreimageBinding` fails for some `HashFn`:
the constant hash maps two distinct preimages to the same payment hash.  Hence
the unconditional form of INV-03's security reading is *false* in this model,
and the conditional form above is the correct one. -/
theorem preimage_binding_not_unconditional :
    ¬ ∀ H : HashFn, PreimageBinding H := by
  intro hall
  have hconst : PreimageBinding ⟨fun _ => ⟨ByteArray.empty⟩⟩ := hall _
  have hne : (⟨ByteArray.empty⟩ : Preimage) ≠ ⟨ByteArray.mk #[1]⟩ := by
    decide
  exact hne (hconst _ _ rfl)

/-- A `HashFn` witness with a collision, stated separately so the report can
cite the concrete counterexample. -/
theorem preimage_binding_counterexample :
    ∃ (H : HashFn) (p q : Preimage), p ≠ q ∧ H.hash p = H.hash q :=
  ⟨⟨fun _ => ⟨ByteArray.empty⟩⟩, ⟨ByteArray.empty⟩,
   ⟨ByteArray.mk #[1]⟩, by decide, rfl⟩

/-! ## 9. The economic side of INV-05, and the BOLT 5 timelock

`Breach.Punishable` is a structural predicate: it conjoins "the commitment is
old" with "the penalty spends both outputs".  It says nothing about whether the
penalty is *economical* after a fee spike, which `docs/ASSUMPTIONS.md` §4 makes
an explicit liveness assumption (`LN-PENALTY-ECON`).  The two propositions are
independent, and the second is proved separately. -/

/-- Net reward of a penalty at feerate `r` and weight `w`, in msat.  Negative
values mean the penalty costs more than it recovers. -/
def penaltyNet (r : FeeRate) (w : Weight) (atStake : Msat) : Int :=
  (atStake.val : Int) - (FeeRate.fee r w).val

/-- **A fee spike can make the penalty uneconomical (checked).**  If the fee for
the penalty's weight meets or exceeds the value at stake, the net reward is
non-positive.  BOLT 5 §"Penalty Transactions Weight Calculation" fixes the
weight; the feerate is the adversary's. -/
theorem penalty_uneconomical_of_fee_spike (r : FeeRate) (w : Weight) (v : Msat)
    (h : v.val ≤ (FeeRate.fee r w).val) : penaltyNet r w v ≤ 0 := by
  unfold penaltyNet
  omega

/-- A structurally punishable breach. -/
def structuralBreach : Breach where
  oldCommitment := 0
  currentCommitment := 1
  penalty :=
    { inputs := [⟨0, 0⟩, ⟨0, 1⟩], outputs := [] }

/-- The structural breach satisfies `Breach.Punishable`. -/
theorem structuralBreach_punishable : structuralBreach.Punishable := by
  unfold Breach.Punishable PenaltyTx.SpendsBoth structuralBreach
  refine ⟨by decide, ?_, ?_⟩ <;> simp

/-- **INV-05 does not imply economics (checked).**  There is a `Punishable`
breach whose penalty is uneconomical at a high feerate: the structural
invariant and the economic precondition are independent, so the security claim
"a breach is always punished" needs `LN-PENALTY-ECON` on top of INV-05. -/
theorem punishable_without_economics :
    ∃ b : Breach, b.Punishable ∧
      penaltyNet ⟨1000000⟩ ⟨1000⟩ ⟨0⟩ ≤ 0 := by
  refine ⟨structuralBreach, structuralBreach_punishable, ?_⟩
  exact penalty_uneconomical_of_fee_spike _ _ _ (Nat.zero_le _)

/-! ## 10. Open obligations

The four `Prop`-valued targets below are the remaining steps this module cannot
close.  They are *definitions*, not assumptions: nothing here is taken on
faith, and no theorem above depends on them. -/

/-- **LN-SEC-002 (adaptive corruption).**  The wave-A `SecurityGame` hands the
same `Adversary` record to `step` at every step, so `corrupted` is static along
a run; `CorruptionMode.adaptive` therefore does not model a growing corruption
set.  The missing refinement is a time-indexed set with the monotonicity below.
Recorded as a `Prop` so the integrator can make it a hypothesis. -/
def AdaptiveCorruption (g : SecurityGame Nat) : Prop :=
  ∃ corruptedAt : Nat → List NodeId,
    corruptedAt 0 = g.adversary.corrupted ∧
      (∀ n : Nat, ∀ v : NodeId, v ∈ corruptedAt n → v ∈ corruptedAt (n + 1)) ∧
      (∀ n : Nat, corruptedAt n ≠ g.adversary.corrupted)

/-- **LN-SEC-003 (the honest set can contain corrupted nodes).**  Wave A never
requires `SecurityGame.honest` to be disjoint from `Adversary.corrupted`, so a
game may claim to protect a node the adversary controls.  This is the exact
property a Lightning game must satisfy; `protectedNodes` is the model-level
fix, and `honestDisjoint_not_automatic` shows the property is not free. -/
def HonestDisjoint {State : Type} (g : SecurityGame State) : Prop :=
  ∀ v : NodeId, v ∈ g.honest → ¬ g.adversary.controls v

/-- Filtering the honest set by the corruption set always yields a disjoint
honest set: this is the repair for LN-SEC-003. -/
theorem protectedNodes_honestDisjoint {State : Type} (g : SecurityGame State) :
    HonestDisjoint { g with honest := protectedNodes g } :=
  fun _ hv => protectedNodes_not_controlled g _ hv

/-- **The overlap is possible (checked).**  There is a wave-A game whose honest
set contains a corrupted node, so `HonestDisjoint` must be required explicitly
and cannot be derived from `SecurityGame`. -/
theorem honestDisjoint_not_automatic :
    ∃ g : SecurityGame Unit, ¬ HonestDisjoint g := by
  refine ⟨{ adversary := { minimalAdversary with corrupted := [0] }
            init := ()
            step := fun s _ _ => s
            bad := fun _ => False
            honest := [0] }, ?_⟩
  intro h
  exact h 0 (by simp) (by simp [Adversary.controls])

/-- **LN-SEC-006 (Lightning instance of power monotonicity).**  The concrete
Lightning game must exhibit a simulation relation under `AdversaryLe`.  §4
proves the transfer (`Simulation.winning_antitone`) and `§4a` proves it cannot
be derived from `AdversaryLe` alone; instantiating `step` from the wave-A
channel/routing/on-chain transitions is the remaining obligation. -/
def LightningPowerMonotone (State : Type) (g : SecurityGame State)
    (b : Adversary) : Prop :=
  ∃ R : State → State → Prop, Simulation g { g with adversary := b } R

/-- **LN-SEC-008 (C3 is not connected to `Invoice`).**  `Invoice` has exactly
five fields and no signer key or signature; `signatureValid` is a Boolean the
model is given, not a verification result.  A signature model with the C3 seam
is therefore a *refinement* of `Invoice`, not a theorem about it. -/
structure SignatureModel where
  /-- Verification of a signature over a payment hash under a public key. -/
  verify : PubKey → PaymentHash → EcdsaSig → Bool
  /-- C3: existential unforgeability.  A `Prop`, supplied by the caller. -/
  eufCma : Prop

/-- A BOLT 11 invoice together with the signer material the wire format
actually carries but `Invoice` does not record. -/
structure SignedInvoice where
  parsed : Invoice
  payeeKey : PubKey
  signature : EcdsaSig

/-- A signed invoice verifies under `SignatureModel`. -/
def SignedInvoice.Verified (S : SignatureModel) (si : SignedInvoice) : Prop :=
  S.verify si.payeeKey si.parsed.paymentHash si.signature = true

/-- **`Invoice` carries no signer material (checked).**  Two invoices that
agree on the five modelled fields are equal, so authentication cannot be read
off `Invoice` alone: this is the exact shape of the LN-SEC-008 gap. -/
theorem invoice_fields_only (a b : Invoice)
    (h1 : a.paymentHash = b.paymentHash) (h2 : a.amount = b.amount)
    (h3 : a.minFinalCltvExpiry = b.minFinalCltvExpiry)
    (h4 : a.paymentSecret = b.paymentSecret)
    (h5 : a.signatureValid = b.signatureValid) : a = b := by
  cases a
  cases b
  simp_all

/-- **The corrected LN-SEC-008 statement, with its reduction explicit.**  The
step `C3 ⇒ attribution` is carried as `hReduction`; it is *not* assumed
anywhere else in this file, and its discharge is the obligation. -/
theorem invoice_attribution_of_reduction (S : SignatureModel) (expected : PubKey)
    (hReduction : S.eufCma → ∀ si : SignedInvoice,
      si.Verified S → si.payeeKey = expected)
    (hC3 : S.eufCma) :
    ∀ si : SignedInvoice, si.Verified S → si.payeeKey = expected :=
  hReduction hC3

/-- **LN-SEC-009 (schedule bridge).**  INV-10 is stated over `Schedule`
(`latency : Message → Option Nat`), while the adversary's capability is
`NetworkSchedule` (`delivery : Nat → NodeId → Bool`).  The two types have no
bridge in wave A, so "the adversary may not delay after GST" is not yet a
restriction on `Adversary`.  The target is a function that reads `delivery` as
the timed schedule and proves `PartiallySynchronous` for it. -/
def ScheduleBridge (ns : NetworkSchedule) (j : NodeId) : Prop :=
  ∃ s : Schedule, ∀ m : Message,
    ns.delivery m.tag j = true → s.DeliveredWithin m (m.send + ns.maxDelay)

end LnLean.Security.ThreatModel
