/-
# Computational-security limits: an explicit interface, not a reduction

This module is the Lean half of `docs/CRYPTO-LIMITS.md`.  It does **not**
prove a computational-security reduction and it does not add a probabilistic
or complexity-theoretic semantics to the model.  It does four things:

1. it fixes a small, explicit *game* record and an *event-level* reduction
   record, and proves the one implication that is purely logical: an
   event-level simulation transfers "no bad state" from the primitive game to
   the protocol game;
2. it fixes an *advantage* record and an *advantage-reduction* record whose
   `tight` field is exactly the accounting inequality a cryptographic
   reduction would have to prove;
3. it records the conventional advantage bounds assumed for C1 (SHA-256
   collision and preimage), C3 (ECDSA EUF-CMA), and C8 (HMAC PRF) as
   `Rat`-valued definitions plus an `AssumedBound` structure whose only
   numeric content is a hypothesis `advantage ≤ bound`;
4. it proves the *algebraic* facts that the existing exact model actually
   supports (no 32-byte SHA-256 collision under C1, no ECDSA message-binding
   failure under C3, no finite-execution HMAC tag collision under C8), and it
   proves a *negative* result showing that the event-level game alone does not
   determine an advantage: a secure game can be assigned advantage 1.

Nothing here is a reduction.  In particular there is no probability space, no
PPT/ensemble model, no negligible-advantage closure, no signing oracle, no
key-generation model, and no efficiency preservation.  The conditional theorem
`AdvantageReduction.bound` is only the arithmetic consequence of the `tight`
field; the field itself is the research obligation.

BOLT sections.  BOLT 1 §Lightning Message Format (32-byte hashes and
signatures), BOLT 2 §Funding Transaction Output and §Commitment Transactions,
BOLT 3 §Commitment Transaction Construction, BOLT 4 §Packet Structure and
§Onion Decryption.

`rust-lightning` anchors at commit `fe49009`
(`fe4900930c6bd5786ec4203274d7cf312776a5a6`):
* `lightning/src/crypto/utils.rs:75-83` — ECDSA signing over a digest;
* `lightning/src/util/message_signing.rs:83-89` — signature verification;
* `lightning/src/ln/chan_utils.rs:600-660` — commitment key derivation and
  the keys used by funding/commitment signatures;
* `lightning/src/ln/peer_channel_encryptor.rs:150-236` — AEAD and HKDF
  interface (not part of C1/C3/C8 here);
* `lightning/src/ln/onion_utils.rs` (BOLT 4 HMAC tags) — the tag width and
  finite-execution binding consumed by C8.

What is **not** modelled.  SHA-256 compression, secp256k1 group arithmetic,
ECDSA signing and nonce generation, DER encoding, BOLT 3 sighash
serialisation, Sphinx key schedules, probabilistic polynomial-time machines,
oracle access, probability spaces, and efficiency of reductions.  Consequently
no theorem below bounds the success probability of any concrete adversary.
-/

import LnLean.Proofs.CryptoTargets

set_option autoImplicit false

namespace LnLean.Proofs.Security.Limits

open LnLean
open LnLean.Crypto
open LnLean.Proofs.WaveD.D07

/-! ## 1. Finite games and event-level reductions -/

/-- A finite, deterministic game skeleton.  `step` is total; an adversary is
represented by the step function it induces, so the record deliberately has no
separate adversary parameter.  `bad` is the protocol-specific failure event. -/
structure Game where
  /-- The state space of the game. -/
  State : Type
  /-- The initial state. -/
  init : State
  /-- One step, indexed by the step number (the horizon is explicit). -/
  step : State → Nat → State
  /-- The bad event. -/
  bad : State → Prop

namespace Game

/-- Run the game for `n` steps. -/
def run (g : Game) : Nat → g.State
  | 0 => g.init
  | n + 1 => g.step (run g n) n

/-- The bad event holds at horizon `n`. -/
def Wins (g : Game) (n : Nat) : Prop := g.bad (run g n)

/-- No horizon reaches a bad state.  This is the event-level notion of
security used by the rest of the tree; it is not a probability statement. -/
def Secure (g : Game) : Prop := ∀ n : Nat, ¬ g.bad (run g n)

end Game

/-- An **event-level reduction**.  `map` carries a protocol state to a
primitive-game state; `map_init` and `map_step` say that it commutes with the
transition functions; `win_transport` says that a protocol bad state maps to a
primitive bad state.  This is a deterministic simulation, not a cryptographic
reduction: it has no efficiency field, no adversary transformation, and no
probability accounting. -/
structure EventReduction (P C : Game) where
  /-- State map from the protocol game to the primitive game. -/
  map : P.State → C.State
  /-- The initial states correspond. -/
  map_init : map P.init = C.init
  /-- The state map commutes with one step. -/
  map_step : ∀ (s : P.State) (n : Nat), map (P.step s n) = C.step (map s) n
  /-- A protocol bad state maps to a primitive bad state. -/
  win_transport : ∀ s : P.State, P.bad s → C.bad (map s)

namespace EventReduction

variable {P C : Game}

/-- The state map commutes with a whole run. -/
theorem map_run (R : EventReduction P C) : ∀ n : Nat, R.map (P.run n) = C.run n
  | 0 => R.map_init
  | n + 1 => by
      show R.map (P.step (P.run n) n) = C.step (C.run n) n
      rw [R.map_step, map_run R n]

/-- **Event-level security transfer.**  If the primitive game has no bad
horizon, then neither does the protocol game.  This is the only reduction
implication that is proved in this module. -/
theorem secure (R : EventReduction P C) (hC : C.Secure) : P.Secure := by
  intro n hbad
  apply hC n
  rw [← R.map_run n]
  exact R.win_transport _ hbad

end EventReduction

/-- The identity event reduction.  It is used for non-vacuity witnesses. -/
def identityReduction (g : Game) : EventReduction g g where
  map := id
  map_init := rfl
  map_step := fun _ _ => rfl
  win_transport := fun _ h => h

/-! ## 2. Advantages and the missing accounting inequality -/

/-- An advantage sequence for a fixed game, indexed by a common cost index
`n` (typically the security parameter; the game horizon and query budgets are
parameters of the surrounding statement).  The record carries only the two
structural facts every probability has: non-negativity and an upper bound of
one.  It deliberately does **not** contain a definitional link to `Game.Wins`;
that link is exactly what the model cannot currently express. -/
structure Advantage (g : Game) where
  /-- Success probability (or advantage) as a rational number. -/
  value : Nat → Rat
  /-- Probabilities are non-negative. -/
  nonneg : ∀ n : Nat, 0 ≤ value n
  /-- Probabilities are at most one. -/
  le_one : ∀ n : Nat, value n ≤ 1

/-- An advantage that is additionally required to vanish on every event-secure
game.  This is the strongest link the exact algebraic model can state; it is
still not a probability semantics, and it is stronger than the computational
requirement (which is *negligible*, not zero). -/
structure ExactAdvantage (g : Game) extends Advantage g where
  /-- Event security forces zero advantage. -/
  zero_of_secure : g.Secure → ∀ n : Nat, value n = 0

/-- **The advantage-level reduction interface.**  `event` is a deterministic
simulation; `protocol` and `primitive` are the two advantage sequences; `loss`
is the reduction loss.  The field `tight` is the accounting inequality that a
cryptographic reduction would prove.  It is a hypothesis, not a theorem of this
module. -/
structure AdvantageReduction (P C : Game) where
  /-- The underlying event-level simulation. -/
  event : EventReduction P C
  /-- Advantage against the protocol game. -/
  protocol : Advantage P
  /-- Advantage against the primitive game. -/
  primitive : Advantage C
  /-- Reduction loss, per horizon. -/
  loss : Nat → Rat
  /-- The loss is non-negative. -/
  loss_nonneg : ∀ n : Nat, 0 ≤ loss n
  /-- **The missing cryptographic step.**  A real reduction proves this
  inequality; here it is a field of the interface. -/
  tight : ∀ n : Nat, protocol.value n ≤ primitive.value n + loss n

namespace AdvantageReduction

variable {P C : Game}

/-- **Conditional advantage bound.**  If the primitive advantage is bounded by
`ε`, then the protocol advantage is bounded by `ε + loss`.  This is pure
arithmetic from `tight`; it is the theorem that would follow *if* a reduction
existed. -/
theorem bound (R : AdvantageReduction P C) {ε : Nat → Rat}
    (h : ∀ n : Nat, R.primitive.value n ≤ ε n) :
    ∀ n : Nat, R.protocol.value n ≤ ε n + R.loss n := by
  intro n
  exact Rat.le_trans (R.tight n) ((Rat.add_le_add_right).mpr (h n))

/-- **Conditional bound with an ideal primitive.**  If the primitive advantage
is zero and the reduction loss is at most `δ`, the protocol advantage is at
most `δ`.  This is the shape a game-hopping proof would have to instantiate;
the zero-advantage hypothesis is the idealisation, not a proved fact about
SHA-256, ECDSA, or HMAC. -/
theorem bound_of_ideal (R : AdvantageReduction P C) {δ : Nat → Rat}
    (hzero : ∀ n : Nat, R.primitive.value n = 0)
    (hδ : ∀ n : Nat, R.loss n ≤ δ n) :
    ∀ n : Nat, R.protocol.value n ≤ δ n := by
  intro n
  have h := R.tight n
  rw [hzero n, Rat.zero_add] at h
  exact Rat.le_trans h (hδ n)

end AdvantageReduction

/-- Addition is monotone for rationals.  Kept local so that the composite bound
below does not depend on a mathlib order library. -/
theorem rat_add_le_add {a b c d : Rat} (hab : a ≤ b) (hcd : c ≤ d) :
    a + c ≤ b + d :=
  Rat.le_trans ((Rat.add_le_add_right).mpr hab) ((Rat.add_le_add_left).mpr hcd)

/-- An advantage accounting for a protocol that consumes C1, C3, and C8 at
once.  `tight` is again the missing reduction inequality. -/
structure CompositeAdvantage where
  /-- Protocol advantage. -/
  protocol : Rat
  /-- Advantage against the C1 (SHA-256) game. -/
  c1 : Rat
  /-- Advantage against the C3 (ECDSA) game. -/
  c3 : Rat
  /-- Advantage against the C8 (HMAC) game. -/
  c8 : Rat
  /-- Reduction loss. -/
  loss : Rat
  /-- The loss is non-negative. -/
  loss_nonneg : 0 ≤ loss
  /-- The missing three-primitive accounting inequality. -/
  tight : protocol ≤ c1 + c3 + c8 + loss

/-- **Composite conditional bound.**  If each primitive advantage is bounded
and the loss is bounded, the protocol advantage is bounded by the sum.  This is
an algebraic union-bound shape, not a proof that the three games are
independent or that the loss is negligible. -/
theorem composite_bound (R : CompositeAdvantage) {b1 b3 b8 δ : Rat}
    (h1 : R.c1 ≤ b1) (h3 : R.c3 ≤ b3) (h8 : R.c8 ≤ b8)
    (hδ : R.loss ≤ δ) :
    R.protocol ≤ (b1 + b3 + b8) + δ := by
  have h13 : R.c1 + R.c3 ≤ b1 + b3 := rat_add_le_add h1 h3
  have h138 : (R.c1 + R.c3) + R.c8 ≤ (b1 + b3) + b8 :=
    rat_add_le_add h13 h8
  exact Rat.le_trans R.tight (rat_add_le_add h138 hδ)

/-! ## 3. Conventional assumed bounds for C1, C3, and C8 -/

/-- The cost parameters at which a bound is stated.  `securityParameter` is
the usual `λ` (for SHA-256 and HMAC, the output length in bits); the query
counts are the adversary's budgets.  These are *parameters of the statement*,
not values derived from the implementation. -/
structure CostModel where
  /-- Security parameter, in bits. -/
  securityParameter : Nat
  /-- Number of hash queries. -/
  hashQueries : Nat
  /-- Number of signature queries. -/
  signatureQueries : Nat
  /-- Number of HMAC queries. -/
  hmacQueries : Nat

/-- Conventional birthday bound for SHA-256 collisions: `q² / 2^λ`.  This is
a heuristic upper bound, not a theorem about the concrete compression
function. -/
def c1CollisionBound (c : CostModel) : Rat :=
  (c.hashQueries : Rat) * (c.hashQueries : Rat) /
    (2 : Rat) ^ c.securityParameter

/-- Conventional preimage bound for SHA-256: `q / 2^λ`. -/
def c1PreimageBound (c : CostModel) : Rat :=
  (c.hashQueries : Rat) / (2 : Rat) ^ c.securityParameter

/-- Conventional EUF-CMA bound for ECDSA at a `λ`-bit security level:
`q_s / 2^λ`.  The generic-group proofs of ECDSA give a comparable shape; the
exact constant and the treatment of nonce bias are outside this model. -/
def c3EufCmaBound (c : CostModel) : Rat :=
  (c.signatureQueries : Rat) / (2 : Rat) ^ c.securityParameter

/-- Conventional PRF bound for HMAC at a `λ`-bit security level:
`q / 2^λ`.  The concrete HMAC proof is a PRF bound under assumptions on the
compression function; this model has no compression function. -/
def c8PrfBound (c : CostModel) : Rat :=
  (c.hmacQueries : Rat) / (2 : Rat) ^ c.securityParameter

/-- The primitive whose advantage is being bounded. -/
inductive Primitive where
  /-- C1, collision resistance on 32-byte preimages. -/
  | c1Collision
  /-- C1, preimage resistance on 32-byte preimages. -/
  | c1Preimage
  /-- C3, ECDSA existential unforgeability. -/
  | c3EufCma
  /-- C8, HMAC pseudorandomness. -/
  | c8Prf
deriving Repr, DecidableEq, BEq

/-- **An assumed bound.**  The only numeric content is `assumed : advantage ≤
bound`; the record cannot be inhabited when the inequality fails.  It is the
Lean counterpart of a line in an assumptions table, not a proof of the bound. -/
structure AssumedBound where
  /-- Which primitive the bound is for. -/
  primitive : Primitive
  /-- The cost model at which the bound is stated. -/
  cost : CostModel
  /-- The adversary's advantage. -/
  advantage : Rat
  /-- The assumed upper bound. -/
  bound : Rat
  /-- The assumed inequality. -/
  assumed : advantage ≤ bound

/-- C1 collision-resistance assumption at a cost model. -/
def c1CollisionAssumption (c : CostModel) (adv : Rat)
    (h : adv ≤ c1CollisionBound c) : AssumedBound where
  primitive := .c1Collision
  cost := c
  advantage := adv
  bound := c1CollisionBound c
  assumed := h

/-- C1 preimage-resistance assumption at a cost model. -/
def c1PreimageAssumption (c : CostModel) (adv : Rat)
    (h : adv ≤ c1PreimageBound c) : AssumedBound where
  primitive := .c1Preimage
  cost := c
  advantage := adv
  bound := c1PreimageBound c
  assumed := h

/-- C3 EUF-CMA assumption at a cost model. -/
def c3EufCmaAssumption (c : CostModel) (adv : Rat)
    (h : adv ≤ c3EufCmaBound c) : AssumedBound where
  primitive := .c3EufCma
  cost := c
  advantage := adv
  bound := c3EufCmaBound c
  assumed := h

/-- C8 HMAC PRF assumption at a cost model. -/
def c8PrfAssumption (c : CostModel) (adv : Rat)
    (h : adv ≤ c8PrfBound c) : AssumedBound where
  primitive := .c8Prf
  cost := c
  advantage := adv
  bound := c8PrfBound c
  assumed := h

/-- An assumed bound is exactly its inequality. -/
theorem assumedBound_holds (A : AssumedBound) : A.advantage ≤ A.bound :=
  A.assumed

/-- **No bound without the inequality.**  The `AssumedBound` interface cannot
be inhabited by a pair that violates its bound.  This is a sanity check on the
interface, not a cryptographic result. -/
theorem no_assumedBound_of_violation {adv bound : Rat} (h : ¬ adv ≤ bound) :
    ¬ ∃ A : AssumedBound, A.advantage = adv ∧ A.bound = bound := by
  rintro ⟨A, rfl, rfl⟩
  exact h A.assumed

/-- Negligibility, stated with an explicit rational denominator: for every
positive `c` there is a horizon after which the advantage is at most `1/c`.
This is a definition only; closure under addition and composition is **not**
proved here. -/
def Negligible (eps : Nat → Rat) : Prop :=
  ∀ c : Nat, 0 < c → ∃ N : Nat, ∀ n : Nat, N ≤ n → eps n ≤ (1 : Rat) / (c : Rat)

/-! ## 4. What the exact algebraic model actually proves -/

/-- A concrete SHA-256 collision on two distinct 32-byte inputs. -/
def Sha256Collision (M : PrimitiveModel) : Prop :=
  ∃ x y : ByteArray,
    x.size = 32 ∧ y.size = 32 ∧ x ≠ y ∧ M.sha256 x = M.sha256 y

/-- **C1 algebraic content.**  Under the model's collision-resistance field,
no 32-byte collision exists.  This is an exact algebraic statement; it says
nothing about the cost of finding a collision in the real SHA-256. -/
theorem algebraic_c1_no_collision (M : PrimitiveModel)
    (h : CollisionResistant M.sha256) : ¬ Sha256Collision M := by
  rintro ⟨x, y, hx, hy, hne, heq⟩
  exact hne (h x y hx hy heq)

/-- A failure of ECDSA message binding: one signature verifies for two distinct
messages under the same key. -/
def EcdsaBindingFailure (M : PrimitiveModel) : Prop :=
  ∃ (pk : PubKey) (m₁ m₂ : ByteArray) (sig : EcdsaSig),
    m₁ ≠ m₂ ∧ M.ecdsaVerify pk m₁ sig = true ∧
      M.ecdsaVerify pk m₂ sig = true

/-- **C3 algebraic content.**  Under `EufCma`, no message-binding failure
exists.  This is the exact message-binding consequence consumed by the
protocol proofs; it is not a statement about forgery probability or key
binding. -/
theorem algebraic_c3_no_binding_failure (M : PrimitiveModel)
    (h : EufCma M.ecdsaVerify) : ¬ EcdsaBindingFailure M := by
  rintro ⟨pk, m₁, m₂, sig, hne, h1, h2⟩
  exact hne (h pk m₁ m₂ sig h1 h2)

/-- A collision of HMAC tags on the finite message list of one execution. -/
def HmacTagCollisionOn (M : PrimitiveModel) (mu : ByteArray)
    (msgs : List ByteArray) : Prop :=
  ∃ m₁ ∈ msgs, ∃ m₂ ∈ msgs, m₁ ≠ m₂ ∧ M.hmacSha256 mu m₁ = M.hmacSha256 mu m₂

/-- **C8 algebraic content.**  Under the finite-execution admission, no tag
collision exists on that execution's message list.  This is the exact
finite binding contract, not global HMAC injectivity and not a PRF bound. -/
theorem algebraic_c8_no_tag_collision (M : PrimitiveModel)
    {mu : ByteArray} {msgs : List ByteArray}
    (h : HmacBindsOn M.hmacSha256 mu msgs) :
    ¬ HmacTagCollisionOn M mu msgs := by
  rintro ⟨m₁, hm₁, m₂, hm₂, hne, heq⟩
  exact hne (h m₁ hm₁ m₂ hm₂ heq)

/-! ## 5. The gap: event security does not determine an advantage -/

/-- The one-state game with no bad event. -/
def unitGame : Game where
  State := Unit
  init := ()
  step := fun s _ => s
  bad := fun _ => False

/-- The unit game is event-secure. -/
theorem unitGame_secure : unitGame.Secure := by
  intro _ h
  exact h

/-- A constant advantage sequence. -/
def constantAdvantage {g : Game} (q : Rat) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    Advantage g where
  value := fun _ => q
  nonneg := fun _ => h0
  le_one := fun _ => h1

/-- **The gap, part 1.**  The same event-secure unit game admits both the
zero advantage and the one advantage.  The event-level game record therefore
does not determine a probability. -/
theorem event_game_does_not_determine_advantage :
    ∃ (A B : Advantage unitGame),
      (∀ n : Nat, A.value n = 0) ∧ (∀ n : Nat, B.value n = 1) := by
  refine ⟨constantAdvantage (0 : Rat) (by decide) (by decide),
    constantAdvantage (1 : Rat) (by decide) (by decide), ?_, ?_⟩
  · intro _
    rfl
  · intro _
    rfl

/-- **The gap, part 2.**  A secure game can carry advantage arbitrarily close
to one.  Consequently `Game.Secure` alone yields no advantage bound, and a
reduction cannot be replaced by the event-level theorem
`EventReduction.secure`. -/
theorem secure_game_unbounded_advantage :
    unitGame.Secure ∧
      ∀ ε : Rat, ε < 1 →
        ∃ A : Advantage unitGame, ¬ A.value 0 ≤ ε := by
  refine ⟨unitGame_secure, ?_⟩
  intro ε hε
  refine ⟨constantAdvantage (1 : Rat) (by decide) (by decide), ?_⟩
  show ¬ ((1 : Rat) ≤ ε)
  exact Rat.not_le.mpr hε

/-- **The gap, part 3.**  An exact advantage functional that is linked to
event security must be zero on the secure unit game.  Adding the link is
possible, but it forces the degenerate exact-zero notion; a computational
treatment needs *negligible*, not zero. -/
def zeroExactAdvantage : ExactAdvantage unitGame where
  value := fun _ => 0
  nonneg := fun _ => by decide
  le_one := fun _ => by decide
  zero_of_secure := fun _ _ => rfl

/-- A constant-one advantage is not an exact advantage on a secure game. -/
theorem constantOne_not_exact :
    ¬ ∃ S : ExactAdvantage unitGame, ∀ n : Nat, S.value n = 1 := by
  rintro ⟨S, hS⟩
  have h0 := S.zero_of_secure unitGame_secure 0
  have h1 := hS 0
  rw [h0] at h1
  exact (by decide : (0 : Rat) ≠ 1) h1

/-! ## 6. Non-vacuity of the reduction interface -/

/-- The zero-loss, zero-advantage reduction of the unit game to itself. -/
def zeroReduction : AdvantageReduction unitGame unitGame where
  event := identityReduction unitGame
  protocol := constantAdvantage (0 : Rat) (by decide) (by decide)
  primitive := constantAdvantage (0 : Rat) (by decide) (by decide)
  loss := fun _ => 0
  loss_nonneg := fun _ => by decide
  tight := fun _ => by
    show (0 : Rat) ≤ 0 + 0
    rw [Rat.zero_add]
    exact Rat.le_refl

/-- The interface is inhabited and the conditional bound is not vacuous: the
zero reduction yields the zero-plus-loss bound. -/
theorem zeroReduction_bound :
    ∀ n : Nat, zeroReduction.protocol.value n ≤ zeroReduction.loss n := by
  intro n
  have h := zeroReduction.bound (ε := fun _ => 0) (fun _ => by
    show (0 : Rat) ≤ 0
    exact Rat.le_refl)
  simpa [Rat.zero_add] using h n

end LnLean.Proofs.Security.Limits
