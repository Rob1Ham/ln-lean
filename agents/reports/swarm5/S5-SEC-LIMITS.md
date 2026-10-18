# S5-SEC-LIMITS — computational-security limits and interface

**Lane:** `S5-SEC-LIMITS` (`CR-01`, `SEC-01`).
**Verdict:** complete for the assigned scope. The lane produced a precise
limits document and a sorry-free Lean interface that states the assumed
advantage bounds and the exact accounting theorem a game-based reduction would
need. **No reduction is claimed or mechanised.** `CR-01` and `SEC-01` remain
open.

- Repository: `/home/ubuntu/ln-lean-repair`
- Branch: `repair/integrated`
- Base commit: `79a92ce` (code `74d6475`)
- Lane files: `docs/CRYPTO-LIMITS.md` (new),
  `LnLean/Proofs/Security/SecurityGameTargets.lean` (new), this report (new).
- No existing model/proof file, `LnLean.lean`, catalog, traceability, audit, or
  shared doc was edited. No Git write was performed.

## Files changed

| File | Change |
|---|---|
| `docs/CRYPTO-LIMITS.md` | New limits document: C1/C3/C8, algebraic-vs-computational gap, reduction blueprint, assumption ledger, release wording, recommended `OPEN-ISSUES` text |
| `LnLean/Proofs/Security/SecurityGameTargets.lean` | New 509-line Lean module: `Game`, `EventReduction`, `Advantage`, `AdvantageReduction`, `CompositeAdvantage`, `CostModel`, `AssumedBound`, algebraic C1/C3/C8 facts, gap theorems |
| `agents/reports/swarm5/S5-SEC-LIMITS.md` | This report |

No file outside the lane's owned set was modified.

## Context note

The requested read path `LnLean/Proofs/Security/SecurityGame.lean` does not
exist at this base. The security-game module is
`LnLean/Proofs/PhaseC3/SecurityGame.lean`; this lane read that file, together
with `LnLean/Proofs/Security/ThreatModelProps.lean` and
`LnLean/Proofs/Security/ReorgTargets.lean`. The new limits module lives under
`LnLean/Proofs/Security/` but deliberately does not import PhaseC3, so it adds
no dependency on the finite phase-C3 game. `docs/OPEN-ISSUES.md` was read and
left unchanged; the recommended `CR-01`/`SEC-01` wording is in
`docs/CRYPTO-LIMITS.md` §12.

## Deliverable

The document covers, with exact references to the Lean forms:

1. **C1 (SHA-256 collision/preimage).** The Lean field is exact injectivity on
   32-byte inputs, not the asymptotic collision game and not injectivity on
   arbitrary byte strings. Conventional `q²/2^λ` and `q/2^λ` bounds are
   recorded. The `L1-05` gap (32-byte payment preimages vs 71-byte witness
   scripts) is stated explicitly.
2. **C3 (ECDSA EUF-CMA/key binding).** The Lean field `EufCma` is message
   binding, not the EUF-CMA game. A reject-all verifier satisfies it, so
   `SigningCompleteness` and `KeyBinding` are separate obligations. No
   standard-model ECDSA reduction is claimed; generic-group bounds are
   described as heuristic shapes.
3. **C8 (HMAC PRF/binding).** `HmacPrf` is refuted for a 32-byte-output HMAC;
   C8 is `HmacBindsOn`, a finite-execution tag-binding admission. The document
   explains why exact binding is not implied by PRF security (a PRF may
   collide) and why a reduction needs a collision-abort hop.
4. **The algebraic-vs-computational gap.** Exact laws vs asymptotic bounds;
   message binding vs unforgeability; finite binding vs PRF; event security vs
   advantage. The gap is mechanised negatively: the same event-secure game
   admits advantage 0 and advantage 1.
5. **What a game-based reduction would need.** The games, adversary
   transformation, event transport, tightness, negligible loss, efficiency,
   oracle simulation, extraction, and composition are enumerated; the
   primitive-specific extraction obstructions are tabulated.

## Exact Lean interface

Namespace `LnLean.Proofs.Security.Limits`. Imports
`LnLean.Proofs.CryptoTargets`.

### Games

```lean
structure Game where
  State : Type
  init : State
  step : State → Nat → State
  bad : State → Prop

def Game.run (g : Game) : Nat → g.State
def Game.Wins (g : Game) (n : Nat) : Prop
def Game.Secure (g : Game) : Prop
```

### Event-level reduction (proved)

```lean
structure EventReduction (P C : Game) where
  map : P.State → C.State
  map_init : map P.init = C.init
  map_step : ∀ (s : P.State) (n : Nat), map (P.step s n) = C.step (map s) n
  win_transport : ∀ s : P.State, P.bad s → C.bad (map s)

theorem EventReduction.map_run (R : EventReduction P C) :
    ∀ n : Nat, R.map (P.run n) = C.run n

theorem EventReduction.secure (R : EventReduction P C) (hC : C.Secure) :
    P.Secure

def identityReduction (g : Game) : EventReduction g g
```

`EventReduction.secure` is a deterministic simulation result. It is not a
cryptographic reduction and carries no efficiency or probability claim.

### Advantage and the missing reduction inequality

```lean
structure Advantage (g : Game) where
  value : Nat → Rat
  nonneg : ∀ n : Nat, 0 ≤ value n
  le_one : ∀ n : Nat, value n ≤ 1

structure ExactAdvantage (g : Game) extends Advantage g where
  zero_of_secure : g.Secure → ∀ n : Nat, value n = 0

structure AdvantageReduction (P C : Game) where
  event : EventReduction P C
  protocol : Advantage P
  primitive : Advantage C
  loss : Nat → Rat
  loss_nonneg : ∀ n : Nat, 0 ≤ loss n
  tight : ∀ n : Nat, protocol.value n ≤ primitive.value n + loss n

theorem AdvantageReduction.bound (R : AdvantageReduction P C) {ε : Nat → Rat}
    (h : ∀ n : Nat, R.primitive.value n ≤ ε n) :
    ∀ n : Nat, R.protocol.value n ≤ ε n + R.loss n

theorem AdvantageReduction.bound_of_ideal (R : AdvantageReduction P C)
    {δ : Nat → Rat}
    (hzero : ∀ n : Nat, R.primitive.value n = 0)
    (hδ : ∀ n : Nat, R.loss n ≤ δ n) :
    ∀ n : Nat, R.protocol.value n ≤ δ n

structure CompositeAdvantage where
  protocol : Rat
  c1 : Rat
  c3 : Rat
  c8 : Rat
  loss : Rat
  loss_nonneg : 0 ≤ loss
  tight : protocol ≤ c1 + c3 + c8 + loss

theorem rat_add_le_add {a b c d : Rat} (hab : a ≤ b) (hcd : c ≤ d) :
    a + c ≤ b + d

theorem composite_bound (R : CompositeAdvantage) {b1 b3 b8 δ : Rat}
    (h1 : R.c1 ≤ b1) (h3 : R.c3 ≤ b3) (h8 : R.c8 ≤ b8)
    (hδ : R.loss ≤ δ) :
    R.protocol ≤ (b1 + b3 + b8) + δ
```

The `tight` field is the exact research obligation. The theorems are pure
arithmetic consequences of it; they do not assert that a reduction exists.

### Cost model and assumed bounds

```lean
structure CostModel where
  securityParameter : Nat
  hashQueries : Nat
  signatureQueries : Nat
  hmacQueries : Nat

def c1CollisionBound (c : CostModel) : Rat
  -- q_hash² / 2^λ
def c1PreimageBound (c : CostModel) : Rat
  -- q_hash / 2^λ
def c3EufCmaBound (c : CostModel) : Rat
  -- q_signature / 2^λ
def c8PrfBound (c : CostModel) : Rat
  -- q_hmac / 2^λ

inductive Primitive
  | c1Collision
  | c1Preimage
  | c3EufCma
  | c8Prf

structure AssumedBound where
  primitive : Primitive
  cost : CostModel
  advantage : Rat
  bound : Rat
  assumed : advantage ≤ bound

def c1CollisionAssumption (c : CostModel) (adv : Rat)
    (h : adv ≤ c1CollisionBound c) : AssumedBound
def c1PreimageAssumption (c : CostModel) (adv : Rat)
    (h : adv ≤ c1PreimageBound c) : AssumedBound
def c3EufCmaAssumption (c : CostModel) (adv : Rat)
    (h : adv ≤ c3EufCmaBound c) : AssumedBound
def c8PrfAssumption (c : CostModel) (adv : Rat)
    (h : adv ≤ c8PrfBound c) : AssumedBound

theorem assumedBound_holds (A : AssumedBound) : A.advantage ≤ A.bound

theorem no_assumedBound_of_violation {adv bound : Rat}
    (h : ¬ adv ≤ bound) :
    ¬ ∃ A : AssumedBound, A.advantage = adv ∧ A.bound = bound

def Negligible (eps : Nat → Rat) : Prop :=
  ∀ c : Nat, 0 < c → ∃ N : Nat, ∀ n : Nat, N ≤ n → eps n ≤ (1 : Rat) / (c : Rat)
```

### Algebraic facts actually proved

```lean
def Sha256Collision (M : PrimitiveModel) : Prop
theorem algebraic_c1_no_collision (M : PrimitiveModel)
    (h : CollisionResistant M.sha256) : ¬ Sha256Collision M

def EcdsaBindingFailure (M : PrimitiveModel) : Prop
theorem algebraic_c3_no_binding_failure (M : PrimitiveModel)
    (h : EufCma M.ecdsaVerify) : ¬ EcdsaBindingFailure M

def HmacTagCollisionOn (M : PrimitiveModel) (mu : ByteArray)
    (msgs : List ByteArray) : Prop
theorem algebraic_c8_no_tag_collision (M : PrimitiveModel)
    {mu : ByteArray} {msgs : List ByteArray}
    (h : HmacBindsOn M.hmacSha256 mu msgs) :
    ¬ HmacTagCollisionOn M mu msgs
```

These are exact algebraic consequences of the existing fields. They are not
probability bounds and do not mention real SHA-256, secp256k1, or HMAC-SHA256.

### The gap (negative results)

```lean
def unitGame : Game
theorem unitGame_secure : unitGame.Secure

def constantAdvantage {g : Game} (q : Rat) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    Advantage g

theorem event_game_does_not_determine_advantage :
    ∃ (A B : Advantage unitGame),
      (∀ n : Nat, A.value n = 0) ∧ (∀ n : Nat, B.value n = 1)

theorem secure_game_unbounded_advantage :
    unitGame.Secure ∧
      ∀ ε : Rat, ε < 1 →
        ∃ A : Advantage unitGame, ¬ A.value 0 ≤ ε

def zeroExactAdvantage : ExactAdvantage unitGame
theorem constantOne_not_exact :
    ¬ ∃ S : ExactAdvantage unitGame, ∀ n : Nat, S.value n = 1

def zeroReduction : AdvantageReduction unitGame unitGame
theorem zeroReduction_bound (n : Nat) :
    zeroReduction.protocol.value n ≤ zeroReduction.loss n
```

`event_game_does_not_determine_advantage` and
`secure_game_unbounded_advantage` are the formal statement that an
event-level "no bad state" theorem cannot be presented as a computational
advantage bound.

## Build

Command, exactly as specified:

```text
cd /home/ubuntu/ln-lean-repair
export PATH=/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Proofs.Security.SecurityGameTargets
```

Result (initial build):

```text
✔ [15/15] Built LnLean.Proofs.Security.SecurityGameTargets (2.1s)
Build completed successfully (15 jobs).
```

The module was rebuilt after a comment-only docstring edit:

```text
✔ [15/15] Built LnLean.Proofs.Security.SecurityGameTargets (843ms)
Build completed successfully (15 jobs).
```

**Build RC: 0** for both runs. No full `lake build` was run.

## Axiom audit

`#print axioms` on every theorem in the module (run in a temporary file with
`lake env lean`):

| Declaration | Axioms |
|---|---|
| `EventReduction.map_run` | none |
| `EventReduction.secure` | none |
| `rat_add_le_add` | `propext`, `Classical.choice`, `Quot.sound` |
| `AdvantageReduction.bound` | `propext`, `Classical.choice`, `Quot.sound` |
| `AdvantageReduction.bound_of_ideal` | `propext`, `Classical.choice`, `Quot.sound` |
| `composite_bound` | `propext`, `Classical.choice`, `Quot.sound` |
| `assumedBound_holds` | none |
| `no_assumedBound_of_violation` | none |
| `algebraic_c1_no_collision` | none |
| `algebraic_c3_no_binding_failure` | none |
| `algebraic_c8_no_tag_collision` | none |
| `unitGame_secure` | none |
| `event_game_does_not_determine_advantage` | `propext`, `Quot.sound` |
| `secure_game_unbounded_advantage` | `propext`, `Quot.sound` |
| `constantOne_not_exact` | `propext`, `Quot.sound` |
| `zeroReduction_bound` | `propext`, `Classical.choice`, `Quot.sound` |

Axiom set is a subset of the permitted
`{propext, Classical.choice, Quot.sound}`. No new axiom, no `sorry`, no
`admit`, no `native_decide`, no `unsafe`, no `@[implemented_by]`.

## Forbidden-construct scan

Raw grep over the new module:

```text
$ grep -nE '\b(sorry|axiom|admit|native_decide|unsafe)\b|@\[implemented_by\]' \
    LnLean/Proofs/Security/SecurityGameTargets.lean
(no output)
```

Code-only scan using `scripts/check.py`'s comment/string stripper:

```text
lines: none
```

`python3 scripts/check.py` (whole tree, run after the file was added) reported:

```text
files=188 obligations=82 sorry_in_proofs=0
check: OK
```

The global file/obligation counts include concurrent lanes and may change
again before integration; the lane-specific result is the clean scan above. No
`collect-obligations.py` was run.

## Scope caveats

1. **No probability space.** `Advantage.value : Nat → Rat` is an accounting
   sequence with non-negativity and `≤ 1`; it is not a measure, and there is no
   link to `Game.Wins`.
2. **No complexity model.** `CostModel` counts queries only. It cannot express
   PPT, runtime, memory, rewinding, oracle programming, or reduction
   efficiency.
3. **No reduction.** `EventReduction` is a deterministic simulation. The
   `AdvantageReduction.tight` field is assumed, not proved. The conditional
   theorems are arithmetic. The interface is trivially satisfiable with a large
   `loss`; it is an accounting device, not evidence that a reduction exists.
4. **C1 is exact and domain-limited.** `CollisionResistant` is injectivity on
   32-byte inputs, stronger than computational collision resistance and
   weaker than arbitrary-message resistance. It does not cover 71-byte witness
   scripts (`L1-05`).
5. **C3 is message binding, not EUF-CMA.** A reject-all verifier satisfies
   `EufCma`. `SigningCompleteness` and `KeyBinding` remain separate hypotheses
   (`WaveE.E06`, `PR-01`). No forgery game or signing oracle is modelled.
6. **C8 is finite binding, not a PRF.** `HmacBindsOn` is satisfied by pairwise
   distinct tags and requires exact collision-freedom on the finite list;
   PRF security does not imply that. The PRF/MAC reductions and the
   collision-abort hop are not mechanised.
7. **No sighash/serialisation bridge.** C3 operates on abstract tagged byte
   strings, not the BOLT 3 sighash (`PR-02`).
8. **No L1/network integration.** The protocol game is not connected to L1
   confirmation, reorg, timelock, or the Noise transport.
9. **`Negligible` is a definition only.** Closure under addition/composition
   and game hopping are not proved.
10. **`zeroReduction` is a non-vacuity witness, not evidence.** It shows the
    interface is inhabited; its advantages and loss are all zero.

## Integration steps for the parent

1. Add `import LnLean.Proofs.Security.SecurityGameTargets` to `LnLean.lean`
   (root import is forbidden for this lane).
2. Update the catalog/traceability only if a row is assigned to a specific
   theorem. This lane did not edit `Obligations.lean`, `Traceability.lean`,
   `AxiomAudit.lean`, or `docs/OPEN-ISSUES.md`.
3. Replace the `CR-01` and `SEC-01` rows with the wording in
   `docs/CRYPTO-LIMITS.md` §12, then record the integration commit and theorem
   names.
4. Refresh generated counts (`check-final.py`, generated indexes) after the
   root import. The module adds one Lean file; the base gate expected 182
   files, and concurrent wave-5 lanes may change that number, so update the
   expected count after all wave-5 files land.
5. Re-run the full gate: full `lake build`, strict catalog audit,
   `check.sh`, `check-final.py`, `check-conformance.py`, `verify-anchors.py`,
   `verify-vendor.sh`, and the exact `sorry` scan. This lane did not run those
   shared gates.
6. Consider adding the module to `docs/THEOREM-INDEX.md` with the headline
   declarations:
   `EventReduction.secure`, `AdvantageReduction.bound`,
   `AdvantageReduction.bound_of_ideal`, `composite_bound`,
   `algebraic_c1_no_collision`, `algebraic_c3_no_binding_failure`,
   `algebraic_c8_no_tag_collision`,
   `secure_game_unbounded_advantage`.

## Human and research decisions

These are not agent decisions; they are recorded in `docs/CRYPTO-LIMITS.md`
§13 and repeated here for the parent.

1. **Probability/complexity foundation:** minimal finite-probability monad over
   `Rat`, mathlib `PMF`/measure theory, or paper-only computational proof.
2. **Security parameter and bound shapes:** fix `λ`, query model, constants,
   `q²` vs `q(q-1)`, and whether quantum adversaries are in scope.
3. **C1:** keep exact 32-byte injectivity (simple, stronger than standard) or
   move to an asymptotic collision game (faithful, much more work).
4. **C3:** add `Sign`/`KeyGen` + `SigningCompleteness`, a `KeyBinding` game, and
   a real EUF-CMA game; otherwise "C3" is message binding only.
5. **C8:** choose PRF, MAC/EUF-CMA, or finite tag binding; if the protocol
   consumes exact binding, add a collision-abort hop with a birthday term.
6. **Protocol game:** fix corruption, schedule, L1, winning condition, and
   game-based vs UC-style claim.
7. **Sighash/serialisation:** decide whether to mechanise BOLT 3 sighash and
   exact byte domains before claiming a C3 reduction (`PR-02`).
8. **Key binding:** decide registration, proof of possession, or authenticated
   handshake for `funding_pubkey` (`PR-01`).
9. **Effort/publication:** full mechanised reduction (large research project)
   vs publish the model with this limits document and a paper proof sketch.
10. **Release wording:** adopt §11 of `docs/CRYPTO-LIMITS.md`; do not claim
    computational security or a proved reduction.

## Blockers

None for this lane. The build is green. The only blockers are the research
items above: no probability semantics, no reduction, no C3 signing/key-binding
model, no C8 PRF model, and no BOLT 3 sighash bridge. These are faithfully
recorded as open, not hidden behind a rewording.
