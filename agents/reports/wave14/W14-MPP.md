# W14-MPP — additive MPP completion and settlement at `≥ total_msat` (G08 / REV-07)

**Lane:** `W14-MPP` (Wave 14, branch `wave-14/16`, base `a331b71`).
**Scope:** additive lower-bound MPP completion and settlement. The existing
exact-sum carrier (`mppComplete`, `MppPayment.settle`,
`MppPayment.settle_requires_sum`) is imported and preserved unchanged; the new
layer accepts a non-empty part set whose sum is at least `total_msat`, rejects
an underpaying set, and exposes the overpay separation required by R32 G08.

## 1. Owned files

- `LnLean/Proofs/Wave14/MppSettlement.lean` (created)
- `agents/reports/wave14/W14-MPP.md` (this report)

No other file was created, modified, or deleted. `LnLean.lean`,
`lakefile.lean`, `scripts/check-final.py`,
`LnLean/Proofs/PhaseC3/AxiomAudit.lean`, `LnLean/Proofs/Traceability.lean`,
`LnLean/Proofs/Obligations.lean`, `docs/`, the catalog, `vendor/`, `refs/`,
the existing payment/MPP/security modules, and other lanes' files are
untouched.

## 2. Existing carrier reused, not duplicated

The review note was correct: `mppCompleteGe` already exists, so this lane did
**not** add a second copy.

| Existing declaration | Location | Use in this lane |
|---|---|---|
| `LnLean.Payment.mppComplete` (exact sum) | `LnLean/Payment/MPP.lean:144` | retained, unchanged; shown narrower by witness |
| `LnLean.Payment.MPPProps.mppCompleteGe` (`parts ≠ [] ∧ target ≤ sum`) | `LnLean/Proofs/Payment/MPPProps.lean:686` | imported and used as the plan-level predicate |
| `LnLean.Payment.MPPProps.mppComplete_implies_completeGe` | `MPPProps.lean:690` | imported and used in `exact_completion_implies_ge_settlement` |
| `LnLean.Security.MppPayment.partsSum` / `SumOK` / `settle` | `LnLean/Security/Invariants.lean:432,436,440` | retained, unchanged |
| `LnLean.Security.MppPayment.settle_requires_sum` | `Invariants.lean:448` | retained, unchanged; used to derive the new exact-to-`≥` theorem |

The module docstring states explicitly that exact completion is **narrower than
BOLT 4, not false**: BOLT 4 permits `sum ≥ total_msat`
(`refs/bolts/04-onion-routing.md:383-385`), the exact predicate is the
conservative special case, and the old exact behaviour is retained as a
permanent witness.

## 3. Definitions and exact headline statements

Namespace:
`LnLean.Proofs.Wave14.MppSettlement` (imports
`LnLean.Proofs.Payment.MPPProps` and `LnLean.Security.Invariants`).

### Definitions

```lean
abbrev SumGe (m : MppPayment) : Prop :=
  m.parts ≠ [] ∧ m.total.val ≤ m.partsSum

def Fulfilled (m : MppPayment) : Prop :=
  m.accepted = true

def settleGe (m : MppPayment) : Option MppPayment :=
  if SumGe m then some { m with accepted := true } else none

def planToPayment (plan : MPPPlan) : MppPayment :=
  { parts := plan.parts.map (fun p => p.amount)
    total := plan.target
    accepted := false }
```

`SumGe` is deliberately the payment-level analogue of the existing
`MPPProps.mppCompleteGe`, including its non-emptiness conjunct. `settleGe`
changes only the `accepted` flag; it preserves `parts` and `total`.

### Headline theorems (11)

```lean
theorem settleGe_iff_sumGe (m : MppPayment) :
    SumGe m ↔ ∃ m', settleGe m = some m'

theorem settleGe_fulfils {m m' : MppPayment} (h : settleGe m = some m') :
    Fulfilled m' ∧ m'.parts = m.parts ∧ m'.total = m.total

theorem sumOK_imp_sumGe {m : MppPayment} (h : m.SumOK)
    (hne : m.parts ≠ []) : SumGe m

theorem exact_settle_implies_ge_settle (m m' : MppPayment)
    (h : m.settle = some m') (hne : m.parts ≠ []) :
    ∃ m'', settleGe m = some m'' ∧ Fulfilled m''

theorem planToPayment_sumGe_iff (plan : MPPPlan) :
    SumGe (planToPayment plan) ↔
      LnLean.Payment.MPPProps.mppCompleteGe plan

theorem exact_completion_implies_ge_settlement (plan : MPPPlan)
    (h : mppComplete plan) :
    LnLean.Payment.MPPProps.mppCompleteGe plan ∧
      ∃ m', settleGe (planToPayment plan) = some m' ∧ Fulfilled m'

theorem overpay_completes_ge_not_exact :
    SumGe overpayPayment ∧ ¬ overpayPayment.SumOK ∧
      overpayPayment.settle = none

theorem overpay_settleGe_fulfilled :
    settleGe overpayPayment = some overpayFulfilled ∧
      Fulfilled overpayFulfilled

theorem underpay_rejected :
    ¬ SumGe underpayPayment ∧ underpayPayment.settle = none ∧
      settleGe underpayPayment = none

theorem overpayPlan_ge_not_exact :
    LnLean.Payment.MPPProps.mppCompleteGe overpayPlan ∧
      ¬ mppComplete overpayPlan

theorem exactPlan_settlesGe :
    ∃ m', settleGe (planToPayment exactPlan) = some m' ∧ Fulfilled m'
```

The supporting declarations `planToPayment_partsSum`,
`planToPayment_overpayPlan`, `overpay_ge_completes`,
`overpay_exact_rejected`, and `exactPlan_complete` are included in the module;
the 11 audited headlines are exactly the block above.

### What each requirement maps to

| Requirement | Theorem |
|---|---|
| exact completion implies `≥` completion | `exact_completion_implies_ge_settlement` (uses existing `mppComplete_implies_completeGe`), `exact_settle_implies_ge_settle`, `sumOK_imp_sumGe` |
| overpay `[120]` vs `100` completes under `≥` but exact rejects | `overpay_completes_ge_not_exact`, `overpay_settleGe_fulfilled`, `overpayPlan_ge_not_exact` |
| underpay is rejected | `underpay_rejected` |
| a concrete `settleGe` result is fulfilled | `overpay_settleGe_fulfilled`, `exactPlan_settlesGe` |
| exact carrier unchanged | no existing declaration edited; `mppComplete`, `settle`, `settle_requires_sum` imported as-is |

## 4. Concrete non-vacuity witnesses

### Overpay (R32 G08 witness)

```lean
def overpayPayment : MppPayment :=
  { parts := [⟨120⟩], total := ⟨100⟩, accepted := false }

def overpayFulfilled : MppPayment :=
  { overpayPayment with accepted := true }
```

Kernel-checked facts:

- `overpay_ge_completes : SumGe overpayPayment` — the lower bound accepts
  `120 ≥ 100`.
- `overpay_exact_rejected` — `¬ overpayPayment.SumOK` and
  `overpayPayment.settle = none`. The retained exact path rejects the same
  value.
- `overpay_settleGe_fulfilled` — `settleGe overpayPayment = some
  overpayFulfilled` and `Fulfilled overpayFulfilled` (`accepted = true`).
  This is a concrete fulfilled result, not an existential supplied by a
  hypothesis.

### Plan-level overpay

```lean
def overpayPlan : MPPPlan :=
  { paymentHash := ⟨ByteArray.empty⟩
    paymentSecret := ⟨ByteArray.empty⟩
    target := ⟨100⟩
    parts := [{ channel := ⟨0, 0, 0⟩, amount := ⟨120⟩, cltv := 0 }] }
```

`overpayPlan_ge_not_exact` proves `mppCompleteGe overpayPlan` **and**
`¬ mppComplete overpayPlan`, exercising the existing plan predicate directly.
`planToPayment_overpayPlan` proves the projection is literally
`overpayPayment`.

### Underpay

```lean
def underpayPayment : MppPayment :=
  { parts := [⟨40⟩], total := ⟨100⟩, accepted := false }
```

`underpay_rejected` proves `¬ SumGe underpayPayment`,
`underpayPayment.settle = none`, and `settleGe underpayPayment = none`.

### Exact positive witness

```lean
def exactPlan : MPPPlan :=
  -- parts 60 + 40, target 100
```

`exactPlan_complete : mppComplete exactPlan` and `exactPlan_settlesGe` uses the
general exact-to-`≥` theorem to obtain a fulfilled `settleGe` result. This
prevents the exact-to-lower-bound headline from being a hypothesis-only
statement.

The values are saturated: no `Nat` subtraction or truncation is involved, and
every witness is a concrete closed term checked by `decide`.

## 5. Build

Command (exactly the scoped module build under the shared lock):

```sh
cd /home/ubuntu/ln-lean-waveh
export PATH=/dev/shm/btc/elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
LEAN_NUM_THREADS=1 flock -w 3600 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Proofs.Wave14.MppSettlement
```

Result: `Build completed successfully (14 jobs).` No warnings, no `sorry`,
no forbidden escape hatch. Transcript: `/tmp/opencode/w14-mpp-build.log`.

## 6. `#print axioms` output

Copied from the successful build transcript:

```text
'LnLean.Proofs.Wave14.MppSettlement.settleGe_iff_sumGe' does not depend on any axioms
'LnLean.Proofs.Wave14.MppSettlement.settleGe_fulfils' does not depend on any axioms
'LnLean.Proofs.Wave14.MppSettlement.sumOK_imp_sumGe' depends on axioms: [propext, Quot.sound]
'LnLean.Proofs.Wave14.MppSettlement.exact_settle_implies_ge_settle' depends on axioms: [propext, Quot.sound]
'LnLean.Proofs.Wave14.MppSettlement.planToPayment_sumGe_iff' depends on axioms: [propext]
'LnLean.Proofs.Wave14.MppSettlement.exact_completion_implies_ge_settlement' depends on axioms: [propext]
'LnLean.Proofs.Wave14.MppSettlement.overpay_completes_ge_not_exact' does not depend on any axioms
'LnLean.Proofs.Wave14.MppSettlement.overpay_settleGe_fulfilled' depends on axioms: [propext]
'LnLean.Proofs.Wave14.MppSettlement.underpay_rejected' does not depend on any axioms
'LnLean.Proofs.Wave14.MppSettlement.overpayPlan_ge_not_exact' does not depend on any axioms
'LnLean.Proofs.Wave14.MppSettlement.exactPlan_settlesGe' depends on axioms: [propext]
```

Every headline is within the allowed set
(`propext`, `Quot.sound`, `Classical.choice`, or none). No `Classical.choice`
is needed.

## 7. Gap closure and remaining boundary

**Closed/narrowed:** R32 G08 in `agents/reports/wave13-review/R32-synthesis.md`
§3 and `REV-07` in `docs/OPEN-ISSUES.md` — "MPP completion at
`≥ total_msat`" was recorded as a **narrower model**, not a false theorem:
`mppComplete` and `MppPayment.settle` require exact equality, while BOLT 4
permits overpay (`settle_requires_sum` is true of its carrier; do not call it
false). This lane supplies:

- `SumGe`, a payment-level lower-bound predicate matching the already-existing
  plan-level `mppCompleteGe`;
- `settleGe`, an additive settlement function that accepts overpay,
  rejects underpay, and returns a fulfilled (`accepted = true`) result;
- `planToPayment_sumGe_iff`, tying the new payment predicate exactly to the
  existing `mppCompleteGe` rather than restating it;
- `exact_completion_implies_ge_settlement` and
  `exact_settle_implies_ge_settle`, showing the retained exact path is a
  special case of the lower-bound path;
- permanent overpay and underpay witnesses with concrete `decide`-checked
  values, including the R32 `parts = [120]`, `total = 100` case.

**Remains external/narrow** (also stated in the module docstring):

- This is an economy-only settlement predicate. Onion construction, route
  selection, per-part fee arithmetic, and the 60-second `mpp_timeout`
  collection window are not modelled.
- Payment-secret derivation/encryption, preimage soundness, and cryptographic
  hash properties are not modelled; `MPPPlan` still carries only opaque fields.
- Per-HTLC identity (`channel_id`, `htlc_id`) is absent; duplicate detection in
  `MPPProps` remains whole-record equality.
- Mixed `total_msat` values across parts are not represented.
- Receiver persistence, event publication, cross-process admission, and
  eventual/live settlement are not proved. `settleGe` is an admission decision
  on a supplied value, not a liveness theorem.
- `mppComplete`/`settle` are intentionally left narrower than BOLT 4. They are
  not marked false, weakened, or removed.

## 8. Shared-file changes the integrator must make

Not applied by this lane:

1. **Root import:** regenerate `LnLean.lean` with `scripts/regen-root.sh` so it
   imports `LnLean.Proofs.Wave14.MppSettlement`. Do not hand-edit the root.
2. **Axiom audit:** add the 11 headline names (and, if the coverage gate
   requires every declaration, the witness/supporting names) to the
   `#print axioms` commands and `auditedTheorems` registry in
   `LnLean/Proofs/PhaseC3/AxiomAudit.lean`. The module already prints every
   audited headline theorem it adds, so this is registry/print-set
   reconciliation.
3. **Catalog/docs (optional, wording only):** if a catalog row is added, point
   it at `MppSettlement.exact_completion_implies_ge_settlement` and
   `MppSettlement.overpay_completes_ge_not_exact`, describing them as an
   **additive lower-bound settlement layer** over the unchanged exact carrier.
   Update `docs/OPEN-ISSUES.md` `REV-07` to say the MPP half is narrowed by
   `W14-MPP` while the route-fee rounding half remains with the route lane. Do
   not mark `mppComplete`, `MppPayment.settle`, or `settle_requires_sum` false.

## 9. Confirmation

No shared file and no other lane's file was edited. My writes were only to
`LnLean/Proofs/Wave14/MppSettlement.lean` and this report. No `git add`,
`git commit`, `git push`, branch switch, or other Git write command was run.
The existing `mppComplete`, `MppPayment.settle`, `MppPayment.settle_requires_sum`,
and `mppCompleteGe` declarations are preserved unchanged; this change is
additive.
