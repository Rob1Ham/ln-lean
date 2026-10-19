# W14-UNIFIED — unified-send fatal/retryable outcome model

## 1. Lane id and scope

Lane `W14-UNIFIED` of Wave 14, worktree `/home/ubuntu/ln-lean-waveh`, branch
`wave-14/16`, base `a331b71`.

Scope: a small **additive** model of unified-send dispatch that distinguishes
`retryable` from `fatal` outcomes and forbids falling back after a fatal (or a
successful) primary attempt.  Closes the "missing carrier" half of R32 G25 /
`REV-06` and the fatal-error policy of R28 T1 for a two-attempt slice.  It does
not claim the full canonical method order, concurrency, async completion,
persistence, or at-most-one-payment.

The existing carriers were inspected first:

* `LnLean/Payment/HTLC.lean:65-69` — `PaymentState` is
  `pending | succeeded | failed`, a **session settlement** status.  It has no
  `retryable`/`fatal` split, and mapping both failure classes to `failed` would
  erase exactly the distinction this lane needs.  It is not redefined or
  reused as the send outcome.
* `LnLean/Payment/HTLC.lean:102-137` — `PaymentSession` and `settle` are the
  session record and absorbing settlement transition; there is no attempt,
  method, or unified plan field.
* `LnLean/Proofs/Payment/KeysendProps.lean:173-253` — `Keysend` carries a
  preimage and a single `PaymentSession`; its `retry` is an unconditional
  outbound reset, still the old carrier and still unchanged.
* A repository-wide grep for `unified`/`Unified` over `LnLean/**/*.lean` finds
  no unified-send carrier.  Per the lane prompt, the model below is therefore
  **self-contained** and labelled as a model.

## 2. Owned files

* `LnLean/Proofs/Wave14/UnifiedSendFatal.lean` (new)
* `agents/reports/wave14/W14-UNIFIED.md` (this report, new)

No other file was created or edited by this lane.

## 3. Headline definitions and statements

Namespace: `LnLean.Proofs.Wave14.UnifiedSendFatal`.

```lean
inductive SendOutcome where
  | succeeded
  | retryable
  | fatal

inductive Method where
  | bolt12
  | bolt11
  | onchain

structure Attempt where
  method : Method
  outcome : SendOutcome

structure UnifiedPlan where
  primary : Attempt
  fallback : Option Attempt := none

structure Dispatch where
  attempts : List Method
  status : SendOutcome

def dispatch (plan : UnifiedPlan) : Dispatch :=
  match plan.primary.outcome with
  | .succeeded => { attempts := [plan.primary.method], status := .succeeded }
  | .fatal     => { attempts := [plan.primary.method], status := .fatal }
  | .retryable =>
      match plan.fallback with
      | none         => { attempts := [plan.primary.method], status := .retryable }
      | some fallback =>
          { attempts := [plan.primary.method, fallback.method]
            status := fallback.outcome }

def unifiedSend (plan : UnifiedPlan) : Dispatch := dispatch plan
```

Required headline theorems:

```lean
theorem fatal_does_not_fallback (primary fallback : Attempt)
    (h : primary.outcome = .fatal) :
    (dispatch { primary := primary, fallback := some fallback }).attempts =
      [primary.method]

theorem retryable_falls_back (primary fallback : Attempt)
    (h : primary.outcome = .retryable) :
    (dispatch { primary := primary, fallback := some fallback }).attempts =
      [primary.method, fallback.method]

theorem succeeded_does_not_fallback (primary fallback : Attempt)
    (h : primary.outcome = .succeeded) :
    (dispatch { primary := primary, fallback := some fallback }).attempts =
      [primary.method]
```

Supporting theorems:

```lean
theorem retryable_without_fallback_stops (primary : Attempt)
    (h : primary.outcome = .retryable) :
    (dispatch { primary := primary, fallback := none }).attempts =
        [primary.method] ∧
      (dispatch { primary := primary, fallback := none }).status = .retryable

theorem fatal_status (primary fallback : Attempt) (h : primary.outcome = .fatal) :
    (dispatch { primary := primary, fallback := some fallback }).status = .fatal

theorem succeeded_status (primary fallback : Attempt)
    (h : primary.outcome = .succeeded) :
    (dispatch { primary := primary, fallback := some fallback }).status = .succeeded

theorem retryable_fallback_status (primary fallback : Attempt)
    (h : primary.outcome = .retryable) :
    (dispatch { primary := primary, fallback := some fallback }).status =
      fallback.outcome

theorem fallback_attempted_iff_retryable (primary fallback : Attempt) :
    (dispatch { primary := primary, fallback := some fallback }).attempts.length =
        2 ↔ primary.outcome = .retryable

theorem only_retryable_advances (primary fallback : Attempt)
    (h : (dispatch { primary := primary, fallback := some fallback }).attempts ≠
      [primary.method]) :
    primary.outcome = .retryable

theorem no_attempt_after_fatal (primary fallback : Attempt)
    (h : primary.outcome = .fatal) (m : Method)
    (hm : m ∈ (dispatch { primary := primary, fallback := some fallback }).attempts) :
    m = primary.method

theorem unifiedSend_eq_dispatch (plan : UnifiedPlan) :
    unifiedSend plan = dispatch plan
```

## 4. Concrete non-vacuity witnesses

All witnesses are concrete `Attempt`/`UnifiedPlan` values using the three named
rails:

```lean
def witnessSucceededPrimary : Attempt := { method := .bolt12, outcome := .succeeded }
def witnessFatalPrimary     : Attempt := { method := .bolt12, outcome := .fatal }
def witnessRetryablePrimary : Attempt := { method := .bolt12, outcome := .retryable }
def witnessFallback         : Attempt := { method := .bolt11, outcome := .succeeded }
def witnessFatalFallback    : Attempt := { method := .bolt11, outcome := .fatal }

def witnessSucceededPlan :=
  { primary := witnessSucceededPrimary, fallback := some witnessFallback }
def witnessFatalPlan :=
  { primary := witnessFatalPrimary, fallback := some witnessFallback }
def witnessRetryablePlan :=
  { primary := witnessRetryablePrimary, fallback := some witnessFallback }
def witnessRetryableFatalFallbackPlan :=
  { primary := witnessRetryablePrimary, fallback := some witnessFatalFallback }
```

The theorems that use them:

* `witness_succeeded_branch`:
  `(dispatch witnessSucceededPlan).attempts = [.bolt12] ∧
   status = .succeeded ∧ Method.bolt11 ∉ attempts`.
* `witness_fatal_branch`:
  `(dispatch witnessFatalPlan).attempts = [.bolt12] ∧
   status = .fatal ∧ Method.bolt11 ∉ attempts`.
* `witness_retryable_branch`:
  `(dispatch witnessRetryablePlan).attempts = [.bolt12, .bolt11] ∧
   status = .succeeded`.
* `witness_retryable_fatal_fallback_branch`:
  `attempts = [.bolt12, .bolt11] ∧ status = .fatal`.
* `witness_branch_lengths`:
  succeeded trace length `1`, fatal trace length `1`, retryable trace length
  `2`.

These are executable closed values, not universally quantified hypotheses, so
the three branches are genuinely inhabited and separated.  The fatal witness in
particular has a BOLT 11 fallback *available* yet its trace contains only
BOLT 12.

## 5. Build command and result

```sh
cd /home/ubuntu/ln-lean-waveh
export PATH=/dev/shm/btc/elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
LEAN_NUM_THREADS=1 flock -w 3600 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Proofs.Wave14.UnifiedSendFatal
```

Result: `Build completed successfully (8 jobs).`

No `sorry`, `axiom`, `admit`, `native_decide`, `unsafe`, or
`@[implemented_by]` occurs in the module (grep-checked).

## 6. `#print axioms` output

```text
'LnLean.Proofs.Wave14.UnifiedSendFatal.fatal_does_not_fallback' depends on axioms: [propext]
'LnLean.Proofs.Wave14.UnifiedSendFatal.retryable_falls_back' depends on axioms: [propext]
'LnLean.Proofs.Wave14.UnifiedSendFatal.succeeded_does_not_fallback' depends on axioms: [propext]
'LnLean.Proofs.Wave14.UnifiedSendFatal.retryable_without_fallback_stops' depends on axioms: [propext]
'LnLean.Proofs.Wave14.UnifiedSendFatal.fatal_status' depends on axioms: [propext]
'LnLean.Proofs.Wave14.UnifiedSendFatal.succeeded_status' depends on axioms: [propext]
'LnLean.Proofs.Wave14.UnifiedSendFatal.retryable_fallback_status' depends on axioms: [propext]
'LnLean.Proofs.Wave14.UnifiedSendFatal.fallback_attempted_iff_retryable' depends on axioms: [propext]
'LnLean.Proofs.Wave14.UnifiedSendFatal.only_retryable_advances' depends on axioms: [propext]
'LnLean.Proofs.Wave14.UnifiedSendFatal.no_attempt_after_fatal' depends on axioms: [propext]
'LnLean.Proofs.Wave14.UnifiedSendFatal.unifiedSend_eq_dispatch' does not depend on any axioms
'LnLean.Proofs.Wave14.UnifiedSendFatal.witness_succeeded_branch' depends on axioms: [propext]
'LnLean.Proofs.Wave14.UnifiedSendFatal.witness_fatal_branch' depends on axioms: [propext]
'LnLean.Proofs.Wave14.UnifiedSendFatal.witness_retryable_branch' depends on axioms: [propext]
'LnLean.Proofs.Wave14.UnifiedSendFatal.witness_retryable_fatal_fallback_branch' depends on axioms: [propext]
'LnLean.Proofs.Wave14.UnifiedSendFatal.witness_branch_lengths' depends on axioms: [propext]
```

All audited names use only `propext`; `Classical.choice` and `Quot.sound` do
not appear.

## 7. Review gap status

* **G25 / `REV-06` "unified send fatal-error class — missing carrier"**:
  *narrowed*.  A carrier now exists on which "fatal does not fall back",
  "retryable does fall back", and "success does not fall back" are proved over
  a concrete two-attempt plan.
* **R28 T1 fatal-policy half**: *narrowed* for the two-attempt slice.  The
  model does not implement the canonical `[bolt12, bolt11, onchain]` order,
  does not prove at-most-one-payment, and does not state
  `unified_send_no_double_pay` (the R28 full target remains open).
* **Still external / narrow**:
  * `SendOutcome` is an input; the classification of real LDK errors
    (`DuplicatePayment`, `PersistenceFailed`, `NotRunning`) as `fatal` is a
    premise taken from the pinned R28 reading of
    `ldk-node/src/payment/unified.rs:329-349`, not derived in Lean.
  * No asynchronous completion, timeout, concurrency, or method-internal
    atomicity.
  * No payment store, persistence, fsync/record ordering, crash behavior, or
    cross-process duplicate prevention.
  * No BOLT 12/BIP 21/BIP 353 parsing, amount preconditions, or wire model.
  * No full three-method plan/trace; a third method would need a list-based
    generalisation and its own induction.

## 8. Shared-file changes for the integrator (not applied)

The module builds standalone but is not yet reachable from the root.  The
integrator must, if the lane is accepted:

1. Add `import LnLean.Proofs.Wave14.UnifiedSendFatal` to the generated root
   (`LnLean.lean` / the Wave-14 aggregator) via `scripts/regen-root.sh`; this
   lane did not edit the root by hand.
2. Optionally add the 16 names audited above to
   `LnLean/Proofs/PhaseC3/AxiomAudit.lean` and to the catalog/traceability
   rows as a new `LN-PAY-UNIFIED-*` entry.  No catalog or docs file was
   touched here.
3. Any `docs/OPEN-ISSUES.md` wording change for G25 is the integrator's; this
   lane did not edit `docs/`.

## 9. Confirmation

No shared file, existing Lean module, script, test, docs file, catalog entry,
vendor file, or other lane's report was edited.  No Git write command was run.
The only writes were the two owned paths listed in §2.
