import LnLean.Payment.HTLC

/-!
# LnLean.Proofs.Wave14.UnifiedSendFatal

Wave-14 lane `W14-UNIFIED` (review gap G25 / `REV-06`; R32 §3 G25 and
§6.3 `W14-OFFER`).

## The defect

A unified send tries several payment methods (BOLT 12, BOLT 11, on-chain) in a
fixed order.  LDK Node does **not** fall through to the next method on every
failure: a duplicate payment or a failed payment-store write aborts the whole
send, because falling back could pay the same offer/invoice twice
(`ldk-node/src/payment/unified.rs:329-349`; R28 §2.2, R32 D7).  The Lean
surface has no carrier for this distinction: `LnLean.Payment.PaymentState`
(`LnLean/Payment/HTLC.lean:65-69`) is a *session settlement* status
(`pending | succeeded | failed`), it has no `retryable` constructor, and no
unified-send dispatch function exists in `LnLean/`.

## What this module adds (a model, not an existing carrier)

This file is deliberately **self-contained**.  It does not redefine
`PaymentSession`, `PaymentState`, `Keysend`, or any keysend/unified record, and
it does not import another Wave 14 lane.

* `SendOutcome` — `succeeded | retryable | fatal`.  `retryable` means "this
  method did not complete and another method may be tried"; `fatal` means "stop
  the unified send, do not try any other method".
* `Method` — the three unified-send rails `bolt12 | bolt11 | onchain`.  It
  names rails only; the canonical ordering policy is not proved here.
* `Attempt` — one method plus the outcome of trying it.
* `UnifiedPlan` — a primary `Attempt` and an optional fallback `Attempt`.
  This is the two-attempt slice of the LDK method list, not the full list.
* `dispatch` / `unifiedSend` — the control flow.  The fallback is attempted
  **only** when the primary outcome is `retryable`.  `succeeded` and `fatal`
  both stop after the primary.
* `Dispatch` — the observed trace (`attempts : List Method`) and the terminal
  `status : SendOutcome`.

Headline results: `fatal_does_not_fallback`, `retryable_falls_back`,
`succeeded_does_not_fallback`, `retryable_without_fallback_stops`, and the
converse `fallback_attempted_iff_retryable`.  Concrete branch witnesses are
`witness_succeeded_branch`, `witness_fatal_branch`, and
`witness_retryable_branch`.

## Boundaries (do not overclaim)

* This is a **finite, two-attempt, single-threaded control-flow model**.  It
  says nothing about asynchronous send completion, timeouts, concurrency, or
  the order in which LDK sorts the full method list.
* `SendOutcome` is an **input** to `dispatch`.  The module does not classify
  real LDK errors into `retryable`/`fatal`; in particular it does not prove
  that `DuplicatePayment`, `PersistenceFailed`, or `NotRunning` are fatal.
  That classification is a premise of the model, taken from the pinned R28
  reading of `unified.rs`.
* It does not prove an at-most-one-payment or no-double-pay property.  A
  method's internal send may itself be non-atomic; payment-store persistence
  and the send/record window are separate carriers (`W14-PAY-STORE`).
* It does not model BOLT 12 offers, BIP 21/353 parsing, on-chain amount
  preconditions, or any wire encoding.
-/

namespace LnLean.Proofs.Wave14.UnifiedSendFatal

set_option autoImplicit false

/-! ## Outcomes, methods, and the plan -/

/-- The three outcomes of one unified-send method attempt.

`retryable` is the only outcome that permits the next method to be tried.
`succeeded` is terminal and `fatal` aborts the unified send. -/
inductive SendOutcome where
  | succeeded
  | retryable
  | fatal
  deriving Repr, DecidableEq, BEq, Inhabited

/-- The payment rails named by a unified send.  This is a name set, not the
canonical sorting proof. -/
inductive Method where
  | bolt12
  | bolt11
  | onchain
  deriving Repr, DecidableEq, BEq, Inhabited

/-- One method and the outcome of trying it. -/
structure Attempt where
  method : Method
  outcome : SendOutcome
  deriving Repr, DecidableEq

/-- A unified-send plan: a primary attempt and an optional fallback.  The
optional fallback is the minimal model of "try the next method in the list". -/
structure UnifiedPlan where
  primary : Attempt
  fallback : Option Attempt := none
  deriving Repr, DecidableEq

/-- The observed result of dispatching a plan: the methods actually attempted,
in order, and the terminal status. -/
structure Dispatch where
  attempts : List Method
  status : SendOutcome
  deriving Repr, DecidableEq

/-! ## Dispatch -/

/-- Dispatch a unified-send plan.

* `succeeded` stops after the primary (`status = succeeded`).
* `fatal` stops after the primary (`status = fatal`) **without** trying the
  fallback.
* `retryable` tries the fallback when one is present; otherwise it stops after
  the primary with `status = retryable`.
* The status after a retryable primary with a fallback is the fallback's own
  outcome.  There is no third attempt in this model. -/
def dispatch (plan : UnifiedPlan) : Dispatch :=
  match plan.primary.outcome with
  | .succeeded =>
      { attempts := [plan.primary.method], status := .succeeded }
  | .fatal =>
      { attempts := [plan.primary.method], status := .fatal }
  | .retryable =>
      match plan.fallback with
      | none =>
          { attempts := [plan.primary.method], status := .retryable }
      | some fallback =>
          { attempts := [plan.primary.method, fallback.method]
            status := fallback.outcome }

/-- Alias for the unified-send entry point.  `dispatch` is the definition; this
name records the LDK-facing operation. -/
def unifiedSend (plan : UnifiedPlan) : Dispatch :=
  dispatch plan

/-! ## Behavioural theorems -/

/-- A fatal primary does not fall back: the trace contains only the primary
method, even when a fallback is supplied. -/
theorem fatal_does_not_fallback (primary fallback : Attempt)
    (h : primary.outcome = .fatal) :
    (dispatch { primary := primary, fallback := some fallback }).attempts =
      [primary.method] := by
  unfold dispatch
  simp [h]

/-- A retryable primary falls back: the trace contains the primary followed by
the fallback method. -/
theorem retryable_falls_back (primary fallback : Attempt)
    (h : primary.outcome = .retryable) :
    (dispatch { primary := primary, fallback := some fallback }).attempts =
      [primary.method, fallback.method] := by
  unfold dispatch
  simp [h]

/-- A successful primary does not fall back: success is terminal. -/
theorem succeeded_does_not_fallback (primary fallback : Attempt)
    (h : primary.outcome = .succeeded) :
    (dispatch { primary := primary, fallback := some fallback }).attempts =
      [primary.method] := by
  unfold dispatch
  simp [h]

/-- A retryable primary with no fallback stops after the primary and reports
`retryable`; it does not invent a second attempt. -/
theorem retryable_without_fallback_stops (primary : Attempt)
    (h : primary.outcome = .retryable) :
    (dispatch { primary := primary, fallback := none }).attempts =
        [primary.method] ∧
      (dispatch { primary := primary, fallback := none }).status = .retryable := by
  unfold dispatch
  simp [h]

/-- The fatal status is preserved: a fatal primary yields `status = fatal`. -/
theorem fatal_status (primary fallback : Attempt) (h : primary.outcome = .fatal) :
    (dispatch { primary := primary, fallback := some fallback }).status = .fatal := by
  unfold dispatch
  simp [h]

/-- The success status is preserved: a successful primary yields
`status = succeeded`. -/
theorem succeeded_status (primary fallback : Attempt)
    (h : primary.outcome = .succeeded) :
    (dispatch { primary := primary, fallback := some fallback }).status =
      .succeeded := by
  unfold dispatch
  simp [h]

/-- The trace after a retryable primary with a fallback ends with the
fallback's outcome: the fallback is the terminal attempt of this model. -/
theorem retryable_fallback_status (primary fallback : Attempt)
    (h : primary.outcome = .retryable) :
    (dispatch { primary := primary, fallback := some fallback }).status =
      fallback.outcome := by
  unfold dispatch
  simp [h]

/-- **Converse direction.**  With a fallback present, a two-element trace is
possible exactly when the primary was `retryable`.  Equivalently, a
`succeeded` or `fatal` primary never advances to the fallback. -/
theorem fallback_attempted_iff_retryable (primary fallback : Attempt) :
    (dispatch { primary := primary, fallback := some fallback }).attempts.length =
        2 ↔
      primary.outcome = .retryable := by
  cases h : primary.outcome <;> simp [dispatch, h]

/-- If the trace is not exactly the primary alone, the primary must have been
retryable.  This is the "no silent fallback" direction: any deviation from the
single-primary trace is explained by `retryable`. -/
theorem only_retryable_advances (primary fallback : Attempt)
    (h : (dispatch { primary := primary, fallback := some fallback }).attempts ≠
      [primary.method]) :
    primary.outcome = .retryable := by
  cases ho : primary.outcome <;> simp [dispatch, ho] at h ⊢

/-- No method other than the primary appears in the trace after a fatal
primary: the fallback method is never called. -/
theorem no_attempt_after_fatal (primary fallback : Attempt)
    (h : primary.outcome = .fatal) (m : Method)
    (hm : m ∈ (dispatch { primary := primary, fallback := some fallback }).attempts) :
    m = primary.method := by
  rw [fatal_does_not_fallback primary fallback h] at hm
  simpa using hm

/-- `unifiedSend` is definitionally `dispatch`. -/
theorem unifiedSend_eq_dispatch (plan : UnifiedPlan) :
    unifiedSend plan = dispatch plan := rfl

/-! ## Concrete branch witnesses -/

/-- Concrete primary: BOLT 12 succeeded. -/
def witnessSucceededPrimary : Attempt :=
  { method := .bolt12, outcome := .succeeded }

/-- Concrete primary: BOLT 12 fatal. -/
def witnessFatalPrimary : Attempt :=
  { method := .bolt12, outcome := .fatal }

/-- Concrete primary: BOLT 12 retryable. -/
def witnessRetryablePrimary : Attempt :=
  { method := .bolt12, outcome := .retryable }

/-- Concrete fallback: BOLT 11 succeeded. -/
def witnessFallback : Attempt :=
  { method := .bolt11, outcome := .succeeded }

/-- Concrete fallback: BOLT 11 fatal, used to show that a fallback's own fatal
outcome is terminal. -/
def witnessFatalFallback : Attempt :=
  { method := .bolt11, outcome := .fatal }

/-- A plan whose primary succeeded, with a fallback available. -/
def witnessSucceededPlan : UnifiedPlan :=
  { primary := witnessSucceededPrimary, fallback := some witnessFallback }

/-- A plan whose primary is fatal, with a fallback available. -/
def witnessFatalPlan : UnifiedPlan :=
  { primary := witnessFatalPrimary, fallback := some witnessFallback }

/-- A plan whose primary is retryable, with a fallback available. -/
def witnessRetryablePlan : UnifiedPlan :=
  { primary := witnessRetryablePrimary, fallback := some witnessFallback }

/-- A plan whose primary is retryable and whose fallback is fatal. -/
def witnessRetryableFatalFallbackPlan : UnifiedPlan :=
  { primary := witnessRetryablePrimary, fallback := some witnessFatalFallback }

/-- The succeeded witness takes the success branch: only BOLT 12 is attempted
and the status is `succeeded`; the BOLT 11 fallback is not called. -/
theorem witness_succeeded_branch :
    (dispatch witnessSucceededPlan).attempts = [.bolt12] ∧
      (dispatch witnessSucceededPlan).status = .succeeded ∧
      Method.bolt11 ∉ (dispatch witnessSucceededPlan).attempts := by
  have htrace : (dispatch witnessSucceededPlan).attempts = [Method.bolt12] := by
    simpa [witnessSucceededPlan, witnessSucceededPrimary, witnessFallback] using
      succeeded_does_not_fallback witnessSucceededPrimary witnessFallback rfl
  have hstatus : (dispatch witnessSucceededPlan).status = .succeeded := by
    simpa [witnessSucceededPlan, witnessSucceededPrimary, witnessFallback] using
      succeeded_status witnessSucceededPrimary witnessFallback rfl
  refine ⟨htrace, hstatus, ?_⟩
  rw [htrace]
  simp

/-- The fatal witness takes the abort branch: only BOLT 12 is attempted, the
status is `fatal`, and the BOLT 11 fallback is **not** called. -/
theorem witness_fatal_branch :
    (dispatch witnessFatalPlan).attempts = [.bolt12] ∧
      (dispatch witnessFatalPlan).status = .fatal ∧
      Method.bolt11 ∉ (dispatch witnessFatalPlan).attempts := by
  have htrace : (dispatch witnessFatalPlan).attempts = [Method.bolt12] := by
    simpa [witnessFatalPlan, witnessFatalPrimary, witnessFallback] using
      fatal_does_not_fallback witnessFatalPrimary witnessFallback rfl
  have hstatus : (dispatch witnessFatalPlan).status = .fatal := by
    simpa [witnessFatalPlan, witnessFatalPrimary, witnessFallback] using
      fatal_status witnessFatalPrimary witnessFallback rfl
  refine ⟨htrace, hstatus, ?_⟩
  rw [htrace]
  simp

/-- The retryable witness takes the fallback branch: BOLT 12 is followed by
BOLT 11, and the final status is the fallback's `succeeded`. -/
theorem witness_retryable_branch :
    (dispatch witnessRetryablePlan).attempts = [.bolt12, .bolt11] ∧
      (dispatch witnessRetryablePlan).status = .succeeded := by
  refine ⟨?_, ?_⟩
  · simpa [witnessRetryablePlan, witnessRetryablePrimary, witnessFallback] using
      retryable_falls_back witnessRetryablePrimary witnessFallback rfl
  · simpa [witnessRetryablePlan, witnessRetryablePrimary, witnessFallback] using
      retryable_fallback_status witnessRetryablePrimary witnessFallback rfl

/-- A retryable primary with a fatal fallback attempts both methods once and
then stops with `fatal`.  There is no third attempt in the model. -/
theorem witness_retryable_fatal_fallback_branch :
    (dispatch witnessRetryableFatalFallbackPlan).attempts = [.bolt12, .bolt11] ∧
      (dispatch witnessRetryableFatalFallbackPlan).status = .fatal := by
  refine ⟨?_, ?_⟩
  · simpa [witnessRetryableFatalFallbackPlan, witnessRetryablePrimary,
      witnessFatalFallback] using
      retryable_falls_back witnessRetryablePrimary witnessFatalFallback rfl
  · simpa [witnessRetryableFatalFallbackPlan, witnessRetryablePrimary,
      witnessFatalFallback] using
      retryable_fallback_status witnessRetryablePrimary witnessFatalFallback rfl

/-- The three branch witnesses are separated by trace length: the succeeded and
fatal traces have length 1, the retryable trace has length 2. -/
theorem witness_branch_lengths :
    (dispatch witnessSucceededPlan).attempts.length = 1 ∧
      (dispatch witnessFatalPlan).attempts.length = 1 ∧
      (dispatch witnessRetryablePlan).attempts.length = 2 := by
  simp [witnessSucceededPlan, witnessSucceededPrimary, witnessFatalPlan,
    witnessFatalPrimary, witnessRetryablePlan, witnessRetryablePrimary,
    witnessFallback, dispatch]

/-! ## Axiom audit -/

#print axioms fatal_does_not_fallback
#print axioms retryable_falls_back
#print axioms succeeded_does_not_fallback
#print axioms retryable_without_fallback_stops
#print axioms fatal_status
#print axioms succeeded_status
#print axioms retryable_fallback_status
#print axioms fallback_attempted_iff_retryable
#print axioms only_retryable_advances
#print axioms no_attempt_after_fatal
#print axioms unifiedSend_eq_dispatch
#print axioms witness_succeeded_branch
#print axioms witness_fatal_branch
#print axioms witness_retryable_branch
#print axioms witness_retryable_fatal_fallback_branch
#print axioms witness_branch_lengths

end LnLean.Proofs.Wave14.UnifiedSendFatal
