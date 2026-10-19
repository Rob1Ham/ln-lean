import LnLean.Proofs.Payment.KeysendProps

/-!
# LnLean.Proofs.Wave14.KeysendRetryGuard

Wave-14 lane `W14-PAY-KEYSEND` (review gap G10 / `REV-03`).

## The defect

`LnLean.Payment.Keysend.retry` (`LnLean/Proofs/Payment/KeysendProps.lean:252-255`)
is an unconditional outbound-side reset: it rewrites the session state to
`pending` whatever the previous state was.  In particular it resets a session
that already `succeeded`.  LDK Node rejects a duplicate keysend whose stored
payment is `Pending` or `Succeeded`
(`ldk-node/src/payment/spontaneous.rs:67-73`, pinned at
`fa123fed131e27ecc420b77fa7086fcf1ddaebb8`); the old reset therefore describes
a retry that the implementation does not permit for a completed payment.

`Keysend.retry` and its theorem `retry_pending` are retained unchanged; they
are true statements about the old carrier and they are the divergence
witness.  This module is additive.

## What this module adds

* `retryIfNotSucceeded` — a guarded retry.  A `succeeded` session is returned
  unchanged (whole record, not merely the state field).  Every other state is
  reset to `pending`; for an already-`pending` session this is a no-op on the
  state, and a `failed` session becomes retryable, matching the LDK Node rule
  that `Failed` records may be overwritten by a new attempt.
* `retryIfNotSucceeded_succeeded` — the succeeded fixpoint.
* `retryIfNotSucceeded_failed` — a failed session becomes `pending`.
* `retryIfNotSucceeded_pending` — a pending session stays `pending`.
* `retryIfNotSucceeded_preimage` / `_session_paymentHash` / `_valid` — the
  guarded retry keeps the sender's preimage, payment hash and structural
  validity, so it cannot silently re-key the payment.
* `legacy_retry_resets_succeeded` — a named statement that the old
  `Keysend.retry` still maps a succeeded session to `pending`.
* Concrete witnesses: `witnessSucceeded` (a settled keysend) and
  `witnessFailed`, with `witness_retry_diverges` showing that the old retry
  yields `pending` while the guarded retry leaves the succeeded record
  identical.

## Boundaries

* This is a record-level transition theorem.  It does **not** model a payment
  store, duplicate admission, persistence, crash recovery, or cross-process
  retries (`W14-PAY-STORE` owns the admission predicate).
* It does **not** claim that LDK performs this exact reset for a failed
  payment; it claims only that `succeeded` is a fixpoint and that non-success
  states are reset to the model's single non-terminal state.
* `retryIfNotSucceeded` is not production-wired here.  Replacing
  `Keysend.retry` at a call site is an integrator decision; the old definition
  and `retry_pending` stay in place.
-/

namespace LnLean.Proofs.Wave14.KeysendRetryGuard

set_option autoImplicit false

open LnLean
open LnLean.Payment

/-! ## The guarded retry -/

/-- Retry a keysend only when it has not already succeeded.

A `succeeded` session is returned unchanged, so a completed payment cannot be
sent again by this path.  A `failed` (or `pending`) session is reset to
`pending`; the preimage, amount, CLTV expiry, CLTV floor and payment hash are
untouched. -/
def retryIfNotSucceeded (k : Keysend) : Keysend :=
  if k.session.state = .succeeded then k
  else { k with session := { k.session with state := .pending } }

/-- The guarded retry is the identity on a succeeded keysend. -/
theorem retryIfNotSucceeded_succeeded (k : Keysend)
    (h : k.session.state = .succeeded) :
    retryIfNotSucceeded k = k := by
  unfold retryIfNotSucceeded
  simp [h]

/-- The guarded retry resets a failed keysend to `pending`, i.e. a failed
payment remains retryable. -/
theorem retryIfNotSucceeded_failed (k : Keysend)
    (h : k.session.state = .failed) :
    (retryIfNotSucceeded k).session.state = .pending := by
  unfold retryIfNotSucceeded
  simp [h]

/-- The guarded retry leaves an already-pending session pending.  Since
`pending` is the only non-terminal model state, the reset is a no-op on the
state field for a pending payment. -/
theorem retryIfNotSucceeded_pending (k : Keysend)
    (h : k.session.state = .pending) :
    (retryIfNotSucceeded k).session.state = .pending := by
  unfold retryIfNotSucceeded
  simp [h]

/-- The guarded retry keeps the sender's preimage: it never invents a new
preimage on either branch. -/
theorem retryIfNotSucceeded_preimage (k : Keysend) :
    (retryIfNotSucceeded k).preimage = k.preimage := by
  unfold retryIfNotSucceeded
  by_cases h : k.session.state = .succeeded <;> simp [h]

/-- The guarded retry keeps the session's payment hash, so a retry stays on
the same payment identity. -/
theorem retryIfNotSucceeded_session_paymentHash (k : Keysend) :
    (retryIfNotSucceeded k).session.paymentHash = k.session.paymentHash := by
  unfold retryIfNotSucceeded
  by_cases h : k.session.state = .succeeded <;> simp [h]

/-- The guarded retry preserves structural validity. -/
theorem retryIfNotSucceeded_valid (k : Keysend) (sha256 : Preimage → PaymentHash)
    (h : k.Valid sha256) : (retryIfNotSucceeded k).Valid sha256 := by
  unfold retryIfNotSucceeded
  by_cases hs : k.session.state = .succeeded
  · simp [hs]
    exact h
  · simp [hs]
    exact ⟨h.hashIsPreimage, h.amountBound⟩

/-! ## The retained old behaviour -/

/-- The old unconditional `Keysend.retry` still resets a succeeded session to
`pending`.  This is exactly `Keysend.retry_pending`
(`KeysendProps.lean:300-301`) exposed under a wave-14 name so the divergence
is auditable; the old definition and theorem are not replaced or weakened. -/
theorem legacy_retry_resets_succeeded (k : Keysend)
    (_h : k.session.state = .succeeded) :
    k.retry.session.state = .pending :=
  Keysend.retry_pending k

/-- The old and guarded retries agree on a failed keysend at the level of the
resulting state: both yield `pending`. -/
theorem legacy_and_guarded_agree_failed (k : Keysend)
    (h : k.session.state = .failed) :
    k.retry.session.state = (retryIfNotSucceeded k).session.state := by
  rw [Keysend.retry_pending, retryIfNotSucceeded_failed k h]

/-! ## Concrete witnesses -/

/-- A concrete 32-byte preimage. -/
def witnessPreimage : Preimage :=
  ⟨ByteArray.mk (List.replicate 32 (7 : UInt8)).toArray⟩

/-- A concrete hash function for the witness: it copies the 32 preimage bytes.
This is not a cryptographic SHA-256; it only inhabits the witness. -/
def witnessSha256 (p : Preimage) : PaymentHash := ⟨p.bytes⟩

/-- A concrete amount, 1000 msat. -/
def witnessAmount : Msat := ⟨1000⟩

/-- A concrete keysend that has been settled successfully. -/
def witnessSucceeded : Keysend :=
  (Keysend.create witnessSha256 witnessPreimage witnessAmount 100 18).settle .succeeded

/-- A concrete keysend that has failed. -/
def witnessFailed : Keysend :=
  (Keysend.create witnessSha256 witnessPreimage witnessAmount 100 18).settle .failed

/-- The succeeded witness really is succeeded. -/
theorem witnessSucceeded_state : witnessSucceeded.session.state = .succeeded := by
  unfold witnessSucceeded Keysend.settle PaymentSession.settle Keysend.create
  simp

/-- The failed witness really is failed. -/
theorem witnessFailed_state : witnessFailed.session.state = .failed := by
  unfold witnessFailed Keysend.settle PaymentSession.settle Keysend.create
  simp

/-- **The divergence witness.**  On the concrete succeeded keysend, the old
`Keysend.retry` returns a `pending` session, while the guarded retry returns
the succeeded record unchanged.  This is the executable separation the review
asked to retain. -/
theorem witness_retry_diverges :
    witnessSucceeded.session.state = .succeeded ∧
    witnessSucceeded.retry.session.state = .pending ∧
    (retryIfNotSucceeded witnessSucceeded).session.state = .succeeded ∧
    retryIfNotSucceeded witnessSucceeded = witnessSucceeded := by
  refine ⟨witnessSucceeded_state, ?_, ?_, ?_⟩
  · exact Keysend.retry_pending witnessSucceeded
  · rw [retryIfNotSucceeded_succeeded witnessSucceeded witnessSucceeded_state]
    exact witnessSucceeded_state
  · exact retryIfNotSucceeded_succeeded witnessSucceeded witnessSucceeded_state

/-- The failed witness exercises the reset branch: the guarded retry turns
`failed` into `pending`. -/
theorem witnessFailed_guarded_retry :
    (retryIfNotSucceeded witnessFailed).session.state = .pending :=
  retryIfNotSucceeded_failed witnessFailed witnessFailed_state

/-! ## Axiom audit -/

#print axioms retryIfNotSucceeded_succeeded
#print axioms retryIfNotSucceeded_failed
#print axioms retryIfNotSucceeded_pending
#print axioms retryIfNotSucceeded_preimage
#print axioms retryIfNotSucceeded_session_paymentHash
#print axioms retryIfNotSucceeded_valid
#print axioms legacy_retry_resets_succeeded
#print axioms legacy_and_guarded_agree_failed
#print axioms witnessSucceeded_state
#print axioms witnessFailed_state
#print axioms witness_retry_diverges
#print axioms witnessFailed_guarded_retry

end LnLean.Proofs.Wave14.KeysendRetryGuard
