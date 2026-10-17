import LnLean.Payment.Invoice
import LnLean.Payment.HTLC
import LnLean.Payment.MPP

/-!
# LnLean.Payment.Laws

English claim.  The payment/invoice layer has the following proved laws.

1. A verified invoice has a 32-byte payment hash, a 32-byte payment secret,
   a 33-byte payee key, and a 65-byte compact signature.
2. A verified invoice's optional amount is at most `Msat.MAX` (21M BTC),
   and its timestamp fits BOLT 11's 35-bit field.
3. Expiry is monotone: once an invoice is expired at time `t`, it remains
   expired at every later time; increasing the relative expiry never moves
   the absolute expiry instant earlier.
4. If an MPP plan is complete then its parts sum exactly to the target, the
   plan is non-empty, and no individual part exceeds the target.
5. The payment-secret binding (the secret's modelled byte field) is
   injective: equal bindings imply equal secrets.
6. `settle` is idempotent for the same outcome, and terminal sessions are
   absorbing (settling with any later outcome is a no-op).
7. `mppAtomic` admits no mixed outcome: it is impossible for one part to have
   succeeded and another to have failed.
8. Paying the invoice's stated amount satisfies `amountSatisfies`.

Every theorem below is proved; there are no obligations in this file.  The
statements are deliberately conditional on `Invoice.Valid` (via
`Invoice.verify`) or on `mppComplete`/`mppAtomic`, because an arbitrary
record of the corresponding type may violate the protocol's field lengths or
amount bounds.  The conditional form is the honest one: it is exactly the
BOLT 11 reader's contract.

BOLT sections.
* BOLT 11 "Data Part" (timestamp), "Tagged Fields" (`p`, `s`, `n`, `x`), and
  "Payer / Payee Requirements" (expiry), plus the amount bounds.
* BOLT 4 "Final Node" (amount at least expected, at most twice expected;
  the HTLC set is fulfilled in full or not at all).
* BOLT 2 `update_add_htlc` (`amount_msat`, `payment_hash`, `cltv_expiry`)
  and the fulfil/fail messages.
* BOLT 9 feature bits 14/15 and 16/17.

BOLT line anchors (pinned BOLTs commit
1aadb719b4007c4cea0ba6e36b08c4fb53788dee).
* `refs/bolts/11-payment-encoding.md:104-131` timestamp/signature.
* `refs/bolts/11-payment-encoding.md:133-163` tagged fields.
* `refs/bolts/11-payment-encoding.md:165-205` reader checks.
* `refs/bolts/11-payment-encoding.md:344-360` expiry rules.
* `refs/bolts/04-onion-routing.md:350-410` MPP/atomicity requirements.
* `refs/bolts/04-onion-routing.md:1528-1545` amount and secret checks.
* `refs/bolts/09-features.md:42-43` feature bits.
* `refs/bolts/02-peer-protocol.md:2772-2790` `update_add_htlc`.

rust-lightning anchors (commit fe4900930c6bd5786ec4203274d7cf312776a5a6).
* `lightning-invoice/src/lib.rs:132`/`:137` 35-bit timestamps.
* `lightning-invoice/src/lib.rs:1322` `check_field_counts` (one `p`).
* `lightning-invoice/src/lib.rs:1357` `check_payment_secret` (one `s`).
* `lightning-invoice/src/lib.rs:1376` `check_amount` (whole msat).
* `lightning-invoice/src/lib.rs:1412` `check_signature`.
* `lightning-invoice/src/lib.rs:1529` `expires_at`.
* `lightning-invoice/src/lib.rs:1543` `is_expired`.
* `lightning-invoice/src/lib.rs:1573` `would_expire`.
* `lightning/src/ln/outbound_payment.rs:320` `mark_fulfilled`.
* `lightning/src/ln/outbound_payment.rs:333` `mark_abandoned`.
* `lightning/src/ln/outbound_payment.rs:949` `check_merge` (secret and
  `total_mpp_amount_msat` must agree across parts).
* `lightning/src/ln/inbound_payment.rs:506` total-at-least-minimum check.
* `lightning/src/ln/inbound_payment.rs:391` `verify`.

Not modelled.
* The converse of field-length validity: field lengths do not imply
  signature validity or invoice authenticity; `Invoice.verify` keeps the
  signature checker as an explicit cryptographic premise.
* The bech32 encoding and signable digest (future `LN-PAY-INVOICE-ENCODING`).
* Overpayment of an HTLC set above `total_msat` (future
  `LN-PAY-MPP-OVERPAY`); `mppComplete` is the exact-sum form.
* Liveness: that a pending session eventually settles.  `settle` is a pure
  transition, not a scheduler.
-/

namespace LnLean.Payment

set_option autoImplicit false

open LnLean

/-! ## Invoice field and amount laws -/

/-- A verified invoice's payment hash is 32 bytes (BOLT 11 `p`, LDK
`PaymentHash([u8; 32])`). -/
theorem invoice_paymentHash_size {digest : Invoice → ByteArray}
    {sigCheck : PubKey → ByteArray → InvoiceSignature → Bool} {i : Invoice}
    (h : Invoice.verify digest sigCheck i) : i.paymentHash.bytes.size = 32 :=
  h.1.paymentHashLength

/-- A verified invoice's payment secret is 32 bytes (BOLT 11 `s`). -/
theorem invoice_paymentSecret_size {digest : Invoice → ByteArray}
    {sigCheck : PubKey → ByteArray → InvoiceSignature → Bool} {i : Invoice}
    (h : Invoice.verify digest sigCheck i) : i.paymentSecret.bytes.size = 32 :=
  h.1.paymentSecretLength

/-- A verified invoice's payee key is 33 bytes (BOLT 11 `n`). -/
theorem invoice_payee_size {digest : Invoice → ByteArray}
    {sigCheck : PubKey → ByteArray → InvoiceSignature → Bool} {i : Invoice}
    (h : Invoice.verify digest sigCheck i) : i.payee.bytes.size = 33 :=
  h.1.payeeLength

/-- A verified invoice's compact signature is 65 bytes (BOLT 11: 64-byte
`R || S` plus a one-byte recovery id). -/
theorem invoice_signature_size {digest : Invoice → ByteArray}
    {sigCheck : PubKey → ByteArray → InvoiceSignature → Bool} {i : Invoice}
    (h : Invoice.verify digest sigCheck i) : i.signature.bytes.size = 65 :=
  h.1.signatureLength

/-- A verified invoice's optional amount is within `Msat.MAX`, i.e. within
the 21 million BTC supply modelled by the L1 amount type. -/
theorem invoice_amount_le_max {digest : Invoice → ByteArray}
    {sigCheck : PubKey → ByteArray → InvoiceSignature → Bool} {i : Invoice}
    (h : Invoice.verify digest sigCheck i) {a : Msat} (ha : i.amount = some a) :
    a.val ≤ Msat.MAX.val :=
  h.1.amountBound a ha

/-- A verified invoice's timestamp fits the 35-bit BOLT 11 field. -/
theorem invoice_timestamp_le_max {digest : Invoice → ByteArray}
    {sigCheck : PubKey → ByteArray → InvoiceSignature → Bool} {i : Invoice}
    (h : Invoice.verify digest sigCheck i) : i.timestamp ≤ MAX_TIMESTAMP :=
  h.1.timestampBound

/-- Verification implies structural validity.  This is the bridge used by
the field-length laws above; it is not a cryptographic soundness claim. -/
theorem verify_implies_valid {digest : Invoice → ByteArray}
    {sigCheck : PubKey → ByteArray → InvoiceSignature → Bool} {i : Invoice}
    (h : Invoice.verify digest sigCheck i) : i.Valid :=
  h.1

/-- Verification runs the supplied signature checker successfully.  The
checker is a premise, so this theorem does not assert ECDSA unforgeability. -/
theorem verify_signature_check {digest : Invoice → ByteArray}
    {sigCheck : PubKey → ByteArray → InvoiceSignature → Bool} {i : Invoice}
    (h : Invoice.verify digest sigCheck i) :
    sigCheck i.payee (digest i) i.signature = true :=
  h.2

/-- Paying exactly the stated amount satisfies the BOLT 4 amount window. -/
theorem amountSatisfies_exact (i : Invoice) (a : Msat)
    (h : i.amount = some a) : i.amountSatisfies a := by
  simp only [Invoice.amountSatisfies, h]
  constructor <;> omega

/-! ## Expiry laws -/

/-- Expiry monotonicity in time: expiry is an up-set.  This matches LDK
`would_expire`, which compares `timestamp + expiry` strictly with the
observation time. -/
theorem isExpired_mono {i : Invoice} {t t' : Timestamp}
    (h : i.isExpired t) (hle : t ≤ t') : i.isExpired t' :=
  Nat.lt_of_lt_of_le h hle

/-- Expiry monotonicity in the duration: a larger relative expiry never
yields an earlier absolute expiry instant. -/
theorem expiry_monotone (i : Invoice) {e e' : Nat} (h : e ≤ e') :
    i.expiresAtWith e ≤ i.expiresAtWith e' := by
  simpa [Invoice.expiresAtWith] using Nat.add_le_add_left h i.timestamp

/-- The absolute expiry is exactly `timestamp + expiry`. -/
theorem expiresAt_eq (i : Invoice) :
    i.expiresAt = i.timestamp + i.expiry := rfl

/-! ## MPP sum laws -/

/-- Completeness gives the exact part sum. -/
theorem mppComplete_sum_eq_target {plan : MPPPlan} (h : mppComplete plan) :
    sumParts plan.parts = plan.target.val :=
  h.2

/-- A complete MPP plan has at least one part. -/
theorem mppComplete_nonempty {plan : MPPPlan} (h : mppComplete plan) :
    plan.parts ≠ [] :=
  h.1

/-- No part of a complete MPP plan exceeds the target. -/
theorem mppComplete_no_part_exceeds_target {plan : MPPPlan}
    (h : mppComplete plan) {p : MPPPart} (hp : p ∈ plan.parts) :
    p.amount.val ≤ plan.target.val := by
  have hle := MPPPart.amount_le_sumParts hp
  rw [mppComplete_sum_eq_target h] at hle
  exact hle

/-- The secret binding is injective on the modelled byte field: two plans
with the same 32-byte secret binding carry the same `PaymentSecret`. -/
theorem paymentSecretBinding_injective {p q : MPPPlan}
    (h : paymentSecretBinding p = paymentSecretBinding q) :
    p.paymentSecret = q.paymentSecret := by
  cases p
  cases q
  simp only [paymentSecretBinding] at h
  exact congrArg PaymentSecret.mk h

/-- Equality of bindings is exactly equality of the payment secrets. -/
theorem paymentSecretBinding_eq_iff (p q : MPPPlan) :
    paymentSecretBinding p = paymentSecretBinding q ↔
      p.paymentSecret = q.paymentSecret := by
  constructor
  · exact paymentSecretBinding_injective
  · intro h
    unfold paymentSecretBinding
    rw [h]

/-- Atomicity excludes a mixed outcome within one HTLC set. -/
theorem mppAtomic_no_mixed {plan : MPPPlan} {outcomes : List PaymentState}
    (h : mppAtomic plan outcomes) {s t : PaymentState}
    (hs : s ∈ outcomes) (ht : t ∈ outcomes)
    (hsucc : s = .succeeded) (hfail : t = .failed) : False := by
  rcases h.2 with hall | hall
  · have hx := hall t ht
    rw [hfail] at hx
    cases hx
  · have hx := hall s hs
    rw [hsucc] at hx
    cases hx

/-! ## Settlement laws -/

/-- Settling twice with the same outcome equals settling once. -/
theorem settle_idempotent (s : PaymentSession) (outcome : PaymentState) :
    PaymentSession.settle (PaymentSession.settle s outcome) outcome =
      PaymentSession.settle s outcome := by
  unfold PaymentSession.settle
  by_cases hs : s.state = .pending
  · by_cases ho : outcome = .pending
    · simp [hs, ho]
    · simp [hs, ho]
  · simp [hs]

/-- A terminal session is fixed by any later settlement attempt. -/
theorem settle_terminal_fixed (s : PaymentSession) (outcome : PaymentState)
    (hs : s.state.isTerminal) :
    PaymentSession.settle s outcome = s :=
  PaymentSession.settle_terminal s outcome hs

/-- A pending session settled successfully reaches `succeeded` (the
non-vacuous form of `settle`'s transition). -/
theorem settle_succeeded_state (s : PaymentSession)
    (hs : s.state = .pending) :
    (PaymentSession.settle s .succeeded).state = .succeeded := by
  apply PaymentSession.settle_pending_terminal
  · exact hs
  · simp [PaymentState.isTerminal]

end LnLean.Payment
