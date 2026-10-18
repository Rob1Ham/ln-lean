import LnLean.Payment.Invoice
import LnLean.Payment.HTLC
import LnLean.Proofs.Payment.InvoiceProps

/-!
# LnLean.Proofs.ModelHardening.F13

English claim.  BOLT 4's "Payload for the Last Node" carries
`payment_data = (payment_secret, total_msat)`.  The final node must compare
that `payment_secret` with the `s` field of the BOLT 11 invoice before it
accepts the HTLC (BOLT 4 final-node requirements; LDK `FinalOnionHopData` is
checked against the registered payment secret).  The shipped model has both
halves of that fact in isolation -- `Invoice.paymentSecret` is a mandatory
32-byte field and `PaymentSession` carries the invoice's payment hash -- but
it never introduces a terminal payload record, so it contains no predicate
tying an invoice's secret to a payload's secret.

This module supplies the missing bridge.

* `FinalPayload` is the part of BOLT 4's final payload relevant to the secret
  binding: the payment secret, `total_msat`, `amt_to_forward`, and
  `outgoing_cltv_value`.
* `FinalPayloadAcceptedFor fp i` is the final-node admission predicate: the
  payload is accepted for invoice `i` only when its payment secret equals the
  invoice's secret.
* `PaymentBridge i s fp` additionally records that the payment session `s`
  is keyed by the invoice's payment hash, giving the full invoice/session/
  final-payload bridge.

Proved here: acceptance is exactly secret equality, so any accepted payload
has the invoice's secret (and its bytes); two payloads accepted for the same
invoice agree; a valid invoice forces every accepted payload's secret to be
32 bytes; and an explicitly constructed `FinalPayload.forInvoice` is accepted.

The unconditional form of LN-PM-003 ("the final payload's secret matches the
invoice's secret") is false for the shipped model, because nothing constrains
an arbitrary payload record.  It was refuted and removed;
`two_accepted_payloads_distinct_secrets` (and its single-payload form
`unconstrained_accept_not_match`) mechanizes the counterexample for one valid
invoice.  The strongest true replacement is `accepted_secret_eq`, which
concludes matching from the explicit `FinalPayloadAcceptedFor` hypothesis.
No claim is silently weakened: matching is only ever concluded through
`FinalPayloadAcceptedFor`.

BOLT anchors (pinned BOLTs commit
`1aadb719b4007c4cea0ba6e36b08c4fb53788dee`).
* `refs/bolts/04-onion-routing.md:185-219` `payload`/`payment_data` TLV types.
* `refs/bolts/04-onion-routing.md:285-295` final payload writer.
* `refs/bolts/04-onion-routing.md:1528-1545` final-node amount/secret checks.
* `refs/bolts/11-payment-encoding.md:133-163` `s` tagged field (32 bytes).

rust-lightning anchors (commit `fe4900930c6bd5786ec4203274d7cf312776a5a6`).
* `lightning/src/ln/onion_payment.rs:329` `FinalOnionHopData { payment_secret,
  total_msat }`.
* `lightning/src/ln/onion_payment.rs:856` final-payload secret/hash checking.
* `lightning-invoice/src/lib.rs:1357` `check_payment_secret`.

Not modelled: bech32 encoding, payment-secret derivation/encryption, and
onion encryption.  The bridge is a semantic admission predicate over already
decoded fields, exactly as `Invoice` itself is.
-/

namespace LnLean.Proofs.ModelHardening.F13

set_option autoImplicit false

open LnLean
open LnLean.Payment

/-! ## The final payload and the bridge -/

/-- The BOLT 4 "Payload for the Last Node" fields that participate in the
invoice binding.  `payment_data` consists of `paymentSecret` and `totalMsat`;
`amtToForward` and `outgoingCltvValue` are the final hop's amount and CLTV
from the same payload. -/
structure FinalPayload where
  /-- BOLT 4 `payment_data.payment_secret`. -/
  paymentSecret : PaymentSecret
  /-- BOLT 4 `payment_data.total_msat`. -/
  totalMsat : Msat
  /-- BOLT 4 final-hop `amt_to_forward`. -/
  amtToForward : Msat
  /-- BOLT 4 final-hop `outgoing_cltv_value`. -/
  outgoingCltvValue : Height
deriving Repr, DecidableEq, BEq

/-- A payload built from an invoice's own payment secret.  The other final-payload
fields are supplied by the sender; only the secret is copied from the invoice. -/
def FinalPayload.forInvoice (i : Invoice) (amtToForward totalMsat : Msat)
    (outgoingCltvValue : Height) : FinalPayload where
  paymentSecret := i.paymentSecret
  totalMsat := totalMsat
  amtToForward := amtToForward
  outgoingCltvValue := outgoingCltvValue

/-- **The missing bridge predicate.**  BOLT 4 requires the final node to
accept an HTLC only when the final payload's `payment_secret` equals the `s`
field of the invoice the payment is for.  The shipped model has no such
predicate; this definition is the reusable admission rule. -/
def FinalPayloadAcceptedFor (fp : FinalPayload) (i : Invoice) : Prop :=
  fp.paymentSecret = i.paymentSecret

/-- The full invoice/session/final-payload bridge: the session is keyed by the
invoice's payment hash (BOLT 11 `p`; BOLT 4 HTLC-set lookup) and the final
payload carries the invoice's payment secret (BOLT 11 `s`). -/
structure PaymentBridge (i : Invoice) (s : PaymentSession) (fp : FinalPayload) : Prop where
  hashMatches : s.paymentHash = i.paymentHash
  secretMatches : FinalPayloadAcceptedFor fp i

/-! ## Matching under the bridge -/

/-- Acceptance is exactly equality of the payload secret and the invoice
secret.  This is the definitional content of the bridge. -/
theorem accepted_iff_secret_eq (fp : FinalPayload) (i : Invoice) :
    FinalPayloadAcceptedFor fp i ↔ fp.paymentSecret = i.paymentSecret :=
  Iff.rfl

/-- **Payment-secret matching.**  Every final payload accepted for an invoice
carries that invoice's payment secret. -/
theorem accepted_secret_eq {fp : FinalPayload} {i : Invoice}
    (h : FinalPayloadAcceptedFor fp i) : fp.paymentSecret = i.paymentSecret :=
  h

/-- Matching at the modelled byte-string level, which is the form later
commitment/derivation layers consume. -/
theorem accepted_secret_bytes_eq {fp : FinalPayload} {i : Invoice}
    (h : FinalPayloadAcceptedFor fp i) :
    fp.paymentSecret.bytes = i.paymentSecret.bytes :=
  congrArg PaymentSecret.bytes h

/-- Two payloads accepted for the same invoice necessarily agree on the
payment secret: the secret is not an unconstrained per-payload choice once
the bridge is enforced (the LDK `check_merge` requirement for a set). -/
theorem accepted_secrets_eq {i : Invoice} {fp₁ fp₂ : FinalPayload}
    (h₁ : FinalPayloadAcceptedFor fp₁ i) (h₂ : FinalPayloadAcceptedFor fp₂ i) :
    fp₁.paymentSecret = fp₂.paymentSecret :=
  h₁.trans h₂.symm

/-- A structurally valid invoice makes every accepted payload's secret a
32-byte value (BOLT 11 `s` has 52 five-bit groups). -/
theorem accepted_secret_size {fp : FinalPayload} {i : Invoice}
    (h : FinalPayloadAcceptedFor fp i) (hv : i.Valid) :
    fp.paymentSecret.bytes.size = 32 := by
  rw [accepted_secret_eq h]
  exact hv.paymentSecretLength

/-- The bridge is stable under replacing the invoice by any invoice with the
same payment secret. -/
theorem accepted_of_invoice_secret_eq {fp : FinalPayload} {i j : Invoice}
    (h : FinalPayloadAcceptedFor fp i) (hij : i.paymentSecret = j.paymentSecret) :
    FinalPayloadAcceptedFor fp j :=
  h.trans hij

/-- **Existence direction.**  The sender can always build a payload that the
bridge accepts: copy the invoice's payment secret into the final payload. -/
theorem forInvoice_accepted (i : Invoice) (amtToForward totalMsat : Msat)
    (outgoingCltvValue : Height) :
    FinalPayloadAcceptedFor
      (FinalPayload.forInvoice i amtToForward totalMsat outgoingCltvValue) i :=
  rfl

/-- The full bridge gives both halves at once: the session hash and the
payload secret match the invoice. -/
theorem bridge_hash_and_secret {i : Invoice} {s : PaymentSession}
    {fp : FinalPayload} (h : PaymentBridge i s fp) :
    s.paymentHash = i.paymentHash ∧ fp.paymentSecret = i.paymentSecret :=
  ⟨h.hashMatches, h.secretMatches⟩

/-- The full bridge can be assembled from its two independently checkable
facts. -/
theorem bridge_of_parts {i : Invoice} {s : PaymentSession} {fp : FinalPayload}
    (hh : s.paymentHash = i.paymentHash) (hs : FinalPayloadAcceptedFor fp i) :
    PaymentBridge i s fp :=
  ⟨hh, hs⟩

/-! ## The unconstrained-secret counterexample -/

/-- 32 zero bytes, used to build concrete secrets for the counterexample. -/
def secretBytesZero : ByteArray :=
  ByteArray.mk (List.replicate 32 (0 : UInt8)).toArray

/-- 32 one bytes, used to build a second concrete secret. -/
def secretBytesOne : ByteArray :=
  ByteArray.mk (List.replicate 32 (1 : UInt8)).toArray

/-- The all-zero 32-byte payment secret. -/
def secretZero : PaymentSecret := ⟨secretBytesZero⟩

/-- The all-one 32-byte payment secret. -/
def secretOne : PaymentSecret := ⟨secretBytesOne⟩

theorem secretBytesZero_size : secretBytesZero.size = 32 := by decide

theorem secretBytesOne_size : secretBytesOne.size = 32 := by decide

/-- The two concrete 32-byte secrets really are different. -/
theorem secretZero_ne_secretOne : secretZero ≠ secretOne := by
  decide

/-- A structurally valid invoice carrying `secretZero`, built from the
committed `zeroAmountInvoice` witness. -/
def counterexampleInvoice : Invoice := zeroAmountInvoice

theorem counterexampleInvoice_valid : counterexampleInvoice.Valid :=
  zeroAmountInvoice_valid

theorem counterexampleInvoice_secret : counterexampleInvoice.paymentSecret = secretZero :=
  rfl

/-- A payload carrying a secret different from the invoice's. -/
def mismatchedPayload : FinalPayload where
  paymentSecret := secretOne
  totalMsat := Msat.zero
  amtToForward := Msat.zero
  outgoingCltvValue := 0

/-- The model's acceptance relation without the bridge: no field of `Invoice`,
`PaymentSession`, `OnionHop`, or `FinalPayload` constrains a payload's secret,
so the shipped model accepts everything.  This is the precise content of the
missing predicate. -/
def UnconstrainedFinalAccept (_fp : FinalPayload) (_i : Invoice) : Prop := True

theorem mismatchedPayload_not_accepted :
    ¬ FinalPayloadAcceptedFor mismatchedPayload counterexampleInvoice := by
  intro h
  have h' : secretOne = secretZero := h
  exact secretZero_ne_secretOne h'.symm

/-- **Counterexample.**  Unconstrained final-payload acceptance does not imply
payment-secret matching: a valid invoice and an accepted payload can disagree
on the secret. -/
theorem unconstrained_accept_not_match :
    ∃ (i : Invoice) (fp : FinalPayload),
      i.Valid ∧ UnconstrainedFinalAccept fp i ∧ ¬ FinalPayloadAcceptedFor fp i :=
  ⟨counterexampleInvoice, mismatchedPayload, counterexampleInvoice_valid, trivial,
    mismatchedPayload_not_accepted⟩

/-- **Stronger counterexample.**  For one valid invoice, the unconstrained
model accepts two final payloads whose payment secrets differ. -/
theorem two_accepted_payloads_distinct_secrets :
    ∃ (i : Invoice) (fp₁ fp₂ : FinalPayload),
      i.Valid ∧ UnconstrainedFinalAccept fp₁ i ∧ UnconstrainedFinalAccept fp₂ i ∧
        fp₁.paymentSecret ≠ fp₂.paymentSecret := by
  refine ⟨counterexampleInvoice,
    FinalPayload.forInvoice counterexampleInvoice Msat.zero Msat.zero 0,
    mismatchedPayload, counterexampleInvoice_valid, trivial, trivial, ?_⟩
  intro h
  have h' : secretZero = secretOne := h
  exact secretZero_ne_secretOne h'

/-! ## The repaired statement boundary

LN-PM-003 as written has no bridge hypothesis.  In the shipped model the
statement is false: `FinalPayload` is a new record, `Invoice` does not mention
it, and the counterexample above produces two payloads with different secrets
for one valid invoice.  The refuted unconditional declaration was removed
rather than retained with an open `sorry`; matching is available only in the
conditional form `accepted_secret_eq` (and its corollaries), whose explicit
`FinalPayloadAcceptedFor` hypothesis is the BOLT 4 final-node secret check. -/

-- REPAIRED: `waveF_f13_unconditional_secret_match` was refuted for the
-- shipped model and removed.  Counterexample:
-- `two_accepted_payloads_distinct_secrets` (`unconstrained_accept_not_match`
-- is the single-payload form).  Strongest true replacement:
-- `accepted_secret_eq : FinalPayloadAcceptedFor fp i → fp.paymentSecret = i.paymentSecret`.

end LnLean.Proofs.ModelHardening.F13
