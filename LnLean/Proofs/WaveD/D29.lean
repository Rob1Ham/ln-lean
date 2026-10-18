import LnLean.Payment.HTLC
import LnLean.Payment.Invoice
import LnLean.Payment.Laws
import LnLean.Payment.MPP

/-!
# D29 — The final onion payload's payment secret matches the invoice's payment secret

Catalog: `LN-PM-003`.  Catalog Lean target:
`LnLean.Payment.Invoice.payment_secret_match`.

## English claim

BOLT 4 "Payload for the Last Node" says that the origin node MUST set the
final hop's `payment_data.payment_secret` to the payment secret supplied by
the recipient, e.g. the BOLT 11 invoice `s` field.  The final node checks the
same field and MUST fail the HTLC if it does not match the expected value for
that payment hash.  The claim is therefore the sender/recipient agreement

> the final onion payload's `payment_secret` equals the invoice's
> `payment_secret`.

## Model reading and the gap this module closes

`LnLean.Payment.Invoice` models the invoice and its mandatory 32-byte
`paymentSecret`, but the model has **no final onion payload type**: the
terminal payload in `LnLean.Routing.Onion` is an opaque `ByteArray`, and no
module relates an invoice to a decoded final-hop payload.  The literal
unconditional claim over arbitrary `Invoice` and arbitrary payload values is
therefore false in the model: two unrelated records need not share a secret.

This module supplies a proof-local completion of the missing model piece:

* `FinalPayload` is the flattened final-hop payload: `amountToForward`,
  `outgoingCltv`, `totalMsat`, and the BOLT 4 `payment_data.payment_secret`;
* `FinalPayload.ofInvoice` is the sender-side construction that copies the
  invoice's secret (LDK `RecipientOnionFields::secret_only`);
* `FinalPayload.secretMatches` is the final node's secret check, and
  `FinalPayload.acceptedBy` additionally applies the BOLT 4 amount window.

The positive results are:

1. `waveD_d29_ofInvoice_secret` — a payload built from invoice `i` carries
   exactly `i.paymentSecret` (unconditional, by construction).
2. `waveD_d29_ofInvoice_acceptedBy` — that payload is accepted by `i` under
   the invoice's amount window.
3. `waveD_d29_secret_check_match` and `waveD_d29_payment_secret_match` — any
   payload that passes the recipient's secret check (or the full acceptance
   predicate) has the invoice's secret.  These are the faithful conditional
   forms of the catalog claim.
4. `waveD_d29_payment_secret_bytes_match`,
   `waveD_d29_accepted_secret_size`, and
   `waveD_d29_acceptedBy_secret_unique` — the match at the byte level, the
   32-byte validity inherited from a valid invoice, and uniqueness of the
   accepted secret.
5. `waveD_d29_accepted_matches_plan_secret` — the bridge to a BOLT 4 MPP
   plan: if the plan binds the invoice secret, then an accepted final payload
   also binds the plan's secret.
6. `waveD_d29_unconditional_claim_false` and
   `waveD_d29_amount_acceptance_not_enough` — mechanized counterexamples: a
   structurally valid invoice and a payload whose amount satisfies the
   invoice can still carry a different secret.  Thus the secret check cannot
   be dropped from the acceptance premise.

The counterexample is the reason the model target is stated conditionally.
It is a negative result about the current model, not a proof failure.

## BOLT anchors

Pinned BOLTs commit `1aadb719b4007c4cea0ba6e36b08c4fb53788dee`.

* `refs/bolts/04-onion-routing.md:185-219` — `payload` TLV format; type 8
  `payment_data` is `(32*byte payment_secret, tu64 total_msat)`.
* `refs/bolts/04-onion-routing.md:285-289` — writer rules: for the final node,
  MUST include `payment_data` and set `payment_secret` to the one provided.
* `refs/bolts/04-onion-routing.md:691-700` — "Payload for the Last Node": the
  origin MUST set `payment_secret` from the recipient's BOLT 11 invoice.
* `refs/bolts/04-onion-routing.md:1533-1535` — the final node MUST fail the
  HTLC if the secret does not match the expected value.
* `refs/bolts/11-payment-encoding.md:133-163` — BOLT 11 tagged fields; the
  `s` payment-secret field has 52 five-bit groups (32 bytes).

## rust-lightning anchors

Pinned commit `fe4900930c6bd5786ec4203274d7cf312776a5a6`.

* `lightning-invoice/src/lib.rs:1195` — `Bolt11Invoice::payment_secret()`,
  the accessor used to obtain the recipient's secret.
* `lightning/src/ln/outbound_payment.rs:1111` —
  `RecipientOnionFields::secret_only(*invoice.payment_secret(), amount)`:
  LDK copies the invoice secret into the outgoing onion fields.
* `lightning/src/ln/onion_payment.rs:856` — the pinned test assertion
  `payment_secret == pay_secret` for the final payload.
* `lightning/src/ln/inbound_payment.rs:391` — `verify` checks the incoming
  `FinalOnionHopData` against the registered payment secret.

## Not modelled

* The BigSize/TLV encoding of the final payload and the concrete
  `FinalOnionHopData` wire type.  `FinalPayload` is a proof-local semantic
  record, not a new model module.
* The sender's onion construction algorithm; `FinalPayload.ofInvoice` is the
  functional core of it (copy the invoice secret and amount fields).
* Payment-secret derivation/encryption (`construct_payment_secret`) and
  preimage soundness; only the opaque 32-byte secret is modelled.
-/

namespace LnLean.Proofs.WaveD.D29

set_option autoImplicit false

open LnLean
open LnLean.Payment

/-! ## The proof-local final-hop payload -/

/-- The semantic content of a BOLT 4 final-hop payload.  The four fields are
the final node's `amt_to_forward`, `outgoing_cltv_value`, and the
`payment_data` pair `(payment_secret, total_msat)`.  `short_channel_id` is
omitted because BOLT 4 forbids it for the final node.

This type is declared in the proof module because no model module currently
defines a final onion payload.  It is a completion of the model, not a model
edit. -/
structure FinalPayload where
  amountToForward : Msat
  outgoingCltv : Height
  totalMsat : Msat
  paymentSecret : PaymentSecret
deriving Repr, DecidableEq, BEq

namespace FinalPayload

/-- The sender-side construction of the final payload for invoice `i`: copy
the invoice's `payment_secret` into `payment_data`, together with the chosen
forwarding amount, total, and CLTV.  This is the functional core of LDK's
`RecipientOnionFields::secret_only(*invoice.payment_secret(), amount)` followed
by the onion writer. -/
def ofInvoice (i : Invoice) (amountToForward totalMsat : Msat)
    (outgoingCltv : Height) : FinalPayload where
  amountToForward := amountToForward
  outgoingCltv := outgoingCltv
  totalMsat := totalMsat
  paymentSecret := i.paymentSecret

/-- The final node's BOLT 4 secret check: the payload's `payment_secret`
equals the invoice's `s` field.  This is exactly the equality that BOLT 4
requires the final node to test, and the value LDK's `inbound_payment::verify`
compares against its registered secret. -/
def secretMatches (p : FinalPayload) (i : Invoice) : Prop :=
  p.paymentSecret = i.paymentSecret

/-- Recipient acceptance of the final payload against the invoice: the BOLT 4
secret check together with the BOLT 4 amount window (`amountSatisfies`).  The
CLTV and `total_msat` checks are not needed for the secret claim and are not
included. -/
def acceptedBy (p : FinalPayload) (i : Invoice) : Prop :=
  p.secretMatches i ∧ i.amountSatisfies p.amountToForward

end FinalPayload

/-! ## Sender-side propagation -/

/-- **A final payload built from an invoice carries that invoice's secret.**
The construction copies the field, so this is unconditional and definitional.
It is the sender half of the catalog claim. -/
theorem waveD_d29_ofInvoice_secret (i : Invoice) (amount total : Msat)
    (cltv : Height) :
    (FinalPayload.ofInvoice i amount total cltv).paymentSecret =
      i.paymentSecret := rfl

/-- The constructed payload passes the recipient's secret check. -/
theorem waveD_d29_ofInvoice_secretMatches (i : Invoice) (amount total : Msat)
    (cltv : Height) :
    (FinalPayload.ofInvoice i amount total cltv).secretMatches i := rfl

/-- The constructed payload is accepted whenever its amount satisfies the
invoice's BOLT 4 amount window. -/
theorem waveD_d29_ofInvoice_acceptedBy (i : Invoice) (amount total : Msat)
    (cltv : Height) (ha : i.amountSatisfies amount) :
    (FinalPayload.ofInvoice i amount total cltv).acceptedBy i :=
  ⟨rfl, ha⟩

/-! ## Recipient-side match -/

/-- Unfolding of the secret check. -/
theorem waveD_d29_secretMatches_iff (p : FinalPayload) (i : Invoice) :
    p.secretMatches i ↔ p.paymentSecret = i.paymentSecret := Iff.rfl

/-- Unfolding of acceptance into the secret check and the amount window. -/
theorem waveD_d29_acceptedBy_iff (p : FinalPayload) (i : Invoice) :
    p.acceptedBy i ↔
      p.paymentSecret = i.paymentSecret ∧
        i.amountSatisfies p.amountToForward := Iff.rfl

/-- **A payload that passes the final node's secret check has the invoice's
secret.**  This is the minimal conditional form of the catalog claim. -/
theorem waveD_d29_secret_check_match (i : Invoice) (p : FinalPayload)
    (h : p.secretMatches i) : p.paymentSecret = i.paymentSecret :=
  h

-- OBLIGATION: LN-WD-D29
/-- **Main theorem.**  A final payload accepted by the recipient against
invoice `i` (BOLT 4 secret check plus the amount window) has exactly the
invoice's payment secret.  The gap to the unconditional claim is the
acceptance/link premise, which the model does not provide as a field; see
`waveD_d29_unconditional_claim_false` for the mechanized gap. -/
theorem waveD_d29_payment_secret_match (i : Invoice) (p : FinalPayload)
    (h : p.acceptedBy i) : p.paymentSecret = i.paymentSecret :=
  h.1

/-- The match at the level of the modelled 32-byte binding: an accepted final
payload has the same secret bytes as the invoice. -/
theorem waveD_d29_payment_secret_bytes_match (i : Invoice) (p : FinalPayload)
    (h : p.acceptedBy i) :
    p.paymentSecret.bytes = i.paymentSecret.bytes :=
  congrArg PaymentSecret.bytes (waveD_d29_payment_secret_match i p h)

/-- Any two accepted final payloads for the same invoice carry the same
secret.  The recipient's secret check therefore determines the accepted
secret uniquely. -/
theorem waveD_d29_acceptedBy_secret_unique {i : Invoice}
    {p q : FinalPayload} (hp : p.acceptedBy i) (hq : q.acceptedBy i) :
    p.paymentSecret = q.paymentSecret :=
  hp.1.trans hq.1.symm

/-- A payload whose secret differs from the invoice's is rejected by the
secret check (contrapositive form of the match). -/
theorem waveD_d29_not_accepted_of_secret_ne {i : Invoice} {p : FinalPayload}
    (h : p.paymentSecret ≠ i.paymentSecret) : ¬ p.acceptedBy i :=
  fun ha => h ha.1

/-- If the invoice is structurally valid, an accepted final payload's secret
inherits the invoice's 32-byte wire length. -/
theorem waveD_d29_accepted_secret_size {i : Invoice} {p : FinalPayload}
    (hi : i.Valid) (hp : p.acceptedBy i) :
    p.paymentSecret.bytes.size = 32 := by
  rw [waveD_d29_payment_secret_match i p hp]
  exact hi.paymentSecretLength

/-! ## Bridge to a BOLT 4 MPP plan -/

/-- If a plan binds the invoice's secret, then an accepted final payload for
that invoice also binds the plan's secret.  This is the plan-level form of the
shared-secret requirement for the HTLC set. -/
theorem waveD_d29_accepted_matches_plan_secret {i : Invoice} {p : FinalPayload}
    {plan : MPPPlan} (hp : p.acceptedBy i)
    (hplan : plan.bindsSecret i.paymentSecret) :
    plan.bindsSecret p.paymentSecret := by
  unfold MPPPlan.bindsSecret at hplan ⊢
  exact hplan.trans (waveD_d29_payment_secret_match i p hp).symm

/-! ## The unconditional reading is false

`Invoice` and `FinalPayload` are unrelated records in the model.  Nothing
forces an arbitrary payload to carry the invoice's secret, and the amount
window alone is not enough: the examples below use a structurally valid
invoice and a payload whose amount satisfies it while the secrets differ. -/

/-- A concrete 32-byte all-zero string, used only for the counterexample. -/
def waveD_d29_bytes32zero : ByteArray :=
  ByteArray.mk (List.replicate 32 (0 : UInt8)).toArray

/-- A concrete 32-byte all-one string, used only for the counterexample. -/
def waveD_d29_bytes32one : ByteArray :=
  ByteArray.mk (List.replicate 32 (1 : UInt8)).toArray

/-- A 33-byte all-zero key, used only for the counterexample. -/
def waveD_d29_bytes33zero : ByteArray :=
  ByteArray.mk (List.replicate 33 (0 : UInt8)).toArray

/-- A 65-byte all-zero signature, used only for the counterexample. -/
def waveD_d29_bytes65zero : ByteArray :=
  ByteArray.mk (List.replicate 65 (0 : UInt8)).toArray

theorem waveD_d29_bytes32zero_size : waveD_d29_bytes32zero.size = 32 := rfl

theorem waveD_d29_bytes32one_size : waveD_d29_bytes32one.size = 32 := rfl

theorem waveD_d29_bytes33zero_size : waveD_d29_bytes33zero.size = 33 := rfl

theorem waveD_d29_bytes65zero_size : waveD_d29_bytes65zero.size = 65 := rfl

/-- The two counterexample secrets are distinct. -/
theorem waveD_d29_bytes32zero_ne_one :
    waveD_d29_bytes32zero ≠ waveD_d29_bytes32one := by
  decide

/-- A structurally valid invoice with a chosen payment secret and a concrete
amount of 1000 msat.  The other fixed fields have their BOLT 11 wire
lengths. -/
def waveD_d29_invoiceWithSecret (s : PaymentSecret) : Invoice where
  network := .mainnet
  amount := some ⟨1000⟩
  paymentHash := ⟨waveD_d29_bytes32zero⟩
  timestamp := 0
  expiry := DEFAULT_EXPIRY
  description := .direct ""
  payee := ⟨waveD_d29_bytes33zero⟩
  features := {}
  signature := ⟨waveD_d29_bytes65zero⟩
  paymentSecret := s
  minFinalCltvExpiry := DEFAULT_MIN_FINAL_CLTV

theorem waveD_d29_invoiceWithSecret_amount (s : PaymentSecret) :
    (waveD_d29_invoiceWithSecret s).amount = some ⟨1000⟩ := rfl

theorem waveD_d29_invoiceWithSecret_valid {s : PaymentSecret}
    (hs : s.bytes.size = 32) :
    (waveD_d29_invoiceWithSecret s).Valid := by
  refine ⟨waveD_d29_bytes32zero_size, hs, waveD_d29_bytes33zero_size,
    waveD_d29_bytes65zero_size, ?_, ?_, ?_⟩
  · intro a ha
    simp [waveD_d29_invoiceWithSecret] at ha
    subst a
    decide
  · simp [waveD_d29_invoiceWithSecret]
  · intro h hh
    cases hh

/-- The counterexample invoice: a valid invoice whose secret is 32 one-bytes. -/
def waveD_d29_exampleInvoice : Invoice :=
  waveD_d29_invoiceWithSecret ⟨waveD_d29_bytes32one⟩

/-- The counterexample final payload: the invoice's amount, but 32 zero-bytes
as the secret. -/
def waveD_d29_examplePayload : FinalPayload where
  amountToForward := ⟨1000⟩
  outgoingCltv := 0
  totalMsat := ⟨1000⟩
  paymentSecret := ⟨waveD_d29_bytes32zero⟩

theorem waveD_d29_exampleInvoice_valid : waveD_d29_exampleInvoice.Valid :=
  waveD_d29_invoiceWithSecret_valid (s := ⟨waveD_d29_bytes32one⟩)
    waveD_d29_bytes32one_size

/-- The example payload's secret differs from the example invoice's. -/
theorem waveD_d29_example_secret_ne :
    waveD_d29_examplePayload.paymentSecret ≠
      waveD_d29_exampleInvoice.paymentSecret := by
  intro h
  exact waveD_d29_bytes32zero_ne_one
    (congrArg PaymentSecret.bytes h)

/-- The example payload's amount still satisfies the invoice's amount window,
so the amount check alone does not force a secret match. -/
theorem waveD_d29_example_amount_satisfies :
    waveD_d29_exampleInvoice.amountSatisfies
      waveD_d29_examplePayload.amountToForward :=
  amountSatisfies_exact waveD_d29_exampleInvoice ⟨1000⟩ rfl

/-- **The amount window alone is not enough.**  There is a valid invoice and a
final payload that passes the amount check but carries a different payment
secret.  This is why the secret check is part of `acceptedBy`. -/
theorem waveD_d29_amount_acceptance_not_enough :
    waveD_d29_exampleInvoice.amountSatisfies
        waveD_d29_examplePayload.amountToForward ∧
      waveD_d29_examplePayload.paymentSecret ≠
        waveD_d29_exampleInvoice.paymentSecret :=
  ⟨waveD_d29_example_amount_satisfies, waveD_d29_example_secret_ne⟩

/-- The literal unconditional reading of the catalog claim: every final
payload carries the secret of every invoice.  The current model has no link
between an arbitrary payload and an invoice, so this form is stated explicitly
and refuted below. -/
def waveD_d29_unconditionalClaim : Prop :=
  ∀ (p : FinalPayload) (i : Invoice), p.paymentSecret = i.paymentSecret

/-- **The literal unconditional claim is false.**  There is no theorem of the
form `∀ p i, p.paymentSecret = i.paymentSecret` in the current model: an
arbitrary final payload and an arbitrary invoice are independent records.
The conditional theorems above are therefore the strongest faithful positive
results. -/
theorem waveD_d29_unconditional_claim_false :
    ¬ waveD_d29_unconditionalClaim := by
  intro h
  exact waveD_d29_example_secret_ne
    (h waveD_d29_examplePayload waveD_d29_exampleInvoice)

end LnLean.Proofs.WaveD.D29

/-! ## Catalog-target alias

The catalog names `LnLean.Payment.Invoice.payment_secret_match`.  The model
module does not declare it, so the conditional target is supplied here, in the
model namespace, using the proof-local final payload. -/

namespace LnLean.Payment

/-- **LN-PM-003 / `payment_secret_match`.**  An accepted final onion payload
has the invoice's payment secret.  This is the conditional form of the catalog
claim; the unconditional form is refuted by
`LnLean.Proofs.WaveD.D29.waveD_d29_unconditional_claim_false`. -/
theorem Invoice.payment_secret_match (i : Invoice)
    (p : LnLean.Proofs.WaveD.D29.FinalPayload)
    (h : p.acceptedBy i) : p.paymentSecret = i.paymentSecret :=
  LnLean.Proofs.WaveD.D29.waveD_d29_payment_secret_match i p h

end LnLean.Payment
