import LnLean.Payment.Invoice
import LnLean.Basic.Core

/-!
# LnLean.Proofs.Payment.InvoiceProps

English claim.  For the BOLT 11 invoice model in `LnLean.Payment.Invoice`:

1. Structural validity (`Invoice.Valid`) gives the fixed wire lengths: the
   payment hash and payment secret are 32 bytes, the payee key is 33 bytes,
   and the compact signature is 65 bytes.  The same holds for any invoice
   returned by the semantic decoder below.
2. A valid invoice's optional amount is at most `Msat.MAX` (21M BTC) and its
   timestamp fits BOLT 11's 35-bit field.
3. BOLT 11's *positivity* rule for a specified amount is **not** a conjunct of
   the shipped `Invoice.Valid`.  We prove the gap with an explicit valid
   counterexample (`exists_valid_zero_amount`) and state the positive amount
   law for the strengthened predicate `Invoice.AmountPositive`; the model does
   not silently acquire the missing conjunct here.
4. `Invoice.amountSatisfies` is characterized exactly: with a specified amount
   `a` it holds iff `a ≤ paid ≤ 2 * a`, and it fails iff `paid < a` or
   `2 * a < paid`.  With no specified amount it holds for every payment,
   including zero (a second documented gap w.r.t. BOLT 11/4).
5. Expiry is monotone in both directions: an invoice valid at `t` is valid at
   every earlier `t' ≤ t`, and a strictly larger relative expiry gives a
   strictly later absolute expiry instant.  "Valid" here is the expiry-only
   predicate `Invoice.validAt`, i.e. `t ≤ timestamp + expiry`; it is not full
   invoice validity.
6. A proof-side *semantic* decoder (`decodeSemantic`, no bech32) preserves the
   network and payee fields, yields structurally valid invoices, fills in the
   BOLT 11 default expiry of 3600 seconds when the `x` field is absent, and
   preserves the `Msat.MAX` amount bound.
7. Verification (`Invoice.verify`) is exactly structural validity plus the
   caller-supplied signature checker's acceptance.  Any claim that the payee
   authorized the invoice is conditional on the crypto assumption C3, supplied
   as an explicit `InvoiceSignatureAssumption`; this file proves no
   unforgeability and no encoding law.

BOLT sections.
* BOLT 11 "Human-Readable Part" (network prefix and optional positive amount),
  "Data Part" (35-bit timestamp, 65-byte compact signature), "Tagged Fields"
  (`p`, `s`, `n`, `x`, `c`, `h`, `d`), and "Payer / Payee Requirements"
  (expiry).
* BOLT 4 "Final Node" amount window (`at least expected`, `at most twice
  expected`).

BOLT line anchors (pinned BOLTs commit
`1aadb719b4007c4cea0ba6e36b08c4fb53788dee`).
* `refs/bolts/11-payment-encoding.md:47-87` HRP, optional amount, positive
  decimal integer, multipliers.
* `refs/bolts/11-payment-encoding.md:104-131` data part, 35-bit timestamp,
  64-byte `R||S` plus 1-byte recovery id.
* `refs/bolts/11-payment-encoding.md:133-163` tagged fields and fixed
  lengths (`p`/`s`/`h` 52 groups, `n` 53 groups), `x` default 3600, `c`
  default 18.
* `refs/bolts/11-payment-encoding.md:165-214` reader/writer checks and the
  exactly-one-`d`-or-`h` rule.
* `refs/bolts/11-payment-encoding.md:344-359` payer/payee expiry rule
  ("after `timestamp` plus `expiry` has passed").
* `refs/bolts/04-onion-routing.md:1529-1547` final-node amount checks
  (below expected: fail; more than twice expected: should fail).

rust-lightning anchors (commit
`fe4900930c6bd5786ec4203274d7cf312776a5a6`).
* `lightning-invoice/src/lib.rs:132` `TIMESTAMP_BITS = 35`;
  `:137` `MAX_TIMESTAMP`; `:142` `DEFAULT_EXPIRY_TIME = 3600`;
  `:149` `DEFAULT_MIN_FINAL_CLTV_EXPIRY_DELTA = 18`.
* `lightning-invoice/src/lib.rs:272` `struct Bolt11Invoice`;
  `:383` `struct RawDataPart`; `:398` `struct PositiveTimestamp`;
  `:527` `enum TaggedField`; `:588` `Bolt11InvoiceSignature`.
* `lightning-invoice/src/lib.rs:1025` signature check on
  `SignedRawBolt11Invoice`; `:1322` `check_field_counts`;
  `:1357` `check_payment_secret`; `:1376` `check_amount`;
  `:1412` `Bolt11Invoice::check_signature`.
* `lightning-invoice/src/lib.rs:1529` `expires_at`;
  `:1534` `expiry_time` (default 3600); `:1543` `is_expired`;
  `:1549` `is_expired_from_epoch`; `:1573` `would_expire` (strict `<`);
  `:1662` `amount_milli_satoshis`.
* `lightning-types/src/payment.rs:23` `PaymentHash([u8; 32])`;
  `:82` `PaymentSecret([u8; 32])`.

Explicitly NOT modelled.
* bech32/charset encoding, HRP string parsing, and the signable digest.  No
  encoding theorem is claimed; `Invoice.verify` takes `digest` as a parameter
  and `decodeSemantic` starts from already-separated semantic fields.  Closing
  the encoding layer is `LN-PAY-INVOICE-ENCODING`.
* Recoverable ECDSA, public-key recovery, and key ownership.  The signature
  law is conditional on `InvoiceSignatureAssumption` (ASSUMPTIONS C3) and is
  not an unforgeability proof.
* HRP amount multipliers, amount precision (`ImpreciseAmount`), UTF-8
  validation of `d`, fallback addresses, private route hints, payment
  metadata, and feature-bit negotiation.
* Timestamp overflow: `Timestamp = Nat`, so LDK's `checked_add` fallback in
  `would_expire` has no counterpart.  Expiry monotonicity is therefore stated
  in the unbounded `Nat` domain.
* Payment-hash/preimage soundness; that remains conditional on a hash
  function (C1) and is not proved here.
-/

namespace LnLean.Payment

set_option autoImplicit false

open LnLean

/-! ## 1. Fixed field lengths and the amount bound -/

/-- A structurally valid invoice has a 32-byte payment hash: BOLT 11 `p` has
`data_length` 52 five-bit groups = 32 bytes; LDK stores
`PaymentHash([u8; 32])`. -/
theorem valid_paymentHash_size {i : Invoice} (h : i.Valid) :
    i.paymentHash.bytes.size = 32 :=
  h.paymentHashLength

/-- A verified invoice has a 32-byte payment hash.  The signature checker is a
parameter, so this is a structural consequence of verification only. -/
theorem verify_paymentHash_size {digest : Invoice → ByteArray}
    {sigCheck : PubKey → ByteArray → InvoiceSignature → Bool} {i : Invoice}
    (h : Invoice.verify digest sigCheck i) : i.paymentHash.bytes.size = 32 :=
  h.1.paymentHashLength

/-- A structurally valid invoice has a 32-byte payment secret (BOLT 11 `s`,
52 groups). -/
theorem valid_paymentSecret_size {i : Invoice} (h : i.Valid) :
    i.paymentSecret.bytes.size = 32 :=
  h.paymentSecretLength

/-- A structurally valid invoice has a 33-byte compressed payee key (BOLT 11
`n`, 53 groups). -/
theorem valid_payee_size {i : Invoice} (h : i.Valid) :
    i.payee.bytes.size = 33 :=
  h.payeeLength

/-- A structurally valid invoice carries the 65-byte compact signature of BOLT
11: 64 bytes `R || S` plus a one-byte recovery id. -/
theorem valid_signature_size {i : Invoice} (h : i.Valid) :
    i.signature.bytes.size = 65 :=
  h.signatureLength

/-- Every amount present in a structurally valid invoice is at most
`Msat.MAX` (the modelled 21M BTC supply). -/
theorem valid_amount_le_max {i : Invoice} (h : i.Valid) {a : Msat}
    (ha : i.amount = some a) : a.val ≤ Msat.MAX.val :=
  h.amountBound a ha

/-- A structurally valid invoice's creation timestamp fits BOLT 11's 35-bit
field (`MAX_TIMESTAMP = 2^35 - 1`, LDK `TIMESTAMP_BITS`). -/
theorem valid_timestamp_le_max {i : Invoice} (h : i.Valid) :
    i.timestamp ≤ MAX_TIMESTAMP :=
  h.timestampBound

/-- BOLT 11's default expiry is exactly one hour.  Checked structurally. -/
theorem DEFAULT_EXPIRY_eq : DEFAULT_EXPIRY = 3600 := rfl

/-- The modelled 35-bit timestamp maximum.  Checked structurally. -/
theorem MAX_TIMESTAMP_eq : MAX_TIMESTAMP = 2 ^ 35 - 1 := rfl

/-! ## 2. Amount positivity: a documented gap and its corrected statement -/

/-- A 32-byte all-zero byte array, used only to build a counterexample. -/
def invoiceBytes32 : ByteArray :=
  ByteArray.mk (List.replicate 32 (0 : UInt8)).toArray

/-- A 33-byte all-zero byte array, used only to build a counterexample. -/
def invoiceBytes33 : ByteArray :=
  ByteArray.mk (List.replicate 33 (0 : UInt8)).toArray

/-- A 65-byte all-zero byte array, used only to build a counterexample. -/
def invoiceBytes65 : ByteArray :=
  ByteArray.mk (List.replicate 65 (0 : UInt8)).toArray

theorem invoiceBytes32_size : invoiceBytes32.size = 32 := by decide

theorem invoiceBytes33_size : invoiceBytes33.size = 33 := by decide

theorem invoiceBytes65_size : invoiceBytes65.size = 65 := by decide

/-- A concrete structurally valid invoice whose specified amount is zero.
This is the counterexample showing that `Invoice.Valid` does not enforce the
BOLT 11 writer rule "MUST encode `amount` as a positive decimal integer". -/
def zeroAmountInvoice : Invoice where
  network := .mainnet
  amount := some Msat.zero
  paymentHash := ⟨invoiceBytes32⟩
  timestamp := 0
  expiry := DEFAULT_EXPIRY
  description := .direct ""
  payee := ⟨invoiceBytes33⟩
  features := {}
  signature := ⟨invoiceBytes65⟩
  paymentSecret := ⟨invoiceBytes32⟩
  minFinalCltvExpiry := DEFAULT_MIN_FINAL_CLTV

theorem zeroAmountInvoice_valid : zeroAmountInvoice.Valid := by
  refine ⟨invoiceBytes32_size, invoiceBytes32_size, invoiceBytes33_size,
    invoiceBytes65_size, ?_, ?_, ?_⟩
  · intro a ha
    simp only [zeroAmountInvoice, Option.some.injEq] at ha
    subst a
    decide
  · decide
  · intro h hh
    simp only [zeroAmountInvoice] at hh
    cases hh

/-- **Counterexample / gap.**  Structural validity alone does not make a
specified amount positive: `some 0` is accepted.  The BOLT 11 positivity rule
must therefore be added as an explicit conjunct by a future model revision
(`LN-PAY-INVOICE-004`). -/
theorem exists_valid_zero_amount :
    ∃ i : Invoice, i.Valid ∧ i.amount = some Msat.zero :=
  ⟨zeroAmountInvoice, zeroAmountInvoice_valid, rfl⟩

/-- The strengthened amount rule: whenever an amount is present, it is
strictly positive.  BOLT 11 line 69 requires a positive decimal integer. -/
def Invoice.AmountPositive (i : Invoice) : Prop :=
  ∀ a : Msat, i.amount = some a → 0 < a.val

/-- With the strengthened predicate, validity yields both the `Msat.MAX`
bound and positivity of the specified amount. -/
theorem valid_amount_bound_and_positive {i : Invoice} (h : i.Valid)
    (hp : i.AmountPositive) {a : Msat} (ha : i.amount = some a) :
    a.val ≤ Msat.MAX.val ∧ 0 < a.val :=
  ⟨h.amountBound a ha, hp a ha⟩

/-! ## 3. Exact characterization of `amountSatisfies` -/

/-- With a specified amount `a`, `amountSatisfies` is exactly the BOLT 4
window `a ≤ paid ≤ 2*a`. -/
theorem amountSatisfies_some_iff (i : Invoice) (a paid : Msat)
    (ha : i.amount = some a) :
    i.amountSatisfies paid ↔ a.val ≤ paid.val ∧ paid.val ≤ 2 * a.val := by
  simp [Invoice.amountSatisfies, ha]

/-- The exact failure set of the BOLT 4 amount window: an underpayment
(`paid < a`) or an overpayment above twice the requested amount. -/
theorem not_amountSatisfies_some_iff (i : Invoice) (a paid : Msat)
    (ha : i.amount = some a) :
    ¬ i.amountSatisfies paid ↔ paid.val < a.val ∨ 2 * a.val < paid.val := by
  rw [amountSatisfies_some_iff i a paid ha]
  omega

/-- A satisfied amount window with a positive requested amount forces the paid
amount to be positive. -/
theorem amountSatisfies_positive_of_positive_amount (i : Invoice) {a paid : Msat}
    (ha : i.amount = some a) (hs : i.amountSatisfies paid) (hpos : 0 < a.val) :
    0 < paid.val := by
  have h := (amountSatisfies_some_iff i a paid ha).1 hs
  omega

/-- With no specified amount, `amountSatisfies` places no restriction.  This
includes `paid = 0`, which BOLT 11's positive-payment convention would exclude;
the gap is recorded rather than hidden. -/
theorem amountSatisfies_none (i : Invoice) (paid : Msat)
    (h : i.amount = none) : i.amountSatisfies paid := by
  simp [Invoice.amountSatisfies, h]

/-! ## 4. Expiry monotonicity -/

namespace Invoice

/-- Expiry-only validity at observation time `t`: the invoice has not passed
`timestamp + expiry`.  This is the BOLT 11 payer/payee rule and is separate
from full structural/signature validity. -/
def validAt (i : Invoice) (t : Timestamp) : Prop := ¬ i.isExpired t

/-- Expiry validity is exactly `t ≤ timestamp + expiry`, matching LDK
`would_expire`'s strict `expires_at < at_time` complement. -/
theorem validAt_iff (i : Invoice) (t : Timestamp) :
    i.validAt t ↔ t ≤ i.timestamp + i.expiry := by
  simp [validAt, isExpired, expiresAt, expiresAtWith]

/-- **Expiry monotonicity (earlier time).**  An invoice valid at `t` is valid
at every earlier observation time `t' ≤ t`. -/
theorem validAt_mono_earlier (i : Invoice) {t t' : Timestamp}
    (h : i.validAt t) (hle : t' ≤ t) : i.validAt t' := by
  rw [validAt_iff] at h ⊢
  exact Nat.le_trans hle h

/-- Dually, expiry is an up-set: once expired, an invoice stays expired at
every later time. -/
theorem isExpired_mono_later (i : Invoice) {t t' : Timestamp}
    (h : i.isExpired t) (hle : t ≤ t') : i.isExpired t' :=
  Nat.lt_of_lt_of_le h hle

/-- A strictly larger relative expiry gives a strictly later absolute expiry
instant, so increasing the `x` field never shortens the invoice's life. -/
theorem expiresAtWith_strict_mono (i : Invoice) {e e' : Nat} (h : e < e') :
    i.expiresAtWith e < i.expiresAtWith e' := by
  simpa [expiresAtWith] using Nat.add_lt_add_left h i.timestamp

/-- The absolute expiry instant is definitionally `timestamp + expiry`. -/
theorem expiresAt_eq_timestamp_add (i : Invoice) :
    i.expiresAt = i.timestamp + i.expiry := rfl

end Invoice

/-! ## 5. Semantic parsing: network and payee preservation

`LnLean.Payment.Invoice` models invoices after decoding; it has no parser.
To state the required preservation law without pretending to model bech32, we
define a *semantic* decoder: it takes the already-separated tagged-field
values, performs the BOLT 11 reader's structural checks, applies the `x`/`c`
defaults, and returns an `Invoice`.  This is the contract the future bech32
parser must refine; no encoding or checksum claim is made. -/

/-- The semantic fields a BOLT 11 reader recovers before validation.  `expiry`
and `minFinalCltvExpiry` are optional because the `x` and `c` tags are
optional; `network` stands for the value parsed from the HRP. -/
structure RawInvoice where
  network : Network
  amount : Option Msat
  paymentHash : PaymentHash
  timestamp : Timestamp
  expiry : Option Nat
  description : InvoiceDescription
  payee : PubKey
  features : InvoiceFeatures
  signature : InvoiceSignature
  paymentSecret : PaymentSecret
  minFinalCltvExpiry : Option Nat

namespace RawInvoice

/-- The BOLT 11 reader's non-cryptographic checks, mirroring
`Invoice.Valid` without applying the `x`/`c` defaults. -/
structure StructurallyValid (r : RawInvoice) : Prop where
  paymentHashLength : r.paymentHash.bytes.size = 32
  paymentSecretLength : r.paymentSecret.bytes.size = 32
  payeeLength : r.payee.bytes.size = 33
  signatureLength : r.signature.bytes.size = 65
  amountBound : ∀ a : Msat, r.amount = some a → a.val ≤ Msat.MAX.val
  timestampBound : r.timestamp ≤ MAX_TIMESTAMP
  descriptionHashLength :
    ∀ h : ByteArray, r.description = InvoiceDescription.hash h → h.size = 32

end RawInvoice

/-- The semantic decoder.  On structurally valid input it returns the invoice
with BOLT 11 defaults for a missing `x` field (3600 seconds) and a missing `c`
field (18 blocks); otherwise it returns `none`.  It does not parse bech32,
check the signature, or build the signable digest. -/
noncomputable def decodeSemantic (r : RawInvoice) : Option Invoice := by
  classical
  exact
    if r.StructurallyValid then
      some {
        network := r.network
        amount := r.amount
        paymentHash := r.paymentHash
        timestamp := r.timestamp
        expiry := r.expiry.getD DEFAULT_EXPIRY
        description := r.description
        payee := r.payee
        features := r.features
        signature := r.signature
        paymentSecret := r.paymentSecret
        minFinalCltvExpiry := r.minFinalCltvExpiry.getD DEFAULT_MIN_FINAL_CLTV
      }
    else none

/-- **Network preservation.**  Any invoice produced by the semantic decoder
carries the network parsed from the HRP. -/
theorem decodeSemantic_network {r : RawInvoice} {i : Invoice}
    (h : decodeSemantic r = some i) : i.network = r.network := by
  unfold decodeSemantic at h
  split at h
  · simp only [Option.some.injEq] at h
    subst i
    rfl
  · simp at h

/-- **Payee preservation.**  Any invoice produced by the semantic decoder
carries the `n` payee key from the input fields. -/
theorem decodeSemantic_payee {r : RawInvoice} {i : Invoice}
    (h : decodeSemantic r = some i) : i.payee = r.payee := by
  unfold decodeSemantic at h
  split at h
  · simp only [Option.some.injEq] at h
    subst i
    rfl
  · simp at h

/-- Decoding a structurally valid raw invoice yields a structurally valid
invoice: all fixed lengths, the amount bound, the timestamp bound, and the
description-hash length are preserved. -/
theorem decodeSemantic_valid {r : RawInvoice} {i : Invoice}
    (h : decodeSemantic r = some i) : i.Valid := by
  unfold decodeSemantic at h
  split at h
  · rename_i hv
    simp only [Option.some.injEq] at h
    subst i
    exact ⟨hv.paymentHashLength, hv.paymentSecretLength, hv.payeeLength,
      hv.signatureLength, hv.amountBound, hv.timestampBound,
      hv.descriptionHashLength⟩
  · simp at h

/-- Decoding preserves the 32-byte payment hash. -/
theorem decodeSemantic_paymentHash_size {r : RawInvoice} {i : Invoice}
    (h : decodeSemantic r = some i) : i.paymentHash.bytes.size = 32 :=
  (decodeSemantic_valid h).paymentHashLength

/-- A missing `x` tag decodes to BOLT 11's default expiry of 3600 seconds
(LDK `expiry_time`'s `unwrap_or(DEFAULT_EXPIRY_TIME)`). -/
theorem decodeSemantic_expiry_none {r : RawInvoice} {i : Invoice}
    (he : r.expiry = none) (h : decodeSemantic r = some i) :
    i.expiry = DEFAULT_EXPIRY := by
  unfold decodeSemantic at h
  split at h
  · simp only [Option.some.injEq] at h
    subst i
    simp [he]
  · simp at h

/-- Decoding preserves the `Msat.MAX` amount bound. -/
theorem decodeSemantic_amount_le_max {r : RawInvoice} {i : Invoice}
    (h : decodeSemantic r = some i) {a : Msat} (ha : i.amount = some a) :
    a.val ≤ Msat.MAX.val :=
  (decodeSemantic_valid h).amountBound a ha

/-- Every structurally valid raw invoice is accepted by the semantic decoder
(it returns `some`), so the decoder does not silently drop valid input. -/
theorem decodeSemantic_isSome {r : RawInvoice} (h : r.StructurallyValid) :
    ∃ i : Invoice, decodeSemantic r = some i := by
  refine ⟨{
    network := r.network
    amount := r.amount
    paymentHash := r.paymentHash
    timestamp := r.timestamp
    expiry := r.expiry.getD DEFAULT_EXPIRY
    description := r.description
    payee := r.payee
    features := r.features
    signature := r.signature
    paymentSecret := r.paymentSecret
    minFinalCltvExpiry := r.minFinalCltvExpiry.getD DEFAULT_MIN_FINAL_CLTV }, ?_⟩
  simp [decodeSemantic, h]

/-! ## 6. Signature verification, conditional on the crypto assumption -/

/-- Verification unfolds to exactly structural validity plus the supplied
checker's acceptance.  No cryptographic property is built into `verify`. -/
theorem verify_iff_valid_and_check (digest : Invoice → ByteArray)
    (sigCheck : PubKey → ByteArray → InvoiceSignature → Bool) (i : Invoice) :
    Invoice.verify digest sigCheck i ↔
      i.Valid ∧ sigCheck i.payee (digest i) i.signature = true :=
  Iff.rfl

/-- The crypto seam for invoice signatures, in the style of
`LnLean.Crypto.Model`: the verifier, the authorization predicate, and the C3
EUF-CMA hypothesis are parameters.  A concrete instantiation must come from
the crypto layer; this structure asserts nothing by itself. -/
structure InvoiceSignatureAssumption where
  /-- The modelled signature verifier (C3 ECDSA in a concrete instantiation). -/
  accepts : PubKey → ByteArray → InvoiceSignature → Bool
  /-- "The payee key authorized this message under this signature". -/
  authorized : PubKey → ByteArray → InvoiceSignature → Prop
  /-- The named unforgeability property (ASSUMPTIONS C3). -/
  eufCma : Prop
  /-- Evidence that the crypto assumption holds for this instantiation. -/
  eufCmaHolds : eufCma
  /-- The crypto layer's soundness contract: accepted signatures are
  authorized. -/
  sound : eufCma → ∀ (pk : PubKey) (msg : ByteArray) (s : InvoiceSignature),
    accepts pk msg s = true → authorized pk msg s

/-- **Conditional signature law.**  If the checker satisfies the C3 soundness
contract, then a verified invoice's digest and signature were authorized by
its payee key.  The crypto assumption is an explicit hypothesis; the theorem
does not prove unforgeability and does not mention bech32. -/
theorem verify_authorized_under_assumption (A : InvoiceSignatureAssumption)
    {digest : Invoice → ByteArray} {i : Invoice}
    (h : Invoice.verify digest A.accepts i) :
    A.authorized i.payee (digest i) i.signature :=
  A.sound A.eufCmaHolds i.payee (digest i) i.signature h.2

end LnLean.Payment
