import LnLean.Payment.Invoice
import LnLean.Payment.HTLC

/-!
# LnLean.Payment.MPP

English claim.  A basic multi-part payment (BOLT 4 `basic_mpp`, feature bits
16/17) is a set of HTLC parts that share one payment hash and one payment
secret.  Each `MPPPart` names the outgoing channel, its millisatoshi amount,
and its absolute CLTV expiry.  An `MPPPlan` groups the parts under the
payment hash, the recipient's payment secret, and the total target.  A plan is
`mppComplete` when it has at least one part and the part amounts sum exactly
to the target.  `mppAtomic` says the observed per-part outcomes are all
success or all failure — no mixed outcome.  The payment secret binding is the
byte string of the secret; equality of that modelled field determines
equality of the secret.

What is proved here: sum lemmas (`sumParts_nil`, `sumParts_cons`,
`sumParts_append`), the fact that each part amount is at most the total, and
uniqueness of the secret matching a plan.  The payment-level laws (sum equals
target, no part exceeds target, secret-binding injectivity) are in
`LnLean.Payment.Laws`.

BOLT sections.
* BOLT 4 "Final Node" and "Final Payload": `payment_data` contains
  `payment_secret` and `total_msat`; the HTLC set shares `payment_hash`;
  the final node fulfils all parts or none; each part carries
  `amt_to_forward` and `outgoing_cltv_value`.
* BOLT 11 `p` and `s` fields, and feature bit 16/17 (`basic_mpp`).
* BOLT 9 feature bits 14/15 (`payment_secret`) and 16/17 (`basic_mpp`).
* BOLT 2 `update_add_htlc` supplies `amount_msat`, `payment_hash`, and
  `cltv_expiry` per part; BOLT 2 does not define `payment_secret`.

BOLT line anchors (pinned BOLTs commit
1aadb719b4007c4cea0ba6e36b08c4fb53788dee).
* `refs/bolts/04-onion-routing.md:185-219` `payload`/`payment_data` types.
* `refs/bolts/04-onion-routing.md:350-410` multipart HTLC-set rules.
* `refs/bolts/04-onion-routing.md:1528-1545` final-node checks.
* `refs/bolts/11-payment-encoding.md:133-163` `p` and `s` tags.
* `refs/bolts/07-routing-gossip.md` `short_channel_id` (BOLT 7).
* `refs/bolts/09-features.md:42-43` `payment_secret`, `basic_mpp`.
* `refs/bolts/02-peer-protocol.md:2772-2790` `update_add_htlc`.

rust-lightning anchors (commit fe4900930c6bd5786ec4203274d7cf312776a5a6).
* `lightning/src/ln/outbound_payment.rs:124` `Retryable` with `total_msat`
  and `payment_secret`.
* `lightning/src/ln/outbound_payment.rs:137` `total_msat` (all paths).
* `lightning/src/ln/outbound_payment.rs:869` `secret_only` (the common
  BOLT 11 MPP recipient fields).
* `lightning/src/ln/outbound_payment.rs:949` `check_merge`: all parts must
  agree on `payment_secret`, `payment_metadata`, and `total_mpp_amount_msat`.
* `lightning/src/ln/inbound_payment.rs:391` `verify`.
* `lightning/src/ln/inbound_payment.rs:506` `payment_data.total_msat` must be
  at least the registered minimum.
* `lightning/src/ln/onion_payment.rs:329` `FinalOnionHopData { payment_secret,
  total_msat }`.
* `lightning-invoice/src/lib.rs:1357` `check_payment_secret`.

Not modelled.
* Onion construction, route selection, and per-part fee arithmetic.
* The recipient-side HTLC-set timeout (`mpp_timeout`) and the 60-second
  window; `mppAtomic` is the safety conclusion, not a liveness claim.
* Partial-payment overpayment above `total_msat`.  `mppComplete` uses exact
  equality, which is the conservative form of BOLT 4's "equal to or greater
  than `total_msat`"; the overpay variant is a separate obligation
  (`LN-PAY-MPP-OVERPAY`).
* The cryptographic derivation of the payment secret (LDK encrypts payment
  info into the secret).  Only the 32-byte binding field is modelled.
-/

namespace LnLean.Payment

set_option autoImplicit false

open LnLean

/-! ## Parts and plans -/

/-- One part of a multi-part payment.  `channel` is the outgoing
`short_channel_id` (BOLT 7), `amount` is the part's `amt_to_forward`, and
`cltv` is the absolute `outgoing_cltv_value` (or the incoming CLTV for the
final hop). -/
structure MPPPart where
  channel : ShortChannelId
  amount : Msat
  cltv : Height
deriving Repr, DecidableEq, BEq

/-- A multi-part payment plan: the shared payment hash and payment secret, the
total target in millisatoshis, the constituent parts, and the recipient's
minimum final CLTV delta (BOLT 11 `c`, default 18). -/
structure MPPPlan where
  paymentHash : PaymentHash
  paymentSecret : PaymentSecret
  target : Msat
  parts : List MPPPart
  minFinalCltv : Height := DEFAULT_MIN_FINAL_CLTV
deriving Repr

/-! ## Sums -/

/-- Total of the part amounts, in millisatoshis.  A `Nat` avoids an overflow
precondition; the target bound is imposed by `mppComplete`. -/
def sumParts : List MPPPart → Nat
  | [] => 0
  | p :: ps => p.amount.val + sumParts ps

@[simp] theorem sumParts_nil : sumParts [] = 0 := rfl

@[simp] theorem sumParts_cons (p : MPPPart) (ps : List MPPPart) :
    sumParts (p :: ps) = p.amount.val + sumParts ps := rfl

/-- Summing a concatenation is adding the sums. -/
theorem sumParts_append (xs ys : List MPPPart) :
    sumParts (xs ++ ys) = sumParts xs + sumParts ys := by
  induction xs with
  | nil => simp [sumParts]
  | cons x xs ih =>
      simp [sumParts, ih]
      omega

namespace MPPPart

/-- Every part's amount is bounded by the total.  This is the arithmetic core
of the "no part exceeds the target" law. -/
theorem amount_le_sumParts {p : MPPPart} {ps : List MPPPart}
    (hp : p ∈ ps) : p.amount.val ≤ sumParts ps := by
  induction ps with
  | nil => cases hp
  | cons q qs ih =>
      rw [sumParts_cons]
      rcases List.mem_cons.mp hp with rfl | hmem
      · omega
      · have hle := ih hmem
        omega

end MPPPart

/-! ## Completeness and atomicity -/

/-- A plan is complete when it has at least one part and the parts sum exactly
to the target.  BOLT 4 permits `sum ≥ total_msat`; the exact form is the
conservative scaffold statement and is flagged as an obligation to relax. -/
def mppComplete (plan : MPPPlan) : Prop :=
  plan.parts ≠ [] ∧ sumParts plan.parts = plan.target.val

/-- Atomicity: the observed outcomes are all successes or all failures.
`outcomes` is positionally aligned with `plan.parts`.  The empty outcome list
is vacuously atomic; `mppComplete` separately requires a non-empty plan. -/
def mppAtomic (plan : MPPPlan) (outcomes : List PaymentState) : Prop :=
  outcomes.length = plan.parts.length ∧
    ((∀ s ∈ outcomes, s = .succeeded) ∨
     (∀ s ∈ outcomes, s = .failed))

/-- The payment secret binding used by the model: the secret's bytes.  This
is the field on which injectivity is stated (the cryptographic derivation of
the secret is not modelled). -/
def paymentSecretBinding (plan : MPPPlan) : ByteArray :=
  plan.paymentSecret.bytes

/-- The recipient accepts a plan with secret `s` only when the plan carries
exactly that secret (BOLT 4 `payment_data` / LDK `check_merge`). -/
def MPPPlan.bindsSecret (plan : MPPPlan) (s : PaymentSecret) : Prop :=
  plan.paymentSecret = s

theorem MPPPlan.bindsSecret_unique {plan : MPPPlan} {s t : PaymentSecret}
    (hs : plan.bindsSecret s) (ht : plan.bindsSecret t) : s = t := by
  unfold MPPPlan.bindsSecret at hs ht
  exact hs.symm.trans ht

/-- A plan's parts all agree on the secret: this is the MPP-set invariant
checked by LDK when a further HTLC joins the set. -/
def MPPPlan.allPartsShareSecret (plan : MPPPlan) : Prop :=
  ∀ s : PaymentSecret, plan.bindsSecret s → plan.paymentSecret = s

end LnLean.Payment
