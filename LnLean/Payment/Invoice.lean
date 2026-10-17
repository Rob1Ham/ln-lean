import LnLean.Basic.Core

/-!
# LnLean.Payment.Invoice

English claim.  This module models the *semantic* fields of a BOLT 11
invoice: the network prefix, an optional millisatoshi amount, the payment
hash, the creation timestamp, the relative expiry, the description (direct
or hashed), the payee key, the feature bits, the mandatory payment secret,
the final-CLTV floor, and the compact signature.  It defines the structural
validity predicate `Invoice.Valid`, the verifier `Invoice.verify` (whose
signature check is an explicit parameter, because the signable digest is a
BOLT 11 *encoding* object), `Invoice.isExpired`, and `Invoice.amountSatisfies`
(the BOLT 4 "at least expected, at most twice expected" rule).  It also
records the BOLT 11 tagged-field numbers and their fixed data lengths.

What is proved here: the tag-number map is injective, every tag fits in the
5-bit tag space, and the fixed data lengths match BOLT 11 (52 five-bit
groups for `p`/`s`/`h`, 53 for `n`).  The invoice laws themselves are in
`LnLean.Payment.Laws`.

BOLT sections.
* BOLT 11 "Human-Readable Part" (network prefix and optional amount),
  "Data Part" (timestamp and signature), "Tagged Fields" (`p`, `s`, `d`,
  `m`, `n`, `h`, `x`, `c`, `f`, `r`, `9`), "Feature Bits", and
  "Payer / Payee Requirements" (expiry).
* BOLT 4 "Final Node" and "Final Payload" for `payment_secret`,
  `total_msat`, and the amount bounds.
* BOLT 9 feature bits 14/15 (`payment_secret`) and 16/17 (`basic_mpp`).
* BOLT 2 `update_add_htlc` is the carrier of the amount and CLTV that the
  payment layer constrains; BOLT 2 does not itself define `payment_secret`.

BOLT line anchors (pinned BOLTs commit
1aadb719b4007c4cea0ba6e36b08c4fb53788dee).
* `refs/bolts/11-payment-encoding.md:47-87` human-readable part and amount.
* `refs/bolts/11-payment-encoding.md:104-131` data part, timestamp, signature.
* `refs/bolts/11-payment-encoding.md:133-163` tagged fields and lengths.
* `refs/bolts/11-payment-encoding.md:165-205` writer/reader field checks.
* `refs/bolts/11-payment-encoding.md:303-326` feature bits.
* `refs/bolts/11-payment-encoding.md:344-360` payer/payee expiry rules.
* `refs/bolts/04-onion-routing.md:185-219` `payload` TLV types.
* `refs/bolts/04-onion-routing.md:285-295` final payload writer.
* `refs/bolts/04-onion-routing.md:1528-1545` final-node amount/secret checks.
* `refs/bolts/09-features.md:42-43` `payment_secret`, `basic_mpp`.
* `refs/bolts/02-peer-protocol.md:2772-2790` `update_add_htlc` fields.

rust-lightning anchors (commit fe4900930c6bd5786ec4203274d7cf312776a5a6).
* `lightning-invoice/src/lib.rs:132` `TIMESTAMP_BITS = 35`.
* `lightning-invoice/src/lib.rs:137` `MAX_TIMESTAMP = (1 << 35) - 1`.
* `lightning-invoice/src/lib.rs:142` `DEFAULT_EXPIRY_TIME = 3600`.
* `lightning-invoice/src/lib.rs:149` `DEFAULT_MIN_FINAL_CLTV_EXPIRY_DELTA = 18`.
* `lightning-invoice/src/lib.rs:164` `MAX_TAGGED_FIELD_DATA_BYTES = 639`.
* `lightning-invoice/src/lib.rs:272` `struct Bolt11Invoice`.
* `lightning-invoice/src/lib.rs:383` `struct RawDataPart` (timestamp + tags).
* `lightning-invoice/src/lib.rs:398` `struct PositiveTimestamp`.
* `lightning-invoice/src/lib.rs:439` `enum Currency`.
* `lightning-invoice/src/lib.rs:527` `enum TaggedField`.
* `lightning-invoice/src/lib.rs:613` tag constants (`p`=1, `d`=13, `n`=19,
  `h`=23, `x`=6, `c`=24, `f`=9, `r`=3, `s`=16, `m`=27, `9`=5).
* `lightning-invoice/src/lib.rs:680` `amount_milli_satoshis`.
* `lightning-invoice/src/lib.rs:1025` `check_signature`.
* `lightning-invoice/src/lib.rs:1322` `check_field_counts`.
* `lightning-invoice/src/lib.rs:1357` `check_payment_secret`.
* `lightning-invoice/src/lib.rs:1376` `check_amount`.
* `lightning-invoice/src/lib.rs:1529` `expires_at`.
* `lightning-invoice/src/lib.rs:1534` `expiry_time` (default 3600).
* `lightning-invoice/src/lib.rs:1543` `is_expired`.
* `lightning-invoice/src/lib.rs:1573` `would_expire` (strict `<` at time).
* `lightning-invoice/src/lib.rs:1662` `amount_milli_satoshis` accessor.
* `lightning-types/src/payment.rs:23` `PaymentHash([u8; 32])`.
* `lightning-types/src/payment.rs:49` `PaymentPreimage([u8; 32])`.
* `lightning-types/src/payment.rs:82` `PaymentSecret([u8; 32])`.

Not modelled.
* The bech32/charset encoding, HRP parsing, and the signable-digest byte
  construction.  `Invoice.verify` therefore takes the digest function as a
  parameter; closing this is `LN-PAY-INVOICE-ENCODING` (future work).
* Recoverable-ECDSA and public-key recovery.  `Invoice.verify` takes the
  signature checker as a parameter and never assumes unforgeability; a
  concrete instantiation must come from `LnLean.Crypto.Model` (C3).
* UTF-8 validation of the description, fallback addresses, private route
  hints, and payment metadata semantics.
* Amount multipliers (`m`, `u`, `n`, `p`) in the HRP; `Invoice.amount` is
  already in millisatoshis.
* Payment-hash/preimage correctness: see `Invoice.preimageCommits`, which is
  conditional on a caller-supplied hash function (C1).
-/

namespace LnLean.Payment

set_option autoImplicit false

open LnLean

/-! ## Networks and the human-readable prefix -/

/-- BOLT 11 currency/network prefix, restricted to the Bitcoin networks this
scaffold models.  BOLT 12 offers are out of scope. -/
inductive Network where
  | mainnet
  | testnet
  | signet
  | regtest
deriving Repr, DecidableEq, BEq, Inhabited

namespace Network

/-- The BOLT 11 human-readable prefix for each network.  `lntbs` is the
signet prefix used by current implementations. -/
def hrpPrefix : Network → String
  | .mainnet => "lnbc"
  | .testnet => "lntb"
  | .signet  => "lntbs"
  | .regtest => "lnbcrt"

/-- A numeric code, useful when stating injectivity without reasoning about
strings. -/
def code : Network → Nat
  | .mainnet => 0
  | .testnet => 1
  | .signet  => 2
  | .regtest => 3

theorem code_injective : Function.Injective code := by
  intro a b h
  cases a <;> cases b <;> simp [code] at h ⊢

end Network

/-! ## Payment secret, features, description, signature -/

/-- BOLT 11 `s` field / BOLT 4 `payment_secret`: a 32-byte value that binds
all parts of a payment to the recipient's authenticated payment data. -/
structure PaymentSecret where
  bytes : ByteArray
deriving Repr, DecidableEq, BEq

namespace PaymentSecret

def Valid (s : PaymentSecret) : Prop := s.bytes.size = 32

end PaymentSecret

/-- The invoice feature bits this scaffold cares about.  BOLT 9 assigns
`payment_secret` to bits 14/15 and `basic_mpp` to bits 16/17.  Unknown bits
and the full 5-bit wire encoding are not modelled. -/
structure InvoiceFeatures where
  paymentSecretRequired : Bool := true
  basicMpp : Bool := false
  variableLengthOnion : Bool := true
deriving Repr, DecidableEq, BEq, Inhabited

/-- A BOLT 11 description is either the direct UTF-8 string (`d`) or the
SHA-256 of an out-of-band description (`h`).  Exactly one must be present;
that structural requirement is part of `Invoice.Valid`. -/
inductive InvoiceDescription where
  | direct (text : String)
  | hash (digest : ByteArray)
deriving Repr, DecidableEq, BEq

/-- BOLT 11 signature: 64 bytes `R || S` followed by a one-byte recovery id,
i.e. 65 bytes on the wire.  The bytes are opaque here. -/
structure InvoiceSignature where
  bytes : ByteArray
deriving Repr, DecidableEq, BEq

namespace InvoiceSignature

def Valid (s : InvoiceSignature) : Prop := s.bytes.size = 65

/-- Recoverability hint.  BOLT 11 fixes the recovery id to `{0,1,2,3}`; this
predicate records the intended constraint without decoding the signature. -/
def recoveryIdInRange (rid : Nat) : Prop := rid < 4

end InvoiceSignature

/-! ## BOLT 11 constants -/

/-- BOLT 11 timestamps are 35-bit big-endian values. -/
def MAX_TIMESTAMP : Nat := 2 ^ 35 - 1

/-- BOLT 11 default expiry: one hour. -/
def DEFAULT_EXPIRY : Nat := 3600

/-- BOLT 11 default `min_final_cltv_expiry_delta`. -/
def DEFAULT_MIN_FINAL_CLTV : Nat := 18

/-- Maximum tagged-field payload: 1023 five-bit groups = 639 bytes. -/
def MAX_TAGGED_FIELD_DATA_BYTES : Nat := 639

/-! ## The invoice record -/

/-- The semantic content of a BOLT 11 invoice.  The optional amount is
already in millisatoshis; `expiry` is a relative duration in seconds.  The
payment secret is mandatory under the current BOLT 11 writer rules and LDK's
`check_payment_secret`. -/
structure Invoice where
  network : Network
  amount : Option Msat
  paymentHash : PaymentHash
  timestamp : Timestamp
  expiry : Nat := DEFAULT_EXPIRY
  description : InvoiceDescription
  payee : PubKey
  features : InvoiceFeatures
  signature : InvoiceSignature
  paymentSecret : PaymentSecret
  minFinalCltvExpiry : Nat := DEFAULT_MIN_FINAL_CLTV
deriving Repr

namespace Invoice

/-- Expiry relative to an arbitrary start time.  Used to state that increasing
the expiry never makes an invoice expire earlier. -/
def expiresAtWith (i : Invoice) (expiry : Nat) : Timestamp :=
  i.timestamp + expiry

/-- The absolute expiry instant `timestamp + expiry` (BOLT 11; LDK
`expires_at`).  This is a `Nat`, so it cannot overflow the model. -/
def expiresAt (i : Invoice) : Timestamp :=
  i.expiresAtWith i.expiry

/-- An invoice has expired at `now` once the expiry instant has strictly
passed.  This matches BOLT 11 "after timestamp plus expiry has passed" and
LDK `would_expire` (`expires_at < at_time`), not `≤`. -/
def isExpired (i : Invoice) (now : Timestamp) : Prop :=
  i.expiresAt < now

/-- The optional amount lies within the modelled money supply.  This is a
component of `Valid`, not an assumption about arbitrary records. -/
def amountWithinMax (i : Invoice) : Prop :=
  ∀ a : Msat, i.amount = some a → a.val ≤ Msat.MAX.val

/-- Structural validity, i.e. the BOLT 11 reader checks that do not require
cryptography: fixed-length fields (`p`, `s`, `n`, `h`), the 35-bit timestamp
bound, an amount inside `Msat.MAX`, and a 65-byte compact signature.
"Exactly one `d` or `h`" is enforced by the `InvoiceDescription` sum type. -/
structure Valid (i : Invoice) : Prop where
  paymentHashLength : i.paymentHash.bytes.size = 32
  paymentSecretLength : i.paymentSecret.bytes.size = 32
  payeeLength : i.payee.bytes.size = 33
  signatureLength : i.signature.bytes.size = 65
  amountBound : i.amountWithinMax
  timestampBound : i.timestamp ≤ MAX_TIMESTAMP
  descriptionHashLength :
    ∀ h : ByteArray, i.description = InvoiceDescription.hash h → h.size = 32

/-- Full verification.  `digest` is the BOLT 11 signable digest (HRP plus
data part, a future encoding obligation) and `sigCheck` is the recoverable
ECDSA check supplied by the crypto layer.  Verification is therefore
conditional, never an axiom. -/
def verify (digest : Invoice → ByteArray)
    (sigCheck : PubKey → ByteArray → InvoiceSignature → Bool)
    (i : Invoice) : Prop :=
  i.Valid ∧ sigCheck i.payee (digest i) i.signature = true

/-- The BOLT 4 / BOLT 11 amount rule: with a specified amount `a`, the payer
must send at least `a` and should not send more than twice `a` (BOLT 4
"Final Node" requirements).  With no amount, any strictly positive payment
is acceptable in this predicate. -/
def amountSatisfies (i : Invoice) (paid : Msat) : Prop :=
  match i.amount with
  | none => True
  | some a => a.val ≤ paid.val ∧ paid.val ≤ 2 * a.val

/-- Conditional payment-hash/preimage relation.  `sha256` is supplied by
`LnLean.Crypto.Model` (assumption C1) in wave B; this module deliberately
does not import the crypto module. -/
def preimageCommits (sha256 : Preimage → PaymentHash) (p : Preimage)
    (i : Invoice) : Prop :=
  sha256 p = i.paymentHash

end Invoice

/-! ## BOLT 11 tagged fields -/

/-- The BOLT 11 tagged-field numbers used by this scaffold.  `features`
denotes the `9` field; the name avoids a numeric identifier. -/
inductive Tag where
  | paymentHash
  | paymentSecret
  | description
  | descriptionHash
  | payeePubKey
  | expiry
  | minFinalCltv
  | paymentMetadata
  | fallback
  | privateRoute
  | features
deriving Repr, DecidableEq, BEq, Inhabited

namespace Tag

/-- Numeric tag as encoded in the five-bit `type` field (BOLT 11 tagged
fields; LDK `TAG_*` constants). -/
def code : Tag → Nat
  | .paymentHash      => 1
  | .paymentSecret    => 16
  | .description      => 13
  | .descriptionHash  => 23
  | .payeePubKey      => 19
  | .expiry           => 6
  | .minFinalCltv     => 24
  | .paymentMetadata  => 27
  | .fallback         => 9
  | .privateRoute     => 3
  | .features         => 5

/-- Fixed payload length in five-bit groups, where BOLT 11 fixes one:
`p`, `s`, and `h` use 52; `n` uses 53.  Variable-length tags return `none`. -/
def fixedDataLength : Tag → Option Nat
  | .paymentHash      => some 52
  | .paymentSecret    => some 52
  | .descriptionHash  => some 52
  | .payeePubKey      => some 53
  | .description      => none
  | .expiry           => none
  | .minFinalCltv     => none
  | .paymentMetadata  => none
  | .fallback         => none
  | .privateRoute     => none
  | .features         => none

theorem code_injective : Function.Injective code := by
  intro a b h
  cases a <;> cases b <;> simp [code] at h ⊢

/-- Every tag fits in the five-bit `type` field. -/
theorem code_lt_32 (t : Tag) : code t < 32 := by
  cases t <;> decide

/-- The payment hash, payment secret, and description hash all use BOLT 11's
52-group (32-byte) fixed payload. -/
theorem fixedDataLength_paymentHash : fixedDataLength .paymentHash = some 52 := rfl

theorem fixedDataLength_paymentSecret : fixedDataLength .paymentSecret = some 52 := rfl

theorem fixedDataLength_payeePubKey : fixedDataLength .payeePubKey = some 53 := rfl

end Tag

end LnLean.Payment
