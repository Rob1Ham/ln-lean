import LnLean.Payment.Invoice
import LnLean.Proofs.Payment.InvoiceProps
import LnLean.Crypto.Hash

/-!
# LnLean.Proofs.PhaseC2.InvoiceBinding

English claim.  This module proves the three binding laws that connect a BOLT
11 invoice to the payment it authorizes:

1. **Amount binding.**  `Invoice.amountSatisfies` is the BOLT 4 final-node
   window `a ≤ paid ≤ 2*a` when the invoice specifies `a`.  For the
   *exact-payment* reading (the payer sends exactly the requested amount, so
   in particular never overpays), the window has a unique solution: any
   `paid` that both satisfies the window and is at most `a` equals `a`.
   Consequently the exact-payment predicate is equivalent to
   `amountSatisfies` plus the no-overpayment side condition.  Paying exactly
   `a` always satisfies the window.
2. **Payment-hash binding.**  `Invoice.preimageCommits sha256 p i` is the
   relation `sha256 p = i.paymentHash`.  A single preimage determines its
   payment hash with no cryptographic hypothesis.  Conversely, an invoice's
   payment hash determines at most one committing preimage *conditional on
   an explicitly stated injectivity hypothesis* for the hash function.  The
   hypothesis is a `Prop` parameter (`HashInjective` /
   `HashInjectiveOnValid`); this module never asserts that SHA-256 is
   injective.  A bridge theorem shows that the existing
   `LnLean.Crypto.CollisionResistant` field of `PrimitiveModel` supplies the
   valid-preimage form, and that `PreimageResistant` supplies the full form.
3. **Expiry binding.**  For a structurally valid invoice, the absolute
   expiry instant `expiresAtWith i e = i.timestamp + e` is monotone (and
   strictly monotone) in the expiry parameter `e`.  Extending the BOLT 11
   `x` field therefore never shortens the invoice's life, and an invoice
   that is unexpired at a smaller relative expiry remains unexpired at every
   larger one.

BOLT sections.
* BOLT 11 "Human-Readable Part" (optional positive amount),
  "Tagged Fields" (`p` payment hash, `x` expiry, `s` payment secret), and
  "Payer / Payee Requirements" (timestamp plus expiry, strict pass rule).
* BOLT 4 "Final Node" amount checks: below the expected amount fails, and
  more than twice the expected amount should fail.

BOLT line anchors (pinned BOLTs commit
`1aadb719b4007c4cea0ba6e36b08c4fb53788dee`).
* `refs/bolts/11-payment-encoding.md:47-87` HRP and optional amount.
* `refs/bolts/11-payment-encoding.md:133-163` tagged fields and fixed
  lengths for `p` and `s`; `x` default 3600.
* `refs/bolts/11-payment-encoding.md:344-359` expiry rule: the invoice has
  expired once `timestamp + expiry` has passed.
* `refs/bolts/04-onion-routing.md:1529-1547` final-node amount checks
  (`at least expected`, `at most twice expected`).

rust-lightning anchors (commit
`fe4900930c6bd5786ec4203274d7cf312776a5a6`).
* `lightning-invoice/src/lib.rs:1376` `check_amount`.
* `lightning-invoice/src/lib.rs:1529` `expires_at`;
  `:1534` `expiry_time`; `:1543` `is_expired`;
  `:1573` `would_expire` (strict `<`).
* `lightning-invoice/src/lib.rs:1662` `amount_milli_satoshis`.
* `lightning-types/src/payment.rs:23` `PaymentHash([u8; 32])`;
  `:49` `PaymentPreimage([u8; 32])`;
  `:70-73` payment hash is SHA-256 of the preimage.

What is explicitly NOT modelled.
* The bech32 encoding, HRP parsing, amount multipliers, and the signable
  digest.  `Invoice.verify` remains a parameterized predicate.
* Concrete SHA-256 compression, digest values, computational hardness, and
  preimage search.  Hash injectivity/collision resistance is a hypothesis,
  not a theorem of this module and not an axiom.
* Amount positivity as part of `Invoice.Valid`: the known phase-C gap
  (`exists_valid_zero_amount`) is inherited and not repaired here.  The
  amount-binding theorems are therefore stated for an arbitrary specified
  `a : Msat`; they do not claim `0 < a` unless that is an explicit
  hypothesis.
* Timestamp overflow and LDK's `checked_add` fallback: `Timestamp = Nat`.
-/

namespace LnLean.Proofs.PhaseC2

open LnLean
open LnLean.Payment
open LnLean.Crypto

set_option autoImplicit false

/-! ## 1. Amount binding for the BOLT 4 final-node window -/

/-- The exact-payment predicate: the payer sends precisely the amount named
by the invoice.  For an invoice without a specified amount the predicate is
vacuously true (there is no amount to match), which mirrors
`amountSatisfies`'s unconstrained `none` branch. -/
def ExactPayment (i : Invoice) (paid : Msat) : Prop :=
  ∀ a : Msat, i.amount = some a → paid = a

/-- Paying exactly the requested amount is always inside the BOLT 4 window.
No positivity or upper-bound hypothesis on `a` is needed. -/
theorem amountSatisfies_exact {i : Invoice} {a : Msat}
    (ha : i.amount = some a) : i.amountSatisfies a := by
  unfold Invoice.amountSatisfies
  rw [ha]
  constructor
  · exact Nat.le_refl a.val
  · exact Nat.le_mul_of_pos_left a.val (by decide : 0 < 2)

/-- **Amount pinning under exact payment.**  If the specified amount is `a`,
the paid amount lies in the BOLT 4 window, and the payer did not overpay
(`paid ≤ a`), then `paid` is exactly `a`.  The window's lower bound and the
no-overpayment side condition squeeze the two values together. -/
theorem amountSatisfies_pins_of_le {i : Invoice} {a paid : Msat}
    (ha : i.amount = some a) (hs : i.amountSatisfies paid)
    (hle : paid.val ≤ a.val) : paid = a := by
  unfold Invoice.amountSatisfies at hs
  rw [ha] at hs
  have hval : paid.val = a.val := Nat.le_antisymm hle hs.1
  cases paid with
  | mk pv =>
    cases a with
    | mk av =>
      simp only at hval
      rw [hval]

/-- **Exact-payment characterization.**  The exact-payment predicate is
equivalent to the BOLT 4 amount window plus the no-overpayment condition
`paid ≤ a`.  This is the precise sense in which `amountSatisfies` *pins*
the paid amount for exact payments: once overpayment is excluded, the
two-sided window has the single solution `paid = a`. -/
theorem exactPayment_iff_amountSatisfies_and_noOverpay
    (i : Invoice) (paid : Msat) :
    ExactPayment i paid ↔
      i.amountSatisfies paid ∧
        (∀ a : Msat, i.amount = some a → paid.val ≤ a.val) := by
  constructor
  · intro he
    constructor
    · unfold Invoice.amountSatisfies
      cases h : i.amount with
      | none => trivial
      | some a =>
          have hp : paid = a := he a h
          rw [hp]
          exact ⟨Nat.le_refl a.val, Nat.le_mul_of_pos_left a.val (by decide : 0 < 2)⟩
    · intro a ha
      rw [he a ha]
      exact Nat.le_refl a.val
  · rintro ⟨hs, hle⟩ a ha
    exact amountSatisfies_pins_of_le ha hs (hle a ha)

/-! ## 2. Payment-hash binding under an explicit hash hypothesis -/

/-- Explicit injectivity hypothesis for the invoice hash function.  This is
the algebraic proxy for collision resistance and is *assumed* of a concrete
instantiation; it is not proved of SHA-256 and is not an axiom of Lean. -/
def HashInjective (sha256 : Preimage → PaymentHash) : Prop :=
  Function.Injective sha256

/-- Weaker, validity-restricted injectivity: equal payment hashes of two
32-byte (valid) preimages imply equal preimages.  This is exactly the shape
of `LnLean.Crypto.CollisionResistant` transported from `ByteArray` to
`Preimage`, and is all that preimage uniqueness needs. -/
def HashInjectiveOnValid (sha256 : Preimage → PaymentHash) : Prop :=
  ∀ p q : Preimage, p.Valid → q.Valid → sha256 p = sha256 q → p = q

/-- Full injectivity implies validity-restricted injectivity. -/
theorem HashInjective.toOnValid {sha256 : Preimage → PaymentHash}
    (h : HashInjective sha256) : HashInjectiveOnValid sha256 := by
  intro p q _ _ hpq
  exact h hpq

/-- **A preimage determines its payment hash.**  Two invoices that both
receive the same committing preimage must carry the same payment hash.  This
direction is purely functional and needs no cryptographic hypothesis. -/
theorem preimageCommits_determines_hash {sha256 : Preimage → PaymentHash}
    (p : Preimage) {i j : Invoice}
    (hi : Invoice.preimageCommits sha256 p i)
    (hj : Invoice.preimageCommits sha256 p j) :
    i.paymentHash = j.paymentHash := by
  unfold Invoice.preimageCommits at hi hj
  rw [← hi, ← hj]

/-- **Preimage uniqueness under injectivity.**  If the hash function is
injective, an invoice's payment hash has at most one committing preimage.
This is the binding direction of `Invoice.preimageCommits`: the preimage
cannot be swapped for another one without changing the payment hash. -/
theorem preimageCommits_unique {sha256 : Preimage → PaymentHash}
    (hinj : HashInjective sha256) {i : Invoice} {p q : Preimage}
    (hp : Invoice.preimageCommits sha256 p i)
    (hq : Invoice.preimageCommits sha256 q i) : p = q := by
  apply hinj
  unfold Invoice.preimageCommits at hp hq
  exact hp.trans hq.symm

/-- **Preimage uniqueness from validity-restricted injectivity.**  The
weaker hypothesis still suffices when both preimages are valid 32-byte
values, which is the domain on which BOLT 2 and BOLT 11 use them. -/
theorem preimageCommits_unique_of_valid {sha256 : Preimage → PaymentHash}
    (hinj : HashInjectiveOnValid sha256) {i : Invoice} {p q : Preimage}
    (hpv : p.Valid) (hqv : q.Valid)
    (hp : Invoice.preimageCommits sha256 p i)
    (hq : Invoice.preimageCommits sha256 q i) : p = q := by
  apply hinj p q hpv hqv
  unfold Invoice.preimageCommits at hp hq
  exact hp.trans hq.symm

/-- **Bridge from the crypto model's collision resistance.**  If a
`PrimitiveModel`'s `sha256` is collision resistant on 32-byte inputs, then
its `paymentHashOf` is injective on valid preimages.  This connects the
explicit `HashInjectiveOnValid` hypothesis above to the existing field
`PrimitiveModel.sha256_collisionResistant` (assumption C1). -/
theorem paymentHashOf_injectiveOnValid (M : PrimitiveModel)
    (h : LnLean.Crypto.CollisionResistant M.sha256) :
    HashInjectiveOnValid M.paymentHashOf := by
  intro p q hp hq hpq
  exact LnLean.Crypto.paymentHash_commits M h hp hq hpq

/-- **Bridge from full preimage resistance.**  If `sha256` is injective on
all byte strings (`PreimageResistant`, the strong algebraic proxy in
`Crypto.Model`), then `paymentHashOf` is fully injective. -/
theorem paymentHashOf_injective (M : PrimitiveModel)
    (h : LnLean.Crypto.PreimageResistant M.sha256) :
    HashInjective M.paymentHashOf := by
  intro p q hpq
  have hbytes :
      PrimitiveModel.digest32 (M.sha256 p.bytes) =
        PrimitiveModel.digest32 (M.sha256 q.bytes) :=
    congrArg PaymentHash.bytes hpq
  have hp' : PrimitiveModel.digest32 (M.sha256 p.bytes) = M.sha256 p.bytes :=
    PrimitiveModel.digest32_of_size (M.sha256_size p.bytes)
  have hq' : PrimitiveModel.digest32 (M.sha256 q.bytes) = M.sha256 q.bytes :=
    PrimitiveModel.digest32_of_size (M.sha256_size q.bytes)
  have hsha : M.sha256 p.bytes = M.sha256 q.bytes := by
    rw [← hp', ← hq']
    exact hbytes
  have hpre : p.bytes = q.bytes := h p.bytes q.bytes hsha
  cases p with
  | mk pb =>
    cases q with
    | mk qb =>
      simp only at hpre
      rw [hpre]

/-- **Model-level preimage uniqueness.**  The crypto model's collision-
resistance field yields at most one valid preimage per invoice payment hash.
This is the invoice-specific form of `LnLean.Crypto.preimage_unique`. -/
theorem preimageCommits_unique_of_collisionResistant (M : PrimitiveModel)
    (h : LnLean.Crypto.CollisionResistant M.sha256)
    {i : Invoice} {p q : Preimage}
    (hpv : p.Valid) (hqv : q.Valid)
    (hp : Invoice.preimageCommits M.paymentHashOf p i)
    (hq : Invoice.preimageCommits M.paymentHashOf q i) : p = q :=
  preimageCommits_unique_of_valid
    (paymentHashOf_injectiveOnValid M h) hpv hqv hp hq

/-! ## 3. Expiry monotonicity for valid invoices -/

/-- Increasing the relative expiry `e` never decreases the absolute expiry
instant `timestamp + e`.  This is the parameterized form used by the BOLT 11
`x` field. -/
theorem expiresAtWith_mono (i : Invoice) {e e' : Nat} (h : e ≤ e') :
    i.expiresAtWith e ≤ i.expiresAtWith e' := by
  simpa [Invoice.expiresAtWith] using Nat.add_le_add_left h i.timestamp

/-- A strictly larger relative expiry gives a strictly later absolute
expiry instant. -/
theorem expiresAtWith_strictMono (i : Invoice) {e e' : Nat} (h : e < e') :
    i.expiresAtWith e < i.expiresAtWith e' := by
  simpa [Invoice.expiresAtWith] using Nat.add_lt_add_left h i.timestamp

/-- **Expiry monotonicity for a valid invoice.**  For `i.Valid`, the actual
absolute expiry `i.expiresAt = timestamp + i.expiry` is monotone when the
expiry parameter is increased beyond `i.expiry`.  The `Valid` hypothesis is
carried to match the protocol claim; the arithmetic itself is independent
of validity. -/
theorem valid_expiresAt_mono {i : Invoice} (_hv : i.Valid) {e' : Nat}
    (h : i.expiry ≤ e') : i.expiresAt ≤ i.expiresAtWith e' := by
  simpa [Invoice.expiresAt] using expiresAtWith_mono i h

/-- **Strict expiry monotonicity for a valid invoice.**  Strictly increasing
the expiry parameter strictly increases the absolute expiry instant. -/
theorem valid_expiresAt_strictMono {i : Invoice} (_hv : i.Valid) {e' : Nat}
    (h : i.expiry < e') : i.expiresAt < i.expiresAtWith e' := by
  simpa [Invoice.expiresAt] using expiresAtWith_strictMono i h

/-- Extending the relative expiry cannot make an invoice expired: if the
invoice has not expired by `expiresAtWith e`, then it has not expired by any
later `expiresAtWith e'` with `e ≤ e'`.  This is the payer-facing form of
expiry monotonicity, matching LDK's strict `would_expire` complement. -/
theorem not_expired_of_expiry_le {i : Invoice} {e e' now : Nat}
    (h : e ≤ e') (hne : ¬ i.expiresAtWith e < now) :
    ¬ i.expiresAtWith e' < now := by
  intro hlt
  exact hne (Nat.lt_of_le_of_lt (expiresAtWith_mono i h) hlt)

/-- Contrapositive form: an invoice that is already expired at a given
relative expiry was also expired under every smaller relative expiry. -/
theorem expired_of_expiry_ge {i : Invoice} {e e' now : Nat}
    (h : e ≤ e') (hexp : i.expiresAtWith e' < now) :
    i.expiresAtWith e < now :=
  Nat.lt_of_le_of_lt (expiresAtWith_mono i h) hexp

end LnLean.Proofs.PhaseC2
