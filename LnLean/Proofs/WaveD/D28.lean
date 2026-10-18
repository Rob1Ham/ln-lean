import LnLean.Payment.HTLC
import LnLean.Payment.Invoice
import LnLean.Payment.Laws
import LnLean.Payment.MPP
import LnLean.Crypto.Model

/-!
# D28 — A BOLT 11 invoice signature is valid for the payee node key

English claim (catalog `LN-PM-002`).  A BOLT 11 invoice signature verifies
under the payee node key carried by the invoice.  BOLT 11 "Data Part" requires
the writer to produce a compact ECDSA/secp256k1 signature over the SHA-256
digest of HRP and data part, and the reader to check it against the `n` tagged
field (or recover the key from the signature when `n` is absent).  LDK
implements exactly this in `Bolt11Invoice::check_signature`: it verifies the
compact ECDSA signature over the stored digest under `payee_pub_key()` when
that field is present, and otherwise recovers the key.

BOLT anchors (pinned BOLTs commit
`1aadb719b4007c4cea0ba6e36b08c4fb53788dee`).
* `refs/bolts/11-payment-encoding.md:104-131` data part, signature and the
  reader's "MUST check that the `signature` is valid" requirement.
* `refs/bolts/11-payment-encoding.md:133-163` tagged fields, including the
  payee key `n` (53 five-bit groups).
* `refs/bolts/11-payment-encoding.md:344-360` payer/payee interactions.

rust-lightning anchors (commit `fe4900930c6bd5786ec4203274d7cf312776a5a6`).
* `lightning-invoice/src/lib.rs:272` `struct Bolt11Invoice`.
* `lightning-invoice/src/lib.rs:588` `struct PayeePubKey`.
* `lightning-invoice/src/lib.rs:1017` `recover_payee_pub_key`.
* `lightning-invoice/src/lib.rs:1025` `check_signature`.
* `lightning-invoice/src/lib.rs:1179` `payee_pub_key`.

What is proved here.

1. The model-level form of the claim: `Invoice.verify digest sigCheck i`
   contains, by construction, the check `sigCheck i.payee (digest i)
   i.signature = true`.  That is `waveD_d28_signature_valid_for_payee` (and
   the exact characterisation `waveD_d28_verify_iff`).  It is unconditional
   and holds for every invoice that the model calls verified.
2. Under the cryptographic premise that a compact signature determines its
   verification key (`SignatureKeyBinding`, the algebraic shadow of secp256k1
   public-key recovery), the payee key is *the* key that accepts the
   signature: any key that accepts it equals `i.payee`
   (`waveD_d28_accepting_key_eq_payee`), and two verified invoices with the
   same message and signature have the same payee
   (`waveD_d28_signing_key_unique`).
3. Under `Crypto.Model.EufCma` (the scaffold's canonical message-binding
   premise) a signature cannot verify under one payee key for two different
   digests, so the signature binds the signed data part
   (`waveD_d28_signature_binds_digest`); with an injective digest function it
   binds the whole invoice (`waveD_d28_signature_binds_invoice`).
4. `Invoice.verify` alone does **not** imply payee-key binding: `sigCheck` is
   an unconstrained parameter.  `waveD_d28_unconditional_binding_false`
   mechanises the counterexample (two valid invoices, distinct payees, the
   same digest and the same signature, both accepted by a key-ignoring
   checker).  Hence the binding conclusion genuinely needs item 2's premise.

Not modelled here (documented gap).  The BOLT 11 signable-digest byte
construction and bech32 encoding (`LN-PAY-INVOICE-ENCODING`), recoverable
ECDSA and secp256k1 key recovery (`LnLean.Crypto.Model`, assumptions C1–C8),
and the case where the `n` field is absent and the payee key must be
recovered from the signature.  `Invoice` always carries an explicit payee
key, so the model follows LDK's `Some(pk)` branch of `check_signature`.
-/

namespace LnLean.Proofs.WaveD.D28

set_option autoImplicit false

open LnLean
open LnLean.Payment

/-! ## The model-level signature statement -/

/-- The semantic reading of "the invoice signature is valid for the payee node
key": the supplied signature checker accepts the invoice's own payee key, the
invoice's signable digest, and the invoice's compact signature.  This is the
second component of `Invoice.verify`; keeping it as a named predicate makes
the catalog claim explicit without changing the model. -/
def signatureValidForPayee (digest : Invoice → ByteArray)
    (sigCheck : PubKey → ByteArray → InvoiceSignature → Bool)
    (i : Invoice) : Prop :=
  sigCheck i.payee (digest i) i.signature = true

/-- `Invoice.verify` is exactly structural validity together with a signature
that is valid for the payee node key.  The digest function and the signature
checker remain parameters: the model never asserts ECDSA unforgeability or
that the digest commits to the invoice fields. -/
theorem waveD_d28_verify_iff (digest : Invoice → ByteArray)
    (sigCheck : PubKey → ByteArray → InvoiceSignature → Bool) (i : Invoice) :
    Invoice.verify digest sigCheck i ↔
      i.Valid ∧ signatureValidForPayee digest sigCheck i :=
  Iff.rfl

-- OBLIGATION: LN-WD-D28
/-- **Main theorem.**  A verified BOLT 11 invoice has a signature that is
valid for its payee node key.  This is the model's `Invoice.verify` contract:
the checker is invoked with `i.payee` and `i.signature` over `digest i`, and
the result is `true`.  No cryptographic assumption is used; conversely this
theorem does not claim that `sigCheck` is a sound ECDSA verifier. -/
theorem waveD_d28_signature_valid_for_payee
    {digest : Invoice → ByteArray}
    {sigCheck : PubKey → ByteArray → InvoiceSignature → Bool}
    {i : Invoice} (h : Invoice.verify digest sigCheck i) :
    signatureValidForPayee digest sigCheck i :=
  h.2

/-- The signature is checked against the invoice's *own* payee key, not an
arbitrary key supplied elsewhere: the key argument of the accepting check is
definitionally `i.payee`, and the message is `digest i`. -/
theorem waveD_d28_accepting_check_is_payee
    {digest : Invoice → ByteArray}
    {sigCheck : PubKey → ByteArray → InvoiceSignature → Bool}
    {i : Invoice} (h : Invoice.verify digest sigCheck i) :
    sigCheck i.payee (digest i) i.signature = true :=
  h.2

/-- A verified invoice's payee key is a well-formed compressed secp256k1 key
(33 bytes), i.e. the key the signature was checked against is a node key on
the wire. -/
theorem waveD_d28_verified_payee_size
    {digest : Invoice → ByteArray}
    {sigCheck : PubKey → ByteArray → InvoiceSignature → Bool}
    {i : Invoice} (h : Invoice.verify digest sigCheck i) :
    i.payee.Valid :=
  h.1.payeeLength

/-- A verified invoice's compact signature is 65 bytes (`R || S` plus the
recovery id), the BOLT 11 wire shape that makes payee-key recovery possible. -/
theorem waveD_d28_verified_signature_size
    {digest : Invoice → ByteArray}
    {sigCheck : PubKey → ByteArray → InvoiceSignature → Bool}
    {i : Invoice} (h : Invoice.verify digest sigCheck i) :
    i.signature.Valid :=
  h.1.signatureLength

/-! ## Conditional key binding

The model's `sigCheck` is an arbitrary Boolean function, so the semantic
content of "valid *for the* payee node key" (uniqueness of the accepting key)
needs an explicit premise.  The premise below is the exact algebraic shadow of
recoverable ECDSA: a compact signature determines at most one verification key.
It is not implied by `Crypto.Model.EufCma`, which fixes the key and binds the
message instead. -/

/-- A signature checker binds the verification key if a message/signature pair
is accepted by at most one key.  This is the property LDK relies on when
`recover_payee_pub_key` turns a compact signature into a unique
`PayeePubKey` (`lightning-invoice/src/lib.rs:1017`). -/
def SignatureKeyBinding
    (sigCheck : PubKey → ByteArray → InvoiceSignature → Bool) : Prop :=
  ∀ (k k' : PubKey) (m : ByteArray) (s : InvoiceSignature),
    sigCheck k m s = true → sigCheck k' m s = true → k = k'

/-- Under key binding, every key that accepts a verified invoice's signature is
the invoice's payee key.  Equivalently: the payee key is the signing key, not
merely one of several keys that happen to accept the signature. -/
theorem waveD_d28_accepting_key_eq_payee
    {digest : Invoice → ByteArray}
    {sigCheck : PubKey → ByteArray → InvoiceSignature → Bool}
    (hbind : SignatureKeyBinding sigCheck)
    {i : Invoice} (hi : Invoice.verify digest sigCheck i)
    {k : PubKey} (hk : sigCheck k (digest i) i.signature = true) :
    k = i.payee :=
  hbind k i.payee (digest i) i.signature hk hi.2

/-- Under key binding, two verified invoices whose signatures are checked over
the same message and are the same signature must name the same payee.  This
is the precise form of "the signature is valid for one payee node key": it
cannot authenticate two distinct payees at once. -/
theorem waveD_d28_signing_key_unique
    {digest : Invoice → ByteArray}
    {sigCheck : PubKey → ByteArray → InvoiceSignature → Bool}
    (hbind : SignatureKeyBinding sigCheck)
    {i j : Invoice}
    (hi : Invoice.verify digest sigCheck i) (hj : Invoice.verify digest sigCheck j)
    (hd : digest i = digest j) (hs : i.signature = j.signature) :
    i.payee = j.payee := by
  refine hbind i.payee j.payee (digest i) i.signature hi.2 ?_
  rw [hd, hs]
  exact hj.2

/-- Recovering the payee key from the signature is unique: under key binding,
any "recovered" key that validates the invoice's signature equals the invoice's
declared payee key.  (The model has no separate recovery function; this states
the uniqueness property such a function would have to satisfy.) -/
theorem waveD_d28_recovered_key_unique
    {digest : Invoice → ByteArray}
    {sigCheck : PubKey → ByteArray → InvoiceSignature → Bool}
    (hbind : SignatureKeyBinding sigCheck)
    {i : Invoice} (hi : Invoice.verify digest sigCheck i) :
    ∀ k : PubKey, sigCheck k (digest i) i.signature = true → k = i.payee :=
  fun _ hk => waveD_d28_accepting_key_eq_payee hbind hi hk

/-! ## What the signature binds (conditional on `EufCma`)

`Crypto.Model.EufCma` fixes the key and says one signature cannot verify for
two messages.  Applied to BOLT 11, this is the statement that the signature
binds the signed data part: a payee cannot reuse one signature for two
different digests. -/

/-- Under `EufCma`, a signature valid under the payee key for a verified
invoice determines the signable digest uniquely: any other verified invoice
with the same payee and signature must have the same digest. -/
theorem waveD_d28_signature_binds_digest
    {digest : Invoice → ByteArray}
    {sigCheck : PubKey → ByteArray → InvoiceSignature → Bool}
    (hEuf : LnLean.Crypto.EufCma sigCheck)
    {i j : Invoice} (hp : i.payee = j.payee)
    (hi : Invoice.verify digest sigCheck i) (hj : Invoice.verify digest sigCheck j)
    (hs : i.signature = j.signature) :
    digest i = digest j := by
  refine hEuf i.payee (digest i) (digest j) i.signature hi.2 ?_
  simpa [hp, hs] using hj.2

/-- Under `EufCma` and an injective signable digest (the model's stand-in for
the BOLT 11 encoding being collision-free), a signature plus a payee key
determines the whole invoice record.  Neither hypothesis is derivable from
`Invoice.verify` itself. -/
theorem waveD_d28_signature_binds_invoice
    {digest : Invoice → ByteArray}
    {sigCheck : PubKey → ByteArray → InvoiceSignature → Bool}
    (hEuf : LnLean.Crypto.EufCma sigCheck)
    (hinj : Function.Injective digest)
    {i j : Invoice} (hp : i.payee = j.payee)
    (hi : Invoice.verify digest sigCheck i) (hj : Invoice.verify digest sigCheck j)
    (hs : i.signature = j.signature) :
    i = j :=
  hinj (waveD_d28_signature_binds_digest hEuf hp hi hj hs)

/-! ## The unconditional binding form is false

`sigCheck` is a parameter of `Invoice.verify`, so the model cannot exclude a
checker that ignores the key.  The counterexample below builds two valid
invoices that differ only in their payee key, share a digest and a signature,
and are both accepted.  Thus key binding must be assumed, not derived. -/

/-- A uniform byte string of length `n`. -/
def bytesOf (n : Nat) (v : UInt8 := 0) : ByteArray :=
  ByteArray.mk (List.replicate n v).toArray

/-- First concrete payee key: 33 zero bytes. -/
def cexPayeeA : PubKey := ⟨bytesOf 33 0⟩

/-- Second concrete payee key: 33 one bytes. -/
def cexPayeeB : PubKey := ⟨bytesOf 33 1⟩

/-- The two counterexample payee keys are distinct. -/
theorem waveD_d28_cex_payees_distinct : cexPayeeA ≠ cexPayeeB := by
  intro h
  have hb : cexPayeeA.bytes = cexPayeeB.bytes := congrArg PubKey.bytes h
  exact (by decide : bytesOf 33 0 ≠ bytesOf 33 1) hb

/-- A structurally valid invoice whose only varying field is the payee key.
All fixed-length fields have the BOLT 11 shapes (32-byte hash and secret,
33-byte key, 65-byte signature), the timestamp is in range, there is no
amount, and the description is the direct form. -/
def cexInvoice (payee : PubKey) : Invoice where
  network := .mainnet
  amount := none
  paymentHash := ⟨bytesOf 32 2⟩
  timestamp := 0
  expiry := DEFAULT_EXPIRY
  description := .direct "d28"
  payee := payee
  features := {}
  signature := ⟨bytesOf 65 3⟩
  paymentSecret := ⟨bytesOf 32 4⟩
  minFinalCltvExpiry := DEFAULT_MIN_FINAL_CLTV

/-- The first counterexample invoice is structurally valid. -/
theorem waveD_d28_cex_valid_a : (cexInvoice cexPayeeA).Valid := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, Nat.zero_le _, ?_⟩
  · intro a ha
    cases ha
  · intro h hh
    cases hh

/-- The second counterexample invoice is structurally valid. -/
theorem waveD_d28_cex_valid_b : (cexInvoice cexPayeeB).Valid := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, Nat.zero_le _, ?_⟩
  · intro a ha
    cases ha
  · intro h hh
    cases hh

/-- A digest function that ignores the invoice. -/
def cexDigest : Invoice → ByteArray := fun _ => bytesOf 0

/-- A signature checker that ignores the key, the message, and the signature. -/
def cexSigCheck : PubKey → ByteArray → InvoiceSignature → Bool :=
  fun _ _ _ => true

/-- Both counterexample invoices verify under the key-ignoring checker. -/
theorem waveD_d28_cex_verify_both :
    Invoice.verify cexDigest cexSigCheck (cexInvoice cexPayeeA) ∧
      Invoice.verify cexDigest cexSigCheck (cexInvoice cexPayeeB) :=
  ⟨⟨waveD_d28_cex_valid_a, rfl⟩, ⟨waveD_d28_cex_valid_b, rfl⟩⟩

/-- The two counterexample invoices share the same signable digest and the same
compact signature, yet their payees differ. -/
theorem waveD_d28_cex_same_message_and_signature :
    cexDigest (cexInvoice cexPayeeA) = cexDigest (cexInvoice cexPayeeB) ∧
      (cexInvoice cexPayeeA).signature = (cexInvoice cexPayeeB).signature :=
  ⟨rfl, rfl⟩

/-- **Negative result.**  The unconditional reading "joint verification under
the same digest and signature implies equal payee keys" is false in the model.
The missing premise is `SignatureKeyBinding` (or, operationally, sound
recoverable-ECDSA key recovery).  This is why the positive binding theorems
above are conditional. -/
theorem waveD_d28_unconditional_binding_false :
    ¬ ∀ (digest : Invoice → ByteArray)
        (sigCheck : PubKey → ByteArray → InvoiceSignature → Bool)
        (i j : Invoice),
        Invoice.verify digest sigCheck i → Invoice.verify digest sigCheck j →
        digest i = digest j → i.signature = j.signature → i.payee = j.payee := by
  intro h
  have hpayee :
      (cexInvoice cexPayeeA).payee = (cexInvoice cexPayeeB).payee :=
    h cexDigest cexSigCheck (cexInvoice cexPayeeA) (cexInvoice cexPayeeB)
      waveD_d28_cex_verify_both.1 waveD_d28_cex_verify_both.2
      waveD_d28_cex_same_message_and_signature.1
      waveD_d28_cex_same_message_and_signature.2
  exact waveD_d28_cex_payees_distinct hpayee

/-- The key-ignoring checker satisfies verification but not key binding, so the
conditional theorems are not vacuous merely because no checker exists.  (This
also records that `SignatureKeyBinding` is a genuine restriction.) -/
theorem waveD_d28_key_binding_not_free :
    ¬ SignatureKeyBinding cexSigCheck := by
  intro hbind
  have hEq : cexPayeeA = cexPayeeB :=
    hbind cexPayeeA cexPayeeB (bytesOf 0) ⟨bytesOf 65 3⟩ rfl rfl
  exact waveD_d28_cex_payees_distinct hEq

end LnLean.Proofs.WaveD.D28
