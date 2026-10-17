import LnLean.Payment.Invoice
import LnLean.Payment.HTLC

/-!
# LnLean.Proofs.Payment.KeysendProps

English claim.  A *keysend* (spontaneous) payment is a Lightning payment with
**no BOLT 11 invoice**.  The sender chooses a 32-byte preimage `p` itself,
computes the payment hash `sha256 p`, and ships both the hash (in
`update_add_htlc`) and `p` (in the final onion payload, LDK TLV type
`5482373484`).  The recipient accepts only if `sha256 p` equals the HTLC's
payment hash; on settlement it reveals `p`, which is the same "proof of
payment" role that a BOLT 11 `p` tag plays for an invoiced payment.  Because
the amount and CLTV checks are the BOLT 4 final-node checks, a keysend is
subject to exactly the same amount window (`expected ≤ paid ≤ 2·expected`) and
CLTV floor (`current_height + min_final_cltv_expiry_delta ≤ cltv_expiry`) as
an invoiced payment whose invoice states the same amount and CLTV delta.

What this module states and proves (all in the wave-A payment model):

1. the payment hash of a keysend session is `sha256` of the sender's preimage
   (`keysend_create_hash`), and a freshly created keysend is structurally
   valid, pending and single-part (`keysend_create_valid`,
   `keysend_create_pending`, `keysend_create_single_part`);
2. a keysend satisfies the same `PaymentSession.preimageCommits` relation that
   wave-A gives for invoiced sessions, and an invoiced session and a keysend
   session over the same hash commit to the same preimage
   (`keysend_preimageCommits`, `keysend_invoice_commit_same_relation`);
3. the amount window and the CLTV floor are the same predicates as for an
   invoiced payment (`keysend_amountWindow_iff_invoice`,
   `keysend_cltvWindow_iff_invoice`, `keysend_accepts_iff_invoice`);
4. a keysend payment has no invoice: its origin tag is not the invoiced one,
   and `hasInvoice` is `false` exactly for keysend origins
   (`keysend_has_no_invoice`, `no_invoice_iff_keysend`);
5. keysend and invoiced sessions are never confused *once their origin tag is
   carried*: the tag is stable under `settle` and constructors are disjoint
   (`tagged_keysend_invoice_distinct`, `origin_tagged_kind`), while the raw
   wave-A `PaymentSession` deliberately forgets the origin
   (`paymentSession_forgets_origin`);
6. the preimage is revealed only on settlement: `revealedPreimage` is `none`
   while pending, `some p` after a successful settlement, and `none` after a
   failed one (`pending_not_revealed`, `settle_succeeded_reveals`,
   `settle_failed_not_revealed`, `reveal_requires_success`);
7. a failed keysend does not consume the preimage: `settle` preserves it and
   the session hash, validity survives failure, and a retry keeps the same
   preimage and hash (`settle_preimage`, `settle_session_paymentHash`,
   `settle_valid`, `retry_valid`, `failed_retry_hash_stable`);
8. under the (idealized) collision-freeness form of assumption C1 the preimage
   of a keysend is uniquely determined by its payment hash, and a keysend that
   reuses an invoiced payment hash must use that invoice's preimage
   (`keysend_preimage_unique`, `keysend_invoice_same_hash_same_preimage`).

`keysend_preimage_unique` and `keysend_invoice_same_hash_same_preimage` take
`CollisionFree sha256` explicitly: collision-freeness is the *idealized*
information-theoretic reading of C1 (`docs/ASSUMPTIONS.md` §1, C1), not a
theorem about a concrete SHA-256 implementation.  No computational
preimage-resistance claim is made anywhere; see "Not modelled".

BOLT sections.  Keysend is **not a BOLT**.  The anchors below are the BOLT
rules a keysend must still obey plus the LDK implementation that defines it.

* BOLT 2 `update_add_htlc` carries `amount_msat`, `payment_hash`,
  `cltv_expiry` for every payment, keysend included.
* BOLT 4 "Final Node": the amount window (`≥ expected`, `≤ 2·expected`), the
  CLTV floor, and the "same preimage for an HTLC set" rule.  BOLT 4 assumes
  `payment_secret` for `payment_data`; a keysend is the *spontaneous* path
  that carries no invoice and therefore no BOLT 11 secret (LDK makes the
  secret optional on its keysend path).
* BOLT 11 `p` tag: 32-byte SHA-256 payment hash whose preimage is proof of
  payment.  A keysend reuses exactly this hash/preimage construction without
  the invoice.
* The keysend TLV type `5482373484` and the "recipient checks
  `sha256(preimage) == payment_hash`" rule have **no specification line**:
  they are LDK-only, so their anchor is marked `UNANCHORED`.

BOLT line anchors (pinned BOLTs commit
`1aadb719b4007c4cea0ba6e36b08c4fb53788dee`).
* `refs/bolts/02-peer-protocol.md:2772-2790` `update_add_htlc`
  (`amount_msat`, `payment_hash`, `cltv_expiry`).
* `refs/bolts/04-onion-routing.md:352-359` an HTLC set shares one
  `payment_hash` / one preimage.
* `refs/bolts/04-onion-routing.md:1528-1550` final-node checks: payment hash
  known, amount at least expected, amount at most twice expected,
  `cltv_expiry` not unreasonably near.
* `refs/bolts/11-payment-encoding.md:133-145` `p` tag is the 256-bit SHA-256
  payment hash; its preimage is proof of payment.

rust-lightning anchors (LDK, commit
`fe4900930c6bd5786ec4203274d7cf312776a5a6`).
* `lightning-types/src/payment.rs:49` `PaymentPreimage([u8; 32])`.
* `lightning/src/ln/outbound_payment.rs:127` `Retryable` stores
  `keysend_preimage : Option<PaymentPreimage>` alongside `payment_hash`; the
  preimage is kept for retries and reloads.
* `lightning/src/ln/outbound_payment.rs:1447-1450` the sender generates the
  keysend preimage randomly and sets `payment_hash = Sha256(preimage)`.
* `lightning/src/ln/msgs.rs:3643` `UNANCHORED`: keysend preimage is written
  as custom TLV `5482373484`; no BOLT defines this type.
* `lightning/src/ln/onion_payment.rs:440-455` recipient check: compute
  `Sha256(preimage)`, reject with `InvalidKeysendPreimage` unless it equals
  `payment_hash`.
* `lightning/src/ln/channelmanager.rs:9339-9400` an accepted keysend becomes
  `OnionPayload::Spontaneous(keysend_preimage)` /
  `PaymentPurpose::SpontaneousPayment(keysend_preimage)`; the preimage is
  only surfaced to the claim path.
* `lightning/src/ln/channelmanager.rs:10210-10211` `claim_funds` derives
  `payment_hash` from the supplied `payment_preimage`.
* `lightning/src/events/mod.rs:1309-1317` `Event::PaymentSent` (the
  settlement receipt) is where the sender is given the preimage.
* `lightning/src/ln/outbound_payment.rs:2905` `keysend_preimage` is
  serialized as an optional field of `Retryable`, i.e. it is not dropped on
  failure.

Not modelled.
* Onion construction and TLV encoding.  The transport of `p` in TLV
  `5482373484` is cited from LDK but not formalized; this file starts from
  the preimage that the recipient already has.
* `ln`'s actual wire check `sha256(preimage) == payment_hash`
  (`onion_payment.rs:440-455`) is represented by the `Keysend.Valid`
  predicate, i.e. as a hypothesis on accepted payments.  There is no
  executable `sha256` in wave A: every hash statement is parameterized by
  `sha256 : Preimage → PaymentHash` and, where needed, by `CollisionFree`.
* Computational preimage resistance (assumption C1's second half).  It is
  not a `Prop` over a total function and is not stated as a theorem; the
  obligation `LN-CR-001` and `docs/ASSUMPTIONS.md` C1 own it.
* Channel-level HTLC states, onion errors, retry scheduling, fees, and the
  recipient's *policy* for accepting spontaneous payments.  In particular,
  the model does not say that a node accepts keysend; it says what holds
  *if* a keysend is accepted and settled.
* MPP for keysend: this model makes a keysend single-part
  (`keysend_create_single_part`).  Whether a real keysend may be split is a
  policy question outside the wave-A payment types.
* No BOLT line exists for keysend; `refs/bolts` contains no occurrence of
  "keysend" or `5482373484` at the pinned commit.  The `5482373484` TLV
  anchor is therefore explicitly `UNANCHORED`.
-/

namespace LnLean.Payment

set_option autoImplicit false

open LnLean

/-! ## Origin kinds -/

/-- The two payment origins this module distinguishes.  Keysend is the
`spontaneous` origin, invoiced is the BOLT 11 origin. -/
inductive PaymentOriginKind where
  | invoiced
  | keysend
deriving Repr, DecidableEq, BEq, Inhabited

namespace PaymentOriginKind

/-- The two origins are distinct constructors.  This is the structural fact
that lets a tagged session tell a keysend from an invoiced payment even when
their payment hashes coincide. -/
theorem keysend_ne_invoiced : PaymentOriginKind.keysend ≠ PaymentOriginKind.invoiced := by
  intro h
  cases h

end PaymentOriginKind

/-! ## The keysend record -/

/-- A keysend payment as the sender's outbound state sees it: the
sender-chosen preimage, the amount, the absolute CLTV expiry of the single
HTLC carrying it, the recipient's final-CLTV floor (keysend has no invoice to
carry one, so the sender uses the protocol default), and the payment session
keyed by the payment hash.

This mirrors LDK's `Retryable` (`payment_hash` + `keysend_preimage` +
`total_msat`); the session here is the wave-A `PaymentSession`. -/
structure Keysend where
  /-- The preimage chosen by the sender (LDK `keysend_preimage`). -/
  preimage : Preimage
  /-- The amount the sender intends to deliver. -/
  amount : Msat
  /-- Absolute CLTV expiry on the carrying HTLC. -/
  cltvExpiry : Height
  /-- Final-CLTV floor the sender applies (BOLT 4). -/
  minFinalCltvExpiry : Nat := DEFAULT_MIN_FINAL_CLTV
  /-- The payment session, whose `paymentHash` is `sha256 preimage`. -/
  session : PaymentSession
deriving Repr

namespace Keysend

/-- Structural validity of a keysend record *as accepted by the recipient*:
the session's payment hash is the SHA-256 of the carried preimage, and the
amount is inside the modelled money supply.  This is the proposition that the
LDK `InvalidKeysendPreimage` check establishes before the payment proceeds
(`lightning/src/ln/onion_payment.rs:440-455`). -/
structure Valid (k : Keysend) (sha256 : Preimage → PaymentHash) : Prop where
  /-- The recipient's check: `sha256(preimage) == payment_hash`. -/
  hashIsPreimage : k.session.paymentHash = sha256 k.preimage
  /-- BOLT 2 amounts are millisatoshis within the 21M BTC supply. -/
  amountBound : k.amount.val ≤ Msat.MAX.val

/-- Build the sender's keysend state from a preimage it chose.  The payment
hash is *defined* as `sha256 preimage`; nothing here consults an invoice. -/
def create (sha256 : Preimage → PaymentHash) (pre : Preimage) (amount : Msat)
    (cltvExpiry : Height) (minFinal : Nat := DEFAULT_MIN_FINAL_CLTV) : Keysend :=
  { preimage := pre
    amount := amount
    cltvExpiry := cltvExpiry
    minFinalCltvExpiry := minFinal
    session :=
      { paymentHash := sha256 pre
        target := amount
        parts := [{ index := 0, amount := amount, cltvExpiry := cltvExpiry }]
        state := .pending } }

/-- The freshly created keysend's payment hash is the SHA-256 of the
sender-chosen preimage.  Checked structurally (`rfl`). -/
theorem create_hash (sha256 : Preimage → PaymentHash) (pre : Preimage) (amount : Msat)
    (cltvExpiry : Height) (minFinal : Nat) :
    (create sha256 pre amount cltvExpiry minFinal).session.paymentHash =
      sha256 pre := rfl

/-- A freshly created keysend is pending.  Checked structurally (`rfl`). -/
theorem create_pending (sha256 : Preimage → PaymentHash) (pre : Preimage) (amount : Msat)
    (cltvExpiry : Height) (minFinal : Nat) :
    (create sha256 pre amount cltvExpiry minFinal).session.state = .pending := rfl

/-- A freshly created keysend carries exactly one part: the wave-A model has
no keysend MPP.  Checked structurally. -/
theorem create_single_part (sha256 : Preimage → PaymentHash) (pre : Preimage)
    (amount : Msat) (cltvExpiry : Height) (minFinal : Nat) :
    (create sha256 pre amount cltvExpiry minFinal).session.parts.length = 1 := rfl

/-- The preimage of a freshly created keysend is the sender's input.  Checked
structurally (`rfl`). -/
theorem create_preimage (sha256 : Preimage → PaymentHash) (pre : Preimage)
    (amount : Msat) (cltvExpiry : Height) (minFinal : Nat) :
    (create sha256 pre amount cltvExpiry minFinal).preimage = pre := rfl

/-- A created keysend is valid whenever its amount fits the money supply. -/
theorem create_valid (sha256 : Preimage → PaymentHash) (pre : Preimage)
    (amount : Msat) (cltvExpiry : Height) (minFinal : Nat)
    (ha : amount.val ≤ Msat.MAX.val) :
    (create sha256 pre amount cltvExpiry minFinal).Valid sha256 := by
  exact ⟨rfl, ha⟩

/-- Settlement of a keysend is the wave-A session settlement; the keysend
record's preimage, amount, expiry and CLTV floor are untouched. -/
def settle (k : Keysend) (outcome : PaymentState) : Keysend :=
  { k with session := PaymentSession.settle k.session outcome }

/-- A new attempt for the same payment: the outbound-side reset that LDK
performs on retry.  The preimage and payment hash are retained (LDK
`Retryable`), only the session state is reset to `pending`. -/
def retry (k : Keysend) : Keysend :=
  { k with session := { k.session with state := .pending } }

/-- Apply a list of settlement outcomes in order.  Used to state that no
sequence of failures can reveal the preimage. -/
def applyOutcomes (k : Keysend) : List PaymentState → Keysend
  | [] => k
  | o :: os => (k.settle o).applyOutcomes os

/-- The preimage is revealed exactly in the `succeeded` session state.  A
failed or pending session exposes nothing. -/
def revealedPreimage (k : Keysend) : Option Preimage :=
  if k.session.state = .succeeded then some k.preimage else none

/-- Settlement never changes the preimage. -/
theorem settle_preimage (k : Keysend) (outcome : PaymentState) :
    (k.settle outcome).preimage = k.preimage := rfl

/-- Settlement never changes the session's payment hash. -/
theorem settle_session_paymentHash (k : Keysend) (outcome : PaymentState) :
    (k.settle outcome).session.paymentHash = k.session.paymentHash := by
  unfold settle PaymentSession.settle
  by_cases h : k.session.state = .pending <;> simp [h]

/-- Settlement never changes the amount. -/
theorem settle_amount (k : Keysend) (outcome : PaymentState) :
    (k.settle outcome).amount = k.amount := rfl

/-- Settlement never changes the CLTV expiry or the final-CLTV floor. -/
theorem settle_cltvExpiry (k : Keysend) (outcome : PaymentState) :
    (k.settle outcome).cltvExpiry = k.cltvExpiry := rfl

/-- Validity is preserved by settlement: failing (or succeeding) a payment
does not invent a new preimage/hash pair. -/
theorem settle_valid (k : Keysend) (sha256 : Preimage → PaymentHash)
    (outcome : PaymentState) (h : k.Valid sha256) : (k.settle outcome).Valid sha256 := by
  refine ⟨?_, h.amountBound⟩
  rw [settle_session_paymentHash, settle_preimage]
  exact h.hashIsPreimage

/-- A retry keeps the preimage. -/
theorem retry_preimage (k : Keysend) : k.retry.preimage = k.preimage := rfl

/-- A retry keeps the payment hash. -/
theorem retry_session_paymentHash (k : Keysend) :
    k.retry.session.paymentHash = k.session.paymentHash := rfl

/-- A retry returns the session to `pending`. -/
theorem retry_pending (k : Keysend) : k.retry.session.state = .pending := rfl

/-- A retry of a valid keysend is still valid. -/
theorem retry_valid (k : Keysend) (sha256 : Preimage → PaymentHash)
    (h : k.Valid sha256) : k.retry.Valid sha256 := by
  refine ⟨?_, h.amountBound⟩
  simpa [retry] using h.hashIsPreimage

/-- After a failure, the retry still carries the original preimage and its
hash.  (This is the "does not consume the preimage" law on the outbound
record; the preimage itself is unchanged and never revealed by the failure.) -/
theorem failed_retry_hash_stable (k : Keysend) (sha256 : Preimage → PaymentHash)
    (h : k.Valid sha256) :
    (k.settle .failed).retry.session.paymentHash = sha256 k.preimage := by
  rw [retry_session_paymentHash, settle_session_paymentHash]
  exact h.hashIsPreimage

/-- A pending keysend reveals nothing. -/
theorem pending_not_revealed (k : Keysend) (h : k.session.state = .pending) :
    k.revealedPreimage = none := by
  unfold revealedPreimage
  simp [h]

/-- A successful settlement reveals exactly the sender's preimage. -/
theorem settle_succeeded_reveals (k : Keysend) (h : k.session.state = .pending) :
    (k.settle .succeeded).revealedPreimage = some k.preimage := by
  unfold revealedPreimage settle PaymentSession.settle
  simp [h]

/-- A failed settlement reveals nothing. -/
theorem settle_failed_not_revealed (k : Keysend) (h : k.session.state = .pending) :
    (k.settle .failed).revealedPreimage = none := by
  unfold revealedPreimage settle PaymentSession.settle
  simp [h]

/-- Revealing a preimage implies the session is in the `succeeded` state. -/
theorem reveal_requires_success (k : Keysend) (h : k.revealedPreimage.isSome) :
    k.session.state = .succeeded := by
  unfold revealedPreimage at h
  by_cases hs : k.session.state = .succeeded
  · exact hs
  · simp [hs] at h

/-- A terminal non-`pending` session is fixed by settlement; in particular a
failed keysend cannot later be turned into a success (so a failure can never
be used to reveal the preimage). -/
theorem settle_terminal_state (k : Keysend) (outcome : PaymentState)
    (h : k.session.state ≠ .pending) :
    (k.settle outcome).session.state = k.session.state := by
  unfold settle PaymentSession.settle
  simp [h]

/-- After a failure, a later successful settlement attempt changes nothing:
the session stays `failed` and the preimage is still not revealed. -/
theorem failed_then_succeeded_not_revealed (k : Keysend) (h : k.session.state = .pending) :
    ((k.settle .failed).settle .succeeded).revealedPreimage = none := by
  have hfail : (k.settle .failed).session.state = .failed := by
    unfold settle PaymentSession.settle
    simp [h]
  have hne : (k.settle .failed).session.state ≠ .pending := by
    rw [hfail]
    intro hp
    cases hp
  unfold revealedPreimage
  rw [settle_terminal_state (k.settle .failed) .succeeded hne, hfail]
  simp

/-- The preimage stored on a keysend record is never part of the session:
two keysends whose preimages hash to the same payment hash have identical
session states.  In other words, the payment session cannot leak the
preimage; only `revealedPreimage` and settlement expose it. -/
theorem session_does_not_store_preimage (sha256 : Preimage → PaymentHash)
    (p q : Preimage) (amount : Msat) (cltvExpiry : Height) (minFinal : Nat)
    (h : sha256 p = sha256 q) :
    (create sha256 p amount cltvExpiry minFinal).session =
      (create sha256 q amount cltvExpiry minFinal).session := by
  simp [create, h]

/-- A keysend satisfies the same conditional preimage-commitment relation
that wave-A defines for invoiced payment sessions. -/
theorem preimageCommits (sha256 : Preimage → PaymentHash) (k : Keysend)
    (h : k.Valid sha256) :
    PaymentSession.preimageCommits sha256 k.preimage k.session :=
  h.hashIsPreimage.symm

/-- An invoiced session and a keysend session over the same payment hash
commit to the same preimage.  This is the shared hash/preimage interface
between BOLT 11 and keysend. -/
theorem invoice_commit_same_relation (sha256 : Preimage → PaymentHash) {k : Keysend}
    (hk : k.Valid sha256) {i : Invoice} (hi : i.paymentHash = k.session.paymentHash) :
    PaymentSession.preimageCommits sha256 k.preimage k.session ∧
      Invoice.preimageCommits sha256 k.preimage i := by
  refine ⟨hk.hashIsPreimage.symm, ?_⟩
  unfold Invoice.preimageCommits
  rw [hi, hk.hashIsPreimage]

/-- Every settlement in a trace preserves the preimage. -/
theorem applyOutcomes_preimage (k : Keysend) (os : List PaymentState) :
    (k.applyOutcomes os).preimage = k.preimage := by
  induction os generalizing k with
  | nil => rfl
  | cons o os ih =>
    have hstep : (k.applyOutcomes (o :: os)).preimage =
        ((k.settle o).applyOutcomes os).preimage := rfl
    rw [hstep, ih (k.settle o), settle_preimage]

/-- Every settlement in a trace preserves the session's payment hash. -/
theorem applyOutcomes_paymentHash (k : Keysend) (os : List PaymentState) :
    (k.applyOutcomes os).session.paymentHash = k.session.paymentHash := by
  induction os generalizing k with
  | nil => rfl
  | cons o os ih =>
    have hstep : (k.applyOutcomes (o :: os)).session.paymentHash =
        ((k.settle o).applyOutcomes os).session.paymentHash := rfl
    rw [hstep, ih (k.settle o), settle_session_paymentHash]

/-- Any preimage ever revealed along a settlement trace is the sender's
original preimage. -/
theorem applyOutcomes_reveal_is_sender_preimage (k : Keysend) (os : List PaymentState)
    {p : Preimage} (h : (k.applyOutcomes os).revealedPreimage = some p) :
    p = k.preimage := by
  unfold revealedPreimage at h
  by_cases hs : (k.applyOutcomes os).session.state = .succeeded
  · simp [hs] at h
    rw [← h, applyOutcomes_preimage]
  · simp [hs] at h

/-- Two settlement traces of the same keysend can only ever reveal the same
preimage. -/
theorem traces_reveal_same_preimage (k : Keysend) (os₁ os₂ : List PaymentState)
    {p q : Preimage} (h₁ : (k.applyOutcomes os₁).revealedPreimage = some p)
    (h₂ : (k.applyOutcomes os₂).revealedPreimage = some q) : p = q := by
  rw [applyOutcomes_reveal_is_sender_preimage k os₁ h₁,
    applyOutcomes_reveal_is_sender_preimage k os₂ h₂]

/-- An all-failure trace from a pending keysend never reveals the preimage.
This is the trace-level form of "a failed keysend does not consume the
preimage": the record keeps it, and no observer learns it.  The remaining
step is the induction using `settle_terminal_state`: after the first failure
the session is terminal, so every later settlement is a no-op. -/
theorem all_failed_outcomes_never_reveal (k : Keysend) (os : List PaymentState)
    (hk : k.session.state = .pending) (hall : ∀ o ∈ os, o = .failed) :
    (k.applyOutcomes os).revealedPreimage = none := by
  -- OBLIGATION: LN-KS-001 A keysend whose every settlement outcome is a failure never reveals its preimage.
  sorry

end Keysend

/-! ## Hash assumption and preimage uniqueness -/

/-- The idealized collision-freeness reading of C1: the modelled `sha256`
maps distinct preimages to distinct payment hashes.  This is strictly stronger
than ordinary computational collision resistance; it is used only to state
what uniqueness would follow *if* C1 held in this idealized form. -/
def CollisionFree (sha256 : Preimage → PaymentHash) : Prop :=
  ∀ p q : Preimage, sha256 p = sha256 q → p = q

/-- Under collision-freeness, a payment hash determines the keysend preimage
uniquely. -/
theorem keysend_preimage_unique (sha256 : Preimage → PaymentHash)
    (hCF : CollisionFree sha256) {k₁ k₂ : Keysend}
    (h₁ : k₁.Valid sha256) (h₂ : k₂.Valid sha256)
    (h : k₁.session.paymentHash = k₂.session.paymentHash) :
    k₁.preimage = k₂.preimage := by
  apply hCF
  rw [← h₁.hashIsPreimage, ← h₂.hashIsPreimage]
  exact h

/-- Under collision-freeness, a keysend that reuses the payment hash of an
invoice must use that invoice's preimage.  This is why the LDK recipient
check makes a keysend-with-an-invoice's-hash useless as a probing device
(`lightning/src/ln/onion_payment.rs:440-455`). -/
theorem keysend_invoice_same_hash_same_preimage (sha256 : Preimage → PaymentHash)
    (hCF : CollisionFree sha256) {k : Keysend} (hk : k.Valid sha256) {i : Invoice}
    (hi : i.paymentHash = k.session.paymentHash) {p : Preimage}
    (hp : sha256 p = i.paymentHash) : p = k.preimage := by
  apply hCF
  rw [hp, hi, hk.hashIsPreimage]

/-! ## Amount and CLTV bounds shared with invoiced payments -/

/-- The BOLT 4 final-node amount window: pay at least the expected amount and
at most twice it.  This is the `some a` branch of `Invoice.amountSatisfies`,
factored out so a keysend (which has no invoice) can be compared with it. -/
def amountWindow (expected paid : Msat) : Prop :=
  expected.val ≤ paid.val ∧ paid.val ≤ 2 * expected.val

/-- The BOLT 4 final-node CLTV floor: the absolute expiry must be at least
`current_height + min_final_cltv_expiry_delta`. -/
def cltvWindow (currentHeight : Height) (minFinal : Nat) (expiry : Height) : Prop :=
  currentHeight + minFinal ≤ expiry

/-- A keysend with amount `k.amount` is subject to exactly the invoiced
amount window of an invoice that states the same amount. -/
theorem keysend_amountWindow_iff_invoice (i : Invoice) (k : Keysend) (paid : Msat)
    (h : i.amount = some k.amount) :
    i.amountSatisfies paid ↔ amountWindow k.amount paid := by
  simp [Invoice.amountSatisfies, amountWindow, h]

/-- The CLTV floor of a keysend is the invoiced floor with the same
`min_final_cltv_expiry_delta`. -/
theorem keysend_cltvWindow_iff_invoice (i : Invoice) (k : Keysend)
    (currentHeight : Height) (h : i.minFinalCltvExpiry = k.minFinalCltvExpiry) :
    cltvWindow currentHeight i.minFinalCltvExpiry k.cltvExpiry ↔
      cltvWindow currentHeight k.minFinalCltvExpiry k.cltvExpiry := by
  rw [h]

/-- A keysend is accepted under the same amount-and-CLTV conjunction that
governs an invoiced payment stating the same amount and CLTV delta.  This is
the precise sense in which "the amount and CLTV bounds are the same as an
invoiced payment". -/
theorem keysend_accepts_iff_invoice (i : Invoice) (k : Keysend)
    (currentHeight : Height) (paid : Msat) (hAmount : i.amount = some k.amount)
    (hCltv : i.minFinalCltvExpiry = k.minFinalCltvExpiry) :
    (i.amountSatisfies paid ∧ cltvWindow currentHeight i.minFinalCltvExpiry k.cltvExpiry) ↔
      (amountWindow k.amount paid ∧
        cltvWindow currentHeight k.minFinalCltvExpiry k.cltvExpiry) := by
  rw [keysend_amountWindow_iff_invoice i k paid hAmount, hCltv]

/-- The CLTV floor is monotone: lowering the required final-CLTV delta never
turns an acceptable expiry into an unacceptable one. -/
theorem cltvWindow_mono {currentHeight expiry : Height} {m m' : Nat}
    (hle : m' ≤ m) (h : cltvWindow currentHeight m expiry) :
    cltvWindow currentHeight m' expiry :=
  Nat.le_trans (Nat.add_le_add_left hle currentHeight) h

/-- A valid keysend's amount is inside the modelled 21M BTC supply. -/
theorem keysend_amount_le_max (k : Keysend) (sha256 : Preimage → PaymentHash)
    (h : k.Valid sha256) : k.amount.val ≤ Msat.MAX.val :=
  h.amountBound

/-! ## Origins: a keysend has no invoice -/

/-- An invoiced session built from the invoice's payment hash.  Its parts are
irrelevant to the origin question, so the wave-A empty part list is used; the
target falls back to zero for amount-less invoices. -/
def Invoice.paymentSession (i : Invoice) : PaymentSession :=
  { paymentHash := i.paymentHash
    target := i.amount.getD Msat.zero
    parts := []
    state := .pending }

/-- A session paired with the payment's origin.  The raw wave-A
`PaymentSession` records no origin, so proofs that must not confuse keysend
with invoiced carry this tag. -/
structure TaggedSession where
  kind : PaymentOriginKind
  session : PaymentSession
deriving Repr

namespace TaggedSession

/-- Settling a tagged session settles the underlying session and leaves the
tag untouched. -/
def settle (t : TaggedSession) (outcome : PaymentState) : TaggedSession :=
  { t with session := PaymentSession.settle t.session outcome }

/-- The origin tag is stable under settlement.  Checked structurally (`rfl`). -/
theorem settle_kind (t : TaggedSession) (outcome : PaymentState) :
    (t.settle outcome).kind = t.kind := rfl

end TaggedSession

/-- Project away the origin tag.  This is what the wave-A `PaymentSession`
type does implicitly, and it is exactly why a tag is needed for the
non-confusion theorem. -/
def forgetOrigin (t : TaggedSession) : PaymentSession := t.session

/-- A keysend-tagged session is never equal to an invoiced-tagged session,
whatever their payment hashes or other session fields. -/
theorem tagged_keysend_invoice_distinct (sk si : PaymentSession) :
    ({ kind := PaymentOriginKind.keysend, session := sk } : TaggedSession) ≠
      { kind := PaymentOriginKind.invoiced, session := si } := by
  intro h
  exact PaymentOriginKind.keysend_ne_invoiced (congrArg TaggedSession.kind h)

/-- A payment origin: either a BOLT 11 invoice or a keysend record. -/
inductive PaymentOrigin where
  | invoiced (invoice : Invoice)
  | keysend (payment : Keysend)
deriving Repr

namespace PaymentOrigin

/-- Whether the origin carries an invoice.  Keysend origins do not. -/
def hasInvoice : PaymentOrigin → Bool
  | .invoiced _ => true
  | .keysend _ => false

/-- The origin's kind tag. -/
def kind : PaymentOrigin → PaymentOriginKind
  | .invoiced _ => .invoiced
  | .keysend _ => .keysend

/-- The payment session associated with the origin. -/
def session : PaymentOrigin → PaymentSession
  | .invoiced i => Invoice.paymentSession i
  | .keysend k => k.session

/-- Tag an origin's session. -/
def tagged (o : PaymentOrigin) : TaggedSession :=
  ⟨o.kind, o.session⟩

end PaymentOrigin

/-- A keysend payment has no invoice: its `hasInvoice` is `false`.  Checked
structurally (`rfl`). -/
theorem keysend_has_no_invoice (k : Keysend) :
    (PaymentOrigin.keysend k).hasInvoice = false := rfl

/-- An invoiced payment has an invoice.  Checked structurally (`rfl`). -/
theorem invoiced_has_invoice (i : Invoice) :
    (PaymentOrigin.invoiced i).hasInvoice = true := rfl

/-- "No invoice" holds exactly for keysend origins. -/
theorem no_invoice_iff_keysend (o : PaymentOrigin) :
    o.hasInvoice = false ↔ ∃ k : Keysend, o = PaymentOrigin.keysend k := by
  constructor
  · cases o with
    | invoiced i =>
      intro h
      simp [PaymentOrigin.hasInvoice] at h
    | keysend k =>
      intro _
      exact ⟨k, rfl⟩
  · rintro ⟨k, rfl⟩
    rfl

/-- The tag attached to an origin is its kind. -/
theorem origin_tagged_kind (o : PaymentOrigin) : o.tagged.kind = o.kind := by
  cases o <;> rfl

/-- The wave-A session type forgets the origin: the same `PaymentSession`
value can be tagged as a keysend or as an invoiced payment.  Hence the
session state alone cannot distinguish the two, and the tag is not
redundant. -/
theorem paymentSession_forgets_origin (sk : PaymentSession) :
    ∃ t₁ t₂ : TaggedSession, t₁ ≠ t₂ ∧ forgetOrigin t₁ = forgetOrigin t₂ := by
  refine ⟨⟨.keysend, sk⟩, ⟨.invoiced, sk⟩, ?_, rfl⟩
  exact tagged_keysend_invoice_distinct sk sk

/-- Settlement of a tagged keysend never changes the tag, so a settled
keysend cannot become an invoiced payment in the session state. -/
theorem tagged_keysend_settle_kind (k : Keysend) (outcome : PaymentState) :
    ((PaymentOrigin.keysend k).tagged.settle outcome).kind =
      PaymentOriginKind.keysend := rfl

end LnLean.Payment
