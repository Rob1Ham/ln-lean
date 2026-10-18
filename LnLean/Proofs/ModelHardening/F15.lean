import LnLean.Payment.HTLC
import LnLean.Payment.Invoice
import LnLean.Proofs.Payment.KeysendProps

/-!
# LnLean.Proofs.ModelHardening.F15

Keysend preimage binding (**LN-PM-KS**, the proof-side companion of
`LN-PM-006`).

## What is missing in the wave-A keysend model

`LnLean.Payment.Keysend` stores the sender-chosen preimage on the outbound
record and has a `Valid` predicate that is *supposed* to stand for the
recipient's LDK check `sha256(preimage) == payment_hash`
(`lightning/src/ln/onion_payment.rs:440-455`).  The settlement transition
`Keysend.settle` and the observation `Keysend.revealedPreimage`, however, do
not consult `Valid`: a successfully settled record simply exposes whatever
`preimage` field it carries.  The connection between the exposed value and
the payment hash committed in the accepted `update_add_htlc` is therefore a
*hypothesis about acceptance*, not a consequence of settlement.  That is the
missing model field: the session records the hash and the terminal state but
does not record that the hash was checked against the preimage.

This module supplies the reusable invariant and states the precise result:

* `IsCommittedPreimage` / `SenderPreimageBinding`: the sender-chosen preimage
  hashes to the session's payment hash (the same relation as
  `PaymentSession.preimageCommits`, factored out and named).
* `AcceptedKeysend`: a keysend that passed the recipient's check and has not
  yet settled.
* Under acceptance, settlement success reveals exactly the sender's
  preimage, and that preimage is committed to by the *acceptance-time* payment
  hash.  The result is extended to every settlement outcome and to whole
  settlement traces, and is preserved by retry.
* Under the idealized collision-freeness form of C1, two accepted keysends
  sharing a payment hash can only reveal the same preimage.
* The unconditional form (no acceptance premise) is **false**.  It has been
  removed from the tree after `unchecked_record_counterexample` mechanized a
  record whose settlement reveals a preimage that is not the one committed by
  its payment hash.  The strongest true replacement is
  `bound_settle_reveals_committed`, which requires
  `SenderPreimageBinding` and the pending state.

No cryptographic hardness claim is made: `sha256` remains an arbitrary
parameter, and the concrete `exampleHash` used by the counterexample is only
a device for exhibiting the missing check.  The BOLT/LDK anchors and all
modelling exclusions are those documented in
`LnLean.Proofs.Payment.KeysendProps`; this file adds no new anchors.
-/

namespace LnLean.Proofs.ModelHardening.F15

open LnLean
open LnLean.Payment

set_option autoImplicit false

/-! ## The committed preimage and the binding predicate -/

/-- `p` is a preimage committed to by the payment hash `h` under the modelled
hash function.  This is the hash/preimage half of an accepted HTLC, with no
reference to a session, invoice, or settlement state. -/
def IsCommittedPreimage (sha256 : Preimage → PaymentHash) (h : PaymentHash)
    (p : Preimage) : Prop :=
  sha256 p = h

/-- The sender-preimage binding predicate for a keysend record: the preimage
carried on the record hashes to the payment hash of the record's session.
This is the property that the recipient's `InvalidKeysendPreimage` check
establishes at acceptance (LDK `onion_payment.rs:440-455`).  It deliberately
does **not** include the amount bound; that is a separate BOLT 2 check. -/
def SenderPreimageBinding (sha256 : Preimage → PaymentHash) (k : Keysend) : Prop :=
  IsCommittedPreimage sha256 k.session.paymentHash k.preimage

/-- A keysend accepted by the recipient: the preimage check passed and the
payment has not yet settled.  Acceptance is exactly the hypothesis that the
wave-A settlement transition does not itself enforce. -/
def AcceptedKeysend (sha256 : Preimage → PaymentHash) (k : Keysend) : Prop :=
  k.Valid sha256 ∧ k.session.state = .pending

/-- The binding predicate is the session-level preimage-commitment relation
of wave A, with the preimage projected out of the keysend record. -/
theorem binding_iff_preimageCommits (sha256 : Preimage → PaymentHash)
    (k : Keysend) :
    SenderPreimageBinding sha256 k ↔
      PaymentSession.preimageCommits sha256 k.preimage k.session :=
  Iff.rfl

/-- The binding predicate together with the BOLT 2 amount bound is exactly
the existing `Keysend.Valid` acceptance predicate.  This shows the new
predicate isolates the hash half of acceptance without weakening the model's
check. -/
theorem valid_iff_binding_and_amountBound (sha256 : Preimage → PaymentHash)
    (k : Keysend) :
    k.Valid sha256 ↔
      SenderPreimageBinding sha256 k ∧ k.amount.val ≤ Msat.MAX.val := by
  constructor
  · intro hv
    exact ⟨hv.hashIsPreimage.symm, hv.amountBound⟩
  · rintro ⟨hb, ha⟩
    exact ⟨hb.symm, ha⟩

/-- Acceptance decomposes into binding, the amount bound, and the pending
state.  Conversely those three facts re-establish acceptance. -/
theorem acceptedKeysend_iff (sha256 : Preimage → PaymentHash) (k : Keysend) :
    AcceptedKeysend sha256 k ↔
      SenderPreimageBinding sha256 k ∧ k.amount.val ≤ Msat.MAX.val ∧
        k.session.state = .pending := by
  constructor
  · rintro ⟨hv, hp⟩
    exact ⟨hv.hashIsPreimage.symm, hv.amountBound, hp⟩
  · rintro ⟨hb, ha, hp⟩
    exact ⟨⟨hb.symm, ha⟩, hp⟩

/-! ## Acceptance makes settlement reveal the committed preimage -/

/-- A preimage observed on a keysend record is the record's stored preimage.
`revealedPreimage` has no other source. -/
theorem reveal_is_stored_preimage (k : Keysend) {p : Preimage}
    (h : k.revealedPreimage = some p) : p = k.preimage := by
  unfold Keysend.revealedPreimage at h
  by_cases hs : k.session.state = .succeeded
  · simp [hs] at h
    exact h.symm
  · simp [hs] at h

/-- Settlement preserves the binding predicate: the preimage and the session's
payment hash are both untouched by `settle`. -/
theorem binding_preserved_by_settle (sha256 : Preimage → PaymentHash)
    (k : Keysend) (outcome : PaymentState)
    (h : SenderPreimageBinding sha256 k) :
    SenderPreimageBinding sha256 (k.settle outcome) := by
  unfold SenderPreimageBinding IsCommittedPreimage at h ⊢
  rwa [Keysend.settle_preimage, Keysend.settle_session_paymentHash]

/-- A retry preserves the binding predicate: LDK's `Retryable` keeps the
keysend preimage and the payment hash across attempts. -/
theorem binding_preserved_by_retry (sha256 : Preimage → PaymentHash)
    (k : Keysend) (h : SenderPreimageBinding sha256 k) :
    SenderPreimageBinding sha256 k.retry := by
  unfold SenderPreimageBinding IsCommittedPreimage at h ⊢
  rwa [Keysend.retry_preimage, Keysend.retry_session_paymentHash]

/-- **Main conditional theorem.**  An accepted keysend that settles
successfully exposes exactly the sender's preimage, and that preimage is
committed to by the payment hash that was accepted in the `update_add_htlc`.
The last conjunct restates the commitment against the settled session, where
it remains true because settlement leaves the hash unchanged. -/
theorem accepted_settle_reveals_committed
    (sha256 : Preimage → PaymentHash) (k : Keysend)
    (hacc : AcceptedKeysend sha256 k) :
    (k.settle .succeeded).revealedPreimage = some k.preimage ∧
      IsCommittedPreimage sha256 k.session.paymentHash k.preimage ∧
      PaymentSession.preimageCommits sha256 k.preimage
        (k.settle .succeeded).session := by
  obtain ⟨hv, hp⟩ := hacc
  refine ⟨Keysend.settle_succeeded_reveals k hp, hv.hashIsPreimage.symm, ?_⟩
  unfold PaymentSession.preimageCommits
  rw [Keysend.settle_session_paymentHash]
  exact hv.hashIsPreimage.symm

/-- **Strongest form of the main theorem.**  The commitment half of
acceptance is the only premise needed for settlement to reveal the committed
preimage; the BOLT 2 amount bound and even the structure of `Keysend.Valid`
play no role.  This is exactly the statement the recipient's preimage check
buys, with the acceptance certificate factored out. -/
theorem bound_settle_reveals_committed
    (sha256 : Preimage → PaymentHash) (k : Keysend)
    (hb : SenderPreimageBinding sha256 k)
    (hp : k.session.state = .pending) :
    (k.settle .succeeded).revealedPreimage = some k.preimage ∧
      IsCommittedPreimage sha256 k.session.paymentHash k.preimage ∧
      PaymentSession.preimageCommits sha256 k.preimage
        (k.settle .succeeded).session := by
  refine ⟨Keysend.settle_succeeded_reveals k hp, hb, ?_⟩
  unfold PaymentSession.preimageCommits
  rw [Keysend.settle_session_paymentHash]
  exact hb

/-- No settlement outcome can expose a preimage other than the accepted
one.  This covers the failed and terminal cases too: they expose nothing,
so the implication is vacuous for them. -/
theorem accepted_any_settlement_reveal_binds
    (sha256 : Preimage → PaymentHash) (k : Keysend) (hacc : k.Valid sha256)
    {outcome : PaymentState} {p : Preimage}
    (h : (k.settle outcome).revealedPreimage = some p) :
    p = k.preimage ∧ IsCommittedPreimage sha256 k.session.paymentHash p := by
  have hp : p = k.preimage := by
    have h' : p = (k.settle outcome).preimage :=
      reveal_is_stored_preimage (k.settle outcome) h
    simpa [Keysend.settle_preimage] using h'
  refine ⟨hp, ?_⟩
  unfold IsCommittedPreimage
  rw [hp]
  exact hacc.hashIsPreimage.symm

/-- The trace-level form: every preimage ever revealed along an arbitrary
settlement trace of an accepted keysend is the accepted preimage and commits
to the acceptance-time payment hash.  Note that no collision-freeness
assumption is needed for this direction; `sha256 p = h` is exactly what the
recipient checked. -/
theorem accepted_trace_reveal_binds
    (sha256 : Preimage → PaymentHash) (k : Keysend) (hacc : k.Valid sha256)
    (os : List PaymentState) {p : Preimage}
    (h : (k.applyOutcomes os).revealedPreimage = some p) :
    p = k.preimage ∧ IsCommittedPreimage sha256 k.session.paymentHash p := by
  have hp : p = k.preimage :=
    Keysend.applyOutcomes_reveal_is_sender_preimage k os h
  refine ⟨hp, ?_⟩
  unfold IsCommittedPreimage
  rw [hp]
  exact hacc.hashIsPreimage.symm

/-- Under the idealized collision-freeness form of C1, two accepted keysends
over the same payment hash cannot equivocate: any preimages their successful
settlements reveal are equal. -/
theorem accepted_same_hash_same_reveal
    (sha256 : Preimage → PaymentHash) (hCF : CollisionFree sha256)
    {k₁ k₂ : Keysend} (h₁ : k₁.Valid sha256) (h₂ : k₂.Valid sha256)
    (hh : k₁.session.paymentHash = k₂.session.paymentHash)
    {p q : Preimage}
    (hp : (k₁.settle .succeeded).revealedPreimage = some p)
    (hq : (k₂.settle .succeeded).revealedPreimage = some q) : p = q := by
  have hp' : p = k₁.preimage := by
    have h' : p = (k₁.settle .succeeded).preimage :=
      reveal_is_stored_preimage (k₁.settle .succeeded) hp
    simpa [Keysend.settle_preimage] using h'
  have hq' : q = k₂.preimage := by
    have h' : q = (k₂.settle .succeeded).preimage :=
      reveal_is_stored_preimage (k₂.settle .succeeded) hq
    simpa [Keysend.settle_preimage] using h'
  rw [hp', hq']
  exact keysend_preimage_unique sha256 hCF h₁ h₂ hh

/-! ## The unconditional statement is false: an unchecked record

The wave-A `Keysend` record is data, not a proof-carrying acceptance
certificate.  The following concrete record passes the settlement transition
without passing the preimage check, and settlement exposes its stored
preimage even though that preimage does not hash to the session's payment
hash.  The hash function below is an illustrative injection on bytes, not
SHA-256. -/

/-- An illustrative hash for the counterexample: it embeds the preimage bytes
in the payment hash.  It is used only to make the unchecked-record gap
concrete; it is not a model of SHA-256 and no cryptographic property is
claimed for it. -/
def exampleHash (p : Preimage) : PaymentHash :=
  ⟨p.bytes⟩

/-- The preimage stored on the unchecked record. -/
def forgedPreimage : Preimage :=
  ⟨ByteArray.mk #[1]⟩

/-- A preimage that genuinely commits to the unchecked record's payment hash.
It is the value the recipient would have accepted. -/
def committedPreimage : Preimage :=
  ⟨ByteArray.empty⟩

/-- A raw keysend record carrying the *wrong* preimage: its session is keyed
by `exampleHash committedPreimage`, but its `preimage` field is
`forgedPreimage`.  It is pending and can be settled successfully, because
`Keysend.settle` never consults `Valid`. -/
def uncheckedKeysend : Keysend :=
  { preimage := forgedPreimage
    amount := Msat.zero
    cltvExpiry := 0
    session :=
      { paymentHash := exampleHash committedPreimage
        target := Msat.zero
        parts := []
        state := .pending } }

/-- The forged and committed preimages are distinct (their byte lengths
differ). -/
theorem forged_ne_committed : forgedPreimage ≠ committedPreimage := by
  intro h
  have hs : forgedPreimage.bytes.size = committedPreimage.bytes.size :=
    congrArg (fun p : Preimage => p.bytes.size) h
  rw [show forgedPreimage.bytes.size = 1 from rfl,
    show committedPreimage.bytes.size = 0 from rfl] at hs
  exact Nat.one_ne_zero hs

/-- The forged preimage does not hash to the committed hash. -/
theorem forged_not_committed_hash :
    exampleHash forgedPreimage ≠ exampleHash committedPreimage := by
  intro h
  have hs : forgedPreimage.bytes.size = committedPreimage.bytes.size :=
    congrArg (fun x : PaymentHash => x.bytes.size) h
  rw [show forgedPreimage.bytes.size = 1 from rfl,
    show committedPreimage.bytes.size = 0 from rfl] at hs
  exact Nat.one_ne_zero hs

/-- The unchecked record fails the sender-preimage binding predicate. -/
theorem uncheckedKeysend_not_bound :
    ¬ SenderPreimageBinding exampleHash uncheckedKeysend := by
  intro h
  unfold SenderPreimageBinding IsCommittedPreimage at h
  simp [uncheckedKeysend] at h
  exact forged_not_committed_hash h

/-- The unchecked record fails `Keysend.Valid`: only the amount field is
within bounds, and the recipient's hash check is exactly what is missing.
This is why the acceptance hypothesis in the conditional theorem is not
redundant. -/
theorem uncheckedKeysend_not_valid :
    ¬ uncheckedKeysend.Valid exampleHash := by
  intro hv
  exact uncheckedKeysend_not_bound hv.hashIsPreimage.symm

/-- **Mechanized counterexample.**  There are a hash function, a pending
keysend, and a genuinely committed preimage such that the keysend's stored
preimage is *different* from the committed one, the keysend is not bound, yet
settlement succeeds and reveals the stored (uncommitted) preimage.  This is
the unchecked-record gap in the wave-A model. -/
theorem unchecked_record_counterexample :
    ∃ (sha256 : Preimage → PaymentHash) (k : Keysend) (pc : Preimage),
      sha256 pc = k.session.paymentHash ∧
        ¬ SenderPreimageBinding sha256 k ∧
        k.session.state = .pending ∧
        (k.settle .succeeded).revealedPreimage = some k.preimage ∧
        k.preimage ≠ pc ∧
        ¬ PaymentSession.preimageCommits sha256 k.preimage
          (k.settle .succeeded).session := by
  refine ⟨exampleHash, uncheckedKeysend, committedPreimage, rfl,
    uncheckedKeysend_not_bound, rfl, ?_, forged_ne_committed, ?_⟩
  · simp [uncheckedKeysend, Keysend.settle, PaymentSession.settle,
      Keysend.revealedPreimage]
  · simpa [PaymentSession.preimageCommits, uncheckedKeysend, Keysend.settle,
      PaymentSession.settle, exampleHash] using forged_not_committed_hash

-- REPAIRED: the refuted unconditional declaration
-- `unconditional_settle_reveals_committed` was removed.  The mechanized
-- counterexample `unchecked_record_counterexample` (above) witnesses the gap;
-- the strongest true replacement is `bound_settle_reveals_committed`, which
-- assumes `SenderPreimageBinding sha256 k` and `k.session.state = .pending`
-- (equivalently `accepted_settle_reveals_committed` under `AcceptedKeysend`).

end LnLean.Proofs.ModelHardening.F15
