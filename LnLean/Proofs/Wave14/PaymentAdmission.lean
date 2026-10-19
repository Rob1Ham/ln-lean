import LnLean.Proofs.Payment.KeysendProps

/-!
# LnLean.Proofs.Wave14.PaymentAdmission

English claim.  LDK Node refuses to start a *new send* for a payment id whose
stored status is `Pending` or `Succeeded`; a `Failed` record, or no record at
all, is admitted (a retry after an explicit failure is a new send).  This
module adds a finite, purely functional payment store that states exactly that
admission rule over the existing wave-A payment status type, and proves the
duplicate-send consequences for two keysends that share one payment hash.

## What is new, and what is deliberately unchanged

* `PaymentStatus` is an `abbrev` for the existing `LnLean.Payment.PaymentState`
  (`pending | succeeded | failed`).  No state type, session record, keysend
  record, settlement function, or existing theorem is redefined.
* `PaymentStore` is a finite list of `(PaymentHash, PaymentStatus)` pairs.
  `PaymentStore.lookup` returns the first matching entry, so
  `PaymentStore.record` prepends and therefore shadows an older entry for the
  same hash.  There is no invariant that keys are unique; lookup order is the
  model's "newest record wins" rule.
* `admitSend` is the LDK admission guard as a `Bool`: `false` exactly for a
  `Pending` or `Succeeded` entry, `true` for `Failed` or absent.
* The old `Keysend.retry` and its theorem `Keysend.retry_pending` are **not**
  changed or replaced.  `Keysend.retry` still resets *any* state, including
  `succeeded`, to `pending`; that divergence from LDK is retained and
  re-witnessed below (`legacy_retry_still_resets_succeeded`).  The new store
  guard is an additional admission layer, not a redefinition of the retry
  record.

## Anchors

LDK Node, pinned at `fa123fed131e27ecc420b77fa7086fcf1ddaebb8` (the review pin
of R12/R32):

* `ldk-node/src/payment/spontaneous.rs:62-73`: the keysend payment id is the
  preimage's payment hash, and the guard rejects `Pending` or `Succeeded` with
  `Error::DuplicatePayment` ("must not send duplicate payments").
* `ldk-node/src/payment/bolt11.rs:206-215`: the same `Pending || Succeeded`
  guard for an invoiced send.
* `ldk-node/src/payment/store.rs:371-378`: `PaymentStatus` is exactly
  `Pending | Succeeded | Failed`.  The status is a stored, persisted value;
  `Failed` is deliberately not part of the duplicate check.

BOLT sections.  There is no BOLT admission rule for a sender-side duplicate:
BOLT 11 defines the payment hash, and BOLT 4's final-node text says a receiver
that has already paid a hash "MAY treat it as unknown. MAY succeed in accepting
it" (`refs/bolts/04-onion-routing.md:1531-1535`).  The rule proved here is the
LDK Node implementation contract, not a BOLT theorem.

## Boundary (do not overclaim)

This is a **single-process, in-memory** model.  `PaymentStore` is a list value;
there is no file, database, log, or network.  In particular this module does
**not** prove, assume, or model:

* persistence or durability of the store across a restart;
* fsync/append ordering between a send and its record;
* crash atomicity, recovery, or replay of a partially written record;
* admission across two processes, two threads, or two store replicas;
* the read-check-send-insert race (LDK performs `get` and later `insert` in
  separate steps; here `record` is a pure function of the admitted state);
* that a `Pending` record eventually becomes terminal, or that a `Failed`
  record is itself accurate.

`admitSend` prevents a duplicate *admission* only for the single list value
supplied to it.  The theorem `two_identical_keysends_not_both_succeed` must be
read in exactly that scope: the second keysend is not admitted by a store that
already records the shared hash as `Pending` or `Succeeded`, so it cannot reach
a settled state through this store API.  It does not say anything about a
second process, a stale in-memory cache, or an already-corrupt store.
-/

namespace LnLean.Proofs.Wave14.PaymentAdmission

set_option autoImplicit false

open LnLean
open LnLean.Payment

/-! ## Payment status and the finite store -/

/-- The payment status used by the store.  This is the existing wave-A
`PaymentState` (`pending | succeeded | failed`), matching LDK Node's
`PaymentStatus` variants; it is an alias so that no existing payment or
keysend declaration changes meaning. -/
abbrev PaymentStatus := PaymentState

/-- A finite, in-memory payment store: a list of `(payment hash, status)`
entries.  Later `record` calls are prepended, and `lookup` returns the first
match, so the newest entry shadows an older one for the same hash. -/
structure PaymentStore where
  entries : List (PaymentHash × PaymentStatus)
deriving Repr, DecidableEq

namespace PaymentStore

/-- Linear lookup over the entry list.  The first entry with the queried hash
wins; this is the model's newest-record-wins rule. -/
def find? : List (PaymentHash × PaymentStatus) → PaymentHash → Option PaymentStatus
  | [], _ => none
  | (h, s) :: rest, ph => if h = ph then some s else find? rest ph

/-- Look up the stored status for a payment hash. -/
def lookup (st : PaymentStore) (ph : PaymentHash) : Option PaymentStatus :=
  find? st.entries ph

/-- The empty store: every hash is absent. -/
def empty : PaymentStore := ⟨[]⟩

/-- Record a status for a payment hash.  The new entry is prepended; any older
entry with the same hash remains in the list but is shadowed by `lookup`. -/
def record (st : PaymentStore) (ph : PaymentHash) (status : PaymentStatus) :
    PaymentStore :=
  ⟨(ph, status) :: st.entries⟩

@[simp] theorem lookup_empty (ph : PaymentHash) : empty.lookup ph = none := rfl

@[simp] theorem lookup_record_same (st : PaymentStore) (ph : PaymentHash)
    (status : PaymentStatus) : (st.record ph status).lookup ph = some status := by
  simp [record, lookup, find?]

/-- Recording a *different* hash does not change the lookup of the queried
hash. -/
theorem lookup_record_other (st : PaymentStore) (ph q : PaymentHash)
    (status : PaymentStatus) (h : ph ≠ q) :
    (st.record ph status).lookup q = st.lookup q := by
  simp [record, lookup, find?, h]

/-- A newer record for the same hash shadows the older one. -/
theorem lookup_record_shadows (st : PaymentStore) (ph : PaymentHash)
    (old new : PaymentStatus) :
    ((st.record ph old).record ph new).lookup ph = some new := by
  simp [record, lookup, find?]

end PaymentStore

/-! ## Admission: reject Pending and Succeeded, allow Failed/absent -/

/-- LDK Node's duplicate-send admission rule: a payment hash is *not* admitted
when the store records it as `Pending` or `Succeeded`; it is admitted when the
store records `Failed` or has no entry.  This is a pure `Bool` so it can be
used as an executable guard. -/
def admitSend (st : PaymentStore) (ph : PaymentHash) : Bool :=
  match st.lookup ph with
  | some .pending => false
  | some .succeeded => false
  | _ => true

/-- A `Pending` entry rejects the duplicate send. -/
theorem duplicate_send_rejected_pending (st : PaymentStore) (ph : PaymentHash)
    (h : st.lookup ph = some .pending) : admitSend st ph = false := by
  simp [admitSend, h]

/-- A `Succeeded` entry rejects the duplicate send. -/
theorem duplicate_send_rejected_succeeded (st : PaymentStore) (ph : PaymentHash)
    (h : st.lookup ph = some .succeeded) : admitSend st ph = false := by
  simp [admitSend, h]

/-- The combined duplicate-send theorem: `Pending` or `Succeeded` is rejected.
This is the headline admission statement; it deliberately does **not** say
"terminal is rejected", because `Failed` is admitted. -/
theorem duplicate_send_rejected (st : PaymentStore) (ph : PaymentHash)
    (h : st.lookup ph = some .pending ∨ st.lookup ph = some .succeeded) :
    admitSend st ph = false := by
  rcases h with h | h
  · exact duplicate_send_rejected_pending st ph h
  · exact duplicate_send_rejected_succeeded st ph h

/-- A `Failed` entry is retryable: the new send is admitted. -/
theorem failed_send_admitted (st : PaymentStore) (ph : PaymentHash)
    (h : st.lookup ph = some .failed) : admitSend st ph = true := by
  simp [admitSend, h]

/-- An absent hash is admitted: a fresh send has no stored status. -/
theorem absent_send_admitted (st : PaymentStore) (ph : PaymentHash)
    (h : st.lookup ph = none) : admitSend st ph = true := by
  simp [admitSend, h]

/-- Exact characterization of a rejected admission: only `Pending` and
`Succeeded` are rejected. -/
theorem admitSend_eq_false_iff (st : PaymentStore) (ph : PaymentHash) :
    admitSend st ph = false ↔
      st.lookup ph = some .pending ∨ st.lookup ph = some .succeeded := by
  unfold admitSend
  cases h : st.lookup ph with
  | none => simp
  | some s => cases s <;> simp

/-- Exact characterization of an admitted send: only `Failed` and absent are
admitted. -/
theorem admitSend_eq_true_iff (st : PaymentStore) (ph : PaymentHash) :
    admitSend st ph = true ↔
      st.lookup ph = none ∨ st.lookup ph = some .failed := by
  unfold admitSend
  cases h : st.lookup ph with
  | none => simp
  | some s => cases s <;> simp

/-! ## Two identical keysends -/

/-- If the store records the shared payment hash as `Pending` or `Succeeded`,
then a second keysend with that same hash is not admitted.  Consequently the
two identical keysends cannot both be sent, and hence cannot both succeed
through this store API.

The theorem is about the supplied store value only.  It is not a cross-process
or crash-recovery theorem; see the module boundary. -/
theorem two_identical_keysends_not_both_succeed
    (st : PaymentStore) (k₁ k₂ : Keysend)
    (hHash : k₁.session.paymentHash = k₂.session.paymentHash)
    (hStatus : st.lookup k₁.session.paymentHash = some .pending ∨
      st.lookup k₁.session.paymentHash = some .succeeded) :
    admitSend st k₂.session.paymentHash = false := by
  rw [← hHash]
  exact duplicate_send_rejected st k₁.session.paymentHash hStatus

/-- Concrete form for the first keysend still `Pending`: recording its session
state in the store makes the second identical keysend inadmissible. -/
theorem two_identical_keysends_not_both_succeed_pending
    (k₁ k₂ : Keysend)
    (hHash : k₁.session.paymentHash = k₂.session.paymentHash)
    (h₁ : k₁.session.state = .pending) :
    admitSend
        (PaymentStore.empty.record k₁.session.paymentHash k₁.session.state)
        k₂.session.paymentHash = false := by
  apply two_identical_keysends_not_both_succeed
  · exact hHash
  · left
    rw [h₁]
    exact PaymentStore.lookup_record_same _ _ _

/-- Concrete form for the first keysend already `Succeeded`: recording its
session state in the store makes the second identical keysend inadmissible. -/
theorem two_identical_keysends_not_both_succeed_succeeded
    (k₁ k₂ : Keysend)
    (hHash : k₁.session.paymentHash = k₂.session.paymentHash)
    (h₁ : k₁.session.state = .succeeded) :
    admitSend
        (PaymentStore.empty.record k₁.session.paymentHash k₁.session.state)
        k₂.session.paymentHash = false := by
  apply two_identical_keysends_not_both_succeed
  · exact hHash
  · right
    rw [h₁]
    exact PaymentStore.lookup_record_same _ _ _

/-! ## Concrete non-vacuity witnesses

R32 §5.2 requires explicit `Pending`, `Succeeded`, and `Failed` store entries.
The witnesses below are concrete 32-byte hashes and concrete keysend records;
none of the admission theorems is vacuous. -/

/-- A concrete 32-byte byte string, used for both sample hashes and preimages. -/
def bytes32 (b : UInt8) : ByteArray :=
  ByteArray.mk (List.replicate 32 b).toArray

/-- A concrete payment hash. -/
def sampleHash : PaymentHash := ⟨bytes32 7⟩

/-- A concrete preimage (not required to hash to `sampleHash`; the sample hash
function is constant, which is enough for the admission witnesses). -/
def samplePreimage : Preimage := ⟨bytes32 9⟩

/-- A sample hash function for the concrete keysend records.  It is a constant
function, so it is not collision-free; collision-freeness is irrelevant to the
store-admission statements. -/
def sampleSha256 (_ : Preimage) : PaymentHash := sampleHash

/-- A concrete, freshly created keysend: pending, 1000 msat, CLTV 18. -/
def sampleKeysend : Keysend :=
  Keysend.create sampleSha256 samplePreimage ⟨1000⟩ 18

/-- The same keysend after a successful settlement. -/
def sampleKeysendSucceeded : Keysend := sampleKeysend.settle .succeeded

/-- The same keysend after a failed settlement. -/
def sampleKeysendFailed : Keysend := sampleKeysend.settle .failed

theorem sampleKeysend_pending : sampleKeysend.session.state = .pending := rfl

theorem sampleKeysendSucceeded_state :
    sampleKeysendSucceeded.session.state = .succeeded := by
  unfold sampleKeysendSucceeded Keysend.settle PaymentSession.settle
  simp [sampleKeysend_pending]

theorem sampleKeysendFailed_state :
    sampleKeysendFailed.session.state = .failed := by
  unfold sampleKeysendFailed Keysend.settle PaymentSession.settle
  simp [sampleKeysend_pending]

/-- Store with a concrete `Pending` entry. -/
def sampleStorePending : PaymentStore :=
  PaymentStore.empty.record sampleHash .pending

/-- Store with a concrete `Succeeded` entry. -/
def sampleStoreSucceeded : PaymentStore :=
  PaymentStore.empty.record sampleHash .succeeded

/-- Store with a concrete `Failed` entry. -/
def sampleStoreFailed : PaymentStore :=
  PaymentStore.empty.record sampleHash .failed

theorem witness_pending_lookup :
    sampleStorePending.lookup sampleHash = some .pending :=
  PaymentStore.lookup_record_same _ _ _

theorem witness_succeeded_lookup :
    sampleStoreSucceeded.lookup sampleHash = some .succeeded :=
  PaymentStore.lookup_record_same _ _ _

theorem witness_failed_lookup :
    sampleStoreFailed.lookup sampleHash = some .failed :=
  PaymentStore.lookup_record_same _ _ _

/-- The concrete `Pending` entry is rejected. -/
theorem witness_pending_rejected :
    admitSend sampleStorePending sampleHash = false :=
  duplicate_send_rejected_pending _ _ witness_pending_lookup

/-- The concrete `Succeeded` entry is rejected. -/
theorem witness_succeeded_rejected :
    admitSend sampleStoreSucceeded sampleHash = false :=
  duplicate_send_rejected_succeeded _ _ witness_succeeded_lookup

/-- The concrete `Failed` entry is admitted (retryable). -/
theorem witness_failed_admitted :
    admitSend sampleStoreFailed sampleHash = true :=
  failed_send_admitted _ _ witness_failed_lookup

/-- The empty store admits a fresh hash. -/
theorem witness_absent_admitted :
    admitSend PaymentStore.empty sampleHash = true :=
  absent_send_admitted _ _ (PaymentStore.lookup_empty sampleHash)

/-- A fresh keysend is admitted by the empty store. -/
theorem witness_fresh_keysend_admitted :
    admitSend PaymentStore.empty sampleKeysend.session.paymentHash = true := by
  apply absent_send_admitted
  exact PaymentStore.lookup_empty _

/-- Concrete duplicate keysend witness with a `Pending` first record. -/
theorem witness_two_identical_keysends_pending :
    admitSend
        (PaymentStore.empty.record sampleKeysend.session.paymentHash
          sampleKeysend.session.state)
        sampleKeysend.session.paymentHash = false :=
  two_identical_keysends_not_both_succeed_pending _ _ rfl sampleKeysend_pending

/-- Concrete duplicate keysend witness with a `Succeeded` first record. -/
theorem witness_two_identical_keysends_succeeded :
    admitSend
        (PaymentStore.empty.record sampleKeysendSucceeded.session.paymentHash
          sampleKeysendSucceeded.session.state)
        sampleKeysendSucceeded.session.paymentHash = false :=
  two_identical_keysends_not_both_succeed_succeeded _ _ rfl
    sampleKeysendSucceeded_state

/-! ## Retained divergence: the old keysend retry record -/

/-- The unchanged legacy `Keysend.retry` still resets a succeeded session to
`pending`.  This is the retained divergence from LDK's duplicate guard; it is
re-witnessed here rather than replaced or deleted.  The new `admitSend` gate is
what rejects the duplicate send; `Keysend.retry` itself is untouched. -/
theorem legacy_retry_still_resets_succeeded :
    sampleKeysendSucceeded.retry.session.state = .pending :=
  Keysend.retry_pending _

/-- Contrast retained in one statement: the legacy retry record resets a
success to `pending`, while the store admits no duplicate for a `Succeeded`
hash. -/
theorem legacy_retry_diverges_from_admission :
    sampleKeysendSucceeded.retry.session.state = .pending ∧
      admitSend sampleStoreSucceeded sampleHash = false :=
  ⟨legacy_retry_still_resets_succeeded, witness_succeeded_rejected⟩

/-! ## Axiom audit -/

#print axioms duplicate_send_rejected
#print axioms duplicate_send_rejected_pending
#print axioms duplicate_send_rejected_succeeded
#print axioms failed_send_admitted
#print axioms absent_send_admitted
#print axioms admitSend_eq_false_iff
#print axioms admitSend_eq_true_iff
#print axioms two_identical_keysends_not_both_succeed
#print axioms two_identical_keysends_not_both_succeed_pending
#print axioms two_identical_keysends_not_both_succeed_succeeded
#print axioms witness_pending_rejected
#print axioms witness_succeeded_rejected
#print axioms witness_failed_admitted
#print axioms witness_absent_admitted
#print axioms witness_two_identical_keysends_pending
#print axioms witness_two_identical_keysends_succeeded
#print axioms legacy_retry_diverges_from_admission

end LnLean.Proofs.Wave14.PaymentAdmission
