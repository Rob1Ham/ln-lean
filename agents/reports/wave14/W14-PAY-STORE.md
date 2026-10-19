# W14-PAY-STORE — finite payment store and duplicate-send admission (T6/G11)

**Lane:** `W14-PAY-STORE` (Wave 14, branch `wave-14/16`, base `a331b71`).
**Scope:** additive T6/G11 store half: a finite in-memory payment store, a
lookup function, and the LDK Node duplicate-send admission rule (`Pending` and
`Succeeded` reject; `Failed` and absent admit), plus the identical-keysend
consequence. The guarded-retry half of T6/G10 is the separate lane
`W14-PAY-KEYSEND` (`KeysendRetryGuard.lean`); this module deliberately does not
import it.

## 1. Owned files

- `LnLean/Proofs/Wave14/PaymentAdmission.lean` (created)
- `agents/reports/wave14/W14-PAY-STORE.md` (this report)

No other file was created, modified, or deleted. `LnLean.lean`,
`lakefile.lean`, `scripts/check-final.py`, `LnLean/Proofs/PhaseC3/AxiomAudit.lean`,
`LnLean/Proofs/Traceability.lean`, `LnLean/Proofs/Obligations.lean`, `docs/`,
the catalog, `vendor/`, `refs/`, the existing payment/keysend modules, and
other lanes' files are untouched.

## 2. Definitions and exact headline statements

Namespace:
`LnLean.Proofs.Wave14.PaymentAdmission` (imports
`LnLean.Proofs.Payment.KeysendProps`).

### Definitions

```lean
abbrev PaymentStatus := PaymentState
-- PaymentState is the existing wave-A type: pending | succeeded | failed.
-- The LDK Node PaymentStatus enum has exactly the same three variants.

structure PaymentStore where
  entries : List (PaymentHash × PaymentStatus)
deriving Repr, DecidableEq

namespace PaymentStore

def find? : List (PaymentHash × PaymentStatus) → PaymentHash → Option PaymentStatus
  | [], _ => none
  | (h, s) :: rest, ph => if h = ph then some s else find? rest ph

def lookup (st : PaymentStore) (ph : PaymentHash) : Option PaymentStatus :=
  find? st.entries ph

def empty : PaymentStore := ⟨[]⟩

def record (st : PaymentStore) (ph : PaymentHash) (status : PaymentStatus) :
    PaymentStore :=
  ⟨(ph, status) :: st.entries⟩

end PaymentStore

def admitSend (st : PaymentStore) (ph : PaymentHash) : Bool :=
  match st.lookup ph with
  | some .pending => false
  | some .succeeded => false
  | _ => true
```

`record` prepends, so the newest entry shadows an older entry with the same
hash. There is no unique-key invariant: `lookup` is explicitly first-match /
newest-record-wins, and `lookup_record_shadows` proves that behaviour.

### Headline theorems (10)

```lean
theorem duplicate_send_rejected (st : PaymentStore) (ph : PaymentHash)
    (h : st.lookup ph = some .pending ∨ st.lookup ph = some .succeeded) :
    admitSend st ph = false

theorem duplicate_send_rejected_pending (st : PaymentStore) (ph : PaymentHash)
    (h : st.lookup ph = some .pending) : admitSend st ph = false

theorem duplicate_send_rejected_succeeded (st : PaymentStore) (ph : PaymentHash)
    (h : st.lookup ph = some .succeeded) : admitSend st ph = false

theorem failed_send_admitted (st : PaymentStore) (ph : PaymentHash)
    (h : st.lookup ph = some .failed) : admitSend st ph = true

theorem absent_send_admitted (st : PaymentStore) (ph : PaymentHash)
    (h : st.lookup ph = none) : admitSend st ph = true

theorem admitSend_eq_false_iff (st : PaymentStore) (ph : PaymentHash) :
    admitSend st ph = false ↔
      st.lookup ph = some .pending ∨ st.lookup ph = some .succeeded

theorem admitSend_eq_true_iff (st : PaymentStore) (ph : PaymentHash) :
    admitSend st ph = true ↔
      st.lookup ph = none ∨ st.lookup ph = some .failed

theorem two_identical_keysends_not_both_succeed
    (st : PaymentStore) (k₁ k₂ : Keysend)
    (hHash : k₁.session.paymentHash = k₂.session.paymentHash)
    (hStatus : st.lookup k₁.session.paymentHash = some .pending ∨
      st.lookup k₁.session.paymentHash = some .succeeded) :
    admitSend st k₂.session.paymentHash = false

theorem two_identical_keysends_not_both_succeed_pending
    (k₁ k₂ : Keysend)
    (hHash : k₁.session.paymentHash = k₂.session.paymentHash)
    (h₁ : k₁.session.state = .pending) :
    admitSend
        (PaymentStore.empty.record k₁.session.paymentHash k₁.session.state)
        k₂.session.paymentHash = false

theorem two_identical_keysends_not_both_succeed_succeeded
    (k₁ k₂ : Keysend)
    (hHash : k₁.session.paymentHash = k₂.session.paymentHash)
    (h₁ : k₁.session.state = .succeeded) :
    admitSend
        (PaymentStore.empty.record k₁.session.paymentHash k₁.session.state)
        k₂.session.paymentHash = false
```

The two exact-characterization theorems are the strongest form of the rule:
`admitSend` is `false` **exactly** for `Pending`/`Succeeded`, and `true`
**exactly** for `Failed`/absent. They also make explicit that "terminal" is
*not* the guard: `Failed` is terminal in `PaymentState.isTerminal` and yet is
admitted, matching LDK.

### Supporting lookup theorems

```lean
theorem PaymentStore.lookup_empty (ph : PaymentHash) :
    PaymentStore.empty.lookup ph = none

theorem PaymentStore.lookup_record_same (st : PaymentStore) (ph : PaymentHash)
    (status : PaymentStatus) :
    (st.record ph status).lookup ph = some status

theorem PaymentStore.lookup_record_other (st : PaymentStore) (ph q : PaymentHash)
    (status : PaymentStatus) (h : ph ≠ q) :
    (st.record ph status).lookup q = st.lookup q

theorem PaymentStore.lookup_record_shadows (st : PaymentStore) (ph : PaymentHash)
    (old new : PaymentStatus) :
    ((st.record ph old).record ph new).lookup ph = some new
```

### Retained old record (not replaced)

```lean
theorem legacy_retry_still_resets_succeeded :
    sampleKeysendSucceeded.retry.session.state = .pending
  -- proof: Keysend.retry_pending (unchanged, KeysendProps.lean:300-301)

theorem legacy_retry_diverges_from_admission :
    sampleKeysendSucceeded.retry.session.state = .pending ∧
      admitSend sampleStoreSucceeded sampleHash = false
```

`Keysend.retry`, `Keysend.retry_pending`, `PaymentSession.settle`, and every
existing payment/keysend declaration are unchanged. The new module only adds
a store layer; it does not redefine the old retry record or hide its
divergence from LDK.

## 3. Concrete non-vacuity witnesses

R32 §5.2 requires explicit `Pending`, `Succeeded`, and `Failed` store entries.
The module supplies all three as concrete values (a 32-byte hash of repeated
`0x07`) rather than quantified hypotheses:

```lean
def bytes32 (b : UInt8) : ByteArray :=
  ByteArray.mk (List.replicate 32 b).toArray

def sampleHash : PaymentHash := ⟨bytes32 7⟩

def sampleStorePending : PaymentStore :=
  PaymentStore.empty.record sampleHash .pending
def sampleStoreSucceeded : PaymentStore :=
  PaymentStore.empty.record sampleHash .succeeded
def sampleStoreFailed : PaymentStore :=
  PaymentStore.empty.record sampleHash .failed
```

Each store is inhabited and each status is exhibited by a kernel-checked
equality:

```lean
theorem witness_pending_lookup :
    sampleStorePending.lookup sampleHash = some .pending
theorem witness_succeeded_lookup :
    sampleStoreSucceeded.lookup sampleHash = some .succeeded
theorem witness_failed_lookup :
    sampleStoreFailed.lookup sampleHash = some .failed
```

The admission witnesses use the corresponding headline theorem, not a
hypothesis restatement:

```lean
theorem witness_pending_rejected :
    admitSend sampleStorePending sampleHash = false
  -- duplicate_send_rejected_pending + witness_pending_lookup

theorem witness_succeeded_rejected :
    admitSend sampleStoreSucceeded sampleHash = false
  -- duplicate_send_rejected_succeeded + witness_succeeded_lookup

theorem witness_failed_admitted :
    admitSend sampleStoreFailed sampleHash = true
  -- failed_send_admitted + witness_failed_lookup

theorem witness_absent_admitted :
    admitSend PaymentStore.empty sampleHash = true
  -- absent_send_admitted + lookup_empty
```

A concrete keysend (`sampleHash`, 1000 msat, CLTV 18) is created with
`Keysend.create`, then settled into the other two states:
`sampleKeysend_pending`, `sampleKeysendSucceeded_state`, and
`sampleKeysendFailed_state` are all proved. The identical-keysend witnesses
are therefore over actual `Keysend` records, not an empty type:

```lean
theorem witness_two_identical_keysends_pending :
    admitSend
        (PaymentStore.empty.record sampleKeysend.session.paymentHash
          sampleKeysend.session.state)
        sampleKeysend.session.paymentHash = false

theorem witness_two_identical_keysends_succeeded :
    admitSend
        (PaymentStore.empty.record sampleKeysendSucceeded.session.paymentHash
          sampleKeysendSucceeded.session.state)
        sampleKeysendSucceeded.session.paymentHash = false
```

`sampleSha256` is a constant inhabiting function, not SHA-256; it is used only
to build concrete keysend records, and no collision-freeness or cryptographic
claim is made.

## 4. Build

Command (exactly the scoped module build under the shared lock):

```sh
cd /home/ubuntu/ln-lean-waveh
export PATH=/dev/shm/btc/elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
LEAN_NUM_THREADS=1 flock -w 3600 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Proofs.Wave14.PaymentAdmission
```

Result: `Build completed successfully (9 jobs).` (no warnings, no `sorry`).
Full transcript: `/tmp/opencode/w14-pay-store-build.log`.

## 5. `#print axioms` output

Copied from the successful build transcript:

```text
'LnLean.Proofs.Wave14.PaymentAdmission.duplicate_send_rejected' depends on axioms: [propext, Quot.sound]
'LnLean.Proofs.Wave14.PaymentAdmission.duplicate_send_rejected_pending' depends on axioms: [propext, Quot.sound]
'LnLean.Proofs.Wave14.PaymentAdmission.duplicate_send_rejected_succeeded' depends on axioms: [propext, Quot.sound]
'LnLean.Proofs.Wave14.PaymentAdmission.failed_send_admitted' depends on axioms: [propext, Quot.sound]
'LnLean.Proofs.Wave14.PaymentAdmission.absent_send_admitted' depends on axioms: [propext, Quot.sound]
'LnLean.Proofs.Wave14.PaymentAdmission.admitSend_eq_false_iff' depends on axioms: [propext, Quot.sound]
'LnLean.Proofs.Wave14.PaymentAdmission.admitSend_eq_true_iff' depends on axioms: [propext, Quot.sound]
'LnLean.Proofs.Wave14.PaymentAdmission.two_identical_keysends_not_both_succeed' depends on axioms: [propext, Quot.sound]
'LnLean.Proofs.Wave14.PaymentAdmission.two_identical_keysends_not_both_succeed_pending' depends on axioms: [propext, Quot.sound]
'LnLean.Proofs.Wave14.PaymentAdmission.two_identical_keysends_not_both_succeed_succeeded' depends on axioms: [propext, Quot.sound]
'LnLean.Proofs.Wave14.PaymentAdmission.witness_pending_rejected' depends on axioms: [propext, Quot.sound]
'LnLean.Proofs.Wave14.PaymentAdmission.witness_succeeded_rejected' depends on axioms: [propext, Quot.sound]
'LnLean.Proofs.Wave14.PaymentAdmission.witness_failed_admitted' depends on axioms: [propext, Quot.sound]
'LnLean.Proofs.Wave14.PaymentAdmission.witness_absent_admitted' depends on axioms: [propext, Quot.sound]
'LnLean.Proofs.Wave14.PaymentAdmission.witness_two_identical_keysends_pending' depends on axioms: [propext, Quot.sound]
'LnLean.Proofs.Wave14.PaymentAdmission.witness_two_identical_keysends_succeeded' depends on axioms: [propext, Quot.sound]
'LnLean.Proofs.Wave14.PaymentAdmission.legacy_retry_diverges_from_admission' depends on axioms: [propext, Quot.sound]
```

Every headline theorem uses only `propext` and `Quot.sound`, inside the
allowed set (`propext`, `Quot.sound`, `Classical.choice`, or none). No
`Classical.choice` is needed. `#print axioms` lines are emitted in the module
for every headline and every witness.

## 6. Gap closure and remaining boundary

**Closed/narrowed:** G11 in `R32-synthesis.md` §3 and the store half of
`REV-03` in `docs/OPEN-ISSUES.md`. The review records that no payment store,
no payment-id admission predicate, and no duplicate-admission theorem existed:
"two `create` calls with the same preimage/hash both settle `succeeded`"
(R32 G11). This lane supplies:

- a finite `PaymentStore` keyed by `PaymentHash`, with executable `lookup`;
- `admitSend` matching LDK Node's `Pending || Succeeded` guard
  (`ldk-node/src/payment/spontaneous.rs:67-73`; `bolt11.rs:206-215`), with
  `Failed` deliberately admitted (`store.rs:371-378`);
- a proof that `Failed` is *not* rejected even though it is a terminal
  `PaymentState`, so the model is not accidentally the stronger and wrong
  "terminal implies reject" rule;
- `two_identical_keysends_not_both_succeed` for two keysends with one payment
  hash when the store records the hash as `Pending` or `Succeeded`, with
  concrete `Pending` and `Succeeded` corollaries.

**Remains external/narrow** (stated explicitly in the module docstring):

- This is a **single-process, in-memory** model. `PaymentStore` is a list
  value; there is no file, database, event log, or socket.
- Persistence, durability across restart, fsync/append ordering, crash
  atomicity, recovery, and replay of a partially written record are **not**
  modelled or proved.
- Admission across two processes, two threads, or two store replicas is **not**
  modelled. `admitSend` constrains exactly the supplied list value.
- The read-check-send-insert race is **not** modelled: LDK performs `get`
  (`bolt11.rs:209`) and later `insert` (`:260-266`) as separate steps; here
  `record` is a pure function of the admitted store.
- No claim that a `Pending` record eventually becomes terminal, that a
  `Failed` record is accurate, or that a stale in-memory cache cannot re-admit
  a duplicate.
- The keysend record's legacy `retry` divergence is retained; fixing the retry
  transition is `W14-PAY-KEYSEND`'s additive `retryIfNotSucceeded`, not this
  module.
- The rule is the LDK Node implementation contract, not a BOLT theorem. BOLT 4
  permits a final node to treat an already-paid hash as unknown or to accept
  it again (`refs/bolts/04-onion-routing.md:1531-1535`); this module does not
  claim receiver-side duplicate rejection.
- No cryptographic hash property is used; `sampleSha256` is only an
  inhabitation for the concrete keysend witnesses.

## 7. Shared-file changes the integrator must make

Not applied by this lane:

1. **Root import:** regenerate `LnLean.lean` with `scripts/regen-root.sh` so it
   imports `LnLean.Proofs.Wave14.PaymentAdmission`. Do not hand-edit the root.
2. **Axiom audit:** add the 10 headline theorem names (and, if the coverage
   gate requires every declaration, the witness/retention names) to
   `#print axioms` and `auditedTheorems` in
   `LnLean/Proofs/PhaseC3/AxiomAudit.lean`. The module already prints every
   declaration it adds, so this is a registry/print-set reconciliation, not a
   new proof obligation.
3. **Catalog/docs (optional, wording only):** if a catalog row is added, point
   it at `PaymentAdmission.duplicate_send_rejected` and
   `PaymentAdmission.two_identical_keysends_not_both_succeed`, and describe
   them as a **finite, single-process, in-memory admission model**. Update
   `docs/OPEN-ISSUES.md` `REV-03` to say the store half is narrowed by
   `W14-PAY-STORE` while persistence/crash/cross-process admission remain
   external. Do not delete `Keysend.retry_pending` and do not describe
   `admitSend` as a persistence or crash-safety theorem.

## 8. Confirmation

No shared file and no other lane's file was edited. My writes were only to
`LnLean/Proofs/Wave14/PaymentAdmission.lean` and this report. No `git add`,
`git commit`, `git push`, or branch switch was run. The existing
`Keysend.retry`, `retry_pending`, `PaymentSession.settle`, and all payment
status/hash/session declarations are preserved unchanged; this change is
additive.
