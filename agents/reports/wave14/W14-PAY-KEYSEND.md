# W14-PAY-KEYSEND — guarded keysend retry (G10 / REV-03, retry half)

**Lane:** `W14-PAY-KEYSEND` (Wave 14, branch `wave-14/16`, base `a331b71`).
**Scope:** additive record-level repair of `Keysend.retry`; the old retry and
`retry_pending` are retained unchanged. This lane is the retry half of T6/G10
only; duplicate-store admission is `W14-PAY-STORE` (`PaymentAdmission.lean`).

## 1. Owned files

- `LnLean/Proofs/Wave14/KeysendRetryGuard.lean` (created)
- `agents/reports/wave14/W14-PAY-KEYSEND.md` (this report)

No other file was created, modified, or deleted. `KeysendProps.lean`,
`LnLean.lean`, `lakefile.lean`, `AxiomAudit.lean`, `Traceability.lean`,
`Obligations.lean`, `docs/`, the catalog, `vendor/`, `refs/`, scripts, tests,
and other lanes' files are untouched (`git status` shows only the new
untracked `LnLean/Proofs/Wave14/` directory and the pre-existing untracked
`agents/swarm/WAVE-14.md`).

## 2. Headline definitions and theorems

Namespace:
`LnLean.Proofs.Wave14.KeysendRetryGuard` (imports
`LnLean.Proofs.Payment.KeysendProps`).

### Definition

```lean
def retryIfNotSucceeded (k : Keysend) : Keysend :=
  if k.session.state = .succeeded then k
  else { k with session := { k.session with state := .pending } }
```

A succeeded session is returned unchanged (the whole record, not just the
state field). A failed session becomes retryable (`pending`). A pending session
is reset to `pending`, which is a no-op on the only non-terminal model state.

### Headline theorems (exact statements)

```lean
theorem retryIfNotSucceeded_succeeded (k : Keysend)
    (h : k.session.state = .succeeded) :
    retryIfNotSucceeded k = k

theorem retryIfNotSucceeded_failed (k : Keysend)
    (h : k.session.state = .failed) :
    (retryIfNotSucceeded k).session.state = .pending

theorem retryIfNotSucceeded_pending (k : Keysend)
    (h : k.session.state = .pending) :
    (retryIfNotSucceeded k).session.state = .pending

theorem legacy_retry_resets_succeeded (k : Keysend)
    (_h : k.session.state = .succeeded) :
    k.retry.session.state = .pending
```

`legacy_retry_resets_succeeded` is proved directly by the retained
`Keysend.retry_pending` (`KeysendProps.lean:300-301`); the old definition and
theorem were not replaced or weakened. (The state hypothesis is kept for
readability and audit against the succeeded case; it is not needed by the
unconditional old theorem, hence the `_h` binder.)

Supporting theorems:

```lean
theorem retryIfNotSucceeded_preimage (k : Keysend) :
    (retryIfNotSucceeded k).preimage = k.preimage

theorem retryIfNotSucceeded_session_paymentHash (k : Keysend) :
    (retryIfNotSucceeded k).session.paymentHash = k.session.paymentHash

theorem retryIfNotSucceeded_valid (k : Keysend) (sha256 : Preimage → PaymentHash)
    (h : k.Valid sha256) : (retryIfNotSucceeded k).Valid sha256

theorem legacy_and_guarded_agree_failed (k : Keysend)
    (h : k.session.state = .failed) :
    k.retry.session.state = (retryIfNotSucceeded k).session.state
```

## 3. Concrete non-vacuity witness

Defined in the module:

```lean
def witnessPreimage : Preimage :=
  ⟨ByteArray.mk (List.replicate 32 (7 : UInt8)).toArray⟩

def witnessSha256 (p : Preimage) : PaymentHash := ⟨p.bytes⟩
def witnessAmount : Msat := ⟨1000⟩

def witnessSucceeded : Keysend :=
  (Keysend.create witnessSha256 witnessPreimage witnessAmount 100 18).settle .succeeded

def witnessFailed : Keysend :=
  (Keysend.create witnessSha256 witnessPreimage witnessAmount 100 18).settle .failed
```

`witnessSha256` is only an inhabitation of `Preimage → PaymentHash` (byte
copy); it is not a cryptographic SHA-256 and no collision-freeness claim is
made.

The separating theorem is:

```lean
theorem witness_retry_diverges :
    witnessSucceeded.session.state = .succeeded ∧
    witnessSucceeded.retry.session.state = .pending ∧
    (retryIfNotSucceeded witnessSucceeded).session.state = .succeeded ∧
    retryIfNotSucceeded witnessSucceeded = witnessSucceeded
```

So on the same concrete succeeded keysend, the old `retry` yields `pending`
while the guarded retry returns the succeeded record unchanged. The other
branch is inhabited too:

```lean
theorem witnessFailed_state : witnessFailed.session.state = .failed
theorem witnessFailed_guarded_retry :
    (retryIfNotSucceeded witnessFailed).session.state = .pending
```

Both witnesses are evaluated by the kernel (`simp` on the concrete
definitions), not assumed.

## 4. Build

Command (exactly the scoped build under the shared lock):

```sh
cd /home/ubuntu/ln-lean-waveh
export PATH=/dev/shm/btc/elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
LEAN_NUM_THREADS=1 flock -w 3600 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Proofs.Wave14.KeysendRetryGuard
```

Result: `Build completed successfully (9 jobs).` The build log is
`/tmp/opencode/w14-keysend-build.log`.

No `sorry`, `axiom`, `admit`, `native_decide`, `unsafe`, or
`@[implemented_by]` occurs in the module. The only matches for those tokens
are the `#print axioms` command lines.

## 5. `#print axioms` output

Copied from the successful build transcript:

```text
'LnLean.Proofs.Wave14.KeysendRetryGuard.retryIfNotSucceeded_succeeded' depends on axioms: [propext]
'LnLean.Proofs.Wave14.KeysendRetryGuard.retryIfNotSucceeded_failed' depends on axioms: [propext]
'LnLean.Proofs.Wave14.KeysendRetryGuard.retryIfNotSucceeded_pending' depends on axioms: [propext]
'LnLean.Proofs.Wave14.KeysendRetryGuard.retryIfNotSucceeded_preimage' depends on axioms: [propext]
'LnLean.Proofs.Wave14.KeysendRetryGuard.retryIfNotSucceeded_session_paymentHash' depends on axioms: [propext]
'LnLean.Proofs.Wave14.KeysendRetryGuard.retryIfNotSucceeded_valid' depends on axioms: [propext]
'LnLean.Proofs.Wave14.KeysendRetryGuard.legacy_retry_resets_succeeded' does not depend on any axioms
'LnLean.Proofs.Wave14.KeysendRetryGuard.legacy_and_guarded_agree_failed' depends on axioms: [propext]
'LnLean.Proofs.Wave14.KeysendRetryGuard.witnessSucceeded_state' depends on axioms: [propext]
'LnLean.Proofs.Wave14.KeysendRetryGuard.witnessFailed_state' depends on axioms: [propext]
'LnLean.Proofs.Wave14.KeysendRetryGuard.witness_retry_diverges' depends on axioms: [propext]
'LnLean.Proofs.Wave14.KeysendRetryGuard.witnessFailed_guarded_retry' depends on axioms: [propext]
```

Every headline theorem uses only `propext` (or no axiom), within the allowed
set (`propext`, `Quot.sound`, `Classical.choice`, or none).

## 6. Gap closure and remaining boundary

**Closed/narrowed:** G10 in `R32-synthesis.md` §3 and the retry half of
`REV-03` in `docs/OPEN-ISSUES.md`. The review's exact complaint was that
`Keysend.retry` resets `succeeded` and that LDK Node rejects a duplicate
keysend while the stored payment is `Pending` or `Succeeded`
(`ldk-node/src/payment/spontaneous.rs:67-73`). This lane supplies an additive
transition with `succeeded` as a proved fixpoint, a proved successful-retry
separation on a concrete keysend, and a named retained theorem
(`legacy_retry_resets_succeeded`) recording that the old retry still resets a
success. `Keysend.retry`, `retry_pending`, `retry_valid`, and
`failed_retry_hash_stable` remain in place and typecheck.

**Remains external/narrow (stated in the module docstring):**

- No payment store, duplicate admission (`Pending`/`Succeeded` rejection),
  persistence, fsync ordering, crash recovery, or cross-process claim. That is
  `W14-PAY-STORE`'s `admitSend`; this module deliberately does not import it.
- `retryIfNotSucceeded` is not production-wired. The old `Keysend.retry`
  remains the only definition currently referenced; choosing a call-site
  replacement is an integrator/maintainer decision.
- The theorem is about the model's single non-terminal state (`pending`), not
  about LDK's internal `Retryable` bookkeeping or its exact reset for a
  `Failed` record.
- No claim that the wire or event layer prevents a second send; only the
  record-level transition is constrained.
- `witnessSha256` is an inhabiting function, not SHA-256; no C1 or
  collision-freeness claim is made here.

## 7. Shared-file changes the integrator must make

Not applied by this lane:

1. **Root import:** regenerate `LnLean.lean` with `scripts/regen-root.sh` so it
   imports `LnLean.Proofs.Wave14.KeysendRetryGuard` (do not hand-edit).
2. **Axiom audit (recommended):** add the three headline names to the
   `#print axioms` set and to `auditedTheorems` in
   `LnLean/Proofs/PhaseC3/AxiomAudit.lean`, or rely on the in-module prints
   above. This lane already emits `#print axioms` for every declaration it
   adds, so a registry entry is optional unless the wave-wide coverage gate
   requires every target to be registered.
3. **Catalog/docs (optional, wording only):** if the integrator wants a
   catalog row for the retry guard, point it at
   `LnLean.Proofs.Wave14.KeysendRetryGuard.retryIfNotSucceeded_succeeded` /
   `..._failed` and describe it as an additive record-level guard, not as a
   production replacement. Update `REV-03` wording to say the retry half is
   narrowed and the store half is in `W14-PAY-STORE`. Do not delete
   `retry_pending` or claim `Keysend.retry` is fixed in place.

## 8. Confirmation

No shared file and no other lane's file was edited. Only the two owned paths
above were written. The old `Keysend.retry` and `retry_pending` are preserved
untouched; this change is additive.
