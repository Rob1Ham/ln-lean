# R12 — Payment lifecycle, retries, MPP, keysend, and probing
**Status:** read-only review
**Pins:** LDK Node `fa123fed131e27ecc420b77fa7086fcf1ddaebb8`, LDK Server `c17dc11dde38f88c53457039ddf30c6b90a63ba2`

Review tip: `f7f062817c185cd70004bb26c652deb99c6fd4bd` (`repair/integrated`).
No Lean, catalog, test, vendor, or other-lane file was modified. Commands are
listed in §7; no `lake build`, no `cargo test`, no network access.

---

## 1. Scope and current Lean surface

### 1.1 Catalog rows that touch this surface

All seven payment rows are `proved` (`docs/THEOREM-INDEX.md:74-80`,
`docs/TRACEABILITY.md:53-59`). None of them is a payment-lifecycle theorem in
the sense of LDK Node's send/store/retry behaviour: they are invoice-wire,
hash/secret-binding, exact-sum, and preimage-binding facts.

| Row | Named target(s) | Module | What the target actually states | Lifecycle scope |
|---|---|---|---|---|
| `LN-PM-001` | `Invoice.consistent_hash`, `Invoice.consistent_amount`, `InvoiceWireTargets.parse_print_paymentHash`, `wire_paymentHash_binding`, `preimage_unique_of_injective`, `preimage_determines_hash` | `LnLean/Security/Invariants.lean:401,406`; `LnLean/Proofs/Payment/InvoiceWireTargets.lean` | A decoded invoice carries the supplied hash/amount; the field-list codec preserves them; preimage uniqueness is conditional on hash injectivity | Invoice construction only; no send attempt |
| `LN-PM-002` | `Invoice.signature_valid`; `signature_not_payment`; `signature_only_separates_verify_from_payment` | `LnLean/Payment/Invoice.lean:267`; `InvoiceWireTargets` | Invoice signature verifies against the payee key; it does **not** prove payment | Authentication only |
| `LN-PM-003` | `Invoice.payment_secret_match`; `paymentSecret_eq_iff_bytes`; `wire_paymentSecret_binding` | `LnLean/Payment/Invoice.lean`; `InvoiceWireTargets` | The final payload's secret matches the invoice's secret field | Wire/secret binding only |
| `LN-PM-004` | `MppPayment.settle_requires_sum` | `LnLean/Security/Invariants.lean:440-454` | If the standalone `MppPayment.settle` returns `some`, `partsSum = total` | Exact-sum acceptance on a carrier unrelated to `PaymentSession` |
| `LN-PM-005` | `MPP.running_total_bound` | `LnLean/Payment/MPP.lean:176-180` | For a plan with exact `mppComplete`, every prefix sums to at most `target` | Arithmetic corollary, not an admission rule and not a reachable-state invariant |
| `LN-PM-006` | `Keysend.preimage_binding` | `LnLean/Proofs/WaveE/E31.lean:198-205` | Under hash injectivity/`IsCommittedPreimage`, a keysend's revealed preimage commits to the session hash | Receiver-side acceptance only; no sender store, no retry |
| `LN-PM-007` | `parseFields_printFields`, `parse_print`, `print_injective`, `duplicateHash_parse_none`, `decodeHop_encodeHop`, `encodeHop_size` | `LnLean/Proofs/Payment/InvoiceWireTargets.lean` | Pre-bech32 field-list codec, round-trip, duplicate-field rejection | Invoice wire only |

The catalog's green state therefore does **not** imply that "duplicate payment",
"retry after success", "late failure after success", "payment-store
persistence", "MPP overpay", or "probing" are modelled. Those behaviours are
simply outside the rows.

### 1.2 Carriers actually present in the Lean tree

There are three *disconnected* payment carriers, plus a hardening layer:

1. **Attempt/session layer** — `LnLean/Payment/HTLC.lean`
   - `PaymentState` has exactly `pending | succeeded | failed`
     (`HTLC.lean:65-69`).
   - `isTerminal` returns `True` for both `succeeded` and `failed`
     (`HTLC.lean:74-77`).
   - `PaymentPart` carries `index`, `amount`, `cltvExpiry`, `state`; it has
     **no `htlc_id`** (`HTLC.lean:93-99`).
   - `PaymentSession` carries `paymentHash`, `target`, `parts`, `state`
     (`HTLC.lean:102-108`).
   - `settle` is absorbing: if the session is not `pending` it is a no-op
     (`HTLC.lean:136-138`), mechanized as `settle_terminal`
     (`HTLC.lean:148-152`).
   - `preimageCommits` is the conditional hash relation
     (`HTLC.lean:128-130`).
2. **Plan layer** — `LnLean/Payment/MPP.lean`
   - `MPPPlan` has one `paymentHash`, one `paymentSecret`, one `target`, a
     `List MPPPart`, and a minimum final CLTV delta (`MPP.lean:92-100`).
   - `mppComplete` is *non-empty and exact sum*
     (`MPP.lean:144-146`), explicitly documented as the conservative scaffold
     for BOLT 4's `sum ≥ total_msat`.
   - `mppAtomic` is a predicate over an outcome list positionally aligned with
     `plan.parts` (`MPP.lean:227-231`); `mppAtomic_no_mixed`
     (`Laws.lean:210-222`) excludes one success and one failure in the *same
     supplied list*, not in a reachable state.
3. **Standalone invariant layer** — `LnLean/Security/Invariants.lean`
   - `MppPayment` is `parts : List Msat`, `total : Msat`, `accepted : Bool`
     (`Invariants.lean:425-430`); `partsSum` (`:432-434`), `SumOK`
     (`:436-438`), `settle` (`:440-446`), `settle_requires_sum` (`:448-454`).
   - This carrier has no hash, secret, channel, CLTV, or `htlc_id`, and **no
     bridge theorem connects it to `PaymentSession` or `MPPPlan`**.
4. **Hardening / counterexample layer**
   - `F13` (invoice/hash boundaries), `F14` (MPP running-total guard and the
     over-total counterexample), `F15` (keysend sender-preimage binding and the
     unchecked-record counterexample).
   - `F14.RunningTotalBound` (`F14.lean:49-50`) and `PartFits`
     (`F14.lean:55-56`) are admission arithmetic, but they are not used by a
     payment collector transition.
   - `F14.mppComplete_of_runningTotalBound_of_ge` (`F14.lean:132-139`) is the
     only existing bridge from `≥` to exact `mppComplete`; it is a lemma about
     a plan, not a settlement rule.
   - `F15.SenderPreimageBinding` / `AcceptedKeysend` (`F15.lean:73-80`);
     `binding_preserved_by_retry` (`F15.lean:139-146`); and the unconditional
     `unchecked_record_counterexample` (`F15.lean:317-334`).
5. **Keysend record** — `LnLean/Proofs/Payment/KeysendProps.lean`
   - `Keysend` wraps a `PaymentSession` (`KeysendProps.lean:173-184`).
   - `create` builds a one-part pending session with `paymentHash = sha256 pre`
     (`KeysendProps.lean:201-212`).
   - `settle` delegates to `PaymentSession.settle` (`:246-248`).
   - **`retry` resets any session to `pending`, unconditionally**
     (`:252-255`); `retry_pending` proves exactly that for *every* `k`
     (`:300-301`).

### 1.3 What is absent (searched, not assumed)

- **No payment store.** There is no declaration named `PaymentStore`,
  `payment_store`, `PaymentDetails`, `PaymentRecord`, or `RetryPolicy` in any
  `.lean` file under `LnLean/` (`rg`, §7). The existing `Keysend.retry` is a
  pure record reset, not a store admission function.
- **No payment persistence.** `LnLean/Proofs/PhaseC3/PersistenceRecovery.lean`
  models only channel commitment counters, the live HTLC set, and
  `channel_ready` (module header `:5-27`). Its only `paymentHash` occurrence
  (`:292`) is a field of a channel HTLC record, not a payment-store entry.
- **No probing model.** `rg -ni 'probe' LnLean --include=*.lean` finds only
  Bitcoin script fixtures in `LnLean/Proofs/WaveH/H04.lean:48-93`
  (`probePrevout`, `probeTable`, `probeUtxo`). There is no `probe`, `prober`,
  `ProbeBudget`, or `locked_msat` declaration in `LnLean/Payment/**` or
  `LnLean/Proofs/Payment/**`.
- **No event/reconciliation layer.** No `PaymentSent`, `PaymentFailed`,
  `PaymentClaimable`, `applyEvent`, or `late` transition exists in Lean.
- **No duplicate-by-hash admission predicate.** Two independently constructed
  `PaymentSession`s with the same `paymentHash` have no relation and can each
  be settled (`HTLC.lean:102-138`); nothing prevents it.
- **No MPP `htlc_id`, per-part `total_msat`, or set-level same-total check.**
  `MPPPart` has channel/amount/CLTV only (`MPP.lean:83-88`); `MPPPlan` has one
  `target`.
- **No equivalence or bridge between the three carriers**, and no theorem that
  `MppPayment.settle` and `PaymentSession.settle` agree.

---

## 2. LDK datapoints (with `file:line`)

Citations are from the pinned read-only clones. Paths below are relative to
`/tmp/opencode/ldk-refs/ldk-node` unless prefixed with `ldk-server/`.

| # | Behaviour | Datapoint | Citation |
|---|---|---|---|
| D1 | BOLT 11 duplicate-payment guard: look up the `PaymentId`, reject if status is `Pending` **or** `Succeeded` | `PaymentId(invoice.payment_hash().0)`; `payment_store.get`; `if Pending or Succeeded { DuplicatePayment }` | `src/payment/bolt11.rs:208-215` |
| D2 | The guard and the send are **not atomic**: lookup → `pay_for_bolt11_invoice` → `payment_store.insert(Pending)` | `get` at `:209`; send at `:236-241`; `insert` at `:260-266` | `src/payment/bolt11.rs:209,236-266` |
| D3 | Spontaneous/keysend id is the hash of the sender-chosen preimage | `PaymentPreimage(...)`; `PaymentHash::from(preimage)`; `PaymentId(payment_hash.0)` | `src/payment/spontaneous.rs:62-65` |
| D4 | Spontaneous/keysend duplicate guard is the same Pending/Succeeded rule, then send, then insert | guard `:67-73`; `send_spontaneous_payment` `:109-115`; `insert` `:129-133` | `src/payment/spontaneous.rs:67-73,109-133` |
| D5 | Payment status is a stored 3-variant value, persisted with the record | `PaymentDetails.status`; `PaymentStatus { Pending, Succeeded, Failed }`; TLV field `(10, status, required)` | `src/payment/store.rs:87-89,140-164,401-408` |
| D6 | Status update is a **plain overwrite**, not a transition relation | `if let Some(status) = update.status { update_if_necessary!(self.status, status); }`; macro assigns whenever different | `src/payment/store.rs:241-248,335-337` |
| D7 | `PaymentSent` writes `Succeeded` unconditionally; a missing record is **not** reconstructed on this path | `status: Some(PaymentStatus::Succeeded)` at `:1550-1556`; `update` matched `Ok(_)` at `:1560-1564`, while the inbound claim path inserts on `NotFound` at `:1484-1498` | `src/event.rs:1550-1564,1484-1498` |
| D8 | Late `PaymentFailed` after `Succeeded` is explicitly ignored for outbound Lightning | `ignore_late_failure` guard on `direction == Outbound && kind.is_lightning_payment() && status == Succeeded` | `src/event.rs:1612-1622` |
| D9 | Retry is an internal `Retry::Timeout(10s)`, not a public retry API; a new call is a new admission decision | `LDK_PAYMENT_RETRY_TIMEOUT = 10s`; `Retry::Timeout(LDK_PAYMENT_RETRY_TIMEOUT)` | `src/config.rs:171-172`; `src/payment/bolt11.rs:218-220`; `src/payment/spontaneous.rs:109-114` |
| D10 | The channel manager has a second duplicate check; a send failure inserts a `Failed` record | `RetryableSendFailure::DuplicatePayment => Err(Error::DuplicatePayment)`; other failures `insert(PaymentStatus::Failed)` | `src/payment/bolt11.rs:274-295`; `src/payment/spontaneous.rs:135-150` |
| D11 | Underpaying MPP is a deliberate LDK extension: declare the invoice total, send less; requires a permissive receiver | doc `:362-375`; `declared_total_mpp_value_msat_override = Some(invoice_amount_msat)` `:401-405`; gRPC doc `:510-520` | `src/payment/bolt11.rs:362-405`; `ldk-server/ldk-server-grpc/src/api.rs:510-537` |
| D12 | Probing budget: `locked_msat` is derived from recent pending probe payments, including pending fees; the loop skips a probe when `locked + amount > max_locked_msat` | `locked_msat` `:830-844`; budget check `:883-888`; handlers only log `:847-863` | `src/probing.rs:830-888` |
| D13 | Probe budget and persistence are tested, including restart | `exhausted_probe_budget_blocks_new_probes` at `:428`, cap loop `:461-480`; `probing_budget_restored_after_node_restart` at `:305-329` | `tests/probing_tests.rs:305-329,428-480` |
| D14 | Duplicate BOLT 11 retry is a regression-tested contract, not merely a comment | `retrying the same BOLT11 invoice must return DuplicatePayment`; `Err(NodeError::DuplicatePayment)` | `tests/integration_tests_rust.rs:5339-5354` |
| D15 | BOLT 4 completes an HTLC set when the set total is **≥** `total_msat`; `total_msat` must be the same across the set | "if the total `amt_to_forward` ... is equal to or greater than `total_msat`: SHOULD fulfill"; "SHOULD fail the entire HTLC set if `total_msat` is not the same" | `refs/bolts/04-onion-routing.md:383,397-410` |
| D16 | BOLT 4 does not forbid accepting a duplicate payment hash at the final node | "if the payment hash has already been paid: MAY treat ... unknown. MAY succeed in accepting" | `refs/bolts/04-onion-routing.md:1531-1535` |
| D17 | Inbound manual claim is an explicit follow-up to `PaymentClaimable`; replayed claim events are idempotent | doc `:240-250`; `Updated`/`Unchanged => "idempotent update ... replayed event"`; `NotFound => insert` | `ldk-server/ldk-server-grpc/src/api.rs:240-250`; `src/event.rs:1484-1498` |
| D18 | Unified payments abort on a duplicate sub-payment rather than falling back | `DuplicatePayment` handlers `:331-333,362-364` | `src/payment/unified.rs:331-364` |

Two precision notes that matter for target fidelity:

- The node-level guard reads a **persistent** store: `PaymentStore` is a
  `DataStore<PaymentDetails, ..., KeepLeastRecentlyUsed>` and its LRU policy
  reads through to the KV store on a miss (`src/types.rs:339`;
  `src/data_store.rs:110-115,207-235`). Eviction from the in-memory cache is
  therefore not itself a duplicate-guard hole.
- The guard's status test is **only** `Pending || Succeeded`
  (`bolt11.rs:209-214`). `Failed` is admitted deliberately. Any Lean theorem
  of the form "terminal ⇒ reject" is therefore wrong for LDK, because
  `PaymentState.isTerminal` includes `failed` (`HTLC.lean:74-77`).

---

## 3. Gap matrix

Legend: **C** = covered faithfully, **P** = partially covered, **M** = missing,
**X** = contradicted (a counterexample exists), **E** = unmodelled/external.

| Behavior | Lean status | LDK evidence | Gap / counterexample | Priority |
|---|---|---|---|---|
| BOLT 11 duplicate send (same `paymentHash`, `Pending`/`Succeeded`) | **M** | D1, D2, D14 | No store, no `PaymentId`, no admission predicate. `k₁ := create sha p a c`; `k₂ := create sha p a c`; both `session.state = .pending` and both `settle .succeeded`; `settle_terminal` does not relate them. The English "must not be paid twice" is unrepresented. | P0 |
| Keysend/spontaneous duplicate send | **X** at lifecycle level | D3, D4, D14 | `Keysend.retry` resets **any** state to `pending` (`KeysendProps.lean:252-255`), and `retry_pending` proves it for a succeeded record (`:300-301`). LDK would return `DuplicatePayment` for the corresponding `Succeeded` store entry (`spontaneous.rs:67-73`). The theorem is true of the model; the model's retry transition contradicts the LDK admission rule. | P0 |
| Retry after a failed attempt (new attempt, same hash/preimage) | **P** | D9, D10 | `Keysend.retry` preserves preimage/hash (`retry_preimage`, `retry_session_paymentHash`) and resets state, which matches the *record* part. But there is no failure-only precondition and no store: it also resets `succeeded`. No retry-policy carrier at all. | P0 |
| Store status machine (`Pending`→`Succeeded`/`Failed`) and persistence | **M** | D5, D6 | `PaymentSession.settle` is absorbing (`settle_terminal`), while LDK's `PaymentDetails.status` is overwritten by `update_if_necessary!` (`store.rs:335-337`). The model has no record that survives a restart. | P1 |
| Late `PaymentFailed` after `Succeeded` | **P (coincidental)** | D8 | Lean's `settle_terminal` makes a second settlement a no-op, which matches the *outcome* of the LDK guard. But there is no event layer, no direction/kind test, and no `PaymentSent`/`PaymentFailed` distinction; the agreement is not proved against LDK, only against the absorbing session. | P1 |
| `PaymentSent` unconditional `Succeeded` (including after `Failed`) | **X** vs `PaymentSession.settle` | D6, D7 | `settle` cannot move `failed`→`succeeded`; `PaymentDetails.update` can (`store.rs:335-337`). This is a store-layer divergence, not a false Lean theorem. Must be modelled as a separate layer, not by changing `settle`. | P1 |
| Guard/send/record atomicity and crash recovery | **E** | D2, D7 | The lookup at `bolt11.rs:209` and insert at `:266` are separate awaits. `PaymentSent` does not reconstruct a missing record (`event.rs:1560-1564`). Lean has no persistence or crash step, so it cannot state the guarantee or the window. The LDK-level duplicate check at `bolt11.rs:277` may cover part of the pending window; that is an external fact to verify, not a Lean theorem. | P1 |
| Duplicate payment hash at the recipient (BOLT 4 MAY accept) | **M** | D16 | `refs/bolts/04-onion-routing.md:1531-1535` allows accept-or-unknown. Lean has no per-hash admission rule, no preimage store, and no paid-hash set. | P2 |
| MPP exact-sum settlement | **P (conservative)** | D15, D17 | `MppPayment.settle` returns `none` unless `partsSum = total` (`Invariants.lean:440-446`), and `mppComplete` is exact (`MPP.lean:144-146`). BOLT 4 permits completion when the set total is **≥** `total_msat` (`04-onion-routing.md:399-402`). Counterexample: `parts = [120]`, `total = 100`; Lean `settle = none`, protocol permits fulfill. | P1 |
| MPP `total_msat` equality across the set | **M (unrepresentable)** | D15 | `MPPPlan` has one `target` for all parts; a mixed-total set cannot be constructed, so the BOLT 4 `SHOULD fail the entire HTLC set if total_msat is not the same` check has no carrier. | P1 |
| MPP part identity (`htlc_id`) and exact duplicate detection | **P** | D11, D15 | `MPPPart` has no `htlc_id` (`MPP.lean:83-88`); `sameKey_distinctAmount_both_counted` (`MPPProps.lean:381-385`) mechanizes that two same-channel/same-CLTV/different-amount parts are both retained. The model cannot distinguish a replayed HTLC from a distinct part with the same key. | P2 |
| MPP atomicity across reachable states | **P** | D15 | `mppAtomic_no_mixed` (`Laws.lean:210-222`) excludes mixed outcomes in a supplied list. It is not a reachability theorem over collector steps, and `MppPayment`'s `accepted : Bool` has no per-part outcome at all. | P2 |
| Inbound `PaymentClaimable` / duplicate or replayed claim | **M** | D17 | No inbound claim state, no `claimed` flag, no preimage store. Lean cannot state "a replayed claim is idempotent" or "a second claim after success is rejected." | P2 |
| Probing budget | **M** | D12, D13 | No probe carrier at all. `locked_msat` is derived from the payment store (`probing.rs:830-844`), so a standalone `Nat` budget would be an over-approximation unless linked to the store. | P2 |
| Probe persistence across restart | **E** | D13 | `probing_budget_restored_after_node_restart` observes `locked_msat > 0` after restart. Lean has no payment persistence, so this must either be modelled with a store snapshot or recorded as external. | P2 |
| Keysend receiver preimage binding | **C (conditional)** | D3; `onion_payment.rs:440-455` cited by `F15.lean:8-11` | `Keysend.preimage_binding` holds under hash injectivity/`IsCommittedPreimage`; the unconditional `unchecked_record_counterexample` is retained. This is the one part of the surface that is faithfully covered, and it is *not* a lifecycle theorem. | — |

Summary shape: the arithmetic/MPP rows are green but narrower than the English
behaviour; the lifecycle, store, persistence, and probing behaviours have no
carrier. The only outright model-level contradiction is the unguarded
`Keysend.retry` reset versus LDK's `Succeeded` duplicate rejection; the MPP
exact-sum rule is a deliberate conservative restriction, not a false theorem.

---

## 4. Proposed targets

All targets are **additive**. None changes `PaymentSession.settle`,
`mppComplete`, `settle_requires_sum`, `Keysend.retry`, or any existing
theorem. New modules are proposed so the blast radius is one import line in a
future `All.lean`.

### T1 — Duplicate-payment send-admission guard (P0)

**Proposed names**
- `LnLean.Payment.Store.PaymentRecord`, `PaymentRecord.status`
- `LnLean.Payment.Store.admit`
- `LnLean.Proofs.Payment.LifecycleTargets.admit_rejects_pending`
- `LnLean.Proofs.Payment.LifecycleTargets.admit_rejects_succeeded`
- `LnLean.Proofs.Payment.LifecycleTargets.admit_allows_failed`
- `LnLean.Proofs.Payment.LifecycleTargets.admit_allows_fresh`

**Statement shape**

```lean
inductive Direction where
  | inbound
  | outbound
deriving DecidableEq, BEq

structure PaymentRecord where
  id        : PaymentHash
  status    : PaymentState       -- pending | succeeded | failed
  amount    : Msat
  direction : Direction

abbrev PaymentStore := List PaymentRecord

def findRecord? (st : PaymentStore) (id : PaymentHash) : Option PaymentRecord :=
  st.find? (fun r => r.id = id)

/-- The LDK guard: reject exactly Pending and Succeeded. -/
def admit (st : PaymentStore) (id : PaymentHash) : Bool :=
  match findRecord? st id with
  | some r => r.status != .pending && r.status != .succeeded
  | none   => true

theorem admit_rejects_pending (st) (id) (r)
    (hfind : findRecord? st id = some r) (hst : r.status = .pending) :
    admit st id = false

theorem admit_rejects_succeeded (st) (id) (r)
    (hfind : findRecord? st id = some r) (hst : r.status = .succeeded) :
    admit st id = false

theorem admit_allows_failed (st) (id) (r)
    (hfind : findRecord? st id = some r) (hst : r.status = .failed) :
    admit st id = true

theorem admit_allows_fresh (st) (id) (h : findRecord? st id = none) :
    admit st id = true
```

**Hypotheses.** `id` is the payment-hash-derived identifier, matching
`bolt11.rs:208` and `spontaneous.rs:64-65`. There is no well-formedness
hypothesis beyond the store lookup. `admit` is deliberately **not** stated as
"reject terminal": `failed` is admitted.

**Non-vacuity witness.** `st := []`, any `id`; `admit_allows_fresh` is
`by simp [admit, h]`. For the rejecting side, `st := [{id, .succeeded, ...}]`;
`admit_rejects_succeeded` is `by simp [admit, findRecord?, hfind, hst]`.

**Why it is faithful.** The two rejection branches are exactly
`src/payment/bolt11.rs:209-214` and `src/payment/spontaneous.rs:67-73`; the
`failed` branch is exactly the absence of a `Failed` test in those guards. The
theorem is per-store-record, so it does not overclaim protection across two
independent stores. It does not model the read-check-send-insert race (T4).

**Feasibility.** High: pure list/`Option` reasoning. **Extension:** model
extension. **Priority:** P0.

---

### T2 — Guarded keysend retry (P0)

**Proposed names**
- `LnLean.Proofs.Payment.KeysendProps.retry?`
- `LnLean.Proofs.Payment.LifecycleTargets.retry?_eq_none_of_succeeded`
- `LnLean.Proofs.Payment.LifecycleTargets.retry?_eq_some_of_failed`
- `LnLean.Proofs.Payment.LifecycleTargets.retry?_eq_none_of_pending`

**Statement shape**

```lean
/-- A new attempt is permitted only after a recorded failure. -/
def Keysend.retry? (k : Keysend) : Option Keysend :=
  if k.session.state = .failed then
    some { k with session := { k.session with state := .pending } }
  else none

theorem retry?_eq_none_of_succeeded (k : Keysend)
    (h : k.session.state = .succeeded) : k.retry? = none

theorem retry?_eq_some_of_failed (k : Keysend)
    (h : k.session.state = .failed) : ∃ k', k.retry? = some k'

theorem retry?_eq_none_of_pending (k : Keysend)
    (h : k.session.state = .pending) : k.retry? = none
```

**Hypotheses.** `retry?` is a *record-level* gate on the stored attempt state.
It is necessary but **not sufficient** for duplicate protection: a fresh
`Keysend` constructed from the same preimage has a fresh `pending` session and
would pass. Cross-session protection is T1.

**Non-vacuity witness.** `k := (create sha p a c).settle .failed`; then
`k.session.state = .failed` by `settle_pending_terminal`, so `retry?_eq_some_of_failed`
applies. For the negative branch, `k := (create sha p a c).settle .succeeded`.

**Why it is faithful.** LDK never retries a succeeded payment: the store guard
rejects `Succeeded` (`spontaneous.rs:67-73`), and the only retry mechanism is
the internal `Retry::Timeout` for a payment that is still pending
(`config.rs:171-172`, `spontaneous.rs:109-114`). The existing `retry` and
`retry_pending` are retained unchanged as the raw reset; the new name makes the
guard explicit rather than falsifying an existing theorem.

**Feasibility.** High. **Extension:** model extension. **Priority:** P0.

---

### T3 — Store/event layer: late success and terminal status (P1)

**Proposed names**
- `LnLean.Payment.Store.applySent`, `applyFailed`, `applyStatus`
- `LnLean.Proofs.Payment.LifecycleTargets.late_failure_after_success_noop`
- `LnLean.Proofs.Payment.LifecycleTargets.failed_then_sent_overwrites`

**Statement shape**

```lean
/-- LDK `PaymentSent`: unconditional overwrite. -/
def applySent (r : PaymentRecord) : PaymentRecord :=
  { r with status := .succeeded }

/-- LDK late-failure guard: only outbound Lightning after success is ignored. -/
def applyFailed (r : PaymentRecord) : PaymentRecord :=
  if r.direction = .outbound ∧ r.status = .succeeded then r
  else { r with status := .failed }

theorem late_failure_after_success_noop (r : PaymentRecord)
    (hd : r.direction = .outbound) (hs : r.status = .succeeded) :
    applyFailed r = r

theorem failed_then_sent_overwrites (r : PaymentRecord)
    (hf : r.status = .failed) :
    (applySent r).status = .succeeded
```

**Hypotheses.** The late-failure guard needs the direction and a
"Lightning payment kind" predicate to match `event.rs:1614-1622`; the shape
above uses `direction` only and must add `kind.isLightning` in the real
statement. `applySent` has no hypothesis, matching `event.rs:1550-1556`.

**Non-vacuity witness.** `r := {id, .failed, amount, .outbound}`;
`failed_then_sent_overwrites` is `rfl`. `r := {id, .succeeded, ...}`;
`late_failure_after_success_noop` is `by simp [applyFailed, hd, hs]`.

**Why it is faithful.** It separates the *store projection* from the *attempt
state*: `PaymentDetails.status` is overwritten by `update_if_necessary!`
(`store.rs:335-337`), while `PaymentSession.settle` is absorbing
(`HTLC.lean:136-152`). The two theorems are characterizations of LDK, not
protocol safety claims. In particular, `failed_then_sent_overwrites` is
**allowed** to contradict `settle_terminal` because it is a different layer;
§5 explains why this must not be "fixed" in `settle`.

**Feasibility.** High. **Extension:** model extension (new store layer).
**Priority:** P1.

---

### T4 — Send/record atomicity: negative window theorem (P1)

**Proposed names**
- `LnLean.Payment.Store.Trace`, `send`, `record`, `sendThenRecord`, `recordThenSend`
- `LnLean.Proofs.Payment.LifecycleTargets.send_then_record_admits_duplicate`
- `LnLean.Proofs.Payment.LifecycleTargets.record_then_send_rejects_duplicate`

**Statement shape**

```lean
/-- The store plus the sends already performed (the network trace). -/
structure Trace where
  store : PaymentStore
  sent  : List PaymentHash

/-- A send performs I/O and does **not** mutate the store. -/
def send (t : Trace) (id : PaymentHash) : Trace :=
  { t with sent := id :: t.sent }

/-- The Pending record write is a separate step. -/
def pendingRecord (id : PaymentHash) : PaymentRecord :=
  { id := id, status := .pending, amount := ⟨0⟩, direction := .outbound }

def record (t : Trace) (id : PaymentHash) : Trace :=
  { t with store := pendingRecord id :: t.store }

/-- Current order: check, send, then record. -/
def sendThenRecord (t : Trace) (id : PaymentHash) : Trace :=
  record (send t id) id

/-- Two sends of the same id can both pass the check before either record. -/
theorem send_then_record_admits_duplicate :
    ∃ (t : Trace) (id : PaymentHash),
      admit t.store id = true ∧
      admit (send t id).store id = true ∧
      (send (send t id) id).sent = [id, id]

/-- The reordered discipline: record Pending before the send. -/
def recordThenSend (t : Trace) (id : PaymentHash) : Trace :=
  send (record t id) id

theorem record_then_send_rejects_duplicate
    (t : Trace) (id : PaymentHash) :
    admit (record t id).store id = false
```

The trace is essential: `sendThenRecord` on its own writes the record, so a
*sequential* second admission would already be rejected. The witness is the
interleaving in which the second admission reads the store after the first
send but before the first record — the crash/retry window. The mechanized
version should state that interleaving explicitly, not rely on definitional
equality.

**Hypotheses.** `send`/`record` model the pinned order
(`bolt11.rs:209` → `:236-241` → `:260-266`). `recordThenSend` is the
*proposed production reorder*, not a claim about current LDK. There is no
hypothesis that the store is durable; durability is external.

**Non-vacuity witness.** `t := {store := [], sent := []}`, `id` arbitrary:
`admit [] id = true`; `(send t id).store = []`, so the second admission is
also `true`; and `(send (send t id) id).sent = [id, id]` records that two
sends actually occurred. The negative theorem is non-vacuous because the
trace keeps the sends; the model does not silently drop the first one.

**Why it is faithful.** It encodes exactly the two separate awaits in
`bolt11.rs:209` and `:266`, and it explains why the store guard alone is not a
crash-safety theorem. The theorem must **not** be presented as "LDK is
vulnerable": the channel-manager duplicate check at `bolt11.rs:277` may cover
the pending window, and `PaymentSent` does not reconstruct a missing record
(`event.rs:1560-1564`) only establishes the node-store part. The honest
conclusion is "the node-level guard is non-atomic; closing it requires either
record-before-send or a lower-layer guarantee that Lean does not model."

**Feasibility.** Medium: needs a small state machine and an interleaving
relation, not arithmetic. **Extension:** model extension + **external**
production/deployment assumption for the fix. **Priority:** P1.

---

### T5 — MPP `≥` settlement variant (P1)

**Proposed names**
- `LnLean.Proofs.Payment.MPPGeTargets.MppPayment.settleGe`
- `LnLean.Proofs.Payment.MPPGeTargets.settleGe_requires_ge`
- `LnLean.Proofs.Payment.MPPGeTargets.settleGe_subsumes_settle`
- `LnLean.Proofs.Payment.MPPGeTargets.settleGe_overpay_witness`

**Statement shape**

```lean
/-- BOLT 4 completion: non-empty and set total at least `total_msat`. -/
def MppPayment.settleGe (m : MppPayment) : Option MppPayment :=
  if m.parts ≠ [] ∧ m.total.val ≤ m.partsSum then
    some { m with accepted := true }
  else none

theorem settleGe_requires_ge (m m' : MppPayment)
    (h : m.settleGe = some m') :
    m.parts ≠ [] ∧ m.total.val ≤ m.partsSum

theorem settleGe_subsumes_settle (m m' : MppPayment)
    (hne : m.parts ≠ []) (h : m.settle = some m') :
    m.settleGe = some m'

theorem settleGe_overpay_witness :
    ∃ m m', m.parts = [⟨120⟩] ∧ m.total = ⟨100⟩ ∧
      m.settleGe = some m' ∧ m'.accepted = true
```

**Hypotheses.** Non-emptiness is required, matching `mppComplete`'s `parts ≠ []`
(`MPP.lean:144-146`). `settleGe` is a *new* function; `MppPayment.settle` and
`settle_requires_sum` (`Invariants.lean:440-454`) are untouched.

**Non-vacuity witness.** `m.parts = [120]`, `m.total = 100`:
`m.settleGe = some ...` and `120 ≥ 100`. This is also the explicit
counterexample to the exact-only model, so it must be retained, not deleted.

**Why it is faithful.** `refs/bolts/04-onion-routing.md:399-402` says fulfill
when the set total is `≥ total_msat`. The exact form remains a valid special
case (`settleGe_subsumes_settle`), so the existing `LN-PM-004` claim is
preserved rather than weakened. The underpaying LDK API
(`bolt11.rs:362-405`) is a **different** extension (declare the full total, send
less) and is not evidence for the `≥` rule; the report should not merge them.

**Feasibility.** High. **Extension:** model extension. **Priority:** P1.

---

### T6 — MPP part identity and set-level consistency (P1/P2)

**Proposed names**
- `LnLean.Payment.MPP.IdentifiedPart` (`htlcId`, per-part `totalMsat`)
- `LnLean.Proofs.Payment.MPPIdentityTargets.distinct_htlc_both_counted`
- `LnLean.Proofs.Payment.MPPIdentityTargets.same_htlc_replay_dropped`
- `LnLean.Proofs.Payment.MPPIdentityTargets.mixed_total_rejected`
- `LnLean.Proofs.Payment.MPPIdentityTargets.reachable_no_mixed`

**Statement shape**

```lean
structure IdentifiedPart where
  htlcId     : Nat
  channel    : ShortChannelId
  amount     : Msat
  totalMsat  : Msat
  cltv       : Height
  state      : PaymentState

def addIdentified (ps : List IdentifiedPart) (p : IdentifiedPart) :
    List IdentifiedPart :=
  if ps.any (fun q => q.htlcId = p.htlcId) then ps else p :: ps

/-- BOLT 4's `total_msat` agreement across one HTLC set. -/
def sameTotal (ps : List IdentifiedPart) : Prop :=
  ∀ p ∈ ps, ∀ q ∈ ps, p.totalMsat = q.totalMsat

theorem distinct_htlc_both_counted (p q : IdentifiedPart)
    (h : p.htlcId ≠ q.htlcId) :
    p ∈ addIdentified [p, q] ∧ q ∈ addIdentified [p, q]

theorem same_htlc_replay_dropped (ps : List IdentifiedPart) (p : IdentifiedPart)
    (h : ∃ q ∈ ps, q.htlcId = p.htlcId) : addIdentified ps p = ps

theorem mixed_total_rejected (ps : List IdentifiedPart)
    (p q : IdentifiedPart) (hp : p ∈ ps) (hq : q ∈ ps)
    (hmix : p.totalMsat ≠ q.totalMsat) : ¬ sameTotal ps

/-- One collector step settles every pending part to one common outcome. -/
def Step (s s' : PaymentSession) : Prop :=
  ∃ o : PaymentState, o.isTerminal ∧ s' = settleParts s o

def Reachable (s s' : PaymentSession) : Prop :=
  Relation.ReflTransGen Step s s'

theorem reachable_no_mixed (s s' : PaymentSession)
    (h0 : ∀ p ∈ s.parts, p.state = .pending)
    (hr : Reachable s s') :
    AllOrNothing s' ∨ AllPending s'
```

**Hypotheses.** `htlcId` is per-channel/per-peer in LDK; a globally unique
`Nat` is a modelling simplification and must be flagged. `totalMsat` is the
BOLT 4 field that `MPPPlan` currently collapses into one `target`.
`reachable_no_mixed` reuses the existing `PaymentPart`/`settleParts` carrier
(`MPPProps.lean:416-419`) and needs the hypothesis that the initial parts are
all `pending`; `IdentifiedPart` is the parallel identity refinement, so the
implementation should add a projection `IdentifiedPart → PaymentPart` rather
than fork the settlement transition.

**Non-vacuity witness.** `p.htlcId = 0`, `q.htlcId = 1`, distinct;
`distinct_htlc_both_counted` is `by simp [addIdentified]`. For the mixed-total
result, take `ps = [p, q]` with `p.totalMsat = 100` and `q.totalMsat = 200`;
`mixed_total_rejected` then yields `¬ sameTotal [p, q]`, which is exactly the
set the BOLT 4 `SHOULD fail the entire HTLC set` rule at
`04-onion-routing.md:397` is about. The result is not vacuous: `ps = [p, p]`
with one total *does* satisfy `sameTotal`, so the hypothesis is satisfiable.

**Why it is faithful.** It fixes the documented gap in
`sameKey_distinctAmount_both_counted` (`MPPProps.lean:381-385`) without
deleting that counterexample: the old model still exhibits the gap, the new
carrier proves the `htlc_id` refinement closes it. It also gives
`mppAtomic_no_mixed` (`Laws.lean:210-222`) a reachability reading.

**Feasibility.** Medium (list dedup + a small transition relation).
**Extension:** model extension. **Priority:** P1 for `mixed_total_rejected`,
P2 for `reachable_no_mixed`.

---

### T7 — Inbound claimable: duplicate and replayed claims (P2)

**Proposed names**
- `LnLean.Payment.Inbound.InboundClaim`, `claim`
- `LnLean.Proofs.Payment.InboundTargets.claim_idempotent`
- `LnLean.Proofs.Payment.InboundTargets.late_claimable_after_claim_noop`

**Statement shape**

```lean
structure InboundClaim where
  paymentHash : PaymentHash
  amount      : Msat
  claimed     : Bool
  preimage    : Option Preimage

def claim (c : InboundClaim) (p : Preimage) : Option InboundClaim :=
  if c.claimed then none
  else some { c with claimed := true, preimage := some p }

theorem claim_idempotent (c : InboundClaim) (p : Preimage)
    (h : c.claimed = true) : claim c p = none

theorem late_claimable_after_claim_noop (c : InboundClaim) (p : Preimage)
    (h : c.claimed = true) :
    claim c p = none
```

**Hypotheses.** A replayed `PaymentClaimable` is idempotent only if the store
update is the `Updated | Unchanged` branch; the `NotFound` branch inserts a
`Succeeded` inbound record (`event.rs:1484-1498`). The model needs both
branches, otherwise `claim_idempotent` hides the insert. The preimage is
assumed known to the claimant; knowledge/proof is external.

**Non-vacuity witness.** `c := {hash, 100, false, none}`; `claim c p = some ...`
with `claimed = true`. Then `claim (claim c p).get! p = none`.

**Why it is faithful.** It matches the pinned idempotent update comment and
the manual-claim contract (`ldk-server api.rs:240-250`). It is a *new* inbound
carrier; it does not pretend `PaymentSession.settle` models receiving.

**Feasibility.** High. **Extension:** model extension. **Priority:** P2.

---

### T8 — Probing budget (P2)

**Proposed names**
- `LnLean.Payment.Probe.ProbeBudget`, `admitProbe`, `releaseProbe`
- `LnLean.Proofs.Payment.ProbeTargets.admitProbe_preserves_budget`
- `LnLean.Proofs.Payment.ProbeTargets.admitProbe_rejects_over_budget`
- `LnLean.Proofs.Payment.ProbeTargets.release_restores_budget`

**Statement shape**

```lean
structure ProbeBudget where
  maxLocked : Nat
  locked    : Nat

def admitProbe (b : ProbeBudget) (amount : Nat) : Option ProbeBudget :=
  if b.locked + amount ≤ b.maxLocked then
    some { b with locked := b.locked + amount }
  else none

def releaseProbe (b : ProbeBudget) (amount : Nat) : ProbeBudget :=
  { b with locked := b.locked - amount }

theorem admitProbe_preserves_budget (b b' : ProbeBudget) (a : Nat)
    (h : admitProbe b a = some b') : b'.locked ≤ b'.maxLocked

theorem admitProbe_rejects_over_budget (b : ProbeBudget) (a : Nat)
    (h : b.maxLocked < b.locked + a) : admitProbe b a = none

theorem release_restores_budget (b : ProbeBudget) (a : Nat)
    (h : a ≤ b.locked) :
    (releaseProbe b a).locked = b.locked - a
```

**Hypotheses.** `amount` must be the delivered amount **plus** pending routing
fees, matching `locked_msat` (`probing.rs:830-844`). The model must either
derive `locked` from the payment store or carry an explicit hypothesis that
`locked` equals that sum; otherwise the standalone `Nat` is an
over-approximation. Probe success/failure handlers only log
(`probing.rs:847-863`), so no outcome transition is needed for the budget
theorem.

**Non-vacuity witness.** `b := {maxLocked := 1000, locked := 0}`,
`a := 400`; `admitProbe b 400 = some {locked := 400}`, and `400 ≤ 1000`.
The over-budget branch: `b.locked = 800`, `a = 400`.

**Why it is faithful.** It is exactly the arithmetic check at
`probing.rs:883-888`, and it matches the cap test
`exhausted_probe_budget_blocks_new_probes` (`tests/probing_tests.rs:428-480`).
The restart property (`:305-329`) is **not** proved by this target; see §5.

**Feasibility.** High for the arithmetic; medium for the store link.
**Extension:** model extension + **external** link to `list_recent_payments`.
**Priority:** P2.

---

## 5. Assumptions, counterexamples, and non-vacuity risks

### 5.1 Existing counterexamples that must be preserved

1. **F14 over-total (`F14.lean:196-229`).** `overTotalPlan` has two 60 msat
   parts against a 100 msat target; `overTotal_counterexample` refutes
   unconditional `RunningTotalBound` preservation, and
   `overTotal_not_complete` (`:261`) shows the plan is not `mppComplete`.
   **Do not replace `mppComplete` with `mppCompleteGe`.** T5 adds a *separate*
   `settleGe`; the exact-sum carrier and the counterexample stay.
2. **F15 unchecked record (`F15.lean:317-334`).** A pending keysend can carry
   an uncommitted preimage and still settle/reveal it. **T2 does not fix this.**
   `retry?` is about attempt admission, not receiver acceptance. Do not claim
   that adding `retry?` closes the unchecked-record gap; `AcceptedKeysend`
   (`F15.lean:79-80`) remains the necessary hypothesis for the reveal theorem.
3. **`MPPProps.sameKey_distinctAmount_both_counted` (`:381-385`).** Two parts
   with the same channel and CLTV but different amounts are both counted.
   T6 must keep this theorem in the old carrier and add the `htlc_id` carrier
   alongside it, not delete or restate the old one as if the gap never existed.
4. **`settle_terminal` / `settle_idempotent` (`HTLC.lean:148-152`,
   `Laws.lean:225-233`).** These are the attempt-layer absorbing laws. T3 is a
   *different* layer; it must not be used to change `settle`. If someone
   "aligns" `settle` with LDK's overwrite, `settle_terminal` becomes false and
   the `LN-PM-004`/`LN-PM-005` reasoning loses its carrier.
5. **`Keysend.retry_pending` (`:300-301`).** The raw `retry` is a total reset
   and the theorem is true. T2 adds `retry?`; it must not redefine `retry`, or
   the existing theorem breaks. Keeping both is the non-vacuity-preserving
   move, and the report should say why the old function remains (it is the
   unguarded transition the counterexample is about).

### 5.2 Assumptions that must stay explicit

- **Crash/durability.** T4's negative theorem is only meaningful with an
  explicit "the first record is not observed by the second admission"
  interleaving. If the target instead assumes `recorded` before the send, it
  proves nothing about the pinned order at `bolt11.rs:209,266`. The fix
  (record-before-send) is a **production reorder**, not a Lean theorem.
- **Lower-layer duplicate check.** `bolt11.rs:277` maps
  `RetryableSendFailure::DuplicatePayment` to `Error::DuplicatePayment`. If
  LDK's channel manager still holds the pending payment after a crash, the
  node-store window may be closed. That is an external fact about the pinned
  LDK build; do not assert either vulnerability or safety from the Lean model.
- **`PaymentSent` does not reconstruct a record.** At `event.rs:1560-1564`
  the update result is matched as `Ok(_)`, unlike the inbound claim path's
  `NotFound => insert` at `:1484-1498`. The target must cite this asymmetry
  and not assume a reconciliation step that the pinned code does not have.
- **Probe budget source.** `locked_msat` is computed from
  `channel_manager.list_recent_payments()` (`probing.rs:830-844`). T8's
  standalone `ProbeBudget` is only an over-approximation until it is linked to
  a payment-store snapshot; the restart property is external/persistence work.
- **MPP underpay vs overpay.** The underpaying API (`bolt11.rs:362-405`) is a
  deliberate LDK extension that declares the full total while sending less;
  it is **not** the BOLT 4 `≥` rule. Only `04-onion-routing.md:399-402`
  supports T5.
- **`total_msat` sameness.** BOLT 4's same-total check
  (`04-onion-routing.md:397`) is `SHOULD`, not `MUST`. T6's
  `mixed_total_rejected` should be phrased as the model's rejection rule, with
  the BOLT strength recorded, not as a protocol invariant.

### 5.3 Non-vacuity traps

- **Naive terminal rejection is wrong.** `PaymentState.isTerminal` includes
  `failed` (`HTLC.lean:74-77`), but LDK admits a new send after `Failed`
  (`bolt11.rs:209-214`). A theorem `admit = false ↔ status.isTerminal` is
  false for the pinned behaviour. T1's `admit_allows_failed` is the
  counterexample-preserving complement and must be kept.
- **Empty MPP plans.** `mppComplete` and `mppCompleteGe` both require
  `parts ≠ []`, so the empty plan cannot witness completion. T5's `settleGe`
  repeats that hypothesis; the overpay witness uses positive amounts, not the
  degenerate `0/0` case.
- **`mppCompleteGe` is arithmetic only.** It is defined at
  `MPPProps.lean:686-688` and `mppComplete_implies_completeGe`
  (`:690-693`) proves exact ⇒ `≥`. Nothing connects it to `MppPayment.settle`
  or `PaymentSession`. T5 must state the bridge; merely naming
  `mppCompleteGe` would be a similarly-named-coverage mistake.
- **`MppPayment.accepted : Bool` is not a state machine.** Setting
  `accepted := true` proves nothing about parts, preimages, or a second claim.
  T5's `settleGe` is an acceptance predicate, not a lifecycle theorem; do not
  promote it to one.
- **`retry?` on a fresh record.** A fresh keysend is `pending`, so `retry?`
  returns `none`; this is correct for "retry the same attempt" but does not
  model "start a new attempt with the same preimage." The latter needs T1's
  store guard. State this explicitly or the target overclaims.

---

## 6. Wave-13 recommendation

### 6.1 Verdict

This is a **safe bounded model-extension lane**, not a repair of an existing
open issue and not a closure of a green catalog row. The catalog is green and
correct at its stated scope; the missing behaviours are *new* model surface.
The lane should add new modules and new issue ids, and must not retarget
`LN-PM-001`–`007`.

Proposed new issue ids (parent-owned; none exists today — `rg` over
`docs/OPEN-ISSUES.md` finds no `PAY-0`/`LN-PAY-0` row):

| Id | Scope | Targets | Disposition |
|---|---|---|---|
| `PAY-01` | Payment lifecycle: duplicate send, retry admission, store/event status, crash window, inbound claimable/replay | T1, T2, T3, T4, T7 | **Implement T1/T2/T3 in wave 13; T4 as a negative model theorem, fix external; defer T7** |
| `PAY-02` | MPP overpay, same-total, `htlc_id`, reachable atomicity | T5, T6 | **Implement T5 in wave 13; defer T6 to wave 14** |
| `PAY-03` | Probing budget and persistence | T8 | **Defer; external link to the payment store required** |

Do **not** add these as `LN-PM-008+` rows until the parent runs the catalog
update; the review lane only proposes names.

### 6.2 Implement / defer / external

**Implement in wave 13 (highest value, lowest risk):**
- **T1** (`admit_rejects_pending`, `admit_rejects_succeeded`,
  `admit_allows_failed`, `admit_allows_fresh`) — new
  `LnLean/Payment/Store.lean` + `LnLean/Proofs/Payment/LifecycleTargets.lean`.
  This is the single most valuable target: it states the behaviour the pinned
  code actually implements and makes the `Failed`-is-admitted subtlety
  explicit.
- **T2** (`retry?` and its three lemmas) — additive in
  `KeysendProps.lean` or in the new targets module; keep `retry` and
  `retry_pending` intact.
- **T3** (`applySent`, `applyFailed`, the two characterization lemmas) — same
  new store module. This is the layer that prevents future readers from
  "fixing" `PaymentSession.settle`.
- **T4** (negative atomicity theorem) — cheap and important, but publish it
  as a *model-level non-atomicity result*, with the external lower-layer
  question stated. Do not let it become an unqualified "LDK double-pays"
  claim.
- **T5** (`settleGe_requires_ge`, `settleGe_subsumes_settle`,
  `settleGe_overpay_witness`) — new
  `LnLean/Proofs/Payment/MPPGeTargets.lean`; keep
  `MppPayment.settle_requires_sum` and `mppComplete` unchanged.

**Defer to wave 14:**
- **T6** (`htlc_id`, `totalMsat`, `reachable_no_mixed`) — needs a new carrier
  and a transition relation; the design should be reviewed against R07/R09
  (HTLC/BOLT 4 lanes) to avoid a fourth disconnected MPP carrier.
- **T7** (inbound claim) — low risk but lower value without a preimage store;
  pair it with the persistence work in R17.
- **T8** (probe budget) — arithmetic is trivial, but the meaningful theorem
  needs the payment-store link; do it after `PAY-01` lands.

**External / human barrier:**
- **Production send/record ordering.** The only way to make the T4 window
  disappear is to record `Pending` before the network send, or to rely on a
  lower-layer dedup guarantee. That is a code/deployment decision, not a proof.
- **LDK channel-manager duplicate behaviour after restart.** The pinned code
  has a second check at `bolt11.rs:277`, but whether it covers every crash
  interleaving is not something the Lean model can establish. Record it as an
  explicit external assumption.
- **Probe persistence.** `probing_budget_restored_after_node_restart` is a
  test observation, not a proof; linking it to a Lean store snapshot is future
  work.

### 6.3 Why not "fix" the existing model

- Changing `PaymentSession.settle` to overwrite status would falsify
  `settle_terminal`/`settle_idempotent` and would silently weaken the
  `LN-PM-004`/`LN-PM-005` story.
- Replacing `mppComplete` with `mppCompleteGe` would invalidate
  `overTotal_counterexample` and lose the mechanized over-total refutation.
  Add `settleGe` alongside.
- Redefining `Keysend.retry` to be guarded would falsify `retry_pending` and
  erase the counterexample. Add `retry?` alongside.

---

## 7. Evidence and commands

### 7.1 Pins and tree state

```sh
git -C /tmp/opencode/ldk-refs/ldk-node rev-parse HEAD
# fa123fed131e27ecc420b77fa7086fcf1ddaebb8
git -C /tmp/opencode/ldk-refs/ldk-server rev-parse HEAD
# c17dc11dde38f88c53457039ddf30c6b90a63ba2
git -C /home/ubuntu/ln-lean-repair rev-parse HEAD
# f7f062817c185cd70004bb26c652deb99c6fd4bd
git -C /home/ubuntu/ln-lean-repair status --porcelain
# only the pre-existing untracked review/report/status paths, plus this report
```

### 7.2 Lean inspection commands

```sh
rg -n "inductive PaymentState|def isTerminal|structure PaymentPart|structure PaymentSession|def settle|theorem settle_terminal" LnLean/Payment/HTLC.lean
rg -n "structure MPPPlan|def mppComplete|theorem running_total_bound|def mppAtomic" LnLean/Payment/MPP.lean
rg -n "mppComplete_sum_eq_target|mppAtomic_no_mixed|settle_idempotent|settle_terminal_fixed" LnLean/Payment/Laws.lean
rg -n "structure MppPayment|def MppPayment.settle|settle_requires_sum" LnLean/Security/Invariants.lean
rg -n "def addParts|sameKey_distinctAmount_both_counted|def settleParts|def AllOrNothing|settleParts_idempotent|def mppCompleteGe" LnLean/Proofs/Payment/MPPProps.lean
rg -n "structure Keysend|def create|def retry|def revealedPreimage|retry_pending" LnLean/Proofs/Payment/KeysendProps.lean
rg -n "RunningTotalBound|PartFits|mppComplete_of_runningTotalBound_of_ge|overTotal_counterexample" LnLean/Proofs/ModelHardening/F14.lean
rg -n "SenderPreimageBinding|AcceptedKeysend|binding_preserved_by_retry|unchecked_record_counterexample" LnLean/Proofs/ModelHardening/F15.lean
rg -n "PaymentStore|payment_store|PaymentDetails|RetryPolicy" LnLean --include=*.lean
# no matches
rg -ni "probe" LnLean --include=*.lean
# only LnLean/Proofs/WaveH/H04.lean:48-93 (Bitcoin script fixtures)
sed -n '1,40p' LnLean/Proofs/PhaseC3/PersistenceRecovery.lean
# channel counters/HTLC set/ready flag only; no payment store
```

### 7.3 LDK inspection commands

```sh
sed -n '195,300p' /tmp/opencode/ldk-refs/ldk-node/src/payment/bolt11.rs
sed -n '55,150p'  /tmp/opencode/ldk-refs/ldk-node/src/payment/spontaneous.rs
sed -n '55,95p;140,170p;325,345p;395,415p' /tmp/opencode/ldk-refs/ldk-node/src/payment/store.rs
sed -n '1478,1500p;1515,1600p;1605,1630p' /tmp/opencode/ldk-refs/ldk-node/src/event.rs
sed -n '820,895p' /tmp/opencode/ldk-refs/ldk-node/src/probing.rs
sed -n '165,180p' /tmp/opencode/ldk-refs/ldk-node/src/config.rs
sed -n '440,480p;305,329p' /tmp/opencode/ldk-refs/ldk-node/tests/probing_tests.rs
sed -n '5339,5354p' /tmp/opencode/ldk-refs/ldk-node/tests/integration_tests_rust.rs
sed -n '500,545p' /tmp/opencode/ldk-refs/ldk-server/ldk-server-grpc/src/api.rs
sed -n '345,410p;1522,1548p' /home/ubuntu/ln-lean-repair/refs/bolts/04-onion-routing.md
```

### 7.4 What was *not* run

- No `lake build`, `lake env lean`, or full-tree build.
- No `cargo test`, `cargo check`, or network fetch against either LDK clone.
- No edits to Lean, docs, tests, vendor, scripts, or another lane's report.
  The only write is this file.

### 7.5 Residual uncertainty

- The crash-window discussion in T4 is a **code-order** observation
  (`bolt11.rs:209` vs `:266`) plus the `PaymentSent` `NotFound` no-op
  (`event.rs:1560-1564`). It does not prove an exploitable double-pay in LDK;
  the channel-manager duplicate check at `bolt11.rs:277` and LDK's own
  persistence must be checked by a code-owning lane (R17/R18/R24) before any
  vulnerability claim.
- The exact set of `PaymentKind` variants covered by the late-failure guard is
  `is_lightning_payment()` (`event.rs:1614-1622`); T3's real statement must
  include that predicate, not just `direction`.
- `MppPayment` at `Invariants.lean:425-430` has no hash/secret, so T5's
  `settleGe` is intentionally an arithmetic/acceptance theorem; it is not a
  full MPP model and must not be cited as one.
