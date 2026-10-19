# Wave 14 — 16 additive repair and assurance lanes

**Base:** `a331b71` (`repair/integrated`, wave-13 review checkpoint)
**Branch:** `wave-14/16`
**Worktree:** `/home/ubuntu/ln-lean-waveh`
**Objective:** turn the Wave 13 review’s tractable model/assurance defects into
green, additive Lean modules. Do not change existing predicate meanings, delete
retained counterexamples, or claim any external cryptographic/protocol barrier
has moved.

## Concurrency

Run eight lanes at a time. Every lane owns exactly one Lean module (the
assurance lane owns one script as well) and one report. The parent owns
`LnLean.lean`, `scripts/check-final.py`, `AxiomAudit.lean`, `Traceability.lean`,
`Obligations.lean`, docs, catalog, vendor, and Git. Lanes must not edit shared
files.

## Lanes

| Lane | Target | Owned Lean module | Owned report |
|---|---|---|---|
| `W14-LIQ-RESERVE` | T1/G01: reserve endpoint direction, corrected outbound/inbound, separation witness | `LnLean/Proofs/Wave14/LiquidityReserve.lean` | `agents/reports/wave14/W14-LIQ-RESERVE.md` |
| `W14-LIQ-INFLIGHT` | T2/G02–G04: directional pending in-flight, corrected add guard, separation and preservation witness | `LnLean/Proofs/Wave14/LiquidityInFlight.lean` | `agents/reports/wave14/W14-LIQ-INFLIGHT.md` |
| `W14-ANCHOR-DEBIT` | T3/G05: production-facing canonical anchor-debit pair, conservation, no-anchor alias, legacy 660 overfund witness | `LnLean/Proofs/Wave14/AnchorDebitConsumer.lean` | `agents/reports/wave14/W14-ANCHOR-DEBIT.md` |
| `W14-ANCHOR-PRESENCE` | G06/G07: exact single-anchor presence and net-dust consumer mismatch witness | `LnLean/Proofs/Wave14/AnchorPresenceConsumer.lean` | `agents/reports/wave14/W14-ANCHOR-PRESENCE.md` |
| `W14-STATE-RECEIPT` | T5/G09: numbered `commitment_signed` receipt adapter, idempotence, replay separation | `LnLean/Proofs/Wave14/NumberedReceipt.lean` | `agents/reports/wave14/W14-STATE-RECEIPT.md` |
| `W14-STATE-SNAPSHOT` | T7/G17: stale-snapshot restore consumer and latest-prefix failure witness | `LnLean/Proofs/Wave14/SnapshotRestoreConsumer.lean` | `agents/reports/wave14/W14-STATE-SNAPSHOT.md` |
| `W14-PAY-STORE` | T6/G11: finite payment store, duplicate pending/succeeded admission, identical-keysend witness | `LnLean/Proofs/Wave14/PaymentAdmission.lean` | `agents/reports/wave14/W14-PAY-STORE.md` |
| `W14-PAY-KEYSEND` | T6/G10: guarded keysend retry, succeeded/failed cases, old divergence retained | `LnLean/Proofs/Wave14/KeysendRetryGuard.lean` | `agents/reports/wave14/W14-PAY-KEYSEND.md` |
| `W14-ROUTE-CHAIN` | T4/G12: chain-backed route predicate, refinement to `routeValid`, disconnected and connected witnesses | `LnLean/Proofs/Wave14/RouteChain.lean` | `agents/reports/wave14/W14-ROUTE-CHAIN.md` |
| `W14-ROUTE-FEE` | G13/G14: floor-vs-ceiling fee separation, additive capacity/min/max usability carrier | `LnLean/Proofs/Wave14/RouteFeeCapacity.lean` | `agents/reports/wave14/W14-ROUTE-FEE.md` |
| `W14-MPP` | G08: additive `settleGe`/overpay-completion layer, underpay rejection witness | `LnLean/Proofs/Wave14/MppSettlement.lean` | `agents/reports/wave14/W14-MPP.md` |
| `W14-FEE-UPDATE` | G15/G16: checked fee-update legality and additive zero-fee/shared-anchor carrier | `LnLean/Proofs/Wave14/FeeUpdateLegality.lean` | `agents/reports/wave14/W14-FEE-UPDATE.md` |
| `W14-DELIVERY` | G18: non-circular delivery oracle/model, eventual-delivery instance, no-delivery counterexample | `LnLean/Proofs/Wave14/DeliveryModel.lean` | `agents/reports/wave14/W14-DELIVERY.md` |
| `W14-READY` | G19: `channel_ready` two-flag gate vs confirmation/connectivity readiness separation | `LnLean/Proofs/Wave14/ReadyUsefulness.lean` | `agents/reports/wave14/W14-READY.md` |
| `W14-ASSURANCE` | T8/G20–G22: catalog/audit/print coverage reconciliation script, negative fixture, Lean membership surface | `LnLean/Proofs/Wave14/AssuranceAudit.lean`, `scripts/check-assurance-coverage.py` | `agents/reports/wave14/W14-ASSURANCE.md` |
| `W14-UNIFIED` | G25: unified-send fatal/retryable outcome carrier, no silent fallback witness | `LnLean/Proofs/Wave14/UnifiedSendFatal.lean` | `agents/reports/wave14/W14-UNIFIED.md` |

## Lane contract

Each lane must follow `/tmp/opencode/wave14-common.md`. In particular:

- Work only on its owned files; do not edit `LnLean.lean`, `lakefile.lean`,
  `scripts/check-final.py`, `AxiomAudit.lean`, `Traceability.lean`,
  `Obligations.lean`, docs, catalog, vendor, refs, or another lane’s files.
- Keep the change additive. Do not redefine existing predicates or delete
  retained counterexamples.
- No `sorry`, `axiom`, `admit`, `native_decide`, `unsafe`, or
  `@[implemented_by]`.
- Include concrete non-vacuity witnesses; do not prove a hypothesis restatement.
- Build only the owned module under the shared build lock.
- Record exact theorem names, build result, axiom output, witness, gap closure,
  and remaining boundaries in the report.
- If the target cannot be made green faithfully, stop and report the blocker
  rather than weakening the statement or leaving a red module.

## Integration

The parent will:

1. verify every lane report and module;
2. regenerate `LnLean.lean` with `scripts/regen-root.sh`;
3. update `scripts/check-final.py`, the axiom audit, catalog/docs where justified;
4. run the full gate and exact `sorry` scan;
5. commit and push non-force only after the merged tree is green.

## Status (2026-10-19)

**Complete.** All 16 lanes built green individually and were integrated at
`f0a3c07` on `wave-14/16`. The full gate is RC 0: 330 Lake jobs, 291 Lean
files, 289 root imports, 51/51 catalog rows proved, 294 target occurrences
(282 unique), 315 anchors, 149 vendor files, 423 `#print axioms` commands over
a 465-name registry, and 0 actual `sorry`. The assurance checker reports the
remaining 72 unprinted / 35 unregistered catalog-target gap; strict mode is
intentionally red until that is closed. Reports are under
`agents/reports/wave14/`; integration evidence is in
`agents/status/WAVE-14-INTEGRATION.md`.
