# Wave 14 integration — 16 additive repair and assurance lanes

**Branch:** `wave-14/16` (from `repair/integrated` at `a331b71`)
**Code integration:** `f0a3c07` (`[WAVE14] integrate 16 additive repair and assurance lanes`)
**Base:** `a331b71` (wave-13 review checkpoint)
**Toolchain:** `leanprover/lean4:v4.35.0`
**Gate log:** `/tmp/opencode/waveh-gate.log`
**Gate runner:** `/tmp/opencode/waveh-gate.sh`

## Result

Wave 14 ran 16 disjoint additive lanes against the Wave 13 review defects.
Every lane built green under the shared build lock. The lanes wrote only their
owned modules and reports; the parent owned root imports, `AxiomAudit`, the
file-count check, the catalog docstring, and documentation.

The catalog remains **51 rows / 51 proved / 0 statement-only / 0 unresolved /
294 target occurrences (282 unique declarations)**. Wave 14 did not add catalog
rows and did not change the meaning of the retained predicates or remove any
counterexample.

## Lanes

| Lane | Primary result | Module |
|---|---|---|
| `W14-LIQ-RESERVE` | Corrected reserve direction and outbound/inbound functions; `reserve_direction_separates`; non-empty corrected witness | `LiquidityReserve.lean` |
| `W14-LIQ-INFLIGHT` | Directional pending-only in-flight cap; `directional_inFlight_separates`; terminal exclusion; `updateAddHtlc_preserves_directionalCap` | `LiquidityInFlight.lean` |
| `W14-ANCHOR-DEBIT` | `commitmentPairCanonical`; conservation under `fee + 660`; no-anchor alias; legacy 660 overfund witness retained | `AnchorDebitConsumer.lean` |
| `W14-ANCHOR-PRESENCE` | Exact anchor presence; single-anchor case; gross/net net-dust mismatch witness | `AnchorPresenceConsumer.lean` |
| `W14-STATE-RECEIPT` | Numbered receipt adapter; fresh/duplicate/wrong-number cases; replay idempotence | `NumberedReceipt.lean` |
| `W14-STATE-SNAPSHOT` | `restore`-applying stale-snapshot consumer; latest-prefix failure witness | `SnapshotRestoreConsumer.lean` |
| `W14-PAY-STORE` | Finite payment store; pending/succeeded duplicate rejection; failed/absent admission | `PaymentAdmission.lean` |
| `W14-PAY-KEYSEND` | `retryIfNotSucceeded`; succeeded/failed/pending cases; legacy succeeded-reset divergence retained | `KeysendRetryGuard.lean` |
| `W14-ROUTE-CHAIN` | `routeChainValid`; refinement to `routeValid`; connected positive and disconnected negative witnesses | `RouteChain.lean` |
| `W14-ROUTE-FEE` | Floor-vs-ceiling fee separation; capacity/`htlcMinimum`/`htlcMaximum` usability carrier | `RouteFeeCapacity.lean` |
| `W14-MPP` | Additive `settleGe`/`≥ total` completion; exact-implies-ge; overpay/underpay witnesses | `MppSettlement.lean` |
| `W14-FEE-UPDATE` | Checked fee-update legality; funder/phase/sufficiency; zero-fee/shared-anchor sidecar | `FeeUpdateLegality.lean` |
| `W14-DELIVERY` | Explicit delivery oracle/model; bounded-to-eventual; zero/fixed-delay and no-delivery instances | `DeliveryModel.lean` |
| `W14-READY` | `UsableChannel`/`Readiness` carrier; two-flag gate separation and positive refinement | `ReadyUsefulness.lean` |
| `W14-ASSURANCE` | Offline assurance checker with report/strict/self-test; 72 unprinted / 35 unregistered exposed | `AssuranceAudit.lean`, `scripts/check-assurance-coverage.py` |
| `W14-UNIFIED` | Fatal/retryable/succeeded unified-send model; fatal does not fall back | `UnifiedSendFatal.lean` |

## Gate evidence

| Check | Result |
|---|---|
| `lake build` | **RC 0**, `Build completed successfully (330 jobs)` |
| `check.sh` | **RC 0**, `files=291 obligations=82 sorry_in_proofs=0` |
| `check-final.py` | **RC 0**, 291 Lean files, 289 root imports, D=33 E=15 F=15 |
| `check-catalog.py --audit` | **RC 0**, 51 proved, 0 statement-only, 294 occurrences (282 unique), 0 unresolved, 0 proved failures, 0 candidates, 12,374 declarations |
| `check-conformance.py` | **RC 0**, 200 Lean references, 22/22 mutation controls, 6 finite BOLT 2 vectors, five live BOLT 2 payloads (`funding_created`, `funding_signed`, `channel_ready`, `open_channel`, `accept_channel`) |
| `verify-vendor.sh` | **RC 0**, 149 files |
| `verify-anchors.py` | **RC 0**, 315 anchors, 0 bad, 2 unanchored rows |
| `AxiomAudit` | **RC 0**, 423 `#print axioms` commands over a 465-name registry; permitted axioms only; 30 new Wave 14 headline entries |
| `check-assurance-coverage.py --report` | **RC 0**, 294 occurrences / 282 unique, 423 prints / 465 registry, 72 unprinted, 35 unregistered, 42 registry-only, 0 traceability mismatches |
| `check-assurance-coverage.py --strict` | **RC 1**, intentional until the 72/35 gap is closed |
| `check-assurance-coverage.py --self-test` | **RC 0**, both injected faults detected |
| Exact `sorry` scan | **0** matching lines |

## Remaining boundaries

- `REV-01`–`REV-07` are **narrowed**, not production-wired. The corrected
  carriers are additive; the old consumers still exist.
- `REV-08` (LDK Server pin alignment) is unchanged and external.
- `REV-09` is closed by the catalog docstring and occurrence/unique wording
  fixes.
- The assurance checker exposes the remaining **72** unique catalog targets not
  printed and **35** absent from the registry. It is not wired into CI yet
  because strict mode is currently red by design.
- No external L1/Noise/EUF-CMA/source barrier moved. No claim of full Lightning
  verification, node-level conformance, or production consumer integration.
- `origin/main` was not touched. The wave is published non-force on
  `repair/integrated`; no history was rewritten.

## Publication

The code commit `f0a3c07` is followed by a docs-only status checkpoint on
`wave-14/16`. The final push is non-force to `origin/repair/integrated` after
fetching the remote tip; if the remote advanced, the parent merges it
non-force before pushing.
