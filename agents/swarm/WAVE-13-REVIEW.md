# Wave 13 review — 32-lane remaining-work scope

**Base:** `f7f0628` (`repair/integrated`)

**Mode:** read-only review. No Lean, docs, tests, vendor, or catalog edits by lanes; each lane writes one report.

**Concurrency:** 8 lanes at a time; R32 runs only after R01–R31 finish.

## Pinned external datapoints

| Repository | Commit | Local read-only path |
|---|---|---|
| `lightningdevkit/ldk-node` | `fa123fed131e27ecc420b77fa7086fcf1ddaebb8` | `/tmp/opencode/ldk-refs/ldk-node` |
| `lightningdevkit/ldk-server` | `c17dc11dde38f88c53457039ddf30c6b90a63ba2` | `/tmp/opencode/ldk-refs/ldk-server` |

These are review datapoints, not vendored dependencies.

## Lanes

| Lane | Scope | Brief | Report |
|---|---|---|---|
| `R01` | L1 script, interpreter, and EC-verifier boundary | `agents/briefs/wave13-review/R01.md` | `agents/reports/wave13-review/R01-l1-script-ec-boundary.md` |
| `R02` | L1 transaction construction, sighash, PSBT, fees, and weight | `agents/briefs/wave13-review/R02.md` | `agents/reports/wave13-review/R02-l1-tx-sighash-fees.md` |
| `R03` | Chain sync, confirmations, reorgs, and finality | `agents/briefs/wave13-review/R03.md` | `agents/reports/wave13-review/R03-l1-chain-sync-finality.md` |
| `R04` | On-chain wallet, UTXOs, balances, and coin control | `agents/briefs/wave13-review/R04.md` | `agents/reports/wave13-review/R04-l1-wallet-utxo-balance.md` |
| `R05` | Channel lifecycle and peer/funding handshake | `agents/briefs/wave13-review/R05.md` | `agents/reports/wave13-review/R05-channel-lifecycle.md` |
| `R06` | Commitment state, fees, dust, and anchor outputs | `agents/briefs/wave13-review/R06.md` | `agents/reports/wave13-review/R06-commitments-fees-dust-anchors.md` |
| `R07` | HTLC add/fulfill/fail, forwarding, and fee accounting | `agents/briefs/wave13-review/R07.md` | `agents/reports/wave13-review/R07-htlc-forwarding-fees.md` |
| `R08` | Close, force-close, revocation, watchtowers, and backup | `agents/briefs/wave13-review/R08.md` | `agents/reports/wave13-review/R08-close-revocation-watchtower.md` |
| `R09` | BOLT 4 onion construction, processing, and errors | `agents/briefs/wave13-review/R09.md` | `agents/reports/wave13-review/R09-bolt4-onion.md` |
| `R10` | BOLT 11 invoice parse/create/sign/verify/expiry | `agents/briefs/wave13-review/R10.md` | `agents/reports/wave13-review/R10-bolt11-invoices.md` |
| `R11` | BOLT 12 offers, invoice requests, refunds, and payer proofs | `agents/briefs/wave13-review/R11.md` | `agents/reports/wave13-review/R11-bolt12-offers.md` |
| `R12` | Payment lifecycle, retries, MPP, keysend, and probing | `agents/briefs/wave13-review/R12.md` | `agents/reports/wave13-review/R12-payment-lifecycle.md` |
| `R13` | BOLT 7 gossip validation, store, and epochs | `agents/briefs/wave13-review/R13.md` | `agents/reports/wave13-review/R13-bolt7-gossip-store.md` |
| `R14` | BOLT 7 node announcements, addresses, chain hash, rotation | `agents/briefs/wave13-review/R14.md` | `agents/reports/wave13-review/R14-bolt7-node-announcements.md` |
| `R15` | BOLT 8 transport, Noise, and TLS/API security | `agents/briefs/wave13-review/R15.md` | `agents/reports/wave13-review/R15-bolt8-transport.md` |
| `R16` | Routing, scoring, pathfinding, and liquidity | `agents/briefs/wave13-review/R16.md` | `agents/reports/wave13-review/R16-routing-scoring-liquidity.md` |
| `R17` | LDK Node builder, config, persistence, data store, and restart | `agents/briefs/wave13-review/R17.md` | `agents/reports/wave13-review/R17-ldk-node-builder-persistence.md` |
| `R18` | LDK Node events, background processing, and message dispatch | `agents/briefs/wave13-review/R18.md` | `agents/reports/wave13-review/R18-ldk-node-events-runtime.md` |
| `R19` | Liquidity, LSPS, JIT channels, and async payments | `agents/briefs/wave13-review/R19.md` | `agents/reports/wave13-review/R19-liquidity-jit-async.md` |
| `R20` | LDK Node public API, FFI, and bindings compatibility | `agents/briefs/wave13-review/R20.md` | `agents/reports/wave13-review/R20-ldk-node-api-ffi.md` |
| `R21` | LDK Server API surface, auth, macaroons, and request binding | `agents/briefs/wave13-review/R21.md` | `agents/reports/wave13-review/R21-ldk-server-api-auth.md` |
| `R22` | LDK Server config, TLS, Tor, metrics, and operations | `agents/briefs/wave13-review/R22.md` | `agents/reports/wave13-review/R22-ldk-server-ops-config.md` |
| `R23` | LDK Server e2e tests, MCP, gRPC, and CLI/client | `agents/briefs/wave13-review/R23.md` | `agents/reports/wave13-review/R23-ldk-server-e2e-mcp.md` |
| `R24` | LDK Server payment, channel, and on-chain API semantics | `agents/briefs/wave13-review/R24.md` | `agents/reports/wave13-review/R24-ldk-server-payment-channel-api.md` |
| `R25` | Splicing | `agents/briefs/wave13-review/R25.md` | `agents/reports/wave13-review/R25-splicing.md` |
| `R26` | Dual funding, interactive tx, and channel negotiation | `agents/briefs/wave13-review/R26.md` | `agents/reports/wave13-review/R26-dual-funding-negotiation.md` |
| `R27` | Anchor channels, zero-fee commitments, and commitment upgrades | `agents/briefs/wave13-review/R27.md` | `agents/reports/wave13-review/R27-anchor-zero-fee-upgrades.md` |
| `R28` | Async payments, trampoline, onion messages, and unified BOLT 12 | `agents/briefs/wave13-review/R28.md` | `agents/reports/wave13-review/R28-async-trampoline-offers.md` |
| `R29` | Catalog coverage matrix against LDK behavior | `agents/briefs/wave13-review/R29.md` | `agents/reports/wave13-review/R29-catalog-coverage-matrix.md` |
| `R30` | Conformance strategy for LDK Node and LDK Server | `agents/briefs/wave13-review/R30.md` | `agents/reports/wave13-review/R30-conformance-strategy.md` |
| `R31` | Non-vacuity, traceability, axiom, and assumption review | `agents/briefs/wave13-review/R31.md` | `agents/reports/wave13-review/R31-nonvacuity-assurance.md` |
| `R32` | Synthesis and wave-13/14 roadmap | `agents/briefs/wave13-review/R32.md` | `agents/reports/wave13-review/R32-synthesis.md` |

## Lane contract

- Read-only inspection; no branch changes, commits, pushes, or builds of the full tree.
- Exactly one writable path: the lane report.
- Classify behavior as covered / partial / missing / contradicted / external, with exact `file:line` evidence from the pinned LDK refs and the Lean tree.
- Propose 3–8 named Lean targets with explicit hypotheses, a non-vacuity witness, and a fidelity/priority assessment.
- Flag any proposal that would weaken an existing theorem, hide an assumption, or be vacuous.
- R32 deduplicates R01–R31 into a ranked wave-13/14 plan with disjoint ownership and gate criteria.
