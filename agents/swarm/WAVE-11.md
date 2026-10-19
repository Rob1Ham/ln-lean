# Wave 11 — node-identity chains, Noise binding, live accept_channel, coverage sources, finite finality, invoices, aggregate HTLCs, non-vacuity

**Status:** complete and integrated.

**Base commit:** `4037264` (wave-10 integration + gate/docs)
**Branch:** `repair/integrated`
**Catalog at launch:** 48 proved / 0 statementOnly / 198 targets
**Full build at launch:** 312 jobs, RC 0 (wave-10 tree)
**Axiom audit at launch:** 323 theorems
**Roadmap:** `docs/OPEN-ISSUES.md`
**Protocol:** `docs/SWARM-LOOP.md`

Wave 10 characterized the transport/authentication, PoP, coverage, node-identity,
EC-domain, and second-live-message boundaries. Wave 11 attacks the next layer
with eight disjoint lanes:

* build an explicit signed rotation chain, preserve wire membership through
  re-signing, and characterize replay/rate limits;
* model a Noise_XK-shaped handshake and AEAD session so that
  `SessionKeyBinding` is derived from handshake laws rather than assumed;
* add a third live BOLT 2 payload (`accept_channel`, type 33) without claiming
  node-level interop;
* characterize full-record, out-of-band, and protocol-extension coverage
  sources and keep the legacy-wire insufficiency boundary;
* connect the finite reorg/retention layer to a bounded-depth block-graph
  finality theorem and preserve the deep-reorg counterexample;
* model the pre-bech32 BOLT 11 field list, including payment-hash/secret
  binding and malformed/duplicate-field rejection;
* extend coverage and fee accounting from one HTLC to an aggregate with an
  explicit no-aliasing/no-duplication law and a separation counterexample;
* mechanize a witness registry for core carriers and predicates, including the
  `withVendorEcdsa` vacuity result.

## Lane acceptance

| Lane | Issue(s) | Owned files | Acceptance |
|---|---|---|---|
| `S11-RT-NODE-CHAIN` | `RT-02` | new `LnLean/Proofs/Routing/NodeIdentityChainTargets.lean`, report | Signed rotation certificate and transitive chain; re-signing preserves wire membership; old signatures fail; per-node timestamp/sequence replay limits |
| `S11-L1-NOISE-AUTH` | `L1-03` | new `LnLean/Proofs/Protocol/NoiseTransportTargets.lean`, report | Handshake/session model; AEAD acceptance and provenance; nonce freshness/replay rejection; derived `SessionKeyBinding`; concrete attributed delivery |
| `S11-CONF-MESSAGES` | `CONF-01` | `tests/conformance/**`, `scripts/check-conformance.py`, `LnLean/Proofs/ConformanceDiffTargets.lean`, report | Live `accept_channel` type-33 payload, 190 Lean references, 18/18 mutation controls |
| `S11-PR-COVERAGE-SOURCE` | `PR-02` | new `LnLean/Proofs/Channel/CoverageSourceTargets.lean`, report | Full-record/out-of-band/extension sources; exactness, separation, legacy-wire insufficiency |
| `S11-L1-FINALITY` | `L1-06` | new `LnLean/Proofs/Security/ChainFinalityTargets.lean`, report | Finite block graph; bounded-depth finality; unique-tip form; deep-reorg counterexample; retention bridge |
| `S11-PAY-INVOICE` | `LN-PM-001`–`003`, new `LN-PM-007` | new `LnLean/Proofs/Payment/InvoiceWireTargets.lean`, report | Field-list parse/print round-trip and injectivity; malformed/duplicate rejection; payment-hash/secret binding; signature-vs-payment separation |
| `S11-HTLC-AGGREGATE` | new `LN-CH-007` | new `LnLean/Proofs/Channel/HtlcAggregateTargets.lean`, report | Aggregate coverage projection; no-double-spend separation; aliasing counterexample; exact fee/weight accounting |
| `S11-MODEL-NONVACUITY` | new `LN-SEC-007` | new `LnLean/Proofs/Model/NonVacuityTargets.lean`, report | 30-entry witness registry; `withVendorEcdsa` accepts nothing; carrier/relation separation |

## Parent integration

* Root imports added for all seven new proof modules.
* Catalog: `LN-CH-007`, `LN-PM-007`, and `LN-SEC-007` added; seven existing
  rows strengthened; `EXPECTED_ROWS` is 51.
* Traceability: id tables, target/proved tables, declaration snapshot, and
  module list regenerated. Per-area counts are `[6,6,7,6,6,6,7,7]`.
* Axiom audit extended from 323 to 407 named theorems. The audit output contains
  only `propext`, `Quot.sound`, and `Classical.choice`.
* Conformance: live `accept_channel` row and 18/18 mutation controls.
* Living docs: `README.md`, `docs/THEOREM-INDEX.md`, `docs/TRACEABILITY.md`,
  `docs/FINAL-STATUS.md`, `docs/WAVE-STATUS.md`, `docs/OPEN-ISSUES.md`,
  `agents/TODO-REPAIR.md`, and `docs/RELEASE-CHECKLIST.md` refreshed.

## Gate at integration

| Check | Result |
|---|---|
| `lake build` | 312 jobs, RC 0 |
| `check-catalog.py --audit` | 51 proved / 0 statement-only / 277 targets / 0 unresolved / 0 proved failures / 11743 declarations |
| `check.sh` | `files=273 obligations=82 sorry_in_proofs=0`, RC 0 |
| `check-final.py` | 273 Lean files, 271 root imports, D=33 E=15 F=15, RC 0 |
| `check-conformance.py` | 190 Lean references, 18/18 mutation controls, 3 live BOLT 2 payloads, RC 0 |
| `verify-vendor.sh` | 149 files, RC 0 |
| `verify-anchors.py` | 311 anchors, 0 bad, 2 unanchored rows, RC 0 |
| `AxiomAudit` | 407 theorems, permitted axioms only, RC 0 |

## Boundaries retained

* `NoiseTransportTargets` proves session binding under explicit handshake/AEAD
  laws; it does not claim computational security or a deployed Noise
  implementation.
* `ChainFinalityTargets` is a finite block-graph bounded-depth result, not a
  PoW/probabilistic/live-chain model.
* `InvoiceWireTargets` models a pre-bech32 field list, not bech32/HRP/checksum
  or signable-digest correctness.
* `CoverageSourceTargets` preserves the legacy-wire insufficiency; production
  coverage still requires an out-of-band/full-record source or a protocol
  change.
* `HtlcAggregateTargets` requires explicit no-aliasing/no-duplication laws.
* `NonVacuityTargets` is a witness registry, not a proof that every catalog row
  is non-vacuous.
* The live `accept_channel` row is finite/public-API conformance, not
  node-level interop.
