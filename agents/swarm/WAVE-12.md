# Wave 12 — address wire, coverage consumer, funding conformance, barrier audit

**Base:** `5ddab4c` (`repair/integrated`, wave-11 status tip)
**Status:** complete and integrated by the parent; publication pending.
**Catalog:** 51 rows / 294 targets; no new rows.

## Lanes and disjoint ownership

| Lane | Issue(s) | Exclusive files | Deliverable |
|---|---|---|---|
| `S12-RT-ADDRESS` | `RT-02` | `LnLean/Proofs/Routing/NodeAddressTargets.lean`, `agents/reports/swarm12/S12-RT-ADDRESS.md` | Corrected BOLT 7 address wire model: `u16 addrlen` and typed descriptors with exact widths, ordering, nonzero ports, at-most-one DNS, round-trip/injectivity, rejection theorems |
| `S12-PR-CONSUMER` | `PR-02` / `LN-PR-004` | `LnLean/Proofs/Channel/CoverageConsumerTargets.lean`, `agents/reports/swarm12/S12-PR-COVERAGE-CONSUMER.md` | Explicit coverage-consumer contract; full-record vs wire-determined determinacy and separation witnesses |
| `S12-CONF-FUNDING` | `CONF-01` | `tests/conformance/rust-lightning/**`, `scripts/check-conformance.py`, `LnLean/Proofs/ConformanceDiffTargets.lean`, `agents/reports/swarm12/S12-CONF-FUNDING.md` | Live `funding_created` (34) and `funding_signed` (35) fixtures/probe and Lean targets |
| `S12-AUDIT-BARRIERS` | P0/P1 audit | `agents/reports/swarm12/S12-AUDIT-BARRIERS.md` | Independent non-vacuity and barrier review; no shared-file edits |

## Acceptance rules

- No lane edits `LnLean/Proofs/Obligations.lean`, `Traceability.lean`,
  `AxiomAudit.lean`, the root import aggregator, or Git history.
- Every target must be a named, sorry-free theorem with explicit hypotheses;
  no vacuous projection may be presented as a substantive result.
- The parent reviews every lane, integrates only faithful results, and records
  rejected drafts and exact blockers.
- Conformance additions must preserve the finite/public-API caveat and include
  mutation controls and provenance hashes.

## Parent integration result

- `NodeAddressTargets`: ten targets added to `LN-RT-002`; `RT-02` remains
  blocked on chain-existence policy and a production gossip pipeline.
- `CoverageConsumerTargets`: eight targets added to `LN-PR-004`.
- `ConformanceDiffTargets`: ten funding-message targets; 200 Lean references,
  22/22 mutation controls, 26 differential fixtures, five live BOLT 2 payloads.
- `Traceability`: declaration snapshot refactored to ID-indexed entries so the
  quadratic membership/nodup checks stay kernel-checked without exceeding the
  default Lean memory limit; exact target spelling remains enforced by the
  strict catalog audit.
- `AxiomAudit`: 435 audited entries.
- Gate: build 314 jobs; catalog 51/51 / 294 targets / 11,898 declarations;
  275 Lean files / 273 root imports; 313 anchors; 149 vendor files; zero actual
  `sorry` or forbidden constructs.
