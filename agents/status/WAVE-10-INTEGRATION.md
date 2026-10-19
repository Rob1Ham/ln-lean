# Wave 10 integration status

**Base:** `9359475` (wave-9 integration)
**Code commit:** `db52cc9` (`[WAVE10] integrate domain, transport-auth, PoP,
coverage, node-identity, and live-message lanes`)
**Branch:** `repair/integrated`
**Result:** six lanes integrated; source and full build gates green; checkpoint
prepared for a non-force push to `origin/repair/integrated`.

## Modules

- `LnLean/Proofs/Bitcoin/EcdsaDomainTargets.lean` — no fixed tag repairs
  `DigestBindsMod`; canonical value-`< n` domain is the exact algebraic repair.
- `LnLean/Proofs/Protocol/TransportAuthTargets.lean` — authenticated session
  separated from explicit `SessionKeyBinding`; composition with the routed
  funding witness; no payload-only sender/attribution.
- `LnLean/Proofs/Crypto/PopProtocolTargets.lean` — concrete challenge-response
  PoP, fixed-width injectivity, honest completeness, conditional soundness,
  replay counterexamples.
- `LnLean/Proofs/Channel/CoverageWitnessTargets.lean` — constructive per-HTLC
  coverage decoder plus legacy-only impossibility.
- `LnLean/Proofs/Routing/NodeIdentityTargets.lean` — store-only rotation
  unlinkability, explicit witness linkage, wire-membership admission boundary.

`ConformanceDiffTargets.lean` was extended in place for the live `open_channel`
row; no new Lean file was added by that lane. The harness/probe/fixture updates
cover the live type-32 base case.

## Catalog and audit

- Catalog: 48 rows, 48 proved, 0 statement-only, 0 unresolved, **198 targets**,
  10,968 declarations.
- Six existing rows strengthened: `LN-L1-001`, `LN-L1-004`, `LN-PR-001`,
  `LN-PR-003`, `LN-PR-004`, `LN-RT-002`.
- `AxiomAudit`: **323** theorems; only `propext`, `Quot.sound`,
  `Classical.choice`.
- Traceability now has 186 unique proved declarations and 61 referenced
  modules. The three transcribed tables are regenerated from the catalog.

## Gate

| Check | Result |
|---|---|
| `lake build` | 305 jobs, RC 0 |
| `check-catalog.py --audit` | 48/48 proved, 198 targets, 10,968 declarations, 0 unresolved |
| `check.sh` | `files=266 obligations=82 sorry_in_proofs=0`, RC 0 |
| `check-final.py` | 266 Lean files, 264 root imports, D=33 E=15 F=15, RC 0 |
| `check-conformance.py` | 185 Lean refs, 16/16 mutation controls, 2 live BOLT 2 payloads, RC 0 |
| `verify-anchors.py` | 311 anchors, 0 bad, 2 unanchored rows, RC 0 |
| `verify-vendor.sh` | 149 files, RC 0 |
| `AxiomAudit` | RC 0, 323 theorems, allowed axioms only |
| Exact `sorry` scan | 0 matching lines |

## Boundaries

- `L1-01` / `L1-07`: no unconditional ECDSA/consensus claim; no fixed tag
  repairs the untyped digest interface. A production repair must restrict the
  message encoding to the canonical domain or use a typed digest with an
  explicit computational hypothesis.
- `L1-03`: `SessionKeyBinding`, C3/key ownership, and the finite C1 funding
  admission remain explicit; no Noise/MAC implementation is claimed.
- `PR-01`: `PopKeySoundOn`/`PopExtractionOn`, `EufCma`, and freshness remain
  explicit; no real signature scheme or computational EUF-CMA claim.
- `PR-02`: production coverage needs an out-of-band/full-record source or a
  protocol change; the legacy wire alone is insufficient.
- `RT-02`: identity across rotation is witness-based, not cryptographic; chain
  existence, address parsing, rate limits, and re-signing remain open.
- `CONF-01`: finite/public-API conformance only; not node-level interop.
