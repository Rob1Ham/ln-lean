# Wave 9 integration status

**Base:** `93fa943` (wave-H merge of `50e8b5c` and `14d9a62`)
**Branch:** `repair/integrated`
**Result:** six lanes integrated; gates green; checkpoint prepared for non-force
push to `origin/repair/integrated`.

## Modules

- `LnLean/Proofs/Bitcoin/EcdsaConcreteTargets.lean`
- `LnLean/Proofs/Channel/PreimageCoverageTargets.lean`
- `LnLean/Proofs/Crypto/AttributionGameTargets.lean`
- `LnLean/Proofs/Protocol/OpenChannelRoutingTargets.lean`
- `LnLean/Proofs/Routing/NodeCanonicalTargets.lean`

`ConformanceDiffTargets.lean` was extended in place for the live
`channel_ready` row; no new Lean file was added by that lane.

## Catalog and audit

- Catalog: 48 rows, 48 proved, 0 statement-only, 0 unresolved, **142 targets**,
  10742 declarations.
- Six existing rows strengthened: `LN-L1-001`, `LN-L1-004`, `LN-PR-001`,
  `LN-PR-003`, `LN-PR-004`, `LN-RT-002`.
- `AxiomAudit`: **269** theorems; only `propext`, `Quot.sound`,
  `Classical.choice`.
- Added 42 target strings (37 unique declarations after the shared EC targets
  in `LN-L1-001`/`LN-L1-004`).

## Gate

| Check | Result |
|---|---|
| `lake build` | 300 jobs, RC 0 |
| `check-catalog.py --audit` | 48/48 proved, 142 targets, 0 unresolved, RC 0 |
| `check-catalog.py --allow-planned` | 48/0/0 planned, RC 0 |
| `check.sh` | `files=261 obligations=82 sorry_in_proofs=0`, RC 0 |
| `check-final.py` | 261 files, 259 root imports, RC 0 |
| `check-conformance.py` | 180 refs, 14/14 controls, 1 live message row, RC 0 |
| `verify-anchors.py` | 310 anchors, 0 bad, 2 unanchored, RC 0 |
| `verify-vendor.sh` | 149 files, RC 0 |
| Forbidden/sorry scan | no actual forbidden constructs; 0 proof `sorry` |

## Preserved boundaries

- `RT-02` remains open and narrowed to rotation identity and wire membership.
- `L1-01`/`L1-04`/`L1-07` remain open; the concrete EC bridge is characterized
  as total-reject-only at the current `ByteArray` interface, with no
  unconditional ECDSA claim.
- `L1-03` keeps transport authentication/C3 and key ownership explicit.
- `PR-01` keeps `KeyBinding`, `PopSound`, and `PopProducedBy` explicit.
- `PR-02` remains mitigated; legacy wire-only coverage is still negative.
- `CONF-01` is finite/public-API conformance for one live message row, not
  node-level interop.
