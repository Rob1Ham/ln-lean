# Wave 11 integration status

**Base:** `4037264` (wave-10 integration)
**Code commit:** `6a48d41` (`[WAVE11]` integration)
**Branch:** `repair/integrated`
**Result:** eight lanes reviewed and integrated; source, build, conformance, and
axiom gates green; checkpoint prepared for a non-force push to
`origin/repair/integrated`.

## Modules

- `LnLean/Proofs/Routing/NodeIdentityChainTargets.lean` — signed rotation
  certificates, transitive authenticated chains, explicit re-signing with
  wire-membership preservation, old-signature counterexamples, and per-node
  timestamp/sequence rate limits.
- `LnLean/Proofs/Protocol/NoiseTransportTargets.lean` — Noise_XK-shaped
  handshake/session model, AEAD acceptance/provenance, nonce freshness/replay,
  derived `SessionKeyBinding`, and concrete attributed delivery.
- `LnLean/Proofs/Channel/CoverageSourceTargets.lean` — full-record,
  out-of-band, and protocol-extension coverage sources; exactness, separation,
  and legacy-wire insufficiency.
- `LnLean/Proofs/Security/ChainFinalityTargets.lean` — finite block graph,
  bounded-depth finality, unique-tip family form, sharp deep-reorg
  counterexample, and retention bridge.
- `LnLean/Proofs/Payment/InvoiceWireTargets.lean` — pre-bech32 BOLT 11
  field-list codec, parse/print round-trip and injectivity,
  duplicate/malformed rejection, payment-hash/secret binding, and
  signature-vs-payment separation.
- `LnLean/Proofs/Channel/HtlcAggregateTargets.lean` — aggregate HTLC coverage,
  no-double-spend separation, aliasing counterexample, and exact fee/weight
  accounting.
- `LnLean/Proofs/Model/NonVacuityTargets.lean` — 30-entry witness registry,
  `withVendorEcdsa` vacuity result, and carrier/relation separation.

`ConformanceDiffTargets.lean` was extended in place for the live
`accept_channel` (type 33) row; no new Lean file was added by that lane. The
harness/probe/fixture updates cover the live type-33 base case.

## Catalog and audit

- Catalog: **51 rows, 51 proved, 0 statement-only, 0 unresolved, 277 targets,
  11,743 declarations**.
- New rows: `LN-CH-007`, `LN-PM-007`, `LN-SEC-007`.
- Seven existing rows strengthened: `LN-L1-003`, `LN-RT-002`, `LN-PR-001`,
  `LN-PR-004`, `LN-PM-001`, `LN-PM-002`, and `LN-PM-003`.
- `AxiomAudit`: **407** theorems; only `propext`, `Quot.sound`,
  `Classical.choice`.
- Traceability now has 265 unique proved declarations and 68 referenced
  modules. The three transcribed tables are regenerated from the catalog.
- Per-area id counts are `[6,6,7,6,6,6,7,7]` in `idAreas` order.

## Gate

| Check | Result |
|---|---|
| `lake build` | 312 jobs, RC 0 |
| `check-catalog.py --audit` | 51/51 proved, 277 targets, 11,743 declarations, 0 unresolved |
| `check.sh` | `files=273 obligations=82 sorry_in_proofs=0`, RC 0 |
| `check-final.py` | 273 Lean files, 271 root imports, D=33 E=15 F=15, RC 0 |
| `check-conformance.py` | 190 Lean refs, 18/18 mutation controls, 3 live BOLT 2 payloads, RC 0 |
| `verify-anchors.py` | 311 anchors, 0 bad, 2 unanchored rows, RC 0 |
| `verify-vendor.sh` | 149 files, RC 0 |
| `AxiomAudit` | RC 0, 407 theorems, allowed axioms only |
| Exact `sorry` scan | 0 matching lines |

## Boundaries

- `L1-01` / `L1-07`: no unconditional ECDSA/consensus claim; no fixed tag
  repairs the untyped digest interface. A production repair must restrict the
  message encoding to the canonical domain or use a typed digest with an
  explicit computational hypothesis.
- `L1-03`: `SessionKeyBinding`, C3/key ownership, and the finite C1 funding
  admission remain explicit; the Noise model is not a computational-security
  claim.
- `L1-06`: finite graph finality only; no PoW/probabilistic/live-chain model.
- `PR-01`: `PopKeySoundOn`/`PopExtractionOn`, `EufCma`, and freshness remain
  explicit; no real signature scheme or computational EUF-CMA claim.
- `PR-02`: production coverage needs an out-of-band/full-record source or a
  protocol change; the legacy wire alone is insufficient.
- `RT-02`: identity across rotation is witness-based, not cryptographic;
  address parsing and a production rotation/announcement pipeline remain open.
- `LN-PM-007`: pre-bech32 field list only; not bech32/HRP/checksum or signable
  digest correctness.
- `LN-CH-007`: explicit no-aliasing/no-duplication laws remain hypotheses.
- `LN-SEC-007`: a witness registry, not a proof that every catalog row is
  non-vacuous.
- `CONF-01`: finite/public-API conformance only; not node-level interop.
