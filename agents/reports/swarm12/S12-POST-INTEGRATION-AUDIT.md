# S12-POST-INTEGRATION-AUDIT — wave-12 closure and wave-13 decision

**Date:** 2026-10-19
**Repository:** `/home/ubuntu/ln-lean-repair`
**Branch:** `repair/integrated`
**Code gate audited:** `d210079` (`[WAVE12]` integration)
**Status tip at audit:** `07288ad` (docs-only status commits)
**Mode:** read-only review of the integrated tree; no lane edits, no new code.

## 1. Integrated wave-12 artifacts

The two wave-12 proof modules are now tracked, root-imported, and included in
the axiom audit:

* `LnLean/Proofs/Routing/NodeAddressTargets.lean` — ten `LN-RT-002` targets.
  It models the real BOLT 7 `u16 addrlen` address blob and typed descriptors,
  with exact 6/18/12/37-byte layouts, nonzero ports, ascending type order, at
  most one type 5, canonical round-trip/injectivity, and explicit rejection
  theorems. The earlier `u8`-count draft and its `sorry` are not present.
* `LnLean/Proofs/Channel/CoverageConsumerTargets.lean` — eight `LN-PR-004`
  targets. It defines an explicit consumer contract separating full-record
  coverage from wire-determined consumer determinacy, with separation
  witnesses showing a legacy wire record cannot reconstruct the source.

The conformance lane added live `funding_created` (type 34) and
`funding_signed` (type 35) fixtures and Lean targets. The suite now checks 200
Lean references, 22/22 mutation controls, 26 differential fixtures, and five
live BOLT 2 payloads. This remains finite/public-API conformance, not a
node-level interoperability test.

The historical post-freeze addendum in `S12-AUDIT-BARRIERS.md` described the
address module while it was still an untracked draft with a `sorry`. That
snapshot is superseded: the corrected module is now imported, sorry-free, and
part of the gate.

## 2. Gate reproduced at the integrated tree

* Full build: **314 jobs, RC 0**.
* Strict catalog: **51/51 proved, 0 statement-only, 294 targets, 0 unresolved,
  0 proved failures, 0 candidates, 11,898 declarations**.
* Source policy: `files=275 obligations=82 sorry_in_proofs=0`, `check: OK`.
* File/import check: 275 Lean files, 273 root imports, D=33 E=15 F=15.
* Conformance: PASS; 200 Lean references, 22/22 mutation controls, 26
  differential fixtures, five live BOLT 2 payloads.
* Anchors: 313 checked, 0 bad, 2 unanchored rows.
* Vendor: 149 files, checksums OK.
* Axiom audit: 435 entries; permitted set is exactly
  `propext`, `Quot.sound`, and `Classical.choice` (the `choice` short name
  printed inside `open Classical` is `Classical.choice` when checked at root).
* Exhaustive code scan: zero actual `sorry`, `axiom`, `admit`,
  `native_decide`, `unsafe`, or `@[implemented_by]`.

## 3. Remaining P0/P1 verdicts

No new tractable P0/P1 proof lane was found.

| Issue | Verdict after wave 12 |
|---|---|
| `L1-01`, `L1-07` | Mechanically blocked at the untyped `ByteArray` EC interface: the vendored verifier is zero-padding invariant and `PrimitiveModel.ecdsa_eufCma` makes the bridge total-rejecting. A typed-digest interface is a model change requiring maintainer sign-off, not a proof of the existing claim. |
| `L1-02` | Externally blocked on a concrete secp256k1 verifier and actual spent amount/context. No `TxValidation.Full` transfer gap remains. |
| `L1-03` | Externally blocked on a real Noise_XK/AEAD implementation, C3, and key ownership. The current model only derives a flag/key-equality boundary. |
| `PR-01` | Externally blocked on a real EUF-CMA/PoP extraction theorem and key ownership; `selfSigModel` is explicitly a toy witness. |
| `PR-02` | Externally blocked on a production out-of-band/full-record coverage source or a protocol change. The model-level source/consumer contract is now closed. |
| `RT-02` | Address parsing/canonicality is now modelled and proved; chain-existence policy, cryptographic rotation identity, and the production gossip pipeline remain external. |
| `OPS-02` | Human legal decision: no project `LICENSE`/`NOTICE`. |
| `OPS-03` | Human release decision: no tag and no `main` merge. |

## 4. Wave-13 decision

No wave-13 proof lane is launched. The only proposed model-level extension is
the optional typed-digest change for `L1-01`/`L1-07`, which changes the
meaning of the funding-signature interface and requires maintainer approval.
Creating more finite Noise/PoP/coverage models would repeat definitional
boundaries without closing the external requirement. The branch therefore
stops at the wave-12 checkpoint with the remaining P0/P1 rows reduced to
explicit, mechanized or external barriers and the release decisions left to a
human.
