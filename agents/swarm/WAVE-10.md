# Wave 10 — domain boundaries, transport auth, PoP, coverage witnesses, node identity, live messages

**Status:** complete and integrated.

**Base commit:** `9158592` (wave-9 integration + gate docs)
**Branch:** `repair/integrated`
**Catalog at launch:** 48 proved / 0 statementOnly / 142 targets
**Full build at launch:** 300 jobs, RC 0
**Axiom audit at launch:** 269 theorems
**Roadmap:** `docs/OPEN-ISSUES.md`
**Protocol:** `docs/SWARM-LOOP.md`

Wave 9 characterized the remaining boundaries but deliberately did not close
them. Wave 10 attacks the next layer:

* whether a canonical tag can repair the `DigestBindsMod` failure, or whether
  the raw-residue interface is fundamentally unable to bind bytes;
* what transport authentication must supply before `EnvelopeAttributed` can be
  derived rather than assumed;
* whether a concrete challenge-response proof-of-possession protocol can
  discharge `PopSound`/`PopProducedBy`, or which unforgeability law remains;
* whether the missing `commitment_signed` coverage data can be characterized
  as a minimal witness and decoded constructively;
* how node-ID rotation and wire membership behave once the node store is
  canonical;
* whether additional BOLT 2 messages can be live-compared with the pinned
  rust-lightning encoder.

Six lanes run in parallel with exclusive files. No lane commits, pushes, edits
`LnLean.lean`, `Obligations.lean`, `Traceability.lean`, `AxiomAudit.lean`, the
shared catalog, or docs owned by another lane; the parent integrates and
records the gate.

## Lanes

| Lane | Issue(s) | Owned files | Deliverable / acceptance |
|---|---|---|---|
| `S10-L1-EC-DOMAIN` | `L1-01`, `L1-07` | new `LnLean/Proofs/Bitcoin/EcdsaDomainTargets.lean`, report | Decide whether any tag repairs `DigestBindsMod`. Prove the sharpest general collision/impossibility, or a faithful conditional domain theorem with an explicit collision-resistant/digest hypothesis. Do not edit `EcdsaConcreteTargets.lean` or the vendor model. |
| `S10-L1-TRANSPORT-AUTH` | `L1-03` | new `LnLean/Proofs/Protocol/TransportAuthTargets.lean`, report | Model transport authentication/provenance above `OpenChannelEnvelope`; derive `EnvelopeAttributed` from explicit session/key-binding laws, prove a concrete non-vacuous route, and retain the no-auth/wrong-key counterexample. Do not edit `OpenChannelRoutingTargets.lean` or core handshake files. |
| `S10-PR-POP-DERIVE` | `PR-01` | new `LnLean/Proofs/Crypto/PopProtocolTargets.lean`, report | Model a challenge-response PoP protocol over the existing key model; prove honest completeness and conditional soundness/attribution, derive as much of `PopSound`/`PopProducedBy`/`KeyBinding` as possible, and retain the replay/no-challenge counterexample. Do not edit `AttributionGameTargets.lean`. |
| `S10-PR-COVERAGE-WITNESS` | `PR-02` | new `LnLean/Proofs/Channel/CoverageWitnessTargets.lean`, report | Characterize the missing `commitment_signed` coverage data as a witness; construct a decoder from `CommitmentSigned` + witness, prove the legacy-only decoder impossible, and show the witness is necessary. Do not edit `PreimageCoverageTargets.lean` or core message records. |
| `S10-RT-NODE-IDENTITY` | `RT-02` | new `LnLean/Proofs/Routing/NodeIdentityTargets.lean`, report | Model node-ID rotation/linkage and wire-level node membership; prove an unlinkability/impossibility boundary without a rotation witness, a linkage theorem with one, and a membership admission theorem/counterexample. Do not edit `NodeCanonicalTargets.lean` or `Gossip.lean`. |
| `S10-CONF-LIVE-MSGS` | `CONF-01` | `tests/conformance/**`, `scripts/check-conformance.py`, `LnLean/Proofs/ConformanceDiffTargets.lean`, report | Add at least one additional live BOLT 2 message row (prefer `open_channel` or `accept_channel`) through pinned rust-lightning `Writeable`; preserve existing rows and mutation controls; otherwise record the exact blocker. Do not edit docs or the catalog. |

## Integration rules

- Each lane gets exclusive files and a report path
  `agents/reports/swarm10/S10-<LANE>.md`.
- Lanes may run scoped builds. Use
  `LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock lake build ...`;
  no concurrent un-locked Lean build.
- No `sorry`, `axiom`, `admit`, `native_decide`, `unsafe`, or
  `@[implemented_by]`. Allowed axioms: `propext`, `Quot.sound`,
  `Classical.choice`.
- Preserve mechanized counterexamples and the strongest true conditional form.
  A narrowed/blocked result is acceptable; a fake proof is not.
- If a requested change touches a forbidden shared file, implement the additive
  part in an owned module and report the exact integration patch.
- The parent integrates only sorry-free, faithful results, then updates the
  catalog, traceability, audit, generated indexes, roadmap, and gate record.

## Integration result

- Five new proof modules are root-imported:
  `EcdsaDomainTargets`, `TransportAuthTargets`, `PopProtocolTargets`,
  `CoverageWitnessTargets`, and `NodeIdentityTargets`. The conformance lane
  extended `ConformanceDiffTargets.lean` in place.
- The catalog remains 48 rows, all `proved`; six rows (`LN-L1-001`,
  `LN-L1-004`, `LN-PR-001`, `LN-PR-003`, `LN-PR-004`, `LN-RT-002`) were
  strengthened from **142 to 198 targets**. `AxiomAudit` now covers **323**
  theorems; only `propext`, `Quot.sound`, and `Classical.choice` occur.
- The live conformance suite now has **185** Lean references and **16/16**
  mutation controls, with both `channel_ready` and `open_channel` payloads
  encoded through the pinned public rust-lightning encoder.
- Wave-10 gate: **305 build jobs, RC 0; 266 Lean files; 264 root imports;
  10,968 declarations; 311 anchors; 149 vendor files; zero actual `sorry` or
  forbidden constructs.**
- `L1-01`/`L1-07` retain the EC/EUF-CMA boundary with the new tag-independent
  obstruction; `L1-03`, `PR-01`, `PR-02`, and `RT-02` are narrowed but remain
  open. `CONF-01` remains finite/public-API conformance, not node interop.

## Launch state

- Base `9158592`; `origin/main` remains `b891a59`.
- Wave 10 had no catalog target additions until integration; the launch commit
  only recorded the lane plan and status.
