# Open Issues and Swarm Roadmap

**Status:** living roadmap after proof-wave 4; wave 5 running.
**Branch:** `repair/integrated`.
**Base commit:** `79a92ce` (wave 5 launch; proof-wave 4 code at `26ced90`).
**Catalog gate:** 48/48 rows `proved`, 0 `statement-only`, 0 unresolved,
61 targets.
**Full build:** 188 jobs, RC 0.
**Rule:** this file is updated by every wave. Closed issues keep their id and
get a `closed` row; new gaps get a new id in the same wave that discovers them.

The catalog is green, but the catalog is a model-level claim. The issues below
are the remaining distance between this tree and a credible public release or
a full Lightning verification claim. Do not turn an assumption into a theorem
by rewording it; add the missing model or keep the scope note.

## Priority summary

| Priority | Meaning | Current issues |
|---|---|---|
| **P0** | Blocks a public release or a reproducible build | `OPS-01`, `OPS-02`, `OPS-03` |
| **P0** | Blocks any claim of spendable L1 scripts | `L1-01`, `L1-02`, `L1-07` |
| **P1** | Major model/verification gap; codeable in a wave | `L1-03`, `L1-04`, `L1-05`, `PR-01`, `PR-02`, `CH-01`, `CH-02`, `CH-03`, `RT-01` |
| **P2** | Longer-term research / conformance / network assumptions | `CR-01`, `L1-06`, `NET-01`, `CONF-01`, `CONF-02`, `MODEL-01`, `MODEL-02`, `SEC-01`, `OPS-04` |

## Open issues

| Id | Priority | Status | Issue | Evidence / current boundary | Next action |
|---|---|---|---|---|---|
| `OPS-01` | P0 | open (mitigated) | Public CI cannot run the full build from a clean checkout | `vendor/btc-lean-core` is gitignored; the pinned snapshot `f950806` is not in public `btc-lean` history and no public artifact exists. `scripts/fetch-vendor.sh` now verifies or provisions an explicit local/URL/exact-git input against `vendor/VENDOR-SHA256` (119 files), returns a distinct skip code when no input is supplied, and `.github/workflows/ci.yml` always runs source gates while marking the build as not run; `REQUIRE_VENDOR_BUILD=true` turns a skip into failure. | Maintainer chooses: (a) publish a checksummed snapshot archive and set `VENDOR_ARTIFACT_URL` + `VENDOR_ARTIFACT_SHA256` (recommended), (b) commit the 119-file snapshot, or (c) keep the explicit skip gate. Publication also requires a provenance/license decision for the `wallet-peer` snapshot. |
| `OPS-02` | P0 | open; decision support ready | No `LICENSE` | No license file in the tree; `docs/LICENSE-DECISION.md` now provides a neutral MIT/Apache-2.0/dual matrix and third-party notice inventory | Maintainer chooses the license and copyright holder, then adds `LICENSE`/`NOTICE`; do not let an agent invent one |
| `OPS-03` | P0 | open; checklist ready | No release tag and `main` is behind | `origin/main` is old; `repair/integrated` is the active branch; no tag; `docs/RELEASE-CHECKLIST.md` now records the pre-tag gates and human choices | Decide PR/merge path to `main`, cut a signed/annotated tag, and publish release notes |
| `OPS-04` | P2 | open (new in wave 4) | Vendor snapshot contains an absolute symlink | `vendor/btc-lean-core/btc-lean-core` points at `/home/ubuntu/ln-lean/vendor/btc-lean-core`, is not in `VENDOR-SHA256`, and is rejected by archive provisioning. | Delete it before publishing a snapshot; keep the checksum manifest authoritative. |
| `L1-01` | P0 | open (mitigated) | P2WSH / `OP_CHECKMULTISIG` spendability is not bridged to the vendored interpreter | `SpendTargets.lean` defines an explicit stack-machine semantics, proves its serializer equal to the seam templates, and proves conditional 2-of-2 funding spends plus rejection cases. It is not a consensus interpreter; sighash is a parameter and CHECKMULTISIG is 2-of-2. | Import the vendored `Bitcoin/Interpreter/Defs.lean` evaluator and connect it to `SpendTargets`; keep the conditional model as the spec. |
| `L1-02` | P0 | open (mitigated) | `to_local` CSV/revocation script is structural plus abstract execution laws | `SpendTargets.lean` proves revocation-branch and delayed-branch spend theorems under `InterpreterLaws`; CSV is an abstract `csvOk` law, not `OP_CSV` execution. `LN-L1-004` keeps the full byte template. | Connect the vendored interpreter and prove `csvOk`/signature checks correspond to its actual `OP_CSV`/`OP_CHECKSIG` semantics. |
| `L1-03` | P1 | open | `FundingScriptHashLinked` is a construction invariant | `LN-L1-001` assumes `witnessScriptHash = H(witnessScript.bytes)`; the model does not construct it end-to-end | Add the funding-state constructor that establishes the link, or derive it from the funding handshake |
| `L1-04` | P1 | open | Anchor weight has an 8 WU spec/serialization gap | `LN-L1-006` proves `serializedAnchorWeight + 8 = 1124 + 172*k`; witness serialization and the Appendix A `count_tx_out` discrepancy remain | Model the missing witness/CompactSize bytes or document the negotiated fee-basis interpretation permanently |
| `L1-05` | P1 | open | C1 is 32-byte payment-preimage collision resistance, not 71-byte script injectivity | `c1_32_does_not_bind_funding_witnessScripts`; the P2WSH reverse direction uses a finite pair-level `CollisionFreeOn` admission | Keep the finite admission and add a construction lemma for the actual revealed script; do not assume global injectivity |
| `L1-06` | P2 | open | Reorg result is conditional on common tip and bounded depth | `LN-L1-003` keeps `SameChain`, common-prefix arithmetic, and `OutOfReachOf` explicit; deep reorgs have a separate failure mode | Connect the hypotheses to the L1 chain model or leave the conditional theorem as the deliverable |
| `L1-07` | P1 | open (new in wave 4) | Vendored real interpreter is not imported | `vendor/btc-lean-core/Bitcoin/Interpreter/Defs.lean` has `evalScriptBytes`, `verifyWitnessProgram`, `checkMultiSig`, and `verifyScriptFull`; the current build imports only four vendor modules. `SpendTargets` therefore uses `InterpreterLaws` plus an unproved `ConsensusSpendBridge`. | Import the vendored interpreter modules, prove the `SpendTargets` serializer/stack relation against them, and discharge or narrow `ConsensusSpendBridge`; this is the highest-value L1 next step. |
| `CR-01` | P2 | open | No computational cryptographic reductions | C1/C3/C8 are exact algebraic laws; no collision-finding, EUF-CMA, PRF, or advantage bounds | Write a limits document and, if desired, a separate computational-security development; do not claim reductions from the algebraic model |
| `PR-01` | P1 | open | `FundingSigningLaw` / `KeyBinding` are hypotheses | `LN-PR-003` proves validity and attribution only under explicit signing correctness and key binding; C3 alone is insufficient | Construct an honest signer in the primitive model and connect `accept_channel.funding_pubkey` to the signer key |
| `PR-02` | P1 | open (mitigated) | `CommitmentSigned` wire record lacks data for wire-only coverage | `CommitmentSignedFull` now carries commitment number, fee, digest, and per-HTLC signed entries, with `ProducedFrom`/`commitment_signed_full_covers` and retained legacy no-decoder negatives. There is still no BOLT 3 sighash serializer or C3 verification, so `sigAt`/digests remain explicit production data. | Add the BOLT 3 sighash serializer and C3 verification so digests/signatures are derived; then decide whether to make the full record a type-132 extension or keep it signer-side. |
| `CH-01` | P1 | open (mitigated) | Rich `CommitmentTx` model is not the legacy consumer path | `CommitmentIntegrationTargets.legacyOutputs_perm_commitmentOutputs` proves the legacy view is a permutation of `CommitmentTx.commitment.commitmentOutputs` under zero dust and nonzero local/remote outputs; D12 remains the unconditional refutation. | Add the core gross/net fields and migrate construction sites (`CH-03`); then prove a single canonical refinement rather than a zero-dust conditional. |
| `CH-02` | P1 | open (mitigated) | Second-stage fee and dust trimming are not integrated end-to-end | `CommitmentIntegrationTargets` computes timeout/success fees from the feerate, proves the exact dust threshold, the trimming partition, and BOLT 3 accounting. The rich `CommitmentHTLCOutput` still lacks a net/gross split, so the patch is explicit. | Add `netAmountSat`/`trimmedSat`/`effectiveFeeSat` to the core model (`CH-03`) and migrate construction sites. |
| `CH-03` | P1 | open (new in wave 4) | Rich commitment outputs lack BOLT-3 gross/net fields | The integration module keeps a net/gross split explicit because `CommitmentHTLCOutput` has only `amountSat` and `Commitment` has no trimmed total/effective fee. The lane report records the exact additive patch with defaults. | Add `netAmountSat`, `trimmedSat`, and `effectiveFeeSat`, switch the dust test to net, and migrate construction sites so `amountSat` is gross. |
| `HT-01` | P1 | closed (tagged namespace) | Untagged global HTLC id uniqueness is false under BOLT 2 per-sender counters | `LN-HT-004` keeps per-sender `dir_id_unique`, the `CrossDisjoint` untagged form, and now the direction-tagged `HTLCTag` namespace with `tagged_id_unique_of_reachable`/`tagged_ids_nodup_of_reachable`. `cross_direction_duplicate_tagged` connects the old counterexample. The wire remains per-sender by BOLT 2 design. | No further model action; keep the tag documented as a model-side namespace, not a new wire encoding. |
| `RT-01` | P1 | open (mitigated) | Gossip key attribution and raw insertion are separate | `admitGossipAttributed` gates updates on `signatureValid` plus `updateKeyAnnounced`; `gossip_graph_edges_update_attributed` ties reachable graph edges to a signed update and an announcement key. Raw `applyGossip` remains unfiltered; endpoint attribution needs explicit `AttributionConsistent`/`KeyAttribution`, and conflicting announcements are not deduped. | Add direction-keyed attribution, a `NodeId → PubKey` consistency invariant, and announcement deduplication; keep the raw-store caveat. |
| `NET-01` | P2 | open | Network/liveness results depend on scheduling/fairness assumptions | `LN-SEC-003` keeps four `Assumptions P`; `LN-SEC-005` uses `FeeScheduleBounded`; `LN-SEC-006` requires a watchtower report | State the adversarial schedule/fairness model explicitly and prove one concrete eventual-delivery instance |
| `CONF-01` | P2 | open (vector suite added) | No shared conformance suite against BOLT vectors | `tests/conformance/vectors.json` + `scripts/check-conformance.py` cover 61 BigSize/TLV vectors with mutation controls, and `ConformanceTargets.lean` has 86 `decide` theorems. The checker is wired into CI. This is vector conformance, not a differential implementation test; two TLV value-minimality/unknown-type cases are declared model gaps. | Add message framing and more encodings; keep the vector suite green. |
| `CONF-02` | P2 | open (new in wave 4) | No differential conformance against rust-lightning | The vector suite checks our model against published BOLT encodings, not live rust-lightning behavior. Message framing was excluded because the model length is payload-only. | Add a differential harness over pinned rust-lightning fixtures and reconcile the framing convention first. |
| `MODEL-01` | P2 | open | No script interpreter / consensus semantics | Scripts are byte templates; sighash, witness, and signature execution are outside the model | Treat as a separate L1 bridge project; do not claim script spendability from the byte templates |
| `MODEL-02` | P2 | open | HTLC state-machine coverage is partial | `LN-CH-101`: no `Step.update_add_htlc` constructor; E37 models affordability on successor functions | Add the missing transition or explicitly scope the state machine to the modelled transitions |
| `SEC-01` | P2 | open | No end-to-end game-based security proof for the full protocol | The tree has invariant, conservation, and conditional security theorems, not a cryptographic game reduction | Keep separate from catalog cleanup; define the game and assumptions before claiming a reduction |

## Wave 4 lanes (complete)

The eight lanes launched from `47189fe` are integrated. Reports are under
`agents/reports/swarm4/`.

| Lane | Issue(s) | Result | Owned files |
|---|---|---|---|
| `S4-L1-SPEND` | `L1-01`, `L1-02` | Explicit interpreter-law stack model; serializer equals seam templates; conditional 2-of-2 funding and both `to_local` branch spends; rejection/limit cases; vendored real interpreter found but not imported | `LnLean/Bitcoin/Seam.lean`, new `SpendTargets.lean` |
| `S4-VENDOR-CI` | `OPS-01` | Pinned `fetch-vendor.sh` with 43-test suite; CI source gates unconditional; clean build explicitly skipped unless a vendor artifact is configured | `.github/workflows/ci.yml`, `scripts/fetch-vendor.sh`, `scripts/verify-vendor.sh` |
| `S4-CONFORMANCE` | `CONF-01` | 61 BigSize/TLV vectors, checker with mutation controls, 86 Lean `decide` theorems; 2 declared model gaps | `tests/conformance/**`, `scripts/check-conformance.py`, new `ConformanceTargets.lean` |
| `S4-PR-WIRE` | `PR-02` | Additive `CommitmentSignedFull`; `ProducedFrom`; conditional exact coverage; legacy no-decoder negatives retained | `LnLean/Protocol/Messages.lean`, new `ProtocolWireTargets.lean` |
| `S4-HTLC-GLOBAL` | `HT-01` | Direction-tagged `HTLCTag`; reachable global uniqueness/Nodup; old cross-direction duplicate maps to distinct tags | `LnLean/Channel/HTLC.lean`, new `HtlcGlobalIdTargets.lean` |
| `S4-FEE-DUST` | `CH-01`, `CH-02` | Second-stage fee from feerate; exact dust threshold; trimming partition; zero-dust legacy permutation; BOLT 3 accounting; core patch recorded | new `CommitmentIntegrationTargets.lean` |
| `S4-GOSSIP-ATTR` | `RT-01` | `admitGossipAttributed`; reachable graph-edge attribution; explicit endpoint hypotheses; raw-store caveat retained | `LnLean/Routing/Gossip.lean`, new `GossipAttributionTargets.lean` |
| `S4-RELEASE` | `OPS-02`, `OPS-03` | Release checklist and neutral license decision matrix; no license/tag/merge/push | `docs/RELEASE-CHECKLIST.md`, `docs/LICENSE-DECISION.md` |

## Wave 5 candidate lanes

These are the next codeable lanes. They are not launched yet; the parent
selects a disjoint eight after the wave-4 checkpoint. Human-only release
decisions (`OPS-02`, `OPS-03`, vendor publication) stay outside agent lanes.

| Lane | Issue(s) | Scope | Owned files |
|---|---|---|---|
| `S5-L1-INTERP` | `L1-01`, `L1-02`, `L1-07` | Import the vendored `Bitcoin/Interpreter/Defs.lean` evaluator; connect `SpendTargets` to `evalScriptBytes`/`verifyWitnessProgram`/`checkMultiSig`; discharge or narrow `ConsensusSpendBridge` | `LnLean/Proofs/Bitcoin/SpendTargets.lean`, new interpreter bridge module |
| `S5-CH-GROSSNET` | `CH-03`, `CH-01`, `CH-02` | Add `netAmountSat`/`trimmedSat`/`effectiveFeeSat` with defaults; switch dust test to net; migrate construction sites; prove canonical refinement | `LnLean/Channel/Commitment.lean`, new integration module |
| `S5-PR-SIGHASH` | `PR-02`, `PR-01` | BOLT 3 sighash serializer; C3-derived digests/signatures; honest signer/key-binding construction | `LnLean/Protocol/Messages.lean`, new `LnLean/Proofs/Channel/SighashTargets.lean` |
| `S5-CONF-DIFF` | `CONF-02`, `CONF-01` | Reconcile payload-only vs transport framing; add pinned rust-lightning differential fixtures and a runner | `tests/conformance/**`, `scripts/check-conformance.py`, new proof module |
| `S5-MODEL-STEP` | `MODEL-02` | Add `Step.update_add_htlc`/success/fail transitions and prove the affordability invariant from the constructor | `LnLean/Channel/State.lean`, new state-machine proof module |
| `S5-L1-FUNDING` | `L1-03`, `L1-05` | Construct the funding hash link from the handshake instead of assuming it; keep the finite C1 admission | `LnLean/Protocol/Handshake.lean`, `LnLean/Bitcoin/Funding.lean`, new proof module |
| `S5-GOSSIP-ATTR2` | `RT-01` | Direction-keyed attribution, `NodeId → PubKey` consistency, announcement deduplication | `LnLean/Routing/Gossip.lean`, new proof module |
| `S5-SEC-LIMITS` | `CR-01`, `SEC-01` | Computational-security limits document and a precise game/assumption definition; no fake reduction | `docs/CRYPTO-LIMITS.md`, new `SecurityGame`-adjacent proof module |

## Wave update protocol

1. At the start of a wave, the parent updates this file with the selected lane
   table and the base commit.
2. Each lane gets exclusive files and a report path; lanes do not touch
   `Obligations.lean`, `Traceability.lean`, root imports, Git history, or the
   shared catalog unless explicitly assigned.
3. A lane that cannot prove the target must record the exact missing model or
   assumption and retain a counterexample/negative theorem. A blocked lane is a
   successful result if it narrows the gap faithfully.
4. The parent integrates only faithful, sorry-free results. It updates the
   catalog, traceability, generated indexes, this roadmap, and the gate record
   in one commit.
5. The gate is: full build, strict `check-catalog --audit`, `check.sh`,
   `check-final.py`, `check-conformance.py`, `verify-anchors.py`,
   `verify-vendor.sh`, and the exact `sorry` scan.
6. Push non-force to `origin/repair/integrated`; never overwrite `main` or
   another worker's branch.
7. Close issues in this file with the commit and theorem names. Add new gaps
   discovered by the wave in the same update. Then launch the next wave.

## Current gate evidence

| Check | Result |
|---|---|
| `lake build` | 188 jobs, RC 0 |
| `check-catalog.py --audit` | 48 proved / 0 statement-only / 61 targets / 0 unresolved / 0 proved failures |
| `check-catalog.py --allow-planned` | 48/0/0 planned, RC 0 |
| `check.sh` | `files=182 obligations=82 sorry_in_proofs=0`, RC 0 |
| `check-final.py` | 182 Lean files, 180 root imports, RC 0 |
| `check-conformance.py` | 61 vectors, 86 Lean checks, 2 declared gaps, RC 0 |
| `verify-anchors.py` | 299 anchors, 0 bad, 2 unanchored rows, RC 0 |
| `verify-vendor.sh` | 119 files, RC 0 |
| Axiom audit | 101 audited theorems; only `propext`, `Quot.sound`, `Classical.choice` |
