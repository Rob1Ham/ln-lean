# Open Issues and Swarm Roadmap

**Status:** living roadmap after proof-wave 5; wave 6 candidate lanes defined.
**Branch:** `repair/integrated`.
**Base commit:** `11a460c` (wave 5 launch); proof-wave 5 code is `6389baa`\n(proof-wave 4 code at `26ced90`).
**Catalog gate:** 48/48 rows `proved`, 0 `statement-only`, 0 unresolved,
67 targets.
**Full build:** 204 jobs, RC 0.
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
| **P0** | Blocks any claim of spendable L1 scripts | `L1-01`, `L1-02`, `L1-07`, `L1-08` |
| **P1** | Major model/verification gap; codeable in a wave | `L1-03`, `L1-04`, `L1-05`, `PR-01`, `PR-02`, `PR-05`, `PR-06`, `CH-01`, `CH-02`, `CH-03`, `CH-04`, `RT-01`, `RT-02` |
| **P2** | Longer-term research / conformance / network assumptions | `CR-01`, `L1-06`, `NET-01`, `CONF-01`, `CONF-02`, `CONF-03`, `MODEL-01`, `MODEL-02`, `MODEL-03`, `SEC-01`, `OPS-04` |

## Open issues

| Id | Priority | Status | Issue | Evidence / current boundary | Next action |
|---|---|---|---|---|---|
| `OPS-01` | P0 | open (mitigated) | Public CI cannot run the full build from a clean checkout | `vendor/btc-lean-core` is gitignored; the pinned snapshot `f950806` is not in public `btc-lean` history and no public artifact exists. `scripts/fetch-vendor.sh` now verifies or provisions an explicit local/URL/exact-git input against `vendor/VENDOR-SHA256` (119 files), returns a distinct skip code when no input is supplied, and `.github/workflows/ci.yml` always runs source gates while marking the build as not run; `REQUIRE_VENDOR_BUILD=true` turns a skip into failure. | Maintainer chooses: (a) publish a checksummed snapshot archive and set `VENDOR_ARTIFACT_URL` + `VENDOR_ARTIFACT_SHA256` (recommended), (b) commit the 119-file snapshot, or (c) keep the explicit skip gate. Publication also requires a provenance/license decision for the `wallet-peer` snapshot. |
| `OPS-02` | P0 | open; decision support ready | No `LICENSE` | No license file in the tree; `docs/LICENSE-DECISION.md` now provides a neutral MIT/Apache-2.0/dual matrix and third-party notice inventory | Maintainer chooses the license and copyright holder, then adds `LICENSE`/`NOTICE`; do not let an agent invent one |
| `OPS-03` | P0 | open; checklist ready | No release tag and `main` is behind | `origin/main` is old; `repair/integrated` is the active branch; no tag; `docs/RELEASE-CHECKLIST.md` now records the pre-tag gates and human choices | Decide PR/merge path to `main`, cut a signed/annotated tag, and publish release notes |
| `OPS-04` | P2 | open (new in wave 4) | Vendor snapshot contains an absolute symlink | `vendor/btc-lean-core/btc-lean-core` points at `/home/ubuntu/ln-lean/vendor/btc-lean-core`, is not in `VENDOR-SHA256`, and is rejected by archive provisioning. | Delete it before publishing a snapshot; keep the checksum manifest authoritative. |
| `L1-01` | P0 | open (mitigated) | P2WSH / `OP_CHECKMULTISIG` spendability is not bridged to the vendored interpreter | `SpendTargets.lean` defines the explicit stack model; `InterpreterBridgeTargets` imports the vendored `Bitcoin.Interpreter.Defs` evaluator, proves the model serializer equal to the vendor `serializeOpcodes`, parses the wire list back exactly, and proves `funding_interpreters_agree` for the positive 2-of-2 funding witness. This is not unconditional consensus spendability: ECDSA/signature checks and context are hypotheses, and the sighash is not constructed. | Add the BIP 143 sighash/context construction and connect it to the vendor `checkECDSASignature` path; keep the conditional bridge as the specification. |
| `L1-02` | P0 | open (mitigated) | `to_local` CSV/revocation script is structural plus abstract execution laws | `InterpreterBridgeTargets` executes the delayed `to_local` branch end to end through the vendored `OP_IF`/`OP_ELSE`/`OP_ENDIF`/`OP_CSV`/`OP_DROP`/`OP_CHECKSIG` path, using `checkSequenceDef` as the shared sequence predicate. The decoded delay, non-negativity/disable-bit conditions, locktime environment, and signature checks remain hypotheses; the revocation branch is not vendor-mechanized. | Vendor-mechanize the revocation branch and construct the locktime/sighash inputs; retain the explicit positive-direction scope. |
| `L1-03` | P1 | open (mitigated) | `FundingScriptHashLinked` is a construction invariant | `FundingNegotiation.toFundingParams` now computes `witnessScriptHash := H(witnessScript.bytes)` from ordered funding keys; `acceptChannel_toFundingParams` and the handshake hash-link theorem establish the modelled path, and `FundingLinkTargets` proves the ordered P2WSH output. There is still no `open_channel` message or key authentication. | Add `open_channel`/key-authentication coverage and extend the construction through the full handshake; keep the handshake theorem. |
| `L1-04` | P1 | open | Anchor weight has an 8 WU spec/serialization gap | `LN-L1-006` proves `serializedAnchorWeight + 8 = 1124 + 172*k`; witness serialization and the Appendix A `count_tx_out` discrepancy remain | Model the missing witness/CompactSize bytes or document the negotiated fee-basis interpretation permanently |
| `L1-05` | P1 | open (partially mitigated) | C1 is 32-byte payment-preimage collision resistance, not 71-byte script injectivity | `c1_32_does_not_bind_funding_witnessScripts` remains; the P2WSH reverse direction still uses a finite pair-level `CollisionFreeOn` admission. `FundingLinkTargets` adds the construction lemma for the actual revealed script but does not assume global or 71-byte injectivity. | Keep the finite admission; if a global claim is required, model a domain-separated script commitment rather than SHA-256 injectivity. |
| `L1-06` | P2 | open | Reorg result is conditional on common tip and bounded depth | `LN-L1-003` keeps `SameChain`, common-prefix arithmetic, and `OutOfReachOf` explicit; deep reorgs have a separate failure mode | Connect the hypotheses to the L1 chain model or leave the conditional theorem as the deliverable |
| `L1-07` | P0 | open (mitigated) | Vendored real interpreter is imported only for positive L1 branches | `InterpreterBridgeTargets` imports `Bitcoin.Interpreter.Defs` and proves the funding 2-of-2 and delayed `to_local` agreement results (31-job lane build, RC 0). The bridge is positive-direction only; BIP 143 sighash construction, the locktime environment, and the revocation branch remain outside it, so no unconditional `ConsensusSpendBridge` is claimed. | Add the sighash/locktime construction and the revocation branch; keep `ConsensusSpendBridge` narrowed to the proved positive path. |
| `L1-08` | P0 | open (new in wave 5) | BIP 143 sighash and locktime/sequence context are assumptions in the L1 bridge | `InterpreterBridgeTargets` states the boundary explicitly: decoded delay `n`, `0 ≤ n`, the disable-bit test and `checkSequenceDef`, `LocktimeEnv` construction, BIP 143 sighash, and default policy flags are hypotheses. The vendor evaluator is exercised, but the transaction digest that commits to the script is not built. | Construct the BIP 143 legacy/witness-v0 sighash and locktime environment from the transaction fields, then prove the vendor signature check consumes it. |
| `CR-01` | P2 | open (limits interface added) | No computational cryptographic reductions | C1/C3/C8 are exact algebraic laws; `docs/CRYPTO-LIMITS.md` and `SecurityGameTargets.lean` now state the missing probability/complexity model, query bounds, and the exact reduction interface. `AdvantageReduction.bound` is arithmetic conditional on an assumed tightness field; no reduction is proved. | Choose a probability/complexity foundation and real games for C1/C3/C8; do not claim computational security from the algebraic model. |
| `PR-01` | P1 | open (partially mitigated) | `FundingSigningLaw` / `KeyBinding` are hypotheses | `SighashTargets` adds an honest signing constructor and `funding_and_commitment_signing_contract`, which composes the funding and commitment contracts under `FundingSigningLaw` + `KeyBinding`. There is still no secret-key model, and C3 alone is shown insufficient for key/tx attribution. | Add a secret-key/key-generation model and connect `accept_channel.funding_pubkey` to the signer key, or keep the conditional contract as the scope. |
| `PR-02` | P1 | open (mitigated) | `CommitmentSigned` wire record lacks data for wire-only coverage | `SighashTargets` adds a BOLT 3-shaped structural commitment/HTLC serializer, `SighashProduces`, and `SighashProduces.coverage`, deriving the digest, commitment signature, and per-HTLC signatures under C3. The serializer is structural rather than bit-exact; C3 binds signatures to digests, not directly to views, and `ProducedFrom` alone still does not determine the digest. | Add bit-exact BOLT 3 encoding and close the C3 view-binding collision gap (`PR-05`, `PR-06`); then decide whether the full record is a type-132 extension or signer-side. |
| `PR-05` | P1 | open (new in wave 5) | BOLT 3 sighash serializer is structural, not bit-exact | `SighashTargets.commitmentPreimage`/`htlcPreimage` bind every modelled field, but the encoding is a structural tuple, not the exact BOLT 3 byte layout. Scripts and outpoint are context inputs, not parsed from raw transactions. | Define the exact BOLT 3 commitment/HTLC preimage byte layout and prove the structural serializer refines it; add byte-level vectors. |
| `PR-06` | P1 | open (new in wave 5) | C3 binds signatures to digests, not directly to commitment/HTLC views | `SighashProduces.signature_binds_digest` proves that a valid signature binds the digest under EUF-CMA, but `commitmentDigest` is a SHA-256-style hash; the arbitrary-preimage/collision gap between a digest and a unique view is stated, not assumed away. | Model a domain-separated injective commitment or add the collision-resistance reduction needed to move from digest binding to view binding. |
| `CH-01` | P1 | open (mitigated) | Rich `CommitmentTx` model is not the legacy consumer path | `CommitmentGrossNetTargets.migratedFrom_outputsNet_perm_commitmentOutputs` proves the net view is a permutation of `Commitment.commitmentOutputs` at arbitrary dust, requiring only `0 < dustLimitSat`; D12 remains the unconditional refutation. Legacy consumers are still not migrated to the rich/net output path. | Migrate the legacy consumers and prove the canonical refinement at their actual construction sites. |
| `CH-02` | P1 | open (mitigated) | Second-stage fee and dust trimming are not integrated end-to-end | `CommitmentGrossNetTargets` adds the net output path, `trimmedValue`, `effectiveFeeSat`, and proves emitted + base fee + trimmed = funding and effective fee = base fee + trimmed. The `CommitmentHTLCOutput`/`Commitment` literal fields are still documented as an integration patch. | Place the remaining `CommitmentHTLCOutput`/`Commitment` fields (`CH-03`) and migrate all construction sites. |
| `CH-03` | P1 | open (partially integrated) | Rich commitment outputs lack BOLT-3 gross/net fields | `CommitmentTx` now has `netAmountSat`/`trimmedSat` with defaults, and `Commitment` has `trimmedSat`/`effectiveFeeSat` plus a net-based output path. The `CommitmentHTLCOutput`/`Commitment` record fields in `LnLean/Channel/Types.lean` were outside lane ownership, so the literal placement remains an exact integration patch. | Apply the recorded `Types.lean` field patch and migrate construction sites so `amountSat` is gross and `netAmountSat` is second-stage (`CH-04`). |
| `CH-04` | P1 | open (new in wave 5) | Gross/net record fields are not yet in `Channel/Types.lean` | `CommitmentGrossNetTargets` proves the net path and arbitrary-dust canonical permutation, and `CommitmentTx` has defaulted net/trimmed fields. The literal `CommitmentHTLCOutput`/`Commitment` fields remain a documented patch because the lane did not own `Types.lean`; legacy consumers still use the old shape. | Apply the exact `Types.lean` patch, migrate construction sites and tests, then prove the canonical refinement at the consumer boundary. |
| `HT-01` | P1 | closed (tagged namespace) | Untagged global HTLC id uniqueness is false under BOLT 2 per-sender counters | `LN-HT-004` keeps per-sender `dir_id_unique`, the `CrossDisjoint` untagged form, and now the direction-tagged `HTLCTag` namespace with `tagged_id_unique_of_reachable`/`tagged_ids_nodup_of_reachable`. `cross_direction_duplicate_tagged` connects the old counterexample. The wire remains per-sender by BOLT 2 design. | No further model action; keep the tag documented as a model-side namespace, not a new wire encoding. |
| `RT-01` | P1 | open (mitigated) | Gossip key attribution and raw insertion are separate | `admitGossipAttributed`/`admitGossipDirected` gate updates on signature validity plus announced-key attribution; `gossip_graph_edges_directional_key_endpoint` proves direction-keyed endpoint attribution under `CanonicalAnnouncements` + `NodeKeyConsistent`; `canonical_directional_attribution_unique` and the conflicting-announcement counterexample record the dedup boundary. Raw `applyGossip` remains append-only/unfiltered, and the consistency/canonical hypotheses are explicit, not derived from admission. | Derive `NodeKeyConsistent`/`CanonicalAnnouncements` from a canonicalizing admission transition (`RT-02`); keep the raw-store caveat. |
| `RT-02` | P1 | open (new in wave 5) | Gossip consistency and canonical-announcement invariants are hypotheses | `GossipKeyConsistencyTargets` proves attribution only under explicit `NodeKeyConsistent` and `CanonicalAnnouncements`; conflicting canonical announcements remain ambiguous without the selector. | Define the canonicalizing store/admission transition and prove it establishes both invariants for reachable states, including key rotation/update supersession. |
| `NET-01` | P2 | open | Network/liveness results depend on scheduling/fairness assumptions | `LN-SEC-003` keeps four `Assumptions P`; `LN-SEC-005` uses `FeeScheduleBounded`; `LN-SEC-006` requires a watchtower report | State the adversarial schedule/fairness model explicitly and prove one concrete eventual-delivery instance |
| `CONF-01` | P2 | open (vector suite added) | No shared conformance suite against BOLT vectors | `tests/conformance/vectors.json` + `scripts/check-conformance.py` cover 61 BigSize/TLV vectors plus 16 framing cases and 7 mutation controls; `ConformanceTargets.lean`/`ConformanceDiffTargets.lean` add 151 `decide` theorems. The checker is wired into CI. This is finite-vector conformance, not a full implementation test; two TLV value-minimality/unknown-type cases are declared model gaps. | Add more encodings and a live differential path when the pinned client can run offline; keep the vector suite green. |
| `CONF-02` | P2 | open (fixtures added) | No live differential conformance against rust-lightning | `tests/conformance/rust-lightning/fixtures.json` pins 26 BigSize, 3 TLV, and 4 wire transcriptions from rust-lightning `fe49009`; the checker runs them offline. The fixtures are transcriptions, not live-regenerated. `Wire.unframe` remains payload-only, and one unknown-even-TLV namespace policy is a declared gap. | Regenerate fixtures from the pinned client when its cache is complete; keep the offline fixtures as the committed baseline (`CONF-03`). |
| `CONF-03` | P2 | open (new in wave 5) | Transport framing is conformance-only and fixtures are offline transcriptions | The `Transport.transportFrame`/`unframeTransport` model lives in `ConformanceDiffTargets`, while production `Wire.unframe` remains payload-only. The 33 rust-lightning fixtures were transcribed from the pinned commit because `cargo test` cannot run offline; they are not live-regenerated. | Promote the framing model into `LnLean/Wire/Message.lean` with the same theorem names, and regenerate/verify fixtures from the pinned client in CI when its cache is available. |
| `MODEL-01` | P2 | open | No script interpreter / consensus semantics | Scripts are byte templates; sighash, witness, and signature execution are outside the model | Treat as a separate L1 bridge project; do not claim script spendability from the byte templates |
| `MODEL-02` | P2 | open (mitigated) | HTLC state-machine coverage is partial | `State.lean` now has an additive `UpdateStep` layer, `updateAddHtlc`/`failHtlcAt`/`fulfillHtlcAt`, and a `Step.update_add_htlc` abbrev shim; `StateTransitionTargets` proves ledger/reserve preservation and E37 refinement. A literal `Step` constructor is still excluded because it requires a new `ProtocolEvent` and breaks the liveness/liquidity folds. | Fold `UpdateEvent` into `ProtocolEvent` with a coordinated migration of `Liveness`, `LiquidityProps`, `D14`, `F03`, and `StateMachineProps`, or keep the explicit `UpdateStep` layer as the scope. |
| `MODEL-03` | P2 | open (new in wave 5) | Commitment-dance transitions are not in the state machine | `UpdateStep` covers add/fail/fulfill, but `commitment_signed`, `revoke_and_ack`, and the revocation/HTLC-signature handshake are not modelled as reachable transitions. | Add the commitment-dance transition layer and prove the reachable-state invariants (no stale commitment, revocation ordering, balance conservation). |
| `SEC-01` | P2 | open (game interface added) | No end-to-end game-based security proof for the full protocol | The tree has invariant, conservation, and conditional security theorems. `SecurityGameTargets` adds `Game`, `EventReduction`, `Advantage`, and `AdvantageReduction` interfaces, but its `tight` field is assumed and the game is a deterministic accounting model. | Define the protocol/corruption/L1 game and a real reduction; keep the interface as a specification, not a security claim. |

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

## Wave 5 lanes (complete)

Wave 5 launched from `11a460c` and integrated eight disjoint lanes. Reports are
under `agents/reports/swarm5/`. The catalog stayed at 48 rows and 0
statement-only; five existing rows were strengthened to 67 resolved targets.

| Lane | Issue(s) | Result | Owned files |
|---|---|---|---|
| `S5-L1-INTERP` | `L1-01`, `L1-02`, `L1-07`, `L1-08` | Vendored interpreter bridge: model serializer = vendor `serializeOpcodes`, exact wire parse; funding 2-of-2 and delayed `to_local` execute through `verifyWitnessProgram`; remaining delay/locktime/BIP 143/revocation boundary explicit | new `InterpreterBridgeTargets.lean` |
| `S5-CH-GROSSNET` | `CH-01`, `CH-02`, `CH-03`, `CH-04` | Defaulted `CommitmentTx.netAmountSat`/`trimmedSat`; net output path, `trimmedValue`, `effectiveFeeSat`; arbitrary-dust canonical permutation; conservation/effective-fee accounting; literal `Types.lean` patch recorded | `LnLean/Channel/Commitment.lean`, new `CommitmentGrossNetTargets.lean` |
| `S5-PR-SIGHASH` | `PR-01`, `PR-02`, `PR-05`, `PR-06` | BOLT 3-shaped structural commitment/HTLC serializer, `SighashProduces`, `SighashProduces.coverage`, honest signing constructor, joint funding/commitment contract; bit-exact/view-binding gaps explicit | new `SighashTargets.lean` |
| `S5-CONF-DIFF` | `CONF-01`, `CONF-02`, `CONF-03` | 16 framing cases, 26 BigSize + 3 TLV + 4 wire rust-lightning fixtures, 7 mutation controls, 146 Lean theorem references; offline transcriptions and payload-only production decoder stated | `tests/conformance/**`, `scripts/check-conformance.py`, new `ConformanceDiffTargets.lean` |
| `S5-MODEL-STEP` | `MODEL-02`, `MODEL-03` | Additive `UpdateStep` layer with add/fail/fulfill, `AffordableAdd`, `Step.update_add_htlc` shim; ledger/reserve preservation and E37 refinement; commitment dance still separate | `LnLean/Channel/State.lean`, new `StateTransitionTargets.lean` |
| `S5-L1-FUNDING` | `L1-03`, `L1-05` | Funding hash link constructed from the handshake; ordered P2WSH output; handshake hash-link theorem; finite `CollisionFreeOn` admission kept; `open_channel`/key auth still open | `LnLean/Bitcoin/Funding.lean`, `LnLean/Protocol/Handshake.lean`, new `FundingLinkTargets.lean` |
| `S5-GOSSIP-ATTR2` | `RT-01`, `RT-02` | Direction-keyed attribution, `NodeId → PubKey` consistency, canonical announcement dedup under explicit invariants; raw store caveat retained | `LnLean/Routing/Gossip.lean`, new `GossipKeyConsistencyTargets.lean` |
| `S5-SEC-LIMITS` | `CR-01`, `SEC-01` | Computational-security limits document and precise `Game`/`EventReduction`/`AdvantageReduction` interface; no reduction claimed | `docs/CRYPTO-LIMITS.md`, new `SecurityGameTargets.lean` |

Wave 5 added eight proof modules, raised the root build to 204 jobs, and
increased the audit to 133 headline theorems. The remaining lane output is
evidence for existing rows, not a claim of unconditional L1 execution or
computational security.

## Wave 6 candidate lanes

These are codeable next steps from the wave-5 gaps. The parent selects a
disjoint eight after the wave-5 checkpoint. Human-only decisions (`OPS-02`,
`OPS-03`, vendor publication) and the probability/complexity foundation
(`CR-01`/`SEC-01`) stay outside an agent lane until a maintainer chooses the
foundation.

| Lane | Issue(s) | Scope | Owned files |
|---|---|---|---|
| `S6-L1-SIGHASH` | `L1-08`, `L1-07` | Construct BIP 143 witness-v0 sighash and `LocktimeEnv` from transaction fields; prove the vendor signature check consumes them | new sighash/bridge module, `LnLean/Proofs/Bitcoin/InterpreterBridgeTargets.lean` |
| `S6-L1-REVOKE` | `L1-02`, `L1-07` | Vendor-mechanize the `to_local` revocation branch and prove the branch-selection/negative cases | new proof module, bridge module |
| `S6-CH-TYPES` | `CH-04`, `CH-03` | Apply the exact `Types.lean` gross/net field patch, migrate construction sites/tests, prove consumer-boundary refinement | `LnLean/Channel/Types.lean`, `Commitment.lean`, new/updated proof module |
| `S6-PR-BITEXACT` | `PR-05`, `PR-02` | Exact BOLT 3 preimage byte layout and refinement of the structural serializer; add byte-level vectors | new/extended `SighashTargets.lean`, conformance fixtures |
| `S6-PR-VIEWBIND` | `PR-06`, `PR-02` | Model a domain-separated commitment or the collision-resistance reduction from digest binding to view binding | new proof module |
| `S6-MODEL-DANCE` | `MODEL-03`, `MODEL-02` | Add commitment_signed/revoke_and_ack transitions and prove reachable-state invariants | `LnLean/Channel/State.lean`, new proof module |
| `S6-GOSSIP-DERIVE` | `RT-02`, `RT-01` | Canonicalizing admission/store transition; derive `NodeKeyConsistent` and `CanonicalAnnouncements` for reachable states | `LnLean/Routing/Gossip.lean`, new proof module |
| `S6-CONF-LIVE` | `CONF-03`, `CONF-02` | Promote transport framing into `Wire/Message.lean` and add a pinned live/regeneration path for rust-lightning fixtures | `LnLean/Wire/Message.lean`, `tests/conformance/**`, `scripts/check-conformance.py` |

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
| `lake build` | 204 jobs, RC 0 |
| `check-catalog.py --audit` | 48 proved / 0 statement-only / 67 targets / 0 unresolved / 0 proved failures / 6898 declarations |
| `check-catalog.py --allow-planned` | 48/0/0 planned, RC 0 |
| `check.sh` | `files=190 obligations=82 sorry_in_proofs=0`, RC 0 |
| `check-final.py` | 190 Lean files, 188 root imports, RC 0 |
| `check-conformance.py` | 61 base + 16 framing, 33 differential fixtures, 146 Lean references, 7/7 mutation controls, 3 declared gaps, RC 0 |
| `verify-anchors.py` | 305 anchors, 0 bad, 2 unanchored rows, RC 0 |
| `verify-vendor.sh` | 119 files, RC 0 |
| Axiom audit | 133 audited theorems; only `propext`, `Quot.sound`, `Classical.choice` |
