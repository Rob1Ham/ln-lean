# Final status — Lightning repair tree

**Repository:** `/home/ubuntu/ln-lean-repair`
**Branch:** `repair/integrated`
**Gate HEAD:** `1c88f17` (`[WAVE12]` docs-only status checkpoint); code integration is
`d210079`; later docs-only status commits may advance the tip.
Base `9359475` (wave-9 integration); wave 10 launched from `9158592`; wave 11
launched from `4037264`; wave 12 launched from `5ddab4c`.
**Catalog state:** **51 `proved` / 0 `statementOnly` / 0 unresolved / 294
target occurrences (282 unique declarations)**.
**Remote refs:** wave 11 is published non-force to `origin/repair/integrated` at
`9940642`, with status commits `90ef1f1` and `5ddab4c`; hosted CI runs
`39288684058`, `39290061147`, and `39290644672` completed both source gates and
the pinned-vendor build gate successfully. Wave 12 is published non-force at
`d210079` with status checkpoints `d9c0d2f`, `07288ad`, `97897b6`, and `1c88f17`; hosted CI
runs `39303105137`, `39303680973`, `39303944696`, `39304616746`, and
`39304938940` are green. The post-integration
audit in `agents/reports/swarm12/S12-POST-INTEGRATION-AUDIT.md` confirms the
remaining P0/P1 rows are external/human barriers and no tractable wave-13 proof
lane remains. `origin/main` is not touched
by this work.
The former `repair/pubbump` branch is merged and retired; its public-core bump
is part of this branch.
**Toolchain:** `leanprover/lean4:v4.35.0`
**L1 build dependency:** read-only `vendor/btc-lean-core` copy of public
`btc-lean` `spec/core` at
`4f5c4f858fb9ca0743042644453cfa92d30dd271` (149 files)
**L1 public reference:** `https://github.com/Rob1Ham/btc-lean`
`main@4f5c4f858fb9ca0743042644453cfa92d30dd271` (same commit; copied, not
imported from the live clone)
**Spec / client references:** `lightning/bolts`
`1aadb719b4007c4cea0ba6e36b08c4fb53788dee`; `rust-lightning`
`fe4900930c6bd5786ec4203274d7cf312776a5a6`

This file describes **this repair repository**, not the older
`ln-lean-final` / `final/integrated` tree. The earlier final tree (132 Lean
files, 15 open `sorry` sites, vacuous global crypto assumptions) is the
starting point of the repair, not its result.

## Wave 13 review (read-only, 2026-10-19)

A 32-lane review used pinned `ldk-node@fa123fed…` and
`ldk-server@c17dc11d…` as behavioral datapoints. All reports are under
`agents/reports/wave13-review/`; `R32-synthesis.md` is the ranked roadmap.
The review did not change Lean code and did not move the external
L1/Noise/EUF-CMA/source barriers. It did find tractable defects in already-
proved consumer rows: `REV-01` reserve/in-flight admission, `REV-02` anchored
commitment debit, `REV-03` replay/duplicate admission, `REV-04` non-chain
`routeValid`, and `REV-05` axiom/traceability coverage overstatement. A
bounded six-lane repair+assurance wave is recommended; see
`agents/reports/wave13-review/R32-synthesis.md` §6.2 and `docs/OPEN-ISSUES.md`.
Hosted CI run `39325365957` is green at `c88d9fd` (source-level gates and the
pinned-vendor build gate).

## What this tree is

A Lean 4 formal model and proof scaffold for the Lightning Network on top of a
read-only `btc-lean` Bitcoin L1 model. It is not a completed proof of
Lightning, and it is not a conformance-tested implementation.

Proof-wave 3 integrated eleven disjoint lanes. It retargeted and promoted the
last eleven catalog rows, so every catalog row now names an exact,
sorry-free theorem. Proof-wave 4 added six bridge/vector modules and
strengthened two catalog targets. Proof-wave 5 added eight bridge/refinement
modules and strengthened five catalog rows to 67 resolved targets. Proof-wave 6
added seven files (one model and six proof modules) and strengthened four rows
to 73 resolved targets. Proof-wave 7 added seven more files (one crypto model
and six proof modules), strengthened six rows to 79 resolved targets, and
closed the consumer, raw-gossip, live-conformance, and fold questions, again
without changing the 48-row count. Proof-wave 8 added seven more proof modules,
strengthened seven rows from 79 to **100** resolved targets, and kept the
48-row count. The independent Wave H 48-lane integration added 45 further
proof modules on top of that base. Proof-wave 9 then added five proof modules,
strengthened six rows from 100 to **142 resolved targets**, and took the tree
to **261 Lean files**, **259 root imports**, and **269 audited headline
theorems** without changing the 48-row catalog. Proof-wave 10 added five more
proof modules, strengthened the same six rows from 142 to **198 resolved
targets**, and took the tree to **266 Lean files**, **264 root imports**, and
**323 audited headline theorems** without changing the 48-row catalog.

* `LnLean/Proofs/Bitcoin/FundingScriptTargets.lean`
* `LnLean/Proofs/Bitcoin/ToLocalScriptTargets.lean`
* `LnLean/Proofs/Bitcoin/WeightTargets.lean`
* `LnLean/Proofs/Channel/CommitmentOrderTargets.lean`
* `LnLean/Proofs/Channel/FeeTargets.lean`
* `LnLean/Proofs/ProtocolCoverageTargets.lean`
* `LnLean/Proofs/ProtocolSigningTargets.lean`
* `LnLean/Proofs/Routing/GossipTargets.lean`
* `LnLean/Proofs/Security/ReorgTargets.lean`
* `LnLean/Proofs/Wire/TLVTargets.lean`
* `LnLean/Proofs/Bitcoin/SpendTargets.lean`
* `LnLean/Proofs/Channel/CommitmentIntegrationTargets.lean`
* `LnLean/Proofs/Channel/HtlcGlobalIdTargets.lean`
* `LnLean/Proofs/ConformanceTargets.lean`
* `LnLean/Proofs/ProtocolWireTargets.lean`
* `LnLean/Proofs/Routing/GossipAttributionTargets.lean`
* `LnLean/Proofs/Bitcoin/InterpreterBridgeTargets.lean`
* `LnLean/Proofs/Bitcoin/FundingLinkTargets.lean`
* `LnLean/Proofs/Channel/CommitmentGrossNetTargets.lean`
* `LnLean/Proofs/Channel/SighashTargets.lean`
* `LnLean/Proofs/Channel/StateTransitionTargets.lean`
* `LnLean/Proofs/ConformanceDiffTargets.lean`
* `LnLean/Proofs/Routing/GossipKeyConsistencyTargets.lean`
* `LnLean/Proofs/Security/SecurityGameTargets.lean`
* `LnLean/Proofs/Bitcoin/SighashBridgeTargets.lean`
* `LnLean/Proofs/Bitcoin/InterpreterRevocationTargets.lean`
* `LnLean/Proofs/Channel/CommitmentTypesTargets.lean`
* `LnLean/Proofs/Channel/SighashViewBindingTargets.lean`
* `LnLean/Proofs/Channel/CommitmentDanceTargets.lean`
* `LnLean/Proofs/Routing/GossipCanonicalTargets.lean`
* `LnLean/Proofs/Bitcoin/SequenceContextTargets.lean`
* `LnLean/Proofs/Channel/CommitmentConsumerTargets.lean`
* `LnLean/Proofs/Channel/ProtocolEventFoldTargets.lean`
* `LnLean/Proofs/Routing/GossipRawRefinementTargets.lean`
* `LnLean/Proofs/Bitcoin/FundingAuthTargets.lean`
* `LnLean/Proofs/Crypto/KeyModelTargets.lean`

The model/support additions are `HtlcBook`/reachability/per-sender ids and
alone direction-tagged `HTLCTag` namespace in `LnLean/Channel/HTLC.lean`, the
rich `CommitmentTx` output model in `LnLean/Channel/Commitment.lean`, the full
BOLT 3 `toLocalScriptFull` model plus delay bytes in
`LnLean/Bitcoin/Seam.lean`, `CommitmentSignedFull` in
`LnLean/Protocol/Messages.lean`, the attributed/canonical gossip transitions in
`LnLean/Routing/Gossip.lean`, the BIP 143 model in
`LnLean/Bitcoin/Sighash.lean`, the secret-key/signer model in
`LnLean/Crypto/KeyModel.lean`, and the guarded fold and funding-phase layers in
`LnLean/Channel/State.lean` and `LnLean/Protocol/Handshake.lean`. Existing legacy declarations are preserved;
mechanized counterexamples such as D12 and the cross-direction HTLC duplicate
are retained.

Proof-wave 10 adds five boundary-focused modules:
`LnLean/Proofs/Bitcoin/EcdsaDomainTargets.lean` (no fixed tag repairs
`DigestBindsMod`; canonical value-`< n` domain is the exact algebraic repair),
`LnLean/Proofs/Protocol/TransportAuthTargets.lean` (session authentication is
separate from the explicit `SessionKeyBinding`), `LnLean/Proofs/Crypto/PopProtocolTargets.lean`
(concrete challenge-response PoP with fixed-width injectivity and replay
counterexamples), `LnLean/Proofs/Channel/CoverageWitnessTargets.lean` (a
constructive witness decoder plus legacy-only impossibility), and
`LnLean/Proofs/Routing/NodeIdentityTargets.lean` (rotation linkage requires an
explicit witness; wire membership is an additive admission gate). The
conformance lane adds a live `open_channel` payload row, taking the suite to
185 Lean references and 16/16 mutation controls.

Proof-wave 11 adds seven root-imported modules and three catalog rows:
`LnLean/Proofs/Routing/NodeIdentityChainTargets.lean` (signed rotation
certificates, transitive chains, re-signing, and replay/rate limits),
`LnLean/Proofs/Protocol/NoiseTransportTargets.lean` (Noise-shaped handshake and
AEAD model deriving the explicit `SessionKeyBinding`),
`LnLean/Proofs/Channel/CoverageSourceTargets.lean` (full-record,
out-of-band, and protocol-extension coverage sources),
`LnLean/Proofs/Security/ChainFinalityTargets.lean` (finite block graph,
bounded-depth finality, and a sharp deep-reorg counterexample),
`LnLean/Proofs/Payment/InvoiceWireTargets.lean` (pre-bech32 BOLT 11 field-list
codec and payment-hash/secret binding), `LnLean/Proofs/Channel/HtlcAggregateTargets.lean`
(aggregate HTLC coverage, no-double-spend separation, fee/weight accounting),
and `LnLean/Proofs/Model/NonVacuityTargets.lean` (a 30-entry witness registry
plus the `withVendorEcdsa` vacuity result). The conformance lane adds a live
`accept_channel` (type 33) row, taking the suite to 190 Lean references,
18/18 mutation controls, and three live BOLT 2 payloads.

Proof-wave 12 adds two root-imported proof modules and extends six catalog
rows without adding a row:
`LnLean/Proofs/Routing/NodeAddressTargets.lean` (the real BOLT 7
`node_announcement.addresses` wire format: `u16 addrlen` followed by typed
IPv4/IPv6/Tor v2/Tor v3/ASCII-DNS descriptors with exact 6/18/12/37-byte
layouts, nonzero ports, ascending type order, at most one type 5, canonical
round-trip/injectivity, and explicit rejection theorems) and
`LnLean/Proofs/Channel/CoverageConsumerTargets.lean` (an explicit consumer
contract separating full-record from wire-determined coverage, with
consumer-completeness and non-determinacy separation results). The conformance
lane adds live `funding_created` (type 34) and `funding_signed` (type 35)
payloads, taking the suite to 200 Lean references, 22/22 mutation controls,
26 differential fixtures, and five live BOLT 2 payloads. The independent
barrier audit re-checked the nine P0/P1 rows: `L1-01`/`L1-07` are blocked at
the untyped `ByteArray` EC interface, `L1-02` has no `TxValidation.Full`
transfer gap, and the other externally blocked rows remain explicit rather
than being claimed closed. Catalog claims were narrowed where prior wording
overstated the mechanized result (`LN-L1-001`, `LN-L1-004`, `LN-CH-007`,
`LN-PR-001`, `LN-RT-002`, `LN-SEC-007`).

## Verified state

| Check | Command | Result |
|---|---|---|
| Full build | `LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock lake build` | **RC 0**, `Build completed successfully (314 jobs).` |
| Actual `sorry` | `grep -RInE '^[[:space:]]*sorry[[:space:]]*$' LnLean --include='*.lean'` | **0 matches** (grep RC 1: no lines) |
| Policy checker | `./scripts/check.sh` | **RC 0**, `files=275 obligations=82 sorry_in_proofs=0`, `check: OK` |
| Selection/root checker | `python3 scripts/check-final.py` | **RC 0**, `selected: D=33 E=15 F=15 total=63`, 275 Lean files, 273 root imports |
| Vendor integrity | `./scripts/verify-vendor.sh` | **RC 0**, `OK (149 files)` |
| Anchors | `python3 scripts/verify-anchors.py` | **RC 0**, `anchors=313 bad=0 unanchored_rows=2` |
| Catalog, strict | `python3 scripts/check-catalog.py --audit` | **RC 0**, 51 proved, 0 statement-only, 294 target occurrences (282 unique), 0 unresolved, 0 proved failures, 0 candidates, 11,898 declarations |
| Catalog, planned-aware | `python3 scripts/check-catalog.py --allow-planned` | **RC 0**, `rows=51 proved=51 statementOnly=0 planned=0 proved_failures=0` |
| Axiom audit | `lake build LnLean.Proofs.PhaseC3.AxiomAudit` | **RC 0**, 393 print commands over a 435-name registry; printed names use only `propext`, `Quot.sound`, `Classical.choice`; coverage gap is `REV-05` |
| Generated index | `python3 scripts/collect-obligations.py` | `237` proof files, `81` markers, `51` catalog rows, `9537` declarations, `0` `sorry` sites |
| Conformance | `python3 scripts/check-conformance.py` | **RC 0**, 61 base + 16 framing + 9 boundary checks, 26 differential fixtures, 200 Lean theorem references, 22/22 mutation controls, 6 finite BOLT 2 message vectors, live 26 BigSize + 3 TLV + 4 wire + 5 BOLT 2 payloads (`funding_created`, `funding_signed`, `channel_ready`, `open_channel`, `accept_channel`) |

Tree size: **275 Lean files** under `LnLean/`, **273** root imports in
`LnLean.lean`; `LnLean.Proofs.All` and the `LnLean.Proofs.PhaseC2` aggregator
are not root-imported. The full build covers 314 Lake jobs.

The `sorry` grep result is exact: **there are no lines consisting only of
`sorry` (modulo whitespace) in any `LnLean/**/*.lean` file.** Prose mentions of
`sorry` in comments are not proof terms.

## Catalog promotions and scope caveats

All 51 rows are `proved`, but a `proved` row means the named declaration exists
and is sorry-free. Several rows keep explicit model, cryptographic, or L1
hypotheses; the scope caveat is part of the row's meaning.

| Row | Exact target(s) | Scope caveat |
|---|---|---|
| `LN-L1-001` | `FundingScriptTargets.fundingScriptPubKey_eq_p2wsh_twoOfTwo`, `FundingLinkTargets.fundingScriptPubKey_eq_p2wsh_ordered`, `InterpreterBridgeTargets.funding_interpreters_agree`, `SighashBridgeTargets.funding_sighash_interpreters_agree`, `FundingAuthTargets.openAccept_hash_linked`, `EcdsaBridgeTargets.fundingSignedValid_iff_vendor`, `EcdsaBridgeTargets.funding_sighash_interpreters_agree_vendor`, `EcdsaDomainTargets.not_digestBindsMod_any_tag`, `EcdsaDomainTargets.digest_domain_dichotomy` | Handshake constructs the hash link; joint open/accept shares it; positive-direction vendored P2WSH execution; BIP 143 digest/locktime constructed and consumed by the vendor checker; conditional `VendorEcdsaBridge` transfer added in wave 8; wave 10 proves no fixed tag satisfies `DigestBindsMod` and isolates the canonical value-`< n` domain repair; abstract EC/transaction-validity context and finite C1 admission retained |
| `LN-L1-003` | `ReorgTargets.reorg_preserves_channel_safety`, `deep_reorg_separate_failure_mode` | Common tip, common-prefix arithmetic, bounded-depth invariant; deep reorg is a separate failure mode |
| `LN-L1-004` | `ToLocalScriptTargets.toLocalScriptFull_carries_csv_and_revocationKey`, `..._commits_delay_and_revocationKey`, `commitmentOutputs_toLocal_commits_delay_and_revocationKey`, `InterpreterBridgeTargets.toLocal_delayed_interpreters_agree`, `InterpreterRevocationTargets.toLocal_revocation_interpreters_agree`, `SighashBridgeTargets.toLocal_sighash_interpreters_agree`, `SequenceContextTargets.toLocal_delayed_realChecker_refinement`, `TxValidTransferTargets.txCheckerFor_some_eq_realCheckerOf`, `TxValidTransferTargets.toLocal_delayed_txCheckerFor_refinement`, `EcdsaBridgeTargets.model_verify_eq_realChecker_seam`, `EcdsaBridgeTargets.toLocal_revocation_interpreters_agree_vendor`, `EcdsaDomainTargets.not_digestBindsMod_any_tag`, `EcdsaDomainTargets.digest_domain_dichotomy` | Full two-branch byte template plus vendored delayed and revocation execution with constructed BIP 143 digest/locktime; decoded BIP 68/112 context is exact and transferred to the real checker; wave 8 proves the exact known-amount `txCheckerFor` transfer and the `minimalData`/`csv ≥ 32768` edges; wave 10 proves the tag-independent digest-domain obstruction and the canonical-domain repair; known-amount and concrete-EC boundaries remain explicit |
| `LN-L1-006` | `WeightTargets.commitmentBaseWeight_model_target` | BOLT 3 fee-basis constants `724`/`1124` and `172` per untrimmed HTLC; exact 8 WU anchor serialization gap retained |
| `LN-CR-005` | `TLVStream.wellFormed_iff_pairwise`, `wellFormed_record_type_unique` | Exact theorem-level characterization; out-of-domain counterexample retained |
| `LN-CH-003` | `Commitment.output_ordering`, `CommitmentTx.migratedFrom_outputsNet_perm_commitmentOutputs`, `CommitmentTypes.CommitmentTx.migrateNet_canonicalOutputs_eq_commitmentOutputs`, `CommitmentConsumer.migratedConsumerOutputs_eq_consumerOutputs_of_migrated`, `CommitmentConsumerSites.commitment_signed_full_covers_migrated`, `CommitmentConsumerSites.migratedConsumerOutputs_eq_viewOfState_outputs`, `CommitmentConsumerSites.viewOfState_outputs_perm_netConsumerOutputs` | Rich `CommitmentTx` model with script/dust/CLTV; five-field gross/net record layer; arbitrary-dust canonical permutation/refinement; normal-form consumer migration; wave 8 adds the proof-layer `SignedState.toCommitmentTx` adapter and concrete sites, but no production `CommitmentTx` consumer; D12 still refutes legacy `commitmentOutputs` |
| `LN-CH-005` | `Fee.commitmentSigningGate_rejected_iff_insufficient`, `..._iff_no_checkedSigning` | Exact fee gate; normal-phase transition form explicit |
| `LN-HT-004` | `HTLC.dir_id_unique`, `id_unique_of_reachable_cross`, `tagged_id_unique_of_reachable`, `tagged_ids_nodup_of_reachable`, `cross_direction_duplicate_tagged` | Per-sender uniqueness; direction-tagged ids are globally unique; the untagged global claim needs `CrossDisjoint` and is otherwise refuted |
| `LN-PR-003` | `Handshake.funding_signed_signing_contract`, `SighashTargets.funding_and_commitment_signing_contract`, `KeyModelTargets.funding_signature_attribution`, `AcceptPayloadTargets.stored_accept_payload_attribution`, `AcceptPayloadTargets.acceptPayload_not_proof_of_possession`, `PopProtocolTargets.challengeMessage_injective_of_valid`, `PopProtocolTargets.accepted_funding_attribution`, `PopProtocolTargets.popSound_of_keySoundOn`, `PopProtocolTargets.pop_protocol_summary` | Conditional on `FundingSigningLaw` + `KeyBinding`; joint funding/commitment contract; secret-key model attributes under `KeyBinding`; wave 8 stores the accept payload with provenance and proves storage is not proof of possession; wave 10 adds a concrete challenge-response PoP with fixed-width injectivity, honest completeness, `PopKeySoundOn`/`PopExtractionOn` derivation, and replay counterexamples; C3/generation alone is insufficient |
| `LN-PR-004` | `ProtocolWireTargets.commitment_signed_full_covers_exact`, `protocol_wire_summary`, `SighashTargets.SighashProduces.coverage`, `SighashViewBindingTargets.commitmentSignature_binds_viewOfState`, `SighashTargets.CommitmentWire.txBytes_parse`, `Bip143Preimage.preimageBytes_eq_bip143MsgL_ofTx`, `commitmentBip143Preimage_eq_bip143MsgL`, `HtlcPreimageTargets.htlcBip143Preimage_eq_bip143MsgL`, `HtlcPreimageTargets.HtlcSpend.successPreimage_eq_bip143MsgL`, `HtlcPreimageTargets.HtlcSpend.timeoutPreimage_eq_bip143MsgL`, `HtlcPreimageTargets.htlc_preimage_target_summary`, `CoverageWitnessTargets.decodeCoverage_canonical`, `CoverageWitnessTargets.no_legacy_only_coverage_decoder`, `CoverageWitnessTargets.coverage_witness_summary` | `CommitmentSignedFull` plus exact BOLT 3 transaction wire layouts/parser round-trips; C3-derived digests; conditional digest-to-view binding; commitment and HTLC second-stage preimage byte equality; wave 10 adds a constructive per-HTLC coverage witness, proves the canonical decode, and rules out every legacy-only decoder/selector; explicit 20-byte hash-image/amount and display-order boundaries retained |
| `LN-PR-001` | `Handshake.open_bounds`, `OpenChannelWireTargets.openChannelWire_end_to_end`, `OpenChannelWire.toFundingParams_hash_linked`, `OpenChannelWireTargets.acceptKey_bound_before_fundingCreated_wire`, `TransportAuthTargets.transport_authenticated_attributed`, `TransportAuthTargets.authenticated_delivery_reaches_fundingCreated`, `TransportAuthTargets.transport_auth_summary` | Type-32 `open_channel` wire record projects to `Handshake.OpenChannel` and funding; `FundingPhase` reachable end-to-end; wave 10 separates transport authentication from explicit `SessionKeyBinding`, composes attributed delivery with the funding route, and retains the no-wire-sender/key-ownership boundaries |
| `LN-RT-002` | `Gossip.update_monotone`, `GossipStoreEpochTargets.epochFold_gossip_eq_canonicalStoreView_rawFold`, `Gossip.replacedUpdates_timestamp_lt`, `GossipStoreEpochTargets.StoreEpoch.epochFold_store_eq_foldl`, `NodeIdentityTargets.canonical_distinct_nodes_no_oriented_store_link`, `NodeIdentityTargets.rotation_preserves_wireMember`, `NodeIdentityTargets.missing_endpoint_channel_admitted` | Update monotonicity plus the wave-8 epoch/replacement-history square; wave 10 proves no antisymmetric store-only rotation link, requires an explicit `RotationWitness` for linkage, shows signatures are not preserved, and separates wire membership from the core admission transition; identity across rotation, chain existence, address parsing, and rate limits remain open |
| `LN-RT-006` | `GossipTargets.gossip_graph_only_valid_announcements` | Reachable signature-gated `admitGossip` states; raw `applyGossip` remains unfiltered and is proved not to refine canonical admission; the canonical-store wrapper is the supported path |

The earlier proof-wave promotions remain valid with their existing caveats
(`LN-CR-001/002/003`, `LN-CH-002`, `LN-HT-003`, `LN-PR-001`, `LN-PR-006`,
`LN-SEC-005`, and the wave-1 rows). Full notes are in
`docs/THEOREM-INDEX.md` and the reports under `agents/reports/`.

## Trust boundary

### C1 — SHA-256

`PrimitiveModel` has no global preimage-resistance field. C1 is 32-byte
payment-preimage collision resistance plus a finite, explicitly admitted
pair-level collision-free condition where a construction needs it. It is not a
global injectivity axiom and does not by itself bind arbitrary 71-byte funding
witness scripts.

### C3 — signatures

C3 is an exact algebraic signing/verification contract plus message binding
and domain separation. It does not prove signing completeness, key attribution,
or EUF-CMA. `LN-PR-003` keeps those as explicit hypotheses.

### C7/C8 — onion

C7 is the deterministic onion construction; C8 is finite-message HMAC binding.
Global HMAC PRF security is not claimed, and the D07 counterexample remains.

### L1 scripts

Scripts are byte templates plus an explicit stack-machine model in
`SpendTargets.lean`. `InterpreterBridgeTargets` imports the vendored
`Bitcoin/Interpreter/Defs.lean`, proves the model serializer equal to the
vendor `serializeOpcodes`, and executes the positive funding 2-of-2 and delayed
`to_local` branches through `verifyWitnessProgram`.
`InterpreterRevocationTargets` adds the revocation branch, branch selection,
and negative cases. `LnLean/Bitcoin/Sighash.lean` models the BIP 143 witness-v0
preimage and proves byte equality with the vendored implementation;
`SighashBridgeTargets` constructs `LocktimeEnv` and proves the checker consumes
the model digest, and `SequenceContextTargets` now characterizes the decoded
BIP 68/112 context exactly and transfers the delayed checker to the real
checker. It is still not a complete consensus interpreter: the EC verifier is
abstract, spent amount/outpoint and `TxValidation.Full` context are explicit
inputs, sequence-range/`minimalData` policy edges remain, CHECKMULTISIG is
2-of-2, and NULLDUMMY is ignored. `MODEL-01` remains open.

### Network / liveness

Safety results quantify over the modelled schedules; liveness results keep
fairness, fee-schedule, or watchtower hypotheses explicit. Computational
cryptographic reductions and full network semantics are not modelled.

## Proof-wave 5 bridge results

Wave 5 added eight modules and strengthened five catalog targets without adding
catalog rows:

* the vendored interpreter now executes the funding 2-of-2 and delayed
  `to_local` branches, with the remaining delay/sighash/revocation boundaries
  explicit;
* the funding hash link is constructed from the handshake;
* the commitment model has an arbitrary-dust net/gross refinement and
  effective-fee accounting, with the literal `Types.lean` field placement still
  an integration patch;
* a structural BOLT 3 sighash serializer derives commitment and HTLC digests
  under C3, with the bit-exact encoding and view-binding collision gaps
  explicit;
* the update state machine has an additive `UpdateStep` layer and E37
  refinement;
* gossip has direction-keyed attribution, `NodeId → PubKey` consistency, and
  canonical dedup under explicit invariants;
* BigSize/TLV conformance now includes transport framing and pinned
  rust-lightning differential fixtures;
* the computational-security limits document and game/reduction interface are
  in place, but no reduction is claimed.

## Proof-wave 6 residual-gap results

Wave 6 added one model module and six proof modules, strengthened four catalog
rows from 67 to 73 targets, and kept the 48-row catalog gate:

* BIP 143 witness-v0 is modelled and proved byte-equal to the vendored
  implementation; the checker consumes the constructed digest and
  `LocktimeEnv` (`L1-08` closed conditionally);
* the `to_local` revocation branch executes through the vendored interpreter,
  with branch-selection and negative cases (`L1-02` positive branches bridged);
* the five-field gross/net commitment record patch is integrated, with
  migration, conservation, effective-fee, and canonical-refinement theorems;
* BOLT 3 transaction wire layouts have exact serialization/parser round-trips;
  the full preimage byte equality to the vendor hash input was closed in wave 8;
* digest binding lifts to view binding under explicit collision-free /
  serialization hypotheses, with a mechanized counterexample showing C1+C3
  alone are insufficient;
* the commitment dance has an additive `DanceStep`/`DanceReachable` layer with
  round, revocation-ordering, stale-commitment, and preservation invariants;
* canonical gossip admission derives `NodeKeyConsistent` and
  `CanonicalAnnouncements` for reachable states, while raw `applyGossip`
  remains outside those guarantees;
* BOLT 8 transport framing is promoted into `LnLean/Wire/Transport`, and the
  rust-lightning fixtures have deterministic provenance checks; live cargo
  regeneration is still blocked.

## Proof-wave 7 residual-gap results

Wave 7 added one crypto model and six proof modules, strengthened six catalog
rows from 73 to 79 targets, and kept the 48-row catalog gate:

* the decoded BIP 68/112 sequence context is characterized exactly and the
  delayed branch is refined at `verifyImpl` and `RealChecker.realCheckerOf`;
* the commitment-wire BIP 143 preimage is byte-equal to the vendored
  `bip143MsgL`/`encode`, with ten-field order, vendored sub-hashes, and
  179/412-byte vectors; the HTLC-wire instantiation was closed in wave 8;
* the legacy commitment consumer path is migrated and refined, with a
  mechanized coverage counterexample and the normal-form premise explicit;
* the literal unguarded `ProtocolEvent` fold is proved impossible; the guarded
  fold/refinement (`GuardedStep`, `GuardedUpdateStep`, `danceStep_iff_guardedStep`)
  is the strongest compatible form;
* raw gossip insertion is proved not to refine canonical admission; the
  canonical-store wrapper, refinement square, reachable invariant, and
  impossibility of canonical-preserving raw extensions are proved;
* the pinned rust-lightning live harness runs offline and agrees on 26/26
  BigSize, 3/3 TLV, and 4/4 wire rows, with a hash-pinned transcript;
* `open_channel` and the funding phase machine are modelled, with the joint
  construction and finite-C1 key-set determination proved; the `Messages.lean`
  wire integration remains an exact patch;
* a secret-key/signer model proves attribution under the unchanged
  `KeyBinding` and mechanizes why key generation plus signing does not imply
  attribution.

## What remains open

The catalog is closed, but the repository is not release-ready. The living list
is [`docs/OPEN-ISSUES.md`](OPEN-ISSUES.md). The P0 blockers are:

* `OPS-01` — the public `--from-git` vendor path is tested locally and hosted
  CI runs `39175507618` and `39177572471` executed the pinned-vendor full build;
* `OPS-02` — no `LICENSE`; a neutral decision matrix is ready;
* `OPS-03` — no release tag and `main` is behind; a release checklist is ready;
* `L1-01`/`L1-02`/`L1-07` — the positive funding, delayed, and revocation
  branches execute through the vendored interpreter with a constructed BIP 143
  digest and an exact decoded sequence context; wave 8 also proves the exact
  known-amount `txCheckerFor` transfer and the sequence/`minimalData` edges.
  Wave 9 characterizes the concrete EC boundary sharply: at the current untyped
  `ByteArray` interface a pointwise `VendorEcdsaBridge` instance is forced to
  total rejection, so no non-vacuous concrete verifier theorem exists there.
  The amount/outpoint context and unconditional `ConsensusSpendBridge` remain
  open, and the EC seam must keep an explicit `VendorEcdsaContract`/EUF-CMA
  hypothesis. Wave 10 sharpens this further: no fixed tag satisfies
  `DigestBindsMod` on arbitrary bytes, even at fixed 33-byte length; the
  canonical value-`< n` domain is the exact algebraic repair available without
  a computational hash assumption.

Wave 7 closed `CH-01` (consumer path), `RT-01` (canonical wrapper and raw
non-refinement), `CONF-02` (live finite comparison), and `MODEL-02`/`MODEL-03`
(guarded fold; literal fold refuted). Wave 8 closed the known-amount
`TxValidation.Full`/`txCheckerFor` transfer, the `HtlcWire` second-stage
preimage, the type-32 `open_channel` wire path, the proof-layer consumer
adapter, and the update/announcement epoch history.

Still open: a non-vacuous concrete EC verifier at this interface or an explicit
`VendorEcdsaContract` (`L1-01`, `L1-07`), transport authentication/C3 and key
ownership for `open_channel` beyond the explicit `EnvelopeAttributed`
hypothesis (`L1-03`), registration proof-of-possession beyond the explicit
`KeyBinding`/`PopSound`/`PopProducedBy` hypotheses (`PR-01`), a legacy
wire-only coverage decoder and the conditional view binding (`PR-02`),
identity/linkage across a `nodeId` rotation plus wire membership, address
parsing, and rate limits (`RT-02`), additional live message encodings and
node-level interop (`CONF-01`), computational C1/C3/C8 reductions (`CR-01`,
`SEC-01`), and release packaging (`OPS-01`–`OPS-04`). The
known-amount/sequence-policy edges for `L1-02` are mechanized; no
`TxValidation.Full` transfer gap remains.

## Reproduce

```sh
export PATH=/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
cd /home/ubuntu/ln-lean-repair

LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock lake build
grep -RInE '^[[:space:]]*sorry[[:space:]]*$' LnLean --include='*.lean' || true

./scripts/check.sh
python3 scripts/check-final.py
python3 scripts/check-catalog.py --audit
python3 scripts/check-catalog.py --allow-planned
python3 scripts/check-conformance.py
python3 scripts/verify-anchors.py
./scripts/verify-vendor.sh
```

Do not run `scripts/collect-obligations.py` merely to inspect status: it
rewrites `docs/OBLIGATIONS-GENERATED.md` and
`agents/status/obligations.json`. Regenerate them deliberately as part of an
integration commit.

## Not claimed

- No theorem here is a proof of Lightning Network security, Bitcoin consensus,
  or computational cryptographic hardness.
- A green build and zero actual `sorry` terms do not imply the catalog rows are
  unconditional statements of the English claims. The scope caveats above are
  part of their meaning.
- The conformance suite is finite BigSize/TLV/framing vector conformance plus
offline pinned rust-lightning fixtures, not a full implementation or live
differential test.
- The 30 proof-wave promotions (eleven in wave 1, eight in wave 2, eleven in
  wave 3) are exact model-level targets; waves 4, 5, and 6 strengthen targets
  rather than adding rows. Describing any of this as full protocol verification
  would be false.


## Proof-wave 8 transfer, wire, and registration results

Wave 8 added seven proof modules and additive protocol/routing/conformance
changes, strengthened seven catalog rows from 79 to **100 targets**, and kept
the 48-row catalog gate:

* `TxValidTransferTargets` proves `txCheckerFor tx nIn (some amount)` is exactly
  `realCheckerOf tx nIn amount`, transfers the delayed/revocation branches, and
  mechanizes the missing-amount, `minimalData`, and `csv ≥ 32768` boundaries;
* `HtlcPreimageTargets` proves the exact `HtlcWire` BIP 143 preimage byte
  equality, synthesizes 143/136-byte HTLC scriptCodes, and records 300/293-byte
  preimage sizes and display-order txid conversion;
* `OpenChannelWireTargets` adds the type-32 `open_channel` constructor and its
  projection/funding/`FundingPhase` end-to-end path; transport attribution
  remains explicit;
* `AcceptPayloadTargets` stores the received `accept_channel` payload with
  provenance and proves the negative proof-of-possession result; attribution
  remains conditional on `KeyBinding`;
* `CommitmentConsumerSitesTargets` supplies the proof-layer consumer adapter
  and concrete sites; there is still no production `CommitmentTx` consumer;
* `EcdsaBridgeTargets` supplies the sharp conditional `VendorEcdsaBridge`
  transfer for the funding/commitment/close verifier paths; EUF-CMA and
  key-binding remain explicit hypotheses;
* `ConformanceDiffTargets` adds six BOLT 2 message vectors, 29 `decide`
  theorems, and 13/13 mutation controls; the live message row remains deferred;
* `GossipStoreEpochTargets` adds typed replacement history and the
  sequence-level canonical-store square, with two divergence witnesses showing
  both admission hypotheses are necessary. Node-announcement canonicalisation
  remains open.


## Wave H 48-lane integration

The Wave H branch adds **45 independent proof modules** under
`LnLean/Proofs/WaveH/`, integrated after the public-core bump and the remote
Wave 8 residual lanes. The merged tree keeps all remote changes and adds:

* H01/H04/H06/H30/H31/H32 — unconditional per-input
  `txCheckerFor (some amount) = realCheckerOf`, the concrete one-input P2WSH
  `scriptLaneTx`/`txVerdictFull` composition, exact `csv < 32768` and
  `MINIMALDATA` boundaries, and the funding/revocation checker instances;
* H07/H08/H09/H11/H12/H37 — HTLC BIP 143 preimage/digest equality, four BOLT 3
  witness scripts with exact scriptCode synthesis, serialization-domain and
  framing boundaries;
* H13–H22 — the **319-byte** BOLT 2 type-32 `open_channel` mandatory payload
  (correcting the earlier 313-byte sketch), the 270-byte `accept_channel`
  payload, and the additive stored-accept/PoP contract;
* H23–H28 — commitment consumer/view adapters, downstream accounting, and the
  construction-site coverage-loss counterexample;
* H33/H34 — `L1-04` closed with the `1116 + 172*k` witness weight vs
  `1124 + 172*k` fee basis (the 8 WU is `count_tx_out`), and `L1-05` closed
  with the 71-byte script-injectivity counterexample plus a domain-separated
  commitment;
* H39–H45 — epoch-gossip sequence projection and supersession, the concrete
  schedule/fairness liveness model, lossless reduction arithmetic and
  separations, and conditional reorg preservation.

H20 was adapted to the remote `HandshakeState` change that removed
`DecidableEq` (the added `acceptChannel?` field); its concrete witness
transitions are now proved by definitional equality rather than `decide`.

## Proof-wave 9 boundary characterization results

Wave 9 added five proof modules and strengthened six catalog rows from 100 to
**142 resolved targets**, extending the audit to **269 headline theorems**:

* `EcdsaConcreteTargets` proves the exact concrete-EC dichotomy
  (`eufCma_vendorVerify_iff_totalReject`, `bridged_model_totalReject`,
  `exists_bridged_model_iff_totalReject`) and identifies `ResidueBinding` +
  `KeyBinding` as the faithful conditional contract. This is an obstruction
  result, not an ECDSA-security theorem.
* `OpenChannelRoutingTargets` adds transport attribution by key equality, the
  concrete routed `open_channel` → `accept_channel` → `funding_created` path,
  and non-attribution/no-signature boundaries; it does not authenticate a
  sender from the wire payload.
* `AttributionGameTargets` proves conditional registration/PoP attribution,
  storage-is-not-possession, and the dropped-`KeyBinding` counterexample under
  explicit `PopSound`/`PopProducedBy` hypotheses.
* `PreimageCoverageTargets` gives the exact eight-field arbitrary-preimage
  characterization, conditional byte/digest/signature transfer, and retained
  dropped-locktime/amount counterexamples; legacy wire-only coverage remains
  negative.
* `NodeCanonicalTargets` adds strict-timestamp node replacement, rotation and
  equal-timestamp boundaries, raw-extension impossibility, and epoch-square
  lifting. `RT-02` is narrowed, not closed.
* `ConformanceDiffTargets` adds one live BOLT 2 `channel_ready` payload row
  through the pinned rust-lightning `Writeable` implementation, with 180 Lean
  references and 14/14 mutation controls. This is finite/public-API evidence,
  not node-level interop.
