# Open Issues and Swarm Roadmap

**Status:** living roadmap after proof-wave 8; wave 8 is integrated on
`repair/integrated` and the wave-9 candidates are tracked below.
**Branch:** `repair/integrated`.
**Base commit:** `9bafdab` (wave 8 code); wave 8 launch is `50d78ed`;
proof-wave 7 code is `b48d041`; wave 7 launch is `3180581`; proof-wave 6 code
is `0a3a5fb` (proof-wave 5 code is `6389baa`; proof-wave 4 code at `26ced90`).
**Catalog gate:** 48/48 rows `proved`, 0 `statement-only`, 0 unresolved,
100 targets.
**Full build:** 250 jobs, RC 0.
**Rule:** this file is updated by every wave. Closed issues keep their id and
get a `closed` row; new gaps get a new id in the same wave that discovers them.

The catalog is green, but the catalog is a model-level claim. The issues below
are the remaining distance between this tree and a credible public release or
a full Lightning verification claim. Do not turn an assumption into a theorem
by rewording it; add the missing model or keep the scope note.

## Priority summary

| Priority | Meaning | Current issues |
|---|---|---|
| **P0** | Blocks a public release or a reproducible build | `OPS-02`, `OPS-03` |
| **P0** | Blocks any claim of spendable L1 scripts | `L1-01`, `L1-02`, `L1-07` |
| **P1** | Major model/verification gap; codeable in a wave | `L1-03`, `L1-04`, `L1-05`, `PR-01`, `PR-02`, `RT-02` |
| **P2** | Longer-term research / conformance / network assumptions | `CR-01`, `L1-06`, `NET-01`, `CONF-01`, `MODEL-01`, `SEC-01` |

## Open issues

| Id | Priority | Status | Issue | Evidence / current boundary | Next action |
|---|---|---|---|---|---|
| `OPS-01` | P0 | closed (hosted CI verified) | Public CI cannot run the full build from a clean checkout | `repair/pubbump` replaced the private `f950806` snapshot with a 149-file copy of public `btc-lean` `spec/core` at `4f5c4f8`; `vendor/VENDOR-SHA256` is regenerated. `scripts/fetch-vendor.sh` now pins `4f5c4f8`, and `--from-git` fetches exactly that commit and verifies the 149-file manifest. CI uses an explicitly configured checksummed archive when present, and otherwise runs `--from-git`; the full build is no longer a skip gate. Local `--from-git --dry-run`, the full 250-job build, and all gates pass. Hosted CI run `39175507618` on `60318ad` and run `39177572471` on `e3e0aa8` completed both the source-level gates and the `Build gate (pinned vendor snapshot required)` job, including `lake build`; the intermediate `68f283c` run was superseded and cancelled. | No further action for the public path; keep `VENDOR_ARTIFACT_URL`/`VENDOR_ARTIFACT_SHA256` optional for offline runners. |
| `OPS-02` | P0 | open; decision support ready | No `LICENSE` | No license file in the tree; `docs/LICENSE-DECISION.md` provides a neutral MIT/Apache-2.0/dual matrix and third-party notice inventory. The vendor copy now comes from the public MIT `btc-lean` repository at `4f5c4f8`, but the repository still needs an explicit project license and notices. | Maintainer chooses the license and copyright holder, then adds `LICENSE`/`NOTICE`; do not let an agent invent one |
| `OPS-03` | P0 | open; checklist ready | No release tag and `main` is behind | `origin/main` is old; `repair/integrated` is the active branch; no tag; `docs/RELEASE-CHECKLIST.md` records the pre-tag gates and human choices | Decide PR/merge path to `main`, cut a signed/annotated tag, and publish release notes |
| `OPS-04` | P2 | closed (public copy) | Vendor snapshot contained an absolute symlink | The `repair/pubbump` public-core copy removes the dangling `btc-lean-core` self-symlink; `vendor/btc-lean-core` is now a real directory, and `VENDOR-SHA256` covers all 149 regular files. | No further action; keep the checksum manifest authoritative. |
| `L1-01` | P0 | open (concrete conditional EC bridge) | P2WSH / `OP_CHECKMULTISIG` spendability is not bridged to the vendored interpreter | `SpendTargets.lean` defines the explicit stack model; `InterpreterBridgeTargets` imports the vendored `Bitcoin.Interpreter.Defs` evaluator, proves the model serializer equal to the vendor `serializeOpcodes`, parses the wire list back exactly, and proves `funding_interpreters_agree` for the positive 2-of-2 funding witness. `SighashBridgeTargets` builds the BIP 143 witness-v0 digest and a `LocktimeEnv` to the vendor `ecdsaEntry`. This is not unconditional consensus spendability: ECDSA remains an abstract verifier, spent amount/outpoint and transaction-validity context are explicit inputs, and the scope is positive-direction P2WSH. Wave 8 `EcdsaBridgeTargets` supplies the exact conditional `VendorEcdsaBridge` transfer (`fundingSignedValid_iff_vendor`), the argument-order/DER/hashtype seam, and the funding/commitment/close interpreter agreements; the bridge is still an explicit hypothesis, not an unconditional verifier theorem. | Keep the constructed sighash/context path and positive-direction scope; a full consensus claim still needs `VendorEcdsaBridge`/EUF-CMA and the spent-amount/transaction-validity context. |
| `L1-02` | P0 | open (tx pipeline transfer exact; known-amount/EC boundary) | `to_local` CSV/revocation execution has a known-amount/concrete-EC boundary | `InterpreterBridgeTargets` executes the delayed branch; `InterpreterRevocationTargets` executes the revocation branch with branch-selection and negative cases. `SequenceContextTargets` proves `decodeNum_delayBytes`, non-negativity/disable-bit facts, exact `checkSequenceDef_delay_iff` (version ≥ 2, height domain, `csv ≤ masked sequence`), `toLocal_delayed_sequence_context_refinement`, and `toLocal_delayed_checkerOf_refinement` at `Bitcoin.Crypto.Ecdsa.Verify.verifyImpl`; `checkerOf_eq_realCheckerOf` transfers to `RealChecker.realCheckerOf` for `nIn < tx.vin.length`, with bad-signature failures mechanized at every evaluator layer. Wave 8 `TxValidTransferTargets` proves `txCheckerFor tx nIn (some amount) = realCheckerOf tx nIn amount`, transfers the delayed/revocation branches, mechanizes the missing-amount case as fail-closed, and proves the `minimalData` and `csv ≥ 32768` decode/verdict edges (including the `csv = 32768` collapse to `0`). The remaining boundary is the known spent amount and the concrete EC verifier, not a `TxValidation.Full` transfer gap. | Keep the known-amount and concrete-EC boundaries explicit; no `TxValidation.Full` transfer gap remains. |
| `L1-03` | P1 | open (transport attribution; wire path closed) | `FundingScriptHashLinked` is a construction invariant | `FundingNegotiation.toFundingParams` computes `witnessScriptHash := H(witnessScript.bytes)` from ordered funding keys, and `FundingLinkTargets` proves the ordered P2WSH output. Wave 7 adds `OpenChannel`, its `toFundingNegotiation`/`toFundingParams` projection, a separate `FundingPhase`/`FundingPhaseEvent`/`fundingStep`/`FundingReachable` machine, and `FundingAuthTargets`: joint open/accept construction, finite-C1 output-determines-key-set, key provenance, phase-link theorems, and the `same_message_distinct_senders` scope counterexample. Wave 8 adds `Msg.openChannel`/`MsgKind.openChannel`, `OpenChannelWire` with six-key/type/length/identity laws, projection to `Handshake.OpenChannel`, funding construction, and end-to-end `FundingPhase` reachability. | No wire patch remains; keep the finite C1 admission, transport-attribution, and `HandshakeState` routing caveats explicit. |
| `L1-04` | P1 | open | Anchor weight has an 8 WU spec/serialization gap | `LN-L1-006` proves `serializedAnchorWeight + 8 = 1124 + 172*k`; witness serialization and the Appendix A `count_tx_out` discrepancy remain | Model the missing witness/CompactSize bytes or document the negotiated fee-basis interpretation permanently |
| `L1-05` | P1 | open (partially mitigated) | C1 is 32-byte payment-preimage collision resistance, not 71-byte script injectivity | `c1_32_does_not_bind_funding_witnessScripts` remains; the P2WSH reverse direction still uses a finite pair-level `CollisionFreeOn` admission. `FundingLinkTargets` adds the construction lemma for the actual revealed script but does not assume global or 71-byte injectivity. | Keep the finite admission; if a global claim is required, model a domain-separated script commitment rather than SHA-256 injectivity. |
| `L1-06` | P2 | open | Reorg result is conditional on common tip and bounded depth | `LN-L1-003` keeps `SameChain`, common-prefix arithmetic, and `OutOfReachOf` explicit; deep reorgs have a separate failure mode | Connect the hypotheses to the L1 chain model or leave the conditional theorem as the deliverable |
| `L1-07` | P0 | open (known-amount/EC boundary) | Vendored real interpreter is imported for the positive L1 branches | `InterpreterBridgeTargets` proves funding 2-of-2 and delayed agreement; `InterpreterRevocationTargets` proves the revocation branch; `SighashBridgeTargets` constructs the digest/`LocktimeEnv`. Wave 7's `SequenceContextTargets` proves the exact BIP 68/112 sequence context and transfers the delayed checker to `Bitcoin.Crypto.Ecdsa.Verify.verifyImpl` and `RealChecker.realCheckerOf` for `nIn < tx.vin.length`. Wave 8 transfers the delayed/revocation branches to `txCheckerFor (some amount)` and closes the `TxValidation.Full` transfer for a known amount; sequence range/policy edges are mechanized. The bridge remains positive-direction with an explicit amount/EC boundary, and unconditional `ConsensusSpendBridge` is still open. | No `TxValidation.Full` transfer gap remains for a known spent amount; keep the positive-direction and amount/EC boundaries explicit. |
| `L1-08` | P0 | closed (constructed under explicit context) | BIP 143 sighash and locktime/sequence context were assumptions in the L1 bridge | `LnLean/Bitcoin/Sighash.lean` defines the ten-field BIP 143 witness-v0 preimage, serializers, sub-hashes, `ofTx`, `digest`, and guarded `sighashWitnessV0`; it proves byte-equality to the vendored `signatureHashBip143Impl`/`signatureHashBip143` and mechanizes ANYONECANPAY/zero-sub-hash omissions. `SighashBridgeTargets` constructs `LocktimeEnv` from transaction fields and proves `checker_consumes_model_digest`, instantiating the funding and delayed `to_local` agreements. Boundaries: abstract EC verifier, explicit spent amount/outpoint and transaction-validity context, positive P2WSH direction, pinned flags. | No further action for the digest construction; keep the explicit context and positive-direction scope. |
| `CR-01` | P2 | open (limits interface added) | No computational cryptographic reductions | C1/C3/C8 are exact algebraic laws; `docs/CRYPTO-LIMITS.md` and `SecurityGameTargets.lean` now state the missing probability/complexity model, query bounds, and the exact reduction interface. `AdvantageReduction.bound` is arithmetic conditional on an assumed tightness field; no reduction is proved. | Choose a probability/complexity foundation and real games for C1/C3/C8; do not claim computational security from the algebraic model. |
| `PR-01` | P1 | open (accept payload stored; attribution conditional) | `FundingSigningLaw` / `KeyBinding` are hypotheses | `SighashTargets` adds the honest signing constructor and joint funding/commitment contract. Wave 7 adds `Crypto/KeyModel.lean`: `SecretKey`, `KeyPair`, deterministic `KeyModel`, domain-scoped `correctOn`, `Owns`, and `Signer`. `KeyModelTargets` proves `funding_signature_attribution` under the unchanged `KeyBinding`, `AdvertisesKey`/negotiation key equality, funding-signature validity, a non-vacuous pinned witness, and `key_generation_not_key_attribution` (generation + secret-key signing + `EufCma` do not imply attribution). Wave 8 adds `HandshakeState.acceptChannel?`, `handshakeStepRecvAccept`, provenance/stability lemmas, and `StoredAccept`; `stored_accept_payload_attribution` remains conditional on `KeyBinding`, and `acceptPayload_not_proof_of_possession` mechanizes the registration boundary. The total `FundingSigningLaw` is still flagged as totality-tensioned. | No payload patch remains; keep the conditional `KeyBinding`/C1 attribution contract and the negative proof-of-possession result explicit. |
| `PR-02` | P1 | open (mitigated; HTLC bytes exact) | `CommitmentSigned` wire record lacks data for wire-only coverage | `SighashTargets` adds a BOLT 3-shaped structural commitment/HTLC serializer, `SighashProduces`, and `SighashProduces.coverage`, deriving the digest, commitment signature, and per-HTLC signatures under C3. Wave 6 adds exact BOLT 3 transaction wire layouts and parser round-trips; wave 7 proves the commitment-wire `Bip143Preimage` byte-equal to the vendored `bip143MsgL`/`encode`, with 179-byte and 412-byte vectors. `SighashViewBindingTargets` conditionally lifts digest binding to view binding. Wave 8 closes the HTLC-wire instantiation (`HtlcPreimageTargets`), so commitment and HTLC second-stage preimages are both byte-equal to the vendored encoder; arbitrary non-transaction-derived preimages still need the eight field-agreement hypotheses, and wire-only coverage remains conditional. | HTLC-wire bytes are now exact; keep the arbitrary-preimage field hypotheses and conditional view binding (`PR-06`). |
| `PR-05` | P1 | closed (commitment + HTLC second-stage bytes; explicit caveats) | BOLT 3 sighash preimage byte-equality across modelled wire paths | `SighashTargets` §13 proves `preimageBytes_eq_encode_bytes` for every `Bip143Preimage`, `preimageBytes_fields` for the ten-field consensus order, and `commitmentBip143Preimage_eq_bip143MsgL` on `CommitmentWire.toTx`; the vendored sub-hashes match `hashPrevouts`/`hashSequence`/`hashOutputs`, with 179-byte and 412-byte vectors. Arbitrary non-transaction-derived preimages reach the vendor encoder only under eight explicit field-agreement hypotheses (`ofTx` discharges them); Wave 8 `HtlcPreimageTargets` proves the same byte equality for every `HtlcWire`, synthesizes 143/136-byte HTLC-success/timeout scriptCodes, and proves 300/293-byte preimage sizes; display-order txid conversion, explicit 20-byte hash images, and the amount context remain documented. | No further wire-byte work; keep the explicit 20-byte hash-image/amount and display-order boundaries documented. |
| `PR-06` | P1 | closed (conditional view binding) | C3 binds signatures to digests, not directly to commitment/HTLC views | `SighashViewBindingTargets` proves `commitmentSignature_binds_view`, `commitmentSignature_binds_viewOfState`, `signature_binds_commitment_view_fields`, and `htlcSignature_binds_htlcView` under explicit `ViewDigestCollisionFree`/`HtlcDigestCollisionFree`/`SerializationBindsViews` hypotheses. `digest_binding_not_view_binding` mechanizes the counterexample showing C1+C3 alone are insufficient; `viewOfState_not_injective_in_state` and `htlcView_ignores_msat_fraction` record the scope boundaries. | Keep the explicit hypotheses and non-vacuity witnesses; no unconditional view binding is claimed. |
| `CH-01` | P1 | closed (proof-layer adapter; coverage caveat) | Rich `CommitmentTx` model is not the legacy consumer path | `S7-CH-CONSUMER` adds `CommitmentTx.consumerOutputs`, `migrateForConsumer`, `migratedConsumerOutputs`, `netConsumerOutputs`, `ofCommitment`, and `CommitmentPair.migrateNet`. `CommitmentConsumerTargets` proves the canonical permutation, normal-form preservation (`Migrated` + `UsesRecordNet`), and coverage-consumer equivalences. `legacyCoverage_not_preserved_by_net_migration` mechanizes the necessary no-trim/normal-form premise; Wave 8 adds the proof-layer `SignedState.toCommitmentTx` adapter, legacy-boundary equality/Perm theorems, a coverage bridge, and concrete site examples; there is still no production `CommitmentTx` consumer. D12 remains the unconditional ordering refutation. | No further migration work for the proof-layer adapter; keep the counterexample and normal-form hypotheses explicit, and do not claim a production consumer. |
| `CH-02` | P1 | closed (record layer integrated) | Second-stage fee and dust trimming were not integrated end-to-end | `CommitmentGrossNetTargets` adds the net output path, `trimmedValue`, `effectiveFeeSat`, and proves emitted + base fee + trimmed = funding and effective fee = base fee + trimmed. Wave 6 places `CommitmentHTLCOutput.netAmountSat` and stored `Commitment.trimmedTotalSat`; `CommitmentTypesTargets` proves the field-boundary dust, migration, conservation, effective-fee, and canonical refinement. The full tree build includes the five-field `LawfulBEq` update. | Keep the net path and record-layer theorems; legacy-consumer migration is tracked as `CH-01`. |
| `CH-03` | P1 | closed (record layer integrated) | Rich commitment outputs lacked BOLT-3 gross/net fields | `CommitmentTx` has `netAmountSat`/`trimmedSat`, and `CommitmentHTLCOutput.netAmountSat` plus stored `Commitment.trimmedTotalSat` are now in `Types.lean`; `CommitmentTypesTargets` proves the field-boundary dust test, migration, conservation, effective-fee accounting, and canonical refinement. The stored field is named `trimmedTotalSat` because the wave-5 computed function already uses `trimmedSat`; this is a naming choice, not a missing field. | No further field work; decide whether to rename `trimmedTotalSat` in a coordinated API change. |
| `CH-04` | P1 | closed (five-field patch applied) | Gross/net record fields were not fully integrated | `S6-CH-TYPES` applied the five-field patch and the parent updated the private `LawfulBEq CommitmentHTLCOutput` instance in `Conservation.lean`; the full 218-job build and strict catalog are green. Construction sites compile with the new field/default. | No further action; keep the `trimmedTotalSat` naming decision under `CH-03`. |
| `HT-01` | P1 | closed (tagged namespace) | Untagged global HTLC id uniqueness is false under BOLT 2 per-sender counters | `LN-HT-004` keeps per-sender `dir_id_unique`, the `CrossDisjoint` untagged form, and now the direction-tagged `HTLCTag` namespace with `tagged_id_unique_of_reachable`/`tagged_ids_nodup_of_reachable`. `cross_direction_duplicate_tagged` connects the old counterexample. The wire remains per-sender by BOLT 2 design. | No further model action; keep the tag documented as a model-side namespace, not a new wire encoding. |
| `RT-01` | P1 | closed (canonical wrapper; raw non-refinement proved) | Gossip key attribution and raw insertion are separate | `admitGossipAttributed`/`admitGossipDirected` gate updates on validity plus announced-key attribution; wave 6 derives `NodeKeyConsistent`/`CanonicalAnnouncements` on canonical reachable states. Wave 7 proves raw `applyGossip` is **not** a function refinement of canonical admission, supplies `applyGossipCanonicalStore` whose gossip/registration projection is exactly `admitGossipCanonical`, proves the sharp refinement square on canonical-shaped stores under admission gates and the raw global clock, and establishes the extended reachable-store invariant. A reachable boundary witness shows the canonical per-slot gate accepts an update the raw global clock rejects, and an impossibility theorem rules out canonical-preserving raw announcement extensions. Wave 8 adds the `StoreEpoch` replacement-history layer, `epochFold_gossip_eq_canonicalStoreView_rawFold`, and `StoreEpoch.epochFold_store_eq_foldl`, with two divergence witnesses showing both admission hypotheses are necessary. | No further action for the raw/canonical square; use the canonical wrapper and the epoch API as the supported path, and keep raw insertion documented as non-canonical. |
| `RT-02` | P1 | open (node-announcement canonicalisation) | Gossip node-announcement canonicalisation remains a design gap | `GossipCanonicalTargets` defines `admitGossipCanonical`, `ReachableCanonical`, and `CanonicalAdmitted`; closure/preservation proofs derive both invariants, with update supersession, node-key rotation, concrete non-vacuity, and conflict witnesses. The rotation boundary and raw-store caveat are explicit. Wave 8 adds the update/announcement epoch history and canonical square, but node-announcement canonicalisation remains open by design. | Keep the canonical update/announcement path and rotation witnesses green; node-announcement canonicalisation remains open. |
| `NET-01` | P2 | open | Network/liveness results depend on scheduling/fairness assumptions | `LN-SEC-003` keeps four `Assumptions P`; `LN-SEC-005` uses `FeeScheduleBounded`; `LN-SEC-006` requires a watchtower report | State the adversarial schedule/fairness model explicitly and prove one concrete eventual-delivery instance |
| `CONF-01` | P2 | open (BOLT 2 message vectors added; live row deferred) | No shared conformance suite against BOLT vectors | `tests/conformance/vectors.json` + `scripts/check-conformance.py` cover 61 BigSize/TLV vectors, 16 framing cases, 9 decoder-boundary cases, and 9 mutation controls; `ConformanceTargets.lean`/`ConformanceDiffTargets.lean` add 151 `decide` theorems. The checker is wired into CI. Wave 8 adds six BOLT 2 payload/field vectors, 29 `decide` theorems, and 13/13 mutation controls; the live message row remains deferred. This is finite-vector conformance, not a full implementation test; two TLV value-minimality/unknown-type cases are declared model gaps. | Add the live BOLT 2 message row when the pinned client can run offline; keep the vector suite green. |
| `CONF-02` | P2 | closed (live finite comparison) | No live differential conformance against rust-lightning | `tests/conformance/rust-lightning/pinned/` now contains a 188-package `Cargo.lock` and public-API `live_probe.rs`; `cargo test --offline --locked` passes both pinned tests. The live probe agrees field-by-field on **26/26 BigSize + 3/3 TLV**, and **4/4 wire** rows check live `LN_MAX_MSG_LEN=65535` (header arithmetic remains source-derived). `live-transcript.json` is SHA-256-pinned and rerun-byte-identical; the checker verifies transcript/probe/lock hashes, fixture digest, result counts, and forged-transcript mutation. Caveats: finite/public-API comparison, not node-level interop; transcript is evidence, not proof; clean machines need one networked `--fetch` before offline runs. | Keep the pinned live harness and transcript green; `CONF-01` remains open for additional encodings only. |
| `CONF-03` | P2 | closed (promoted + deterministic) | Transport framing was conformance-only and fixtures were offline transcriptions | `LnLean.Wire.Transport` contains the BOLT 8 length/frame/decoder model with the wave-5 theorem names, while production `Wire.unframe` remains payload-only and is proved to reject every transport frame. `generate.py` deterministically re-derives and provenance-checks the fixtures; wave 7 adds the live transcript and hash checks. | No further action; keep the promoted transport module, deterministic generator, and live harness green. |
| `MODEL-01` | P2 | open (narrowed) | No complete script interpreter / consensus semantics | Scripts have byte templates plus a vendored-interpreter bridge for positive funding, delayed, and revocation branches, with a constructed BIP 143 digest/locktime context. Still outside: a concrete EC verifier, transaction-validity model, full policy/flag semantics, NULLDUMMY, and unconditional `ConsensusSpendBridge`. | Keep the explicit positive-direction bridge and abstract EC/context boundary; do not claim full consensus script spendability. |
| `MODEL-02` | P2 | closed (guarded fold; literal fold refuted) | HTLC state-machine coverage is partial | Wave 7's `ProtocolEventFoldTargets` proves the literal unguarded fold is **impossible** without falsifying retained counterexamples (`literal_round_fold_refuted`, `literal_revoke_fold_refuted`, `fold_cannot_both_preserve_balance_and_carry_add`, `fold_cannot_both_preserve_htlcs_and_carry_add`). It supplies the strongest true guarded refinement: `GuardedStep`/`GuardedReachable`/`GuardedUpdateStep`/`GuardedUpdateReachable`, `guardedStep_iff_step_and_guards`, `danceStep_iff_guardedStep`, ordered/ledger/reserve preservation, and a guarded no-double-`commitment_signed` theorem. All wave-5/6 counterexamples are retained. | No further model action; keep the guarded layer and the literal-fold impossibility results. The downstream migration patches in the lane report must not be applied without resolving the retained counterexamples. |
| `MODEL-03` | P2 | closed (guarded fold; additive compatibility proved) | Commitment-dance transitions are separate from the core `Step` state machine | `State.lean` keeps `DanceEvent`/`DanceStep`/`DanceReachable` and the wave-6 dance results; wave 7 proves `danceStep_iff_guardedStep`, `guardedStep_commitmentSigned_iff_danceStep`, `guardedStep_revokeAndAck_iff_danceStep`, `guardedReachable_preserves_ordered`, and `guarded_no_double_commitmentSigned`. The guarded fold is the maximal compatible refinement; the unguarded `ProtocolEvent` fold is refuted. | No further fold action; keep the guarded compatibility layer and the impossibility boundary explicit. |
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

## Wave 6 lanes (complete)

Wave 6 launched from `201a0a0` and integrated seven new Lean files (one model
module and six proof modules). The catalog stayed at 48 rows and 0
statement-only; four existing rows were strengthened from 67 to 73 resolved
targets. Reports are under `agents/reports/swarm6/`.

| Lane | Issue(s) | Result | Owned files |
|---|---|---|---|
| `S6-L1-SIGHASH` | `L1-08`, `L1-07` | BIP 143 witness-v0 preimage/digest and guarded sighash; vendor byte equality; constructed `LocktimeEnv`; checker digest consumption and funding/to_local instantiations | new `LnLean/Bitcoin/Sighash.lean`, new `SighashBridgeTargets.lean` |
| `S6-L1-REVOKE` | `L1-02`, `L1-07` | Vendored revocation branch, branch selection, wrong-key/delayed-key/wrong-branch negatives; no missing vendor opcode | new `InterpreterRevocationTargets.lean` |
| `S6-CH-TYPES` | `CH-04`, `CH-03` | Five-field gross/net record patch, migration API, field-boundary conservation/effective-fee/canonical refinement; downstream `LawfulBEq` patch recorded | `LnLean/Channel/Types.lean`, `Commitment.lean`, new `CommitmentTypesTargets.lean` |
| `S6-PR-BITEXACT` | `PR-05`, `PR-02` | Exact BOLT 3 transaction wire layouts/parser round-trips, BIP 143 preimage size/vector, shared-view/digest refinement, script strictness counterexample | `SighashTargets.lean` §12 |
| `S6-PR-VIEWBIND` | `PR-06`, `PR-02` | Conditional signature-to-view binding, non-vacuity witnesses, digest-binding-only counterexample | new `SighashViewBindingTargets.lean` |
| `S6-MODEL-DANCE` | `MODEL-03`, `MODEL-02` | Additive dance layer, ordered round window, guard necessity, revocation ordering, no stale/revoked commitment, balance/HTLC/ledger/reserve preservation | `LnLean/Channel/State.lean`, new `CommitmentDanceTargets.lean` |
| `S6-GOSSIP-DERIVE` | `RT-02`, `RT-01` | Canonical admission/store, derived `NodeKeyConsistent`/`CanonicalAnnouncements`, rotation/supersession, raw-store caveat retained | `LnLean/Routing/Gossip.lean`, new `GossipCanonicalTargets.lean` |
| `S6-CONF-LIVE` | `CONF-03`, `CONF-02` | Promoted `Wire.Transport`, deterministic fixture provenance, 9 mutation controls; live cargo still blocked | `LnLean/Wire/Message.lean`, `ConformanceDiffTargets.lean`, `tests/conformance/**` |

Wave 6 raised the root build to 218 jobs and the audit to 163 headline
theorems. The remaining lane output is evidence for existing rows and the
wave-7 candidates below, not a claim of unconditional consensus execution or
computational security.

## Wave 7 lanes (complete)

Wave 7 launched from `3180581` and integrated seven new Lean files (one crypto
model module and six proof modules). The catalog stayed at 48 rows and 0
statement-only; six existing rows were strengthened from 73 to **79 resolved
targets**. Reports are under `agents/reports/swarm7/`.

| Lane | Issue(s) | Result | Owned files |
|---|---|---|---|
| `S7-L1-SEQUENCE` | `L1-02`, `L1-07` | Exact BIP 68/112 `checkSequenceDef` characterization, policy dependence, sequence/disable-bit facts, delayed branch refinement at `verifyImpl` and `RealChecker.realCheckerOf`, bad-signature failures at every evaluator layer | new `SequenceContextTargets.lean` |
| `S7-PR-PREIMAGE` | `PR-05`, `PR-02` | `preimageBytes_eq_encode_bytes` for every preimage, ten-field consensus order, vendored sub-hash equality, commitment-wire `bip143MsgL` byte equality, 179/412-byte vectors; HTLC instantiation/field hypotheses explicit | `SighashTargets.lean` §13, `Sighash.lean` |
| `S7-CH-CONSUMER` | `CH-01`, `CH-02` | Consumer migration API, canonical permutation, normal-form preservation, coverage equivalences, `legacyCoverage_not_preserved_by_net_migration`; `trimmedTotalSat` kept | `Commitment.lean`, new `CommitmentConsumerTargets.lean` |
| `S7-MODEL-FOLD` | `MODEL-02`, `MODEL-03` | Guarded fold/refinement (`GuardedStep`, `GuardedUpdateStep`, `danceStep_iff_guardedStep`) plus mechanized impossibility of the literal unguarded fold; all counterexamples retained | `State.lean`, new `ProtocolEventFoldTargets.lean` |
| `S7-RT-RAW` | `RT-01` | Raw `applyGossip` non-refinement, canonical-store wrapper with exact projection, sharp refinement square, extended reachable invariant, per-slot/global-clock boundary witness, raw-extension impossibility | `Gossip.lean`, new `GossipRawRefinementTargets.lean` |
| `S7-CONF-LIVE` | `CONF-02`, `CONF-01` | Pinned 188-package `Cargo.lock` + public-API live probe; `cargo test --offline --locked` passes; 26/26 BigSize, 3/3 TLV, 4/4 wire live rows; hash-pinned transcript and forged-transcript mutation | `tests/conformance/**`, `ConformanceDiffTargets.lean`, `check-conformance.py` |
| `S7-L1-FUNDING-AUTH` | `L1-03` | `OpenChannel` projection, separate funding phase machine, joint open/accept construction, finite-C1 output-determines-key-set, key provenance, transport scope counterexample; `Messages.openChannel` patch recorded | `Funding.lean`, `Handshake.lean`, new `FundingAuthTargets.lean` |
| `S7-PR-KEY` | `PR-01` | `SecretKey`/`KeyPair` deterministic model, scoped signing correctness, `Owns`/`Signer`, conditional attribution under `KeyBinding`, non-vacuous witness, `key_generation_not_key_attribution`, total-law tension | new `Crypto/KeyModel.lean`, new `KeyModelTargets.lean` |

Wave 7 closed `CH-01`, `RT-01`, `CONF-02`, `MODEL-02`, and `MODEL-03`. It
narrowed `L1-02`/`L1-07` to the `TxValidation.Full`/`txCheckerFor` transfer and
policy edges, `PR-05` to the `HtlcWire`/scriptCode instantiation, `L1-03` to
the `Messages.lean` type-32 `openChannel` integration, and `PR-01` to the
`AcceptChannel`/registration or proof-of-possession path. Two strong negative
results are retained: raw gossip insertion has no canonical refinement, and the
literal unguarded `ProtocolEvent` fold is impossible without falsifying the
wave-5/6 counterexamples.

## Wave 8 candidate lanes (historical)

These were the codeable next steps after the wave-7 checkpoint; all eight were
selected and completed in wave 8. The parent
selects a disjoint set; human-only release decisions (`OPS-02`, `OPS-03`, vendor
publication) and the probability/complexity foundation (`CR-01`/`SEC-01`) stay
outside an agent lane.

| Candidate | Issue(s) | Scope |
|---|---|---|
| `S8-L1-TXVALID` | `L1-02`, `L1-07` | Import `Bitcoin.TxValidation.Full`/`txCheckerFor`, complete the final delayed/revocation transfer, and model the `minimalData`/`csv ≥ 32768` policy edges |
| `S8-PR-HTLCPREIMAGE` | `PR-05` | Instantiate the byte-equality theorem for `HtlcWire`, synthesize the HTLC scriptCode, and document display-order txid conversion |
| `S8-L1-OPENCHANNEL-WIRE` | `L1-03` | Apply the exact `Messages.lean` type-32 `openChannel` patch (321-byte model length: 287 fixed + 34 shutdown script, `chain_hash`/TLV header omitted; channel id, pubkeys), add the root import, and connect the phase machine end-to-end |
| `S8-PR-ACCEPT-PAYLOAD` | `PR-01` | Add `acceptChannel?` to `HandshakeState`, set it on `recvAcceptChannel`, and either model registration/proof-of-possession or strengthen the conditional attribution contract |
| `S8-CH-CONSUMER-SITES` | `CH-01` | Apply the migrated consumer path at the actual downstream construction sites and compile the proposed `SighashTargets` `viewOfState` adapter |
| `S8-L1-EC-BRIDGE` | `L1-01`, `L1-07` | Investigate a concrete ECDSA verifier bridge for `Bitcoin.Crypto.Ecdsa.Verify.verifyImpl`; keep the abstract-verifier boundary if no faithful implementation is available |
| `S8-CONF-ENCODINGS` | `CONF-01` | Add more BOLT encodings and, if the environment permits, a node-level or wider live differential path; keep the finite/public-API caveat |
| `S8-MODEL-STORE-EPOCH` | `RT-01` | Model gossip-store epochs/replacements explicitly and refine the canonical wrapper against the raw store over a realistic update sequence |

## Wave 8 lanes (complete)

Wave 8 launched from `50d78ed` and is integrated as `9bafdab`. Eight disjoint
lanes delivered the transfer, wire, registration, EC-bridge, conformance, and
store-epoch work; the parent added the root imports, strengthened seven catalog
rows from 79 to **100 targets**, and extended the axiom audit to 215 theorems.

| Lane | Issue(s) | Result | Owned files |
|---|---|---|---|
| `S8-L1-TXVALID` | `L1-02`, `L1-07` | Exact known-amount `txCheckerFor`/`realCheckerOf` transfer; delayed/revocation branch transfer; missing amount fail-closed; `minimalData` and `csv ≥ 32768` boundaries, including the `csv = 32768` collapse | new `TxValidTransferTargets.lean` |
| `S8-PR-HTLCPREIMAGE` | `PR-05`, `PR-02` | Exact `HtlcWire` BIP 143 byte equality, `ofTx`/`toPreimage` bridge, 143/136-byte scriptCodes, 300/293-byte preimages, display-order txid conversion | new `HtlcPreimageTargets.lean` |
| `S8-L1-OPENCHANNEL-WIRE` | `L1-03` | Type-32 `Msg.openChannel`, six-key/type/length/identity laws, projection to `Handshake.OpenChannel`, funding construction, end-to-end `FundingPhase` reachability | `Messages.lean`, new `OpenChannelWireTargets.lean` |
| `S8-PR-ACCEPT-PAYLOAD` | `PR-01` | `HandshakeState.acceptChannel?`, `handshakeStepRecvAccept`, provenance/stability, `StoredAccept`, conditional attribution, negative proof-of-possession | `Handshake.lean`, new `AcceptPayloadTargets.lean` |
| `S8-CH-CONSUMER-SITES` | `CH-01` | Proof-layer `SignedState.toCommitmentTx`, legacy-boundary equality/Perm, coverage bridge, concrete sites; no production `CommitmentTx` consumer | `CommitmentConsumerTargets.lean`, new `CommitmentConsumerSitesTargets.lean` |
| `S8-L1-EC-BRIDGE` | `L1-01`, `L1-07` | Sharp conditional `VendorEcdsaBridge`; exact argument-order bridge; funding/commitment/close agreement; EUF-CMA/key-binding transfer; message-reduction and key-parsing boundaries | new `EcdsaBridgeTargets.lean` |
| `S8-CONF-ENCODINGS` | `CONF-01` | Six BOLT 2 message vectors, 29 `decide` theorems, 13/13 mutation controls; live message row deferred | `ConformanceDiffTargets.lean`, `scripts/check-conformance.py`, `tests/conformance/**` |
| `S8-MODEL-STORE-EPOCH` | `RT-01`, `RT-02` | Typed replacement history, `StoreEpoch`/`epochStep`/`epochFold`, sequence-level canonical square, two divergence witnesses; replacement removals in `Gossip.lean`; node-announcement canonicalisation remains open | `Gossip.lean`, new `GossipStoreEpochTargets.lean` |

Wave 8 closes the `TxValidation.Full` transfer for a known spent amount, the
`Msg.openChannel` wire gap, the HTLC second-stage preimage gap, and the
proof-layer consumer adapter. It narrows `L1-01`/`L1-07` to the explicit
`VendorEcdsaBridge` and known-amount boundaries, `PR-01` to the conditional
`KeyBinding`/proof-of-possession boundary, `PR-02` to arbitrary-preimage and
wire-only coverage, `RT-02` to node-announcement canonicalisation, and
`CONF-01` to the deferred live message row. No unconditional consensus or
computational-security claim is added.

## Wave 9 candidates

| Candidate | Issue(s) | Scope |
|---|---|---|
| `S9-L1-EC-UNCONDITIONAL` | `L1-01`, `L1-07` | Decide whether a concrete EC verifier implementation/EUF-CMA instance can replace `VendorEcdsaBridge` without weakening the model; keep the amount/context boundary |
| `S9-L1-OPENCHANNEL-ROUTING` | `L1-03` | Connect the type-32 wire record to transport attribution/`HandshakeState` routing and the peer frame path |
| `S9-PR-ATTRIBUTION` | `PR-01` | Model a registration/proof-of-possession game or prove the strongest available attribution contract; do not treat storage as possession |
| `S9-PR-ARBITRARY-PREIMAGE` | `PR-02` | Characterize wire-only coverage and the eight arbitrary-preimage field hypotheses; keep the conditional view-binding boundary |
| `S9-RT-NODE-CANON` | `RT-02` | Canonicalise node announcements and close the remaining store-epoch design gap |
| `S9-CONF-LIVE-MSG` | `CONF-01` | Add a live BOLT 2 message row to the pinned differential harness |

Human-only release decisions (`OPS-02`, `OPS-03`), the probability/complexity
foundation (`CR-01`/`SEC-01`), and any `main` merge remain outside agent lanes.

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
| `lake build` | 250 jobs, RC 0 |
| `check-catalog.py --audit` | 48 proved / 0 statement-only / 100 targets / 0 unresolved / 0 proved failures / 8181 declarations |
| `check-catalog.py --allow-planned` | 48/0/0 planned, RC 0 |
| `check.sh` | `files=211 obligations=82 sorry_in_proofs=0`, RC 0 |
| `check-final.py` | 211 Lean files, 209 root imports, RC 0 |
| `check-conformance.py` | 61 base + 16 framing + 9 boundaries, 33 differential fixtures, 175 Lean references, 13/13 mutation controls, 6 BOLT 2 message vectors, 3 declared gaps, live 26 BigSize + 3 TLV + 4 wire, RC 0 |
| `verify-anchors.py` | 306 anchors, 0 bad, 2 unanchored rows, RC 0 |
| `verify-vendor.sh` | 149 files, RC 0 |
| Axiom audit | 215 audited theorems; only `propext`, `Quot.sound`, `Classical.choice` |
