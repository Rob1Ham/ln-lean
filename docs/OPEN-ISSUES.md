# Open Issues and Swarm Roadmap

**Status:** living roadmap after the proof-wave 12 integration; four wave-12
lanes are complete on `repair/integrated`.
**Branch:** `repair/integrated`.
**Gate commit:** `d9c0d2f` (`[WAVE12]` status); code integration is `d210079`.
Published tips include `9940642`, `90ef1f1`, `5ddab4c`, `d210079`, and
`d9c0d2f`. Hosted CI runs `39288684058`, `39290061147`, `39290644672`,
`39303105137`, and `39303680973` are green.
**Base commit:** `9359475` (wave-9 integration; wave 10 launched from
`9158592`; wave 11 from `4037264`; wave 12 from `5ddab4c`). Wave 8 launch was
`50d78ed`; proof-wave 7 code is `b48d041`; wave 7 launch is `3180581`;
proof-wave 6 code is `0a3a5fb` (proof-wave 5 code is `6389baa`; proof-wave 4
code at `26ced90`).
**Catalog gate:** 51/51 rows `proved`, 0 `statement-only`, 0 unresolved,
294 targets.
**Full build:** 314 jobs, RC 0, 275 Lean files, 273 root imports, 435 audited
theorems.
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
| **P1** | Major model/verification gap; codeable in a wave | `L1-03`, `PR-01`, `PR-02`, `RT-02` |
| **P2** | Longer-term research / conformance / network assumptions | `CR-01`, `L1-06`, `NET-01`, `CONF-01`, `MODEL-01`, `SEC-01` |

## Open issues

| Id | Priority | Status | Issue | Evidence / current boundary | Next action |
|---|---|---|---|---|---|
| `OPS-01` | P0 | closed (hosted CI verified) | Public CI cannot run the full build from a clean checkout | `repair/pubbump` replaced the private `f950806` snapshot with a 149-file copy of public `btc-lean` `spec/core` at `4f5c4f8`; `vendor/VENDOR-SHA256` is regenerated. `scripts/fetch-vendor.sh` now pins `4f5c4f8`, and `--from-git` fetches exactly that commit and verifies the 149-file manifest. CI uses an explicitly configured checksummed archive when present, and otherwise runs `--from-git`; the full build is no longer a skip gate. Local `--from-git --dry-run`, the full 250-job build, and all gates pass. Hosted CI run `39175507618` on `60318ad` and run `39177572471` on `e3e0aa8` completed both the source-level gates and the `Build gate (pinned vendor snapshot required)` job, including `lake build`; the intermediate `68f283c` run was superseded and cancelled. | No further action for the public path; keep `VENDOR_ARTIFACT_URL`/`VENDOR_ARTIFACT_SHA256` optional for offline runners. |
| `OPS-02` | P0 | blocked (human legal decision) | No `LICENSE` | No license file in the tree; `docs/LICENSE-DECISION.md` provides a neutral MIT/Apache-2.0/dual matrix and third-party notice inventory. The vendor copy now comes from the public MIT `btc-lean` repository at `4f5c4f8`, but the repository still needs an explicit project license and notices. | Maintainer chooses the license and copyright holder, then adds `LICENSE`/`NOTICE`; do not let an agent invent one Wave 12 audit confirms there is still no `LICENSE`/`NOTICE` and no agent authority to choose the grant or copyright holder. |
| `OPS-03` | P0 | blocked (human release decision) | No release tag and `main` is behind | `origin/main` is old; `repair/integrated` is the active branch; no tag; `docs/RELEASE-CHECKLIST.md` records the pre-tag gates and human choices | Decide PR/merge path to `main`, cut a signed/annotated tag, and publish release notes Wave 12 audit confirms there is still no release tag; the PR/merge path, tag object, and release notes remain maintainer decisions. |
| `OPS-04` | P2 | closed (public copy) | Vendor snapshot contained an absolute symlink | The `repair/pubbump` public-core copy removes the dangling `btc-lean-core` self-symlink; `vendor/btc-lean-core` is now a real directory, and `VENDOR-SHA256` covers all 149 regular files. | No further action; keep the checksum manifest authoritative. |
| `L1-01` | P0 | blocked (mechanized impossibility at untyped ByteArray interface; typed-digest/secp256k1 external) | P2WSH / `OP_CHECKMULTISIG` spendability is not bridged to the vendored interpreter | `SpendTargets.lean` defines the explicit stack model; `InterpreterBridgeTargets` imports the vendored `Bitcoin.Interpreter.Defs` evaluator, proves the model serializer equal to the vendor `serializeOpcodes`, parses the wire list back exactly, and proves `funding_interpreters_agree` for the positive 2-of-2 funding witness. `SighashBridgeTargets` builds the BIP 143 witness-v0 digest and a `LocktimeEnv` to the vendor `ecdsaEntry`. This is not unconditional consensus spendability: ECDSA remains an abstract verifier, spent amount/outpoint and transaction-validity context are explicit inputs, and the scope is positive-direction P2WSH. Wave 8 `EcdsaBridgeTargets` supplies the exact conditional `VendorEcdsaBridge` transfer (`fundingSignedValid_iff_vendor`), the argument-order/DER/hashtype seam, and the funding/commitment/close interpreter agreements; the bridge is still an explicit hypothesis, not an unconditional verifier theorem. Wave 9 `EcdsaConcreteTargets` proves the exact dichotomy: `eufCma_vendorVerify_iff_totalReject`, `bridged_model_totalReject`, and `exists_bridged_model_iff_totalReject` show that a concrete `verifyImpl` instance satisfies the pointwise bridge only as the total-rejecting verifier; `withVendorEcdsa_no_funding` identifies the wave-8 concrete model as that vacuous instance. The faithful concrete contract is `ResidueBinding` + `KeyBinding`, and `not_digestBindsMod_fundingTag` shows byte-level transaction binding needs a canonical `DigestBindsMod` domain. Wave 10 `EcdsaDomainTargets` proves `not_digestBindsMod_any_tag` and `no_digestBindsMod_anywhere`: no fixed tag repairs the untyped interface, even at fixed 33-byte length; `digestBindsModOn_canonical33`/`_canonical32` isolate the canonical value-`< n` domain as the exact algebraic repair. | Keep the constructed sighash/context path and positive-direction scope; no unconditional verifier theorem is available at the `ByteArray` interface. A production repair must restrict the message encoding to the canonical domain or use a typed digest with an explicit computational hypothesis; EUF-CMA, `KeyBinding`, and the spent-amount/transaction-validity context remain explicit. Wave 12 audit confirms `no_bridged_nontrivial_model` blocks a non-vacuous bridge at the current interface; the 33-byte canonical instance is abstract and does not cover real funding transaction bytes, so a typed-digest or concrete secp256k1 repair is external. |
| `L1-02` | P0 | blocked (concrete secp256k1 + spent amount/context external; no TxValidation.Full transfer gap) | `to_local` CSV/revocation execution has a known-amount/concrete-EC boundary | `InterpreterBridgeTargets` executes the delayed branch; `InterpreterRevocationTargets` executes the revocation branch with branch-selection and negative cases. `SequenceContextTargets` proves `decodeNum_delayBytes`, non-negativity/disable-bit facts, exact `checkSequenceDef_delay_iff` (version ≥ 2, height domain, `csv ≤ masked sequence`), `toLocal_delayed_sequence_context_refinement`, and `toLocal_delayed_checkerOf_refinement` at `Bitcoin.Crypto.Ecdsa.Verify.verifyImpl`; `checkerOf_eq_realCheckerOf` transfers to `RealChecker.realCheckerOf` for `nIn < tx.vin.length`, with bad-signature failures mechanized at every evaluator layer. Wave 8 `TxValidTransferTargets` proves `txCheckerFor tx nIn (some amount) = realCheckerOf tx nIn amount`, transfers the delayed/revocation branches, mechanizes the missing-amount case as fail-closed, and proves the `minimalData` and `csv ≥ 32768` decode/verdict edges (including the `csv = 32768` collapse to `0`). The remaining boundary is the known spent amount and the concrete EC verifier, not a `TxValidation.Full` transfer gap. Wave 10 `EcdsaDomainTargets` proves the same tag-independent digest-domain obstruction and the canonical-domain repair for the `to_local` EC seam. | Keep the known-amount and concrete-EC boundaries explicit; no `TxValidation.Full` transfer gap remains. Wave 12 audit confirms the full-pipeline transfer is complete for a known amount; only a concrete secp256k1 verifier and the actual amount/validity context remain. |
| `L1-03` | P1 | blocked (real Noise/AEAD + key ownership external; model-level flag/equality only) | `FundingScriptHashLinked` is a construction invariant | `FundingNegotiation.toFundingParams` computes `witnessScriptHash := H(witnessScript.bytes)` from ordered funding keys, and `FundingLinkTargets` proves the ordered P2WSH output. Wave 7 adds `OpenChannel`, its `toFundingNegotiation`/`toFundingParams` projection, a separate `FundingPhase`/`FundingPhaseEvent`/`fundingStep`/`FundingReachable` machine, and `FundingAuthTargets`: joint open/accept construction, finite-C1 output-determines-key-set, key provenance, phase-link theorems, and the `same_message_distinct_senders` scope counterexample. Wave 8 adds `Msg.openChannel`/`MsgKind.openChannel`, `OpenChannelWire` with six-key/type/length/identity laws, projection to `Handshake.OpenChannel`, funding construction, and end-to-end `FundingPhase` reachability. Wave 9 `OpenChannelRoutingTargets` adds the transport `OpenChannelEnvelope`, `EnvelopeAttributed` as transport-key equality, an additive `OpenRouteState`/`recvOpen` layer, the concrete `open_channel` → `accept_channel` → `funding_created` route (`openRoute_initial_to_fundingCreated`), wire-to-funding construction, and the non-attribution/no-signature boundaries (`wire_payload_does_not_determine_sender`, `unattributed_open_is_routed`, `wire_carries_no_signature`). `wire_binding_needs_FundingScript_C1` records the finite-C1 scope. Wave 10 `TransportAuthTargets` separates an authenticated session (`TransportAuthenticated`) from the explicit `SessionKeyBinding`, composes attributed delivery with the routed `funding_created` witness, and proves `transport_auth_not_from_wire`, `unattributed_delivery_exists`, and `no_wire_sender_function`.  Wave 11 `NoiseTransportTargets` adds a Noise_XK-shaped handshake/session model, nonce freshness, accepted-frame peer binding, and a concrete attributed delivery; the explicit `SessionKeyBinding`, C3/key ownership, and finite C1 funding admission remain hypotheses, and no real AEAD/Noise implementation is claimed. | No core wire/handshake patch remains; keep the finite C1 admission, explicit `SessionKeyBinding`, transport authentication/C3, and key ownership visible. The routed model does not authenticate the sender from the payload alone, and no Noise/MAC implementation is claimed.  Keep the explicit `SessionKeyBinding`/C3/key-ownership boundary; no payload-only sender attribution and no computational transport security claim. Wave 12 audit confirms `TransportAuthenticated` is a session flag and `SessionKeyBinding` is the explicit equality `peerKey = fundingPubKey`; a real Noise_XK/AEAD implementation, C3, and key ownership remain external. |
| `L1-04` | P1 | closed (fee-basis interpretation) | Anchor weight has an 8 WU spec/serialization gap | Wave H H33 proves the witness-inclusive commitment weight is `1116 + 172*k`, that `1124 + 172*k` is the fee basis, and that the extra 8 WU is the Appendix A `count_tx_out` field, not missing witness bytes; the literal `1124` weight claim is retained as a counterexample. | No further model action; keep the literal/fee-basis distinction explicit in downstream fee consumers. |
| `L1-05` | P1 | closed (counterexample + domain-separated construction) | C1 is 32-byte payment-preimage collision resistance, not 71-byte script injectivity | Wave H H34 proves unconditional counterexamples: a C1-satisfying primitive model collides on 71-byte funding scripts, and no primitive model binds all 71-byte scripts. It then proves a domain-separated `scriptCommitment` binds the revealed witness script under the retained finite `CollisionFreeOn` pair admission. | No global SHA-256 injectivity claim; keep the finite pair admission for the domain-separated commitment. |
| `L1-06` | P2 | open (finite graph finality proved; PoW/probabilistic chain absent) | Reorg result is conditional on common tip and bounded depth | `LN-L1-003` keeps `SameChain`, common-prefix arithmetic, and `OutOfReachOf` explicit; deep reorgs have a separate failure mode  Wave 11 `ChainFinalityTargets` adds a finite block/chain graph, a bounded-depth finality theorem, a unique-tip family form, a sharp deep-reorg counterexample, and bridges to `ReorgTargets`/`OutOfReachOf`; it does not model PoW, probability, or a live chain. | Connect the hypotheses to the L1 chain model or leave the conditional theorem as the deliverable  Keep the finite-graph conditional result; a probabilistic/PoW chain model or an explicit external finality assumption remains. |
| `L1-07` | P0 | blocked (mechanized EC impossibility; positive-direction known-amount scope) | Vendored real interpreter is imported for the positive L1 branches | `InterpreterBridgeTargets` proves funding 2-of-2 and delayed agreement; `InterpreterRevocationTargets` proves the revocation branch; `SighashBridgeTargets` constructs the digest/`LocktimeEnv`. Wave 7's `SequenceContextTargets` proves the exact BIP 68/112 sequence context and transfers the delayed checker to `Bitcoin.Crypto.Ecdsa.Verify.verifyImpl` and `RealChecker.realCheckerOf` for `nIn < tx.vin.length`. Wave 8 transfers the delayed/revocation branches to `txCheckerFor (some amount)` and closes the `TxValidation.Full` transfer for a known amount; sequence range/policy edges are mechanized. Wave 9 `EcdsaConcreteTargets` proves the concrete bridge dichotomy: `eufCma_vendorVerify_iff_totalReject`, `no_bridged_nontrivial_model`, and `exists_bridged_model_iff_totalReject`, so a non-vacuous concrete instance is impossible at the current untyped `ByteArray` interface; `fundingTag_digest_collision_witness` and `not_digestBindsMod_fundingTag` record the missing canonical-domain condition. The bridge remains positive-direction with an explicit amount/EC boundary, and unconditional `ConsensusSpendBridge` is still open. Wave 10 `EcdsaDomainTargets` proves no fixed tag repairs the untyped digest interface and identifies the canonical value-`< n` domain as the exact algebraic repair. | No `TxValidation.Full` transfer gap remains for a known spent amount; keep the positive-direction, known-amount, and EC-interface boundaries explicit. Do not claim a concrete non-vacuous verifier at this interface. Wave 12 audit confirms the same zero-padding/C3 obstruction and the positive-direction/known-amount boundary; no unconditional `ConsensusSpendBridge` follows at the current interface. |
| `L1-08` | P0 | closed (constructed under explicit context) | BIP 143 sighash and locktime/sequence context were assumptions in the L1 bridge | `LnLean/Bitcoin/Sighash.lean` defines the ten-field BIP 143 witness-v0 preimage, serializers, sub-hashes, `ofTx`, `digest`, and guarded `sighashWitnessV0`; it proves byte-equality to the vendored `signatureHashBip143Impl`/`signatureHashBip143` and mechanizes ANYONECANPAY/zero-sub-hash omissions. `SighashBridgeTargets` constructs `LocktimeEnv` from transaction fields and proves `checker_consumes_model_digest`, instantiating the funding and delayed `to_local` agreements. Boundaries: abstract EC verifier, explicit spent amount/outpoint and transaction-validity context, positive P2WSH direction, pinned flags. | No further action for the digest construction; keep the explicit context and positive-direction scope. |
| `CR-01` | P2 | open (limits interface added) | No computational cryptographic reductions | C1/C3/C8 are exact algebraic laws; `docs/CRYPTO-LIMITS.md` and `SecurityGameTargets.lean` now state the missing probability/complexity model, query bounds, and the exact reduction interface. `AdvantageReduction.bound` is arithmetic conditional on an assumed tightness field; no reduction is proved. | Choose a probability/complexity foundation and real games for C1/C3/C8; do not claim computational security from the algebraic model. |
| `PR-01` | P1 | blocked (real EUF-CMA/PoP extraction + key ownership external; toy non-vacuity only) | `FundingSigningLaw` / `KeyBinding` are hypotheses | `SighashTargets` adds the honest signing constructor and joint funding/commitment contract. Wave 7 adds `Crypto/KeyModel.lean`: `SecretKey`, `KeyPair`, deterministic `KeyModel`, domain-scoped `correctOn`, `Owns`, and `Signer`. `KeyModelTargets` proves `funding_signature_attribution` under the unchanged `KeyBinding`, `AdvertisesKey`/negotiation key equality, funding-signature validity, a non-vacuous pinned witness, and `key_generation_not_key_attribution` (generation + secret-key signing + `EufCma` do not imply attribution). Wave 8 adds `HandshakeState.acceptChannel?`, `handshakeStepRecvAccept`, provenance/stability lemmas, and `StoredAccept`; `stored_accept_payload_attribution` remains conditional on `KeyBinding`, and `acceptPayload_not_proof_of_possession` mechanizes the registration boundary. The total `FundingSigningLaw` is still flagged as totality-tensioned. Wave 9 `AttributionGameTargets` adds a registration/PoP game over `StoredAccept`: `register_of_storedRegistration`, `stored_registration_funding_attribution`, `stored_pop_attribution`, `stored_pop_attribution_contract`, `stored_payload_not_possession`, `stored_attribution_fails_without_keyBinding`, and `attribution_game_summary`. `PopSound` and `PopProducedBy` are explicit extraction/provenance laws; storage and acceptance are not possession. Wave 10 `PopProtocolTargets` models a concrete verifier-issued `(channelId, nonce)` challenge, proves the fixed-width encoding injective, gives honest completeness against the advertised funding key, derives `PopSound`/`PopProducedBy` from `PopKeySoundOn`/`PopExtractionOn`, and mechanizes unbound-challenge, nonce-free, no-`Valid`, and reused-challenge replay. | No payload patch remains; keep the conditional `KeyBinding`/C1 attribution contract, the explicit `PopKeySoundOn`/`PopExtractionOn` hypotheses, `EufCma` plus freshness, and the replay counterexamples visible. No real signature scheme or computational EUF-CMA claim is made. Wave 12 audit confirms `PopKeySoundOn`, `PopExtractionOn`, and `KeyBinding` are explicit hypotheses; `selfSigModel` is a toy witness, so a real EUF-CMA signature scheme with key ownership and freshness remains external. |
| `PR-02` | P1 | blocked (production coverage source/protocol change external; model-level source/consumer closed) | `CommitmentSigned` wire record lacks data for wire-only coverage | `SighashTargets` adds a BOLT 3-shaped structural commitment/HTLC serializer, `SighashProduces`, and `SighashProduces.coverage`, deriving the digest, commitment signature, and per-HTLC signatures under C3. Wave 6 adds exact BOLT 3 transaction wire layouts and parser round-trips; wave 7 proves the commitment-wire `Bip143Preimage` byte-equal to the vendored `bip143MsgL`/`encode`, with 179-byte and 412-byte vectors. `SighashViewBindingTargets` conditionally lifts digest binding to view binding. Wave 8 closes the HTLC-wire instantiation (`HtlcPreimageTargets`), so commitment and HTLC second-stage preimages are both byte-equal to the vendored encoder; arbitrary non-transaction-derived preimages still need the eight field-agreement hypotheses, and wire-only coverage remains conditional. Wave 9 `PreimageCoverageTargets` makes the eight hypotheses exact (`fieldAgreement_iff_eq_ofTx_and_amount`, `FieldAgreement.bytes_eq`, `FieldAgreement.digest_eq_vendor`, `wireSignatureCovers_of_preimage`), retains dropped-locktime/amount counterexamples, proves `legacy_projection_not_determine_htlc_coverage`, and records the display-order, 20-byte hash-image, and gross-amount boundaries.  Wave 11 `CoverageSourceTargets` models full-record, out-of-band, and protocol-extension sources; proves full-record exactness, legacy-wire insufficiency, source separation, and conditional extension-plus-wire determination. It does not change the protocol or claim a production decoder. | HTLC-wire bytes are exact; the arbitrary-preimage hypotheses are now explicit and complete. Wave 10 `CoverageWitnessTargets` supplies a constructive per-HTLC witness decoder (`decodeCoverage_canonical`, `decodeCoverage_covers`), proves no legacy-only decoder or wire-compatible selector is correct for all full records, and shows the amount row is necessary. The legacy wire projection still has no coverage decoder; production coverage needs an out-of-band/full-record source or a protocol change. Keep both boundaries visible.  Keep the explicit source/binding law; production coverage still needs an out-of-band/full-record source or a protocol change. Wave 12 adds `CoverageConsumerTargets`: a full-record source yields an exact consumer, no wire-determined consumer exists, and an extension determines one only under the explicit `ExtensionConsumerLaw`; concrete witnesses exercise all three sources. Production coverage still needs an out-of-band/full-record source or a protocol change. |
| `PR-05` | P1 | closed (commitment + HTLC second-stage bytes; explicit caveats) | BOLT 3 sighash preimage byte-equality across modelled wire paths | `SighashTargets` §13 proves `preimageBytes_eq_encode_bytes` for every `Bip143Preimage`, `preimageBytes_fields` for the ten-field consensus order, and `commitmentBip143Preimage_eq_bip143MsgL` on `CommitmentWire.toTx`; the vendored sub-hashes match `hashPrevouts`/`hashSequence`/`hashOutputs`, with 179-byte and 412-byte vectors. Arbitrary non-transaction-derived preimages reach the vendor encoder only under eight explicit field-agreement hypotheses (`ofTx` discharges them); Wave 8 `HtlcPreimageTargets` proves the same byte equality for every `HtlcWire`, synthesizes 143/136-byte HTLC-success/timeout scriptCodes, and proves 300/293-byte preimage sizes; display-order txid conversion, explicit 20-byte hash images, and the amount context remain documented. | No further wire-byte work; keep the explicit 20-byte hash-image/amount and display-order boundaries documented. |
| `PR-06` | P1 | closed (conditional view binding) | C3 binds signatures to digests, not directly to commitment/HTLC views | `SighashViewBindingTargets` proves `commitmentSignature_binds_view`, `commitmentSignature_binds_viewOfState`, `signature_binds_commitment_view_fields`, and `htlcSignature_binds_htlcView` under explicit `ViewDigestCollisionFree`/`HtlcDigestCollisionFree`/`SerializationBindsViews` hypotheses. `digest_binding_not_view_binding` mechanizes the counterexample showing C1+C3 alone are insufficient; `viewOfState_not_injective_in_state` and `htlcView_ignores_msat_fraction` record the scope boundaries. | Keep the explicit hypotheses and non-vacuity witnesses; no unconditional view binding is claimed. |
| `CH-01` | P1 | closed (proof-layer adapter; coverage caveat) | Rich `CommitmentTx` model is not the legacy consumer path | `S7-CH-CONSUMER` adds `CommitmentTx.consumerOutputs`, `migrateForConsumer`, `migratedConsumerOutputs`, `netConsumerOutputs`, `ofCommitment`, and `CommitmentPair.migrateNet`. `CommitmentConsumerTargets` proves the canonical permutation, normal-form preservation (`Migrated` + `UsesRecordNet`), and coverage-consumer equivalences. `legacyCoverage_not_preserved_by_net_migration` mechanizes the necessary no-trim/normal-form premise; Wave 8 adds the proof-layer `SignedState.toCommitmentTx` adapter, legacy-boundary equality/Perm theorems, a coverage bridge, and concrete site examples; there is still no production `CommitmentTx` consumer. D12 remains the unconditional ordering refutation. | No further migration work for the proof-layer adapter; keep the counterexample and normal-form hypotheses explicit, and do not claim a production consumer. |
| `CH-02` | P1 | closed (record layer integrated) | Second-stage fee and dust trimming were not integrated end-to-end | `CommitmentGrossNetTargets` adds the net output path, `trimmedValue`, `effectiveFeeSat`, and proves emitted + base fee + trimmed = funding and effective fee = base fee + trimmed. Wave 6 places `CommitmentHTLCOutput.netAmountSat` and stored `Commitment.trimmedTotalSat`; `CommitmentTypesTargets` proves the field-boundary dust, migration, conservation, effective-fee, and canonical refinement. The full tree build includes the five-field `LawfulBEq` update. | Keep the net path and record-layer theorems; legacy-consumer migration is tracked as `CH-01`. |
| `CH-03` | P1 | closed (record layer integrated) | Rich commitment outputs lacked BOLT-3 gross/net fields | `CommitmentTx` has `netAmountSat`/`trimmedSat`, and `CommitmentHTLCOutput.netAmountSat` plus stored `Commitment.trimmedTotalSat` are now in `Types.lean`; `CommitmentTypesTargets` proves the field-boundary dust test, migration, conservation, effective-fee accounting, and canonical refinement. The stored field is named `trimmedTotalSat` because the wave-5 computed function already uses `trimmedSat`; this is a naming choice, not a missing field. | No further field work; decide whether to rename `trimmedTotalSat` in a coordinated API change. |
| `CH-04` | P1 | closed (five-field patch applied) | Gross/net record fields were not fully integrated | `S6-CH-TYPES` applied the five-field patch and the parent updated the private `LawfulBEq CommitmentHTLCOutput` instance in `Conservation.lean`; the full 218-job build and strict catalog are green. Construction sites compile with the new field/default. | No further action; keep the `trimmedTotalSat` naming decision under `CH-03`. |
| `HT-01` | P1 | closed (tagged namespace) | Untagged global HTLC id uniqueness is false under BOLT 2 per-sender counters | `LN-HT-004` keeps per-sender `dir_id_unique`, the `CrossDisjoint` untagged form, and now the direction-tagged `HTLCTag` namespace with `tagged_id_unique_of_reachable`/`tagged_ids_nodup_of_reachable`. `cross_direction_duplicate_tagged` connects the old counterexample. The wire remains per-sender by BOLT 2 design. | No further model action; keep the tag documented as a model-side namespace, not a new wire encoding. |
| `RT-01` | P1 | closed (canonical wrapper; raw non-refinement proved) | Gossip key attribution and raw insertion are separate | `admitGossipAttributed`/`admitGossipDirected` gate updates on validity plus announced-key attribution; wave 6 derives `NodeKeyConsistent`/`CanonicalAnnouncements` on canonical reachable states. Wave 7 proves raw `applyGossip` is **not** a function refinement of canonical admission, supplies `applyGossipCanonicalStore` whose gossip/registration projection is exactly `admitGossipCanonical`, proves the sharp refinement square on canonical-shaped stores under admission gates and the raw global clock, and establishes the extended reachable-store invariant. A reachable boundary witness shows the canonical per-slot gate accepts an update the raw global clock rejects, and an impossibility theorem rules out canonical-preserving raw announcement extensions. Wave 8 adds the `StoreEpoch` replacement-history layer, `epochFold_gossip_eq_canonicalStoreView_rawFold`, and `StoreEpoch.epochFold_store_eq_foldl`, with two divergence witnesses showing both admission hypotheses are necessary. | No further action for the raw/canonical square; use the canonical wrapper and the epoch API as the supported path, and keep raw insertion documented as non-canonical. |
| `RT-02` | P1 | blocked (address parsing modelled; chain policy/production pipeline external) | Gossip node-announcement canonicalisation remains a design gap | `GossipCanonicalTargets` defines `admitGossipCanonical`, `ReachableCanonical`, and `CanonicalAdmitted`; closure/preservation proofs derive both invariants, with update supersession, node-key rotation, concrete non-vacuity, and conflict witnesses. The rotation boundary and raw-store caveat are explicit. Wave 8 adds the update/announcement epoch history and canonical square, but node-announcement canonicalisation remains open by design. Wave 9 `NodeCanonicalTargets` adds an additive node layer: `insertNodeCanonical`, BOLT 7 strict-timestamp `NodeSupersedes`, `CanonicalNodeAnnouncements`, a node-canonical view, `applyGossipNodeCanonical`, `ReachableNodeCanonical`, and `NodeCanonicalAdmitted`. It proves reachable replacement and rotation witnesses, the equal-timestamp unrecoverable boundary, `no_canonical_node_preserving_raw_node_extension`, the per-slot/global-clock separation, and lifts the wave-8 epoch square to the node-canonical view. Wave 10 `NodeIdentityTargets` proves no antisymmetric store-only relation links two canonically distinct wire keys (`canonical_distinct_nodes_no_oriented_store_link`, `no_store_function_selects_both_rotation_worlds`); an explicit `RotationWitness` preserves wire membership (`rotation_preserves_wireMember`) but not signatures (`rotation_not_signature_preserving`); `WireMember` requires both channel wire keys to have node announcements, and `missing_endpoint_channel_admitted` shows the core transition does not enforce it.  Wave 11 `NodeIdentityChainTargets` adds signed rotation certificates, transitive chains, explicit re-signing with wire membership, old-signature counterexamples, and per-node timestamp/sequence replay limits. Address parsing and a production rotation/announcement pipeline remain outside the model. | Keep the canonical update/announcement/node path and rotation witnesses green. Remaining: identity across a `nodeId` rotation (the witness is opaque, not cryptographic), chain existence, address parsing, rate limits, and re-signing of rotated channel announcements.  Keep the signed-chain/re-signing/rate layer; address parsing, chain-existence policy, and a production gossip pipeline remain future work. Wave 12 adds `NodeAddressTargets`: the real BOLT 7 `u16 addrlen` blob, typed IPv4/IPv6/Tor v2/Tor v3/ASCII-DNS descriptors with exact 6/18/12/37-byte layouts, nonzero ports, ascending type order, at most one type 5, canonical-list round-trip/injectivity, and explicit rejection of truncated, unsorted, two-DNS, and malformed inputs. Chain-existence policy, cryptographic rotation identity, and a production gossip pipeline remain external. |
| `NET-01` | P2 | open | Network/liveness results depend on scheduling/fairness assumptions | `LN-SEC-003` keeps four `Assumptions P`; `LN-SEC-005` uses `FeeScheduleBounded`; `LN-SEC-006` requires a watchtower report | State the adversarial schedule/fairness model explicitly and prove one concrete eventual-delivery instance |
| `CONF-01` | P2 | open (five live message rows; additional encodings remain) | No shared conformance suite against BOLT vectors | `tests/conformance/vectors.json` + `scripts/check-conformance.py` cover 61 BigSize/TLV vectors, 16 framing cases, 9 decoder-boundary cases, and 9 mutation controls; `ConformanceTargets.lean`/`ConformanceDiffTargets.lean` add 151 `decide` theorems. The checker is wired into CI. Wave 8 adds six BOLT 2 payload/field vectors, 29 `decide` theorems, and 13/13 mutation controls; the live message row remained deferred. Wave 9 `S9-CONF-LIVE-MSG` adds the live BOLT 2 `channel_ready` (type 36) payload encoded through the pinned rust-lightning `Writeable` implementation under `cargo --offline --locked`, with five Lean targets (`diff_msg_channel_ready_payload`, `_length`, `_transport`, `_header`, `_frame_prefix`), 180 Lean references, 14/14 mutation controls, and a hash-pinned transcript. Wave 10 `S10-CONF-LIVE-MSGS` adds the live `open_channel` (type 32) base case through the public `OpenChannel`/`CommonOpenChannelFields` encoder, with five more Lean targets, 185 Lean references, 16/16 mutation controls, and transcript hash `9c6b664d7ac4…`. This remains finite/public-API conformance, not node-level interop; two TLV value-minimality/unknown-type cases are declared model gaps.  Wave 11 adds a live `accept_channel` (type 33) payload through the pinned public rust-lightning `Writeable` encoder, five Lean targets, two mutation controls, 190 Lean references, 18/18 controls, and three live BOLT 2 payloads (`channel_ready`, `open_channel`, `accept_channel`). Wave 12 adds live `funding_created` (type 34) and `funding_signed` (type 35) payloads through the same public `Writeable` API, ten Lean targets, four mutation controls, 200 Lean references, 22/22 controls, and five live BOLT 2 payloads, with fixture digest `1d5ed91c…` and transcript `a47b2aa4…`. This remains finite/public-API conformance, not node-level interop. | Keep both live message rows and the vector suite green; additional message encodings, TLVs, Noise/MAC, dispatch, full decoders, and node-level interop remain future work. Do not claim full protocol conformance.  Keep the three live rows and vector suite green; additional encodings, TLVs, Noise/MAC, dispatch, full decoders, and node-level interop remain future work. |
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

## Wave H 48-lane integration (complete)

Wave H adds **45 independent proof modules** under `LnLean/Proofs/WaveH/` on
top of the remote wave-8 residual lanes. The merged tree keeps all remote
changes, the public-core bump, and the 100-target catalog. It closes `L1-04`
(H33) and `L1-05` (H34), independently confirms `PR-05` (H07/H08/H09), and
adds the per-input `txCheckerFor` equality (H01), the concrete one-input P2WSH
composition (H04), exact `csv`/`MINIMALDATA` boundaries (H05/H06), the
**319-byte** `open_channel` payload (H13–H19), the accept/PoP contract
(H20–H22), commitment-site accounting (H23–H28), epoch-gossip refinement
(H39–H42), schedule/fairness liveness (H43), reduction arithmetic (H44), and
conditional reorg preservation (H45). H46–H48 provide the vendor/clean-checkout
and release artifacts. H20 was adapted to the remote `HandshakeState` change
that removed `DecidableEq`.

## Wave 9 lanes (complete)

Wave 9 launched from `10d18a1` and is integrated on top of the wave-H merge
`b15744b`. Six disjoint lanes delivered the EC-boundary characterization,
transport routing, registration/PoP, arbitrary-preimage coverage, node
canonicalisation, and the live `channel_ready` row. The parent added five new
modules, strengthened six catalog rows from 100 to **142 targets**, and extended
the axiom audit to 269 theorems. Reports are under `agents/reports/swarm9/`.

| Lane | Issue(s) | Owned files | Scope |
|---|---|---|---|
| `S9-L1-EC-UNCONDITIONAL` | `L1-01`, `L1-07` | new `LnLean/Proofs/Bitcoin/EcdsaConcreteTargets.lean`, report | Decide whether a concrete `verifyImpl` instance can satisfy `VendorEcdsaBridge`, or prove the sharpest obstruction/separation; keep `EufCma`/`KeyBinding` explicit |
| `S9-L1-OPENCHANNEL-ROUTING` | `L1-03` | new `LnLean/Proofs/Protocol/OpenChannelRoutingTargets.lean`, report | Transport attribution/provenance and handshake routing for `OpenChannelWire`; wire → `Handshake.OpenChannel` → funding plus a non-attribution boundary |
| `S9-PR-ATTRIBUTION` | `PR-01` | new `LnLean/Proofs/Crypto/AttributionGameTargets.lean`, report | Registration/proof-of-possession game over `StoredAccept`; storage is not possession; conditional `KeyBinding` attribution |
| `S9-PR-ARBITRARY-PREIMAGE` | `PR-02` | new `LnLean/Proofs/Channel/PreimageCoverageTargets.lean`, report | Wire-only coverage and the eight arbitrary-preimage field hypotheses; conditional coverage plus dropped-hypothesis counterexample |
| `S9-RT-NODE-CANON` | `RT-02` | new `LnLean/Proofs/Routing/NodeCanonicalTargets.lean`, report | Node-announcement canonicalisation against the canonical store; invariants, replacement/rotation, and boundary witnesses |
| `S9-CONF-LIVE-MSG` | `CONF-01` | `tests/conformance/**`, `scripts/check-conformance.py`, `LnLean/Proofs/ConformanceDiffTargets.lean`, report | Live BOLT 2 message row if the pinned harness supports it; otherwise the exact blocker with the finite row retained |

Results:

* `S9-L1-EC-UNCONDITIONAL` — concrete `verifyImpl` satisfies the pointwise
  bridge only as total rejection; `VendorEcdsaContract` (`ResidueBinding` +
  `KeyBinding`) is the faithful conditional form, and canonical-domain binding
  is still missing.
* `S9-L1-OPENCHANNEL-ROUTING` — additive transport/routing envelope, concrete
  `open_channel` → `accept_channel` → `funding_created` witness, and explicit
  non-attribution/no-signature boundaries; no core handshake patch.
* `S9-PR-ATTRIBUTION` — registration/PoP game over `StoredAccept`; storage is
  not possession, and the dropped-`KeyBinding` counterexample is retained.
* `S9-PR-ARBITRARY-PREIMAGE` — exact eight-field characterization, conditional
  byte/digest/signature transfer, dropped-locktime/amount counterexamples, and
  display-order/hash-image/amount boundaries.
* `S9-RT-NODE-CANON` — additive node canonicalisation with strict-timestamp
  replacement, rotation/equal-timestamp boundaries, raw-extension
  impossibility, and epoch-square lifting; `RT-02` is narrowed, not closed.
* `S9-CONF-LIVE-MSG` — live `channel_ready` payload through pinned
  rust-lightning `Writeable`; 180 Lean references and 14/14 mutation controls,
  with the finite/public-API caveat retained.

## Wave 10 lanes (complete)

Wave 10 launched from `9158592`, the wave-9 integration and gate-docs tip.
Six disjoint lanes attacked the next layer of the remaining P0/P1 boundaries;
the parent integrated root imports, catalog targets, audit entries, docs, and
the final gate. Reports are under `agents/reports/swarm10/`.

Results:

* `S10-L1-EC-DOMAIN` — no fixed tag repairs `DigestBindsMod`
  (`not_digestBindsMod_any_tag`, `no_digestBindsMod_anywhere`), including at
  fixed 33-byte length; the exact algebraic repair is a canonical fixed-size
  value-`< n` message domain. No unconditional ECDSA/consensus claim.
* `S10-L1-TRANSPORT-AUTH` — authenticated session and explicit
  `SessionKeyBinding` are separated; attributed delivery composes with the
  routed funding witness; no payload-only sender function or transport
  attribution exists. `L1-03` stays open for key binding and C3 ownership.
* `S10-PR-POP-DERIVE` — concrete challenge-response PoP with fixed-width
  injectivity, honest completeness, `PopKeySoundOn`/`PopExtractionOn`
  derivations, and replay counterexamples; `PR-01` keeps its explicit
  computational and key-ownership hypotheses.
* `S10-PR-COVERAGE-WITNESS` — constructive per-HTLC coverage decoder plus a
  proof that no legacy-only decoder/selector is correct for all full records;
  production coverage needs an out-of-band/full-record source or a protocol
  change. `PR-02` is narrowed, not closed.
* `S10-RT-NODE-IDENTITY` — no antisymmetric store-only rotation link; an
  explicit `RotationWitness` preserves wire membership but not signatures;
  wire membership is an additive admission gate not enforced by the core
  transition. `RT-02` is narrowed to the remaining identity/chain/address/rate
  boundaries.
* `S10-CONF-LIVE-MSGS` — live `open_channel` (type 32) row through the pinned
  public rust-lightning `Writeable` encoder; 185 Lean references and 16/16
  mutation controls, with the finite/public-API caveat retained.

| Lane | Issue(s) | Owned files | Scope |
|---|---|---|---|
| `S10-L1-EC-DOMAIN` | `L1-01`, `L1-07` | new `LnLean/Proofs/Bitcoin/EcdsaDomainTargets.lean`, report | Decide whether a canonical tag can repair `DigestBindsMod`; prove the general collision/impossibility or a faithful conditional domain theorem |
| `S10-L1-TRANSPORT-AUTH` | `L1-03` | new `LnLean/Proofs/Protocol/TransportAuthTargets.lean`, report | Transport authentication above `OpenChannelEnvelope`; derive `EnvelopeAttributed` from explicit session/key-binding laws and retain the no-auth boundary |
| `S10-PR-POP-DERIVE` | `PR-01` | new `LnLean/Proofs/Crypto/PopProtocolTargets.lean`, report | Challenge-response PoP protocol; honest completeness, conditional soundness/attribution, and replay/no-challenge counterexample |
| `S10-PR-COVERAGE-WITNESS` | `PR-02` | new `LnLean/Proofs/Channel/CoverageWitnessTargets.lean`, report | Characterize the missing coverage data as a witness; constructive decoder plus legacy-only impossibility |
| `S10-RT-NODE-IDENTITY` | `RT-02` | new `LnLean/Proofs/Routing/NodeIdentityTargets.lean`, report | Node-ID rotation/linkage and wire membership; unlinkability boundary, linkage theorem, and admission/counterexample |
| `S10-CONF-LIVE-MSGS` | `CONF-01` | `tests/conformance/**`, `scripts/check-conformance.py`, `LnLean/Proofs/ConformanceDiffTargets.lean`, report | At least one additional live BOLT 2 message row through pinned rust-lightning `Writeable`; otherwise the exact blocker |

## Wave 11 lanes (complete)

Wave 11 launched from the wave-10 checkpoint `4037264`. Eight disjoint lanes
ran; reports are in `agents/reports/swarm11/`. The catalog gained three rows
(`LN-CH-007`, `LN-PM-007`, `LN-SEC-007`) and seven existing rows were
strengthened, for **51 rows / 277 targets**.

| Lane | Issue(s) | Owned files | Result |
|---|---|---|---|
| `S11-RT-NODE-CHAIN` | `RT-02` | new `LnLean/Proofs/Routing/NodeIdentityChainTargets.lean`, report | Signed rotation certificates, transitive chains, re-signing/wire-membership preservation, old-signature counterexamples, per-node rate/replay limits |
| `S11-L1-NOISE-AUTH` | `L1-03` | new `LnLean/Proofs/Protocol/NoiseTransportTargets.lean`, report | Noise_XK-shaped handshake/session model, AEAD acceptance/provenance, freshness/replay, derived `SessionKeyBinding`, concrete attributed route |
| `S11-CONF-MESSAGES` | `CONF-01` | `tests/conformance/**`, `scripts/check-conformance.py`, `LnLean/Proofs/ConformanceDiffTargets.lean`, report | Live `accept_channel` (type 33) row; 190 Lean references and 18/18 mutation controls |
| `S11-PR-COVERAGE-SOURCE` | `PR-02` | new `LnLean/Proofs/Channel/CoverageSourceTargets.lean`, report | Full-record/out-of-band/protocol-extension sources; exactness, separation, and legacy-wire insufficiency |
| `S11-L1-FINALITY` | `L1-06` | new `LnLean/Proofs/Security/ChainFinalityTargets.lean`, report | Finite block graph, bounded-depth finality, unique-tip form, sharp deep-reorg counterexample |
| `S11-PAY-INVOICE` | `LN-PM-001`–`003`, new `LN-PM-007` | new `LnLean/Proofs/Payment/InvoiceWireTargets.lean`, report | Pre-bech32 field-list codec, round-trip/injectivity, payment-hash/secret binding, signature-vs-payment separation |
| `S11-HTLC-AGGREGATE` | new `LN-CH-007` | new `LnLean/Proofs/Channel/HtlcAggregateTargets.lean`, report | Aggregate HTLC coverage, no-double-spend separation, aliasing counterexample, fee/weight accounting |
| `S11-MODEL-NONVACUITY` | new `LN-SEC-007` | new `LnLean/Proofs/Model/NonVacuityTargets.lean`, report | 30-entry witness registry, `withVendorEcdsa` vacuity, carrier/relation separation |

## Wave 12 lanes (complete)

Wave 12 launched from the wave-11 checkpoint `5ddab4c`. Four disjoint lanes
ran; reports are in `agents/reports/swarm12/`. The catalog remains at 51 rows
and extends to **294 targets**. The independent barrier audit found no new
model-level P0 closure; the remaining P0/P1 rows are externally blocked or
human decisions.

| Lane | Issue(s) | Owned files | Result |
|---|---|---|---|
| `S12-RT-ADDRESS` | `RT-02` | new `LnLean/Proofs/Routing/NodeAddressTargets.lean`, report | BOLT 7 `u16 addrlen` blob and typed IPv4/IPv6/Tor v2/Tor v3/ASCII-DNS descriptors; exact widths, ordering, nonzero ports, round-trip/injectivity, rejection theorems; ten `LN-RT-002` targets |
| `S12-PR-CONSUMER` | `PR-02` / `LN-PR-004` | new `LnLean/Proofs/Channel/CoverageConsumerTargets.lean`, report | Explicit full-record/wire-determined coverage-consumer contract and non-determinacy separation; eight `LN-PR-004` targets |
| `S12-CONF-FUNDING` | `CONF-01` | `tests/conformance/**`, `scripts/check-conformance.py`, `LnLean/Proofs/ConformanceDiffTargets.lean`, report | Live `funding_created` (34) and `funding_signed` (35) payloads; ten Lean targets, 200 refs, 22/22 controls, five live BOLT 2 payloads |
| `S12-AUDIT-BARRIERS` | P0/P1 audit | `agents/reports/swarm12/S12-AUDIT-BARRIERS.md` | Independent non-vacuity/barrier review of the nine P0/P1 rows; no model-level closure; explicit external requirements recorded |

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
| `lake build` | 314 jobs, RC 0 |
| `check-catalog.py --audit` | 51 proved / 0 statement-only / 294 targets / 0 unresolved / 0 proved failures / 11898 declarations |
| `check-catalog.py --allow-planned` | 51/0/0 planned, RC 0 |
| `check.sh` | `files=275 obligations=82 sorry_in_proofs=0`, RC 0 |
| `check-final.py` | 275 Lean files, 273 root imports, RC 0 |
| `check-conformance.py` | 61 base + 16 framing + 9 boundaries, 26 differential fixtures, 200 Lean references, 22/22 mutation controls, 6 finite BOLT 2 message vectors, 3 declared gaps, live 26 BigSize + 3 TLV + 4 wire + 5 BOLT 2 payloads (`funding_created`, `funding_signed`, `channel_ready`, `open_channel`, `accept_channel`), RC 0 |
| `verify-anchors.py` | 313 anchors, 0 bad, 2 unanchored rows, RC 0 |
| `verify-vendor.sh` | 149 files, RC 0 |
| Axiom audit | 435 audited theorems; only `propext`, `Quot.sound`, `Classical.choice` |
