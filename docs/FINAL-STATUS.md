# Final status — Lightning repair tree

**Repository:** `/home/ubuntu/ln-lean-repair`
**Branch:** `repair/integrated`
**Gate HEAD:** proof-wave 7 integration is recorded in the final status commit.
Proof-wave 6 code was `0a3a5fb`; wave 7 launched from `3180581`.
**Catalog state:** **48 `proved` / 0 `statementOnly` / 0 unresolved / 79
targets**.
**Remote refs:** push is non-force to `origin/repair/integrated`. `origin/main`
is not touched by this work. `origin/repair/pubbump` remains a separate
compatibility branch.
**Toolchain:** `leanprover/lean4:v4.35.0`
**L1 build dependency:** read-only `vendor/btc-lean-core` snapshot
`f95080638ae571a3664f4f41b9b6f6b4cfa7c5eb`
**L1 public reference:** `https://github.com/Rob1Ham/btc-lean`
`main@4f5c4f858fb9ca0743042644453cfa92d30dd271` (review only; not imported)
**Spec / client references:** `lightning/bolts`
`1aadb719b4007c4cea0ba6e36b08c4fb53788dee`; `rust-lightning`
`fe4900930c6bd5786ec4203274d7cf312776a5a6`

This file describes **this repair repository**, not the older
`ln-lean-final` / `final/integrated` tree. The earlier final tree (132 Lean
files, 15 open `sorry` sites, vacuous global crypto assumptions) is the
starting point of the repair, not its result.

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
without changing the 48-row count.

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

## Verified state

| Check | Command | Result |
|---|---|---|
| Full build | `LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock lake build` | **RC 0**, `Build completed successfully (233 jobs).` |
| Actual `sorry` | `grep -RInE '^[[:space:]]*sorry[[:space:]]*$' LnLean --include='*.lean'` | **0 matches** (grep RC 1: no lines) |
| Policy checker | `./scripts/check.sh` | **RC 0**, `files=204 obligations=82 sorry_in_proofs=0`, `check: OK` |
| Selection/root checker | `python3 scripts/check-final.py` | **RC 0**, `selected: D=33 E=15 F=15 total=63`, 204 Lean files, 202 root imports |
| Vendor integrity | `./scripts/verify-vendor.sh` | **RC 0**, `OK (119 files)` |
| Anchors | `python3 scripts/verify-anchors.py` | **RC 0**, `anchors=306 bad=0 unanchored_rows=2` |
| Catalog, strict | `python3 scripts/check-catalog.py --audit` | **RC 0**, 48 proved, 0 statement-only, 79 targets, 0 unresolved, 0 proved failures, 0 candidates |
| Catalog, planned-aware | `python3 scripts/check-catalog.py --allow-planned` | **RC 0**, `rows=48 proved=48 statementOnly=0 planned=0 proved_failures=0` |
| Axiom audit | `lake build LnLean.Proofs.PhaseC3.AxiomAudit` | **RC 0**, 194 audited theorems; only `propext`, `Quot.sound`, `Classical.choice` |
| Generated index | `python3 scripts/collect-obligations.py` | `166` proof files, `81` markers, `48` catalog rows, `5761` declarations, `0` `sorry` sites |
| Conformance | `python3 scripts/check-conformance.py` | **RC 0**, 61 base + 16 framing + 9 boundary checks, 33 differential fixtures, 146 Lean theorem references, 9 mutation controls, live 26 BigSize + 3 TLV + 4 wire |

Tree size: **204 Lean files** under `LnLean/`, **202** root imports in
`LnLean.lean`; `LnLean.Proofs.All` and the `LnLean.Proofs.PhaseC2` aggregator
are not root-imported. The full build covers 233 Lake jobs.

The `sorry` grep result is exact: **there are no lines consisting only of
`sorry` (modulo whitespace) in any `LnLean/**/*.lean` file.** Prose mentions of
`sorry` in comments are not proof terms.

## Catalog promotions and scope caveats

All 48 rows are `proved`, but a `proved` row means the named declaration exists
and is sorry-free. Several rows keep explicit model, cryptographic, or L1
hypotheses; the scope caveat is part of the row's meaning.

| Row | Exact target(s) | Scope caveat |
|---|---|---|
| `LN-L1-001` | `FundingScriptTargets.fundingScriptPubKey_eq_p2wsh_twoOfTwo`, `FundingLinkTargets.fundingScriptPubKey_eq_p2wsh_ordered`, `InterpreterBridgeTargets.funding_interpreters_agree`, `SighashBridgeTargets.funding_sighash_interpreters_agree`, `FundingAuthTargets.openAccept_hash_linked` | Handshake constructs the hash link; joint open/accept shares it; positive-direction vendored P2WSH execution; BIP 143 digest/locktime constructed and consumed by the vendor checker; abstract EC/transaction-validity context and finite C1 admission retained |
| `LN-L1-003` | `ReorgTargets.reorg_preserves_channel_safety`, `deep_reorg_separate_failure_mode` | Common tip, common-prefix arithmetic, bounded-depth invariant; deep reorg is a separate failure mode |
| `LN-L1-004` | `ToLocalScriptTargets.toLocalScriptFull_carries_csv_and_revocationKey`, `..._commits_delay_and_revocationKey`, `commitmentOutputs_toLocal_commits_delay_and_revocationKey`, `InterpreterBridgeTargets.toLocal_delayed_interpreters_agree`, `InterpreterRevocationTargets.toLocal_revocation_interpreters_agree`, `SighashBridgeTargets.toLocal_sighash_interpreters_agree`, `SequenceContextTargets.toLocal_delayed_realChecker_refinement` | Full two-branch byte template plus vendored delayed and revocation execution with constructed BIP 143 digest/locktime; decoded BIP 68/112 context is exact and transferred to the real checker; ECDSA, key-separation, `TxValidation.Full`, and sequence-range/policy edges remain explicit |
| `LN-L1-006` | `WeightTargets.commitmentBaseWeight_model_target` | BOLT 3 fee-basis constants `724`/`1124` and `172` per untrimmed HTLC; exact 8 WU anchor serialization gap retained |
| `LN-CR-005` | `TLVStream.wellFormed_iff_pairwise`, `wellFormed_record_type_unique` | Exact theorem-level characterization; out-of-domain counterexample retained |
| `LN-CH-003` | `Commitment.output_ordering`, `CommitmentTx.migratedFrom_outputsNet_perm_commitmentOutputs`, `CommitmentTypes.CommitmentTx.migrateNet_canonicalOutputs_eq_commitmentOutputs`, `CommitmentConsumer.migratedConsumerOutputs_eq_consumerOutputs_of_migrated` | Rich `CommitmentTx` model with script/dust/CLTV; five-field gross/net record layer; arbitrary-dust canonical permutation/refinement; normal-form consumer migration; D12 still refutes legacy `commitmentOutputs`; `trimmedTotalSat` naming decision |
| `LN-CH-005` | `Fee.commitmentSigningGate_rejected_iff_insufficient`, `..._iff_no_checkedSigning` | Exact fee gate; normal-phase transition form explicit |
| `LN-HT-004` | `HTLC.dir_id_unique`, `id_unique_of_reachable_cross`, `tagged_id_unique_of_reachable`, `tagged_ids_nodup_of_reachable`, `cross_direction_duplicate_tagged` | Per-sender uniqueness; direction-tagged ids are globally unique; the untagged global claim needs `CrossDisjoint` and is otherwise refuted |
| `LN-PR-003` | `Handshake.funding_signed_signing_contract`, `SighashTargets.funding_and_commitment_signing_contract`, `KeyModelTargets.funding_signature_attribution` | Conditional on `FundingSigningLaw` + `KeyBinding`; joint funding/commitment contract; secret-key model attributes under `KeyBinding`; C3/generation alone is insufficient |
| `LN-PR-004` | `ProtocolWireTargets.commitment_signed_full_covers_exact`, `protocol_wire_summary`, `SighashTargets.SighashProduces.coverage`, `SighashViewBindingTargets.commitmentSignature_binds_viewOfState`, `SighashTargets.CommitmentWire.txBytes_parse`, `Bip143Preimage.preimageBytes_eq_bip143MsgL_ofTx`, `commitmentBip143Preimage_eq_bip143MsgL` | `CommitmentSignedFull` plus exact BOLT 3 transaction wire layouts/parser round-trips; C3-derived digests; conditional digest-to-view binding; commitment-wire preimage byte equality; HTLC-wire instantiation pending; wire-only negative results retained |
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
  the full preimage byte equality to the vendor hash input remains open;
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
  179/412-byte vectors; the HTLC-wire instantiation remains open;
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

* `OPS-01` — public CI still cannot build from a clean checkout, but the
  `fetch-vendor.sh` path and publication recipe are tested (mitigated);
* `OPS-02` — no `LICENSE`; a neutral decision matrix is ready;
* `OPS-03` — no release tag and `main` is behind; a release checklist is ready;
* `L1-01`/`L1-02`/`L1-07` — the positive funding, delayed, and revocation
  branches now execute through the vendored interpreter and a constructed BIP
  143 digest, but a concrete EC verifier, transaction-validity context,
  decoded sequence context, and unconditional `ConsensusSpendBridge` remain
  open.

Wave 7 closed `CH-01` (consumer path), `RT-01` (canonical wrapper and raw
non-refinement), `CONF-02` (live finite comparison), and `MODEL-02`/`MODEL-03`
(guarded fold; literal fold refuted). `L1-08`, `CH-02`, `CH-03`, `CH-04`,
`PR-06`, `RT-02`, and `CONF-03` remain closed on their recorded conditional
boundaries.

Still open: `TxValidation.Full`/`txCheckerFor` transfer and sequence/policy
edges (`L1-02`, `L1-07`), the `HtlcWire` preimage instantiation (`PR-05`),
the `Messages.openChannel` wire patch (`L1-03`), `AcceptChannel` payload and
registration/proof-of-possession (`PR-01`), computational C1/C3/C8 reductions
(`CR-01`, `SEC-01`), the concrete EC verifier (`L1-01`), and release
packaging (`OPS-01`–`OPS-04`).

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
