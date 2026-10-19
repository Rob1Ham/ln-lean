# Repair TODO — integrated Lightning proof tree

**Worktree:** `/home/ubuntu/ln-lean-repair`
**Branch:** `repair/integrated` (from `final/integrated@af6caae`)
**Toolchain:** `leanprover/lean4:v4.35.0`
**L1 public reference:** `https://github.com/Rob1Ham/btc-lean` (`main@4f5c4f8`)
**Vendor L1 snapshot:** public `btc-lean` `spec/core` at `4f5c4f8` (149 files;
  read-only copy; `repair/pubbump` merged)

## Baseline (done)

- [x] Branch from the green `final/integrated` tree (132 modules, 15 open sites).
- [x] Add the 17 C2 repair modules and 12 C3 composition modules (29 total).
- [x] Replace the five refuted Wave-C sites with the C2 repaired files:
  `FundingProps`, `ReserveProps`, `GossipProps` (5 → 0 sites there).
- [x] Add `LnLean.Proofs.Common` so C2/C3 can share the base without a root import cycle.
- [x] Full root build: **170 jobs, RC 0**.
- [x] Remaining actual `sorry` sites: **10** (`WaveE/E40` + `F03,F04,F05,F06,F07,F09,F13,F14,F15`).

## R1 — Repair the ten remaining false/underspecified sites (0 `sorry` target)

Each site already has a mechanized counterexample and a proved conditional or
admitted-step replacement. The repair is to remove the refuted unconditional
declaration and its open marker, keeping the counterexample and conditional
form. Do **not** turn a false claim into `True`, do not add axioms, and do not
delete the negative result.

- [x] R01 — `LnLean/Proofs/WaveE/E40.lean` — `waveE_e40_accepted_update_signature_length`
- [x] R02 — `LnLean/Proofs/ModelHardening/F03.lean` — `committedUpdate_preserves_ledger_unconditional`
- [x] R03 — `LnLean/Proofs/ModelHardening/F04.lean` — `waveF_f04_legacy_unconditional_conservation`
- [x] R04 — `LnLean/Proofs/ModelHardening/F05.lean` — `waveF_f05_accepted_update_key_announced`
- [x] R05 — `LnLean/Proofs/ModelHardening/F06.lean` — `bindChannel_capacity_positive`
- [x] R06 — `LnLean/Proofs/ModelHardening/F07.lean` — `accepted_message_signatures_64`
- [x] R07 — `LnLean/Proofs/ModelHardening/F09.lean` — `dust_trim_preserves_conservation`
- [x] R08 — `LnLean/Proofs/ModelHardening/F13.lean` — `waveF_f13_unconditional_secret_match`
- [x] R09 — `LnLean/Proofs/ModelHardening/F14.lean` — `waveF_f14_running_total_bound`
- [x] R10 — `LnLean/Proofs/ModelHardening/F15.lean` — `unconditional_settle_reveals_committed`

## R2 — Crypto model consistency

- [x] `M01` — remove the globally inconsistent `sha256_preimageResistant` field
  from `PrimitiveModel`; retain the 32-byte `CollisionResistant` assumption and
  the non-vacuous `preimageResistant_vacuous` negative theorem. Update
  `rejectAllEcdsa` and all downstream uses. Result: the contradictory field pair
  is gone, `PrimitiveModel` is no longer forced uninhabited, SHA-256 headlines
  are no longer vacuous, and no `sorry` is added.

- [x] `M02` — remove the impossible global `hmac_prf` field from
  `PrimitiveModel`; retain only `hmac_size`; prove `hmacPrf_vacuous`; replace
  D07's global `HmacPrf` hypothesis with finite-message `HmacBindsOn`. Update
  `rejectAllEcdsa`, `docs/HMAC-LIMITS.md`, and the C8 text in
  `docs/ASSUMPTIONS.md`. No `sorry` or axiom is added.

- [x] `CCR01` — remove the `CrossChannelRouting` elaboration blowup by
  rewriting `lastAmount` as `(forwardAmounts path).getLastD 0` and proving
  `backwardConserves_sender_eq_last_add_feeSum` by ordinary list induction.
  Module RC 0 at ~1.7 GiB peak (previously 12–19 GiB / SIGKILL).

## R3 — Catalog mechanics

- [x] `K01` — add a source-level checker that resolves every catalog
  `leanTarget` exactly, rejects stale/missing names, and only marks a row
  `proved` when the exact declaration is a theorem/lemma with no `sorry` in its
  body. Keep `statementOnly` otherwise. Publish the candidate/decision table.

## R4 — Public `btc-lean` reference

- [x] `L01` — pin `refs/PINNED.md` and `docs/L1-PIN.md` to the public
  `Rob1Ham/btc-lean` repository; record `main@4f5c4f8`; add
  `refs/btc-lean -> /home/ubuntu/btc-lean-public` as a read-only reference;
  audit the 87-file vendor/public diff and the public script model. Do not
  edit `vendor/btc-lean-core`.

## R5 — Final gate

- [x] Full build with zero actual `sorry` in `LnLean/` — RC 0, 170 jobs,
  `sorry_in_proofs=0`.
- [x] Vendor integrity and anchor checks pass — 119 vendor files, 298 anchors,
  0 bad.
- [x] `scripts/check.sh` / policy checker passes — RC 0.
- [x] `python3 scripts/check-final.py` passes — 164 Lean files, 162 root
  imports.
- [x] Catalog checker passes and reports exact counts — 18 proved / 30
  statementOnly, 23 planned, 0 proved failures; `--allow-planned` RC 0.
- [x] Update `docs/FINAL-STATUS.md`, `docs/WAVE-STATUS.md`, and
  `agents/reports/FINAL-REPAIR.md` at final HEAD `68c236d`.
- [x] Non-force push of `repair/integrated` to `origin`; new remote branch
  created, no rewrite of `main` or another worker's branch. The isolated
  `repair/pubbump` compatibility branch was also pushed separately.

## R6 — Proof-wave round (done)

Supersedes the R5 catalog counts. Eight disjoint lanes ran against the green
repair tree; the catalog now has exact targets for eleven additional rows.

- [x] `W01` — `LN-CR-006` `LnLean.Wire.Message.decode_length`.
- [x] `R01` — `LN-RT-002` `Gossip.update_monotone`, `LN-RT-005`
  `Route.cltv_accumulates`.
- [x] `O01` — `LN-RT-003` `Onion.peel_deterministic`, `LN-RT-004`
  `Onion.hmac_sound` (checked `openLayer`; raw-`peel` D25 counterexample
  retained).
- [x] `P01` — `LN-PR-005` `Peer.reestablish_no_rollback`; D17/E19/E20/
  FeatureClosure retargets documented for the other protocol rows.
- [x] `M01` — `LN-PM-002` `Invoice.signature_valid` (model projection; C3
  remains an assumption), `LN-PM-005` `MPP.running_total_bound`.
- [x] `S01` — `LN-SEC-002` `Conservation.global_conservation` (multi-channel
  only), `LN-SEC-003` `Security.safety_async` (explicit `Assumptions P`),
  `LN-SEC-006` `Liveness.watchtower_bridge` (requires a report).
- [x] `H01` — no fake exact target; added HTLC partition and live-id
  invariants, retained the unconditional-id counterexample.
- [x] `C01` — no fake exact target; added commitment nonnegativity/sum/
  trimming lemmas, retained D46/D12 counterexamples.
- [x] At the end of R6: **29 proved / 19 statementOnly**, **12 planned**, 0
  promotion candidates.
- [x] Full build **170 jobs RC 0**; `check.sh`, `check-final.py`, vendor,
  anchors, public-reference, and planned-aware catalog audit all RC 0.
- [x] Commit and non-force push to `origin/repair/integrated`.

## R7 — Proof-wave 2 (done)

Five disjoint lanes extended the model and promoted eight more exact targets.

- [x] `SEC05-ECON` — `LN-SEC-005` `Liveness.penalty_economical` under
  `FeeScheduleBounded`; unconditional D34 spike counterexample retained.
- [x] `CH02-WF` — `LN-CH-002` `Commitment.outputs_nonnegative` under the BOLT 3
  balance equation; D46 retained.
- [x] `HT-LEDGER` — `LN-HT-003` `HTLC.amount_conservation` under the explicit
  ledger invariant; `LN-HT-004` deliberately retained.
- [x] `PR-WRAPPERS` — `LN-PR-001` `Handshake.open_bounds` and `LN-PR-006`
  `Handshake.feature_intersection` (support-set intersection, BOLT 1 survival).
  `LN-PR-003/004` deliberately retained as conditional characterizations.
- [x] `CR-RETARGET` — retargeted `LN-CR-001/002/003` from `PrimitiveModel`
  fields to `CryptoTargets` conditional contracts; D05/D07 counterexamples
  retained.
- [x] New modules `LnLean/Proofs/ProtocolTargets.lean` and
  `LnLean/Proofs/CryptoTargets.lean`; root imports and `AxiomAudit` extended.
- [x] Catalog: **37 proved / 11 statementOnly**, **1 planned** (`LN-CH-003`),
  3 exact-but-retained, 7 definition targets.
- [x] Full gate and non-force push after integration.

### Proof-wave 3 — catalog closed

- [x] Retargeted and promoted the last eleven rows; catalog is now
  **48 proved / 0 statementOnly / 0 unresolved**.
- [x] `LN-CH-003` — rich `CommitmentTx` ordering/dust/CLTV model; D12 legacy
  refutation retained.
- [x] `LN-HT-004` — per-sender `dir_id_unique`; global form under
  `CrossDisjoint`; cross-direction counterexample retained.
- [x] `LN-PR-003` — `FundingSigningLaw` + `KeyBinding` conditional contract.
- [x] `LN-PR-004` — coverage from per-output signed data + BOLT 3 equations;
  wire-only negative results retained.
- [x] `LN-L1-001/003/004/006`, `LN-CR-005`, `LN-CH-005`, `LN-RT-006` —
  exact theorem targets with explicit scope caveats.
- [x] New proof modules root-imported; `Traceability`, `AxiomAudit`,
  generated indexes, README, and CI status updated.
- [x] Full gate: build 182 jobs, strict catalog RC 0, `check.sh` RC 0,
  `check-final.py` 176/174 RC 0, anchors 299/0 bad, vendor 119 OK.

### Proof-wave 4 — non-catalog attack

- [x] `S4-L1-SPEND` — explicit interpreter-law stack model; serializer equals
  seam templates; conditional 2-of-2 funding and both `to_local` spends;
  rejection cases; vendored real interpreter identified but not imported.
- [x] `S4-VENDOR-CI` — pinned `fetch-vendor.sh`, 43-test suite, CI source
  gates unconditional, explicit clean-build skip unless configured.
- [x] `S4-CONFORMANCE` — 61 BigSize/TLV vectors, checker with mutation
  controls, 86 Lean `decide` theorems.
- [x] `S4-PR-WIRE` — `CommitmentSignedFull`, `ProducedFrom`, conditional exact
  coverage; legacy no-decoder negatives retained.
- [x] `S4-HTLC-GLOBAL` — direction-tagged `HTLCTag` namespace with reachable
  global uniqueness/Nodup; old duplicate maps to distinct tags.
- [x] `S4-FEE-DUST` — second-stage fee, exact dust threshold, trimming
  partition, zero-dust legacy permutation, BOLT 3 accounting.
- [x] `S4-GOSSIP-ATTR` — attributed gossip admission and graph-edge theorem;
  raw-store caveat retained.
- [x] `S4-RELEASE` — release checklist and neutral license matrix; no license,
  tag, merge, or push.
- [x] Six new modules root-imported; `LN-HT-004` and `LN-PR-004` strengthened;
  `AxiomAudit` extended to 101 theorems.
- [x] Full gate: build 188 jobs, strict catalog 61 targets RC 0, `check.sh`
  182/82/0 RC 0, `check-final.py` 182/180 RC 0, conformance 61/86 RC 0,
  anchors 299/0 bad, vendor 119 OK.

### Proof-wave 5 — bridge and completeness attack

- [x] `S5-L1-INTERP` — vendored interpreter bridge for the positive funding
  2-of-2 and delayed `to_local` branches; serializer/wire equality; BIP 143,
  locktime, and revocation boundaries explicit.
- [x] `S5-CH-GROSSNET` — defaulted gross/net commitment fields, net output
  path, arbitrary-dust canonical permutation, conservation/effective-fee
  accounting; literal `Types.lean` patch recorded.
- [x] `S5-PR-SIGHASH` — structural BOLT 3 serializer, `SighashProduces`,
  C3-derived digests/signatures, honest signer, joint funding/commitment
  contract; bit-exact and view-binding gaps retained.
- [x] `S5-CONF-DIFF` — 16 framing cases, 33 pinned rust-lightning fixtures,
  7 mutation controls, 146 Lean references; offline transcriptions documented.
- [x] `S5-MODEL-STEP` — additive `UpdateStep` add/fail/fulfill layer,
  affordability guard, ledger/reserve preservation, E37 refinement.
- [x] `S5-L1-FUNDING` — handshake-constructed funding hash link, ordered P2WSH
  output, handshake theorem; finite C1 admission retained.
- [x] `S5-GOSSIP-ATTR2` — direction-keyed attribution, `NodeId → PubKey`
  consistency, canonical dedup under explicit invariants.
- [x] `S5-SEC-LIMITS` — `docs/CRYPTO-LIMITS.md` and deterministic
  game/reduction interface; no reduction claimed.
- [x] Eight new modules root-imported; five catalog rows strengthened to 67
  targets; `AxiomAudit` extended to 133 theorems.
- [x] Full gate: build 204 jobs, strict catalog 67 targets RC 0, `check.sh`
  190/82/0 RC 0, `check-final.py` 190/188 RC 0, conformance 61+16/33/146 RC 0,
  anchors 305/0 bad, vendor 119 OK.

### Proof-wave 6 — residual L1/encoding/state-machine attack

- [x] `S6-L1-SIGHASH` — BIP 143 witness-v0 model/digest, vendor byte equality,
  constructed `LocktimeEnv`, checker digest consumption, funding/to_local
  instantiations.
- [x] `S6-L1-REVOKE` — vendored `to_local` revocation branch, branch selection,
  wrong-key/delayed-key/wrong-branch negatives.
- [x] `S6-CH-TYPES` — five-field gross/net record patch, migration API,
  field-boundary conservation/effective-fee/canonical refinement.
- [x] `S6-PR-BITEXACT` — exact BOLT 3 transaction wire layouts/parser
  round-trips, BIP 143 preimage size/vector, shared-view/digest refinement,
  script strictness counterexample.
- [x] `S6-PR-VIEWBIND` — conditional signature-to-view binding, non-vacuity
  witnesses, digest-binding-only counterexample.
- [x] `S6-MODEL-DANCE` — additive dance layer, round window, revocation
  ordering, no stale/revoked commitment, balance/ledger/reserve preservation.
- [x] `S6-GOSSIP-DERIVE` — canonical admission/store, derived
  `NodeKeyConsistent`/`CanonicalAnnouncements`, rotation/supersession.
- [x] `S6-CONF-LIVE` — promoted `Wire.Transport`, deterministic fixture
  provenance, 9 mutation controls; live cargo still blocked.
- [x] Seven new files root-imported; four catalog rows strengthened from 67 to
  73 targets; `AxiomAudit` extended to 163 theorems.
- [x] Full gate: build 218 jobs, strict catalog 73 targets RC 0, `check.sh`
  197/82/0 RC 0, `check-final.py` 197/195 RC 0, conformance 61+16+9/33/146
  RC 0, anchors 306/0 bad, vendor 119 OK.

### Proof-wave 7 — sequence, preimage, consumer, fold, and key model

- [x] `S7-L1-SEQUENCE` — exact BIP 68/112 context, policy dependence,
  delayed branch refinement at `verifyImpl`/`realCheckerOf`, bad-signature
  failures at every evaluator layer.
- [x] `S7-PR-PREIMAGE` — preimage byte equality to `encode`/`bip143MsgL`,
  ten-field order, vendored sub-hashes, 179/412-byte vectors.
- [x] `S7-CH-CONSUMER` — consumer migration API, canonical permutation,
  normal-form preservation, coverage counterexample, `trimmedTotalSat` kept.
- [x] `S7-MODEL-FOLD` — guarded fold/refinement; literal unguarded fold
  mechanized as impossible; all counterexamples retained.
- [x] `S7-RT-RAW` — raw gossip non-refinement, canonical-store wrapper,
  reachable invariant, raw-extension impossibility.
- [x] `S7-CONF-LIVE` — pinned 188-package cache and live probe;
  `cargo test --offline --locked`; 26/26 BigSize + 3/3 TLV + 4/4 wire;
  hash-pinned transcript and forged-transcript mutation.
- [x] `S7-L1-FUNDING-AUTH` — `OpenChannel`, funding phase machine, joint
  construction, finite-C1 key-set determination, transport counterexample.
- [x] `S7-PR-KEY` — secret-key/signer model, conditional attribution,
  non-vacuous witness, generation-not-attribution counterexample.
- [x] Seven new files root-imported; six catalog rows strengthened from 73 to
  79 targets; `AxiomAudit` extended to 194 theorems.
- [x] Full gate: build 233 jobs, strict catalog 79 targets RC 0, `check.sh`
  204/82/0 RC 0, `check-final.py` 204/202 RC 0, conformance
  61+16+9/33/146 RC 0 with live evidence, anchors 306/0 bad, vendor 119 OK.
- [x] Closed `CH-01`, `RT-01`, `CONF-02`, `MODEL-02`, and `MODEL-03`;
  retained `L1-02`/`L1-07`, `PR-05`, `L1-03`, and `PR-01` with narrower
  boundaries.

### Public-core vendor bump — merged

- [x] `V01` — replace the private `f950806` snapshot with the public
  `btc-lean` `spec/core` at `4f5c4f8`; 149-file real directory, no self-symlink,
  regenerated `vendor/VENDOR-SHA256`; full 233-job build green on the bump.
- [x] Parent — merge `repair/pubbump`, pin `scripts/fetch-vendor.sh` to
  `4f5c4f8`, make CI fall back to `--from-git` instead of skipping the build,
  and retire the merged branch.
- [x] `OPS-01` closed with hosted CI runs `39175507618` and `39177572471` executing the pinned-vendor full build; `OPS-04` closed.

### Proof-wave 8 — residual transfer, wire, registration, EC, and store epochs

Wave 8 launched from `50d78ed`; the lane plan is `agents/swarm/WAVE-8.md` and
reports go to `agents/reports/swarm8/`.

- [x] `S8-L1-TXVALID` — exact known-amount `txCheckerFor`/`realCheckerOf`
  transfer, delayed/revocation transfer, missing-amount fail-closed, and
  `minimalData`/`csv ≥ 32768` policy edges.
- [x] `S8-PR-HTLCPREIMAGE` — `HtlcWire` preimage byte equality, 143/136-byte
  scriptCode synthesis, and display-order txid boundary.
- [x] `S8-L1-OPENCHANNEL-WIRE` — type-32 `Msg.openChannel` constructor,
  six-key/type/length/identity laws, and end-to-end funding projection.
- [x] `S8-PR-ACCEPT-PAYLOAD` — `acceptChannel?` storage/provenance and the
  conditional attribution/negative possession bridge.
- [x] `S8-CH-CONSUMER-SITES` — proof-layer consumer adapter and compiled site
  examples; no production `CommitmentTx` consumer.
- [x] `S8-L1-EC-BRIDGE` — sharp conditional `VendorEcdsaBridge` and exact
  `verifyImpl` transfer; no unconditional EC claim.
- [x] `S8-CONF-ENCODINGS` — six BOLT 2 message vectors, 29 `decide` theorems,
  and 13/13 mutation controls; live message row deferred.
- [x] `S8-MODEL-STORE-EPOCH` — gossip-store epochs/replacement history over
  the canonical wrapper, with two divergence witnesses.
- [x] Parent integration: seven new root imports, seven catalog rows
  strengthened from 79 to 100 targets, audit extended to 215 theorems, generated
  indexes/docs refreshed, full gate green, and code commit `9bafdab`.

Wave-8 reports are in `agents/reports/swarm8/`. The proof-wave-8 gate is
**build 250 jobs, strict catalog 100 targets / 8181 declarations, check.sh
`files=211 obligations=82 sorry_in_proofs=0`, 215 audited theorems, 306
anchors, 149 vendor files, and 0 forbidden constructs.** The next candidates
are tracked in `docs/OPEN-ISSUES.md`; wave 10 later attacked the next layer.

### Proof-wave 9 — remaining boundaries after wave H

Wave 9 launched from `10d18a1` and is integrated on top of the wave-H merge
`b15744b`. The lane plan is `agents/swarm/WAVE-9.md`; reports are in
`agents/reports/swarm9/`. All six lanes are complete and integrated.

- [x] `S9-PR-ATTRIBUTION` — registration/PoP game over `StoredAccept`, storage
  is not possession, conditional `KeyBinding` attribution, and the
  dropped-`KeyBinding` counterexample.
- [x] `S9-L1-EC-UNCONDITIONAL` — sharp EC obstruction: the concrete pointwise
  bridge forces total rejection; `VendorEcdsaContract` is the faithful
  conditional form.
- [x] `S9-L1-OPENCHANNEL-ROUTING` — transport attribution envelope, concrete
  `open_channel` → `accept_channel` → `funding_created` route, and explicit
  non-attribution/no-signature boundaries.
- [x] `S9-PR-ARBITRARY-PREIMAGE` — wire-only coverage and the eight
  arbitrary-preimage field hypotheses, with dropped-locktime/amount
  counterexamples, display-order and 20-byte hash-image boundaries.
- [x] `S9-RT-NODE-CANON` — node-announcement canonicalisation; `RT-02`
  narrowed to rotation identity and wire membership, not closed.
- [x] `S9-CONF-LIVE-MSG` — live `channel_ready` payload encoded through the
  pinned rust-lightning `Writeable` implementation; 180 Lean refs and 14/14
  mutation controls.
- [x] Parent integration: five root-imported modules, six catalog rows
  strengthened from 100 to 142 targets, audit extended to 269 theorems,
  generated indexes/docs refreshed, full gate green, and the non-force
  checkpoint committed at `9359475`.

Wave-9 gate: **build 300 jobs, strict catalog 142 targets / 10742
declarations, `check.sh` `files=261 obligations=82 sorry_in_proofs=0`, 269
audited theorems, 310 anchors, 149 vendor files, conformance 180 refs and
14/14 controls, and zero actual `sorry`/forbidden constructs.**

### Proof-wave 10 — boundary layer and second live row

Wave 10 launched from `9158592` (wave-9 integration and gate docs). The lane
plan is `agents/swarm/WAVE-10.md`; reports are in
`agents/reports/swarm10/`. All six lanes are complete and integrated.

- [x] `S10-L1-EC-DOMAIN` — no fixed tag repairs `DigestBindsMod`
  (`not_digestBindsMod_any_tag`, `no_digestBindsMod_anywhere`); the exact
  algebraic repair is a canonical fixed-size value-`< n` domain. No
  unconditional ECDSA/consensus claim.
- [x] `S10-L1-TRANSPORT-AUTH` — authenticated session separated from explicit
  `SessionKeyBinding`; attributed delivery composed with the funding route;
  no payload-only sender or transport-attribution function.
- [x] `S10-PR-POP-DERIVE` — concrete challenge-response PoP, fixed-width
  injectivity, honest completeness, derived `PopSound`/`PopProducedBy`, and
  replay counterexamples.
- [x] `S10-PR-COVERAGE-WITNESS` — constructive per-HTLC coverage decoder plus
  legacy-only impossibility; production coverage needs an out-of-band/full
  record or a protocol change.
- [x] `S10-RT-NODE-IDENTITY` — no antisymmetric store-only rotation link;
  explicit witness preserves wire membership but not signatures; core
  admission does not enforce wire membership.
- [x] `S10-CONF-LIVE-MSGS` — live `open_channel` (type 32) base case through
  the pinned public rust-lightning encoder; 185 Lean refs and 16/16 mutation
  controls.
- [x] Parent integration: five root-imported modules, six catalog rows
  strengthened from 142 to 198 targets, audit extended to 323 theorems,
  generated indexes/docs refreshed, full gate green, and the non-force
  checkpoint prepared.

Wave-10 gate: **build 305 jobs, strict catalog 198 targets / 10968
declarations, `check.sh` `files=266 obligations=82 sorry_in_proofs=0`, 323
audited theorems, 311 anchors, 149 vendor files, conformance 185 refs and
16/16 controls, and zero actual `sorry`/forbidden constructs.**

The catalog is no longer the work queue. Open issues are tracked in
`docs/OPEN-ISSUES.md`; the swarm protocol is `docs/SWARM-LOOP.md`.
Human-gated release decisions remain outside agent lanes.

### Proof-wave 11 — identity chains, Noise binding, coverage sources, finality, invoices, aggregate HTLCs, non-vacuity

Wave 11 launched from `4037264` with eight disjoint lanes and integrated
seven new proof modules plus the live `accept_channel` conformance row. The
catalog gained `LN-CH-007`, `LN-PM-007`, and `LN-SEC-007`, and seven existing
rows were strengthened.

- [x] `S11-RT-NODE-CHAIN` — signed rotation certificates, transitive
  authenticated chains, explicit re-signing with wire-membership preservation,
  old-signature counterexamples, and per-node timestamp/sequence rate limits.
- [x] `S11-L1-NOISE-AUTH` — Noise_XK-shaped handshake/session model, AEAD
  acceptance/provenance, nonce freshness/replay, derived `SessionKeyBinding`,
  and concrete attributed delivery; computational security remains explicit.
- [x] `S11-CONF-MESSAGES` — live `accept_channel` type-33 payload through the
  pinned public rust-lightning `Writeable` encoder; 190 Lean references and
  18/18 mutation controls.
- [x] `S11-PR-COVERAGE-SOURCE` — full-record, out-of-band, and
  protocol-extension sources; exactness, separation, and legacy-wire
  insufficiency.
- [x] `S11-L1-FINALITY` — finite block graph, bounded-depth finality,
  unique-tip family form, sharp deep-reorg counterexample, and bridge to the
  existing reorg/retention layer.
- [x] `S11-PAY-INVOICE` — pre-bech32 BOLT 11 field-list codec, parse/print
  round-trip and injectivity, duplicate/malformed rejection, payment-hash and
  secret binding, and signature-vs-payment separation.
- [x] `S11-HTLC-AGGREGATE` — aggregate HTLC coverage, no-double-spend
  separation, aliasing counterexample, and exact fee/weight accounting.
- [x] `S11-MODEL-NONVACUITY` — 30-entry witness registry, `withVendorEcdsa`
  vacuity result, and carrier/relation inhabitance separation.
- [x] Parent integration: seven root-imported modules, three new catalog rows,
  seven rows strengthened from 198 to 277 targets, audit extended to 407
  theorems, generated indexes/docs refreshed, full gate green, and a non-force
  checkpoint published at `9940642` and `90ef1f1` (hosted CI
  `39288684058` and `39290061147` green).

Wave-11 gate: **build 312 jobs, strict catalog 51/51 proved / 277 targets /
11743 declarations, `check.sh` `files=273 obligations=82 sorry_in_proofs=0`,
407 audited theorems, 311 anchors, 149 vendor files, conformance 190 refs and
18/18 controls, and zero actual `sorry`/forbidden constructs.**

## Commands

```sh
export PATH=/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
cd /home/ubuntu/ln-lean-repair
flock -w 1800 /tmp/ln-build.lock lake build LnLean
./scripts/verify-vendor.sh
python3 scripts/verify-anchors.py
./scripts/check.sh
python3 scripts/check-final.py
python3 scripts/check-catalog.py --allow-planned
python3 scripts/check-conformance.py
```
