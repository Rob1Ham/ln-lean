# Wave status — repair branch

**Repository:** `/home/ubuntu/ln-lean-repair`
**Branch:** `repair/integrated`
**Gate HEAD:** `f0a3c07` (`[WAVE14]` code integration); later docs-only status
commits may advance the tip.
Base `9359475` (wave-9 integration); wave 10 launched from `9158592`; wave 11
launched from `4037264`; wave 12 launched from `5ddab4c`; wave 14 launched from
`a331b71`.
**Catalog:** 51 proved / 0 statementOnly / 0 unresolved / 294 target occurrences
(282 unique declarations).
**Wave 14:** integrated at `f0a3c07`; 16 disjoint additive repair/assurance
lanes complete. Reports are under `agents/reports/wave14/`; lane plan and
contract are `agents/swarm/WAVE-14.md`. The wave narrows `REV-01`–`REV-07`
without moving the external barriers and without adding catalog rows. Local
gate: **330 jobs, 291 Lean files, 289 root imports, 315 anchors, 0 `sorry`**.
**Wave 12:** historical; integrated and published non-force at `d210079` with
four lanes (BOLT 7 address parsing, coverage-consumer contract, live
`funding_created`/`funding_signed`, barrier audit). Hosted CI through the
wave-13 review tip `a331b71` is green.
**Toolchain:** `leanprover/lean4:v4.35.0`

This file describes the repair branch. Older wave tables are retained as
history; they are not a claim about the current tree. Current open work is in
`docs/OPEN-ISSUES.md`; the operating protocol is `docs/SWARM-LOOP.md`.

## Wave 13 review (read-only, 2026-10-19)

A 32-lane review scoped remaining work against pinned
`ldk-node@fa123fed131e27ecc420b77fa7086fcf1ddaebb8` and
`ldk-server@c17dc11dde38f88c53457039ddf30c6b90a63ba2`. All 32 reports are in
`agents/reports/wave13-review/`; `R32-synthesis.md` is the ranked result and
`README.md` is the short index. The review did not change Lean code.

The review found no new path through the external L1/Noise/EUF-CMA/source
barriers, but it did find tractable defects in already-proved consumer rows:
reserve/in-flight admission (`REV-01`), anchored commitment debit (`REV-02`),
replay/duplicate admission (`REV-03`), non-chain-backed `routeValid`
(`REV-04`), and axiom/traceability coverage overstatement (`REV-05`). A
bounded six-lane repair+assurance wave (`W13-LIQ`, `W13-ANCHOR`, `W13-PAY`,
`W13-STATE`, `W13-ROUTE`, `W13-ASSURANCE`) is recommended; see
`agents/reports/wave13-review/R32-synthesis.md` §6.2. The S12 sentence "no new
tractable P0/P1 proof lane" remains true only for the eight external-barrier
rows, not for this review-derived class. Hosted CI run `39325365957` is green
at `c88d9fd` (source-level gates and the pinned-vendor build gate).

## Current state

| Metric | Value |
|---|---|
| Lean files under `LnLean/` | **291** |
| Root imports in `LnLean.lean` | **289** (`LnLean.Proofs.All` and the `PhaseC2` aggregator are not root-imported) |
| Full build | **RC 0**, `Build completed successfully (330 jobs)` |
| Actual `sorry` lines | **0** (`grep -RInE '^[[:space:]]*sorry[[:space:]]*$' LnLean --include='*.lean'` → no matches, grep RC 1) |
| Proof files with the word `sorry` in prose | comments only, not proof terms |
| Catalog rows | **51** |
| Catalog `proved` | **51** |
| Catalog `statementOnly` | **0** |
| Catalog targets | **294 occurrences / 282 unique declarations** (12 duplicate ECDSA names) |
| Unresolved/planned targets | **0** |
| Vendor snapshot | **OK**, 149 files from public `btc-lean` `4f5c4f8`; `fetch-vendor.sh --from-git` tested |
| Anchors | **315 checked, 0 bad**, 2 unanchored rows |
| Generated obligation index | 253 proof files, 81 markers, 51 catalog rows, 9978 declarations, 0 `sorry` sites |
| Axiom audit | **423 `#print axioms` commands; 465-name registry**; printed names use only `propext`, `Quot.sound`, `Classical.choice`; 72 unique catalog targets are unprinted and 35 absent from the registry (`REV-05`) |
| Conformance | 61 base + 16 framing + 9 boundary checks, 26 differential fixtures, 200 Lean references, 22/22 mutation controls, 3 declared model gaps; live 26 BigSize + 3 TLV + 4 wire + 5 BOLT 2 messages; 6 finite BOLT 2 message vectors |
| Public L1 pin | `Rob1Ham/btc-lean` `main@4f5c4f8` |
| Build dependency | `vendor/btc-lean-core` `4f5c4f8` (public `spec/core` copy) |

The exact `sorry` result is **zero matching lines**. Prose mentions of
`sorry` in documentation are not `sorry` terms.

## Proof-wave 14 gate

- `lake build` — **RC 0**, 330 jobs.
- `check-catalog.py --audit` — **RC 0**, 51 proved, 0 statement-only,
  294 target occurrences (282 unique), 0 unresolved, 0 proved failures, 0
  candidates, 12,374 declarations.
- `check.sh` — **RC 0**: `files=291 obligations=82 sorry_in_proofs=0`,
  `check: OK`.
- `check-final.py` — **RC 0**: 291 Lean files, 289 root imports, D=33 E=15
  F=15.
- `check-conformance.py` — **RC 0**: 200 Lean references, 22/22 mutation
  controls, 6 finite BOLT 2 message vectors, and five live BOLT 2 payloads
  (`funding_created`, `funding_signed`, `channel_ready`, `open_channel`,
  `accept_channel`), unchanged from wave 12.
- `verify-vendor.sh` — **RC 0**, 149 files (public `4f5c4f8` snapshot).
- `verify-anchors.py` — **RC 0**, 315 anchors, 0 bad, 2 unanchored rows.
- `AxiomAudit` — **RC 0**, 423 `#print axioms` commands over a 465-name
  registry; 30 new Wave 14 headline entries; every printed name uses only the
  permitted classical axioms.
- `check-assurance-coverage.py --report` — **RC 0**: 294 occurrences / 282
  unique, 423 prints / 465 registry, 72 unprinted, 35 unregistered, 0
  traceability mismatches. `--strict` is **RC 1** on the current gap, as
  intended; `--self-test` is **RC 0** and detects both injected faults.
- Exact `sorry` scan — **0** matching lines.

## Proof-wave 12 gate (historical)

- `lake build` — **RC 0**, 314 jobs.
- `check-catalog.py --audit` — **RC 0**, 51 proved, 0 statement-only,
  294 target occurrences (282 unique), 0 unresolved, 0 proved failures, 0
  candidates, 11,898 declarations.
- `check.sh` — **RC 0**: `files=275 obligations=82 sorry_in_proofs=0`,
  `check: OK`.
- `check-final.py` — **RC 0**: 275 Lean files, 273 root imports, D=33 E=15
  F=15.
- `check-conformance.py` — **RC 0**: 200 Lean references, 22/22 mutation
  controls, 6 finite BOLT 2 message vectors, 26 differential fixtures, live
  transcript `a47b2aa4a2e16f519efa451c0090262f1ebba80a3999fda8668ee554f2dbc892`
  with 26 BigSize + 3 TLV + 4 wire + 5 live BOLT 2 payloads
  (`funding_created`, `funding_signed`, `channel_ready`, `open_channel`,
  `accept_channel`).
- `verify-vendor.sh` — **RC 0**, 149 files (public `4f5c4f8` snapshot).
- `verify-anchors.py` — **RC 0**, 313 anchors, 0 bad, 2 unanchored rows.
- `AxiomAudit` — **RC 0**, 393 `#print axioms` commands over a 435-name
  registry; every printed name uses only the permitted classical axioms. The
  `choice` short name printed inside `open Classical` namespaces is
  `Classical.choice` when checked at root. Registry-to-print coverage is not
  complete; see `REV-05` and `agents/reports/wave13-review/R31-*.md`.

## Proof-wave 11 gate

- `lake build` — **RC 0**, 312 jobs.
- `check-catalog.py --audit` — **RC 0**, 51 proved, 0 statement-only,
  277 targets, 0 unresolved, 0 proved failures, 0 candidates, 11,743
  declarations.
- `check.sh` — **RC 0**: `files=273 obligations=82 sorry_in_proofs=0`,
  `check: OK`.
- `check-final.py` — **RC 0**: 273 Lean files, 271 root imports, D=33 E=15
  F=15.
- `check-conformance.py` — **RC 0**: 190 Lean references, 18/18 mutation
  controls, 6 finite BOLT 2 message vectors, live transcript `2677d760420f…`
  with 26 BigSize + 3 TLV + 4 wire + 3 live BOLT 2 payloads
  (`channel_ready`, `open_channel`, `accept_channel`).
- `verify-vendor.sh` — **RC 0**, 149 files (public `4f5c4f8` snapshot).
- `verify-anchors.py` — **RC 0**, 311 anchors, 0 bad, 2 unanchored rows.
- `AxiomAudit` — **RC 0**, 407 audited theorems with the permitted classical
  axioms only.

## Proof-wave 10 gate

- `lake build` — **RC 0**, 305 jobs.
- `check-catalog.py --audit` — **RC 0**, 48 proved, 0 statement-only,
  198 targets, 0 unresolved, 0 proved failures, 0 candidates, 10968
  declarations.
- `check.sh` — **RC 0**: `files=266 obligations=82 sorry_in_proofs=0`,
  `check: OK`.
- `check-final.py` — **RC 0**: 266 Lean files, 264 root imports, D=33 E=15
  F=15.
- `check-conformance.py` — **RC 0**: 61 base + 16 framing + 9 boundary
  checks, 33 differential fixtures, 185 Lean references, 16/16 mutation
  controls, 6 finite BOLT 2 message vectors, live transcript `9c6b664d7ac4…`
  with 26 BigSize + 3 TLV + 4 wire + 2 live BOLT 2 payloads
  (`channel_ready`, `open_channel`).
- `verify-vendor.sh` — **RC 0**, 149 files (public `4f5c4f8` snapshot).
- `verify-anchors.py` — **RC 0**, 311 anchors, 0 bad, 2 unanchored rows.
- `AxiomAudit` — **RC 0**, 323 audited theorems with the permitted classical
  axioms only.

**Proof-wave 10 gate: PASS.** Push is non-force to
`origin/repair/integrated`; the exact commit is recorded in
`docs/FINAL-STATUS.md`.

## Proof-wave 9 gate

- `lake build` — **RC 0**, 300 jobs.
- `check-catalog.py --audit` — **RC 0**, 48 proved, 0 statement-only,
  142 targets, 0 unresolved, 0 proved failures, 0 candidates, 10742
  declarations.
- `check-catalog.py --allow-planned` — **RC 0**, same counts with
  `planned=0`.
- `check.sh` — **RC 0**: `files=261 obligations=82 sorry_in_proofs=0`,
  `check: OK`.
- `check-final.py` — **RC 0**: 261 Lean files, 259 root imports, D=33 E=15
  F=15.
- `check-conformance.py` — **RC 0**: 61 base + 16 framing + 9 boundary
  checks, 33 differential fixtures, 180 Lean references, 14/14 mutation
  controls, 6 finite BOLT 2 message vectors, deterministic fixture provenance
  verified, live transcript `105920ff8e46…` with 26 BigSize + 3 TLV + 4 wire
  + 1 live BOLT 2 `channel_ready` payload.
- `verify-vendor.sh` — **RC 0**, 149 files (public `4f5c4f8` snapshot).
- `verify-anchors.py` — **RC 0**, 310 anchors, 0 bad, 2 unanchored rows.
- `AxiomAudit` — **RC 0**, 269 audited theorems with the permitted classical
  axioms only.

**Proof-wave 9 gate: PASS.** Push is non-force to
`origin/repair/integrated`; the exact commit is recorded in
`docs/FINAL-STATUS.md`.

## Wave 6 lanes

| Lane | Issue / row | Result |
|---|---|---|
| `S6-L1-SIGHASH` | `L1-08`, `L1-07` | BIP 143 witness-v0 model, vendor byte equality, constructed `LocktimeEnv`, checker digest consumption, funding/to_local instantiation |
| `S6-L1-REVOKE` | `L1-02`, `L1-07` | Vendored revocation branch, branch selection, wrong-key/delayed-key/wrong-branch negatives |
| `S6-CH-TYPES` | `CH-04`, `CH-03` | Five-field gross/net record patch, migration API, field-boundary conservation/effective-fee/canonical refinement |
| `S6-PR-BITEXACT` | `PR-05`, `PR-02` | Exact BOLT 3 transaction wire layouts, BIP 143 preimage size/vector, shared-view/digest refinement, script strictness counterexample |
| `S6-PR-VIEWBIND` | `PR-06`, `PR-02` | Conditional signature-to-view binding, non-vacuity witnesses, digest-binding-only counterexample |
| `S6-MODEL-DANCE` | `MODEL-03`, `MODEL-02` | Additive commitment-dance layer, round window, revocation ordering, no stale commitment, balance/reserve/ledger preservation |
| `S6-GOSSIP-DERIVE` | `RT-02`, `RT-01` | Canonical admission/store, derived `NodeKeyConsistent`/`CanonicalAnnouncements`, rotation/supersession, raw-store counterexample retained |
| `S6-CONF-LIVE` | `CONF-03`, `CONF-02` | Promoted `Wire.Transport`, deterministic fixture provenance, 9 mutation controls; live cargo still blocked |

Wave 6 added seven Lean files (one model module and six proof modules),
strengthened four catalog rows from 67 to 73 resolved targets, extended the
audit to 163 headline theorems, and kept the 48/0/0 catalog gate.

## Wave 7 lanes

| Lane | Issue / row | Result |
|---|---|---|
| `S7-L1-SEQUENCE` | `L1-02`, `L1-07` | Exact BIP 68/112 context, policy dependence, delayed branch refinement at `verifyImpl`/`realCheckerOf`, bad-signature failures |
| `S7-PR-PREIMAGE` | `PR-05`, `PR-02` | Preimage byte equality to `encode`/`bip143MsgL`, ten-field order, vendored sub-hashes, 179/412-byte vectors |
| `S7-CH-CONSUMER` | `CH-01`, `CH-02` | Consumer migration API, canonical permutation, normal-form preservation, coverage counterexample |
| `S7-MODEL-FOLD` | `MODEL-02`, `MODEL-03` | Guarded fold/refinement; literal unguarded fold mechanized as impossible; counterexamples retained |
| `S7-RT-RAW` | `RT-01` | Raw gossip non-refinement, canonical-store wrapper, reachable invariant, raw-extension impossibility |
| `S7-CONF-LIVE` | `CONF-02`, `CONF-01` | Pinned live cargo harness, 26/26 BigSize + 3/3 TLV + 4/4 wire, hash-pinned transcript |
| `S7-L1-FUNDING-AUTH` | `L1-03` | `OpenChannel`, funding phase machine, joint construction, finite-C1 key-set determination, scope counterexample |
| `S7-PR-KEY` | `PR-01` | Secret-key model, conditional attribution, non-vacuous witness, `key_generation_not_key_attribution` |

Wave 7 added seven Lean files (one crypto model and six proof modules),
strengthened six catalog rows from 73 to 79 resolved targets, extended the
audit to 194 headline theorems, and closed `CH-01`, `RT-01`, `CONF-02`,
`MODEL-02`, and `MODEL-03`. The remaining open issues are in
`docs/OPEN-ISSUES.md`.

## Wave H 48-lane integration

The independent Wave H branch was merged into the remote wave-8 residual tree.
It adds **45 proof modules** under `LnLean/Proofs/WaveH/` and keeps the remote
public-core bump, protocol/routing changes, and 100-target catalog. The merged
gate is **295 Lake jobs, RC 0**, with **256 Lean files**, **254 root imports**,
**227 audited theorems**, **309 anchors**, **149 vendor files**, and zero actual
`sorry`.

Wave H closes `L1-04` (H33: `1116 + 172*k` witness weight vs `1124 + 172*k`
fee basis; the 8 WU is `count_tx_out`) and `L1-05` (H34: 71-byte script
injectivity counterexample plus a domain-separated commitment). H07/H08/H09
independently confirm the HTLC preimage/scriptCode path and `PR-05`. H13–H22
fix the **319-byte** `open_channel` payload and add the accept/PoP contract.
H39–H45 add epoch gossip, schedule/fairness liveness, reduction arithmetic,
and conditional reorg preservation. H46–H48 provide vendor/clean-checkout and
release artifacts. H20 was adapted to the remote `HandshakeState` change that
removed `DecidableEq`.

## Historical waves

| Wave | Scope | Result |
|---|---|---|
| Repair lanes `R01`–`R10`, `M01`, `M02`, `K01`, `L01`, `CCR01` | Repair false sites, crypto interface, catalog checker, public pin, elaboration blowup | Green; counterexamples retained |
| Proof-wave 1 (`W01`, `R01`, `O01`, `H01`, `C01`, `P01`, `M01`, `S01`) | Exact targets for wire, routing/onion, payments, security/liveness | 11 rows promoted; HTLC/commitment gaps narrowed |
| Proof-wave 2 (`SEC05-ECON`, `CH02-WF`, `HT-LEDGER`, `PR-WRAPPERS`, `CR-RETARGET`) | Penalty economics, commitment nonnegativity, HTLC partition, protocol wrappers, crypto retargets | 8 rows promoted; 11 remained |
| Proof-wave 3 (12 lanes) | Final catalog retargets and release hygiene | **11 rows promoted; 48/0/0** |
| Proof-wave 4 (8 lanes) | L1 spend bridge, vendor/CI, conformance, wire, global ids, fee/dust, gossip attribution, release | **6 modules; 61 targets; 188-job gate** |
| Proof-wave 5 (8 lanes) | Vendored L1 bridge, gross/net, sighash, differential conformance, update step, funding link, gossip consistency, crypto limits | **8 modules; 67 targets; 204-job gate** |
| Proof-wave 6 (8 lanes) | BIP 143/revocation, five-field commitment, bit-exact wire, conditional view binding, dance, canonical gossip, transport promotion | **7 files; 73 targets; 218-job gate** |
| Proof-wave 7 (8 lanes) | Sequence context, preimage equality, consumer migration, guarded fold, raw gossip, live conformance, open_channel auth, key model | **7 files; 79 targets; 233-job gate** |
| Proof-wave 8 (8 lanes) | `TxValidation.Full` transfer, HTLC preimage, type-32 `open_channel`, accept payload, consumer adapter, conditional ECDSA bridge, BOLT 2 encodings, store epochs | **7 files; 100 targets; 250-job gate** |
| Wave H 48-lane integration | 45 independent modules: per-input checker/composition, HTLC preimage/scriptCode, 319-byte `open_channel`, accept/PoP, commitment sites, anchor/script-commitment, epoch gossip, liveness, reduction arithmetic, reorg, release artifacts | **45 files; 100 targets; 227 audited; 295-job merged gate** |
| Proof-wave 9 (6 lanes) | EC boundary, transport routing, registration/PoP, arbitrary preimages, node canonicalisation, live `channel_ready` | **5 files; 142 targets; 269 audited; 300-job gate** |
| Proof-wave 10 (6 lanes) | Tag-independent EC digest obstruction, transport auth, concrete PoP, coverage witness, node identity/wire membership, live `open_channel` | **5 files; 198 targets; 323 audited; 305-job gate** |

## Reproduce

```sh
export PATH=/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
cd /home/ubuntu/ln-lean-repair

LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock lake build
./scripts/check.sh
python3 scripts/check-final.py
python3 scripts/check-catalog.py --audit
python3 scripts/check-catalog.py --allow-planned
python3 scripts/check-conformance.py
python3 scripts/verify-anchors.py
./scripts/verify-vendor.sh
```

## Not claimed

A green build and zero actual `sorry` terms do not make the model a full
Lightning verification. The concrete EC/transaction-validity bridge, the
`HtlcWire` preimage instantiation, `Messages.openChannel` integration,
`AcceptChannel` registration, computational crypto, vendor reproducibility,
and release packaging remain open. The literal unguarded fold and canonical
raw-gossip refinement are now mechanized as impossible rather than merely
unfinished. See `docs/OPEN-ISSUES.md`.


## Wave 8 lanes

Wave 8 launched from `50d78ed` and integrated seven new proof modules plus
additive protocol/routing/conformance changes. The catalog stayed at 48 rows
and 0 statement-only; seven existing rows were strengthened from 79 to **100
resolved targets**. Reports are under `agents/reports/swarm8/`.

| Lane | Issue(s) | Result | Owned files |
|---|---|---|---|
| `S8-L1-TXVALID` | `L1-02`, `L1-07` | Exact `txCheckerFor (some amount) = realCheckerOf` transfer; delayed/revocation branch transfer; missing amount fail-closed; `minimalData` and `csv ≥ 32768` decode boundaries, including the `csv = 32768` collapse | new `TxValidTransferTargets.lean` |
| `S8-PR-HTLCPREIMAGE` | `PR-05`, `PR-02` | Exact `HtlcWire` BIP 143 preimage byte equality, `ofTx`/`toPreimage` bridge, 143/136-byte scriptCode synthesis, 300/293-byte preimages, display-order txid conversion | new `HtlcPreimageTargets.lean` |
| `S8-L1-OPENCHANNEL-WIRE` | `L1-03` | Type-32 `Msg.openChannel`, `MsgKind.openChannel`, six-key/type/length/identity laws, projection to `Handshake.OpenChannel`, funding construction, end-to-end `FundingPhase` reachability | `Messages.lean`, new `OpenChannelWireTargets.lean` |
| `S8-PR-ACCEPT-PAYLOAD` | `PR-01` | `HandshakeState.acceptChannel?`, `handshakeStepRecvAccept`, provenance/stability lemmas, `StoredAccept`, conditional attribution, negative proof-of-possession | `Handshake.lean`, new `AcceptPayloadTargets.lean` |
| `S8-CH-CONSUMER-SITES` | `CH-01` | Proof-layer `SignedState.toCommitmentTx`, legacy-boundary equality/Perm theorems, coverage bridge, concrete site examples; no production `CommitmentTx` consumer | `CommitmentConsumerTargets.lean`, new `CommitmentConsumerSitesTargets.lean` |
| `S8-L1-EC-BRIDGE` | `L1-01`, `L1-07` | Sharp conditional `VendorEcdsaBridge`; exact `verifyImpl` argument-order bridge; funding/commitment/close agreement; EUF-CMA/key-binding transfer; message-reduction and key-parsing boundaries | new `EcdsaBridgeTargets.lean` |
| `S8-CONF-ENCODINGS` | `CONF-01` | Six BOLT 2 message vectors, 29 `decide` theorems, 13/13 mutation controls; live message row deferred | `ConformanceDiffTargets.lean`, `scripts/check-conformance.py`, `tests/conformance/**` |
| `S8-MODEL-STORE-EPOCH` | `RT-01`, `RT-02` | Typed replacement history, `StoreEpoch`/`epochStep`/`epochFold`, sequence-level canonical square, two divergence witnesses; replacement removals in `Gossip.lean`; node-announcement canonicalisation remains open | `Gossip.lean`, new `GossipStoreEpochTargets.lean` |
