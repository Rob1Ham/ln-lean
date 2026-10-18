# Wave status — repair branch

**Repository:** `/home/ubuntu/ln-lean-repair`
**Branch:** `repair/integrated`
**Gate HEAD:** `b48d041` (`[PROOF] integrate proof-wave 7 sequence, preimage,
consumer, fold, and key lanes`). Status commits may advance the branch tip.
Proof-wave 6 code was `0a3a5fb`; wave 7 launched from `3180581`.
**Catalog:** 48 proved / 0 statementOnly / 0 unresolved / 79 targets.
**Toolchain:** `leanprover/lean4:v4.35.0`

This file describes the repair branch. Older wave tables are retained as
history; they are not a claim about the current tree. Current open work is in
`docs/OPEN-ISSUES.md`; the operating protocol is `docs/SWARM-LOOP.md`.

## Current state

| Metric | Value |
|---|---|
| Lean files under `LnLean/` | **204** |
| Root imports in `LnLean.lean` | **202** (`LnLean.Proofs.All` and the `PhaseC2` aggregator are not root-imported) |
| Full build | **RC 0**, `Build completed successfully (233 jobs)` |
| Actual `sorry` lines | **0** (`grep -RInE '^[[:space:]]*sorry[[:space:]]*$' LnLean --include='*.lean'` → no matches, grep RC 1) |
| Proof files with the word `sorry` in prose | comments only, not proof terms |
| Catalog rows | **48** |
| Catalog `proved` | **48** |
| Catalog `statementOnly` | **0** |
| Catalog targets | **79** |
| Unresolved/planned targets | **0** |
| Vendor snapshot | **OK**, 119 files; `fetch-vendor.sh` tested |
| Anchors | **306 checked, 0 bad**, 2 unanchored rows |
| Generated obligation index | 166 proof files, 81 markers, 5761 declarations, 0 `sorry` sites |
| Axiom audit | 194 theorems; only `propext`, `Quot.sound`, `Classical.choice` |
| Conformance | 61 base + 16 framing + 9 boundary checks, 33 differential fixtures, 146 Lean references, 9/9 mutation controls, 3 declared model gaps; live 26 BigSize + 3 TLV + 4 wire |
| Public L1 pin | `Rob1Ham/btc-lean` `main@4f5c4f8` |
| Build dependency | `vendor/btc-lean-core` `f950806` |

The exact `sorry` result is **zero matching lines**. Prose mentions of
`sorry` in documentation are not `sorry` terms.

## Proof-wave 7 gate

- `lake build` — **RC 0**, 233 jobs.
- `check-catalog.py --audit` — **RC 0**, 48 proved, 0 statement-only,
  79 targets, 0 unresolved, 0 proved failures, 0 candidates, 7707
  declarations.
- `check-catalog.py --allow-planned` — **RC 0**, same counts with
  `planned=0`.
- `check.sh` — **RC 0**: `files=204 obligations=82 sorry_in_proofs=0`,
  `check: OK`.
- `check-final.py` — **RC 0**: 204 Lean files, 202 root imports, D=33 E=15
  F=15.
- `check-conformance.py` — **RC 0**: 61 base + 16 framing + 9 boundary
  checks, 33 differential fixtures, 146 Lean references, 9/9 mutation
  controls, deterministic fixture provenance verified, live transcript
  `3dd7a98f…` with 26 BigSize + 3 TLV + 4 wire live rows.
- `verify-vendor.sh` — **RC 0**, 119 files.
- `verify-anchors.py` — **RC 0**, 306 anchors, 0 bad, 2 unanchored rows.
- `AxiomAudit` — **RC 0**, 194 audited theorems with the permitted classical
  axioms only.

**Proof-wave 7 gate: PASS.** Push is non-force to
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

## Wave 8 lanes

Wave 8 launched 48 lanes from `50d78ed`. **43 Lean modules** and the three
artifact lanes H46–H48 are integrated; **H04** produced no module in the
worktree and **H08** did not build, so both are recorded as dropped rather than
carried as false green claims. The full gate is **286 Lake jobs, RC 0**, with
**247 Lean files**, **245 root imports**, **48/48 catalog rows proved**, **79
targets**, **204 audited headline theorems**, and zero actual `sorry`.

| Lane group | Issues | Result |
|---|---|---|
| `H01`, `H02`, `H03`, `H05`, `H06`, `H31`, `H32` | `L1-02`, `L1-07` | Unconditional `txCheckerFor (some amount) = realCheckerOf` equality; delayed/revocation branches at `txCheckerFor`; exact `csv < 32768` boundary and `MINIMALDATA` policy split; full-script composition guard remains open |
| `H29`, `H30`, `H31` | `L1-01`, `L1-07` | Concrete `verifyImpl` interface and funding 2-of-2 checker instantiation; positive EC witness remains open |
| `H07`, `H09`, `H11`, `H12`, `H37` | `PR-05`, `PR-02` | HTLC BIP 143 preimage/digest equality, wire serialization domain, conditional wire-view binding, and exact 65533/65535 framing boundary; scriptCode synthesis (H08) dropped |
| `H13`, `H14`, `H15`, `H16`, `H17`, `H18`, `H19` | `L1-03`, `PR-01` | BOLT 2 type-32 `open_channel` mandatory payload fixed at **319 bytes** (not 313), encode/decode round-trip, field projections; `accept_channel` 270-byte payload; `Messages.lean` patch remains unapplied |
| `H20`, `H21`, `H22` | `PR-01` | Accept payload carried through the handshake extension; registration + PoP contract and attribution under `KeyBinding`; PoP game remains open |
| `H23`, `H24`, `H25`, `H26`, `H27`, `H28` | `CH-01`, `CH-02`, `PR-02` | Commitment/tx view adapters, transaction view, consumer boundary, downstream accounting, and the construction-site coverage-loss counterexample |
| `H33` | `L1-04` | **Closed**: witness-inclusive commitment weight is `1116 + 172*k`; `1124 + 172*k` is the fee basis, the extra 8 WU is `count_tx_out`, not missing witness bytes |
| `H34` | `L1-05` | **Closed on its recorded boundary**: C1 is refuted for 71-byte script injectivity; a domain-separated commitment binds under the retained finite pair admission |
| `H35`, `H36`, `H38` | `CONF-01` | Additional conformance/decoder/TLV boundary targets; finite-vector scope retained |
| `H39`, `H40`, `H41`, `H42` | `RT-01`, `RT-02` | Epoch store, sequence projection square, supersession/rotation preservation, and raw boundary-extension impossibility |
| `H43` | `NET-01` | Explicit adversarial schedule/fairness model with eventual-delivery and eventual-inclusion instances; unconditional liveness still open |
| `H44` | `SEC-01`, `CR-01` | Lossless event bound, event-cover accounting, negligible-add closure, and sharp separations; no reduction/game claimed |
| `H45` | `L1-06` | Reorg safety with explicit common-tip/bounded-depth hypotheses; concrete reorg preservation |
| `H46`–`H48` | release/artifact | Vendor artifact digest verifier, clean-checkout dry run, and release/PR decision support; H46 intentionally flags the OPS-04 absolute symlink |

H46’s strict vendor check still fails on the absolute symlink
`vendor/btc-lean-core/btc-lean-core`; it is not wired into CI. The ordinary
`verify-vendor.sh` gate is green for the 119-file manifest.

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
| Proof-wave 8 (48 lanes) | Per-input L1 checker, HTLC preimage/wire, 319-byte `open_channel`, accept/PoP, commitment sites, anchor/script-commitment, epoch gossip, liveness, security arithmetic, reorg, release artifacts | **43 files; 79 targets; 204 audited; 286-job gate; H04/H08 dropped** |

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
