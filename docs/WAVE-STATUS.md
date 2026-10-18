# Wave status — repair branch

**Repository:** `/home/ubuntu/ln-lean-repair`
**Branch:** `repair/integrated`
**Gate HEAD:** this proof-wave 6 checkpoint; the status commit records the exact
hash. Proof-wave 5 code was `6389baa`; wave 6 launched from `201a0a0`.
**Catalog:** 48 proved / 0 statementOnly / 0 unresolved / 73 targets.
**Toolchain:** `leanprover/lean4:v4.35.0`

This file describes the repair branch. Older wave tables are retained as
history; they are not a claim about the current tree. Current open work is in
`docs/OPEN-ISSUES.md`; the operating protocol is `docs/SWARM-LOOP.md`.

## Current state

| Metric | Value |
|---|---|
| Lean files under `LnLean/` | **197** |
| Root imports in `LnLean.lean` | **195** (`LnLean.Proofs.All` and the `PhaseC2` aggregator are not root-imported) |
| Full build | **RC 0**, `Build completed successfully (218 jobs)` |
| Actual `sorry` lines | **0** (`grep -RInE '^[[:space:]]*sorry[[:space:]]*$' LnLean --include='*.lean'` → no matches, grep RC 1) |
| Proof files with the word `sorry` in prose | comments only, not proof terms |
| Catalog rows | **48** |
| Catalog `proved` | **48** |
| Catalog `statementOnly` | **0** |
| Catalog targets | **73** |
| Unresolved/planned targets | **0** |
| Vendor snapshot | **OK**, 119 files; `fetch-vendor.sh` tested |
| Anchors | **306 checked, 0 bad**, 2 unanchored rows |
| Generated obligation index | 160 proof files, 81 markers, 5512 declarations, 0 `sorry` sites |
| Axiom audit | 163 theorems; only `propext`, `Quot.sound`, `Classical.choice` |
| Conformance | 61 base + 16 framing + 9 boundary checks, 33 differential fixtures, 146 Lean references, 9/9 mutation controls, 3 declared model gaps |
| Public L1 pin | `Rob1Ham/btc-lean` `main@4f5c4f8` |
| Build dependency | `vendor/btc-lean-core` `f950806` |

The exact `sorry` result is **zero matching lines**. Prose mentions of
`sorry` in documentation are not `sorry` terms.

## Proof-wave 6 gate

- `lake build` — **RC 0**, 218 jobs.
- `check-catalog.py --audit` — **RC 0**, 48 proved, 0 statement-only,
  73 targets, 0 unresolved, 0 proved failures, 0 candidates, 7345
  declarations.
- `check-catalog.py --allow-planned` — **RC 0**, same counts with
  `planned=0`.
- `check.sh` — **RC 0**: `files=197 obligations=82 sorry_in_proofs=0`,
  `check: OK`.
- `check-final.py` — **RC 0**: 197 Lean files, 195 root imports, D=33 E=15
  F=15.
- `check-conformance.py` — **RC 0**: 61 base + 16 framing + 9 boundary
  checks, 33 differential fixtures, 146 Lean references, 9/9 mutation
  controls, deterministic fixture provenance verified.
- `verify-vendor.sh` — **RC 0**, 119 files.
- `verify-anchors.py` — **RC 0**, 306 anchors, 0 bad, 2 unanchored rows.
- `AxiomAudit` — **RC 0**, 163 audited theorems with the permitted classical
  axioms only.

**Proof-wave 6 gate: PASS.** Push is non-force to
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

## Wave 7 candidates

The remaining codeable gaps are: exact BIP 143 preimage equality to the
vendored `bip143MsgL`/`LnLean.Bitcoin.Sighash.encode`, the
`trimmedTotalSat`/`trimmedSat` naming decision and coordinated rename, live
rust-lightning fixture regeneration, folding `UpdateStep`/`DanceStep` into
`ProtocolEvent`, raw `applyGossip` refinement, and the computational-security
game foundation. Release decisions (`OPS-02`, `OPS-03`, vendor publication)
remain human-only.

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
Lightning verification. The concrete EC/transaction-validity bridge, full
consensus sighash equality, live differential conformance, commitment-dance
folding, raw gossip-store refinement, computational crypto, vendor
reproducibility, and release packaging remain open. See
`docs/OPEN-ISSUES.md`.
