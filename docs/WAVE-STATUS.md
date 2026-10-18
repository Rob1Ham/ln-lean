# Wave status — repair branch

**Repository:** `/home/ubuntu/ln-lean-repair`
**Branch:** `repair/integrated`
**Gate HEAD:** `26ced90` (`[PROOF] integrate proof-wave 4 bridge and
conformance lanes`). Status commits may advance the branch tip. Proof-wave 3
code was `0c99c92`; wave 4 launched from `47189fe`.
**Catalog:** 48 proved / 0 statementOnly / 0 unresolved / 61 targets.
**Toolchain:** `leanprover/lean4:v4.35.0`

This file describes the repair branch. Older wave tables are retained as
history; they are not a claim about the current tree. Current open work is in
`docs/OPEN-ISSUES.md`; the operating protocol is `docs/SWARM-LOOP.md`.

## Current state

| Metric | Value |
|---|---|
| Lean files under `LnLean/` | **182** |
| Root imports in `LnLean.lean` | **180** (`LnLean.Proofs.All` and the `PhaseC2` aggregator are not root-imported) |
| Full build | **RC 0**, `Build completed successfully (188 jobs)` |
| Actual `sorry` lines | **0** (`grep -RInE '^[[:space:]]*sorry[[:space:]]*$' LnLean --include='*.lean'` → no matches, grep RC 1) |
| Proof files with the word `sorry` in prose | comments only, not proof terms |
| Catalog rows | **48** |
| Catalog `proved` | **48** |
| Catalog `statementOnly` | **0** |
| Catalog targets | **61** |
| Unresolved/planned targets | **0** |
| Vendor snapshot | **OK**, 119 files; `fetch-vendor.sh` tested |
| Anchors | **299 checked, 0 bad**, 2 unanchored rows |
| Generated obligation index | 146 proof files, 81 markers, 4834 declarations, 0 `sorry` sites |
| Axiom audit | 101 theorems; only `propext`, `Quot.sound`, `Classical.choice` |
| Conformance | 61 BigSize/TLV vectors; 86 Lean checks; 2 declared model gaps |
| Public L1 pin | `Rob1Ham/btc-lean` `main@4f5c4f8` |
| Build dependency | `vendor/btc-lean-core` `f950806` |

The exact `sorry` result is **zero matching lines**. Prose mentions of
`sorry` in documentation are not `sorry` terms.

## Proof-wave 4 gate

- `lake build` — **RC 0**, 188 jobs.
- `check-catalog.py --audit` — **RC 0**, 48 proved, 0 statement-only,
  61 targets, 0 unresolved, 0 proved failures, 0 candidates.
- `check-catalog.py --allow-planned` — **RC 0**, same counts with
  `planned=0`.
- `check.sh` — **RC 0**: `files=182 obligations=82 sorry_in_proofs=0`,
  `check: OK`.
- `check-final.py` — **RC 0**: 182 Lean files, 180 root imports, D=33 E=15
  F=15.
- `check-conformance.py` — **RC 0**: 61 vectors, 26 BOLT Appendix A anchors,
  85 Lean theorem references, 2 declared gaps.
- `verify-vendor.sh` — **RC 0**, 119 files.
- `verify-anchors.py` — **RC 0**, 299 anchors, 0 bad, 2 unanchored rows.
- `AxiomAudit` — **RC 0**, 101 audited theorems with the permitted classical
  axioms only.

**Proof-wave 4 gate: PASS.** Push is non-force to
`origin/repair/integrated`; the exact commit is recorded in
`docs/FINAL-STATUS.md`.

## Wave 4 lanes

| Lane | Issue / row | Result |
|---|---|---|
| `S4-L1-SPEND` | `L1-01`, `L1-02` | Explicit interpreter-law/stack model; serializer equals seam templates; conditional 2-of-2 funding and both `to_local` branch spend theorems; rejection/limit cases; vendored real interpreter found but not yet imported |
| `S4-VENDOR-CI` | `OPS-01` | `fetch-vendor.sh` verifies/provisions only pinned local/URL/exact-git input; 43-test suite; CI source gates unconditional; clean-checkout build remains an explicit skip unless configured |
| `S4-CONFORMANCE` | `CONF-01` | 61 BigSize/TLV vectors, checker with 3 mutation controls, 86 Lean `decide` theorems; vector conformance only, 2 declared model gaps |
| `S4-PR-WIRE` | `PR-02` | Additive `CommitmentSignedFull` with commitment number/fee/digest/per-HTLC entries; `ProducedFrom` and conditional exact coverage; legacy no-decoder negatives retained |
| `S4-HTLC-GLOBAL` | `HT-01` | Direction-tagged `HTLCTag` namespace with reachable global uniqueness/Nodup; original cross-direction duplicate maps to distinct tags |
| `S4-FEE-DUST` | `CH-01`, `CH-02` | Second-stage fee from feerate, exact dust threshold, trimming partition, `legacyOutputs` permutation under zero dust, BOLT 3 accounting; core gross/net patch recorded |
| `S4-GOSSIP-ATTR` | `RT-01` | `admitGossipAttributed` + reachable graph-edge key attribution; endpoint form needs explicit consistency; raw `applyGossip` caveat retained |
| `S4-RELEASE` | `OPS-02`, `OPS-03` | Release checklist and neutral MIT/Apache-2.0/dual-license matrix; no license, tag, merge, or push |

Wave 4 added six modules and strengthened `LN-HT-004` and `LN-PR-004`; it did
not add catalog rows or weaken the 48/0/0 gate.

## Historical waves

| Wave | Scope | Result |
|---|---|---|
| Repair lanes `R01`–`R10`, `M01`, `M02`, `K01`, `L01`, `CCR01` | Repair false sites, crypto interface, catalog checker, public pin, elaboration blowup | Green; counterexamples retained |
| Proof-wave 1 (`W01`, `R01`, `O01`, `H01`, `C01`, `P01`, `M01`, `S01`) | Exact targets for wire, routing/onion, payments, security/liveness | 11 rows promoted; HTLC/commitment gaps narrowed |
| Proof-wave 2 (`SEC05-ECON`, `CH02-WF`, `HT-LEDGER`, `PR-WRAPPERS`, `CR-RETARGET`) | Penalty economics, commitment nonnegativity, HTLC partition, protocol wrappers, crypto retargets | 8 rows promoted; 11 remained |
| Proof-wave 3 (12 lanes) | Final catalog retargets and release hygiene | **11 rows promoted; 48/0/0** |
| Proof-wave 4 (8 lanes) | L1 spend bridge, vendor/CI, conformance, wire, global ids, fee/dust, gossip attribution, release | **6 modules; 61 targets; 188-job gate** |

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
Lightning verification. The L1 consensus interpreter/sighash bridge,
computational crypto, wire completeness, differential conformance, vendor
reproducibility, and release packaging remain open. See
`docs/OPEN-ISSUES.md`.
