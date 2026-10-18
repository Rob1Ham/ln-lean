# Wave status — repair branch

**Repository:** `/home/ubuntu/ln-lean-repair`
**Branch:** `repair/integrated`
**Gate HEAD:** `6389baa` (`[PROOF] integrate proof-wave 5 bridge and\nconformance lanes`). Status commits may advance the branch tip. Proof-wave 4\ncode was `26ced90`; wave 5 launched from `11a460c`.
**Catalog:** 48 proved / 0 statementOnly / 0 unresolved / 67 targets.
**Toolchain:** `leanprover/lean4:v4.35.0`

This file describes the repair branch. Older wave tables are retained as
history; they are not a claim about the current tree. Current open work is in
`docs/OPEN-ISSUES.md`; the operating protocol is `docs/SWARM-LOOP.md`.

## Current state

| Metric | Value |
|---|---|
| Lean files under `LnLean/` | **190** |
| Root imports in `LnLean.lean` | **188** (`LnLean.Proofs.All` and the `PhaseC2` aggregator are not root-imported) |
| Full build | **RC 0**, `Build completed successfully (204 jobs)` |
| Actual `sorry` lines | **0** (`grep -RInE '^[[:space:]]*sorry[[:space:]]*$' LnLean --include='*.lean'` → no matches, grep RC 1) |
| Proof files with the word `sorry` in prose | comments only, not proof terms |
| Catalog rows | **48** |
| Catalog `proved` | **48** |
| Catalog `statementOnly` | **0** |
| Catalog targets | **67** |
| Unresolved/planned targets | **0** |
| Vendor snapshot | **OK**, 119 files; `fetch-vendor.sh` tested |
| Anchors | **305 checked, 0 bad**, 2 unanchored rows |
| Generated obligation index | 154 proof files, 81 markers, 5235 declarations, 0 `sorry` sites |
| Axiom audit | 133 theorems; only `propext`, `Quot.sound`, `Classical.choice` |
| Conformance | 61 base + 16 framing checks, 33 differential fixtures, 146 Lean references, 7/7 mutation controls, 3 declared model gaps |
| Public L1 pin | `Rob1Ham/btc-lean` `main@4f5c4f8` |
| Build dependency | `vendor/btc-lean-core` `f950806` |

The exact `sorry` result is **zero matching lines**. Prose mentions of
`sorry` in documentation are not `sorry` terms.

## Proof-wave 5 gate

- `lake build` — **RC 0**, 204 jobs.
- `check-catalog.py --audit` — **RC 0**, 48 proved, 0 statement-only,
  67 targets, 0 unresolved, 0 proved failures, 0 candidates, 6898
  declarations.
- `check-catalog.py --allow-planned` — **RC 0**, same counts with
  `planned=0`.
- `check.sh` — **RC 0**: `files=190 obligations=82 sorry_in_proofs=0`,
  `check: OK`.
- `check-final.py` — **RC 0**: 190 Lean files, 188 root imports, D=33 E=15
  F=15.
- `check-conformance.py` — **RC 0**: 61 base + 16 framing checks, 33
  differential fixtures, 146 Lean theorem references, 7/7 mutation controls.
- `verify-vendor.sh` — **RC 0**, 119 files.
- `verify-anchors.py` — **RC 0**, 305 anchors, 0 bad, 2 unanchored rows.
- `AxiomAudit` — **RC 0**, 133 audited theorems with the permitted classical
  axioms only.

**Proof-wave 5 gate: PASS.** Push is non-force to
`origin/repair/integrated`; the exact commit is recorded in
`docs/FINAL-STATUS.md`.

## Wave 5 lanes

| Lane | Issue / row | Result |
|---|---|---|
| `S5-L1-INTERP` | `L1-01`, `L1-02`, `L1-07`, `L1-08` | Vendored interpreter bridge: serializer equals vendor `serializeOpcodes`, exact wire parse, funding 2-of-2 and delayed `to_local` execute through `verifyWitnessProgram`; BIP 143/locktime/revocation boundaries explicit |
| `S5-CH-GROSSNET` | `CH-01`, `CH-02`, `CH-03`, `CH-04` | Net/gross commitment path, arbitrary-dust canonical permutation, effective-fee/conservation accounting; literal `Types.lean` fields remain a patch |
| `S5-PR-SIGHASH` | `PR-01`, `PR-02`, `PR-05`, `PR-06` | Structural BOLT 3 serializer, `SighashProduces.coverage`, honest signer, joint funding/commitment contract; bit-exact and view-binding gaps explicit |
| `S5-CONF-DIFF` | `CONF-01`, `CONF-02`, `CONF-03` | 16 framing cases, 33 pinned rust-lightning fixtures, 7 mutation controls, 146 Lean references; online regeneration and production framing remain open |
| `S5-MODEL-STEP` | `MODEL-02`, `MODEL-03` | Additive `UpdateStep` add/fail/fulfill layer, affordability guard, ledger/reserve preservation, E37 refinement; commitment dance separate |
| `S5-L1-FUNDING` | `L1-03`, `L1-05` | Funding hash link constructed from the handshake, ordered P2WSH output, handshake hash-link theorem; finite C1 admission retained |
| `S5-GOSSIP-ATTR2` | `RT-01`, `RT-02` | Direction-keyed attribution, `NodeId → PubKey` consistency, canonical dedup under explicit invariants; raw-store and derivation gaps retained |
| `S5-SEC-LIMITS` | `CR-01`, `SEC-01` | `docs/CRYPTO-LIMITS.md` plus a precise deterministic game/reduction interface; no computational reduction claimed |

Wave 5 added eight proof modules, strengthened five catalog rows to 67
resolved targets, extended the audit to 133 headline theorems, and did not add
catalog rows or weaken the 48/0/0 gate.

## Wave 6 lanes (launched)

Wave 6 launched from `86c1733` and attacks the residual wave-5 gaps: BIP 143 sighash/locktime, the
revocation branch, literal gross/net `Types.lean` fields, bit-exact BOLT 3
preimages, digest-to-view binding, commitment dance, gossip invariant
derivation, and live transport/fixture conformance. See
`agents/swarm/WAVE-6.md` for the lane/owned-file table; integration is pending.

## Historical waves

| Wave | Scope | Result |
|---|---|---|
| Repair lanes `R01`–`R10`, `M01`, `M02`, `K01`, `L01`, `CCR01` | Repair false sites, crypto interface, catalog checker, public pin, elaboration blowup | Green; counterexamples retained |
| Proof-wave 1 (`W01`, `R01`, `O01`, `H01`, `C01`, `P01`, `M01`, `S01`) | Exact targets for wire, routing/onion, payments, security/liveness | 11 rows promoted; HTLC/commitment gaps narrowed |
| Proof-wave 2 (`SEC05-ECON`, `CH02-WF`, `HT-LEDGER`, `PR-WRAPPERS`, `CR-RETARGET`) | Penalty economics, commitment nonnegativity, HTLC partition, protocol wrappers, crypto retargets | 8 rows promoted; 11 remained |
| Proof-wave 3 (12 lanes) | Final catalog retargets and release hygiene | **11 rows promoted; 48/0/0** |
| Proof-wave 4 (8 lanes) | L1 spend bridge, vendor/CI, conformance, wire, global ids, fee/dust, gossip attribution, release | **6 modules; 61 targets; 188-job gate** |
| Proof-wave 5 (8 lanes) | Vendored L1 bridge, gross/net, sighash, differential conformance, update step, funding link, gossip consistency, crypto limits | **8 modules; 67 targets; 204-job gate** |

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
Lightning verification. The L1 consensus sighash/revocation bridge,
computational crypto, bit-exact wire/sighash encoding, commitment dance,
gossip invariant derivation, live differential conformance, vendor
reproducibility, and release packaging remain open. See
`docs/OPEN-ISSUES.md`.
