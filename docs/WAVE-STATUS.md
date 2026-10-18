# Wave status — repair branch

**Repository:** `/home/ubuntu/ln-lean-repair`
**Branch:** `repair/integrated`
**Gate HEAD:** this proof-wave 3 working tree; the status commit records the
exact hash.
**Catalog:** 48 proved / 0 statementOnly / 0 unresolved.
**Toolchain:** `leanprover/lean4:v4.35.0`

This file describes the repair branch. Older wave tables are retained as
history; they are not a claim about the current tree. Current open work is in
`docs/OPEN-ISSUES.md`; the operating protocol is `docs/SWARM-LOOP.md`.

## Current state

| Metric | Value |
|---|---|
| Lean files under `LnLean/` | **176** |
| Root imports in `LnLean.lean` | **174** (`LnLean.Proofs.All` and the `PhaseC2` aggregator are not root-imported) |
| Full build | **RC 0**, `Build completed successfully (182 jobs)` |
| Actual `sorry` lines | **0** (`grep -RInE '^[[:space:]]*sorry[[:space:]]*$' LnLean --include='*.lean'` → no matches, grep RC 1) |
| Proof files with the word `sorry` in prose | comments only, not proof terms |
| Catalog rows | **48** |
| Catalog `proved` | **48** |
| Catalog `statementOnly` | **0** |
| Unresolved/planned targets | **0** |
| Vendor snapshot | **OK**, 119 files |
| Anchors | **299 checked, 0 bad**, 2 unanchored rows |
| Generated obligation index | 140 proof files, 81 markers, 4506 declarations, 0 `sorry` sites |
| Axiom audit | 79 theorems; only `propext`, `Quot.sound`, `Classical.choice` |
| Public L1 pin | `Rob1Ham/btc-lean` `main@4f5c4f8` |
| Build dependency | `vendor/btc-lean-core` `f950806` |

The exact `sorry` result is **zero matching lines**. Prose mentions of
`sorry` in documentation are not `sorry` terms.

## Proof-wave 3 gate

- `lake build` — **RC 0**, 182 jobs.
- `check-catalog.py --audit` — **RC 0**, 48 proved, 0 statement-only,
  0 unresolved, 0 proved failures, 0 candidates.
- `check-catalog.py --allow-planned` — **RC 0**, same counts with
  `planned=0`.
- `check.sh` — **RC 0**: `files=176 obligations=82 sorry_in_proofs=0`,
  `check: OK`.
- `check-final.py` — **RC 0**: 176 Lean files, 174 root imports, D=33 E=15
  F=15.
- `verify-vendor.sh` — **RC 0**, 119 files.
- `verify-anchors.py` — **RC 0**, 299 anchors, 0 bad, 2 unanchored rows.
- `AxiomAudit` — **RC 0**, 79 audited theorems with the permitted classical
  axioms only.

**Proof-wave 3 gate: PASS.** Push is non-force to
`origin/repair/integrated`; the exact commit is recorded in
`docs/FINAL-STATUS.md`.

## Wave 3 lanes

| Lane | Issue / row | Result |
|---|---|---|
| `S3-HT004` | `LN-HT-004` | `HtlcBook` allocator/insertion model; per-sender `dir_id_unique`; global `id_unique_of_reachable_cross` under `CrossDisjoint`; cross-direction counterexample retained |
| `S3-PR003` | `LN-PR-003` | `funding_signed_signing_contract` under explicit `FundingSigningLaw` + `KeyBinding`; C3-only gap mechanized |
| `S3-PR004` | `LN-PR-004` | `commitment_signed_covers_exact_of_state` from per-output signed data + BOLT 3 value equations; wire-only negative results retained |
| `S3-CH003` | `LN-CH-003` | Rich `CommitmentTx` output model; `output_ordering` with script/dust/CLTV sort; D12 legacy refutation retained |
| `S3-L1001` | `LN-L1-001` | P2WSH 2-of-2 funding target under witness-script hash link + finite pair-level admission |
| `S3-L1003` | `LN-L1-003` | Bounded-reorg safety + explicit deep-reorg failure mode |
| `S3-L1004` | `LN-L1-004` | Full two-branch `toLocalScriptFull` carrying CSV delay and revocation key; output-level commitment |
| `S3-L1006` | `LN-L1-006` | BOLT 3 fee-basis weight target; exact 8 WU anchor serialization gap |
| `S3-CR005` | `LN-CR-005` | Exact TLV `WellFormed ↔ Pairwise (<)` and record-type uniqueness |
| `S3-CH005` | `LN-CH-005` | Exact fee-gate rejection iff insufficient / iff no checked signing |
| `S3-RT006` | `LN-RT-006` | Signature-gated reachable gossip graph only valid announcements; raw `applyGossip` unfiltered |
| `S3-RELEASE` | release hygiene | README/ROADMAP counts, CI workflow, license/tag/main decisions left to maintainer |

## Historical waves

| Wave | Scope | Result |
|---|---|---|
| Repair lanes `R01`–`R10`, `M01`, `M02`, `K01`, `L01`, `CCR01` | Repair false sites, crypto interface, catalog checker, public pin, elaboration blowup | Green; counterexamples retained |
| Proof-wave 1 (`W01`, `R01`, `O01`, `H01`, `C01`, `P01`, `M01`, `S01`) | Exact targets for wire, routing/onion, payments, security/liveness | 11 rows promoted; HTLC/commitment gaps narrowed |
| Proof-wave 2 (`SEC05-ECON`, `CH02-WF`, `HT-LEDGER`, `PR-WRAPPERS`, `CR-RETARGET`) | Penalty economics, commitment nonnegativity, HTLC partition, protocol wrappers, crypto retargets | 8 rows promoted; 11 remained |
| Proof-wave 3 (12 lanes) | Final catalog retargets and release hygiene | **11 rows promoted; 48/0/0** |

## Reproduce

```sh
export PATH=/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
cd /home/ubuntu/ln-lean-repair

LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock lake build
./scripts/check.sh
python3 scripts/check-final.py
python3 scripts/check-catalog.py --audit
python3 scripts/check-catalog.py --allow-planned
python3 scripts/verify-anchors.py
./scripts/verify-vendor.sh
```

## Not claimed

A green build and zero actual `sorry` terms do not make the model a full
Lightning verification. The L1 script interpreter, computational crypto,
wire completeness, conformance, vendor reproducibility, and release packaging
remain open. See `docs/OPEN-ISSUES.md`.
