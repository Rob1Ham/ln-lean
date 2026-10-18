# Final integrator report

## Tree

- Branch: `final/integrated`
- Base: `a9f8d87` (Wave-C)
- Worktree: `/home/ubuntu/ln-lean-final`
- Lean files: **132** (69 base + 33 D + 15 E + 15 F)
- Root imports: **132**
- Selection manifest: `agents/status/FINAL-SELECTION.md`
- Source hashes: `agents/status/final-import.sha256`

## Gate evidence

```text
python3 scripts/check-final.py                 -> OK (63 selected, 132 files, 132 imports)
lake build                                     -> RC 0, 140 jobs
./scripts/verify-vendor.sh                     -> OK (119 files)
python3 scripts/verify-anchors.py              -> 288 anchors, 0 bad, 2 unanchored rows
./scripts/check.sh                             -> OK
python3 scripts/collect-obligations.py          -> 95 markers, 48 catalog rows, 15 sorries
python3 scripts/collect-anchors.py             -> 132 files with anchors, 710 rows
```

## Selection decisions

- D14 is kept and E14 is excluded: both declare
  `LnLean.Channel.Reserve.bounds` with incompatible statements.
- E37 is kept over D37 (no `sorry`, sharp affordability/ledger equivalence).
- E39 is kept over D39 for the guarded capacity result; the D39 store-level
  admission invariant is recorded as a follow-up, not merged.
- E40 is kept with one marked `sorry` for the false unconditional
  signature-length claim; its conditional/iff companion is proved.
- D41–D48 and E45/E48 are annex/refinement modules, not second closures of
  their catalog IDs.
- F10 is excluded from the final tree.  It remains on `wave-f/16` with a
  repaired marker; the premise mismatch is documented in `agents/reports/F10.md`.

## Honest status

This is still a scaffold.  The final tree has **15 real `sorry` sites**:

- 5 pre-existing Wave-C sites in `FundingProps`, `ReserveProps`, and
  `GossipProps`;
- 1 in `WaveE/E40`;
- 9 in `F03`, `F04`, `F05`, `F06`, `F07`, `F09`, `F13`, `F14`, `F15`.

Every site is a false or underspecified unconditional statement retained next
to an `-- OBLIGATION:` marker, with a proved conditional/counterexample
companion.  The catalog remains **13/48 proved, 35 statement-only**.

**Crypto interface caveat:** `PrimitiveModel` carries both `sha256_size` and
`sha256_preimageResistant`, which are jointly inconsistent
(`preimageResistant_vacuous`).  Theorems over `M : PrimitiveModel` are
vacuous; byte-decomposition results are unaffected.  Do not present the
SHA-256-shaped headlines as a real hash bridge.

Do not describe the following as closed:

- `LN-L1-004`: the model's `toLocalScript` is a flat seam fragment, not the
  full BOLT 3 two-branch witness script.
- `LN-PR-004`: both D20/E20 are negative/conditional.
- `LN-SEC-003`: the named catalog declaration does not exist.
- `LN-SEC-005`: D34's at-stake field is post-fee; the uneconomical-penalty
  counterexample is withdrawn.
- `LN-CH-101`: no `Step.update_add_htlc` constructor; E37 models the
  affordability arithmetic on successor functions.
- `LN-GOSSIP-002`: the raw `applyGossip` path remains unguarded; E39 proves
  the guarded store result.

## Remote

No Wave-D/E/F/G or final branch has been pushed.  `main` remains `b891a59`;
`wave-c/235` is 20 commits ahead of `origin/wave-c/235`.  Push only with a
valid write credential, non-force, and after a final `git status`/gate rerun.

## Reproduce

```sh
cd /home/ubuntu/ln-lean-final
export PATH=/dev/shm/btc/elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
python3 scripts/check-final.py
flock -w 1800 /tmp/ln-build.lock lake build
./scripts/verify-vendor.sh
python3 scripts/verify-anchors.py
./scripts/check.sh
```
