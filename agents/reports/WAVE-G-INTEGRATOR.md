# Wave-G integrator report

## Result

- Branch: `wave-g/audit`
- Reports: **32/32**
- Gate: `python3 scripts/check-wave-g.py --strict` → OK
- Read-only: no Lean edits, no builds, no git writes by auditors
- Selection: one whole-file D/E version per target, plus the strong F
  model-hardening modules

## Cross-cutting findings

- **One hard Lean collision:** `LnLean.Channel.Reserve.bounds` is declared in
  both `D14.lean:404` and `E14.lean:579` with incompatible statements.  Keep
  D14 and exclude E14 physically; `regen-root.sh` imports every file under
  `LnLean/`.
- **F10 is excluded:** its marker is inline after `sorry`, so `check.py` cannot
  collect it, and its premise has a Msat/Nat mismatch.  The other 15 F modules
  are kept.
- **D41–D48 are annex modules:** they share catalog IDs with earlier targets
  but have distinct namespaces/declarations.  They are kept as refinements,
  not as second closures.
- **Lane gate scripts were not relocatable.**  The E/F gates initially verified
  the D worktree because `regen-root.sh`, `check.sh`, `verify-vendor.sh`, and
  the collectors/indexers hard-coded `/home/ubuntu/ln-lean`.  The scripts now
  resolve the root from their own location; E was rerun green on its own tree.
- **Stale artifacts:** `D40` had an olean older than its source; the final gate
  rebuilds every selected module.  `D37Alt`/`E03Alt` are removed.
- **Sorry inventory:** 5 base Wave-C + 2 D + 2 E + 10 F real sorries.  The
  selected tree has 5 base + 1 E40 + 9 F = 15 real sorries; every selected
  claim is conditional, a counterexample, or explicitly open.  Do not describe
  the catalog as closed.
- **Current remote:** no Wave-D/E/F/G branch has been pushed.  `wave-c/235` is
  20 commits ahead of `origin/wave-c/235`; `main` remains `b891a59`.

## Selection manifest

### Primary slots 01–48

| Slot | Keep | Slot | Keep |
|---:|---|---:|---|
| 01 | `WaveD/D01` | 25 | `WaveD/D25` |
| 02 | `WaveD/D02` | 26 | `WaveE/E26` |
| 03 | `WaveD/D03` | 27 | `WaveD/D27` |
| 04 | `WaveD/D04` | 28 | `WaveD/D28` |
| 05 | `WaveD/D05` | 29 | `WaveD/D29` |
| 06 | `WaveE/E06` | 30 | `WaveD/D30` |
| 07 | `WaveD/D07` | 31 | `WaveE/E31` |
| 08 | `WaveD/D08` | 32 | `WaveD/D32` |
| 09 | `WaveE/E09` | 33 | `WaveE/E33` |
| 10 | `WaveD/D10` | 34 | `WaveD/D34` (open/erratum) |
| 11 | `WaveD/D11` | 35 | `WaveE/E35` |
| 12 | `WaveD/D12` | 36 | `WaveD/D36` |
| 13 | `WaveD/D13` | 37 | `WaveE/E37` |
| 14 | `WaveD/D14` | 38 | `WaveD/D38` |
| 15 | `WaveD/D15` | 39 | `WaveE/E39` |
| 16 | `WaveD/D16` | 40 | `WaveE/E40` |
| 17 | `WaveD/D17` | 41 | `WaveD/D41` (annex 01) |
| 18 | `WaveD/D18` | 42 | `WaveD/D42` (annex 03) |
| 19 | `WaveE/E19` | 43 | `WaveD/D43` (annex 03) |
| 20 | `WaveE/E20` (negative) | 44 | `WaveD/D44` (annex 04) |
| 21 | `WaveD/D21` | 45 | `WaveE/E45` (annex 11) |
| 22 | `WaveE/E22` | 46 | `WaveD/D46` (annex 11) |
| 23 | `WaveD/D23` | 47 | `WaveD/D47` (annex 12) |
| 24 | `WaveE/E24` | 48 | `WaveE/E48` (annex 12) |

Counts: **33 D, 15 E, 15 F = 63 selected files**.

### Model hardening

Keep `F01`–`F09` and `F11`–`F16` (15).  Exclude `F10`.

## Known open/low-confidence items

- `D34`: its `d34AtStake` is post-fee, so the advertised uneconomical-penalty
  counterexample is withdrawn; slot 34 remains open.  G17 recommends a
  corrected E34 instead, but no corrected file exists yet.
- `D20`/`E20`: both are negative/conditional for `LN-PR-004`; no positive
  closure of the remote-commitment claim.
- `D03`/`D42`/`D43`: the catalog `toLocalScript` is the flat seam template, not
  the full BOLT 3 two-branch witness script.  Do not mark `LN-L1-004` closed.
- `E33`: catalog declaration `LnLean.Proofs.Security.safety_async` does not
  exist; the async model is the best available artifact, not a closure.
- `E37`: no `Channel.State.Step.update_add_htlc` constructor; the affordability
  arithmetic is a successor-function model.
- `E39`: guarded store admission is proved, but the raw `applyGossip` remains
  unguarded; keep the distinction explicit.
- `E40`: false unconditional signature-length claim retained with one marked
  `sorry`; conditional/necessary-and-sufficient companion proved.

## Final-tree rule

Copy only the 63 selected whole files to their original paths.  Start from a
fresh `a9f8d87` worktree, copy the base 69 modules plus selected files, do not
merge proof bodies, do not copy `.lake` or host-local symlinks, and regenerate
`LnLean.lean` with the root-relative `scripts/regen-root.sh`.  Expected:
132 Lean files and 132 imports.
