# S3-RELEASE — README, roadmap, and CI release hygiene

**Verdict:** documentation now matches the committed proof-wave 2 state at
`repair/integrated` HEAD `4c627a7`. No Lean code, scripts, status files, or
proof modules were modified by this lane. No git index/ref operations were
performed.

- Repository: `/home/ubuntu/ln-lean-repair`
- Branch: `repair/integrated` (HEAD `4c627a7`)
- Scope: `README.md`, `docs/ROADMAP.md`, new `.github/workflows/ci.yml`, this report.
- Pre-existing untracked `agents/status/REPAIR.status` was left untouched.

## Files changed

| File | Change |
|---|---|
| `README.md` | Rewritten status, 11-row obligation table, layout, build, checks, references, release note |
| `docs/ROADMAP.md` | Counts and per-step status updated to 37/11; technical plan preserved |
| `.github/workflows/ci.yml` | New CI workflow (source gates + vendor-gated full build) |
| `agents/reports/swarm3/S3-RELEASE.md` | This report |

`git diff --check -- README.md docs/ROADMAP.md` → RC 0.

## Verified proof-wave 2 snapshot

The worktree was dirty from a concurrent lane while this report was written
(see "Contradictions"). To verify the committed state rather than the moving
worktree, I exported HEAD with `git archive HEAD` to
`/tmp/opencode/s3-pristine` and ran the gates there.

| Check | Result |
|---|---|
| Lean files under `LnLean/` | 166 (36 model + 130 proof) |
| Root imports in `LnLean.lean` | 164 |
| `./scripts/check.sh` | RC 0 — `files=166 obligations=81 sorry_in_proofs=0` |
| `python3 scripts/check-final.py` | RC 0 — `D=33 E=15 F=15 total=63`, 166 files, 164 imports |
| `python3 scripts/check-catalog.py --allow-planned` | RC 0 — `rows=48 proved=37 statementOnly=11 targets=51 unresolved=0 planned=1 proved_failures=0 duplicate_ids=0 candidates=3` |
| `python3 scripts/verify-anchors.py` | RC 0 — `anchors=298 bad=0 unanchored_rows=2` (using pinned `refs/rust-lightning`) |
| Actual `sorry` lines | 0 (`grep -RInE '^[[:space:]]*sorry[[:space:]]*$' LnLean --include='*.lean'` → RC 1, no lines) |
| Strict catalog `--audit` | RC 1 by design — only `LN-CH-003` is an unresolved planned target |

The full 172-job build was not rerun in this lane (build work belongs to the
proof lanes and the gate owner). The README reports the recorded gate result
from `docs/FINAL-STATUS.md` / `docs/WAVE-STATUS.md`: RC 0, 172 jobs.

## README stale claims fixed

| Old README claim | Current claim |
|---|---|
| 132 Lean files, `69 base + 33 D + 15 E + 15 F` | 166 files: 36 model + 130 proof (33 WaveD, 15 WaveE, 15 ModelHardening, 17 PhaseC2, 12 PhaseC3) |
| 95 obligation markers | 81 markers as counted by `check.sh`; 48 catalog rows with 51 targets |
| 15 documented open sites | 0 actual `sorry` sites; 11 `statement-only` catalog rows |
| `export PATH=/dev/shm/btc/elan/toolchains/...` | `lean-toolchain` pins `leanprover/lean4:v4.35.0`; optional `$HOME/.elan/bin` PATH note |
| `cd /home/ubuntu/ln-lean-final` | `cd /home/ubuntu/ln-lean-repair` |
| `check-final.py ... 132/132 imports` | 166 files, 164 root imports (2 aggregators excluded) |
| No catalog checker in Checks | `check-catalog.py --allow-planned` documented with 48/37/11/1 output |
| `docs/FINAL-STATUS.md` described as D/E/F final gate | described as proof-wave 2 gate and open rows |

The "**This is scaffolding, not a completed proof.**" warning is retained, now
followed by the explicit 37/11 breakdown. The 11 remaining rows are listed in
a table with their current targets and why each is still `statement-only`
(1 planned, 3 exact-but-retained, 7 definition/predicate-only).

A `## Release status` section records that no `LICENSE` file exists, licensing
is a maintainer decision, and no release tag has been cut. No license was
chosen and no `LICENSE` file was added.

## ROADMAP updates

`docs/ROADMAP.md` keeps its Phase-C technical plan, mathlib/L1-bridge/
cryptographic sections, dependency order, and exit criteria. Changes are
status-only:

* Header: 29 `proved` / 19 `statement-only` → **37 / 11**, plus the 1 planned
  (`LN-CH-003`) and 3 exact-but-retained rows.
* Mathlib section: added a status note that the fallback (no mathlib) was
  used and that `LN-CH-002`, `LN-HT-003`, `LN-PM-005`, `LN-RT-005`, and
  `LN-SEC-002`/`003` are now proved; `LN-CH-003` remains planned.
* L1 bridge section: added a note distinguishing a model-level `proved` row
  from an established L1 script bridge; listed which bridge rows remain
  `statement-only`.
* Step 1: `LN-CH-002` and `LN-SEC-002` proved; `LN-CH-003` planned;
  `LN-CH-005` still `statement-only`; `LN-CH-006` proved.
* Step 2: `LN-HT-003` proved; `LN-HT-004` exact theorem retained because it
  assumes the uniqueness it claims; `LN-PR-004` still `statement-only`.
* Step 3: `LN-SEC-005`/`006` proved at model level with economic/watchtower
  hypotheses explicit.
* Step 4: `LN-RT-005` and `LN-RT-002`/`003`/`004` proved; `LN-RT-006`
  remains `statement-only`.
* Step 5: `LN-PR-005` and `LN-SEC-003` proved; eventual delivery after GST
  remains future work; `LN-SEC-005`/`006` keep their economic caveats.
* Exit criteria: added the current 37/11 position and stated the criteria are
  the exit bar, not a claim that it is met.

## CI workflow

New file: `.github/workflows/ci.yml`.

* Triggers: `push` and `pull_request` for `main` and `repair/**`, plus
  `workflow_dispatch`.
* Permissions: `contents: read`; concurrency group cancels superseded runs.
* `source-gates` job (required signal):
  1. checkout;
  2. Python 3.12;
  3. `python3 scripts/check-catalog.py --allow-planned`;
  4. `./scripts/check.sh`;
  5. `python3 scripts/check-final.py`;
  6. fetch `refs/rust-lightning` at pinned
     `fe4900930c6bd5786ec4203274d7cf312776a5a6` (the same pin as
     `refs/PINNED.md`);
  7. `python3 scripts/verify-anchors.py`.
* `build` job: checks for `vendor/btc-lean-core/lakefile.lean`; if present,
  runs `leanprover/lean-action@v1` with `auto-config: false`, `build: true`,
  `use-mathlib-cache: false`, then `./scripts/verify-vendor.sh`. If absent,
  the job emits an explicit warning and skips the build/checksum steps.

`vendor/btc-lean-core` is deliberately gitignored (only
`vendor/VENDOR-SHA256` is tracked), and the vendor commit `f950806` is not in
public `btc-lean` history, so a clean public checkout cannot run the full
build. The build job is therefore skip-gated rather than silently failing;
this is called out in the README and under release blockers below.

### Validation performed

| Validation | Result |
|---|---|
| `python3 -c 'yaml.safe_load(...)'` (PyYAML 6.0.1) | parse OK; keys `name`, `on`, `permissions`, `concurrency`, `env`, `jobs`; jobs `build`, `source-gates` |
| `actionlint -no-color .github/workflows/ci.yml` (v1.7.12) | RC 0, no findings |
| Pinned anchor fetch by SHA in a scratch clone | RC 0, checked out `fe490093...` |
| Source-gate commands on pristine HEAD | RC 0 (table above) |

**CI has not run on GitHub and is not claimed to pass.** Only YAML/schema
syntax, the anchor-fetch command, and the underlying gate scripts were
validated locally. No full CI build was run.

## Remaining release blockers

1. **License (human decision).** There is no `LICENSE` file. No license was
   chosen or added by this lane; a maintainer must select one and add the file.
2. **Release tag.** `git tag` is empty. No version/tag has been cut; the tag
   name and signing policy are human decisions.
3. **PR/merge decision.** `repair/integrated` is pushed to
   `origin/repair/integrated`; merging into `main` (and whether to open a PR)
   is a human decision. `origin/main` was recorded as untouched.
4. **Vendor snapshot is not in version control.** The full 172-job build and
   `verify-vendor.sh` cannot run from a clean public checkout. Vendoring the
   snapshot, publishing it as an artifact/submodule, or accepting a
   private-provisioning step is required before CI can provide the build gate.
5. **Concurrent proof-wave work in the worktree.** At report time another lane
   had added untracked proof modules and modified model modules (details
   below). Those files must be committed or discarded, the expected counts in
   `check-final.py` and the generated indexes refreshed, and the gate rerun
   before release.
6. **Generated documentation lags.** `docs/ANCHORS-GENERATED.md` still says
   132 Lean files scanned; `docs/OBLIGATIONS-GENERATED.md` says 80 wave-B
   markers while `check.sh` counts 81 obligation markers. Regenerate with the
   normal generator owner (not this lane; `collect-obligations.py` was not
   run).
7. **Branch protection / required checks.** The new workflow must be enabled
   in repository settings and, if desired, marked required. Not verifiable
   from this checkout.
8. **CI status.** No GitHub Actions run exists yet, so no green-CI claim can
   be attached to the tag/PR.

## Contradictions and anomalies found

1. **Worktree drift during this lane.** HEAD was `4c627a7` and initially had
   only the pre-existing `agents/status/REPAIR.status` untracked. While this
   lane ran, another agent modified `LnLean/Bitcoin/Seam.lean` and
   `LnLean/Channel/HTLC.lean` and added at least these proof modules (the list
   was still growing when this report was written): `ProtocolSigningTargets`,
   `ProtocolCoverageTargets`, `Wire/TLVTargets`, `Bitcoin/ToLocalScriptTargets`,
   `Bitcoin/WeightTargets`, `Channel/FeeTargets`, `Routing/GossipTargets`, and
   `Security/ReorgTargets` (mtimes 14:40–14:45). In the dirty worktree,
   `check-final.py` fails (`expected 166, found 168+`) and
   `verify-anchors.py` reported 299 anchors at first check (and more after the
   later file appeared). README/ROADMAP intentionally describe committed HEAD
   `4c627a7`, not this transient state. The merging lane must re-run and update
   the gate after the concurrent proof work lands.
2. **Gate HEAD vs branch tip.** `docs/FINAL-STATUS.md` and
   `docs/WAVE-STATUS.md` name gate HEAD `2e74367` (the proof commit), while the
   branch tip is `4c627a7` (the status commit). This is not a state
   contradiction, but a reader comparing the two SHAs may think the docs are
   stale. The README avoids pinning a SHA and points to those docs.
3. **Marker count mismatch.** `check.sh` reports `obligations=81`;
   `docs/WAVE-STATUS.md` and `docs/OBLIGATIONS-GENERATED.md` say "80 markers"
   (the generated index counts proof-file markers, while `check.sh` scans all
   `LnLean` modules). The README uses the `check.sh` figure in its check
   example.
4. **Generated anchor index stale.** `docs/ANCHORS-GENERATED.md` reports 132
   scanned files, while the tree has 166 and `verify-anchors.py` checks 298
   anchors. It was not regenerated here because generated-doc ownership and
   `collect-obligations.py` are outside this lane.
5. **Strict vs planned-aware catalog mode.** `--audit` exits 1 solely because
   `LN-CH-003` has no declaration; `--allow-planned` exits 0 with
   `planned=1`. The README states this explicitly so a red strict run is not
   mistaken for a broken proof.
6. **README's old "15 documented open sites" did not match the tree.** The
   committed tree has zero `sorry` terms and 11 `statement-only` rows; the old
   figure described the pre-repair final tree.

## Constraints honored

* No edits to `LnLean/`, `scripts/`, `agents/status/`, `Obligations.lean`,
  `Traceability.lean`, or any proof module.
* No `LICENSE` file added and no license selected.
* No `git add`, `commit`, `push`, `checkout`, or `reset`; no files deleted.
* `collect-obligations.py` was not run.
* Pre-existing `agents/status/REPAIR.status` preserved.
