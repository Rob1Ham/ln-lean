# ln-lean — final project plan from the current state

Status snapshot: 2026-10-18.  This plan covers the remaining D/E/F/G work,
the final combined tree, full verification, and the first remote push.

## Status update — integrated

Phases 0–6 are complete on `final/integrated`:

- Wave D: `wave-d/48` at `c07b216`, 48/48 modules/reports, gate green.
- Wave E: `wave-e/48` at `636e191`, 48/48 modules/reports, gate green.
- Wave F: `wave-f/16` at `387b45e`, 16/16 modules/reports, gate green.
- Wave G: `wave-g/audit` at `d181f9c`, 32/32 reports, gate green.
- Final tree: 132 Lean files, 63 selected whole files, 140-job build RC 0,
  vendor/anchors/policy/index gates green.
- The D37 recursion failure was resolved by the original agent; `D37Alt` was
  discarded.  E03 used the canonical module.
- Phase 7 (remote push) remains pending; no D/E/F/G/final branch has been
  pushed.  `main` is still `b891a59`.

See `agents/reports/FINAL-INTEGRATOR.md` and
`agents/status/FINAL-SELECTION.md` for the final evidence.

## 1. Initial state (superseded)

### Remote truth

- Remote: `https://github.com/Rob1Ham/ln-lean.git`
- `origin/main` = `b891a59` (local `main` is identical)
- `origin/wave-c/235` = `7084bb3`
- Local `wave-c/235` = `a9f8d87`, **20 commits ahead**, not pushed
- `origin/phase-c` exists; the other box's `phase-c` worktree is isolated and
  must not be edited or force-pushed
- `wave-d/48`, `wave-e/48`, `wave-f/16`, and `wave-g/audit` have **never been
  pushed** and have no upstream branch

### Local lanes

| Lane | Worktree | Local head | Content state |
|---|---|---|---|
| Wave C | `/home/ubuntu/ln-lean` (`wave-c/235`) | `a9f8d87` | 20/25 closed; 5 documented open obligations |
| Wave D | `/home/ubuntu/ln-lean` (`wave-d/48`) | `fa249a7` + uncommitted D outputs | 48/48 modules; final reports pending |
| Wave E | `/home/ubuntu/ln-lean-wavee` (`wave-e/48`) | `20b5679` + uncommitted E outputs | 48/48 modules; final reports pending |
| Wave F | `/home/ubuntu/ln-lean-wavef` (`wave-f/16`) | `d863c80` + uncommitted F outputs | 16/16 modules; 7 reports pending |
| Wave G | `/home/ubuntu/ln-lean-audit` (`wave-g/audit`) | `4b4c3e2` + reports | 32 audit agents running |
| Other box | `/home/ubuntu/ln-lean-phasec` (`phase-c`) | `eeaaf57` | read-only; do not touch |

### Known preflight issue (resolved)

- The canonical `D37.lean` initially failed its exact build with
  `maximum recursion depth has been reached`; the original D37 agent recovered
  it, and the final canonical module builds RC 0 with one documented `sorry`.
- `D37Alt` was discarded.  E03 used the canonical module.
- Final selection uses E37 (no `sorry`) for slot 37; D37 remains on the D
  branch as an alternate artifact.

### Hard rules

- Bitcoin L1 proofs in `vendor/btc-lean-core` are read-only.
- No model edits during D/E/F/G integration.
- `sorry` only under `LnLean/Proofs/`, adjacent to an `-- OBLIGATION:` marker.
- No force-push; never rewrite `main` or the other box's history.
- One whole-file version per target in the final tree.
- Every integration gate must finish with a green exact-module and full build.

## 2. Phase 0 — finish and freeze agent output

**Owner:** parent integrator.

1. Wait for D27, D37, E01, E03, E43, E47, and the seven F reports.
2. Run the non-building completers:
   ```sh
   cd /home/ubuntu/ln-lean && python3 scripts/check-wave-d.py
   cd /home/ubuntu/ln-lean-wavee && python3 scripts/check-wave-e.py
   cd /home/ubuntu/ln-lean-wavef && python3 scripts/check-wave-f.py
   cd /home/ubuntu/ln-lean-audit && python3 scripts/check-wave-g.py
   ```
3. Freeze writes: announce that no agent may edit a lane after its gate starts.
4. Record the final session map under `agents/status/`.

**Exit criteria:** 48/48 D and E modules, 16/16 F modules, and all required
reports present.  Missing reports are either delivered or recorded as a named
lane failure with a replacement version.

## 3. Phase 1 — Wave-D gate

**Owner:** parent.

```sh
cd /home/ubuntu/ln-lean
python3 scripts/check-wave-d.py --strict --build
./scripts/integrate-d.sh
```

`integrate-d.sh` performs the exact-module builds, root regeneration, full
build, `verify-vendor.sh`, `check.sh`, `verify-anchors.py`, and index
collection.

**Commit on `wave-d/48`:**

```sh
git add LnLean/Proofs/WaveD agents/reports/D*.md scripts agents docs
git commit -m '[LN-WAVE-D] integrate 48 targets, gate green'
```

**Exit criteria:** exact builds RC 0; full build RC 0; policy/anchor gates OK;
only documented `sorry` sites remain; no model or vendor edits.

## 4. Phase 2 — Wave-E gate

**Owner:** parent.

```sh
cd /home/ubuntu/ln-lean-wavee
python3 scripts/check-wave-e.py --strict --build
./scripts/integrate-e.sh
git add LnLean/Proofs/WaveE agents/reports/E*.md scripts agents docs
git commit -m '[LN-WAVE-E] integrate independent 48-target lane, gate green'
```

**Exit criteria:** same as Wave D.  E03 must use the canonical module, not
`E03Alt`, unless the audit explicitly selects the replacement.

## 5. Phase 3 — Wave-F gate

**Owner:** parent.

```sh
cd /home/ubuntu/ln-lean-wavef
python3 scripts/check-wave-f.py --strict --build
./scripts/integrate-f.sh
git add LnLean/Proofs/ModelHardening agents/reports/F*.md scripts agents docs
git commit -m '[LN-WAVE-F] integrate 16 model-hardening modules, gate green'
```

**Exit criteria:** 16/16 exact builds; every F `sorry` has a named marker and a
documented reason; full build green.

## 6. Phase 4 — Wave-G audit aggregation

**Owner:** parent + audit reviewers.

1. Run `python3 scripts/check-wave-g.py --strict`.
2. Collect G01–G24 verdicts into a 48-row selection matrix:
   `target | D status | E status | G recommendation | parent decision`.
3. Apply the ranking order:
   1. fewer real `sorry` sites;
   2. green exact-module build;
   3. faithful catalog/BOLT statement;
   4. fewer/weaker added hypotheses;
   5. stronger counterexample or model grounding.
4. Resolve G27 namespace-collision findings before copying files.
5. Record every override of a G recommendation with a one-line reason.

**Exit criteria:** one explicit decision per target; no unresolved namespace
collision; G31 remaining-obligation table accepted.

## 7. Phase 5 — final combined tree

**Branch:** `final/integrated` from `wave-c/235` tip `a9f8d87`.

```sh
cd /home/ubuntu/ln-lean
git worktree add -b final/integrated /home/ubuntu/ln-lean-final a9f8d87
```

For each target `NN`:

- if D wins, copy `LnLean/Proofs/WaveD/DNN.lean` and `agents/reports/DNN.md`;
- if E wins, copy `LnLean/Proofs/WaveE/ENN.lean` and `agents/reports/ENN.md`;
- if F wins, copy the relevant `LnLean/Proofs/ModelHardening/FNN.lean` and
  report;
- copy the G03/G19/G30 replacement only after promoting it to a canonical name.

Keep the original file path and namespace of the winning whole file.  Do not
merge proof bodies from two lanes into one module.

Then:

```sh
cd /home/ubuntu/ln-lean-final
./scripts/regen-root.sh
flock -w 1800 /tmp/ln-build.lock lake build
./scripts/verify-vendor.sh
./scripts/check.sh
python3 scripts/verify-anchors.py
python3 scripts/collect-obligations.py
python3 scripts/collect-anchors.py
```

**Exit criteria:** full 100+ job root build RC 0; no unexpected changed files;
all reports and the selection matrix present.

## 8. Phase 6 — documentation and release commit

Update:

- `docs/WAVE-STATUS.md` — final counts, remaining obligations, lane comparison;
- `agents/reports/INTEGRATOR.md` — final selection and gate evidence;
- `agents/reports/WAVE-D-INTEGRATOR.md`;
- `agents/reports/WAVE-E-INTEGRATOR.md`;
- `agents/reports/WAVE-F-INTEGRATOR.md`;
- `agents/reports/WAVE-G-INTEGRATOR.md`;
- `README.md` — proof status and reproduction commands.

Commit:

```sh
git add -A
git commit -m '[LN-FINAL] integrate strongest D/E/F proofs, green full gate'
```

Tag after the push is verified:

```sh
git tag -a v0.4.0 -m 'ln-lean D/E/F/G integrated proof release'
```

## 9. Phase 7 — remote push and PRs

### Credential prerequisite

A fresh GitHub PAT with **write** access to `Rob1Ham/ln-lean` is required.
Store it at `/tmp/opencode/gh-token` with mode `600`; never commit it.

Use a temporary `GIT_ASKPASS` script, push, then delete the helper and token.

### Push order (non-force only)

```sh
git push origin wave-c/235
git push origin wave-d/48
git push origin wave-e/48
git push origin wave-f/16
git push origin wave-g/audit
git push origin final/integrated
```

Do **not** push `main` directly if branch protection/PR review is expected.
Open PRs:

1. `wave-c/235` → `main`
2. `wave-d/48` → `main`
3. `wave-e/48` → `main`
4. `wave-f/16` → `final/integrated` or `main`
5. `wave-g/audit` → `final/integrated`
6. `final/integrated` → `main`

`main` must remain fast-forwardable from the pushed head.  If it has moved,
rebase only local feature branches; never force-push a shared branch.

### Exit criteria

- All six branches visible on `origin`.
- PRs open with green CI (if configured) or local gate evidence.
- `/tmp/opencode/gh-token` and the askpass helper deleted.
- `phase-c` and the other box's worktree untouched.

## 10. Risk register

| Risk | Mitigation |
|---|---|
| Missing agent report blocks strict gate | Promote the replacement alt or record a named failure and use the other lane's version. |
| Cross-lane duplicate declarations | Run G27 before copying; rename or select one whole file. |
| One lane's module fails root build despite exact-module pass | Build the final combined tree early; keep per-target fallback file. |
| Push token invalid | Do not retry credentials blindly; wait for a fresh PAT, then use temporary askpass. |
| `main` moved on remote | Rebase feature branches; never force-push shared history. |
| Other box's `phase-c` tree changes | Treat `/home/ubuntu/ln-lean-phasec` as read-only; never merge its branch without explicit review. |
| Build lock contention | Serialize all builds with `/tmp/ln-build.lock`; no parallel full builds. |

## 11. Definition of done

- [ ] 48/48 D and E modules, 16/16 F modules, 32/32 G reports.
- [ ] Every target has one selected whole-file version and a recorded reason.
- [ ] Exact-module builds green for every selected module.
- [ ] Full root build RC 0.
- [ ] `verify-vendor.sh`, `check.sh`, and `verify-anchors.py` green.
- [ ] Only documented `sorry` sites remain, each with an adjacent marker.
- [ ] `docs/WAVE-STATUS.md`, README, and all integrator reports updated.
- [ ] `final/integrated` committed and tagged.
- [ ] All lanes and final branch pushed non-force with PRs open.
- [ ] `main` history not rewritten; `phase-c` and the other box untouched.
