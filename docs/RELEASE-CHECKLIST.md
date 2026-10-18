# Release checklist — ln-lean

**Status: NOT RELEASABLE.** This is a preparation checklist, not a release
approval. It records the current facts, the gates a maintainer must run, and the
decisions that are still open. It does **not** choose a license, a version, a
tag name, a merge strategy, or a tag signing method.

**Repository:** `/home/ubuntu/ln-lean-repair`
**Branch:** `repair/integrated`
**Lane base:** `47189fe` (`[STATUS] define wave 4 open-issue lanes`)
**Snapshot used for the original lane checks:** `f2123ef`; wave-4 integration
later added six Lean modules and new gate commands. The current tree is
**182 Lean files / 180 root imports / 188 build jobs / 61 catalog targets**;
re-run every gate row before tagging.
**Target release type:** a **model/proof-tree** release, not an implementation
release and not a complete verification of Lightning.

Evidence labels used below:

| Label | Meaning |
|---|---|
| **Verified** | Command was run while preparing this checklist at the snapshot above. |
| **Historical** | Result recorded in an earlier gate document; not re-run here. |
| **Not run** | Deliberately not executed in this lane. |
| **Blocked** | Cannot pass until a maintainer decision or external artifact exists. |

## Current snapshot

| Item | State | Evidence |
|---|---|---|
| Branch tip | wave-4 integration working tree (status commit records the hash) | `git rev-parse HEAD` |
| `origin/main` | `b891a59`; **61 commits behind** `HEAD`; `main` is an ancestor of `HEAD` | `git rev-list --count origin/main..HEAD` = 61; `git merge-base --is-ancestor origin/main HEAD` |
| Release tags | none | `git tag -l` empty; GitHub tags API empty |
| GitHub releases | none | GitHub releases API empty |
| `LICENSE` | **none** at repository root | `find` / `git ls-files` |
| Project version | **not declared** in `lakefile.lean` | `lake-manifest.json` `"version": "1.3.0"` is the Lake manifest schema version, not this project's version |
| Vendor snapshot | 119 files, checksums OK locally; **gitignored and not tracked** | `./scripts/verify-vendor.sh`; `git check-ignore vendor/btc-lean-core/lakefile.lean` |
| Vendor provenance | `vendor/btc-lean-core` at `f95080638ae571a3664f4f41b9b6f6b4cfa7c5eb`, **not present in public `btc-lean` history** | `refs/PINNED.md` |
| Catalog | 48 rows, 48 `proved`, 0 `statementOnly`, 0 unresolved, 0 proved failures | `python3 scripts/check-catalog.py --audit` — **Verified** |
| Source policy check | `files=182 obligations=82 sorry_in_proofs=0` | `./scripts/check.sh` — **Verified** |
| File/import check | 182 Lean files, 180 root imports, D=33 E=15 F=15 | `python3 scripts/check-final.py` — **Verified** |
| Vendor integrity | `OK (119 files)` | `./scripts/verify-vendor.sh` — **Verified** |
| Anchors | 299 anchors, 0 bad, 2 unanchored rows | `python3 scripts/verify-anchors.py` — **Verified** |
| Full build | **not run in this lane** (lane rule). Historical claim: 188 jobs, RC 0 at the wave-4 gate. | See build gate below |
| Public CI | 3 runs, all `success`; latest run #3 at `f2123ef`. The build job's `lake build` and `verify-vendor.sh` steps were **skipped**. | GitHub Actions API, run `39138200828` |

The working tree at the snapshot was clean except for the pre-existing untracked
`agents/status/REPAIR.status`. Other Wave-4 lanes may add unrelated changes in
the shared checkout while this checklist is being prepared; only the committed
release commit matters. A release must not be cut from a dirty tree, and all
gates must be rerun after integration at the exact tag commit.

## 1. Catalog gate

The catalog is a **model-level** claim: a `proved` row means the named
declaration exists and is sorry-free. It does not make the English sentence
unconditional. The scope caveats in `docs/THEOREM-INDEX.md`,
`docs/FINAL-STATUS.md`, and each lane report are part of the release claim.

- [ ] Run the strict audit and the planned-aware audit at the **exact release
      commit**, not at an earlier gate commit:

  ```sh
  python3 scripts/check-catalog.py --audit
  python3 scripts/check-catalog.py --allow-planned
  ```

- [ ] Require: 48 rows, 48 `proved`, 0 `statementOnly`, 0 unresolved,
      0 proved failures, 0 duplicate ids, 0 promotion candidates.
      **Verified at `f2123ef`:** `rows=48 proved=48 statementOnly=0 targets=61
      unresolved=0 proved_failures=0 duplicate_ids=0 candidates=0
      declarations=5942`. If integration deliberately changes the catalog,
      record the new expected counts and why; do not silently accept a
      different number.
- [ ] Reconcile every catalog target with `docs/THEOREM-INDEX.md` and
      `docs/TRACEABILITY.md`. Do not promote a row just because its name exists.
- [ ] Confirm the release notes repeat the catalogue caveats: conditional
      signing/key binding, finite collision admissions, per-sender HTLC ids,
      reachable-gossip scope, rich-vs-legacy commitment scope, and conditional
      liveness/reorg results.
- [ ] Do **not** describe the release as "Lightning verified", "consensus
      spendable", "conformance-tested", or "computationally secure". Those
      claims are blocked by `L1-01`, `L1-02`, `CR-01`, `CONF-01`, `MODEL-01`,
      and `SEC-01`, whether or not the catalog stays green.

## 2. Build gates

The full build is the only gate that compiles every module. Source checks are
not a substitute. **This lane did not run `lake build`.**

- [ ] Toolchain: `leanprover/lean4:v4.35.0` from `lean-toolchain`; `lake
      --version` must report Lean 4.35.0.
- [ ] Serialize the build under the shared lock:

  ```sh
  export PATH="$HOME/.elan/bin:$PATH"
  LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock lake build
  ```

- [ ] Require RC 0 and record the exact job count from the output. The docs
      claim `Build completed successfully (188 jobs)`; treat that as
      **historical** until the same command passes at the tag commit.
- [ ] Axiom audit:

  ```sh
  lake build LnLean.Proofs.PhaseC3.AxiomAudit
  ```

  Require RC 0 and only `propext`, `Quot.sound`, `Classical.choice`. Historical
  count: 101 audited theorems.
- [ ] Exact `sorry` scan (must print nothing):

  ```sh
  grep -RInE '^[[:space:]]*sorry[[:space:]]*$' LnLean --include='*.lean'
  ```

  **Verified at `f2123ef`:** no matching lines (`check.sh` reports
  `sorry_in_proofs=0`).
- [ ] Policy/source checks:

  ```sh
  ./scripts/check.sh
  python3 scripts/check-final.py
  ```

  **Verified at `f2123ef`:** `files=182 obligations=82 sorry_in_proofs=0`,
  `check: OK`; `lean files=182`, `root imports=180`, `check-final: OK`.
- [ ] Vendor integrity and anchors:

  ```sh
  ./scripts/verify-vendor.sh
  python3 scripts/verify-anchors.py
  ```

  **Verified at `f2123ef`:** `OK (119 files)`; `anchors=299 bad=0
  unanchored_rows=2`, `verify-anchors: OK`. The anchor check requires the
  pinned `refs/rust-lightning` checkout.
- [ ] `git diff --check` must be clean, and the release tree must contain no
      generated-file drift. If generated indexes are deliberately regenerated,
      rerun every gate afterwards.
- [ ] Confirm the build does not depend on `/home/ubuntu/btc-lean-public`,
      `refs/btc-lean`, or any other local-only path. The build dependency must
      remain `vendor/btc-lean-core` or the chosen replacement policy.

## 3. Vendor reproducibility (`OPS-01`)

**This is a hard release blocker and is not resolved.** `vendor/btc-lean-core`
is excluded by `.gitignore` (`vendor/`), its pin `f950806` is not in public
`btc-lean` history, and the public CI build job therefore skips the build.
A clean public checkout of the current tree cannot satisfy the `core` path
dependency declared in `lakefile.lean`, so `lake build` cannot proceed without
external provisioning.

A maintainer must choose one packaging policy (this checklist does not choose):

| Option | What it requires | Consequence |
|---|---|---|
| Commit a checksummed vendor snapshot | Track the 119 files (or an archive), keep `vendor/VENDOR-SHA256`, confirm redistribution rights, include the upstream license/provenance | Public checkout can build; repository grows; vendor edits become reviewable |
| Publish a separate vendor artifact | Versioned archive + `SHA256SUMS`, download/provision script, checksum verification in CI, documented pin | Public checkout needs a provisioning step; artifact hosting and retention must be maintained |
| Fetch a public ancestor | Bump the pin to a commit in public `btc-lean` history, adapt imports, refresh checksums and anchors, full rebuild | Requires a deliberate pin-bump project; the current snapshot lineage is not public |

- [ ] Record the chosen policy and its checksum/provenance record in the release
      notes and in `docs/OPEN-ISSUES.md` (`OPS-01`).
- [ ] Verify the pack procedure from a **clean clone**, not the working tree:

  ```sh
  rm -rf /tmp/ln-lean-release-check
  : "${TAG:?set TAG to the tag being verified}"
  git clone https://github.com/Rob1Ham/ln-lean.git /tmp/ln-lean-release-check
  cd /tmp/ln-lean-release-check
  git checkout "$TAG"
  test ! -e vendor/btc-lean-core/lakefile.lean   # current state
  python3 scripts/check-catalog.py --audit
  ./scripts/check.sh
  python3 scripts/check-final.py
  ```

  Then provision the vendor exactly as the chosen policy specifies and run the
  full build and `./scripts/verify-vendor.sh` in that clone.
- [ ] If the snapshot is redistributed, include the upstream `btc-lean` MIT
      license and Bitcoin Core notice, plus the provenance record. The snapshot
      itself contains **no `LICENSE` file**; see `docs/LICENSE-DECISION.md`.
- [ ] Do not remove the CI skip gate until the clean-clone build path actually
      runs and `verify-vendor.sh` passes in CI.

## 4. License decision (`OPS-02`)

**This is a hard release blocker and is not resolved.** There is no `LICENSE`,
`COPYING`, `NOTICE`, or `AUTHORS` file at the repository root. GitHub reports
the repository license as `None`. A public release with no license leaves
downstream users without a clear grant.

- [ ] Read `docs/LICENSE-DECISION.md` and record a maintainer decision. This
      checklist does not select MIT, Apache-2.0, dual licensing, or any other
      option.
- [ ] Confirm the copyright holder/authorized licensor. Commit authorship in
      this tree is automation identities (`LN Fleet`, `LN Integrator`, etc.);
      there is no CLA, DCO, or contributor policy in the tree.
- [ ] Add the chosen `LICENSE` file(s) at the root and track them with Git.
- [ ] Add third-party notices/attribution:
  - `btc-lean` is MIT at the public pin, with portions derived from Bitcoin
    Core (MIT); preserve the notice if vendored code is distributed.
  - `rust-lightning` is dual MIT OR Apache-2.0 and is reference-only in this
    tree; preserve notices if any text/code is copied.
  - The BOLTs are CC-BY-4.0, not a software license; attribution is required
    for quoted/adapted spec text. Add the CC-BY attribution to the notice or
    release documentation.
- [ ] Update `README.md`'s release-status paragraph and any package metadata
      only after the decision. Do not leave "no LICENSE" text in a tagged
      release.
- [ ] Record the decision, date, and approver in the sign-off table below.

## 5. Tag / PR / merge path (`OPS-03`)

**This is a hard release blocker and is not resolved.** There is no tag and no
release. `origin/main` is at `b891a59`; `HEAD` is 61 commits ahead and `main`
is an ancestor, so a fast-forward is technically possible. The path below is a
sequence, not a decision on PR vs direct merge or merge-commit vs fast-forward.

Maintainer choices required:

1. PR to `main` (gives review and CI evidence) vs direct fast-forward.
2. Merge commit vs fast-forward merge.
3. Tag name and version scheme.
4. Signed tag (`git tag -s`, requires a configured signing key) vs annotated
   tag (`git tag -a`).
5. Whether the tag is cut on `main`'s merge commit or on `repair/integrated`
   (the release commit and the checked commit must be the same object).

Suggested safe sequence — **do not run until the choices above are recorded**:

```sh
# Replace the placeholders with the maintainer-approved values.
: "${TAG:?set TAG to the approved tag name}"
: "${RELEASE_NOTES:?set RELEASE_NOTES to the approved notes file}"

# 0. Freeze the exact release commit.
git switch repair/integrated
git status --porcelain=v1          # must be empty
git fetch origin

# 1. Push the reviewed branch non-force.
git push origin repair/integrated

# 2. Open a PR and require the source-level CI job to pass.
gh pr create --base main --head repair/integrated \
  --title "Release $TAG: model/proof-tree snapshot" \
  --body-file "$RELEASE_NOTES"

# 3. Merge without rewriting main (choose one; maintainer decision).
#    Fast-forward:
git switch main && git pull --ff-only origin main
git merge --ff-only repair/integrated
#    Or merge commit:
# git merge --no-ff repair/integrated

# 4. Tag the exact merge commit (choose signed or annotated).
git tag -s "$TAG" -m "ln-lean $TAG model/proof-tree release"
# git tag -a "$TAG" -m "ln-lean $TAG model/proof-tree release"

# 5. Push the tag and publish the release.
git push origin main
git push origin "$TAG"
gh release create "$TAG" --title "ln-lean $TAG" --notes-file "$RELEASE_NOTES"
```

If `gh` is not installed, open the PR and create the release in the GitHub web
UI; use the same base/head branches, tag, and notes file.

- [ ] Confirm the tag resolves to the exact commit whose gate output is
      recorded: `git rev-parse <TAG>^{commit}` equals the recorded hash.
- [ ] Confirm `git tag -v <TAG>` (signed) or `git cat-file -t <TAG>` (annotated)
      matches the chosen method.
- [ ] Never force-push `main` and never move a published tag.
- [ ] Release notes must state that this is a model/proof tree, list the open
      issues and scope caveats, and link the license and this checklist.

## 6. Public CI status — truth note

The workflow at `f2123ef` was `.github/workflows/ci.yml`; wave-4 integration
adds the pinned `fetch-vendor.sh` path and the conformance step. Its
**source-gates** job is a real signal; its **build** job is skip-gated on the
vendor snapshot. A concurrent Wave-4 vendor lane is changing this workflow in
the shared checkout; re-check the integrated workflow and rerun CI before
carrying any of the statements below into release notes.

Observed from the GitHub Actions API at `f2123ef` (run #3, id `39138200828`,
<https://github.com/Rob1Ham/ln-lean/actions/runs/39138200828>):

- Workflow conclusion: `success`.
- `Source-level gates`: all executed steps succeeded — catalog audit,
  `check.sh`, `check-final.py`, pinned rust-lightning fetch, anchor check.
- `Full build (requires the vendored btc-lean snapshot)`: job conclusion
  `success`, but **`Install pinned Lean toolchain and run lake build` and
  `Verify vendored snapshot checksums` were skipped**. The vendor-presence step
  found no snapshot and emitted a warning.

Therefore:

- **Green CI does not prove that the tree builds.** Do not cite the build job
  as build evidence until `OPS-01` is resolved and those steps execute.
- The source-level job passes on a clean checkout without the vendor snapshot;
  it was independently reproduced from a `git archive` export of `HEAD` for the
  catalog, `check.sh`, and `check-final.py` checks in this lane.
- The anchor job needs the network fetch of the pinned `rust-lightning` commit;
  it succeeded in CI run #3.
- There is no CI badge in `README.md`. Do not add one that implies a full build.
- After a release, re-check the workflow run on `main` and record its URL and
  job-step status in the release notes. If the build steps are still skipped,
  say so explicitly. This section describes run #3 against the workflow
  committed at `f2123ef`; an integrated vendor-policy change must be verified
  fresh, not assumed from this note.

## 7. Documentation sync

- [ ] Update `README.md` counts and release status **after** integration, using
      the actual numbers at the release commit, not the wave-3 numbers
      (currently 182 Lean files, 180 root imports, 48 catalog rows).
- [ ] Update `docs/FINAL-STATUS.md` and `docs/WAVE-STATUS.md` with the release
      commit/tag and current gate evidence. Remove stale "Gate HEAD" references
      if they no longer identify the tagged commit.
- [ ] Update `docs/OPEN-ISSUES.md`: close `OPS-01`, `OPS-02`, and `OPS-03` only
      when their evidence exists; keep `L1-01`/`L1-02` and the other model gaps
      open with accurate scope notes.
- [ ] Reconcile `docs/THEOREM-INDEX.md` and `docs/TRACEABILITY.md` with the
      catalog, anchor count, and module list at the tag commit.
- [ ] Regenerate `docs/OBLIGATIONS-GENERATED.md` and
      `agents/status/obligations.json` only as a deliberate integration step
      (`python3 scripts/collect-obligations.py` rewrites them); commit the
      result and rerun the full gate.
- [ ] Check links and stale hashes:

  ```sh
  grep -RInE '0c99c92|47189fe|no `LICENSE`|no release tag|skip-gated' \
    README.md docs agents/reports/swarm4
  git diff --check
  git diff --check origin/main..HEAD
  ```

  Stale text is acceptable only where it is explicitly historical.
- [ ] Confirm the release notes and docs do not claim conformance, consensus
      spendability, computational security, or full Lightning verification.

## 8. Artifact and versioning

- [ ] Choose the release version. There is currently **no project version** in
      `lakefile.lean`; `lake-manifest.json` `"version": "1.3.0"` is the Lake
      manifest format version and must not be presented as the release number.
- [ ] Choose the artifact shape:
  - **Source-only** (GitHub auto-generated source archive at the tag) — requires
    no vendor redistribution; the archive excludes `vendor/` because it is
    gitignored, so the build prerequisite must be documented.
  - **Source + provisioned vendor artifact** — requires the OPS-01 policy,
    checksums, and the vendor license/provenance.
  - **Built `.olean`/binary artifact** — additionally requires the exact Lean
    toolchain, vendor rights, and a reproducible build attestation. Do not
    publish one while public CI cannot run the build.
- [ ] Verify the source archive contains: `LICENSE` (chosen), `README.md`,
      `docs/`, `LnLean/`, `lakefile.lean`, `lean-toolchain`, `lake-manifest.json`,
      and no `.lake/`, `refs/`, `vendor/` (unless deliberately packaged),
      secrets, or local absolute paths.
- [ ] Publish `SHA256SUMS` for any manually attached artifact and sign it if
      the project has a signing process.
- [ ] Record the artifact hashes, tag object hash, commit hash, toolchain
      version, and CI run URL in the release notes.

## 9. Rollback

Rollback is a maintainer action. Do not rewrite `main` history.

| Situation | Safe action |
|---|---|
| Gate fails before tagging | Fix or drop the change; do not tag. Reset only the uncommitted working tree or the unpushed branch with maintainer approval. |
| Tag created locally, not pushed | `git tag -d "$TAG"` locally; no public effect. |
| Tag pushed, no release published | Ask the maintainer before `git push origin ":refs/tags/$TAG"`; record why. Avoid moving a tag that others may have fetched. |
| Release published with a bad tag | Prefer a new patch tag (`$NEXT_TAG`, for example the next patch version) containing the revert/fix. Do not move the old tag. Edit the old release notes to mark it superseded; delete the release only with maintainer approval. |
| Bad merge on `main` | `git revert -m 1 "$MERGE_COMMIT"` (or revert the offending commits), open a PR, rerun the full gate, merge normally. Never force-push `main`. |
| Vendor artifact compromised or checksum mismatch | Remove/withdraw the artifact, publish an advisory, rotate checksums, rebuild from the pinned source, and re-release under a new tag. |
| Documentation/version error after release | Revert the doc commit and cut a new patch tag; do not silently rewrite release notes that users may have cited. |

- [ ] Record the rollback owner and the communication channel before tagging.
- [ ] Keep the previous release/tag available until the new one has passed a
      clean-clone build (once OPS-01 permits it).

## 10. Exact pre-tag runbook

Run from the repository root on the exact commit to be tagged. This is the
maintainer runbook; it was **not** executed as a full build by this lane.

```sh
set -euo pipefail
export PATH="$HOME/.elan/bin:$PATH"
cd /home/ubuntu/ln-lean-repair

# 1. Exact commit and clean tree.
#    Check out the branch whose tip will be tagged (main after merge, or the
#    release branch if the maintainer chose that path).
: "${RELEASE_BRANCH:?set RELEASE_BRANCH to main or the release branch}"
git switch "$RELEASE_BRANCH"
git fetch origin
git status --porcelain=v1
git rev-parse HEAD
git log -1 --format='%H %s'

# 2. Catalog.
python3 scripts/check-catalog.py --audit
python3 scripts/check-catalog.py --allow-planned

# 3. Full build, serialized.
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock lake build

# 4. Axioms and policy.
lake build LnLean.Proofs.PhaseC3.AxiomAudit
./scripts/check.sh
python3 scripts/check-final.py

# 5. Exact sorry scan: must print nothing.
grep -RInE '^[[:space:]]*sorry[[:space:]]*$' LnLean --include='*.lean' || true

# 6. Vendor and anchors.
./scripts/verify-vendor.sh
python3 scripts/verify-anchors.py

# 7. License and release metadata.
test -f LICENSE
git ls-files --error-unmatch LICENSE
: "${TAG:?set TAG to the approved tag name}"
: "${VERSION:?set VERSION to the approved release version}"
printf 'release version: %s\ntag: %s\n' "$VERSION" "$TAG"

# 8. Record evidence, then tag the exact commit.
git rev-parse HEAD
git tag -l "$TAG"          # must be empty before tagging
```

Do not proceed to tag if any command fails, if `git status --porcelain` is not
empty, if `LICENSE` is absent, if the vendor policy is still undecided, or if
the public CI build steps are still skipped without an explicit release caveat.

## Release blockers

| Blocker | Type | Blocks | Resolution owner |
|---|---|---|---|
| `OPS-01` — vendor snapshot is gitignored and not reproducible from public history | Hard release blocker | Clean public build and honest build CI | Maintainer chooses packaging policy |
| `OPS-02` — no `LICENSE` | Hard release blocker | Any public grant of rights | Maintainer chooses license; see `docs/LICENSE-DECISION.md` |
| `OPS-03` — no tag, `main` behind | Hard release blocker | Tagged release and release notes | Maintainer chooses PR/merge/tag path |
| Vendor snapshot has no `LICENSE`; public `btc-lean` is MIT but the `f950806` lineage is not public | Legal/provenance blocker if the snapshot or a build artifact is redistributed | Redistribution of vendor code or compiled artifacts | Maintainer confirms grant and adds notices |
| BOLT text is CC-BY-4.0 and no project-level attribution file exists | Compliance blocker for quoted spec text | Publishing docs/release notes with BOLT excerpts | Maintainer adds attribution |
| No project version or release notes | Packaging blocker | Artifact naming and release publication | Maintainer chooses version and notes |
| Public CI build steps skipped | Claim blocker | Any statement that CI proves the build | Resolved only by `OPS-01` |
| `L1-01`, `L1-02`, `MODEL-01` | Claim blocker | Any "spendable script" or interpreter claim | Out of scope for this release; disclose |
| `CR-01`, `SEC-01` | Claim blocker | Any computational-security or full-verification claim | Disclose as open research |
| `CONF-01` | Claim blocker | Any conformance claim | Disclose as open |
| `PR-02`, `CH-01`, `CH-02`, `HT-01`, `RT-01` | Model-gap disclosure | Any "complete wire/commitment/HTLC/gossip" claim | Disclose in release notes |

**Release decision:** not approved. The earliest credible release is a
model/proof-tree release that explicitly discloses the open issues, has a
tracked license, and either has a reproducible vendor path or documents that the
build requires external provisioning. A release that implies a full build from
public CI, consensus spendability, conformance, or full Lightning verification
would be false.

## Sign-off

| Decision / gate | Value | Owner | Date | Evidence |
|---|---|---|---|---|
| License choice | _maintainer decision required_ | | | `docs/LICENSE-DECISION.md` |
| Copyright holder / authority confirmed | _pending_ | | | |
| Vendor packaging policy (`OPS-01`) | _pending_ | | | |
| PR/merge strategy (`OPS-03`) | _pending_ | | | |
| Tag name / version | _pending_ | | | |
| Tag signing method | _pending_ | | | |
| Full build at release commit | _not run in this lane_ | | | 188-job wave-4 historical claim only |
| Public CI build actually executed | _pending `OPS-01`_ | | | Run #3 skipped build steps |
| Release notes scope review | _pending_ | | | Must repeat open-issue caveats |
