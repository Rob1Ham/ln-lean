# S4-VENDOR-CI — vendor provisioning + honest CI build gate

**Lane:** `S4-VENDOR-CI` (`OPS-01`)
**Branch:** `repair/integrated`
**Base commit:** `47189fe` (`[STATUS] define wave 4 open-issue lanes`)
**Date:** 2026-10-18
**Status:** complete; `OPS-01` is **mitigated, not closed**. The build path is
reproducible *given an explicit checksummed input*; a clean public checkout
still has no build input because the pinned snapshot is not public.

## Deliverables

| File | Change |
|---|---|
| `scripts/fetch-vendor.sh` | **New.** Verify or provision the pinned snapshot from a local archive, an explicit URL + SHA-256, or the exact pinned git commit. Never follows a branch/tag tip. Always verifies against `vendor/VENDOR-SHA256`. Distinct exit code `3` means "no input supplied" (the CI skip gate). |
| `scripts/verify-vendor.sh` | **Edited.** Added an optional `SNAPSHOT_DIR` argument (default `vendor/btc-lean-core`) so a staged candidate can be verified with the identical 119-file checksum comparison. Output and exit codes for the default invocation are unchanged. Also moved the two `/tmp` scratch files to `mktemp` so parallel lanes cannot clobber each other. |
| `.github/workflows/ci.yml` | **Edited.** `source-gates` keeps all existing gates and always runs; it gains one shell-syntax/executable-bit check for the two vendor scripts. The build job now calls `fetch-vendor.sh --ci`: it provisions and verifies when a checksummed artifact is configured, otherwise records an explicit `available=false`, a `::warning`, and a job summary stating the full build did **not** run and why. `REQUIRE_VENDOR_BUILD=true` converts the skip into a failure. |
| `agents/reports/swarm4/S4-VENDOR-CI.md` | This report. |

No other files were edited. No git command that writes history was run. No full
`lake build` was run. `docs/OPEN-ISSUES.md` was not edited; the recommended
wording is at the end of this report.

## Why a public fetch path does not exist

The brief allowed either an available public/artifact URL or a documented
local/tarball input plus a clear failure. I checked the public sources first:

```
gh api repos/Rob1Ham/btc-lean/commits/f95080638ae571a3664f4f41b9b6f6b4cfa7c5eb
  -> HTTP 422: No commit found for SHA
gh api 'search/commits?q=f95080638ae571a3664f4f41b9b6f6b4cfa7c5eb'
  -> total_count = 0
git -C /home/ubuntu/btc-lean-public ls-remote --heads origin
  -> no wallet-peer branch (current heads: main, audit4-*, p0-* ... p5-*)
gh api repos/Rob1Ham/ln-lean/releases
  -> [] (no releases)
gh api repos/Rob1Ham/btc-lean/releases
  -> tag data-2026.10.17, assets assets.sha256, manifest.sha256,
     btc-lean-data-2026.10.17.tar.gz
```

The public `data-2026.10.17` tarball contains `spec/db/**` but **no**
`spec/core/**`, so it is not the build input. Content comparison of public
`main@4f5c4f8` (`spec/core`) against the tracked manifest:

```
manifest files 119  match 36  missing 3  different 80
```

So the pinned snapshot is a separate lineage, exactly as `refs/PINNED.md` says.
No URL can be embedded in the script without inventing one. The implementation
therefore supports an artifact URL for the day a maintainer publishes one, and
otherwise fails with explicit, tested instructions.

## `scripts/fetch-vendor.sh`

Modes (mutually exclusive):

| Mode | Input | Network | Pinning |
|---|---|---|---|
| `--check` (default) | existing `vendor/btc-lean-core` | none | 119-file manifest |
| `--from-tarball PATH` | local `.tar`/`.tar.gz` | none | 119-file manifest; archive SHA-256 optional |
| `--url URL` | published archive | HTTPS or `file://` | `--sha256` **required** + 119-file manifest |
| `--from-git` | exact `--commit` from `--repo` | git | commit must equal `f950806...`; refuses any other commit |
| `--ci` | env `VENDOR_ARTIFACT_URL` + `VENDOR_ARTIFACT_SHA256`, or `VENDOR_ARTIFACT_PATH` | as above | as above |

Safety properties:

* No branch, tag, `main`, `HEAD`, or "latest" is ever fetched. `--from-git`
  fetches `origin <exact SHA>` and rejects the result unless
  `rev-parse HEAD == f95080638ae571a3664f4f41b9b6f6b4cfa7c5eb`.
* `--url` without `--sha256` is a usage error (exit 2). `http://` is refused
  unless `--allow-http` (tests/local mirrors only).
* Archive members are validated before extraction: absolute paths, `..`
  components, symlinks, hardlinks, devices, and other non-regular members are
  rejected. Extraction uses Python 3.12 `tarfile.extractall(filter="data")`.
* Every candidate is `cd`-ed into and compared against `vendor/VENDOR-SHA256`
  with the same `find | sort -z | xargs -0 sha256sum | diff` logic as before,
  then verified again after installation.
* `--dest` defaults to `vendor/btc-lean-core`. Installation refuses to replace
  an existing tree without `--force`; `--force` moves the old tree to
  `DEST.bak-<UTC>-<pid>` (never deletes it). A failed post-install check moves
  the new tree to `DEST.failed-*` and restores the backup.
* `--dry-run` extracts and verifies in a temp directory, then exits without
  writing `DEST`.
* `.lake`/`.git` are stripped from archives before installation, so a build
  cache is never published or installed.
* Tarball layouts accepted: snapshot at archive root, a single wrapper
  directory, or a full `btc-lean` tree containing `spec/core/`.

Exit codes: `0` verified/provisioned, `1` integrity/unsafe-archive/refused
install, `2` usage/configuration, `3` unavailable with no input (CI skip).

`verify-vendor.sh` default behavior is preserved exactly:

```
$ ./scripts/verify-vendor.sh
verify-vendor: OK (119 files)
RC=0
```

The diff header now names `mktemp` files instead of fixed `/tmp/ln-vendor-now.*`;
the comparison, messages, and RC are unchanged.

## Exact commands and results

### Syntax and baseline

| Command | Result |
|---|---|
| `bash -n scripts/fetch-vendor.sh scripts/verify-vendor.sh` | RC 0, no output |
| `./scripts/verify-vendor.sh` | RC 0, `OK (119 files)` |
| `./scripts/fetch-vendor.sh` | RC 0, `OK: vendor/btc-lean-core matches vendor/VENDOR-SHA256 (119 files)` |
| `./scripts/fetch-vendor.sh --help` | RC 0 |
| `./scripts/fetch-vendor.sh --bogus` | RC 2 |
| `./scripts/fetch-vendor.sh --from-tarball` (no value) | RC 2 |
| `./scripts/fetch-vendor.sh --url file:///x` (no SHA) | RC 2 |
| `./scripts/check.sh` | RC 0, `files=181 obligations=82 sorry_in_proofs=0`, `check: OK` (181 includes other lanes' uncommitted files) |
| `python3 scripts/check-catalog.py --audit` | RC 0, `rows=48 proved=48 statementOnly=0 ... proved_failures=0`, `OK` |

### Lane test suite (43 checks, all pass)

The suite is `/tmp/opencode/s4-vendor-ci/run-tests.sh`. It builds a tarball from
the real snapshot, installs only into `/tmp/opencode/s4-vendor-ci/work/**`, and
re-verifies the real vendor tree at start and finish. It never writes
`vendor/btc-lean-core`.

```
$ /tmp/opencode/s4-vendor-ci/run-tests.sh
PASS  baseline verify-vendor (rc=0)
PASS  absent dest -> 3 (rc=3)
PASS  absent message mentions OPS-01
PASS  dry-run tarball (rc=0)
PASS  dry-run left vendor intact
PASS  vendor verifies after dry-run (rc=0)
PASS  tarball install (rc=0)
PASS  installed tree verifies (rc=0)
PASS  installed file count is 119
PASS  installed content equals manifest
PASS  existing dest without --force -> 1 (rc=1)
PASS  existing dest with --force (rc=0)
PASS  backup created
PASS  wrong archive sha -> 1 (rc=1)
PASS  no install on wrong archive sha
PASS  tampered content -> 1 (rc=1)
PASS  no install on tampered content
PASS  path traversal -> 1 (rc=1)
PASS  traversal rejected by name check
PASS  no traversal write outside staging
PASS  absolute symlink member -> 1 (rc=1)
PASS  symlink rejected
PASS  wrapped archive layout (rc=0)
PASS  wrapped tree verifies (rc=0)
PASS  archive with .lake installs (rc=0)
PASS  .lake stripped from install
PASS  ambiguous layout -> 1 (rc=1)
PASS  ambiguous layout message
PASS  URL without sha -> 2 (rc=2)
PASS  file URL with sha (rc=0)
PASS  URL tree verifies (rc=0)
PASS  http URL blocked -> 2 (rc=2)
PASS  CI VENDOR_ARTIFACT_PATH (rc=0)
PASS  CI VENDOR_ARTIFACT_URL + SHA (rc=0)
PASS  CI URL without SHA -> 2 (rc=2)
PASS  CI URL + PATH -> 2 (rc=2)
PASS  from-git unreachable -> 1 (rc=1)
PASS  from-git unpinned commit -> 1 (rc=1)
PASS  unpinned commit explicitly refused
PASS  unknown option -> 2 (rc=2)
PASS  missing archive -> 2 (rc=2)
PASS  bad sha format -> 2 (rc=2)
PASS  final verify-vendor (rc=0)

RESULT: pass=43 fail=0
SUITE RC=0
```

Notable concrete outputs:

```
# dry run against a tarball: verifies, exits 0, does not touch vendor
$ ./scripts/fetch-vendor.sh --from-tarball /tmp/opencode/s4-vendor-ci/btc-lean-core-f950806.tar.gz --dry-run
fetch-vendor: extracting ... into a temporary staging directory
fetch-vendor: no archive SHA-256 supplied; the 119-file manifest is the integrity gate
verify-vendor: OK (119 files)
fetch-vendor: DRY RUN: verified candidate at /tmp/ln-vendor-stage.XXXXXX; vendor/btc-lean-core was not modified
RC=0

# tampered archive: rejected by the per-file manifest, nothing installed
$ ./scripts/fetch-vendor.sh --from-tarball /tmp/opencode/s4-vendor-ci/work/tampered.tar.gz --dest /tmp/.../never
verify-vendor: MODIFIED
... Bitcoin.lean hash diff ...
fetch-vendor: checksum verification failed for ... (diff against vendor/VENDOR-SHA256 is above)
RC=1
```

### Canonical publication recipe (tested)

The per-file manifest is the pin. For a maintainer who chooses the artifact
path, this deterministic recipe excludes `.lake` and the stray local symlink:

```
tar --sort=name --mtime='@0' --owner=0 --group=0 --numeric-owner \
    --exclude=.lake --exclude=./btc-lean-core \
    -C vendor/btc-lean-core -czf btc-lean-core-f950806.tar.gz .

sha256sum btc-lean-core-f950806.tar.gz
# 48df03705b76d588bbfd94d2bbbb00f8e37686664e0c82873ff48145e8f6d412
```

I built it twice byte-for-byte (`cmp` RC 0), then installed it through the URL
path with the hash pinned:

```
$ ./scripts/fetch-vendor.sh --url file:///tmp/opencode/s4-vendor-ci/canonical-1.tar.gz \
    --sha256 48df0370...e8f6d412 --dest /tmp/opencode/s4-vendor-ci/canonical-install
fetch-vendor: archive SHA-256 OK (48df0370...e8f6d412)
verify-vendor: OK (119 files)
verify-vendor: OK (119 files)
fetch-vendor: provisioned ... (pinned commit f95080638ae571a3664f4f41b9b6f6b4cfa7c5eb)
RC=0
```

Deflate output can differ across zlib versions; the archive hash is only a
transport pin, and the 119-file manifest remains authoritative.

### Workflow validation

| Validation | Result |
|---|---|
| `python3 -c 'import yaml; yaml.safe_load(open(".github/workflows/ci.yml"))'` (PyYAML 6.0.1) | parse OK; jobs `source-gates`, `build` |
| `actionlint -no-color .github/workflows/ci.yml` (v1.7.12, downloaded to `/tmp/opencode`) | RC 0, no findings |
| `bash -n` on both scripts | RC 0 |
| `test -x` on both scripts | RC 0 |

I also extracted the exact `run:` block of the provisioning step from the YAML
and executed it in three simulated workspaces (the extraction guarantees the
tested shell is the shipped shell):

| Simulation | `available` output | Step RC | Summary/warning |
|---|---|---|---|
| Clean tree, no artifact input | `false` | 0 | `::warning title=Full build not run::...` + OPS-01 summary |
| Same, `REQUIRE_VENDOR_BUILD=true` | `false` | 1 | `::error title=Vendor build required::...` |
| `VENDOR_ARTIFACT_PATH=<canonical tar>` | `true` | 0 | provisioned + verified 119 files |
| Real worktree (vendor present) | `true` | 0 | `verify-vendor: OK (119 files)` |

## CI behavior

`source-gates` (always runs, no vendor dependency):

1. checkout, Python 3.12;
2. `check-catalog.py --audit`;
3. `check.sh`;
4. `check-final.py`;
5. `bash -n` + executable-bit check for the vendor scripts;
6. fetch pinned rust-lightning by SHA;
7. `verify-anchors.py`.

`build`:

1. checkout, Python 3.12;
2. `./scripts/fetch-vendor.sh --ci`;
   * RC 0 -> `available=true`, summary "provisioned and verified";
   * RC 3 -> `available=false`, `::warning`, summary says the full build did
     **not** run and why, gives provisioning options; if
     `REQUIRE_VENDOR_BUILD=true`, fail with `::error`;
   * RC 1/2 -> fail (tampered archive, bad hash, misconfiguration);
3. if `available=true`: `verify-vendor.sh`, then `leanprover/lean-action@v1`
   (`auto-config: false`, `build: true`, `use-mathlib-cache: false`), then a
   summary line confirming the build ran.
4. if `available=false`: the three build steps are visibly *skipped*.

Configuration (repository variables, never secrets):

| Variable | Meaning |
|---|---|
| `VENDOR_ARTIFACT_URL` | HTTPS URL of the published snapshot archive |
| `VENDOR_ARTIFACT_SHA256` | Required with the URL; 64-hex archive hash |
| `VENDOR_ARTIFACT_PATH` | Self-hosted alternative: local archive path |
| `REQUIRE_VENDOR_BUILD` | `true` (case-insensitive; `1`/`yes` also work) turns "unavailable" into a failed job |

A clean public checkout today takes the RC 3 path: source gates run, the build
job is green but explicitly reports that the build did not run. That is the
truthful state until the maintainer makes one of the policy choices below.
**No GitHub Actions run exists for this branch; no green-CI claim is made.**

## Anomalies found

1. **Stray absolute symlink in the snapshot.**
   `vendor/btc-lean-core/btc-lean-core -> /home/ubuntu/ln-lean/vendor/btc-lean-core`.
   It is not in `vendor/VENDOR-SHA256` (the manifest has 119 regular files and
   `verify-vendor.sh` uses `find -type f`), so it is invisible to the checksum
   gate and irrelevant to the build. It is a local convenience link into a
   different checkout. A naive `tar -czf` of the whole directory includes it and
   `fetch-vendor.sh` rejects the archive (`unsupported archive member`) for
   safety. **Recommendation:** delete the symlink before publishing a snapshot
   (vendor edit, so not done here). The canonical recipe excludes it.
2. **Public `btc-lean` moved.** `origin/main` now resolves to
   `08208274bcdcab2a5baa1426c0057472e5c0de07`; the `data-2026.10.17` tag still
   points at `4f5c4f8`. `refs/PINNED.md` records `4f5c4f8` as the review pin.
   This does not affect the build input, but the review pin is no longer the
   branch tip.
3. **File modes.** 118 manifest files are `0444`, one (`Test/Script/Parser/run.sh`)
   is `0555`, and the snapshot root is `0775`. Archive extraction preserves
   executable bits; the manifest does not record modes, so this is outside the
   integrity claim.
4. **`check-final.py` currently fails in this shared worktree** (`expected 176
   Lean files, found 182`) because other wave-4 lanes have added/edited Lean
   modules that the parent has not integrated yet. This lane did not touch
   `LnLean/**`; the failure is not caused by S4-VENDOR-CI. `check.sh` and
   `check-catalog.py --audit` both pass.
5. **No build artifact for `f950806` exists publicly.** `ln-lean` has no
   releases, and the `btc-lean` release tarball has no `spec/core`. The script
   cannot manufacture one; publication is a maintainer action.

## Remaining policy decision (for the maintainer)

`OPS-01` cannot be closed from inside this lane because it requires either a
publication action (release artifact) or a version-control change
(`.gitignore`/vendor commit), both outside the owned files.

| Option | Work | Result |
|---|---|---|
| **A. Publish a checksummed artifact (recommended)** | Remove the stray symlink, run the canonical tar recipe, upload the archive to a public release, set `VENDOR_ARTIFACT_URL` + `VENDOR_ARTIFACT_SHA256`, optionally set `REQUIRE_VENDOR_BUILD=true` | Clean CI builds with the exact 119-file snapshot; no repo bloat; publication needs a provenance/license decision for the `wallet-peer` lineage |
| **B. Commit the snapshot** | Remove `vendor/` from `.gitignore` (or unignore `vendor/btc-lean-core/`), commit the 119 files, keep the manifest | `fetch-vendor.sh --check` and the build work in every checkout; adds vendored provenance and repository size; same license question |
| **C. Keep the explicit skip gate** | Nothing | CI is honest but never builds; not release-ready |

A second, non-technical decision: whether the unpublished `wallet-peer`
snapshot may be redistributed at all. That is a maintainer/licensing call, not
something this lane can decide.

## Recommended `docs/OPEN-ISSUES.md` wording (not applied)

Replace the current `OPS-01` row with:

```
| `OPS-01` | P0 | open (mitigated) | Public CI cannot run the full build from a clean checkout | `vendor/btc-lean-core` is gitignored; the pinned snapshot `f950806` is not in public `btc-lean` history and no public artifact exists. `scripts/fetch-vendor.sh` now verifies or provisions an explicit local/URL/git-exact input against `vendor/VENDOR-SHA256` (119 files), returns a distinct skip code when no input is supplied, and `.github/workflows/ci.yml` always runs the source gates while marking the build as not run (with `REQUIRE_VENDOR_BUILD=true` available to fail instead). | Maintainer chooses: (a) publish a checksummed snapshot archive and set `VENDOR_ARTIFACT_URL` + `VENDOR_ARTIFACT_SHA256` (recommended), (b) commit the 119-file snapshot so `--check` works in CI, or (c) keep the explicit skip gate. Publication also requires a provenance/license decision for the `wallet-peer` snapshot. |
```

If the parent prefers to keep the issue `open` until a build actually runs, use
`open` instead of `open (mitigated)`; the evidence cell and next action stay
the same.

## Non-actions / scope

* No `lake build` (full or per-module) was run.
* No vendor file was edited; the stray symlink was only reported.
* No `LnLean/**`, `docs/**`, `lakefile.lean`, `lean-toolchain`,
  `vendor/VENDOR-SHA256`, or `collect-obligations.py` change.
* No git commit, push, tag, release, or artifact publication.
* `docs/OPEN-ISSUES.md` was not edited; the wording above is the handoff.
* No CI run was triggered on GitHub; actionlint/PyYAML and the extracted step
  logic are the local evidence.

## Integration notes

* Add `scripts/fetch-vendor.sh` with mode `100755` (it is `0775` in the
  worktree).
* `scripts/verify-vendor.sh` and `.github/workflows/ci.yml` are modified.
* Do not add `vendor/btc-lean-core` to git. Only `vendor/VENDOR-SHA256` should
  remain tracked.
* If the maintainer publishes the canonical archive, the tested archive hash is
  `48df03705b76d588bbfd94d2bbbb00f8e37686664e0c82873ff48145e8f6d412`
  (rebuild it from the same 119 files; the per-file manifest is the real gate).
* The lane test suite is outside the repo at
  `/tmp/opencode/s4-vendor-ci/run-tests.sh`; it can be rerun without touching
  the vendor snapshot.
