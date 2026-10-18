# S4-RELEASE — `OPS-02`, `OPS-03`

**Base:** `47189fe` (`[STATUS] define wave 4 open-issue lanes`)
**Checked snapshot:** `f2123ef` (`[STATUS] note wave 4 launch from 47189fe`)
**Verdict:** artifact-only / **blocked on maintainer decisions**. No license was
chosen, no `LICENSE` was created, no tag/PR/merge/push was performed, and no
full build was run.

## Deliverables

- `docs/RELEASE-CHECKLIST.md` — release gates for catalog, build, vendor
  reproducibility, license, tag/PR/merge, public CI, docs sync, artifacts, and
  rollback, with an exact pre-tag runbook and blocker table.
- `docs/LICENSE-DECISION.md` — neutral MIT / Apache-2.0 / dual
  `MIT OR Apache-2.0` decision matrix, third-party obligations, compatibility
  analysis, and a blank maintainer decision record. No recommendation is
  presented as a decision.
- `agents/reports/swarm4/S4-RELEASE.md` — this report.

No other files were edited by this lane. No `LICENSE`, tag, merge, commit, or
push was created.

## Checks performed

All commands were run in `/home/ubuntu/ln-lean-repair` unless noted.

| Check | Command | Result |
|---|---|---|
| Catalog, strict | `python3 scripts/check-catalog.py --audit` | **RC 0**; `rows=48 proved=48 statementOnly=0 targets=57 unresolved=0 proved_failures=0 duplicate_ids=0 candidates=0 declarations=5942` |
| Policy/sorry | `./scripts/check.sh` | **RC 0**; `files=176 obligations=82 sorry_in_proofs=0`; `check: OK` |
| Files/imports | `python3 scripts/check-final.py` | **RC 0**; 176 Lean files, 174 root imports, `D=33 E=15 F=15 total=63` |
| Vendor integrity | `./scripts/verify-vendor.sh` | **RC 0**; `verify-vendor: OK (119 files)` |
| Anchors | `python3 scripts/verify-anchors.py` | **RC 0**; `anchors=299 bad=0 unanchored_rows=2` |
| Exact `sorry` scan | `grep -RInE '^[[:space:]]*sorry[[:space:]]*$' LnLean --include='*.lean'` | No matches (covered by `check.sh`) |
| Clean public export | `git archive HEAD \| tar -x -C /tmp/opencode/s4-clean`, then catalog/`check.sh`/`check-final.py` | **RC 0** for all three; vendor absent as expected; `verify-vendor.sh` fails without vendor (expected) |
| CI YAML syntax | PyYAML `safe_load` | Parses as a mapping; jobs `source-gates` and `build` are present. PyYAML's YAML 1.1 rules represent the `on` key as boolean `True` (a known parser quirk), so this is a syntax check only. `actionlint` was not installed; GitHub-specific schema validation was not independently repeated. |
| Git/tag state | `git status`, `git tag -l`, `git rev-list --count origin/main..HEAD` | At check time the tree was clean except pre-existing untracked `agents/status/REPAIR.status`; no tags; 61 commits ahead of `origin/main`; `main` is an ancestor |
| GitHub state | GitHub API (`/repos/Rob1Ham/ln-lean`, `/tags`, `/releases`, Actions runs) | Public repo; default branch `main`; license `None`; no tags; no releases; 3 CI runs, all `success` |
| License inputs | local `refs/`, vendor tree, GitHub license API | `btc-lean` public pin MIT (with Bitcoin Core portions); vendor snapshot has **no** `LICENSE`; `rust-lightning` dual MIT/Apache-2.0; BOLTs CC-BY-4.0; Lean 4 Apache-2.0 |

**Not run:** full `lake build`, `collect-obligations.py`, `collect-anchors.py`,
any Git write command. The `182 jobs, RC 0` figure is historical (recorded at
`0c99c92`) and is not re-verified here.

**Shared-checkout note:** other Wave-4 lanes subsequently created or modified
their own files in this checkout (`LnLean/Bitcoin/Seam.lean`,
`LnLean/Channel/HTLC.lean`, `LnLean/Protocol/Messages.lean`,
`LnLean/Routing/Gossip.lean`, `.github/workflows/ci.yml`,
`scripts/verify-vendor.sh`, `scripts/fetch-vendor.sh`, new conformance/test
files). This lane did not touch them and did not use them for the verified
results above. In particular, the public-CI note below describes run #3 against
the **committed** workflow at `f2123ef`, not the uncommitted vendor-lane
rewrite. The parent must integrate under the normal gate and rerun every check
at the release commit.

## Public CI truth note

Latest observed run: **#3**, id `39138200828`, branch `repair/integrated`, commit
`f2123ef`, conclusion `success` (2026-10-18T14:56Z),
<https://github.com/Rob1Ham/ln-lean/actions/runs/39138200828>. All three recorded
runs (#1 `80bad41`, #2 `47189fe`, #3 `f2123ef`) concluded `success`; only run #3
was inspected at job-step level, and its build steps were skipped.

Job detail for run #3 against the committed workflow at `f2123ef`:

- `Source-level gates` — all executed steps succeeded: catalog audit,
  `check.sh`, `check-final.py`, pinned `rust-lightning` fetch, anchor check.
- `Full build (requires the vendored btc-lean snapshot)` — job conclusion
  `success`, but `Install pinned Lean toolchain and run lake build` and
  `Verify vendored snapshot checksums` were **skipped**. The vendor-presence
  step found no snapshot and emitted a warning.

Therefore green public CI **does not prove the tree builds**. It proves the
source-level gates and anchors pass on a clean checkout. `OPS-01` remains the
reason. No CI badge exists in `README.md`; none should be added that implies a
full build.

## Open blockers

| Blocker | Evidence | Blocks |
|---|---|---|
| `OPS-01` vendor reproducibility | `vendor/` is gitignored; `f950806` is not in public `btc-lean` history; CI build steps skipped | Clean public build and honest build CI |
| `OPS-02` no license | No root `LICENSE`/`COPYING`/`NOTICE`/`AUTHORS`; GitHub license `None` | Any public grant of rights |
| `OPS-03` no tag, `main` behind | No tags/releases; `origin/main` at `b891a59`, 61 commits behind `HEAD` | Tagged release and release notes |
| Vendor snapshot rights | Snapshot has no `LICENSE`; public `btc-lean` MIT at `4f5c4f8` does not automatically prove the `f950806` lineage grant | Redistribution of vendor code or compiled artifacts |
| BOLT attribution | BOLTs are CC-BY-4.0; no project-level attribution/notice file | Publishing docs/release notes with BOLT excerpts |
| No project version/release notes | `lakefile.lean` has no version; `lake-manifest.json` `1.3.0` is the manifest schema | Artifact naming and release publication |
| Public CI build skipped | Run #3 job steps skipped | Any claim that CI proves the build |
| Model/claim gaps | `L1-01`, `L1-02`, `MODEL-01`, `CR-01`, `SEC-01`, `CONF-01`, `PR-02`, `CH-01`, `CH-02`, `HT-01`, `RT-01` | Any spendability, conformance, computational-security, or full-verification claim; a caveated model release may disclose them instead |

## Exact human decisions required

1. **License option:** MIT, Apache-2.0, dual `MIT OR Apache-2.0`, or another
   option after legal review. **No choice is made in this lane.**
2. **Copyright holder / authorized licensor:** confirm ownership and authority;
   the commit history uses automation identities and there is no CLA/DCO.
3. **Contribution policy:** inbound = outbound, DCO, CLA, or another policy.
4. **Vendor packaging policy (`OPS-01`):** commit a checksummed snapshot, publish
   a separate checksummed artifact, or bump to a public `btc-lean` ancestor.
5. **Vendor redistribution and rights:** confirm the `f950806` grant and approve
   the `btc-lean` MIT / Bitcoin Core notice if the snapshot or binaries ship.
6. **Third-party notices:** approve attribution for `btc-lean`, Bitcoin Core,
   `rust-lightning` (if applicable), and BOLTs CC-BY-4.0.
7. **Tag/merge path (`OPS-03`):** PR vs direct fast-forward; merge commit vs
   fast-forward; tag on `main`'s merge commit vs the branch; signed vs annotated
   tag; tag name/version.
8. **Version and release notes:** choose the project version and approve notes
   that repeat the model-level caveats and open issues.
9. **Trademark/name policy and whether legal review is required.**

## Scope caveats

- This lane produced release **preparation** documents only. It is not a
  release approval and does not assert that the tree is releasable.
- No license text was drafted or applied; `docs/LICENSE-DECISION.md` is a
  comparison and a blank decision record, not legal advice.
- No claim is made that the full build passes at `f2123ef`; only the source
  gates, vendor checksum, and anchors were re-run.
- Public CI is reported exactly as observed: source gates green, build job green
  only because its build steps were skipped.
- The `docs/OPEN-ISSUES.md` lane table lists broader ownership for
  `S4-RELEASE`; the spawning prompt for this lane restricted writes to the three
  new files, so `README.md` and `.github/` were intentionally not edited.
- The catalog is a model-level claim; the release checklist requires the open
  issue caveats to stay visible in release notes.

## Integration recommendation

- Integrate the three new files as docs/report additions only.
- Do **not** mark `OPS-02` or `OPS-03` closed; both require maintainer action.
- Do **not** add a `LICENSE`, tag, or release from this lane.
- When the parent updates `docs/OPEN-ISSUES.md`, link this lane's checklist and
  license matrix under `OPS-02`/`OPS-03` and keep both open until the decisions
  and evidence exist.
