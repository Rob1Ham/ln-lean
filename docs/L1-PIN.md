# L1 pin (read-only references)

This repository has two distinct L1 facts. They must not be conflated.

| Role | Source | Commit | Used by |
|---|---|---|---|
| Authoritative reference | public `https://github.com/Rob1Ham/btc-lean` (`main`) | `4f5c4f858fb9ca0743042644453cfa92d30dd271` | review and future pin bumps only |
| Build dependency | `vendor/btc-lean-core` (snapshot) | `f95080638ae571a3664f4f41b9b6f6b4cfa7c5eb` | the current `lake build` |

## Authoritative public reference

The public `Rob1Ham/btc-lean` repository is the authoritative L1 reference for
review and for any future pin bump. Pinned facts:

* Repository: `https://github.com/Rob1Ham/btc-lean`
* Branch: `main`
* Commit: `4f5c4f858fb9ca0743042644453cfa92d30dd271`
* Committer date: `2026-10-18T01:29:18Z` (author date `2026-10-17T22:45:19Z`)
* Release tag: `data-2026.10.17` (same commit)
* Local clone: `/home/ubuntu/btc-lean-public`
* Read-only local reference: `refs/btc-lean -> /home/ubuntu/btc-lean-public`
  (untracked symlink, excluded by `.git/info/exclude`; do not commit it)
* Check: `./scripts/check-public-reference.sh`

The clone is a partial (`blob:none`) clone of a single release commit, not a
shallow clone. It is never imported by `lakefile.lean` and is not required for
a build.

## Vendor snapshot used by the current build

`vendor/btc-lean-core` is a read-only snapshot of the existing `btc-lean`
Bitcoin L1 **model** (`spec/core`). It is consumed as a Lake path dependency;
it is never edited by this repository or by any LN agent.

* Source worktree: `/dev/shm/btc/wt` on `sensitive-isolated-box-2`
* Source branch: `wallet-peer`
* Snapshot commit: `f95080638ae571a3664f4f41b9b6f6b4cfa7c5eb`
* Toolchain: `leanprover/lean4:v4.35.0`
* Snapshot scope: `spec/core` only. The `btc-lean` proof tree (`spec/proofs`)
  is **not** copied and is not modified.
* Integrity: `vendor/VENDOR-SHA256` lists the source-file digests (119 files);
  run `./scripts/verify-vendor.sh` before and after every wave.

**`f950806` is not in public `btc-lean` history.** The public clone has no
object for that commit (`git cat-file -e` fails) and its history is a single
release commit. The vendor snapshot is therefore a separate lineage, not an
ancestor of public `main`; the public tree is not a fast-forward of the
snapshot. See `docs/BTC-LEAN-PUBLIC.md` for the audited diff (87 paths).

The current build imports only `Bitcoin.Data.Basic`, `Bitcoin.Data.Script`,
`Bitcoin.Data.Tx`, and `Bitcoin.RuleAttr` from the vendor package. The public
clone's `spec/core` is **not** imported into this build, and no Lean theorem
in this tree is proved against it.

## Bump policy

If the L1 model must change, the change belongs in the `btc-lean` repository
and the pin is updated deliberately. A vendor bump is a separate change with:

1. a chosen public commit (record URL, commit, date in `refs/PINNED.md` here);
2. a full replacement of `vendor/btc-lean-core/spec/core` contents;
3. a regenerated `vendor/VENDOR-SHA256`;
4. a full clean `lake build` at RC 0 plus `scripts/verify-anchors.py` and
   `scripts/check.sh`;
5. a review of every vendored `path:line` anchor that moved.

It is not part of this repair, and no LN agent has write permission on
`vendor/btc-lean-core` (the source files are mode `0444`).

## Verify

```sh
cd /home/ubuntu/ln-lean-repair
./scripts/check-public-reference.sh   # public URL/commit + vendor digest, offline
./scripts/verify-vendor.sh            # vendor digest only
```
