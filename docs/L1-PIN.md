# L1 pin (public core, build dependency)

This repository has two distinct L1 facts. They must not be conflated, even
though as of the `repair/pubbump` bump both name the same public commit.

| Role | Source | Commit | Used by |
|---|---|---|---|
| Authoritative reference | public `https://github.com/Rob1Ham/btc-lean` (`main`) | `4f5c4f858fb9ca0743042644453cfa92d30dd271` | review and future pin bumps |
| Build dependency | `vendor/btc-lean-core` (byte-identical copy of public `spec/core`) | `4f5c4f858fb9ca0743042644453cfa92d30dd271` | the current `lake build` |

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

`vendor/btc-lean-core` is a copy of the public `spec/core` tree at the pin
above. It is consumed as a Lake path dependency and is never edited by this
repository or by any LN agent.

* Pin: `4f5c4f858fb9ca0743042644453cfa92d30dd271` (public `main`, tag
  `data-2026.10.17`)
* Copy source: `/home/ubuntu/btc-lean-public/spec/core` (clean worktree at the
  pin; the public clone is not modified)
* Copy date: `2026-10-18`
* Toolchain: `leanprover/lean4:v4.35.0` (identical to the public
  `spec/core/lean-toolchain`)
* Copy scope: `spec/core` only. The `btc-lean` proof tree (`spec/proofs`) is
  **not** copied and is not modified.
* Shape: a real directory copy, not a symlink; source files are mode `0444`,
  directories stay writable so Lake can create `.lake/`.
* Size: 149 files, 146 of them `.lean`.
* Integrity: `vendor/VENDOR-SHA256` lists all 149 source-file digests;
  `./scripts/verify-vendor.sh` re-checks them before and after every wave and
  excludes `.lake/`.
* Equivalence check:
  `diff -r -x .lake vendor/btc-lean-core /home/ubuntu/btc-lean-public/spec/core`
  is empty (the `.lake/` build cache is created by the first build and is
  excluded; without `-x .lake` it shows up as the single "Only in" entry).

`vendor/` is listed in `.gitignore`, so the vendor payload itself is not
committed (historical layout). The tracked record of the bump is
`vendor/VENDOR-SHA256` plus this file and `refs/PINNED.md`; a fresh checkout
must populate `vendor/btc-lean-core` from the public pin and re-run
`./scripts/verify-vendor.sh`.

### Wiring

`lakefile.lean` is unchanged by the bump:

```lean
require «core» from "vendor/btc-lean-core"
```

The public package is named `«core»` and exposes a default `lean_lib Bitcoin`,
so the existing path dependency resolves it directly. The public `lakefile`
also declares two `default_target` executables (`btclean`, `capstone`); as a
path dependency only the imported library closure is built, so they are not
part of this build.

The build imports only `Bitcoin.RuleAttr`, `Bitcoin.Data.Basic`,
`Bitcoin.Data.Script`, and `Bitcoin.Data.Tx` from the core (4 modules). A full
`lake build` is 170 jobs: those 4 core modules, 164 `LnLean` modules, and the
library/root facets.

## Superseded snapshot (history)

Before `repair/pubbump` the build used a different snapshot,
`f95080638ae571a3664f4f41b9b6f6b4cfa7c5eb` (`wallet-peer` lineage,
119 manifest files). **That commit is not in public `btc-lean` history**: the
public clone has no object for it (`git cat-file -e` fails) and its history is
a single release commit. It was a separate lineage, not an ancestor of public
`main`, and is now retired on this branch. The pre-bump audit of the 87-path
difference is kept in `docs/BTC-LEAN-PUBLIC.md`.

## Bump policy

If the L1 model must change, the change belongs in the `btc-lean` repository
and the pin is updated deliberately. A vendor bump is a separate change with:

1. a chosen public commit (record URL, commit, date in `refs/PINNED.md` here);
2. a full replacement of `vendor/btc-lean-core` with that commit's `spec/core`
   (copy, never symlink; do not edit the public clone);
3. a regenerated `vendor/VENDOR-SHA256`;
4. a full clean `lake build` at RC 0 plus `scripts/verify-anchors.py` and
   `scripts/check.sh`;
5. a review of every vendored `path:line` anchor that moved.

The bump recorded here was executed as the `V01` lane; see
`agents/reports/V01.md`.

## Verify

```sh
./scripts/check-public-reference.sh   # public URL/commit + vendor digest, offline
./scripts/verify-vendor.sh            # vendor digest only
diff -r -x .lake vendor/btc-lean-core /home/ubuntu/btc-lean-public/spec/core  # empty
```
