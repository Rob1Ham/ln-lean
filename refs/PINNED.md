# Pinned references (read-only)

These clones are for anchor checking and review only. They are not imported
or built by this repository.

| Reference | Repository | Commit | Date |
|---|---|---|---|
| rust-lightning (LDK) | `https://github.com/lightningdevkit/rust-lightning` | `fe4900930c6bd5786ec4203274d7cf312776a5a6` | 2026-10-17 |
| BOLTs | `https://github.com/lightning/bolts` | `1aadb719b4007c4cea0ba6e36b08c4fb53788dee` | 2026-09-21 |
| btc-lean (L1 public, authoritative) | `https://github.com/Rob1Ham/btc-lean` | `4f5c4f858fb9ca0743042644453cfa92d30dd271` | 2026-10-18 |

Every module docstring cites `path:line` anchors at the pinned commit above.
Agents must not edit, pull, or rebase these trees.

## L1 authority

The public `Rob1Ham/btc-lean` repository at `main@4f5c4f8` is the
authoritative L1 reference for review and for any future pin bump. The local
clone is `/home/ubuntu/btc-lean-public`; `refs/btc-lean` is an untracked,
git-excluded symlink to it (never commit the symlink).

* Commit: `4f5c4f858fb9ca0743042644453cfa92d30dd271`
  ("btc-lean: Lean 4 model of Bitcoin consensus with row-level Core traceability").
* Committer date `2026-10-18T01:29:18Z`; author date `2026-10-17T22:45:19Z`.
* Release tag `data-2026.10.17` points at the same commit.
* Clone shape: partial (`blob:none`), one release commit, not shallow.

## Vendor snapshot (build input)

`vendor/btc-lean-core` remains the read-only snapshot used by the current
build: commit `f95080638ae571a3664f4f41b9b6f6b4cfa7c5eb` (source branch
`wallet-peer`). **That commit is not present in public `btc-lean` history**:
`git -C /home/ubuntu/btc-lean-public cat-file -e f950806...` fails, and the
clone holds no object for it. The snapshot is a separate lineage, not an
ancestor of public `main`.

* Imported by `lakefile.lean` as the path dependency `«core»`.
* Integrity: `vendor/VENDOR-SHA256` (119 files); check with
  `./scripts/verify-vendor.sh` or `./scripts/check-public-reference.sh`.
* Never edit; see `docs/L1-PIN.md`.

## Bump policy

A vendor bump is a separate, deliberate change outside any repair lane: take
the chosen public commit's `spec/core`, refresh `vendor/VENDOR-SHA256`, run a
full `lake build`, re-run `scripts/verify-anchors.py` and `scripts/check.sh`,
and review the vendored line anchors. It is **not** part of the L01 public
reference repair, and the public clone must never become a build dependency.
