# L1 pin (read-only)

`vendor/btc-lean-core` is a byte-for-byte snapshot of the existing
`btc-lean` Bitcoin L1 Lean development, taken from
`/home/ubuntu/btc-lean/spec/core`.

* Source repository: `https://github.com/Rob1Ham/btc-lean`
* Source commit at snapshot time: `fd58ef10`
* Toolchain: `leanprover/lean4:v4.35.0`
* Snapshot verified with `rsync -ainc --delete` (no differences).

**Do not edit anything under `vendor/`.** It is git-ignored in this
repository and is consumed only as a Lake path dependency. If the L1 model
must change, that change belongs in the `btc-lean` repository and must be
re-pinned here.
