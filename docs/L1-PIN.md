# L1 pin (read-only reference)

`vendor/btc-lean-core` is a read-only snapshot of the existing `btc-lean`
Bitcoin L1 **model** (`spec/core`). It is consumed as a Lake path dependency;
it is never edited by this repository or by any LN agent.

* Source worktree: `/dev/shm/btc/wt` on `sensitive-isolated-box-2`
* Source branch: `wallet-peer`
* Snapshot commit: `f95080638ae571a3664f4f41b9b6f6b4cfa7c5eb`
* Toolchain: `leanprover/lean4:v4.35.0`
* Snapshot scope: `spec/core` only. The `btc-lean` proof tree (`spec/proofs`)
  is **not** copied and is not modified.
* Integrity: `vendor/VENDOR-SHA256` lists the source-file digests; run
  `./scripts/verify-vendor.sh` before and after every wave.

If the L1 model must change, the change belongs in the `btc-lean` repository
and the pin is updated deliberately. No LN agent has write permission on
`vendor/btc-lean-core` (the source files are mode `0444`).
