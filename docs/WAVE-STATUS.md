# Wave status

`ln-lean` is a Lean 4 formal-model and proof **scaffold** for the Lightning
Network.  It is layered on a read-only snapshot of the existing `btc-lean`
Bitcoin L1 model.  It is not a completed proof of Lightning.

## Two waves

| Wave | Agents | Purpose | Output |
|---|---:|---|---|
| A | 8 | executable model modules, one per domain | `LnLean/{Bitcoin,Crypto,Wire,Channel,Protocol,Routing,Payment,Security}/` |
| B | 32 | proof statements and obligation markers | `LnLean/Proofs/**` |

Wave B is gated on `agents/status/A-GREEN`.  The gate means every wave-A
module builds and `scripts/check.sh` passes, so a proof agent never starts
from missing or broken imports.

## Reproduce

```sh
export PATH=/dev/shm/btc/elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
cd /home/ubuntu/ln-lean

./scripts/verify-vendor.sh          # L1 snapshot checksums and read-only modes
python3 scripts/check-wave-a.py     # presence of all wave-A modules/docs
python3 scripts/check-wave-a.py --build
./scripts/check.sh                  # forbidden constructs, unmarked sorry, duplicate ids
./scripts/regen-root.sh             # regenerate LnLean.lean
flock -w 1800 /tmp/ln-build.lock lake build
```

## Integrity

* `vendor/btc-lean-core/` is a snapshot of `btc-lean` `spec/core` at
  `f95080638ae571a3664f4f41b9b6f6b4cfa7c5eb`.  Source files are mode
  `0444`; `vendor/VENDOR-SHA256` is versioned and checked by
  `scripts/verify-vendor.sh`.  The Bitcoin L1 proofs are not copied or
  modified.
* `refs/rust-lightning` is pinned at
  `fe4900930c6bd5786ec4203274d7cf312776a5a6`.
* `refs/bolts` is pinned at
  `1aadb719b4007c4cea0ba6e36b08c4fb53788dee`.

## Honest status

An obligation is a named claim, not a proof.  A module may contain
`sorry` only under `LnLean/Proofs/` and only with a
`-- OBLIGATION: LN-...` marker (or the structured catalog in
`LnLean/Proofs/Obligations.lean`).  Cryptographic correctness is
conditional on the `Prop` fields in the primitive model; it is never
asserted as an axiom.  `docs/THEOREM-INDEX.md` and
`docs/OBLIGATIONS-GENERATED.md` are the status views.
