# Wave status

`ln-lean` is a Lean 4 formal-model and proof **scaffold** for the Lightning
Network.  It is layered on a read-only snapshot of the existing `btc-lean`
Bitcoin L1 model.  It is not a completed proof of Lightning.

## Waves

| Wave | Agents | Purpose | Output |
|---|---:|---|---|
| A | 8 | executable model modules, one per domain | `LnLean/{Bitcoin,Crypto,Wire,Channel,Protocol,Routing,Payment,Security}/` |
| B | 32 | proof statements and obligation markers | `LnLean/Proofs/**` |
| C | 16 | close the remaining proof obligations, one file per agent | `wave-c/235` |

Wave B is gated on `agents/status/A-GREEN`.  The gate means every wave-A
module builds and `scripts/check.sh` passes, so a proof agent never starts
from missing or broken imports.

## Current status

Waves A, B and C are complete.

Wave A: all **8/8** agents exited with RC 0, all **35** expected modules
build, all four wave-A docs exist, and the vendor checksum, policy checks,
and pinned-anchor checker pass.  The A-green gate was written at
`2026-10-17T22:35:33Z`; the 32 wave-B agents started immediately after it.

Wave B: all **32/32** agents wrote their expected modules.  **31** exited
with RC 0; B02 hit the wrapper budget (`exit=130`) after writing its
726-line `ScriptProps` module, and the integrator removed one redundant
tactic and verified the module.  The B integration snapshot had **69** Lean
files (36 model, 33 proof), **1541** proof declarations, **48** obligation
markers, and **25** `sorry` sites under `LnLean/Proofs/`.  The full root
build was **77 jobs, RC 0** at integration commit `78c2f3f`.

Wave C: **16/16** proof-closure agents exited with RC 0 on branch
`wave-c/235`; every assigned module builds.  Wave C closed **20 of the 25**
remaining `sorry` sites.  The final tree has **69** Lean files (36 model,
33 proof), **1547** proof declarations, **32** retained obligation markers,
and **5** `sorry` sites.  The full root build is **77 jobs, RC 0**.  The
other box's independent `phase-c` lane closed 19 of 25; this branch is
stronger on `FundingProps` and equal on the other files, so no `phase-c`
file was merged.  See `agents/reports/WAVE-C-INTEGRATOR.md`.

Five obligations remain open, deliberately:

| Site | Reason |
|---|---|
| `FundingProps` `LN-FUND-001` | false as stated without the well-formed/range hypothesis; a counterexample is documented |
| `ReserveProps` `LN-CH-101` | false without an affordability guard; the guarded companion is proved |
| `GossipProps` `LN-GOSSIP-001` … `003` | false for the current model (unconstrained key/capacity/signature fields); private counterexamples are mechanized |

The wave-A catalog has **48** obligations: 13 are marked `proved` against the
small security models, 35 are `statementOnly`.  That distinction is the
honest status: a statement-only row is a tracked future theorem, not a
result.  The obligation markers are additional named proof targets; they do
not change the catalog's status.

## Reproduce

```sh
export PATH=/dev/shm/btc/elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
cd /home/ubuntu/ln-lean

./scripts/verify-vendor.sh          # L1 snapshot checksums and read-only modes
python3 scripts/verify-anchors.py   # BOLT/LDK path:line anchors
./scripts/check.sh                  # forbidden constructs, unmarked sorry, duplicate ids
python3 scripts/check-wave-a.py --build
python3 scripts/check-wave-b.py --build
python3 scripts/check-wave-c.py --build
./scripts/regen-root.sh             # regenerate LnLean.lean
flock -w 1800 /tmp/ln-build.lock lake build
./scripts/integrate-c.sh            # Wave-C full gate + generated indexes/report
./scripts/finalize.sh               # full integration gate + generated indexes/report
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
