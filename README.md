# ln-lean

A Lean 4 formal model and proof scaffold for the Lightning Network, layered
on the existing `btc-lean` Bitcoin L1 formalization.

**This is scaffolding, not a completed proof.** The tree compiles, the
definitions are anchored to BOLTs and `rust-lightning`, and every unproved
claim is a named obligation.  Wave A (8 agents) built the 35 executable model
modules; wave B (32 agents) added the proof statements under
`LnLean/Proofs/`; wave C (16 agents) closed 20 of the 25 remaining proof
obligations.  An independent `phase-c` lane also finished at 20/25; the final
branch uses its stronger whole-file versions for the three files that remain
open.  Five obligations remain, each documented as either false for the
current model or requiring a missing model invariant.  See
`docs/WAVE-STATUS.md` and `agents/reports/WAVE-C-INTEGRATOR.md`.

## Layout

```
LnLean/Basic/Core.lean      shared vocabulary (msat, ids, direction, errors)
LnLean/Bitcoin/Seam.lean    L1 aliases + funding/commitment scripts
LnLean/Crypto/              primitive model, hash/signature specs
LnLean/Wire/                BigSize, TLV, message framing
LnLean/Channel/             state machine, commitments, HTLC, revocation
LnLean/Protocol/            handshake, peer, features, errors
LnLean/Routing/             graph, gossip, onion, route construction
LnLean/Payment/             invoices, MPP, keysend, liquidity
LnLean/Security/            threat model and invariant catalog
LnLean/Proofs/              obligation modules and theorem statements
```

## Build

```sh
export PATH=/dev/shm/btc/elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
cd /home/ubuntu/ln-lean
flock -w 900 /tmp/ln-build.lock lake build
```

Per-module (the normal agent path):

```sh
flock -w 900 /tmp/ln-build.lock lake build LnLean.Channel.Commitment
```

## Checks

```sh
./scripts/verify-vendor.sh          # L1 snapshot checksums and read-only modes
python3 scripts/check-wave-a.py --build
python3 scripts/check-wave-b.py --build
python3 scripts/verify-anchors.py   # BOLT/LDK path:line anchors
./scripts/check.sh                  # forbidden constructs, unmarked sorry, duplicate ids
./scripts/regen-root.sh             # regenerate LnLean.lean from the module tree
```

## References

* `refs/rust-lightning` — pinned Lightning Dev Kit implementation.
* `refs/bolts` — BOLT specifications.
* `vendor/btc-lean-core` — pinned Bitcoin L1 Lean model.

## Documentation

* `docs/CHARTER.md` — goals, non-goals, phases.
* `docs/ARCHITECTURE.md` — module graph and modelling decisions.
* `docs/ASSUMPTIONS.md` — cryptographic/L1/network TCB.
* `docs/SCOPE.md` — in/out of scope.
* `docs/THEOREM-INDEX.md` — every theorem and its status.
* `docs/TRACEABILITY.md` — obligation → BOLT → rust-lightning anchors.
* `docs/ROADMAP.md` — how to close the scaffold into a proof.
* `docs/WAVE-STATUS.md` — agent waves, gate, and reproduce commands.
* `docs/OBLIGATIONS-GENERATED.md` — generated obligation/marker index.
* `docs/ANCHORS-GENERATED.md` — generated BOLT/LDK anchor index.
