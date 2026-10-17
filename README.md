# ln-lean

A Lean 4 formal model and proof scaffold for the Lightning Network, layered
on the existing `btc-lean` Bitcoin L1 formalization.

**This is scaffolding, not a completed proof.** The tree compiles, the
definitions are anchored to BOLTs and `rust-lightning`, and every unproved
claim is a named obligation.

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
./scripts/check.sh          # forbidden constructs, unmarked sorry, obligation count
./scripts/regen-root.sh     # regenerate LnLean.lean from the module tree
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
