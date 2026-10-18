# ln-lean

A Lean 4 formal model and proof scaffold for the Lightning Network, layered
on the existing `btc-lean` Bitcoin L1 formalization.

**This is scaffolding, not a completed proof.** The tree compiles, the
definitions are anchored to BOLTs and `rust-lightning`, and every unproved
claim is a named obligation.  Wave A (8 agents) built the 35 executable model
modules; wave B (32 agents) added the proof statements under
`LnLean/Proofs/`; wave C (16 agents) closed 20 of the 25 remaining proof
obligations.  Waves D and E independently attempted the same 48 catalog
targets; wave F added 16 model-hardening modules; wave G ran 32 read-only
audits and produced the final selection.  The integrated tree has **132 Lean
files** (69 base + 33 D + 15 E + 15 F), **95 obligation markers**, and **15
documented open sites**.  See `docs/WAVE-STATUS.md`,
`agents/status/FINAL-SELECTION.md`, and
`agents/reports/FINAL-INTEGRATOR.md`.

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
cd /home/ubuntu/ln-lean-final
flock -w 900 /tmp/ln-build.lock lake build
```

Per-module (the normal agent path):

```sh
flock -w 900 /tmp/ln-build.lock lake build LnLean.Channel.Commitment
```

## Checks

```sh
python3 scripts/check-final.py      # sparse selection, one module per slot, 132/132 imports
./scripts/verify-vendor.sh          # L1 snapshot checksums and read-only modes
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
* `docs/FINAL-STATUS.md` — integrated D/E/F final gate and open sites.
* `agents/status/FINAL-SELECTION.md` — one-file-per-slot selection manifest.
* `docs/PROJECT-PLAN.md` — remaining integration/push plan.
* `docs/OBLIGATIONS-GENERATED.md` — generated obligation/marker index.
* `docs/ANCHORS-GENERATED.md` — generated BOLT/LDK anchor index.
