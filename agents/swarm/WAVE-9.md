# Wave 9 — EC boundary, transport attribution, registration, arbitrary preimages, node canonicalisation, live messages

**Status:** running; launched from `10d18a1`.

**Launch commit:** `10d18a1` (`[DOCS] finalize hosted CI evidence`)
**Branch:** `repair/integrated`
**Catalog at launch:** 48 proved / 0 statementOnly / 100 targets
**Full build at launch:** 250 jobs, RC 0
**Axiom audit at launch:** 215 theorems
**Roadmap:** `docs/OPEN-ISSUES.md`
**Protocol:** `docs/SWARM-LOOP.md`

Wave 8 closed the known-amount `TxValidation.Full` transfer, the `HtlcWire`
second-stage preimage, the type-32 `open_channel` wire path, the proof-layer
consumer adapter, and the update/announcement epoch square. Wave 9 attacks the
remaining boundaries that wave 8 deliberately left explicit:

* whether a concrete EC verifier can instantiate or replace
  `VendorEcdsaBridge`, or whether the abstract seam is unavoidable;
* transport attribution and `HandshakeState` routing for the new
  `OpenChannelWire` record;
* a registration/proof-of-possession game for `accept_channel`, beyond storing
  the payload;
* wire-only coverage and the eight arbitrary-preimage field hypotheses;
* node-announcement canonicalisation in the store-epoch model;
* a live BOLT 2 message row in the pinned differential harness.

Six lanes run in parallel with exclusive files. No lane commits, pushes, edits
`LnLean.lean`, `Obligations.lean`, `Traceability.lean`, `AxiomAudit.lean`, the
shared catalog, or docs owned by another lane; the parent integrates and
records the gate.

## Lanes

| Lane | Issue(s) | Owned files | Deliverable / acceptance |
|---|---|---|---|
| `S9-L1-EC-UNCONDITIONAL` | `L1-01`, `L1-07` | new `LnLean/Proofs/Bitcoin/EcdsaConcreteTargets.lean`, report | Decide whether a concrete `Bitcoin.Crypto.Ecdsa.Verify.verifyImpl` instance can satisfy `VendorEcdsaBridge`, or prove the sharpest obstruction/separation. Keep `EufCma`/`KeyBinding` explicit. Do not edit `EcdsaBridgeTargets.lean` or `PrimitiveModel`; if a core patch is needed, report it. |
| `S9-L1-OPENCHANNEL-ROUTING` | `L1-03` | new `LnLean/Proofs/Protocol/OpenChannelRoutingTargets.lean`, report | Model transport attribution/provenance for `OpenChannelWire` and the handshake-receive path; prove wire → `Handshake.OpenChannel` → funding reachability and a non-attribution/forgery boundary. Do not edit `Messages.lean`/`Handshake.lean`; report any exact core patch instead. |
| `S9-PR-ATTRIBUTION` | `PR-01` | new `LnLean/Proofs/Crypto/AttributionGameTargets.lean`, report | Model a registration/proof-of-possession game over `StoredAccept`; prove storage is not possession, conditional attribution under `KeyBinding`, and a counterexample without it. Do not edit `AcceptPayloadTargets.lean`. |
| `S9-PR-ARBITRARY-PREIMAGE` | `PR-02` | new `LnLean/Proofs/Channel/PreimageCoverageTargets.lean`, report | Characterize wire-only coverage and the eight arbitrary-preimage field hypotheses; prove coverage under the hypotheses, a counterexample when dropped, and the display-order/BIP 143 boundary. Do not edit `HtlcPreimageTargets.lean`. |
| `S9-RT-NODE-CANON` | `RT-02` | new `LnLean/Proofs/Routing/NodeCanonicalTargets.lean`, report | Model node-announcement canonicalisation against the canonical store; prove the invariants/replacement/rotation results and the boundary witnesses. Do not edit `Gossip.lean` or `GossipStoreEpochTargets.lean`; keep additive definitions in the owned module. |
| `S9-CONF-LIVE-MSG` | `CONF-01` | `tests/conformance/**`, `scripts/check-conformance.py`, `LnLean/Proofs/ConformanceDiffTargets.lean`, report | Add a live BOLT 2 message row if the pinned rust-lightning harness supports it; otherwise record the exact blocker and keep the finite row. Preserve the existing 175 Lean references and 13/13 mutation controls. Do not edit docs or the catalog. |

## Integration rules

- Each lane gets exclusive files and a report path
  `agents/reports/swarm9/S9-<LANE>.md`.
- Lanes may run scoped builds. Use
  `LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock lake build ...`;
  no concurrent un-locked Lean build.
- No `sorry`, `axiom`, `admit`, `native_decide`, `unsafe`, or
  `@[implemented_by]`. Allowed axioms: `propext`, `Quot.sound`,
  `Classical.choice`.
- Preserve mechanized counterexamples and the strongest true conditional form.
  A narrowed/blocked result is acceptable; a fake proof is not.
- If a requested change touches a forbidden shared file, implement the additive
  part in an owned module and report the exact integration patch.
- The parent integrates only sorry-free, faithful results, then updates the
  catalog, traceability, audit, generated indexes, roadmap, and gate record.

## Launch state

- Base `10d18a1`; `origin/main` remains `b891a59`.
- Working tree before launch has only the pre-existing untracked
  `agents/status/REPAIR.status`.
- Wave 9 has no catalog target additions until integration; the launch commit
  only records the lane plan and status.
