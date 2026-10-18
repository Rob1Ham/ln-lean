# Wave 8 — transaction-validity transfer, HTLC preimages, wire registration, and store epochs

**Status:** running; launched from `50d78ed`.

**Launch commit:** `50d78ed` (`[STATUS] correct proof-wave 7 L1 boundary note`)
**Branch:** `repair/integrated`
**Catalog at launch:** 48 proved / 0 statementOnly / 79 targets
**Full build at launch:** 233 jobs, RC 0
**Axiom audit at launch:** 194 theorems
**Roadmap:** `docs/OPEN-ISSUES.md`
**Protocol:** `docs/SWARM-LOOP.md`

Wave 7 closed the consumer, raw-gossip, live-conformance, and fold questions.
Wave 8 attacks the remaining concrete transfer and integration gaps:

* the final `TxValidation.Full` / `txCheckerFor` bridge for the delayed and
  revocation branches;
* the `HtlcWire` preimage byte-equality instantiation and HTLC scriptCode
  discipline;
* the BOLT 2 type-32 `open_channel` wire constructor and its end-to-end
  projection;
* the `accept_channel` payload/registration path for key attribution;
* the actual commitment-consumer construction sites;
* a concrete ECDSA verifier bridge for the abstract signing model;
* wider finite/live BOLT encodings;
* explicit gossip-store epochs and replacement sequences.

Eight lanes run in parallel with exclusive files. No lane commits, pushes,
edits `LnLean.lean`, `Obligations.lean`, `Traceability.lean`,
`AxiomAudit.lean`, the shared catalog, or docs owned by another lane; the
parent integrates and records the gate.

## Lanes

| Lane | Issue(s) | Owned files | Deliverable / acceptance |
|---|---|---|---|
| `S8-L1-TXVALID` | `L1-02`, `L1-07` | new `LnLean/Proofs/Bitcoin/TxValidTransferTargets.lean`, report | Import `Bitcoin.TxValidation.Full`; prove `txCheckerFor` equals/refines `RealChecker.realCheckerOf` for in-range inputs and `some` amounts, then transfer the delayed/revocation refinements. Model the `minimalData` / `csv ≥ 32768` policy edges explicitly. Keep the positive-direction and missing-amount boundaries. |
| `S8-PR-HTLCPREIMAGE` | `PR-05`, `PR-02` | new `LnLean/Proofs/Channel/HtlcPreimageTargets.lean`, report | Instantiate `Bip143Preimage.preimageBytes_eq_bip143MsgL` for `HtlcWire.toTx`, synthesize the HTLC-success/timeout scriptCode as far as the model permits, and document display-order txid conversion. Retain arbitrary-preimage field hypotheses. |
| `S8-L1-OPENCHANNEL-WIRE` | `L1-03` | `LnLean/Protocol/Messages.lean`, `LnLean/Protocol/Laws.lean`, `LnLean/Proofs/Liveness.lean`, `LnLean/Proofs/PhaseC3/PersistenceRecovery.lean`, `LnLean/Proofs/Protocol/ErrorProps.lean`, `LnLean/Proofs/Protocol/ChannelReestablishProps.lean`, `LnLean/Proofs/WaveD/D21.lean`, new `LnLean/Proofs/Protocol/OpenChannelWireTargets.lean`, report | Add the type-32 `open_channel` constructor without moving `Handshake.OpenChannel` (use an `OpenChannelWire` record), repair every exhaustive `Msg` match, and prove type/length/channel-id/pubkey/projection laws. If a downstream file outside the write set breaks, report the exact patch instead of editing it. |
| `S8-PR-ACCEPT-PAYLOAD` | `PR-01` | `LnLean/Protocol/Handshake.lean`, `LnLean/Proofs/Crypto/KeyModelTargets.lean`, new `LnLean/Proofs/Crypto/AcceptPayloadTargets.lean`, report | Add `acceptChannel?` storage to `HandshakeState`, set it on `recvAcceptChannel`, and connect the stored payload to `AdvertisesKey` / funding-key attribution. Preserve the negative result that the field alone is not proof of possession; model registration or keep the conditional contract. |
| `S8-CH-CONSUMER-SITES` | `CH-01` | `LnLean/Proofs/Channel/CommitmentConsumerTargets.lean`, new `LnLean/Proofs/Channel/CommitmentConsumerSitesTargets.lean`, report | Audit the actual `CommitmentTx` / `SignedState` construction and consumer sites, add a compiled `viewOfState`/net-consumer adapter where it belongs, and prove the migrated output list is what those sites read. Do not duplicate the consumer API already in `Commitment.lean`. |
| `S8-L1-EC-BRIDGE` | `L1-01`, `L1-07` | new `LnLean/Proofs/Bitcoin/EcdsaBridgeTargets.lean`, report | Investigate and, where faithful, prove a bridge from the abstract `PrimitiveModel.ecdsaVerify` seam to the concrete vendored `Bitcoin.Crypto.Ecdsa.Verify.verifyImpl` (including DER/pubkey/32-byte digest preconditions). If no unconditional bridge is available, prove the sharpest conditional/extraction form and keep the abstract boundary. |
| `S8-CONF-ENCODINGS` | `CONF-01` | `tests/conformance/**`, `scripts/check-conformance.py`, `LnLean/Proofs/ConformanceDiffTargets.lean`, report | Add more BOLT encodings (at least `open_channel`/`accept_channel` and one HTLC path) to the finite vector suite and Lean `decide` checks. Add a wider live differential row only if the pinned harness supports it; keep the finite/public-API caveat. |
| `S8-MODEL-STORE-EPOCH` | `RT-01` | `LnLean/Routing/Gossip.lean`, new `LnLean/Proofs/Routing/GossipStoreEpochTargets.lean`, report | Model gossip-store epochs/replacements explicitly and refine the canonical wrapper against the raw store over a realistic update sequence. Keep the raw non-refinement and per-slot/global-clock boundary results intact. |

## Integration rules

- Each lane gets exclusive files and a report path
  `agents/reports/swarm8/S8-<LANE>.md`.
- Lanes may run scoped builds. `S8-L1-OPENCHANNEL-WIRE` and
  `S8-PR-ACCEPT-PAYLOAD` may run the full `lake build` under the shared lock
  because their edits are cross-cutting; no other lane may.
- No `sorry`, `axiom`, `admit`, `native_decide`, `unsafe`, or
  `@[implemented_by]`. Allowed axioms: `propext`, `Quot.sound`,
  `Classical.choice`.
- Preserve mechanized counterexamples and the strongest true conditional
  form. A narrowed/blocked result is acceptable; a fake proof is not.
- If a requested change touches a forbidden shared file, implement the
  additive part in an owned module and report the exact integration patch.
- The parent integrates only sorry-free, faithful results, then updates the
  catalog, traceability, audit, generated indexes, roadmap, and gate record.

## Launch state

- Base `50d78ed`; `origin/main` remains `b891a59`.
- Working tree before launch has only the pre-existing untracked
  `agents/status/REPAIR.status`.
- Wave 8 has no catalog target additions until integration; the launch commit
  only records the lane plan and status.
