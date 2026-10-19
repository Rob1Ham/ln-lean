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

---

# Appendix — Wave H 48-lane manifest and results

# Wave 8 — 48-agent continuation wave

**Status:** 48 lanes executed; 45 Lean modules merged, H04/H08 recovered and green; parent integration complete.
**Branch:** `wave-h/48`
**Worktree:** `/home/ubuntu/ln-lean-waveh`
**Launch base:** `50d78ed` (`[STATUS] correct proof-wave 7 L1 boundary note`)
**Baseline gate:** full build RC 0 (`233 jobs`), 204 Lean files, 202 root
imports, 48/48 catalog rows proved, 79 targets, zero actual `sorry`.
**Merged gate:** 295 jobs, 256 Lean files, 254 root imports, 100 targets,
227 audited theorems, zero actual `sorry`.
**Roadmap:** `docs/OPEN-ISSUES.md`
**Protocol:** `docs/SWARM-LOOP.md`

This wave is a 48-lane continuation of proof-wave 7. Each lane owns exactly one
new Lean module and one report. The parent owns all shared files, root imports,
catalog/traceability/audit updates, counts, documentation, Git history, and the
final gate.

## Absolute lane rules

- Work only in `/home/ubuntu/ln-lean-waveh` on `wave-h/48` at `50d78ed`.
- Do not edit `LnLean.lean`, `LnLean/Proofs/Obligations.lean`,
  `LnLean/Proofs/Traceability.lean`,
  `LnLean/Proofs/PhaseC3/AxiomAudit.lean`, `scripts/check*.py`,
  `scripts/check.sh`, `docs/**`, `agents/status/**`, the catalog, or any other
  lane's files. Your only writable files are your assigned module and report.
- Do not touch `vendor/**`, `refs/**`, the `.lake` symlink, or Git. No commit,
  checkout, branch, tag, reset, push, or worktree command.
- No `sorry`, `axiom`, `admit`, `native_decide`, `unsafe`, or
  `@[implemented_by]`. Only `propext`, `Quot.sound`, and `Classical.choice`
  may appear in `#print axioms`.
- Keep every existing counterexample. A faithful narrowed, conditional, or
  negative result is better than a false unconditional theorem.
- Build only your module under the shared lock:
  `export PATH=/dev/shm/btc/elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH`
  then
  `LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock lake build LnLean.Proofs.WaveH.Hxx`
- Do not run the full `lake build`, `collect-obligations.py`,
  `collect-anchors.py`, `check.sh`, or any catalog/conformance gate.
- If the literal target is false or needs a shared-file edit, stop at the
  strongest true additive result, state the exact counterexample or integration
  patch, and report `narrowed`/`refuted`/`blocked`.
- Report path: `agents/reports/wave8/Hxx.md`, using the template in
  `docs/SWARM-LOOP.md` and the exact module path.

## Lane table

| Lane | Issues | Owned module / artifact | Acceptance target |
|---|---|---|---|
| `H01` | `L1-02`, `L1-07` | `LnLean/Proofs/WaveH/H01.lean` | Prove `Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount) = Bitcoin.Capstone.RealChecker.realCheckerOf tx nIn amount` for `nIn < tx.vin.length`; derive the `none`/missing-data behavior and any required checker extensionality. |
| `H02` | `L1-02`, `L1-07` | `LnLean/Proofs/WaveH/H02.lean` | Transfer the delayed `to_local` refinement (`SequenceContextTargets.toLocal_delayed_checkerOf_refinement` or its real-checker form) from `realCheckerOf` to `TxValidation.Full.txCheckerFor` under `some amount` and the existing sequence/signature hypotheses. |
| `H03` | `L1-02`, `L1-07` | `LnLean/Proofs/WaveH/H03.lean` | Transfer the revocation-branch acceptance/rejection result to `txCheckerFor`; prove wrong-key and wrong-branch negatives at the full-checker boundary. |
| `H04` | `L1-02`, `L1-07` | `LnLean/Proofs/WaveH/H04.lean` | Relate the full `TxValidation.Full.scriptLaneTx` (or `txVerdictFull`) result for a one-input delayed/revocation transaction to the exact checker-level side conditions. Keep the table/amount/flag premises explicit. |
| `H05` | `L1-02`, `L1-07`, `MODEL-01` | `LnLean/Proofs/WaveH/H05.lean` | Model the `minimalData` policy edge: exhibit the non-minimal false encoding divergence (`truthy` versus vendor/Core cast), prove the default-policy result, and give the precise policy-gated acceptance theorem or counterexample. |
| `H06` | `L1-02`, `L1-07` | `LnLean/Proofs/WaveH/H06.lean` | Prove the `csv ≥ 32768` / disable-bit boundary for the fixed-width `delayBytes` encoding; show why the out-of-range branch is not representable and connect it to the sequence-context hypotheses. |
| `H07` | `PR-05`, `PR-02` | `LnLean/Proofs/WaveH/H07.lean` | Define `htlcBip143Preimage` for the existing `SighashTargets.HtlcWire` and prove its version/outpoint/index/sequence/locktime/scriptCode fields, then byte equality with `Bitcoin.SigHash.bip143MsgL` using `Bip143Preimage.ofTx`. |
| `H08` | `PR-05`, `PR-02` | `LnLean/Proofs/WaveH/H08.lean` | Synthesize the BOLT 3 HTLC scriptCode(s): define the offered and received HTLC witness-script/scriptCode bytes, prove their sizes and byte layout, and instantiate the H07 preimage with the synthesized scriptCode. |
| `H09` | `PR-05`, `PR-02` | `LnLean/Proofs/WaveH/H09.lean` | Prove the HTLC preimage digest equals the vendored `signatureHashBip143Impl` for the wire transaction, with a concrete 179-byte (or correctly sized) vector and the guarded/out-of-range behavior. |
| `H10` | `PR-05`, `PR-02` | `LnLean/Proofs/WaveH/H10.lean` | Model display-order txid conversion: define byte reversal, prove involution and size, and prove the internal-order funding txid used by the preimage is the reverse of the display form. Keep the domain explicit. |
| `H11` | `PR-05`, `PR-02` | `LnLean/Proofs/WaveH/H11.lean` | Strengthen `HtlcWire` serialization: prove parser round-trip and wire-domain for value/script bounds, plus truncated/oversized negative cases. Do not edit `SighashTargets`; define the extension additively. |
| `H12` | `PR-06`, `PR-02` | `LnLean/Proofs/WaveH/H12.lean` | Prove a conditional HTLC signature-to-view binding theorem for the `HtlcWire` path, with an explicit collision-free/serialization hypothesis and a counterexample showing digest binding alone does not bind the HTLC view. |
| `H13` | `L1-03` | `LnLean/Proofs/WaveH/H13.lean` | Add an additive BOLT 2 type-32 `OpenChannelMsg` record with the full wire-relevant fields and prove its fixed payload length is `319` (the exact BOLT 2 mandatory value; the earlier `313` sketch was an under-count). |
| `H14` | `L1-03` | `LnLean/Proofs/WaveH/H14.lean` | Prove an encode/decode round-trip for `OpenChannelMsg` field-by-field (or a faithful parser theorem) without modifying `Protocol/Messages.lean`; record the exact shared-file patch separately. |
| `H15` | `L1-03` | `LnLean/Proofs/WaveH/H15.lean` | Prove `OpenChannelMsg.toOpenChannel` agrees with the existing `Protocol.Handshake.OpenChannel` projection (temporary id, funding satoshis, push msat, funding pubkey) and preserves the funding negotiation. |
| `H16` | `L1-03` | `LnLean/Proofs/WaveH/H16.lean` | Add an additive `FundingPhase`/handshake bridge for a received or sent `OpenChannelMsg`; prove that the phase transition carries the exact message and that `sendAccept` still requires `openReceived`. |
| `H17` | `L1-03` | `LnLean/Proofs/WaveH/H17.lean` | Prove the type-32 registration facts: `wireType = 32`, unique type, length bound, channel-id extraction, and pubkey extraction for `OpenChannelMsg`; report the exact `Messages.lean` integration patch. |
| `H18` | `L1-03` | `LnLean/Proofs/WaveH/H18.lean` | Add negative/truncation/wrong-type tests for `OpenChannelMsg` decoding and prove the decoder rejects them. Keep the test model local and reproducible. |
| `H19` | `PR-01` | `LnLean/Proofs/WaveH/H19.lean` | Add an additive full `AcceptChannelPayload` record at the handshake boundary, including the funding key, and prove its fixed payload length and field projections. |
| `H20` | `PR-01` | `LnLean/Proofs/WaveH/H20.lean` | Model `acceptReceived? : Option AcceptChannel` on a local extension of `HandshakeState`, prove `recvAcceptChannel` sets it, and relate it to the existing boolean `acceptReceived` flag. |
| `H21` | `PR-01` | `LnLean/Proofs/WaveH/H21.lean` | Connect the stored accept payload to `KeyModelTargets.AdvertisesKey` and prove the strongest faithful key-registration theorem; keep transport attribution explicit. |
| `H22` | `PR-01` | `LnLean/Proofs/WaveH/H22.lean` | Add a proof-of-possession/registration model for `accept_channel.funding_pubkey`; prove attribution under the model or the sharp conditional contract, with the missing game stated exactly. |
| `H23` | `PR-01` | `LnLean/Proofs/WaveH/H23.lean` | Provide a non-vacuous accept-payload/registration witness and a complete honest open/accept/funding negotiation witness, all within the new model. |
| `H24` | `PR-01` | `LnLean/Proofs/WaveH/H24.lean` | Preserve and strengthen the negative result: two senders can emit the same `accept_channel` payload, so payload equality alone does not establish sender attribution. State the exact additional premise needed. |
| `H25` | `CH-01`, `CH-02` | `LnLean/Proofs/WaveH/H25.lean` | Build the actual `viewOfState` adapter at the rich commitment/sighash construction site and prove it agrees with the wire-view fields used by `SighashTargets`. Keep the adapter additive. |
| `H26` | `CH-01`, `CH-02` | `LnLean/Proofs/WaveH/H26.lean` | Apply the migrated consumer path at the downstream `CommitmentParams`/`commitmentOutputs` boundary; prove the migrated output list equals the legacy consumer list under the documented normal form. |
| `H27` | `CH-01`, `CH-02` | `LnLean/Proofs/WaveH/H27.lean` | Prove downstream net-output conservation/effective-fee accounting for the migrated construction (emitted + base fee + trimmed = funding), with the exact hypothesis boundary. |
| `H28` | `CH-01`, `CH-02` | `LnLean/Proofs/WaveH/H28.lean` | Retain the legacy-coverage failure at the actual downstream construction site: mechanize the counterexample that net migration alone does not preserve legacy coverage, and identify the sufficient normal-form premise. |
| `H29` | `L1-01`, `L1-07` | `LnLean/Proofs/WaveH/H29.lean` | Bridge the model `sigCheck`/`InterpreterLaws` signature check to the concrete vendored `Bitcoin.Crypto.Ecdsa.Verify.verifyImpl` for a constructed BIP 143 digest; keep the message/sighash and key-encoding premises explicit. |
| `H30` | `L1-01`, `L1-07` | `LnLean/Proofs/WaveH/H30.lean` | Instantiate the funding 2-of-2 spend at `txCheckerFor` with the concrete vendor ECDSA verifier; prove the positive branch and a wrong-key negative. |
| `H31` | `L1-02`, `L1-07` | `LnLean/Proofs/WaveH/H31.lean` | Instantiate the delayed `to_local` branch at `txCheckerFor` with the concrete vendor ECDSA verifier and the exact sequence context; prove the iff/refinement under the existing side conditions. |
| `H32` | `L1-02`, `L1-07` | `LnLean/Proofs/WaveH/H32.lean` | Instantiate the revocation `to_local` branch at `txCheckerFor` with the concrete vendor ECDSA verifier; prove the positive branch and the wrong-key/wrong-branch negatives. |
| `H33` | `L1-04` | `LnLean/Proofs/WaveH/H33.lean` | Model the missing anchor witness serialization bytes and prove the corrected anchor/commitment weight relation, including the retained `+8 WU` gap and the exact BOLT 3 fee-basis interpretation. |
| `H34` | `L1-05` | `LnLean/Proofs/WaveH/H34.lean` | Prove the 32-byte payment-preimage C1 model does not bind arbitrary 71-byte funding witness scripts; supply a concrete collision/injectivity counterexample or a domain-separated script commitment that closes the intended construction. |
| `H35` | `CONF-01` | `LnLean/Proofs/WaveH/H35.lean` | Add BigSize boundary vectors (`0`, `252`, `253`, `65535`, `65536`, and larger widths) with encode/decode round-trips and minimality/rejection theorems. |
| `H36` | `CONF-01` | `LnLean/Proofs/WaveH/H36.lean` | Add TLV unknown-type/value-minimality boundary cases and prove the model's acceptance/rejection behavior, keeping the two declared model gaps explicit. |
| `H37` | `CONF-01`, `CONF-03` | `LnLean/Proofs/WaveH/H37.lean` | Add transport/wire framing boundary cases around `65535`/`65536` bytes, including truncation, oversized payload, and the payload-only production decoder boundary. |
| `H38` | `CONF-01` | `LnLean/Proofs/WaveH/H38.lean` | Add at least 16 new deterministic conformance `decide` theorems over existing encoders/decoders across BigSize/TLV/framing, with stable references and no shared test-file edits. |
| `H39` | `RT-01`, `RT-02` | `LnLean/Proofs/WaveH/H39.lean` | Define an additive gossip-store epoch/replacement model over the canonical store and prove the basic epoch invariants and monotonicity facts. |
| `H40` | `RT-01`, `RT-02` | `LnLean/Proofs/WaveH/H40.lean` | Refine the canonical wrapper against the raw store over a realistic replacement/epoch sequence; prove the exact projection square or the sharp obstruction. |
| `H41` | `RT-01`, `RT-02` | `LnLean/Proofs/WaveH/H41.lean` | Prove supersession/rotation preservation across epochs: stale announcements remain rejected, current keys/announcements survive, and the canonical reachable invariant is preserved. |
| `H42` | `RT-01` | `LnLean/Proofs/WaveH/H42.lean` | Mechanize the raw-extension impossibility at an epoch boundary, or the sharpest true conditional refinement; preserve the existing raw non-refinement counterexample. |
| `H43` | `NET-01`, `SEC-01` | `LnLean/Proofs/WaveH/H43.lean` | State a concrete adversarial schedule/fairness model and prove one eventual-delivery/eventual-inclusion instance under explicit fairness and finite-delay premises. |
| `H44` | `SEC-01`, `CR-01` | `LnLean/Proofs/WaveH/H44.lean` | Strengthen the `Game`/`EventReduction`/`AdvantageReduction` interface: prove the bound arithmetic without assuming tightness, and state the exact remaining reduction obligation. |
| `H45` | `L1-06`, `NET-01` | `LnLean/Proofs/WaveH/H45.lean` | Add a concrete bounded-reorg/common-tip instance for the existing reorg result, or prove the sharp conditional transfer; keep deep-reorg failure separate. |
| `H46` | `OPS-01`, `OPS-04` | `scripts/waveh/verify-vendor-artifact.sh`, `docs/waveh/H46.md`, report | Add a checked vendor-snapshot artifact verifier (manifest, 119-file digest, prohibited absolute symlink) without committing the snapshot or changing the existing vendor/CI. |
| `H47` | `OPS-01`, `OPS-03` | `scripts/waveh/clean-checkout-dry-run.sh`, `docs/waveh/H47.md`, report | Produce a reproducible clean-checkout/source-gate dry-run script that distinguishes source checks from the explicit vendor-build skip; do not touch `main`, tags, or remotes. |
| `H48` | `OPS-02`, `OPS-03` | `docs/waveh/H48.md`, report | Update the release decision/checklist with the exact remaining human choices (license, vendor artifact publication, PR/main path) and a non-force integration/PR plan; do not invent a license or tag. |

## Parent integration protocol

1. Collect the 48 reports and inspect every module diff.
2. Reject fake proofs, silent assumptions, shared-file edits outside ownership,
   and any lane that used a forbidden construct.
3. Keep only green, sorry-free `WaveH/Hxx.lean` modules; delete failed Lean
   modules (their reports remain as evidence).
4. Update `scripts/check-final.py` expected file count, add all kept modules to
   `LnLean.lean`, and update the catalog/traceability/audit/docs in one parent
   commit.
5. Run the full gate from `docs/SWARM-LOOP.md`, including the exact `sorry`
   scan, catalog audit, conformance, anchors, vendor, and axiom audit.
6. Commit `[PROOF] integrate wave 8 ...` and `[STATUS] record wave 8 ...`.
7. Push non-force to `origin/repair/integrated` only if an authenticated token
   is available; otherwise record the local gate and leave `main` untouched.

## Success condition

A successful wave is not “48 new files.” It is: every retained module is
sorry-free and faithful, the full tree stays green, at least one open issue is
closed or materially narrowed, and every remaining gap is recorded with an
exact theorem, counterexample, or integration patch.
