# Wave 7 — sequence context, preimage equality, consumer migration, and fold refinement

**Status:** complete; all eight lanes integrated and gated at `b48d041`.

**Launch commit:** `3180581` (`[STATUS] define and launch wave 7 residual lanes`)
**Branch:** `repair/integrated`
**Catalog at launch:** 48 proved / 0 statementOnly / 73 targets
**Catalog at integration:** 48 proved / 0 statementOnly / 79 targets
**Full build at integration:** 233 jobs, RC 0
**Axiom audit at integration:** 194 theorems
**Roadmap:** `docs/OPEN-ISSUES.md`
**Protocol:** `docs/SWARM-LOOP.md`

Wave 6 closed the conditional BIP 143, revocation, five-field gross/net,
view-binding, canonical-gossip, and transport-promotion gaps. Wave 7 attacks the
remaining codeable gaps: decoded sequence/policy context, exact preimage
byte-equality to the vendor hash input, legacy commitment-consumer migration,
folding/refining the update and dance layers, raw gossip-store refinement, live
rust-lightning conformance, `open_channel`/funding-key authentication, and a
secret-key/signer model.

Eight lanes run in parallel with exclusive files. No lane commits, pushes,
edits `LnLean.lean`, `Obligations.lean`, `Traceability.lean`,
`AxiomAudit.lean`, the shared catalog, or docs owned by another lane; the
parent integrates and records the gate.

## Lanes

| Lane | Issue(s) | Owned files | Deliverable / acceptance |
|---|---|---|---|
| `S7-L1-SEQUENCE` | `L1-02`, `L1-07` | new `LnLean/Proofs/Bitcoin/SequenceContextTargets.lean`, report | Connect decoded delay, non-negativity/disable-bit, `checkSequenceDef`, policy flags, and the concrete EC/transaction-validity boundary to the vendored positive-branch bridge. Prove the strongest faithful sequence/refinement theorem; do not edit the bridge modules. |
| `S7-PR-PREIMAGE` | `PR-05`, `PR-02` | `LnLean/Proofs/Channel/SighashTargets.lean`, `LnLean/Bitcoin/Sighash.lean`, report | Prove `Bip143Preimage.preimageBytes` equals the vendored `bip143MsgL`/`LnLean.Bitcoin.Sighash.encode` for the modelled fields, including script/outpoint and hash byte order; add vectors. Keep all existing §12 results and scope notes. |
| `S7-CH-CONSUMER` | `CH-01`, `CH-02` | `LnLean/Channel/Commitment.lean`, new `LnLean/Proofs/Channel/CommitmentConsumerTargets.lean`, report | Add the legacy-to-rich/net consumer migration path and prove canonical refinement at the actual consumer boundary. Decide/report the `trimmedTotalSat` naming question. If a downstream construction site outside ownership needs an edit, record the exact patch. |
| `S7-MODEL-FOLD` | `MODEL-02`, `MODEL-03` | `LnLean/Channel/State.lean`, new `LnLean/Proofs/Channel/ProtocolEventFoldTargets.lean`, report | Either fold `UpdateStep`/`DanceStep` into `ProtocolEvent`/`Step` with the coordinated liveness/liquidity/D14/F03 migration, or prove a formal refinement/embedding from the additive layers into the existing folds. Preserve all counterexamples and keep the strongest true form if the literal fold breaks downstream invariants. |
| `S7-RT-RAW` | `RT-01` | `LnLean/Routing/Gossip.lean`, new `LnLean/Proofs/Routing/GossipRawRefinementTargets.lean`, report | Refine raw `applyGossip` to the canonical admission/store path, or deprecate raw insertion behind a proved wrapper. Keep the conflicting-announcement counterexample and the canonical reachable-state theorems unchanged. |
| `S7-CONF-LIVE` | `CONF-02`, `CONF-01` | `tests/conformance/**`, `scripts/check-conformance.py`, `LnLean/Proofs/ConformanceDiffTargets.lean`, report | Complete the pinned cargo cache/live harness where possible and run `cargo test --offline`; compare live rust-lightning output with the committed fixtures. If the cache is unavailable, add a deterministic, reproducible live-harness path and do not claim a live run. Keep the current offline/deterministic checks green. |
| `S7-L1-FUNDING-AUTH` | `L1-03` | `LnLean/Bitcoin/Funding.lean`, `LnLean/Protocol/Handshake.lean`, new `LnLean/Proofs/Bitcoin/FundingAuthTargets.lean`, report | Add `open_channel` coverage and funding-key authentication, extending the handshake construction without weakening the hash link. Prove the strongest faithful authentication/construction theorem and retain the finite C1 admission. |
| `S7-PR-KEY` | `PR-01` | new `LnLean/Crypto/KeyModel.lean`, new `LnLean/Proofs/Crypto/KeyModelTargets.lean`, report | Add a secret-key/key-generation model and connect `accept_channel.funding_pubkey` to the signer key, or prove the sharpest conditional contract. Do not assume C3 gives key attribution; retain the counterexample/negative result. |

## Integration result

All eight lanes returned sorry-free results and were integrated with the
parent-owned catalog, audit, and docs updates.

- Seven new Lean files: `SequenceContextTargets`, `CommitmentConsumerTargets`,
  `ProtocolEventFoldTargets`, `GossipRawRefinementTargets`,
  `FundingAuthTargets`, `KeyModelTargets`, and `Crypto/KeyModel`.
- Six catalog rows strengthened from 73 to 79 targets; `AxiomAudit` extended
  from 163 to 194 theorems.
- Closed `CH-01`, `RT-01`, `CONF-02`, `MODEL-02`, and `MODEL-03`.
- Narrowed `L1-02`/`L1-07` to the `TxValidation.Full` transfer,
  `PR-05` to the `HtlcWire` instantiation, `L1-03` to the `Messages.openChannel`
  wire patch, and `PR-01` to the `AcceptChannel`/registration path.
- Two strong negative results are retained: raw gossip insertion is not a
  canonical refinement, and the literal unguarded `ProtocolEvent` fold is
  impossible without falsifying retained counterexamples.
- Live conformance is now a real pinned run: 26/26 BigSize, 3/3 TLV, 4/4 wire,
  with a SHA-256-pinned transcript and forged-transcript mutation control.

## Lane rules

- Read `docs/OPEN-ISSUES.md`, `agents/swarm/WAVE-7.md`,
  `docs/ASSUMPTIONS.md`, `docs/THEOREM-INDEX.md`, the wave-6 reports, and the
  owned modules first.
- No `sorry`, `axiom`, `admit`, `native_decide`, `unsafe`, or
  `@[implemented_by]`. Allowed axioms: `propext`, `Quot.sound`,
  `Classical.choice`.
- Preserve mechanized counterexamples and strongest true conditional forms.
  A narrowed/blocked result is acceptable and valuable; a fake proof is not.
- Build only your module(s) under the shared lock:
  `LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock lake build <Module>`.
- Do not run the full `lake build`, `collect-obligations.py`,
  `collect-anchors.py`, or any Git write command.
- Report exact signatures, build result, axiom result, forbidden-construct
  scan, scope caveats, integration steps, and blockers in
  `agents/reports/swarm7/S7-<LANE>.md`.
- If a requested change would touch a forbidden shared file, implement the
  additive part in your owned module and report the exact integration patch.
