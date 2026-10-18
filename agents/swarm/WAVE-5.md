# Wave 5 — bridge and completeness attack plan

**Base commit:** `74d6475` (`[STATUS] record proof-wave 4 gate HEAD`)
**Branch:** `repair/integrated`
**Catalog:** 48 proved / 0 statementOnly / 61 targets
**Full build at base:** 188 jobs, RC 0
**Roadmap:** `docs/OPEN-ISSUES.md`
**Protocol:** `docs/SWARM-LOOP.md`

Wave 4 added six modules and closed or mitigated several non-catalog gaps. Wave
5 attacks the gaps that wave 4 exposed. Eight lanes run in parallel with
exclusive files. No lane commits, pushes, edits `LnLean.lean`,
`Obligations.lean`, `Traceability.lean`, `AxiomAudit.lean`, the shared catalog,
or docs owned by another lane; the parent integrates and records the gate.

## Lanes

| Lane | Issue(s) | Owned files | Deliverable / acceptance |
|---|---|---|---|
| `S5-L1-INTERP` | `L1-01`, `L1-02`, `L1-07` | `LnLean/Proofs/Bitcoin/SpendTargets.lean`, new `LnLean/Proofs/Bitcoin/InterpreterBridgeTargets.lean`, report | Import the vendored interpreter modules if they build; connect the `SpendTargets` stack/serializer model to `evalScriptBytes`/`verifyWitnessProgram`/`checkMultiSig`; discharge or precisely narrow `ConsensusSpendBridge`. If the vendored interpreter cannot build, prove the strongest correspondence lemmas and record the exact missing vendor dependency. |
| `S5-CH-GROSSNET` | `CH-03`, `CH-01`, `CH-02` | `LnLean/Channel/Commitment.lean`, new `LnLean/Proofs/Channel/CommitmentGrossNetTargets.lean`, report | Add `netAmountSat`/`trimmedSat`/`effectiveFeeSat` with defaults preserving existing record literals; switch the dust test to net; migrate construction sites; prove the canonical legacy refinement and conservation without the zero-dust workaround. |
| `S5-PR-SIGHASH` | `PR-02`, `PR-01` | `LnLean/Protocol/Messages.lean`, new `LnLean/Proofs/Channel/SighashTargets.lean`, report | Add a BOLT 3 commitment sighash serializer model and prove that `CommitmentSignedFull` digests/signatures are derived from it under C3, rather than supplied; add an honest-signer/key-binding construction for the funding contract where feasible. Do not edit `Commitment.lean`; import it. |
| `S5-CONF-DIFF` | `CONF-02`, `CONF-01` | `tests/conformance/**`, `scripts/check-conformance.py`, new `LnLean/Proofs/ConformanceDiffTargets.lean`, report | Reconcile the payload-only model length with the BOLT transport frame; add message-framing vectors and pinned rust-lightning differential fixtures. Keep the checker runnable without a network; document any fixture that cannot be regenerated. |
| `S5-MODEL-STEP` | `MODEL-02` | `LnLean/Channel/State.lean`, new `LnLean/Proofs/Channel/StateTransitionTargets.lean`, report | Add the missing `Step.update_add_htlc` (and success/fail if needed) transition; prove affordability/conservation from the constructor, preserving existing transition semantics and E37 counterexamples. |
| `S5-L1-FUNDING` | `L1-03`, `L1-05` | `LnLean/Protocol/Handshake.lean`, `LnLean/Bitcoin/Funding.lean`, new `LnLean/Proofs/Bitcoin/FundingLinkTargets.lean`, report | Construct the funding witness-script hash link from handshake data instead of assuming `FundingScriptHashLinked`; keep the finite C1 admission and prove the strongest construction/refinement result. |
| `S5-GOSSIP-ATTR2` | `RT-01` | `LnLean/Routing/Gossip.lean`, new `LnLean/Proofs/Routing/GossipKeyConsistencyTargets.lean`, report | Add direction-keyed update attribution, a `NodeId → PubKey` consistency invariant, and announcement deduplication. Preserve raw `applyGossip`, the wave-4 attributed transition, and all existing counterexamples. |
| `S5-SEC-LIMITS` | `CR-01`, `SEC-01` | new `docs/CRYPTO-LIMITS.md`, new `LnLean/Proofs/Security/SecurityGameTargets.lean`, report | Write a precise computational-security limits document and define a game/assumption interface without claiming a reduction. The Lean module should state the assumed advantage bounds and the exact theorem that would be needed for a reduction, with no fake proof. |

## Lane rules

- Read `docs/OPEN-ISSUES.md`, `docs/ASSUMPTIONS.md`, `docs/THEOREM-INDEX.md`,
  the relevant prior reports, and the owned modules first.
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
  `agents/reports/swarm5/S5-<LANE>.md`.
- If a requested change would touch a forbidden shared file, implement the
  additive part in your owned module and report the exact integration patch.
