# Phase-C2 lanes

This branch continues the phase-C work from the second box
(`sensitive-isolated-box-2`, `172.31.96.235`) while the first box may keep
working on `main`.

* Worktree: `/home/ubuntu/ln-lean-phasec2`
* Branch: `phase-c2`, based on `phase-c` (`de31d60`)
* Parent lane: `phase-c` closed 20/25 sorries; the five remaining ones are
  refuted statements with counterexamples. C2 repairs those model claims and
  adds independent proof modules under `LnLean/Proofs/PhaseC2/`.

## Rules

1. Every new module lives under `LnLean/Proofs/PhaseC2/` and is self-contained.
2. Only the owner edits the target file. No edits to `lakefile.lean`,
   `LnLean.lean`, `docs/`, `refs/`, or `vendor/`.
3. `sorry` is permitted in C2 modules only with an adjacent
   `-- OBLIGATION: PC2-...` marker. At least one named theorem per module must
   be fully proved.
4. A false statement is repaired by proving a counterexample and keeping the
   strongest true conditional form; removing a false theorem is allowed only
   with that counterexample present.
5. Commit only the target file and `agents/reports/PCxx.md`.

## Ownership

| Agent | Target | Kind |
|---|---|---|
| PC17 | `LnLean/Proofs/Bitcoin/FundingProps.lean` | repair refuted claim |
| PC18 | `LnLean/Proofs/Channel/ReserveProps.lean` | repair refuted claim |
| PC19 | `LnLean/Proofs/Routing/GossipProps.lean` | repair three refuted claims |
| PC20 | `LnLean/Proofs/PhaseC2/GlobalConservation.lean` | new |
| PC21 | `LnLean/Proofs/PhaseC2/CommitmentAlgebra.lean` | new |
| PC22 | `LnLean/Proofs/PhaseC2/HTLCPartition.lean` | new |
| PC23 | `LnLean/Proofs/PhaseC2/HTLCUniqueIds.lean` | new |
| PC24 | `LnLean/Proofs/PhaseC2/RevocationNumber.lean` | new |
| PC25 | `LnLean/Proofs/PhaseC2/PenaltyDoubleSpend.lean` | new |
| PC26 | `LnLean/Proofs/PhaseC2/CltvAccumulation.lean` | new |
| PC27 | `LnLean/Proofs/PhaseC2/OnionLayers.lean` | new |
| PC28 | `LnLean/Proofs/PhaseC2/MPPPrefix.lean` | new |
| PC29 | `LnLean/Proofs/PhaseC2/InvoiceBinding.lean` | new |
| PC30 | `LnLean/Proofs/PhaseC2/FeatureClosure.lean` | new |
| PC31 | `LnLean/Proofs/PhaseC2/ReestablishRange.lean` | new |
| PC32 | `LnLean/Proofs/PhaseC2/LivenessDelivery.lean` | new |
| PC33 | `LnLean/Proofs/PhaseC2/FundingBridge.lean` | new |
| PC34 | `LnLean/Proofs/PhaseC2/CommitmentBridge.lean` | new |
| PC35 | `LnLean/Proofs/PhaseC2/HTLCBridge.lean` | new |
| PC36 | `LnLean/Proofs/PhaseC2/PenaltyBridge.lean` | new |
