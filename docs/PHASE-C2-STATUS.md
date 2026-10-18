# Phase C2 status — model repair and independent proof modules

**Branch:** `phase-c2` (based on `phase-c`)
**Worktree:** `/home/ubuntu/ln-lean-phasec2`
**Agents:** PC17–PC36 plus three targeted repair agents
**Base result:** phase C closed 20/25 proof-side `sorry` sites; the five
remaining ones were refuted unconditional statements with mechanized
counterexamples.

## Result

Phase C2 does two things:

1. It repairs the five refuted statements by removing the false
   unconditional theorem and retaining the counterexample and the strongest
   true conditional theorem. After the repair the repository has **zero
   actual `sorry` terms** (`grep -RIn '^[[:space:]]*sorry[[:space:]]*$'`
   returns nothing). Retained `-- OBLIGATION:` markers are traceability
   annotations for proved-or-replaced claims, not open proofs.
2. It adds independent proof modules under `LnLean/Proofs/PhaseC2/` for
   multi-channel conservation, commitment output algebra, HTLC partitioning
   and id freshness, revocation numbering, penalty exclusivity, CLTV
   accumulation, onion layers, MPP prefix sums, invoice binding, feature
   closure, reestablish ranges, end-to-end liveness, and the four L1 script
   bridges.

## Repairs

| File | Action |
|---|---|
| `Proofs/Bitcoin/FundingProps.lean` | removed false `witnessScript_parse_eq_none`; kept `witnessScript_parse_ne_none_counterexample` and `witnessScript_parse_eq_none_of_wellFormed` |
| `Proofs/Channel/ReserveProps.lean` | removed false `committed_update_preserves_ledger`; kept the counterexample, `committed_update_preserves_ledger_of_le`, and the new deficit-accounting theorem |
| `Proofs/Routing/GossipProps.lean` | removed the three refuted admission claims; kept all three counterexamples and the three `*_of_*` conditional forms |

## New modules

`PhaseC2/` contains: `GlobalConservation`, `CommitmentAlgebra`,
`HTLCPartition`, `HTLCUniqueIds`, `RevocationNumber`, `PenaltyDoubleSpend`,
`CltvAccumulation`, `OnionLayers`, `MPPPrefix`, `InvoiceBinding`,
`FeatureClosure`, `ReestablishRange`, `LivenessDelivery`, `FundingBridge`,
`CommitmentBridge`, `HTLCBridge`, `PenaltyBridge`. The bridge modules keep
L1 acceptance as an explicit structure field, never an axiom.

## Gate

```sh
export PATH=/dev/shm/btc/elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
cd /home/ubuntu/ln-lean-phasec2
flock -w 900 /tmp/ln-build.lock lake build            # 77 jobs, RC 0
flock -w 900 /tmp/ln-build.lock lake build LnLean.Proofs.PhaseC2  # aggregator
./scripts/check-c2.sh                                  # policy gate
```

The aggregator imports all 17 modules and builds 94 jobs. The actual final
gate is `files=87 obligations=25 sorry_in_proofs=0`, `check: OK`, and
`grep -RIn '^[[:space:]]*sorry[[:space:]]*$' LnLean --include='*.lean'`
returns nothing. The aggregator is not added to the wave-A root module.

## Reports

`agents/reports/PC17.md` … `agents/reports/PC36.md`. Every report records the
theorem table, exact build RC, `sorry` count, and axioms used.
