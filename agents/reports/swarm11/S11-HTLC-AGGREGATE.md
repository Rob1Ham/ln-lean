# S11-HTLC-AGGREGATE — aggregate multi-HTLC second-stage coverage and spending

**Lane:** `S11-HTLC-AGGREGATE`  
**Branch:** `repair/integrated`  
**Module:** `LnLean/Proofs/Channel/HtlcAggregateTargets.lean` (new, 1024 lines)  
**Report:** `agents/reports/swarm11/S11-HTLC-AGGREGATE.md`  
**Issues addressed:** `PR-02`, `PR-05`, `CH-01` (aggregate extension); integration
hook to a future `LN-PR-004` / `LN-CH-*` catalog row.

## 1. Scope and model

The new module owns exactly one Lean file and one report.  It does not edit root
imports, the catalog, traceability, audit lists, docs, scripts, or tests.  It
imports `LnLean.Channel.HTLC` and
`LnLean.Proofs.Channel.CoverageWitnessTargets` and builds additively on the
wave-10 per-HTLC coverage witness.

The model has four layers:

1. **Aggregate rows.** `HtlcRecordRef` (line 82) carries a commitment identity,
   a direction-tagged BOLT 2 id (`HTLCTag = Direction × Nat`), a millisatoshi
   amount, `cltv_expiry`, a `ScriptPubKey` identity, a commitment txid, an
   output index, and a lifecycle tag.  `HtlcRecordRef.SpendTarget` (line 151)
   is the previous outpoint plus script identity a second-stage spend consumes.
2. **Coverage projection.** `CoverageRow` (line 224) is the commitment-output
   projection.  `Aggregate.coverage` (line 269) is the list projection and
   `Aggregate.coverageValue` (line 279) its satoshi sum.
3. **Separation.** `SecondStageSpend` (line 410) targets one
   `SpendTarget`; `Aggregate.NoSpendAliasing` (line 298) is the explicit
   collision-freedom premise.
4. **Fee/weight.** `AggregateTx` (line 586) adds base/per-input/per-output
   weight, input/output value, and paid fee.  `weight`, `requiredFee`,
   `FeeSufficient`, and `Funded` are lines 607–624.

The model is structural.  It does not execute scripts, construct BIP 143
digests, claim signature unforgeability, or claim consensus validity.  Scripts
are opaque identities and fee/weight numbers are parameters.

## 2. Key results

| Result | Name | Line |
|---|---|---:|
| Aggregate coverage is the per-HTLC list | `Aggregate.aggregate_coverage_projection` | 370 |
| Aggregate value is the per-HTLC sum | `Aggregate.coverageValue_eq_sum` | 328 |
| Distinct commitments separate records | `Aggregate.distinct_commitments_separate` | 388 |
| No-double-spend under no aliasing | `no_double_spend_of_noAliasing` | 456 |
| Aliasing is necessary | `same_spend_distinct_records_imp_aliasing` | 466 |
| Mechanized aliasing counterexample | `aliasing_double_spend_witness` | 547 |
| No selector on the aliased aggregate | `no_spend_selector_on_aliased_aggregate` | 559 |
| Aggregate weight formula | `AggregateTx.weight_eq` | 626 |
| Required fee boundary | `AggregateTx.not_funded_of_output_add_fee_gt` | 691 |
| Concrete rejected aggregate | `rejectedAggregate` | 867 |
| Concrete funded variant | `fundedTx_ok` | 879 |
| Legacy wire does not carry aggregate coverage | `legacy_wire_does_not_carry_aggregate_coverage` | 970 |
| Bundled lane result | `htlc_aggregate_summary` | 1001 |

### 2.1 Aggregate coverage theorem

`aggregate_coverage_projection` states, for an aggregate `a`:

* `a.coverage = a.records.map coverageOf`;
* `a.coverage.Nodup`;
* `a.coverage.length = a.records.length`;
* `a.coverageValue = (a.records.map (fun r => r.amountSat)).sum`;
* rows from distinct commitment ids have distinct coverage rows.

The explicit hypotheses are `a.NoDuplication` (line 288) and
`a.DistinctCommitments` (line 293).  `NoDuplication` is load-bearing:
`duplicateAggregate_not_noDuplication` (line 812) proves that repeating a row
duplicates the coverage projection.  `DistinctCommitments` is load-bearing for
the cross-commitment reading: `distinctCommitments_separate_witness` (line 798)
and `distinctCommitments_separate` identify rows with equal commitment ids.

### 2.2 Separation / no-double-spend theorem

`spend_target_separates_of_noAliasing` (line 447) and
`no_double_spend_of_noAliasing` (line 456) prove:

```text
a.NoSpendAliasing ->
r1 ∈ a.records -> r2 ∈ a.records ->
s.Spends r1 -> s.Spends r2 -> r1 = r2
```

The converse direction is explicit:
`same_spend_distinct_records_imp_aliasing` (line 466) says two distinct rows
covered by one spend satisfy `Aliased r1 r2`.  The aliasing counterexample is
concrete:

* `aliasRecordA` (line 499) is 1000 msat, local id 0, output index 0;
* `aliasRecordB` (line 511) is 2000 msat, same commitment outpoint/script;
* `alias_records_distinct` (line 519) and `alias_records_same_target` (line
  523) show the rows are distinct but share one target;
* `alias_spend_covers_both` (line 532) and
  `aliasing_double_spend_witness` (line 547) show one spend covers both;
* `aliasAggregate_not_noSpendAliasing` (line 537) and
  `no_spend_selector_on_aliased_aggregate` (line 559) show the premise cannot
  be dropped and no target-to-record selector exists on that aggregate.

### 2.3 Fee/weight accounting and boundary

`AggregateTx.weight` is
`baseWeight + records.length * (inputWeight + outputWeight)` and
`requiredFee = feeForWeight r weight`.  `Funded` is
`outputValueSat + requiredFee.val <= inputValueSat`.

`boundaryTx` (line 831) has two rows, `baseWeight = 500`,
`inputWeight = outputWeight = 100`, hence weight `900`; at feerate `1000`
msat/kW the required fee is `900` msat.  It spends 3 sat and produces 3 sat,
so `boundaryTx_not_funded` (line 850) and `rejectedAggregate` (line 867)
prove rejection, and `boundaryTx_fee_insufficient` (line 858) proves the paid
fee is insufficient.  `fundedTx` (line 875) raises the input value to 1000 sat
and pays 900 msat; `fundedTx_ok` (line 879) and
`funded_and_rejected_same_rows` (line 891) show the same rows can be funded,
isolating the failure to the accounting boundary.

### 2.4 Non-vacuity

`witnessAggregate` (line 740) has two distinct rows
(`witnessRecordA` line 717, `witnessRecordB` line 728) with different
directions, ids, amounts, expiries, and scripts.  It satisfies
`witnessAggregate_noDuplication` (line 744), has two coverage rows (line 749),
coverage value `3` sat (line 755), and
`witnessAggregate_nonvacuous` (line 761).  The cross-commitment witness
`distinctCommitmentAggregate` (line 772) is the non-vacuous instance for the
distinct-commitment premise.

### 2.5 Wave-10 boundary preserved

`aggregateOfFull` (line 918) extracts aggregate rows from a full
`CommitmentSignedFull`; the legacy wire record is still
`CommitmentSigned`.  `aggregate_wire_boundary_witness` (line 944) shows two
full records with the same legacy projection but different aggregate
coverage, and `no_legacy_only_aggregate_coverage_decoder` (line 954) proves no
function from `CommitmentSigned` alone is correct for every full record.
`legacy_wire_does_not_carry_aggregate_coverage` (line 970) bundles that
negative.  This is exactly the wave-10 boundary: aggregate coverage needs an
out-of-band/full-record source; the legacy wire is not claimed to carry it.

## 3. Assumptions and boundaries

* `Aggregate.NoDuplication`: no two aggregate rows project to the same
  coverage row.  Not implied by the bare list; refuted for
  `duplicateAggregate` (line 812).
* `Aggregate.DistinctCommitments`: commitment ids are pairwise distinct.  This
  is the cross-commitment reading; it is deliberately stronger than a single
  commitment's HTLC list.
* `Aggregate.NoSpendAliasing`: the second-stage target map is injective on
  aggregate rows.  Dropping it is unsound (line 547).
* Script identity is an explicit parameter (`ScriptPubKey`); the module does
  not derive it from keys or payment hashes.
* Fee/weight constants are parameters; the module does not claim a consensus
  weight estimator.  `Funded`/`FeeSufficient` are accounting predicates, not
  `TxValidation.Full`.
* No production `CommitmentTx` consumer is claimed; `CH-01` remains at the
  proof-layer adapter boundary.
* The legacy `commitment_signed` wire is not sufficient for aggregate
  coverage.

## 4. Build and audits

Build command (lane requirement):

```text
cd /home/ubuntu/ln-lean-repair
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Proofs.Channel.HtlcAggregateTargets
```

Result: **success**, `54` jobs, RC `0`, no errors and no warnings from the new
module.

Forbidden-token scan (the six restricted Lean tokens required by the lane) on
the new module: **0 hits**.

Axiom audit (`#print axioms`) on **every public theorem** in the new module:
**74/74 audited**, no unexpected constants.  Observed sets are subsets of
`{propext, Quot.sound, Classical.choice}`; 35 theorems depend on no axioms
and 39 depend on a subset.  The largest set,
`{propext, Classical.choice, Quot.sound}`, appears only on
`not_noSpendAliasing_iff_exists_aliased` (line 473).  The two headline
theorems report `{propext, Quot.sound}`
(`htlc_aggregate_summary`, line 1001) and `{propext}`
(`no_legacy_only_aggregate_coverage_decoder`, line 954).

## 5. Theorem inventory (74 public theorems)

### §1 aggregate rows and projections

| Line | Theorem |
|---:|---|
| 168 | `LnLean.Proofs.Channel.HtlcAggregate.HtlcRecordRef.direction_eq_tag_fst` |
| 171 | `LnLean.Proofs.Channel.HtlcAggregate.HtlcRecordRef.htlcId_eq_tag_snd` |
| 174 | `LnLean.Proofs.Channel.HtlcAggregate.HtlcRecordRef.amountSat_eq` |
| 177 | `LnLean.Proofs.Channel.HtlcAggregate.HtlcRecordRef.outpoint_eq` |
| 182 | `LnLean.Proofs.Channel.HtlcAggregate.HtlcRecordRef.spendTarget_eq` |
| 185 | `LnLean.Proofs.Channel.HtlcAggregate.HtlcRecordRef.toCommitmentHtlcOutput_direction` |
| 188 | `LnLean.Proofs.Channel.HtlcAggregate.HtlcRecordRef.toCommitmentHtlcOutput_amountSat` |
| 191 | `LnLean.Proofs.Channel.HtlcAggregate.HtlcRecordRef.toCommitmentHtlcOutput_cltvExpiry` |
| 194 | `LnLean.Proofs.Channel.HtlcAggregate.HtlcRecordRef.toCommitmentHtlcOutput_state` |
| 199 | `LnLean.Proofs.Channel.HtlcAggregate.HtlcRecordRef.ext_iff` |
| 242 | `LnLean.Proofs.Channel.HtlcAggregate.CoverageRow.key_eq` |
| 245 | `LnLean.Proofs.Channel.HtlcAggregate.CoverageRow.valueSat_eq` |

### §2 aggregate coverage projection

| Line | Theorem |
|---:|---|
| 306 | `LnLean.Proofs.Channel.HtlcAggregate.Aggregate.coverage_eq_map` |
| 309 | `LnLean.Proofs.Channel.HtlcAggregate.Aggregate.perHtlcCoverage_eq_map` |
| 315 | `LnLean.Proofs.Channel.HtlcAggregate.Aggregate.aggregateCoverage_eq_perHtlcCoverage` |
| 318 | `LnLean.Proofs.Channel.HtlcAggregate.Aggregate.coverage_length_eq` |
| 322 | `LnLean.Proofs.Channel.HtlcAggregate.Aggregate.perHtlcCoverage_length_eq` |
| 328 | `LnLean.Proofs.Channel.HtlcAggregate.Aggregate.coverageValue_eq_sum` |
| 339 | `LnLean.Proofs.Channel.HtlcAggregate.Aggregate.coverageValue_eq_outputValue` |
| 346 | `LnLean.Proofs.Channel.HtlcAggregate.Aggregate.coverage_append` |
| 352 | `LnLean.Proofs.Channel.HtlcAggregate.Aggregate.coverage_nodup_of_noDuplication` |
| 357 | `LnLean.Proofs.Channel.HtlcAggregate.Aggregate.coverage_length_eq_of_noDuplication` |
| 370 | `LnLean.Proofs.Channel.HtlcAggregate.Aggregate.aggregate_coverage_projection` |
| 388 | `LnLean.Proofs.Channel.HtlcAggregate.Aggregate.distinct_commitments_separate` |

### §3 separation and aliasing

| Line | Theorem |
|---:|---|
| 422 | `LnLean.Proofs.Channel.HtlcAggregate.SecondStageSpend.spends_target_eq` |
| 425 | `LnLean.Proofs.Channel.HtlcAggregate.SecondStageSpend.spends_of_target_eq` |
| 429 | `LnLean.Proofs.Channel.HtlcAggregate.SecondStageSpend.spends_of_spends_of_target_eq` |
| 441 | `LnLean.Proofs.Channel.HtlcAggregate.aliased_iff` |
| 447 | `LnLean.Proofs.Channel.HtlcAggregate.spend_target_separates_of_noAliasing` |
| 456 | `LnLean.Proofs.Channel.HtlcAggregate.no_double_spend_of_noAliasing` |
| 466 | `LnLean.Proofs.Channel.HtlcAggregate.same_spend_distinct_records_imp_aliasing` |
| 473 | `LnLean.Proofs.Channel.HtlcAggregate.not_noSpendAliasing_iff_exists_aliased` |
| 519 | `LnLean.Proofs.Channel.HtlcAggregate.alias_records_distinct` |
| 523 | `LnLean.Proofs.Channel.HtlcAggregate.alias_records_same_target` |
| 532 | `LnLean.Proofs.Channel.HtlcAggregate.alias_spend_covers_both` |
| 537 | `LnLean.Proofs.Channel.HtlcAggregate.aliasAggregate_not_noSpendAliasing` |
| 547 | `LnLean.Proofs.Channel.HtlcAggregate.aliasing_double_spend_witness` |
| 559 | `LnLean.Proofs.Channel.HtlcAggregate.no_spend_selector_on_aliased_aggregate` |
| 571 | `LnLean.Proofs.Channel.HtlcAggregate.record_distinctness_not_spend_separation` |

### §4 fee and weight accounting

| Line | Theorem |
|---:|---|
| 626 | `LnLean.Proofs.Channel.HtlcAggregate.AggregateTx.weight_eq` |
| 634 | `LnLean.Proofs.Channel.HtlcAggregate.AggregateTx.weight_empty` |
| 640 | `LnLean.Proofs.Channel.HtlcAggregate.AggregateTx.weight_append_singleton` |
| 650 | `LnLean.Proofs.Channel.HtlcAggregate.AggregateTx.requiredFee_val` |
| 654 | `LnLean.Proofs.Channel.HtlcAggregate.AggregateTx.requiredFee_nonneg` |
| 658 | `LnLean.Proofs.Channel.HtlcAggregate.AggregateTx.requiredFee_mono_weight` |
| 664 | `LnLean.Proofs.Channel.HtlcAggregate.AggregateTx.feeSufficient_mono_paid` |
| 670 | `LnLean.Proofs.Channel.HtlcAggregate.AggregateTx.not_feeSufficient_of_lt` |
| 678 | `LnLean.Proofs.Channel.HtlcAggregate.AggregateTx.funded_iff` |
| 684 | `LnLean.Proofs.Channel.HtlcAggregate.AggregateTx.outputValue_le_input_of_funded` |
| 691 | `LnLean.Proofs.Channel.HtlcAggregate.AggregateTx.not_funded_of_output_add_fee_gt` |
| 701 | `LnLean.Proofs.Channel.HtlcAggregate.AggregateTx.insufficient_fee_not_feeSufficient` |

### §5 witnesses and rejected aggregate

| Line | Theorem |
|---:|---|
| 744 | `LnLean.Proofs.Channel.HtlcAggregate.witnessAggregate_noDuplication` |
| 749 | `LnLean.Proofs.Channel.HtlcAggregate.witnessAggregate_coverage_length` |
| 755 | `LnLean.Proofs.Channel.HtlcAggregate.witnessAggregate_coverageValue` |
| 761 | `LnLean.Proofs.Channel.HtlcAggregate.witnessAggregate_nonvacuous` |
| 778 | `LnLean.Proofs.Channel.HtlcAggregate.distinctCommitmentAggregate_distinct` |
| 784 | `LnLean.Proofs.Channel.HtlcAggregate.distinctCommitmentAggregate_noDuplication` |
| 790 | `LnLean.Proofs.Channel.HtlcAggregate.distinctCommitmentAggregate_rows_distinct` |
| 798 | `LnLean.Proofs.Channel.HtlcAggregate.distinctCommitments_separate_witness` |
| 812 | `LnLean.Proofs.Channel.HtlcAggregate.duplicateAggregate_not_noDuplication` |
| 819 | `LnLean.Proofs.Channel.HtlcAggregate.duplicateAggregate_lengths` |
| 841 | `LnLean.Proofs.Channel.HtlcAggregate.boundaryTx_weight` |
| 845 | `LnLean.Proofs.Channel.HtlcAggregate.boundaryTx_requiredFee` |
| 850 | `LnLean.Proofs.Channel.HtlcAggregate.boundaryTx_not_funded` |
| 858 | `LnLean.Proofs.Channel.HtlcAggregate.boundaryTx_fee_insufficient` |
| 867 | `LnLean.Proofs.Channel.HtlcAggregate.rejectedAggregate` |
| 879 | `LnLean.Proofs.Channel.HtlcAggregate.fundedTx_ok` |
| 891 | `LnLean.Proofs.Channel.HtlcAggregate.funded_and_rejected_same_rows` |

### §6 legacy-wire boundary and summary

| Line | Theorem |
|---:|---|
| 922 | `LnLean.Proofs.Channel.HtlcAggregate.aggregateOfFullWith_coverage_length` |
| 931 | `LnLean.Proofs.Channel.HtlcAggregate.aggregateOfFull_witnessA_coverage_ne_witnessB` |
| 944 | `LnLean.Proofs.Channel.HtlcAggregate.aggregate_wire_boundary_witness` |
| 954 | `LnLean.Proofs.Channel.HtlcAggregate.no_legacy_only_aggregate_coverage_decoder` |
| 970 | `LnLean.Proofs.Channel.HtlcAggregate.legacy_wire_does_not_carry_aggregate_coverage` |
| 1001 | `LnLean.Proofs.Channel.HtlcAggregate.htlc_aggregate_summary` |



## 6. Integration notes and recommended targets

* Add the module to the root import/catalog in the **parent** integration
  step; this lane intentionally did not edit `LnLean.lean`, the catalog,
  traceability, audit, docs, scripts, or tests.
* Suggested catalog row `LN-PR-004` (aggregate multi-HTLC coverage):
  `Aggregate.aggregate_coverage_projection`,
  `Aggregate.coverageValue_eq_sum`,
  `legacy_wire_does_not_carry_aggregate_coverage`.
* Suggested `LN-CH-005` (aggregate second-stage separation):
  `no_double_spend_of_noAliasing`,
  `same_spend_distinct_records_imp_aliasing`,
  `aliasing_double_spend_witness`.
* Suggested `LN-CH-006` (aggregate second-stage fee/weight boundary):
  `AggregateTx.weight_eq`, `AggregateTx.not_funded_of_output_add_fee_gt`,
  `rejectedAggregate`, `fundedTx_ok`.
* Keep `PR-02`'s scope note: per-HTLC coverage needs the full-record/witness
  source.  This module does not claim that the legacy wire carries aggregate
  coverage and does not close `PR-02` for a production decoder.
* Keep `PR-05`'s wire-byte work separate: this module adds no new sighash
  preimage or vendor-encoder theorem.
* Keep `CH-01`'s caveat: no production `CommitmentTx` consumer is introduced.
* The fee/weight theorem is an accounting model.  It is not a
  `ConsensusSpendBridge` and does not replace `TxValidation.Full`.
