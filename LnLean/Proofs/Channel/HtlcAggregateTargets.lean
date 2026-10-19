/-
# Aggregate multi-HTLC second-stage coverage and spending (PR-02, PR-05, CH-01)

The wave-10 coverage module `LnLean.Proofs.Channel.CoverageWitnessTargets`
characterizes the data that one BOLT 2 `commitment_signed` record omits and
proves that no decoder from the legacy wire alone recovers per-HTLC coverage.
This module lifts that result from one commitment record to an **aggregate**
of HTLC outputs taken from one or more commitments:

* `HtlcRecordRef` is an aggregate row: a commitment identity, a direction-tagged
  BOLT 2 id (`HTLCTag`), an amount, a `cltv_expiry`, a script identity, and the
  second-stage outpoint the row may spend.
* `Aggregate.coverage` is the list projection of the rows onto the
  commitment-output key.  `Aggregate.coverageValue` is its satoshi sum.
* `Aggregate.NoDuplication` and `Aggregate.DistinctCommitments` are explicit
  hypotheses.  Under them the aggregate projection is exactly the list (and
  sum) of the per-HTLC projections
  (`aggregate_coverage_projection`, `aggregate_coverageValue_eq_sum`).
  `duplicateAggregate_not_noDuplication` mechanizes why the no-duplication
  premise is load-bearing.
* `SecondStageSpend` is a second-stage spend with an explicit target
  (`SpendTarget = outpoint + script identity`).  Under
  `Aggregate.NoSpendAliasing` two spends of the same target identify the same
  row (`spend_target_separates_of_noAliasing`,
  `no_double_spend_of_noAliasing`).  The contrapositive
  `same_spend_distinct_records_imp_aliasing` makes the collision/aliasing
  hypothesis explicit.  Dropping it is not sound:
  `aliasing_double_spend_witness` and
  `no_spend_selector_on_aliased_aggregate` exhibit two distinct records with
  the same target.
* `AggregateTx` adds fee and weight accounting.  `AggregateTx.weight` is
  base weight plus the per-row input/output weight, `requiredFee` is the BOLT 3
  floor fee, and `Funded` is `outputValue + requiredFee ≤ inputValue`.  The
  concrete `boundaryTx` is *rejected*: its weight-derived fee plus output value
  exceeds its input value and its paid fee is below the required fee.

## Wave-10 boundary

The legacy `commitment_signed` wire still carries no aggregate coverage:
`aggregateOfFull` is a full-record projection (one row per signed entry), and
`no_legacy_only_aggregate_coverage_decoder` proves that no function from
`CommitmentSigned` alone returns `aggregateOfFull f |>.coverage` for every full
record.  This module does **not** claim that the legacy wire carries aggregate
coverage; aggregate coverage needs an out-of-band/full-record source exactly as
in wave 10.

## Scope

The model is structural: it does not construct BIP 143 digests, execute
scripts, or claim signature unforgeability.  Scripts are opaque identities
(`ScriptPubKey`), and amounts are floored millisatoshis.  Fee/weight numbers are
parameters, not a consensus weight estimator.  Anchors: BOLT 3 §"Commitment
Transaction", §"HTLC Outputs", and §4 "Fees"; BOLT 2 §"Committing Updates So
Far".  Model anchors: `LnLean/Channel/Types.lean`,
`LnLean/Channel/HTLC.lean`, `LnLean/Channel/Commitment.lean`,
`LnLean/Protocol/Messages.lean`, and
`LnLean/Proofs/Channel/CoverageWitnessTargets.lean`.
-/

import LnLean.Channel.HTLC
import LnLean.Proofs.Channel.CoverageWitnessTargets

namespace LnLean.Proofs.Channel.HtlcAggregate

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open LnLean
open LnLean.Channel
open LnLean.Protocol
open LnLean.Proofs
open LnLean.Proofs.Channel.CoverageWitnessTargets

/-! ## 1. Aggregate HTLC rows -/

/-- One HTLC output row of an aggregate.  The row is deliberately richer than
the legacy wire: it carries the commitment identity, the direction-tagged
BOLT 2 id (`HTLCTag`), the millisatoshi amount, `cltv_expiry`, the script
identity of the HTLC output, and the commitment outpoint the second-stage
transaction spends. -/
structure HtlcRecordRef where
  /-- Commitment number (or any model-side commitment identity). -/
  commitmentId : Nat
  /-- Direction-tagged BOLT 2 id.  The tag is the wave-4 `HTLCTag` view, not a
  new wire encoding. -/
  tag : HTLCTag
  /-- `amount_msat` of the HTLC. -/
  amountMsat : Msat
  /-- `cltv_expiry` of the HTLC. -/
  cltvExpiry : Height
  /-- Script identity of the commitment HTLC output.  Opaque bytes: this module
  does not interpret scripts. -/
  script : ScriptPubKey
  /-- Internal-order commitment txid (the spent outpoint's transaction id). -/
  commitmentTxid : ByteArray
  /-- Index of the HTLC output in the commitment transaction. -/
  outputIndex : Nat
  /-- Lifecycle tag; offered and received outputs use different scripts. -/
  state : HTLCState := .offered
deriving Repr, DecidableEq, BEq

namespace HtlcRecordRef

/-- The direction component of the row. -/
def direction (r : HtlcRecordRef) : Direction := r.tag.1

/-- The BOLT 2 per-sender id of the row. -/
def htlcId (r : HtlcRecordRef) : Nat := r.tag.2

/-- The floored satoshi value of the row.  This is the gross commitment output
value; the second-stage fee is accounted separately. -/
def amountSat (r : HtlcRecordRef) : Nat := r.amountMsat.toSatFloor

/-- The commitment-output key: commitment identity, direction-tagged id,
floor(amount), expiry, and script identity.  It does not include the lifecycle
tag because a removed record is not an output row. -/
structure OutputKey where
  commitmentId : Nat
  tag : HTLCTag
  amountSat : Nat
  cltvExpiry : Height
  script : ScriptPubKey
deriving Repr, DecidableEq, BEq

/-- The output key of a row. -/
def outputKey (r : HtlcRecordRef) : OutputKey :=
  { commitmentId := r.commitmentId
    tag := r.tag
    amountSat := r.amountSat
    cltvExpiry := r.cltvExpiry
    script := r.script }

/-- The record identity used for aggregate de-duplication. -/
def recordKey (r : HtlcRecordRef) : Nat × HTLCTag := (r.commitmentId, r.tag)

/-- The commitment outpoint a second-stage transaction spends. -/
structure Outpoint where
  commitmentId : Nat
  txid : ByteArray
  index : Nat
deriving Repr, DecidableEq, BEq

/-- The outpoint of the row. -/
def outpoint (r : HtlcRecordRef) : Outpoint :=
  { commitmentId := r.commitmentId, txid := r.commitmentTxid, index := r.outputIndex }

/-- An output identity that a spend targets: the previous outpoint plus the
spent output's script identity.  Both components are explicit because two rows
can alias on an outpoint while still naming the same script. -/
structure SpendTarget where
  outpoint : Outpoint
  script : ScriptPubKey
deriving Repr, DecidableEq, BEq

/-- The second-stage spend target of the row. -/
def spendTarget (r : HtlcRecordRef) : SpendTarget :=
  { outpoint := r.outpoint, script := r.script }

/-- The commitment-output projection.  This is the wave-3
`CommitmentHTLCOutput` the row would contribute to a commitment transaction. -/
def toCommitmentHtlcOutput (r : HtlcRecordRef) : CommitmentHTLCOutput :=
  { direction := r.direction
    amountSat := r.amountSat
    cltvExpiry := r.cltvExpiry
    state := r.state }

@[simp] theorem direction_eq_tag_fst (r : HtlcRecordRef) :
    r.direction = r.tag.1 := rfl

@[simp] theorem htlcId_eq_tag_snd (r : HtlcRecordRef) :
    r.htlcId = r.tag.2 := rfl

@[simp] theorem amountSat_eq (r : HtlcRecordRef) :
    r.amountSat = r.amountMsat.toSatFloor := rfl

@[simp] theorem outpoint_eq (r : HtlcRecordRef) :
    r.outpoint =
      { commitmentId := r.commitmentId, txid := r.commitmentTxid,
        index := r.outputIndex } := rfl

@[simp] theorem spendTarget_eq (r : HtlcRecordRef) :
    r.spendTarget = { outpoint := r.outpoint, script := r.script } := rfl

@[simp] theorem toCommitmentHtlcOutput_direction (r : HtlcRecordRef) :
    r.toCommitmentHtlcOutput.direction = r.direction := rfl

@[simp] theorem toCommitmentHtlcOutput_amountSat (r : HtlcRecordRef) :
    r.toCommitmentHtlcOutput.amountSat = r.amountSat := rfl

@[simp] theorem toCommitmentHtlcOutput_cltvExpiry (r : HtlcRecordRef) :
    r.toCommitmentHtlcOutput.cltvExpiry = r.cltvExpiry := rfl

@[simp] theorem toCommitmentHtlcOutput_state (r : HtlcRecordRef) :
    r.toCommitmentHtlcOutput.state = r.state := rfl

/-- Equality of aggregate rows is determined by the fields that enter the
coverage projection plus the outpoint and lifecycle data. -/
theorem ext_iff {r₁ r₂ : HtlcRecordRef} :
    r₁ = r₂ ↔
      r₁.commitmentId = r₂.commitmentId ∧
        r₁.tag = r₂.tag ∧
          r₁.amountMsat = r₂.amountMsat ∧
            r₁.cltvExpiry = r₂.cltvExpiry ∧
              r₁.script = r₂.script ∧
                r₁.commitmentTxid = r₂.commitmentTxid ∧
                  r₁.outputIndex = r₂.outputIndex ∧
                    r₁.state = r₂.state := by
  constructor
  · intro h
    subst h
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rintro ⟨hc, ht, ha, he, hs, htx, hi, hst⟩
    cases r₁
    cases r₂
    simp_all

end HtlcRecordRef

/-! ## 2. Aggregate coverage projection -/

/-- The per-HTLC coverage row of an aggregate.  It is the commitment-output
key plus the direction tag; the amount is the floored gross value. -/
structure CoverageRow where
  commitmentId : Nat
  tag : HTLCTag
  direction : Direction
  amountSat : Nat
  cltvExpiry : Height
  script : ScriptPubKey
deriving Repr, DecidableEq, BEq

namespace CoverageRow

/-- The de-duplication key of a coverage row.  Two rows with the same key are
the same HTLC output row for aggregate purposes. -/
def key (c : CoverageRow) : Nat × HTLCTag := (c.commitmentId, c.tag)

/-- The satoshi value contributed by a coverage row. -/
def valueSat (c : CoverageRow) : Nat := c.amountSat

@[simp] theorem key_eq (c : CoverageRow) :
    c.key = (c.commitmentId, c.tag) := rfl

@[simp] theorem valueSat_eq (c : CoverageRow) : c.valueSat = c.amountSat := rfl

end CoverageRow

/-- Project one aggregate row onto its coverage row. -/
def coverageOf (r : HtlcRecordRef) : CoverageRow :=
  { commitmentId := r.commitmentId
    tag := r.tag
    direction := r.direction
    amountSat := r.amountSat
    cltvExpiry := r.cltvExpiry
    script := r.script }

/-- An aggregate of HTLC output rows.  `records` is kept as a list because the
order is part of the model-side transaction construction; all sums below are
per-list-order sums and could be replaced by permutations. -/
structure Aggregate where
  records : List HtlcRecordRef
deriving Repr

namespace Aggregate

/-- The aggregate coverage projection: one coverage row per aggregate row, in
aggregate order. -/
def coverage (a : Aggregate) : List CoverageRow :=
  a.records.map coverageOf

/-- The per-HTLC coverage list.  This is the list whose sum/list identity the
aggregate theorem states; it is intentionally a separate definition so the
theorem is not merely a reducible abbreviation. -/
def perHtlcCoverage (a : Aggregate) : List CoverageRow :=
  a.records.map (fun r => coverageOf r)

/-- The satoshi sum of the aggregate coverage projection. -/
def coverageValue (a : Aggregate) : Nat :=
  (a.coverage.map CoverageRow.valueSat).sum

/-- The gross satoshi sum of the aggregate's rows. -/
def outputValue (a : Aggregate) : Nat :=
  (a.records.map HtlcRecordRef.amountSat).sum

/-- No two aggregate rows project to the same coverage row.  This is the
explicit no-duplication hypothesis of the aggregate theorem. -/
def NoDuplication (a : Aggregate) : Prop := a.coverage.Nodup

/-- The aggregate's commitment identities are pairwise distinct.  This is the
explicit distinct-commitment hypothesis.  It is stronger than needed for a
single commitment's HTLC list; it is used for cross-commitment aggregates. -/
def DistinctCommitments (a : Aggregate) : Prop :=
  (a.records.map (fun r => r.commitmentId)).Nodup

/-- The aggregate's second-stage spend targets are injective on its rows.  This
is the no-aliasing/collision-freedom premise for the separation theorem. -/
def NoSpendAliasing (a : Aggregate) : Prop :=
  ∀ r₁ ∈ a.records, ∀ r₂ ∈ a.records,
    r₁.spendTarget = r₂.spendTarget → r₁ = r₂

/-- The record identities `(commitmentId, tag)` are pairwise distinct. -/
def NoRecordDuplication (a : Aggregate) : Prop :=
  (a.records.map HtlcRecordRef.recordKey).Nodup

theorem coverage_eq_map (a : Aggregate) :
    a.coverage = a.records.map coverageOf := rfl

theorem perHtlcCoverage_eq_map (a : Aggregate) :
    a.perHtlcCoverage = a.records.map coverageOf := rfl

/-- The aggregate coverage projection and the per-HTLC projection are the same
list.  This is deliberately the definitional half of the aggregate theorem;
the hypotheses enter in the length/Nodup/sum corollaries below. -/
theorem aggregateCoverage_eq_perHtlcCoverage (a : Aggregate) :
    a.coverage = a.perHtlcCoverage := rfl

theorem coverage_length_eq (a : Aggregate) :
    a.coverage.length = a.records.length := by
  simp [coverage]

theorem perHtlcCoverage_length_eq (a : Aggregate) :
    a.perHtlcCoverage.length = a.records.length := by
  simp [perHtlcCoverage]

/-- **The per-HTLC sum is the aggregate sum.**  The aggregate coverage value is
the list sum of the individual output values. -/
theorem coverageValue_eq_sum (a : Aggregate) :
    a.coverageValue = (a.records.map (fun r => r.amountSat)).sum := by
  unfold coverageValue coverage
  induction a.records with
  | nil => rfl
  | cons r rs ih =>
      simp only [List.map_cons, List.sum_cons] at ih ⊢
      rw [ih]
      rfl

/-- The aggregate output value is the same list sum. -/
theorem coverageValue_eq_outputValue (a : Aggregate) :
    a.coverageValue = a.outputValue := by
  rw [coverageValue_eq_sum]
  rfl

/-- Coverage is append-homomorphic: an aggregate split into two parts has the
concatenation of the two coverage lists. -/
theorem coverage_append (a b : Aggregate) :
    (Aggregate.mk (a.records ++ b.records)).coverage =
      a.coverage ++ b.coverage := by
  simp [coverage]

/-- A no-duplication aggregate has a duplicate-free coverage projection. -/
theorem coverage_nodup_of_noDuplication (a : Aggregate)
    (h : a.NoDuplication) : a.coverage.Nodup := h

/-- Under no duplication the coverage projection has exactly one row per
aggregate row. -/
theorem coverage_length_eq_of_noDuplication (a : Aggregate)
    (_h : a.NoDuplication) : a.coverage.length = a.records.length :=
  coverage_length_eq a

/-- **Aggregate coverage projection.**  Under explicit no-duplication and
distinct-commitment hypotheses, the aggregate coverage is exactly the list of
per-HTLC coverage rows, is duplicate-free, has one row per aggregate row, and
its value is the sum of the per-HTLC values.

The distinct-commitment premise is the cross-commitment reading: it is used
below in `distinct_commitments_separate` and in the separation section.  The
list identity itself does not need it; keeping it in the bundle makes the
aggregate scope explicit. -/
theorem aggregate_coverage_projection (a : Aggregate)
    (hdup : a.NoDuplication) (_hcommit : a.DistinctCommitments) :
    a.coverage = a.records.map coverageOf ∧
      a.coverage.Nodup ∧
        a.coverage.length = a.records.length ∧
          a.coverageValue = (a.records.map (fun r => r.amountSat)).sum ∧
            (∀ r₁ ∈ a.records, ∀ r₂ ∈ a.records,
              r₁.commitmentId ≠ r₂.commitmentId →
                coverageOf r₁ ≠ coverageOf r₂) := by
  refine ⟨coverage_eq_map a, hdup, coverage_length_eq a,
    coverageValue_eq_sum a, ?_⟩
  intro r₁ _ r₂ _ hid heq
  have hc : r₁.commitmentId = r₂.commitmentId := by
    simpa [coverageOf] using congrArg CoverageRow.commitmentId heq
  exact hid hc

/-- Distinct aggregate commitments have distinct coverage-row commitment
identities.  This is the projection form of the distinct-commitment premise. -/
theorem distinct_commitments_separate (a : Aggregate)
    (h : a.DistinctCommitments) {r₁ r₂ : HtlcRecordRef}
    (h₁ : r₁ ∈ a.records) (h₂ : r₂ ∈ a.records)
    (hid : r₁.commitmentId = r₂.commitmentId) : r₁ = r₂ := by
  -- `map` of a `Nodup` list is `Nodup`; equal ids therefore occupy the same
  -- index, and the same index gives the same record.
  unfold Aggregate.DistinctCommitments at h
  rw [List.nodup_iff_eq_of_getElem_eq] at h
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h₁
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem h₂
  have hidx : i = j :=
    h i j (by simpa using hi) (by simpa using hj) (by simpa using hid)
  subst hidx
  rfl

end Aggregate

/-! ## 3. Second-stage spends and no-double-spend separation -/

/-- A second-stage spend.  `target` is the commitment outpoint plus script
identity the spend consumes; `valueSat` is the produced second-stage output
value, and `weight` is the transaction weight. -/
structure SecondStageSpend where
  target : HtlcRecordRef.SpendTarget
  valueSat : Nat
  weight : Weight
deriving Repr

namespace SecondStageSpend

/-- A spend covers a row exactly when it targets that row's outpoint/script. -/
def Spends (s : SecondStageSpend) (r : HtlcRecordRef) : Prop :=
  s.target = r.spendTarget

theorem spends_target_eq {s : SecondStageSpend} {r : HtlcRecordRef}
    (h : s.Spends r) : s.target = r.spendTarget := h

theorem spends_of_target_eq {s : SecondStageSpend} {r : HtlcRecordRef}
    (h : s.target = r.spendTarget) : s.Spends r := h

/-- A spend of one row also covers any row with the same target. -/
theorem spends_of_spends_of_target_eq {s : SecondStageSpend}
    {r₁ r₂ : HtlcRecordRef} (h₁ : s.Spends r₁)
    (ht : r₁.spendTarget = r₂.spendTarget) : s.Spends r₂ :=
  h₁.trans ht

end SecondStageSpend

/-- The explicit aliasing/collision relation: two distinct records share one
second-stage target. -/
def Aliased (r₁ r₂ : HtlcRecordRef) : Prop :=
  r₁ ≠ r₂ ∧ r₁.spendTarget = r₂.spendTarget

theorem aliased_iff (r₁ r₂ : HtlcRecordRef) :
    Aliased r₁ r₂ ↔ r₁ ≠ r₂ ∧ r₁.spendTarget = r₂.spendTarget := Iff.rfl

/-- **Separation under no aliasing.**  If an aggregate has no two distinct rows
with the same spend target, then one spend cannot cover two rows.  This is the
no-double-spend theorem for aggregate second-stage coverage. -/
theorem spend_target_separates_of_noAliasing
    (a : Aggregate) (hsep : a.NoSpendAliasing)
    {s : SecondStageSpend} {r₁ r₂ : HtlcRecordRef}
    (hm₁ : r₁ ∈ a.records) (hm₂ : r₂ ∈ a.records)
    (h₁ : s.Spends r₁) (h₂ : s.Spends r₂) : r₁ = r₂ :=
  hsep r₁ hm₁ r₂ hm₂ (h₁.symm.trans h₂)

/-- The same theorem stated as uniqueness of the record selected by a
successful spend. -/
theorem no_double_spend_of_noAliasing
    (a : Aggregate) (hsep : a.NoSpendAliasing)
    {s : SecondStageSpend} {r₁ r₂ : HtlcRecordRef}
    (hm₁ : r₁ ∈ a.records) (hm₂ : r₂ ∈ a.records)
    (h₁ : s.Spends r₁) (h₂ : s.Spends r₂) : r₁ = r₂ :=
  spend_target_separates_of_noAliasing a hsep hm₁ hm₂ h₁ h₂

/-- **Contrapositive/aliasing form.**  If two distinct aggregate rows are both
spent by the same second-stage spend, then the aliasing hypothesis holds.  No
aggregate with distinct records on one target can be separated. -/
theorem same_spend_distinct_records_imp_aliasing
    {s : SecondStageSpend} {r₁ r₂ : HtlcRecordRef}
    (hne : r₁ ≠ r₂) (h₁ : s.Spends r₁) (h₂ : s.Spends r₂) :
    Aliased r₁ r₂ :=
  ⟨hne, h₁.symm.trans h₂⟩

/-- An aggregate fails separation exactly when it has an aliased pair. -/
theorem not_noSpendAliasing_iff_exists_aliased (a : Aggregate) :
    ¬ a.NoSpendAliasing ↔
      ∃ r₁ ∈ a.records, ∃ r₂ ∈ a.records, Aliased r₁ r₂ := by
  constructor
  · intro h
    unfold Aggregate.NoSpendAliasing at h
    by_cases hno : ∃ r₁ ∈ a.records, ∃ r₂ ∈ a.records, Aliased r₁ r₂
    · exact hno
    · exfalso
      apply h
      intro r₁ hm₁ r₂ hm₂ ht
      by_cases heq : r₁ = r₂
      · exact heq
      · exact False.elim (hno ⟨r₁, hm₁, r₂, hm₂, heq, ht⟩)
  · rintro ⟨r₁, hm₁, r₂, hm₂, hne, ht⟩ hsep
    exact hne (hsep r₁ hm₁ r₂ hm₂ ht)

/-! ## 4. The aliasing counterexample -/

/-- Script identity used by the aliasing witness. -/
def aliasScript : ScriptPubKey := ⟨[0x51]⟩

/-- Commitment txid used by the aliasing witness. -/
def aliasTxid : ByteArray := ByteArray.empty

/-- First aliased row: 1000 msat (1 sat gross). -/
def aliasRecordA : HtlcRecordRef :=
  { commitmentId := 0
    tag := (.local, 0)
    amountMsat := ⟨1000⟩
    cltvExpiry := 100
    script := aliasScript
    commitmentTxid := aliasTxid
    outputIndex := 0
    state := .offered }

/-- Second aliased row: 2000 msat (2 sat gross).  It is a distinct record but
shares the commitment outpoint and script of `aliasRecordA`. -/
def aliasRecordB : HtlcRecordRef :=
  { aliasRecordA with amountMsat := ⟨2000⟩, state := .received }

/-- The aggregate containing the aliased pair. -/
def aliasAggregate : Aggregate :=
  { records := [aliasRecordA, aliasRecordB] }

/-- The two aliased rows are distinct. -/
theorem alias_records_distinct : aliasRecordA ≠ aliasRecordB := by
  decide

/-- They nevertheless share one second-stage target. -/
theorem alias_records_same_target :
    aliasRecordA.spendTarget = aliasRecordB.spendTarget := by
  decide

/-- A spend of the shared target. -/
def aliasSpend : SecondStageSpend :=
  { target := aliasRecordA.spendTarget, valueSat := 1, weight := ⟨100⟩ }

/-- The one spend covers both rows. -/
theorem alias_spend_covers_both :
    aliasSpend.Spends aliasRecordA ∧ aliasSpend.Spends aliasRecordB := by
  constructor <;> rfl

/-- The aliasing aggregate violates the no-aliasing premise. -/
theorem aliasAggregate_not_noSpendAliasing :
    ¬ aliasAggregate.NoSpendAliasing := by
  unfold Aggregate.NoSpendAliasing
  intro hsep
  exact alias_records_distinct
    (hsep aliasRecordA (by simp [aliasAggregate])
      aliasRecordB (by simp [aliasAggregate]) alias_records_same_target)

/-- **Dropping the aliasing hypothesis is unsound.**  There are two distinct
aggregate records and one second-stage spend that covers both. -/
theorem aliasing_double_spend_witness :
    ∃ (a : Aggregate) (r₁ r₂ : HtlcRecordRef) (s : SecondStageSpend),
      r₁ ∈ a.records ∧ r₂ ∈ a.records ∧ r₁ ≠ r₂ ∧
        s.Spends r₁ ∧ s.Spends r₂ := by
  refine ⟨aliasAggregate, aliasRecordA, aliasRecordB, aliasSpend,
    by simp [aliasAggregate], by simp [aliasAggregate],
    alias_records_distinct, alias_spend_covers_both.1,
    alias_spend_covers_both.2⟩

/-- A spend selector is a function from a target back to a record.  On the
aliased aggregate no such selector can be correct for every row, because the
two rows share their target. -/
theorem no_spend_selector_on_aliased_aggregate :
    ¬ ∃ choose : HtlcRecordRef.SpendTarget → HtlcRecordRef,
        ∀ r ∈ aliasAggregate.records, choose r.spendTarget = r := by
  rintro ⟨choose, hchoose⟩
  have hA := hchoose aliasRecordA (by simp [aliasAggregate])
  have hB := hchoose aliasRecordB (by simp [aliasAggregate])
  exact alias_records_distinct (by
    rw [← hA, ← hB, alias_records_same_target])

/-- No-double-spend cannot be obtained from record identity alone: the two
aliased records are distinct, so record distinctness is not a substitute for
target injectivity. -/
theorem record_distinctness_not_spend_separation :
    aliasRecordA ≠ aliasRecordB ∧
      ¬ (∀ r₁ r₂ : HtlcRecordRef,
        r₁ ≠ r₂ → r₁.spendTarget ≠ r₂.spendTarget) := by
  refine ⟨alias_records_distinct, ?_⟩
  intro h
  exact h aliasRecordA aliasRecordB alias_records_distinct
    alias_records_same_target

/-! ## 5. Fee and weight accounting for the aggregate transaction -/

/-- An aggregate second-stage transaction.  `baseWeight` is the transaction
overhead; per row the model charges one input and one output.  `inputValueSat`
is the sum of spent commitment outputs, `outputValueSat` is the value of the
produced outputs, and `paidFeeSat` is the fee the transaction actually pays. -/
structure AggregateTx where
  /-- The aggregate whose rows this transaction spends. -/
  aggregate : Aggregate
  /-- Constant transaction overhead, in weight units. -/
  baseWeight : Nat
  /-- Weight contributed by one spent HTLC input. -/
  inputWeight : Nat
  /-- Weight contributed by one second-stage output. -/
  outputWeight : Nat
  /-- Total value of the spent commitment outputs. -/
  inputValueSat : Nat
  /-- Total value of the produced second-stage outputs. -/
  outputValueSat : Nat
  /-- The fee actually paid by the transaction. -/
  paidFeeSat : Nat
deriving Repr

namespace AggregateTx

/-- The aggregate transaction weight: base plus one input+output pair per
aggregate row. -/
def weight (tx : AggregateTx) : Weight :=
  ⟨tx.baseWeight +
    (tx.aggregate.records.map (fun _ => tx.inputWeight + tx.outputWeight)).sum⟩

/-- The BOLT 3 floor fee for the aggregate weight. -/
def requiredFee (tx : AggregateTx) (r : FeeRate) : Msat :=
  feeForWeight r tx.weight

/-- The fee actually paid is sufficient for the feerate and weight. -/
def FeeSufficient (tx : AggregateTx) (r : FeeRate) : Prop :=
  (tx.requiredFee r).val ≤ tx.paidFeeSat

/-- The aggregate is funded when its produced output value plus the required
fee is at most the spent input value.  This is the accounting boundary; it does
not claim consensus validity. -/
def Funded (tx : AggregateTx) (r : FeeRate) : Prop :=
  tx.outputValueSat + (tx.requiredFee r).val ≤ tx.inputValueSat

/-- Weight formula in terms of the number of aggregate rows. -/
theorem weight_eq (tx : AggregateTx) :
    tx.weight.val =
      tx.baseWeight +
        (tx.aggregate.records.length * (tx.inputWeight + tx.outputWeight)) := by
  unfold weight
  simp [List.map_const', List.sum_replicate_nat]

/-- An empty aggregate pays only the base weight. -/
theorem weight_empty (tx : AggregateTx) (h : tx.aggregate.records = []) :
    tx.weight.val = tx.baseWeight := by
  rw [weight_eq, h]
  simp

/-- Adding one row increases the weight by exactly one input+output pair. -/
theorem weight_append_singleton (tx : AggregateTx) (r : HtlcRecordRef) :
    (({ tx with aggregate :=
        { records := tx.aggregate.records ++ [r] } } : AggregateTx).weight).val =
      tx.weight.val + tx.inputWeight + tx.outputWeight := by
  rw [weight_eq, weight_eq]
  simp only [List.length_append, List.length_singleton]
  rw [Nat.add_mul, Nat.one_mul]
  simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- The required fee is the BOLT 3 floor fee on the aggregate weight. -/
theorem requiredFee_val (tx : AggregateTx) (r : FeeRate) :
    (tx.requiredFee r).val = r.msatPerKw * tx.weight.val / 1000 := rfl

/-- The required fee is nonnegative. -/
theorem requiredFee_nonneg (tx : AggregateTx) (r : FeeRate) :
    0 ≤ (tx.requiredFee r).val := Nat.zero_le _

/-- A higher weight cannot lower the required fee. -/
theorem requiredFee_mono_weight (tx : AggregateTx) (r : FeeRate)
    {w : Weight} (h : tx.weight.val ≤ w.val) :
    (tx.requiredFee r).val ≤ (feeForWeight r w).val :=
  feeForWeight_mono_weight r h

/-- Fee sufficiency is monotone in the paid fee. -/
theorem feeSufficient_mono_paid (tx : AggregateTx) (r : FeeRate)
    {paid : Nat} (h : tx.FeeSufficient r) (hle : tx.paidFeeSat ≤ paid) :
    (tx.requiredFee r).val ≤ paid :=
  Nat.le_trans h hle

/-- A paid fee below the required fee is insufficient. -/
theorem not_feeSufficient_of_lt (tx : AggregateTx) (r : FeeRate)
    (h : tx.paidFeeSat < (tx.requiredFee r).val) :
    ¬ tx.FeeSufficient r := by
  intro hs
  unfold AggregateTx.FeeSufficient at hs
  omega

/-- Funded means exactly the accounting inequality. -/
theorem funded_iff (tx : AggregateTx) (r : FeeRate) :
    tx.Funded r ↔
      tx.outputValueSat + (tx.requiredFee r).val ≤ tx.inputValueSat :=
  Iff.rfl

/-- A funded aggregate's output value is at most its input value. -/
theorem outputValue_le_input_of_funded (tx : AggregateTx) (r : FeeRate)
    (h : tx.Funded r) : tx.outputValueSat ≤ tx.inputValueSat := by
  unfold AggregateTx.Funded at h
  omega

/-- **Fee/weight boundary.**  If the output value plus the weight-derived fee
exceeds the input value, the aggregate is rejected. -/
theorem not_funded_of_output_add_fee_gt (tx : AggregateTx) (r : FeeRate)
    (h : tx.inputValueSat < tx.outputValueSat + (tx.requiredFee r).val) :
    ¬ tx.Funded r := by
  intro hf
  unfold AggregateTx.Funded at hf
  omega

/-- A fee below the required fee also rejects the aggregate under the explicit
fee-sufficiency condition.  This is the separate fee boundary; it does not
replace `Funded`, which is about input/output accountancy. -/
theorem insufficient_fee_not_feeSufficient (tx : AggregateTx) (r : FeeRate)
    (h : tx.paidFeeSat < (tx.requiredFee r).val) :
    ¬ tx.FeeSufficient r :=
  not_feeSufficient_of_lt tx r h

end AggregateTx

/-! ## 6. Concrete non-vacuity witness and rejected aggregate -/

/-- Script identity A for the witness aggregate. -/
def witnessScriptA : ScriptPubKey := ⟨[0x51]⟩

/-- Script identity B for the witness aggregate. -/
def witnessScriptB : ScriptPubKey := ⟨[0x52]⟩

/-- First witness row: local HTLC id 0, 1000 msat. -/
def witnessRecordA : HtlcRecordRef :=
  { commitmentId := 0
    tag := (.local, 0)
    amountMsat := ⟨1000⟩
    cltvExpiry := 100
    script := witnessScriptA
    commitmentTxid := aliasTxid
    outputIndex := 0
    state := .offered }

/-- Second witness row: remote HTLC id 0, 2000 msat. -/
def witnessRecordB : HtlcRecordRef :=
  { commitmentId := 0
    tag := (.remote, 0)
    amountMsat := ⟨2000⟩
    cltvExpiry := 200
    script := witnessScriptB
    commitmentTxid := aliasTxid
    outputIndex := 1
    state := .received }

/-- The two-row non-vacuity aggregate.  Both rows belong to commitment 0 but
carry different directions, ids, amounts, expiries, and scripts. -/
def witnessAggregate : Aggregate :=
  { records := [witnessRecordA, witnessRecordB] }

/-- The witness aggregate has no duplicate coverage row. -/
theorem witnessAggregate_noDuplication : witnessAggregate.NoDuplication := by
  simp [Aggregate.NoDuplication, Aggregate.coverage, witnessAggregate,
    coverageOf, witnessRecordA, witnessRecordB]

/-- The witness aggregate's coverage has two rows. -/
theorem witnessAggregate_coverage_length :
    witnessAggregate.coverage.length = 2 := by
  decide

/-- The witness aggregate's coverage value is the sum of the two floored
amounts: 1 + 2 = 3 sat. -/
theorem witnessAggregate_coverageValue :
    witnessAggregate.coverageValue = 3 := by
  decide

/-- The witness aggregate is genuinely non-vacuous: it has two distinct records
and a duplicate-free two-row coverage projection. -/
theorem witnessAggregate_nonvacuous :
    witnessAggregate.records.length = 2 ∧
      witnessAggregate.coverage.length = 2 ∧
        witnessAggregate.NoDuplication ∧
          witnessRecordA ≠ witnessRecordB := by
  refine ⟨rfl, witnessAggregate_coverage_length,
    witnessAggregate_noDuplication, ?_⟩
  decide

/-- A cross-commitment witness: the same HTLC row under two commitment
identities.  This is the non-vacuous instance for `DistinctCommitments`. -/
def distinctCommitmentAggregate : Aggregate :=
  { records :=
      [{ witnessRecordA with commitmentId := 7 },
       { witnessRecordA with commitmentId := 8 }] }

/-- The cross-commitment witness satisfies the distinct-commitment premise. -/
theorem distinctCommitmentAggregate_distinct :
    distinctCommitmentAggregate.DistinctCommitments := by
  simp [Aggregate.DistinctCommitments, distinctCommitmentAggregate,
    witnessRecordA]

/-- The cross-commitment witness has duplicate-free two-row coverage. -/
theorem distinctCommitmentAggregate_noDuplication :
    distinctCommitmentAggregate.NoDuplication := by
  simp [Aggregate.NoDuplication, Aggregate.coverage, distinctCommitmentAggregate,
    coverageOf, witnessRecordA]

/-- The two rows of the cross-commitment witness are distinct. -/
theorem distinctCommitmentAggregate_rows_distinct :
    ({ witnessRecordA with commitmentId := 7 } : HtlcRecordRef) ≠
      { witnessRecordA with commitmentId := 8 } := by
  decide

/-- **The distinct-commitment hypothesis has content.**  `distinct_commitments_separate`
identifies any two rows with the same commitment id; the cross-commitment
witness shows that rows under different commitment ids remain distinct. -/
theorem distinctCommitments_separate_witness :
    distinctCommitmentAggregate.DistinctCommitments ∧
      ({ witnessRecordA with commitmentId := 7 } : HtlcRecordRef) ≠
        { witnessRecordA with commitmentId := 8 } :=
  ⟨distinctCommitmentAggregate_distinct,
    distinctCommitmentAggregate_rows_distinct⟩

/-- A duplicate aggregate: the same row twice.  Its coverage projection is not
duplicate-free, so it does not satisfy `NoDuplication`. -/
def duplicateAggregate : Aggregate :=
  { records := [witnessRecordA, witnessRecordA] }

/-- **The no-duplication premise is necessary.**  Duplicating an aggregate row
duplicates the coverage projection. -/
theorem duplicateAggregate_not_noDuplication :
    ¬ duplicateAggregate.NoDuplication := by
  simp [Aggregate.NoDuplication, Aggregate.coverage, duplicateAggregate,
    coverageOf, witnessRecordA]

/-- The duplicate aggregate still has two rows; the failure is specifically a
duplicate *coverage* row, not a length collapse. -/
theorem duplicateAggregate_lengths :
    duplicateAggregate.records.length = 2 ∧
      duplicateAggregate.coverage.length = 2 := by
  decide

/-- A concrete feerate for the boundary witness: 1000 msat per 1000 weight
units. -/
def boundaryRate : FeeRate := ⟨1000⟩

/-- The aggregate transaction used for the fee/weight boundary.  It spends the
two witness rows (input value 3 sat), produces 3 sat, pays only 1 sat, and has
weight `500 + 2 * (100 + 100) = 900`. -/
def boundaryTx : AggregateTx :=
  { aggregate := witnessAggregate
    baseWeight := 500
    inputWeight := 100
    outputWeight := 100
    inputValueSat := 3
    outputValueSat := 3
    paidFeeSat := 1 }

/-- The boundary transaction's weight is 900 weight units. -/
theorem boundaryTx_weight : boundaryTx.weight.val = 900 := by
  decide

/-- The required fee at the boundary feerate is 900 msat. -/
theorem boundaryTx_requiredFee : (boundaryTx.requiredFee boundaryRate).val = 900 := by
  decide

/-- **The aggregate fee/weight boundary is real.**  The boundary transaction
spends 3 sat, pays out 3 sat, and owes 900 msat; funding fails. -/
theorem boundaryTx_not_funded : ¬ boundaryTx.Funded boundaryRate := by
  intro h
  unfold AggregateTx.Funded at h
  rw [boundaryTx_requiredFee] at h
  simp [boundaryTx] at h

/-- The boundary transaction also fails the separate paid-fee sufficiency
condition. -/
theorem boundaryTx_fee_insufficient :
    ¬ boundaryTx.FeeSufficient boundaryRate :=
  boundaryTx.not_feeSufficient_of_lt boundaryRate (by
    rw [boundaryTx_requiredFee]
    decide)

/-- **Rejected aggregate.**  A concrete aggregate is rejected because its
weight-derived fee plus output value exceeds its input value, and separately
because its paid fee is below the required fee. -/
theorem rejectedAggregate :
    ¬ boundaryTx.Funded boundaryRate ∧
      ¬ boundaryTx.FeeSufficient boundaryRate :=
  ⟨boundaryTx_not_funded, boundaryTx_fee_insufficient⟩

/-- A funded variant of the boundary aggregate: raise the input value to 1000
sat and pay the full fee.  This shows the boundary is not a vacuous rejection of
every aggregate. -/
def fundedTx : AggregateTx :=
  { boundaryTx with inputValueSat := 1000, paidFeeSat := 900 }

/-- The funded variant satisfies both the funding and fee conditions. -/
theorem fundedTx_ok :
    fundedTx.Funded boundaryRate ∧ fundedTx.FeeSufficient boundaryRate := by
  constructor
  · unfold AggregateTx.Funded
    rw [show (fundedTx.requiredFee boundaryRate).val = 900 by decide]
    decide
  · unfold AggregateTx.FeeSufficient
    rw [show (fundedTx.requiredFee boundaryRate).val = 900 by decide]
    decide

/-- The funded and rejected variants use the same aggregate rows; only the
accounting differs.  This isolates the failure to the fee/weight boundary. -/
theorem funded_and_rejected_same_rows :
    fundedTx.aggregate = boundaryTx.aggregate ∧
      fundedTx.Funded boundaryRate ∧
        ¬ boundaryTx.Funded boundaryRate :=
  ⟨rfl, fundedTx_ok.1, boundaryTx_not_funded⟩

/-! ## 7. The wave-10 legacy-wire boundary -/

/-- Aggregate rows extracted from one full `commitment_signed` record.  The
script identity is an explicit projection because the legacy full record does
not carry script bytes; `scriptOfEntry` makes that dependency visible rather
than inventing wire data. -/
def aggregateOfFullWith (scriptOfEntry : SignedHtlcEntry → ScriptPubKey)
    (f : CommitmentSignedFull) : Aggregate :=
  { records :=
      f.htlcEntries.map (fun e =>
        { commitmentId := f.commitmentNumber
          tag := (e.direction, e.htlcId)
          amountMsat := e.amount
          cltvExpiry := e.cltvExpiry
          script := scriptOfEntry e
          commitmentTxid := f.commitmentDigest
          outputIndex := e.htlcId
          state := e.htlcState }) }

/-- The canonical extraction used below: every entry gets the same opaque
script identity, because the legacy record carries no script bytes. -/
def aggregateOfFull (f : CommitmentSignedFull) : Aggregate :=
  aggregateOfFullWith (fun _ => ⟨[]⟩) f

/-- Extraction produces exactly one coverage row per signed entry. -/
theorem aggregateOfFullWith_coverage_length
    (scriptOfEntry : SignedHtlcEntry → ScriptPubKey)
    (f : CommitmentSignedFull) :
    (aggregateOfFullWith scriptOfEntry f).coverage.length =
      f.htlcEntries.length := by
  simp [aggregateOfFullWith, Aggregate.coverage]

/-- The canonical extraction for the wave-10 counterexample records.  The two
full records differ only in the amount row. -/
theorem aggregateOfFull_witnessA_coverage_ne_witnessB :
    (aggregateOfFull witnessFullA).coverage ≠
      (aggregateOfFull witnessFullB).coverage := by
  intro h
  have hval := congrArg (fun l : List CoverageRow =>
    l.map CoverageRow.amountSat) h
  simp [aggregateOfFull, aggregateOfFullWith, Aggregate.coverage,
    witnessFullA, witnessFullB, witnessEntryA, witnessEntryB,
    coverageOf, HtlcRecordRef.amountSat] at hval
  simp [Msat.toSatFloor, Msat.MSAT_PER_SAT] at hval

/-- The two wave-10 full records still have the same legacy projection, while
their extracted aggregate coverage differs. -/
theorem aggregate_wire_boundary_witness :
    witnessFullA.toCommitmentSigned = witnessFullB.toCommitmentSigned ∧
      (aggregateOfFull witnessFullA).coverage ≠
        (aggregateOfFull witnessFullB).coverage :=
  ⟨witness_full_same_projection, aggregateOfFull_witnessA_coverage_ne_witnessB⟩

/-- **No legacy-only aggregate coverage decoder.**  There is no function from
the legacy `commitment_signed` record alone that returns the extracted
aggregate coverage for every full record.  This is the aggregate restatement of
the wave-10 `no_legacy_only_coverage_decoder`. -/
theorem no_legacy_only_aggregate_coverage_decoder :
    ¬ ∃ decode : CommitmentSigned → List CoverageRow,
        ∀ f : CommitmentSignedFull,
          decode f.toCommitmentSigned = (aggregateOfFull f).coverage := by
  rintro ⟨decode, hdecode⟩
  have hsame : decode witnessFullA.toCommitmentSigned =
      decode witnessFullB.toCommitmentSigned := by
    rw [witness_full_same_projection]
  have hA := hdecode witnessFullA
  have hB := hdecode witnessFullB
  exact aggregateOfFull_witnessA_coverage_ne_witnessB
    (hA.symm.trans (hsame.trans hB))

/-- The legacy wire boundary in one statement: the wire projection does not
determine aggregate coverage.  The legacy record is not claimed to carry
aggregate coverage. -/
theorem legacy_wire_does_not_carry_aggregate_coverage :
    witnessFullA.toCommitmentSigned = witnessFullB.toCommitmentSigned ∧
      (aggregateOfFull witnessFullA).coverage ≠
        (aggregateOfFull witnessFullB).coverage ∧
          (¬ ∃ decode : CommitmentSigned → List CoverageRow,
            ∀ f : CommitmentSignedFull,
              decode f.toCommitmentSigned = (aggregateOfFull f).coverage) :=
  ⟨aggregate_wire_boundary_witness.1,
    aggregate_wire_boundary_witness.2,
    no_legacy_only_aggregate_coverage_decoder⟩

/-! ## 8. Summary -/

/-- Bundled faithful reading of this lane:

1. Aggregate coverage is the list of per-HTLC coverage rows and its value is
   the sum of the per-HTLC floored amounts
   (`aggregate_coverage_projection`, `coverageValue_eq_sum`).
2. Under explicit no-aliasing, one second-stage target identifies one record
   (`no_double_spend_of_noAliasing`); without it, the aliasing witness has two
   distinct records on one target (`aliasing_double_spend_witness`).
3. The fee/weight boundary rejects a concrete aggregate
   (`rejectedAggregate`) while a funded variant with the same rows succeeds
   (`fundedTx_ok`).
4. The legacy wire still does not determine aggregate coverage
   (`legacy_wire_does_not_carry_aggregate_coverage`).

The hypotheses are explicit: `Aggregate.NoDuplication`,
`Aggregate.DistinctCommitments`, and `Aggregate.NoSpendAliasing` are not
discharged by the bare record list.  This module is a structural model; it does
not claim script execution, signature unforgeability, or consensus validity. -/
theorem htlc_aggregate_summary :
    (∀ a : Aggregate,
      a.coverage = a.records.map coverageOf ∧
        a.coverageValue = (a.records.map (fun r => r.amountSat)).sum) ∧
      (∀ (a : Aggregate), a.NoSpendAliasing →
        ∀ {s : SecondStageSpend} {r₁ r₂ : HtlcRecordRef},
          r₁ ∈ a.records → r₂ ∈ a.records →
            s.Spends r₁ → s.Spends r₂ → r₁ = r₂) ∧
      (∃ (a : Aggregate) (r₁ r₂ : HtlcRecordRef) (s : SecondStageSpend),
        r₁ ∈ a.records ∧ r₂ ∈ a.records ∧ r₁ ≠ r₂ ∧
          s.Spends r₁ ∧ s.Spends r₂) ∧
      (¬ boundaryTx.Funded boundaryRate ∧
        ¬ boundaryTx.FeeSufficient boundaryRate) ∧
      (¬ ∃ decode : CommitmentSigned → List CoverageRow,
        ∀ f : CommitmentSignedFull,
          decode f.toCommitmentSigned = (aggregateOfFull f).coverage) := by
  refine ⟨?_, ?_, aliasing_double_spend_witness, rejectedAggregate,
    no_legacy_only_aggregate_coverage_decoder⟩
  · intro a
    exact ⟨Aggregate.coverage_eq_map a, Aggregate.coverageValue_eq_sum a⟩
  · intro a hsep s r₁ r₂ hm₁ hm₂ h₁ h₂
    exact no_double_spend_of_noAliasing a hsep hm₁ hm₂ h₁ h₂

end LnLean.Proofs.Channel.HtlcAggregate
