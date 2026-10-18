import LnLean.Channel.Commitment
import LnLean.Proofs.Channel.CommitmentGrossNetTargets

/-!
# Gross/net record fields and the canonical refinement at the field boundary
(CH-03, CH-04)

Wave 5 proved the BOLT 3 gross/net accounting through additive `CommitmentTx`
fields, but the concrete `CommitmentHTLCOutput` and `Commitment` records in
`LnLean/Channel/Types.lean` still had a single satoshi value each.  This module
records the wave-6 core patch and proves the refinement and fee accounting at
the *new record boundary*:

* `CommitmentHTLCOutput.amountSat` is **gross**; the new
  `CommitmentHTLCOutput.netAmountSat` (default `amountSat`) is the
  second-stage value used by the dust test;
* `Commitment.trimmedTotalSat` (default `0`) records the gross value removed
  by trimming and added to the commitment fee;
* `CommitmentTx.netAmountSat` now defaults to the record field
  `CommitmentHTLCOutput.netAmountSat`, so the canonical net path
  `CommitmentTx.htlcOutputNet` / `CommitmentTx.outputsNet` reads the record
  directly;
* `Commitment.migrateNet` and `CommitmentTx.migrateNet` construct the migrated
  record: below-dust non-HTLC outputs are zeroed, surviving HTLCs are filtered
  by the net field, and the removed gross value is stored in
  `Commitment.trimmedTotalSat` (and `CommitmentTx.trimmedSat`).

## Naming note

The stored field is `Commitment.trimmedTotalSat`, not `Commitment.trimmedSat`.
`LnLean.Channel.Commitment.trimmedSat` is already the computed nominal trim
value (a function of a dust limit and a net projection), and the wave-5 proof
module `CommitmentGrossNetTargets` consumes it as a function.  Renaming the
computed function to `Commitment.trimmedValueFor` (added here as an alias) and
the stored field to `trimmedSat` is the remaining integration rename; it is
recorded in the lane report.

## Results

* `CommitmentHTLCOutput.netAmountSat_default`: a literal that omits the new
  field has `netAmountSat = amountSat`, so every pre-wave-6 construction site
  (including `legacyHtlcOutput`, `netHtlcOutput`, and D12's `mkHtlcOutput`)
  keeps its exact semantics.
* `CommitmentTx.htlcOutputNet_eq_none_iff_recordNet`: on a transaction whose
  net projection is the record field, the canonical dust test is exactly
  `netAmountSat < dustLimitSat`.
* `Commitment.migrateNet_totalOutputValue_add_trimmedTotalSat` and
  `Commitment.migrateNet_conservation`: emitted value + base fee + stored
  trimmed value = funding value.
* `Commitment.migrateNet_effectiveFee_eq`: the effective commitment fee is
  exactly `feeSat + trimmedTotalSat`.
* `CommitmentTx.migrateNet_outputsNet_perm_commitmentOutputs`: the migrated
  sorted net output list is a permutation of the legacy consumer path
  `Commitment.commitmentOutputs`, at an arbitrary dust limit (with the BOLT 2
  `0 < dustLimitSat` domain hypothesis used by wave 5).
* D12's refutations and the wave-5 `migratedFrom` refinement remain imported
  and are restated here unchanged.

## Scope caveats

* Script execution, signatures, witnesses, and sighash are out of scope.
* `CommitmentHTLCOutput.netAmountSat` is caller-supplied.  It is related to the
  gross value by the explicit `NetConsistentOnRecords` hypothesis
  (`net + second_stage_fee = gross`), not by a definition.
* The refinement is a permutation, not list equality: the rich model sorts and
  the legacy function does not (D12).
* The zero-dust wave-4 path and the positive-dust migration path are both
  retained; nothing in D12 or wave 4 is weakened.
-/

namespace LnLean.Proofs.Channel.CommitmentTypes

set_option autoImplicit false

open LnLean
open LnLean.Channel
open LnLean.Proofs.Channel

/-! ## 1. The record-field boundary and its defaults -/

/-- A `CommitmentHTLCOutput` literal that omits `netAmountSat` has the identity
projection `netAmountSat = amountSat`.  This is the compatibility fact that
keeps every pre-wave-6 construction site unchanged. -/
theorem CommitmentHTLCOutput.netAmountSat_default (direction : Direction)
    (amountSat : Nat) (cltvExpiry : Height) (state : HTLCState) :
    ({ direction := direction, amountSat := amountSat, cltvExpiry := cltvExpiry,
       state := state } : CommitmentHTLCOutput).netAmountSat = amountSat := rfl

/-- A `Commitment` literal that omits `trimmedTotalSat` records zero trimmed
value. -/
theorem Commitment.trimmedTotalSat_default (holder : Direction) (number funding
    toLocal toRemote fee contestDelay : Nat) (htlcs : List CommitmentHTLCOutput)
    (anchors : Bool) :
    ({ holder := holder
       commitmentNumber := number
       fundingValueSat := funding
       toLocalSat := toLocal
       toRemoteSat := toRemote
       htlcs := htlcs
       feeSat := fee
       contestDelay := contestDelay
       anchorOutputs := anchors } : Commitment).trimmedTotalSat = 0 := rfl

/-- The owned zero-HTLC constructor keeps the default stored trimmed value. -/
theorem zeroHtlcCommitment_trimmedTotalSat (holder : Direction) (number funding
    toLocal fee contestDelay : Nat) (anchors : Bool) :
    (zeroHtlcCommitment holder number funding toLocal fee contestDelay
      anchors).trimmedTotalSat = 0 := rfl

/-- Both commitments built from balances keep the default stored trimmed
value; no existing construction site needed an explicit field. -/
theorem commitmentPairOfBalances_trimmedTotalSat (localParams remoteParams
    : ChannelParams) (b : Balance) (fee number : Nat) (funder : Direction) :
    (commitmentPairOfBalances localParams remoteParams b fee number
        funder).localCommitment.trimmedTotalSat = 0 ∧
      (commitmentPairOfBalances localParams remoteParams b fee number
        funder).remoteCommitment.trimmedTotalSat = 0 :=
  ⟨rfl, rfl⟩

/-- The downstream legacy projection in `CommitmentIntegrationTargets` omits
the new field and therefore has `netAmountSat = amountSat` by definition. -/
theorem legacyHtlcOutput_netAmountSat (h : HTLCRecord) :
    (CommitmentIntegration.legacyHtlcOutput h).netAmountSat =
      (CommitmentIntegration.legacyHtlcOutput h).amountSat := rfl

/-- The downstream rich net projection also omits the new field, so its
record-level net value is its (already net) gross value. -/
theorem netHtlcOutput_netAmountSat (t s : Nat) (h : HTLCRecord) :
    (CommitmentIntegration.netHtlcOutput t s h).netAmountSat =
      (CommitmentIntegration.netHtlcOutput t s h).amountSat := rfl

/-! ## 2. The dust test at the record field -/

/-- The legacy gross dust test is retained unchanged for every pre-wave-6
consumer. -/
theorem CommitmentTx.htlcOutput_gross_retained (tx : CommitmentTx)
    (h : CommitmentHTLCOutput) :
    tx.htlcOutput h =
      (if tx.dustLimitSat ≤ h.amountSat then
        some (CommitmentTxOutput.htlc h (tx.htlcScript h)) else none) := rfl

/-- When the transaction's net projection is the record field, the canonical
dust test reads `CommitmentHTLCOutput.netAmountSat`. -/
theorem CommitmentTx.htlcOutputNet_eq_recordNet {tx : CommitmentTx}
    (hnet : tx.UsesRecordNet) (h : CommitmentHTLCOutput) :
    tx.htlcOutputNet h =
      (if tx.dustLimitSat ≤ h.netAmountSat then
        some (CommitmentTxOutput.htlc h (tx.htlcScript h)) else none) := by
  unfold CommitmentTx.htlcOutputNet
  rw [hnet h]

/-- **The net dust test at the record boundary.**  A transaction that uses the
record net projection trims an HTLC exactly when its net second-stage value is
below the owner's dust limit. -/
theorem CommitmentTx.htlcOutputNet_eq_none_iff_recordNet {tx : CommitmentTx}
    (hnet : tx.UsesRecordNet) (h : CommitmentHTLCOutput) :
    tx.htlcOutputNet h = none ↔ h.netAmountSat < tx.dustLimitSat := by
  rw [CommitmentTx.htlcOutputNet_eq_recordNet hnet]
  by_cases hd : tx.dustLimitSat ≤ h.netAmountSat <;> simp [hd] <;> omega

/-- The at-or-above-dust half of the record-level test. -/
theorem CommitmentTx.htlcOutputNet_isSome_iff_recordNet {tx : CommitmentTx}
    (hnet : tx.UsesRecordNet) (h : CommitmentHTLCOutput) :
    (tx.htlcOutputNet h).isSome = true ↔
      tx.dustLimitSat ≤ h.netAmountSat := by
  rw [CommitmentTx.htlcOutputNet_eq_recordNet hnet]
  by_cases hd : tx.dustLimitSat ≤ h.netAmountSat <;> simp [hd]

/-- BOLT 3's net test and its gross threshold are the same statement once the
record-level identity `net + second_stage_fee = gross` holds. -/
theorem CommitmentHTLCOutput.net_lt_dust_iff_gross_lt_threshold
    {h : CommitmentHTLCOutput} {dustLimitSat feeSat : Nat}
    (hnet : h.netAmountSat + feeSat = h.amountSat) :
    h.netAmountSat < dustLimitSat ↔
      h.amountSat < dustLimitSat + feeSat := by
  omega

/-- Equality with the gross threshold is kept, not trimmed. -/
theorem CommitmentHTLCOutput.not_dust_of_threshold_eq
    {h : CommitmentHTLCOutput} {dustLimitSat feeSat : Nat}
    (hnet : h.netAmountSat + feeSat = h.amountSat)
    (heq : h.amountSat = dustLimitSat + feeSat) :
    dustLimitSat ≤ h.netAmountSat := by
  omega

/-! ## 3. The record-level migration and its value accounting -/

/-- **Emitted value plus stored trimmed value is the nominal output value.**
The migration removes below-dust outputs and records their whole gross value in
`Commitment.trimmedTotalSat`; anchors are never trimmed.  No dust-limit
positivity is needed for this value identity. -/
theorem Commitment.migrateNet_totalOutputValue_add_trimmedTotalSat
    (c : Commitment) (dustLimitSat : Nat) :
    (c.migrateNet dustLimitSat).totalOutputValue +
        (c.migrateNet dustLimitSat).trimmedTotalSat =
      c.totalOutputValue := by
  have hpart := CommitmentGrossNet.sum_map_ite_add_sum_map_ite dustLimitSat
    (fun h => h.netAmountSat) (fun h => h.amountSat) c.htlcs
  have hsum : htlcOutputsValue c.htlcs =
      (c.htlcs.map (fun h => h.amountSat)).sum :=
    Commitment.htlcOutputValue_eq_sum c
  have hkeep : c.htlcs.filter (fun h => h.keepAtDust dustLimitSat) =
      c.htlcs.filter
        (CommitmentGrossNet.keepHtlc dustLimitSat (fun h => h.netAmountSat)) :=
    rfl
  unfold Commitment.migrateNet Commitment.totalOutputValue
    Commitment.htlcOutputValue Commitment.anchorOutputValue
    Commitment.trimmedSat
  rw [hkeep, CommitmentGrossNet.htlcOutputsValue_filter_keep, hsum]
  by_cases hL : dustLimitSat ≤ c.toLocalSat <;>
  by_cases hR : dustLimitSat ≤ c.toRemoteSat <;>
    simp [hL, hR] at hpart ⊢ <;>
    omega

/-- **BOLT 3 conservation at the record boundary.**  If the nominal record
satisfies the balance equation, the migrated record's emitted value plus the
same base fee plus the stored trimmed value reconstructs the funding value. -/
theorem Commitment.migrateNet_conservation (c : Commitment)
    (dustLimitSat : Nat)
    (hbal : c.totalOutputValue + c.feeSat = c.fundingValueSat) :
    (c.migrateNet dustLimitSat).totalOutputValue +
        (c.migrateNet dustLimitSat).feeSat +
        (c.migrateNet dustLimitSat).trimmedTotalSat =
      c.fundingValueSat := by
  have h := Commitment.migrateNet_totalOutputValue_add_trimmedTotalSat c
    dustLimitSat
  have hfee := Commitment.migrateNet_feeSat c dustLimitSat
  rw [hfee]
  omega

/-- **The effective fee is the base fee plus the stored trimmed value.**  The
second-stage fee is not part of it: it is withheld later by the HTLC
transaction out of the gross HTLC output. -/
theorem Commitment.migrateNet_effectiveFee_eq (c : Commitment)
    (dustLimitSat : Nat)
    (hbal : c.totalOutputValue + c.feeSat = c.fundingValueSat) :
    (c.migrateNet dustLimitSat).effectiveFeeSat =
      c.feeSat + (c.migrateNet dustLimitSat).trimmedTotalSat := by
  have h := Commitment.migrateNet_conservation c dustLimitSat hbal
  have hfee := Commitment.migrateNet_feeSat c dustLimitSat
  rw [hfee] at h
  have hle : (c.migrateNet dustLimitSat).totalOutputValue ≤
      c.fundingValueSat := by omega
  unfold Commitment.effectiveFeeSat
  exact (Nat.sub_eq_iff_eq_add hle).2 (by omega)

/-- The effective fee is the funding residual for the migrated record. -/
theorem Commitment.migrateNet_effectiveFee_val (c : Commitment)
    (dustLimitSat : Nat) :
    (c.migrateNet dustLimitSat).effectiveFeeSat =
      c.fundingValueSat - (c.migrateNet dustLimitSat).totalOutputValue := rfl

/-- The stored field on the migrated record is exactly the computed nominal
trim value under the record net projection. -/
theorem Commitment.migrateNet_trimmedTotalSat_eq_trimmedSat
    (c : Commitment) (dustLimitSat : Nat) :
    (c.migrateNet dustLimitSat).trimmedTotalSat =
      c.trimmedSat dustLimitSat (fun h => h.netAmountSat) := rfl

/-- The same statement through the future-facing alias. -/
theorem Commitment.migrateNet_trimmedTotalSat_eq_trimmedValueFor
    (c : Commitment) (dustLimitSat : Nat) :
    (c.migrateNet dustLimitSat).trimmedTotalSat =
      c.trimmedValueFor dustLimitSat (fun h => h.netAmountSat) := rfl

/-- Every HTLC retained by the record migration satisfies the net dust test. -/
theorem Commitment.migrateNet_htlc_survives (c : Commitment)
    (dustLimitSat : Nat) {h : CommitmentHTLCOutput}
    (hmem : h ∈ (c.migrateNet dustLimitSat).htlcs) :
    dustLimitSat ≤ h.netAmountSat := by
  rw [Commitment.migrateNet_htlcs] at hmem
  exact CommitmentHTLCOutput.keepAtDust_eq_true_iff.1
    (List.mem_filter.1 hmem).2

/-- A general stored-field balance form: if emitted value, base fee, and stored
trimmed value add up to funding, then the effective fee is the base fee plus
the stored trimmed value. -/
theorem Commitment.effectiveFee_eq_feeSat_add_trimmedTotalSat
    (c : Commitment)
    (h : c.totalOutputValue + c.feeSat + c.trimmedTotalSat =
      c.fundingValueSat) :
    c.effectiveFeeSat = c.feeSat + c.trimmedTotalSat := by
  have hle : c.totalOutputValue ≤ c.fundingValueSat := by omega
  unfold Commitment.effectiveFeeSat
  exact (Nat.sub_eq_iff_eq_add hle).2 (by omega)

/-! ## 4. The transaction-level migration -/

/-- The migrated transaction is a `Migrated` record: zeroed non-HTLC outputs
are below dust, survivors satisfy the record net test.  BOLT 2 requires
`dust_limit_satoshis >= 354`, so the positivity hypothesis is the protocol
domain. -/
theorem CommitmentTx.migrateNet_migrated (tx : CommitmentTx)
    (hdust : 0 < tx.dustLimitSat) : (tx.migrateNet).Migrated := by
  unfold CommitmentTx.Migrated
  constructor
  · unfold CommitmentTx.migrateNet Commitment.migrateNet
    dsimp only
    by_cases hL : tx.dustLimitSat ≤ tx.commitment.toLocalSat
    · have hpos : tx.commitment.toLocalSat ≠ 0 := by omega
      have hnot : ¬ tx.commitment.toLocalSat < tx.dustLimitSat := by omega
      simp [hL, hpos, hnot]
    · have hlt : tx.commitment.toLocalSat < tx.dustLimitSat :=
        Nat.lt_of_not_le hL
      simp [hL]
      omega
  · constructor
    · unfold CommitmentTx.migrateNet Commitment.migrateNet
      dsimp only
      by_cases hR : tx.dustLimitSat ≤ tx.commitment.toRemoteSat
      · have hpos : tx.commitment.toRemoteSat ≠ 0 := by omega
        have hnot : ¬ tx.commitment.toRemoteSat < tx.dustLimitSat := by omega
        simp [hR, hpos, hnot]
      · have hlt : tx.commitment.toRemoteSat < tx.dustLimitSat :=
          Nat.lt_of_not_le hR
        simp [hR]
        omega
    · intro h hmem
      rw [CommitmentTx.migrateNet_htlcs] at hmem
      exact CommitmentHTLCOutput.keepAtDust_eq_true_iff.1
        (List.mem_filter.1 hmem).2

/-- Every HTLC left in the migrated transaction satisfies the record net dust
test. -/
theorem CommitmentTx.migrateNet_htlc_survives (tx : CommitmentTx)
    {h : CommitmentHTLCOutput} (hmem : h ∈ (tx.migrateNet).commitment.htlcs) :
    tx.dustLimitSat ≤ h.netAmountSat := by
  rw [CommitmentTx.migrateNet_htlcs] at hmem
  exact CommitmentHTLCOutput.keepAtDust_eq_true_iff.1
    (List.mem_filter.1 hmem).2

/-- The stored transaction-level trimmed value and the stored record-level
trimmed value are the same number on a migrated transaction. -/
theorem CommitmentTx.migrateNet_trimmedSat_eq_commitment_trimmedTotalSat
    (tx : CommitmentTx) :
    (tx.migrateNet).trimmedSat =
      (tx.migrateNet).commitment.trimmedTotalSat := rfl

/-- The migrated transaction's stored trimmed value is the computed record
value `Commitment.trimmedValueFor` under the record net projection. -/
theorem CommitmentTx.migrateNet_trimmedSat_eq_trimmedValueFor
    (tx : CommitmentTx) :
    (tx.migrateNet).trimmedSat =
      tx.commitment.trimmedValueFor tx.dustLimitSat
        (fun h => h.netAmountSat) := rfl

/-- **Emitted value plus stored transaction trimmed value is the nominal output
value at the transaction boundary.** -/
theorem CommitmentTx.migrateNet_totalOutputValue_add_trimmedSat
    (tx : CommitmentTx) :
    (tx.migrateNet).commitment.totalOutputValue +
        (tx.migrateNet).trimmedSat =
      tx.commitment.totalOutputValue := by
  have h := Commitment.migrateNet_totalOutputValue_add_trimmedTotalSat
    tx.commitment tx.dustLimitSat
  have h' : (tx.migrateNet).trimmedSat =
      (tx.commitment.migrateNet tx.dustLimitSat).trimmedTotalSat := rfl
  rw [CommitmentTx.migrateNet_commitment, h']
  exact h

/-- **Transaction-boundary conservation.** -/
theorem CommitmentTx.migrateNet_conservation (tx : CommitmentTx)
    (hbal : tx.commitment.totalOutputValue + tx.commitment.feeSat =
      tx.commitment.fundingValueSat) :
    (tx.migrateNet).commitment.totalOutputValue +
        (tx.migrateNet).commitment.feeSat +
        (tx.migrateNet).trimmedSat =
      tx.commitment.fundingValueSat := by
  have h := CommitmentTx.migrateNet_totalOutputValue_add_trimmedSat tx
  have hfee : (tx.migrateNet).commitment.feeSat = tx.commitment.feeSat := rfl
  rw [hfee]
  omega

/-- **Transaction-boundary effective-fee accounting.** -/
theorem CommitmentTx.migrateNet_effectiveFee_eq (tx : CommitmentTx)
    (hbal : tx.commitment.totalOutputValue + tx.commitment.feeSat =
      tx.commitment.fundingValueSat) :
    (tx.migrateNet).commitment.effectiveFeeSat =
      (tx.migrateNet).commitment.feeSat + (tx.migrateNet).trimmedSat := by
  have h := CommitmentTx.migrateNet_conservation tx hbal
  have hle : (tx.migrateNet).commitment.totalOutputValue ≤
      tx.commitment.fundingValueSat := by omega
  unfold Commitment.effectiveFeeSat
  exact (Nat.sub_eq_iff_eq_add hle).2 (by omega)

/-! ## 5. Canonical refinement at the record boundary -/

/-- The migrated sorted net output list is a permutation of the migrated
canonical trimmed list. -/
theorem CommitmentTx.migrateNet_outputsNet_perm_canonicalOutputs
    (tx : CommitmentTx) :
    ((tx.migrateNet).outputsNet.map CommitmentTxOutput.toCommitmentOutput).Perm
      (tx.migrateNet).canonicalOutputs :=
  CommitmentGrossNet.outputsNet_refines_canonicalOutputs tx.migrateNet

/-- **Canonical refinement to the legacy consumer path.**  On a migrated
transaction the sorted net output list is a permutation of
`Commitment.commitmentOutputs`.  This is the wave-6 form of the CH-01/CH-04
refinement: gross output values, net dust test, stored trimmed value. -/
theorem CommitmentTx.migrateNet_outputsNet_perm_commitmentOutputs
    (tx : CommitmentTx) (hdust : 0 < tx.dustLimitSat) :
    ((tx.migrateNet).outputsNet.map CommitmentTxOutput.toCommitmentOutput).Perm
      (tx.migrateNet).commitment.commitmentOutputs :=
  CommitmentGrossNet.outputsNet_perm_commitmentOutputs_of_migrated
    tx.migrateNet (CommitmentTx.migrateNet_migrated tx hdust)

/-- The migrated canonical list is exactly the legacy output path on the
migrated record. -/
theorem CommitmentTx.migrateNet_canonicalOutputs_eq_commitmentOutputs
    (tx : CommitmentTx) (hdust : 0 < tx.dustLimitSat) :
    (tx.migrateNet).canonicalOutputs =
      (tx.migrateNet).commitment.commitmentOutputs :=
  CommitmentGrossNet.canonicalOutputs_eq_commitmentOutputs_of_migrated
    tx.migrateNet (CommitmentTx.migrateNet_migrated tx hdust)

/-- The net projection of the migrated transaction is the record field, so the
canonical net dust test of Section 2 applies to it. -/
theorem CommitmentTx.migrateNet_htlcOutputNet_eq_none_iff
    (tx : CommitmentTx) (h : CommitmentHTLCOutput) :
    (tx.migrateNet).htlcOutputNet h = none ↔
      h.netAmountSat < tx.dustLimitSat :=
  CommitmentTx.htlcOutputNet_eq_none_iff_recordNet
    (CommitmentTx.migrateNet_usesRecordNet tx) h

/-! ## 6. The record field under the BOLT 3 fee schedule -/

/-- The record-level form of BOLT 3's second-stage relation:
`net + second_stage_fee = gross`.  It is a hypothesis, not a definition,
because the net field is caller-supplied. -/
def NetConsistentOnRecords (c : Commitment) (anchors : Bool) (r : FeeRate) :
    Prop :=
  ∀ h ∈ c.htlcs,
    h.netAmountSat + CommitmentGrossNet.htlcSecondStageFee anchors r h =
      h.amountSat

/-- The record-level net relation implies the wave-5 `CommitmentTx`
`NetConsistent` relation on the migrated transaction. -/
theorem CommitmentTx.netConsistent_migrateNet {tx : CommitmentTx}
    {anchors : Bool} {r : FeeRate}
    (hc : NetConsistentOnRecords tx.commitment anchors r) :
    CommitmentGrossNet.NetConsistent (tx.migrateNet) anchors r := by
  intro h hmem
  rw [CommitmentTx.migrateNet_htlcs] at hmem
  exact hc h (List.mem_filter.1 hmem).1

/-- On a record with the BOLT 3 net relation, the migrated transaction trims
exactly the HTLCs whose gross value is below `dust_limit + second_stage_fee`. -/
theorem CommitmentTx.migrateNet_trims_iff_gross_threshold
    (tx : CommitmentTx) {anchors : Bool} {r : FeeRate}
    (hc : NetConsistentOnRecords tx.commitment anchors r)
    {h : CommitmentHTLCOutput}
    (hmem : h ∈ (tx.migrateNet).commitment.htlcs) :
    (tx.migrateNet).htlcOutputNet h = none ↔
      h.amountSat < tx.dustLimitSat +
        CommitmentGrossNet.htlcSecondStageFee anchors r h :=
  CommitmentGrossNet.htlcOutputNet_eq_none_iff_gross_threshold
    tx.migrateNet h anchors r
    (CommitmentTx.netConsistent_migrateNet hc h hmem)

/-! ## 7. Preserved refutations and the wave-5 path -/

/-- D12's unconditional ordering refutation is retained unchanged. -/
theorem d12_output_ordering_fails_retained :
    ¬ (∀ c : Commitment,
        (c.commitmentOutputs.map CommitmentOutput.value).Pairwise (· ≤ ·)) :=
  LnLean.Proofs.WaveD.D12.waveD_d12_output_ordering_fails

/-- D12's zero-valued HTLC counterexample is retained unchanged. -/
theorem d12_zero_value_htlc_emitted_retained :
    CommitmentOutput.htlc .local 0 ∈
      LnLean.Proofs.WaveD.D12.zeroValueHtlcCommitment.commitmentOutputs :=
  LnLean.Proofs.WaveD.D12.waveD_d12_zero_value_htlc_emitted

/-- The wave-5 positive-dust `migratedFrom` refinement remains available
unchanged; the record-field migration is an additional path, not a weakening. -/
theorem wave5_migratedFrom_outputsNet_perm_commitmentOutputs_retained
    (tx : CommitmentTx) (hdust : 0 < tx.dustLimitSat) :
    ((tx.migratedFrom).outputsNet.map
        CommitmentTxOutput.toCommitmentOutput).Perm
      (tx.migratedFrom).commitment.commitmentOutputs :=
  CommitmentTx.migratedFrom_outputsNet_perm_commitmentOutputs tx hdust

/-- The wave-4 zero-dust counterexample is retained: trimming changes the
output multiset, so a permutation is not unconditional. -/
theorem wave4_dust_trimming_not_perm_retained :
    ¬ (CommitmentIntegration.legacyOutputs
          CommitmentIntegration.dustDemoTx).Perm
        CommitmentIntegration.dustDemoTx.commitment.commitmentOutputs :=
  CommitmentIntegration.dust_trimming_not_perm

end LnLean.Proofs.Channel.CommitmentTypes
