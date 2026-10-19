/-
# H27 — downstream net-output conservation and effective-fee accounting
(CH-01, CH-02)

**Catalog issues.**

* `CH-02` (P1, closed at the record layer): the second-stage fee / dust trim
  path was integrated in `CommitmentGrossNetTargets` and
  `CommitmentTypesTargets`, which prove
  `emitted + base fee + trimmedTotalSat = funding` and
  `effectiveFeeSat = feeSat + trimmedTotalSat` at the `Commitment` /
  `CommitmentTx` record boundary.
* `CH-01` (P1, closed for the consumer path): wave 7 added the downstream
  consumer API `CommitmentTx.consumerOutputs`, `migrateForConsumer`,
  `migratedConsumerOutputs`, `netConsumerOutputs` and the canonical
  permutation.  What was still missing is the *value* account at that
  downstream boundary: the actual lists a consumer reads were related to
  `commitmentOutputs` by permutations, but no theorem said that their emitted
  value plus the base fee plus the stored trimmed value reconstructs the
  funding value, or that the effective fee they imply is the base fee plus
  the trimmed value.

This module supplies exactly that downstream account.

## Results

1. **Value faithfulness of the migrated consumer list.**  For every
   `CommitmentTx tx`, the legacy-shaped migrated list
   `tx.migratedConsumerOutputs` and the sorted rich list
   `tx.netConsumerOutputs` have the *same* emitted value, equal to
   `(tx.migrateNet).commitment.totalOutputValue`.  No dust-limit positivity
   hypothesis is used: zero-valued trimmed non-HTLC outputs contribute zero
   and surviving HTLCs contribute their gross `amountSat`.
2. **Three-term conservation at the downstream boundary.**  If the *nominal*
   record is conserved (`CommitmentConserved tx.commitment`), then
   `emitted + (tx.migrateNet).commitment.feeSat +
   (tx.migrateNet).commitment.trimmedTotalSat = funding`, for the legacy and
   the rich consumer lists alike.
3. **Effective-fee accounting downstream.**  Under the same hypothesis,
   `(tx.migrateNet).commitment.effectiveFeeSat =
   (tx.migrateNet).commitment.feeSat +
   (tx.migrateNet).commitment.trimmedTotalSat`, and equivalently
   `= tx.commitment.feeSat + tx.recordTrimmedValue` (the stored
   `Commitment.trimmedTotalSat` boundary).  The second-stage HMTC fee is not
   part of this number: it is withheld later by the HTLC transaction out of
   the gross HTLC output.
4. **The exact hypothesis boundary.**
   * `CommitmentConserved tx.commitment` is *necessary*.  A concrete
     under-funded record (`underfundedTx`) satisfies neither the three-term
     equation nor the effective-fee identity after migration.
   * `0 < dustLimitSat` is **not** needed for any value theorem in this
     module.  It is needed only for the list-equality/`Migrated` normal form
     used by the consumer-permutation results, not for the accounting.
   * The legacy `CommitmentConserved` predicate is *not* preserved by
     migration when anything is trimmed:
     `CommitmentConserved (tx.migrateNet).commitment ↔ trimmedTotalSat = 0`.
     With trimming, the correct downstream relation is the three-term
     equation / `effectiveFeeSat`, not the two-term predicate.  The concrete
     `dustDemoTx` (a 500-sat HTLC under a 1000-sat dust limit) exhibits
     `effectiveFeeSat = 500` while `CommitmentConserved` fails.
5. **Construction sites.**  The accounting is instantiated for
   `commitmentPairOfBalances` (both sides, in the anchor-disabled BOLT 3
   domain where that constructor is known to conserve) and for the
   `CommitmentTx.ofCommitment` lift.

## Scope caveats

* Scripts, signatures, witnesses, sighash, and the second-stage HTLC
  transactions are out of scope; this is output-value accounting only.
* `CommitmentHTLCOutput.netAmountSat` is caller-supplied.  Its relation to
  the gross value is the explicit `NetConsistentOnRecords` hypothesis of
  `CommitmentTypesTargets`; no theorem here assumes it.
* The emitted value is a *sum*, not an order.  D12's ordering refutation and
  wave-4's trimming counterexample remain true and are restated below.
* `trimmedTotalSat` is the stored gross value removed by trimming; the naming
  decision of waves 6/7 (`trimmedTotalSat` stored, `trimmedSat` computed) is
  kept unchanged.

## Anchors

* BOLT 3 §2 "Trimmed Outputs" (`refs/bolts/03-transactions.md:308-367`): a
  trimmed output's whole gross value is added to the commitment fee; the
  commitment output carries the gross HTLC value while the dust test uses the
  post-second-stage-fee value.
* BOLT 3 §4 "Fees" (`refs/bolts/03-transactions.md:464-576`): the base fee is
  `feerate_per_kw * weight / 1000`; the second-stage fee is paid by the
  HTLC-timeout/success transaction, not by the commitment transaction.
* Model: `LnLean/Proofs/Channel/CommitmentGrossNetTargets.lean` §5-6,
  `LnLean/Proofs/Channel/CommitmentTypesTargets.lean` §3-4,
  `LnLean/Channel/Commitment.lean` (CH-01 consumer path),
  `LnLean/Proofs/Conservation.lean` (`CommitmentConserved`, `ChannelLedger`).
-/

import LnLean.Proofs.Channel.CommitmentConsumerTargets
import LnLean.Proofs.Conservation

namespace LnLean.Proofs.WaveH.H27

set_option autoImplicit false

open LnLean
open LnLean.Channel
open LnLean.Proofs
open LnLean.Proofs.Channel

/-! ## 0. A sum lemma for permutations -/

/-- Permutations preserve the sum of a `Nat`-valued image.  Stated locally
because it is the only list-permutation/sum fact this module needs. -/
theorem perm_sum_map_eq_nat {α : Type} (f : α → Nat) {l₁ l₂ : List α}
    (h : l₁.Perm l₂) : (l₁.map f).sum = (l₂.map f).sum := by
  induction h with
  | nil => rfl
  | cons a _ ih => simp [ih]
  | swap a b l => simp [Nat.add_left_comm]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Filtering a list and then mapping `g` sums the `g` values of the kept
elements.  This is the list-level form used by the net HTLC value count. -/
theorem sum_map_filter_prop {α : Type} (p : α → Prop) [DecidablePred p]
    (g : α → Nat) :
    ∀ l : List α,
      ((l.filter p).map g).sum =
        (l.map (fun a => if p a then g a else 0)).sum
  | [] => rfl
  | a :: t => by
      by_cases hp : p a <;> simp [hp, sum_map_filter_prop p g t]

/-- A `filterMap` with a `some`/`none` test is a filter followed by a map. -/
theorem filterMap_if_some_map {α β : Type} (p : α → Prop) [DecidablePred p]
    (f : α → β) :
    ∀ l : List α,
      l.filterMap (fun a => if p a then some (f a) else none) =
        (l.filter p).map f
  | [] => rfl
  | a :: t => by
      by_cases hp : p a <;> simp [hp, filterMap_if_some_map p f t]

/-! ## 1. The emitted value of each downstream list -/

/-- The value contributed by the `to_local` slot of the rich net list: either
the output value or zero when it is trimmed. -/
theorem toLocalOutput_value_sum (tx : CommitmentTx) :
    ((tx.toLocalOutput.toList.map (fun o => o.valueSat)).sum) =
      if tx.dustLimitSat ≤ tx.commitment.toLocalSat then
        tx.commitment.toLocalSat else 0 := by
  unfold CommitmentTx.toLocalOutput CommitmentTxOutput.toLocal
  by_cases h : tx.dustLimitSat ≤ tx.commitment.toLocalSat <;> simp [h]

/-- The value contributed by the `to_remote` slot of the rich net list. -/
theorem toRemoteOutput_value_sum (tx : CommitmentTx) :
    ((tx.toRemoteOutput.toList.map (fun o => o.valueSat)).sum) =
      if tx.dustLimitSat ≤ tx.commitment.toRemoteSat then
        tx.commitment.toRemoteSat else 0 := by
  unfold CommitmentTx.toRemoteOutput CommitmentTxOutput.toRemote
  by_cases h : tx.dustLimitSat ≤ tx.commitment.toRemoteSat <;> simp [h]

/-- The value contributed by the HTLC slots of the rich net list: the gross
`amountSat` of each surviving HTLC and zero for each trimmed one. -/
theorem htlcOutputNet_value_sum (tx : CommitmentTx) :
    (((tx.commitment.htlcs.filterMap tx.htlcOutputNet).map
        (fun o => o.valueSat)).sum) =
      (tx.commitment.htlcs.map (fun h =>
        if tx.dustLimitSat ≤ tx.netAmountSat h then h.amountSat else 0)).sum := by
  have hfm : tx.commitment.htlcs.filterMap tx.htlcOutputNet =
      (tx.commitment.htlcs.filter
        (fun h => tx.dustLimitSat ≤ tx.netAmountSat h)).map
        (fun h => CommitmentTxOutput.htlc h (tx.htlcScript h)) := by
    unfold CommitmentTx.htlcOutputNet
    exact filterMap_if_some_map _ _ _
  rw [hfm, List.map_map]
  rw [show ((fun o => o.valueSat) ∘
      fun h => CommitmentTxOutput.htlc h (tx.htlcScript h)) =
      (fun h => h.amountSat) from by
    funext h
    rfl]
  exact sum_map_filter_prop (fun h => tx.dustLimitSat ≤ tx.netAmountSat h)
    (fun h => h.amountSat) tx.commitment.htlcs

/-- The value contributed by the local anchor slot. -/
theorem localAnchorOutput_value_sum (tx : CommitmentTx) :
    ((tx.localAnchorOutput.toList.map (fun o => o.valueSat)).sum) =
      if tx.commitment.anchorOutputs then anchorOutputSat else 0 := by
  unfold CommitmentTx.localAnchorOutput CommitmentTxOutput.localAnchor
  by_cases h : tx.commitment.anchorOutputs <;> simp [h]

/-- The value contributed by the remote anchor slot. -/
theorem remoteAnchorOutput_value_sum (tx : CommitmentTx) :
    ((tx.remoteAnchorOutput.toList.map (fun o => o.valueSat)).sum) =
      if tx.commitment.anchorOutputs then anchorOutputSat else 0 := by
  unfold CommitmentTx.remoteAnchorOutput CommitmentTxOutput.remoteAnchor
  by_cases h : tx.commitment.anchorOutputs <;> simp [h]

/-- The emitted value of the rich pre-sort net list, in closed form. -/
theorem outputsUnsortedNet_value_sum (tx : CommitmentTx) :
    ((tx.outputsUnsortedNet.map (fun o => o.valueSat)).sum) =
      (if tx.dustLimitSat ≤ tx.commitment.toLocalSat then
        tx.commitment.toLocalSat else 0) +
      (if tx.dustLimitSat ≤ tx.commitment.toRemoteSat then
        tx.commitment.toRemoteSat else 0) +
      (tx.commitment.htlcs.map (fun h =>
        if tx.dustLimitSat ≤ tx.netAmountSat h then h.amountSat else 0)).sum +
      tx.commitment.anchorOutputValue := by
  unfold CommitmentTx.outputsUnsortedNet
  simp only [List.map_append, List.sum_append]
  rw [toLocalOutput_value_sum, toRemoteOutput_value_sum,
    htlcOutputNet_value_sum, localAnchorOutput_value_sum,
    remoteAnchorOutput_value_sum]
  unfold Commitment.anchorOutputValue
  by_cases ha : tx.commitment.anchorOutputs <;> simp [ha] <;> omega

/-- Sorting preserves the emitted value. -/
theorem outputsNet_value_sum (tx : CommitmentTx) :
    ((tx.outputsNet.map (fun o => o.valueSat)).sum) =
      ((tx.outputsUnsortedNet.map (fun o => o.valueSat)).sum) :=
  perm_sum_map_eq_nat _ (CommitmentTx.outputsNet_perm tx)

/-- A record whose non-HTLC slots are either zero or at least the dust limit
and whose HTLCs all survive the net dust test emits exactly its
`totalOutputValue`.  This is the general form; the migrated record satisfies
both premises by construction. -/
theorem outputsNet_value_sum_eq_totalOutputValue_of {t : CommitmentTx}
    (hL : (if t.dustLimitSat ≤ t.commitment.toLocalSat then
        t.commitment.toLocalSat else 0) = t.commitment.toLocalSat)
    (hR : (if t.dustLimitSat ≤ t.commitment.toRemoteSat then
        t.commitment.toRemoteSat else 0) = t.commitment.toRemoteSat)
    (hH : ∀ h ∈ t.commitment.htlcs, t.dustLimitSat ≤ t.netAmountSat h) :
    ((t.outputsNet.map (fun o => o.valueSat)).sum) =
      t.commitment.totalOutputValue := by
  rw [outputsNet_value_sum, outputsUnsortedNet_value_sum]
  have hht : (t.commitment.htlcs.map (fun h =>
      if t.dustLimitSat ≤ t.netAmountSat h then h.amountSat else 0)).sum =
      t.commitment.htlcOutputValue := by
    rw [Commitment.htlcOutputValue_eq_sum]
    congr 1
    apply List.map_congr_left
    intro h hmem
    simp [hH h hmem]
  rw [hL, hR, hht]
  rfl

/-- The migrated record's emitted rich value is its `totalOutputValue`. -/
theorem migrateNet_outputsNet_value_sum_eq_totalOutputValue (tx : CommitmentTx) :
    (((tx.migrateNet).outputsNet.map (fun o => o.valueSat)).sum) =
      (tx.migrateNet).commitment.totalOutputValue := by
  apply outputsNet_value_sum_eq_totalOutputValue_of
  · unfold CommitmentTx.migrateNet Commitment.migrateNet
    dsimp only
    by_cases hd : tx.dustLimitSat ≤ tx.commitment.toLocalSat
    · simp [hd]
    · by_cases h0 : tx.dustLimitSat ≤ 0 <;> simp [hd, h0]
  · unfold CommitmentTx.migrateNet Commitment.migrateNet
    dsimp only
    by_cases hd : tx.dustLimitSat ≤ tx.commitment.toRemoteSat
    · simp [hd]
    · by_cases h0 : tx.dustLimitSat ≤ 0 <;> simp [hd, h0]
  · intro h hmem
    exact CommitmentTypes.CommitmentTx.migrateNet_htlc_survives tx hmem

/-- **The legacy-shaped migrated consumer list is value-faithful.**  Its value
sum is exactly the migrated record's `totalOutputValue`; this is
`Commitment.commitmentOutputs_sum_eq_totalOutputValue` at the consumer
boundary. -/
theorem migratedConsumerOutputs_sum_eq_totalOutputValue (tx : CommitmentTx) :
    (tx.migratedConsumerOutputs.map CommitmentOutput.value).sum =
      (tx.migrateNet).commitment.totalOutputValue := by
  rw [CommitmentConsumer.migratedConsumerOutputs_eq]
  exact Commitment.commitmentOutputs_sum_eq_totalOutputValue _

/-- **The rich sorted net consumer list is value-faithful.**  Its value sum is
also exactly the migrated record's `totalOutputValue`.  The proof uses only
the migrated record's survivor facts; no `0 < dustLimitSat` hypothesis is
needed, because a zeroed `to_local`/`to_remote` contributes zero either way. -/
theorem netConsumerOutputs_value_sum_eq_totalOutputValue (tx : CommitmentTx) :
    ((tx.netConsumerOutputs.map (fun o => o.valueSat)).sum) =
      (tx.migrateNet).commitment.totalOutputValue := by
  rw [CommitmentConsumer.netConsumerOutputs_eq]
  exact migrateNet_outputsNet_value_sum_eq_totalOutputValue tx

/-- **Trimming removes exactly the stored gross trimmed value from the
consumer-visible list.**  This is the no-hypothesis value form of
`emitted + trimmed = nominal emitted`: it holds for every transaction, because
it is the wave-5 total-output split read at the downstream list boundary. -/
theorem migratedConsumerOutputs_sum_add_trimmed_eq_consumerOutputs
    (tx : CommitmentTx) :
    (tx.migratedConsumerOutputs.map CommitmentOutput.value).sum +
        (tx.migrateNet).commitment.trimmedTotalSat =
      (tx.consumerOutputs.map CommitmentOutput.value).sum := by
  rw [migratedConsumerOutputs_sum_eq_totalOutputValue,
    CommitmentConsumer.consumerOutputs_eq_commitmentOutputs,
    Commitment.commitmentOutputs_sum_eq_totalOutputValue]
  have h :=
    CommitmentTypes.CommitmentTx.migrateNet_totalOutputValue_add_trimmedSat tx
  have ht :=
    CommitmentTypes.CommitmentTx.migrateNet_trimmedSat_eq_commitment_trimmedTotalSat tx
  rw [ht] at h
  exact h

/-- The two downstream lists carry the same emitted value.  A consumer can
switch from `List CommitmentOutput` to `List CommitmentTxOutput` without
changing the value it accounts for. -/
theorem netConsumerOutputs_value_sum_eq_migratedConsumerOutputs
    (tx : CommitmentTx) :
    ((tx.netConsumerOutputs.map (fun o => o.valueSat)).sum) =
      (tx.migratedConsumerOutputs.map CommitmentOutput.value).sum := by
  rw [netConsumerOutputs_value_sum_eq_totalOutputValue,
    migratedConsumerOutputs_sum_eq_totalOutputValue]

/-- The same trimming-delta identity for the rich net list. -/
theorem netConsumerOutputs_value_sum_add_trimmed_eq_consumerOutputs
    (tx : CommitmentTx) :
    ((tx.netConsumerOutputs.map (fun o => o.valueSat)).sum) +
        (tx.migrateNet).commitment.trimmedTotalSat =
      (tx.consumerOutputs.map CommitmentOutput.value).sum := by
  rw [netConsumerOutputs_value_sum_eq_migratedConsumerOutputs]
  exact migratedConsumerOutputs_sum_add_trimmed_eq_consumerOutputs tx

/-! ## 2. Three-term conservation at the downstream boundary -/

/-- **Downstream conservation, legacy-shaped list.**  If the nominal record
satisfies the BOLT 3 balance equation (`CommitmentConserved`), then the
consumer-visible emitted value plus the base fee plus the stored trimmed total
reconstructs the funding value.  The migrated record's stored
`trimmedTotalSat` is the only extra term: the base fee is unchanged. -/
theorem migratedConsumerOutputs_conservation (tx : CommitmentTx)
    (hc : CommitmentConserved tx.commitment) :
    (tx.migratedConsumerOutputs.map CommitmentOutput.value).sum +
        (tx.migrateNet).commitment.feeSat +
        (tx.migrateNet).commitment.trimmedTotalSat =
      tx.commitment.fundingValueSat := by
  rw [migratedConsumerOutputs_sum_eq_totalOutputValue]
  have hbal : tx.commitment.totalOutputValue + tx.commitment.feeSat =
      tx.commitment.fundingValueSat := (commitmentConserved_iff _).1 hc
  have h := CommitmentTypes.CommitmentTx.migrateNet_conservation tx hbal
  have ht :=
    CommitmentTypes.CommitmentTx.migrateNet_trimmedSat_eq_commitment_trimmedTotalSat tx
  rw [ht] at h
  exact h

/-- **Downstream conservation, rich net list.**  The same three-term identity
for the sorted rich list a `CommitmentTxOutput`-aware consumer reads. -/
theorem netConsumerOutputs_conservation (tx : CommitmentTx)
    (hc : CommitmentConserved tx.commitment) :
    ((tx.netConsumerOutputs.map (fun o => o.valueSat)).sum) +
        (tx.migrateNet).commitment.feeSat +
        (tx.migrateNet).commitment.trimmedTotalSat =
      tx.commitment.fundingValueSat := by
  rw [netConsumerOutputs_value_sum_eq_totalOutputValue]
  have hbal : tx.commitment.totalOutputValue + tx.commitment.feeSat =
      tx.commitment.fundingValueSat := (commitmentConserved_iff _).1 hc
  have h := CommitmentTypes.CommitmentTx.migrateNet_conservation tx hbal
  have ht :=
    CommitmentTypes.CommitmentTx.migrateNet_trimmedSat_eq_commitment_trimmedTotalSat tx
  rw [ht] at h
  exact h

/-- The emitted value is the funding residual after the base fee and the
trimmed total.  This is the "no value creation" direction of the three-term
equation. -/
theorem migratedConsumerOutputs_sum_eq_funding_sub_fee_sub_trimmed
    (tx : CommitmentTx) (hc : CommitmentConserved tx.commitment) :
    (tx.migratedConsumerOutputs.map CommitmentOutput.value).sum =
      tx.commitment.fundingValueSat -
        ((tx.migrateNet).commitment.feeSat +
          (tx.migrateNet).commitment.trimmedTotalSat) := by
  have h := migratedConsumerOutputs_conservation tx hc
  omega

/-- Emitted value never exceeds the funding value. -/
theorem migratedConsumerOutputs_sum_le_funding (tx : CommitmentTx)
    (hc : CommitmentConserved tx.commitment) :
    (tx.migratedConsumerOutputs.map CommitmentOutput.value).sum ≤
      tx.commitment.fundingValueSat := by
  have h := migratedConsumerOutputs_conservation tx hc
  omega

/-- Emitted value never exceeds the funding value (rich list). -/
theorem netConsumerOutputs_value_sum_le_funding (tx : CommitmentTx)
    (hc : CommitmentConserved tx.commitment) :
    ((tx.netConsumerOutputs.map (fun o => o.valueSat)).sum) ≤
      tx.commitment.fundingValueSat := by
  have h := netConsumerOutputs_conservation tx hc
  omega

/-- **No value creation downstream of a conserving ledger.**  If the nominal
commitment spends the ledger's funding output, the migrated consumer list
cannot pay more than the ledger's funding value. -/
theorem migrated_ledger_no_value_creation (l : ChannelLedger)
    (tx : CommitmentTx) (hc : CommitmentConserved tx.commitment)
    (hfund : tx.commitment.fundingValueSat = l.fundingValueSat) :
    (tx.migratedConsumerOutputs.map CommitmentOutput.value).sum ≤
      l.fundingValueSat := by
  have h := migratedConsumerOutputs_sum_le_funding tx hc
  omega

/-! ## 3. Effective-fee accounting at the downstream boundary -/

/-- **Effective fee = base fee + stored trimmed total.**  This is the CH-02
account in the form a downstream consumer observes.  The second-stage fee is
not included: BOLT 3 withholds it later in the HTLC-timeout/success
transaction out of the gross HTLC output. -/
theorem migrateNet_effectiveFee_eq_feeSat_add_trimmedTotalSat
    (tx : CommitmentTx) (hc : CommitmentConserved tx.commitment) :
    (tx.migrateNet).commitment.effectiveFeeSat =
      (tx.migrateNet).commitment.feeSat +
        (tx.migrateNet).commitment.trimmedTotalSat := by
  have hbal : tx.commitment.totalOutputValue + tx.commitment.feeSat =
      tx.commitment.fundingValueSat := (commitmentConserved_iff _).1 hc
  have h := CommitmentTypes.CommitmentTx.migrateNet_effectiveFee_eq tx hbal
  have ht :=
    CommitmentTypes.CommitmentTx.migrateNet_trimmedSat_eq_commitment_trimmedTotalSat tx
  rw [ht] at h
  exact h

/-- The same identity at the stored-field boundary: the base fee is the
nominal `feeSat` and the trimmed term is the stored
`Commitment.trimmedTotalSat` (computed as `recordTrimmedValue`). -/
theorem migrateNet_effectiveFee_eq_record_fields (tx : CommitmentTx)
    (hc : CommitmentConserved tx.commitment) :
    (tx.migrateNet).commitment.effectiveFeeSat =
      tx.commitment.feeSat + tx.recordTrimmedValue := by
  have h := migrateNet_effectiveFee_eq_feeSat_add_trimmedTotalSat tx hc
  have ht :=
    CommitmentTypes.CommitmentTx.migrateNet_trimmedSat_eq_commitment_trimmedTotalSat tx
  have hr := CommitmentTx.migrateNet_trimmedSat tx
  rw [← ht] at h
  rw [hr] at h
  rw [CommitmentTx.migrateNet_commitment, Commitment.migrateNet_feeSat] at h
  exact h

/-- The effective fee is the funding residual after the consumer-visible
emitted value. -/
theorem migrateNet_effectiveFee_eq_funding_sub_emitted (tx : CommitmentTx) :
    (tx.migrateNet).commitment.effectiveFeeSat =
      tx.commitment.fundingValueSat -
        (tx.migratedConsumerOutputs.map CommitmentOutput.value).sum := by
  rw [migratedConsumerOutputs_sum_eq_totalOutputValue]
  rfl

/-- **The complete downstream net-output account.**  Under exactly the nominal
BOLT 3 balance equation, the migrated construction satisfies both consumer
forms of `emitted + base fee + trimmed = funding`, the effective-fee identity,
and the residual form of the emitted value.  No dust-limit positivity
hypothesis appears. -/
theorem downstream_net_output_accounting (tx : CommitmentTx)
    (hc : CommitmentConserved tx.commitment) :
    (tx.migratedConsumerOutputs.map CommitmentOutput.value).sum +
        (tx.migrateNet).commitment.feeSat +
        (tx.migrateNet).commitment.trimmedTotalSat =
      tx.commitment.fundingValueSat ∧
    ((tx.netConsumerOutputs.map (fun o => o.valueSat)).sum) +
        (tx.migrateNet).commitment.feeSat +
        (tx.migrateNet).commitment.trimmedTotalSat =
      tx.commitment.fundingValueSat ∧
    (tx.migrateNet).commitment.effectiveFeeSat =
        (tx.migrateNet).commitment.feeSat +
          (tx.migrateNet).commitment.trimmedTotalSat ∧
    (tx.migratedConsumerOutputs.map CommitmentOutput.value).sum =
      tx.commitment.fundingValueSat -
        ((tx.migrateNet).commitment.feeSat +
          (tx.migrateNet).commitment.trimmedTotalSat) := by
  exact ⟨migratedConsumerOutputs_conservation tx hc,
    netConsumerOutputs_conservation tx hc,
    migrateNet_effectiveFee_eq_feeSat_add_trimmedTotalSat tx hc,
    migratedConsumerOutputs_sum_eq_funding_sub_fee_sub_trimmed tx hc⟩

/-! ## 4. The exact hypothesis boundary -/

/-- **The legacy two-term predicate is not preserved by trimming.**  The
migrated record satisfies the downstream three-term equation; its
`CommitmentConserved` reading (emitted + base fee = funding) holds exactly
when nothing was trimmed.  This is the exact reason the downstream account
must use `effectiveFeeSat`/`trimmedTotalSat` rather than the legacy
predicate. -/
theorem migrateNet_conserved_iff_no_trim (tx : CommitmentTx)
    (hc : CommitmentConserved tx.commitment) :
    CommitmentConserved (tx.migrateNet).commitment ↔
      (tx.migrateNet).commitment.trimmedTotalSat = 0 := by
  have hbal : tx.commitment.totalOutputValue + tx.commitment.feeSat =
      tx.commitment.fundingValueSat := (commitmentConserved_iff _).1 hc
  have h := CommitmentTypes.CommitmentTx.migrateNet_conservation tx hbal
  have ht :=
    CommitmentTypes.CommitmentTx.migrateNet_trimmedSat_eq_commitment_trimmedTotalSat tx
  rw [ht] at h
  change (tx.migrateNet).commitment.totalOutputValue +
      (tx.migrateNet).commitment.feeSat = tx.commitment.fundingValueSat ↔
    (tx.migrateNet).commitment.trimmedTotalSat = 0
  constructor
  · intro hcons
    omega
  · intro hzero
    omega

/-- A non-zero trimmed total makes the migrated record non-conserving in the
legacy two-term sense. -/
theorem migrateNet_not_conserved_of_trimmed_pos (tx : CommitmentTx)
    (hc : CommitmentConserved tx.commitment)
    (hpos : 0 < (tx.migrateNet).commitment.trimmedTotalSat) :
    ¬ CommitmentConserved (tx.migrateNet).commitment := by
  rw [migrateNet_conserved_iff_no_trim tx hc]
  omega

/-! ### 4.1 `CommitmentConserved` is necessary: an under-funded record -/

/-- A record whose nominal outputs already exceed its funding value: the
balance equation fails by 11000 satoshis. -/
def underfundedTx : CommitmentTx :=
  { commitment :=
      { holder := .local
        commitmentNumber := 0
        fundingValueSat := 50000
        toLocalSat := 60000
        toRemoteSat := 0
        htlcs := []
        feeSat := 1000
        contestDelay := 0
        anchorOutputs := false }
    dustLimitSat := 354
    toLocalScript := ⟨[]⟩
    toRemoteScript := ⟨[]⟩
    localAnchorScript := ⟨[]⟩
    remoteAnchorScript := ⟨[]⟩
    htlcScript := fun _ => ⟨[]⟩ }

/-- The under-funded witness really violates the balance equation. -/
theorem underfundedTx_balance_fails :
    ¬ (underfundedTx.commitment.totalOutputValue +
        underfundedTx.commitment.feeSat =
      underfundedTx.commitment.fundingValueSat) := by
  decide

/-- **Without the balance equation the three-term account is false.**  The
migrated witness emits 60000 sat with a 1000-sat base fee and no trimming,
which is 61000 sat against a 50000-sat funding value. -/
theorem conservation_needs_balance :
    (underfundedTx.migrateNet).commitment.totalOutputValue +
        (underfundedTx.migrateNet).commitment.feeSat +
        (underfundedTx.migrateNet).commitment.trimmedTotalSat ≠
      underfundedTx.commitment.fundingValueSat := by
  decide

/-- The same failure at the actual downstream emitted list. -/
theorem emitted_sum_conservation_needs_balance :
    (underfundedTx.migratedConsumerOutputs.map CommitmentOutput.value).sum +
        (underfundedTx.migrateNet).commitment.feeSat +
        (underfundedTx.migrateNet).commitment.trimmedTotalSat ≠
      underfundedTx.commitment.fundingValueSat := by
  decide

/-- **Without the balance equation the effective-fee identity is false.**
Truncated subtraction gives `effectiveFeeSat = 0`, while
`feeSat + trimmedTotalSat = 1000`. -/
theorem effectiveFee_needs_balance :
    (underfundedTx.migrateNet).commitment.effectiveFeeSat ≠
      (underfundedTx.migrateNet).commitment.feeSat +
        (underfundedTx.migrateNet).commitment.trimmedTotalSat := by
  decide

/-! ### 4.2 A non-vacuous trimmed instance: `dustDemoTx` -/

/-- The 500-sat HTLC of `dustDemoTx` is trimmed (its net value is below the
1000-sat dust limit), and the whole gross value becomes `trimmedTotalSat`. -/
theorem dustDemoTx_migrateNet_trimmedTotalSat :
    (CommitmentIntegration.dustDemoTx.migrateNet).commitment.trimmedTotalSat =
      500 := by
  decide

/-- Nothing is emitted downstream after migration: the only output was the
trimmed HTLC. -/
theorem dustDemoTx_migratedConsumerOutputs :
    CommitmentIntegration.dustDemoTx.migratedConsumerOutputs = [] := by
  decide

/-- The migrated record has a positive trimmed total. -/
theorem dustDemoTx_migrateNet_trimmed_pos :
    0 < (CommitmentIntegration.dustDemoTx.migrateNet).commitment.trimmedTotalSat := by
  rw [dustDemoTx_migrateNet_trimmedTotalSat]
  decide

/-- The legacy two-term `CommitmentConserved` is false on the migrated demo
record: 0 emitted + 0 base fee against a 500-sat funding value.  The remaining
500 sat are exactly the trimmed total. -/
theorem dustDemoTx_migrateNet_not_conserved :
    ¬ CommitmentConserved
      (CommitmentIntegration.dustDemoTx.migrateNet).commitment := by
  rw [commitmentConserved_iff]
  decide

/-- The downstream three-term account holds on the migrated demo record:
`0 + 0 + 500 = 500`. -/
theorem dustDemoTx_migrateNet_conservation :
    (CommitmentIntegration.dustDemoTx.migrateNet).commitment.totalOutputValue +
        (CommitmentIntegration.dustDemoTx.migrateNet).commitment.feeSat +
        (CommitmentIntegration.dustDemoTx.migrateNet).commitment.trimmedTotalSat =
      CommitmentIntegration.dustDemoTx.commitment.fundingValueSat := by
  have hbal :
      CommitmentIntegration.dustDemoTx.commitment.totalOutputValue +
          CommitmentIntegration.dustDemoTx.commitment.feeSat =
        CommitmentIntegration.dustDemoTx.commitment.fundingValueSat := by
    decide
  exact CommitmentTypes.CommitmentTx.migrateNet_conservation _ hbal

/-- The effective fee on the migrated demo record is the full 500 sat, which
is the base fee (0) plus the trimmed total (500). -/
theorem dustDemoTx_migrateNet_effectiveFee :
    (CommitmentIntegration.dustDemoTx.migrateNet).commitment.effectiveFeeSat =
      500 := by
  decide

/-- The effective-fee identity is non-vacuous on the demo record. -/
theorem dustDemoTx_migrateNet_effectiveFee_eq :
    (CommitmentIntegration.dustDemoTx.migrateNet).commitment.effectiveFeeSat =
      (CommitmentIntegration.dustDemoTx.migrateNet).commitment.feeSat +
        (CommitmentIntegration.dustDemoTx.migrateNet).commitment.trimmedTotalSat := by
  have hbal :
      CommitmentIntegration.dustDemoTx.commitment.totalOutputValue +
          CommitmentIntegration.dustDemoTx.commitment.feeSat =
        CommitmentIntegration.dustDemoTx.commitment.fundingValueSat := by
    decide
  exact CommitmentTypes.CommitmentTx.migrateNet_effectiveFee_eq _ hbal

/-! ## 5. Construction sites -/

/-- **`commitmentPairOfBalances`, both sides.**  In the BOLT 3 non-anchor
domain where the owned builder is known to conserve, migrating either side
preserves the three-term account and yields the effective-fee identity. -/
theorem commitmentPairOfBalances_migrateNet_accounting
    (localParams remoteParams : ChannelParams) (b : Balance)
    (fee number dustLimitSat : Nat) (funder : Direction)
    (hLocalAnchors : localParams.anchorOutputs = false)
    (hRemoteAnchors : remoteParams.anchorOutputs = false)
    (hfit : fee ≤
      (if funder = Direction.local then b.localSat else b.remoteSat)) :
    let p := commitmentPairOfBalances localParams remoteParams b fee number funder
    (p.localCommitment.migrateNet dustLimitSat).totalOutputValue +
        (p.localCommitment.migrateNet dustLimitSat).feeSat +
        (p.localCommitment.migrateNet dustLimitSat).trimmedTotalSat =
      p.localCommitment.fundingValueSat ∧
    (p.localCommitment.migrateNet dustLimitSat).effectiveFeeSat =
        (p.localCommitment.migrateNet dustLimitSat).feeSat +
          (p.localCommitment.migrateNet dustLimitSat).trimmedTotalSat ∧
    (p.remoteCommitment.migrateNet dustLimitSat).totalOutputValue +
        (p.remoteCommitment.migrateNet dustLimitSat).feeSat +
        (p.remoteCommitment.migrateNet dustLimitSat).trimmedTotalSat =
      p.remoteCommitment.fundingValueSat ∧
    (p.remoteCommitment.migrateNet dustLimitSat).effectiveFeeSat =
        (p.remoteCommitment.migrateNet dustLimitSat).feeSat +
          (p.remoteCommitment.migrateNet dustLimitSat).trimmedTotalSat := by
  obtain ⟨hl, hr⟩ :=
    commitmentPairOfBalances_conserved localParams remoteParams b fee number
      funder hLocalAnchors hRemoteAnchors hfit
  have hl' : (commitmentPairOfBalances localParams remoteParams b fee number
        funder).localCommitment.totalOutputValue +
        (commitmentPairOfBalances localParams remoteParams b fee number
          funder).localCommitment.feeSat =
      (commitmentPairOfBalances localParams remoteParams b fee number
        funder).localCommitment.fundingValueSat :=
    (commitmentConserved_iff _).1 hl
  have hr' : (commitmentPairOfBalances localParams remoteParams b fee number
        funder).remoteCommitment.totalOutputValue +
        (commitmentPairOfBalances localParams remoteParams b fee number
          funder).remoteCommitment.feeSat =
      (commitmentPairOfBalances localParams remoteParams b fee number
        funder).remoteCommitment.fundingValueSat :=
    (commitmentConserved_iff _).1 hr
  dsimp only
  exact ⟨CommitmentTypes.Commitment.migrateNet_conservation _ _ hl',
    CommitmentTypes.Commitment.migrateNet_effectiveFee_eq _ _ hl',
    CommitmentTypes.Commitment.migrateNet_conservation _ _ hr',
    CommitmentTypes.Commitment.migrateNet_effectiveFee_eq _ _ hr'⟩

/-- **The `CommitmentTx.ofCommitment` construction lift.**  Any legacy record
that conserves yields the downstream three-term account after being lifted to
the rich transaction and migrated. -/
theorem ofCommitment_migrateNet_conservation (c : Commitment)
    (dustLimitSat : Nat) (toLocalScript toRemoteScript localAnchorScript
      remoteAnchorScript : ScriptPubKey)
    (htlcScript : CommitmentHTLCOutput → ScriptPubKey)
    (hc : CommitmentConserved c) :
    ((CommitmentTx.ofCommitment c dustLimitSat toLocalScript toRemoteScript
        localAnchorScript remoteAnchorScript htlcScript).migrateNet).commitment.totalOutputValue +
        ((CommitmentTx.ofCommitment c dustLimitSat toLocalScript toRemoteScript
          localAnchorScript remoteAnchorScript htlcScript).migrateNet).commitment.feeSat +
        ((CommitmentTx.ofCommitment c dustLimitSat toLocalScript toRemoteScript
          localAnchorScript remoteAnchorScript htlcScript).migrateNet).commitment.trimmedTotalSat =
      c.fundingValueSat := by
  have hbal : c.totalOutputValue + c.feeSat = c.fundingValueSat :=
    (commitmentConserved_iff _).1 hc
  have h := CommitmentTypes.CommitmentTx.migrateNet_conservation
    (CommitmentTx.ofCommitment c dustLimitSat toLocalScript toRemoteScript
      localAnchorScript remoteAnchorScript htlcScript) hbal
  have ht := CommitmentTypes.CommitmentTx.migrateNet_trimmedSat_eq_commitment_trimmedTotalSat
    (CommitmentTx.ofCommitment c dustLimitSat toLocalScript toRemoteScript
      localAnchorScript remoteAnchorScript htlcScript)
  rw [ht] at h
  simpa [CommitmentTx.ofCommitment] using h

/-! ## 6. Retained counterexamples -/

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

/-- The wave-4 trimming counterexample is retained: value accounting does not
imply multiset equality. -/
theorem wave4_dust_trimming_not_perm_retained :
    ¬ (CommitmentIntegration.legacyOutputs
          CommitmentIntegration.dustDemoTx).Perm
        CommitmentIntegration.dustDemoTx.commitment.commitmentOutputs :=
  CommitmentIntegration.dust_trimming_not_perm

end LnLean.Proofs.WaveH.H27
