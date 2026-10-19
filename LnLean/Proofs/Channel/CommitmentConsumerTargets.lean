import LnLean.Channel.Commitment
import LnLean.Proofs.Channel.CommitmentTypesTargets
import LnLean.Protocol.Messages
import LnLean.Proofs.Channel.CommitmentTxProps

/-!
# Legacy commitment-consumer migration (CH-01)

Open issue `CH-01` records that the rich `CommitmentTx` gross/net model is not
the path that legacy consumers actually read.  Wave 5/6 proved the canonical
refinement at the *record* and *transaction* boundaries
(`CommitmentTx.migratedFrom_outputsNet_perm_commitmentOutputs`,
`CommitmentTypes.CommitmentTx.migrateNet_outputsNet_perm_commitmentOutputs`),
but the consumers still read `Commitment.commitmentOutputs` through their own
construction sites.

This module closes the consumer-boundary step:

* `CommitmentTx.consumerOutputs` is the legacy output list a consumer reads;
  `CommitmentTx.migrateForConsumer` (definitionally `migrateNet`) is the
  drop-in net replacement; `CommitmentTx.migratedConsumerOutputs` is the
  legacy-shaped list after migration and `CommitmentTx.netConsumerOutputs` is
  the sorted rich net list.  These live in the owned core module
  `LnLean/Channel/Commitment.lean`, together with the construction-site lift
  `CommitmentTx.ofCommitment`.
* `netConsumerOutputs_perm_migratedConsumerOutputs`: on a protocol-valid
  positive dust limit, the sorted rich net list is a permutation of the
  migrated legacy consumer list.  This is the canonical refinement at the
  consumer's `List CommitmentOutput` boundary.
* `migratedConsumerOutputs_eq_consumerOutputs_of_migrated`: when the consumer
  record is already in the BOLT 3 survivor normal form (`Migrated` and using
  the record net projection), the migrated consumer list is exactly the
  original legacy list.  The `commitment_signed` coverage consumer therefore
  reads exactly the same output list after migration.
* `CoversMigratedOutputs` is the `commitment_signed` coverage predicate applied
  at the migrated consumer boundary.  Its formula is exactly the legacy
  `ProtocolCoverageTargets.CoversHtlcOutputs m c := m.htlcSignatures.length =
  htlcOutputCount c.commitmentOutputs`; the legacy formula is restated as
  `coversMigratedOutputs_iff_legacy` so the proof does not depend on the
  wave-E imports that currently pull the `Handshake` module.
  `coversMigratedOutputs_iff_survivingHtlcs` proves the count is exactly the
  number of net-surviving HTLCs, and
  `coversMigratedOutputs_iff_legacy_of_migrated` proves the legacy predicate
  is unchanged on the normal form.
* `legacyCoverage_not_preserved_by_net_migration`: trimming really changes the
  consumer list, so the normal-form premise is not removable.  This is the
  consumer-boundary counterpart of D12 and wave-4 `dust_trimming_not_perm`;
  both are restated unchanged.
* `CommitmentPair.migrateNet` and its projections provide the pair-level
  construction-site migration used by `commitmentPairOfBalances`.

## Sighash consumer

The sighash consumer `LnLean.Proofs.Channel.SighashTargets.viewOfState` reads
`st.toCommitment.commitmentOutputs` (`viewOfState_outputs`).  The same boundary
theorem applies to it once that module is imported:

```lean
theorem viewOfState_outputs_refines_netConsumerOutputs
    (ctx : SighashTargets.SighashContext)
    (st : SignedState) (tx : CommitmentTx)
    (hst : st.toCommitment = tx.commitment)
    (hnet : tx.UsesRecordNet) (hm : tx.Migrated)
    (hdust : 0 < tx.dustLimitSat) :
    (tx.netConsumerOutputs.map CommitmentTxOutput.toCommitmentOutput).Perm
      (SighashTargets.viewOfState ctx st).outputs
```

The proof is `viewOfState_outputs`, `← hst`,
`netConsumerOutputs_perm_migratedConsumerOutputs`, and
`migratedConsumerOutputs_eq_consumerOutputs_of_migrated`.  It is recorded as an
integration step rather than imported here because wave 7 lane
`S7-PR-PREIMAGE` is editing `SighashTargets.lean` and its current import
closure (`WaveE.E20` → `Protocol.Handshake`) is temporarily unbuildable.  The
theorem is purely additive; no edit to `SighashTargets.lean` is required.

## Scope

* Script execution, signatures, witnesses, sighash bytes, and consensus
  validity are out of scope.  The coverage theorem is about the output list
  the consumer reads; it does not claim a digest is preserved under a different
  order (D12 refutes that reading).
* `CommitmentHTLCOutput.netAmountSat` is caller-supplied.  The BOLT 3 relation
  `net + second_stage_fee = gross` remains the explicit
  `NetConsistentOnRecords` hypothesis from `CommitmentTypesTargets`.
* The refinement is a `List.Perm`, not list equality, because the rich model
  sorts and the legacy consumer list does not (D12).
* Only the required lane modules are built; no full-tree build is claimed.

## Naming decision

The stored record field remains `Commitment.trimmedTotalSat`.
`Commitment.trimmedSat` is the established computed trim function consumed by
the wave-5 module `CommitmentGrossNetTargets`, and `Commitment.trimmedValueFor`
is the computed alias.  Renaming the field would require coordinated edits in
`LnLean/Channel/Types.lean` and the unowned wave-5 module, so this lane keeps
the unambiguous stored/computed pair.  The exact rename patch, if a future
catalog decision requires it, is recorded in the lane report.
-/

namespace LnLean.Proofs.Channel.CommitmentConsumer

set_option autoImplicit false

open LnLean
open LnLean.Channel
open LnLean.Protocol

/-! ## 1. Consumer-boundary definitions and permutations -/

theorem consumerOutputs_eq_commitmentOutputs (tx : CommitmentTx) :
    tx.consumerOutputs = tx.commitment.commitmentOutputs := rfl

theorem migratedConsumerOutputs_eq (tx : CommitmentTx) :
    tx.migratedConsumerOutputs =
      (tx.migrateNet).commitment.commitmentOutputs := rfl

theorem netConsumerOutputs_eq (tx : CommitmentTx) :
    tx.netConsumerOutputs = (tx.migrateNet).outputsNet := rfl

/-- The sorted rich net list refines the migrated legacy consumer list at a
protocol-valid positive dust limit. -/
theorem netConsumerOutputs_perm_migratedConsumerOutputs (tx : CommitmentTx)
    (hdust : 0 < tx.dustLimitSat) :
    (tx.netConsumerOutputs.map CommitmentTxOutput.toCommitmentOutput).Perm
      tx.migratedConsumerOutputs := by
  rw [netConsumerOutputs_eq, migratedConsumerOutputs_eq]
  exact CommitmentTypes.CommitmentTx.migrateNet_outputsNet_perm_commitmentOutputs
    tx hdust

/-- The migrated consumer list is exactly the rich canonical trimmed list. -/
theorem migratedConsumerOutputs_eq_canonicalOutputs (tx : CommitmentTx)
    (hdust : 0 < tx.dustLimitSat) :
    tx.migratedConsumerOutputs = (tx.migrateNet).canonicalOutputs := by
  rw [migratedConsumerOutputs_eq]
  exact (CommitmentTypes.CommitmentTx.migrateNet_canonicalOutputs_eq_commitmentOutputs
    tx hdust).symm

/-- The construction-site lift agrees with the legacy record projection. -/
theorem ofCommitment_consumerOutputs (c : Commitment) (dustLimitSat : Nat)
    (toLocalScript toRemoteScript localAnchorScript remoteAnchorScript :
      ScriptPubKey) (htlcScript : CommitmentHTLCOutput → ScriptPubKey) :
    (CommitmentTx.ofCommitment c dustLimitSat toLocalScript toRemoteScript
        localAnchorScript remoteAnchorScript htlcScript).consumerOutputs =
      c.commitmentOutputs := rfl

/-! ## 2. The normal form: migration preserves an already-migrated consumer -/

/-- A `Bool`-filter identity: if every element of a list satisfies `p`, the
filter is the original list. -/
theorem filter_eq_self_of_forall {α : Type} {p : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, p x = true) → l.filter p = l
  | [], _ => rfl
  | h :: t, hl => by
      have hh : p h = true := hl h (by simp)
      have ht : ∀ x ∈ t, p x = true := fun x hx => hl x (by simp [hx])
      simp [hh, filter_eq_self_of_forall ht]

/-- The value form of the migration on a non-HTLC output in the normal form:
below-dust values are already zero and surviving values are unchanged. -/
theorem if_dust_eq_self {d v : Nat} (_hd : 0 < d) (h : v = 0 ↔ v < d) :
    (if d ≤ v then v else 0) = v := by
  by_cases h0 : v = 0
  · have hlt : v < d := h.mp h0
    simp [h0]
  · have hge : d ≤ v := by
      by_cases hlt : v < d
      · exact absurd (h.mpr hlt) h0
      · omega
    simp [hge]

/-- On a record already in the BOLT 3 survivor normal form, the net migration
does not change the legacy consumer output list.  The record must use its own
`netAmountSat` field: the migration filters on the record field, while
`Migrated` is stated with the transaction projection. -/
theorem migratedConsumerOutputs_eq_consumerOutputs_of_migrated
    (tx : CommitmentTx) (hnet : tx.UsesRecordNet) (hm : tx.Migrated)
    (hdust : 0 < tx.dustLimitSat) :
    tx.migratedConsumerOutputs = tx.consumerOutputs := by
  obtain ⟨hl, hr, hh⟩ := hm
  have hL : (tx.migrateNet).commitment.toLocalSat =
      tx.commitment.toLocalSat := by
    unfold CommitmentTx.migrateNet Commitment.migrateNet
    dsimp only
    exact if_dust_eq_self hdust hl
  have hR : (tx.migrateNet).commitment.toRemoteSat =
      tx.commitment.toRemoteSat := by
    unfold CommitmentTx.migrateNet Commitment.migrateNet
    dsimp only
    exact if_dust_eq_self hdust hr
  have hH : (tx.migrateNet).commitment.htlcs = tx.commitment.htlcs := by
    unfold CommitmentTx.migrateNet Commitment.migrateNet
    dsimp only
    rw [filter_eq_self_of_forall]
    intro h hmem
    have hs : tx.dustLimitSat ≤ h.netAmountSat := by
      have h' := hh h hmem
      rwa [hnet h] at h'
    exact (CommitmentHTLCOutput.keepAtDust_eq_true_iff).2 hs
  have hA : (tx.migrateNet).commitment.anchorOutputs =
      tx.commitment.anchorOutputs := rfl
  rw [migratedConsumerOutputs_eq, consumerOutputs_eq_commitmentOutputs]
  unfold Commitment.commitmentOutputs
  rw [hL, hR, hH, hA]

/-- A consumer record satisfying the explicit no-trim conditions is in the
BOLT 3 survivor normal form. -/
theorem migrated_of_no_trim (tx : CommitmentTx) (hdust : 0 < tx.dustLimitSat)
    (hl : tx.dustLimitSat ≤ tx.commitment.toLocalSat)
    (hr : tx.dustLimitSat ≤ tx.commitment.toRemoteSat)
    (hh : ∀ h ∈ tx.commitment.htlcs,
      tx.dustLimitSat ≤ tx.netAmountSat h) :
    tx.Migrated := by
  unfold CommitmentTx.Migrated
  constructor
  · constructor
    · intro h0; omega
    · intro hlt; omega
  · constructor
    · constructor
      · intro h0; omega
      · intro hlt; omega
    · exact hh

/-- **The consumer path in one step.**  On the BOLT 3 survivor normal form the
sorted rich net list is a permutation of the *same* `consumerOutputs` list a
legacy consumer reads.  This is the legacy-shaped form of
`netConsumerOutputs_perm_migratedConsumerOutputs` with the migrated consumer
list identified with the original one. -/
theorem netConsumerOutputs_perm_consumerOutputs_of_migrated
    (tx : CommitmentTx) (hnet : tx.UsesRecordNet) (hm : tx.Migrated)
    (hdust : 0 < tx.dustLimitSat) :
    (tx.netConsumerOutputs.map CommitmentTxOutput.toCommitmentOutput).Perm
      tx.consumerOutputs := by
  have h := netConsumerOutputs_perm_migratedConsumerOutputs tx hdust
  rwa [migratedConsumerOutputs_eq_consumerOutputs_of_migrated tx hnet hm hdust]
    at h

/-- The no-trim corollary of the consumer-path permutation. -/
theorem netConsumerOutputs_perm_consumerOutputs_of_no_trim
    (tx : CommitmentTx) (hnet : tx.UsesRecordNet)
    (hdust : 0 < tx.dustLimitSat)
    (hl : tx.dustLimitSat ≤ tx.commitment.toLocalSat)
    (hr : tx.dustLimitSat ≤ tx.commitment.toRemoteSat)
    (hh : ∀ h ∈ tx.commitment.htlcs,
      tx.dustLimitSat ≤ tx.netAmountSat h) :
    (tx.netConsumerOutputs.map CommitmentTxOutput.toCommitmentOutput).Perm
      tx.consumerOutputs :=
  netConsumerOutputs_perm_consumerOutputs_of_migrated tx hnet
    (migrated_of_no_trim tx hdust hl hr hh) hdust

/-- The count a coverage consumer reads is preserved on the normal form. -/
theorem netConsumerOutputs_length_eq_consumerOutputs_of_migrated
    (tx : CommitmentTx) (hnet : tx.UsesRecordNet) (hm : tx.Migrated)
    (hdust : 0 < tx.dustLimitSat) :
    tx.netConsumerOutputs.length = tx.consumerOutputs.length := by
  have h := netConsumerOutputs_perm_consumerOutputs_of_migrated tx hnet hm hdust
  simpa using h.length_eq

/-! ## 3. The `commitment_signed` coverage consumer -/

/-- Coverage of a migrated commitment transaction: the wire carries one HTLC
signature per surviving HTLC output of the net-migrated consumer list.  The
legacy predicate is `m.htlcSignatures.length = htlcOutputCount
c.commitmentOutputs` (`LnLean.Proofs.ProtocolCoverageTargets.CoversHtlcOutputs`);
this is the same predicate at the consumer boundary, without importing the
wave-E module closure. -/
def CoversMigratedOutputs (m : CommitmentSigned) (tx : CommitmentTx) : Prop :=
  m.htlcSignatures.length = htlcOutputCount tx.migratedConsumerOutputs

/-- The migrated coverage predicate is exactly the legacy formula applied to
the migrated commitment record. -/
theorem coversMigratedOutputs_iff_legacyRecord (m : CommitmentSigned)
    (tx : CommitmentTx) :
    CoversMigratedOutputs m tx ↔
      m.htlcSignatures.length =
        htlcOutputCount (tx.migrateForConsumer).commitment.commitmentOutputs := by
  unfold CoversMigratedOutputs
  rw [migratedConsumerOutputs_eq, CommitmentTx.migrateForConsumer_eq_migrateNet]

/-- The migrated coverage count is exactly the number of net-surviving HTLCs. -/
theorem coversMigratedOutputs_iff_survivingHtlcs (m : CommitmentSigned)
    (tx : CommitmentTx) :
    CoversMigratedOutputs m tx ↔
      m.htlcSignatures.length =
        (tx.commitment.htlcs.filter
          (fun h => h.keepAtDust tx.dustLimitSat)).length := by
  unfold CoversMigratedOutputs
  rw [migratedConsumerOutputs_eq, Commitment.htlcOutputCount_commitmentOutputs,
    CommitmentTx.migrateNet_htlcs]

/-- On an already-migrated record the legacy coverage formula is unchanged:
the consumer does not need a new predicate, only the migrated record. -/
theorem coversMigratedOutputs_iff_legacy_of_migrated (m : CommitmentSigned)
    (tx : CommitmentTx) (hnet : tx.UsesRecordNet) (hm : tx.Migrated)
    (hdust : 0 < tx.dustLimitSat) :
    CoversMigratedOutputs m tx ↔
      m.htlcSignatures.length =
        htlcOutputCount tx.commitment.commitmentOutputs := by
  unfold CoversMigratedOutputs
  rw [migratedConsumerOutputs_eq_consumerOutputs_of_migrated tx hnet hm hdust,
    consumerOutputs_eq_commitmentOutputs]

/-- The no-trim corollary of the coverage equivalence. -/
theorem coversMigratedOutputs_iff_legacy_of_no_trim (m : CommitmentSigned)
    (tx : CommitmentTx) (hnet : tx.UsesRecordNet)
    (hdust : 0 < tx.dustLimitSat)
    (hl : tx.dustLimitSat ≤ tx.commitment.toLocalSat)
    (hr : tx.dustLimitSat ≤ tx.commitment.toRemoteSat)
    (hh : ∀ h ∈ tx.commitment.htlcs,
      tx.dustLimitSat ≤ tx.netAmountSat h) :
    CoversMigratedOutputs m tx ↔
      m.htlcSignatures.length =
        htlcOutputCount tx.commitment.commitmentOutputs :=
  coversMigratedOutputs_iff_legacy_of_migrated m tx hnet
    (migrated_of_no_trim tx hdust hl hr hh) hdust

/-- One-signature wire record used to show that trimming changes coverage. -/
def oneHtlcSigMessage : CommitmentSigned where
  channelId := ChannelId.zero
  signature := ⟨ByteArray.empty⟩
  htlcSignatures := [⟨ByteArray.empty⟩]

/-- **The normal-form premise is necessary.**  A message that covers the
nominal one-HTLC demo commitment (gross 500 sat, dust 1000) no longer covers
the net-migrated record: the HTLC is trimmed, so the commitment transaction
has no HTLC output at all.  This is the consumer-boundary form of D12 and
wave-4 `dust_trimming_not_perm`; both remain unchanged below. -/
theorem legacyCoverage_not_preserved_by_net_migration :
    oneHtlcSigMessage.htlcSignatures.length =
        htlcOutputCount
          CommitmentIntegration.dustDemoTx.commitment.commitmentOutputs ∧
      ¬ CoversMigratedOutputs oneHtlcSigMessage
        CommitmentIntegration.dustDemoTx := by
  constructor
  · rw [Commitment.htlcOutputCount_commitmentOutputs]
    simp [oneHtlcSigMessage, CommitmentIntegration.dustDemoTx]
  · unfold CoversMigratedOutputs
    decide

/-! ## 4. Pair-level construction-site migration -/

theorem CommitmentPair.migrateNet_htlcs (p : CommitmentPair)
    (dustLimitSat : Nat) :
    (p.migrateNet dustLimitSat).localCommitment.htlcs =
        p.localCommitment.htlcs.filter
          (fun h => h.keepAtDust dustLimitSat) ∧
      (p.migrateNet dustLimitSat).remoteCommitment.htlcs =
        p.remoteCommitment.htlcs.filter
          (fun h => h.keepAtDust dustLimitSat) :=
  ⟨rfl, rfl⟩

/-- The owned pair constructor has no HTLCs, so pair migration only applies
the non-HTLC dust rule. -/
theorem commitmentPairOfBalances_migrateNet_htlcs (localParams remoteParams
    : ChannelParams) (b : Balance) (fee number : Nat)
    (funder : Direction) (dustLimitSat : Nat) :
    ((commitmentPairOfBalances localParams remoteParams b fee number
        funder).migrateNet dustLimitSat).localCommitment.htlcs = [] ∧
      ((commitmentPairOfBalances localParams remoteParams b fee number
        funder).migrateNet dustLimitSat).remoteCommitment.htlcs = [] :=
  ⟨rfl, rfl⟩

/-! ## 5. Preserved counterexamples -/

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

/-- The wave-4 trimming counterexample is retained unchanged. -/
theorem wave4_dust_trimming_not_perm_retained :
    ¬ (CommitmentIntegration.legacyOutputs
          CommitmentIntegration.dustDemoTx).Perm
        CommitmentIntegration.dustDemoTx.commitment.commitmentOutputs :=
  CommitmentIntegration.dust_trimming_not_perm

/-- The wave-6 record-boundary refinement is retained unchanged. -/
theorem wave6_migrateNet_refinement_retained (tx : CommitmentTx)
    (hdust : 0 < tx.dustLimitSat) :
    ((tx.migrateNet).outputsNet.map
        CommitmentTxOutput.toCommitmentOutput).Perm
      (tx.migrateNet).commitment.commitmentOutputs :=
  CommitmentTypes.CommitmentTx.migrateNet_outputsNet_perm_commitmentOutputs
    tx hdust

end LnLean.Proofs.Channel.CommitmentConsumer
