/-
# Wave 8 lane H28 — legacy coverage is not preserved at the downstream
`commitment_signed` construction site (CH-01, CH-02)

**Issues.**

* `CH-01`: the rich `CommitmentTx` gross/net model is not the path legacy
  consumers read.  Wave 7's `CommitmentConsumerTargets` proves the consumer
  migration theorems and retains
  `legacyCoverage_not_preserved_by_net_migration`, but that counterexample is
  stated on the synthetic `oneHtlcSigMessage` / `dustDemoTx` pair, not on a
  message that an actual `commitment_signed` construction site emits.
* `CH-02`: the second-stage fee/net path changes the number of HTLC outputs, so
  the `commitment_signed` HTLC-signature count must be re-established after
  migration.

**Result of this module.**  This module does not weaken or replace the
existing counterexamples; it retains them and adds the *construction-site*
instance:

1. `siteTx` lifts exactly the signer-side state `st.toCommitment` (the object
   `ProducedFrom`/`commitment_signed_full_covers` constrains in
   `ProtocolWireTargets`) to a rich `CommitmentTx` via
   `CommitmentTx.ofCommitment`, adding only the dust limit and scripts.
   `siteMessage` is exactly the honest downstream wire message
   (`commitmentSignedFullOfState …).toCommitmentSigned`.
2. `siteMessage_covers_legacy`: the honest message always covers the legacy
   HTLC-output list of the state it was built from.
3. `legacyCoverage_not_preserved_at_construction_site`: a concrete honest site
   with one 500-sat HTLC and a 1000-sat dust limit.  The message covers
   `st.toCommitment` (one HTLC output, one signature), but after
   `migrateForConsumer` the HTLC is trimmed and the same message no longer
   covers the migrated consumer list.  This is the exact integration-site
   counterexample.
4. `exists_construction_site_coverage_loss`: the existential form, with the
   record field projection in force (`tx.UsesRecordNet`), so the loss is caused
   by genuine BOLT 3 net trimming and not by a net-projection mismatch.
5. The sufficient premise, in three forms:
   * exact: `MigratesConsumerIdentity tx` (`migratedConsumerOutputs =
     consumerOutputs`) is enough (`siteCoverage_iff_of_consumerIdentity`);
   * normal form: `SiteNormalForm tx` (`UsesRecordNet`, positive dust,
     `Migrated`) is enough (`siteCoverage_iff_of_normalForm`);
   * no-trim: `SiteNoTrim tx` (positive dust and every emitted value at or
     above the dust limit) implies the normal form
     (`siteCoverage_iff_of_noTrim`).
6. `migrated_alone_does_not_preserve_coverage`: `Migrated` stated against a
   *different* net projection than the record field is not enough.  A record
   whose `CommitmentHTLCOutput.netAmountSat` is below dust but whose
   `CommitmentTx.netAmountSat` projection is above dust satisfies `Migrated`
   and still loses coverage, because `Commitment.migrateNet` filters on the
   record field.  This pins `UsesRecordNet` as a necessary conjunct of the
   normal form.
7. `siteNoTrim_nonvacuous`: a surviving 2000-sat HTLC at the same site keeps
   coverage, so the no-trim premise is satisfiable and not a hidden
   contradiction.
8. `wave7_wire_realized_at_site`: wave 7's `oneHtlcSigMessage` / `dustDemoTx`
   pair is not synthetic — the message is definitionally `trimmedSiteMessage`
   and the wave-7 legacy list is definitionally the site's `consumerOutputs`.
   The D12, wave-4, and wave-7 counterexamples are otherwise retained
   unchanged.

**Scope.**  Coverage is the positional BOLT 2 predicate
`m.htlcSignatures.length = htlcOutputCount …`.  No signature is verified and
no sighash is constructed.  The `commitmentPairOfBalances` pair is not a
witness for HTLC-coverage loss: it has no HTLCs by construction, so trimming
only changes its non-HTLC outputs
(`commitmentPairOfBalances_coverage_preserved`).  The failure needs a state
with a real HTLC set, which is exactly the `SignedState` construction site.

-/

import LnLean.Proofs.ProtocolWireTargets
import LnLean.Proofs.Channel.CommitmentConsumerTargets
import LnLean.Proofs.Channel.CommitmentIntegrationTargets
import LnLean.Proofs.WaveD.D12

namespace LnLean.Proofs.WaveH.H28

set_option autoImplicit false

open LnLean
open LnLean.Channel
open LnLean.Protocol
open LnLean.Proofs
open LnLean.Proofs.ProtocolWireTargets
open LnLean.Proofs.Channel
open LnLean.Proofs.ProtocolCoverageTargets

/-! ## 1. The downstream construction site -/

/-- The signer-side commitment state of `ProtocolWireTargets.SignedState`,
lifted to the rich consumer transaction.  The commitment record is exactly
`st.toCommitment`; the lift adds only the owner's dust limit and the scripts. -/
def siteTx (st : SignedState) (dustLimitSat : Nat)
    (toLocalScript toRemoteScript localAnchorScript remoteAnchorScript :
      ScriptPubKey)
    (htlcScript : CommitmentHTLCOutput → ScriptPubKey) : CommitmentTx :=
  CommitmentTx.ofCommitment st.toCommitment dustLimitSat toLocalScript
    toRemoteScript localAnchorScript remoteAnchorScript htlcScript

/-- The same lift with an explicit net projection.  Used only to show that
`Migrated` must be stated against the record field; the default site keeps
`UsesRecordNet`. -/
def siteTxWithNet (st : SignedState) (dustLimitSat : Nat)
    (netAmountSat : CommitmentHTLCOutput → Nat)
    (toLocalScript toRemoteScript localAnchorScript remoteAnchorScript :
      ScriptPubKey)
    (htlcScript : CommitmentHTLCOutput → ScriptPubKey) : CommitmentTx :=
  { siteTx st dustLimitSat toLocalScript toRemoteScript localAnchorScript
      remoteAnchorScript htlcScript with
    netAmountSat := netAmountSat }

/-- The site lift with empty scripts.  Script bytes do not participate in
`commitmentOutputs`, in `htlcOutputCount`, or in either coverage predicate, so
this is the minimal concrete witness. -/
def siteTxSimple (st : SignedState) (dustLimitSat : Nat) : CommitmentTx :=
  siteTx st dustLimitSat ⟨[]⟩ ⟨[]⟩ ⟨[]⟩ ⟨[]⟩ (fun _ => ⟨[]⟩)

/-- The honest downstream `commitment_signed` message for the state: the
legacy projection of the full record produced by
`commitmentSignedFullOfState`. -/
def siteMessage (st : SignedState) (commitSig : EcdsaSig)
    (sigAt : SignedHtlc → EcdsaSig) : CommitmentSigned :=
  (commitmentSignedFullOfState st commitSig sigAt).toCommitmentSigned

theorem siteTx_commitment (st : SignedState) (dustLimitSat : Nat)
    (toLocalScript toRemoteScript localAnchorScript remoteAnchorScript :
      ScriptPubKey)
    (htlcScript : CommitmentHTLCOutput → ScriptPubKey) :
    (siteTx st dustLimitSat toLocalScript toRemoteScript localAnchorScript
      remoteAnchorScript htlcScript).commitment = st.toCommitment := rfl

@[simp] theorem siteTxSimple_commitment (st : SignedState) (dustLimitSat : Nat) :
    (siteTxSimple st dustLimitSat).commitment = st.toCommitment := rfl

@[simp] theorem siteTxSimple_dustLimitSat (st : SignedState)
    (dustLimitSat : Nat) :
    (siteTxSimple st dustLimitSat).dustLimitSat = dustLimitSat := rfl

@[simp] theorem siteTxSimple_netAmountSat (st : SignedState)
    (dustLimitSat : Nat) (h : CommitmentHTLCOutput) :
    (siteTxSimple st dustLimitSat).netAmountSat h = h.netAmountSat := rfl

theorem siteTxSimple_usesRecordNet (st : SignedState) (dustLimitSat : Nat) :
    (siteTxSimple st dustLimitSat).UsesRecordNet :=
  fun _ => rfl

theorem siteMessage_htlcSignatures (st : SignedState) (commitSig : EcdsaSig)
    (sigAt : SignedHtlc → EcdsaSig) :
    (siteMessage st commitSig sigAt).htlcSignatures = st.htlcs.map sigAt := by
  simp [siteMessage, commitmentSignedFullOfState]

/-- The honest message covers the legacy HTLC-output list of the state it was
constructed from.  This is the positive half of the site instance. -/
theorem siteMessage_covers_legacy (st : SignedState) (commitSig : EcdsaSig)
    (sigAt : SignedHtlc → EcdsaSig) :
    ProtocolCoverageTargets.CoversHtlcOutputs
      (siteMessage st commitSig sigAt) st.toCommitment := by
  rw [ProtocolCoverageTargets.coversHtlcOutputs_iff_length,
    siteMessage_htlcSignatures, SignedState.toCommitment_htlcs_length,
    List.length_map]

/-! ## 2. The concrete construction-site counterexample -/

/-- A signer-side state whose only non-anchor output is one offered HTLC of
500 satoshis.  The owner's dust limit at the site is 1000 satoshis, so BOLT 3
trims the HTLC after net migration. -/
def trimmedSiteState : SignedState where
  channelId := ChannelId.zero
  holder := .local
  commitmentNumber := 0
  fundingValueSat := 500
  toLocalSat := 0
  toRemoteSat := 0
  feeSat := 0
  contestDelay := 144
  anchorOutputs := false
  feerate := ⟨0⟩
  commitmentDigest := ByteArray.empty
  htlcs := [{ htlcId := 0
              amount := ⟨500000⟩
              paymentHash := ⟨ByteArray.empty⟩
              direction := .local
              htlcState := .offered
              cltvExpiry := 0
              signedDataDigest := ByteArray.empty }]

/-- The state's whole commitment record, in explicit form. -/
theorem trimmedSiteState_toCommitment_eq :
    trimmedSiteState.toCommitment =
      { holder := .local
        commitmentNumber := 0
        fundingValueSat := 500
        toLocalSat := 0
        toRemoteSat := 0
        htlcs := [{ direction := .local
                    amountSat := 500
                    cltvExpiry := 0
                    state := .offered
                    netAmountSat := 500 }]
        feeSat := 0
        contestDelay := 144
        anchorOutputs := false } := rfl

/-- The state's one HTLC projects to a 500-satoshi commitment output, whose net
value defaults to the same 500 satoshis. -/
theorem trimmedSiteState_toCommitment_htlcs :
    trimmedSiteState.toCommitment.htlcs =
      [{ direction := .local
         amountSat := 500
         cltvExpiry := 0
         state := .offered
         netAmountSat := 500 }] := rfl

/-- The 500-sat HTLC is below the 1000-sat dust limit. -/
@[simp] theorem trimmedSiteHtlc_keepAtDust_false :
    ({ direction := .local
       amountSat := 500
       cltvExpiry := 0
       state := .offered
       netAmountSat := 500 } : CommitmentHTLCOutput).keepAtDust 1000 = false := by
  decide

/-- The legacy consumer list at the site: exactly the one 500-sat HTLC output. -/
theorem trimmedSiteTx_consumerOutputs :
    (siteTxSimple trimmedSiteState 1000).consumerOutputs =
      [CommitmentOutput.htlc .local 500] := by
  rw [CommitmentTx.consumerOutputs_eq]
  simp [siteTxSimple, siteTx, CommitmentTx.ofCommitment_commitment,
    trimmedSiteState_toCommitment_eq, Commitment.commitmentOutputs]

/-- After net migration the HTLC is below the dust limit, so the migrated
consumer list is empty. -/
theorem trimmedSiteTx_migratedConsumerOutputs :
    (siteTxSimple trimmedSiteState 1000).migratedConsumerOutputs = [] := by
  rw [CommitmentTx.migratedConsumerOutputs_eq]
  simp [CommitmentTx.migrateNet, Commitment.migrateNet,
    trimmedSiteState_toCommitment_eq, Commitment.commitmentOutputs,
    CommitmentHTLCOutput.keepAtDust, siteTxSimple_dustLimitSat]

/-- The one-signature honest message used by the concrete witness. -/
def trimmedSiteMessage : CommitmentSigned :=
  siteMessage trimmedSiteState ⟨ByteArray.empty⟩ (fun _ => ⟨ByteArray.empty⟩)

theorem trimmedSiteMessage_htlcSignatures :
    trimmedSiteMessage.htlcSignatures = [⟨ByteArray.empty⟩] := by
  rw [trimmedSiteMessage, siteMessage_htlcSignatures]
  rfl

/-- The exact site counterexample's migrated consumer list is empty. -/
theorem trimmedSiteMessage_length :
    trimmedSiteMessage.htlcSignatures.length = 1 := by
  rw [trimmedSiteMessage_htlcSignatures]
  rfl

/-- **The exact integration-site counterexample.**  The honest
`commitment_signed` message for `trimmedSiteState` covers the legacy HTLC-output
list of `st.toCommitment`, but not the consumer list after
`CommitmentTx.migrateForConsumer`: the 500-sat HTLC is trimmed at the 1000-sat
dust limit, so the wire carries one signature too many. -/
theorem legacyCoverage_not_preserved_at_construction_site :
    ProtocolCoverageTargets.CoversHtlcOutputs trimmedSiteMessage
        (siteTxSimple trimmedSiteState 1000).commitment ∧
      ¬ CommitmentConsumer.CoversMigratedOutputs trimmedSiteMessage
        (siteTxSimple trimmedSiteState 1000) := by
  constructor
  · rw [siteTxSimple_commitment]
    exact siteMessage_covers_legacy _ _ _
  · unfold CommitmentConsumer.CoversMigratedOutputs
    rw [trimmedSiteTx_migratedConsumerOutputs, trimmedSiteMessage_length]
    simp [htlcOutputCount]

/-- Existential form of the same site instance.  `UsesRecordNet` is in force,
so the loss is genuine net trimming, not a net-projection mismatch. -/
theorem exists_construction_site_coverage_loss :
    ∃ (st : SignedState) (m : CommitmentSigned) (tx : CommitmentTx),
      tx.commitment = st.toCommitment ∧
        0 < tx.dustLimitSat ∧
        tx.UsesRecordNet ∧
        ProtocolCoverageTargets.CoversHtlcOutputs m st.toCommitment ∧
        ¬ CommitmentConsumer.CoversMigratedOutputs m tx := by
  refine ⟨trimmedSiteState, trimmedSiteMessage,
    siteTxSimple trimmedSiteState 1000, rfl, by decide,
    siteTxSimple_usesRecordNet _ _, ?_, ?_⟩
  · exact siteMessage_covers_legacy _ _ _
  · exact (legacyCoverage_not_preserved_at_construction_site).2

/-! ## 3. The sufficient premise -/

/-- The exact sufficient condition: net migration leaves the legacy consumer
output list unchanged.  This is the weakest premise used below. -/
def MigratesConsumerIdentity (tx : CommitmentTx) : Prop :=
  tx.migratedConsumerOutputs = tx.consumerOutputs

/-- The checkable BOLT 3 survivor normal form at the site: the record uses its
own net field, the dust limit is positive, and the record is `Migrated`. -/
def SiteNormalForm (tx : CommitmentTx) : Prop :=
  tx.UsesRecordNet ∧ 0 < tx.dustLimitSat ∧ tx.Migrated

/-- The direct no-trim premise: positive dust and every emitted value is at or
above the dust limit, so `Commitment.migrateNet` changes nothing. -/
def SiteNoTrim (tx : CommitmentTx) : Prop :=
  tx.UsesRecordNet ∧
    0 < tx.dustLimitSat ∧
    tx.dustLimitSat ≤ tx.commitment.toLocalSat ∧
    tx.dustLimitSat ≤ tx.commitment.toRemoteSat ∧
    (∀ h ∈ tx.commitment.htlcs, tx.dustLimitSat ≤ h.netAmountSat)

/-- On the consumer list, the coverage predicates agree as soon as migration is
the identity. -/
theorem siteCoverage_iff_of_consumerIdentity (m : CommitmentSigned)
    (tx : CommitmentTx) (h : MigratesConsumerIdentity tx) :
    CommitmentConsumer.CoversMigratedOutputs m tx ↔
      ProtocolCoverageTargets.CoversHtlcOutputs m tx.commitment := by
  unfold MigratesConsumerIdentity at h
  unfold CommitmentConsumer.CoversMigratedOutputs
    ProtocolCoverageTargets.CoversHtlcOutputs
  rw [h, CommitmentTx.consumerOutputs_eq]

/-- `SiteNoTrim` implies the survivor normal form. -/
theorem siteNormalForm_of_noTrim (tx : CommitmentTx) (h : SiteNoTrim tx) :
    SiteNormalForm tx := by
  obtain ⟨hnet, hd, hl, hr, hh⟩ := h
  refine ⟨hnet, hd, ?_⟩
  exact CommitmentConsumer.migrated_of_no_trim tx hd hl hr
    (fun h' hmem => by simpa [hnet h'] using hh h' hmem)

/-- The no-trim premise leaves the legacy consumer list unchanged. -/
theorem consumerIdentity_of_noTrim (tx : CommitmentTx) (h : SiteNoTrim tx) :
    MigratesConsumerIdentity tx := by
  have hnf := siteNormalForm_of_noTrim tx h
  obtain ⟨hnet, hd, _hl, _hr, _hh⟩ := h
  unfold MigratesConsumerIdentity
  exact CommitmentConsumer.migratedConsumerOutputs_eq_consumerOutputs_of_migrated
    tx hnet hnf.2.2 hd

/-- The survivor normal form leaves the legacy consumer list unchanged. -/
theorem consumerIdentity_of_normalForm (tx : CommitmentTx)
    (h : SiteNormalForm tx) : MigratesConsumerIdentity tx := by
  obtain ⟨hnet, hd, hm⟩ := h
  unfold MigratesConsumerIdentity
  exact CommitmentConsumer.migratedConsumerOutputs_eq_consumerOutputs_of_migrated
    tx hnet hm hd

/-- **Sufficient normal-form premise.**  On `SiteNormalForm`, the migrated
coverage predicate is exactly the legacy `commitment_signed` coverage predicate
applied to the construction-site commitment. -/
theorem siteCoverage_iff_of_normalForm (m : CommitmentSigned) (tx : CommitmentTx)
    (h : SiteNormalForm tx) :
    CommitmentConsumer.CoversMigratedOutputs m tx ↔
      ProtocolCoverageTargets.CoversHtlcOutputs m tx.commitment :=
  siteCoverage_iff_of_consumerIdentity m tx (consumerIdentity_of_normalForm tx h)

/-- **Sufficient no-trim premise.**  It is enough that every output is at or
above the dust limit (with the record net projection), i.e. that migration
performs no trimming at all. -/
theorem siteCoverage_iff_of_noTrim (m : CommitmentSigned) (tx : CommitmentTx)
    (h : SiteNoTrim tx) :
    CommitmentConsumer.CoversMigratedOutputs m tx ↔
      ProtocolCoverageTargets.CoversHtlcOutputs m tx.commitment :=
  siteCoverage_iff_of_consumerIdentity m tx (consumerIdentity_of_noTrim tx h)

/-- The concrete witness lies outside the normal form: its HTLC does not
survive the net dust test. -/
theorem trimmedSiteTx_not_migrated :
    ¬ (siteTxSimple trimmedSiteState 1000).Migrated := by
  intro hm
  have hmem : ({ direction := .local
                 amountSat := 500
                 cltvExpiry := 0
                 state := .offered
                 netAmountSat := 500 } : CommitmentHTLCOutput) ∈
      (siteTxSimple trimmedSiteState 1000).commitment.htlcs := by
    rw [siteTxSimple_commitment, trimmedSiteState_toCommitment_eq]
    simp
  have hh := hm.2.2 _ hmem
  simp [siteTxSimple_dustLimitSat, siteTxSimple_netAmountSat] at hh

theorem trimmedSiteTx_not_normalForm :
    ¬ SiteNormalForm (siteTxSimple trimmedSiteState 1000) :=
  fun h => trimmedSiteTx_not_migrated h.2.2

theorem trimmedSiteTx_not_noTrim :
    ¬ SiteNoTrim (siteTxSimple trimmedSiteState 1000) :=
  fun h => trimmedSiteTx_not_migrated (siteNormalForm_of_noTrim _ h).2.2

/-! ## 4. `Migrated` alone is not the normal form: `UsesRecordNet` is needed -/

/-- A state with one 500-sat HTLC, used with an explicit net projection that
claims 2000 satoshis.  The record field still says 500, which is what
`Commitment.migrateNet` filters on.  This is the same state as
`trimmedSiteState`; only the transaction's net projection differs. -/
abbrev mismatchedNetSiteState : SignedState := trimmedSiteState

/-- The mismatched site transaction: the net projection says every HTLC is at
2000 satoshis, but the record field is still 500. -/
def mismatchedNetSiteTx : CommitmentTx :=
  siteTxWithNet mismatchedNetSiteState 1000 (fun _ => 2000)
    ⟨[]⟩ ⟨[]⟩ ⟨[]⟩ ⟨[]⟩ (fun _ => ⟨[]⟩)

@[simp] theorem mismatchedNetSiteTx_dustLimitSat :
    mismatchedNetSiteTx.dustLimitSat = 1000 := rfl

@[simp] theorem mismatchedNetSiteTx_netAmountSat (h : CommitmentHTLCOutput) :
    mismatchedNetSiteTx.netAmountSat h = 2000 := rfl

@[simp] theorem mismatchedNetSiteTx_commitment :
    mismatchedNetSiteTx.commitment = mismatchedNetSiteState.toCommitment := rfl

@[simp] theorem mismatchedNetSiteTx_htlcs :
    mismatchedNetSiteTx.commitment.htlcs =
      [{ direction := .local
         amountSat := 500
         cltvExpiry := 0
         state := .offered
         netAmountSat := 500 }] :=
  trimmedSiteState_toCommitment_htlcs

/-- The record is `Migrated` under the *transaction's* net projection. -/
theorem mismatchedNetSiteTx_migrated : mismatchedNetSiteTx.Migrated := by
  unfold CommitmentTx.Migrated
  refine ⟨?_, ?_, ?_⟩
  · rw [mismatchedNetSiteTx_commitment, trimmedSiteState_toCommitment_eq]
    decide
  · rw [mismatchedNetSiteTx_commitment, trimmedSiteState_toCommitment_eq]
    decide
  · intro h hmem
    rw [mismatchedNetSiteTx_htlcs] at hmem
    simp only [List.mem_singleton] at hmem
    subst hmem
    rw [mismatchedNetSiteTx_dustLimitSat, mismatchedNetSiteTx_netAmountSat]
    decide

/-- But the transaction does *not* use the record net field. -/
theorem mismatchedNetSiteTx_not_usesRecordNet :
    ¬ mismatchedNetSiteTx.UsesRecordNet := by
  intro h
  have hh := h { direction := .local
                 amountSat := 500
                 cltvExpiry := 0
                 state := .offered
                 netAmountSat := 500 }
  simp [mismatchedNetSiteTx, siteTxWithNet] at hh

/-- The same honest message still covers the legacy construction-site list. -/
theorem mismatchedNetSiteMessage_covers_legacy :
    ProtocolCoverageTargets.CoversHtlcOutputs
      (siteMessage mismatchedNetSiteState ⟨ByteArray.empty⟩
        (fun _ => ⟨ByteArray.empty⟩))
      mismatchedNetSiteState.toCommitment :=
  siteMessage_covers_legacy _ _ _

/-- The migrated consumer list is empty: the record-field 500-sat value is
below the dust limit, whatever the transaction projection says. -/
theorem mismatchedNetSiteTx_migratedConsumerOutputs :
    mismatchedNetSiteTx.migratedConsumerOutputs = [] := by
  rw [CommitmentTx.migratedConsumerOutputs_eq]
  simp [CommitmentTx.migrateNet, Commitment.migrateNet,
    mismatchedNetSiteTx_commitment, trimmedSiteState_toCommitment_eq,
    Commitment.commitmentOutputs, CommitmentHTLCOutput.keepAtDust,
    mismatchedNetSiteTx_dustLimitSat]

/-- **`Migrated` needs `UsesRecordNet`.**  A record can satisfy `Migrated`
against one net projection while `migrateNet` filters on the record field and
still trims an output.  Coverage is therefore not preserved by
`Migrated + 0 < dust` alone. -/
theorem migrated_alone_does_not_preserve_coverage :
    ∃ (st : SignedState) (m : CommitmentSigned) (tx : CommitmentTx),
      tx.commitment = st.toCommitment ∧
        tx.Migrated ∧
        0 < tx.dustLimitSat ∧
        ¬ tx.UsesRecordNet ∧
        ProtocolCoverageTargets.CoversHtlcOutputs m st.toCommitment ∧
        ¬ CommitmentConsumer.CoversMigratedOutputs m tx := by
  refine ⟨mismatchedNetSiteState,
    siteMessage mismatchedNetSiteState ⟨ByteArray.empty⟩
      (fun _ => ⟨ByteArray.empty⟩),
    mismatchedNetSiteTx, rfl, mismatchedNetSiteTx_migrated, by decide,
    mismatchedNetSiteTx_not_usesRecordNet, ?_, ?_⟩
  · exact mismatchedNetSiteMessage_covers_legacy
  · unfold CommitmentConsumer.CoversMigratedOutputs
    rw [mismatchedNetSiteTx_migratedConsumerOutputs]
    rw [siteMessage_htlcSignatures]
    simp [mismatchedNetSiteState, trimmedSiteState, htlcOutputCount]

/-! ## 5. Non-vacuity of the no-trim premise -/

/-- A signer-side state whose single HTLC is 2000 satoshis at a 1000-satoshi
dust limit, with both non-HTLC outputs above dust.  Nothing is trimmed. -/
def survivingSiteState : SignedState where
  channelId := ChannelId.zero
  holder := .local
  commitmentNumber := 1
  fundingValueSat := 6000
  toLocalSat := 2000
  toRemoteSat := 2000
  feeSat := 0
  contestDelay := 144
  anchorOutputs := false
  feerate := ⟨0⟩
  commitmentDigest := ByteArray.empty
  htlcs := [{ htlcId := 1
              amount := ⟨2000000⟩
              paymentHash := ⟨ByteArray.empty⟩
              direction := .remote
              htlcState := .received
              cltvExpiry := 100
              signedDataDigest := ByteArray.empty }]

/-- The surviving state's whole commitment record, in explicit form. -/
theorem survivingSiteState_toCommitment_eq :
    survivingSiteState.toCommitment =
      { holder := .local
        commitmentNumber := 1
        fundingValueSat := 6000
        toLocalSat := 2000
        toRemoteSat := 2000
        htlcs := [{ direction := .remote
                    amountSat := 2000
                    cltvExpiry := 100
                    state := .received
                    netAmountSat := 2000 }]
        feeSat := 0
        contestDelay := 144
        anchorOutputs := false } := rfl

theorem survivingSiteTx_commitment :
    (siteTxSimple survivingSiteState 1000).commitment =
      survivingSiteState.toCommitment := rfl

theorem survivingSiteTx_noTrim :
    SiteNoTrim (siteTxSimple survivingSiteState 1000) := by
  refine ⟨siteTxSimple_usesRecordNet _ _, by decide, ?_, ?_, ?_⟩
  · rw [survivingSiteTx_commitment, survivingSiteState_toCommitment_eq]
    decide
  · rw [survivingSiteTx_commitment, survivingSiteState_toCommitment_eq]
    decide
  · intro h hmem
    rw [survivingSiteTx_commitment, survivingSiteState_toCommitment_eq] at hmem
    simp only [List.mem_singleton] at hmem
    subst hmem
    simp

/-- The no-trim site keeps coverage: the honest one-signature message covers
both the legacy and the migrated consumer lists. -/
theorem siteNoTrim_nonvacuous :
    ProtocolCoverageTargets.CoversHtlcOutputs
        (siteMessage survivingSiteState ⟨ByteArray.empty⟩
          (fun _ => ⟨ByteArray.empty⟩))
        (siteTxSimple survivingSiteState 1000).commitment ∧
      CommitmentConsumer.CoversMigratedOutputs
        (siteMessage survivingSiteState ⟨ByteArray.empty⟩
          (fun _ => ⟨ByteArray.empty⟩))
        (siteTxSimple survivingSiteState 1000) := by
  constructor
  · rw [siteTxSimple_commitment]
    exact siteMessage_covers_legacy _ _ _
  · exact (siteCoverage_iff_of_noTrim _ _
      (survivingSiteTx_noTrim)).2
      (siteMessage_covers_legacy _ _ _)

/-! ## 6. Where the failure cannot occur: the `commitmentPairOfBalances` pair -/

/-- A commitment with no HTLCs keeps HTLC coverage under any net migration:
trimming only changes non-HTLC outputs. -/
theorem coversMigratedOutputs_iff_legacy_of_noHtlcs (m : CommitmentSigned)
    (tx : CommitmentTx) (hempty : tx.commitment.htlcs = []) :
    CommitmentConsumer.CoversMigratedOutputs m tx ↔
      ProtocolCoverageTargets.CoversHtlcOutputs m tx.commitment := by
  unfold CommitmentConsumer.CoversMigratedOutputs
    ProtocolCoverageTargets.CoversHtlcOutputs
  rw [CommitmentTx.migratedConsumerOutputs_eq,
    Commitment.htlcOutputCount_commitmentOutputs,
    Commitment.htlcOutputCount_commitmentOutputs,
    CommitmentTx.migrateNet_htlcs, hempty]
  simp

/-- The actual pair constructor `commitmentPairOfBalances` has no HTLCs
(`Commitment.htlcs = []` by construction), so the integration-site HTLC
coverage failure cannot be produced there.  This is why the concrete witness
above uses the richer `SignedState` site. -/
theorem commitmentPairOfBalances_coverage_preserved
    (localParams remoteParams : ChannelParams) (b : Balance) (fee number : Nat)
    (funder : Direction) (dustLimitSat : Nat) (m : CommitmentSigned)
    (toLocalScript toRemoteScript localAnchorScript remoteAnchorScript :
      ScriptPubKey)
    (htlcScript : CommitmentHTLCOutput → ScriptPubKey) :
    ProtocolCoverageTargets.CoversHtlcOutputs m
        (CommitmentTx.ofCommitment
          (commitmentPairOfBalances localParams remoteParams b fee number
            funder).localCommitment
          dustLimitSat toLocalScript toRemoteScript localAnchorScript
          remoteAnchorScript htlcScript).commitment ↔
      CommitmentConsumer.CoversMigratedOutputs m
        (CommitmentTx.ofCommitment
          (commitmentPairOfBalances localParams remoteParams b fee number
            funder).localCommitment
          dustLimitSat toLocalScript toRemoteScript localAnchorScript
          remoteAnchorScript htlcScript) :=
  (coversMigratedOutputs_iff_legacy_of_noHtlcs m _ rfl).symm

/-! ## 7. Existing counterexamples retained unchanged -/

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

/-- Wave 7's consumer-boundary coverage failure is retained unchanged. -/
theorem consumer_legacyCoverage_not_preserved_retained :
    CommitmentConsumer.oneHtlcSigMessage.htlcSignatures.length =
        htlcOutputCount
          CommitmentIntegration.dustDemoTx.commitment.commitmentOutputs ∧
      ¬ CommitmentConsumer.CoversMigratedOutputs
        CommitmentConsumer.oneHtlcSigMessage
        CommitmentIntegration.dustDemoTx :=
  CommitmentConsumer.legacyCoverage_not_preserved_by_net_migration

/-- Wave 4's trimming counterexample is retained unchanged. -/
theorem wave4_dust_trimming_not_perm_retained :
    ¬ (CommitmentIntegration.legacyOutputs
          CommitmentIntegration.dustDemoTx).Perm
        CommitmentIntegration.dustDemoTx.commitment.commitmentOutputs :=
  CommitmentConsumer.wave4_dust_trimming_not_perm_retained

/-- **The wave-7 synthetic wire record is realized by the honest site.**  The
concrete arithmetic is deliberately the same as
`CommitmentConsumer.legacyCoverage_not_preserved_by_net_migration`; what is new
is the provenance: `oneHtlcSigMessage` is exactly the message that
`commitmentSignedFullOfState` emits for `trimmedSiteState`, and the legacy
consumer list is exactly the one wave 7 computed.  The wave-7 counterexample is
therefore not a synthetic artifact: it is the actual downstream site of a
500-sat HTLC under a 1000-sat dust limit. -/
theorem wave7_wire_realized_at_site :
    CommitmentConsumer.oneHtlcSigMessage = trimmedSiteMessage ∧
      CommitmentIntegration.dustDemoTx.commitment.commitmentOutputs =
        (siteTxSimple trimmedSiteState 1000).consumerOutputs := by
  constructor
  · rfl
  · rw [trimmedSiteTx_consumerOutputs]
    exact CommitmentIntegration.dustDemoTx_commitmentOutputs

/-! ## 8. Axiom pins -/

section Pins

/-- info: 'LnLean.Proofs.WaveH.H28.siteMessage_covers_legacy' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms siteMessage_covers_legacy
/-- info: 'LnLean.Proofs.WaveH.H28.legacyCoverage_not_preserved_at_construction_site' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms legacyCoverage_not_preserved_at_construction_site
/-- info: 'LnLean.Proofs.WaveH.H28.exists_construction_site_coverage_loss' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms exists_construction_site_coverage_loss
/-- info: 'LnLean.Proofs.WaveH.H28.siteCoverage_iff_of_normalForm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms siteCoverage_iff_of_normalForm
/-- info: 'LnLean.Proofs.WaveH.H28.siteCoverage_iff_of_noTrim' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms siteCoverage_iff_of_noTrim
/-- info: 'LnLean.Proofs.WaveH.H28.migrated_alone_does_not_preserve_coverage' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms migrated_alone_does_not_preserve_coverage
/-- info: 'LnLean.Proofs.WaveH.H28.siteNoTrim_nonvacuous' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms siteNoTrim_nonvacuous
/-- info: 'LnLean.Proofs.WaveH.H28.trimmedSiteTx_not_migrated' depends on axioms: [propext] -/
#guard_msgs in #print axioms trimmedSiteTx_not_migrated
/-- info: 'LnLean.Proofs.WaveH.H28.wave7_wire_realized_at_site' depends on axioms: [propext] -/
#guard_msgs in #print axioms wave7_wire_realized_at_site
/-- info: 'LnLean.Proofs.WaveH.H28.commitmentPairOfBalances_coverage_preserved' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms commitmentPairOfBalances_coverage_preserved

end Pins

end LnLean.Proofs.WaveH.H28
