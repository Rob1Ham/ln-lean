import LnLean.Proofs.Channel.CommitmentConsumerTargets
import LnLean.Proofs.Channel.SighashTargets
import LnLean.Proofs.Channel.SighashViewBindingTargets

/-!
# Actual commitment-consumer sites (CH-01, S8-CH-CONSUMER-SITES)

`CommitmentConsumerTargets` proves the migration at the abstract consumer
boundary: a consumer reading `CommitmentTx.consumerOutputs` can switch to
`migrateForConsumer`/`netConsumerOutputs` without changing the `CommitmentOutput`
type or the coverage count.  This module connects that boundary to the
**actual** construction and consumer sites in the tree.

## The audited sites

A repository-wide search for `CommitmentTx`, `consumerOutputs`,
`migrateForConsumer`, `netConsumerOutputs`, and `viewOfState` finds:

* **Construction:** production modules contain **no** `CommitmentTx`
  constructor.  The core module `LnLean/Channel/Commitment.lean` defines the
  structure and the only production lift, `CommitmentTx.ofCommitment`.  The
  two other literals are proof-layer demos (`CommitmentIntegration.dustDemoTx`
  and `CommitmentTx.migratedFrom`).  The signed-state construction site is
  `LnLean.Proofs.ProtocolWireTargets.SignedState.toCommitment`; it produces a
  `Commitment`, not a `CommitmentTx`.
* **Sighash consumer:** `LnLean.Proofs.Channel.SighashTargets.viewOfState`
  reads `st.toCommitment.commitmentOutputs` into
  `CommitmentSighashView.outputs` (`viewOfState_outputs`).  This is the list the
  commitment preimage serializes.
* **Coverage consumer:** `LnLean.Proofs.ProtocolCoverageTargets.CoversHtlcOutputs`
  reads `c.commitmentOutputs`, and
  `LnLean.Proofs.ProtocolWireTargets.commitment_signed_full_covers` applies it
  to `st.toCommitment` for an honestly produced `CommitmentSignedFull`.

There is no external/production `CommitmentTx` consumer to edit.  The adapter
below therefore lives at the boundary of those two real proof-layer consumers:
it lifts a `SignedState` to a `CommitmentTx` (`SignedState.toCommitmentTx`)
with the caller's dust limit and scripts, and proves that the migrated lists
are what the existing consumers read.

## Results

* `SignedState.toCommitmentTx`: the construction-site adapter
  (`CommitmentTx.ofCommitment st.toCommitment ...`).  Its commitment projection
  is definitionally `st.toCommitment`, and its net projection uses the record
  field, so `UsesRecordNet` holds definitionally.
* `migratedConsumerOutputs_eq_viewOfState_outputs`: on the survivor normal form,
  the legacy-shaped migrated list is **exactly** `(viewOfState ctx st).outputs`.
  This is the strongest statement at the `List CommitmentOutput` boundary.
* `viewOfState_outputs_perm_netConsumerOutputs`: the sorted rich net list is a
  permutation of the same sighash output list.  Equality is impossible in
  general: the legacy list is not value-sorted (D12).
* `coversHtlcOutputs_iff_coversMigratedOutputs`: the actual
  `CoversHtlcOutputs` predicate on `st.toCommitment` is exactly
  `CoversMigratedOutputs` on the constructed transaction.
* `commitment_signed_full_covers_migrated`: the honest `commitment_signed`
  production theorem delivers `CoversMigratedOutputs` at the migrated site,
  end to end, from `ProducedFrom` plus the two BOLT 3 value equations.
* `siteExample_migrated`/`siteExample_perm`: a concrete non-vacuous
  instantiation of the no-trim form.
* `legacyCoverage_not_preserved_at_site`: the wave-7 consumer-boundary
  counterexample is re-exported unchanged.  D12 and wave-4 trimming are still
  available from `CommitmentConsumerTargets`; nothing is weakened.

## Boundaries

* The normal-form hypotheses `Migrated` and (for the abstract theorem)
  `UsesRecordNet` remain explicit.  For the adapter transaction
  `UsesRecordNet` is definitional; `Migrated` is the genuine BOLT 3
  survivor/no-trim premise.  `legacyCoverage_not_preserved_at_site` shows it
  cannot be dropped.
* The refinement at the sorted boundary is `List.Perm`, not equality.  Nothing
  here claims that the sighash *digest* is invariant under reordering; D12 is
  the refutation of that reading.
* Script execution, signatures, witnesses, and consensus validity remain out
  of scope.  `SignedState.toCommitmentTx` supplies the caller's scripts
  explicitly; it does not invent them.
-/

namespace LnLean.Proofs.Channel.CommitmentConsumerSites

set_option autoImplicit false

open LnLean
open LnLean.Channel
open LnLean.Protocol
open LnLean.Crypto
open LnLean.Proofs
open LnLean.Proofs.ProtocolWireTargets
open LnLean.Proofs.ProtocolCoverageTargets
open LnLean.Proofs.Channel.CommitmentConsumer
open LnLean.Proofs.Channel.SighashTargets
open LnLean.Proofs.Channel.SighashViewBindingTargets

/-! ## 1. The construction-site adapter -/

/-- Lift the signed-state construction site to the rich `CommitmentTx` model at
a caller-supplied dust limit and script set.  This is the compiled adapter the
consumer path was missing: `st.toCommitment` is the record the existing
consumers already read, and `ofCommitment` keeps it definitionally. -/
def _root_.LnLean.Proofs.ProtocolWireTargets.SignedState.toCommitmentTx
    (st : SignedState) (dustLimitSat : Nat)
    (toLocalScript toRemoteScript localAnchorScript remoteAnchorScript :
      ScriptPubKey)
    (htlcScript : CommitmentHTLCOutput → ScriptPubKey) : CommitmentTx :=
  CommitmentTx.ofCommitment st.toCommitment dustLimitSat toLocalScript
    toRemoteScript localAnchorScript remoteAnchorScript htlcScript

@[simp] theorem signedStateToCommitmentTx_commitment (st : SignedState)
    (dustLimitSat : Nat)
    (toLocalScript toRemoteScript localAnchorScript remoteAnchorScript :
      ScriptPubKey)
    (htlcScript : CommitmentHTLCOutput → ScriptPubKey) :
    (st.toCommitmentTx dustLimitSat toLocalScript toRemoteScript
        localAnchorScript remoteAnchorScript htlcScript).commitment =
      st.toCommitment := rfl

@[simp] theorem signedStateToCommitmentTx_dustLimitSat (st : SignedState)
    (dustLimitSat : Nat)
    (toLocalScript toRemoteScript localAnchorScript remoteAnchorScript :
      ScriptPubKey)
    (htlcScript : CommitmentHTLCOutput → ScriptPubKey) :
    (st.toCommitmentTx dustLimitSat toLocalScript toRemoteScript
        localAnchorScript remoteAnchorScript htlcScript).dustLimitSat =
      dustLimitSat := rfl

/-- The adapter uses the record net projection, so the abstract migration
theorem's compatibility hypothesis is definitional at the real site. -/
theorem signedStateToCommitmentTx_usesRecordNet (st : SignedState)
    (dustLimitSat : Nat)
    (toLocalScript toRemoteScript localAnchorScript remoteAnchorScript :
      ScriptPubKey)
    (htlcScript : CommitmentHTLCOutput → ScriptPubKey) :
    (st.toCommitmentTx dustLimitSat toLocalScript toRemoteScript
        localAnchorScript remoteAnchorScript htlcScript).UsesRecordNet :=
  fun _ => rfl

/-- The legacy consumer list of the adapter is the state's commitment output
list, unchanged. -/
@[simp] theorem signedStateToCommitmentTx_consumerOutputs (st : SignedState)
    (dustLimitSat : Nat)
    (toLocalScript toRemoteScript localAnchorScript remoteAnchorScript :
      ScriptPubKey)
    (htlcScript : CommitmentHTLCOutput → ScriptPubKey) :
    (st.toCommitmentTx dustLimitSat toLocalScript toRemoteScript
        localAnchorScript remoteAnchorScript htlcScript).consumerOutputs =
      st.toCommitment.commitmentOutputs := rfl

/-! ## 2. Normal-form transfer to the constructed transaction -/

/-- The explicit no-trim conditions on the state make the constructed
transaction `Migrated`.  This is the premise the site adapter inherits from the
abstract migration API, not a new assumption. -/
theorem signedStateToCommitmentTx_migrated_of_no_trim (st : SignedState)
    (dustLimitSat : Nat)
    (toLocalScript toRemoteScript localAnchorScript remoteAnchorScript :
      ScriptPubKey)
    (htlcScript : CommitmentHTLCOutput → ScriptPubKey)
    (hdust : 0 < dustLimitSat)
    (hl : dustLimitSat ≤ st.toCommitment.toLocalSat)
    (hr : dustLimitSat ≤ st.toCommitment.toRemoteSat)
    (hh : ∀ h ∈ st.toCommitment.htlcs,
      dustLimitSat ≤ h.netAmountSat) :
    (st.toCommitmentTx dustLimitSat toLocalScript toRemoteScript
        localAnchorScript remoteAnchorScript htlcScript).Migrated := by
  apply migrated_of_no_trim
  · exact hdust
  · exact hl
  · exact hr
  · exact hh

/-! ## 3. The sighash consumer (`viewOfState`) -/

/-- **Exact equality at the consumer's `List CommitmentOutput` boundary.**  On
the BOLT 3 survivor normal form, the legacy-shaped migrated list of the
constructed transaction is exactly the output list `viewOfState` reads.  This
is stronger than the permutation form and is the strongest statement available
at this type. -/
theorem migratedConsumerOutputs_eq_viewOfState_outputs
    (ctx : SighashContext) (st : SignedState) (dustLimitSat : Nat)
    (toLocalScript toRemoteScript localAnchorScript remoteAnchorScript :
      ScriptPubKey)
    (htlcScript : CommitmentHTLCOutput → ScriptPubKey)
    (hm : (st.toCommitmentTx dustLimitSat toLocalScript toRemoteScript
        localAnchorScript remoteAnchorScript htlcScript).Migrated)
    (hdust : 0 < dustLimitSat) :
    (st.toCommitmentTx dustLimitSat toLocalScript toRemoteScript
        localAnchorScript remoteAnchorScript htlcScript).migratedConsumerOutputs =
      (viewOfState ctx st).outputs := by
  rw [migratedConsumerOutputs_eq_consumerOutputs_of_migrated _
    (signedStateToCommitmentTx_usesRecordNet st dustLimitSat toLocalScript
      toRemoteScript localAnchorScript remoteAnchorScript htlcScript) hm hdust,
    consumerOutputs_eq_commitmentOutputs, viewOfState_outputs,
    signedStateToCommitmentTx_commitment]

/-- The no-trim corollary of the exact sighash-consumer equality. -/
theorem migratedConsumerOutputs_eq_viewOfState_outputs_of_no_trim
    (ctx : SighashContext) (st : SignedState) (dustLimitSat : Nat)
    (toLocalScript toRemoteScript localAnchorScript remoteAnchorScript :
      ScriptPubKey)
    (htlcScript : CommitmentHTLCOutput → ScriptPubKey)
    (hdust : 0 < dustLimitSat)
    (hl : dustLimitSat ≤ st.toCommitment.toLocalSat)
    (hr : dustLimitSat ≤ st.toCommitment.toRemoteSat)
    (hh : ∀ h ∈ st.toCommitment.htlcs,
      dustLimitSat ≤ h.netAmountSat) :
    (st.toCommitmentTx dustLimitSat toLocalScript toRemoteScript
        localAnchorScript remoteAnchorScript htlcScript).migratedConsumerOutputs =
      (viewOfState ctx st).outputs :=
  migratedConsumerOutputs_eq_viewOfState_outputs ctx st dustLimitSat
    toLocalScript toRemoteScript localAnchorScript remoteAnchorScript htlcScript
    (signedStateToCommitmentTx_migrated_of_no_trim st dustLimitSat
      toLocalScript toRemoteScript localAnchorScript remoteAnchorScript
      htlcScript hdust hl hr hh) hdust

/-- **The sorted rich net list is the list the sighash consumer reads**, up to
the BOLT 3 sort.  This is `netConsumerOutputs_perm_migratedConsumerOutputs`
instantiated at the actual `viewOfState` site. -/
theorem viewOfState_outputs_perm_netConsumerOutputs
    (ctx : SighashContext) (st : SignedState) (dustLimitSat : Nat)
    (toLocalScript toRemoteScript localAnchorScript remoteAnchorScript :
      ScriptPubKey)
    (htlcScript : CommitmentHTLCOutput → ScriptPubKey)
    (hm : (st.toCommitmentTx dustLimitSat toLocalScript toRemoteScript
        localAnchorScript remoteAnchorScript htlcScript).Migrated)
    (hdust : 0 < dustLimitSat) :
    ((st.toCommitmentTx dustLimitSat toLocalScript toRemoteScript
        localAnchorScript remoteAnchorScript htlcScript).netConsumerOutputs.map
        CommitmentTxOutput.toCommitmentOutput).Perm
      (viewOfState ctx st).outputs := by
  have hperm := netConsumerOutputs_perm_consumerOutputs_of_migrated
    (st.toCommitmentTx dustLimitSat toLocalScript toRemoteScript
      localAnchorScript remoteAnchorScript htlcScript)
    (signedStateToCommitmentTx_usesRecordNet st dustLimitSat toLocalScript
      toRemoteScript localAnchorScript remoteAnchorScript htlcScript) hm hdust
  rw [signedStateToCommitmentTx_consumerOutputs, ← viewOfState_outputs] at hperm
  exact hperm

/-- The no-trim corollary of the sighash-consumer permutation. -/
theorem viewOfState_outputs_perm_netConsumerOutputs_of_no_trim
    (ctx : SighashContext) (st : SignedState) (dustLimitSat : Nat)
    (toLocalScript toRemoteScript localAnchorScript remoteAnchorScript :
      ScriptPubKey)
    (htlcScript : CommitmentHTLCOutput → ScriptPubKey)
    (hdust : 0 < dustLimitSat)
    (hl : dustLimitSat ≤ st.toCommitment.toLocalSat)
    (hr : dustLimitSat ≤ st.toCommitment.toRemoteSat)
    (hh : ∀ h ∈ st.toCommitment.htlcs,
      dustLimitSat ≤ h.netAmountSat) :
    ((st.toCommitmentTx dustLimitSat toLocalScript toRemoteScript
        localAnchorScript remoteAnchorScript htlcScript).netConsumerOutputs.map
        CommitmentTxOutput.toCommitmentOutput).Perm
      (viewOfState ctx st).outputs :=
  viewOfState_outputs_perm_netConsumerOutputs ctx st dustLimitSat
    toLocalScript toRemoteScript localAnchorScript remoteAnchorScript htlcScript
    (signedStateToCommitmentTx_migrated_of_no_trim st dustLimitSat
      toLocalScript toRemoteScript localAnchorScript remoteAnchorScript
      htlcScript hdust hl hr hh) hdust

/-- The count the sighash consumer serializes is the migrated net count. -/
theorem viewOfState_outputs_length_eq_netConsumerOutputs
    (ctx : SighashContext) (st : SignedState) (dustLimitSat : Nat)
    (toLocalScript toRemoteScript localAnchorScript remoteAnchorScript :
      ScriptPubKey)
    (htlcScript : CommitmentHTLCOutput → ScriptPubKey)
    (hm : (st.toCommitmentTx dustLimitSat toLocalScript toRemoteScript
        localAnchorScript remoteAnchorScript htlcScript).Migrated)
    (hdust : 0 < dustLimitSat) :
    (viewOfState ctx st).outputs.length =
      (st.toCommitmentTx dustLimitSat toLocalScript toRemoteScript
        localAnchorScript remoteAnchorScript htlcScript).netConsumerOutputs.length := by
  have h := viewOfState_outputs_perm_netConsumerOutputs ctx st dustLimitSat
    toLocalScript toRemoteScript localAnchorScript remoteAnchorScript
    htlcScript hm hdust
  simpa using h.length_eq.symm

/-- **Signature-bound consumer preservation.**  The view-binding theorem
`signature_binds_commitment_view_fields` says a verifying commitment signature
forces the alternative state's output list to equal the honest state's.  At
the migrated consumer boundary this means both states read exactly the same
legacy-shaped net list.  This is the signature-verifying counterpart of the
`viewOfState` adapter above; it keeps all cryptographic hypotheses explicit
(`EufCma`, `ViewDigestCollisionFree`) and does not claim reordering-invariant
digests. -/
theorem signature_binds_migratedConsumerOutputs
    {M : PrimitiveModel} (hC3 : EufCma M.ecdsaVerify)
    {law : CommitmentSigningLaw M}
    {ctx : SighashContext} {st : SignedState} {f : CommitmentSignedFull}
    (h : SighashProduces M law ctx st f)
    {views : List CommitmentSighashView}
    (hbind : ViewDigestCollisionFree M views)
    (hv : viewOfState ctx st ∈ views)
    {ctx' : SighashContext} {st' : SignedState}
    (hv' : viewOfState ctx' st' ∈ views)
    (hver : M.ecdsaVerify ctx.commitmentKey
      (commitmentTag ++ commitmentDigest M (viewOfState ctx' st'))
      f.commitmentSignature = true)
    (dustLimitSat : Nat)
    (toLocalScript toRemoteScript localAnchorScript remoteAnchorScript :
      ScriptPubKey)
    (htlcScript : CommitmentHTLCOutput → ScriptPubKey)
    (hm : (st.toCommitmentTx dustLimitSat toLocalScript toRemoteScript
        localAnchorScript remoteAnchorScript htlcScript).Migrated)
    (hm' : (st'.toCommitmentTx dustLimitSat toLocalScript toRemoteScript
        localAnchorScript remoteAnchorScript htlcScript).Migrated)
    (hdust : 0 < dustLimitSat) :
    (st'.toCommitmentTx dustLimitSat toLocalScript toRemoteScript
        localAnchorScript remoteAnchorScript htlcScript).migratedConsumerOutputs =
      (st.toCommitmentTx dustLimitSat toLocalScript toRemoteScript
        localAnchorScript remoteAnchorScript htlcScript).migratedConsumerOutputs := by
  have hout := (SighashViewBindingTargets.signature_binds_commitment_view_fields
    hC3 h hbind hv hv' hver).1
  rw [migratedConsumerOutputs_eq_viewOfState_outputs ctx' st' dustLimitSat
    toLocalScript toRemoteScript localAnchorScript remoteAnchorScript htlcScript
    hm' hdust,
    migratedConsumerOutputs_eq_viewOfState_outputs ctx st dustLimitSat
    toLocalScript toRemoteScript localAnchorScript remoteAnchorScript htlcScript
    hm hdust]
  simpa using hout

/-! ## 4. The `commitment_signed` coverage consumer -/

/-- The actual coverage predicate on the state's commitment is exactly the
migrated coverage predicate on the constructed transaction. -/
theorem coversHtlcOutputs_iff_coversMigratedOutputs
    (m : CommitmentSigned) (st : SignedState) (dustLimitSat : Nat)
    (toLocalScript toRemoteScript localAnchorScript remoteAnchorScript :
      ScriptPubKey)
    (htlcScript : CommitmentHTLCOutput → ScriptPubKey)
    (hm : (st.toCommitmentTx dustLimitSat toLocalScript toRemoteScript
        localAnchorScript remoteAnchorScript htlcScript).Migrated)
    (hdust : 0 < dustLimitSat) :
    CoversHtlcOutputs m st.toCommitment ↔
      CoversMigratedOutputs m
        (st.toCommitmentTx dustLimitSat toLocalScript toRemoteScript
          localAnchorScript remoteAnchorScript htlcScript) := by
  rw [coversMigratedOutputs_iff_legacy_of_migrated m _
    (signedStateToCommitmentTx_usesRecordNet st dustLimitSat toLocalScript
      toRemoteScript localAnchorScript remoteAnchorScript htlcScript) hm hdust,
    signedStateToCommitmentTx_commitment]
  rfl

/-- The migrated coverage predicate on the constructed transaction is exactly
one signature per state HTLC. -/
theorem coversMigratedOutputs_iff_stateHtlcs
    (m : CommitmentSigned) (st : SignedState) (dustLimitSat : Nat)
    (toLocalScript toRemoteScript localAnchorScript remoteAnchorScript :
      ScriptPubKey)
    (htlcScript : CommitmentHTLCOutput → ScriptPubKey)
    (hm : (st.toCommitmentTx dustLimitSat toLocalScript toRemoteScript
        localAnchorScript remoteAnchorScript htlcScript).Migrated)
    (hdust : 0 < dustLimitSat) :
    CoversMigratedOutputs m
        (st.toCommitmentTx dustLimitSat toLocalScript toRemoteScript
          localAnchorScript remoteAnchorScript htlcScript) ↔
      m.htlcSignatures.length = st.toCommitment.htlcs.length := by
  rw [← coversHtlcOutputs_iff_coversMigratedOutputs m st dustLimitSat
    toLocalScript toRemoteScript localAnchorScript remoteAnchorScript
    htlcScript hm hdust]
  unfold CoversHtlcOutputs
  rw [Commitment.htlcOutputCount_commitmentOutputs]

/-- **End to end at the actual production theorem.**  From `ProducedFrom` and
the two BOLT 3 value equations, the honestly produced full `commitment_signed`
record covers the migrated consumer output list of the constructed
transaction.  This is `commitment_signed_full_covers` composed with the site
adapter, not a restatement of the abstract migration lemma. -/
theorem commitment_signed_full_covers_migrated
    (f : CommitmentSignedFull) (st : SignedState)
    (sigAt : SignedHtlc → EcdsaSig)
    (hprod : ProducedFrom f st sigAt)
    (hcons : CommitmentConserved st.toCommitment)
    (hres : FeeIsFundingResidual st.feerate st.toCommitment)
    (dustLimitSat : Nat)
    (toLocalScript toRemoteScript localAnchorScript remoteAnchorScript :
      ScriptPubKey)
    (htlcScript : CommitmentHTLCOutput → ScriptPubKey)
    (hm : (st.toCommitmentTx dustLimitSat toLocalScript toRemoteScript
        localAnchorScript remoteAnchorScript htlcScript).Migrated)
    (hdust : 0 < dustLimitSat) :
    CoversMigratedOutputs f.toCommitmentSigned
      (st.toCommitmentTx dustLimitSat toLocalScript toRemoteScript
        localAnchorScript remoteAnchorScript htlcScript) := by
  have h := commitment_signed_full_covers f st sigAt hprod hcons hres
  exact (coversHtlcOutputs_iff_coversMigratedOutputs f.toCommitmentSigned st
    dustLimitSat toLocalScript toRemoteScript localAnchorScript
    remoteAnchorScript htlcScript hm hdust).mp h.2.2.1

/-! ## 5. Non-vacuity at the site -/

/-- A concrete state in the survivor normal form at the BOLT 2 dust limit 354:
both balance outputs are well above dust and the single HTLC has a net value of
354 sat. -/
def siteExampleState : SignedState where
  channelId := ChannelId.zero
  holder := .local
  commitmentNumber := 0
  fundingValueSat := 20897
  toLocalSat := 10000
  toRemoteSat := 10000
  feeSat := 543
  contestDelay := 144
  anchorOutputs := false
  feerate := ⟨1000⟩
  commitmentDigest := ByteArray.empty
  htlcs := [{ htlcId := 1
              amount := ⟨354000⟩
              paymentHash := ⟨ByteArray.empty⟩
              direction := .local
              htlcState := .offered
              cltvExpiry := 100
              signedDataDigest := ByteArray.empty }]

/-- A concrete sighash context for the site example. -/
def siteExampleContext : SighashContext where
  fundingTxid := ByteArray.empty
  fundingOutputIndex := 0
  fundingScript := ByteArray.empty
  obscuredCommitmentNumber := 0
  secondStageFeeSat := 0
  commitmentKey := ⟨ByteArray.empty⟩

/-- The empty script used by the concrete adapter instantiation. -/
def siteExampleScript : ScriptPubKey := ⟨[]⟩

theorem siteExample_migrated :
    (siteExampleState.toCommitmentTx 354 siteExampleScript siteExampleScript
      siteExampleScript siteExampleScript (fun _ => siteExampleScript)).Migrated := by
  unfold CommitmentTx.Migrated
  decide

/-- The exact legacy-shaped equality is instantiated on the concrete state. -/
theorem siteExample_migratedConsumerOutputs_eq_view :
    (siteExampleState.toCommitmentTx 354 siteExampleScript siteExampleScript
        siteExampleScript siteExampleScript (fun _ => siteExampleScript)).migratedConsumerOutputs =
      (viewOfState siteExampleContext siteExampleState).outputs :=
  migratedConsumerOutputs_eq_viewOfState_outputs siteExampleContext
    siteExampleState 354 siteExampleScript siteExampleScript siteExampleScript
    siteExampleScript (fun _ => siteExampleScript) siteExample_migrated (by decide)

/-- The sorted net-list permutation is instantiated on the concrete state. -/
theorem siteExample_view_perm :
    ((siteExampleState.toCommitmentTx 354 siteExampleScript siteExampleScript
        siteExampleScript siteExampleScript (fun _ => siteExampleScript)).netConsumerOutputs.map
        CommitmentTxOutput.toCommitmentOutput).Perm
      (viewOfState siteExampleContext siteExampleState).outputs :=
  viewOfState_outputs_perm_netConsumerOutputs siteExampleContext
    siteExampleState 354 siteExampleScript siteExampleScript siteExampleScript
    siteExampleScript (fun _ => siteExampleScript) siteExample_migrated (by decide)

/-! ## 6. Preserved counterexamples -/

/-- The wave-7 consumer-boundary counterexample is retained unchanged: a
one-signature message covers the nominal 500-sat demo commitment but not its
net migration at dust 1000.  The normal-form premise in the site adapter above
cannot be dropped. -/
theorem legacyCoverage_not_preserved_at_site :
    CommitmentConsumer.oneHtlcSigMessage.htlcSignatures.length =
        htlcOutputCount
          CommitmentIntegration.dustDemoTx.commitment.commitmentOutputs ∧
      ¬ CoversMigratedOutputs CommitmentConsumer.oneHtlcSigMessage
        CommitmentIntegration.dustDemoTx :=
  legacyCoverage_not_preserved_by_net_migration

end LnLean.Proofs.Channel.CommitmentConsumerSites
