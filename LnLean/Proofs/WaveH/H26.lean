/-
# H26 — migrated consumer path at the `CommitmentParams` boundary (CH-01, CH-02)

**Catalog issues.**  `CH-01` (closed at the consumer path) records that the rich
`CommitmentTx` gross/net model is not the path legacy consumers read, and
`CH-02` records the second-stage fee/dust integration.  Wave 7 closed the
record/transaction consumer boundary in
`LnLean/Proofs/Channel/CommitmentConsumerTargets.lean`: the migrated consumer
list `CommitmentTx.migratedConsumerOutputs` equals the legacy consumer list
`CommitmentTx.consumerOutputs` on the BOLT 3 survivor normal form
(`Migrated` + `UsesRecordNet` + a positive dust limit).

**What this module adds.**  The downstream script construction site
`LnLean.Bitcoin.CommitmentParams.commitmentOutputs`
(`LnLean/Bitcoin/ScriptTemplates.lean`) builds a `List
LnLean.Bitcoin.CommitmentOutput` (kind, signed `BtcAmount`, `scriptPubKey`), a
different type from the value-only legacy `List Channel.CommitmentOutput` read
by the consumer.  The migrated consumer path is therefore not reachable at that
boundary without an explicit projection.  This module supplies it:

* `commitmentOutputToLegacy` projects one script-level output onto the legacy
  value-only consumer type.  It is total on the four implemented kinds
  (`toLocal`, `toRemote`, `localAnchor`, `remoteAnchor`); the `offeredHtlc`,
  `receivedHtlc`, and `mutualClose` kinds are outside the zero-HTLC
  `CommitmentParams` boundary and map to `none`.  A negative signed `BtcAmount`
  also maps to `none`, because the legacy consumer type carries a `Nat`; this
  is exactly the `0 ≤ toLocalValue`/`0 ≤ toRemoteValue` obligation recorded by
  wave-E `E45`.
* `paramsConsumerOutputs` is the legacy-shaped consumer list of a
  `CommitmentParams`.
* `paramsToCommitment` lifts the parameters to the channel `Commitment` record
  (zero HTLCs, both anchors, the parameters' values and CSV delay).  The
  caller supplies the fields the script parameters do not carry (`holder`,
  counters, funding value, fee).
* `paramsTx` wraps that record with `CommitmentTx.ofCommitment`.
* `paramsToCommitment_commitmentOutputs` and `paramsTx_consumerOutputs` state
  that the legacy output list read through the script-level parameters is
  exactly `paramsConsumerOutputs`.
* **Main result:** `paramsTx_migratedConsumerOutputs_eq` and
  `paramsTx_migrated_eq_legacy_consumerOutputs` apply the wave-7 migration at
  this downstream boundary: under the documented normal form
  (`0 < dustLimitSat`, `dustLimitSat ≤ toLocalValue`, `dustLimitSat ≤
  toRemoteValue`, nonnegative signed values) the migrated consumer list equals
  both the legacy consumer list and the `CommitmentParams` consumer list.
  `paramsTx_migrateForConsumer_consumerOutputs` records the drop-in consumer
  switch to `migrateForConsumer`.
* `paramsTx_netConsumerOutputs_perm_paramsConsumerOutputs` carries the sorted
  rich net list (`netConsumerOutputs`) to the same boundary as a permutation.
* `paramsConsumerOutputs_values_eq` shows the projected values are the
  script-level `BtcAmount` values coerced to `Nat`, so the projection does not
  silently change any satoshi amount.
* **Counterexamples kept.**  `belowDust_migration_changes_params_boundary`
  shows the positive-dust/no-trim premise is necessary: a below-dust
  `to_local` is trimmed by the migration, so the migrated list no longer has
  the script-level output.  `negative_toLocal_projection_drops` and
  `negative_value_not_represented` keep wave-E `E45`'s nonnegativity boundary.
  `zero_toLocal_params_not_legacy` shows the legacy function omits a
  zero-valued `to_local` while the script-level list always emits it, so the
  zero-value edge needs the same normal form.

**Scope.**  This is a value-only list equality at the consumer boundary.  It
does not claim script bytes, witness data, sighash digests, signature
coverage, or consensus validity are preserved; the legacy consumer type has no
script field.  `CommitmentParams.commitmentOutputs` is the zero-HTLC template
list, so HTLC outputs (and the second-stage fee on them) are outside this
theorem; the HTLC field boundary remains
`CommitmentHTLCOutput.netAmountSat` with the explicit `NetConsistentOnRecords`
hypothesis from `CommitmentTypesTargets`.  Keys and witness-script hashes are
not constrained here; `CommitmentParams.HashesMatch` remains the missing crypto
bridge.  No full-tree build is claimed.

**BOLT sections.**  BOLT 3 §2 `Commitment Transaction` (`to_local`,
`to_remote`, anchors), §3 trimming (`dust_limit_satoshis` and the second-stage
fee basis).

**Anchors.**  `LnLean/Bitcoin/ScriptTemplates.lean`
(`CommitmentParams`, `commitmentOutputs`, `anchorValue`),
`LnLean/Channel/Commitment.lean` (`Commitment.commitmentOutputs`,
`CommitmentTx.consumerOutputs`, `migrateForConsumer`,
`migratedConsumerOutputs`), and
`LnLean/Proofs/Channel/CommitmentConsumerTargets.lean`
(`migratedConsumerOutputs_eq_consumerOutputs_of_migrated`,
`netConsumerOutputs_perm_migratedConsumerOutputs`).

**Build.**  Module-only target `lake build LnLean.Proofs.WaveH.H26`.  The root
import is left to the integrator (`LnLean.lean` is outside this lane).
-/

import LnLean.Proofs.Channel.CommitmentConsumerTargets
import LnLean.Bitcoin.ScriptTemplates

namespace LnLean.Proofs.WaveH.H26

set_option autoImplicit false

open LnLean
open LnLean.Channel

/-! ## 1. Legacy projection of the script-level output list -/

/-- Project one script-level (`LnLean.Bitcoin`) commitment output onto the
legacy value-only consumer type.  The zero-HTLC `CommitmentParams` boundary
only emits the four implemented kinds; `offeredHtlc`, `receivedHtlc`, and
`mutualClose` are outside it and map to `none` rather than inventing a legacy
value.  A negative signed `BtcAmount` maps to `none`: the legacy
`CommitmentOutput` stores a `Nat`, and wave-E `E45` records the matching
nonnegativity obligation. -/
def commitmentOutputToLegacy (o : LnLean.Bitcoin.CommitmentOutput) :
    Option CommitmentOutput :=
  match o.kind with
  | .toLocal =>
      if 0 ≤ o.value then some (CommitmentOutput.toLocal o.value.toNat) else none
  | .toRemote =>
      if 0 ≤ o.value then some (CommitmentOutput.toRemote o.value.toNat) else none
  | .localAnchor => some CommitmentOutput.localAnchor
  | .remoteAnchor => some CommitmentOutput.remoteAnchor
  | .offeredHtlc => none
  | .receivedHtlc => none
  | .mutualClose => none

/-- The legacy-shaped consumer list of the script-level `CommitmentParams`
construction.  This is the list a pre-CH-01 consumer can read after the
parameters are lifted to a `CommitmentTx`. -/
def paramsConsumerOutputs (p : LnLean.Bitcoin.CommitmentParams) :
    List CommitmentOutput :=
  (LnLean.Bitcoin.commitmentOutputs p).filterMap commitmentOutputToLegacy

/-- The projection of the four-output `CommitmentParams` list, spelled out.
The two signed values must be nonnegative for the projection to keep them. -/
theorem paramsConsumerOutputs_eq (p : LnLean.Bitcoin.CommitmentParams)
    (hl : 0 ≤ p.toLocalValue) (hr : 0 ≤ p.toRemoteValue) :
    paramsConsumerOutputs p =
      [CommitmentOutput.toLocal p.toLocalValue.toNat,
       CommitmentOutput.toRemote p.toRemoteValue.toNat,
       CommitmentOutput.localAnchor, CommitmentOutput.remoteAnchor] := by
  simp [paramsConsumerOutputs, commitmentOutputToLegacy,
    LnLean.Bitcoin.commitmentOutputs, hl, hr]

/-- The script-level construction always emits four outputs at this boundary. -/
theorem paramsConsumerOutputs_length (p : LnLean.Bitcoin.CommitmentParams)
    (hl : 0 ≤ p.toLocalValue) (hr : 0 ≤ p.toRemoteValue) :
    (paramsConsumerOutputs p).length = 4 := by
  rw [paramsConsumerOutputs_eq p hl hr]
  rfl

/-- The projected consumer values are exactly the script-level `BtcAmount`
values (coerced to `Nat`), so the projection preserves every satoshi amount
under the nonnegativity normal form.  The two anchors are the BOLT 3 330-sat
outputs on both sides. -/
theorem paramsConsumerOutputs_values_eq (p : LnLean.Bitcoin.CommitmentParams)
    (hl : 0 ≤ p.toLocalValue) (hr : 0 ≤ p.toRemoteValue) :
    ((paramsConsumerOutputs p).map CommitmentOutput.value).map
        (fun n : Nat => Int.ofNat n) =
      (LnLean.Bitcoin.commitmentOutputs p).map
        LnLean.Bitcoin.CommitmentOutput.value := by
  rw [paramsConsumerOutputs_eq p hl hr]
  simp [LnLean.Bitcoin.commitmentOutputs, CommitmentOutput.value,
    anchorOutputSat, LnLean.Bitcoin.anchorValue, Int.toNat_of_nonneg hl,
    Int.toNat_of_nonneg hr]

/-! ## 2. Lifting the parameters to the channel commitment record -/

/-- Lift the script-level `CommitmentParams` to the channel `Commitment`
record at the zero-HTLC boundary: no HTLCs, both anchors, and the parameters'
two values and CSV delay.  The caller supplies the fields the script
parameters do not carry: broadcasting direction, commitment number, funding
value, and fee. -/
def paramsToCommitment (p : LnLean.Bitcoin.CommitmentParams)
    (holder : Direction) (commitmentNumber fundingValueSat feeSat : Nat) :
    Commitment :=
  { holder := holder
    commitmentNumber := commitmentNumber
    fundingValueSat := fundingValueSat
    toLocalSat := p.toLocalValue.toNat
    toRemoteSat := p.toRemoteValue.toNat
    htlcs := []
    feeSat := feeSat
    contestDelay := p.toSelfDelay
    anchorOutputs := true
    trimmedTotalSat := 0 }

@[simp] theorem paramsToCommitment_toLocalSat
    (p : LnLean.Bitcoin.CommitmentParams) (holder : Direction)
    (commitmentNumber fundingValueSat feeSat : Nat) :
    (paramsToCommitment p holder commitmentNumber fundingValueSat feeSat).toLocalSat =
      p.toLocalValue.toNat := rfl

@[simp] theorem paramsToCommitment_toRemoteSat
    (p : LnLean.Bitcoin.CommitmentParams) (holder : Direction)
    (commitmentNumber fundingValueSat feeSat : Nat) :
    (paramsToCommitment p holder commitmentNumber fundingValueSat feeSat).toRemoteSat =
      p.toRemoteValue.toNat := rfl

@[simp] theorem paramsToCommitment_htlcs
    (p : LnLean.Bitcoin.CommitmentParams) (holder : Direction)
    (commitmentNumber fundingValueSat feeSat : Nat) :
    (paramsToCommitment p holder commitmentNumber fundingValueSat feeSat).htlcs = [] :=
  rfl

@[simp] theorem paramsToCommitment_anchorOutputs
    (p : LnLean.Bitcoin.CommitmentParams) (holder : Direction)
    (commitmentNumber fundingValueSat feeSat : Nat) :
    (paramsToCommitment p holder commitmentNumber fundingValueSat feeSat).anchorOutputs =
      true := rfl

@[simp] theorem paramsToCommitment_contestDelay
    (p : LnLean.Bitcoin.CommitmentParams) (holder : Direction)
    (commitmentNumber fundingValueSat feeSat : Nat) :
    (paramsToCommitment p holder commitmentNumber fundingValueSat feeSat).contestDelay =
      p.toSelfDelay := rfl

/-- The legacy output list of the lifted record is exactly the legacy-shaped
projection of the script-level `CommitmentParams` list, provided the two
signed values are nonnegative and non-zero.  The non-zero condition is the
legacy `commitmentOutputs` convention: a zero `to_local`/`to_remote` output is
not emitted, while `CommitmentParams.commitmentOutputs` always contains it. -/
theorem paramsToCommitment_commitmentOutputs
    (p : LnLean.Bitcoin.CommitmentParams) (holder : Direction)
    (commitmentNumber fundingValueSat feeSat : Nat)
    (hl : 0 ≤ p.toLocalValue) (hr : 0 ≤ p.toRemoteValue)
    (hl0 : p.toLocalValue.toNat ≠ 0) (hr0 : p.toRemoteValue.toNat ≠ 0) :
    (paramsToCommitment p holder commitmentNumber fundingValueSat feeSat).commitmentOutputs =
      paramsConsumerOutputs p := by
  rw [paramsConsumerOutputs_eq p hl hr]
  simp [Commitment.commitmentOutputs, paramsToCommitment, hl0, hr0]

/-! ## 3. The transaction-level construction site -/

/-- The downstream construction site: a `CommitmentTx` whose commitment record
is lifted from `CommitmentParams` and whose scripts are supplied by the caller
(they are not part of the value-only consumer list). -/
def paramsTx (p : LnLean.Bitcoin.CommitmentParams) (holder : Direction)
    (commitmentNumber fundingValueSat feeSat dustLimitSat : Nat)
    (toLocalScript toRemoteScript localAnchorScript remoteAnchorScript :
      ScriptPubKey) (htlcScript : CommitmentHTLCOutput → ScriptPubKey) :
    CommitmentTx :=
  CommitmentTx.ofCommitment
    (paramsToCommitment p holder commitmentNumber fundingValueSat feeSat)
    dustLimitSat toLocalScript toRemoteScript localAnchorScript
    remoteAnchorScript htlcScript

/-- The legacy consumer list read through the script-level construction site. -/
theorem paramsTx_consumerOutputs (p : LnLean.Bitcoin.CommitmentParams)
    (holder : Direction) (commitmentNumber fundingValueSat feeSat dustLimitSat :
      Nat) (toLocalScript toRemoteScript localAnchorScript remoteAnchorScript :
      ScriptPubKey) (htlcScript : CommitmentHTLCOutput → ScriptPubKey)
    (hl : 0 ≤ p.toLocalValue) (hr : 0 ≤ p.toRemoteValue)
    (hl0 : p.toLocalValue.toNat ≠ 0) (hr0 : p.toRemoteValue.toNat ≠ 0) :
    (paramsTx p holder commitmentNumber fundingValueSat feeSat dustLimitSat
        toLocalScript toRemoteScript localAnchorScript remoteAnchorScript
        htlcScript).consumerOutputs = paramsConsumerOutputs p := by
  simp only [paramsTx, CommitmentTx.consumerOutputs,
    CommitmentTx.ofCommitment_commitment]
  exact paramsToCommitment_commitmentOutputs p holder commitmentNumber
    fundingValueSat feeSat hl hr hl0 hr0

/-- **Main result.**  Apply the wave-7 net migration at the downstream
`CommitmentParams`/`commitmentOutputs` boundary: on the documented normal form
(positive dust limit, both commitment values at or above it, nonnegative signed
values) the migrated consumer list is exactly the legacy-shaped projection of
the script-level output list. -/
theorem paramsTx_migratedConsumerOutputs_eq
    (p : LnLean.Bitcoin.CommitmentParams) (holder : Direction)
    (commitmentNumber fundingValueSat feeSat dustLimitSat : Nat)
    (toLocalScript toRemoteScript localAnchorScript remoteAnchorScript :
      ScriptPubKey) (htlcScript : CommitmentHTLCOutput → ScriptPubKey)
    (hdust : 0 < dustLimitSat)
    (hl : 0 ≤ p.toLocalValue) (hr : 0 ≤ p.toRemoteValue)
    (hld : dustLimitSat ≤ p.toLocalValue.toNat)
    (hrd : dustLimitSat ≤ p.toRemoteValue.toNat) :
    (paramsTx p holder commitmentNumber fundingValueSat feeSat dustLimitSat
        toLocalScript toRemoteScript localAnchorScript remoteAnchorScript
        htlcScript).migratedConsumerOutputs = paramsConsumerOutputs p := by
  have hnet : (paramsTx p holder commitmentNumber fundingValueSat feeSat
      dustLimitSat toLocalScript toRemoteScript localAnchorScript
      remoteAnchorScript htlcScript).UsesRecordNet := fun _ => rfl
  have hm : (paramsTx p holder commitmentNumber fundingValueSat feeSat
      dustLimitSat toLocalScript toRemoteScript localAnchorScript
      remoteAnchorScript htlcScript).Migrated := by
    refine LnLean.Proofs.Channel.CommitmentConsumer.migrated_of_no_trim
      (paramsTx p holder commitmentNumber fundingValueSat feeSat dustLimitSat
        toLocalScript toRemoteScript localAnchorScript remoteAnchorScript
        htlcScript) hdust ?_ ?_ ?_
    · simpa [paramsTx, CommitmentTx.ofCommitment, paramsToCommitment] using hld
    · simpa [paramsTx, CommitmentTx.ofCommitment, paramsToCommitment] using hrd
    · intro h hmem
      simp [paramsTx, CommitmentTx.ofCommitment, paramsToCommitment] at hmem
  have h := LnLean.Proofs.Channel.CommitmentConsumer.migratedConsumerOutputs_eq_consumerOutputs_of_migrated
    (paramsTx p holder commitmentNumber fundingValueSat feeSat dustLimitSat
      toLocalScript toRemoteScript localAnchorScript remoteAnchorScript
      htlcScript) hnet hm hdust
  rw [h]
  exact paramsTx_consumerOutputs p holder commitmentNumber fundingValueSat feeSat
    dustLimitSat toLocalScript toRemoteScript localAnchorScript remoteAnchorScript
    htlcScript hl hr (by omega) (by omega)

/-- **The requested equality.**  The migrated output list equals the legacy
consumer list at the downstream `CommitmentParams` construction site under the
documented normal form. -/
theorem paramsTx_migrated_eq_legacy_consumerOutputs
    (p : LnLean.Bitcoin.CommitmentParams) (holder : Direction)
    (commitmentNumber fundingValueSat feeSat dustLimitSat : Nat)
    (toLocalScript toRemoteScript localAnchorScript remoteAnchorScript :
      ScriptPubKey) (htlcScript : CommitmentHTLCOutput → ScriptPubKey)
    (hdust : 0 < dustLimitSat)
    (hl : 0 ≤ p.toLocalValue) (hr : 0 ≤ p.toRemoteValue)
    (hld : dustLimitSat ≤ p.toLocalValue.toNat)
    (hrd : dustLimitSat ≤ p.toRemoteValue.toNat) :
    (paramsTx p holder commitmentNumber fundingValueSat feeSat dustLimitSat
        toLocalScript toRemoteScript localAnchorScript remoteAnchorScript
        htlcScript).migratedConsumerOutputs =
      (paramsTx p holder commitmentNumber fundingValueSat feeSat dustLimitSat
        toLocalScript toRemoteScript localAnchorScript remoteAnchorScript
        htlcScript).consumerOutputs := by
  rw [paramsTx_migratedConsumerOutputs_eq p holder commitmentNumber
      fundingValueSat feeSat dustLimitSat toLocalScript toRemoteScript
      localAnchorScript remoteAnchorScript htlcScript hdust hl hr hld hrd]
  exact (paramsTx_consumerOutputs p holder commitmentNumber fundingValueSat
    feeSat dustLimitSat toLocalScript toRemoteScript localAnchorScript
    remoteAnchorScript htlcScript hl hr (by omega) (by omega)).symm

/-- The drop-in consumer switch: a consumer that keeps reading
`CommitmentTx.consumerOutputs` but is handed the migrated transaction
(`migrateForConsumer`) reads exactly the `CommitmentParams` consumer list. -/
theorem paramsTx_migrateForConsumer_consumerOutputs
    (p : LnLean.Bitcoin.CommitmentParams) (holder : Direction)
    (commitmentNumber fundingValueSat feeSat dustLimitSat : Nat)
    (toLocalScript toRemoteScript localAnchorScript remoteAnchorScript :
      ScriptPubKey) (htlcScript : CommitmentHTLCOutput → ScriptPubKey)
    (hdust : 0 < dustLimitSat)
    (hl : 0 ≤ p.toLocalValue) (hr : 0 ≤ p.toRemoteValue)
    (hld : dustLimitSat ≤ p.toLocalValue.toNat)
    (hrd : dustLimitSat ≤ p.toRemoteValue.toNat) :
    (paramsTx p holder commitmentNumber fundingValueSat feeSat dustLimitSat
        toLocalScript toRemoteScript localAnchorScript remoteAnchorScript
        htlcScript).migrateForConsumer.consumerOutputs =
      paramsConsumerOutputs p := by
  simpa only [CommitmentTx.migratedConsumerOutputs, CommitmentTx.consumerOutputs]
    using paramsTx_migratedConsumerOutputs_eq p holder commitmentNumber
      fundingValueSat feeSat dustLimitSat toLocalScript toRemoteScript
      localAnchorScript remoteAnchorScript htlcScript hdust hl hr hld hrd

/-- The sorted rich net list (`netConsumerOutputs`) is a permutation of the same
`CommitmentParams` consumer list: a consumer that can read
`CommitmentTxOutput` gets the BOLT 3 sorted order, and a consumer that can only
read the legacy type gets `migratedConsumerOutputs`; both refine the same
script-level output multiset. -/
theorem paramsTx_netConsumerOutputs_perm_paramsConsumerOutputs
    (p : LnLean.Bitcoin.CommitmentParams) (holder : Direction)
    (commitmentNumber fundingValueSat feeSat dustLimitSat : Nat)
    (toLocalScript toRemoteScript localAnchorScript remoteAnchorScript :
      ScriptPubKey) (htlcScript : CommitmentHTLCOutput → ScriptPubKey)
    (hdust : 0 < dustLimitSat)
    (hl : 0 ≤ p.toLocalValue) (hr : 0 ≤ p.toRemoteValue)
    (hld : dustLimitSat ≤ p.toLocalValue.toNat)
    (hrd : dustLimitSat ≤ p.toRemoteValue.toNat) :
    ((paramsTx p holder commitmentNumber fundingValueSat feeSat dustLimitSat
          toLocalScript toRemoteScript localAnchorScript remoteAnchorScript
          htlcScript).netConsumerOutputs.map
        CommitmentTxOutput.toCommitmentOutput).Perm
      (paramsConsumerOutputs p) := by
  have h := LnLean.Proofs.Channel.CommitmentConsumer.netConsumerOutputs_perm_migratedConsumerOutputs
    (paramsTx p holder commitmentNumber fundingValueSat feeSat dustLimitSat
      toLocalScript toRemoteScript localAnchorScript remoteAnchorScript
      htlcScript) hdust
  rw [paramsTx_migratedConsumerOutputs_eq p holder commitmentNumber
      fundingValueSat feeSat dustLimitSat toLocalScript toRemoteScript
      localAnchorScript remoteAnchorScript htlcScript hdust hl hr hld hrd] at h
  exact h

/-! ## 4. The normal-form premises are necessary -/

/-- Concrete parameters with both values positive; `toLocalValue` is below the
demo dust limit used by the counterexample. -/
def demoParams : LnLean.Bitcoin.CommitmentParams where
  revocationKey := ⟨ByteArray.empty⟩
  delayedPaymentKey := ⟨ByteArray.empty⟩
  remotePaymentKey := ⟨ByteArray.empty⟩
  localFundingKey := ⟨ByteArray.empty⟩
  remoteFundingKey := ⟨ByteArray.empty⟩
  toSelfDelay := 144
  toLocalValue := 500
  toRemoteValue := 1000
  toLocalWitnessScriptHash := ByteArray.empty
  toRemoteWitnessScriptHash := ByteArray.empty
  localAnchorWitnessScriptHash := ByteArray.empty
  remoteAnchorWitnessScriptHash := ByteArray.empty

/-- Concrete script placeholder; the value-only consumer list never reads it. -/
def emptyScriptPubKey : ScriptPubKey := ⟨[]⟩

/-- The demo transaction at the script boundary. -/
def demoTx : CommitmentTx :=
  paramsTx demoParams .local 0 2000 100 1000
    emptyScriptPubKey emptyScriptPubKey emptyScriptPubKey emptyScriptPubKey
    (fun _ => emptyScriptPubKey)

/-- **The positive-dust/no-trim premise is necessary at the params boundary.**
`demoParams.toLocalValue = 500` is below the dust limit `1000`, so the net
migration zeros (and therefore drops) the `to_local` output.  The migrated list
has three entries while the script-level projection still has four.  This is
the `CommitmentParams` counterpart of
`legacyCoverage_not_preserved_by_net_migration` and wave-4
`dust_trimming_not_perm`; both are unchanged. -/
theorem belowDust_migration_changes_params_boundary :
    demoTx.migratedConsumerOutputs ≠ paramsConsumerOutputs demoParams ∧
      demoTx.migratedConsumerOutputs.length = 3 ∧
      (paramsConsumerOutputs demoParams).length = 4 := by
  refine ⟨?_, by decide, ?_⟩
  · intro h
    have h3 : demoTx.migratedConsumerOutputs.length = 3 := by decide
    rw [h] at h3
    have h4 : (paramsConsumerOutputs demoParams).length = 4 := by decide
    omega
  · decide

/-- A zero `to_local` value is emitted by the script-level list but omitted by
the legacy `Commitment.commitmentOutputs` function.  So the legacy boundary
also needs the non-zero part of the normal form, not only nonnegativity. -/
theorem zero_toLocal_params_not_legacy :
    (paramsToCommitment { demoParams with toLocalValue := 0 } .local 0 2000 100).commitmentOutputs ≠
      paramsConsumerOutputs { demoParams with toLocalValue := 0 } := by
  intro h
  have h3 : ((paramsToCommitment { demoParams with toLocalValue := 0 } .local 0 2000 100).commitmentOutputs).length = 3 := by
    decide
  have h4 : (paramsConsumerOutputs { demoParams with toLocalValue := 0 }).length = 4 := by
    decide
  rw [h] at h3
  omega

/-- A negative signed `to_local` value has no legacy `Nat` counterpart; the
projection drops it rather than truncating to zero.  This keeps wave-E `E45`'s
`0 ≤ toLocalValue` obligation explicit. -/
theorem negative_toLocal_projection_drops :
    commitmentOutputToLegacy
        { kind := LnLean.Bitcoin.OutputKind.toLocal, value := -1,
          scriptPubKey := ⟨ByteArray.empty⟩ } = none := by
  simp [commitmentOutputToLegacy]

/-- Consequently the negative-value parameter set is not representable by the
legacy consumer list: the script-level list has four outputs, the projection
has three.  The missing hypothesis is exactly `0 ≤ p.toLocalValue` (and
symmetrically for `toRemoteValue`). -/
theorem negative_value_not_represented :
    (paramsConsumerOutputs { demoParams with toLocalValue := -1 }).length = 3 ∧
      (LnLean.Bitcoin.commitmentOutputs
        { demoParams with toLocalValue := -1 }).length = 4 := by
  constructor <;> decide

/-! ## 5. Preserved consumer-migration counterexamples -/

/-- Wave-7's consumer-boundary coverage counterexample is retained unchanged:
one HTLC signature covers the nominal demo commitment, but not the net-migrated
one. -/
theorem legacyCoverage_counterexample_retained :
    LnLean.Proofs.Channel.CommitmentConsumer.oneHtlcSigMessage.htlcSignatures.length =
        htlcOutputCount
          LnLean.Proofs.Channel.CommitmentIntegration.dustDemoTx.commitment.commitmentOutputs ∧
      ¬ LnLean.Proofs.Channel.CommitmentConsumer.CoversMigratedOutputs
        LnLean.Proofs.Channel.CommitmentConsumer.oneHtlcSigMessage
        LnLean.Proofs.Channel.CommitmentIntegration.dustDemoTx :=
  LnLean.Proofs.Channel.CommitmentConsumer.legacyCoverage_not_preserved_by_net_migration

/-- D12's unconditional output-ordering refutation is retained unchanged. -/
theorem d12_ordering_counterexample_retained :
    ¬ (∀ c : Commitment,
        (c.commitmentOutputs.map CommitmentOutput.value).Pairwise (· ≤ ·)) :=
  LnLean.Proofs.Channel.CommitmentConsumer.d12_output_ordering_fails_retained

/-- Wave-4's dust-trimming non-permutation counterexample is retained
unchanged. -/
theorem dust_trimming_counterexample_retained :
    ¬ (LnLean.Proofs.Channel.CommitmentIntegration.legacyOutputs
          LnLean.Proofs.Channel.CommitmentIntegration.dustDemoTx).Perm
        LnLean.Proofs.Channel.CommitmentIntegration.dustDemoTx.commitment.commitmentOutputs :=
  LnLean.Proofs.Channel.CommitmentConsumer.wave4_dust_trimming_not_perm_retained

end LnLean.Proofs.WaveH.H26
