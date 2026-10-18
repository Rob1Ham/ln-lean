import LnLean.Channel.Commitment
import LnLean.Channel.HTLC
import LnLean.Proofs.Channel.CommitmentIntegrationTargets
import LnLean.Proofs.WaveD.D12

/-!
# BOLT 3 gross/net commitment outputs, trimming, and conservation (CH-03)

Open issue `CH-03` records that the rich commitment model has only one satoshi
value per HTLC (`CommitmentHTLCOutput.amountSat`) and no recorded trimmed
total/effective fee, so the second-stage (net) value cannot be represented and
the trim accounting stays explicit in the wave-4 integration module.  This
module supplies the missing gross/net layer and proves the canonical legacy
refinement and the exact fee accounting.

## Model

BOLT 3 uses two values for each HTLC:

* the **gross** value `amount_msat / 1000`, which is the value of the
  commitment transaction output (`03-transactions.md:365`), and
* the **net** value `gross - second_stage_fee`, which is what the
  HTLC-timeout/HTLC-success transaction pays (`03-transactions.md:381`).

The dust test is on the net value (equivalently
`gross < dust_limit + second_stage_fee`), and the commitment output is gross
(`03-transactions.md:330-346`).  A trimmed output's whole gross value is added
to the commitment transaction fee (`03-transactions.md:329`).

The core patch in `LnLean/Channel/Commitment.lean` is additive:

* `CommitmentTx.netAmountSat : CommitmentHTLCOutput → Nat` (default
  `h.amountSat`) is the second-stage value used by the BOLT 3 dust test;
* `CommitmentTx.trimmedSat : Nat` (default `0`) records the gross value
  removed by trimming;
* `CommitmentTx.outputsNet` / `CommitmentTx.htlcOutputNet` are the net-based
  construction; the pre-CH-03 `outputs`/`htlcOutput` are retained unchanged for
  every existing consumer;
* `Commitment.trimmedSat` computes the trimmed gross value for a nominal
  record, and `Commitment.effectiveFeeSat` is
  `fundingValueSat - totalOutputValue`.

`CommitmentHTLCOutput` itself is defined in `LnLean/Channel/Types.lean`, which
is outside this lane's ownership.  The additive field
`netAmountSat : Nat := amountSat` and the corresponding
`Commitment.trimmedSat : Nat := 0` field are recorded as an exact integration
patch in `agents/reports/swarm5/S5-CH-GROSSNET.md`; the core patch above is the
same design expressed through the owned `CommitmentTx` extension, with identity
and zero defaults preserving every existing record literal.

## Results

* `outputsNet_refines_canonicalOutputs`: the sorted net-based output list maps
  to a **permutation** of the legacy-shaped, BOLT-3-trimmed output list at
  **arbitrary** dust limit.  There is no `dustLimitSat = 0` hypothesis.
* `canonicalOutputs_eq_commitmentOutputs_of_migrated`: on a migrated record
  (trimmed outputs zeroed, survivors at or above dust) that canonical list is
  exactly `Commitment.commitmentOutputs`.
* `outputsNet_perm_commitmentOutputs_of_migrated`: consequently the rich sorted
  list refines the actual legacy consumer path `commitmentOutputs`, again at
  arbitrary dust.
* `migratedFrom_totalOutputValue_add_trimmedSat`: the migrated record's emitted
  value plus its recorded trimmed value is the nominal output value.
* `migratedFrom_conservation` and `migratedFrom_effectiveFee_eq`: the funding
  value splits as `emitted + base fee + trimmed`, and the effective fee is
  exactly `base fee + trimmed`.  The second-stage fee is *not* part of the
  commitment fee: it is paid later out of the gross HTLC output.
* `outputsNet_spec`: the net construction is a permutation of its pre-sort
  list, sorted by value/script/CLTV, trims exactly the below-dust HTLCs, and
  emits no below-dust non-anchor output.

The wave-4 conditional results and the D12 refutations remain imported and are
restated at the end of this module (`wave4_*`, `d12_*`).  Nothing in D12 is
weakened: the unconditional ordering claim about `commitmentOutputs` is still
false, and the legacy function still emits a zero-valued HTLC output.

## Scope caveats

* Script execution, signature checking, witnesses, and sighash are out of
  scope; script bytes are the caller-supplied `CommitmentTx` fields.
* `option_anchors` second-stage fees are zero, as BOLT 3 prescribes.
* BOLT 2 requires `dust_limit_satoshis >= 354` (`02-peer-protocol.md:870`).
  The migration theorems therefore assume `0 < dustLimitSat` when they must
  match the legacy "omit zero-valued outputs" convention; the conservation and
  canonical-permutation theorems themselves are unconditional.
* The legacy `Commitment.commitmentOutputs` is still not sorted; the refinement
  is a permutation, which is the strongest true relation.
-/

namespace LnLean.Proofs.Channel.CommitmentGrossNet

set_option autoImplicit false

open LnLean
open LnLean.Channel

/-! ## 1. The BOLT 3 second-stage fee -/

/-- BOLT 3 HTLC-timeout fee from the negotiated feerate: weight 663, zero with
`option_anchors`. -/
def htlcTimeoutFee (anchors : Bool) (r : FeeRate) : Nat :=
  CommitmentIntegration.htlcTimeoutFeeSat anchors r

/-- BOLT 3 HTLC-success fee from the negotiated feerate: weight 703, zero with
`option_anchors`. -/
def htlcSuccessFee (anchors : Bool) (r : FeeRate) : Nat :=
  CommitmentIntegration.htlcSuccessFeeSat anchors r

/-- The direction-dependent second-stage fee for one commitment HTLC output. -/
def htlcSecondStageFee (anchors : Bool) (r : FeeRate)
    (h : CommitmentHTLCOutput) : Nat :=
  CommitmentIntegration.secondStageFeeAt anchors r h.direction

theorem htlcTimeoutFee_eq (anchors : Bool) (r : FeeRate) :
    htlcTimeoutFee anchors r = CommitmentIntegration.htlcTimeoutFeeSat anchors r := rfl

theorem htlcSuccessFee_eq (anchors : Bool) (r : FeeRate) :
    htlcSuccessFee anchors r = CommitmentIntegration.htlcSuccessFeeSat anchors r := rfl

theorem htlcSecondStageFee_local (anchors : Bool) (r : FeeRate) :
    htlcSecondStageFee anchors r
        { direction := .local, amountSat := 0, cltvExpiry := 0,
          state := .offered } =
      htlcTimeoutFee anchors r := by
  simp [htlcSecondStageFee, htlcTimeoutFee, CommitmentIntegration.secondStageFeeAt,
    secondStageFee]

theorem htlcSecondStageFee_remote (anchors : Bool) (r : FeeRate) :
    htlcSecondStageFee anchors r
        { direction := .remote, amountSat := 0, cltvExpiry := 0,
          state := .received } =
      htlcSuccessFee anchors r := by
  simp [htlcSecondStageFee, htlcSuccessFee, CommitmentIntegration.secondStageFeeAt,
    secondStageFee]

/-- With `option_anchors`, BOLT 3's second-stage transactions pay no fee. -/
theorem htlcSecondStageFee_anchors (r : FeeRate) (h : CommitmentHTLCOutput) :
    htlcSecondStageFee true r h = 0 := by
  unfold htlcSecondStageFee CommitmentIntegration.secondStageFeeAt
  exact CommitmentIntegration.secondStageFeeAt_anchors r h.direction

/-- The fee depends only on the output's direction. -/
theorem htlcSecondStageFee_eq_of_direction {anchors : Bool} {r : FeeRate}
    {h₁ h₂ : CommitmentHTLCOutput} (hd : h₁.direction = h₂.direction) :
    htlcSecondStageFee anchors r h₁ = htlcSecondStageFee anchors r h₂ := by
  simp [htlcSecondStageFee, hd]

/-! ## 2. Net consistency and the exact trimming threshold

`NetConsistent` is the BOLT 3 relation between the gross value carried by the
commitment output and the net value used by the dust test:
`net + second_stage_fee = gross`.  It is a hypothesis, not a definition,
because the net amount is supplied by the caller (it depends on the
second-stage fee schedule and on the commitment number only through the
feerate, which is already a parameter). -/

/-- Every HTLC in the commitment has `net + second_stage_fee = gross`. -/
def NetConsistent (tx : CommitmentTx) (anchors : Bool) (r : FeeRate) : Prop :=
  ∀ h ∈ tx.commitment.htlcs,
    tx.netAmountSat h + htlcSecondStageFee anchors r h = h.amountSat

/-- Under net consistency, the net value never exceeds the gross value. -/
theorem netAmountSat_le_amountSat_of_netConsistent {tx : CommitmentTx}
    {anchors : Bool} {r : FeeRate} (hc : NetConsistent tx anchors r)
    {h : CommitmentHTLCOutput} (hmem : h ∈ tx.commitment.htlcs) :
    tx.netAmountSat h ≤ h.amountSat := by
  have hnet := hc h hmem
  omega

/-- BOLT 3's dust test in net form and its gross-threshold form are equivalent
whenever `net + second_stage_fee = gross`.  No positivity hypothesis on the
dust limit is needed: the relation is exact, not a saturating subtraction. -/
theorem net_lt_dust_iff_gross_lt_threshold {tx : CommitmentTx}
    {h : CommitmentHTLCOutput} {anchors : Bool} {r : FeeRate}
    (hnet : tx.netAmountSat h + htlcSecondStageFee anchors r h = h.amountSat) :
    tx.netAmountSat h < tx.dustLimitSat ↔
      h.amountSat < tx.dustLimitSat + htlcSecondStageFee anchors r h := by
  omega

/-- The BOLT 3 net-based `htlcOutputNet` is absent exactly when the gross
amount is below `dust_limit + second_stage_fee`. -/
theorem htlcOutputNet_eq_none_iff_gross_threshold (tx : CommitmentTx)
    (h : CommitmentHTLCOutput) (anchors : Bool) (r : FeeRate)
    (hnet : tx.netAmountSat h + htlcSecondStageFee anchors r h = h.amountSat) :
    tx.htlcOutputNet h = none ↔
      h.amountSat < tx.dustLimitSat + htlcSecondStageFee anchors r h := by
  unfold CommitmentTx.htlcOutputNet
  by_cases hd : tx.dustLimitSat ≤ tx.netAmountSat h
  · have hnot : ¬ h.amountSat <
        tx.dustLimitSat + htlcSecondStageFee anchors r h := by
      omega
    simp [hd, hnot]
  · have hlt : tx.netAmountSat h < tx.dustLimitSat := Nat.lt_of_not_le hd
    have hlt' : h.amountSat <
        tx.dustLimitSat + htlcSecondStageFee anchors r h := by
      omega
    simp [hd, hlt']

/-- Equality with the threshold is kept, not trimmed: a gross amount exactly
`dust_limit + second_stage_fee` produces its commitment output. -/
theorem htlcOutputNet_isSome_of_threshold_eq (tx : CommitmentTx)
    (h : CommitmentHTLCOutput) (anchors : Bool) (r : FeeRate)
    (hnet : tx.netAmountSat h + htlcSecondStageFee anchors r h = h.amountSat)
    (heq : h.amountSat = tx.dustLimitSat + htlcSecondStageFee anchors r h) :
    (tx.htlcOutputNet h).isSome = true := by
  have hle : tx.dustLimitSat ≤ tx.netAmountSat h := by omega
  unfold CommitmentTx.htlcOutputNet
  simp [hle]

/-! ## 3. The canonical legacy-shaped trimmed output list -/

/-- The BOLT 3 trim decision as a `Bool`, so it can be used by `List.filter`
and `List.filterMap` without decidability friction. -/
def keepHtlc (dustLimitSat : Nat) (netAmountSat : CommitmentHTLCOutput → Nat)
    (h : CommitmentHTLCOutput) : Bool :=
  decide (dustLimitSat ≤ netAmountSat h)

theorem keepHtlc_eq_true_iff {d : Nat} {net : CommitmentHTLCOutput → Nat}
    {h : CommitmentHTLCOutput} :
    keepHtlc d net h = true ↔ d ≤ net h :=
  decide_eq_true_iff

/-- The legacy group order (`to_local`, `to_remote`, HTLCs, anchors) with the
BOLT 3 net-based dust filter applied and **gross** HTLC values emitted.  This
is the canonical consumer-shaped view of the net construction. -/
def _root_.LnLean.Channel.CommitmentTx.canonicalOutputs
    (tx : CommitmentTx) : List CommitmentOutput :=
  (if tx.dustLimitSat ≤ tx.commitment.toLocalSat then
    [CommitmentOutput.toLocal tx.commitment.toLocalSat] else []) ++
  (if tx.dustLimitSat ≤ tx.commitment.toRemoteSat then
    [CommitmentOutput.toRemote tx.commitment.toRemoteSat] else []) ++
  (tx.commitment.htlcs.filterMap (fun h =>
    if keepHtlc tx.dustLimitSat tx.netAmountSat h = true then
      some (CommitmentOutput.htlc h.direction h.amountSat)
    else none)) ++
  (if tx.commitment.anchorOutputs then
    [CommitmentOutput.localAnchor, CommitmentOutput.remoteAnchor] else [])

/-- Pointwise congruence for `List.filterMap`, absent from the core library. -/
theorem filterMap_congr_pointwise {α β : Type} {f g : α → Option β}
    (h : ∀ a, f a = g a) (l : List α) : l.filterMap f = l.filterMap g := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      simp only [List.filterMap_cons]
      rw [h a, ih]

/-- Mapping the net-based pre-sort output list to the legacy output type is
exactly the canonical trimmed list. -/
theorem map_outputsUnsortedNet_eq_canonicalOutputs (tx : CommitmentTx) :
    (tx.outputsUnsortedNet.map CommitmentTxOutput.toCommitmentOutput) =
      tx.canonicalOutputs := by
  have hloc :
      ((tx.toLocalOutput.toList).map CommitmentTxOutput.toCommitmentOutput) =
        (if tx.dustLimitSat ≤ tx.commitment.toLocalSat then
          [CommitmentOutput.toLocal tx.commitment.toLocalSat] else []) := by
    unfold CommitmentTx.toLocalOutput
    by_cases h : tx.dustLimitSat ≤ tx.commitment.toLocalSat <;>
      simp [h, CommitmentTxOutput.toLocal, CommitmentTxOutput.toCommitmentOutput]
  have hrem :
      ((tx.toRemoteOutput.toList).map CommitmentTxOutput.toCommitmentOutput) =
        (if tx.dustLimitSat ≤ tx.commitment.toRemoteSat then
          [CommitmentOutput.toRemote tx.commitment.toRemoteSat] else []) := by
    unfold CommitmentTx.toRemoteOutput
    by_cases h : tx.dustLimitSat ≤ tx.commitment.toRemoteSat <;>
      simp [h, CommitmentTxOutput.toRemote, CommitmentTxOutput.toCommitmentOutput]
  have hhtlc :
      (tx.commitment.htlcs.filterMap tx.htlcOutputNet).map
          CommitmentTxOutput.toCommitmentOutput =
        tx.commitment.htlcs.filterMap (fun h =>
          if keepHtlc tx.dustLimitSat tx.netAmountSat h = true then
            some (CommitmentOutput.htlc h.direction h.amountSat)
          else none) := by
    rw [List.map_filterMap]
    apply filterMap_congr_pointwise
    intro h
    unfold CommitmentTx.htlcOutputNet keepHtlc
    by_cases hd : tx.dustLimitSat ≤ tx.netAmountSat h <;>
      simp [hd, CommitmentTxOutput.toCommitmentOutput, CommitmentTxOutput.htlc]
  have hanchL :
      ((tx.localAnchorOutput.toList).map CommitmentTxOutput.toCommitmentOutput) =
        (if tx.commitment.anchorOutputs then
          [CommitmentOutput.localAnchor] else []) := by
    unfold CommitmentTx.localAnchorOutput
    by_cases h : tx.commitment.anchorOutputs <;>
      simp [h, CommitmentTxOutput.localAnchor, CommitmentTxOutput.toCommitmentOutput]
  have hanchR :
      ((tx.remoteAnchorOutput.toList).map CommitmentTxOutput.toCommitmentOutput) =
        (if tx.commitment.anchorOutputs then
          [CommitmentOutput.remoteAnchor] else []) := by
    unfold CommitmentTx.remoteAnchorOutput
    by_cases h : tx.commitment.anchorOutputs <;>
      simp [h, CommitmentTxOutput.remoteAnchor, CommitmentTxOutput.toCommitmentOutput]
  unfold CommitmentTx.outputsUnsortedNet CommitmentTx.canonicalOutputs
  simp only [List.map_append]
  rw [hloc, hrem, hhtlc, hanchL, hanchR]
  by_cases ha : tx.commitment.anchorOutputs <;> simp [ha]

/-- **Canonical legacy refinement at arbitrary dust limit.**  The sorted
net-based output list projects to a permutation of the legacy-shaped trimmed
list.  No zero-dust hypothesis and no non-zero-output hypothesis are needed:
the trimming is part of the canonical list itself. -/
theorem outputsNet_refines_canonicalOutputs (tx : CommitmentTx) :
    (tx.outputsNet.map CommitmentTxOutput.toCommitmentOutput).Perm
      tx.canonicalOutputs := by
  rw [← map_outputsUnsortedNet_eq_canonicalOutputs]
  exact (CommitmentTx.outputsNet_perm tx).map CommitmentTxOutput.toCommitmentOutput

/-! ## 4. Migrated records: exact refinement to `commitmentOutputs`

A *migrated* record has already applied the BOLT 3 trim filter: every trimmed
output is zeroed (so the legacy function, which omits zero-valued
non-HTLC outputs, agrees) and the surviving HTLCs are exactly those at or above
the net dust threshold.  This is the normal form produced by
`CommitmentTx.migratedFrom` below. -/

/-- A commitment transaction whose outputs have already been migrated to the
BOLT 3 survivor set: a zero non-HTLC output is exactly a below-dust one, and
every HTLC in the list survives the net dust test. -/
def _root_.LnLean.Channel.CommitmentTx.Migrated (tx : CommitmentTx) : Prop :=
  (tx.commitment.toLocalSat = 0 ↔
      tx.commitment.toLocalSat < tx.dustLimitSat) ∧
  (tx.commitment.toRemoteSat = 0 ↔
      tx.commitment.toRemoteSat < tx.dustLimitSat) ∧
  (∀ h ∈ tx.commitment.htlcs, tx.dustLimitSat ≤ tx.netAmountSat h)

/-- On a list where every element survives the net dust test, filtering is the
identity followed by the same output map. -/
theorem filterMap_keep_eq_map (d : Nat)
    (net : CommitmentHTLCOutput → Nat) :
    ∀ l : List CommitmentHTLCOutput,
      (∀ x ∈ l, keepHtlc d net x = true) →
      l.filterMap (fun h =>
        if keepHtlc d net h = true then
          some (CommitmentOutput.htlc h.direction h.amountSat)
        else none) =
      l.map (fun h => CommitmentOutput.htlc h.direction h.amountSat)
  | [], _ => rfl
  | h :: t, hk => by
      have hh' : keepHtlc d net h = true := hk h (by simp)
      have ht : ∀ x ∈ t, keepHtlc d net x = true :=
        fun x hx => hk x (by simp [hx])
      simp [hh', filterMap_keep_eq_map d net t ht]

/-- On a migrated record the canonical trimmed list is exactly the legacy
`Commitment.commitmentOutputs`.  No dust-limit hypothesis appears: `Migrated`
already states that zeroed outputs are below dust and survivors are above it. -/
theorem canonicalOutputs_eq_commitmentOutputs_of_migrated (tx : CommitmentTx)
    (hm : tx.Migrated) :
    tx.canonicalOutputs = tx.commitment.commitmentOutputs := by
  obtain ⟨hl, hr, hh⟩ := hm
  have hloc :
      (if tx.dustLimitSat ≤ tx.commitment.toLocalSat then
        [CommitmentOutput.toLocal tx.commitment.toLocalSat] else []) =
      (if tx.commitment.toLocalSat = 0 then []
        else [CommitmentOutput.toLocal tx.commitment.toLocalSat]) := by
    by_cases h0 : tx.commitment.toLocalSat = 0
    · have hlt : tx.commitment.toLocalSat < tx.dustLimitSat := hl.mp h0
      simp [h0]
      omega
    · have hge : tx.dustLimitSat ≤ tx.commitment.toLocalSat := by
        by_cases hlt : tx.commitment.toLocalSat < tx.dustLimitSat
        · exact absurd (hl.mpr hlt) h0
        · omega
      simp [h0, hge]
  have hrem :
      (if tx.dustLimitSat ≤ tx.commitment.toRemoteSat then
        [CommitmentOutput.toRemote tx.commitment.toRemoteSat] else []) =
      (if tx.commitment.toRemoteSat = 0 then []
        else [CommitmentOutput.toRemote tx.commitment.toRemoteSat]) := by
    by_cases h0 : tx.commitment.toRemoteSat = 0
    · have hlt : tx.commitment.toRemoteSat < tx.dustLimitSat := hr.mp h0
      simp [h0]
      omega
    · have hge : tx.dustLimitSat ≤ tx.commitment.toRemoteSat := by
        by_cases hlt : tx.commitment.toRemoteSat < tx.dustLimitSat
        · exact absurd (hr.mpr hlt) h0
        · omega
      simp [h0, hge]
  have hmap :
      tx.commitment.htlcs.filterMap (fun h =>
        if keepHtlc tx.dustLimitSat tx.netAmountSat h = true then
          some (CommitmentOutput.htlc h.direction h.amountSat)
        else none) =
      tx.commitment.htlcs.map
        (fun h => CommitmentOutput.htlc h.direction h.amountSat) :=
    filterMap_keep_eq_map tx.dustLimitSat tx.netAmountSat tx.commitment.htlcs
      (fun x hx => (keepHtlc_eq_true_iff).2 (hh x hx))
  unfold CommitmentTx.canonicalOutputs Commitment.commitmentOutputs
  rw [hloc, hrem, hmap]

/-- **The canonical legacy refinement without the zero-dust workaround.**  On a
migrated record, the sorted net-based output list refines the actual legacy
consumer path `Commitment.commitmentOutputs` by permutation, at an arbitrary
dust limit. -/
theorem outputsNet_perm_commitmentOutputs_of_migrated (tx : CommitmentTx)
    (hm : tx.Migrated) :
    (tx.outputsNet.map CommitmentTxOutput.toCommitmentOutput).Perm
      tx.commitment.commitmentOutputs := by
  rw [← canonicalOutputs_eq_commitmentOutputs_of_migrated tx hm]
  exact outputsNet_refines_canonicalOutputs tx

/-! ## 5. The migrated construction and its accounting -/

/-- Apply the BOLT 3 net-based trim filter to a nominal commitment transaction:
zero every below-dust `to_local`/`to_remote`, keep exactly the surviving
HTLCs, and record the removed gross value in `trimmedSat`. -/
def _root_.LnLean.Channel.CommitmentTx.migratedFrom (tx : CommitmentTx) : CommitmentTx :=
  { tx with
    commitment :=
      { tx.commitment with
        toLocalSat :=
          if tx.dustLimitSat ≤ tx.commitment.toLocalSat then
            tx.commitment.toLocalSat else 0
        toRemoteSat :=
          if tx.dustLimitSat ≤ tx.commitment.toRemoteSat then
            tx.commitment.toRemoteSat else 0
        htlcs := tx.commitment.htlcs.filter
          (keepHtlc tx.dustLimitSat tx.netAmountSat) },
    trimmedSat := tx.trimmedValue }

theorem _root_.LnLean.Channel.CommitmentTx.migratedFrom_feeSat (tx : CommitmentTx) :
    (tx.migratedFrom).commitment.feeSat = tx.commitment.feeSat := rfl

theorem _root_.LnLean.Channel.CommitmentTx.migratedFrom_fundingValueSat (tx : CommitmentTx) :
    (tx.migratedFrom).commitment.fundingValueSat =
      tx.commitment.fundingValueSat := rfl

theorem _root_.LnLean.Channel.CommitmentTx.migratedFrom_trimmedSat (tx : CommitmentTx) :
    (tx.migratedFrom).trimmedSat = tx.trimmedValue := rfl

/-- The migration is idempotent on the trim decision. -/
theorem _root_.LnLean.Channel.CommitmentTx.migratedFrom_htlcs (tx : CommitmentTx) :
    (tx.migratedFrom).commitment.htlcs =
      tx.commitment.htlcs.filter
        (keepHtlc tx.dustLimitSat tx.netAmountSat) := rfl

/-- A protocol-valid positive dust limit makes the migrated record a `Migrated`
record.  BOLT 2 requires `dust_limit_satoshis >= 354`
(`02-peer-protocol.md:870`), so the positivity hypothesis is the protocol
domain, not a model workaround. -/
theorem _root_.LnLean.Channel.CommitmentTx.migratedFrom_migrated (tx : CommitmentTx)
    (hdust : 0 < tx.dustLimitSat) : (tx.migratedFrom).Migrated := by
  unfold CommitmentTx.Migrated
  constructor
  · -- to_local: zeroing exactly the below-dust value
    by_cases hd : tx.dustLimitSat ≤ tx.commitment.toLocalSat
    · have hpos : tx.commitment.toLocalSat ≠ 0 := by omega
      have hnot : ¬ tx.commitment.toLocalSat < tx.dustLimitSat := by omega
      simp [CommitmentTx.migratedFrom, hd, hpos, hnot]
    · have hlt : tx.commitment.toLocalSat < tx.dustLimitSat :=
        Nat.lt_of_not_le hd
      simp [CommitmentTx.migratedFrom, hd]
      omega
  · constructor
    · by_cases hd : tx.dustLimitSat ≤ tx.commitment.toRemoteSat
      · have hpos : tx.commitment.toRemoteSat ≠ 0 := by omega
        have hnot : ¬ tx.commitment.toRemoteSat < tx.dustLimitSat := by omega
        simp [CommitmentTx.migratedFrom, hd, hpos, hnot]
      · have hlt : tx.commitment.toRemoteSat < tx.dustLimitSat :=
          Nat.lt_of_not_le hd
        simp [CommitmentTx.migratedFrom, hd]
        omega
    · intro h hmem
      rw [CommitmentTx.migratedFrom_htlcs] at hmem
      exact (keepHtlc_eq_true_iff).1 (List.mem_filter.1 hmem).2

/-- The migrated record keeps the nominal net projection. -/
theorem _root_.LnLean.Channel.CommitmentTx.migratedFrom_netAmountSat (tx : CommitmentTx)
    (h : CommitmentHTLCOutput) :
    (tx.migratedFrom).netAmountSat h = tx.netAmountSat h := rfl

/-- Net consistency survives migration. -/
theorem _root_.LnLean.Channel.CommitmentTx.migratedFrom_netConsistent (tx : CommitmentTx)
    {anchors : Bool} {r : FeeRate} (hc : NetConsistent tx anchors r) :
    NetConsistent (tx.migratedFrom) anchors r := by
  intro h hmem
  rw [CommitmentTx.migratedFrom_htlcs] at hmem
  exact hc h (List.mem_filter.1 hmem).1

/-- The canonical legacy-shaped list is invariant under migration. -/
theorem _root_.LnLean.Channel.CommitmentTx.canonicalOutputs_migratedFrom (tx : CommitmentTx) :
    (tx.migratedFrom).canonicalOutputs = tx.canonicalOutputs := by
  unfold CommitmentTx.canonicalOutputs CommitmentTx.migratedFrom
  have hkept :
      (tx.commitment.htlcs.filter
          (keepHtlc tx.dustLimitSat tx.netAmountSat)).filterMap
        (fun h =>
          if keepHtlc tx.dustLimitSat tx.netAmountSat h = true then
            some (CommitmentOutput.htlc h.direction h.amountSat)
          else none) =
      tx.commitment.htlcs.filterMap (fun h =>
        if keepHtlc tx.dustLimitSat tx.netAmountSat h = true then
          some (CommitmentOutput.htlc h.direction h.amountSat)
        else none) := by
    rw [List.filterMap_filter]
    apply filterMap_congr_pointwise
    intro h
    by_cases hh : keepHtlc tx.dustLimitSat tx.netAmountSat h = true <;>
      simp [hh]
  have hloc :
      (if tx.dustLimitSat ≤
          (if tx.dustLimitSat ≤ tx.commitment.toLocalSat then
            tx.commitment.toLocalSat else 0) then
        [CommitmentOutput.toLocal
          (if tx.dustLimitSat ≤ tx.commitment.toLocalSat then
            tx.commitment.toLocalSat else 0)]
      else []) =
      (if tx.dustLimitSat ≤ tx.commitment.toLocalSat then
        [CommitmentOutput.toLocal tx.commitment.toLocalSat] else []) := by
    by_cases hd : tx.dustLimitSat ≤ tx.commitment.toLocalSat <;>
      simp [hd] <;> omega
  have hrem :
      (if tx.dustLimitSat ≤
          (if tx.dustLimitSat ≤ tx.commitment.toRemoteSat then
            tx.commitment.toRemoteSat else 0) then
        [CommitmentOutput.toRemote
          (if tx.dustLimitSat ≤ tx.commitment.toRemoteSat then
            tx.commitment.toRemoteSat else 0)]
      else []) =
      (if tx.dustLimitSat ≤ tx.commitment.toRemoteSat then
        [CommitmentOutput.toRemote tx.commitment.toRemoteSat] else []) := by
    by_cases hd : tx.dustLimitSat ≤ tx.commitment.toRemoteSat <;>
      simp [hd] <;> omega
  rw [hkept, hloc, hrem]

/-- Migration does not change the rich net-based output list (as a
permutation): it is a canonical representative of the same trimmed output
set. -/
theorem _root_.LnLean.Channel.CommitmentTx.migratedFrom_outputsNet_perm_canonicalOutputs
    (tx : CommitmentTx) :
    ((tx.migratedFrom).outputsNet.map CommitmentTxOutput.toCommitmentOutput).Perm
      tx.canonicalOutputs := by
  have h := outputsNet_refines_canonicalOutputs tx.migratedFrom
  rwa [CommitmentTx.canonicalOutputs_migratedFrom] at h

/-- **End-to-end refinement without a zero-dust hypothesis.**  For a
protocol-valid positive dust limit, the migrated record's sorted net-based
output list is a permutation of that record's legacy
`Commitment.commitmentOutputs`. -/
theorem _root_.LnLean.Channel.CommitmentTx.migratedFrom_outputsNet_perm_commitmentOutputs
    (tx : CommitmentTx) (hdust : 0 < tx.dustLimitSat) :
    ((tx.migratedFrom).outputsNet.map CommitmentTxOutput.toCommitmentOutput).Perm
      (tx.migratedFrom).commitment.commitmentOutputs := by
  have hm := CommitmentTx.migratedFrom_migrated tx hdust
  rw [← canonicalOutputs_eq_commitmentOutputs_of_migrated
    (tx.migratedFrom) hm]
  exact outputsNet_refines_canonicalOutputs tx.migratedFrom

/-! ### 6. Value accounting -/

/-- Splitting a list sum by the keep/trim decision. -/
theorem sum_map_ite_add_sum_map_ite (d : Nat)
    (net : CommitmentHTLCOutput → Nat) (g : CommitmentHTLCOutput → Nat)
    (hs : List CommitmentHTLCOutput) :
    (hs.map (fun h => if d ≤ net h then g h else 0)).sum +
      (hs.map (fun h => if d ≤ net h then 0 else g h)).sum =
    (hs.map g).sum := by
  induction hs with
  | nil => rfl
  | cons h t ih =>
      by_cases hd : d ≤ net h <;> simp [hd] <;> omega

/-- The kept HTLC value of the net-based construction. -/
theorem htlcOutputsValue_filter_keep (d : Nat)
    (net : CommitmentHTLCOutput → Nat) (hs : List CommitmentHTLCOutput) :
    htlcOutputsValue (hs.filter (keepHtlc d net)) =
      (hs.map (fun h => if d ≤ net h then h.amountSat else 0)).sum := by
  induction hs with
  | nil => rfl
  | cons h t ih =>
      by_cases hd : d ≤ net h
      · have hk : keepHtlc d net h = true := (keepHtlc_eq_true_iff).2 hd
        simp [hk, htlcOutputsValue, hd, ih]
      · have hk : keepHtlc d net h = false := by
          cases hb : keepHtlc d net h
          · rfl
          · exact absurd ((keepHtlc_eq_true_iff).1 hb) hd
        simp [hk, hd, ih]

/-- **The migrated record's emitted value plus its recorded trimmed value is
the nominal output value.**  This is the value split that the legacy record
cannot express without a trimmed-total field. -/
theorem _root_.LnLean.Channel.CommitmentTx.migratedFrom_totalOutputValue_add_trimmedSat
    (tx : CommitmentTx) :
    (tx.migratedFrom).commitment.totalOutputValue +
        (tx.migratedFrom).trimmedSat =
      tx.commitment.totalOutputValue := by
  have hpart := sum_map_ite_add_sum_map_ite tx.dustLimitSat tx.netAmountSat
    (fun h => h.amountSat) tx.commitment.htlcs
  unfold CommitmentTx.migratedFrom Commitment.totalOutputValue
    Commitment.htlcOutputValue Commitment.anchorOutputValue CommitmentTx.trimmedValue
    Commitment.trimmedSat
  have hsum : htlcOutputsValue tx.commitment.htlcs =
      (tx.commitment.htlcs.map (fun h => h.amountSat)).sum := by
    simpa [Commitment.htlcOutputValue] using
      Commitment.htlcOutputValue_eq_sum tx.commitment
  rw [htlcOutputsValue_filter_keep, hsum]
  by_cases hL : tx.dustLimitSat ≤ tx.commitment.toLocalSat <;>
  by_cases hR : tx.dustLimitSat ≤ tx.commitment.toRemoteSat <;>
    simp [hL, hR] at hpart ⊢ <;>
    omega

/-- **BOLT 3 conservation of the migrated record.**  If the nominal record
satisfies the balance equation `totalOutputValue + baseFee = funding`, then the
migrated record's emitted value plus the same base fee plus the recorded
trimmed value reconstructs the funding value. -/
theorem _root_.LnLean.Channel.CommitmentTx.migratedFrom_conservation (tx : CommitmentTx)
    (hbal : tx.commitment.totalOutputValue + tx.commitment.feeSat =
      tx.commitment.fundingValueSat) :
    (tx.migratedFrom).commitment.totalOutputValue +
        (tx.migratedFrom).commitment.feeSat +
        (tx.migratedFrom).trimmedSat =
      tx.commitment.fundingValueSat := by
  have h := CommitmentTx.migratedFrom_totalOutputValue_add_trimmedSat tx
  have hfee := CommitmentTx.migratedFrom_feeSat tx
  rw [hfee]
  omega

/-- **Effective-fee accounting.**  The actual commitment fee is the base fee
plus the gross value removed by trimming.  The second-stage fee is paid later
by the HTLC transaction out of the gross HTLC output, so it does not appear
here; that is BOLT 3's `03-transactions.md:329` and `:381` accounting. -/
theorem _root_.LnLean.Channel.CommitmentTx.migratedFrom_effectiveFee_eq (tx : CommitmentTx)
    (hbal : tx.commitment.totalOutputValue + tx.commitment.feeSat =
      tx.commitment.fundingValueSat) :
    (tx.migratedFrom).commitment.effectiveFeeSat =
      (tx.migratedFrom).commitment.feeSat +
        (tx.migratedFrom).trimmedSat := by
  have h := CommitmentTx.migratedFrom_conservation tx hbal
  have hle : (tx.migratedFrom).commitment.totalOutputValue ≤
      tx.commitment.fundingValueSat := by omega
  unfold Commitment.effectiveFeeSat
  exact (Nat.sub_eq_iff_eq_add hle).2 (by omega)

/-- The same accounting read through the `Commitment.trimmedSat` function and
the recorded field: they agree on the migrated record by construction. -/
theorem _root_.LnLean.Channel.CommitmentTx.migratedFrom_trimmedSat_eq_computed (tx : CommitmentTx) :
    (tx.migratedFrom).trimmedSat =
      tx.commitment.trimmedSat tx.dustLimitSat tx.netAmountSat := rfl

/-- The effective fee is the funding residual. -/
theorem _root_.LnLean.Channel.CommitmentTx.migratedFrom_effectiveFee_val (tx : CommitmentTx) :
    (tx.migratedFrom).commitment.effectiveFeeSat =
      tx.commitment.fundingValueSat -
        (tx.migratedFrom).commitment.totalOutputValue := rfl

/-! ## 7. The net-based rich specification -/

/-- Every emitted non-anchor output of the net construction is at or above the
owner's dust limit, provided the net value never exceeds the gross value. -/
theorem _root_.LnLean.Channel.CommitmentTx.outputsNet_nonAnchor_value_ge_dust (tx : CommitmentTx)
    (hle : ∀ h, tx.netAmountSat h ≤ h.amountSat)
    {o : CommitmentTxOutput} (ho : o ∈ tx.outputsNet)
    (hl : o.kind ≠ .localAnchor) (hr : o.kind ≠ .remoteAnchor) :
    tx.dustLimitSat ≤ o.valueSat := by
  rw [CommitmentTx.mem_outputsNet_iff, CommitmentTx.mem_outputsUnsortedNet_iff] at ho
  rcases ho with h | h | h | h | h
  · rw [CommitmentTx.mem_toLocalOutput_iff] at h
    rw [h.2]
    exact h.1
  · rw [CommitmentTx.mem_toRemoteOutput_iff] at h
    rw [h.2]
    exact h.1
  · rw [List.mem_filterMap] at h
    obtain ⟨a, _, ha⟩ := h
    rw [CommitmentTx.mem_htlcOutputNet_iff] at ha
    rw [ha.2]
    exact Nat.le_trans ha.1 (hle a)
  · unfold CommitmentTx.localAnchorOutput at h
    by_cases ha : tx.commitment.anchorOutputs
    · simp [ha] at h
      have hk : o.kind = .localAnchor := by rw [h]; rfl
      exact absurd hk hl
    · simp [ha] at h
  · unfold CommitmentTx.remoteAnchorOutput at h
    by_cases ha : tx.commitment.anchorOutputs
    · simp [ha] at h
      have hk : o.kind = .remoteAnchor := by rw [h]; rfl
      exact absurd hk hr
    · simp [ha] at h

/-- **Net-based rich specification.**  The net construction is a permutation of
its pre-sort list; it is sorted by value, script, and CLTV; it trims exactly
the below-dust HTLCs; it emits every at-or-above-dust HTLC; and every emitted
non-anchor output is at or above the dust limit. -/
theorem _root_.LnLean.Channel.CommitmentTx.outputsNet_spec (tx : CommitmentTx)
    (hle : ∀ h, tx.netAmountSat h ≤ h.amountSat) :
    tx.outputsNet.Perm tx.outputsUnsortedNet ∧
    tx.outputsNet.Pairwise CommitmentTxOutput.le ∧
    (tx.outputsNet.map (fun o => o.valueSat)).Pairwise (· ≤ ·) ∧
    tx.outputsNet.Pairwise (fun a b =>
      a.valueSat = b.valueSat → a.scriptPubKey.le b.scriptPubKey) ∧
    tx.outputsNet.Pairwise (fun a b =>
      a.valueSat = b.valueSat → a.scriptPubKey = b.scriptPubKey →
        a.cltvExpiry ≤ b.cltvExpiry) ∧
    (tx.toLocalOutput = none ↔ tx.commitment.toLocalSat < tx.dustLimitSat) ∧
    (tx.toRemoteOutput = none ↔ tx.commitment.toRemoteSat < tx.dustLimitSat) ∧
    (∀ h ∈ tx.commitment.htlcs,
      tx.netAmountSat h < tx.dustLimitSat → tx.htlcOutputNet h = none) ∧
    (∀ h ∈ tx.commitment.htlcs, tx.dustLimitSat ≤ tx.netAmountSat h →
      CommitmentTxOutput.htlc h (tx.htlcScript h) ∈ tx.outputsNet) ∧
    (∀ o ∈ tx.outputsNet, o.kind ≠ .localAnchor → o.kind ≠ .remoteAnchor →
      tx.dustLimitSat ≤ o.valueSat) := by
  exact ⟨tx.outputsNet_perm, tx.outputsNet_pairwise,
    tx.outputsNet_values_sorted, tx.outputsNet_scripts_sorted,
    tx.outputsNet_cltvs_sorted, tx.toLocal_trimmed_iff,
    tx.toRemote_trimmed_iff,
    fun h _ hd => tx.htlcOutputNet_eq_none_of_dust h hd,
    fun h hm hd => tx.htlcOutputNet_mem_outputsNet h hm hd,
    fun o ho => tx.outputsNet_nonAnchor_value_ge_dust hle ho⟩

/-- The net specification phrased with the BOLT 3 gross threshold: a
net-consistent commitment trims exactly the HTLCs whose gross value is below
`dust_limit + second_stage_fee`. -/
theorem _root_.LnLean.Channel.CommitmentTx.outputsNet_trims_iff_gross_threshold (tx : CommitmentTx)
    {anchors : Bool} {r : FeeRate} (hc : NetConsistent tx anchors r)
    {h : CommitmentHTLCOutput} (hmem : h ∈ tx.commitment.htlcs) :
    tx.htlcOutputNet h = none ↔
      h.amountSat < tx.dustLimitSat + htlcSecondStageFee anchors r h :=
  htlcOutputNet_eq_none_iff_gross_threshold tx h anchors r (hc h hmem)

/-! ## 8. Retained wave-4 results and D12 refutations -/

/-- D12's unconditional ordering refutation is retained unchanged. -/
theorem d12_output_ordering_fails :
    ¬ (∀ c : Commitment,
        (c.commitmentOutputs.map CommitmentOutput.value).Pairwise (· ≤ ·)) :=
  LnLean.Proofs.WaveD.D12.waveD_d12_output_ordering_fails

/-- D12's zero-valued HTLC counterexample is retained unchanged. -/
theorem d12_zero_value_htlc_emitted :
    CommitmentOutput.htlc .local 0 ∈
      LnLean.Proofs.WaveD.D12.zeroValueHtlcCommitment.commitmentOutputs :=
  LnLean.Proofs.WaveD.D12.waveD_d12_zero_value_htlc_emitted

/-- D12's CLTV-tiebreak information-loss result is retained unchanged. -/
theorem d12_cltv_tiebreak_not_recoverable :
    LnLean.Proofs.WaveD.D12.cltvOrderLeft.htlcs ≠
        LnLean.Proofs.WaveD.D12.cltvOrderRight.htlcs ∧
      LnLean.Proofs.WaveD.D12.cltvOrderLeft.commitmentOutputs =
        LnLean.Proofs.WaveD.D12.cltvOrderRight.commitmentOutputs :=
  LnLean.Proofs.WaveD.D12.waveD_d12_cltv_tiebreak_not_recoverable

/-- The wave-4 zero-dust conditional permutation is retained: the
`dustLimitSat = 0` hypothesis is still necessary for the *unfiltered* legacy
comparison. -/
theorem wave4_dust_trimming_not_perm :
    ¬ (CommitmentIntegration.legacyOutputs
          CommitmentIntegration.dustDemoTx).Perm
        CommitmentIntegration.dustDemoTx.commitment.commitmentOutputs :=
  CommitmentIntegration.dust_trimming_not_perm

/-- The wave-4 end-to-end conditional refinement is retained verbatim: at zero
dust and zero second-stage fees, the rich net construction refines the legacy
commitment built from the same records.  This lane's
`migratedFrom_outputsNet_perm_commitmentOutputs` removes the zero-dust premise
by migrating the record instead. -/
theorem wave4_richOutputs_refine_legacyCommitment_retained
    (tx : CommitmentTx) (holder : Direction) (number funding fee toLocal
      contestDelay : Nat) (anchors : Bool) (hs : List HTLCRecord)
    (hcommit : tx.commitment =
      CommitmentIntegration.netCommitmentOfRecords holder number funding fee
        toLocal contestDelay anchors 0 0 0 hs)
    (hdust : tx.dustLimitSat = 0)
    (hl : tx.commitment.toLocalSat ≠ 0)
    (hr : tx.commitment.toRemoteSat ≠ 0) :
    (CommitmentIntegration.legacyOutputs tx).Perm
      (CommitmentIntegration.legacyCommitmentOfRecords holder number funding fee
        toLocal contestDelay anchors hs).commitmentOutputs :=
  CommitmentIntegration.richOutputs_refine_legacyCommitment tx holder number
    funding fee toLocal contestDelay anchors hs hcommit hdust hl hr

end LnLean.Proofs.Channel.CommitmentGrossNet
