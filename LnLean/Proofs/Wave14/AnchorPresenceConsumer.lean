import LnLean.Channel.Commitment

/-!
# Wave 14 — exact anchor presence and the net-dust consumer boundary

Lane `W14-ANCHOR-PRESENCE`.  This module is **additive**.  It does not change
`Commitment.commitmentOutputs`, `CommitmentTx.outputs`, `CommitmentTx.outputsNet`,
`CommitmentTx.localAnchorOutput`, `CommitmentTx.remoteAnchorOutput`, or the
catalog theorem `output_ordering`.

## What BOLT 3 requires

BOLT 3 §3 (`refs/bolts/03-transactions.md:729-731`) states that when
`option_anchors` applies:

* add `to_local_anchor` iff `to_local` exists **or** there is at least one
  untrimmed HTLC;
* add `to_remote_anchor` iff `to_remote` exists **or** there is at least one
  untrimmed HTLC.

The "untrimmed" test on the BOLT-3-exact path is the **net** (second-stage)
dust test, i.e. `dust_limit_satoshis ≤ amount - second_stage_fee`.  The legacy
rich model (`CommitmentTx.localAnchorOutput` / `CommitmentTx.remoteAnchorOutput`)
instead emits both anchors whenever the flag is on.  This module defines the
exact presence predicate/function alongside the existing definitions and
proves the single-anchor exception and a net-dust mismatch witness.

## Boundaries

* `CommitmentTx` takes the owner's dust limit and the script bytes as
  parameters; this module inherits those caller-supplied fields.  It is not a
  claim that the model derives scripts or dust limits from funding keys.
* Anchor presence here is about the **output list**.  The funder debit
  (the 660-sat conservation repair) is a separate target and is not restated.
* `zero_fee_commitments` and `shared_anchor` are not modelled.
* The exact path uses `CommitmentTx.netAmountSat` for the HTLC dust test.  A
  caller that leaves the default identity projection gets the legacy
  gross-equals-net behaviour, exactly as for `outputsNet`.
* The retained legacy counterexamples (`waveD_d12_output_ordering_fails`,
  `waveD_d12_cltv_tiebreak_not_recoverable`,
  `waveD_d12_dust_trimming_requires_filter`) and the gross/net distinction in
  `CommitmentTx.outputs` versus `CommitmentTx.outputsNet` are untouched.
-/

namespace LnLean.Proofs.Wave14.AnchorPresenceConsumer

open LnLean
open LnLean.Channel

/-! ## Exact anchor presence -/

/-- At least one HTLC survives the BOLT 3 **net** (second-stage) dust test.
This is the "there are untrimmed HTLCs" side condition of the anchor rule. -/
def hasUntrimmedHtlcNet (tx : CommitmentTx) : Prop :=
  ∃ h ∈ tx.commitment.htlcs, tx.dustLimitSat ≤ tx.netAmountSat h

/-- Executable form of `hasUntrimmedHtlcNet`, used by the presence functions. -/
def hasUntrimmedHtlcNetB (tx : CommitmentTx) : Bool :=
  tx.commitment.htlcs.any (fun h => decide (tx.dustLimitSat ≤ tx.netAmountSat h))

theorem hasUntrimmedHtlcNetB_iff (tx : CommitmentTx) :
    hasUntrimmedHtlcNetB tx = true ↔ hasUntrimmedHtlcNet tx := by
  unfold hasUntrimmedHtlcNetB hasUntrimmedHtlcNet
  rw [List.any_eq_true]
  constructor
  · rintro ⟨h, hmem, hp⟩
    exact ⟨h, hmem, of_decide_eq_true hp⟩
  · rintro ⟨h, hmem, hp⟩
    exact ⟨h, hmem, decide_eq_true hp⟩

/-- BOLT 3's anchor-need predicate for one side of the commitment.  The
`local` anchor is needed when `to_local` is non-dust or an HTLC survives the
net dust test; symmetrically for `remote`. -/
def anchorNeeded (tx : CommitmentTx) : Direction → Prop
  | .local =>
      tx.dustLimitSat ≤ tx.commitment.toLocalSat ∨ hasUntrimmedHtlcNet tx
  | .remote =>
      tx.dustLimitSat ≤ tx.commitment.toRemoteSat ∨ hasUntrimmedHtlcNet tx

/-- Exact executable presence of the local anchor. -/
def localAnchorPresent (tx : CommitmentTx) : Bool :=
  tx.commitment.anchorOutputs &&
    (decide (tx.dustLimitSat ≤ tx.commitment.toLocalSat) ||
      hasUntrimmedHtlcNetB tx)

/-- Exact executable presence of the remote anchor. -/
def remoteAnchorPresent (tx : CommitmentTx) : Bool :=
  tx.commitment.anchorOutputs &&
    (decide (tx.dustLimitSat ≤ tx.commitment.toRemoteSat) ||
      hasUntrimmedHtlcNetB tx)

theorem localAnchorPresent_eq_true_iff (tx : CommitmentTx) :
    localAnchorPresent tx = true ↔
      tx.commitment.anchorOutputs = true ∧ anchorNeeded tx .local := by
  unfold localAnchorPresent anchorNeeded
  rw [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    hasUntrimmedHtlcNetB_iff]

theorem remoteAnchorPresent_eq_true_iff (tx : CommitmentTx) :
    remoteAnchorPresent tx = true ↔
      tx.commitment.anchorOutputs = true ∧ anchorNeeded tx .remote := by
  unfold remoteAnchorPresent anchorNeeded
  rw [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    hasUntrimmedHtlcNetB_iff]

/-- Exact local anchor output: emitted only when the flag is on and the local
side is non-dust or an HTLC survives the net dust test. -/
def localAnchorOutputExact (tx : CommitmentTx) : Option CommitmentTxOutput :=
  if localAnchorPresent tx then
    some (CommitmentTxOutput.localAnchor tx.localAnchorScript)
  else none

/-- Exact remote anchor output: emitted only when the flag is on and the
remote side is non-dust or an HTLC survives the net dust test. -/
def remoteAnchorOutputExact (tx : CommitmentTx) : Option CommitmentTxOutput :=
  if remoteAnchorPresent tx then
    some (CommitmentTxOutput.remoteAnchor tx.remoteAnchorScript)
  else none

theorem localAnchorOutputExact_eq_some_iff {tx : CommitmentTx}
    {o : CommitmentTxOutput} :
    localAnchorOutputExact tx = some o ↔
      localAnchorPresent tx = true ∧
        o = CommitmentTxOutput.localAnchor tx.localAnchorScript := by
  unfold localAnchorOutputExact
  cases h : localAnchorPresent tx <;> simp [eq_comm]

theorem remoteAnchorOutputExact_eq_some_iff {tx : CommitmentTx}
    {o : CommitmentTxOutput} :
    remoteAnchorOutputExact tx = some o ↔
      remoteAnchorPresent tx = true ∧
        o = CommitmentTxOutput.remoteAnchor tx.remoteAnchorScript := by
  unfold remoteAnchorOutputExact
  cases h : remoteAnchorPresent tx <;> simp [eq_comm]

theorem localAnchorOutputExact_ne_none_iff (tx : CommitmentTx) :
    localAnchorOutputExact tx ≠ none ↔ localAnchorPresent tx = true := by
  unfold localAnchorOutputExact
  cases h : localAnchorPresent tx <;> simp

theorem remoteAnchorOutputExact_ne_none_iff (tx : CommitmentTx) :
    remoteAnchorOutputExact tx ≠ none ↔ remoteAnchorPresent tx = true := by
  unfold remoteAnchorOutputExact
  cases h : remoteAnchorPresent tx <;> simp

/-- **Headline specification.**  The exact local anchor is emitted exactly
when `option_anchors` is on and `to_local` is non-dust or an HTLC survives the
net dust test; the remote anchor is emitted exactly when the flag is on and
`to_remote` is non-dust or an HTLC survives the net dust test.  When the flag
is off, neither exact anchor is emitted. -/
theorem exactAnchorPresence_spec (tx : CommitmentTx) :
    (localAnchorOutputExact tx ≠ none ↔
      tx.commitment.anchorOutputs = true ∧
        (tx.dustLimitSat ≤ tx.commitment.toLocalSat ∨
          hasUntrimmedHtlcNet tx)) ∧
    (remoteAnchorOutputExact tx ≠ none ↔
      tx.commitment.anchorOutputs = true ∧
        (tx.dustLimitSat ≤ tx.commitment.toRemoteSat ∨
          hasUntrimmedHtlcNet tx)) ∧
    (tx.commitment.anchorOutputs = false →
      localAnchorOutputExact tx = none ∧
        remoteAnchorOutputExact tx = none) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [localAnchorOutputExact_ne_none_iff, localAnchorPresent_eq_true_iff]
    rfl
  · rw [remoteAnchorOutputExact_ne_none_iff, remoteAnchorPresent_eq_true_iff]
    rfl
  · intro hflag
    have hl : localAnchorPresent tx = false := by
      unfold localAnchorPresent
      simp [hflag]
    have hr : remoteAnchorPresent tx = false := by
      unfold remoteAnchorPresent
      simp [hflag]
    constructor
    · unfold localAnchorOutputExact
      simp [hl]
    · unfold remoteAnchorOutputExact
      simp [hr]

/-- The exact path is a refinement of the legacy rich path when both sides are
non-dust: the additive definitions agree with the existing
`CommitmentTx.localAnchorOutput`/`remoteAnchorOutput` in the case where the
single-anchor exception cannot fire. -/
theorem exactAnchors_eq_legacy_of_both_needed (tx : CommitmentTx)
    (hflag : tx.commitment.anchorOutputs = true)
    (hl : tx.dustLimitSat ≤ tx.commitment.toLocalSat)
    (hr : tx.dustLimitSat ≤ tx.commitment.toRemoteSat) :
    localAnchorOutputExact tx = tx.localAnchorOutput ∧
      remoteAnchorOutputExact tx = tx.remoteAnchorOutput := by
  have hlp : localAnchorPresent tx = true := by
    rw [localAnchorPresent_eq_true_iff]
    exact ⟨hflag, Or.inl hl⟩
  have hrp : remoteAnchorPresent tx = true := by
    rw [remoteAnchorPresent_eq_true_iff]
    exact ⟨hflag, Or.inl hr⟩
  constructor
  · unfold localAnchorOutputExact CommitmentTx.localAnchorOutput
    simp [hlp, hflag]
  · unfold remoteAnchorOutputExact CommitmentTx.remoteAnchorOutput
    simp [hrp, hflag]

/-! ## Additive exact output list -/

/-- The pre-sort output list with exact anchor presence.  It is the exact
counterpart of `CommitmentTx.outputsUnsortedNet`; the non-anchor and HTLC
parts are unchanged. -/
def outputsUnsortedExact (tx : CommitmentTx) : List CommitmentTxOutput :=
  tx.toLocalOutput.toList ++
    (tx.toRemoteOutput.toList ++
      (tx.commitment.htlcs.filterMap tx.htlcOutputNet ++
        (localAnchorOutputExact tx).toList ++
          (remoteAnchorOutputExact tx).toList))

/-- The BOLT 3-sorted output list with exact anchor presence. -/
def outputsExact (tx : CommitmentTx) : List CommitmentTxOutput :=
  sortOutputs (outputsUnsortedExact tx)

theorem outputsExact_perm (tx : CommitmentTx) :
    (outputsExact tx).Perm (outputsUnsortedExact tx) :=
  sortOutputs_perm _

/-! ## Concrete non-vacuity witnesses -/

/-- A tiny script used by the witnesses. -/
def witnessScript (tag : UInt8) : ScriptPubKey :=
  ⟨[tag]⟩

/-- The single-anchor witness: `to_local = 0`, `to_remote = 50 000`, no HTLCs,
dust limit 330, `option_anchors` on.  BOLT 3 emits only the remote anchor. -/
def singleAnchorTx : CommitmentTx :=
  { commitment :=
      { holder := .local
        commitmentNumber := 0
        fundingValueSat := 50_330
        toLocalSat := 0
        toRemoteSat := 50_000
        htlcs := []
        feeSat := 0
        contestDelay := 144
        anchorOutputs := true }
    dustLimitSat := 330
    toLocalScript := witnessScript 1
    toRemoteScript := witnessScript 2
    localAnchorScript := witnessScript 3
    remoteAnchorScript := witnessScript 4
    htlcScript := fun _ => witnessScript 5 }

/-- Predicate used only to count anchors in the witness lists. -/
def isAnchorOutput : CommitmentTxOutput → Bool
  | ⟨.localAnchor, _, _, _⟩ => true
  | ⟨.remoteAnchor, _, _, _⟩ => true
  | _ => false

theorem singleAnchor_local_not_needed : ¬ anchorNeeded singleAnchorTx .local := by
  simp [anchorNeeded, hasUntrimmedHtlcNet, singleAnchorTx]

theorem singleAnchor_remote_needed : anchorNeeded singleAnchorTx .remote := by
  simp [anchorNeeded, hasUntrimmedHtlcNet, singleAnchorTx]

theorem singleAnchor_local_absent :
    localAnchorOutputExact singleAnchorTx = none := by
  decide

theorem singleAnchor_remote_present :
    remoteAnchorOutputExact singleAnchorTx =
      some (CommitmentTxOutput.remoteAnchor singleAnchorTx.remoteAnchorScript) := by
  decide

theorem singleAnchor_legacy_two_anchors :
    (singleAnchorTx.outputsUnsorted.filter isAnchorOutput).length = 2 := by
  decide

theorem singleAnchor_exact_one_anchor :
    (outputsUnsortedExact singleAnchorTx |>.filter isAnchorOutput).length = 1 := by
  decide

theorem singleAnchor_exact_value :
    ((outputsUnsortedExact singleAnchorTx).map (fun o => o.valueSat)).sum = 50_330 := by
  decide

theorem singleAnchor_legacy_value :
    (singleAnchorTx.outputsUnsorted.map (fun o => o.valueSat)).sum = 50_660 := by
  decide

/-- **Headline single-anchor case.**  With one non-dust side and no HTLCs, the
exact path emits exactly one 330-sat anchor while the legacy rich path emits
both, for a 330-sat difference in gross output value. -/
theorem singleAnchor_case :
    singleAnchorTx.commitment.anchorOutputs = true ∧
      singleAnchorTx.commitment.toLocalSat = 0 ∧
      singleAnchorTx.commitment.htlcs = [] ∧
      singleAnchorTx.dustLimitSat = 330 ∧
      localAnchorOutputExact singleAnchorTx = none ∧
      remoteAnchorOutputExact singleAnchorTx =
        some (CommitmentTxOutput.remoteAnchor singleAnchorTx.remoteAnchorScript) ∧
      (outputsUnsortedExact singleAnchorTx |>.filter isAnchorOutput).length = 1 ∧
      (singleAnchorTx.outputsUnsorted.filter isAnchorOutput).length = 2 ∧
      ((outputsUnsortedExact singleAnchorTx).map (fun o => o.valueSat)).sum = 50_330 ∧
      (singleAnchorTx.outputsUnsorted.map (fun o => o.valueSat)).sum = 50_660 := by
  exact ⟨rfl, rfl, rfl, rfl, singleAnchor_local_absent,
    singleAnchor_remote_present, singleAnchor_exact_one_anchor,
    singleAnchor_legacy_two_anchors, singleAnchor_exact_value,
    singleAnchor_legacy_value⟩

/-! ## Net-dust mismatch witness -/

/-- Gross value of the witness HTLC. -/
def netDustGross : Nat := 1000

/-- Second-stage fee withheld by the HTLC-timeout/success transaction. -/
def netDustSecondStageFee : Nat := 167

/-- Net value used by BOLT 3's commitment dust test. -/
def netDustNet : Nat := netDustGross - netDustSecondStageFee

/-- The owner's dust limit. -/
def netDustLimit : Nat := 900

theorem netDustNet_eq : netDustNet = 833 := by
  decide

theorem netDustNet_lt_limit : netDustNet < netDustLimit := by
  decide

theorem netDustGross_ge_limit : netDustLimit ≤ netDustGross := by
  decide

/-- The witness HTLC: gross 1000, net 833 (`1000 - 167`). -/
def netDustHtlc : CommitmentHTLCOutput :=
  { direction := .local
    amountSat := netDustGross
    cltvExpiry := 500
    state := .offered
    netAmountSat := netDustNet }

/-- A transaction carrying only the witness HTLC, no anchors, dust limit 900. -/
def netDustTx : CommitmentTx :=
  { commitment :=
      { holder := .local
        commitmentNumber := 0
        fundingValueSat := 1000
        toLocalSat := 0
        toRemoteSat := 0
        htlcs := [netDustHtlc]
        feeSat := 0
        contestDelay := 144
        anchorOutputs := false }
    dustLimitSat := netDustLimit
    toLocalScript := witnessScript 1
    toRemoteScript := witnessScript 2
    localAnchorScript := witnessScript 3
    remoteAnchorScript := witnessScript 4
    htlcScript := fun _ => witnessScript 5 }

theorem netDust_gross_keeps :
    netDustTx.htlcOutput netDustHtlc =
      some (CommitmentTxOutput.htlc netDustHtlc
        (netDustTx.htlcScript netDustHtlc)) :=
  (CommitmentTx.mem_htlcOutput_iff).2 ⟨by decide, rfl⟩

theorem netDust_net_trims :
    netDustTx.htlcOutputNet netDustHtlc = none :=
  CommitmentTx.htlcOutputNet_eq_none_of_dust netDustTx netDustHtlc (by decide)

theorem netDust_gross_consumer_keeps :
    CommitmentTxOutput.htlc netDustHtlc
        (netDustTx.htlcScript netDustHtlc) ∈ netDustTx.outputs := by
  apply CommitmentTx.htlcOutput_mem_outputs
  · simp [netDustTx]
  · decide

theorem netDust_net_consumer_trims :
    CommitmentTxOutput.htlc netDustHtlc
        (netDustTx.htlcScript netDustHtlc) ∉ netDustTx.outputsNet := by
  rw [CommitmentTx.mem_outputsNet_iff, CommitmentTx.mem_outputsUnsortedNet_iff]
  simp [CommitmentTx.toLocalOutput,
    CommitmentTx.toRemoteOutput, CommitmentTx.htlcOutputNet,
    CommitmentTx.localAnchorOutput, CommitmentTx.remoteAnchorOutput,
    netDustTx, netDustHtlc, netDustNet, netDustGross, netDustLimit,
    netDustSecondStageFee]

/-- **Headline net-dust mismatch.**  With gross 1000, second-stage fee 167,
and dust limit 900, the legacy gross consumer (`CommitmentTx.htlcOutput` /
`CommitmentTx.outputs`) keeps the output, while the exact net path
(`CommitmentTx.htlcOutputNet` / `CommitmentTx.outputsNet`) trims it.  The
statement uses the existing definitions; it does not redefine
`output_ordering` or `outputsNet`. -/
theorem netDust_mismatch :
    netDustGross = 1000 ∧
      netDustSecondStageFee = 167 ∧
      netDustLimit = 900 ∧
      netDustNet = 833 ∧
      netDustTx.htlcOutput netDustHtlc ≠ none ∧
      netDustTx.htlcOutputNet netDustHtlc = none ∧
      CommitmentTxOutput.htlc netDustHtlc
          (netDustTx.htlcScript netDustHtlc) ∈ netDustTx.outputs ∧
      CommitmentTxOutput.htlc netDustHtlc
          (netDustTx.htlcScript netDustHtlc) ∉ netDustTx.outputsNet := by
  refine ⟨rfl, rfl, rfl, netDustNet_eq, ?_, netDust_net_trims,
    netDust_gross_consumer_keeps, netDust_net_consumer_trims⟩
  rw [netDust_gross_keeps]
  exact Option.some_ne_none _

end LnLean.Proofs.Wave14.AnchorPresenceConsumer

/-! ## Axiom audit -/

#print axioms LnLean.Proofs.Wave14.AnchorPresenceConsumer.exactAnchorPresence_spec
#print axioms LnLean.Proofs.Wave14.AnchorPresenceConsumer.singleAnchor_case
#print axioms LnLean.Proofs.Wave14.AnchorPresenceConsumer.netDust_mismatch
#print axioms LnLean.Proofs.Wave14.AnchorPresenceConsumer.exactAnchors_eq_legacy_of_both_needed
