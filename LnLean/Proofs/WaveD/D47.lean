import LnLean.Channel.Commitment
import LnLean.Channel.HTLC
import LnLean.Channel.Fee
import LnLean.Channel.Types
import LnLean.Proofs.Channel.CommitmentTxProps

/-!
# LnLean.Proofs.WaveD.D47

Dust HTLC trimming and fee accounting.

BOLT 3 says that a commitment transaction emits an output for an HTLC exactly
when the HTLC's value *after* deducting the second-stage (HTLC-timeout or
HTLC-success) fee is at least the broadcaster's `dust_limit_satoshis`; the
comparison is strict, so equality with the dust limit is not dust
(`refs/bolts/03-transactions.md:305-354`, especially `:330`).  The value of
every trimmed HTLC is not paid to either party: it is added to the
transaction fee (`03-transactions.md:348-353`), so the fee actually paid by a
commitment transaction is the BOLT 3 base fee plus the total trimmed HTLC
value.

The model splits this claim over three places.

* `LnLean.Channel.HTLC` provides the per-record dust test
  `isDustHTLC`/`hasOutput`, whose threshold is
  `htlcOutputValue = floor(amount_msat / 1000) - secondStageFee`.
* `LnLean.Channel.Commitment.commitmentOutputs` emits exactly the HTLCs that
  are stored in the `Commitment.htlcs` list; it performs no dust test itself
  (it trims `to_local`/`to_remote` only on `= 0`).
* `LnLean.Proofs.Channel.CommitmentTxProps` adds `Commitment.addHtlc`, which
  applies the dust threshold `dust_limit + htlc_tx_fee` when appending an
  HTLC, but leaves `feeSat` untouched.

This module proves the exactness of the trimming rule (below the threshold is
dropped, at or above the threshold is kept, equality is kept) and the value
partition it induces.  It then gives the BOLT 3 fee-accounting construction
that the model is missing: reduce the residual output by the *whole* pending
HTLC value (as BOLT 3 does with the funder's output) and emit only the
surviving HTLC outputs.  Under the
explicit no-underflow hypothesis, the emitted value plus the base fee plus the
trimmed value is exactly the funding value, i.e. the effective fee is
`feeSat + trimmedValue`.  Finally it records, with proof, why this accounting
is **not** a consequence of the current model constructors: the existing
pre-trimmed `buildCommitment` leaves the trimmed value in `to_remote` instead
of moving it to the fee, and `Commitment.feeSat` is an independent field that
is not observable from the output list.

Only BOLT 3 value arithmetic is modelled; output ordering is the sibling
obligation D48.  Every claim below is fully proved.
-/

namespace LnLean.Proofs.WaveD.D47

open LnLean
open LnLean.Channel

set_option autoImplicit false

-- OBLIGATION: LN-WD-D47

/-! ## The dust threshold -/

/-- The commitment-output value that the BOLT 3 dust test compares with the
dust limit: the whole-satoshi HTLC amount, not reduced by the second-stage
fee.  This is the amount that an emitted HTLC output carries. -/
def waveD_d47_dustThreshold (h : CommitmentHTLCOutput) (dustLimitSat
    timeoutFeeSat successFeeSat : Nat) : Nat :=
  dustLimitSat + secondStageFee h.direction timeoutFeeSat successFeeSat

/-- The BOLT 3 trimming predicate for an HTLC output: the HTLC is dust iff its
amount is strictly below the dust limit plus its second-stage fee.  Equality
is not dust. -/
def waveD_d47_isDustOutput (h : CommitmentHTLCOutput) (dustLimitSat
    timeoutFeeSat successFeeSat : Nat) : Bool :=
  decide (h.amountSat <
    waveD_d47_dustThreshold h dustLimitSat timeoutFeeSat successFeeSat)

/-- The threshold is the dust limit plus the direction's second-stage fee. -/
theorem waveD_d47_dustThreshold_eq (d t s : Nat) (h : CommitmentHTLCOutput) :
    waveD_d47_dustThreshold h d t s = d + secondStageFee h.direction t s := rfl

theorem waveD_d47_isDust_iff (d t s : Nat) (h : CommitmentHTLCOutput) :
    waveD_d47_isDustOutput h d t s = true ↔
      h.amountSat < d + secondStageFee h.direction t s := by
  unfold waveD_d47_isDustOutput waveD_d47_dustThreshold
  exact decide_eq_true_iff

theorem waveD_d47_not_isDust_iff (d t s : Nat) (h : CommitmentHTLCOutput) :
    waveD_d47_isDustOutput h d t s = false ↔
      d + secondStageFee h.direction t s ≤ h.amountSat := by
  constructor
  · intro hf
    have hnot : ¬ h.amountSat < d + secondStageFee h.direction t s := by
      intro hlt
      have ht := (waveD_d47_isDust_iff d t s h).mpr hlt
      rw [hf] at ht
      exact Bool.noConfusion ht
    omega
  · intro hge
    have hnot : ¬ h.amountSat < d + secondStageFee h.direction t s := by omega
    cases hb : waveD_d47_isDustOutput h d t s with
    | false => rfl
    | true => exact absurd ((waveD_d47_isDust_iff d t s h).mp hb) hnot

/-- The model's HTLC-level dust test is the same strict comparison once the
amount is rounded to satoshis.  The positivity of the dust limit is needed
only because `htlcOutputValue` uses saturating `Nat` subtraction; every
negotiated BOLT 3 dust limit is positive (default 546 for P2WPKH). -/
theorem waveD_d47_isDustHTLC_iff_threshold {h : HTLCRecord} {d t s : Nat}
    (hd : 0 < d) :
    isDustHTLC h d t s = true ↔
      Msat.toSatFloor h.amountMsat < d + secondStageFee h.direction t s := by
  rw [isDust_iff]
  unfold htlcOutputValue
  omega

/-- The HTLC-level output test, written as the threshold inequality. -/
theorem waveD_d47_hasOutput_iff_threshold {h : HTLCRecord} {d t s : Nat}
    (hd : 0 < d) :
    hasOutput h d t s = true ↔
      d + secondStageFee h.direction t s ≤ Msat.toSatFloor h.amountMsat := by
  rw [hasOutput_iff]
  unfold htlcOutputValue
  omega

/-- Equality with the threshold (amount equal to dust limit plus second-stage
fee) is kept, not trimmed. -/
theorem waveD_d47_threshold_not_dust (h : HTLCRecord) (d t s : Nat) (hd : 0 < d)
    (heq : Msat.toSatFloor h.amountMsat = d + secondStageFee h.direction t s) :
    isDustHTLC h d t s = false := by
  have hnot : ¬ Msat.toSatFloor h.amountMsat <
      d + secondStageFee h.direction t s := by omega
  cases hb : isDustHTLC h d t s with
  | false => rfl
  | true =>
      exact absurd ((waveD_d47_isDustHTLC_iff_threshold hd).mp hb) hnot

/-! ## Lifting an HTLC record to a commitment output -/

/-- The commitment-output projection of a model HTLC.  No field is invented:
the value is exactly the whole-satoshi amount used by the commitment
constructor. -/
def CommitmentHTLCOutput.ofHTLC (h : HTLCRecord) : CommitmentHTLCOutput :=
  { direction := h.direction
    amountSat := Msat.toSatFloor h.amountMsat
    cltvExpiry := h.cltvExpiry
    state := h.state }

/-- On the projection, the commitment-level dust test agrees exactly with the
HTLC model's `isDustHTLC`.  Thus `trimHtlcs` below implements precisely the
dust test of `LnLean.Channel.HTLC`. -/
theorem waveD_d47_ofHTLC_isDust_iff {h : HTLCRecord} {d t s : Nat} (hd : 0 < d) :
    waveD_d47_isDustOutput (CommitmentHTLCOutput.ofHTLC h) d t s = true ↔
      isDustHTLC h d t s = true := by
  rw [waveD_d47_isDust_iff, waveD_d47_isDustHTLC_iff_threshold hd]
  simp [CommitmentHTLCOutput.ofHTLC]

/-! ## Trimming a list of HTLC outputs -/

/-- The HTLC outputs that survive trimming, in their original order. -/
def trimHtlcs (dustLimitSat timeoutFeeSat successFeeSat : Nat)
    (hs : List CommitmentHTLCOutput) : List CommitmentHTLCOutput :=
  hs.filter (fun h => !waveD_d47_isDustOutput h dustLimitSat timeoutFeeSat
    successFeeSat)

/-- The HTLC outputs removed by trimming. -/
def dustHtlcs (dustLimitSat timeoutFeeSat successFeeSat : Nat)
    (hs : List CommitmentHTLCOutput) : List CommitmentHTLCOutput :=
  hs.filter (fun h => waveD_d47_isDustOutput h dustLimitSat timeoutFeeSat
    successFeeSat)

/-- Exactness, forward direction: an HTLC survives iff it was present and its
amount is at or above the dust threshold.  In particular no dust HTLC
survives. -/
theorem waveD_d47_mem_trimHtlcs {d t s : Nat} {hs : List CommitmentHTLCOutput}
    {h : CommitmentHTLCOutput} :
    h ∈ trimHtlcs d t s hs ↔
      h ∈ hs ∧ ¬ h.amountSat < d + secondStageFee h.direction t s := by
  unfold trimHtlcs
  rw [List.mem_filter]
  constructor
  · rintro ⟨hm, hb⟩
    refine ⟨hm, ?_⟩
    intro hlt
    have htrue : waveD_d47_isDustOutput h d t s = true :=
      (waveD_d47_isDust_iff d t s h).mpr hlt
    rw [htrue] at hb
    exact Bool.noConfusion hb
  · rintro ⟨hm, hnot⟩
    refine ⟨hm, ?_⟩
    cases hb : waveD_d47_isDustOutput h d t s with
    | false => rfl
    | true => exact absurd ((waveD_d47_isDust_iff d t s h).mp hb) hnot

/-- Exactness, dust direction: an HTLC is trimmed iff it was present and its
amount is strictly below the dust threshold. -/
theorem waveD_d47_mem_dustHtlcs {d t s : Nat} {hs : List CommitmentHTLCOutput}
    {h : CommitmentHTLCOutput} :
    h ∈ dustHtlcs d t s hs ↔
      h ∈ hs ∧ h.amountSat < d + secondStageFee h.direction t s := by
  unfold dustHtlcs
  rw [List.mem_filter]
  constructor
  · rintro ⟨hm, hb⟩
    exact ⟨hm, (waveD_d47_isDust_iff d t s h).mp hb⟩
  · rintro ⟨hm, hlt⟩
    exact ⟨hm, (waveD_d47_isDust_iff d t s h).mpr hlt⟩

/-- Every dust HTLC is absent from the trimmed list. -/
theorem waveD_d47_dust_not_mem_trim {d t s : Nat} {hs : List CommitmentHTLCOutput}
    {h : CommitmentHTLCOutput}
    (hd : h.amountSat < d + secondStageFee h.direction t s) :
    h ∉ trimHtlcs d t s hs := by
  rw [waveD_d47_mem_trimHtlcs]
  rintro ⟨_, hnot⟩
  exact hnot hd

/-- Every non-dust HTLC of the input is present in the trimmed list. -/
theorem waveD_d47_untouched_mem_trim {d t s : Nat} {hs : List CommitmentHTLCOutput}
    {h : CommitmentHTLCOutput} (hm : h ∈ hs)
    (hnd : ¬ h.amountSat < d + secondStageFee h.direction t s) :
    h ∈ trimHtlcs d t s hs :=
  (waveD_d47_mem_trimHtlcs).mpr ⟨hm, hnd⟩

/-- Trimming is idempotent. -/
theorem waveD_d47_trimHtlcs_idempotent (d t s : Nat)
    (hs : List CommitmentHTLCOutput) :
    trimHtlcs d t s (trimHtlcs d t s hs) = trimHtlcs d t s hs := by
  unfold trimHtlcs
  induction hs with
  | nil => rfl
  | cons h tl ih =>
      by_cases hlt : h.amountSat < d + secondStageFee h.direction t s <;>
        simp [waveD_d47_isDustOutput, waveD_d47_dustThreshold, hlt] at ih ⊢

/-- The lengths split exactly between survivors and trimmed outputs. -/
theorem waveD_d47_filter_length_partition (p : CommitmentHTLCOutput → Bool)
    (hs : List CommitmentHTLCOutput) :
    (hs.filter p).length + (hs.filter (fun h => !p h)).length = hs.length := by
  induction hs with
  | nil => rfl
  | cons h tl ih =>
      cases hp : p h <;> simp [hp] at ih ⊢ <;> omega

theorem waveD_d47_trimHtlcs_length_add (d t s : Nat)
    (hs : List CommitmentHTLCOutput) :
    (trimHtlcs d t s hs).length + (dustHtlcs d t s hs).length = hs.length := by
  have h := waveD_d47_filter_length_partition
    (fun h => waveD_d47_isDustOutput h d t s) hs
  unfold trimHtlcs dustHtlcs
  omega

/-- The HTLC value of the input is the sum of the surviving values and the
trimmed values.  This is the value form of the exactness of the trim. -/
theorem waveD_d47_filter_value_partition (p : CommitmentHTLCOutput → Bool)
    (hs : List CommitmentHTLCOutput) :
    htlcOutputsValue hs =
      htlcOutputsValue (hs.filter p) +
        htlcOutputsValue (hs.filter (fun h => !p h)) := by
  induction hs with
  | nil => rfl
  | cons h tl ih =>
      cases hp : p h <;>
        simp [hp, htlcOutputsValue, ih] <;> omega

theorem waveD_d47_htlcValue_partition (d t s : Nat)
    (hs : List CommitmentHTLCOutput) :
    htlcOutputsValue hs =
      htlcOutputsValue (trimHtlcs d t s hs) +
        htlcOutputsValue (dustHtlcs d t s hs) := by
  have h := waveD_d47_filter_value_partition
    (fun h => waveD_d47_isDustOutput h d t s) hs
  unfold trimHtlcs dustHtlcs
  omega

/-! ## Effective fee -/

/-- The fee actually paid by a commitment transaction: the funding value minus
the total value of the emitted outputs.  For a BOLT 3 commitment this is the
base commitment fee plus the total value of all trimmed HTLCs. -/
def effectiveFee (c : Commitment) : Nat :=
  c.fundingValueSat - c.totalOutputValue

theorem waveD_d47_effectiveFee_eq (c : Commitment) :
    effectiveFee c = c.fundingValueSat - c.totalOutputValue := rfl

/-! ## The BOLT 3 fee-accounting construction -/

/-- A commitment constructed the BOLT 3 way: the residual output
`to_remote` is reduced by the **whole** pending HTLC value (trimmed and
untrimmed alike), while only the surviving HTLCs become outputs.  The trimmed
value therefore remains unallocated and is paid as fee.  `d`, `t`, `s` are
the dust limit, the HTLC-timeout fee, and the HTLC-success fee.  (The value
identity below is independent of which side is the funder; `to_remote` is the
model's residual convention, matching `buildCommitment`.) -/
def buildCommitmentTrimmed (holder : Direction) (number funding fee toLocal : Nat)
    (hs : List CommitmentHTLCOutput) (d t s contestDelay : Nat) (anchors : Bool) :
    Commitment :=
  { holder := holder
    commitmentNumber := number
    fundingValueSat := funding
    toLocalSat := toLocal
    toRemoteSat :=
      funding - fee - toLocal - htlcOutputsValue hs - commitmentAnchorTotal anchors
    htlcs := trimHtlcs d t s hs
    feeSat := fee
    contestDelay := contestDelay
    anchorOutputs := anchors }

theorem waveD_d47_buildCommitmentTrimmed_htlcs (holder : Direction) (number funding
    fee toLocal : Nat) (hs : List CommitmentHTLCOutput) (d t s contestDelay : Nat)
    (anchors : Bool) :
    (buildCommitmentTrimmed holder number funding fee toLocal hs d t s contestDelay
      anchors).htlcs = trimHtlcs d t s hs := rfl

theorem waveD_d47_buildCommitmentTrimmed_toLocal (holder : Direction) (number funding
    fee toLocal : Nat) (hs : List CommitmentHTLCOutput) (d t s contestDelay : Nat)
    (anchors : Bool) :
    (buildCommitmentTrimmed holder number funding fee toLocal hs d t s contestDelay
      anchors).toLocalSat = toLocal := rfl

theorem waveD_d47_buildCommitmentTrimmed_fundingValue (holder : Direction)
    (number funding fee toLocal : Nat) (hs : List CommitmentHTLCOutput)
    (d t s contestDelay : Nat) (anchors : Bool) :
    (buildCommitmentTrimmed holder number funding fee toLocal hs d t s contestDelay
      anchors).fundingValueSat = funding := rfl

theorem waveD_d47_buildCommitmentTrimmed_toRemote (holder : Direction) (number funding
    fee toLocal : Nat) (hs : List CommitmentHTLCOutput) (d t s contestDelay : Nat)
    (anchors : Bool) :
    (buildCommitmentTrimmed holder number funding fee toLocal hs d t s contestDelay
        anchors).toRemoteSat =
      funding - fee - toLocal - htlcOutputsValue hs - commitmentAnchorTotal anchors := rfl

theorem waveD_d47_buildCommitmentTrimmed_htlcOutputValue (holder : Direction)
    (number funding fee toLocal : Nat) (hs : List CommitmentHTLCOutput)
    (d t s contestDelay : Nat) (anchors : Bool) :
    (buildCommitmentTrimmed holder number funding fee toLocal hs d t s contestDelay
      anchors).htlcOutputValue = htlcOutputsValue (trimHtlcs d t s hs) := rfl

theorem waveD_d47_buildCommitmentTrimmed_anchorOutputValue (holder : Direction)
    (number funding fee toLocal : Nat) (hs : List CommitmentHTLCOutput)
    (d t s contestDelay : Nat) (anchors : Bool) :
    (buildCommitmentTrimmed holder number funding fee toLocal hs d t s contestDelay
      anchors).anchorOutputValue = commitmentAnchorTotal anchors := rfl

/-- The emitted HTLC outputs of the trimmed construction are exactly the
survivors of the trim. -/
theorem waveD_d47_buildCommitmentTrimmed_htlcOutputCount (holder : Direction)
    (number funding fee toLocal : Nat) (hs : List CommitmentHTLCOutput)
    (d t s contestDelay : Nat) (anchors : Bool) :
    htlcOutputCount
        (buildCommitmentTrimmed holder number funding fee toLocal hs d t s
          contestDelay anchors).commitmentOutputs =
      (trimHtlcs d t s hs).length := by
  rw [Commitment.htlcOutputCount_commitmentOutputs]
  rfl

/-- Total emitted value of the trimmed construction, under the explicit
no-underflow condition that the base fee, the funder output, the whole
pending HTLC value and the anchors fit in the funding value. -/
theorem waveD_d47_buildCommitmentTrimmed_totalOutputValue (holder : Direction)
    (number funding fee toLocal : Nat) (hs : List CommitmentHTLCOutput)
    (d t s contestDelay : Nat) (anchors : Bool)
    (hfit : fee + toLocal + htlcOutputsValue hs +
      commitmentAnchorTotal anchors ≤ funding) :
    (buildCommitmentTrimmed holder number funding fee toLocal hs d t s contestDelay
        anchors).totalOutputValue =
      funding - fee - htlcOutputsValue (dustHtlcs d t s hs) := by
  unfold Commitment.totalOutputValue
  rw [waveD_d47_buildCommitmentTrimmed_toLocal holder number funding fee toLocal hs
        d t s contestDelay anchors,
      waveD_d47_buildCommitmentTrimmed_toRemote holder number funding fee toLocal hs
        d t s contestDelay anchors,
      waveD_d47_buildCommitmentTrimmed_htlcOutputValue holder number funding fee
        toLocal hs d t s contestDelay anchors,
      waveD_d47_buildCommitmentTrimmed_anchorOutputValue holder number funding fee
        toLocal hs d t s contestDelay anchors]
  have hpart := waveD_d47_htlcValue_partition d t s hs
  omega

/-- **Fee accounting.**  Under the no-underflow hypothesis, the fee actually
paid by the BOLT 3 construction is the base commitment fee plus the total
value of the trimmed HTLCs. -/
theorem waveD_d47_effectiveFee_buildCommitmentTrimmed (holder : Direction)
    (number funding fee toLocal : Nat) (hs : List CommitmentHTLCOutput)
    (d t s contestDelay : Nat) (anchors : Bool)
    (hfit : fee + toLocal + htlcOutputsValue hs +
      commitmentAnchorTotal anchors ≤ funding) :
    effectiveFee
        (buildCommitmentTrimmed holder number funding fee toLocal hs d t s contestDelay
          anchors) =
      fee + htlcOutputsValue (dustHtlcs d t s hs) := by
  unfold effectiveFee
  rw [waveD_d47_buildCommitmentTrimmed_fundingValue holder number funding fee
        toLocal hs d t s contestDelay anchors,
      waveD_d47_buildCommitmentTrimmed_totalOutputValue holder number funding fee
        toLocal hs d t s contestDelay anchors hfit]
  have hpart := waveD_d47_htlcValue_partition d t s hs
  omega

/-- Equivalent ledger form: emitted outputs plus the effective fee reconstruct
the funding value, where the effective fee is `fee + trimmedValue`.  This is
the "trimmed value is accounted for as fee" statement. -/
theorem waveD_d47_trimmed_value_accounted_as_fee (holder : Direction)
    (number funding fee toLocal : Nat) (hs : List CommitmentHTLCOutput)
    (d t s contestDelay : Nat) (anchors : Bool)
    (hfit : fee + toLocal + htlcOutputsValue hs +
      commitmentAnchorTotal anchors ≤ funding) :
    outputsValue
        (buildCommitmentTrimmed holder number funding fee toLocal hs d t s contestDelay
          anchors).commitmentOutputs +
        (fee + htlcOutputsValue (dustHtlcs d t s hs)) = funding := by
  rw [Commitment.outputsValue_commitmentOutputs]
  rw [waveD_d47_buildCommitmentTrimmed_totalOutputValue holder number funding fee
    toLocal hs d t s contestDelay anchors hfit]
  have hpart := waveD_d47_htlcValue_partition d t s hs
  omega

/-! ## Why the current model constructors do not prove the accounting -/

/-- The residual of the existing pre-trimmed constructor, made explicit. -/
theorem waveD_d47_buildCommitment_toRemote (holder : Direction) (number funding fee
    toLocal : Nat) (htlcs : List CommitmentHTLCOutput) (contestDelay : Nat)
    (anchors : Bool) :
    (buildCommitment holder number funding fee toLocal htlcs contestDelay
        anchors).toRemoteSat =
      funding - fee - toLocal - htlcOutputsValue htlcs -
        commitmentAnchorTotal anchors := rfl

/-- The existing pre-trimmed constructor `buildCommitment` subtracts only the
surviving HTLC values from the funder.  Its `to_remote` therefore exceeds the
BOLT 3 residual by exactly the trimmed value: the trimmed value stays with
the counterparty instead of being paid as fee. -/
theorem waveD_d47_pretrimmed_toRemote_excess (holder : Direction) (number funding
    fee toLocal : Nat) (hs : List CommitmentHTLCOutput) (d t s contestDelay : Nat)
    (anchors : Bool)
    (hfit : fee + toLocal + htlcOutputsValue hs +
      commitmentAnchorTotal anchors ≤ funding) :
    (buildCommitment holder number funding fee toLocal (trimHtlcs d t s hs)
        contestDelay anchors).toRemoteSat =
      (buildCommitmentTrimmed holder number funding fee toLocal hs d t s contestDelay
          anchors).toRemoteSat +
        htlcOutputsValue (dustHtlcs d t s hs) := by
  rw [waveD_d47_buildCommitment_toRemote,
    waveD_d47_buildCommitmentTrimmed_toRemote]
  have hpart := waveD_d47_htlcValue_partition d t s hs
  omega

/-- Consequently the existing pre-trimmed constructor satisfies
`outputs + fee = funding`; crediting the trimmed value to the fee on top of it
would over-count.  The model therefore has no theorem of the BOLT 3 form
without changing the construction (or adding a fee/effective-fee field). -/
theorem waveD_d47_pretrimmed_fee_excludes_trimmed (holder : Direction) (number
    funding fee toLocal : Nat) (hs : List CommitmentHTLCOutput) (d t s contestDelay
    : Nat) (anchors : Bool)
    (hfit : fee + toLocal + htlcOutputsValue hs +
      commitmentAnchorTotal anchors ≤ funding)
    (hdust : 0 < htlcOutputsValue (dustHtlcs d t s hs)) :
    outputsValue
        (buildCommitment holder number funding fee toLocal (trimHtlcs d t s hs)
          contestDelay anchors).commitmentOutputs +
        fee + htlcOutputsValue (dustHtlcs d t s hs) ≠ funding := by
  have hcons := buildCommitment_conservation holder number funding fee toLocal
    (trimHtlcs d t s hs) contestDelay anchors (by
      have hpart := waveD_d47_htlcValue_partition d t s hs
      omega)
  omega

/-- The model's `feeSat` is an independent record field, not a function of the
trimming decision: two commitments with the same HTLC list and the same output
list can carry different fees.  Any accounting theorem must therefore relate
`feeSat` to a separately computed trimmed value (as
`buildCommitmentTrimmed` does), rather than derive it from the outputs. -/
theorem waveD_d47_feeSat_not_determined_by_outputs :
    ∃ c c' : Commitment,
      c.commitmentOutputs = c'.commitmentOutputs ∧
        c.htlcs = c'.htlcs ∧ c.feeSat ≠ c'.feeSat := by
  refine ⟨{ holder := .local, commitmentNumber := 0, fundingValueSat := 1000
            toLocalSat := 400, toRemoteSat := 500, htlcs := [], feeSat := 0
            contestDelay := 0, anchorOutputs := false },
          { holder := .local, commitmentNumber := 0, fundingValueSat := 1000
            toLocalSat := 400, toRemoteSat := 500, htlcs := [], feeSat := 1
            contestDelay := 0, anchorOutputs := false }, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · simp

/-- The existing `Commitment.addHtlc` also drops a dust HTLC without crediting
its value to the fee: the fee field, the output list, and the total output
value are all unchanged.  This is the constructor-level form of the missing
fee-accounting step. -/
theorem waveD_d47_addHtlc_dust_fee_unchanged (c : Commitment)
    (h : CommitmentHTLCOutput) (d f : Nat)
    (hd : h.amountSat < d + f) :
    (c.addHtlc d f h).feeSat = c.feeSat ∧
      (c.addHtlc d f h).totalOutputValue = c.totalOutputValue ∧
        (c.addHtlc d f h).commitmentOutputs = c.commitmentOutputs := by
  simp [Commitment.addHtlc, hd]

end LnLean.Proofs.WaveD.D47
