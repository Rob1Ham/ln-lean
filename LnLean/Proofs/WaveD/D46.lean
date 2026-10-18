import LnLean.Channel.Commitment
import LnLean.Channel.Fee
import LnLean.Channel.HTLC
import LnLean.Channel.Types
import LnLean.Channel.Laws

/-!
# LnLean.Proofs.WaveD.D46 — commitment output sum bound

English claim (catalog `LN-CH-002`).  The sum of the values of the outputs of a
commitment transaction is at most the channel's funding value.  Equivalently,
a commitment cannot pay out more than it holds: every satoshi leaving the
funding output is either an emitted output or the commitment fee.

The model (`LnLean.Channel.Commitment`) stores `fundingValueSat` as an ordinary
record field, so the bare statement `c.totalOutputValue ≤ c.fundingValueSat`
is *not* true for an arbitrary `Commitment` value: nothing forces the record's
fields to be consistent.  The faithful unconditional statements therefore come
in two forms, both proved here without `sorry`:

* a general budget form (`c.feeSat + c.totalOutputValue ≤ c.fundingValueSat`,
  which BOLT 3's balance equation supplies) implies the output bound;
* for the two constructors that actually implement the BOLT 3 balance
  equation, `settledCommitment` (with HTLCs) and `zeroHtlcCommitment`, the
  bound follows from the explicit fee/trim affordability hypothesis
  `fee + toLocal + htlcValue + anchors ≤ funding`.

The remaining arithmetic is isolated into reusable lemmas:

* `waveD_d46_emittedValue_eq_total`: the sum over the *emitted* output list
  `commitmentOutputs` (which omits zero-valued `to_local`/`to_remote`) equals
  `totalOutputValue`, so the bound is about real outputs and not about a
  bookkeeping total;
* `waveD_d46_dustTrim_total_le`: BOLT 3 dust trimming (zeroing a
  below-dust `to_local`/`to_remote`, filtering below-dust HTLC outputs)
  can only decrease the output sum, hence preserves the bound;
* `waveD_d46_settled_output_eq_residual`: under the affordability hypothesis
  the emitted value is exactly `funding - fee`, which is the tight form of
  the bound.

Two checked counterexamples document why the hypotheses cannot be dropped:
an arbitrary inconsistent `Commitment` record, and the anchor-blind
`commitmentPairOfBalances` builder with `option_anchors` enabled and a zero
fee (the known Wave-A gap recorded in `LnLean.Proofs.Conservation`).

BOLT sections.
* BOLT 3 §2 `Commitment Transaction Outputs`
  (`refs/bolts/03-transactions.md:102-307`): `to_local`, `to_remote`, HTLC
  outputs, and the two 330-sat anchor outputs.
* BOLT 3 §2 `Trimmed Outputs` (`:308-367`): below-dust outputs are not
  emitted; their value stays with the funder.
* BOLT 3 §4 `Fees` (`:464-576`): the commitment fee is
  `feerate_per_kw * weight / 1000`, rounded down, and is paid out of the
  funder's output.

What is NOT modelled here.
* The feerate/weight computation itself (`commitmentFee` and
  `feeForWeight` are used, but this module only consumes the resulting
  `feeSat`).
* Output ordering, scripts, signatures, witnesses, and the exact Bitcoin
  consensus rules.
* The second-stage HTLC transactions; an HTLC output is already a
  `CommitmentHTLCOutput` with its value settled.
-/

namespace LnLean.Proofs.WaveD.D46

open LnLean
open LnLean.Channel

set_option autoImplicit false

-- OBLIGATION: LN-WD-D46

/-! ## The emitted output list and its value -/

/-- Sum of the values of the outputs actually emitted by
`Commitment.commitmentOutputs`, i.e. after zero-valued `to_local`/`to_remote`
outputs have been omitted by BOLT 3 trimming. -/
def waveD_d46_emittedValue (c : Commitment) : Nat :=
  ((Commitment.commitmentOutputs c).map CommitmentOutput.value).sum

/-- A commitment respects the fee budget when its fee plus the sum of all its
output values fits inside the funding value.  This is exactly the BOLT 3
balance equation written as an inequality (equality for a conserving
commitment). -/
def waveD_d46_OutputBudget (c : Commitment) : Prop :=
  c.feeSat + c.totalOutputValue ≤ c.fundingValueSat

/-! ## Elementary list arithmetic -/

private theorem waveD_d46_sum_map_append (xs ys : List CommitmentOutput) :
    ((xs ++ ys).map CommitmentOutput.value).sum =
      (xs.map CommitmentOutput.value).sum +
        (ys.map CommitmentOutput.value).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.cons_append, List.map_cons, List.sum_cons, ih]
      omega

private theorem waveD_d46_sum_map_toLocal (v : Nat) :
    (([CommitmentOutput.toLocal v]).map CommitmentOutput.value).sum = v := by
  simp [CommitmentOutput.value]

private theorem waveD_d46_sum_map_toRemote (v : Nat) :
    (([CommitmentOutput.toRemote v]).map CommitmentOutput.value).sum = v := by
  simp [CommitmentOutput.value]

private theorem waveD_d46_sum_map_htlc (hs : List CommitmentHTLCOutput) :
    ((hs.map (fun h => CommitmentOutput.htlc h.direction h.amountSat)).map
        CommitmentOutput.value).sum = htlcOutputsValue hs := by
  induction hs with
  | nil => rfl
  | cons h t ih =>
      simp only [List.map_cons, List.sum_cons, htlcOutputsValue,
        CommitmentOutput.value]
      rw [ih]

private theorem waveD_d46_sum_map_anchors (anchors : Bool) :
    (((if anchors then
          [CommitmentOutput.localAnchor, CommitmentOutput.remoteAnchor]
        else [])).map CommitmentOutput.value).sum =
      (if anchors then 2 * anchorOutputSat else 0) := by
  cases anchors <;> simp [CommitmentOutput.value, anchorOutputSat]

/-! ## The emitted sum is the total output value -/

/-- **Trimming does not change the ledger.**  Omitting a zero-valued
`to_local`/`to_remote` from `commitmentOutputs` removes exactly zero from the
sum, so the sum over the emitted output list equals `totalOutputValue` (which
counts all four output groups as stored in the record). -/
theorem waveD_d46_emittedValue_eq_total (c : Commitment) :
    waveD_d46_emittedValue c = c.totalOutputValue := by
  unfold waveD_d46_emittedValue Commitment.commitmentOutputs
    Commitment.totalOutputValue Commitment.htlcOutputValue
    Commitment.anchorOutputValue
  rw [waveD_d46_sum_map_append, waveD_d46_sum_map_append,
    waveD_d46_sum_map_append]
  rw [waveD_d46_sum_map_htlc, waveD_d46_sum_map_anchors]
  by_cases hL : c.toLocalSat = 0 <;>
    by_cases hR : c.toRemoteSat = 0 <;>
    simp [hL, hR, CommitmentOutput.value] <;>
    omega

/-- The same identity written out group by group: the emitted output list
carries exactly the value of the four groups stored in the record. -/
theorem waveD_d46_emittedValue_eq_groups (c : Commitment) :
    waveD_d46_emittedValue c = c.toLocalSat + c.toRemoteSat +
      c.htlcOutputValue + c.anchorOutputValue := by
  rw [waveD_d46_emittedValue_eq_total]
  rfl

/-! ## The general budget form -/

/-- **Output sum bound from the fee budget.**  If the fee plus all output
values is at most the funding value, then the output sum alone is at most the
funding value.  The fee is a natural number, so no value is created. -/
theorem waveD_d46_output_le_funding_of_budget (c : Commitment)
    (h : waveD_d46_OutputBudget c) :
    c.totalOutputValue ≤ c.fundingValueSat := by
  unfold waveD_d46_OutputBudget at h
  omega

/-- Emitted-output form of `waveD_d46_output_le_funding_of_budget`: the sum
of the values of the outputs actually in the transaction is bounded by the
funding value. -/
theorem waveD_d46_emitted_le_funding_of_budget (c : Commitment)
    (h : waveD_d46_OutputBudget c) :
    waveD_d46_emittedValue c ≤ c.fundingValueSat := by
  rw [waveD_d46_emittedValue_eq_total]
  exact waveD_d46_output_le_funding_of_budget c h

/-! ## The BOLT 3 balance equation for `settledCommitment` -/

/-- **Exact residual.**  For a commitment built by `settledCommitment` — whose
`to_remote` is the remainder after `to_local`, the fee, the untrimmed HTLC
outputs, and the anchors — the affordability hypothesis makes the saturating
subtractions exact, and the output sum is exactly `funding - fee`. -/
theorem waveD_d46_settled_output_eq_residual
    (holder : Direction) (number funding toLocal fee contestDelay : Nat)
    (htlcs : List CommitmentHTLCOutput) (anchors : Bool)
    (h : fee + toLocal + htlcOutputsValue htlcs +
        (if anchors then 2 * anchorOutputSat else 0) ≤ funding) :
    (settledCommitment holder number funding toLocal fee contestDelay htlcs
        anchors).totalOutputValue = funding - fee := by
  have hcons := conservation_with_htlcs holder number funding toLocal fee
    contestDelay htlcs anchors h
  omega

/-- **The output sum of a settled commitment is at most its funding value.**
This is the main positive result of the module: BOLT 3 deducts the fee first,
so the four output groups left over cannot exceed what the channel funded. -/
theorem waveD_d46_settled_output_bound
    (holder : Direction) (number funding toLocal fee contestDelay : Nat)
    (htlcs : List CommitmentHTLCOutput) (anchors : Bool)
    (h : fee + toLocal + htlcOutputsValue htlcs +
        (if anchors then 2 * anchorOutputSat else 0) ≤ funding) :
    (settledCommitment holder number funding toLocal fee contestDelay htlcs
        anchors).totalOutputValue ≤ funding := by
  have hcons := conservation_with_htlcs holder number funding toLocal fee
    contestDelay htlcs anchors h
  omega

/-- The bound for the outputs actually emitted by a settled commitment. -/
theorem waveD_d46_settled_emitted_bound
    (holder : Direction) (number funding toLocal fee contestDelay : Nat)
    (htlcs : List CommitmentHTLCOutput) (anchors : Bool)
    (h : fee + toLocal + htlcOutputsValue htlcs +
        (if anchors then 2 * anchorOutputSat else 0) ≤ funding) :
    waveD_d46_emittedValue
        (settledCommitment holder number funding toLocal fee contestDelay
          htlcs anchors) ≤ funding := by
  rw [waveD_d46_emittedValue_eq_total]
  exact waveD_d46_settled_output_bound holder number funding toLocal fee
    contestDelay htlcs anchors h

/-- The settled commitment satisfies the fee budget (with equality), so the
general budget theorem applies to it as well. -/
theorem waveD_d46_settled_budget
    (holder : Direction) (number funding toLocal fee contestDelay : Nat)
    (htlcs : List CommitmentHTLCOutput) (anchors : Bool)
    (h : fee + toLocal + htlcOutputsValue htlcs +
        (if anchors then 2 * anchorOutputSat else 0) ≤ funding) :
    waveD_d46_OutputBudget
      (settledCommitment holder number funding toLocal fee contestDelay
        htlcs anchors) := by
  unfold waveD_d46_OutputBudget
  have hcons := conservation_with_htlcs holder number funding toLocal fee
    contestDelay htlcs anchors h
  have hfund : (settledCommitment holder number funding toLocal fee contestDelay
      htlcs anchors).fundingValueSat = funding := rfl
  rw [hfund]
  change fee + (settledCommitment holder number funding toLocal fee contestDelay
    htlcs anchors).totalOutputValue ≤ funding
  omega

/-- The zero-HTLC commitment (the opening commitment and a quiet channel's
commitment) has emitted value at most the funding value. -/
theorem waveD_d46_zeroHtlc_emitted_bound
    (holder : Direction) (number funding toLocal fee contestDelay : Nat)
    (anchors : Bool)
    (h : fee + toLocal +
        (if anchors then 2 * anchorOutputSat else 0) ≤ funding) :
    waveD_d46_emittedValue
        (zeroHtlcCommitment holder number funding toLocal fee contestDelay
          anchors) ≤ funding := by
  have hbase := waveD_d46_settled_emitted_bound holder number funding toLocal
    fee contestDelay [] anchors (by simpa [htlcOutputsValue] using h)
  simpa [zeroHtlcCommitment, settledCommitment, htlcOutputsValue] using hbase

/-! ## Dust trimming cannot increase the output sum -/

/-- HTLC dust trimming never increases the HTLC output value: filtering out
some HTLC outputs from a list can only lower the sum of their values. -/
private theorem waveD_d46_htlcOutputsValue_filter_le
    (p : CommitmentHTLCOutput → Bool) :
    ∀ hs : List CommitmentHTLCOutput,
      htlcOutputsValue (hs.filter p) ≤ htlcOutputsValue hs
  | [] => by simp [htlcOutputsValue]
  | h :: t => by
      have ih := waveD_d46_htlcOutputsValue_filter_le p t
      cases hp : p h <;> simp [List.filter, hp, htlcOutputsValue] <;> omega

/-- BOLT 3 dust trimming applied to every value-bearing output: a below-dust
`to_local`/`to_remote` becomes a zero-valued (hence omitted) output, and
below-dust HTLC outputs are removed from the list.  In BOLT 3 the trimmed
value is retained by the funder and effectively becomes fee; the model only
needs that it is not paid out, so the output sum cannot grow. -/
def waveD_d46_applyDustTrim (dustLimitSat : Nat) (c : Commitment) :
    Commitment :=
  { c with
    toLocalSat := if c.toLocalSat < dustLimitSat then 0 else c.toLocalSat
    toRemoteSat := if c.toRemoteSat < dustLimitSat then 0 else c.toRemoteSat
    htlcs := c.htlcs.filter (fun h => decide (dustLimitSat ≤ h.amountSat)) }

private theorem waveD_d46_dustTrim_toLocal_le (dustLimitSat : Nat)
    (c : Commitment) :
    (waveD_d46_applyDustTrim dustLimitSat c).toLocalSat ≤ c.toLocalSat := by
  simp only [waveD_d46_applyDustTrim]
  split <;> omega

private theorem waveD_d46_dustTrim_toRemote_le (dustLimitSat : Nat)
    (c : Commitment) :
    (waveD_d46_applyDustTrim dustLimitSat c).toRemoteSat ≤ c.toRemoteSat := by
  simp only [waveD_d46_applyDustTrim]
  split <;> omega

private theorem waveD_d46_dustTrim_htlcValue_le (dustLimitSat : Nat)
    (c : Commitment) :
    (waveD_d46_applyDustTrim dustLimitSat c).htlcOutputValue ≤
      c.htlcOutputValue := by
  simp only [waveD_d46_applyDustTrim, Commitment.htlcOutputValue]
  exact waveD_d46_htlcOutputsValue_filter_le
    (fun h => decide (dustLimitSat ≤ h.amountSat)) c.htlcs

private theorem waveD_d46_dustTrim_anchorValue (dustLimitSat : Nat)
    (c : Commitment) :
    (waveD_d46_applyDustTrim dustLimitSat c).anchorOutputValue =
      c.anchorOutputValue := by
  simp only [waveD_d46_applyDustTrim, Commitment.anchorOutputValue]
  rfl

/-- **Trimming lowers the output sum.**  Applying `waveD_d46_applyDustTrim`
cannot increase `totalOutputValue`, whichever outputs fall below the dust
limit. -/
theorem waveD_d46_dustTrim_total_le (dustLimitSat : Nat) (c : Commitment) :
    (waveD_d46_applyDustTrim dustLimitSat c).totalOutputValue ≤
      c.totalOutputValue := by
  have hL := waveD_d46_dustTrim_toLocal_le dustLimitSat c
  have hR := waveD_d46_dustTrim_toRemote_le dustLimitSat c
  have hH := waveD_d46_dustTrim_htlcValue_le dustLimitSat c
  have hA := waveD_d46_dustTrim_anchorValue dustLimitSat c
  unfold Commitment.totalOutputValue
  omega

/-- **Trimming preserves the funding bound.**  If a commitment's output sum
fits inside its funding value, so does the output sum of its dust-trimmed
version. -/
theorem waveD_d46_dustTrim_output_bound (dustLimitSat : Nat)
    (c : Commitment) (h : c.totalOutputValue ≤ c.fundingValueSat) :
    (waveD_d46_applyDustTrim dustLimitSat c).totalOutputValue ≤
      (waveD_d46_applyDustTrim dustLimitSat c).fundingValueSat := by
  have hle := waveD_d46_dustTrim_total_le dustLimitSat c
  simp only [waveD_d46_applyDustTrim] at hle ⊢
  omega

/-- Emitted-output form of the trimming bound. -/
theorem waveD_d46_dustTrim_emitted_bound (dustLimitSat : Nat)
    (c : Commitment) (h : c.totalOutputValue ≤ c.fundingValueSat) :
    waveD_d46_emittedValue (waveD_d46_applyDustTrim dustLimitSat c) ≤
      (waveD_d46_applyDustTrim dustLimitSat c).fundingValueSat := by
  rw [waveD_d46_emittedValue_eq_total]
  exact waveD_d46_dustTrim_output_bound dustLimitSat c h

/-- **Trim after construction.**  Constructing the BOLT 3 balance equation
and then applying dust trimming still leaves the emitted outputs within the
funding value.  This is the combined fee/trim arithmetic: the fee is removed
first, then trimmed outputs are dropped, and neither step creates value. -/
theorem waveD_d46_settled_dustTrim_emitted_bound
    (holder : Direction) (number funding toLocal fee contestDelay dustLimit
      : Nat) (htlcs : List CommitmentHTLCOutput) (anchors : Bool)
    (h : fee + toLocal + htlcOutputsValue htlcs +
        (if anchors then 2 * anchorOutputSat else 0) ≤ funding) :
    waveD_d46_emittedValue
        (waveD_d46_applyDustTrim dustLimit
          (settledCommitment holder number funding toLocal fee contestDelay
            htlcs anchors)) ≤ funding := by
  rw [waveD_d46_emittedValue_eq_total]
  have hbase : (settledCommitment holder number funding toLocal fee
      contestDelay htlcs anchors).totalOutputValue ≤ funding :=
    waveD_d46_settled_output_bound holder number funding toLocal fee
      contestDelay htlcs anchors h
  have htrim := waveD_d46_dustTrim_output_bound dustLimit
    (settledCommitment holder number funding toLocal fee contestDelay htlcs
      anchors) (by simpa [settledCommitment] using hbase)
  simpa [waveD_d46_applyDustTrim, settledCommitment] using htrim

/-! ## Both commitments of a channel (anchor-free case) -/

/-- **Both commitment transactions stay within the funding value.**  With
`option_anchors` disabled, `commitmentPairOfBalances` places the balances in
the two outputs (minus the funder's fee, a saturating subtraction) and emits
no anchors, so each commitment's output sum is at most the funding value.
No affordability hypothesis is needed: truncating the funder's output can
only lower the sum. -/
theorem waveD_d46_pair_output_bound
    (localParams remoteParams : ChannelParams) (b : Balance) (fee number : Nat)
    (funder : Direction)
    (hLocalAnchors : localParams.anchorOutputs = false)
    (hRemoteAnchors : remoteParams.anchorOutputs = false) :
    (commitmentPairOfBalances localParams remoteParams b fee number
        funder).localCommitment.totalOutputValue ≤
        b.localSat + b.remoteSat ∧
      (commitmentPairOfBalances localParams remoteParams b fee number
        funder).remoteCommitment.totalOutputValue ≤
        b.localSat + b.remoteSat := by
  cases funder <;>
    simp [commitmentPairOfBalances, Commitment.totalOutputValue,
      Commitment.htlcOutputValue, Commitment.anchorOutputValue,
      htlcOutputsValue, hLocalAnchors, hRemoteAnchors] <;>
    omega

/-! ## Counterexamples: the hypotheses are not removable -/

/-- An inconsistent commitment record: 500 satoshis of `to_local` funded by a
100-satoshi funding output, no fee.  The model does not tie `fundingValueSat`
to the output fields, so the bare output-sum inequality is false. -/
def waveD_d46_overfundedCommitment : Commitment :=
  { holder := Direction.local
    commitmentNumber := 0
    fundingValueSat := 100
    toLocalSat := 500
    toRemoteSat := 0
    htlcs := []
    feeSat := 0
    contestDelay := 0
    anchorOutputs := false }

/-- **Unconditional form is false.**  There is a `Commitment` whose output sum
exceeds its funding value, so any theorem of the shape
`∀ c, c.totalOutputValue ≤ c.fundingValueSat` would be unsound.  The budget
(or an explicit construction such as `settledCommitment`) is necessary. -/
theorem waveD_d46_unconditional_counterexample :
    ¬ (∀ c : Commitment, c.totalOutputValue ≤ c.fundingValueSat) := by
  intro h
  have hc := h waveD_d46_overfundedCommitment
  simp [waveD_d46_overfundedCommitment, Commitment.totalOutputValue,
    Commitment.htlcOutputValue, Commitment.anchorOutputValue,
    htlcOutputsValue] at hc

/-- Demo parameters with `option_anchors` enabled. -/
def waveD_d46_anchorParams : ChannelParams :=
  { dustLimitSat := 546
    channelReserveSat := 1000
    toSelfDelay := 144
    maxHtlcValue := ⟨1000000000⟩
    htlcMinimum := ⟨1000⟩
    feerate := ⟨253⟩
    anchorOutputs := true }

/-- Demo balances for the anchor counterexample. -/
def waveD_d46_demoBalance : Balance :=
  { localBalance := Msat.ofSat 60000
    remoteBalance := Msat.ofSat 39000 }

/-- **The anchor-free hypothesis in `waveD_d46_pair_output_bound` is
necessary for this builder.**  `commitmentPairOfBalances` emits the two
330-satoshi anchor outputs when anchors are negotiated but does not debit them
from the funder, so with a zero fee the local commitment's outputs exceed the
funding value by 660 satoshis.  This is the Wave-A builder gap already
recorded in `LnLean.Proofs.Conservation`; the sum bound must not be stated
unconditionally for this constructor. -/
theorem waveD_d46_pair_anchor_counterexample :
    ¬ ((commitmentPairOfBalances waveD_d46_anchorParams waveD_d46_anchorParams
          waveD_d46_demoBalance 0 0 Direction.local).localCommitment.totalOutputValue
        ≤ waveD_d46_demoBalance.localSat + waveD_d46_demoBalance.remoteSat) := by
  decide

end LnLean.Proofs.WaveD.D46
