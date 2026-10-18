import LnLean.Channel.Commitment
import LnLean.Channel.Fee
import LnLean.Channel.HTLC
import LnLean.Channel.HTLCLaws
import LnLean.Channel.Laws
import LnLean.Channel.Penalty
import LnLean.Channel.Revocation
import LnLean.Channel.State
import LnLean.Channel.Types

/-!
# LnLean.Proofs.WaveD.D11

English claim (catalog `LN-CH-002`, BOLT 3 §Commitment Transaction Outputs,
LDK `lightning/src/ln/chan_utils.rs:1908`).  No commitment output has a
negative value and the output sum stays within the funding value.

The model is value arithmetic over `Nat`:

* `CommitmentOutput.value : CommitmentOutput → Nat` (Types.lean) makes every
  output value a natural number, so non-negativity holds by the type.  This
  is not a way of dodging the claim: the record cannot represent a negative
  output, and `commitmentOutputs` omits zero-valued `to_local`/`to_remote`
  outputs (the BOLT 3 trimming rule).
* `Commitment.totalOutputValue` is `to_local + to_remote + HTLC outputs +
  anchors`.  For an arbitrary `Commitment` record this can exceed
  `fundingValueSat`; the bound needs the BOLT 3 balance equation
  `outputs + fee = funding`, which `settledCommitment` satisfies under the
  explicit cover hypothesis below.  `waveD_d11_overspent_outputs_exceed`
  is the checked counterexample showing the hypothesis is necessary.

What this module proves:

1. every emitted commitment output is non-negative
   (`waveD_d11_output_value_nonneg`);
2. the emitted output list's value sum is exactly `totalOutputValue`
   (`waveD_d11_outputsValue_eq_total`), so the list-level sum and the record
   arithmetic agree;
3. any emitted output is at most the total output value
   (`waveD_d11_output_value_le_total`);
4. for a commitment satisfying the BOLT 3 balance equation, the emitted
   output sum is at most the funding value
   (`waveD_d11_outputs_within_funding`), and so is every single output
   (`waveD_d11_output_value_le_funding`);
5. the canonical `settledCommitment` construction satisfies the bound
   unconditionally once its cover hypothesis holds
   (`waveD_d11_settled_outputs_within_funding`,
   `waveD_d11_zeroHtlc_outputs_within_funding`);
6. a record whose `to_remote` is the BOLT 3 residual satisfies the bound
   (`waveD_d11_residual_outputs_within_funding`);
7. `commitmentPairOfBalances` with anchors disabled satisfies the bound for
   both commitments (`waveD_d11_pair_outputs_within_funding`).

Fidelity note.  `commitmentPairOfBalances` sets `anchorOutputs` from the
negotiated parameters but does not debit the two 330-satoshi anchor outputs
from the funder's balance (the same gap already recorded in
`LnLean.Proofs.Conservation`).  With anchors enabled its output sum therefore
exceeds the funding value by the anchor total when the fee does not cover it;
`waveD_d11_pair_anchor_outputs_exceed` is the checked counterexample.  This
is a limitation of the wave-A builder, not a weakening of the claim.

BOLT sections.
* BOLT 3 §2 `Commitment Transaction Outputs`
  (`refs/bolts/03-transactions.md:102-307`): `to_local`, `to_remote`,
  offered/received HTLC outputs, and the two 330-satoshi anchor outputs.
* BOLT 3 §2 `Trimmed Outputs` (`refs/bolts/03-transactions.md:305-367`):
  zero/dust outputs are not emitted.
* BOLT 3 §4 `Fees` (`refs/bolts/03-transactions.md:464-576`): the leftover
  after outputs is the fee, so outputs plus fee equal the funding value.
* LDK anchor: `lightning/src/ln/chan_utils.rs:1887-1945`
  (`insert_non_htlc_outputs`: non-zero outputs and the conditional anchors).

What is NOT modelled.
* Script bytes, witness weights, signatures, and output ordering; this is
  value arithmetic on the commitment record only.
* The single-anchor exception and the `shared_anchor` output.
* Whether a counterparty actually broadcasts the commitment.
-/

namespace LnLean.Proofs.WaveD.D11

set_option autoImplicit false

open LnLean
open LnLean.Channel

-- OBLIGATION: LN-WD-D11

/-! ## Non-negativity of every emitted output -/

/-- **No commitment output has a negative value.**  Every output emitted by
`Commitment.commitmentOutputs` has a `Nat` value.  This covers all four
constructors: `toLocal`, `toRemote`, HTLC outputs, and the two anchors. -/
theorem waveD_d11_output_value_nonneg (c : Commitment) (o : CommitmentOutput)
    (_ho : o ∈ c.commitmentOutputs) :
    0 ≤ o.value :=
  Nat.zero_le _

/-- The catalog statement at the record level: every output value is
non-negative, with no hypothesis on the commitment record (the model's value
type is `Nat`). -/
theorem waveD_d11_all_outputs_nonnegative (c : Commitment) :
    ∀ o : CommitmentOutput, o ∈ c.commitmentOutputs → 0 ≤ o.value :=
  fun o ho => waveD_d11_output_value_nonneg c o ho

/-! ## The emitted list sums to `totalOutputValue` -/

/-- **List/value agreement.**  Summing `CommitmentOutput.value` over the
emitted output list is exactly the record's `totalOutputValue`.  A zero
`to_local`/`to_remote` is omitted from the list but contributes zero, and
the anchor values are the two 330-satoshi outputs. -/
theorem waveD_d11_outputsValue_eq_total (c : Commitment) :
    (c.commitmentOutputs.map CommitmentOutput.value).sum = c.totalOutputValue := by
  by_cases hL : c.toLocalSat = 0 <;>
    by_cases hR : c.toRemoteSat = 0 <;>
    by_cases hA : c.anchorOutputs <;>
    simp [Commitment.commitmentOutputs, Commitment.totalOutputValue,
      Commitment.htlcOutputValue_eq_sum, Commitment.anchorOutputValue,
      hL, hR, hA, CommitmentOutput.value, anchorOutputSat,
      List.map_map, Function.comp_def] <;>
    omega

/-- Membership in the emitted list never exceeds the total output value. -/
private theorem value_le_sum_of_mem {l : List CommitmentOutput}
    {o : CommitmentOutput} (ho : o ∈ l) :
    o.value ≤ (l.map CommitmentOutput.value).sum := by
  induction l with
  | nil => cases ho
  | cons x xs ih =>
      rw [List.map_cons, List.sum_cons]
      rcases List.mem_cons.mp ho with rfl | hmem
      · omega
      · have := ih hmem
        omega

/-- **Every single emitted output is at most the total output value.**
Consequently, when the total is bounded by the funding value, so is each
individual output. -/
theorem waveD_d11_output_value_le_total (c : Commitment)
    (o : CommitmentOutput) (ho : o ∈ c.commitmentOutputs) :
    o.value ≤ c.totalOutputValue := by
  rw [← waveD_d11_outputsValue_eq_total]
  exact value_le_sum_of_mem ho

/-! ## The sum bound under the BOLT 3 balance equation -/

/-- **Output sum within the funding value.**  If the commitment satisfies the
BOLT 3 balance equation `outputs + fee = funding`, then the sum of the
emitted output values is at most the funding value.  This is the exact
hypothesis that an arbitrary `Commitment` record need not satisfy; see
`waveD_d11_overspent_outputs_exceed`. -/
theorem waveD_d11_outputs_within_funding (c : Commitment)
    (hcons : c.totalOutputValue + c.feeSat = c.fundingValueSat) :
    (c.commitmentOutputs.map CommitmentOutput.value).sum ≤ c.fundingValueSat := by
  rw [waveD_d11_outputsValue_eq_total]
  omega

/-- **Every single output stays within the funding value.** -/
theorem waveD_d11_output_value_le_funding (c : Commitment)
    (hcons : c.totalOutputValue + c.feeSat = c.fundingValueSat)
    (o : CommitmentOutput) (ho : o ∈ c.commitmentOutputs) :
    o.value ≤ c.fundingValueSat := by
  have h₁ := waveD_d11_output_value_le_total c o ho
  omega

/-- The catalog-level conjunction: non-negativity is unconditional, and the
sum bound is the BOLT 3 balance equation specialised to the emitted list. -/
theorem waveD_d11_outputs_nonnegative (c : Commitment) :
    (∀ o : CommitmentOutput, o ∈ c.commitmentOutputs → 0 ≤ o.value) ∧
      (c.totalOutputValue + c.feeSat = c.fundingValueSat →
        (c.commitmentOutputs.map CommitmentOutput.value).sum ≤
          c.fundingValueSat) :=
  ⟨waveD_d11_all_outputs_nonnegative c, waveD_d11_outputs_within_funding c⟩

/-! ## The canonical `settledCommitment` construction -/

/-- **Settled commitment output sum.**  Under the cover hypothesis used by
`conservation_with_htlcs` (the funding value pays the holder's output, the
fee, all untrimmed HTLC outputs, and the anchors), the emitted output sum is
exactly `funding - fee`, hence at most the funding value. -/
theorem waveD_d11_settled_outputs_eq_funding_sub_fee
    (holder : Direction) (number funding toLocal fee contestDelay : Nat)
    (htlcs : List CommitmentHTLCOutput) (anchors : Bool)
    (h : fee + toLocal + htlcOutputsValue htlcs +
        (if anchors then 2 * anchorOutputSat else 0) ≤ funding) :
    ((settledCommitment holder number funding toLocal fee contestDelay
        htlcs anchors).commitmentOutputs.map CommitmentOutput.value).sum =
      funding - fee := by
  have hcons := conservation_with_htlcs holder number funding toLocal fee
    contestDelay htlcs anchors h
  rw [waveD_d11_outputsValue_eq_total]
  omega

/-- **The canonical settled commitment stays within the funding value.** -/
theorem waveD_d11_settled_outputs_within_funding
    (holder : Direction) (number funding toLocal fee contestDelay : Nat)
    (htlcs : List CommitmentHTLCOutput) (anchors : Bool)
    (h : fee + toLocal + htlcOutputsValue htlcs +
        (if anchors then 2 * anchorOutputSat else 0) ≤ funding) :
    ((settledCommitment holder number funding toLocal fee contestDelay
        htlcs anchors).commitmentOutputs.map CommitmentOutput.value).sum ≤
      funding := by
  rw [waveD_d11_settled_outputs_eq_funding_sub_fee holder number funding
    toLocal fee contestDelay htlcs anchors h]
  exact Nat.sub_le _ _

/-- **The zero-HTLC opening commitment stays within the funding value.**  The
special case used at channel opening and after all HTLCs have settled. -/
theorem waveD_d11_zeroHtlc_outputs_within_funding
    (holder : Direction) (number funding toLocal fee contestDelay : Nat)
    (anchors : Bool)
    (h : fee + toLocal + (if anchors then 2 * anchorOutputSat else 0) ≤
      funding) :
    ((zeroHtlcCommitment holder number funding toLocal fee contestDelay
        anchors).commitmentOutputs.map CommitmentOutput.value).sum ≤
      funding := by
  rw [waveD_d11_outputsValue_eq_total]
  have hc := zeroHtlc_conservation holder number funding toLocal fee
    contestDelay anchors h
  omega

/-! ## `to_remote` as the BOLT 3 residual -/

/-- **Residual form of the bound.**  If a commitment's `to_remote` is exactly
the BOLT 3 residual `funding - fee - to_local - htlcs - anchors`, and the
funding value covers those components, then the emitted output sum stays
within the funding value.  This is the record-level counterpart of
`settledCommitment` and holds for any commitment sharing that residual. -/
theorem waveD_d11_residual_outputs_within_funding (c : Commitment)
    (hremote : c.toRemoteSat =
      c.fundingValueSat - c.feeSat - c.toLocalSat - c.htlcOutputValue -
        c.anchorOutputValue)
    (hcover : c.feeSat + c.toLocalSat + c.htlcOutputValue +
        c.anchorOutputValue ≤ c.fundingValueSat) :
    (c.commitmentOutputs.map CommitmentOutput.value).sum ≤
      c.fundingValueSat := by
  rw [waveD_d11_outputsValue_eq_total]
  unfold Commitment.totalOutputValue
  rw [hremote]
  omega

/-! ## The balance-derived commitment pair (no anchors) -/

/-- **Both commitments of a balance-derived pair stay within funding when
anchors are disabled.**  The funder's output pays the fee on each of the two
transactions, so the output sum is `funding - fee` on both. -/
theorem waveD_d11_pair_outputs_within_funding
    (localParams remoteParams : ChannelParams) (b : Balance)
    (fee number : Nat) (funder : Direction)
    (hLocalAnchors : localParams.anchorOutputs = false)
    (hRemoteAnchors : remoteParams.anchorOutputs = false)
    (hbal : fee ≤
      (if funder = Direction.local then b.localSat else b.remoteSat)) :
    ((commitmentPairOfBalances localParams remoteParams b fee number
          funder).localCommitment.commitmentOutputs.map
        CommitmentOutput.value).sum ≤
      (commitmentPairOfBalances localParams remoteParams b fee number
          funder).localCommitment.fundingValueSat ∧
    ((commitmentPairOfBalances localParams remoteParams b fee number
          funder).remoteCommitment.commitmentOutputs.map
        CommitmentOutput.value).sum ≤
      (commitmentPairOfBalances localParams remoteParams b fee number
          funder).remoteCommitment.fundingValueSat := by
  constructor <;> rw [waveD_d11_outputsValue_eq_total]
  · cases funder <;>
      (first
        | have hbal' : fee ≤ b.localSat := by
            simpa [commitmentPairOfBalances] using hbal
        | have hbal' : fee ≤ b.remoteSat := by
            simpa [commitmentPairOfBalances] using hbal) <;>
      simp [commitmentPairOfBalances, Commitment.totalOutputValue,
        Commitment.htlcOutputValue, Commitment.anchorOutputValue,
        htlcOutputsValue, hLocalAnchors] <;>
      omega
  · cases funder <;>
      (first
        | have hbal' : fee ≤ b.localSat := by
            simpa [commitmentPairOfBalances] using hbal
        | have hbal' : fee ≤ b.remoteSat := by
            simpa [commitmentPairOfBalances] using hbal) <;>
      simp [commitmentPairOfBalances, Commitment.totalOutputValue,
        Commitment.htlcOutputValue, Commitment.anchorOutputValue,
        htlcOutputsValue, hRemoteAnchors] <;>
      omega

/-! ## The balance equation is necessary: checked counterexamples -/

/-- A commitment with one satoshi of `to_local` and a zero funding value.
The model cannot force a record's fields to satisfy the BOLT 3 balance
equation, so the bound is not true for arbitrary records. -/
def waveD_d11_overspentCommitment : Commitment :=
  { holder := Direction.local
    commitmentNumber := 0
    fundingValueSat := 0
    toLocalSat := 1
    toRemoteSat := 0
    htlcs := []
    feeSat := 0
    contestDelay := 0
    anchorOutputs := false }

/-- **Checked: an arbitrary commitment can emit more than its funding
value.**  Hence `waveD_d11_outputs_within_funding`'s balance-equation
hypothesis (or a construction such as `settledCommitment`) is necessary. -/
theorem waveD_d11_overspent_outputs_exceed :
    (waveD_d11_overspentCommitment.commitmentOutputs.map
        CommitmentOutput.value).sum >
      waveD_d11_overspentCommitment.fundingValueSat := by
  decide

/-- The counterexample still satisfies non-negativity: it is only the sum
bound that fails without the balance equation. -/
theorem waveD_d11_overspent_still_nonnegative :
    ∀ o : CommitmentOutput,
      o ∈ waveD_d11_overspentCommitment.commitmentOutputs → 0 ≤ o.value :=
  waveD_d11_all_outputs_nonnegative _

/-- Demo parameters with anchors enabled. -/
def waveD_d11_anchorParams : ChannelParams :=
  { dustLimitSat := 546
    channelReserveSat := 1000
    toSelfDelay := 144
    maxHtlcValue := ⟨1000000000⟩
    htlcMinimum := ⟨1000⟩
    feerate := ⟨253⟩
    anchorOutputs := true }

/-- Demo balances for the anchor counterexample. -/
def waveD_d11_anchorBalance : Balance :=
  { localBalance := Msat.ofSat 1000
    remoteBalance := Msat.ofSat 1000 }

/-- **Checked: `commitmentPairOfBalances` with anchors is not conserving.**
It emits the two 330-satoshi anchors without debiting them from the funder,
so with a zero fee the local commitment's output sum is 2660 sat against a
funding value of 2000 sat.  The fix is to subtract
`2 * anchorOutputSat` from the funder's output in the wave-A builder (LDK
`insert_non_htlc_outputs`); this module does not edit the model. -/
theorem waveD_d11_pair_anchor_outputs_exceed :
    (commitmentPairOfBalances waveD_d11_anchorParams waveD_d11_anchorParams
          waveD_d11_anchorBalance 0 0 Direction.local).localCommitment.totalOutputValue >
      (commitmentPairOfBalances waveD_d11_anchorParams waveD_d11_anchorParams
          waveD_d11_anchorBalance 0 0 Direction.local).localCommitment.fundingValueSat := by
  decide

/-- The same anchor gap on the emitted output list rather than on
`totalOutputValue`: the list sum is 2660 sat for a 2000-sat funding value. -/
theorem waveD_d11_pair_anchor_outputs_list_exceed :
    ((commitmentPairOfBalances waveD_d11_anchorParams waveD_d11_anchorParams
          waveD_d11_anchorBalance 0 0 Direction.local).localCommitment.commitmentOutputs.map
        CommitmentOutput.value).sum >
      (commitmentPairOfBalances waveD_d11_anchorParams waveD_d11_anchorParams
          waveD_d11_anchorBalance 0 0 Direction.local).localCommitment.fundingValueSat := by
  rw [waveD_d11_outputsValue_eq_total]
  exact waveD_d11_pair_anchor_outputs_exceed

end LnLean.Proofs.WaveD.D11
