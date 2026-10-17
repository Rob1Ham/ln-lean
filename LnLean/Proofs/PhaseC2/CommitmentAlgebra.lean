import LnLean.Proofs.Conservation
import LnLean.Proofs.Channel.CommitmentTxProps

/-!
# LnLean.Proofs.PhaseC2.CommitmentAlgebra

English claim.  A commitment transaction's value is the sum of its four
BOLT 3 output groups: the holder's `to_local` output, the `to_remote`
output, one output per untrimmed HTLC, and (when `option_anchors` is
negotiated) two 330-satoshi anchor outputs.  `totalOutputValue` is exactly
that group sum, and it also equals the sum of the values in the emitted
output list `commitmentOutputs` (zero-valued `to_local`/`to_remote` entries
are omitted from the list but contribute zero).  Under the conservation
predicate `CommitmentConserved` the same total is the funding value minus
the commitment fee.  The anchor/no-anchor and zero-HTLC forms are
specializations; each conditional equality carries exactly the arithmetic
precondition under which the natural-number subtraction in
`zeroHtlcCommitment` is the intended residual.

BOLT sections.
* BOLT 3 §2 `Commitment Transaction` (`03-transactions.md:102-307`):
  `to_local` at `:113-135`, `to_remote` at `:136-147`, anchors at
  `:148-198`, and offered/received HTLC outputs at `:199-304`.
* BOLT 3 §2 `Trimmed Outputs` (`:308-367`): a zero/dust output is not
  emitted and its value stays in the corresponding balance.
* BOLT 3 §4 `Fees` (`:464-576`): the commitment fee is the floored
  feerate-times-weight product, and outputs plus fee reconstruct funding.

rust-lightning anchors at `fe4900930c6bd5786ec4203274d7cf312776a5a6`.
* `lightning/src/ln/chan_utils.rs:1713-1740`
  (`CommitmentTransaction::new`).
* `lightning/src/ln/chan_utils.rs:1887-1945`
  (`insert_non_htlc_outputs`, including the 330-sat anchors and trimming).
* `lightning/src/ln/chan_utils.rs:716-744`
  (`HTLCOutputInCommitment` and its satoshi value).
* `lightning/src/sign/tx_builder.rs:984-1145`
  (`TxBuilder::build_commitment_transaction`, the funder subtraction).

What is NOT modelled.
* Transaction serialization, output order (BIP 69+CLTV sorting), the
  obscured commitment number, `nSequence`, signatures, and witnesses.
* Second-stage HTLC transactions and their fees; the HTLC outputs here are
  the already-untrimmed commitment-level outputs.
* Anchor child-pays-for-parent fee bumping, `shared_anchor`, zero-fee
  commitments, and dust trimming of `to_local`/`to_remote` against the
  broadcaster's dust limit (the model trims only at zero).
-/

namespace LnLean.Proofs.PhaseC2

open LnLean
open LnLean.Channel

set_option autoImplicit false

/-! ## The group decomposition -/

/-- `totalOutputValue` written as the four BOLT 3 groups, with the HTLC
group expanded to the plain sum of the HTLC amounts. -/
theorem totalOutputValue_eq_toLocal_add_toRemote_add_htlcSum_add_anchor
    (c : Commitment) :
    c.totalOutputValue =
      c.toLocalSat + c.toRemoteSat +
        (c.htlcs.map (fun h => h.amountSat)).sum + c.anchorOutputValue := by
  rw [Commitment.totalOutputValue_eq, Commitment.htlcOutputValue_eq_sum]

/-- The emitted output list has exactly the same value as
`totalOutputValue`: trimming a zero-valued `to_local`/`to_remote` output
does not change the sum. -/
theorem totalOutputValue_eq_commitmentOutputs_sum (c : Commitment) :
    c.totalOutputValue = outputsValue c.commitmentOutputs :=
  (Commitment.outputsValue_commitmentOutputs c).symm

/-- Converse direction of the list identity, phrased for rewriting an
output-list sum into the algebraic total. -/
theorem commitmentOutputs_sum_eq_totalOutputValue (c : Commitment) :
    outputsValue c.commitmentOutputs = c.totalOutputValue :=
  Commitment.outputsValue_commitmentOutputs c

/-- The sum over the emitted output list, written directly as the four
groups. -/
theorem commitmentOutputs_sum_eq_group_sum (c : Commitment) :
    outputsValue c.commitmentOutputs =
      c.toLocalSat + c.toRemoteSat + c.htlcOutputValue +
        c.anchorOutputValue := by
  rw [commitmentOutputs_sum_eq_totalOutputValue, Commitment.totalOutputValue_eq]

/-! ## Anchor and no-anchor specializations -/

/-- Without anchors the anchor group contributes nothing, so the total is
`to_local + to_remote + HTLC outputs`. -/
theorem totalOutputValue_noAnchors (c : Commitment)
    (h : c.anchorOutputs = false) :
    c.totalOutputValue =
      c.toLocalSat + c.toRemoteSat + c.htlcOutputValue := by
  simp [Commitment.totalOutputValue, Commitment.anchorOutputValue, h]

/-- With anchors the anchor group contributes exactly two 330-satoshi
outputs. -/
theorem totalOutputValue_anchors (c : Commitment)
    (h : c.anchorOutputs = true) :
    c.totalOutputValue =
      c.toLocalSat + c.toRemoteSat + c.htlcOutputValue +
        2 * anchorOutputSat := by
  simp [Commitment.totalOutputValue, Commitment.anchorOutputValue, h]

/-- Turning anchors on adds exactly the two anchor outputs (`2 * 330`
satoshis) to the total, with every other field held fixed. -/
theorem totalOutputValue_anchor_delta (c : Commitment) :
    ({ c with anchorOutputs := true } : Commitment).totalOutputValue =
      ({ c with anchorOutputs := false } : Commitment).totalOutputValue +
        2 * anchorOutputSat := by
  simp [Commitment.totalOutputValue, Commitment.htlcOutputValue,
    Commitment.anchorOutputValue]

/-! ## Conservation -/

/-- **The output algebra under conservation.**  If outputs plus fee equal
the funding value, then the total output value is exactly the residual
funding value after the fee. -/
theorem totalOutputValue_eq_funding_sub_fee (c : Commitment)
    (hc : CommitmentConserved c) :
    c.totalOutputValue = c.fundingValueSat - c.feeSat := by
  unfold CommitmentConserved at hc
  omega

/-- Restatement of conservation as an algebraic decomposition of the
funding value. -/
theorem funding_eq_totalOutputValue_add_fee (c : Commitment)
    (hc : CommitmentConserved c) :
    c.fundingValueSat = c.totalOutputValue + c.feeSat :=
  hc.symm

/-- Under conservation the no-anchor group sum is the funding residual. -/
theorem totalOutputValue_noAnchors_eq_funding_sub_fee (c : Commitment)
    (hc : CommitmentConserved c) (h : c.anchorOutputs = false) :
    c.toLocalSat + c.toRemoteSat + c.htlcOutputValue =
      c.fundingValueSat - c.feeSat := by
  rw [← totalOutputValue_noAnchors c h]
  exact totalOutputValue_eq_funding_sub_fee c hc

/-- Under conservation the anchor group sum is the funding residual. -/
theorem totalOutputValue_anchors_eq_funding_sub_fee (c : Commitment)
    (hc : CommitmentConserved c) (h : c.anchorOutputs = true) :
    c.toLocalSat + c.toRemoteSat + c.htlcOutputValue +
        2 * anchorOutputSat =
      c.fundingValueSat - c.feeSat := by
  rw [← totalOutputValue_anchors c h]
  exact totalOutputValue_eq_funding_sub_fee c hc

/-! ## Zero-HTLC specializations -/

/-- With no HTLC outputs the HTLC group contributes zero. -/
theorem totalOutputValue_of_htlcs_nil (c : Commitment)
    (h : c.htlcs = []) :
    c.totalOutputValue =
      c.toLocalSat + c.toRemoteSat + c.anchorOutputValue := by
  simp [Commitment.totalOutputValue, Commitment.htlcOutputValue,
    htlcOutputsValue, h]

/-- The group-sum form for `zeroHtlcCommitment`, before any arithmetic
precondition: `to_remote` is the residual
`funding - fee - to_local - anchors`. -/
theorem zeroHtlcCommitment_totalOutputValue
    (holder : Direction) (number funding toLocal fee contestDelay : Nat)
    (anchors : Bool) :
    (zeroHtlcCommitment holder number funding toLocal fee contestDelay
        anchors).totalOutputValue =
      toLocal +
        (funding - fee - toLocal -
          (if anchors then 2 * anchorOutputSat else 0)) +
        (if anchors then 2 * anchorOutputSat else 0) := by
  by_cases h : anchors
  · simp [zeroHtlcCommitment, Commitment.totalOutputValue,
      Commitment.htlcOutputValue, htlcOutputsValue, Commitment.anchorOutputValue, h]
  · simp [zeroHtlcCommitment, Commitment.totalOutputValue,
      Commitment.htlcOutputValue, htlcOutputsValue, Commitment.anchorOutputValue, h]

/-- Zero-HTLC, no-anchor total value.  The precondition is exactly the
non-underflow condition for `to_remote = funding - fee - toLocal`. -/
theorem zeroHtlcCommitment_totalOutputValue_noAnchors
    (holder : Direction) (number funding toLocal fee contestDelay : Nat)
    (h : fee + toLocal ≤ funding) :
    (zeroHtlcCommitment holder number funding toLocal fee contestDelay
        false).totalOutputValue = funding - fee := by
  rw [zeroHtlcCommitment_totalOutputValue]
  simp
  omega

/-- Zero-HTLC, anchor total value.  The precondition additionally covers
the two 330-satoshi anchors, so the residual does not underflow. -/
theorem zeroHtlcCommitment_totalOutputValue_anchors
    (holder : Direction) (number funding toLocal fee contestDelay : Nat)
    (h : fee + toLocal + 2 * anchorOutputSat ≤ funding) :
    (zeroHtlcCommitment holder number funding toLocal fee contestDelay
        true).totalOutputValue = funding - fee := by
  rw [zeroHtlcCommitment_totalOutputValue]
  simp
  omega

/-- Zero-HTLC, no-anchor conservation. -/
theorem zeroHtlcCommitment_conserved_noAnchors
    (holder : Direction) (number funding toLocal fee contestDelay : Nat)
    (h : fee + toLocal ≤ funding) :
    CommitmentConserved
      (zeroHtlcCommitment holder number funding toLocal fee contestDelay
        false) := by
  unfold CommitmentConserved
  rw [zeroHtlcCommitment_totalOutputValue_noAnchors
    holder number funding toLocal fee contestDelay h]
  simp [zeroHtlcCommitment]
  omega

/-- Zero-HTLC, anchor conservation. -/
theorem zeroHtlcCommitment_conserved_anchors
    (holder : Direction) (number funding toLocal fee contestDelay : Nat)
    (h : fee + toLocal + 2 * anchorOutputSat ≤ funding) :
    CommitmentConserved
      (zeroHtlcCommitment holder number funding toLocal fee contestDelay
        true) := by
  unfold CommitmentConserved
  rw [zeroHtlcCommitment_totalOutputValue_anchors
    holder number funding toLocal fee contestDelay h]
  simp [zeroHtlcCommitment]
  omega

end LnLean.Proofs.PhaseC2
