import LnLean.Proofs.Common

/-!
# LnLean.Proofs.PhaseC3.CloseConservation

English claim.  A channel can be closed cooperatively or unilaterally, and
both paths conserve the single L1 funding value.

* **Cooperative close.**  The closing transaction pays the two final
  off-chain balances directly, except that the funder pays the negotiated
  closing fee out of its own output.  The two closing outputs plus the
  closing fee are exactly the funding value
  (`cooperativeClose_outputs_add_fee`, `cooperativeClose_conserved`).
  The only non-truncation hypothesis is that the fee fits in the funder's
  balance; under that hypothesis the funder's output plus the fee
  reconstructs the funder balance exactly
  (`cooperativeClose_funder_output_add_fee`).

* **Unilateral close.**  The current commitment transaction is built by
  `buildCommitment`.  Its emitted outputs (including untrimmed HTLC outputs
  and, when negotiated, the two 330-satoshi anchors) plus its commitment fee
  equal the funding value (`unilateralClose_conserved`).  The exact
  non-truncation bound is
  `fee + toLocal + htlcOutputsValue htlcs + commitmentAnchorTotal anchors ≤
  funding`; under it the residual `toRemote` is the truthful remainder.
  The CSV contest delay is metadata only: changing it does not change any
  output value (`contestDelay_totalOutputValue`) and cannot create value
  (`contestDelay_no_value_creation`).

* **Agreement.**  If both paths are available on the same funding value,
  then the two conservation equations have the same right-hand side
  (`closePaths_totals_agree`).  When the two fees are equal, the output
  totals themselves agree (`closePaths_output_totals_agree_of_fee_eq`), and
  the concrete constructions from one `Balance` satisfy the same law
  (`cooperative_unilateral_agree`,
  `cooperative_unilateral_output_totals_eq_of_fee_eq`).

The fee bounds are stated in terms of the existing `Balance`, `Commitment`
and fee definitions: the cooperative closing fee is bounded by the funder's
balance and hence by the funding value; the unilateral commitment fee is
bounded by the funding value, and any feerate-derived required fee that the
recorded fee covers is bounded by the funding value as well.

BOLT sections.
* BOLT 2 `closing_signed`
  (`refs/bolts/02-peer-protocol.md:2411-2501`): a mutual close has no
  in-flight HTLCs and pays a negotiated closing fee.
* BOLT 3 §2 `Commitment Transaction`
  (`refs/bolts/03-transactions.md:83-353`): `to_local`, `to_remote`, HTLC
  outputs and the two anchor outputs; the CSV delay on `to_local` is the
  counterparty's `to_self_delay`.
* BOLT 3 §4 `Fees` (`refs/bolts/03-transactions.md:464-576`): the
  commitment fee is `feerate_per_kw * weight / 1000`, rounded down.
* BOLT 5 `Revoked Transaction Close Handling`
  (`refs/bolts/05-onchain.md:510-621`) explains why unilateral closes are
  contestable; this file proves only the value equation of the current
  commitment.

What is NOT modelled.
* Signatures, witness bytes, output ordering, `nSequence`, and the obscured
  commitment number.  The theorems are about output values and fees only.
* Second-stage HTLC transactions, anchor child-pays-for-parent, RBF, and the
  penalty path (covered by `LnLean.Proofs.Conservation`).
* The model gap in `commitmentPairOfBalances`: that builder does not debit
  the two anchors, so this file uses `buildCommitment` for the unilateral
  path.  The gap is already recorded in `CommitmentTxProps`.
-/

namespace LnLean.Proofs.PhaseC3

open LnLean
open LnLean.Channel
open LnLean.Proofs

set_option autoImplicit false

/-! ## Common balance arithmetic -/

/-- The satoshi value that the funder owns in a balance. -/
def funderBalance (b : Balance) (funder : Direction) : Nat :=
  if funder = Direction.local then b.localSat else b.remoteSat

theorem funderBalance_local (b : Balance) :
    funderBalance b Direction.local = b.localSat := rfl

theorem funderBalance_remote (b : Balance) :
    funderBalance b Direction.remote = b.remoteSat := rfl

/-- The funder's balance is part of the funding value; this is the basic
upper bound used by every fee bound below. -/
theorem funderBalance_le_total (b : Balance) (funder : Direction) :
    funderBalance b funder ≤ b.localSat + b.remoteSat := by
  unfold funderBalance
  cases funder <;> simp <;> omega

/-! ## Cooperative close -/

/-- The value core of a cooperative (`closing_signed`) transaction: two
closing outputs and one negotiated closing fee. -/
structure CooperativeClose where
  fundingValueSat : Nat
  toLocalSat : Nat
  toRemoteSat : Nat
  closingFeeSat : Nat
deriving Repr, DecidableEq, BEq

namespace CooperativeClose

/-- The two closing outputs. -/
def totalOutputValue (t : CooperativeClose) : Nat :=
  t.toLocalSat + t.toRemoteSat

/-- Conservation of a cooperative close: outputs plus the closing fee equal
the funding value. -/
def conserved (t : CooperativeClose) : Prop :=
  t.totalOutputValue + t.closingFeeSat = t.fundingValueSat

theorem conserved_iff (t : CooperativeClose) :
    t.conserved ↔ t.totalOutputValue + t.closingFeeSat = t.fundingValueSat :=
  Iff.rfl

/-- A conserving cooperative close never creates value. -/
theorem conserved_no_value_creation (t : CooperativeClose) (h : t.conserved) :
    t.totalOutputValue ≤ t.fundingValueSat := by
  unfold conserved at h
  omega

/-- The closing fee of a conserving cooperative close is exactly the residual
funding value. -/
theorem conserved_fee_eq_residual (t : CooperativeClose) (h : t.conserved) :
    t.closingFeeSat = t.fundingValueSat - t.totalOutputValue := by
  unfold conserved at h
  omega

/-- A final zero-HTLC, non-anchor commitment viewed as a cooperative close:
the commitment's two non-HTLC outputs are the closing outputs and its
commitment fee is the agreed closing fee. -/
def ofFinalCommitment (c : Commitment) : CooperativeClose :=
  { fundingValueSat := c.fundingValueSat
    toLocalSat := c.toLocalSat
    toRemoteSat := c.toRemoteSat
    closingFeeSat := c.feeSat }

/-- For a zero-HTLC commitment without anchors, the cooperative-close output
total is exactly the commitment output total.  This is the bridge between a
"final commitment" and a close transaction. -/
theorem ofFinalCommitment_totalOutputValue (c : Commitment)
    (hfinal : c.htlcs = [] ∧ c.anchorOutputs = false) :
    (ofFinalCommitment c).totalOutputValue = c.totalOutputValue := by
  rcases hfinal with ⟨hhtlcs, hanchors⟩
  unfold ofFinalCommitment totalOutputValue Commitment.totalOutputValue
    Commitment.htlcOutputValue Commitment.anchorOutputValue
  rw [hhtlcs, hanchors]
  simp [htlcOutputsValue]

/-- A conserving final commitment yields a conserving cooperative close with
the same two output values and the same fee. -/
theorem ofFinalCommitment_conserved (c : Commitment)
    (hfinal : c.htlcs = [] ∧ c.anchorOutputs = false)
    (hc : CommitmentConserved c) :
    (ofFinalCommitment c).conserved := by
  unfold CommitmentConserved at hc
  unfold conserved
  rw [ofFinalCommitment_totalOutputValue c hfinal]
  simpa [ofFinalCommitment] using hc

end CooperativeClose

/-- Build a cooperative close from the final off-chain balance.  The funder
pays the agreed `fee` from its own output; the non-funder receives its whole
balance.  No dust trimming is applied: callers may use
`cooperativeClose_distributes` to check the two exact outputs. -/
def cooperativeClose (b : Balance) (fee : Nat) (funder : Direction) :
    CooperativeClose :=
  { fundingValueSat := b.localSat + b.remoteSat
    toLocalSat := b.localSat - (if funder = Direction.local then fee else 0)
    toRemoteSat := b.remoteSat - (if funder = Direction.remote then fee else 0)
    closingFeeSat := fee }

/-- **Exact distribution of a cooperative close.**  Under the non-truncation
bound `fee ≤ funderBalance b funder`, either the local party or the remote
party is the funder; that party's output plus the fee reconstructs its
balance exactly, and the other party's output is its whole balance. -/
theorem cooperativeClose_distributes (b : Balance) (fee : Nat)
    (funder : Direction) (h : fee ≤ funderBalance b funder) :
    (funder = Direction.local ∧
        (cooperativeClose b fee funder).toLocalSat + fee = b.localSat ∧
        (cooperativeClose b fee funder).toRemoteSat = b.remoteSat) ∨
      (funder = Direction.remote ∧
        (cooperativeClose b fee funder).toLocalSat = b.localSat ∧
        (cooperativeClose b fee funder).toRemoteSat + fee = b.remoteSat) := by
  by_cases hlocal : funder = Direction.local
  · subst hlocal
    left
    refine ⟨rfl, ?_, ?_⟩
    · unfold funderBalance at h
      simp [cooperativeClose] at h ⊢
      omega
    · simp [cooperativeClose]
  · right
    have hremote : funder = Direction.remote := by
      cases funder <;> simp_all
    subst hremote
    refine ⟨rfl, ?_, ?_⟩
    · simp [cooperativeClose]
    · unfold funderBalance at h
      simp [cooperativeClose] at h ⊢
      omega

/-- **Cooperative close conservation.**  The two closing outputs plus the
negotiated closing fee are exactly the funding value
`b.localSat + b.remoteSat`.  The hypothesis is precisely the absence of
`Nat` truncation in the funder's output. -/
theorem cooperativeClose_outputs_add_fee (b : Balance) (fee : Nat)
    (funder : Direction) (h : fee ≤ funderBalance b funder) :
    (cooperativeClose b fee funder).totalOutputValue +
        (cooperativeClose b fee funder).closingFeeSat =
      b.localSat + b.remoteSat := by
  unfold cooperativeClose CooperativeClose.totalOutputValue at ⊢
  unfold funderBalance at h
  cases funder <;> simp at h ⊢ <;> omega

/-- The cooperative close built from a balance is conserving. -/
theorem cooperativeClose_conserved (b : Balance) (fee : Nat)
    (funder : Direction) (h : fee ≤ funderBalance b funder) :
    (cooperativeClose b fee funder).conserved := by
  unfold CooperativeClose.conserved
  exact cooperativeClose_outputs_add_fee b fee funder h

/-- The funder's output plus the closing fee reconstructs the funder balance
exactly, for either choice of funder. -/
theorem cooperativeClose_funder_output_add_fee (b : Balance) (fee : Nat)
    (funder : Direction) (h : fee ≤ funderBalance b funder) :
    (if funder = Direction.local then
        (cooperativeClose b fee funder).toLocalSat
      else (cooperativeClose b fee funder).toRemoteSat) + fee =
      funderBalance b funder := by
  unfold funderBalance at h ⊢
  cases funder <;> simp [cooperativeClose] at h ⊢ <;> omega

/-- **Cooperative fee bound.**  The agreed closing fee is at most the funding
value, because it is at most the funder's balance. -/
theorem cooperativeClose_fee_le_funding (b : Balance) (fee : Nat)
    (funder : Direction) (h : fee ≤ funderBalance b funder) :
    fee ≤ b.localSat + b.remoteSat :=
  Nat.le_trans h (funderBalance_le_total b funder)

/-- The closing fee is also bounded by the funding value of the close record
itself. -/
theorem cooperativeClose_closingFee_le_fundingValue (b : Balance) (fee : Nat)
    (funder : Direction) (h : fee ≤ funderBalance b funder) :
    (cooperativeClose b fee funder).closingFeeSat ≤
      (cooperativeClose b fee funder).fundingValueSat := by
  simpa [cooperativeClose] using cooperativeClose_fee_le_funding b fee funder h

/-! ## Unilateral close -/

/-- **Unilateral close conservation.**  The current commitment transaction
built by `buildCommitment` has outputs plus commitment fee equal to its
funding value, provided the exact non-truncation bound
`fee + toLocal + HTLCs + anchors ≤ funding` holds.  This covers

* untrimmed HTLC outputs through `htlcOutputsValue`;
* the two 330-satoshi anchors through `commitmentAnchorTotal`;
* both anchor settings and either holder.

The hypothesis is the minimal one that makes the residual `toRemote`
(`funding - fee - toLocal - HTLCs - anchors`) the true remainder. -/
theorem unilateralClose_conserved
    (holder : Direction) (number funding fee toLocal : Nat)
    (htlcs : List CommitmentHTLCOutput) (contestDelay : Nat) (anchors : Bool)
    (h : fee + toLocal + htlcOutputsValue htlcs +
        commitmentAnchorTotal anchors ≤ funding) :
    CommitmentConserved
      (buildCommitment holder number funding fee toLocal htlcs contestDelay
        anchors) := by
  unfold CommitmentConserved
  rw [← Commitment.outputsValue_commitmentOutputs]
  exact buildCommitment_conservation holder number funding fee toLocal htlcs
    contestDelay anchors h

/-- The fee recorded on a unilateral close is exactly the fee argument. -/
theorem unilateralClose_fee_eq (holder : Direction) (number funding fee toLocal
    : Nat) (htlcs : List CommitmentHTLCOutput) (contestDelay : Nat)
    (anchors : Bool) :
    (buildCommitment holder number funding fee toLocal htlcs contestDelay
      anchors).feeSat = fee := rfl

/-- **Unilateral fee bound.**  The commitment fee is at most the funding
value, under the same non-truncation bound as conservation. -/
theorem unilateralClose_fee_le_funding
    (_holder : Direction) (_number funding fee toLocal : Nat)
    (htlcs : List CommitmentHTLCOutput) (_contestDelay : Nat) (anchors : Bool)
    (h : fee + toLocal + htlcOutputsValue htlcs +
        commitmentAnchorTotal anchors ≤ funding) :
    fee ≤ funding := by
  omega

/-- **Required-fee bound.**  If the recorded commitment fee covers the fee
required by the feerate and the commitment's weight, then that required fee
is bounded by the funding value.  This connects the close path to
`commitmentFee`/`feeForWeight` without assuming the fee is exactly the
required amount. -/
theorem unilateralClose_requiredFee_le_funding
    (r : FeeRate) (holder : Direction) (number funding fee toLocal : Nat)
    (htlcs : List CommitmentHTLCOutput) (contestDelay : Nat) (anchors : Bool)
    (h : fee + toLocal + htlcOutputsValue htlcs +
        commitmentAnchorTotal anchors ≤ funding)
    (hpaid : (commitmentFee r
      (buildCommitment holder number funding fee toLocal htlcs contestDelay
        anchors)).val ≤ fee) :
    (commitmentFee r
      (buildCommitment holder number funding fee toLocal htlcs contestDelay
        anchors)).val ≤ funding := by
  have hfee : fee ≤ funding :=
    unilateralClose_fee_le_funding holder number funding fee toLocal htlcs
      contestDelay anchors h
  omega

/-- **Changing the CSV contest delay creates no value.**  `contestDelay` is
the delay on the broadcaster's `to_local` output, not an amount; the output
total is independent of it. -/
theorem contestDelay_totalOutputValue (c : Commitment) (d : Nat) :
    ({ c with contestDelay := d } : Commitment).totalOutputValue =
      c.totalOutputValue := rfl

/-- The contest delay does not affect the conservation equation either. -/
theorem contestDelay_conserved_iff (c : Commitment) (d : Nat) :
    CommitmentConserved ({ c with contestDelay := d } : Commitment) ↔
      CommitmentConserved c := by
  unfold CommitmentConserved
  rw [contestDelay_totalOutputValue]

/-- **Contest-delay outputs do not create value.**  Any commitment obtained
by changing only the CSV delay emits at most the original funding value. -/
theorem contestDelay_no_value_creation (c : Commitment) (d : Nat)
    (hc : CommitmentConserved c) :
    ({ c with contestDelay := d } : Commitment).totalOutputValue ≤
      c.fundingValueSat := by
  rw [contestDelay_totalOutputValue]
  exact conserved_no_value_creation c hc

/-- A unilateral close stays conserving after the contest delay is changed to
any value, so the delay cannot be used to manufacture extra outputs. -/
theorem unilateralClose_contestDelay_conserved
    (holder : Direction) (number funding fee toLocal : Nat)
    (htlcs : List CommitmentHTLCOutput) (contestDelay : Nat) (anchors : Bool)
    (h : fee + toLocal + htlcOutputsValue htlcs +
        commitmentAnchorTotal anchors ≤ funding) (d : Nat) :
    CommitmentConserved
      ({ buildCommitment holder number funding fee toLocal htlcs contestDelay
          anchors with contestDelay := d } : Commitment) := by
  rw [contestDelay_conserved_iff]
  exact unilateralClose_conserved holder number funding fee toLocal htlcs
    contestDelay anchors h

/-! ## Both close paths on one funding value -/

/-- Two close paths that spend the same funding output.  `sameFunding` is a
proof field, so an agreement theorem cannot accidentally compare different
channels. -/
structure ClosePaths where
  cooperative : CooperativeClose
  unilateral : Commitment
  sameFunding : cooperative.fundingValueSat = unilateral.fundingValueSat

/-- **The two paths agree on the same funding value.**  If the cooperative
close and the unilateral commitment both conserve, then their
"outputs plus fee" totals are the same number: the one funding value. -/
theorem closePaths_totals_agree (p : ClosePaths)
    (hc : p.cooperative.conserved)
    (hu : CommitmentConserved p.unilateral) :
    p.cooperative.totalOutputValue + p.cooperative.closingFeeSat =
      p.unilateral.totalOutputValue + p.unilateral.feeSat := by
  unfold CooperativeClose.conserved at hc
  unfold CommitmentConserved at hu
  rw [hc, hu, p.sameFunding]

/-- **Output totals agree when the fees agree.**  Under the same funding value
and equal fees, the two conservation equations give equal output totals. -/
theorem closePaths_output_totals_agree_of_fee_eq (p : ClosePaths)
    (hc : p.cooperative.conserved)
    (hu : CommitmentConserved p.unilateral)
    (hfee : p.cooperative.closingFeeSat = p.unilateral.feeSat) :
    p.cooperative.totalOutputValue = p.unilateral.totalOutputValue := by
  have h := closePaths_totals_agree p hc hu
  omega

/-- **Concrete agreement from one balance.**  The cooperative close built
from `b` and the unilateral commitment built on the satoshi funding value
`b.localSat + b.remoteSat` have the same "outputs plus fee" total. -/
theorem cooperative_unilateral_agree
    (b : Balance) (feeCoop feeUni : Nat) (funder holder : Direction)
    (number toLocal : Nat) (htlcs : List CommitmentHTLCOutput)
    (contestDelay : Nat) (anchors : Bool)
    (hcoop : feeCoop ≤ funderBalance b funder)
    (huni : feeUni + toLocal + htlcOutputsValue htlcs +
        commitmentAnchorTotal anchors ≤ b.localSat + b.remoteSat) :
    (cooperativeClose b feeCoop funder).totalOutputValue +
        (cooperativeClose b feeCoop funder).closingFeeSat =
      (buildCommitment holder number (b.localSat + b.remoteSat) feeUni toLocal
        htlcs contestDelay anchors).totalOutputValue +
      (buildCommitment holder number (b.localSat + b.remoteSat) feeUni toLocal
        htlcs contestDelay anchors).feeSat := by
  let cc := cooperativeClose b feeCoop funder
  let uc := buildCommitment holder number (b.localSat + b.remoteSat) feeUni
    toLocal htlcs contestDelay anchors
  have hc : cc.conserved :=
    cooperativeClose_conserved b feeCoop funder hcoop
  have hu : CommitmentConserved uc :=
    unilateralClose_conserved holder number (b.localSat + b.remoteSat) feeUni
      toLocal htlcs contestDelay anchors huni
  have hsame : cc.fundingValueSat = uc.fundingValueSat := rfl
  exact closePaths_totals_agree ⟨cc, uc, hsame⟩ hc hu

/-- **Concrete output-total agreement when the agreed fees coincide.** -/
theorem cooperative_unilateral_output_totals_eq_of_fee_eq
    (b : Balance) (feeCoop feeUni : Nat) (funder holder : Direction)
    (number toLocal : Nat) (htlcs : List CommitmentHTLCOutput)
    (contestDelay : Nat) (anchors : Bool)
    (hcoop : feeCoop ≤ funderBalance b funder)
    (huni : feeUni + toLocal + htlcOutputsValue htlcs +
        commitmentAnchorTotal anchors ≤ b.localSat + b.remoteSat)
    (hfee : feeCoop = feeUni) :
    (cooperativeClose b feeCoop funder).totalOutputValue =
      (buildCommitment holder number (b.localSat + b.remoteSat) feeUni toLocal
        htlcs contestDelay anchors).totalOutputValue := by
  let cc := cooperativeClose b feeCoop funder
  let uc := buildCommitment holder number (b.localSat + b.remoteSat) feeUni
    toLocal htlcs contestDelay anchors
  have hc : cc.conserved :=
    cooperativeClose_conserved b feeCoop funder hcoop
  have hu : CommitmentConserved uc :=
    unilateralClose_conserved holder number (b.localSat + b.remoteSat) feeUni
      toLocal htlcs contestDelay anchors huni
  have hsame : cc.fundingValueSat = uc.fundingValueSat := rfl
  have h := closePaths_totals_agree ⟨cc, uc, hsame⟩ hc hu
  change cc.totalOutputValue = uc.totalOutputValue
  have h' : cc.totalOutputValue + feeCoop = uc.totalOutputValue + feeUni := h
  omega

/-! ## Checked numeric instance -/

/-- A concrete cooperative close: 60 000 + 39 000 satoshis of closing outputs
and a 1 000-satoshi fee exactly spend a 100 000-satoshi funding value. -/
theorem concrete_cooperative_close_conserved :
    (cooperativeClose
      { localBalance := Msat.ofSat 60000
        remoteBalance := Msat.ofSat 39000 }
      1000 Direction.local).conserved := by
  apply cooperativeClose_conserved
  decide

/-- A concrete unilateral close with one 5 000-satoshi HTLC output and no
anchors: the outputs plus the 1 000-satoshi fee are exactly 100 000
satoshis. -/
theorem concrete_unilateral_close_conserved :
    CommitmentConserved
      (buildCommitment Direction.local 0 100000 1000 60000
        [{ direction := Direction.local
           amountSat := 5000
           cltvExpiry := 500
           state := HTLCState.offered }] 144 false) := by
  apply unilateralClose_conserved
  decide

end LnLean.Proofs.PhaseC3
