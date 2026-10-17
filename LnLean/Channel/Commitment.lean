import LnLean.Channel.Types
import LnLean.Channel.Fee

/-!
# LnLean.Channel.Commitment

English claim.  A commitment transaction has `to_local`, `to_remote`, one
output per untrimmed HTLC, and (when `option_anchors` is negotiated) two
anchor outputs of 330 satoshis each.  Its expected weight is
`724 + 172 * num_htlcs` without anchors and `1124 + 172 * num_htlcs` with
anchors (BOLT 3 §4), and its fee is the floored product of the negotiated
feerate with that weight.  The local and remote commitment transactions are
**not** symmetric: `to_local` belongs to the broadcaster, the CSV delay on
that output is the *counterparty's* `to_self_delay`, and the funder pays the
fee out of its own output on both transactions.

BOLT sections.
* BOLT 3 §2 `Commitment Transaction` (`03-transactions.md:83-353`):
  `to_local` at `:113-135`, `to_remote` at `:136-147`, anchors at
  `:148-198`, offered/received HTLC outputs at `:199-304`, trimming at
  `:305-354`.
* BOLT 3 §4 `Fees` (`03-transactions.md:464-576`), expected weights at
  `:490-502`, base-fee rule at `:518-522`.
* BOLT 2 §2 (`to_self_delay` semantics at `02-peer-protocol.md:750-752`)
  and §3 (`update_fee` at `:3250-3265`).

rust-lightning anchors at `fe4900930c6bd5786ec4203274d7cf312776a5a6`.
* `lightning/src/ln/chan_utils.rs:1614-1630`
  (`struct CommitmentTransaction`), `:1713-1740`
  (`CommitmentTransaction::new`), `:1887-1945` (`insert_non_htlc_outputs`,
  including the 330-sat anchors and trimming), `:275-298`
  (`COMMITMENT_TX_WEIGHT_PER_HTLC`, base weights, `commit_tx_fee_sat`).
* `lightning/src/ln/channel.rs:1546-1610` (the `Channel` context that owns
  the two commitment counters).

What is NOT modelled.
* Exact output ordering, the obscured commitment number, `nSequence`, and
  signature/witness bytes.
* Zero-fee commitments and the `shared_anchor` output.
* HTLC second-stage transactions and their 663/703 weights.
* `to_local` justice/penalty spending; the revocation workstream owns it.
-/

namespace LnLean.Channel

set_option autoImplicit false

open LnLean

/-! ## Weight constants (BOLT 3 §4) -/

/-- Base commitment weight.  BOLT 3: 724 without anchors, 1124 with
`option_anchors` (`03-transactions.md:495-497`). -/
def commitmentBaseWeight (anchors : Bool) : Nat :=
  if anchors then 1124 else 724

/-- Weight added by one untrimmed HTLC output. -/
def commitmentHtlcWeight : Nat := 172

theorem commitmentHtlcWeight_eq : commitmentHtlcWeight = 172 := rfl

theorem commitmentBaseWeight_noAnchors :
    commitmentBaseWeight false = 724 := rfl

theorem commitmentBaseWeight_anchors :
    commitmentBaseWeight true = 1124 := rfl

/-- Expected commitment weight, in weight units. -/
def commitmentWeight (anchors : Bool) (numHtlcs : Nat) : Weight :=
  ⟨commitmentBaseWeight anchors + commitmentHtlcWeight * numHtlcs⟩

theorem commitmentWeight_val (anchors : Bool) (numHtlcs : Nat) :
    (commitmentWeight anchors numHtlcs).val =
      commitmentBaseWeight anchors + commitmentHtlcWeight * numHtlcs := rfl

theorem commitmentWeight_zero_htlcs (anchors : Bool) :
    commitmentWeight anchors 0 = ⟨commitmentBaseWeight anchors⟩ := by
  simp [commitmentWeight]

/-- Adding an untrimmed HTLC increases the weight by exactly 172. -/
theorem commitmentWeight_succ (anchors : Bool) (numHtlcs : Nat) :
    (commitmentWeight anchors (numHtlcs + 1)).val =
      (commitmentWeight anchors numHtlcs).val + commitmentHtlcWeight := by
  simp [commitmentWeight, commitmentHtlcWeight, Nat.mul_succ]
  omega

/-- Weight is monotone in the number of untrimmed HTLCs. -/
theorem commitmentWeight_mono_htlcs (anchors : Bool) {n m : Nat} (h : n ≤ m) :
    (commitmentWeight anchors n).val ≤ (commitmentWeight anchors m).val := by
  unfold commitmentWeight
  simp
  exact Nat.mul_le_mul_left commitmentHtlcWeight h

/-- Anchor outputs add 400 weight units (two 330-sat outputs). -/
theorem commitmentWeight_anchor_delta (n : Nat) :
    (commitmentWeight true n).val = (commitmentWeight false n).val + 400 := by
  simp [commitmentWeight, commitmentBaseWeight]
  omega

/-! ## Outputs -/

/-- The output list of a commitment transaction, in BOLT 3 order:
`to_local`, `to_remote`, HTLC outputs, then the two anchors.  Zero-valued
`to_local`/`to_remote` outputs are not emitted (trimming); HTLCs in this
record have already survived BOLT 3's HTLC dust test. -/
def Commitment.commitmentOutputs (c : Commitment) : List CommitmentOutput :=
  (if c.toLocalSat = 0 then [] else [CommitmentOutput.toLocal c.toLocalSat]) ++
  (if c.toRemoteSat = 0 then [] else [CommitmentOutput.toRemote c.toRemoteSat]) ++
  c.htlcs.map (fun h => CommitmentOutput.htlc h.direction h.amountSat) ++
  (if c.anchorOutputs then [CommitmentOutput.localAnchor,
                            CommitmentOutput.remoteAnchor] else [])

/-- Sum of the HTLC output values. -/
def htlcOutputsValue : List CommitmentHTLCOutput → Nat
  | [] => 0
  | h :: t => h.amountSat + htlcOutputsValue t

/-- The HTLC part of the commitment value. -/
def Commitment.htlcOutputValue (c : Commitment) : Nat :=
  htlcOutputsValue c.htlcs

/-- The anchor part of the commitment value: two 330-sat outputs. -/
def Commitment.anchorOutputValue (c : Commitment) : Nat :=
  if c.anchorOutputs then 2 * anchorOutputSat else 0

/-- The HTLC outputs contribute exactly the sum of their amounts. -/
theorem Commitment.htlcOutputValue_eq_sum (c : Commitment) :
    c.htlcOutputValue = (c.htlcs.map (fun h => h.amountSat)).sum := by
  unfold Commitment.htlcOutputValue
  induction c.htlcs with
  | nil => rfl
  | cons h t ih => simp [htlcOutputsValue, ih]

/-- Mapping an HTLC output to its value is the same as projecting the
amount directly. -/
theorem map_htlcOutput_value (c : Commitment) :
    ((c.htlcs.map (fun h => CommitmentOutput.htlc h.direction h.amountSat)).map
        CommitmentOutput.value) =
      c.htlcs.map (fun h => h.amountSat) := by
  induction c.htlcs with
  | nil => rfl
  | cons h t ih => simp [CommitmentOutput.value, ih]

/-- Total value of all commitment outputs, in satoshis.  This is the sum of
the four output groups; a zero-valued `to_local`/`to_remote` is omitted
from `commitmentOutputs` but contributes zero to the sum. -/
def Commitment.totalOutputValue (c : Commitment) : Nat :=
  c.toLocalSat + c.toRemoteSat + c.htlcOutputValue + c.anchorOutputValue

/-- The defining equation of `totalOutputValue`, made explicit. -/
theorem Commitment.totalOutputValue_eq (c : Commitment) :
    c.totalOutputValue =
      c.toLocalSat + c.toRemoteSat + c.htlcOutputValue + c.anchorOutputValue := rfl

/-- The weight of a concrete commitment record. -/
def Commitment.weight (c : Commitment) : Weight :=
  commitmentWeight c.anchorOutputs c.htlcs.length

/-- The fee required by a feerate for a concrete commitment record. -/
def commitmentFee (r : FeeRate) (c : Commitment) : Msat :=
  feeForWeight r c.weight

theorem commitmentFee_val (r : FeeRate) (c : Commitment) :
    (commitmentFee r c).val = r.msatPerKw * (c.weight).val / 1000 := rfl

theorem commitmentFee_nonneg (r : FeeRate) (c : Commitment) :
    0 ≤ (commitmentFee r c).val :=
  Nat.zero_le _

/-- More HTLCs on a commitment cannot lower its required fee. -/
theorem commitmentFee_mono_htlcs (r : FeeRate) (c : Commitment) {m : Nat}
    (h : c.htlcs.length ≤ m) :
    (commitmentFee r c).val ≤
      (feeForWeight r (commitmentWeight c.anchorOutputs m)).val := by
  unfold commitmentFee Commitment.weight
  exact feeForWeight_mono_weight r (commitmentWeight_mono_htlcs c.anchorOutputs h)

/-! ## A zero-HTLC commitment -/

/-- A commitment with no HTLCs, whose `to_remote` value is whatever remains
after the holder's `to_local`, the fee, and the anchors.  When the
hypothesis `fee + toLocal + anchors ≤ funding` holds, this is the exact
BOLT 3 conservation equation. -/
def zeroHtlcCommitment (holder : Direction) (number funding toLocal fee
    contestDelay : Nat) (anchors : Bool) : Commitment :=
  let anchorTotal := if anchors then 2 * anchorOutputSat else 0
  { holder := holder
    commitmentNumber := number
    fundingValueSat := funding
    toLocalSat := toLocal
    toRemoteSat := funding - fee - toLocal - anchorTotal
    htlcs := []
    feeSat := fee
    contestDelay := contestDelay
    anchorOutputs := anchors }

theorem zeroHtlcCommitment_htlcs (holder : Direction) (number funding toLocal
    fee contestDelay : Nat) (anchors : Bool) :
    (zeroHtlcCommitment holder number funding toLocal fee contestDelay anchors).htlcs = [] := rfl

theorem zeroHtlcCommitment_fee (holder : Direction) (number funding toLocal
    fee contestDelay : Nat) (anchors : Bool) :
    (zeroHtlcCommitment holder number funding toLocal fee contestDelay anchors).feeSat = fee := rfl

/-! ## Local/remote asymmetry -/

/-- Build the two commitment records from the same balances.  The `funder`
pays `fee` out of its output on *both* commitments.  `localCommitment`
belongs to the local node and has CSV delay `remoteParams.toSelfDelay`;
`remoteCommitment` belongs to the remote node and has CSV delay
`localParams.toSelfDelay` (BOLT 2: `to_self_delay` delays the *other*
side's output). -/
def commitmentPairOfBalances (localParams remoteParams : ChannelParams)
    (b : Balance) (fee number : Nat) (funder : Direction) : CommitmentPair :=
  let funding := b.localSat + b.remoteSat
  { localCommitment :=
      { holder := .local
        commitmentNumber := number
        fundingValueSat := funding
        toLocalSat := if funder = .local then b.localSat - fee else b.localSat
        toRemoteSat := if funder = .remote then b.remoteSat - fee else b.remoteSat
        htlcs := []
        feeSat := fee
        contestDelay := remoteParams.toSelfDelay
        anchorOutputs := localParams.anchorOutputs }
    remoteCommitment :=
      { holder := .remote
        commitmentNumber := number
        fundingValueSat := funding
        toLocalSat := if funder = .remote then b.remoteSat - fee else b.remoteSat
        toRemoteSat := if funder = .local then b.localSat - fee else b.localSat
        htlcs := []
        feeSat := fee
        contestDelay := localParams.toSelfDelay
        anchorOutputs := remoteParams.anchorOutputs } }

theorem commitmentPair_funding (localParams remoteParams : ChannelParams)
    (b : Balance) (fee number : Nat) (funder : Direction) :
    (commitmentPairOfBalances localParams remoteParams b fee number funder).localCommitment.fundingValueSat =
        b.localSat + b.remoteSat ∧
      (commitmentPairOfBalances localParams remoteParams b fee number funder).remoteCommitment.fundingValueSat =
        b.localSat + b.remoteSat := by
  simp [commitmentPairOfBalances]

/-- The two commitments are held by different parties. -/
theorem commitmentPair_holders_differ (localParams remoteParams : ChannelParams)
    (b : Balance) (fee number : Nat) (funder : Direction) :
    (commitmentPairOfBalances localParams remoteParams b fee number funder).localCommitment.holder ≠
      (commitmentPairOfBalances localParams remoteParams b fee number funder).remoteCommitment.holder := by
  simp [commitmentPairOfBalances]

/-- Asymmetric CSV delays: if the two endpoints chose different
`to_self_delay` values, the two commitment transactions have different
`contestDelay`. -/
theorem commitmentPair_contestDelay_asymmetry
    (localParams remoteParams : ChannelParams) (b : Balance) (fee number : Nat)
    (funder : Direction) (h : localParams.toSelfDelay ≠ remoteParams.toSelfDelay) :
    (commitmentPairOfBalances localParams remoteParams b fee number funder).localCommitment.contestDelay ≠
      (commitmentPairOfBalances localParams remoteParams b fee number funder).remoteCommitment.contestDelay := by
  simpa [commitmentPairOfBalances] using h.symm

/-- With a zero fee and the local node as funder, the two `to_local`
outputs differ whenever the off-chain balances differ. -/
theorem commitmentPair_toLocal_asymmetry
    (localParams remoteParams : ChannelParams) (b : Balance) (number : Nat)
    (h : b.localSat ≠ b.remoteSat) :
    (commitmentPairOfBalances localParams remoteParams b 0 number .local).localCommitment.toLocalSat ≠
      (commitmentPairOfBalances localParams remoteParams b 0 number .local).remoteCommitment.toLocalSat := by
  simpa [commitmentPairOfBalances] using h

end LnLean.Channel
