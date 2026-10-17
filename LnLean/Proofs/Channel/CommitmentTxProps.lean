import LnLean.Channel.Commitment
import LnLean.Channel.Types
import LnLean.Bitcoin.Seam

/-!
# LnLean.Proofs.Channel.CommitmentTxProps

English claim.  This module isolates the value/ordering core of the
commitment-transaction construction used by `LnLean.Channel.Commitment`.
For a commitment with no HTLCs the output list is exactly

* `to_local`, `to_remote` when `option_anchors` is not negotiated, and
* `to_local`, `to_remote`, `to_local_anchor`, `to_remote_anchor` when it is
  (with the two 330-satoshi anchors supplied by `anchorOutputSat`),

and its output value plus the commitment fee reconstructs the funding value
whenever the BOLT 3 residual `funding - fee - toLocal - anchors` does not
underflow.  Adding one untrimmed HTLC adds exactly one `htlc` output; adding
a dust HTLC adds none.  The local and remote commitment records are not
symmetric: the funder's own output pays the fee on both transactions, each
transaction's CSV delay is the *counterparty's* `to_self_delay`, and the same
off-chain balance appears as `to_local` on one transaction and as `to_remote`
on the other.  The commitment number is a construction parameter: it is not
recoverable from the output list, and it only changes on the two BOLT 2
counter-advancing events modelled by `CommitmentCounterStep`.

BOLT sections.
* BOLT 3 §2 `Commitment Transaction` (`03-transactions.md:83-353`):
  output set and trimming requirements at `:102-155` and `:305-353`,
  anchors at `:148-198`.
* BOLT 3 §4 `Fees` (`03-transactions.md:464-530`): expected weight
  `724 + 172 * htlcs` (no anchors) or `1124 + 172 * htlcs` (anchors) at
  `:490-502`, and the floor-divided base fee at `:518-523`.
* BOLT 3 `Commitment Transaction Construction` (`:705-735`): subtract the
  base fee (and the two anchors) from the funder, then sort outputs.
* BOLT 2 §3 `commitment_signed` / `revoke_and_ack`
  (`02-peer-protocol.md:3097-3249`) and `to_self_delay`
  (`02-peer-protocol.md:750-752`).

rust-lightning anchors at `fe4900930c6bd5786ec4203274d7cf312776a5a6`.
* `lightning/src/sign/tx_builder.rs:984-1145`
  (`TxBuilder::build_commitment_transaction` at this commit; the function
  moved out of `chan_utils.rs`), especially the HTLC dust test at `:997-1025`,
  the funder subtraction at `:1048-1076`, and output trimming at `:1078-1097`.
* `lightning/src/ln/chan_utils.rs:1713-1740`
  (`CommitmentTransaction::new`, commitment number is a construction input),
  `:1887-1945` (`insert_non_htlc_outputs`: non-zero outputs and the
  conditional anchors), `:275-298` (`COMMITMENT_TX_WEIGHT_PER_HTLC = 172`,
  base weights and `commit_tx_fee_sat`).

What is explicitly NOT modelled.
* The obscured commitment number (`SHA256(payment_basepoint || ...)` XOR),
  `nVersion`, `nLockTime`, `nSequence`, signature witnesses, and txid bytes.
* BIP 69+CLTV output *sorting*: the model emits outputs in the fixed group
  order `to_local, to_remote, HTLCs, anchors`.  This order is deterministic
  but is not the sorted order required at the end of BOLT 3 §6.
* The single-anchor exception (no HTLCs and one commitment output below
  dust): `Commitment.commitmentOutputs` always emits both anchors when
  `anchorOutputs = true`.
* Dust trimming of `to_local`/`to_remote` against the broadcaster's dust
  limit: the model trims only on `= 0`, so callers must pass pre-trimmed
  values.  HTLC dust is modelled separately by `Commitment.addHtlc`, whose
  threshold takes the second-stage HTLC fee as a parameter.
* HTLC second-stage transactions, `shared_anchor`, `zero_fee_commitments`,
  and fee bumping.
* The refinement relation between `LnLean.Channel.State.Step` and the
  isolated `CommitmentCounterStep` (module import boundary; see the report).
-/

namespace LnLean.Channel

set_option autoImplicit false

open LnLean

/-! ## Output groups -/

/-- The `to_local` group of the output list, omitted when the value is zero. -/
def Commitment.toLocalOutputs (c : Commitment) : List CommitmentOutput :=
  if c.toLocalSat = 0 then [] else [CommitmentOutput.toLocal c.toLocalSat]

/-- The `to_remote` group of the output list, omitted when the value is zero. -/
def Commitment.toRemoteOutputs (c : Commitment) : List CommitmentOutput :=
  if c.toRemoteSat = 0 then [] else [CommitmentOutput.toRemote c.toRemoteSat]

/-- The HTLC outputs, in the order of `c.htlcs`. -/
def Commitment.htlcOutputs (c : Commitment) : List CommitmentOutput :=
  c.htlcs.map (fun h => CommitmentOutput.htlc h.direction h.amountSat)

/-- The anchor group: two outputs iff `option_anchors` is negotiated. -/
def Commitment.anchorOutputsList (c : Commitment) : List CommitmentOutput :=
  if c.anchorOutputs then
    [CommitmentOutput.localAnchor, CommitmentOutput.remoteAnchor]
  else []

/-- The total anchor value emitted by the model: `2 * 330` satoshis when
anchors are negotiated, zero otherwise. -/
def commitmentAnchorTotal (anchors : Bool) : Nat :=
  if anchors then 2 * anchorOutputSat else 0

theorem commitmentAnchorTotal_false : commitmentAnchorTotal false = 0 := rfl

theorem commitmentAnchorTotal_true :
    commitmentAnchorTotal true = 2 * anchorOutputSat := rfl

/-- The output list is exactly the concatenation of its four groups.  This is
the structural form used by all value and count lemmas below. -/
theorem Commitment.commitmentOutputs_eq_decomposition (c : Commitment) :
    c.commitmentOutputs =
      c.toLocalOutputs ++
        (c.toRemoteOutputs ++ (c.htlcOutputs ++ c.anchorOutputsList)) := by
  simp [Commitment.commitmentOutputs, Commitment.toLocalOutputs,
    Commitment.toRemoteOutputs, Commitment.htlcOutputs,
    Commitment.anchorOutputsList]

/-- The anchor value of a record agrees with `commitmentAnchorTotal`. -/
theorem Commitment.anchorOutputValue_eq_total (c : Commitment) :
    c.anchorOutputValue = commitmentAnchorTotal c.anchorOutputs := rfl

/-! ## Sum of output values -/

/-- Sum of the satoshi values of a commitment output list. -/
def outputsValue (l : List CommitmentOutput) : Nat :=
  (l.map CommitmentOutput.value).sum

theorem outputsValue_append (a b : List CommitmentOutput) :
    outputsValue (a ++ b) = outputsValue a + outputsValue b := by
  induction a with
  | nil => simp [outputsValue]
  | cons x xs _ =>
      simp [outputsValue, Nat.add_assoc]

theorem outputsValue_toLocalOutputs (c : Commitment) :
    outputsValue c.toLocalOutputs = c.toLocalSat := by
  unfold Commitment.toLocalOutputs outputsValue
  by_cases h : c.toLocalSat = 0 <;> simp [h, CommitmentOutput.value]

theorem outputsValue_toRemoteOutputs (c : Commitment) :
    outputsValue c.toRemoteOutputs = c.toRemoteSat := by
  unfold Commitment.toRemoteOutputs outputsValue
  by_cases h : c.toRemoteSat = 0 <;> simp [h, CommitmentOutput.value]

theorem outputsValue_htlcOutputs (c : Commitment) :
    outputsValue c.htlcOutputs = c.htlcOutputValue := by
  unfold Commitment.htlcOutputs outputsValue
  rw [Commitment.htlcOutputValue_eq_sum]
  exact congrArg List.sum (map_htlcOutput_value c)

theorem outputsValue_anchorOutputsList (c : Commitment) :
    outputsValue c.anchorOutputsList = c.anchorOutputValue := by
  unfold Commitment.anchorOutputsList outputsValue
  by_cases h : c.anchorOutputs
  · simp [h, CommitmentOutput.value, Commitment.anchorOutputValue, anchorOutputSat]
  · simp [h, Commitment.anchorOutputValue]

/-- The sum of the emitted output values is `totalOutputValue`.  A zero-valued
`to_local`/`to_remote` is omitted from the list but contributes zero, so the
identity holds in both trimmed and untrimmed cases. -/
theorem Commitment.outputsValue_commitmentOutputs (c : Commitment) :
    outputsValue c.commitmentOutputs = c.totalOutputValue := by
  rw [Commitment.commitmentOutputs_eq_decomposition]
  simp only [outputsValue_append, outputsValue_toLocalOutputs,
    outputsValue_toRemoteOutputs, outputsValue_htlcOutputs,
    outputsValue_anchorOutputsList]
  unfold Commitment.totalOutputValue
  omega

/-! ## An explicit construction with HTLCs -/

/-- Build a commitment transaction record from the BOLT 3 construction data.
`toLocal` is the broadcaster's output before subtracting the fee, the HTLC
value and the anchors; `toRemote` is the residual.  Callers must supply
pre-trimmed `htlcs` and a `toLocal` that does not underflow. -/
def buildCommitment (holder : Direction) (number funding fee toLocal : Nat)
    (htlcs : List CommitmentHTLCOutput) (contestDelay : Nat) (anchors : Bool) :
    Commitment :=
  { holder := holder
    commitmentNumber := number
    fundingValueSat := funding
    toLocalSat := toLocal
    toRemoteSat :=
      funding - fee - toLocal - htlcOutputsValue htlcs - commitmentAnchorTotal anchors
    htlcs := htlcs
    feeSat := fee
    contestDelay := contestDelay
    anchorOutputs := anchors }

theorem buildCommitment_commitmentNumber (holder : Direction) (number funding fee
    toLocal : Nat) (htlcs : List CommitmentHTLCOutput) (contestDelay : Nat)
    (anchors : Bool) :
    (buildCommitment holder number funding fee toLocal htlcs contestDelay anchors).commitmentNumber =
      number := rfl

theorem buildCommitment_htlcs (holder : Direction) (number funding fee toLocal : Nat)
    (htlcs : List CommitmentHTLCOutput) (contestDelay : Nat) (anchors : Bool) :
    (buildCommitment holder number funding fee toLocal htlcs contestDelay anchors).htlcs =
      htlcs := rfl

/-- Conservation for the explicit construction: if the fee, the broadcaster's
output, the untrimmed HTLC values and the anchors fit inside the funding
value, then the emitted output values plus the fee reconstruct the funding
value exactly. -/
theorem buildCommitment_conservation (holder : Direction) (number funding fee
    toLocal : Nat) (htlcs : List CommitmentHTLCOutput) (contestDelay : Nat)
    (anchors : Bool)
    (h : fee + toLocal + htlcOutputsValue htlcs + commitmentAnchorTotal anchors ≤ funding) :
    outputsValue
        (buildCommitment holder number funding fee toLocal htlcs contestDelay anchors).commitmentOutputs
      + fee = funding := by
  rw [Commitment.outputsValue_commitmentOutputs]
  unfold Commitment.totalOutputValue Commitment.htlcOutputValue
    Commitment.anchorOutputValue buildCommitment
  simp only
  have hanchor : (if anchors then 2 * anchorOutputSat else 0) =
      commitmentAnchorTotal anchors := rfl
  rw [hanchor]
  omega

/-! ## The zero-HTLC commitment -/

theorem zeroHtlcCommitment_outputs_noAnchors (holder : Direction) (number funding
    toLocal fee contestDelay : Nat) (hL : toLocal ≠ 0)
    (hR : funding - fee - toLocal ≠ 0) :
    (zeroHtlcCommitment holder number funding toLocal fee contestDelay false).commitmentOutputs =
      [CommitmentOutput.toLocal toLocal,
       CommitmentOutput.toRemote (funding - fee - toLocal)] := by
  simp [zeroHtlcCommitment, Commitment.commitmentOutputs, hL, hR]

theorem zeroHtlcCommitment_outputs_anchors (holder : Direction) (number funding
    toLocal fee contestDelay : Nat) (hL : toLocal ≠ 0)
    (hR : funding - fee - toLocal - 2 * anchorOutputSat ≠ 0) :
    (zeroHtlcCommitment holder number funding toLocal fee contestDelay true).commitmentOutputs =
      [CommitmentOutput.toLocal toLocal,
       CommitmentOutput.toRemote (funding - fee - toLocal - 2 * anchorOutputSat),
       CommitmentOutput.localAnchor,
       CommitmentOutput.remoteAnchor] := by
  simp [zeroHtlcCommitment, Commitment.commitmentOutputs,
    anchorOutputSat] at hR ⊢
  simp [hL, hR]

/-- The zero-HTLC commitment has exactly two outputs without anchors and four
with anchors, assuming both non-anchor outputs are non-zero. -/
theorem zeroHtlcCommitment_outputs_length (holder : Direction) (number funding
    toLocal fee contestDelay : Nat) (anchors : Bool) (hL : toLocal ≠ 0)
    (hR : (zeroHtlcCommitment holder number funding toLocal fee contestDelay anchors).toRemoteSat ≠ 0) :
    (zeroHtlcCommitment holder number funding toLocal fee contestDelay anchors).commitmentOutputs.length =
      2 + (if anchors then 2 else 0) := by
  by_cases ha : anchors
  · simp [zeroHtlcCommitment, Commitment.commitmentOutputs, ha] at hR ⊢
    simp [hL, hR]
  · simp [zeroHtlcCommitment, Commitment.commitmentOutputs, ha] at hR ⊢
    simp [hL, hR]

/-- Zero-HTLC conservation.  The hypothesis is exactly BOLT 3's requirement
that the funder can cover the fee and the two anchors; without it the
model's `Nat` subtraction silently truncates `to_remote` at zero. -/
theorem zeroHtlcCommitment_conservation (holder : Direction) (number funding
    toLocal fee contestDelay : Nat) (anchors : Bool)
    (h : fee + toLocal + commitmentAnchorTotal anchors ≤ funding) :
    outputsValue
        (zeroHtlcCommitment holder number funding toLocal fee contestDelay anchors).commitmentOutputs
      + fee = funding := by
  rw [Commitment.outputsValue_commitmentOutputs]
  unfold Commitment.totalOutputValue Commitment.htlcOutputValue
    Commitment.anchorOutputValue zeroHtlcCommitment commitmentAnchorTotal at *
  simp only [htlcOutputsValue, Nat.add_zero]
  by_cases ha : anchors <;> simp [ha] at * <;> omega

/-! ## Adding one HTLC -/

/-- Add one HTLC output using the BOLT 3 dust test.  The threshold is the
broadcaster's dust limit plus the second-stage HTLC fee, matching
`03-transactions.md:333-346` and `tx_builder.rs:997-1008`. -/
def Commitment.addHtlc (dustLimitSat htlcTxFeeSat : Nat) (c : Commitment)
    (h : CommitmentHTLCOutput) : Commitment :=
  if h.amountSat < dustLimitSat + htlcTxFeeSat then c
  else { c with htlcs := c.htlcs ++ [h] }

/-- A dust HTLC leaves the output list unchanged. -/
theorem Commitment.addHtlc_dust (c : Commitment) (h : CommitmentHTLCOutput)
    (dustLimitSat htlcTxFeeSat : Nat)
    (hd : h.amountSat < dustLimitSat + htlcTxFeeSat) :
    (c.addHtlc dustLimitSat htlcTxFeeSat h).commitmentOutputs = c.commitmentOutputs := by
  simp [Commitment.addHtlc, hd]

/-- A non-dust HTLC inserts exactly one `htlc` output, after the existing HTLC
outputs and before the anchor group. -/
theorem Commitment.addHtlc_outputs (c : Commitment) (h : CommitmentHTLCOutput)
    (dustLimitSat htlcTxFeeSat : Nat)
    (hnd : ¬ h.amountSat < dustLimitSat + htlcTxFeeSat) :
    (c.addHtlc dustLimitSat htlcTxFeeSat h).commitmentOutputs =
      c.toLocalOutputs ++
        (c.toRemoteOutputs ++
          ((c.htlcOutputs ++ [CommitmentOutput.htlc h.direction h.amountSat]) ++
            c.anchorOutputsList)) := by
  simp [Commitment.addHtlc, hnd, Commitment.commitmentOutputs,
    Commitment.toLocalOutputs, Commitment.toRemoteOutputs,
    Commitment.htlcOutputs, Commitment.anchorOutputsList, List.map_append]

/-- A non-dust HTLC increases the output-list length by exactly one. -/
theorem Commitment.addHtlc_length (c : Commitment) (h : CommitmentHTLCOutput)
    (dustLimitSat htlcTxFeeSat : Nat)
    (hnd : ¬ h.amountSat < dustLimitSat + htlcTxFeeSat) :
    (c.addHtlc dustLimitSat htlcTxFeeSat h).commitmentOutputs.length =
      c.commitmentOutputs.length + 1 := by
  rw [Commitment.addHtlc_outputs c h dustLimitSat htlcTxFeeSat hnd,
    Commitment.commitmentOutputs_eq_decomposition c]
  simp [List.length_append]
  omega

/-- Number of `htlc` constructors in an output list. -/
def htlcOutputCount : List CommitmentOutput → Nat
  | [] => 0
  | CommitmentOutput.htlc _ _ :: t => 1 + htlcOutputCount t
  | _ :: t => htlcOutputCount t

theorem htlcOutputCount_append (a b : List CommitmentOutput) :
    htlcOutputCount (a ++ b) = htlcOutputCount a + htlcOutputCount b := by
  induction a with
  | nil => simp [htlcOutputCount]
  | cons x xs ih =>
      cases x <;> simp [htlcOutputCount, ih] <;> omega

theorem htlcOutputCount_map_htlc (l : List CommitmentHTLCOutput) :
    htlcOutputCount
        (l.map (fun h => CommitmentOutput.htlc h.direction h.amountSat)) =
      l.length := by
  induction l with
  | nil => rfl
  | cons h t ih =>
      simp only [List.map_cons, htlcOutputCount, ih, List.length_cons]
      omega

theorem Commitment.htlcOutputCount_commitmentOutputs (c : Commitment) :
    htlcOutputCount c.commitmentOutputs = c.htlcs.length := by
  rw [Commitment.commitmentOutputs_eq_decomposition]
  simp only [htlcOutputCount_append, Commitment.toLocalOutputs,
    Commitment.toRemoteOutputs, Commitment.htlcOutputs,
    Commitment.anchorOutputsList]
  by_cases hL : c.toLocalSat = 0
  · by_cases hR : c.toRemoteSat = 0
    · by_cases hA : c.anchorOutputs <;>
        simp [hL, hR, hA, htlcOutputCount, htlcOutputCount_map_htlc]
    · by_cases hA : c.anchorOutputs <;>
        simp [hL, hR, hA, htlcOutputCount, htlcOutputCount_map_htlc]
  · by_cases hR : c.toRemoteSat = 0
    · by_cases hA : c.anchorOutputs <;>
        simp [hL, hR, hA, htlcOutputCount, htlcOutputCount_map_htlc]
    · by_cases hA : c.anchorOutputs <;>
        simp [hL, hR, hA, htlcOutputCount, htlcOutputCount_map_htlc]

/-- A non-dust HTLC increases the number of HTLC outputs by exactly one. -/
theorem Commitment.addHtlc_htlcOutputCount (c : Commitment) (h : CommitmentHTLCOutput)
    (dustLimitSat htlcTxFeeSat : Nat)
    (hnd : ¬ h.amountSat < dustLimitSat + htlcTxFeeSat) :
    htlcOutputCount (c.addHtlc dustLimitSat htlcTxFeeSat h).commitmentOutputs =
      htlcOutputCount c.commitmentOutputs + 1 := by
  rw [Commitment.addHtlc_outputs c h dustLimitSat htlcTxFeeSat hnd,
    Commitment.commitmentOutputs_eq_decomposition c]
  simp only [htlcOutputCount_append, htlcOutputCount]
  omega

/-- A dust HTLC leaves the HTLC-output count unchanged. -/
theorem Commitment.addHtlc_htlcOutputCount_dust (c : Commitment)
    (h : CommitmentHTLCOutput) (dustLimitSat htlcTxFeeSat : Nat)
    (hd : h.amountSat < dustLimitSat + htlcTxFeeSat) :
    htlcOutputCount (c.addHtlc dustLimitSat htlcTxFeeSat h).commitmentOutputs =
      htlcOutputCount c.commitmentOutputs := by
  simp [Commitment.addHtlc, hd]

/-! ## Local/remote asymmetry -/

/-- The funder pays the fee on **both** commitments.  For a local funder the
fee comes out of the local balance, which is `to_local` on the local
transaction and `to_remote` on the remote transaction. -/
theorem commitmentPair_fee_owner_local (localParams remoteParams : ChannelParams)
    (b : Balance) (fee number : Nat) (h : fee ≤ b.localSat) :
    let p := commitmentPairOfBalances localParams remoteParams b fee number Direction.local
    p.localCommitment.toLocalSat + fee = b.localSat ∧
      p.localCommitment.toRemoteSat = b.remoteSat ∧
      p.remoteCommitment.toLocalSat = b.remoteSat ∧
      p.remoteCommitment.toRemoteSat + fee = b.localSat := by
  simp [commitmentPairOfBalances, Nat.sub_add_cancel h]

/-- The symmetric statement when the remote party funds the channel. -/
theorem commitmentPair_fee_owner_remote (localParams remoteParams : ChannelParams)
    (b : Balance) (fee number : Nat) (h : fee ≤ b.remoteSat) :
    let p := commitmentPairOfBalances localParams remoteParams b fee number Direction.remote
    p.localCommitment.toLocalSat = b.localSat ∧
      p.localCommitment.toRemoteSat + fee = b.remoteSat ∧
      p.remoteCommitment.toLocalSat + fee = b.remoteSat ∧
      p.remoteCommitment.toRemoteSat = b.localSat := by
  simp [commitmentPairOfBalances, Nat.sub_add_cancel h]

/-- The exact CSV delays: each transaction delays the broadcaster's output by
the *counterparty's* `to_self_delay`. -/
theorem commitmentPair_contestDelay_exact (localParams remoteParams : ChannelParams)
    (b : Balance) (fee number : Nat) (funder : Direction) :
    let p := commitmentPairOfBalances localParams remoteParams b fee number funder
    p.localCommitment.contestDelay = remoteParams.toSelfDelay ∧
      p.remoteCommitment.contestDelay = localParams.toSelfDelay := by
  simp [commitmentPairOfBalances]

/-- The two output *values* swap roles: the same off-chain balance is
`to_local` on one transaction and `to_remote` on the other.  This is the
output-level content of the local/remote asymmetry. -/
theorem commitmentPair_output_values_swap (localParams remoteParams : ChannelParams)
    (b : Balance) (fee number : Nat) (funder : Direction) :
    let p := commitmentPairOfBalances localParams remoteParams b fee number funder
    p.localCommitment.toLocalSat = p.remoteCommitment.toRemoteSat ∧
      p.localCommitment.toRemoteSat = p.remoteCommitment.toLocalSat := by
  simp [commitmentPairOfBalances]

/-- Without anchors, the two commitment records conserve the funding value:
output sum plus fee equals the funding value. -/
theorem commitmentPair_conservation_noAnchors (localParams remoteParams : ChannelParams)
    (b : Balance) (fee number : Nat) (funder : Direction)
    (hA : localParams.anchorOutputs = false)
    (hB : remoteParams.anchorOutputs = false)
    (hf : fee ≤ (if funder = Direction.local then b.localSat else b.remoteSat)) :
    let p := commitmentPairOfBalances localParams remoteParams b fee number funder
    p.localCommitment.totalOutputValue + fee = p.localCommitment.fundingValueSat ∧
      p.remoteCommitment.totalOutputValue + fee = p.remoteCommitment.fundingValueSat := by
  cases funder <;>
    simp [commitmentPairOfBalances, hA, hB, Commitment.totalOutputValue,
      Commitment.htlcOutputValue, Commitment.anchorOutputValue, htlcOutputsValue] at hf ⊢ <;>
    omega

/-- Model gap, stated explicitly: with anchors the pair construction subtracts
only the fee from the funder and **not** the 660 satoshi anchor total, so the
output sum plus fee exceeds the funding value by exactly `2 * 330`.  The
BOLT 3 construction subtracts the anchors from the funder as well
(`03-transactions.md:319-324`); fixing this requires editing
`LnLean.Channel.Commitment` (A3-owned), so B09 records it instead. -/
-- OBLIGATION: LN-COMMIT-005 `commitmentPairOfBalances` must subtract the two anchors from the funder on both commitments; the current A3 model subtracts only the fee.
theorem commitmentPair_conservation_anchors_gap (localParams remoteParams : ChannelParams)
    (b : Balance) (fee number : Nat) (funder : Direction)
    (hA : localParams.anchorOutputs = true)
    (hB : remoteParams.anchorOutputs = true)
    (hf : fee ≤ (if funder = Direction.local then b.localSat else b.remoteSat)) :
    let p := commitmentPairOfBalances localParams remoteParams b fee number funder
    p.localCommitment.totalOutputValue + fee =
        p.localCommitment.fundingValueSat + 2 * anchorOutputSat ∧
      p.remoteCommitment.totalOutputValue + fee =
        p.remoteCommitment.fundingValueSat + 2 * anchorOutputSat := by
  cases funder <;>
    simp [commitmentPairOfBalances, hA, hB, Commitment.totalOutputValue,
      Commitment.htlcOutputValue, Commitment.anchorOutputValue, htlcOutputsValue] at hf ⊢ <;>
    omega

/-! ## Output ordering is deterministic -/

/-- The group decomposition fixes the order: `to_local`, `to_remote`, HTLCs,
anchors.  The output list is a function of the record, so the order has no
hidden freedom. -/
-- OBLIGATION: LN-COMMIT-006 BOLT 3 §6 requires BIP 69+CLTV sorting of the final outputs; the model fixes the group order instead, so sorted-order equivalence is open.
theorem commitmentOutputs_deterministic (c c' : Commitment) (h : c = c') :
    c.commitmentOutputs = c'.commitmentOutputs := by
  rw [h]

/-- In a zero-HTLC anchor commitment the two anchors are the last two
outputs. -/
-- OBLIGATION: LN-COMMIT-004 BOLT 3's single-anchor exception (no HTLCs and one output below dust) is not modelled: `commitmentOutputs` always emits both anchors when `anchorOutputs = true`.
theorem zeroHtlcCommitment_last_two_anchors (holder : Direction) (number funding
    toLocal fee contestDelay : Nat) (hL : toLocal ≠ 0)
    (hR : funding - fee - toLocal - 2 * anchorOutputSat ≠ 0) :
    (zeroHtlcCommitment holder number funding toLocal fee contestDelay true).commitmentOutputs.drop 2 =
      [CommitmentOutput.localAnchor, CommitmentOutput.remoteAnchor] := by
  rw [zeroHtlcCommitment_outputs_anchors holder number funding toLocal fee
    contestDelay hL hR]
  rfl

/-! ## The commitment number -/

/-- The commitment number is carried by the construction and does not affect
the output list. -/
theorem commitmentOutputs_number_independent (c : Commitment) (n : Nat) :
    ({ c with commitmentNumber := n } : Commitment).commitmentOutputs =
      c.commitmentOutputs := rfl

/-- The commitment number is not recoverable from the output list: two records
with the same (empty) output list can carry different numbers. -/
theorem commitmentNumber_not_determined_by_outputs :
    ∃ c c' : Commitment,
      c.commitmentOutputs = c'.commitmentOutputs ∧
        c.commitmentNumber ≠ c'.commitmentNumber := by
  refine ⟨zeroHtlcCommitment Direction.local 0 0 0 0 0 false,
    zeroHtlcCommitment Direction.local 1 0 0 0 0 false, ?_, ?_⟩
  · simp [zeroHtlcCommitment, Commitment.commitmentOutputs]
  · simp [zeroHtlcCommitment]

/-- The counter fragment of the BOLT 2 transition relation, isolated so this
module can state the commitment-number law without importing
`LnLean.Channel.State` (outside the B09 wave-A import set).
`commitmentSigned` advances the *remote* counter, `revoke_and_ack` advances
the *local* counter; no other event in `State.Step` touches either counter. -/
inductive CommitmentCounterStep : Channel → Channel → Prop where
  | commitmentSigned (c : Channel) (h : c.phase = ChannelPhase.normal) :
      CommitmentCounterStep c
        { c with remoteCommitmentNumber := c.remoteCommitmentNumber + 1 }
  | revokeAndAck (c : Channel) (h : c.phase = ChannelPhase.normal) :
      CommitmentCounterStep c
        { c with localCommitmentNumber := c.localCommitmentNumber + 1 }

/-- Both counter-advancing events require the `normal` phase. -/
theorem commitmentCounterStep_requires_normal {c c' : Channel}
    (h : CommitmentCounterStep c c') : c.phase = ChannelPhase.normal := by
  cases h <;> assumption

/-- Under a counter step exactly one counter advances, by exactly one. -/
theorem commitmentCounterStep_exact {c c' : Channel}
    (h : CommitmentCounterStep c c') :
    (c'.localCommitmentNumber = c.localCommitmentNumber ∧
        c'.remoteCommitmentNumber = c.remoteCommitmentNumber + 1) ∨
      (c'.localCommitmentNumber = c.localCommitmentNumber + 1 ∧
        c'.remoteCommitmentNumber = c.remoteCommitmentNumber) := by
  cases h <;> simp

/-- Conditional form of the BOLT 2 law: for any transition relation that
refines `CommitmentCounterStep` (in the final tree, `LnLean.Channel.Step`),
a change of either commitment counter is exactly one of the two legal
counter advances.  The refinement hypothesis is the bridge that B09 cannot
discharge without importing `State.lean`; see the report. -/
-- OBLIGATION: LN-COMMIT-003 The refinement `LnLean.Channel.Step` → `CommitmentCounterStep` (and the identification of `Commitment.commitmentNumber` with the channel counter) is not proved: importing `State.lean` is outside the B09 import set.
theorem commitmentNumber_changes_only_on_valid_step
    {R : Channel → Channel → Prop}
    (hR : ∀ {c c' : Channel}, R c c' → CommitmentCounterStep c c')
    {c c' : Channel} (h : R c c')
    (_hchange : c'.localCommitmentNumber ≠ c.localCommitmentNumber ∨
      c'.remoteCommitmentNumber ≠ c.remoteCommitmentNumber) :
    (c'.localCommitmentNumber = c.localCommitmentNumber + 1 ∧
        c'.remoteCommitmentNumber = c.remoteCommitmentNumber) ∨
      (c'.localCommitmentNumber = c.localCommitmentNumber ∧
        c'.remoteCommitmentNumber = c.remoteCommitmentNumber + 1) := by
  rcases commitmentCounterStep_exact (hR h) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact Or.inl ⟨h1, h2⟩

/-! ## Deferred proof obligations -/

/-- The number of HTLC outputs of a built commitment is the number of HTLCs
it was constructed with (all inputs are assumed pre-trimmed). -/
theorem buildCommitment_htlcOutputCount (holder : Direction) (number funding fee
    toLocal : Nat) (htlcs : List CommitmentHTLCOutput) (contestDelay : Nat)
    (anchors : Bool) :
    htlcOutputCount
        (buildCommitment holder number funding fee toLocal htlcs contestDelay anchors).commitmentOutputs =
      htlcs.length := by
  simpa [buildCommitment] using
    Commitment.htlcOutputCount_commitmentOutputs
      (buildCommitment holder number funding fee toLocal htlcs contestDelay anchors)

/-- A zero-HTLC commitment emits no HTLC-typed output, for any anchor setting. -/
theorem zeroHtlcCommitment_no_htlcOutput (holder : Direction) (number funding
    toLocal fee contestDelay : Nat) (anchors : Bool) :
    htlcOutputCount
        (zeroHtlcCommitment holder number funding toLocal fee contestDelay anchors).commitmentOutputs =
      0 := by
  simpa [zeroHtlcCommitment] using
    Commitment.htlcOutputCount_commitmentOutputs
      (zeroHtlcCommitment holder number funding toLocal fee contestDelay anchors)

end LnLean.Channel
