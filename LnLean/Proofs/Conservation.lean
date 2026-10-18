import LnLean.Basic.Core
import LnLean.Bitcoin.Seam
import LnLean.Channel.Commitment

/-!
# LnLean.Proofs.Conservation

English claim.  A Lightning channel never creates value.  For every modelled
commitment transaction, the sum of its emitted outputs plus its commitment
fee equals the funding value.  The claim is preserved by each modelled
value-moving step:

* adding an HTLC output moves exactly the HTLC amount from the funder's
  balance output into a new HTLC output (and a dust HTLC produces no output
  and no debit);
* fulfilling or failing an HTLC removes its output and credits exactly the
  same amount to the receiver (fulfilment) or back to the funder (failure);
* a fee update moves the fee difference into or out of the payer's output;
* a mutual close with no in-flight HTLCs splits the funding value into the
  two closing outputs and the negotiated closing fee;
* a penalty sweep spends the outputs of a revoked commitment into one sweep
  output plus the penalty fee.

Consequently no finite sequence of such steps creates value: every
commitment reachable from a conserving commitment has outputs bounded by the
funding value.  Anchors are included as two 330-satoshi outputs when
`option_anchors` is set.

BOLT sections.
* BOLT 3 §2 `Commitment Transaction Outputs`
  (`refs/bolts/03-transactions.md:102-307`): `to_local`, `to_remote`,
  offered/received HTLC outputs, and the two anchor outputs.
* BOLT 3 §2 `Trimmed Outputs` (`:308-367`): an output below the dust limit is
  not produced and its value stays in the balance.
* BOLT 3 §4 `Fee Calculation` (`:466-576`): the commitment fee is
  `feerate_per_kw * weight / 1000`, rounded down.
* BOLT 3 §5 `Dust Limits` (`:583-620`).
* BOLT 2 `closing_signed` (`refs/bolts/02-peer-protocol.md:2411-2501`): a
  mutual close has no HTLCs and pays a negotiated closing fee.
* BOLT 5 `Revoked Transaction Close Handling`
  (`refs/bolts/05-onchain.md:510-621`): the punisher claims all outputs of
  the revoked commitment with a penalty transaction that pays a fee.

rust-lightning anchors at `fe4900930c6bd5786ec4203274d7cf312776a5a6`.
* `lightning/src/ln/chan_utils.rs:275-298` (`COMMITMENT_TX_WEIGHT_PER_HTLC`
  and `commit_tx_fee_sat`).
* `lightning/src/ln/chan_utils.rs:716-744` (`HTLCOutputInCommitment` and
  `to_bitcoin_amount`, the floor conversion to satoshis).
* `lightning/src/ln/chan_utils.rs:1778` and `:1842`
  (`nondust_htlcs_value_sum_sat`: the contract's output value sum is taken
  over *non-dust* HTLCs only).
* `lightning/src/ln/chan_utils.rs:1887-1966`
  (`insert_non_htlc_outputs`, including the 330-sat anchors).
* `lightning/src/chain/channelmonitor.rs:597-599` (a revoked-state HTLC
  transaction is resolved by the revocation path) and
  `:2402-2414` (justice transactions for revoked outputs).

What is NOT modelled.
* Wire encoding, transaction ordering, `nSequence`, signatures, witnesses,
  and script execution.  The equation is over output *values* only.
* The BOLT 2 `update_add_htlc` / `update_fulfill_htlc` / `update_fail_htlc`
  guard conditions and the SHA-256 preimage relation; those live in
  `LnLean.Channel.HTLC`.  That module cannot be imported together with
  `LnLean.Channel.Commitment` at the pinned tree because both declare a
  top-level `LnLean.Channel.HTLC` structure (see the report); this file
  therefore treats an HTLC as a `CommitmentHTLCOutput` and models settlement
  as a commitment-ledger operation.
* Second-stage HTLC transactions (HTLC-timeout/HTLC-success), their
  663/703 weights, and the second-stage fee split.
* Anchor child-pays-for-parent fee bumping, package relay, RBF, and the
  economics of penalty fees (BOLT 5 is a recommendation, not consensus).
* Whether the counterparty actually broadcasts the latest commitment, and
  watchtower liveness.  The theorem is about what the transaction does when
  it is built.
-/

namespace LnLean.Proofs

open LnLean
open LnLean.Channel

set_option autoImplicit false

/-! ## The conservation predicate -/

/-- A commitment conserves value when the sum of its emitted outputs plus
its commitment fee is exactly the funding value.  This is the BOLT 3
balance equation, stated on `Commitment.totalOutputValue`
(`LnLean/Channel/Commitment.lean`). -/
def CommitmentConserved (c : Commitment) : Prop :=
  c.totalOutputValue + c.feeSat = c.fundingValueSat

theorem commitmentConserved_iff (c : Commitment) :
    CommitmentConserved c ↔ c.totalOutputValue + c.feeSat = c.fundingValueSat :=
  Iff.rfl

/-- Conservation immediately rules out value creation: emitted outputs can
never exceed the funding value, because the fee is a natural number. -/
theorem conserved_no_value_creation (c : Commitment)
    (hc : CommitmentConserved c) :
    c.totalOutputValue ≤ c.fundingValueSat := by
  unfold CommitmentConserved at hc
  omega

/-- A conserving commitment's fee is exactly the residual funding value. -/
theorem conserved_fee_eq_residual (c : Commitment)
    (hc : CommitmentConserved c) :
    c.feeSat = c.fundingValueSat - c.totalOutputValue := by
  unfold CommitmentConserved at hc
  omega

/-- A checked finite example: 60000 + 39000 satoshis of outputs with a
1000-satoshi fee exactly spend a 100000-satoshi funding output. -/
theorem concrete_commitment_conserved :
    CommitmentConserved
      { holder := Direction.local
        commitmentNumber := 0
        fundingValueSat := 100000
        toLocalSat := 60000
        toRemoteSat := 39000
        htlcs := []
        feeSat := 1000
        contestDelay := 144
        anchorOutputs := false } := by
  unfold CommitmentConserved
  decide

/-! ## Moving value between a balance and an output -/

/-- Which of the two non-HTLC outputs of a commitment is debited or
credited.  `toLocal` is the holder's output (BOLT 3 §2). -/
inductive BalanceSide where
  | toLocal
  | toRemote
deriving Repr, DecidableEq, BEq

/-- The value currently assigned to one side of a commitment. -/
def balanceOn (c : Commitment) : BalanceSide → Nat
  | .toLocal => c.toLocalSat
  | .toRemote => c.toRemoteSat

/-- Remove `amountSat` from one side.  The caller is responsible for the
affordability condition, which is a hypothesis of the conservation lemmas. -/
def debitCommitment (c : Commitment) (side : BalanceSide) (amountSat : Nat) :
    Commitment :=
  match side with
  | .toLocal => { c with toLocalSat := c.toLocalSat - amountSat }
  | .toRemote => { c with toRemoteSat := c.toRemoteSat - amountSat }

/-- Add `amountSat` to one side. -/
def creditCommitment (c : Commitment) (side : BalanceSide) (amountSat : Nat) :
    Commitment :=
  match side with
  | .toLocal => { c with toLocalSat := c.toLocalSat + amountSat }
  | .toRemote => { c with toRemoteSat := c.toRemoteSat + amountSat }

@[simp] theorem fee_debit (c : Commitment) (side : BalanceSide)
    (amountSat : Nat) :
    (debitCommitment c side amountSat).feeSat = c.feeSat := by
  cases side <;> rfl

@[simp] theorem funding_debit (c : Commitment) (side : BalanceSide)
    (amountSat : Nat) :
    (debitCommitment c side amountSat).fundingValueSat = c.fundingValueSat := by
  cases side <;> rfl

@[simp] theorem fee_credit (c : Commitment) (side : BalanceSide)
    (amountSat : Nat) :
    (creditCommitment c side amountSat).feeSat = c.feeSat := by
  cases side <;> rfl

@[simp] theorem funding_credit (c : Commitment) (side : BalanceSide)
    (amountSat : Nat) :
    (creditCommitment c side amountSat).fundingValueSat = c.fundingValueSat := by
  cases side <;> rfl

/-- The output that funds an HTLC: the funder's own `to_local` when the
commitment is held by the funder, otherwise `to_remote`.  `funder` is the
local endpoint's `Direction` (`local` = offered by us). -/
def fundingSide (c : Commitment) (funder : Direction) : BalanceSide :=
  if c.holder = funder then .toLocal else .toRemote

@[simp] theorem htlcOutputValue_setToLocal (c : Commitment) (v : Nat) :
    ({ c with toLocalSat := v } : Commitment).htlcOutputValue =
      c.htlcOutputValue := rfl

@[simp] theorem htlcOutputValue_setToRemote (c : Commitment) (v : Nat) :
    ({ c with toRemoteSat := v } : Commitment).htlcOutputValue =
      c.htlcOutputValue := rfl

@[simp] theorem anchorOutputValue_setToLocal (c : Commitment) (v : Nat) :
    ({ c with toLocalSat := v } : Commitment).anchorOutputValue =
      c.anchorOutputValue := rfl

@[simp] theorem anchorOutputValue_setToRemote (c : Commitment) (v : Nat) :
    ({ c with toRemoteSat := v } : Commitment).anchorOutputValue =
      c.anchorOutputValue := rfl

@[simp] theorem anchorOutputValue_setHtlcs (c : Commitment)
    (hs : List CommitmentHTLCOutput) :
    ({ c with htlcs := hs } : Commitment).anchorOutputValue =
      c.anchorOutputValue := rfl

theorem totalOutputValue_setToLocal (c : Commitment) (v : Nat) :
    ({ c with toLocalSat := v } : Commitment).totalOutputValue =
      v + c.toRemoteSat + c.htlcOutputValue + c.anchorOutputValue := rfl

theorem totalOutputValue_setToRemote (c : Commitment) (v : Nat) :
    ({ c with toRemoteSat := v } : Commitment).totalOutputValue =
      c.toLocalSat + v + c.htlcOutputValue + c.anchorOutputValue := rfl

theorem totalOutputValue_setHtlcs (c : Commitment)
    (hs : List CommitmentHTLCOutput) :
    ({ c with htlcs := hs } : Commitment).totalOutputValue =
      c.toLocalSat + c.toRemoteSat + htlcOutputsValue hs +
        c.anchorOutputValue := by
  simp [Commitment.totalOutputValue, Commitment.htlcOutputValue]

theorem totalOutputValue_debit (c : Commitment) (side : BalanceSide)
    (amountSat : Nat) (h : amountSat ≤ balanceOn c side) :
    (debitCommitment c side amountSat).totalOutputValue =
      c.totalOutputValue - amountSat := by
  cases side <;>
    simp [debitCommitment, balanceOn, Commitment.totalOutputValue] at h ⊢ <;>
    omega

theorem totalOutputValue_credit (c : Commitment) (side : BalanceSide)
    (amountSat : Nat) :
    (creditCommitment c side amountSat).totalOutputValue =
      c.totalOutputValue + amountSat := by
  cases side <;>
    simp [creditCommitment, Commitment.totalOutputValue] <;>
    omega

/-- Debiting a balance and adding that same amount back as an output
preserves the output total, provided the balance covers the debit. -/
theorem debit_add_restore (c : Commitment) (side : BalanceSide)
    (amountSat : Nat) (h : amountSat ≤ balanceOn c side) :
    (debitCommitment c side amountSat).totalOutputValue + amountSat =
      c.totalOutputValue := by
  cases side <;>
    simp [debitCommitment, balanceOn, Commitment.totalOutputValue] at h ⊢ <;>
    omega

/-- Prepending one HTLC output increases `totalOutputValue` by exactly the
output's value. -/
theorem totalOutputValue_cons_htlc (c : Commitment)
    (h : CommitmentHTLCOutput) :
    ({ c with htlcs := h :: c.htlcs } : Commitment).totalOutputValue =
      c.totalOutputValue + h.amountSat := by
  rw [totalOutputValue_setHtlcs]
  simp [htlcOutputsValue, Commitment.totalOutputValue,
    Commitment.htlcOutputValue, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm]

/-! ## Adding an HTLC -/

/-- Add an HTLC output, replacing the corresponding balance with the HTLC
output (BOLT 3 §2: an offered HTLC is an output of the commitment, funded by
the offerer's balance). -/
def addHTLCOutput (c : Commitment) (h : CommitmentHTLCOutput) :
    Commitment :=
  let c' := debitCommitment c (fundingSide c h.direction) h.amountSat
  { c' with htlcs := h :: c'.htlcs }

theorem addHTLCOutput_total (c : Commitment) (h : CommitmentHTLCOutput)
    (hle : h.amountSat ≤ balanceOn c (fundingSide c h.direction)) :
    (addHTLCOutput c h).totalOutputValue = c.totalOutputValue := by
  dsimp only [addHTLCOutput]
  rw [totalOutputValue_cons_htlc]
  exact debit_add_restore c (fundingSide c h.direction) h.amountSat hle

/-- **Adding an HTLC preserves the conservation equation.**  The HTLC output
replaces the corresponding balance, so the output sum is unchanged and the
fee is unchanged. -/
theorem addHTLCOutput_conserved (c : Commitment) (h : CommitmentHTLCOutput)
    (hc : CommitmentConserved c)
    (hle : h.amountSat ≤ balanceOn c (fundingSide c h.direction)) :
    CommitmentConserved (addHTLCOutput c h) := by
  unfold CommitmentConserved at hc ⊢
  rw [addHTLCOutput_total c h hle]
  simpa [addHTLCOutput] using hc

/-- Dust-aware add.  An output strictly below the dust limit is not produced
(BOLT 3 §2 `Trimmed Outputs`), so neither the HTLC output nor a debit is
added: the value remains in the corresponding balance. -/
def addHTLCDustAware (dustLimitSat : Nat) (c : Commitment)
    (h : CommitmentHTLCOutput) : Commitment :=
  if h.amountSat < dustLimitSat then c else addHTLCOutput c h

/-- **Adding an HTLC preserves conservation even when dust is trimmed.** -/
theorem addHTLCDustAware_conserved (dustLimitSat : Nat) (c : Commitment)
    (h : CommitmentHTLCOutput) (hc : CommitmentConserved c)
    (hle : h.amountSat ≤ balanceOn c (fundingSide c h.direction)) :
    CommitmentConserved (addHTLCDustAware dustLimitSat c h) := by
  unfold addHTLCDustAware
  split
  · exact hc
  · exact addHTLCOutput_conserved c h hc hle

/-- A dust HTLC leaves the commitment outputs exactly as they were. -/
theorem addHTLCDustAware_dust (dustLimitSat : Nat) (c : Commitment)
    (h : CommitmentHTLCOutput) (hdust : h.amountSat < dustLimitSat) :
    addHTLCDustAware dustLimitSat c h = c := by
  unfold addHTLCDustAware
  simp [hdust]

/-! ## Fulfilling and failing an HTLC -/

theorem htlcOutputsValue_append (xs ys : List CommitmentHTLCOutput) :
    htlcOutputsValue (xs ++ ys) =
      htlcOutputsValue xs + htlcOutputsValue ys := by
  induction xs with
  | nil => simp [htlcOutputsValue]
  | cons h t ih => simp [htlcOutputsValue, ih, Nat.add_assoc]

/-- The total output value after replacing a middle segment of the HTLC list. -/
theorem totalOutputValue_htlcs_append (c : Commitment)
    (before after : List CommitmentHTLCOutput) :
    ({ c with htlcs := before ++ after } : Commitment).totalOutputValue =
      c.toLocalSat + c.toRemoteSat +
        (htlcOutputsValue before + htlcOutputsValue after) +
        c.anchorOutputValue := by
  rw [totalOutputValue_setHtlcs, htlcOutputsValue_append]

/-- Replace one HTLC output (decomposed as `before ++ h :: after`) by its
value in the list, and credit the same value to one balance.  The total
output value is unchanged: the value moves from an output slot to a balance
slot, never appears twice and never disappears. -/
theorem credit_replace_htlcs_total (c : Commitment)
    (before after : List CommitmentHTLCOutput) (h : CommitmentHTLCOutput)
    (side : BalanceSide) (hmem : c.htlcs = before ++ h :: after) :
    ({ creditCommitment c side h.amountSat with htlcs := before ++ after } :
        Commitment).totalOutputValue = c.totalOutputValue := by
  have hsum : htlcOutputsValue c.htlcs =
      htlcOutputsValue before + h.amountSat + htlcOutputsValue after := by
    rw [hmem, htlcOutputsValue_append]
    simp [htlcOutputsValue, Nat.add_assoc]
  cases side <;>
    (by_cases hanch : c.anchorOutputs <;>
      simp [creditCommitment, Commitment.totalOutputValue,
        Commitment.htlcOutputValue, Commitment.anchorOutputValue,
        htlcOutputsValue_append, hanch] at hsum ⊢ <;>
      omega)

/-- Settle one HTLC output at commitment level.  `before` and `after` are the
HTLC outputs surrounding it, so the caller cannot accidentally erase the
wrong (possibly equal-valued) entry.  A fulfilled HTLC credits the
counterparty of the offerer; a failed HTLC credits the offerer back.
`hadOutput = false` models a dust HTLC, which never had a commitment output
and therefore moves nothing. -/
def settleHTLCOutputAt (c : Commitment)
    (before after : List CommitmentHTLCOutput) (h : CommitmentHTLCOutput)
    (fulfilled hadOutput : Bool) : Commitment :=
  let creditor : Direction :=
    if fulfilled then h.direction.flip else h.direction
  if hadOutput then
    { creditCommitment c (fundingSide c creditor) h.amountSat with
        htlcs := before ++ after }
  else c

/-- **Fulfilling or failing an HTLC preserves the conservation equation.**
The HTLC output is removed and exactly its value is credited to the party
that receives it (the counterparty on fulfilment, the offerer on failure). -/
theorem settleHTLCOutputAt_conserved (c : Commitment)
    (before after : List CommitmentHTLCOutput) (h : CommitmentHTLCOutput)
    (fulfilled hadOutput : Bool) (hc : CommitmentConserved c)
    (hmem : c.htlcs = before ++ h :: after) :
    CommitmentConserved
      (settleHTLCOutputAt c before after h fulfilled hadOutput) := by
  unfold settleHTLCOutputAt
  cases hadOutput with
  | false => exact hc
  | true =>
      dsimp only
      simp only [ite_true]
      unfold CommitmentConserved at hc ⊢
      rw [credit_replace_htlcs_total c before after h
        (fundingSide c (if fulfilled then h.direction.flip else h.direction)) hmem]
      split <;> simpa using hc

/-- Fulfilment case of `settleHTLCOutputAt_conserved`, named for the BOLT 2
`update_fulfill_htlc` transition. -/
theorem fulfillHTLCOutput_conserved (c : Commitment)
    (before after : List CommitmentHTLCOutput) (h : CommitmentHTLCOutput)
    (hc : CommitmentConserved c)
    (hmem : c.htlcs = before ++ h :: after) :
    CommitmentConserved
      (settleHTLCOutputAt c before after h true true) :=
  settleHTLCOutputAt_conserved c before after h true true hc hmem

/-- Failure case of `settleHTLCOutputAt_conserved`, named for the BOLT 2
`update_fail_htlc` transition. -/
theorem failHTLCOutput_conserved (c : Commitment)
    (before after : List CommitmentHTLCOutput) (h : CommitmentHTLCOutput)
    (hc : CommitmentConserved c)
    (hmem : c.htlcs = before ++ h :: after) :
    CommitmentConserved
      (settleHTLCOutputAt c before after h false true) :=
  settleHTLCOutputAt_conserved c before after h false true hc hmem

/-- A dust HTLC has no commitment output; settling it is a no-op on the
commitment ledger.  Its off-chain balance update is outside this value
equation. -/
theorem settle_dust_noop (c : Commitment)
    (before after : List CommitmentHTLCOutput) (h : CommitmentHTLCOutput)
    (fulfilled : Bool) :
    settleHTLCOutputAt c before after h fulfilled false = c := rfl

/-! ## Fee updates -/

@[simp] theorem htlcOutputValue_setToRemoteFee (c : Commitment) (v f : Nat) :
    ({ c with toRemoteSat := v, feeSat := f } : Commitment).htlcOutputValue =
      c.htlcOutputValue := rfl

@[simp] theorem anchorOutputValue_setToRemoteFee (c : Commitment)
    (v f : Nat) :
    ({ c with toRemoteSat := v, feeSat := f } : Commitment).anchorOutputValue =
      c.anchorOutputValue := rfl

/-- Reprice a commitment by moving the fee difference into or out of the
`to_remote` output.  This is the value part of BOLT 2 `update_fee`; the
reserve/affordability checks are obligations of the fee workstream. -/
def repriceFee (c : Commitment) (newFeeSat : Nat) : Commitment :=
  { c with
    toRemoteSat := c.toRemoteSat + c.feeSat - newFeeSat
    feeSat := newFeeSat }

/-- **A fee update preserves conservation** when the payer's output plus the
old fee covers the new fee.  The added fee is exactly the value removed from
the output. -/
theorem repriceFee_conserved (c : Commitment) (newFeeSat : Nat)
    (hc : CommitmentConserved c)
    (h : newFeeSat ≤ c.toRemoteSat + c.feeSat) :
    CommitmentConserved (repriceFee c newFeeSat) := by
  unfold CommitmentConserved at hc ⊢
  simp [repriceFee, Commitment.totalOutputValue] at *
  omega

/-! ## Both commitment transactions of a channel -/

/-- **The two commitments produced by `commitmentPairOfBalances` conserve
value when anchors are disabled.**  The funder pays the same fee on both
transactions; the non-funder receives the remainder.

The anchor hypotheses are necessary: the current
`commitmentPairOfBalances` sets `anchorOutputs` from the parameters but does
not debit the two 330-satoshi anchor outputs, so with anchors the equation is
false.  `commitmentPair_anchorCounterexample` below is the checked
counterexample, and the report records this as an integration gap. -/
theorem commitmentPairOfBalances_conserved
    (localParams remoteParams : ChannelParams) (b : Balance)
    (fee number : Nat) (funder : Direction)
    (hLocalAnchors : localParams.anchorOutputs = false)
    (hRemoteAnchors : remoteParams.anchorOutputs = false)
    (hbal : fee ≤
      (if funder = Direction.local then b.localSat else b.remoteSat)) :
    CommitmentConserved
        (commitmentPairOfBalances localParams remoteParams b fee number
          funder).localCommitment ∧
      CommitmentConserved
        (commitmentPairOfBalances localParams remoteParams b fee number
          funder).remoteCommitment := by
  cases funder <;>
    simp_all [commitmentPairOfBalances, CommitmentConserved,
      Commitment.totalOutputValue, Commitment.htlcOutputValue,
      Commitment.anchorOutputValue, htlcOutputsValue] <;>
    omega

/-- Demo parameters for the anchor counterexample. -/
def demoParams (anchors : Bool) : ChannelParams :=
  { dustLimitSat := 546
    channelReserveSat := 1000
    toSelfDelay := 144
    maxHtlcValue := ⟨1000000000⟩
    htlcMinimum := ⟨1000⟩
    feerate := ⟨253⟩
    anchorOutputs := anchors }

/-- Demo balances for the anchor counterexample. -/
def demoBalance : Balance :=
  { localBalance := Msat.ofSat 60000
    remoteBalance := Msat.ofSat 39000 }

/-- **Checked counterexample to anchor-blind pair construction.**  With
anchors enabled, `commitmentPairOfBalances` emits 660 satoshis of anchor
outputs without debiting them from the funder, so the local commitment is not
conserving (its outputs plus fee exceed the funding value by 660).  This is a
real gap in the wave-A builder, not a weakness of the conservation claim. -/
theorem commitmentPair_anchorCounterexample :
    ¬ CommitmentConserved
      (commitmentPairOfBalances (demoParams true) (demoParams true)
        demoBalance 1000 0 Direction.local).localCommitment := by
  unfold CommitmentConserved
  decide

/-! ## Mutual close -/

/-- A mutual-close transaction: two closing outputs and a negotiated closing
fee (BOLT 2 `closing_signed`). -/
structure MutualCloseTx where
  fundingValueSat : Nat
  toLocalSat : Nat
  toRemoteSat : Nat
  closingFeeSat : Nat
deriving Repr, DecidableEq, BEq

def MutualCloseTx.totalOutputValue (t : MutualCloseTx) : Nat :=
  t.toLocalSat + t.toRemoteSat

def MutualCloseTx.conserved (t : MutualCloseTx) : Prop :=
  t.totalOutputValue + t.closingFeeSat = t.fundingValueSat

/-- Build a mutual-close transaction whose remote output is the remainder
after the local output and the closing fee. -/
def mutualCloseTx (funding toLocal closingFee : Nat) : MutualCloseTx :=
  { fundingValueSat := funding
    toLocalSat := toLocal
    toRemoteSat := funding - toLocal - closingFee
    closingFeeSat := closingFee }

/-- **A mutual close preserves the equation with the closing fee.**  The two
closing outputs plus the negotiated fee are exactly the funding value. -/
theorem mutualClose_conserved (funding toLocal closingFee : Nat)
    (h : closingFee + toLocal ≤ funding) :
    (mutualCloseTx funding toLocal closingFee).conserved := by
  unfold mutualCloseTx MutualCloseTx.conserved
    MutualCloseTx.totalOutputValue
  simp
  omega

/-! ## Penalty sweep -/

/-- A penalty transaction abstracted to values: it spends all outputs of one
revoked commitment, pays one sweep output, and keeps `penaltyFeeSat` as the
miner fee (BOLT 5 revoked-close handling). -/
structure PenaltySweepTx where
  sweptValueSat : Nat
  sweepOutputSat : Nat
  penaltyFeeSat : Nat
deriving Repr, DecidableEq, BEq

/-- Build the value part of a penalty sweep over the outputs of `c`. -/
def penaltySweepTx (c : Commitment) (penaltyFeeSat : Nat) : PenaltySweepTx :=
  { sweptValueSat := c.totalOutputValue
    sweepOutputSat := c.totalOutputValue - penaltyFeeSat
    penaltyFeeSat := penaltyFeeSat }

/-- The sweep output plus the penalty fee is exactly the swept value. -/
theorem penaltySweep_conserved (c : Commitment) (penaltyFeeSat : Nat)
    (hfee : penaltyFeeSat ≤ c.totalOutputValue) :
    (penaltySweepTx c penaltyFeeSat).sweepOutputSat +
        (penaltySweepTx c penaltyFeeSat).penaltyFeeSat =
      (penaltySweepTx c penaltyFeeSat).sweptValueSat := by
  simp [penaltySweepTx]
  omega

/-- **A penalty transaction preserves the channel equation.**  Substituting
the sweep equation into the revoked commitment's conservation equation gives
`sweep + penalty_fee + commitment_fee = funding`. -/
theorem penalty_preserves_channel_equation (c : Commitment)
    (penaltyFeeSat : Nat) (hc : CommitmentConserved c)
    (hfee : penaltyFeeSat ≤ c.totalOutputValue) :
    (penaltySweepTx c penaltyFeeSat).sweepOutputSat + penaltyFeeSat +
        c.feeSat = c.fundingValueSat := by
  unfold CommitmentConserved at hc
  simp [penaltySweepTx] at *
  omega

/-! ## Global statements: finite runs and channel ledgers -/

/-- Iterate a commitment step `n` times. -/
def CommitmentTrace (step : Commitment → Commitment) :
    Nat → Commitment → Commitment
  | 0, c => c
  | n + 1, c => step (CommitmentTrace step n c)

/-- **No finite run of conserving steps creates value.**  If a step function
preserves `CommitmentConserved`, then every iterate preserves it. -/
theorem trace_conserved (step : Commitment → Commitment)
    (hstep : ∀ c, CommitmentConserved c → CommitmentConserved (step c)) :
    ∀ n c, CommitmentConserved c →
      CommitmentConserved (CommitmentTrace step n c)
  | 0, _, hc => hc
  | n + 1, c, hc => hstep _ (trace_conserved step hstep n c hc)

/-- A channel ledger: one funding value and every commitment transaction
that the model has built for it (local, remote, and historical states). -/
structure ChannelLedger where
  fundingValueSat : Nat
  commitments : List Commitment

/-- Every commitment in the ledger spends the same funding output and is
conserving. -/
def ChannelLedger.AllConserved (l : ChannelLedger) : Prop :=
  ∀ c, c ∈ l.commitments →
    c.fundingValueSat = l.fundingValueSat ∧ CommitmentConserved c

/-- **Global conservation for a channel ledger**: no commitment in a
conserving ledger emits more than the channel's funding value. -/
theorem ledger_no_value_creation (l : ChannelLedger)
    (h : l.AllConserved) (c : Commitment) (hc : c ∈ l.commitments) :
    c.totalOutputValue ≤ l.fundingValueSat := by
  rcases h c hc with ⟨hfund, hcons⟩
  rw [← hfund]
  exact conserved_no_value_creation c hcons

/-! ## Open obligation -/

/-- Erase-based settlement: the same operation as
`settleHTLCOutputAt`, but locating the output with `List.erase` instead of a
caller-supplied decomposition.  This is the form needed by an HTLC-id-based
protocol transition. -/
def settleHTLCOutputErase (c : Commitment)
    (h : CommitmentHTLCOutput) (fulfilled hadOutput : Bool) : Commitment :=
  let creditor : Direction :=
    if fulfilled then h.direction.flip else h.direction
  if hadOutput then
    { creditCommitment c (fundingSide c creditor) h.amountSat with
        htlcs := c.htlcs.erase h }
  else c

/- The model derives `BEq` and `DecidableEq` separately; recover the
`LawfulBEq` instances needed by the `List.erase` lemmas.  The derived
implementations compare constructors and all fields, so these are the
model's actual equalities. -/
private instance : LawfulBEq Direction where
  eq_of_beq := by
    intro a b h
    cases a <;> cases b <;> first | rfl | exact Bool.noConfusion h
  rfl := by intro a; cases a <;> rfl

private instance : LawfulBEq HTLCState where
  eq_of_beq := by
    intro a b h
    cases a <;> cases b <;> first | rfl | exact Bool.noConfusion h
  rfl := by intro a; cases a <;> rfl

private instance : LawfulBEq CommitmentHTLCOutput where
  eq_of_beq := by
    intro a b h
    cases a with
    | mk da aa ca sa na =>
      cases b with
      | mk db ab cb sb nb =>
        simp [BEq.beq, instBEqCommitmentHTLCOutput.beq] at h
        rcases h with ⟨hda, haa, hca, hsa, hna⟩
        have hda' : da = db := LawfulBEq.eq_of_beq (α := Direction) hda
        have hsa' : sa = sb := LawfulBEq.eq_of_beq (α := HTLCState) hsa
        rw [hda', haa, hca, hsa', hna]
  rfl := by
    intro a
    cases a with
    | mk d am c s n =>
      have hd : instBEqDirection.beq d d = true := by cases d <;> rfl
      have hs : instBEqHTLCState.beq s s = true := by cases s <;> rfl
      simp [BEq.beq, instBEqCommitmentHTLCOutput.beq, hd, hs]

/-- An HTLC's value is at most the sum of all HTLC output values in a list
that contains it. -/
private theorem amount_le_htlcOutputsValue (l : List CommitmentHTLCOutput)
    (h : CommitmentHTLCOutput) (hmem : h ∈ l) :
    h.amountSat ≤ htlcOutputsValue l := by
  induction l with
  | nil => cases hmem
  | cons x xs ih =>
      simp only [htlcOutputsValue]
      by_cases hx : x = h
      · subst x
        omega
      · have hmem' : h ∈ xs := by
          rcases List.mem_cons.mp hmem with h_eq | h_in
          · exact (hx h_eq.symm).elim
          · exact h_in
        have hle := ih hmem'
        omega

/-- `List.erase` removes exactly one occurrence's value from the HTLC output
sum.  When several outputs have the same value, `erase` still removes one
list element, so the arithmetic is unchanged. -/
private theorem htlcOutputsValue_erase (l : List CommitmentHTLCOutput)
    (h : CommitmentHTLCOutput) (hmem : h ∈ l) :
    htlcOutputsValue (l.erase h) = htlcOutputsValue l - h.amountSat := by
  have hle := amount_le_htlcOutputsValue l h hmem
  rcases List.exists_erase_eq hmem with ⟨before, after, _, rfl, herase⟩
  rw [herase, htlcOutputsValue_append, htlcOutputsValue_append]
  simp only [htlcOutputsValue]
  omega

/-- Crediting one side by an HTLC's value while erasing that HTLC from the
list preserves the total output value. -/
private theorem totalOutputValue_credit_erase (c : Commitment)
    (h : CommitmentHTLCOutput) (side : BalanceSide)
    (hmem : h ∈ c.htlcs) :
    ({ creditCommitment c side h.amountSat with htlcs := c.htlcs.erase h } :
        Commitment).totalOutputValue = c.totalOutputValue := by
  have hsum := htlcOutputsValue_erase c.htlcs h hmem
  have hle := amount_le_htlcOutputsValue c.htlcs h hmem
  cases side <;>
    (by_cases hanch : c.anchorOutputs <;>
      simp [creditCommitment, Commitment.totalOutputValue,
        Commitment.htlcOutputValue, Commitment.anchorOutputValue, hsum,
        hanch] <;>
      omega)

/-- **Conservation for `List.erase`-based settlement (LN-CONS-004).**
Erasing one HTLC output from the list removes exactly its value from the
output sum (including when equal-valued outputs are duplicated), so
crediting that value to a balance preserves the conservation equation. -/
theorem settleHTLCOutputErase_conserved (c : Commitment)
    (h : CommitmentHTLCOutput) (fulfilled hadOutput : Bool)
    (hc : CommitmentConserved c) (hmem : h ∈ c.htlcs) :
    CommitmentConserved (settleHTLCOutputErase c h fulfilled hadOutput) := by
  unfold settleHTLCOutputErase
  cases hadOutput with
  | false => exact hc
  | true =>
      dsimp only
      simp only [ite_true]
      unfold CommitmentConserved at hc ⊢
      rw [totalOutputValue_credit_erase c h
        (fundingSide c (if fulfilled then h.direction.flip else h.direction)) hmem]
      simpa using hc

end LnLean.Proofs
