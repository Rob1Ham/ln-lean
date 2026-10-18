import LnLean.Channel.HTLC
import LnLean.Channel.HTLCLaws
import LnLean.Channel.Commitment
import LnLean.Channel.Revocation
import LnLean.Channel.Penalty
import LnLean.Channel.Types
import LnLean.Proofs.Conservation

/-!
# LnLean.Proofs.WaveD.D15 — HTLC amount conservation

Catalog obligation `LN-HT-003` ("Offered, received, and trimmed HTLC amounts
plus balances and fee equal the funding value"), whose catalog target is
`LnLean.Channel.HTLC.amount_conservation` (statement-only in the pinned tree:
the model module `LnLean.Channel.HTLC` defines `HTLCRecord`, `htlcSet`,
`htlcOutputValue`, `isDustHTLC`, and the lifecycle transitions, but no
conservation theorem, and nothing links a `Balance`/`HTLCRecord` list to a
`Commitment`).

This file supplies that missing link without touching the model:

* `untrimmed` / `offeredUntrimmed` / `receivedUntrimmed` / `trimmedHtlcs`
  are the three BOLT 3 buckets.  `waveD_d15_partition_covers` proves that,
  for any live HTLC set, the three buckets are an exact partition.
* `waveD_d15_amount_conservation_msat` is the millisecond accounting
  identity: if the two off-chain balances plus the live HTLC values are the
  funding value, then balances plus offered plus received plus trimmed
  amounts are the funding value.
* `commitmentOf` builds the BOLT 3 commitment record for a balance, an HTLC
  list, and a fee: `to_local`/`to_remote` are the balances with the base fee
  and the anchor outputs debited from the funder's output, the HTLC outputs
  are the untrimmed offered/received HTLCs (each carrying its second-stage
  fee), and `feeSat` is the base fee plus the withheld second-stage fees
  plus the trimmed HTLC value.
* `waveD_d15_amount_conservation` proves `CommitmentConserved` for that
  record: output values plus fee equal the funding value.
* `waveD_d15_without_balance_invariant_false` is a checked counterexample
  showing that the equation is false without the balance/HTLC/funding
  invariant, which the current model does not state.

The only additional hypotheses of the satoshi-level theorem beyond the
BOLT 3 data are: (1) the missing off-chain invariant
`balance.local + balance.remote + sum htlc = funding`, (2) every HTLC amount
and both balances are whole satoshis (so BOLT 3's floor rounding loses
nothing and the equality is exact), (3) a positive dust limit (so an
untrimmed output cannot underflow its second-stage fee), and (4) the funder
can pay the base fee and the anchor outputs.

BOLT anchors.
* BOLT 2 §Adding an HTLC: `refs/bolts/02-peer-protocol.md:2772` (amount in
  msat, positive, total in flight bounded).
* BOLT 3 §Commitment Transaction Outputs: `refs/bolts/03-transactions.md:199`
  (offered HTLC output), `:251` (received HTLC output), `:305` (trimming and
  the rule that a trimmed output's value is added to the fee).
* BOLT 3 §Fees: `refs/bolts/03-transactions.md:464` (the funder pays the
  commitment fee out of its own output) and `:518` (second-stage fees).
* rust-lightning `lightning/src/ln/chan_utils.rs:716`
  (`HTLCOutputInCommitment`) and `:744` (`to_bitcoin_amount`, i.e. floor
  division by 1000).

Not modelled here: wire encodings, signatures, transaction ordering, and
whether the counterparty actually broadcasts the commitment.  As in
`LnLean.Proofs.Conservation`, the equation is over output *values*.
-/

namespace LnLean.Proofs.WaveD.D15

open LnLean
open LnLean.Channel
open List

set_option autoImplicit false

/-! ## Amount sums over `HTLCRecord` lists -/

/-- Total HTLC value in millisatoshis.  This is the `HTLCRecord`-level
counterpart of `LnLean.Channel.totalHtlcValue`. -/
def htlcAmountSum (hs : List HTLCRecord) : Nat :=
  (hs.map (fun h => h.amountMsat.val)).sum

/-- Total HTLC value in satoshis after BOLT 3 floor rounding. -/
def htlcSatSum (hs : List HTLCRecord) : Nat :=
  (hs.map (fun h => h.amountMsat.toSatFloor)).sum

/-- Total on-chain output value of a list of HTLC records, in satoshis.
Each record contributes `htlcOutputValue`, i.e. its floored amount minus the
BOLT 3 second-stage fee for its direction. -/
def htlcOutputSum (timeoutFee successFee : Nat) (hs : List HTLCRecord) : Nat :=
  (hs.map (fun h => htlcOutputValue h timeoutFee successFee)).sum

/-- Total second-stage fee withheld from a list of HTLC outputs, in
satoshis.  BOLT 3 charges the timeout fee to an offered HTLC and the success
fee to a received HTLC. -/
def htlcFeeSum (timeoutFee successFee : Nat) (hs : List HTLCRecord) : Nat :=
  (hs.map (fun h => secondStageFee h.direction timeoutFee successFee)).sum

@[simp] theorem waveD_d15_htlcAmountSum_nil : htlcAmountSum [] = 0 := rfl

@[simp] theorem waveD_d15_htlcSatSum_nil : htlcSatSum [] = 0 := rfl

theorem waveD_d15_htlcAmountSum_append (xs ys : List HTLCRecord) :
    htlcAmountSum (xs ++ ys) = htlcAmountSum xs + htlcAmountSum ys := by
  unfold htlcAmountSum
  rw [List.map_append, List.sum_append]

theorem waveD_d15_htlcSatSum_append (xs ys : List HTLCRecord) :
    htlcSatSum (xs ++ ys) = htlcSatSum xs + htlcSatSum ys := by
  unfold htlcSatSum
  rw [List.map_append, List.sum_append]

/-! ## The BOLT 3 partition: offered / received / trimmed -/

/-- The live HTLCs whose commitment output survives the dust test. -/
def untrimmed (dustLimit timeoutFee successFee : Nat)
    (hs : List HTLCRecord) : List HTLCRecord :=
  (htlcSet hs).filter (fun h => !isDustHTLC h dustLimit timeoutFee successFee)

/-- The untrimmed HTLCs offered by the local endpoint. -/
def offeredUntrimmed (dustLimit timeoutFee successFee : Nat)
    (hs : List HTLCRecord) : List HTLCRecord :=
  (untrimmed dustLimit timeoutFee successFee hs).filter
    (fun h => decide (h.direction = Direction.local))

/-- The untrimmed HTLCs received by the local endpoint. -/
def receivedUntrimmed (dustLimit timeoutFee successFee : Nat)
    (hs : List HTLCRecord) : List HTLCRecord :=
  (untrimmed dustLimit timeoutFee successFee hs).filter
    (fun h => decide (h.direction = Direction.remote))

/-- The live HTLCs whose output is trimmed: their value is added to the
commitment fee (BOLT 3 §Commitment Transaction Outputs). -/
def trimmedHtlcs (dustLimit timeoutFee successFee : Nat)
    (hs : List HTLCRecord) : List HTLCRecord :=
  (htlcSet hs).filter (fun h => isDustHTLC h dustLimit timeoutFee successFee)

/-- Splitting a list on a Boolean predicate, up to permutation.  The
concatenation of the two filters is a permutation, not literally the
original list: filtering preserves relative order inside each bucket. -/
theorem waveD_d15_filter_dust_perm (dustLimit timeoutFee successFee : Nat)
    (l : List HTLCRecord) :
    l.filter (fun h => !isDustHTLC h dustLimit timeoutFee successFee) ++
      l.filter (fun h => isDustHTLC h dustLimit timeoutFee successFee) ~ l := by
  simpa using List.filter_append_perm
    (fun h : HTLCRecord => !isDustHTLC h dustLimit timeoutFee successFee) l

/-- Splitting a list into its offered and received parts, up to permutation.
Every `Direction` is either `local` or `remote`. -/
theorem waveD_d15_filter_direction_perm (l : List HTLCRecord) :
    l.filter (fun h => decide (h.direction = Direction.local)) ++
      l.filter (fun h => decide (h.direction = Direction.remote)) ~ l := by
  have hcomp :
      (fun h : HTLCRecord => !decide (h.direction = Direction.local)) =
        (fun h => decide (h.direction = Direction.remote)) := by
    funext h
    cases h.direction <;> rfl
  simpa [hcomp] using List.filter_append_perm
    (fun h : HTLCRecord => decide (h.direction = Direction.local)) l

/-- **The offered/received/trimmed partition.**  For any live HTLC set, the
three BOLT 3 buckets cover it exactly, up to permutation.  This is the
partition whose amounts the catalog claim adds up; order is irrelevant for
the amount sum. -/
theorem waveD_d15_partition_perm (dustLimit timeoutFee successFee : Nat)
    (hs : List HTLCRecord) :
    offeredUntrimmed dustLimit timeoutFee successFee hs ++
        receivedUntrimmed dustLimit timeoutFee successFee hs ++
        trimmedHtlcs dustLimit timeoutFee successFee hs ~ htlcSet hs := by
  have hdir :
      offeredUntrimmed dustLimit timeoutFee successFee hs ++
          receivedUntrimmed dustLimit timeoutFee successFee hs ~
        untrimmed dustLimit timeoutFee successFee hs := by
    unfold offeredUntrimmed receivedUntrimmed
    exact waveD_d15_filter_direction_perm
      (untrimmed dustLimit timeoutFee successFee hs)
  have hdust :
      untrimmed dustLimit timeoutFee successFee hs ++
          trimmedHtlcs dustLimit timeoutFee successFee hs ~ htlcSet hs := by
    unfold untrimmed trimmedHtlcs
    exact waveD_d15_filter_dust_perm dustLimit timeoutFee successFee (htlcSet hs)
  exact (hdir.append_right (trimmedHtlcs dustLimit timeoutFee successFee hs)).trans
    hdust

/-- The millisecond amount of the live HTLC set splits over the three
buckets.  Permutation is enough because `List.sum` is permutation-invariant. -/
theorem waveD_d15_htlcAmountSum_partition (dustLimit timeoutFee successFee : Nat)
    (hs : List HTLCRecord) :
    htlcAmountSum (htlcSet hs) =
      htlcAmountSum (offeredUntrimmed dustLimit timeoutFee successFee hs) +
        htlcAmountSum (receivedUntrimmed dustLimit timeoutFee successFee hs) +
        htlcAmountSum (trimmedHtlcs dustLimit timeoutFee successFee hs) := by
  have hp := waveD_d15_partition_perm dustLimit timeoutFee successFee hs
  have hsum := (hp.map (fun h : HTLCRecord => h.amountMsat.val)).sum_nat
  rw [List.map_append, List.map_append, List.sum_append, List.sum_append] at hsum
  exact hsum.symm

/-- The satoshi amount of the live HTLC set splits over the three buckets. -/
theorem waveD_d15_htlcSatSum_partition (dustLimit timeoutFee successFee : Nat)
    (hs : List HTLCRecord) :
    htlcSatSum (htlcSet hs) =
      htlcSatSum (offeredUntrimmed dustLimit timeoutFee successFee hs) +
        htlcSatSum (receivedUntrimmed dustLimit timeoutFee successFee hs) +
        htlcSatSum (trimmedHtlcs dustLimit timeoutFee successFee hs) := by
  have hp := waveD_d15_partition_perm dustLimit timeoutFee successFee hs
  have hsum := (hp.map (fun h : HTLCRecord => h.amountMsat.toSatFloor)).sum_nat
  rw [List.map_append, List.map_append, List.sum_append, List.sum_append] at hsum
  exact hsum.symm

/-! ## Exact millisecond conservation -/

/-- **Millisecond form of `LN-HT-003`.**  If the off-chain balances plus the
live HTLC values are the funding value, then the balances plus the offered,
received, and trimmed HTLC amounts are the funding value.  No rounding or
dust hypothesis is needed: this is the exact msat accounting identity that
underlies BOLT 3's satoshi equation. -/
theorem waveD_d15_amount_conservation_msat
    (dustLimit timeoutFee successFee : Nat) (b : Balance)
    (hs : List HTLCRecord) (funding : Msat)
    (hbal : b.localBalance.val + b.remoteBalance.val +
      htlcAmountSum (htlcSet hs) = funding.val) :
    b.localBalance.val + b.remoteBalance.val +
      htlcAmountSum (offeredUntrimmed dustLimit timeoutFee successFee hs) +
      htlcAmountSum (receivedUntrimmed dustLimit timeoutFee successFee hs) +
      htlcAmountSum (trimmedHtlcs dustLimit timeoutFee successFee hs) =
        funding.val := by
  have hpart := waveD_d15_htlcAmountSum_partition dustLimit timeoutFee successFee hs
  omega

/-! ## Whole-satoshi amounts -/

/-- If every amount in a list is a whole number of satoshis, then the
millisecond sum is exactly 1000 times the floored sum (no rounding loss). -/
theorem waveD_d15_htlcAmountSum_eq_1000_mul (hs : List HTLCRecord)
    (h : ∀ x ∈ hs, x.amountMsat.val = 1000 * x.amountMsat.toSatFloor) :
    htlcAmountSum hs = 1000 * htlcSatSum hs := by
  induction hs with
  | nil => rfl
  | cons x xs ih =>
      have hx : x.amountMsat.val = 1000 * x.amountMsat.toSatFloor := h x (by simp)
      have hxs : ∀ y ∈ xs, y.amountMsat.val = 1000 * y.amountMsat.toSatFloor :=
        fun y hy => h y (by simp [hy])
      have hih := ih hxs
      calc
        htlcAmountSum (x :: xs) = x.amountMsat.val + htlcAmountSum xs := rfl
        _ = 1000 * x.amountMsat.toSatFloor + 1000 * htlcSatSum xs := by rw [hx, hih]
        _ = 1000 * (x.amountMsat.toSatFloor + htlcSatSum xs) := by rw [Nat.mul_add]
        _ = 1000 * htlcSatSum (x :: xs) := rfl

/-- **Satoshi form of the partition identity.**  If every amount is a whole
number of satoshis, the two balances plus the offered, received, and trimmed
HTLC amounts equal the funding value.  This is the direct satoshi analogue of
the catalog wording; the commitment-fee form is
`waveD_d15_amount_conservation` below. -/
theorem waveD_d15_amount_conservation_sat
    (dustLimit timeoutFee successFee : Nat) (b : Balance)
    (hs : List HTLCRecord) (funding : Msat) (fundingSat : Nat)
    (hwhole : ∀ h ∈ hs,
      h.amountMsat.val = 1000 * h.amountMsat.toSatFloor)
    (hwholeLocal : b.localBalance.val = 1000 * b.localSat)
    (hwholeRemote : b.remoteBalance.val = 1000 * b.remoteSat)
    (hwholeFunding : funding.val = 1000 * fundingSat)
    (hbal : b.localBalance.val + b.remoteBalance.val +
      htlcAmountSum (htlcSet hs) = funding.val) :
    b.localSat + b.remoteSat +
      htlcSatSum (offeredUntrimmed dustLimit timeoutFee successFee hs) +
      htlcSatSum (receivedUntrimmed dustLimit timeoutFee successFee hs) +
      htlcSatSum (trimmedHtlcs dustLimit timeoutFee successFee hs) =
        fundingSat := by
  have hwholeSet : htlcAmountSum (htlcSet hs) =
      1000 * htlcSatSum (htlcSet hs) := by
    apply waveD_d15_htlcAmountSum_eq_1000_mul
    intro x hx
    exact hwhole x (List.mem_filter.mp (by simpa [htlcSet] using hx)).1
  have hsum := waveD_d15_htlcSatSum_partition dustLimit timeoutFee successFee hs
  omega

/-! ## Second-stage fees and output values -/

/-- An untrimmed HTLC's second-stage fee is covered by its floored amount.
Otherwise the saturating subtraction in `htlcOutputValue` would make the
output zero, which is below a positive dust limit, so the HTLC would have
been trimmed. -/
theorem waveD_d15_untrimmed_secondStage_le (dustLimit timeoutFee successFee : Nat)
    (hdust : 0 < dustLimit) {hs : List HTLCRecord} {h : HTLCRecord}
    (hm : h ∈ untrimmed dustLimit timeoutFee successFee hs) :
    secondStageFee h.direction timeoutFee successFee ≤ h.amountMsat.toSatFloor := by
  have hnotdust : isDustHTLC h dustLimit timeoutFee successFee = false := by
    have hp := (List.mem_filter.mp hm).2
    simpa using hp
  have hge := nonDust_value_ge h dustLimit timeoutFee successFee hnotdust
  unfold htlcOutputValue at hge
  omega

/-- **Output value plus withheld fee equals the floored amount.**  For every
list whose second-stage fees are covered, the sum of the commitment output
values plus the sum of the withheld second-stage fees is exactly the sum of
the floored HTLC amounts.  This is the local form of BOLT 3's
`amount / 1000 - second_stage_fee` output rule. -/
theorem waveD_d15_htlcOutputSum_add_fee (timeoutFee successFee : Nat)
    (hs : List HTLCRecord)
    (h : ∀ x ∈ hs,
      secondStageFee x.direction timeoutFee successFee ≤ x.amountMsat.toSatFloor) :
    htlcOutputSum timeoutFee successFee hs +
      htlcFeeSum timeoutFee successFee hs = htlcSatSum hs := by
  induction hs with
  | nil => rfl
  | cons x xs ih =>
      have hx := h x (by simp)
      have hxs : ∀ y ∈ xs,
          secondStageFee y.direction timeoutFee successFee ≤ y.amountMsat.toSatFloor :=
        fun y hy => h y (by simp [hy])
      have hih := ih hxs
      have hxf : htlcOutputValue x timeoutFee successFee +
          secondStageFee x.direction timeoutFee successFee =
            x.amountMsat.toSatFloor := by
        unfold htlcOutputValue
        exact Nat.sub_add_cancel hx
      calc
        htlcOutputSum timeoutFee successFee (x :: xs) +
            htlcFeeSum timeoutFee successFee (x :: xs)
            = (htlcOutputValue x timeoutFee successFee +
                htlcOutputSum timeoutFee successFee xs) +
              (secondStageFee x.direction timeoutFee successFee +
                htlcFeeSum timeoutFee successFee xs) := rfl
        _ = (htlcOutputValue x timeoutFee successFee +
                secondStageFee x.direction timeoutFee successFee) +
              (htlcOutputSum timeoutFee successFee xs +
                htlcFeeSum timeoutFee successFee xs) := by omega
        _ = x.amountMsat.toSatFloor + htlcSatSum xs := by rw [hxf, hih]
        _ = htlcSatSum (x :: xs) := rfl

/-! ## The commitment record implied by a balance and an HTLC partition -/

/-- The amount debited from the funder's output: the base commitment fee
plus, when `option_anchors` is negotiated, the two 330-satoshi anchor
outputs (BOLT 3 §Commitment Transaction; the funder pays both). -/
def commitmentDeduction (baseFee : Nat) (anchors : Bool) : Nat :=
  baseFee + (if anchors then 2 * anchorOutputSat else 0)

/-- The holder's `to_local` output.  The holder owns it; the funder (which
may be either endpoint) has the deduction taken from its own balance
(BOLT 3 §Fees). -/
def commitmentToLocal (holder funder : Direction) (b : Balance)
    (deduct : Nat) : Nat :=
  match holder, funder with
  | .local, .local => b.localSat - deduct
  | .local, .remote => b.localSat
  | .remote, .local => b.remoteSat
  | .remote, .remote => b.remoteSat - deduct

/-- The counterparty's `to_remote` output. -/
def commitmentToRemote (holder funder : Direction) (b : Balance)
    (deduct : Nat) : Nat :=
  match holder, funder with
  | .local, .local => b.remoteSat
  | .local, .remote => b.remoteSat - deduct
  | .remote, .local => b.localSat - deduct
  | .remote, .remote => b.localSat

/-- The two non-HTLC outputs of a commitment are the balances minus the
deduction taken from the funder's own output, as long as that output covers
the deduction.  This is why the funder, not the pair jointly, must afford the
fee (BOLT 3 §Fees). -/
theorem waveD_d15_commitmentBalances_add (holder funder : Direction)
    (b : Balance) (deduct : Nat)
    (h : deduct ≤
      (if funder = Direction.local then b.localSat else b.remoteSat)) :
    commitmentToLocal holder funder b deduct +
      commitmentToRemote holder funder b deduct =
        b.localSat + b.remoteSat - deduct := by
  cases holder <;> cases funder
  · change (b.localSat - deduct) + b.remoteSat =
        b.localSat + b.remoteSat - deduct
    exact (Nat.sub_add_comm h).symm
  · change b.localSat + (b.remoteSat - deduct) =
        b.localSat + b.remoteSat - deduct
    exact (Nat.add_sub_assoc h b.localSat).symm
  · change b.remoteSat + (b.localSat - deduct) =
        b.localSat + b.remoteSat - deduct
    calc
      b.remoteSat + (b.localSat - deduct)
          = b.remoteSat + b.localSat - deduct :=
            (Nat.add_sub_assoc h b.remoteSat).symm
      _ = b.localSat + b.remoteSat - deduct := by
            rw [Nat.add_comm b.remoteSat b.localSat]
  · change (b.remoteSat - deduct) + b.localSat =
        b.localSat + b.remoteSat - deduct
    calc
      (b.remoteSat - deduct) + b.localSat
          = b.remoteSat + b.localSat - deduct :=
            (Nat.sub_add_comm h).symm
      _ = b.localSat + b.remoteSat - deduct := by
            rw [Nat.add_comm b.remoteSat b.localSat]

/-- The commitment HTLC outputs: one per untrimmed offered HTLC (timeout
path) followed by one per untrimmed received HTLC (success path). -/
def partitionCommitmentHTLCs (dustLimit timeoutFee successFee : Nat)
    (hs : List HTLCRecord) : List CommitmentHTLCOutput :=
  (offeredUntrimmed dustLimit timeoutFee successFee hs).map
      (fun h => ({ direction := Direction.local
                   amountSat := htlcOutputValue h timeoutFee successFee
                   cltvExpiry := h.cltvExpiry
                   state := h.state } : CommitmentHTLCOutput)) ++
    (receivedUntrimmed dustLimit timeoutFee successFee hs).map
      (fun h => ({ direction := Direction.remote
                   amountSat := htlcOutputValue h timeoutFee successFee
                   cltvExpiry := h.cltvExpiry
                   state := h.state } : CommitmentHTLCOutput))

/-- The commitment fee implied by a partition: the base miner fee, plus the
second-stage fees withheld from the untrimmed HTLC outputs, plus the whole
value of the trimmed HTLCs (BOLT 3 adds trimmed value to the fee). -/
def partitionFee (dustLimit timeoutFee successFee baseFee : Nat)
    (hs : List HTLCRecord) : Nat :=
  baseFee +
    htlcFeeSum timeoutFee successFee
      (offeredUntrimmed dustLimit timeoutFee successFee hs) +
    htlcFeeSum timeoutFee successFee
      (receivedUntrimmed dustLimit timeoutFee successFee hs) +
    htlcSatSum (trimmedHtlcs dustLimit timeoutFee successFee hs)

/-- The BOLT 3 commitment record implied by an off-chain balance, an HTLC
list, and a base fee.  This is the proof-local bridge between the
`HTLCRecord` model and the `Commitment` value model; it changes no model
definition. -/
def commitmentOf (holder funder : Direction) (b : Balance)
    (hs : List HTLCRecord) (number fundingSat baseFee dustLimit timeoutFee
      successFee contestDelay : Nat) (anchors : Bool) : Commitment :=
  { holder := holder
    commitmentNumber := number
    fundingValueSat := fundingSat
    toLocalSat := commitmentToLocal holder funder b
      (commitmentDeduction baseFee anchors)
    toRemoteSat := commitmentToRemote holder funder b
      (commitmentDeduction baseFee anchors)
    htlcs := partitionCommitmentHTLCs dustLimit timeoutFee successFee hs
    feeSat := partitionFee dustLimit timeoutFee successFee baseFee hs
    contestDelay := contestDelay
    anchorOutputs := anchors }

/-! ### Value of the generated HTLC outputs -/

theorem waveD_d15_htlcOutputsValue_map (l : List HTLCRecord)
    (dir : Direction) (timeoutFee successFee : Nat) :
    htlcOutputsValue
        (l.map (fun h => ({ direction := dir
                            amountSat := htlcOutputValue h timeoutFee successFee
                            cltvExpiry := h.cltvExpiry
                            state := h.state } : CommitmentHTLCOutput))) =
      htlcOutputSum timeoutFee successFee l := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [htlcOutputsValue, htlcOutputSum, ih]

/-- The generated HTLC output list is worth exactly the offered plus
received untrimmed output sums. -/
theorem waveD_d15_partitionCommitmentHTLCs_value
    (dustLimit timeoutFee successFee : Nat) (hs : List HTLCRecord) :
    htlcOutputsValue
        (partitionCommitmentHTLCs dustLimit timeoutFee successFee hs) =
      htlcOutputSum timeoutFee successFee
          (offeredUntrimmed dustLimit timeoutFee successFee hs) +
        htlcOutputSum timeoutFee successFee
          (receivedUntrimmed dustLimit timeoutFee successFee hs) := by
  unfold partitionCommitmentHTLCs
  rw [htlcOutputsValue_append,
    waveD_d15_htlcOutputsValue_map, waveD_d15_htlcOutputsValue_map]

/-! ## Satoshi-level conservation -/

-- OBLIGATION: LN-WD-D15

/-- **Satoshi form of `LN-HT-003`.**  The commitment generated by
`commitmentOf` conserves value: the sum of its `to_local`/`to_remote`
outputs, its untrimmed offered and received HTLC outputs, and its anchor
outputs, plus its fee, is exactly the funding value.

The balance invariant `hbal` is the missing model field identified in the
report: `Balance` and the HTLC list are independent of
`Channel.fundingValue`, so the claim is false without it (see
`waveD_d15_without_balance_invariant_false`).  `hwhole*` says the amounts
are whole satoshis, so BOLT 3's floor rounding loses nothing; `hdust` keeps
the second-stage fee below the HTLC amount; `hfund` says the funder can pay
the base fee and the anchor outputs. -/
theorem waveD_d15_amount_conservation
    (holder funder : Direction) (b : Balance) (hs : List HTLCRecord)
    (funding : Msat) (number fundingSat baseFee dustLimit timeoutFee
      successFee contestDelay : Nat) (anchors : Bool)
    (hdust : 0 < dustLimit)
    (hwhole : ∀ h ∈ hs,
      h.amountMsat.val = 1000 * h.amountMsat.toSatFloor)
    (hwholeLocal : b.localBalance.val = 1000 * b.localSat)
    (hwholeRemote : b.remoteBalance.val = 1000 * b.remoteSat)
    (hwholeFunding : funding.val = 1000 * fundingSat)
    (hbal : b.localBalance.val + b.remoteBalance.val +
      htlcAmountSum (htlcSet hs) = funding.val)
    (hfund : commitmentDeduction baseFee anchors ≤
      (if funder = Direction.local then b.localSat else b.remoteSat)) :
    CommitmentConserved
      (commitmentOf holder funder b hs number fundingSat baseFee dustLimit
        timeoutFee successFee contestDelay anchors) := by
  let c := commitmentOf holder funder b hs number fundingSat baseFee dustLimit
    timeoutFee successFee contestDelay anchors
  let D := commitmentDeduction baseFee anchors
  change CommitmentConserved c
  have hTL : c.toLocalSat = commitmentToLocal holder funder b D := rfl
  have hTR : c.toRemoteSat = commitmentToRemote holder funder b D := rfl
  have hHtlcs : c.htlcs =
      partitionCommitmentHTLCs dustLimit timeoutFee successFee hs := rfl
  have hFee : c.feeSat =
      partitionFee dustLimit timeoutFee successFee baseFee hs := rfl
  have hAnchor : c.anchorOutputValue =
      (if anchors then 2 * anchorOutputSat else 0) := rfl
  have hFund : c.fundingValueSat = fundingSat := rfl
  have hout := waveD_d15_partitionCommitmentHTLCs_value
    dustLimit timeoutFee successFee hs
  have hoff := waveD_d15_htlcOutputSum_add_fee timeoutFee successFee
    (offeredUntrimmed dustLimit timeoutFee successFee hs)
    (fun h hm => waveD_d15_untrimmed_secondStage_le dustLimit timeoutFee
      successFee hdust (List.mem_filter.mp hm).1)
  have hrec := waveD_d15_htlcOutputSum_add_fee timeoutFee successFee
    (receivedUntrimmed dustLimit timeoutFee successFee hs)
    (fun h hm => waveD_d15_untrimmed_secondStage_le dustLimit timeoutFee
      successFee hdust (List.mem_filter.mp hm).1)
  have hbar := waveD_d15_commitmentBalances_add holder funder b D hfund
  have hsum := waveD_d15_htlcSatSum_partition dustLimit timeoutFee successFee hs
  have hwholeSet : htlcAmountSum (htlcSet hs) =
      1000 * htlcSatSum (htlcSet hs) := by
    apply waveD_d15_htlcAmountSum_eq_1000_mul
    intro x hx
    exact hwhole x (List.mem_filter.mp (by simpa [htlcSet] using hx)).1
  have hD : D = baseFee + (if anchors then 2 * anchorOutputSat else 0) := rfl
  have hDsum : D ≤ b.localSat + b.remoteSat := by
    cases funder <;> simp at hfund ⊢ <;> omega
  unfold CommitmentConserved
  simp only [Commitment.totalOutputValue, Commitment.htlcOutputValue,
    hTL, hTR, hHtlcs, hAnchor, hFee, hFund, partitionFee]
  rw [hout, hbar]
  omega

/-! ## The balance invariant is necessary -/

/-- **Checked counterexample: the equation is false without the
balance/HTLC/funding invariant.**  Two zero balances, one live offered HTLC
of 1000 msat (one satoshi), and a funding value of zero generate a
commitment with a one-satoshi HTLC output, no fee, and no balance outputs;
its outputs plus fee are one satoshi, not zero. -/
theorem waveD_d15_without_balance_invariant_false :
    ¬ CommitmentConserved
        (commitmentOf Direction.local Direction.local
          { localBalance := ⟨0⟩, remoteBalance := ⟨0⟩ }
          [{ id := 0
             direction := Direction.local
             amountMsat := ⟨1000⟩
             paymentHash := ⟨ByteArray.empty⟩
             cltvExpiry := 0
             state := HTLCState.offered }]
          0 0 0 1 0 0 0 false) := by
  unfold CommitmentConserved
  decide

end LnLean.Proofs.WaveD.D15
