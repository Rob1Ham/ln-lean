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
* The legacy `Commitment.commitmentOutputs` function emits a fixed group order
  and applies no dust filter.  BOLT 3's value/script/CLTV ordering and dust
  trimming are modelled separately by the faithful `CommitmentTx` extension
  at the end of this file.  The obscured commitment number, `nSequence`, and
  signature/witness bytes remain unmodelled.
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

/-! ## Gross/net values and the effective fee (CH-03 core patch)

BOLT 3 distinguishes two satoshi values for every HTLC on a commitment
transaction:

* the **gross** value `amount_msat / 1000`, which is the value of the
  commitment transaction output, and
* the **net** value `gross - second_stage_fee`, which is what the
  HTLC-timeout/HTLC-success transaction pays after its own fee.

The dust test is on the net value: BOLT 3 trims an HTLC iff
`gross - second_stage_fee < dust_limit_satoshis`, equivalently
`gross < dust_limit_satoshis + second_stage_fee` (`03-transactions.md:330`).
The commitment output itself is gross (`03-transactions.md:365`), and a trimmed
output's whole gross value is added to the commitment transaction fee
(`03-transactions.md:329`).

The record boundary now carries both values: `CommitmentHTLCOutput.amountSat`
is gross and `CommitmentHTLCOutput.netAmountSat` (default `amountSat`) is the
second-stage value used by the dust test; `Commitment.trimmedTotalSat`
(default `0`) records the gross value removed by trimming.  Those fields are
defined in `LnLean/Channel/Types.lean` and are carried by every literal
unchanged through their defaults.

`Commitment.trimmedSat` below is the *computed* nominal trimmed value for a
given dust limit and net projection; the stored field is therefore named
`trimmedTotalSat` to avoid the name collision.  `Commitment.trimmedValueFor`
is the future-facing alias recommended by the wave-5 integration note.
`effectiveFeeSat` is the actual commitment fee,
`fundingValueSat - totalOutputValue`; when `totalOutputValue` is the emitted
(survivor) value, it is exactly `feeSat + trimmedTotalSat`.

**Naming decision (CH-01/CH-03, wave 7).**  The stored field stays
`trimmedTotalSat`.  `trimmedSat` is the established *computed* function used by
the wave-5 module `CommitmentGrossNetTargets` and by `CommitmentTx.trimmedValue`
/ `recordTrimmedValue`; renaming either side would be a breaking, coordinated
API change across files outside this lane.  The pair `trimmedTotalSat` (stored)
and `trimmedValueFor` (computed alias) is unambiguous and is kept. -/

/-- The gross satoshi value that BOLT 3 trims from a nominal commitment record
under an owner's dust limit and a net-value projection.  A trimmed
`to_local`/`to_remote` contributes its whole value; a trimmed HTLC contributes
its gross `amountSat`.  Anchors are never trimmed. -/
def Commitment.trimmedSat (c : Commitment) (dustLimitSat : Nat)
    (netAmountSat : CommitmentHTLCOutput → Nat) : Nat :=
  (if dustLimitSat ≤ c.toLocalSat then 0 else c.toLocalSat) +
  (if dustLimitSat ≤ c.toRemoteSat then 0 else c.toRemoteSat) +
  (c.htlcs.map (fun h =>
    if dustLimitSat ≤ netAmountSat h then 0 else h.amountSat)).sum

/-- Future-facing alias for the computed nominal trimmed value.  The stored
record field is `Commitment.trimmedTotalSat`; this alias keeps the computation
available under the name recommended for a later rename. -/
def Commitment.trimmedValueFor (c : Commitment) (dustLimitSat : Nat)
    (netAmountSat : CommitmentHTLCOutput → Nat) : Nat :=
  c.trimmedSat dustLimitSat netAmountSat

theorem Commitment.trimmedValueFor_eq_trimmedSat (c : Commitment)
    (dustLimitSat : Nat) (netAmountSat : CommitmentHTLCOutput → Nat) :
    c.trimmedValueFor dustLimitSat netAmountSat =
      c.trimmedSat dustLimitSat netAmountSat := rfl

/-- The **effective** commitment fee: everything in the funding value that the
commitment transaction does not pay to an output.  With a BOLT-3-migrated
record (only surviving outputs in `htlcs`, trimmed outputs zeroed), this is the
base fee plus the gross value added by trimming. -/
def Commitment.effectiveFeeSat (c : Commitment) : Nat :=
  c.fundingValueSat - c.totalOutputValue

/-- Under the BOLT 3 balance equation the effective fee is exactly the residual
of the funding value. -/
theorem Commitment.totalOutputValue_add_effectiveFeeSat (c : Commitment)
    (h : c.totalOutputValue ≤ c.fundingValueSat) :
    c.totalOutputValue + c.effectiveFeeSat = c.fundingValueSat := by
  unfold Commitment.effectiveFeeSat
  omega

/-- The effective fee is the base fee when trimming removes nothing and the
balance equation holds. -/
theorem Commitment.effectiveFeeSat_eq_feeSat (c : Commitment)
    (h : c.totalOutputValue + c.feeSat = c.fundingValueSat) :
    c.effectiveFeeSat = c.feeSat := by
  unfold Commitment.effectiveFeeSat
  omega

/-- The BOLT 3 net-value dust test on a record: the HTLC survives exactly when
`dustLimitSat ≤ netAmountSat`.  This is the record-field counterpart of the
`CommitmentTx.htlcOutputNet` test and of the computed `trimmedSat` predicate. -/
def CommitmentHTLCOutput.keepAtDust (dustLimitSat : Nat)
    (h : CommitmentHTLCOutput) : Bool :=
  decide (dustLimitSat ≤ h.netAmountSat)

theorem CommitmentHTLCOutput.keepAtDust_eq_true_iff
    {dustLimitSat : Nat} {h : CommitmentHTLCOutput} :
    h.keepAtDust dustLimitSat = true ↔ dustLimitSat ≤ h.netAmountSat :=
  decide_eq_true_iff

theorem CommitmentHTLCOutput.keepAtDust_eq_false_iff
    {dustLimitSat : Nat} {h : CommitmentHTLCOutput} :
    h.keepAtDust dustLimitSat = false ↔ ¬ dustLimitSat ≤ h.netAmountSat :=
  decide_eq_false_iff_not

/-- Copy a gross record with an explicit net second-stage value. -/
def CommitmentHTLCOutput.withNet (h : CommitmentHTLCOutput) (netAmountSat : Nat) :
    CommitmentHTLCOutput :=
  { h with netAmountSat := netAmountSat }

theorem CommitmentHTLCOutput.withNet_netAmountSat (h : CommitmentHTLCOutput)
    (netAmountSat : Nat) :
    (h.withNet netAmountSat).netAmountSat = netAmountSat := rfl

theorem CommitmentHTLCOutput.withNet_amountSat (h : CommitmentHTLCOutput)
    (netAmountSat : Nat) :
    (h.withNet netAmountSat).amountSat = h.amountSat := rfl

/-- The default net projection is the identity (`netAmountSat = amountSat`). -/
theorem CommitmentHTLCOutput.withNet_amountSat_self (h : CommitmentHTLCOutput) :
    (h.withNet h.amountSat).netAmountSat = h.amountSat := rfl

/-- A nominal commitment with the BOLT 3 net-based dust filter applied:
below-dust `to_local`/`to_remote` are zeroed, below-dust HTLCs are removed, and
the removed gross value is recorded in `trimmedTotalSat`.  The net projection
is the record's own `CommitmentHTLCOutput.netAmountSat` field. -/
def Commitment.migrateNet (c : Commitment) (dustLimitSat : Nat) : Commitment :=
  { c with
    toLocalSat := if dustLimitSat ≤ c.toLocalSat then c.toLocalSat else 0
    toRemoteSat := if dustLimitSat ≤ c.toRemoteSat then c.toRemoteSat else 0
    htlcs := c.htlcs.filter (fun h => h.keepAtDust dustLimitSat)
    trimmedTotalSat := c.trimmedSat dustLimitSat (fun h => h.netAmountSat) }

theorem Commitment.migrateNet_feeSat (c : Commitment) (dustLimitSat : Nat) :
    (c.migrateNet dustLimitSat).feeSat = c.feeSat := rfl

theorem Commitment.migrateNet_fundingValueSat (c : Commitment) (dustLimitSat : Nat) :
    (c.migrateNet dustLimitSat).fundingValueSat = c.fundingValueSat := rfl

theorem Commitment.migrateNet_htlcs (c : Commitment) (dustLimitSat : Nat) :
    (c.migrateNet dustLimitSat).htlcs =
      c.htlcs.filter (fun h => h.keepAtDust dustLimitSat) := rfl

theorem Commitment.migrateNet_trimmedTotalSat (c : Commitment) (dustLimitSat : Nat) :
    (c.migrateNet dustLimitSat).trimmedTotalSat =
      c.trimmedSat dustLimitSat (fun h => h.netAmountSat) := rfl

/-- Migrate both commitments of a pair to the BOLT 3 net survivor set.  This is
the pair-level entry point used by the construction sites
`commitmentPairOfBalances` and by channel-state consumers: each side is
trimmed against its own caller-supplied dust limit (the protocol passes the
same value to both sides in the two-party model). -/
def CommitmentPair.migrateNet (p : CommitmentPair) (dustLimitSat : Nat) :
    CommitmentPair :=
  { localCommitment := p.localCommitment.migrateNet dustLimitSat
    remoteCommitment := p.remoteCommitment.migrateNet dustLimitSat }

theorem CommitmentPair.migrateNet_localCommitment (p : CommitmentPair)
    (dustLimitSat : Nat) :
    (p.migrateNet dustLimitSat).localCommitment =
      p.localCommitment.migrateNet dustLimitSat := rfl

theorem CommitmentPair.migrateNet_remoteCommitment (p : CommitmentPair)
    (dustLimitSat : Nat) :
    (p.migrateNet dustLimitSat).remoteCommitment =
      p.remoteCommitment.migrateNet dustLimitSat := rfl

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

/-! ## Output nonnegativity and the funding bound (LN-CH-002)

The catalog claim LN-CH-002 has two halves.  The first half — no commitment
output has a negative value — is structural in this model: every value field is
a `Nat`, so `CommitmentOutput.value` and every emitted output value are
nonnegative, unconditionally.  The second half — the output sum stays within
the funding value — is *not* structural: `Commitment` is a plain record with no
well-formedness invariant, so a caller can supply `toLocalSat` larger than
`fundingValueSat`.  The bound therefore needs the BOLT 3 balance equation as an
explicit hypothesis.

The proof layer states that equation as `CommitmentConserved` in
`LnLean.Proofs.Conservation`.  That module imports this one, so importing it
here would invert the dependency.  We use the explicit equality
`c.totalOutputValue + c.feeSat = c.fundingValueSat` instead, which is
definitionally the same proposition; `CommitmentConserved` is definitionally
equal to it, so the proof-layer theorem can be recovered without adding any
new assumption. -/

/-- Every `CommitmentOutput.value` is a natural number, hence nonnegative. -/
theorem CommitmentOutput.value_nonneg (o : CommitmentOutput) : 0 ≤ o.value :=
  Nat.zero_le _

/-- Nonnegativity of an output value when read as a mathematical integer. -/
theorem CommitmentOutput.value_nonneg_int (o : CommitmentOutput) :
    0 ≤ (o.value : Int) := by
  exact_mod_cast CommitmentOutput.value_nonneg o

/-- Every output emitted by `Commitment.commitmentOutputs` is nonnegative. -/
theorem Commitment.commitmentOutputs_value_nonneg (c : Commitment) :
    ∀ o ∈ c.commitmentOutputs, 0 ≤ o.value :=
  fun o _ => CommitmentOutput.value_nonneg o

/-- Every emitted output value is nonnegative after coercion to `Int`.  This is
the model-level reading of "no commitment output has a negative value". -/
theorem Commitment.commitmentOutputs_value_nonneg_int (c : Commitment) :
    ∀ o ∈ c.commitmentOutputs, 0 ≤ (o.value : Int) :=
  fun o _ => CommitmentOutput.value_nonneg_int o

/-- The sum of the emitted output values is nonnegative. -/
theorem Commitment.commitmentOutputs_sum_nonneg (c : Commitment) :
    0 ≤ (c.commitmentOutputs.map CommitmentOutput.value).sum :=
  Nat.zero_le _

/-- `totalOutputValue` is a natural number, hence nonnegative. -/
theorem Commitment.totalOutputValue_nonneg (c : Commitment) :
    0 ≤ c.totalOutputValue :=
  Nat.zero_le _

/-- `totalOutputValue` is nonnegative after coercion to `Int`. -/
theorem Commitment.totalOutputValue_nonneg_int (c : Commitment) :
    0 ≤ (c.totalOutputValue : Int) := by
  exact_mod_cast Commitment.totalOutputValue_nonneg c

/-- The value paid by the emitted output list is exactly `totalOutputValue`.
A zero-valued `to_local`/`to_remote` is omitted from the list but contributes
zero, so the identity needs no trimming hypothesis. -/
theorem Commitment.commitmentOutputs_sum_eq_totalOutputValue (c : Commitment) :
    (c.commitmentOutputs.map CommitmentOutput.value).sum = c.totalOutputValue := by
  have hloc :
      ((if c.toLocalSat = 0 then []
        else [CommitmentOutput.toLocal c.toLocalSat]).map
          CommitmentOutput.value).sum = c.toLocalSat := by
    by_cases h : c.toLocalSat = 0 <;> simp [h, CommitmentOutput.value]
  have hrem :
      ((if c.toRemoteSat = 0 then []
        else [CommitmentOutput.toRemote c.toRemoteSat]).map
          CommitmentOutput.value).sum = c.toRemoteSat := by
    by_cases h : c.toRemoteSat = 0 <;> simp [h, CommitmentOutput.value]
  have hhtlc :
      ((c.htlcs.map
        (fun h => CommitmentOutput.htlc h.direction h.amountSat)).map
          CommitmentOutput.value).sum = c.htlcOutputValue := by
    unfold Commitment.htlcOutputValue
    induction c.htlcs with
    | nil => rfl
    | cons h t ih =>
        simp only [List.map_cons, List.sum_cons, CommitmentOutput.value,
          htlcOutputsValue]
        rw [ih]
  have hanch :
      ((if c.anchorOutputs then
        [CommitmentOutput.localAnchor, CommitmentOutput.remoteAnchor] else []).map
          CommitmentOutput.value).sum = c.anchorOutputValue := by
    unfold Commitment.anchorOutputValue
    by_cases h : c.anchorOutputs <;>
      simp [h, CommitmentOutput.value, anchorOutputSat]
  simp only [Commitment.commitmentOutputs, List.map_append, List.sum_append]
  rw [hloc, hrem, hhtlc, hanch]
  unfold Commitment.totalOutputValue
  omega

/-- **Conservation-conditional funding bound.**  If a commitment's emitted
outputs plus its fee equal the funding value (the BOLT 3 balance equation),
then the output sum cannot exceed the funding value.  The fee is a `Nat`, so no
further side condition is needed.  This is the second half of LN-CH-002; it is
conditional because the model has no built-in conservation invariant. -/
theorem Commitment.totalOutputValue_le_funding_of_fee (c : Commitment)
    (h : c.totalOutputValue + c.feeSat = c.fundingValueSat) :
    c.totalOutputValue ≤ c.fundingValueSat := by
  omega

/-- The emitted output-list sum is within funding under the same explicit
conservation hypothesis. -/
theorem Commitment.commitmentOutputs_sum_le_funding_of_fee (c : Commitment)
    (h : c.totalOutputValue + c.feeSat = c.fundingValueSat) :
    (c.commitmentOutputs.map CommitmentOutput.value).sum ≤ c.fundingValueSat := by
  rw [Commitment.commitmentOutputs_sum_eq_totalOutputValue c]
  exact Commitment.totalOutputValue_le_funding_of_fee c h

/-- Combined conditional form of LN-CH-002: every emitted output is
nonnegative (unconditional) and, assuming the BOLT 3 balance equation, the
emitted sum is at most the funding value. -/
theorem Commitment.outputs_nonneg_and_sum_le_funding_of_fee (c : Commitment)
    (h : c.totalOutputValue + c.feeSat = c.fundingValueSat) :
    (∀ o ∈ c.commitmentOutputs, 0 ≤ (o.value : Int)) ∧
      (c.commitmentOutputs.map CommitmentOutput.value).sum ≤ c.fundingValueSat :=
  ⟨Commitment.commitmentOutputs_value_nonneg_int c,
    Commitment.commitmentOutputs_sum_le_funding_of_fee c h⟩

/-- **Catalog target `LN-CH-002`.**  No commitment output has a negative value
and, under the BOLT 3 balance equation
`totalOutputValue + feeSat = fundingValueSat`, the emitted output sum stays
within the funding value.

The first conjunct holds unconditionally (output values are `Nat` and are read
as `Int`, so a negative output is unrepresentable; see
`commitmentOutputs_value_nonneg_int`); the hypothesis `h` is needed only for
the second conjunct.  The funding bound is *not* unconditional, because
`Commitment` has no well-formedness invariant forcing the balance equation
(D46's `waveD_d46_unconditional_counterexample` refutes the bare bound).  The
proof is exactly C01's
`Commitment.outputs_nonneg_and_sum_le_funding_of_fee`, named at the catalog
target rather than restated with a new hypothesis. -/
theorem Commitment.outputs_nonnegative (c : Commitment)
    (h : c.totalOutputValue + c.feeSat = c.fundingValueSat) :
    (∀ o ∈ c.commitmentOutputs, 0 ≤ (o.value : Int)) ∧
      (c.commitmentOutputs.map CommitmentOutput.value).sum ≤ c.fundingValueSat :=
  Commitment.outputs_nonneg_and_sum_le_funding_of_fee c h

/-! ## Model-level trimming facts (LN-CH-003)

`commitmentOutputs` trims a `to_local`/`to_remote` output exactly when its
value is zero, and it emits every HTLC in `c.htlcs` verbatim.  The latter is
*not* BOLT 3's dust test: the model assumes HTLCs are already pre-trimmed (see
the docstring of `commitmentOutputs`), and `LnLean.Proofs.WaveD.D12` mechanizes
both the exact dust filter over `HTLCRecord` and the counterexample showing
that a zero-valued HTLC output is still emitted.  The lemmas below record the
true model-level facts, including the conditional "no sub-dust HTLC output"
statement for a pre-trimmed `htlcs` list.

No unconditional `output_ordering` theorem is added for this legacy output
function: D12 refutes it (`waveD_d12_output_ordering_fails`), and
`CommitmentOutput` carries neither a script nor an HTLC expiry, so the BOLT
`(value, script, cltv)` key is not even representable on this type.  The
faithful extension below (`CommitmentTx`) supplies both keys, the owner's dust
limit, and the deterministic BOLT 3 construction, and proves the true
ordering/trimming theorem there (`CommitmentTx.outputs_spec`). -/

/-- A `to_local` output occurs in `commitmentOutputs` exactly when it carries
the commitment's `toLocalSat` and that value is nonzero. -/
theorem Commitment.toLocal_mem_commitmentOutputs_iff {c : Commitment} {v : Nat} :
    CommitmentOutput.toLocal v ∈ c.commitmentOutputs ↔
      v = c.toLocalSat ∧ c.toLocalSat ≠ 0 := by
  unfold Commitment.commitmentOutputs
  by_cases h : c.toLocalSat = 0
  · rw [h]
    simp
  · simp [h]

/-- A `to_remote` output occurs in `commitmentOutputs` exactly when it carries
the commitment's `toRemoteSat` and that value is nonzero. -/
theorem Commitment.toRemote_mem_commitmentOutputs_iff {c : Commitment} {v : Nat} :
    CommitmentOutput.toRemote v ∈ c.commitmentOutputs ↔
      v = c.toRemoteSat ∧ c.toRemoteSat ≠ 0 := by
  unfold Commitment.commitmentOutputs
  by_cases h : c.toRemoteSat = 0
  · rw [h]
    simp
  · simp [h]

/-- Zero-valued `to_local` outputs are trimmed. -/
theorem Commitment.toLocal_zero_not_mem (c : Commitment) :
    CommitmentOutput.toLocal 0 ∉ c.commitmentOutputs := by
  rw [Commitment.toLocal_mem_commitmentOutputs_iff]
  intro h
  omega

/-- Zero-valued `to_remote` outputs are trimmed. -/
theorem Commitment.toRemote_zero_not_mem (c : Commitment) :
    CommitmentOutput.toRemote 0 ∉ c.commitmentOutputs := by
  rw [Commitment.toRemote_mem_commitmentOutputs_iff]
  intro h
  omega

/-- An HTLC output occurs in `commitmentOutputs` exactly when some HTLC in
`c.htlcs` has the same direction and amount.  This makes explicit that the
model applies no dust filter in `commitmentOutputs` itself. -/
theorem Commitment.htlc_mem_commitmentOutputs_iff {c : Commitment}
    {dir : Direction} {v : Nat} :
    CommitmentOutput.htlc dir v ∈ c.commitmentOutputs ↔
      ∃ h ∈ c.htlcs, h.direction = dir ∧ h.amountSat = v := by
  unfold Commitment.commitmentOutputs
  by_cases hl : c.toLocalSat = 0 <;>
  by_cases hr : c.toRemoteSat = 0 <;>
  by_cases ha : c.anchorOutputs <;>
  simp [hl, hr, ha, List.mem_map, and_assoc, and_comm]

/-- **Conditional no-dust-output lemma.**  If every HTLC already in `c.htlcs`
is at or above a dust limit (i.e. the record was built from pre-trimmed
HTLCs), then every emitted HTLC output is at or above that limit.  The
hypothesis is the model's pre-trimming contract, not BOLT 3's
`amount - second_stage_fee < dust_limit` test; the exact test and its
counterexample live in D12. -/
theorem Commitment.htlc_mem_commitmentOutputs_value_ge {c : Commitment}
    {dustLimitSat : Nat} (hpre : ∀ h ∈ c.htlcs, dustLimitSat ≤ h.amountSat) :
    ∀ (dir : Direction) (v : Nat),
      CommitmentOutput.htlc dir v ∈ c.commitmentOutputs → dustLimitSat ≤ v := by
  intro dir v hv
  obtain ⟨h, hmem, _hdir, rfl⟩ :=
    (Commitment.htlc_mem_commitmentOutputs_iff (c := c) (dir := dir)
      (v := v)).1 hv
  exact hpre h hmem

/-! ## BOLT 3 ordered, dust-trimmed commitment outputs (LN-CH-003 model extension)

The value-only `Commitment` record above has no `scriptPubKey`, no
`cltv_expiry` on its non-HTLC outputs, and (in `commitmentOutputs`) no dust
filter.  BOLT 3, however, defines the commitment transaction output set by

* trimming every output whose value is below the transaction owner's
  `dust_limit_satoshis` (with the second-stage fee charged first for HTLC
  outputs), and
* sorting the surviving outputs by value, then by `scriptpubkey` (memcmp with
  the shorter prefix first), then by `cltv_expiry` for HTLC outputs.

`LnLean.Proofs.WaveD.D12` shows that the unconditional ordering claim is
*false* of `commitmentOutputs` (`waveD_d12_output_ordering_fails`) and that
the CLTV tiebreak is unrecoverable from the old output type
(`waveD_d12_cltv_tiebreak_not_recoverable`).  That counterexample is retained
unchanged.

The types and functions below are the smallest faithful extension that makes
the true BOLT 3 statement expressible:

* `ScriptPubKey` is a raw script byte string (the model does not import a
  Bitcoin script interpreter; see `LnLean.Bitcoin.ScriptTemplates` for the
  L1 template side);
* `CommitmentTxOutput` tags one output with its kind, value, script, and CLTV;
* `CommitmentTxOutput.le` is BOLT 3's three-key lexicographic order;
* `CommitmentTx` adds the owner's dust limit and the per-output scripts to an
  existing `Commitment`, and `CommitmentTx.outputs` is the deterministic
  dust-trimmed, sorted construction.

The ordering/trimming theorem is `CommitmentTx.outputs_spec`; the catalog
target `output_ordering` in
`LnLean.Proofs.Channel.CommitmentOrderTargets` restates it.  No unconditional
statement about the legacy `commitmentOutputs` function is claimed: D12's
counterexample remains the correct statement about that function.
-/

/-! ### Script keys and BOLT 3 output order -/

/-- A raw `scriptPubKey`: the bytes that BOLT 3 compares with `memcmp`.  The
model does not interpret scripts; it only needs the byte string to order
outputs. -/
structure ScriptPubKey where
  bytes : List UInt8
deriving Repr, DecidableEq, BEq

theorem ScriptPubKey.ext_iff {a b : ScriptPubKey} : a = b ↔ a.bytes = b.bytes := by
  constructor
  · intro h; rw [h]
  · intro h; cases a; cases b; simp_all

theorem ScriptPubKey.ext {a b : ScriptPubKey} (h : a.bytes = b.bytes) : a = b :=
  ScriptPubKey.ext_iff.2 h

def ScriptPubKey.le (a b : ScriptPubKey) : Prop := a.bytes ≤ b.bytes

instance (a b : ScriptPubKey) : Decidable (a.le b) :=
  inferInstanceAs (Decidable (a.bytes ≤ b.bytes))

theorem ScriptPubKey.le_refl (a : ScriptPubKey) : a.le a := List.le_refl _

theorem ScriptPubKey.le_trans {a b c : ScriptPubKey} (hab : a.le b) (hbc : b.le c) : a.le c :=
  List.le_trans hab hbc

theorem ScriptPubKey.le_total (a b : ScriptPubKey) : a.le b ∨ b.le a := List.le_total _ _

/-- The role of an output in the BOLT 3 commitment construction. -/
inductive CommitmentOutputKind where
  | toLocal
  | toRemote
  | htlc (direction : Direction)
  | localAnchor
  | remoteAnchor
deriving Repr, DecidableEq, BEq

/-- One commitment output with the full BOLT 3 sort key: its kind, satoshi
value, `scriptPubKey`, and `cltv_expiry` (zero for non-HTLC outputs). -/
structure CommitmentTxOutput where
  kind : CommitmentOutputKind
  valueSat : Nat
  scriptPubKey : ScriptPubKey
  cltvExpiry : Height
deriving Repr, DecidableEq, BEq

/-- BOLT 3 non-strict lexicographic order: value, then `scriptPubKey`
(memcmp), then `cltv_expiry`.  The kind is not part of the key. -/
def CommitmentTxOutput.le (a b : CommitmentTxOutput) : Prop :=
  a.valueSat < b.valueSat ∨
    (a.valueSat = b.valueSat ∧
      (a.scriptPubKey.bytes < b.scriptPubKey.bytes ∨
        (a.scriptPubKey.bytes = b.scriptPubKey.bytes ∧ a.cltvExpiry ≤ b.cltvExpiry)))

instance (a b : CommitmentTxOutput) : Decidable (a.le b) := by
  unfold CommitmentTxOutput.le; infer_instance

theorem CommitmentTxOutput.le_refl (a : CommitmentTxOutput) : a.le a :=
  Or.inr ⟨rfl, Or.inr ⟨rfl, Nat.le_refl _⟩⟩

theorem CommitmentTxOutput.le_trans {a b c : CommitmentTxOutput}
    (hab : a.le b) (hbc : b.le c) : a.le c := by
  rcases hab with hv | ⟨hv, hs | ⟨hs, hc⟩⟩
  · rcases hbc with hv' | ⟨hv', _⟩
    · exact Or.inl (Nat.lt_trans hv hv')
    · exact Or.inl (by omega)
  · rcases hbc with hv' | ⟨hv', hs' | ⟨hs', hc'⟩⟩
    · exact Or.inl (by omega)
    · exact Or.inr ⟨by omega, Or.inl (List.lt_trans hs hs')⟩
    · exact Or.inr ⟨by omega, Or.inl (hs' ▸ hs)⟩
  · rcases hbc with hv' | ⟨hv', hs' | ⟨hs', hc'⟩⟩
    · exact Or.inl (by omega)
    · exact Or.inr ⟨by omega, Or.inl (by rw [hs]; exact hs')⟩
    · exact Or.inr ⟨by omega, Or.inr ⟨by rw [hs, hs'], Nat.le_trans hc hc'⟩⟩

theorem CommitmentTxOutput.le_total (a b : CommitmentTxOutput) : a.le b ∨ b.le a := by
  rcases Nat.lt_trichotomy a.valueSat b.valueSat with hv | hv | hv
  · exact Or.inl (Or.inl hv)
  · rcases Std.lt_trichotomy a.scriptPubKey.bytes b.scriptPubKey.bytes with hs | hs | hs
    · exact Or.inl (Or.inr ⟨hv, Or.inl hs⟩)
    · rcases Nat.le_total a.cltvExpiry b.cltvExpiry with hc | hc
      · exact Or.inl (Or.inr ⟨hv, Or.inr ⟨hs, hc⟩⟩)
      · exact Or.inr (Or.inr ⟨hv.symm, Or.inr ⟨hs.symm, hc⟩⟩)
    · exact Or.inr (Or.inr ⟨hv.symm, Or.inl hs⟩)
  · exact Or.inr (Or.inl hv)

/-- Sort commitment outputs by the BOLT 3 three-key order.  `mergeSort` is a
function, so the result is deterministic for a fixed input list; equal-key
outputs are interchangeable on-chain and their relative order is irrelevant. -/
def sortOutputs (l : List CommitmentTxOutput) : List CommitmentTxOutput :=
  l.mergeSort (fun a b => decide (CommitmentTxOutput.le a b))

theorem sortOutputs_perm (l : List CommitmentTxOutput) : (sortOutputs l).Perm l :=
  List.mergeSort_perm l _

theorem sortOutputs_pairwise (l : List CommitmentTxOutput) :
    (sortOutputs l).Pairwise CommitmentTxOutput.le := by
  have h := List.pairwise_mergeSort
    (le := fun a b => decide (CommitmentTxOutput.le a b))
    (by
      intro a b c hab hbc
      exact decide_eq_true
        (CommitmentTxOutput.le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc)))
    (by
      intro a b
      by_cases hab : CommitmentTxOutput.le a b
      · simp [decide_eq_true hab]
      · rcases CommitmentTxOutput.le_total a b with h | h
        · exact absurd h hab
        · simp [decide_eq_false hab, decide_eq_true h])
    l
  exact h.imp (fun {a b} hab => of_decide_eq_true hab)

theorem sortOutputs_values (l : List CommitmentTxOutput) :
    (sortOutputs l).Pairwise (fun a b => a.valueSat ≤ b.valueSat) := by
  refine (sortOutputs_pairwise l).imp ?_
  intro a b hab
  rcases hab with hv | ⟨hv, _⟩
  · exact Nat.le_of_lt hv
  · exact Nat.le_of_eq hv

theorem sortOutputs_scripts (l : List CommitmentTxOutput) :
    (sortOutputs l).Pairwise (fun a b =>
      a.valueSat = b.valueSat → a.scriptPubKey.le b.scriptPubKey) := by
  refine (sortOutputs_pairwise l).imp ?_
  intro a b hab hv
  rcases hab with hlt | ⟨_, hs | ⟨hs, _⟩⟩
  · omega
  · exact List.le_of_lt hs
  · change a.scriptPubKey.bytes ≤ b.scriptPubKey.bytes
    rw [hs]
    exact List.le_refl _

theorem sortOutputs_cltvs (l : List CommitmentTxOutput) :
    (sortOutputs l).Pairwise (fun a b =>
      a.valueSat = b.valueSat → a.scriptPubKey = b.scriptPubKey →
        a.cltvExpiry ≤ b.cltvExpiry) := by
  refine (sortOutputs_pairwise l).imp ?_
  intro a b hab hv hsp
  rcases hab with hlt | ⟨_, hs | ⟨hs, hc⟩⟩
  · omega
  · exfalso
    exact List.lt_irrefl _ (hsp ▸ hs)
  · exact hc

/-- The script, CLTV, and dust data that the value-only `Commitment` record
does not carry.  `dustLimitSat` is the transaction owner's
`dust_limit_satoshis`.  `htlcScript` is an explicit function because script
bytes depend on funding keys and payment hashes that are outside this module. -/
structure CommitmentTx where
  commitment : Commitment
  dustLimitSat : Nat
  toLocalScript : ScriptPubKey
  toRemoteScript : ScriptPubKey
  localAnchorScript : ScriptPubKey
  remoteAnchorScript : ScriptPubKey
  htlcScript : CommitmentHTLCOutput → ScriptPubKey
  /-- The **net** (second-stage) satoshi value of an HTLC output.  BOLT 3 runs
  the dust test on `amount - second_stage_fee`
  (`03-transactions.md:330-346`), while the commitment output itself carries
  the **gross** `amountSat`.  The default delegates to the record field
  `CommitmentHTLCOutput.netAmountSat`, whose own default is the identity
  `amountSat`, so every existing `CommitmentTx` literal keeps its legacy
  gross-equals-net semantics while a BOLT-3-exact record can set the net value
  once at the `CommitmentHTLCOutput` boundary. -/
  netAmountSat : CommitmentHTLCOutput → Nat := fun h => h.netAmountSat
  /-- Gross satoshi value removed by the BOLT 3 dust filter.  BOLT 3 adds a
  trimmed output's value to the commitment transaction fee, so this is the
  difference between the nominal output value and the value the commitment
  transaction actually pays.  The default zero preserves every existing
  `CommitmentTx` literal. -/
  trimmedSat : Nat := 0

def CommitmentTxOutput.toLocal (v : Nat) (script : ScriptPubKey) : CommitmentTxOutput :=
  { kind := .toLocal, valueSat := v, scriptPubKey := script, cltvExpiry := 0 }

def CommitmentTxOutput.toRemote (v : Nat) (script : ScriptPubKey) : CommitmentTxOutput :=
  { kind := .toRemote, valueSat := v, scriptPubKey := script, cltvExpiry := 0 }

def CommitmentTxOutput.htlc (h : CommitmentHTLCOutput) (script : ScriptPubKey) :
    CommitmentTxOutput :=
  { kind := .htlc h.direction, valueSat := h.amountSat, scriptPubKey := script,
    cltvExpiry := h.cltvExpiry }

def CommitmentTxOutput.localAnchor (script : ScriptPubKey) : CommitmentTxOutput :=
  { kind := .localAnchor, valueSat := anchorOutputSat, scriptPubKey := script,
    cltvExpiry := 0 }

def CommitmentTxOutput.remoteAnchor (script : ScriptPubKey) : CommitmentTxOutput :=
  { kind := .remoteAnchor, valueSat := anchorOutputSat, scriptPubKey := script,
    cltvExpiry := 0 }

/-- The `to_local` output of the rich commitment model, or `none` when its
value is below the owner's dust limit. -/
def CommitmentTx.toLocalOutput (tx : CommitmentTx) : Option CommitmentTxOutput :=
  if tx.dustLimitSat ≤ tx.commitment.toLocalSat then
    some (CommitmentTxOutput.toLocal tx.commitment.toLocalSat tx.toLocalScript)
  else none

/-- The `to_remote` output, or `none` when below the owner's dust limit. -/
def CommitmentTx.toRemoteOutput (tx : CommitmentTx) : Option CommitmentTxOutput :=
  if tx.dustLimitSat ≤ tx.commitment.toRemoteSat then
    some (CommitmentTxOutput.toRemote tx.commitment.toRemoteSat tx.toRemoteScript)
  else none

/-- The HTLC output for `h`, or `none` when its post-second-stage-fee value
is below the owner's dust limit.  This is BOLT 3's trimming test
`amount - second_stage_fee < dust_limit_satoshis`. -/
def CommitmentTx.htlcOutput (tx : CommitmentTx) (h : CommitmentHTLCOutput) :
    Option CommitmentTxOutput :=
  if tx.dustLimitSat ≤ h.amountSat then
    some (CommitmentTxOutput.htlc h (tx.htlcScript h))
  else none

def CommitmentTx.localAnchorOutput (tx : CommitmentTx) : Option CommitmentTxOutput :=
  if tx.commitment.anchorOutputs then
    some (CommitmentTxOutput.localAnchor tx.localAnchorScript)
  else none

def CommitmentTx.remoteAnchorOutput (tx : CommitmentTx) : Option CommitmentTxOutput :=
  if tx.commitment.anchorOutputs then
    some (CommitmentTxOutput.remoteAnchor tx.remoteAnchorScript)
  else none

/-- The output list before BOLT 3 sorting: trimmed non-HTLC outputs in the
construction order `to_local, to_remote`, then the surviving HTLCs in the
commitment's HTLC order, then the anchors. -/
def CommitmentTx.outputsUnsorted (tx : CommitmentTx) : List CommitmentTxOutput :=
  tx.toLocalOutput.toList ++
    (tx.toRemoteOutput.toList ++
      (tx.commitment.htlcs.filterMap tx.htlcOutput ++
        (tx.localAnchorOutput.toList ++ tx.remoteAnchorOutput.toList)))

/-- The BOLT 3 commitment output list: the trimmed construction, sorted by
value, then script, then CLTV.  This is the object of `outputs_spec` and of the
catalog target `output_ordering`. -/
def CommitmentTx.outputs (tx : CommitmentTx) : List CommitmentTxOutput :=
  sortOutputs tx.outputsUnsorted

/-! ### Net-based BOLT 3 dust test (CH-03)

`CommitmentTx.htlcOutput` above is retained unchanged for compatibility: it
tests the gross `amountSat`, the pre-CH-03 convention in which a record's
`amountSat` is already net of the second-stage fee.  The CH-03 path below is
the BOLT-3-exact one: `CommitmentTxOutput.htlc` still carries the gross
`amountSat`, while the dust test uses `netAmountSat`.  Under the BOLT 3 fee
schedule the two forms are related by
`gross = net + second_stage_fee`, so the net test is exactly
`gross < dust_limit + second_stage_fee`.
-/

/-- BOLT 3's dust-trimmed HTLC output, testing the **net** (second-stage)
value while emitting the **gross** `amountSat`. -/
def CommitmentTx.htlcOutputNet (tx : CommitmentTx) (h : CommitmentHTLCOutput) :
    Option CommitmentTxOutput :=
  if tx.dustLimitSat ≤ tx.netAmountSat h then
    some (CommitmentTxOutput.htlc h (tx.htlcScript h))
  else none

/-- The pre-sort output list of the net-based (BOLT-3-exact) construction. -/
def CommitmentTx.outputsUnsortedNet (tx : CommitmentTx) : List CommitmentTxOutput :=
  tx.toLocalOutput.toList ++
    (tx.toRemoteOutput.toList ++
      (tx.commitment.htlcs.filterMap tx.htlcOutputNet ++
        (tx.localAnchorOutput.toList ++ tx.remoteAnchorOutput.toList)))

/-- The sorted net-based output list.  This is the CH-03 replacement for
`CommitmentTx.outputs` when `amountSat` is gross and `netAmountSat` is the
second-stage value. -/
def CommitmentTx.outputsNet (tx : CommitmentTx) : List CommitmentTxOutput :=
  sortOutputs tx.outputsUnsortedNet

/-- The gross value removed by the net-based BOLT 3 dust filter.  This is the
computed counterpart of the recorded `CommitmentTx.trimmedSat` field. -/
def CommitmentTx.trimmedValue (tx : CommitmentTx) : Nat :=
  tx.commitment.trimmedSat tx.dustLimitSat tx.netAmountSat

theorem CommitmentTx.trimmedValue_eq_trimmedSat (tx : CommitmentTx) :
    tx.trimmedValue = tx.commitment.trimmedSat tx.dustLimitSat tx.netAmountSat := rfl

theorem CommitmentTx.trimmedValue_eq_trimmedValueFor (tx : CommitmentTx) :
    tx.trimmedValue =
      tx.commitment.trimmedValueFor tx.dustLimitSat tx.netAmountSat := rfl

/-- The net projection is exactly the record-level field.  The default of
`CommitmentTx.netAmountSat` has this shape; a caller that overrides it records
a transaction-specific projection. -/
def CommitmentTx.UsesRecordNet (tx : CommitmentTx) : Prop :=
  ∀ h : CommitmentHTLCOutput, tx.netAmountSat h = h.netAmountSat

theorem CommitmentTx.usesRecordNet_default (tx : CommitmentTx) :
    ({ tx with netAmountSat := fun h => h.netAmountSat }).UsesRecordNet :=
  fun _ => rfl

/-- The gross value removed by trimming computed from the record fields. -/
def CommitmentTx.recordTrimmedValue (tx : CommitmentTx) : Nat :=
  tx.commitment.trimmedSat tx.dustLimitSat (fun h => h.netAmountSat)

theorem CommitmentTx.recordTrimmedValue_eq_trimmedValueFor (tx : CommitmentTx) :
    tx.recordTrimmedValue =
      tx.commitment.trimmedValueFor tx.dustLimitSat (fun h => h.netAmountSat) := rfl

/-- The BOLT 3 migration at the record-field boundary.  It applies the same
trim filter as `CommitmentTx.migratedFrom`, but reads `netAmountSat` from each
`CommitmentHTLCOutput` and records the removed gross value in both the stored
`Commitment.trimmedTotalSat` field and the rich `CommitmentTx.trimmedSat`
field. -/
def CommitmentTx.migrateNet (tx : CommitmentTx) : CommitmentTx :=
  { tx with
    commitment := tx.commitment.migrateNet tx.dustLimitSat
    netAmountSat := fun h => h.netAmountSat
    trimmedSat := tx.recordTrimmedValue }

theorem CommitmentTx.migrateNet_commitment (tx : CommitmentTx) :
    (tx.migrateNet).commitment =
      tx.commitment.migrateNet tx.dustLimitSat := rfl

theorem CommitmentTx.migrateNet_netAmountSat (tx : CommitmentTx)
    (h : CommitmentHTLCOutput) :
    (tx.migrateNet).netAmountSat h = h.netAmountSat := rfl

theorem CommitmentTx.migrateNet_usesRecordNet (tx : CommitmentTx) :
    (tx.migrateNet).UsesRecordNet :=
  fun _ => rfl

theorem CommitmentTx.migrateNet_trimmedSat (tx : CommitmentTx) :
    (tx.migrateNet).trimmedSat = tx.recordTrimmedValue := rfl

theorem CommitmentTx.migrateNet_htlcs (tx : CommitmentTx) :
    (tx.migrateNet).commitment.htlcs =
      tx.commitment.htlcs.filter
        (fun h => h.keepAtDust tx.dustLimitSat) := rfl

theorem CommitmentTx.migrateNet_commitment_trimmedTotalSat (tx : CommitmentTx) :
    (tx.migrateNet).commitment.trimmedTotalSat = tx.recordTrimmedValue := rfl

/-! ### Legacy-consumer migration path (CH-01)

The existing consumers of a commitment transaction read a `List
CommitmentOutput` built from `Commitment.commitmentOutputs` (sighash views,
`commitment_signed` coverage, reserve checks).  Those consumers do not know
about `CommitmentTx` scripts, the dust limit, or the net second-stage value.
The three definitions below make the migration explicit at that boundary:

* `consumerOutputs` is the legacy list they read;
* `migrateForConsumer` is the drop-in net replacement for the transaction
  (definitionally `migrateNet`, exposed under a consumer-facing name);
* `migratedConsumerOutputs` is the legacy-shaped list after migration, so a
  consumer can keep its output type and change only the commitment it reads.

`netConsumerOutputs` is the sorted rich net list a consumer should read when
it can consume `CommitmentTxOutput` directly.  The refinement proofs live in
`LnLean.Proofs.Channel.CommitmentConsumerTargets`. -/

/-- The legacy output list a pre-CH-01 consumer reads from a transaction. -/
def CommitmentTx.consumerOutputs (tx : CommitmentTx) : List CommitmentOutput :=
  tx.commitment.commitmentOutputs

/-- Migrate a transaction to the BOLT 3 net path at a legacy consumer
boundary.  This is the same record migration as `migrateNet`, named for the
consumer-facing integration step. -/
def CommitmentTx.migrateForConsumer (tx : CommitmentTx) : CommitmentTx :=
  tx.migrateNet

/-- The legacy-shaped output list after the net migration.  A consumer that
expects `List CommitmentOutput` can switch from `consumerOutputs` to this
function without changing its output type. -/
def CommitmentTx.migratedConsumerOutputs (tx : CommitmentTx) :
    List CommitmentOutput :=
  tx.migrateForConsumer.commitment.commitmentOutputs

/-- The sorted rich net output list at the consumer boundary.  A consumer that
can consume `CommitmentTxOutput` should read this list instead of
`migratedConsumerOutputs`; the two differ only by the BOLT 3 sort. -/
def CommitmentTx.netConsumerOutputs (tx : CommitmentTx) :
    List CommitmentTxOutput :=
  tx.migrateForConsumer.outputsNet

theorem CommitmentTx.migrateForConsumer_eq_migrateNet (tx : CommitmentTx) :
    tx.migrateForConsumer = tx.migrateNet := rfl

theorem CommitmentTx.consumerOutputs_eq (tx : CommitmentTx) :
    tx.consumerOutputs = tx.commitment.commitmentOutputs := rfl

theorem CommitmentTx.migratedConsumerOutputs_eq (tx : CommitmentTx) :
    tx.migratedConsumerOutputs =
      (tx.migrateNet).commitment.commitmentOutputs := rfl

theorem CommitmentTx.netConsumerOutputs_eq (tx : CommitmentTx) :
    tx.netConsumerOutputs = (tx.migrateNet).outputsNet := rfl

/-- Lift a legacy `Commitment` to a rich `CommitmentTx` at a construction site.
The caller supplies the owner's dust limit and the per-output scripts; the net
projection defaults to the record field `CommitmentHTLCOutput.netAmountSat`,
so a legacy record keeps its gross = net semantics until the caller sets the
net fields.  This is the construction half of the consumer migration: existing
`Commitment` producers do not have to change, they wrap the record here. -/
def CommitmentTx.ofCommitment (c : Commitment) (dustLimitSat : Nat)
    (toLocalScript toRemoteScript localAnchorScript remoteAnchorScript :
      ScriptPubKey)
    (htlcScript : CommitmentHTLCOutput → ScriptPubKey) : CommitmentTx :=
  { commitment := c
    dustLimitSat := dustLimitSat
    toLocalScript := toLocalScript
    toRemoteScript := toRemoteScript
    localAnchorScript := localAnchorScript
    remoteAnchorScript := remoteAnchorScript
    htlcScript := htlcScript }

theorem CommitmentTx.ofCommitment_commitment (c : Commitment)
    (dustLimitSat : Nat) (toLocalScript toRemoteScript localAnchorScript
      remoteAnchorScript : ScriptPubKey)
    (htlcScript : CommitmentHTLCOutput → ScriptPubKey) :
    (CommitmentTx.ofCommitment c dustLimitSat toLocalScript toRemoteScript
      localAnchorScript remoteAnchorScript htlcScript).commitment = c := rfl

theorem CommitmentTx.outputsNet_perm (tx : CommitmentTx) :
    tx.outputsNet.Perm tx.outputsUnsortedNet :=
  sortOutputs_perm tx.outputsUnsortedNet

theorem CommitmentTx.mem_outputsNet_iff {tx : CommitmentTx} {o : CommitmentTxOutput} :
    o ∈ tx.outputsNet ↔ o ∈ tx.outputsUnsortedNet :=
  (sortOutputs_perm tx.outputsUnsortedNet).mem_iff

theorem CommitmentTx.mem_outputsUnsortedNet_iff {tx : CommitmentTx}
    {o : CommitmentTxOutput} :
    o ∈ tx.outputsUnsortedNet ↔
      o ∈ tx.toLocalOutput.toList ∨
      o ∈ tx.toRemoteOutput.toList ∨
      o ∈ tx.commitment.htlcs.filterMap tx.htlcOutputNet ∨
      o ∈ tx.localAnchorOutput.toList ∨
      o ∈ tx.remoteAnchorOutput.toList := by
  simp [CommitmentTx.outputsUnsortedNet, List.mem_append]

theorem CommitmentTx.mem_htlcOutputNet_iff {tx : CommitmentTx}
    {h : CommitmentHTLCOutput} {o : CommitmentTxOutput} :
    tx.htlcOutputNet h = some o ↔
      tx.dustLimitSat ≤ tx.netAmountSat h ∧
        o = CommitmentTxOutput.htlc h (tx.htlcScript h) := by
  unfold CommitmentTx.htlcOutputNet
  by_cases hd : tx.dustLimitSat ≤ tx.netAmountSat h <;> simp [hd, eq_comm]

theorem CommitmentTx.htlcOutputNet_eq_none_of_dust (tx : CommitmentTx)
    (h : CommitmentHTLCOutput) (hd : tx.netAmountSat h < tx.dustLimitSat) :
    tx.htlcOutputNet h = none := by
  unfold CommitmentTx.htlcOutputNet
  simp [Nat.not_le.mpr hd]

theorem CommitmentTx.htlcOutputNet_mem_outputsNet (tx : CommitmentTx)
    (h : CommitmentHTLCOutput) (hmem : h ∈ tx.commitment.htlcs)
    (hd : tx.dustLimitSat ≤ tx.netAmountSat h) :
    CommitmentTxOutput.htlc h (tx.htlcScript h) ∈ tx.outputsNet := by
  rw [CommitmentTx.mem_outputsNet_iff, CommitmentTx.mem_outputsUnsortedNet_iff]
  right; right; left
  rw [List.mem_filterMap]
  exact ⟨h, hmem, (CommitmentTx.mem_htlcOutputNet_iff).2 ⟨hd, rfl⟩⟩

theorem CommitmentTx.outputsNet_pairwise (tx : CommitmentTx) :
    tx.outputsNet.Pairwise CommitmentTxOutput.le :=
  sortOutputs_pairwise tx.outputsUnsortedNet

theorem CommitmentTx.outputsNet_values_sorted (tx : CommitmentTx) :
    (tx.outputsNet.map (fun o => o.valueSat)).Pairwise (· ≤ ·) := by
  rw [List.pairwise_map]
  exact sortOutputs_values tx.outputsUnsortedNet

theorem CommitmentTx.outputsNet_scripts_sorted (tx : CommitmentTx) :
    tx.outputsNet.Pairwise (fun a b =>
      a.valueSat = b.valueSat → a.scriptPubKey.le b.scriptPubKey) :=
  sortOutputs_scripts tx.outputsUnsortedNet

theorem CommitmentTx.outputsNet_cltvs_sorted (tx : CommitmentTx) :
    tx.outputsNet.Pairwise (fun a b =>
      a.valueSat = b.valueSat → a.scriptPubKey = b.scriptPubKey →
        a.cltvExpiry ≤ b.cltvExpiry) :=
  sortOutputs_cltvs tx.outputsUnsortedNet

theorem CommitmentTx.outputs_perm (tx : CommitmentTx) :
    tx.outputs.Perm tx.outputsUnsorted :=
  sortOutputs_perm tx.outputsUnsorted

theorem CommitmentTx.mem_outputs_iff {tx : CommitmentTx} {o : CommitmentTxOutput} :
    o ∈ tx.outputs ↔ o ∈ tx.outputsUnsorted :=
  (sortOutputs_perm tx.outputsUnsorted).mem_iff

theorem CommitmentTx.mem_outputsUnsorted_iff {tx : CommitmentTx} {o : CommitmentTxOutput} :
    o ∈ tx.outputsUnsorted ↔
      o ∈ tx.toLocalOutput.toList ∨
      o ∈ tx.toRemoteOutput.toList ∨
      o ∈ tx.commitment.htlcs.filterMap tx.htlcOutput ∨
      o ∈ tx.localAnchorOutput.toList ∨
      o ∈ tx.remoteAnchorOutput.toList := by
  simp [CommitmentTx.outputsUnsorted, List.mem_append]

theorem CommitmentTx.mem_toLocalOutput_iff {tx : CommitmentTx} {o : CommitmentTxOutput} :
    o ∈ tx.toLocalOutput.toList ↔
      tx.dustLimitSat ≤ tx.commitment.toLocalSat ∧
        o = CommitmentTxOutput.toLocal tx.commitment.toLocalSat tx.toLocalScript := by
  unfold CommitmentTx.toLocalOutput
  by_cases h : tx.dustLimitSat ≤ tx.commitment.toLocalSat <;> simp [h]

theorem CommitmentTx.mem_toRemoteOutput_iff {tx : CommitmentTx} {o : CommitmentTxOutput} :
    o ∈ tx.toRemoteOutput.toList ↔
      tx.dustLimitSat ≤ tx.commitment.toRemoteSat ∧
        o = CommitmentTxOutput.toRemote tx.commitment.toRemoteSat tx.toRemoteScript := by
  unfold CommitmentTx.toRemoteOutput
  by_cases h : tx.dustLimitSat ≤ tx.commitment.toRemoteSat <;> simp [h]

theorem CommitmentTx.mem_htlcOutput_iff {tx : CommitmentTx} {h : CommitmentHTLCOutput}
    {o : CommitmentTxOutput} :
    tx.htlcOutput h = some o ↔
      tx.dustLimitSat ≤ h.amountSat ∧
        o = CommitmentTxOutput.htlc h (tx.htlcScript h) := by
  unfold CommitmentTx.htlcOutput
  by_cases hd : tx.dustLimitSat ≤ h.amountSat <;> simp [hd, eq_comm]

theorem CommitmentTx.htlcOutput_eq_none_of_dust (tx : CommitmentTx)
    (h : CommitmentHTLCOutput) (hd : h.amountSat < tx.dustLimitSat) :
    tx.htlcOutput h = none := by
  unfold CommitmentTx.htlcOutput
  simp [Nat.not_le.mpr hd]

theorem CommitmentTx.htlcOutput_mem_outputs (tx : CommitmentTx)
    (h : CommitmentHTLCOutput) (hmem : h ∈ tx.commitment.htlcs)
    (hd : tx.dustLimitSat ≤ h.amountSat) :
    CommitmentTxOutput.htlc h (tx.htlcScript h) ∈ tx.outputs := by
  rw [CommitmentTx.mem_outputs_iff, CommitmentTx.mem_outputsUnsorted_iff]
  right; right; left
  rw [List.mem_filterMap]
  exact ⟨h, hmem, (CommitmentTx.mem_htlcOutput_iff).2 ⟨hd, rfl⟩⟩

/-- Every emitted output other than an anchor is at or above the dust limit.
Anchors are exempt: BOLT 3 fixes them at 330 satoshis and adds them whenever
`option_anchors` is negotiated (the single-anchor exception is out of scope). -/
theorem CommitmentTx.nonAnchor_output_value_ge_dust (tx : CommitmentTx)
    {o : CommitmentTxOutput} (ho : o ∈ tx.outputs)
    (hl : o.kind ≠ .localAnchor) (hr : o.kind ≠ .remoteAnchor) :
    tx.dustLimitSat ≤ o.valueSat := by
  rw [CommitmentTx.mem_outputs_iff, CommitmentTx.mem_outputsUnsorted_iff] at ho
  rcases ho with h | h | h | h | h
  · rw [CommitmentTx.mem_toLocalOutput_iff] at h
    rw [h.2]
    exact h.1
  · rw [CommitmentTx.mem_toRemoteOutput_iff] at h
    rw [h.2]
    exact h.1
  · rw [List.mem_filterMap] at h
    obtain ⟨a, _, ha⟩ := h
    rw [CommitmentTx.mem_htlcOutput_iff] at ha
    rw [ha.2]
    exact ha.1
  · unfold CommitmentTx.localAnchorOutput at h
    by_cases ha : tx.commitment.anchorOutputs
    · simp [ha] at h
      have hk : o.kind = .localAnchor := by rw [h]; rfl
      exact absurd hk hl
    · simp [ha] at h
  · unfold CommitmentTx.remoteAnchorOutput at h
    by_cases ha : tx.commitment.anchorOutputs
    · simp [ha] at h
      have hk : o.kind = .remoteAnchor := by rw [h]; rfl
      exact absurd hk hr
    · simp [ha] at h




def CommitmentTxOutput.toCommitmentOutput (o : CommitmentTxOutput) : CommitmentOutput :=
  match o.kind with
  | .toLocal => .toLocal o.valueSat
  | .toRemote => .toRemote o.valueSat
  | .htlc d => .htlc d o.valueSat
  | .localAnchor => .localAnchor
  | .remoteAnchor => .remoteAnchor

/-- With dust limit zero and non-zero `to_local`/`to_remote`, the kind/value
projection of the rich pre-sort output list is exactly the legacy
`Commitment.commitmentOutputs`.  The extension therefore adds script, CLTV, and
dust data without changing the non-dust output set. -/
theorem CommitmentTx.map_toCommitmentOutput_outputsUnsorted (tx : CommitmentTx)
    (hdust : tx.dustLimitSat = 0)
    (hl : tx.commitment.toLocalSat ≠ 0) (hr : tx.commitment.toRemoteSat ≠ 0) :
    (tx.outputsUnsorted.map CommitmentTxOutput.toCommitmentOutput) =
      tx.commitment.commitmentOutputs := by
  by_cases ha : tx.commitment.anchorOutputs <;>
  simp [CommitmentTx.outputsUnsorted, CommitmentTx.toLocalOutput,
    CommitmentTx.toRemoteOutput, CommitmentTx.htlcOutput,
    CommitmentTx.localAnchorOutput, CommitmentTx.remoteAnchorOutput,
    Commitment.commitmentOutputs, CommitmentTxOutput.toCommitmentOutput,
    CommitmentTxOutput.htlc, CommitmentTxOutput.toLocal,
    CommitmentTxOutput.toRemote, CommitmentTxOutput.localAnchor,
    CommitmentTxOutput.remoteAnchor, hdust, hl, hr, ha, List.map_filterMap]




theorem CommitmentTx.outputs_pairwise (tx : CommitmentTx) :
    tx.outputs.Pairwise CommitmentTxOutput.le :=
  sortOutputs_pairwise tx.outputsUnsorted

theorem CommitmentTx.outputs_values_sorted (tx : CommitmentTx) :
    (tx.outputs.map (fun o => o.valueSat)).Pairwise (· ≤ ·) := by
  rw [List.pairwise_map]
  exact sortOutputs_values tx.outputsUnsorted

theorem CommitmentTx.outputs_scripts_sorted (tx : CommitmentTx) :
    tx.outputs.Pairwise (fun a b =>
      a.valueSat = b.valueSat → a.scriptPubKey.le b.scriptPubKey) :=
  sortOutputs_scripts tx.outputsUnsorted

theorem CommitmentTx.outputs_cltvs_sorted (tx : CommitmentTx) :
    tx.outputs.Pairwise (fun a b =>
      a.valueSat = b.valueSat → a.scriptPubKey = b.scriptPubKey →
        a.cltvExpiry ≤ b.cltvExpiry) :=
  sortOutputs_cltvs tx.outputsUnsorted

theorem CommitmentTx.toLocal_trimmed_iff (tx : CommitmentTx) :
    tx.toLocalOutput = none ↔ tx.commitment.toLocalSat < tx.dustLimitSat := by
  unfold CommitmentTx.toLocalOutput
  by_cases h : tx.dustLimitSat ≤ tx.commitment.toLocalSat <;>
    simp [h] <;> omega

theorem CommitmentTx.toRemote_trimmed_iff (tx : CommitmentTx) :
    tx.toRemoteOutput = none ↔ tx.commitment.toRemoteSat < tx.dustLimitSat := by
  unfold CommitmentTx.toRemoteOutput
  by_cases h : tx.dustLimitSat ≤ tx.commitment.toRemoteSat <;>
    simp [h] <;> omega

theorem CommitmentTx.no_dust_htlc_output (tx : CommitmentTx)
    {o : CommitmentTxOutput} (ho : o ∈ tx.outputs) (hk : ∃ dir, o.kind = .htlc dir) :
    tx.dustLimitSat ≤ o.valueSat := by
  apply CommitmentTx.nonAnchor_output_value_ge_dust tx ho
  · rintro h
    obtain ⟨dir, hd⟩ := hk
    rw [h] at hd
    cases hd
  · rintro h
    obtain ⟨dir, hd⟩ := hk
    rw [h] at hd
    cases hd

/-- **Rich-model specification of `LN-CH-003`.**  The sorted output list is a
permutation of the trimmed construction; it satisfies the three BOLT 3 order
components; `to_local`/`to_remote` are trimmed exactly below the dust limit;
dust HTLCs produce no output and non-dust HTLCs produce theirs; and every
non-anchor emitted output is at or above the dust limit. -/
theorem CommitmentTx.outputs_spec (tx : CommitmentTx) :
    tx.outputs.Perm tx.outputsUnsorted ∧
    tx.outputs.Pairwise CommitmentTxOutput.le ∧
    (tx.outputs.map (fun o => o.valueSat)).Pairwise (· ≤ ·) ∧
    tx.outputs.Pairwise (fun a b =>
      a.valueSat = b.valueSat → a.scriptPubKey.le b.scriptPubKey) ∧
    tx.outputs.Pairwise (fun a b =>
      a.valueSat = b.valueSat → a.scriptPubKey = b.scriptPubKey →
        a.cltvExpiry ≤ b.cltvExpiry) ∧
    (tx.toLocalOutput = none ↔ tx.commitment.toLocalSat < tx.dustLimitSat) ∧
    (tx.toRemoteOutput = none ↔ tx.commitment.toRemoteSat < tx.dustLimitSat) ∧
    (∀ h ∈ tx.commitment.htlcs, h.amountSat < tx.dustLimitSat → tx.htlcOutput h = none) ∧
    (∀ h ∈ tx.commitment.htlcs, tx.dustLimitSat ≤ h.amountSat →
      CommitmentTxOutput.htlc h (tx.htlcScript h) ∈ tx.outputs) ∧
    (∀ o ∈ tx.outputs, o.kind ≠ .localAnchor → o.kind ≠ .remoteAnchor →
      tx.dustLimitSat ≤ o.valueSat) := by
  exact ⟨CommitmentTx.outputs_perm tx, CommitmentTx.outputs_pairwise tx,
    CommitmentTx.outputs_values_sorted tx, CommitmentTx.outputs_scripts_sorted tx,
    CommitmentTx.outputs_cltvs_sorted tx, CommitmentTx.toLocal_trimmed_iff tx,
    CommitmentTx.toRemote_trimmed_iff tx, fun h _ hd => CommitmentTx.htlcOutput_eq_none_of_dust tx h hd,
    fun h hm hd => CommitmentTx.htlcOutput_mem_outputs tx h hm hd,
    fun o ho => CommitmentTx.nonAnchor_output_value_ge_dust tx ho⟩

end LnLean.Channel
