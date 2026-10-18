import LnLean.Channel.Commitment
import LnLean.Channel.Types
import LnLean.Bitcoin.ScriptTemplates

/-!
# Anchor debit conservation

BOLT 3 deducts the commitment fee *and* the two 330-satoshi anchor outputs from
the funder's own output.  The Wave-C constructor
`LnLean.Channel.commitmentPairOfBalances` deducts only the fee, so an anchored
commitment overfunds its outputs by exactly `2 * 330 = 660` satoshis.  This
module records the missing debit rule as a reusable predicate, proves the
general overfunding gap, mechanizes the concrete 660-satoshi counterexample,
and constructs/proves the corrected pair.

The corrected construction is conditional on the funder being able to pay
`fee + 660`: `Nat` subtraction truncates, so without that hypothesis the
corrected record would silently underflow and the conservation equation would
not hold.  This affordability condition is a real BOLT 3 precondition, not a
weakening of the arithmetic claim.

BOLT 3 §2 (`03-transactions.md:148-198`, anchor outputs; `:319-324`, the
funder pays the anchors) and §4 (`03-transactions.md:490-502`, expected
weights).  rust-lightning at
`fe4900930c6bd5786ec4203274d7cf312776a5a6`:
`lightning/src/ln/chan_utils.rs:1887-1945` (`insert_non_htlc_outputs`) and
`lightning/src/ln/chan_utils.rs:1009-1044` (anchor value and scripts).
-/

namespace LnLean.Proofs.ModelHardening.F04

set_option autoImplicit false

open LnLean
open LnLean.Channel

/-! ## The missing anchor-debit quantity -/

/-- The value absorbed by the funder on one commitment for its anchors:
`2 * 330` when the commitment carries anchors, `0` otherwise. -/
def anchorDebitSat (anchors : Bool) : Nat :=
  if anchors then 2 * anchorOutputSat else 0

theorem waveF_f04_anchorDebitSat_true :
    anchorDebitSat true = 2 * anchorOutputSat := rfl

theorem waveF_f04_anchorDebitSat_false :
    anchorDebitSat false = 0 := rfl

/-- The exact 660-satoshi total of the two anchor outputs. -/
theorem waveF_f04_anchorDebitSat_eq_660 :
    anchorDebitSat true = 660 := rfl

/-- Total amount the funder gives up on a commitment: the fee plus the anchor
debit for the commitment's anchor variant. -/
def funderDebitSat (fee : Nat) (anchors : Bool) : Nat :=
  fee + anchorDebitSat anchors

theorem waveF_f04_funderDebitSat_noAnchors (fee : Nat) :
    funderDebitSat fee false = fee := by
  simp [funderDebitSat, anchorDebitSat]

theorem waveF_f04_funderDebitSat_anchors (fee : Nat) :
    funderDebitSat fee true = fee + 660 := by
  simp [funderDebitSat, anchorDebitSat, anchorOutputSat]

/-! ## Reusable invariants -/

end LnLean.Proofs.ModelHardening.F04

namespace LnLean.Channel

/-- A commitment conserves the funding value when its outputs plus the fee add
up to exactly the funding amount. -/
def Commitment.Conserves (c : Commitment) : Prop :=
  c.totalOutputValue + c.feeSat = c.fundingValueSat

/-- The funder-debit rule for one commitment.  `preFunderSat` is the funder's
off-chain balance before this commitment is built.  The predicate says that
the funder can afford the fee plus anchors, and that the funder's own output
on this commitment is exactly what remains after that debit.  It is stated
relative to a global `funder` direction because a commitment's `holder` may be
either endpoint. -/
def Commitment.FunderDebited (c : Commitment) (funder : Direction)
    (preFunderSat : Nat) : Prop :=
  LnLean.Proofs.ModelHardening.F04.funderDebitSat c.feeSat c.anchorOutputs ≤
      preFunderSat ∧
    (if funder = c.holder then c.toLocalSat else c.toRemoteSat) =
      preFunderSat -
        LnLean.Proofs.ModelHardening.F04.funderDebitSat c.feeSat c.anchorOutputs

/-- The anchor-debit rule for both commitments of a pair, from the same
off-chain balance and funder. -/
def CommitmentPair.AnchorDebitRule (p : CommitmentPair) (b : Balance)
    (funder : Direction) : Prop :=
  let preFunderSat := if funder = Direction.local then b.localSat else b.remoteSat
  p.localCommitment.FunderDebited funder preFunderSat ∧
    p.remoteCommitment.FunderDebited funder preFunderSat

end LnLean.Channel

namespace LnLean.Proofs.ModelHardening.F04

open LnLean
open LnLean.Channel

/-! ## The legacy model overfunds anchored commitments by 660 satoshis -/

/-- **General overfunding gap.**  When both commitments carry anchors, the
existing pair constructor subtracts only the fee.  Each commitment's output
sum plus fee therefore exceeds its funding value by exactly the two anchors.
The hypothesis `fee ≤ funder balance` avoids `Nat` truncation in the
constructor, so the gap is exactly 660 rather than a saturated artefact. -/
theorem waveF_f04_legacy_anchor_gap
    (localParams remoteParams : ChannelParams) (b : Balance)
    (fee number : Nat) (funder : Direction)
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

-- REPAIRED: the false unconditional legacy claim was removed.  It is refuted
-- by `waveF_f04_counterexample_not_conserves` and, in general, by
-- `waveF_f04_legacy_anchor_not_conserves` (via `waveF_f04_legacy_anchor_gap`).
-- The strongest true replacement is `waveF_f04_corrected_conservation` for the
-- anchor-debit constructor `commitmentPairWithAnchorDebit`, under the explicit
-- BOLT 3 affordability hypotheses.

/-- The legacy anchored pair does **not** conserve: both commitments fail
`Commitment.Conserves`. -/
theorem waveF_f04_legacy_anchor_not_conserves
    (localParams remoteParams : ChannelParams) (b : Balance)
    (fee number : Nat) (funder : Direction)
    (hA : localParams.anchorOutputs = true)
    (hB : remoteParams.anchorOutputs = true)
    (hf : fee ≤ (if funder = Direction.local then b.localSat else b.remoteSat)) :
    let p := commitmentPairOfBalances localParams remoteParams b fee number funder
    ¬ p.localCommitment.Conserves ∧ ¬ p.remoteCommitment.Conserves := by
  dsimp only
  have hgap := waveF_f04_legacy_anchor_gap localParams remoteParams b fee number
    funder hA hB hf
  dsimp only at hgap
  rcases hgap with ⟨hL, hR⟩
  have hL' : (commitmentPairOfBalances localParams remoteParams b fee number
      funder).localCommitment.totalOutputValue + fee =
      (commitmentPairOfBalances localParams remoteParams b fee number
        funder).localCommitment.fundingValueSat + 660 := by
    simpa [anchorOutputSat] using hL
  have hR' : (commitmentPairOfBalances localParams remoteParams b fee number
      funder).remoteCommitment.totalOutputValue + fee =
      (commitmentPairOfBalances localParams remoteParams b fee number
        funder).remoteCommitment.fundingValueSat + 660 := by
    simpa [anchorOutputSat] using hR
  constructor
  · intro h
    unfold Commitment.Conserves at h
    have hfee : (commitmentPairOfBalances localParams remoteParams b fee
        number funder).localCommitment.feeSat = fee := rfl
    rw [hfee] at h
    omega
  · intro h
    unfold Commitment.Conserves at h
    have hfee : (commitmentPairOfBalances localParams remoteParams b fee
        number funder).remoteCommitment.feeSat = fee := rfl
    rw [hfee] at h
    omega

/-- The legacy constructor also violates the reusable anchor-debit rule: its
funder output is `preFunderSat - fee`, not `preFunderSat - (fee + 660)`. -/
theorem waveF_f04_legacy_local_anchor_violates_rule
    (localParams remoteParams : ChannelParams) (b : Balance)
    (fee number : Nat) (funder : Direction)
    (hA : localParams.anchorOutputs = true) :
    ¬ (commitmentPairOfBalances localParams remoteParams b fee number
        funder).localCommitment.FunderDebited funder
        (if funder = Direction.local then b.localSat else b.remoteSat) := by
  intro h
  cases funder <;>
    simp [commitmentPairOfBalances, Commitment.FunderDebited, funderDebitSat,
      anchorDebitSat, anchorOutputSat, hA] at h <;>
    omega

/-- Consequently the whole legacy pair violates `AnchorDebitRule`. -/
theorem waveF_f04_legacy_anchor_violates_rule
    (localParams remoteParams : ChannelParams) (b : Balance)
    (fee number : Nat) (funder : Direction)
    (hA : localParams.anchorOutputs = true) :
    ¬ (commitmentPairOfBalances localParams remoteParams b fee number
        funder).AnchorDebitRule b funder := by
  intro h
  exact waveF_f04_legacy_local_anchor_violates_rule localParams remoteParams b
    fee number funder hA h.1

/-! ## The concrete 660-satoshi counterexample -/

/-- Channel parameters for the mechanized counterexample. -/
def waveF_f04_counterexampleParams (anchors : Bool) : ChannelParams :=
  { dustLimitSat := 546
    channelReserveSat := 1000
    toSelfDelay := 144
    maxHtlcValue := Msat.ofSat 100_000
    htlcMinimum := Msat.ofSat 1
    feerate := ⟨1000⟩
    anchorOutputs := anchors }

/-- A 100 000-satoshi channel split 60 000 / 40 000, with the local endpoint
as funder. -/
def waveF_f04_counterexampleBalance : Balance :=
  { localBalance := Msat.ofSat 60_000
    remoteBalance := Msat.ofSat 40_000 }

/-- The legacy anchored commitment overfunds by exactly 660 satoshis: its
output sum plus the 1 000-satoshi fee is 100 660, not 100 000. -/
theorem waveF_f04_counterexample_660 :
    let p := commitmentPairOfBalances
      (waveF_f04_counterexampleParams true) (waveF_f04_counterexampleParams true)
      waveF_f04_counterexampleBalance 1000 0 Direction.local
    p.localCommitment.totalOutputValue + 1000 = 100_000 + 660 := by
  decide

/-- The concrete legacy commitment fails conservation. -/
theorem waveF_f04_counterexample_not_conserves :
    let p := commitmentPairOfBalances
      (waveF_f04_counterexampleParams true) (waveF_f04_counterexampleParams true)
      waveF_f04_counterexampleBalance 1000 0 Direction.local
    ¬ p.localCommitment.Conserves := by
  dsimp only
  unfold Commitment.Conserves
  decide

/-! ## Corrected construction -/

/-- Build the two commitment records with the missing debit rule applied.  On
each commitment the funder's own output is reduced by `fee + anchorDebit`;
the counterparty output is untouched, and the anchor outputs are still
emitted.  When the two endpoints disagree about `anchorOutputs`, each
commitment uses its own flag, just as in `commitmentPairOfBalances`. -/
def commitmentPairWithAnchorDebit (localParams remoteParams : ChannelParams)
    (b : Balance) (fee number : Nat) (funder : Direction) : CommitmentPair :=
  let funding := b.localSat + b.remoteSat
  let localDebit := funderDebitSat fee localParams.anchorOutputs
  let remoteDebit := funderDebitSat fee remoteParams.anchorOutputs
  { localCommitment :=
      { holder := .local
        commitmentNumber := number
        fundingValueSat := funding
        toLocalSat := if funder = .local then b.localSat - localDebit else b.localSat
        toRemoteSat := if funder = .remote then b.remoteSat - localDebit else b.remoteSat
        htlcs := []
        feeSat := fee
        contestDelay := remoteParams.toSelfDelay
        anchorOutputs := localParams.anchorOutputs }
    remoteCommitment :=
      { holder := .remote
        commitmentNumber := number
        fundingValueSat := funding
        toLocalSat := if funder = .remote then b.remoteSat - remoteDebit else b.remoteSat
        toRemoteSat := if funder = .local then b.localSat - remoteDebit else b.localSat
        htlcs := []
        feeSat := fee
        contestDelay := localParams.toSelfDelay
        anchorOutputs := remoteParams.anchorOutputs } }

/-- **Corrected conservation theorem.**  Under the BOLT 3 affordability
condition for the funder (`fee + anchorDebit ≤ funder balance`, separately for
each commitment's anchor variant), the corrected pair conserves the funding
value on both commitments. -/
theorem waveF_f04_corrected_conservation
    (localParams remoteParams : ChannelParams) (b : Balance)
    (fee number : Nat) (funder : Direction)
    (hL : funderDebitSat fee localParams.anchorOutputs ≤
      (if funder = Direction.local then b.localSat else b.remoteSat))
    (hR : funderDebitSat fee remoteParams.anchorOutputs ≤
      (if funder = Direction.local then b.localSat else b.remoteSat)) :
    let p := commitmentPairWithAnchorDebit localParams remoteParams b fee number funder
    p.localCommitment.totalOutputValue + fee = p.localCommitment.fundingValueSat ∧
      p.remoteCommitment.totalOutputValue + fee = p.remoteCommitment.fundingValueSat := by
  cases funder <;>
    cases hA : localParams.anchorOutputs <;>
    cases hB : remoteParams.anchorOutputs <;>
    simp [commitmentPairWithAnchorDebit, Commitment.totalOutputValue,
      Commitment.htlcOutputValue, Commitment.anchorOutputValue, htlcOutputsValue,
      funderDebitSat, anchorDebitSat, anchorOutputSat, hA, hB] at hL hR ⊢ <;>
    omega

/-- The corrected pair satisfies the reusable anchor-debit rule: on both
commitments, the funder's own output is reduced by exactly the fee and the
anchors they carry. -/
theorem waveF_f04_corrected_anchor_debit_rule
    (localParams remoteParams : ChannelParams) (b : Balance)
    (fee number : Nat) (funder : Direction)
    (hL : funderDebitSat fee localParams.anchorOutputs ≤
      (if funder = Direction.local then b.localSat else b.remoteSat))
    (hR : funderDebitSat fee remoteParams.anchorOutputs ≤
      (if funder = Direction.local then b.localSat else b.remoteSat)) :
    (commitmentPairWithAnchorDebit localParams remoteParams b fee number
      funder).AnchorDebitRule b funder := by
  cases funder <;>
    cases hA : localParams.anchorOutputs <;>
    cases hB : remoteParams.anchorOutputs <;>
    simp [commitmentPairWithAnchorDebit, CommitmentPair.AnchorDebitRule,
      Commitment.FunderDebited, funderDebitSat, anchorDebitSat, anchorOutputSat,
      hA, hB] at hL hR ⊢ <;>
    omega

/-- The only difference from the legacy pair is on the funder's own output:
the legacy value exceeds the corrected value by exactly the anchor debit (660
satoshi for an anchored commitment).  This is the local form of the missing
adjustment. -/
theorem waveF_f04_corrected_absorbs_anchor_debit
    (localParams remoteParams : ChannelParams) (b : Balance)
    (fee number : Nat) (funder : Direction)
    (hL : funderDebitSat fee localParams.anchorOutputs ≤
      (if funder = Direction.local then b.localSat else b.remoteSat))
    (hR : funderDebitSat fee remoteParams.anchorOutputs ≤
      (if funder = Direction.local then b.localSat else b.remoteSat)) :
    let legacy := commitmentPairOfBalances localParams remoteParams b fee number funder
    let corrected := commitmentPairWithAnchorDebit localParams remoteParams b fee number funder
    (if funder = Direction.local then
        legacy.localCommitment.toLocalSat =
          corrected.localCommitment.toLocalSat + anchorDebitSat localParams.anchorOutputs
      else
        legacy.localCommitment.toRemoteSat =
          corrected.localCommitment.toRemoteSat + anchorDebitSat localParams.anchorOutputs) ∧
      (if funder = Direction.local then
        legacy.remoteCommitment.toRemoteSat =
          corrected.remoteCommitment.toRemoteSat + anchorDebitSat remoteParams.anchorOutputs
      else
        legacy.remoteCommitment.toLocalSat =
          corrected.remoteCommitment.toLocalSat + anchorDebitSat remoteParams.anchorOutputs) := by
  cases funder <;>
    cases hA : localParams.anchorOutputs <;>
    cases hB : remoteParams.anchorOutputs <;>
    simp [commitmentPairOfBalances, commitmentPairWithAnchorDebit,
      funderDebitSat, anchorDebitSat, anchorOutputSat, hA, hB] at hL hR ⊢ <;>
    omega

/-- Corollary in the exact 660-satoshi form: with anchors on both commitments
the corrected funder output is the legacy output minus 660. -/
theorem waveF_f04_corrected_absorbs_660
    (localParams remoteParams : ChannelParams) (b : Balance)
    (fee number : Nat) (funder : Direction)
    (hA : localParams.anchorOutputs = true)
    (hB : remoteParams.anchorOutputs = true)
    (hL : funderDebitSat fee true ≤
      (if funder = Direction.local then b.localSat else b.remoteSat))
    (hR : funderDebitSat fee true ≤
      (if funder = Direction.local then b.localSat else b.remoteSat)) :
    let legacy := commitmentPairOfBalances localParams remoteParams b fee number funder
    let corrected := commitmentPairWithAnchorDebit localParams remoteParams b fee number funder
    (if funder = Direction.local then
        legacy.localCommitment.toLocalSat = corrected.localCommitment.toLocalSat + 660
      else
        legacy.localCommitment.toRemoteSat = corrected.localCommitment.toRemoteSat + 660) ∧
      (if funder = Direction.local then
        legacy.remoteCommitment.toRemoteSat = corrected.remoteCommitment.toRemoteSat + 660
      else
        legacy.remoteCommitment.toLocalSat = corrected.remoteCommitment.toLocalSat + 660) := by
  have h := waveF_f04_corrected_absorbs_anchor_debit localParams remoteParams b
    fee number funder (by simpa [hA, hB] using hL) (by simpa [hA, hB] using hR)
  simpa [hA, hB, anchorDebitSat, anchorOutputSat] using h

/-- The corrected pair still conserves in the concrete counterexample. -/
theorem waveF_f04_counterexample_corrected_conserves :
    let p := commitmentPairWithAnchorDebit
      (waveF_f04_counterexampleParams true) (waveF_f04_counterexampleParams true)
      waveF_f04_counterexampleBalance 1000 0 Direction.local
    p.localCommitment.Conserves ∧ p.remoteCommitment.Conserves := by
  have h := waveF_f04_corrected_conservation
    (waveF_f04_counterexampleParams true) (waveF_f04_counterexampleParams true)
    waveF_f04_counterexampleBalance 1000 0 Direction.local
    (by decide) (by decide)
  simpa [Commitment.Conserves, commitmentPairWithAnchorDebit] using h

end LnLean.Proofs.ModelHardening.F04
