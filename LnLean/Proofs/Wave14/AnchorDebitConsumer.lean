import LnLean.Proofs.ModelHardening.F04
import LnLean.Proofs.Conservation

/-!
# Production-facing anchor-debit commitment pair

This module promotes the corrected anchor-debit construction that was
mechanized in `LnLean.Proofs.ModelHardening.F04` behind the additive,
production-facing name `commitmentPairCanonical`.  The legacy constructor
`LnLean.Channel.commitmentPairOfBalances` is **not** changed: it still
subtracts only the commitment fee, and the checked counterexamples
`waveF_f04_counterexample_660`, `waveF_f04_counterexample_not_conserves` and
`commitmentPair_anchorCounterexample` remain valid statements about it.

## What is proved

On each commitment of the pair, the funder pays the commitment fee plus the
two 330-satoshi anchor outputs when that commitment carries anchors (BOLT 3
§2, `03-transactions.md:319-324`).  Consequently the funder's own output is
reduced by `fee + 660`; the counterparty output and the two anchor outputs are
unchanged.  `commitmentPairCanonical_conserved` states the resulting value
equation

`totalOutputValue + fee = fundingValueSat`

for both commitments, under the explicit affordability hypotheses
`fee + 660 ≤ funder balance` for the two endpoint variants.  When both endpoint
anchor flags are false the canonical pair is definitionally the legacy pair
(`commitmentPairCanonical_eq_legacy_of_noAnchors`).

## Boundaries (do not overclaim)

* This is **value conservation**, not a weight, script, signature, or
  serialization theorem.  `Commitment` is value arithmetic only; scripts and
  witness bytes live in a different layer.
* The `1124` WU figure is the fee basis for the **zero-fee anchor form**; it is
  not the literal serialized weight of an anchored commitment.  This module
  proves no weight statement and therefore does not depend on that figure.
* The pair constructor emits no HTLCs, does not recompute the commitment fee,
  does not perform dust trimming, and does not model single-anchor,
  zero-fee/`shared_anchor`, splice, or dual-funding variants.
* `fee + 660 ≤ funder balance` is a real BOLT 3 affordability precondition.
  Without it `Nat` subtraction truncates and the conservation equation is not
  claimed.
* The two commitments can disagree about `anchorOutputs`; the hypotheses are
  therefore stated separately for the local and remote commitment variants.
* Downstreams must treat `commitmentPairCanonical` as the anchored-value
  constructor and keep using `commitmentPairOfBalances` only where the
  no-anchor hypothesis is explicit.

BOLT 3 anchors: `refs/bolts/03-transactions.md:148-198`, `:319-324`.
rust-lightning pin `fe4900930c6bd5786ec4203274d7cf312776a5a6`:
`lightning/src/ln/chan_utils.rs:1009-1044` (anchor value/scripts) and
`:1887-1945` (`insert_non_htlc_outputs`).
-/

namespace LnLean.Proofs.Wave14.AnchorDebitConsumer

set_option autoImplicit false

open LnLean
open LnLean.Channel
open LnLean.Proofs.ModelHardening.F04

/-- Production-facing additive alias for the corrected anchor-debit pair
constructor.  The funder pays `fee + 660` on a commitment that carries anchors,
and `fee` on a commitment that does not.  The legacy
`commitmentPairOfBalances` is deliberately left unchanged. -/
def commitmentPairCanonical (localParams remoteParams : ChannelParams)
    (b : Balance) (fee number : Nat) (funder : Direction) : CommitmentPair :=
  commitmentPairWithAnchorDebit localParams remoteParams b fee number funder

/-- **Headline conservation theorem (general form).**  If the funder can afford
the fee plus the anchor debit on each commitment's own anchor variant, the
canonical pair conserves the funding value on both commitments. -/
theorem commitmentPairCanonical_conserved_of_funderDebit
    (localParams remoteParams : ChannelParams) (b : Balance)
    (fee number : Nat) (funder : Direction)
    (hL : funderDebitSat fee localParams.anchorOutputs ≤
      (if funder = Direction.local then b.localSat else b.remoteSat))
    (hR : funderDebitSat fee remoteParams.anchorOutputs ≤
      (if funder = Direction.local then b.localSat else b.remoteSat)) :
    let p := commitmentPairCanonical localParams remoteParams b fee number funder
    p.localCommitment.totalOutputValue + fee = p.localCommitment.fundingValueSat ∧
      p.remoteCommitment.totalOutputValue + fee = p.remoteCommitment.fundingValueSat := by
  dsimp only
  exact waveF_f04_corrected_conservation localParams remoteParams b fee number
    funder hL hR

/-- **Headline conservation theorem.**  Explicit `fee + 660 ≤ funder balance`
hypotheses for both endpoint commitments.  This is the BOLT 3 affordability
condition with the anchor debit written out; it is stronger than strictly
necessary on an endpoint whose anchor flag is false, but it keeps the two
commitment variants uniform at the consumer boundary. -/
theorem commitmentPairCanonical_conserved
    (localParams remoteParams : ChannelParams) (b : Balance)
    (fee number : Nat) (funder : Direction)
    (hL : fee + 660 ≤
      (if funder = Direction.local then b.localSat else b.remoteSat))
    (hR : fee + 660 ≤
      (if funder = Direction.local then b.localSat else b.remoteSat)) :
    let p := commitmentPairCanonical localParams remoteParams b fee number funder
    p.localCommitment.totalOutputValue + fee = p.localCommitment.fundingValueSat ∧
      p.remoteCommitment.totalOutputValue + fee = p.remoteCommitment.fundingValueSat := by
  have hL' : funderDebitSat fee localParams.anchorOutputs ≤
      (if funder = Direction.local then b.localSat else b.remoteSat) := by
    cases funder <;> cases h : localParams.anchorOutputs <;>
      simp [funderDebitSat, anchorDebitSat, anchorOutputSat] at hL ⊢ <;>
      omega
  have hR' : funderDebitSat fee remoteParams.anchorOutputs ≤
      (if funder = Direction.local then b.localSat else b.remoteSat) := by
    cases funder <;> cases h : remoteParams.anchorOutputs <;>
      simp [funderDebitSat, anchorDebitSat, anchorOutputSat] at hR ⊢ <;>
      omega
  exact commitmentPairCanonical_conserved_of_funderDebit localParams remoteParams b
    fee number funder hL' hR'

/-- **Behaviour-preserving no-anchor alias.**  With both endpoint anchor flags
false the canonical constructor is exactly the legacy constructor.  This is the
only case in which the legacy pair is value-conserving. -/
theorem commitmentPairCanonical_eq_legacy_of_noAnchors
    (localParams remoteParams : ChannelParams) (b : Balance)
    (fee number : Nat) (funder : Direction)
    (hL : localParams.anchorOutputs = false)
    (hR : remoteParams.anchorOutputs = false) :
    commitmentPairCanonical localParams remoteParams b fee number funder =
      commitmentPairOfBalances localParams remoteParams b fee number funder := by
  simp only [commitmentPairCanonical, commitmentPairWithAnchorDebit,
    commitmentPairOfBalances]
  rw [hL, hR]
  cases funder <;> rfl

/-- **The legacy constructor overfunds the concrete anchored pair by 660 sat.**
This is the production-facing restatement of the retained witness
`waveF_f04_counterexample_660` (60 000 / 40 000 split, fee 1000, both endpoints
anchored).  It is intentionally a theorem about the unchanged legacy
constructor, not about `commitmentPairCanonical`. -/
theorem legacy_anchor_overfunds_660 :
    let p := commitmentPairOfBalances
      (waveF_f04_counterexampleParams true)
      (waveF_f04_counterexampleParams true)
      waveF_f04_counterexampleBalance 1000 0 Direction.local
    p.localCommitment.totalOutputValue + 1000 = 100_000 + 660 := by
  simpa using waveF_f04_counterexample_660

/-- Concrete **anchored** non-vacuity witness.  On the retained 60 000 / 40 000
counterexample the canonical pair carries anchors on both commitments, the
funder's output is `60 000 - (1000 + 660) = 58 340` on each, and both
commitments conserve the 100 000-sat funding value. -/
theorem commitmentPairCanonical_anchored_witness :
    let p := commitmentPairCanonical
      (waveF_f04_counterexampleParams true)
      (waveF_f04_counterexampleParams true)
      waveF_f04_counterexampleBalance 1000 0 Direction.local
    p.localCommitment.anchorOutputs = true ∧
      p.remoteCommitment.anchorOutputs = true ∧
      p.localCommitment.toLocalSat = 58_340 ∧
      p.remoteCommitment.toRemoteSat = 58_340 ∧
      p.localCommitment.totalOutputValue + 1000 = 100_000 ∧
      p.remoteCommitment.totalOutputValue + 1000 = 100_000 := by
  decide

/-- The anchored canonical pair differs from the anchored legacy pair by exactly
the 660-sat anchor debit on the funder's outputs.  This makes the debit, rather
than only the conservation sum, concrete. -/
theorem commitmentPairCanonical_legacy_gap_660 :
    let canonical := commitmentPairCanonical
      (waveF_f04_counterexampleParams true)
      (waveF_f04_counterexampleParams true)
      waveF_f04_counterexampleBalance 1000 0 Direction.local
    let legacy := commitmentPairOfBalances
      (waveF_f04_counterexampleParams true)
      (waveF_f04_counterexampleParams true)
      waveF_f04_counterexampleBalance 1000 0 Direction.local
    legacy.localCommitment.toLocalSat = canonical.localCommitment.toLocalSat + 660 ∧
      legacy.remoteCommitment.toRemoteSat =
        canonical.remoteCommitment.toRemoteSat + 660 := by
  decide

/-- Concrete **non-anchored** witness.  With both endpoint flags false the
canonical pair equals the legacy pair, both commitments carry no anchors, and
both conserve the funding value.  This is the positive half required by the
R32 §5.2 non-vacuity rule: the no-anchor alias is not the empty case of an
anchored-only theorem. -/
theorem commitmentPairCanonical_noAnchor_witness :
    let p := commitmentPairCanonical
      (waveF_f04_counterexampleParams false)
      (waveF_f04_counterexampleParams false)
      waveF_f04_counterexampleBalance 1000 0 Direction.local
    p.localCommitment.anchorOutputs = false ∧
      p.remoteCommitment.anchorOutputs = false ∧
      p = commitmentPairOfBalances
        (waveF_f04_counterexampleParams false)
        (waveF_f04_counterexampleParams false)
        waveF_f04_counterexampleBalance 1000 0 Direction.local ∧
      p.localCommitment.totalOutputValue + 1000 = 100_000 ∧
      p.remoteCommitment.totalOutputValue + 1000 = 100_000 := by
  dsimp only
  refine ⟨rfl, rfl, ?_, by decide, by decide⟩
  exact commitmentPairCanonical_eq_legacy_of_noAnchors
    (waveF_f04_counterexampleParams false)
    (waveF_f04_counterexampleParams false)
    waveF_f04_counterexampleBalance 1000 0 Direction.local rfl rfl

/-! ## Axiom audit -/

#print axioms commitmentPairCanonical_conserved_of_funderDebit
#print axioms commitmentPairCanonical_conserved
#print axioms commitmentPairCanonical_eq_legacy_of_noAnchors
#print axioms legacy_anchor_overfunds_660
#print axioms commitmentPairCanonical_anchored_witness
#print axioms commitmentPairCanonical_legacy_gap_660
#print axioms commitmentPairCanonical_noAnchor_witness

end LnLean.Proofs.Wave14.AnchorDebitConsumer
