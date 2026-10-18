import LnLean.Bitcoin.Funding
import LnLean.Bitcoin.Laws
import LnLean.Bitcoin.ScriptTemplates
import LnLean.Bitcoin.Seam
import LnLean.Channel.Commitment
import LnLean.Channel.HTLC
import LnLean.Security.Model
import LnLean.Proofs.Bitcoin.WeightProps

/-!
# LnLean.Proofs.WaveD.D04

English claim (catalog `LN-L1-006`).  The commitment base weight is the
BOLT 3 constant 724 before HTLC outputs.

The model exposes the constant twice:

* `LnLean.Bitcoin.commitmentBaseWeight` is the seam's bare `Weight`, `⟨724⟩`
  (`LnLean/Bitcoin/Seam.lean:166-169`);
* `LnLean.Channel.commitmentBaseWeight anchors` selects `724` for the
  non-anchor commitment and `1124` when `option_anchors` applies
  (`LnLean/Channel/Commitment.lean:52-55`).

This module proves that the two agree on the non-anchor variant, that the
value is exactly 724, that it is precisely the expected weight of a
commitment with zero untrimmed HTLC outputs, and that every HTLC output adds
`172` on top of it.  It also checks the BOLT 3 Appendix A byte construction
`4 * 125 + 224 = 724`.

Fidelity note.  BOLT 3 gives two base constants: `724` without
`option_anchors` and `1124` with it.  The catalog target is the bare,
non-anchor seam constant, so the 724 claim is proved for
`commitmentBaseWeight false`; the anchor variant is proved separately to be
1124.  There is no claim here that 724 is the anchor base.

BOLT sections.
* BOLT 3 §4 "Fees" (`refs/bolts/03-transactions.md:491-498`):
  `724 + 172 * num-untrimmed-htlc-outputs` without anchors and
  `1124 + 172 * ...` with anchors.
* BOLT 3 Appendix A "Expected Weight of the Commitment Transaction"
  (`refs/bolts/03-transactions.md:973-1086`): 125 non-witness bytes and 224
  witness weight before HTLC outputs, i.e. `4 * 125 + 224 = 724`; each HTLC
  output adds 43 non-witness bytes, i.e. `4 * 43 = 172`.

LDK anchor: `lightning/src/ln/chan_utils.rs:279-284`
(`COMMITMENT_TX_BASE_WEIGHT = 724`, `COMMITMENT_TX_BASE_ANCHOR_WEIGHT = 1124`).

What is NOT modelled.
* Actual serialized transaction weight.  `Bitcoin.Data.Tx` has no weight
  function; the Appendix A check is arithmetic on BOLT 3's own byte counts,
  not a bound on a real serialization (see
  `LnLean.Proofs.Bitcoin.WeightProps`).
* Dust trimming.  `numHtlcs` counts *untrimmed* outputs; which HTLCs are
  trimmed is decided in `LnLean.Channel.Fee`, not here.
* Anchor's shared-anchor / zero-fee-commitment variants.
-/

namespace LnLean.Proofs.WaveD.D04

set_option autoImplicit false

-- OBLIGATION: LN-WD-D04

/-! ## The seam constant is 724 -/

/-- The seam's commitment base weight has value 724 (BOLT 3 §4; LDK
`chan_utils.rs:281`). -/
theorem waveD_d04_seam_base_weight_value :
    LnLean.Bitcoin.commitmentBaseWeight.val = 724 := rfl

/-- The seam constant *is* `⟨724⟩`. -/
theorem waveD_d04_seam_base_weight_eq :
    LnLean.Bitcoin.commitmentBaseWeight = ⟨724⟩ := rfl

/-- The channel layer's non-anchor base weight is the same 724. -/
theorem waveD_d04_channel_base_weight_non_anchor :
    LnLean.Channel.commitmentBaseWeight false = 724 :=
  LnLean.Channel.commitmentBaseWeight_noAnchors

/-- The seam constant and the channel layer's non-anchor constant agree as
`Weight` values. -/
theorem waveD_d04_seam_eq_channel_base_weight :
    LnLean.Bitcoin.commitmentBaseWeight =
      ⟨LnLean.Channel.commitmentBaseWeight false⟩ := rfl

/-- The seam constant agrees with the wave-A restatement in
`LnLean.Proofs.Bitcoin.WeightProps`. -/
theorem waveD_d04_seam_eq_weightProps_base_weight :
    LnLean.Bitcoin.commitmentBaseWeight.val =
      LnLean.Proofs.Bitcoin.baseWeight false :=
  (LnLean.Proofs.Bitcoin.baseWeight_noAnchors).symm

/-! ## 724 is the weight before HTLC outputs -/

/-- A commitment with zero untrimmed HTLC outputs has exactly the seam's
base weight: no HTLC output has been added yet. -/
theorem waveD_d04_weight_zero_htlcs :
    LnLean.Channel.commitmentWeight false 0 =
      LnLean.Bitcoin.commitmentBaseWeight := by
  simp [LnLean.Channel.commitmentWeight,
    LnLean.Channel.commitmentBaseWeight,
    LnLean.Bitcoin.commitmentBaseWeight]

/-- Closed BOLT 3 decomposition: the non-anchor commitment weight is the
base constant 724 plus 172 for each untrimmed HTLC output. -/
theorem waveD_d04_weight_decomposition (n : Nat) :
    (LnLean.Channel.commitmentWeight false n).val =
      LnLean.Bitcoin.commitmentBaseWeight.val + 172 * n := rfl

/-- Adding one untrimmed HTLC output adds exactly 172 weight units on top of
the base weight. -/
theorem waveD_d04_weight_succ (n : Nat) :
    (LnLean.Channel.commitmentWeight false (n + 1)).val =
      (LnLean.Channel.commitmentWeight false n).val + 172 := by
  simpa [LnLean.Channel.commitmentHtlcWeight] using
    LnLean.Channel.commitmentWeight_succ false n

/-- HTLC outputs only add weight: the base constant is a lower bound on every
non-anchor commitment weight. -/
theorem waveD_d04_base_le_weight (n : Nat) :
    LnLean.Bitcoin.commitmentBaseWeight.val ≤
      (LnLean.Channel.commitmentWeight false n).val := by
  rw [waveD_d04_weight_decomposition, waveD_d04_seam_base_weight_value]
  omega

/-- The base constant plus all HTLC-output contributions is the full weight;
i.e. 724 is exactly the HTLC-independent part. -/
theorem waveD_d04_weight_sub_htlc_part (n : Nat) :
    (LnLean.Channel.commitmentWeight false n).val - 172 * n =
      LnLean.Bitcoin.commitmentBaseWeight.val := by
  rw [waveD_d04_weight_decomposition, Nat.add_sub_cancel]

/-! ## Concrete commitment records -/

/-- Any non-anchor commitment record with `k` untrimmed HTLC outputs has
weight `724 + 172 * k`. -/
theorem waveD_d04_commitment_weight_decomposition
    (c : LnLean.Channel.Commitment) (hAnchor : c.anchorOutputs = false) :
    (LnLean.Channel.Commitment.weight c).val =
      LnLean.Bitcoin.commitmentBaseWeight.val + 172 * c.htlcs.length := by
  simp [LnLean.Channel.Commitment.weight, hAnchor,
    LnLean.Channel.commitmentWeight,
    LnLean.Channel.commitmentBaseWeight,
    LnLean.Channel.commitmentHtlcWeight,
    LnLean.Bitcoin.commitmentBaseWeight]

/-- A non-anchor commitment with no HTLC outputs has weight exactly 724,
whatever its balances, fee, commitment number, or CSV delay. -/
theorem waveD_d04_commitment_weight_no_htlcs
    (c : LnLean.Channel.Commitment) (hAnchor : c.anchorOutputs = false)
    (hHtlc : c.htlcs = []) :
    (LnLean.Channel.Commitment.weight c).val = 724 := by
  rw [waveD_d04_commitment_weight_decomposition c hAnchor]
  simp [LnLean.Bitcoin.commitmentBaseWeight, hHtlc]

/-! ## The anchor variant is 1124, not 724 -/

/-- BOLT 3's anchor variant uses base weight 1124. -/
theorem waveD_d04_anchor_base_weight :
    LnLean.Channel.commitmentBaseWeight true = 1124 :=
  LnLean.Channel.commitmentBaseWeight_anchors

/-- The seam's 724 is the non-anchor constant and is strictly below the
anchor base weight. -/
theorem waveD_d04_seam_base_lt_anchor_base :
    LnLean.Bitcoin.commitmentBaseWeight.val <
      LnLean.Channel.commitmentBaseWeight true := by
  rw [waveD_d04_seam_base_weight_value, waveD_d04_anchor_base_weight]
  decide

/-! ## BOLT 3 Appendix A byte check -/

/-- Appendix A reconstructs the non-anchor base weight as 125 non-witness
bytes (`4 * 125 = 500`) plus 224 witness weight units: `500 + 224 = 724`. -/
theorem waveD_d04_appendixA_bytes :
    LnLean.Bitcoin.commitmentBaseWeight.val = 4 * 125 + 224 := by
  decide

/-- The same reconstruction through the committed byte model in
`LnLean.Proofs.Bitcoin.WeightProps`: the seam constant is the zero-HTLC
Appendix A weight. -/
theorem waveD_d04_appendixA_weightFromBytes :
    LnLean.Bitcoin.commitmentBaseWeight.val =
      LnLean.Proofs.Bitcoin.weightFromBytes false 0 := by
  have h := LnLean.Proofs.Bitcoin.weightFromBytes_eq_commitmentWeight false 0
  simpa [LnLean.Proofs.Bitcoin.commitmentWeight,
    LnLean.Proofs.Bitcoin.baseWeight,
    LnLean.Proofs.Bitcoin.htlcWeight,
    LnLean.Bitcoin.commitmentBaseWeight] using h

end LnLean.Proofs.WaveD.D04
