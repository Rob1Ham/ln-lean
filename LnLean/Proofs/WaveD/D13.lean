import LnLean.Channel.Commitment
import LnLean.Channel.Fee
import LnLean.Channel.HTLC
import LnLean.Channel.HTLCLaws
import LnLean.Channel.Laws
import LnLean.Channel.Penalty
import LnLean.Channel.Revocation
import LnLean.Channel.State
import LnLean.Channel.Types

/-!
# LnLean.Proofs.WaveD.D13 — fee-insufficient commitments are rejected before signing

English claim (catalog `LN-CH-005`).  A commitment whose paid fee does not
cover the base fee required by the negotiated `feerate_per_kw` for its
expected weight is rejected before any signature is produced.

The model in `LnLean.Channel.Fee` provides `feeSufficient` (and
`feeForWeight`, the floored BOLT 3 base fee), but it does **not** provide the
catalog's target declaration `LnLean.Channel.Fee.feeInsufficient`.  This
module supplies that exact declaration as the negation of `feeSufficient`
and proves the rejection result about it.  No model file is modified.

The second half of the module mechanizes the signing gate:

* `commitmentFeePaid` converts the commitment record's whole-satoshi
  `feeSat` field into millisatoshis exactly (`1 sat = 1000 msat`).
* `commitmentFeeInsufficient` is `feeInsufficient` at the commitment's own
  weight and paid fee.
* `commitmentSigningGate` is the pre-signature check: it either emits the
  commitment for signing or returns an `error` with
  `ErrorCode.feeInsufficient`.
* `FeeCheckedStep` is the channel transition relation refined by that gate;
  its only `commitment_signed` constructor carries a sufficiency proof.  An
  insufficient commitment therefore has no checked signing derivation.

BOLT sections.
* BOLT 3 §Fees (`refs/bolts/03-transactions.md:464-530`): expected weights
  `724 + 172 * num-untrimmed-htlcs` (and `1124 + ...` with anchors); the base
  fee is `feerate_per_kw * weight / 1000`, rounded down.
* BOLT 5 §Commitment Transaction (`refs/bolts/05-onchain.md:546-580`): a
  commitment must pay a fee sufficient for relay; zero-fee commitments are
  excluded from this model (see `LnLean.Channel.Fee` "What is NOT modelled").
* BOLT 2 §Updating Fees (`refs/bolts/02-peer-protocol.md:3250-3310`):
  `update_fee` replaces the feerate and the receiver checks affordability.

rust-lightning anchors at `fe4900930c6bd5786ec4203274d7cf312776a5a6`.
* `lightning/src/ln/chan_utils.rs:275-298` (`COMMITMENT_TX_WEIGHT_PER_HTLC`,
  base weights, `commit_tx_fee_sat`).
* `lightning/src/ln/channel.rs:3721` (commitment construction context that
  carries `feerate_per_kw`; the catalog's LDK anchor).

What is NOT modelled.
* `zero_fee_commitments`, anchor child-pays-for-parent, RBF, and mempool
  policy.  The gate is the BOLT 3 base-fee check, not a relay simulation.
* The fee is compared on the *base* fee for the expected weight; BOLT 3
  allows the actual on-chain fee to be higher after trimming.
* The `Channel` record has no per-commitment fee/weight fields and `Step`
  has no fee precondition.  `FeeCheckedStep` therefore refines `Step` with
  the commitment record supplied as a separate index; this gap is recorded
  in `agents/reports/D13.md` and is not hidden by a strengthening of `Step`.
-/

namespace LnLean.Channel

namespace Fee

/-- Catalog target `LN-CH-005`.  The fee paid is *insufficient* for the
feerate and weight.  This is the exact negation of the model's
`feeSufficient`; it is supplied here because `LnLean.Channel.Fee` defines
only the positive predicate. -/
def feeInsufficient (r : FeeRate) (w : Weight) (paid : Msat) : Prop :=
  ¬ feeSufficient r w paid

end Fee

end LnLean.Channel

namespace LnLean.Proofs.WaveD.D13

set_option autoImplicit false

open LnLean
open LnLean.Channel

/-! ## The catalog predicate, arithmetically -/

/-- `feeInsufficient` is failure of the required-fee comparison. -/
theorem waveD_d13_feeInsufficient_iff_not_sufficient
    (r : FeeRate) (w : Weight) (paid : Msat) :
    Fee.feeInsufficient r w paid ↔ ¬ feeSufficient r w paid :=
  Iff.rfl

/-- Numeric form: the required floored fee strictly exceeds the paid fee. -/
theorem waveD_d13_feeInsufficient_iff_lt
    (r : FeeRate) (w : Weight) (paid : Msat) :
    Fee.feeInsufficient r w paid ↔ paid.val < (feeForWeight r w).val := by
  unfold Fee.feeInsufficient feeSufficient
  exact Nat.not_le

/-- A sufficient fee is not insufficient, and conversely. -/
theorem waveD_d13_not_insufficient_iff
    (r : FeeRate) (w : Weight) (paid : Msat) :
    ¬ Fee.feeInsufficient r w paid ↔ feeSufficient r w paid := by
  unfold Fee.feeInsufficient
  exact Classical.not_not

/-! ## Commitment-level paid fee -/

/-- The fee recorded on a commitment, in millisatoshis.  `Commitment.feeSat`
is a whole number of satoshis, so the conversion is exact. -/
def waveD_d13_commitmentFeePaid (c : Commitment) : Msat :=
  ⟨c.feeSat * 1000⟩

theorem waveD_d13_commitmentFeePaid_val (c : Commitment) :
    (waveD_d13_commitmentFeePaid c).val = c.feeSat * 1000 := rfl

/-- The commitment pays at least the base fee required by `r` for its own
expected weight. -/
def waveD_d13_commitmentFeeSufficient
    (r : FeeRate) (c : Commitment) : Prop :=
  feeSufficient r c.weight (waveD_d13_commitmentFeePaid c)

/-- The commitment under-pays the base fee required by `r` for its own
expected weight. -/
def waveD_d13_commitmentFeeInsufficient
    (r : FeeRate) (c : Commitment) : Prop :=
  Fee.feeInsufficient r c.weight (waveD_d13_commitmentFeePaid c)

/-- Decidability of the commitment-level sufficiency predicate, needed by the
pre-signature gate and by the concrete `decide` examples. -/
instance waveD_d13_decidable_commitmentFeeSufficient
    (r : FeeRate) (c : Commitment) :
    Decidable (waveD_d13_commitmentFeeSufficient r c) :=
  inferInstanceAs (Decidable ((feeForWeight r c.weight).val ≤
    (waveD_d13_commitmentFeePaid c).val))

/-- Decidability of the commitment-level insufficiency predicate. -/
instance waveD_d13_decidable_commitmentFeeInsufficient
    (r : FeeRate) (c : Commitment) :
    Decidable (waveD_d13_commitmentFeeInsufficient r c) :=
  inferInstanceAs (Decidable (¬ (feeForWeight r c.weight).val ≤
    (waveD_d13_commitmentFeePaid c).val))

/-- Insufficiency is exactly the negation of sufficiency at the commitment
level. -/
theorem waveD_d13_commitmentFeeInsufficient_iff_not_sufficient
    (r : FeeRate) (c : Commitment) :
    waveD_d13_commitmentFeeInsufficient r c ↔
      ¬ waveD_d13_commitmentFeeSufficient r c := by
  unfold waveD_d13_commitmentFeeInsufficient
    waveD_d13_commitmentFeeSufficient Fee.feeInsufficient
  exact Iff.rfl

/-- The commitment-level predicate is definitionally the model predicate at
`c.weight` and the exact msat value of `c.feeSat`. -/
theorem waveD_d13_commitmentFeeSufficient_iff_model
    (r : FeeRate) (c : Commitment) :
    waveD_d13_commitmentFeeSufficient r c ↔
      feeSufficient r c.weight ⟨c.feeSat * 1000⟩ :=
  Iff.rfl

/-- Numeric characterization of commitment-level insufficiency. -/
theorem waveD_d13_commitmentFeeInsufficient_iff_lt
    (r : FeeRate) (c : Commitment) :
    waveD_d13_commitmentFeeInsufficient r c ↔
      c.feeSat * 1000 < (feeForWeight r c.weight).val := by
  unfold waveD_d13_commitmentFeeInsufficient waveD_d13_commitmentFeePaid
  rw [waveD_d13_feeInsufficient_iff_lt]

/-- An insufficient commitment leaves a strictly positive msat shortfall. -/
theorem waveD_d13_insufficient_has_positive_deficit
    {r : FeeRate} {c : Commitment}
    (h : waveD_d13_commitmentFeeInsufficient r c) :
    ∃ d : Nat, 0 < d ∧
      (feeForWeight r c.weight).val = c.feeSat * 1000 + d := by
  have hlt := (waveD_d13_commitmentFeeInsufficient_iff_lt r c).mp h
  refine ⟨(feeForWeight r c.weight).val - c.feeSat * 1000, ?_, ?_⟩
  · omega
  · omega

/-! ## The pre-signature gate -/

/-- The protocol error returned when the gate refuses to sign. -/
def waveD_d13_feeInsufficientError : ProtocolError :=
  { code := ErrorCode.feeInsufficient }

/-- Outcome of the pre-signature fee check: the commitment is either
released for signing, or rejected with an explicit protocol error. -/
inductive waveD_d13_SignVerdict where
  | signed (commitment : Commitment)
  | rejected (error : ProtocolError)
  deriving Repr

namespace waveD_d13_SignVerdict

/-- Does this verdict release a transaction for signing? -/
def emitsSignature : waveD_d13_SignVerdict → Bool
  | .signed _ => true
  | .rejected _ => false

/-- The commitment released for signing, if any. -/
def commitment? : waveD_d13_SignVerdict → Option Commitment
  | .signed c => some c
  | .rejected _ => none

end waveD_d13_SignVerdict

/-- The BOLT 3 base-fee gate, evaluated before any signature is produced.
It signs only when the commitment's paid fee covers
`feeForWeight r c.weight`; otherwise it returns `feeInsufficient`. -/
def waveD_d13_commitmentSigningGate
    (r : FeeRate) (c : Commitment) : waveD_d13_SignVerdict :=
  if waveD_d13_commitmentFeeSufficient r c then
    .signed c
  else
    .rejected waveD_d13_feeInsufficientError

/-- The gate signs exactly the fee-sufficient commitments. -/
theorem waveD_d13_gate_signs_iff
    (r : FeeRate) (c : Commitment) :
    waveD_d13_commitmentSigningGate r c = .signed c ↔
      waveD_d13_commitmentFeeSufficient r c := by
  constructor
  · intro h
    unfold waveD_d13_commitmentSigningGate at h
    split at h
    · assumption
    · simp at h
  · intro hsuff
    unfold waveD_d13_commitmentSigningGate
    simp [hsuff]

/-- The gate rejects exactly the fee-insufficient commitments. -/
theorem waveD_d13_gate_rejects_iff
    (r : FeeRate) (c : Commitment) :
    waveD_d13_commitmentSigningGate r c =
        .rejected waveD_d13_feeInsufficientError ↔
      waveD_d13_commitmentFeeInsufficient r c := by
  constructor
  · intro h
    have hn : ¬ waveD_d13_commitmentFeeSufficient r c := by
      intro hsuff
      have hsigned : waveD_d13_commitmentSigningGate r c = .signed c :=
        (waveD_d13_gate_signs_iff r c).mpr hsuff
      rw [hsigned] at h
      simp at h
    exact (waveD_d13_commitmentFeeInsufficient_iff_not_sufficient r c).mpr hn
  · intro hins
    have hn : ¬ waveD_d13_commitmentFeeSufficient r c :=
      (waveD_d13_commitmentFeeInsufficient_iff_not_sufficient r c).mp hins
    unfold waveD_d13_commitmentSigningGate
    simp [hn]

/-- An insufficient commitment is rejected, with the BOLT 1
`fee_insufficient` error code. -/
theorem waveD_d13_gate_rejects_of_insufficient
    {r : FeeRate} {c : Commitment}
    (h : waveD_d13_commitmentFeeInsufficient r c) :
    waveD_d13_commitmentSigningGate r c =
      .rejected waveD_d13_feeInsufficientError :=
  (waveD_d13_gate_rejects_iff r c).mpr h

/-- An insufficient commitment emits no signature bit. -/
theorem waveD_d13_gate_no_signature_of_insufficient
    {r : FeeRate} {c : Commitment}
    (h : waveD_d13_commitmentFeeInsufficient r c) :
    (waveD_d13_commitmentSigningGate r c).emitsSignature = false := by
  have hn : ¬ waveD_d13_commitmentFeeSufficient r c :=
    (waveD_d13_commitmentFeeInsufficient_iff_not_sufficient r c).mp h
  unfold waveD_d13_commitmentSigningGate
  simp [hn, waveD_d13_SignVerdict.emitsSignature]

/-- A sufficient commitment emits the signature bit. -/
theorem waveD_d13_gate_signature_of_sufficient
    {r : FeeRate} {c : Commitment}
    (h : waveD_d13_commitmentFeeSufficient r c) :
    (waveD_d13_commitmentSigningGate r c).emitsSignature = true := by
  unfold waveD_d13_commitmentSigningGate
  simp [h, waveD_d13_SignVerdict.emitsSignature]

/-- An insufficient commitment yields no commitment to sign. -/
theorem waveD_d13_gate_commitment?_eq_none_of_insufficient
    {r : FeeRate} {c : Commitment}
    (h : waveD_d13_commitmentFeeInsufficient r c) :
    (waveD_d13_commitmentSigningGate r c).commitment? = none := by
  have hn : ¬ waveD_d13_commitmentFeeSufficient r c :=
    (waveD_d13_commitmentFeeInsufficient_iff_not_sufficient r c).mp h
  unfold waveD_d13_commitmentSigningGate
  simp [hn, waveD_d13_SignVerdict.commitment?]

/-- Any commitment the gate releases is the original commitment and its fee
is sufficient. -/
theorem waveD_d13_gate_signed_imp
    (r : FeeRate) (c : Commitment) {c' : Commitment}
    (h : waveD_d13_commitmentSigningGate r c = .signed c') :
    c' = c ∧ waveD_d13_commitmentFeeSufficient r c := by
  unfold waveD_d13_commitmentSigningGate at h
  split at h
  · rename_i hsuff
    injection h with hc
    exact ⟨hc.symm, hsuff⟩
  · simp at h

/-- No insufficient commitment can be released for signing. -/
theorem waveD_d13_no_signed_verdict_of_insufficient
    {r : FeeRate} {c : Commitment}
    (h : waveD_d13_commitmentFeeInsufficient r c) :
    ¬ ∃ c' : Commitment, waveD_d13_commitmentSigningGate r c = .signed c' := by
  rintro ⟨c', hc'⟩
  exact h (waveD_d13_gate_signed_imp r c hc').2

/-- End-to-end soundness: if a signature bit is emitted, the commitment's
paid fee covers the base fee required by its weight. -/
theorem waveD_d13_emitted_signature_sound
    {r : FeeRate} {c : Commitment}
    (h : (waveD_d13_commitmentSigningGate r c).emitsSignature = true) :
    waveD_d13_commitmentFeeSufficient r c := by
  unfold waveD_d13_commitmentSigningGate at h
  split at h
  · assumption
  · simp [waveD_d13_SignVerdict.emitsSignature] at h

/-! ## The rejection is the catalog statement -/

/-- Direct form of `LN-CH-005`: an insufficient fee at the commitment's own
weight is rejected before signing. -/
theorem waveD_d13_rejected_before_signing
    {r : FeeRate} {c : Commitment}
    (h : Fee.feeInsufficient r c.weight (waveD_d13_commitmentFeePaid c)) :
    waveD_d13_commitmentSigningGate r c =
      .rejected waveD_d13_feeInsufficientError :=
  waveD_d13_gate_rejects_of_insufficient h

/-! ## Monotonicity in the feerate and the weight -/

/-- Raising the feerate cannot turn an insufficient commitment into a
sufficient one. -/
theorem waveD_d13_insufficient_mono_rate
    {r r' : FeeRate} {c : Commitment}
    (hr : r.msatPerKw ≤ r'.msatPerKw)
    (h : waveD_d13_commitmentFeeInsufficient r c) :
    waveD_d13_commitmentFeeInsufficient r' c :=
  fun hsuff => h (feeSufficient_rate_mono hr hsuff)

/-- Adding untrimmed HTLC weight cannot turn an insufficient commitment into
a sufficient one. -/
theorem waveD_d13_insufficient_mono_weight
    {r : FeeRate} {w₁ w₂ : Weight} {paid : Msat}
    (hw : w₁.val ≤ w₂.val)
    (h : Fee.feeInsufficient r w₁ paid) :
    Fee.feeInsufficient r w₂ paid := by
  intro hsuff
  exact h (Nat.le_trans (feeForWeight_mono_weight r hw) hsuff)

/-- The commitment-level version: more untrimmed HTLCs can only make a fee
shortfall worse. -/
theorem waveD_d13_commitment_insufficient_mono_htlcs
    (r : FeeRate) (c : Commitment) {m : Nat}
    (hm : c.htlcs.length ≤ m)
    (h : waveD_d13_commitmentFeeInsufficient r c) :
    Fee.feeInsufficient r (commitmentWeight c.anchorOutputs m)
      (waveD_d13_commitmentFeePaid c) := by
  intro hsuff
  exact h (Nat.le_trans (commitmentFee_mono_htlcs r c hm) hsuff)

/-- Specialization to a negotiated `update_fee`: an insufficient commitment
stays insufficient after raising the parameter feerate. -/
theorem waveD_d13_updateFee_insufficient
    {p : ChannelParams} {r : FeeRate} (hr : p.feerate.msatPerKw ≤ r.msatPerKw)
    {c : Commitment}
    (h : waveD_d13_commitmentFeeInsufficient p.feerate c) :
    waveD_d13_commitmentFeeInsufficient (updateFee p r).feerate c := by
  simpa [updateFee] using waveD_d13_insufficient_mono_rate hr h

/-- A zero feerate requires no fee, so rejection is not vacuous. -/
theorem waveD_d13_zero_rate_sufficient (c : Commitment) :
    waveD_d13_commitmentFeeSufficient ⟨0⟩ c := by
  unfold waveD_d13_commitmentFeeSufficient waveD_d13_commitmentFeePaid
  simp [feeSufficient, feeForWeight]

theorem waveD_d13_zero_rate_gate_signs (c : Commitment) :
    (waveD_d13_commitmentSigningGate ⟨0⟩ c).emitsSignature = true :=
  waveD_d13_gate_signature_of_sufficient (waveD_d13_zero_rate_sufficient c)

/-! ## Checked signing transition -/

/-- `FeeCheckedStep r c cm e c' cm'` refines the BOLT 2 step relation
`Step c e c'` with the pre-signature fee gate.  The *only* way to perform
`commitment_signed` is the constructor carrying a proof that the commitment
`cm` pays the base fee required at rate `r`.  Every other event is the
unmodified `Step` relation and leaves `cm` untouched.

The commitment record is a separate index because `LnLean.Channel.Channel`
does not carry a commitment transaction (or its fee) as a field. -/
inductive waveD_d13_FeeCheckedStep (r : FeeRate) :
    Channel → Commitment → ProtocolEvent → Channel → Commitment → Prop where
  /-- Signing is permitted only for a fee-sufficient commitment. -/
  | commitmentSigned (c : Channel) (cm : Commitment)
      (hphase : c.phase = ChannelPhase.normal)
      (hsufficient : waveD_d13_commitmentFeeSufficient r cm) :
      waveD_d13_FeeCheckedStep r c cm ProtocolEvent.commitmentSigned
        { c with remoteCommitmentNumber := c.remoteCommitmentNumber + 1 } cm
  /-- All non-signing events are exactly the BOLT 2 transition. -/
  | lift (c : Channel) (cm : Commitment) {e : ProtocolEvent} {c' : Channel}
      (hstep : Step c e c')
      (hne : e ≠ ProtocolEvent.commitmentSigned) :
      waveD_d13_FeeCheckedStep r c cm e c' cm

/-- The checked relation only performs legal BOLT 2 steps. -/
theorem waveD_d13_feeCheckedStep_step
    {r : FeeRate} {c : Channel} {cm : Commitment} {e : ProtocolEvent}
    {c' : Channel} {cm' : Commitment}
    (h : waveD_d13_FeeCheckedStep r c cm e c' cm') :
    Step c e c' := by
  cases h with
  | commitmentSigned hphase _ => exact Step.commitmentSigned c hphase
  | lift hstep _ => exact hstep

/-- Every checked `commitment_signed` has a fee-sufficient commitment. -/
theorem waveD_d13_feeCheckedStep_commitmentSigned_sufficient
    {r : FeeRate} {c : Channel} {cm : Commitment}
    {c' : Channel} {cm' : Commitment}
    (h : waveD_d13_FeeCheckedStep r c cm ProtocolEvent.commitmentSigned c' cm') :
    waveD_d13_commitmentFeeSufficient r cm := by
  cases h with
  | commitmentSigned _ hsufficient => exact hsufficient
  | lift _ hne => exact (hne rfl).elim

/-- An insufficient commitment admits no checked signing transition.  This
is the "rejected before signing" property at the transition level. -/
theorem waveD_d13_insufficient_no_checked_signing
    {r : FeeRate} {c : Channel} {cm : Commitment}
    {c' : Channel} {cm' : Commitment}
    (h : waveD_d13_commitmentFeeInsufficient r cm) :
    ¬ waveD_d13_FeeCheckedStep r c cm
        ProtocolEvent.commitmentSigned c' cm' := by
  intro hstep
  exact h (waveD_d13_feeCheckedStep_commitmentSigned_sufficient hstep)

/-- A legal non-signing BOLT 2 step is also a checked step. -/
theorem waveD_d13_feeCheckedStep_of_step_of_ne
    {r : FeeRate} {c : Channel} {cm : Commitment} {e : ProtocolEvent}
    {c' : Channel}
    (h : Step c e c') (hne : e ≠ ProtocolEvent.commitmentSigned) :
    waveD_d13_FeeCheckedStep r c cm e c' cm :=
  waveD_d13_FeeCheckedStep.lift c cm h hne

/-- Full characterization of the checked signing transition. -/
theorem waveD_d13_feeCheckedStep_commitmentSigned_iff
    {r : FeeRate} {c : Channel} {cm : Commitment}
    {c' : Channel} {cm' : Commitment} :
    waveD_d13_FeeCheckedStep r c cm ProtocolEvent.commitmentSigned c' cm' ↔
      c' = { c with remoteCommitmentNumber := c.remoteCommitmentNumber + 1 } ∧
        cm' = cm ∧ c.phase = ChannelPhase.normal ∧
          waveD_d13_commitmentFeeSufficient r cm := by
  constructor
  · intro h
    cases h with
    | commitmentSigned hphase hsufficient =>
        exact ⟨rfl, rfl, hphase, hsufficient⟩
    | lift _ hne => exact (hne rfl).elim
  · rintro ⟨rfl, rfl, hphase, hsufficient⟩
    exact waveD_d13_FeeCheckedStep.commitmentSigned c _ hphase hsufficient

/-! ## A concrete threshold example -/

/-- A zero-HTLC, no-anchor commitment (expected weight 724) paying 1 sat. -/
def waveD_d13_exampleCommitment : Commitment :=
  { holder := .local
    commitmentNumber := 0
    fundingValueSat := 100000
    toLocalSat := 50000
    toRemoteSat := 49000
    htlcs := []
    feeSat := 1
    contestDelay := 144
    anchorOutputs := false }

theorem waveD_d13_example_weight :
    waveD_d13_exampleCommitment.weight.val = 724 := by
  decide

/-- At 1000 msat/kw the required fee is 724 msat, covered by the 1 sat
(1000 msat) paid fee. -/
theorem waveD_d13_example_sufficient_at_low_rate :
    waveD_d13_commitmentFeeSufficient ⟨1000⟩
      waveD_d13_exampleCommitment := by
  decide

/-- After raising the feerate to 2000 msat/kw the required fee is 1448 msat,
which the 1 sat paid fee no longer covers. -/
theorem waveD_d13_example_insufficient_at_high_rate :
    waveD_d13_commitmentFeeInsufficient ⟨2000⟩
      waveD_d13_exampleCommitment := by
  decide

theorem waveD_d13_example_gate_signs_at_low_rate :
    (waveD_d13_commitmentSigningGate ⟨1000⟩
      waveD_d13_exampleCommitment).emitsSignature = true :=
  waveD_d13_gate_signature_of_sufficient
    waveD_d13_example_sufficient_at_low_rate

theorem waveD_d13_example_gate_rejects_at_high_rate :
    (waveD_d13_commitmentSigningGate ⟨2000⟩
      waveD_d13_exampleCommitment).emitsSignature = false :=
  waveD_d13_gate_no_signature_of_insufficient
    waveD_d13_example_insufficient_at_high_rate

/-- A single `update_fee` can move the same commitment from accepted to
rejected, which is exactly the behaviour the gate is meant to enforce. -/
theorem waveD_d13_example_updateFee_flips_verdict :
    (waveD_d13_commitmentSigningGate ⟨1000⟩
        waveD_d13_exampleCommitment).emitsSignature = true ∧
      (waveD_d13_commitmentSigningGate ⟨2000⟩
        waveD_d13_exampleCommitment).emitsSignature = false :=
  ⟨waveD_d13_example_gate_signs_at_low_rate,
    waveD_d13_example_gate_rejects_at_high_rate⟩

/-- The high-rate rejection is a genuine transition-level rejection: no
checked `commitment_signed` derivation exists for this commitment. -/
theorem waveD_d13_example_no_checked_signing_at_high_rate
    (c : Channel) (c' : Channel) (cm' : Commitment) :
    ¬ waveD_d13_FeeCheckedStep ⟨2000⟩ c waveD_d13_exampleCommitment
        ProtocolEvent.commitmentSigned c' cm' :=
  waveD_d13_insufficient_no_checked_signing
    waveD_d13_example_insufficient_at_high_rate

-- OBLIGATION: LN-WD-D13

end LnLean.Proofs.WaveD.D13
