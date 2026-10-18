import LnLean.Channel.Commitment
import LnLean.Channel.Fee
import LnLean.Channel.State
import LnLean.Proofs.WaveD.D13

/-!
# LnLean.Proofs.Channel.FeeTargets

English claim (catalog `LN-CH-005`).  A commitment whose recorded fee does
not cover the BOLT 3 base fee required by the negotiated `feerate_per_kw` for
its expected weight is rejected by the pre-signature fee check; conversely,
the check rejects a commitment exactly when its fee is insufficient.

This module closes the gap recorded for `LN-CH-005`.  The catalog target
`LnLean.Channel.Fee.feeInsufficient` (supplied by
`LnLean.Proofs.WaveD.D13`) is only a predicate definition: it says that the
paid millisatoshi amount is below `feerate_per_kw * weight / 1000`.  A
predicate definition is not a proof that a commitment carrying such a fee is
rejected before signing.  The declarations below give that proof at three
levels, all with the feerate `r`, the weight `w`, and the paid fee `paid`
explicit:

* `feeAccepted` is the executable Boolean version of `feeSufficient`.
  `feeAccepted_eq_true_iff` and `feeAccepted_eq_false_iff` characterize it
  exactly; the latter is the first exact "rejected iff insufficient" step.
* `commitmentSigningGate` is the pre-signature gate for a concrete
  `Commitment`, using the commitment's own `weight` and its recorded
  `feeSat` converted to millisatoshis.  The headline theorem
  `commitmentSigningGate_rejected_iff_insufficient` is an iff between the
  gate's rejection verdict and `Fee.feeInsufficient`.
* `LnLean.Proofs.WaveD.D13.waveD_d13_FeeCheckedStep` is the transition
  relation whose only `commitment_signed` constructor carries a sufficiency
  proof.  `no_checkedCommitmentSigned_iff_insufficient` is the converse of
  D13's one-directional no-derivation theorem: for a channel in the `normal`
  phase, *absence* of a checked signing derivation is equivalent to fee
  insufficiency.  `commitmentSigningGate_rejected_iff_no_checkedSigning`
  composes the two levels: the gate rejects exactly those commitments for
  which no checked signing transition exists.

The explicit policy assumptions are:

* The fee is BOLT 3's *base* commitment fee, floored:
  `r.msatPerKw * w.val / 1000`.  It is compared against the commitment's
  recorded `feeSat`, converted exactly as `feeSat * 1000` millisatoshis
  (BOLT 3 stores commitment fees in whole satoshis).
* The weight is the BOLT 3 expected weight
  `724 + 172 * num_untrimmed_htlcs` (or `1124 + ...` with anchors), exposed
  as `Commitment.weight`.
* Zero-fee commitments, anchor child-pays-for-parent, RBF, mempool/relay
  policy, fee estimation, and the difference between the required base fee
  and the actual on-chain fee after trimming are **not** modelled.  The gate
  is the model's policy precondition, not a relay simulation.
* The refusal is represented by `ErrorCode.feeInsufficient`; no wire
  encoding of the `error` message is claimed.

BOLT sections.
* BOLT 3 §4 `Fees` (`03-transactions.md:464-576`), in particular the expected
  weights at `:490-502` and the floor-divided base-fee rule at `:518-523`.
* BOLT 3 §5 `Dust Limits` (`03-transactions.md:583-620`); trimming happens
  before the weight is fixed, so the gate is applied to the post-trim
  commitment weight.
* BOLT 2 §3 `update_fee` and the receiver's affordability check
  (`02-peer-protocol.md:3250-3310`).

rust-lightning anchors at `fe4900930c6bd5786ec4203274d7cf312776a5a6`.
* `lightning/src/ln/chan_utils.rs:275-298`
  (`COMMITMENT_TX_WEIGHT_PER_HTLC = 172`, base weights, `commit_tx_fee_sat`).
* `lightning/src/ln/channel.rs:3721` (the commitment construction context
  carrying `feerate_per_kw`; the catalog's LDK anchor).

The module does not modify `LnLean.Channel.Fee` or
`LnLean.Channel.Commitment`.  It reuses the exact target predicate from D13
and adds theorems; the statement-only predicate itself is unchanged.
-/

namespace LnLean.Channel

namespace Fee

set_option autoImplicit false

open LnLean

/-! ## The paid fee of a commitment, in millisatoshis -/

/-- The fee recorded on a commitment, in millisatoshis.  `Commitment.feeSat`
is a whole number of satoshis, so the conversion is exact.  This is
definitionally the same value as D13's
`waveD_d13_commitmentFeePaid`. -/
def commitmentFeePaidMsat (c : Commitment) : Msat :=
  ⟨c.feeSat * 1000⟩

theorem commitmentFeePaidMsat_val (c : Commitment) :
    (commitmentFeePaidMsat c).val = c.feeSat * 1000 := rfl

/-- The commitment's recorded fee covers the BOLT 3 base fee required by
`r` at the commitment's own expected weight. -/
def CommitmentFeeSufficient (r : FeeRate) (c : Commitment) : Prop :=
  feeSufficient r c.weight (commitmentFeePaidMsat c)

/-- The commitment's recorded fee is below the BOLT 3 base fee required by
`r` at the commitment's own expected weight. -/
def CommitmentFeeInsufficient (r : FeeRate) (c : Commitment) : Prop :=
  feeInsufficient r c.weight (commitmentFeePaidMsat c)

/-! Decidability instances for the two commitment-level predicates, so the
gate below is computable and the concrete examples do not need classical
logic. -/

instance commitmentFeeSufficientDecidable (r : FeeRate) (c : Commitment) :
    Decidable (CommitmentFeeSufficient r c) :=
  inferInstanceAs (Decidable ((feeForWeight r c.weight).val ≤
    (commitmentFeePaidMsat c).val))

instance commitmentFeeInsufficientDecidable (r : FeeRate) (c : Commitment) :
    Decidable (CommitmentFeeInsufficient r c) :=
  inferInstanceAs (Decidable (¬ (feeForWeight r c.weight).val ≤
    (commitmentFeePaidMsat c).val))

/-- Decidability of the model predicate at explicit parameters.  This is the
instance the executable check and the concrete examples use. -/
instance feeSufficientDecidable (r : FeeRate) (w : Weight) (paid : Msat) :
    Decidable (feeSufficient r w paid) :=
  inferInstanceAs (Decidable ((feeForWeight r w).val ≤ paid.val))

/-! ## The generic Boolean pre-signature check -/

/-- The executable form of `feeSufficient`: `true` exactly when the paid
millisatoshi amount covers the floored requirement of feerate `r` and weight
`w`. -/
def feeAccepted (r : FeeRate) (w : Weight) (paid : Msat) : Bool :=
  decide (feeSufficient r w paid)

/-- The Boolean check accepts exactly the fee-sufficient parameters. -/
theorem feeAccepted_eq_true_iff (r : FeeRate) (w : Weight) (paid : Msat) :
    feeAccepted r w paid = true ↔ feeSufficient r w paid := by
  unfold feeAccepted
  exact decide_eq_true_iff

/-- The Boolean check rejects exactly the fee-insufficient parameters.  This
is the parameter-level "rejected iff insufficient" theorem, with the feerate,
weight, and paid fee all explicit. -/
theorem feeAccepted_eq_false_iff (r : FeeRate) (w : Weight) (paid : Msat) :
    feeAccepted r w paid = false ↔ feeInsufficient r w paid := by
  unfold feeAccepted
  rw [decide_eq_false_iff_not]
  unfold feeInsufficient
  exact Iff.rfl

/-- Exact floored-product characterization of sufficiency:
`r * w / 1000 ≤ paid` iff `r * w ≤ paid * 1000 + 999`.  The `+ 999` is the
floor, not slack in the policy. -/
theorem feeSufficient_iff_product_le (r : FeeRate) (w : Weight) (paid : Msat) :
    feeSufficient r w paid ↔
      r.msatPerKw * w.val ≤ paid.val * 1000 + 999 := by
  unfold feeSufficient feeForWeight
  exact Nat.div_le_iff_le_mul (by decide : 0 < 1000)

/-- Exact strict-product characterization of insufficiency:
the floored requirement exceeds the paid fee iff the paid millisatoshis plus
the floor residue stay strictly below the raw product. -/
theorem feeInsufficient_iff_product_lt (r : FeeRate) (w : Weight) (paid : Msat) :
    feeInsufficient r w paid ↔
      paid.val * 1000 + 999 < r.msatPerKw * w.val := by
  unfold feeInsufficient
  rw [feeSufficient_iff_product_le]
  exact Nat.not_le

/-! ## The pre-signature verdict and gate -/

/-- Outcome of the pre-signature fee check for one commitment: either the
commitment is released for signing, or the check returns an explicit protocol
error. -/
inductive SigningVerdict where
  | sign (commitment : Commitment)
  | reject (error : ProtocolError)
deriving Repr

namespace SigningVerdict

/-- Does this verdict release a signature? -/
def emitsSignature : SigningVerdict → Bool
  | .sign _ => true
  | .reject _ => false

/-- Is this verdict a rejection? -/
def isRejected : SigningVerdict → Prop
  | .sign _ => False
  | .reject _ => True

/-- The commitment released for signing, if any. -/
def commitment? : SigningVerdict → Option Commitment
  | .sign c => some c
  | .reject _ => none

theorem isRejected_iff_emitsSignature_eq_false (v : SigningVerdict) :
    v.isRejected ↔ v.emitsSignature = false := by
  cases v <;> simp [isRejected, emitsSignature]

end SigningVerdict

/-- The BOLT 3 base-fee gate, evaluated before any signature is produced.
It releases `c` only when `c.feeSat`, read as millisatoshis, covers
`feeForWeight r c.weight`; otherwise it returns the `fee_insufficient`
error. -/
def commitmentSigningGate (r : FeeRate) (c : Commitment) : SigningVerdict :=
  if feeSufficient r c.weight (commitmentFeePaidMsat c) then
    .sign c
  else
    .reject { code := ErrorCode.feeInsufficient }

/-- The gate releases the commitment for signing exactly when its fee is
sufficient. -/
theorem commitmentSigningGate_sign_iff (r : FeeRate) (c : Commitment) :
    commitmentSigningGate r c = .sign c ↔ CommitmentFeeSufficient r c := by
  unfold commitmentSigningGate CommitmentFeeSufficient
  by_cases h : feeSufficient r c.weight (commitmentFeePaidMsat c)
  · simp [h]
  · simp [h]

/-- **Headline theorem for `LN-CH-005`.**  The pre-signature gate rejects a
commitment exactly when its recorded fee is insufficient for the negotiated
feerate and its own expected weight.  This is an iff, not merely a sufficient
condition, and it names `Fee.feeInsufficient` explicitly. -/
theorem commitmentSigningGate_rejected_iff_insufficient
    (r : FeeRate) (c : Commitment) :
    (commitmentSigningGate r c).isRejected ↔
      feeInsufficient r c.weight (commitmentFeePaidMsat c) := by
  unfold commitmentSigningGate
  by_cases h : feeSufficient r c.weight (commitmentFeePaidMsat c)
  · simp [h, SigningVerdict.isRejected, feeInsufficient]
  · simp [h, SigningVerdict.isRejected, feeInsufficient]

/-- The commitment-level form of the headline theorem. -/
theorem commitmentSigningGate_rejected_iff_commitmentFeeInsufficient
    (r : FeeRate) (c : Commitment) :
    (commitmentSigningGate r c).isRejected ↔ CommitmentFeeInsufficient r c :=
  commitmentSigningGate_rejected_iff_insufficient r c

/-- The gate emits no signature exactly for an insufficient commitment. -/
theorem commitmentSigningGate_emitsSignature_eq_false_iff
    (r : FeeRate) (c : Commitment) :
    (commitmentSigningGate r c).emitsSignature = false ↔
      feeInsufficient r c.weight (commitmentFeePaidMsat c) := by
  rw [← SigningVerdict.isRejected_iff_emitsSignature_eq_false]
  exact commitmentSigningGate_rejected_iff_insufficient r c

/-- An insufficient commitment is rejected with the explicit
`ErrorCode.feeInsufficient` payload. -/
theorem commitmentSigningGate_rejects_of_insufficient
    {r : FeeRate} {c : Commitment} (h : CommitmentFeeInsufficient r c) :
    commitmentSigningGate r c =
      .reject { code := ErrorCode.feeInsufficient } := by
  unfold commitmentSigningGate
  unfold CommitmentFeeInsufficient at h
  unfold feeInsufficient at h
  simp [h]

/-- A sufficient commitment is released for signing. -/
theorem commitmentSigningGate_signs_of_sufficient
    {r : FeeRate} {c : Commitment} (h : CommitmentFeeSufficient r c) :
    commitmentSigningGate r c = .sign c :=
  (commitmentSigningGate_sign_iff r c).mpr h

/-- Every signature released by the gate carries a sufficient fee. -/
theorem commitmentSigningGate_sign_sound
    {r : FeeRate} {c c' : Commitment}
    (h : commitmentSigningGate r c = .sign c') :
    c' = c ∧ CommitmentFeeSufficient r c := by
  unfold commitmentSigningGate at h
  by_cases hs : feeSufficient r c.weight (commitmentFeePaidMsat c)
  · simp [hs] at h
    exact ⟨h.symm, hs⟩
  · simp [hs] at h

/-- No insufficient commitment is ever released by the gate. -/
theorem commitmentSigningGate_no_sign_of_insufficient
    {r : FeeRate} {c : Commitment} (h : CommitmentFeeInsufficient r c) :
    commitmentSigningGate r c ≠ .sign c := by
  rw [commitmentSigningGate_rejects_of_insufficient h]
  simp

/-! ## Numeric characterizations at the commitment level -/

/-- Insufficiency is the strict failure of the floored comparison. -/
theorem commitmentFeeInsufficient_iff_lt (r : FeeRate) (c : Commitment) :
    CommitmentFeeInsufficient r c ↔
      c.feeSat * 1000 < (feeForWeight r c.weight).val := by
  unfold CommitmentFeeInsufficient feeInsufficient feeSufficient
    commitmentFeePaidMsat
  exact Nat.not_le

/-- Exact product form: the commitment is insufficient iff the raw required
product exceeds the paid millisatoshis plus the floor residue.  The paid fee
is `feeSat * 1000` msat, so the product bound is
`(feeSat * 1000) * 1000 + 999`. -/
theorem commitmentFeeInsufficient_iff_product_lt
    (r : FeeRate) (c : Commitment) :
    CommitmentFeeInsufficient r c ↔
      (c.feeSat * 1000) * 1000 + 999 < r.msatPerKw * c.weight.val :=
  feeInsufficient_iff_product_lt r c.weight (commitmentFeePaidMsat c)

/-- Sufficiency in the same product form. -/
theorem commitmentFeeSufficient_iff_product_le
    (r : FeeRate) (c : Commitment) :
    CommitmentFeeSufficient r c ↔
      r.msatPerKw * c.weight.val ≤ (c.feeSat * 1000) * 1000 + 999 :=
  feeSufficient_iff_product_le r c.weight (commitmentFeePaidMsat c)

/-- Literal feerate-threshold form of insufficiency, for positive weight: the
negotiated feerate is above the largest rate the recorded fee can cover.
The threshold is exact for the floored BOLT 3 requirement. -/
theorem commitmentFeeInsufficient_iff_rate_gt
    (r : FeeRate) (c : Commitment) (hw : 0 < c.weight.val) :
    CommitmentFeeInsufficient r c ↔
      ((c.feeSat * 1000) * 1000 + 999) / c.weight.val < r.msatPerKw := by
  rw [commitmentFeeInsufficient_iff_product_lt, Nat.div_lt_iff_lt_mul hw]

/-- Dual feerate-threshold form: the commitment is sufficient exactly when
the negotiated feerate is at most the rate the recorded fee covers. -/
theorem commitmentFeeSufficient_iff_rate_le
    (r : FeeRate) (c : Commitment) (hw : 0 < c.weight.val) :
    CommitmentFeeSufficient r c ↔
      r.msatPerKw ≤ ((c.feeSat * 1000) * 1000 + 999) / c.weight.val := by
  rw [commitmentFeeSufficient_iff_product_le, Nat.le_div_iff_mul_le hw]

/-- An insufficient commitment leaves a strictly positive millisatoshi
shortfall. -/
theorem commitmentFeeInsufficient_has_deficit
    {r : FeeRate} {c : Commitment} (h : CommitmentFeeInsufficient r c) :
    ∃ d : Nat, 0 < d ∧
      (feeForWeight r c.weight).val = c.feeSat * 1000 + d := by
  have hlt := (commitmentFeeInsufficient_iff_lt r c).mp h
  exact ⟨(feeForWeight r c.weight).val - c.feeSat * 1000,
    by omega, by omega⟩

/-! ## Monotonicity of rejection in feerate and weight -/

/-- Raising the negotiated feerate cannot turn an insufficient commitment
into a sufficient one. -/
theorem commitmentFeeInsufficient_mono_rate
    {r r' : FeeRate} {c : Commitment}
    (hr : r.msatPerKw ≤ r'.msatPerKw)
    (h : CommitmentFeeInsufficient r c) :
    CommitmentFeeInsufficient r' c := by
  intro hsuff
  exact h (feeSufficient_rate_mono hr hsuff)

/-- Increasing the weight at a fixed feerate cannot turn an insufficient
commitment into a sufficient one.  This covers both added HTLC weight and the
anchor delta. -/
theorem commitmentFeeInsufficient_mono_weight
    {r : FeeRate} {c c' : Commitment}
    (hw : c.weight.val ≤ c'.weight.val)
    (hpaid : c'.feeSat = c.feeSat)
    (h : CommitmentFeeInsufficient r c) :
    CommitmentFeeInsufficient r c' := by
  change ¬ feeSufficient r c.weight (commitmentFeePaidMsat c) at h
  change ¬ feeSufficient r c'.weight (commitmentFeePaidMsat c')
  intro hsuff
  apply h
  change (feeForWeight r c'.weight).val ≤ c'.feeSat * 1000 at hsuff
  change (feeForWeight r c.weight).val ≤ c.feeSat * 1000
  rw [← hpaid]
  exact Nat.le_trans (feeForWeight_mono_weight r hw) hsuff

/-- More untrimmed HTLCs than a commitment already has can only make an
insufficient fee worse. -/
theorem commitmentFeeInsufficient_mono_htlcs
    (r : FeeRate) (c : Commitment) {m : Nat}
    (hm : c.htlcs.length ≤ m)
    (h : CommitmentFeeInsufficient r c) :
    feeInsufficient r (commitmentWeight c.anchorOutputs m)
      (commitmentFeePaidMsat c) := by
  change ¬ feeSufficient r c.weight (commitmentFeePaidMsat c) at h
  change ¬ feeSufficient r (commitmentWeight c.anchorOutputs m)
    (commitmentFeePaidMsat c)
  intro hsuff
  apply h
  change (feeForWeight r (commitmentWeight c.anchorOutputs m)).val ≤
    c.feeSat * 1000 at hsuff
  change (feeForWeight r c.weight).val ≤ c.feeSat * 1000
  exact Nat.le_trans (commitmentFee_mono_htlcs r c hm) hsuff

/-! ## Transition level: no checked signing exactly when insufficient

`LnLean.Proofs.WaveD.D13.waveD_d13_FeeCheckedStep r c cm e c' cm'` refines
the BOLT 2 `Step` relation with the pre-signature fee gate.  Its only
`commitment_signed` constructor carries a proof that the commitment `cm` is
fee-sufficient.  D13 proves the one-directional statement that an
insufficient commitment has no such derivation; the theorems below prove the
converse under the explicit phase assumption (`commitment_signed` is only
legal in the `normal` phase), yielding an exact characterization.
-/

/-- The commitment-level sufficiency predicate is definitionally D13's. -/
theorem commitmentFeeSufficient_iff_d13 (r : FeeRate) (c : Commitment) :
    CommitmentFeeSufficient r c ↔
      LnLean.Proofs.WaveD.D13.waveD_d13_commitmentFeeSufficient r c :=
  Iff.rfl

/-- A checked `commitment_signed` transition exists at the canonical
successor state iff the commitment is fee-sufficient.  The phase hypothesis
is necessary: before `normal`, `commitment_signed` is illegal for any fee. -/
theorem checkedCommitmentSigned_iff_sufficient
    {r : FeeRate} {c : Channel} {cm : Commitment}
    (hphase : c.phase = ChannelPhase.normal) :
    LnLean.Proofs.WaveD.D13.waveD_d13_FeeCheckedStep r c cm
        ProtocolEvent.commitmentSigned
        { c with remoteCommitmentNumber := c.remoteCommitmentNumber + 1 } cm ↔
      CommitmentFeeSufficient r cm := by
  rw [LnLean.Proofs.WaveD.D13.waveD_d13_feeCheckedStep_commitmentSigned_iff]
  simp [hphase, CommitmentFeeSufficient,
    LnLean.Proofs.WaveD.D13.waveD_d13_commitmentFeeSufficient,
    LnLean.Proofs.WaveD.D13.waveD_d13_commitmentFeePaid,
    commitmentFeePaidMsat]

/-- Some checked `commitment_signed` derivation exists iff the commitment is
fee-sufficient. -/
theorem exists_checkedCommitmentSigned_iff_sufficient
    {r : FeeRate} {c : Channel} {cm : Commitment}
    (hphase : c.phase = ChannelPhase.normal) :
    (∃ c' cm', LnLean.Proofs.WaveD.D13.waveD_d13_FeeCheckedStep r c cm
        ProtocolEvent.commitmentSigned c' cm') ↔
      CommitmentFeeSufficient r cm := by
  constructor
  · rintro ⟨c', cm', hstep⟩
    rcases (LnLean.Proofs.WaveD.D13.waveD_d13_feeCheckedStep_commitmentSigned_iff
      (r := r) (c := c) (cm := cm) (c' := c') (cm' := cm')).mp hstep with
      ⟨_, _, _, hsuff⟩
    exact (commitmentFeeSufficient_iff_d13 r cm).mpr hsuff
  · intro hsuff
    exact ⟨_, _, (checkedCommitmentSigned_iff_sufficient hphase).mpr hsuff⟩

/-- **Exact transition-level characterization.**  For a channel in the
`normal` phase, an insufficient commitment admits no checked signing
transition, and a sufficient commitment does have one. -/
theorem no_checkedCommitmentSigned_iff_insufficient
    {r : FeeRate} {c : Channel} {cm : Commitment}
    (hphase : c.phase = ChannelPhase.normal) :
    (¬ ∃ c' cm', LnLean.Proofs.WaveD.D13.waveD_d13_FeeCheckedStep r c cm
        ProtocolEvent.commitmentSigned c' cm') ↔
      CommitmentFeeInsufficient r cm := by
  rw [exists_checkedCommitmentSigned_iff_sufficient hphase]
  unfold CommitmentFeeInsufficient feeInsufficient CommitmentFeeSufficient
  exact Iff.rfl

/-- **Combined catalog statement.**  The pre-signature gate rejects a
commitment exactly when the checked transition relation admits no
`commitment_signed` derivation for it.  This connects the executable verdict,
the `feeInsufficient` predicate, and the signing relation in one iff. -/
theorem commitmentSigningGate_rejected_iff_no_checkedSigning
    {r : FeeRate} {c : Channel} {cm : Commitment}
    (hphase : c.phase = ChannelPhase.normal) :
    (commitmentSigningGate r cm).isRejected ↔
      ¬ ∃ c' cm', LnLean.Proofs.WaveD.D13.waveD_d13_FeeCheckedStep r c cm
        ProtocolEvent.commitmentSigned c' cm' := by
  constructor
  · intro hr
    exact (no_checkedCommitmentSigned_iff_insufficient hphase).mpr
      ((commitmentSigningGate_rejected_iff_commitmentFeeInsufficient r cm).mp hr)
  · intro hno
    exact (commitmentSigningGate_rejected_iff_commitmentFeeInsufficient r cm).mpr
      ((no_checkedCommitmentSigned_iff_insufficient hphase).mp hno)

/-- Unconditional forward direction of `LN-CH-005`, with no phase hypothesis:
an insufficient commitment has no checked signing derivation at all.  (An
insufficient commitment is also rejected by any channel in any phase, because
the gate does not inspect the phase.) -/
theorem insufficient_no_checkedCommitmentSigned
    {r : FeeRate} {c : Channel} {cm : Commitment}
    (h : CommitmentFeeInsufficient r cm) :
    ¬ ∃ c' cm', LnLean.Proofs.WaveD.D13.waveD_d13_FeeCheckedStep r c cm
        ProtocolEvent.commitmentSigned c' cm' := by
  rintro ⟨c', cm', hstep⟩
  have hsuff :=
    LnLean.Proofs.WaveD.D13.waveD_d13_feeCheckedStep_commitmentSigned_sufficient
      (r := r) (c := c) (cm := cm) (c' := c') (cm' := cm') hstep
  exact h ((commitmentFeeSufficient_iff_d13 r cm).mpr hsuff)

/-- Direct conjunction form of the catalog claim: the pre-signature gate
rejects the commitment and the checked signing relation has no derivation for
it.  The left conjunct is the executable verdict; the right conjunct is the
"before signing" transition fact. -/
theorem commitment_rejected_before_signing
    {r : FeeRate} {c : Channel} {cm : Commitment}
    (h : feeInsufficient r cm.weight (commitmentFeePaidMsat cm)) :
    (commitmentSigningGate r cm).isRejected ∧
      ¬ ∃ c' cm', LnLean.Proofs.WaveD.D13.waveD_d13_FeeCheckedStep r c cm
        ProtocolEvent.commitmentSigned c' cm' :=
  ⟨(commitmentSigningGate_rejected_iff_insufficient r cm).mpr h,
    insufficient_no_checkedCommitmentSigned (r := r) (c := c) (cm := cm) h⟩

/-! ## Non-vacuity: a concrete commitment at two feerates

The following record has no HTLCs and no anchors, so its BOLT 3 expected
weight is `724`.  It pays one satoshi (1000 msat).  At `1000 msat/kw` the
required fee is 724 msat and the gate signs; at `2000 msat/kw` the required
fee is 1448 msat, so the gate rejects and no checked signing transition
exists. -/

/-- A zero-HTLC, no-anchor commitment (weight 724) paying 1 satoshi. -/
def sampleCommitment : Commitment :=
  { holder := .local
    commitmentNumber := 0
    fundingValueSat := 100000
    toLocalSat := 50000
    toRemoteSat := 49000
    htlcs := []
    feeSat := 1
    contestDelay := 144
    anchorOutputs := false }

theorem sampleCommitment_weight : sampleCommitment.weight.val = 724 := by
  decide

theorem sampleCommitment_feePaid :
    (commitmentFeePaidMsat sampleCommitment).val = 1000 := by
  decide

/-- At 1000 msat/kw the 1 satoshi fee covers the required 724 msat. -/
theorem sampleCommitment_sufficient_at_low_rate :
    CommitmentFeeSufficient ⟨1000⟩ sampleCommitment := by
  unfold CommitmentFeeSufficient commitmentFeePaidMsat feeSufficient
    feeForWeight Commitment.weight commitmentWeight commitmentBaseWeight
    commitmentHtlcWeight sampleCommitment
  decide

/-- At 2000 msat/kw the required 1448 msat exceeds the paid 1000 msat. -/
theorem sampleCommitment_insufficient_at_high_rate :
    CommitmentFeeInsufficient ⟨2000⟩ sampleCommitment := by
  unfold CommitmentFeeInsufficient feeInsufficient feeSufficient
    commitmentFeePaidMsat feeForWeight Commitment.weight commitmentWeight
    commitmentBaseWeight commitmentHtlcWeight sampleCommitment
  decide

theorem sampleCommitment_gate_signs_at_low_rate :
    (commitmentSigningGate ⟨1000⟩ sampleCommitment).emitsSignature = true := by
  have h : feeSufficient ⟨1000⟩ sampleCommitment.weight
      (commitmentFeePaidMsat sampleCommitment) :=
    sampleCommitment_sufficient_at_low_rate
  unfold commitmentSigningGate
  simp [h, SigningVerdict.emitsSignature]

theorem sampleCommitment_gate_rejects_at_high_rate :
    (commitmentSigningGate ⟨2000⟩ sampleCommitment).isRejected :=
  (commitmentSigningGate_rejected_iff_commitmentFeeInsufficient _ _).mpr
    sampleCommitment_insufficient_at_high_rate

/-- At the low rate a checked signing derivation exists (for any normal-phase
channel), so the transition-level characterization is not vacuous in the
positive direction. -/
theorem sampleCommitment_checked_signing_at_low_rate
    {c : Channel} (hphase : c.phase = ChannelPhase.normal) :
    LnLean.Proofs.WaveD.D13.waveD_d13_FeeCheckedStep ⟨1000⟩ c
      sampleCommitment ProtocolEvent.commitmentSigned
      { c with remoteCommitmentNumber := c.remoteCommitmentNumber + 1 }
      sampleCommitment :=
  (checkedCommitmentSigned_iff_sufficient hphase).mpr
    sampleCommitment_sufficient_at_low_rate

/-- At the high rate no checked signing derivation exists. -/
theorem sampleCommitment_no_checked_signing_at_high_rate
    {c : Channel} (hphase : c.phase = ChannelPhase.normal) :
    ¬ ∃ c' cm', LnLean.Proofs.WaveD.D13.waveD_d13_FeeCheckedStep ⟨2000⟩ c
      sampleCommitment ProtocolEvent.commitmentSigned c' cm' :=
  (no_checkedCommitmentSigned_iff_insufficient hphase).mpr
    sampleCommitment_insufficient_at_high_rate

end Fee

end LnLean.Channel
