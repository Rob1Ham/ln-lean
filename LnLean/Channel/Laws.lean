import LnLean.Channel.Types
import LnLean.Channel.State
import LnLean.Channel.Commitment
import LnLean.Channel.Fee

/-!
# LnLean.Channel.Laws

English claim.  This module states the channel-level laws that the
definitions in `Types`, `State`, `Commitment`, and `Fee` must satisfy:

1. **Value conservation.**  For a commitment whose `to_remote` is whatever
   remains after `to_local`, the fee, the untrimmed HTLC outputs, and the
   anchors, the sum of the outputs plus the fee equals the funding value.
2. **Fee monotonicity.**  The fee is non-decreasing in the feerate and in
   the transaction weight; raising the feerate cannot lower a commitment
   fee.
3. **Commitment-number discipline.**  Only `commitment_signed` and
   `revoke_and_ack` change a commitment counter, and each changes exactly
   one counter by exactly one.  Every other event leaves both counters
   unchanged.
4. **Phase progression.**  No legal step, and no finite sequence of legal
   steps, moves the channel to an earlier phase.
5. **Reserve non-negativity.**  Once the reserve is met, the value above it
   is a natural number whose addition to the reserve reconstructs the
   balance; in particular the post-reserve remainder is non-negative.

BOLT sections.
* BOLT 2 §2-§3 (`02-peer-protocol.md:629-1135`, `:3097-3265`) for the
  lifecycle and the commitment dance.
* BOLT 3 §2 and §4 (`03-transactions.md:83-353`, `:464-576`) for outputs,
  fees, and the conservation equation.

rust-lightning anchors at `fe4900930c6bd5786ec4203274d7cf312776a5a6`.
* `lightning/src/ln/chan_utils.rs:1614-1740` (`CommitmentTransaction` and
  its constructor), `:289-298` (`commit_tx_fee_sat`), `:275-283`
  (per-HTLC weight).
* `lightning/src/ln/channel.rs:1546-1610` (channel/commitment counters),
  `:3290-3320` (`update_fee` reserve/affordability handling).

What is NOT modelled.
* The counterexample where a promise is false: none of the laws below is
  weakened.  If a future change makes one false, the corrected statement
  and counterexample must be recorded here.
* HTLC lifecycle conservation (in-flight value, fulfil/fail) is the HTLC
  workstream.
* On-chain fee spikes and penalty economics (BOLT 5, `LN-PENALTY-ECON`).
-/

namespace LnLean.Channel

set_option autoImplicit false

open LnLean

/-! ## Conservation -/

/-- A commitment with an arbitrary list of untrimmed HTLCs, whose
`to_remote` is settled as the remainder after `to_local`, the fee, the HTLC
outputs, and the anchors.  This is the BOLT 3 balance equation before any
dust trimming of `to_local`/`to_remote`. -/
def settledCommitment (holder : Direction) (number funding toLocal fee
    contestDelay : Nat) (htlcs : List CommitmentHTLCOutput) (anchors : Bool) : Commitment :=
  let anchorTotal := if anchors then 2 * anchorOutputSat else 0
  { holder := holder
    commitmentNumber := number
    fundingValueSat := funding
    toLocalSat := toLocal
    toRemoteSat := funding - fee - toLocal - htlcOutputsValue htlcs - anchorTotal
    htlcs := htlcs
    feeSat := fee
    contestDelay := contestDelay
    anchorOutputs := anchors }

/-- **Conservation with HTLCs.**  If the funding covers the holder's output,
the fee, the untrimmed HTLC outputs, and the anchors, then the sum of the
commitment outputs plus the fee is exactly the funding value. -/
theorem conservation_with_htlcs (holder : Direction) (number funding toLocal fee
    contestDelay : Nat) (htlcs : List CommitmentHTLCOutput) (anchors : Bool)
    (h : fee + toLocal + htlcOutputsValue htlcs +
        (if anchors then 2 * anchorOutputSat else 0) ≤ funding) :
    (settledCommitment holder number funding toLocal fee contestDelay htlcs anchors).totalOutputValue
      + fee = funding := by
  unfold settledCommitment Commitment.totalOutputValue Commitment.htlcOutputValue
    Commitment.anchorOutputValue
  simp
  omega

/-- **Zero-HTLC conservation.**  The special case of `conservation_with_htlcs`
used by the opening commitment and by a channel with no in-flight HTLCs. -/
theorem zeroHtlc_conservation (holder : Direction) (number funding toLocal fee
    contestDelay : Nat) (anchors : Bool)
    (h : fee + toLocal + (if anchors then 2 * anchorOutputSat else 0) ≤ funding) :
    (zeroHtlcCommitment holder number funding toLocal fee contestDelay anchors).totalOutputValue
      + fee = funding := by
  unfold zeroHtlcCommitment Commitment.totalOutputValue Commitment.htlcOutputValue
    Commitment.anchorOutputValue htlcOutputsValue
  simp
  omega

/-- A channel with no in-flight HTLCs and no anchors conserves value. -/
theorem zeroHtlc_conservation_noAnchors (holder : Direction) (number funding
    toLocal fee contestDelay : Nat) (h : fee + toLocal ≤ funding) :
    (zeroHtlcCommitment holder number funding toLocal fee contestDelay false).totalOutputValue
      + fee = funding := by
  apply zeroHtlc_conservation
  simpa using h

/-! ## Fee monotonicity -/

/-- **Fee monotonicity in the feerate.** -/
theorem fee_monotone_rate {r₁ r₂ : FeeRate} (h : r₁.msatPerKw ≤ r₂.msatPerKw)
    (w : Weight) :
    (feeForWeight r₁ w).val ≤ (feeForWeight r₂ w).val :=
  feeForWeight_mono_rate h w

/-- **Fee monotonicity in the weight.** -/
theorem fee_monotone_weight (r : FeeRate) {w₁ w₂ : Weight}
    (h : w₁.val ≤ w₂.val) :
    (feeForWeight r w₁).val ≤ (feeForWeight r w₂).val :=
  feeForWeight_mono_weight r h

/-- **Joint fee monotonicity.** -/
theorem fee_monotone {r₁ r₂ : FeeRate} {w₁ w₂ : Weight}
    (hr : r₁.msatPerKw ≤ r₂.msatPerKw) (hw : w₁.val ≤ w₂.val) :
    (feeForWeight r₁ w₁).val ≤ (feeForWeight r₂ w₂).val :=
  feeForWeight_mono hr hw

/-- A commitment with more untrimmed HTLCs has a fee at least as large. -/
theorem commitment_fee_monotone_htlcs (r : FeeRate) (c : Commitment) {m : Nat}
    (h : c.htlcs.length ≤ m) :
    (commitmentFee r c).val ≤
      (feeForWeight r (commitmentWeight c.anchorOutputs m)).val :=
  commitmentFee_mono_htlcs r c h

/-- Raising the feerate via `update_fee` cannot lower the required fee. -/
theorem update_fee_monotone_fee {p : ChannelParams} {r : FeeRate}
    (h : p.feerate.msatPerKw ≤ r.msatPerKw) (w : Weight) :
    (feeForWeight p.feerate w).val ≤
      (feeForWeight (updateFee p r).feerate w).val :=
  updateFee_fee_ge h w

/-- If a fee is sufficient at the new rate, it is sufficient at any lower
rate. -/
theorem feeSufficient_of_le_rate {r₁ r₂ : FeeRate} {w : Weight} {paid : Msat}
    (hr : r₁.msatPerKw ≤ r₂.msatPerKw) (h : feeSufficient r₂ w paid) :
    feeSufficient r₁ w paid :=
  feeSufficient_rate_mono hr h

/-! ## Commitment-number discipline -/

/-- **Exact counter effect of one step.**  Either this is a
`commitment_signed`, which increments only the remote counter; or a
`revoke_and_ack`, which increments only the local counter; or neither
counter changes.  The disjunction is exhaustive. -/
theorem step_commitment_numbers {c c' : Channel} {e : ProtocolEvent}
    (h : Step c e c') :
    (e = ProtocolEvent.commitmentSigned ∧
        c'.remoteCommitmentNumber = c.remoteCommitmentNumber + 1 ∧
        c'.localCommitmentNumber = c.localCommitmentNumber) ∨
      (e = ProtocolEvent.revokeAndAck ∧
        c'.localCommitmentNumber = c.localCommitmentNumber + 1 ∧
        c'.remoteCommitmentNumber = c.remoteCommitmentNumber) ∨
      (c'.localCommitmentNumber = c.localCommitmentNumber ∧
        c'.remoteCommitmentNumber = c.remoteCommitmentNumber) := by
  cases h <;> simp

/-- **Commitment numbers move only on commitment updates.**  If either
counter changes, the event is `commitment_signed` or `revoke_and_ack`; in
particular `open_channel`, `funding_locked`, `update_fee`, `shutdown`, and
`closing_signed` never move a counter. -/
theorem commitment_number_increment_only_on_update {c c' : Channel}
    {e : ProtocolEvent} (h : Step c e c')
    (hchange : c'.localCommitmentNumber ≠ c.localCommitmentNumber ∨
      c'.remoteCommitmentNumber ≠ c.remoteCommitmentNumber) :
    e = ProtocolEvent.commitmentSigned ∨ e = ProtocolEvent.revokeAndAck := by
  rcases step_commitment_numbers h with ⟨he, _, _⟩ | ⟨he, _, _⟩ | ⟨hL, hR⟩
  · exact Or.inl he
  · exact Or.inr he
  · exact False.elim (hchange.elim (fun hh => hh hL) (fun hh => hh hR))

/-- A `commitment_signed` increments exactly the remote counter. -/
theorem commitmentSigned_remote_succ {c c' : Channel}
    (h : Step c ProtocolEvent.commitmentSigned c') :
    c'.remoteCommitmentNumber = c.remoteCommitmentNumber + 1 ∧
      c'.localCommitmentNumber = c.localCommitmentNumber := by
  cases h
  exact ⟨rfl, rfl⟩

/-- A `revoke_and_ack` increments exactly the local counter. -/
theorem revokeAndAck_local_succ {c c' : Channel}
    (h : Step c ProtocolEvent.revokeAndAck c') :
    c'.localCommitmentNumber = c.localCommitmentNumber + 1 ∧
      c'.remoteCommitmentNumber = c.remoteCommitmentNumber := by
  cases h
  exact ⟨rfl, rfl⟩

/-! ## Phase progression -/

/-- **No phase regression on one step.** -/
theorem phase_progression {c c' : Channel} {e : ProtocolEvent}
    (h : Step c e c') : phaseRank c.phase ≤ phaseRank c'.phase :=
  step_phaseRank_le h

/-- **No phase regression on any finite run.** -/
theorem reachable_phase_progression {a b : Channel} (h : Reachable a b) :
    phaseRank a.phase ≤ phaseRank b.phase :=
  Reachable.phaseRank_le h

/-- The terminal phase is absorbing: a closed channel has no successor. -/
theorem closed_is_absorbing (c c' : Channel) (e : ProtocolEvent)
    (h : c.phase = ChannelPhase.closed) : ¬ Step c e c' :=
  no_step_from_closed c c' e h

/-! ## Reserve -/

/-- **Reserve non-negativity.**  Meeting the reserve makes the value above
it a natural number that reconstructs the local balance when the reserve is
added back. -/
theorem reserve_nonneg (b : Balance) (reserveSat : Nat)
    (h : reserveSatisfied b reserveSat) :
    0 ≤ reserveRemaining b reserveSat ∧
      reserveRemaining b reserveSat + reserveSat = b.localSat :=
  ⟨reserveRemaining_nonneg b reserveSat, reserveRemaining_add h⟩

/-- The reserve itself is a natural number, so no negative reserve can be
represented in the first place. -/
theorem reserve_value_nonneg (reserveSat : Nat) : 0 ≤ reserveSat :=
  Nat.zero_le _

/-- Meeting a larger reserve implies meeting a smaller one. -/
theorem reserveSatisfied_mono {b : Balance} {r₁ r₂ : Nat} (h : r₁ ≤ r₂)
    (hr : reserveSatisfied b r₂) : reserveSatisfied b r₁ :=
  Nat.le_trans h hr

/-! ## Closing and fee-update safety -/

/-- `update_fee` cannot change the lifecycle phase. -/
theorem updateFee_preserves_phase (c : Channel) (r : FeeRate) :
    (updateChannelFee c r).phase = c.phase := rfl

/-- `update_fee` cannot change the commitment counters. -/
theorem updateFee_preserves_commitment_numbers (c : Channel) (r : FeeRate) :
    (updateChannelFee c r).localCommitmentNumber = c.localCommitmentNumber ∧
      (updateChannelFee c r).remoteCommitmentNumber = c.remoteCommitmentNumber :=
  ⟨rfl, rfl⟩

end LnLean.Channel
