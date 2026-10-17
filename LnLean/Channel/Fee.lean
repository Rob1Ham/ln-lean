import LnLean.Channel.Types

/-!
# LnLean.Channel.Fee

English claim.  A commitment fee is `feerate_per_kw * weight / 1000`,
rounded down, exactly as BOLT 3 §4 (`Fee Calculation`) prescribes.  The fee
is monotone in both the feerate and the transaction weight.  `update_fee`
replaces the feerate and cannot lower the fee when the new rate is at least
the old one.  Dust is a strict inequality against the owner's dust limit;
the channel reserve is a lower bound on the owner's balance, and the
remaining value above the reserve is computed without underflow once the
reserve check holds.

BOLT sections.
* BOLT 3 §4 `Fees` (`03-transactions.md:464-576`), especially the base fee
  rule at `:503-522`: multiply `feerate_per_kw` by `weight`, divide by 1000,
  rounding down.
* BOLT 3 §5 `Dust Limits` (`03-transactions.md:583-620`).
* BOLT 2 §2 (`channel_reserve_satoshis` at `02-peer-protocol.md:734-737`,
  `:811`, `:884`) and §3 `update_fee` (`:3250-3265`).

rust-lightning anchors at `fe4900930c6bd5786ec4203274d7cf312776a5a6`.
* `lightning/src/ln/chan_utils.rs:289-298` (`commit_tx_fee_sat`, the
  floor-divided `feerate_per_kw * weight / 1000`).
* `lightning/src/ln/chan_utils.rs:275-283`
  (`COMMITMENT_TX_WEIGHT_PER_HTLC = 172`, base weight helpers).
* `lightning/src/ln/channel.rs:2800-2810` (the `update_fee` affordability
  check and reserve interaction, as quoted in BOLT 2 §3).

What is NOT modelled.
* Bitcoin Core `getdustthreshold` and its relay policy.  The dust limit is a
  negotiated parameter; `isDust` compares against it directly.
* Mempool/package-relay economics and fee estimation (BOLT 5).  The feerate
  is an input, not an oracle.
* Fee bumping (`tx_init_rbf`) and anchor child-pays-for-parent.
* The HTLC-timeout/HTLC-success fees (663/703 weights); they belong to the
  HTLC workstream.
-/

namespace LnLean.Channel

set_option autoImplicit false

open LnLean

/-! ## Fee from feerate and weight -/

/-- BOLT 3 base fee: `feerate_per_kw * weight / 1000`, rounded **down**.
`LnLean.FeeRate.fee` in `Basic.Core` rounds up; commitment fees use this
floor version because the specification says "rounding down". -/
def feeForWeight (r : FeeRate) (w : Weight) : Msat :=
  ⟨r.msatPerKw * w.val / 1000⟩

theorem feeForWeight_val (r : FeeRate) (w : Weight) :
    (feeForWeight r w).val = r.msatPerKw * w.val / 1000 := rfl

theorem feeForWeight_nonneg (r : FeeRate) (w : Weight) :
    0 ≤ (feeForWeight r w).val :=
  Nat.zero_le _

/-- Monotonicity in the feerate for a fixed weight. -/
theorem feeForWeight_mono_rate {r₁ r₂ : FeeRate} (h : r₁.msatPerKw ≤ r₂.msatPerKw)
    (w : Weight) :
    (feeForWeight r₁ w).val ≤ (feeForWeight r₂ w).val := by
  unfold feeForWeight
  exact Nat.div_le_div_right (Nat.mul_le_mul_right w.val h)

/-- Monotonicity in the weight for a fixed feerate. -/
theorem feeForWeight_mono_weight (r : FeeRate) {w₁ w₂ : Weight}
    (h : w₁.val ≤ w₂.val) :
    (feeForWeight r w₁).val ≤ (feeForWeight r w₂).val := by
  unfold feeForWeight
  exact Nat.div_le_div_right (Nat.mul_le_mul_left r.msatPerKw h)

/-- Monotonicity in both arguments at once. -/
theorem feeForWeight_mono {r₁ r₂ : FeeRate} {w₁ w₂ : Weight}
    (hr : r₁.msatPerKw ≤ r₂.msatPerKw) (hw : w₁.val ≤ w₂.val) :
    (feeForWeight r₁ w₁).val ≤ (feeForWeight r₂ w₂).val :=
  Nat.le_trans (feeForWeight_mono_rate hr w₁) (feeForWeight_mono_weight r₂ hw)

/-- A zero-weight transaction pays no fee. -/
theorem feeForWeight_zero_weight (r : FeeRate) :
    feeForWeight r ⟨0⟩ = Msat.zero := by
  simp [feeForWeight, Msat.zero]

/-! ## Sufficiency -/

/-- The fee actually paid covers the fee required by the feerate and weight. -/
def feeSufficient (r : FeeRate) (w : Weight) (paid : Msat) : Prop :=
  (feeForWeight r w).val ≤ paid.val

theorem feeSufficient_refl (r : FeeRate) (w : Weight) :
    feeSufficient r w (feeForWeight r w) :=
  Nat.le_refl _

/-- Paying more than the required fee preserves sufficiency. -/
theorem feeSufficient_mono_paid {r : FeeRate} {w : Weight} {paid paid' : Msat}
    (h : feeSufficient r w paid) (hle : paid.val ≤ paid'.val) :
    feeSufficient r w paid' :=
  Nat.le_trans h hle

/-- A higher feerate makes sufficiency harder to satisfy. -/
theorem feeSufficient_rate_mono {r₁ r₂ : FeeRate} {w : Weight} {paid : Msat}
    (hr : r₁.msatPerKw ≤ r₂.msatPerKw) (h : feeSufficient r₂ w paid) :
    feeSufficient r₁ w paid :=
  Nat.le_trans (feeForWeight_mono_rate hr w) h

/-! ## `update_fee` -/

/-- Replace the feerate in a set of channel parameters.  BOLT 2: an
`update_fee` is a replacement, not an HTLC, and applies to the commitment
transactions. -/
def updateFee (p : ChannelParams) (r : FeeRate) : ChannelParams :=
  { p with feerate := r }

theorem updateFee_feerate (p : ChannelParams) (r : FeeRate) :
    (updateFee p r).feerate = r := rfl

/-- The same replacement on the local view of a channel. -/
def updateChannelFee (c : Channel) (r : FeeRate) : Channel :=
  { c with localEndpoint :=
      { c.localEndpoint with params := updateFee c.localEndpoint.params r } }

theorem updateChannelFee_phase (c : Channel) (r : FeeRate) :
    (updateChannelFee c r).phase = c.phase := rfl

theorem updateChannelFee_localCommitmentNumber (c : Channel) (r : FeeRate) :
    (updateChannelFee c r).localCommitmentNumber = c.localCommitmentNumber := rfl

/-- Raising the feerate cannot lower the fee on a fixed weight. -/
theorem updateFee_fee_ge {p : ChannelParams} {r : FeeRate}
    (h : p.feerate.msatPerKw ≤ r.msatPerKw) (w : Weight) :
    (feeForWeight p.feerate w).val ≤ (feeForWeight (updateFee p r).feerate w).val := by
  simpa [updateFee] using feeForWeight_mono_rate h w

/-! ## Dust -/

/-- An output is dust when its satoshi value is strictly below the dust
limit of the party that owns the output. -/
def isDust (dustLimitSat : Nat) (amountSat : Nat) : Prop :=
  amountSat < dustLimitSat

/-- Millisatoshi form: BOLT 3 rounds output amounts down before comparing to
the dust limit. -/
def isDustMsat (dustLimitSat : Nat) (amount : Msat) : Prop :=
  amount.toSatFloor < dustLimitSat

theorem isDustMsat_iff (dustLimitSat : Nat) (amount : Msat) :
    isDustMsat dustLimitSat amount = isDust dustLimitSat amount.toSatFloor := rfl

/-- No value is dust against a zero limit. -/
theorem not_isDust_zero_limit (amountSat : Nat) : ¬ isDust 0 amountSat := by
  simp [isDust]

/-- A value equal to the dust limit is not dust. -/
theorem not_isDust_self (dustLimitSat : Nat) : ¬ isDust dustLimitSat dustLimitSat := by
  simp [isDust]

/-! ## Reserve -/

/-- The local balance meets the reserve it must keep. -/
def reserveSatisfied (b : Balance) (reserveSat : Nat) : Prop :=
  reserveSat ≤ b.localSat

/-- Value above the reserve.  Under `reserveSatisfied` this subtraction does
not truncate. -/
def reserveRemaining (b : Balance) (reserveSat : Nat) : Nat :=
  b.localSat - reserveSat

theorem reserveRemaining_add {b : Balance} {reserveSat : Nat}
    (h : reserveSatisfied b reserveSat) :
    reserveRemaining b reserveSat + reserveSat = b.localSat := by
  unfold reserveRemaining
  exact Nat.sub_add_cancel h

/-- The reserve check is exactly the statement that the remaining value
plus the reserve reconstructs the local balance. -/
theorem reserveSatisfied_iff {b : Balance} {reserveSat : Nat} :
    reserveSatisfied b reserveSat ↔
      reserveRemaining b reserveSat + reserveSat = b.localSat := by
  constructor
  · exact reserveRemaining_add
  · intro h
    unfold reserveSatisfied reserveRemaining at *
    omega

theorem reserveRemaining_le (b : Balance) (reserveSat : Nat) :
    reserveRemaining b reserveSat ≤ b.localSat := by
  unfold reserveRemaining
  exact Nat.sub_le _ _

theorem reserveRemaining_nonneg (b : Balance) (reserveSat : Nat) :
    0 ≤ reserveRemaining b reserveSat :=
  Nat.zero_le _

end LnLean.Channel
