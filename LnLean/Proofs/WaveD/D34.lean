import LnLean.Security.Invariants
import LnLean.Security.Model
import LnLean.Bitcoin.Laws
import LnLean.Channel.Laws
import LnLean.Routing.Laws
import LnLean.Channel.Fee
import LnLean.Channel.Penalty
import LnLean.Proofs.Security.ThreatModelProps

/-!
# LnLean.Proofs.WaveD.D34

English claim (catalog `LN-SEC-005`).  A penalty transaction remains
economical under the modelled fee spike.

## What the model provides

`LnLean.Security.Model.FeeEnvironment` models the adversary's fee capability
as a base feerate, a height-indexed feerate `atHeight`, and an optional
`spikeAt : Height`.  `LnLean.Security.ThreatModel.penaltyNet r w v` is the net
reward, in millisatoshis, of a penalty of weight `w` at feerate `r` when `v`
is at stake:

`penaltyNet r w v = v - FeeRate.fee r w`,

where `FeeRate.fee` is the ceiling fee of `LnLean.Basic.Core`.  The predicate
`penaltyEconomical r w v` below is `0 < penaltyNet r w v`, i.e. the fee is
strictly below the value at stake.

## Result

The *unconditional* reading

`∀ env h w v, env.spikeAt = some h → 0 < penaltyNet (env.atHeight h) w v`

is **false** in the current model: `FeeEnvironment.atHeight` is an arbitrary
function and `spikeAt` carries no bound, so the adversary may set a feerate
whose required fee exceeds any value at stake.  This is mechanized as
`waveD_d34_unconditional_claim_false` and, for a concrete penalty returned by
`penaltyValid`, as `waveD_d34_spike_breaks_valid_penalty`.

The strongest true statement proved here is the bounded-spike form
`waveD_d34_economical_under_bounded_spike`: if the entire fee schedule (the
base rate and every `atHeight`) lies below a break-even feerate `rMax` at
which the penalty is still economical, then the penalty is economical at every
height, in particular at the recorded spike height
(`waveD_d34_economical_at_spike`).  Equivalently, the missing economic
liveness hypothesis `LN-PENALTY-ECON` is exactly a bound on the adversary's
feerate schedule relative to the penalty weight and the value at stake.

The break-even feerate is characterized arithmetically by
`waveD_d34_economical_iff_rate_bound`.

## Concrete valid penalty

Section 4 constructs a literal `RevocationScheme`, `RevokedCommitment`,
`PenaltyTx`, and `PenaltyWitness` that satisfy `penaltyValid` (breach, both
old outputs spent, one sweep output, timely confirmation), with a sweep of
1500 sat and a 500 sat penalty fee.  Under a modelled spike to 1,500,001
msat/kw at weight 1000, the required fee is 1,500,001 msat against a value at
stake of 1,500,000 msat: the net reward is non-positive and even
`feeSufficient` fails.  `penaltyValid` does not require fee sufficiency, so
validity does not imply economics.

## BOLT and LDK anchors

* BOLT 5 §"Revoked Transaction Close Handling",
  `refs/bolts/05-onchain.md:510-559`: the revocation key resolves the old
  outputs, and a single penalty transaction may resolve all of them.
* BOLT 5 §"Penalty Transactions Weight Calculation",
  `refs/bolts/05-onchain.md:582-610`: `to_local_penalty_input_weight = 324`,
  the optional `to_remote` input adds `272`, and the non-witness part is
  `4 * 53 + 2` weight units.  `bolt5PenaltyWeightTwoOutputs` records the
  resulting 810 for the two-input sweep; the theorems keep the weight
  parametric because the model's `PenaltyTx` has no weight field.
* BOLT 5 `security_delay` policy, `refs/bolts/05-onchain.md:552`: a node must
  actively fee-bump; the model has no fee-bumping strategy.
* LDK `lightning/src/chain/chaininterface.rs:350`: the `FeeEstimator` /
  `get_est_sat_per_1000_weight` interface through which a fee spike reaches
  the channel.  The feerate is an input, not an oracle, exactly as in
  `FeeEnvironment`.

## What is NOT modelled

* No link between `RevokedCommitment.penaltyFee` (an `Int` satoshi amount) and
  `FeeEnvironment`; `penaltyValid` does not require the fee to be sufficient.
* No weight field or weight function on `PenaltyTx`; `w` is a parameter.
* No BTC/fiat exchange rate, so "economical" means positive millisatoshi net
  reward, not a profitable breach.
* No mempool/relay policy, RBF, child-pays-for-parent, package relay,
  pinning, anchor output fee bumping, or spike duration.
* No bound on `FeeEnvironment.atHeight` or on `spikeAt`.  Adding that bound
  is the model change that would make the catalog claim unconditional.
-/

namespace LnLean.Proofs.WaveD.D34

set_option autoImplicit false

open LnLean
open LnLean.Security (FeeEnvironment)
open LnLean.Security.ThreatModel (penaltyNet)
open LnLean.Channel
open LnLean.Bitcoin

-- OBLIGATION: LN-WD-D34

/-! ## 1. Penalty economics and fee monotonicity -/

/-- A penalty of weight `w` is economical at feerate `r` when its net reward
is strictly positive, i.e. the required fee is strictly below the value at
stake.  This is `0 < penaltyNet r w atStake` unfolded. -/
def penaltyEconomical (r : FeeRate) (w : Weight) (atStake : Msat) : Prop :=
  0 < penaltyNet r w atStake

/-- Economical is exactly "the ceiling fee is below the value at stake". -/
theorem waveD_d34_economical_iff_fee_lt (r : FeeRate) (w : Weight)
    (v : Msat) :
    penaltyEconomical r w v ↔ (FeeRate.fee r w).val < v.val := by
  unfold penaltyEconomical penaltyNet
  constructor <;> intro h <;> omega

/-- The ceiling fee is monotone in the feerate. -/
theorem waveD_d34_fee_mono_rate {r₁ r₂ : FeeRate}
    (h : r₁.msatPerKw ≤ r₂.msatPerKw) (w : Weight) :
    (FeeRate.fee r₁ w).val ≤ (FeeRate.fee r₂ w).val := by
  unfold FeeRate.fee
  exact Nat.div_le_div_right
    (Nat.add_le_add_right (Nat.mul_le_mul_right w.val h) 999)

/-- The ceiling fee is monotone in the transaction weight. -/
theorem waveD_d34_fee_mono_weight (r : FeeRate) {w₁ w₂ : Weight}
    (h : w₁.val ≤ w₂.val) :
    (FeeRate.fee r w₁).val ≤ (FeeRate.fee r w₂).val := by
  unfold FeeRate.fee
  exact Nat.div_le_div_right
    (Nat.add_le_add_right (Nat.mul_le_mul_left r.msatPerKw h) 999)

/-- A penalty that is economical at a high feerate is economical at every
lower feerate.  This is the monotonicity step behind the bounded-spike
theorem. -/
theorem waveD_d34_economical_mono_rate {r₁ r₂ : FeeRate} {w : Weight}
    {v : Msat} (hr : r₁.msatPerKw ≤ r₂.msatPerKw)
    (h : penaltyEconomical r₂ w v) :
    penaltyEconomical r₁ w v := by
  rw [waveD_d34_economical_iff_fee_lt] at *
  exact Nat.lt_of_le_of_lt (waveD_d34_fee_mono_rate hr w) h

/-- Sharp break-even form: a penalty is economical exactly when the exact
fee product `r * w` is below `1000 * v` by at least the 999-msat ceiling
remainder.  This is the arithmetic threshold an `LN-PENALTY-ECON` bound would
have to respect. -/
theorem waveD_d34_economical_iff_rate_bound (r : FeeRate) (w : Weight)
    (v : Msat) :
    penaltyEconomical r w v ↔
      r.msatPerKw * w.val + 999 < v.val * 1000 := by
  rw [waveD_d34_economical_iff_fee_lt]
  unfold FeeRate.fee
  exact Nat.div_lt_iff_lt_mul (by decide : 0 < 1000)

/-! ## 2. The modelled fee spike -/

/-- The feerate actually in force: the spike height's rate when the
environment records a spike, and the base rate otherwise. -/
def effectiveRate (env : FeeEnvironment) : FeeRate :=
  match env.spikeAt with
  | some h => env.atHeight h
  | none => env.base

/-- A whole adversary fee schedule lies below a candidate break-even
feerate.  This is the explicit `LN-PENALTY-ECON` bound: it covers both the
base feerate and every height-indexed feerate the adversary may select. -/
def FeeScheduleBounded (env : FeeEnvironment) (rMax : FeeRate) : Prop :=
  env.base.msatPerKw ≤ rMax.msatPerKw ∧
    ∀ h : Height, (env.atHeight h).msatPerKw ≤ rMax.msatPerKw

/-- The effective rate respects a schedule bound. -/
theorem waveD_d34_effectiveRate_le (env : FeeEnvironment) (rMax : FeeRate)
    (hb : FeeScheduleBounded env rMax) :
    (effectiveRate env).msatPerKw ≤ rMax.msatPerKw := by
  rcases hb with ⟨hbase, hall⟩
  unfold effectiveRate
  cases env.spikeAt with
  | none => exact hbase
  | some h => exact hall h

/-- At a recorded spike height the effective rate is the spike rate. -/
theorem waveD_d34_effectiveRate_eq_spike (env : FeeEnvironment)
    {h : Height} (hs : env.spikeAt = some h) :
    effectiveRate env = env.atHeight h := by
  simp [effectiveRate, hs]

/-- **The penalty remains economical under a bounded fee spike.**  If every
rate the adversary can select, including the spike, is at most a break-even
rate `rMax`, and the penalty is economical at `rMax`, then it is economical at
the rate actually in force. -/
theorem waveD_d34_economical_under_bounded_spike (env : FeeEnvironment)
    (rMax : FeeRate) (w : Weight) (v : Msat)
    (hb : FeeScheduleBounded env rMax)
    (h : penaltyEconomical rMax w v) :
    penaltyEconomical (effectiveRate env) w v :=
  waveD_d34_economical_mono_rate
    (waveD_d34_effectiveRate_le env rMax hb) h

/-- The bound applies at every height, not only at the recorded spike: the
base rate and every `atHeight` are economical. -/
theorem waveD_d34_economical_throughout_bounded_schedule
    (env : FeeEnvironment) (rMax : FeeRate) (w : Weight) (v : Msat)
    (hb : FeeScheduleBounded env rMax)
    (h : penaltyEconomical rMax w v) :
    penaltyEconomical env.base w v ∧
      ∀ h : Height, penaltyEconomical (env.atHeight h) w v := by
  refine ⟨waveD_d34_economical_mono_rate hb.1 h, ?_⟩
  intro h'
  exact waveD_d34_economical_mono_rate (hb.2 h') h

/-- **At the modelled spike.**  The same conclusion specialised to the height
named by `spikeAt`, which is the form of the catalog claim. -/
theorem waveD_d34_economical_at_spike (env : FeeEnvironment) (rMax : FeeRate)
    (w : Weight) (v : Msat) {spikeHeight : Height}
    (hb : FeeScheduleBounded env rMax) (hs : env.spikeAt = some spikeHeight)
    (hecon : penaltyEconomical rMax w v) :
    penaltyEconomical (env.atHeight spikeHeight) w v := by
  simpa [waveD_d34_effectiveRate_eq_spike env hs] using
    waveD_d34_economical_under_bounded_spike env rMax w v hb hecon

/-! ## 3. The unconditional claim is false -/

/-- **Any value at stake can be made uneconomical by an admissible spike.**
For an arbitrary `v`, take a spike to `(v + 1) * 1000` msat/kw at weight 1:
the ceiling fee is exactly `v + 1`, so the net reward is `-1`.  Nothing in
`FeeEnvironment` excludes this schedule. -/
theorem waveD_d34_spike_can_break_economy (v : Msat) :
    ∃ (env : FeeEnvironment) (w : Weight) (h : Height),
      env.spikeAt = some h ∧ ¬ penaltyEconomical (env.atHeight h) w v := by
  refine ⟨{ base := ⟨0⟩
            atHeight := fun _ => ⟨(v.val + 1) * 1000⟩
            spikeAt := some 0 }, ⟨1⟩, 0, rfl, ?_⟩
  intro hpos
  rw [waveD_d34_economical_iff_fee_lt] at hpos
  have hfee : (FeeRate.fee (⟨(v.val + 1) * 1000⟩ : FeeRate)
      (⟨1⟩ : Weight)).val = v.val + 1 := by
    show ((v.val + 1) * 1000 * 1 + 999) / 1000 = v.val + 1
    rw [Nat.mul_one]
    exact Nat.div_eq_of_lt_le (by omega) (by omega)
  rw [hfee] at hpos
  omega

/-- **The catalog claim is not true unconditionally.**  There is no theorem
of the form "every modelled spike leaves the penalty economical"; the
quantifier is refuted by the schedule constructed above. -/
theorem waveD_d34_unconditional_claim_false :
    ¬ ∀ (env : FeeEnvironment) (h : Height) (w : Weight) (v : Msat),
        env.spikeAt = some h → penaltyEconomical (env.atHeight h) w v := by
  intro hall
  rcases waveD_d34_spike_can_break_economy ⟨0⟩ with ⟨env, w, h, hs, hne⟩
  exact hne (hall env h w ⟨0⟩ hs)

/-! ## 4. A concrete valid penalty that the spike breaks -/

/-- A valid 33-byte public key used by the concrete revocation scheme.  The
scheme below is a witness that the `RevocationScheme` interface is
inhabited; it is not a cryptographic instantiation. -/
def d34ZeroKey : PubKey :=
  ⟨ByteArray.mk (List.replicate 33 (0 : UInt8)).toArray⟩

theorem waveD_d34_zeroKey_valid : d34ZeroKey.Valid := by
  unfold d34ZeroKey PubKey.Valid
  decide

/-- A concrete `RevocationScheme` satisfying the model interface:
`pointOf` is the zero key, `derivePubkey` returns the point's own bytes, and
`derivePrivkey` returns the zero key.  `consistent` holds definitionally and
`injective_point` holds because a point is its key. -/
def d34Scheme : RevocationScheme where
  pointOf := fun _ => ⟨d34ZeroKey⟩
  pointOf_valid := fun _ => waveD_d34_zeroKey_valid
  derivePubkey := fun _ p => ⟨⟨p.key.bytes⟩⟩
  derivePrivkey := fun _ _ => ⟨d34ZeroKey⟩
  consistent := by
    intro base s
    rfl
  injective_point := by
    intro base p q h
    have h1 : (⟨⟨p.key.bytes⟩⟩ : RevocationKey).key =
        (⟨⟨q.key.bytes⟩⟩ : RevocationKey).key :=
      congrArg RevocationKey.key h
    have h2 : p.key.bytes = q.key.bytes := congrArg PubKey.bytes h1
    cases p with
    | mk pk =>
      cases q with
      | mk qk =>
        simp only [PerCommitmentPoint.mk.injEq]
        cases pk
        cases qk
        cases h2
        rfl

/-- A revoked commitment with 1000 sat on each old main output, a 500 sat
penalty fee, and therefore a 1500 sat sweep. -/
def d34Commitment : RevokedCommitment where
  number := 0
  currentNumber := 1
  toLocal := ⟨ByteArray.empty, 0⟩
  toRemote := ⟨ByteArray.empty, 1⟩
  toLocalValue := 1000
  toRemoteValue := 1000
  breachHeight := 0
  penaltyFee := 500

/-- The two-input, one-output penalty transaction for `d34Commitment`. -/
def d34Penalty : PenaltyTx where
  inputLocal := d34Commitment.toLocal
  inputRemote := d34Commitment.toRemote
  sweep := ⟨1500, Bitcoin.Data.Script.empty⟩

/-- The revocation witness.  The abstract scheme's `consistent` field makes
the key conjunct hold for every secret, so the secret is unconstrained. -/
def d34Witness : PenaltyWitness where
  secret := ⟨ByteArray.empty⟩
  revocationBase := d34ZeroKey

/-- The value at stake, converted from the sweep's satoshis to millisatoshis:
1500 sat = 1,500,000 msat. -/
def d34AtStake : Msat := Msat.ofSat d34Penalty.sweep.value.toNat

/-- The 500 sat penalty fee as a millisatoshi amount: 500,000 msat. -/
def d34PaidMsat : Msat := Msat.ofSat d34Commitment.penaltyFee.toNat

theorem waveD_d34_atStake_val : d34AtStake.val = 1500000 := by
  simp [d34AtStake, d34Penalty, Msat.ofSat, Msat.MSAT_PER_SAT]

theorem waveD_d34_paid_val : d34PaidMsat.val = 500000 := by
  simp [d34PaidMsat, d34Commitment, Msat.ofSat, Msat.MSAT_PER_SAT]

/-- The concrete penalty is valid: the commitment is revoked (`0 < 1`), the
witness derives the revocation key, both old outputs are spent, the sweep is
`1000 + 1000 - 500 = 1500`, and the confirmation at height 0 is inside the
window 1. -/
theorem waveD_d34_valid_penalty :
    penaltyValid d34Scheme d34Commitment d34Penalty d34Witness 0 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [breachDetected, d34Commitment]
  · exact deriveRevocationPubkey_consistent d34Scheme
      d34Witness.revocationBase d34Witness.secret
  · simp [penaltySpendsBoth, d34Penalty, d34Commitment]
  · simp [d34Penalty, d34Commitment]
  · simp [timelyL1Confirmation, d34Commitment]

/-- The concrete penalty pays a positive fee (500 sat) and sweeps 1500 sat. -/
theorem waveD_d34_valid_penalty_values :
    d34Commitment.penaltyFee = 500 ∧ d34Penalty.sweep.value = 1500 :=
  ⟨rfl, rfl⟩

/-- **A valid penalty that the modelled spike makes uneconomical.**  The
environment spikes at height 0 to 1,500,001 msat/kw.  At weight 1000 the
required fee is 1,500,001 msat, which is above the 1,500,000 msat at stake and
above the 500,000 msat the transaction pays.  Hence the net reward is
non-positive and the fee is insufficient, even though `penaltyValid` holds. -/
theorem waveD_d34_spike_breaks_valid_penalty :
    ∃ (env : FeeEnvironment) (w : Weight),
      env.spikeAt = some 0 ∧
      penaltyValid d34Scheme d34Commitment d34Penalty d34Witness 0 1 ∧
      ¬ penaltyEconomical (env.atHeight 0) w d34AtStake ∧
      ¬ feeSufficient (env.atHeight 0) w d34PaidMsat := by
  refine ⟨{ base := ⟨0⟩
            atHeight := fun _ => ⟨d34AtStake.val + 1⟩
            spikeAt := some 0 },
          ⟨1000⟩, rfl, waveD_d34_valid_penalty, ?_, ?_⟩
  · intro hpos
    rw [waveD_d34_economical_iff_fee_lt] at hpos
    rw [waveD_d34_atStake_val] at hpos
    have hfee : (FeeRate.fee (⟨1500000 + 1⟩ : FeeRate) (⟨1000⟩ : Weight)).val
        = 1500001 := by
      show (1500001 * 1000 + 999) / 1000 = 1500001
      exact Nat.div_eq_of_lt_le (by omega) (by omega)
    rw [hfee] at hpos
    omega
  · intro hsuff
    unfold feeSufficient at hsuff
    rw [waveD_d34_paid_val] at hsuff
    rw [waveD_d34_atStake_val] at hsuff
    have hfee : (feeForWeight (⟨1500000 + 1⟩ : FeeRate) (⟨1000⟩ : Weight)).val
        = 1500001 := by
      unfold feeForWeight
      show 1500001 * 1000 / 1000 = 1500001
      exact Nat.div_eq_of_lt_le (by omega) (by omega)
    rw [hfee] at hsuff
    omega

/-! ## 5. BOLT 5 weight anchor -/

/-- BOLT 5's two-input penalty weight: `to_local` penalty input 324, the
optional `to_remote` input 272, and the 53 non-witness bytes plus 2-byte
witness header (`4 * 53 + 2 = 214`), for 810 weight units.  This is a
constant check only; the model's `PenaltyTx` has no weight field, so the
economic theorems keep `w` parametric. -/
def bolt5PenaltyWeightTwoOutputs : Weight :=
  ⟨324 + 272 + (4 * 53 + 2)⟩

/-- The BOLT 5 two-input penalty weight evaluates to 810. -/
theorem waveD_d34_bolt5_penalty_weight :
    bolt5PenaltyWeightTwoOutputs.val = 810 := by
  decide

end LnLean.Proofs.WaveD.D34
