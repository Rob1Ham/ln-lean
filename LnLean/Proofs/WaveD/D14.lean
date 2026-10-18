import LnLean.Channel.Commitment
import LnLean.Channel.Fee
import LnLean.Channel.HTLC
import LnLean.Channel.HTLCLaws
import LnLean.Channel.Laws
import LnLean.Channel.Penalty
import LnLean.Channel.Revocation
import LnLean.Channel.State
import LnLean.Channel.Types
import LnLean.Proofs.Channel.ReserveProps

/-!
# LnLean.Proofs.WaveD.D14

English claim (catalogue `LN-CH-006`).  HTLC exposure and channel reserve
bounds are respected by admissible updates.

BOLT 2 §Bounding exposure to trimmed in-flight HTLCs
(`refs/bolts/02-peer-protocol.md:2726-2770`) bounds the value of trimmed
in-flight HTLCs by `max_dust_htlc_exposure_msat`.  BOLT 2 §2
(`refs/bolts/02-peer-protocol.md:734-737`, `:884`) defines the channel
reserve as the minimum direct balance the peer must keep, and
`refs/bolts/02-peer-protocol.md:811`, `:869` require the reserve to lie
between the dust limit and the channel value.  LDK checks the peer's reserve
against the channel value at `lightning/src/ln/channel.rs:4223`.

What this module proves, and what it cannot prove about `State.Step`:

1. `LnLean.Channel.Reserve.bounds`: for the policy layer defined below, an
   **admissible** `update_add_htlc` — positive amount, in-flight cap,
   opening reserve bound, current reserve invariant, offer-side reserve
   guard, and dust-exposure headroom on both commitments — preserves the
   opening reserve bound, the reserve invariant, and the dust-exposure bound.
   The balance of the offering side is actually debited by the update, so the
   reserve invariant is not a re-statement of an unchanged balance.
2. The exposure arithmetic is BOLT 3's: an HTLC contributes to exposure
   exactly when its commitment output would be trimmed
   (`amount_msat / 1000 - second_stage_fee < dust_limit_satoshis`), and it
   contributes its full millisatoshi amount.  `exposureOn_append` and
   `exposureOn_mono_fees` are the two structural facts.
3. `State.Step` in the current model changes neither `balance` nor `htlcs`
   (only phase, commitment counters, and the feerate).  Therefore the
   literal catalogue claim about "admissible updates" cannot be a theorem
   about `Step`: it neither enforces nor repairs either bound.  The two
   mechanized counterexamples below exhibit a legal `Step` from a channel
   outside the reserve bound and from a channel above the exposure bound, and
   `waveD_d14_step_*` prove the violations persist.

The obligation id is LN-WD-D14.

The only gaps are model gaps, not proof gaps: `Channel` has no
`max_dust_htlc_exposure_msat` field, no `update_add_htlc` constructor in
`Step`, and no link from `feerate` to the HTLC-timeout/success fees.  The
policy layer below supplies them explicitly and is proved unconditionally;
the report names each missing field.
-/

-- OBLIGATION: LN-WD-D14

namespace LnLean.Channel

namespace Reserve

set_option autoImplicit false

open LnLean
open LnLean.Proofs.Channel
  (localReserveSat remoteReserveSat ReserveInvariant ReserveWithinCapacity
   spendLocalBalance spendRemoteBalance
   spendLocal_preserves_reserve spendRemote_preserves_remoteReserve)

/-! ## Dust-exposure policy

`ChannelParams` in `LnLean.Channel.Types` does not carry
`max_dust_htlc_exposure_msat`, so the policy is an explicit parameter.  The
two second-stage fees are also parameters here: `Channel.Commitment` exposes
the base commitment fee only, and `State.Step.updateFee` changes `feerate`
without deriving the HTLC fees from it. -/

/-- The node-policy parameter of BOLT 2 §Bounding exposure to trimmed
in-flight HTLCs, plus the two BOLT 3 second-stage fees needed to decide
whether an HTLC output is trimmed. -/
structure ExposurePolicy where
  /-- `max_dust_htlc_exposure_msat`. -/
  maxDustHtlcExposureMsat : Nat
  /-- The HTLC-timeout second-stage fee, charged to an offered HTLC. -/
  timeoutFeeSat : Nat
  /-- The HTLC-success second-stage fee, charged to a received HTLC. -/
  successFeeSat : Nat
deriving Repr, DecidableEq, BEq

/-- The direction of an HTLC on a commitment whose holder is `holder`.
`Direction` in the model is always relative to the local endpoint, so on the
remote commitment every direction flips. -/
def offeredDirection (holder : Direction) (h : HTLC) : Direction :=
  match holder with
  | .local => h.direction
  | .remote => h.direction.flip

/-- HTLCs that are still live, in the Boolean form needed by `List.filter`.
`HTLC.isPending` in `Types` is the corresponding `Prop`.  Only a live HTLC
can have a commitment output and hence contribute to dust exposure. -/
def isPendingB (h : HTLC) : Bool :=
  h.state == HTLCState.offered || h.state == HTLCState.received

/-- The exposure contribution of one HTLC in millisatoshis.  The BOLT 3
trimming test is `amount_msat / 1000 - second_stage_fee < dust_limit`; a
trimmed HTLC has no output, so its whole amount becomes a miner fee if the
commitment is broadcast.  A settled HTLC has already left the commitment and
contributes nothing.  This mirrors `LnLean.Channel.isDustHTLC` for the
`Channel.htlcs` representation (`Types.HTLC`, not `HTLC.HTLCRecord`). -/
def dustContribution (dir : Direction) (dustLimit timeout success : Nat)
    (h : HTLC) : Nat :=
  if isPendingB h then
    if decide (h.amountSat - secondStageFee dir timeout success < dustLimit) then
      h.amount.val
    else
      0
  else
    0

/-- The dust exposure of a list of HTLCs on one named commitment. -/
def exposureOn : Direction → Nat → Nat → Nat → List HTLC → Nat
  | _, _, _, _, [] => 0
  | holder, dust, timeout, success, h :: hs =>
      dustContribution (offeredDirection holder h) dust timeout success h +
        exposureOn holder dust timeout success hs

/-- Dust exposure of the local commitment.  BOLT 3 uses the dust limit set by
the transaction owner, i.e. `localEndpoint.params.dustLimitSat`. -/
def localExposure (c : Channel) (p : ExposurePolicy) : Nat :=
  exposureOn .local c.localEndpoint.params.dustLimitSat p.timeoutFeeSat
    p.successFeeSat c.htlcs

/-- Dust exposure of the remote commitment (the remote endpoint owns that
commitment, hence its dust limit and flipped HTLC directions). -/
def remoteExposure (c : Channel) (p : ExposurePolicy) : Nat :=
  exposureOn .remote c.remoteEndpoint.params.dustLimitSat p.timeoutFeeSat
    p.successFeeSat c.htlcs

/-- `max_dust_htlc_exposure_msat` is respected on both commitment
transactions. -/
def ExposureBounded (c : Channel) (p : ExposurePolicy) : Prop :=
  localExposure c p ≤ p.maxDustHtlcExposureMsat ∧
    remoteExposure c p ≤ p.maxDustHtlcExposureMsat

/-! ## Structural exposure lemmas -/

/-- Appending one HTLC adds exactly its contribution to the exposure. -/
theorem exposureOn_append (holder : Direction) (dust timeout success : Nat)
    (hs : List HTLC) (h : HTLC) :
    exposureOn holder dust timeout success (hs ++ [h]) =
      exposureOn holder dust timeout success hs +
        dustContribution (offeredDirection holder h) dust timeout success h := by
  induction hs with
  | nil => simp [exposureOn]
  | cons x xs ih =>
      simp only [List.cons_append, exposureOn]
      rw [ih]
      omega

/-- An HTLC never contributes more than its own millisatoshi amount. -/
theorem dustContribution_le_amount (dir : Direction) (dust timeout success : Nat)
    (h : HTLC) :
    dustContribution dir dust timeout success h ≤ h.amount.val := by
  unfold dustContribution
  split
  · split <;> simp
  · simp

/-- Raising either second-stage fee can only turn more HTLCs into dust, so
the exposure is monotone in the fees.  This is the arithmetic behind BOLT 2's
warning that a higher `feerate_per_kw` may trim multiple HTLCs. -/
theorem dustContribution_mono_fees {dir : Direction} {dust t₁ t₂ s₁ s₂ : Nat}
    (ht : t₁ ≤ t₂) (hs : s₁ ≤ s₂) (h : HTLC) :
    dustContribution dir dust t₁ s₁ h ≤ dustContribution dir dust t₂ s₂ h := by
  have hfee : secondStageFee dir t₁ s₁ ≤ secondStageFee dir t₂ s₂ := by
    cases dir <;> simp_all [secondStageFee]
  unfold dustContribution
  cases hp : isPendingB h
  · simp
  · by_cases hold : decide (h.amountSat - secondStageFee dir t₁ s₁ < dust) = true
    · have hnew : decide (h.amountSat - secondStageFee dir t₂ s₂ < dust) = true := by
        rw [decide_eq_true_iff] at hold ⊢
        exact Nat.lt_of_le_of_lt (Nat.sub_le_sub_left hfee h.amountSat) hold
      simp [hold, hnew]
    · simp [hold]

/-- Pointwise exposure monotonicity in the second-stage fees. -/
theorem exposureOn_mono_fees (holder : Direction) (dust : Nat)
    {t₁ t₂ s₁ s₂ : Nat} (ht : t₁ ≤ t₂) (hs : s₁ ≤ s₂) (hs' : List HTLC) :
    exposureOn holder dust t₁ s₁ hs' ≤ exposureOn holder dust t₂ s₂ hs' := by
  induction hs' with
  | nil => simp [exposureOn]
  | cons x xs ih =>
      simp only [exposureOn]
      exact Nat.add_le_add (dustContribution_mono_fees ht hs x) ih

/-! ## The reserve guard of one update -/

/-- `update_add_htlc` debits the offering side.  After the debit the sender
must still hold its reserve: BOLT 2 §2 says the reserve is specified by the
peer's `channel_reserve_satoshis`, so a local offer is checked against the
remote endpoint's parameter and vice versa.  Amounts are compared in
millisatoshis (`reserve * 1000`). -/
def offeringReserveGuard (c : Channel) (h : HTLC) : Prop :=
  match h.direction with
  | .local =>
      localReserveSat c * Msat.MSAT_PER_SAT + h.amount.val ≤
        c.balance.localBalance.val
  | .remote =>
      remoteReserveSat c * Msat.MSAT_PER_SAT + h.amount.val ≤
        c.balance.remoteBalance.val

/-- The exposure headroom required by BOLT 2 before adding `h`: on each
commitment, the current dust balance plus the new HTLC must not exceed
`max_dust_htlc_exposure_msat`. -/
def AddWithinExposure (c : Channel) (p : ExposurePolicy) (h : HTLC) : Prop :=
  dustContribution (offeredDirection .local h) c.localEndpoint.params.dustLimitSat
      p.timeoutFeeSat p.successFeeSat h + localExposure c p ≤
        p.maxDustHtlcExposureMsat ∧
    dustContribution (offeredDirection .remote h) c.remoteEndpoint.params.dustLimitSat
      p.timeoutFeeSat p.successFeeSat h + remoteExposure c p ≤
        p.maxDustHtlcExposureMsat

/-- The pending subset of the channel's HTLC list. -/
def pendingHtlcs (hs : List HTLC) : List HTLC :=
  hs.filter isPendingB

/-- Total value in flight, in millisatoshis. -/
def inFlightMsat (hs : List HTLC) : Nat :=
  ((pendingHtlcs hs).map (fun h => h.amount.val)).sum

/-- `max_htlc_value_in_flight_msat` is advertised by the receiving side, so a
local offer is capped by the remote endpoint's parameter and vice versa
(BOLT 2 `02-peer-protocol.md:739-741`). -/
def htlcCap (c : Channel) (h : HTLC) : Nat :=
  match h.direction with
  | .local => c.remoteEndpoint.params.maxHtlcValue.val
  | .remote => c.localEndpoint.params.maxHtlcValue.val

/-- An admissible `update_add_htlc` in the sense of this module: the BOLT 2
sending-node guards (positive amount and in-flight cap), the opening reserve
bound, the two current invariants, the offer-side reserve guard, and the
dust-exposure headroom.  All of these are policy preconditions in LDK; none
of them is a field of `LnLean.Channel.Channel`, which is why the theorem is
stated over this predicate rather than over `State.Step`. -/
def AdmissibleAdd (c : Channel) (p : ExposurePolicy) (h : HTLC) : Prop :=
  0 < h.amount.val ∧
    inFlightMsat c.htlcs + h.amount.val ≤ htlcCap c h ∧
    ReserveWithinCapacity c ∧
    ReserveInvariant c ∧
    offeringReserveGuard c h ∧
    AddWithinExposure c p h

/-! ## The modelled update -/

/-- `update_add_htlc`: debit the offering side and append the HTLC.  This
mirrors `LnLean.Channel.HTLC.addHTLC`'s positive-amount/in-flight/cltv guards
at the channel level; the cltv check is not needed for the reserve or
exposure bounds and is therefore not repeated in `AdmissibleAdd`. -/
def applyAddHtlc (c : Channel) (h : HTLC) : Channel :=
  { c with
    balance :=
      match h.direction with
      | .local => spendLocalBalance c.balance h.amount.val
      | .remote => spendRemoteBalance c.balance h.amount.val
    htlcs := c.htlcs ++ [h] }

@[simp] theorem applyAddHtlc_htlcs (c : Channel) (h : HTLC) :
    (applyAddHtlc c h).htlcs = c.htlcs ++ [h] := rfl

/-- A local offer that passes the reserve guard keeps the local reserve after
the debit (the arithmetic core, reusing the wave-A proof). -/
theorem applyAddHtlc_local_reserve {c : Channel} {h : HTLC}
    (hd : h.direction = .local)
    (hguard : localReserveSat c * Msat.MSAT_PER_SAT + h.amount.val ≤
      c.balance.localBalance.val) :
    reserveSatisfied (applyAddHtlc c h).balance (localReserveSat c) := by
  have h := spendLocal_preserves_reserve (b := c.balance)
    (reserve := localReserveSat c) (amountMsat := h.amount.val) hguard
  simpa [applyAddHtlc, hd] using h

/-- The symmetric statement for a received HTLC. -/
theorem applyAddHtlc_remote_reserve {c : Channel} {h : HTLC}
    (hd : h.direction = .remote)
    (hguard : remoteReserveSat c * Msat.MSAT_PER_SAT + h.amount.val ≤
      c.balance.remoteBalance.val) :
    remoteReserveSat c ≤ (applyAddHtlc c h).balance.remoteSat := by
  have h := spendRemote_preserves_remoteReserve (b := c.balance)
    (reserve := remoteReserveSat c) (amountMsat := h.amount.val) hguard
  simpa [applyAddHtlc, hd] using h

/-- The update preserves the reserve invariant on both sides: the offering
side by the guard, the other side because its balance is untouched. -/
theorem applyAddHtlc_reserveInvariant {c : Channel} {h : HTLC}
    (hres : ReserveInvariant c) (hguard : offeringReserveGuard c h) :
    ReserveInvariant (applyAddHtlc c h) := by
  rcases hres with ⟨hl, hr⟩
  by_cases hd : h.direction = .local
  · have hg : localReserveSat c * Msat.MSAT_PER_SAT + h.amount.val ≤
        c.balance.localBalance.val := by
      simpa [offeringReserveGuard, hd] using hguard
    refine ⟨applyAddHtlc_local_reserve hd hg, ?_⟩
    simpa [applyAddHtlc, hd, spendLocalBalance, Balance.remoteSat,
      remoteReserveSat] using hr
  · have hd' : h.direction = .remote := by
      cases hdir : h.direction <;> simp_all
    have hg : remoteReserveSat c * Msat.MSAT_PER_SAT + h.amount.val ≤
        c.balance.remoteBalance.val := by
      simpa [offeringReserveGuard, hd'] using hguard
    refine ⟨?_, applyAddHtlc_remote_reserve hd' hg⟩
    simpa [applyAddHtlc, hd', spendRemoteBalance, Balance.localSat,
      localReserveSat, reserveSatisfied] using hl

/-- The opening capacity bound is unaffected by an update (neither the
funding value nor a reserve parameter changes). -/
theorem applyAddHtlc_reserveWithinCapacity (c : Channel) (h : HTLC)
    (hc : ReserveWithinCapacity c) :
    ReserveWithinCapacity (applyAddHtlc c h) := by
  simpa [ReserveWithinCapacity, localReserveSat, remoteReserveSat,
    Channel.fundingValueSat, applyAddHtlc] using hc

/-- Exposure of the local commitment after appending one HTLC. -/
theorem localExposure_applyAddHtlc (c : Channel) (p : ExposurePolicy) (h : HTLC) :
    localExposure (applyAddHtlc c h) p =
      localExposure c p +
        dustContribution (offeredDirection .local h) c.localEndpoint.params.dustLimitSat
          p.timeoutFeeSat p.successFeeSat h := by
  simp [localExposure, applyAddHtlc, exposureOn_append]

/-- Exposure of the remote commitment after appending one HTLC. -/
theorem remoteExposure_applyAddHtlc (c : Channel) (p : ExposurePolicy) (h : HTLC) :
    remoteExposure (applyAddHtlc c h) p =
      remoteExposure c p +
        dustContribution (offeredDirection .remote h) c.remoteEndpoint.params.dustLimitSat
          p.timeoutFeeSat p.successFeeSat h := by
  simp [remoteExposure, applyAddHtlc, exposureOn_append]

/-- The exposure headroom already implies the current exposure bound, since a
contribution is a natural number. -/
theorem exposureBounded_of_addWithinExposure {c : Channel} {p : ExposurePolicy}
    {h : HTLC} (hadm : AddWithinExposure c p h) :
    ExposureBounded c p := by
  rcases hadm with ⟨hl, hr⟩
  exact ⟨by omega, by omega⟩

/-- An admissible update preserves the dust-exposure bound on both
commitments. -/
theorem applyAddHtlc_exposureBounded {c : Channel} {p : ExposurePolicy}
    {h : HTLC} (hexp : ExposureBounded c p) (hadm : AddWithinExposure c p h) :
    ExposureBounded (applyAddHtlc c h) p := by
  rcases hexp with ⟨hl, hr⟩
  rcases hadm with ⟨hdl, hdr⟩
  constructor
  · rw [localExposure_applyAddHtlc]
    omega
  · rw [remoteExposure_applyAddHtlc]
    omega

/-! ## Projections of admissibility -/

theorem admissible_amount_pos {c : Channel} {p : ExposurePolicy} {h : HTLC}
    (hadm : AdmissibleAdd c p h) : 0 < h.amount.val :=
  hadm.1

theorem admissible_inFlight {c : Channel} {p : ExposurePolicy} {h : HTLC}
    (hadm : AdmissibleAdd c p h) :
    inFlightMsat c.htlcs + h.amount.val ≤ htlcCap c h :=
  hadm.2.1

theorem admissible_reserveWithinCapacity {c : Channel} {p : ExposurePolicy}
    {h : HTLC} (hadm : AdmissibleAdd c p h) :
    ReserveWithinCapacity c :=
  hadm.2.2.1

theorem admissible_reserveInvariant {c : Channel} {p : ExposurePolicy}
    {h : HTLC} (hadm : AdmissibleAdd c p h) :
    ReserveInvariant c :=
  hadm.2.2.2.1

theorem admissible_reserveGuard {c : Channel} {p : ExposurePolicy}
    {h : HTLC} (hadm : AdmissibleAdd c p h) :
    offeringReserveGuard c h :=
  hadm.2.2.2.2.1

theorem admissible_exposure {c : Channel} {p : ExposurePolicy} {h : HTLC}
    (hadm : AdmissibleAdd c p h) :
    AddWithinExposure c p h :=
  hadm.2.2.2.2.2

/-! ## The bound theorem -/

/-- **`LN-CH-006`.**  An admissible `update_add_htlc` respects the channel
reserve bounds and the `max_dust_htlc_exposure_msat` bound: after the update
both reserves still fit the channel value, both balances still meet the
reserve specified by the peer, and both commitments' dust exposure stays
within the configured maximum.

The debit is real: `applyAddHtlc` subtracts the HTLC amount from the offering
side's balance, and `applyAddHtlc_local_reserve` / `applyAddHtlc_remote_reserve`
are where the reserve arithmetic happens.  Admissibility includes the
pre-state invariants and the opening capacity bound because the model's
`Channel` record carries no enforcement of them; the theorem is not a
re-statement of an unchanged state. -/
theorem bounds {c : Channel} {p : ExposurePolicy} {h : HTLC}
    (hadm : AdmissibleAdd c p h) :
    ReserveWithinCapacity (applyAddHtlc c h) ∧
      ReserveInvariant (applyAddHtlc c h) ∧
      ExposureBounded (applyAddHtlc c h) p := by
  have hcap := admissible_reserveWithinCapacity hadm
  have hres := admissible_reserveInvariant hadm
  have hguard := admissible_reserveGuard hadm
  have hexp := admissible_exposure hadm
  exact ⟨applyAddHtlc_reserveWithinCapacity c h hcap,
    applyAddHtlc_reserveInvariant hres hguard,
    applyAddHtlc_exposureBounded (exposureBounded_of_addWithinExposure hexp) hexp⟩

end Reserve

end LnLean.Channel

/-! ## The limits of `State.Step` -/

namespace LnLean.Proofs.WaveD.D14

set_option autoImplicit false

open LnLean
open LnLean.Channel
open LnLean.Channel.Reserve
open LnLean.Proofs.Channel
  (localReserveSat remoteReserveSat ReserveInvariant ReserveWithinCapacity)

/-- `LN-CH-006` under its exact catalogue name. -/
theorem waveD_d14_bounds {c : Channel} {p : ExposurePolicy} {h : HTLC}
    (hadm : AdmissibleAdd c p h) :
    ReserveWithinCapacity (applyAddHtlc c h) ∧
      ReserveInvariant (applyAddHtlc c h) ∧
      ExposureBounded (applyAddHtlc c h) p :=
  LnLean.Channel.Reserve.bounds hadm

/-- The post-update reserve bound in its two-balance form. -/
theorem waveD_d14_reserve_headroom {c : Channel} {p : ExposurePolicy} {h : HTLC}
    (hadm : AdmissibleAdd c p h) :
    localReserveSat (applyAddHtlc c h) ≤ (applyAddHtlc c h).balance.localSat ∧
      remoteReserveSat (applyAddHtlc c h) ≤ (applyAddHtlc c h).balance.remoteSat :=
  (LnLean.Channel.Reserve.bounds hadm).2.1

/-- Raising either second-stage fee cannot lower the dust exposure of a
commitment.  This is the formal core of BOLT 2's remark that an increased
`feerate_per_kw` can trim several HTLCs at once; the model has no field
linking `feerate` to these fees, so the fees are the explicit policy inputs. -/
theorem waveD_d14_exposure_mono_fees (c : Channel) {p₁ p₂ : ExposurePolicy}
    (ht : p₁.timeoutFeeSat ≤ p₂.timeoutFeeSat)
    (hs : p₁.successFeeSat ≤ p₂.successFeeSat) :
    localExposure c p₁ ≤ localExposure c p₂ ∧
      remoteExposure c p₁ ≤ remoteExposure c p₂ :=
  ⟨exposureOn_mono_fees .local c.localEndpoint.params.dustLimitSat ht hs c.htlcs,
   exposureOn_mono_fees .remote c.remoteEndpoint.params.dustLimitSat ht hs c.htlcs⟩

/-! ### `Step` preserves the balance and the HTLC list -/

/-- No `State.Step` changes the channel balance. -/
theorem waveD_d14_step_balance {c c' : Channel} {e : ProtocolEvent}
    (h : Step c e c') : c'.balance = c.balance := by
  cases h <;> rfl

/-- No `State.Step` changes the HTLC list, in particular no step adds an
HTLC.  `update_add_htlc` is not a constructor of `Step`. -/
theorem waveD_d14_step_htlcs {c c' : Channel} {e : ProtocolEvent}
    (h : Step c e c') : c'.htlcs = c.htlcs := by
  cases h <;> rfl

/-- The local reserve parameter is unchanged by every step. -/
theorem waveD_d14_step_localReserveSat {c c' : Channel} {e : ProtocolEvent}
    (h : Step c e c') : localReserveSat c' = localReserveSat c := by
  cases h <;> rfl

/-- The remote reserve parameter is unchanged by every step. -/
theorem waveD_d14_step_remoteReserveSat {c c' : Channel} {e : ProtocolEvent}
    (h : Step c e c') : remoteReserveSat c' = remoteReserveSat c := by
  cases h <;> rfl

/-- Consequently `Step` preserves the reserve invariant exactly. -/
theorem waveD_d14_step_reserve_iff {c c' : Channel} {e : ProtocolEvent}
    (h : Step c e c') : ReserveInvariant c' ↔ ReserveInvariant c := by
  have hb : c'.balance = c.balance := waveD_d14_step_balance h
  have hl : localReserveSat c' = localReserveSat c :=
    waveD_d14_step_localReserveSat h
  have hr : remoteReserveSat c' = remoteReserveSat c :=
    waveD_d14_step_remoteReserveSat h
  simp [ReserveInvariant, hb, hl, hr]

/-- A legal step cannot repair a reserve violation. -/
theorem waveD_d14_step_cannot_repair_reserve {c c' : Channel}
    {e : ProtocolEvent} (h : Step c e c') (hc : ¬ ReserveInvariant c) :
    ¬ ReserveInvariant c' := by
  intro h'
  exact hc ((waveD_d14_step_reserve_iff h).1 h')

/-- `Step` preserves the reserve invariant (because it preserves balances and
reserve parameters). -/
theorem waveD_d14_step_preserves_reserve {c c' : Channel} {e : ProtocolEvent}
    (h : Step c e c') (hc : ReserveInvariant c) : ReserveInvariant c' :=
  (waveD_d14_step_reserve_iff h).2 hc

/-- The dust exposure of both commitments is unchanged by every legal step. -/
theorem waveD_d14_step_exposure {c c' : Channel} {e : ProtocolEvent}
    (h : Step c e c') (p : ExposurePolicy) :
    localExposure c' p = localExposure c p ∧
      remoteExposure c' p = remoteExposure c p := by
  have hh : c'.htlcs = c.htlcs := waveD_d14_step_htlcs h
  have hdl : c'.localEndpoint.params.dustLimitSat =
      c.localEndpoint.params.dustLimitSat := by
    cases h <;> rfl
  have hdr : c'.remoteEndpoint.params.dustLimitSat =
      c.remoteEndpoint.params.dustLimitSat := by
    cases h <;> rfl
  constructor <;> simp [localExposure, remoteExposure, hh, hdl, hdr]

/-- A legal step cannot repair an exposure violation either. -/
theorem waveD_d14_step_cannot_repair_exposure {c c' : Channel}
    {e : ProtocolEvent} (h : Step c e c') (p : ExposurePolicy)
    (hc : ¬ ExposureBounded c p) : ¬ ExposureBounded c' p := by
  intro h'
  rcases waveD_d14_step_exposure h p with ⟨hl, hr⟩
  rcases h' with ⟨h1, h2⟩
  exact hc ⟨by omega, by omega⟩

/-! ### Mechanized counterexamples to the claim about `Step`

`Step` is the model's only transition relation.  These witnesses show that
"admissible updates respect the bounds" is false if "admissible" is read as
"there is a legal `Step`": `commitment_signed` is legal from a normal-phase
channel with zero balances and positive reserves, and from a channel whose
single offered HTLC is dust while the exposure maximum is zero. -/

private def demoPubKey : PubKey := ⟨ByteArray.empty⟩

private def demoParams (reserve dust : Nat) : ChannelParams :=
  { dustLimitSat := dust
    channelReserveSat := reserve
    toSelfDelay := 144
    maxHtlcValue := ⟨1000000⟩
    htlcMinimum := ⟨1⟩
    feerate := ⟨253⟩
    anchorOutputs := false }

private def demoEndpoint (reserve dust : Nat) : Endpoint :=
  { nodeId := demoPubKey
    fundingPubKey := demoPubKey
    paymentBasepoint := demoPubKey
    delayedPaymentBasepoint := demoPubKey
    params := demoParams reserve dust }

private def demoChannel : Channel :=
  { channelId := ChannelId.zero
    funding := { txid := ByteArray.empty, index := 0 }
    fundingValue := ⟨1000000⟩
    localEndpoint := demoEndpoint 1000 546
    remoteEndpoint := demoEndpoint 1000 546
    phase := ChannelPhase.normal
    localCommitmentNumber := 0
    remoteCommitmentNumber := 0
    balance := { localBalance := ⟨0⟩, remoteBalance := ⟨0⟩ }
    htlcs := [] }

private def afterCommitmentSigned (c : Channel) : Channel :=
  { c with remoteCommitmentNumber := c.remoteCommitmentNumber + 1 }

private def demoDustHtlc : HTLC :=
  { direction := .local
    amount := ⟨1⟩
    paymentHash := ⟨ByteArray.empty⟩
    cltvExpiry := 0
    state := .offered }

private def demoPolicy : ExposurePolicy :=
  { maxDustHtlcExposureMsat := 0
    timeoutFeeSat := 0
    successFeeSat := 0 }

private def demoExposedChannel : Channel :=
  { demoChannel with htlcs := [demoDustHtlc] }

private theorem demoChannel_not_reserve : ¬ ReserveInvariant demoChannel := by
  intro hb
  have h1 : localReserveSat demoChannel ≤ demoChannel.balance.localSat := hb.1
  have hl : localReserveSat demoChannel = 1000 := rfl
  have hs : demoChannel.balance.localSat = 0 := rfl
  rw [hl, hs] at h1
  omega

private theorem demoHtlc_is_dust_local :
    decide (demoDustHtlc.amountSat -
      secondStageFee (offeredDirection .local demoDustHtlc) 0 0 < 546) = true := by
  decide

private theorem demoHtlc_is_dust_remote :
    decide (demoDustHtlc.amountSat -
      secondStageFee (offeredDirection .remote demoDustHtlc) 0 0 < 546) = true := by
  decide

private theorem demoHtlc_contribution_local :
    dustContribution (offeredDirection .local demoDustHtlc) 546 0 0 demoDustHtlc = 1 := by
  have hp : isPendingB demoDustHtlc = true := by decide
  unfold dustContribution
  rw [hp, demoHtlc_is_dust_local]
  rfl

private theorem demoHtlc_contribution_remote :
    dustContribution (offeredDirection .remote demoDustHtlc) 546 0 0 demoDustHtlc = 1 := by
  have hp : isPendingB demoDustHtlc = true := by decide
  unfold dustContribution
  rw [hp, demoHtlc_is_dust_remote]
  rfl

private theorem demoExposedChannel_not_exposure :
    ¬ ExposureBounded demoExposedChannel demoPolicy := by
  intro hb
  have hl : localExposure demoExposedChannel demoPolicy = 1 := by
    simp [localExposure, exposureOn, demoExposedChannel, demoChannel, demoEndpoint,
      demoParams, demoPolicy, demoHtlc_contribution_local]
  have hmax : demoPolicy.maxDustHtlcExposureMsat = 0 := rfl
  have h1 := hb.1
  rw [hl, hmax] at h1
  omega

/-- **Reserve bound counterexample.**  A normal-phase channel whose balances
are both zero while both reserves are 1000 sat has a legal
`commitment_signed` step, and the successor still violates the reserve.  So
`Step` does not enforce the reserve bound. -/
theorem waveD_d14_counterexample_step_ignores_reserve :
    ∃ (c c' : Channel) (e : ProtocolEvent),
      Step c e c' ∧ ¬ ReserveInvariant c' := by
  refine ⟨demoChannel, afterCommitmentSigned demoChannel,
    ProtocolEvent.commitmentSigned, Step.commitmentSigned demoChannel rfl, ?_⟩
  intro h'
  exact demoChannel_not_reserve
    ((waveD_d14_step_reserve_iff (Step.commitmentSigned demoChannel rfl)).1 h')

/-- **Exposure bound counterexample.**  A normal-phase channel with one dust
HTLC of 1 msat and `max_dust_htlc_exposure_msat = 0` has a legal
`commitment_signed` step, and the successor is still above the maximum.  So
`Step` does not enforce the exposure bound either. -/
theorem waveD_d14_counterexample_step_ignores_exposure :
    ∃ (c c' : Channel) (e : ProtocolEvent) (p : ExposurePolicy),
      Step c e c' ∧ ¬ ExposureBounded c p ∧ ¬ ExposureBounded c' p := by
  refine ⟨demoExposedChannel, afterCommitmentSigned demoExposedChannel,
    ProtocolEvent.commitmentSigned, demoPolicy,
    Step.commitmentSigned demoExposedChannel rfl, demoExposedChannel_not_exposure, ?_⟩
  intro h'
  rcases waveD_d14_step_exposure
    (Step.commitmentSigned demoExposedChannel rfl) demoPolicy with ⟨hl, hr⟩
  exact demoExposedChannel_not_exposure (by
    constructor
    · rw [← hl]; exact h'.1
    · rw [← hr]; exact h'.2)

end LnLean.Proofs.WaveD.D14
