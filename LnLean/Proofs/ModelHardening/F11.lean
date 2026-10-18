import LnLean.Channel.Fee
import LnLean.Channel.HTLC
import LnLean.Channel.State
import LnLean.Proofs.Channel.ReserveProps

/-!
# LnLean.Proofs.ModelHardening.F11

English claim.  This module hardens the reserve obligation `LN-CH-RESERVE`
by naming the *admissible update* that a BOLT 2 `update_add_htlc` must obey
and by proving the exact reserve arithmetic for it.

The wave-A model deliberately has no balance-changing transition:
`LnLean.Channel.State.Step` changes only the phase, the commitment counters,
and the feerate.  `LnLean.Proofs.Channel.ReserveProps` therefore isolates the
balance arithmetic of `update_add_htlc` in `spendLocalBalance` /
`spendRemoteBalance` and records the missing transition as `LN-CH-101`.
Following that precedent, this module defines a proof-level update record
(`waveF_f11_Update`) and its effect (`waveF_f11_apply`).  Nothing here changes
the model.

Main results.

1. `waveF_f11_Admissible` is the reusable update predicate.  It requires:
   the channel to be in the `normal` phase; a positive amount; a valid
   `cltv_expiry`; the sender's `htlc_minimum_msat`; the HTLC-exposure cap
   advertised by the receiving endpoint; and the sender's post-spend balance
   to stay above its reserve.  The cap is tracked per direction:
   `waveF_f11_inFlightFor c .local` (offered by us) is bounded by the
   *remote* endpoint's `max_htlc_value_in_flight_msat`, while
   `waveF_f11_inFlightFor c .remote` (received by us) is bounded by our own.
2. `waveF_f11_admissible_preserves_reserveInvariant`: if the old channel
   satisfies `ReserveInvariant`, every admissible update keeps it.  Under the
   non-truncation premise `amount <= balance` (which the reserve guard itself
   implies), `waveF_f11_apply_local_reserve_iff` and
   `waveF_f11_apply_remote_reserve_iff` show that the post-update reserve
   check is equivalent to the guard in `waveF_f11_Admissible`; the guard is
   therefore necessary as well as sufficient.
3. `waveF_f11_admissible_preserves_exposureInvariant`: admissible updates
   also preserve the per-direction HTLC-exposure bound.
4. `waveF_f11_inadmissible_update_breaks_reserve` is a mechanised violating
   update: the channel starts with a valid reserve, the update mechanically
   satisfies the normal-phase, positivity, expiry, minimum, and exposure
   conjuncts, fails the reserve guard, and the resulting channel violates
   `ReserveInvariant`.  Together with the conditional iff on the reserve guard
   this is a precise negative result, not a weakened positive one.

BOLT sections.
* BOLT 2 `update_add_htlc`: `refs/bolts/02-peer-protocol.md:2822`
  (`amount_msat > 0`), `:2823` (`amount_msat >= htlc_minimum_msat`),
  `:2824` (`cltv_expiry < 500000000`), `:2828-2831`
  (`max_htlc_value_in_flight_msat`).
* BOLT 2 reserve requirement: `refs/bolts/02-peer-protocol.md:884-896`
  (the reserve keeps a party able to pay on-chain fees).
* BOLT 3 outputs: `refs/bolts/03-transactions.md:83-353`.

rust-lightning anchors at `fe4900930c6bd5786ec4203274d7cf312776a5a6`.
* `lightning/src/ln/channel.rs:2697-2705` (`get_htlc_maximum_msat`).
* `lightning/src/ln/channel.rs:5880-5891` (an accepted HTLC must leave the
  counterparty above its reserve).
* `lightning/src/ln/channel.rs:2484-2493` (`get_available_balances`).

What is NOT modelled.
* The `update_add_htlc` constructor itself: `Step` neither moves balances nor
  appends HTLCs, so `waveF_f11_apply` is an explicit proof-level operation,
  not a `Step`.  The bridge remains obligation `LN-CH-101`.
* Onion payloads, MPP, and the fee estimator.  The exposure cap is the
  negotiated `max_htlc_value_in_flight_msat`, not a fee-adjusted value.
-/

namespace LnLean.Proofs.ModelHardening.F11

set_option autoImplicit false

open LnLean
open LnLean.Channel
open LnLean.Proofs.Channel

-- OBLIGATION: LN-WF-F11

/-! ## 1. The proof-level `update_add_htlc` record and its effect -/

/-- One pending HTLC addition, from the local endpoint's point of view.
`direction = .local` means we offer the HTLC; `.remote` means the peer offers
it.  The payment hash and expiry are carried so that the resulting `HTLC`
record is fully determined. -/
structure waveF_f11_Update where
  /-- Who offers the HTLC. -/
  direction : Direction
  /-- `amount_msat` on the wire. -/
  amount : Msat
  /-- `payment_hash` on the wire. -/
  paymentHash : PaymentHash
  /-- `cltv_expiry` on the wire. -/
  cltvExpiry : Height
deriving Repr

/-- The lifecycle state of an added HTLC: an offered HTLC is `offered`, a
received one is `received`.  Both states are pending. -/
def waveF_f11_stateFor : Direction → HTLCState
  | .local => .offered
  | .remote => .received

/-- The channel HTLC record created by an update. -/
def waveF_f11_htlcOf (u : waveF_f11_Update) : HTLC :=
  { direction := u.direction
    amount := u.amount
    paymentHash := u.paymentHash
    cltvExpiry := u.cltvExpiry
    state := waveF_f11_stateFor u.direction }

/-- Spend the sender's balance by the update amount.  This reuses the
truncated operations isolated by `ReserveProps`. -/
def waveF_f11_spendFor (b : Balance) : Direction → Nat → Balance
  | .local, amount => spendLocalBalance b amount
  | .remote, amount => spendRemoteBalance b amount

/-- The channel after the update: the sender's balance is reduced and the
pending HTLC is appended.  Only `balance` and `htlcs` change. -/
def waveF_f11_apply (c : Channel) (u : waveF_f11_Update) : Channel :=
  { c with
    balance := waveF_f11_spendFor c.balance u.direction u.amount.val
    htlcs := c.htlcs ++ [waveF_f11_htlcOf u] }

/-! ## 2. HTLC exposure, per direction -/

/-- Value currently in flight in direction `d`: the sum of the pending
(`offered`/`received`) HTLC amounts offered by that side. -/
def waveF_f11_inFlightFor (c : Channel) (d : Direction) : Nat :=
  ((c.htlcs.filter (fun h =>
      h.direction = d ∧
        (h.state = HTLCState.offered ∨ h.state = HTLCState.received))).map
    (fun h => h.amount.val)).sum

/-- The exposure cap that applies to an HTLC offered by `d`.  BOLT 2: the
receiving node advertises `max_htlc_value_in_flight_msat`, so an HTLC we
offer is capped by the remote endpoint's parameter, and one the peer offers
is capped by ours. -/
def waveF_f11_capFor (c : Channel) : Direction → Nat
  | .local => c.remoteEndpoint.params.maxHtlcValue.val
  | .remote => c.localEndpoint.params.maxHtlcValue.val

/-- The `htlc_minimum_msat` that applies to an HTLC offered by `d`, again
taken from the receiving endpoint. -/
def waveF_f11_minFor (c : Channel) : Direction → Nat
  | .local => c.remoteEndpoint.params.htlcMinimum.val
  | .remote => c.localEndpoint.params.htlcMinimum.val

/-- Both per-direction exposure bounds hold.  This is the channel-level
invariant that a sequence of admissible updates maintains. -/
def waveF_f11_ExposureInvariant (c : Channel) : Prop :=
  waveF_f11_inFlightFor c .local ≤ waveF_f11_capFor c .local ∧
    waveF_f11_inFlightFor c .remote ≤ waveF_f11_capFor c .remote

/-! ## 3. The admissible-update predicate -/

/-- **Admissible update.**  A BOLT 2 `update_add_htlc` is admissible in
channel `c` when:

* the channel is in normal operation;
* the amount is positive and at least the receiving endpoint's
  `htlc_minimum_msat`;
* `cltv_expiry` is below `MAX_CLTV_EXPIRY`;
* the total value in flight offered by this side, plus the new amount, does
  not exceed the receiving endpoint's `max_htlc_value_in_flight_msat`;
* the sender's balance, after the spend, still meets the reserve advertised
  by the peer.

The reserve conjunct is in millisatoshis: `reserve * 1000 + amount <=
balance`.  This is exactly what the division by 1000 in `reserveSatisfied`
requires; see `waveF_f11_local_spend_reserve_iff`. -/
def waveF_f11_Admissible (c : Channel) (u : waveF_f11_Update) : Prop :=
  c.phase = ChannelPhase.normal ∧
  0 < u.amount.val ∧
  u.cltvExpiry < MAX_CLTV_EXPIRY ∧
  waveF_f11_minFor c u.direction ≤ u.amount.val ∧
  waveF_f11_inFlightFor c u.direction + u.amount.val ≤
    waveF_f11_capFor c u.direction ∧
  (match u.direction with
    | .local =>
        localReserveSat c * Msat.MSAT_PER_SAT + u.amount.val ≤
          c.balance.localBalance.val
    | .remote =>
        remoteReserveSat c * Msat.MSAT_PER_SAT + u.amount.val ≤
          c.balance.remoteBalance.val)

/-! ## 4. Exact reserve arithmetic for one balance drop -/

/-- Dropping `amount` millisatoshis from the local balance leaves the local
reserve satisfied **iff** the reserve-plus-amount fits in the old balance.
The `→` direction is the safety theorem; the `←` direction shows the guard
is not stronger than necessary.  The equivalence is exact because the
division by `MSAT_PER_SAT` is floor division and `reserve * 1000` is a
multiple of 1000. -/
theorem waveF_f11_local_spend_reserve_iff (b : Balance) (reserve amount : Nat)
    (hfit : amount ≤ b.localBalance.val) :
    reserveSatisfied (spendLocalBalance b amount) reserve ↔
      reserve * Msat.MSAT_PER_SAT + amount ≤ b.localBalance.val := by
  show reserve ≤ (b.localBalance.val - amount) / Msat.MSAT_PER_SAT ↔
    reserve * Msat.MSAT_PER_SAT + amount ≤ b.localBalance.val
  rw [Nat.le_div_iff_mul_le (by decide : 0 < Msat.MSAT_PER_SAT)]
  omega

/-- Symmetric exact arithmetic for the remote balance.  The hypothesis
`amount ≤ remoteBalance` is the non-truncation premise: without it the
truncated subtraction can hide a reserve violation, exactly as in
`ReserveProps.committed_update_preserves_ledger` versus its `_of_le`
correction. -/
theorem waveF_f11_remote_spend_reserve_iff (b : Balance) (reserve amount : Nat)
    (hfit : amount ≤ b.remoteBalance.val) :
    reserve ≤ (spendRemoteBalance b amount).remoteSat ↔
      reserve * Msat.MSAT_PER_SAT + amount ≤ b.remoteBalance.val := by
  show reserve ≤ (b.remoteBalance.val - amount) / Msat.MSAT_PER_SAT ↔
    reserve * Msat.MSAT_PER_SAT + amount ≤ b.remoteBalance.val
  rw [Nat.le_div_iff_mul_le (by decide : 0 < Msat.MSAT_PER_SAT)]
  omega

/-- A local spend leaves the remote balance, hence the remote satoshi
balance, untouched. -/
@[simp] theorem waveF_f11_spendLocal_remoteSat (b : Balance) (amount : Nat) :
    (spendLocalBalance b amount).remoteSat = b.remoteSat := rfl

/-- A remote spend leaves the local balance, hence the local satoshi
balance, untouched. -/
@[simp] theorem waveF_f11_spendRemote_localSat (b : Balance) (amount : Nat) :
    (spendRemoteBalance b amount).localSat = b.localSat := rfl

/-- The post-update local reserve check is exactly the local guard of
`waveF_f11_Admissible`. -/
theorem waveF_f11_apply_local_reserve_iff {c : Channel} {u : waveF_f11_Update}
    (hd : u.direction = .local)
    (hfit : u.amount.val ≤ c.balance.localBalance.val) :
    reserveSatisfied (waveF_f11_apply c u).balance
        (localReserveSat (waveF_f11_apply c u)) ↔
      localReserveSat c * Msat.MSAT_PER_SAT + u.amount.val ≤
        c.balance.localBalance.val := by
  simp [waveF_f11_apply, waveF_f11_spendFor, hd, localReserveSat,
    waveF_f11_local_spend_reserve_iff, hfit]

/-- The post-update remote reserve check is exactly the remote guard of
`waveF_f11_Admissible`. -/
theorem waveF_f11_apply_remote_reserve_iff {c : Channel} {u : waveF_f11_Update}
    (hd : u.direction = .remote)
    (hfit : u.amount.val ≤ c.balance.remoteBalance.val) :
    remoteReserveSat (waveF_f11_apply c u) ≤
        (waveF_f11_apply c u).balance.remoteSat ↔
      remoteReserveSat c * Msat.MSAT_PER_SAT + u.amount.val ≤
        c.balance.remoteBalance.val := by
  simp [waveF_f11_apply, waveF_f11_spendFor, hd, remoteReserveSat,
    waveF_f11_remote_spend_reserve_iff, hfit]

/-! ## 5. Preservation theorems -/

/-- **Reserve preservation.**  Every admissible update preserves
`ReserveInvariant`, whichever side offers the HTLC.  The untouched side is
unchanged, and the spent side is covered by the exact guards of
`waveF_f11_Admissible`. -/
theorem waveF_f11_admissible_preserves_reserveInvariant
    {c : Channel} {u : waveF_f11_Update}
    (hadm : waveF_f11_Admissible c u) (hinv : ReserveInvariant c) :
    ReserveInvariant (waveF_f11_apply c u) := by
  rcases hadm with ⟨_, _, _, _, _, hres⟩
  rcases hinv with ⟨hloc, hrem⟩
  cases hd : u.direction
  · simp only [hd] at hres
    have hfit : u.amount.val ≤ c.balance.localBalance.val := by omega
    refine ⟨?_, ?_⟩
    · exact (waveF_f11_apply_local_reserve_iff hd hfit).2 hres
    · simpa [waveF_f11_apply, waveF_f11_spendFor, hd, ReserveInvariant,
        reserveSatisfied, remoteReserveSat] using hrem
  · simp only [hd] at hres
    have hfit : u.amount.val ≤ c.balance.remoteBalance.val := by omega
    refine ⟨?_, ?_⟩
    · simpa [waveF_f11_apply, waveF_f11_spendFor, hd, ReserveInvariant,
        reserveSatisfied, localReserveSat] using hloc
    · exact (waveF_f11_apply_remote_reserve_iff hd hfit).2 hres

/-- Appending a pending HTLC adds exactly its amount to the in-flight value
of its direction. -/
theorem waveF_f11_inFlightFor_apply (c : Channel) (u : waveF_f11_Update) :
    waveF_f11_inFlightFor (waveF_f11_apply c u) u.direction =
      waveF_f11_inFlightFor c u.direction + u.amount.val := by
  cases hd : u.direction <;>
    simp [waveF_f11_apply, waveF_f11_inFlightFor, waveF_f11_htlcOf,
      waveF_f11_stateFor, hd, List.filter_append]

/-- Appending an HTLC in one direction leaves the other direction's
in-flight value unchanged. -/
theorem waveF_f11_inFlightFor_apply_of_ne (c : Channel) (u : waveF_f11_Update)
    {d : Direction} (hne : d ≠ u.direction) :
    waveF_f11_inFlightFor (waveF_f11_apply c u) d =
      waveF_f11_inFlightFor c d := by
  cases hd : u.direction <;> cases hdd : d <;>
    simp_all [waveF_f11_apply, waveF_f11_inFlightFor, waveF_f11_htlcOf,
      waveF_f11_stateFor, List.filter_append]

/-- The exposure cap does not change under an update. -/
theorem waveF_f11_capFor_apply (c : Channel) (u : waveF_f11_Update)
    (d : Direction) :
    waveF_f11_capFor (waveF_f11_apply c u) d = waveF_f11_capFor c d := by
  cases hd : u.direction <;> cases d <;> rfl

/-- **Exposure preservation.**  An admissible update keeps both
per-direction in-flight values under their caps.  The offered direction uses
the admissibility guard; the other direction is untouched. -/
theorem waveF_f11_admissible_preserves_exposureInvariant
    {c : Channel} {u : waveF_f11_Update}
    (hadm : waveF_f11_Admissible c u)
    (hinv : waveF_f11_ExposureInvariant c) :
    waveF_f11_ExposureInvariant (waveF_f11_apply c u) := by
  rcases hadm with ⟨_, _, _, _, hexp, _⟩
  rcases hinv with ⟨hloc, hrem⟩
  cases hd : u.direction
  · simp only [hd] at hexp
    have hsame := waveF_f11_inFlightFor_apply c u
    simp only [hd] at hsame
    refine ⟨?_, ?_⟩
    · rw [hsame, waveF_f11_capFor_apply]
      exact hexp
    · rw [waveF_f11_inFlightFor_apply_of_ne (c := c) (u := u) (d := .remote)
          (by simp [hd]), waveF_f11_capFor_apply]
      exact hrem
  · simp only [hd] at hexp
    have hsame := waveF_f11_inFlightFor_apply c u
    simp only [hd] at hsame
    refine ⟨?_, ?_⟩
    · rw [waveF_f11_inFlightFor_apply_of_ne (c := c) (u := u) (d := .local)
          (by simp [hd]), waveF_f11_capFor_apply]
      exact hloc
    · rw [hsame, waveF_f11_capFor_apply]
      exact hexp

/-! ## 6. A mechanised violating update -/

/-- **Violating update.**  There is a channel with a valid reserve and an
update that meets the normal-phase, positivity, expiry, minimum, and exposure
checks but breaks the reserve guard; the resulting channel violates
`ReserveInvariant`.  Concretely the local balance is 2000 sat, the local
reserve is 1000 sat, and the offered HTLC is 1500 sat: the post-spend
balance is 500 sat, below the reserve.  This is the negative half of the
`LN-CH-RESERVE` statement, mechanised rather than asserted: the statement
lists the five passing conjuncts explicitly, so it is not merely `¬
Admissible`. -/
theorem waveF_f11_inadmissible_update_breaks_reserve :
    ∃ (c : Channel) (u : waveF_f11_Update),
      ReserveInvariant c ∧
      c.phase = ChannelPhase.normal ∧
      0 < u.amount.val ∧
      u.cltvExpiry < MAX_CLTV_EXPIRY ∧
      waveF_f11_minFor c u.direction ≤ u.amount.val ∧
      waveF_f11_inFlightFor c u.direction + u.amount.val ≤
        waveF_f11_capFor c u.direction ∧
      ¬ waveF_f11_Admissible c u ∧
      ¬ ReserveInvariant (waveF_f11_apply c u) := by
  let p : ChannelParams :=
    { dustLimitSat := 546
      channelReserveSat := 1000
      toSelfDelay := 144
      maxHtlcValue := ⟨1000000000⟩
      htlcMinimum := ⟨1000⟩
      feerate := ⟨253⟩
      anchorOutputs := false }
  let e : Endpoint :=
    { nodeId := ⟨ByteArray.empty⟩
      fundingPubKey := ⟨ByteArray.empty⟩
      paymentBasepoint := ⟨ByteArray.empty⟩
      delayedPaymentBasepoint := ⟨ByteArray.empty⟩
      params := p }
  let c : Channel :=
    { channelId := ⟨ByteArray.empty⟩
      funding := ⟨ByteArray.empty, 0⟩
      fundingValue := ⟨1000000000⟩
      localEndpoint := e
      remoteEndpoint := e
      phase := ChannelPhase.normal
      localCommitmentNumber := 0
      remoteCommitmentNumber := 0
      balance := { localBalance := ⟨2000000⟩, remoteBalance := ⟨998000000⟩ }
      htlcs := [] }
  let u : waveF_f11_Update :=
    { direction := Direction.local
      amount := ⟨1500000⟩
      paymentHash := ⟨ByteArray.empty⟩
      cltvExpiry := 0 }
  refine ⟨c, u, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · show localReserveSat c ≤ c.balance.localSat
      decide
    · show remoteReserveSat c ≤ c.balance.remoteSat
      decide
  · rfl
  · decide
  · decide
  · show (1000 : Nat) ≤ 1500000
    decide
  · show (0 : Nat) + 1500000 ≤ 1000000000
    decide
  · intro hadm
    obtain ⟨-, -, -, -, -, hres⟩ := hadm
    simp only [c, e, u, p, localReserveSat, Msat.MSAT_PER_SAT] at hres
    omega
  · intro hinv
    obtain ⟨hl, -⟩ := hinv
    simp only [c, e, u, p, waveF_f11_apply, waveF_f11_spendFor,
      localReserveSat, reserveSatisfied, Balance.localSat, Msat.toSatFloor,
      Msat.MSAT_PER_SAT, spendLocalBalance] at hl
    omega

end LnLean.Proofs.ModelHardening.F11
