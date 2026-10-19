import LnLean.Channel.State
import LnLean.Proofs.Payment.LiquidityProps

/-!
# LnLean.Proofs.Wave14.LiquidityInFlight

English claim.  BOLT 2's `max_htlc_value_in_flight_msat` bounds the value
**offered by one sender**, not the sum of both directions
(`refs/bolts/02-peer-protocol.md:739-742`).  It also counts only HTLCs that
are still in flight: once an HTLC is `fulfilled`, `failed`, or `removed`, its
value is no longer part of the bucket (`refs/bolts/02-peer-protocol.md:2829-2834`).
The Wave-13 review recorded the existing pooled predicate as G02/G03: the old
`pendingHtlcValueOf` sums both directions and `AffordableAdd.withinInFlight`
uses that pooled total, so a channel can reject an add that BOLT 2 admits.

This module is **additive**.  It does not redefine `pendingHtlcValueOf`,
`AffordableAdd`, `AffordableAdd.withinInFlight`, `LiquidityProps.addHtlc?`,
`LiquidityProps.sumByDirection`, `D14.inFlightMsat`, or `E37.pendingValue`.
Those declarations keep their existing meaning and their retained
counterexamples.  Instead it introduces:

* `pendingHtlcValueInDirection` — the pending-only, one-direction sum;
* `WithinInFlightDirectional` — the directional BOLT 2 cap test;
* `AffordableAddDirectional` — the full additive add guard: the existing
  correct positive / `cltv_expiry` / `htlc_minimum_msat` / offered-balance /
  reserve guards (the reserve side comes from the already-correct
  `State.offeringReserveSat`) plus the directional pending-only cap.

Delivered results.

1. `directional_inFlight_separates` — concrete witness: a remote-offered
   pending 600 msat HTLC plus a new local 500 msat add under a 1000 msat
   receiver cap.  The directional test accepts; the old pooled test rejects.
2. `terminal_htlc_excluded_witness` — a settled 600 msat local HTLC plus a
   500 msat local add under the same cap: directional accepts, while the old
   direction sum (`LiquidityProps.sumByDirection`, which ignores state)
   rejects.  This is the G03 separation.
3. `directionalAdmission_separates_pooled` — the same state also satisfies
   every field of the **full** new guard while the old `AffordableAdd` fails,
   so the new predicate is inhabited and strictly weaker on a concrete state.
4. `updateAddHtlc_preserves_directionalCap` — an add admitted by
   `AffordableAddDirectional` keeps the directional cap after
   `Channel.updateAddHtlc`.
5. `affordableAdd_toDirectional` — every old `AffordableAdd` is also accepted
   by the new guard.  The old pooled predicate is therefore **conservative but
   not BOLT-2-faithful**: it implies the directional bound, while the
   separation witness shows the converse fails.

Boundaries (deliberately not claimed).

* The carrier is the `Channel` record of `LnLean.Channel.Types`.  It has no
  wire encoding, no commitment-signature round, no fee/dust deduction, and no
  per-HTLC `max_accepted_htlcs` counter.  The directional cap is a value cap
  on this record only.
* `AffordableAddDirectional` is a predicate on the pre-state.  It is not wired
  into `UpdateStep`; doing so would change an existing relation and is left to
  an integrator decision.
* `LiquidityProps.addHtlc?` still uses `sumByDirection`, still counts terminal
  HTLCs, and still omits the positive / CLTV / minimum guards.  This module
  documents that divergence; it does not silently repair that existing
  consumer.
* No reserve-endpoint repair is made here.  The reserve direction is a
  separate Wave-14 lane; this module uses `State.offeringReserveSat`, which is
  already the receiver's advertised reserve.

BOLT and LDK anchors.
* BOLT 2 `refs/bolts/02-peer-protocol.md:730-742` (reserve and
  `max_htlc_value_in_flight_msat` semantics).
* BOLT 2 `refs/bolts/02-peer-protocol.md:2822-2852` (add guards).
* LDK `refs/rust-lightning/lightning/src/ln/channel.rs:5854-5870` (the
  in-flight check filters `!htlc.outbound`).
-/

namespace LnLean.Proofs.Wave14.LiquidityInFlight

set_option autoImplicit false

open LnLean
open LnLean.Channel

/-! ## Pending-only, directional value -/

/-- The directional sum, as a list function.  This is the form used by the
append and compatibility lemmas. -/
def pendingHtlcValueInDirectionList (dir : Direction) (hs : List HTLC) : Nat :=
  ((hs.filter (fun h =>
      (h.state = HTLCState.offered ∨ h.state = HTLCState.received) ∧
      h.direction = dir)).map
    (fun h => h.amount.val)).sum

/-- The pending HTLC value in one direction, in millisatoshis.  Only the two
pre-settlement states (`offered`, `received`) contribute; `fulfilled`,
`failed`, and `removed` entries are excluded.  `dir` is the **offering**
direction: `.local` means the local endpoint offered the HTLC, `.remote`
means the remote endpoint offered it. -/
def pendingHtlcValueInDirection (c : Channel) (dir : Direction) : Nat :=
  pendingHtlcValueInDirectionList dir c.htlcs

theorem pendingHtlcValueInDirection_eq_list (c : Channel) (dir : Direction) :
    pendingHtlcValueInDirection c dir =
      pendingHtlcValueInDirectionList dir c.htlcs := rfl

/-- The directional BOLT 2 in-flight cap.  `receiverParams c dir` is the
endpoint that receives the offered HTLC, so for a local offer it is the
remote endpoint's advertised `max_htlc_value_in_flight_msat`. -/
def WithinInFlightDirectional (c : Channel) (dir : Direction)
    (amount : Msat) : Prop :=
  pendingHtlcValueInDirection c dir + amount.val ≤
    (receiverParams c dir).maxHtlcValue.val

/-- The full additive add guard.  It keeps every guard of `AffordableAdd`
that the existing declarations express correctly, and replaces only the
pooled in-flight test by the directional pending-only test.

The reserve field is `offeringReserveSat`, i.e. the reserve advertised by the
**receiver**; that side is already correct in `State.lean`.  This module does
not introduce another reserve definition. -/
structure AffordableAddDirectional (c : Channel) (dir : Direction)
    (amount : Msat) (cltvExpiry : Height) : Prop where
  /-- The amount is strictly positive. -/
  positive : 0 < amount.val
  /-- BOLT 2's `cltv_expiry` bound. -/
  cltvBelowMaximum : cltvExpiry < MAX_CLTV_EXPIRY
  /-- The receiver's `htlc_minimum_msat` is respected. -/
  atLeastHtlcMinimum : (receiverParams c dir).htlcMinimum.val ≤ amount.val
  /-- The amount fits the offering side's settled balance. -/
  fitsOffered : amount.val ≤ (offeredBalance c dir).val
  /-- The offering side stays above the receiver's advertised reserve. -/
  leavesReserve :
    offeringReserveSat c dir * Msat.MSAT_PER_SAT + amount.val ≤
      (offeredBalance c dir).val
  /-- The receiver's directional pending-only in-flight bound is respected. -/
  withinInFlightDirectional : WithinInFlightDirectional c dir amount

/-! ## Basic list arithmetic -/

theorem pendingHtlcValueInDirectionList_append_singleton
    (dir : Direction) (hs : List HTLC) (h : HTLC) :
    pendingHtlcValueInDirectionList dir (hs ++ [h]) =
      pendingHtlcValueInDirectionList dir hs +
        (if (h.state = HTLCState.offered ∨ h.state = HTLCState.received) ∧
            h.direction = dir then h.amount.val else 0) := by
  unfold pendingHtlcValueInDirectionList
  rw [List.filter_append, List.map_append, List.sum_append]
  by_cases hp : (h.state = HTLCState.offered ∨
      h.state = HTLCState.received) ∧ h.direction = dir
  · simp [hp]
  · simp [hp]

/-- The HTLC record appended by `updateAddHtlc`. -/
def addHtlcRecord (dir : Direction) (amount : Msat) (ph : PaymentHash)
    (cltv : Height) : HTLC :=
  { direction := dir
    amount := amount
    paymentHash := ph
    cltvExpiry := cltv
    state := match dir with
      | .local => .offered
      | .remote => .received }

theorem addHtlcRecord_direction (dir : Direction) (amount : Msat)
    (ph : PaymentHash) (cltv : Height) :
    (addHtlcRecord dir amount ph cltv).direction = dir := rfl

theorem addHtlcRecord_state (dir : Direction) (amount : Msat)
    (ph : PaymentHash) (cltv : Height) :
    (addHtlcRecord dir amount ph cltv).state = HTLCState.offered ∨
      (addHtlcRecord dir amount ph cltv).state = HTLCState.received := by
  cases dir <;> simp [addHtlcRecord]

theorem addHtlcRecord_isPending (dir : Direction) (amount : Msat)
    (ph : PaymentHash) (cltv : Height) :
    (addHtlcRecord dir amount ph cltv).isPending :=
  addHtlcRecord_state dir amount ph cltv

theorem updateAddHtlc_htlcs_eq (c : Channel) (dir : Direction) (amount : Msat)
    (ph : PaymentHash) (cltv : Height) :
    (updateAddHtlc c dir amount ph cltv).htlcs =
      c.htlcs ++ [addHtlcRecord dir amount ph cltv] := rfl

/-- Appending a pending HTLC in `dir` raises the directional sum by exactly
its amount. -/
theorem pendingHtlcValueInDirection_updateAddHtlc_same
    (c : Channel) (dir : Direction) (amount : Msat) (ph : PaymentHash)
    (cltv : Height) :
    pendingHtlcValueInDirection (updateAddHtlc c dir amount ph cltv) dir =
      pendingHtlcValueInDirection c dir + amount.val := by
  unfold pendingHtlcValueInDirection
  rw [updateAddHtlc_htlcs_eq,
    pendingHtlcValueInDirectionList_append_singleton]
  have hp : ((addHtlcRecord dir amount ph cltv).state = HTLCState.offered ∨
      (addHtlcRecord dir amount ph cltv).state = HTLCState.received) ∧
      (addHtlcRecord dir amount ph cltv).direction = dir :=
    ⟨addHtlcRecord_state dir amount ph cltv, rfl⟩
  rw [ite_eq_left hp]
  rfl

/-- Appending an HTLC in `dir` leaves every other direction's sum unchanged. -/
theorem pendingHtlcValueInDirection_updateAddHtlc_other
    (c : Channel) (dir dir' : Direction) (amount : Msat) (ph : PaymentHash)
    (cltv : Height) (hne : dir' ≠ dir) :
    pendingHtlcValueInDirection (updateAddHtlc c dir amount ph cltv) dir' =
      pendingHtlcValueInDirection c dir' := by
  unfold pendingHtlcValueInDirection
  rw [updateAddHtlc_htlcs_eq,
    pendingHtlcValueInDirectionList_append_singleton]
  have hdir : (addHtlcRecord dir amount ph cltv).direction = dir := rfl
  have hconj : ¬ (((addHtlcRecord dir amount ph cltv).state =
        HTLCState.offered ∨ (addHtlcRecord dir amount ph cltv).state =
        HTLCState.received) ∧
      (addHtlcRecord dir amount ph cltv).direction = dir') := by
    intro hc
    exact hne ((hdir.symm.trans hc.2).symm)
  rw [ite_eq_right hconj]
  simp

/-! ## Compatibility with the pooled predicate -/

/-- Directional pending value never exceeds the pooled pending value. -/
theorem pendingHtlcValueInDirectionList_le_pendingValueList
    (dir : Direction) (hs : List HTLC) :
    pendingHtlcValueInDirectionList dir hs ≤
      ((hs.filter (fun h =>
        h.state = HTLCState.offered ∨ h.state = HTLCState.received)).map
        (fun h => h.amount.val)).sum := by
  induction hs with
  | nil => simp [pendingHtlcValueInDirectionList]
  | cons h hs ih =>
      unfold pendingHtlcValueInDirectionList at ih ⊢
      by_cases hp : h.state = HTLCState.offered ∨ h.state = HTLCState.received
      · by_cases hd : h.direction = dir
        · simp [hp, hd] at ih ⊢
          omega
        · simp [hp, hd] at ih ⊢
          omega
      · simp [hp] at ih ⊢
        omega

/-- The pooled `pendingHtlcValueOf` is the pending-only list sum. -/
theorem pendingHtlcValueOf_eq_pendingList (c : Channel) :
    pendingHtlcValueOf c =
      ((c.htlcs.filter (fun h =>
        h.state = HTLCState.offered ∨ h.state = HTLCState.received)).map
        (fun h => h.amount.val)).sum := rfl

theorem pendingHtlcValueInDirection_le_pendingHtlcValueOf
    (c : Channel) (dir : Direction) :
    pendingHtlcValueInDirection c dir ≤ pendingHtlcValueOf c := by
  rw [pendingHtlcValueInDirection_eq_list, pendingHtlcValueOf_eq_pendingList]
  exact pendingHtlcValueInDirectionList_le_pendingValueList dir c.htlcs

/-- The old pooled guard implies the new directional guard.  Thus the old
predicate is **conservative but not BOLT-2-faithful**: it accepts a subset of
what the directional rule accepts. -/
theorem affordableAdd_toDirectional {c : Channel} {dir : Direction}
    {amount : Msat} {cltvExpiry : Height}
    (h : AffordableAdd c dir amount cltvExpiry) :
    AffordableAddDirectional c dir amount cltvExpiry :=
  { positive := h.positive
    cltvBelowMaximum := h.cltvBelowMaximum
    atLeastHtlcMinimum := h.atLeastHtlcMinimum
    fitsOffered := h.fitsOffered
    leavesReserve := h.leavesReserve
    withinInFlightDirectional := by
      unfold WithinInFlightDirectional
      exact Nat.le_trans
        (Nat.add_le_add_right
          (pendingHtlcValueInDirection_le_pendingHtlcValueOf c dir) amount.val)
        h.withinInFlight }

/-! ## Preservation of the directional cap -/

/-- `update_add_htlc` admitted by the directional guard preserves the
directional pending-only cap. -/
theorem updateAddHtlc_preserves_directionalCap
    (c : Channel) (dir : Direction) (amount : Msat) (ph : PaymentHash)
    (cltv : Height) (h : AffordableAddDirectional c dir amount cltv) :
    pendingHtlcValueInDirection (updateAddHtlc c dir amount ph cltv) dir ≤
      (receiverParams c dir).maxHtlcValue.val := by
  rw [pendingHtlcValueInDirection_updateAddHtlc_same]
  exact h.withinInFlightDirectional

/-! ## Concrete witnesses -/

/-- A public key value used only to inhabit the witness records. -/
def witnessPubKey : PubKey := ⟨ByteArray.empty⟩

/-- Parameters for a witness endpoint.  The caller chooses the advertised
reserve, in-flight cap, and HTLC minimum. -/
def witnessParams (reserveSat maxHtlcMsat minHtlcMsat : Nat) : ChannelParams :=
  { dustLimitSat := 0
    channelReserveSat := reserveSat
    toSelfDelay := 0
    maxHtlcValue := ⟨maxHtlcMsat⟩
    htlcMinimum := ⟨minHtlcMsat⟩
    feerate := ⟨0⟩
    anchorOutputs := false }

def witnessEndpoint (params : ChannelParams) : Endpoint :=
  { nodeId := witnessPubKey
    fundingPubKey := witnessPubKey
    paymentBasepoint := witnessPubKey
    delayedPaymentBasepoint := witnessPubKey
    params := params }

/-- A witness channel.  The endpoints are fully concrete, so every arithmetic
test below is decidable. -/
def witnessChannel (localParams remoteParams : ChannelParams)
    (localBalance remoteBalance : Nat) (htlcs : List HTLC) : Channel :=
  { channelId := ChannelId.zero
    funding := ⟨ByteArray.empty, 0⟩
    fundingValue := ⟨localBalance + remoteBalance⟩
    localEndpoint := witnessEndpoint localParams
    remoteEndpoint := witnessEndpoint remoteParams
    phase := ChannelPhase.normal
    localCommitmentNumber := 0
    remoteCommitmentNumber := 0
    balance := { localBalance := ⟨localBalance⟩
                 remoteBalance := ⟨remoteBalance⟩ }
    htlcs := htlcs }

def witnessHtlc (dir : Direction) (amountMsat : Nat)
    (state : HTLCState) : HTLC :=
  { direction := dir
    amount := ⟨amountMsat⟩
    paymentHash := ⟨ByteArray.empty⟩
    cltvExpiry := 0
    state := state }

/-- G02 witness state.

From the local endpoint's view, the remote side has offered a pending
600 msat HTLC.  The local side wants to offer 500 msat; the *receiver* of that
local offer is the remote endpoint, which advertises a 1000 msat cap.

* directional local pending value: `0`; `0 + 500 ≤ 1000` accepts;
* pooled pending value: `600`; `600 + 500 > 1000` rejects. -/
def separationChannel : Channel :=
  witnessChannel
    (witnessParams 0 0 0)
    (witnessParams 0 1000 0)
    1000 700
    [witnessHtlc .remote 600 .received]

/-- G03 witness state.

A local HTLC of 600 msat is already settled (`fulfilled`), so it is not in
flight.  A new 500 msat local add is offered under the same 1000 msat cap.

* directional local pending value: `0`; `0 + 500 ≤ 1000` accepts;
* the old state-blind `sumByDirection .local` total: `600`; `600 + 500 >
  1000` rejects. -/
def terminalChannel : Channel :=
  witnessChannel
    (witnessParams 0 0 0)
    (witnessParams 0 1000 0)
    1000 700
    [witnessHtlc .local 600 .fulfilled]

/-! ### Computed fields of the witness states -/

@[simp] theorem separationChannel_offeredBalance_local :
    (offeredBalance separationChannel .local).val = 1000 := rfl

@[simp] theorem separationChannel_receiverMax_local :
    (receiverParams separationChannel .local).maxHtlcValue.val = 1000 := rfl

@[simp] theorem separationChannel_receiverMin_local :
    (receiverParams separationChannel .local).htlcMinimum.val = 0 := rfl

@[simp] theorem separationChannel_reserve_local :
    offeringReserveSat separationChannel .local = 0 := rfl

@[simp] theorem terminalChannel_offeredBalance_local :
    (offeredBalance terminalChannel .local).val = 1000 := rfl

@[simp] theorem terminalChannel_receiverMax_local :
    (receiverParams terminalChannel .local).maxHtlcValue.val = 1000 := rfl

@[simp] theorem terminalChannel_receiverMin_local :
    (receiverParams terminalChannel .local).htlcMinimum.val = 0 := rfl

@[simp] theorem terminalChannel_reserve_local :
    offeringReserveSat terminalChannel .local = 0 := rfl

/-- In the G02 witness the local direction has no pending HTLC: the 600 msat
HTLC was offered by the remote side. -/
@[simp] theorem separationChannel_pending_local :
    pendingHtlcValueInDirection separationChannel .local = 0 := by
  unfold separationChannel witnessChannel witnessHtlc
    pendingHtlcValueInDirection pendingHtlcValueInDirectionList
  simp

/-- The pooled bucket still contains the remote 600 msat HTLC. -/
@[simp] theorem separationChannel_pending_pooled :
    pendingHtlcValueOf separationChannel = 600 := by
  unfold separationChannel witnessChannel witnessHtlc pendingHtlcValueOf
  simp

/-- In the G03 witness the local 600 msat HTLC is terminal, so the local
directional pending bucket is empty. -/
@[simp] theorem terminalChannel_pending_local :
    pendingHtlcValueInDirection terminalChannel .local = 0 := by
  unfold terminalChannel witnessChannel witnessHtlc
    pendingHtlcValueInDirection pendingHtlcValueInDirectionList
  simp

/-- The old state-blind direction sum still counts the terminal HTLC. -/
@[simp] theorem terminalChannel_sumByDirection_local :
    LnLean.Proofs.Payment.sumByDirection .local terminalChannel.htlcs = 600 := by
  unfold terminalChannel witnessChannel witnessHtlc
    LnLean.Proofs.Payment.sumByDirection
  simp

/-- **G02 separation.**  A concrete state in which the directional pending-only
cap accepts an add while the old pooled predicate rejects it. -/
theorem directional_inFlight_separates :
    ∃ (c : Channel) (dir : Direction) (amount : Msat),
      WithinInFlightDirectional c dir amount ∧
      ¬ (pendingHtlcValueOf c + amount.val ≤
          (receiverParams c dir).maxHtlcValue.val) := by
  refine ⟨separationChannel, .local, ⟨500⟩, ?_, ?_⟩
  · unfold WithinInFlightDirectional
    rw [separationChannel_pending_local, separationChannel_receiverMax_local]
    simp
  · rw [separationChannel_pending_pooled, separationChannel_receiverMax_local]
    simp

/-- **G03 separation.**  A concrete state in which a terminal HTLC is excluded
from the directional sum but is still counted by the old state-blind
`LiquidityProps.sumByDirection` total. -/
theorem terminal_htlc_excluded_witness :
    ∃ (c : Channel) (amount : Msat),
      WithinInFlightDirectional c .local amount ∧
      ¬ (LnLean.Proofs.Payment.sumByDirection .local c.htlcs + amount.val ≤
          (receiverParams c .local).maxHtlcValue.val) := by
  refine ⟨terminalChannel, ⟨500⟩, ?_, ?_⟩
  · unfold WithinInFlightDirectional
    rw [terminalChannel_pending_local, terminalChannel_receiverMax_local]
    simp
  · rw [terminalChannel_sumByDirection_local, terminalChannel_receiverMax_local]
    simp

/-- The separation state inhabits the **full** new guard.  All five existing
guard components hold; only the pooled in-flight test fails. -/
theorem directional_witness_affordable :
    AffordableAddDirectional separationChannel .local ⟨500⟩ 0 :=
  { positive := by simp
    cltvBelowMaximum := by simp [MAX_CLTV_EXPIRY]
    atLeastHtlcMinimum := by simp
    fitsOffered := by simp
    leavesReserve := by simp
    withinInFlightDirectional := by
      unfold WithinInFlightDirectional
      simp }

/-- **Strict predicate separation.**  The full directional guard accepts a
concrete add that the old pooled `AffordableAdd` rejects.  This establishes
non-vacuity of `AffordableAddDirectional` and shows that the old predicate is
strictly stronger (conservative) on this carrier. -/
theorem directionalAdmission_separates_pooled :
    ∃ (c : Channel) (dir : Direction) (amount : Msat) (cltv : Height),
      AffordableAddDirectional c dir amount cltv ∧
      ¬ AffordableAdd c dir amount cltv := by
  refine ⟨separationChannel, .local, ⟨500⟩, 0,
    directional_witness_affordable, ?_⟩
  intro h
  have hnot : ¬ (pendingHtlcValueOf separationChannel +
      (⟨500⟩ : Msat).val ≤
        (receiverParams separationChannel .local).maxHtlcValue.val) := by
    rw [separationChannel_pending_pooled, separationChannel_receiverMax_local]
    simp
  exact hnot h.withinInFlight

/-- The terminal-HTLC witness also inhabits the full new guard. -/
theorem terminal_witness_affordable :
    AffordableAddDirectional terminalChannel .local ⟨500⟩ 0 :=
  { positive := by simp
    cltvBelowMaximum := by simp [MAX_CLTV_EXPIRY]
    atLeastHtlcMinimum := by simp
    fitsOffered := by simp
    leavesReserve := by simp
    withinInFlightDirectional := by
      unfold WithinInFlightDirectional
      simp }

/-- The preservation theorem applied to the concrete separation witness: the
600 msat remote pending HTLC is not part of the local direction, so after the
500 msat local add the local directional bucket is exactly 500 msat. -/
theorem separationChannel_after_add_value :
    pendingHtlcValueInDirection
        (updateAddHtlc separationChannel .local ⟨500⟩ ⟨ByteArray.empty⟩ 0)
        .local = 500 := by
  rw [pendingHtlcValueInDirection_updateAddHtlc_same,
    separationChannel_pending_local]
  simp

/-! ## Axiom audit -/

#print axioms pendingHtlcValueInDirection_le_pendingHtlcValueOf
#print axioms affordableAdd_toDirectional
#print axioms directional_inFlight_separates
#print axioms terminal_htlc_excluded_witness
#print axioms directionalAdmission_separates_pooled
#print axioms updateAddHtlc_preserves_directionalCap

end LnLean.Proofs.Wave14.LiquidityInFlight
