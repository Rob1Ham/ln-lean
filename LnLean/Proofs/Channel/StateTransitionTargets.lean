import LnLean.Channel.State
import LnLean.Channel.HTLC
import LnLean.Proofs.Channel.ReserveProps
import LnLean.Proofs.WaveE.E37

/-!
# LnLean.Proofs.Channel.StateTransitionTargets

English claim (obligation `MODEL-02` / `LN-CH-101`).  The channel state machine
now has the BOLT 2 HTLC update transitions that the lifecycle relation `Step`
deliberately omits: `update_add_htlc`, `update_fulfill_htlc`, and
`update_fail_htlc` (`LnLean.Channel.UpdateStep`).  This module proves, *from
the constructors*,

1. the successor-function refinement: the local `update_add_htlc` target is
   exactly `LnLean.Proofs.WaveE.E37.committedAdd`, and the new affordability
   predicate implies E37's `AffordableCommittedAdd`;
2. ledger conservation for every update transition — the add constructor
   carries `AffordableAdd`, so the truncated-subtraction obstruction is ruled
   out by construction; fulfilment and failure conserve because the pending
   bucket and the credited balance move by the same amount;
3. the reserve and in-flight invariants after an affordable add, and their
   preservation along `UpdateReachable`;
4. determinism of the update relation and monotonicity of the phase rank;
5. non-vacuity and the retained E37 counterexample: without the affordability
   guard the ledger equation is still false.

The additive relation is used instead of a new `Step` constructor because
`Step` is lifecycle-only by construction: `LnLean.Proofs.WaveD.D14`,
`LnLean.Proofs.ModelHardening.F03`, `LnLean.Proofs.Payment.LiquidityProps`,
and `LnLean.Proofs.PhaseC2.LivenessDelivery` all prove that a `Step` changes
neither balances nor the HTLC list, and `LnLean.Proofs.Liveness.step?` matches
`ProtocolEvent` exhaustively.  Those modules are outside this lane; the exact
migration patch is recorded in `agents/reports/swarm5/S5-MODEL-STEP.md`.

BOLT anchors.
* BOLT 2 §3 `update_add_htlc` (`02-peer-protocol.md:2739-2831`), reserve
  rationale (`:884-896`), `update_fulfill_htlc` (`:2913-2930`), and
  `update_fail_htlc` (`:2944-2960`).
* BOLT 3 §2 second-stage outputs (not modelled here; fee accounting is the
  `ReserveProps` boundary).

What is NOT modelled.
* Second-stage fees and dust trimming of the added HTLC output.
* The commitment dance that turns a pending update into a signed commitment;
  `UpdateStep` records the message effect, not the `commitment_signed` /
  `revoke_and_ack` round.
* HTLC ids: `HTLC` has no id field, so settlement selects the record by its
  list index and the guard requires the selected record to be pending.
-/

namespace LnLean.Proofs.Channel.StateTransitionTargets

set_option autoImplicit false

open LnLean
open LnLean.Channel

/-! ## The pending bucket as a list function -/

/-- The pending-value functional on an HTLC list. -/
def listPending (hs : List HTLC) : Nat :=
  ((hs.filter
      (fun h => h.state = HTLCState.offered ∨ h.state = HTLCState.received)).map
    (fun h => h.amount.val)).sum

/-- `pendingHtlcValueOf` is the channel-level form of `listPending`. -/
theorem pendingHtlcValueOf_eq_listPending (c : Channel) :
    pendingHtlcValueOf c = listPending c.htlcs := rfl

/-- The per-record contribution to the pending bucket. -/
def contribution (h : HTLC) : Nat :=
  if h.state = HTLCState.offered ∨ h.state = HTLCState.received then
    h.amount.val
  else 0

/-- `listPending` is the sum of the per-record contributions. -/
theorem listPending_eq_sum_contribution (hs : List HTLC) :
    listPending hs = (hs.map contribution).sum := by
  unfold listPending
  induction hs with
  | nil => rfl
  | cons h t ih =>
      rw [List.filter_cons]
      by_cases hp : h.state = HTLCState.offered ∨ h.state = HTLCState.received
      · simp only [hp, decide_true, ite_true, List.map_cons, List.sum_cons, ih]
        simp [contribution, hp]
      · simp only [hp, decide_false, Bool.false_eq_true, ite_false, ih]
        simp [contribution, hp]

/-- Value of one pending record plus the pending value of the tail. -/
theorem listPending_cons (h : HTLC) (hs : List HTLC) :
    listPending (h :: hs) = contribution h + listPending hs := by
  rw [listPending_eq_sum_contribution, listPending_eq_sum_contribution,
    List.map_cons, List.sum_cons]

/-- A settled record contributes nothing to the pending bucket. -/
theorem contribution_eq_zero_of_settled {h : HTLC}
    (hs : h.state = HTLCState.fulfilled ∨ h.state = HTLCState.failed ∨
      h.state = HTLCState.removed) :
    contribution h = 0 := by
  rcases hs with h' | h' | h' <;> simp [contribution, h']

/-- A pending record contributes exactly its amount. -/
theorem contribution_eq_amount_of_pending {h : HTLC}
    (hp : h.state = HTLCState.offered ∨ h.state = HTLCState.received) :
    contribution h = h.amount.val := by
  unfold contribution
  simp [hp]

/-! ## The index surgery behind fulfil / fail -/

/-- **Pending value after settling the record at `i`.**  Replacing the record
at `i` by a settled copy removes exactly that record's contribution. -/
theorem listPending_mapHtlcAt_settle (st : HTLCState)
    (hst : st = HTLCState.fulfilled ∨ st = HTLCState.failed ∨
      st = HTLCState.removed)
    (i : Nat) (hs : List HTLC) (x : HTLC) (hi : hs[i]? = some x) :
    listPending hs =
      listPending (mapHtlcAt i (fun h => { h with state := st }) hs) +
        contribution x := by
  induction hs generalizing i with
  | nil => simp at hi
  | cons y ys ih =>
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
          have hxy : y = x := hi
          subst hxy
          have hzero : contribution { y with state := st } = 0 := by
            apply contribution_eq_zero_of_settled
            rcases hst with h' | h' | h' <;> simp [h']
          rw [mapHtlcAt, listPending_cons, listPending_cons, hzero]
          omega
      | succ k =>
          simp only [List.getElem?_cons_succ] at hi
          have hrec := ih k hi
          rw [mapHtlcAt, listPending_cons, listPending_cons]
          omega

/-- Settling the record at `i` reduces the channel's pending value by the
record's amount. -/
theorem pendingHtlcValueOf_settleAt (c : Channel) (i : Nat) (st : HTLCState)
    (hst : st = HTLCState.fulfilled ∨ st = HTLCState.failed ∨
      st = HTLCState.removed)
    (h : HTLC) (hi : c.htlcs[i]? = some h) (hp : h.isPending) :
    pendingHtlcValueOf c =
      listPending (setHtlcStateAt c.htlcs i st) + h.amount.val := by
  have hp' : h.state = HTLCState.offered ∨ h.state = HTLCState.received := hp
  have hc : contribution h = h.amount.val :=
    contribution_eq_amount_of_pending hp'
  have := listPending_mapHtlcAt_settle st hst i c.htlcs h hi
  rw [pendingHtlcValueOf_eq_listPending]
  unfold setHtlcStateAt
  omega

/-! ## Projections of the successor functions -/

@[simp] theorem updateAddHtlc_channelId (c : Channel) (dir : Direction)
    (amount : Msat) (ph : PaymentHash) (cltv : Height) :
    (updateAddHtlc c dir amount ph cltv).channelId = c.channelId := rfl

@[simp] theorem updateAddHtlc_funding (c : Channel) (dir : Direction)
    (amount : Msat) (ph : PaymentHash) (cltv : Height) :
    (updateAddHtlc c dir amount ph cltv).funding = c.funding := rfl

@[simp] theorem updateAddHtlc_fundingValue (c : Channel) (dir : Direction)
    (amount : Msat) (ph : PaymentHash) (cltv : Height) :
    (updateAddHtlc c dir amount ph cltv).fundingValue = c.fundingValue := rfl

@[simp] theorem updateAddHtlc_phase (c : Channel) (dir : Direction)
    (amount : Msat) (ph : PaymentHash) (cltv : Height) :
    (updateAddHtlc c dir amount ph cltv).phase = c.phase := rfl

@[simp] theorem updateAddHtlc_localCommitmentNumber (c : Channel) (dir : Direction)
    (amount : Msat) (ph : PaymentHash) (cltv : Height) :
    (updateAddHtlc c dir amount ph cltv).localCommitmentNumber =
      c.localCommitmentNumber := rfl

@[simp] theorem updateAddHtlc_remoteCommitmentNumber (c : Channel) (dir : Direction)
    (amount : Msat) (ph : PaymentHash) (cltv : Height) :
    (updateAddHtlc c dir amount ph cltv).remoteCommitmentNumber =
      c.remoteCommitmentNumber := rfl

/-- The added record is exactly the one at the end of the HTLC list. -/
theorem updateAddHtlc_htlcs (c : Channel) (dir : Direction) (amount : Msat)
    (ph : PaymentHash) (cltv : Height) :
    (updateAddHtlc c dir amount ph cltv).htlcs = c.htlcs ++
      [{ direction := dir
         amount := amount
         paymentHash := ph
         cltvExpiry := cltv
         state := match dir with
           | .local => HTLCState.offered
           | .remote => HTLCState.received }] := rfl

theorem failHtlcAt_htlcs (c : Channel) (i : Nat) (h : HTLC)
    (hi : c.htlcs[i]? = some h) :
    (failHtlcAt c i).htlcs = setHtlcStateAt c.htlcs i HTLCState.failed := by
  unfold failHtlcAt
  rw [hi]

theorem fulfillHtlcAt_htlcs (c : Channel) (i : Nat) (h : HTLC)
    (hi : c.htlcs[i]? = some h) :
    (fulfillHtlcAt c i).htlcs = setHtlcStateAt c.htlcs i HTLCState.fulfilled := by
  unfold fulfillHtlcAt
  rw [hi]

@[simp] theorem failHtlcAt_localReserveSat (c : Channel) (i : Nat) :
    LnLean.Proofs.Channel.localReserveSat (failHtlcAt c i) =
      LnLean.Proofs.Channel.localReserveSat c := by
  unfold failHtlcAt LnLean.Proofs.Channel.localReserveSat
  split <;> rfl

@[simp] theorem failHtlcAt_remoteReserveSat (c : Channel) (i : Nat) :
    LnLean.Proofs.Channel.remoteReserveSat (failHtlcAt c i) =
      LnLean.Proofs.Channel.remoteReserveSat c := by
  unfold failHtlcAt LnLean.Proofs.Channel.remoteReserveSat
  split <;> rfl

@[simp] theorem fulfillHtlcAt_localReserveSat (c : Channel) (i : Nat) :
    LnLean.Proofs.Channel.localReserveSat (fulfillHtlcAt c i) =
      LnLean.Proofs.Channel.localReserveSat c := by
  unfold fulfillHtlcAt LnLean.Proofs.Channel.localReserveSat
  split <;> rfl

@[simp] theorem fulfillHtlcAt_remoteReserveSat (c : Channel) (i : Nat) :
    LnLean.Proofs.Channel.remoteReserveSat (fulfillHtlcAt c i) =
      LnLean.Proofs.Channel.remoteReserveSat c := by
  unfold fulfillHtlcAt LnLean.Proofs.Channel.remoteReserveSat
  split <;> rfl

@[simp] theorem failHtlcAt_fundingValue (c : Channel) (i : Nat) :
    (failHtlcAt c i).fundingValue = c.fundingValue := by
  unfold failHtlcAt
  split <;> rfl

@[simp] theorem fulfillHtlcAt_fundingValue (c : Channel) (i : Nat) :
    (fulfillHtlcAt c i).fundingValue = c.fundingValue := by
  unfold fulfillHtlcAt
  split <;> rfl

/-! ## Pending value after an add -/

/-- Appending a pending record raises the pending value by exactly its
amount, in either direction. -/
theorem pendingHtlcValueOf_updateAddHtlc (c : Channel) (dir : Direction)
    (amount : Msat) (ph : PaymentHash) (cltv : Height) :
    pendingHtlcValueOf (updateAddHtlc c dir amount ph cltv) =
      pendingHtlcValueOf c + amount.val := by
  rw [pendingHtlcValueOf_eq_listPending, pendingHtlcValueOf_eq_listPending,
    updateAddHtlc_htlcs]
  unfold listPending
  rw [List.filter_append, List.map_append, List.sum_append]
  cases dir <;> simp

/-- Settling a pending record at `i` removes exactly its amount from the
pending bucket. -/
theorem pendingHtlcValueOf_failHtlcAt (c : Channel) (i : Nat) (h : HTLC)
    (hi : c.htlcs[i]? = some h) (hp : h.isPending) :
    pendingHtlcValueOf c = pendingHtlcValueOf (failHtlcAt c i) + h.amount.val := by
  have hsettle :=
    pendingHtlcValueOf_settleAt c i HTLCState.failed (by simp) h hi hp
  rw [pendingHtlcValueOf_eq_listPending] at hsettle
  rw [pendingHtlcValueOf_eq_listPending, pendingHtlcValueOf_eq_listPending,
    failHtlcAt_htlcs c i h hi]
  exact hsettle

theorem pendingHtlcValueOf_fulfillHtlcAt (c : Channel) (i : Nat) (h : HTLC)
    (hi : c.htlcs[i]? = some h) (hp : h.isPending) :
    pendingHtlcValueOf c = pendingHtlcValueOf (fulfillHtlcAt c i) + h.amount.val := by
  have hsettle :=
    pendingHtlcValueOf_settleAt c i HTLCState.fulfilled (by simp) h hi hp
  rw [pendingHtlcValueOf_eq_listPending] at hsettle
  rw [pendingHtlcValueOf_eq_listPending, pendingHtlcValueOf_eq_listPending,
    fulfillHtlcAt_htlcs c i h hi]
  exact hsettle

/-! ## Balance totals after the successor functions -/

/-- The settled total after an affordable add drops by exactly the amount. -/
theorem balanceVal_updateAddHtlc (c : Channel) (dir : Direction) (amount : Msat)
    (ph : PaymentHash) (cltv : Height)
    (hfit : amount.val ≤ (offeredBalance c dir).val) :
    (updateAddHtlc c dir amount ph cltv).balance.localBalance.val +
        (updateAddHtlc c dir amount ph cltv).balance.remoteBalance.val =
      c.balance.localBalance.val + c.balance.remoteBalance.val - amount.val := by
  cases dir
  · simp [updateAddHtlc, offeredBalance] at hfit ⊢
    omega
  · simp [updateAddHtlc, offeredBalance] at hfit ⊢
    omega

/-- Failure credits the offering side. -/
theorem balanceVal_failHtlcAt (c : Channel) (i : Nat) (h : HTLC)
    (hi : c.htlcs[i]? = some h) :
    (failHtlcAt c i).balance.localBalance.val +
        (failHtlcAt c i).balance.remoteBalance.val =
      c.balance.localBalance.val + c.balance.remoteBalance.val + h.amount.val := by
  unfold failHtlcAt
  rw [hi]
  cases hd : h.direction <;> simp [hd] <;> omega

/-- Fulfilment credits the receiving side. -/
theorem balanceVal_fulfillHtlcAt (c : Channel) (i : Nat) (h : HTLC)
    (hi : c.htlcs[i]? = some h) :
    (fulfillHtlcAt c i).balance.localBalance.val +
        (fulfillHtlcAt c i).balance.remoteBalance.val =
      c.balance.localBalance.val + c.balance.remoteBalance.val + h.amount.val := by
  unfold fulfillHtlcAt
  rw [hi]
  cases hd : h.direction <;> simp [hd] <;> omega

/-- The componentwise balance inequalities for failure. -/
theorem failHtlcAt_balance_ge (c : Channel) (i : Nat) :
    c.balance.localBalance.val ≤ (failHtlcAt c i).balance.localBalance.val ∧
      c.balance.remoteBalance.val ≤ (failHtlcAt c i).balance.remoteBalance.val := by
  unfold failHtlcAt
  cases hg : c.htlcs[i]? with
  | none => simp
  | some h =>
      cases hd : h.direction <;> simp [hd]

theorem fulfillHtlcAt_balance_ge (c : Channel) (i : Nat) :
    c.balance.localBalance.val ≤ (fulfillHtlcAt c i).balance.localBalance.val ∧
      c.balance.remoteBalance.val ≤ (fulfillHtlcAt c i).balance.remoteBalance.val := by
  unfold fulfillHtlcAt
  cases hg : c.htlcs[i]? with
  | none => simp
  | some h =>
      cases hd : h.direction <;> simp [hd]

/-! ## The E37 refinement -/

/-- E37's pending value is this module's pending value. -/
theorem pendingValue_eq_pendingHtlcValueOf (c : Channel) :
    LnLean.Proofs.WaveE.E37.pendingValue c = pendingHtlcValueOf c := rfl

/-- E37's `ledgerValue` is the settled total plus the pending bucket and the
fee; this module's pending bucket agrees definitionally. -/
theorem ledgerValue_eq (c : Channel) (fee : Msat) :
    LnLean.Proofs.WaveE.E37.ledgerValue c fee =
      c.balance.localBalance.val + c.balance.remoteBalance.val +
        pendingHtlcValueOf c + fee.val := by
  rw [LnLean.Proofs.WaveE.E37.ledgerValue, pendingValue_eq_pendingHtlcValueOf]

/-- **Successor-function refinement.**  E37's `committedAdd` is exactly the
local `update_add_htlc` target with an empty payment hash and zero expiry: the
new transition is the missing constructor for E37's successor function, not a
second model. -/
theorem committedAdd_eq_updateAddHtlc (c : Channel) (amount : Msat) :
    LnLean.Proofs.WaveE.E37.committedAdd c amount =
      updateAddHtlc c .local amount ⟨ByteArray.empty⟩ 0 := rfl

/-- **Affordability refinement.**  The new constructor's guard implies E37's
`AffordableCommittedAdd` for a local add. -/
theorem affordableAdd_implies_e37 {c : Channel} {amount : Msat}
    (h : AffordableAdd c .local amount 0) :
    LnLean.Proofs.WaveE.E37.AffordableCommittedAdd c amount where
  fitsSettled := h.fitsOffered
  leavesReserve := h.leavesReserve
  atLeastHtlcMinimum := h.atLeastHtlcMinimum
  withinReceiverInFlight := h.withinInFlight

/-! ## Ledger conservation from the constructors -/

/-- An affordable add preserves E37's ledger value. -/
theorem ledgerValue_updateAddHtlc (c : Channel) (dir : Direction) (amount : Msat)
    (ph : PaymentHash) (cltv : Height) (fee : Msat)
    (haff : AffordableAdd c dir amount cltv) :
    LnLean.Proofs.WaveE.E37.ledgerValue (updateAddHtlc c dir amount ph cltv) fee =
      LnLean.Proofs.WaveE.E37.ledgerValue c fee := by
  have hp := pendingHtlcValueOf_updateAddHtlc c dir amount ph cltv
  have hb := balanceVal_updateAddHtlc c dir amount ph cltv haff.fitsOffered
  rw [ledgerValue_eq, ledgerValue_eq, hp, hb]
  have hS : amount.val ≤
      c.balance.localBalance.val + c.balance.remoteBalance.val := by
    have hfit := haff.fitsOffered
    cases dir <;> simp [offeredBalance] at hfit ⊢ <;> omega
  omega

/-- Failure preserves E37's ledger value: the pending bucket loses exactly the
amount that the offering balance gains. -/
theorem ledgerValue_failHtlcAt (c : Channel) (i : Nat) (h : HTLC)
    (hi : c.htlcs[i]? = some h) (hp : h.isPending) (fee : Msat) :
    LnLean.Proofs.WaveE.E37.ledgerValue (failHtlcAt c i) fee =
      LnLean.Proofs.WaveE.E37.ledgerValue c fee := by
  have hpend := pendingHtlcValueOf_failHtlcAt c i h hi hp
  have hbal := balanceVal_failHtlcAt c i h hi
  rw [ledgerValue_eq, ledgerValue_eq, hpend, hbal]
  omega

/-- Fulfilment preserves E37's ledger value: the pending bucket loses exactly
the amount that the receiving balance gains. -/
theorem ledgerValue_fulfillHtlcAt (c : Channel) (i : Nat) (h : HTLC)
    (hi : c.htlcs[i]? = some h) (hp : h.isPending) (fee : Msat) :
    LnLean.Proofs.WaveE.E37.ledgerValue (fulfillHtlcAt c i) fee =
      LnLean.Proofs.WaveE.E37.ledgerValue c fee := by
  have hpend := pendingHtlcValueOf_fulfillHtlcAt c i h hi hp
  have hbal := balanceVal_fulfillHtlcAt c i h hi
  rw [ledgerValue_eq, ledgerValue_eq, hpend, hbal]
  omega

/-- A lifecycle step preserves E37's ledger value. -/
theorem ledgerValue_step {c c' : Channel} {e : ProtocolEvent} (h : Step c e c')
    (fee : Msat) :
    LnLean.Proofs.WaveE.E37.ledgerValue c' fee =
      LnLean.Proofs.WaveE.E37.ledgerValue c fee := by
  have hb : c'.balance = c.balance := by cases h <;> rfl
  have hh : c'.htlcs = c.htlcs := by cases h <;> rfl
  rw [ledgerValue_eq, ledgerValue_eq]
  rw [hb]
  congr 1
  rw [pendingHtlcValueOf_eq_listPending, pendingHtlcValueOf_eq_listPending, hh]

/-- A lifecycle step preserves the funding value. -/
theorem step_fundingValue_eq {c c' : Channel} {e : ProtocolEvent}
    (h : Step c e c') : c'.fundingValue = c.fundingValue := by
  cases h <;> rfl

/-- **Ledger conservation of every update transition, from the constructors.**
No separate affordability hypothesis is needed for `update_add_htlc`: the
guard is a constructor argument.  The lifecycle embedding uses the existing
balance/HTLC preservation of `Step`. -/
theorem updateStep_preserves_ledger {hashFn : ByteArray → ByteArray}
    {c c' : Channel} {e : UpdateEvent} (hs : UpdateStep hashFn c e c')
    (fee : Msat)
    (hled : LnLean.Proofs.WaveE.E37.ledgerValue c fee = c.fundingValue.val) :
    LnLean.Proofs.WaveE.E37.ledgerValue c' fee = c'.fundingValue.val := by
  cases hs with
  | lifecycle hstep =>
      rw [ledgerValue_step hstep, step_fundingValue_eq hstep]
      exact hled
  | update_add_htlc hphase dir amount ph cltv haff =>
      rw [ledgerValue_updateAddHtlc c dir amount ph cltv fee haff]
      simpa using hled
  | update_fulfill_htlc hphase i hh p hi hpending hpre =>
      rw [ledgerValue_fulfillHtlcAt c i hh hi hpending fee]
      simpa using hled
  | update_fail_htlc hphase i hh hi hpending =>
      rw [ledgerValue_failHtlcAt c i hh hi hpending fee]
      simpa using hled

/-- **The local add refines E37's conservation theorem.**  This is the same
statement as `E37.waveE_e37_affordable_preserves_ledger`, transported across
the successor-function equality. -/
theorem updateStep_add_local_ledger_via_E37 (c : Channel) (fee amount : Msat)
    (haff : AffordableAdd c .local amount 0)
    (hled : LnLean.Proofs.WaveE.E37.ledgerValue c fee = c.fundingValue.val) :
    LnLean.Proofs.WaveE.E37.ledgerValue
        (LnLean.Proofs.WaveE.E37.committedAdd c amount) fee =
      (LnLean.Proofs.WaveE.E37.committedAdd c amount).fundingValue.val :=
  LnLean.Proofs.WaveE.E37.waveE_e37_affordable_preserves_ledger c fee amount
    (affordableAdd_implies_e37 haff) hled

/-! ## Determinism, phase rank, and counters -/

/-- For a fixed source and update event the target is unique. -/
theorem updateStep_deterministic {hashFn : ByteArray → ByteArray}
    {c c₁ c₂ : Channel} {e : UpdateEvent}
    (h₁ : UpdateStep hashFn c e c₁) (h₂ : UpdateStep hashFn c e c₂) :
    c₁ = c₂ := by
  cases h₁ with
  | lifecycle hs₁ =>
      cases h₂ with
      | lifecycle hs₂ => cases hs₁ <;> cases hs₂ <;> rfl
  | update_add_htlc hphase dir amount ph cltv haff =>
      cases h₂ with
      | update_add_htlc _ _ _ _ _ _ => rfl
  | update_fulfill_htlc hphase i hh p hi hpending hpre =>
      cases h₂ with
      | update_fulfill_htlc _ _ _ _ _ _ _ => rfl
  | update_fail_htlc hphase i hh hi hpending =>
      cases h₂ with
      | update_fail_htlc _ _ _ _ _ => rfl

/-- Every update transition is non-decreasing in the phase rank. -/
theorem updateStep_phaseRank_le {hashFn : ByteArray → ByteArray}
    {c c' : Channel} {e : UpdateEvent} (h : UpdateStep hashFn c e c') :
    phaseRank c.phase ≤ phaseRank c'.phase := by
  cases h with
  | lifecycle hs => exact step_phaseRank_le hs
  | update_add_htlc hphase dir amount ph cltv haff =>
      simp [updateAddHtlc]
  | update_fulfill_htlc hphase i hh p hi hpending hpre =>
      unfold fulfillHtlcAt
      split <;> simp
  | update_fail_htlc hphase i hh hi hpending =>
      unfold failHtlcAt
      split <;> simp

/-- The add transition leaves both commitment counters unchanged. -/
theorem updateStep_add_counters {hashFn : ByteArray → ByteArray}
    {c c' : Channel} {dir : Direction} {amount : Msat} {ph : PaymentHash}
    {cltv : Height} (h : UpdateStep hashFn c (.addHtlc dir amount ph cltv) c') :
    c'.localCommitmentNumber = c.localCommitmentNumber ∧
      c'.remoteCommitmentNumber = c.remoteCommitmentNumber := by
  cases h
  exact ⟨rfl, rfl⟩

/-! ## Reserve and spendable balance after an affordable add -/

/-- An affordable add preserves `ReserveInvariant`. -/
theorem updateAddHtlc_reserveInvariant {c : Channel} {dir : Direction}
    {amount : Msat} {cltv : Height} (haff : AffordableAdd c dir amount cltv)
    (hres : LnLean.Proofs.Channel.ReserveInvariant c) :
    LnLean.Proofs.Channel.ReserveInvariant
      (updateAddHtlc c dir amount ⟨ByteArray.empty⟩ cltv) := by
  rcases hres with ⟨hl, hr⟩
  cases dir
  · refine ⟨?_, ?_⟩
    · have h := LnLean.Proofs.Channel.spendLocal_preserves_reserve
          (b := c.balance)
          (reserve := LnLean.Proofs.Channel.localReserveSat c)
          (amountMsat := amount.val) (by
            simpa [offeringReserveSat, offeredBalance,
              LnLean.Proofs.Channel.localReserveSat] using haff.leavesReserve)
      simpa [LnLean.Proofs.Channel.ReserveInvariant,
        LnLean.Proofs.Channel.localReserveSat, updateAddHtlc,
        LnLean.Proofs.Channel.spendLocalBalance] using h
    · simpa [LnLean.Proofs.Channel.ReserveInvariant,
        LnLean.Proofs.Channel.remoteReserveSat,
        LnLean.Channel.Balance.remoteSat,
        updateAddHtlc] using hr
  · refine ⟨?_, ?_⟩
    · simpa [LnLean.Proofs.Channel.ReserveInvariant,
        LnLean.Proofs.Channel.localReserveSat,
        LnLean.Channel.reserveSatisfied,
        LnLean.Channel.Balance.localSat, Msat.toSatFloor,
        updateAddHtlc] using hl
    · have h := LnLean.Proofs.Channel.spendRemote_preserves_remoteReserve
          (b := c.balance)
          (reserve := LnLean.Proofs.Channel.remoteReserveSat c)
          (amountMsat := amount.val) (by
            simpa [offeringReserveSat, offeredBalance,
              LnLean.Proofs.Channel.remoteReserveSat] using haff.leavesReserve)
      simpa [LnLean.Proofs.Channel.ReserveInvariant,
        LnLean.Proofs.Channel.remoteReserveSat, updateAddHtlc,
        LnLean.Proofs.Channel.spendRemoteBalance] using h

/-- An affordable add keeps the receiver's in-flight exposure within its
advertised maximum. -/
theorem updateAddHtlc_inFlight_le {c : Channel} {dir : Direction}
    {amount : Msat} {cltv : Height} (haff : AffordableAdd c dir amount cltv) :
    pendingHtlcValueOf (updateAddHtlc c dir amount ⟨ByteArray.empty⟩ cltv) ≤
      (receiverParams c dir).maxHtlcValue.val := by
  rw [pendingHtlcValueOf_updateAddHtlc]
  exact haff.withinInFlight

/-- Balance growth preserves `ReserveInvariant` when the reserve parameters are
unchanged. -/
theorem reserveInvariant_of_balance_ge {c c' : Channel}
    (hlr : LnLean.Proofs.Channel.localReserveSat c' =
      LnLean.Proofs.Channel.localReserveSat c)
    (hrr : LnLean.Proofs.Channel.remoteReserveSat c' =
      LnLean.Proofs.Channel.remoteReserveSat c)
    (hl : c.balance.localBalance.val ≤ c'.balance.localBalance.val)
    (hr : c.balance.remoteBalance.val ≤ c'.balance.remoteBalance.val)
    (hres : LnLean.Proofs.Channel.ReserveInvariant c) :
    LnLean.Proofs.Channel.ReserveInvariant c' := by
  rcases hres with ⟨h1, h2⟩
  constructor
  · show LnLean.Channel.reserveSatisfied c'.balance
      (LnLean.Proofs.Channel.localReserveSat c')
    rw [hlr]
    unfold LnLean.Channel.reserveSatisfied Balance.localSat
      Msat.toSatFloor at h1 ⊢
    exact Nat.le_trans h1 (Nat.div_le_div_right hl)
  · show LnLean.Proofs.Channel.remoteReserveSat c' ≤ c'.balance.remoteSat
    rw [hrr]
    unfold Balance.remoteSat Msat.toSatFloor at h2 ⊢
    exact Nat.le_trans h2 (Nat.div_le_div_right hr)

/-- Every update transition preserves `ReserveInvariant`. -/
theorem updateStep_preserves_reserve {hashFn : ByteArray → ByteArray}
    {c c' : Channel} {e : UpdateEvent} (hs : UpdateStep hashFn c e c')
    (hres : LnLean.Proofs.Channel.ReserveInvariant c) :
    LnLean.Proofs.Channel.ReserveInvariant c' := by
  cases hs with
  | lifecycle hstep =>
      exact LnLean.Proofs.Channel.step_preserves_reserveInvariant hstep hres
  | update_add_htlc hphase dir amount ph cltv haff =>
      exact updateAddHtlc_reserveInvariant haff hres
  | update_fulfill_htlc hphase i hh p hi hpending hpre =>
      exact reserveInvariant_of_balance_ge (c := c) (c' := fulfillHtlcAt c i)
        (by simp) (by simp) (fulfillHtlcAt_balance_ge c i).1
        (fulfillHtlcAt_balance_ge c i).2 hres
  | update_fail_htlc hphase i hh hi hpending =>
      exact reserveInvariant_of_balance_ge (c := c) (c' := failHtlcAt c i)
        (by simp) (by simp) (failHtlcAt_balance_ge c i).1
        (failHtlcAt_balance_ge c i).2 hres

/-! ## Reachability -/

/-- `UpdateReachable` preserves E37's ledger value. -/
theorem updateReachable_preserves_ledger {hashFn : ByteArray → ByteArray}
    {a b : Channel} (h : UpdateReachable hashFn a b) (fee : Msat)
    (hled : LnLean.Proofs.WaveE.E37.ledgerValue a fee = a.fundingValue.val) :
    LnLean.Proofs.WaveE.E37.ledgerValue b fee = b.fundingValue.val := by
  induction h with
  | refl => exact hled
  | step _ hs ih => exact updateStep_preserves_ledger hs fee ih

/-- `UpdateReachable` preserves `ReserveInvariant`. -/
theorem updateReachable_preserves_reserve {hashFn : ByteArray → ByteArray}
    {a b : Channel} (h : UpdateReachable hashFn a b)
    (hres : LnLean.Proofs.Channel.ReserveInvariant a) :
    LnLean.Proofs.Channel.ReserveInvariant b := by
  induction h with
  | refl => exact hres
  | step _ hs ih => exact updateStep_preserves_reserve hs ih

/-- Every lifecycle trace is an update trace. -/
theorem updateReachable_of_reachable {hashFn : ByteArray → ByteArray}
    {a b : Channel} (h : Reachable a b) : UpdateReachable hashFn a b := by
  induction h with
  | refl => exact UpdateReachable.refl a
  | step _ hs ih => exact UpdateReachable.step ih (UpdateStep.lifecycle hs)

/-! ## Guard extraction

Each constructor exposes exactly the predicate it checks; these projections
are what a consumer uses instead of a separate `reject` branch. -/

/-- An `update_add_htlc` transition carries its affordability certificate. -/
theorem updateStep_add_affordable {hashFn : ByteArray → ByteArray}
    {c c' : Channel} {dir : Direction} {amount : Msat} {ph : PaymentHash}
    {cltv : Height} (h : UpdateStep hashFn c (.addHtlc dir amount ph cltv) c') :
    AffordableAdd c dir amount cltv := by
  cases h
  assumption

/-- An `update_fail_htlc` transition selects a pending HTLC. -/
theorem updateStep_fail_pending {hashFn : ByteArray → ByteArray}
    {c c' : Channel} {i : Nat} (h : UpdateStep hashFn c (.failHtlc i) c') :
    ∃ x ∈ c.htlcs, x.isPending ∧ c' = failHtlcAt c i := by
  cases h with
  | update_fail_htlc hphase i' hh hi hpending =>
      exact ⟨hh, List.mem_of_getElem? hi, hpending, rfl⟩

/-- An `update_fulfill_htlc` transition selects a pending HTLC and carries the
preimage hypothesis. -/
theorem updateStep_fulfill_pending {hashFn : ByteArray → ByteArray}
    {c c' : Channel} {i : Nat} {p : Preimage}
    (h : UpdateStep hashFn c (.fulfillHtlc i p) c') :
    ∃ x ∈ c.htlcs, x.isPending ∧ p.Valid ∧
      hashFn p.bytes = x.paymentHash.bytes ∧ c' = fulfillHtlcAt c i := by
  cases h with
  | update_fulfill_htlc hphase i' hh pp hi hpending hpre =>
      exact ⟨hh, List.mem_of_getElem? hi, hpending, hpre.1, hpre.2, rfl⟩

/-- A lifecycle event is legal in the update relation exactly when it is legal
in `Step`.  This is the refinement direction of the embedding. -/
theorem updateStep_lifecycle_iff {hashFn : ByteArray → ByteArray}
    {c c' : Channel} {e : ProtocolEvent} :
    UpdateStep hashFn c (.lifecycle e) c' ↔ Step c e c' := by
  constructor
  · intro h
    cases h with
    | lifecycle hs => exact hs
  · intro h
    exact UpdateStep.lifecycle h

/-! ## Non-vacuity and the retained counterexample -/

/-- **Non-vacuity.**  A concrete affordable add exists and conserves the
ledger: a 500-msat local HTLC in a channel with settled balances 1000/1000
msat, funding 2000 msat, zero reserve, a 1-msat minimum, and a 1000-msat
in-flight cap. -/
theorem updateStep_add_witness :
    ∃ (c c' : Channel) (e : UpdateEvent) (fee : Msat),
      UpdateStep (fun b : ByteArray => b) c e c' ∧
        LnLean.Proofs.WaveE.E37.ledgerValue c fee = c.fundingValue.val ∧
          LnLean.Proofs.WaveE.E37.ledgerValue c' fee = c'.fundingValue.val := by
  let c := LnLean.Proofs.WaveE.E37.testChannel 1000 1000 2000 0 1 1000
  let amount : Msat := ⟨500⟩
  let fee : Msat := ⟨0⟩
  have haff : AffordableAdd c .local amount 0 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [c, LnLean.Proofs.WaveE.E37.testChannel, amount,
        MAX_CLTV_EXPIRY, offeredBalance, offeringReserveSat, receiverParams,
        pendingHtlcValueOf]
  have hstep :
      UpdateStep (fun b : ByteArray => b) c
        (.addHtlc .local amount ⟨ByteArray.empty⟩ 0)
        (updateAddHtlc c .local amount ⟨ByteArray.empty⟩ 0) :=
    UpdateStep.update_add_htlc c (by simp [c, LnLean.Proofs.WaveE.E37.testChannel])
      .local amount ⟨ByteArray.empty⟩ 0 haff
  have hled : LnLean.Proofs.WaveE.E37.ledgerValue c fee =
      c.fundingValue.val := by
    simp [c, LnLean.Proofs.WaveE.E37.testChannel, fee,
      LnLean.Proofs.WaveE.E37.ledgerValue, LnLean.Proofs.WaveE.E37.pendingValue]
  exact ⟨c, _, _, fee, hstep, hled,
    updateStep_preserves_ledger hstep fee hled⟩

/-- **The unguarded add still breaks the ledger.**  Dropping the affordability
guard from the successor function (the E37 counterexample) keeps the ledger
equation false: a zero-local-balance channel that adds a 1-msat local HTLC has
successor ledger 1001 against funding 1000.  The constructor cannot be
instantiated in this state because `AffordableAdd.fitsOffered` fails, which is
exactly the `MODEL-02` gap that the guard closes. -/
theorem unguarded_add_ledger_counterexample :
    ∃ (c : Channel) (dir : Direction) (amount : Msat) (ph : PaymentHash)
        (cltv : Height) (fee : Msat),
      LnLean.Proofs.WaveE.E37.ledgerValue c fee = c.fundingValue.val ∧
        ¬ AffordableAdd c dir amount cltv ∧
          LnLean.Proofs.WaveE.E37.ledgerValue
              (updateAddHtlc c dir amount ph cltv) fee ≠
            (updateAddHtlc c dir amount ph cltv).fundingValue.val := by
  let c := LnLean.Proofs.WaveE.E37.testChannel 0 1000 1000 0 0 0
  let amount : Msat := ⟨1⟩
  refine ⟨c, .local, amount, ⟨ByteArray.empty⟩, 0, ⟨0⟩, ?_, ?_, ?_⟩
  · simp [c, LnLean.Proofs.WaveE.E37.testChannel,
      LnLean.Proofs.WaveE.E37.ledgerValue, LnLean.Proofs.WaveE.E37.pendingValue]
  · intro haff
    have hf := haff.fitsOffered
    simp [c, LnLean.Proofs.WaveE.E37.testChannel, amount, offeredBalance] at hf
  · simp [c, LnLean.Proofs.WaveE.E37.testChannel, amount,
      updateAddHtlc, LnLean.Proofs.WaveE.E37.ledgerValue,
      LnLean.Proofs.WaveE.E37.pendingValue]

/-- The local add target is literally E37's successor.  This is the
constructor-level form of `committedAdd_eq_updateAddHtlc`. -/
theorem updateStep_add_local_target (c : Channel) (amount : Msat)
    (hphase : c.phase = ChannelPhase.normal)
    (haff : AffordableAdd c .local amount 0) :
    ∃ (e : UpdateEvent) (c' : Channel),
      UpdateStep (fun b : ByteArray => b) c e c' ∧
        c' = LnLean.Proofs.WaveE.E37.committedAdd c amount := by
  refine ⟨.addHtlc .local amount ⟨ByteArray.empty⟩ 0,
    updateAddHtlc c .local amount ⟨ByteArray.empty⟩ 0,
    UpdateStep.update_add_htlc c hphase
      .local amount ⟨ByteArray.empty⟩ 0 haff, ?_⟩
  exact (committedAdd_eq_updateAddHtlc c amount).symm

end LnLean.Proofs.Channel.StateTransitionTargets
