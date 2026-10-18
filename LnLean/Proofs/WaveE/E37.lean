import LnLean.Channel.Commitment
import LnLean.Channel.State
import LnLean.Channel.Laws
import LnLean.Proofs.Channel.ReserveProps

/-!
# LnLean.Proofs.WaveE.E37

English claim (obligation `LN-CH-101`).  A committed update --- a local
`update_add_htlc`, modelled as dropping the offered amount from the settled
local balance and appending one pending `offered` HTLC --- preserves the
channel ledger

`settled local + settled remote + pending in-flight + fee = funding`

**only when the offered amount is affordable**, i.e. in particular when it is
covered by the settled local balance.  The unguarded statement is false in the
current model: the balance drop is truncated natural subtraction, so an amount
larger than the local balance adds in-flight value without removing settled
value.  `LnLean.Proofs.Channel.ReserveProps` records that false statement as
an open obligation; this module replaces the gap with a proved negative result, an
affordability predicate, and the sharp conditional theorem.

What is delivered here.

1. `ledgerValue` / `pendingValue`: the settled-plus-in-flight ledger and the
   pending HTLC value.  The pending value is definitionally the Wave-C
   `htlcInFlightValue`; `waveE_e37_pendingValue_eq_inFlight` records that.
2. `AffordableCommittedAdd`: the BOLT 2 affordability checks for a committed
   local add that the current model can express —
   * the amount fits the settled local balance (no truncated subtraction);
   * the post-update local balance still meets the peer's channel reserve;
   * the amount meets the receiver's `htlc_minimum_msat`;
   * the total in-flight value stays within the receiver's
     `max_htlc_value_in_flight_msat`.
3. `waveE_e37_affordable_preserves_ledger`: ledger conservation under the
   predicate, plus `waveE_e37_affordable_preserves_ledger_delta` (the same
   equation without assuming the old ledger equation).
4. `waveE_e37_ledger_iff_covered`: a *sharp* result — for the single-add
   update shape, `amount.val ≤ localBalance.val` is necessary **and**
   sufficient for ledger conservation.  The other affordability conjuncts are
   policy checks, not needed for the arithmetic.
5. `waveE_e37_affordable_preserves_reserve` and
   `waveE_e37_affordable_preserves_exposure`: affordability also keeps the
   Wave-C `ReserveInvariant` and the receiver's in-flight bound, bundled in
   `waveE_e37_affordable_preserves_accounting`.
6. `waveE_e37_unguarded_ledger_counterexample`,
   `waveE_e37_unguarded_claim_false`, and
   `waveE_e37_covered_can_break_reserve`: mechanized counterexamples showing
   that the unguarded ledger claim fails and that "covered" alone does not
   preserve the reserve.

BOLT anchors.
* BOLT 2 §3 `update_add_htlc` (`02-peer-protocol.md:2739-2750`) and the
  reserve rationale (`02-peer-protocol.md:884-896`).
* BOLT 2 §2 `open_channel` / `accept_channel` fields for
  `channel_reserve_satoshis`, `htlc_minimum_msat`, and
  `max_htlc_value_in_flight_msat` (`02-peer-protocol.md:680-760`,
  `:907-960`).
* LDK anchor: `lightning/src/ln/channel.rs:5880-5891` (an accepted remote
  HTLC must leave the counterparty above its selected reserve).

What is NOT modelled.
* A `Step` / `update_add_htlc` constructor: `LnLean.Channel.State.Step` still
  changes only phase, commitment counters, and feerate.  The update shape is
  therefore an explicit successor function `committedAdd`, and affordability
  is a predicate on the pre-state, not a protocol-side check.
* The net-of-second-stage-fee HTLC dust test (the known
  `gross_dust_rule_insufficient` gap in `ReserveProps`).  Dust affordability
  is not claimed here.
* Fee accounting for the added HTLC weight; `fee` is held fixed, as in
  `ReserveProps.committed_update_preserves_ledger_of_le`.
-/

namespace LnLean.Proofs.WaveE.E37

set_option autoImplicit false

open LnLean
open LnLean.Channel

-- OBLIGATION: LN-WE-E37

/-! ## The ledger and the pending value -/

/-- Pending HTLC value: the sum of the amounts of the `offered` and
`received` HTLCs of a channel, in millisatoshis. -/
def pendingValue (c : Channel) : Nat :=
  ((c.htlcs.filter
      (fun h => h.state = HTLCState.offered ∨ h.state = HTLCState.received)).map
    (fun h => h.amount.val)).sum

/-- The pending value is the Wave-C `htlcInFlightValue`; the two lanes agree
definitionally. -/
theorem waveE_e37_pendingValue_eq_inFlight (c : Channel) :
    pendingValue c = LnLean.Proofs.Channel.htlcInFlightValue c := rfl

/-- Settled-plus-in-flight ledger of a channel at a fixed on-chain fee:
both settled balances, the pending HTLC value, and the fee. -/
def ledgerValue (c : Channel) (fee : Msat) : Nat :=
  c.balance.localBalance.val + c.balance.remoteBalance.val + pendingValue c +
    fee.val

/-- The ledger in the `Balance.total` form used by
`ReserveProps.committed_update_preserves_ledger_of_le`. -/
theorem waveE_e37_ledgerValue_eq_total (c : Channel) (fee : Msat) :
    ledgerValue c fee =
      c.balance.total.val + LnLean.Proofs.Channel.htlcInFlightValue c +
        fee.val := by
  rw [ledgerValue, waveE_e37_pendingValue_eq_inFlight]
  rfl

/-! ## The committed update -/

/-- The settled local balance after a committed local add.  This is the
Wave-C `spendLocalBalance`, reused so that the truncation behaviour is the
same in both lanes. -/
abbrev spendLocal := LnLean.Proofs.Channel.spendLocalBalance

/-- The successor channel of a committed local `update_add_htlc`: drop the
offered amount from the settled local balance and append one pending
`offered` HTLC.  The fee, the funding value, and the endpoints are
unchanged. -/
def committedAdd (c : Channel) (amount : Msat) : Channel :=
  { c with
    balance := spendLocal c.balance amount.val
    htlcs := c.htlcs ++
      [{ direction := Direction.local
         amount := amount
         paymentHash := ⟨ByteArray.empty⟩
         cltvExpiry := 0
         state := HTLCState.offered }] }

/-- Appending one pending local HTLC raises the pending value by exactly its
amount. -/
theorem waveE_e37_pendingValue_committedAdd (c : Channel) (amount : Msat) :
    pendingValue (committedAdd c amount) = pendingValue c + amount.val := by
  unfold committedAdd pendingValue
  rw [List.filter_append, List.map_append, List.sum_append]
  simp

/-! ## Affordability -/

/-- BOLT 2 affordability of a committed local HTLC add.  `c` is the pre-state
and `amount` the amount of the `update_add_htlc`.

* `fitsSettled`: the offered amount is at most the settled local balance, so
  the committed balance drop does not truncate.
* `leavesReserve`: after the drop the local balance still meets the reserve
  the *remote* endpoint advertised (`localReserveSat`), in millisatoshis.
* `atLeastHtlcMinimum`: the amount is at least the receiver's
  `htlc_minimum_msat`.
* `withinReceiverInFlight`: the total pending value after the add stays
  within the receiver's `max_htlc_value_in_flight_msat`.  This also implies
  the per-HTLC cap, because `pendingValue c` is non-negative. -/
structure AffordableCommittedAdd (c : Channel) (amount : Msat) : Prop where
  /-- The amount is covered by the settled local balance. -/
  fitsSettled : amount.val ≤ c.balance.localBalance.val
  /-- The post-update local balance still meets the applicable reserve. -/
  leavesReserve :
    LnLean.Proofs.Channel.localReserveSat c * Msat.MSAT_PER_SAT + amount.val ≤
      c.balance.localBalance.val
  /-- The receiver's `htlc_minimum_msat` is respected. -/
  atLeastHtlcMinimum :
    c.remoteEndpoint.params.htlcMinimum.val ≤ amount.val
  /-- The receiver's `max_htlc_value_in_flight_msat` is respected after the
  add. -/
  withinReceiverInFlight :
    pendingValue c + amount.val ≤ c.remoteEndpoint.params.maxHtlcValue.val

/-- Affordability implies the arithmetic coverage condition. -/
theorem waveE_e37_affordable_fits {c : Channel} {amount : Msat}
    (h : AffordableCommittedAdd c amount) :
    amount.val ≤ c.balance.localBalance.val :=
  h.fitsSettled

/-- Affordability implies that the post-update local balance still meets the
reserve; this is the component used by the reserve proof. -/
theorem waveE_e37_affordable_leaves_reserve {c : Channel} {amount : Msat}
    (h : AffordableCommittedAdd c amount) :
    LnLean.Proofs.Channel.localReserveSat c * Msat.MSAT_PER_SAT + amount.val ≤
      c.balance.localBalance.val :=
  h.leavesReserve

/-! ## Ledger conservation under coverage and under affordability -/

/-- **Ledger delta under a covered add.**  If the amount fits the settled
local balance, then the committed add leaves `ledgerValue` unchanged.  This
does not assume that the pre-state ledger equals the funding value. -/
theorem waveE_e37_covered_preserves_ledger_delta (c : Channel) (fee amount : Msat)
    (h_fits : amount.val ≤ c.balance.localBalance.val) :
    ledgerValue (committedAdd c amount) fee = ledgerValue c fee := by
  have hpend := waveE_e37_pendingValue_committedAdd c amount
  have hbal : (committedAdd c amount).balance.localBalance.val +
      (committedAdd c amount).balance.remoteBalance.val =
      c.balance.localBalance.val + c.balance.remoteBalance.val - amount.val := by
    simp [committedAdd, spendLocal, LnLean.Proofs.Channel.spendLocalBalance]
    omega
  have hS : amount.val ≤
      c.balance.localBalance.val + c.balance.remoteBalance.val := by omega
  unfold ledgerValue
  rw [hbal, hpend]
  omega

/-- **Ledger conservation under a covered add.**  If the pre-state ledger
equals the funding value and the amount is covered by the settled local
balance, the successor ledger still equals the funding value. -/
theorem waveE_e37_covered_preserves_ledger (c : Channel) (fee amount : Msat)
    (h_fits : amount.val ≤ c.balance.localBalance.val)
    (h_old : ledgerValue c fee = c.fundingValue.val) :
    ledgerValue (committedAdd c amount) fee =
      (committedAdd c amount).fundingValue.val := by
  rw [waveE_e37_covered_preserves_ledger_delta c fee amount h_fits]
  simpa [committedAdd] using h_old

/-- **Ledger conservation under an affordable add.**  The named affordability
predicate of this module supplies the coverage condition. -/
theorem waveE_e37_affordable_preserves_ledger (c : Channel) (fee amount : Msat)
    (h_aff : AffordableCommittedAdd c amount)
    (h_old : ledgerValue c fee = c.fundingValue.val) :
    ledgerValue (committedAdd c amount) fee =
      (committedAdd c amount).fundingValue.val :=
  waveE_e37_covered_preserves_ledger c fee amount h_aff.fitsSettled h_old

/-- **Sharpness of the coverage guard.**  For the single-add update shape and
a pre-state whose ledger equals the funding value, the successor ledger
equals the funding value **if and only if** the amount is covered by the
settled local balance.  Truncated subtraction is the only obstruction: if
`amount.val > localBalance.val` the drop truncates to zero while the pending
value grows by the full amount, so the ledger grows by
`amount.val - localBalance.val > 0`. -/
theorem waveE_e37_ledger_iff_covered (c : Channel) (fee amount : Msat)
    (h_old : ledgerValue c fee = c.fundingValue.val) :
    ledgerValue (committedAdd c amount) fee =
        (committedAdd c amount).fundingValue.val ↔
      amount.val ≤ c.balance.localBalance.val := by
  constructor
  · intro hnew
    apply Nat.le_of_not_gt
    intro hgt
    have hzero : c.balance.localBalance.val - amount.val = 0 :=
      Nat.sub_eq_zero_of_le (Nat.le_of_lt hgt)
    have hold :
        c.balance.localBalance.val + c.balance.remoteBalance.val +
            pendingValue c + fee.val = c.fundingValue.val := h_old
    have hnew' :
        (c.balance.localBalance.val - amount.val) + c.balance.remoteBalance.val +
            (pendingValue c + amount.val) + fee.val = c.fundingValue.val := by
      have h' := hnew
      unfold ledgerValue at h'
      rw [waveE_e37_pendingValue_committedAdd c amount] at h'
      simp only [committedAdd, spendLocal,
        LnLean.Proofs.Channel.spendLocalBalance] at h'
      exact h'
    rw [hzero] at hnew'
    omega
  · intro h_fits
    exact waveE_e37_covered_preserves_ledger c fee amount h_fits h_old

/-! ## The accounting invariant preserved by an affordable add -/

/-- The channel accounting invariant of this module: ledger conservation, the
Wave-C `ReserveInvariant`, and the receiver's in-flight exposure bound. -/
def ChannelAccountingInvariant (c : Channel) (fee : Msat) : Prop :=
  ledgerValue c fee = c.fundingValue.val ∧
    LnLean.Proofs.Channel.ReserveInvariant c ∧
      pendingValue c ≤ c.remoteEndpoint.params.maxHtlcValue.val

/-- An affordable add preserves both reserve balances.  The local check is
`ReserveProps.spendLocal_preserves_reserve`; the remote balance is untouched
by a local add. -/
theorem waveE_e37_affordable_preserves_reserve {c : Channel} {amount : Msat}
    (h_aff : AffordableCommittedAdd c amount)
    (hres : LnLean.Proofs.Channel.ReserveInvariant c) :
    LnLean.Proofs.Channel.ReserveInvariant (committedAdd c amount) := by
  rcases hres with ⟨hloc, hrem⟩
  refine ⟨?_, ?_⟩
  · have h := LnLean.Proofs.Channel.spendLocal_preserves_reserve
        (b := c.balance)
        (reserve := LnLean.Proofs.Channel.localReserveSat c)
        (amountMsat := amount.val) h_aff.leavesReserve
    simpa [committedAdd, spendLocal, LnLean.Proofs.Channel.ReserveInvariant,
      LnLean.Proofs.Channel.localReserveSat] using h
  · simpa [committedAdd, spendLocal, LnLean.Proofs.Channel.spendLocalBalance,
      LnLean.Proofs.Channel.ReserveInvariant,
      LnLean.Proofs.Channel.remoteReserveSat, Balance.remoteSat] using hrem

/-- An affordable add keeps the receiver's total in-flight exposure within
its advertised `max_htlc_value_in_flight_msat`. -/
theorem waveE_e37_affordable_preserves_exposure {c : Channel} {amount : Msat}
    (h_aff : AffordableCommittedAdd c amount) :
    pendingValue (committedAdd c amount) ≤
      c.remoteEndpoint.params.maxHtlcValue.val := by
  rw [waveE_e37_pendingValue_committedAdd]
  exact h_aff.withinReceiverInFlight

/-- **Affordable committed updates preserve the accounting invariant.** -/
theorem waveE_e37_affordable_preserves_accounting (c : Channel) (fee amount : Msat)
    (h_aff : AffordableCommittedAdd c amount)
    (hinv : ChannelAccountingInvariant c fee) :
    ChannelAccountingInvariant (committedAdd c amount) fee := by
  rcases hinv with ⟨hled, hres, _hexp⟩
  exact ⟨waveE_e37_affordable_preserves_ledger c fee amount h_aff hled,
    waveE_e37_affordable_preserves_reserve h_aff hres,
    waveE_e37_affordable_preserves_exposure h_aff⟩

/-! ## Agreement with the Wave-C conditional theorem -/

/-- The ledger theorem of this module is the same statement as
`ReserveProps.committed_update_preserves_ledger_of_le`: its `h_fits`
hypothesis is exactly `fitsSettled`, and its `h_step` shape is the unfolding
of `committedAdd`.  This is a consistency check between the two waves, not an
extra hypothesis. -/
theorem waveE_e37_agrees_with_reserveProps (c : Channel) (fee amount : Msat)
    (h_fits : amount.val ≤ c.balance.localBalance.val)
    (h_old : ledgerValue c fee = c.fundingValue.val) :
    (committedAdd c amount).balance.total.val +
        LnLean.Proofs.Channel.htlcInFlightValue (committedAdd c amount) +
          fee.val =
      (committedAdd c amount).fundingValue.val := by
  have h_old' : c.balance.total.val +
      LnLean.Proofs.Channel.htlcInFlightValue c + fee.val =
        c.fundingValue.val := by
    rw [← waveE_e37_ledgerValue_eq_total]
    exact h_old
  exact LnLean.Proofs.Channel.committed_update_preserves_ledger_of_le c
    (committedAdd c amount) fee amount h_fits h_old' rfl

/-! ## Counterexamples -/

/-- A zero-HTLC testing channel with the given settled balances (msat),
funding value (msat), and the reserve (sat), `htlc_minimum_msat`, and
`max_htlc_value_in_flight_msat` advertised by both endpoints. -/
def testChannel (localMsat remoteMsat fundingMsat reserveSat htlcMinMsat
    maxHtlcMsat : Nat) : Channel :=
  let p : ChannelParams :=
    { dustLimitSat := 0
      channelReserveSat := reserveSat
      toSelfDelay := 0
      maxHtlcValue := ⟨maxHtlcMsat⟩
      htlcMinimum := ⟨htlcMinMsat⟩
      feerate := ⟨0⟩
      anchorOutputs := false }
  let e : Endpoint :=
    { nodeId := ⟨ByteArray.empty⟩
      fundingPubKey := ⟨ByteArray.empty⟩
      paymentBasepoint := ⟨ByteArray.empty⟩
      delayedPaymentBasepoint := ⟨ByteArray.empty⟩
      params := p }
  { channelId := ⟨ByteArray.empty⟩
    funding := ⟨ByteArray.empty, 0⟩
    fundingValue := ⟨fundingMsat⟩
    localEndpoint := e
    remoteEndpoint := e
    phase := ChannelPhase.normal
    localCommitmentNumber := 0
    remoteCommitmentNumber := 0
    balance := { localBalance := ⟨localMsat⟩, remoteBalance := ⟨remoteMsat⟩ }
    htlcs := [] }

/-! ## A concrete affordable update (non-vacuity) -/

/-- The affordability predicate is inhabited and the conservation theorem
applies to a concrete update: a 500-msat local HTLC in a channel with a
1000-msat settled local balance, zero reserve, a 1-msat minimum, and a
1000-msat in-flight cap. -/
theorem waveE_e37_affordable_witness :
    ∃ (c : Channel) (fee amount : Msat),
      AffordableCommittedAdd c amount ∧
        ledgerValue c fee = c.fundingValue.val ∧
          ledgerValue (committedAdd c amount) fee =
            (committedAdd c amount).fundingValue.val := by
  let c := testChannel 1000 1000 2000 0 1 1000
  let fee : Msat := ⟨0⟩
  let amount : Msat := ⟨500⟩
  have haff : AffordableCommittedAdd c amount := by
    constructor
    · simp [c, testChannel, amount]
    · simp [c, testChannel, amount, LnLean.Proofs.Channel.localReserveSat]
    · simp [c, testChannel, amount]
    · simp [c, testChannel, amount, pendingValue]
  have hled : ledgerValue c fee = c.fundingValue.val := by
    simp [c, testChannel, fee, ledgerValue, pendingValue]
  exact ⟨c, fee, amount, haff, hled,
    waveE_e37_affordable_preserves_ledger c fee amount haff hled⟩

/-- **Counterexample to the unguarded committed-update ledger.**  A
fully-funded channel (`remote = funding = 1000` msat, `local = 0`) satisfies
the ledger equation, but adding a 1-msat local HTLC is not affordable: the
truncated local drop stays at zero while the pending value grows to 1, so the
successor ledger is 1001, not 1000. -/
theorem waveE_e37_unguarded_ledger_counterexample :
    ∃ (c : Channel) (fee amount : Msat),
      ledgerValue c fee = c.fundingValue.val ∧
        ¬ AffordableCommittedAdd c amount ∧
          ledgerValue (committedAdd c amount) fee ≠
            (committedAdd c amount).fundingValue.val := by
  let c := testChannel 0 1000 1000 0 0 0
  let fee : Msat := ⟨0⟩
  let amount : Msat := ⟨1⟩
  refine ⟨c, fee, amount, ?_, ?_, ?_⟩
  · simp [c, testChannel, fee, ledgerValue, pendingValue]
  · intro h
    have hle := h.leavesReserve
    simp [c, testChannel, amount, LnLean.Proofs.Channel.localReserveSat] at hle
  · simp [c, testChannel, fee, amount, ledgerValue, pendingValue, committedAdd,
      spendLocal, LnLean.Proofs.Channel.spendLocalBalance]

/-- The unguarded ledger statement as a closed proposition: every committed
local add, with no affordability hypothesis, preserves the ledger. -/
def UnguardedLedgerClaim : Prop :=
  ∀ (c : Channel) (fee amount : Msat),
    ledgerValue c fee = c.fundingValue.val →
      ledgerValue (committedAdd c amount) fee =
        (committedAdd c amount).fundingValue.val

/-- **The unguarded claim is false.**  This is the mechanized negation of the
`LN-CH-101` statement without an affordability guard. -/
theorem waveE_e37_unguarded_claim_false : ¬ UnguardedLedgerClaim := by
  intro h
  obtain ⟨c, fee, amount, hold, _hnot, hbad⟩ :=
    waveE_e37_unguarded_ledger_counterexample
  exact hbad (h c fee amount hold)

/-- **Coverage alone does not preserve the reserve.**  A channel that meets
both reserves, with `local = 500` sat and a 400-sat reserve, conserves the
ledger when 200 sat are committed locally, but the post-update local balance
is only 300 sat, below the 400-sat reserve.  This is exactly the extra
`leavesReserve` conjunct of `AffordableCommittedAdd`; the ledger equation by
itself cannot see it. -/
theorem waveE_e37_covered_can_break_reserve :
    ∃ (c : Channel) (fee amount : Msat),
      amount.val ≤ c.balance.localBalance.val ∧
        LnLean.Proofs.Channel.ReserveInvariant c ∧
        ledgerValue c fee = c.fundingValue.val ∧
          ledgerValue (committedAdd c amount) fee =
            (committedAdd c amount).fundingValue.val ∧
          ¬ LnLean.Proofs.Channel.ReserveInvariant (committedAdd c amount) := by
  let c := testChannel 500000 500000 1000000 400 0 0
  let fee : Msat := ⟨0⟩
  let amount : Msat := ⟨200000⟩
  have hfits : amount.val ≤ c.balance.localBalance.val := by
    simp [c, testChannel, amount]
  have hled : ledgerValue c fee = c.fundingValue.val := by
    simp [c, testChannel, fee, ledgerValue, pendingValue]
  have hres0 : LnLean.Proofs.Channel.ReserveInvariant c := by
    simp [c, testChannel, LnLean.Proofs.Channel.ReserveInvariant,
      reserveSatisfied, LnLean.Proofs.Channel.localReserveSat,
      LnLean.Proofs.Channel.remoteReserveSat, Balance.localSat,
      Balance.remoteSat, Msat.toSatFloor, Msat.MSAT_PER_SAT]
  refine ⟨c, fee, amount, hfits, hres0, hled, ?_, ?_⟩
  · exact waveE_e37_covered_preserves_ledger c fee amount hfits hled
  · intro h
    have hres : 400 ≤
        (committedAdd c amount).balance.localSat := by
      simpa [LnLean.Proofs.Channel.ReserveInvariant, reserveSatisfied,
        c, testChannel, committedAdd, spendLocal,
        LnLean.Proofs.Channel.localReserveSat, Balance.localSat] using h.1
    have hbal : (committedAdd c amount).balance.localSat = 300 := by
      simp [c, testChannel, amount, committedAdd, spendLocal,
        LnLean.Proofs.Channel.spendLocalBalance, Balance.localSat,
        Msat.toSatFloor, Msat.MSAT_PER_SAT]
    omega

end LnLean.Proofs.WaveE.E37
