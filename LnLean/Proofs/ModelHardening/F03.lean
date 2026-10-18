import LnLean.Channel.Commitment
import LnLean.Channel.State
import LnLean.Channel.Laws
import LnLean.Proofs.Channel.ReserveProps

/-!
# LnLean.Proofs.ModelHardening.F03

English claim.  Every value subtraction in the Lightning model is a
natural-number subtraction, and Lean's `Nat.sub` truncates at zero.  The
ledger equations of BOLT 2 §3 (`update_add_htlc`) and the BOLT 3 §2
`to_remote` "remainder" rule are therefore *conditional*: they hold exactly
when the debit fits.  This module isolates that side condition once, as
`NoUnderflow` at the arithmetic level, `Affordable`/`ReserveAffordable` at the
balance level, and `CommitmentFunded` at the commitment level.  Under these
predicates it proves

1. the truncated subtraction is exact and the residual is a non-negative
   natural number that adds back to the available amount
   (`residual_add_eq`, `residual_nonneg`);
2. a committed update (the arithmetic core of `update_add_htlc`: debit one
   side of the balance and append a pending HTLC) preserves the settled plus
   in-flight ledger (`committedUpdate_preserves_ledger`);
3. the affordability invariant is stable under every legal `Step`
   (`step_preserves_affordable`, `step_preserves_ledgerBalanced`);
4. a funded commitment conserves value and its `to_remote` output is exactly
   the non-negative residual (`settledCommitment_conservation_of_funded`,
   `settledCommitment_toRemote_eq_residual`).

The unconditional committed-update ledger is **false**: with truncated
subtraction an HTLC larger than the settled balance adds in-flight value
without removing settled value.  The faithful unconditional statement is kept
below with the obligation marker, the mechanized refutation
`committedUpdate_ledger_counterexample` / `committedUpdate_preserves_ledger_not_unconditional`
records why, and the corrected theorem carries the affordability hypothesis.
The same gap is mechanized for the commitment remainder in
`zeroHtlc_conservation_not_unconditional`.

BOLT sections.
* BOLT 2 §2 (`channel_reserve_satoshis`, `02-peer-protocol.md:734-737`,
  `:811`, `:884-896`).
* BOLT 2 §3 `update_add_htlc` reserve and exposure checks
  (`02-peer-protocol.md:2739-2750`).
* BOLT 3 §2 `to_remote` as the remainder (`03-transactions.md:136-147`) and
  §4 fees (`03-transactions.md:464-576`).

rust-lightning anchors at `fe4900930c6bd5786ec4203274d7cf312776a5a6`.
* `lightning/src/ln/channel.rs:8370` (`update_add_htlc` amount/reserve
  admission), `:5880-5891` (an accepted remote HTLC must leave the
  counterparty above its reserve), `:2484-2493` (`get_available_balances`).
* `lightning/src/ln/chan_utils.rs:1887-1945` (`to_remote` remainder and
  trimming in `insert_non_htlc_outputs`).

What is NOT modelled.  `Channel.Step` still has no `update_add_htlc`
constructor, so the committed update is a named operation on the record, not
a transition; the ledger law is proved for the operation.  Fee computation
and second-stage HTLC fees are outside this module (`Fee`, `Commitment`).
-/

namespace LnLean.Proofs.ModelHardening

namespace F03

set_option autoImplicit false

open LnLean
open LnLean.Channel
open LnLean.Proofs.Channel

/-! ## 1. The reusable no-underflow predicate -/

/-- `NoUnderflow available debit` is the side condition that the truncated
natural subtraction `available - debit` is exact: the debit fits inside the
available amount.  It is deliberately a `Prop` over `Nat` so that it can be
used for balances (millisatoshis), commitment outputs (satoshis), and the
commitment-number arithmetic alike. -/
def NoUnderflow (available debit : Nat) : Prop :=
  debit ≤ available

/-- `NoUnderflow` is exactly the add-back equation for `Nat.sub`. -/
theorem noUnderflow_iff (available debit : Nat) :
    NoUnderflow available debit ↔ available - debit + debit = available := by
  unfold NoUnderflow
  omega

/-- The value left after a debit.  This is the residual the protocol calls
"whatever remains" (BOLT 3 §2 `to_remote`) or the "available balance above
the reserve" (BOLT 2 §2/LDK `get_available_balances`). -/
def residual (available debit : Nat) : Nat :=
  available - debit

/-- Under `NoUnderflow` the residual is exact: residual plus debit
reconstructs the available amount. -/
theorem residual_add_eq {available debit : Nat} (h : NoUnderflow available debit) :
    residual available debit + debit = available := by
  unfold residual NoUnderflow at *
  exact Nat.sub_add_cancel h

/-- The residual of a natural-number subtraction is always a natural number,
hence non-negative. -/
theorem residual_nonneg (available debit : Nat) : 0 ≤ residual available debit :=
  Nat.zero_le _

/-- Without the invariant the residual saturates, which is precisely the
truncated-subtraction failure: an unaffordable debit leaves zero, not a
negative remainder. -/
theorem residual_zero_of_not_noUnderflow {available debit : Nat}
    (h : ¬ NoUnderflow available debit) : residual available debit = 0 := by
  unfold residual NoUnderflow at *
  omega

/-- A debit no larger than another debit is affordable whenever the larger one
is: the invariant is monotone in the amount. -/
theorem noUnderflow_of_le {available debit debit' : Nat} (h : debit' ≤ debit)
    (hb : NoUnderflow available debit) : NoUnderflow available debit' :=
  Nat.le_trans h hb

/-! ## 2. Affordability of a balance debit -/

/-- The amount available on one side of a balance, in millisatoshis. -/
def balanceAvailableFor (b : Balance) : Direction → Nat
  | .local => b.localBalance.val
  | .remote => b.remoteBalance.val

/-- Debit one side of a balance.  This is truncated at zero; `Affordable` is
the side condition that makes it exact.  For the local side this is the
balance effect of BOLT 2 `update_add_htlc`. -/
def debitBalance (b : Balance) : Direction → Nat → Balance
  | .local, amount => { b with localBalance := ⟨b.localBalance.val - amount⟩ }
  | .remote, amount => { b with remoteBalance := ⟨b.remoteBalance.val - amount⟩ }

/-- A balance debit is affordable when the debited side covers the amount.
This is `NoUnderflow` specialised to a `Balance` and a `Direction`. -/
def Affordable (b : Balance) (side : Direction) (amountMsat : Nat) : Prop :=
  NoUnderflow (balanceAvailableFor b side) amountMsat

theorem affordable_local_iff (b : Balance) (amount : Nat) :
    Affordable b .local amount ↔ amount ≤ b.localBalance.val :=
  Iff.rfl

theorem affordable_remote_iff (b : Balance) (amount : Nat) :
    Affordable b .remote amount ↔ amount ≤ b.remoteBalance.val :=
  Iff.rfl

/-- Affordability is exactly the balance add-back equation on the debited
side. -/
theorem affordable_iff_residual (b : Balance) (side : Direction) (amount : Nat) :
    Affordable b side amount ↔
      balanceAvailableFor (debitBalance b side amount) side + amount =
        balanceAvailableFor b side := by
  cases side with
  | «local» =>
      show amount ≤ b.localBalance.val ↔
        b.localBalance.val - amount + amount = b.localBalance.val
      omega
  | «remote» =>
      show amount ≤ b.remoteBalance.val ↔
        b.remoteBalance.val - amount + amount = b.remoteBalance.val
      omega

/-- An affordable local debit removes exactly `amount` from the total
balance. -/
theorem debit_local_total {b : Balance} {amount : Nat}
    (h : amount ≤ b.localBalance.val) :
    (debitBalance b .local amount).total.val + amount = b.total.val := by
  unfold debitBalance
  simp only [Balance.total_val]
  omega

/-- An affordable remote debit removes exactly `amount` from the total
balance. -/
theorem debit_remote_total {b : Balance} {amount : Nat}
    (h : amount ≤ b.remoteBalance.val) :
    (debitBalance b .remote amount).total.val + amount = b.total.val := by
  unfold debitBalance
  simp only [Balance.total_val]
  omega

/-- An unaffordable local debit saturates the debited side at zero. -/
theorem debit_local_saturates_of_not_affordable {b : Balance} {amount : Nat}
    (h : ¬ Affordable b .local amount) :
    balanceAvailableFor (debitBalance b .local amount) .local = 0 := by
  simp only [Affordable, NoUnderflow, balanceAvailableFor] at h
  show b.localBalance.val - amount = 0
  omega

/-- Debit affordability with a reserve floor: after the debit the balance
still covers `reserveSat`.  This is the BOLT 2 `update_add_htlc` admission
rule (LDK `channel.rs:5880-5891`), expressed as a no-underflow condition. -/
def ReserveAffordable (b : Balance) (reserveSat amountMsat : Nat) : Prop :=
  reserveSat * Msat.MSAT_PER_SAT + amountMsat ≤ b.localBalance.val

/-- A reserve-affordable debit is affordable. -/
theorem reserveAffordable_imp_affordable {b : Balance} {reserveSat amount : Nat}
    (h : ReserveAffordable b reserveSat amount) : Affordable b .local amount := by
  rw [affordable_local_iff]
  have h' : reserveSat * 1000 + amount ≤ b.localBalance.val := by
    simpa [ReserveAffordable, Msat.MSAT_PER_SAT] using h
  omega

/-- A reserve-affordable debit preserves the local reserve. -/
theorem reserveAffordable_preserves_reserve {b : Balance} {reserveSat amount : Nat}
    (h : ReserveAffordable b reserveSat amount) :
    reserveSatisfied (debitBalance b .local amount) reserveSat := by
  have h' : reserveSat * 1000 + amount ≤ b.localBalance.val := by
    simpa [ReserveAffordable, Msat.MSAT_PER_SAT] using h
  show reserveSat ≤ (b.localBalance.val - amount) / 1000
  rw [Nat.le_div_iff_mul_le (by decide : 0 < 1000)]
  exact Nat.le_sub_of_add_le' (by simpa [Nat.add_comm] using h')

/-- The reserve remaining after a reserve-affordable debit is the exact
non-negative residual, and it reconstructs the balance together with the
reserve and the debit. -/
theorem reserveAffordable_residual {b : Balance} {reserveSat amount : Nat}
    (h : ReserveAffordable b reserveSat amount) :
    residual b.localBalance.val (reserveSat * Msat.MSAT_PER_SAT + amount) +
        (reserveSat * Msat.MSAT_PER_SAT + amount) = b.localBalance.val :=
  residual_add_eq (by simpa [ReserveAffordable, NoUnderflow] using h)

/-! ## 3. Channel ledger and committed updates -/

/-- The settled-plus-in-flight ledger of a channel, including the fee bucket.
This is the equation a real `update_add_htlc` must preserve. -/
def LedgerBalanced (c : Channel) (fee : Msat) : Prop :=
  c.balance.total.val + htlcInFlightValue c + fee.val = c.fundingValue.val

/-- The arithmetic core of BOLT 2 `update_add_htlc` for a local offer: debit
the local balance and append one pending `offered` HTLC.  The model's `Step`
relation does not yet contain this constructor. -/
def addLocalHtlc (c : Channel) (amount : Msat) : Channel :=
  { c with
    balance := debitBalance c.balance .local amount.val
    htlcs := c.htlcs ++
      [{ direction := Direction.local
         amount := amount
         paymentHash := ⟨ByteArray.empty⟩
         cltvExpiry := 0
         state := HTLCState.offered }] }

/-- Adding a pending local HTLC increases the in-flight bucket by exactly its
amount. -/
theorem addLocalHtlc_inFlight (c : Channel) (amount : Msat) :
    htlcInFlightValue (addLocalHtlc c amount) =
      htlcInFlightValue c + amount.val := by
  unfold addLocalHtlc htlcInFlightValue
  exact inFlightSum_append_offered c.htlcs amount

/-- Deleting an affordable amount from the local side removes exactly that
amount from the settled total, independently of the in-flight bucket. -/
theorem addLocalHtlc_balance (c : Channel) {amount : Msat}
    (h : Affordable c.balance .local amount.val) :
    (addLocalHtlc c amount).balance.total.val + amount.val =
      c.balance.total.val := by
  have hfit : amount.val ≤ c.balance.localBalance.val := h
  unfold addLocalHtlc
  exact debit_local_total hfit

/-- **Conditional committed-update ledger conservation.**  If the added local
HTLC fits inside the settled local balance (the `NoUnderflow`/`Affordable`
invariant), then the settled plus in-flight ledger with the fee bucket is
preserved.  This is the corrected form of
`committedUpdate_preserves_ledger_unconditional` below. -/
theorem committedUpdate_preserves_ledger {c : Channel} {fee amount : Msat}
    (haff : Affordable c.balance .local amount.val)
    (hledger : LedgerBalanced c fee) :
    LedgerBalanced (addLocalHtlc c amount) fee := by
  have hbal := addLocalHtlc_balance c (amount := amount) haff
  have hflight := addLocalHtlc_inFlight c amount
  have hfund : (addLocalHtlc c amount).fundingValue.val = c.fundingValue.val := rfl
  unfold LedgerBalanced at hledger ⊢
  omega

/-- The affordability invariant is preserved by every legal `Step`: the wave-A
transition relation never moves a balance. -/
theorem step_preserves_affordable {c c' : Channel} {e : ProtocolEvent}
    (h : Step c e c') {side : Direction} {amount : Nat}
    (ha : Affordable c.balance side amount) :
    Affordable c'.balance side amount := by
  cases h <;> simpa [Affordable, balanceAvailableFor] using ha

/-- In-flight value depends only on the channel's HTLC list. -/
theorem htlcInFlightValue_of_htlcs_eq {c c' : Channel} (h : c'.htlcs = c.htlcs) :
    htlcInFlightValue c' = htlcInFlightValue c := by
  unfold htlcInFlightValue
  rw [h]

/-- Every legal `Step` leaves the HTLC list unchanged. -/
theorem step_htlcs_eq {c c' : Channel} {e : ProtocolEvent} (h : Step c e c') :
    c'.htlcs = c.htlcs := by
  cases h <;> rfl

/-- The settled ledger invariant is preserved by every legal `Step`. -/
theorem step_preserves_ledgerBalanced {c c' : Channel} {e : ProtocolEvent}
    (h : Step c e c') {fee : Msat} (hl : LedgerBalanced c fee) :
    LedgerBalanced c' fee := by
  have hb : c'.balance = c.balance := by cases h <;> rfl
  have hf : c'.fundingValue = c.fundingValue := by cases h <;> rfl
  unfold LedgerBalanced at hl ⊢
  rw [htlcInFlightValue_of_htlcs_eq (step_htlcs_eq h), hb, hf]
  exact hl

/-! ## 4. Commitment remainder and conservation -/

/-- The commitment subtraction is exact when the funding covers the fee, the
holder's output, every untrimmed HTLC output, and the anchors.  This is
`NoUnderflow` for the BOLT 3 §2 balance equation. -/
def CommitmentFunded (funding toLocal fee htlcTotal anchors : Nat) : Prop :=
  NoUnderflow funding (fee + toLocal + htlcTotal + anchors)

/-- Under `CommitmentFunded`, the chained subtraction of the BOLT 3 balance
equation collapses to a single residual subtraction. -/
theorem residual_chain {funding fee toLocal htlcTotal anchors : Nat}
    (h : fee + toLocal + htlcTotal + anchors ≤ funding) :
    funding - fee - toLocal - htlcTotal - anchors =
      funding - (fee + toLocal + htlcTotal + anchors) := by
  omega

/-- The `to_remote` output of a settled commitment is exactly the residual
left by the fee, the holder output, the HTLC outputs, and the anchors. -/
theorem settledCommitment_toRemote_eq_residual
    (holder : Direction) (number funding toLocal fee contestDelay : Nat)
    (htlcs : List CommitmentHTLCOutput) (anchors : Bool)
    (h : CommitmentFunded funding toLocal fee (htlcOutputsValue htlcs)
      (if anchors then 2 * anchorOutputSat else 0)) :
    (settledCommitment holder number funding toLocal fee contestDelay htlcs
      anchors).toRemoteSat =
      residual funding (fee + toLocal + htlcOutputsValue htlcs +
        (if anchors then 2 * anchorOutputSat else 0)) := by
  have hle : fee + toLocal + htlcOutputsValue htlcs +
      (if anchors then 2 * anchorOutputSat else 0) ≤ funding := by
    simpa [CommitmentFunded, NoUnderflow] using h
  unfold settledCommitment residual
  exact residual_chain hle

/-- The `to_remote` residual adds back to the funding value, so it is the
exact non-negative remainder rather than a truncated zero. -/
theorem settledCommitment_residual_add
    (holder : Direction) (number funding toLocal fee contestDelay : Nat)
    (htlcs : List CommitmentHTLCOutput) (anchors : Bool)
    (h : CommitmentFunded funding toLocal fee (htlcOutputsValue htlcs)
      (if anchors then 2 * anchorOutputSat else 0)) :
    (settledCommitment holder number funding toLocal fee contestDelay htlcs
        anchors).toRemoteSat +
        (fee + toLocal + htlcOutputsValue htlcs +
          (if anchors then 2 * anchorOutputSat else 0)) = funding := by
  have hres := settledCommitment_toRemote_eq_residual holder number funding
    toLocal fee contestDelay htlcs anchors h
  rw [hres]
  exact residual_add_eq (by simpa [CommitmentFunded, NoUnderflow] using h)

/-- The residual commitment output is non-negative (it is a `Nat`). -/
theorem settledCommitment_toRemote_nonneg
    (holder : Direction) (number funding toLocal fee contestDelay : Nat)
    (htlcs : List CommitmentHTLCOutput) (anchors : Bool) :
    0 ≤ (settledCommitment holder number funding toLocal fee contestDelay
      htlcs anchors).toRemoteSat :=
  Nat.zero_le _

/-- **Commitment conservation under the funded invariant.**  This is exactly
`conservation_with_htlcs` with its hypothesis packaged as `CommitmentFunded`. -/
theorem settledCommitment_conservation_of_funded
    (holder : Direction) (number funding toLocal fee contestDelay : Nat)
    (htlcs : List CommitmentHTLCOutput) (anchors : Bool)
    (h : CommitmentFunded funding toLocal fee (htlcOutputsValue htlcs)
      (if anchors then 2 * anchorOutputSat else 0)) :
    (settledCommitment holder number funding toLocal fee contestDelay htlcs
      anchors).totalOutputValue + fee = funding := by
  apply conservation_with_htlcs
  simpa [CommitmentFunded, NoUnderflow] using h

/-- The zero-HTLC special case of the funded conservation law. -/
theorem zeroHtlc_conservation_of_funded
    (holder : Direction) (number funding toLocal fee contestDelay : Nat)
    (anchors : Bool)
    (h : CommitmentFunded funding toLocal fee 0
      (if anchors then 2 * anchorOutputSat else 0)) :
    (zeroHtlcCommitment holder number funding toLocal fee contestDelay
      anchors).totalOutputValue + fee = funding := by
  apply zeroHtlc_conservation
  simpa [CommitmentFunded, NoUnderflow] using h

/-! ## 5. The truncated-subtraction counterexamples -/

/-- A concrete channel with zero funding and zero balances, used by the
negative results. -/
def zeroChannel : Channel :=
  let p : ChannelParams :=
    { dustLimitSat := 0
      channelReserveSat := 0
      toSelfDelay := 0
      maxHtlcValue := ⟨0⟩
      htlcMinimum := ⟨0⟩
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
    fundingValue := ⟨0⟩
    localEndpoint := e
    remoteEndpoint := e
    phase := ChannelPhase.negotiating
    localCommitmentNumber := 0
    remoteCommitmentNumber := 0
    balance := { localBalance := ⟨0⟩, remoteBalance := ⟨0⟩ }
    htlcs := [] }

/-- The zero channel satisfies the ledger equation. -/
theorem zeroChannel_ledger : LedgerBalanced zeroChannel ⟨0⟩ := by
  simp [LedgerBalanced, zeroChannel, htlcInFlightValue, Balance.total_val]

/-- The same channel rejects a 1-msat local HTLC by the affordability
predicate. -/
theorem zeroChannel_not_affordable :
    ¬ Affordable zeroChannel.balance .local 1 := by
  simp [Affordable, NoUnderflow, balanceAvailableFor, zeroChannel]

/-- **Mechanized counterexample to the unconditional committed-update
ledger.**  With zero balances, a 1-msat local HTLC is not affordable; the
truncated debit leaves the settled balance at zero while the in-flight bucket
grows by one, so the ledger equation fails. -/
theorem committedUpdate_ledger_counterexample :
    ¬ LedgerBalanced (addLocalHtlc zeroChannel ⟨1⟩) ⟨0⟩ := by
  simp [LedgerBalanced, addLocalHtlc, zeroChannel, debitBalance,
    htlcInFlightValue, Balance.total_val]

/-- The negation of the unconditional committed-update ledger is a theorem:
no such law can hold for arbitrary amounts. -/
theorem committedUpdate_preserves_ledger_not_unconditional :
    ¬ (∀ (c : Channel) (fee amount : Msat),
        LedgerBalanced c fee → LedgerBalanced (addLocalHtlc c amount) fee) := by
  intro h
  exact committedUpdate_ledger_counterexample
    (h zeroChannel ⟨0⟩ ⟨1⟩ zeroChannel_ledger)

/-- **Faithful unconditional statement, kept as an open obligation.**  Without
the affordability hypothesis this is false by
`committedUpdate_ledger_counterexample`; the corrected conditional theorem is
`committedUpdate_preserves_ledger`. -/
theorem committedUpdate_preserves_ledger_unconditional
    (c : Channel) (fee amount : Msat) (hledger : LedgerBalanced c fee) :
    LedgerBalanced (addLocalHtlc c amount) fee := by
  -- OBLIGATION: LN-WF-F03
  sorry

/-- The arithmetic invariant is not vacuous: residual add-back fails exactly
when the debit does not fit. -/
theorem residual_add_eq_not_unconditional :
    ¬ (∀ available debit : Nat, residual available debit + debit = available) := by
  intro h
  have h01 : residual 0 1 + 1 = 0 := h 0 1
  simp [residual] at h01

/-- **Mechanized counterexample to unconditional commitment conservation.**
A zero-funding commitment with a 1-sat fee has `to_remote = 0` by truncation,
so outputs plus fee exceed the funding value.  `CommitmentFunded` is exactly
the missing side condition. -/
theorem zeroHtlc_conservation_not_unconditional :
    ∃ (holder : Direction) (number funding toLocal fee contestDelay : Nat)
        (anchors : Bool),
      (zeroHtlcCommitment holder number funding toLocal fee contestDelay
        anchors).totalOutputValue + fee ≠ funding := by
  refine ⟨Direction.local, 0, 0, 0, 1, 0, false, ?_⟩
  simp [zeroHtlcCommitment, Commitment.totalOutputValue,
    Commitment.htlcOutputValue, Commitment.anchorOutputValue, htlcOutputsValue]

/-- The funded invariant is satisfiable: 1000 sat of funding cover a 100 sat
fee, a 400 sat holder output, no HTLCs, and no anchors. -/
theorem commitmentFunded_witness : CommitmentFunded 1000 400 100 0 0 := by
  unfold CommitmentFunded NoUnderflow
  decide

/-- A concrete instance of the conditional theorem: the zero channel can add
a zero-value HTLC and its ledger still balances. -/
theorem zeroChannel_add_zero_ledger :
    LedgerBalanced (addLocalHtlc zeroChannel ⟨0⟩) ⟨0⟩ :=
  committedUpdate_preserves_ledger
    (by simp [Affordable, NoUnderflow, balanceAvailableFor, zeroChannel])
    zeroChannel_ledger

end F03

end LnLean.Proofs.ModelHardening
