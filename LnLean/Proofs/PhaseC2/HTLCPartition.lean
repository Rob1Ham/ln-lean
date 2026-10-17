import LnLean.Channel.Types

/-!
# LnLean.Proofs.PhaseC2.HTLCPartition

English claim.  The HTLCs of a channel state divide by lifecycle state into
four disjoint buckets: `offered`, `received`, `settled` (`fulfilled` or
`failed`) and `removed`.  The pending bucket is exactly the union of the
offered and received buckets, so its amount sum is the sum of those two
buckets; all four bucket sums together equal the amount sum of the whole
list.  Appending one offered HTLC increases the in-flight (pending) bucket by
exactly its amount.  Consequently a modelled `update_add_htlc` step that
removes the amount from the settled local balance and appends an offered
record leaves the settled-plus-in-flight ledger unchanged, which is the
identity used by `LnLean.Proofs.Channel.ReserveProps`.

BOLT anchors.
* BOLT 2 `update_add_htlc`: `refs/bolts/02-peer-protocol.md:2772` (an added
  HTLC has an amount, a direction, a payment hash, a CLTV expiry, and an id).
* BOLT 2 `update_fulfill_htlc` / `update_fail_htlc`:
  `refs/bolts/02-peer-protocol.md:2913` (a live HTLC moves to a settled state).
* BOLT 2 removing an HTLC: `refs/bolts/02-peer-protocol.md:3097` (settled
  HTLCs are removed from the commitment set).
* BOLT 3 HTLC outputs and trimming: `refs/bolts/03-transactions.md:305`.

rust-lightning anchors (commit fe49009).
* `lightning/src/ln/chan_utils.rs:716` (`HTLCOutputInCommitment`: the
  `offered` flag, amount, payment hash, and CLTV expiry).
* `lightning/src/ln/chan_utils.rs:735` (`to_bitcoin_amount`).

What is NOT modelled.
* Wire encoding/decoding, onion payloads, and MPP splitting.
* SHA-256, signatures, and script execution: the state tags are given.
* On-chain output construction/fee estimation.  This module proves only the
  list-level partition and the settled/in-flight Nat arithmetic.
* The definitions `htlcInFlightValue` and `spendLocalBalance` below mirror
  the identically named definitions in `LnLean.Proofs.Channel.ReserveProps`;
  they are repeated here so this module depends only on the channel
  vocabulary, not on the reserve proof module's transition obligations.
-/

namespace LnLean.Proofs.PhaseC2.HTLCPartition

open LnLean
open LnLean.Channel

set_option autoImplicit false

/-! ## 1. State buckets -/

/-- An HTLC is in the offered bucket exactly when its state is `offered`. -/
def isOfferedHTLC (h : HTLC) : Bool := h.state = HTLCState.offered

/-- An HTLC is in the received bucket exactly when its state is `received`. -/
def isReceivedHTLC (h : HTLC) : Bool := h.state = HTLCState.received

/-- The settled bucket: fulfilled or failed HTLCs no longer carry in-flight
value but have not yet been removed from the channel record. -/
def isSettledHTLC (h : HTLC) : Bool :=
  h.state = HTLCState.fulfilled ∨ h.state = HTLCState.failed

/-- The removed bucket. -/
def isRemovedHTLC (h : HTLC) : Bool := h.state = HTLCState.removed

/-- The pending (in-flight) bucket: offered or received. -/
def isPendingHTLC (h : HTLC) : Bool :=
  h.state = HTLCState.offered ∨ h.state = HTLCState.received

/-- HTLCs in the offered state. -/
def offeredHTLCs (l : List HTLC) : List HTLC := l.filter isOfferedHTLC

/-- HTLCs in the received state. -/
def receivedHTLCs (l : List HTLC) : List HTLC := l.filter isReceivedHTLC

/-- HTLCs in a settled state (`fulfilled` or `failed`). -/
def settledHTLCs (l : List HTLC) : List HTLC := l.filter isSettledHTLC

/-- HTLCs in the removed state. -/
def removedHTLCs (l : List HTLC) : List HTLC := l.filter isRemovedHTLC

/-- HTLCs still in flight (`offered` or `received`). -/
def pendingHTLCs (l : List HTLC) : List HTLC := l.filter isPendingHTLC

/-! ## 2. Membership and disjointness -/

theorem mem_offeredHTLCs {l : List HTLC} {h : HTLC} :
    h ∈ offeredHTLCs l ↔ h ∈ l ∧ h.state = HTLCState.offered := by
  unfold offeredHTLCs isOfferedHTLC
  rw [List.mem_filter]
  simp

theorem mem_receivedHTLCs {l : List HTLC} {h : HTLC} :
    h ∈ receivedHTLCs l ↔ h ∈ l ∧ h.state = HTLCState.received := by
  unfold receivedHTLCs isReceivedHTLC
  rw [List.mem_filter]
  simp

theorem mem_settledHTLCs {l : List HTLC} {h : HTLC} :
    h ∈ settledHTLCs l ↔
      h ∈ l ∧ (h.state = HTLCState.fulfilled ∨ h.state = HTLCState.failed) := by
  unfold settledHTLCs isSettledHTLC
  rw [List.mem_filter]
  simp

theorem mem_removedHTLCs {l : List HTLC} {h : HTLC} :
    h ∈ removedHTLCs l ↔ h ∈ l ∧ h.state = HTLCState.removed := by
  unfold removedHTLCs isRemovedHTLC
  rw [List.mem_filter]
  simp

theorem mem_pendingHTLCs {l : List HTLC} {h : HTLC} :
    h ∈ pendingHTLCs l ↔
      h ∈ l ∧ (h.state = HTLCState.offered ∨ h.state = HTLCState.received) := by
  unfold pendingHTLCs isPendingHTLC
  rw [List.mem_filter]
  simp

/-- The pending list is the disjoint union of the offered and received
buckets: every pending member is in exactly one of them. -/
theorem pendingHTLCs_partition (l : List HTLC) (h : HTLC) :
    h ∈ pendingHTLCs l ↔ h ∈ offeredHTLCs l ∨ h ∈ receivedHTLCs l := by
  rw [mem_pendingHTLCs, mem_offeredHTLCs, mem_receivedHTLCs]
  constructor
  · rintro ⟨hm, hs | hs⟩
    · exact Or.inl ⟨hm, hs⟩
    · exact Or.inr ⟨hm, hs⟩
  · rintro (⟨hm, hs⟩ | ⟨hm, hs⟩)
    · exact ⟨hm, Or.inl hs⟩
    · exact ⟨hm, Or.inr hs⟩

/-- No HTLC is both offered and received. -/
theorem offered_received_disjoint (l : List HTLC) (h : HTLC)
    (ho : h ∈ offeredHTLCs l) (hr : h ∈ receivedHTLCs l) : False := by
  rw [mem_offeredHTLCs] at ho
  rw [mem_receivedHTLCs] at hr
  rw [ho.2] at hr
  simp at hr

/-- No HTLC is both settled and removed. -/
theorem settled_removed_disjoint (l : List HTLC) (h : HTLC)
    (hs : h ∈ settledHTLCs l) (hr : h ∈ removedHTLCs l) : False := by
  rw [mem_settledHTLCs] at hs
  rw [mem_removedHTLCs] at hr
  rw [hr.2] at hs
  simp at hs

/-- No pending HTLC is settled. -/
theorem pending_settled_disjoint (l : List HTLC) (h : HTLC)
    (hp : h ∈ pendingHTLCs l) (hs : h ∈ settledHTLCs l) : False := by
  rw [mem_pendingHTLCs] at hp
  rw [mem_settledHTLCs] at hs
  rcases hp.2 with ho | ho <;> rw [ho] at hs <;> simp at hs

/-- No pending HTLC is removed. -/
theorem pending_removed_disjoint (l : List HTLC) (h : HTLC)
    (hp : h ∈ pendingHTLCs l) (hr : h ∈ removedHTLCs l) : False := by
  rw [mem_pendingHTLCs] at hp
  rw [mem_removedHTLCs] at hr
  rcases hp.2 with ho | ho <;> rw [ho] at hr <;> simp at hr

/-- Every HTLC of the list belongs to at least one of the four state
buckets; combined with the disjointness lemmas this is a partition. -/
theorem mem_stateBuckets {l : List HTLC} {h : HTLC} (hm : h ∈ l) :
    h ∈ offeredHTLCs l ∨ h ∈ receivedHTLCs l ∨
      h ∈ settledHTLCs l ∨ h ∈ removedHTLCs l := by
  cases hs : h.state with
  | offered =>
      exact Or.inl ((mem_offeredHTLCs).2 ⟨hm, hs⟩)
  | received =>
      exact Or.inr (Or.inl ((mem_receivedHTLCs).2 ⟨hm, hs⟩))
  | fulfilled =>
      exact Or.inr (Or.inr (Or.inl ((mem_settledHTLCs).2 ⟨hm, Or.inl hs⟩)))
  | failed =>
      exact Or.inr (Or.inr (Or.inl ((mem_settledHTLCs).2 ⟨hm, Or.inr hs⟩)))
  | removed =>
      exact Or.inr (Or.inr (Or.inr ((mem_removedHTLCs).2 ⟨hm, hs⟩)))

/-! ## 3. Amount sums over the buckets -/

/-- The amount sum of a list of HTLCs. -/
def htlcAmountSum (l : List HTLC) : Nat := (l.map (fun h => h.amount.val)).sum

/-- Total offered amount. -/
def offeredValue (l : List HTLC) : Nat := htlcAmountSum (offeredHTLCs l)

/-- Total received amount. -/
def receivedValue (l : List HTLC) : Nat := htlcAmountSum (receivedHTLCs l)

/-- Total settled amount. -/
def settledValue (l : List HTLC) : Nat := htlcAmountSum (settledHTLCs l)

/-- Total removed amount. -/
def removedValue (l : List HTLC) : Nat := htlcAmountSum (removedHTLCs l)

/-- Total pending (in-flight) amount. -/
def pendingValue (l : List HTLC) : Nat := htlcAmountSum (pendingHTLCs l)

/-- The sum over the offered/received partition equals the sum over the
whole pending list. -/
theorem pendingValue_eq_offered_add_received (l : List HTLC) :
    pendingValue l = offeredValue l + receivedValue l := by
  induction l with
  | nil => rfl
  | cons h t ih =>
      unfold pendingValue offeredValue receivedValue htlcAmountSum
        pendingHTLCs offeredHTLCs receivedHTLCs
        isPendingHTLC isOfferedHTLC isReceivedHTLC at ih ⊢
      cases hs : h.state <;> simp [hs] at ih ⊢ <;> omega

/-- The sum over all four state buckets equals the amount sum of the whole
list. -/
theorem totalValue_eq_stateBuckets (l : List HTLC) :
    htlcAmountSum l =
      offeredValue l + receivedValue l + settledValue l + removedValue l := by
  induction l with
  | nil => rfl
  | cons h t ih =>
      unfold offeredValue receivedValue settledValue removedValue htlcAmountSum
        offeredHTLCs receivedHTLCs settledHTLCs removedHTLCs
        isOfferedHTLC isReceivedHTLC isSettledHTLC isRemovedHTLC at ih ⊢
      cases hs : h.state <;> simp [hs] at ih ⊢ <;> omega

/-! ## 4. The in-flight bucket of a channel -/

/-- An offered HTLC with the given amount and empty payment metadata.  This is
the record used by the arithmetic core of `update_add_htlc` in
`LnLean.Proofs.Channel.ReserveProps`. -/
def offeredHTLC (amount : Msat) : HTLC :=
  { direction := Direction.local
    amount := amount
    paymentHash := ⟨ByteArray.empty⟩
    cltvExpiry := 0
    state := HTLCState.offered }

/-- The channel's in-flight HTLC value: offered plus received amounts.  This
is definitionally the `htlcInFlightValue` of
`LnLean.Proofs.Channel.ReserveProps`. -/
def htlcInFlightValue (c : Channel) : Nat :=
  ((c.htlcs.filter (fun h =>
      h.state = HTLCState.offered ∨ h.state = HTLCState.received)).map
    (fun h => h.amount.val)).sum

/-- The channel definition agrees with the list-level `pendingValue`. -/
theorem htlcInFlightValue_eq_pendingValue (c : Channel) :
    htlcInFlightValue c = pendingValue c.htlcs := by
  unfold htlcInFlightValue pendingValue htlcAmountSum pendingHTLCs isPendingHTLC
  rfl

/-- Appending an offered HTLC adds exactly its amount to the pending sum.
This restates the arithmetic core of `inFlightSum_append_offered`. -/
theorem pendingValue_append_offered (l : List HTLC) (amount : Msat) :
    pendingValue (l ++ [offeredHTLC amount]) = pendingValue l + amount.val := by
  unfold pendingValue htlcAmountSum pendingHTLCs isPendingHTLC offeredHTLC
  simp [List.filter_append, List.map_append, List.sum_append]

/-- ReserveProps-compatible name for the append law on the in-flight list. -/
theorem inFlightSum_append_offered (l : List HTLC) (amount : Msat) :
    pendingValue (l ++ [offeredHTLC amount]) = pendingValue l + amount.val :=
  pendingValue_append_offered l amount

/-- Appending one offered HTLC to a channel increases its in-flight bucket by
exactly the HTLC amount. -/
theorem htlcInFlightValue_append_offered (c : Channel) (amount : Msat) :
    htlcInFlightValue { c with htlcs := c.htlcs ++ [offeredHTLC amount] } =
      htlcInFlightValue c + amount.val := by
  rw [htlcInFlightValue_eq_pendingValue, htlcInFlightValue_eq_pendingValue,
    pendingValue_append_offered]

/-! ## 5. The settled-plus-in-flight ledger -/

/-- Drop `amountMsat` from the settled local balance, with truncated Nat
subtraction.  Mirrors `LnLean.Proofs.Channel.spendLocalBalance`. -/
def spendLocalBalance (b : Balance) (amountMsat : Nat) : Balance :=
  { b with localBalance := ⟨b.localBalance.val - amountMsat⟩ }

/-- When the amount fits, the settled total drops by exactly that amount. -/
theorem spendLocalBalance_total_val {b : Balance} {amountMsat : Nat}
    (h : amountMsat ≤ b.localBalance.val) :
    (spendLocalBalance b amountMsat).total.val = b.total.val - amountMsat := by
  simp [spendLocalBalance, Balance.total_val]
  omega

/-- The ledger bucket used by `ReserveProps`: settled balance plus in-flight
HTLC value. -/
def settledPlusInFlight (c : Channel) : Nat :=
  c.balance.total.val + htlcInFlightValue c

/-- The settled-plus-in-flight identity: a committed update that drops the
amount from the settled local balance and appends an offered HTLC leaves the
bucket unchanged (provided the amount fits). -/
theorem committed_update_settledPlusInFlight_eq (c c' : Channel) (amount : Msat)
    (h_fits : amount.val ≤ c.balance.localBalance.val)
    (h_step : c' = { c with
      balance := spendLocalBalance c.balance amount.val
      htlcs := c.htlcs ++ [offeredHTLC amount] }) :
    settledPlusInFlight c' = settledPlusInFlight c := by
  subst c'
  unfold settledPlusInFlight
  rw [spendLocalBalance_total_val h_fits]
  simp only [Balance.total_val] at *
  simp only [htlcInFlightValue_eq_pendingValue]
  rw [pendingValue_append_offered]
  omega

/-- The settled-plus-in-flight ledger equation is preserved by the modelled
committed update, which is the corrected `ReserveProps` ledger theorem. -/
theorem committed_update_preserves_ledger (c c' : Channel) (fee : Msat)
    (amount : Msat)
    (h_fits : amount.val ≤ c.balance.localBalance.val)
    (h_old : c.balance.total.val + htlcInFlightValue c + fee.val =
      c.fundingValue.val)
    (h_step : c' = { c with
      balance := spendLocalBalance c.balance amount.val
      htlcs := c.htlcs ++ [offeredHTLC amount] }) :
    c'.balance.total.val + htlcInFlightValue c' + fee.val =
      c'.fundingValue.val := by
  subst c'
  rw [spendLocalBalance_total_val h_fits]
  simp only [Balance.total_val] at h_old ⊢
  simp only [htlcInFlightValue_eq_pendingValue] at h_old ⊢
  rw [pendingValue_append_offered]
  omega

/-- The same ledger identity in subtractive form, as used when the fee bucket
is read off the funding value. -/
theorem settledPlusInFlight_eq_funding_sub_fee {c : Channel} {fee : Msat}
    (h : settledPlusInFlight c + fee.val = c.fundingValue.val) :
    settledPlusInFlight c = c.fundingValue.val - fee.val := by
  omega

end LnLean.Proofs.PhaseC2.HTLCPartition
