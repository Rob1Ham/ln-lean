import LnLean.Payment.MPP
import LnLean.Channel.State

/-!
# LnLean.Proofs.Payment.LiquidityProps

English claim.  A channel endpoint has two liquidity quantities: *outbound*
liquidity is what the local side may still send, and *inbound* liquidity is
what the remote side may still send.  Both are read off the channel balance,
so they are complementary: `outbound + inbound` is the total off-chain value
held by the two parties.  Each side must keep `channel_reserve_satoshis`
(converted to millisatoshis) in its own balance; a spend is accepted only
when the *post-spend* balance still covers that reserve.  A spend that would
break the reserve is rejected outright (`addHtlc? = none`); the model never
truncates the requested amount.  Likewise, an HTLC is admitted only when the
value already offered in the same direction plus the new amount stays within
the receiving side's advertised `max_htlc_value_in_flight_msat`; consequently
no single pending HTLC exceeds the applicable `max_htlc_value`.  For a
multi-part payment, `planFits` bounds the plan's summed amount by the
reserve-adjusted outbound liquidity of the channel.

The module also states the BOLT 3 conservation law
`local + remote + fee = funding_value` as the predicate `Conserved`.  It is a
precondition, not a theorem of arbitrary `Channel` records (the record has no
well-formedness invariant): the module proves its consequences (capacity
bounds, the "inbound is the complement" equation, and preservation of the
reserve by every `Channel.Step`) and shows that adding an HTLC that passes the
reserve check turns it into `local + remote + in-flight + fee = funding_value`.

BOLT sections.
* BOLT 2 §`open_channel`: `max_htlc_value_in_flight_msat` and
  `channel_reserve_satoshis` fields and their meaning.
* BOLT 2 §Adding an HTLC: the sender MUST NOT add an HTLC whose amount, added
  to the offered total, exceeds the remote's
  `max_htlc_value_in_flight_msat`, and MUST NOT spend below its reserve.
* BOLT 3 §Commitment Transaction Construction and §Fee Calculation: the base
  fee is subtracted from the funder's output, and outputs plus fee are funded
  by the funding output.

BOLT line anchors (pinned BOLTs commit
`1aadb719b4007c4cea0ba6e36b08c4fb53788dee`).
* `refs/bolts/02-peer-protocol.md:693-694` the two `open_channel` fields.
* `refs/bolts/02-peer-protocol.md:730-741` their meaning; the reserve is
  "the minimum amount that the other node is to keep as a direct payment",
  `max_htlc_value_in_flight_msat` is the cap on outstanding offered value.
* `refs/bolts/02-peer-protocol.md:884-886` the channel reserve rule
  (1% suggested, initially possibly unmet, then maintained).
* `refs/bolts/02-peer-protocol.md:2829-2834` MUST NOT exceed the remote's
  `max_htlc_value_in_flight_msat`.
* `refs/bolts/02-peer-protocol.md:2846-2852` the receiver rejects an amount
  the sender cannot afford while maintaining its reserve.
* `refs/bolts/03-transactions.md:316-327` fee and anchor deductions from the
  funder output.
* `refs/bolts/03-transactions.md:704-730` commitment output construction.

rust-lightning anchors at
`fe4900930c6bd5786ec4203274d7cf312776a5a6`.
* `lightning/src/ln/channel.rs:113-125` `AvailableBalances`:
  `inbound_capacity_msat`, `outbound_capacity_msat`, and the next-HTLC limit.
* `lightning/src/ln/channel.rs:2697-2703` `get_htlc_maximum_msat` caps the
  next HTLC by `(value - counterparty_reserve - holder_reserve) * 1000` and
  by `max_htlc_value_in_flight_msat`.
* `lightning/src/ln/channel.rs:5866-5871` rejects an inbound HTLC when
  `inbound_htlcs_value_msat > holder_max_htlc_value_in_flight_msat`.
* `lightning/src/ln/channel.rs:5888-5894` rejects an HTLC that would put the
  remote under its selected reserve.
* `lightning/src/ln/channel.rs:6552-6605` `get_available_balances_for_scope`
  (inbound/outbound capacity computation).
* `lightning/src/ln/channel.rs:8370` `update_add_htlc`.
* `lightning/src/ln/channel.rs:13842-13863` the assertion that a new
  commitment balance below the selected reserve is never accepted.

What is explicitly NOT modelled.
* HTLC scripts, second-stage transactions, revocation, and on-chain fees:
  only the off-chain balance movement is modelled.
* The full LDK outbound-capacity formula.  `availableOutbound` subtracts the
  reserve only; LDK additionally subtracts commitment fees, anchor values,
  dust exposure, and in-flight HTLCs (`channel.rs:6552-6605`).  The simplified
  number is therefore an upper bound, not an equality; refining it needs
  `LnLean.Channel.Commitment` and `LnLean.Channel.Fee`, which this proof does
  not import.
* `max_accepted_htlcs`, `htlc_minimum_msat`, duplicate HTLC ids, and the CLTV
  checks.  The cap proved here is the value cap only.
* Channel construction.  `Channel.Step` never changes balances, so
  `step_preserves_meetsReserve` is a preservation result; it does not prove
  that the opening handshake establishes the reserve for both sides.
  BOLT 2 itself allows the reserve to be unmet initially
  (`02-peer-protocol.md:884`).
* MPP routing.  `MPPPart.channel` is a BOLT 7 `short_channel_id`, while
  `Channel` carries only a `ChannelId`, so a part cannot be resolved to a
  `Channel` in this model.  `planFits` is deliberately channel-agnostic: it
  checks a plan against one channel's outbound liquidity when the caller has
  already selected that channel.
* Atomicity and liveness of MPP; those are `LnLean.Payment.MPP` and wave-B
  payment obligations.
-/

namespace LnLean.Proofs.Payment

set_option autoImplicit false

open LnLean
open LnLean.Channel
open LnLean.Payment

/-! ## Balance, reserve, and capacity -/

/-- Local channel reserve in millisatoshis.  BOLT 2 carries the reserve in
satoshis; the balance is in millisatoshis. -/
def reserveMsat (c : Channel) : Nat :=
  c.localEndpoint.params.channelReserveSat * Msat.MSAT_PER_SAT

/-- The remote side's reserve, in millisatoshis. -/
def remoteReserveMsat (c : Channel) : Nat :=
  c.remoteEndpoint.params.channelReserveSat * Msat.MSAT_PER_SAT

/-- Outbound liquidity from the local endpoint's point of view: the local
balance, before subtracting the reserve. -/
def outboundLiquidity (c : Channel) : Nat :=
  c.balance.localBalance.val

/-- Inbound liquidity from the local endpoint's point of view: the remote
balance, before subtracting the remote's reserve. -/
def inboundLiquidity (c : Channel) : Nat :=
  c.balance.remoteBalance.val

/-- The balance of one side, in millisatoshis. -/
def balanceOf (c : Channel) : Direction → Nat
  | .local => outboundLiquidity c
  | .remote => inboundLiquidity c

/-- The reserve one side must keep, in millisatoshis. -/
def reserveOf (c : Channel) : Direction → Nat
  | .local => reserveMsat c
  | .remote => remoteReserveMsat c

/-- `MeetsReserveOn c d` says side `d` still holds at least its negotiated
channel reserve. -/
def MeetsReserveOn (c : Channel) (d : Direction) : Prop :=
  reserveOf c d ≤ balanceOf c d

/-- The local side meets its reserve (BOLT 2 `channel_reserve_satoshis`). -/
def MeetsReserve (c : Channel) : Prop :=
  MeetsReserveOn c .local

/-- The remote side meets its reserve. -/
def MeetsRemoteReserve (c : Channel) : Prop :=
  MeetsReserveOn c .remote

/-- Outbound liquidity net of the local reserve.  This is the amount a new
outgoing HTLC may draw on; compare LDK's `outbound_capacity_msat`. -/
def availableOutbound (c : Channel) : Nat :=
  outboundLiquidity c - reserveMsat c

/-- Inbound liquidity net of the remote reserve. -/
def availableInbound (c : Channel) : Nat :=
  inboundLiquidity c - remoteReserveMsat c

@[simp] theorem reserveMsat_eq (c : Channel) :
    reserveMsat c = c.localEndpoint.params.channelReserveSat * 1000 := rfl

@[simp] theorem remoteReserveMsat_eq (c : Channel) :
    remoteReserveMsat c = c.remoteEndpoint.params.channelReserveSat * 1000 := rfl

@[simp] theorem outboundLiquidity_eq (c : Channel) :
    outboundLiquidity c = c.balance.localBalance.val := rfl

@[simp] theorem inboundLiquidity_eq (c : Channel) :
    inboundLiquidity c = c.balance.remoteBalance.val := rfl

@[simp] theorem balanceOf_local (c : Channel) : balanceOf c .local = outboundLiquidity c := rfl

@[simp] theorem balanceOf_remote (c : Channel) : balanceOf c .remote = inboundLiquidity c := rfl

@[simp] theorem reserveOf_local (c : Channel) : reserveOf c .local = reserveMsat c := rfl

@[simp] theorem reserveOf_remote (c : Channel) : reserveOf c .remote = remoteReserveMsat c := rfl

theorem meetsReserve_iff (c : Channel) :
    MeetsReserve c ↔ reserveMsat c ≤ outboundLiquidity c := Iff.rfl

theorem meetsRemoteReserve_iff (c : Channel) :
    MeetsRemoteReserve c ↔ remoteReserveMsat c ≤ inboundLiquidity c := Iff.rfl

/-- Balances are non-negative: `Msat` wraps a `Nat`.  This is a structural
lemma, not an economic assumption. -/
theorem balance_local_nonneg (c : Channel) : 0 ≤ c.balance.localBalance.val :=
  Nat.zero_le _

theorem balance_remote_nonneg (c : Channel) : 0 ≤ c.balance.remoteBalance.val :=
  Nat.zero_le _

/-- A reserve is a non-negative number of millisatoshis. -/
theorem reserveMsat_nonneg (c : Channel) : 0 ≤ reserveMsat c :=
  Nat.zero_le _

/-- Outbound plus inbound liquidity is the total off-chain balance. -/
theorem outbound_add_inbound_eq_total (c : Channel) :
    outboundLiquidity c + inboundLiquidity c = c.balance.total.val := rfl

/-- Inbound liquidity is the complement of outbound liquidity with respect to
the total off-chain balance. -/
theorem inbound_eq_total_sub_outbound (c : Channel) :
    inboundLiquidity c = c.balance.total.val - outboundLiquidity c := by
  rw [← outbound_add_inbound_eq_total]
  omega

/-- Total value of a list of HTLCs in millisatoshis. -/
def sumHtlcs : List HTLC → Nat
  | [] => 0
  | h :: hs => h.amount.val + sumHtlcs hs

/-! ## Conservation: balances plus fee equal the funding value -/

/-- The commitment fee in millisatoshis for a commitment transaction of
weight `w`, at the current feerate. -/
def feeMsat (c : Channel) (w : Weight) : Nat :=
  (c.localEndpoint.params.feerate.fee w).val

/-- BOLT 3 conservation, as a predicate on a channel record: the two direct
balances plus the commitment fee equal the funding value.  In-flight HTLC
value is handled by `ConservedWithPending` below. -/
def Conserved (c : Channel) (w : Weight) : Prop :=
  outboundLiquidity c + inboundLiquidity c + feeMsat c w = c.fundingValue.val

/-- Refined conservation: the two direct balances, the value locked in pending
HTLCs, and the fee equal the funding value.  This is the form that holds in a
ledger where `Balance` excludes in-flight HTLCs. -/
def ConservedWithPending (c : Channel) (w : Weight) : Prop :=
  outboundLiquidity c + inboundLiquidity c + sumHtlcs c.htlcs + feeMsat c w =
    c.fundingValue.val

/-- Under conservation, the two direct balances never exceed the capacity. -/
theorem conserved_total_le_capacity {c : Channel} {w : Weight}
    (h : Conserved c w) :
    outboundLiquidity c + inboundLiquidity c ≤ c.fundingValue.val := by
  unfold Conserved at h
  omega

/-- Under conservation, inbound liquidity is the capacity minus outbound
liquidity and the fee. -/
theorem conserved_inbound_eq {c : Channel} {w : Weight}
    (h : Conserved c w) :
    inboundLiquidity c = c.fundingValue.val - outboundLiquidity c - feeMsat c w := by
  unfold Conserved at h
  omega

/-- Under conservation, outbound liquidity never exceeds the capacity. -/
theorem conserved_outbound_le_capacity {c : Channel} {w : Weight}
    (h : Conserved c w) :
    outboundLiquidity c ≤ c.fundingValue.val := by
  unfold Conserved at h
  omega

/-- The reserve-adjusted outbound liquidity is at most the capacity, provided
the local side meets its reserve and conservation holds. -/
theorem availableOutbound_le_capacity {c : Channel} {w : Weight}
    (_hr : MeetsReserve c) (hc : Conserved c w) :
    availableOutbound c ≤ c.fundingValue.val := by
  have hcap := conserved_outbound_le_capacity hc
  unfold availableOutbound
  omega

/-- In a settled channel (`htlcs = []`), refined and plain conservation
coincide. -/
theorem conservedWithPending_of_settled {c : Channel} {w : Weight}
    (hs : c.htlcs = []) (h : Conserved c w) :
    ConservedWithPending c w := by
  unfold ConservedWithPending
  rw [hs]
  simp only [sumHtlcs]
  unfold Conserved at h
  omega

/-! ## HTLC totals and the `max_htlc_value` cap -/

@[simp] theorem sumHtlcs_nil : sumHtlcs [] = 0 := rfl

@[simp] theorem sumHtlcs_cons (h : HTLC) (hs : List HTLC) :
    sumHtlcs (h :: hs) = h.amount.val + sumHtlcs hs := rfl

/-- Every member of an HTLC list is bounded by that list's total value. -/
theorem htlc_amount_le_sumHtlcs {h : HTLC} {hs : List HTLC}
    (hm : h ∈ hs) : h.amount.val ≤ sumHtlcs hs := by
  induction hs with
  | nil => cases hm
  | cons q qs ih =>
      rw [sumHtlcs_cons]
      rcases List.mem_cons.mp hm with rfl | hmem
      · omega
      · have hle := ih hmem
        omega

/-- Total value offered in one direction. -/
def sumByDirection (d : Direction) : List HTLC → Nat
  | [] => 0
  | h :: hs =>
      (if h.direction = d then h.amount.val else 0) + sumByDirection d hs

@[simp] theorem sumByDirection_nil (d : Direction) : sumByDirection d [] = 0 := rfl

@[simp] theorem sumByDirection_cons (d : Direction) (h : HTLC) (hs : List HTLC) :
    sumByDirection d (h :: hs) =
      (if h.direction = d then h.amount.val else 0) + sumByDirection d hs := rfl

/-- Every HTLC contributes at most its own amount to the total for its own
direction. -/
theorem amount_le_sumByDirection {d : Direction} {h : HTLC} {hs : List HTLC}
    (hm : h ∈ hs) (hd : h.direction = d) :
    h.amount.val ≤ sumByDirection d hs := by
  induction hs with
  | nil => cases hm
  | cons q qs ih =>
      rw [sumByDirection_cons]
      rcases List.mem_cons.mp hm with rfl | hmem
      · have hif : (if h.direction = d then h.amount.val else 0) = h.amount.val := by
          simp [hd]
        rw [hif]
        omega
      · have hle := ih hmem
        have hnonneg : 0 ≤ (if q.direction = d then q.amount.val else 0) :=
          Nat.zero_le _
        omega

/-- The `max_htlc_value_in_flight_msat` applicable to an HTLC offered in
direction `d`: the *receiving* side advertises it, so a local offer is capped
by the remote endpoint's value and a remote offer by the local endpoint's. -/
def maxHtlcValue (c : Channel) : Direction → Nat
  | .local => c.remoteEndpoint.params.maxHtlcValue.val
  | .remote => c.localEndpoint.params.maxHtlcValue.val

@[simp] theorem maxHtlcValue_local (c : Channel) :
    maxHtlcValue c .local = c.remoteEndpoint.params.maxHtlcValue.val := rfl

@[simp] theorem maxHtlcValue_remote (c : Channel) :
    maxHtlcValue c .remote = c.localEndpoint.params.maxHtlcValue.val := rfl

/-- Both directional in-flight caps hold for the pending HTLCs. -/
def WithinHtlcCaps (c : Channel) : Prop :=
  sumByDirection .local c.htlcs ≤ maxHtlcValue c .local ∧
    sumByDirection .remote c.htlcs ≤ maxHtlcValue c .remote

/-- No single pending HTLC exceeds the `max_htlc_value` advertised by the
side that receives it.  This is the single-HTLC consequence of the BOLT 2
in-flight cap. -/
theorem single_htlc_le_max {c : Channel} (hc : WithinHtlcCaps c)
    {h : HTLC} (hm : h ∈ c.htlcs) :
    h.amount.val ≤ maxHtlcValue c h.direction := by
  cases hd : h.direction
  · have hle := amount_le_sumByDirection (d := .local) hm hd
    have hcap := hc.1
    simpa using Nat.le_trans hle hcap
  · have hle := amount_le_sumByDirection (d := .remote) hm hd
    have hcap := hc.2
    simpa using Nat.le_trans hle hcap

/-! ## Adding an HTLC: reserve and cap checks -/

/-- The balance after spending `amt` from side `d`. -/
def spendBalance (c : Channel) (d : Direction) (amt : Msat) : Balance :=
  match d with
  | .local =>
      { c.balance with localBalance := ⟨outboundLiquidity c - amt.val⟩ }
  | .remote =>
      { c.balance with remoteBalance := ⟨inboundLiquidity c - amt.val⟩ }

/-- Try to add an HTLC `h` to the channel.  The HTLC is accepted only if

1. the offered total in `h`'s direction plus `h.amount` stays within the
   receiving side's `max_htlc_value_in_flight_msat`, and
2. the sending side's balance after the HTLC still covers its reserve.

Otherwise the result is `none`: the payment is rejected, never truncated.
BOLT 2 requires both checks before `update_add_htlc`
(`02-peer-protocol.md:2829-2852`). -/
def addHtlc? (c : Channel) (h : HTLC) : Option Channel :=
  if sumByDirection h.direction c.htlcs + h.amount.val ≤
        maxHtlcValue c h.direction ∧
      reserveOf c h.direction + h.amount.val ≤ balanceOf c h.direction then
    some { c with
      balance := spendBalance c h.direction h.amount
      htlcs := h :: c.htlcs }
  else
    none

/-- The accepted channel has exactly the expected shape. -/
theorem addHtlc?_some_shape {c c' : Channel} {h : HTLC}
    (hs : addHtlc? c h = some c') :
    c' = { c with
      balance := spendBalance c h.direction h.amount
      htlcs := h :: c.htlcs } := by
  unfold addHtlc? at hs
  split at hs
  · simp only [Option.some.injEq] at hs
    exact hs.symm
  · simp at hs

/-- The two acceptance conditions extracted from a successful `addHtlc?`. -/
theorem addHtlc?_some_conditions {c c' : Channel} {h : HTLC}
    (hs : addHtlc? c h = some c') :
    sumByDirection h.direction c.htlcs + h.amount.val ≤
        maxHtlcValue c h.direction ∧
      reserveOf c h.direction + h.amount.val ≤ balanceOf c h.direction := by
  unfold addHtlc? at hs
  split at hs
  · assumption
  · simp at hs

/-- `addHtlc?` returns `none` exactly when one of the two checks fails. -/
theorem addHtlc?_isNone (c : Channel) (h : HTLC) :
    addHtlc? c h = none ↔
      ¬ (sumByDirection h.direction c.htlcs + h.amount.val ≤
            maxHtlcValue c h.direction ∧
          reserveOf c h.direction + h.amount.val ≤ balanceOf c h.direction) := by
  unfold addHtlc?
  by_cases hc : (sumByDirection h.direction c.htlcs + h.amount.val ≤
        maxHtlcValue c h.direction ∧
      reserveOf c h.direction + h.amount.val ≤ balanceOf c h.direction)
  · simp [hc]
  · simp [hc]

/-- A spend that would leave the sender below its reserve is rejected. -/
theorem addHtlc?_none_of_reserve {c : Channel} {h : HTLC}
    (hr : balanceOf c h.direction < reserveOf c h.direction + h.amount.val) :
    addHtlc? c h = none := by
  rw [addHtlc?_isNone]
  exact fun hc => absurd hc.2 (by omega)

/-- An HTLC whose addition would exceed the in-flight cap is rejected. -/
theorem addHtlc?_none_of_cap {c : Channel} {h : HTLC}
    (hc : maxHtlcValue c h.direction <
      sumByDirection h.direction c.htlcs + h.amount.val) :
    addHtlc? c h = none := by
  rw [addHtlc?_isNone]
  exact fun hcc => absurd hcc.1 (by omega)

/-- A successful spend leaves the sender at or above its reserve. -/
theorem addHtlc?_some_meetsReserveOn {c c' : Channel} {h : HTLC}
    (hs : addHtlc? c h = some c') :
    MeetsReserveOn c' h.direction := by
  rcases addHtlc?_some_conditions hs with ⟨_, hres⟩
  rw [addHtlc?_some_shape hs]
  cases hd : h.direction
  · simp only [hd, MeetsReserveOn, reserveOf_local, balanceOf_local, reserveMsat,
      outboundLiquidity, spendBalance] at hres ⊢
    omega
  · simp only [hd, MeetsReserveOn, reserveOf_remote, balanceOf_remote, remoteReserveMsat,
      inboundLiquidity, spendBalance] at hres ⊢
    omega

/-- A successful local offer leaves the local side at or above its reserve. -/
theorem addHtlc?_some_meetsReserve {c c' : Channel} {h : HTLC}
    (hs : addHtlc? c h = some c') (hd : h.direction = .local) :
    MeetsReserve c' := by
  have h := addHtlc?_some_meetsReserveOn hs
  rw [hd] at h
  simpa [MeetsReserve] using h

/-- A successful remote offer leaves the remote side at or above its reserve. -/
theorem addHtlc?_some_meetsRemoteReserve {c c' : Channel} {h : HTLC}
    (hs : addHtlc? c h = some c') (hd : h.direction = .remote) :
    MeetsRemoteReserve c' := by
  have h := addHtlc?_some_meetsReserveOn hs
  rw [hd] at h
  simpa [MeetsRemoteReserve] using h

/-- Accepted value is never truncated: the sender's post-spend balance plus
the HTLC amount is exactly the pre-spend balance. -/
theorem addHtlc?_some_balanceOf_add {c c' : Channel} {h : HTLC}
    (hs : addHtlc? c h = some c') :
    balanceOf c' h.direction + h.amount.val = balanceOf c h.direction := by
  rcases addHtlc?_some_conditions hs with ⟨_, hres⟩
  rw [addHtlc?_some_shape hs]
  unfold balanceOf spendBalance outboundLiquidity inboundLiquidity
  cases hd : h.direction <;> simp [hd] at * <;> omega

/-- The direction not spent is unchanged. -/
theorem addHtlc?_some_balanceOf_other {c c' : Channel} {h : HTLC}
    (hs : addHtlc? c h = some c') {d : Direction} (hne : d ≠ h.direction) :
    balanceOf c' d = balanceOf c d := by
  rw [addHtlc?_some_shape hs]
  unfold balanceOf spendBalance outboundLiquidity inboundLiquidity
  cases hd : h.direction <;> cases d <;> simp_all

/-- The fee is unchanged by adding an HTLC (only the balance and HTLC list
change). -/
theorem addHtlc?_some_fee_eq {c c' : Channel} {h : HTLC} (hs : addHtlc? c h = some c')
    (w : Weight) : feeMsat c' w = feeMsat c w := by
  rw [addHtlc?_some_shape hs]
  rfl

/-- The funding value is unchanged by adding an HTLC. -/
theorem addHtlc?_some_fundingValue_eq {c c' : Channel} {h : HTLC}
    (hs : addHtlc? c h = some c') : c'.fundingValue = c.fundingValue := by
  rw [addHtlc?_some_shape hs]

/-- Adding an HTLC moves value from one direct balance into the in-flight
HTLC, so the sum of the two direct balances plus the new HTLC amount is
unchanged. -/
theorem addHtlc?_some_total_add {c c' : Channel} {h : HTLC}
    (hs : addHtlc? c h = some c') :
    outboundLiquidity c' + inboundLiquidity c' + h.amount.val =
      outboundLiquidity c + inboundLiquidity c := by
  have hadd := addHtlc?_some_balanceOf_add hs
  cases hd : h.direction
  · have hother := addHtlc?_some_balanceOf_other hs (d := .remote) (by simp [hd])
    simp only [hd, balanceOf_local, balanceOf_remote, outboundLiquidity,
      inboundLiquidity] at hadd hother ⊢
    omega
  · have hother := addHtlc?_some_balanceOf_other hs (d := .local) (by simp [hd])
    simp only [hd, balanceOf_local, balanceOf_remote, outboundLiquidity,
      inboundLiquidity] at hadd hother ⊢
    omega

/-- Adding an HTLC preserving conservation plus the in-flight amount. -/
theorem addHtlc?_some_conserved_with_pending {c c' : Channel} {h : HTLC}
    {w : Weight} (hs : addHtlc? c h = some c') (hc : Conserved c w) :
    outboundLiquidity c' + inboundLiquidity c' + h.amount.val + feeMsat c' w =
      c'.fundingValue.val := by
  have htot := addHtlc?_some_total_add hs
  have hfee := addHtlc?_some_fee_eq hs w
  have hfund := congrArg Msat.val (addHtlc?_some_fundingValue_eq hs)
  unfold Conserved at hc
  omega

/-- A newly accepted HTLC's amount is within the applicable
`max_htlc_value`. -/
theorem addHtlc?_some_amount_le_max {c c' : Channel} {h : HTLC}
    (hs : addHtlc? c h = some c') :
    h.amount.val ≤ maxHtlcValue c h.direction := by
  rcases addHtlc?_some_conditions hs with ⟨hcap, _⟩
  omega

/-- The in-flight cap of the spent direction is preserved by an accepted
HTLC. -/
theorem addHtlc?_some_withinCap {c c' : Channel} {h : HTLC}
    (hs : addHtlc? c h = some c') :
    sumByDirection h.direction c'.htlcs ≤ maxHtlcValue c' h.direction := by
  rcases addHtlc?_some_conditions hs with ⟨hcap, _⟩
  rw [addHtlc?_some_shape hs]
  cases hd : h.direction <;>
    simp [hd, sumByDirection, maxHtlcValue] at * <;> omega

/-- `addHtlc?` preserves the two directional in-flight caps. -/
theorem addHtlc?_some_withinCaps {c c' : Channel} {h : HTLC}
    (hs : addHtlc? c h = some c') (hcaps : WithinHtlcCaps c) :
    WithinHtlcCaps c' := by
  rcases addHtlc?_some_conditions hs with ⟨hcap, _⟩
  rw [addHtlc?_some_shape hs]
  unfold WithinHtlcCaps at *
  constructor
  · by_cases hd : h.direction = .local
    · simp [hd, sumByDirection, maxHtlcValue] at hcap ⊢
      omega
    · simp [hd, sumByDirection, maxHtlcValue] at hcaps ⊢
      exact hcaps.1
  · by_cases hd : h.direction = .remote
    · simp [hd, sumByDirection, maxHtlcValue] at hcap ⊢
      omega
    · simp [hd, sumByDirection, maxHtlcValue] at hcaps ⊢
      exact hcaps.2

/-! ## Channel transitions preserve the reserve -/

/-- No `Channel.Step` changes the balance: value movement is owned by the
HTLC/commitment workstream, not by the channel-lifecycle relation. -/
theorem step_preserves_balance {c c' : Channel} {e : ProtocolEvent}
    (h : Step c e c') : c'.balance = c.balance := by
  cases h <;> rfl

/-- No `Channel.Step` changes the funding value. -/
theorem step_preserves_fundingValue {c c' : Channel} {e : ProtocolEvent}
    (h : Step c e c') : c'.fundingValue = c.fundingValue := by
  cases h <;> rfl

/-- Every legal BOLT 2 channel-lifecycle step preserves the local reserve. -/
theorem step_preserves_meetsReserve {c c' : Channel} {e : ProtocolEvent}
    (h : Step c e c') (hr : MeetsReserve c) : MeetsReserve c' := by
  unfold MeetsReserve MeetsReserveOn reserveOf balanceOf at hr ⊢
  cases h <;> simpa [reserveMsat, outboundLiquidity] using hr

/-- Reachability preserves the local reserve. -/
theorem reachable_preserves_meetsReserve {c c' : Channel}
    (h : Reachable c c') (hr : MeetsReserve c) : MeetsReserve c' := by
  induction h with
  | refl => exact hr
  | step _ hs ih => exact step_preserves_meetsReserve hs ih

/-- If conservation holds before a legal step and the step is not `update_fee`
(which changes the feerate but not the balances), it holds afterwards. -/
theorem step_preserves_conserved_of_no_fee {c c' : Channel} {e : ProtocolEvent}
    {w : Weight} (hs : Step c e c')
    (hnofee : ∀ r : FeeRate, e ≠ ProtocolEvent.updateFee r)
    (hc : Conserved c w) :
    Conserved c' w := by
  have hbal := step_preserves_balance hs
  have hfund := step_preserves_fundingValue hs
  have hend : c'.localEndpoint = c.localEndpoint := by
    cases hs with
    | updateFee _ r => exact absurd rfl (hnofee r)
    | _ => rfl
  unfold Conserved at hc ⊢
  unfold outboundLiquidity inboundLiquidity feeMsat
  rw [hbal, hfund]
  rw [hend]
  exact hc

/-! ## MPP plans against outbound liquidity -/

/-- Total amount of an MPP plan, in millisatoshis. -/
def planTotal (p : MPPPlan) : Nat :=
  sumParts p.parts

/-- A plan fits a channel when its total is within the channel's
reserve-adjusted outbound liquidity.  Because `MPPPart` names a BOLT 7
`short_channel_id` and `Channel` has only a `ChannelId`, the caller chooses
the channel; this is the per-channel feasibility predicate. -/
def planFits (c : Channel) (p : MPPPlan) : Prop :=
  planTotal p ≤ availableOutbound c

/-- A feasible plan never exceeds the raw outbound balance. -/
theorem planFits_total_le_outbound {c : Channel} {p : MPPPlan}
    (h : planFits c p) :
    planTotal p ≤ outboundLiquidity c := by
  unfold planFits availableOutbound at h
  omega

/-- A complete MPP plan whose total fits the channel has target at most the
outbound balance.  This is the plan-level "total does not exceed available
outbound liquidity" statement. -/
theorem mppComplete_target_le_outbound {c : Channel} {p : MPPPlan}
    (hc : mppComplete p) (hf : planFits c p) :
    p.target.val ≤ outboundLiquidity c := by
  have hsum : sumParts p.parts = p.target.val := hc.2
  have hle := planFits_total_le_outbound hf
  unfold planTotal at hle
  omega

/-- If every part is at most `B` and the plan has `n` parts, its total is at
most `n * B`.  This is the arithmetic fact that turns per-part caps into a
plan bound. -/
theorem sumParts_le_length_mul (ps : List MPPPart) (B : Nat)
    (h : ∀ p ∈ ps, p.amount.val ≤ B) :
    sumParts ps ≤ ps.length * B := by
  induction ps with
  | nil => simp [sumParts]
  | cons p ps ih =>
      rw [sumParts_cons]
      have hp : p.amount.val ≤ B := h p (by simp)
      have hps : ∀ q ∈ ps, q.amount.val ≤ B := by
        intro q hq
        exact h q (by simp [hq])
      have hle := ih hps
      have hlen : (ps.length + 1) * B = ps.length * B + B := by
        rw [Nat.add_mul]
        simp
      simp only [List.length_cons]
      rw [hlen]
      omega

/-- A plan whose parts are each within `B` fits whenever `n * B` is within
the reserve-adjusted outbound liquidity. -/
theorem planFits_of_parts_bounded {c : Channel} {p : MPPPlan} {B : Nat}
    (hB : ∀ q ∈ p.parts, q.amount.val ≤ B)
    (hlen : p.parts.length * B ≤ availableOutbound c) :
    planFits c p := by
  unfold planFits planTotal
  exact Nat.le_trans (sumParts_le_length_mul p.parts B hB) hlen

/-- Feasibility is monotone in the plan total: if `q`'s total is at most
`p`'s total and `p` fits, then `q` fits. -/
theorem planFits_of_total_le {c : Channel} {p q : MPPPlan}
    (hq : planTotal q ≤ planTotal p) (hp : planFits c p) :
    planFits c q := by
  unfold planFits at *
  omega

end LnLean.Proofs.Payment
