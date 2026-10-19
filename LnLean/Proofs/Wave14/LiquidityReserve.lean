import LnLean.Proofs.Payment.LiquidityProps

/-!
# LnLean.Proofs.Wave14.LiquidityReserve

Additive repair of the channel-reserve **direction** in
`LnLean.Proofs.Payment.LiquidityProps` (Wave-13 review gap G01 / `REV-01`,
R32 §4 T1).  The legacy carrier is not changed:

* `LiquidityProps.reserveMsat` still reads
  `c.localEndpoint.params.channelReserveSat`;
* `LiquidityProps.reserveOf .local` inherits that reading;
* `LiquidityProps.availableOutbound`, `MeetsReserve`, `planFits`, and
  `addHtlc?` keep their old meaning.

`reserveMsat_eq_localEndpoint` below makes that legacy reading explicit and
auditable.  The old reading is **inverted** for local outbound: BOLT 2 carries
`channel_reserve_satoshis` as the reserve that the *receiving* peer must keep,
so the value advertised by the local endpoint is the reserve the **remote**
side must maintain, and the value advertised by the remote endpoint is the
reserve the **local** side must maintain (BOLT 2
`refs/bolts/02-peer-protocol.md:730-741`, `:884-887`; LDK datapoint D1,
`refs/rust-lightning/lightning/src/ln/channel.rs:6552-6605`).

The corrected names are:

* `localReserveMsat c = c.remoteEndpoint.params.channelReserveSat * 1000`;
* `remoteReserveMsatCorrected c = c.localEndpoint.params.channelReserveSat * 1000`;
* `availableOutboundCorrected c = outboundLiquidity c - localReserveMsat c`;
* `availableInboundCorrected c = inboundLiquidity c - remoteReserveMsatCorrected c`.

**Upper-bound boundary.**  `availableOutboundCorrected` is still only an
*upper bound* on the amount the local side can actually send.  It subtracts
exactly one reserve and nothing else: BOLT 3 commitment fees, anchor output
values, dust exposure, and in-flight HTLC value are all omitted.  It is
therefore not LDK's `outbound_capacity_msat` equality
(`channel.rs:6552-6605`); refining it needs `LnLean.Channel.Commitment` and
`LnLean.Channel.Fee`, which this module deliberately does not import.  The
same boundary applies to `availableInboundCorrected`.

The separation theorem `reserve_direction_separates` uses a concrete
`Channel` witness with local reserve 0, remote reserve 1 sat, local balance
1000 msat, remote balance 0, and no HTLCs: the legacy outbound reading reports
1000 msat while the corrected reading reports 0.  A second witness with both
reserves zero (`corrected_outbound_nonempty`) shows the corrected value is
inhabited and positive, so the corrected predicate is not vacuous.

This module adds no admission function.  Correcting the full `addHtlc?` guard
(directional in-flight, positivity, `htlc_minimum`, CLTV bound) is the separate
`W13-LIQ` in-flight/guard lane; this file closes only the reserve direction and
keeps every old carrier intact.
-/

namespace LnLean.Proofs.Wave14.LiquidityReserve

set_option autoImplicit false

open LnLean
open LnLean.Channel
open LnLean.Proofs.Payment

/-! ## Corrected reserve direction -/

/-- The reserve the **local** side must keep, in millisatoshis.  BOLT 2's
`channel_reserve_satoshis` is advertised by the *peer*: the remote endpoint's
value is the reserve the local side must maintain.  This is the BOLT 2
direction; it is the corrected counterpart of the legacy inverted reading in
`LnLean.Proofs.Payment.reserveMsat`. -/
def localReserveMsat (c : Channel) : Nat :=
  c.remoteEndpoint.params.channelReserveSat * Msat.MSAT_PER_SAT

/-- The reserve the **remote** side must keep, in millisatoshis.  This is the
local endpoint's advertised `channel_reserve_satoshis`, i.e. the corrected
counterpart of `LnLean.Proofs.Payment.remoteReserveMsat`, which reads the
remote endpoint and therefore uses the wrong side for inbound capacity. -/
def remoteReserveMsatCorrected (c : Channel) : Nat :=
  c.localEndpoint.params.channelReserveSat * Msat.MSAT_PER_SAT

/-- Corrected outbound liquidity from the local endpoint's point of view: the
local balance minus the reserve advertised by the **remote** endpoint.

This is still only an **upper bound** on spendable outbound capacity.  It
omits BOLT 3 commitment fees, anchor output values, dust exposure, and the
value already in flight; it is not LDK's `outbound_capacity_msat` equality.
-/
def availableOutboundCorrected (c : Channel) : Nat :=
  outboundLiquidity c - localReserveMsat c

/-- Corrected inbound liquidity from the local endpoint's point of view: the
remote balance minus the reserve advertised by the **local** endpoint.

Like `availableOutboundCorrected`, this is an upper bound only: fees, anchors,
dust, and in-flight HTLCs are not subtracted. -/
def availableInboundCorrected (c : Channel) : Nat :=
  inboundLiquidity c - remoteReserveMsatCorrected c

@[simp] theorem localReserveMsat_eq (c : Channel) :
    localReserveMsat c =
      c.remoteEndpoint.params.channelReserveSat * Msat.MSAT_PER_SAT := rfl

@[simp] theorem remoteReserveMsatCorrected_eq (c : Channel) :
    remoteReserveMsatCorrected c =
      c.localEndpoint.params.channelReserveSat * Msat.MSAT_PER_SAT := rfl

@[simp] theorem availableOutboundCorrected_eq (c : Channel) :
    availableOutboundCorrected c =
      outboundLiquidity c -
        c.remoteEndpoint.params.channelReserveSat * Msat.MSAT_PER_SAT := rfl

@[simp] theorem availableInboundCorrected_eq (c : Channel) :
    availableInboundCorrected c =
      inboundLiquidity c -
        c.localEndpoint.params.channelReserveSat * Msat.MSAT_PER_SAT := rfl

/-! ## Auditing the legacy carrier -/

/-- **The legacy carrier is auditable.**  `reserveMsat` reads the local
endpoint's advertised reserve.  Under BOLT 2 direction (D1) that value is the
reserve the *remote* side must keep, so `reserveMsat` is the inverted reading
for local outbound.  This theorem is definitional: it does not change the old
predicate, it only makes the old side explicit. -/
theorem reserveMsat_eq_localEndpoint (c : Channel) :
    reserveMsat c =
      c.localEndpoint.params.channelReserveSat * Msat.MSAT_PER_SAT := rfl

/-- When both endpoints advertise the same reserve, the corrected outbound
value coincides with the legacy value.  The repair therefore changes only the
direction, not the arithmetic; on symmetric channels the old number was
accidentally right. -/
theorem availableOutboundCorrected_eq_availableOutbound_of_reserve_eq
    (c : Channel)
    (h : c.localEndpoint.params.channelReserveSat =
      c.remoteEndpoint.params.channelReserveSat) :
    availableOutboundCorrected c = availableOutbound c := by
  rw [availableOutboundCorrected_eq, availableOutbound, reserveMsat, h]

/-! ## Upper-bound boundaries -/

/-- The corrected outbound value never exceeds the raw local balance.  This is
the only arithmetic guarantee claimed here: fees, anchors, dust, and in-flight
HTLCs are **not** subtracted, so equality with LDK's outbound capacity is not
claimed. -/
theorem availableOutboundCorrected_le_outboundLiquidity (c : Channel) :
    availableOutboundCorrected c ≤ outboundLiquidity c :=
  Nat.sub_le _ _

/-- The corrected inbound value never exceeds the raw remote balance.  It
likewise omits fees, anchors, dust, and in-flight HTLCs. -/
theorem availableInboundCorrected_le_inboundLiquidity (c : Channel) :
    availableInboundCorrected c ≤ inboundLiquidity c :=
  Nat.sub_le _ _

/-! ## Concrete witnesses -/

/-- Parameters with a chosen advertised `channel_reserve_satoshis`; all other
amounts are zero so that the witnesses isolate the reserve direction. -/
def witnessParams (reserveSat : Nat) : ChannelParams :=
  { dustLimitSat := 0
    channelReserveSat := reserveSat
    toSelfDelay := 0
    maxHtlcValue := ⟨0⟩
    htlcMinimum := ⟨0⟩
    feerate := ⟨0⟩
    anchorOutputs := false }

/-- An endpoint carrying `witnessParams reserveSat`. -/
def witnessEndpoint (reserveSat : Nat) : Endpoint :=
  { nodeId := ⟨ByteArray.empty⟩
    fundingPubKey := ⟨ByteArray.empty⟩
    paymentBasepoint := ⟨ByteArray.empty⟩
    delayedPaymentBasepoint := ⟨ByteArray.empty⟩
    params := witnessParams reserveSat }

/-- A concrete channel: both reserves, both balances, and no HTLCs are
parameters.  It is used only to instantiate the separation and non-vacuity
witnesses below. -/
def witnessChannel (localReserveSat remoteReserveSat localBalanceMsat
    remoteBalanceMsat : Nat) : Channel :=
  { channelId := ⟨ByteArray.empty⟩
    funding := { txid := ByteArray.empty, index := 0 }
    fundingValue := ⟨localBalanceMsat + remoteBalanceMsat⟩
    localEndpoint := witnessEndpoint localReserveSat
    remoteEndpoint := witnessEndpoint remoteReserveSat
    phase := ChannelPhase.normal
    localCommitmentNumber := 0
    remoteCommitmentNumber := 0
    balance :=
      { localBalance := ⟨localBalanceMsat⟩
        remoteBalance := ⟨remoteBalanceMsat⟩ }
    htlcs := [] }

/-- **Reserve direction separates legacy from corrected outbound.**  The
witness advertises local reserve 0 and remote reserve 1 sat, holds 1000 msat
locally and 0 remotely, and has no HTLCs.  The legacy `reserveMsat` reads the
local endpoint and reports 0, so `availableOutbound = 1000`; the corrected
`localReserveMsat` reads the remote endpoint and reports 1000, so
`availableOutboundCorrected = 0`.  BOLT 2 D1 says the remote endpoint's
advertised reserve is the one the local side must keep, hence 0 is the
faithful outbound figure for this channel. -/
theorem reserve_direction_separates :
    ∃ c : Channel,
      c.localEndpoint.params.channelReserveSat = 0 ∧
      c.remoteEndpoint.params.channelReserveSat = 1 ∧
      reserveMsat c = 0 ∧
      localReserveMsat c = Msat.MSAT_PER_SAT ∧
      availableOutbound c = 1000 ∧
      availableOutboundCorrected c = 0 := by
  refine ⟨witnessChannel 0 1 1000 0, ?_⟩
  decide

/-- **The corrected predicate is inhabited and non-empty.**  With both
endpoints advertising a zero reserve, the corrected outbound value is the full
1000 msat local balance: the corrected reading is not an always-zero or
otherwise vacuous predicate. -/
theorem corrected_outbound_nonempty :
    ∃ c : Channel,
      localReserveMsat c = 0 ∧
      remoteReserveMsatCorrected c = 0 ∧
      availableOutboundCorrected c = 1000 ∧
      0 < availableOutboundCorrected c := by
  refine ⟨witnessChannel 0 0 1000 0, ?_⟩
  decide

/-! ## Axiom audit -/

#print axioms reserveMsat_eq_localEndpoint
#print axioms availableOutboundCorrected_eq_availableOutbound_of_reserve_eq
#print axioms availableOutboundCorrected_le_outboundLiquidity
#print axioms availableInboundCorrected_le_inboundLiquidity
#print axioms reserve_direction_separates
#print axioms corrected_outbound_nonempty

end LnLean.Proofs.Wave14.LiquidityReserve
