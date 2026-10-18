import LnLean.Protocol.Handshake
import LnLean.Protocol.Laws
import LnLean.Protocol.Messages
import LnLean.Protocol.Peer

/-!
# D17 — `open_channel` funding bounds

## English claim

An `open_channel` message is accepted only when its `funding_satoshis` is
above the negotiated dust limit and at or above the acceptor's minimum
channel value.  This module states that boundary as an acceptor predicate and
proves the two bounds, together with the rejection directions.

## Where the claim lives in the model

The wave-A `LnLean.Protocol.Handshake` module deliberately has no
`open_channel` constructor: `Messages.lean`'s "What is NOT modelled" section
records that the arrival of `open_channel` is absorbed into the
`HandshakeState.canSendAccept` guard.  Consequently the catalog target
`LnLean.Protocol.Handshake.open_bounds` does not exist in the committed model,
and there is no existing field in which a funding amount could be bounded.

To state the claim faithfully without modifying the model, this module
introduces the minimal acceptor-side record and validation function that the
BOLT 2 text describes.  The record contains only the `open_channel` fields
that the funding bound depends on: `funding_satoshis`, `push_msat`,
`dust_limit_satoshis`, and `channel_reserve_satoshis`.

## BOLT sections

* BOLT 2 §"The `open_channel` Message"
  (`refs/bolts/02-peer-protocol.md:680-890`):
  * `dust_limit_satoshis` is the threshold below which outputs are not
    generated (`:727-733`);
  * the receiver MAY fail the channel if `funding_satoshis` is too small
    (`:850`);
  * the receiver MUST fail if `dust_limit_satoshis` is greater than
    `channel_reserve_satoshis` (`:869`) or smaller than `354 satoshis`
    (`:870`);
  * `push_msat` must not exceed `1000 * funding_satoshis` (`:808`);
  * absent `option_support_large_channel`, `funding_satoshis` must be less
    than `2^24` (`:805-808`, `:873`).

## rust-lightning anchors (commit fe49009)

* `lightning/src/ln/channelmanager.rs:17521` `handle_open_channel`, the
  catalog anchor, dispatches into `internal_open_channel`.
* `lightning/src/ln/channel.rs:4182` rejects a channel value below
  `MIN_CHANNEL_VALUE_SATOSHIS` (1000 sat, declared at `:1031`).
* `lightning/src/ln/channel.rs:4198` rejects a channel value at or above
  `TOTAL_BITCOIN_SUPPLY_SATOSHIS` (`:1003`).
* `lightning/src/ln/channel.rs:4202` rejects a reserve larger than the
  channel value; `:4209` rejects a dust limit larger than the channel value.
* `lightning/src/ln/channel.rs:4267` enforces the configured
  `min_funding_satoshis` policy bound.
* `lightning/src/ln/channel.rs:4308` rejects a dust limit below
  `MIN_CHAN_DUST_LIMIT_SATOSHIS` (`:1025`).
* `lightning/src/ln/channel.rs:4354` rejects a channel whose reserve leaves
  no spendable value after the dust-limit check.

## What is modelled, and what is not

* The acceptor check is a single predicate.  It is the conjunction of the
  budget-independent BOLT 2 and LDK conditions that mention the funding
  amount, the dust limit, the reserve, or `push_msat`.
* Fee sufficiency, commitment-output checks, chain-hash checks, key
  validity, channel type, and feature negotiation are outside this module.
  They do not affect the two funding bounds proved here.
* The strict dust condition `dust_limit_satoshis < funding_satoshis` is the
  stated claim ("only above the dust bound").  LDK's literal check is the
  weaker `dust_limit_satoshis ≤ channel_value_satoshis`
  (`channel.rs:4209`); the strict form is the acceptor policy used here and
  is documented in the report.
-/

namespace LnLean.Proofs.WaveD.D17

set_option autoImplicit false

open LnLean

-- OBLIGATION: LN-WD-D17

/-! ## Constants fixed by BOLT 2 / LDK -/

/-- LDK's hard lower bound on a channel value, in satoshis
(`MIN_CHANNEL_VALUE_SATOSHIS`, `channel.rs:1031`). -/
def minChannelValueSatoshis : Nat := 1000

/-- BOLT 2's lower bound on a peer's `dust_limit_satoshis`, in satoshis
(`02-peer-protocol.md:870`, `MIN_CHAN_DUST_LIMIT_SATOSHIS` in
`channel.rs:1025`). -/
def minDustLimitSatoshis : Nat := 354

/-- Total bitcoin supply in satoshis; LDK rejects a channel value at or
above this (`channel.rs:1003`, `:4198`). -/
def totalBitcoinSupplySatoshis : Nat := 21000000 * 100000000

/-- `2^24` satoshis, BOLT 2's legacy large-channel threshold
(`02-peer-protocol.md:805-808`). -/
def largeChannelThresholdSatoshis : Nat := 16777216

/-! ## The `open_channel` funding fields -/

/-- The subset of BOLT 2 `open_channel` (`02-peer-protocol.md:686-706`) that
the funding-bound check reads.  Amounts are satoshis and millisatoshis,
matching the wire units. -/
structure OpenChannelMsg where
  /-- `funding_satoshis`: the amount the funder puts into the channel. -/
  fundingSatoshis : Nat
  /-- `push_msat`: the initial amount given to the receiver. -/
  pushMsat : Msat
  /-- `dust_limit_satoshis`: outputs below this are not generated. -/
  dustLimitSatoshis : Nat
  /-- `channel_reserve_satoshis`: the minimum balance kept by the peer. -/
  channelReserveSatoshis : Nat
deriving Repr, DecidableEq, BEq

/-- The acceptor's local policy.  `minFundingSatoshis` is LDK's
`ChannelHandshakeLimits::min_funding_satoshis`; `supportsLargeChannel` is the
negotiated `option_support_large_channel` bit. -/
structure AcceptPolicy where
  minFundingSatoshis : Nat
  supportsLargeChannel : Bool := false
deriving Repr, DecidableEq, BEq

namespace OpenChannelMsg

/-- The dust bound: the channel value is strictly above the negotiated dust
limit. -/
def dustBound (m : OpenChannelMsg) : Prop :=
  m.dustLimitSatoshis < m.fundingSatoshis

/-- The hard minimum-channel bound: at least LDK's 1000 satoshi floor. -/
def minChannelBound (m : OpenChannelMsg) : Prop :=
  minChannelValueSatoshis ≤ m.fundingSatoshis

/-- The policy minimum-channel bound. -/
def policyMinBound (p : AcceptPolicy) (m : OpenChannelMsg) : Prop :=
  p.minFundingSatoshis ≤ m.fundingSatoshis

/-- The acceptor-side validation predicate for the opening message.

It contains exactly the BOLT 2 / LDK conditions that mention the funding
amount, dust limit, reserve, or `push_msat`:

* the channel value is strictly above the negotiated dust limit;
* it is at least the hard 1000-satoshi minimum;
* it is at least the acceptor's configured `min_funding_satoshis`;
* the dust limit is itself in `[354, channel_reserve_satoshis]`;
* the reserve is no larger than the channel value;
* the channel value is below the total bitcoin supply;
* `push_msat ≤ 1000 * funding_satoshis`;
* unless large channels are supported, the value is below `2^24`. -/
def accepts (p : AcceptPolicy) (m : OpenChannelMsg) : Prop :=
  m.dustBound ∧
  m.minChannelBound ∧
  OpenChannelMsg.policyMinBound p m ∧
  minDustLimitSatoshis ≤ m.dustLimitSatoshis ∧
  m.dustLimitSatoshis ≤ m.channelReserveSatoshis ∧
  m.channelReserveSatoshis ≤ m.fundingSatoshis ∧
  m.fundingSatoshis < totalBitcoinSupplySatoshis ∧
  m.pushMsat.val ≤ m.fundingSatoshis * Msat.MSAT_PER_SAT ∧
  (p.supportsLargeChannel = true ∨
    m.fundingSatoshis < largeChannelThresholdSatoshis)

/-- Decidability of the acceptor predicate, used by the transition below. -/
instance instDecidableAccepts (p : AcceptPolicy) (m : OpenChannelMsg) :
    Decidable (OpenChannelMsg.accepts p m) := by
  unfold OpenChannelMsg.accepts OpenChannelMsg.dustBound
    OpenChannelMsg.minChannelBound OpenChannelMsg.policyMinBound
  infer_instance

end OpenChannelMsg

/-- The receipt issued when an `open_channel` message passes validation. -/
structure OpenChannelAcceptance where
  fundingSatoshis : Nat
  dustLimitSatoshis : Nat
  channelReserveSatoshis : Nat
  minFundingSatoshis : Nat
deriving Repr, DecidableEq, BEq

/-- The acceptor transition: `some receipt` exactly when `accepts` holds.
This is the local replacement for the missing
`LnLean.Protocol.Handshake.open_bounds` boundary. -/
def acceptOpenChannel (p : AcceptPolicy) (m : OpenChannelMsg) :
    Option OpenChannelAcceptance :=
  if OpenChannelMsg.accepts p m then
    some
      { fundingSatoshis := m.fundingSatoshis
        dustLimitSatoshis := m.dustLimitSatoshis
        channelReserveSatoshis := m.channelReserveSatoshis
        minFundingSatoshis := p.minFundingSatoshis }
  else
    none

/-! ## Positive direction: every accepted message satisfies the bounds -/

/-- The three funding bounds extracted from a successful acceptance.  This is
the module's form of the catalog target `Handshake.open_bounds`. -/
theorem waveD_d17_open_bounds {p : AcceptPolicy} {m : OpenChannelMsg}
    {a : OpenChannelAcceptance}
    (h : acceptOpenChannel p m = some a) :
    m.dustLimitSatoshis < m.fundingSatoshis ∧
    minChannelValueSatoshis ≤ m.fundingSatoshis ∧
    p.minFundingSatoshis ≤ m.fundingSatoshis := by
  unfold acceptOpenChannel at h
  split at h
  · rename_i hacc
    exact ⟨hacc.1, hacc.2.1, hacc.2.2.1⟩
  · simp at h

/-- An accepted `open_channel` puts the channel value strictly above the
message's `dust_limit_satoshis`. -/
theorem waveD_d17_accept_funding_above_dust {p : AcceptPolicy}
    {m : OpenChannelMsg} {a : OpenChannelAcceptance}
    (h : acceptOpenChannel p m = some a) :
    m.dustLimitSatoshis < m.fundingSatoshis :=
  (waveD_d17_open_bounds h).1

/-- An accepted `open_channel` meets the hard minimum channel value of 1000
satoshis. -/
theorem waveD_d17_accept_funding_at_least_min_channel {p : AcceptPolicy}
    {m : OpenChannelMsg} {a : OpenChannelAcceptance}
    (h : acceptOpenChannel p m = some a) :
    minChannelValueSatoshis ≤ m.fundingSatoshis :=
  (waveD_d17_open_bounds h).2.1

/-- An accepted `open_channel` meets the acceptor's configured
`min_funding_satoshis`. -/
theorem waveD_d17_accept_funding_at_least_policy_min {p : AcceptPolicy}
    {m : OpenChannelMsg} {a : OpenChannelAcceptance}
    (h : acceptOpenChannel p m = some a) :
    p.minFundingSatoshis ≤ m.fundingSatoshis :=
  (waveD_d17_open_bounds h).2.2

/-- An accepted opening also satisfies BOLT 2's reserve/dust ordering: the
negotiated dust limit is no larger than the reserve. -/
theorem waveD_d17_accept_reserve_at_least_dust {p : AcceptPolicy}
    {m : OpenChannelMsg} {a : OpenChannelAcceptance}
    (h : acceptOpenChannel p m = some a) :
    m.dustLimitSatoshis ≤ m.channelReserveSatoshis := by
  unfold acceptOpenChannel at h
  split at h
  · rename_i hacc
    exact hacc.2.2.2.2.1
  · simp at h

/-! ## Negative direction: values at or below a bound are rejected -/

/-- A funding amount at or below the negotiated dust limit is rejected. -/
theorem waveD_d17_reject_of_funding_le_dust {p : AcceptPolicy}
    {m : OpenChannelMsg}
    (h : m.fundingSatoshis ≤ m.dustLimitSatoshis) :
    acceptOpenChannel p m = none := by
  unfold acceptOpenChannel
  have hnot : ¬ OpenChannelMsg.accepts p m := by
    intro hacc
    exact Nat.not_lt_of_ge h hacc.1
  simp [hnot]

/-- A funding amount below the hard minimum channel value is rejected. -/
theorem waveD_d17_reject_of_funding_below_min_channel {p : AcceptPolicy}
    {m : OpenChannelMsg}
    (h : m.fundingSatoshis < minChannelValueSatoshis) :
    acceptOpenChannel p m = none := by
  unfold acceptOpenChannel
  have hnot : ¬ OpenChannelMsg.accepts p m := by
    intro hacc
    exact Nat.not_le_of_gt h hacc.2.1
  simp [hnot]

/-- A funding amount below the acceptor's configured policy minimum is
rejected. -/
theorem waveD_d17_reject_of_funding_below_policy_min {p : AcceptPolicy}
    {m : OpenChannelMsg}
    (h : m.fundingSatoshis < p.minFundingSatoshis) :
    acceptOpenChannel p m = none := by
  unfold acceptOpenChannel
  have hnot : ¬ OpenChannelMsg.accepts p m := by
    intro hacc
    exact Nat.not_le_of_gt h hacc.2.2.1
  simp [hnot]

/-! ## Non-vacuity witnesses -/

/-- A concrete policy: 1000 satoshi minimum, legacy (non-large) channels. -/
def examplePolicy : AcceptPolicy where
  minFundingSatoshis := 1000
  supportsLargeChannel := false

/-- A concrete valid opening: 100000 sat, 546 sat dust, 1000 sat reserve. -/
def acceptedExample : OpenChannelMsg where
  fundingSatoshis := 100000
  pushMsat := ⟨0⟩
  dustLimitSatoshis := 546
  channelReserveSatoshis := 1000

/-- The same opening with the funding amount set exactly to the dust limit. -/
def dustRejectedExample : OpenChannelMsg where
  fundingSatoshis := 546
  pushMsat := ⟨0⟩
  dustLimitSatoshis := 546
  channelReserveSatoshis := 1000

/-- A second rejected opening: one satoshi below the hard minimum channel
value. -/
def belowMinChannelExample : OpenChannelMsg where
  fundingSatoshis := 999
  pushMsat := ⟨0⟩
  dustLimitSatoshis := 546
  channelReserveSatoshis := 999

/-- The accepted witness really is accepted. -/
theorem waveD_d17_example_accepted :
    acceptOpenChannel examplePolicy acceptedExample =
      some
        { fundingSatoshis := 100000
          dustLimitSatoshis := 546
          channelReserveSatoshis := 1000
          minFundingSatoshis := 1000 } := by
  unfold acceptOpenChannel OpenChannelMsg.accepts OpenChannelMsg.dustBound
    OpenChannelMsg.minChannelBound OpenChannelMsg.policyMinBound
  decide

/-- The dust-equality witness is rejected, so the strict dust bound is not
vacuous. -/
theorem waveD_d17_example_dust_rejected :
    acceptOpenChannel examplePolicy dustRejectedExample = none := by
  unfold acceptOpenChannel OpenChannelMsg.accepts OpenChannelMsg.dustBound
    OpenChannelMsg.minChannelBound OpenChannelMsg.policyMinBound
  decide

/-- The below-minimum witness is rejected, so the minimum-channel bound is not
vacuous. -/
theorem waveD_d17_example_below_min_rejected :
    acceptOpenChannel examplePolicy belowMinChannelExample = none := by
  unfold acceptOpenChannel OpenChannelMsg.accepts OpenChannelMsg.dustBound
    OpenChannelMsg.minChannelBound OpenChannelMsg.policyMinBound
  decide

end LnLean.Proofs.WaveD.D17
