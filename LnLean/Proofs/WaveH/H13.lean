/-
# H13 — the BOLT 2 type-32 `open_channel` wire record and its fixed payload
length (`L1-03`)

**Issue.** `L1-03` (P1, open/mitigated): `LnLean.Protocol.Messages` has no
`open_channel` (type 32) constructor at all, so the opener's funding message is
not represented on the wire and the funding-negotiation phase has no wire
payload.  Wave 7 added `Protocol.Handshake.OpenChannel` — a *four-field*
funding projection (temporary channel id, funding satoshis, push msat, funding
pubkey) — plus the `FundingPhase`/`fundingStep` machine, but its report could
only propose the `Messages.lean` patch.  This module is the additive wire record
that patch needs, kept local because `Protocol/Messages.lean` is a shared file
outside this lane's write set.

**Result.** `OpenChannelMsg` carries every fixed BOLT 2 `open_channel` field in
BOLT 2 order plus the optional `open_channel_tlvs` stream, and

* `fixedPayloadLength` — the sum of the eighteen fixed field widths — is proved
  to be **`319` bytes** (`fixedPayloadLength_eq_319`), with the field basis
  spelled out both term-by-term (`fixedPayloadLength_decomposition`) and grouped
  (`fixedPayloadLength_grouped`);
* `payloadLength` is exactly `319 + tlvsLength`, so the mandatory payload is
  `319` and every optional TLV is additional (`payloadLength_eq`,
  `payloadLength_no_tlvs`);
* the TLV accounting is exact — type (BigSize) + length (BigSize) + value — so a
  34-byte `upfront_shutdown_script` gives `355` payload bytes
  (`payloadLength_upfront_34`) and a payload fits BOLT 1's `65535`-byte frame
  whenever the TLV bytes fit (`payloadLength_le_65535`);
* **the task's `313` is not the BOLT 2 value.**  `313` is exactly the field sum
  of the wave-7 patch sketch, which *omits* `chain_hash` (`32`) and
  `channel_reserve_satoshis` (`8`) and counts a 34-byte
  `shutdown_scriptpubkey` as a fixed field with no TLV type/length prefix
  (`2`).  `reducedBasisLength_eq_313` and `reducedBasis_gap` mechanize that
  reconciliation: the same message with a 34-byte shutdown script is
  `313 + 42 = 355` payload bytes.

## Why 319 and not 313 (field basis)

BOLT 2 §"The `open_channel` Message"
(`refs/bolts/02-peer-protocol.md:686-716`) lists:

| # | field | BOLT 1 type | bytes |
|---|---|---|---|
| 1 | `chain_hash` | `chain_hash` | 32 |
| 2 | `temporary_channel_id` | `32*byte` | 32 |
| 3 | `funding_satoshis` | `u64` | 8 |
| 4 | `push_msat` | `u64` | 8 |
| 5 | `dust_limit_satoshis` | `u64` | 8 |
| 6 | `max_htlc_value_in_flight_msat` | `u64` | 8 |
| 7 | `channel_reserve_satoshis` | `u64` | 8 |
| 8 | `htlc_minimum_msat` | `u64` | 8 |
| 9 | `feerate_per_kw` | `u32` | 4 |
| 10 | `to_self_delay` | `u16` | 2 |
| 11 | `max_accepted_htlcs` | `u16` | 2 |
| 12 | `funding_pubkey` | `point` | 33 |
| 13 | `revocation_basepoint` | `point` | 33 |
| 14 | `payment_basepoint` | `point` | 33 |
| 15 | `delayed_payment_basepoint` | `point` | 33 |
| 16 | `htlc_basepoint` | `point` | 33 |
| 17 | `first_per_commitment_point` | `point` | 33 |
| 18 | `channel_flags` | `byte` | 1 |
| — | `open_channel_tlvs` | TLV stream | variable |

Widths are BOLT 1 §"Fundamental Types" (`01-messaging.md:223-259`):
`u16`/`u32`/`u64` = 2/4/8, `chain_hash` = 32, `point` = 33 compressed bytes,
`byte` = 1.  The fixed sum is
`32 + 32 + 6*8 + 4 + 2 + 2 + 6*33 + 1 = 319`.

The wave-7 sketch in `agents/reports/swarm7/S7-L1-FUNDING-AUTH.md` §7.1 summed
`32 + 8 + 8 + 8 + 8 + 8 + 4 + 2 + 2 + 6*33 + 1 + 34 = 313`: it dropped
`chain_hash` and `channel_reserve_satoshis` and folded the 34-byte shutdown
script value in as if it were a fixed field.  `313 + 32 + 8 - 34 = 319`, and
the TLV prefix is still missing (`tlvEntryLength`), so `313` under-counts a real
message with that script by `42` bytes.

## What is modelled / not modelled

* The record is a **length model**, not a byte encoder: no field is serialized
  here (H14/H18 own encode/decode and truncation).  `wireLength` adds BOLT 1's
  two-byte message type, matching `Protocol.Messages.msgLength`, which excludes
  it.
* `fundingSatoshis : BtcAmount` (`= Int`) matches `Protocol.Handshake.OpenChannel`
  and `FundingNegotiation`; `pushMsat : Msat` keeps the unit distinct.  Wire
  range/non-negativity facts are an explicit predicate (`WellFormedOnWire`),
  not a change to the value representation.
* `channelFlags` is a `Nat` with the `FitsU8` width predicate so that BOLT 2's
  "undefined bits must be 0" rule can be stated later; only its one-byte width
  is used here.
* The TLV stream models the two defined `open_channel_tlvs` entries (type 0
  `upfront_shutdown_script`, type 1 `channel_type`), each as
  `Option ByteArray`; unknown TLV types are out of scope.
* No `Msg`/`MsgKind` constructor, `wireType` case, or root import is added:
  `LnLean.Protocol.Messages` is shared and untouched.  The exact patch is in
  `agents/reports/wave8/H13.md`.
* Authentication is not claimed.  `open_channel` carries no sender identity and
  no signature; transport attribution stays the explicit hypothesis of
  `FundingAuthTargets` (`docs/ASSUMPTIONS.md` §3).

## Anchors

* BOLT 2 §"Channel Establishment v1" (`refs/bolts/02-peer-protocol.md:629-680`)
  and §"The `open_channel` Message" (`:680-716`) — field list and TLV stream.
* BOLT 1 §"Fundamental Types" (`refs/bolts/01-messaging.md:221-259`) — widths;
  §"Lightning Message Format" (`:43-92`) — two-byte type and 65535-byte payload
  bound.
* rust-lightning `lightning/src/ln/msgs.rs:289` (`struct OpenChannel`), `:3295`
  (`impl Writeable`: exact field order, TLV types 0 and 1).
* Model: `LnLean/Protocol/Handshake.lean` §"Explicit `open_channel` coverage"
  (`OpenChannel`, `FundingPhase`), `LnLean/Wire/BigSize.lean` (`encode`,
  `encode_size_*`).
-/

import LnLean.Protocol.Handshake
import LnLean.Wire.BigSize

namespace LnLean.Proofs.WaveH.H13

set_option autoImplicit false

open LnLean

/-! ## 1. Fixed field widths (BOLT 2 field order, BOLT 1 widths) -/

/-- `chain_hash`: 32-byte chain identifier (BOLT 1 `:252`). -/
def wChainHash : Nat := 32

/-- `temporary_channel_id`: `32*byte` (BOLT 2 `:689`). -/
def wTemporaryChannelId : Nat := 32

/-- `funding_satoshis`: `u64`. -/
def wFundingSatoshis : Nat := 8

/-- `push_msat`: `u64`. -/
def wPushMsat : Nat := 8

/-- `dust_limit_satoshis`: `u64`. -/
def wDustLimit : Nat := 8

/-- `max_htlc_value_in_flight_msat`: `u64`. -/
def wMaxHtlcValueInFlight : Nat := 8

/-- `channel_reserve_satoshis`: `u64`. -/
def wChannelReserve : Nat := 8

/-- `htlc_minimum_msat`: `u64`. -/
def wHtlcMinimum : Nat := 8

/-- `feerate_per_kw`: `u32`. -/
def wFeerate : Nat := 4

/-- `to_self_delay`: `u16`. -/
def wToSelfDelay : Nat := 2

/-- `max_accepted_htlcs`: `u16`. -/
def wMaxAcceptedHtlcs : Nat := 2

/-- A `point` is a 33-byte compressed public key (BOLT 1 `:257`).  Six of the
eighteen fixed fields are points. -/
def wPoint : Nat := 33

/-- `channel_flags`: one `byte`. -/
def wChannelFlags : Nat := 1

/-- BOLT 1 message type: two bytes, excluded from `Protocol.Messages.msgLength`
and from `payloadLength` here. -/
def wMessageType : Nat := 2

/-! ## 2. The wire record -/

/-- Optional `open_channel_tlvs` (BOLT 2 `:708-715`).  Both defined entries are
`Option`; an absent entry contributes no bytes. -/
structure OpenChannelTlvs where
  /-- TLV type 0 `upfront_shutdown_script`: the twenty-byte or thirty-four-byte
  witness program, or the empty script. -/
  upfrontShutdownScript : Option ByteArray := none
  /-- TLV type 1 `channel_type`: the explicit channel-type feature bit set. -/
  channelType : Option ByteArray := none
deriving Repr, BEq

/-- BOLT 2 `open_channel` (wire type 32), in BOLT 2 field order.  All eighteen
fixed fields are present; `chain_hash` and `channel_reserve_satoshis` are
included, which the wave-7 patch sketch omitted. -/
structure OpenChannelMsg where
  /-- BOLT 2 `chain_hash`: the chain the channel lives on. -/
  chainHash : ChainHash
  /-- BOLT 2 `temporary_channel_id`. -/
  temporaryChannelId : ChannelId
  /-- BOLT 2 `funding_satoshis`, the L1 output value. -/
  fundingSatoshis : LnLean.Bitcoin.BtcAmount
  /-- BOLT 2 `push_msat`, the opener's initial gift. -/
  pushMsat : Msat
  /-- BOLT 2 `dust_limit_satoshis`. -/
  dustLimitSatoshis : Nat
  /-- BOLT 2 `max_htlc_value_in_flight_msat`. -/
  maxHtlcValueInFlightMsat : Nat
  /-- BOLT 2 `channel_reserve_satoshis`. -/
  channelReserveSatoshis : Nat
  /-- BOLT 2 `htlc_minimum_msat`. -/
  htlcMinimumMsat : Nat
  /-- BOLT 2 `feerate_per_kw`. -/
  feeratePerKw : Nat
  /-- BOLT 2 `to_self_delay`. -/
  toSelfDelay : Nat
  /-- BOLT 2 `max_accepted_htlcs`. -/
  maxAcceptedHtlcs : Nat
  /-- BOLT 2 `funding_pubkey`: the opener's key in the 2-of-2 funding script. -/
  fundingPubKey : PubKey
  /-- BOLT 2 `revocation_basepoint`. -/
  revocationBasepoint : PubKey
  /-- BOLT 2 `payment_basepoint`. -/
  paymentBasepoint : PubKey
  /-- BOLT 2 `delayed_payment_basepoint`. -/
  delayedPaymentBasepoint : PubKey
  /-- BOLT 2 `htlc_basepoint`. -/
  htlcBasepoint : PubKey
  /-- BOLT 2 `first_per_commitment_point`. -/
  firstPerCommitmentPoint : PubKey
  /-- BOLT 2 `channel_flags`: only the `announce_channel` bit is defined. -/
  channelFlags : Nat
  /-- Optional `open_channel_tlvs`; defaulted so that fixed-field literals do not
  have to mention it. -/
  tlvs : OpenChannelTlvs := {}
deriving Repr, BEq

/-! ## 3. The fixed payload length is 319 -/

/-- The mandatory payload: the sum of the eighteen fixed field widths, in BOLT 2
order.  Optional TLVs are additional. -/
def OpenChannelMsg.fixedPayloadLength : Nat :=
  wChainHash + wTemporaryChannelId + wFundingSatoshis + wPushMsat +
  wDustLimit + wMaxHtlcValueInFlight + wChannelReserve + wHtlcMinimum +
  wFeerate + wToSelfDelay + wMaxAcceptedHtlcs +
  wPoint + wPoint + wPoint + wPoint + wPoint + wPoint +
  wChannelFlags

/-- **Field-basis statement.**  Term by term, in the BOLT 2 field order of
`refs/bolts/02-peer-protocol.md:688-705`. -/
theorem fixedPayloadLength_decomposition :
    OpenChannelMsg.fixedPayloadLength =
      32 + 32 + 8 + 8 + 8 + 8 + 8 + 8 + 4 + 2 + 2 +
        33 + 33 + 33 + 33 + 33 + 33 + 1 := by
  unfold OpenChannelMsg.fixedPayloadLength wChainHash wTemporaryChannelId
    wFundingSatoshis wPushMsat wDustLimit wMaxHtlcValueInFlight wChannelReserve
    wHtlcMinimum wFeerate wToSelfDelay wMaxAcceptedHtlcs wPoint wChannelFlags
  decide

/-- The same sum grouped by BOLT 1 width class: two 32-byte ids, six `u64`,
one `u32`, two `u16`, six points, one byte. -/
theorem fixedPayloadLength_grouped :
    OpenChannelMsg.fixedPayloadLength = 32 + 32 + 6 * 8 + 4 + 2 + 2 + 6 * 33 + 1 := by
  unfold OpenChannelMsg.fixedPayloadLength wChainHash wTemporaryChannelId
    wFundingSatoshis wPushMsat wDustLimit wMaxHtlcValueInFlight wChannelReserve
    wHtlcMinimum wFeerate wToSelfDelay wMaxAcceptedHtlcs wPoint wChannelFlags
  decide

/-- **The fixed BOLT 2 `open_channel` payload is 319 bytes.**  This is the exact
value derived from the local BOLT reference; the wave-8 task table's `313` is
reconciled in §6. -/
theorem fixedPayloadLength_eq_319 :
    OpenChannelMsg.fixedPayloadLength = 319 := by
  rw [fixedPayloadLength_grouped]

/-- The mandatory payload alone fits BOLT 1's two-byte framing bound. -/
theorem fixedPayloadLength_le_65535 : OpenChannelMsg.fixedPayloadLength ≤ 65535 := by
  rw [fixedPayloadLength_eq_319]
  decide

/-! ## 4. TLV accounting and the payload length -/

/-- Bytes of one TLV record: a BigSize type, a canonical BigSize length, and the
value (BOLT 1 §"Type-Length-Value Format"). -/
def tlvEntryLength (typ : Nat) (value : ByteArray) : Nat :=
  (LnLean.Wire.encode typ).size + (LnLean.Wire.encode value.size).size + value.size

/-- Every BigSize encoding consumes at least one byte. -/
theorem encode_size_pos (n : Nat) : 0 < (LnLean.Wire.encode n).size := by
  rcases LnLean.Wire.encode_size_cases n with h | h | h | h <;> omega

/-- Every TLV record is non-empty. -/
theorem tlvEntryLength_pos (typ : Nat) (value : ByteArray) :
    0 < tlvEntryLength typ value := by
  unfold tlvEntryLength
  have h1 := encode_size_pos typ
  omega

/-- A TLV whose type and length both fit in one BigSize byte costs
`2 + value.size` bytes. -/
theorem tlvEntryLength_short (typ : Nat) (value : ByteArray)
    (ht : typ < 0xfd) (hv : value.size < 0xfd) :
    tlvEntryLength typ value = 2 + value.size := by
  unfold tlvEntryLength
  rw [LnLean.Wire.encode_size_lt_0xfd typ ht,
    LnLean.Wire.encode_size_lt_0xfd value.size hv]

namespace OpenChannelTlvs

/-- Total bytes of the optional TLV stream. -/
def tlvsLength (t : OpenChannelTlvs) : Nat :=
  (match t.upfrontShutdownScript with
    | none => 0
    | some v => tlvEntryLength 0 v) +
  (match t.channelType with
    | none => 0
    | some v => tlvEntryLength 1 v)

/-- No TLVs, no bytes. -/
@[simp] theorem tlvsLength_empty :
    ({} : OpenChannelTlvs).tlvsLength = 0 := rfl

/-- Only the type-0 `upfront_shutdown_script` entry is present. -/
theorem tlvsLength_upfront_only (spk : ByteArray) :
    ({ upfrontShutdownScript := some spk, channelType := none } :
        OpenChannelTlvs).tlvsLength = tlvEntryLength 0 spk := by
  simp [tlvsLength]

/-- Only the type-1 `channel_type` entry is present. -/
theorem tlvsLength_channelType_only (ct : ByteArray) :
    ({ upfrontShutdownScript := none, channelType := some ct } :
        OpenChannelTlvs).tlvsLength = tlvEntryLength 1 ct := by
  simp [tlvsLength]

/-- The TLV stream is empty exactly when both defined entries are absent. -/
theorem tlvsLength_eq_zero_iff (t : OpenChannelTlvs) :
    t.tlvsLength = 0 ↔
      t.upfrontShutdownScript = none ∧ t.channelType = none := by
  constructor
  · intro h
    cases hu : t.upfrontShutdownScript with
    | none =>
      cases hc : t.channelType with
      | none => exact ⟨rfl, rfl⟩
      | some v =>
        have hp := tlvEntryLength_pos 1 v
        simp [tlvsLength, hu, hc] at h
        omega
    | some v =>
      have hp := tlvEntryLength_pos 0 v
      simp [tlvsLength, hu] at h
      omega
  · rintro ⟨hu, hc⟩
    simp [tlvsLength, hu, hc]

/-- A 34-byte shutdown script (P2WSH) costs `36` TLV bytes: type `0x00`, length
`0x22`, then the program. -/
theorem tlvsLength_upfront_34 (spk : ByteArray) (h : spk.size = 34) :
    ({ upfrontShutdownScript := some spk, channelType := none } :
        OpenChannelTlvs).tlvsLength = 36 := by
  rw [tlvsLength_upfront_only]
  rw [tlvEntryLength_short 0 spk (by decide) (by omega)]
  omega

end OpenChannelTlvs

namespace OpenChannelMsg

/-- Payload length in bytes, excluding BOLT 1's two-byte message type. -/
def payloadLength (m : OpenChannelMsg) : Nat :=
  OpenChannelMsg.fixedPayloadLength + m.tlvs.tlvsLength

/-- Total wire length including BOLT 1's two-byte message type. -/
def wireLength (m : OpenChannelMsg) : Nat :=
  wMessageType + m.payloadLength

/-- **The payload is 319 plus the optional TLV bytes.** -/
theorem payloadLength_eq (m : OpenChannelMsg) :
    m.payloadLength = 319 + m.tlvs.tlvsLength := by
  unfold payloadLength
  rw [fixedPayloadLength_eq_319]

/-- With no optional TLVs the payload is exactly the 319 fixed bytes. -/
theorem payloadLength_no_tlvs (m : OpenChannelMsg) (h : m.tlvs = {}) :
    m.payloadLength = 319 := by
  rw [payloadLength_eq, h]
  simp

/-- With a 34-byte `upfront_shutdown_script` and no `channel_type`, the payload
is `355 = 319 + 36` bytes. -/
theorem payloadLength_upfront_34 (m : OpenChannelMsg) (spk : ByteArray)
    (h : m.tlvs = { upfrontShutdownScript := some spk, channelType := none })
    (hspk : spk.size = 34) :
    m.payloadLength = 355 := by
  rw [payloadLength_eq, h, OpenChannelTlvs.tlvsLength_upfront_34 spk hspk]

/-- The wire length is the two-byte type plus the payload. -/
theorem wireLength_eq (m : OpenChannelMsg) :
    m.wireLength = 2 + m.payloadLength := by
  unfold wireLength wMessageType
  rfl

/-- Without TLVs the whole message is 321 bytes on the wire. -/
theorem wireLength_no_tlvs (m : OpenChannelMsg) (h : m.tlvs = {}) :
    m.wireLength = 321 := by
  rw [wireLength_eq, payloadLength_no_tlvs m h]

/-- Payload lengths are positive. -/
theorem payloadLength_pos (m : OpenChannelMsg) : 0 < m.payloadLength := by
  rw [payloadLength_eq]
  omega

/-- Payload lengths never decrease when a TLV is added. -/
theorem payloadLength_mono_tlvs {m₁ m₂ : OpenChannelMsg}
    (h : m₁.tlvs.tlvsLength ≤ m₂.tlvs.tlvsLength) :
    m₁.payloadLength ≤ m₂.payloadLength := by
  rw [payloadLength_eq m₁, payloadLength_eq m₂]
  omega

/-- The payload length is determined by the TLV stream alone: no fixed field
contributes a variable number of bytes.  Two messages with the same optional
TLVs have the same payload length, and equal payload lengths imply equal TLV
lengths. -/
theorem payloadLength_eq_iff (m₁ m₂ : OpenChannelMsg) :
    m₁.payloadLength = m₂.payloadLength ↔
      m₁.tlvs.tlvsLength = m₂.tlvs.tlvsLength := by
  rw [payloadLength_eq m₁, payloadLength_eq m₂]
  omega

/-- Equal TLV streams give equal payload lengths. -/
theorem payloadLength_congr_tlvs {m₁ m₂ : OpenChannelMsg}
    (h : m₁.tlvs = m₂.tlvs) : m₁.payloadLength = m₂.payloadLength := by
  simp [payloadLength, h]

/-- **Framing bound.**  If the optional TLV stream fits in `65216 = 65535 - 319`
bytes, the payload fits BOLT 1's two-byte length field.  BigSize is at most nine
bytes per entry, so this is never the binding constraint for two TLVs. -/
theorem payloadLength_le_65535 (m : OpenChannelMsg)
    (h : m.tlvs.tlvsLength ≤ 65216) : m.payloadLength ≤ 65535 := by
  rw [payloadLength_eq]
  omega

end OpenChannelMsg

/-! ## 5. Wire-range predicate and a concrete well-formed witness -/

/-- A value that fits BOLT 1's `byte` encoding. -/
def FitsU8 (n : Nat) : Prop := n < 2 ^ 8

/-- A value that fits BOLT 1's `u16` encoding. -/
def FitsU16 (n : Nat) : Prop := n < 2 ^ 16

/-- A value that fits BOLT 1's `u32` encoding. -/
def FitsU32 (n : Nat) : Prop := n < 2 ^ 32

/-- A value that fits BOLT 1's `u64` encoding. -/
def FitsU64 (n : Nat) : Prop := n < 2 ^ 64

/-- Wire-domain facts for an `open_channel`: identifiers and points have their
BOLT 1 sizes, the integer fields fit their declared widths, and the funding
value is a non-negative in-range Bitcoin amount.  This predicate is *not* used
by the length theorems; it records the field set the length is about. -/
def OpenChannelMsg.WellFormedOnWire (m : OpenChannelMsg) : Prop :=
  m.chainHash.Valid ∧
  m.temporaryChannelId.Valid ∧
  0 ≤ m.fundingSatoshis ∧
  m.fundingSatoshis ≤ Bitcoin.Data.MAX_MONEY ∧
  FitsU64 m.pushMsat.val ∧
  FitsU64 m.dustLimitSatoshis ∧
  FitsU64 m.maxHtlcValueInFlightMsat ∧
  FitsU64 m.channelReserveSatoshis ∧
  FitsU64 m.htlcMinimumMsat ∧
  FitsU32 m.feeratePerKw ∧
  FitsU16 m.toSelfDelay ∧
  FitsU16 m.maxAcceptedHtlcs ∧
  m.fundingPubKey.Valid ∧
  m.revocationBasepoint.Valid ∧
  m.paymentBasepoint.Valid ∧
  m.delayedPaymentBasepoint.Valid ∧
  m.htlcBasepoint.Valid ∧
  m.firstPerCommitmentPoint.Valid ∧
  FitsU8 m.channelFlags

/-- A concrete byte string of `n` zero bytes (witness construction only). -/
def zeros (n : Nat) : ByteArray :=
  ByteArray.mk (List.replicate n (0 : UInt8)).toArray

/-- `zeros n` has exactly `n` bytes. -/
theorem zeros_size (n : Nat) : (zeros n).size = n := by
  unfold zeros
  rw [← ByteArray.size_data]
  simp

/-- The minimal well-formed `open_channel` used to show the length theorem is
non-vacuous: mainnet chain hash (all zeroes here), zero-value channel, one
satoshi reserve, `feerate_per_kw = 253`, a 144-block `to_self_delay`, 483 HTLCs,
and the `announce_channel` flag. -/
def witness : OpenChannelMsg where
  chainHash := ⟨zeros 32⟩
  temporaryChannelId := ⟨zeros 32⟩
  fundingSatoshis := 1000000
  pushMsat := ⟨0⟩
  dustLimitSatoshis := 0
  maxHtlcValueInFlightMsat := 0
  channelReserveSatoshis := 1
  htlcMinimumMsat := 0
  feeratePerKw := 253
  toSelfDelay := 144
  maxAcceptedHtlcs := 483
  fundingPubKey := ⟨zeros 33⟩
  revocationBasepoint := ⟨zeros 33⟩
  paymentBasepoint := ⟨zeros 33⟩
  delayedPaymentBasepoint := ⟨zeros 33⟩
  htlcBasepoint := ⟨zeros 33⟩
  firstPerCommitmentPoint := ⟨zeros 33⟩
  channelFlags := 1
  tlvs := {}

/-- The witness satisfies every wire-width fact. -/
theorem witness_wellFormed : witness.WellFormedOnWire := by
  unfold OpenChannelMsg.WellFormedOnWire
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    first
    | decide
    | simp [witness, ChainHash.Valid, ChannelId.Valid, PubKey.Valid,
        FitsU8, FitsU16, FitsU32, FitsU64, zeros_size]

/-- The witness has no optional TLVs, so its payload is exactly 319 bytes. -/
theorem witness_payloadLength : witness.payloadLength = 319 :=
  OpenChannelMsg.payloadLength_no_tlvs witness rfl

/-- The witness's full wire length is 321 bytes. -/
theorem witness_wireLength : witness.wireLength = 321 :=
  OpenChannelMsg.wireLength_no_tlvs witness rfl

/-- The length result is non-vacuous: a well-formed record exists whose payload
is exactly the BOLT 2 fixed length. -/
theorem exists_wellFormed_payloadLength :
    ∃ m : OpenChannelMsg, m.WellFormedOnWire ∧ m.payloadLength = 319 :=
  ⟨witness, witness_wellFormed, witness_payloadLength⟩

/-! ## 6. Reconciliation with the task table's `313`

The wave-7 patch sketch's field basis.  It omits `chain_hash` (`32`) and
`channel_reserve_satoshis` (`8`), and counts a 34-byte `shutdown_scriptpubkey`
value as a fixed field (with no TLV type/length prefix). -/
def reducedBasisLength : Nat :=
  32 + 8 + 8 + 8 + 8 + 8 + 4 + 2 + 2 + 6 * 33 + 1 + 34

/-- The reduced basis sums to `313`, the figure in the wave-8 task table. -/
theorem reducedBasisLength_eq_313 : reducedBasisLength = 313 := by
  unfold reducedBasisLength
  decide

/-- `313 + 6 = 319`: the reduced basis is six bytes short of the BOLT 2 fixed
payload because `-32 (chain_hash) - 8 (channel_reserve) + 34 (shutdown) = -6`. -/
theorem reducedBasisLength_add_six :
    reducedBasisLength + 6 = OpenChannelMsg.fixedPayloadLength := by
  rw [reducedBasisLength_eq_313, fixedPayloadLength_eq_319]

/-- `313` is not the fixed BOLT 2 payload length. -/
theorem reducedBasisLength_ne_fixed :
    reducedBasisLength ≠ OpenChannelMsg.fixedPayloadLength := by
  rw [reducedBasisLength_eq_313, fixedPayloadLength_eq_319]
  decide

/-- The exact field-basis adjustment from the reduced basis to the fixed
payload: drop the 34-byte shutdown value, add `chain_hash` and
`channel_reserve_satoshis`. -/
theorem reducedBasisLength_adjustment :
    reducedBasisLength - 34 + 32 + 8 = OpenChannelMsg.fixedPayloadLength := by
  rw [reducedBasisLength_eq_313, fixedPayloadLength_eq_319]

/-- **The gap on a real message.**  The same `open_channel` with a 34-byte
`upfront_shutdown_script` and no `channel_type` has a `355`-byte payload, which
is `313 + 42`: the reduced basis misses `chain_hash` (`32`),
`channel_reserve_satoshis` (`8`), and the TLV type/length prefix (`2`). -/
theorem reducedBasis_gap (m : OpenChannelMsg) (spk : ByteArray)
    (h : m.tlvs = { upfrontShutdownScript := some spk, channelType := none })
    (hspk : spk.size = 34) :
    m.payloadLength = reducedBasisLength + 42 := by
  rw [OpenChannelMsg.payloadLength_upfront_34 m spk h hspk, reducedBasisLength_eq_313]

/-- The `42`-byte gap decomposes into the three omitted categories. -/
theorem reducedBasis_gap_decomposition : (42 : Nat) = 32 + 8 + 2 := by
  decide

/-! ## 7. Axiom audit -/

#print axioms fixedPayloadLength_decomposition
#print axioms fixedPayloadLength_grouped
#print axioms fixedPayloadLength_eq_319
#print axioms OpenChannelMsg.payloadLength_eq
#print axioms OpenChannelMsg.payloadLength_no_tlvs
#print axioms OpenChannelMsg.payloadLength_upfront_34
#print axioms OpenChannelMsg.wireLength_no_tlvs
#print axioms OpenChannelMsg.payloadLength_eq_iff
#print axioms OpenChannelMsg.payloadLength_le_65535
#print axioms OpenChannelTlvs.tlvsLength_eq_zero_iff
#print axioms OpenChannelTlvs.tlvsLength_upfront_34
#print axioms witness_wellFormed
#print axioms exists_wellFormed_payloadLength
#print axioms reducedBasisLength_eq_313
#print axioms reducedBasisLength_add_six
#print axioms reducedBasis_gap

end LnLean.Proofs.WaveH.H13
