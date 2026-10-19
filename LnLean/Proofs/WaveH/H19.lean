/-
# H19 — full BOLT 2 `accept_channel` payload at the handshake boundary (PR-01)

**Catalog issue.** `PR-01` (P1): `HandshakeState` carries only the boolean
`acceptReceived` flag; the `AcceptChannel` message is a `Msg` payload, but the
handshake boundary has no full, typed payload record that the later key
attribution/registration lanes (H20–H24) can store and project.  This module
adds that record *additively*: it does not edit `LnLean/Protocol/Messages.lean`
and it does not change `HandshakeState`.

## Result of this module

1. `AcceptChannelPayload` is the complete **mandatory** BOLT 2 `accept_channel`
   (type 33) field set in wire order — all fourteen fixed-width fields,
   including `funding_pubkey`, the four basepoints, and
   `first_per_commitment_point`.  It is the full field set of the message, not
   the funding-relevant projection that `Handshake.OpenChannel` uses.
2. The fixed payload length is proved to be **270 bytes** from the individual
   field widths: `fieldWidths` records each BOLT 2 width, `fieldWidthSum`
   computes `270`, and `mandatoryPayloadLength_eq_fieldWidthSum` /
   `payloadLength_eq` connect the arithmetic to the record.  This agrees with
   the existing `msgLength (.acceptChannel _) = 270` theorem
   (`payloadLength_eq_msgLength`), so the additive record cannot drift from the
   wire model.
3. Field projections: `toAcceptChannel` is a lossless bijection with the
   existing `Messages.AcceptChannel` record (`toAcceptChannel_ofAcceptChannel`,
   `ofAcceptChannel_toAcceptChannel`, `toAcceptChannel_injective`) and each of
   the fourteen fields has a `@[simp]` projection lemma.  The `Msg` boundary
   projections (`msgLength`, `msgType`, `channelId?`, `pubKeys`) are proved as
   well.
4. The handshake funding-key projection is proved: for any `AcceptChannelPayload`
   the remote funding key of `AcceptChannel.toFundingNegotiation` /
   `AcceptChannel.toFundingParams` is exactly `payload.fundingPubKey`
   (`toFundingNegotiation_remoteFundingKey`,
   `toFundingParams_remoteFundingKey`), and `sendFundingCreated` still implies
   that the accept message has already been received
   (`fundingKey_bound_before_fundingCreated`).
5. Structural validity is characterized: `AcceptChannelPayload.Valid`
   (32-byte temporary id, six 33-byte points) is *equivalent* to the existing
   `wellFormed (.acceptChannel p.toAcceptChannel)`
   (`wellFormed_toAcceptChannel_iff`).  A concrete all-zero-byte witness
   (`zeroPayload`) discharges vacuity.
6. The variable-length `accept_channel_tlvs` stream is modelled separately
   (`AcceptChannelTLVs`) with an exact additive length law
   `payloadLengthWithTLVs p t = 270 + tlvBytes t`; TLV bytes never shrink the
   payload (`payloadLength_le_withTLVs`) and a BigSize-derived bound is given.

## Basis of the 270-byte length

`refs/bolts/02-peer-protocol.md:913-929` (§"The `accept_channel` Message")
lists, in order:

```
32 temporary_channel_id
 8 dust_limit_satoshis
 8 max_htlc_value_in_flight_msat
 8 channel_reserve_satoshis
 8 htlc_minimum_msat
 4 minimum_depth
 2 to_self_delay
 2 max_accepted_htlcs
33 funding_pubkey
33 revocation_basepoint
33 payment_basepoint
33 delayed_payment_basepoint
33 htlc_basepoint
33 first_per_commitment_point
```

Sum: `32 + 4*8 + 4 + 2*2 + 6*33 = 32 + 32 + 4 + 4 + 198 = 270`.
The optional `accept_channel_tlvs` (types 0 `upfront_shutdown_script` and
1 `channel_type`, `refs/bolts/02-peer-protocol.md:931-938`) are **not** part of
the fixed-width sum; they are modelled additively in §"TLV extension".

## Hypotheses / scope

* The record models the **wire fields** only.  It does not model semantic
  `accept_channel` requirements (reserve/dust inequalities, `minimum_depth`,
  required `channel_type`, feature negotiation); those stay in the handshake
  and conformance layers.
* `deriving BEq` is structural; no `DecidableEq` is derived because the
  underlying `ByteArray` fields do not provide one.  Equality-based key
  attribution is therefore a hypothesis about the model, not a decision
  procedure (see `docs/ASSUMPTIONS.md` §3 on transport authentication).
* The record carries the funding **key**, not an attribution proof.  Any claim
  that the key belongs to the peer still needs the explicit transport /
  registration hypothesis tracked by `PR-01`; this module only proves that the
  key survives every projection.
* `ByteArray` values are never parsed here; widths are size facts.  A payload
  whose `ChannelId`/`PubKey` bytes have the wrong length is excluded by
  `Valid`, exactly as `wellFormed` excludes it.

## Integration patch (shared file, *not* applied)

`LnLean/Protocol/Messages.lean` already contains the fourteen fields, so no
semantic patch is required.  To expose this record at the message boundary the
parent may apply, in one parent-owned commit:

```lean
-- LnLean/Proofs/WaveH/H19.lean, after the module builds
-- LnLean.lean: import LnLean.Proofs.WaveH.H19
```

and, only if the handshake state is extended (lane H20's patch), the parent may
reuse `AcceptChannelPayload.toAcceptChannel`/`ofAcceptChannel` rather than
duplicating the field list.  No edit to `Messages.lean` is part of this lane.

## Anchors

* BOLT 2 §"The `accept_channel` Message" (`refs/bolts/02-peer-protocol.md:907-966`),
  wire type 33 at `:913`, field list at `:915-928`, TLVs at `:929-938`.
* BOLT 1 §"Lightning Message Format" (`refs/bolts/01-messaging.md:43-92`):
  two-byte type and the 65535-byte payload bound used by `wellFormed`.
* Model: `LnLean/Protocol/Messages.lean` (`AcceptChannel`, `msgLength`,
  `msgLength_acceptChannel`), `LnLean/Protocol/Handshake.lean`
  (`AcceptChannel.toFundingNegotiation`, `acceptReceived_of_sendFundingCreated`),
  `LnLean/Wire/BigSize.lean` (`encode_size_lt_0xfd`, `encode_size_le_nine`).
-/

import LnLean.Protocol.Handshake
import LnLean.Wire.BigSize

namespace LnLean.Proofs.WaveH.H19

set_option autoImplicit false

open LnLean
open LnLean.Protocol
open LnLean.Bitcoin

/-! ## The full mandatory `accept_channel` payload -/

/-- The complete mandatory BOLT 2 `accept_channel` (type 33) payload, in wire
order.  Field names follow `LnLean.Protocol.AcceptChannel` (BOLT 2 names in
lower camel case).  The optional `accept_channel_tlvs` stream is modelled by
`AcceptChannelTLVs` separately, because it is variable length. -/
structure AcceptChannelPayload where
  /-- BOLT 2 `temporary_channel_id` (`32*byte`). -/
  temporaryChannelId : ChannelId
  /-- BOLT 2 `dust_limit_satoshis` (`u64`). -/
  dustLimitSatoshis : Nat
  /-- BOLT 2 `max_htlc_value_in_flight_msat` (`u64`). -/
  maxHtlcValueInFlightMsat : Nat
  /-- BOLT 2 `channel_reserve_satoshis` (`u64`). -/
  channelReserveSatoshis : Nat
  /-- BOLT 2 `htlc_minimum_msat` (`u64`). -/
  htlcMinimumMsat : Nat
  /-- BOLT 2 `minimum_depth` (`u32`). -/
  minimumDepth : Nat
  /-- BOLT 2 `to_self_delay` (`u16`). -/
  toSelfDelay : Nat
  /-- BOLT 2 `max_accepted_htlcs` (`u16`). -/
  maxAcceptedHtlcs : Nat
  /-- BOLT 2 `funding_pubkey` (`point`).  The key that fixes the P2WSH
  funding script together with the opener's key. -/
  fundingPubKey : PubKey
  /-- BOLT 2 `revocation_basepoint` (`point`). -/
  revocationBasepoint : PubKey
  /-- BOLT 2 `payment_basepoint` (`point`). -/
  paymentBasepoint : PubKey
  /-- BOLT 2 `delayed_payment_basepoint` (`point`). -/
  delayedPaymentBasepoint : PubKey
  /-- BOLT 2 `htlc_basepoint` (`point`). -/
  htlcBasepoint : PubKey
  /-- BOLT 2 `first_per_commitment_point` (`point`). -/
  firstPerCommitmentPoint : PubKey
deriving Repr, BEq

namespace AcceptChannelPayload

/-! ### Field widths and the fixed payload length -/

/-- The BOLT 2 fixed field widths in bytes, in wire order.  Basis:
`refs/bolts/02-peer-protocol.md:915-928`. -/
def fieldWidths : List (String × Nat) :=
  [("temporary_channel_id", 32),
   ("dust_limit_satoshis", 8),
   ("max_htlc_value_in_flight_msat", 8),
   ("channel_reserve_satoshis", 8),
   ("htlc_minimum_msat", 8),
   ("minimum_depth", 4),
   ("to_self_delay", 2),
   ("max_accepted_htlcs", 2),
   ("funding_pubkey", 33),
   ("revocation_basepoint", 33),
   ("payment_basepoint", 33),
   ("delayed_payment_basepoint", 33),
   ("htlc_basepoint", 33),
   ("first_per_commitment_point", 33)]

/-- Sum of the BOLT 2 fixed field widths. -/
def fieldWidthSum : Nat := (fieldWidths.map (·.2)).sum

/-- The fixed-width sum is exactly `270` bytes. -/
theorem fieldWidthSum_eq : fieldWidthSum = 270 := by
  decide

/-- The fixed payload length of the mandatory `accept_channel` field set. -/
def mandatoryPayloadLength : Nat := 270

/-- The constant is the actual sum of the BOLT 2 field widths, not an
independently chosen number. -/
theorem mandatoryPayloadLength_eq_fieldWidthSum :
    mandatoryPayloadLength = fieldWidthSum := by
  decide

/-- The payload length of a concrete record.  It is constant: every mandatory
`accept_channel` field has a fixed wire width. -/
def payloadLength (_p : AcceptChannelPayload) : Nat := mandatoryPayloadLength

/-- Every mandatory `accept_channel` payload is exactly 270 bytes. -/
@[simp] theorem payloadLength_eq (p : AcceptChannelPayload) :
    p.payloadLength = 270 := rfl

/-! ### Projection to and from the existing message record

`toAcceptChannel`/`ofAcceptChannel` are the identity on the fourteen fields.
They are the bridge that lets later lanes store an `AcceptChannelPayload` while
reusing every existing `AcceptChannel`/`Msg` theorem.
-/

/-- The payload as the existing `Messages.AcceptChannel` record. -/
def toAcceptChannel (p : AcceptChannelPayload) : AcceptChannel :=
  { temporaryChannelId := p.temporaryChannelId
    dustLimitSatoshis := p.dustLimitSatoshis
    maxHtlcValueInFlightMsat := p.maxHtlcValueInFlightMsat
    channelReserveSatoshis := p.channelReserveSatoshis
    htlcMinimumMsat := p.htlcMinimumMsat
    minimumDepth := p.minimumDepth
    toSelfDelay := p.toSelfDelay
    maxAcceptedHtlcs := p.maxAcceptedHtlcs
    fundingPubKey := p.fundingPubKey
    revocationBasepoint := p.revocationBasepoint
    paymentBasepoint := p.paymentBasepoint
    delayedPaymentBasepoint := p.delayedPaymentBasepoint
    htlcBasepoint := p.htlcBasepoint
    firstPerCommitmentPoint := p.firstPerCommitmentPoint }

/-- The existing `Messages.AcceptChannel` record as a full payload. -/
def ofAcceptChannel (m : AcceptChannel) : AcceptChannelPayload :=
  { temporaryChannelId := m.temporaryChannelId
    dustLimitSatoshis := m.dustLimitSatoshis
    maxHtlcValueInFlightMsat := m.maxHtlcValueInFlightMsat
    channelReserveSatoshis := m.channelReserveSatoshis
    htlcMinimumMsat := m.htlcMinimumMsat
    minimumDepth := m.minimumDepth
    toSelfDelay := m.toSelfDelay
    maxAcceptedHtlcs := m.maxAcceptedHtlcs
    fundingPubKey := m.fundingPubKey
    revocationBasepoint := m.revocationBasepoint
    paymentBasepoint := m.paymentBasepoint
    delayedPaymentBasepoint := m.delayedPaymentBasepoint
    htlcBasepoint := m.htlcBasepoint
    firstPerCommitmentPoint := m.firstPerCommitmentPoint }

@[simp] theorem toAcceptChannel_ofAcceptChannel (m : AcceptChannel) :
    toAcceptChannel (ofAcceptChannel m) = m := rfl

@[simp] theorem ofAcceptChannel_toAcceptChannel (p : AcceptChannelPayload) :
    ofAcceptChannel (toAcceptChannel p) = p := rfl

/-- The projection loses no information. -/
theorem toAcceptChannel_injective :
    Function.Injective toAcceptChannel := by
  intro a b h
  have h' := congrArg ofAcceptChannel h
  simpa using h'

/-- The additive record agrees with the pre-existing wire length theorem, so
the two definitions cannot drift. -/
theorem payloadLength_eq_msgLength (p : AcceptChannelPayload) :
    p.payloadLength =
      msgLength (.acceptChannel (toAcceptChannel p)) := rfl

/-! ### Field projections -/

@[simp] theorem toAcceptChannel_temporaryChannelId (p : AcceptChannelPayload) :
    (toAcceptChannel p).temporaryChannelId = p.temporaryChannelId := rfl

@[simp] theorem toAcceptChannel_dustLimitSatoshis (p : AcceptChannelPayload) :
    (toAcceptChannel p).dustLimitSatoshis = p.dustLimitSatoshis := rfl

@[simp] theorem toAcceptChannel_maxHtlcValueInFlightMsat
    (p : AcceptChannelPayload) :
    (toAcceptChannel p).maxHtlcValueInFlightMsat =
      p.maxHtlcValueInFlightMsat := rfl

@[simp] theorem toAcceptChannel_channelReserveSatoshis
    (p : AcceptChannelPayload) :
    (toAcceptChannel p).channelReserveSatoshis = p.channelReserveSatoshis := rfl

@[simp] theorem toAcceptChannel_htlcMinimumMsat (p : AcceptChannelPayload) :
    (toAcceptChannel p).htlcMinimumMsat = p.htlcMinimumMsat := rfl

@[simp] theorem toAcceptChannel_minimumDepth (p : AcceptChannelPayload) :
    (toAcceptChannel p).minimumDepth = p.minimumDepth := rfl

@[simp] theorem toAcceptChannel_toSelfDelay (p : AcceptChannelPayload) :
    (toAcceptChannel p).toSelfDelay = p.toSelfDelay := rfl

@[simp] theorem toAcceptChannel_maxAcceptedHtlcs (p : AcceptChannelPayload) :
    (toAcceptChannel p).maxAcceptedHtlcs = p.maxAcceptedHtlcs := rfl

@[simp] theorem toAcceptChannel_fundingPubKey (p : AcceptChannelPayload) :
    (toAcceptChannel p).fundingPubKey = p.fundingPubKey := rfl

@[simp] theorem toAcceptChannel_revocationBasepoint (p : AcceptChannelPayload) :
    (toAcceptChannel p).revocationBasepoint = p.revocationBasepoint := rfl

@[simp] theorem toAcceptChannel_paymentBasepoint (p : AcceptChannelPayload) :
    (toAcceptChannel p).paymentBasepoint = p.paymentBasepoint := rfl

@[simp] theorem toAcceptChannel_delayedPaymentBasepoint
    (p : AcceptChannelPayload) :
    (toAcceptChannel p).delayedPaymentBasepoint = p.delayedPaymentBasepoint := rfl

@[simp] theorem toAcceptChannel_htlcBasepoint (p : AcceptChannelPayload) :
    (toAcceptChannel p).htlcBasepoint = p.htlcBasepoint := rfl

@[simp] theorem toAcceptChannel_firstPerCommitmentPoint
    (p : AcceptChannelPayload) :
    (toAcceptChannel p).firstPerCommitmentPoint = p.firstPerCommitmentPoint := rfl

/-! ### `Msg` boundary projections -/

/-- The message type carried by the projected payload is BOLT 2 type 33. -/
@[simp] theorem msgType_toAcceptChannel (p : AcceptChannelPayload) :
    msgType (.acceptChannel (toAcceptChannel p)) = 33 := rfl

/-- The wire length of the projected message is the payload length. -/
@[simp] theorem msgLength_toAcceptChannel (p : AcceptChannelPayload) :
    msgLength (.acceptChannel (toAcceptChannel p)) = p.payloadLength := rfl

/-- The channel identifier extracted by `channelId?` is the temporary
channel id. -/
@[simp] theorem channelId?_toAcceptChannel (p : AcceptChannelPayload) :
    channelId? (.acceptChannel (toAcceptChannel p)) =
      some p.temporaryChannelId := rfl

/-- `pubKeys` extracts exactly the six BOLT 2 points, in wire order. -/
@[simp] theorem pubKeys_toAcceptChannel (p : AcceptChannelPayload) :
    pubKeys (.acceptChannel (toAcceptChannel p)) =
      [p.fundingPubKey, p.revocationBasepoint, p.paymentBasepoint,
       p.delayedPaymentBasepoint, p.htlcBasepoint, p.firstPerCommitmentPoint] := rfl

/-! ### Structural validity -/

/-- Wire-domain validity of the full payload: a 32-byte temporary channel id
and six 33-byte compressed points.  This is exactly the identifier/key part of
`wellFormed`; length and signature checks are discharged below. -/
def Valid (p : AcceptChannelPayload) : Prop :=
  p.temporaryChannelId.Valid ∧
  p.fundingPubKey.Valid ∧
  p.revocationBasepoint.Valid ∧
  p.paymentBasepoint.Valid ∧
  p.delayedPaymentBasepoint.Valid ∧
  p.htlcBasepoint.Valid ∧
  p.firstPerCommitmentPoint.Valid

theorem Valid.temporaryChannelId {p : AcceptChannelPayload} (h : p.Valid) :
    p.temporaryChannelId.Valid := h.1

theorem Valid.fundingPubKey {p : AcceptChannelPayload} (h : p.Valid) :
    p.fundingPubKey.Valid := h.2.1

theorem Valid.revocationBasepoint {p : AcceptChannelPayload} (h : p.Valid) :
    p.revocationBasepoint.Valid := h.2.2.1

theorem Valid.paymentBasepoint {p : AcceptChannelPayload} (h : p.Valid) :
    p.paymentBasepoint.Valid := h.2.2.2.1

theorem Valid.delayedPaymentBasepoint {p : AcceptChannelPayload} (h : p.Valid) :
    p.delayedPaymentBasepoint.Valid := h.2.2.2.2.1

theorem Valid.htlcBasepoint {p : AcceptChannelPayload} (h : p.Valid) :
    p.htlcBasepoint.Valid := h.2.2.2.2.2.1

theorem Valid.firstPerCommitmentPoint {p : AcceptChannelPayload}
    (h : p.Valid) : p.firstPerCommitmentPoint.Valid := h.2.2.2.2.2.2

/-- The full payload is well formed at the message boundary exactly when its
identifiers and keys have BOLT 1/2 wire sizes.  The 270-byte length is under
the 65535-byte bound, the message carries no signatures, and it has no semantic
side conditions in the wire model. -/
theorem wellFormed_toAcceptChannel_iff (p : AcceptChannelPayload) :
    wellFormed (.acceptChannel (toAcceptChannel p)) ↔ p.Valid := by
  simp [wellFormed, msgLength, idsValid, channelId?, pubKeys,
    sigsValid, signatures, semanticOk, Valid]

/-- The same characterization for an arbitrary existing message record. -/
theorem wellFormed_ofAcceptChannel_iff (m : AcceptChannel) :
    wellFormed (.acceptChannel m) ↔ (ofAcceptChannel m).Valid := by
  rw [← toAcceptChannel_ofAcceptChannel m]
  exact wellFormed_toAcceptChannel_iff (ofAcceptChannel m)

/-! ### Non-vacuity -/

/-- `n` repetitions of a byte. -/
def bytesN (n : Nat) (b : UInt8) : ByteArray :=
  ByteArray.mk (List.replicate n b).toArray

theorem bytesN_size (n : Nat) (b : UInt8) : (bytesN n b).size = n := by
  simp [bytesN, ByteArray.size]

/-- A 33-byte point with the given repeated byte. -/
def pub33 (b : UInt8) : PubKey := ⟨bytesN 33 b⟩

theorem pub33_valid (b : UInt8) : (pub33 b).Valid := bytesN_size 33 b

/-- A 32-byte identifier with the given repeated byte. -/
def id32 (b : UInt8) : ChannelId := ⟨bytesN 32 b⟩

theorem id32_valid (b : UInt8) : (id32 b).Valid := bytesN_size 32 b

/-- An all-zero-byte payload.  Its purpose is to refute vacuity of the record,
the length, the projections, and the validity characterization. -/
def zeroPayload : AcceptChannelPayload where
  temporaryChannelId := id32 0
  dustLimitSatoshis := 0
  maxHtlcValueInFlightMsat := 0
  channelReserveSatoshis := 0
  htlcMinimumMsat := 0
  minimumDepth := 0
  toSelfDelay := 0
  maxAcceptedHtlcs := 0
  fundingPubKey := pub33 0
  revocationBasepoint := pub33 0
  paymentBasepoint := pub33 0
  delayedPaymentBasepoint := pub33 0
  htlcBasepoint := pub33 0
  firstPerCommitmentPoint := pub33 0

@[simp] theorem zeroPayload_valid : zeroPayload.Valid := by
  simp [Valid, zeroPayload, id32_valid, pub33_valid]

@[simp] theorem zeroPayload_payloadLength : zeroPayload.payloadLength = 270 := rfl

/-- The zero payload is accepted by the existing decoder-acceptance predicate. -/
theorem zeroPayload_wellFormed :
    wellFormed (.acceptChannel (toAcceptChannel zeroPayload)) := by
  rw [wellFormed_toAcceptChannel_iff]
  exact zeroPayload_valid

end AcceptChannelPayload

/-! ## TLV extension

BOLT 2 appends `accept_channel_tlvs` to the fixed fields.  The existing `Msg`
model does not parse TLVs, so the extension is modelled here as an *additive*
length contribution rather than a new message constructor.  This keeps the
fixed 270-byte theorem exact while making the total payload length faithful.
-/

/-- Optional BOLT 2 `accept_channel_tlvs` records (types 0 and 1).  Values are
kept as opaque bytes: this lane proves lengths, not `shutdown_scriptpubkey`
validity or `channel_type` feature bits. -/
structure AcceptChannelTLVs where
  /-- TLV type 0 `upfront_shutdown_script`: `...*byte shutdown_scriptpubkey`. -/
  upfrontShutdownScript : Option ByteArray := none
  /-- TLV type 1 `channel_type`: `...*byte type`. -/
  channelType : Option ByteArray := none
deriving Repr, BEq

/-- Exact encoded size of one TLV record: BigSize(type) + BigSize(length) +
value.  BOLT 1 §"Type-Length-Value Format". -/
def tlvEntryLength (typ : Nat) (value : ByteArray) : Nat :=
  (LnLean.Wire.encode typ).size +
  (LnLean.Wire.encode value.size).size + value.size

/-- A TLV record with both its type and value below `0xfd` occupies
`2 + value.size` bytes.  Both BOLT 2 `accept_channel` TLV types are `0` and
`1`, so the type is always one byte. -/
theorem tlvEntryLength_eq_two_add (typ : Nat) (value : ByteArray)
    (ht : typ < 0xfd) (hv : value.size < 0xfd) :
    tlvEntryLength typ value = 2 + value.size := by
  simp [tlvEntryLength, LnLean.Wire.encode_size_lt_0xfd typ ht,
    LnLean.Wire.encode_size_lt_0xfd value.size hv]

/-- Any canonical TLV record is at most `18 + value.size` bytes. -/
theorem tlvEntryLength_le (typ : Nat) (value : ByteArray) :
    tlvEntryLength typ value ≤ 18 + value.size := by
  unfold tlvEntryLength
  have h1 := LnLean.Wire.encode_size_le_nine typ
  have h2 := LnLean.Wire.encode_size_le_nine value.size
  omega

/-- Length contribution of an optional TLV record. -/
def optionalTLVLength (typ : Nat) : Option ByteArray → Nat
  | none => 0
  | some value => tlvEntryLength typ value

@[simp] theorem optionalTLVLength_none (typ : Nat) :
    optionalTLVLength typ none = 0 := rfl

@[simp] theorem optionalTLVLength_some (typ : Nat) (value : ByteArray) :
    optionalTLVLength typ (some value) = tlvEntryLength typ value := rfl

/-- Total TLV stream length contribution. -/
def tlvBytes (t : AcceptChannelTLVs) : Nat :=
  optionalTLVLength 0 t.upfrontShutdownScript +
  optionalTLVLength 1 t.channelType

@[simp] theorem tlvBytes_empty : tlvBytes {} = 0 := rfl

/-- An empty TLV stream contributes at most 36 bytes of encoding overhead on
top of the two value lengths. -/
theorem tlvBytes_le (t : AcceptChannelTLVs) :
    tlvBytes t ≤ 36 +
      (match t.upfrontShutdownScript with | none => 0 | some v => v.size) +
      (match t.channelType with | none => 0 | some v => v.size) := by
  have h0 : optionalTLVLength 0 t.upfrontShutdownScript ≤
      18 + (match t.upfrontShutdownScript with | none => 0 | some v => v.size) := by
    cases t.upfrontShutdownScript with
    | none => simp
    | some v => simpa using tlvEntryLength_le 0 v
  have h1 : optionalTLVLength 1 t.channelType ≤
      18 + (match t.channelType with | none => 0 | some v => v.size) := by
    cases t.channelType with
    | none => simp
    | some v => simpa using tlvEntryLength_le 1 v
  unfold tlvBytes
  omega

/-- Total `accept_channel` payload length including the optional TLV stream:
the fixed 270 bytes plus the TLV contribution.  The two parts are disjoint and
additive. -/
def payloadLengthWithTLVs (_p : AcceptChannelPayload) (t : AcceptChannelTLVs) : Nat :=
  AcceptChannelPayload.mandatoryPayloadLength + tlvBytes t

/-- Exact decomposition of the full payload length. -/
theorem payloadLengthWithTLVs_eq (p : AcceptChannelPayload)
    (t : AcceptChannelTLVs) :
    payloadLengthWithTLVs p t = 270 + tlvBytes t := rfl

/-- With no TLVs the full length is exactly the fixed 270 bytes. -/
@[simp] theorem payloadLengthWithTLVs_empty (p : AcceptChannelPayload) :
    payloadLengthWithTLVs p {} = 270 := rfl

/-- TLVs only add bytes; the fixed payload is a lower bound. -/
theorem payloadLength_le_withTLVs (p : AcceptChannelPayload)
    (t : AcceptChannelTLVs) :
    p.payloadLength ≤ payloadLengthWithTLVs p t :=
  Nat.le_add_right _ _

/-- The full payload fits BOLT 1's 65535-byte frame whenever the two TLV
values together are at most 65229 bytes (each record then adds its value size
plus at most 18 bytes of BigSize overhead). -/
theorem payloadLengthWithTLVs_le_65535 (p : AcceptChannelPayload)
    (t : AcceptChannelTLVs)
    (hsize :
      (match t.upfrontShutdownScript with | none => 0 | some v => v.size) +
      (match t.channelType with | none => 0 | some v => v.size) ≤ 65229) :
    payloadLengthWithTLVs p t ≤ 65535 := by
  have hb := tlvBytes_le t
  rw [payloadLengthWithTLVs_eq]
  omega

/-! ## Handshake funding-key boundary -/

namespace AcceptChannelPayload

/-- The remote funding key of the existing accept-only negotiation is exactly
the payload's `funding_pubkey`. -/
@[simp] theorem toFundingNegotiation_remoteFundingKey
    (p : AcceptChannelPayload) (localFundingKey : PubKey)
    (fundingSatoshis : BtcAmount) (pushMsat : Msat)
    (temporaryChannelId : TemporaryChannelId) :
    ((toAcceptChannel p).toFundingNegotiation localFundingKey fundingSatoshis
      pushMsat temporaryChannelId).remoteFundingKey = p.fundingPubKey := rfl

/-- The local funding key is the opener's explicit key, unchanged. -/
@[simp] theorem toFundingNegotiation_localFundingKey
    (p : AcceptChannelPayload) (localFundingKey : PubKey)
    (fundingSatoshis : BtcAmount) (pushMsat : Msat)
    (temporaryChannelId : TemporaryChannelId) :
    ((toAcceptChannel p).toFundingNegotiation localFundingKey fundingSatoshis
      pushMsat temporaryChannelId).localFundingKey = localFundingKey := rfl

/-- The funding parameters derived from the payload carry exactly the
payload's funding key as the remote key. -/
@[simp] theorem toFundingParams_remoteFundingKey
    (p : AcceptChannelPayload) (H : ByteArray → ByteArray)
    (localFundingKey : PubKey) (fundingSatoshis : BtcAmount) (pushMsat : Msat)
    (temporaryChannelId : TemporaryChannelId) :
    ((toAcceptChannel p).toFundingParams H localFundingKey fundingSatoshis
      pushMsat temporaryChannelId).remoteFundingKey = p.fundingPubKey := rfl

/-- At the v1 handshake boundary, `funding_created` can only be sent after
`accept_channel` has been received, and the payload's funding key is the remote
key of the derived funding parameters.  This is the exact point where a stored
`AcceptChannelPayload` becomes available to the funding construction; it is
*not* a proof that the key belongs to the peer. -/
theorem fundingKey_bound_before_fundingCreated {s s' : HandshakeState}
    (h : handshakeStep s .sendFundingCreated = some s')
    (p : AcceptChannelPayload) (H : ByteArray → ByteArray)
    (localFundingKey : PubKey) (fundingSatoshis : BtcAmount) (pushMsat : Msat)
    (temporaryChannelId : TemporaryChannelId) :
    s.acceptReceived = true ∧
      ((toAcceptChannel p).toFundingParams H localFundingKey fundingSatoshis
        pushMsat temporaryChannelId).remoteFundingKey = p.fundingPubKey :=
  ⟨acceptReceived_of_sendFundingCreated h, rfl⟩

end AcceptChannelPayload

end LnLean.Proofs.WaveH.H19
