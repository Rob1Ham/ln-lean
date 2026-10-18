import LnLean.Protocol.Handshake
import LnLean.Proofs.Bitcoin.FundingAuthTargets

/-!
# Wave 8, lane H15 — the type-32 `open_channel` projection (`L1-03`)

**English claim.**  BOLT 2 `open_channel` (wire type 32) carries the opener's
funding-side fields.  The v1 handshake model in `LnLean.Protocol.Handshake`
represents exactly the funding-relevant part of that message as
`Protocol.Handshake.OpenChannel` (`temporary_channel_id`, `funding_satoshis`,
`push_msat`, `funding_pubkey`).  This module defines the **wire-complete**
type-32 record `OpenChannelMsg` and the projection

`OpenChannelMsg.toOpenChannel : OpenChannelMsg → Protocol.Handshake.OpenChannel`

and proves that the projection:

1. agrees field-by-field on the four funding fields;
2. determines `Protocol.Handshake.OpenChannel` completely, and loses no
   funding information (it is surjective onto the four funding fields);
3. preserves the funding negotiation, definitionally equal to the existing
   accept-only construction;
4. preserves the funding hash link `witnessScriptHash = H witnessScript.bytes`
   and the P2WSH output law;
5. keeps both advertised funding keys literally in the constructed witness
   script (via `FundingAuthTargets`).

## Why the record is local

Lane H13 (the additive `OpenChannelMsg` module with the fixed payload length)
is not present in this worktree at base `50d78ed`, so this module keeps its own
type-32 record.  If H13 lands, replace the local structure with an import and
re-point `toOpenChannel`; every statement below is about the four funding
fields and remains valid.

The record contains the eighteen fixed BOLT 2 fields:

`chain_hash`, `temporary_channel_id`, `funding_satoshis`, `push_msat`,
`dust_limit_satoshis`, `max_htlc_value_in_flight_msat`,
`channel_reserve_satoshis`, `htlc_minimum_msat`, `feerate_per_kw`,
`to_self_delay`, `max_accepted_htlcs`, `funding_pubkey`,
`revocation_basepoint`, `payment_basepoint`, `delayed_payment_basepoint`,
`htlc_basepoint`, `first_per_commitment_point`, `channel_flags`.

Optional `open_channel_tlvs` (`upfront_shutdown_script`, `channel_type`) are
not part of the fixed payload and are outside this record, matching the
`Messages.lean` policy of not parsing TLV streams.

## BOLT sections

* BOLT 2 §"The `open_channel` Message"
  (`refs/bolts/02-peer-protocol.md:680-740`): the type-32 field list and the
  `open_channel_tlvs` stream.
* BOLT 2 §"Channel Establishment v1"
  (`refs/bolts/02-peer-protocol.md:629-680`): the funding fields are fixed by
  `open_channel` and `accept_channel`.
* BOLT 3 §"Funding Transaction Output": P2WSH over
  `2 <pubkey1> <pubkey2> 2 OP_CHECKMULTISIG` with lexicographically ordered
  keys.

## What is not claimed

* No wire decoder/encoder is defined here (H14/H18 own that).
* No `Msg`/`MsgKind` constructor is added; `LnLean.Protocol.Messages` is a
  shared file and is untouched.  The exact integration patch is in the lane
  report.
* No sender identity or signature is attached.  Transport attribution remains
  the explicit hypothesis of `FundingAuthTargets`.
-/

namespace LnLean.Proofs.WaveH.H15

set_option autoImplicit false

open LnLean
open LnLean.Bitcoin
open LnLean.Protocol
open LnLean.Proofs.Bitcoin.FundingAuthTargets
open LnLean.Proofs.Bitcoin.FundingScriptTargets

/-! ## The wire-complete type-32 record -/

/-- BOLT 2 `open_channel` (wire type 32), fixed payload fields only.  Optional
TLV fields are excluded, as in `LnLean.Protocol.Messages`. -/
structure OpenChannelMsg where
  /-- `chain_hash`: the genesis hash of the chain the channel lives on. -/
  chainHash : ChainHash
  /-- `temporary_channel_id`. -/
  temporaryChannelId : ChannelId
  /-- `funding_satoshis`, the L1 output value. -/
  fundingSatoshis : BtcAmount
  /-- `push_msat`, the opener's initial gift. -/
  pushMsat : Msat
  /-- `dust_limit_satoshis`. -/
  dustLimitSatoshis : Nat
  /-- `max_htlc_value_in_flight_msat`. -/
  maxHtlcValueInFlightMsat : Nat
  /-- `channel_reserve_satoshis`. -/
  channelReserveSatoshis : Nat
  /-- `htlc_minimum_msat`. -/
  htlcMinimumMsat : Nat
  /-- `feerate_per_kw`. -/
  feeratePerKw : Nat
  /-- `to_self_delay` (u16 on the wire). -/
  toSelfDelay : Nat
  /-- `max_accepted_htlcs` (u16 on the wire). -/
  maxAcceptedHtlcs : Nat
  /-- `funding_pubkey`, the opener's funding key. -/
  fundingPubKey : PubKey
  /-- `revocation_basepoint`. -/
  revocationBasepoint : PubKey
  /-- `payment_basepoint`. -/
  paymentBasepoint : PubKey
  /-- `delayed_payment_basepoint`. -/
  delayedPaymentBasepoint : PubKey
  /-- `htlc_basepoint`. -/
  htlcBasepoint : PubKey
  /-- `first_per_commitment_point`. -/
  firstPerCommitmentPoint : PubKey
  /-- `channel_flags` (one byte on the wire). -/
  channelFlags : Nat
deriving Repr, BEq

namespace OpenChannelMsg

/-- BOLT 2 wire type of the message. -/
def wireType : Nat := 32

/-- The record is the type-32 `open_channel` message. -/
theorem wireType_eq : wireType = 32 := rfl

/-- Fixed payload width in bytes: `32 + 32 + 6*8 + 4 + 2 + 2 + 6*33 + 1`. -/
def fixedPayloadWidth : Nat :=
  32 + 32 + 8 + 8 + 8 + 8 + 8 + 8 + 4 + 2 + 2 + 6 * 33 + 1

/-- BOLT 2's fixed `open_channel` payload is 319 bytes.  (The `313` figure in
the wave-8 task table is not the BOLT 2 value; the field list above sums to
319.) -/
theorem fixedPayloadWidth_eq : fixedPayloadWidth = 319 := by decide

/-- **The projection to the existing handshake type.**  Only the four
funding-relevant fields are kept; every other wire field is deliberately
dropped because it does not enter the funding output. -/
def toOpenChannel (m : OpenChannelMsg) : LnLean.Protocol.OpenChannel :=
  { temporaryChannelId := m.temporaryChannelId
    fundingSatoshis := m.fundingSatoshis
    pushMsat := m.pushMsat
    fundingPubKey := m.fundingPubKey }

/-- The projection written out as an explicit record. -/
theorem toOpenChannel_eq (m : OpenChannelMsg) :
    m.toOpenChannel =
      { temporaryChannelId := m.temporaryChannelId
        fundingSatoshis := m.fundingSatoshis
        pushMsat := m.pushMsat
        fundingPubKey := m.fundingPubKey } := rfl

/-! ## Field-by-field agreement -/

@[simp] theorem toOpenChannel_temporaryChannelId (m : OpenChannelMsg) :
    m.toOpenChannel.temporaryChannelId = m.temporaryChannelId := rfl

@[simp] theorem toOpenChannel_fundingSatoshis (m : OpenChannelMsg) :
    m.toOpenChannel.fundingSatoshis = m.fundingSatoshis := rfl

@[simp] theorem toOpenChannel_pushMsat (m : OpenChannelMsg) :
    m.toOpenChannel.pushMsat = m.pushMsat := rfl

@[simp] theorem toOpenChannel_fundingPubKey (m : OpenChannelMsg) :
    m.toOpenChannel.fundingPubKey = m.fundingPubKey := rfl

/-- The four projected fields are exactly the four `open_channel` fields, so
the wire record determines the handshake record. -/
theorem toOpenChannel_ext {m₁ m₂ : OpenChannelMsg}
    (hid : m₁.temporaryChannelId = m₂.temporaryChannelId)
    (hsat : m₁.fundingSatoshis = m₂.fundingSatoshis)
    (hpush : m₁.pushMsat = m₂.pushMsat)
    (hkey : m₁.fundingPubKey = m₂.fundingPubKey) :
    m₁.toOpenChannel = m₂.toOpenChannel := by
  cases m₁
  cases m₂
  simp_all [toOpenChannel]

/-- Conversely, equal projections force agreement on all four funding fields:
the projection is injective on exactly the information it keeps. -/
theorem fields_eq_of_toOpenChannel_eq {m₁ m₂ : OpenChannelMsg}
    (h : m₁.toOpenChannel = m₂.toOpenChannel) :
    m₁.temporaryChannelId = m₂.temporaryChannelId ∧
      m₁.fundingSatoshis = m₂.fundingSatoshis ∧
      m₁.pushMsat = m₂.pushMsat ∧
      m₁.fundingPubKey = m₂.fundingPubKey :=
  ⟨congrArg (fun o : LnLean.Protocol.OpenChannel => o.temporaryChannelId) h,
    congrArg (fun o : LnLean.Protocol.OpenChannel => o.fundingSatoshis) h,
    congrArg (fun o : LnLean.Protocol.OpenChannel => o.pushMsat) h,
    congrArg (fun o : LnLean.Protocol.OpenChannel => o.fundingPubKey) h⟩

/-- No funding information is lost: every handshake `OpenChannel` is the
projection of some type-32 record.  The non-funding fields are filled with
canonical empty/zero values. -/
theorem toOpenChannel_surjective (o : LnLean.Protocol.OpenChannel) :
    ∃ m : OpenChannelMsg, m.toOpenChannel = o := by
  refine ⟨{ chainHash := ⟨ByteArray.empty⟩
            temporaryChannelId := o.temporaryChannelId
            fundingSatoshis := o.fundingSatoshis
            pushMsat := o.pushMsat
            dustLimitSatoshis := 0
            maxHtlcValueInFlightMsat := 0
            channelReserveSatoshis := 0
            htlcMinimumMsat := 0
            feeratePerKw := 0
            toSelfDelay := 0
            maxAcceptedHtlcs := 0
            fundingPubKey := o.fundingPubKey
            revocationBasepoint := ⟨ByteArray.empty⟩
            paymentBasepoint := ⟨ByteArray.empty⟩
            delayedPaymentBasepoint := ⟨ByteArray.empty⟩
            htlcBasepoint := ⟨ByteArray.empty⟩
            firstPerCommitmentPoint := ⟨ByteArray.empty⟩
            channelFlags := 0 }, rfl⟩

/-! ## The projection preserves the funding negotiation -/

/-- The joint negotiation computed from the wire message is definitionally the
existing accept-only negotiation with the opener's fields supplied from the
type-32 record.  No hash or key is recomputed. -/
theorem toFundingNegotiation_eq (m : OpenChannelMsg) (a : AcceptChannel) :
    m.toOpenChannel.toFundingNegotiation a =
      a.toFundingNegotiation m.fundingPubKey m.fundingSatoshis m.pushMsat
        ⟨m.temporaryChannelId⟩ := rfl

/-- The same statement referred to the existing `Handshake` theorem, making
the reuse explicit. -/
theorem toFundingNegotiation_eq_acceptOnly (m : OpenChannelMsg)
    (a : AcceptChannel) :
    m.toOpenChannel.toFundingNegotiation a =
      a.toFundingNegotiation m.fundingPubKey m.fundingSatoshis m.pushMsat
        ⟨m.temporaryChannelId⟩ :=
  LnLean.Protocol.OpenChannel.toFundingNegotiation_eq_acceptChannel _ a

@[simp] theorem toFundingNegotiation_localFundingKey (m : OpenChannelMsg)
    (a : AcceptChannel) :
    (m.toOpenChannel.toFundingNegotiation a).localFundingKey =
      m.fundingPubKey := rfl

@[simp] theorem toFundingNegotiation_remoteFundingKey (m : OpenChannelMsg)
    (a : AcceptChannel) :
    (m.toOpenChannel.toFundingNegotiation a).remoteFundingKey =
      a.fundingPubKey := rfl

@[simp] theorem toFundingNegotiation_fundingSatoshis (m : OpenChannelMsg)
    (a : AcceptChannel) :
    (m.toOpenChannel.toFundingNegotiation a).fundingSatoshis =
      m.fundingSatoshis := rfl

@[simp] theorem toFundingNegotiation_pushMsat (m : OpenChannelMsg)
    (a : AcceptChannel) :
    (m.toOpenChannel.toFundingNegotiation a).pushMsat = m.pushMsat := rfl

@[simp] theorem toFundingNegotiation_temporaryChannelId (m : OpenChannelMsg)
    (a : AcceptChannel) :
    (m.toOpenChannel.toFundingNegotiation a).temporaryChannelId =
      ⟨m.temporaryChannelId⟩ := rfl

/-- The funding parameters computed from the wire message are the existing
handshake construction with the opener's fields taken from the record. -/
theorem toFundingParams_eq (H : ByteArray → ByteArray) (m : OpenChannelMsg)
    (a : AcceptChannel) :
    m.toOpenChannel.toFundingParams H a =
      a.toFundingParams H m.fundingPubKey m.fundingSatoshis m.pushMsat
        ⟨m.temporaryChannelId⟩ := rfl

/-! ## The projection preserves the hash link and output law -/

/-- The P2WSH program is computed as `H` of the BOLT 3 witness script; the
projection does not introduce a separate hash argument. -/
theorem toFundingParams_witnessScriptHash (H : ByteArray → ByteArray)
    (m : OpenChannelMsg) (a : AcceptChannel) :
    (m.toOpenChannel.toFundingParams H a).witnessScriptHash =
      H (m.toOpenChannel.toFundingParams H a).witnessScript.bytes :=
  LnLean.Protocol.OpenChannel.toFundingParams_witnessScriptHash H _ a

/-- The funding-script hash link holds for the projection by construction. -/
theorem toFundingParams_hashLinked (H : ByteArray → ByteArray)
    (m : OpenChannelMsg) (a : AcceptChannel) :
    FundingScriptHashLinked H (m.toOpenChannel.toFundingParams H a) :=
  LnLean.Bitcoin.FundingNegotiation.toFundingParams_witnessScriptHash H _

/-- The funding output is the P2WSH wrapper over the computed program. -/
theorem toFundingParams_fundingScriptPubKey (H : ByteArray → ByteArray)
    (m : OpenChannelMsg) (a : AcceptChannel) :
    (m.toOpenChannel.toFundingParams H a).fundingScriptPubKey =
      p2wsh (H (m.toOpenChannel.toFundingParams H a).witnessScript.bytes) :=
  LnLean.Protocol.OpenChannel.toFundingParams_fundingScriptPubKey H _ a

/-- Both advertised funding keys occur literally in the witness script, so the
projection keeps the key commitment established for the handshake type. -/
theorem toFundingParams_keys_in_script (H : ByteArray → ByteArray)
    (m : OpenChannelMsg) (a : AcceptChannel) :
    KeyInScript (m.toOpenChannel.toFundingParams H a).witnessScript.bytes
        m.fundingPubKey ∧
      KeyInScript (m.toOpenChannel.toFundingParams H a).witnessScript.bytes
        a.fundingPubKey :=
  openAccept_both_keys_in_script H _ a

/-! ## Non-vacuity -/

private def zeros32 : ByteArray :=
  ByteArray.mk (List.replicate 32 (0 : UInt8)).toArray

private def key33 (b : UInt8) : ByteArray :=
  ByteArray.mk (List.replicate 33 b).toArray

private def pub33 (b : UInt8) : PubKey := ⟨key33 b⟩

private def demoAccept : AcceptChannel :=
  { temporaryChannelId := ⟨zeros32⟩
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
    firstPerCommitmentPoint := pub33 0 }

/-- A concrete type-32 record. -/
private def demoMsg : OpenChannelMsg :=
  { chainHash := ⟨zeros32⟩
    temporaryChannelId := ⟨zeros32⟩
    fundingSatoshis := 0
    pushMsat := ⟨0⟩
    dustLimitSatoshis := 0
    maxHtlcValueInFlightMsat := 0
    channelReserveSatoshis := 0
    htlcMinimumMsat := 0
    feeratePerKw := 0
    toSelfDelay := 0
    maxAcceptedHtlcs := 0
    fundingPubKey := pub33 0
    revocationBasepoint := pub33 0
    paymentBasepoint := pub33 0
    delayedPaymentBasepoint := pub33 0
    htlcBasepoint := pub33 0
    firstPerCommitmentPoint := pub33 0
    channelFlags := 0 }

/-- The concrete projection is the expected four-field record. -/
theorem demoMsg_projection :
    demoMsg.toOpenChannel =
      { temporaryChannelId := ⟨zeros32⟩
        fundingSatoshis := 0
        pushMsat := ⟨0⟩
        fundingPubKey := pub33 0 } := rfl

/-- The projection is non-vacuous and the funding hash link holds on a
concrete message/accept pair. -/
theorem demoMsg_hashLinked :
    FundingScriptHashLinked (fun _ => zeros32)
      (demoMsg.toOpenChannel.toFundingParams (fun _ => zeros32) demoAccept) :=
  toFundingParams_hashLinked _ _ _

end OpenChannelMsg

/-! ## Axiom audit -/

#print axioms OpenChannelMsg.toOpenChannel_temporaryChannelId
#print axioms OpenChannelMsg.toOpenChannel_fundingSatoshis
#print axioms OpenChannelMsg.toOpenChannel_pushMsat
#print axioms OpenChannelMsg.toOpenChannel_fundingPubKey
#print axioms OpenChannelMsg.toOpenChannel_ext
#print axioms OpenChannelMsg.fields_eq_of_toOpenChannel_eq
#print axioms OpenChannelMsg.toOpenChannel_surjective
#print axioms OpenChannelMsg.toFundingNegotiation_eq
#print axioms OpenChannelMsg.toFundingNegotiation_eq_acceptOnly
#print axioms OpenChannelMsg.toFundingParams_eq
#print axioms OpenChannelMsg.toFundingParams_witnessScriptHash
#print axioms OpenChannelMsg.toFundingParams_hashLinked
#print axioms OpenChannelMsg.toFundingParams_fundingScriptPubKey
#print axioms OpenChannelMsg.toFundingParams_keys_in_script
#print axioms OpenChannelMsg.demoMsg_projection
#print axioms OpenChannelMsg.demoMsg_hashLinked

end LnLean.Proofs.WaveH.H15
