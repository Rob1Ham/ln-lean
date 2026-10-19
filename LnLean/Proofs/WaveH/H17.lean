/-
# Wave 8 H17 — `open_channel` (type 32) registration facts (L1-03)

**English claim.**  BOLT 2 channel establishment starts with the funder's
`open_channel` message, whose wire type is 32.  `LnLean.Protocol.Messages`
currently models the other seventeen BOLT 1/2 messages but has no type-32
constructor, so type 32 is not registered there.  This module defines an
**additive local** `OpenChannelMsg` record and proves the registration facts a
`Messages.lean` integration needs:

1. the wire type is exactly `32` and the type table is injective, so 32 is
   unique among the modelled message kinds;
2. decoding the type table returns the `openChannel` kind
   (`kindOfType? (wireType k) = some k`), and `kindOfType? 32 = some .openChannel`;
3. the mandatory BOLT 2 v1 payload is `319` bytes, and the optional
   `shutdown_scriptpubkey` TLV adds at most `1 + 9 + |script|` bytes, which
   gives the BOLT 1 framing bound under an explicit script-size hypothesis;
4. a `wellFormed` message exposes its channel id, all six public keys, the
   `chain_hash` width, and the fixed-width `u32`/`u16` field domains;
5. a concrete non-vacuous witness satisfies `wellFormed`.

The record is local and importable.  `LnLean/Protocol/Messages.lean` is
**not** edited by this lane; the exact integration patch is in
`agents/reports/wave8/H17.md`.

## BOLT sections

* BOLT 2 §"The `open_channel` Message" (`refs/bolts/02-peer-protocol.md:680-760`):
  type 32 and the field list.
* BOLT 1 §"Lightning Message Format" (`refs/bolts/01-messaging.md:43-92`):
  the type space and the 65535-byte payload bound.
* BOLT 1 §Appendix A: canonical BigSize encoding, used for the optional TLV.

## rust-lightning anchors (commit fe49009)

* `lightning/src/ln/msgs.rs:289` `OpenChannel`; `:191`
  `CommonOpenChannelFields`; `:3295` `impl Writeable for OpenChannel`.
* `lightning/src/ln/wire.rs` type constants (`open_channel = 32`).

## What is NOT modelled

* `channel_type` and other non-shutdown TLVs are not modelled; their bytes are
  not counted.  `shutdown_scriptpubkey` is represented by `Option ByteArray`
  and its TLV overhead is counted.
* `funding_satoshis` is the vendor `BtcAmount` (`Int`) to match the existing
  handshake projection; no `MoneyRange` check is made here.
* `channel_flags` is a `UInt8`; no flag semantics (`announce_channel`) are
  asserted.
* No signature is carried by `open_channel`; `signatures` is empty and
  `sigsValid` is vacuous.
* Wire serialization is a length model, not a byte encoder.
-/

import LnLean.Protocol.Messages
import LnLean.Wire.BigSize

namespace LnLean.Proofs.WaveH.H17

set_option autoImplicit false

open LnLean
open LnLean.Protocol

/-! ## 1. The local type-32 wire record -/

/-- BOLT 2 `open_channel` (type 32), wire-relevant fields.  `chain_hash` and
`channel_reserve_satoshis` are included: the wave-7 patch sketch omitted both
(40 bytes) and summed the shutdown TLV without its two-byte header.
`shutdown_scriptpubkey` is the optional `open_channel_tlvs` type-0 entry. -/
structure OpenChannelMsg where
  /-- BOLT 2 `chain_hash` (32 bytes). -/
  chainHash : ByteArray
  /-- BOLT 2 `temporary_channel_id` (32 bytes). -/
  temporaryChannelId : ChannelId
  /-- BOLT 2 `funding_satoshis` (`u64`). -/
  fundingSatoshis : LnLean.Bitcoin.BtcAmount
  /-- BOLT 2 `push_msat` (`u64`). -/
  pushMsat : Msat
  /-- BOLT 2 `dust_limit_satoshis` (`u64`). -/
  dustLimitSatoshis : Nat
  /-- BOLT 2 `max_htlc_value_in_flight_msat` (`u64`). -/
  maxHtlcValueInFlightMsat : Nat
  /-- BOLT 2 `channel_reserve_satoshis` (`u64`). -/
  channelReserveSatoshis : Nat
  /-- BOLT 2 `htlc_minimum_msat` (`u64`). -/
  htlcMinimumMsat : Nat
  /-- BOLT 2 `feerate_per_kw` (`u32`). -/
  feeratePerKw : Nat
  /-- BOLT 2 `to_self_delay` (`u16`). -/
  toSelfDelay : Nat
  /-- BOLT 2 `max_accepted_htlcs` (`u16`). -/
  maxAcceptedHtlcs : Nat
  /-- BOLT 2 `funding_pubkey` (`point`, 33 bytes). -/
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
  /-- BOLT 2 `channel_flags` (`u8`). -/
  channelFlags : UInt8
  /-- Optional `open_channel_tlvs` type 0 (`upfront_shutdown_script`). -/
  shutdownScriptpubkey : Option ByteArray := none
deriving Repr, BEq

/-! ## 2. Wire-type table and type uniqueness -/

/-- The modelled message kinds, extended by `openChannel`.  The seventeen
existing constructors and their numeric types are copied from
`LnLean.Protocol.MsgKind`/`wireType`; `openChannel` is the new type 32. -/
inductive Kind where
  | warning
  | init
  | error
  | ping
  | pong
  | openChannel
  | acceptChannel
  | fundingCreated
  | fundingSigned
  | channelReady
  | shutdown
  | closingSigned
  | updateAddHtlc
  | updateFulfillHtlc
  | updateFailHtlc
  | commitmentSigned
  | revokeAndAck
  | channelReestablish
deriving Repr, DecidableEq, BEq, Inhabited

/-- BOLT wire type of a kind, including the new type 32. -/
def wireType : Kind → Nat
  | .warning => 1
  | .init => 16
  | .error => 17
  | .ping => 18
  | .pong => 19
  | .openChannel => 32
  | .acceptChannel => 33
  | .fundingCreated => 34
  | .fundingSigned => 35
  | .channelReady => 36
  | .shutdown => 38
  | .closingSigned => 39
  | .updateAddHtlc => 128
  | .updateFulfillHtlc => 130
  | .updateFailHtlc => 131
  | .commitmentSigned => 132
  | .revokeAndAck => 133
  | .channelReestablish => 136

/-- Decode a wire type to its kind, including type 32. -/
def kindOfType? : Nat → Option Kind
  | 1 => some .warning
  | 16 => some .init
  | 17 => some .error
  | 18 => some .ping
  | 19 => some .pong
  | 32 => some .openChannel
  | 33 => some .acceptChannel
  | 34 => some .fundingCreated
  | 35 => some .fundingSigned
  | 36 => some .channelReady
  | 38 => some .shutdown
  | 39 => some .closingSigned
  | 128 => some .updateAddHtlc
  | 130 => some .updateFulfillHtlc
  | 131 => some .updateFailHtlc
  | 132 => some .commitmentSigned
  | 133 => some .revokeAndAck
  | 136 => some .channelReestablish
  | _ => none

/-- The local kind of the type-32 record. -/
def OpenChannelMsg.kind (_ : OpenChannelMsg) : Kind := .openChannel

/-- The wire type of the local record. -/
def OpenChannelMsg.wireType (_ : OpenChannelMsg) : Nat := 32

/-- The local record's BOLT type is 32. -/
@[simp] theorem OpenChannelMsg.wireType_eq_32 (m : OpenChannelMsg) :
    m.wireType = 32 := rfl

/-- The local record's kind is `openChannel`. -/
@[simp] theorem OpenChannelMsg.kind_eq (m : OpenChannelMsg) :
    m.kind = Kind.openChannel := rfl

/-- The local kind `openChannel` is the only one absent from the existing
`Messages.MsgKind`; the other seventeen map back to their original tags. -/
def Kind.toMsgKind? : Kind → Option LnLean.Protocol.MsgKind
  | .warning => some .warning
  | .init => some .init
  | .error => some .error
  | .ping => some .ping
  | .pong => some .pong
  | .openChannel => none
  | .acceptChannel => some .acceptChannel
  | .fundingCreated => some .fundingCreated
  | .fundingSigned => some .fundingSigned
  | .channelReady => some .channelReady
  | .shutdown => some .shutdown
  | .closingSigned => some .closingSigned
  | .updateAddHtlc => some .updateAddHtlc
  | .updateFulfillHtlc => some .updateFulfillHtlc
  | .updateFailHtlc => some .updateFailHtlc
  | .commitmentSigned => some .commitmentSigned
  | .revokeAndAck => some .revokeAndAck
  | .channelReestablish => some .channelReestablish

/-- On every pre-existing constructor the local table has exactly the
`Messages.wireType` value.  This ties the local uniqueness proof to the shared
table instead of leaving it as an unconnected copy. -/
theorem wireType_eq_messages {k : Kind} {j : LnLean.Protocol.MsgKind}
    (h : k.toMsgKind? = some j) : wireType k = LnLean.Protocol.wireType j := by
  cases k <;> simp [Kind.toMsgKind?, wireType, LnLean.Protocol.wireType] at h ⊢
  all_goals (subst h; rfl)

/-- The wire-type table and the existing `Messages` table agree on all
seventeen shared kinds. -/
theorem wireType_shared (k : Kind) (h : k ≠ .openChannel) :
    ∃ j : LnLean.Protocol.MsgKind,
      k.toMsgKind? = some j ∧ wireType k = LnLean.Protocol.wireType j := by
  cases k <;> simp_all [Kind.toMsgKind?, wireType, LnLean.Protocol.wireType]
  all_goals exact ⟨_, rfl, rfl⟩

/-- Type 32 is the `openChannel` kind. -/
@[simp] theorem wireType_openChannel : wireType .openChannel = 32 := rfl


/-- The type table is injective on the local kind space, so each kind has
exactly one wire type. -/
theorem wireType_injective : Function.Injective wireType := by
  intro a b h
  cases a <;> cases b <;> simp [wireType] at h ⊢ <;> omega

/-- **Type uniqueness.**  A kind has wire type 32 exactly when it is
`openChannel`; no other modelled message is type 32. -/
theorem wireType_eq_32_iff (k : Kind) :
    wireType k = 32 ↔ k = .openChannel := by
  cases k <;> simp [wireType] <;> omega

/-- Every modelled type is a nonzero 16-bit value. -/
theorem wireType_lt_65536 (k : Kind) : wireType k < 65536 := by
  cases k <;> simp [wireType] <;> omega

theorem wireType_ne_zero (k : Kind) : wireType k ≠ 0 := by
  cases k <;> simp [wireType]

/-- Decoding a kind's wire type returns that kind: each message has exactly
one registration entry. -/
@[simp] theorem kindOfType?_wireType (k : Kind) :
    kindOfType? (wireType k) = some k := by
  cases k <;> rfl

/-- Type 32 decodes to the `openChannel` kind. -/
@[simp] theorem kindOfType?_32 : kindOfType? 32 = some .openChannel := rfl

/-- The registration is a function: at most one kind decodes from a type. -/
theorem kindOfType?_unique {t : Nat} {k₁ k₂ : Kind}
    (h₁ : kindOfType? t = some k₁) (h₂ : kindOfType? t = some k₂) :
    k₁ = k₂ := by
  rw [h₁] at h₂
  exact Option.some.inj h₂

/-! ## 3. Payload length -/

/-- The mandatory BOLT 2 v1 `open_channel` payload:
`chain_hash` 32 + `temporary_channel_id` 32 + six `u64` fields 48 +
`feerate_per_kw` 4 + two `u16` fields 4 + six points 198 + `channel_flags` 1
= 319 bytes.  Optional TLVs are additional. -/
def basePayloadLength : Nat := 319

/-- The field-sum arithmetic behind `319`. -/
theorem basePayloadLength_eq :
    32 + 32 + 6 * 8 + 4 + 2 + 2 + 6 * 33 + 1 = basePayloadLength := by
  unfold basePayloadLength
  decide

/-- The mandatory length as a literal. -/
theorem basePayloadLength_eq_319 : basePayloadLength = 319 := rfl

/-- Length of one TLV record with a one-byte type, a canonical BigSize length,
and the value.  The only TLV modelled here is type 0, whose type byte is 1. -/
def tlvEntryLength (valueLength : Nat) : Nat :=
  1 + (LnLean.Wire.encode valueLength).size + valueLength

/-- Payload length: the mandatory fields plus the optional shutdown TLV. -/
def msgLength (m : OpenChannelMsg) : Nat :=
  basePayloadLength +
    match m.shutdownScriptpubkey with
    | none => 0
    | some s => tlvEntryLength s.size

/-- Without a shutdown script the payload is exactly 319 bytes. -/
theorem msgLength_none (m : OpenChannelMsg)
    (h : m.shutdownScriptpubkey = none) : msgLength m = 319 := by
  simp [msgLength, basePayloadLength, h]

/-- With a shutdown script the payload is the mandatory length plus the TLV
record (type byte, BigSize length, value). -/
theorem msgLength_some (m : OpenChannelMsg) (s : ByteArray)
    (h : m.shutdownScriptpubkey = some s) :
    msgLength m = 319 + 1 + (LnLean.Wire.encode s.size).size + s.size := by
  simp [msgLength, basePayloadLength, tlvEntryLength, h]
  omega

/-- A standard short shutdown script (< 253 bytes) adds exactly two bytes of
TLV overhead plus the script. -/
theorem msgLength_some_short (m : OpenChannelMsg) (s : ByteArray)
    (h : m.shutdownScriptpubkey = some s) (hs : s.size < 0xfd) :
    msgLength m = 321 + s.size := by
  have henc := LnLean.Wire.encode_size_lt_0xfd s.size hs
  simp [msgLength, basePayloadLength, tlvEntryLength, h, henc]
  omega

/-- The standard 34-byte `shutdown_scriptpubkey` TLV gives a 355-byte payload:
319 mandatory + 1 type byte + 1 BigSize length byte + 34 script bytes. -/
theorem msgLength_shutdown_34 (m : OpenChannelMsg) (s : ByteArray)
    (h : m.shutdownScriptpubkey = some s) (hs : s.size = 34) :
    msgLength m = 355 := by
  have hlt : s.size < 0xfd := by omega
  rw [msgLength_some_short m s h hlt, hs]

/-- The mandatory payload alone fits BOLT 1's two-byte framing bound. -/
theorem basePayloadLength_le_65535 : basePayloadLength ≤ 65535 := by
  unfold basePayloadLength
  decide

/-- Without optional TLVs the payload fits the framing bound. -/
theorem msgLength_le_65535_of_no_shutdown (m : OpenChannelMsg)
    (h : m.shutdownScriptpubkey = none) : msgLength m ≤ 65535 := by
  rw [msgLength_none m h]
  exact basePayloadLength_le_65535

/-- **Payload length bound with an optional shutdown script.**  BigSize is at
most nine bytes, so a shutdown script of at most `65206` bytes keeps the
payload within `65535`. -/
theorem msgLength_le_65535_of_shutdown_bound (m : OpenChannelMsg)
    (h : ∀ s, m.shutdownScriptpubkey = some s → s.size ≤ 65206) :
    msgLength m ≤ 65535 := by
  cases hs : m.shutdownScriptpubkey with
  | none =>
      rw [msgLength_none m hs]
      exact basePayloadLength_le_65535
  | some s =>
      have hbound := h s hs
      have henc := LnLean.Wire.encode_size_le_nine s.size
      rw [msgLength_some m s hs]
      omega

/-- Every payload is at least the mandatory length. -/
theorem basePayloadLength_le_msgLength (m : OpenChannelMsg) :
    basePayloadLength ≤ msgLength m := by
  cases hs : m.shutdownScriptpubkey <;> simp [msgLength, hs]

/-- Payload lengths are positive. -/
theorem msgLength_pos (m : OpenChannelMsg) : 0 < msgLength m := by
  have h := basePayloadLength_le_msgLength m
  have hb : 0 < basePayloadLength := by unfold basePayloadLength; decide
  omega

theorem msgLength_ne_zero (m : OpenChannelMsg) : msgLength m ≠ 0 :=
  Nat.ne_of_gt (msgLength_pos m)

/-! ## 4. Channel-id and public-key extraction -/

/-- The channel identifier carried by `open_channel` is its temporary id. -/
def channelId? (m : OpenChannelMsg) : Option ChannelId :=
  some m.temporaryChannelId

/-- `open_channel` carries no signature. -/
def signatures (_ : OpenChannelMsg) : List EcdsaSig := []

/-- All six public keys of `open_channel`, in BOLT 2 field order. -/
def pubKeys (m : OpenChannelMsg) : List PubKey :=
  [m.fundingPubKey, m.revocationBasepoint, m.paymentBasepoint,
   m.delayedPaymentBasepoint, m.htlcBasepoint, m.firstPerCommitmentPoint]

/-- The channel-id projection is the temporary channel id. -/
@[simp] theorem channelId?_eq (m : OpenChannelMsg) :
    channelId? m = some m.temporaryChannelId := rfl

/-- Any extracted channel id is the temporary channel id. -/
theorem channelId?_eq_some_iff (m : OpenChannelMsg) (c : ChannelId) :
    channelId? m = some c ↔ m.temporaryChannelId = c := by
  simp [channelId?]

/-- The extraction is a function of the record, not of the wire bytes. -/
theorem channelId?_unique {m : OpenChannelMsg} {c₁ c₂ : ChannelId}
    (h₁ : channelId? m = some c₁) (h₂ : channelId? m = some c₂) : c₁ = c₂ := by
  rw [channelId?_eq_some_iff] at h₁ h₂
  exact h₁.symm.trans h₂

/-- The public-key projection is the six-key BOLT 2 list. -/
@[simp] theorem pubKeys_eq (m : OpenChannelMsg) :
    pubKeys m =
      [m.fundingPubKey, m.revocationBasepoint, m.paymentBasepoint,
       m.delayedPaymentBasepoint, m.htlcBasepoint, m.firstPerCommitmentPoint] :=
  rfl

/-- The projection has exactly six entries. -/
@[simp] theorem pubKeys_length (m : OpenChannelMsg) : (pubKeys m).length = 6 :=
  rfl

/-- There are no signatures to extract. -/
@[simp] theorem signatures_eq (m : OpenChannelMsg) : signatures m = [] := rfl

theorem fundingPubKey_mem_pubKeys (m : OpenChannelMsg) :
    m.fundingPubKey ∈ pubKeys m := by
  simp [pubKeys]

theorem revocationBasepoint_mem_pubKeys (m : OpenChannelMsg) :
    m.revocationBasepoint ∈ pubKeys m := by
  simp [pubKeys]

theorem paymentBasepoint_mem_pubKeys (m : OpenChannelMsg) :
    m.paymentBasepoint ∈ pubKeys m := by
  simp [pubKeys]

theorem delayedPaymentBasepoint_mem_pubKeys (m : OpenChannelMsg) :
    m.delayedPaymentBasepoint ∈ pubKeys m := by
  simp [pubKeys]

theorem htlcBasepoint_mem_pubKeys (m : OpenChannelMsg) :
    m.htlcBasepoint ∈ pubKeys m := by
  simp [pubKeys]

theorem firstPerCommitmentPoint_mem_pubKeys (m : OpenChannelMsg) :
    m.firstPerCommitmentPoint ∈ pubKeys m := by
  simp [pubKeys]

/-! ## 5. Well-formedness -/

/-- Local decoder acceptance for `open_channel`: the BOLT 1 length bound, the
32-byte `chain_hash`, a valid 32-byte temporary channel id, valid 33-byte
public keys, and the `u32`/`u16` field domains.  Optional TLV bytes are
already included in `msgLength`. -/
def wellFormed (m : OpenChannelMsg) : Prop :=
  msgLength m ≤ 65535 ∧
  m.chainHash.size = 32 ∧
  m.temporaryChannelId.Valid ∧
  (∀ p ∈ pubKeys m, p.Valid) ∧
  m.feeratePerKw < 2 ^ 32 ∧
  m.toSelfDelay < 2 ^ 16 ∧
  m.maxAcceptedHtlcs < 2 ^ 16

/-- A well-formed message fits the BOLT 1 framing bound. -/
theorem wellFormed_length {m : OpenChannelMsg} (h : wellFormed m) :
    msgLength m ≤ 65535 := h.1

/-- A well-formed message has a 32-byte chain hash. -/
theorem wellFormed_chainHash {m : OpenChannelMsg} (h : wellFormed m) :
    m.chainHash.size = 32 := h.2.1

/-- A well-formed message has a valid temporary channel id. -/
theorem wellFormed_channelId {m : OpenChannelMsg} (h : wellFormed m) :
    m.temporaryChannelId.Valid := h.2.2.1

/-- **Channel-id extraction.**  Any channel id extracted from a well-formed
message is valid. -/
theorem wellFormed_channelId?_valid {m : OpenChannelMsg} {c : ChannelId}
    (h : wellFormed m) (hc : channelId? m = some c) : c.Valid := by
  rw [channelId?_eq_some_iff] at hc
  subst hc
  exact h.2.2.1

/-- **Public-key extraction.**  Every extracted public key is valid. -/
theorem wellFormed_pubKey {m : OpenChannelMsg} {p : PubKey}
    (h : wellFormed m) (hp : p ∈ pubKeys m) : p.Valid := h.2.2.2.1 p hp

/-- In particular the funding key is valid. -/
theorem wellFormed_fundingPubKey {m : OpenChannelMsg} (h : wellFormed m) :
    m.fundingPubKey.Valid :=
  wellFormed_pubKey h (fundingPubKey_mem_pubKeys m)

/-- The revocation basepoint is valid. -/
theorem wellFormed_revocationBasepoint {m : OpenChannelMsg} (h : wellFormed m) :
    m.revocationBasepoint.Valid :=
  wellFormed_pubKey h (revocationBasepoint_mem_pubKeys m)

/-- The payment basepoint is valid. -/
theorem wellFormed_paymentBasepoint {m : OpenChannelMsg} (h : wellFormed m) :
    m.paymentBasepoint.Valid :=
  wellFormed_pubKey h (paymentBasepoint_mem_pubKeys m)

/-- The delayed-payment basepoint is valid. -/
theorem wellFormed_delayedPaymentBasepoint {m : OpenChannelMsg}
    (h : wellFormed m) : m.delayedPaymentBasepoint.Valid :=
  wellFormed_pubKey h (delayedPaymentBasepoint_mem_pubKeys m)

/-- The HTLC basepoint is valid. -/
theorem wellFormed_htlcBasepoint {m : OpenChannelMsg} (h : wellFormed m) :
    m.htlcBasepoint.Valid :=
  wellFormed_pubKey h (htlcBasepoint_mem_pubKeys m)

/-- The first per-commitment point is valid. -/
theorem wellFormed_firstPerCommitmentPoint {m : OpenChannelMsg}
    (h : wellFormed m) : m.firstPerCommitmentPoint.Valid :=
  wellFormed_pubKey h (firstPerCommitmentPoint_mem_pubKeys m)

/-- The `u32` feerate domain. -/
theorem wellFormed_feerate {m : OpenChannelMsg} (h : wellFormed m) :
    m.feeratePerKw < 2 ^ 32 := h.2.2.2.2.1

/-- The `u16` `to_self_delay` domain. -/
theorem wellFormed_toSelfDelay {m : OpenChannelMsg} (h : wellFormed m) :
    m.toSelfDelay < 2 ^ 16 := h.2.2.2.2.2.1

/-- The `u16` `max_accepted_htlcs` domain. -/
theorem wellFormed_maxAcceptedHtlcs {m : OpenChannelMsg} (h : wellFormed m) :
    m.maxAcceptedHtlcs < 2 ^ 16 := h.2.2.2.2.2.2

/-- `open_channel` carries no signatures, so the signature-size check is
vacuous. -/
theorem signatures_length (m : OpenChannelMsg) : (signatures m).length = 0 := rfl

/-! ## 6. Non-vacuity -/

/-- A concrete 33-byte compressed-key placeholder. -/
def zeroPubKey : PubKey :=
  ⟨ByteArray.mk (List.replicate 33 (0 : UInt8)).toArray⟩

@[simp] theorem zeroPubKey_valid : zeroPubKey.Valid := rfl

/-- A concrete well-formed type-32 message with no shutdown TLV. -/
def exampleOpenChannel : OpenChannelMsg where
  chainHash := ChannelId.zero.bytes
  temporaryChannelId := ChannelId.zero
  fundingSatoshis := 100000
  pushMsat := Msat.zero
  dustLimitSatoshis := 546
  maxHtlcValueInFlightMsat := 1000000
  channelReserveSatoshis := 1000
  htlcMinimumMsat := 1
  feeratePerKw := 253
  toSelfDelay := 144
  maxAcceptedHtlcs := 483
  fundingPubKey := zeroPubKey
  revocationBasepoint := zeroPubKey
  paymentBasepoint := zeroPubKey
  delayedPaymentBasepoint := zeroPubKey
  htlcBasepoint := zeroPubKey
  firstPerCommitmentPoint := zeroPubKey
  channelFlags := 1
  shutdownScriptpubkey := none

@[simp] theorem exampleOpenChannel_wireType :
    exampleOpenChannel.wireType = 32 := rfl

@[simp] theorem exampleOpenChannel_msgLength : msgLength exampleOpenChannel = 319 := by
  simp [msgLength, basePayloadLength, exampleOpenChannel]

theorem exampleOpenChannel_chainHash : exampleOpenChannel.chainHash.size = 32 := by
  simpa [exampleOpenChannel, ChannelId.Valid] using ChannelId.zero_valid

theorem exampleOpenChannel_channelId : exampleOpenChannel.temporaryChannelId.Valid := by
  simpa [exampleOpenChannel, ChannelId.Valid] using ChannelId.zero_valid

theorem exampleOpenChannel_pubKeys :
    ∀ p ∈ pubKeys exampleOpenChannel, p.Valid := by
  intro p hp
  have hp' : p = zeroPubKey := by
    simpa [pubKeys, exampleOpenChannel] using hp
  rw [hp']
  exact zeroPubKey_valid

/-- **The local record is non-vacuous.** -/
theorem exampleOpenChannel_wellFormed : wellFormed exampleOpenChannel := by
  refine ⟨?_, exampleOpenChannel_chainHash, exampleOpenChannel_channelId,
    exampleOpenChannel_pubKeys, ?_, ?_, ?_⟩
  · rw [exampleOpenChannel_msgLength]
    decide
  · decide
  · decide
  · decide

/-- The non-vacuous witness also satisfies the unconditional length bound. -/
theorem exampleOpenChannel_length : msgLength exampleOpenChannel ≤ 65535 :=
  wellFormed_length exampleOpenChannel_wellFormed

/-- The non-vacuous witness has a valid extracted channel id. -/
theorem exampleOpenChannel_channelId_valid :
    (channelId? exampleOpenChannel).isSome = true := by
  simp [channelId?]

end LnLean.Proofs.WaveH.H17
