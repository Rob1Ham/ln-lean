/-
# H14 — BOLT 2 `open_channel` (type 32) wire round trip (L1-03)

## English claim

BOLT 2 defines `open_channel` (type 32) as a fixed 18-field prefix followed by
an optional `open_channel_tlvs` stream.  The fixed prefix is

`chain_hash` (32) · `temporary_channel_id` (32) · six `u64` amounts (48) ·
`feerate_per_kw` (u32, 4) · `to_self_delay` and `max_accepted_htlcs` (two
`u16`, 4) · six `point` values (6 × 33 = 198) · `channel_flags` (1)

which sums to **319** payload bytes; the two-byte BOLT 1 type field makes the
message 321 bytes.

This module defines that wire record locally (it does **not** modify
`LnLean/Protocol/Messages.lean`), together with a big-endian encoder, a
strict prefix decoder, and proves:

1. `encode_size`: on the wire domain (fixed-width sizes and integer bounds)
   the payload is exactly 319 bytes;
2. `decode_encode`: the decoder inverts the encoder on the wire domain;
3. `decode_encode_<field>`: the round trip is field-by-field for all 18
   fields;
4. `decode_length`: every payload the decoder accepts is exactly 319 bytes
   (no truncation, no trailing bytes), so the parser is length-faithful;
5. `encode_injective_on_wireValid`: encoding is injective on the wire domain;
6. a concrete 319-byte witness, so none of the above is vacuous.

## Scope

The optional `open_channel_tlvs` stream (type 0 `upfront_shutdown_script`,
type 1 `channel_type`) is **not** decoded here.  Adding it would change the
accepted length from exactly 319 to "319 + a well-formed TLV stream" and needs
the TLV layer; this module therefore proves the sharp statement for the fixed
prefix and records the missing bytes in the lane report.  In particular the
wave-7 provisional `Messages.lean` patch used a 313-byte `msgLength` for a
different record: it omits `chain_hash` (32) and `channel_reserve_satoshis`
(8) and instead assumes an inline 34-byte `shutdown_scriptpubkey`.  The full
BOLT 2 fixed prefix is `313 + 32 + 8 - 34 = 319`.

No signature, policy, or consensus claim is made: the record is a byte layout,
not an authenticated message.

## Anchors

* BOLT 2 §"The `open_channel` Message"
  (`refs/bolts/02-peer-protocol.md:680-712`): the 18 fixed fields and the
  `open_channel_tlvs` stream.
* BOLT 1 §"Lightning Message Format"
  (`refs/bolts/01-messaging.md:43-92`): the two-byte type and the 65535-byte
  payload bound.
* Model convention: `LnLean/Protocol/Messages.lean` (`msgLength`,
  `channelId?`, `pubKeys`, `wellFormed`) and `LnLean/Wire/BigSize.lean`
  (`beBytes`, `decodeBE`, `bytesToList`).
-/

import LnLean.Protocol.Messages
import LnLean.Wire.BigSize
import LnLean.Wire.Message

namespace LnLean.Proofs.WaveH.H14

set_option autoImplicit false

open LnLean
open LnLean.Wire

/-! ## 1. The wire record -/

/-- BOLT 2 `open_channel` (type 32), fixed prefix only.

The eighteen fields are exactly the mandatory BOLT 2 fields up to and
including `channel_flags`; `open_channel_tlvs` is a separate optional tail and
is not part of this record.  Identifiers and public keys use the same wrapper
types as `LnLean.Protocol.AcceptChannel`, so the record can be moved into
`Messages.lean` unchanged. -/
structure OpenChannelMsg where
  /-- BOLT 2 `chain_hash` (32 bytes). -/
  chainHash : ChainHash
  /-- BOLT 2 `temporary_channel_id` (32 bytes). -/
  temporaryChannelId : ChannelId
  /-- BOLT 2 `funding_satoshis` (`u64`). -/
  fundingSatoshis : Nat
  /-- BOLT 2 `push_msat` (`u64`). -/
  pushMsat : Nat
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
  fundingPubkey : PubKey
  /-- BOLT 2 `revocation_basepoint` (`point`, 33 bytes). -/
  revocationBasepoint : PubKey
  /-- BOLT 2 `payment_basepoint` (`point`, 33 bytes). -/
  paymentBasepoint : PubKey
  /-- BOLT 2 `delayed_payment_basepoint` (`point`, 33 bytes). -/
  delayedPaymentBasepoint : PubKey
  /-- BOLT 2 `htlc_basepoint` (`point`, 33 bytes). -/
  htlcBasepoint : PubKey
  /-- BOLT 2 `first_per_commitment_point` (`point`, 33 bytes). -/
  firstPerCommitmentPoint : PubKey
  /-- BOLT 2 `channel_flags` (`byte`). -/
  channelFlags : UInt8
deriving Repr, BEq

namespace OpenChannelMsg

/-- The BOLT 1/2 message type of `open_channel`. -/
def wireType : Nat := 32

@[simp] theorem wireType_eq : wireType = 32 := rfl

/-- The wire domain: the fixed-width identifiers/points have exactly their
BOLT 2 sizes and each integer fits its declared width.  `channel_flags` is a
`UInt8`, so it is always one byte.  Without these side conditions `beBytes`
truncates modulo `256^k` and the round trip can only recover the truncated
value. -/
structure WireValid (m : OpenChannelMsg) : Prop where
  chainHash_size : m.chainHash.bytes.size = 32
  temporaryChannelId_size : m.temporaryChannelId.bytes.size = 32
  fundingSatoshis_lt : m.fundingSatoshis < 256 ^ 8
  pushMsat_lt : m.pushMsat < 256 ^ 8
  dustLimitSatoshis_lt : m.dustLimitSatoshis < 256 ^ 8
  maxHtlcValueInFlightMsat_lt : m.maxHtlcValueInFlightMsat < 256 ^ 8
  channelReserveSatoshis_lt : m.channelReserveSatoshis < 256 ^ 8
  htlcMinimumMsat_lt : m.htlcMinimumMsat < 256 ^ 8
  feeratePerKw_lt : m.feeratePerKw < 256 ^ 4
  toSelfDelay_lt : m.toSelfDelay < 256 ^ 2
  maxAcceptedHtlcs_lt : m.maxAcceptedHtlcs < 256 ^ 2
  fundingPubkey_size : m.fundingPubkey.bytes.size = 33
  revocationBasepoint_size : m.revocationBasepoint.bytes.size = 33
  paymentBasepoint_size : m.paymentBasepoint.bytes.size = 33
  delayedPaymentBasepoint_size : m.delayedPaymentBasepoint.bytes.size = 33
  htlcBasepoint_size : m.htlcBasepoint.bytes.size = 33
  firstPerCommitmentPoint_size : m.firstPerCommitmentPoint.bytes.size = 33

theorem wireValid_chainHash_valid {m : OpenChannelMsg} (h : m.WireValid) :
    m.chainHash.Valid := h.chainHash_size

theorem wireValid_temporaryChannelId_valid {m : OpenChannelMsg}
    (h : m.WireValid) : m.temporaryChannelId.Valid := h.temporaryChannelId_size

theorem wireValid_fundingPubkey_valid {m : OpenChannelMsg}
    (h : m.WireValid) : m.fundingPubkey.Valid := h.fundingPubkey_size

theorem wireValid_revocationBasepoint_valid {m : OpenChannelMsg}
    (h : m.WireValid) : m.revocationBasepoint.Valid := h.revocationBasepoint_size

theorem wireValid_paymentBasepoint_valid {m : OpenChannelMsg}
    (h : m.WireValid) : m.paymentBasepoint.Valid := h.paymentBasepoint_size

theorem wireValid_delayedPaymentBasepoint_valid {m : OpenChannelMsg}
    (h : m.WireValid) : m.delayedPaymentBasepoint.Valid :=
  h.delayedPaymentBasepoint_size

theorem wireValid_htlcBasepoint_valid {m : OpenChannelMsg}
    (h : m.WireValid) : m.htlcBasepoint.Valid := h.htlcBasepoint_size

theorem wireValid_firstPerCommitmentPoint_valid {m : OpenChannelMsg}
    (h : m.WireValid) : m.firstPerCommitmentPoint.Valid :=
  h.firstPerCommitmentPoint_size

/-! ## 2. Field widths and the encoder -/

/-- The width of each fixed field, in wire order. -/
def fieldWidths : List Nat :=
  [32, 32, 8, 8, 8, 8, 8, 8, 4, 2, 2, 33, 33, 33, 33, 33, 33, 1]

/-- The payload chunks, in wire order.  Numeric fields are big-endian
fixed-width; identifiers and points are their raw 32/33 bytes. -/
def chunks (m : OpenChannelMsg) : List ByteArray :=
  [m.chainHash.bytes,
   m.temporaryChannelId.bytes,
   beBytes m.fundingSatoshis 8,
   beBytes m.pushMsat 8,
   beBytes m.dustLimitSatoshis 8,
   beBytes m.maxHtlcValueInFlightMsat 8,
   beBytes m.channelReserveSatoshis 8,
   beBytes m.htlcMinimumMsat 8,
   beBytes m.feeratePerKw 4,
   beBytes m.toSelfDelay 2,
   beBytes m.maxAcceptedHtlcs 2,
   m.fundingPubkey.bytes,
   m.revocationBasepoint.bytes,
   m.paymentBasepoint.bytes,
   m.delayedPaymentBasepoint.bytes,
   m.htlcBasepoint.bytes,
   m.firstPerCommitmentPoint.bytes,
   beBytes m.channelFlags.toNat 1]

/-- The fixed-prefix payload: concatenation of the field chunks. -/
def encode (m : OpenChannelMsg) : ByteArray :=
  ((chunks m).map bytesToList).flatten.toByteArray

/-- Payload length, excluding the two-byte BOLT 1 type. -/
def payloadSize (m : OpenChannelMsg) : Nat := (encode m).size

/-- Whole-message length, including the two-byte BOLT 1 type. -/
def messageSize (m : OpenChannelMsg) : Nat := 2 + payloadSize m

@[simp] theorem bytesToList_encode (m : OpenChannelMsg) :
    bytesToList (encode m) = ((chunks m).map bytesToList).flatten := by
  simp [encode, bytesToList_toByteArray]

/-! ## 3. The decoder

The decoder is a strict prefix parser: it consumes the eighteen fixed widths
in order and requires the input to be fully consumed.  Trailing bytes and
short inputs are rejected. -/

end OpenChannelMsg

/-- Consume exactly `n` bytes from the front of a byte list.  `none` when
fewer than `n` bytes remain. -/
def takeExact (n : Nat) (l : List UInt8) : Option (ByteArray × List UInt8) :=
  if n ≤ l.length then some ((l.take n).toByteArray, l.drop n) else none

/-- Consume a sequence of fixed-width fields and require exact consumption. -/
def parseFields : List Nat → List UInt8 → Option (List ByteArray)
  | [], l => if l.isEmpty then some [] else none
  | n :: ns, l =>
      match takeExact n l with
      | none => none
      | some (b, rest) =>
          match parseFields ns rest with
          | none => none
          | some bs => some (b :: bs)

namespace OpenChannelMsg

/-- Rebuild the record from the eighteen parsed chunks.  Any other chunk
count is rejected. -/
def decodeChunks : List ByteArray → Option OpenChannelMsg
  | [chainHash, temporaryChannelId, fundingSatoshis, pushMsat,
     dustLimitSatoshis, maxHtlcValueInFlightMsat, channelReserveSatoshis,
     htlcMinimumMsat, feeratePerKw, toSelfDelay, maxAcceptedHtlcs,
     fundingPubkey, revocationBasepoint, paymentBasepoint,
     delayedPaymentBasepoint, htlcBasepoint, firstPerCommitmentPoint,
     channelFlags] =>
      some
        { chainHash := ⟨chainHash⟩
          temporaryChannelId := ⟨temporaryChannelId⟩
          fundingSatoshis := decodeBE fundingSatoshis
          pushMsat := decodeBE pushMsat
          dustLimitSatoshis := decodeBE dustLimitSatoshis
          maxHtlcValueInFlightMsat := decodeBE maxHtlcValueInFlightMsat
          channelReserveSatoshis := decodeBE channelReserveSatoshis
          htlcMinimumMsat := decodeBE htlcMinimumMsat
          feeratePerKw := decodeBE feeratePerKw
          toSelfDelay := decodeBE toSelfDelay
          maxAcceptedHtlcs := decodeBE maxAcceptedHtlcs
          fundingPubkey := ⟨fundingPubkey⟩
          revocationBasepoint := ⟨revocationBasepoint⟩
          paymentBasepoint := ⟨paymentBasepoint⟩
          delayedPaymentBasepoint := ⟨delayedPaymentBasepoint⟩
          htlcBasepoint := ⟨htlcBasepoint⟩
          firstPerCommitmentPoint := ⟨firstPerCommitmentPoint⟩
          channelFlags := (decodeBE channelFlags).toUInt8 }
  | _ => none

/-- Decode a fixed-prefix `open_channel` payload.  The input must be exactly
the concatenation of the eighteen fields; no TLV tail is accepted. -/
def decode (b : ByteArray) : Option OpenChannelMsg :=
  (parseFields fieldWidths (bytesToList b)).bind decodeChunks

end OpenChannelMsg

/-! ## 4. Parser lemmas -/

/-- `takeExact` returns exactly `n` bytes. -/
theorem takeExact_size {n : Nat} {l : List UInt8} {c : ByteArray}
    {rest : List UInt8} (h : takeExact n l = some (c, rest)) : c.size = n := by
  by_cases hle : n ≤ l.length
  · simp only [takeExact, ite_eq_left hle, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [List.size_toByteArray, List.length_take, Nat.min_eq_left hle]
  · simp only [takeExact, ite_eq_right hle] at h
    simp at h

/-- `takeExact` consumes exactly `n` bytes of the input. -/
theorem takeExact_length {n : Nat} {l : List UInt8} {c : ByteArray}
    {rest : List UInt8} (h : takeExact n l = some (c, rest)) :
    l.length = n + rest.length := by
  by_cases hle : n ≤ l.length
  · simp only [takeExact, ite_eq_left hle, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [List.length_drop]
    omega
  · simp only [takeExact, ite_eq_right hle] at h
    simp at h

/-- `takeExact` prepends one known chunk. -/
theorem takeExact_append (n : Nat) (c : ByteArray) (rest : List UInt8)
    (h : c.size = n) :
    takeExact n (bytesToList c ++ rest) = some (c, rest) := by
  have hn : n = (bytesToList c).length := by rw [← h, bytesToList_length]
  by_cases hle : n ≤ (bytesToList c ++ rest).length
  · simp only [takeExact, ite_eq_left hle]
    rw [hn, List.take_left, List.drop_left, toByteArray_bytesToList]
  · have hle' : (bytesToList c).length ≤ (bytesToList c ++ rest).length := by
      rw [List.length_append]
      exact Nat.le_add_right _ _
    omega

/-- If the widths and the `ByteArray.size` image of the chunks agree, then
every chunk in the zip has its declared width. -/
theorem zip_size_of_map_size (ws : List Nat) (cs : List ByteArray)
    (h : cs.map ByteArray.size = ws) :
    ∀ k c, (k, c) ∈ ws.zip cs → c.size = k := by
  induction ws generalizing cs with
  | nil =>
      intro k c hm
      simp at hm
  | cons w ws ih =>
      intro k c' hm
      cases cs with
      | nil => simp at h
      | cons c cs =>
          have h' : c.size = w ∧ cs.map ByteArray.size = ws := by
            simpa using h
          rcases h' with ⟨hc, htail⟩
          simp only [List.zip_cons_cons, List.mem_cons] at hm
          rcases hm with hm | hm
          · obtain ⟨rfl, rfl⟩ := hm
            exact hc
          · exact ih cs htail k c' hm

namespace OpenChannelMsg

/-- On the wire domain the chunk sizes are exactly the field widths. -/
theorem chunks_size_eq (m : OpenChannelMsg) (h : m.WireValid) :
    (chunks m).map ByteArray.size = fieldWidths := by
  simp [chunks, fieldWidths, beBytes_size, h.chainHash_size,
    h.temporaryChannelId_size, h.fundingPubkey_size,
    h.revocationBasepoint_size, h.paymentBasepoint_size,
    h.delayedPaymentBasepoint_size, h.htlcBasepoint_size,
    h.firstPerCommitmentPoint_size]

/-- Consequently the chunk list has the same length as the width list. -/
theorem chunks_length (m : OpenChannelMsg) (h : m.WireValid) :
    (chunks m).length = fieldWidths.length := by
  have := congrArg List.length (chunks_size_eq m h)
  simpa using this

end OpenChannelMsg

/-- **Chunk parser round trip.**  Parsing the concatenation of chunks whose
sizes match the width list returns exactly those chunks. -/
theorem parseFields_chunks :
    ∀ (ws : List Nat) (cs : List ByteArray),
      cs.length = ws.length →
      (∀ k c, (k, c) ∈ ws.zip cs → c.size = k) →
      parseFields ws ((cs.map bytesToList).flatten) = some cs := by
  intro ws
  induction ws with
  | nil =>
      intro cs hlen _
      cases cs with
      | nil => simp [parseFields]
      | cons c cs => simp at hlen
  | cons w ws ih =>
      intro cs hlen hsz
      cases cs with
      | nil => simp at hlen
      | cons c cs =>
          have hc : c.size = w := hsz w c (by simp)
          have hlen' : cs.length = ws.length := by simpa using hlen
          have hsz' : ∀ k c', (k, c') ∈ ws.zip cs → c'.size = k := by
            intro k c' hm
            exact hsz k c' (List.mem_cons_of_mem _ hm)
          simp only [List.map_cons, List.flatten_cons, parseFields]
          rw [takeExact_append w c _ hc]
          dsimp only
          rw [ih cs hlen' hsz']

/-- **Parser length law.**  Every payload accepted by the fixed-prefix parser
has length equal to the sum of the declared widths. -/
theorem parseFields_length :
    ∀ (ws : List Nat) (l : List UInt8) (cs : List ByteArray),
      parseFields ws l = some cs → l.length = ws.sum := by
  intro ws
  induction ws with
  | nil =>
      intro l cs h
      cases l with
      | nil => simp
      | cons x xs => simp [parseFields] at h
  | cons w ws ih =>
      intro l cs h
      cases ht : takeExact w l with
      | none => simp [parseFields, ht] at h
      | some p =>
          obtain ⟨c, rest⟩ := p
          cases hr : parseFields ws rest with
          | none => simp [parseFields, ht, hr] at h
          | some cs' =>
              have hsome : parseFields (w :: ws) l = some (c :: cs') := by
                simp [parseFields, ht, hr]
              have hl := takeExact_length ht
              have hrec := ih rest cs' hr
              rw [List.sum_cons]
              omega

/-- **Parser shape law.**  An accepted chunk list has exactly one chunk per
declared width, and every chunk has its declared width. -/
theorem parseFields_spec :
    ∀ (ws : List Nat) (l : List UInt8) (cs : List ByteArray),
      parseFields ws l = some cs →
      cs.length = ws.length ∧
        (∀ k c, (k, c) ∈ ws.zip cs → c.size = k) := by
  intro ws
  induction ws with
  | nil =>
      intro l cs h
      cases l with
      | nil =>
          simp [parseFields] at h
          subst h
          exact ⟨rfl, by simp⟩
      | cons x xs => simp [parseFields] at h
  | cons w ws ih =>
      intro l cs h
      cases ht : takeExact w l with
      | none => simp [parseFields, ht] at h
      | some p =>
          obtain ⟨c, rest⟩ := p
          cases hr : parseFields ws rest with
          | none => simp [parseFields, ht, hr] at h
          | some cs' =>
              have hsome : parseFields (w :: ws) l = some (c :: cs') := by
                simp [parseFields, ht, hr]
              rw [hsome] at h
              have hcons : c :: cs' = cs := Option.some.inj h
              rw [← hcons]
              have hc := takeExact_size ht
              have ih' := ih rest cs' hr
              refine ⟨by simp [ih'.1], ?_⟩
              intro k c' hm
              simp only [List.zip_cons_cons, List.mem_cons] at hm
              rcases hm with hm | hm
              · obtain ⟨rfl, rfl⟩ := hm
                exact hc
              · exact ih'.2 k c' hm

/-- Every byte array is smaller than `256 ^ size` when read big-endian. -/
theorem decodeBEList_lt_pow : ∀ l : List UInt8, decodeBEList l < 256 ^ l.length
  | [] => by simp [decodeBEList]
  | b :: rest => by
      rw [decodeBEList]
      have hb : b.toNat < 256 := by
        have := b.toNat_lt
        simpa using this
      have hr : decodeBEList rest < 256 ^ rest.length := decodeBEList_lt_pow rest
      have h1 : b.toNat * 256 ^ rest.length + decodeBEList rest <
          b.toNat * 256 ^ rest.length + 256 ^ rest.length :=
        Nat.add_lt_add_left hr _
      have h2 : b.toNat * 256 ^ rest.length + 256 ^ rest.length ≤
          256 * 256 ^ rest.length := by
        rw [← Nat.succ_mul]
        exact Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hb)
      have h3 := Nat.lt_of_lt_of_le h1 h2
      simpa [Nat.pow_succ, Nat.mul_comm] using h3

/-- Big-endian decoding of a byte array is bounded by `256 ^ size`. -/
theorem decodeBE_lt_pow (b : ByteArray) : decodeBE b < 256 ^ b.size := by
  unfold decodeBE
  rw [← bytesToList_length b]
  exact decodeBEList_lt_pow (bytesToList b)

/-! ## 5. Round trip and length -/

/-- **Encoder/decoder round trip.**  On the wire domain the strict
fixed-prefix decoder returns the original `open_channel` record. -/
theorem decode_encode (m : OpenChannelMsg) (h : m.WireValid) :
    OpenChannelMsg.decode (OpenChannelMsg.encode m) = some m := by
  have hmap := OpenChannelMsg.chunks_size_eq m h
  have hlen := OpenChannelMsg.chunks_length m h
  have hsz : ∀ k c, (k, c) ∈ OpenChannelMsg.fieldWidths.zip
      (OpenChannelMsg.chunks m) → c.size = k :=
    zip_size_of_map_size OpenChannelMsg.fieldWidths (OpenChannelMsg.chunks m) hmap
  have hparse : parseFields OpenChannelMsg.fieldWidths (bytesToList (OpenChannelMsg.encode m)) =
      some (OpenChannelMsg.chunks m) := by
    rw [OpenChannelMsg.bytesToList_encode]
    exact parseFields_chunks OpenChannelMsg.fieldWidths (OpenChannelMsg.chunks m)
      hlen hsz
  simp only [OpenChannelMsg.decode, hparse]
  change OpenChannelMsg.decodeChunks (OpenChannelMsg.chunks m) = some m
  have hflags : m.channelFlags.toNat < 256 ^ 1 := by
    have hpow : (256 : Nat) ^ 1 = 2 ^ 8 := by decide
    rw [hpow]
    exact m.channelFlags.toNat_lt
  simp only [OpenChannelMsg.decodeChunks, OpenChannelMsg.chunks]
  simp only [decodeBE_beBytes_of_lt, h.fundingSatoshis_lt, h.pushMsat_lt,
    h.dustLimitSatoshis_lt, h.maxHtlcValueInFlightMsat_lt,
    h.channelReserveSatoshis_lt, h.htlcMinimumMsat_lt, h.feeratePerKw_lt,
    h.toSelfDelay_lt, h.maxAcceptedHtlcs_lt, hflags,
    Nat.toUInt8, UInt8.ofNat_toNat]

/-- **Payload length.**  On the wire domain the fixed-prefix payload is
exactly the BOLT 2 sum `32+32+6*8+4+2+2+6*33+1 = 319`. -/
theorem encode_size (m : OpenChannelMsg) (h : m.WireValid) :
    (OpenChannelMsg.encode m).size = 319 := by
  have hsum : OpenChannelMsg.fieldWidths.sum = 319 := by decide
  have hmap := OpenChannelMsg.chunks_size_eq m h
  rw [← bytesToList_length (OpenChannelMsg.encode m), OpenChannelMsg.bytesToList_encode,
    List.length_flatten, List.map_map]
  have hmap' : List.map (List.length ∘ bytesToList) (OpenChannelMsg.chunks m) =
      List.map ByteArray.size (OpenChannelMsg.chunks m) := by
    apply List.map_congr_left
    intro c _
    simp [Function.comp_apply, bytesToList_length]
  rw [hmap', hmap, hsum]

/-- The documented arithmetic form of the payload layout. -/
theorem payload_layout : 32 + 32 + 8 * 6 + 4 + 2 + 2 + 33 * 6 + 1 = 319 := by
  decide

/-- **Whole-message length.**  With the two-byte BOLT 1 type the message is
321 bytes on the wire domain. -/
theorem messageSize_eq (m : OpenChannelMsg) (h : m.WireValid) :
    OpenChannelMsg.messageSize m = 321 := by
  unfold OpenChannelMsg.messageSize OpenChannelMsg.payloadSize
  rw [encode_size m h]

/-- **Decoder length law.**  Every payload accepted by the strict
fixed-prefix decoder is exactly 319 bytes: no truncated input and no trailing
bytes (including a TLV tail) are accepted. -/
theorem decode_length (b : ByteArray) (m : OpenChannelMsg)
    (h : OpenChannelMsg.decode b = some m) : b.size = 319 := by
  have hsum : OpenChannelMsg.fieldWidths.sum = 319 := by decide
  unfold OpenChannelMsg.decode at h
  cases hp : parseFields OpenChannelMsg.fieldWidths (bytesToList b) with
  | none => simp [hp] at h
  | some cs =>
      have hlen := parseFields_length OpenChannelMsg.fieldWidths (bytesToList b) cs hp
      rw [← bytesToList_length b, hlen, hsum]

/-- **Encoding is injective on the wire domain.** -/
theorem encode_injective_on_wireValid {m₁ m₂ : OpenChannelMsg}
    (h₁ : m₁.WireValid) (h₂ : m₂.WireValid)
    (he : OpenChannelMsg.encode m₁ = OpenChannelMsg.encode m₂) : m₁ = m₂ := by
  have hr₁ := decode_encode m₁ h₁
  have hr₂ := decode_encode m₂ h₂
  rw [he, hr₂] at hr₁
  exact (Option.some.inj hr₁).symm

/-! ### Field-by-field round trip

The decoder reconstructs every one of the eighteen fields.  These projections
make the round trip usable fieldwise without unfolding `decode_encode`. -/

@[simp] theorem decode_encode_chainHash (m : OpenChannelMsg) (h : m.WireValid) :
    (OpenChannelMsg.decode (OpenChannelMsg.encode m)).map (fun r => r.chainHash) =
      some m.chainHash := by
  rw [decode_encode m h]
  rfl

@[simp] theorem decode_encode_temporaryChannelId (m : OpenChannelMsg)
    (h : m.WireValid) :
    (OpenChannelMsg.decode (OpenChannelMsg.encode m)).map
      (fun r => r.temporaryChannelId) = some m.temporaryChannelId := by
  rw [decode_encode m h]
  rfl

@[simp] theorem decode_encode_fundingSatoshis (m : OpenChannelMsg) (h : m.WireValid) :
    (OpenChannelMsg.decode (OpenChannelMsg.encode m)).map
      (fun r => r.fundingSatoshis) = some m.fundingSatoshis := by
  rw [decode_encode m h]
  rfl

@[simp] theorem decode_encode_pushMsat (m : OpenChannelMsg) (h : m.WireValid) :
    (OpenChannelMsg.decode (OpenChannelMsg.encode m)).map (fun r => r.pushMsat) =
      some m.pushMsat := by
  rw [decode_encode m h]
  rfl

@[simp] theorem decode_encode_dustLimitSatoshis (m : OpenChannelMsg)
    (h : m.WireValid) :
    (OpenChannelMsg.decode (OpenChannelMsg.encode m)).map
      (fun r => r.dustLimitSatoshis) = some m.dustLimitSatoshis := by
  rw [decode_encode m h]
  rfl

@[simp] theorem decode_encode_maxHtlcValueInFlightMsat (m : OpenChannelMsg)
    (h : m.WireValid) :
    (OpenChannelMsg.decode (OpenChannelMsg.encode m)).map
      (fun r => r.maxHtlcValueInFlightMsat) = some m.maxHtlcValueInFlightMsat := by
  rw [decode_encode m h]
  rfl

@[simp] theorem decode_encode_channelReserveSatoshis (m : OpenChannelMsg)
    (h : m.WireValid) :
    (OpenChannelMsg.decode (OpenChannelMsg.encode m)).map
      (fun r => r.channelReserveSatoshis) = some m.channelReserveSatoshis := by
  rw [decode_encode m h]
  rfl

@[simp] theorem decode_encode_htlcMinimumMsat (m : OpenChannelMsg)
    (h : m.WireValid) :
    (OpenChannelMsg.decode (OpenChannelMsg.encode m)).map
      (fun r => r.htlcMinimumMsat) = some m.htlcMinimumMsat := by
  rw [decode_encode m h]
  rfl

@[simp] theorem decode_encode_feeratePerKw (m : OpenChannelMsg) (h : m.WireValid) :
    (OpenChannelMsg.decode (OpenChannelMsg.encode m)).map
      (fun r => r.feeratePerKw) = some m.feeratePerKw := by
  rw [decode_encode m h]
  rfl

@[simp] theorem decode_encode_toSelfDelay (m : OpenChannelMsg) (h : m.WireValid) :
    (OpenChannelMsg.decode (OpenChannelMsg.encode m)).map
      (fun r => r.toSelfDelay) = some m.toSelfDelay := by
  rw [decode_encode m h]
  rfl

@[simp] theorem decode_encode_maxAcceptedHtlcs (m : OpenChannelMsg)
    (h : m.WireValid) :
    (OpenChannelMsg.decode (OpenChannelMsg.encode m)).map
      (fun r => r.maxAcceptedHtlcs) = some m.maxAcceptedHtlcs := by
  rw [decode_encode m h]
  rfl

@[simp] theorem decode_encode_fundingPubkey (m : OpenChannelMsg) (h : m.WireValid) :
    (OpenChannelMsg.decode (OpenChannelMsg.encode m)).map
      (fun r => r.fundingPubkey) = some m.fundingPubkey := by
  rw [decode_encode m h]
  rfl

@[simp] theorem decode_encode_revocationBasepoint (m : OpenChannelMsg)
    (h : m.WireValid) :
    (OpenChannelMsg.decode (OpenChannelMsg.encode m)).map
      (fun r => r.revocationBasepoint) = some m.revocationBasepoint := by
  rw [decode_encode m h]
  rfl

@[simp] theorem decode_encode_paymentBasepoint (m : OpenChannelMsg)
    (h : m.WireValid) :
    (OpenChannelMsg.decode (OpenChannelMsg.encode m)).map
      (fun r => r.paymentBasepoint) = some m.paymentBasepoint := by
  rw [decode_encode m h]
  rfl

@[simp] theorem decode_encode_delayedPaymentBasepoint (m : OpenChannelMsg)
    (h : m.WireValid) :
    (OpenChannelMsg.decode (OpenChannelMsg.encode m)).map
      (fun r => r.delayedPaymentBasepoint) = some m.delayedPaymentBasepoint := by
  rw [decode_encode m h]
  rfl

@[simp] theorem decode_encode_htlcBasepoint (m : OpenChannelMsg) (h : m.WireValid) :
    (OpenChannelMsg.decode (OpenChannelMsg.encode m)).map
      (fun r => r.htlcBasepoint) = some m.htlcBasepoint := by
  rw [decode_encode m h]
  rfl

@[simp] theorem decode_encode_firstPerCommitmentPoint (m : OpenChannelMsg)
    (h : m.WireValid) :
    (OpenChannelMsg.decode (OpenChannelMsg.encode m)).map
      (fun r => r.firstPerCommitmentPoint) = some m.firstPerCommitmentPoint := by
  rw [decode_encode m h]
  rfl

@[simp] theorem decode_encode_channelFlags (m : OpenChannelMsg) (h : m.WireValid) :
    (OpenChannelMsg.decode (OpenChannelMsg.encode m)).map
      (fun r => r.channelFlags) = some m.channelFlags := by
  rw [decode_encode m h]
  rfl

/-! ## 6. Non-vacuity: a concrete 319-byte witness -/

/-- A run of `n` zero bytes. -/
def zeros (n : Nat) : ByteArray := (List.replicate n 0).toByteArray

@[simp] theorem zeros_size (n : Nat) : (zeros n).size = n := by
  simp [zeros]

/-- The zero-payload `open_channel` witness: all identifiers, amounts, and
points are zero bytes of the BOLT 2 widths. -/
def witness : OpenChannelMsg where
  chainHash := ⟨zeros 32⟩
  temporaryChannelId := ⟨zeros 32⟩
  fundingSatoshis := 0
  pushMsat := 0
  dustLimitSatoshis := 0
  maxHtlcValueInFlightMsat := 0
  channelReserveSatoshis := 0
  htlcMinimumMsat := 0
  feeratePerKw := 0
  toSelfDelay := 0
  maxAcceptedHtlcs := 0
  fundingPubkey := ⟨zeros 33⟩
  revocationBasepoint := ⟨zeros 33⟩
  paymentBasepoint := ⟨zeros 33⟩
  delayedPaymentBasepoint := ⟨zeros 33⟩
  htlcBasepoint := ⟨zeros 33⟩
  firstPerCommitmentPoint := ⟨zeros 33⟩
  channelFlags := 0

theorem witness_wireValid : witness.WireValid := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩ <;>
    simp [witness, zeros_size]

/-- The witness has a 319-byte payload. -/
theorem witness_encode_size : (OpenChannelMsg.encode witness).size = 319 :=
  encode_size witness witness_wireValid

/-- The witness round-trips. -/
theorem witness_roundtrip :
    OpenChannelMsg.decode (OpenChannelMsg.encode witness) = some witness :=
  decode_encode witness witness_wireValid

/-- The witness is accepted with exactly 319 input bytes. -/
theorem witness_decode_length : (OpenChannelMsg.encode witness).size = 319 :=
  decode_length (OpenChannelMsg.encode witness) witness witness_roundtrip

/-- Any input whose length is not exactly 319 bytes is rejected. -/
theorem decode_eq_none_of_size_ne {b : ByteArray} (h : b.size ≠ 319) :
    OpenChannelMsg.decode b = none := by
  cases hd : OpenChannelMsg.decode b with
  | none => rfl
  | some m => exact absurd (decode_length b m hd) h

/-- Inputs shorter than the 319-byte fixed prefix are rejected. -/
theorem decode_eq_none_of_size_lt {b : ByteArray} (h : b.size < 319) :
    OpenChannelMsg.decode b = none :=
  decode_eq_none_of_size_ne (Nat.ne_of_lt h)

/-- Inputs longer than the 319-byte fixed prefix are rejected (no TLV tail is
accepted). -/
theorem decode_eq_none_of_size_gt {b : ByteArray} (h : 319 < b.size) :
    OpenChannelMsg.decode b = none :=
  decode_eq_none_of_size_ne (Nat.ne_of_gt h)

/-! ## 7. Decoder soundness -/

/-- **Decoder soundness, chunk level.**  A record assembled from chunks with
the declared widths is wire-valid. -/
theorem decodeChunks_wireValid_of_spec {cs : List ByteArray} {m : OpenChannelMsg}
    (hsz : ∀ k c, (k, c) ∈ OpenChannelMsg.fieldWidths.zip cs → c.size = k)
    (h : OpenChannelMsg.decodeChunks cs = some m) : m.WireValid := by
  simp only [OpenChannelMsg.decodeChunks] at h
  split at h
  · rename_i chainHash temporaryChannelId fundingSatoshis pushMsat
      dustLimitSatoshis maxHtlcValueInFlightMsat channelReserveSatoshis
      htlcMinimumMsat feeratePerKw toSelfDelay maxAcceptedHtlcs
      fundingPubkey revocationBasepoint paymentBasepoint
      delayedPaymentBasepoint htlcBasepoint firstPerCommitmentPoint channelFlags
    simp only [Option.some.injEq] at h
    subst h
    have hch : chainHash.size = 32 :=
      hsz 32 chainHash (by simp [OpenChannelMsg.fieldWidths])
    have htid : temporaryChannelId.size = 32 :=
      hsz 32 temporaryChannelId (by simp [OpenChannelMsg.fieldWidths])
    have hfund : decodeBE fundingSatoshis < 256 ^ 8 := by
      have hs : fundingSatoshis.size = 8 :=
        hsz 8 fundingSatoshis (by simp [OpenChannelMsg.fieldWidths])
      have := decodeBE_lt_pow fundingSatoshis
      rwa [hs] at this
    have hpush : decodeBE pushMsat < 256 ^ 8 := by
      have hs : pushMsat.size = 8 :=
        hsz 8 pushMsat (by simp [OpenChannelMsg.fieldWidths])
      have := decodeBE_lt_pow pushMsat
      rwa [hs] at this
    have hdust : decodeBE dustLimitSatoshis < 256 ^ 8 := by
      have hs : dustLimitSatoshis.size = 8 :=
        hsz 8 dustLimitSatoshis (by simp [OpenChannelMsg.fieldWidths])
      have := decodeBE_lt_pow dustLimitSatoshis
      rwa [hs] at this
    have hmaxflight : decodeBE maxHtlcValueInFlightMsat < 256 ^ 8 := by
      have hs : maxHtlcValueInFlightMsat.size = 8 :=
        hsz 8 maxHtlcValueInFlightMsat (by simp [OpenChannelMsg.fieldWidths])
      have := decodeBE_lt_pow maxHtlcValueInFlightMsat
      rwa [hs] at this
    have hreserve : decodeBE channelReserveSatoshis < 256 ^ 8 := by
      have hs : channelReserveSatoshis.size = 8 :=
        hsz 8 channelReserveSatoshis (by simp [OpenChannelMsg.fieldWidths])
      have := decodeBE_lt_pow channelReserveSatoshis
      rwa [hs] at this
    have hhtlcmin : decodeBE htlcMinimumMsat < 256 ^ 8 := by
      have hs : htlcMinimumMsat.size = 8 :=
        hsz 8 htlcMinimumMsat (by simp [OpenChannelMsg.fieldWidths])
      have := decodeBE_lt_pow htlcMinimumMsat
      rwa [hs] at this
    have hfeerate : decodeBE feeratePerKw < 256 ^ 4 := by
      have hs : feeratePerKw.size = 4 :=
        hsz 4 feeratePerKw (by simp [OpenChannelMsg.fieldWidths])
      have := decodeBE_lt_pow feeratePerKw
      rwa [hs] at this
    have hselfdelay : decodeBE toSelfDelay < 256 ^ 2 := by
      have hs : toSelfDelay.size = 2 :=
        hsz 2 toSelfDelay (by simp [OpenChannelMsg.fieldWidths])
      have := decodeBE_lt_pow toSelfDelay
      rwa [hs] at this
    have hmaxhtlcs : decodeBE maxAcceptedHtlcs < 256 ^ 2 := by
      have hs : maxAcceptedHtlcs.size = 2 :=
        hsz 2 maxAcceptedHtlcs (by simp [OpenChannelMsg.fieldWidths])
      have := decodeBE_lt_pow maxAcceptedHtlcs
      rwa [hs] at this
    have hfundkey : fundingPubkey.size = 33 :=
      hsz 33 fundingPubkey (by simp [OpenChannelMsg.fieldWidths])
    have hrevkey : revocationBasepoint.size = 33 :=
      hsz 33 revocationBasepoint (by simp [OpenChannelMsg.fieldWidths])
    have hpaykey : paymentBasepoint.size = 33 :=
      hsz 33 paymentBasepoint (by simp [OpenChannelMsg.fieldWidths])
    have hdelkey : delayedPaymentBasepoint.size = 33 :=
      hsz 33 delayedPaymentBasepoint (by simp [OpenChannelMsg.fieldWidths])
    have hhtlckey : htlcBasepoint.size = 33 :=
      hsz 33 htlcBasepoint (by simp [OpenChannelMsg.fieldWidths])
    have hfirstkey : firstPerCommitmentPoint.size = 33 :=
      hsz 33 firstPerCommitmentPoint (by simp [OpenChannelMsg.fieldWidths])
    exact ⟨hch, htid, hfund, hpush, hdust, hmaxflight, hreserve, hhtlcmin,
      hfeerate, hselfdelay, hmaxhtlcs, hfundkey, hrevkey, hpaykey, hdelkey,
      hhtlckey, hfirstkey⟩
  · simp at h

/-- **Decoder soundness.**  Every record accepted by `decode` is wire-valid. -/
theorem decode_wireValid (b : ByteArray) (m : OpenChannelMsg)
    (h : OpenChannelMsg.decode b = some m) : m.WireValid := by
  simp only [OpenChannelMsg.decode] at h
  cases hp : parseFields OpenChannelMsg.fieldWidths (bytesToList b) with
  | none => simp [hp] at h
  | some cs =>
      simp only [hp, Option.bind_some] at h
      exact decodeChunks_wireValid_of_spec
        (parseFields_spec OpenChannelMsg.fieldWidths (bytesToList b) cs hp).2 h

/-! ## 8. Axiom audit -/

#print axioms decode_encode
#print axioms encode_size
#print axioms decode_length
#print axioms decode_wireValid
#print axioms encode_injective_on_wireValid
#print axioms witness_roundtrip

end LnLean.Proofs.WaveH.H14
