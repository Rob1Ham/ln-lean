/-
# H18 — negative, truncation, and wrong-type tests for `open_channel` (L1-03)

**Catalog issue.** `L1-03` (P1): the type-32 `open_channel` message is not
registered in `LnLean.Protocol.Messages`, and no decoder boundary exists for it.
Lanes H13/H14/H17 add the wire record, a round-trip/parser theorem, and the
type-registration facts.  This module is the independent negative side: a
local, reproducible byte-level decoder for the mandatory BOLT 2 v1 payload and
machine-checked rejection tests for malformed frames.

## Model

The mandatory BOLT 2 `open_channel` data (BOLT 2 §"The `open_channel`
Message", `refs/bolts/02-peer-protocol.md:686-706`) is parsed in order:

```
chain_hash                   32
temporary_channel_id         32
funding_satoshis              8
push_msat                     8
dust_limit_satoshis           8
max_htlc_value_in_flight_msat 8
channel_reserve_satoshis      8
htlc_minimum_msat             8
feerate_per_kw                4
to_self_delay                 2
max_accepted_htlcs            2
funding_pubkey               33
revocation_basepoint         33
payment_basepoint            33
delayed_payment_basepoint    33
htlc_basepoint               33
first_per_commitment_point   33
channel_flags                 1
                            ---
                            319 bytes
```

This is exactly `H17.basePayloadLength`/`msgLength_none` (the wave-7 sketch's
`313` omitted `chain_hash` and under-counted `channel_reserve_satoshis`).
Integers are read big-endian into `Nat`; byte fields are kept as exact byte
slices, so no `ByteArray`/`PubKey`/`BtcAmount` coercion hides a width.

`decodeFrame` models the **payload-only BOLT 1 abstract frame**
`type (2) || payload length (2) || payload`.  It is deliberately not the BOLT 8
transport frame, whose length field counts the type as well; the concrete
theorem `decodeFrame_transportFrame_sample` records that boundary.

## Exact acceptance conditions

`decodePayload l = some m` holds only when all of the following hold:

1. `l.length = 319` (so both every fixed-width read succeeds and there are no
   trailing bytes);
2. the six point fields each have a first byte in `{0x02, 0x03}` (compressed
   public-key tag);
3. every fixed-width integer field is present and read as a big-endian `Nat`.

`decodeFrame l = some m` additionally requires:

4. at least four header bytes;
5. the type field decodes to `32` (`0x0020`);
6. the declared payload length equals the number of remaining bytes;
7. the remaining payload satisfies 1-3.

## Exact rejection conditions (proved here)

* Any payload with `l.length ≠ 319` — every truncation, every extra byte, and
  every legitimate TLV extension — is rejected by
  `decodePayload_eq_none_of_length_ne`.
* Any list shorter than four bytes is rejected
  (`decodeFrame_eq_none_of_length_lt_four`).
* Any header with type ≠ 32 is rejected
  (`decodeFrame_eq_none_of_type_ne`), including types 31, 33, 64, and 65535 in
  the concrete vectors.
* Any header whose declared payload length differs from the remaining byte
  count is rejected (`decodeFrame_eq_none_of_declared_ne`).
* The concrete vectors below also reject `0x00`/`0x04`/`0xff` point tags.

## Parser boundaries (not modelled, therefore not checked)

* `channel_flags` undefined bits are **accepted**: BOLT 2 says the receiving
  node MUST ignore them.  `decodePayload_sample_flags_ff` pins that decision.
* No semantic check is made: `channel_reserve >= dust_limit`, amount ranges,
  `chain_hash` identity, curve membership of the point bytes, `feerate_per_kw`,
  and `to_self_delay` semantics are outside this decoder.
* Optional `open_channel_tlvs` are not parsed.  A payload carrying an
  `upfront_shutdown_script` is rejected by the exact-length rule; extending the
  decoder is a separate model change.  `H17.msgLength_some` is the length model
  for that extension.
* No signature is carried, and no cryptographic check is performed.

## Reproducibility

All vectors are local `List UInt8` values built from explicit big-endian
encoders; there is no external fixture and no filesystem/network input.  Kernel
`decide` is used only on the bounded concrete vectors.

## Anchors

* BOLT 2 §"The `open_channel` Message" (type 32, field list):
  `refs/bolts/02-peer-protocol.md:680-706`.
* BOLT 2 requirements: undefined `channel_flags` bits MUST be ignored
  (`refs/bolts/02-peer-protocol.md:812`, `:838`).
* BOLT 1 §"Lightning Message Format": two-byte type and payload length
  (`refs/bolts/01-messaging.md:43-92`).
* rust-lightning `OpenChannel` wire order:
  `refs/rust-lightning/lightning/src/ln/msgs.rs:3295-3350`; record at `:289`,
  common fields at `:191`.
* Model cross-reference: `LnLean.Proofs.WaveH.H17` (`basePayloadLength = 319`,
  `msgLength_none`).
-/

import LnLean.Basic.Core

namespace LnLean.Proofs.WaveH.H18

set_option autoImplicit false
set_option maxRecDepth 100000

open LnLean

/-! ## 1. Local wire record and fixed constants -/

/-- BOLT 2 `open_channel` (type 32) mandatory payload.  Byte fields are exact
wire slices; integer fields are the big-endian `Nat` values (a `u64` field is
therefore automatically below `2^64`).  Optional TLVs are not represented. -/
structure OpenChannelMsg where
  chainHash : List UInt8
  temporaryChannelId : List UInt8
  fundingSatoshis : Nat
  pushMsat : Nat
  dustLimitSatoshis : Nat
  maxHtlcValueInFlightMsat : Nat
  channelReserveSatoshis : Nat
  htlcMinimumMsat : Nat
  feeratePerKw : Nat
  toSelfDelay : Nat
  maxAcceptedHtlcs : Nat
  fundingPubkey : List UInt8
  revocationBasepoint : List UInt8
  paymentBasepoint : List UInt8
  delayedPaymentBasepoint : List UInt8
  htlcBasepoint : List UInt8
  firstPerCommitmentPoint : List UInt8
  channelFlags : UInt8
deriving Repr, DecidableEq, BEq

/-- BOLT 2 wire type of `open_channel`. -/
def TYPE_OPEN_CHANNEL : Nat := 32

/-- Mandatory BOLT 2 v1 payload length (H17's `basePayloadLength`). -/
def PAYLOAD_LEN : Nat := 319

/-! ## 2. Fixed-width big-endian readers -/

/-- Big-endian encoding of `n` into exactly `len` bytes (most significant
first).  It truncates modulo `256^len`, which is the wire reader's domain. -/
def beBytes : Nat → Nat → List UInt8
  | 0, _ => []
  | k + 1, n => ((n / 256 ^ k) % 256).toUInt8 :: beBytes k n

/-- Big-endian value of a byte list. -/
def beNat (l : List UInt8) : Nat :=
  l.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- The two-byte big-endian type/length field. -/
def be16 (a b : UInt8) : Nat := a.toNat * 256 + b.toNat

/-- Read exactly `n` bytes, returning them and the remaining bytes. -/
def readN : Nat → List UInt8 → Option (List UInt8 × List UInt8)
  | 0, l => some ([], l)
  | _ + 1, [] => none
  | n + 1, b :: bs =>
      match readN n bs with
      | some (xs, rest) => some (b :: xs, rest)
      | none => none

/-- Read a big-endian unsigned integer of exactly `n` bytes. -/
def readU (n : Nat) (l : List UInt8) : Option (Nat × List UInt8) :=
  match readN n l with
  | some (xs, rest) => some (beNat xs, rest)
  | none => none

/-- Read one byte. -/
def readByte : List UInt8 → Option (UInt8 × List UInt8)
  | [] => none
  | b :: rest => some (b, rest)

/-- Read a 33-byte compressed public key and check its tag byte.  Only the
structural tag is checked; curve membership is outside the model. -/
def readPoint (l : List UInt8) : Option (List UInt8 × List UInt8) :=
  match readN 33 l with
  | some (xs, rest) =>
      match xs with
      | b :: _ => if b = 0x02 || b = 0x03 then some (xs, rest) else none
      | [] => none
  | none => none

/-! ## 3. Parser -/

/-- Parse the 18 mandatory fields in BOLT 2 wire order.  This function does not
check the total length; `decodePayload` does. -/
def parseOpenChannel (l : List UInt8) : Option OpenChannelMsg := do
  let (chainHash, r1) ← readN 32 l
  let (temporaryChannelId, r2) ← readN 32 r1
  let (fundingSatoshis, r3) ← readU 8 r2
  let (pushMsat, r4) ← readU 8 r3
  let (dustLimitSatoshis, r5) ← readU 8 r4
  let (maxHtlcValueInFlightMsat, r6) ← readU 8 r5
  let (channelReserveSatoshis, r7) ← readU 8 r6
  let (htlcMinimumMsat, r8) ← readU 8 r7
  let (feeratePerKw, r9) ← readU 4 r8
  let (toSelfDelay, r10) ← readU 2 r9
  let (maxAcceptedHtlcs, r11) ← readU 2 r10
  let (fundingPubkey, r12) ← readPoint r11
  let (revocationBasepoint, r13) ← readPoint r12
  let (paymentBasepoint, r14) ← readPoint r13
  let (delayedPaymentBasepoint, r15) ← readPoint r14
  let (htlcBasepoint, r16) ← readPoint r15
  let (firstPerCommitmentPoint, r17) ← readPoint r16
  let (channelFlags, r18) ← readByte r17
  if r18.isEmpty then
    some
      { chainHash := chainHash
        temporaryChannelId := temporaryChannelId
        fundingSatoshis := fundingSatoshis
        pushMsat := pushMsat
        dustLimitSatoshis := dustLimitSatoshis
        maxHtlcValueInFlightMsat := maxHtlcValueInFlightMsat
        channelReserveSatoshis := channelReserveSatoshis
        htlcMinimumMsat := htlcMinimumMsat
        feeratePerKw := feeratePerKw
        toSelfDelay := toSelfDelay
        maxAcceptedHtlcs := maxAcceptedHtlcs
        fundingPubkey := fundingPubkey
        revocationBasepoint := revocationBasepoint
        paymentBasepoint := paymentBasepoint
        delayedPaymentBasepoint := delayedPaymentBasepoint
        htlcBasepoint := htlcBasepoint
        firstPerCommitmentPoint := firstPerCommitmentPoint
        channelFlags := channelFlags }
  else
    none

/-- Decode exactly the mandatory 319-byte `open_channel` payload.  Trailing
bytes (including TLVs) are rejected. -/
def decodePayload (l : List UInt8) : Option OpenChannelMsg :=
  if l.length = PAYLOAD_LEN then parseOpenChannel l else none

/-- Payload-only BOLT 1 abstract frame: `type || length || payload`, where the
length counts the payload only. -/
def decodeFrame : List UInt8 → Option OpenChannelMsg
  | a :: b :: c :: d :: rest =>
      if be16 a b = TYPE_OPEN_CHANNEL then
        if be16 c d = rest.length then decodePayload rest else none
      else none
  | _ => none

/-- Build a payload-only abstract frame. -/
def frameBytes (t : Nat) (payload : List UInt8) : List UInt8 :=
  beBytes 2 t ++ beBytes 2 payload.length ++ payload

/-- Build a BOLT 8 transport frame, whose declared length includes the type.
This is used only to prove that `decodeFrame` is not a transport decoder. -/
def transportFrameBytes (t : Nat) (payload : List UInt8) : List UInt8 :=
  beBytes 2 t ++ beBytes 2 (payload.length + 2) ++ payload

/-! ## 4. Generic rejection theorems -/

/-- **Every payload of the wrong length is rejected.**  This is the exact
truncation/oversize condition. -/
theorem decodePayload_eq_none_of_length_ne {l : List UInt8}
    (h : l.length ≠ PAYLOAD_LEN) : decodePayload l = none := by
  simp [decodePayload, h]

/-- A decoded payload is exactly 319 bytes. -/
theorem decodePayload_some_length {l : List UInt8} {m : OpenChannelMsg}
    (h : decodePayload l = some m) : l.length = PAYLOAD_LEN := by
  by_cases hlen : l.length = PAYLOAD_LEN
  · exact hlen
  · rw [decodePayload_eq_none_of_length_ne hlen] at h
    simp at h

/-- A frame shorter than its four-byte header is rejected. -/
theorem decodeFrame_eq_none_of_length_lt_four {l : List UInt8}
    (h : l.length < 4) : decodeFrame l = none := by
  match l with
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | [_, _, _] => rfl
  | _ :: _ :: _ :: _ :: rest =>
      simp only [List.length_cons] at h
      omega

/-- **Wrong type is rejected.** -/
theorem decodeFrame_eq_none_of_type_ne {a b c d : UInt8} {rest : List UInt8}
    (h : be16 a b ≠ TYPE_OPEN_CHANNEL) :
    decodeFrame (a :: b :: c :: d :: rest) = none := by
  simp [decodeFrame, h]

/-- **A declared-length mismatch is rejected.** -/
theorem decodeFrame_eq_none_of_declared_ne {a b c d : UInt8}
    {rest : List UInt8} (h : be16 c d ≠ rest.length) :
    decodeFrame (a :: b :: c :: d :: rest) = none := by
  simp [decodeFrame, h]

/-- A well-typed frame with a wrong-length payload is rejected. -/
theorem decodeFrame_eq_none_of_payload_length_ne {a b c d : UInt8}
    {rest : List UInt8} (ht : be16 a b = TYPE_OPEN_CHANNEL)
    (hd : be16 c d = rest.length) (hl : rest.length ≠ PAYLOAD_LEN) :
    decodeFrame (a :: b :: c :: d :: rest) = none := by
  simp [decodeFrame, ht, hd, decodePayload, hl]

/-! ## 5. Reproducible concrete vectors -/

/-- 32-byte chain hash filler. -/
def chainHashBytes : List UInt8 := List.replicate 32 0x11

/-- 32-byte temporary channel id filler. -/
def temporaryIdBytes : List UInt8 := List.replicate 32 0x22

/-- A 33-byte point with the given compressed tag and zero body. -/
def pointBytes (tag : UInt8) : List UInt8 := tag :: List.replicate 32 0x44

/-- A fully specified 319-byte payload with the six point tags and the
`channel_flags` byte as parameters. -/
def payloadWith (pf pr pp pd ph p1 : UInt8) (flags : UInt8) : List UInt8 :=
  chainHashBytes ++ temporaryIdBytes ++
  beBytes 8 100000 ++          -- funding_satoshis
  beBytes 8 0 ++               -- push_msat
  beBytes 8 546 ++             -- dust_limit_satoshis
  beBytes 8 1000000000 ++      -- max_htlc_value_in_flight_msat
  beBytes 8 1000 ++            -- channel_reserve_satoshis
  beBytes 8 1 ++               -- htlc_minimum_msat
  beBytes 4 253 ++             -- feerate_per_kw
  beBytes 2 144 ++             -- to_self_delay
  beBytes 2 483 ++             -- max_accepted_htlcs
  pointBytes pf ++ pointBytes pr ++ pointBytes pp ++
  pointBytes pd ++ pointBytes ph ++ pointBytes p1 ++
  [flags]

/-- The canonical test payload: all six tags are `0x02`, flags `0x01`. -/
def samplePayload : List UInt8 := payloadWith 0x02 0x02 0x02 0x02 0x02 0x02 0x01

/-- The message the canonical payload decodes to. -/
def sampleMsg : OpenChannelMsg where
  chainHash := chainHashBytes
  temporaryChannelId := temporaryIdBytes
  fundingSatoshis := 100000
  pushMsat := 0
  dustLimitSatoshis := 546
  maxHtlcValueInFlightMsat := 1000000000
  channelReserveSatoshis := 1000
  htlcMinimumMsat := 1
  feeratePerKw := 253
  toSelfDelay := 144
  maxAcceptedHtlcs := 483
  fundingPubkey := pointBytes 0x02
  revocationBasepoint := pointBytes 0x02
  paymentBasepoint := pointBytes 0x02
  delayedPaymentBasepoint := pointBytes 0x02
  htlcBasepoint := pointBytes 0x02
  firstPerCommitmentPoint := pointBytes 0x02
  channelFlags := 0x01

/-! ### 5.1 Positive controls -/

theorem samplePayload_length : samplePayload.length = PAYLOAD_LEN := by decide

/-- The canonical payload decodes, with every field extracted in order. -/
theorem decodePayload_sample : decodePayload samplePayload = some sampleMsg := by
  decide

/-- The canonical payload framed as type 32 decodes. -/
theorem decodeFrame_sample :
    decodeFrame (frameBytes TYPE_OPEN_CHANNEL samplePayload) = some sampleMsg := by
  decide

/-- Decoder boundary: undefined `channel_flags` bits are accepted (BOLT 2 says
the receiver MUST ignore them). -/
theorem decodePayload_sample_flags_ff :
    decodePayload (payloadWith 0x02 0x02 0x02 0x02 0x02 0x02 0xff) =
      some { sampleMsg with channelFlags := 0xff } := by
  decide

/-! ### 5.2 Payload truncation and oversize -/

theorem decodePayload_empty : decodePayload [] = none := by decide

theorem decodePayload_truncated_31 : decodePayload (samplePayload.take 31) = none := by
  decide

theorem decodePayload_truncated_63 : decodePayload (samplePayload.take 63) = none := by
  decide

theorem decodePayload_truncated_112 : decodePayload (samplePayload.take 112) = none := by
  decide

theorem decodePayload_truncated_118 : decodePayload (samplePayload.take 118) = none := by
  decide

theorem decodePayload_truncated_300 : decodePayload (samplePayload.take 300) = none := by
  decide

theorem decodePayload_truncated_317 : decodePayload (samplePayload.take 317) = none := by
  decide

theorem decodePayload_truncated_318 : decodePayload (samplePayload.take 318) = none := by
  decide

theorem decodePayload_dropLast : decodePayload samplePayload.dropLast = none := by
  decide

theorem decodePayload_oversized_320 :
    decodePayload (samplePayload ++ [0x00]) = none := by
  decide

/-- The exact-length rule also rejects a legitimate optional TLV extension:
this is a declared parser boundary, not a BOLT 2 verdict. -/
theorem decodePayload_tlv_extension :
    decodePayload (samplePayload ++ [0x00, 0x22, 0x00, 0x14] ++
      List.replicate 20 0x55) = none := by
  decide

/-! ### 5.3 Wrong type -/

theorem decodeFrame_wrong_type_0 :
    decodeFrame (frameBytes 0 samplePayload) = none := by decide

theorem decodeFrame_wrong_type_31 :
    decodeFrame (frameBytes 31 samplePayload) = none := by decide

theorem decodeFrame_wrong_type_33 :
    decodeFrame (frameBytes 33 samplePayload) = none := by decide

/-- Type 64 is `open_channel2`; the v1 decoder must not accept it. -/
theorem decodeFrame_wrong_type_64 :
    decodeFrame (frameBytes 64 samplePayload) = none := by decide

theorem decodeFrame_wrong_type_65535 :
    decodeFrame (frameBytes 65535 samplePayload) = none := by decide

/-! ### 5.4 Header truncation and declared-length mismatch -/

theorem decodeFrame_header_empty : decodeFrame [] = none := by decide

theorem decodeFrame_header_one : decodeFrame [0x00] = none := by decide

theorem decodeFrame_header_two : decodeFrame [0x00, 0x20] = none := by decide

theorem decodeFrame_header_three : decodeFrame [0x00, 0x20, 0x01] = none := by decide

/-- Type 32 but the declared length is one byte short of the payload. -/
theorem decodeFrame_declared_318 :
    decodeFrame (beBytes 2 32 ++ beBytes 2 318 ++ samplePayload) = none := by
  decide

/-- Type 32 but the declared length is one byte longer than the payload. -/
theorem decodeFrame_declared_320 :
    decodeFrame (beBytes 2 32 ++ beBytes 2 320 ++ samplePayload) = none := by
  decide

/-- Type 32 and a correct declared length, but only 318 payload bytes. -/
theorem decodeFrame_truncated_payload_318 :
    decodeFrame (beBytes 2 32 ++ beBytes 2 318 ++ samplePayload.take 318) = none := by
  decide

/-- Type 32 and a correct declared length, but one extra payload byte. -/
theorem decodeFrame_oversized_payload_320 :
    decodeFrame (beBytes 2 32 ++ beBytes 2 320 ++ (samplePayload ++ [0x00])) = none := by
  decide

/-- A BOLT 8 transport frame is not a payload-only frame; this concrete vector
is the framing boundary. -/
theorem decodeFrame_transportFrame_sample :
    decodeFrame (transportFrameBytes 32 samplePayload) = none := by
  decide

/-! ### 5.5 Invalid compressed-point tags -/

theorem decodePayload_bad_funding_tag_00 :
    decodePayload (payloadWith 0x00 0x02 0x02 0x02 0x02 0x02 0x01) = none := by
  decide

theorem decodePayload_bad_funding_tag_04 :
    decodePayload (payloadWith 0x04 0x02 0x02 0x02 0x02 0x02 0x01) = none := by
  decide

theorem decodePayload_bad_revocation_tag_ff :
    decodePayload (payloadWith 0x02 0xff 0x02 0x02 0x02 0x02 0x01) = none := by
  decide

theorem decodePayload_bad_htlc_tag_01 :
    decodePayload (payloadWith 0x02 0x02 0x02 0x02 0x01 0x02 0x01) = none := by
  decide

theorem decodePayload_bad_first_point_tag_00 :
    decodePayload (payloadWith 0x02 0x02 0x02 0x02 0x02 0x00 0x01) = none := by
  decide

/-- A valid alternate compressed tag (`0x03`) is accepted. -/
theorem decodePayload_alternate_tag_03 :
    decodePayload (payloadWith 0x03 0x03 0x03 0x03 0x03 0x03 0x00) =
      some { sampleMsg with
        fundingPubkey := pointBytes 0x03
        revocationBasepoint := pointBytes 0x03
        paymentBasepoint := pointBytes 0x03
        delayedPaymentBasepoint := pointBytes 0x03
        htlcBasepoint := pointBytes 0x03
        firstPerCommitmentPoint := pointBytes 0x03
        channelFlags := 0x00 } := by
  decide

/-! ## 6. Axiom audit -/

#print axioms decodePayload_eq_none_of_length_ne
#print axioms decodeFrame_eq_none_of_type_ne
#print axioms decodeFrame_eq_none_of_declared_ne
#print axioms decodePayload_sample
#print axioms decodeFrame_sample
#print axioms decodePayload_truncated_318
#print axioms decodeFrame_wrong_type_33
#print axioms decodePayload_bad_funding_tag_04

end LnLean.Proofs.WaveH.H18
