/-
# H37 — transport / payload-only framing boundaries at 65535/65536 bytes
(CONF-01, CONF-03)

**Catalog issues.**

* `CONF-01` (P2, open for more encodings): the finite conformance suite has
  transport-framing rows at `65532`/`65533`/`65534`/`65535` declared length,
  but the *byte* boundary `65535`/`65536` and the truncation cases were only
  stated as arithmetic (`declaredForPayload`), not as decoder accept/reject
  theorems over payloads.
* `CONF-03` (P2, closed): `LnLean.Wire.Transport` is the promoted BOLT 8
  framing model, while production `LnLean.Wire.unframe` is deliberately the
  payload-only decoder.  The distinction is recorded generically
  (`Transport.unframe_transportFrame_eq_none`); this module makes the
  `65535`/`65536` boundary cases explicit.

## Result of this module

The module keeps **three** different size limits apart and proves the model's
behaviour at each:

1. **Transport framing (`Transport.transportFrame` / `unframeTransport`).**
   The two-byte length field counts the type plus the payload, so a message
   fits iff its payload is at most `65533` bytes.  A `65533`-byte payload has
   declared transport length `65535 = 0xffff` and round-trips; a `65534`-byte
   payload has transport length `65536`, which the fixed-width header cannot
   express (`u16BE 65536 = 00 00`), does **not** fit, and its transport frame
   is rejected by `unframeTransport`.
2. **Payload-only production decoder (`Wire.frame` / `Wire.unframe`).**
   Its second field counts only the payload, so it accepts payloads up to
   `65535` bytes and rejects `65536` bytes — *without* enforcing the BOLT 1/8
   `65535`-byte message limit.  In particular a `65535`-byte payload is
   accepted by `unframe` while it does not fit the transport limit.
3. **The cross-decoder boundary.**  The production `unframe` rejects every
   transport frame, including the maximum legal one (`payload = 65533`,
   declared `0xffff`) and the maximal payload-only one (`payload = 65535`).

Truncation/oversize cases are stated over a raw frame builder
`rawFrame type declared payload`, so no proof forces the kernel to reduce a
65 KiB byte array: all large cases are generic in the payload and use only its
size.  The only concrete byte vectors are small.

**Scope.**  The length header remains the plaintext abstract header; Noise
encryption, the 16-byte MACs, and the message body are not modelled here.
This module adds boundary theorems, not a new transport implementation, and
does not change `LnLean/Wire/Message.lean` (the promoted `Transport` namespace
is imported as-is).  It closes no issue by itself; it supplies the Lean side of
the `CONF-01` framing rows and the explicit `CONF-03` boundary.

## Build

Module-only target: `lake build LnLean.Proofs.WaveH.H37`.  Root import is the
integrator's call.
-/

import LnLean.Wire.Message

namespace LnLean.Proofs.WaveH.H37

set_option autoImplicit false

open LnLean
open LnLean.Wire
open LnLean.Wire.Transport

/-! ## Byte and payload builders -/

/-- Byte-array literal used by the small vectors. -/
def bytes (l : List UInt8) : ByteArray := l.toByteArray

/-- A payload of `n` zero bytes.  Large boundary cases are stated over this
builder so no proof has to reduce a 65 KiB array. -/
def zeros (n : Nat) : ByteArray := (List.replicate n (0 : UInt8)).toByteArray

@[simp] theorem zeros_size (n : Nat) : (zeros n).size = n := by
  simp [zeros, List.size_toByteArray]

/-- The canonical `init`-typed (`type = 16`) message with an `n`-byte payload. -/
def msgOfSize (n : Nat) : WireMessage := ⟨16, zeros n⟩

@[simp] theorem msgOfSize_payload_size (n : Nat) : (msgOfSize n).payload.size = n := by
  simp [msgOfSize]

/-! ## The fixed-width two-byte header truncates at 65536 -/

/-- The maximum value the two-byte header can carry. -/
theorem header_65535 : u16BE 65535 = bytes [0xff, 0xff] := by decide

/-- `65536` is not representable: the fixed-width encoder wraps to `00 00`.
This is exactly why a size check must run before framing. -/
theorem header_65536_truncates : u16BE 65536 = bytes [0x00, 0x00] := by decide

/-- `65537` wraps to `00 01`. -/
theorem header_65537_truncates : u16BE 65537 = bytes [0x00, 0x01] := by decide

/-- Every two-byte big-endian field denotes a value below `65536`; the field
therefore can never *declare* an oversized transport length. -/
theorem u16Nat_lt_65536 (hi lo : UInt8) : u16Nat hi lo < 65536 := by
  unfold u16Nat
  have h1 := UInt8.toNat_lt hi
  have h2 := UInt8.toNat_lt lo
  omega

/-! ## Fits boundary: 65533 payload bytes is the transport maximum -/

/-- The modelled BOLT 1/8 maximum message size (type plus payload) is
`65535`, i.e. the largest value the two-byte transport field can declare. -/
theorem MAX_MESSAGE_SIZE_eq : MAX_MESSAGE_SIZE = 65535 := rfl

/-- The corresponding payload budget is `65533` bytes. -/
theorem MAX_PAYLOAD_SIZE_eq : MAX_PAYLOAD_SIZE = 65533 := rfl

/-- Any payload of at most `65533` bytes fits the BOLT 1/8 message limit. -/
theorem fits_of_payload_le (m : WireMessage) (h : m.payload.size ≤ 65533) :
    m.fits :=
  (Transport.fits_iff_payload m).mpr h

/-- No payload of `65534` or more bytes fits the transport limit. -/
theorem not_fits_of_payload_ge (m : WireMessage) (h : 65534 ≤ m.payload.size) :
    ¬ m.fits := by
  intro hf
  have hp : m.payload.size ≤ 65533 := (Transport.fits_iff_payload m).mp hf
  omega

/-- Transport length arithmetic at the four boundary payload sizes. -/
theorem transportLength_65533 : transportLength (msgOfSize 65533) = 65535 := by
  rw [Transport.transportLength]
  rw [msgOfSize_payload_size]

theorem transportLength_65534 : transportLength (msgOfSize 65534) = 65536 := by
  rw [Transport.transportLength]
  rw [msgOfSize_payload_size]

theorem transportLength_65535 : transportLength (msgOfSize 65535) = 65537 := by
  rw [Transport.transportLength]
  rw [msgOfSize_payload_size]

theorem transportLength_65536 : transportLength (msgOfSize 65536) = 65538 := by
  rw [Transport.transportLength]
  rw [msgOfSize_payload_size]

theorem msgOfSize_65533_fits : (msgOfSize 65533).fits := by
  apply fits_of_payload_le
  simp

theorem msgOfSize_65534_not_fits : ¬ (msgOfSize 65534).fits := by
  apply not_fits_of_payload_ge
  simp

theorem msgOfSize_65535_not_fits : ¬ (msgOfSize 65535).fits := by
  apply not_fits_of_payload_ge
  simp

theorem msgOfSize_65536_not_fits : ¬ (msgOfSize 65536).fits := by
  apply not_fits_of_payload_ge
  simp

/-! ## Transport framing at the maximum legal length -/

/-- At a `65533`-byte payload the transport header is literally `ff ff`. -/
theorem transportFrame_65533_header (m : WireMessage) (h : m.payload.size = 65533) :
    transportFrame m = u16BE m.type.toNat ++ bytes [0xff, 0xff] ++ m.payload := by
  rw [Transport.transportFrame_header_eq, h, header_65535]

/-- At a `65534`-byte payload the transport header silently truncates to
`00 00`, i.e. the written header no longer declares the intended length. -/
theorem transportFrame_65534_header (m : WireMessage) (h : m.payload.size = 65534) :
    transportFrame m = u16BE m.type.toNat ++ bytes [0x00, 0x00] ++ m.payload := by
  rw [Transport.transportFrame_header_eq, h]
  have hsum : 65534 + 2 = 65536 := by decide
  rw [hsum, header_65536_truncates]

/-- The maximum legal transport frame decodes. -/
theorem unframeTransport_transportFrame_65533 (m : WireMessage)
    (h : m.payload.size = 65533) :
    unframeTransport (transportFrame m) = some m := by
  apply Transport.unframeTransport_transportFrame
  omega

/-- The maximum legal transport frame declares exactly `65535`. -/
theorem declaredTransportLength_65533 (m : WireMessage)
    (h : m.payload.size = 65533) :
    Transport.declaredTransportLength? (transportFrame m) = some 65535 := by
  have hrt := unframeTransport_transportFrame_65533 m h
  have hdec := Transport.decode_transport_length (transportFrame m) m hrt
  rw [hdec.1]
  have hms : m.messageSize = 65535 := by
    unfold WireMessage.messageSize
    omega
  rw [hms]

/-- **Oversized payloads are rejected by the transport decoder.**  When the
payload is at least `65534` bytes the intended transport length is at least
`65536`; the header wraps modulo `2^16` and the decoder's consistency check
`declared = payload.size + 2` can no longer hold. -/
theorem unframeTransport_transportFrame_oversized (m : WireMessage)
    (h : 65534 ≤ m.payload.size) :
    unframeTransport (transportFrame m) = none := by
  unfold unframeTransport
  rw [transportFrame, lengthHeader, bytesToList_append, bytesToList_append]
  rw [bytesToList_u16BE m.type.toNat (MessageType.toNat_lt m.type)]
  rw [bytesToList_u16BE_mod (transportLength m)]
  simp only [List.cons_append, List.nil_append, unframeTransportList]
  rw [bytesToList_length]
  rw [u16Nat_u16BE_mod (transportLength m)]
  have hne : ¬ ((transportLength m) % 65536 = m.payload.size + 2) := by
    unfold Transport.transportLength
    intro heq
    have hle : 65536 ≤ 2 + m.payload.size := by omega
    have hlt : (2 + m.payload.size) % 65536 < 65536 :=
      Nat.mod_lt _ (by decide : 0 < 65536)
    omega
  rw [ite_eq_right hne]

theorem unframeTransport_65534 :
    unframeTransport (transportFrame (msgOfSize 65534)) = none := by
  apply unframeTransport_transportFrame_oversized
  simp

theorem unframeTransport_65535 :
    unframeTransport (transportFrame (msgOfSize 65535)) = none := by
  apply unframeTransport_transportFrame_oversized
  simp

theorem unframeTransport_65536 :
    unframeTransport (transportFrame (msgOfSize 65536)) = none := by
  apply unframeTransport_transportFrame_oversized
  simp

/-! ## The payload-only production decoder boundary -/

/-- **Payload-only decoder at its own maximum.**  `Wire.frame` stores the
payload length, not the message length, so a `65535`-byte payload still fits
the two-byte field and `Wire.unframe` accepts it.  This is *not* a conformance
claim: the message does not fit the BOLT 1/8 limit. -/
theorem unframe_frame_65535 (m : WireMessage) (h : m.payload.size = 65535) :
    unframe (frame m) = some m := by
  apply Wire.unframe_frame
  omega

/-- **Payload-only decoder rejects 65536 payload bytes.**  The payload length no
longer fits the two-byte field, so the truncated declared value cannot equal
the actual payload length. -/
theorem unframe_frame_eq_none_of_payload_ge (m : WireMessage)
    (h : 65536 ≤ m.payload.size) : unframe (frame m) = none := by
  unfold unframe
  rw [frame, bytesToList_append, bytesToList_append]
  rw [bytesToList_u16BE m.type.toNat (MessageType.toNat_lt m.type)]
  rw [bytesToList_u16BE_mod m.payload.size]
  simp only [List.cons_append, List.nil_append, unframeList]
  rw [bytesToList_length]
  rw [u16Nat_u16BE_mod m.payload.size]
  have hne : ¬ (m.payload.size = m.payload.size % 65536) := by
    intro heq
    have hlt : m.payload.size % 65536 < 65536 :=
      Nat.mod_lt _ (by decide : 0 < 65536)
    omega
  rw [ite_eq_right hne]

theorem unframe_frame_65536 :
    unframe (frame (msgOfSize 65536)) = none := by
  apply unframe_frame_eq_none_of_payload_ge
  simp

/-- The production decoder rejects the maximum *legal* transport frame, whose
declared field is `65535` but whose payload is `65533` bytes. -/
theorem production_decoder_rejects_max_transport (m : WireMessage)
    (_h : m.payload.size = 65533) : unframe (transportFrame m) = none :=
  Transport.unframe_transportFrame_eq_none m

/-- **The two conventions disagree at the top of the payload range.**  For a
`65535`-byte payload the payload-only frame decodes, the transport frame is
rejected by the production decoder, and the message does not fit the transport
limit.  The three facts together are the explicit `CONF-03` boundary. -/
theorem payload_65535_decoder_split (m : WireMessage)
    (h : m.payload.size = 65535) :
    unframe (frame m) = some m ∧
      unframe (transportFrame m) = none ∧
      ¬ m.fits := by
  refine ⟨unframe_frame_65535 m h, Transport.unframe_transportFrame_eq_none m, ?_⟩
  apply not_fits_of_payload_ge
  omega

/-! ## Raw frames: declared-length truncation and mismatch -/

/-- A raw frame with an arbitrary declared length.  The same bytes are read as
a payload length by `Wire.unframe` and as a whole-message length by
`Transport.unframeTransport`. -/
def rawFrame (ty : MessageType) (declared : Nat) (payload : ByteArray) : ByteArray :=
  u16BE ty.toNat ++ u16BE declared ++ payload

/-- **Transport decoder mismatch.**  A raw transport frame whose declared
length (representable, `< 65536`) differs from `payload.size + 2` is rejected. -/
theorem unframeTransport_rawFrame_eq_none (ty : MessageType) (declared : Nat)
    (payload : ByteArray) (hdecl : declared < 65536)
    (h : declared ≠ payload.size + 2) :
    unframeTransport (rawFrame ty declared payload) = none := by
  unfold unframeTransport rawFrame
  rw [bytesToList_append, bytesToList_append]
  rw [bytesToList_u16BE ty.toNat (MessageType.toNat_lt ty)]
  rw [bytesToList_u16BE declared hdecl]
  simp only [List.cons_append, List.nil_append, unframeTransportList]
  rw [bytesToList_length]
  rw [u16Nat_roundtrip declared hdecl]
  rw [ite_eq_right h]

/-- **Payload-only decoder mismatch.**  A raw model frame whose payload length
differs from the declared field is rejected. -/
theorem unframe_rawFrame_eq_none (ty : MessageType) (declared : Nat)
    (payload : ByteArray) (hdecl : declared < 65536)
    (h : payload.size ≠ declared) :
    unframe (rawFrame ty declared payload) = none := by
  unfold unframe rawFrame
  rw [bytesToList_append, bytesToList_append]
  rw [bytesToList_u16BE ty.toNat (MessageType.toNat_lt ty)]
  rw [bytesToList_u16BE declared hdecl]
  simp only [List.cons_append, List.nil_append, unframeList]
  rw [bytesToList_length]
  rw [u16Nat_roundtrip declared hdecl]
  rw [ite_eq_right h]

/-- A raw transport frame with the maximum declared length `65535` and a
one-byte-short payload (`65532`) is rejected. -/
theorem declared_65535_truncated_one (p : ByteArray) (h : p.size = 65532) :
    unframeTransport (rawFrame 16 65535 p) = none := by
  apply unframeTransport_rawFrame_eq_none
  · decide
  · omega

/-- A raw transport frame with the maximum declared length `65535` and a
one-byte-long payload (`65534`) is rejected as a trailing byte. -/
theorem declared_65535_trailing_one (p : ByteArray) (h : p.size = 65534) :
    unframeTransport (rawFrame 16 65535 p) = none := by
  apply unframeTransport_rawFrame_eq_none
  · decide
  · omega

/-- A raw transport frame with the maximum declared length and an empty body is
rejected. -/
theorem declared_65535_empty (p : ByteArray) (h : p.size = 0) :
    unframeTransport (rawFrame 16 65535 p) = none := by
  apply unframeTransport_rawFrame_eq_none
  · decide
  · omega

/-- The largest representable declared value (`65535`) with a payload of
`65533` bytes is exactly the maximum legal transport frame and decodes. -/
theorem declared_65535_accepts (ty : MessageType) (p : ByteArray)
    (h : p.size = 65533) :
    unframeTransport (rawFrame ty 65535 p) = some ⟨ty, p⟩ := by
  unfold unframeTransport rawFrame
  rw [bytesToList_append, bytesToList_append]
  rw [bytesToList_u16BE ty.toNat (MessageType.toNat_lt ty)]
  rw [bytesToList_u16BE 65535 (by decide)]
  simp only [List.cons_append, List.nil_append, unframeTransportList]
  rw [bytesToList_length, u16Nat_roundtrip 65535 (by decide), h]
  simp only [ite_true]
  rw [u16FromBytes_roundtrip ty.toNat (MessageType.toNat_lt ty),
    toByteArray_bytesToList]
  simp only [UInt16.ofNat_toNat]

/-- The intended declared value `65536` is not representable: it is written as
`00 00`.  Consequently the raw transport frame for a `65534`-byte payload,
*even if a caller asks for declared `65536`*, is rejected. -/
theorem declared_65536_truncates_and_rejects (p : ByteArray) (h : p.size = 65534) :
    unframeTransport (rawFrame 16 65536 p) = none := by
  have hsame : rawFrame 16 65536 p = rawFrame 16 0 p := by
    unfold rawFrame
    rw [header_65536_truncates]
    have hzero : u16BE 0 = bytes [0x00, 0x00] := by decide
    rw [hzero]
  rw [hsame]
  apply unframeTransport_rawFrame_eq_none
  · decide
  · omega

/-- The payload-only decoder rejects a raw frame whose declared field is
`65535` but whose payload is `65536` bytes: the declared length is smaller than
the actual payload. -/
theorem payload_decoder_65536_payload_declared_65535 (p : ByteArray)
    (h : p.size = 65536) :
    unframe (rawFrame 16 65535 p) = none := by
  apply unframe_rawFrame_eq_none
  · decide
  · omega

/-- The payload-only decoder rejects the raw frame that would be needed for a
`65536`-byte payload: declared `65536` truncates to `00 00`, so the decoded
declared length is `0`, not `65536`. -/
theorem payload_decoder_65536_payload_declared_65536 (p : ByteArray)
    (h : p.size = 65536) :
    unframe (rawFrame 16 65536 p) = none := by
  have hsame : rawFrame 16 65536 p = rawFrame 16 0 p := by
    unfold rawFrame
    rw [header_65536_truncates]
    have hzero : u16BE 0 = bytes [0x00, 0x00] := by decide
    rw [hzero]
  rw [hsame]
  apply unframe_rawFrame_eq_none
  · decide
  · omega

/-! ## Small concrete vectors (declared `0xffff` truncation) -/

/-- Declared `0xffff` with no payload: the transport decoder rejects the
truncated body. -/
theorem vector_transport_max_declared_empty :
    unframeTransport (bytes [0x00, 0x10, 0xff, 0xff]) = none := by decide

/-- Declared `0xffff` with a two-byte payload: rejected (body is `65531` bytes
short of the maximum frame). -/
theorem vector_transport_max_declared_short :
    unframeTransport (bytes [0x00, 0x10, 0xff, 0xff, 0xaa, 0xbb]) = none := by
  decide

/-- Declared `0x0000` with a one-byte payload: rejected, showing the truncation
of an intended `65536` declares zero rather than `65536`. -/
theorem vector_transport_zero_declared_trailing :
    unframeTransport (bytes [0x00, 0x10, 0x00, 0x00, 0xaa]) = none := by decide

/-- The payload-only decoder accepts the raw *model* frame declaring a
`65535`-byte payload even though the transport limit is `65533`.  This small
statement only checks the header arithmetic; the payload itself is symbolic. -/
theorem vector_model_max_declared_empty :
    unframe (bytes [0x00, 0x10, 0xff, 0xff]) = none := by decide

/-! ## Boundary table -/

/-- The complete `65533`/`65534`/`65535`/`65536` boundary table for a type-16
message: exactly one of the four payload sizes fits transport framing, the
transport decoder accepts only `65533`, and the payload-only decoder accepts
both `65533` and `65535` but rejects `65536`. -/
theorem boundary_table :
    (msgOfSize 65533).fits ∧
      ¬ (msgOfSize 65534).fits ∧
      ¬ (msgOfSize 65535).fits ∧
      ¬ (msgOfSize 65536).fits ∧
      unframeTransport (transportFrame (msgOfSize 65533)) =
        some (msgOfSize 65533) ∧
      unframeTransport (transportFrame (msgOfSize 65534)) = none ∧
      unframeTransport (transportFrame (msgOfSize 65535)) = none ∧
      unframe (frame (msgOfSize 65533)) = some (msgOfSize 65533) ∧
      unframe (frame (msgOfSize 65535)) = some (msgOfSize 65535) ∧
      unframe (frame (msgOfSize 65536)) = none := by
  refine ⟨msgOfSize_65533_fits, msgOfSize_65534_not_fits,
    msgOfSize_65535_not_fits, msgOfSize_65536_not_fits, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply unframeTransport_transportFrame_65533
    simp
  · exact unframeTransport_65534
  · exact unframeTransport_65535
  · apply Wire.unframe_frame
    simp
  · apply unframe_frame_65535
    simp
  · exact unframe_frame_65536

end LnLean.Proofs.WaveH.H37
