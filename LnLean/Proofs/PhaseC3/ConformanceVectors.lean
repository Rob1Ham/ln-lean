import LnLean.Proofs.Common

/-!
# LnLean.Proofs.PhaseC3.ConformanceVectors

**English claim of this module.**  A small set of published BOLT wire vectors,
checked against the *existing* executable model by evaluation of the model's
own definitions (never by `decide`/`native_decide`):

* **BOLT 1 BigSize** (Appendix A).  The canonical encodings of
  `0, 1, 0xfc, 0xfd, 0x10000, 0xffffffff` are computed byte-for-byte from
  `Wire.encode`, and `Wire.decode` recovers each value together with the
  number of bytes consumed.
* **BOLT 4 onion packet sizes.**  The packet header fields `1 + 33` plus the
  `hop_payloads` field (1300) plus the HMAC (32) sum to `1366`; a failure
  packet with four bytes of failure data under the model's 256-byte pad
  target is `2 + 4 + (256 - 4) + 32 = 290`.
* **BOLT 11 tagged fields.**  The five-bit tag codes of `p`, `s`, and `n` are
  `1`, `16`, and `19`; their fixed data lengths are 52, 52, and 53 five-bit
  groups; and the tag-code map is injective, so the three codes are distinct.
* **BOLT 1 message framing.**  A concrete `type = 16` message with a
  four-byte payload frames as `00 10 00 04 01 02 03 04` and has length 8.

Every fact below is a named theorem whose proof is `rfl`, `simp` with the
model's proved lemmas, an existing model theorem, or `omega` for arithmetic
side conditions.  There is no `decide`, `native_decide`, placeholder proof, `axiom`,
`admit`, `unsafe`, or `implemented_by`.

The vectors check *the model as written*; they do not claim that the model's
opaque ciphertext, HMAC, or key-derivation behaviour matches a real
implementation.  BOLT 4 cryptographic content remains abstract (see
`LnLean.Routing.Onion`).
-/

namespace LnLean.Proofs.PhaseC3

set_option autoImplicit false

open LnLean

/-! ## BOLT 1: BigSize canonical encodings

BOLT 1 Appendix A test vectors.  The byte lists are the exact output of the
model's `Wire.encode`; the round trips run the model's `Wire.decode`. -/

/-- BigSize `0` encodes as the single byte `00`. -/
theorem bigsize_encode_zero : Wire.bytesToList (Wire.encode 0) = [0x00] := by
  simp [Wire.encode, Wire.oneByte, Wire.bytesToList_toByteArray]

/-- BigSize `1` encodes as the single byte `01`. -/
theorem bigsize_encode_one : Wire.bytesToList (Wire.encode 1) = [0x01] := by
  simp [Wire.encode, Wire.oneByte, Wire.bytesToList_toByteArray]

/-- BigSize `0xfc` (252) still fits the one-byte form and encodes as `fc`. -/
theorem bigsize_encode_fc : Wire.bytesToList (Wire.encode 0xfc) = [0xfc] := by
  simp [Wire.encode, Wire.oneByte, Wire.bytesToList_toByteArray]

/-- BigSize `0xfd` (253) is the first two-byte value: `fd 00 fd`. -/
theorem bigsize_encode_fd :
    Wire.bytesToList (Wire.encode 0xfd) = [0xfd, 0x00, 0xfd] := by
  simp [Wire.encode, Wire.oneByte, Wire.beBytes, Wire.beBytesAux,
    Wire.bytesToList_append, Wire.bytesToList_toByteArray]

/-- BigSize `0x10000` (65536) is the first four-byte value: `fe 00 01 00 00`. -/
theorem bigsize_encode_10000 :
    Wire.bytesToList (Wire.encode 0x10000) = [0xfe, 0x00, 0x01, 0x00, 0x00] := by
  simp [Wire.encode, Wire.oneByte, Wire.beBytes, Wire.beBytesAux,
    Wire.bytesToList_append, Wire.bytesToList_toByteArray]

/-- BigSize `0xffffffff` (4294967295) still uses the four-byte form:
`fe ff ff ff ff`. -/
theorem bigsize_encode_ffffffff :
    Wire.bytesToList (Wire.encode 0xffffffff) = [0xfe, 0xff, 0xff, 0xff, 0xff] := by
  simp [Wire.encode, Wire.oneByte, Wire.beBytes, Wire.beBytesAux,
    Wire.bytesToList_append, Wire.bytesToList_toByteArray]

/-- The canonical encoding sizes at the BOLT 1 boundaries. -/
theorem bigsize_canonical_sizes :
    (Wire.encode 0).size = 1 ∧ (Wire.encode 0xfc).size = 1 ∧
    (Wire.encode 0xfd).size = 3 ∧ (Wire.encode 0x10000).size = 5 ∧
    (Wire.encode 0xffffffff).size = 5 := by
  refine ⟨Wire.encode_size_lt_0xfd 0 (by omega),
    Wire.encode_size_lt_0xfd 0xfc (by omega),
    Wire.encode_size_le_0xffff 0xfd (by omega) (by omega),
    Wire.encode_size_le_0xffffffff 0x10000 (by omega) (by omega),
    Wire.encode_size_le_0xffffffff 0xffffffff (by omega) (by omega)⟩

/-- Decode/encode round trip at `0`. -/
theorem bigsize_roundtrip_zero :
    Wire.decode (Wire.encode 0) = some (0, 1) :=
  Wire.decode_encode_lt_0xfd 0 (by omega)

/-- Decode/encode round trip at `1`. -/
theorem bigsize_roundtrip_one :
    Wire.decode (Wire.encode 1) = some (1, 1) :=
  Wire.decode_encode_lt_0xfd 1 (by omega)

/-- Decode/encode round trip at `0xfc`. -/
theorem bigsize_roundtrip_fc :
    Wire.decode (Wire.encode 0xfc) = some (0xfc, 1) :=
  Wire.decode_encode_lt_0xfd 0xfc (by omega)

/-- Decode/encode round trip at `0xfd` (three bytes consumed). -/
theorem bigsize_roundtrip_fd :
    Wire.decode (Wire.encode 0xfd) = some (0xfd, 3) :=
  Wire.decode_encode_le_ffff 0xfd (by omega) (by omega)

/-- Decode/encode round trip at `0x10000` (five bytes consumed). -/
theorem bigsize_roundtrip_10000 :
    Wire.decode (Wire.encode 0x10000) = some (0x10000, 5) :=
  Wire.decode_encode_le_ffffffff 0x10000 (by omega) (by omega)

/-- Decode/encode round trip at `0xffffffff` (five bytes consumed). -/
theorem bigsize_roundtrip_ffffffff :
    Wire.decode (Wire.encode 0xffffffff) = some (0xffffffff, 5) :=
  Wire.decode_encode_le_ffffffff 0xffffffff (by omega) (by omega)

/-! ## BOLT 4: onion packet and failure-packet sizes -/

/-- The four BOLT 4 packet fields sum to the published 1366-byte size:
`version` 1 + `ephemeral_key` 33 + `hop_payloads` 1300 + `hmac` 32. -/
theorem bolt4_onion_packet_len :
    1 + 33 + Routing.HOP_PAYLOADS_LEN + Routing.ONION_HMAC_LEN = 1366 := by
  simp [Routing.HOP_PAYLOADS_LEN, Routing.ONION_HMAC_LEN]

/-- The model's `OnionPacket.wireSize` evaluates to 1366 bytes for every
packet. -/
theorem bolt4_onion_wire_size (p : Routing.OnionPacket) : p.wireSize = 1366 := by
  simp [Routing.OnionPacket.wireSize, Routing.HOP_PAYLOADS_LEN,
    Routing.ONION_HMAC_LEN]

/-- Four bytes of failure data (representative of a short BOLT 4 error). -/
def failureData : ByteArray := ([0x01, 0x02, 0x03, 0x04] : List UInt8).toByteArray

/-- Four bytes fit under the model's 256-byte failure-message pad target. -/
theorem failureData_fits_pad : failureData.size ≤ Routing.ONION_ERROR_PAD := by
  simp [failureData, List.size_toByteArray, Routing.ONION_ERROR_PAD]

/-- A BOLT 4 failure packet with four bytes of failure data is
`2 + 4 + (256 - 4) + 32 = 290` bytes. -/
theorem bolt4_failure_packet_len :
    Routing.OnionError.packetSize ⟨ErrorCode.invalidOnion, failureData⟩ = 290 := by
  simp [Routing.OnionError.packetSize, Routing.ONION_ERROR_LEN_LEN,
    Routing.ONION_ERROR_PAD, Routing.ONION_ERROR_HMAC_LEN, failureData,
    List.size_toByteArray]

/-! ## BOLT 11: tag codes and fixed data lengths -/

/-- BOLT 11 five-bit tag codes for the mandatory fields: `p = 1`,
`s = 16`, `n = 19`. -/
theorem bolt11_tag_codes :
    Payment.Tag.code .paymentHash = 1 ∧
    Payment.Tag.code .paymentSecret = 16 ∧
    Payment.Tag.code .payeePubKey = 19 := by
  simp [Payment.Tag.code]

/-- BOLT 11 fixed data lengths in five-bit groups: `p = 52`, `s = 52`,
`n = 53`. -/
theorem bolt11_fixed_data_lengths :
    Payment.Tag.fixedDataLength .paymentHash = some 52 ∧
    Payment.Tag.fixedDataLength .paymentSecret = some 52 ∧
    Payment.Tag.fixedDataLength .payeePubKey = some 53 := by
  simp [Payment.Tag.fixedDataLength]

/-- The tag-code map is injective, and concretely the three mandatory codes
are pairwise distinct. -/
theorem bolt11_tag_codes_injective :
    Function.Injective Payment.Tag.code ∧
    Payment.Tag.code .paymentHash ≠ Payment.Tag.code .paymentSecret ∧
    Payment.Tag.code .paymentSecret ≠ Payment.Tag.code .payeePubKey ∧
    Payment.Tag.code .paymentHash ≠ Payment.Tag.code .payeePubKey := by
  refine ⟨Payment.Tag.code_injective, ?_, ?_, ?_⟩
  · intro h
    have heq : Payment.Tag.paymentHash = Payment.Tag.paymentSecret :=
      Payment.Tag.code_injective h
    cases heq
  · intro h
    have heq : Payment.Tag.paymentSecret = Payment.Tag.payeePubKey :=
      Payment.Tag.code_injective h
    cases heq
  · intro h
    have heq : Payment.Tag.paymentHash = Payment.Tag.payeePubKey :=
      Payment.Tag.code_injective h
    cases heq

/-! ## BOLT 1: message-frame length vector -/

/-- A concrete message: type 16 (`init`) with a four-byte payload. -/
def demoMessage : Wire.WireMessage :=
  { type := 16, payload := ([0x01, 0x02, 0x03, 0x04] : List UInt8).toByteArray }

/-- The abstract frame `type || length || payload` is exactly
`00 10 00 04 01 02 03 04`. -/
theorem message_frame_bytes :
    Wire.bytesToList (Wire.frame demoMessage) =
      [0x00, 0x10, 0x00, 0x04, 0x01, 0x02, 0x03, 0x04] := by
  simp [Wire.frame, Wire.u16BE, Wire.beBytes, Wire.beBytesAux,
    Wire.bytesToList_append, Wire.bytesToList_toByteArray, demoMessage,
    List.size_toByteArray]

/-- The framed message has four bytes of type/length overhead plus the
four-byte payload, total 8 bytes. -/
theorem message_frame_size : (Wire.frame demoMessage).size = 8 := by
  rw [Wire.frame_size]
  simp [demoMessage, List.size_toByteArray]

/-- Decoding the frame returns the original message (four payload bytes fit
the two-byte length field). -/
theorem message_frame_roundtrip :
    Wire.unframe (Wire.frame demoMessage) = some demoMessage := by
  apply Wire.unframe_frame
  simp [demoMessage, List.size_toByteArray]

end LnLean.Proofs.PhaseC3
