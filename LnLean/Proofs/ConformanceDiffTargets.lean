/-
# Transport-framing and pinned rust-lightning differential targets

**What this module is.**  Concrete, machine-checked expectations for the BOLT 8
transport frame that wraps a BOLT 1 Lightning message, plus the differential
fixtures in `tests/conformance/rust-lightning/fixtures.json`.  Small framing
vectors are closed by kernel reduction (`decide`); the large boundary facts use
the model's proved length lemmas.

**The framing reconciliation (important).**  Two different two-byte fields are
easy to confuse:

* `LnLean.Wire.frame` is the *model's abstract payload-only frame*:
  `type || payload.size || payload`.  Its second field is the payload length.
* The BOLT 8 transport length is the size of the **whole Lightning message**,
  i.e. `type` plus `payload`.  BOLT 8 §Lightning Message Specification says:
  "Each message is prefixed with another AEAD ciphertext, which encodes the
  total length of the following Lightning message"; rust-lightning computes
  exactly `msgbuf.len() - 16 - 2` after the 18-byte length/MAC reservation
  (`lightning/src/ln/peer_channel_encryptor.rs:518-540`) and bounds it by
  `LN_MAX_MSG_LEN = u16::MAX` (`:36`).  The concrete transport frame is
  therefore `type || (2 + payload.size) || payload`.

Consequently `Wire.unframe` (which expects the declared value to equal the
payload length) **must not** be used as a transport decoder: its length check
is two bytes too small for this convention, and the concrete theorem
`payload_decoder_rejects_transport_frame` below is the witness.  The
`Transport` namespace below is an explicitly separate conformance reference
decoder for the transport convention.  It is not wired
into the production `LnLean.Wire` model; that gap is recorded in the report.

**Vectors.**  `tests/conformance/vectors.json` (`framing` object) holds the
small valid frames, malformed/truncated frames, and the length-boundary table.
`tests/conformance/rust-lightning/fixtures.json` holds fixtures transcribed from
the pinned rust-lightning unit test `bigsize_encoding_decoding`
(`lightning/src/util/ser.rs:1857-1901`), the TLV reader test
`retired_tlvs_skipped_on_read` (`lightning/src/util/ser_macros.rs:2047-2071`),
and the wire length header described above.  The runner is offline: it reads
only committed JSON and this module's source, never the network or a Rust
toolchain.

**Scope.**  This is vector/differential conformance, not a full implementation
test.  It does not model Noise encryption, the 16-byte MACs, message dispatch,
or any message body.  The length header here is plaintext, exactly as in the
model's abstract frame.

**Build.**  Module-only target:
`lake build LnLean.Proofs.ConformanceDiffTargets`.  Root import is left to the
integrator (`LnLean.lean` is outside this lane's ownership).
-/

import LnLean.Wire.Message
import LnLean.Wire.TLV
import LnLean.Proofs.Wire.TLVTargets

namespace LnLean.Proofs.Conformance.Diff

set_option autoImplicit false

open LnLean
open LnLean.Wire

/-- Byte-array literal used by the vector statements. -/
def bytes (l : List UInt8) : ByteArray := l.toByteArray

/-- The transport length as a function of the payload size.  This is the
arithmetic half of `Transport.transportLength`, extracted so the large boundary
facts do not require reducing a 65K-byte array. -/
def declaredForPayload (payloadSize : Nat) : Nat := 2 + payloadSize

/-! ## The transport frame -/

namespace Transport

/-- The BOLT 8 transport length: the total Lightning message size, i.e. the
two-byte type plus the payload.  This is **not** the payload length. -/
def transportLength (m : WireMessage) : Nat := 2 + m.payload.size

/-- The transport length is definitionally the model's `messageSize`. -/
theorem transportLength_eq_messageSize (m : WireMessage) :
    transportLength m = m.messageSize := rfl

/-- The two-byte big-endian length header of a transport frame. -/
def lengthHeader (m : WireMessage) : ByteArray := u16BE (transportLength m)

/-- The concrete BOLT 8 transport frame: `type || transportLength || payload`.
The `length` field counts the type bytes and the payload, unlike
`LnLean.Wire.frame`. -/
def transportFrame (m : WireMessage) : ByteArray :=
  u16BE m.type.toNat ++ lengthHeader m ++ m.payload

/-- The transport header is exactly the payload length plus two. -/
theorem transportFrame_header_eq (m : WireMessage) :
    transportFrame m =
      u16BE m.type.toNat ++ u16BE (m.payload.size + 2) ++ m.payload := by
  simp [transportFrame, lengthHeader, transportLength, Nat.add_comm]

/-- The transport frame has two type bytes, two length bytes, and the payload. -/
theorem transportFrame_size (m : WireMessage) :
    (transportFrame m).size = 4 + m.payload.size := by
  simp [transportFrame, lengthHeader, u16BE, beBytes_size, ByteArray.size_append]

/-- Frame size in terms of the model's message size. -/
theorem transportFrame_size_eq (m : WireMessage) :
    (transportFrame m).size = m.messageSize + 2 := by
  rw [transportFrame_size]
  unfold WireMessage.messageSize
  omega

/-- A message fits the BOLT 8 limit exactly when its transport length fits in
the two-byte header. -/
theorem fits_iff_transportLength (m : WireMessage) :
    m.fits ↔ transportLength m ≤ MAX_MESSAGE_SIZE := by
  unfold WireMessage.fits WireMessage.messageSize transportLength MAX_MESSAGE_SIZE
  omega

/-- The payload budget is 65533 bytes once the two type bytes are counted. -/
theorem fits_iff_payload (m : WireMessage) :
    m.fits ↔ m.payload.size ≤ 65533 := by
  simpa [MAX_PAYLOAD_SIZE] using Wire.fits_payload_iff m

/-- The two conventions are observably different on a concrete message: the
model frame's second field is `00 04`, the transport frame's is `00 06`. -/
theorem transportFrame_differs_from_model_frame :
    Transport.transportFrame ⟨16, bytes [0x01, 0x02, 0x03, 0x04]⟩ ≠
      Wire.frame ⟨16, bytes [0x01, 0x02, 0x03, 0x04]⟩ := by
  decide

end Transport

open Transport

/-! ## A transport decoder (conformance reference only) -/

/-- Parse a single BOLT 8 transport frame `type || length || payload`.  The
declared length must equal `2 + payload.size`; trailing bytes and short
payloads are rejected, so the decoder is length-total for one frame. -/
def unframeTransportList : List UInt8 → Option WireMessage
  | a :: b :: c :: d :: rest =>
      if u16Nat c d = rest.length + 2 then
        some ⟨u16FromBytes a b, rest.toByteArray⟩
      else none
  | _ => none

/-- Decode one abstract BOLT 8 transport frame. -/
def unframeTransport (b : ByteArray) : Option WireMessage :=
  unframeTransportList (bytesToList b)

/-- The declared transport length, read from the two-byte big-endian field.
Returns `none` when the input is shorter than the four-byte header. -/
def declaredTransportLength? (b : ByteArray) : Option Nat :=
  match bytesToList b with
  | _ :: _ :: c :: d :: _ => some (u16Nat c d)
  | _ => none

/-- Inversion for the transport decoder. -/
theorem unframeTransportList_eq_some_iff (l : List UInt8) (m : WireMessage) :
    unframeTransportList l = some m ↔
      ∃ a b c d rest, l = a :: b :: c :: d :: rest ∧
        u16Nat c d = rest.length + 2 ∧
        m = ⟨u16FromBytes a b, rest.toByteArray⟩ := by
  constructor
  · intro h
    cases l with
    | nil => simp [unframeTransportList] at h
    | cons a l1 =>
      cases l1 with
      | nil => simp [unframeTransportList] at h
      | cons b l2 =>
        cases l2 with
        | nil => simp [unframeTransportList] at h
        | cons c l3 =>
          cases l3 with
          | nil => simp [unframeTransportList] at h
          | cons d rest =>
            simp only [unframeTransportList] at h
            by_cases hlen : u16Nat c d = rest.length + 2
            · rw [ite_eq_left hlen] at h
              simp only [Option.some.injEq] at h
              exact ⟨a, b, c, d, rest, rfl, hlen, h.symm⟩
            · rw [ite_eq_right hlen] at h
              simp at h
  · rintro ⟨a, b, c, d, rest, rfl, hlen, rfl⟩
    simp [unframeTransportList, hlen]

/-- **Transport frame/unframe round trip.**  For a payload that leaves room for
the two type bytes in a two-byte length field, decoding the transport frame
returns the original message. -/
theorem unframeTransport_transportFrame (m : WireMessage)
    (h : m.payload.size < 65534) : unframeTransport (transportFrame m) = some m := by
  have ht : m.type.toNat < 65536 := MessageType.toNat_lt m.type
  have hlen : transportLength m < 65536 := by
    unfold transportLength
    omega
  unfold unframeTransport
  rw [transportFrame, lengthHeader, bytesToList_append, bytesToList_append]
  rw [bytesToList_u16BE m.type.toNat ht]
  rw [bytesToList_u16BE (transportLength m) hlen]
  simp only [List.cons_append, List.nil_append, unframeTransportList]
  rw [bytesToList_length, u16Nat_roundtrip (transportLength m) hlen]
  have hdecl : transportLength m = m.payload.size + 2 := by
    unfold transportLength
    omega
  rw [hdecl]
  simp only [ite_true]
  rw [u16FromBytes_roundtrip m.type.toNat ht, toByteArray_bytesToList]
  simp only [UInt16.ofNat_toNat]

/-- A message that satisfies the BOLT 1/8 size limit round-trips through the
transport frame. -/
theorem unframeTransport_transportFrame_of_fits (m : WireMessage) (h : m.fits) :
    unframeTransport (transportFrame m) = some m := by
  apply unframeTransport_transportFrame
  have hp : m.payload.size ≤ 65533 := (Transport.fits_iff_payload m).mp h
  omega

/-- **Declared transport length law.**  On every successful transport decode:
the declared length is the whole-message size, the payload is exactly the tail
after the four-byte header, and the frame accounts for every input byte. -/
theorem decode_transport_length (b : ByteArray) (m : WireMessage)
    (h : unframeTransport b = some m) :
    declaredTransportLength? b = some m.messageSize ∧
      (bytesToList b).drop 4 = bytesToList m.payload ∧
      b.size = 4 + m.payload.size := by
  have hlist : unframeTransportList (bytesToList b) = some m := by
    simpa [unframeTransport] using h
  rcases (unframeTransportList_eq_some_iff _ _).mp hlist with
    ⟨a, bty, c, d, rest, hb, hlen, hm⟩
  subst hm
  have hdrop : (bytesToList b).drop 4 = rest := by
    rw [hb]
    simp
  refine ⟨?_, ?_, ?_⟩
  · unfold declaredTransportLength? WireMessage.messageSize
    rw [hb]
    simp [hlen, List.size_toByteArray]
    omega
  · rw [hdrop, bytesToList_toByteArray]
  · have hb_size : b.size = (bytesToList b).length := (bytesToList_length b).symm
    rw [hb_size, hb]
    simp only [List.length_cons]
    rw [List.size_toByteArray]
    omega

/-! ## The model's payload-only decoder is not a transport decoder -/

/-- The model's `Wire.unframe` reads the second field as the payload length, so
it rejects the BOLT 8 transport frame even for a small valid message.  This is
the exact decoder gap that the `Transport` namespace repairs for conformance. -/
theorem payload_decoder_rejects_transport_frame :
    Wire.unframe
        (Transport.transportFrame
          ⟨16, bytes [0x01, 0x02, 0x03, 0x04]⟩) = none := by
  decide

/-- The payload-only model frame still decodes as documented; only the length
convention differs from the transport frame. -/
theorem payload_decoder_accepts_model_frame :
    Wire.unframe
        (Wire.frame ⟨16, bytes [0x01, 0x02, 0x03, 0x04]⟩) =
      some ⟨16, bytes [0x01, 0x02, 0x03, 0x04]⟩ := by
  apply Wire.unframe_frame
  simp [bytes, List.size_toByteArray]

/-! ## Concrete transport-framing vectors -/

/-- `init` (`type = 16`) with an empty payload: transport length `2`,
frame `00 10 00 02`. -/
theorem frame_init_empty :
    Transport.transportFrame ⟨16, bytes []⟩ = bytes [0x00, 0x10, 0x00, 0x02] := by
  decide

/-- `init` with a four-byte payload: transport length `6`, frame
`00 10 00 06 01 02 03 04`.  Compare the model's payload-only frame
`00 10 00 04 01 02 03 04`. -/
theorem frame_init_four :
    Transport.transportFrame ⟨16, bytes [0x01, 0x02, 0x03, 0x04]⟩ =
      bytes [0x00, 0x10, 0x00, 0x06, 0x01, 0x02, 0x03, 0x04] := by
  decide

/-- The last commitment-group type (`255`) with a one-byte payload. -/
theorem frame_type_255 :
    Transport.transportFrame ⟨255, bytes [0xff]⟩ =
      bytes [0x00, 0xff, 0x00, 0x03, 0xff] := by
  decide

/-- The first routing-group type (`256`) with an empty payload. -/
theorem frame_type_256 :
    Transport.transportFrame ⟨256, bytes []⟩ =
      bytes [0x01, 0x00, 0x00, 0x02] := by
  decide

/-- The largest custom type (`65535`) with a one-byte payload. -/
theorem frame_type_custom_65535 :
    Transport.transportFrame ⟨65535, bytes [0x2a]⟩ =
      bytes [0xff, 0xff, 0x00, 0x03, 0x2a] := by
  decide

/-- A type-0 control message with a two-byte payload. -/
theorem frame_type_zero :
    Transport.transportFrame ⟨0, bytes [0xaa, 0xbb]⟩ =
      bytes [0x00, 0x00, 0x00, 0x04, 0xaa, 0xbb] := by
  decide

/-! ## Truncated and malformed transport frames -/

theorem frame_reject_empty : unframeTransport (bytes []) = none := by decide

theorem frame_reject_short_header :
    unframeTransport (bytes [0x00, 0x10, 0x00]) = none := by decide

theorem frame_reject_length_zero :
    unframeTransport (bytes [0x00, 0x10, 0x00, 0x00]) = none := by decide

theorem frame_reject_length_one :
    unframeTransport (bytes [0x00, 0x10, 0x00, 0x01]) = none := by decide

theorem frame_reject_truncated_payload :
    unframeTransport (bytes [0x00, 0x10, 0x00, 0x03]) = none := by decide

theorem frame_reject_truncated_payload_short :
    unframeTransport (bytes [0x00, 0x10, 0x00, 0x04, 0xaa]) = none := by decide

theorem frame_reject_trailing_byte :
    unframeTransport (bytes [0x00, 0x10, 0x00, 0x02, 0xaa]) = none := by decide

theorem frame_reject_trailing_two_bytes :
    unframeTransport (bytes [0x00, 0x10, 0x00, 0x03, 0xaa, 0xbb]) = none := by decide

theorem frame_reject_max_length_truncated :
    unframeTransport (bytes [0x00, 0x10, 0xff, 0xff]) = none := by decide

theorem frame_reject_zero_type_zero_length :
    unframeTransport (bytes [0x00, 0x00, 0x00, 0x00]) = none := by decide

/-! ## Length boundaries -/

/-- The transport length is exactly `declaredForPayload` of the payload size. -/
theorem transportLength_eq_declaredForPayload (m : WireMessage) :
    Transport.transportLength m = declaredForPayload m.payload.size := rfl

/-- The transport length of a zero-byte payload is `2`. -/
theorem boundary_declared_0 : declaredForPayload 0 = 2 := by decide

/-- The transport length of a one-byte payload is `3`. -/
theorem boundary_declared_1 : declaredForPayload 1 = 3 := by decide

/-- The last one-byte-BigSize payload length (`252`) gives transport length
`254`, still the `0x00fe` two-byte header. -/
theorem boundary_declared_252 : declaredForPayload 252 = 254 := by decide

/-- A `253`-byte payload crosses the BigSize-style `0xfd` boundary, but the
transport header is a fixed two-byte field: transport length `255 = 0x00ff`. -/
theorem boundary_declared_253 : declaredForPayload 253 = 255 := by decide

/-- A 256-byte payload gives transport length `258 = 0x0102`. -/
theorem boundary_declared_256 : declaredForPayload 256 = 258 := by decide

/-- The largest payload that leaves the transport length at `65534 = 0xfffe`. -/
theorem boundary_declared_65532 : declaredForPayload 65532 = 65534 := by decide

/-- The maximum legal transport length `65535 = 0xffff` (payload `65533`). -/
theorem boundary_declared_65533 : declaredForPayload 65533 = 65535 := by decide

/-- One byte over the limit: transport length `65536`, which does **not** fit
the two-byte header.  An encoder must reject the message before framing. -/
theorem boundary_declared_65534 : declaredForPayload 65534 = 65536 := by decide

/-- Two bytes over the limit: `65537 = 0x10001`, which would truncate to
`0x0001` in the fixed header. -/
theorem boundary_declared_65535 : declaredForPayload 65535 = 65537 := by decide

/-- Every message with a `65533`-byte payload fits the transport limit. -/
theorem boundary_fits_65533 (m : WireMessage) (h : m.payload.size = 65533) :
    m.fits := by
  rw [Transport.fits_iff_transportLength]
  unfold Transport.transportLength MAX_MESSAGE_SIZE
  omega

/-- No message with a `65534`-byte payload fits the transport limit. -/
theorem boundary_not_fits_65534 (m : WireMessage) (h : m.payload.size = 65534) :
    ¬ m.fits := by
  rw [Transport.fits_iff_transportLength]
  unfold Transport.transportLength MAX_MESSAGE_SIZE
  omega

/-- The two-byte big-endian header for the maximum transport length. -/
theorem header_65535 : u16BE 65535 = bytes [0xff, 0xff] := by decide

/-- `u16BE` is a truncating fixed-width encoding: `65536` wraps to `00 00`.
This is why the size check must happen before the header is written. -/
theorem header_65536_truncates : u16BE 65536 = bytes [0x00, 0x00] := by decide

/-- A frame carrying the maximum legal transport length decodes.  The proof is
generic in the payload and uses only its size, so no 65K-byte reduction is
needed. -/
theorem boundary_frame_65533_roundtrip (m : WireMessage)
    (h : m.payload.size = 65533) :
    unframeTransport (Transport.transportFrame m) = some m := by
  apply unframeTransport_transportFrame
  omega

/-! ## Pinned rust-lightning BigSize fixtures -/

/-- rust-lightning `BigSize(252)` writes `fc`
(`lightning/src/util/ser.rs:1859-1875`). -/
theorem diff_bigsize_encode_252 : Wire.encode 252 = bytes [0xfc] := by decide

/-- rust-lightning `BigSize(253)` writes `fd 00 fd`. -/
theorem diff_bigsize_encode_253 :
    Wire.encode 253 = bytes [0xfd, 0x00, 0xfd] := by decide

/-- rust-lightning `BigSize(65535)` writes `fd ff ff`. -/
theorem diff_bigsize_encode_65535 :
    Wire.encode 65535 = bytes [0xfd, 0xff, 0xff] := by decide

/-- rust-lightning `BigSize(65536)` writes `fe 00 01 00 00`. -/
theorem diff_bigsize_encode_65536 :
    Wire.encode 65536 = bytes [0xfe, 0x00, 0x01, 0x00, 0x00] := by decide

/-- rust-lightning reads `fc` as `252`, consuming one byte. -/
theorem diff_bigsize_decode_252 : Wire.decode (bytes [0xfc]) = some (252, 1) := by
  decide

/-- rust-lightning reads `fd 00 fd` as `253`, consuming three bytes. -/
theorem diff_bigsize_decode_253 :
    Wire.decode (bytes [0xfd, 0x00, 0xfd]) = some (253, 3) := by decide

/-- rust-lightning reads `fd ff ff` as `65535`, consuming three bytes. -/
theorem diff_bigsize_decode_65535 :
    Wire.decode (bytes [0xfd, 0xff, 0xff]) = some (65535, 3) := by decide

/-- rust-lightning reads `fe 00 01 00 00` as `65536`, consuming five bytes. -/
theorem diff_bigsize_decode_65536 :
    Wire.decode (bytes [0xfe, 0x00, 0x01, 0x00, 0x00]) = some (65536, 5) := by
  decide

/-- rust-lightning returns `DecodeError::InvalidValue` for `fd 00 fc`; the
model returns `none` (the model does not distinguish error classes). -/
theorem diff_bigsize_reject_noncanonical_253 :
    Wire.decode (bytes [0xfd, 0x00, 0xfc]) = none := by decide

/-- rust-lightning returns `DecodeError::ShortRead` for `fd 00`; the model
returns `none`. -/
theorem diff_bigsize_reject_short_253 :
    Wire.decode (bytes [0xfd, 0x00]) = none := by decide

/-- rust-lightning returns `DecodeError::ShortRead` for the tag-only `ff`
input; the model returns `none`. -/
theorem diff_bigsize_reject_tag_only_ff :
    Wire.decode (bytes [0xff]) = none := by decide

/-! ## Pinned rust-lightning TLV fixtures -/

/-- The rust-lightning `retired_tlvs_skipped_on_read` stream
(`lightning/src/util/ser_macros.rs:2051-2058`): four strictly increasing
records `2, 3, 5, 7`.  The structural model parser accepts it. -/
theorem diff_tlv_retired_skipped_decode :
    decodeTLV
        (bytes [0x02, 0x04, 0xff, 0xff, 0xff, 0xff,
                0x03, 0x08, 0xde, 0xad, 0xbe, 0xef, 0x1b, 0xad, 0xbe, 0xef,
                0x05, 0x02, 0x12, 0x34,
                0x07, 0x04, 0x1b, 0xad, 0x1d, 0xea]) =
      some (TLVStream.mk
        [⟨2, bytes [0xff, 0xff, 0xff, 0xff]⟩,
         ⟨3, bytes [0xde, 0xad, 0xbe, 0xef, 0x1b, 0xad, 0xbe, 0xef]⟩,
         ⟨5, bytes [0x12, 0x34]⟩,
         ⟨7, bytes [0x1b, 0xad, 0x1d, 0xea]⟩]) := by
  decide

/-- The same stream passes the strict-ordering admission layer. -/
theorem diff_tlv_retired_skipped_admission :
    decodeAdmissible
        (bytes [0x02, 0x04, 0xff, 0xff, 0xff, 0xff,
                0x03, 0x08, 0xde, 0xad, 0xbe, 0xef, 0x1b, 0xad, 0xbe, 0xef,
                0x05, 0x02, 0x12, 0x34,
                0x07, 0x04, 0x1b, 0xad, 0x1d, 0xea]) = true := by
  decide

/-- rust-lightning rejects the unknown even type `2` with
`UnknownRequiredFeature` (`lightning/src/util/ser_macros.rs:2060-2064`).  The
model has no namespace policy, so it parses and admits the single record.  This
is a declared differential gap, not a conformance claim. -/
theorem diff_tlv_unknown_even_2_decode :
    decodeTLV (bytes [0x02, 0x04, 0xff, 0xff, 0xff, 0xff]) =
      some (TLVStream.mk [⟨2, bytes [0xff, 0xff, 0xff, 0xff]⟩]) := by
  decide

/-- The model's actual admission decision for the unknown even type: accept. -/
theorem diff_tlv_unknown_even_2_admission :
    decodeAdmissible (bytes [0x02, 0x04, 0xff, 0xff, 0xff, 0xff]) = true := by
  decide

/-- rust-lightning treats the truncated record `02 04 ff ff` as `ShortRead`
(`lightning/src/util/ser_macros.rs:2066-2071`); the model parser rejects it. -/
theorem diff_tlv_truncated_2_decode :
    decodeTLV (bytes [0x02, 0x04, 0xff, 0xff]) = none := by decide

/-- The admission layer also rejects the truncated record. -/
theorem diff_tlv_truncated_2_admission :
    decodeAdmissible (bytes [0x02, 0x04, 0xff, 0xff]) = false := by decide

/-! ## Pinned rust-lightning wire-framing fixtures -/

/-- The transport length used for the `init` message (`type = 16`) with an
empty payload is `2`; rust-lightning computes `msgbuf.len() - 16 - 2` and
writes it big-endian. -/
theorem diff_wire_init_empty_length :
    Transport.transportLength ⟨16, bytes []⟩ = 2 := by decide

/-- The transport length for `init` with a four-byte payload is `6`. -/
theorem diff_wire_init_four_length :
    Transport.transportLength ⟨16, bytes [0x01, 0x02, 0x03, 0x04]⟩ = 6 := by
  decide

/-- The maximum transport length is `65535`; rust-lightning's
`LN_MAX_MSG_LEN = u16::MAX` rejects anything larger. -/
theorem diff_wire_max_length : declaredForPayload 65533 = 65535 :=
  boundary_declared_65533

/-- One byte over rust-lightning's limit is a transport length of `65536`,
which cannot fit the two-byte header. -/
theorem diff_wire_over_max_length : declaredForPayload 65534 = 65536 :=
  boundary_declared_65534

end LnLean.Proofs.Conformance.Diff
