/-
# Transport-framing, BOLT 2 payload, and pinned rust-lightning differential targets

**What this module is.**  Concrete, machine-checked expectations for the BOLT 8
transport frame that wraps a BOLT 1 Lightning message, finite BOLT 2
`open_channel`/`accept_channel`/`commitment_signed`/`update_add_htlc` payload
encodings, plus the differential fixtures in
`tests/conformance/rust-lightning/fixtures.json`.  Small framing and message
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
`payload_decoder_rejects_transport_frame` below is the witness.  The BOLT 8
model is promoted to `LnLean.Wire.Transport` in `LnLean/Wire/Message.lean`
(`transportFrame`, `unframeTransport`, and the length laws); this module imports
it and keeps the finite vectors.  Production `Wire.unframe` is deliberately
unchanged, and the generic boundary `Wire.Transport.unframe_transportFrame_eq_none`
states that it rejects every transport frame.

**Vectors.**  `tests/conformance/vectors.json` (`framing` object) holds the
small valid frames, malformed/truncated frames, and the length-boundary table;
its `messages` object holds the finite BOLT 2 payload/field rows below.
`tests/conformance/rust-lightning/fixtures.json` holds fixtures transcribed from
the pinned rust-lightning unit test `bigsize_encoding_decoding`
(`lightning/src/util/ser.rs:1857-1901`), the TLV reader test
`retired_tlvs_skipped_on_read` (`lightning/src/util/ser_macros.rs:2047-2071`),
and the wire length header described above.  The checker is offline: it reads
only committed JSON and this module's source, never the network or a Rust
toolchain.  A separate optional harness
(`tests/conformance/rust-lightning/generate.py --live`) runs the pinned tests
and a public-API probe under `cargo --offline --locked` with the committed
`pinned/Cargo.lock`, and records the comparison in `live-transcript.json`; the
checker verifies that transcript hash and its pinned provenance.  The live run
is evidence for the same finite rows, not a new model theorem.

**Scope.**  This is vector/differential conformance, not a full implementation
test.  It does not model Noise encryption, the 16-byte MACs, message dispatch,
full message decoders, or arbitrary-message serialization.  The BOLT 2 records
below are finite encoding fixtures with synthetic keys/signatures, not
serializer-correctness or signature-validity theorems.  The length header here
is plaintext, exactly as in the model's abstract frame.

**Build.**  Module-only target:
`lake build LnLean.Proofs.ConformanceDiffTargets`.  `LnLean.lean` already imports
this module; root-level changes remain parent-owned.
-/

import LnLean.Wire.Message
import LnLean.Wire.TLV
import LnLean.Proofs.Wire.TLVTargets

namespace LnLean.Proofs.Conformance.Diff

set_option autoImplicit false
set_option maxRecDepth 10000

open LnLean
open LnLean.Wire

/-- Byte-array literal used by the vector statements. -/
def bytes (l : List UInt8) : ByteArray := l.toByteArray

/-- The transport length as a function of the payload size.  This is the
arithmetic half of `Transport.transportLength`, extracted so the large boundary
facts do not require reducing a 65K-byte array. -/
def declaredForPayload (payloadSize : Nat) : Nat := 2 + payloadSize

/-! ## Transport model (promoted)

The BOLT 8 transport model now lives in `LnLean.Wire.Message` under
`LnLean.Wire.Transport`; see that module for `transportLength`,
`transportFrame`, `unframeTransport`, the round trip, and the declared-length
law.  This conformance module imports it and keeps only the concrete vectors,
the boundary table, and the differential fixtures.  The `open` below makes the
same short names visible here so the vector statements read as they did in
wave 5. -/

open Transport

/-- The two conventions are observably different on a concrete message: the
model frame's second field is `00 04`, the transport frame's is `00 06`. -/
theorem transportFrame_differs_from_model_frame :
    Transport.transportFrame ⟨16, bytes [0x01, 0x02, 0x03, 0x04]⟩ ≠
      Wire.frame ⟨16, bytes [0x01, 0x02, 0x03, 0x04]⟩ := by
  decide

/-! ## The model's payload-only decoder is not a transport decoder -/

/-- The model's `Wire.unframe` reads the second field as the payload length, so
it rejects the BOLT 8 transport frame even for a small valid message.  This is
the exact decoder gap that the promoted `Transport` namespace repairs. -/
theorem payload_decoder_rejects_transport_frame :
    Wire.unframe
        (Transport.transportFrame
          ⟨16, bytes [0x01, 0x02, 0x03, 0x04]⟩) = none :=
  LnLean.Wire.Transport.unframe_transportFrame_eq_none _

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


/-! ## BOLT 2 message payload vectors (S8-CONF-ENCODINGS)

These are independent fixtures, not serializers from `LnLean.Protocol.Messages`.
`open_channel` is a local `OpenChannelWire` record because this lane must not
depend on the type-32 `Msg.openChannel` constructor owned by another wave-8 lane.
The other records mirror the BOLT 2 field order and fixed widths so the byte
vectors can be checked by kernel reduction.  Optional `open_channel_tlvs` /
`accept_channel_tlvs` type-0 `upfront_shutdown_script` records are built with the
model's own `Wire.encode` BigSize encoder. -/

/-- Fixed-width big-endian `u32` payload field. -/
abbrev u32BE (n : Nat) : ByteArray := beBytes n 4

/-- Fixed-width big-endian `u64` payload field. -/
abbrev u64BE (n : Nat) : ByteArray := beBytes n 8

/-- `n` copies of one byte, used for the synthetic key/script/signature fill. -/
abbrev repeatedByte (n : Nat) (b : UInt8) : ByteArray :=
  (List.replicate n b).toByteArray

/-- A synthetic compressed point: one prefix byte plus a 32-byte fill. -/
abbrev point33 (pfx : UInt8) (fill : UInt8) : ByteArray :=
  bytes [pfx] ++ repeatedByte 32 fill

/-- One BOLT 1 TLV record: BigSize type || BigSize length || value. -/
abbrev tlvRecord (ty : Nat) (value : ByteArray) : ByteArray :=
  Wire.encode ty ++ Wire.encode value.size ++ value

/-- A BOLT 2 `open_channel` payload.  Field order follows the pinned BOLT 2
section; `upfrontShutdownScript` is the optional type-0 TLV. -/
structure OpenChannelWire where
  chainHash : ByteArray
  temporaryChannelId : ByteArray
  fundingSatoshis : Nat
  pushMsat : Nat
  dustLimitSatoshis : Nat
  maxHtlcValueInFlightMsat : Nat
  channelReserveSatoshis : Nat
  htlcMinimumMsat : Nat
  feeratePerKw : Nat
  toSelfDelay : Nat
  maxAcceptedHtlcs : Nat
  fundingPubKey : ByteArray
  revocationBasepoint : ByteArray
  paymentBasepoint : ByteArray
  delayedPaymentBasepoint : ByteArray
  htlcBasepoint : ByteArray
  firstPerCommitmentPoint : ByteArray
  channelFlags : ByteArray
  upfrontShutdownScript : Option ByteArray

namespace OpenChannelWire

/-- The BOLT 2 `open_channel` payload bytes. -/
def payload (m : OpenChannelWire) : ByteArray :=
  m.chainHash ++ m.temporaryChannelId ++
  u64BE m.fundingSatoshis ++ u64BE m.pushMsat ++
  u64BE m.dustLimitSatoshis ++ u64BE m.maxHtlcValueInFlightMsat ++
  u64BE m.channelReserveSatoshis ++ u64BE m.htlcMinimumMsat ++
  u32BE m.feeratePerKw ++ u16BE m.toSelfDelay ++ u16BE m.maxAcceptedHtlcs ++
  m.fundingPubKey ++ m.revocationBasepoint ++ m.paymentBasepoint ++
  m.delayedPaymentBasepoint ++ m.htlcBasepoint ++ m.firstPerCommitmentPoint ++
  m.channelFlags ++
  (match m.upfrontShutdownScript with
   | none => ByteArray.empty
   | some script => tlvRecord 0 script)

end OpenChannelWire

/-- A BOLT 2 `accept_channel` payload. -/
structure AcceptChannelWire where
  temporaryChannelId : ByteArray
  dustLimitSatoshis : Nat
  maxHtlcValueInFlightMsat : Nat
  channelReserveSatoshis : Nat
  htlcMinimumMsat : Nat
  minimumDepth : Nat
  toSelfDelay : Nat
  maxAcceptedHtlcs : Nat
  fundingPubKey : ByteArray
  revocationBasepoint : ByteArray
  paymentBasepoint : ByteArray
  delayedPaymentBasepoint : ByteArray
  htlcBasepoint : ByteArray
  firstPerCommitmentPoint : ByteArray
  upfrontShutdownScript : Option ByteArray

namespace AcceptChannelWire

/-- The BOLT 2 `accept_channel` payload bytes. -/
def payload (m : AcceptChannelWire) : ByteArray :=
  m.temporaryChannelId ++
  u64BE m.dustLimitSatoshis ++ u64BE m.maxHtlcValueInFlightMsat ++
  u64BE m.channelReserveSatoshis ++ u64BE m.htlcMinimumMsat ++
  u32BE m.minimumDepth ++ u16BE m.toSelfDelay ++ u16BE m.maxAcceptedHtlcs ++
  m.fundingPubKey ++ m.revocationBasepoint ++ m.paymentBasepoint ++
  m.delayedPaymentBasepoint ++ m.htlcBasepoint ++ m.firstPerCommitmentPoint ++
  (match m.upfrontShutdownScript with
   | none => ByteArray.empty
   | some script => tlvRecord 0 script)

end AcceptChannelWire

/-- A BOLT 2 `commitment_signed` payload: channel id, 64-byte commitment
signature, `u16` HTLC count, then one 64-byte signature per HTLC. -/
structure CommitmentSignedWire where
  channelId : ByteArray
  signature : ByteArray
  htlcSignatures : List ByteArray

namespace CommitmentSignedWire

/-- The BOLT 2 `commitment_signed` payload bytes (without TLVs). -/
def payload (m : CommitmentSignedWire) : ByteArray :=
  m.channelId ++ m.signature ++ u16BE m.htlcSignatures.length ++
    m.htlcSignatures.foldl (fun acc sig => acc ++ sig) ByteArray.empty

end CommitmentSignedWire

/-- A BOLT 2 `update_add_htlc` payload. -/
structure UpdateAddHtlcWire where
  channelId : ByteArray
  htlcId : Nat
  amountMsat : Nat
  paymentHash : ByteArray
  cltvExpiry : Nat
  onionRoutingPacket : ByteArray

namespace UpdateAddHtlcWire

/-- The BOLT 2 `update_add_htlc` payload bytes. -/
def payload (m : UpdateAddHtlcWire) : ByteArray :=
  m.channelId ++ u64BE m.htlcId ++ u64BE m.amountMsat ++
    m.paymentHash ++ u32BE m.cltvExpiry ++ m.onionRoutingPacket

end UpdateAddHtlcWire

/-- BOLT 0 mainnet `chain_hash` (the hash is used directly, not reversed). -/
abbrev chainHashMainnet : ByteArray :=
  bytes [
  0x6f, 0xe2, 0x8c, 0x0a, 0xb6, 0xf1, 0xb3, 0x72, 0xc1, 0xa6,
  0xa2, 0x46, 0xae, 0x63, 0xf7, 0x4f, 0x93, 0x1e, 0x83, 0x65,
  0xe1, 0x5a, 0x08, 0x9c, 0x68, 0xd6, 0x19, 0x00, 0x00, 0x00,
  0x00, 0x00]

/-- Synthetic 32-byte temporary channel id shared by the open/accept vectors. -/
abbrev tempChannelId : ByteArray :=
  bytes [
  0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a,
  0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10, 0x11, 0x12, 0x13, 0x14,
  0x15, 0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e,
  0x1f, 0x20]

/-- Synthetic 64-byte commitment signature. -/
abbrev commitmentSignature : ByteArray :=
  bytes [
  0xa0, 0xa1, 0xa2, 0xa3, 0xa4, 0xa5, 0xa6, 0xa7, 0xa8, 0xa9,
  0xaa, 0xab, 0xac, 0xad, 0xae, 0xaf, 0xb0, 0xb1, 0xb2, 0xb3,
  0xb4, 0xb5, 0xb6, 0xb7, 0xb8, 0xb9, 0xba, 0xbb, 0xbc, 0xbd,
  0xbe, 0xbf, 0xa0, 0xa1, 0xa2, 0xa3, 0xa4, 0xa5, 0xa6, 0xa7,
  0xa8, 0xa9, 0xaa, 0xab, 0xac, 0xad, 0xae, 0xaf, 0xb0, 0xb1,
  0xb2, 0xb3, 0xb4, 0xb5, 0xb6, 0xb7, 0xb8, 0xb9, 0xba, 0xbb,
  0xbc, 0xbd, 0xbe, 0xbf]

/-- Synthetic 64-byte HTLC signature 0. -/
abbrev htlcSignature0 : ByteArray :=
  bytes [
  0xe0, 0xe1, 0xe2, 0xe3, 0xe4, 0xe5, 0xe6, 0xe7, 0xe8, 0xe9,
  0xea, 0xeb, 0xec, 0xed, 0xee, 0xef, 0xf0, 0xf1, 0xf2, 0xf3,
  0xf4, 0xf5, 0xf6, 0xf7, 0xf8, 0xf9, 0xfa, 0xfb, 0xfc, 0xfd,
  0xfe, 0xff, 0xe0, 0xe1, 0xe2, 0xe3, 0xe4, 0xe5, 0xe6, 0xe7,
  0xe8, 0xe9, 0xea, 0xeb, 0xec, 0xed, 0xee, 0xef, 0xf0, 0xf1,
  0xf2, 0xf3, 0xf4, 0xf5, 0xf6, 0xf7, 0xf8, 0xf9, 0xfa, 0xfb,
  0xfc, 0xfd, 0xfe, 0xff]

/-- Synthetic 64-byte HTLC signature 1. -/
abbrev htlcSignature1 : ByteArray :=
  bytes [
  0xf0, 0xf1, 0xf2, 0xf3, 0xf4, 0xf5, 0xf6, 0xf7, 0xf8, 0xf9,
  0xfa, 0xfb, 0xfc, 0xfd, 0xfe, 0xff, 0xf0, 0xf1, 0xf2, 0xf3,
  0xf4, 0xf5, 0xf6, 0xf7, 0xf8, 0xf9, 0xfa, 0xfb, 0xfc, 0xfd,
  0xfe, 0xff, 0xf0, 0xf1, 0xf2, 0xf3, 0xf4, 0xf5, 0xf6, 0xf7,
  0xf8, 0xf9, 0xfa, 0xfb, 0xfc, 0xfd, 0xfe, 0xff, 0xf0, 0xf1,
  0xf2, 0xf3, 0xf4, 0xf5, 0xf6, 0xf7, 0xf8, 0xf9, 0xfa, 0xfb,
  0xfc, 0xfd, 0xfe, 0xff]

/-- Base `open_channel` fixture: no TLV extension, 319-byte payload. -/
abbrev openChannelBaseFixture : OpenChannelWire where
  chainHash := chainHashMainnet
  temporaryChannelId := tempChannelId
  fundingSatoshis := 100000
  pushMsat := 0
  dustLimitSatoshis := 546
  maxHtlcValueInFlightMsat := 1000000000
  channelReserveSatoshis := 1000
  htlcMinimumMsat := 1000
  feeratePerKw := 253
  toSelfDelay := 144
  maxAcceptedHtlcs := 483
  fundingPubKey := point33 0x02 0x11
  revocationBasepoint := point33 0x03 0x22
  paymentBasepoint := point33 0x02 0x33
  delayedPaymentBasepoint := point33 0x03 0x44
  htlcBasepoint := point33 0x02 0x55
  firstPerCommitmentPoint := point33 0x03 0x66
  channelFlags := bytes [0x01]
  upfrontShutdownScript := none

/-- Synthetic P2WPKH `upfront_shutdown_script` (22 bytes). -/
abbrev openShutdownScript : ByteArray :=
  bytes [0x00, 0x14] ++ repeatedByte 20 0x5a

/-- `open_channel` with the type-0 `upfront_shutdown_script` TLV: 343 bytes. -/
abbrev openChannelUpfrontShutdownFixture : OpenChannelWire :=
  { openChannelBaseFixture with upfrontShutdownScript := some openShutdownScript }

/-- Base `accept_channel` fixture: no TLV extension, 270-byte payload. -/
abbrev acceptChannelBaseFixture : AcceptChannelWire where
  temporaryChannelId := tempChannelId
  dustLimitSatoshis := 546
  maxHtlcValueInFlightMsat := 1000000000
  channelReserveSatoshis := 1000
  htlcMinimumMsat := 1000
  minimumDepth := 6
  toSelfDelay := 144
  maxAcceptedHtlcs := 483
  fundingPubKey := point33 0x02 0x77
  revocationBasepoint := point33 0x03 0x88
  paymentBasepoint := point33 0x02 0x99
  delayedPaymentBasepoint := point33 0x03 0xaa
  htlcBasepoint := point33 0x02 0xbb
  firstPerCommitmentPoint := point33 0x03 0xcc
  upfrontShutdownScript := none

/-- Synthetic P2WSH `upfront_shutdown_script` (34 bytes). -/
abbrev acceptShutdownScript : ByteArray :=
  bytes [0x00, 0x20] ++ repeatedByte 32 0xdd

/-- `accept_channel` with the type-0 TLV: 306 bytes. -/
abbrev acceptChannelUpfrontShutdownFixture : AcceptChannelWire :=
  { acceptChannelBaseFixture with upfrontShutdownScript := some acceptShutdownScript }

/-- `commitment_signed` with two 64-byte HTLC signatures: 226 bytes. -/
abbrev commitmentSignedTwoHtlcsFixture : CommitmentSignedWire where
  channelId := tempChannelId
  signature := commitmentSignature
  htlcSignatures := [htlcSignature0, htlcSignature1]

/-- `update_add_htlc` with a 1366-byte onion packet: 1450 bytes. -/
abbrev updateAddHtlcFixture : UpdateAddHtlcWire where
  channelId := tempChannelId
  htlcId := 7
  amountMsat := 1000000
  paymentHash := repeatedByte 32 0x42
  cltvExpiry := 800000
  onionRoutingPacket := bytes [0x01] ++ repeatedByte 1365 0xaa

/-- open_channel: payload length (319 bytes). -/
theorem msg_open_channel_base_length : openChannelBaseFixture.payload.size = 319 := by decide

/-- The BOLT 8 transport length for this open_channel payload is 321. -/
theorem msg_open_channel_base_transport :
    Transport.transportLength ⟨32, openChannelBaseFixture.payload⟩ = 321 := by decide

/-- The transport header is `0141`. -/
theorem msg_open_channel_base_header :
    Transport.lengthHeader ⟨32, openChannelBaseFixture.payload⟩ = bytes [0x01, 0x41] := by decide

/-- The type and transport header together: `00200141`. -/
theorem msg_open_channel_base_frame_prefix :
    u16BE 32 ++ Transport.lengthHeader ⟨32, openChannelBaseFixture.payload⟩ = bytes [0x00, 0x20, 0x01, 0x41] := by decide

/-- The exact 319-byte open_channel payload. -/
theorem msg_open_channel_base_payload :
    openChannelBaseFixture.payload = bytes [
      0x6f, 0xe2, 0x8c, 0x0a, 0xb6, 0xf1, 0xb3, 0x72, 0xc1, 0xa6,
      0xa2, 0x46, 0xae, 0x63, 0xf7, 0x4f, 0x93, 0x1e, 0x83, 0x65,
      0xe1, 0x5a, 0x08, 0x9c, 0x68, 0xd6, 0x19, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,
      0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10, 0x11, 0x12,
      0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b, 0x1c,
      0x1d, 0x1e, 0x1f, 0x20, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01,
      0x86, 0xa0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, 0x22, 0x00, 0x00,
      0x00, 0x00, 0x3b, 0x9a, 0xca, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x03, 0xe8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x03, 0xe8, 0x00, 0x00, 0x00, 0xfd, 0x00, 0x90, 0x01, 0xe3,
      0x02, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11,
      0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11,
      0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11,
      0x11, 0x11, 0x11, 0x03, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22,
      0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22,
      0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22,
      0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x02, 0x33, 0x33, 0x33,
      0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33,
      0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33,
      0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x03,
      0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44,
      0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44,
      0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44,
      0x44, 0x44, 0x02, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55,
      0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55,
      0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55,
      0x55, 0x55, 0x55, 0x55, 0x55, 0x03, 0x66, 0x66, 0x66, 0x66,
      0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66,
      0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66,
      0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x01] := by decide

/-- open_channel: payload length (343 bytes). -/
theorem msg_open_channel_upfront_shutdown_length : openChannelUpfrontShutdownFixture.payload.size = 343 := by decide

/-- The BOLT 8 transport length for this open_channel payload is 345. -/
theorem msg_open_channel_upfront_shutdown_transport :
    Transport.transportLength ⟨32, openChannelUpfrontShutdownFixture.payload⟩ = 345 := by decide

/-- The transport header is `0159`. -/
theorem msg_open_channel_upfront_shutdown_header :
    Transport.lengthHeader ⟨32, openChannelUpfrontShutdownFixture.payload⟩ = bytes [0x01, 0x59] := by decide

/-- The type and transport header together: `00200159`. -/
theorem msg_open_channel_upfront_shutdown_frame_prefix :
    u16BE 32 ++ Transport.lengthHeader ⟨32, openChannelUpfrontShutdownFixture.payload⟩ = bytes [0x00, 0x20, 0x01, 0x59] := by decide

/-- The exact 343-byte open_channel payload. -/
theorem msg_open_channel_upfront_shutdown_payload :
    openChannelUpfrontShutdownFixture.payload = bytes [
      0x6f, 0xe2, 0x8c, 0x0a, 0xb6, 0xf1, 0xb3, 0x72, 0xc1, 0xa6,
      0xa2, 0x46, 0xae, 0x63, 0xf7, 0x4f, 0x93, 0x1e, 0x83, 0x65,
      0xe1, 0x5a, 0x08, 0x9c, 0x68, 0xd6, 0x19, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,
      0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10, 0x11, 0x12,
      0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b, 0x1c,
      0x1d, 0x1e, 0x1f, 0x20, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01,
      0x86, 0xa0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, 0x22, 0x00, 0x00,
      0x00, 0x00, 0x3b, 0x9a, 0xca, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x03, 0xe8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x03, 0xe8, 0x00, 0x00, 0x00, 0xfd, 0x00, 0x90, 0x01, 0xe3,
      0x02, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11,
      0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11,
      0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11,
      0x11, 0x11, 0x11, 0x03, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22,
      0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22,
      0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22,
      0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x02, 0x33, 0x33, 0x33,
      0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33,
      0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33,
      0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x03,
      0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44,
      0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44,
      0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44,
      0x44, 0x44, 0x02, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55,
      0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55,
      0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55,
      0x55, 0x55, 0x55, 0x55, 0x55, 0x03, 0x66, 0x66, 0x66, 0x66,
      0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66,
      0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66,
      0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x01, 0x00,
      0x16, 0x00, 0x14, 0x5a, 0x5a, 0x5a, 0x5a, 0x5a, 0x5a, 0x5a,
      0x5a, 0x5a, 0x5a, 0x5a, 0x5a, 0x5a, 0x5a, 0x5a, 0x5a, 0x5a,
      0x5a, 0x5a, 0x5a] := by decide

/-- accept_channel: payload length (270 bytes). -/
theorem msg_accept_channel_base_length : acceptChannelBaseFixture.payload.size = 270 := by decide

/-- The BOLT 8 transport length for this accept_channel payload is 272. -/
theorem msg_accept_channel_base_transport :
    Transport.transportLength ⟨33, acceptChannelBaseFixture.payload⟩ = 272 := by decide

/-- The transport header is `0110`. -/
theorem msg_accept_channel_base_header :
    Transport.lengthHeader ⟨33, acceptChannelBaseFixture.payload⟩ = bytes [0x01, 0x10] := by decide

/-- The type and transport header together: `00210110`. -/
theorem msg_accept_channel_base_frame_prefix :
    u16BE 33 ++ Transport.lengthHeader ⟨33, acceptChannelBaseFixture.payload⟩ = bytes [0x00, 0x21, 0x01, 0x10] := by decide

/-- The exact 270-byte accept_channel payload. -/
theorem msg_accept_channel_base_payload :
    acceptChannelBaseFixture.payload = bytes [
      0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a,
      0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10, 0x11, 0x12, 0x13, 0x14,
      0x15, 0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e,
      0x1f, 0x20, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, 0x22,
      0x00, 0x00, 0x00, 0x00, 0x3b, 0x9a, 0xca, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x03, 0xe8, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x03, 0xe8, 0x00, 0x00, 0x00, 0x06, 0x00, 0x90,
      0x01, 0xe3, 0x02, 0x77, 0x77, 0x77, 0x77, 0x77, 0x77, 0x77,
      0x77, 0x77, 0x77, 0x77, 0x77, 0x77, 0x77, 0x77, 0x77, 0x77,
      0x77, 0x77, 0x77, 0x77, 0x77, 0x77, 0x77, 0x77, 0x77, 0x77,
      0x77, 0x77, 0x77, 0x77, 0x77, 0x03, 0x88, 0x88, 0x88, 0x88,
      0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88,
      0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88,
      0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x02, 0x99,
      0x99, 0x99, 0x99, 0x99, 0x99, 0x99, 0x99, 0x99, 0x99, 0x99,
      0x99, 0x99, 0x99, 0x99, 0x99, 0x99, 0x99, 0x99, 0x99, 0x99,
      0x99, 0x99, 0x99, 0x99, 0x99, 0x99, 0x99, 0x99, 0x99, 0x99,
      0x99, 0x03, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa,
      0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa,
      0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa,
      0xaa, 0xaa, 0xaa, 0xaa, 0x02, 0xbb, 0xbb, 0xbb, 0xbb, 0xbb,
      0xbb, 0xbb, 0xbb, 0xbb, 0xbb, 0xbb, 0xbb, 0xbb, 0xbb, 0xbb,
      0xbb, 0xbb, 0xbb, 0xbb, 0xbb, 0xbb, 0xbb, 0xbb, 0xbb, 0xbb,
      0xbb, 0xbb, 0xbb, 0xbb, 0xbb, 0xbb, 0xbb, 0x03, 0xcc, 0xcc,
      0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc,
      0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc,
      0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc] := by decide

/-- accept_channel: payload length (306 bytes). -/
theorem msg_accept_channel_upfront_shutdown_length : acceptChannelUpfrontShutdownFixture.payload.size = 306 := by decide

/-- The BOLT 8 transport length for this accept_channel payload is 308. -/
theorem msg_accept_channel_upfront_shutdown_transport :
    Transport.transportLength ⟨33, acceptChannelUpfrontShutdownFixture.payload⟩ = 308 := by decide

/-- The transport header is `0134`. -/
theorem msg_accept_channel_upfront_shutdown_header :
    Transport.lengthHeader ⟨33, acceptChannelUpfrontShutdownFixture.payload⟩ = bytes [0x01, 0x34] := by decide

/-- The type and transport header together: `00210134`. -/
theorem msg_accept_channel_upfront_shutdown_frame_prefix :
    u16BE 33 ++ Transport.lengthHeader ⟨33, acceptChannelUpfrontShutdownFixture.payload⟩ = bytes [0x00, 0x21, 0x01, 0x34] := by decide

/-- The exact 306-byte accept_channel payload. -/
theorem msg_accept_channel_upfront_shutdown_payload :
    acceptChannelUpfrontShutdownFixture.payload = bytes [
      0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a,
      0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10, 0x11, 0x12, 0x13, 0x14,
      0x15, 0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e,
      0x1f, 0x20, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, 0x22,
      0x00, 0x00, 0x00, 0x00, 0x3b, 0x9a, 0xca, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x03, 0xe8, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x03, 0xe8, 0x00, 0x00, 0x00, 0x06, 0x00, 0x90,
      0x01, 0xe3, 0x02, 0x77, 0x77, 0x77, 0x77, 0x77, 0x77, 0x77,
      0x77, 0x77, 0x77, 0x77, 0x77, 0x77, 0x77, 0x77, 0x77, 0x77,
      0x77, 0x77, 0x77, 0x77, 0x77, 0x77, 0x77, 0x77, 0x77, 0x77,
      0x77, 0x77, 0x77, 0x77, 0x77, 0x03, 0x88, 0x88, 0x88, 0x88,
      0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88,
      0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88,
      0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x02, 0x99,
      0x99, 0x99, 0x99, 0x99, 0x99, 0x99, 0x99, 0x99, 0x99, 0x99,
      0x99, 0x99, 0x99, 0x99, 0x99, 0x99, 0x99, 0x99, 0x99, 0x99,
      0x99, 0x99, 0x99, 0x99, 0x99, 0x99, 0x99, 0x99, 0x99, 0x99,
      0x99, 0x03, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa,
      0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa,
      0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa,
      0xaa, 0xaa, 0xaa, 0xaa, 0x02, 0xbb, 0xbb, 0xbb, 0xbb, 0xbb,
      0xbb, 0xbb, 0xbb, 0xbb, 0xbb, 0xbb, 0xbb, 0xbb, 0xbb, 0xbb,
      0xbb, 0xbb, 0xbb, 0xbb, 0xbb, 0xbb, 0xbb, 0xbb, 0xbb, 0xbb,
      0xbb, 0xbb, 0xbb, 0xbb, 0xbb, 0xbb, 0xbb, 0x03, 0xcc, 0xcc,
      0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc,
      0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc,
      0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc,
      0x00, 0x22, 0x00, 0x20, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd,
      0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd,
      0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd,
      0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd] := by decide

/-- commitment_signed: payload length (226 bytes). -/
theorem msg_commitment_signed_two_htlcs_length : commitmentSignedTwoHtlcsFixture.payload.size = 226 := by decide

/-- The BOLT 8 transport length for this commitment_signed payload is 228. -/
theorem msg_commitment_signed_two_htlcs_transport :
    Transport.transportLength ⟨132, commitmentSignedTwoHtlcsFixture.payload⟩ = 228 := by decide

/-- The transport header is `00e4`. -/
theorem msg_commitment_signed_two_htlcs_header :
    Transport.lengthHeader ⟨132, commitmentSignedTwoHtlcsFixture.payload⟩ = bytes [0x00, 0xe4] := by decide

/-- The type and transport header together: `008400e4`. -/
theorem msg_commitment_signed_two_htlcs_frame_prefix :
    u16BE 132 ++ Transport.lengthHeader ⟨132, commitmentSignedTwoHtlcsFixture.payload⟩ = bytes [0x00, 0x84, 0x00, 0xe4] := by decide

/-- The exact 226-byte commitment_signed payload. -/
theorem msg_commitment_signed_two_htlcs_payload :
    commitmentSignedTwoHtlcsFixture.payload = bytes [
      0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a,
      0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10, 0x11, 0x12, 0x13, 0x14,
      0x15, 0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e,
      0x1f, 0x20, 0xa0, 0xa1, 0xa2, 0xa3, 0xa4, 0xa5, 0xa6, 0xa7,
      0xa8, 0xa9, 0xaa, 0xab, 0xac, 0xad, 0xae, 0xaf, 0xb0, 0xb1,
      0xb2, 0xb3, 0xb4, 0xb5, 0xb6, 0xb7, 0xb8, 0xb9, 0xba, 0xbb,
      0xbc, 0xbd, 0xbe, 0xbf, 0xa0, 0xa1, 0xa2, 0xa3, 0xa4, 0xa5,
      0xa6, 0xa7, 0xa8, 0xa9, 0xaa, 0xab, 0xac, 0xad, 0xae, 0xaf,
      0xb0, 0xb1, 0xb2, 0xb3, 0xb4, 0xb5, 0xb6, 0xb7, 0xb8, 0xb9,
      0xba, 0xbb, 0xbc, 0xbd, 0xbe, 0xbf, 0x00, 0x02, 0xe0, 0xe1,
      0xe2, 0xe3, 0xe4, 0xe5, 0xe6, 0xe7, 0xe8, 0xe9, 0xea, 0xeb,
      0xec, 0xed, 0xee, 0xef, 0xf0, 0xf1, 0xf2, 0xf3, 0xf4, 0xf5,
      0xf6, 0xf7, 0xf8, 0xf9, 0xfa, 0xfb, 0xfc, 0xfd, 0xfe, 0xff,
      0xe0, 0xe1, 0xe2, 0xe3, 0xe4, 0xe5, 0xe6, 0xe7, 0xe8, 0xe9,
      0xea, 0xeb, 0xec, 0xed, 0xee, 0xef, 0xf0, 0xf1, 0xf2, 0xf3,
      0xf4, 0xf5, 0xf6, 0xf7, 0xf8, 0xf9, 0xfa, 0xfb, 0xfc, 0xfd,
      0xfe, 0xff, 0xf0, 0xf1, 0xf2, 0xf3, 0xf4, 0xf5, 0xf6, 0xf7,
      0xf8, 0xf9, 0xfa, 0xfb, 0xfc, 0xfd, 0xfe, 0xff, 0xf0, 0xf1,
      0xf2, 0xf3, 0xf4, 0xf5, 0xf6, 0xf7, 0xf8, 0xf9, 0xfa, 0xfb,
      0xfc, 0xfd, 0xfe, 0xff, 0xf0, 0xf1, 0xf2, 0xf3, 0xf4, 0xf5,
      0xf6, 0xf7, 0xf8, 0xf9, 0xfa, 0xfb, 0xfc, 0xfd, 0xfe, 0xff,
      0xf0, 0xf1, 0xf2, 0xf3, 0xf4, 0xf5, 0xf6, 0xf7, 0xf8, 0xf9,
      0xfa, 0xfb, 0xfc, 0xfd, 0xfe, 0xff] := by decide

/-- update_add_htlc: payload length (1450 bytes). -/
theorem msg_update_add_htlc_base_length : updateAddHtlcFixture.payload.size = 1450 := by decide

/-- The BOLT 8 transport length for this update_add_htlc payload is 1452. -/
theorem msg_update_add_htlc_base_transport :
    Transport.transportLength ⟨128, updateAddHtlcFixture.payload⟩ = 1452 := by decide

/-- The transport header is `05ac`. -/
theorem msg_update_add_htlc_base_header :
    Transport.lengthHeader ⟨128, updateAddHtlcFixture.payload⟩ = bytes [0x05, 0xac] := by decide

/-- The type and transport header together: `008005ac`. -/
theorem msg_update_add_htlc_base_frame_prefix :
    u16BE 128 ++ Transport.lengthHeader ⟨128, updateAddHtlcFixture.payload⟩ = bytes [0x00, 0x80, 0x05, 0xac] := by decide


/-! ## Compatibility path for the wave-5 audit -/

/-! Compatibility path for the wave-5 fully-qualified name
`LnLean.Proofs.Conformance.Diff.Transport.transportFrame_size` used by
`LnLean/Proofs/PhaseC3/AxiomAudit.lean`.  The real theorem is
`LnLean.Wire.Transport.transportFrame_size`; this is a one-line delegation, not
a second proof.  Declared last so the earlier `Transport.*` references resolve
to the promoted `LnLean.Wire.Transport` namespace. -/
namespace Transport

theorem transportFrame_size (m : WireMessage) :
    (LnLean.Wire.Transport.transportFrame m).size = 4 + m.payload.size :=
  LnLean.Wire.Transport.transportFrame_size m

end Transport

end LnLean.Proofs.Conformance.Diff
