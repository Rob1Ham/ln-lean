/-
# Wave 8 lane H38 — additional deterministic wire-conformance vectors

**Issue.**  `CONF-01` (finite conformance vector suite; see
`docs/OPEN-ISSUES.md`).  This module is additive: it does **not** edit
`tests/conformance/vectors.json`, `scripts/check-conformance.py`, or any other
shared fixture.  Every vector below is stated locally on the existing model
encoders/decoders:

* `LnLean.Wire.encode` / `LnLean.Wire.decode` (BOLT 1 BigSize),
* `LnLean.Wire.decodeTLV`, `LnLean.Wire.TLVStream.encode`,
  `LnLean.Wire.TLVRecord.encode` (BOLT 1 TLV),
* `LnLean.Wire.frame` / `LnLean.Wire.unframe` (payload-only model frame) and
  `LnLean.Wire.Transport.transportFrame` / `unframeTransport` (BOLT 8 transport
  frame) from `LnLean/Wire/Message.lean`.

All theorems are closed by kernel reduction (`decide`), so they are
deterministic, need no axioms beyond the standard kernel, and cannot drift with
toolchain behaviour.

## New boundaries (relative to the existing vectors)

The existing suites are `LnLean.Proofs.ConformanceTargets` and
`LnLean.Proofs.ConformanceDiffTargets`.  They already pin BigSize
`0, 1, 252, 253, 254, 255, 256, 65535, 65536, 4294967295, 4294967296,
2^64-1`, TLV types `1, 2, 31, 254, 255, 65535, 65536, 2^64-1` and empty
streams, and framing types `0, 16, 255, 256, 65535`.  This module adds only
values outside that inventory:

* BigSize two-byte payload high-bit boundary `32768 = 0x8000`
  (`fd 80 00`), plus its decode.
* BigSize three-byte-value / four-byte-field boundary `16777215 = 0xffffff`
  (`fe 00 ff ff ff`) and the next value `16777216 = 0x01000000`
  (`fe 01 00 00 00`), plus decodes.
* BigSize eight-byte payload high-bit boundary `2^63`
  (`ff 80 00 00 00 00 00 00 00`) and the largest non-maximal `uint64`
  `2^64-2` (`ff ff ff ff ff ff ff fe`), plus decodes.
* BigSize streaming decodes (trailing bytes left unconsumed) for the
  three-, five-, and nine-byte length classes; the existing suite has only the
  one-byte trailing case `[0x00, 0xff]`.
* BigSize non-minimal four-byte value `65021 = 0xfdfd` (the interior of the
  `0xfd..0xfffe` region that must use the three-byte class); the existing suite
  only pins `0` and `65535` in the four-byte class.
* TLV type `0`, type `252`, type `253` (the type-field BigSize class
  transition `fc` to `fd 00 fd`), and the adjacent types `65535`/`65536`
  (the three-byte/five-byte type-field transition inside one stream).
* TLV **encoder** vectors (`TLVStream.encode` / `TLVRecord.encode`); the
  existing suites only decode, apart from the empty-stream encoding.
* TLV value-length BigSize class transition: one-byte length `252` (`fc`)
  versus three-byte length `253` (`fd 00 fd`).
* Framing types `1`, `128`, `32768`, `65534` (the existing framing vectors use
  `0, 16, 255, 256, 65535`), the minimal declared transport length `2`, the
  concrete payload-only-decoder rejection of that same minimal transport frame,
  the payload-only frame `00 10 00 00` and its successful decode, the two-byte
  header boundary `255`/`256`, and one-byte / two-byte truncated headers.

**What this is not.**  Finite-vector conformance only.  It does not add
known-type length validation, even/odd unknown-type policy, or message-body
semantics, and it does not change the two declared TLV model gaps recorded in
`LnLean.Proofs.ConformanceTargets`.

**Build.**  Module-only target:
`lake build LnLean.Proofs.WaveH.H38` (root import is integrator-owned).
-/

import LnLean.Wire.Message
import LnLean.Wire.TLV
import LnLean.Proofs.Wire.TLVTargets

namespace LnLean.Proofs.WaveH.H38

set_option autoImplicit false

-- The TLV length-class vectors parse 252/253-byte values; the reference parser
-- is structurally recursive, so the default `decide` recursion budget is too
-- small.  This is a reduction-depth setting only; no proof changes.
set_option maxRecDepth 100000

open LnLean
open LnLean.Wire

/-- Byte-array literal used by every vector statement (local to this lane). -/
def bytes (l : List UInt8) : ByteArray := l.toByteArray

/-- A value repeated `n` times, used only for the TLV length-class vectors. -/
def repeated (n : Nat) (b : UInt8) : ByteArray := (List.replicate n b).toByteArray

/-- `WireMessage` derives `Repr` but not `DecidableEq`; this local instance is
needed only so the positive framing vectors can close by `decide`.  It is
definitionally the pair of the two field equalities and is not exported as a
shared instance (it is `local`). -/
local instance wireMessageDecidableEq : DecidableEq WireMessage := by
  intro a b
  rcases a with ⟨ta, pa⟩
  rcases b with ⟨tb, pb⟩
  by_cases ht : ta = tb
  · subst ht
    by_cases hp : pa = pb
    · subst hp
      exact isTrue rfl
    · exact isFalse (by intro h; exact hp (congrArg WireMessage.payload h))
  · exact isFalse (by intro h; exact ht (congrArg WireMessage.type h))

/-! ## BigSize: new payload-width boundaries -/

/-- `32768 = 0x8000` is the high-bit boundary of the two-byte payload class. -/
theorem h38_bigsize_encode_32768 : Wire.encode 32768 = bytes [0xfd, 0x80, 0x00] := by
  decide

theorem h38_bigsize_decode_32768 :
    Wire.decode (bytes [0xfd, 0x80, 0x00]) = some (32768, 3) := by
  decide

/-- `16777215 = 0xffffff` fills three bytes but still needs the four-byte class
because it exceeds `0xffff`. -/
theorem h38_bigsize_encode_16777215 :
    Wire.encode 16777215 = bytes [0xfe, 0x00, 0xff, 0xff, 0xff] := by
  decide

theorem h38_bigsize_decode_16777215 :
    Wire.decode (bytes [0xfe, 0x00, 0xff, 0xff, 0xff]) = some (16777215, 5) := by
  decide

/-- `16777216 = 0x01000000` is the first value using the fourth payload byte. -/
theorem h38_bigsize_encode_16777216 :
    Wire.encode 16777216 = bytes [0xfe, 0x01, 0x00, 0x00, 0x00] := by
  decide

theorem h38_bigsize_decode_16777216 :
    Wire.decode (bytes [0xfe, 0x01, 0x00, 0x00, 0x00]) = some (16777216, 5) := by
  decide

/-- `2^63` is the high-bit boundary of the eight-byte payload class. -/
theorem h38_bigsize_encode_pow63 :
    Wire.encode 9223372036854775808 =
      bytes [0xff, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] := by
  decide

theorem h38_bigsize_decode_pow63 :
    Wire.decode
        (bytes [0xff, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]) =
      some (9223372036854775808, 9) := by
  decide

/-- `2^64 - 2` is the largest `uint64` below the maximal `0xff..ff`. -/
theorem h38_bigsize_encode_uint64_max_minus_one :
    Wire.encode 18446744073709551614 =
      bytes [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe] := by
  decide

theorem h38_bigsize_decode_uint64_max_minus_one :
    Wire.decode (bytes [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe]) =
      some (18446744073709551614, 9) := by
  decide

/-! ## BigSize: streaming consumption in each multi-byte class

`Wire.decode` is a streaming decoder: it returns the consumed length and leaves
trailing bytes alone.  The existing suite pins only the one-byte case
`[0x00, 0xff]`; these pin one witness in the three-, five-, and nine-byte
classes. -/

theorem h38_bigsize_decode_streaming_fd :
    Wire.decode (bytes [0xfd, 0x00, 0xfd, 0xaa]) = some (253, 3) := by
  decide

theorem h38_bigsize_decode_streaming_fe :
    Wire.decode (bytes [0xfe, 0x00, 0x01, 0x00, 0x00, 0xaa]) = some (65536, 5) := by
  decide

theorem h38_bigsize_decode_streaming_ff :
    Wire.decode
        (bytes [0xff, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0xaa]) =
      some (4294967296, 9) := by
  decide

/-- `0xfdfd = 65021` lies in `0xfd..0xfffe`, so a four-byte encoding is
non-minimal and must be rejected.  This is the interior of the four-byte
rejection region; the existing vectors pin only `0` and `65535`. -/
theorem h38_bigsize_reject_noncanonical_four_interior :
    Wire.decode (bytes [0xfe, 0x00, 0x00, 0xfd, 0xfd]) = none := by
  decide

/-! ## TLV: new type boundaries -/

/-- Type `0` is the smallest legal TLV type. -/
theorem h38_tlv_type_zero_decode :
    decodeTLV (bytes [0x00, 0x00]) =
      some (TLVStream.mk [⟨0, bytes []⟩]) := by
  decide

theorem h38_tlv_type_zero_admission : decodeAdmissible (bytes [0x00, 0x00]) = true := by
  decide

/-- Type `252 = 0xfc` is the last type encoded in one BigSize byte. -/
theorem h38_tlv_type_252_decode :
    decodeTLV (bytes [0xfc, 0x00]) =
      some (TLVStream.mk [⟨252, bytes []⟩]) := by
  decide

/-- Type `253` crosses into the three-byte type field `fd 00 fd`. -/
theorem h38_tlv_type_253_decode :
    decodeTLV (bytes [0xfd, 0x00, 0xfd, 0x00]) =
      some (TLVStream.mk [⟨253, bytes []⟩]) := by
  decide

theorem h38_tlv_type_253_admission :
    decodeAdmissible (bytes [0xfd, 0x00, 0xfd, 0x00]) = true := by
  decide

/-- The adjacent types `65535`/`65536` straddle the three-byte/five-byte type
field transition and remain strictly increasing. -/
theorem h38_tlv_type_class_adjacent_decode :
    decodeTLV (bytes [0xfd, 0xff, 0xff, 0x00, 0xfe, 0x00, 0x01, 0x00, 0x00, 0x00]) =
      some (TLVStream.mk [⟨65535, bytes []⟩, ⟨65536, bytes []⟩]) := by
  decide

theorem h38_tlv_type_class_adjacent_admission :
    decodeAdmissible
        (bytes [0xfd, 0xff, 0xff, 0x00, 0xfe, 0x00, 0x01, 0x00, 0x00, 0x00]) = true := by
  decide

/-! ## TLV: encoder vectors

The existing conformance modules only decode, apart from `encodeTLV_empty`.
These pin the record/stream encoders on concrete input. -/

/-- One record: `BigSize(1) || BigSize(1) || value`. -/
theorem h38_tlv_encode_single_record :
    TLVStream.encode (TLVStream.mk [⟨1, bytes [0x2a]⟩]) =
      bytes [0x01, 0x01, 0x2a] := by
  decide

/-- A five-byte type plus a one-byte length: `fe 00 01 00 00 || 02 || aa bb`. -/
theorem h38_tlv_encode_multibyte_type :
    TLVStream.encode (TLVStream.mk [⟨65536, bytes [0xaa, 0xbb]⟩]) =
      bytes [0xfe, 0x00, 0x01, 0x00, 0x00, 0x02, 0xaa, 0xbb] := by
  decide

/-- The record encoder is exactly the composition of its two BigSize fields and
the value, on a concrete record. -/
theorem h38_tlv_encode_record_bytes :
    TLVRecord.encode ⟨1, bytes [0x2a]⟩ = bytes [0x01, 0x01, 0x2a] := by
  decide

/-! ## TLV: value-length BigSize class transition

A 252-byte value uses the one-byte length field `fc`; a 253-byte value uses the
three-byte field `fd 00 fd`.  Both parse back exactly. -/

theorem h38_tlv_value_length_252_decode :
    decodeTLV (bytes [0x01, 0xfc] ++ repeated 252 0xaa) =
      some (TLVStream.mk [⟨1, repeated 252 0xaa⟩]) := by
  decide

theorem h38_tlv_value_length_253_decode :
    decodeTLV (bytes [0x01, 0xfd, 0x00, 0xfd] ++ repeated 253 0xaa) =
      some (TLVStream.mk [⟨1, repeated 253 0xaa⟩]) := by
  decide

theorem h38_tlv_value_length_253_admission :
    decodeAdmissible (bytes [0x01, 0xfd, 0x00, 0xfd] ++ repeated 253 0xaa) = true := by
  decide

/-! ## Framing: new type boundaries -/

/-- Type `1` with an empty payload: transport length `2`. -/
theorem h38_frame_type_1_empty :
    Transport.transportFrame ⟨1, bytes []⟩ = bytes [0x00, 0x01, 0x00, 0x02] := by
  decide

/-- Type `128` is the first commitment-group type. -/
theorem h38_frame_type_128_first_commitment :
    Transport.transportFrame ⟨128, bytes [0xaa]⟩ =
      bytes [0x00, 0x80, 0x00, 0x03, 0xaa] := by
  decide

/-- Type `32768` is the first custom-message type. -/
theorem h38_frame_type_32768_first_custom :
    Transport.transportFrame ⟨32768, bytes []⟩ = bytes [0x80, 0x00, 0x00, 0x02] := by
  decide

/-- Type `65534` is the last type below the maximal `65535`. -/
theorem h38_frame_type_65534 :
    Transport.transportFrame ⟨65534, bytes []⟩ = bytes [0xff, 0xfe, 0x00, 0x02] := by
  decide

/-! ## Framing: the minimal frame and the two length conventions

`00 10 00 02` is the minimal BOLT 8 transport frame (type `16` = `init`, empty
payload, declared length `2`).  The payload-only decoder reads the declared
field as a payload length, so it rejects exactly these four bytes.  This is the
concrete instance of the generic `unframe_transportFrame_eq_none`; the existing
suite has only the eight-byte four-payload case. -/

theorem h38_frame_minimal_transport_decode :
    Transport.unframeTransport (bytes [0x00, 0x10, 0x00, 0x02]) =
      some ⟨16, bytes []⟩ := by
  decide

theorem h38_payload_decoder_rejects_minimal_transport_frame :
    Wire.unframe (bytes [0x00, 0x10, 0x00, 0x02]) = none := by
  decide

/-- The corresponding payload-only frame: declared length `0`, not `2`. -/
theorem h38_payload_frame_empty :
    Wire.frame ⟨16, bytes []⟩ = bytes [0x00, 0x10, 0x00, 0x00] := by
  decide

theorem h38_payload_frame_empty_decode :
    Wire.unframe (bytes [0x00, 0x10, 0x00, 0x00]) = some ⟨16, bytes []⟩ := by
  decide

/-! ## Framing: two-byte header boundaries and short headers -/

/-- The transport length `255 = 0x00ff` still fits a two-byte header. -/
theorem h38_u16BE_255 : u16BE 255 = bytes [0x00, 0xff] := by decide

/-- The transport length `256 = 0x0100` is the first needing the second byte. -/
theorem h38_u16BE_256 : u16BE 256 = bytes [0x01, 0x00] := by decide

theorem h38_frame_reject_one_byte_hint : Transport.unframeTransport (bytes [0x00]) = none := by
  decide

theorem h38_frame_reject_two_byte_hint :
    Transport.unframeTransport (bytes [0x00, 0x10]) = none := by
  decide

/-! ## Vector count and audit note

The module contains 39 `decide` theorems (BigSize 14, TLV 13, framing 12) over
new boundaries only; see the header list.  Each is kernel reduction with no
local assumption and no opaque constant; the audit result is recorded in the
lane report.
-/

end LnLean.Proofs.WaveH.H38
