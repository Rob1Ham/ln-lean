/-
# Wire conformance vector targets (BigSize and TLV)

**What this module is.**  Concrete, machine-checked expectations for the BOLT 1
BigSize and TLV encodings.  Each theorem restates one vector from
`tests/conformance/vectors.json` and closes it by kernel reduction
(`decide`).  The Python checker `scripts/check-conformance.py` validates the
same JSON against an independent reference implementation and cross-checks that
every vector names a theorem declared here.

**What this module is not.**  This is *vector conformance*, not a full
implementation test and not a proof that the Lean model is a complete BOLT 1
implementation.  The vectors cover the modelled encoding/decoding decisions;
they do not cover IO, allocation limits, message-specific value decoding,
namespace/known-type policy, or rust-lightning byte-for-byte behaviour.

**Positive results.**  `Wire.encode` produces the BOLT 1 Appendix A bytes for
all canonical boundary values, `Wire.decode` returns the documented value and
consumed length, and `decodeTLV` parses the sorted/empty streams.

**Negative results (the model's exact boundary).**

* `Wire.decode` rejects every non-minimally encoded BigSize and every short
  read.  This is the model's `Option`-valued canonicality rule.
* `decodeTLV` is structural only: it rejects non-canonical/truncated streams but
  *accepts* duplicate and out-of-order record types.  The BOLT 1 ordering rule
  is enforced by `decodeAdmissible` (from `LnLean.Proofs.Wire.TLVTargets`), and
  the vectors split `parser` from `admission` accordingly.  No theorem
  `decodeTLV b = some s → s.WellFormed` exists; the duplicate/out-of-order
  vectors below are the concrete refutation.
* The model has no namespace or known-type length policy, so BOLT 1 Appendix B
  cases such as an unknown even type (`12 00`) are parsed and admitted.  Those
  vectors are marked `not-modelled` in the JSON; the theorems below record the
  model's actual decision and do **not** claim spec conformance.

**Sources.**  BOLT 1 Appendix A (BigSize vectors), Appendix B (TLV vectors),
pinned at `refs/bolts/01-messaging.md`; the canonicality rule is also anchored
to `lightning/src/util/ser.rs:442-490` in `LnLean/Wire/BigSize.lean`.

**Build.**  Module-only target:
`lake build LnLean.Proofs.ConformanceTargets`.  Root import is intentionally
left to the integrator (`LnLean.lean` is outside this lane's ownership).
-/

import LnLean.Wire.BigSize
import LnLean.Wire.TLV
import LnLean.Proofs.Wire.TLVTargets

namespace LnLean.Proofs.Conformance

set_option autoImplicit false

open LnLean
open LnLean.Wire

/-- Byte-array literal used by every vector statement. -/
def bytes (l : List UInt8) : ByteArray := l.toByteArray

/-! ## BigSize: canonical encodings

The twelve values below include every BOLT 1 Appendix A encoding vector plus the
two interior boundaries `0xfe`/`0xff` (254, 255) and `0x100` (256) that sit
between the published endpoints. -/

theorem bigsize_encode_zero : Wire.encode 0 = bytes [0x00] := by decide

theorem bigsize_encode_one : Wire.encode 1 = bytes [0x01] := by decide

theorem bigsize_encode_one_byte_high : Wire.encode 252 = bytes [0xfc] := by decide

theorem bigsize_encode_two_byte_low : Wire.encode 253 = bytes [0xfd, 0x00, 0xfd] := by decide

theorem bigsize_encode_two_byte_254 : Wire.encode 254 = bytes [0xfd, 0x00, 0xfe] := by decide

theorem bigsize_encode_two_byte_255 : Wire.encode 255 = bytes [0xfd, 0x00, 0xff] := by decide

theorem bigsize_encode_two_byte_256 : Wire.encode 256 = bytes [0xfd, 0x01, 0x00] := by decide

theorem bigsize_encode_two_byte_high : Wire.encode 65535 = bytes [0xfd, 0xff, 0xff] := by decide

theorem bigsize_encode_four_byte_low :
    Wire.encode 65536 = bytes [0xfe, 0x00, 0x01, 0x00, 0x00] := by decide

theorem bigsize_encode_four_byte_high :
    Wire.encode 4294967295 = bytes [0xfe, 0xff, 0xff, 0xff, 0xff] := by decide

theorem bigsize_encode_eight_byte_low :
    Wire.encode 4294967296 = bytes [0xff, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00] := by
  decide

theorem bigsize_encode_eight_byte_high :
    Wire.encode 18446744073709551615 =
      bytes [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] := by
  decide

/-- The encoded length of every canonical vector is the BOLT 1 length class
(1, 3, 5, or 9 bytes). -/
theorem bigsize_encode_lengths :
    (Wire.encode 0).size = 1 ∧
    (Wire.encode 252).size = 1 ∧
    (Wire.encode 253).size = 3 ∧
    (Wire.encode 65535).size = 3 ∧
    (Wire.encode 65536).size = 5 ∧
    (Wire.encode 4294967295).size = 5 ∧
    (Wire.encode 4294967296).size = 9 ∧
    (Wire.encode 18446744073709551615).size = 9 := by
  decide

/-! ## BigSize: accepted decodes

Each theorem records the value and the number of bytes consumed.  The last one
documents that `Wire.decode` is a streaming decoder: trailing bytes are left
unconsumed rather than rejected. -/

theorem bigsize_decode_zero : Wire.decode (bytes [0x00]) = some (0, 1) := by decide

theorem bigsize_decode_one_byte_high :
    Wire.decode (bytes [0xfc]) = some (252, 1) := by decide

theorem bigsize_decode_two_byte_low :
    Wire.decode (bytes [0xfd, 0x00, 0xfd]) = some (253, 3) := by decide

theorem bigsize_decode_two_byte_254 :
    Wire.decode (bytes [0xfd, 0x00, 0xfe]) = some (254, 3) := by decide

theorem bigsize_decode_two_byte_255 :
    Wire.decode (bytes [0xfd, 0x00, 0xff]) = some (255, 3) := by decide

theorem bigsize_decode_two_byte_256 :
    Wire.decode (bytes [0xfd, 0x01, 0x00]) = some (256, 3) := by decide

theorem bigsize_decode_two_byte_high :
    Wire.decode (bytes [0xfd, 0xff, 0xff]) = some (65535, 3) := by decide

theorem bigsize_decode_four_byte_low :
    Wire.decode (bytes [0xfe, 0x00, 0x01, 0x00, 0x00]) = some (65536, 5) := by decide

theorem bigsize_decode_four_byte_high :
    Wire.decode (bytes [0xfe, 0xff, 0xff, 0xff, 0xff]) = some (4294967295, 5) := by decide

theorem bigsize_decode_eight_byte_low :
    Wire.decode (bytes [0xff, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00]) =
      some (4294967296, 9) := by
  decide

theorem bigsize_decode_eight_byte_high :
    Wire.decode
        (bytes [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]) =
      some (18446744073709551615, 9) := by
  decide

theorem bigsize_decode_trailing_ignored :
    Wire.decode (bytes [0x00, 0xff]) = some (0, 1) := by decide

/-! ## BigSize: rejected decodes

Every BOLT 1 Appendix A non-canonical and short-read vector, plus the zero-value
encodings in the `0xfd`/`0xfe`/`0xff` classes that the appendix covers
indirectly. -/

theorem bigsize_reject_noncanonical_two :
    Wire.decode (bytes [0xfd, 0x00, 0xfc]) = none := by decide

theorem bigsize_reject_noncanonical_two_zero :
    Wire.decode (bytes [0xfd, 0x00, 0x00]) = none := by decide

theorem bigsize_reject_noncanonical_four :
    Wire.decode (bytes [0xfe, 0x00, 0x00, 0xff, 0xff]) = none := by decide

theorem bigsize_reject_noncanonical_four_zero :
    Wire.decode (bytes [0xfe, 0x00, 0x00, 0x00, 0x00]) = none := by decide

theorem bigsize_reject_noncanonical_eight :
    Wire.decode (bytes [0xff, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0xff, 0xff]) = none := by
  decide

theorem bigsize_reject_noncanonical_eight_zero :
    Wire.decode (bytes [0xff, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]) = none := by
  decide

theorem bigsize_reject_short_two : Wire.decode (bytes [0xfd, 0x00]) = none := by decide

theorem bigsize_reject_short_four :
    Wire.decode (bytes [0xfe, 0xff, 0xff]) = none := by decide

theorem bigsize_reject_short_eight :
    Wire.decode (bytes [0xff, 0xff, 0xff, 0xff, 0xff]) = none := by decide

theorem bigsize_reject_empty : Wire.decode (bytes []) = none := by decide

theorem bigsize_reject_tag_only_two : Wire.decode (bytes [0xfd]) = none := by decide

theorem bigsize_reject_tag_only_four : Wire.decode (bytes [0xfe]) = none := by decide

theorem bigsize_reject_tag_only_eight : Wire.decode (bytes [0xff]) = none := by decide

/-! ## TLV: empty and sorted streams

The reference parser accepts these and the BOLT 1 ordering admission accepts
them.  `tlv_empty` is the Appendix B empty-message case; `tlv_sorted_three_254`
is the `n1` `tlv4` stream (`fd00fe 02 0226`) preceded by records 1 and 2. -/

theorem tlv_empty_decode :
    decodeTLV (bytes []) = some (TLVStream.mk []) := by decide

theorem tlv_empty_admission : decodeAdmissible (bytes []) = true := by decide

theorem tlv_sorted_single_decode :
    decodeTLV (bytes [0x01, 0x01, 0x2a]) =
      some (TLVStream.mk [⟨1, bytes [0x2a]⟩]) := by
  decide

theorem tlv_sorted_single_admission :
    decodeAdmissible (bytes [0x01, 0x01, 0x2a]) = true := by decide

theorem tlv_sorted_two_decode :
    decodeTLV (bytes [0x01, 0x01, 0x2a, 0x02, 0x02, 0x2b, 0x2c]) =
      some (TLVStream.mk
        [⟨1, bytes [0x2a]⟩, ⟨2, bytes [0x2b, 0x2c]⟩]) := by
  decide

theorem tlv_sorted_two_admission :
    decodeAdmissible (bytes [0x01, 0x01, 0x2a, 0x02, 0x02, 0x2b, 0x2c]) = true := by
  decide

theorem tlv_sorted_three_254_decode :
    decodeTLV
        (bytes [0x01, 0x00, 0x02, 0x01, 0xff, 0xfd, 0x00, 0xfe, 0x02, 0x02, 0x26]) =
      some (TLVStream.mk
        [⟨1, bytes []⟩, ⟨2, bytes [0xff]⟩, ⟨254, bytes [0x02, 0x26]⟩]) := by
  decide

theorem tlv_sorted_three_254_admission :
    decodeAdmissible
        (bytes [0x01, 0x00, 0x02, 0x01, 0xff, 0xfd, 0x00, 0xfe, 0x02, 0x02, 0x26]) = true := by
  decide

theorem tlv_type_65535_decode :
    decodeTLV (bytes [0xfd, 0xff, 0xff, 0x00]) =
      some (TLVStream.mk [⟨65535, bytes []⟩]) := by
  decide

theorem tlv_type_65535_admission :
    decodeAdmissible (bytes [0xfd, 0xff, 0xff, 0x00]) = true := by decide

theorem tlv_type_65536_decode :
    decodeTLV (bytes [0xfe, 0x00, 0x01, 0x00, 0x00, 0x00]) =
      some (TLVStream.mk [⟨65536, bytes []⟩]) := by
  decide

theorem tlv_type_65536_admission :
    decodeAdmissible (bytes [0xfe, 0x00, 0x01, 0x00, 0x00, 0x00]) = true := by decide

/-- The largest type representable in the BigSize `uint64` domain. -/
theorem tlv_max_type_decode :
    decodeTLV
        (bytes [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x00]) =
      some (TLVStream.mk [⟨18446744073709551615, bytes []⟩]) := by
  decide

theorem tlv_max_type_admission :
    decodeAdmissible
        (bytes [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x00]) = true := by
  decide

/-! ## TLV: duplicate and out-of-order types

The structural parser accepts all four streams.  The BOLT 1 ordering
admission rejects them.  These are the concrete witnesses that `decodeTLV`
alone is not an ordering-enforcing decoder. -/

theorem tlv_duplicate_type_decode :
    decodeTLV (bytes [0x01, 0x01, 0x2a, 0x01, 0x01, 0x2b]) =
      some (TLVStream.mk [⟨1, bytes [0x2a]⟩, ⟨1, bytes [0x2b]⟩]) := by
  decide

theorem tlv_duplicate_type_admission :
    decodeAdmissible (bytes [0x01, 0x01, 0x2a, 0x01, 0x01, 0x2b]) = false := by decide

theorem tlv_out_of_order_decode :
    decodeTLV (bytes [0x02, 0x01, 0x2a, 0x01, 0x01, 0x2b]) =
      some (TLVStream.mk [⟨2, bytes [0x2a]⟩, ⟨1, bytes [0x2b]⟩]) := by
  decide

theorem tlv_out_of_order_admission :
    decodeAdmissible (bytes [0x02, 0x01, 0x2a, 0x01, 0x01, 0x2b]) = false := by decide

theorem tlv_bolt_unsorted_1f_0f_decode :
    decodeTLV (bytes [0x1f, 0x00, 0x0f, 0x01, 0x2a]) =
      some (TLVStream.mk [⟨31, bytes []⟩, ⟨15, bytes [0x2a]⟩]) := by
  decide

theorem tlv_bolt_unsorted_1f_0f_admission :
    decodeAdmissible (bytes [0x1f, 0x00, 0x0f, 0x01, 0x2a]) = false := by decide

theorem tlv_bolt_duplicate_1f_decode :
    decodeTLV (bytes [0x1f, 0x00, 0x1f, 0x01, 0x2a]) =
      some (TLVStream.mk [⟨31, bytes []⟩, ⟨31, bytes [0x2a]⟩]) := by
  decide

theorem tlv_bolt_duplicate_1f_admission :
    decodeAdmissible (bytes [0x1f, 0x00, 0x1f, 0x01, 0x2a]) = false := by decide

/-! ## TLV: out-of-domain and non-canonical fields

The type `2^64` and the length `2^64` are outside the BigSize domain.  `encode`
truncates them to eight zero bytes, which is non-minimal, so both the parser and
the admission check reject the stream.  The smaller non-canonical fields are
rejected by `Wire.decode` before TLV structure matters. -/

theorem tlv_out_of_domain_type_2_64_decode :
    decodeTLV
        (bytes [0xff, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]) = none := by
  decide

theorem tlv_out_of_domain_type_2_64_admission :
    decodeAdmissible
        (bytes [0xff, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]) = false := by
  decide

theorem tlv_out_of_domain_length_2_64_decode :
    decodeTLV
        (bytes [0x01, 0xff, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]) = none := by
  decide

theorem tlv_out_of_domain_length_2_64_admission :
    decodeAdmissible
        (bytes [0x01, 0xff, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]) = false := by
  decide

theorem tlv_noncanonical_type_fe_zero_decode :
    decodeTLV (bytes [0xfe, 0x00, 0x00, 0x00, 0x00, 0x00]) = none := by decide

theorem tlv_noncanonical_type_fe_zero_admission :
    decodeAdmissible (bytes [0xfe, 0x00, 0x00, 0x00, 0x00, 0x00]) = false := by decide

theorem tlv_noncanonical_length_fd_zero_decode :
    decodeTLV (bytes [0x01, 0xfd, 0x00, 0x00]) = none := by decide

theorem tlv_noncanonical_length_fd_zero_admission :
    decodeAdmissible (bytes [0x01, 0xfd, 0x00, 0x00]) = false := by decide

/-! ## TLV: truncated streams

All of these fail structurally: a short BigSize, a missing length, or a value
shorter than the declared length. -/

theorem tlv_truncated_type_fd_decode : decodeTLV (bytes [0xfd]) = none := by decide

theorem tlv_truncated_type_fd_admission : decodeAdmissible (bytes [0xfd]) = false := by
  decide

theorem tlv_truncated_type_fd01_decode : decodeTLV (bytes [0xfd, 0x01]) = none := by decide

theorem tlv_truncated_type_fd01_admission : decodeAdmissible (bytes [0xfd, 0x01]) = false := by
  decide

theorem tlv_missing_length_decode : decodeTLV (bytes [0xfd, 0x01, 0x01]) = none := by decide

theorem tlv_missing_length_admission :
    decodeAdmissible (bytes [0xfd, 0x01, 0x01]) = false := by decide

theorem tlv_truncated_length_fd_decode : decodeTLV (bytes [0x0f, 0xfd]) = none := by decide

theorem tlv_truncated_length_fd_admission :
    decodeAdmissible (bytes [0x0f, 0xfd]) = false := by decide

theorem tlv_truncated_length_fd26_decode : decodeTLV (bytes [0x0f, 0xfd, 0x26]) = none := by
  decide

theorem tlv_truncated_length_fd26_admission :
    decodeAdmissible (bytes [0x0f, 0xfd, 0x26]) = false := by decide

theorem tlv_truncated_value_decode :
    decodeTLV (bytes [0x0f, 0xfd, 0x26, 0x02]) = none := by decide

theorem tlv_truncated_value_admission :
    decodeAdmissible (bytes [0x0f, 0xfd, 0x26, 0x02]) = false := by decide

theorem tlv_value_truncated_small_decode :
    decodeTLV (bytes [0x01, 0x03, 0x2a, 0x2b]) = none := by decide

theorem tlv_value_truncated_small_admission :
    decodeAdmissible (bytes [0x01, 0x03, 0x2a, 0x2b]) = false := by decide

/-! ## TLV: declared scope gaps (not BOLT conformance)

These vectors are accepted by the model but would be rejected by BOLT 1 under a
namespace/known-type policy.  The theorems record the model's actual decision;
they are *not* positive conformance claims.  The JSON marks both cases
`not-modelled`. -/

/-- BOLT 1 Appendix B: `12 00` is an unknown **even** type and must be rejected
by a namespace-aware decoder.  The model has no namespace policy, so the
structural parser and the ordering admission both accept it. -/
theorem tlv_unknown_even_12_decode :
    decodeTLV (bytes [0x12, 0x00]) =
      some (TLVStream.mk [⟨18, bytes []⟩]) := by
  decide

theorem tlv_unknown_even_12_admission :
    decodeAdmissible (bytes [0x12, 0x00]) = true := by decide

/-- BOLT 1 Appendix B: for `n1` type 1 (`tu64 amount_msat`), `01 02 0001` is a
non-minimal value encoding and must be rejected.  The model treats TLV values as
opaque bytes, so it accepts the record. -/
theorem tlv_known_type_nonminimal_value_decode :
    decodeTLV (bytes [0x01, 0x02, 0x00, 0x01]) =
      some (TLVStream.mk [⟨1, bytes [0x00, 0x01]⟩]) := by
  decide

theorem tlv_known_type_nonminimal_value_admission :
    decodeAdmissible (bytes [0x01, 0x02, 0x00, 0x01]) = true := by decide

/-! ## Vector count

A single closed theorem pinning the number of BigSize and TLV expectations is
not useful by itself; the count is maintained in the JSON and the report.  The
`#print axioms` audit covers every declaration above. -/

end LnLean.Proofs.Conformance
