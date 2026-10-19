/-
# H35 — BigSize boundary vectors and minimality (CONF-01)

**Catalog issue.**  `CONF-01` (P2): the shared conformance suite is finite-vector
conformance, and the wave-8 task is to add more BOLT 1 BigSize boundary
vectors.  The shared fixtures (`tests/conformance/**`), the checker and
`LnLean/Proofs/ConformanceTargets.lean` are integrator-owned, so this module
keeps its new vector set local.

**What this module is.**  A self-contained BigSize vector and minimality module:

1. **Boundary encodings.**  The canonical bytes of
   `0`, `252`, `253`, `65535`, `65536`, and the larger-width representatives
   `16777215`, `16777216`, `4294967295`, `4294967296`, `2^63` and `2^64-1`
   are pinned with `decide` on the concrete literals.
2. **Round trips.**  For each of those values `decode (encode n)` returns
   `some (n, k)` with the exact BOLT 1 width class `k ∈ {1,3,5,9}`.  These are
   concrete (`decide`) instances of the general
   `LnLean.Wire.decode_encode` theorem.
3. **Minimality.**  `encode` is proved to use exactly the narrowest class, and
   the decoder is proved to reject every *wider* class carrying the same value.
   The generic theorems `decode_wideForm_fd_below`,
   `decode_wideForm_fe_below` and `decode_wideForm_ff_below` are proved for
   **all** `Nat` values in the offending range, not just the concrete vectors;
   `minimality_lt_0xfd`, `minimality_le_ffff`,
   `minimality_le_ffffffff` and `minimality_gt_ffffffff` package the exact
   class membership and the rejected wider forms.
4. **Rejection vectors.**  Concrete non-minimal encodings, short reads, empty
   input and tag-only inputs all decode to `none`.
5. **Domain boundary.**  `2^64` is outside the model's `uint64` domain: `encode`
   truncates it to eight zero payload bytes, which is the non-minimal `0xff`
   form, so `decode` rejects it.  A concrete collision
   (`encode (2^64 + 2^32) = encode 2^32`) records that `encode` is *not*
   injective above the domain; the round-trip law therefore genuinely needs
   its `n < 2^64` hypothesis.

**What this module is not.**  It is still finite-vector conformance plus
class-level minimality for the model `LnLean.Wire.encode`/`decode`.  It does not
test IO, allocation limits (`MAX_BUF_SIZE`), byte-cursor behaviour, streaming
concatenation, or rust-lightning byte-for-byte behaviour, and it does not edit
or extend the shared `vectors.json` fixture set.  No full implementation test is
claimed.

**BOLT sections.**  BOLT 1 §Appendix A: BigSize Test Vectors (canonical bytes
and the "minimally encoded" requirement); BOLT 1 §Type-Length-Value Format
(BigSize is used for TLV type and length).

**Anchors.**  Model `LnLean/Wire/BigSize.lean` (`encode`, `decode`,
`decodePayload`, `decode_encode`); shared vector module
`LnLean/Proofs/ConformanceTargets.lean`; proofs of the class lemmas
`LnLean/Proofs/Wire/TLVProps.lean`.  rust-lightning
`lightning/src/util/ser.rs:442-490` for the canonicality checks and
`lightning/src/util/ser.rs:62` for `MAX_BUF_SIZE`.

**Build.**  Module-only target `lake build LnLean.Proofs.WaveH.H35`.  The root
import is left to the integrator (`LnLean.lean` is outside this lane).
-/

import LnLean.Proofs.Wire.TLVProps

namespace LnLean.Proofs.WaveH.H35

set_option autoImplicit false

open LnLean
open LnLean.Wire

/-- Byte-array literal used by every vector statement. -/
def bytes (l : List UInt8) : ByteArray := l.toByteArray

/-! ## Canonical boundary encodings

Every statement is `decide` on a concrete, bounded byte literal.  The values
cover all four BOLT 1 width classes and both sides of every class boundary. -/

theorem bigsize_encode_zero : encode 0 = bytes [0x00] := by decide

theorem bigsize_encode_252 : encode 252 = bytes [0xfc] := by decide

theorem bigsize_encode_253 : encode 253 = bytes [0xfd, 0x00, 0xfd] := by decide

theorem bigsize_encode_65535 : encode 65535 = bytes [0xfd, 0xff, 0xff] := by decide

theorem bigsize_encode_65536 :
    encode 65536 = bytes [0xfe, 0x00, 0x01, 0x00, 0x00] := by decide

theorem bigsize_encode_16777215 :
    encode 16777215 = bytes [0xfe, 0x00, 0xff, 0xff, 0xff] := by decide

theorem bigsize_encode_16777216 :
    encode 16777216 = bytes [0xfe, 0x01, 0x00, 0x00, 0x00] := by decide

theorem bigsize_encode_4294967295 :
    encode 4294967295 = bytes [0xfe, 0xff, 0xff, 0xff, 0xff] := by decide

theorem bigsize_encode_4294967296 :
    encode 4294967296 =
      bytes [0xff, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00] := by
  decide

theorem bigsize_encode_2p63 :
    encode 9223372036854775808 =
      bytes [0xff, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] := by
  decide

theorem bigsize_encode_max :
    encode 18446744073709551615 =
      bytes [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] := by
  decide

/-! ## Canonical boundary decodes

The decoder returns the value and the number of bytes consumed. -/

theorem bigsize_decode_zero : decode (bytes [0x00]) = some (0, 1) := by decide

theorem bigsize_decode_252 : decode (bytes [0xfc]) = some (252, 1) := by decide

theorem bigsize_decode_253 :
    decode (bytes [0xfd, 0x00, 0xfd]) = some (253, 3) := by decide

theorem bigsize_decode_65535 :
    decode (bytes [0xfd, 0xff, 0xff]) = some (65535, 3) := by decide

theorem bigsize_decode_65536 :
    decode (bytes [0xfe, 0x00, 0x01, 0x00, 0x00]) = some (65536, 5) := by decide

theorem bigsize_decode_16777215 :
    decode (bytes [0xfe, 0x00, 0xff, 0xff, 0xff]) = some (16777215, 5) := by decide

theorem bigsize_decode_16777216 :
    decode (bytes [0xfe, 0x01, 0x00, 0x00, 0x00]) = some (16777216, 5) := by
  decide

theorem bigsize_decode_4294967295 :
    decode (bytes [0xfe, 0xff, 0xff, 0xff, 0xff]) = some (4294967295, 5) := by
  decide

theorem bigsize_decode_4294967296 :
    decode (bytes [0xff, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00]) =
      some (4294967296, 9) := by
  decide

theorem bigsize_decode_2p63 :
    decode (bytes [0xff, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]) =
      some (9223372036854775808, 9) := by
  decide

theorem bigsize_decode_max :
    decode (bytes [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]) =
      some (18446744073709551615, 9) := by
  decide

/-! ## Encode/decode round trips at the boundaries -/

theorem bigsize_roundtrip_zero : decode (encode 0) = some (0, 1) := by decide

theorem bigsize_roundtrip_252 : decode (encode 252) = some (252, 1) := by decide

theorem bigsize_roundtrip_253 : decode (encode 253) = some (253, 3) := by decide

theorem bigsize_roundtrip_65535 : decode (encode 65535) = some (65535, 3) := by
  decide

theorem bigsize_roundtrip_65536 : decode (encode 65536) = some (65536, 5) := by
  decide

theorem bigsize_roundtrip_16777215 :
    decode (encode 16777215) = some (16777215, 5) := by decide

theorem bigsize_roundtrip_16777216 :
    decode (encode 16777216) = some (16777216, 5) := by decide

theorem bigsize_roundtrip_4294967295 :
    decode (encode 4294967295) = some (4294967295, 5) := by decide

theorem bigsize_roundtrip_4294967296 :
    decode (encode 4294967296) = some (4294967296, 9) := by decide

theorem bigsize_roundtrip_2p63 :
    decode (encode 9223372036854775808) = some (9223372036854775808, 9) := by
  decide

theorem bigsize_roundtrip_max :
    decode (encode 18446744073709551615) = some (18446744073709551615, 9) := by
  decide

/-- The width classes of the boundary vectors in one closed statement. -/
theorem bigsize_boundary_lengths :
    (encode 0).size = 1 ∧
    (encode 252).size = 1 ∧
    (encode 253).size = 3 ∧
    (encode 65535).size = 3 ∧
    (encode 65536).size = 5 ∧
    (encode 16777215).size = 5 ∧
    (encode 16777216).size = 5 ∧
    (encode 4294967295).size = 5 ∧
    (encode 4294967296).size = 9 ∧
    (encode 9223372036854775808).size = 9 ∧
    (encode 18446744073709551615).size = 9 := by
  decide

/-! ## Generic minimality: the decoder rejects every wider form

`wideForm tag n w` is the raw `tag || w-byte big-endian n` encoding.  The three
lemmas below are proved for arbitrary `Nat` values, so they are minimality
laws rather than vector checks: a value that belongs to a narrower class is
rejected when it is re-encoded in any wider class. -/

/-- The raw `tag`-prefixed fixed-width encoding. -/
def wideForm (tag : UInt8) (n w : Nat) : ByteArray :=
  oneByte tag ++ beBytes n w

/-- The byte list of a `wideForm` is the tag followed by the payload bytes. -/
theorem bytesToList_wideForm (tag : UInt8) (n w : Nat) :
    bytesToList (wideForm tag n w) = tag :: beBytesAux w n [] := by
  simp [wideForm, bytesToList_append, bytesToList_oneByte, bytesToList_beBytes]

/-- A `0xfd`-tagged two-byte payload below `0xfd` is non-minimal: `decodePayload`
returns `none`. -/
theorem decodePayload_fd_below (n : Nat) (hn : n < 0xfd) (rest : List UInt8) :
    decodePayload 0xfd 2 (beBytesAux 2 n [] ++ rest) = none := by
  unfold decodePayload
  have hlen : (beBytesAux 2 n [] ++ rest).length = 2 + rest.length := by
    rw [List.length_append, beBytesAux_length]
    simp
  rw [ite_eq_right (by omega)]
  have htake : List.take 2 (beBytesAux 2 n [] ++ rest) = beBytesAux 2 n [] := by
    rw [show 2 = (beBytesAux 2 n []).length by simp [beBytesAux_length]]
    exact List.take_left
  rw [htake, decodeBEList_beBytesAux]
  simp only [List.length_nil]
  have hlt : n < 256 ^ 2 := by
    have hp : 256 ^ 2 = 65536 := by decide
    omega
  rw [Nat.mod_eq_of_lt hlt]
  simp [decodeBEList, hn]

/-- A `0xfe`-tagged four-byte payload below `0x10000` is non-minimal. -/
theorem decodePayload_fe_below (n : Nat) (hn : n < 0x10000) (rest : List UInt8) :
    decodePayload 0xfe 4 (beBytesAux 4 n [] ++ rest) = none := by
  unfold decodePayload
  have hlen : (beBytesAux 4 n [] ++ rest).length = 4 + rest.length := by
    rw [List.length_append, beBytesAux_length]
    simp
  rw [ite_eq_right (by omega)]
  have htake : List.take 4 (beBytesAux 4 n [] ++ rest) = beBytesAux 4 n [] := by
    rw [show 4 = (beBytesAux 4 n []).length by simp [beBytesAux_length]]
    exact List.take_left
  rw [htake, decodeBEList_beBytesAux]
  simp only [List.length_nil]
  have hlt : n < 256 ^ 4 := by
    have hp : 256 ^ 4 = 4294967296 := by decide
    omega
  rw [Nat.mod_eq_of_lt hlt]
  simp [decodeBEList, hn]

/-- A `0xff`-tagged eight-byte payload below `0x100000000` is non-minimal. -/
theorem decodePayload_ff_below (n : Nat) (hn : n < 0x100000000) (rest : List UInt8) :
    decodePayload 0xff 8 (beBytesAux 8 n [] ++ rest) = none := by
  unfold decodePayload
  have hlen : (beBytesAux 8 n [] ++ rest).length = 8 + rest.length := by
    rw [List.length_append, beBytesAux_length]
    simp
  rw [ite_eq_right (by omega)]
  have htake : List.take 8 (beBytesAux 8 n [] ++ rest) = beBytesAux 8 n [] := by
    rw [show 8 = (beBytesAux 8 n []).length by simp [beBytesAux_length]]
    exact List.take_left
  rw [htake, decodeBEList_beBytesAux]
  simp only [List.length_nil]
  have hlt : n < 256 ^ 8 := by
    have hp : 256 ^ 8 = 18446744073709551616 := by decide
    omega
  rw [Nat.mod_eq_of_lt hlt]
  simp [decodeBEList, hn]

/-- Decoding the wider `0xfd` form of a value below `0xfd` fails. -/
theorem decode_wideForm_fd_below (n : Nat) (hn : n < 0xfd) :
    decode (wideForm 0xfd n 2) = none := by
  unfold decode
  rw [bytesToList_wideForm]
  simpa using decodePayload_fd_below n hn ([] : List UInt8)

/-- Decoding the wider `0xfe` form of a value below `0x10000` fails. -/
theorem decode_wideForm_fe_below (n : Nat) (hn : n < 0x10000) :
    decode (wideForm 0xfe n 4) = none := by
  unfold decode
  rw [bytesToList_wideForm]
  simpa using decodePayload_fe_below n hn ([] : List UInt8)

/-- Decoding the wider `0xff` form of a value below `0x100000000` fails. -/
theorem decode_wideForm_ff_below (n : Nat) (hn : n < 0x100000000) :
    decode (wideForm 0xff n 8) = none := by
  unfold decode
  rw [bytesToList_wideForm]
  simpa using decodePayload_ff_below n hn ([] : List UInt8)

/-! ## Generic minimality: the canonical class is accepted

The companions of the rejection lemmas: the exact class boundaries are the
accepted ranges of `decodePayload`. -/

/-- The canonical `0xfd` form decodes to the two-byte-class value. -/
theorem decodePayload_fd_canonical (n : Nat) (h1 : 0xfd ≤ n) (h2 : n ≤ 0xffff)
    (rest : List UInt8) :
    decodePayload 0xfd 2 (beBytesAux 2 n [] ++ rest) = some (n, 3) := by
  unfold decodePayload
  have hlen : (beBytesAux 2 n [] ++ rest).length = 2 + rest.length := by
    rw [List.length_append, beBytesAux_length]
    simp
  rw [ite_eq_right (by omega)]
  have htake : List.take 2 (beBytesAux 2 n [] ++ rest) = beBytesAux 2 n [] := by
    rw [show 2 = (beBytesAux 2 n []).length by simp [beBytesAux_length]]
    exact List.take_left
  rw [htake, decodeBEList_beBytesAux]
  simp only [List.length_nil]
  have hlt : n < 256 ^ 2 := by
    have hp : 256 ^ 2 = 65536 := by decide
    omega
  rw [Nat.mod_eq_of_lt hlt]
  simp [decodeBEList, h1, h2]

/-- The canonical `0xfe` form decodes to the four-byte-class value. -/
theorem decodePayload_fe_canonical (n : Nat) (h1 : 0x10000 ≤ n)
    (h2 : n ≤ 0xffffffff) (rest : List UInt8) :
    decodePayload 0xfe 4 (beBytesAux 4 n [] ++ rest) = some (n, 5) := by
  unfold decodePayload
  have hlen : (beBytesAux 4 n [] ++ rest).length = 4 + rest.length := by
    rw [List.length_append, beBytesAux_length]
    simp
  rw [ite_eq_right (by omega)]
  have htake : List.take 4 (beBytesAux 4 n [] ++ rest) = beBytesAux 4 n [] := by
    rw [show 4 = (beBytesAux 4 n []).length by simp [beBytesAux_length]]
    exact List.take_left
  rw [htake, decodeBEList_beBytesAux]
  simp only [List.length_nil]
  have hlt : n < 256 ^ 4 := by
    have hp : 256 ^ 4 = 4294967296 := by decide
    omega
  rw [Nat.mod_eq_of_lt hlt]
  simp [decodeBEList, h1, h2]

/-- The canonical `0xff` form decodes to the eight-byte-class value. -/
theorem decodePayload_ff_canonical (n : Nat) (h1 : 0x100000000 ≤ n)
    (h2 : n < 18446744073709551616) (rest : List UInt8) :
    decodePayload 0xff 8 (beBytesAux 8 n [] ++ rest) = some (n, 9) := by
  unfold decodePayload
  have hlen : (beBytesAux 8 n [] ++ rest).length = 8 + rest.length := by
    rw [List.length_append, beBytesAux_length]
    simp
  rw [ite_eq_right (by omega)]
  have htake : List.take 8 (beBytesAux 8 n [] ++ rest) = beBytesAux 8 n [] := by
    rw [show 8 = (beBytesAux 8 n []).length by simp [beBytesAux_length]]
    exact List.take_left
  rw [htake, decodeBEList_beBytesAux]
  simp only [List.length_nil]
  have hlt : n < 256 ^ 8 := by
    have hp : 256 ^ 8 = 18446744073709551616 := by decide
    omega
  rw [Nat.mod_eq_of_lt hlt]
  simp [decodeBEList, h1]

/-- The canonical `0xfd` form of an in-class value decodes. -/
theorem decode_wideForm_fd (n : Nat) (h1 : 0xfd ≤ n) (h2 : n ≤ 0xffff) :
    decode (wideForm 0xfd n 2) = some (n, 3) := by
  unfold decode
  rw [bytesToList_wideForm]
  simpa using decodePayload_fd_canonical n h1 h2 ([] : List UInt8)

/-- The canonical `0xfe` form of an in-class value decodes. -/
theorem decode_wideForm_fe (n : Nat) (h1 : 0x10000 ≤ n) (h2 : n ≤ 0xffffffff) :
    decode (wideForm 0xfe n 4) = some (n, 5) := by
  unfold decode
  rw [bytesToList_wideForm]
  simpa using decodePayload_fe_canonical n h1 h2 ([] : List UInt8)

/-- The canonical `0xff` form of an in-class value decodes. -/
theorem decode_wideForm_ff (n : Nat) (h1 : 0x100000000 ≤ n)
    (h2 : n < 18446744073709551616) :
    decode (wideForm 0xff n 8) = some (n, 9) := by
  unfold decode
  rw [bytesToList_wideForm]
  simpa using decodePayload_ff_canonical n h1 h2 ([] : List UInt8)

/-! ## `encode` is exactly the canonical wide form -/

/-- Below `0xfd`, `encode` is the single-byte form. -/
theorem encode_eq_oneByte (n : Nat) (hn : n < 0xfd) :
    encode n = oneByte n.toUInt8 := by
  simp [encode, hn]

/-- In `0xfd..0xffff`, `encode` is the `0xfd` wide form. -/
theorem encode_eq_wideForm_fd (n : Nat) (h1 : 0xfd ≤ n) (h2 : n ≤ 0xffff) :
    encode n = wideForm 0xfd n 2 := by
  simp [encode, wideForm, Nat.not_lt.mpr h1, h2]

/-- In `0x10000..0xffffffff`, `encode` is the `0xfe` wide form. -/
theorem encode_eq_wideForm_fe (n : Nat) (h1 : 0x10000 ≤ n) (h2 : n ≤ 0xffffffff) :
    encode n = wideForm 0xfe n 4 := by
  have hlt : ¬ n < 0xfd := by omega
  have hgt : ¬ n ≤ 0xffff := by omega
  simp [encode, wideForm, hlt, hgt, h2]

/-- Above `0xffffffff`, `encode` is the `0xff` wide form. -/
theorem encode_eq_wideForm_ff (n : Nat) (h : 0xffffffff < n) :
    encode n = wideForm 0xff n 8 := by
  have hlt : ¬ n < 0xfd := by omega
  have hgt : ¬ n ≤ 0xffff := by omega
  have hgt2 : ¬ n ≤ 0xffffffff := by omega
  simp [encode, wideForm, hlt, hgt, hgt2]

/-! ## Minimality packages

Each theorem states (a) the exact width class used by `encode`, (b) that no
narrower class is used, and (c) that every wider class carrying the same value
is rejected by `decode`.  Together these are the model's minimal-encoding
guarantee at the class level. -/

/-- Minimality for the one-byte class. -/
theorem minimality_lt_0xfd (n : Nat) (hn : n < 0xfd) :
    (encode n).size = 1 ∧
      decode (wideForm 0xfd n 2) = none ∧
      decode (wideForm 0xfe n 4) = none ∧
      decode (wideForm 0xff n 8) = none :=
  ⟨encode_size_lt_0xfd n hn,
   decode_wideForm_fd_below n hn,
   decode_wideForm_fe_below n (by omega),
   decode_wideForm_ff_below n (by omega)⟩

/-- Minimality for the three-byte class. -/
theorem minimality_le_ffff (n : Nat) (h1 : 0xfd ≤ n) (h2 : n ≤ 0xffff) :
    (encode n).size = 3 ∧
      ¬ (encode n).size = 1 ∧
      decode (wideForm 0xfe n 4) = none ∧
      decode (wideForm 0xff n 8) = none := by
  have h3 : (encode n).size = 3 := encode_size_le_0xffff n h1 h2
  exact ⟨h3, by omega,
    decode_wideForm_fe_below n (by omega),
    decode_wideForm_ff_below n (by omega)⟩

/-- Minimality for the five-byte class. -/
theorem minimality_le_ffffffff (n : Nat) (h1 : 0x10000 ≤ n)
    (h2 : n ≤ 0xffffffff) :
    (encode n).size = 5 ∧
      ¬ (encode n).size = 1 ∧
      ¬ (encode n).size = 3 ∧
      decode (wideForm 0xff n 8) = none := by
  have h5 : (encode n).size = 5 := encode_size_le_0xffffffff n h1 h2
  exact ⟨h5, by omega, by omega, decode_wideForm_ff_below n (by omega)⟩

/-- Minimality for the nine-byte class.  There is no wider BigSize class. -/
theorem minimality_gt_ffffffff (n : Nat) (h1 : 0xffffffff < n)
    (h2 : n < 18446744073709551616) :
    (encode n).size = 9 ∧
      ¬ (encode n).size = 1 ∧
      ¬ (encode n).size = 3 ∧
      ¬ (encode n).size = 5 := by
  have hdom : n < 18446744073709551616 := h2
  have h9 : (encode n).size = 9 := encode_size_gt_0xffffffff n h1
  exact ⟨h9, by omega, by omega, by omega⟩

/-! ## Concrete rejection vectors (the wider form of each boundary value) -/

theorem bigsize_reject_nonminimal_252 :
    decode (bytes [0xfd, 0x00, 0xfc]) = none := by decide

theorem bigsize_reject_nonminimal_zero_two :
    decode (bytes [0xfd, 0x00, 0x00]) = none := by decide

theorem bigsize_reject_nonminimal_65535 :
    decode (bytes [0xfe, 0x00, 0x00, 0xff, 0xff]) = none := by decide

theorem bigsize_reject_nonminimal_zero_four :
    decode (bytes [0xfe, 0x00, 0x00, 0x00, 0x00]) = none := by decide

theorem bigsize_reject_nonminimal_ffffffff :
    decode (bytes [0xff, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0xff, 0xff]) = none := by
  decide

theorem bigsize_reject_nonminimal_zero_eight :
    decode (bytes [0xff, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]) = none := by
  decide

/-! ## Short reads, empty input and tag-only input -/

theorem bigsize_reject_empty : decode (bytes []) = none := by decide

theorem bigsize_reject_tag_only_fd : decode (bytes [0xfd]) = none := by decide

theorem bigsize_reject_tag_only_fe : decode (bytes [0xfe]) = none := by decide

theorem bigsize_reject_tag_only_ff : decode (bytes [0xff]) = none := by decide

theorem bigsize_reject_short_two :
    decode (bytes [0xfd, 0x00]) = none := by decide

theorem bigsize_reject_short_four :
    decode (bytes [0xfe, 0x00, 0x00, 0x00]) = none := by decide

theorem bigsize_reject_short_eight :
    decode (bytes [0xff, 0x00, 0x00, 0x00, 0x00]) = none := by decide

/-! ## The `uint64` domain boundary

`encode` truncates values at `2^64`; the resulting `0xff` payload is below
`0x100000000`, so the non-minimal rejection rule makes `decode` return `none`.
The last theorem records a concrete collision above the domain, which is why
`decode_encode` carries `n < 2^64` as a hypothesis. -/

theorem bigsize_encode_above_domain :
    encode 18446744073709551616 =
      bytes [0xff, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] := by
  decide

theorem bigsize_decode_encode_above_domain :
    decode (encode 18446744073709551616) = none := by decide

theorem bigsize_decode_encode_above_domain_plus_five :
    decode (encode 18446744073709551621) = none := by decide

theorem bigsize_encode_above_domain_collision :
    encode (18446744073709551616 + 4294967296) = encode 4294967296 := by decide

/-- The collision decodes to the truncated value, not the original one. -/
theorem bigsize_decode_encode_above_domain_wrong :
    decode (encode (18446744073709551616 + 4294967296)) =
      some (4294967296, 9) := by
  decide

/-- The round-trip value component fails outside the `uint64` domain. -/
theorem bigsize_above_domain_not_roundtrip :
    decode (encode (18446744073709551616 + 4294967296)) ≠
      some (18446744073709551616 + 4294967296, 9) := by
  rw [bigsize_decode_encode_above_domain_wrong]
  simp

end LnLean.Proofs.WaveH.H35
