/-
# BOLT 1 BigSize and TLV framing laws

**English claim.**  On the model's `uint64` domain, `Wire.decode` inverts
`Wire.encode`; canonical BigSize encodings are the shortest possible, with
lengths exactly `1`, `3`, `5`, or `9` according to the `<0xfd`, `≤0xffff`,
`≤0xffffffff` boundaries, and encoded length is monotone in the value.  A
canonical TLV stream (`TLVStream.Canonical` below) has strictly increasing
(hence unique) types, and encoding followed by decoding returns the same
stream.  Finally, the encoded TLV-stream length is the sum of the record
sizes, and a fitting BOLT 1 message frame (two type bytes plus a two-byte
length header plus payload) is bounded by `65535 + 2`, with unframing
inverting framing.

**BOLT sections.**  BOLT 1 §Lightning Message Format (`type || payload`,
maximum message size `65535`), §Type-Length-Value Format (record layout,
strictly-increasing types, minimal BigSize), §Appendix A: BigSize Test
Vectors (1/3/5/9-byte encodings and minimality), §Appendix B/C (TLV test
vectors and message extension ordering).

**rust-lightning anchors (commit fe49009).**
* `lightning/src/util/ser.rs:442-490` — `BigSize` `Writeable`/`Readable`;
  the `0xfd`/`0xfe`/`0xff` tags and the minimality checks.
* `lightning/src/util/ser.rs:62` — `MAX_BUF_SIZE = 64 * 1024`.
* `lightning/src/ln/wire.rs:184-205` — message dispatch keyed by `u16`
  `type_id`.
* `lightning/src/ln/peer_channel_encryptor.rs:36` — `LN_MAX_MSG_LEN =
  u16::MAX = 65535`; `:518-522` rejects a larger encrypted message.
* `lightning/src/util/ser_macros.rs:772-792` — `impl_writeable_msg!`
  appends a TLV stream after the fixed fields.

**Explicitly not modelled.**  Concrete message bodies, known-type length
validation, even/odd unknown-TLV policy, TLV compression, the real
byte-cursor/IO error behaviour, and Noise encryption of the two-byte length
header.  The wave-A `TLV` docstring says the reference parser rejects
non-increasing types; the implementation in `LnLean/Wire/TLV.lean` does not
check ordering, and `decodeTLV_accepts_duplicate_types` below is a checked
counterexample.  The full parser round trip is therefore stated only for
canonical input and left as an obligation.
-/

import LnLean.Wire.BigSize
import LnLean.Wire.TLV
import LnLean.Wire.Message

namespace LnLean.Wire

set_option autoImplicit false

open LnLean

/-! ## BigSize: round trip -/

/-- The model's BigSize domain: values representable by an unsigned 64-bit
integer. -/
def BigSizeDomain (n : Nat) : Prop := n < 18446744073709551616

/-- **BigSize round trip.**  Decoding a canonical encoding returns the value
and the exact number of bytes consumed.  This is the wave-A `decode_encode`
law under a domain-explicit name. -/
theorem decodeBigSize_encodeBigSize (n : Nat) (h : BigSizeDomain n) :
    decode (encode n) = some (n, (encode n).size) :=
  decode_encode n h

/-- The value component of the BigSize round trip. -/
theorem decodeBigSize_encodeBigSize_fst (n : Nat) (h : BigSizeDomain n) :
    (decode (encode n)).map Prod.fst = some n := by
  rw [decodeBigSize_encodeBigSize n h]
  rfl

/-! ## BigSize: canonical length and boundaries -/

/-- The encoded length is the BOLT 1 piecewise function: one byte below
`0xfd`, then `3`, `5`, or `9` bytes at the three boundaries.  This both
identifies the shortest form and records the exact boundary conditions. -/
theorem encode_size_eq (n : Nat) :
    (encode n).size =
      (if n < 0xfd then 1
       else if n ≤ 0xffff then 3
       else if n ≤ 0xffffffff then 5
       else 9) := by
  by_cases h1 : n < 0xfd
  · rw [encode_size_lt_0xfd n h1]
    simp [h1]
  · have h1' : 0xfd ≤ n := by omega
    by_cases h2 : n ≤ 0xffff
    · rw [encode_size_le_0xffff n h1' h2]
      simp [h1, h2]
    · have h2' : 0x10000 ≤ n := by omega
      by_cases h3 : n ≤ 0xffffffff
      · rw [encode_size_le_0xffffffff n h2' h3]
        simp [h1, h2, h3]
      · rw [encode_size_gt_0xffffffff n (by omega)]
        simp [h1, h2, h3]

/-- The single-byte case is exactly the range below `0xfd`, i.e. the
one-byte encoding is used precisely when it is the shortest one. -/
theorem encode_size_eq_one_iff (n : Nat) :
    (encode n).size = 1 ↔ n < 0xfd := by
  rw [encode_size_eq n]
  by_cases h1 : n < 0xfd
  · simp [h1] <;> omega
  · have h1' : 0xfd ≤ n := by omega
    by_cases h2 : n ≤ 0xffff
    · simp [h1, h2] <;> omega
    · have h2' : 0x10000 ≤ n := by omega
      by_cases h3 : n ≤ 0xffffffff
      · simp [h1, h2, h3] <;> omega
      · simp [h1, h2, h3] <;> omega

/-- A value in `0xfd..0xffff` has the three-byte encoding. -/
theorem encode_size_eq_three_iff (n : Nat) :
    (encode n).size = 3 ↔ 0xfd ≤ n ∧ n ≤ 0xffff := by
  rw [encode_size_eq n]
  by_cases h1 : n < 0xfd
  · simp [h1] <;> omega
  · have h1' : 0xfd ≤ n := by omega
    by_cases h2 : n ≤ 0xffff
    · simp [h1, h2, h1'] <;> omega
    · have h2' : 0x10000 ≤ n := by omega
      by_cases h3 : n ≤ 0xffffffff
      · simp [h1, h2, h3] <;> omega
      · simp [h1, h2, h3] <;> omega

/-- A value in `0x10000..0xffffffff` has the five-byte encoding. -/
theorem encode_size_eq_five_iff (n : Nat) :
    (encode n).size = 5 ↔ 0x10000 ≤ n ∧ n ≤ 0xffffffff := by
  rw [encode_size_eq n]
  by_cases h1 : n < 0xfd
  · simp [h1] <;> omega
  · have h1' : 0xfd ≤ n := by omega
    by_cases h2 : n ≤ 0xffff
    · simp [h1, h2] <;> omega
    · have h2' : 0x10000 ≤ n := by omega
      by_cases h3 : n ≤ 0xffffffff
      · simp [h1, h2, h3, h2'] <;> omega
      · simp [h1, h2, h3] <;> omega

/-- A value above `0xffffffff` has the nine-byte encoding. -/
theorem encode_size_eq_nine_iff (n : Nat) :
    (encode n).size = 9 ↔ 0xffffffff < n := by
  rw [encode_size_eq n]
  by_cases h1 : n < 0xfd
  · simp [h1] <;> omega
  · by_cases h2 : n ≤ 0xffff
    · simp [h1, h2] <;> omega
    · by_cases h3 : n ≤ 0xffffffff
      · simp [h1, h2, h3] <;> omega
      · have h3' : 0xffffffff < n := by omega
        simp [h1, h2, h3, h3'] <;> omega

/-- Encoded length is monotone in the value. -/
theorem encode_size_monotone {n m : Nat} (h : n ≤ m) :
    (encode n).size ≤ (encode m).size := by
  by_cases hm1 : m < 0xfd
  · have hn1 : n < 0xfd := by omega
    rw [encode_size_lt_0xfd n hn1, encode_size_lt_0xfd m hm1]
    omega
  · have hm1' : 0xfd ≤ m := by omega
    by_cases hm2 : m ≤ 0xffff
    · rw [encode_size_le_0xffff m hm1' hm2]
      by_cases hn1 : n < 0xfd
      · rw [encode_size_lt_0xfd n hn1]; omega
      · rw [encode_size_le_0xffff n (by omega) (by omega)]; omega
    · have hm2' : 0x10000 ≤ m := by omega
      by_cases hm3 : m ≤ 0xffffffff
      · rw [encode_size_le_0xffffffff m hm2' hm3]
        by_cases hn1 : n < 0xfd
        · rw [encode_size_lt_0xfd n hn1]; omega
        · by_cases hn2 : n ≤ 0xffff
          · rw [encode_size_le_0xffff n (by omega) hn2]; omega
          · rw [encode_size_le_0xffffffff n (by omega) (by omega)]; omega
      · rw [encode_size_gt_0xffffffff m (by omega)]
        by_cases hn1 : n < 0xfd
        · rw [encode_size_lt_0xfd n hn1]; omega
        · by_cases hn2 : n ≤ 0xffff
          · rw [encode_size_le_0xffff n (by omega) hn2]; omega
          · by_cases hn3 : n ≤ 0xffffffff
            · rw [encode_size_le_0xffffffff n (by omega) hn3]; omega
            · rw [encode_size_gt_0xffffffff n (by omega)]; omega

/-- No canonical BigSize encoding is longer than nine bytes. -/
theorem encode_size_le_nine' (n : Nat) : (encode n).size ≤ 9 :=
  encode_size_le_nine n

/-! ## TLV: canonical ordering -/

/-- A TLV record whose type and length both lie in the BigSize domain. -/
def TLVRecord.InDomain (r : TLVRecord) : Prop :=
  r.type < 18446744073709551616 ∧ r.value.size < 18446744073709551616

/-- A canonical outgoing TLV stream: strictly-increasing (hence unique)
types, and both BigSize fields of every record are representable. -/
def TLVStream.Canonical (s : TLVStream) : Prop :=
  s.Sorted ∧ s.Unique ∧ ∀ r ∈ s.records, r.InDomain

/-- A canonical stream is sorted. -/
theorem canonical_sorted (s : TLVStream) (h : s.Canonical) : s.Sorted := h.1

/-- A canonical stream has unique types. -/
theorem canonical_unique (s : TLVStream) (h : s.Canonical) : s.Unique := h.2.1

/-- A strictly-increasing adjacent-type list is pairwise strictly
increasing. -/
theorem sortedTypes_pairwise_lt (l : List Nat) (h : SortedTypes l) :
    l.Pairwise (· < ·) := by
  induction l with
  | nil => simp
  | cons a rest ih =>
      cases rest with
      | nil => simp
      | cons b rest' =>
          rw [List.pairwise_cons]
          exact ⟨fun x hx => sortedTypes_lt_of_mem_of_head h x hx, ih h.2⟩

/-- Every pair of types in a canonical stream, in stream order, is strictly
increasing. -/
theorem canonical_types_pairwise_lt (s : TLVStream) (h : s.Canonical) :
    s.types.Pairwise (· < ·) :=
  sortedTypes_pairwise_lt s.types h.1

/-- In a canonical stream every adjacent pair of record types is strictly
increasing.  This is the local form of the BOLT 1 "strictly-increasing"
requirement. -/
theorem canonical_adjacent_lt (s : TLVStream) (h : s.Canonical)
    {r₁ r₂ : TLVRecord} {rest : List TLVRecord}
    (hr : s.records = r₁ :: r₂ :: rest) : r₁.type < r₂.type := by
  have hsort : SortedTypes (r₁.type :: r₂.type :: rest.map TLVRecord.type) := by
    have := h.1
    unfold TLVStream.Sorted TLVStream.types at this
    rw [hr, List.map_cons, List.map_cons] at this
    exact this
  exact hsort.1

/-! ## TLV: the reference parser does not enforce ordering -/

/-- Two `type = 1` records (`value = 0x2a` and `0x2b`) concatenated. -/
def duplicateTypeStream : ByteArray :=
  ([0x01, 0x01, 0x2a, 0x01, 0x01, 0x2b] : List UInt8).toByteArray

/-- Checked counterexample: the reference parser accepts a stream with
duplicate (non-increasing) types.  Consequently uniqueness must be asserted
as a property of *canonical input*, not as a guarantee of `decodeTLV`. -/
theorem decodeTLV_accepts_duplicate_types :
    decodeTLV duplicateTypeStream =
      some (TLVStream.mk
        [⟨1, ([0x2a] : List UInt8).toByteArray⟩,
         ⟨1, ([0x2b] : List UInt8).toByteArray⟩]) := by
  decide

/-! ## TLV: encoded size -/

/-- The length of a folded record stream is the accumulator length plus the
sum of the record sizes. -/
theorem encode_foldl_size (acc : ByteArray) (rs : List TLVRecord) :
    (rs.foldl (fun acc r => acc ++ TLVRecord.encode r) acc).size =
      acc.size + (rs.map TLVRecord.encodedSize).sum := by
  induction rs generalizing acc with
  | nil => simp
  | cons r rs ih =>
      simp only [List.foldl]
      rw [ih (acc ++ TLVRecord.encode r)]
      rw [ByteArray.size_append, TLVRecord.encode_size]
      simp only [List.map_cons, List.sum_cons]
      omega

/-- The encoded length of a TLV stream is the sum of its record sizes. -/
theorem encodeTLV_size_eq (s : TLVStream) :
    (encodeTLV s).size = (s.records.map TLVRecord.encodedSize).sum := by
  unfold encodeTLV TLVStream.encode
  rw [encode_foldl_size ByteArray.empty s.records]
  simp

/-- If the sum of the record sizes fits the BOLT 1 payload budget, the
encoded TLV stream fits that budget. -/
theorem encodeTLV_size_le_of_sum_le (s : TLVStream)
    (h : (s.records.map TLVRecord.encodedSize).sum ≤ MAX_PAYLOAD_SIZE) :
    (encodeTLV s).size ≤ MAX_PAYLOAD_SIZE := by
  rw [encodeTLV_size_eq s]
  exact h

/-! ## TLV: parser round trip (obligation) -/

/-- **Canonical TLV round trip.**  Encoding a canonical stream and running
the reference parser returns the original stream.  The parser itself does
not enforce canonicality (see `decodeTLV_accepts_duplicate_types`), so the
hypothesis is essential. -/
theorem decodeTLV_encodeTLV (s : TLVStream) (h : s.Canonical) :
    decodeTLV (encodeTLV s) = some s := by
  -- OBLIGATION: LN-WIRE-001 canonical TLV streams round-trip through encodeTLV/decodeTLV
  sorry

/-! ## Message framing -/

/-- A fitting BOLT 1 message has an abstract frame of at most `65535 + 2`
bytes: the two type bytes, the two-byte length header, and the payload. -/
theorem frame_size_le_max_of_fits (m : WireMessage) (h : m.fits) :
    (frame m).size ≤ MAX_MESSAGE_SIZE + 2 := by
  rw [frame_size_eq]
  unfold WireMessage.fits at h
  omega

/-- The frame length in terms of the payload, with the BOLT 1 maximum made
explicit. -/
theorem frame_size_le_max_iff (m : WireMessage) :
    (frame m).size ≤ MAX_MESSAGE_SIZE + 2 ↔ m.fits := by
  rw [frame_size_eq]
  unfold WireMessage.fits WireMessage.messageSize MAX_MESSAGE_SIZE
  omega

/-- **Message frame/unframe round trip.**  A message that satisfies the
BOLT 1 size limit is recovered exactly by `unframe` after framing. -/
theorem unframe_framedMessage_of_fits (m : WireMessage) (h : m.fits) :
    unframe (frame m) = some m :=
  unframe_frame_of_fits m h

end LnLean.Wire
