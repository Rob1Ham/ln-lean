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

/-! ## TLV: parser round trip -/

/-- `decodePayload` with a `0xfd` tag ignores a suffix after the two-byte
payload. -/
private theorem decodePayload_fd_append (n : Nat) (h1 : 0xfd ≤ n) (h2 : n ≤ 0xffff)
    (rest : List UInt8) :
    decodePayload 0xfd 2 (beBytesAux 2 n [] ++ rest) = some (n, 3) := by
  unfold decodePayload
  have hlen : (beBytesAux 2 n [] ++ rest).length = 2 + rest.length := by
    simp [List.length_append, beBytesAux_length]
  rw [ite_eq_right (by omega)]
  have htake : List.take 2 (beBytesAux 2 n [] ++ rest) = beBytesAux 2 n [] := by
    rw [show 2 = (beBytesAux 2 n []).length by simp [beBytesAux_length]]
    exact List.take_left
  rw [htake]
  rw [decodeBEList_beBytesAux]
  simp only [List.length_nil]
  have hlt : n < 256 ^ 2 := by
    have hp : 256 ^ 2 = 65536 := by decide
    omega
  rw [Nat.mod_eq_of_lt hlt]
  simp [decodeBEList, h1, h2]

/-- `decodePayload` with a `0xfe` tag ignores a suffix after the four-byte
payload. -/
private theorem decodePayload_fe_append (n : Nat) (h1 : 0x10000 ≤ n) (h2 : n ≤ 0xffffffff)
    (rest : List UInt8) :
    decodePayload 0xfe 4 (beBytesAux 4 n [] ++ rest) = some (n, 5) := by
  unfold decodePayload
  have hlen : (beBytesAux 4 n [] ++ rest).length = 4 + rest.length := by
    simp [List.length_append, beBytesAux_length]
  rw [ite_eq_right (by omega)]
  have htake : List.take 4 (beBytesAux 4 n [] ++ rest) = beBytesAux 4 n [] := by
    rw [show 4 = (beBytesAux 4 n []).length by simp [beBytesAux_length]]
    exact List.take_left
  rw [htake]
  rw [decodeBEList_beBytesAux]
  simp only [List.length_nil]
  have hlt : n < 256 ^ 4 := by
    have hp : 256 ^ 4 = 4294967296 := by decide
    omega
  rw [Nat.mod_eq_of_lt hlt]
  simp [decodeBEList, h1, h2]

/-- `decodePayload` with a `0xff` tag ignores a suffix after the eight-byte
payload. -/
private theorem decodePayload_ff_append (n : Nat) (h : 0x100000000 ≤ n)
    (hmax : n < 18446744073709551616) (rest : List UInt8) :
    decodePayload 0xff 8 (beBytesAux 8 n [] ++ rest) = some (n, 9) := by
  unfold decodePayload
  have hlen : (beBytesAux 8 n [] ++ rest).length = 8 + rest.length := by
    simp [List.length_append, beBytesAux_length]
  rw [ite_eq_right (by omega)]
  have htake : List.take 8 (beBytesAux 8 n [] ++ rest) = beBytesAux 8 n [] := by
    rw [show 8 = (beBytesAux 8 n []).length by simp [beBytesAux_length]]
    exact List.take_left
  rw [htake]
  rw [decodeBEList_beBytesAux]
  simp only [List.length_nil]
  have hlt : n < 256 ^ 8 := by
    have hp : 256 ^ 8 = 18446744073709551616 := by decide
    omega
  rw [Nat.mod_eq_of_lt hlt]
  simp [decodeBEList, h]

/-- `decode` on a byte list, used to reason about a `BigSize` followed by a
suffix without repeatedly unfolding the `ByteArray` conversion. -/
private def decodeL (l : List UInt8) : Option (Nat × Nat) :=
  match l with
  | [] => none
  | x :: rest =>
      if x.toNat < 0xfd then some (x.toNat, 1)
      else if x = 0xfd then decodePayload x 2 rest
      else if x = 0xfe then decodePayload x 4 rest
      else decodePayload x 8 rest

private theorem decode_toByteArray_eq_decodeL (l : List UInt8) :
    decode l.toByteArray = decodeL l := by
  unfold decode decodeL
  rw [bytesToList_toByteArray]
  rfl

/-- Decoding a canonical BigSize at the head of a byte list is independent of
the suffix. -/
private theorem decodeL_encode_append (n : Nat) (hn : BigSizeDomain n)
    (rest : List UInt8) :
    decodeL (bytesToList (encode n) ++ rest) = some (n, (encode n).size) := by
  by_cases h1 : n < 0xfd
  · have h256 : n < 256 := by omega
    have henc : encode n = oneByte n.toUInt8 := by simp [encode, h1]
    rw [henc, bytesToList_oneByte]
    simp [decodeL, toUInt8_toNat_of_lt h256, h1, oneByte_size]
  · have h1' : 0xfd ≤ n := by omega
    by_cases h2 : n ≤ 0xffff
    · have henc : encode n = oneByte 0xfd ++ beBytes n 2 := by simp [encode, h1, h2]
      rw [henc, bytesToList_append, bytesToList_oneByte, bytesToList_beBytes]
      simp [decodeL, decodePayload_fd_append n h1' h2 rest, oneByte_size, beBytes_size,
        ByteArray.size_append]
    · have h2' : 0x10000 ≤ n := by omega
      by_cases h3 : n ≤ 0xffffffff
      · have henc : encode n = oneByte 0xfe ++ beBytes n 4 := by
          simp [encode, h1, h2, h3]
        rw [henc, bytesToList_append, bytesToList_oneByte, bytesToList_beBytes]
        simp [decodeL, decodePayload_fe_append n h2' h3 rest, oneByte_size, beBytes_size,
          ByteArray.size_append]
      · have h3' : 0xffffffff < n := by omega
        have hlow : 0x100000000 ≤ n := by omega
        have henc : encode n = oneByte 0xff ++ beBytes n 8 := by
          simp [encode, h1, h2, h3]
        rw [henc, bytesToList_append, bytesToList_oneByte, bytesToList_beBytes]
        simp [decodeL, decodePayload_ff_append n hlow hn rest, oneByte_size, beBytes_size,
          ByteArray.size_append]

/-- Byte-array form of `decodeL_encode_append`. -/
private theorem decode_encode_append (n : Nat) (hn : BigSizeDomain n)
    (rest : List UInt8) :
    decode ((bytesToList (encode n) ++ rest).toByteArray) =
      some (n, (encode n).size) := by
  unfold decode
  rw [bytesToList_toByteArray]
  exact decodeL_encode_append n hn rest

/-- A record value survives a round trip through its byte list. -/
private theorem value_toByteArray (r : TLVRecord) :
    (bytesToList r.value).toByteArray = r.value := by
  apply ByteArray.ext
  rw [List.data_toByteArray]
  exact Array.toArray_toList

/-- Parsing a record encoding followed by arbitrary bytes returns exactly that
record, provided both BigSize fields are in the `uint64` domain. -/
private theorem parseRecord_encode_append (r : TLVRecord) (hr : r.InDomain)
    (rest : List UInt8) :
    parseRecord (bytesToList (TLVRecord.encode r) ++ rest) = some (r, rest) := by
  have hb : bytesToList (TLVRecord.encode r) =
      bytesToList (encode r.type) ++ bytesToList (encode r.value.size) ++
        bytesToList r.value := by
    simp [TLVRecord.encode, bytesToList_append]
  rw [hb]
  unfold parseRecord
  simp only [List.append_assoc]
  rw [decode_encode_append r.type hr.1
    (bytesToList (encode r.value.size) ++ (bytesToList r.value ++ rest))]
  simp only
  rw [← bytesToList_length (encode r.type), List.drop_left]
  rw [decode_encode_append r.value.size hr.2 (bytesToList r.value ++ rest)]
  simp only
  rw [← bytesToList_length (encode r.value.size), List.drop_left]
  have hlen : ¬ (bytesToList r.value ++ rest).length < r.value.size := by
    rw [List.length_append, bytesToList_length]
    omega
  rw [ite_eq_right hlen]
  rw [← bytesToList_length r.value, List.take_left, List.drop_left, value_toByteArray r]

/-- `bytesToList` of a folded stream encoding is the concatenation of the
record byte lists. -/
private theorem bytesToList_foldl_encode (rs : List TLVRecord) (acc : ByteArray) :
    bytesToList (rs.foldl (fun acc r => acc ++ TLVRecord.encode r) acc) =
      bytesToList acc ++ rs.flatMap (fun r => bytesToList (TLVRecord.encode r)) := by
  induction rs generalizing acc with
  | nil => simp
  | cons r rs ih =>
      simp only [List.foldl]
      rw [ih (acc ++ TLVRecord.encode r)]
      rw [bytesToList_append]
      simp [List.flatMap_cons, List.append_assoc]

/-- The byte list of an encoded TLV stream is the concatenation of all record
encodings. -/
private theorem bytesToList_encodeTLV (s : TLVStream) :
    bytesToList (encodeTLV s) =
      s.records.flatMap (fun r => bytesToList (TLVRecord.encode r)) := by
  unfold encodeTLV TLVStream.encode
  rw [bytesToList_foldl_encode]
  simp [bytesToList]

/-- Every record encoding is at least one byte long. -/
private theorem one_le_encodedSize (r : TLVRecord) : 1 ≤ r.encodedSize := by
  rcases encode_size_cases r.type with h1 | h1 | h1 | h1 <;>
    rcases encode_size_cases r.value.size with h2 | h2 | h2 | h2 <;>
    unfold TLVRecord.encodedSize <;> omega

/-- The number of records is at most the sum of their encoded sizes. -/
private theorem length_le_sum_encodedSize (rs : List TLVRecord) :
    rs.length ≤ (rs.map TLVRecord.encodedSize).sum := by
  induction rs with
  | nil => simp
  | cons r rs ih =>
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      have h := one_le_encodedSize r
      omega

/-- One unfolding step of the fuel-bounded parser on a nonempty input. -/
private theorem decodeTLVGo_succ_cons (fuel : Nat) (x : UInt8) (xs : List UInt8) :
    decodeTLVGo (fuel + 1) (x :: xs) =
      (match parseRecord (x :: xs) with
       | none => none
       | some (r, rest) =>
           match decodeTLVGo fuel rest with
           | none => none
           | some rs => some (r :: rs)) := rfl

/-- The fuel-bounded parser consumes a list of encoded records, provided every
record is in the `uint64` domain and there is at least one unit of fuel per
record. -/
private theorem decodeTLVGo_encode (rs : List TLVRecord)
    (hdom : ∀ r ∈ rs, r.InDomain) (fuel : Nat) (hfuel : rs.length ≤ fuel) :
    decodeTLVGo fuel
      (rs.flatMap (fun r => bytesToList (TLVRecord.encode r))) = some rs := by
  induction rs generalizing fuel with
  | nil =>
      cases fuel <;> simp [decodeTLVGo]
  | cons r rs ih =>
      cases fuel with
      | zero => simp at hfuel
      | succ f =>
          have hlen : rs.length ≤ f := by simp at hfuel; omega
          rw [List.flatMap_cons]
          cases hb : bytesToList (TLVRecord.encode r) with
          | nil =>
              have hzero : (bytesToList (TLVRecord.encode r)).length = 0 := by
                rw [hb]; rfl
              rw [bytesToList_length] at hzero
              have hpos : 0 < (TLVRecord.encode r).size := by
                rw [TLVRecord.encode_size]
                exact Nat.lt_of_lt_of_le (by decide) (one_le_encodedSize r)
              omega
          | cons x xs =>
              simp only [List.cons_append]
              rw [decodeTLVGo_succ_cons]
              rw [← List.cons_append, ← hb]
              rw [parseRecord_encode_append r (hdom r (by simp)) _]
              simp only
              rw [ih (fun x hx => hdom x (by simp [hx])) f hlen]

/-- **Canonical TLV round trip.**  Encoding a canonical stream and running
the reference parser returns the original stream.  The parser itself does
not enforce canonicality (see `decodeTLV_accepts_duplicate_types`), so the
hypothesis is essential. -/
theorem decodeTLV_encodeTLV (s : TLVStream) (h : s.Canonical) :
    decodeTLV (encodeTLV s) = some s := by
  unfold decodeTLV
  rw [bytesToList_encodeTLV]
  have hdom : ∀ r ∈ s.records, r.InDomain := h.2.2
  have hfuel : s.records.length ≤ (encodeTLV s).size + 1 := by
    rw [encodeTLV_size_eq]
    have := length_le_sum_encodedSize s.records
    omega
  rw [decodeTLVGo_encode s.records hdom ((encodeTLV s).size + 1) hfuel]

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
