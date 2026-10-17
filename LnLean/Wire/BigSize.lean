/-
# BOLT 1 BigSize

**English claim.**  A `BigSize` is a canonical variable-length integer:
values below `0xfd` are one byte; `0xfd` followed by two big-endian bytes
covers `0xfd..0xffff`; `0xfe` plus four bytes covers `0x10000..0xffffffff`;
and `0xff` plus eight bytes covers larger `uint64` values.  `encode` emits the
minimal representation, and `decode` rejects non-minimal encodings.  The
encoded length is therefore exactly `1`, `3`, `5`, or `9` bytes according to
the value's range.

**BOLT sections.**  BOLT 1 §Appendix A: BigSize Test Vectors (the encoding
and the "minimally encoded" requirement); BOLT 1 §Type-Length-Value Format
(uses BigSize for TLV type and length).

**rust-lightning anchors (commit fe49009).**
* `lightning/src/util/ser.rs:442-490` — `BigSize` `Writeable`/`Readable`,
  including the canonicality checks for `0xfd`, `0xfe`, and `0xff`.
* `lightning/src/util/ser.rs:62` — `MAX_BUF_SIZE = 64 * 1024` bounds the
  buffers that BigSize parsing can allocate.

**Not modelled.**  IO/`Read` errors and short-read exceptions (the model
returns `Option`), `u64` overflow beyond `2^64-1`, the concrete test-vector
runner, and Rust's byte-cursor implementation.  The decoder models the
canonicality rule as `none`.
-/

import LnLean.Basic.Core

namespace LnLean.Wire

set_option autoImplicit false

open LnLean

/-! ## Byte-list conversion helpers -/

/-- The byte list underlying a `ByteArray`.  `ByteArray.toList` is a loop in
the current core library; `data.toList` has the reusable append/push lemmas
that the proofs below need. -/
def bytesToList (b : ByteArray) : List UInt8 := b.data.toList

/-- `bytesToList` of `List.toByteArray` is the original list. -/
theorem bytesToList_toByteArray (l : List UInt8) :
    bytesToList l.toByteArray = l :=
  List.toList_data_toByteArray

/-- A single byte as a `ByteArray`. -/
def oneByte (b : UInt8) : ByteArray := [b].toByteArray

theorem oneByte_size (b : UInt8) : (oneByte b).size = 1 := by
  simp [oneByte]

/-- The length of `bytesToList` is the byte-array size. -/
theorem bytesToList_length (b : ByteArray) : (bytesToList b).length = b.size := by
  simp [bytesToList, Array.length_toList, ByteArray.size_data]

/-! ## Big-endian fixed-width encoding -/

/-- Prepend the low byte of `n` while consuming `k` bytes.  The accumulator
holds the already-emitted high-order bytes. -/
def beBytesAux : Nat → Nat → List UInt8 → List UInt8
  | 0, _, acc => acc
  | k + 1, n, acc => beBytesAux k (n / 256) ((n % 256).toUInt8 :: acc)

/-- Big-endian encoding of `n` into exactly `len` bytes (truncating modulo
`256^len`). -/
def beBytes (n len : Nat) : ByteArray :=
  (beBytesAux len n []).toByteArray

/-- `beBytesAux` emits exactly the requested number of bytes. -/
theorem beBytesAux_length (k n : Nat) (acc : List UInt8) :
    (beBytesAux k n acc).length = acc.length + k := by
  induction k generalizing n acc with
  | zero => simp [beBytesAux]
  | succ k ih =>
      simp [beBytesAux, ih, Nat.add_comm, Nat.add_left_comm]

/-- `beBytes n len` has exactly `len` bytes. -/
theorem beBytes_size (n len : Nat) : (beBytes n len).size = len := by
  unfold beBytes
  rw [← ByteArray.size_data, List.data_toByteArray, List.size_toArray]
  rw [beBytesAux_length]
  simp

/-- The byte list of `beBytes`. -/
theorem bytesToList_beBytes (n len : Nat) :
    bytesToList (beBytes n len) = beBytesAux len n [] := by
  unfold beBytes
  exact bytesToList_toByteArray _

/-- Big-endian decoding of a byte list. -/
def decodeBEList : List UInt8 → Nat
  | [] => 0
  | b :: rest => b.toNat * 256 ^ rest.length + decodeBEList rest

/-- Big-endian decoding of a `ByteArray`. -/
def decodeBE (b : ByteArray) : Nat :=
  decodeBEList (bytesToList b)

/-- `256 ^ k` is positive. -/
theorem pow256_pos (k : Nat) : 0 < 256 ^ k :=
  Nat.pow_pos (by decide : 0 < 256)

/-- The low byte of `n` is exactly `n % 256` when it fits. -/
theorem toUInt8_toNat_of_lt {n : Nat} (h : n < 256) : (n.toUInt8).toNat = n := by
  simp [Nat.toUInt8, Nat.mod_eq_of_lt h]

/-- Splitting `n` at 256: the high part shifted left plus the low byte is the
low `k+1` bytes of `n`. -/
theorem div256_mod (n k : Nat) :
    ((n / 256) % 256 ^ k) * 256 + n % 256 = n % (256 ^ k * 256) := by
  have hmod : (n / 256) % 256 ^ k < 256 ^ k := Nat.mod_lt _ (pow256_pos k)
  have hr : n % 256 < 256 := Nat.mod_lt n (by decide)
  have hrM : n % 256 < 256 * 256 ^ k :=
    Nat.lt_of_lt_of_le hr (Nat.le_mul_of_pos_right 256 (pow256_pos k))
  have hMpos : 0 < 256 * 256 ^ k := Nat.mul_pos (by decide) (pow256_pos k)
  have hbound : 256 * ((n / 256) % 256 ^ k) + n % 256 < 256 * 256 ^ k := by
    have h1 : 256 * ((n / 256) % 256 ^ k) + n % 256 <
        256 * ((n / 256) % 256 ^ k) + 256 :=
      Nat.add_lt_add_left hr _
    have h2 : 256 * ((n / 256) % 256 ^ k) + 256 =
        256 * (((n / 256) % 256 ^ k) + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
    have h3 : ((n / 256) % 256 ^ k) + 1 ≤ 256 ^ k := Nat.succ_le_of_lt hmod
    have h4 : 256 * (((n / 256) % 256 ^ k) + 1) ≤ 256 * 256 ^ k :=
      Nat.mul_le_mul_left 256 h3
    omega
  calc
    ((n / 256) % 256 ^ k) * 256 + n % 256
        = 256 * ((n / 256) % 256 ^ k) + n % 256 := by rw [Nat.mul_comm]
    _ = (256 * ((n / 256) % 256 ^ k) + n % 256) % (256 * 256 ^ k) :=
        (Nat.mod_eq_of_lt hbound).symm
    _ = ((256 * (n / 256)) % (256 * 256 ^ k) + n % 256) % (256 * 256 ^ k) := by
        rw [Nat.mul_mod_mul_left]
    _ = ((256 * (n / 256)) % (256 * 256 ^ k) +
          n % 256 % (256 * 256 ^ k)) % (256 * 256 ^ k) := by
        rw [Nat.mod_eq_of_lt hrM]
    _ = (256 * (n / 256) + n % 256) % (256 * 256 ^ k) := by
        rw [← Nat.add_mod]
    _ = n % (256 * 256 ^ k) := by rw [Nat.div_add_mod]
    _ = n % (256 ^ k * 256) := by rw [Nat.mul_comm (256 ^ k) 256]

/-- Decoding the big-endian encoding of `n` into `k` bytes recovers
`n % 256^k`. -/
theorem decodeBEList_beBytesAux (k n : Nat) (acc : List UInt8) :
    decodeBEList (beBytesAux k n acc) =
      (n % 256 ^ k) * 256 ^ acc.length + decodeBEList acc := by
  induction k generalizing n acc with
  | zero => simp [beBytesAux, Nat.mod_one]
  | succ k ih =>
      rw [beBytesAux]
      rw [ih]
      simp only [decodeBEList, List.length_cons]
      rw [toUInt8_toNat_of_lt (Nat.mod_lt n (by decide))]
      rw [Nat.pow_succ]
      rw [show n % 256 ^ (k + 1) = n % (256 ^ k * 256) by rw [Nat.pow_succ]]
      rw [Nat.mul_comm (256 ^ acc.length) 256]
      rw [← Nat.mul_assoc]
      rw [← Nat.add_assoc]
      rw [← Nat.add_mul]
      rw [div256_mod]

/-- Decoding a fixed-width encoding gives `n % 256^len`. -/
theorem decodeBE_beBytes (n len : Nat) :
    decodeBE (beBytes n len) = n % 256 ^ len := by
  unfold decodeBE
  rw [bytesToList_beBytes, decodeBEList_beBytesAux]
  simp [decodeBEList]

/-- If `n` fits in `len` bytes, decoding recovers `n` exactly. -/
theorem decodeBE_beBytes_of_lt (n len : Nat) (h : n < 256 ^ len) :
    decodeBE (beBytes n len) = n := by
  rw [decodeBE_beBytes, Nat.mod_eq_of_lt h]

/-! ## Encoding and decoding -/

/-- Canonical BigSize encoding (BOLT 1 Appendix A). -/
def encode (n : Nat) : ByteArray :=
  if n < 0xfd then oneByte n.toUInt8
  else if n ≤ 0xffff then oneByte 0xfd ++ beBytes n 2
  else if n ≤ 0xffffffff then oneByte 0xfe ++ beBytes n 4
  else oneByte 0xff ++ beBytes n 8

/-- Decode a payload after a `0xfd`/`0xfe`/`0xff` tag.  Non-minimal values
produce `none`. -/
def decodePayload (tag : UInt8) (len : Nat) (rest : List UInt8) :
    Option (Nat × Nat) :=
  if rest.length < len then none
  else
    let v := decodeBEList (rest.take len)
    if tag = 0xfd then
      if v < 0xfd ∨ 0xffff < v then none else some (v, len + 1)
    else if tag = 0xfe then
      if v < 0x10000 ∨ 0xffffffff < v then none else some (v, len + 1)
    else
      if v < 0x100000000 then none else some (v, len + 1)

/-- Decode a BigSize, returning the value and the number of bytes consumed. -/
def decode (b : ByteArray) : Option (Nat × Nat) :=
  match bytesToList b with
  | [] => none
  | x :: rest =>
      if x.toNat < 0xfd then some (x.toNat, 1)
      else if x = 0xfd then decodePayload x 2 rest
      else if x = 0xfe then decodePayload x 4 rest
      else decodePayload x 8 rest

/-! ## Canonical lengths -/

/-- Values below `0xfd` encode in a single byte. -/
theorem encode_size_lt_0xfd (n : Nat) (h : n < 0xfd) :
    (encode n).size = 1 := by
  simp [encode, h, oneByte_size]

/-- Values in `0xfd..0xffff` encode in `0xfd` plus two bytes, total 3. -/
theorem encode_size_le_0xffff (n : Nat) (h1 : 0xfd ≤ n) (h2 : n ≤ 0xffff) :
    (encode n).size = 3 := by
  have hlt : ¬ n < 0xfd := by omega
  simp [encode, hlt, h2, oneByte_size, beBytes_size]

/-- Values in `0x10000..0xffffffff` encode in `0xfe` plus four bytes, total 5. -/
theorem encode_size_le_0xffffffff (n : Nat) (h1 : 0x10000 ≤ n)
    (h2 : n ≤ 0xffffffff) : (encode n).size = 5 := by
  have hlt : ¬ n < 0xfd := by omega
  have hgt : ¬ n ≤ 0xffff := by omega
  simp [encode, hlt, hgt, h2, oneByte_size, beBytes_size]

/-- Values above `0xffffffff` encode in `0xff` plus eight bytes, total 9. -/
theorem encode_size_gt_0xffffffff (n : Nat) (h : 0xffffffff < n) :
    (encode n).size = 9 := by
  have hlt : ¬ n < 0xfd := by omega
  have hgt2 : ¬ n ≤ 0xffff := by omega
  have hgt3 : ¬ n ≤ 0xffffffff := by omega
  simp [encode, hlt, hgt2, hgt3, oneByte_size, beBytes_size]

/-- Every BigSize encoding has length 1, 3, 5, or 9. -/
theorem encode_size_cases (n : Nat) :
    (encode n).size = 1 ∨ (encode n).size = 3 ∨
    (encode n).size = 5 ∨ (encode n).size = 9 := by
  by_cases h1 : n < 0xfd
  · exact Or.inl (encode_size_lt_0xfd n h1)
  · by_cases h2 : n ≤ 0xffff
    · exact Or.inr (Or.inl (encode_size_le_0xffff n (by omega) h2))
    · by_cases h3 : n ≤ 0xffffffff
      · exact Or.inr (Or.inr (Or.inl (encode_size_le_0xffffffff n (by omega) h3)))
      · exact Or.inr (Or.inr (Or.inr (encode_size_gt_0xffffffff n (by omega))))

/-- No canonical encoding is longer than nine bytes. -/
theorem encode_size_le_nine (n : Nat) : (encode n).size ≤ 9 := by
  rcases encode_size_cases n with h | h | h | h <;> omega

/-! ## Round trip for the single-byte case -/

/-- `decode (encode n) = some (n, 1)` for `n < 0xfd`. -/
theorem decode_encode_lt_0xfd (n : Nat) (h : n < 0xfd) :
    decode (encode n) = some (n, 1) := by
  have h256 : n < 256 := by omega
  have henc : encode n = oneByte n.toUInt8 := by simp [encode, h]
  rw [henc]
  unfold decode oneByte
  rw [bytesToList_toByteArray]
  simp [toUInt8_toNat_of_lt h256, h]

/-- The byte list of `oneByte`. -/
theorem bytesToList_oneByte (b : UInt8) : bytesToList (oneByte b) = [b] := by
  simp [oneByte, bytesToList_toByteArray]

/-- `bytesToList` commutes with concatenation. -/
theorem bytesToList_append (a b : ByteArray) :
    bytesToList (a ++ b) = bytesToList a ++ bytesToList b := by
  simp [bytesToList, ByteArray.data_append, Array.toList_append]

/-- Decode a `0xfd`-tagged two-byte payload. -/
theorem decodePayload_fd (n : Nat) (h1 : 0xfd ≤ n) (h2 : n ≤ 0xffff) :
    decodePayload 0xfd 2 (beBytesAux 2 n []) = some (n, 3) := by
  unfold decodePayload
  have hlen : (beBytesAux 2 n []).length = 2 := by
    simpa using beBytesAux_length 2 n []
  rw [if_neg (by omega)]
  rw [List.take_of_length_le (by omega)]
  rw [decodeBEList_beBytesAux]
  simp only [List.length_nil, Nat.mul_zero, Nat.add_zero]
  have hlt : n < 256 ^ 2 := by
    have hp : 256 ^ 2 = 65536 := by decide
    omega
  rw [Nat.mod_eq_of_lt hlt]
  simp [decodeBEList, h1, h2]

/-- Decode a `0xfe`-tagged four-byte payload. -/
theorem decodePayload_fe (n : Nat) (h1 : 0x10000 ≤ n) (h2 : n ≤ 0xffffffff) :
    decodePayload 0xfe 4 (beBytesAux 4 n []) = some (n, 5) := by
  unfold decodePayload
  have hlen : (beBytesAux 4 n []).length = 4 := by
    simpa using beBytesAux_length 4 n []
  rw [if_neg (by omega)]
  rw [List.take_of_length_le (by omega)]
  rw [decodeBEList_beBytesAux]
  simp only [List.length_nil, Nat.mul_zero, Nat.add_zero]
  have hlt : n < 256 ^ 4 := by
    have hp : 256 ^ 4 = 4294967296 := by decide
    omega
  rw [Nat.mod_eq_of_lt hlt]
  simp [decodeBEList, h1, h2]

/-- Decode a `0xff`-tagged eight-byte payload. -/
theorem decodePayload_ff (n : Nat) (h : 0x100000000 ≤ n)
    (hmax : n < 18446744073709551616) :
    decodePayload 0xff 8 (beBytesAux 8 n []) = some (n, 9) := by
  unfold decodePayload
  have hlen : (beBytesAux 8 n []).length = 8 := by
    simpa using beBytesAux_length 8 n []
  rw [if_neg (by omega)]
  rw [List.take_of_length_le (by omega)]
  rw [decodeBEList_beBytesAux]
  simp only [List.length_nil, Nat.mul_zero, Nat.add_zero]
  have hlt : n < 256 ^ 8 := by
    have hp : 256 ^ 8 = 18446744073709551616 := by decide
    omega
  rw [Nat.mod_eq_of_lt hlt]
  simp [decodeBEList, h]

/-- `decode (encode n) = some (n, 3)` for `0xfd ≤ n ≤ 0xffff`. -/
theorem decode_encode_le_ffff (n : Nat) (h1 : 0xfd ≤ n) (h2 : n ≤ 0xffff) :
    decode (encode n) = some (n, 3) := by
  have hlt : ¬ n < 0xfd := by omega
  unfold decode encode
  rw [if_neg hlt, if_pos h2]
  rw [bytesToList_append, bytesToList_oneByte, bytesToList_beBytes]
  simp [decodePayload_fd, h1, h2]

/-- `decode (encode n) = some (n, 5)` for `0x10000 ≤ n ≤ 0xffffffff`. -/
theorem decode_encode_le_ffffffff (n : Nat) (h1 : 0x10000 ≤ n)
    (h2 : n ≤ 0xffffffff) : decode (encode n) = some (n, 5) := by
  have hlt : ¬ n < 0xfd := by omega
  have hgt : ¬ n ≤ 0xffff := by omega
  unfold decode encode
  rw [if_neg hlt, if_neg hgt, if_pos h2]
  rw [bytesToList_append, bytesToList_oneByte, bytesToList_beBytes]
  simp [decodePayload_fe, h1, h2]

/-- `decode (encode n) = some (n, 9)` for `0xffffffff < n < 2^64`. -/
theorem decode_encode_gt_0xffffffff (n : Nat) (h : 0xffffffff < n)
    (hmax : n < 18446744073709551616) : decode (encode n) = some (n, 9) := by
  have hlt : ¬ n < 0xfd := by omega
  have hgt : ¬ n ≤ 0xffff := by omega
  have hgt2 : ¬ n ≤ 0xffffffff := by omega
  have hlow : 0x100000000 ≤ n := by omega
  unfold decode encode
  rw [if_neg hlt, if_neg hgt, if_neg hgt2]
  rw [bytesToList_append, bytesToList_oneByte, bytesToList_beBytes]
  simp [decodePayload_ff, hlow, hmax]

/-- **BigSize round trip.**  For every `uint64` value, decoding the canonical
encoding returns the value and the encoded length. -/
theorem decode_encode (n : Nat) (h : n < 18446744073709551616) :
    decode (encode n) = some (n, (encode n).size) := by
  by_cases h1 : n < 0xfd
  · rw [decode_encode_lt_0xfd n h1, encode_size_lt_0xfd n h1]
  · by_cases h2 : n ≤ 0xffff
    · rw [decode_encode_le_ffff n (by omega) h2, encode_size_le_0xffff n (by omega) h2]
    · by_cases h3 : n ≤ 0xffffffff
      · rw [decode_encode_le_ffffffff n (by omega) h3,
          encode_size_le_0xffffffff n (by omega) h3]
      · rw [decode_encode_gt_0xffffffff n (by omega) h,
          encode_size_gt_0xffffffff n (by omega)]

end LnLean.Wire
