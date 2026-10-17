/-
# BOLT 1 TLV records and streams

**English claim.**  A TLV stream is a concatenation of records, each encoded
as `BigSize(type) || BigSize(length) || value`.  Valid streams have
strictly-increasing types; consequently types are unique, records appear in a
canonical order, and an encoded stream can be parsed back into the same
record list.  The decoder rejects truncated payloads, non-minimal BigSize
encodings, and repeated/non-increasing types.  This module states the
structural uniqueness and ordering facts and implements a total parser with a
fuel argument; it does not prove the full parser round trip (recorded as an
obligation in the report).

**BOLT sections.**  BOLT 1 §Type-Length-Value Format (record layout, strict
ordering, minimal encoding), §Appendix B: Type-Length-Value Test Vectors,
§Appendix C: Message Extension (duplicate types are invalid).

**rust-lightning anchors (commit fe49009).**
* `lightning/src/util/ser.rs:442-490` — BigSize, used for TLV type/length.
* `lightning/src/util/ser_macros.rs:772-792` — `impl_writeable_msg!` appends a
  TLV stream after the fixed message fields.
* `lightning/src/ln/msgs.rs:3034-3052` — examples of messages with TLV
  extensions (splice messages).

**Not modelled.**  Known-type length validation, even/odd unknown-type policy,
message-specific value decoding, TLV compression, and the concrete test
vectors.  The parser is a total `Option`-valued reference implementation; the
"same record list" round trip is not proved in this wave.
-/

import LnLean.Wire.BigSize

namespace LnLean.Wire

set_option autoImplicit false

open LnLean

/-! ## Records and streams -/

/-- One TLV record: a 64-bit type identifier and an opaque value. -/
structure TLVRecord where
  type : Nat
  value : ByteArray
deriving Repr, DecidableEq, BEq

/-- A TLV stream is an ordered list of records. -/
structure TLVStream where
  records : List TLVRecord
deriving Repr, DecidableEq, BEq

namespace TLVRecord

/-- Encoded size of a record's two BigSize fields plus its value. -/
def encodedSize (r : TLVRecord) : Nat :=
  (Wire.encode r.type).size + (Wire.encode r.value.size).size + r.value.size

/-- A record is encoded as `BigSize(type) || BigSize(length) || value`. -/
def encode (r : TLVRecord) : ByteArray :=
  Wire.encode r.type ++ Wire.encode r.value.size ++ r.value

end TLVRecord

namespace TLVStream

/-- The list of record types, in stream order. -/
def types (s : TLVStream) : List Nat := s.records.map TLVRecord.type

/-- One record's encoded bytes. -/
def encodeRecord (r : TLVRecord) : ByteArray := TLVRecord.encode r

/-- The concatenation of all record encodings. -/
def encode (s : TLVStream) : ByteArray :=
  s.records.foldl (fun acc r => acc ++ TLVRecord.encode r) ByteArray.empty

end TLVStream

/-- The TLV `encode`/`decode` names required by the interface. -/
def encodeTLV (s : TLVStream) : ByteArray := s.encode

/-! ## Sortedness and uniqueness -/

/-- Strictly-increasing record types.  A one-element stream is sorted. -/
def SortedTypes : List Nat → Prop
  | [] => True
  | a :: b :: rest => a < b ∧ SortedTypes (b :: rest)
  | [_] => True

/-- A stream is sorted when its record types are. -/
def TLVStream.Sorted (s : TLVStream) : Prop := SortedTypes s.types

/-- A stream has unique types when its type list has no duplicates. -/
def TLVStream.Unique (s : TLVStream) : Prop := s.types.Nodup

/-- The BOLT 1 well-formedness condition for an outgoing stream. -/
def TLVStream.WellFormed (s : TLVStream) : Prop := s.Sorted ∧ s.Unique

/-- In a sorted list, every element after the head is greater than the head. -/
theorem sortedTypes_lt_of_mem_of_head {l : List Nat} :
    ∀ {a : Nat}, SortedTypes (a :: l) → ∀ x : Nat, x ∈ l → a < x := by
  induction l with
  | nil =>
      intro a h x hx
      cases hx
  | cons b rest ih =>
      intro a h x hx
      have hab : a < b := h.1
      have hs : SortedTypes (b :: rest) := h.2
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hab
      · exact Nat.lt_trans hab (ih hs x hx)

/-- A sorted list's head does not occur in its tail. -/
theorem sortedTypes_not_mem_head {a b : Nat} {rest : List Nat}
    (h : SortedTypes (a :: b :: rest)) : a ∉ b :: rest := by
  intro hmem
  have hlt : a < a := sortedTypes_lt_of_mem_of_head h a hmem
  exact Nat.lt_irrefl a hlt

/-- Strictly-increasing types are unique (BOLT 1: "hence MUST not produce more
than a single TLV record with the same type"). -/
theorem sortedTypes_nodup (l : List Nat) (h : SortedTypes l) : l.Nodup := by
  induction l with
  | nil => simp
  | cons a rest ih =>
      cases rest with
      | nil => simp
      | cons b rest' =>
          have hh : a < b ∧ SortedTypes (b :: rest') := h
          rw [List.nodup_cons]
          exact ⟨sortedTypes_not_mem_head h, ih hh.2⟩

/-- Sortedness implies type uniqueness for a TLV stream. -/
theorem sorted_implies_unique (s : TLVStream) (h : s.Sorted) : s.Unique :=
  sortedTypes_nodup s.types h

/-- A well-formed stream has no duplicate types. -/
theorem wellFormed_types_nodup (s : TLVStream) (h : s.WellFormed) : s.types.Nodup :=
  h.2

/-- A well-formed stream is sorted. -/
theorem wellFormed_sorted (s : TLVStream) (h : s.WellFormed) : s.Sorted :=
  h.1

/-- The empty stream is well formed. -/
theorem empty_wellFormed : (TLVStream.mk []).WellFormed := by
  constructor <;> simp [TLVStream.Sorted, TLVStream.Unique, TLVStream.types, SortedTypes]

/-- A one-record stream is well formed. -/
theorem singleton_wellFormed (r : TLVRecord) :
    (TLVStream.mk [r]).WellFormed := by
  constructor
  · simp [TLVStream.Sorted, TLVStream.types, SortedTypes]
  · simp [TLVStream.Unique, TLVStream.types]

/-! ## Encoding sizes -/

/-- A record's encoded size is the sum of its two BigSize fields and value. -/
theorem TLVRecord.encodedSize_eq (r : TLVRecord) :
    r.encodedSize = (Wire.encode r.type).size + (Wire.encode r.value.size).size + r.value.size :=
  rfl

/-- The encoded record has exactly `encodedSize` bytes. -/
theorem TLVRecord.encode_size (r : TLVRecord) :
    (TLVRecord.encode r).size = r.encodedSize := by
  simp [TLVRecord.encode, TLVRecord.encodedSize, ByteArray.size_append, Nat.add_assoc]

/-- Each BigSize field of a record is at most nine bytes. -/
theorem TLVRecord.encodedSize_le (r : TLVRecord) :
    r.encodedSize ≤ 27 + r.value.size := by
  have h1 : (Wire.encode r.type).size ≤ 9 := encode_size_le_nine r.type
  have h2 : (Wire.encode r.value.size).size ≤ 9 := encode_size_le_nine r.value.size
  unfold TLVRecord.encodedSize
  omega

/-! ## A total reference parser -/

/-- Parse one record from a byte list, returning the record and the remaining
bytes.  Failures cover short reads, non-canonical BigSize fields, and
truncated values. -/
def parseRecord (l : List UInt8) : Option (TLVRecord × List UInt8) :=
  match decode l.toByteArray with
  | none => none
  | some (ty, n1) =>
      let l1 := l.drop n1
      match decode l1.toByteArray with
      | none => none
      | some (len, n2) =>
          let l2 := l1.drop n2
          if l2.length < len then none
          else
            some (⟨ty, (l2.take len).toByteArray⟩, l2.drop len)

/-- Fuel-bounded parser.  Each successful record consumes at least two bytes,
so `size + 1` fuel is enough for any stream that fits in the input. -/
def decodeTLVGo : Nat → List UInt8 → Option (List TLVRecord)
  | 0, l => if l = [] then some [] else none
  | fuel + 1, l =>
      match l with
      | [] => some []
      | _ =>
          match parseRecord l with
          | none => none
          | some (r, rest) =>
              match decodeTLVGo fuel rest with
              | none => none
              | some rs => some (r :: rs)

/-- Decode a complete TLV stream from a byte array. -/
def decodeTLV (b : ByteArray) : Option TLVStream :=
  match decodeTLVGo (b.size + 1) (bytesToList b) with
  | none => none
  | some records => some ⟨records⟩

/-- The empty stream decodes to the empty record list. -/
theorem decodeTLV_empty : decodeTLV ByteArray.empty = some (TLVStream.mk []) := by
  unfold decodeTLV
  have hbytes : bytesToList ByteArray.empty = [] := rfl
  rw [hbytes]
  rfl

/-- Encoding the empty stream produces no bytes. -/
theorem encodeTLV_empty : encodeTLV (TLVStream.mk []) = ByteArray.empty := rfl

end LnLean.Wire
