/-
# Exact targets for `LN-CR-005`: TLV stream well-formedness

**English claim (catalog).**  A TLV stream is strictly sorted by type and has
no duplicate types.

`LnLean.Wire.TLVStream.WellFormed` is a predicate `def` (BOLT 1 §Type-Length-
Value Format):

```lean
def TLVStream.WellFormed (s : TLVStream) : Prop := s.Sorted ∧ s.Unique
```

A `def` cannot be promoted as a theorem, and the implication
`sorted → unique` was already proved in `LnLean/Wire/TLV.lean`.  This module
supplies the exact theorem-level content behind the row:

1. **Characterization.**  `wellFormed_iff_pairwise` proves that a stream is
   well formed *exactly* when its type list is pairwise strictly increasing;
   `wellFormed_record_type_unique` proves the operational reading of "no
   duplicate types": two records in a well-formed stream with equal type are
   the same record (type *and* value).  `wellFormed_cons_cons` is the
   record-level recursive characterization.
2. **Executable admission.**  `sortedTypesB` / `TLVStream.admissible` are a
   boolean decision procedure for the predicate, and
   `admissible_eq_true_iff` proves it exact.  `decodeAdmissible` combines the
   reference parser with the admission check, and
   `decodeAdmissible_eq_true_iff` proves that it accepts exactly the byte
   strings that decode to a well-formed stream.
3. **Encoder/decoder preservation.**  `decodeTLV_encodeTLV_of_wellFormed`
   proves that encoding a well-formed stream whose BigSize fields lie in the
   `uint64` domain, then decoding, returns the same stream.  The domain
   hypothesis is essential: `Wire.encode` truncates values above `2^64-1`.
4. **The parser gap is retained.**  `decodeTLV` does *not* enforce ordering
   (`TLVProps.decodeTLV_accepts_duplicate_types`); `duplicateStream` is the
   decoded duplicate-type stream, and
   `decodeAdmissible_duplicateTypeStream` proves that the admission layer
   rejects it.  No theorem `decodeTLV b = some s → s.WellFormed` exists or can
   exist, so the admission check — not the parser — is the enforcement point.

**BOLT sections.**  BOLT 1 §Type-Length-Value Format (record layout,
strictly-increasing types, minimal BigSize), §Appendix B: Type-Length-Value
Test Vectors, §Appendix C: Message Extension (duplicate types invalid).

**rust-lightning anchors (commit fe49009).**
* `lightning/src/util/ser.rs:442-490` — `BigSize` encoding/decoding.
* `lightning/src/util/ser_macros.rs:772-792` — `impl_writeable_msg!` appends
  the TLV stream after the fixed message fields.
* `lightning/src/ln/msgs.rs:3034-3052` — splice messages with TLV extensions.

**Not modelled / not claimed.**  Known-type length validation, even/odd
unknown-type policy, message-specific value decoding, TLV compression, and the
concrete test-vector runner.  The parser does not check ordering, so the
round-trip theorem is stated for canonical input only.  The admission predicate
defined here is not yet wired into a production decode path in
`LnLean/Wire/TLV.lean`.
-/

import LnLean.Proofs.Wire.TLVProps

namespace LnLean.Wire

set_option autoImplicit false

open LnLean

/-! ## A boolean decision procedure for strict ordering -/

/-- Executable form of `SortedTypes`: adjacent types strictly increase. -/
def sortedTypesB : List Nat → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => decide (a < b) && sortedTypesB (b :: rest)

/-- The boolean checker agrees with the inductive predicate. -/
theorem sortedTypesB_eq_true_iff (l : List Nat) :
    sortedTypesB l = true ↔ SortedTypes l := by
  induction l with
  | nil => simp [sortedTypesB, SortedTypes]
  | cons a rest ih =>
      cases rest with
      | nil => simp [sortedTypesB, SortedTypes]
      | cons b rest' =>
          simp only [sortedTypesB, SortedTypes, Bool.and_eq_true, decide_eq_true_eq]
          rw [ih]

/-- `SortedTypes` and its boolean checker accept the same lists. -/
theorem sortedTypes_iff_sortedTypesB (l : List Nat) :
    SortedTypes l ↔ sortedTypesB l = true :=
  (sortedTypesB_eq_true_iff l).symm

/-- Pairwise strict increase implies the adjacent-pair predicate.  This is the
converse of `sortedTypes_pairwise_lt`. -/
theorem sortedTypes_of_pairwise {l : List Nat} (h : l.Pairwise (· < ·)) :
    SortedTypes l := by
  induction l with
  | nil => trivial
  | cons a rest ih =>
      cases rest with
      | nil => trivial
      | cons b rest' =>
          rw [List.pairwise_cons] at h
          exact ⟨h.1 b (by simp), ih h.2⟩

/-- **No duplicate types at the record level.**  In a list of records with
strictly increasing types, equal types force equal records (type and value). -/
theorem sortedTypes_record_type_unique :
    ∀ (rs : List TLVRecord), SortedTypes (rs.map TLVRecord.type) →
      ∀ r₁ ∈ rs, ∀ r₂ ∈ rs, r₁.type = r₂.type → r₁ = r₂
  | [], _ => by intro r₁ h₁; cases h₁
  | [r], _ => by
      intro r₁ h₁ r₂ h₂ _
      rcases List.mem_cons.mp h₁ with rfl | h₁'
      · rcases List.mem_cons.mp h₂ with rfl | h₂'
        · rfl
        · cases h₂'
      · cases h₁'
  | r :: s :: rest, h => by
      simp only [List.map_cons] at h
      intro r₁ h₁ r₂ h₂ hty
      rcases List.mem_cons.mp h₁ with h₁r | h₁'
      · subst r₁
        rcases List.mem_cons.mp h₂ with h₂r | h₂'
        · subst r₂
          rfl
        · have hmem : r₂.type ∈ (s :: rest).map TLVRecord.type :=
            List.mem_map.mpr ⟨r₂, h₂', rfl⟩
          simp only [List.map_cons] at h hmem
          have hlt : r.type < r₂.type :=
            sortedTypes_lt_of_mem_of_head h r₂.type hmem
          exact absurd hty (Nat.ne_of_lt hlt)
      · rcases List.mem_cons.mp h₂ with h₂r | h₂'
        · subst r₂
          have hmem : r₁.type ∈ (s :: rest).map TLVRecord.type :=
            List.mem_map.mpr ⟨r₁, h₁', rfl⟩
          simp only [List.map_cons] at h hmem
          have hlt : r.type < r₁.type :=
            sortedTypes_lt_of_mem_of_head h r₁.type hmem
          exact absurd hty.symm (Nat.ne_of_lt hlt)
        · exact sortedTypes_record_type_unique (s :: rest) h.2 r₁ h₁' r₂ h₂' hty

/-! ## The exact branch of `WellFormed` -/

namespace TLVStream

/-- Executable BOLT 1 admission check for an outgoing stream: its record types
must be strictly increasing. -/
def admissible (s : TLVStream) : Bool := sortedTypesB s.types

/-- The admission check is exact for `WellFormed`.  The `Unique` half is
redundant once strict ordering is checked (`sorted_implies_unique`). -/
theorem admissible_eq_true_iff (s : TLVStream) :
    s.admissible = true ↔ s.WellFormed := by
  unfold TLVStream.WellFormed TLVStream.Sorted TLVStream.Unique
  rw [admissible, sortedTypesB_eq_true_iff]
  exact ⟨fun h => ⟨h, sortedTypes_nodup s.types h⟩, fun h => h.1⟩

/-- Well-formedness is exactly strict ordering of the type list.  This is the
strongest exact characterization available from the current API: the
`Unique` conjunct carries no additional information. -/
theorem wellFormed_iff_sorted (s : TLVStream) : s.WellFormed ↔ s.Sorted :=
  ⟨fun h => h.1, fun h => ⟨h, sorted_implies_unique s h⟩⟩

/-- The literal catalog reading: sorted types and no duplicate types. -/
theorem wellFormed_iff_sorted_nodup (s : TLVStream) :
    s.WellFormed ↔ s.Sorted ∧ s.types.Nodup :=
  Iff.rfl

/-- Well-formedness is exactly pairwise strict increase of the record types.
This converts the adjacent-pair definition `SortedTypes` into the
order-theoretic pairwise form used by BOLT 1 ("each type is strictly greater
than the previous one"). -/
theorem wellFormed_iff_pairwise (s : TLVStream) :
    s.WellFormed ↔ s.types.Pairwise (· < ·) := by
  rw [wellFormed_iff_sorted]
  unfold TLVStream.Sorted
  exact ⟨sortedTypes_pairwise_lt s.types, sortedTypes_of_pairwise⟩

/-- Record-level recursive characterization.  A stream with at least two
records is well formed exactly when its first type is below its second type and
the tail stream is well formed.  Together with `empty_wellFormed` and
`singleton_wellFormed` this is a complete structural definition of the
predicate. -/
theorem wellFormed_cons_cons (r₁ r₂ : TLVRecord) (rest : List TLVRecord) :
    (TLVStream.mk (r₁ :: r₂ :: rest)).WellFormed ↔
      r₁.type < r₂.type ∧ (TLVStream.mk (r₂ :: rest)).WellFormed := by
  constructor
  · intro h
    refine ⟨h.1.1, h.1.2, ?_⟩
    have hnodup : (r₁.type :: r₂.type :: rest.map TLVRecord.type).Nodup := h.2
    exact (List.nodup_cons.mp hnodup).2
  · rintro ⟨hlt, htail⟩
    refine ⟨⟨hlt, htail.1⟩, ?_⟩
    have htailNodup : (r₂.type :: rest.map TLVRecord.type).Nodup := htail.2
    show (r₁.type :: r₂.type :: rest.map TLVRecord.type).Nodup
    rw [List.nodup_cons]
    refine ⟨?_, htailNodup⟩
    intro hmem
    rcases List.mem_cons.mp hmem with heq | hmem'
    · exact Nat.lt_irrefl r₂.type (heq ▸ hlt)
    · have hgt : r₂.type < r₁.type :=
        sortedTypes_lt_of_mem_of_head htail.1 r₁.type hmem'
      exact Nat.lt_asymm hlt hgt

/-- **No duplicate types, operationally.**  In a well-formed stream, two
records with the same type are identical records; in particular the value is
determined by the position. -/
theorem wellFormed_record_type_unique (s : TLVStream) (h : s.WellFormed) :
    ∀ r₁ ∈ s.records, ∀ r₂ ∈ s.records, r₁.type = r₂.type → r₁ = r₂ :=
  sortedTypes_record_type_unique s.records h.1

/-- `WellFormed` is decidable via the exact boolean admission check. -/
def decidable_wellFormed (s : TLVStream) : Decidable s.WellFormed :=
  decidable_of_iff (s.admissible = true) s.admissible_eq_true_iff

end TLVStream

/-! ## The parser plus the admission check -/

/-- Decode a byte string and accept it only when the decoded stream is well
formed.  This is the enforcement point that BOLT 1 requires and that the raw
reference parser does not provide. -/
def decodeAdmissible (b : ByteArray) : Bool :=
  match decodeTLV b with
  | none => false
  | some s => s.admissible

/-- `decodeAdmissible` accepts exactly the byte strings whose decoded stream is
well formed. -/
theorem decodeAdmissible_eq_true_iff (b : ByteArray) :
    decodeAdmissible b = true ↔ ∃ s, decodeTLV b = some s ∧ s.WellFormed := by
  unfold decodeAdmissible
  cases decodeTLV b with
  | none => simp
  | some s =>
      dsimp only
      rw [TLVStream.admissible_eq_true_iff]
      constructor
      · intro hs
        exact ⟨s, rfl, hs⟩
      · rintro ⟨t, ht, hwf⟩
        have hst : s = t := Option.some.inj ht
        rw [hst]
        exact hwf

/-! ## Encoder/decoder preservation -/

/-- **Well-formedness is preserved by encode followed by decode**, provided the
BigSize fields are in the `uint64` domain.  This is the well-formedness
specialization of `decodeTLV_encodeTLV`; it avoids restating the full
`Canonical` package at call sites. -/
theorem decodeTLV_encodeTLV_of_wellFormed (s : TLVStream) (h : s.WellFormed)
    (hdom : ∀ r ∈ s.records, r.InDomain) :
    decodeTLV (encodeTLV s) = some s :=
  decodeTLV_encodeTLV s ⟨h.1, h.2, hdom⟩

/-- The decoded result of an encoded well-formed stream is well formed (and is
the original stream). -/
theorem decodeTLV_encodeTLV_wellFormed (s : TLVStream) (h : s.WellFormed)
    (hdom : ∀ r ∈ s.records, r.InDomain) :
    ∃ t, decodeTLV (encodeTLV s) = some t ∧ t.WellFormed :=
  ⟨s, decodeTLV_encodeTLV_of_wellFormed s h hdom, h⟩

/-- The admission check accepts the encoding of every well-formed
domain-respecting stream. -/
theorem decodeAdmissible_encodeTLV (s : TLVStream) (h : s.WellFormed)
    (hdom : ∀ r ∈ s.records, r.InDomain) :
    decodeAdmissible (encodeTLV s) = true := by
  rw [decodeAdmissible_eq_true_iff]
  exact ⟨s, decodeTLV_encodeTLV_of_wellFormed s h hdom, h⟩

/-- Canonical streams have injective encodings: two canonical streams with the
same bytes are the same stream.  Ordering and uniqueness are therefore part of
the serialization contract, not a decoder-side guess. -/
theorem encodeTLV_injective_of_canonical {s t : TLVStream}
    (hs : s.Canonical) (ht : t.Canonical) (h : encodeTLV s = encodeTLV t) :
    s = t := by
  have hs' := decodeTLV_encodeTLV s hs
  have ht' := decodeTLV_encodeTLV t ht
  rw [h, ht'] at hs'
  exact (Option.some.inj hs').symm

/-! ## The retained parser gap -/

/-- The duplicate-type stream that the reference parser returns for
`duplicateTypeStream` (`[0x01,0x01,0x2a, 0x01,0x01,0x2b]`). -/
def duplicateStream : TLVStream :=
  TLVStream.mk
    [⟨1, ([0x2a] : List UInt8).toByteArray⟩,
     ⟨1, ([0x2b] : List UInt8).toByteArray⟩]

/-- The reference parser returns the duplicate-type stream. -/
theorem decodeTLV_duplicateTypeStream :
    decodeTLV duplicateTypeStream = some duplicateStream := by
  rw [decodeTLV_accepts_duplicate_types]
  rfl

/-- That stream is not well formed: its types are `[1, 1]`. -/
theorem duplicateStream_not_wellFormed : ¬ duplicateStream.WellFormed := by
  intro h
  have hs : SortedTypes [1, 1] := h.1
  simp [SortedTypes] at hs

/-- The admission layer rejects the duplicate-type stream even though the raw
parser accepts it.  This is the exact statement of the parser/admission split:
`decodeTLV` alone does not establish `LN-CR-005`. -/
theorem decodeAdmissible_duplicateTypeStream :
    decodeAdmissible duplicateTypeStream = false := by
  unfold decodeAdmissible
  rw [decodeTLV_duplicateTypeStream]
  simp [duplicateStream, TLVStream.admissible, TLVStream.types, sortedTypesB]

/-! ## The `uint64` domain hypothesis is essential -/

/-- A singleton stream whose type exceeds the `uint64` BigSize domain. -/
def outOfDomainStream : TLVStream :=
  TLVStream.mk [⟨18446744073709551616, ByteArray.empty⟩]

/-- The out-of-domain stream is well formed as a record list: ordering and
uniqueness say nothing about BigSize representability. -/
theorem outOfDomainStream_wellFormed : outOfDomainStream.WellFormed :=
  singleton_wellFormed _

/-- `encode` truncates the type to eight zero bytes; the resulting `0xff`
followed by zeros is non-minimal, so `decode` rejects the whole stream.  The
unconditional encoder/decoder round trip for well-formed streams is therefore
**false**, not merely unproved. -/
theorem decodeTLV_encodeTLV_outOfDomainStream :
    decodeTLV (encodeTLV outOfDomainStream) = none := by
  decide

theorem outOfDomainStream_not_roundtrip :
    decodeTLV (encodeTLV outOfDomainStream) ≠ some outOfDomainStream := by
  rw [decodeTLV_encodeTLV_outOfDomainStream]
  simp

/-! ## Non-vacuity witness -/

/-- A two-record, strictly increasing stream. -/
def exampleStream : TLVStream :=
  TLVStream.mk
    [⟨1, ([0x2a] : List UInt8).toByteArray⟩,
     ⟨2, ([0x2b, 0x2c] : List UInt8).toByteArray⟩]

theorem exampleStream_wellFormed : exampleStream.WellFormed := by
  rw [TLVStream.wellFormed_iff_pairwise]
  simp [exampleStream, TLVStream.types]

theorem exampleStream_inDomain :
    ∀ r ∈ exampleStream.records, r.InDomain := by
  intro r hr
  simp [exampleStream] at hr
  rcases hr with rfl | rfl <;>
    simp [TLVRecord.InDomain]

/-- The encoder/decoder round trip is non-vacuous on this witness. -/
theorem exampleStream_decode_encode :
    decodeTLV (encodeTLV exampleStream) = some exampleStream :=
  decodeTLV_encodeTLV_of_wellFormed exampleStream exampleStream_wellFormed
    exampleStream_inDomain

theorem exampleStream_decodeAdmissible :
    decodeAdmissible (encodeTLV exampleStream) = true :=
  decodeAdmissible_encodeTLV exampleStream exampleStream_wellFormed
    exampleStream_inDomain

end LnLean.Wire
