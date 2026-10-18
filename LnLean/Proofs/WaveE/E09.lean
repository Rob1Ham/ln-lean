/-
# Wave E — E09: TLV strict ordering and type uniqueness

**Catalog claim (LN-CR-005).**  A TLV stream is strictly sorted by type and has
no duplicate types.

**Model target.**  `LnLean.Wire.TLVStream.WellFormed`, which the model defines
as `TLVStream.Sorted ∧ TLVStream.Unique`.

This module establishes the following facts about that target:

* `WellFormed` unfolds exactly to strict sortedness of the record-type list plus
  type uniqueness, and strict sortedness alone already implies uniqueness.
* Strict sortedness is equivalent to the type list being pairwise strictly
  increasing; adjacent types are strictly increasing.
* A well-formed stream contains at most one record of each type.
* Appending a record whose type is greater than every existing type preserves
  well-formedness.
* The reference decoder does **not** enforce ordering: a byte stream with two
  `type = 1` records is accepted and yields a non-well-formed `TLVStream`.
  Hence the claim must be read as a property of well-formed (canonical) streams,
  not as a guarantee about arbitrary `decodeTLV` output.

All results are unconditional theorems about the model and every proof is
complete.
-/

import LnLean.Crypto.Hash
import LnLean.Crypto.Model
import LnLean.Crypto.Sig
import LnLean.Wire.BigSize
import LnLean.Wire.TLV
import LnLean.Wire.Message

namespace LnLean.Proofs.WaveE.E09

set_option autoImplicit false

open LnLean
open LnLean.Wire

-- OBLIGATION: LN-WE-E09

/-! ## Well-formedness: definitional characterisation -/

/-- `WellFormed` is exactly strict sortedness together with type uniqueness. -/
theorem waveE_e09_wellFormed_iff (s : TLVStream) :
    s.WellFormed ↔ s.Sorted ∧ s.Unique :=
  Iff.rfl

/-- A well-formed stream is strictly sorted by type. -/
theorem waveE_e09_wellFormed_sorted (s : TLVStream) (h : s.WellFormed) :
    s.Sorted :=
  h.1

/-- A well-formed stream has no duplicate types. -/
theorem waveE_e09_wellFormed_unique (s : TLVStream) (h : s.WellFormed) :
    s.Unique :=
  h.2

/-- A well-formed stream's type list is duplicate-free. -/
theorem waveE_e09_no_duplicate_types (s : TLVStream) (h : s.WellFormed) :
    s.types.Nodup :=
  h.2

/-- Because strictly increasing types are automatically distinct, the
uniqueness conjunct of `WellFormed` is redundant: well-formedness is exactly
strict sortedness. -/
theorem waveE_e09_wellFormed_iff_sorted (s : TLVStream) :
    s.WellFormed ↔ s.Sorted := by
  constructor
  · exact waveE_e09_wellFormed_sorted s
  · intro h
    exact ⟨h, sorted_implies_unique s h⟩

/-! ## Strict ordering, adjacent and pairwise -/

/-- Strict sortedness is pairwise strict increase of the type list. -/
theorem waveE_e09_sorted_pairwise_lt (l : List Nat) (h : SortedTypes l) :
    l.Pairwise (· < ·) := by
  induction l with
  | nil => simp
  | cons a rest ih =>
      cases rest with
      | nil => simp
      | cons b rest' =>
          rw [List.pairwise_cons]
          exact ⟨fun x hx => sortedTypes_lt_of_mem_of_head h x hx, ih h.2⟩

/-- Pairwise strict increase implies the model's `SortedTypes`.  Together with
`waveE_e09_sorted_pairwise_lt` this identifies the model's notion of strict
sortedness with the standard list predicate. -/
theorem waveE_e09_pairwise_lt_sorted (l : List Nat) (h : l.Pairwise (· < ·)) :
    SortedTypes l := by
  induction l with
  | nil => trivial
  | cons a rest ih =>
      cases rest with
      | nil => trivial
      | cons b rest' =>
          rw [List.pairwise_cons] at h
          exact ⟨h.1 b (by simp), ih h.2⟩

/-- A well-formed stream's type list is pairwise strictly increasing. -/
theorem waveE_e09_wellFormed_pairwise_lt (s : TLVStream) (h : s.WellFormed) :
    s.types.Pairwise (· < ·) :=
  waveE_e09_sorted_pairwise_lt s.types h.1

/-- The BOLT 1 local ordering requirement: adjacent record types in a
well-formed stream are strictly increasing. -/
theorem waveE_e09_adjacent_lt (s : TLVStream) (h : s.WellFormed)
    {r₁ r₂ : TLVRecord} {rest : List TLVRecord}
    (hr : s.records = r₁ :: r₂ :: rest) : r₁.type < r₂.type := by
  have hsort : SortedTypes (r₁.type :: r₂.type :: rest.map TLVRecord.type) := by
    have h' : SortedTypes (s.records.map TLVRecord.type) := h.1
    rw [hr] at h'
    simpa using h'
  exact hsort.1

/-! ## At most one record per type -/

/-- In a list whose image under `f` is duplicate-free, two members with the
same image are the same element. -/
private theorem eq_of_map_nodup {α β : Type} {f : α → β} :
    ∀ {l : List α}, (l.map f).Nodup →
      ∀ {a b : α}, a ∈ l → b ∈ l → f a = f b → a = b
  | [], _, _, _, ha, _, _ => by simp at ha
  | c :: cs, h, a, b, ha, hb, hf => by
      rw [List.map_cons, List.nodup_cons] at h
      obtain ⟨hnot, hnd⟩ := h
      rcases List.mem_cons.mp ha with rfl | ha'
      · rcases List.mem_cons.mp hb with rfl | hb'
        · rfl
        · exact absurd (List.mem_map.mpr ⟨b, hb', hf.symm⟩) hnot
      · rcases List.mem_cons.mp hb with rfl | hb'
        · exact absurd (List.mem_map.mpr ⟨a, ha', hf⟩) hnot
        · exact eq_of_map_nodup hnd ha' hb' hf

/-- **No duplicate types as records.**  In a well-formed stream, two records
with the same type are the very same record. -/
theorem waveE_e09_record_eq_of_type_eq (s : TLVStream) (h : s.WellFormed)
    {r₁ r₂ : TLVRecord} (h₁ : r₁ ∈ s.records) (h₂ : r₂ ∈ s.records)
    (ht : r₁.type = r₂.type) : r₁ = r₂ :=
  eq_of_map_nodup h.2 h₁ h₂ ht

/-- A well-formed stream has at most one occurrence of each type. -/
theorem waveE_e09_type_count_le_one (s : TLVStream) (h : s.WellFormed)
    (t : Nat) : s.types.count t ≤ 1 :=
  (List.nodup_iff_count.mp h.2) t

/-! ## Preservation under appending a larger type -/

/-- Appending a strictly larger type to a sorted type list keeps it sorted. -/
private theorem sortedTypes_append_singleton {l : List Nat} {a : Nat}
    (h : SortedTypes l) (hlt : ∀ x ∈ l, x < a) : SortedTypes (l ++ [a]) := by
  induction l with
  | nil => simp [SortedTypes]
  | cons b rest ih =>
      cases rest with
      | nil =>
          simp only [List.cons_append, List.nil_append]
          exact ⟨hlt b (by simp), trivial⟩
      | cons c rest' =>
          have hbc : b < c := h.1
          have hs : SortedTypes (c :: rest') := h.2
          have hih : SortedTypes ((c :: rest') ++ [a]) :=
            ih hs (fun x hx => hlt x (by simp [hx]))
          simp only [List.cons_append]
          exact ⟨hbc, hih⟩

/-- Appending a fresh record whose type is greater than every existing type
preserves well-formedness. -/
theorem waveE_e09_append_wellFormed (s : TLVStream) (r : TLVRecord)
    (h : s.WellFormed) (hgt : ∀ x ∈ s.types, x < r.type) :
    (TLVStream.mk (s.records ++ [r])).WellFormed := by
  constructor
  · show SortedTypes ((s.records ++ [r]).map TLVRecord.type)
    rw [List.map_append]
    simp only [List.map_singleton]
    exact sortedTypes_append_singleton h.1 hgt
  · show ((s.records ++ [r]).map TLVRecord.type).Nodup
    rw [List.map_append]
    simp only [List.map_singleton]
    rw [List.nodup_append]
    refine ⟨h.2, by simp, ?_⟩
    intro a ha b hb
    have hb' : b = r.type := by simpa using hb
    subst hb'
    intro hab
    have hlt := hgt a ha
    rw [hab] at hlt
    exact Nat.lt_irrefl r.type hlt

/-! ## Non-vacuity -/

/-- The empty stream is well formed. -/
theorem waveE_e09_empty_wellFormed : (TLVStream.mk []).WellFormed :=
  empty_wellFormed

/-- A one-record stream is well formed. -/
theorem waveE_e09_singleton_wellFormed (r : TLVRecord) :
    (TLVStream.mk [r]).WellFormed :=
  singleton_wellFormed r

/-! ## The decoder does not enforce well-formedness

BOLT 1 requires outgoing streams to be strictly ordered, but the model's
`decodeTLV` only parses records: it has no non-increasing-type check.  The
following checked counterexample is therefore the precise negative result for
any reading of LN-CR-005 as "every decoded stream is well formed". -/

/-- Two records with `type = 1` and distinct values. -/
def waveE_e09_duplicateTypeStream : TLVStream :=
  TLVStream.mk
    [⟨1, ([0x2a] : List UInt8).toByteArray⟩,
     ⟨1, ([0x2b] : List UInt8).toByteArray⟩]

/-- Its BOLT 1 encoding: `01 01 2a 01 01 2b`. -/
def waveE_e09_duplicateTypeBytes : ByteArray :=
  ([0x01, 0x01, 0x2a, 0x01, 0x01, 0x2b] : List UInt8).toByteArray

/-- A stream with two records of the same type is not well formed. -/
theorem waveE_e09_duplicateTypeStream_not_wellFormed :
    ¬ waveE_e09_duplicateTypeStream.WellFormed := by
  intro h
  have hs : SortedTypes waveE_e09_duplicateTypeStream.types := h.1
  unfold waveE_e09_duplicateTypeStream TLVStream.types at hs
  simp [SortedTypes] at hs

/-- The reference decoder accepts the duplicate-type byte stream. -/
theorem waveE_e09_decodeTLV_accepts_duplicate_types :
    decodeTLV waveE_e09_duplicateTypeBytes = some waveE_e09_duplicateTypeStream := by
  decide

/-- Consequently `decodeTLV` does not guarantee `WellFormed`. -/
theorem waveE_e09_decoded_not_wellFormed :
    ∃ (b : ByteArray) (s : TLVStream), decodeTLV b = some s ∧ ¬ s.WellFormed :=
  ⟨waveE_e09_duplicateTypeBytes, waveE_e09_duplicateTypeStream,
    waveE_e09_decodeTLV_accepts_duplicate_types,
    waveE_e09_duplicateTypeStream_not_wellFormed⟩

/-- The unconditional statement "every TLV stream is well formed" is false. -/
theorem waveE_e09_not_all_wellFormed : ¬ ∀ s : TLVStream, s.WellFormed := by
  intro hall
  exact waveE_e09_duplicateTypeStream_not_wellFormed (hall waveE_e09_duplicateTypeStream)

end LnLean.Proofs.WaveE.E09
