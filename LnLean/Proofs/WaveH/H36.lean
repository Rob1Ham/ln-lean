/-
# H36 — TLV unknown-type and value-minimality boundaries (`CONF-01`)

**Catalog issue.**  `CONF-01` (P2): the finite conformance suite covers 61
BigSize/TLV vectors, but `docs/OPEN-ISSUES.md` records *two declared model
gaps* in the TLV row:

1. **Unknown-type / namespace policy.**  BOLT 1 Appendix B requires an
   unknown **even** type such as `12 00` to be rejected by a namespace-aware
   decoder.  `LnLean.Wire.TLV` has no known-type set and no even/odd policy.
2. **Known-type value minimality.**  BOLT 1 Appendix B requires the `n1`
   `tu64 amount_msat` value `0001` to be rejected as a non-minimal integer
   encoding.  `LnLean.Wire.TLV` stores TLV values as opaque `ByteArray`s and
   never interprets them.

This module adds a **local** vector module (no shared fixture edit) that pins
the model's actual decisions at those two gaps and at the neighbouring
structural boundaries:

* unknown even/odd types, including large types and a non-minimal value;
* minimal versus non-minimal BigSize encodings of the TLV **type** and
  **length** fields (the model *does* enforce these);
* minimal versus non-minimal `tu64`-style **value** encodings (the model does
  *not* enforce these);
* duplicate types, both adjacent and non-adjacent (the parser accepts, the
  ordering admission rejects);
* truncation at every field boundary (the parser rejects the whole stream).

Two structural theorems make the two gaps non-vector-specific:

* `any_type_value_admitted`: **every** record type in the `uint64` domain with
  **every** value is admitted by `decodeAdmissible` (no namespace, no
  known-type length, no value check).
* `admission_value_opaque`: two decoded streams with the same type list get
  the same admission decision, whatever their value bytes are.

The exact acceptance boundary is
`decodeAdmissible_iff_sorted`: for a decoded stream, admission accepts **iff**
the record types are strictly increasing.  The parser/admission split is the
one already recorded in `LnLean.Proofs.Wire.TLVTargets`: `decodeTLV` itself
does not check ordering, and `decodeAdmissible` is the enforcement point.

## Scope

This is finite/local vector conformance plus structural theorems about the
existing `LnLean.Wire.TLV` model.  It does **not** add a namespace policy, a
known-type table, a `tu64`/message-value decoder, or a production decode path.
The two gap theorems are negative statements about the model, not BOLT
conformance claims.  The shared `tests/conformance/vectors.json` and
`scripts/check-conformance.py` are deliberately untouched; the corresponding
JSON additions are left to the parent.

**BOLT sections.**  BOLT 1 §Type-Length-Value Format; §Appendix B
(Type-Length-Value Test Vectors, including `12 00` and the non-minimal `n1`
`tu64` value); §Appendix C (duplicate types invalid).

-/

import LnLean.Proofs.Wire.TLVTargets

namespace LnLean.Proofs.WaveH.H36

set_option autoImplicit false

open LnLean
open LnLean.Wire

/-! ## Local vector helpers -/

/-- Local byte-array literal.  Kept in this module so no shared fixture file is
edited. -/
def bytes (l : List UInt8) : ByteArray := l.toByteArray

/-! ## Unknown types (declared model gap 1) -/

/-- BOLT 1 Appendix B unknown **even** type 18, empty value: `12 00`. -/
def unknownEven12 : ByteArray := bytes [0x12, 0x00]

/-- BOLT 1 Appendix B says `12 00` must be rejected by a namespace-aware
decoder.  The model's parser accepts it as an ordinary record. -/
theorem unknownEven12_decode :
    decodeTLV unknownEven12 = some (TLVStream.mk [⟨18, bytes []⟩]) := by
  decide

/-- The ordering admission also accepts the unknown even type, because it only
looks at the (singleton, trivially sorted) type list. -/
theorem unknownEven12_admission : decodeAdmissible unknownEven12 = true := by
  decide

/-- The same stream is well formed under the model's structural predicate.
This is why the model *cannot* express the namespace gap as a
`WellFormed` failure: the gap is a missing policy, not a broken predicate. -/
theorem unknownEven12_wellFormed :
    (TLVStream.mk [⟨18, bytes []⟩]).WellFormed :=
  singleton_wellFormed _

/-- **Declared gap 1, explicit.**  The parser returns the unknown even record
and the admission layer accepts it; no known-type/namespace filter exists. -/
theorem unknown_even_type_gap :
    decodeTLV unknownEven12 = some (TLVStream.mk [⟨18, bytes []⟩]) ∧
      decodeAdmissible unknownEven12 = true :=
  ⟨unknownEven12_decode, unknownEven12_admission⟩

/-- An unknown **odd** type 19, empty value: `13 00`.  BOLT 1 permits odd
unknown types to be ignored for forward compatibility; the model also has no
"ignore" processing and simply returns the record. -/
def unknownOdd19 : ByteArray := bytes [0x13, 0x00]

theorem unknownOdd19_decode :
    decodeTLV unknownOdd19 = some (TLVStream.mk [⟨19, bytes []⟩]) := by
  decide

theorem unknownOdd19_admission : decodeAdmissible unknownOdd19 = true := by
  decide

/-- An unknown odd type with a one-byte value: `13 01 2a`. -/
def unknownOdd19Value : ByteArray := bytes [0x13, 0x01, 0x2a]

theorem unknownOdd19Value_decode :
    decodeTLV unknownOdd19Value = some (TLVStream.mk [⟨19, bytes [0x2a]⟩]) := by
  decide

theorem unknownOdd19Value_admission : decodeAdmissible unknownOdd19Value = true := by
  decide

/-- The two declared gaps composed: unknown even type 18 with the
non-minimal value `0001`. -/
def unknownEven12NonMinimalValue : ByteArray := bytes [0x12, 0x02, 0x00, 0x01]

theorem unknownEven12NonMinimalValue_decode :
    decodeTLV unknownEven12NonMinimalValue =
      some (TLVStream.mk [⟨18, bytes [0x00, 0x01]⟩]) := by
  decide

theorem unknownEven12NonMinimalValue_admission :
    decodeAdmissible unknownEven12NonMinimalValue = true := by
  decide

/-- A singleton stream inherits the round trip from the canonical encoder. -/
theorem decodeTLV_singleton_of_inDomain (r : TLVRecord) (h : r.InDomain) :
    decodeTLV (encodeTLV (TLVStream.mk [r])) = some (TLVStream.mk [r]) :=
  decodeTLV_encodeTLV_of_wellFormed (TLVStream.mk [r]) (singleton_wellFormed r) (by
    intro r' hr'
    rcases List.mem_cons.mp hr' with rfl | hnil
    · exact h
    · cases hnil)

/-- A singleton stream is admitted for every in-domain record. -/
theorem decodeAdmissible_singleton_of_inDomain (r : TLVRecord) (h : r.InDomain) :
    decodeAdmissible (encodeTLV (TLVStream.mk [r])) = true :=
  decodeAdmissible_encodeTLV (TLVStream.mk [r]) (singleton_wellFormed r) (by
    intro r' hr'
    rcases List.mem_cons.mp hr' with rfl | hnil
    · exact h
    · cases hnil)

/-- The unknown-type gap is structural, not a property of type 18: every
in-domain record with **any** type and **any** value is admitted.  Equivalently,
the admission layer has no namespace, known-type length, or value check. -/
theorem any_type_value_admitted (ty : Nat) (v : ByteArray)
    (hty : ty < 18446744073709551616) (hv : v.size < 18446744073709551616) :
    decodeAdmissible (encodeTLV (TLVStream.mk [⟨ty, v⟩])) = true :=
  decodeAdmissible_singleton_of_inDomain ⟨ty, v⟩ ⟨hty, hv⟩

/-- The same general statement at the parser boundary: every in-domain
singleton record round-trips through `encodeTLV`/`decodeTLV`. -/
theorem any_singleton_roundtrip (ty : Nat) (v : ByteArray)
    (hty : ty < 18446744073709551616) (hv : v.size < 18446744073709551616) :
    decodeTLV (encodeTLV (TLVStream.mk [⟨ty, v⟩])) =
      some (TLVStream.mk [⟨ty, v⟩]) :=
  decodeTLV_singleton_of_inDomain ⟨ty, v⟩ ⟨hty, hv⟩

/-! ## Minimal versus non-minimal BigSize **type** encodings

The model does enforce BigSize minimality on the structural type field, because
`parseRecord` uses `Wire.decode`.  These boundary pairs show that the same type
value is accepted in its shortest form and rejected in every longer form. -/

/-- Type 252 (`0xfc`), the largest one-byte type. -/
def type252Minimal : ByteArray := bytes [0xfc, 0x00]

theorem type252Minimal_decode :
    decodeTLV type252Minimal = some (TLVStream.mk [⟨252, bytes []⟩]) := by
  decide

theorem type252Minimal_admission : decodeAdmissible type252Minimal = true := by
  decide

/-- Type 252 encoded with the `0xfd` tag: three bytes for a value that has a
one-byte canonical form. -/
def type252NonMinimalFd : ByteArray := bytes [0xfd, 0x00, 0xfc, 0x00]

theorem type252NonMinimalFd_decode : decodeTLV type252NonMinimalFd = none := by
  decide

theorem type252NonMinimalFd_admission : decodeAdmissible type252NonMinimalFd = false := by
  decide

/-- Type 253 (`0xfd`), the smallest three-byte type. -/
def type253MinimalFd : ByteArray := bytes [0xfd, 0x00, 0xfd, 0x00]

theorem type253MinimalFd_decode :
    decodeTLV type253MinimalFd = some (TLVStream.mk [⟨253, bytes []⟩]) := by
  decide

theorem type253MinimalFd_admission : decodeAdmissible type253MinimalFd = true := by
  decide

/-- Type 253 encoded with the `0xfe` tag: five bytes for a three-byte value. -/
def type253NonMinimalFe : ByteArray := bytes [0xfe, 0x00, 0x00, 0x00, 0xfd, 0x00]

theorem type253NonMinimalFe_decode : decodeTLV type253NonMinimalFe = none := by
  decide

theorem type253NonMinimalFe_admission : decodeAdmissible type253NonMinimalFe = false := by
  decide

/-- Type 65535 (`0xffff`), the largest three-byte type. -/
def type65535MinimalFd : ByteArray := bytes [0xfd, 0xff, 0xff, 0x00]

theorem type65535MinimalFd_decode :
    decodeTLV type65535MinimalFd = some (TLVStream.mk [⟨65535, bytes []⟩]) := by
  decide

theorem type65535MinimalFd_admission : decodeAdmissible type65535MinimalFd = true := by
  decide

/-- Type 65535 encoded with the `0xfe` tag. -/
def type65535NonMinimalFe : ByteArray :=
  bytes [0xfe, 0x00, 0x00, 0xff, 0xff, 0x00]

theorem type65535NonMinimalFe_decode : decodeTLV type65535NonMinimalFe = none := by
  decide

theorem type65535NonMinimalFe_admission :
    decodeAdmissible type65535NonMinimalFe = false := by
  decide

/-- Type 65536 (`0x10000`), the smallest five-byte type. -/
def type65536MinimalFe : ByteArray := bytes [0xfe, 0x00, 0x01, 0x00, 0x00, 0x00]

theorem type65536MinimalFe_decode :
    decodeTLV type65536MinimalFe = some (TLVStream.mk [⟨65536, bytes []⟩]) := by
  decide

theorem type65536MinimalFe_admission : decodeAdmissible type65536MinimalFe = true := by
  decide

/-- Type 65536 encoded with the `0xff` tag: nine bytes for a five-byte value. -/
def type65536NonMinimalFf : ByteArray :=
  bytes [0xff, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00]

theorem type65536NonMinimalFf_decode : decodeTLV type65536NonMinimalFf = none := by
  decide

theorem type65536NonMinimalFf_admission :
    decodeAdmissible type65536NonMinimalFf = false := by
  decide

/-- The largest `uint64` type, minimally encoded with the `0xff` tag. -/
def typeMaxMinimalFf : ByteArray :=
  bytes [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x00]

theorem typeMaxMinimalFf_decode :
    decodeTLV typeMaxMinimalFf =
      some (TLVStream.mk [⟨18446744073709551615, bytes []⟩]) := by
  decide

theorem typeMaxMinimalFf_admission : decodeAdmissible typeMaxMinimalFf = true := by
  decide

/-! ## Minimal versus non-minimal BigSize **length** encodings -/

/-- Length zero encoded in its unique one-byte form. -/
def lengthZeroMinimal : ByteArray := bytes [0x01, 0x00]

theorem lengthZeroMinimal_decode :
    decodeTLV lengthZeroMinimal = some (TLVStream.mk [⟨1, bytes []⟩]) := by
  decide

theorem lengthZeroMinimal_admission : decodeAdmissible lengthZeroMinimal = true := by
  decide

/-- Length zero encoded with the `0xfd` tag. -/
def lengthZeroNonMinimalFd : ByteArray := bytes [0x01, 0xfd, 0x00, 0x00]

theorem lengthZeroNonMinimalFd_decode : decodeTLV lengthZeroNonMinimalFd = none := by
  decide

theorem lengthZeroNonMinimalFd_admission :
    decodeAdmissible lengthZeroNonMinimalFd = false := by
  decide

/-- Length zero encoded with the `0xfe` tag. -/
def lengthZeroNonMinimalFe : ByteArray := bytes [0x01, 0xfe, 0x00, 0x00, 0x00, 0x00]

theorem lengthZeroNonMinimalFe_decode : decodeTLV lengthZeroNonMinimalFe = none := by
  decide

theorem lengthZeroNonMinimalFe_admission :
    decodeAdmissible lengthZeroNonMinimalFe = false := by
  decide

/-- Length zero encoded with the `0xff` tag. -/
def lengthZeroNonMinimalFf : ByteArray :=
  bytes [0x01, 0xff, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem lengthZeroNonMinimalFf_decode : decodeTLV lengthZeroNonMinimalFf = none := by
  decide

theorem lengthZeroNonMinimalFf_admission :
    decodeAdmissible lengthZeroNonMinimalFf = false := by
  decide

/-- Length one encoded in its unique one-byte form, with the value byte. -/
def lengthOneMinimal : ByteArray := bytes [0x01, 0x01, 0x2a]

theorem lengthOneMinimal_decode :
    decodeTLV lengthOneMinimal = some (TLVStream.mk [⟨1, bytes [0x2a]⟩]) := by
  decide

theorem lengthOneMinimal_admission : decodeAdmissible lengthOneMinimal = true := by
  decide

/-- Length one encoded with the `0xfd` tag. -/
def lengthOneNonMinimalFd : ByteArray := bytes [0x01, 0xfd, 0x00, 0x01, 0x2a]

theorem lengthOneNonMinimalFd_decode : decodeTLV lengthOneNonMinimalFd = none := by
  decide

theorem lengthOneNonMinimalFd_admission :
    decodeAdmissible lengthOneNonMinimalFd = false := by
  decide

/-! ## Minimal versus non-minimal `tu64` **value** encodings

`LnLean.Wire.TLV` treats a value as opaque bytes.  A local reference predicate
`MinimalTu64Value` records the BOLT 1 `tu64` convention used by known types
such as `n1 amount_msat`: the value must be the canonical (shortest) BigSize
encoding of an integer.  The model never consults this predicate, which is the
declared value-minimality gap. -/

/-- Local BOLT 1 `tu64` reference convention: the value bytes are exactly the
canonical BigSize encoding of some natural number. -/
def MinimalTu64Value (v : ByteArray) : Prop := ∃ n : Nat, Wire.encode n = v

theorem minimalTu64_zero : MinimalTu64Value (bytes [0x00]) :=
  ⟨0, by decide⟩

theorem minimalTu64_one : MinimalTu64Value (bytes [0x01]) :=
  ⟨1, by decide⟩

theorem minimalTu64_252 : MinimalTu64Value (bytes [0xfc]) :=
  ⟨252, by decide⟩

theorem minimalTu64_253 : MinimalTu64Value (bytes [0xfd, 0x00, 0xfd]) :=
  ⟨253, by decide⟩

theorem minimalTu64_65536 :
    MinimalTu64Value (bytes [0xfe, 0x00, 0x01, 0x00, 0x00]) :=
  ⟨65536, by decide⟩

/-- No BigSize encoding has two bytes, so no two-byte value is a minimal
`tu64`.  This is the exact reason `0001` (and every other leading-zero
two-byte integer value) is non-minimal. -/
theorem not_minimalTu64_of_size_two (v : ByteArray) (hv : v.size = 2) :
    ¬ MinimalTu64Value v := by
  rintro ⟨n, hn⟩
  have hsz := congrArg ByteArray.size hn
  rw [hv] at hsz
  rcases encode_size_cases n with h1 | h1 | h1 | h1 <;> omega

/-- The BOLT 1 Appendix B non-minimal `tu64` value `0001`. -/
theorem nonminimalTu64_zero_one :
    ¬ MinimalTu64Value (bytes [0x00, 0x01]) :=
  not_minimalTu64_of_size_two _ (by decide)

/-- Known type 1 with the minimal value `00` (zero). -/
def valueMinimalZero : ByteArray := bytes [0x01, 0x01, 0x00]

theorem valueMinimalZero_decode :
    decodeTLV valueMinimalZero = some (TLVStream.mk [⟨1, bytes [0x00]⟩]) := by
  decide

theorem valueMinimalZero_admission : decodeAdmissible valueMinimalZero = true := by
  decide

/-- Known type 1 with the minimal value `01` (one). -/
def valueMinimalOne : ByteArray := bytes [0x01, 0x01, 0x01]

theorem valueMinimalOne_decode :
    decodeTLV valueMinimalOne = some (TLVStream.mk [⟨1, bytes [0x01]⟩]) := by
  decide

theorem valueMinimalOne_admission : decodeAdmissible valueMinimalOne = true := by
  decide

/-- Known type 1 with the non-minimal value `0001`: BOLT 1 Appendix B's
rejected `n1` case. -/
def valueNonMinimalZeroOne : ByteArray := bytes [0x01, 0x02, 0x00, 0x01]

theorem valueNonMinimalZeroOne_decode :
    decodeTLV valueNonMinimalZeroOne =
      some (TLVStream.mk [⟨1, bytes [0x00, 0x01]⟩]) := by
  decide

theorem valueNonMinimalZeroOne_admission :
    decodeAdmissible valueNonMinimalZeroOne = true := by
  decide

/-- **Declared gap 2, explicit.**  The value is not a minimal `tu64` encoding,
yet the model's admission accepts the record: TLV values are opaque. -/
theorem value_minimality_gap :
    ¬ MinimalTu64Value (bytes [0x00, 0x01]) ∧
      decodeAdmissible valueNonMinimalZeroOne = true :=
  ⟨nonminimalTu64_zero_one, valueNonMinimalZeroOne_admission⟩

/-- Admission depends only on the type list: two decoded streams with equal
types receive equal decisions, regardless of their value bytes.  This is the
structural form of the value-opacity gap. -/
theorem admission_value_opaque {b c : ByteArray} {s t : TLVStream}
    (hb : decodeTLV b = some s) (hc : decodeTLV c = some t)
    (h : s.types = t.types) :
    decodeAdmissible b = decodeAdmissible c := by
  have hadm : TLVStream.admissible s = TLVStream.admissible t := by
    unfold TLVStream.admissible
    rw [h]
  unfold decodeAdmissible
  rw [hb, hc]
  exact hadm

/-! ## Exact acceptance characterization -/

/-- For a decoded stream, the admission layer accepts exactly when the record
types are strictly increasing.  Nothing else — no type membership, no known
length, no value interpretation — is checked. -/
theorem decodeAdmissible_iff_sorted {b : ByteArray} {s : TLVStream}
    (hd : decodeTLV b = some s) :
    decodeAdmissible b = true ↔ s.Sorted := by
  rw [decodeAdmissible_eq_true_iff]
  constructor
  · rintro ⟨t, ht, hwf⟩
    have hst : s = t := by
      rw [hd] at ht
      exact Option.some.inj ht
    subst hst
    exact hwf.1
  · intro hs
    exact ⟨s, hd, (TLVStream.wellFormed_iff_sorted s).mpr hs⟩

/-- A stream that fails well-formedness is rejected by the admission check. -/
theorem admissible_eq_false_of_not_wellFormed (s : TLVStream)
    (h : ¬ s.WellFormed) : s.admissible = false := by
  cases hb : s.admissible with
  | false => rfl
  | true => exact absurd ((TLVStream.admissible_eq_true_iff s).mp hb) h

/-! ## Duplicate types: parser accepts, admission rejects -/

/-- Two adjacent records with the same type and the same value. -/
def duplicateSameValue : ByteArray := bytes [0x01, 0x01, 0x2a, 0x01, 0x01, 0x2a]

theorem duplicateSameValue_decode :
    decodeTLV duplicateSameValue =
      some (TLVStream.mk [⟨1, bytes [0x2a]⟩, ⟨1, bytes [0x2a]⟩]) := by
  decide

theorem duplicateSameValue_admission :
    decodeAdmissible duplicateSameValue = false := by
  decide

/-- Two adjacent empty-type records (`0f 00 0f 00`). -/
def duplicateEmptyType15 : ByteArray := bytes [0x0f, 0x00, 0x0f, 0x00]

theorem duplicateEmptyType15_decode :
    decodeTLV duplicateEmptyType15 =
      some (TLVStream.mk [⟨15, bytes []⟩, ⟨15, bytes []⟩]) := by
  decide

theorem duplicateEmptyType15_admission :
    decodeAdmissible duplicateEmptyType15 = false := by
  decide

/-- A non-adjacent duplicate (`1, 2, 1`): caught by the sortedness check, not
merely by an adjacent-equality check. -/
def duplicateNonAdjacent : ByteArray :=
  bytes [0x01, 0x01, 0x2a, 0x02, 0x01, 0x2b, 0x01, 0x01, 0x2c]

theorem duplicateNonAdjacent_decode :
    decodeTLV duplicateNonAdjacent =
      some (TLVStream.mk
        [⟨1, bytes [0x2a]⟩, ⟨2, bytes [0x2b]⟩, ⟨1, bytes [0x2c]⟩]) := by
  decide

theorem duplicateNonAdjacent_admission :
    decodeAdmissible duplicateNonAdjacent = false := by
  decide

/-- Duplicate **unknown** even types: the parser accepts, admission rejects
because of ordering, independently of the missing namespace policy. -/
def duplicateUnknownEven : ByteArray := bytes [0x12, 0x00, 0x12, 0x00]

theorem duplicateUnknownEven_decode :
    decodeTLV duplicateUnknownEven =
      some (TLVStream.mk [⟨18, bytes []⟩, ⟨18, bytes []⟩]) := by
  decide

theorem duplicateUnknownEven_admission :
    decodeAdmissible duplicateUnknownEven = false := by
  decide

/-- Any decoded stream whose first two records share a type is rejected by
admission.  This is the general adjacent-duplicate rule, not a vector fact. -/
theorem admissible_false_of_adjacent_duplicate (ty : Nat) (v₁ v₂ : ByteArray)
    (rest : List TLVRecord) :
    ¬ (TLVStream.mk (⟨ty, v₁⟩ :: ⟨ty, v₂⟩ :: rest)).WellFormed := by
  intro h
  have hlt : ty < ty :=
    ((TLVStream.wellFormed_cons_cons ⟨ty, v₁⟩ ⟨ty, v₂⟩ rest).mp h).1
  exact Nat.lt_irrefl ty hlt

/-- Admission-level form of `admissible_false_of_adjacent_duplicate`. -/
theorem decodeAdmissible_false_of_adjacent_duplicate {b : ByteArray} {ty : Nat}
    {v₁ v₂ : ByteArray} {rest : List TLVRecord}
    (hd : decodeTLV b = some (TLVStream.mk (⟨ty, v₁⟩ :: ⟨ty, v₂⟩ :: rest))) :
    decodeAdmissible b = false := by
  unfold decodeAdmissible
  rw [hd]
  exact admissible_eq_false_of_not_wellFormed _
    (admissible_false_of_adjacent_duplicate ty v₁ v₂ rest)

/-- Any decoded stream whose head type reappears in the tail is rejected by
admission.  This covers non-adjacent duplicates generically. -/
theorem admissible_false_of_repeated_head (ty : Nat) (v : ByteArray)
    (rest : List TLVRecord) (hmem : ty ∈ rest.map TLVRecord.type) :
    ¬ (TLVStream.mk (⟨ty, v⟩ :: rest)).WellFormed := by
  cases rest with
  | nil => simp at hmem
  | cons r rest' =>
      intro h
      have hsort : SortedTypes (ty :: r.type :: rest'.map TLVRecord.type) := by
        simpa [TLVStream.Sorted, TLVStream.types] using h.1
      have hmem' : ty ∈ r.type :: rest'.map TLVRecord.type := by
        simpa using hmem
      exact sortedTypes_not_mem_head hsort hmem'

/-- Admission-level form of `admissible_false_of_repeated_head`. -/
theorem decodeAdmissible_false_of_repeated_head {b : ByteArray} {ty : Nat}
    {v : ByteArray} {rest : List TLVRecord}
    (hd : decodeTLV b = some (TLVStream.mk (⟨ty, v⟩ :: rest)))
    (hmem : ty ∈ rest.map TLVRecord.type) :
    decodeAdmissible b = false := by
  unfold decodeAdmissible
  rw [hd]
  exact admissible_eq_false_of_not_wellFormed _
    (admissible_false_of_repeated_head ty v rest hmem)

/-! ## Truncation at every field boundary -/

/-- A valid first record followed by a dangling type byte. -/
def truncatedAfterRecord : ByteArray := bytes [0x01, 0x01, 0x2a, 0x02]

theorem truncatedAfterRecord_decode : decodeTLV truncatedAfterRecord = none := by
  decide

theorem truncatedAfterRecord_admission :
    decodeAdmissible truncatedAfterRecord = false := by
  decide

/-- A dangling type byte plus the first byte of a `0xfd` length. -/
def truncatedLengthAfterRecord : ByteArray := bytes [0x01, 0x01, 0x2a, 0x02, 0xfd]

theorem truncatedLengthAfterRecord_decode :
    decodeTLV truncatedLengthAfterRecord = none := by
  decide

theorem truncatedLengthAfterRecord_admission :
    decodeAdmissible truncatedLengthAfterRecord = false := by
  decide

/-- A declared length of two with only one value byte present. -/
def truncatedValueShort : ByteArray := bytes [0x01, 0x02, 0x2a]

theorem truncatedValueShort_decode : decodeTLV truncatedValueShort = none := by
  decide

theorem truncatedValueShort_admission :
    decodeAdmissible truncatedValueShort = false := by
  decide

/-- A declared length of one with no value byte present. -/
def truncatedValueEmpty : ByteArray := bytes [0x01, 0x01]

theorem truncatedValueEmpty_decode : decodeTLV truncatedValueEmpty = none := by
  decide

theorem truncatedValueEmpty_admission :
    decodeAdmissible truncatedValueEmpty = false := by
  decide

/-- A `0xfe` type tag with only one of its four payload bytes. -/
def truncatedTypeFe : ByteArray := bytes [0xfe, 0x00]

theorem truncatedTypeFe_decode : decodeTLV truncatedTypeFe = none := by
  decide

theorem truncatedTypeFe_admission : decodeAdmissible truncatedTypeFe = false := by
  decide

/-- A `0xff` type tag with only three of its eight payload bytes. -/
def truncatedTypeFf : ByteArray := bytes [0xff, 0x00, 0x00, 0x00]

theorem truncatedTypeFf_decode : decodeTLV truncatedTypeFf = none := by
  decide

theorem truncatedTypeFf_admission : decodeAdmissible truncatedTypeFf = false := by
  decide

/-- A `0xfe` length tag with only two of its four payload bytes. -/
def truncatedLengthFe : ByteArray := bytes [0x01, 0xfe, 0x00, 0x00]

theorem truncatedLengthFe_decode : decodeTLV truncatedLengthFe = none := by
  decide

theorem truncatedLengthFe_admission : decodeAdmissible truncatedLengthFe = false := by
  decide

/-- A type byte with no length field at all. -/
def truncatedTypeOnly : ByteArray := bytes [0x02]

theorem truncatedTypeOnly_decode : decodeTLV truncatedTypeOnly = none := by
  decide

theorem truncatedTypeOnly_admission : decodeAdmissible truncatedTypeOnly = false := by
  decide

/-- A control stream with a complete one-byte length and value: the truncation
vectors above fail for the stated reason, not because all short inputs fail. -/
def completeControl : ByteArray := bytes [0x02, 0x02, 0x2a, 0x2b]

theorem completeControl_decode :
    decodeTLV completeControl = some (TLVStream.mk [⟨2, bytes [0x2a, 0x2b]⟩]) := by
  decide

theorem completeControl_admission : decodeAdmissible completeControl = true := by
  decide

/-! ## Boundary summary

The positive and negative vectors above partition the model's decisions:

* structural BigSize minimality is **enforced** for type and length
  (`type*Minimal*`/`*NonMinimal*`, `length*Minimal*`/`*NonMinimal*`);
* `tu64` value minimality is **not** enforced (`valueNonMinimalZeroOne`);
* namespace/known-type policy is **not** enforced
  (`unknownEven12`, `any_type_value_admitted`);
* ordering and duplicate suppression are enforced only by `decodeAdmissible`,
  not by `decodeTLV` (`duplicate*`, `decodeAdmissible_iff_sorted`);
* truncation is rejected by the parser at every field boundary (`truncated*`).
-/

end LnLean.Proofs.WaveH.H36
