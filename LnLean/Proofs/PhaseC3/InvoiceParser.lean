import LnLean
import LnLean.Payment.Invoice
import LnLean.Proofs.Payment.InvoiceProps
import LnLean.Wire.BigSize

/-!
# LnLean.Proofs.PhaseC3.InvoiceParser

English claim.  On the modelled BOLT 11 tagged-field subset consisting of the
payment hash (`p`, tag 1), payment secret (`s`, tag 16), description (`d`, tag
13), and expiry (`x`, tag 6), this module defines a canonical tag list
(`TagList`), a field encoder, and a field parser, and proves:

1. **Round trip.**  Parsing the encoding of a canonical tag list returns that
   exact list, in order.  Canonicality is the precondition: the payment hash
   and payment secret payloads must be 32 bytes (BOLT 11 `data_length` 52
   five-bit groups), the description payload must fit BOLT 11's 639-byte
   maximum, and the expiry integer must fit in `uint64`.  The encoder uses the
   minimum number of big-endian bytes for `x`, as BOLT 11 requires.
2. **Tag-code injectivity.**  The four tag numbers are pairwise distinct and
   all fit in the 5-bit `type` field.  The codes agree with
   `LnLean.Payment.Tag.code` on the corresponding constructors, so the local
   subset cannot drift from the invoice model.
3. **Fixed data lengths.**  `p` and `s` are 52 five-bit groups = 32 bytes;
   `d` and `x` are variable length.  These are linked to
   `LnLean.Payment.Tag.fixedDataLength` and to `Invoice.Valid`'s 32-byte
   payment-hash/payment-secret fields.
4. **Canonicality is necessary.**  A 31-byte payment hash is encoded but not
   parsed back; without the size precondition the round trip fails.  This is
   proved as an explicit counterexample, not hidden behind a hypothesis.
5. **No silent field loss.**  A successful parse consumes every input field
   and preserves the tag of each field (strengthened by round trip).

BOLT sections (pinned BOLTs commit
`1aadb719b4007c4cea0ba6e36b08c4fb53788dee`).
* BOLT 11 §Tagged Fields: `refs/bolts/11-payment-encoding.md:133-163`
  (5-bit type, 10-bit data length, 639-byte maximum, `p`/`s` length 52,
  `d` variable UTF-8, `x` variable big-endian seconds).
* BOLT 11 §Requirements: `refs/bolts/11-payment-encoding.md:165-214`
  (writer must use the minimum `data_length` for `x`, no leading zero
  field-elements; reader must fail a fixed-length field of the wrong length).
* BOLT 11 §Payer / Payee Requirements:
  `refs/bolts/11-payment-encoding.md:344-360` (expiry semantics, not restated
  here).

rust-lightning anchors at pinned commit
`fe4900930c6bd5786ec4203274d7cf312776a5a6`.
* `lightning-invoice/src/lib.rs:164` `MAX_TAGGED_FIELD_DATA_BYTES = 639`.
* `lightning-invoice/src/lib.rs:527` `enum TaggedField`.
* `lightning-invoice/src/lib.rs:613` tag constants (`p`=1, `d`=13, `x`=6,
  `s`=16, and the other BOLT 11 tags).
* `lightning-invoice/src/lib.rs:1322` `check_field_counts` (exactly one `p`,
  one `d`-or-`h`, one `s`; not enforced by this per-field parser).
* `lightning-invoice/src/lib.rs:1357` `check_payment_secret`.
* `lightning-invoice/src/de.rs:503` `parse_u64_be` (checked big-endian
  accumulation, overflow rejected).
* `lightning-invoice/src/de.rs:640` `ExpiryTime::from_base32`
  (`IntegerOverflowError` for values above `u64`).

What is explicitly NOT modelled.
* bech32/charset decoding, the checksum, the human-readable part, and the
  signable-digest bytes.  The parser starts from already-separated tagged
  fields; no bech32 correctness is claimed.
* The 5-bit group packing itself.  Fields are modelled as `ByteArray`, and
  the group-to-byte law is only the arithmetic
  `groupsToBytes 52 = 32`/`groupsToBytes 53 = 33` plus the trailing padding
  witness.  Bit-level padding and the 10-bit length prefix are obligations
  of the future wire encoder.
* UTF-8 validation of `d` and the `String` representation.  The description
  payload is modelled as opaque bytes, so a `d` field is accepted without a
  UTF-8 proof; closing this is the obligation `PC3-PC40-UTF8`.
* The `h` description-hash tag and every other tag (`n`, `c`, `f`, `r`, `9`,
  `m`).  Their fixed lengths are already recorded by
  `LnLean.Payment.Tag.fixedDataLength`, but this parser subset rejects them.
* Multiplicity and preference ordering of tags (BOLT 11 permits repeated `r`
  and requires "most preferred first" for repeats).  `TagList` is an ordered
  list; only per-value canonicality is required for the round trip.
* Signature checking, payment-hash/preimage soundness, and expiry semantics;
  those live in `LnLean.Payment.Invoice` and its proofs.
-/

namespace LnLean.Proofs.PhaseC3

open LnLean
open LnLean.Payment
open LnLean.Wire

set_option autoImplicit false

/-! ## 1. The four-tag subset and its codes -/

/-- The BOLT 11 tags modelled by this parser: the mandatory payment hash and
payment secret, the direct description, and the optional expiry. -/
inductive TagKind where
  | paymentHash
  | paymentSecret
  | description
  | expiry
deriving Repr, DecidableEq, BEq, Inhabited

namespace TagKind

/-- Numeric tag in the 5-bit `type` field.  Values are BOLT 11's `p`=1,
`s`=16, `d`=13, and `x`=6. -/
def code : TagKind → Nat
  | .paymentHash   => 1
  | .paymentSecret => 16
  | .description   => 13
  | .expiry        => 6

/-- Embedding into the invoice model's full tag enumeration. -/
def toTag : TagKind → Tag
  | .paymentHash   => .paymentHash
  | .paymentSecret => .paymentSecret
  | .description   => .description
  | .expiry        => .expiry

/-- The BOLT 11 fixed payload length in five-bit groups, where BOLT 11 fixes
one: `p` and `s` use 52 groups; `d` and `x` are variable. -/
def fixedGroups : TagKind → Option Nat
  | .paymentHash   => some 52
  | .paymentSecret => some 52
  | .description   => none
  | .expiry        => none

/-- The tag numbers are pairwise distinct, hence the tag-code map is
injective.  This is the local version of
`LnLean.Payment.Tag.code_injective`, restricted to the modelled subset. -/
theorem code_injective : Function.Injective code := by
  intro a b h
  cases a <;> cases b <;> simp [code] at h ⊢

/-- Every modelled tag fits in BOLT 11's 5-bit `type` field. -/
theorem code_lt_32 (k : TagKind) : code k < 32 := by
  cases k <;> decide

/-- The local codes agree with the full invoice model's `Tag.code`. -/
theorem toTag_code (k : TagKind) : Tag.code k.toTag = code k := by
  cases k <;> rfl

/-- The embedding preserves distinctness of tags. -/
theorem toTag_injective : Function.Injective toTag := by
  intro a b h
  cases a <;> cases b <;> simp [toTag] at h ⊢

/-- Tag-code injectivity across the embedding: two modelled tags with the same
BOLT 11 number are equal.  Derived from the invoice model's injectivity
theorem, not re-assumed. -/
theorem toTag_code_injective :
    Function.Injective (fun k : TagKind => Tag.code k.toTag) := by
  intro a b h
  exact toTag_injective (Tag.code_injective h)

/-- Fixed lengths in five-bit groups agree with the invoice model. -/
theorem toTag_fixedDataLength (k : TagKind) :
    Tag.fixedDataLength k.toTag = fixedGroups k := by
  cases k <;> rfl

/-- The four modelled tags, unfolded, so no case analysis is needed to read
off a length.  `p` is 52 groups (32 bytes), `s` is 52 groups (32 bytes), and
`d`/`x` are variable. -/
theorem fixedGroups_paymentHash : fixedGroups .paymentHash = some 52 := rfl

theorem fixedGroups_paymentSecret : fixedGroups .paymentSecret = some 52 := rfl

theorem fixedGroups_description : fixedGroups .description = none := rfl

theorem fixedGroups_expiry : fixedGroups .expiry = none := rfl

end TagKind

/-! ## 2. Five-bit groups to bytes -/

/-- The byte length of a payload of `g` five-bit groups: `g * 5` bits, padded
to whole bytes with zero bits.  BOLT 11 pads field data to a multiple of five
bits; the byte view used by this model follows that padding. -/
def groupsToBytes (g : Nat) : Nat := g * 5 / 8

/-- `p` is 52 groups = 260 bits = 32 bytes plus 4 padding bits. -/
theorem groupsToBytes_52 : groupsToBytes 52 = 32 := by decide

/-- `n` is 53 groups = 265 bits = 33 bytes plus 1 padding bit.  Recorded for
the fixed-length family even though `n` is outside this parser subset. -/
theorem groupsToBytes_53 : groupsToBytes 53 = 33 := by decide

/-- The exact padding arithmetic for the 52-group fields. -/
theorem groups52_bits : 52 * 5 = 32 * 8 + 4 := by decide

/-- The exact padding arithmetic for the 53-group payee key. -/
theorem groups53_bits : 53 * 5 = 33 * 8 + 1 := by decide

/-- A 32-byte payload is exactly the byte length of a 52-group field.  This is
the bridge used by the canonicality predicate below. -/
theorem groupsToBytes_52_eq {b : ByteArray} :
    b.size = groupsToBytes 52 ↔ b.size = 32 := by
  rw [groupsToBytes_52]

/-- `Invoice.Valid` already gives the 32-byte payment hash; this theorem
states it in the parser's group-to-byte vocabulary. -/
theorem valid_paymentHash_groups {i : Invoice} (h : i.Valid) :
    i.paymentHash.bytes.size = groupsToBytes 52 := by
  rw [groupsToBytes_52]
  exact h.paymentHashLength

/-- The corresponding statement for the payment secret. -/
theorem valid_paymentSecret_groups {i : Invoice} (h : i.Valid) :
    i.paymentSecret.bytes.size = groupsToBytes 52 := by
  rw [groupsToBytes_52]
  exact h.paymentSecretLength

/-- BOLT 11's maximum tagged-field payload is 639 bytes.  The parser enforces
it for the variable-length description. -/
theorem maxTaggedFieldDataBytes_eq : MAX_TAGGED_FIELD_DATA_BYTES = 639 := rfl

/-! ## 3. Canonical big-endian expiry integers -/

/-- The number of bytes needed for the minimum-length big-endian encoding of a
natural number: one byte for `0..255`, two for `256..65535`, and so on.
BOLT 11 requires the minimum `data_length` for `x` (no leading zero
field-elements). -/
def expiryWidth (n : Nat) : Nat :=
  if n < 256 then 1 else 1 + expiryWidth (n / 256)
termination_by n
decreasing_by
  exact Nat.div_lt_self (by omega) (by decide)

/-- The width is never zero, so every expiry payload has at least one byte. -/
theorem expiryWidth_pos (n : Nat) : 0 < expiryWidth n := by
  unfold expiryWidth
  split <;> omega

/-- The width is large enough: `n` fits in `expiryWidth n` bytes. -/
theorem expiryWidth_spec (n : Nat) : n < 256 ^ expiryWidth n := by
  refine Nat.strongRecOn n ?_
  intro n ih
  unfold expiryWidth
  split
  · assumption
  · rename_i hn
    have hdiv : n / 256 < 256 ^ expiryWidth (n / 256) :=
      ih (n / 256) (Nat.div_lt_self (by omega) (by decide))
    have hle : n / 256 + 1 ≤ 256 ^ expiryWidth (n / 256) :=
      Nat.succ_le_of_lt hdiv
    have hdecomp : 256 * (n / 256) + n % 256 = n := Nat.div_add_mod n 256
    have hmod : n % 256 < 256 := Nat.mod_lt n (by decide)
    have hmul : n < (n / 256 + 1) * 256 := by omega
    have hstep : (n / 256 + 1) * 256 ≤ 256 ^ expiryWidth (n / 256) * 256 :=
      Nat.mul_le_mul_right 256 hle
    have hpow : 256 ^ expiryWidth (n / 256) * 256 =
        256 ^ (expiryWidth (n / 256) + 1) := by
      rw [Nat.pow_succ]
    calc
      n < (n / 256 + 1) * 256 := hmul
      _ ≤ 256 ^ expiryWidth (n / 256) * 256 := hstep
      _ = 256 ^ (expiryWidth (n / 256) + 1) := hpow
      _ = 256 ^ (1 + expiryWidth (n / 256)) := by rw [Nat.add_comm]

/-- Minimum-width encodings are at most `k` bytes whenever the value fits in
`k` bytes.  Used with `k = 8` to bound `uint64` expiries. -/
theorem expiryWidth_le_of_lt {n k : Nat} (hk : 0 < k) (h : n < 256 ^ k) :
    expiryWidth n ≤ k := by
  have key : ∀ n : Nat, ∀ k : Nat, 0 < k → n < 256 ^ k → expiryWidth n ≤ k := by
    intro n
    refine Nat.strongRecOn n ?_
    intro n ih k hk h
    rcases k with _ | k'
    · omega
    · rcases k' with _ | k''
      · have h256 : (256 : Nat) ^ 1 = 256 := by decide
        rw [h256] at h
        unfold expiryWidth
        split <;> omega
      · have hexp : 256 ^ (k'' + 2) = 256 ^ (k'' + 1) * 256 := by
          rw [Nat.pow_succ]
        unfold expiryWidth
        split
        · omega
        · rename_i hn
          have hdiv : n / 256 < 256 ^ (k'' + 1) := by
            rw [Nat.div_lt_iff_lt_mul (by decide)]
            rw [hexp] at h
            exact h
          have hrec := ih (n / 256) (Nat.div_lt_self (by omega) (by decide))
            (k'' + 1) (by omega) hdiv
          omega
  exact key n k hk h

/-- A `uint64` expiry value needs at most eight bytes. -/
theorem expiryWidth_le_eight {n : Nat} (h : n < 2 ^ 64) : expiryWidth n ≤ 8 := by
  have hpow : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
  exact expiryWidth_le_of_lt (by decide) (by rwa [hpow])

/-- The payload of a canonical `x` field: its byte length is the minimum width
of the value it denotes.  Equivalently, the payload has no leading zero bytes
and no missing bytes. -/
def ExpiryCanonical (b : ByteArray) : Prop :=
  b.size = expiryWidth (decodeBE b)

/-- The canonicality test is decidable, so the parser can branch on it
without classical choice. -/
instance expiryCanonicalDecidable (b : ByteArray) : Decidable (ExpiryCanonical b) := by
  unfold ExpiryCanonical
  infer_instance

/-- Encoding an expiry with its minimum width produces a canonical payload. -/
theorem expiryCanonical_beBytes (n : Nat) :
    ExpiryCanonical (beBytes n (expiryWidth n)) := by
  unfold ExpiryCanonical
  rw [beBytes_size, decodeBE_beBytes_of_lt n (expiryWidth n) (expiryWidth_spec n)]

/-! ## 4. Tagged values and canonicality -/

/-- A semantic tagged-field value.  `description` carries the raw UTF-8
payload bytes (UTF-8 validity is not checked here); `expiry` carries seconds
and is encoded in minimum-width big-endian form. -/
inductive Value where
  | paymentHash (data : ByteArray)
  | paymentSecret (data : ByteArray)
  | description (data : ByteArray)
  | expiry (seconds : Nat)
deriving Repr, DecidableEq, BEq

namespace Value

/-- The tag kind of a value. -/
def kind : Value → TagKind
  | .paymentHash _   => .paymentHash
  | .paymentSecret _ => .paymentSecret
  | .description _   => .description
  | .expiry _        => .expiry

/-- The BOLT 11 tag of a value. -/
def tag (v : Value) : Tag := v.kind.toTag

/-- The payload bytes of a value.  The expiry payload is the minimum-width
big-endian encoding of the seconds value. -/
def data : Value → ByteArray
  | .paymentHash b   => b
  | .paymentSecret b => b
  | .description b   => b
  | .expiry n        => beBytes n (expiryWidth n)

/-- Per-value canonicality, the exact precondition of the round trip:

* `p` and `s` payloads are 32 bytes (52 five-bit groups);
* `d` payloads fit BOLT 11's 639-byte maximum;
* `x` values fit in `uint64`, so their minimum-width encoding has at most
  eight bytes and LDK's checked `parse_u64_be` accepts it.

The description has no UTF-8 conjunct because the payload is opaque bytes in
this model (obligation `PC3-PC40-UTF8`). -/
def Canonical : Value → Prop
  | .paymentHash b   => b.size = groupsToBytes 52
  | .paymentSecret b => b.size = groupsToBytes 52
  | .description b   => b.size ≤ MAX_TAGGED_FIELD_DATA_BYTES
  | .expiry n        => n < 2 ^ 64

theorem canonical_paymentHash_iff {b : ByteArray} :
    Canonical (.paymentHash b) ↔ b.size = 32 := by
  simp [Canonical, groupsToBytes_52]

theorem canonical_paymentSecret_iff {b : ByteArray} :
    Canonical (.paymentSecret b) ↔ b.size = 32 := by
  simp [Canonical, groupsToBytes_52]

theorem canonical_description_iff {b : ByteArray} :
    Canonical (.description b) ↔ b.size ≤ 639 := by
  simp [Canonical, maxTaggedFieldDataBytes_eq]

theorem canonical_expiry_iff {n : Nat} :
    Canonical (.expiry n) ↔ n < 2 ^ 64 := Iff.rfl

end Value

/-! ## 5. Fields, encoding, and parsing -/

/-- A tagged field after the 5-bit type and 10-bit length prefix have been
decoded: a BOLT 11 tag number plus payload bytes.  The length prefix and
bit-level padding are outside this model. -/
structure Field where
  tag : Tag
  data : ByteArray
deriving Repr, DecidableEq, BEq

/-- Encode one semantic value as a BOLT 11 tagged field. -/
def encodeField (v : Value) : Field :=
  { tag := v.tag, data := v.data }

/-- Encode an ordered tag list.  Order is preserved exactly. -/
def encodeFields (vs : List Value) : List Field :=
  vs.map encodeField

/-- Decode one tagged field on the modelled subset.  Unknown tags and
fixed-length payloads of the wrong size are rejected.  The description length
is checked against BOLT 11's 639-byte maximum.  The expiry payload must be
canonical (minimum length) and at most eight bytes, matching LDK's
`parse_u64_be`/`IntegerOverflowError` behaviour. -/
def decodeField (f : Field) : Option Value :=
  match f.tag with
  | .paymentHash =>
      if f.data.size = groupsToBytes 52 then some (.paymentHash f.data) else none
  | .paymentSecret =>
      if f.data.size = groupsToBytes 52 then some (.paymentSecret f.data) else none
  | .description =>
      if f.data.size ≤ MAX_TAGGED_FIELD_DATA_BYTES then
        some (.description f.data)
      else none
  | .expiry =>
      if f.data.size ≤ 8 ∧ ExpiryCanonical f.data then
        some (.expiry (decodeBE f.data))
      else none
  | _ => none

/-- Parse an ordered list of tagged fields.  Parsing fails if any field is
outside the subset or not canonical; it never drops a field silently. -/
def parseFields : List Field → Option (List Value)
  | [] => some []
  | f :: fs =>
      match decodeField f with
      | none => none
      | some v =>
          match parseFields fs with
          | none => none
          | some vs => some (v :: vs)

/-! ## 6. Basic decoder facts -/

/-- A decoded value always carries the tag of the field it came from. -/
theorem decodeField_tag {f : Field} {v : Value}
    (h : decodeField f = some v) : v.tag = f.tag := by
  obtain ⟨t, d⟩ := f
  cases t <;> simp only [decodeField] at h ⊢
  · split at h
    · simp only [Option.some.injEq] at h
      subst h
      rfl
    · simp at h
  · split at h
    · simp only [Option.some.injEq] at h
      subst h
      rfl
    · simp at h
  · split at h
    · simp only [Option.some.injEq] at h
      subst h
      rfl
    · simp at h
  · simp at h
  · simp at h
  · split at h
    · simp only [Option.some.injEq] at h
      subst h
      rfl
    · simp at h
  all_goals simp at h

/-- Decoding an encoded canonical value returns that value.  This is the
per-field round trip; the expiry case uses the minimum-width encoding law and
the `uint64` bound. -/
theorem decodeField_encodeField {v : Value} (h : v.Canonical) :
    decodeField (encodeField v) = some v := by
  cases v with
  | paymentHash b =>
      simp only [Value.Canonical] at h
      simp [encodeField, Value.tag, Value.kind, TagKind.toTag, Value.data,
        decodeField, h]
  | paymentSecret b =>
      simp only [Value.Canonical] at h
      simp [encodeField, Value.tag, Value.kind, TagKind.toTag, Value.data,
        decodeField, h]
  | description b =>
      simp only [Value.Canonical] at h
      simp [encodeField, Value.tag, Value.kind, TagKind.toTag, Value.data,
        decodeField, h]
  | expiry n =>
      simp only [Value.Canonical] at h
      have hsize : (beBytes n (expiryWidth n)).size = expiryWidth n :=
        beBytes_size n (expiryWidth n)
      have hle : expiryWidth n ≤ 8 := expiryWidth_le_eight h
      have hcan : ExpiryCanonical (beBytes n (expiryWidth n)) :=
        expiryCanonical_beBytes n
      have hdec : decodeBE (beBytes n (expiryWidth n)) = n :=
        decodeBE_beBytes_of_lt n (expiryWidth n) (expiryWidth_spec n)
      simp [encodeField, Value.tag, Value.kind, TagKind.toTag, Value.data,
        decodeField, hsize, hle, hcan, hdec]

/-- A successful parse preserves the tag of every field, in order. -/
theorem parseFields_tags {fs : List Field} {vs : List Value}
    (h : parseFields fs = some vs) :
    vs.map Value.tag = fs.map Field.tag := by
  induction fs generalizing vs with
  | nil =>
      simp only [parseFields, Option.some.injEq] at h
      subst h
      rfl
  | cons f fs ih =>
      simp only [parseFields] at h
      split at h
      · simp at h
      · rename_i v hv
        split at h
        · simp at h
        · rename_i vs' hvs
          simp only [Option.some.injEq] at h
          subst h
          simp only [List.map_cons, decodeField_tag hv, ih hvs]

/-- A successful parse consumes exactly one value per field; no field is
silently dropped or duplicated. -/
theorem parseFields_length {fs : List Field} {vs : List Value}
    (h : parseFields fs = some vs) : vs.length = fs.length := by
  induction fs generalizing vs with
  | nil =>
      simp only [parseFields, Option.some.injEq] at h
      subst h
      rfl
  | cons f fs ih =>
      simp only [parseFields] at h
      split at h
      · simp at h
      · split at h
        · simp at h
        · rename_i vs' hvs
          simp only [Option.some.injEq] at h
          subst h
          simp [ih hvs]

/-! ## 7. The canonical tag list and the round trip -/

/-- A canonical tag list: an ordered list whose every value satisfies the
per-field canonicality predicate.  Multiplicity and preference ordering are
invoice-level checks (LDK `check_field_counts`) and are not part of this
per-field parser contract. -/
structure TagList where
  values : List Value
  canonical : ∀ v ∈ values, v.Canonical

/-- List-level round trip: encoding a list of canonical values and parsing it
returns the same list. -/
theorem parseFields_encodeFields (vs : List Value)
    (h : ∀ v ∈ vs, v.Canonical) :
    parseFields (encodeFields vs) = some vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
      have hv : v.Canonical := h v (by simp)
      have hvs : ∀ w ∈ vs, w.Canonical := fun w hw => h w (by simp [hw])
      have htail : parseFields (List.map encodeField vs) = some vs := ih hvs
      simp only [encodeFields, List.map_cons, parseFields,
        decodeField_encodeField hv, htail]

namespace TagList

/-- Encode a canonical tag list. -/
def encode (l : TagList) : List Field := encodeFields l.values

/-- **Round trip.**  Parsing the encoding of a canonical tag list returns the
original list, in order.  This is the main theorem of the module. -/
theorem parse_encode (l : TagList) :
    parseFields (encode l) = some l.values := by
  have h := parseFields_encodeFields l.values l.canonical
  simpa [encode] using h

/-- Consequence: the encoded list parses successfully. -/
theorem parse_encode_isSome (l : TagList) :
    (parseFields (encode l)).isSome = true := by
  rw [parse_encode l]
  rfl

/-- Consequence: the round trip preserves the number of tags. -/
theorem parse_encode_length (l : TagList) :
    (parseFields (encode l)).map List.length = some l.values.length := by
  rw [parse_encode l]
  rfl

end TagList

/-- **Injectivity of canonical encoding.**  Two canonical tag lists with the
same encoding are equal.  Follows from the round trip; the canonicality
precondition cannot be dropped (see `roundtrip_needs_canonicality`). -/
theorem encodeFields_injective {a b : List Value}
    (ha : ∀ v ∈ a, v.Canonical) (hb : ∀ v ∈ b, v.Canonical)
    (h : encodeFields a = encodeFields b) : a = b := by
  have hpa : parseFields (encodeFields a) = some a :=
    TagList.parse_encode ⟨a, ha⟩
  have hpb : parseFields (encodeFields b) = some b :=
    TagList.parse_encode ⟨b, hb⟩
  rw [h] at hpa
  rw [hpa] at hpb
  exact Option.some.inj hpb

/-! ## 8. Canonicality is necessary: an explicit counterexample -/

/-- A 31-byte payload, one byte short of BOLT 11's 52 groups. -/
def shortHashBytes : ByteArray :=
  ByteArray.mk (List.replicate 31 (0 : UInt8)).toArray

theorem shortHashBytes_size : shortHashBytes.size = 31 := by decide

/-- A payment-hash value with a 31-byte payload is not canonical. -/
theorem shortHash_not_canonical : ¬ Value.Canonical (.paymentHash shortHashBytes) := by
  simp [Value.Canonical, shortHashBytes_size, groupsToBytes_52]

/-- **The canonicality precondition is necessary.**  There is a value whose
encoding is not parsed back: a 31-byte payment hash is encoded to a field but
the decoder rejects the wrong fixed length.  Without canonicality the round
trip is false. -/
theorem roundtrip_needs_canonicality :
    ∃ v : Value, ¬ v.Canonical ∧ decodeField (encodeField v) = none := by
  refine ⟨.paymentHash shortHashBytes, shortHash_not_canonical, ?_⟩
  simp [encodeField, Value.tag, Value.kind, TagKind.toTag, Value.data,
    decodeField, shortHashBytes_size, groupsToBytes_52]

/-- Dually, a canonical 32-byte payment hash is accepted. -/
theorem decodeField_paymentHash_of_size {b : ByteArray} (h : b.size = 32) :
    decodeField { tag := .paymentHash, data := b } = some (.paymentHash b) := by
  simp [decodeField, h, groupsToBytes_52]

end LnLean.Proofs.PhaseC3
