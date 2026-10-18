/-
# Wave D / D08 — BigSize encoding and decoding are inverse on canonical encodings

**Catalog.** `LN-CR-004` — "BigSize encoding and decoding are inverse on
canonical encodings."  Target: `LnLean.Wire.BigSize.decode_encode`.
BOLT 1 §Fundamental Types and §Appendix A; `rust-lightning`
`lightning/src/util/ser.rs:442`.

**What this module establishes.**  The model already proves the forward
round trip `LnLean.Wire.decode_encode`: for every `uint64` value `n`,
`decode (encode n) = some (n, (encode n).size)`.  Here we expose that result
under the Wave-D names and add the parts of "inverse on canonical encodings"
that the model theorem alone does not spell out:

* the converse direction on the image of `encode`: a canonical encoding
  decodes to its unique source value and re-encodes to the same bytes
  (`waveD_d08_decode_canonical_encoding`);
* the strong converse for arbitrary bytes: if `decode` consumes the whole
  byte array then the array is a canonical encoding, and conversely
  (`waveD_d08_decode_full_canonical`, `waveD_d08_decode_full_iff`), using
  base-256 digit uniqueness (`waveD_d08_decodeBEList_inj`,
  `waveD_d08_beBytesAux_decodeBEList`);
* `encode` is injective on the `uint64` domain
  (`waveD_d08_encode_injective`);
* a complete `iff` characterisation of `decode (encode n)`
  (`waveD_d08_decode_encode_iff`);
* the encoded length is always one of `1, 3, 5, 9`
  (`waveD_d08_decode_encode_length_cases`);
* the minimality checks reject concrete non-canonical / short encodings
  (`waveD_d08_noncanonical_*`, `waveD_d08_short_*`);
* the `uint64` bound is essential in the model: `encode` truncates modulo
  `2^64`, and `decode (encode (2^64)) = none`, so the unconditional
  statement outside the bound is false (`waveD_d08_encode_truncates`).

The only hypothesis is the model's documented domain restriction
`n < 2^64`, which is exactly `uint64`; it is inherited from the model's
`decode_encode` and is not an additional assumption of the claim.

No `sorry`, no new axioms, no Mathlib.
-/

import LnLean.Crypto.Hash
import LnLean.Crypto.Model
import LnLean.Crypto.Sig
import LnLean.Wire.BigSize
import LnLean.Wire.TLV
import LnLean.Wire.Message

namespace LnLean.Proofs.WaveD.D08

set_option autoImplicit false

open LnLean
open LnLean.Wire

/-! ## The canonical-encoding predicate -/

/-- A byte array is a canonical BigSize encoding when it is exactly
`Wire.encode n` for a `uint64` value `n`. -/
def waveD_d08_IsCanonicalEncoding (b : ByteArray) : Prop :=
  ∃ n : Nat, n < 18446744073709551616 ∧ b = encode n

-- OBLIGATION: LN-WD-D08
/-- **Forward round trip.**  Decoding the canonical encoding of a `uint64`
returns the value and the number of bytes consumed.  This is the catalog
target `LnLean.Wire.BigSize.decode_encode`, restated under the Wave-D name. -/
theorem waveD_d08_decode_encode (n : Nat) (h : n < 18446744073709551616) :
    decode (encode n) = some (n, (encode n).size) :=
  LnLean.Wire.decode_encode n h

/-- **Converse on canonical encodings.**  If `b` is canonical and decodes to
`(v, len)`, then `v` is a `uint64`, `len` is the full byte length of `b`, and
re-encoding `v` recovers `b` exactly.  Together with
`waveD_d08_decode_encode` this says `decode` and `encode` are mutually inverse
on the canonical encodings. -/
theorem waveD_d08_decode_canonical_encoding {b : ByteArray}
    (hb : waveD_d08_IsCanonicalEncoding b) {v len : Nat}
    (hd : decode b = some (v, len)) :
    v < 18446744073709551616 ∧ len = b.size ∧ encode v = b := by
  rcases hb with ⟨n, hn, rfl⟩
  have h := waveD_d08_decode_encode n hn
  rw [h] at hd
  have hp : (n, (encode n).size) = (v, len) := Option.some.inj hd
  injection hp with hv hl
  subst hv
  exact ⟨hn, hl.symm, rfl⟩

/-- **`encode` is injective on `uint64`.**  Two values with the same canonical
encoding are equal.  This is the "decode then encode" inverse law read
contrapositively. -/
theorem waveD_d08_encode_injective {n m : Nat}
    (hn : n < 18446744073709551616) (hm : m < 18446744073709551616)
    (h : encode n = encode m) : n = m := by
  have h1 := waveD_d08_decode_encode n hn
  have h2 := waveD_d08_decode_encode m hm
  rw [h] at h1
  have hs : some (n, (encode m).size) = some (m, (encode m).size) :=
    h1.symm.trans h2
  exact congrArg Prod.fst (Option.some.inj hs)

/-- **Complete `iff` form of the round trip.**  For a `uint64` value `n`,
`decode (encode n)` succeeds exactly with the source value and the canonical
length. -/
theorem waveD_d08_decode_encode_iff (n m len : Nat)
    (hn : n < 18446744073709551616) :
    (decode (encode n) = some (m, len)) ↔
      (m = n ∧ len = (encode n).size) := by
  rw [waveD_d08_decode_encode n hn]
  constructor
  · intro h
    have hp : (n, (encode n).size) = (m, len) := Option.some.inj h
    exact ⟨(congrArg Prod.fst hp).symm, (congrArg Prod.snd hp).symm⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- **Canonical lengths.**  The length reported by a successful decode of the
canonical encoding of a `uint64` is one of `1`, `3`, `5`, `9`. -/
theorem waveD_d08_decode_encode_length_cases (n : Nat) :
    (encode n).size = 1 ∨ (encode n).size = 3 ∨
    (encode n).size = 5 ∨ (encode n).size = 9 :=
  LnLean.Wire.encode_size_cases n

/-! ## Auxiliary big-endian lemmas

These are the list-level facts needed for the converse direction: the
big-endian digit representation of a byte list is unique, and re-encoding
`decodeBEList` of a list at that list's own length returns the list. -/

/-- Every big-endian byte list decodes to a value below `256^length`. -/
theorem waveD_d08_decodeBEList_lt (l : List UInt8) :
    decodeBEList l < 256 ^ l.length := by
  induction l with
  | nil => simp [decodeBEList]
  | cons b rest ih =>
      rw [decodeBEList, List.length_cons, Nat.pow_succ]
      have hb : b.toNat ≤ 255 := by
        have h := UInt8.toNat_lt b
        omega
      have h1 : b.toNat * 256 ^ rest.length ≤ 255 * 256 ^ rest.length :=
        Nat.mul_le_mul_right _ hb
      have h2 : b.toNat * 256 ^ rest.length + decodeBEList rest <
          255 * 256 ^ rest.length + 256 ^ rest.length :=
        Nat.add_lt_add_of_le_of_lt h1 ih
      have h3 : 255 * 256 ^ rest.length + 256 ^ rest.length =
          256 ^ rest.length * 256 := by
        calc
          255 * 256 ^ rest.length + 256 ^ rest.length
              = 255 * 256 ^ rest.length + 1 * 256 ^ rest.length := by
                rw [Nat.one_mul]
          _ = (255 + 1) * 256 ^ rest.length := (Nat.add_mul 255 1 _).symm
          _ = 256 * 256 ^ rest.length := by rfl
          _ = 256 ^ rest.length * 256 := Nat.mul_comm _ _
      omega

/-- `decodeBEList` is injective on lists of equal length: base-256 digits are
unique. -/
theorem waveD_d08_decodeBEList_inj {l₁ l₂ : List UInt8}
    (hlen : l₁.length = l₂.length) (h : decodeBEList l₁ = decodeBEList l₂) :
    l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
      have : l₂.length = 0 := hlen.symm
      cases l₂ with
      | nil => rfl
      | cons _ _ => simp at this
  | cons b rest ih =>
      cases l₂ with
      | nil => simp at hlen
      | cons c rest₂ =>
          have hk : rest.length = rest₂.length := by simpa using hlen
          have hbnd₁ : decodeBEList rest < 256 ^ rest.length :=
            waveD_d08_decodeBEList_lt rest
          have hbnd₂ : decodeBEList rest₂ < 256 ^ rest₂.length :=
            waveD_d08_decodeBEList_lt rest₂
          have hbnd₂' : decodeBEList rest₂ < 256 ^ rest.length := by
            rw [← hk] at hbnd₂
            exact hbnd₂
          have hs : b.toNat * 256 ^ rest.length + decodeBEList rest =
              c.toNat * 256 ^ rest₂.length + decodeBEList rest₂ := by
            simpa [decodeBEList] using h
          have hs' : b.toNat * 256 ^ rest.length + decodeBEList rest =
              c.toNat * 256 ^ rest.length + decodeBEList rest₂ := by
            rw [← hk] at hs
            exact hs
          have hdiv : ∀ a d : Nat, d < 256 ^ rest.length →
              (a * 256 ^ rest.length + d) / 256 ^ rest.length = a := by
            intro a d hd
            rw [Nat.add_comm, Nat.add_mul_div_right _ _ (pow256_pos rest.length),
              Nat.div_eq_of_lt hd, Nat.zero_add]
          have hmod : ∀ a d : Nat, d < 256 ^ rest.length →
              (a * 256 ^ rest.length + d) % 256 ^ rest.length = d := by
            intro a d hd
            rw [Nat.add_comm, Nat.mul_comm a, Nat.add_mul_mod_self_left,
              Nat.mod_eq_of_lt hd]
          have hhead_nat : b.toNat = c.toNat := by
            have h₁ := hdiv b.toNat (decodeBEList rest) hbnd₁
            have h₂ := hdiv c.toNat (decodeBEList rest₂) hbnd₂'
            rw [hs'] at h₁
            exact h₁.symm.trans h₂
          have htail : decodeBEList rest = decodeBEList rest₂ := by
            have h₁ := hmod b.toNat (decodeBEList rest) hbnd₁
            have h₂ := hmod c.toNat (decodeBEList rest₂) hbnd₂'
            rw [hs'] at h₁
            exact h₁.symm.trans h₂
          have hhead : b = c := UInt8.toNat_inj.mp hhead_nat
          subst hhead
          rw [ih hk htail]

/-- Re-encoding `decodeBEList l` into `l.length` bytes gives back `l`. -/
theorem waveD_d08_beBytesAux_decodeBEList (l : List UInt8) :
    beBytesAux l.length (decodeBEList l) [] = l := by
  have hlen : (beBytesAux l.length (decodeBEList l) []).length = l.length := by
    rw [beBytesAux_length]
    simp
  have hdec : decodeBEList (beBytesAux l.length (decodeBEList l) []) =
      decodeBEList l := by
    rw [decodeBEList_beBytesAux]
    simp only [List.length_nil]
    rw [Nat.mul_one]
    exact Nat.mod_eq_of_lt (waveD_d08_decodeBEList_lt l)
  exact waveD_d08_decodeBEList_inj hlen hdec

/-- `bytesToList` is injective on byte arrays. -/
theorem waveD_d08_bytesToList_inj {a b : ByteArray}
    (h : bytesToList a = bytesToList b) : a = b :=
  ByteArray.ext (Array.toList_inj.mp h)

/-! ## The converse: a full decode identifies a canonical encoding

The forward round trip only says `encode` then `decode` is the identity.  For
the converse we need: if `decode` succeeds *and consumes the whole byte array*
then the array is exactly the canonical encoding of the decoded value.  This
is the direction that rules out non-canonical byte strings of a valid length,
and it uses the digit-uniqueness lemmas above.
-/

/-- **Full decode of arbitrary bytes.**  If `decode b` succeeds with a length
equal to `b.size`, then `b` is the canonical encoding of the decoded
`uint64` value.  Consequently the canonical encodings are *exactly* the byte
arrays on which `decode` consumes everything. -/
theorem waveD_d08_decode_full_canonical (b : ByteArray) (v len : Nat)
    (hd : decode b = some (v, len)) (hlen : len = b.size) :
    v < 18446744073709551616 ∧ encode v = b := by
  have hsize : (bytesToList b).length = b.size := bytesToList_length b
  rcases hbl : bytesToList b with _ | ⟨x, rest⟩
  · simp only [decode, hbl] at hd
    simp at hd
  · simp only [decode, hbl] at hd
    rw [hbl] at hsize
    by_cases hlt : x.toNat < 0xfd
    · -- one-byte case
      rw [ite_eq_left hlt] at hd
      have hp : (x.toNat, 1) = (v, len) := Option.some.inj hd
      have hv : x.toNat = v := congrArg Prod.fst hp
      have hl : 1 = len := congrArg Prod.snd hp
      have hs1 : (x :: rest).length = 1 := hsize.trans (hl.trans hlen).symm
      cases rest with
      | nil =>
          have hb : b = [x].toByteArray := by
            apply waveD_d08_bytesToList_inj
            rw [hbl, bytesToList_toByteArray]
          have hx : (x.toNat).toUInt8 = x := by
            apply UInt8.toNat_inj.mp
            rw [toUInt8_toNat_of_lt (by have := UInt8.toNat_lt x; omega)]
          refine ⟨by have := UInt8.toNat_lt x; omega, ?_⟩
          rw [hb, ← hv]
          simp [encode, hlt, oneByte, hx]
      | cons y ys => simp at hs1
    · by_cases hfd : x = 0xfd
      · -- 0xfd tag, two payload bytes
        rw [ite_eq_right hlt, ite_eq_left hfd] at hd
        unfold decodePayload at hd
        split at hd
        · simp at hd
        · rename_i hge
          dsimp only at hd
          split at hd
          · simp at hd
          · rename_i hgood
            have h1 : ¬ decodeBEList (rest.take 2) < 0xfd :=
              fun h => hgood (Or.inl h)
            have h2 : ¬ 0xffff < decodeBEList (rest.take 2) :=
              fun h => hgood (Or.inr h)
            have hlow : 0xfd ≤ decodeBEList (rest.take 2) := by omega
            have hhigh : decodeBEList (rest.take 2) ≤ 0xffff := by omega
            have hp : (decodeBEList (rest.take 2), 2 + 1) = (v, len) :=
              Option.some.inj hd
            have hv : decodeBEList (rest.take 2) = v := congrArg Prod.fst hp
            have hl : 2 + 1 = len := congrArg Prod.snd hp
            have hrl : rest.length = 2 := by
              have hs : (x :: rest).length = 3 := hsize.trans (hl.trans hlen).symm
              simp only [List.length_cons] at hs
              omega
            have htake : rest.take 2 = rest := List.take_of_length_le (by omega)
            have hvrest : v = decodeBEList rest := by
              rw [← hv, htake]
            have hbe : beBytesAux 2 v [] = rest := by
              rw [hvrest, ← hrl]
              exact waveD_d08_beBytesAux_decodeBEList rest
            have henc : encode v = b := by
              apply waveD_d08_bytesToList_inj
              rw [hbl]
              have hvlt : ¬ v < 0xfd := by omega
              simp only [encode, ite_eq_right hvlt, ite_eq_left (by omega : v ≤ 0xffff)]
              rw [bytesToList_append, bytesToList_oneByte, bytesToList_beBytes, hbe,
                hfd]
              simp
            exact ⟨by omega, henc⟩
      · by_cases hfe : x = 0xfe
        · -- 0xfe tag, four payload bytes
          rw [ite_eq_right hlt, ite_eq_right hfd, ite_eq_left hfe] at hd
          unfold decodePayload at hd
          split at hd
          · simp at hd
          · rename_i hge
            dsimp only at hd
            split at hd
            · simp at hd
            · rename_i hgood
              have h1 : ¬ decodeBEList (rest.take 4) < 0x10000 :=
                fun h => hgood (Or.inl h)
              have h2 : ¬ 0xffffffff < decodeBEList (rest.take 4) :=
                fun h => hgood (Or.inr h)
              have hlow : 0x10000 ≤ decodeBEList (rest.take 4) := by omega
              have hhigh : decodeBEList (rest.take 4) ≤ 0xffffffff := by omega
              have hp : (decodeBEList (rest.take 4), 4 + 1) = (v, len) :=
                Option.some.inj hd
              have hv : decodeBEList (rest.take 4) = v := congrArg Prod.fst hp
              have hl : 4 + 1 = len := congrArg Prod.snd hp
              have hrl : rest.length = 4 := by
                have hs : (x :: rest).length = 5 := hsize.trans (hl.trans hlen).symm
                simp only [List.length_cons] at hs
                omega
              have htake : rest.take 4 = rest := List.take_of_length_le (by omega)
              have hvrest : v = decodeBEList rest := by
                rw [← hv, htake]
              have hbe : beBytesAux 4 v [] = rest := by
                rw [hvrest, ← hrl]
                exact waveD_d08_beBytesAux_decodeBEList rest
              have henc : encode v = b := by
                apply waveD_d08_bytesToList_inj
                rw [hbl]
                have hvlt : ¬ v < 0xfd := by omega
                have hvgt : ¬ v ≤ 0xffff := by omega
                simp only [encode, ite_eq_right hvlt, ite_eq_right hvgt,
                  ite_eq_left (by omega : v ≤ 0xffffffff)]
                rw [bytesToList_append, bytesToList_oneByte, bytesToList_beBytes, hbe,
                  hfe]
                simp
              exact ⟨by omega, henc⟩
        · -- 0xff tag, eight payload bytes
          rw [ite_eq_right hlt, ite_eq_right hfd, ite_eq_right hfe] at hd
          unfold decodePayload at hd
          split at hd
          · simp at hd
          · rename_i hge
            have hxff : x = 0xff := by
              apply UInt8.toNat_inj.mp
              have h255 : (0xff : UInt8).toNat = 255 := by decide
              rw [h255]
              have h253 : (0xfd : UInt8).toNat = 253 := by decide
              have h254 : (0xfe : UInt8).toNat = 254 := by decide
              have h1 : x.toNat ≠ 253 := by
                intro h
                exact hfd (UInt8.toNat_inj.mp (by rw [h253]; exact h))
              have h2 : x.toNat ≠ 254 := by
                intro h
                exact hfe (UInt8.toNat_inj.mp (by rw [h254]; exact h))
              have h3 : x.toNat < 256 := by
                have h := UInt8.toNat_lt x
                have hpow : 2 ^ 8 = 256 := by decide
                omega
              omega
            dsimp only at hd
            split at hd
            · simp at hd
            · rename_i hgood
              have hlow : 0x100000000 ≤ decodeBEList (rest.take 8) := by
                omega
              have hp : (decodeBEList (rest.take 8), 8 + 1) = (v, len) :=
                Option.some.inj hd
              have hv : decodeBEList (rest.take 8) = v := congrArg Prod.fst hp
              have hl : 8 + 1 = len := congrArg Prod.snd hp
              have hrl : rest.length = 8 := by
                have hs : (x :: rest).length = 9 :=
                  hsize.trans (hl.trans hlen).symm
                simp only [List.length_cons] at hs
                omega
              have htake : rest.take 8 = rest :=
                List.take_of_length_le (by omega)
              have hvrest : v = decodeBEList rest := by
                rw [← hv, htake]
              have hbe : beBytesAux 8 v [] = rest := by
                rw [hvrest, ← hrl]
                exact waveD_d08_beBytesAux_decodeBEList rest
              have hbound : v < 18446744073709551616 := by
                have hbnd : decodeBEList rest < 256 ^ rest.length :=
                  waveD_d08_decodeBEList_lt rest
                rw [hrl] at hbnd
                have hp8 : 256 ^ 8 = 18446744073709551616 := by decide
                rw [hp8] at hbnd
                rw [hvrest]
                exact hbnd
              have henc : encode v = b := by
                apply waveD_d08_bytesToList_inj
                rw [hbl]
                have hvlt : ¬ v < 0xfd := by omega
                have hvgt1 : ¬ v ≤ 0xffff := by omega
                have hvgt2 : ¬ v ≤ 0xffffffff := by omega
                simp only [encode, ite_eq_right hvlt, ite_eq_right hvgt1, ite_eq_right hvgt2]
                rw [bytesToList_append, bytesToList_oneByte, bytesToList_beBytes,
                  hbe, hxff]
                simp
              exact ⟨hbound, henc⟩

/-- **Characterisation of full decodes.**  A byte array decodes completely
(value `v`, length equal to its size) exactly when `v` is a `uint64` and the
array is the canonical encoding of `v`.  This is the two-sided inverse law on
canonical encodings. -/
theorem waveD_d08_decode_full_iff (b : ByteArray) (v : Nat) :
    decode b = some (v, b.size) ↔
      (v < 18446744073709551616 ∧ waveD_d08_IsCanonicalEncoding b ∧
        b = encode v) := by
  constructor
  · intro hd
    obtain ⟨hv, henc⟩ := waveD_d08_decode_full_canonical b v b.size hd rfl
    exact ⟨hv, ⟨v, hv, henc.symm⟩, henc.symm⟩
  · rintro ⟨hv, ⟨n, hn, hbn⟩, hbv⟩
    have hvn : v = n := by
      apply waveD_d08_encode_injective hv hn
      rw [← hbv, hbn]
    have h := waveD_d08_decode_encode n hn
    rw [hbn, hvn]
    exact h

/-! ## Canonicality is enforced by the decoder

The `decodePayload` checks reject a multi-byte tag carrying a value that would
fit in a shorter encoding.  The following closed examples are computed by the
kernel and show the minimality rule in action. -/

/-- A `0xfd` tag whose payload is `1 < 0xfd` is non-minimal and rejected. -/
theorem waveD_d08_noncanonical_fd_small :
    decode ([0xfd, 0x00, 0x01].toByteArray) = none := by
  decide

/-- The boundary just below the `0xfd` range is rejected under a `0xfd` tag. -/
theorem waveD_d08_noncanonical_fd_boundary :
    decode ([0xfd, 0x00, 0xfc].toByteArray) = none := by
  decide

/-- A `0xfe` tag carrying `0xffff` (which fits in a `0xfd` encoding) is
rejected. -/
theorem waveD_d08_noncanonical_fe_small :
    decode ([0xfe, 0x00, 0x00, 0xff, 0xff].toByteArray) = none := by
  decide

/-- A `0xff` tag carrying `0xffffffff` (which fits in a `0xfe` encoding) is
rejected. -/
theorem waveD_d08_noncanonical_ff_small :
    decode ([0xff, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0xff, 0xff].toByteArray)
      = none := by
  decide

/-- A truncated `0xfd` payload is rejected (short read). -/
theorem waveD_d08_short_fd_payload :
    decode ([0xfd, 0x01].toByteArray) = none := by
  decide

/-- A truncated `0xff` payload is rejected (short read). -/
theorem waveD_d08_short_ff_payload :
    decode ([0xff, 0x01, 0x02, 0x03].toByteArray) = none := by
  decide

/-- A canonical non-minimal value is still accepted at its own width: the
`0xfd` encoding of `0xfd` itself is canonical and round-trips. -/
theorem waveD_d08_fd_lower_boundary :
    decode (encode 0xfd) = some (0xfd, 3) := by
  rw [waveD_d08_decode_encode 0xfd (by decide)]
  decide

/-! ## The `uint64` bound is essential -/

/-- **Truncation counterexample.**  `encode` is a `Nat` function that writes
exactly eight payload bytes for values above `0xffffffff`, so it truncates
modulo `2^64`.  In particular the canonical-looking nine-byte encoding of
`2^64` is all zeroes and is rejected by the decoder's minimality check.
Thus `decode (encode n) = some (n, (encode n).size)` is *false* without the
`n < 2^64` hypothesis of the catalog claim. -/
theorem waveD_d08_encode_truncates :
    encode 18446744073709551616
      = [0xff, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00].toByteArray ∧
    decode (encode 18446744073709551616) = none := by
  decide

/-- The truncation is observable as a failed round trip: the value `2^64` does
not decode back to itself. -/
theorem waveD_d08_decode_encode_fails_above_uint64 :
    decode (encode 18446744073709551616) ≠
      some (18446744073709551616, (encode 18446744073709551616).size) := by
  rw [waveD_d08_encode_truncates.2]
  simp

end LnLean.Proofs.WaveD.D08
