import LnLean.Proofs.Bitcoin.EcdsaConcreteTargets

/-!
# ECDSA domain targets: no fixed tag repairs `DigestBindsMod`

Wave 9 (`EcdsaConcreteTargets`) left the exact residual boundary of the
concrete ECDSA bridge visible:

* `ResidueBinding vendorVerify` says that `verifyImpl` binds only the reduced
  scalar `bytesToNatBE msg % n`, not the byte string.
* `DigestBindsMod fundingTag` was the additional side condition needed by
  `residueBinding_vendor_funding_eq_of_digestBinds` to recover transaction
  equality from two accepted signatures.
* `not_digestBindsMod_fundingTag` proved that this side condition fails for the
  particular funding tag, using `zeros 33` and the 33-byte encoding `nBytes33`
  of the group order.

The natural wave-10 question is whether a different *fixed* tag can repair the
interface.  This module answers it negatively and sharply:

* `bytesToNatBE_append` is the missing arithmetic lemma: big-endian decoding
  distributes over concatenation as
  `bytesToNatBE (a ++ b) = bytesToNatBE a * 256 ^ b.size + bytesToNatBE b`.
* `tagged_zeros_nBytes33_modEq` shows that for **every** tag, the two distinct
  33-byte messages `zeros 33` and `nBytes33` have congruent tagged values.
  The tag contributes the same `bytesToNatBE tag * 256 ^ 33` offset to both
  sides, while the suffixes differ by exactly `n`.
* `not_digestBindsMod_any_tag : ∀ tag, ¬ DigestBindsMod tag` and
  `no_digestBindsMod_anywhere : ¬ ∃ tag, DigestBindsMod tag` therefore rule
  out every fixed tag, not merely `fundingTag`.
* `not_digestBindsModOn33_any_tag` strengthens the failure to the full
  33-byte message domain: even fixing the message length to 33 does not make
  the raw residue map injective.  The collision is not a length artefact.
* `digest_domain_dichotomy` bundles the negative result with the exact
  positive repair: on `Canonical33` (33-byte encodings whose numeric value is
  already below `n`) every tag *does* bind.  This is the restricted-domain
  alternative left open by wave 9.  `canonical33_zeros` and
  `not_canonical33_nBytes33` show that the restriction is non-vacuous and
  that it excludes precisely the `nBytes33` side of the collision.

The conditional extraction theorem forms are preserved generically in
`residueBinding_vendor_eq_of_digestBinds_any_tag` and
`vendorEcdsaContract_eq_of_digestBinds_any_tag`.  Since their
`DigestBindsMod` hypothesis is now proved unsatisfiable for every tag, they
remain true but have no instance at the untyped `ByteArray` interface.  A
faithful repair must either restrict the message domain (as `Canonical33`
does) or move the binding obligation to a computational hash / collision
resistance assumption at a typed digest domain.  No unconditional ECDSA or
consensus-security claim is made here.
-/

namespace LnLean.Proofs.Bitcoin.EcdsaDomainTargets

set_option autoImplicit false

open Bitcoin.Crypto.Curve.Secp (bytesToNatBE n)
open Bitcoin.Crypto.Ecdsa.Verify
open LnLean
open LnLean.Crypto
open LnLean.Proofs.Bitcoin.EcdsaBridgeTargets
open LnLean.Proofs.Bitcoin.EcdsaConcreteTargets

/-! ## 1. Big-endian append arithmetic

`bytesToNatBE` is the vendored fold
`b.data.foldl (fun acc u => acc * 256 + u.toNat) 0`.  The two structural facts
needed below are the accumulator law for this fold and the resulting
concatenation law.  Both are proved for arbitrary `ByteArray`s; no tag or
secp256k1-specific input is used. -/

/-- The fold step of the vendored big-endian decoder. -/
private def beStep (acc : Nat) (u : UInt8) : Nat := acc * 256 + u.toNat

/-- `Array.foldl` is the list fold over `toList` (in the direction needed to
apply the list accumulator lemma). -/
private theorem array_foldl_eq_list (f : Nat → UInt8 → Nat) (init : Nat)
    (xs : Array UInt8) :
    Array.foldl f init xs = List.foldl f init xs.toList :=
  Eq.symm (Array.foldl_toList (f := f) (init := init) (xs := xs))

/-- **Accumulator law.**  Folding the big-endian step from an arbitrary
accumulator is the accumulated value shifted by `256 ^ length` plus the fold
from zero. -/
private theorem list_foldl_acc (l : List UInt8) (acc : Nat) :
    l.foldl beStep acc = acc * 256 ^ l.length + l.foldl beStep 0 := by
  induction l generalizing acc with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons, List.length_cons, beStep]
      rw [ih (acc * 256 + x.toNat), ih 0, ih (0 * 256 + x.toNat)]
      simp only [Nat.zero_mul, Nat.zero_add]
      rw [Nat.pow_succ, Nat.add_mul]
      rw [Nat.mul_assoc, Nat.mul_comm 256 (256 ^ xs.length), ← Nat.mul_assoc]
      rw [Nat.add_assoc]

/-- **Concatenation law for `bytesToNatBE`.**  This is the arithmetic lemma
wave 9 lacked: the numeric value of `a ++ b` is the value of `a` shifted by
the length of `b`, plus the value of `b`. -/
theorem bytesToNatBE_append (a b : ByteArray) :
    bytesToNatBE (a ++ b) =
      bytesToNatBE a * 256 ^ b.size + bytesToNatBE b := by
  unfold bytesToNatBE
  rw [ByteArray.data_append, Array.foldl_append]
  change Array.foldl beStep (Array.foldl beStep 0 a.data) b.data =
    Array.foldl beStep 0 a.data * 256 ^ b.size + Array.foldl beStep 0 b.data
  simp only [array_foldl_eq_list]
  have hbs : b.data.toList.length = b.size := by
    show b.data.toList.length = b.data.size
    rw [Array.length_toList]
  rw [list_foldl_acc b.data.toList (List.foldl beStep 0 a.data.toList), hbs]

/-! ## 2. Fixed-length big-endian injectivity

The canonical-domain theorem needs the fact that `bytesToNatBE` is injective
on messages of a fixed size.  This is proved by induction on the list,
extracting the leading byte from the value with `Nat.add_mod_eq_ite`. -/

/-- A fold of `beStep` from zero is strictly below `256 ^ length`. -/
private theorem list_foldl_lt_pow (l : List UInt8) :
    l.foldl beStep 0 < 256 ^ l.length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      rw [List.foldl_cons]
      simp only [beStep, Nat.zero_mul, Nat.zero_add]
      rw [list_foldl_acc xs x.toNat]
      simp only [List.length_cons]
      rw [Nat.pow_succ]
      have hx : x.toNat < 256 := by
        have := UInt8.toNat_lt x
        simpa using this
      have hle : (x.toNat + 1) * 256 ^ xs.length ≤ 256 ^ xs.length * 256 := by
        calc (x.toNat + 1) * 256 ^ xs.length
            ≤ 256 * 256 ^ xs.length :=
              Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hx)
          _ = 256 ^ xs.length * 256 := Nat.mul_comm _ _
      rw [Nat.succ_mul] at hle
      exact Nat.lt_of_lt_of_le (by omega) hle

/-- `bytesToNatBE` of a byte array is below `256 ^ size`. -/
theorem bytesToNatBE_lt_pow_size (m : ByteArray) :
    bytesToNatBE m < 256 ^ m.size := by
  unfold bytesToNatBE
  change Array.foldl beStep 0 m.data < 256 ^ m.size
  rw [array_foldl_eq_list]
  have hlen : m.data.toList.length = m.size := by
    show m.data.toList.length = m.data.size
    rw [Array.length_toList]
  rw [← hlen]
  exact list_foldl_lt_pow m.data.toList

/-- List-level fixed-length injectivity of the big-endian fold. -/
private theorem list_foldl_injective_of_length_eq {xs ys : List UInt8}
    (hlen : xs.length = ys.length)
    (h : xs.foldl beStep 0 = ys.foldl beStep 0) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
      have hys : ys = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)
      subst hys
      rfl
  | cons x xs ih =>
      cases ys with
      | nil => simp at hlen
      | cons y ys =>
          have hlen' : xs.length = ys.length := by simpa using hlen
          have hxval : (x :: xs).foldl beStep 0 =
              x.toNat * 256 ^ xs.length + xs.foldl beStep 0 := by
            rw [List.foldl_cons]
            simp only [beStep, Nat.zero_mul, Nat.zero_add]
            rw [list_foldl_acc xs x.toNat]
          have hyval : (y :: ys).foldl beStep 0 =
              y.toNat * 256 ^ ys.length + ys.foldl beStep 0 := by
            rw [List.foldl_cons]
            simp only [beStep, Nat.zero_mul, Nat.zero_add]
            rw [list_foldl_acc ys y.toNat]
          rw [hxval, hyval] at h
          rw [← hlen'] at h hyval
          have hVx : xs.foldl beStep 0 < 256 ^ xs.length := list_foldl_lt_pow xs
          have hVy : ys.foldl beStep 0 < 256 ^ xs.length := by
            have := list_foldl_lt_pow ys
            rwa [← hlen'] at this
          have hxy : x.toNat ≤ y.toNat := by
            apply Nat.le_of_not_gt
            intro hyx
            have hle : y.toNat * 256 ^ xs.length + 256 ^ xs.length ≤
                x.toNat * 256 ^ xs.length := by
              have h1 : (y.toNat + 1) * 256 ^ xs.length ≤
                  x.toNat * 256 ^ xs.length :=
                Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hyx)
              rwa [Nat.succ_mul] at h1
            omega
          have hyx : y.toNat ≤ x.toNat := by
            apply Nat.le_of_not_gt
            intro hxy'
            have hle : x.toNat * 256 ^ xs.length + 256 ^ xs.length ≤
                y.toNat * 256 ^ xs.length := by
              have h1 : (x.toNat + 1) * 256 ^ xs.length ≤
                  y.toNat * 256 ^ xs.length :=
                Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hxy')
              rwa [Nat.succ_mul] at h1
            omega
          have hxy_eq : x.toNat = y.toNat := by omega
          have hx_eq : x = y := UInt8.toNat.inj hxy_eq
          subst hx_eq
          have hvals : xs.foldl beStep 0 = ys.foldl beStep 0 := Nat.add_left_cancel h
          rw [ih hlen' hvals]

/-- **Fixed-length injectivity.**  On byte arrays of equal size, equal
big-endian values determine equal byte arrays. -/
theorem bytesToNatBE_injective_of_size_eq {m₁ m₂ : ByteArray}
    (hsize : m₁.size = m₂.size)
    (hval : bytesToNatBE m₁ = bytesToNatBE m₂) : m₁ = m₂ := by
  have hlen : m₁.data.toList.length = m₂.data.toList.length := by
    simp only [Array.length_toList, ByteArray.size_data]
    exact hsize
  have hv : m₁.data.toList.foldl beStep 0 = m₂.data.toList.foldl beStep 0 := by
    unfold bytesToNatBE at hval
    change Array.foldl beStep 0 m₁.data = Array.foldl beStep 0 m₂.data at hval
    simpa only [array_foldl_eq_list] using hval
  have hlist : m₁.data.toList = m₂.data.toList :=
    list_foldl_injective_of_length_eq hlen hv
  exact ByteArray.ext (Array.toList_inj.mp hlist)

/-! ## 3. The all-zero suffix and the suffix encoding `n` -/

/-- `zeros k` has size `k`. -/
theorem zeros_size (k : Nat) : (zeros k).size = k := by
  unfold zeros
  show (List.replicate k (0 : UInt8)).toArray.size = k
  rw [List.size_toArray, List.length_replicate]

/-- `zeros k` decodes to zero. -/
theorem bytesToNatBE_zeros (k : Nat) : bytesToNatBE (zeros k) = 0 := by
  unfold bytesToNatBE zeros
  rw [← Array.foldl_toList]
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [List.replicate_succ]
      simp only [List.foldl_cons]
      simpa using ih

/-- Appending the all-zero 33-byte suffix shifts the tag value by
`256 ^ 33`. -/
theorem bytesToNatBE_append_zeros33 (tag : ByteArray) :
    bytesToNatBE (tag ++ zeros 33) = bytesToNatBE tag * 256 ^ 33 := by
  rw [bytesToNatBE_append, bytesToNatBE_zeros, zeros_size, Nat.add_zero]

/-- Appending `nBytes33` shifts the tag value by `256 ^ 33` and then adds
exactly `n`. -/
theorem bytesToNatBE_append_nBytes33 (tag : ByteArray) :
    bytesToNatBE (tag ++ nBytes33) = bytesToNatBE tag * 256 ^ 33 + n := by
  rw [bytesToNatBE_append, bytesToNatBE_nBytes33, nBytes33_size]

/-- **Suffix-shift collision reduction.**  Any two equal-size suffixes whose
big-endian values differ by exactly `n` collide under every tag.  This isolates
the failure mechanism from the particular `fundingTag` and from the particular
`zeros 33` / `nBytes33` pair. -/
theorem tagged_modEq_of_value_add_n (tag a b : ByteArray)
    (hsize : a.size = b.size)
    (hval : bytesToNatBE b = bytesToNatBE a + n) :
    bytesToNatBE (tag ++ a) % n = bytesToNatBE (tag ++ b) % n := by
  rw [bytesToNatBE_append, bytesToNatBE_append, hsize, hval, ← Nat.add_assoc,
    Nat.add_mod_right]

/-- **Tag-independent collision.**  For every tag, the tagged all-zero
33-byte message and the tagged 33-byte encoding of `n` have equal reduced
value.  The tag contributes the same offset to both sides. -/
theorem tagged_zeros_nBytes33_modEq (tag : ByteArray) :
    bytesToNatBE (tag ++ zeros 33) % n =
      bytesToNatBE (tag ++ nBytes33) % n := by
  apply tagged_modEq_of_value_add_n tag (zeros 33) nBytes33
  · rw [zeros_size, nBytes33_size]
  · rw [bytesToNatBE_nBytes33, bytesToNatBE_zeros, Nat.zero_add]

/-! ## 4. No fixed tag binds the untyped `ByteArray` domain -/

/-- **Every fixed tag fails.**  The wave-9 funding-tag counterexample
generalizes: no tag whatsoever makes `DigestBindsMod` true, because the
distinct 33-byte messages `zeros 33` and `nBytes33` always collide. -/
theorem not_digestBindsMod_any_tag : ∀ tag : ByteArray, ¬ DigestBindsMod tag := by
  intro tag h
  have heq : zeros 33 = nBytes33 :=
    h (zeros 33) nBytes33 (tagged_zeros_nBytes33_modEq tag)
  exact nBytes33_ne_zeros33 heq.symm

/-- There is no tag at all that satisfies `DigestBindsMod`. -/
theorem no_digestBindsMod_anywhere :
    ¬ ∃ tag : ByteArray, DigestBindsMod tag := by
  rintro ⟨tag, h⟩
  exact not_digestBindsMod_any_tag tag h

/-- A concrete collision witness for every tag. -/
theorem digest_collision_witness_any_tag (tag : ByteArray) :
    ∃ m₁ m₂ : ByteArray, m₁ ≠ m₂ ∧
      bytesToNatBE (tag ++ m₁) % n = bytesToNatBE (tag ++ m₂) % n :=
  ⟨zeros 33, nBytes33, nBytes33_ne_zeros33.symm, tagged_zeros_nBytes33_modEq tag⟩

/-- **Even fixed-length 33-byte messages do not bind.**  The collision pair
has the same size, so length restriction alone cannot repair the interface. -/
theorem not_digestBindsModOn33_any_tag (tag : ByteArray) :
    ¬ (∀ m₁ m₂ : ByteArray, m₁.size = 33 → m₂.size = 33 →
      bytesToNatBE (tag ++ m₁) % n = bytesToNatBE (tag ++ m₂) % n → m₁ = m₂) := by
  intro h
  have heq : zeros 33 = nBytes33 :=
    h (zeros 33) nBytes33 (zeros_size 33) nBytes33_size
      (tagged_zeros_nBytes33_modEq tag)
  exact nBytes33_ne_zeros33 heq.symm

/-! ## 5. Conditional extraction forms are preserved, but unsatisfiable

The wave-9 extraction theorems are restated for an arbitrary tag.  Their
`DigestBindsMod` hypothesis is retained verbatim; the new impossibility theorem
shows that no tag instantiates it.  This makes the exact remaining alternative
explicit rather than hiding it behind a repaired-looking interface. -/

/-- Generic conditional extraction under reduced-message binding: any tag
whose tagged residue map is injective recovers message equality. -/
theorem residueBinding_vendor_eq_of_digestBinds_any_tag
    (h : ResidueBinding vendorVerify) (tag : ByteArray) (ht : DigestBindsMod tag)
    {key : PubKey} {m₁ m₂ : ByteArray} {sig : EcdsaSig}
    (h₁ : verifyImpl sig.bytes key.bytes (tag ++ m₁) = true)
    (h₂ : verifyImpl sig.bytes key.bytes (tag ++ m₂) = true) :
    m₁ = m₂ :=
  ht m₁ m₂ (h key (tag ++ m₁) (tag ++ m₂) sig h₁ h₂)

/-- The same extraction under the full wave-9 `VendorEcdsaContract`. -/
theorem vendorEcdsaContract_eq_of_digestBinds_any_tag
    (h : VendorEcdsaContract) (tag : ByteArray) (ht : DigestBindsMod tag)
    {key : PubKey} {m₁ m₂ : ByteArray} {sig : EcdsaSig}
    (h₁ : verifyImpl sig.bytes key.bytes (tag ++ m₁) = true)
    (h₂ : verifyImpl sig.bytes key.bytes (tag ++ m₂) = true) :
    m₁ = m₂ :=
  residueBinding_vendor_eq_of_digestBinds_any_tag h.1 tag ht h₁ h₂

/-- **The conditional extraction hypothesis is empty at this interface.**
For every tag, the side condition of the wave-9 extraction theorem is false. -/
theorem digestBindsMod_hypothesis_empty (tag : ByteArray) :
    DigestBindsMod tag ↔ False :=
  ⟨not_digestBindsMod_any_tag tag, False.elim⟩

/-! ## 6. The exact positive repair: a canonical 33-byte domain

The failure is caused by suffixes whose numeric values differ by `n`, not by
the tag and not by the message length.  Restricting messages to 33-byte
encodings whose value is already reduced (`< n`) removes exactly that
degree of freedom and yields a genuine, non-vacuous binding theorem for
every tag. -/

/-- `CanonicalOfSize k m` holds when `m` is a `k`-byte big-endian encoding
whose numeric value is already a reduced scalar, `bytesToNatBE m < n`. -/
def CanonicalOfSize (k : Nat) (m : ByteArray) : Prop :=
  m.size = k ∧ bytesToNatBE m < n

/-- The 33-byte canonical domain used by the wave-9 collision pair. -/
def Canonical33 (m : ByteArray) : Prop :=
  CanonicalOfSize 33 m

/-- Domain-restricted digest binding: `DigestBindsMod` with an explicit
message predicate `P`. -/
def DigestBindsModOn (P : ByteArray → Prop) (tag : ByteArray) : Prop :=
  ∀ m₁ m₂ : ByteArray, P m₁ → P m₂ →
    bytesToNatBE (tag ++ m₁) % n = bytesToNatBE (tag ++ m₂) % n → m₁ = m₂

/-- `n` is positive. -/
theorem n_pos : 0 < n := by decide

/-- The canonical domain is non-empty. -/
theorem canonical33_zeros : Canonical33 (zeros 33) := by
  constructor
  · exact zeros_size 33
  · rw [bytesToNatBE_zeros]
    exact n_pos

/-- The `nBytes33` collision side is *not* canonical: its value is exactly
`n`, so the canonical restriction excludes precisely the bad suffix. -/
theorem not_canonical33_nBytes33 : ¬ Canonical33 nBytes33 := by
  intro h
  have hv := h.2
  rw [bytesToNatBE_nBytes33] at hv
  exact Nat.lt_irrefl n hv

/-- Cancellation of a common prefix modulo `n`, for reduced summands. -/
private theorem mod_add_cancel_of_lt {r a b k : Nat}
    (hr : r < k) (ha : a < k) (hb : b < k)
    (h : (r + a) % k = (r + b) % k) : a = b := by
  rw [Nat.add_mod_eq_ite] at h
  rw [Nat.add_mod_eq_ite] at h
  simp only [Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h
  by_cases h1 : k ≤ r + a <;> by_cases h2 : k ≤ r + b
  · rw [ite_eq_left h1, ite_eq_left h2] at h; omega
  · rw [ite_eq_left h1, ite_eq_right h2] at h; omega
  · rw [ite_eq_right h1, ite_eq_left h2] at h; omega
  · rw [ite_eq_right h1, ite_eq_right h2] at h; omega

/-- **Positive canonical-domain theorem, general fixed size.**  For every tag
and every size `k`, the tagged residue map is injective on `k`-byte encodings
whose value is already reduced modulo `n`.  The value bound is the exact
missing condition; fixed-length injectivity then recovers the bytes. -/
theorem digestBindsModOn_canonicalOfSize (tag : ByteArray) (k : Nat) :
    DigestBindsModOn (CanonicalOfSize k) tag := by
  intro m₁ m₂ h₁ h₂ hmod
  rcases h₁ with ⟨hs₁, hv₁⟩
  rcases h₂ with ⟨hs₂, hv₂⟩
  simp only [bytesToNatBE_append, hs₁, hs₂] at hmod
  have hmod' : (bytesToNatBE tag * 256 ^ k % n + bytesToNatBE m₁) % n =
      (bytesToNatBE tag * 256 ^ k % n + bytesToNatBE m₂) % n := by
    have hleft : (bytesToNatBE tag * 256 ^ k + bytesToNatBE m₁) % n =
        (bytesToNatBE tag * 256 ^ k % n + bytesToNatBE m₁) % n := by
      calc (bytesToNatBE tag * 256 ^ k + bytesToNatBE m₁) % n
          = (bytesToNatBE tag * 256 ^ k % n + bytesToNatBE m₁ % n) % n :=
            Nat.add_mod _ _ _
        _ = (bytesToNatBE tag * 256 ^ k % n + bytesToNatBE m₁) % n := by
            rw [Nat.mod_eq_of_lt hv₁]
    have hright : (bytesToNatBE tag * 256 ^ k + bytesToNatBE m₂) % n =
        (bytesToNatBE tag * 256 ^ k % n + bytesToNatBE m₂) % n := by
      calc (bytesToNatBE tag * 256 ^ k + bytesToNatBE m₂) % n
          = (bytesToNatBE tag * 256 ^ k % n + bytesToNatBE m₂ % n) % n :=
            Nat.add_mod _ _ _
        _ = (bytesToNatBE tag * 256 ^ k % n + bytesToNatBE m₂) % n := by
            rw [Nat.mod_eq_of_lt hv₂]
    exact hleft.symm.trans (hmod.trans hright)
  have hvals : bytesToNatBE m₁ = bytesToNatBE m₂ :=
    mod_add_cancel_of_lt (Nat.mod_lt _ n_pos) hv₁ hv₂ hmod'
  exact bytesToNatBE_injective_of_size_eq (hs₁.trans hs₂.symm) hvals

/-- The 33-byte instance, matching the wave-9 collision pair. -/
theorem digestBindsModOn_canonical33 (tag : ByteArray) :
    DigestBindsModOn Canonical33 tag :=
  digestBindsModOn_canonicalOfSize tag 33

/-- The 32-byte canonical digest domain: the natural typed-digest instance of
the repair.  Every tag binds 32-byte digests whose value is already below `n`. -/
def CanonicalDigest32 (m : ByteArray) : Prop :=
  CanonicalOfSize 32 m

/-- Positive 32-byte digest theorem. -/
theorem digestBindsModOn_canonical32 (tag : ByteArray) :
    DigestBindsModOn CanonicalDigest32 tag :=
  digestBindsModOn_canonicalOfSize tag 32

/-- The canonical 32-byte domain is non-empty. -/
theorem canonical32_zeros : CanonicalDigest32 (zeros 32) := by
  constructor
  · exact zeros_size 32
  · rw [bytesToNatBE_zeros]
    exact n_pos

/-- Funding-domain extraction on the canonical domain.  This is the faithful
replacement for `residueBinding_vendor_funding_eq_of_digestBinds`: the
unrestricted `DigestBindsMod fundingTag` hypothesis is replaced by the
checkable value bound `Canonical33` on the two transaction byte strings. -/
theorem residueBinding_vendor_funding_eq_of_canonical33
    (h : ResidueBinding vendorVerify) {key : PubKey} {m₁ m₂ : ByteArray}
    {sig : EcdsaSig}
    (hm₁ : Canonical33 m₁) (hm₂ : Canonical33 m₂)
    (h₁ : verifyImpl sig.bytes key.bytes (fundingTag ++ m₁) = true)
    (h₂ : verifyImpl sig.bytes key.bytes (fundingTag ++ m₂) = true) :
    m₁ = m₂ :=
  digestBindsModOn_canonical33 fundingTag m₁ m₂ hm₁ hm₂
    (h key (fundingTag ++ m₁) (fundingTag ++ m₂) sig h₁ h₂)

/-- The same canonical-domain funding extraction under the full
`VendorEcdsaContract`. -/
theorem vendorEcdsaContract_funding_eq_of_canonical33
    (h : VendorEcdsaContract) {key : PubKey} {m₁ m₂ : ByteArray}
    {sig : EcdsaSig}
    (hm₁ : Canonical33 m₁) (hm₂ : Canonical33 m₂)
    (h₁ : verifyImpl sig.bytes key.bytes (fundingTag ++ m₁) = true)
    (h₂ : verifyImpl sig.bytes key.bytes (fundingTag ++ m₂) = true) :
    m₁ = m₂ :=
  residueBinding_vendor_funding_eq_of_canonical33 h.1 hm₁ hm₂ h₁ h₂

/-- **Domain dichotomy.**  For every tag: full `DigestBindsMod` is false,
the canonical 33-byte restriction is true, and even the unrestricted
fixed-length-33 domain is false.  The missing condition is therefore the
value bound `bytesToNatBE m < n`, not an alternative tag. -/
theorem digest_domain_dichotomy (tag : ByteArray) :
    (¬ DigestBindsMod tag) ∧
      DigestBindsModOn Canonical33 tag ∧
      ¬ (∀ m₁ m₂ : ByteArray, m₁.size = 33 → m₂.size = 33 →
        bytesToNatBE (tag ++ m₁) % n = bytesToNatBE (tag ++ m₂) % n → m₁ = m₂) :=
  ⟨not_digestBindsMod_any_tag tag, digestBindsModOn_canonical33 tag,
    not_digestBindsModOn33_any_tag tag⟩

end LnLean.Proofs.Bitcoin.EcdsaDomainTargets
