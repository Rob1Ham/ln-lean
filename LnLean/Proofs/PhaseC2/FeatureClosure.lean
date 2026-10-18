import LnLean.Proofs.Protocol.FeaturesProps

/-!
# LnLean.Proofs.PhaseC2.FeatureClosure

## English claim

BOLT 9 represents feature `n` by the adjacent bit pair `2*n` (even,
required) and `2*n+1` (odd, optional).  `LnLean.Proofs.Protocol.FeaturesProps`
models this as a `FeatureVector` (a bit predicate plus a wire byte length),
with `requires`, `offersOptional`, `supports`, `intersection` (bitwise AND),
and BOLT 1's `negotiated` rule.

This module proves the closure laws of that model:

1. **Acceptance is closed under intersection.**  If a receiver accepts two
   vectors (no unknown even bit is set in either), it accepts their bitwise
   intersection.  Dually, acceptance is closed under union.
2. **Intersection is idempotent, commutative, and associative**, and it
   preserves BOLT 1's padding condition `Bounded`.
3. **Requirement in an intersection is exactly conjunction**: the even bit of
   feature `n` is set in `intersection f g` iff it is set in both `f` and `g`.
   Consequently an optional feature can never become required by intersection:
   if neither peer sets the even bit, the intersection does not set it either.
   The odd bit obeys the same pointwise conjunction law.
4. **Negotiation is idempotent**: `negotiated f f n = f.supports n`, and
   `mutualSupport f f n = f.supports n`.
5. **Negotiation is commutative exactly when** the two peers share support for
   `n` or neither requires `n`.  BOLT 1's unrestricted rule is *not*
   commutative (a required bit is an asymmetric disjunct); the strongest
   usable conditional form is `negotiated_comm_of_mutually_accepted`, where
   each peer supports every feature the other requires.  A concrete
   counterexample records the failure without that hypothesis.
6. The support set of a bitwise intersection is contained in the intersection
   of the support sets, but equality can fail (FeaturesProps'
   `bitwiseIntersection_not_negotiation`): two peers may support a feature
   through different bits of the pair.  Negotiated support is therefore
   `mutualSupport`, not the raw bitwise `intersection`.

The required-bit predicate is stated both through the existing Boolean
`FeatureVector.requires` and through the Prop-valued `Required` defined below,
so the closure statements are readable as set/bit properties.

## BOLT sections

* BOLT 9 §"Assigned Feature Flags" (`refs/bolts/09-features.md:11-15`):
  adjacent even/odd pairs.  `:73`: the two bits of a pair must not both be
  set.  `:79-80`: when both bits are set the receiver treats the pair as
  mandatory.
* BOLT 1 §"The `init` Message" (`refs/bolts/01-messaging.md:268-330`): bit
  numbering (`:272-274`), zero padding (`:278`), combining the global and
  local bitmaps with OR (`:318`), and the unknown odd/even receive rule
  (`:320-323`).  Because acceptance ignores unknown odd bits, intersecting
  even bits is the acceptance-preserving operation.

## rust-lightning anchors (commit fe49009)

* `lightning-types/src/features.rs:286-290`: `EVEN_BIT`/`ODD_BIT`, the
  adjacent-pair encoding.
* `lightning-types/src/features.rs:322-333`: `requires_feature` tests the
  even bit; `supports_feature` tests the OR of both bits.
* `lightning-types/src/features.rs:336-356`: `set_required_bit` /
  `set_optional_bit`; setting one bit clears the other bit of the pair.
* `lightning-types/src/features.rs:1042-1091`: `requires_unknown_bits` and
  `requires_unknown_bits_from`, the even-bit scan behind `Accepts`.
* `lightning/src/ln/features.rs:24-48`: length-prefixed `InitFeatures` codec;
  the wire length is metadata and does not affect the bitwise closure laws.
* `lightning/src/ln/channel.rs:4702`: feature intersection used when
  negotiating channel types.

## What is explicitly NOT modelled

* Byte-level encoding and the big-endian/little-endian reversal.  Proofs are
  purely pointwise over `Nat -> Bool`; no `Nat.land`, `ByteArray` arithmetic,
  or codec round-trip is used.
* The concrete `KnownFeatures` table and the BOLT 9 dependency graph.
  `Accepts` is kept abstract in `known`, exactly as in FeaturesProps.
* The full BOLT 1 handshake/disconnect protocol.  The negation of required
  bits is modelled only as a Boolean vector; the transport action that
  follows a `closeConnection` verdict is outside this module.
* The distinction between global and local feature bitmaps (BOLT 1 ORs them
  before applying the receive rule).
* Channel-type feature templates and script selection; those belong to the
  Bitcoin/Protocol modules.
-/

namespace LnLean.Proofs.PhaseC2

set_option autoImplicit false

open LnLean
open LnLean.Proofs.Protocol

/-! ## Required and optional bits as propositions -/

/-- The even (required) bit of feature `n` is set.  This is the Prop-valued
form of `FeatureVector.requires`. -/
def Required (f : FeatureVector) (n : Nat) : Prop := f.requires n = true

/-- The odd (optional) bit of feature `n` is set.  This is the Prop-valued
form of `FeatureVector.offersOptional`. -/
def Optional (f : FeatureVector) (n : Nat) : Prop := f.offersOptional n = true

/-- The required-bit predicate is literally the even bit of the pair. -/
theorem required_iff_even_bit (f : FeatureVector) (n : Nat) :
    Required f n ↔ f.hasBit (requiredBit n) = true :=
  Iff.rfl

/-- Requirement implies support.  This is FeaturesProps'
`supports_of_requires` restated at the `Required` boundary. -/
theorem supports_of_required {f : FeatureVector} {n : Nat}
    (h : Required f n) : f.supports n = true :=
  FeatureVector.supports_of_requires f n h

/-! ## Intersection of accepted vectors -/

/-- **Acceptance is closed under intersection.**  If a receiver accepts both
`f` and `g` under BOLT 1's unknown-even-bit rule, then it accepts the bitwise
intersection `intersection f g`.  The intersection can only clear bits, so it
cannot introduce an unknown required bit. -/
theorem accepts_intersection (known : KnownFeatures) (f g : FeatureVector)
    (hf : Accepts known f) (hg : Accepts known g) :
    Accepts known (intersection f g) := by
  rw [accepts_iff_no_unknown_required] at hf hg ⊢
  intro n hn
  rw [intersection_requires, hf n hn, hg n hn]
  rfl

/-- **Acceptance is closed under union** (the dual law).  BOLT 1 combines the
global and local bitmaps with OR; this theorem says that combining two
accepted bitmaps this way is again accepted. -/
theorem accepts_union (known : KnownFeatures) (f g : FeatureVector)
    (hf : Accepts known f) (hg : Accepts known g) :
    Accepts known (union f g) := by
  rw [accepts_iff_no_unknown_required] at hf hg ⊢
  intro n hn
  show (f.requires n || g.requires n) = false
  rw [hf n hn, hg n hn]
  rfl

/-! ## Required bits cannot be created by intersection -/

/-- Requirement in an intersection is exactly conjunction: the even bit of
feature `n` survives iff both operands set it. -/
theorem intersection_required_iff (f g : FeatureVector) (n : Nat) :
    Required (intersection f g) n ↔ Required f n ∧ Required g n := by
  unfold Required
  rw [intersection_requires, Bool.and_eq_true_iff]

/-- The optional bit obeys the same pointwise conjunction law. -/
theorem intersection_optional_iff (f g : FeatureVector) (n : Nat) :
    Optional (intersection f g) n ↔ Optional f n ∧ Optional g n := by
  unfold Optional
  rw [intersection_offersOptional, Bool.and_eq_true_iff]

/-- **An optional feature cannot become required by intersection.**  If
neither operand sets the even bit of feature `n`, the intersection does not
set it either. -/
theorem optional_not_required_by_intersection (f g : FeatureVector) (n : Nat)
    (hf : f.requires n = false) (hg : g.requires n = false) :
    (intersection f g).requires n = false := by
  rw [intersection_requires, hf, hg]
  rfl

/-- Version stated with `Required` and `Optional`: if both peers offer feature
`n` only through the odd bit, the intersection keeps the odd bit and still
does not require the feature. -/
theorem optional_stays_optional (f g : FeatureVector) (n : Nat)
    (hfr : f.requires n = false) (hgr : g.requires n = false)
    (hfo : f.offersOptional n = true) (hgo : g.offersOptional n = true) :
    Optional (intersection f g) n ∧ ¬ Required (intersection f g) n := by
  constructor
  · exact (intersection_optional_iff f g n).2 ⟨hfo, hgo⟩
  · intro hr
    have hrr : (intersection f g).requires n = true := hr
    rw [optional_not_required_by_intersection f g n hfr hgr] at hrr
    cases hrr

/-- Pointwise corollary: if the left operand does not require `n`, no
intersection with it can require `n`. -/
theorem intersection_requires_false_of_left (f g : FeatureVector) (n : Nat)
    (h : f.requires n = false) : (intersection f g).requires n = false := by
  rw [intersection_requires, h]
  rfl

/-! ## Algebraic laws of intersection -/

/-- Bitwise intersection is idempotent. -/
theorem intersection_idempotent (f : FeatureVector) :
    intersection f f = f := by
  cases f with
  | mk bits byteLen =>
      simp [intersection, Bool.and_self]

/-- Bitwise intersection is commutative. -/
theorem intersection_commutative (f g : FeatureVector) :
    intersection f g = intersection g f := by
  cases f with
  | mk fb fl =>
      cases g with
      | mk gb gl =>
          simp only [intersection]
          have hb : (fun i => fb i && gb i) = (fun i => gb i && fb i) := by
            funext i
            exact Bool.and_comm (fb i) (gb i)
          have hl : max fl gl = max gl fl := Nat.max_comm fl gl
          rw [hb, hl]

/-- Bitwise intersection is associative. -/
theorem intersection_associative (f g h : FeatureVector) :
    intersection (intersection f g) h = intersection f (intersection g h) := by
  cases f with
  | mk fb fl =>
      cases g with
      | mk gb gl =>
          cases h with
          | mk hb hl =>
              simp [intersection, Bool.and_assoc]

/-- Intersection preserves BOLT 1's zero-padding condition. -/
theorem intersection_preserves_bounded {f g : FeatureVector} (hf : f.Bounded)
    (hg : g.Bounded) : (intersection f g).Bounded :=
  LnLean.Proofs.Protocol.intersection_bounded hf hg

/-! ## Idempotence of negotiation -/

/-- **Negotiation is idempotent.**  Negotiating a vector against itself yields
exactly its support predicate. -/
theorem negotiated_idempotent (f : FeatureVector) (n : Nat) :
    negotiated f f n = f.supports n := by
  unfold negotiated mutualSupport FeatureVector.supports
  rw [Bool.and_self, ← Bool.or_assoc, Bool.or_self]

/-- Mutual support is idempotent. -/
theorem mutualSupport_idempotent (f : FeatureVector) (n : Nat) :
    mutualSupport f f n = f.supports n := by
  unfold mutualSupport
  rw [Bool.and_self]

/-! ## Commutativity of negotiation -/

/-- A feature not supported by a vector has its required bit clear. -/
theorem req_false_of_supports_false {f : FeatureVector} {n : Nat}
    (h : f.supports n = false) : f.requires n = false := by
  cases hr : f.requires n with
  | false => rfl
  | true =>
      rw [FeatureVector.supports_of_requires f n hr] at h
      cases h

/-- **Exact commutativity condition.**  At feature `n`, BOLT 1's negotiation
rule commutes iff either both peers support `n`, or neither peer requires it.
This is the strongest pointwise form: it drops the global "each peer supports
everything the other requires" hypothesis used below. -/
theorem negotiated_comm_iff (l r : FeatureVector) (n : Nat) :
    negotiated l r n = negotiated r l n ↔
      mutualSupport l r n = true ∨
        (l.requires n = false ∧ r.requires n = false) := by
  unfold negotiated mutualSupport
  by_cases hsl : l.supports n = true
  · by_cases hsr : r.supports n = true
    · simp [hsl, hsr]
    · have hsr0 : r.supports n = false := by
        cases h : r.supports n with
        | false => rfl
        | true => exact absurd h hsr
      have hr0 : r.requires n = false := req_false_of_supports_false hsr0
      by_cases hl : l.requires n = true
      · simp [hsl, hsr, hl, hr0]
      · have hl0 : l.requires n = false := by
          cases h : l.requires n with
          | false => rfl
          | true => exact absurd h hl
        simp [hsl, hsr, hl0, hr0]
  · have hsl0 : l.supports n = false := by
      cases h : l.supports n with
      | false => rfl
      | true => exact absurd h hsl
    have hl0 : l.requires n = false := req_false_of_supports_false hsl0
    by_cases hsr : r.supports n = true
    · by_cases hr : r.requires n = true
      · simp [hsl, hsr, hl0, hr]
      · have hr0 : r.requires n = false := by
          cases h : r.requires n with
          | false => rfl
          | true => exact absurd h hr
        simp [hsl, hsr, hl0, hr0]
    · have hsr0 : r.supports n = false := by
        cases h : r.supports n with
        | false => rfl
        | true => exact absurd h hsr
      have hr0 : r.requires n = false := req_false_of_supports_false hsr0
      simp [hsl, hsr, hl0, hr0]

/-- **Conditional commutativity of BOLT 1 negotiation.**  If each peer
supports every feature the other requires (BOLT 1's "it did not disconnect"
assumption for both directions), the full negotiation rule is commutative. -/
theorem negotiated_comm_of_mutually_accepted
    (l r : FeatureVector)
    (hLR : ∀ n, l.requires n = true → r.supports n = true)
    (hRL : ∀ n, r.requires n = true → l.supports n = true) (n : Nat) :
    negotiated l r n = negotiated r l n := by
  rw [negotiated_comm_iff]
  by_cases hm : mutualSupport l r n = true
  · exact Or.inl hm
  · right
    constructor
    · cases h : l.requires n with
      | false => rfl
      | true =>
          have hs : r.supports n = true := hLR n h
          have hl : l.supports n = true :=
            FeatureVector.supports_of_requires l n h
          have : mutualSupport l r n = true := by simp [mutualSupport, hl, hs]
          exact absurd this hm
    · cases h : r.requires n with
      | false => rfl
      | true =>
          have hs : l.supports n = true := hRL n h
          have hr : r.supports n = true :=
            FeatureVector.supports_of_requires r n h
          have : mutualSupport l r n = true := by simp [mutualSupport, hs, hr]
          exact absurd this hm

/-- A vector setting only feature 0's required bit. -/
def onlyRequiredZero : FeatureVector where
  bits := fun i => i == 0
  byteLen := 1

/-- A vector with no feature bits set. -/
def noFeatures : FeatureVector where
  bits := fun _ => false
  byteLen := 1

/-- **Counterexample to unconditional commutativity.**  The local vector
requires feature 0 while the remote vector offers nothing; the asymmetric
required-bit disjunct makes the two negotiation orders disagree.  Hence the
conditional form above is necessary and cannot be dropped. -/
theorem negotiated_not_commutative_unconditional :
    negotiated onlyRequiredZero noFeatures 0 ≠
      negotiated noFeatures onlyRequiredZero 0 := by
  decide

/-! ## Support sets -/

/-- The support set of a feature vector, as a predicate on feature numbers.
This is the set-level reading of `FeatureVector.supports`. -/
def SupportSet (f : FeatureVector) : Nat → Prop :=
  fun n => f.supports n = true

/-- Intersecting the bit predicates can only shrink the support set: every
feature supported by `intersection f g` is supported by both operands.  The
reverse inclusion fails; see `bitwiseIntersection_not_negotiation` in
FeaturesProps and the note in the module docstring. -/
theorem supportSet_intersection_subset (f g : FeatureVector) {n : Nat}
    (hn : SupportSet (intersection f g) n) :
    SupportSet f n ∧ SupportSet g n :=
  supports_of_intersection_supports hn

end LnLean.Proofs.PhaseC2
