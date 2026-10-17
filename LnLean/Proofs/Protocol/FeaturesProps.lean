import LnLean.Protocol.Messages
import LnLean.Basic.Core

/-!
# LnLean.Proofs.Protocol.FeaturesProps

## English claim

This module gives the feature-bit model that `LnLean.Protocol.Messages` leaves
opaque (`InitMsg.features` is a `ByteArray`).

1. A feature `n` is represented by the adjacent pair of bits `2*n` (even,
   required) and `2*n+1` (odd, optional).  Bit numbering starts at the least
   significant bit, as BOLT 1 requires.
2. A required feature implies the corresponding optional feature *in the
   sense of support*: `supports n` is the disjunction of the even and odd
   bits.  It does **not** imply that the odd bit itself is set; BOLT 9
   forbids setting both bits of a pair.
3. The receive rule is exact at the pair level: an unknown odd bit is
   ignored, while an unknown even bit makes the connection unacceptable.
   A vector is accepted iff it sets no even bit of an unknown feature.
4. Mutual support is the intersection of the two support sets and is
   commutative.  The full BOLT 1 negotiation rule is
   `local.requires n || (local.supports n && remote.supports n)`; it is
   *not* commutative for arbitrary vectors.  It reduces to the symmetric
   intersection exactly when the peer supports every locally required
   feature (the BOLT 1 "it did not disconnect" assumption), and then it is
   commutative.
5. A `FeatureVector` that is padded (`Bounded`) has every set bit below
   `8 * byteLen`; hence a vector whose `byteLen` fits BOLT 1's `u16` length
   field has all bits below `8 * 65535`.
6. The feature gates choose the BOLT 3 `to_remote` template:
   `option_anchors` (bits 22/23) selects the keyed-anchor CSV template,
   otherwise `option_static_remotekey` (bits 12/13) selects P2WPKH, and
   otherwise the legacy template is used.

## BOLT sections

* BOLT 1 §"The `init` Message" (`refs/bolts/01-messaging.md:268-330`):
  bit numbering (`:272-274`), byte padding (`:278`), combining the global and
  local bitmaps with OR (`:318`), and the unknown odd/even receive rules
  (`:320-323`).
* BOLT 9 §"Assigned Feature Flags" (`refs/bolts/09-features.md:1-90`):
  adjacent even/odd pairs (`:11-15`), `option_static_remotekey` (`:41`),
  `option_anchors` (`:45`), the "do not set both bits" rule (`:73`), and
  transitive dependencies (`:74`).  A receiver treats both bits of a pair as
  mandatory when both are set (`:79-80`).
* BOLT 2 §"Defined Channel Types"
  (`refs/bolts/02-peer-protocol.md:786-793`): the anchor channel type is
  bits 22 **and** 12, while the static-remotekey type is bit 12.
* BOLT 3 §"`to_remote` Output"
  (`refs/bolts/03-transactions.md:136-146`): with `option_anchors` the output
  is a one-block-CSV script; otherwise it is a simple P2WPKH.

## rust-lightning anchors (commit fe49009)

* `lightning/src/ln/features.rs:24-48`: `write_be` and the length-prefixed
  `Readable`/`Writeable` implementations for `InitFeatures`; the `u16` length
  prefix (`:36`) is the wire bound used by `FeatureVector.byteLen`.
* `lightning/src/ln/features.rs:51-56`: `InitFeatures` uses the
  length-prefixed codec.
* `lightning-types/src/features.rs:286-290`: `EVEN_BIT = ODD_BIT - 1` and
  `ODD_BIT`; the adjacent-pair encoding.
* `lightning-types/src/features.rs:322-333`: `requires_feature` tests the
  even bit, while `supports_feature` tests the OR of both bits.
* `lightning-types/src/features.rs:336-356`: `set_required_bit` sets the even
  bit and clears the paired odd bit; `set_optional_bit` sets the odd bit.
* `lightning-types/src/features.rs:477-483`: `StaticRemoteKey` at odd bit 13
  (even 12); `:531-537`: `AnchorsZeroFeeHtlcTx` at odd bit 23 (even 22).
* `lightning-types/src/features.rs:1042-1071`: `requires_unknown_bits_from`
  selects unknown even bits; `:1073-1091`: `requires_unknown_bits`.
* `lightning-types/src/features.rs:1017-1035`: little-endian vs. big-endian
  byte order and `from_be_bytes`; this module uses bit indices only and does
  not re-implement that byte swap.
* `lightning/src/ln/chan_utils.rs:704-712`
  `get_countersigner_payment_script`: anchors select the keyed-anchor P2WSH
  script, otherwise P2WPKH; `:1007-1013` is the anchor redeem script.

## What is explicitly NOT modelled

* Byte-level serialization.  `FeatureVector` is a bit predicate plus a byte
  length; the BOLT 1 big-endian packing and LDK's `from_be_bytes` reversal are
  represented only through the abstract `FeatureCodec` interface below.
* The complete BOLT 9 dependency table.  `DependenciesSatisfied` is a generic
  predicate; no concrete table of dependencies is instantiated.
* Global vs. local feature bitmaps are not kept separate.  BOLT 1 combines
  them with OR before applying the receive rule, so a single vector suffices.
* Feature bits in `channel_announcement`, `node_announcement`, invoices, or
  blinded paths are not modelled; only the `init`-style pair semantics are.
* The actual BOLT 3 script bytes.  This module imports only
  `LnLean.Protocol.Messages` and `LnLean.Basic.Core` (plus Lean core), not
  `LnLean.Bitcoin.Seam`, so it selects an abstract `ScriptTemplate` tag.  The
  byte-level templates are the subject of the Bitcoin proof modules.
* The `init_tlvs` stream, `networks`, and `remote_addr` are not part of this
  model (they are already absent from `LnLean.Protocol.Messages`).
-/

namespace LnLean.Proofs.Protocol

set_option autoImplicit false

open LnLean
open LnLean.Protocol

/-! ## Adjacent even/odd feature pairs -/

/-- The even (required) bit of feature number `n`. -/
def requiredBit (n : Nat) : Nat := 2 * n

/-- The odd (optional) bit of feature number `n`. -/
def optionalBit (n : Nat) : Nat := 2 * n + 1

/-- The two bits of a feature are adjacent, with the odd bit immediately
above the even bit. -/
theorem optionalBit_adjacent (n : Nat) : optionalBit n = requiredBit n + 1 := rfl

/-- The required bit is even. -/
theorem requiredBit_even (n : Nat) : ∃ k, requiredBit n = 2 * k := ⟨n, rfl⟩

/-- The optional bit is odd. -/
theorem optionalBit_odd (n : Nat) : ∃ k, optionalBit n = 2 * k + 1 := ⟨n, rfl⟩

/-- The required bit precedes the optional bit of the same feature. -/
theorem requiredBit_lt_optionalBit (n : Nat) : requiredBit n < optionalBit n := by
  unfold requiredBit optionalBit
  omega

/-! ## Feature vectors -/

/-- A feature vector is a bit predicate together with the number of bytes it
occupies on the wire.  `bits i = true` means bit `i` is set.  The vector is
*not* required to be padded; use `Bounded` for BOLT 1's zero-padding rule. -/
structure FeatureVector where
  bits : Nat → Bool
  byteLen : Nat

namespace FeatureVector

/-- Test one raw bit. -/
def hasBit (f : FeatureVector) (i : Nat) : Bool := f.bits i

/-- The even (required) bit of feature `n` is set. -/
def requires (f : FeatureVector) (n : Nat) : Bool := f.hasBit (requiredBit n)

/-- The odd (optional) bit of feature `n` is set. -/
def offersOptional (f : FeatureVector) (n : Nat) : Bool :=
  f.hasBit (optionalBit n)

/-- `f` supports feature `n` when either bit of the pair is set.  This is the
LDK `supports_feature` test (`REQUIRED_MASK | OPTIONAL_MASK`). -/
def supports (f : FeatureVector) (n : Nat) : Bool :=
  f.requires n || f.offersOptional n

/-- A required feature implies support for that feature.  Note that this does
**not** say the odd bit is set; BOLT 9 forbids setting both bits. -/
theorem supports_of_requires (f : FeatureVector) (n : Nat)
    (h : f.requires n = true) : f.supports n = true := by
  simp [supports, h]

/-- An optional bit also implies support. -/
theorem supports_of_optional (f : FeatureVector) (n : Nat)
    (h : f.offersOptional n = true) : f.supports n = true := by
  simp [supports, h]

/-- BOLT 1's zero-padding rule: every bit at or above `8 * byteLen` is zero.
This is the model's "padded to bytes with 0s" condition. -/
def Bounded (f : FeatureVector) : Prop :=
  ∀ i, 8 * f.byteLen ≤ i → f.bits i = false

/-- A set bit of a padded vector lies inside the wire bytes. -/
theorem bounded_bit_lt {f : FeatureVector} (hf : f.Bounded) {i : Nat}
    (hi : f.hasBit i = true) : i < 8 * f.byteLen := by
  apply Nat.lt_of_not_le
  intro hle
  have hfalse : f.bits i = false := hf i hle
  rw [hasBit, hfalse] at hi
  cases hi

/-- The wire-length corollary: if the vector occupies at most 65535 bytes
(BOLT 1's `u16` length field), every set bit is below `8 * 65535`. -/
theorem bounded_bit_lt_wire {f : FeatureVector} (hf : f.Bounded)
    (hlen : f.byteLen ≤ 65535) {i : Nat} (hi : f.hasBit i = true) :
    i < 8 * 65535 := by
  have h := bounded_bit_lt hf hi
  omega

/-- A zero-length vector has no set bits at all. -/
theorem bounded_of_zero_length {f : FeatureVector} (hf : f.Bounded)
    (h0 : f.byteLen = 0) : ∀ i, f.bits i = false := by
  intro i
  exact hf i (by simp [h0])

end FeatureVector

/-! ## Unknown-bit receive rule -/

/-- Features understood by the receiver, indexed by feature number.  Features
are allocated in pairs, so knowing feature `n` means knowing both bit `2*n`
and bit `2*n+1`. -/
abbrev KnownFeatures := Nat → Bool

/-- The three outcomes of BOLT 1's unknown-bit rule. -/
inductive FeatureVerdict where
  | accept
  | ignore
  | closeConnection
deriving Repr, DecidableEq, BEq

/-- An unknown even (required) bit causes a connection close. -/
def requiredVerdict (known : KnownFeatures) (n : Nat) : FeatureVerdict :=
  if known n then .accept else .closeConnection

/-- An unknown odd (optional) bit is ignored. -/
def optionalVerdict (known : KnownFeatures) (n : Nat) : FeatureVerdict :=
  if known n then .accept else .ignore

theorem requiredVerdict_unknown (known : KnownFeatures) (n : Nat)
    (h : known n = false) : requiredVerdict known n = .closeConnection := by
  simp [requiredVerdict, h]

theorem optionalVerdict_unknown (known : KnownFeatures) (n : Nat)
    (h : known n = false) : optionalVerdict known n = .ignore := by
  simp [optionalVerdict, h]

theorem requiredVerdict_known (known : KnownFeatures) (n : Nat)
    (h : known n = true) : requiredVerdict known n = .accept := by
  simp [requiredVerdict, h]

theorem optionalVerdict_known (known : KnownFeatures) (n : Nat)
    (h : known n = true) : optionalVerdict known n = .accept := by
  simp [optionalVerdict, h]

/-- A vector is rejected when it sets the even bit of a feature the receiver
does not know.  Odd bits are deliberately absent from this predicate. -/
def UnknownRequired (known : KnownFeatures) (f : FeatureVector) : Prop :=
  ∃ n, known n = false ∧ f.requires n = true

/-- The receiver accepts a vector exactly when it has no unknown required
bits. -/
def Accepts (known : KnownFeatures) (f : FeatureVector) : Prop :=
  ¬ UnknownRequired known f

/-- **Exact rule.**  Acceptance is equivalent to every unknown feature having
its even bit clear. -/
theorem accepts_iff_no_unknown_required (known : KnownFeatures)
    (f : FeatureVector) :
    Accepts known f ↔ ∀ n, known n = false → f.requires n = false := by
  constructor
  · rintro h n hn
    cases hb : f.requires n with
    | false => rfl
    | true => exact (h ⟨n, hn, hb⟩).elim
  · rintro h ⟨n, hn, hr⟩
    have hf := h n hn
    rw [hf] at hr
    cases hr

/-- Setting an unknown even bit is rejected. -/
theorem rejects_unknown_even (known : KnownFeatures) (f : FeatureVector)
    (n : Nat) (hk : known n = false) (hr : f.requires n = true) :
    ¬ Accepts known f := by
  intro h
  exact h ⟨n, hk, hr⟩

/-- An unknown odd bit alone does not cause rejection: the rule only looks at
even bits. -/
theorem ignores_unknown_odd (known : KnownFeatures) (f : FeatureVector)
    (n : Nat) (_hk : known n = false) (_ho : f.offersOptional n = true)
    (hno : ∀ m, known m = false → f.requires m = false) :
    Accepts known f :=
  (accepts_iff_no_unknown_required known f).2 hno

/-! ## Negotiation -/

/-- Mutual support: the intersection of the two peers' support sets. -/
def mutualSupport (f g : FeatureVector) (n : Nat) : Bool :=
  f.supports n && g.supports n

/-- The symmetric intersection of supports is commutative. -/
theorem mutualSupport_comm (f g : FeatureVector) (n : Nat) :
    mutualSupport f g n = mutualSupport g f n := by
  simp [mutualSupport, Bool.and_comm]

/-- BOLT 1's negotiation rule.  The local node may rely on a feature it
requires (an even bit), because a peer that did not support it was required to
disconnect; otherwise both peers must have offered the feature. -/
def negotiated (lcl rmt : FeatureVector) (n : Nat) : Bool :=
  lcl.requires n || mutualSupport lcl rmt n

/-- Under BOLT 1's acceptance assumption, negotiation is exactly the
intersection of supports. -/
theorem negotiated_eq_mutualSupport_of_peer_supports
    (lcl rmt : FeatureVector)
    (h : ∀ n, lcl.requires n = true → rmt.supports n = true) (n : Nat) :
    negotiated lcl rmt n = mutualSupport lcl rmt n := by
  unfold negotiated mutualSupport
  by_cases hl : lcl.requires n = true
  · have hsupp : rmt.supports n = true := h n hl
    have hloc : lcl.supports n = true :=
      FeatureVector.supports_of_requires lcl n hl
    simp [hl, hsupp, hloc]
  · have hl' : lcl.requires n = false := by
      cases hb : lcl.requires n with
      | false => rfl
      | true => exact absurd hb hl
    simp [hl']

/-- **Conditional commutativity.**  When both peers accept each other's
required bits, the full BOLT 1 negotiation rule is commutative. -/
theorem negotiated_comm_of_mutually_accepted
    (lcl rmt : FeatureVector)
    (hLR : ∀ n, lcl.requires n = true → rmt.supports n = true)
    (hRL : ∀ n, rmt.requires n = true → lcl.supports n = true)
    (n : Nat) :
    negotiated lcl rmt n = negotiated rmt lcl n := by
  rw [negotiated_eq_mutualSupport_of_peer_supports lcl rmt hLR n,
      negotiated_eq_mutualSupport_of_peer_supports rmt lcl hRL n,
      mutualSupport_comm]

/-- A vector with only feature 0's required bit set. -/
def localRequiredOnly : FeatureVector where
  bits := fun i => i == 0
  byteLen := 1

/-- A vector with no bits set. -/
def emptyVector : FeatureVector where
  bits := fun _ => false
  byteLen := 1

/-- **The unconditional rule is not commutative.**  This is the corrected
form of the mission's "negotiation is commutative" claim: local requirement
is an asymmetric disjunct, so the full rule must be restricted as in
`negotiated_comm_of_mutually_accepted`. -/
theorem negotiated_not_commutative :
    negotiated localRequiredOnly emptyVector 0 ≠
      negotiated emptyVector localRequiredOnly 0 := by
  decide

/-! ## Intersection of feature vectors -/

/-- Bitwise AND of two feature vectors, with the larger wire length. -/
def intersection (f g : FeatureVector) : FeatureVector where
  bits := fun i => f.bits i && g.bits i
  byteLen := max f.byteLen g.byteLen

theorem intersection_requires (f g : FeatureVector) (n : Nat) :
    (intersection f g).requires n = (f.requires n && g.requires n) := rfl

theorem intersection_offersOptional (f g : FeatureVector) (n : Nat) :
    (intersection f g).offersOptional n =
      (f.offersOptional n && g.offersOptional n) := rfl

/-- Bitwise intersection is commutative. -/
theorem intersection_comm (f g : FeatureVector) :
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

/-- One direction that does hold: if the bitwise intersection supports a
feature then both operands support it. -/
theorem supports_of_intersection_supports {f g : FeatureVector} {n : Nat}
    (h : (intersection f g).supports n = true) :
    f.supports n = true ∧ g.supports n = true := by
  rw [FeatureVector.supports, intersection_requires, intersection_offersOptional] at h
  by_cases hfr : f.requires n = true <;>
    by_cases hgr : g.requires n = true <;>
    by_cases hfo : f.offersOptional n = true <;>
    by_cases hgo : g.offersOptional n = true <;>
    simp_all [FeatureVector.supports]

/-- Hence bitwise intersection implies mutual support. -/
theorem mutualSupport_of_intersection_supports {f g : FeatureVector} {n : Nat}
    (h : (intersection f g).supports n = true) : mutualSupport f g n = true := by
  rcases supports_of_intersection_supports h with ⟨hf, hg⟩
  simp [mutualSupport, hf, hg]

/-- A vector supporting feature 0 only through its odd bit. -/
def oddOnlyZero : FeatureVector where
  bits := fun i => i == 1
  byteLen := 1

/-- A vector supporting feature 0 only through its even bit. -/
def evenOnlyZero : FeatureVector where
  bits := fun i => i == 0
  byteLen := 1

/-- **Corrected claim.**  Bitwise AND of the vectors is not the same as
intersection of the support sets: one peer can offer feature 0 only as
optional while the other requires it, so both support it but the bitwise AND
contains neither bit.  Negotiation is therefore `mutualSupport`, not the raw
`intersection`. -/
theorem bitwiseIntersection_not_negotiation :
    (intersection oddOnlyZero evenOnlyZero).supports 0 ≠
      mutualSupport oddOnlyZero evenOnlyZero 0 := by
  decide

/-- The intersection of two padded vectors is padded. -/
theorem intersection_bounded {f g : FeatureVector} (hf : f.Bounded)
    (hg : g.Bounded) : (intersection f g).Bounded := by
  intro i hi
  have hfl : f.byteLen ≤ max f.byteLen g.byteLen := Nat.le_max_left _ _
  have hgl : g.byteLen ≤ max f.byteLen g.byteLen := Nat.le_max_right _ _
  have hfi : 8 * f.byteLen ≤ i :=
    Nat.le_trans (Nat.mul_le_mul_left 8 hfl) hi
  have hgi : 8 * g.byteLen ≤ i :=
    Nat.le_trans (Nat.mul_le_mul_left 8 hgl) hi
  have hfb : f.bits i = false := hf i hfi
  have hgb : g.bits i = false := hg i hgi
  show (f.bits i && g.bits i) = false
  rw [hfb, hgb]
  rfl

/-- Bitwise OR of two feature vectors, matching BOLT 1's combination of the
global and local feature bitmaps. -/
def union (f g : FeatureVector) : FeatureVector where
  bits := fun i => f.bits i || g.bits i
  byteLen := max f.byteLen g.byteLen

/-- Combining the two feature bitmaps is commutative. -/
theorem union_comm (f g : FeatureVector) : union f g = union g f := by
  cases f with
  | mk fb fl =>
  cases g with
  | mk gb gl =>
  simp only [union]
  have hb : (fun i => fb i || gb i) = (fun i => gb i || fb i) := by
    funext i
    exact Bool.or_comm (fb i) (gb i)
  have hl : max fl gl = max gl fl := Nat.max_comm fl gl
  rw [hb, hl]

/-- BOLT 9's transitive-dependency condition for a dependency table `deps`:
whenever feature `n` is supported, every feature in `deps n` is supported.
The concrete table is not instantiated in this module. -/
def DependenciesSatisfied (deps : Nat → List Nat) (f : FeatureVector) : Prop :=
  ∀ n m, m ∈ deps n → f.supports n = true → f.supports m = true

/-- **Corrected claim.**  It is *negotiated support* (`mutualSupport`), not
the raw bitwise `intersection`, that preserves BOLT 9's transitive
dependencies: two peers can support the same feature through different bits of
the pair, so the bitwise AND may lose a dependency even when both support it. -/
theorem dependencies_preserved_by_negotiation
    (deps : Nat → List Nat) (f g : FeatureVector)
    (hf : DependenciesSatisfied deps f) (hg : DependenciesSatisfied deps g) :
    ∀ n m, m ∈ deps n → mutualSupport f g n = true →
      mutualSupport f g m = true := by
  intro n m hmem hn
  rw [mutualSupport] at hn
  rw [Bool.and_eq_true] at hn
  rcases hn with ⟨hfn, hgn⟩
  rw [mutualSupport, Bool.and_eq_true]
  exact ⟨hf n m hmem hfn, hg n m hmem hgn⟩

/-- Intersecting accepted vectors keeps the result accepted. -/
theorem accepts_intersection_of_accepts
    (known : KnownFeatures) (f g : FeatureVector)
    (hf : Accepts known f) (hg : Accepts known g) :
    Accepts known (intersection f g) := by
  -- LN-FEAT-012: the required bit of the intersection is the conjunction of
  -- the two inputs' required bits, so it cannot be set unless both inputs set
  -- it.  Hence an unknown feature stays unrequired in the intersection.
  rw [accepts_iff_no_unknown_required] at hf hg ⊢
  intro n hn
  rw [intersection_requires, hf n hn, hg n hn]
  rfl

/-! ## Abstract wire codec -/

/-- A byte-level feature codec.  This is the seam at which a future module
connects BOLT 1's big-endian byte packing to `FeatureVector`; the concrete
codec is deliberately not implemented here. -/
structure FeatureCodec where
  decode : ByteArray → FeatureVector
  encode : FeatureVector → ByteArray
  byteLen_eq : ∀ b, (decode b).byteLen = b.size
  decode_bounded : ∀ b, (decode b).Bounded

/-- For any codec, a decoded vector is bounded by the actual wire length. -/
theorem decoded_bit_lt_wire (c : FeatureCodec) (b : ByteArray) {i : Nat}
    (hi : (c.decode b).hasBit i = true) : i < 8 * b.size := by
  have h := FeatureVector.bounded_bit_lt (c.decode_bounded b) hi
  rw [c.byteLen_eq b] at h
  exact h

/-- No decoded bit lies at or above the wire length. -/
theorem decoded_no_high_bits (c : FeatureCodec) (b : ByteArray) {i : Nat}
    (hi : 8 * b.size ≤ i) : (c.decode b).bits i = false := by
  have hb := c.decode_bounded b
  unfold FeatureVector.Bounded at hb
  rw [c.byteLen_eq b] at hb
  exact hb i hi

/-! ## Script-template gating -/

/-- The `to_remote` script family selected by the negotiated feature vector.
The byte-level scripts are proved about in the Bitcoin modules; here we model
only the BOLT 3 branch selection. -/
inductive ScriptTemplate where
  | legacyToRemote
  | staticRemoteKeyToRemote
  | anchoredToRemote
deriving Repr, DecidableEq, BEq

/-- Feature number of `option_static_remotekey`: even bit 12, odd bit 13. -/
def staticRemoteKeyFeature : Nat := 6

/-- Feature number of `option_anchors`: even bit 22, odd bit 23. -/
def anchorsFeature : Nat := 11

theorem staticRemoteKey_bits :
    requiredBit staticRemoteKeyFeature = 12 ∧
      optionalBit staticRemoteKeyFeature = 13 :=
  ⟨rfl, rfl⟩

theorem anchors_bits :
    requiredBit anchorsFeature = 22 ∧ optionalBit anchorsFeature = 23 :=
  ⟨rfl, rfl⟩

/-- BOLT 3's `to_remote` template gate: anchors take precedence, then
`option_static_remotekey`, otherwise the legacy template. -/
def commitmentTemplate (f : FeatureVector) : ScriptTemplate :=
  if f.supports anchorsFeature then .anchoredToRemote
  else if f.supports staticRemoteKeyFeature then .staticRemoteKeyToRemote
  else .legacyToRemote

/-- Supporting `option_anchors` selects the anchored template. -/
theorem template_anchors_of_supports (f : FeatureVector)
    (h : f.supports anchorsFeature = true) :
    commitmentTemplate f = .anchoredToRemote := by
  simp [commitmentTemplate, h]

/-- Without anchors, supporting `option_static_remotekey` selects the P2WPKH
template. -/
theorem template_static_of_no_anchors (f : FeatureVector)
    (ha : f.supports anchorsFeature = false)
    (hs : f.supports staticRemoteKeyFeature = true) :
    commitmentTemplate f = .staticRemoteKeyToRemote := by
  simp [commitmentTemplate, ha, hs]

/-- With neither feature the legacy template is selected. -/
theorem template_legacy_of_no_features (f : FeatureVector)
    (ha : f.supports anchorsFeature = false)
    (hs : f.supports staticRemoteKeyFeature = false) :
    commitmentTemplate f = .legacyToRemote := by
  simp [commitmentTemplate, ha, hs]

/-- The anchored template is selected exactly when anchors are supported. -/
theorem template_eq_anchors_iff (f : FeatureVector) :
    commitmentTemplate f = .anchoredToRemote ↔
      f.supports anchorsFeature = true := by
  by_cases ha : f.supports anchorsFeature = true
  · simp [commitmentTemplate, ha]
  · have ha' : f.supports anchorsFeature = false := by
      cases hb : f.supports anchorsFeature with
      | false => rfl
      | true => exact absurd hb ha
    by_cases hs : f.supports staticRemoteKeyFeature = true <;>
      simp [commitmentTemplate, ha', hs]

/-- Static-remotekey support prevents the legacy template, whether or not
anchors are also supported. -/
theorem template_ne_legacy_of_static (f : FeatureVector)
    (hs : f.supports staticRemoteKeyFeature = true) :
    commitmentTemplate f ≠ .legacyToRemote := by
  by_cases ha : f.supports anchorsFeature = true
  · simp [commitmentTemplate, ha]
  · have ha' : f.supports anchorsFeature = false := by
      cases hb : f.supports anchorsFeature with
      | false => rfl
      | true => exact absurd hb ha
    simp [commitmentTemplate, ha', hs]

/-- A channel type containing anchors also contains static remotekey (BOLT 2
lists the anchor type as bits 22 **and** 12).  This is a predicate on channel
types; it is deliberately *not* asserted for a bare `init` vector. -/
def ChannelTypeAnchorsImplyStatic (f : FeatureVector) : Prop :=
  f.supports anchorsFeature = true → f.supports staticRemoteKeyFeature = true

theorem channelType_anchors_implies_static (f : FeatureVector)
    (h : ChannelTypeAnchorsImplyStatic f)
    (ha : f.supports anchorsFeature = true) :
    f.supports staticRemoteKeyFeature = true :=
  h ha

/-! ## Setting feature bits -/

/-- Set feature `n` as required, clearing its optional bit, following LDK's
`set_required_bit`. -/
def setRequired (f : FeatureVector) (n : Nat) : FeatureVector where
  bits := fun i =>
    if i = requiredBit n then true
    else if i = optionalBit n then false
    else f.bits i
  byteLen := f.byteLen

theorem setRequired_requires (f : FeatureVector) (n : Nat) :
    (setRequired f n).requires n = true := by
  simp [setRequired, FeatureVector.requires, FeatureVector.hasBit]

theorem setRequired_clears_optional (f : FeatureVector) (n : Nat) :
    (setRequired f n).offersOptional n = false := by
  have hne : optionalBit n ≠ requiredBit n := by
    unfold requiredBit optionalBit
    omega
  simp [setRequired, FeatureVector.offersOptional, FeatureVector.hasBit, hne]

theorem setRequired_supports (f : FeatureVector) (n : Nat) :
    (setRequired f n).supports n = true := by
  simp [FeatureVector.supports, setRequired_requires f n]

/-! ## Wire length of the `init` feature field -/

/-- The `init` payload length as computed by the wave-A message model. -/
theorem init_msgLength_eq (m : InitMsg) :
    msgLength (.init m) = 4 + m.globalfeatures.size + m.features.size := rfl

/-- If the two feature bitmaps fit BOLT 1's framing bound, the `init` message
is well formed with respect to length.  The remaining `wellFormed`
conjuncts (ids, signatures, semantics) are trivial for `init`. -/
theorem init_msgLength_le_65535 (m : InitMsg)
    (h : m.globalfeatures.size + m.features.size ≤ 65531) :
    msgLength (.init m) ≤ 65535 := by
  rw [init_msgLength_eq]
  omega

end LnLean.Proofs.Protocol
