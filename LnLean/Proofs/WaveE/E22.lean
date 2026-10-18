import LnLean.Protocol.Handshake
import LnLean.Protocol.Laws
import LnLean.Protocol.Messages
import LnLean.Protocol.Peer
import LnLean.Proofs.Protocol.FeaturesProps

/-!
# LnLean.Proofs.WaveE.E22

## English claim

Negotiated channel features are the intersection of both peers' supported
features (catalog `LN-PR-006`; BOLT 9 §Features, BOLT 2 §Defined Channel Types;
LDK `lightning/src/ln/channel.rs:4702`).

## Model

`LnLean.Protocol.Handshake` deliberately leaves feature negotiation out: the
module docstring says "`init` carries opaque feature bytes".  The feature-bit
model is `LnLean.Proofs.Protocol.FeatureVector`, where feature `n` occupies the
adjacent even bit `2*n` (required) and odd bit `2*n+1` (optional), and
`supports n` is the disjunction of the two bits.

This module re-derives the negotiation claim on top of that model.

* A peer's *supported set* is `supportSet f = {n | f.supports n}`.
* `featureIntersection lcl rmt n` is membership in the intersection of the two
  supported sets.
* BOLT 1's actual negotiation rule is
  `negotiated lcl rmt n = lcl.requires n || (lcl.supports n && rmt.supports n)`.
  The first disjunct is asymmetric: a locally *required* feature is used even
  if the peer did not advertise it, because a peer that cannot support a
  required feature must have disconnected.  Hence the claim is true exactly
  under the BOLT 1 survival hypothesis that the peer supports every locally
  required feature (`waveE_e22_negotiated_iff_both_support`).
* Without that hypothesis the unconditional claim is false; a required-only
  local vector negotiates a feature against an empty peer vector
  (`waveE_e22_unconditional_claim_false`).
* The intersection must be taken at the level of *supported features*, not as
  a bitwise AND of the raw bit vectors: one peer may require feature `n` while
  the other offers it optionally, so both support it while the bitwise AND
  contains neither bit (`waveE_e22_bitwise_and_not_support_intersection`).

## BOLT sections

* BOLT 9 §Features: adjacent even/odd pairs, required-vs-optional semantics,
  the "do not set both bits of a pair" rule, and transitive dependencies.
* BOLT 2 §Defined Channel Types: a channel type is a feature set that both
  peers must support.  `waveE_e22_channel_type_subset_intersection` records
  that a channel type selected under negotiation lies inside the intersection.
* BOLT 1 §"The `init` Message": the local/global bitmaps are combined with OR
  and the unknown-even-bit receive rule decides whether the connection stays
  up; that rule is what supplies the survival hypothesis used below.

## rust-lightning anchor

* `lightning/src/ln/channel.rs:4702` is the catalog's anchor for channel
  feature/type negotiation.  The scaffolding has no channel-type field, so the
  theorem below is stated over the `init` feature vectors exposed by
  `FeaturesProps` rather than over an LDK `ChannelTypeFeatures` value.

## What is NOT modelled

* No byte-level codec: only `FeatureVector`'s bit predicate is used; the
  abstract `FeatureCodec` seam of `FeaturesProps` is available but not needed
  for the intersection law.
* No channel-type TLV and no concrete BOLT 9 dependency table.  The channel
  type theorem is a subset law with the selection predicate as a hypothesis.
* The negotiated set is represented as a `Nat → Bool` support predicate, not
  as a re-serialised feature vector.  There is no canonical negotiated wire
  vector when the two peers support a feature through different bits.
-/

namespace LnLean.Proofs.WaveE.E22

set_option autoImplicit false

open LnLean
open LnLean.Protocol
open LnLean.Proofs.Protocol

-- OBLIGATION: LN-WE-E22

/-! ## The intersection of the two supported-feature sets -/

/-- Membership in the intersection of the peers' supported feature sets:
feature `n` is supported by the local vector `lcl` and by the remote vector
`rmt`.  This is the "negotiated channel features" predicate of the claim. -/
def featureIntersection (lcl rmt : FeatureVector) (n : Nat) : Bool :=
  lcl.supports n && rmt.supports n

/-- The intersection is exactly `FeaturesProps.mutualSupport`; keeping the
name `featureIntersection` makes the catalog claim explicit. -/
theorem waveE_e22_featureIntersection_eq_mutualSupport
    (lcl rmt : FeatureVector) :
    featureIntersection lcl rmt = mutualSupport lcl rmt := rfl

/-- Membership characterisation: a feature is in the intersection iff both
peers support it. -/
theorem waveE_e22_featureIntersection_iff
    (lcl rmt : FeatureVector) (n : Nat) :
    featureIntersection lcl rmt n = true ↔
      lcl.supports n = true ∧ rmt.supports n = true := by
  unfold featureIntersection
  rw [Bool.and_eq_true]

/-- The intersection does not depend on which peer is named first. -/
theorem waveE_e22_featureIntersection_comm
    (lcl rmt : FeatureVector) :
    featureIntersection lcl rmt = featureIntersection rmt lcl := by
  funext n
  unfold featureIntersection
  rw [Bool.and_comm]

/-- Every feature in the intersection is supported locally. -/
theorem waveE_e22_supports_left_of_featureIntersection
    {lcl rmt : FeatureVector} {n : Nat}
    (h : featureIntersection lcl rmt n = true) : lcl.supports n = true :=
  ((waveE_e22_featureIntersection_iff lcl rmt n).1 h).1

/-- Every feature in the intersection is supported remotely. -/
theorem waveE_e22_supports_right_of_featureIntersection
    {lcl rmt : FeatureVector} {n : Nat}
    (h : featureIntersection lcl rmt n = true) : rmt.supports n = true :=
  ((waveE_e22_featureIntersection_iff lcl rmt n).1 h).2

/-- Anything in the intersection is already negotiated, with no survival
hypothesis: the local side may rely on the intersection through its second
disjunct. -/
theorem waveE_e22_negotiated_of_featureIntersection
    (lcl rmt : FeatureVector) (n : Nat)
    (h : featureIntersection lcl rmt n = true) :
    negotiated lcl rmt n = true := by
  rcases (waveE_e22_featureIntersection_iff lcl rmt n).1 h with ⟨hl, hr⟩
  unfold negotiated mutualSupport
  simp [hl, hr]

/-! ## The negotiated set under the BOLT 1 survival hypothesis -/

/-- **Main theorem.**  If the peer supports every feature the local node
requires — the BOLT 1 outcome when the peer did not disconnect — then the
locally negotiated rule is exactly the intersection of the two supported sets.

The hypothesis `hAccept` is the only added assumption.  It is exactly the
contrapositive of BOLT 1's unknown-even-bit rule: an even (required) bit the
peer cannot support forces the peer to close the connection, so on a surviving
connection every locally required feature is supported remotely. -/
theorem waveE_e22_negotiated_eq_featureIntersection
    (lcl rmt : FeatureVector)
    (hAccept : ∀ n, lcl.requires n = true → rmt.supports n = true)
    (n : Nat) :
    negotiated lcl rmt n = featureIntersection lcl rmt n := by
  unfold negotiated mutualSupport featureIntersection
  by_cases hl : lcl.requires n = true
  · have hrs : rmt.supports n = true := hAccept n hl
    have hls : lcl.supports n = true :=
      FeatureVector.supports_of_requires lcl n hl
    simp [hl, hrs, hls]
  · have hl' : lcl.requires n = false := by
      cases hb : lcl.requires n with
      | false => rfl
      | true => exact absurd hb hl
    simp [hl', FeatureVector.supports]

/-- Pointwise form of the main theorem: negotiation succeeds iff both peers
support the feature. -/
theorem waveE_e22_negotiated_iff_both_support
    (lcl rmt : FeatureVector)
    (hAccept : ∀ n, lcl.requires n = true → rmt.supports n = true)
    (n : Nat) :
    negotiated lcl rmt n = true ↔
      lcl.supports n = true ∧ rmt.supports n = true := by
  rw [waveE_e22_negotiated_eq_featureIntersection lcl rmt hAccept n]
  exact waveE_e22_featureIntersection_iff lcl rmt n

/-- The set of negotiated feature numbers, as a predicate (the scaffold has no
`Set` import; a set is represented extensionally as `Nat → Prop`). -/
def negotiatedSet (lcl rmt : FeatureVector) : Nat → Prop :=
  fun n => negotiated lcl rmt n = true

/-- The set of feature numbers a peer supports, as a predicate. -/
def supportSet (f : FeatureVector) : Nat → Prop :=
  fun n => f.supports n = true

/-- **Set-level statement of the claim.**  Under the survival hypothesis, the
negotiated feature set is literally the intersection of the two peers'
supported-feature sets. -/
theorem waveE_e22_negotiatedSet_eq_inter
    (lcl rmt : FeatureVector)
    (hAccept : ∀ n, lcl.requires n = true → rmt.supports n = true) :
    negotiatedSet lcl rmt = fun n => supportSet lcl n ∧ supportSet rmt n := by
  funext n
  exact propext (waveE_e22_negotiated_iff_both_support lcl rmt hAccept n)

/-- Membership form of the set equality: a feature number is negotiated iff it
belongs to both supported sets. -/
theorem waveE_e22_negotiatedSet_iff_inter
    (lcl rmt : FeatureVector)
    (hAccept : ∀ n, lcl.requires n = true → rmt.supports n = true)
    (n : Nat) :
    negotiatedSet lcl rmt n ↔ supportSet lcl n ∧ supportSet rmt n :=
  waveE_e22_negotiated_iff_both_support lcl rmt hAccept n

/-- Both peers reach the same negotiated set when each accepts the other's
required bits; so "the" negotiated set is well defined. -/
theorem waveE_e22_negotiated_symmetric
    (lcl rmt : FeatureVector)
    (hLR : ∀ n, lcl.requires n = true → rmt.supports n = true)
    (hRL : ∀ n, rmt.requires n = true → lcl.supports n = true)
    (n : Nat) :
    negotiated lcl rmt n = negotiated rmt lcl n := by
  rw [waveE_e22_negotiated_eq_featureIntersection lcl rmt hLR n,
      waveE_e22_negotiated_eq_featureIntersection rmt lcl hRL n]
  unfold featureIntersection
  rw [Bool.and_comm]

/-! ## Consequence for BOLT 2 channel types -/

/-- **Channel-type subset law.**  A channel type selected under negotiation —
i.e. one whose supported features are all negotiated — is supported by both
peers.  This is the BOLT 2 §Defined Channel Types requirement expressed over
the model's feature vectors.  The concrete channel-type TLV is not modelled;
`hct` is the selection predicate. -/
theorem waveE_e22_channel_type_subset_intersection
    (lcl rmt ct : FeatureVector)
    (hAccept : ∀ n, lcl.requires n = true → rmt.supports n = true)
    (hct : ∀ n, ct.supports n = true → negotiated lcl rmt n = true) :
    ∀ n, ct.supports n = true → featureIntersection lcl rmt n = true := by
  intro n hn
  rw [← waveE_e22_negotiated_eq_featureIntersection lcl rmt hAccept n]
  exact hct n hn

/-! ## The unconditional claim is false -/

/-- **Negative result.**  Without the survival hypothesis the claim fails: a
peer that requires feature 0 but has not yet heard from an empty peer still
negotiates feature 0, while the intersection is empty.  This is the symmetric
counterexample to the unconditional reading of `LN-PR-006`. -/
theorem waveE_e22_unconditional_claim_false :
    negotiated localRequiredOnly emptyVector 0 = true ∧
      featureIntersection localRequiredOnly emptyVector 0 = false := by
  decide

/-- **Why "intersection" means supported features, not bitwise AND.**  One
peer can require feature 0 (even bit set) while the other offers it optionally
(odd bit set).  Both support it, so it is negotiated, but the bitwise AND of
the raw vectors sets neither bit.  A bitwise-AND reading of the claim would be
wrong even under mutual acceptance. -/
theorem waveE_e22_bitwise_and_not_support_intersection :
    (intersection oddOnlyZero evenOnlyZero).supports 0 ≠
      featureIntersection oddOnlyZero evenOnlyZero 0 := by
  decide

end LnLean.Proofs.WaveE.E22
