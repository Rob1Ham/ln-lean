import LnLean.Routing.Gossip
import LnLean.Routing.Graph
import LnLean.Routing.Laws
import LnLean.Routing.Onion
import LnLean.Routing.Route

/-!
# LnLean.Proofs.WaveD.D25

**An onion layer with an invalid HMAC is rejected rather than forwarded.**

Catalog obligation `LN-RT-004`, BOLT 4 "Packet Structure", with the LDK
anchor `lightning/src/ln/onion_payment.rs:505` (`peel_payment_onion`).

The model in `LnLean.Routing.Onion` exposes two different ways to inspect the
outermost layer:

* `peel` is the *total structural* peel: it never consults an HMAC and always
  returns `some` (`peel_isSome`).  It is the bookkeeping step, not the
  acceptance decision.
* `openLayer` is the *checked* peel used before forwarding: it consults the
  abstract verifier `I.verifyHmac tag l.hmac` and returns `none` unless the
  verifier accepts the head layer.

The obligation is a statement about the checked step.  This module proves,
unconditionally in the model:

* `waveD_d25_hmac_sound` — a successful `openLayer` (i.e. a forward) entails
  that some layer of the packet carried the expected hop and that the
  verifier accepted its HMAC.  This is the mechanical half of
  `LnLean.Routing.Onion.hmac_sound`.
* `waveD_d25_invalid_hmac_rejected` — if the head layer's HMAC is rejected by
  the verifier, `openLayer` returns `none`.
* `waveD_d25_no_forward_of_invalid` — under the same hypothesis there is no
  `hop`/`next` for which `openLayer` returns `some`, so the invalid layer is
  not forwarded by the checked path.
* `waveD_d25_openLayer_forward_iff_accepted` — for a non-empty packet, the
  checked path produces a forward result exactly when the verifier accepts
  the head layer.
* `waveD_d25_wrong_tag_rejected` — a conditional form of "invalid HMAC":
  if a layer carries a tag different from the expected tag and the verifier
  rejects wrong tags, the layer is rejected.  The verifier-rejects-wrong-tags
  premise is exactly the shape of the C8 (`hmacBinding`) cryptographic
  assumption and is **not** proved here.

The negative companion `waveD_d25_peel_bypasses_hmac` is a mechanized
counterexample to the stronger reading "every peel rejects an invalid HMAC":
`peel` on a one-layer packet with an always-rejecting verifier still returns
a forward payload.  The rejection guarantee therefore belongs to
`openLayer`; an implementation that forwards from `peel` without calling
`openLayer` does not get it.

What is **not** modelled or proved: HMAC unforgeability (C8).  The model has
no predicate separating an "authentic" HMAC from a merely verifier-accepted
one, so the cryptographic implication "a forged tag is invalid, hence the
verifier returns `false`" is represented only by the explicit hypothesis of
`waveD_d25_wrong_tag_rejected`.
-/

namespace LnLean.Proofs.WaveD.D25

open LnLean.Routing

set_option autoImplicit false

-- OBLIGATION: LN-WD-D25

/-! ## The rejection predicate -/

/-- The verifier rejects `tag` for the layer `l`.  In the model this is the
only available notion of an "invalid HMAC": `verifyHmac` is an opaque
`ByteArray → ByteArray → Bool` and validity is not a separate field. -/
def MacInvalid (I : OnionInterface) (tag : ByteArray) (l : OnionLayer) : Prop :=
  I.verifyHmac tag l.hmac = false

/-- The verifier accepts `tag` for the layer `l`. -/
def MacAccepted (I : OnionInterface) (tag : ByteArray) (l : OnionLayer) : Prop :=
  I.verifyHmac tag l.hmac = true

theorem waveD_d25_macInvalid_iff_not_accepted (I : OnionInterface)
    (tag : ByteArray) (l : OnionLayer) :
    MacInvalid I tag l ↔ ¬ MacAccepted I tag l := by
  unfold MacInvalid MacAccepted
  constructor
  · intro h ha
    rw [h] at ha
    exact Bool.noConfusion ha
  · intro h
    cases hv : I.verifyHmac tag l.hmac with
    | false => rfl
    | true => exact absurd hv h

/-! ## Soundness of the checked peel -/

/-- **Mechanical half of `LnLean.Routing.Onion.hmac_sound`.**  A successful
`openLayer` — the only path in the model that yields a hop to forward —
entails that some layer of the packet carried that hop, that removing it
leaves the packet's tail, and that the verifier accepted the layer's HMAC. -/
theorem waveD_d25_hmac_sound {I : OnionInterface} {tag : ByteArray}
    {p : OnionPacket} {hop : OnionHop} {next : OnionPacket}
    (h : openLayer I tag p = some (hop, next)) :
    ∃ l ∈ p.layers, l.hop = hop ∧ next.layers = p.layers.tail ∧
      I.verifyHmac tag l.hmac = true := by
  obtain ⟨l, hmem, hhop, hver⟩ := openLayer_verified h
  exact ⟨l, hmem, hhop, openLayer_next_layers h, hver⟩

/-- **Invalid HMAC is rejected.**  If the head layer's HMAC does not pass the
verifier, `openLayer` returns `none`; the inner packet is not exposed. -/
theorem waveD_d25_invalid_hmac_rejected {I : OnionInterface} {tag : ByteArray}
    {p : OnionPacket} {l : OnionLayer} {ls : List OnionLayer}
    (hp : p.layers = l :: ls) (hinv : MacInvalid I tag l) :
    openLayer I tag p = none :=
  openLayer_reject hp hinv

/-- **An invalid head layer is not forwarded.**  Under the rejection
hypothesis there is no hop/next pair returned by `openLayer`, so no forward
instruction can be derived from the checked path. -/
theorem waveD_d25_no_forward_of_invalid {I : OnionInterface} {tag : ByteArray}
    {p : OnionPacket} {l : OnionLayer} {ls : List OnionLayer}
    (hp : p.layers = l :: ls) (hinv : MacInvalid I tag l) :
    ¬ ∃ hop next, openLayer I tag p = some (hop, next) := by
  rintro ⟨hop, next, h⟩
  have hnone := openLayer_reject hp hinv
  rw [hnone] at h
  simp at h

/-- **Forwarding is exactly HMAC acceptance.**  For a non-empty packet the
checked peel produces a forward result if and only if the verifier accepts
the head layer.  This is the sharp form of "rejected rather than
forwarded": rejection and forwarding are complementary outcomes of the same
test. -/
theorem waveD_d25_openLayer_forward_iff_accepted {I : OnionInterface}
    {tag : ByteArray} (version : Nat) (ephemeralKey : PubKey)
    (routingInfo : ByteArray) (l : OnionLayer) (ls : List OnionLayer)
    (hmac : ByteArray) :
    (∃ hop next,
        openLayer I tag ⟨version, ephemeralKey, routingInfo, l :: ls, hmac⟩ =
          some (hop, next)) ↔
      I.verifyHmac tag l.hmac = true := by
  by_cases hacc : I.verifyHmac tag l.hmac = true
  · constructor
    · intro _
      exact hacc
    · intro _
      exact ⟨l.hop, ⟨version, ephemeralKey, routingInfo, ls, hmac⟩, by
        simp [openLayer, hacc]⟩
  · have hfalse : I.verifyHmac tag l.hmac = false := by
      cases hv : I.verifyHmac tag l.hmac with
      | false => rfl
      | true => exact absurd hv hacc
    constructor
    · rintro ⟨hop, next, h⟩
      simp [openLayer, hfalse] at h
    · intro h
      exact absurd h hacc

/-- If the verifier accepts the head layer, the checked peel returns exactly
that head hop and the packet with the head removed. -/
theorem waveD_d25_openLayer_accepted {I : OnionInterface} {tag : ByteArray}
    (version : Nat) (ephemeralKey : PubKey) (routingInfo : ByteArray)
    (l : OnionLayer) (ls : List OnionLayer) (hmac : ByteArray)
    (hacc : I.verifyHmac tag l.hmac = true) :
    openLayer I tag ⟨version, ephemeralKey, routingInfo, l :: ls, hmac⟩ =
      some (l.hop, ⟨version, ephemeralKey, routingInfo, ls, hmac⟩) := by
  simp [openLayer, hacc]

/-! ## Conditional cryptographic form: wrong tag rejected -/

/-- The verifier rejects every layer tag that differs from the expected tag.
This is the concrete verifier-binding shape of the C8 (`hmacBinding`)
assumption: a correct HMAC verifier accepts only the authentic tag.  It is a
hypothesis, not a theorem of the model. -/
def VerifierRejectsWrongTag (I : OnionInterface) (tag : ByteArray)
    (layers : List OnionLayer) : Prop :=
  ∀ l, l ∈ layers → l.hmac ≠ tag → I.verifyHmac tag l.hmac = false

/-- **Conditional form of "invalid HMAC is rejected".**  If the head layer
carries a tag different from the expected tag and the verifier rejects wrong
tags, the layer is rejected.  The `hbind` hypothesis is the unproved
cryptographic content; the model supplies only its use. -/
theorem waveD_d25_wrong_tag_rejected {I : OnionInterface} {tag : ByteArray}
    {p : OnionPacket} {l : OnionLayer} {ls : List OnionLayer}
    (hp : p.layers = l :: ls) (hwrong : l.hmac ≠ tag)
    (hbind : VerifierRejectsWrongTag I tag p.layers) :
    openLayer I tag p = none := by
  apply openLayer_reject hp
  exact hbind l (by simp [hp]) hwrong

/-- Contrapositive of `waveD_d25_wrong_tag_rejected`: under a verifier that
rejects wrong tags, an accepted layer carries exactly the expected tag. -/
theorem waveD_d25_accepted_tag_eq {I : OnionInterface} {tag : ByteArray}
    {p : OnionPacket} {hop : OnionHop} {next : OnionPacket}
    (hbind : VerifierRejectsWrongTag I tag p.layers)
    (h : openLayer I tag p = some (hop, next)) :
    ∃ l ∈ p.layers, l.hop = hop ∧ l.hmac = tag ∧
      I.verifyHmac tag l.hmac = true := by
  obtain ⟨l, hmem, hhop, _, hver⟩ := waveD_d25_hmac_sound h
  refine ⟨l, hmem, hhop, ?_, hver⟩
  by_cases htag : l.hmac = tag
  · exact htag
  · have hfalse := hbind l hmem htag
    rw [hfalse] at hver
    cases hver

/-! ## Counterexample: `peel` alone does not enforce the check -/

/-- An interface whose verifier rejects every tag. -/
def rejectingInterface : OnionInterface where
  verifyHmac := fun _ _ => false
  hmacBinding := False

/-- A sample hop used only by the counterexample. -/
def sampleHop : OnionHop where
  node := { index := 0 }
  shortChannelId := { block := 0, txIndex := 0, outputIndex := 0 }
  amountMsat := { val := 1000 }
  cltvDelta := 40

/-- A one-layer sample packet with an empty (rejected) HMAC. -/
def samplePacket : OnionPacket where
  version := ONION_VERSION
  ephemeralKey := { bytes := ByteArray.empty }
  routingInfo := ByteArray.empty
  layers := [{ hop := sampleHop, ciphertext := ByteArray.empty,
               hmac := ByteArray.empty }]
  hmac := ByteArray.empty

/-- **`peel` bypasses the HMAC check.**  With an always-rejecting verifier,
the checked peel rejects the layer, but the structural `peel` still returns
a forward payload.  Hence the rejection theorem is a statement about
`openLayer`, not about `peel`; the model's `peel` is intentionally total. -/
theorem waveD_d25_peel_bypasses_hmac :
    MacInvalid rejectingInterface ByteArray.empty
        { hop := sampleHop, ciphertext := ByteArray.empty,
          hmac := ByteArray.empty } ∧
      (∃ next, peel samplePacket =
        some (.forward sampleHop next)) ∧
      openLayer rejectingInterface ByteArray.empty samplePacket = none := by
  refine ⟨rfl, ⟨⟨ONION_VERSION, { bytes := ByteArray.empty },
    ByteArray.empty, [], ByteArray.empty⟩, rfl⟩, ?_⟩
  simp [openLayer, rejectingInterface, samplePacket, sampleHop]

end LnLean.Proofs.WaveD.D25
