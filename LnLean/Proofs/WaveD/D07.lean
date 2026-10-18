/-
# D07 — Onion integrity checks are HMAC-SHA256 tags (C8)

**English claim.**  A BOLT 4 onion layer is authenticated by a 32-byte
HMAC-SHA256 tag.  During onion decryption the receiver derives the per-hop
`mu` key, computes

```
HMAC256(mu, hop_payloads || associated_data)
```

and accepts the layer only when this value equals the packet's `hmac` field
(`refs/bolts/04-onion-routing.md:936-939`).

**C8 is a finite-execution admission.**  The security property used here is
that, for the messages of *one* onion execution, equal tags under the same
`mu` authenticate equal messages.  This is the predicate
`HmacBindsOn M.hmacSha256 mu msgs`, where `msgs` is the finite list of
`hop_payloads || associated_data` values in scope.  It is satisfiable whenever
those finitely many messages have pairwise distinct tags (the structural
theorem `hmacBindsOn_of_pairwise_tags`; `hmacBindsOn_singleton` gives an
explicit non-empty instance).  It is **not** the global claim that
`hmacSha256` is injective on all `ByteArray` for a fixed key.  That global
claim is uninhabited for any 32-byte-output HMAC, which this module proves as
the negative theorem `hmacPrf_vacuous` using the pigeonhole result
`no_injective_hash_into_32_bytes`.  The abbreviation `HmacPrf` remains only
for that negative result and for traceability; it is no longer a field of
`PrimitiveModel` and no positive theorem assumes it.

This module connects the model's `hmacSha256` operation to the onion
interface of `LnLean.Routing.Onion`:

* `onionHmacTag` is the BOLT 4 tag construction above.
* `hmacOnionInterface M mu msgs` is the concrete `OnionInterface` whose
  verifier compares the expected tag with the stored layer tag, and whose
  `hmacBinding` proposition is exactly `HmacBindsOn M.hmacSha256 mu msgs`.
* `openWithHmac` opens a layer using the expected BOLT 4 tag.  A successful
  open yields a head layer whose stored `hmac` is that HMAC tag, and (under
  the finite-execution admission) that tag determines the authenticated
  `hop_payloads` uniquely on `msgs`: any other payload list whose
  `hop_payloads || associated_data` is in `msgs` and which carries the same
  tag and associated data is equal to the original one.

The final theorem records why the *abstract* `OnionInterface` alone is not
enough: its verifier is an uninterpreted `Bool` function, so a permissive
interface accepts an arbitrary stored tag.  The HMAC link and the C8
admission are what rule this out for `hmacOnionInterface`; no such permissive
interface is used there.

**BOLT sections.**  BOLT 4 §Packet Structure (`hmac` is a 32-byte field of
the packet and of each `hop_payloads` entry; `refs/bolts/04-onion-routing.md:147-176`)
and §Onion Decryption (`refs/bolts/04-onion-routing.md:936-939`: derive `mu`,
compute `HMAC256(mu, hop_payloads || associated_data)`, compare in constant
time, reject on mismatch).

**rust-lightning anchors (pinned commit `fe49009`).**
* `lightning/src/ln/onion_payment.rs:505` — `peel_payment_onion`, the inbound
  onion peel/forward/deliver path.
* `lightning/src/ln/onion_utils.rs` — onion packet construction and the
  `mu`-keyed HMAC used for each layer.

**Not modelled.**  The Sphinx key schedule (`mu` is an opaque byte array
here), the ChaCha20-Poly1305 layer encryption, the concrete `hop_payloads`
encoding, and constant-time comparison.  The tag-binding contract is an exact
algebraic law over the finite messages of one execution, not a computational
PRF or unforgeability game; computational HMAC security and forgery
resistance are outside the model.  No theorem below asserts a concrete HMAC
value or computational hardness.
-/

import LnLean.Crypto.Hash
import LnLean.Crypto.Model
import LnLean.Proofs.Crypto.Sha256Props
import LnLean.Routing.Onion

namespace LnLean.Proofs.WaveD.D07

open LnLean LnLean.Crypto LnLean.Routing LnLean.Proofs.Crypto

set_option autoImplicit false

-- OBLIGATION: LN-WD-D07

/-! ## The BOLT 4 tag -/

/-- The BOLT 4 layer tag: `HMAC256(mu, hop_payloads || associated_data)`.
`mu` is the per-hop HMAC key derived from the shared secret; the model keeps
it opaque.  `associatedData` carries the packet fields that BOLT 4 binds to
the tag (the modeller supplies them; the onion model does not encode them). -/
def onionHmacTag (M : PrimitiveModel) (mu hopPayloads associatedData : ByteArray) :
    ByteArray :=
  M.hmacSha256 mu (hopPayloads ++ associatedData)

/-- The tag has exactly the 32-byte width of BOLT 4's `hmac` field. -/
theorem waveD_d07_onionHmacTag_size_eq_32 (M : PrimitiveModel)
    (mu hopPayloads associatedData : ByteArray) :
    (onionHmacTag M mu hopPayloads associatedData).size = 32 := by
  unfold onionHmacTag
  exact M.hmac_size mu (hopPayloads ++ associatedData)

/-- The tag width is the onion model's constant `ONION_HMAC_LEN`. -/
theorem waveD_d07_onionHmacTag_size_eq_ONION_HMAC_LEN (M : PrimitiveModel)
    (mu hopPayloads associatedData : ByteArray) :
    (onionHmacTag M mu hopPayloads associatedData).size = ONION_HMAC_LEN := by
  rw [waveD_d07_onionHmacTag_size_eq_32]
  rfl

/-! ## C8 as a finite-execution admission -/

/-- Finite-execution HMAC tag binding: on the finite message list `msgs` of
one onion execution, two messages with the same tag under the same key `mu`
are equal.  This is satisfiable for any HMAC on a message set with pairwise
distinct tags; it makes no global injectivity claim. -/
def HmacBindsOn (hmac : ByteArray → ByteArray → ByteArray)
    (mu : ByteArray) (msgs : List ByteArray) : Prop :=
  ∀ m₁ ∈ msgs, ∀ m₂ ∈ msgs, hmac mu m₁ = hmac mu m₂ → m₁ = m₂

/-- **Negative result, not an axiom.**  For a fixed key, a 32-byte-output
`hmacSha256` cannot be injective on all of `ByteArray`.  This is the HMAC
instance of `no_injective_hash_into_32_bytes`; it is why `HmacPrf` is not a
field of `PrimitiveModel`. -/
theorem hmacPrf_vacuous (M : PrimitiveModel) (k : ByteArray) :
    ¬ HmacPrf M.hmacSha256 := by
  intro h
  exact no_injective_hash_into_32_bytes
    (fun m : ByteArray => M.hmacSha256 k m)
    (fun m : ByteArray => M.hmac_size k m)
    (fun m₁ m₂ heq => h k m₁ m₂ heq)

/-- The finite contract is satisfied whenever the messages in scope have
pairwise distinct tags.  This is the precise satisfiability condition: no
claim is made about messages outside the execution. -/
theorem hmacBindsOn_of_pairwise_tags
    {hmac : ByteArray → ByteArray → ByteArray} {mu : ByteArray}
    {msgs : List ByteArray}
    (h : ∀ m₁ ∈ msgs, ∀ m₂ ∈ msgs, m₁ ≠ m₂ → hmac mu m₁ ≠ hmac mu m₂) :
    HmacBindsOn hmac mu msgs := by
  intro m₁ hm₁ m₂ hm₂ heq
  by_cases hne : m₁ = m₂
  · exact hne
  · exact absurd heq (h m₁ hm₁ m₂ hm₂ hne)

/-- An explicit non-empty instance: on a one-message execution the binding
contract holds for every HMAC, with no cryptographic assumption. -/
theorem hmacBindsOn_singleton (hmac : ByteArray → ByteArray → ByteArray)
    (mu m : ByteArray) : HmacBindsOn hmac mu [m] := by
  intro m₁ hm₁ m₂ hm₂ _
  simp only [List.mem_singleton] at hm₁ hm₂
  rw [hm₁, hm₂]

/-! ## C8: a tag authenticates one message -/

/-- Under the finite-execution admission, equal tags under the same `mu`
force equal authenticated messages (the concatenated
`hop_payloads || associated_data`) whenever both concatenations belong to the
execution's message list. -/
theorem waveD_d07_onionHmacTag_message_unique (M : PrimitiveModel)
    {mu : ByteArray} {msgs : List ByteArray}
    (hb : HmacBindsOn M.hmacSha256 mu msgs) {hp₁ hp₂ ad₁ ad₂ : ByteArray}
    (hm₁ : hp₁ ++ ad₁ ∈ msgs) (hm₂ : hp₂ ++ ad₂ ∈ msgs)
    (h : onionHmacTag M mu hp₁ ad₁ = onionHmacTag M mu hp₂ ad₂) :
    hp₁ ++ ad₁ = hp₂ ++ ad₂ := by
  exact hb (hp₁ ++ ad₁) hm₁ (hp₂ ++ ad₂) hm₂ h

/-- With the same associated data, an authentic tag determines the
`hop_payloads` value: two payload lists carrying the same tag under the same
`mu` are equal, provided both concatenations are in the execution's message
list.  This is the message-binding content of C8 at the onion payload
boundary. -/
theorem waveD_d07_onionHmacTag_payloads_unique (M : PrimitiveModel)
    {mu : ByteArray} {msgs : List ByteArray}
    (hb : HmacBindsOn M.hmacSha256 mu msgs) {hp₁ hp₂ ad : ByteArray}
    (hm₁ : hp₁ ++ ad ∈ msgs) (hm₂ : hp₂ ++ ad ∈ msgs)
    (h : onionHmacTag M mu hp₁ ad = onionHmacTag M mu hp₂ ad) : hp₁ = hp₂ := by
  exact append_right_cancel (waveD_d07_onionHmacTag_message_unique M hb hm₁ hm₂ h)

/-- No tag reuse for distinct payloads on the admitted message set: an
attacker cannot present a different `hop_payloads` value under the genuine
tag when both concatenations are in `msgs`. -/
theorem waveD_d07_onionHmacTag_no_reuse (M : PrimitiveModel)
    {mu : ByteArray} {msgs : List ByteArray}
    (hb : HmacBindsOn M.hmacSha256 mu msgs) {hp hp' ad : ByteArray}
    (hm' : hp' ++ ad ∈ msgs) (hm : hp ++ ad ∈ msgs) (hne : hp' ≠ hp) :
    onionHmacTag M mu hp' ad ≠ onionHmacTag M mu hp ad := by
  intro htag
  exact hne (waveD_d07_onionHmacTag_payloads_unique M hb hm' hm htag)

/-! ## A concrete HMAC onion interface -/

/-- The concrete onion interface used for HMAC tags.  The verifier accepts a
layer only when its stored tag is exactly the expected tag; C8 is the
interface's `hmacBinding` proposition, the finite-execution tag binding on the
messages `msgs` under `mu`. -/
def hmacOnionInterface (M : PrimitiveModel) (mu : ByteArray)
    (msgs : List ByteArray) : OnionInterface where
  verifyHmac := fun expected stored => decide (expected = stored)
  hmacBinding := HmacBindsOn M.hmacSha256 mu msgs

/-- The concrete verifier accepts exactly when the expected and stored tags
are equal. -/
theorem waveD_d07_hmacOnionInterface_verify (M : PrimitiveModel) (mu : ByteArray)
    (msgs : List ByteArray) (expected stored : ByteArray) :
    (hmacOnionInterface M mu msgs).verifyHmac expected stored = true ↔
      expected = stored := by
  unfold hmacOnionInterface
  simp

/-- Open the outermost layer against the BOLT 4 tag computed for
`hopPayloads || associatedData`.  The message list `msgs` is the finite
execution context carrying the C8 admission; the verifier itself depends only
on the expected and stored tags. -/
def openWithHmac (M : PrimitiveModel) (mu : ByteArray) (msgs : List ByteArray)
    (hopPayloads associatedData : ByteArray) (p : OnionPacket) :
    Option (OnionHop × OnionPacket) :=
  openLayer (hmacOnionInterface M mu msgs)
    (onionHmacTag M mu hopPayloads associatedData) p

/-- **Mechanical half.**  A successful HMAC open yields the head layer and
its stored tag is exactly the expected BOLT 4 tag. -/
theorem waveD_d07_openWithHmac_tag (M : PrimitiveModel)
    {mu : ByteArray} {msgs : List ByteArray}
    {hopPayloads associatedData : ByteArray} {p : OnionPacket}
    {hop : OnionHop} {next : OnionPacket}
    (hopen : openWithHmac M mu msgs hopPayloads associatedData p =
      some (hop, next)) :
    ∃ l, l ∈ p.layers ∧ l.hop = hop ∧
      l.hmac = onionHmacTag M mu hopPayloads associatedData := by
  unfold openWithHmac at hopen
  obtain ⟨l, hmem, hhop, hver⟩ := openLayer_verified hopen
  refine ⟨l, hmem, hhop, ?_⟩
  exact ((waveD_d07_hmacOnionInterface_verify M mu msgs _ _).mp hver).symm

/-- **Integrity under finite-execution C8.**  A successful HMAC open yields a
head layer whose tag authenticates `hopPayloads`, and any other payload list
whose concatenation is in the admitted message set and which is offered with
that same tag and associated data must be the original one. -/
theorem waveD_d07_openWithHmac_layer_authentic (M : PrimitiveModel)
    {mu : ByteArray} {msgs : List ByteArray}
    (hb : HmacBindsOn M.hmacSha256 mu msgs)
    {hopPayloads associatedData : ByteArray} {p : OnionPacket}
    {hop : OnionHop} {next : OnionPacket}
    (hmem : hopPayloads ++ associatedData ∈ msgs)
    (hopen : openWithHmac M mu msgs hopPayloads associatedData p =
      some (hop, next)) :
    ∃ l, l ∈ p.layers ∧ l.hop = hop ∧
      l.hmac = onionHmacTag M mu hopPayloads associatedData ∧
      (∀ hp', hp' ++ associatedData ∈ msgs →
        l.hmac = onionHmacTag M mu hp' associatedData → hp' = hopPayloads) := by
  obtain ⟨l, hmeml, hhop, htag⟩ :=
    waveD_d07_openWithHmac_tag M hopen
  refine ⟨l, hmeml, hhop, htag, ?_⟩
  intro hp' hmem' hclaim
  apply waveD_d07_onionHmacTag_payloads_unique M hb hmem' hmem
  rw [← hclaim, htag]

/-! ## Why the abstract interface needs the HMAC link -/

/-- A permissive `OnionInterface`: its verifier ignores both arguments and
its binding contract is the intentionally weakest proposition.  This shows
that `OnionInterface.verifyHmac` is uninterpreted in the base onion model, so
the HMAC/C8 connection must be supplied by a concrete interface such as
`hmacOnionInterface`, not derived from the interface alone. -/
def permissiveOnionInterface : OnionInterface where
  verifyHmac := fun _ _ => true
  hmacBinding := True

/-- The abstract interface admits a verifier that accepts a stored tag
different from the expected one. -/
theorem waveD_d07_abstract_interface_accepts_any_tag :
    ∃ (I : OnionInterface) (expected stored : ByteArray),
      I.verifyHmac expected stored = true ∧ stored ≠ expected := by
  refine ⟨permissiveOnionInterface, ByteArray.empty, ByteArray.mk #[1], rfl, ?_⟩
  decide

end LnLean.Proofs.WaveD.D07
