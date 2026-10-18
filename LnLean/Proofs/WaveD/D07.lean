/-
# D07 — Onion integrity checks are HMAC-SHA256 tags (C8)

**English claim.**  A BOLT 4 onion layer is authenticated by a 32-byte
HMAC-SHA256 tag.  During onion decryption the receiver derives the per-hop
`mu` key, computes

```
HMAC256(mu, hop_payloads || associated_data)
```

and accepts the layer only when this value equals the packet's `hmac` field
(`refs/bolts/04-onion-routing.md:936-939`).  The security property used here
is assumption C8: under a fixed key, HMAC-SHA256 is a PRF, so a tag can
authenticate at most one message.  In the Lean model C8 is the `Prop`-valued
field `PrimitiveModel.hmac_prf` (`HmacPrf M.hmacSha256`); it is never an
axiom.

This module connects the model's `hmacSha256` operation to the onion
interface of `LnLean.Routing.Onion`:

* `onionHmacTag` is the BOLT 4 tag construction above.
* `hmacOnionInterface` is the concrete `OnionInterface` whose verifier
  compares the expected tag with the stored layer tag, and whose
  `hmacBinding` proposition is exactly C8.
* `openWithHmac` opens a layer using the expected BOLT 4 tag.  A successful
  open yields a head layer whose stored `hmac` is that HMAC tag, and (under
  C8) that tag determines the authenticated `hop_payloads` uniquely: any
  other payload list offered with the same tag and associated data is equal
  to the original one.

The final theorem records why the *abstract* `OnionInterface` alone is not
enough: its verifier is an uninterpreted `Bool` function, so a permissive
interface accepts an arbitrary stored tag.  The HMAC link and the C8 field
are what rule this out; no such permissive interface is used by
`hmacOnionInterface`.

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
encoding, and constant-time comparison.  The model idealises C8 as exact
injectivity of `hmacSha256` in its message argument for a fixed key, which is
stronger than the computational PRF statement but is the visible
over-approximation already used by the model.  No theorem below asserts a
concrete HMAC value or computational hardness.
-/

import LnLean.Crypto.Hash
import LnLean.Crypto.Model
import LnLean.Routing.Onion

namespace LnLean.Proofs.WaveD.D07

open LnLean LnLean.Crypto LnLean.Routing

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

/-- Assumption C8, as supplied by the model's `hmac_prf` field.  Stating it
separately keeps the dependency on C8 visible in every security theorem. -/
theorem waveD_d07_c8_from_model (M : PrimitiveModel) : HmacPrf M.hmacSha256 :=
  M.hmac_prf

/-! ## C8: a tag authenticates one message -/

/-- Under C8, equal tags under the same `mu` force equal authenticated
messages (the concatenated `hop_payloads || associated_data`). -/
theorem waveD_d07_onionHmacTag_message_unique (M : PrimitiveModel)
    (hC8 : HmacPrf M.hmacSha256) {mu hp₁ hp₂ ad₁ ad₂ : ByteArray}
    (h : onionHmacTag M mu hp₁ ad₁ = onionHmacTag M mu hp₂ ad₂) :
    hp₁ ++ ad₁ = hp₂ ++ ad₂ := by
  exact hC8 mu (hp₁ ++ ad₁) (hp₂ ++ ad₂) h

/-- With the same associated data, an authentic tag determines the
`hop_payloads` value: two payload lists carrying the same tag under the same
`mu` are equal.  This is the message-binding content of C8 at the onion
payload boundary. -/
theorem waveD_d07_onionHmacTag_payloads_unique (M : PrimitiveModel)
    (hC8 : HmacPrf M.hmacSha256) {mu hp₁ hp₂ ad : ByteArray}
    (h : onionHmacTag M mu hp₁ ad = onionHmacTag M mu hp₂ ad) : hp₁ = hp₂ := by
  exact append_right_cancel (waveD_d07_onionHmacTag_message_unique M hC8 h)

/-- No tag reuse for distinct payloads: an attacker cannot present a
different `hop_payloads` value under the genuine tag. -/
theorem waveD_d07_onionHmacTag_no_reuse (M : PrimitiveModel)
    (hC8 : HmacPrf M.hmacSha256) {mu hp hp' ad : ByteArray}
    (hne : hp' ≠ hp) :
    onionHmacTag M mu hp' ad ≠ onionHmacTag M mu hp ad := by
  intro htag
  exact hne (waveD_d07_onionHmacTag_payloads_unique M hC8 htag)

/-! ## A concrete HMAC onion interface -/

/-- The concrete onion interface used for HMAC tags.  The verifier accepts a
layer only when its stored tag is exactly the expected tag; C8 is the
interface's `hmacBinding` proposition. -/
def hmacOnionInterface (M : PrimitiveModel) : OnionInterface where
  verifyHmac := fun expected stored => decide (expected = stored)
  hmacBinding := HmacPrf M.hmacSha256

/-- The concrete verifier accepts exactly when the expected and stored tags
are equal. -/
theorem waveD_d07_hmacOnionInterface_verify (M : PrimitiveModel)
    (expected stored : ByteArray) :
    (hmacOnionInterface M).verifyHmac expected stored = true ↔
      expected = stored := by
  unfold hmacOnionInterface
  simp

/-- Open the outermost layer against the BOLT 4 tag computed for
`hopPayloads || associatedData`. -/
def openWithHmac (M : PrimitiveModel) (mu hopPayloads associatedData : ByteArray)
    (p : OnionPacket) : Option (OnionHop × OnionPacket) :=
  openLayer (hmacOnionInterface M) (onionHmacTag M mu hopPayloads associatedData) p

/-- **Mechanical half.**  A successful HMAC open yields the head layer and
its stored tag is exactly the expected BOLT 4 tag. -/
theorem waveD_d07_openWithHmac_tag (M : PrimitiveModel)
    {mu hopPayloads associatedData : ByteArray} {p : OnionPacket}
    {hop : OnionHop} {next : OnionPacket}
    (hopen : openWithHmac M mu hopPayloads associatedData p = some (hop, next)) :
    ∃ l, l ∈ p.layers ∧ l.hop = hop ∧
      l.hmac = onionHmacTag M mu hopPayloads associatedData := by
  unfold openWithHmac at hopen
  obtain ⟨l, hmem, hhop, hver⟩ := openLayer_verified hopen
  refine ⟨l, hmem, hhop, ?_⟩
  exact ((waveD_d07_hmacOnionInterface_verify M _ _).mp hver).symm

/-- **Integrity under C8.**  A successful HMAC open yields a head layer whose
tag authenticates `hopPayloads`, and any other payload list offered with that
same tag and associated data must be the original one. -/
theorem waveD_d07_openWithHmac_layer_authentic (M : PrimitiveModel)
    (hC8 : HmacPrf M.hmacSha256)
    {mu hopPayloads associatedData : ByteArray} {p : OnionPacket}
    {hop : OnionHop} {next : OnionPacket}
    (hopen : openWithHmac M mu hopPayloads associatedData p = some (hop, next)) :
    ∃ l, l ∈ p.layers ∧ l.hop = hop ∧
      l.hmac = onionHmacTag M mu hopPayloads associatedData ∧
      (∀ hp', l.hmac = onionHmacTag M mu hp' associatedData → hp' = hopPayloads) := by
  obtain ⟨l, hmem, hhop, htag⟩ :=
    waveD_d07_openWithHmac_tag M hopen
  refine ⟨l, hmem, hhop, htag, ?_⟩
  intro hp' hclaim
  apply waveD_d07_onionHmacTag_payloads_unique M hC8
  rw [← hclaim, htag]

/-! ## Why the abstract interface needs the HMAC link -/

/-- A permissive `OnionInterface`: its verifier ignores both arguments.  This
shows that `OnionInterface.verifyHmac` is uninterpreted in the base onion
model, so the HMAC/C8 connection must be supplied by a concrete interface
such as `hmacOnionInterface`, not derived from the interface alone. -/
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
