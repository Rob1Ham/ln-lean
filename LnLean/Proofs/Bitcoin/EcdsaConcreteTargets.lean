import LnLean.Proofs.Bitcoin.EcdsaBridgeTargets

/-!
# Concrete ECDSA targets: the `verifyImpl` instance is vacuous under C3

Wave 8 (`EcdsaBridgeTargets`) made the abstract ECDSA seam explicit:
`VendorEcdsaBridge M` is the pointwise equation between the model verifier
`M.ecdsaVerify` and the vendored
`Bitcoin.Crypto.Ecdsa.Verify.verifyImpl`, and `withVendorEcdsa M₀ hEuf` is a
`PrimitiveModel` whose verifier is literally `verifyImpl`, built from a
supplied `hEuf : EufCma vendorVerify`.

This module answers the wave-9 question left open by that construction:
*can a concrete `verifyImpl` instance satisfy or replace
`VendorEcdsaBridge`?*  The answer is a sharp dichotomy, not a new
assumption:

* `eufCma_vendorVerify_iff_totalReject` — the model's C3 hypothesis at the
  vendor verifier is **equivalent to total rejection**:
  `EufCma vendorVerify ↔ ∀ pk msg sig, verifyImpl sig.bytes pk.bytes msg = false`.
  The forward direction uses only one structural fact: `verifyImpl` reads the
  message through `bytesToNatBE msg % n`, so prepending a zero byte leaves the
  verdict unchanged while changing the byte string
  (`zeroPad`, `bytesToNatBE_zeroPad`, `verifyImpl_zeroPad`).  A verifier with
  that invariance cannot bind byte-level messages unless every verification
  fails.
* `exists_bridged_model_iff_totalReject` — a `PrimitiveModel` satisfying the
  bridge exists **iff** the concrete verifier rejects every input.  The
  backward direction is `withVendorEcdsa`; the forward direction uses the
  mandatory `M.ecdsa_eufCma` field.
* `no_bridged_nontrivial_model` — no bridged model accepts any signature.
  Equivalently, the concrete instance exists only in the vacuous case.
* `withVendorEcdsa_totalReject` and `withVendorEcdsa_no_funding` — the Wave-8
  concrete model's verifier is the constant-`false` function, so its checked
  funding predicate is always `false` and `fundingSignedValid` is
  unsatisfiable.  The Wave-8 funding-binding theorem is therefore true but
  vacuous at that instance.

The obstruction is *not* an ECDSA security claim.  It is the mismatch between
the model's untyped `ByteArray` message argument (with byte-level `EufCma`)
and the vendor verifier's scalar reduction.  The same module isolates the
strongest property the concrete interface can actually support:

* `ResidueBinding verify` — any two accepted messages have equal reduced
  scalar `bytesToNatBE · % n`.  `EufCma v → ResidueBinding v`
  (`residueBinding_of_eufCma`), but the converse fails
  (`residueBinding_not_eufCma`, using `residueZeroVerify`), so this is a
  genuine weakening rather than a restatement.
* `VendorEcdsaContract` — `ResidueBinding vendorVerify ∧ KeyBinding
  vendorVerify`.  It transfers across the bridge
  (`residueBinding_iff_vendor`), and it is consistent with acceptance
  (`contract_consistent_with_acceptance`, via the abstract `pointVerify`).
  Adding C3 to the contract forces total rejection
  (`eufCma_and_contract_iff`).
* `residueBinding_vendor_funding_eq_of_digestBinds` — the exact conditional
  extraction: residue binding plus a digest-injectivity side condition
  `DigestBindsMod fundingTag` gives `m₁ = m₂`.  The side condition is not
  automatic: `not_digestBindsMod_fundingTag` exhibits two distinct 33-byte
  messages whose funding-tagged values differ by exactly `n`.  A faithful
  repair must therefore restrict transaction encodings (or use a typed digest
  domain), not merely weaken C3 to residue binding.

## What is not claimed

There is no ECDSA security proof, no forgery, and no unconditional consensus
statement.  `EufCma vendorVerify` is not refuted unconditionally: that would
require a mechanized accepted signature, which is deliberately not attempted
here.  The negative results are stated relative to an explicit acceptance
witness (`AcceptsSome`).  Key binding remains an independent hypothesis: the
module proves `ResidueBinding` does not imply it, and the existing
`eufCma_not_keyBinding` counterexample is retained by import.

The concrete digest counterexample uses `fundingTag` and two 33-byte
encodings; it shows the tagged residue map is not injective on the untyped
`ByteArray` domain, not that two real transactions collide.
-/

namespace LnLean.Proofs.Bitcoin.EcdsaConcreteTargets

set_option autoImplicit false

open Bitcoin.Crypto.Curve.Secp (bytesToNatBE n)
open Bitcoin.Crypto.Ecdsa.Verify
open LnLean
open LnLean.Crypto
open LnLean.Proofs.Bitcoin.EcdsaBridgeTargets

/-! ## 1. Non-canonical message representations

`bytesToNatBE` is a big-endian fold starting at `0`, so a leading zero byte
does not change the numeric value.  This is the entire mechanism behind the
obstruction: the vendor verifier sees the value, while `EufCma` quantifies
over the byte string.
-/

/-- Prepend one zero byte.  The numeric value is unchanged, the byte string
is not. -/
def zeroPad (b : ByteArray) : ByteArray :=
  ByteArray.mk (0 :: b.data.toList).toArray

/-- A zero-padded message is strictly longer. -/
theorem zeroPad_size (b : ByteArray) : (zeroPad b).size = b.size + 1 := by
  show (0 :: b.data.toList).toArray.size = b.data.size + 1
  rw [List.size_toArray]
  simp

/-- A zero-padded message is a different byte string. -/
theorem zeroPad_ne (b : ByteArray) : zeroPad b ≠ b := by
  intro h
  have hs := congrArg ByteArray.size h
  rw [zeroPad_size] at hs
  omega

/-- Zero padding preserves the big-endian numeric value. -/
theorem bytesToNatBE_zeroPad (b : ByteArray) :
    bytesToNatBE (zeroPad b) = bytesToNatBE b := by
  unfold bytesToNatBE zeroPad
  simp

/-- Consequently it preserves the reduced scalar. -/
theorem zeroPad_modEq (b : ByteArray) :
    bytesToNatBE (zeroPad b) % n = bytesToNatBE b % n := by
  rw [bytesToNatBE_zeroPad]

/-- `verifyImpl` cannot distinguish a message from its zero-padded form. -/
theorem verifyImpl_zeroPad (sig pk b : ByteArray) :
    verifyImpl sig pk (zeroPad b) = verifyImpl sig pk b := by
  apply verifyImpl_msg_congr
  exact zeroPad_modEq b

/-! ## 2. The obstruction: C3 at the vendor verifier is total rejection -/

/-- A verifier accepts at least one input. -/
def AcceptsSome (v : PubKey → ByteArray → EcdsaSig → Bool) : Prop :=
  ∃ (pk : PubKey) (msg : ByteArray) (sig : EcdsaSig), v pk msg sig = true

/-- **General zero-padding obstruction.**  Any verifier invariant under
prepending a zero byte satisfies byte-level `EufCma` only if it rejects every
input.  The converse is immediate. -/
theorem eufCma_iff_totalReject_of_zeroPad
    (v : PubKey → ByteArray → EcdsaSig → Bool)
    (hpad : ∀ (pk : PubKey) (msg : ByteArray) (sig : EcdsaSig),
      v pk (zeroPad msg) sig = v pk msg sig) :
    EufCma v ↔
      ∀ (pk : PubKey) (msg : ByteArray) (sig : EcdsaSig), v pk msg sig = false := by
  constructor
  · intro he pk msg sig
    cases h : v pk msg sig with
    | false => rfl
    | true =>
        exfalso
        have hpad' : v pk (zeroPad msg) sig = true := by rw [hpad]; exact h
        exact zeroPad_ne msg (he pk msg (zeroPad msg) sig h hpad').symm
  · intro h pk m₁ m₂ s h₁ h₂
    have hfalse := h pk m₁ s
    rw [hfalse] at h₁
    exact (Bool.false_ne_true h₁).elim

/-- **The concrete obstruction.**  `EufCma vendorVerify` holds exactly when
the vendored verifier rejects every key/message/signature triple.  In
particular, on any input where ECDSA verification succeeds, the model's C3
field is false for the concrete verifier. -/
theorem eufCma_vendorVerify_iff_totalReject :
    EufCma vendorVerify ↔
      ∀ (pk : PubKey) (msg : ByteArray) (sig : EcdsaSig),
        vendorVerify pk msg sig = false :=
  eufCma_iff_totalReject_of_zeroPad vendorVerify
    (fun pk msg sig => verifyImpl_zeroPad sig.bytes pk.bytes msg)

/-- Boolean-existence form: C3 fails exactly when the vendor verifier accepts
something. -/
theorem not_eufCma_vendorVerify_iff_accepts :
    ¬ EufCma vendorVerify ↔ AcceptsSome vendorVerify := by
  rw [eufCma_vendorVerify_iff_totalReject]
  constructor
  · intro h
    apply Classical.byContradiction
    intro hnone
    apply h
    intro pk msg sig
    cases hb : vendorVerify pk msg sig with
    | false => rfl
    | true => exact (hnone ⟨pk, msg, sig, hb⟩).elim
  · rintro ⟨pk, msg, sig, h⟩ htotal
    have hf := htotal pk msg sig
    rw [hf] at h
    exact (Bool.false_ne_true h).elim

/-- Conditional refutation: one accepted signature refutes C3 at
`verifyImpl`.  This is the sharp form of the wave-8 message-reduction
boundary, with `zeroPad` as the explicit same-residue companion. -/
theorem not_eufCma_vendorVerify_of_accepts
    (hacc : ∃ (pk : PubKey) (msg : ByteArray) (sig : EcdsaSig),
      verifyImpl sig.bytes pk.bytes msg = true) :
    ¬ EufCma vendorVerify :=
  not_eufCma_vendorVerify_iff_accepts.mpr hacc

/-! ## 3. What the bridge can and cannot identify

The bridge itself is satisfiable, but only by a model whose verifier is the
constant-`false` function.  This is the exact answer to "can a concrete
`verifyImpl` instance replace `VendorEcdsaBridge`?": the pointwise bridge is
realized, but its C3 field cannot be non-vacuous.
-/

/-- **C3 through the bridge.**  For any model satisfying the pointwise bridge,
the model's `EufCma` field is exactly the statement that `verifyImpl` rejects
every input. -/
theorem bridge_eufCma_iff_verifyImpl_totalReject (M : PrimitiveModel)
    (h : VendorEcdsaBridge M) :
    EufCma M.ecdsaVerify ↔
      ∀ (pk : PubKey) (msg : ByteArray) (sig : EcdsaSig),
        verifyImpl sig.bytes pk.bytes msg = false := by
  rw [eufCma_iff_vendor M h, eufCma_vendorVerify_iff_totalReject]
  rfl

/-- No bridged model can accept a signature. -/
theorem no_accepted_signature_of_bridged_eufCma (M : PrimitiveModel)
    (h : VendorEcdsaBridge M)
    (hacc : ∃ (pk : PubKey) (msg : ByteArray) (sig : EcdsaSig),
      verifyImpl sig.bytes pk.bytes msg = true) : False := by
  have htot := (bridge_eufCma_iff_verifyImpl_totalReject M h).mp M.ecdsa_eufCma
  rcases hacc with ⟨pk, msg, sig, hv⟩
  have hf := htot pk msg sig
  rw [hf] at hv
  exact Bool.false_ne_true hv

/-- **Every bridged model is total-rejecting.**  This is the unconditional
form of the separation: the pointwise bridge plus the mandatory C3 field leave
no room for an accepting verifier. -/
theorem bridged_model_totalReject (M : PrimitiveModel)
    (h : VendorEcdsaBridge M) :
    ∀ (pk : PubKey) (msg : ByteArray) (sig : EcdsaSig),
      M.ecdsaVerify pk msg sig = false := by
  intro pk msg sig
  have htot := (bridge_eufCma_iff_verifyImpl_totalReject M h).mp M.ecdsa_eufCma
  rw [h pk msg sig]
  exact htot pk msg sig

/-- No bridged model accepts any signature. -/
theorem bridged_model_no_accept (M : PrimitiveModel)
    (h : VendorEcdsaBridge M) :
    ¬ ∃ (pk : PubKey) (msg : ByteArray) (sig : EcdsaSig),
      M.ecdsaVerify pk msg sig = true := by
  rintro ⟨pk, msg, sig, hv⟩
  have hf := bridged_model_totalReject M h pk msg sig
  rw [hf] at hv
  exact Bool.false_ne_true hv

/-- **No non-vacuous bridged model.**  There is no `PrimitiveModel` that both
satisfies `VendorEcdsaBridge` and accepts at least one signature. -/
theorem no_bridged_nontrivial_model :
    ¬ ∃ M : PrimitiveModel,
        VendorEcdsaBridge M ∧
          ∃ (pk : PubKey) (msg : ByteArray) (sig : EcdsaSig),
            M.ecdsaVerify pk msg sig = true := by
  rintro ⟨M, h, hacc⟩
  exact bridged_model_no_accept M h hacc

/-- **Exact existence criterion.**  A bridged `PrimitiveModel` exists exactly
when the concrete verifier is total-rejecting.  The backward direction is the
Wave-8 construction `withVendorEcdsa`; the forward direction is the
obstruction above.  The parameter `M₀` is any ambient model supplying the
other primitive fields; the criterion itself does not depend on it. -/
theorem exists_bridged_model_iff_totalReject (M₀ : PrimitiveModel) :
    (∃ M : PrimitiveModel, VendorEcdsaBridge M) ↔
      ∀ (pk : PubKey) (msg : ByteArray) (sig : EcdsaSig),
        verifyImpl sig.bytes pk.bytes msg = false := by
  constructor
  · rintro ⟨M, h⟩
    exact (bridge_eufCma_iff_verifyImpl_totalReject M h).mp M.ecdsa_eufCma
  · intro htot
    have hEuf : EufCma vendorVerify :=
      eufCma_vendorVerify_iff_totalReject.mpr htot
    exact ⟨withVendorEcdsa M₀ hEuf, withVendorEcdsa_bridge M₀ hEuf⟩

/-- The converse of the obstruction as a usable introduction rule. -/
theorem eufCma_of_totalReject
    (h : ∀ (pk : PubKey) (msg : ByteArray) (sig : EcdsaSig),
      vendorVerify pk msg sig = false) :
    EufCma vendorVerify :=
  eufCma_vendorVerify_iff_totalReject.mpr h

/-! ### The Wave-8 concrete model is the total-rejecting model -/

/-- The constructed model's verifier is total-rejecting. -/
theorem withVendorEcdsa_totalReject (M₀ : PrimitiveModel)
    (hEuf : EufCma vendorVerify) (pk : PubKey) (msg : ByteArray)
    (sig : EcdsaSig) :
    (withVendorEcdsa M₀ hEuf).ecdsaVerify pk msg sig = false := by
  rw [withVendorEcdsa_ecdsaVerify]
  exact (eufCma_vendorVerify_iff_totalReject.mp hEuf) pk msg sig

/-- At `withVendorEcdsa`, `verifyImpl` is the constant-`false` function. -/
theorem withVendorEcdsa_verifyImpl_false (M₀ : PrimitiveModel)
    (hEuf : EufCma vendorVerify) (pk : PubKey) (msg : ByteArray)
    (sig : EcdsaSig) :
    verifyImpl sig.bytes pk.bytes msg = false := by
  simpa [withVendorEcdsa_ecdsaVerify, vendorVerify] using
    withVendorEcdsa_totalReject M₀ hEuf pk msg sig

/-- The checked funding predicate is always false at `withVendorEcdsa`. -/
theorem withVendorEcdsa_no_funding (M₀ : PrimitiveModel)
    (hEuf : EufCma vendorVerify) (key : PubKey) (tx : ByteArray)
    (sig : EcdsaSig) :
    verifyFundingChecked (withVendorEcdsa M₀ hEuf) key tx sig = false := by
  unfold verifyFundingChecked verifyFunding
  rw [withVendorEcdsa_totalReject M₀ hEuf]
  simp

/-- The vendor-side funding predicate is unsatisfiable at the concrete
model. -/
theorem withVendorEcdsa_fundingValidVendor_false (M₀ : PrimitiveModel)
    (hEuf : EufCma vendorVerify) (key : PubKey) (tx : ByteArray)
    (sig : EcdsaSig) :
    ¬ fundingValidVendor key tx sig := by
  intro hv
  unfold fundingValidVendor at hv
  have hf := withVendorEcdsa_verifyImpl_false M₀ hEuf key (fundingTag ++ tx) sig
  rw [hf] at hv
  exact Bool.false_ne_true hv.2

/-- The protocol-level `funding_signed` validity predicate is unsatisfiable at
`withVendorEcdsa`: the Wave-8 bridge is true but vacuous at this instance. -/
theorem withVendorEcdsa_fundingSignedValid_false (M₀ : PrimitiveModel)
    (hEuf : EufCma vendorVerify) (key : PubKey) (tx : ByteArray)
    (m : LnLean.Protocol.FundingSigned) :
    ¬ LnLean.Proofs.WaveE.E19.fundingSignedValid
        (withVendorEcdsa M₀ hEuf) key tx m := by
  intro hv
  change verifyFundingChecked (withVendorEcdsa M₀ hEuf) key tx m.signature = true at hv
  rw [withVendorEcdsa_no_funding] at hv
  exact Bool.false_ne_true hv

/-- The hypothesis of the Wave-8 funding message-binding theorem is
unsatisfiable at the constructed model.  The theorem remains true, but no
funding signature reaches it. -/
theorem withVendorEcdsa_funding_hypothesis_false (M₀ : PrimitiveModel)
    (hEuf : EufCma vendorVerify) {key : PubKey} {tx : ByteArray}
    {sig : EcdsaSig} :
    verifyImpl sig.bytes key.bytes (fundingTag ++ tx) = true → False := by
  intro h
  have hf := withVendorEcdsa_verifyImpl_false M₀ hEuf key (fundingTag ++ tx) sig
  rw [hf] at h
  exact Bool.false_ne_true h

/-- Packaged statement: the Wave-8 bridge and its total-rejection
consequence, at the same instance. -/
theorem withVendorEcdsa_bridge_and_totalReject (M₀ : PrimitiveModel)
    (hEuf : EufCma vendorVerify) :
    VendorEcdsaBridge (withVendorEcdsa M₀ hEuf) ∧
      ∀ (pk : PubKey) (msg : ByteArray) (sig : EcdsaSig),
        (withVendorEcdsa M₀ hEuf).ecdsaVerify pk msg sig = false :=
  ⟨withVendorEcdsa_bridge M₀ hEuf,
    withVendorEcdsa_totalReject M₀ hEuf⟩

/-! ## 4. The strongest faithful contract at the concrete verifier

Byte-level `EufCma` is unattainable.  The property the concrete interface can
actually support is *reduced-message* binding: the verifier sees only
`bytesToNatBE msg % n`, so one signature can at most bind that scalar.
-/

/-- Reduced-message binding: any two accepted messages have the same scalar
modulo the group order.  This is the exact message content visible to
`verifyImpl`. -/
def ResidueBinding {Sig : Type} (verify : PubKey → ByteArray → Sig → Bool) : Prop :=
  ∀ (pk : PubKey) (m₁ m₂ : ByteArray) (s : Sig),
    verify pk m₁ s = true → verify pk m₂ s = true →
      bytesToNatBE m₁ % n = bytesToNatBE m₂ % n

/-- Byte-level binding implies reduced-message binding. -/
theorem residueBinding_of_eufCma {Sig : Type}
    {verify : PubKey → ByteArray → Sig → Bool} (h : EufCma verify) :
    ResidueBinding verify := by
  intro pk m₁ m₂ s h₁ h₂
  rw [h pk m₁ m₂ s h₁ h₂]

/-- Reduced-message binding transfers across the pointwise bridge exactly. -/
theorem residueBinding_iff_vendor (M : PrimitiveModel)
    (h : VendorEcdsaBridge M) :
    ResidueBinding M.ecdsaVerify ↔ ResidueBinding vendorVerify := by
  constructor
  · intro hr pk m₁ m₂ s h₁ h₂
    apply hr pk m₁ m₂ s
    · rw [h pk m₁ s]; exact h₁
    · rw [h pk m₂ s]; exact h₂
  · intro hr pk m₁ m₂ s h₁ h₂
    apply hr pk m₁ m₂ s
    · rw [← h pk m₁ s]; exact h₁
    · rw [← h pk m₂ s]; exact h₂

/-- The strongest faithful contract available at the concrete verifier:
reduced-message binding plus key binding.  Both are explicit hypotheses; no
message-binding content beyond the reduced scalar is claimed. -/
def VendorEcdsaContract : Prop :=
  ResidueBinding vendorVerify ∧ KeyBinding vendorVerify

/-- Projection: the contract carries reduced-message binding. -/
theorem vendorEcdsaContract_residueBinding (h : VendorEcdsaContract) :
    ResidueBinding vendorVerify := h.1

/-- Projection: the contract carries key binding, independently. -/
theorem vendorEcdsaContract_keyBinding (h : VendorEcdsaContract) :
    KeyBinding vendorVerify := h.2

/-- The contract is satisfied by a total-rejecting verifier.  This is the
vacuous boundary, not the intended use. -/
theorem vendorEcdsaContract_of_totalReject
    (h : ∀ (pk : PubKey) (msg : ByteArray) (sig : EcdsaSig),
      verifyImpl sig.bytes pk.bytes msg = false) :
    VendorEcdsaContract := by
  constructor
  · intro pk m₁ m₂ s h₁ h₂
    have hf : vendorVerify pk m₁ s = false := h pk m₁ s
    rw [hf] at h₁
    exact (Bool.false_ne_true h₁).elim
  · intro pk₁ pk₂ m s h₁ h₂
    have hf : vendorVerify pk₁ m s = false := h pk₁ m s
    rw [hf] at h₁
    exact (Bool.false_ne_true h₁).elim

/-- **Exact characterization of the C3-plus-contract case.**  Asking for C3
and the faithful contract together is exactly asking for total rejection plus
key binding.  There is no intermediate non-vacuous point. -/
theorem eufCma_and_contract_iff :
    EufCma vendorVerify ∧ VendorEcdsaContract ↔
      (∀ (pk : PubKey) (msg : ByteArray) (sig : EcdsaSig),
        vendorVerify pk msg sig = false) ∧ KeyBinding vendorVerify := by
  constructor
  · rintro ⟨he, hc⟩
    exact ⟨eufCma_vendorVerify_iff_totalReject.mp he, hc.2⟩
  · rintro ⟨htot, hkb⟩
    have hr : ResidueBinding vendorVerify :=
      (vendorEcdsaContract_of_totalReject
        (fun pk msg sig => htot pk msg sig)).1
    have hc : VendorEcdsaContract := And.intro hr hkb
    exact And.intro (eufCma_vendorVerify_iff_totalReject.mpr htot) hc

/-- Funding-domain consequence of reduced-message binding: one signature
binds the reduced funding-tagged value, not the transaction bytes. -/
theorem residueBinding_vendor_funding_bound
    (h : ResidueBinding vendorVerify) {key : PubKey} {m₁ m₂ : ByteArray}
    {sig : EcdsaSig}
    (h₁ : verifyImpl sig.bytes key.bytes (fundingTag ++ m₁) = true)
    (h₂ : verifyImpl sig.bytes key.bytes (fundingTag ++ m₂) = true) :
    bytesToNatBE (fundingTag ++ m₁) % n =
      bytesToNatBE (fundingTag ++ m₂) % n :=
  h key _ _ sig h₁ h₂

/-- The same bound under the full contract. -/
theorem vendorEcdsaContract_funding_bound (h : VendorEcdsaContract)
    {key : PubKey} {m₁ m₂ : ByteArray} {sig : EcdsaSig}
    (h₁ : verifyImpl sig.bytes key.bytes (fundingTag ++ m₁) = true)
    (h₂ : verifyImpl sig.bytes key.bytes (fundingTag ++ m₂) = true) :
    bytesToNatBE (fundingTag ++ m₁) % n =
      bytesToNatBE (fundingTag ++ m₂) % n :=
  residueBinding_vendor_funding_bound h.1 h₁ h₂

/-! ## 5. Strictness and consistency of the reduced-message contract -/

/-- A verifier that accepts exactly the messages reducing to `0`.  It ignores
the key and signature, and is used only to separate residue binding from
byte-level binding and from key binding. -/
def residueZeroVerify : PubKey → ByteArray → EcdsaSig → Bool :=
  fun _ m _ => decide (bytesToNatBE m % n = 0)

/-- Residue binding does hold for `residueZeroVerify`. -/
theorem residueBinding_residueZeroVerify : ResidueBinding residueZeroVerify := by
  intro pk m₁ m₂ s h₁ h₂
  simp only [residueZeroVerify, decide_eq_true_eq] at h₁ h₂
  rw [h₁, h₂]

/-- Residue binding does not imply byte-level binding: `residueZeroVerify`
accepts both the empty message and a one-byte zero message. -/
theorem not_eufCma_residueZeroVerify : ¬ EufCma residueZeroVerify := by
  intro h
  have hEq : ByteArray.empty = ByteArray.mk #[0] :=
    h ⟨ByteArray.empty⟩ ByteArray.empty (ByteArray.mk #[0]) ⟨ByteArray.empty⟩
      (by decide) (by decide)
  have hs := congrArg ByteArray.size hEq
  exact absurd hs (by decide)

/-- The reduced-message contract is strictly weaker than byte-level C3. -/
theorem residueBinding_not_eufCma :
    ∃ verify : PubKey → ByteArray → EcdsaSig → Bool,
      ResidueBinding verify ∧ ¬ EufCma verify :=
  ⟨residueZeroVerify, residueBinding_residueZeroVerify,
    not_eufCma_residueZeroVerify⟩

/-- Residue binding does not imply key binding; `residueZeroVerify` ignores
the key. -/
theorem not_keyBinding_residueZeroVerify : ¬ KeyBinding residueZeroVerify := by
  intro hkb
  have hEq : (⟨ByteArray.empty⟩ : PubKey) = ⟨ByteArray.mk #[0]⟩ :=
    hkb ⟨ByteArray.empty⟩ ⟨ByteArray.mk #[0]⟩ ByteArray.empty ⟨ByteArray.empty⟩
      (by decide) (by decide)
  have hs := congrArg (fun p : PubKey => p.bytes.size) hEq
  exact absurd hs (by decide)

/-- Residue binding and key binding are independent hypotheses. -/
theorem residueBinding_not_keyBinding :
    ∃ verify : PubKey → ByteArray → EcdsaSig → Bool,
      ResidueBinding verify ∧ ¬ KeyBinding verify :=
  ⟨residueZeroVerify, residueBinding_residueZeroVerify,
    not_keyBinding_residueZeroVerify⟩

/-- A verifier accepting exactly one key/message/signature point.  This is a
consistency witness for the contract: it has residue binding, key binding,
and at least one acceptance, so the contract is not vacuous as a property
set.  (It is not the vendor verifier; the concrete instance remains the
subject of the obstruction above.) -/
def pointVerify (pk₀ : PubKey) (m₀ : ByteArray) (s₀ : EcdsaSig) :
    PubKey → ByteArray → EcdsaSig → Bool :=
  fun pk m s =>
    decide (pk.bytes = pk₀.bytes) && decide (m = m₀) &&
      decide (s.bytes = s₀.bytes)

/-- The point verifier accepts its own point. -/
theorem pointVerify_accepts (pk₀ : PubKey) (m₀ : ByteArray) (s₀ : EcdsaSig) :
    pointVerify pk₀ m₀ s₀ pk₀ m₀ s₀ = true := by
  simp [pointVerify]

/-- The point verifier is byte-level `EufCma`. -/
theorem eufCma_pointVerify (pk₀ : PubKey) (m₀ : ByteArray) (s₀ : EcdsaSig) :
    EufCma (pointVerify pk₀ m₀ s₀) := by
  intro pk m₁ m₂ s h₁ h₂
  simp only [pointVerify, Bool.and_eq_true, decide_eq_true_eq] at h₁ h₂
  rw [h₁.1.2, h₂.1.2]

/-- The point verifier is key-binding. -/
theorem keyBinding_pointVerify (pk₀ : PubKey) (m₀ : ByteArray) (s₀ : EcdsaSig) :
    KeyBinding (pointVerify pk₀ m₀ s₀) := by
  intro pk₁ pk₂ m s h₁ h₂
  simp only [pointVerify, Bool.and_eq_true, decide_eq_true_eq] at h₁ h₂
  exact congrArg (fun b : ByteArray => ({ bytes := b } : PubKey))
    (h₁.1.1.trans h₂.1.1.symm)

/-- The reduced-message contract plus key binding is consistent with
acceptance: the abstract point verifier realizes it.  This rules out the
reading that `VendorEcdsaContract` is vacuous for structural reasons; the
vacuous case is specific to `verifyImpl`'s mod-`n` message reduction. -/
theorem contract_consistent_with_acceptance :
    ∃ verify : PubKey → ByteArray → EcdsaSig → Bool,
      ResidueBinding verify ∧ KeyBinding verify ∧
        ∃ (pk : PubKey) (msg : ByteArray) (sig : EcdsaSig),
          verify pk msg sig = true := by
  refine ⟨pointVerify ⟨ByteArray.empty⟩ ByteArray.empty ⟨ByteArray.empty⟩,
    ?_, ?_, ?_⟩
  · exact residueBinding_of_eufCma (eufCma_pointVerify _ _ _)
  · exact keyBinding_pointVerify _ _ _
  · exact ⟨_, _, _, pointVerify_accepts _ _ _⟩

/-! ## 6. Conditional extraction and the digest-domain boundary

Reduced-message binding yields transaction equality only if the tagged
encoding is injective modulo `n`.  That side condition is *not* automatic on
`ByteArray`: two distinct 33-byte messages shifted by exactly `n` collide
under the funding tag.
-/

/-- The missing domain condition: the funding-tagged value determines the
untagged transaction bytes modulo `n`. -/
def DigestBindsMod (tag : ByteArray) : Prop :=
  ∀ m₁ m₂ : ByteArray,
    bytesToNatBE (tag ++ m₁) % n = bytesToNatBE (tag ++ m₂) % n → m₁ = m₂

/-- **Conditional extraction.**  Under reduced-message binding and a
digest-injectivity side condition, one signature binds the transaction bytes,
not merely their reduced value. -/
theorem residueBinding_vendor_funding_eq_of_digestBinds
    (h : ResidueBinding vendorVerify) (ht : DigestBindsMod fundingTag)
    {key : PubKey} {m₁ m₂ : ByteArray} {sig : EcdsaSig}
    (h₁ : verifyImpl sig.bytes key.bytes (fundingTag ++ m₁) = true)
    (h₂ : verifyImpl sig.bytes key.bytes (fundingTag ++ m₂) = true) :
    m₁ = m₂ :=
  ht m₁ m₂ (residueBinding_vendor_funding_bound h h₁ h₂)

/-- The same extraction under the full contract. -/
theorem vendorEcdsaContract_funding_eq_of_digestBinds
    (h : VendorEcdsaContract) (ht : DigestBindsMod fundingTag)
    {key : PubKey} {m₁ m₂ : ByteArray} {sig : EcdsaSig}
    (h₁ : verifyImpl sig.bytes key.bytes (fundingTag ++ m₁) = true)
    (h₂ : verifyImpl sig.bytes key.bytes (fundingTag ++ m₂) = true) :
    m₁ = m₂ :=
  residueBinding_vendor_funding_eq_of_digestBinds h.1 ht h₁ h₂

/-- The 33-byte big-endian encoding of the secp256k1 group order: a leading
zero byte followed by the 32-byte value of `n`.  Its big-endian value is `n`. -/
def nBytes33 : ByteArray :=
  ByteArray.mk #[
    0x00, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe, 0xba,
    0xae, 0xdc, 0xe6, 0xaf, 0x48, 0xa0, 0x3b, 0xbf, 0xd2,
    0x5e, 0x8c, 0xd0, 0x36, 0x41, 0x41]

/-- The encoding is 33 bytes. -/
theorem nBytes33_size : nBytes33.size = 33 := by decide

/-- The encoding has value exactly `n`. -/
theorem bytesToNatBE_nBytes33 : bytesToNatBE nBytes33 = n := by decide

/-- It is not the all-zero 33-byte string. -/
theorem nBytes33_ne_zeros33 : nBytes33 ≠ zeros 33 := by decide

/-- Two distinct 33-byte messages whose funding-tagged values are congruent
modulo `n`: the all-zero message and the 33-byte encoding of `n`. -/
theorem fundingTag_digest_collision :
    bytesToNatBE (fundingTag ++ zeros 33) % n =
      bytesToNatBE (fundingTag ++ nBytes33) % n := by decide

/-- **The digest side condition fails for the funding tag.**  The tagged
residue map is not injective on `ByteArray`, so reduced-message binding cannot
be upgraded to byte-level transaction binding without restricting the
encoding domain. -/
theorem not_digestBindsMod_fundingTag : ¬ DigestBindsMod fundingTag := by
  intro h
  have heq : zeros 33 = nBytes33 := h (zeros 33) nBytes33 fundingTag_digest_collision
  exact nBytes33_ne_zeros33 heq.symm

/-- The failure is witnessed by a concrete distinct pair. -/
theorem fundingTag_digest_collision_witness :
    ∃ m₁ m₂ : ByteArray, m₁ ≠ m₂ ∧
      bytesToNatBE (fundingTag ++ m₁) % n =
        bytesToNatBE (fundingTag ++ m₂) % n :=
  ⟨zeros 33, nBytes33, nBytes33_ne_zeros33.symm,
    fundingTag_digest_collision⟩

end LnLean.Proofs.Bitcoin.EcdsaConcreteTargets
