import Bitcoin.Crypto.Ecdsa.Verify
import Bitcoin.Crypto.Ecdsa.Der
import Bitcoin.Crypto.Seam.Der
import LnLean.Proofs.Crypto.EcdsaProps
import LnLean.Proofs.Bitcoin.SequenceContextTargets
import LnLean.Proofs.WaveE.E19

/-!
# Bridging the abstract ECDSA seam to the concrete vendored verifier

Wave 8 (lane `S8-L1-EC-BRIDGE`) closes the *implementation* half of the
abstract ECDSA boundary recorded in `L1-01` / `L1-07`.  The Lightning model
has a single opaque verifier field

```lean
M.ecdsaVerify : PubKey → ByteArray → EcdsaSig → Bool
```

while the vendored Bitcoin interpreter uses the concrete lax secp256k1
verifier

```lean
Bitcoin.Crypto.Ecdsa.Verify.verifyImpl : ByteArray → ByteArray → ByteArray → Bool
```

whose argument order is `verifyImpl sig pk msg32` (`Ecdsa/Verify.lean:82`,
pinned by the vendor comments: `verifyLax sig pubKey msg32`, mirroring
`CPubKey::Verify(hash, sig)`).  This module makes the seam explicit:

* `vendorVerify` is `verifyImpl` re-ordered into the model's
  `PubKey → msg → sig` order.
* `VendorEcdsaBridge M` is the pointwise equality
  `M.ecdsaVerify pk msg sig = verifyImpl sig.bytes pk.bytes msg`.
  It is an *assumption about a model instance*, not a theorem about ECDSA
  security.
* `verifyImpl_eq_model` is the exact bridge equation, in both directions;
  `eufCma_iff_vendor` and `keyBinding_iff_vendor` show that the model's C3
  and key-binding hypotheses transfer to the vendor verifier exactly.
* The funding / commitment / close predicates and the checked funding
  validity condition are rewritten in terms of `verifyImpl`.
* The funding, delayed `to_local`, and revocation interpreter agreements
  (`funding_sighash_interpreters_agree`, `toLocal_sighash_interpreters_agree`,
  `toLocal_revocation_interpreters_agree`) are restated with *model-level*
  ECDSA hypotheses and conclusions at the concrete
  `checkerOf verifyImpl` / `RealChecker.realCheckerOf` seam.
* `withVendorEcdsa M₀ hEuf` is a `PrimitiveModel` whose `ecdsaVerify` is
  literally `verifyImpl`.  It can be built only by supplying
  `hEuf : EufCma vendorVerify`; collision resistance (C1) and every other
  primitive field are inherited from `M₀` unchanged.
* `fundingSignedValid` (the protocol-level `funding_signed` validity
  predicate from `WaveE.E19`) is characterized as `fundingValidVendor`:
  wire shape plus `verifyImpl` on the funding-tagged transaction bytes.
  Its message binding is derived from the model's C3, and the checked
  predicate at `withVendorEcdsa` is exactly the vendor predicate.

## What is *not* claimed

There is no ECDSA security proof and no unconditional C3 theorem.  The
vendor verifier reduces the message with `bytesToNatBE msg % n` before the
group computation, so `EufCma vendorVerify` (message binding in the model's
sense, on arbitrary byte strings) is **not** a theorem; it is a genuine
extra hypothesis.  `verifyImpl_msg_congr` proves that only `msg % n` matters,
and `not_eufCma_vendorVerify_of_reduction` extracts a message-binding failure
from any accepted signature whose message has a distinct same-residue
companion.  Key binding remains independent (`KeyBinding` is not implied by
`EufCma`; the existing `eufCma_not_keyBinding` counterexample is retained
here verbatim).

Other boundaries made explicit below:

* DER: `verifyImpl` parses a *DER body* (no trailing sighash byte).  The
  interpreter strips the sighash byte before calling it
  (`ecdsaEntry_pops_hashtype`); the model's compact 64-byte wire signature is
  not DER and is rejected by `verifyImpl` (concrete counterexample).
* Pubkey: the seam's `isValidPubKey` gate checks only the header byte, while
  `verifyImpl`'s `parsePubKey` checks the length and curve equation; a
  one-byte `0x02` key passes the gate and is rejected by the verifier.
* Digest: `verifyImpl` imposes no 32-byte size gate on `msg`; on the script
  path the message is `sighashWitnessV0`, which is 32 bytes
  (`sighashWitnessV0_size`).  The 32-byte domain is therefore a property of
  the *context construction*, not of the verifier.
* Amount / sighash dispatch: the amount and hashtype reach the digest through
  `checkerOf`, exactly as in `SighashBridgeTargets`; the EC verifier sees only
  the composed digest.
-/

namespace LnLean.Proofs.Bitcoin.EcdsaBridgeTargets

set_option autoImplicit false

open Bitcoin.Data
open Bitcoin.Activation
open Bitcoin.Script.Parser
open Bitcoin.Numeric
open Bitcoin.Crypto.Ecdsa.Verify
open Bitcoin.Crypto.Ecdsa.Der (parseDerLax)
open Bitcoin.Crypto.Curve.Secp (bytesToNatBE n)
open Bitcoin.Interpreter
open LnLean
open LnLean.Crypto
open LnLean.Bitcoin
open LnLean.Bitcoin.Sighash
open LnLean.Proofs.Bitcoin.SpendTargets
open LnLean.Proofs.Bitcoin.InterpreterBridgeTargets
open LnLean.Proofs.Bitcoin.InterpreterRevocationTargets
open LnLean.Proofs.Bitcoin.SighashBridgeTargets
open LnLean.Proofs.Bitcoin.SequenceContextTargets

/-! ## 1. The model-order wrapper and the bridge -/

/-- The concrete vendored verifier with the model's argument order.
`verifyImpl` takes `(sig, pk, msg)`; the model takes `(pk, msg, sig)`. -/
def vendorVerify (pk : PubKey) (msg : ByteArray) (sig : EcdsaSig) : Bool :=
  verifyImpl sig.bytes pk.bytes msg

@[simp] theorem vendorVerify_def (pk : PubKey) (msg : ByteArray)
    (sig : EcdsaSig) :
    vendorVerify pk msg sig = verifyImpl sig.bytes pk.bytes msg := rfl

/-- **The seam bridge.**  A model instance whose abstract verifier agrees
pointwise with the concrete vendored lax secp256k1 verifier.  The arguments
are written in the model's order; `verifyImpl` receives them as
`sig.bytes`, `pk.bytes`, `msg`. -/
def VendorEcdsaBridge (M : PrimitiveModel) : Prop :=
  ∀ (pk : PubKey) (msg : ByteArray) (sig : EcdsaSig),
    M.ecdsaVerify pk msg sig = vendorVerify pk msg sig

/-- **Exact bridge / argument-order theorem.**  Under `VendorEcdsaBridge M`,
the concrete call `verifyImpl sig pk msg` is the model call
`M.ecdsaVerify pk msg sig`.  This is the shape every transfer below uses:
the vendor order `sig pk msg` on the left, the model order `pk msg sig` on
the right. -/
theorem verifyImpl_eq_model (M : PrimitiveModel) (h : VendorEcdsaBridge M)
    (pk : PubKey) (msg : ByteArray) (sig : EcdsaSig) :
    verifyImpl sig.bytes pk.bytes msg = M.ecdsaVerify pk msg sig :=
  (h pk msg sig).symm

/-- Boolean face of the bridge: acceptance transfers in both directions. -/
theorem verifyImpl_true_iff_model (M : PrimitiveModel)
    (h : VendorEcdsaBridge M) (pk : PubKey) (msg : ByteArray)
    (sig : EcdsaSig) :
    verifyImpl sig.bytes pk.bytes msg = true ↔ M.ecdsaVerify pk msg sig = true := by
  rw [verifyImpl_eq_model M h]

/-- **C3 transfers exactly.**  Given the bridge, `EufCma` for the abstract
verifier is equivalent to `EufCma` for the vendor verifier.  In particular,
the `PrimitiveModel` field is neither stronger nor weaker than the concrete
message-binding statement; it is exactly that statement. -/
theorem eufCma_iff_vendor (M : PrimitiveModel) (h : VendorEcdsaBridge M) :
    EufCma M.ecdsaVerify ↔ EufCma vendorVerify := by
  constructor
  · intro he pk m₁ m₂ s h₁ h₂
    apply he pk m₁ m₂ s
    · rw [h pk m₁ s]; exact h₁
    · rw [h pk m₂ s]; exact h₂
  · intro he pk m₁ m₂ s h₁ h₂
    apply he pk m₁ m₂ s
    · rw [← h pk m₁ s]; exact h₁
    · rw [← h pk m₂ s]; exact h₂

/-- **Key binding transfers exactly** (as a hypothesis, not as a theorem
about ECDSA).  The bridge does not create or remove key binding. -/
theorem keyBinding_iff_vendor (M : PrimitiveModel) (h : VendorEcdsaBridge M) :
    KeyBinding M.ecdsaVerify ↔ KeyBinding vendorVerify := by
  constructor
  · intro hk pk₁ pk₂ m s h₁ h₂
    apply hk pk₁ pk₂ m s
    · rw [h pk₁ m s]; exact h₁
    · rw [h pk₂ m s]; exact h₂
  · intro hk pk₁ pk₂ m s h₁ h₂
    apply hk pk₁ pk₂ m s
    · rw [← h pk₁ m s]; exact h₁
    · rw [← h pk₂ m s]; exact h₂

/-! ## 2. The message-reduction boundary (why C3 is a hypothesis) -/

/-- `verifyImpl` consults the message only through `bytesToNatBE msg % n`
(libsecp256k1's `scalar_set_b32` reduction).  Messages with the same residue
modulo the group order `n` produce identical verdicts. -/
theorem verifyImpl_msg_congr (sig pk : ByteArray) {m₁ m₂ : ByteArray}
    (h : bytesToNatBE m₁ % n = bytesToNatBE m₂ % n) :
    verifyImpl sig pk m₁ = verifyImpl sig pk m₂ := by
  unfold verifyImpl
  split
  · rfl
  · split
    · rfl
    · dsimp only
      rw [h]

/-- **Sharp conditional extraction: the vendor verifier is not `EufCma` on
arbitrary byte strings.**  If one signature is accepted for `m₁`, and `m₂` is
a *distinct* message with the same value modulo `n`, then message binding
fails.  This is exactly the gap between the model's `EufCma` (byte-level
message binding) and `verifyImpl`'s mod-`n` message treatment; it is not an
ECDSA break and it does not produce a forgery. -/
theorem not_eufCma_vendorVerify_of_reduction
    {pk : PubKey} {m₁ m₂ : ByteArray} {sig : EcdsaSig}
    (hacc : vendorVerify pk m₁ sig = true) (hne : m₁ ≠ m₂)
    (hmod : bytesToNatBE m₁ % n = bytesToNatBE m₂ % n) :
    ¬ EufCma vendorVerify := by
  intro he
  have hacc₂ : vendorVerify pk m₂ sig = true := by
    show verifyImpl sig.bytes pk.bytes m₂ = true
    rw [← verifyImpl_msg_congr sig.bytes pk.bytes hmod]
    exact hacc
  exact hne (he pk m₁ m₂ sig hacc hacc₂)

/-- **Key binding is not implied by C3.**  A vendor-accepted signature under
two distinct keys refutes `KeyBinding vendorVerify`; ECDSA message binding
alone says nothing about which key accepted it.  The model-level counterexample
`eufCma_not_keyBinding` is retained in the same module. -/
theorem not_keyBinding_vendorVerify_of_two_keys
    {pk₁ pk₂ : PubKey} {msg : ByteArray} {sig : EcdsaSig}
    (hne : pk₁ ≠ pk₂)
    (h₁ : vendorVerify pk₁ msg sig = true)
    (h₂ : vendorVerify pk₂ msg sig = true) :
    ¬ KeyBinding vendorVerify := by
  intro hkb
  exact hne (hkb pk₁ pk₂ msg sig h₁ h₂)

/-- The retained model-level counterexample, restated as a single package:
`EufCma` does not imply `KeyBinding`. -/
theorem eufCma_not_keyBinding_retained :
    EufCma (singleMessageVerify ByteArray.empty) ∧
      ¬ KeyBinding (singleMessageVerify ByteArray.empty) :=
  ⟨eufCma_singleMessage ByteArray.empty,
    eufCma_not_keyBinding⟩

/-! ## 3. Model signature predicates at `verifyImpl` -/

/-- Funding-domain verification at the vendor verifier: the model's
`fundingTag`-tagged message is passed as-is, and only the argument order
changes. -/
theorem verifyFunding_eq_vendor (M : PrimitiveModel)
    (h : VendorEcdsaBridge M) (pk : PubKey) (msg : ByteArray)
    (sig : EcdsaSig) :
    verifyFunding M pk msg sig =
      verifyImpl sig.bytes pk.bytes (fundingTag ++ msg) := by
  unfold verifyFunding
  exact h pk (fundingTag ++ msg) sig

/-- Commitment-domain verification at the vendor verifier. -/
theorem verifyCommitment_eq_vendor (M : PrimitiveModel)
    (h : VendorEcdsaBridge M) (pk : PubKey) (msg : ByteArray)
    (sig : EcdsaSig) :
    verifyCommitment M pk msg sig =
      verifyImpl sig.bytes pk.bytes (commitmentTag ++ msg) := by
  unfold verifyCommitment
  exact h pk (commitmentTag ++ msg) sig

/-- Close-domain verification at the vendor verifier. -/
theorem verifyClose_eq_vendor (M : PrimitiveModel)
    (h : VendorEcdsaBridge M) (pk : PubKey) (msg : ByteArray)
    (sig : EcdsaSig) :
    verifyClose M pk msg sig =
      verifyImpl sig.bytes pk.bytes (closeTag ++ msg) := by
  unfold verifyClose
  exact h pk (closeTag ++ msg) sig

/-- The checked (wire-gated) funding predicate at the vendor verifier. -/
theorem verifyFundingChecked_eq_vendor (M : PrimitiveModel)
    (h : VendorEcdsaBridge M) (pk : PubKey) (msg : ByteArray)
    (sig : EcdsaSig) :
    verifyFundingChecked M pk msg sig =
      (wireSigOK sig.bytes &&
        verifyImpl sig.bytes pk.bytes (fundingTag ++ msg)) := by
  unfold verifyFundingChecked
  rw [verifyFunding_eq_vendor M h]

/-- The vendor-side funding signature-validity condition: the signature has
an accepted wire shape and `verifyImpl` accepts the funding-tagged
transaction.  This is the concrete counterpart of the model's
`verifyFundingChecked` / `fundingSignedValid`; the handshake record is not
needed, only its `EcdsaSig` field. -/
def fundingValidVendor (key : PubKey) (tx : ByteArray) (sig : EcdsaSig) : Prop :=
  wireSigOK sig.bytes = true ∧
    verifyImpl sig.bytes key.bytes (fundingTag ++ tx) = true

/-- `verifyFundingChecked` at the vendor verifier is exactly
`fundingValidVendor`. -/
theorem verifyFundingChecked_iff_vendor (M : PrimitiveModel)
    (h : VendorEcdsaBridge M) (key : PubKey) (tx : ByteArray)
    (sig : EcdsaSig) :
    verifyFundingChecked M key tx sig = true ↔ fundingValidVendor key tx sig := by
  rw [verifyFundingChecked_eq_vendor M h]
  unfold fundingValidVendor
  rw [Bool.and_eq_true]

/-- **Funding-record bridge.**  The protocol-level `fundingSignedValid`
predicate of `WaveE.E19` (wire shape plus checked funding-domain signature)
is, under the seam bridge, exactly the vendor-side `fundingValidVendor`
condition.  No new cryptographic hypothesis is introduced: this is the
`verifyFundingChecked` characterization read at `m.signature`. -/
theorem fundingSignedValid_iff_vendor (M : PrimitiveModel)
    (h : VendorEcdsaBridge M) (fundingKey : PubKey) (fundingTx : ByteArray)
    (m : LnLean.Protocol.FundingSigned) :
    LnLean.Proofs.WaveE.E19.fundingSignedValid M fundingKey fundingTx m ↔
      fundingValidVendor fundingKey fundingTx m.signature :=
  verifyFundingChecked_iff_vendor M h fundingKey fundingTx m.signature

/-- **Message binding at the vendor verifier, conditional on the model's C3.**
Under the bridge and `EufCma M.ecdsaVerify`, one signature cannot accept two
distinct funding-tagged transactions.  This is the transfer of
`verifyFunding_message_bound` to `verifyImpl`. -/
theorem verifyImpl_funding_message_bound (M : PrimitiveModel)
    (h : VendorEcdsaBridge M) (hM : EufCma M.ecdsaVerify)
    {pk : PubKey} {m₁ m₂ : ByteArray} {sig : EcdsaSig}
    (h₁ : verifyImpl sig.bytes pk.bytes (fundingTag ++ m₁) = true)
    (h₂ : verifyImpl sig.bytes pk.bytes (fundingTag ++ m₂) = true) :
    m₁ = m₂ := by
  have h₁' : verifyFunding M pk m₁ sig = true := by
    rw [verifyFunding_eq_vendor M h]; exact h₁
  have h₂' : verifyFunding M pk m₂ sig = true := by
    rw [verifyFunding_eq_vendor M h]; exact h₂
  exact verifyFunding_message_bound M hM h₁' h₂'

/-- **Funding-record message binding at the vendor verifier.**  Under the
bridge and the model's C3, one `funding_signed` signature cannot be valid for
two distinct funding transactions.  This is the `E19` binding statement
transferred through `verifyImpl`. -/
theorem fundingSignedValid_vendor_binds_tx (M : PrimitiveModel)
    (h : VendorEcdsaBridge M) (hM : EufCma M.ecdsaVerify)
    {fundingKey : PubKey} {tx₁ tx₂ : ByteArray}
    {m : LnLean.Protocol.FundingSigned}
    (h₁ : LnLean.Proofs.WaveE.E19.fundingSignedValid M fundingKey tx₁ m)
    (h₂ : LnLean.Proofs.WaveE.E19.fundingSignedValid M fundingKey tx₂ m) :
    tx₁ = tx₂ := by
  have hv₁ := (fundingSignedValid_iff_vendor M h fundingKey tx₁ m).mp h₁
  have hv₂ := (fundingSignedValid_iff_vendor M h fundingKey tx₂ m).mp h₂
  exact verifyImpl_funding_message_bound M h hM hv₁.2 hv₂.2

/-- **Cross-domain separation at the vendor verifier.**  Under the model's
`AssumesEufCma`, one signature cannot be both a funding and a commitment
signature, for any pair of untagged messages. -/
theorem verifyImpl_no_funding_commitment_reuse (M : PrimitiveModel)
    (h : VendorEcdsaBridge M) (hM : AssumesEufCma M)
    {pk : PubKey} {m₁ m₂ : ByteArray} {sig : EcdsaSig}
    (hf : verifyImpl sig.bytes pk.bytes (fundingTag ++ m₁) = true)
    (hc : verifyImpl sig.bytes pk.bytes (commitmentTag ++ m₂) = true) :
    False := by
  have hf' : verifyFunding M pk m₁ sig = true := by
    rw [verifyFunding_eq_vendor M h]; exact hf
  have hc' : verifyCommitment M pk m₂ sig = true := by
    rw [verifyCommitment_eq_vendor M h]; exact hc
  exact no_cross_domain_reuse_funding_commitment M hM hf' hc'

/-! ## 4. Wire, DER, pubkey, and digest boundaries -/

/-- A concrete 64-byte compact signature (all zeros) — accepted by the
model's `wireSigOK` because compact acceptance is length-only. -/
theorem parseDerLax_zeros64 : parseDerLax (zeros 64) = none := by decide

/-- **The model's compact wire form is not the vendor's DER input.**  A
64-byte compact signature (which `wireSigOK` accepts) is rejected by
`verifyImpl`: the vendor expects the DER body, without the trailing sighash
byte, and the interpreter's `ecdsaEntry` performs that split before the call.
This is an implementation boundary, not a model failure: the on-chain path
always passes `sig.extract 0 (sig.size - 1)`. -/
theorem verifyImpl_compact64_zeros_false (pk msg : ByteArray) :
    verifyImpl (zeros 64) pk msg = false := by
  unfold verifyImpl
  rw [parseDerLax_zeros64]

/-- The two faces together: `wireSigOK` accepts the compact form while
`verifyImpl` rejects it. -/
theorem wireSigOK_compact64_not_vendor_accepted (pk msg : ByteArray) :
    wireSigOK (zeros 64) = true ∧
      verifyImpl (zeros 64) pk msg = false :=
  ⟨wireSigOK_accepts_compact64, verifyImpl_compact64_zeros_false pk msg⟩

/-- A header-valid but malformed compressed pubkey: one byte `0x02`. -/
def oneByteCompressedKey : ByteArray := ByteArray.mk #[0x02]

/-- The seam's `isValidPubKey` gate accepts it (it checks only the header). -/
theorem isValidPubKey_oneByteCompressedKey :
    Bitcoin.Crypto.Seam.Der.isValidPubKey oneByteCompressedKey = true := by
  decide

/-- The vendor's `parsePubKey` rejects it (it requires 33 bytes and the
curve equation). -/
theorem parsePubKey_oneByteCompressedKey :
    parsePubKey oneByteCompressedKey = none := by
  decide

/-- **The seam's pubkey gate is weaker than the vendor parser.**  A
signature with a one-byte `0x02` pubkey reaches `verifyImpl` through the
`isValidPubKey` gate and is rejected by `parsePubKey`. -/
theorem verifyImpl_oneBytePubKey_false (sig msg : ByteArray) :
    verifyImpl sig oneByteCompressedKey msg = false := by
  unfold verifyImpl
  split
  · rfl
  · rw [parsePubKey_oneByteCompressedKey]

/-- The digest consumed by the seam is a 32-byte BIP 143 digest.  This is the
only place the 32-byte precondition enters: `verifyImpl` itself accepts an
arbitrary `msg` and reduces it modulo `n`. -/
theorem seamDigest_size (tx : Bitcoin.Data.Tx) (nIn : Nat) (scriptCode : ByteArray)
    (ht : UInt32) (amount : Amount) :
    (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn scriptCode ht amount).size = 32 :=
  LnLean.Bitcoin.Sighash.sighashWitnessV0_size tx nIn scriptCode ht amount

/-! ## 5. The interpreter seam: model hypotheses, vendor checker conclusion -/

/-- **Headline seam theorem.**  For a valid pubkey and a non-empty witness
signature, the model's abstract verifier applied to the BIP 143 digest and
the DER body (the signature minus its hashtype byte) is *exactly* the
vendored `checkerOf verifyImpl` ECDSA verdict on the full witness signature.
This packages argument order, DER-body splitting, hashtype popping, the
amount, and the sighash dispatch into one equation. -/
theorem model_verify_eq_vendor_seam (M : PrimitiveModel)
    (h : VendorEcdsaBridge M) (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount)
    (sig scriptCode : ByteArray) (pk : PubKey)
    (ed : Bitcoin.Crypto.Seam.ScriptExecutionData)
    (hpk : Bitcoin.Crypto.Seam.Der.isValidPubKey pk.bytes = true)
    (hne : 0 < sig.size) :
    M.ecdsaVerify pk
        (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn scriptCode
          (hashtypeOf sig) amount)
        ⟨sig.extract 0 (sig.size - 1)⟩ =
      (checkerOf verifyImpl tx nIn amount).base.checkECDSASignature
        sig pk.bytes scriptCode .witnessV0 ed := by
  rw [checker_consumes_model_digest verifyImpl tx nIn amount sig pk.bytes
    scriptCode ed hpk hne]
  exact h pk
    (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn scriptCode
      (hashtypeOf sig) amount)
    ⟨sig.extract 0 (sig.size - 1)⟩

/-- The same seam equation at the capstone `RealChecker.realCheckerOf`, for an
in-range signing input.  This is the form the transaction-validity pipeline
consumes (`L1-07`). -/
theorem model_verify_eq_realChecker_seam (M : PrimitiveModel)
    (h : VendorEcdsaBridge M) (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount)
    (hIn : nIn < tx.vin.length)
    (sig scriptCode : ByteArray) (pk : PubKey)
    (ed : Bitcoin.Crypto.Seam.ScriptExecutionData)
    (hpk : Bitcoin.Crypto.Seam.Der.isValidPubKey pk.bytes = true)
    (hne : 0 < sig.size) :
    M.ecdsaVerify pk
        (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn scriptCode
          (hashtypeOf sig) amount)
        ⟨sig.extract 0 (sig.size - 1)⟩ =
      (Bitcoin.Capstone.RealChecker.realCheckerOf tx nIn amount).base.checkECDSASignature
        sig pk.bytes scriptCode .witnessV0 ed := by
  rw [← checkerOf_eq_realCheckerOf tx nIn amount hIn]
  exact model_verify_eq_vendor_seam M h tx nIn amount sig scriptCode pk ed hpk hne

/-! ### Funding 2-of-2

The wave-5/6 theorem `funding_sighash_interpreters_agree` is parameterized by
an arbitrary `verify`.  Instantiating it at `verifyImpl` and replacing each
hypothesis by the model-level `M.ecdsaVerify` call (via the bridge) transfers
the funding signature-validity statement to the concrete verifier. -/

theorem funding_sighash_interpreters_agree_vendor
    (M : PrimitiveModel) (h : VendorEcdsaBridge M)
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount)
    (a b : PubKey) (s1 s2 dummy : ByteArray)
    (ha : a.bytes.size = 33) (hb : b.bytes.size = 33)
    (hs1 : s1.size ≤ 520) (hs2 : s2.size ≤ 520) (hdu : dummy.size ≤ 520)
    (hpka : Bitcoin.Crypto.Seam.Der.isValidPubKey a.bytes = true)
    (hpkb : Bitcoin.Crypto.Seam.Der.isValidPubKey b.bytes = true)
    (hne1 : 0 < s1.size) (hne2 : 0 < s2.size)
    (h1 : M.ecdsaVerify a
      (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn
        (serializeOpcodes (fundingOps a b)) (hashtypeOf s1) amount)
      ⟨s1.extract 0 (s1.size - 1)⟩ = true)
    (h2 : M.ecdsaVerify b
      (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn
        (serializeOpcodes (fundingOps a b)) (hashtypeOf s2) amount)
      ⟨s2.extract 0 (s2.size - 1)⟩ = true) :
    verifyWitnessProgram 6
        [dummy, s1, s2, serializeOpcodes (fundingOps a b)] 0
        (hashSha256 (serializeOpcodes (fundingOps a b)))
        ({} : ScriptFlags) ({} : PolicyFlags)
        (checkerOf verifyImpl tx nIn amount) false = .ok ∧
      P2WSHSpend (vendorLaws (checkerOf verifyImpl tx nIn amount)
          (serializeOpcodes (fundingOps a b)))
        (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn
          (serializeOpcodes (fundingOps a b)) (hashtypeOf s1) amount)
        (hashSha256 (serializeOpcodes (fundingOps a b)))
        (serializeOpcodes (fundingOps a b)) (fundingProg a b) [s2, s1, dummy] ∧
      (checkerOf verifyImpl tx nIn amount).base.checkECDSASignature s1 a.bytes
          (serializeOpcodes (fundingOps a b)) .witnessV0
          (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true ∧
      (checkerOf verifyImpl tx nIn amount).base.checkECDSASignature s2 b.bytes
          (serializeOpcodes (fundingOps a b)) .witnessV0
          (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true := by
  have h1' : verifyImpl (s1.extract 0 (s1.size - 1)) a.bytes
      (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn
        (serializeOpcodes (fundingOps a b)) (hashtypeOf s1) amount) = true := by
    rw [verifyImpl_eq_model M h a _ ⟨s1.extract 0 (s1.size - 1)⟩]
    exact h1
  have h2' : verifyImpl (s2.extract 0 (s2.size - 1)) b.bytes
      (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn
        (serializeOpcodes (fundingOps a b)) (hashtypeOf s2) amount) = true := by
    rw [verifyImpl_eq_model M h b _ ⟨s2.extract 0 (s2.size - 1)⟩]
    exact h2
  exact funding_sighash_interpreters_agree verifyImpl tx nIn amount a b s1 s2 dummy
    ha hb hs1 hs2 hdu hpka hpkb hne1 hne2 h1' h2'

/-! ### Delayed `to_local` branch -/

theorem toLocal_delayed_sighash_interpreters_agree_vendor
    (M : PrimitiveModel) (h : VendorEcdsaBridge M)
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (n : Bitcoin.Numeric.ScriptNum)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hpk : Bitcoin.Crypto.Seam.Der.isValidPubKey delayedPaymentKey.bytes = true)
    (hne : 0 < sig.size)
    (hdec : decodeNum ({} : PolicyFlags) (delayBytes csv) 5 = .ok n)
    (hnn : 0 ≤ n)
    (hdis : Int.toNat n &&& SEQUENCE_LOCKTIME_DISABLE_FLAG = 0)
    (hseq : checkSequenceDef (locktimeEnvOf tx nIn) n = true)
    (hsig : M.ecdsaVerify delayedPaymentKey
      (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn
        (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
        (hashtypeOf sig) amount)
      ⟨sig.extract 0 (sig.size - 1)⟩ = true) :
    verifyWitnessProgram 10
        [sig, ByteArray.empty,
          serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)]
        0
        (hashSha256
          (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)))
        ({ csv := true } : ScriptFlags) ({} : PolicyFlags)
        (checkerOf verifyImpl tx nIn amount) false = .ok ∧
      P2WSHSpend (vendorLawsCSV (checkerOf verifyImpl tx nIn amount)
          (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)) n)
        (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn
          (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
          (hashtypeOf sig) amount)
        (hashSha256
          (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)))
        (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
        (toLocalProg revocationKey delayedPaymentKey csv) [zeroByte, sig] ∧
      (checkerOf verifyImpl tx nIn amount).base.checkECDSASignature sig
          delayedPaymentKey.bytes
          (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
          .witnessV0 (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true := by
  have hsig' : verifyImpl (sig.extract 0 (sig.size - 1)) delayedPaymentKey.bytes
      (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn
        (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
        (hashtypeOf sig) amount) = true := by
    rw [verifyImpl_eq_model M h delayedPaymentKey _ ⟨sig.extract 0 (sig.size - 1)⟩]
    exact hsig
  exact toLocal_sighash_interpreters_agree verifyImpl tx nIn amount
    revocationKey delayedPaymentKey csv sig n hr hd hsigsz hpk hne
    hdec hnn hdis hseq hsig'

/-! ### Revocation branch -/

theorem toLocal_revocation_interpreters_agree_vendor
    (M : PrimitiveModel) (h : VendorEcdsaBridge M)
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks) (sig : ByteArray)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hpk : Bitcoin.Crypto.Seam.Der.isValidPubKey revocationKey.bytes = true)
    (hne : 0 < sig.size)
    (hsig : M.ecdsaVerify revocationKey
      (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn
        (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
        (hashtypeOf sig) amount)
      ⟨sig.extract 0 (sig.size - 1)⟩ = true) :
    verifyWitnessProgram 10
        [sig, revocationSelector,
          serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)]
        0
        (hashSha256
          (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)))
        ({ csv := true } : ScriptFlags) ({} : PolicyFlags)
        (checkerOf verifyImpl tx nIn amount) false = .ok ∧
      P2WSHSpend (vendorLaws (checkerOf verifyImpl tx nIn amount)
          (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)))
        (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn
          (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
          (hashtypeOf sig) amount)
        (hashSha256
          (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)))
        (toLocalScriptFull revocationKey delayedPaymentKey csv).bytes
        (toLocalProg revocationKey delayedPaymentKey csv) [oneByte, sig] := by
  have hchk : (checkerOf verifyImpl tx nIn amount).base.checkECDSASignature sig
      revocationKey.bytes
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      .witnessV0 (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true := by
    rw [checker_consumes_model_digest verifyImpl tx nIn amount sig
      revocationKey.bytes
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData) hpk hne]
    rw [verifyImpl_eq_model M h revocationKey _ ⟨sig.extract 0 (sig.size - 1)⟩]
    exact hsig
  exact toLocal_revocation_interpreters_agree (checkerOf verifyImpl tx nIn amount)
    (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      (hashtypeOf sig) amount)
    revocationKey delayedPaymentKey csv sig hr hd hsigsz hchk

/-! ## 6. A `PrimitiveModel` whose verifier is `verifyImpl` -/

/-- Replace a model's abstract ECDSA verifier by the concrete vendored one.
Every other primitive field (in particular C1's `sha256_collisionResistant`)
is inherited from `M₀`.  The only new input is `EufCma vendorVerify`, i.e.
the concrete message-binding hypothesis.  This is deliberately a
*construction under an explicit hypothesis*, not a proof of ECDSA security. -/
def withVendorEcdsa (M₀ : PrimitiveModel) (hEuf : EufCma vendorVerify) :
    PrimitiveModel :=
  { M₀ with
    ecdsaVerify := vendorVerify
    ecdsa_eufCma := hEuf }

@[simp] theorem withVendorEcdsa_ecdsaVerify (M₀ : PrimitiveModel)
    (hEuf : EufCma vendorVerify) :
    (withVendorEcdsa M₀ hEuf).ecdsaVerify = vendorVerify := rfl

/-- Collision resistance (C1) is inherited unchanged. -/
theorem withVendorEcdsa_sha256_collisionResistant (M₀ : PrimitiveModel)
    (hEuf : EufCma vendorVerify) :
    CollisionResistant (withVendorEcdsa M₀ hEuf).sha256 := by
  simpa [withVendorEcdsa] using M₀.sha256_collisionResistant

/-- The concrete model's C3 field is exactly the supplied vendor `EufCma`. -/
theorem withVendorEcdsa_eufCma (M₀ : PrimitiveModel)
    (hEuf : EufCma vendorVerify) :
    EufCma (withVendorEcdsa M₀ hEuf).ecdsaVerify := hEuf

/-- The constructed model satisfies the seam bridge by construction. -/
theorem withVendorEcdsa_bridge (M₀ : PrimitiveModel)
    (hEuf : EufCma vendorVerify) :
    VendorEcdsaBridge (withVendorEcdsa M₀ hEuf) := by
  intro pk msg sig
  rfl

/-- **Funding validity at the concrete model.**  This is
`verifyFundingChecked_iff_vendor` instantiated at `withVendorEcdsa`: the
abstract model's checked funding predicate is exactly wire-shape acceptance
plus `verifyImpl` on the funding-tagged transaction.  For a `FundingSigned`
record `m`, this is the statement at `m.signature`. -/
theorem verifyFundingChecked_withVendor_iff (M₀ : PrimitiveModel)
    (hEuf : EufCma vendorVerify) (key : PubKey) (tx : ByteArray)
    (sig : EcdsaSig) :
    verifyFundingChecked (withVendorEcdsa M₀ hEuf) key tx sig = true ↔
      fundingValidVendor key tx sig :=
  verifyFundingChecked_iff_vendor (withVendorEcdsa M₀ hEuf)
    (withVendorEcdsa_bridge M₀ hEuf) key tx sig

/-- At the concrete model, `fundingSignedValid` is the vendor predicate for
every `funding_signed` record. -/
theorem fundingSignedValid_withVendor_iff (M₀ : PrimitiveModel)
    (hEuf : EufCma vendorVerify) (fundingKey : PubKey) (fundingTx : ByteArray)
    (m : LnLean.Protocol.FundingSigned) :
    LnLean.Proofs.WaveE.E19.fundingSignedValid (withVendorEcdsa M₀ hEuf)
        fundingKey fundingTx m ↔
      fundingValidVendor fundingKey fundingTx m.signature :=
  fundingSignedValid_iff_vendor (withVendorEcdsa M₀ hEuf)
    (withVendorEcdsa_bridge M₀ hEuf) fundingKey fundingTx m

/-- The concrete model's funding message binding, with the C3 field as the
only cryptographic input. -/
theorem withVendor_verifyImpl_funding_message_bound (M₀ : PrimitiveModel)
    (hEuf : EufCma vendorVerify) {key : PubKey} {m₁ m₂ : ByteArray}
    {sig : EcdsaSig}
    (h₁ : verifyImpl sig.bytes key.bytes (fundingTag ++ m₁) = true)
    (h₂ : verifyImpl sig.bytes key.bytes (fundingTag ++ m₂) = true) :
    m₁ = m₂ :=
  verifyImpl_funding_message_bound (withVendorEcdsa M₀ hEuf)
    (withVendorEcdsa_bridge M₀ hEuf) hEuf h₁ h₂

end LnLean.Proofs.Bitcoin.EcdsaBridgeTargets
