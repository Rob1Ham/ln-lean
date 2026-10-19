# S9-L1-EC-UNCONDITIONAL — concrete ECDSA targets and the C3 vacuity boundary

**Lane:** `S9-L1-EC-UNCONDITIONAL`
**Issues:** `L1-01`, `L1-07`
**Branch / base:** `repair/integrated` at `50e8b5c`
**Status:** complete (scoped build + axiom audit clean)
**Owned files created:** `LnLean/Proofs/Bitcoin/EcdsaConcreteTargets.lean`,
`agents/reports/swarm9/S9-L1-EC-UNCONDITIONAL.md`
**Files edited outside the owned set:** none. No Git write, commit, or push.
No core patch was applied; the additive model lives in the owned module and
the proposed core patch is recorded in §7.

---

## 1. Objective

Wave 8 (`EcdsaBridgeTargets`) introduced the pointwise seam

```lean
def vendorVerify (pk : PubKey) (msg : ByteArray) (sig : EcdsaSig) : Bool :=
  verifyImpl sig.bytes pk.bytes msg

def VendorEcdsaBridge (M : PrimitiveModel) : Prop :=
  ∀ pk msg sig, M.ecdsaVerify pk msg sig = vendorVerify pk msg sig
```

and the concrete model

```lean
def withVendorEcdsa (M₀ : PrimitiveModel) (hEuf : EufCma vendorVerify) : PrimitiveModel
```

The wave-9 question is whether a concrete `verifyImpl` instance can
**satisfy or replace** `VendorEcdsaBridge`, or whether the abstract seam is
unavoidable.  The answer must keep `EufCma` and `KeyBinding` explicit, must
not claim computational ECDSA security, and must not claim unconditional
consensus.

## 2. Answer in one paragraph

The bridge is satisfiable, but **only vacuously**.  `verifyImpl` reads the
message through `bytesToNatBE msg % n`; prepending a zero byte changes the
byte string but not the verdict.  Consequently the model's byte-level
`EufCma` field at the vendor verifier is *equivalent to total rejection*:
`EufCma vendorVerify ↔ ∀ pk msg sig, verifyImpl sig.bytes pk.bytes msg = false`.
Because every `PrimitiveModel` carries `M.ecdsa_eufCma`, **every** model
satisfying the pointwise bridge is the constant-`false` verifier
(`bridged_model_totalReject`), and no bridged model accepts any signature
(`no_bridged_nontrivial_model`).  A bridged model exists exactly when the
concrete verifier is total-rejecting
(`exists_bridged_model_iff_totalReject`).  The wave-8 `withVendorEcdsa`
model is therefore the total-rejecting model: its checked funding predicate
is always `false` and `fundingSignedValid` is unsatisfiable
(`withVendorEcdsa_no_funding`, `withVendorEcdsa_fundingSignedValid_false`).
The obstruction is the mismatch between the untyped `ByteArray` message
domain and the vendor scalar reduction, not an ECDSA break.  The strongest
faithful property of the concrete interface is reduced-message binding
(`ResidueBinding`), packaged with key binding as `VendorEcdsaContract`; it is
strictly weaker than `EufCma`, transfers across the bridge exactly, and is
consistent with acceptance.  Upgrading residue binding to byte-level
transaction equality needs a digest-injectivity side condition
(`DigestBindsMod fundingTag`) which is **false** on the untyped domain
(`not_digestBindsMod_fundingTag`), so a faithful repair must restrict the
transaction/digest encoding, not merely weaken C3.

## 3. Exact claims

All names below are in namespace
`LnLean.Proofs.Bitcoin.EcdsaConcreteTargets`; the prefix is omitted inside
this section for readability.

### 3.1 The zero-padding obstruction

```lean
def zeroPad (b : ByteArray) : ByteArray :=
  ByteArray.mk (0 :: b.data.toList).toArray

theorem zeroPad_size (b : ByteArray) : (zeroPad b).size = b.size + 1
theorem zeroPad_ne (b : ByteArray) : zeroPad b ≠ b
theorem bytesToNatBE_zeroPad (b : ByteArray) :
    bytesToNatBE (zeroPad b) = bytesToNatBE b
theorem zeroPad_modEq (b : ByteArray) :
    bytesToNatBE (zeroPad b) % n = bytesToNatBE b % n
theorem verifyImpl_zeroPad (sig pk b : ByteArray) :
    verifyImpl sig pk (zeroPad b) = verifyImpl sig pk b
```

General form, independent of the concrete curve:

```lean
theorem eufCma_iff_totalReject_of_zeroPad
    (v : PubKey → ByteArray → EcdsaSig → Bool)
    (hpad : ∀ pk msg sig, v pk (zeroPad msg) sig = v pk msg sig) :
    EufCma v ↔ ∀ pk msg sig, v pk msg sig = false
```

### 3.2 The concrete obstruction and its consequences

```lean
def AcceptsSome (v : PubKey → ByteArray → EcdsaSig → Bool) : Prop :=
  ∃ pk msg sig, v pk msg sig = true

theorem eufCma_vendorVerify_iff_totalReject :
    EufCma vendorVerify ↔
      ∀ pk msg sig, vendorVerify pk msg sig = false

theorem not_eufCma_vendorVerify_iff_accepts :
    ¬ EufCma vendorVerify ↔ AcceptsSome vendorVerify

theorem not_eufCma_vendorVerify_of_accepts
    (hacc : ∃ pk msg sig, verifyImpl sig.bytes pk.bytes msg = true) :
    ¬ EufCma vendorVerify
```

The bridge consequences are unconditional (they use the mandatory
`M.ecdsa_eufCma` field, not an extra hypothesis):

```lean
theorem bridge_eufCma_iff_verifyImpl_totalReject
    (M : PrimitiveModel) (h : VendorEcdsaBridge M) :
    EufCma M.ecdsaVerify ↔
      ∀ pk msg sig, verifyImpl sig.bytes pk.bytes msg = false

theorem bridged_model_totalReject
    (M : PrimitiveModel) (h : VendorEcdsaBridge M) :
    ∀ pk msg sig, M.ecdsaVerify pk msg sig = false

theorem bridged_model_no_accept
    (M : PrimitiveModel) (h : VendorEcdsaBridge M) :
    ¬ ∃ pk msg sig, M.ecdsaVerify pk msg sig = true

theorem no_bridged_nontrivial_model :
    ¬ ∃ M : PrimitiveModel,
        VendorEcdsaBridge M ∧
          ∃ pk msg sig, M.ecdsaVerify pk msg sig = true

theorem exists_bridged_model_iff_totalReject (M₀ : PrimitiveModel) :
    (∃ M : PrimitiveModel, VendorEcdsaBridge M) ↔
      ∀ pk msg sig, verifyImpl sig.bytes pk.bytes msg = false
```

`exists_bridged_model_iff_totalReject` is the exact answer to the lane
question: the pointwise bridge is realizable precisely in the total-rejecting
case.  The backward direction is the wave-8 construction; the forward
direction is the obstruction.

### 3.3 The wave-8 concrete model is the vacuous instance

```lean
theorem withVendorEcdsa_totalReject
    (M₀ : PrimitiveModel) (hEuf : EufCma vendorVerify) :
    ∀ pk msg sig, (withVendorEcdsa M₀ hEuf).ecdsaVerify pk msg sig = false

theorem withVendorEcdsa_verifyImpl_false
    (M₀ : PrimitiveModel) (hEuf : EufCma vendorVerify) :
    ∀ pk msg sig, verifyImpl sig.bytes pk.bytes msg = false

theorem withVendorEcdsa_no_funding
    (M₀ : PrimitiveModel) (hEuf : EufCma vendorVerify)
    (key : PubKey) (tx : ByteArray) (sig : EcdsaSig) :
    verifyFundingChecked (withVendorEcdsa M₀ hEuf) key tx sig = false

theorem withVendorEcdsa_fundingValidVendor_false
    (M₀ : PrimitiveModel) (hEuf : EufCma vendorVerify)
    (key : PubKey) (tx : ByteArray) (sig : EcdsaSig) :
    ¬ fundingValidVendor key tx sig

theorem withVendorEcdsa_fundingSignedValid_false
    (M₀ : PrimitiveModel) (hEuf : EufCma vendorVerify)
    (key : PubKey) (tx : ByteArray) (m : LnLean.Protocol.FundingSigned) :
    ¬ LnLean.Proofs.WaveE.E19.fundingSignedValid
        (withVendorEcdsa M₀ hEuf) key tx m

theorem withVendorEcdsa_funding_hypothesis_false
    (M₀ : PrimitiveModel) (hEuf : EufCma vendorVerify) :
    verifyImpl sig.bytes key.bytes (fundingTag ++ tx) = true → False

theorem withVendorEcdsa_bridge_and_totalReject
    (M₀ : PrimitiveModel) (hEuf : EufCma vendorVerify) :
    VendorEcdsaBridge (withVendorEcdsa M₀ hEuf) ∧
      ∀ pk msg sig, (withVendorEcdsa M₀ hEuf).ecdsaVerify pk msg sig = false
```

This does **not** refute the wave-8 theorem
`withVendor_verifyImpl_funding_message_bound`; that theorem is true.  It
shows that its premise is unsatisfiable at `withVendorEcdsa`, so the theorem
is vacuous at the concrete instance.

### 3.4 The strongest faithful contract

```lean
def ResidueBinding {Sig : Type}
    (verify : PubKey → ByteArray → Sig → Bool) : Prop :=
  ∀ pk m₁ m₂ s,
    verify pk m₁ s = true → verify pk m₂ s = true →
      bytesToNatBE m₁ % n = bytesToNatBE m₂ % n

theorem residueBinding_of_eufCma {Sig : Type}
    {verify : PubKey → ByteArray → Sig → Bool} (h : EufCma verify) :
    ResidueBinding verify

theorem residueBinding_iff_vendor (M : PrimitiveModel)
    (h : VendorEcdsaBridge M) :
    ResidueBinding M.ecdsaVerify ↔ ResidueBinding vendorVerify

def VendorEcdsaContract : Prop :=
  ResidueBinding vendorVerify ∧ KeyBinding vendorVerify

theorem vendorEcdsaContract_residueBinding (h : VendorEcdsaContract) :
    ResidueBinding vendorVerify
theorem vendorEcdsaContract_keyBinding (h : VendorEcdsaContract) :
    KeyBinding vendorVerify
theorem vendorEcdsaContract_of_totalReject
    (h : ∀ pk msg sig, verifyImpl sig.bytes pk.bytes msg = false) :
    VendorEcdsaContract

theorem eufCma_and_contract_iff :
    EufCma vendorVerify ∧ VendorEcdsaContract ↔
      (∀ pk msg sig, vendorVerify pk msg sig = false) ∧
        KeyBinding vendorVerify

theorem residueBinding_vendor_funding_bound
    (h : ResidueBinding vendorVerify) :
    verifyImpl sig.bytes key.bytes (fundingTag ++ m₁) = true →
    verifyImpl sig.bytes key.bytes (fundingTag ++ m₂) = true →
      bytesToNatBE (fundingTag ++ m₁) % n =
        bytesToNatBE (fundingTag ++ m₂) % n
```

`ResidueBinding` is the message content the vendor verifier can see.  The
contract is the exact non-vacuous hypothesis set; `eufCma_and_contract_iff`
shows that adding C3 to it collapses to total rejection plus key binding.

### 3.5 Strictness and consistency of the reduced-message contract

```lean
def residueZeroVerify : PubKey → ByteArray → EcdsaSig → Bool :=
  fun _ m _ => decide (bytesToNatBE m % n = 0)

theorem residueBinding_residueZeroVerify : ResidueBinding residueZeroVerify
theorem not_eufCma_residueZeroVerify : ¬ EufCma residueZeroVerify
theorem residueBinding_not_eufCma :
    ∃ verify, ResidueBinding verify ∧ ¬ EufCma verify
theorem not_keyBinding_residueZeroVerify : ¬ KeyBinding residueZeroVerify
theorem residueBinding_not_keyBinding :
    ∃ verify, ResidueBinding verify ∧ ¬ KeyBinding verify
```

The contract is not vacuous as a property set: an abstract point verifier
realizes it with an acceptance.

```lean
def pointVerify (pk₀ : PubKey) (m₀ : ByteArray) (s₀ : EcdsaSig)
    (pk : PubKey) (m : ByteArray) (s : EcdsaSig) : Bool :=
  decide (pk.bytes = pk₀.bytes) && decide (m = m₀) &&
    decide (s.bytes = s₀.bytes)

theorem pointVerify_accepts (pk₀ m₀ s₀) :
    pointVerify pk₀ m₀ s₀ pk₀ m₀ s₀ = true
theorem eufCma_pointVerify (pk₀ m₀ s₀) :
    EufCma (pointVerify pk₀ m₀ s₀)
theorem keyBinding_pointVerify (pk₀ m₀ s₀) :
    KeyBinding (pointVerify pk₀ m₀ s₀)

theorem contract_consistent_with_acceptance :
    ∃ verify, ResidueBinding verify ∧ KeyBinding verify ∧
      ∃ pk msg sig, verify pk msg sig = true
```

`pointVerify` is abstract, not `verifyImpl`; it only proves the contract
itself is structurally consistent.

### 3.6 Conditional extraction and the digest-domain boundary

```lean
def DigestBindsMod (tag : ByteArray) : Prop :=
  ∀ m₁ m₂,
    bytesToNatBE (tag ++ m₁) % n = bytesToNatBE (tag ++ m₂) % n → m₁ = m₂

theorem residueBinding_vendor_funding_eq_of_digestBinds
    (h : ResidueBinding vendorVerify) (ht : DigestBindsMod fundingTag) :
    verifyImpl sig.bytes key.bytes (fundingTag ++ m₁) = true →
    verifyImpl sig.bytes key.bytes (fundingTag ++ m₂) = true → m₁ = m₂

theorem vendorEcdsaContract_funding_eq_of_digestBinds
    (h : VendorEcdsaContract) (ht : DigestBindsMod fundingTag) :
    verifyImpl sig.bytes key.bytes (fundingTag ++ m₁) = true →
    verifyImpl sig.bytes key.bytes (fundingTag ++ m₂) = true → m₁ = m₂
```

The side condition is **not** automatic on `ByteArray`:

```lean
def nBytes33 : ByteArray :=  -- 0x00 followed by the 32-byte value of n
  ByteArray.mk #[0x00, 0xff, ..., 0x41, 0x41]

theorem nBytes33_size : nBytes33.size = 33
theorem bytesToNatBE_nBytes33 : bytesToNatBE nBytes33 = n
theorem nBytes33_ne_zeros33 : nBytes33 ≠ zeros 33
theorem fundingTag_digest_collision :
    bytesToNatBE (fundingTag ++ zeros 33) % n =
      bytesToNatBE (fundingTag ++ nBytes33) % n
theorem not_digestBindsMod_fundingTag : ¬ DigestBindsMod fundingTag
theorem fundingTag_digest_collision_witness :
    ∃ m₁ m₂, m₁ ≠ m₂ ∧
      bytesToNatBE (fundingTag ++ m₁) % n =
        bytesToNatBE (fundingTag ++ m₂) % n
```

`zeros 33` and `nBytes33` are distinct 33-byte messages; the tagged values
differ by exactly `n`, so they collide modulo `n`.  This is a property of the
untyped encoding domain, **not** a claim that two real transactions collide.

## 4. Artifacts

- `LnLean/Proofs/Bitcoin/EcdsaConcreteTargets.lean` — 629 lines, new,
  untracked.
- `agents/reports/swarm9/S9-L1-EC-UNCONDITIONAL.md` — this report.
- Not modified: `EcdsaBridgeTargets.lean`, `PrimitiveModel`/`Crypto.Model.lean`,
  `LnLean/Bitcoin/**` core files, `LnLean.lean`, `Obligations.lean`,
  `Traceability.lean`, `AxiomAudit.lean`, catalog/docs, vendor, and Git state.
  Other lanes' working-tree changes are present and untouched.

## 5. Validation

### 5.1 Scoped build

Exact command (shared lock, single thread, only the new module):

```bash
export PATH=/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Proofs.Bitcoin.EcdsaConcreteTargets
```

Result (after the final edit):

```text
✔ [60/60] Built LnLean.Proofs.Bitcoin.EcdsaConcreteTargets (1.1s)
Build completed successfully (60 jobs).
```

No full `lake build` was run.

### 5.2 Axiom audit

All 48 public theorems were checked with `#print axioms` via
`lake env lean` under the same lock.  Every theorem depends only on a subset
of `{propext, Quot.sound, Classical.choice}`.  Representative output:

```text
'eufCma_vendorVerify_iff_totalReject' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'bridged_model_totalReject' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'no_bridged_nontrivial_model' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'exists_bridged_model_iff_totalReject' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'withVendorEcdsa_fundingSignedValid_false' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'residueBinding_iff_vendor' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'eufCma_and_contract_iff' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'not_digestBindsMod_fundingTag' depends on axioms:
  [propext, Quot.sound]
'fundingTag_digest_collision' does not depend on any axioms
'bytesToNatBE_nBytes33' does not depend on any axioms
'residueBinding_of_eufCma' does not depend on any axioms
'not_eufCma_residueZeroVerify' does not depend on any axioms
```

No axiom outside the allowed set appears.

### 5.3 Forbidden-construct scan

```bash
grep -nE '\b(sorry|admit|axiom|native_decide|unsafe|implemented_by)\b' \
  LnLean/Proofs/Bitcoin/EcdsaConcreteTargets.lean
# exit 1 (no matches)
```

No `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, or
`@[implemented_by]` is used.

### 5.4 Git state

`git status --short` shows the new module and this report as untracked, plus
other lanes' pre-existing/parallel changes.  This lane ran no `git add`,
`git commit`, or `git push`.

## 6. Gaps and trust boundary

1. **No unconditional `¬ EufCma vendorVerify`.**  The equivalence
   `EufCma vendorVerify ↔ totalReject` is unconditional, but refuting the
   right side requires a mechanized accepted signature.  We did not attempt
   to evaluate a concrete secp256k1 signature in the kernel.  The refutation
   is therefore stated relative to an explicit acceptance witness
   (`not_eufCma_vendorVerify_of_accepts`, `AcceptsSome`).  The model-level
   separation `no_bridged_nontrivial_model` does not need this witness and is
   unconditional.
2. **No ECDSA security claim.**  Nothing here proves or refutes EUF-CMA,
   computational hardness, or a forgery.  The obstruction is about the
   message *representation* and the `% n` reduction, not about the curve.
3. **No real-transaction collision claim.**  `not_digestBindsMod_fundingTag`
   is a statement about arbitrary 33-byte `ByteArray`s; it does not assert
   that two valid BOLT/L1 transactions share a digest.
4. **The concrete contract is a hypothesis, not a theorem.**
   `ResidueBinding vendorVerify` and `KeyBinding vendorVerify` are not
   proved.  `VendorEcdsaContract` names exactly what a faithful concrete
   instantiation would have to supply.  `contract_consistent_with_acceptance`
   uses the abstract `pointVerify`, not `verifyImpl`.
5. **Key binding stays independent.**  `ResidueBinding` does not imply
   `KeyBinding` (`residueBinding_not_keyBinding`), and the wave-8
   `eufCma_not_keyBinding` counterexample is retained by import.  No
   signature-identifies-the-signer claim.
6. **The wave-8 concrete model is characterized, not refuted.**  Every
   theorem in `EcdsaBridgeTargets` remains true; at `withVendorEcdsa` its
   signature hypotheses are simply unsatisfiable.  This is the honest trust
   boundary the wave-8 report already flagged, now made exact.
7. **Positive-direction scope and consensus.**  Nothing here changes the
   wave-5/6/7 positive-direction P2WSH scope, the known-amount
   `TxValidation.Full` transfer, or any unconditional consensus claim.
8. **`DigestBindsMod` is not discharged.**  The conditional extraction is the
   strongest statement available without restricting the transaction
   encoding.  A canonical serializer/no-collision proof is future work.

## 7. Proposed core patch (not applied)

The additive model in the owned module is sufficient for this lane.  If the
integrator wants a *non-vacuous* concrete C3 instance, the minimal core change
is to type the ECDSA message domain in `LnLean/Crypto/Model.lean`
(currently lines 71–73 and 101–120):

```lean
-- Proposed, NOT applied.
abbrev EufCmaOn (domain : ByteArray → Prop)
    {Sig : Type} (verify : PubKey → ByteArray → Sig → Bool) : Prop :=
  ∀ (pk : PubKey) (m₁ m₂ : ByteArray) (s : Sig),
    domain m₁ → domain m₂ →
      verify pk m₁ s = true → verify pk m₂ s = true → m₁ = m₂

structure PrimitiveModel where
  ...
  ecdsaDomain : ByteArray → Prop
  ecdsaVerify : PubKey → ByteArray → EcdsaSig → Bool
  ...
  ecdsa_eufCma : EufCmaOn ecdsaDomain ecdsaVerify
```

Every existing consumer of `M.ecdsa_eufCma` would then need the two domain
hypotheses; that is a broad, cross-cutting patch and was deliberately not
attempted here.  A less invasive alternative is to keep `PrimitiveModel`
unchanged and use `VendorEcdsaContract` (`ResidueBinding` + `KeyBinding`) as
the concrete refinement contract.

Important: even `ecdsaDomain msg := msg.size = 32` only removes the
zero-padding obstruction.  It does **not** remove the mod-`n` collision
(`not_digestBindsMod_fundingTag`), because 32-byte digests can still differ by
`n`.  To recover byte-level transaction binding, the domain must be a
canonical encoding with a proved `DigestBindsMod` (or an equivalent
serializer injectivity lemma).  A size-only patch would be a fake fix.

## 8. Catalog integration recommendation

**Existing rows.**  `LN-L1-001` (funding/P2WSH/EC seam) and `LN-L1-004`
(`to_local`/EC seam) are the right rows for L1-01/L1-07.  Append the following
to both `leanTarget` strings (and to the two mirrored string lists in
`Traceability.lean`, lines 214/217 and 266/269):

```text
; LnLean.Proofs.Bitcoin.EcdsaConcreteTargets.eufCma_vendorVerify_iff_totalReject
; LnLean.Proofs.Bitcoin.EcdsaConcreteTargets.bridged_model_totalReject
; LnLean.Proofs.Bitcoin.EcdsaConcreteTargets.exists_bridged_model_iff_totalReject
; LnLean.Proofs.Bitcoin.EcdsaConcreteTargets.withVendorEcdsa_no_funding
; LnLean.Proofs.Bitcoin.EcdsaConcreteTargets.not_digestBindsMod_fundingTag
```

Do **not** change either row's `status` or upgrade its claim to
"unconditional".  The new targets are boundary/trust evidence: they show the
concrete C3 instance is vacuous at the current interface.  Update the claim
text to say that the EC boundary is now *characterized* (total rejection),
not merely assumed.

`LN-CR-002` is a relevant caveat row (commitment-domain binding under C3):
the integrator may cross-reference
`EcdsaConcreteTargets.eufCma_vendorVerify_iff_totalReject` there to record
that C3 is not instantiated non-vacuously by `verifyImpl`.  This is optional
and should not change `LN-CR-002`'s status.

**Root import.**  In `LnLean.lean`, after line 30
(`import LnLean.Proofs.Bitcoin.EcdsaBridgeTargets`), add:

```lean
import LnLean.Proofs.Bitcoin.EcdsaConcreteTargets
```

**Traceability.**  Add entries for the five theorems above and the module
string `"LnLean.Proofs.Bitcoin.EcdsaConcreteTargets"` beside the existing
`EcdsaBridgeTargets` module entry around line 499.

**Axiom audit.**  In `LnLean/Proofs/PhaseC3/AxiomAudit.lean`, add the import
and `#print axioms` lines for at least:

```text
eufCma_vendorVerify_iff_totalReject
bridged_model_totalReject
bridged_model_no_accept
no_bridged_nontrivial_model
exists_bridged_model_iff_totalReject
withVendorEcdsa_no_funding
withVendorEcdsa_fundingSignedValid_false
residueBinding_iff_vendor
eufCma_and_contract_iff
residueBinding_not_eufCma
residueBinding_not_keyBinding
not_digestBindsMod_fundingTag
```

**Docs.**  Update `docs/OPEN-ISSUES.md` `L1-01` / `L1-07` to state the exact
dichotomy: `VendorEcdsaBridge` plus C3 forces total rejection; the faithful
concrete contract is `ResidueBinding` + `KeyBinding`; `DigestBindsMod` is the
missing domain condition.  Keep both issues open (the cryptographic and
domain-repair work is not discharged).

**New obligation id.**  Not recommended in this lane.  A dedicated
`LN-CR-00x` "concrete ECDSA C3 boundary" would require coordinated edits to
the id table, traceability, obligations, audit, and generated docs; the
existing `LN-L1-001` / `LN-L1-004` evidence lists are sufficient.

## 9. Summary

- **Answer:** a concrete `verifyImpl` instance satisfies `VendorEcdsaBridge`
  only as the total-rejecting verifier.  There is no non-vacuous bridged
  `PrimitiveModel`; the obstruction is the untyped `ByteArray` message domain
  plus `bytesToNatBE msg % n`, not ECDSA security.
- **Headline theorems:** `eufCma_vendorVerify_iff_totalReject`,
  `bridged_model_totalReject`, `no_bridged_nontrivial_model`,
  `exists_bridged_model_iff_totalReject`,
  `withVendorEcdsa_fundingSignedValid_false`.
- **Faithful contract:** `ResidueBinding`, `VendorEcdsaContract`,
  `residueBinding_iff_vendor`, `eufCma_and_contract_iff`,
  `residueBinding_not_eufCma`, `residueBinding_not_keyBinding`,
  `contract_consistent_with_acceptance`.
- **Conditional extraction / boundary:** `DigestBindsMod`,
  `residueBinding_vendor_funding_eq_of_digestBinds`,
  `not_digestBindsMod_fundingTag`,
  `fundingTag_digest_collision_witness`.
- **Files:** `LnLean/Proofs/Bitcoin/EcdsaConcreteTargets.lean` (new, 629
  lines), `agents/reports/swarm9/S9-L1-EC-UNCONDITIONAL.md` (this report).
- **Validation:** scoped build 60/60, 1.1 s, RC 0; axiom audit within
  `{propext, Quot.sound, Classical.choice}`; forbidden-construct scan clean.
- **Lane status:** **complete**.  No blocker.  The only remaining work is
  integration (§8) and the explicit domain/cryptographic hypotheses (§6–§7).
