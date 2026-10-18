# S8-L1-EC-BRIDGE — bridging `PrimitiveModel.ecdsaVerify` to the vendored `verifyImpl`

**Lane:** `S8-L1-EC-BRIDGE` (`L1-01`, `L1-07`).
**Repository:** `/home/ubuntu/ln-lean-repair`.
**Base commit:** `60318ad` (shared wave-8 tree; other lanes were active).
**Verdict:** complete for the assigned scope.  The abstract verifier field is
connected to `Bitcoin.Crypto.Ecdsa.Verify.verifyImpl` by an explicit,
pointwise bridge hypothesis with the argument order `sig pk msg` on the
vendor side and `pk msg sig` on the model side.  Under that hypothesis, C3
(`EufCma`) and key binding transfer **iff**, the funding/commitment/close
predicates and the protocol-level `fundingSignedValid` predicate are
rewritten at `verifyImpl`, and the funding, delayed `to_local`, and
revocation interpreter agreements are restated with model-level ECDSA
hypotheses at `checkerOf verifyImpl` and `RealChecker.realCheckerOf`.  A
concrete `PrimitiveModel` is constructed by supplying exactly one new
hypothesis, `EufCma vendorVerify`; C1 and every other primitive field are
inherited unchanged.  There is **no** unconditional ECDSA security proof and
**no** unconditional bridge: the message-reduction extraction theorem shows
why `EufCma vendorVerify` on arbitrary byte strings is a genuine extra
assumption, not a theorem.

- Lane file (exclusive ownership, new):
  - `LnLean/Proofs/Bitcoin/EcdsaBridgeTargets.lean` — 673 lines.
  - `agents/reports/swarm8/S8-L1-EC-BRIDGE.md` — this report.
- Not modified: all other `LnLean/**` files (including
  `Protocol/Handshake.lean`, `Protocol/Messages.lean`,
  `SequenceContextTargets.lean`, `SighashBridgeTargets.lean`,
  `Obligations.lean`, `Traceability.lean`, `PhaseC3/AxiomAudit.lean`,
  `LnLean.lean`), shared docs/scripts, other lanes' files, and `vendor/**`.
  No Git write commands were run.  The new module is untracked.

## 1. Result in one paragraph

The Lightning model keeps ECDSA behind one opaque field
`M.ecdsaVerify : PubKey → ByteArray → EcdsaSig → Bool`; the vendored
interpreter calls
`verifyImpl : ByteArray → ByteArray → ByteArray → Bool` with order
`(sig, pk, msg32)` (`Bitcoin/Crypto/Ecdsa/Verify.lean:82`).  Because
`M.ecdsaVerify` is an unconstrained structure field, no theorem can identify
it with `verifyImpl` without an assumption about that particular model
instance.  This lane makes that assumption explicit and minimal:
`VendorEcdsaBridge M` is the pointwise equation between the two calls, and
`verifyImpl_eq_model` is the exact bridge equation.  The lane then proves
that the model's C3 and key-binding hypotheses are *equivalent* at the vendor
verifier, derives the mod-`n` message-reduction boundary, rewrites the
funding/commitment/close and `funding_signed` predicates, and packages the
whole interpreter seam (argument order, DER-body split, hashtype popping,
amount, BIP 143 dispatch) as one equation at `checkerOf verifyImpl` and at
`RealChecker.realCheckerOf` for in-range inputs.  Finally,
`withVendorEcdsa M₀ hEuf` is a `PrimitiveModel` whose `ecdsaVerify` is
literally `vendorVerify`; the only new input is `hEuf : EufCma vendorVerify`,
and C1 is inherited from `M₀` by
`withVendorEcdsa_sha256_collisionResistant`.

## 2. The exact bridge and argument order

```lean
def vendorVerify (pk : PubKey) (msg : ByteArray) (sig : EcdsaSig) : Bool :=
  verifyImpl sig.bytes pk.bytes msg

def VendorEcdsaBridge (M : PrimitiveModel) : Prop :=
  ∀ (pk : PubKey) (msg : ByteArray) (sig : EcdsaSig),
    M.ecdsaVerify pk msg sig = vendorVerify pk msg sig

theorem verifyImpl_eq_model (M : PrimitiveModel) (h : VendorEcdsaBridge M)
    (pk : PubKey) (msg : ByteArray) (sig : EcdsaSig) :
    verifyImpl sig.bytes pk.bytes msg = M.ecdsaVerify pk msg sig
```

Read the vendor call as `verifyImpl sig pk msg`: the first argument is the
**DER signature body**, the second the **serialized public key**, the third
the **32-byte digest**.  The model call is `M.ecdsaVerify pk msg sig`.  The
bridge is deliberately stated in the model's order and then unfolded to the
vendor order, so every transfer below has the vendor order on the left and
the model order on the right.  `verifyImpl_true_iff_model` gives the Boolean
acceptance face.

### 2.1 What makes this faithful, and what it does not say

* `VendorEcdsaBridge` is an assumption about a model instance.  It is the
  weakest statement that lets the model and the vendor verifier be used
  interchangeably; it says nothing about whether ECDSA is secure.
* `eufCma_iff_vendor` and `keyBinding_iff_vendor` show the bridge is
  *exactly* hypothesis-preserving: it neither strengthens nor weakens C3 or
  key binding.
* The concrete model `withVendorEcdsa` is built **from** a supplied
  `hEuf : EufCma vendorVerify`; it is not a proof of that hypothesis.

## 3. What is mechanized

### 3.1 Transfer of C3 and key binding

```lean
theorem eufCma_iff_vendor (M : PrimitiveModel) (h : VendorEcdsaBridge M) :
    EufCma M.ecdsaVerify ↔ EufCma vendorVerify

theorem keyBinding_iff_vendor (M : PrimitiveModel) (h : VendorEcdsaBridge M) :
    KeyBinding M.ecdsaVerify ↔ KeyBinding vendorVerify
```

Both directions are proved pointwise from the bridge; no classical reasoning
about ECDSA is used.

### 3.2 The message-reduction boundary (why C3 stays a hypothesis)

`verifyImpl` reduces the message with `bytesToNatBE msg % n` before the group
computation (libsecp256k1 `scalar_set_b32`), so it cannot distinguish
messages with the same residue modulo the secp256k1 order:

```lean
theorem verifyImpl_msg_congr (sig pk : ByteArray) {m₁ m₂ : ByteArray}
    (h : bytesToNatBE m₁ % n = bytesToNatBE m₂ % n) :
    verifyImpl sig pk m₁ = verifyImpl sig pk m₂

theorem not_eufCma_vendorVerify_of_reduction
    {pk : PubKey} {m₁ m₂ : ByteArray} {sig : EcdsaSig}
    (hacc : vendorVerify pk m₁ sig = true) (hne : m₁ ≠ m₂)
    (hmod : bytesToNatBE m₁ % n = bytesToNatBE m₂ % n) :
    ¬ EufCma vendorVerify
```

This is the sharp conditional extraction: any accepted signature whose
message has a distinct same-residue companion refutes byte-level message
binding for the vendor verifier.  It is an *implementation/domain* boundary,
not an ECDSA break and not a forgery: the two messages are the same scalar.
Consequently `EufCma vendorVerify` is genuinely an extra hypothesis in
`withVendorEcdsa`.  On the 32-byte seam digests the reduction is still
possible for values `≥ n`; the 32-byte domain alone does not remove it.
Whether the protocol ever presents two distinct byte strings with the same
residue is a separate domain-separation question, not claimed here.

Key binding is likewise independent of C3:

```lean
theorem not_keyBinding_vendorVerify_of_two_keys
    {pk₁ pk₂ : PubKey} {msg : ByteArray} {sig : EcdsaSig}
    (hne : pk₁ ≠ pk₂)
    (h₁ : vendorVerify pk₁ msg sig = true)
    (h₂ : vendorVerify pk₂ msg sig = true) :
    ¬ KeyBinding vendorVerify

theorem eufCma_not_keyBinding_retained :
    EufCma (singleMessageVerify ByteArray.empty) ∧
      ¬ KeyBinding (singleMessageVerify ByteArray.empty)
```

The existing model-level counterexample is retained verbatim, so this lane
does not silently upgrade C3 to key attribution.

### 3.3 Funding, commitment, close, and the `funding_signed` record

```lean
theorem verifyFunding_eq_vendor ... :
    verifyFunding M pk msg sig =
      verifyImpl sig.bytes pk.bytes (fundingTag ++ msg)

theorem verifyCommitment_eq_vendor ... :
    verifyCommitment M pk msg sig =
      verifyImpl sig.bytes pk.bytes (commitmentTag ++ msg)

theorem verifyClose_eq_vendor ... :
    verifyClose M pk msg sig =
      verifyImpl sig.bytes pk.bytes (closeTag ++ msg)

theorem verifyFundingChecked_eq_vendor ... :
    verifyFundingChecked M pk msg sig =
      (wireSigOK sig.bytes &&
        verifyImpl sig.bytes pk.bytes (fundingTag ++ msg))

def fundingValidVendor (key : PubKey) (tx : ByteArray) (sig : EcdsaSig) : Prop :=
  wireSigOK sig.bytes = true ∧
    verifyImpl sig.bytes key.bytes (fundingTag ++ tx) = true

theorem verifyFundingChecked_iff_vendor ... :
    verifyFundingChecked M key tx sig = true ↔ fundingValidVendor key tx sig
```

At the protocol level, `WaveE.E19.fundingSignedValid` is exactly this
checked predicate at `m.signature`:

```lean
theorem fundingSignedValid_iff_vendor (M : PrimitiveModel)
    (h : VendorEcdsaBridge M) (fundingKey : PubKey) (fundingTx : ByteArray)
    (m : LnLean.Protocol.FundingSigned) :
    WaveE.E19.fundingSignedValid M fundingKey fundingTx m ↔
      fundingValidVendor fundingKey fundingTx m.signature
```

Message binding and cross-domain separation transfer with the model's C3:

```lean
theorem verifyImpl_funding_message_bound (M : PrimitiveModel)
    (h : VendorEcdsaBridge M) (hM : EufCma M.ecdsaVerify)
    {pk : PubKey} {m₁ m₂ : ByteArray} {sig : EcdsaSig}
    (h₁ : verifyImpl sig.bytes pk.bytes (fundingTag ++ m₁) = true)
    (h₂ : verifyImpl sig.bytes pk.bytes (fundingTag ++ m₂) = true) :
    m₁ = m₂

theorem fundingSignedValid_vendor_binds_tx (M : PrimitiveModel)
    (h : VendorEcdsaBridge M) (hM : EufCma M.ecdsaVerify)
    {fundingKey : PubKey} {tx₁ tx₂ : ByteArray}
    {m : LnLean.Protocol.FundingSigned}
    (h₁ : WaveE.E19.fundingSignedValid M fundingKey tx₁ m)
    (h₂ : WaveE.E19.fundingSignedValid M fundingKey tx₂ m) :
    tx₁ = tx₂

theorem verifyImpl_no_funding_commitment_reuse (M : PrimitiveModel)
    (h : VendorEcdsaBridge M) (hM : AssumesEufCma M)
    {pk : PubKey} {m₁ m₂ : ByteArray} {sig : EcdsaSig}
    (hf : verifyImpl sig.bytes pk.bytes (fundingTag ++ m₁) = true)
    (hc : verifyImpl sig.bytes pk.bytes (commitmentTag ++ m₂) = true) :
    False
```

### 3.4 DER, pubkey, and digest boundaries

```lean
theorem parseDerLax_zeros64 : parseDerLax (zeros 64) = none

theorem verifyImpl_compact64_zeros_false (pk msg : ByteArray) :
    verifyImpl (zeros 64) pk msg = false

theorem wireSigOK_compact64_not_vendor_accepted (pk msg : ByteArray) :
    wireSigOK (zeros 64) = true ∧ verifyImpl (zeros 64) pk msg = false

def oneByteCompressedKey : ByteArray := ByteArray.mk #[0x02]

theorem isValidPubKey_oneByteCompressedKey :
    Bitcoin.Crypto.Seam.Der.isValidPubKey oneByteCompressedKey = true

theorem parsePubKey_oneByteCompressedKey :
    parsePubKey oneByteCompressedKey = none

theorem verifyImpl_oneBytePubKey_false (sig msg : ByteArray) :
    verifyImpl sig oneByteCompressedKey msg = false

theorem seamDigest_size (tx : Bitcoin.Data.Tx) (nIn : Nat) (scriptCode : ByteArray)
    (ht : UInt32) (amount : Amount) :
    (sighashWitnessV0 tx nIn scriptCode ht amount).size = 32
```

Three distinct gates must not be conflated:

| Gate | Where | What it checks |
|---|---|---|
| `wireSigOK` (model) | `LnLean.Crypto.Sig` | compact 64-byte wire shape (length), no DER parse |
| `isValidPubKey` (seam) | `Bitcoin.Crypto.Seam.Der` | non-empty and a recognized header byte; **no length check** |
| `parsePubKey` / `parseDerLax` (vendor) | `Verify.lean` | exact 33/65-byte key plus curve equation; lax DER body |

A 64-byte compact signature passes `wireSigOK` and fails `parseDerLax`; a
one-byte `0x02` key passes `isValidPubKey` and fails `parsePubKey`.  The
on-chain path never feeds the compact form to `verifyImpl`: `ecdsaEntry`
pops the last (hashtype) byte and passes `sig.extract 0 (sig.size - 1)`.

`verifyImpl` itself has **no** 32-byte size gate on `msg`; the 32-byte
precondition belongs to the constructed BIP 143 digest
(`sighashWitnessV0_size`), not to the verifier.

### 3.5 The interpreter seam, amount, and sighash dispatch

```lean
theorem model_verify_eq_vendor_seam (M : PrimitiveModel)
    (h : VendorEcdsaBridge M) (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount)
    (sig scriptCode : ByteArray) (pk : PubKey)
    (ed : Bitcoin.Crypto.Seam.ScriptExecutionData)
    (hpk : isValidPubKey pk.bytes = true) (hne : 0 < sig.size) :
    M.ecdsaVerify pk
        (sighashWitnessV0 tx nIn scriptCode (hashtypeOf sig) amount)
        ⟨sig.extract 0 (sig.size - 1)⟩ =
      (checkerOf verifyImpl tx nIn amount).base.checkECDSASignature
        sig pk.bytes scriptCode .witnessV0 ed

theorem model_verify_eq_realChecker_seam (M : PrimitiveModel)
    (h : VendorEcdsaBridge M) (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount)
    (hIn : nIn < tx.vin.length) ... :
    M.ecdsaVerify pk
        (sighashWitnessV0 tx nIn scriptCode (hashtypeOf sig) amount)
        ⟨sig.extract 0 (sig.size - 1)⟩ =
      (Bitcoin.Capstone.RealChecker.realCheckerOf tx nIn amount).base.checkECDSASignature
        sig pk.bytes scriptCode .witnessV0 ed
```

The first theorem is the complete seam: it simultaneously fixes the argument
order, the DER-body split (`extract 0 (sig.size - 1)`), the hashtype byte
(`hashtypeOf sig`), the amount (`amount` is a parameter of both
`sighashWitnessV0` and `checkerOf`), and the witness-v0 dispatch.  The EC
verifier sees only the composed digest; `Amount` never reaches `verifyImpl`
directly.  `checkerOf` sets the “amount present” flag to `true`;
`realCheckerOf` is the capstone wiring, and the transfer needs
`nIn < tx.vin.length` only because the two totalizations use different dummy
`TxIn` values out of range (`checkerOf_eq_realCheckerOf`).

The three branch agreements are re-proved with model-level hypotheses:

```lean
theorem funding_sighash_interpreters_agree_vendor
    (M : PrimitiveModel) (h : VendorEcdsaBridge M) ... :
    verifyWitnessProgram 6 ... (checkerOf verifyImpl tx nIn amount) false = .ok ∧
      P2WSHSpend ... ∧
      checkECDSASignature s1 a.bytes ... = true ∧
      checkECDSASignature s2 b.bytes ... = true

theorem toLocal_delayed_sighash_interpreters_agree_vendor
    (M : PrimitiveModel) (h : VendorEcdsaBridge M) ... :
    verifyWitnessProgram 10 ... (checkerOf verifyImpl tx nIn amount) false = .ok ∧
      P2WSHSpend ... ∧ checkECDSASignature sig delayedPaymentKey.bytes ... = true

theorem toLocal_revocation_interpreters_agree_vendor
    (M : PrimitiveModel) (h : VendorEcdsaBridge M) ... :
    verifyWitnessProgram 10 ... (checkerOf verifyImpl tx nIn amount) false = .ok ∧
      P2WSHSpend ...
```

Their full hypothesis lists are in the signature appendix; they are the
wave-5/6/7 theorems with each abstract-verifier call replaced by
`M.ecdsaVerify`, then discharged to `verifyImpl` via
`verifyImpl_eq_model`.

### 3.6 The concrete model

```lean
def withVendorEcdsa (M₀ : PrimitiveModel) (hEuf : EufCma vendorVerify) :
    PrimitiveModel :=
  { M₀ with ecdsaVerify := vendorVerify, ecdsa_eufCma := hEuf }

theorem withVendorEcdsa_sha256_collisionResistant (M₀ : PrimitiveModel)
    (hEuf : EufCma vendorVerify) :
    CollisionResistant (withVendorEcdsa M₀ hEuf).sha256

theorem withVendorEcdsa_eufCma (M₀ : PrimitiveModel) (hEuf : EufCma vendorVerify) :
    EufCma (withVendorEcdsa M₀ hEuf).ecdsaVerify

theorem withVendorEcdsa_bridge (M₀ : PrimitiveModel) (hEuf : EufCma vendorVerify) :
    VendorEcdsaBridge (withVendorEcdsa M₀ hEuf)

theorem verifyFundingChecked_withVendor_iff (M₀ : PrimitiveModel)
    (hEuf : EufCma vendorVerify) (key : PubKey) (tx : ByteArray) (sig : EcdsaSig) :
    verifyFundingChecked (withVendorEcdsa M₀ hEuf) key tx sig = true ↔
      fundingValidVendor key tx sig

theorem fundingSignedValid_withVendor_iff (M₀ : PrimitiveModel)
    (hEuf : EufCma vendorVerify) (fundingKey : PubKey) (fundingTx : ByteArray)
    (m : LnLean.Protocol.FundingSigned) :
    WaveE.E19.fundingSignedValid (withVendorEcdsa M₀ hEuf) fundingKey fundingTx m ↔
      fundingValidVendor fundingKey fundingTx m.signature

theorem withVendor_verifyImpl_funding_message_bound (M₀ : PrimitiveModel)
    (hEuf : EufCma vendorVerify) ... :
    m₁ = m₂
```

This is the intended use: pick the project's existing `M₀` (with its C1
field and all other primitives), supply the concrete C3 hypothesis, and the
resulting model's verifier is definitionally `verifyImpl`.  The
`fundingSignedValid` theorem is new relative to the initial lane snapshot:
`Protocol/Handshake.lean` was broken by another wave-8 lane when this module
was started, so the first build deliberately avoided `WaveE.E19`.  The shared
tree was repaired during the lane, `ln-lean-repair` now builds E19, and the
record-level bridge was added and re-verified.

## 4. Build and audit evidence

Build (only the new module, shared lock, single thread, current tree):

```text
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Proofs.Bitcoin.EcdsaBridgeTargets
```

Result:

```text
✔ [59/59] Built LnLean.Proofs.Bitcoin.EcdsaBridgeTargets (875ms)
Build completed successfully (59 jobs).
```

`#print axioms` was run on all 37 public theorems (temporary script,
`lake env lean`, same lock).  Result: every theorem depends only on
`propext`, `Quot.sound`, and `Classical.choice`; two `decide` facts depend on
no axioms (`parseDerLax_zeros64`, `isValidPubKey_oneByteCompressedKey`), and
two depend only on `[propext, Quot.sound]`
(`eufCma_not_keyBinding_retained`, `parsePubKey_oneByteCompressedKey`).
Representative output:

```text
'...verifyImpl_eq_model' depends on axioms: [propext, Classical.choice, Quot.sound]
'...eufCma_iff_vendor' depends on axioms: [propext, Classical.choice, Quot.sound]
'...keyBinding_iff_vendor' depends on axioms: [propext, Classical.choice, Quot.sound]
'...not_eufCma_vendorVerify_of_reduction' depends on axioms: [propext, Classical.choice, Quot.sound]
'...model_verify_eq_vendor_seam' depends on axioms: [propext, Classical.choice, Quot.sound]
'...model_verify_eq_realChecker_seam' depends on axioms: [propext, Classical.choice, Quot.sound]
'...fundingSignedValid_iff_vendor' depends on axioms: [propext, Classical.choice, Quot.sound]
'...withVendorEcdsa_sha256_collisionResistant' depends on axioms: [propext, Classical.choice, Quot.sound]
'...parseDerLax_zeros64' does not depend on any axioms
'...isValidPubKey_oneByteCompressedKey' does not depend on any axioms
'...eufCma_not_keyBinding_retained' depends on axioms: [propext, Quot.sound]
'...parsePubKey_oneByteCompressedKey' depends on axioms: [propext, Quot.sound]
```

No axiom outside the allowed set appears; no `sorry`, `admit`, `axiom`
declaration, `native_decide`, `unsafe`, or `@[implemented_by]` is used.

Forbidden-construct scan:

```text
grep -nE '\b(sorry|admit|axiom|native_decide|unsafe|implemented_by)\b' \
  LnLean/Proofs/Bitcoin/EcdsaBridgeTargets.lean
# no matches (grep exit 1)
```

## 5. Boundaries: what is *not* claimed

1. **No unconditional verifier bridge.**  `M.ecdsaVerify` is a field of
   `PrimitiveModel`; `VendorEcdsaBridge M` is an assumption about an
   instance.  The concrete model requires `hEuf : EufCma vendorVerify`.
2. **No ECDSA security proof and no unconditional C3.**  `EufCma
   vendorVerify` is not derived from the curve implementation.  The mod-`n`
   reduction theorem shows that byte-level message binding is actually false
   for `verifyImpl` in the presence of a same-residue companion message; the
   protocol must rely on domain separation / digest uniqueness, which is not
   proved here.  No forgery construction and no claim about computational
   ECDSA hardness are made.
3. **C1 is inherited, not reproved.**  `withVendorEcdsa_sha256_collisionResistant`
   is exactly `M₀.sha256_collisionResistant`; the bridge concerns ECDSA only
   and does not touch the hash assumption.
4. **Key binding is independent.**  `keyBinding_iff_vendor` is an iff under
   the bridge, and the retained `eufCma_not_keyBinding` counterexample plus
   `not_keyBinding_vendorVerify_of_two_keys` show C3 does not imply key
   attribution.  No “signature identifies the signer” claim.
5. **DER is lax, and the compact wire form is different.**  `verifyImpl`
   parses a DER body via `parseDerLax` (no trailing sighash byte).  The
   model's `wireSigOK` accepts a 64-byte compact signature, which the vendor
   verifier rejects; the interpreter strips the hashtype byte first.  Strict
   DER/BIP 66 policy is not modeled by `verifyImpl`.
6. **The pubkey gate is weaker than the parser.**  `isValidPubKey` checks
   only non-emptiness and the header byte; `parsePubKey` enforces exact
   length and the curve equation.  The seam theorem assumes only
   `isValidPubKey`, which is faithful to `ecdsaVerdict`; malformed short keys
   reach `verifyImpl` and fail closed there.
7. **The 32-byte digest is a context property.**  `verifyImpl` has no size
   gate and reduces any `msg` modulo `n`; `sighashWitnessV0` is proved
   32 bytes.  Treating the digest as a 32-byte value is justified by the
   constructor, not by the verifier.
8. **Amount and sighash dispatch.**  `Amount` and the hashtype enter only
   through `sighashWitnessV0` / `sighashDispatch`; `checkerOf` fixes
   “amount present” to `true`.  The missing-amount failure is handled in
   `TxValidTransferTargets`, not here.  `realCheckerOf` transfer requires
   `nIn < tx.vin.length`.
9. **Positive-direction scope retained.**  The three interpreter agreements
   are the existing positive-direction P2WSH statements with the verifier
   instantiated; no new negative-direction or full-consensus claim is added.

## 6. Integration steps (not performed; shared files)

The lane owns only the new module and this report.  The exact integration
patch for the integrator is:

1. **Root import.**  In `LnLean.lean`, add after
   `import LnLean.Proofs.Bitcoin.AnchorProps` (line 29, alphabetical):
   ```lean
   import LnLean.Proofs.Bitcoin.EcdsaBridgeTargets
   ```
2. **Traceability.**  In `LnLean/Proofs/Traceability.lean`, add entries to the
   public-theorem table (around line 403) and to the module list (around
   line 470):
   ```lean
   , ⟨"LnLean.Proofs.Bitcoin.EcdsaBridgeTargets.model_verify_eq_vendor_seam",
       "LnLean.Proofs.Bitcoin.EcdsaBridgeTargets"⟩
   , ⟨"LnLean.Proofs.Bitcoin.EcdsaBridgeTargets.model_verify_eq_realChecker_seam",
       "LnLean.Proofs.Bitcoin.EcdsaBridgeTargets"⟩
   , ⟨"LnLean.Proofs.Bitcoin.EcdsaBridgeTargets.fundingSignedValid_iff_vendor",
       "LnLean.Proofs.Bitcoin.EcdsaBridgeTargets"⟩
   , ⟨"LnLean.Proofs.Bitcoin.EcdsaBridgeTargets.verifyImpl_funding_message_bound",
       "LnLean.Proofs.Bitcoin.EcdsaBridgeTargets"⟩
   , "LnLean.Proofs.Bitcoin.EcdsaBridgeTargets"
   ```
3. **Axiom audit.**  In `LnLean/Proofs/PhaseC3/AxiomAudit.lean`, add the
   import and `#print axioms` lines for at least:
   `verifyImpl_eq_model`, `eufCma_iff_vendor`, `keyBinding_iff_vendor`,
   `not_eufCma_vendorVerify_of_reduction`, `verifyFundingChecked_iff_vendor`,
   `fundingSignedValid_iff_vendor`, `model_verify_eq_vendor_seam`,
   `model_verify_eq_realChecker_seam`,
   `funding_sighash_interpreters_agree_vendor`,
   `toLocal_delayed_sighash_interpreters_agree_vendor`,
   `toLocal_revocation_interpreters_agree_vendor`,
   `withVendorEcdsa_sha256_collisionResistant`,
   `withVendorEcdsa_bridge`.
4. **Catalog targets.**  In `LnLean/Proofs/Obligations.lean`, append to
   `LN-L1-001.leanTarget`:
   `LnLean.Proofs.Bitcoin.EcdsaBridgeTargets.fundingSignedValid_iff_vendor;
    LnLean.Proofs.Bitcoin.EcdsaBridgeTargets.funding_sighash_interpreters_agree_vendor`,
   and to `LN-L1-004.leanTarget`:
   `LnLean.Proofs.Bitcoin.EcdsaBridgeTargets.model_verify_eq_realChecker_seam;
    LnLean.Proofs.Bitcoin.EcdsaBridgeTargets.toLocal_revocation_interpreters_agree_vendor`.
   No new obligation id is needed (see §8).
5. **Docs.**  Update `docs/OPEN-ISSUES.md` `L1-01` / `L1-07` text,
   `docs/ROADMAP.md`'s remaining-gap sentence, and `docs/THEOREM-INDEX.md`;
   regenerate `docs/OBLIGATIONS-GENERATED.md` with the repository's
   `scripts/collect-obligations.py` (not run in this lane, per instructions).
6. **Full build.**  Run the repository's normal full build and axiom sweep at
   integration time; this lane only ran the scoped target and a scoped
   `#print axioms` script.

## 7. Blockers

None for the assigned scope.  The initial blocker — the shared
`LnLean/Protocol/Handshake.lean` was mid-edit by another wave-8 lane, so
`WaveE.E19` could not be imported — is resolved in the current tree:
`lake build LnLean.Proofs.WaveE.E19` completes (19 jobs), and the
`fundingSignedValid` bridge is now mechanized.

One dependency risk remains: `EcdsaBridgeTargets` now imports
`LnLean.Proofs.WaveE.E19`, which pulls in the protocol/`Handshake` closure.
If another lane breaks that closure again, this module will not build even
though its ECDSA content is independent.  If the integrator prefers the
original low-coupling layout, dropping the `WaveE.E19` import and the three
`fundingSignedValid_*` theorems leaves the rest of the module unchanged;
`fundingValidVendor` and `verifyFundingChecked_iff_vendor` already express
the same condition without the record type.

## 8. Catalog / roadmap recommendation (`L1-01`, `L1-07`)

**Keep both issues open.**  The bridge closes the “concrete EC verifier”
implementation gap but does not discharge the cryptographic hypothesis.

* **`L1-01` (P2WSH/`OP_CHECKMULTISIG` spendability).**  Replace the sentence
  “ECDSA remains an abstract verifier” with: “ECDSA is bridged pointwise to
  `Bitcoin.Crypto.Ecdsa.Verify.verifyImpl` under `VendorEcdsaBridge`; the
  concrete model `withVendorEcdsa` requires only `EufCma vendorVerify`, and
  C1 is inherited.  The bridge is an explicit hypothesis, not an ECDSA
  security proof; the mod-`n` message reduction is a documented boundary.”
  Add `model_verify_eq_realChecker_seam` and
  `fundingSignedValid_iff_vendor` to the evidence list.
* **`L1-07` (vendored real interpreter).**  Add
  `model_verify_eq_vendor_seam` /
  `model_verify_eq_realChecker_seam` and the three `*_vendor` branch
  agreements to the evidence list.  The remaining gap is unchanged:
  `TxValidation.Full`/`txCheckerFor` transfer, the `minimalData` and
  `csv ≥ 32768` policy edges, and the explicit C3 hypothesis.
* **Obligations.**  `LN-L1-001` and `LN-L1-004` are the right catalog
  entries; extend their `leanTarget` strings as in §6.4.  Do **not** add a
  new `LN-L1-00x` id in this lane: the id table (`LnLean/Proofs/Obligations.lean`,
  `Traceability.lean` `idTable`) and the generated docs are shared catalog
  state, and a new id would require coordinated edits outside this lane's
  write set.  If a dedicated “concrete ECDSA bridge” obligation is desired,
  the integrator should add it in one commit together with the id table,
  traceability table, and generated documents.
* **Roadmap wording.**  The “full consensus claim would need a concrete EC
  verifier” item should become “needs the explicit `EufCma vendorVerify`
  hypothesis (C3) and the `TxValidation.Full` transfer”; the concrete
  verifier itself is now wired.
* **Do not upgrade** `LN-CR-002`/C3 status based on this lane: the bridge
  transfers C3, it does not prove it.  The existing `EufCma`/`KeyBinding`
  separation remains the correct statement.

## 9. Parent summary

`EcdsaBridgeTargets.lean` builds cleanly (59 jobs, exit 0).  It defines the
pointwise seam bridge in model order (`pk msg sig`) against vendor order
(`sig pk msg`), proves the exact bridge equation and the iff-transfers of C3
and key binding, exposes the `% n` message-reduction gap with a sharp
extraction theorem, rewrites the funding/commitment/close and
`funding_signed` predicates at `verifyImpl`, proves the DER/compact,
pubkey-gate/parser, and 32-byte-digest boundaries with concrete
counterexamples, and restates the funding, delayed `to_local`, and revocation
interpreter agreements with model-level ECDSA hypotheses at
`checkerOf verifyImpl` and `RealChecker.realCheckerOf`.  The concrete
`withVendorEcdsa` model needs only `EufCma vendorVerify`; C1 is inherited.
All 37 public theorems use only `propext`, `Quot.sound`, and
`Classical.choice`; no forbidden constructs; no vendor or shared proof file
was edited; no Git write.  Remaining work is integration (§6) and the
explicit cryptographic hypothesis, not a missing implementation link.

## Appendix: full theorem signatures

The following is the exact `#check @...` output for every public theorem in
the module (37 theorems; `@` removed for readability).

```lean
vendorVerify_def : ∀ (pk : LnLean.PubKey) (msg : ByteArray) (sig : LnLean.EcdsaSig),
  vendorVerify pk msg sig = Bitcoin.Crypto.Ecdsa.Verify.verifyImpl sig.bytes pk.bytes msg
verifyImpl_eq_model : ∀ (M : LnLean.Crypto.PrimitiveModel),
  VendorEcdsaBridge M →
    ∀ (pk : LnLean.PubKey) (msg : ByteArray) (sig : LnLean.EcdsaSig),
      Bitcoin.Crypto.Ecdsa.Verify.verifyImpl sig.bytes pk.bytes msg = M.ecdsaVerify pk msg sig
verifyImpl_true_iff_model : ∀ (M : LnLean.Crypto.PrimitiveModel),
  VendorEcdsaBridge M →
    ∀ (pk : LnLean.PubKey) (msg : ByteArray) (sig : LnLean.EcdsaSig),
      Bitcoin.Crypto.Ecdsa.Verify.verifyImpl sig.bytes pk.bytes msg = true ↔ M.ecdsaVerify pk msg sig = true
eufCma_iff_vendor : ∀ (M : LnLean.Crypto.PrimitiveModel),
  VendorEcdsaBridge M → (LnLean.Crypto.EufCma M.ecdsaVerify ↔ LnLean.Crypto.EufCma vendorVerify)
keyBinding_iff_vendor : ∀ (M : LnLean.Crypto.PrimitiveModel),
  VendorEcdsaBridge M → (LnLean.Crypto.KeyBinding M.ecdsaVerify ↔ LnLean.Crypto.KeyBinding vendorVerify)
verifyImpl_msg_congr : ∀ (sig pk : ByteArray) {m₁ m₂ : ByteArray},
  Bitcoin.Crypto.Curve.Secp.bytesToNatBE m₁ % Bitcoin.Crypto.Curve.Secp.n =
      Bitcoin.Crypto.Curve.Secp.bytesToNatBE m₂ % Bitcoin.Crypto.Curve.Secp.n →
    Bitcoin.Crypto.Ecdsa.Verify.verifyImpl sig pk m₁ = Bitcoin.Crypto.Ecdsa.Verify.verifyImpl sig pk m₂
not_eufCma_vendorVerify_of_reduction : ∀ {pk : LnLean.PubKey} {m₁ m₂ : ByteArray} {sig : LnLean.EcdsaSig},
  vendorVerify pk m₁ sig = true →
    m₁ ≠ m₂ →
      Bitcoin.Crypto.Curve.Secp.bytesToNatBE m₁ % Bitcoin.Crypto.Curve.Secp.n =
          Bitcoin.Crypto.Curve.Secp.bytesToNatBE m₂ % Bitcoin.Crypto.Curve.Secp.n →
        ¬LnLean.Crypto.EufCma vendorVerify
not_keyBinding_vendorVerify_of_two_keys : ∀ {pk₁ pk₂ : LnLean.PubKey} {msg : ByteArray} {sig : LnLean.EcdsaSig},
  pk₁ ≠ pk₂ → vendorVerify pk₁ msg sig = true → vendorVerify pk₂ msg sig = true → ¬LnLean.Crypto.KeyBinding vendorVerify
eufCma_not_keyBinding_retained : LnLean.Crypto.EufCma (LnLean.Crypto.singleMessageVerify ByteArray.empty) ∧
  ¬LnLean.Crypto.KeyBinding (LnLean.Crypto.singleMessageVerify ByteArray.empty)
verifyFunding_eq_vendor : ∀ (M : LnLean.Crypto.PrimitiveModel),
  VendorEcdsaBridge M →
    ∀ (pk : LnLean.PubKey) (msg : ByteArray) (sig : LnLean.EcdsaSig),
      LnLean.Crypto.verifyFunding M pk msg sig =
        Bitcoin.Crypto.Ecdsa.Verify.verifyImpl sig.bytes pk.bytes (LnLean.Crypto.fundingTag ++ msg)
verifyCommitment_eq_vendor : ∀ (M : LnLean.Crypto.PrimitiveModel),
  VendorEcdsaBridge M →
    ∀ (pk : LnLean.PubKey) (msg : ByteArray) (sig : LnLean.EcdsaSig),
      LnLean.Crypto.verifyCommitment M pk msg sig =
        Bitcoin.Crypto.Ecdsa.Verify.verifyImpl sig.bytes pk.bytes (LnLean.Crypto.commitmentTag ++ msg)
verifyClose_eq_vendor : ∀ (M : LnLean.Crypto.PrimitiveModel),
  VendorEcdsaBridge M →
    ∀ (pk : LnLean.PubKey) (msg : ByteArray) (sig : LnLean.EcdsaSig),
      LnLean.Crypto.verifyClose M pk msg sig =
        Bitcoin.Crypto.Ecdsa.Verify.verifyImpl sig.bytes pk.bytes (LnLean.Crypto.closeTag ++ msg)
verifyFundingChecked_eq_vendor : ∀ (M : LnLean.Crypto.PrimitiveModel),
  VendorEcdsaBridge M →
    ∀ (pk : LnLean.PubKey) (msg : ByteArray) (sig : LnLean.EcdsaSig),
      LnLean.Crypto.verifyFundingChecked M pk msg sig =
        (LnLean.Crypto.wireSigOK sig.bytes &&
          Bitcoin.Crypto.Ecdsa.Verify.verifyImpl sig.bytes pk.bytes (LnLean.Crypto.fundingTag ++ msg))
verifyFundingChecked_iff_vendor : ∀ (M : LnLean.Crypto.PrimitiveModel),
  VendorEcdsaBridge M →
    ∀ (key : LnLean.PubKey) (tx : ByteArray) (sig : LnLean.EcdsaSig),
      LnLean.Crypto.verifyFundingChecked M key tx sig = true ↔ fundingValidVendor key tx sig
fundingSignedValid_iff_vendor : ∀ (M : LnLean.Crypto.PrimitiveModel),
  VendorEcdsaBridge M →
    ∀ (fundingKey : LnLean.PubKey) (fundingTx : ByteArray) (m : LnLean.Protocol.FundingSigned),
      LnLean.Proofs.WaveE.E19.fundingSignedValid M fundingKey fundingTx m ↔
        fundingValidVendor fundingKey fundingTx m.signature
verifyImpl_funding_message_bound : ∀ (M : LnLean.Crypto.PrimitiveModel),
  VendorEcdsaBridge M →
    LnLean.Crypto.EufCma M.ecdsaVerify →
      ∀ {pk : LnLean.PubKey} {m₁ m₂ : ByteArray} {sig : LnLean.EcdsaSig},
        Bitcoin.Crypto.Ecdsa.Verify.verifyImpl sig.bytes pk.bytes (LnLean.Crypto.fundingTag ++ m₁) = true →
          Bitcoin.Crypto.Ecdsa.Verify.verifyImpl sig.bytes pk.bytes (LnLean.Crypto.fundingTag ++ m₂) = true → m₁ = m₂
fundingSignedValid_vendor_binds_tx : ∀ (M : LnLean.Crypto.PrimitiveModel),
  VendorEcdsaBridge M →
    LnLean.Crypto.EufCma M.ecdsaVerify →
      ∀ {fundingKey : LnLean.PubKey} {tx₁ tx₂ : ByteArray} {m : LnLean.Protocol.FundingSigned},
        LnLean.Proofs.WaveE.E19.fundingSignedValid M fundingKey tx₁ m →
          LnLean.Proofs.WaveE.E19.fundingSignedValid M fundingKey tx₂ m → tx₁ = tx₂
verifyImpl_no_funding_commitment_reuse : ∀ (M : LnLean.Crypto.PrimitiveModel),
  VendorEcdsaBridge M →
    LnLean.Crypto.AssumesEufCma M →
      ∀ {pk : LnLean.PubKey} {m₁ m₂ : ByteArray} {sig : LnLean.EcdsaSig},
        Bitcoin.Crypto.Ecdsa.Verify.verifyImpl sig.bytes pk.bytes (LnLean.Crypto.fundingTag ++ m₁) = true →
          Bitcoin.Crypto.Ecdsa.Verify.verifyImpl sig.bytes pk.bytes (LnLean.Crypto.commitmentTag ++ m₂) = true → False
parseDerLax_zeros64 : Bitcoin.Crypto.Ecdsa.Der.parseDerLax (LnLean.Crypto.zeros 64) = none
verifyImpl_compact64_zeros_false : ∀ (pk msg : ByteArray),
  Bitcoin.Crypto.Ecdsa.Verify.verifyImpl (LnLean.Crypto.zeros 64) pk msg = false
wireSigOK_compact64_not_vendor_accepted : ∀ (pk msg : ByteArray),
  LnLean.Crypto.wireSigOK (LnLean.Crypto.zeros 64) = true ∧
    Bitcoin.Crypto.Ecdsa.Verify.verifyImpl (LnLean.Crypto.zeros 64) pk msg = false
isValidPubKey_oneByteCompressedKey : Bitcoin.Crypto.Seam.Der.isValidPubKey oneByteCompressedKey = true
parsePubKey_oneByteCompressedKey : Bitcoin.Crypto.Ecdsa.Verify.parsePubKey oneByteCompressedKey = none
verifyImpl_oneBytePubKey_false : ∀ (sig msg : ByteArray),
  Bitcoin.Crypto.Ecdsa.Verify.verifyImpl sig oneByteCompressedKey msg = false
seamDigest_size : ∀ (tx : Bitcoin.Data.Tx) (nIn : Nat) (scriptCode : ByteArray) (ht : UInt32)
  (amount : Bitcoin.Data.Amount), (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn scriptCode ht amount).size = 32
model_verify_eq_vendor_seam : ∀ (M : LnLean.Crypto.PrimitiveModel),
  VendorEcdsaBridge M →
    ∀ (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Bitcoin.Data.Amount) (sig scriptCode : ByteArray)
      (pk : LnLean.PubKey) (ed : Bitcoin.Crypto.Seam.ScriptExecutionData),
      Bitcoin.Crypto.Seam.Der.isValidPubKey pk.bytes = true →
        0 < sig.size →
          M.ecdsaVerify pk
              (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn scriptCode
                (LnLean.Proofs.Bitcoin.SighashBridgeTargets.hashtypeOf sig) amount)
              { bytes := sig.extract 0 (sig.size - 1) } =
            (LnLean.Proofs.Bitcoin.SighashBridgeTargets.checkerOf Bitcoin.Crypto.Ecdsa.Verify.verifyImpl tx nIn
                    amount).base.checkECDSASignature
              sig pk.bytes scriptCode Bitcoin.Crypto.Seam.SigVersion.witnessV0 ed
model_verify_eq_realChecker_seam : ∀ (M : LnLean.Crypto.PrimitiveModel),
  VendorEcdsaBridge M →
    ∀ (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Bitcoin.Data.Amount),
      nIn < tx.vin.length →
        ∀ (sig scriptCode : ByteArray) (pk : LnLean.PubKey) (ed : Bitcoin.Crypto.Seam.ScriptExecutionData),
          Bitcoin.Crypto.Seam.Der.isValidPubKey pk.bytes = true →
            0 < sig.size →
              M.ecdsaVerify pk
                  (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn scriptCode
                    (LnLean.Proofs.Bitcoin.SighashBridgeTargets.hashtypeOf sig) amount)
                  { bytes := sig.extract 0 (sig.size - 1) } =
                (Bitcoin.Capstone.RealChecker.realCheckerOf tx nIn amount).base.checkECDSASignature sig pk.bytes
                  scriptCode Bitcoin.Crypto.Seam.SigVersion.witnessV0 ed
funding_sighash_interpreters_agree_vendor : ∀ (M : LnLean.Crypto.PrimitiveModel),
  VendorEcdsaBridge M →
    ∀ (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Bitcoin.Data.Amount) (a b : LnLean.PubKey) (s1 s2 dummy : ByteArray),
      a.bytes.size = 33 →
        b.bytes.size = 33 →
          s1.size ≤ 520 →
            s2.size ≤ 520 →
              dummy.size ≤ 520 →
                Bitcoin.Crypto.Seam.Der.isValidPubKey a.bytes = true →
                  Bitcoin.Crypto.Seam.Der.isValidPubKey b.bytes = true →
                    0 < s1.size →
                      0 < s2.size →
                        M.ecdsaVerify a
                              (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn
                                (Bitcoin.Script.Parser.serializeOpcodes
                                  (LnLean.Proofs.Bitcoin.InterpreterBridgeTargets.fundingOps a b))
                                (LnLean.Proofs.Bitcoin.SighashBridgeTargets.hashtypeOf s1) amount)
                              { bytes := s1.extract 0 (s1.size - 1) } =
                            true →
                          M.ecdsaVerify b
                                (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn
                                  (Bitcoin.Script.Parser.serializeOpcodes
                                    (LnLean.Proofs.Bitcoin.InterpreterBridgeTargets.fundingOps a b))
                                  (LnLean.Proofs.Bitcoin.SighashBridgeTargets.hashtypeOf s2) amount)
                                { bytes := s2.extract 0 (s2.size - 1) } =
                              true →
                            Bitcoin.Interpreter.verifyWitnessProgram 6
                                  [dummy, s1, s2,
                                    Bitcoin.Script.Parser.serializeOpcodes
                                      (LnLean.Proofs.Bitcoin.InterpreterBridgeTargets.fundingOps a b)]
                                  0
                                  (Bitcoin.Interpreter.hashSha256
                                    (Bitcoin.Script.Parser.serializeOpcodes
                                      (LnLean.Proofs.Bitcoin.InterpreterBridgeTargets.fundingOps a b)))
                                  { } { }
                                  (LnLean.Proofs.Bitcoin.SighashBridgeTargets.checkerOf
                                    Bitcoin.Crypto.Ecdsa.Verify.verifyImpl tx nIn amount)
                                  false =
                                Bitcoin.Interpreter.VerifyOutcome.ok ∧
                              LnLean.Proofs.Bitcoin.SpendTargets.P2WSHSpend
                                  (LnLean.Proofs.Bitcoin.InterpreterBridgeTargets.vendorLaws
                                    (LnLean.Proofs.Bitcoin.SighashBridgeTargets.checkerOf
                                      Bitcoin.Crypto.Ecdsa.Verify.verifyImpl tx nIn amount)
                                    (Bitcoin.Script.Parser.serializeOpcodes
                                      (LnLean.Proofs.Bitcoin.InterpreterBridgeTargets.fundingOps a b)))
                                  (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn
                                    (Bitcoin.Script.Parser.serializeOpcodes
                                      (LnLean.Proofs.Bitcoin.InterpreterBridgeTargets.fundingOps a b))
                                    (LnLean.Proofs.Bitcoin.SighashBridgeTargets.hashtypeOf s1) amount)
                                  (Bitcoin.Interpreter.hashSha256
                                    (Bitcoin.Script.Parser.serializeOpcodes
                                      (LnLean.Proofs.Bitcoin.InterpreterBridgeTargets.fundingOps a b)))
                                  (Bitcoin.Script.Parser.serializeOpcodes
                                    (LnLean.Proofs.Bitcoin.InterpreterBridgeTargets.fundingOps a b))
                                  (LnLean.Proofs.Bitcoin.SpendTargets.fundingProg a b) [s2, s1, dummy] ∧
                                (LnLean.Proofs.Bitcoin.SighashBridgeTargets.checkerOf
                                            Bitcoin.Crypto.Ecdsa.Verify.verifyImpl tx nIn
                                            amount).base.checkECDSASignature
                                      s1 a.bytes
                                      (Bitcoin.Script.Parser.serializeOpcodes
                                        (LnLean.Proofs.Bitcoin.InterpreterBridgeTargets.fundingOps a b))
                                      Bitcoin.Crypto.Seam.SigVersion.witnessV0 default =
                                    true ∧
                                  (LnLean.Proofs.Bitcoin.SighashBridgeTargets.checkerOf
                                            Bitcoin.Crypto.Ecdsa.Verify.verifyImpl tx nIn
                                            amount).base.checkECDSASignature
                                      s2 b.bytes
                                      (Bitcoin.Script.Parser.serializeOpcodes
                                        (LnLean.Proofs.Bitcoin.InterpreterBridgeTargets.fundingOps a b))
                                      Bitcoin.Crypto.Seam.SigVersion.witnessV0 default =
                                    true
toLocal_delayed_sighash_interpreters_agree_vendor : ∀ (M : LnLean.Crypto.PrimitiveModel),
  VendorEcdsaBridge M →
    ∀ (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Bitcoin.Data.Amount)
      (revocationKey delayedPaymentKey : LnLean.PubKey) (csv : LnLean.Blocks) (sig : ByteArray)
      (n : Bitcoin.Numeric.ScriptNum),
      revocationKey.bytes.size = 33 →
        delayedPaymentKey.bytes.size = 33 →
          sig.size ≤ 520 →
            Bitcoin.Crypto.Seam.Der.isValidPubKey delayedPaymentKey.bytes = true →
              0 < sig.size →
                Bitcoin.Interpreter.decodeNum { } (LnLean.Proofs.Bitcoin.SpendTargets.delayBytes csv) 5 = Except.ok n →
                  0 ≤ n →
                    Int.toNat n &&& Bitcoin.Interpreter.SEQUENCE_LOCKTIME_DISABLE_FLAG = 0 →
                      Bitcoin.Interpreter.checkSequenceDef
                            (LnLean.Proofs.Bitcoin.SighashBridgeTargets.locktimeEnvOf tx nIn) n =
                          true →
                        M.ecdsaVerify delayedPaymentKey
                              (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn
                                (Bitcoin.Script.Parser.serializeOpcodes
                                  (LnLean.Proofs.Bitcoin.InterpreterBridgeTargets.toLocalOps revocationKey
                                    delayedPaymentKey csv))
                                (LnLean.Proofs.Bitcoin.SighashBridgeTargets.hashtypeOf sig) amount)
                              { bytes := sig.extract 0 (sig.size - 1) } =
                            true →
                          Bitcoin.Interpreter.verifyWitnessProgram 10
                                [sig, ByteArray.empty,
                                  Bitcoin.Script.Parser.serializeOpcodes
                                    (LnLean.Proofs.Bitcoin.InterpreterBridgeTargets.toLocalOps revocationKey
                                      delayedPaymentKey csv)]
                                0
                                (Bitcoin.Interpreter.hashSha256
                                  (Bitcoin.Script.Parser.serializeOpcodes
                                    (LnLean.Proofs.Bitcoin.InterpreterBridgeTargets.toLocalOps revocationKey
                                      delayedPaymentKey csv)))
                                { csv := true } { }
                                (LnLean.Proofs.Bitcoin.SighashBridgeTargets.checkerOf
                                  Bitcoin.Crypto.Ecdsa.Verify.verifyImpl tx nIn amount)
                                false =
                              Bitcoin.Interpreter.VerifyOutcome.ok ∧
                            LnLean.Proofs.Bitcoin.SpendTargets.P2WSHSpend
                                (LnLean.Proofs.Bitcoin.InterpreterBridgeTargets.vendorLawsCSV
                                  (LnLean.Proofs.Bitcoin.SighashBridgeTargets.checkerOf
                                    Bitcoin.Crypto.Ecdsa.Verify.verifyImpl tx nIn amount)
                                  (Bitcoin.Script.Parser.serializeOpcodes
                                    (LnLean.Proofs.Bitcoin.InterpreterBridgeTargets.toLocalOps revocationKey
                                      delayedPaymentKey csv))
                                  n)
                                (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn
                                  (Bitcoin.Script.Parser.serializeOpcodes
                                    (LnLean.Proofs.Bitcoin.InterpreterBridgeTargets.toLocalOps revocationKey
                                      delayedPaymentKey csv))
                                  (LnLean.Proofs.Bitcoin.SighashBridgeTargets.hashtypeOf sig) amount)
                                (Bitcoin.Interpreter.hashSha256
                                  (Bitcoin.Script.Parser.serializeOpcodes
                                    (LnLean.Proofs.Bitcoin.InterpreterBridgeTargets.toLocalOps revocationKey
                                      delayedPaymentKey csv)))
                                (Bitcoin.Script.Parser.serializeOpcodes
                                  (LnLean.Proofs.Bitcoin.InterpreterBridgeTargets.toLocalOps revocationKey
                                    delayedPaymentKey csv))
                                (LnLean.Proofs.Bitcoin.SpendTargets.toLocalProg revocationKey delayedPaymentKey csv)
                                [LnLean.Proofs.Bitcoin.SpendTargets.zeroByte, sig] ∧
                              (LnLean.Proofs.Bitcoin.SighashBridgeTargets.checkerOf
                                        Bitcoin.Crypto.Ecdsa.Verify.verifyImpl tx nIn amount).base.checkECDSASignature
                                  sig delayedPaymentKey.bytes
                                  (Bitcoin.Script.Parser.serializeOpcodes
                                    (LnLean.Proofs.Bitcoin.InterpreterBridgeTargets.toLocalOps revocationKey
                                      delayedPaymentKey csv))
                                  Bitcoin.Crypto.Seam.SigVersion.witnessV0 default =
                                true
toLocal_revocation_interpreters_agree_vendor : ∀ (M : LnLean.Crypto.PrimitiveModel),
  VendorEcdsaBridge M →
    ∀ (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Bitcoin.Data.Amount)
      (revocationKey delayedPaymentKey : LnLean.PubKey) (csv : LnLean.Blocks) (sig : ByteArray),
      revocationKey.bytes.size = 33 →
        delayedPaymentKey.bytes.size = 33 →
          sig.size ≤ 520 →
            Bitcoin.Crypto.Seam.Der.isValidPubKey revocationKey.bytes = true →
              0 < sig.size →
                M.ecdsaVerify revocationKey
                      (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn
                        (Bitcoin.Script.Parser.serializeOpcodes
                          (LnLean.Proofs.Bitcoin.InterpreterBridgeTargets.toLocalOps revocationKey delayedPaymentKey
                            csv))
                        (LnLean.Proofs.Bitcoin.SighashBridgeTargets.hashtypeOf sig) amount)
                      { bytes := sig.extract 0 (sig.size - 1) } =
                    true →
                  Bitcoin.Interpreter.verifyWitnessProgram 10
                        [sig, LnLean.Proofs.Bitcoin.InterpreterRevocationTargets.revocationSelector,
                          Bitcoin.Script.Parser.serializeOpcodes
                            (LnLean.Proofs.Bitcoin.InterpreterBridgeTargets.toLocalOps revocationKey delayedPaymentKey
                              csv)]
                        0
                        (Bitcoin.Interpreter.hashSha256
                          (Bitcoin.Script.Parser.serializeOpcodes
                            (LnLean.Proofs.Bitcoin.InterpreterBridgeTargets.toLocalOps revocationKey delayedPaymentKey
                              csv)))
                        { csv := true } { }
                        (LnLean.Proofs.Bitcoin.SighashBridgeTargets.checkerOf Bitcoin.Crypto.Ecdsa.Verify.verifyImpl tx
                          nIn amount)
                        false =
                      Bitcoin.Interpreter.VerifyOutcome.ok ∧
                    LnLean.Proofs.Bitcoin.SpendTargets.P2WSHSpend
                      (LnLean.Proofs.Bitcoin.InterpreterBridgeTargets.vendorLaws
                        (LnLean.Proofs.Bitcoin.SighashBridgeTargets.checkerOf Bitcoin.Crypto.Ecdsa.Verify.verifyImpl tx
                          nIn amount)
                        (Bitcoin.Script.Parser.serializeOpcodes
                          (LnLean.Proofs.Bitcoin.InterpreterBridgeTargets.toLocalOps revocationKey delayedPaymentKey
                            csv)))
                      (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn
                        (Bitcoin.Script.Parser.serializeOpcodes
                          (LnLean.Proofs.Bitcoin.InterpreterBridgeTargets.toLocalOps revocationKey delayedPaymentKey
                            csv))
                        (LnLean.Proofs.Bitcoin.SighashBridgeTargets.hashtypeOf sig) amount)
                      (Bitcoin.Interpreter.hashSha256
                        (Bitcoin.Script.Parser.serializeOpcodes
                          (LnLean.Proofs.Bitcoin.InterpreterBridgeTargets.toLocalOps revocationKey delayedPaymentKey
                            csv)))
                      (LnLean.Bitcoin.toLocalScriptFull revocationKey delayedPaymentKey csv).bytes
                      (LnLean.Proofs.Bitcoin.SpendTargets.toLocalProg revocationKey delayedPaymentKey csv)
                      [LnLean.Proofs.Bitcoin.SpendTargets.oneByte, sig]
withVendorEcdsa_ecdsaVerify : ∀ (M₀ : LnLean.Crypto.PrimitiveModel) (hEuf : LnLean.Crypto.EufCma vendorVerify),
  (withVendorEcdsa M₀ hEuf).ecdsaVerify = vendorVerify
withVendorEcdsa_sha256_collisionResistant : ∀ (M₀ : LnLean.Crypto.PrimitiveModel)
  (hEuf : LnLean.Crypto.EufCma vendorVerify), LnLean.Crypto.CollisionResistant (withVendorEcdsa M₀ hEuf).sha256
withVendorEcdsa_eufCma : ∀ (M₀ : LnLean.Crypto.PrimitiveModel) (hEuf : LnLean.Crypto.EufCma vendorVerify),
  LnLean.Crypto.EufCma (withVendorEcdsa M₀ hEuf).ecdsaVerify
withVendorEcdsa_bridge : ∀ (M₀ : LnLean.Crypto.PrimitiveModel) (hEuf : LnLean.Crypto.EufCma vendorVerify),
  VendorEcdsaBridge (withVendorEcdsa M₀ hEuf)
verifyFundingChecked_withVendor_iff : ∀ (M₀ : LnLean.Crypto.PrimitiveModel) (hEuf : LnLean.Crypto.EufCma vendorVerify)
  (key : LnLean.PubKey) (tx : ByteArray) (sig : LnLean.EcdsaSig),
  LnLean.Crypto.verifyFundingChecked (withVendorEcdsa M₀ hEuf) key tx sig = true ↔ fundingValidVendor key tx sig
fundingSignedValid_withVendor_iff : ∀ (M₀ : LnLean.Crypto.PrimitiveModel) (hEuf : LnLean.Crypto.EufCma vendorVerify)
  (fundingKey : LnLean.PubKey) (fundingTx : ByteArray) (m : LnLean.Protocol.FundingSigned),
  LnLean.Proofs.WaveE.E19.fundingSignedValid (withVendorEcdsa M₀ hEuf) fundingKey fundingTx m ↔
    fundingValidVendor fundingKey fundingTx m.signature
withVendor_verifyImpl_funding_message_bound : ∀ (M₀ : LnLean.Crypto.PrimitiveModel),
  LnLean.Crypto.EufCma vendorVerify →
    ∀ {key : LnLean.PubKey} {m₁ m₂ : ByteArray} {sig : LnLean.EcdsaSig},
      Bitcoin.Crypto.Ecdsa.Verify.verifyImpl sig.bytes key.bytes (LnLean.Crypto.fundingTag ++ m₁) = true →
        Bitcoin.Crypto.Ecdsa.Verify.verifyImpl sig.bytes key.bytes (LnLean.Crypto.fundingTag ++ m₂) = true → m₁ = m₂
```
