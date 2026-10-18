# S6-PR-VIEWBIND — domain-separated commitment and digest→view binding

**Lane:** `S6-PR-VIEWBIND` (issues `PR-06`, `PR-02`).
**Repository:** `/home/ubuntu/ln-lean-repair`
**Branch / base:** `repair/integrated` at `201a0a0` (wave-6 launch).
**Toolchain:** `leanprover/lean4:v4.35.0`.
**Verdict:** complete for the assigned scope. The lane adds a
domain-separated commitment value, isolates the cryptographic and encoding
halves of view binding as explicit hypotheses, proves that a valid C3
signature over the digest binds the commitment/HTLC view under those
hypotheses, and keeps a full mechanized counterexample showing that C1 as
formalized plus C3 do **not** imply view binding. No global SHA-256 injectivity
is assumed.

- Lane files (exclusive ownership, both new):
  - `LnLean/Proofs/Channel/SighashViewBindingTargets.lean` — 868 lines.
  - `agents/reports/swarm6/S6-PR-VIEWBIND.md` — this report.
- Not modified: `SighashTargets.lean`, `LnLean.lean`, `Obligations.lean`,
  `Traceability.lean`, `LnLean/Proofs/PhaseC3/AxiomAudit.lean`,
  `scripts/check-final.py`, shared docs/scripts, other lanes' files, and
  `vendor/**`. No Git write was made.
- The other modified/untracked files visible in `git status` belong to
  concurrent wave-6 lanes and were left untouched.

## 1. Result in one paragraph

Wave 5 proved that C3 (`EufCma`) binds a produced commitment signature to the
**digest** `commitmentDigest M v`; it did not prove that equal digests imply
equal commitment/HTLC **views**, because the model's C1 field
(`CollisionResistant M.sha256`) is injectivity only on **32-byte** preimages
while a tagged commitment preimage is at least 39 bytes. This lane names the
signed value as an explicit domain-separated commitment,
`viewCommitment v = commitmentTag ++ commitmentPreimage v`, and states the
missing bridge in two parts on a finite admissible list:
`SerializationBindsViews views` (the serializer is injective on those views)
and `ViewDigestCollisionFree M views` (the hash is collision-free on their
tagged serializations). Under those hypotheses and C3, a produced commitment
signature that verifies for any admissible view's digest forces that view to be
`viewOfState ctx st`; the per-HTLC analogue binds both the HTLC view and its
parent commitment view. The hypotheses are non-vacuous, and the counterexample
`digest_binding_not_view_binding` shows why they cannot be dropped: a full
`PrimitiveModel` satisfying C1 and C3 has two distinct views with the same
digest and one signature valid for both.

## 2. Required build and observed result

### 2.1 Official command in the shared tree

```sh
cd /home/ubuntu/ln-lean-repair
export PATH=/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Proofs.Channel.SighashViewBindingTargets
```

Observed: **build failed before reaching the lane module**, in the shared
dependency `LnLean/Proofs/Conservation.lean`, because the concurrent
`S6-CH-TYPES` lane added `CommitmentHTLCOutput.netAmountSat` to
`LnLean/Channel/Types.lean` and the old four-field `LawfulBEq` instance in
`Conservation.lean` no longer matches the five-field constructor. The failure
persisted on the final re-run after other lanes had advanced the build graph.

```text
✖ [16/34] Building LnLean.Proofs.Conservation (2.3s)
error: LnLean/Proofs/Conservation.lean:649:68: Application type mismatch:
  The argument hsa has type
    instBEqHTLCState.beq sa sb = true ∧ netAmountSat✝¹ = netAmountSat✝
  but is expected to have type
    (sa == sb) = true
error: LnLean/Proofs/Conservation.lean:645:23: unsolved goals
  ...
  hsa : instBEqHTLCState.beq sa sb = true ∧ netAmountSat✝¹ = netAmountSat✝
  ⊢ { ... netAmountSat := netAmountSat✝¹ } =
    { ... netAmountSat := netAmountSat✝ }
error: build failed
```

This is outside lane ownership; the exact integration patch is in §9.1.

### 2.2 Typecheck/build in an isolated identical copy

To verify the lane module itself without editing the shared file, the tree was
copied to `/tmp/opencode/s6vb` (excluding `.git`), the five-field
`LawfulBEq` patch was applied there only, and the same module target was built:

```sh
cd /tmp/opencode/s6vb
export PATH=/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
lake build LnLean.Proofs.Channel.SighashViewBindingTargets
```

Observed:

```text
Build completed successfully (34 jobs).
```

No warnings were emitted by the lane module. The module source in the isolated
copy has the same SHA-256 as the deliverable in the shared tree:

```text
92c1cdcc8ab0215e063f19feea4ebd888fed0879275e1fa2c785b0053b3497d8
  LnLean/Proofs/Channel/SighashViewBindingTargets.lean
```

The imported dependency sources `SighashTargets.lean`,
`Crypto/EcdsaProps.lean`, `ProtocolWireTargets.lean`, `Crypto/Model.lean`, and
`Crypto/Sig.lean` also compare byte-identical between the shared tree and the
isolated copy. No full `lake build`, `collect-obligations.py`,
`collect-anchors.py`, or Git write was run.

## 3. Exact signatures

Namespace:
`LnLean.Proofs.Channel.SighashViewBindingTargets`. All names below are relative
to that namespace. `CommitmentSighashView`, `HtlcSighashView`,
`commitmentPreimage`, `htlcPreimage`, `commitmentDigest`, `htlcDigest`,
`SighashProduces`, `viewOfState`, `htlcViewOfState`, `honestFull`,
`CommitmentSigningLaw`, and `SighashContext` are imported from
`LnLean.Proofs.Channel.SighashTargets`; `EufCma`, `CollisionResistant`, and
`PrimitiveModel` from `LnLean.Crypto.Model`.

### 3.1 Domain-separated commitment values

```lean
def viewCommitment (v : CommitmentSighashView) : ByteArray :=
  commitmentTag ++ commitmentPreimage v

def htlcCommitment
    (p : CommitmentSighashView × HtlcSighashView) : ByteArray :=
  commitmentTag ++ commitmentPreimage p.1 ++ htlcPreimage p.2

theorem commitmentDigest_eq_sha256_viewCommitment
    (M : PrimitiveModel) (v : CommitmentSighashView) :
    commitmentDigest M v = M.sha256 (viewCommitment v)

theorem htlcDigest_eq_sha256_htlcCommitment
    (M : PrimitiveModel) (v : CommitmentSighashView)
    (h : HtlcSighashView) :
    htlcDigest M v h = M.sha256 (htlcCommitment (v, h))

theorem viewCommitment_not_fundingDomain
    (v : CommitmentSighashView) (m : ByteArray) :
    viewCommitment v ≠ fundingTag ++ m

theorem commitmentPreimage_size (v : CommitmentSighashView) :
    (commitmentPreimage v).size =
      107 + v.fundingTxid.size + v.fundingScript.size +
        (v.outputs.map
          (fun o => (commitmentOutputBytes o).size)).sum +
        (v.htlcs.map
          (fun h => (htlcPreimage h).size)).sum

theorem commitmentPreimage_size_ge (v : CommitmentSighashView) :
    33 ≤ (commitmentPreimage v).size

theorem taggedPreimage_size_ge (v : CommitmentSighashView) :
    39 ≤ (commitmentTag ++ commitmentPreimage v).size

theorem taggedPreimage_size_ne_32 (v : CommitmentSighashView) :
    (commitmentTag ++ commitmentPreimage v).size ≠ 32
```

`commitmentDigest_eq_sha256_viewCommitment` and
`htlcDigest_eq_sha256_htlcCommitment` are `rfl`: the existing wave-5 digest
definitions already hash exactly the named domain-separated byte strings, so
the lane adds names and structure rather than changing the serializer.
`viewCommitment_not_fundingDomain` uses the existing prefix-freeness of the
`commitmentTag` / `fundingTag`; it is structural and holds for every payload.

### 3.2 The two explicit binding hypotheses

```lean
def ViewDigestCollisionFree (M : PrimitiveModel)
    (views : List CommitmentSighashView) : Prop :=
  ∀ v ∈ views, ∀ w ∈ views,
    commitmentDigest M v = commitmentDigest M w → v = w

def HtlcDigestCollisionFree (M : PrimitiveModel)
    (pairs : List (CommitmentSighashView × HtlcSighashView)) : Prop :=
  ∀ p ∈ pairs, ∀ q ∈ pairs,
    htlcDigest M p.1 p.2 = htlcDigest M q.1 q.2 → p = q

def SerializationBindsViews
    (views : List CommitmentSighashView) : Prop :=
  ∀ v ∈ views, ∀ w ∈ views,
    commitmentPreimage v = commitmentPreimage w → v = w

theorem viewDigestCollisionFree_of_serializationBinds
    {M : PrimitiveModel} {views : List CommitmentSighashView}
    (hser : SerializationBindsViews views)
    (hcol : ∀ v ∈ views, ∀ w ∈ views,
      M.sha256 (viewCommitment v) = M.sha256 (viewCommitment w) →
        viewCommitment v = viewCommitment w) :
    ViewDigestCollisionFree M views
```

The decomposition is deliberate: `hser` is the encoding half and `hcol` is the
cryptographic half. `ViewDigestCollisionFree` is **not** derived from
`M.sha256_collisionResistant`; the counterexample in §4 is exactly a model where
the latter holds and the former fails. The finite list restriction keeps the
hypothesis non-vacuous and prevents a claim of global SHA-256 injectivity.

### 3.3 Main positive theorems

```lean
theorem commitmentSignature_binds_view {M : PrimitiveModel}
    (hC3 : EufCma M.ecdsaVerify) {law : CommitmentSigningLaw M}
    {ctx : SighashContext} {st : SignedState} {f : CommitmentSignedFull}
    (h : SighashProduces M law ctx st f)
    {views : List CommitmentSighashView}
    (hbind : ViewDigestCollisionFree M views)
    (hv : viewOfState ctx st ∈ views)
    {w : CommitmentSighashView} (hw : w ∈ views)
    (hver : M.ecdsaVerify ctx.commitmentKey
      (commitmentTag ++ commitmentDigest M w)
      f.commitmentSignature = true) :
    w = viewOfState ctx st

theorem honestSignature_binds_view {M : PrimitiveModel}
    (hC3 : EufCma M.ecdsaVerify) (law : CommitmentSigningLaw M)
    (ctx : SighashContext) (st : SignedState)
    {views : List CommitmentSighashView}
    (hbind : ViewDigestCollisionFree M views)
    (hv : viewOfState ctx st ∈ views)
    {w : CommitmentSighashView} (hw : w ∈ views)
    (hver : M.ecdsaVerify ctx.commitmentKey
      (commitmentTag ++ commitmentDigest M w)
      (law.sign ctx.commitmentKey
        (commitmentTag ++
          commitmentDigest M (viewOfState ctx st))) = true) :
    w = viewOfState ctx st

theorem commitmentSignature_binds_viewOfState {M : PrimitiveModel}
    (hC3 : EufCma M.ecdsaVerify) {law : CommitmentSigningLaw M}
    {ctx : SighashContext} {st : SignedState} {f : CommitmentSignedFull}
    (h : SighashProduces M law ctx st f)
    {views : List CommitmentSighashView}
    (hbind : ViewDigestCollisionFree M views)
    (hv : viewOfState ctx st ∈ views)
    {ctx' : SighashContext} {st' : SignedState}
    (hv' : viewOfState ctx' st' ∈ views)
    (hver : M.ecdsaVerify ctx.commitmentKey
      (commitmentTag ++
        commitmentDigest M (viewOfState ctx' st'))
      f.commitmentSignature = true) :
    viewOfState ctx' st' = viewOfState ctx st
```

`commitmentSignature_binds_view` and
`commitmentSignature_binds_viewOfState` are the main `PR-06` result.
`honestSignature_binds_view` is the same statement for an honest signing law,
without needing a `SighashProduces` witness.

The field-level `PR-02` consequence is:

```lean
theorem signature_binds_commitment_view_fields {M : PrimitiveModel}
    (hC3 : EufCma M.ecdsaVerify) {law : CommitmentSigningLaw M}
    {ctx : SighashContext} {st : SignedState} {f : CommitmentSignedFull}
    (h : SighashProduces M law ctx st f)
    {views : List CommitmentSighashView}
    (hbind : ViewDigestCollisionFree M views)
    (hv : viewOfState ctx st ∈ views)
    {ctx' : SighashContext} {st' : SignedState}
    (hv' : viewOfState ctx' st' ∈ views)
    (hver : M.ecdsaVerify ctx.commitmentKey
      (commitmentTag ++
        commitmentDigest M (viewOfState ctx' st'))
      f.commitmentSignature = true) :
    st'.toCommitment.commitmentOutputs = st.toCommitment.commitmentOutputs ∧
      st'.feeSat = st.feeSat ∧
      st'.holder = st.holder ∧
      st'.commitmentNumber = st.commitmentNumber ∧
      st'.toLocalSat = st.toLocalSat ∧
      st'.toRemoteSat = st.toRemoteSat ∧
      st'.fundingValueSat = st.fundingValueSat ∧
      st'.contestDelay = st.contestDelay ∧
      st'.anchorOutputs = st.anchorOutputs ∧
      st'.feerate = st.feerate ∧
      htlcViewsOfState ctx' st' = htlcViewsOfState ctx st
```

The full view equality is stronger than this projection: it also fixes the
context-derived commitment-view fields (`obscuredCommitmentNumber`,
`fundingTxid`, `fundingOutputIndex`, `fundingScript`) because they are fields
of `CommitmentSighashView`; the embedded HTLC views carry
`secondStageFeeSat`. The projection theorem states the state-record fields
explicitly; the equality theorem is the strongest form to use when a consumer
needs the context side as well.

### 3.4 Second-stage HTLC binding

```lean
theorem htlcSignature_binds_htlcView {M : PrimitiveModel}
    (hC3 : EufCma M.ecdsaVerify) {law : CommitmentSigningLaw M}
    {ctx : SighashContext} {st : SignedState} {f : CommitmentSignedFull}
    (h : SighashProduces M law ctx st f)
    {pairs : List (CommitmentSighashView × HtlcSighashView)}
    (hbind : HtlcDigestCollisionFree M pairs)
    {hh : SignedHtlc} (hmem : hh ∈ st.htlcs)
    (hp : (viewOfState ctx st, htlcViewOfState ctx st hh) ∈ pairs)
    {w : CommitmentSighashView} {g : HtlcSighashView}
    (hq : (w, g) ∈ pairs)
    (hver : M.ecdsaVerify ctx.commitmentKey
      (commitmentTag ++ htlcDigest M w g)
      (entryOfSighash M law ctx st hh).signature = true) :
    w = viewOfState ctx st ∧
      g = htlcViewOfState ctx st hh

theorem htlcSignature_binds_htlc_fields {M : PrimitiveModel}
    (hC3 : EufCma M.ecdsaVerify) {law : CommitmentSigningLaw M}
    {ctx : SighashContext} {st : SignedState} {f : CommitmentSignedFull}
    (h : SighashProduces M law ctx st f)
    {pairs : List (CommitmentSighashView × HtlcSighashView)}
    (hbind : HtlcDigestCollisionFree M pairs)
    {hh : SignedHtlc} (hmem : hh ∈ st.htlcs)
    (hp : (viewOfState ctx st, htlcViewOfState ctx st hh) ∈ pairs)
    {w : CommitmentSighashView} {g : HtlcSighashView}
    (hq : (w, g) ∈ pairs)
    (hver : M.ecdsaVerify ctx.commitmentKey
      (commitmentTag ++ htlcDigest M w g)
      (entryOfSighash M law ctx st hh).signature = true) :
    w = viewOfState ctx st ∧
      g.htlcId = hh.htlcId ∧
      g.parentCommitmentNumber = st.commitmentNumber ∧
      g.direction = hh.direction ∧
      g.htlcState = hh.htlcState ∧
      g.amountSat = hh.amount.toSatFloor ∧
      g.paymentHash = hh.paymentHash ∧
      g.cltvExpiry = hh.cltvExpiry ∧
      g.secondStageFeeSat = ctx.secondStageFeeSat
```

The parent commitment view is bound simultaneously, so a second-stage signature
cannot be moved to another commitment number or another HTLC view even if the
per-HTLC fields happen to match.

### 3.5 What C3 alone gives

```lean
theorem honestSignature_excludes_distinct_digest {M : PrimitiveModel}
    (hC3 : EufCma M.ecdsaVerify) (law : CommitmentSigningLaw M)
    (ctx : SighashContext) (st : SignedState)
    {w : CommitmentSighashView}
    (hne : commitmentDigest M w ≠
      commitmentDigest M (viewOfState ctx st)) :
    M.ecdsaVerify ctx.commitmentKey
      (commitmentTag ++ commitmentDigest M w)
      (law.sign ctx.commitmentKey
        (commitmentTag ++
          commitmentDigest M (viewOfState ctx st))) ≠ true

theorem produced_signature_not_funding {M : PrimitiveModel}
    (hC3 : EufCma M.ecdsaVerify) {law : CommitmentSigningLaw M}
    {ctx : SighashContext} {st : SignedState} {f : CommitmentSignedFull}
    (h : SighashProduces M law ctx st f)
    (hf : verifyFunding M ctx.commitmentKey
      (commitmentDigest M (viewOfState ctx st))
      f.commitmentSignature = true) :
    False
```

The first theorem is the exact boundary: C3 excludes a view only when its
**digest differs**. The second records the unchanged domain-separation negative
against the funding domain.

### 3.6 Non-vacuity

```lean
theorem viewDigestCollisionFree_nil (M : PrimitiveModel) :
    ViewDigestCollisionFree M []

theorem viewDigestCollisionFree_singleton (M : PrimitiveModel)
    (v : CommitmentSighashView) :
    ViewDigestCollisionFree M [v]

theorem viewDigestCollisionFree_pair (M : PrimitiveModel)
    {v w : CommitmentSighashView}
    (hne : commitmentDigest M v ≠ commitmentDigest M w) :
    ViewDigestCollisionFree M [v, w]

theorem htlcDigestCollisionFree_singleton (M : PrimitiveModel)
    (p : CommitmentSighashView × HtlcSighashView) :
    HtlcDigestCollisionFree M [p]

theorem example_honestFull_binds_view (M : PrimitiveModel)
    (hC3 : EufCma M.ecdsaVerify) (law : CommitmentSigningLaw M)
    (ctx : SighashContext) {w : CommitmentSighashView}
    (hw : w ∈ [viewOfState ctx exampleSignedState])
    (hver : M.ecdsaVerify ctx.commitmentKey
      (commitmentTag ++ commitmentDigest M w)
      (honestFull M law ctx exampleSignedState).commitmentSignature = true) :
    w = viewOfState ctx exampleSignedState
```

The singleton instance is deliberately the weakest admissible-list case, but
it is a genuine instantiation on the concrete `exampleSignedState`; the pair
lemma gives the useful non-vacuous two-view case whenever the digests differ.

### 3.7 Counterexample and scope negatives

```lean
def zeroBytes (n : Nat) : ByteArray

def widthOrZero (w : Nat) (b : ByteArray) : ByteArray

def lazySha256 (b : ByteArray) : ByteArray :=
  widthOrZero 32 b

def lazyModel (d₀ : ByteArray) : PrimitiveModel

def viewCollisionModel : PrimitiveModel :=
  lazyModel viewBindingTestMessage

theorem lazySha256_size (b : ByteArray) :
    (lazySha256 b).size = 32

theorem lazySha256_collisionResistant :
    CollisionResistant lazySha256

theorem lazyModel_commitmentDigest
    (d₀ : ByteArray) (v : CommitmentSighashView) :
    commitmentDigest (lazyModel d₀) v = zeroBytes 32

theorem viewCollisionModel_digest (v : CommitmentSighashView) :
    commitmentDigest viewCollisionModel v = zeroBytes 32

theorem digest_binding_not_view_binding :
    ∃ (M : PrimitiveModel) (pk : PubKey) (sig : EcdsaSig)
      (v w : CommitmentSighashView),
      v ≠ w ∧
        CollisionResistant M.sha256 ∧
        EufCma M.ecdsaVerify ∧
        CommitmentSignedBy M pk v sig ∧
        CommitmentSignedBy M pk w sig

theorem viewCollisionModel_not_viewBinding :
    ¬ (∀ v w : CommitmentSighashView,
        commitmentDigest viewCollisionModel v =
          commitmentDigest viewCollisionModel w → v = w)

theorem viewOfState_not_injective_in_state (ctx : SighashContext) :
    ∃ st st' : SignedState,
      st ≠ st' ∧ viewOfState ctx st = viewOfState ctx st'

theorem htlcView_ignores_msat_fraction
    (ctx : SighashContext) (st : SignedState) :
    htlcViewOfState ctx st
        { htlcId := 1, amount := ⟨1000⟩,
          paymentHash := ⟨ByteArray.empty⟩,
          direction := .local, htlcState := .offered,
          cltvExpiry := 100, signedDataDigest := ByteArray.empty } =
      htlcViewOfState ctx st
        { htlcId := 1, amount := ⟨1001⟩,
          paymentHash := ⟨ByteArray.empty⟩,
          direction := .local, htlcState := .offered,
          cltvExpiry := 100, signedDataDigest := ByteArray.empty }
```

### 3.8 Bundled summary

`view_binding_summary` (module lines 818–867) is the conjunction of: equal
views giving equal commitment inputs/digests; the main C3-plus-binding
commitment theorem; the second-stage HTLC theorem; singleton non-vacuity; the
mechanized C1+C3 counterexample; and the `viewOfState` non-injectivity
negative. Its exact Lean type is the corresponding conjunction of the
statements displayed in §§3.1, 3.3, 3.4, 3.6, and 3.7. It is guarded by
`set_option linter.unusedVariables false in` only because the bundled
statement has no free variables; it introduces no axiom or trust escape.

## 4. The counterexample in detail

`lazySha256` is `widthOrZero 32`: the identity on inputs of exactly 32 bytes,
and the all-zero 32-byte string on every other input. Lean checks both model
fields it must satisfy:

- `lazySha256_size : ∀ b, (lazySha256 b).size = 32`;
- `lazySha256_collisionResistant : CollisionResistant lazySha256`.

The second is exactly the model's C1 field: injectivity on 32-byte inputs.
`commitmentTag` is six bytes and every canonical commitment preimage is at
least 33 bytes (`commitmentPreimage_size_ge`), so every tagged preimage is at
least 39 bytes (`taggedPreimage_size_ge`) and never 32 bytes
(`taggedPreimage_size_ne_32`). Hence `lazySha256` maps **every** commitment
commitment to `zeroBytes 32` (`lazyModel_commitmentDigest`).

`lazyModel d₀` fills every other `PrimitiveModel` field, including
`ecdsaVerify := singleMessageVerify d₀`; `singleMessageVerify` accepts exactly
one message per key and satisfies `EufCma`
(`eufCma_singleMessage`). `viewCollisionModel` instantiates
`d₀ = commitmentTag ++ zeroBytes 32`. Therefore:

- every view has digest `zeroBytes 32`;
- every message `commitmentTag ++ commitmentDigest M v` is the same test
  message;
- the empty signature is accepted for every view
  (`signedBy_viewCollisionModel`);
- `testView 0` and `testView 1` are distinct but share the digest
  (`testView_zero_ne_one`, `viewCollisionModel_digest`).

`digest_binding_not_view_binding` packages this as one model, one key, one
signature, and two distinct views. This is the mechanized reason the positive
theorems carry `ViewDigestCollisionFree` rather than trying to derive view
binding from `CollisionResistant M.sha256` alone.

The model is not a cryptographic proposal: it is a legitimate **model** of the
existing C1/C3 fields, and its purpose is to refute the implication
`C1 + C3 ⇒ view binding`. It does not refute the positive theorem, which
assumes the extra finite-list collision-freedom hypothesis.

The two scope negatives are independent of the counterexample:

- `viewOfState_not_injective_in_state` changes the stored
  `SignedState.commitmentDigest` field and leaves the canonical view unchanged.
  The serializer derives the digest; it does not read the stored one. View
  binding is binding of the canonical view, not of every signer-side record
  field.
- `htlcView_ignores_msat_fraction` compares 1000 msat and 1001 msat: both floor
  to one satoshi, so the HTLC view is identical. The millisatoshi amount is a
  wire/state detail outside the signed HTLC view. This is a scope boundary, not
  a claim that sub-satoshi differences are signed.

## 5. Axiom audit

Audit file: `/tmp/opencode/s6vb/Audit.lean` (outside the repository). It imports
the lane module and runs `#print axioms` on every headline and negative
declaration. It was run with `lake env lean Audit.lean` in the isolated copy
whose module source has the same SHA-256 as the deliverable. Full observed
output, grouped:

| Declaration | Axioms |
|---|---|
| `commitmentDigest_eq_sha256_viewCommitment` | none |
| `htlcDigest_eq_sha256_htlcCommitment` | none |
| `viewCommitment_not_fundingDomain` | `propext`, `Quot.sound` |
| `commitmentPreimage_size` | `propext`, `Quot.sound` |
| `commitmentPreimage_size_ge` | `propext`, `Quot.sound` |
| `taggedPreimage_size_ne_32` | `propext`, `Quot.sound` |
| `viewDigestCollisionFree_of_serializationBinds` | `propext`, `Quot.sound` |
| `commitmentSignature_binds_view` | `propext`, `Classical.choice`, `Quot.sound` |
| `honestSignature_binds_view` | `propext`, `Classical.choice`, `Quot.sound` |
| `commitmentSignature_binds_viewOfState` | `propext`, `Classical.choice`, `Quot.sound` |
| `signature_binds_commitment_view_fields` | `propext`, `Classical.choice`, `Quot.sound` |
| `htlcSignature_binds_htlcView` | `propext`, `Classical.choice`, `Quot.sound` |
| `htlcSignature_binds_htlc_fields` | `propext`, `Classical.choice`, `Quot.sound` |
| `honestSignature_excludes_distinct_digest` | `propext`, `Classical.choice`, `Quot.sound` |
| `produced_signature_not_funding` | `propext`, `Classical.choice`, `Quot.sound` |
| `viewDigestCollisionFree_nil` | none |
| `viewDigestCollisionFree_singleton` | `propext` |
| `viewDigestCollisionFree_pair` | `propext` |
| `htlcDigestCollisionFree_singleton` | `propext` |
| `example_honestFull_binds_view` | `propext`, `Classical.choice`, `Quot.sound` |
| `lazySha256_collisionResistant` | `propext` |
| `lazyModel_commitmentDigest` | `propext`, `Quot.sound` |
| `viewCollisionModel_digest` | `propext`, `Quot.sound` |
| `digest_binding_not_view_binding` | `propext`, `Quot.sound` |
| `viewCollisionModel_not_viewBinding` | `propext`, `Quot.sound` |
| `viewOfState_not_injective_in_state` | `propext` |
| `htlcView_ignores_msat_fraction` | `propext` |
| `view_binding_summary` | `propext`, `Classical.choice`, `Quot.sound` |

Every declaration depends only on a subset of the allowed axioms
`propext`, `Quot.sound`, `Classical.choice`. No `sorryAx`, no lane-defined
axiom, and no other foundational dependency appears.

## 6. Forbidden-construct scan

Command run on the lane module:

```sh
grep -nE '\b(sorry|axiom|admit|native_decide|unsafe)\b|implemented_by' \
  LnLean/Proofs/Channel/SighashViewBindingTargets.lean
```

Observed: no matches (`CLEAN`). The module contains no `sorry`, `axiom`,
`admit`, `native_decide`, `unsafe`, or `@[implemented_by]`.

## 7. Scope caveats and honest limits

1. **No global SHA-256 injectivity.** The positive theorem assumes
   `ViewDigestCollisionFree M views` on a finite admissible list. It does not
   assume or prove that SHA-256 is injective on all byte strings. C1 remains
   the model's 32-byte injectivity field, and
   `LnLean.Proofs.Crypto.preimageResistant_vacuous` still refutes global
   injectivity for a 32-byte-output hash.
2. **The cryptographic half is an assumption, not a reduction.** There is no
   computational reduction from a real hash to the collision-freedom premise,
   no birthday-bound calculation, and no probability model. The lane isolates
   the assumption; it does not discharge it.
3. **The encoding half is an explicit hypothesis.** `SerializationBindsViews`
   is not proved for arbitrary views. `natBytes` is an eight-byte truncating
   encoding, so it is not injective on unbounded `Nat` fields; the hypothesis
   must be restricted to the admissible views. The module states this boundary
   rather than silently assuming serializer injectivity.
4. **The serializer is still the wave-5 structural BOLT 3-shaped model, not a
   bit-exact transaction encoder.** `PR-05` (exact byte layout) is a separate
   lane. Scripts are opaque context bytes; the model does not derive them from
   funding keys. The exact preimage width formula is proved, but bit-exactness
   against Bitcoin consensus is not claimed here.
5. **The admissible list is finite.** `ViewDigestCollisionFree` and
   `HtlcDigestCollisionFree` are list-indexed. They are non-vacuous and usable
   for concrete states, but they are not global statements about all possible
   views.
6. **No secret-key model.** Signing laws are keyed by the public key, the same
   idealization as the wave-5 `SighashTargets` and handshake modules. There is
   no private-key extraction or nonce model (`PR-01` remains separate).
7. **View binding is not state-record binding.** A signature binds the
   canonical commitment/HTLC view. It does not bind the stored
   `SignedState.commitmentDigest` field, the per-HTLC `signedDataDigest` field,
   or sub-satoshi HTLC fractions; the two scope negatives above are mechanized.
8. **C3 plus C1 alone is insufficient.** The counterexample is part of the
   deliverable and must not be removed when integrating. It is the formal
   justification for the extra hypothesis in the positive theorem.

## 8. Integration steps for the parent

1. **Apply the shared-file dependency fix in §9.1.** This is required before
   any module importing `SighashTargets` can build in the shared tree.
2. **Root import.** Add, after line 49 of `LnLean.lean`
   (`import LnLean.Proofs.Channel.SighashTargets`):
   ```lean
   import LnLean.Proofs.Channel.SighashViewBindingTargets
   ```
3. **Axiom audit entries.** In `LnLean/Proofs/PhaseC3/AxiomAudit.lean`, add the
   import and the headline `#print axioms` lines. Suggested mandatory entries:
   ```lean
   #print axioms LnLean.Proofs.Channel.SighashViewBindingTargets.commitmentSignature_binds_view
   #print axioms LnLean.Proofs.Channel.SighashViewBindingTargets.htlcSignature_binds_htlcView
   #print axioms LnLean.Proofs.Channel.SighashViewBindingTargets.signature_binds_commitment_view_fields
   #print axioms LnLean.Proofs.Channel.SighashViewBindingTargets.digest_binding_not_view_binding
   #print axioms LnLean.Proofs.Channel.SighashViewBindingTargets.viewCollisionModel_not_viewBinding
   #print axioms LnLean.Proofs.Channel.SighashViewBindingTargets.view_binding_summary
   ```
   and add those names to the audit's summary string near lines 365–368.
4. **Catalog / theorem index.** Add the lane to the `PR-06` / `PR-02` rows in
   `docs/OPEN-ISSUES.md` and to the `LN-PR-004` row/narrative in
   `docs/THEOREM-INDEX.md` (or a new `LN-PR-005` row if the parent prefers a
   separate view-binding entry). Suggested headline set:
   `commitmentSignature_binds_view`,
   `commitmentSignature_binds_viewOfState`,
   `signature_binds_commitment_view_fields`,
   `htlcSignature_binds_htlcView`, and `digest_binding_not_view_binding`.
   Record `PR-06` as a conditional closure: the digest→view gap is now an
   explicit named hypothesis, not an unstated one.
5. **Do not mark `PR-06` unconditionally closed.** The remaining assumption
   `ViewDigestCollisionFree` is cryptographic and list-indexed; the catalog
   should say so. `PR-02` is strengthened by the view/field theorems but remains
   narrowed by the structural serializer and the explicit encoding hypothesis.
6. **Run the gate only after all lanes are merged.** Do not use this lane's
   isolated build as gate evidence for the shared tree. The final gate should
   include the module in the full `lake build`, the strict catalog audit,
   `check.sh`, `check-final.py`, `check-conformance.py`,
   `verify-anchors.py`, `verify-vendor.sh`, and the exact forbidden-construct
   scan.

## 9. Blockers

### 9.1 Shared-tree blocker: five-field `LawfulBEq CommitmentHTLCOutput`

`LnLean/Channel/Types.lean` (owned by `S6-CH-TYPES`) now has:

```lean
structure CommitmentHTLCOutput where
  direction : Direction
  amountSat : Nat
  cltvExpiry : Height
  state : HTLCState
  netAmountSat : Nat := amountSat
```

`LnLean/Proofs/Conservation.lean` still has a four-field private
`LawfulBEq CommitmentHTLCOutput` instance at lines 645–660. The exact
integration patch, validated in `/tmp/opencode/s6vb`, is:

```lean
private instance : LawfulBEq CommitmentHTLCOutput where
  eq_of_beq := by
    intro a b h
    cases a with
    | mk da aa ca sa na =>
      cases b with
      | mk db ab cb sb nb =>
        simp [BEq.beq, instBEqCommitmentHTLCOutput.beq] at h
        rcases h with ⟨hda, haa, hca, hsa, hna⟩
        have hda' : da = db := LawfulBEq.eq_of_beq (α := Direction) hda
        have hsa' : sa = sb := LawfulBEq.eq_of_beq (α := HTLCState) hsa
        rw [hda', haa, hca, hsa', hna]
  rfl := by
    intro a
    cases a with
    | mk d am c s n =>
      have hd : instBEqDirection.beq d d = true := by cases d <;> rfl
      have hs : instBEqHTLCState.beq s s = true := by cases s <;> rfl
      simp [BEq.beq, instBEqCommitmentHTLCOutput.beq, hd, hs]
```

This file is outside the lane's ownership, so it was not edited. With that
patch, the isolated copy builds the lane module successfully
(`Build completed successfully (34 jobs)`).

### 9.2 No blocker in the lane module

No missing vendor opcode, missing import, or unproved lane obligation was
found. The only reason the official shared-tree command does not reach the
lane module is the unrelated shared dependency above.

## 10. Final summary for the parent

`S6-PR-VIEWBIND` is complete for its assigned scope. The new module
`LnLean/Proofs/Channel/SighashViewBindingTargets.lean` names the signed
commitment value as `commitmentTag ++ commitmentPreimage v`, proves the
existing digest is its SHA-256 image by `rfl`, and proves structural domain
separation from funding. It isolates view binding into
`ViewDigestCollisionFree` (cryptographic half) and
`SerializationBindsViews` (encoding half), composes them, and proves under C3
plus collision-freedom that a produced commitment signature binds
`viewOfState ctx st`, including the field-level and across-state forms. It
proves the analogous second-stage result binding both the HTLC view and its
parent commitment view. It supplies empty/singleton/pair non-vacuity lemmas and
instantiates the theorem on `exampleSignedState`. It mechanizes the essential
negative: a full `PrimitiveModel` satisfying C1 and C3 has two distinct views
with the same digest and one signature valid for both, so digest binding alone
is insufficient; it also records that view binding is not state-record binding
and that the HTLC view floors millisatoshi amounts. The module builds cleanly
(34 jobs) in an isolated copy with an identical source hash, and its `#print
axioms` audit shows only `propext`, `Quot.sound`, and `Classical.choice`; the
forbidden-construct scan is clean. The official shared-tree build is currently
blocked before this module by the unrelated five-field
`LawfulBEq CommitmentHTLCOutput` break in `Conservation.lean`; the exact
one-instance patch is given in §9.1. Integration requires that fix, the root
import, the AxiomAudit entries, and catalog/traceability rows; `PR-06` should be
recorded as conditionally closed with the named collision-freedom hypothesis,
not as an unconditional proof of SHA-256 view injectivity.
