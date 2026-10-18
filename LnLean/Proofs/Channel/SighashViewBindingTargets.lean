/-
# Sighash view binding targets — domain-separated commitment and digest→view binding (PR-06, PR-02)

**Catalog issues.**

* `PR-06` (P1): C3 (`EufCma`) binds a commitment signature to the *digest*
  `commitmentDigest M v`.  Nothing in the wave-5 module says that equal digests
  imply equal commitment/HTLC *views*, because the model's C1 field
  (`CollisionResistant M.sha256`) is injectivity only on **32-byte** preimages,
  while a serialized commitment preimage is longer.  The digest-to-view gap was
  stated, correctly, as an open cryptographic assumption.
* `PR-02` (P1): the wave-5 serializer derives the digest and the signature from
  the state, but "what a signature covers" was still only the digest.  A
  faithful view-binding statement has to say which canonical serialization the
  digest is a commitment to, and which part of the state that serialization
  determines.

**Result of this module.**

1. The signed commitment input is identified as an explicit
   **domain-separated commitment** value: `viewCommitment v` is the commitment
   domain tag `LnLean.Crypto.commitmentTag` followed by the wave-5 canonical
   preimage, so `commitmentDigest M v = M.sha256 (viewCommitment v)` by
   definition.  Domain separation is structural: a commitment-domain encoding
   is never equal to a funding-domain encoding for *any* pair of payloads
   (`viewCommitment_not_fundingDomain`, via the existing prefix-freeness of the
   tags).
2. Two explicit hypotheses are separated, instead of being hidden in one:
   * `ViewDigestCollisionFree M views` — the model's SHA-256 is collision-free
     on the *tagged commitment serializations* of the admissible views.  This
     is the cryptographic half; it is **not** derivable from
     `CollisionResistant M.sha256` (see item 6) and it is **not** an assumption
     of global SHA-256 injectivity.
   * `SerializationBindsViews views` — the canonical serializer is injective on
     the admissible views.  This is the encoding half.  It is *false* for
     arbitrary naturals because the 8-byte `natBytes` field truncates
     (`256^8`), so it must be restricted; the module keeps it as an explicit
     hypothesis and states the truncation boundary.
   `viewDigestCollisionFree_of_serializationBinds` composes the two: a SHA-256
   collision-freedom hypothesis **on the serializer image** plus serializer
   injectivity gives view binding.
3. **Main positive theorem.**  Under `ViewDigestCollisionFree` and C3, a
   commitment signature produced by `SighashProduces` — or by an honest signing
   law — that verifies for the digest of *any* admissible view `w` forces
   `w = viewOfState ctx st`.  The per-HTLC analogue
   (`htlcSignature_binds_htlcView`) binds the **pair** of the second-stage HTLC
   view and its parent commitment view, so a second-stage signature cannot be
   moved to another commitment number or another HTLC view.
4. Concrete consequences: the bound view determines the commitment output list,
   the fee, `to_local`/`to_remote`, the contest delay, the anchor flag, the
   feerate, the commitment number, and the full HTLC view list
   (`signature_binds_commitment_view_fields`); the bound HTLC view determines
   its id, parent commitment number, direction, lifecycle, satoshi amount,
   payment hash, CLTV expiry, and second-stage fee
   (`htlcSignature_binds_htlc_fields`).
5. The hypotheses are non-vacuous and finite: `ViewDigestCollisionFree` holds
   for the empty and singleton view lists and for a pair of views with
   *different* digests, so the main theorem is instantiated on the concrete
   `exampleSignedState`.
6. **Mechanized counterexample — digest binding alone is insufficient.**  A
   full `PrimitiveModel` (`lazyModel`) is built whose `sha256` is the identity
   on 32-byte inputs and the all-zero 32-byte string elsewhere.  It satisfies
   the model's `sha256_size` **and** `sha256_collisionResistant` fields
   (`lazySha256_collisionResistant`), so it is a legitimate model of C1, and its
   ECDSA verifier is the single-message verifier, so it satisfies C3.  In that
   model two *distinct* views have the same commitment digest, and one
   signature is a valid `CommitmentSignedBy` signature for **both**
   (`digest_binding_not_view_binding`).  Hence
   `CollisionResistant M.sha256 + EufCma M.ecdsaVerify` do **not** imply view
   binding, and `viewCollisionModel_not_viewBinding` records the same fact as a
   negated universal.  This is the exact reason the positive theorem carries
   `ViewDigestCollisionFree` as an extra hypothesis rather than assuming global
   SHA-256 injectivity.
7. A second negative shows what view binding does **not** cover:
   `viewOfState` deliberately ignores the state's stored `commitmentDigest`
   field, so two distinct `SignedState` records have the same view
   (`viewOfState_not_injective_in_state`), and the HTLC view commits only to
   satoshi-floored amounts (`htlcView_ignores_msat_fraction`).  View binding is
   binding of the *canonical commitment/HTLC view*, not of every field of the
   signer-side record.

## Scope

This module does **not** prove SHA-256 collision resistance, does **not**
assume global SHA-256 injectivity (which is refuted for a 32-byte-output hash in
`LnLean.Proofs.Crypto.preimageResistant_vacuous`), and does **not** mechanize a
computational reduction.  The cryptographic hypothesis is stated on the range of
the serializer, exactly where C1 does not apply.  The serializer remains the
wave-5 structural BOLT 3-shaped model (`PR-05` is a separate lane); the encoding
half is an explicit hypothesis, not derived from bit-exactness.  The signing law
is keyed by a public key; there is no secret-key model (`PR-01`).

## Anchors

* BOLT 3 §"Commitment Transaction" (`03-transactions.md:83-353`): the signed
  commitment transaction fields (funding outpoint, outputs, obscured commitment
  number) that the serializer orders.
* BOLT 2 §"Committing Updates So Far" (type 132): one commitment signature plus
  one signature per untrimmed HTLC output.
* Model: `LnLean/Proofs/Channel/SighashTargets.lean`
  (`CommitmentSighashView`, `HtlcSighashView`, `commitmentPreimage`,
  `htlcPreimage`, `commitmentDigest`, `htlcDigest`, `SighashProduces`,
  `viewOfState`, `htlcViewOfState`, `honestFull`),
  `LnLean/Crypto/Sig.lean` (`commitmentTag`, `fundingTag`,
  `verifyFunding_not_verifyCommitment`),
  `LnLean/Crypto/Model.lean` (`CollisionResistant`, `EufCma`),
  `LnLean/Proofs/Crypto/EcdsaProps.lean`
  (`singleMessageVerify`, `eufCma_singleMessage`,
  `fundingTag_commitmentTag_prefixFree`),
  `LnLean/Proofs/Crypto/Sha256Props.lean` (`preimageResistant_vacuous`),
  `docs/CRYPTO-LIMITS.md` §2, §7.1 (C1 is 32-byte injectivity; C1 is
  satisfiable and not global injectivity).
-/

import LnLean.Proofs.Channel.SighashTargets
import LnLean.Proofs.Crypto.EcdsaProps
import LnLean.Proofs.ProtocolWireTargets

namespace LnLean.Proofs.Channel.SighashViewBindingTargets

set_option autoImplicit false

open LnLean
open LnLean.Protocol
open LnLean.Channel
open LnLean.Crypto
open LnLean.Proofs
open LnLean.Proofs.ProtocolWireTargets
open LnLean.Proofs.Channel.SighashTargets

/-! ## 1. The domain-separated view commitment

The signed message is `commitmentTag ++ commitmentPreimage v`.  This section
names that byte string, proves it is exactly the input of `commitmentDigest`,
and records the structural domain separation against the funding domain. -/

/-- The domain-separated commitment input of a commitment view: the commitment
domain tag followed by the wave-5 canonical BOLT 3-shaped preimage.  This is
the value a view-binding commitment hashes; `commitmentDigest` is its SHA-256
image by definition. -/
def viewCommitment (v : CommitmentSighashView) : ByteArray :=
  commitmentTag ++ commitmentPreimage v

/-- The domain-separated second-stage commitment input: the commitment domain
tag, the parent commitment preimage, and the per-HTLC preimage.  A second-stage
signature is a commitment to this whole byte string, not only to the HTLC
fields. -/
def htlcCommitment (p : CommitmentSighashView × HtlcSighashView) : ByteArray :=
  commitmentTag ++ commitmentPreimage p.1 ++ htlcPreimage p.2

/-- `commitmentDigest` is literally the SHA-256 image of `viewCommitment`. -/
theorem commitmentDigest_eq_sha256_viewCommitment (M : PrimitiveModel)
    (v : CommitmentSighashView) :
    commitmentDigest M v = M.sha256 (viewCommitment v) := rfl

/-- `htlcDigest` is literally the SHA-256 image of `htlcCommitment`. -/
theorem htlcDigest_eq_sha256_htlcCommitment (M : PrimitiveModel)
    (v : CommitmentSighashView) (h : HtlcSighashView) :
    htlcDigest M v h = M.sha256 (htlcCommitment (v, h)) := rfl

/-- Equal views have equal commitment inputs.  This direction needs no
cryptographic hypothesis: it is extensionality of the serializer. -/
theorem viewCommitment_eq_of_view_eq {v w : CommitmentSighashView} (h : v = w) :
    viewCommitment v = viewCommitment w :=
  congrArg viewCommitment h

/-- Equal views have equal commitment digests. -/
theorem commitmentDigest_eq_of_view_eq (M : PrimitiveModel)
    {v w : CommitmentSighashView} (h : v = w) :
    commitmentDigest M v = commitmentDigest M w :=
  congrArg (commitmentDigest M) h

/-- **Domain separation, structural.**  A commitment-domain encoding can never
be equal to a funding-domain encoding, for *any* pair of payloads.  The
commitment tag and the funding tag are prefix-free
(`fundingTag_commitmentTag_prefixFree`), so a commitment view commitment cannot
be replayed as a funding-tagged message. -/
theorem viewCommitment_not_fundingDomain (v : CommitmentSighashView)
    (m : ByteArray) : viewCommitment v ≠ fundingTag ++ m :=
  (fundingTag_commitmentTag_prefixFree m (commitmentPreimage v)).symm

/-! ### 1.1 Width of the canonical serializer

The counterexample in section 5 needs the fact that a commitment preimage is
longer than 26 bytes, so that prepending the six-byte domain tag can never
produce a 32-byte input (the only inputs on which the lazy hash is injective).
The exact width formula is also the arithmetic boundary of the encoding
hypothesis: `natBytes` is an eight-byte truncating encoding. -/

theorem natBytes_size (n : Nat) : (natBytes n).size = 8 := by
  unfold natBytes
  simp [ByteArray.size, Array.size]

theorem bytesField_size (b : ByteArray) : (bytesField b).size = 8 + b.size := by
  unfold bytesField
  rw [ByteArray.size_append, natBytes_size]

theorem directionBytes_size (d : Direction) : (directionBytes d).size = 1 := by
  cases d <;> rfl

theorem htlcStateBytes_size (s : HTLCState) : (htlcStateBytes s).size = 1 := by
  cases s <;> rfl

theorem boolBytes_size (b : Bool) : (boolBytes b).size = 1 := by
  cases b <;> rfl

theorem oneByte_size (x : UInt8) : (ByteArray.mk #[x]).size = 1 := by
  simp [ByteArray.size, Array.size]

theorem concatBytes_size (l : List ByteArray) :
    (concatBytes l).size = (l.map ByteArray.size).sum := by
  induction l with
  | nil => rfl
  | cons b t ih =>
      simp [concatBytes, ByteArray.size_append, ih, List.sum_cons]

/-- The exact width of a commitment preimage.  The fixed part is 107 bytes; the
variable part is the funding txid, the funding script, and the two encoded
lists. -/
theorem commitmentPreimage_size (v : CommitmentSighashView) :
    (commitmentPreimage v).size =
      107 + v.fundingTxid.size + v.fundingScript.size +
        (v.outputs.map (fun o => (commitmentOutputBytes o).size)).sum +
        (v.htlcs.map (fun h => (htlcPreimage h).size)).sum := by
  simp [commitmentPreimage, natBytes_size, bytesField_size, directionBytes_size,
    boolBytes_size, oneByte_size, concatBytes_size, ByteArray.size_append,
    Function.comp_def]
  omega

/-- Every commitment preimage is at least 33 bytes. -/
theorem commitmentPreimage_size_ge (v : CommitmentSighashView) :
    33 ≤ (commitmentPreimage v).size := by
  rw [commitmentPreimage_size]
  omega

/-- No tagged commitment preimage is 32 bytes, so the lazy hash collapses it. -/
theorem taggedPreimage_size_ge (v : CommitmentSighashView) :
    39 ≤ (commitmentTag ++ commitmentPreimage v).size := by
  rw [ByteArray.size_append, commitmentTag_size]
  have := commitmentPreimage_size_ge v
  omega

theorem taggedPreimage_size_ne_32 (v : CommitmentSighashView) :
    (commitmentTag ++ commitmentPreimage v).size ≠ 32 := by
  have := taggedPreimage_size_ge v
  omega

/-! ## 2. Explicit binding hypotheses

The two halves of the digest-to-view bridge are named separately:

* the **cryptographic** half: SHA-256 is collision-free on the serializer image
  of the admissible views (this is where C1 does not apply, because the
  preimages are longer than 32 bytes);
* the **encoding** half: the serializer itself is injective on the admissible
  views (this fails for unbounded naturals because `natBytes` truncates to
  8 bytes, so it is a real restriction).

Both are predicates over an explicit finite list of admissible views, the same
finite-admission pattern the tree already uses for P2WSH script binding
(`L1-05`) and HMAC tag binding (C8).  A finite list keeps the hypothesis
non-vacuous and prevents any claim of global SHA-256 injectivity. -/

/-- **Cryptographic binding hypothesis.**  On the admissible view list, equal
commitment digests imply equal views.  Equivalently, the model's SHA-256 is
collision-free on the tagged commitment serializations of those views.  This
is *not* a consequence of `CollisionResistant M.sha256`; see
`digest_binding_not_view_binding`. -/
def ViewDigestCollisionFree (M : PrimitiveModel)
    (views : List CommitmentSighashView) : Prop :=
  ∀ v ∈ views, ∀ w ∈ views, commitmentDigest M v = commitmentDigest M w → v = w

/-- **Cryptographic binding hypothesis, second stage.**  On the admissible
pair list, equal second-stage digests imply equal (commitment view, HTLC view)
pairs. -/
def HtlcDigestCollisionFree (M : PrimitiveModel)
    (pairs : List (CommitmentSighashView × HtlcSighashView)) : Prop :=
  ∀ p ∈ pairs, ∀ q ∈ pairs,
    htlcDigest M p.1 p.2 = htlcDigest M q.1 q.2 → p = q

/-- **Encoding binding hypothesis.**  The canonical serializer is injective on
the admissible views.  This is the structural half of view binding; it is
independent of the hash function.  It must be restricted to well-formed views:
`natBytes` is an eight-byte truncating encoding, so it is not injective on
unbounded naturals. -/
def SerializationBindsViews (views : List CommitmentSighashView) : Prop :=
  ∀ v ∈ views, ∀ w ∈ views, commitmentPreimage v = commitmentPreimage w → v = w

/-- The cryptographic hypothesis on the serializer image and the encoding
hypothesis compose to the digest-level hypothesis.  This is the exact
decomposition of "the commitment binds the view": SHA-256 must be collision-free
on the tagged preimages, and the preimage encoding must itself determine the
view. -/
theorem viewDigestCollisionFree_of_serializationBinds {M : PrimitiveModel}
    {views : List CommitmentSighashView}
    (hser : SerializationBindsViews views)
    (hcol : ∀ v ∈ views, ∀ w ∈ views,
      M.sha256 (viewCommitment v) = M.sha256 (viewCommitment w) →
        viewCommitment v = viewCommitment w) :
    ViewDigestCollisionFree M views := by
  intro v hv w hw hd
  have hch : viewCommitment v = viewCommitment w := hcol v hv w hw hd
  have hpre : commitmentPreimage v = commitmentPreimage w :=
    append_left_cancel hch
  exact hser v hv w hw hpre

/-! ## 3. Main positive theorems: a valid C3 signature binds the view -/

/-- **PR-06, main positive direction.**  Let `M` satisfy C3, let `f` be
produced from `(law, ctx, st)` under the wave-5 serializer, and suppose the model
is collision-free on the admissible view list.  If the produced commitment
signature verifies in the commitment domain for the digest of *any* admissible
view `w`, then `w` is exactly the view of `st`.  So the signature binds the
canonical commitment view, not merely the digest. -/
theorem commitmentSignature_binds_view {M : PrimitiveModel}
    (hC3 : EufCma M.ecdsaVerify) {law : CommitmentSigningLaw M}
    {ctx : SighashContext} {st : SignedState} {f : CommitmentSignedFull}
    (h : SighashProduces M law ctx st f)
    {views : List CommitmentSighashView}
    (hbind : ViewDigestCollisionFree M views)
    (hv : viewOfState ctx st ∈ views)
    {w : CommitmentSighashView} (hw : w ∈ views)
    (hver : M.ecdsaVerify ctx.commitmentKey
      (commitmentTag ++ commitmentDigest M w) f.commitmentSignature = true) :
    w = viewOfState ctx st := by
  have hd : commitmentDigest M w = commitmentDigest M (viewOfState ctx st) :=
    SighashProduces.signature_binds_digest hC3 h hver
  exact hbind w hw (viewOfState ctx st) hv hd

/-- The honest-signer form, independent of `SighashProduces`: the honest
signature over the derived digest, verified for the digest of an admissible
view, binds that view.  C3 supplies the digest equality and the binding
hypothesis upgrades it to view equality. -/
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
        (commitmentTag ++ commitmentDigest M (viewOfState ctx st))) = true) :
    w = viewOfState ctx st := by
  have hder : M.ecdsaVerify ctx.commitmentKey
      (commitmentTag ++ commitmentDigest M (viewOfState ctx st))
      (law.sign ctx.commitmentKey
        (commitmentTag ++ commitmentDigest M (viewOfState ctx st))) = true :=
    law.verifies _ _
  have htag : commitmentTag ++ commitmentDigest M w =
      commitmentTag ++ commitmentDigest M (viewOfState ctx st) :=
    hC3 _ _ _ _ hver hder
  have hd : commitmentDigest M w = commitmentDigest M (viewOfState ctx st) :=
    append_left_cancel htag
  exact hbind w hw (viewOfState ctx st) hv hd

/-- **View binding across states.**  A signature that verifies for the view of a
second admissible state forces that state's view to be the first state's view. -/
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
      (commitmentTag ++ commitmentDigest M (viewOfState ctx' st'))
      f.commitmentSignature = true) :
    viewOfState ctx' st' = viewOfState ctx st :=
  commitmentSignature_binds_view hC3 h hbind hv hv' hver

/-- **What view binding yields concretely for states.**  The bound view
determines the commitment output list, the fee, the holder, the commitment
number, the balances, the funding value, the contest delay, the anchor flag, the
feerate, and the whole HTLC view list.  This is the `PR-02` "signature covers a
commitment view" statement at field granularity. -/
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
      (commitmentTag ++ commitmentDigest M (viewOfState ctx' st'))
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
      htlcViewsOfState ctx' st' = htlcViewsOfState ctx st := by
  have hview := commitmentSignature_binds_viewOfState hC3 h hbind hv hv' hver
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [viewOfState] using
      congrArg (fun v : CommitmentSighashView => v.outputs) hview
  · simpa [viewOfState] using
      congrArg (fun v : CommitmentSighashView => v.feeSat) hview
  · simpa [viewOfState] using
      congrArg (fun v : CommitmentSighashView => v.holder) hview
  · simpa [viewOfState] using
      congrArg (fun v : CommitmentSighashView => v.commitmentNumber) hview
  · simpa [viewOfState] using
      congrArg (fun v : CommitmentSighashView => v.toLocalSat) hview
  · simpa [viewOfState] using
      congrArg (fun v : CommitmentSighashView => v.toRemoteSat) hview
  · simpa [viewOfState] using
      congrArg (fun v : CommitmentSighashView => v.fundingValueSat) hview
  · simpa [viewOfState] using
      congrArg (fun v : CommitmentSighashView => v.contestDelay) hview
  · simpa [viewOfState] using
      congrArg (fun v : CommitmentSighashView => v.anchorOutputs) hview
  · have hfr : st'.feerate.msatPerKw = st.feerate.msatPerKw :=
      congrArg (fun v : CommitmentSighashView => v.feeratePerKw) hview
    exact congrArg FeeRate.mk hfr
  · simpa [viewOfState] using
      congrArg (fun v : CommitmentSighashView => v.htlcs) hview

/-- **PR-06, second-stage positive direction.**  Under C3 and collision-freedom
on the admissible second-stage pairs, a produced per-HTLC signature that
verifies for the digest of any admissible `(w, g)` pair forces `(w, g)` to be the
produced pair: the parent commitment view *and* the HTLC view are both bound.
This is why the second-stage digest includes the parent commitment preimage. -/
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
    w = viewOfState ctx st ∧ g = htlcViewOfState ctx st hh := by
  have hd : htlcDigest M w g =
      htlcDigest M (viewOfState ctx st) (htlcViewOfState ctx st hh) :=
    SighashProduces.htlc_signature_binds_digest hC3 h hmem hver
  have hpair : (w, g) = (viewOfState ctx st, htlcViewOfState ctx st hh) :=
    hbind (w, g) hq (viewOfState ctx st, htlcViewOfState ctx st hh) hp hd
  exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩

/-- **What second-stage view binding yields concretely.**  The bound HTLC view
fixes the HTLC id, the parent commitment number, direction, lifecycle, the
satoshi amount, the payment hash, the CLTV expiry, and the second-stage fee.
The parent commitment view is bound simultaneously. -/
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
      g.secondStageFeeSat = ctx.secondStageFeeSat := by
  obtain ⟨hw, hg⟩ := htlcSignature_binds_htlcView hC3 h hbind hmem hp hq hver
  subst hg
  exact ⟨hw, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **What C3 alone gives, in the honest-signer form.**  Without the view-binding
hypothesis the only conclusion is that the verified digest is the derived digest:
a signature can be excluded for any view whose digest differs, but distinct
views with equal digests are not excluded (section 5). -/
theorem honestSignature_excludes_distinct_digest {M : PrimitiveModel}
    (hC3 : EufCma M.ecdsaVerify) (law : CommitmentSigningLaw M)
    (ctx : SighashContext) (st : SignedState)
    {w : CommitmentSighashView}
    (hne : commitmentDigest M w ≠ commitmentDigest M (viewOfState ctx st)) :
    M.ecdsaVerify ctx.commitmentKey
      (commitmentTag ++ commitmentDigest M w)
      (law.sign ctx.commitmentKey
        (commitmentTag ++ commitmentDigest M (viewOfState ctx st))) ≠ true := by
  intro hver
  have hder : M.ecdsaVerify ctx.commitmentKey
      (commitmentTag ++ commitmentDigest M (viewOfState ctx st))
      (law.sign ctx.commitmentKey
        (commitmentTag ++ commitmentDigest M (viewOfState ctx st))) = true :=
    law.verifies _ _
  have htag : commitmentTag ++ commitmentDigest M w =
      commitmentTag ++ commitmentDigest M (viewOfState ctx st) :=
    hC3 _ _ _ _ hver hder
  exact hne (append_left_cancel htag)

/-- A produced commitment signature is never a funding-domain signature over
the same digest payload: the two domains are separated by C3 and the tags. -/
theorem produced_signature_not_funding {M : PrimitiveModel}
    (hC3 : EufCma M.ecdsaVerify) {law : CommitmentSigningLaw M}
    {ctx : SighashContext} {st : SignedState} {f : CommitmentSignedFull}
    (h : SighashProduces M law ctx st f)
    (hf : verifyFunding M ctx.commitmentKey
      (commitmentDigest M (viewOfState ctx st)) f.commitmentSignature = true) :
    False :=
  funding_signature_not_commitment_signature M hC3 hf h.commitmentSignedBy

/-! ## 4. Non-vacuity of the binding hypotheses -/

/-- The binding hypothesis holds on the empty list. -/
theorem viewDigestCollisionFree_nil (M : PrimitiveModel) :
    ViewDigestCollisionFree M [] := by
  intro v hv
  cases hv

/-- The binding hypothesis holds on a singleton list: the only possible pair of
admissible views is the view with itself. -/
theorem viewDigestCollisionFree_singleton (M : PrimitiveModel)
    (v : CommitmentSighashView) : ViewDigestCollisionFree M [v] := by
  intro a ha b hb _
  rw [List.mem_singleton] at ha hb
  rw [ha, hb]

/-- A pair of views with different digests satisfies the binding hypothesis.
This is the useful non-vacuous instance: the hypothesis is exactly "these two
views are not a digest collision". -/
theorem viewDigestCollisionFree_pair (M : PrimitiveModel)
    {v w : CommitmentSighashView}
    (hne : commitmentDigest M v ≠ commitmentDigest M w) :
    ViewDigestCollisionFree M [v, w] := by
  intro a ha b hb heq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · rfl
  · exact absurd heq hne
  · exact absurd heq.symm hne
  · rfl

/-- The second-stage binding hypothesis holds on a singleton pair list. -/
theorem htlcDigestCollisionFree_singleton (M : PrimitiveModel)
    (p : CommitmentSighashView × HtlcSighashView) :
    HtlcDigestCollisionFree M [p] := by
  intro a ha b hb _
  rw [List.mem_singleton] at ha hb
  rw [ha, hb]

/-- **Instantiation on the concrete state.**  The wave-5 `exampleSignedState`
satisfies the main positive theorem with the singleton admissible view list, so
the conditional is not vacuous. -/
theorem example_honestFull_binds_view (M : PrimitiveModel)
    (hC3 : EufCma M.ecdsaVerify) (law : CommitmentSigningLaw M)
    (ctx : SighashContext) {w : CommitmentSighashView}
    (hw : w ∈ [viewOfState ctx exampleSignedState])
    (hver : M.ecdsaVerify ctx.commitmentKey
      (commitmentTag ++ commitmentDigest M w)
      (honestFull M law ctx exampleSignedState).commitmentSignature = true) :
    w = viewOfState ctx exampleSignedState :=
  commitmentSignature_binds_view hC3
    (honestFull_produces M law ctx exampleSignedState)
    (viewDigestCollisionFree_singleton M (viewOfState ctx exampleSignedState))
    (List.mem_singleton_self _) hw hver

/-! ## 5. Negative results: digest binding alone is insufficient -/

/-- The all-zero byte string of the given length. -/
def zeroBytes (n : Nat) : ByteArray :=
  ByteArray.mk (List.replicate n (0 : UInt8)).toArray

theorem zeroBytes_size (n : Nat) : (zeroBytes n).size = n := by
  unfold zeroBytes
  simp [ByteArray.size, Array.size]

/-- A width-padded byte string: the identity on inputs of width `w` and the
all-zero string of width `w` otherwise.  This always has width `w`. -/
def widthOrZero (w : Nat) (b : ByteArray) : ByteArray :=
  if b.size = w then b else zeroBytes w

theorem widthOrZero_size (w : Nat) (b : ByteArray) :
    (widthOrZero w b).size = w := by
  unfold widthOrZero
  split
  · assumption
  · exact zeroBytes_size w

/-- A lazy hash: the identity on 32-byte inputs, the all-zero 32-byte string
otherwise.  It has a 32-byte output and is injective on 32-byte inputs, so it
satisfies the model's C1 field; it is *not* injective on the long preimages a
commitment serializer produces.  `docs/CRYPTO-LIMITS.md` §7.1 uses exactly this
function to show that the C1 field is satisfiable. -/
def lazySha256 (b : ByteArray) : ByteArray :=
  widthOrZero 32 b

theorem lazySha256_size (b : ByteArray) : (lazySha256 b).size = 32 :=
  widthOrZero_size 32 b

theorem lazySha256_of_size {b : ByteArray} (h : b.size = 32) :
    lazySha256 b = b := by
  unfold lazySha256 widthOrZero
  simp [h]

theorem lazySha256_of_ne {b : ByteArray} (h : b.size ≠ 32) :
    lazySha256 b = zeroBytes 32 := by
  unfold lazySha256 widthOrZero
  simp [h]

/-- **Lazy SHA-256 satisfies C1 as formalized.**  It is injective on 32-byte
inputs, which is exactly the `CollisionResistant` field. -/
theorem lazySha256_collisionResistant : CollisionResistant lazySha256 := by
  intro x y hx hy h
  rw [lazySha256_of_size hx, lazySha256_of_size hy] at h
  exact h

/-- A legitimate `PrimitiveModel`: lazy SHA-256 (satisfying `sha256_size` and
`sha256_collisionResistant`), width-padded HASH160 and HMAC, identity AEAD, and
the single-message ECDSA verifier (which satisfies `EufCma`).  It *does* satisfy
every structural and assumed field of the model; it fails only the unstated
global view injectivity. -/
def lazyModel (d₀ : ByteArray) : PrimitiveModel where
  sha256 := lazySha256
  hash160 := widthOrZero 20
  ecdsaVerify := singleMessageVerify d₀
  schnorrVerify := fun _ _ _ => false
  ecdh := fun _ _ => zeroBytes 32
  hkdf := fun _ _ _ => zeroBytes 32
  aeadSeal := fun _ _ p => p
  aeadOpen := fun _ _ c => some c
  hmacSha256 := fun _ m => widthOrZero 32 m
  sha256_size := lazySha256_size
  hash160_size := fun b => widthOrZero_size 20 b
  hmac_size := fun _ m => widthOrZero_size 32 m
  sha256_collisionResistant := lazySha256_collisionResistant
  ecdsa_eufCma := eufCma_singleMessage d₀
  schnorr_eufCma := by
    intro _pk _m₁ _m₂ _s h₁ _h₂
    exact absurd h₁ (by simp)
  aead_indCca :=
    ⟨fun _ _ _ => rfl, fun _ _ _ _ h => (Option.some.inj h).symm⟩

/-- The message the single-message verifier accepts: the commitment domain tag
followed by 32 zero bytes.  Every commitment digest in `lazyModel` is exactly
these 32 zero bytes. -/
def viewBindingTestMessage : ByteArray := commitmentTag ++ zeroBytes 32

/-- The concrete collision model used for the counterexample. -/
def viewCollisionModel : PrimitiveModel := lazyModel viewBindingTestMessage

theorem commitmentTag_append_zeroBytes_size :
    (commitmentTag ++ zeroBytes 32).size = 38 := by
  rw [ByteArray.size_append, commitmentTag_size, zeroBytes_size]

/-- The `sha256` field of the lazy model, without unfolding the whole record. -/
theorem lazyModel_sha256 (d₀ : ByteArray) :
    (lazyModel d₀).sha256 = lazySha256 := rfl

/-- The `ecdsaVerify` field of the lazy model, without unfolding the whole
record. -/
theorem lazyModel_ecdsaVerify (d₀ : ByteArray) :
    (lazyModel d₀).ecdsaVerify = singleMessageVerify d₀ := rfl

/-- In the lazy model every commitment digest is the same 32 zero bytes: each
tagged preimage is longer than 32 bytes and `lazySha256` collapses all such
inputs. -/
theorem lazyModel_commitmentDigest (d₀ : ByteArray) (v : CommitmentSighashView) :
    commitmentDigest (lazyModel d₀) v = zeroBytes 32 := by
  show (lazyModel d₀).sha256 (commitmentTag ++ commitmentPreimage v) = zeroBytes 32
  rw [lazyModel_sha256]
  exact lazySha256_of_ne (taggedPreimage_size_ne_32 v)

/-- Every commitment digest of the counterexample model is the same 32 zero
bytes. -/
theorem viewCollisionModel_digest (v : CommitmentSighashView) :
    commitmentDigest viewCollisionModel v = zeroBytes 32 :=
  lazyModel_commitmentDigest viewBindingTestMessage v

/-- A test view family: only the fee differs. -/
def testView (feeSat : Nat) : CommitmentSighashView where
  commitmentNumber := 0
  obscuredCommitmentNumber := 0
  fundingTxid := ByteArray.empty
  fundingOutputIndex := 0
  fundingValueSat := 0
  fundingScript := ByteArray.empty
  holder := .local
  toLocalSat := 0
  toRemoteSat := 0
  outputs := []
  feeSat := feeSat
  contestDelay := 0
  anchorOutputs := false
  feeratePerKw := 0
  htlcs := []

theorem testView_injective : Function.Injective testView := by
  intro a b h
  have hfee : a = b := by
    have := congrArg (fun v : CommitmentSighashView => v.feeSat) h
    simpa [testView] using this
  exact hfee

theorem testView_zero_ne_one : testView 0 ≠ testView 1 := by
  intro h
  have h01 : (0 : Nat) = 1 := testView_injective h
  exact absurd h01 (by decide)

/-- The single-message verifier accepts the test message under any key and any
signature, so one signature is a valid commitment signature for every view whose
digest is the test message's `sha256` input payload. -/
theorem signedBy_viewCollisionModel (v : CommitmentSighashView) :
    CommitmentSignedBy viewCollisionModel ⟨ByteArray.empty⟩ v ⟨ByteArray.empty⟩ := by
  unfold CommitmentSignedBy SignedBy
  show (lazyModel viewBindingTestMessage).ecdsaVerify ⟨ByteArray.empty⟩
      (commitmentTag ++ commitmentDigest viewCollisionModel v)
      ⟨ByteArray.empty⟩ = true
  rw [lazyModel_ecdsaVerify, viewCollisionModel_digest]
  show decide (commitmentTag ++ zeroBytes 32 = commitmentTag ++ zeroBytes 32) = true
  exact decide_eq_true rfl

/-- **Mechanized counterexample: C1 + C3 do not bind the view.**  There is a
model satisfying the model's C1 field (`CollisionResistant M.sha256`) and C3
(`EufCma M.ecdsaVerify`), one signature, and two *distinct* commitment views such
that the signature is a valid commitment signature for both.  Digest binding
therefore does not imply view binding without the extra hypothesis
`ViewDigestCollisionFree`. -/
theorem digest_binding_not_view_binding :
    ∃ (M : PrimitiveModel) (pk : PubKey) (sig : EcdsaSig)
      (v w : CommitmentSighashView),
      v ≠ w ∧
        CollisionResistant M.sha256 ∧
        EufCma M.ecdsaVerify ∧
        CommitmentSignedBy M pk v sig ∧
        CommitmentSignedBy M pk w sig := by
  refine ⟨viewCollisionModel, ⟨ByteArray.empty⟩, ⟨ByteArray.empty⟩,
    testView 0, testView 1, testView_zero_ne_one,
    viewCollisionModel.sha256_collisionResistant,
    viewCollisionModel.ecdsa_eufCma,
    signedBy_viewCollisionModel (testView 0),
    signedBy_viewCollisionModel (testView 1)⟩

/-- The negated universal: in the collision model, equal digests do not imply
equal views, so global view binding is false even though C1 and C3 hold. -/
theorem viewCollisionModel_not_viewBinding :
    ¬ (∀ v w : CommitmentSighashView,
        commitmentDigest viewCollisionModel v =
          commitmentDigest viewCollisionModel w → v = w) := by
  intro h
  have hd : commitmentDigest viewCollisionModel (testView 0) =
      commitmentDigest viewCollisionModel (testView 1) := by
    rw [viewCollisionModel_digest, viewCollisionModel_digest]
  exact testView_zero_ne_one (h _ _ hd)

/-- **View binding is not state-record binding.**  `viewOfState` does not read
the state's stored `commitmentDigest` field (it is the field the serializer
replaces), so two distinct `SignedState` records share a view.  View binding is
a statement about the canonical commitment view, not about the whole
signer-side record. -/
theorem viewOfState_not_injective_in_state (ctx : SighashContext) :
    ∃ st st' : SignedState, st ≠ st' ∧ viewOfState ctx st = viewOfState ctx st' := by
  refine ⟨exampleSignedState,
    { exampleSignedState with commitmentDigest := ByteArray.mk #[0x00] }, ?_, rfl⟩
  intro h
  have hd : ByteArray.empty = ByteArray.mk #[0x00] :=
    congrArg (fun s : SignedState => s.commitmentDigest) h
  have hs := congrArg ByteArray.size hd
  simp [ByteArray.size] at hs

/-- **The second-stage view commits to floored satoshis only.**  Two HTLCs that
differ by a sub-satoshi amount have the same `HtlcSighashView`, because
`amountSat` is `Msat.toSatFloor`.  The millisatoshi amount is carried by the wire
entry, not by the signed commitment view; this is a scope boundary of view
binding, not a bug in it. -/
theorem htlcView_ignores_msat_fraction (ctx : SighashContext) (st : SignedState) :
    htlcViewOfState ctx st
        { htlcId := 1
          amount := ⟨1000⟩
          paymentHash := ⟨ByteArray.empty⟩
          direction := .local
          htlcState := .offered
          cltvExpiry := 100
          signedDataDigest := ByteArray.empty } =
      htlcViewOfState ctx st
        { htlcId := 1
          amount := ⟨1001⟩
          paymentHash := ⟨ByteArray.empty⟩
          direction := .local
          htlcState := .offered
          cltvExpiry := 100
          signedDataDigest := ByteArray.empty } := by
  have h1 : (1000 : Nat) / 1000 = 1 := by decide
  simp [htlcViewOfState, Msat.toSatFloor, Msat.MSAT_PER_SAT, h1]

/-! ## 6. Summary -/

set_option linter.unusedVariables false in
/-- Bundled faithful reading of the lane.

1. Equal views determine equal domain-separated commitment inputs and digests.
2. Under C3 and `ViewDigestCollisionFree`, a produced commitment signature that
   verifies for any admissible view's digest binds that view.
3. Under C3 and `HtlcDigestCollisionFree`, a produced second-stage signature
   binds both the HTLC view and its parent commitment view.
4. The binding hypothesis is non-vacuous on a singleton admissible list.
5. C1 as formalized plus C3 do **not** imply view binding: there is a model, a
   signature, and two distinct views making the signature valid for both.
6. View binding is not state-record binding, and the second-stage view commits
   only to satoshi-floored amounts. -/
theorem view_binding_summary :
    (∀ (M : PrimitiveModel) (v w : CommitmentSighashView), v = w →
        viewCommitment v = viewCommitment w ∧
          commitmentDigest M v = commitmentDigest M w) ∧
      (∀ (M : PrimitiveModel) (hC3 : EufCma M.ecdsaVerify)
        (law : CommitmentSigningLaw M) (ctx : SighashContext)
        (st : SignedState) (f : CommitmentSignedFull),
        SighashProduces M law ctx st f →
        ∀ (views : List CommitmentSighashView),
          ViewDigestCollisionFree M views →
          viewOfState ctx st ∈ views →
          ∀ w : CommitmentSighashView, w ∈ views →
            M.ecdsaVerify ctx.commitmentKey
              (commitmentTag ++ commitmentDigest M w)
              f.commitmentSignature = true →
            w = viewOfState ctx st) ∧
      (∀ (M : PrimitiveModel) (hC3 : EufCma M.ecdsaVerify)
        (law : CommitmentSigningLaw M) (ctx : SighashContext)
        (st : SignedState) (f : CommitmentSignedFull),
        SighashProduces M law ctx st f →
        ∀ (pairs : List (CommitmentSighashView × HtlcSighashView)),
          HtlcDigestCollisionFree M pairs →
          ∀ (hh : SignedHtlc), hh ∈ st.htlcs →
            (viewOfState ctx st, htlcViewOfState ctx st hh) ∈ pairs →
            ∀ (w : CommitmentSighashView) (g : HtlcSighashView),
              (w, g) ∈ pairs →
                M.ecdsaVerify ctx.commitmentKey
                  (commitmentTag ++ htlcDigest M w g)
                  (entryOfSighash M law ctx st hh).signature = true →
                w = viewOfState ctx st ∧ g = htlcViewOfState ctx st hh) ∧
      (∀ (M : PrimitiveModel) (v : CommitmentSighashView),
        ViewDigestCollisionFree M [v]) ∧
      (∃ (M : PrimitiveModel) (pk : PubKey) (sig : EcdsaSig)
        (v w : CommitmentSighashView),
        v ≠ w ∧
          CollisionResistant M.sha256 ∧
          EufCma M.ecdsaVerify ∧
          CommitmentSignedBy M pk v sig ∧
          CommitmentSignedBy M pk w sig) ∧
      (∀ ctx : SighashContext,
        ∃ st st' : SignedState, st ≠ st' ∧ viewOfState ctx st = viewOfState ctx st') :=
  ⟨fun _M _v _w h => ⟨viewCommitment_eq_of_view_eq h, commitmentDigest_eq_of_view_eq _M h⟩,
    fun M hC3 law ctx st f h views hbind hv w hw hver =>
      commitmentSignature_binds_view hC3 h hbind hv hw hver,
    fun M hC3 law ctx st f h pairs hbind hh hmem hp w g hq hver =>
      htlcSignature_binds_htlcView hC3 h hbind hmem hp hq hver,
    fun M v => viewDigestCollisionFree_singleton M v,
    digest_binding_not_view_binding,
    viewOfState_not_injective_in_state⟩

end LnLean.Proofs.Channel.SighashViewBindingTargets
