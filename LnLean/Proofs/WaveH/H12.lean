/-
# H12 — Conditional HTLC-wire signature-to-view binding (PR-06, PR-02)

**Catalog issues.**

* `PR-06` (P1): C3 (`EufCma`) binds a signature to a *digest*, not to a view.
  The wave-6 module `SighashViewBindingTargets` proved the commitment-level and
  second-stage binding theorems for the structural wave-5 serializer, with
  `ViewDigestCollisionFree`/`HtlcDigestCollisionFree` and
  `SerializationBindsViews` as explicit hypotheses, and mechanized
  `digest_binding_not_view_binding` plus `htlcView_ignores_msat_fraction`.
  The exact-wire `HtlcWire` path (the BOLT 3 second-stage HTLC transaction) had
  no view, no serializer and no binding statement of its own: a wire-path
  signature was only known to bind a 32-byte digest.
* `PR-02` (P1): the wire record must carry enough data for a wire-only
  statement of *what a signature covers*.  The structural `htlcDigest` is a
  function of the parent commitment preimage and the `HtlcSighashView` only; it
  never reads the second-stage transaction bytes, so digest binding on the
  structural path cannot bind the wire fields (section 7.3).

**Result of this module.**

1. The HTLC-wire view `HtlcWireView` pairs the exact BOLT 3 second-stage wire
   transaction (`SighashTargets.HtlcWire`: version, commitment outpoint,
   sequence, value, scriptPubKey, locktime) with the structural
   `HtlcSighashView`.  `HtlcWireContext` supplies the three pieces BOLT 3 puts
   into the second-stage transaction but the channel state does not carry: the
   parent commitment txid, the spent commitment output index, and the HTLC
   `scriptPubKey`.  `htlcWireViewOfState` derives the view from a `SignedState`
   HTLC; the derived wire uses version `2`, `nSequence = 0xffffffff`,
   `nLockTime = 0`, and the **satoshi-floored** HTLC amount, matching BOLT 3.
2. The canonical wire serializer `htlcWirePreimage` is
   `tag(0x21) ‖ htlcPreimage htlc ‖ HtlcWire.txBytes`, domain-separated from the
   structural second-stage preimage (tag `0x20`).  `htlcWireDigest` is
   `SHA-256(commitmentTag ‖ htlcWirePreimage)`, so the signed message commits to
   the exact wire bytes *and* the structural HTLC view.  Exact size formulas are
   proved; every tagged wire preimage has at least 85 bytes, so the lazy-model
   counterexample applies.
3. Two binding hypotheses are kept separate and explicit:
   * `HtlcWireDigestCollisionFree M views` — SHA-256 is collision-free on the
     tagged wire serializations of the admissible views (the cryptographic
     half; **not** derivable from the model's 32-byte `CollisionResistant`
     field);
   * `HtlcWireSerializationBinds views` — the wire serializer is injective on
     the admissible views (the encoding half).
   `htlcWireDigestCollisionFree_of_serializationBinds` composes them.
4. The production relation `HtlcWireProduces` says a `SignedHtlcEntry` carries
   the state HTLC's identification fields (id, `amount_msat`, payment hash,
   direction, state, CLTV) and derives its `signedDataDigest` and `signature`
   from the wire serializer; `wireEntryOfSighash` is the derived entry.
   `HtlcWireProduces.wire_signature_binds_digest` is the C3 step: a produced
   wire signature validates for no message other than the derived wire digest.
5. **Main positive theorem.**  Under C3 and `HtlcWireDigestCollisionFree`, a
   produced wire signature that verifies for the wire digest of *any* admissible
   wire view `w` forces `w = htlcWireViewOfState wctx ctx st hh`.  The companion
   field theorem lists every bound field: all seven wire fields and all eight
   `HtlcSighashView` fields.  `htlcWireSignature_not_valid_for_distinct` is the
   replay form: the signature is invalid for every other admissible view.
6. Non-vacuity: the hypotheses hold on singletons and on pairs with distinct
   digests (`htlcWireDigestCollisionFree_pair`), the serializer hypothesis holds
   on any pair whose `scriptPubKey` lengths differ
   (`htlcWireSerializationBinds_pair_of_scriptPubKey_size_ne`), the honest
   derived signature verifies for the derived view, and the main theorem is
   instantiated on `exampleSignedState`.
7. **Negatives.**

   * `wire_digest_binding_not_view_binding`: a full `PrimitiveModel` satisfying
     the model's C1 field and C3 (the existing `viewCollisionModel`: lazy
     SHA-256, single-message verifier) has one signature valid for **two
     distinct wire views**.  Hence digest binding plus C1 plus C3 does not bind
     the wire view; the collision-free hypothesis is load-bearing.
   * `wireEntry_signedData_ignores_msat_fraction`: two HTLCs differing by one
     millisatoshi have the *same* wire digest and the *same* signature but
     different `amount_msat`.  This preserves and strengthens
     `SighashViewTargets.htlcView_ignores_msat_fraction`: the wire path signs
     the floored satoshi amount only.
   * `structuralDigest_ignores_wire`: two distinct wire views with the same
     `HtlcSighashView` have the same structural `htlcDigest`.  The structural
     digest cannot bind the wire bytes, which is why the wire serializer adds
     them.

## Scope

This module does **not** prove the BIP 143 byte equality of the second-stage
preimage (that is the `HtlcWire`/scriptCode instantiation of `PR-05`); it models
the *view-level* message that the wire path signs, exactly as the wave-5
`htlcDigest` models the structural message.  The `HtlcWire` scripts and the
parent commitment txid are opaque byte strings supplied by `HtlcWireContext`;
the module does not synthesize the BOLT 3 offered/received HTLC scriptCode.
The cryptographic hypothesis is stated on the range of the wire serializer and
is not derived from `CollisionResistant M.sha256` (which is 32-byte injectivity
only), and no global SHA-256 injectivity is assumed.  There is no secret-key
model: the signing law is keyed by the public key, as in the parent modules.
The signed view commits to the **floored** HTLC amount, so `amount_msat` is wire
data that is not covered by the signature; this is a scope boundary, not a
defect of the binding theorem.

## Anchors

* BOLT 3 §"HTLC-timeout and HTLC-success Transactions"
  (`03-transactions.md`): version 2, one input spending the commitment HTLC
  output, `nSequence = 0xffffffff`, `nLockTime = 0`, and the satoshi-denominated
  HTLC amount.
* BOLT 3 §"Commitment Transaction" (`03-transactions.md:83-353`): the commitment
  outpoint and the obscured commitment number that the HTLC view names.
* BOLT 2 §"Committing Updates So Far" (type 132): one commitment signature plus
  one `HTLC_signature` per untrimmed HTLC output.
* Model: `LnLean/Proofs/Channel/SighashTargets.lean` (`HtlcWire`,
  `HtlcWire.txBytes`, `HtlcWire.WellFormed`, `HtlcSighashView`, `htlcPreimage`,
  `htlcDigest`, `SighashContext`, `htlcViewOfState`, `SignedBy`,
  `CommitmentSigningLaw`), `LnLean/Proofs/Channel/SighashViewBindingTargets.lean`
  (`lazyModel`, `viewCollisionModel`, `lazySha256_of_ne`,
  `htlcView_ignores_msat_fraction`, `zeroBytes`), `LnLean/Crypto/Model.lean`
  (`PrimitiveModel`, `EufCma`, `CollisionResistant`, `append_left_cancel`),
  `LnLean/Proofs/Crypto/EcdsaProps.lean` (`singleMessageVerify`,
  `eufCma_singleMessage`), `docs/CRYPTO-LIMITS.md` §2, §7.1.
-/

import LnLean.Proofs.Channel.SighashViewBindingTargets

namespace LnLean.Proofs.WaveH.H12

set_option autoImplicit false

open LnLean
open LnLean.Protocol
open LnLean.Channel
open LnLean.Crypto
open LnLean.Proofs
open LnLean.Proofs.ProtocolWireTargets
open LnLean.Proofs.Channel.SighashTargets
open LnLean.Proofs.Channel.SighashViewBindingTargets
open Bitcoin.Serialization

/-! ## 1. The second-stage HTLC-wire view

`HtlcWire` is the exact BOLT 3 second-stage transaction.  The pieces BOLT 3
takes from the parent commitment (its txid and the spent output index) and the
HTLC `scriptPubKey` are not in `SignedState`, so they are supplied explicitly by
`HtlcWireContext`.  The view pairs the resulting wire with the structural
`HtlcSighashView`; it is the object a wire-path signature is supposed to bind. -/

/-- BOLT 3 second-stage transaction version. -/
def htlcWireVersion : UInt32 := 2

/-- BOLT 3 second-stage input sequence (`0xffffffff`, no relative lock). -/
def htlcWireSequence : UInt32 := 0xffffffff

/-- BOLT 3 second-stage locktime (`0`). -/
def htlcWireLocktime : UInt32 := 0

/-- The non-state data of a second-stage HTLC transaction: the parent commitment
outpoint and the HTLC `scriptPubKey`.  The script bytes are opaque here; deriving
them from the funding keys is the scriptCode-synthesis lane. -/
structure HtlcWireContext where
  /-- The parent commitment transaction id, in consensus-internal byte order. -/
  commitmentTxid : ByteArray
  /-- The commitment output index the second-stage input spends. -/
  commitmentOutputIndex : UInt32
  /-- The HTLC `scriptPubKey`/witness-script bytes. -/
  htlcScript : ByteArray
deriving Repr, BEq

/-- The exact second-stage `HtlcWire` for an HTLC view and wire context:
version 2, one input at the commitment outpoint, `nSequence = 0xffffffff`, a
single output paying the floored satoshi amount to the HTLC script, and
`nLockTime = 0`. -/
def htlcWireOfView (wctx : HtlcWireContext) (v : HtlcSighashView) : HtlcWire where
  version := htlcWireVersion
  commitmentTxid := wctx.commitmentTxid
  commitmentOutputIndex := wctx.commitmentOutputIndex
  sequence := htlcWireSequence
  valueSat := UInt64.ofNat v.amountSat
  scriptPubKey := wctx.htlcScript
  locktime := htlcWireLocktime

@[simp] theorem htlcWireOfView_version (wctx : HtlcWireContext)
    (v : HtlcSighashView) : (htlcWireOfView wctx v).version = htlcWireVersion := rfl

@[simp] theorem htlcWireOfView_commitmentTxid (wctx : HtlcWireContext)
    (v : HtlcSighashView) :
    (htlcWireOfView wctx v).commitmentTxid = wctx.commitmentTxid := rfl

@[simp] theorem htlcWireOfView_commitmentOutputIndex (wctx : HtlcWireContext)
    (v : HtlcSighashView) :
    (htlcWireOfView wctx v).commitmentOutputIndex = wctx.commitmentOutputIndex := rfl

@[simp] theorem htlcWireOfView_sequence (wctx : HtlcWireContext)
    (v : HtlcSighashView) :
    (htlcWireOfView wctx v).sequence = htlcWireSequence := rfl

@[simp] theorem htlcWireOfView_valueSat (wctx : HtlcWireContext)
    (v : HtlcSighashView) :
    (htlcWireOfView wctx v).valueSat = UInt64.ofNat v.amountSat := rfl

@[simp] theorem htlcWireOfView_scriptPubKey (wctx : HtlcWireContext)
    (v : HtlcSighashView) :
    (htlcWireOfView wctx v).scriptPubKey = wctx.htlcScript := rfl

@[simp] theorem htlcWireOfView_locktime (wctx : HtlcWireContext)
    (v : HtlcSighashView) :
    (htlcWireOfView wctx v).locktime = htlcWireLocktime := rfl

/-- The wire-domain conditions of a derived second-stage wire.  The amount
bound is the Bitcoin `MoneyRange`-style bound (`< 2^63`), which the model's
`HtlcWire.WellFormed` requires. -/
theorem htlcWireOfView_wellFormed (wctx : HtlcWireContext) (v : HtlcSighashView)
    (htxid : wctx.commitmentTxid.size = 32)
    (hscript : wctx.htlcScript.size ≤ Bitcoin.Serialization.MAX_SIZE)
    (hval : v.amountSat < 9223372036854775808) :
    (htlcWireOfView wctx v).WellFormed := by
  refine ⟨htxid, hscript, ?_⟩
  show (UInt64.ofNat v.amountSat).toNat < 9223372036854775808
  rw [UInt64.toNat_ofNat']
  rw [Nat.mod_eq_of_lt (by omega : v.amountSat < 2 ^ 64)]
  exact hval

/-- A second-stage HTLC view: the exact wire transaction plus the structural
HTLC view.  Every field a wire-path signature could be replayed onto lives in
one of the two components. -/
structure HtlcWireView where
  /-- The exact BOLT 3 second-stage transaction. -/
  wire : HtlcWire
  /-- The structural per-HTLC sighash view. -/
  htlc : HtlcSighashView
deriving Repr, BEq

/-- The derived wire view of a state HTLC: the BOLT 3 second-stage wire built
from the structural view (so the amount is the satoshi floor) and the
non-state wire context. -/
def htlcWireViewOfState (wctx : HtlcWireContext) (ctx : SighashContext)
    (st : SignedState) (h : SignedHtlc) : HtlcWireView where
  wire := htlcWireOfView wctx (htlcViewOfState ctx st h)
  htlc := htlcViewOfState ctx st h

@[simp] theorem htlcWireViewOfState_wire (wctx : HtlcWireContext)
    (ctx : SighashContext) (st : SignedState) (h : SignedHtlc) :
    (htlcWireViewOfState wctx ctx st h).wire =
      htlcWireOfView wctx (htlcViewOfState ctx st h) := rfl

@[simp] theorem htlcWireViewOfState_htlc (wctx : HtlcWireContext)
    (ctx : SighashContext) (st : SignedState) (h : SignedHtlc) :
    (htlcWireViewOfState wctx ctx st h).htlc = htlcViewOfState ctx st h := rfl

/-! ## 2. Canonical wire serializer and digest

The wire preimage is a distinct sub-tag (`0x21`) followed by the structural
second-stage preimage (`htlcPreimage`, which starts with `0x20`) and the exact
wire transaction bytes.  The sub-tag keeps the wire path in its own domain under
the shared commitment tag, and the wire bytes are what the structural path does
not model. -/

/-- Domain sub-tag of the exact second-stage HTLC-wire preimage.  Distinct from
the structural `htlcPreimage` tag `0x20`. -/
def htlcWireTag : UInt8 := 0x21

/-- The exact second-stage HTLC-wire preimage:
`0x21 ‖ htlcPreimage htlc ‖ HtlcWire.txBytes`. -/
def htlcWirePreimage (v : HtlcWireView) : ByteArray :=
  ByteArray.mk #[htlcWireTag] ++ htlcPreimage v.htlc ++ v.wire.txBytes

/-- The wire-path digest: SHA-256 of the commitment domain tag followed by the
wire preimage.  The signed message commits to the exact wire transaction and to
the structural HTLC view. -/
def htlcWireDigest (M : PrimitiveModel) (v : HtlcWireView) : ByteArray :=
  M.sha256 (commitmentTag ++ htlcWirePreimage v)

/-- `htlcWireDigest` is literally the SHA-256 image of the tagged wire
preimage. -/
theorem htlcWireDigest_eq_sha256 (M : PrimitiveModel) (v : HtlcWireView) :
    htlcWireDigest M v = M.sha256 (commitmentTag ++ htlcWirePreimage v) := rfl

theorem htlcWireDigest_size (M : PrimitiveModel) (v : HtlcWireView) :
    (htlcWireDigest M v).size = 32 :=
  M.sha256_size _

/-- A wire-path signature: verification in the commitment domain over a wire
digest. -/
def HtlcWireSignedBy (M : PrimitiveModel) (pk : PubKey) (v : HtlcWireView)
    (s : EcdsaSig) : Prop :=
  SignedBy M pk commitmentTag (htlcWireDigest M v) s

/-- The wire preimage is domain-separated from the structural second-stage
preimage: the two sub-tags differ, so no wire preimage can be replayed as the
structural message of any HTLC view. -/
theorem htlcWirePreimage_ne_structural (v : HtlcWireView) (h : HtlcSighashView) :
    htlcWirePreimage v ≠ htlcPreimage h := by
  intro heq
  have hb := congrArg bL heq
  simp [htlcWirePreimage, htlcPreimage, htlcWireTag, bL, List.cons.injEq] at hb

/-! ### 2.1 Width of the wire serializer

The counterexample model collapses every input that is not exactly 32 bytes.
A tagged wire preimage is at least 85 bytes, so no wire digest can accidentally
land in the injective part of that model. -/

/-- Exact width of the structural second-stage preimage. -/
theorem htlcPreimage_size (h : HtlcSighashView) :
    (htlcPreimage h).size = 51 + h.paymentHash.bytes.size := by
  simp [htlcPreimage, natBytes_size, directionBytes_size, htlcStateBytes_size,
    bytesField_size, oneByte_size, ByteArray.size_append]
  omega

/-- Exact width of the wire preimage: the sub-tag byte, the structural
preimage, and the exact wire transaction bytes. -/
theorem htlcWirePreimage_size (v : HtlcWireView) :
    (htlcWirePreimage v).size =
      79 + v.htlc.paymentHash.bytes.size + v.wire.commitmentTxid.size +
        compactSizeWidth v.wire.scriptPubKey.size + v.wire.scriptPubKey.size := by
  simp [htlcWirePreimage, htlcPreimage_size, HtlcWire.txBytes_size,
    oneByte_size, ByteArray.size_append]
  omega

/-- Exact width of the tagged wire preimage (the input of the hash). -/
theorem taggedHtlcWirePreimage_size (v : HtlcWireView) :
    (commitmentTag ++ htlcWirePreimage v).size =
      85 + v.htlc.paymentHash.bytes.size + v.wire.commitmentTxid.size +
        compactSizeWidth v.wire.scriptPubKey.size + v.wire.scriptPubKey.size := by
  rw [ByteArray.size_append, commitmentTag_size, htlcWirePreimage_size]
  omega

theorem taggedHtlcWirePreimage_size_ge (v : HtlcWireView) :
    85 ≤ (commitmentTag ++ htlcWirePreimage v).size := by
  rw [taggedHtlcWirePreimage_size]
  omega

theorem taggedHtlcWirePreimage_size_ne_32 (v : HtlcWireView) :
    (commitmentTag ++ htlcWirePreimage v).size ≠ 32 := by
  have := taggedHtlcWirePreimage_size_ge v
  omega

/-- The serializer determines the parent commitment txid length when the other
size contributions agree, so two such views with different txid lengths cannot
have the same wire preimage.  This is a proved, non-vacuous fragment of the
encoding hypothesis. -/
theorem htlcWirePreimage_ne_of_txid_size_ne {v w : HtlcWireView}
    (hph : v.htlc.paymentHash.bytes.size = w.htlc.paymentHash.bytes.size)
    (hscript : v.wire.scriptPubKey.size = w.wire.scriptPubKey.size)
    (h : v.wire.commitmentTxid.size ≠ w.wire.commitmentTxid.size) :
    htlcWirePreimage v ≠ htlcWirePreimage w := by
  intro heq
  have hs := congrArg ByteArray.size heq
  rw [htlcWirePreimage_size, htlcWirePreimage_size, hph, hscript] at hs
  omega

/-! ## 3. Explicit binding hypotheses

As in the structural module, the cryptographic half and the encoding half are
separate predicates over an explicit finite list of admissible views.  Neither
is derived from `CollisionResistant M.sha256`, and neither assumes global
SHA-256 injectivity. -/

/-- **Cryptographic binding hypothesis.**  On the admissible wire-view list,
equal wire digests imply equal wire views. -/
def HtlcWireDigestCollisionFree (M : PrimitiveModel)
    (views : List HtlcWireView) : Prop :=
  ∀ v ∈ views, ∀ w ∈ views, htlcWireDigest M v = htlcWireDigest M w → v = w

/-- **Encoding binding hypothesis.**  The wire serializer is injective on the
admissible views. -/
def HtlcWireSerializationBinds (views : List HtlcWireView) : Prop :=
  ∀ v ∈ views, ∀ w ∈ views, htlcWirePreimage v = htlcWirePreimage w → v = w

/-- Collision-freedom on the serializer image plus serializer injectivity give
wire-digest binding. -/
theorem htlcWireDigestCollisionFree_of_serializationBinds {M : PrimitiveModel}
    {views : List HtlcWireView}
    (hser : HtlcWireSerializationBinds views)
    (hcol : ∀ v ∈ views, ∀ w ∈ views,
      M.sha256 (commitmentTag ++ htlcWirePreimage v) =
        M.sha256 (commitmentTag ++ htlcWirePreimage w) →
      commitmentTag ++ htlcWirePreimage v = commitmentTag ++ htlcWirePreimage w) :
    HtlcWireDigestCollisionFree M views := by
  intro v hv w hw hd
  exact hser v hv w hw (append_left_cancel (hcol v hv w hw hd))

/-- The binding hypothesis holds on the empty list. -/
theorem htlcWireDigestCollisionFree_nil (M : PrimitiveModel) :
    HtlcWireDigestCollisionFree M [] := by
  intro v hv
  cases hv

/-- The binding hypothesis holds on a singleton list. -/
theorem htlcWireDigestCollisionFree_singleton (M : PrimitiveModel)
    (v : HtlcWireView) : HtlcWireDigestCollisionFree M [v] := by
  intro a ha b hb _
  rw [List.mem_singleton] at ha hb
  rw [ha, hb]

/-- A pair of views with different digests satisfies the binding hypothesis:
the hypothesis is exactly "these two views are not a digest collision". -/
theorem htlcWireDigestCollisionFree_pair (M : PrimitiveModel)
    {v w : HtlcWireView} (hne : htlcWireDigest M v ≠ htlcWireDigest M w) :
    HtlcWireDigestCollisionFree M [v, w] := by
  intro a ha b hb heq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · rfl
  · exact absurd heq hne
  · exact absurd heq.symm hne
  · rfl

/-- The serializer hypothesis holds on a singleton list. -/
theorem htlcWireSerializationBinds_singleton (v : HtlcWireView) :
    HtlcWireSerializationBinds [v] := by
  intro a ha b hb _
  rw [List.mem_singleton] at ha hb
  rw [ha, hb]

/-- The serializer hypothesis holds on a pair whose parent commitment txids have
different lengths (with the other size contributions fixed): the preimages
cannot collide.  A proved, non-vacuous instance. -/
theorem htlcWireSerializationBinds_pair_of_txid_size_ne
    {v w : HtlcWireView}
    (hph : v.htlc.paymentHash.bytes.size = w.htlc.paymentHash.bytes.size)
    (hscript : v.wire.scriptPubKey.size = w.wire.scriptPubKey.size)
    (h : v.wire.commitmentTxid.size ≠ w.wire.commitmentTxid.size) :
    HtlcWireSerializationBinds [v, w] := by
  intro a ha b hb hpre
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
  rcases ha with h1 | h1
  · subst h1
    rcases hb with h2 | h2
    · subst h2
      rfl
    · subst h2
      exact absurd hpre (htlcWirePreimage_ne_of_txid_size_ne hph hscript h)
  · subst h1
    rcases hb with h2 | h2
    · subst h2
      exact absurd hpre
        (htlcWirePreimage_ne_of_txid_size_ne hph.symm hscript.symm h.symm)
    · subst h2
      rfl

/-! ## 4. The wire production relation

The wave-4 `SignedHtlcEntry` carries identification data plus a digest and a
signature.  `HtlcWireProduces` says the identification data are the state's and
the digest and signature are *derived* from the wire serializer.  It is the
wire-path analogue of `SighashProduces` for one HTLC entry. -/

/-- The wire-path entry derived from a state HTLC: identification data from the
state, digest and signature from the wire serializer. -/
def wireEntryOfSighash (M : PrimitiveModel) (law : CommitmentSigningLaw M)
    (wctx : HtlcWireContext) (ctx : SighashContext) (st : SignedState)
    (h : SignedHtlc) : SignedHtlcEntry where
  htlcId := h.htlcId
  amount := h.amount
  paymentHash := h.paymentHash
  direction := h.direction
  htlcState := h.htlcState
  cltvExpiry := h.cltvExpiry
  signedDataDigest := htlcWireDigest M (htlcWireViewOfState wctx ctx st h)
  signature := law.sign ctx.commitmentKey
    (commitmentTag ++ htlcWireDigest M (htlcWireViewOfState wctx ctx st h))

@[simp] theorem wireEntryOfSighash_htlcId (M : PrimitiveModel)
    (law : CommitmentSigningLaw M) (wctx : HtlcWireContext)
    (ctx : SighashContext) (st : SignedState) (h : SignedHtlc) :
    (wireEntryOfSighash M law wctx ctx st h).htlcId = h.htlcId := rfl

@[simp] theorem wireEntryOfSighash_amount (M : PrimitiveModel)
    (law : CommitmentSigningLaw M) (wctx : HtlcWireContext)
    (ctx : SighashContext) (st : SignedState) (h : SignedHtlc) :
    (wireEntryOfSighash M law wctx ctx st h).amount = h.amount := rfl

@[simp] theorem wireEntryOfSighash_digest (M : PrimitiveModel)
    (law : CommitmentSigningLaw M) (wctx : HtlcWireContext)
    (ctx : SighashContext) (st : SignedState) (h : SignedHtlc) :
    (wireEntryOfSighash M law wctx ctx st h).signedDataDigest =
      htlcWireDigest M (htlcWireViewOfState wctx ctx st h) := rfl

@[simp] theorem wireEntryOfSighash_signature (M : PrimitiveModel)
    (law : CommitmentSigningLaw M) (wctx : HtlcWireContext)
    (ctx : SighashContext) (st : SignedState) (h : SignedHtlc) :
    (wireEntryOfSighash M law wctx ctx st h).signature =
      law.sign ctx.commitmentKey
        (commitmentTag ++ htlcWireDigest M (htlcWireViewOfState wctx ctx st h)) := rfl

/-- **`HtlcWireProduces`.**  A signed entry was produced on the exact-wire HTLC
path when its identification fields are the state HTLC's and its digest and
signature are the wire serializer's derived values.  No digest or signature is
free data. -/
structure HtlcWireProduces (M : PrimitiveModel) (law : CommitmentSigningLaw M)
    (wctx : HtlcWireContext) (ctx : SighashContext) (st : SignedState)
    (hh : SignedHtlc) (e : SignedHtlcEntry) : Prop where
  htlcId_eq : e.htlcId = hh.htlcId
  amount_eq : e.amount = hh.amount
  paymentHash_eq : e.paymentHash = hh.paymentHash
  direction_eq : e.direction = hh.direction
  htlcState_eq : e.htlcState = hh.htlcState
  cltvExpiry_eq : e.cltvExpiry = hh.cltvExpiry
  signedDataDigest_eq :
    e.signedDataDigest = htlcWireDigest M (htlcWireViewOfState wctx ctx st hh)
  signature_eq : e.signature = law.sign ctx.commitmentKey
    (commitmentTag ++ htlcWireDigest M (htlcWireViewOfState wctx ctx st hh))

/-- The derived entry satisfies the production relation definitionally. -/
theorem wireEntryOfSighash_produces (M : PrimitiveModel)
    (law : CommitmentSigningLaw M) (wctx : HtlcWireContext)
    (ctx : SighashContext) (st : SignedState) (h : SignedHtlc) :
    HtlcWireProduces M law wctx ctx st h
      (wireEntryOfSighash M law wctx ctx st h) :=
  { htlcId_eq := rfl
    amount_eq := rfl
    paymentHash_eq := rfl
    direction_eq := rfl
    htlcState_eq := rfl
    cltvExpiry_eq := rfl
    signedDataDigest_eq := rfl
    signature_eq := rfl }

/-- **C3 binds a produced wire signature to the derived wire digest.**  If the
signature of a produced entry validates for any message `msg` in the commitment
domain, that message is the derived wire digest. -/
theorem HtlcWireProduces.wire_signature_binds_digest {M : PrimitiveModel}
    (hC3 : EufCma M.ecdsaVerify) {law : CommitmentSigningLaw M}
    {wctx : HtlcWireContext} {ctx : SighashContext} {st : SignedState}
    {hh : SignedHtlc} {e : SignedHtlcEntry}
    (h : HtlcWireProduces M law wctx ctx st hh e) {msg : ByteArray}
    (hver : M.ecdsaVerify ctx.commitmentKey (commitmentTag ++ msg) e.signature = true) :
    msg = htlcWireDigest M (htlcWireViewOfState wctx ctx st hh) := by
  have hder : M.ecdsaVerify ctx.commitmentKey
      (commitmentTag ++ htlcWireDigest M (htlcWireViewOfState wctx ctx st hh))
      e.signature = true := by
    rw [h.signature_eq]
    exact law.verifies _ _
  exact append_left_cancel (hC3 _ _ _ _ hver hder)

/-- A derived wire entry's signature is a valid wire-path signature for the
derived view. -/
theorem wireEntryOfSighash_signedBy (M : PrimitiveModel)
    (law : CommitmentSigningLaw M) (wctx : HtlcWireContext)
    (ctx : SighashContext) (st : SignedState) (h : SignedHtlc) :
    HtlcWireSignedBy M ctx.commitmentKey (htlcWireViewOfState wctx ctx st h)
      (wireEntryOfSighash M law wctx ctx st h).signature := by
  unfold HtlcWireSignedBy SignedBy
  exact law.verifies _ _

/-- The wire entry's identification fields are the wave-4 entry's fields: the
wire production relation refines `entryOfSighash` at the identification level
while replacing its signalled digest with the wire digest. -/
theorem wireEntryOfSighash_identification_eq (M : PrimitiveModel)
    (law : CommitmentSigningLaw M) (wctx : HtlcWireContext)
    (ctx : SighashContext) (st : SignedState) (h : SignedHtlc) :
    (wireEntryOfSighash M law wctx ctx st h).htlcId =
        (entryOfSighash M law ctx st h).htlcId ∧
      (wireEntryOfSighash M law wctx ctx st h).amount =
        (entryOfSighash M law ctx st h).amount ∧
      (wireEntryOfSighash M law wctx ctx st h).paymentHash =
        (entryOfSighash M law ctx st h).paymentHash ∧
      (wireEntryOfSighash M law wctx ctx st h).direction =
        (entryOfSighash M law ctx st h).direction ∧
      (wireEntryOfSighash M law wctx ctx st h).htlcState =
        (entryOfSighash M law ctx st h).htlcState ∧
      (wireEntryOfSighash M law wctx ctx st h).cltvExpiry =
        (entryOfSighash M law ctx st h).cltvExpiry :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## 5. Main positive theorems: a valid wire signature binds the wire view -/

/-- **PR-06 for the `HtlcWire` path, main positive direction.**  Let `M` satisfy
C3, let `e` be produced from `(hh, st)` on the wire path, and suppose the model
is collision-free on the admissible wire-view list.  If the produced signature
verifies in the commitment domain for the wire digest of *any* admissible view
`w`, then `w` is exactly the derived wire view of `hh`.  So the signature binds
the second-stage transaction and the HTLC view, not merely the digest. -/
theorem htlcWireSignature_binds_view {M : PrimitiveModel}
    (hC3 : EufCma M.ecdsaVerify) {law : CommitmentSigningLaw M}
    {wctx : HtlcWireContext} {ctx : SighashContext} {st : SignedState}
    {hh : SignedHtlc} {e : SignedHtlcEntry}
    (h : HtlcWireProduces M law wctx ctx st hh e)
    {views : List HtlcWireView}
    (hbind : HtlcWireDigestCollisionFree M views)
    (hv : htlcWireViewOfState wctx ctx st hh ∈ views)
    {w : HtlcWireView} (hw : w ∈ views)
    (hver : M.ecdsaVerify ctx.commitmentKey
      (commitmentTag ++ htlcWireDigest M w) e.signature = true) :
    w = htlcWireViewOfState wctx ctx st hh := by
  have hd : htlcWireDigest M w =
      htlcWireDigest M (htlcWireViewOfState wctx ctx st hh) :=
    HtlcWireProduces.wire_signature_binds_digest hC3 h hver
  exact hbind w hw (htlcWireViewOfState wctx ctx st hh) hv hd

/-- **Replay form.**  A produced wire signature is invalid for every admissible
wire view other than the derived one. -/
theorem htlcWireSignature_not_valid_for_distinct {M : PrimitiveModel}
    (hC3 : EufCma M.ecdsaVerify) {law : CommitmentSigningLaw M}
    {wctx : HtlcWireContext} {ctx : SighashContext} {st : SignedState}
    {hh : SignedHtlc} {e : SignedHtlcEntry}
    (h : HtlcWireProduces M law wctx ctx st hh e)
    {views : List HtlcWireView}
    (hbind : HtlcWireDigestCollisionFree M views)
    (hv : htlcWireViewOfState wctx ctx st hh ∈ views)
    {w : HtlcWireView} (hw : w ∈ views)
    (hne : w ≠ htlcWireViewOfState wctx ctx st hh) :
    M.ecdsaVerify ctx.commitmentKey
      (commitmentTag ++ htlcWireDigest M w) e.signature ≠ true := by
  intro hver
  exact hne (htlcWireSignature_binds_view hC3 h hbind hv hw hver)

/-- **What wire-view binding yields concretely.**  The bound view determines
every wire field (version, commitment outpoint, sequence, value, HTLC script,
locktime) and every structural HTLC view field (id, parent commitment number,
direction, lifecycle, floored satoshi amount, payment hash, CLTV expiry,
second-stage fee).  This is the `PR-02` "a wire-path signature covers this
second-stage transaction and HTLC view" statement at field granularity. -/
theorem htlcWireSignature_binds_fields {M : PrimitiveModel}
    (hC3 : EufCma M.ecdsaVerify) {law : CommitmentSigningLaw M}
    {wctx : HtlcWireContext} {ctx : SighashContext} {st : SignedState}
    {hh : SignedHtlc} {e : SignedHtlcEntry}
    (h : HtlcWireProduces M law wctx ctx st hh e)
    {views : List HtlcWireView}
    (hbind : HtlcWireDigestCollisionFree M views)
    (hv : htlcWireViewOfState wctx ctx st hh ∈ views)
    {w : HtlcWireView} (hw : w ∈ views)
    (hver : M.ecdsaVerify ctx.commitmentKey
      (commitmentTag ++ htlcWireDigest M w) e.signature = true) :
    w.wire.version = 2 ∧
      w.wire.commitmentTxid = wctx.commitmentTxid ∧
      w.wire.commitmentOutputIndex = wctx.commitmentOutputIndex ∧
      w.wire.sequence = 0xffffffff ∧
      w.wire.valueSat = UInt64.ofNat hh.amount.toSatFloor ∧
      w.wire.scriptPubKey = wctx.htlcScript ∧
      w.wire.locktime = 0 ∧
      w.htlc.htlcId = hh.htlcId ∧
      w.htlc.parentCommitmentNumber = st.commitmentNumber ∧
      w.htlc.direction = hh.direction ∧
      w.htlc.htlcState = hh.htlcState ∧
      w.htlc.amountSat = hh.amount.toSatFloor ∧
      w.htlc.paymentHash = hh.paymentHash ∧
      w.htlc.cltvExpiry = hh.cltvExpiry ∧
      w.htlc.secondStageFeeSat = ctx.secondStageFeeSat := by
  have hwv := htlcWireSignature_binds_view hC3 h hbind hv hw hver
  subst hwv
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The bound entry's identification fields are the state HTLC's, so wire
binding reaches the wave-4 signed entry as well. -/
theorem htlcWireSignature_binds_entry {M : PrimitiveModel}
    {law : CommitmentSigningLaw M}
    {wctx : HtlcWireContext} {ctx : SighashContext} {st : SignedState}
    {hh : SignedHtlc} {e : SignedHtlcEntry}
    (h : HtlcWireProduces M law wctx ctx st hh e) :
    e.htlcId = hh.htlcId ∧ e.amount = hh.amount ∧
      e.paymentHash = hh.paymentHash ∧ e.direction = hh.direction ∧
      e.htlcState = hh.htlcState ∧ e.cltvExpiry = hh.cltvExpiry ∧
      e.signedDataDigest =
        htlcWireDigest M (htlcWireViewOfState wctx ctx st hh) :=
  ⟨h.htlcId_eq, h.amount_eq, h.paymentHash_eq, h.direction_eq, h.htlcState_eq,
    h.cltvExpiry_eq, h.signedDataDigest_eq⟩

/-! ## 6. Non-vacuity of the positive theorem -/

/-- A concrete wire context with a 32-byte parent commitment txid. -/
def exampleWireContext : HtlcWireContext where
  commitmentTxid := zeroBytes 32
  commitmentOutputIndex := 0
  htlcScript := zeroBytes 34

/-- The concrete state's single HTLC, projected out of `exampleSignedState`. -/
def exampleSignedHtlc : SignedHtlc where
  htlcId := 1
  amount := ⟨1000⟩
  paymentHash := ⟨ByteArray.empty⟩
  direction := .local
  htlcState := .offered
  cltvExpiry := 100
  signedDataDigest := ByteArray.empty

theorem exampleSignedHtlc_mem : exampleSignedHtlc ∈ exampleSignedState.htlcs := by
  simp [exampleSignedState, exampleSignedHtlc]

/-- **Instantiation on the concrete state.**  The wave-5 `exampleSignedState`
satisfies the main positive theorem with the singleton admissible wire-view
list, so the conditional is not vacuous. -/
theorem example_wireSignature_binds_view (M : PrimitiveModel)
    (hC3 : EufCma M.ecdsaVerify) (law : CommitmentSigningLaw M)
    (ctx : SighashContext) {w : HtlcWireView}
    (hw : w ∈ [htlcWireViewOfState exampleWireContext ctx exampleSignedState
      exampleSignedHtlc])
    (hver : M.ecdsaVerify ctx.commitmentKey
      (commitmentTag ++ htlcWireDigest M w)
      (wireEntryOfSighash M law exampleWireContext ctx exampleSignedState
        exampleSignedHtlc).signature = true) :
    w = htlcWireViewOfState exampleWireContext ctx exampleSignedState
      exampleSignedHtlc :=
  htlcWireSignature_binds_view hC3
    (wireEntryOfSighash_produces M law exampleWireContext ctx exampleSignedState
      exampleSignedHtlc)
    (htlcWireDigestCollisionFree_singleton M
      (htlcWireViewOfState exampleWireContext ctx exampleSignedState exampleSignedHtlc))
    (List.mem_singleton_self _) hw hver

/-- The honest derived wire signature verifies for the derived view. -/
theorem example_wireEntry_verifies (M : PrimitiveModel)
    (law : CommitmentSigningLaw M) (ctx : SighashContext) :
    M.ecdsaVerify ctx.commitmentKey
      (commitmentTag ++ htlcWireDigest M
        (htlcWireViewOfState exampleWireContext ctx exampleSignedState exampleSignedHtlc))
      (wireEntryOfSighash M law exampleWireContext ctx exampleSignedState
        exampleSignedHtlc).signature = true :=
  wireEntryOfSighash_signedBy M law exampleWireContext ctx exampleSignedState
    exampleSignedHtlc

/-! ## 7. Negative results

### 7.1 Digest binding alone does not bind the wire view

The existing `viewCollisionModel` satisfies the model's C1 field
(`CollisionResistant M.sha256`) and C3 (`EufCma M.ecdsaVerify`) and its
`sha256` collapses every input that is not 32 bytes.  Every tagged wire
preimage is at least 85 bytes, so every wire digest in that model is the same
32 zero bytes and one signature validates for every wire view. -/

theorem lazyModel_wireDigest (d₀ : ByteArray) (v : HtlcWireView) :
    htlcWireDigest (lazyModel d₀) v = zeroBytes 32 := by
  unfold htlcWireDigest
  rw [lazyModel_sha256]
  exact lazySha256_of_ne (taggedHtlcWirePreimage_size_ne_32 v)

/-- In the counterexample model every wire digest is the same 32 zero bytes. -/
theorem viewCollisionModel_wireDigest (v : HtlcWireView) :
    htlcWireDigest viewCollisionModel v = zeroBytes 32 :=
  lazyModel_wireDigest viewBindingTestMessage v

/-- Two distinct concrete wire views, differing in the parent commitment txid. -/
def shortTxidWireContext : HtlcWireContext where
  commitmentTxid := ByteArray.mk #[0x01]
  commitmentOutputIndex := 0
  htlcScript := zeroBytes 34

/-- A concrete structural HTLC view used by the negative examples. -/
def exampleHtlcView : HtlcSighashView where
  htlcId := 1
  parentCommitmentNumber := 0
  direction := .local
  htlcState := .offered
  amountSat := 1000
  paymentHash := ⟨ByteArray.empty⟩
  cltvExpiry := 100
  secondStageFeeSat := 0

def exampleWireView : HtlcWireView where
  wire := htlcWireOfView exampleWireContext exampleHtlcView
  htlc := exampleHtlcView

def shortTxidWireView : HtlcWireView where
  wire := htlcWireOfView shortTxidWireContext exampleHtlcView
  htlc := exampleHtlcView

theorem exampleWireView_ne_shortTxid :
    exampleWireView ≠ shortTxidWireView := by
  intro heq
  have hs := congrArg (fun v : HtlcWireView => v.wire.commitmentTxid.size) heq
  have h1 : exampleWireView.wire.commitmentTxid.size = 32 := by
    simp [exampleWireView, htlcWireOfView, exampleWireContext, zeroBytes_size]
  have h2 : shortTxidWireView.wire.commitmentTxid.size = 1 := by
    simp [shortTxidWireView, htlcWireOfView, shortTxidWireContext, oneByte_size]
  rw [h1, h2] at hs
  omega

/-- One signature is a valid wire-path signature for every wire view in the
collision model. -/
theorem wireSignedBy_viewCollisionModel (v : HtlcWireView) :
    HtlcWireSignedBy viewCollisionModel ⟨ByteArray.empty⟩ v ⟨ByteArray.empty⟩ := by
  unfold HtlcWireSignedBy SignedBy
  show (lazyModel viewBindingTestMessage).ecdsaVerify ⟨ByteArray.empty⟩
      (commitmentTag ++ htlcWireDigest viewCollisionModel v)
      ⟨ByteArray.empty⟩ = true
  rw [lazyModel_ecdsaVerify, viewCollisionModel_wireDigest]
  show decide (commitmentTag ++ zeroBytes 32 = commitmentTag ++ zeroBytes 32) = true
  exact decide_eq_true rfl

/-- **Mechanized counterexample: C1 + C3 do not bind the HTLC wire view.**
There is a model satisfying the model's C1 field and C3, one signature, and two
*distinct* wire views such that the signature is a valid wire-path signature for
both.  Digest binding therefore does not imply wire-view binding without
`HtlcWireDigestCollisionFree`. -/
theorem wire_digest_binding_not_view_binding :
    ∃ (M : PrimitiveModel) (pk : PubKey) (sig : EcdsaSig) (v w : HtlcWireView),
      v ≠ w ∧
        CollisionResistant M.sha256 ∧
        EufCma M.ecdsaVerify ∧
        HtlcWireSignedBy M pk v sig ∧
        HtlcWireSignedBy M pk w sig :=
  ⟨viewCollisionModel, ⟨ByteArray.empty⟩, ⟨ByteArray.empty⟩,
    exampleWireView, shortTxidWireView, exampleWireView_ne_shortTxid,
    viewCollisionModel.sha256_collisionResistant,
    viewCollisionModel.ecdsa_eufCma,
    wireSignedBy_viewCollisionModel exampleWireView,
    wireSignedBy_viewCollisionModel shortTxidWireView⟩

/-- The negated universal: in the collision model equal wire digests do not
imply equal wire views, so global wire-view binding is false even though C1 and
C3 hold. -/
theorem wireCollisionModel_not_viewBinding :
    ¬ (∀ v w : HtlcWireView,
        htlcWireDigest viewCollisionModel v =
          htlcWireDigest viewCollisionModel w → v = w) := by
  intro h
  have hd : htlcWireDigest viewCollisionModel exampleWireView =
      htlcWireDigest viewCollisionModel shortTxidWireView := by
    rw [viewCollisionModel_wireDigest, viewCollisionModel_wireDigest]
  exact exampleWireView_ne_shortTxid (h _ _ hd)

/-! ### 7.2 The wire path signs the floored satoshi amount only

This preserves and strengthens `htlcView_ignores_msat_fraction`: two HTLCs that
differ by one millisatoshi have the same wire view, hence the same wire digest
and the same wire-path signature.  The signed data does not bind `amount_msat`;
the millisatoshi amount survives only as unsigned wire data in the entry. -/

/-- A concrete signed HTLC parameterised by its millisatoshi amount. -/
def msatTestHtlc (amount : Msat) : SignedHtlc where
  htlcId := 1
  amount := amount
  paymentHash := ⟨ByteArray.empty⟩
  direction := .local
  htlcState := .offered
  cltvExpiry := 100
  signedDataDigest := ByteArray.empty

/-- **Millisecond-amount blindness, wire-path form.**  The two HTLCs differ by
exactly one millisatoshi and have the same wire view. -/
theorem htlcWireView_ignores_msat_fraction (wctx : HtlcWireContext)
    (ctx : SighashContext) (st : SignedState) :
    htlcWireViewOfState wctx ctx st (msatTestHtlc ⟨1000⟩) =
      htlcWireViewOfState wctx ctx st (msatTestHtlc ⟨1001⟩) := by
  have h := htlcView_ignores_msat_fraction (ctx := ctx) (st := st)
  simpa [htlcWireViewOfState, msatTestHtlc] using
    congrArg (fun v : HtlcSighashView =>
      (⟨htlcWireOfView wctx v, v⟩ : HtlcWireView)) h

/-- The millisatoshi amounts really differ, so the collision is not an artefact
of the test data. -/
theorem msatTestHtlc_amount_ne :
    (msatTestHtlc ⟨1000⟩).amount ≠ (msatTestHtlc ⟨1001⟩).amount := by
  intro h
  have hv : (1000 : Nat) = 1001 := congrArg Msat.val h
  exact absurd hv (by decide)

/-- **The wire-path signed data does not bind `amount_msat`.**  The derived
entries for the two HTLCs have equal `signedDataDigest` and equal `signature`,
while their `amount` fields differ. -/
theorem wireEntry_signedData_ignores_msat_fraction (M : PrimitiveModel)
    (law : CommitmentSigningLaw M) (wctx : HtlcWireContext)
    (ctx : SighashContext) (st : SignedState) :
    (wireEntryOfSighash M law wctx ctx st (msatTestHtlc ⟨1000⟩)).signedDataDigest =
        (wireEntryOfSighash M law wctx ctx st (msatTestHtlc ⟨1001⟩)).signedDataDigest ∧
      (wireEntryOfSighash M law wctx ctx st (msatTestHtlc ⟨1000⟩)).signature =
        (wireEntryOfSighash M law wctx ctx st (msatTestHtlc ⟨1001⟩)).signature ∧
      (wireEntryOfSighash M law wctx ctx st (msatTestHtlc ⟨1000⟩)).amount ≠
        (wireEntryOfSighash M law wctx ctx st (msatTestHtlc ⟨1001⟩)).amount := by
  have h := htlcWireView_ignores_msat_fraction wctx ctx st
  refine ⟨?_, ?_, ?_⟩
  · simp [h]
  · simp [h]
  · simpa using msatTestHtlc_amount_ne

/-- The wire digests themselves coincide, so the collision is at the full
signed-message level. -/
theorem wireDigest_ignores_msat_fraction (M : PrimitiveModel)
    (wctx : HtlcWireContext) (ctx : SighashContext) (st : SignedState) :
    htlcWireDigest M (htlcWireViewOfState wctx ctx st (msatTestHtlc ⟨1000⟩)) =
      htlcWireDigest M (htlcWireViewOfState wctx ctx st (msatTestHtlc ⟨1001⟩)) := by
  rw [htlcWireView_ignores_msat_fraction wctx ctx st]

/-- Consequently two distinct `SignedHtlc` records can produce the same wire
signature: wire binding is binding of the floored view, not of the raw HTLC
record. -/
theorem wireEntry_signature_collision (M : PrimitiveModel)
    (law : CommitmentSigningLaw M) (wctx : HtlcWireContext)
    (ctx : SighashContext) (st : SignedState) :
    ∃ (e₁ e₂ : SignedHtlcEntry),
      e₁.signature = e₂.signature ∧ e₁.signedDataDigest = e₂.signedDataDigest ∧
        e₁.amount ≠ e₂.amount :=
  ⟨wireEntryOfSighash M law wctx ctx st (msatTestHtlc ⟨1000⟩),
    wireEntryOfSighash M law wctx ctx st (msatTestHtlc ⟨1001⟩),
    (wireEntry_signedData_ignores_msat_fraction M law wctx ctx st).2.1,
    (wireEntry_signedData_ignores_msat_fraction M law wctx ctx st).1,
    (wireEntry_signedData_ignores_msat_fraction M law wctx ctx st).2.2⟩

/-! ### 7.3 The structural digest does not bind the wire bytes

`htlcDigest` reads the parent commitment view and `HtlcSighashView` only; it
never reads `HtlcWire`.  Two distinct wire views with the same structural view
therefore share the structural digest, which is exactly why the wire serializer
must add the wire bytes. -/

/-- Two distinct wire views with the same structural `HtlcSighashView`. -/
theorem wireView_not_determined_by_htlcView :
    ∃ v w : HtlcWireView, v ≠ w ∧ v.htlc = w.htlc :=
  ⟨exampleWireView, shortTxidWireView, exampleWireView_ne_shortTxid, rfl⟩

/-- The structural second-stage digest cannot distinguish two wire views that
share a structural view: digest binding on the structural path does not bind the
wire transaction. -/
theorem structuralDigest_ignores_wire (M : PrimitiveModel)
    (parent : CommitmentSighashView) :
    ∃ v w : HtlcWireView,
      v ≠ w ∧ htlcDigest M parent v.htlc = htlcDigest M parent w.htlc :=
  ⟨exampleWireView, shortTxidWireView, exampleWireView_ne_shortTxid, rfl⟩

/-! ## 8. Summary -/

set_option linter.unusedVariables false in
/-- Bundled faithful reading of the lane.

1. Equal wire views have equal wire digests (extensionality).
2. Under C3 and `HtlcWireDigestCollisionFree`, a produced wire signature that
   verifies for any admissible view's wire digest binds that view.
3. The binding hypothesis is non-vacuous on a singleton admissible list.
4. C1 as formalized plus C3 do **not** imply wire-view binding.
5. The signed wire data ignores the millisatoshi fraction of the HTLC amount.
6. The structural `htlcDigest` does not determine the wire transaction. -/
theorem htlc_wire_binding_summary :
    (∀ (M : PrimitiveModel) (v : HtlcWireView),
        (htlcWireDigest M v).size = 32) ∧
      (∀ (M : PrimitiveModel) (_hC3 : EufCma M.ecdsaVerify)
        (law : CommitmentSigningLaw M) (wctx : HtlcWireContext)
        (ctx : SighashContext) (st : SignedState) (hh : SignedHtlc)
        (e : SignedHtlcEntry),
        HtlcWireProduces M law wctx ctx st hh e →
        ∀ (views : List HtlcWireView),
          HtlcWireDigestCollisionFree M views →
          htlcWireViewOfState wctx ctx st hh ∈ views →
          ∀ w : HtlcWireView, w ∈ views →
            M.ecdsaVerify ctx.commitmentKey
              (commitmentTag ++ htlcWireDigest M w) e.signature = true →
            w = htlcWireViewOfState wctx ctx st hh) ∧
      (∀ (M : PrimitiveModel) (v : HtlcWireView),
        HtlcWireDigestCollisionFree M [v]) ∧
      (∃ (M : PrimitiveModel) (pk : PubKey) (sig : EcdsaSig) (v w : HtlcWireView),
        v ≠ w ∧ CollisionResistant M.sha256 ∧ EufCma M.ecdsaVerify ∧
          HtlcWireSignedBy M pk v sig ∧ HtlcWireSignedBy M pk w sig) ∧
      (∀ (M : PrimitiveModel) (law : CommitmentSigningLaw M)
        (wctx : HtlcWireContext) (ctx : SighashContext) (st : SignedState),
        (wireEntryOfSighash M law wctx ctx st (msatTestHtlc ⟨1000⟩)).signedDataDigest =
            (wireEntryOfSighash M law wctx ctx st (msatTestHtlc ⟨1001⟩)).signedDataDigest ∧
          (wireEntryOfSighash M law wctx ctx st (msatTestHtlc ⟨1000⟩)).amount ≠
            (wireEntryOfSighash M law wctx ctx st (msatTestHtlc ⟨1001⟩)).amount) ∧
      (∀ (M : PrimitiveModel) (parent : CommitmentSighashView),
        ∃ v w : HtlcWireView,
          v ≠ w ∧ htlcDigest M parent v.htlc = htlcDigest M parent w.htlc) :=
  ⟨fun M v => htlcWireDigest_size M v,
    fun M _hC3 law wctx ctx st hh e h views hbind hv w hw hver =>
      htlcWireSignature_binds_view _hC3 h hbind hv hw hver,
    fun M v => htlcWireDigestCollisionFree_singleton M v,
    wire_digest_binding_not_view_binding,
    fun M law wctx ctx st =>
      ⟨(wireEntry_signedData_ignores_msat_fraction M law wctx ctx st).1,
        (wireEntry_signedData_ignores_msat_fraction M law wctx ctx st).2.2⟩,
    structuralDigest_ignores_wire⟩

end LnLean.Proofs.WaveH.H12
