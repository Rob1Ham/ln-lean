/-
# H25 — the rich construction-site `viewOfState` adapter (CH-01, CH-02)

**Catalog issues.**

* `CH-01` (P1): the rich `CommitmentTx` construction site is not the path the
  legacy consumers read.  Wave 7 migrated the *record* and *consumer list*
  boundaries, but the sighash consumer still builds its view from
  `SignedState.toCommitment.commitmentOutputs` (`SighashTargets.viewOfState`),
  not from the rich, dust-trimmed, sorted `CommitmentTx.outputsNet`.
* `CH-02` (P1): the second-stage-fee/net path must be integrated end to end.
  The rich site is the one that carries `netAmountSat` and the dust limit, so
  the sighash view must be derivable from it.

**Result of this module.**  This module is purely additive; it edits no shared
module.  It builds the missing adapter at the rich site and proves it is the
same object as the wire view that `SighashTargets` already reasons about:

1. `wireOfTx` is the actual BOLT 3-shaped commitment wire transaction
   (`CommitmentWire`) built from a rich `CommitmentTx` and the sighash context:
   version 2, the context's funding outpoint, the obscured commitment number
   encoded into `nSequence`/`nLockTime`, and the rich `outputsNet` output list
   with its scripts.  `metaOfState` is the non-wire metadata.
2. `viewOfTx` is the construction-site `viewOfState` adapter: its scalar fields
   come from the sighash state/context, its outputs come from the rich
   `CommitmentTx.outputsNet` (the CH-03 net path), and its HTLC views come from
   the state's HTLC descriptors.
3. `viewOfTx_eq_viewOfWire` proves the adapter **is** `SighashTargets.viewOfWire`
   of the wire transaction it constructs.  Every `viewOfWire_*` field lemma and
   every structural-view theorem in `SighashTargets` therefore applies to the
   rich site unchanged.
4. `viewOfTx_outputs_perm_viewOfState` refines the adapter against the existing
   `SighashTargets.viewOfState` under the documented rich normal form (dust
   limit zero, both non-HTLC outputs nonzero, and the rich transaction carrying
   exactly the state's commitment).  The refinement is a `List.Perm`, not list
   equality: the rich site sorts and the legacy view does not, and D12 refutes
   any order-insensitive reading of the commitment digest.
5. `viewOfTx_eq_viewOfState_of_outputs` is the exact-equality form: when the
   rich net output list already projects to the legacy `commitmentOutputs`, the
   adapter is *definitionally the same view* as `SighashTargets.viewOfState`,
   so every existing `SighashProduces`/digest/coverage theorem applies with no
   new hypothesis.  This is the caller-side integration contract.
6. `wireOfTx_wellFormed` and `wireOfTx_txBytes_parse` show the constructed wire
   is a real parsable Bitcoin transaction under explicit bounds, and
   `viewOfTx_obscured` proves the rich view's obscured commitment number is
   exactly `SighashTargets.obscuredOfWire` of that wire.
7. `exampleTx_view_eq` and `exampleTx_digest_eq` are a non-vacuous concrete
   instance: a rich one-output commitment whose adapter equals the legacy view
   and therefore carries the same 32-byte commitment digest.

## Scope / honest gaps

* The structural `CommitmentSighashView` still does not model output scripts,
  so `viewOfTx` is strictly coarser than the wire bytes.  Two rich transactions
  with the same output *values* have the same view (`viewOfTx_eq_of_map_eq`)
  while their wires can differ; this is the construction-site counterpart of
  `SighashTargets.structuralView_not_determine_scripts` and is retained, not
  hidden.
* The HTLC identification data (`htlcId`, `paymentHash`) is not carried by
  `CommitmentHTLCOutput`; the adapter therefore reads the HTLC views from the
  sighash state `st` (`htlcViewsOfState`), exactly as `viewOfState` does.  A
  caller that only has a `CommitmentTx` must supply that metadata separately.
* The equality/permutation results are stated against
  `st.toCommitment = tx.commitment`; without the state there is no HTLC
  identity and no legacy view to compare against.
* The obscured-number encoding is proved for `obscuredCommitmentNumber < 2^48`
  (BOLT 3's 48-bit field); no claim is made for out-of-range values.

## Anchors

* BOLT 3 §"Commitment Transaction" (`refs/bolts/03-transactions.md:83-353`):
  obscured commitment number in `nSequence`/`nLockTime`, funding outpoint,
  ordered output set.
* Model: `LnLean/Proofs/Channel/SighashTargets.lean` §2 (`viewOfState`),
  §12.1-12.2 (`CommitmentWire`, `CommitmentMeta`, `viewOfWire`,
  `obscuredOfWire`, `Obscures`); `LnLean/Channel/Commitment.lean`
  (`CommitmentTx`, `outputsNet`, `CommitmentTxOutput.toCommitmentOutput`,
  `map_toCommitmentOutput_outputsUnsorted`).
-/

import LnLean.Proofs.Channel.SighashTargets

namespace LnLean.Proofs.WaveH.H25

set_option autoImplicit false

open LnLean
open LnLean.Channel
open LnLean.Crypto
open LnLean.Protocol
open LnLean.Proofs.ProtocolWireTargets
open LnLean.Proofs.Channel.SighashTargets

/-! ## 1. The wire transaction at the rich construction site -/

/-- The wire output corresponding to one rich commitment output: the value
projection `CommitmentTxOutput.toCommitmentOutput` plus the output script the
rich site carries. -/
def toExactOutput (o : CommitmentTxOutput) : ExactCommitmentOutput :=
  { output := o.toCommitmentOutput
    scriptPubKey := o.scriptPubKey.bytes.toByteArray }

/-- The wire output projects back to the structural `CommitmentOutput`. -/
@[simp] theorem toExactOutput_output (o : CommitmentTxOutput) :
    (toExactOutput o).output = o.toCommitmentOutput := rfl

/-- The wire output keeps the rich script bytes. -/
@[simp] theorem toExactOutput_scriptPubKey (o : CommitmentTxOutput) :
    (toExactOutput o).scriptPubKey = o.scriptPubKey.bytes.toByteArray := rfl

/-- BOLT 3 high 24 bits of the obscured commitment number, carried in
`nSequence` as `0x80000000 | high24`. -/
def sequenceOfObscured (obscured : Nat) : UInt32 :=
  UInt32.ofNat (0x80000000 + (obscured / 2 ^ 24) % 2 ^ 24)

/-- BOLT 3 low 24 bits of the obscured commitment number, carried in
`nLockTime` as `0x20000000 | low24`. -/
def locktimeOfObscured (obscured : Nat) : UInt32 :=
  UInt32.ofNat (0x20000000 + obscured % 2 ^ 24)

/-- The actual commitment wire transaction of a rich `CommitmentTx`: version 2,
the context funding outpoint, the obscured commitment number in
`nSequence`/`nLockTime`, and the rich net output list with scripts.  This is
the construction site the sighash consumer should sign. -/
def wireOfTx (ctx : SighashContext) (tx : CommitmentTx) : CommitmentWire where
  version := 2
  fundingTxid := ctx.fundingTxid
  fundingOutputIndex := UInt32.ofNat ctx.fundingOutputIndex
  sequence := sequenceOfObscured ctx.obscuredCommitmentNumber
  outputs := tx.outputsNet.map toExactOutput
  locktime := locktimeOfObscured ctx.obscuredCommitmentNumber

@[simp] theorem wireOfTx_fundingTxid (ctx : SighashContext) (tx : CommitmentTx) :
    (wireOfTx ctx tx).fundingTxid = ctx.fundingTxid := rfl

@[simp] theorem wireOfTx_outputs (ctx : SighashContext) (tx : CommitmentTx) :
    (wireOfTx ctx tx).outputs =
      tx.outputsNet.map toExactOutput := rfl

@[simp] theorem wireOfTx_outputs_map (ctx : SighashContext) (tx : CommitmentTx) :
    (wireOfTx ctx tx).outputs.map (fun o => o.output) =
      tx.outputsNet.map CommitmentTxOutput.toCommitmentOutput := by
  simp [wireOfTx, List.map_map, toExactOutput]

/-- The rich net output count is the wire output count. -/
@[simp] theorem wireOfTx_outputs_length (ctx : SighashContext) (tx : CommitmentTx) :
    (wireOfTx ctx tx).outputs.length = tx.outputsNet.length := by
  simp [wireOfTx]

/-! ## 2. The non-wire metadata of the state and context -/

/-- The non-wire metadata `SighashTargets.CommitmentMeta` determined by the
sighash state and context.  The HTLC views are the state's, exactly as in
`SighashTargets.viewOfState`. -/
def metaOfState (ctx : SighashContext) (st : SignedState) : CommitmentMeta where
  commitmentNumber := st.commitmentNumber
  obscuredCommitmentNumber := ctx.obscuredCommitmentNumber
  fundingValueSat := st.fundingValueSat
  fundingScript := ctx.fundingScript
  holder := st.holder
  toLocalSat := st.toLocalSat
  toRemoteSat := st.toRemoteSat
  feeSat := st.feeSat
  contestDelay := st.contestDelay
  anchorOutputs := st.anchorOutputs
  feeratePerKw := st.feerate.msatPerKw
  htlcs := htlcViewsOfState ctx st

@[simp] theorem metaOfState_commitmentNumber (ctx : SighashContext)
    (st : SignedState) :
    (metaOfState ctx st).commitmentNumber = st.commitmentNumber := rfl

@[simp] theorem metaOfState_htlcs (ctx : SighashContext) (st : SignedState) :
    (metaOfState ctx st).htlcs = htlcViewsOfState ctx st := rfl

@[simp] theorem metaOfState_obscured (ctx : SighashContext) (st : SignedState) :
    (metaOfState ctx st).obscuredCommitmentNumber =
      ctx.obscuredCommitmentNumber := rfl

/-! ## 3. The construction-site `viewOfState` adapter -/

/-- **The rich-site `viewOfState` adapter.**  The scalar view fields are the
sighash state/context fields (identical to `SighashTargets.viewOfState`), while
the output list is the rich `CommitmentTx.outputsNet` net construction rather
than the legacy `Commitment.commitmentOutputs` projection.  The HTLC views are
the state's, because `CommitmentHTLCOutput` carries no `htlcId`/`paymentHash`.
-/
def viewOfTx (ctx : SighashContext) (st : SignedState) (tx : CommitmentTx) :
    CommitmentSighashView where
  commitmentNumber := st.commitmentNumber
  obscuredCommitmentNumber := ctx.obscuredCommitmentNumber
  fundingTxid := ctx.fundingTxid
  fundingOutputIndex := ctx.fundingOutputIndex
  fundingValueSat := st.fundingValueSat
  fundingScript := ctx.fundingScript
  holder := st.holder
  toLocalSat := st.toLocalSat
  toRemoteSat := st.toRemoteSat
  outputs := tx.outputsNet.map CommitmentTxOutput.toCommitmentOutput
  feeSat := st.feeSat
  contestDelay := st.contestDelay
  anchorOutputs := st.anchorOutputs
  feeratePerKw := st.feerate.msatPerKw
  htlcs := htlcViewsOfState ctx st

@[simp] theorem viewOfTx_commitmentNumber (ctx : SighashContext)
    (st : SignedState) (tx : CommitmentTx) :
    (viewOfTx ctx st tx).commitmentNumber = st.commitmentNumber := rfl

@[simp] theorem viewOfTx_fundingTxid (ctx : SighashContext) (st : SignedState)
    (tx : CommitmentTx) :
    (viewOfTx ctx st tx).fundingTxid = ctx.fundingTxid := rfl

@[simp] theorem viewOfTx_holder (ctx : SighashContext) (st : SignedState)
    (tx : CommitmentTx) :
    (viewOfTx ctx st tx).holder = st.holder := rfl

@[simp] theorem viewOfTx_outputs (ctx : SighashContext) (st : SignedState)
    (tx : CommitmentTx) :
    (viewOfTx ctx st tx).outputs =
      tx.outputsNet.map CommitmentTxOutput.toCommitmentOutput := rfl

@[simp] theorem viewOfTx_outputs_length (ctx : SighashContext) (st : SignedState)
    (tx : CommitmentTx) :
    (viewOfTx ctx st tx).outputs.length = tx.outputsNet.length := by
  simp [viewOfTx]

@[simp] theorem viewOfTx_htlcs (ctx : SighashContext) (st : SignedState)
    (tx : CommitmentTx) :
    (viewOfTx ctx st tx).htlcs = htlcViewsOfState ctx st := rfl

@[simp] theorem viewOfTx_feeSat (ctx : SighashContext) (st : SignedState)
    (tx : CommitmentTx) :
    (viewOfTx ctx st tx).feeSat = st.feeSat := rfl

/-! ## 4. Agreement with the `SighashTargets` wire view -/

/-- **The adapter is the wire view.**  Under the wire-domain hypothesis
`fundingOutputIndex < 2^32` (the BOLT 3 output index is a 4-byte field), the
view built at the rich construction site is exactly
`SighashTargets.viewOfWire` of the wire transaction it constructs.  This is the
sense in which the adapter "agrees with the wire-view fields used by
`SighashTargets`": every `viewOfWire_*` projection and every structural-view
theorem applies verbatim.  Without the bound only the index field can differ,
and `viewOfTx_fundingOutputIndex_mod` records the exact modulo relation. -/
theorem viewOfTx_eq_viewOfWire (ctx : SighashContext) (st : SignedState)
    (tx : CommitmentTx) (hidx : ctx.fundingOutputIndex < 2 ^ 32) :
    viewOfTx ctx st tx = viewOfWire (wireOfTx ctx tx) (metaOfState ctx st) := by
  simp [viewOfTx, viewOfWire, wireOfTx, metaOfState,
    toExactOutput, List.map_map, Nat.mod_eq_of_lt hidx]

/-- The funding outpoint of the rich view is the wire outpoint (txid exactly,
index modulo the 32-bit wire width). -/
theorem viewOfTx_fundingOutputIndex_mod (ctx : SighashContext)
    (st : SignedState) (tx : CommitmentTx) :
    (viewOfTx ctx st tx).fundingOutputIndex % 2 ^ 32 =
      (wireOfTx ctx tx).fundingOutputIndex.toNat := by
  simp [viewOfTx, wireOfTx]

/-- In the wire domain (`fundingOutputIndex < 2^32`) the rich view's funding
output index is exactly the wire field. -/
theorem viewOfTx_fundingOutputIndex_of_lt (ctx : SighashContext)
    (st : SignedState) (tx : CommitmentTx)
    (h : ctx.fundingOutputIndex < 2 ^ 32) :
    (viewOfTx ctx st tx).fundingOutputIndex =
      (wireOfTx ctx tx).fundingOutputIndex.toNat := by
  calc (viewOfTx ctx st tx).fundingOutputIndex
      = (viewOfTx ctx st tx).fundingOutputIndex % 2 ^ 32 :=
        (Nat.mod_eq_of_lt h).symm
    _ = (wireOfTx ctx tx).fundingOutputIndex.toNat :=
        viewOfTx_fundingOutputIndex_mod ctx st tx

/-- The rich view's output list is the wire output list projected onto the
structural `CommitmentOutput` type.  This is `viewOfWire_outputs` at the rich
site. -/
theorem viewOfTx_outputs_eq_wire (ctx : SighashContext) (st : SignedState)
    (tx : CommitmentTx) :
    (viewOfTx ctx st tx).outputs =
      (wireOfTx ctx tx).outputs.map (fun o => o.output) := by
  rw [wireOfTx_outputs_map]
  rfl

/-- The rich view's commitment number is the wire metadata's commitment
number (`viewOfWire_commitmentNumber` at the rich site). -/
theorem viewOfTx_commitmentNumber_eq_wire (ctx : SighashContext)
    (st : SignedState) (tx : CommitmentTx) :
    (viewOfTx ctx st tx).commitmentNumber =
      (metaOfState ctx st).commitmentNumber := rfl

/-- The rich view's HTLC list is the wire metadata's HTLC list
(`viewOfWire_htlcs` at the rich site). -/
theorem viewOfTx_htlcs_eq_wire (ctx : SighashContext) (st : SignedState)
    (tx : CommitmentTx) :
    (viewOfTx ctx st tx).htlcs = (metaOfState ctx st).htlcs := rfl

/-! ## 5. The obscured commitment number of the constructed wire -/

/-- With the BOLT 3 48-bit obscured number, the constructed wire satisfies
`SighashTargets.Obscures` for the state metadata. -/
theorem wireOfTx_obscures (ctx : SighashContext) (st : SignedState)
    (tx : CommitmentTx) (h : ctx.obscuredCommitmentNumber < 2 ^ 48) :
    Obscures (wireOfTx ctx tx) (metaOfState ctx st) := by
  refine ⟨h, ?_, ?_⟩
  · show (UInt32.ofNat (0x20000000 + ctx.obscuredCommitmentNumber % 2 ^ 24)).toNat =
      0x20000000 + (ctx.obscuredCommitmentNumber % 2 ^ 24)
    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt]
    omega
  · show (UInt32.ofNat
        (0x80000000 + (ctx.obscuredCommitmentNumber / 2 ^ 24) % 2 ^ 24)).toNat =
      0x80000000 + ((ctx.obscuredCommitmentNumber / 2 ^ 24) % 2 ^ 24)
    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt]
    omega

/-- **The rich view's obscured number is the wire's.**  Under the 48-bit
domain hypothesis, the adapter's `obscuredCommitmentNumber` is exactly
`SighashTargets.obscuredOfWire` of the wire transaction the rich site builds. -/
theorem viewOfTx_obscured (ctx : SighashContext) (st : SignedState)
    (tx : CommitmentTx) (h : ctx.obscuredCommitmentNumber < 2 ^ 48) :
    (viewOfTx ctx st tx).obscuredCommitmentNumber =
      obscuredOfWire (wireOfTx ctx tx) := by
  have hobs := wireOfTx_obscures ctx st tx h
  rw [obscuredOfWire_eq_of_obscures (wireOfTx ctx tx) (metaOfState ctx st) hobs]
  simp [viewOfTx, metaOfState, Nat.mod_eq_of_lt h]

/-! ## 6. Agreement with the existing `viewOfState` -/

/-- **Exact refinement at the caller boundary.**  If the rich net output list
projects to the state's legacy `CommitmentOutput` list, the adapter is the same
view as `SighashTargets.viewOfState`.  Every existing `SighashTargets` theorem
(digest derivation, `SighashProduces`, C3 binding, coverage) then applies to
the rich construction site with no new hypothesis. -/
theorem viewOfTx_eq_viewOfState_of_outputs (ctx : SighashContext)
    (st : SignedState) (tx : CommitmentTx)
    (hout : tx.outputsNet.map CommitmentTxOutput.toCommitmentOutput =
      st.toCommitment.commitmentOutputs) :
    viewOfTx ctx st tx = viewOfState ctx st := by
  simp [viewOfTx, viewOfState, hout]

/-- **The rich site inherits the derived commitment digest.**  Under exact
output agreement, the `SighashTargets.honestFull` record's commitment digest
is the digest of the rich adapter's view. -/
theorem honestFull_commitmentDigest_eq_rich (M : PrimitiveModel)
    (law : CommitmentSigningLaw M) (ctx : SighashContext) (st : SignedState)
    (tx : CommitmentTx)
    (hout : tx.outputsNet.map CommitmentTxOutput.toCommitmentOutput =
      st.toCommitment.commitmentOutputs) :
    (honestFull M law ctx st).commitmentDigest =
      commitmentDigest M (viewOfTx ctx st tx) := by
  rw [viewOfTx_eq_viewOfState_of_outputs ctx st tx hout]
  rfl

/-- **C3 binds the rich-site digest.**  Under exact output agreement, a
produced commitment signature in the commitment domain validates for no
message other than the rich adapter's derived digest. -/
theorem sighashProduces_signature_binds_rich_digest (M : PrimitiveModel)
    (hC3 : EufCma M.ecdsaVerify) (law : CommitmentSigningLaw M)
    (ctx : SighashContext) (st : SignedState) (tx : CommitmentTx)
    (hout : tx.outputsNet.map CommitmentTxOutput.toCommitmentOutput =
      st.toCommitment.commitmentOutputs)
    {f : CommitmentSignedFull} (h : SighashProduces M law ctx st f)
    {msg : ByteArray}
    (hver : M.ecdsaVerify ctx.commitmentKey (commitmentTag ++ msg)
      f.commitmentSignature = true) :
    msg = commitmentDigest M (viewOfTx ctx st tx) := by
  rw [← honestFull_commitmentDigest_eq_rich M law ctx st tx hout]
  exact SighashProduces.signature_binds_digest hC3 h hver

/-- With dust limit zero the rich net construction is the legacy gross
construction before sorting: both `htlcOutputNet` and `htlcOutput` keep every
HTLC, because the dust test `0 ≤ value` always holds. -/
theorem htlcOutputNet_eq_htlcOutput_of_dustLimit_zero (tx : CommitmentTx)
    (h : tx.dustLimitSat = 0) (x : CommitmentHTLCOutput) :
    tx.htlcOutputNet x = tx.htlcOutput x := by
  simp [CommitmentTx.htlcOutputNet, CommitmentTx.htlcOutput, h]

theorem outputsUnsortedNet_eq_outputsUnsorted_of_dustLimit_zero
    (tx : CommitmentTx) (h : tx.dustLimitSat = 0) :
    tx.outputsUnsortedNet = tx.outputsUnsorted := by
  have hf : tx.htlcOutputNet = tx.htlcOutput :=
    funext (htlcOutputNet_eq_htlcOutput_of_dustLimit_zero tx h)
  simp [CommitmentTx.outputsUnsortedNet, CommitmentTx.outputsUnsorted, hf]

/-- **Rich normal form refines the legacy view up to output order.**  Under the
documented rich normal form (dust limit zero, both non-HTLC outputs nonzero,
and the rich transaction carrying exactly the state's commitment), the rich
view's output list is a permutation of the legacy view's output list.  The
permutation is not strengthened to equality: the rich site sorts (BOLT 3) and
the legacy view keeps construction order, and D12 keeps the ordering
refutation. -/
theorem viewOfTx_outputs_perm_viewOfState (ctx : SighashContext)
    (st : SignedState) (tx : CommitmentTx)
    (hst : tx.commitment = st.toCommitment)
    (hdust : tx.dustLimitSat = 0)
    (hl : st.toCommitment.toLocalSat ≠ 0)
    (hr : st.toCommitment.toRemoteSat ≠ 0) :
    (viewOfTx ctx st tx).outputs.Perm (viewOfState ctx st).outputs := by
  have hmap : tx.outputsUnsorted.map CommitmentTxOutput.toCommitmentOutput =
      st.toCommitment.commitmentOutputs := by
    have hrich := CommitmentTx.map_toCommitmentOutput_outputsUnsorted tx hdust
      (by rw [hst]; exact hl) (by rw [hst]; exact hr)
    rwa [hst] at hrich
  have hperm := (CommitmentTx.outputsNet_perm tx).map
    CommitmentTxOutput.toCommitmentOutput
  rw [outputsUnsortedNet_eq_outputsUnsorted_of_dustLimit_zero tx hdust] at hperm
  simpa [viewOfTx, viewOfState, hmap] using hperm

/-- The wire-level consequence of the normal form: the rich view and the legacy
view have the same number of outputs. -/
theorem viewOfTx_outputs_length_eq_viewOfState (ctx : SighashContext)
    (st : SignedState) (tx : CommitmentTx)
    (hst : tx.commitment = st.toCommitment)
    (hdust : tx.dustLimitSat = 0)
    (hl : st.toCommitment.toLocalSat ≠ 0)
    (hr : st.toCommitment.toRemoteSat ≠ 0) :
    (viewOfTx ctx st tx).outputs.length = (viewOfState ctx st).outputs.length :=
  (viewOfTx_outputs_perm_viewOfState ctx st tx hst hdust hl hr).length_eq

/-! ## 7. The adapter drops output scripts (retained coarseness) -/

/-- Two rich transactions whose net output lists project to the same
`CommitmentOutput` list give the same view, regardless of their scripts. -/
theorem viewOfTx_eq_of_map_eq (ctx : SighashContext) (st : SignedState)
    {tx₁ tx₂ : CommitmentTx}
    (h : tx₁.outputsNet.map CommitmentTxOutput.toCommitmentOutput =
      tx₂.outputsNet.map CommitmentTxOutput.toCommitmentOutput) :
    viewOfTx ctx st tx₁ = viewOfTx ctx st tx₂ := by
  simp [viewOfTx, h]

/-- The structural projection of a non-anchor rich output preserves its value.
Anchors are canonicalized to the BOLT 3 330 satoshis, which is why this needs
the two anchor exclusions. -/
theorem toCommitmentOutput_value_of_not_anchor (o : CommitmentTxOutput)
    (hl : o.kind ≠ .localAnchor) (hr : o.kind ≠ .remoteAnchor) :
    o.toCommitmentOutput.value = o.valueSat := by
  rcases o with ⟨k, v, s, c⟩
  cases k with
  | toLocal => rfl
  | toRemote => rfl
  | htlc d => rfl
  | localAnchor => exact absurd rfl hl
  | remoteAnchor => exact absurd rfl hr

/-- Every projected output is bounded by the rich output's value or by the
canonical 330-satoshi anchor value. -/
theorem toCommitmentOutput_value_lt (o : CommitmentTxOutput)
    (h : o.valueSat < 2 ^ 63) : o.toCommitmentOutput.value < 2 ^ 63 := by
  rcases o with ⟨k, v, s, c⟩
  cases k <;>
    simp [CommitmentTxOutput.toCommitmentOutput, CommitmentOutput.value,
      anchorOutputSat] <;>
    omega

/-! ## 8. The constructed wire is a real transaction -/

/-- Under explicit bounds the constructed wire is in the serialization wire
domain. -/
theorem wireOfTx_wellFormed (ctx : SighashContext) (tx : CommitmentTx)
    (hfund : ctx.fundingTxid.size = 32)
    (hlen : tx.outputsNet.length ≤ Bitcoin.Serialization.MAX_SIZE)
    (hbound : ∀ o ∈ tx.outputsNet,
      o.scriptPubKey.bytes.length ≤ Bitcoin.Serialization.MAX_SIZE ∧
        o.valueSat < 2 ^ 63) :
    (wireOfTx ctx tx).WellFormed := by
  refine ⟨hfund, by simpa [wireOfTx] using hlen, ?_⟩
  intro o ho
  rw [wireOfTx_outputs, List.mem_map] at ho
  obtain ⟨a, ha, rfl⟩ := ho
  obtain ⟨hsz, hval⟩ := hbound a ha
  exact ⟨by simpa using hsz, by simpa using toCommitmentOutput_value_lt a hval⟩

/-- The constructed wire serializes and parses back to its own transaction.
This is the round-trip guarantee that makes the adapter's wire an actual
Bitcoin transaction rather than an abstract view. -/
theorem wireOfTx_txBytes_parse (ctx : SighashContext) (tx : CommitmentTx)
    (h : (wireOfTx ctx tx).WellFormed) :
    Bitcoin.Serialization.decTxCore (Bitcoin.Serialization.bL (wireOfTx ctx tx).txBytes) =
      .ok ((wireOfTx ctx tx).toTx, []) :=
  CommitmentWire.txBytes_parse (wireOfTx ctx tx) h

/-! ## 9. Non-vacuity: a concrete rich construction site -/

/-- A concrete funding txid. -/
def exampleFundingTxid : ByteArray := ByteArray.mk ((List.replicate 32 (0x11 : UInt8)).toArray)

/-- A concrete sighash context. -/
def exampleCtx : SighashContext where
  fundingTxid := exampleFundingTxid
  fundingOutputIndex := 0
  fundingScript := ByteArray.mk #[0x51]
  obscuredCommitmentNumber := 0x1234
  secondStageFeeSat := 0
  commitmentKey := ⟨ByteArray.empty⟩

/-- A concrete zero-HTLC state with a single surviving `to_local` output: the
`to_remote` value is below the rich site's dust limit. -/
def exampleSt : SignedState where
  channelId := ChannelId.zero
  holder := .local
  commitmentNumber := 0
  fundingValueSat := 3000
  toLocalSat := 2000
  toRemoteSat := 0
  feeSat := 1000
  contestDelay := 144
  anchorOutputs := false
  feerate := ⟨1000⟩
  commitmentDigest := ByteArray.empty
  htlcs := []

/-- The rich construction of `exampleSt`. -/
def exampleTx : CommitmentTx where
  commitment := exampleSt.toCommitment
  dustLimitSat := 1000
  toLocalScript := ⟨[0x51]⟩
  toRemoteScript := ⟨[0x51]⟩
  localAnchorScript := ⟨[0x51]⟩
  remoteAnchorScript := ⟨[0x51]⟩
  htlcScript := fun _ => ⟨[0x51]⟩

/-- The rich pre-sort net output list is the single `to_local` output. -/
theorem exampleTx_outputsUnsortedNet :
    exampleTx.outputsUnsortedNet =
      [CommitmentTxOutput.toLocal 2000 exampleTx.toLocalScript] := by
  simp [CommitmentTx.outputsUnsortedNet, CommitmentTx.toLocalOutput,
    CommitmentTx.toRemoteOutput, CommitmentTx.localAnchorOutput,
    CommitmentTx.remoteAnchorOutput, exampleTx, exampleSt,
    SignedState.toCommitment]

/-- The rich net output list is the single `to_local` output. -/
theorem exampleTx_outputsNet :
    exampleTx.outputsNet = [CommitmentTxOutput.toLocal 2000 exampleTx.toLocalScript] := by
  rw [CommitmentTx.outputsNet, exampleTx_outputsUnsortedNet, sortOutputs,
    List.mergeSort_singleton]

/-- The concrete adapter equals the legacy view at the same site. -/
theorem exampleTx_view_eq :
    viewOfTx exampleCtx exampleSt exampleTx = viewOfState exampleCtx exampleSt := by
  apply viewOfTx_eq_viewOfState_of_outputs
  rw [exampleTx_outputsNet]
  simp [exampleSt, SignedState.toCommitment, Commitment.commitmentOutputs,
    CommitmentTxOutput.toCommitmentOutput, CommitmentTxOutput.toLocal]

/-- The concrete adapter's commitment digest is exactly the legacy derived
digest, so the rich site inherits every `SighashTargets` digest theorem. -/
theorem exampleTx_digest_eq (M : PrimitiveModel) :
    commitmentDigest M (viewOfTx exampleCtx exampleSt exampleTx) =
      commitmentDigest M (viewOfState exampleCtx exampleSt) := by
  rw [exampleTx_view_eq]

/-- The concrete digest is 32 bytes, as in `SighashTargets`. -/
theorem exampleTx_digest_size (M : PrimitiveModel) :
    (commitmentDigest M (viewOfTx exampleCtx exampleSt exampleTx)).size = 32 :=
  commitmentDigest_size M _

/-- The concrete wire is well formed and parses: the adapter is attached to a
real serializable transaction even in the non-vacuous instance. -/
theorem exampleTx_wire_wellFormed : (wireOfTx exampleCtx exampleTx).WellFormed := by
  refine ⟨?_, ?_, ?_⟩
  · show (List.replicate 32 (0x11 : UInt8)).toArray.size = 32
    simp
  · rw [wireOfTx_outputs, exampleTx_outputsNet]
    decide
  · intro o ho
    rw [wireOfTx_outputs, List.mem_map] at ho
    obtain ⟨a, ha, rfl⟩ := ho
    rw [exampleTx_outputsNet] at ha
    simp only [List.mem_singleton] at ha
    subst ha
    exact ⟨by decide, by decide⟩

/-- The concrete wire round-trips through the serializer. -/
theorem exampleTx_wire_parse :
    Bitcoin.Serialization.decTxCore
        (Bitcoin.Serialization.bL (wireOfTx exampleCtx exampleTx).txBytes) =
      .ok ((wireOfTx exampleCtx exampleTx).toTx, []) :=
  wireOfTx_txBytes_parse exampleCtx exampleTx exampleTx_wire_wellFormed

/-! ## 10. Summary -/

/-- Bundled faithful reading of the lane.

1. The adapter is exactly the `SighashTargets` wire view of the wire
   transaction the rich construction site builds.
2. Its funding outpoint, output list, commitment number, HTLC list, and
   obscured number are the wire fields.
3. Under the rich normal form its output list is a permutation of the legacy
   `viewOfState` output list; under exact output agreement the two views are
   equal and all existing digest/coverage theorems transfer.
4. The constructed wire is well formed and parses.
5. The view remains coarser than the wire bytes (scripts dropped). -/
theorem viewOfTx_summary :
    (∀ (ctx : SighashContext) (st : SignedState) (tx : CommitmentTx),
        ctx.fundingOutputIndex < 2 ^ 32 →
        viewOfTx ctx st tx = viewOfWire (wireOfTx ctx tx) (metaOfState ctx st)) ∧
      (∀ (ctx : SighashContext) (st : SignedState) (tx : CommitmentTx)
        (_h : ctx.obscuredCommitmentNumber < 2 ^ 48),
        (viewOfTx ctx st tx).obscuredCommitmentNumber =
          obscuredOfWire (wireOfTx ctx tx)) ∧
      (∀ (ctx : SighashContext) (st : SignedState) (tx : CommitmentTx),
        tx.outputsNet.map CommitmentTxOutput.toCommitmentOutput =
            st.toCommitment.commitmentOutputs →
          viewOfTx ctx st tx = viewOfState ctx st) ∧
      (∀ (ctx : SighashContext) (st : SignedState) (tx : CommitmentTx),
        tx.commitment = st.toCommitment →
        tx.dustLimitSat = 0 →
        st.toCommitment.toLocalSat ≠ 0 →
        st.toCommitment.toRemoteSat ≠ 0 →
        (viewOfTx ctx st tx).outputs.Perm (viewOfState ctx st).outputs) ∧
      (∀ (ctx : SighashContext) (tx : CommitmentTx),
        (wireOfTx ctx tx).WellFormed →
        Bitcoin.Serialization.decTxCore
            (Bitcoin.Serialization.bL (wireOfTx ctx tx).txBytes) =
          .ok ((wireOfTx ctx tx).toTx, [])) ∧
      (∀ (M : PrimitiveModel),
        commitmentDigest M (viewOfTx exampleCtx exampleSt exampleTx) =
          commitmentDigest M (viewOfState exampleCtx exampleSt)) :=
  ⟨viewOfTx_eq_viewOfWire,
    viewOfTx_obscured,
    viewOfTx_eq_viewOfState_of_outputs,
    viewOfTx_outputs_perm_viewOfState,
    wireOfTx_txBytes_parse,
    fun _M => exampleTx_digest_eq _M⟩

end LnLean.Proofs.WaveH.H25
