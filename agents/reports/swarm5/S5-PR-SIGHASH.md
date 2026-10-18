# S5-PR-SIGHASH — BOLT 3 commitment sighash serializer, `SighashProduces`, C3 binding

**Lane:** `S5-PR-SIGHASH`
**Issues:** `PR-02` (P1, open/mitigated), `PR-01` (P1, open)
**Worktree:** `/home/ubuntu/ln-lean-repair`
**Branch / base:** `repair/integrated` @ `79a92ce` (wave-5 plan); code base `74d6475`
**Toolchain:** `leanprover/lean4:v4.35.0`

**Owned files changed**

| File | Change |
|---|---|
| `LnLean/Protocol/Messages.lean` | **No change.** The existing `CommitmentSignedFull` / `SignedHtlcEntry` records are imported unchanged; the new model is signer-side, so no wire type was added or modified. |
| `LnLean/Proofs/Channel/SighashTargets.lean` | **New** (960 lines): BOLT 3-shaped commitment and per-HTLC sighash models, serializers, digests, `SignedBy`, `SighashProduces`, honest constructor, C3 binding, coverage composition, load-bearing negative, funding/key-binding contract, preserved legacy negatives. |
| `agents/reports/swarm5/S5-PR-SIGHASH.md` | This report. |

**Verdict.** PR-02 is narrowed from "digests and signatures are supplied data"
to "digests and signatures are equations to a BOLT 3-shaped serializer". The
new relation `SighashProduces` derives the commitment digest, commitment
signature, every per-HTLC digest, every per-HTLC signature, and the full signed
entry list from `(PrimitiveModel, CommitmentSigningLaw, SighashContext,
SignedState)`. Two records produced from the same inputs are *the same record*
(`SighashProduces.eq_honestFull`), and under C3 a produced signature verifies
for no digest other than the derived one. The relation composes with the
wave-4 `ProducedFrom`/coverage theorem without changing it, and a mechanized
negative shows `ProducedFrom` alone does **not** determine the digest. PR-01 is
addressed by one signing law serving both the funding and commitment domains,
plus the explicit `Crypto.KeyBinding` contract; C3 alone still does not give key
attribution, and that separation is retained.

---

## 1. Model additions

All declarations are in namespace
`LnLean.Proofs.Channel.SighashTargets`.  The module imports
`LnLean.Protocol.Messages`, `LnLean.Channel.Commitment`,
`LnLean.Channel.Fee`, `LnLean.Crypto.Sig`,
`LnLean.Proofs.ProtocolCoverageTargets`,
`LnLean.Proofs.ProtocolWireTargets`, and
`LnLean.Proofs.ProtocolSigningTargets`.

### 1.1 Commitment view (BOLT 3 fields)

```lean
structure CommitmentSighashView where
  commitmentNumber : Nat
  obscuredCommitmentNumber : Nat
  fundingTxid : ByteArray
  fundingOutputIndex : Nat
  fundingValueSat : Nat
  fundingScript : ByteArray
  holder : Direction
  toLocalSat : Nat
  toRemoteSat : Nat
  outputs : List CommitmentOutput
  feeSat : Nat
  contestDelay : Nat
  anchorOutputs : Bool
  feeratePerKw : Nat
  htlcs : List HtlcSighashView
deriving Repr, BEq
```

`outputs` is the commitment's BOLT 3 output list
(`st.toCommitment.commitmentOutputs`); `htlcs` is the signed HTLC set;
`obscuredCommitmentNumber` is the BOLT 3 XOR-obscured value carried in
`nSequence`/`nLockTime`; `feeSat` is the commitment fee; `holder` selects the
local/remote transaction.

### 1.2 Per-HTLC second-stage view

```lean
structure HtlcSighashView where
  htlcId : Nat
  parentCommitmentNumber : Nat
  direction : Direction
  htlcState : HTLCState
  amountSat : Nat
  paymentHash : PaymentHash
  cltvExpiry : Height
  secondStageFeeSat : Nat
deriving Repr, BEq
```

### 1.3 Serializer

The serializer is a deterministic, structural BOLT 3-shaped preimage.  It is
**not** a bit-exact Bitcoin transaction encoder (see §7).

```lean
def natBytes (n : Nat) : ByteArray
def bytesField (b : ByteArray) : ByteArray          -- length-prefixed
def commitmentOutputBytes : CommitmentOutput → ByteArray
def directionBytes : Direction → ByteArray
def htlcStateBytes : HTLCState → ByteArray
def boolBytes : Bool → ByteArray
def concatBytes : List ByteArray → ByteArray

def htlcPreimage (h : HtlcSighashView) : ByteArray
def commitmentPreimage (v : CommitmentSighashView) : ByteArray
```

Field order in `commitmentPreimage`: version/domain tag, commitment number,
obscured commitment number, funding txid, funding output index, funding value,
funding script, holder direction, `to_local`, `to_remote`, output count and
outputs, fee, contest delay, anchor flag, feerate, HTLC count and HTLC
preimages.

Field order in `htlcPreimage`: domain tag, parent commitment number, HTLC id,
direction, lifecycle tag, amount, payment hash, CLTV expiry, second-stage fee.

### 1.4 Digests

```lean
def commitmentDigest (M : PrimitiveModel) (v : CommitmentSighashView) : ByteArray :=
  M.sha256 (commitmentTag ++ commitmentPreimage v)

def htlcDigest (M : PrimitiveModel) (v : CommitmentSighashView)
    (h : HtlcSighashView) : ByteArray :=
  M.sha256 (commitmentTag ++ commitmentPreimage v ++ htlcPreimage h)

theorem commitmentDigest_size (M) (v) : (commitmentDigest M v).size = 32
theorem htlcDigest_size (M) (v) (h) : (htlcDigest M v h).size = 32
```

`commitmentTag` is the existing `LnLean.Crypto.commitmentTag`; a commitment
preimage therefore cannot be replayed in the funding or closing domain.

### 1.5 `SignedBy`

```lean
def SignedBy (M : PrimitiveModel) (pk : PubKey) (domain msg : ByteArray)
    (s : EcdsaSig) : Prop :=
  M.ecdsaVerify pk (domain ++ msg) s = true

def CommitmentSignedBy (M) (pk) (v : CommitmentSighashView) (s : EcdsaSig) : Prop :=
  SignedBy M pk commitmentTag (commitmentDigest M v) s

def HtlcSignedBy (M) (pk) (v) (h : HtlcSighashView) (s : EcdsaSig) : Prop :=
  SignedBy M pk commitmentTag (htlcDigest M v h) s

theorem signedBy_commitmentTag_iff (M) (pk) (msg) (s) :
    SignedBy M pk commitmentTag msg s ↔ verifyCommitment M pk msg s = true
```

The commitment and per-HTLC signatures are over their **digests**, matching
BOLT 3's "signature over the sighash" shape, and both use the commitment
domain tag.

### 1.6 Signing law

```lean
structure CommitmentSigningLaw (M : PrimitiveModel) where
  sign : PubKey → ByteArray → EcdsaSig
  verifies : ∀ (pk) (msg), M.ecdsaVerify pk msg (sign pk msg) = true
  wire : ∀ (pk) (msg), wireSigOK (sign pk msg).bytes = true

def CommitmentSigningLaw.ofFunding {M}
    (law : LnLean.Protocol.Handshake.FundingSigningLaw M) :
    CommitmentSigningLaw M
```

`ofFunding` is the PR-01 bridge: one honest signer serves the funding and
commitment domains, with the domain tags keeping the signatures separate.

### 1.7 Context and state view

```lean
structure SighashContext where
  fundingTxid : ByteArray
  fundingOutputIndex : Nat
  fundingScript : ByteArray
  obscuredCommitmentNumber : Nat
  secondStageFeeSat : Nat
  commitmentKey : PubKey

def htlcViewOfState (ctx) (st : SignedState) (h : SignedHtlc) : HtlcSighashView
def htlcViewsOfState (ctx) (st : SignedState) : List HtlcSighashView
def viewOfState (ctx) (st : SignedState) : CommitmentSighashView
def entryOfSighash (M) (law) (ctx) (st) (h : SignedHtlc) : SignedHtlcEntry
def honestFull (M) (law) (ctx) (st : SignedState) : CommitmentSignedFull
```

`viewOfState` deliberately does **not** read the state's explicit
`commitmentDigest` or `signedDataDigest` fields; those are exactly the fields
the serializer replaces.  `entryOfSighash` derives both the second-stage digest
and its signature.

### 1.8 `SighashProduces`

```lean
structure SighashProduces (M : PrimitiveModel) (law : CommitmentSigningLaw M)
    (ctx : SighashContext) (st : SignedState) (f : CommitmentSignedFull) : Prop where
  channelId_eq : f.channelId = st.channelId
  commitmentNumber_eq : f.commitmentNumber = st.commitmentNumber
  feePaid_eq : f.feePaid.val = st.feeSat
  commitmentDigest_eq : f.commitmentDigest = commitmentDigest M (viewOfState ctx st)
  commitmentSignature_eq : f.commitmentSignature =
    law.sign ctx.commitmentKey
      (commitmentTag ++ commitmentDigest M (viewOfState ctx st))
  htlcEntries_eq : f.htlcEntries = st.htlcs.map (entryOfSighash M law ctx st)
```

No digest, signature, or entry is free: every field is an equation to a
computed value.

---

## 2. Exact signatures of the main theorems

```lean
theorem honestFull_produces (M) (law) (ctx) (st) :
    SighashProduces M law ctx st (honestFull M law ctx st)

theorem SighashProduces.digest_unique {M law ctx st f g}
    (hf : SighashProduces M law ctx st f)
    (hg : SighashProduces M law ctx st g) :
    f.commitmentDigest = g.commitmentDigest ∧
      f.commitmentSignature = g.commitmentSignature

theorem SighashProduces.entries_unique {M law ctx st f g}
    (hf : SighashProduces M law ctx st f)
    (hg : SighashProduces M law ctx st g) :
    f.htlcEntries = g.htlcEntries

theorem SighashProduces.eq_honestFull {M law ctx st f}
    (h : SighashProduces M law ctx st f) :
    f = honestFull M law ctx st

theorem SighashProduces.signature_binds_digest {M}
    (hC3 : EufCma M.ecdsaVerify) {law ctx st f}
    (h : SighashProduces M law ctx st f) {msg : ByteArray}
    (hver : M.ecdsaVerify ctx.commitmentKey (commitmentTag ++ msg)
      f.commitmentSignature = true) :
    msg = commitmentDigest M (viewOfState ctx st)

theorem SighashProduces.htlc_signature_binds_digest {M}
    (hC3 : EufCma M.ecdsaVerify) {law ctx st f}
    (_h : SighashProduces M law ctx st f) {hh : SignedHtlc}
    (_hmem : hh ∈ st.htlcs) {msg : ByteArray}
    (hver : M.ecdsaVerify ctx.commitmentKey (commitmentTag ++ msg)
      (entryOfSighash M law ctx st hh).signature = true) :
    msg = htlcDigest M (viewOfState ctx st) (htlcViewOfState ctx st hh)

theorem SighashProduces.commitmentSignedBy {M law ctx st f}
    (h : SighashProduces M law ctx st f) :
    CommitmentSignedBy M ctx.commitmentKey (viewOfState ctx st)
      f.commitmentSignature

theorem SighashProduces.entrySignedBy {M law ctx st f}
    (_h : SighashProduces M law ctx st f) (hh : SignedHtlc)
    (_hmem : hh ∈ st.htlcs) :
    HtlcSignedBy M ctx.commitmentKey (viewOfState ctx st)
      (htlcViewOfState ctx st hh)
      (entryOfSighash M law ctx st hh).signature

theorem SighashProduces.entries_digest {M law ctx st f}
    (h : SighashProduces M law ctx st f) :
    f.htlcEntries.map (fun e => e.signedDataDigest) =
      st.htlcs.map (fun hh =>
        htlcDigest M (viewOfState ctx st) (htlcViewOfState ctx st hh))

theorem SighashProduces.entry_count {M law ctx st f}
    (h : SighashProduces M law ctx st f) :
    f.htlcEntries.length = st.htlcs.length

theorem SighashProduces.entries_map_output {M law ctx st f}
    (h : SighashProduces M law ctx st f) :
    f.htlcEntries.map SignedHtlcEntry.toCommitmentHtlcOutput =
      st.toCommitment.htlcs

theorem SighashProduces.coverage {M law ctx st f}
    (h : SighashProduces M law ctx st f)
    (hcons : CommitmentConserved st.toCommitment)
    (hres : FeeIsFundingResidual st.feerate st.toCommitment) :
    f.htlcEntries.map SignedHtlcEntry.toCommitmentHtlcOutput =
        st.toCommitment.htlcs ∧
      f.toCommitmentSigned.htlcSignatures.length =
        st.toCommitment.htlcs.length ∧
      CoversHtlcOutputs f.toCommitmentSigned st.toCommitment ∧
      f.feePaid.val = (commitmentFee st.feerate st.toCommitment).val ∧
      f.commitmentNumber = st.toCommitment.commitmentNumber ∧
      f.commitmentDigest = commitmentDigest M (viewOfState ctx st) ∧
      CommitmentSignedBy M ctx.commitmentKey (viewOfState ctx st)
        f.commitmentSignature

theorem producedFrom_of_sighashProduces {M law ctx st f}
    (h : SighashProduces M law ctx st f)
    (hdig : st.commitmentDigest = commitmentDigest M (viewOfState ctx st))
    (hhtlc : ∀ hh ∈ st.htlcs,
      hh.signedDataDigest =
        htlcDigest M (viewOfState ctx st) (htlcViewOfState ctx st hh)) :
    ProducedFrom f st
      (fun hh => law.sign ctx.commitmentKey
        (commitmentTag ++
          htlcDigest M (viewOfState ctx st) (htlcViewOfState ctx st hh)))

theorem commitment_signed_full_covers_of_sighash
    (M) (law) (ctx) (f) (st) (sigAt : SignedHtlc → EcdsaSig)
    (hsh : SighashProduces M law ctx st f)
    (hprod : ProducedFrom f st sigAt)
    (hcons : CommitmentConserved st.toCommitment)
    (hres : FeeIsFundingResidual st.feerate st.toCommitment) :
    (f.htlcEntries.map SignedHtlcEntry.toCommitmentHtlcOutput =
        st.toCommitment.htlcs ∧
      f.toCommitmentSigned.htlcSignatures.length =
        st.toCommitment.htlcs.length ∧
      CoversHtlcOutputs f.toCommitmentSigned st.toCommitment ∧
      f.feePaid.val = (commitmentFee st.feerate st.toCommitment).val ∧
      f.commitmentNumber = st.toCommitment.commitmentNumber ∧
      waveE_e20_commitment_signed_covers
        f.toCommitmentSigned st.feerate st.toCommitment) ∧
      f.commitmentDigest = commitmentDigest M (viewOfState ctx st) ∧
      CommitmentSignedBy M ctx.commitmentKey (viewOfState ctx st)
        f.commitmentSignature

theorem honest_commitment_signed_full_covers
    (M) (law) (ctx) (st)
    (hcons : CommitmentConserved st.toCommitment)
    (hres : FeeIsFundingResidual st.feerate st.toCommitment) :
    (honestFull M law ctx st).htlcEntries.map
        SignedHtlcEntry.toCommitmentHtlcOutput = st.toCommitment.htlcs ∧
      (honestFull M law ctx st).feePaid.val =
        (commitmentFee st.feerate st.toCommitment).val ∧
      (honestFull M law ctx st).commitmentDigest =
        commitmentDigest M (viewOfState ctx st) ∧
      CommitmentSignedBy M ctx.commitmentKey (viewOfState ctx st)
        (honestFull M law ctx st).commitmentSignature
```

Negative/attribution results:

```lean
theorem producedFrom_not_sighashProduces (M) (law) (ctx)
    (commitSig : EcdsaSig) (sigAt : SignedHtlc → EcdsaSig) :
    ¬ SighashProduces M law ctx exampleSignedState
        (commitmentSignedFullOfState exampleSignedState commitSig sigAt)

theorem producedFrom_without_serialized_digest :
    ∃ (f : CommitmentSignedFull) (st : SignedState)
      (sigAt : SignedHtlc → EcdsaSig),
      ProducedFrom f st sigAt ∧ f.commitmentDigest = ByteArray.empty

theorem funding_and_commitment_signing_contract
    (M) (law : LnLean.Protocol.Handshake.FundingSigningLaw M)
    (hkb : KeyBinding M.ecdsaVerify)
    (channelId) (fundingKey) (fundingTx) (ctx) (st) :
    (let m := honestFundingSigned law channelId fundingKey fundingTx
     wireSigOK m.signature.bytes = true ∧
       fundingSignedValid M fundingKey fundingTx m ∧
       (∀ fundingKey', fundingSignedValid M fundingKey' fundingTx m →
         fundingKey' = fundingKey) ∧
       (∀ fundingTx', fundingSignedValid M fundingKey fundingTx' m →
         fundingTx' = fundingTx)) ∧
      SighashProduces M (CommitmentSigningLaw.ofFunding law) ctx st
        (honestFull M (CommitmentSigningLaw.ofFunding law) ctx st) ∧
      CommitmentSignedBy M ctx.commitmentKey (viewOfState ctx st)
        (honestFull M (CommitmentSigningLaw.ofFunding law) ctx st).commitmentSignature

theorem signedBy_attribution_not_from_eufCma (M₀) (msg) :
    ∃ (M) (sig) (k₁ k₂ : PubKey),
      k₁ ≠ k₂ ∧ EufCma M.ecdsaVerify ∧
        SignedBy M k₁ commitmentTag msg sig ∧
        SignedBy M k₂ commitmentTag msg sig
```

Preserved legacy negatives:

```lean
theorem legacy_wire_cannot_determine_coverage :
    ¬ ∃ g : CommitmentSigned → Commitment,
        ∀ (m : CommitmentSigned) (r : FeeRate),
          waveE_e20_commitment_signed_covers m r (g m)

theorem legacy_wire_cannot_select_htlc_set :
    ¬ ∃ g : CommitmentSigned → List CommitmentHTLCOutput,
        ∀ (m : CommitmentSigned) (c : Commitment),
          waveE_e20_covers_htlcs m c → c.htlcs = g m
```

Bundled `sighash_summary` contains the honest constructor, uniqueness,
C3 digest binding, the `ProducedFrom` bridge, both legacy negatives, and the
`ProducedFrom`-without-serializer witness.

---

## 3. Proof strategy

1. **Keep the wire record untouched.** `CommitmentSigned` remains the BOLT 2
   type-132 record; `CommitmentSignedFull` remains the wave-4 signer-side
   record. No field was added, so every existing record literal and decoder
   theorem is unaffected.
2. **Do not read the supplied digest fields.** `viewOfState` projects only the
   semantic state (number, balances, fee, holder, HTLC descriptors, output
   list) and the external context (outpoint, scripts, obscured number,
   second-stage fee, key). The state's `commitmentDigest` and
   `signedDataDigest` are deliberately excluded, so the derived record cannot
   simply copy the old data.
3. **Define production by equations.** `SighashProduces` has one equation per
   derived field. `honestFull` is the corresponding pure function, and
   `honestFull_produces` is definitional.
4. **Derivation/uniqueness.** `digest_unique`, `entries_unique`, and
   `eq_honestFull` are consequences of the equations; no cryptographic
   assumption is used.
5. **C3 binding.** `signature_binds_digest` applies the model's
   `EufCma M.ecdsaVerify` field to the *tagged* messages and cancels the
   common `commitmentTag` prefix. `htlc_signature_binds_digest` does the same
   for a per-HTLC entry.
6. **Coverage.** `SighashProduces.coverage` proves the wave-4 coverage
   conclusions directly from the derived entry equations, the two BOLT 3
   value equations, and `Commitment.htlcOutputCount_commitmentOutputs`.
   `commitment_signed_full_covers_of_sighash` additionally takes the wave-4
   `ProducedFrom` relation and reuses `commitment_signed_full_covers`, showing
   the two contracts compose rather than replacing one another.
7. **Load-bearing negative.** The wave-4 concrete state stores
   `commitmentDigest = ByteArray.empty`. Its `commitmentSignedFullOfState`
   record satisfies `ProducedFrom`, but `commitmentDigest` is shown to be
   32 bytes by `sha256_size`, so no `SighashProduces` relation can hold for it.
8. **Funding/key binding.** `CommitmentSigningLaw.ofFunding` reuses the
   wave-3 `FundingSigningLaw`; `funding_and_commitment_signing_contract` is
   the wave-3 contract (`funding_signed_signing_contract`) conjoined with the
   serializer production and signature-validity results. The negative
   `signedBy_attribution_not_from_eufCma` reuses the single-message EUF-CMA
   model to show that C3 does not make key attribution automatic.
9. **Domain separation.** `funding_signature_not_commitment_signature` uses
   the existing `Crypto.verifyFunding_not_verifyCommitment` tag-separation
   theorem, so an honest funding signature is not a commitment signature over
   the same untagged message.

---

## 4. Build and axiom results

Commands, under the shared lock, single Lean thread:

```sh
export PATH=/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
cd /home/ubuntu/ln-lean-repair

LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Protocol.Messages LnLean.Proofs.Channel.SighashTargets
# ✔ [33/33] Built LnLean.Proofs.Channel.SighashTargets
# Build completed successfully (33 jobs).
# RC 0, 0 warnings.
```

`#print axioms` (scratch file `/tmp/opencode/s5_sighash_audit.lean`, run with
`lake env lean`):

| Declaration | Axioms |
|---|---|
| `commitmentDigest_size` | none |
| `htlcDigest_size` | none |
| `honestFull_produces` | `propext`, `Classical.choice`, `Quot.sound` |
| `SighashProduces.digest_unique` | `propext`, `Classical.choice`, `Quot.sound` |
| `SighashProduces.entries_unique` | `propext`, `Classical.choice`, `Quot.sound` |
| `SighashProduces.eq_honestFull` | `propext`, `Classical.choice`, `Quot.sound` |
| `SighashProduces.signature_binds_digest` | `propext`, `Classical.choice`, `Quot.sound` |
| `SighashProduces.htlc_signature_binds_digest` | `propext`, `Classical.choice`, `Quot.sound` |
| `SighashProduces.commitmentSignedBy` | `propext`, `Classical.choice`, `Quot.sound` |
| `SighashProduces.coverage` | `propext`, `Classical.choice`, `Quot.sound` |
| `producedFrom_of_sighashProduces` | `propext`, `Classical.choice`, `Quot.sound` |
| `commitment_signed_full_covers_of_sighash` | `propext`, `Classical.choice`, `Quot.sound` |
| `honest_commitment_signed_full_covers` | `propext`, `Classical.choice`, `Quot.sound` |
| `producedFrom_not_sighashProduces` | `propext`, `Classical.choice`, `Quot.sound` |
| `legacy_wire_cannot_determine_coverage` | `propext`, `Quot.sound` |
| `legacy_wire_cannot_select_htlc_set` | `propext` |
| `producedFrom_without_serialized_digest` | none |
| `funding_and_commitment_signing_contract` | `propext`, `Classical.choice`, `Quot.sound` |
| `signedBy_attribution_not_from_eufCma` | `propext`, `Quot.sound` |
| `sighash_summary` | `propext`, `Classical.choice`, `Quot.sound` |

The complete audit of 27 declarations contains only the three permitted
axioms (`propext`, `Quot.sound`, `Classical.choice`).  Three declarations
depend on no axioms at all.

Forbidden-construct scan over both owned Lean files:

```sh
grep -nE '\b(sorry|axiom|admit|native_decide|unsafe)\b|implemented_by' \
  LnLean/Protocol/Messages.lean LnLean/Proofs/Channel/SighashTargets.lean
# no matches
```

No full `lake build`, no `collect-obligations.py`, no Git write command, and
no edit to `LnLean/Channel/Commitment.lean`, `LnLean.lean`,
`Obligations.lean`, `Traceability.lean`, `AxiomAudit.lean`, docs, scripts, or
another lane's files was performed.

---

## 5. Compatibility and concurrent-lane dependency

* `LnLean/Channel/Commitment.lean` was already modified by the concurrent
  `S5-CH-GROSSNET` lane in this worktree (additive gross/net fields).  The
  build above was run against that *current* file; the lane did not edit it.
  `SighashTargets` consumes only `Commitment`, `CommitmentOutput`,
  `commitmentOutputs`, `commitmentFee`, `Commitment.htlcOutputCount_...`,
  and `SignedState.toCommitment`, so additive defaulted fields do not break
  this module.
* `LnLean/Proofs/ProtocolWireTargets.lean` is imported unchanged;
  `SignedState`, `SignedHtlc`, `ProducedFrom`,
  `commitmentSignedFullOfState`, `exampleSignedState`, and
  `commitment_signed_full_covers` are reused, not duplicated or weakened.
* `LnLean/Proofs/ProtocolSigningTargets.lean` is imported for
  `FundingSigningLaw`, `honestFundingSigned`,
  `funding_signed_signing_contract`, and `singleMessageEcdsaModel`.  The
  wave-3 contract is restated inside the new bundle, not altered.
* No `Msg` constructor, `msgLength` branch, `wellFormed` clause, or record
  literal in `Messages.lean` was touched.

---

## 6. Integration steps (parent / catalog owner)

1. **Root import.** Add
   `import LnLean.Proofs.Channel.SighashTargets` to `LnLean.lean` (this lane
   may not edit it).  The module already builds as an explicit target.
2. **Axiom audit.** Add the declarations in §4 to
   `LnLean/Proofs/AxiomAudit.lean`; expected result is the three permitted
   axioms only.
3. **Catalog.** Recommended target for `PR-02`:
   * primary: `LnLean.Proofs.Channel.SighashTargets.commitment_signed_full_covers_of_sighash`
     or the direct `SighashProduces.coverage`;
   * bundled: `LnLean.Proofs.Channel.SighashTargets.sighash_summary`;
   * claim text must keep: "conditional on a structural BOLT 3 serializer,
     an explicit signing law, and the two BOLT 3 value equations; C3 binds
     signatures to digests, not to views (SHA-256 collision gap); the legacy
     wire record still has no decoder."
4. **Catalog.** Recommended target for `PR-01`: keep
   `LnLean.Protocol.Handshake.funding_signed_signing_contract` as the primary
   row or add
   `LnLean.Proofs.Channel.SighashTargets.funding_and_commitment_signing_contract`
   as the joint funding/commitment bundle.  The `KeyBinding` hypothesis and
   the missing `fundingPubKey`/`fundingTx` fields must stay in the claim.
5. **Roadmap.** Update `PR-02` from "no BOLT 3 sighash serializer or C3
   verification" to "structural serializer and C3 digest binding proved; view
   binding still requires a collision-resistance statement on the serializer
   output, and bit-exact transaction encoding remains out of scope".  Update
   `PR-01` to note that one signing law now serves both domains, while key
   attribution remains conditional on `KeyBinding`.
6. Do **not** delete `ProtocolWireTargets.lean` or
   `ProtocolSigningTargets.lean`; both remain part of the evidence chain and
   are imported here.

---

## 7. Scope caveats and residual gaps

1. **Structural, not bit-exact, serializer.** `commitmentPreimage` uses the
   BOLT 3 field order and simple fixed-width/length-prefixed encodings.  It
   does not reproduce Bitcoin's exact `nVersion`, `nLockTime`, `nSequence`,
   varint, or script encoding, and it does not derive scripts from funding
   keys.  It is a faithful *model* of what the signature commits to, not a
   consensus encoder.
2. **Digest binding vs. view binding.** C3 and `EufCma` are message binding:
   they prove a signature cannot verify for two different **digests**.  The
   model's `sha256_collisionResistant` field is injectivity only on 32-byte
   preimages, not on arbitrary serialized preimages, so this module does not
   prove that equal digests imply equal views.  That is the exact remaining
   cryptographic gap; the theorems are stated at digest level to avoid
   assuming it.
3. **No secret-key model.** `CommitmentSigningLaw.sign` is keyed by `PubKey`,
   the same idealization as `FundingSigningLaw` and
   `WaveE.E06.SigningCompleteness`.  It is an interface stand-in, not a claim
   that a public key can sign.
4. **Commitment context is external.** The funding outpoint, funding script,
   obscured commitment number, second-stage fee, and signing key are supplied
   by `SighashContext`.  The channel state does not carry them; deriving them
   from the BOLT 2 handshake is `L1-03`/`PR-01` work, not this lane.
5. **State coherence is explicit.** `producedFrom_of_sighashProduces` needs
   `st.commitmentDigest` and each `st.signedDataDigest` to equal the derived
   values.  This is not automatic (`producedFrom_without_serialized_digest`
   exhibits a `ProducedFrom` record with an empty digest), but it is exactly
   the contract a state built by the honest constructor satisfies.
6. **Fee units.** The module inherits the tree's existing convention that
   `Commitment.feeSat` is used in the `commitmentFee`/`FeeIsFundingResidual`
   equations; it does not change or reinterpret that convention.
7. **Funding payload fields.** `FundingSigned` still has no
   `fundingPubKey`/`fundingTx` field, so the funding half is a predicate
   (`FundingSignedProducedBy`) plus `KeyBinding`, not a wire-record theorem.
   `signedBy_attribution_not_from_eufCma` proves C3 alone cannot supply that
   attribution.
8. **Trimmed HTLCs.** `SignedState.htlcs` is the signed (untrimmed) set, as in
   wave 4; dust trimming and second-stage fee integration remain the
   `CH-01`/`CH-02`/`CH-03` lane's scope.  `secondStageFeeSat` is an explicit
   context parameter.
9. **No computational reduction.** As with the rest of the tree, C1/C3 are
   algebraic interface laws; this module makes no advantage-bound or EUF-CMA
   reduction claim (`CR-01`/`SEC-01` remain separate).

---

## 8. Blockers / residual gaps table

| Missing item | Consequence | Status here |
|---|---|---|
| Bit-exact BOLT 3 / Bitcoin transaction encoder | The serializer is a structural model, not a consensus encoder | Documented §7.1; separate L1/model lane |
| SHA-256 collision resistance on arbitrary preimages | Signature binds the digest, not necessarily the view | Stated as exact gap §7.2; no fake proof |
| Secret-key / ownership model | Signing law is keyed by `PubKey` | Inherited idealization §7.3 |
| `fundingPubKey` / `fundingTx` on `FundingSigned` | Key/tx attribution remains a predicate | `KeyBinding` + `FundingSignedProducedBy`; `PR-01` remains conditional |
| Funding outpoint/scripts in channel state | `SighashContext` is external | `L1-03` handshake-construction lane |
| Bit-exact HTLC second-stage transaction | `htlcPreimage` is structural | Documented §7.8 |
| Root import / catalog / axiom audit | Parent-owned | §6 integration steps |

No blocker prevents the conditional theorems; the blockers are exactly the
model fields and cryptographic assumptions that the faithful claim keeps
explicit.
