# S4-PR-WIRE — full `commitment_signed` model and conditional coverage (PR-02)

**Lane:** `S4-PR-WIRE`
**Issue:** `PR-02` (P1, open)
**Worktree:** `/home/ubuntu/ln-lean-repair`
**Branch / base:** `repair/integrated` @ `47189fe`
**Toolchain:** `leanprover/lean4:v4.35.0`

**Owned files changed**

| File | Change |
|---|---|
| `LnLean/Protocol/Messages.lean` | **Additive only** (+180 lines): one additive import, `SignedHtlcEntry`, `CommitmentSignedFull`, its projection and structural lemmas. No existing declaration was renamed, removed, or changed. |
| `LnLean/Proofs/ProtocolWireTargets.lean` | **New** (652 lines): `SignedHtlc`, `SignedState`, `ProducedFrom`, conditional coverage, honest construction, well-formedness, concrete non-vacuity instance, preserved negative results, projection-loss results. |
| `agents/reports/swarm4/S4-PR-WIRE.md` | This report. |

**Verdict.** PR-02 is narrowed at the model level. The full record now carries
the commitment number, paid fee, commitment digest, and per-HTLC signed entries
(id, millisatoshi amount, payment hash, direction, lifecycle tag, expiry,
signed-data digest, signature). An explicit `SignedState` and an explicit
production relation `ProducedFrom` connect the record to the commitment state.
Under `ProducedFrom` plus the two BOLT 3 value equations, the entries are
proved to cover exactly the state's HTLC set and the fee is proved equal to the
floored BOLT 3 formula fee. The legacy wire record is unchanged,
`CommitmentSignedFull.toCommitmentSigned` is its forgetful projection, and the
existing negative results (no wire-only coverage decoder, no HTLC-set selector)
are preserved and re-exported.

---

## 1. Model additions in `LnLean/Protocol/Messages.lean`

All declarations are in `namespace LnLean.Protocol`. The only new import is
`LnLean.Channel.Types` (for `HTLCState` and `CommitmentHTLCOutput`); it creates
no cycle (`Channel.Types` imports only `Basic.Core` and `Bitcoin.Seam`).

```lean
structure SignedHtlcEntry where
  htlcId : Nat
  amount : Msat
  paymentHash : PaymentHash
  direction : Direction
  htlcState : HTLCState
  cltvExpiry : Nat
  signedDataDigest : ByteArray
  signature : EcdsaSig
deriving Repr, BEq

structure CommitmentSignedFull where
  channelId : ChannelId
  commitmentNumber : Nat
  feePaid : Msat
  commitmentDigest : ByteArray
  commitmentSignature : EcdsaSig
  htlcEntries : List SignedHtlcEntry
deriving Repr, BEq
```

Projection / forgetful map:

```lean
def SignedHtlcEntry.toCommitmentHtlcOutput (e : SignedHtlcEntry) :
    CommitmentHTLCOutput
-- amountSat := e.amount.toSatFloor, preserving direction/state/expiry

def SignedHtlcEntry.ident (e : SignedHtlcEntry) :
    Nat × Msat × PaymentHash × Direction × Nat

def CommitmentSignedFull.toCommitmentSigned (f : CommitmentSignedFull) :
    CommitmentSigned
-- channelId := f.channelId
-- signature := f.commitmentSignature
-- htlcSignatures := f.htlcEntries.map (fun e => e.signature)
```

Structural/forgetful theorems:

```lean
@[simp] theorem CommitmentSignedFull.toCommitmentSigned_channelId ...
@[simp] theorem CommitmentSignedFull.toCommitmentSigned_signature ...
@[simp] theorem CommitmentSignedFull.toCommitmentSigned_htlcSignatures ...
theorem CommitmentSignedFull.signatures_toCommitmentSigned (f) :
    signatures (.commitmentSigned f.toCommitmentSigned) =
      f.commitmentSignature :: f.htlcEntries.map (fun e => e.signature)
theorem CommitmentSignedFull.msgLength_toCommitmentSigned (f) :
    msgLength (.commitmentSigned f.toCommitmentSigned) =
      34 + sigLen f.commitmentSignature +
        sigListLen (f.htlcEntries.map (fun e => e.signature))
def CommitmentSignedFull.ofWire (m : CommitmentSigned) : CommitmentSignedFull
theorem CommitmentSignedFull.toCommitmentSigned_ofWire (m) :
    (ofWire m).toCommitmentSigned = m
theorem CommitmentSignedFull.toCommitmentSigned_surjective (m) :
    ∃ f : CommitmentSignedFull, f.toCommitmentSigned = m
```

`ofWire` is an embedding with empty metadata, not an honest-signer claim. Its
purpose is conservativity: the extension does not exclude any legacy record.

---

## 2. Exact signatures in `LnLean/Proofs/ProtocolWireTargets.lean`

All declarations are in `namespace LnLean.Proofs.ProtocolWireTargets`.

### 2.1 State-side HTLC and state

```lean
structure SignedHtlc where
  htlcId : Nat
  amount : Msat
  paymentHash : PaymentHash
  direction : Direction
  htlcState : HTLCState
  cltvExpiry : Height
  signedDataDigest : ByteArray
deriving Repr, BEq

def SignedHtlc.toEntry (h : SignedHtlc) (signature : EcdsaSig) :
    SignedHtlcEntry
def SignedHtlc.toCommitmentHtlcOutput (h : SignedHtlc) :
    CommitmentHTLCOutput
def SignedHtlc.ident (h : SignedHtlc) :
    Nat × Msat × PaymentHash × Direction × Nat

structure SignedState where
  channelId : ChannelId
  holder : Direction
  commitmentNumber : Nat
  fundingValueSat : Nat
  toLocalSat : Nat
  toRemoteSat : Nat
  feeSat : Nat
  contestDelay : Nat
  anchorOutputs : Bool
  feerate : FeeRate
  commitmentDigest : ByteArray
  htlcs : List SignedHtlc
deriving Repr, BEq

def SignedState.toCommitment (st : SignedState) : Commitment
-- htlcs := st.htlcs.map SignedHtlc.toCommitmentHtlcOutput, all other fields copied
```

`SignedState.toCommitment` is a definition, not a hypothesis: the commitment's
HTLC list is *by construction* the descriptor projection, so "covers the
current HTLC set" is stated on the same list the commitment emits.

### 2.2 Production relation

```lean
structure ProducedFrom (f : CommitmentSignedFull) (st : SignedState)
    (sigAt : SignedHtlc → EcdsaSig) : Prop where
  channelId_eq : f.channelId = st.channelId
  commitmentNumber_eq : f.commitmentNumber = st.commitmentNumber
  feePaid_eq : f.feePaid.val = st.feeSat
  commitmentDigest_eq : f.commitmentDigest = st.commitmentDigest
  htlcEntries_eq : f.htlcEntries =
    st.htlcs.map (fun h => h.toEntry (sigAt h))
```

Consequences (all derived, none assumed):

```lean
theorem ProducedFrom.entries_map_output (h : ProducedFrom f st sigAt) :
    f.htlcEntries.map SignedHtlcEntry.toCommitmentHtlcOutput =
      st.toCommitment.htlcs

theorem ProducedFrom.entries_signatures (h : ProducedFrom f st sigAt) :
    f.toCommitmentSigned.htlcSignatures = st.htlcs.map sigAt

theorem ProducedFrom.entries_digests (h : ProducedFrom f st sigAt) :
    f.htlcEntries.map (fun e => e.signedDataDigest) =
      st.htlcs.map (fun h => h.signedDataDigest)

theorem ProducedFrom.entry_count (h : ProducedFrom f st sigAt) :
    f.htlcEntries.length = st.htlcs.length

theorem ProducedFrom.entry_metadata (h : ProducedFrom f st sigAt) :
    f.htlcEntries.map SignedHtlcEntry.ident =
      st.htlcs.map SignedHtlc.ident
```

### 2.3 Conditional coverage theorem

```lean
theorem commitment_signed_full_covers
    (f : CommitmentSignedFull) (st : SignedState)
    (sigAt : SignedHtlc → EcdsaSig)
    (hprod : ProducedFrom f st sigAt)
    (hcons : CommitmentConserved st.toCommitment)
    (hres : FeeIsFundingResidual st.feerate st.toCommitment) :
    f.htlcEntries.map SignedHtlcEntry.toCommitmentHtlcOutput =
        st.toCommitment.htlcs ∧
      f.toCommitmentSigned.htlcSignatures.length =
        st.toCommitment.htlcs.length ∧
      CoversHtlcOutputs f.toCommitmentSigned st.toCommitment ∧
      f.feePaid.val =
        (commitmentFee st.feerate st.toCommitment).val ∧
      f.commitmentNumber = st.toCommitment.commitmentNumber ∧
      f.commitmentDigest = st.commitmentDigest ∧
      waveE_e20_commitment_signed_covers
        f.toCommitmentSigned st.feerate st.toCommitment ∧
      f.htlcEntries.map SignedHtlcEntry.ident =
        st.htlcs.map SignedHtlc.ident
```

`CommitmentConserved` is the existing
`LnLean.Proofs.CommitmentConserved` (`totalOutputValue + feeSat = funding`).
`FeeIsFundingResidual` is the existing
`LnLean.Proofs.ProtocolCoverageTargets.FeeIsFundingResidual`
(`totalOutputValue + formulaFee = funding`). The fee equality is `omega` from
those two equations and `feePaid_eq`; the coverage conjunctions are derived
from `htlcEntries_eq`. Neither `waveE_e20_covers_htlcs` nor
`waveE_e20_covers_fee` is a hypothesis.

Catalog-shaped corollary:

```lean
theorem commitment_signed_full_covers_exact
    (f) (st) (sigAt) (hprod) (hcons) (hres) :
    f.toCommitmentSigned.htlcSignatures.length =
        st.toCommitment.htlcs.length ∧
      (signatures (.commitmentSigned f.toCommitmentSigned)).length =
        st.toCommitment.htlcs.length + 1 ∧
      f.feePaid.val =
        (commitmentFee st.feerate st.toCommitment).val ∧
      waveE_e20_commitment_signed_covers
        f.toCommitmentSigned st.feerate st.toCommitment
```

### 2.4 Honest construction and well-formedness

```lean
def commitmentSignedFullOfState (st : SignedState) (commitSig : EcdsaSig)
    (sigAt : SignedHtlc → EcdsaSig) : CommitmentSignedFull

theorem producedFrom_commitmentSignedFullOfState (st) (commitSig) (sigAt) :
    ProducedFrom (commitmentSignedFullOfState st commitSig sigAt) st sigAt

theorem wellFormed_toCommitmentSigned (f : CommitmentSignedFull)
    (hcid : f.channelId.Valid)
    (hcommit : f.commitmentSignature.bytes.size ≤ 73)
    (hentries : ∀ e ∈ f.htlcEntries, e.signature.bytes.size ≤ 73)
    (hlen : 34 + f.commitmentSignature.bytes.size +
        sigListLen (f.htlcEntries.map (fun e => e.signature)) ≤ 65535) :
    wellFormed (.commitmentSigned f.toCommitmentSigned)
```

The construction's fee and commitment number are copied from the state, so
`producedFrom_commitmentSignedFullOfState` is definitional. The legacy
projection is structurally `wellFormed` under the same BOLT 1 bounds the old
record already needed.

Concrete non-vacuity instance (`amount = 1000 msat → 1 sat`, weight
`724 + 172 = 896`, fee `1000 * 896 / 1000 = 896`, funding
`10000 + 10000 + 1 + 896 = 20897`):

```lean
def exampleSignedState : SignedState
theorem exampleSignedState_conserved :
    CommitmentConserved exampleSignedState.toCommitment
theorem exampleSignedState_residual :
    FeeIsFundingResidual exampleSignedState.feerate exampleSignedState.toCommitment
theorem example_commitment_signed_full_covers (commitSig) (sigAt) :
    (commitmentSignedFullOfState exampleSignedState commitSig sigAt).htlcEntries.map
        SignedHtlcEntry.toCommitmentHtlcOutput =
        exampleSignedState.toCommitment.htlcs ∧
      (commitmentSignedFullOfState exampleSignedState commitSig sigAt).feePaid.val =
        (commitmentFee exampleSignedState.feerate
          exampleSignedState.toCommitment).val
```

### 2.5 Preserved negative results and projection limits

```lean
theorem legacy_wire_cannot_determine_coverage :
    ¬ ∃ g : CommitmentSigned → Commitment,
        ∀ (m : CommitmentSigned) (r : FeeRate),
          waveE_e20_commitment_signed_covers m r (g m)
-- exactly ProtocolCoverageTargets.no_wire_determined_coverage

theorem legacy_wire_cannot_select_htlc_set :
    ¬ ∃ g : CommitmentSigned → List CommitmentHTLCOutput,
        ∀ (m : CommitmentSigned) (c : Commitment),
          waveE_e20_covers_htlcs m c → c.htlcs = g m
-- exactly ProtocolCoverageTargets.no_coverage_htlc_selector

theorem projection_forgets_fee_and_number :
    ∃ f g : CommitmentSignedFull,
      f.toCommitmentSigned = g.toCommitmentSigned ∧
        f.feePaid ≠ g.feePaid ∧ f.commitmentNumber ≠ g.commitmentNumber

theorem projection_forgets_entry_metadata :
    ∃ f g : CommitmentSignedFull,
      f.toCommitmentSigned = g.toCommitmentSigned ∧
        f.htlcEntries ≠ g.htlcEntries

theorem count_coverage_not_exact_coverage :
    mismatchedFull.toCommitmentSigned.htlcSignatures.length =
        exampleSignedState.toCommitment.htlcs.length ∧
      mismatchedFull.htlcEntries.map SignedHtlcEntry.toCommitmentHtlcOutput ≠
        exampleSignedState.toCommitment.htlcs

theorem wellFormed_full_can_fail_coverage :
    ∃ f : CommitmentSignedFull,
      f.toCommitmentSigned = waveE_e20_emptyCommitmentSigned ∧
        wellFormed (.commitmentSigned f.toCommitmentSigned) ∧
        ¬ waveE_e20_commitment_signed_covers f.toCommitmentSigned ⟨0⟩
            (waveE_e20_commitmentWith 1 0)
```

### 2.6 Summary theorem

```lean
theorem protocol_wire_summary :
    (∀ (f : CommitmentSignedFull) (st : SignedState)
        (sigAt : SignedHtlc → EcdsaSig),
        ProducedFrom f st sigAt →
        CommitmentConserved st.toCommitment →
        FeeIsFundingResidual st.feerate st.toCommitment →
        f.htlcEntries.map SignedHtlcEntry.toCommitmentHtlcOutput =
            st.toCommitment.htlcs ∧
          f.toCommitmentSigned.htlcSignatures.length =
            st.toCommitment.htlcs.length ∧
          f.feePaid.val =
            (commitmentFee st.feerate st.toCommitment).val ∧
          waveE_e20_commitment_signed_covers
            f.toCommitmentSigned st.feerate st.toCommitment) ∧
      (∀ (st : SignedState) (commitSig : EcdsaSig)
          (sigAt : SignedHtlc → EcdsaSig),
        ProducedFrom (commitmentSignedFullOfState st commitSig sigAt) st sigAt) ∧
      (¬ ∃ g : CommitmentSigned → Commitment,
          ∀ (m : CommitmentSigned) (r : FeeRate),
            waveE_e20_commitment_signed_covers m r (g m)) ∧
      (¬ ∃ g : CommitmentSigned → List CommitmentHTLCOutput,
          ∀ (m : CommitmentSigned) (c : Commitment),
            waveE_e20_covers_htlcs m c → c.htlcs = g m) ∧
      (∃ f g : CommitmentSignedFull,
          f.toCommitmentSigned = g.toCommitmentSigned ∧
            f.feePaid ≠ g.feePaid)
```

---

## 3. Proof strategy

1. **Do not change the wire struct.** `CommitmentSigned` remains exactly the
   BOLT 2 type 132 record. The full record is a separate signer-side type with
   a total forgetful projection, so every existing record literal, `Msg`
   constructor, `msgLength` branch, and `wellFormed` proof is untouched.
2. **Make the state a definition, not a hypothesis.** In `SignedState`,
   `toCommitment` computes the commitment's HTLC list from the descriptor
   list. Therefore the "current HTLC set" in the conclusion is literally the
   set the commitment carries; no separate coherence hypothesis is hidden in
   the coverage theorem.
3. **Make the production relation explicit and field-by-field.** `ProducedFrom`
   states channel id, commitment number, fee, digest, and the per-HTLC
   signature assignment. This is the analogue of S3's `HtlcSignaturesMatch`
   but with the missing wire fields restored; the coverage conclusion is not a
   field of the relation.
4. **Split the two halves.** *Entries*: `htlcEntries_eq` plus
   `List.map_map` gives the descriptor/identification equalities. *Fee*:
   `CommitmentConserved` and `FeeIsFundingResidual` are the two BOLT 3 value
   equations; `omega` forces `feeSat`, and `feePaid_eq` transfers it to the
   record. `CoversHtlcOutputs` follows by
   `Commitment.htlcOutputCount_commitmentOutputs`.
5. **Keep the negative results alive.** The no-decoder and no-selector
   theorems are imported from `ProtocolCoverageTargets` and restated under this
   module's names, not weakened or duplicated. New projection-loss theorems
   show the added fields are necessary data.
6. **Show the theorem is inhabited.** `exampleSignedState` satisfies both value
   equations by `decide` (no axioms), and the honest constructor covers it.

---

## 4. Build and axiom results

Commands run under the shared build lock, single Lean thread:

```sh
export PATH=/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
cd /home/ubuntu/ln-lean-repair

LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Protocol.Messages
# Build completed successfully (10 jobs), RC 0.

LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Proofs.ProtocolWireTargets
# ✔ [20/20] Built LnLean.Proofs.ProtocolWireTargets
# Build completed successfully (20 jobs), RC 0.
```

Direct downstream modules (all 15 files that import
`LnLean.Protocol.Messages`, plus the catalog wrapper) were rebuilt:

```sh
lake build LnLean.Proofs.ProtocolCoverageTargets LnLean.Proofs.ProtocolTargets \
  LnLean.Protocol.Handshake
# Build completed successfully (28 jobs), RC 0.

lake build LnLean.Proofs.ProtocolTargets LnLean.Proofs.WaveD.D17 \
  LnLean.Proofs.WaveD.D18 LnLean.Proofs.WaveD.D21 LnLean.Proofs.WaveD.D05 \
  LnLean.Proofs.WaveE.E19 LnLean.Proofs.WaveE.E22 LnLean.Proofs.WaveE.E06 \
  LnLean.Proofs.ModelHardening.F12 LnLean.Proofs.Protocol.HandshakeProps \
  LnLean.Proofs.Protocol.FeaturesProps LnLean.Proofs.Protocol.ErrorProps \
  LnLean.Proofs.Common
# ✔ [140/140] Built LnLean.Proofs.Common
# Build completed successfully (140 jobs), RC 0.
```

No full `lake build`, no `collect-obligations.py`, and no Git write command
was run.

`#print axioms` (scratch file `/tmp/opencode/s4_pr_wire_audit.lean`, run with
`lake env lean`):

| Declaration | Axioms |
|---|---|
| `CommitmentSignedFull.toCommitmentSigned_ofWire` | `propext` |
| `CommitmentSignedFull.toCommitmentSigned_surjective` | `propext` |
| `ProducedFrom.entries_map_output` | `propext` |
| `ProducedFrom.entries_signatures` | `propext` |
| `ProducedFrom.entries_digests` | `propext` |
| `ProducedFrom.entry_count` | `propext` |
| `ProducedFrom.entry_metadata` | `propext` |
| `commitment_signed_full_covers` | `propext`, `Quot.sound` |
| `commitment_signed_full_covers_exact` | `propext`, `Quot.sound` |
| `producedFrom_commitmentSignedFullOfState` | none |
| `wellFormed_toCommitmentSigned` | `propext`, `Classical.choice`, `Quot.sound` |
| `exampleSignedState_conserved` | none |
| `exampleSignedState_residual` | none |
| `example_commitment_signed_full_covers` | `propext`, `Quot.sound` |
| `legacy_wire_cannot_determine_coverage` | `propext`, `Quot.sound` |
| `legacy_wire_cannot_select_htlc_set` | `propext` |
| `projection_forgets_fee_and_number` | none |
| `projection_forgets_entry_metadata` | `propext` |
| `count_coverage_not_exact_coverage` | `propext` |
| `wellFormed_full_can_fail_coverage` | `propext`, `Classical.choice`, `Quot.sound` |
| `protocol_wire_summary` | `propext`, `Classical.choice`, `Quot.sound` |

Only the three permitted axioms (`propext`, `Quot.sound`, `Classical.choice`)
appear. The classical axioms are inherited from existing E20/`sigsValid`
dependencies, not from a new assumption.

Forbidden-construct scan (both owned Lean files):

```sh
grep -nE '\b(sorry|axiom|admit|native_decide|unsafe)\b|implemented_by' \
  LnLean/Protocol/Messages.lean LnLean/Proofs/ProtocolWireTargets.lean
# no matches
```

---

## 5. Compatibility notes

* `CommitmentSigned`, `Msg`, `MsgKind`, `msgLength`, `signatures`,
  `wellFormed`, and every existing name in `Messages.lean` are unchanged.
  The new import (`LnLean.Channel.Types`) creates no cycle.
* `CommitmentSignedFull` is **not** added to `Msg`: it is not a new BOLT wire
  type. It is a signer-side record whose `toCommitmentSigned` is the actual
  type-132 message. This avoids changing `Msg.kind`, `wireType`, `msgLength`,
  or any exhaustive match.
* `ofWire`/`toCommitmentSigned_ofWire` prove the extension is conservative at
  the wire level; `projection_forgets_fee_and_number` and
  `projection_forgets_entry_metadata` prove it is genuinely richer.
* The S3 negative results and their names in
  `LnLean.Proofs.ProtocolCoverageTargets` are untouched; the new module
  re-exports them under `legacy_wire_cannot_*`.
* All 15 direct importers of `Messages` compile after the change (RC 0). No
  record literal in the tree needed editing.

---

## 6. Integration steps (for the parent / integration owner)

1. **Root import.** Add
   `import LnLean.Proofs.ProtocolWireTargets` to `LnLean.lean` (this lane may
   not edit that file). The module already builds as an explicit target.
2. **Axiom audit.** Add the declarations from §4 to
   `LnLean/Proofs/AxiomAudit.lean` (owned by the parent). The expected result
   is the three permitted axioms only.
3. **Catalog retarget for `LN-PR-004`.** The old target
   `LnLean.Protocol.Messages.commitment_signed_covers` still takes coverage as
   a hypothesis and must not be promoted as-is. Recommended:
   * primary target: `LnLean.Proofs.ProtocolWireTargets.commitment_signed_full_covers_exact`;
   * bundled target: `LnLean.Proofs.ProtocolWireTargets.protocol_wire_summary`;
   * claim text must mention the conditional `ProducedFrom` + BOLT 3 value
     equations and the preserved wire-only negative results.
4. **`PR-02` roadmap update.** Record the new model fields and the remaining
   caveats (§7). `PR-02` can be narrowed to "conditional coverage proved; the
   production relation and sighash serializer are explicit hypotheses" or left
   open pending item 5.
5. **Optional next model step (not done here).** Add a BOLT 3
   `Commitment → ByteArray` sighash serializer and C3 verification so that
   `ProducedFrom`'s `sigAt`/digest fields can be derived from ECDSA rather than
   supplied. That is a separate cryptographic-model lane, not a wire-model
   edit.
6. Do **not** replace `ProtocolCoverageTargets.lean`; its negative results and
   `FeeIsFundingResidual` are imported by this lane and remain part of the
   evidence chain.

---

## 7. Scope caveats

1. **`ProducedFrom` is a signed-data relation, not a verifier.** `sigAt` is an
   explicit family `SignedHtlc → EcdsaSig`; `commitmentDigest` and
   `signedDataDigest` are explicit byte strings. The model still has no BOLT 3
   sighash serializer and no commitment-signature verification (C3 is not
   applied here). The theorem says what follows from an honestly produced
   record; it does not authenticate a received message.
2. **Fee units.** `Commitment.feeSat` is treated by the existing
   `waveE_e20_covers_fee` and `FeeIsFundingResidual` as the millisatoshi fee
   value, while `totalOutputValue` is in satoshis. This lane inherits that
   existing convention unchanged. `CommitmentSignedFull.feePaid` is a `Msat`,
   and `feePaid_eq` relates it to `st.feeSat`; no new unit mismatch is
   introduced beyond the inherited one.
3. **Exact HTLC identity vs. output identity.** The commitment output
   projection floors millisatoshi amounts to satoshis, so two distinct entries
   (e.g. `1000` and `1999` msat) can map to the same `CommitmentHTLCOutput`.
   Exact identity is carried by `ProducedFrom.entry_metadata`
   (id, msat amount, payment hash, direction, expiry) and
   `ProducedFrom.entry_digests`; `ProducedFrom.entries_map_output` is the
   on-chain output view. The main theorem states both.
4. **Channel membership.** `SignedState.channelId` and
   `CommitmentSignedFull.channelId` are related by `ProducedFrom.channelId_eq`,
   but `Commitment` itself still has no channel id, so channel membership of a
   commitment is a production-relation fact, not a `Commitment` field.
5. **Trimmed HTLCs.** `SignedState.htlcs` is the set of HTLCs the commitment
   emits (`Commitment.htlcs`); dust trimming and second-stage fees are the
   `CH-01`/`CH-02` lane's scope and are not modelled here. If an HTLC is
   trimmed, it must not appear in `SignedState.htlcs`, matching BOLT 2's
   "one signature per untrimmed HTLC output".
6. **No computational security claim.** As with the rest of the tree, C1/C3
   are algebraic interface assumptions; this module makes no reduction or
   advantage-bound claim.
7. **The legacy record alone remains insufficient.** The new theorem is a
   statement about the *full* record; `legacy_wire_cannot_determine_coverage`
   and `legacy_wire_cannot_select_htlc_set` are retained precisely so the old
   record is not credited with the new result.

---

## 8. Blockers / residual gaps

| Missing item | Consequence | Status here |
|---|---|---|
| BOLT 3 commitment sighash serializer `Commitment → ByteArray` | `commitmentDigest` cannot be computed from the state | Explicit field; not derived |
| Per-HTLC second-stage sighash serializer | `signedDataDigest` cannot be computed from the HTLC output | Explicit field; not derived |
| C3 verification wired to `ecdsaVerify` | `ProducedFrom`'s `sigAt` cannot be validated | Explicit relation; cryptographic lane |
| Commitments do not carry `channelId` | Channel membership is not a `Commitment` invariant | `ProducedFrom.channelId_eq` |
| Dust/second-stage fee integration | `SignedState.htlcs` must already be the untrimmed set | `CH-01`/`CH-02` lane |
| Full catalog/axiom-audit integration | Root import, `Obligations`, `Traceability`, `AxiomAudit` are parent-owned | §6 |

No blocker prevents the conditional theorem; the blockers are exactly the
fields the faithful claim keeps explicit.
