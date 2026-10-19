# S8-CH-CONSUMER-SITES — actual commitment-consumer construction/consumer sites (CH-01)

- Lane: `S8-CH-CONSUMER-SITES` (issue `CH-01`)
- Branch: `repair/integrated`
- Base commit: `3953c8c` (wave 8 launch; roadmap launch `50d78ed`)
- Owned files changed:
  - `LnLean/Proofs/Channel/CommitmentConsumerTargets.lean` (+35 lines, additive)
  - new `LnLean/Proofs/Channel/CommitmentConsumerSitesTargets.lean`
  - `agents/reports/swarm8/S8-CH-CONSUMER-SITES.md` (this report)
- Read-only files consulted: `docs/OPEN-ISSUES.md`, `agents/swarm/WAVE-8.md`,
  `agents/reports/swarm7/S7-CH-CONSUMER.md`, `LnLean/Channel/Commitment.lean`,
  `LnLean/Channel/Types.lean`, `LnLean/Proofs/ProtocolWireTargets.lean`,
  `LnLean/Proofs/ProtocolCoverageTargets.lean`,
  `LnLean/Proofs/Channel/SighashTargets.lean`,
  `LnLean/Proofs/Channel/SighashViewBindingTargets.lean`,
  `LnLean/Proofs/Channel/CommitmentTypesTargets.lean`,
  `LnLean/Proofs/Channel/CommitmentGrossNetTargets.lean`,
  `LnLean/Proofs/Channel/CommitmentIntegrationTargets.lean`,
  `LnLean/Proofs/WaveD/D12.lean`.

## 1. Verdict

**Delivered, compiled, and axiom-clean.**  The audit found **no production
`CommitmentTx` construction or consumer site**: outside the core module
`LnLean/Channel/Commitment.lean`, no model/protocol/L1 module even mentions
`CommitmentTx`.  The two real downstream consumers are proof-layer modules that
read a `Commitment` (`SignedState.toCommitment`):

1. `SighashTargets.viewOfState` — the sighash consumer;
2. `ProtocolCoverageTargets.CoversHtlcOutputs` applied by
   `ProtocolWireTargets.commitment_signed_full_covers` — the
   `commitment_signed` coverage consumer.

The lane therefore added the minimal **proof-layer adapter**
`SignedState.toCommitmentTx` at exactly that boundary and connected it to both
consumers.  It did not invent a fake production consumer.

At the actual `viewOfState` site:

- the legacy-shaped migrated list is **exactly** the list `viewOfState` reads
  (strongest statement at `List CommitmentOutput`);
- the sorted rich net list is a **permutation** of that same list (equality is
  false in general, D12);
- the `commitment_signed` coverage predicate is **equivalent** on
  `st.toCommitment` and on the constructed migrated transaction;
- the honest production theorem `commitment_signed_full_covers` now yields
  `CoversMigratedOutputs` at the migrated site end to end.

The normal-form hypotheses (`Migrated`, and `UsesRecordNet` in the abstract
API) remain explicit.  For the adapter transaction `UsesRecordNet` is
definitional; `Migrated` is the genuine BOLT 3 no-trim premise and the retained
counterexample shows it cannot be dropped.

## 2. Exact construction/consumer sites audited

Search commands (run at `3953c8c` plus this lane's additions):

```sh
grep -rln "CommitmentTx" LnLean/Channel LnLean/Protocol LnLean/Bitcoin \
  LnLean/Wire LnLean/Crypto LnLean/Routing
grep -rn "CommitmentTx where\|: CommitmentTx :=\|{ commitment :=" LnLean/
grep -rn "def viewOfState\|def CoversHtlcOutputs\|def .*consumerOutputs" LnLean/
grep -rn "SignedState where\|: SignedState :=" LnLean/
```

### 2.1 Construction sites

| Site | File:line | What it does | Consumer relevance |
|---|---|---|---|
| `CommitmentTx` structure | `LnLean/Channel/Commitment.lean:849` | rich output model | core definition |
| `CommitmentTx.ofCommitment` | `LnLean/Channel/Commitment.lean:1097` | the only production lift from a legacy `Commitment` | construction adapter |
| `CommitmentTx.migratedFrom` | `LnLean/Proofs/Channel/CommitmentGrossNetTargets.lean:408` | proof-layer migration demo | not a downstream site |
| `CommitmentIntegration.dustDemoTx` | `LnLean/Proofs/Channel/CommitmentIntegrationTargets.lean:744` | counterexample literal | retained counterexample |
| `SignedState.toCommitment` | `LnLean/Proofs/ProtocolWireTargets.lean:206` | the signed-state record projection consumers read | **actual state construction** |

There is **no** production `CommitmentTx` literal: the model/protocol/L1
directories contain `CommitmentTx` only in `LnLean/Channel/Commitment.lean`
(173 occurrences, all definitions or doc strings).  `SignedState` is itself a
proof-layer signed-state model; its only constructions in the tree are
`exampleSignedState` (`ProtocolWireTargets.lean:422`), the concrete witness
below, and the new adapter.

### 2.2 Consumer sites

| Consumer | File:line | What it reads | Connected by |
|---|---|---|---|
| `viewOfState` | `LnLean/Proofs/Channel/SighashTargets.lean:351` | `st.toCommitment.commitmentOutputs` into `CommitmentSighashView.outputs` (`viewOfState_outputs`, line 379) | `migratedConsumerOutputs_eq_viewOfState_outputs`, `viewOfState_outputs_perm_netConsumerOutputs` |
| `CoversHtlcOutputs` | `LnLean/Proofs/ProtocolCoverageTargets.lean:102` | `htlcOutputCount c.commitmentOutputs` | `coversHtlcOutputs_iff_coversMigratedOutputs`, `coversMigratedOutputs_iff_stateHtlcs` |
| `commitment_signed_full_covers` | `LnLean/Proofs/ProtocolWireTargets.lean:303` | `CoversHtlcOutputs … st.toCommitment` | `commitment_signed_full_covers_migrated` |
| view binding | `LnLean/Proofs/Channel/SighashViewBindingTargets.lean:380` | output-list equality under a verifying signature | `signature_binds_migratedConsumerOutputs` |

The only model-level definition of a consumer list is
`CommitmentTx.consumerOutputs` at
`LnLean/Channel/Commitment.lean:1055`, defined as
`tx.commitment.commitmentOutputs` (legacy) and `netConsumerOutputs` at line
1074, defined as `tx.migrateForConsumer.outputsNet`.

## 3. Files changed

### 3.1 `LnLean/Proofs/Channel/CommitmentConsumerTargets.lean` (additive, +35)

New consumer-path corollaries between `migrated_of_no_trim` and the
`commitment_signed` coverage section:

```lean
theorem netConsumerOutputs_perm_consumerOutputs_of_migrated
    (tx : CommitmentTx) (hnet : tx.UsesRecordNet) (hm : tx.Migrated)
    (hdust : 0 < tx.dustLimitSat) :
    (tx.netConsumerOutputs.map CommitmentTxOutput.toCommitmentOutput).Perm
      tx.consumerOutputs

theorem netConsumerOutputs_perm_consumerOutputs_of_no_trim
    (tx : CommitmentTx) (hnet : tx.UsesRecordNet)
    (hdust : 0 < tx.dustLimitSat)
    (hl : tx.dustLimitSat ≤ tx.commitment.toLocalSat)
    (hr : tx.dustLimitSat ≤ tx.commitment.toRemoteSat)
    (hh : ∀ h ∈ tx.commitment.htlcs,
      tx.dustLimitSat ≤ tx.netAmountSat h) :
    (tx.netConsumerOutputs.map CommitmentTxOutput.toCommitmentOutput).Perm
      tx.consumerOutputs

theorem netConsumerOutputs_length_eq_consumerOutputs_of_migrated
    (tx : CommitmentTx) (hnet : tx.UsesRecordNet) (hm : tx.Migrated)
    (hdust : 0 < tx.dustLimitSat) :
    tx.netConsumerOutputs.length = tx.consumerOutputs.length
```

These are direct consequences of the pre-existing
`netConsumerOutputs_perm_migratedConsumerOutputs` and
`migratedConsumerOutputs_eq_consumerOutputs_of_migrated`; no statement is
weakened and no existing name is changed.

### 3.2 new `LnLean/Proofs/Channel/CommitmentConsumerSitesTargets.lean`

Namespace `LnLean.Proofs.Channel.CommitmentConsumerSites`.  Imports
`CommitmentConsumerTargets`, `SighashTargets`, and
`SighashViewBindingTargets`.

Adapter:

```lean
def _root_.LnLean.Proofs.ProtocolWireTargets.SignedState.toCommitmentTx
    (st : SignedState) (dustLimitSat : Nat)
    (toLocalScript toRemoteScript localAnchorScript remoteAnchorScript :
      ScriptPubKey)
    (htlcScript : CommitmentHTLCOutput → ScriptPubKey) : CommitmentTx
```

Projections and normal form:

```lean
@[simp] theorem signedStateToCommitmentTx_commitment (…) :
    (st.toCommitmentTx …).commitment = st.toCommitment

@[simp] theorem signedStateToCommitmentTx_dustLimitSat (…) :
    (st.toCommitmentTx …).dustLimitSat = dustLimitSat

theorem signedStateToCommitmentTx_usesRecordNet (…) :
    (st.toCommitmentTx …).UsesRecordNet

@[simp] theorem signedStateToCommitmentTx_consumerOutputs (…) :
    (st.toCommitmentTx …).consumerOutputs =
      st.toCommitment.commitmentOutputs

theorem signedStateToCommitmentTx_migrated_of_no_trim
    (st : SignedState) (dustLimitSat : Nat) (…) (hdust : 0 < dustLimitSat)
    (hl : dustLimitSat ≤ st.toCommitment.toLocalSat)
    (hr : dustLimitSat ≤ st.toCommitment.toRemoteSat)
    (hh : ∀ h ∈ st.toCommitment.htlcs,
      dustLimitSat ≤ h.netAmountSat) :
    (st.toCommitmentTx …).Migrated
```

Sighash consumer (`viewOfState`):

```lean
theorem migratedConsumerOutputs_eq_viewOfState_outputs
    (ctx : SighashContext) (st : SignedState) (dustLimitSat : Nat) (…)
    (hm : (st.toCommitmentTx …).Migrated)
    (hdust : 0 < dustLimitSat) :
    (st.toCommitmentTx …).migratedConsumerOutputs =
      (viewOfState ctx st).outputs

theorem migratedConsumerOutputs_eq_viewOfState_outputs_of_no_trim
    (ctx : SighashContext) (st : SignedState) (dustLimitSat : Nat) (…)
    (hdust : 0 < dustLimitSat)
    (hl : dustLimitSat ≤ st.toCommitment.toLocalSat)
    (hr : dustLimitSat ≤ st.toCommitment.toRemoteSat)
    (hh : ∀ h ∈ st.toCommitment.htlcs,
      dustLimitSat ≤ h.netAmountSat) :
    (st.toCommitmentTx …).migratedConsumerOutputs =
      (viewOfState ctx st).outputs

theorem viewOfState_outputs_perm_netConsumerOutputs
    (ctx : SighashContext) (st : SignedState) (dustLimitSat : Nat) (…)
    (hm : (st.toCommitmentTx …).Migrated)
    (hdust : 0 < dustLimitSat) :
    ((st.toCommitmentTx …).netConsumerOutputs.map
        CommitmentTxOutput.toCommitmentOutput).Perm
      (viewOfState ctx st).outputs

theorem viewOfState_outputs_perm_netConsumerOutputs_of_no_trim (…) : …
theorem viewOfState_outputs_length_eq_netConsumerOutputs (…) : …
```

Signature-bound preservation (uses `SighashViewBindingTargets`):

```lean
theorem signature_binds_migratedConsumerOutputs
    {M : PrimitiveModel} (hC3 : EufCma M.ecdsaVerify)
    {law : CommitmentSigningLaw M}
    {ctx : SighashContext} {st : SignedState} {f : CommitmentSignedFull}
    (h : SighashProduces M law ctx st f)
    {views : List CommitmentSighashView}
    (hbind : ViewDigestCollisionFree M views)
    (hv : viewOfState ctx st ∈ views)
    {ctx' : SighashContext} {st' : SignedState}
    (hv' : viewOfState ctx' st' ∈ views)
    (hver : M.ecdsaVerify ctx.commitmentKey
      (commitmentTag ++ commitmentDigest M (viewOfState ctx' st'))
      f.commitmentSignature = true)
    (dustLimitSat : Nat) (… scripts …)
    (hm : (st.toCommitmentTx …).Migrated)
    (hm' : (st'.toCommitmentTx …).Migrated)
    (hdust : 0 < dustLimitSat) :
    (st'.toCommitmentTx …).migratedConsumerOutputs =
      (st.toCommitmentTx …).migratedConsumerOutputs
```

Coverage consumer:

```lean
theorem coversHtlcOutputs_iff_coversMigratedOutputs
    (m : CommitmentSigned) (st : SignedState) (dustLimitSat : Nat) (…)
    (hm : (st.toCommitmentTx …).Migrated)
    (hdust : 0 < dustLimitSat) :
    CoversHtlcOutputs m st.toCommitment ↔
      CoversMigratedOutputs m (st.toCommitmentTx …)

theorem coversMigratedOutputs_iff_stateHtlcs
    (m : CommitmentSigned) (st : SignedState) (dustLimitSat : Nat) (…)
    (hm : (st.toCommitmentTx …).Migrated)
    (hdust : 0 < dustLimitSat) :
    CoversMigratedOutputs m (st.toCommitmentTx …) ↔
      m.htlcSignatures.length = st.toCommitment.htlcs.length

theorem commitment_signed_full_covers_migrated
    (f : CommitmentSignedFull) (st : SignedState)
    (sigAt : SignedHtlc → EcdsaSig)
    (hprod : ProducedFrom f st sigAt)
    (hcons : CommitmentConserved st.toCommitment)
    (hres : FeeIsFundingResidual st.feerate st.toCommitment)
    (dustLimitSat : Nat) (… scripts …)
    (hm : (st.toCommitmentTx …).Migrated)
    (hdust : 0 < dustLimitSat) :
    CoversMigratedOutputs f.toCommitmentSigned (st.toCommitmentTx …)
```

Non-vacuity and retained counterexample:

```lean
def siteExampleState : SignedState
def siteExampleContext : SighashContext
def siteExampleScript : ScriptPubKey

theorem siteExample_migrated : (siteExampleState.toCommitmentTx …).Migrated
theorem siteExample_migratedConsumerOutputs_eq_view : …
theorem siteExample_view_perm : …

theorem legacyCoverage_not_preserved_at_site :
    CommitmentConsumer.oneHtlcSigMessage.htlcSignatures.length =
        htlcOutputCount
          CommitmentIntegration.dustDemoTx.commitment.commitmentOutputs ∧
      ¬ CoversMigratedOutputs CommitmentConsumer.oneHtlcSigMessage
        CommitmentIntegration.dustDemoTx
```

The concrete witness uses the BOLT 2 dust limit 354, two 10 000-sat balance
outputs, and one 354-sat net HTLC, so `Migrated` and both consumer statements
are instantiated on non-vacuous data.

## 4. Build result

Exact command, under the shared lock:

```sh
cd /home/ubuntu/ln-lean-repair
export PATH=/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Proofs.Channel.CommitmentConsumerSitesTargets
```

Observed final output:

```text
✔ [60/60] Built LnLean.Proofs.Channel.CommitmentConsumerSitesTargets (752ms)
Build completed successfully (60 jobs).
RC=0
```

`LnLean.Proofs.Channel.CommitmentConsumerTargets` also rebuilds in the same
60-job closure.  No warnings originate from either owned file (the remaining
warnings are pre-existing `if_neg` deprecations in
`LnLean/Bitcoin/Sighash.lean`).  No full-tree build, catalog script, or Git
write was run by this lane.

## 5. Axiom result

`#print axioms` (scratch file `/tmp/opencode/AuditSitesWave8.lean`, not
committed):

```text
no axioms:        signedStateToCommitmentTx_commitment,
                  signedStateToCommitmentTx_usesRecordNet,
                  signedStateToCommitmentTx_consumerOutputs,
                  siteExample_migrated
propext, Quot.sound:
                  signedStateToCommitmentTx_migrated_of_no_trim,
                  migratedConsumerOutputs_eq_viewOfState_outputs,
                  migratedConsumerOutputs_eq_viewOfState_outputs_of_no_trim,
                  viewOfState_outputs_perm_netConsumerOutputs,
                  viewOfState_outputs_perm_netConsumerOutputs_of_no_trim,
                  viewOfState_outputs_length_eq_netConsumerOutputs,
                  coversHtlcOutputs_iff_coversMigratedOutputs,
                  coversMigratedOutputs_iff_stateHtlcs,
                  commitment_signed_full_covers_migrated,
                  siteExample_migratedConsumerOutputs_eq_view,
                  siteExample_view_perm,
                  legacyCoverage_not_preserved_at_site,
                  netConsumerOutputs_perm_consumerOutputs_of_migrated,
                  netConsumerOutputs_perm_consumerOutputs_of_no_trim,
                  netConsumerOutputs_length_eq_consumerOutputs_of_migrated
propext, Classical.choice, Quot.sound:
                  signature_binds_migratedConsumerOutputs
```

Every set is a subset of the allowed
`{propext, Quot.sound, Classical.choice}`.  No `sorryAx`, user axiom,
`native_decide`, `unsafe`, or `@[implemented_by]` occurs.

Note: vendor `.olean` artifacts were partially absent in the shared tree when
the audit was run (only 6 of 129 vendor modules were built).  This lane rebuilt
the read-only vendor library with `lake build Bitcoin` under the same shared
lock; no vendor source was edited.  The required lane build above is green
after that.

## 6. Forbidden-construct scan

```sh
cd /home/ubuntu/ln-lean-repair
grep -nE '\b(sorry|axiom|admit|native_decide|unsafe|implemented_by)\b' \
  LnLean/Proofs/Channel/CommitmentConsumerSitesTargets.lean \
  LnLean/Proofs/Channel/CommitmentConsumerTargets.lean
```

Observed output:

```text
NO_FORBIDDEN_TOKENS
```

(`decide` in `siteExample_migrated` is kernel reduction, not
`native_decide`; the axiom audit confirms no extra axioms.)

## 7. Adapter and counterexample boundaries

- **No external/production consumer exists.**  `CommitmentTx` is referenced
  only by its own core definitions.  `SignedState`/`viewOfState`/
  `CoversHtlcOutputs` are proof-layer models.  The lane therefore adds a
  proof-layer adapter and states this boundary rather than patching a fake
  production call site.
- **Strongest list statement is split by type.**  At the legacy
  `List CommitmentOutput` boundary the migrated list is *exactly* the
  `viewOfState` list.  At the sorted rich `List CommitmentTxOutput` boundary
  the relation is `List.Perm`: the rich path sorts (BOLT 3), the legacy path
  does not.  D12's `waveD_d12_output_ordering_fails` refutes unconditional
  equality/ordering, and is retained unchanged.
- **Normal-form hypotheses are explicit and necessary.**
  `Migrated` (zero non-HTLC outputs are exactly below-dust; every listed HTLC
  survives) and `0 < dustLimitSat` are required.  For the adapter transaction
  `UsesRecordNet` is definitional.  `legacyCoverage_not_preserved_at_site`
  re-exports the wave-7 one-signature/dust-1000 counterexample showing a
  coverage consumer can lose a signature if the premise is dropped.
- **No reordering-invariant digest claim.**  The permutation statement is about
  the output multiset/list a consumer reads; `viewOfState` serializes the list
  in its legacy order.  Nothing here says a sighash digest is invariant under
  reordering.
- **Crypto hypotheses stay explicit.**  The signature-bound preservation
  theorem keeps `EufCma`, `ViewDigestCollisionFree`, and the verified-message
  equation as hypotheses; it does not derive them.
- **Scripts/dust are caller-supplied.**  `SignedState.toCommitmentTx` takes the
  dust limit and all scripts explicitly, exactly like `ofCommitment`; it does
  not invent consensus data.
- **Out of scope:** script execution, signatures, witnesses, sighash bytes,
  consensus validity, and a production wire-to-`SignedState` constructor.

## 8. Integration steps (parent only)

1. Import the module from the aggregate/root proof module:
   ```lean
   import LnLean.Proofs.Channel.CommitmentConsumerSitesTargets
   ```
   (`LnLean.lean` is outside this lane's write set.)
2. Register the CH-01 target evidence in `LnLean/Proofs/Obligations.lean` and
   `LnLean/Proofs/Traceability.lean`.  Suggested addition to the existing
   CH-01 target string:
   ```text
   LnLean.Proofs.Channel.CommitmentConsumerSites.migratedConsumerOutputs_eq_viewOfState_outputs;
   LnLean.Proofs.Channel.CommitmentConsumerSites.viewOfState_outputs_perm_netConsumerOutputs;
   LnLean.Proofs.Channel.CommitmentConsumerSites.coversHtlcOutputs_iff_coversMigratedOutputs;
   LnLean.Proofs.Channel.CommitmentConsumerSites.commitment_signed_full_covers_migrated
   ```
3. Add the headline theorems to `LnLean/Proofs/PhaseC3/AxiomAudit.lean` (the
   §5 list is ready).
4. Update `docs/OPEN-ISSUES.md` `CH-01`: keep it closed, and record that the
   consumer path is now compiled at the actual `viewOfState` and
   `CoversHtlcOutputs` sites.  Keep the D12 and
   `legacyCoverage_not_preserved_by_net_migration` caveats.
5. Optional: when a production `SignedState` construction path is added, use
   `SignedState.toCommitmentTx` at that site; no consumer proof changes are
   needed.

## 9. Blockers

- **None for this lane.**  The required build and axiom audit are green.
- **Transient shared-worktree interference (resolved at report time).**  During
  the lane, `LnLean/Protocol/Handshake.lean` was mid-edit by
  `S8-PR-ACCEPT-PAYLOAD` and did not compile; because
  `SighashTargets` imports `WaveE.E20 → Protocol.Handshake`, the lane build
  failed transiently.  The lane waited, rebuilt once the other lane's edit
  stabilized, and verified the required target (60 jobs, RC 0).  The lane
  reads `Handshake` only through the existing import closure; it does not edit
  it.
- **Vendor artifact gap (environment only).**  Only 6/129 vendor `.olean`
  files were present initially; `lake build Bitcoin` was run under the shared
  lock to make the `#print axioms` scratch check possible.  No vendor source
  changed.

## 10. Catalog/roadmap recommendation for CH-01

**Keep `CH-01` closed, with the consumer path now evidenced at real sites.**
The issue's remaining sentence ("the rich model is not the legacy consumer
path") is now answered by compiled theorems rather than a proposal:

- the construction site is `SignedState.toCommitmentTx`;
- the sighash consumer reads exactly the migrated legacy list and the sorted
  net list up to BOLT 3 permutation;
- the `commitment_signed` coverage consumer is equivalent at the migrated site,
  including the honest-production theorem;
- the normal-form premise and the coverage counterexample are explicit.

Recommended catalog edits:

1. Add the four site theorems from §8.2 to the CH-01 row's evidence list; do
   not add a new row (the model did not grow, only the consumer connection).
2. Keep the D12 / `legacyCoverage_not_preserved_by_net_migration` anchors
   unchanged; do not upgrade the claim to digest- or byte-level consumer
   invariance.
3. Roadmap: no further `CH-01` lane.  If a production `SignedState`/wire
   constructor appears later, the only follow-up is to call
   `SignedState.toCommitmentTx` there (an integration step, not a proof gap).
   Byte-level consumer equivalence would belong to `PR-05`/`L1-01`, not
   `CH-01`.
