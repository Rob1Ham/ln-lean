# S7-CH-CONSUMER — legacy commitment-consumer migration to the rich/net path

- Lane: `S7-CH-CONSUMER` (issues `CH-01`, `CH-02`)
- Branch: `repair/integrated`
- Launch commit: `3180581` (wave 7 launch)
- Owned files:
  - `LnLean/Channel/Commitment.lean`
  - new `LnLean/Proofs/Channel/CommitmentConsumerTargets.lean`
  - `agents/reports/swarm7/S7-CH-CONSUMER.md` (this report)

Read-only files consulted: `docs/OPEN-ISSUES.md`, `agents/swarm/WAVE-7.md`,
`docs/ASSUMPTIONS.md`, `agents/reports/swarm6/S6-CH-TYPES.md`,
`LnLean/Channel/Types.lean`,
`LnLean/Proofs/Channel/CommitmentGrossNetTargets.lean`,
`LnLean/Proofs/Channel/CommitmentTypesTargets.lean`,
`LnLean/Proofs/Channel/CommitmentIntegrationTargets.lean`,
`LnLean/Proofs/Channel/CommitmentTxProps.lean`,
`LnLean/Proofs/ProtocolCoverageTargets.lean`,
`LnLean/Proofs/ProtocolWireTargets.lean`,
`LnLean/Proofs/Channel/SighashTargets.lean`,
`LnLean/Proofs/WaveD/D12.lean`.

## 1. Result

`CH-01` is closed at the consumer boundary for the coverage consumer and for
any consumer that reads the legacy `List CommitmentOutput` path.  The core
migration API is now in the owned `Commitment.lean`:

- `CommitmentTx.consumerOutputs` — the legacy output list
  (`tx.commitment.commitmentOutputs`).
- `CommitmentTx.migrateForConsumer` — the drop-in net replacement
  (definitionally `tx.migrateNet`).
- `CommitmentTx.migratedConsumerOutputs` — the legacy-shaped list after
  migration (`tx.migrateForConsumer.commitment.commitmentOutputs`).
- `CommitmentTx.netConsumerOutputs` — the sorted rich net list
  (`tx.migrateForConsumer.outputsNet`).
- `CommitmentTx.ofCommitment` — lifts an existing `Commitment` record to the
  rich model with caller-supplied dust limit and scripts; the net projection
  defaults to the record field, so no existing producer changes.
- `CommitmentPair.migrateNet` — pair-level migration used by
  `commitmentPairOfBalances` and channel-state consumers.

The proof module proves the canonical refinement at that boundary:

- `netConsumerOutputs_perm_migratedConsumerOutputs`: the sorted rich net list
  is a permutation of the migrated legacy consumer list at a protocol-valid
  positive dust limit.
- `migratedConsumerOutputs_eq_consumerOutputs_of_migrated`: in the BOLT 3
  survivor normal form (`Migrated` + record net projection), migration does
  not change the legacy consumer list at all.
- `CoversMigratedOutputs` plus four equivalences: the actual
  `commitment_signed` coverage formula is exactly one signature per
  net-surviving HTLC; on the normal form it is unchanged from the legacy
  formula; the premises are necessary.
- `legacyCoverage_not_preserved_by_net_migration`: a new consumer-boundary
  counterexample showing the normal-form/no-trim premise cannot be dropped.
- `d12_*` and `wave4_dust_trimming_not_perm_retained` are restated unchanged.

`CH-02` remains closed at the record layer (wave 6).  This lane adds the
consumer path on top of it; no field, conservation, or effective-fee theorem is
weakened.

### 1.1 `trimmedTotalSat` naming decision

**Decision: keep `Commitment.trimmedTotalSat`; do not rename in wave 7.**

Reasons:

1. `Commitment.trimmedSat` is already the *computed* trim function
   (`Commitment → Nat → (CommitmentHTLCOutput → Nat) → Nat`) and is consumed by
   the unowned wave-5 module `CommitmentGrossNetTargets` and by
   `CommitmentTx.trimmedValue` / `recordTrimmedValue`.
2. The field lives in `LnLean/Channel/Types.lean`, which this lane may not
   edit.  A rename would also require coordinated edits in the unowned wave-5
   and wave-6 modules, i.e. a breaking cross-file API change with no semantic
   gain.
3. The stored/computed pair is unambiguous and documented:
   `Commitment.trimmedTotalSat` (stored gross value removed by trimming) and
   `Commitment.trimmedValueFor` (computed alias).  The core doc comment now
   states the decision explicitly.

If a future catalog decision insists on the literal field name
`Commitment.trimmedSat`, the exact coordinated patch is:

```lean
-- 1. LnLean/Channel/Types.lean: rename the stored field
structure Commitment where
  ...
  trimmedSat : Nat := 0          -- was trimmedTotalSat

-- 2. LnLean/Channel/Commitment.lean: rename the computed function
def Commitment.trimmedValueFor (c : Commitment) (dustLimitSat : Nat)
    (netAmountSat : CommitmentHTLCOutput → Nat) : Nat := ...
-- delete the old computed `Commitment.trimmedSat` and the alias body, then
-- update `CommitmentTx.trimmedValue`, `recordTrimmedValue`,
-- `Commitment.migrateNet`, and all doc/name references.

-- 3. LnLean/Proofs/Channel/CommitmentGrossNetTargets.lean (unowned):
--    line 593 `unfold ... Commitment.trimmedSat` → `Commitment.trimmedValueFor`
--    line 640 `tx.commitment.trimmedSat ...` → `tx.commitment.trimmedValueFor ...`

-- 4. LnLean/Proofs/Channel/CommitmentTypesTargets.lean:
--    stored-field references `trimmedTotalSat` → `trimmedSat`;
--    computed references stay on `trimmedValueFor`.
```

This lane did not apply the rename.

## 2. Required build

Command run exactly as specified, under `flock`:

```sh
cd /home/ubuntu/ln-lean-repair
export PATH=/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Channel.Commitment \
    LnLean.Proofs.Channel.CommitmentConsumerTargets \
    LnLean.Proofs.Channel.CommitmentTypesTargets \
    LnLean.Proofs.Channel.CommitmentGrossNetTargets
```

Observed final output:

```text
✔ [24/24] Built LnLean.Proofs.Channel.CommitmentConsumerTargets (714ms)
Build completed successfully (24 jobs).
```

**Build RC: 0.**  No warnings from the two owned files.  No full
`lake build`, `collect-obligations.py`, `collect-anchors.py`, or Git write was
run.

## 3. Exact signatures

### 3.1 `LnLean/Channel/Commitment.lean` (owned additions)

```lean
def CommitmentPair.migrateNet (p : CommitmentPair) (dustLimitSat : Nat) :
    CommitmentPair

theorem CommitmentPair.migrateNet_localCommitment (p : CommitmentPair)
    (dustLimitSat : Nat) :
    (p.migrateNet dustLimitSat).localCommitment =
      p.localCommitment.migrateNet dustLimitSat

theorem CommitmentPair.migrateNet_remoteCommitment (p : CommitmentPair)
    (dustLimitSat : Nat) :
    (p.migrateNet dustLimitSat).remoteCommitment =
      p.remoteCommitment.migrateNet dustLimitSat

def CommitmentTx.consumerOutputs (tx : CommitmentTx) : List CommitmentOutput

def CommitmentTx.migrateForConsumer (tx : CommitmentTx) : CommitmentTx

def CommitmentTx.migratedConsumerOutputs (tx : CommitmentTx) :
    List CommitmentOutput

def CommitmentTx.netConsumerOutputs (tx : CommitmentTx) :
    List CommitmentTxOutput

theorem CommitmentTx.migrateForConsumer_eq_migrateNet (tx : CommitmentTx) :
    tx.migrateForConsumer = tx.migrateNet

theorem CommitmentTx.consumerOutputs_eq (tx : CommitmentTx) :
    tx.consumerOutputs = tx.commitment.commitmentOutputs

theorem CommitmentTx.migratedConsumerOutputs_eq (tx : CommitmentTx) :
    tx.migratedConsumerOutputs =
      (tx.migrateNet).commitment.commitmentOutputs

theorem CommitmentTx.netConsumerOutputs_eq (tx : CommitmentTx) :
    tx.netConsumerOutputs = (tx.migrateNet).outputsNet

def CommitmentTx.ofCommitment (c : Commitment) (dustLimitSat : Nat)
    (toLocalScript toRemoteScript localAnchorScript remoteAnchorScript :
      ScriptPubKey)
    (htlcScript : CommitmentHTLCOutput → ScriptPubKey) : CommitmentTx

theorem CommitmentTx.ofCommitment_commitment (c : Commitment)
    (dustLimitSat : Nat) (toLocalScript toRemoteScript localAnchorScript
      remoteAnchorScript : ScriptPubKey)
    (htlcScript : CommitmentHTLCOutput → ScriptPubKey) :
    (CommitmentTx.ofCommitment c dustLimitSat toLocalScript toRemoteScript
      localAnchorScript remoteAnchorScript htlcScript).commitment = c
```

### 3.2 `LnLean/Proofs/Channel/CommitmentConsumerTargets.lean`

Namespace: `LnLean.Proofs.Channel.CommitmentConsumer`.

```lean
theorem consumerOutputs_eq_commitmentOutputs (tx : CommitmentTx) :
    tx.consumerOutputs = tx.commitment.commitmentOutputs

theorem migratedConsumerOutputs_eq (tx : CommitmentTx) :
    tx.migratedConsumerOutputs =
      (tx.migrateNet).commitment.commitmentOutputs

theorem netConsumerOutputs_eq (tx : CommitmentTx) :
    tx.netConsumerOutputs = (tx.migrateNet).outputsNet

theorem netConsumerOutputs_perm_migratedConsumerOutputs (tx : CommitmentTx)
    (hdust : 0 < tx.dustLimitSat) :
    (tx.netConsumerOutputs.map CommitmentTxOutput.toCommitmentOutput).Perm
      tx.migratedConsumerOutputs

theorem migratedConsumerOutputs_eq_canonicalOutputs (tx : CommitmentTx)
    (hdust : 0 < tx.dustLimitSat) :
    tx.migratedConsumerOutputs = (tx.migrateNet).canonicalOutputs

theorem ofCommitment_consumerOutputs (c : Commitment) (dustLimitSat : Nat)
    (toLocalScript toRemoteScript localAnchorScript remoteAnchorScript :
      ScriptPubKey) (htlcScript : CommitmentHTLCOutput → ScriptPubKey) :
    (CommitmentTx.ofCommitment c dustLimitSat toLocalScript toRemoteScript
        localAnchorScript remoteAnchorScript htlcScript).consumerOutputs =
      c.commitmentOutputs

theorem migratedConsumerOutputs_eq_consumerOutputs_of_migrated
    (tx : CommitmentTx) (hnet : tx.UsesRecordNet) (hm : tx.Migrated)
    (hdust : 0 < tx.dustLimitSat) :
    tx.migratedConsumerOutputs = tx.consumerOutputs

theorem migrated_of_no_trim (tx : CommitmentTx) (hdust : 0 < tx.dustLimitSat)
    (hl : tx.dustLimitSat ≤ tx.commitment.toLocalSat)
    (hr : tx.dustLimitSat ≤ tx.commitment.toRemoteSat)
    (hh : ∀ h ∈ tx.commitment.htlcs,
      tx.dustLimitSat ≤ tx.netAmountSat h) :
    tx.Migrated

def CoversMigratedOutputs (m : CommitmentSigned) (tx : CommitmentTx) : Prop :=
  m.htlcSignatures.length = htlcOutputCount tx.migratedConsumerOutputs

theorem coversMigratedOutputs_iff_legacyRecord (m : CommitmentSigned)
    (tx : CommitmentTx) :
    CoversMigratedOutputs m tx ↔
      m.htlcSignatures.length =
        htlcOutputCount (tx.migrateForConsumer).commitment.commitmentOutputs

theorem coversMigratedOutputs_iff_survivingHtlcs (m : CommitmentSigned)
    (tx : CommitmentTx) :
    CoversMigratedOutputs m tx ↔
      m.htlcSignatures.length =
        (tx.commitment.htlcs.filter
          (fun h => h.keepAtDust tx.dustLimitSat)).length

theorem coversMigratedOutputs_iff_legacy_of_migrated (m : CommitmentSigned)
    (tx : CommitmentTx) (hnet : tx.UsesRecordNet) (hm : tx.Migrated)
    (hdust : 0 < tx.dustLimitSat) :
    CoversMigratedOutputs m tx ↔
      m.htlcSignatures.length =
        htlcOutputCount tx.commitment.commitmentOutputs

theorem coversMigratedOutputs_iff_legacy_of_no_trim (m : CommitmentSigned)
    (tx : CommitmentTx) (hnet : tx.UsesRecordNet)
    (hdust : 0 < tx.dustLimitSat)
    (hl : tx.dustLimitSat ≤ tx.commitment.toLocalSat)
    (hr : tx.dustLimitSat ≤ tx.commitment.toRemoteSat)
    (hh : ∀ h ∈ tx.commitment.htlcs,
      tx.dustLimitSat ≤ tx.netAmountSat h) :
    CoversMigratedOutputs m tx ↔
      m.htlcSignatures.length =
        htlcOutputCount tx.commitment.commitmentOutputs

def oneHtlcSigMessage : CommitmentSigned

theorem legacyCoverage_not_preserved_by_net_migration :
    oneHtlcSigMessage.htlcSignatures.length =
        htlcOutputCount
          CommitmentIntegration.dustDemoTx.commitment.commitmentOutputs ∧
      ¬ CoversMigratedOutputs oneHtlcSigMessage
        CommitmentIntegration.dustDemoTx

theorem CommitmentPair.migrateNet_htlcs (p : CommitmentPair)
    (dustLimitSat : Nat) :
    (p.migrateNet dustLimitSat).localCommitment.htlcs =
        p.localCommitment.htlcs.filter
          (fun h => h.keepAtDust dustLimitSat) ∧
      (p.migrateNet dustLimitSat).remoteCommitment.htlcs =
        p.remoteCommitment.htlcs.filter
          (fun h => h.keepAtDust dustLimitSat)

theorem commitmentPairOfBalances_migrateNet_htlcs (localParams remoteParams
    : ChannelParams) (b : Balance) (fee number : Nat)
    (funder : Direction) (dustLimitSat : Nat) :
    ((commitmentPairOfBalances localParams remoteParams b fee number
        funder).migrateNet dustLimitSat).localCommitment.htlcs = [] ∧
      ((commitmentPairOfBalances localParams remoteParams b fee number
        funder).migrateNet dustLimitSat).remoteCommitment.htlcs = []
```

Retained counterexamples/refinements:

```lean
theorem d12_output_ordering_fails_retained : ...
theorem d12_zero_value_htlc_emitted_retained : ...
theorem wave4_dust_trimming_not_perm_retained : ...
theorem wave6_migrateNet_refinement_retained (tx : CommitmentTx)
    (hdust : 0 < tx.dustLimitSat) : ...
```

## 4. Axiom audit

Scratch file `/tmp/opencode/AuditConsumer.lean` (not committed) ran
`#print axioms` on all headline results:

```text
no axioms:      CommitmentPair.migrateNet_htlcs,
                commitmentPairOfBalances_migrateNet_htlcs
propext only:   coversMigratedOutputs_iff_legacyRecord,
                d12_zero_value_htlc_emitted_retained
propext, Quot.sound:
                netConsumerOutputs_perm_migratedConsumerOutputs,
                migratedConsumerOutputs_eq_canonicalOutputs,
                migratedConsumerOutputs_eq_consumerOutputs_of_migrated,
                migrated_of_no_trim,
                coversMigratedOutputs_iff_survivingHtlcs,
                coversMigratedOutputs_iff_legacy_of_migrated,
                coversMigratedOutputs_iff_legacy_of_no_trim,
                legacyCoverage_not_preserved_by_net_migration,
                d12_output_ordering_fails_retained,
                wave4_dust_trimming_not_perm_retained,
                wave6_migrateNet_refinement_retained
```

All axiom sets are subsets of the allowed
`{propext, Quot.sound, Classical.choice}`.  No theorem depends on `sorryAx`,
a user axiom, `native_decide`, `unsafe`, or `@[implemented_by]`.

## 5. Forbidden-construct scan

```sh
cd /home/ubuntu/ln-lean-repair
grep -nE '\b(sorry|axiom|admit|native_decide|unsafe|implemented_by)\b' \
  LnLean/Channel/Commitment.lean \
  LnLean/Proofs/Channel/CommitmentConsumerTargets.lean
```

Observed output:

```text
NO_FORBIDDEN_TOKENS
```

## 6. Scope caveats

- Script execution, signatures, witnesses, sighash bytes, and consensus
  validity are out of scope.  The coverage theorem is about the output list a
  consumer reads; it does **not** claim a digest is preserved under a different
  output order.  D12's `waveD_d12_output_ordering_fails` remains the refutation
  of that reading.
- `CommitmentHTLCOutput.netAmountSat` is caller-supplied.  The BOLT 3 identity
  `net + second_stage_fee = gross` remains the explicit
  `NetConsistentOnRecords` / `NetConsistent` hypothesis from wave 5/6.
- The refinement is a `List.Perm`, not list equality: the rich model sorts and
  the legacy consumer list does not (D12).  On a record already in the survivor
  normal form and using the record net projection, the migrated consumer list
  *is* the original legacy list
  (`migratedConsumerOutputs_eq_consumerOutputs_of_migrated`).
- The normal-form/no-trim premise is necessary:
  `legacyCoverage_not_preserved_by_net_migration` shows a one-signature message
  covering the nominal 500-sat HTLC demo commitment but not the net-migrated
  record at dust 1000.
- `migratedConsumerOutputs_eq_consumerOutputs_of_migrated` requires
  `tx.UsesRecordNet`.  This is not removable: `tx.Migrated` is stated with the
  transaction projection `tx.netAmountSat`, while `migrateNet` filters on the
  record field `CommitmentHTLCOutput.netAmountSat`.  For `migrateNet` results
  the condition holds definitionally; for a caller-supplied custom projection
  it is the explicit compatibility hypothesis.
- `CommitmentTx.ofCommitment` does not invent dust limits or scripts; the
  construction site supplies them, so no existing producer is silently
  changed.
- No cross-implementation or consensus-level check is claimed.

## 7. Downstream construction sites

### 7.1 No edit required for the delivered results

All constructions in this lane are additive.  The following downstream sites
compile unchanged and can opt in:

- `LnLean/Proofs/ProtocolCoverageTargets.lean`:
  `CoversHtlcOutputs m c := m.htlcSignatures.length =
  htlcOutputCount c.commitmentOutputs`.  The migrated predicate is the same
  formula on `tx.migratedConsumerOutputs`; the bridge is
  `coversMigratedOutputs_iff_legacyRecord`.
- `LnLean/Proofs/ProtocolWireTargets.lean`:
  `SignedState.toCommitment` and `commitmentSignedFullOfState` can be wrapped
  with `CommitmentTx.ofCommitment`; no field or proof change is needed for the
  gross = net path.
- `LnLean/Proofs/Channel/CommitmentIntegrationTargets.lean` and
  `CommitmentOrderTargets.lean`: the gross `outputs`/`legacyOutputs` consumers
  keep their existing signatures; the new net path is opt-in via
  `migrateForConsumer`.

### 7.2 Proposed sighash-consumer theorem (not compiled in this lane)

The actual sighash consumer is `SighashTargets.viewOfState`, whose
`viewOfState_outputs` lemma reads `st.toCommitment.commitmentOutputs`.  The
following theorem is the exact boundary adapter.  It is recorded as an
integration step instead of being imported because wave-7 lane
`S7-PR-PREIMAGE` is editing `SighashTargets.lean`, and its current import
closure (`WaveE.E20` → `Protocol.Handshake`) is temporarily unbuildable in this
shared worktree.  The theorem is purely additive; no edit to
`SighashTargets.lean` is required.

```lean
import LnLean.Proofs.Channel.CommitmentConsumerTargets
import LnLean.Proofs.Channel.SighashTargets

open LnLean LnLean.Channel LnLean.Proofs.Channel
open LnLean.Proofs.Channel.SighashTargets
open LnLean.Proofs.Channel.CommitmentConsumer

theorem viewOfState_outputs_refines_netConsumerOutputs
    (ctx : SighashContext) (st : SignedState) (tx : CommitmentTx)
    (hst : st.toCommitment = tx.commitment)
    (hnet : tx.UsesRecordNet) (hm : tx.Migrated)
    (hdust : 0 < tx.dustLimitSat) :
    (tx.netConsumerOutputs.map CommitmentTxOutput.toCommitmentOutput).Perm
      (viewOfState ctx st).outputs := by
  rw [viewOfState_outputs, ← hst]
  have hperm := netConsumerOutputs_perm_migratedConsumerOutputs tx hdust
  rw [migratedConsumerOutputs_eq_consumerOutputs_of_migrated tx hnet hm hdust]
    at hperm
  simpa [consumerOutputs_eq_commitmentOutputs] using hperm

theorem viewOfState_outputs_refines_netConsumerOutputs_of_no_trim
    (ctx : SighashContext) (st : SignedState) (tx : CommitmentTx)
    (hst : st.toCommitment = tx.commitment)
    (hnet : tx.UsesRecordNet) (hdust : 0 < tx.dustLimitSat)
    (hl : tx.dustLimitSat ≤ tx.commitment.toLocalSat)
    (hr : tx.dustLimitSat ≤ tx.commitment.toRemoteSat)
    (hh : ∀ h ∈ tx.commitment.htlcs,
      tx.dustLimitSat ≤ tx.netAmountSat h) :
    (tx.netConsumerOutputs.map CommitmentTxOutput.toCommitmentOutput).Perm
      (viewOfState ctx st).outputs :=
  viewOfState_outputs_refines_netConsumerOutputs ctx st tx hst hnet
    (migrated_of_no_trim tx hdust hl hr hh) hdust
```

### 7.3 Optional `ProtocolWireTargets` net-field patch

If the parent wants `SignedState.toCommitment` itself to carry BOLT 3 net
values (rather than passing a `CommitmentTx` with an explicit net projection),
the minimal downstream patch is:

```lean
-- LnLean/Proofs/ProtocolWireTargets.lean
structure SignedHtlc where
  htlcId : Nat
  amount : Msat
  paymentHash : PaymentHash
  direction : Direction
  htlcState : HTLCState
  cltvExpiry : Height
  signedDataDigest : ByteArray
  /-- BOLT 3 net (post-second-stage-fee) value; default keeps gross = net. -/
  netAmountSat : Nat := amount.toSatFloor

def SignedHtlc.toCommitmentHtlcOutput (h : SignedHtlc) :
    CommitmentHTLCOutput where
  direction := h.direction
  amountSat := h.amount.toSatFloor
  cltvExpiry := h.cltvExpiry
  state := h.htlcState
  netAmountSat := h.netAmountSat
```

`SignedState` needs no dust/script fields: `CommitmentTx.ofCommitment` supplies
them at the construction site.  If the full wire record must carry net values,
`LnLean/Protocol/Messages.lean` would need the same additive
`SignedHtlcEntry.netAmountSat` field and copy in
`SignedHtlcEntry.toCommitmentHtlcOutput`; that is a separate, coordinated
wire-record change (PR-02), not required for this lane.

## 8. Integration steps (parent only)

1. Add `import LnLean.Proofs.Channel.CommitmentConsumerTargets` to the root
   import module (or the aggregate proof module).
2. Register the `CH-01` targets in `LnLean/Proofs/Obligations.lean` and
   `LnLean/Proofs/Traceability.lean`.  Suggested target string:
   `LnLean.Channel.CommitmentTx.migratedFrom_outputsNet_perm_commitmentOutputs;
    LnLean.Proofs.Channel.CommitmentConsumer.netConsumerOutputs_perm_migratedConsumerOutputs;
    LnLean.Proofs.Channel.CommitmentConsumer.coversMigratedOutputs_iff_legacy_of_migrated`.
3. Add the headline theorems to `LnLean/Proofs/PhaseC3/AxiomAudit.lean` (the
   list in §4 is ready).
4. Update `docs/OPEN-ISSUES.md`:
   - `CH-01`: `open (mitigated)` → `closed (consumer path)`, citing
     `CommitmentTx.consumerOutputs`, `CommitmentTx.migrateForConsumer`,
     `netConsumerOutputs_perm_migratedConsumerOutputs`, and
     `coversMigratedOutputs_iff_legacy_of_migrated`.
   - `CH-02`: keep closed; note this lane proves the consumer boundary on top
     of the wave-6 record layer.
   - `CH-03`: keep the `trimmedTotalSat` naming decision of §1.1 (no rename).
5. Optionally add the §7.2 adapter theorems after `S7-PR-PREIMAGE` integrates
   and `SighashTargets.lean` builds cleanly again.
6. Do not apply the §1.1 rename or the §7.3 patch unless a maintainer decides
   the catalog needs the literal field name / full net-aware `SignedState`.

## 9. Blockers

- **Full-tree build not claimed.**  The required lane build is green (24
  jobs).  A full `lake build` was not run, as required by lane policy.
- **Shared-worktree interference (transient).**  At lane build time,
  `LnLean/Protocol/Handshake.lean` was modified by another wave-7 lane and its
  proofs did not compile (`canSendAccept`/`canRecvAccept` conjunction shape).
  `SighashTargets.lean` is also being edited by `S7-PR-PREIMAGE`.  This lane
  therefore deliberately imports only
  `Commitment`, `CommitmentTypesTargets`, `Protocol.Messages`, and
  `CommitmentTxProps`; it does not depend on the currently unstable
  `SighashTargets` import closure.  The sighash adapter is recorded in §7.2.
- **No structural blocker in this lane.**  No downstream construction site
  needs an edit for the delivered results.
