# S6-CH-TYPES — gross/net record fields and the canonical field-boundary refinement

- Lane: `S6-CH-TYPES` (issues `CH-04`, `CH-03`)
- Branch: `repair/integrated`
- Launch commit: `201a0a0` (wave 6 launch)
- Owned files:
  - `LnLean/Channel/Types.lean` (core record patch)
  - `LnLean/Channel/Commitment.lean` (computed net/trim path, migrations)
  - `LnLean/Proofs/Channel/CommitmentTypesTargets.lean` (new)
  - `agents/reports/swarm6/S6-CH-TYPES.md` (this report)

Read-only files consulted: `docs/OPEN-ISSUES.md`,
`agents/swarm/WAVE-6.md`, `docs/ASSUMPTIONS.md`,
`agents/reports/swarm5/S5-CH-GROSSNET.md`, `LnLean/Proofs/WaveD/D12.lean`,
`LnLean/Proofs/Channel/CommitmentIntegrationTargets.lean`,
`LnLean/Proofs/Channel/CommitmentOrderTargets.lean`,
`LnLean/Proofs/Channel/CommitmentGrossNetTargets.lean`,
`LnLean/Channel/HTLC.lean`.

## 1. Result

The BOLT 3 gross/net record-field patch is now in the owned core types:

- `CommitmentHTLCOutput.amountSat` is documented and treated as the **gross**
  commitment output value; the new field
  `CommitmentHTLCOutput.netAmountSat : Nat := amountSat` is the **net**
  second-stage value used by the dust test.
- `Commitment.trimmedTotalSat : Nat := 0` records the gross value removed by
  trimming and added to the commitment fee.
- `CommitmentTx.netAmountSat` now defaults to
  `fun h => h.netAmountSat`, so the canonical net path
  `CommitmentTx.htlcOutputNet` / `CommitmentTx.outputsNet` reads the record
  field directly instead of a transaction-level override.
- `Commitment.migrateNet` and `CommitmentTx.migrateNet` construct the BOLT 3
  migrated record at the new boundary: below-dust non-HTLC outputs are zeroed,
  HTLCs are filtered by `netAmountSat`, and the removed gross value is stored in
  both `Commitment.trimmedTotalSat` and `CommitmentTx.trimmedSat`.
- The canonical refinement is proved at the field boundary:
  `CommitmentTx.migrateNet_outputsNet_perm_commitmentOutputs` shows the sorted
  net output list is a permutation of the legacy consumer path
  `Commitment.commitmentOutputs`, for arbitrary dust limit and protocol-valid
  `0 < dustLimitSat`.
- Exact accounting is proved:
  emitted + base fee + stored trimmed = funding, and
  effective fee = base fee + stored trimmed.

D12's refutations and the wave-4/wave-5 results are imported and restated; none
is weakened. The legacy gross path (`CommitmentTx.htlcOutput`,
`CommitmentTx.outputs`, `Commitment.commitmentOutputs`) is retained byte-for-byte
in signature and semantics, so the wave-4/wave-5 consumers keep compiling.

### 1.1 Field-name decision (important integration note)

`Commitment.trimmedSat` was already the **computed** nominal trim function in
`Commitment.lean`, introduced by wave 5. A structure field cannot share that
name, and the unowned wave-5 module
`LnLean/Proofs/Channel/CommitmentGrossNetTargets.lean` consumes
`Commitment.trimmedSat` as a three-argument function. Since that file is outside
this lane's ownership and is part of the required build, the stored field is
named `Commitment.trimmedTotalSat` (the second option recorded in
`S5-CH-GROSSNET.md` §9), and the computed function is kept unchanged.

`Commitment.trimmedValueFor` is added as the future-facing alias. The final
rename to the literal names (`Commitment.trimmedSat` field and
`Commitment.trimmedValueFor` computed function) requires the coordinated patch
in §8.2.

## 2. Required build

Command run exactly as specified, under `flock`:

```sh
cd /home/ubuntu/ln-lean-repair
export PATH=/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Channel.Types LnLean.Channel.Commitment \
    LnLean.Proofs.Channel.CommitmentTypesTargets \
    LnLean.Proofs.Channel.CommitmentGrossNetTargets
```

Observed output:

```text
Build completed successfully (21 jobs).
```

**Build RC: 0.** No warnings were emitted. No full `lake build`,
`collect-obligations.py`, `collect-anchors.py`, or Git write was run.

## 3. Exact signatures

### 3.1 `LnLean/Channel/Types.lean`

```lean
structure CommitmentHTLCOutput where
  direction : Direction
  /-- Gross value carried by the commitment output (`amount_msat / 1000`). -/
  amountSat : Nat
  cltvExpiry : Height
  state : HTLCState
  /-- Net second-stage value; the default is the legacy identity projection. -/
  netAmountSat : Nat := amountSat
deriving Repr, DecidableEq, BEq

structure Commitment where
  holder : Direction
  commitmentNumber : Nat
  fundingValueSat : Nat
  toLocalSat : Nat
  toRemoteSat : Nat
  htlcs : List CommitmentHTLCOutput
  feeSat : Nat
  contestDelay : Nat
  anchorOutputs : Bool
  /-- Gross value removed by trimming and added to the commitment fee. -/
  trimmedTotalSat : Nat := 0
deriving Repr, DecidableEq, BEq
```

Both fields are appended after the existing fields with defaults that refer only
to earlier fields, so every named record literal and every `{ x with ... }`
update in the tree elaborates unchanged. There are no positional
`CommitmentHTLCOutput.mk`/`Commitment.mk` uses in the tree.

### 3.2 `LnLean/Channel/Commitment.lean` (new core API)

```lean
def Commitment.trimmedValueFor (c : Commitment) (dustLimitSat : Nat)
    (netAmountSat : CommitmentHTLCOutput → Nat) : Nat :=
  c.trimmedSat dustLimitSat netAmountSat

theorem Commitment.trimmedValueFor_eq_trimmedSat (c : Commitment)
    (dustLimitSat : Nat) (netAmountSat : CommitmentHTLCOutput → Nat) :
    c.trimmedValueFor dustLimitSat netAmountSat =
      c.trimmedSat dustLimitSat netAmountSat

def CommitmentHTLCOutput.keepAtDust (dustLimitSat : Nat)
    (h : CommitmentHTLCOutput) : Bool :=
  decide (dustLimitSat ≤ h.netAmountSat)

theorem CommitmentHTLCOutput.keepAtDust_eq_true_iff
    {dustLimitSat : Nat} {h : CommitmentHTLCOutput} :
    h.keepAtDust dustLimitSat = true ↔ dustLimitSat ≤ h.netAmountSat

theorem CommitmentHTLCOutput.keepAtDust_eq_false_iff
    {dustLimitSat : Nat} {h : CommitmentHTLCOutput} :
    h.keepAtDust dustLimitSat = false ↔ ¬ dustLimitSat ≤ h.netAmountSat

def CommitmentHTLCOutput.withNet (h : CommitmentHTLCOutput)
    (netAmountSat : Nat) : CommitmentHTLCOutput

theorem CommitmentHTLCOutput.withNet_netAmountSat
    (h : CommitmentHTLCOutput) (netAmountSat : Nat) :
    (h.withNet netAmountSat).netAmountSat = netAmountSat

theorem CommitmentHTLCOutput.withNet_amountSat
    (h : CommitmentHTLCOutput) (netAmountSat : Nat) :
    (h.withNet netAmountSat).amountSat = h.amountSat

theorem CommitmentHTLCOutput.withNet_amountSat_self
    (h : CommitmentHTLCOutput) :
    (h.withNet h.amountSat).netAmountSat = h.amountSat

def Commitment.migrateNet (c : Commitment) (dustLimitSat : Nat) :
    Commitment :=
  { c with
    toLocalSat := if dustLimitSat ≤ c.toLocalSat then c.toLocalSat else 0
    toRemoteSat := if dustLimitSat ≤ c.toRemoteSat then c.toRemoteSat else 0
    htlcs := c.htlcs.filter (fun h => h.keepAtDust dustLimitSat)
    trimmedTotalSat := c.trimmedSat dustLimitSat (fun h => h.netAmountSat) }

theorem Commitment.migrateNet_feeSat (c : Commitment) (dustLimitSat : Nat) :
    (c.migrateNet dustLimitSat).feeSat = c.feeSat

theorem Commitment.migrateNet_fundingValueSat (c : Commitment)
    (dustLimitSat : Nat) :
    (c.migrateNet dustLimitSat).fundingValueSat = c.fundingValueSat

theorem Commitment.migrateNet_htlcs (c : Commitment) (dustLimitSat : Nat) :
    (c.migrateNet dustLimitSat).htlcs =
      c.htlcs.filter (fun h => h.keepAtDust dustLimitSat)

theorem Commitment.migrateNet_trimmedTotalSat (c : Commitment)
    (dustLimitSat : Nat) :
    (c.migrateNet dustLimitSat).trimmedTotalSat =
      c.trimmedSat dustLimitSat (fun h => h.netAmountSat)
```

`CommitmentTx` field change:

```lean
  netAmountSat : CommitmentHTLCOutput → Nat := fun h => h.netAmountSat
```

New `CommitmentTx` API:

```lean
def CommitmentTx.UsesRecordNet (tx : CommitmentTx) : Prop :=
  ∀ h : CommitmentHTLCOutput, tx.netAmountSat h = h.netAmountSat

theorem CommitmentTx.usesRecordNet_default (tx : CommitmentTx) :
    ({ tx with netAmountSat := fun h => h.netAmountSat }).UsesRecordNet

def CommitmentTx.recordTrimmedValue (tx : CommitmentTx) : Nat :=
  tx.commitment.trimmedSat tx.dustLimitSat (fun h => h.netAmountSat)

theorem CommitmentTx.recordTrimmedValue_eq_trimmedValueFor
    (tx : CommitmentTx) :
    tx.recordTrimmedValue =
      tx.commitment.trimmedValueFor tx.dustLimitSat
        (fun h => h.netAmountSat)

def CommitmentTx.migrateNet (tx : CommitmentTx) : CommitmentTx :=
  { tx with
    commitment := tx.commitment.migrateNet tx.dustLimitSat
    netAmountSat := fun h => h.netAmountSat
    trimmedSat := tx.recordTrimmedValue }

theorem CommitmentTx.migrateNet_commitment (tx : CommitmentTx) :
    (tx.migrateNet).commitment =
      tx.commitment.migrateNet tx.dustLimitSat

theorem CommitmentTx.migrateNet_netAmountSat (tx : CommitmentTx)
    (h : CommitmentHTLCOutput) :
    (tx.migrateNet).netAmountSat h = h.netAmountSat

theorem CommitmentTx.migrateNet_usesRecordNet (tx : CommitmentTx) :
    (tx.migrateNet).UsesRecordNet

theorem CommitmentTx.migrateNet_trimmedSat (tx : CommitmentTx) :
    (tx.migrateNet).trimmedSat = tx.recordTrimmedValue

theorem CommitmentTx.migrateNet_htlcs (tx : CommitmentTx) :
    (tx.migrateNet).commitment.htlcs =
      tx.commitment.htlcs.filter
        (fun h => h.keepAtDust tx.dustLimitSat)

theorem CommitmentTx.migrateNet_commitment_trimmedTotalSat
    (tx : CommitmentTx) :
    (tx.migrateNet).commitment.trimmedTotalSat = tx.recordTrimmedValue
```

### 3.3 `LnLean/Proofs/Channel/CommitmentTypesTargets.lean`

Namespace: `LnLean.Proofs.Channel.CommitmentTypes`.

Default and construction-site compatibility:

```lean
theorem CommitmentHTLCOutput.netAmountSat_default
    (direction : Direction) (amountSat : Nat) (cltvExpiry : Height)
    (state : HTLCState) :
    ({ direction := direction, amountSat := amountSat,
       cltvExpiry := cltvExpiry, state := state } :
      CommitmentHTLCOutput).netAmountSat = amountSat

theorem Commitment.trimmedTotalSat_default
    (holder : Direction) (number funding toLocal toRemote fee contestDelay : Nat)
    (htlcs : List CommitmentHTLCOutput) (anchors : Bool) :
    ({ holder := holder, commitmentNumber := number,
       fundingValueSat := funding, toLocalSat := toLocal,
       toRemoteSat := toRemote, htlcs := htlcs, feeSat := fee,
       contestDelay := contestDelay, anchorOutputs := anchors } :
      Commitment).trimmedTotalSat = 0

theorem zeroHtlcCommitment_trimmedTotalSat ... :
    (zeroHtlcCommitment ...).trimmedTotalSat = 0

theorem commitmentPairOfBalances_trimmedTotalSat ... :
    (commitmentPairOfBalances ...).localCommitment.trimmedTotalSat = 0 ∧
      (commitmentPairOfBalances ...).remoteCommitment.trimmedTotalSat = 0

theorem legacyHtlcOutput_netAmountSat (h : HTLCRecord) :
    (CommitmentIntegration.legacyHtlcOutput h).netAmountSat =
      (CommitmentIntegration.legacyHtlcOutput h).amountSat

theorem netHtlcOutput_netAmountSat (t s : Nat) (h : HTLCRecord) :
    (CommitmentIntegration.netHtlcOutput t s h).netAmountSat =
      (CommitmentIntegration.netHtlcOutput t s h).amountSat
```

Net dust test at the record boundary:

```lean
theorem CommitmentTx.htlcOutput_gross_retained (tx : CommitmentTx)
    (h : CommitmentHTLCOutput) :
    tx.htlcOutput h =
      (if tx.dustLimitSat ≤ h.amountSat then
        some (CommitmentTxOutput.htlc h (tx.htlcScript h)) else none)

theorem CommitmentTx.htlcOutputNet_eq_recordNet {tx : CommitmentTx}
    (hnet : tx.UsesRecordNet) (h : CommitmentHTLCOutput) :
    tx.htlcOutputNet h =
      (if tx.dustLimitSat ≤ h.netAmountSat then
        some (CommitmentTxOutput.htlc h (tx.htlcScript h)) else none)

theorem CommitmentTx.htlcOutputNet_eq_none_iff_recordNet
    {tx : CommitmentTx} (hnet : tx.UsesRecordNet)
    (h : CommitmentHTLCOutput) :
    tx.htlcOutputNet h = none ↔ h.netAmountSat < tx.dustLimitSat

theorem CommitmentTx.htlcOutputNet_isSome_iff_recordNet
    {tx : CommitmentTx} (hnet : tx.UsesRecordNet)
    (h : CommitmentHTLCOutput) :
    (tx.htlcOutputNet h).isSome = true ↔
      tx.dustLimitSat ≤ h.netAmountSat

theorem CommitmentHTLCOutput.net_lt_dust_iff_gross_lt_threshold
    {h : CommitmentHTLCOutput} {dustLimitSat feeSat : Nat}
    (hnet : h.netAmountSat + feeSat = h.amountSat) :
    h.netAmountSat < dustLimitSat ↔
      h.amountSat < dustLimitSat + feeSat

theorem CommitmentHTLCOutput.not_dust_of_threshold_eq
    {h : CommitmentHTLCOutput} {dustLimitSat feeSat : Nat}
    (hnet : h.netAmountSat + feeSat = h.amountSat)
    (heq : h.amountSat = dustLimitSat + feeSat) :
    dustLimitSat ≤ h.netAmountSat
```

Record-level accounting:

```lean
theorem Commitment.migrateNet_totalOutputValue_add_trimmedTotalSat
    (c : Commitment) (dustLimitSat : Nat) :
    (c.migrateNet dustLimitSat).totalOutputValue +
        (c.migrateNet dustLimitSat).trimmedTotalSat =
      c.totalOutputValue

theorem Commitment.migrateNet_conservation (c : Commitment)
    (dustLimitSat : Nat)
    (hbal : c.totalOutputValue + c.feeSat = c.fundingValueSat) :
    (c.migrateNet dustLimitSat).totalOutputValue +
        (c.migrateNet dustLimitSat).feeSat +
        (c.migrateNet dustLimitSat).trimmedTotalSat =
      c.fundingValueSat

theorem Commitment.migrateNet_effectiveFee_eq (c : Commitment)
    (dustLimitSat : Nat)
    (hbal : c.totalOutputValue + c.feeSat = c.fundingValueSat) :
    (c.migrateNet dustLimitSat).effectiveFeeSat =
      c.feeSat + (c.migrateNet dustLimitSat).trimmedTotalSat

theorem Commitment.migrateNet_effectiveFee_val (c : Commitment)
    (dustLimitSat : Nat) :
    (c.migrateNet dustLimitSat).effectiveFeeSat =
      c.fundingValueSat - (c.migrateNet dustLimitSat).totalOutputValue

theorem Commitment.effectiveFee_eq_feeSat_add_trimmedTotalSat
    (c : Commitment)
    (h : c.totalOutputValue + c.feeSat + c.trimmedTotalSat =
      c.fundingValueSat) :
    c.effectiveFeeSat = c.feeSat + c.trimmedTotalSat

theorem Commitment.migrateNet_trimmedTotalSat_eq_trimmedSat
    (c : Commitment) (dustLimitSat : Nat) :
    (c.migrateNet dustLimitSat).trimmedTotalSat =
      c.trimmedSat dustLimitSat (fun h => h.netAmountSat)

theorem Commitment.migrateNet_trimmedTotalSat_eq_trimmedValueFor
    (c : Commitment) (dustLimitSat : Nat) :
    (c.migrateNet dustLimitSat).trimmedTotalSat =
      c.trimmedValueFor dustLimitSat (fun h => h.netAmountSat)

theorem Commitment.migrateNet_htlc_survives (c : Commitment)
    (dustLimitSat : Nat) {h : CommitmentHTLCOutput}
    (hmem : h ∈ (c.migrateNet dustLimitSat).htlcs) :
    dustLimitSat ≤ h.netAmountSat
```

Transaction-level migration and refinement:

```lean
theorem CommitmentTx.migrateNet_migrated (tx : CommitmentTx)
    (hdust : 0 < tx.dustLimitSat) : (tx.migrateNet).Migrated

theorem CommitmentTx.migrateNet_htlc_survives (tx : CommitmentTx)
    {h : CommitmentHTLCOutput}
    (hmem : h ∈ (tx.migrateNet).commitment.htlcs) :
    tx.dustLimitSat ≤ h.netAmountSat

theorem CommitmentTx.migrateNet_trimmedSat_eq_commitment_trimmedTotalSat
    (tx : CommitmentTx) :
    (tx.migrateNet).trimmedSat =
      (tx.migrateNet).commitment.trimmedTotalSat

theorem CommitmentTx.migrateNet_trimmedSat_eq_trimmedValueFor
    (tx : CommitmentTx) :
    (tx.migrateNet).trimmedSat =
      tx.commitment.trimmedValueFor tx.dustLimitSat
        (fun h => h.netAmountSat)

theorem CommitmentTx.migrateNet_totalOutputValue_add_trimmedSat
    (tx : CommitmentTx) :
    (tx.migrateNet).commitment.totalOutputValue +
        (tx.migrateNet).trimmedSat =
      tx.commitment.totalOutputValue

theorem CommitmentTx.migrateNet_conservation (tx : CommitmentTx)
    (hbal : tx.commitment.totalOutputValue + tx.commitment.feeSat =
      tx.commitment.fundingValueSat) :
    (tx.migrateNet).commitment.totalOutputValue +
        (tx.migrateNet).commitment.feeSat +
        (tx.migrateNet).trimmedSat =
      tx.commitment.fundingValueSat

theorem CommitmentTx.migrateNet_effectiveFee_eq (tx : CommitmentTx)
    (hbal : tx.commitment.totalOutputValue + tx.commitment.feeSat =
      tx.commitment.fundingValueSat) :
    (tx.migrateNet).commitment.effectiveFeeSat =
      (tx.migrateNet).commitment.feeSat + (tx.migrateNet).trimmedSat

theorem CommitmentTx.migrateNet_outputsNet_perm_canonicalOutputs
    (tx : CommitmentTx) :
    ((tx.migrateNet).outputsNet.map
        CommitmentTxOutput.toCommitmentOutput).Perm
      (tx.migrateNet).canonicalOutputs

theorem CommitmentTx.migrateNet_outputsNet_perm_commitmentOutputs
    (tx : CommitmentTx) (hdust : 0 < tx.dustLimitSat) :
    ((tx.migrateNet).outputsNet.map
        CommitmentTxOutput.toCommitmentOutput).Perm
      (tx.migrateNet).commitment.commitmentOutputs

theorem CommitmentTx.migrateNet_canonicalOutputs_eq_commitmentOutputs
    (tx : CommitmentTx) (hdust : 0 < tx.dustLimitSat) :
    (tx.migrateNet).canonicalOutputs =
      (tx.migrateNet).commitment.commitmentOutputs

theorem CommitmentTx.migrateNet_htlcOutputNet_eq_none_iff
    (tx : CommitmentTx) (h : CommitmentHTLCOutput) :
    (tx.migrateNet).htlcOutputNet h = none ↔
      h.netAmountSat < tx.dustLimitSat
```

BOLT 3 fee-schedule bridge:

```lean
def NetConsistentOnRecords (c : Commitment) (anchors : Bool)
    (r : FeeRate) : Prop :=
  ∀ h ∈ c.htlcs,
    h.netAmountSat + CommitmentGrossNet.htlcSecondStageFee anchors r h =
      h.amountSat

theorem CommitmentTx.netConsistent_migrateNet {tx : CommitmentTx}
    {anchors : Bool} {r : FeeRate}
    (hc : NetConsistentOnRecords tx.commitment anchors r) :
    CommitmentGrossNet.NetConsistent (tx.migrateNet) anchors r

theorem CommitmentTx.migrateNet_trims_iff_gross_threshold
    (tx : CommitmentTx) {anchors : Bool} {r : FeeRate}
    (hc : NetConsistentOnRecords tx.commitment anchors r)
    {h : CommitmentHTLCOutput}
    (hmem : h ∈ (tx.migrateNet).commitment.htlcs) :
    (tx.migrateNet).htlcOutputNet h = none ↔
      h.amountSat < tx.dustLimitSat +
        CommitmentGrossNet.htlcSecondStageFee anchors r h
```

Preserved results:

```lean
theorem d12_output_ordering_fails_retained : ...
theorem d12_zero_value_htlc_emitted_retained : ...
theorem wave5_migratedFrom_outputsNet_perm_commitmentOutputs_retained
    (tx : CommitmentTx) (hdust : 0 < tx.dustLimitSat) : ...
theorem wave4_dust_trimming_not_perm_retained : ...
```

## 4. Axiom audit

Scratch file `/tmp/opencode/AuditTypes.lean` (not committed) ran `#print axioms`
on all headline results. Summary:

```text
no axioms:      netAmountSat_default, trimmedTotalSat_default,
                zeroHtlcCommitment_trimmedTotalSat,
                commitmentPairOfBalances_trimmedTotalSat,
                legacyHtlcOutput_netAmountSat, netHtlcOutput_netAmountSat,
                htlcOutput_gross_retained, htlcOutputNet_eq_recordNet,
                migrateNet_trimmedSat_eq_commitment_trimmedTotalSat,
                migrateNet_trimmedSat_eq_trimmedValueFor,
                migrateNet_trimmedTotalSat_eq_trimmedSat,
                migrateNet_trimmedTotalSat_eq_trimmedValueFor
propext only:   htlcOutputNet_isSome_iff_recordNet,
                migrateNet_htlc_survives, netConsistent_migrateNet
propext, Quot.sound:
                htlcOutputNet_eq_none_iff_recordNet,
                not_dust_of_threshold_eq,
                migrateNet_totalOutputValue_add_trimmedTotalSat,
                migrateNet_conservation, migrateNet_effectiveFee_eq,
                effectiveFee_eq_feeSat_add_trimmedTotalSat,
                migrateNet_migrated, migrateNet_totalOutputValue_add_trimmedSat,
                migrateNet_conservation (tx), migrateNet_effectiveFee_eq (tx),
                migrateNet_outputsNet_perm_canonicalOutputs,
                migrateNet_outputsNet_perm_commitmentOutputs,
                migrateNet_canonicalOutputs_eq_commitmentOutputs,
                migrateNet_htlcOutputNet_eq_none_iff,
                migrateNet_trims_iff_gross_threshold,
                d12_output_ordering_fails_retained,
                wave5_..._retained, wave4_..._retained
propext, Classical.choice, Quot.sound:
                net_lt_dust_iff_gross_lt_threshold
```

No theorem depends on `sorryAx`, a user axiom, or any axiom outside
`{propext, Quot.sound, Classical.choice}`. `Classical.choice` appears only
through `omega`, as in the wave-5 audit.

## 5. Forbidden-construct scan

```sh
cd /home/ubuntu/ln-lean-repair
grep -nE '\b(sorry|axiom|admit|native_decide|unsafe|implemented_by)\b' \
  LnLean/Channel/Types.lean \
  LnLean/Channel/Commitment.lean \
  LnLean/Proofs/Channel/CommitmentTypesTargets.lean
```

Observed output:

```text
NO_FORBIDDEN_TOKENS
```

## 6. Scope caveats

- Script execution, signatures, witnesses, sighash, and consensus validity are
  out of scope; scripts remain caller-supplied `CommitmentTx` fields.
- `CommitmentHTLCOutput.netAmountSat` is caller-supplied. The BOLT 3 identity
  `net + second_stage_fee = gross` is the explicit hypothesis
  `NetConsistentOnRecords` (or `CommitmentGrossNet.NetConsistent` at the
  `CommitmentTx` level); it is not derived from a fee schedule.
- The legacy dust test `CommitmentTx.htlcOutput` and its `CommitmentTx.outputs`
  path remain **gross** (`amountSat`) for compatibility. The canonical net test
  is `CommitmentTx.htlcOutputNet` on a `UsesRecordNet` transaction (in
  particular on `migrateNet`/`migratedFrom`). Changing the legacy path to net
  would falsify the wave-4 trimming-preservation theorem
  `CommitmentIntegration.legacyOutputs_sum_add_trimmedValue`, whose
  `trimmedValue` is gross-based; the wave-6 patch therefore does not silently
  change that consumer.
- The refinement is a `List.Perm`, not list equality: the rich model sorts and
  `Commitment.commitmentOutputs` does not (D12).
- `CommitmentTx.migrateNet_migrated` and the canonical permutation require
  `0 < dustLimitSat`, as in wave 5; BOLT 2 requires
  `dust_limit_satoshis >= 354` (`02-peer-protocol.md:870`), so this is the
  protocol domain, not a workaround. The value-accounting theorems do not need
  positivity.
- The stored field is `trimmedTotalSat`, not the literal `trimmedSat`; see
  §1.1 and §8.2.
- No cross-implementation or consensus-level check is claimed.

## 7. Construction-site migration

### 7.1 Owned construction sites (all compile with defaults)

No owned `Commitment`/`CommitmentHTLCOutput` literal had to change:

- `zeroHtlcCommitment` and `commitmentPairOfBalances` in
  `LnLean/Channel/Commitment.lean` use named literals, so
  `trimmedTotalSat` defaults to `0`; proved by
  `zeroHtlcCommitment_trimmedTotalSat` and
  `commitmentPairOfBalances_trimmedTotalSat`.
- The rich `CommitmentTx` literals in wave-4/wave-5 modules omit
  `netAmountSat`; `CommitmentTx.netAmountSat` now delegates to the record
  field, whose default is `amountSat`, so their gross-equals-net semantics is
  unchanged. `legacyHtlcOutput_netAmountSat` and
  `netHtlcOutput_netAmountSat` record this for the two downstream producers.
- D12's `mkHtlcOutput` (unowned) also relies on the default; its
  counterexamples remain imported and are restated.

### 7.2 Construction sites outside ownership that need no change

- `CommitmentIntegrationTargets.dustDemoTx` — `CommitmentTx` literal; defaults
  preserve it.
- `CommitmentGrossNetTargets.migratedFrom` — `CommitmentTx` update; preserves
  `netAmountSat`, which now defaults to the record field.
- `CommitmentOrderTargets` — uses the retained gross `htlcOutput`/`outputs`
  path; unchanged.
- `D12.mkHtlcOutput`, `D47.CommitmentHTLCOutput.ofHTLC`,
  `ProtocolWireTargets.toCommitmentHtlcOutput`,
  `Protocol/Messages.lean` — named literals; `netAmountSat` defaults to
  `amountSat`.

## 8. Integration steps and required parent patches

### 8.1 Wiring (parent only)

1. Add `import LnLean.Proofs.Channel.CommitmentTypesTargets` to `LnLean.lean`
   (or the aggregate proof module).
2. Register the new CH-03/CH-04 targets in
   `LnLean/Proofs/Obligations.lean` and
   `LnLean/Proofs/Traceability.lean`.
3. Add the headline theorems to
   `LnLean/Proofs/PhaseC3/AxiomAudit.lean` (the list in §4 is ready).
4. Update `docs/OPEN-ISSUES.md` rows `CH-03`/`CH-04` with the field names and
   theorem names, keeping the rename note of §8.2 if the literal
   `Commitment.trimmedSat` field is required.
5. Optionally refresh the wave-5 header of
   `LnLean/Proofs/Channel/CommitmentGrossNetTargets.lean` (lines 43-49), which
   still says the `Types.lean` fields are an unapplied patch. It is a comment
   only and outside this lane's ownership.

### 8.2 Optional literal-name rename (needs a coordinated patch)

If the catalog requires the stored field to be named exactly
`Commitment.trimmedSat`:

1. In `LnLean/Channel/Types.lean`, rename `Commitment.trimmedTotalSat` to
   `Commitment.trimmedSat`.
2. In `LnLean/Channel/Commitment.lean`, rename the computed
   `Commitment.trimmedSat` to `Commitment.trimmedValueFor` and delete the
   alias; update `CommitmentTx.trimmedValue`, `recordTrimmedValue`,
   `Commitment.migrateNet`, and all doc references.
3. In the unowned
   `LnLean/Proofs/Channel/CommitmentGrossNetTargets.lean`, update the two
   function uses:
   - line 593 (`unfold ... Commitment.trimmedSat`) → `Commitment.trimmedValueFor`;
   - line 640 (`tx.commitment.trimmedSat tx.dustLimitSat tx.netAmountSat`) →
     `tx.commitment.trimmedValueFor ...`.
4. In `LnLean/Proofs/Channel/CommitmentTypesTargets.lean`, replace
   `trimmedTotalSat` field references with `trimmedSat` and keep the computed
   function references on `trimmedValueFor`.

This rename was not applied because `CommitmentGrossNetTargets.lean` is outside
lane ownership and is part of the required build.

### 8.3 Required patch for the unowned `Conservation.lean`

Adding a fifth field to `CommitmentHTLCOutput` changes its `.mk` arity. The
private `LawfulBEq CommitmentHTLCOutput` instance in
`LnLean/Proofs/Conservation.lean:639-657` pattern-matches four fields and will
fail the full build. Exact patch:

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

No other four-field `CommitmentHTLCOutput` pattern match exists in the tree
(checked with `grep`); all other construction sites are named literals.

### 8.4 Build caveat

The required lane build is green (21 jobs). A full `lake build` was not run and
is not claimed: the `Conservation.lean` patch in §8.3 is required first. This is
the only known structural blocker; it is a mechanical field-arity update, not a
proof failure.

## 9. Reproduction checklist

```sh
cd /home/ubuntu/ln-lean-repair
export PATH=/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH

# 1. Required build (under the shared lock)
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Channel.Types LnLean.Channel.Commitment \
    LnLean.Proofs.Channel.CommitmentTypesTargets \
    LnLean.Proofs.Channel.CommitmentGrossNetTargets

# 2. Axiom audit (scratch file, not committed)
LEAN_NUM_THREADS=1 lake env lean /tmp/opencode/AuditTypes.lean

# 3. Forbidden constructs
grep -nE '\b(sorry|axiom|admit|native_decide|unsafe|implemented_by)\b' \
  LnLean/Channel/Types.lean LnLean/Channel/Commitment.lean \
  LnLean/Proofs/Channel/CommitmentTypesTargets.lean
```

## 10. Blockers

- Full-tree build: **not claimed**. The unowned
  `Conservation.lean` `LawfulBEq` instance must be updated for the fifth
  `CommitmentHTLCOutput` field (§8.3). This is the only known breakage.
- Literal field name `Commitment.trimmedSat`: the stored field is
  `Commitment.trimmedTotalSat` to avoid the wave-5 computed-function collision.
  A coordinated rename (§8.2) is required if the catalog insists on the
  literal field name.
