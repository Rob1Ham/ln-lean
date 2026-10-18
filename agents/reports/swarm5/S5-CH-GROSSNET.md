# S5-CH-GROSSNET — BOLT 3 gross/net commitment values, trimming, and conservation

- Lane: `S5-CH-GROSSNET` (issues CH-03, CH-01, CH-02)
- Branch: `repair/integrated`
- HEAD: `11a460c`
- Owned files:
  - `LnLean/Channel/Commitment.lean` (additive core patch)
  - `LnLean/Proofs/Channel/CommitmentGrossNetTargets.lean` (new)
  - `agents/reports/swarm5/S5-CH-GROSSNET.md` (this report)
- Read-only files consulted (not edited): `LnLean/Channel/Types.lean`,
  `LnLean/Channel/HTLC.lean`, `LnLean/Channel/Fee.lean`,
  `LnLean/Proofs/Channel/CommitmentIntegrationTargets.lean`,
  `LnLean/Proofs/Channel/CommitmentOrderTargets.lean`,
  `LnLean/Proofs/WaveD/D12.lean`, `agents/reports/swarm4/S4-FEE-DUST.md`.

## 1. Result

The lane closes the representational gap in CH-03 without breaking any
existing record literal, signature, or theorem:

- a **gross** commitment HTLC output value (`CommitmentHTLCOutput.amountSat`)
  is separated from a **net** second-stage value used by the dust test
  (`CommitmentTx.netAmountSat`, default `fun h => h.amountSat`);
- the gross value removed by trimming is recorded
  (`CommitmentTx.trimmedSat`, default `0`) and computed independently
  (`Commitment.trimmedSat` / `CommitmentTx.trimmedValue`);
- the actual commitment fee is exposed as
  `Commitment.effectiveFeeSat = fundingValueSat - totalOutputValue`;
- the rich dust test is switched to the net value on the new path
  (`CommitmentTx.htlcOutputNet`, `outputsUnsortedNet`, `outputsNet`) while the
  pre-CH-03 path (`htlcOutput`, `outputs`) is retained unchanged for every
  existing consumer;
- the canonical legacy refinement is proved **without** the wave-4 zero-dust
  workaround: the sorted net list is a permutation of the BOLT 3 trimmed
  legacy-shaped list at an arbitrary dust limit, and of
  `Commitment.commitmentOutputs` on a migrated record;
- conservation is proved exactly: emitted value + base fee + trimmed gross
  value = funding value, and effective fee = base fee + trimmed gross value.

D12's refutations and the wave-4 conditional results stay imported and are
restated at the end of the new module. Nothing in D12 is weakened.

### 1.1 Scope decision: `Types.lean`

`CommitmentHTLCOutput` and `Commitment` are defined in
`LnLean/Channel/Types.lean`, which is outside this lane's ownership. The
literal requested field placement therefore cannot be applied here. The same
design is expressed additively on the owned `CommitmentTx` extension:

| Requested field | Lane implementation | Default |
|---|---|---|
| `CommitmentHTLCOutput.netAmountSat : Nat` | `CommitmentTx.netAmountSat : CommitmentHTLCOutput → Nat` | `fun h => h.amountSat` |
| `Commitment.trimmedSat : Nat` | `Commitment.trimmedSat` (computed) + `CommitmentTx.trimmedSat : Nat` | `0` |
| `Commitment.effectiveFeeSat` | `Commitment.effectiveFeeSat` (computed) | n/a |

The exact future `Types.lean` patch, including the name-collision handling for
`Commitment.trimmedSat`, is in §9.

## 2. Required build

Command run exactly as specified, under `flock`:

```sh
cd /home/ubuntu/ln-lean-repair
export PATH=/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Channel.Commitment \
    LnLean.Proofs.Channel.CommitmentGrossNetTargets
```

Observed output:

```text
Build completed successfully (20 jobs).
```

**Build RC: 0.** The build produced no warnings after cleanup.

No full `lake build`, `collect-obligations.py`, git commit, or git push was
run. The working tree already contained other lanes' uncommitted changes;
this lane touched only its three owned files.

## 3. Exact signatures

### 3.1 Core patch: `LnLean/Channel/Commitment.lean`

Computed trimmed value and effective fee (after
`Commitment.totalOutputValue_eq`, around line 196):

```lean
def Commitment.trimmedSat (c : Commitment) (dustLimitSat : Nat)
    (netAmountSat : CommitmentHTLCOutput → Nat) : Nat :=
  (if dustLimitSat ≤ c.toLocalSat then 0 else c.toLocalSat) +
  (if dustLimitSat ≤ c.toRemoteSat then 0 else c.toRemoteSat) +
  (c.htlcs.map (fun h =>
    if dustLimitSat ≤ netAmountSat h then 0 else h.amountSat)).sum

def Commitment.effectiveFeeSat (c : Commitment) : Nat :=
  c.fundingValueSat - c.totalOutputValue

theorem Commitment.totalOutputValue_add_effectiveFeeSat (c : Commitment)
    (h : c.totalOutputValue ≤ c.fundingValueSat) :
    c.totalOutputValue + c.effectiveFeeSat = c.fundingValueSat

theorem Commitment.effectiveFeeSat_eq_feeSat (c : Commitment)
    (h : c.totalOutputValue + c.feeSat = c.fundingValueSat) :
    c.effectiveFeeSat = c.feeSat
```

Additive fields in `CommitmentTx` (line 753 ff.):

```lean
structure CommitmentTx where
  -- existing fields unchanged ...
  netAmountSat : CommitmentHTLCOutput → Nat := fun h => h.amountSat
  trimmedSat : Nat := 0
```

Net-based construction (line 855 ff.), added without changing the old path:

```lean
def CommitmentTx.htlcOutputNet (tx : CommitmentTx) (h : CommitmentHTLCOutput) :
    Option CommitmentTxOutput :=
  if tx.dustLimitSat ≤ tx.netAmountSat h then
    some (CommitmentTxOutput.htlc h (tx.htlcScript h))
  else none

def CommitmentTx.outputsUnsortedNet (tx : CommitmentTx) : List CommitmentTxOutput :=
  tx.toLocalOutput.toList ++
    (tx.toRemoteOutput.toList ++
      (tx.commitment.htlcs.filterMap tx.htlcOutputNet ++
        (tx.localAnchorOutput.toList ++ tx.remoteAnchorOutput.toList)))

def CommitmentTx.outputsNet (tx : CommitmentTx) : List CommitmentTxOutput :=
  sortOutputs tx.outputsUnsortedNet

def CommitmentTx.trimmedValue (tx : CommitmentTx) : Nat :=
  tx.commitment.trimmedSat tx.dustLimitSat tx.netAmountSat

theorem CommitmentTx.trimmedValue_eq_trimmedSat (tx : CommitmentTx) :
    tx.trimmedValue = tx.commitment.trimmedSat tx.dustLimitSat tx.netAmountSat
```

Supporting membership/sortedness lemmas added next to `outputsNet`:

```lean
theorem CommitmentTx.outputsNet_perm (tx : CommitmentTx) :
    tx.outputsNet.Perm tx.outputsUnsortedNet

theorem CommitmentTx.mem_outputsNet_iff {tx : CommitmentTx} {o : CommitmentTxOutput} :
    o ∈ tx.outputsNet ↔ o ∈ tx.outputsUnsortedNet

theorem CommitmentTx.mem_outputsUnsortedNet_iff {tx : CommitmentTx}
    {o : CommitmentTxOutput} :
    o ∈ tx.outputsUnsortedNet ↔
      o ∈ tx.toLocalOutput.toList ∨
      o ∈ tx.toRemoteOutput.toList ∨
      o ∈ tx.commitment.htlcs.filterMap tx.htlcOutputNet ∨
      o ∈ tx.localAnchorOutput.toList ∨
      o ∈ tx.remoteAnchorOutput.toList

theorem CommitmentTx.mem_htlcOutputNet_iff {tx : CommitmentTx}
    {h : CommitmentHTLCOutput} {o : CommitmentTxOutput} :
    tx.htlcOutputNet h = some o ↔
      tx.dustLimitSat ≤ tx.netAmountSat h ∧
        o = CommitmentTxOutput.htlc h (tx.htlcScript h)

theorem CommitmentTx.htlcOutputNet_eq_none_of_dust (tx : CommitmentTx)
    (h : CommitmentHTLCOutput) (hd : tx.netAmountSat h < tx.dustLimitSat) :
    tx.htlcOutputNet h = none

theorem CommitmentTx.htlcOutputNet_mem_outputsNet (tx : CommitmentTx)
    (h : CommitmentHTLCOutput) (hmem : h ∈ tx.commitment.htlcs)
    (hd : tx.dustLimitSat ≤ tx.netAmountSat h) :
    CommitmentTxOutput.htlc h (tx.htlcScript h) ∈ tx.outputsNet

theorem CommitmentTx.outputsNet_pairwise (tx : CommitmentTx) :
    tx.outputsNet.Pairwise CommitmentTxOutput.le

theorem CommitmentTx.outputsNet_values_sorted (tx : CommitmentTx) :
    (tx.outputsNet.map (fun o => o.valueSat)).Pairwise (· ≤ ·)

theorem CommitmentTx.outputsNet_scripts_sorted (tx : CommitmentTx) :
    tx.outputsNet.Pairwise (fun a b =>
      a.valueSat = b.valueSat → a.scriptPubKey.le b.scriptPubKey)

theorem CommitmentTx.outputsNet_cltvs_sorted (tx : CommitmentTx) :
    tx.outputsNet.Pairwise (fun a b =>
      a.valueSat = b.valueSat → a.scriptPubKey = b.scriptPubKey →
        a.cltvExpiry ≤ b.cltvExpiry)
```

`CommitmentTx.htlcOutput` and `CommitmentTx.outputs` are **unchanged** (still
test gross `amountSat`), so every existing theorem and consumer compiles
without a migration.

### 3.2 New module: namespace

`LnLean.Proofs.Channel.CommitmentGrossNetTargets.lean` uses

```lean
namespace LnLean.Proofs.Channel.CommitmentGrossNet
```

and roots the record-level definitions in the channel namespace so dot
notation works:

```lean
LnLean.Channel.CommitmentTx.canonicalOutputs
LnLean.Channel.CommitmentTx.Migrated
LnLean.Channel.CommitmentTx.migratedFrom
```

### 3.3 Second-stage fee and the exact gross threshold

```lean
def htlcTimeoutFee (anchors : Bool) (r : FeeRate) : Nat
def htlcSuccessFee (anchors : Bool) (r : FeeRate) : Nat
def htlcSecondStageFee (anchors : Bool) (r : FeeRate)
    (h : CommitmentHTLCOutput) : Nat

theorem htlcTimeoutFee_eq (anchors : Bool) (r : FeeRate) :
    htlcTimeoutFee anchors r = CommitmentIntegration.htlcTimeoutFeeSat anchors r

theorem htlcSuccessFee_eq (anchors : Bool) (r : FeeRate) :
    htlcSuccessFee anchors r = CommitmentIntegration.htlcSuccessFeeSat anchors r

theorem htlcSecondStageFee_anchors (r : FeeRate) (h : CommitmentHTLCOutput) :
    htlcSecondStageFee true r h = 0

def NetConsistent (tx : CommitmentTx) (anchors : Bool) (r : FeeRate) : Prop :=
  ∀ h ∈ tx.commitment.htlcs,
    tx.netAmountSat h + htlcSecondStageFee anchors r h = h.amountSat

theorem netAmountSat_le_amountSat_of_netConsistent {tx : CommitmentTx}
    {anchors : Bool} {r : FeeRate} (hc : NetConsistent tx anchors r)
    {h : CommitmentHTLCOutput} (hmem : h ∈ tx.commitment.htlcs) :
    tx.netAmountSat h ≤ h.amountSat

theorem net_lt_dust_iff_gross_lt_threshold {tx : CommitmentTx}
    {h : CommitmentHTLCOutput} {anchors : Bool} {r : FeeRate}
    (hnet : tx.netAmountSat h + htlcSecondStageFee anchors r h = h.amountSat) :
    tx.netAmountSat h < tx.dustLimitSat ↔
      h.amountSat < tx.dustLimitSat + htlcSecondStageFee anchors r h

theorem htlcOutputNet_eq_none_iff_gross_threshold (tx : CommitmentTx)
    (h : CommitmentHTLCOutput) (anchors : Bool) (r : FeeRate)
    (hnet : tx.netAmountSat h + htlcSecondStageFee anchors r h = h.amountSat) :
    tx.htlcOutputNet h = none ↔
      h.amountSat < tx.dustLimitSat + htlcSecondStageFee anchors r h

theorem htlcOutputNet_isSome_of_threshold_eq (tx : CommitmentTx)
    (h : CommitmentHTLCOutput) (anchors : Bool) (r : FeeRate)
    (hnet : tx.netAmountSat h + htlcSecondStageFee anchors r h = h.amountSat)
    (heq : h.amountSat = tx.dustLimitSat + htlcSecondStageFee anchors r h) :
    (tx.htlcOutputNet h).isSome = true
```

Equality with the threshold is kept, matching BOLT 3's strict `less than`
trimming rule.

### 3.4 Canonical legacy-shaped trimmed list

`keepHtlc` is a decidable trim predicate; `canonicalOutputs` is the legacy
`CommitmentOutput` shape after applying the same trim decision:

```lean
def keepHtlc (dustLimitSat : Nat) (netAmountSat : CommitmentHTLCOutput → Nat)
    (h : CommitmentHTLCOutput) : Bool :=
  decide (dustLimitSat ≤ netAmountSat h)

theorem keepHtlc_eq_true_iff {d : Nat} {net : CommitmentHTLCOutput → Nat}
    {h : CommitmentHTLCOutput} :
    keepHtlc d net h = true ↔ d ≤ net h

def CommitmentTx.canonicalOutputs (tx : CommitmentTx) : List CommitmentOutput :=
  (if tx.dustLimitSat ≤ tx.commitment.toLocalSat then
    [CommitmentOutput.toLocal tx.commitment.toLocalSat] else []) ++
  (if tx.dustLimitSat ≤ tx.commitment.toRemoteSat then
    [CommitmentOutput.toRemote tx.commitment.toRemoteSat] else []) ++
  (tx.commitment.htlcs.filterMap (fun h =>
    if keepHtlc tx.dustLimitSat tx.netAmountSat h = true then
      some (CommitmentOutput.htlc h.direction h.amountSat)
    else none)) ++
  (if tx.commitment.anchorOutputs then
    [CommitmentOutput.localAnchor, CommitmentOutput.remoteAnchor] else [])

theorem filterMap_congr_pointwise {α β : Type} {f g : α → Option β}
    (h : ∀ a, f a = g a) (l : List α) :
    l.filterMap f = l.filterMap g

theorem map_outputsUnsortedNet_eq_canonicalOutputs (tx : CommitmentTx) :
    (tx.outputsUnsortedNet.map CommitmentTxOutput.toCommitmentOutput) =
      tx.canonicalOutputs

theorem outputsNet_refines_canonicalOutputs (tx : CommitmentTx) :
    (tx.outputsNet.map CommitmentTxOutput.toCommitmentOutput).Perm
      tx.canonicalOutputs
```

**No zero-dust hypothesis and no non-zero-output hypothesis are used.**

### 3.5 Migrated records and the exact legacy path

```lean
def CommitmentTx.Migrated (tx : CommitmentTx) : Prop :=
  (tx.commitment.toLocalSat = 0 ↔
      tx.commitment.toLocalSat < tx.dustLimitSat) ∧
  (tx.commitment.toRemoteSat = 0 ↔
      tx.commitment.toRemoteSat < tx.dustLimitSat) ∧
  (∀ h ∈ tx.commitment.htlcs, tx.dustLimitSat ≤ tx.netAmountSat h)

theorem filterMap_keep_eq_map (d : Nat)
    (net : CommitmentHTLCOutput → Nat) :
    ∀ l : List CommitmentHTLCOutput,
      (∀ x ∈ l, keepHtlc d net x = true) →
      l.filterMap (fun h =>
        if keepHtlc d net h = true then
          some (CommitmentOutput.htlc h.direction h.amountSat)
        else none) =
      l.map (fun h => CommitmentOutput.htlc h.direction h.amountSat)

theorem canonicalOutputs_eq_commitmentOutputs_of_migrated (tx : CommitmentTx)
    (hm : tx.Migrated) :
    tx.canonicalOutputs = tx.commitment.commitmentOutputs

theorem outputsNet_perm_commitmentOutputs_of_migrated (tx : CommitmentTx)
    (hm : tx.Migrated) :
    (tx.outputsNet.map CommitmentTxOutput.toCommitmentOutput).Perm
      tx.commitment.commitmentOutputs
```

The migration constructor and its invariants:

```lean
def CommitmentTx.migratedFrom (tx : CommitmentTx) : CommitmentTx :=
  { tx with
    commitment :=
      { tx.commitment with
        toLocalSat :=
          if tx.dustLimitSat ≤ tx.commitment.toLocalSat then
            tx.commitment.toLocalSat else 0
        toRemoteSat :=
          if tx.dustLimitSat ≤ tx.commitment.toRemoteSat then
            tx.commitment.toRemoteSat else 0
        htlcs := tx.commitment.htlcs.filter
          (keepHtlc tx.dustLimitSat tx.netAmountSat) },
    trimmedSat := tx.trimmedValue }

theorem CommitmentTx.migratedFrom_feeSat (tx : CommitmentTx) :
    (tx.migratedFrom).commitment.feeSat = tx.commitment.feeSat

theorem CommitmentTx.migratedFrom_fundingValueSat (tx : CommitmentTx) :
    (tx.migratedFrom).commitment.fundingValueSat =
      tx.commitment.fundingValueSat

theorem CommitmentTx.migratedFrom_trimmedSat (tx : CommitmentTx) :
    (tx.migratedFrom).trimmedSat = tx.trimmedValue

theorem CommitmentTx.migratedFrom_htlcs (tx : CommitmentTx) :
    (tx.migratedFrom).commitment.htlcs =
      tx.commitment.htlcs.filter
        (keepHtlc tx.dustLimitSat tx.netAmountSat)

theorem CommitmentTx.migratedFrom_migrated (tx : CommitmentTx)
    (hdust : 0 < tx.dustLimitSat) : (tx.migratedFrom).Migrated

theorem CommitmentTx.migratedFrom_netConsistent (tx : CommitmentTx)
    {anchors : Bool} {r : FeeRate} (hc : NetConsistent tx anchors r) :
    NetConsistent (tx.migratedFrom) anchors r

theorem CommitmentTx.canonicalOutputs_migratedFrom (tx : CommitmentTx) :
    (tx.migratedFrom).canonicalOutputs = tx.canonicalOutputs

theorem CommitmentTx.migratedFrom_outputsNet_perm_commitmentOutputs
    (tx : CommitmentTx) (hdust : 0 < tx.dustLimitSat) :
    ((tx.migratedFrom).outputsNet.map CommitmentTxOutput.toCommitmentOutput).Perm
      (tx.migratedFrom).commitment.commitmentOutputs
```

The only hypothesis is `0 < tx.dustLimitSat`. This is not a workaround: BOLT 2
requires `dust_limit_satoshis >= 354` (`02-peer-protocol.md:870`). The
positivity is needed only because the legacy
`Commitment.commitmentOutputs` omits zero-valued non-HTLC outputs; the
canonical permutation and all conservation theorems are unconditional.

### 3.6 Conservation, trimmed value, effective fee

```lean
theorem sum_map_ite_add_sum_map_ite (d : Nat)
    (net g : CommitmentHTLCOutput → Nat) (hs : List CommitmentHTLCOutput) :
    (hs.map (fun h => if d ≤ net h then g h else 0)).sum +
      (hs.map (fun h => if d ≤ net h then 0 else g h)).sum =
    (hs.map g).sum

theorem htlcOutputsValue_filter_keep (d : Nat)
    (net : CommitmentHTLCOutput → Nat) (hs : List CommitmentHTLCOutput) :
    htlcOutputsValue (hs.filter (keepHtlc d net)) =
      (hs.map (fun h => if d ≤ net h then h.amountSat else 0)).sum

theorem CommitmentTx.migratedFrom_totalOutputValue_add_trimmedSat
    (tx : CommitmentTx) :
    (tx.migratedFrom).commitment.totalOutputValue +
        (tx.migratedFrom).trimmedSat =
      tx.commitment.totalOutputValue

theorem CommitmentTx.migratedFrom_conservation (tx : CommitmentTx)
    (hbal : tx.commitment.totalOutputValue + tx.commitment.feeSat =
      tx.commitment.fundingValueSat) :
    (tx.migratedFrom).commitment.totalOutputValue +
        (tx.migratedFrom).commitment.feeSat +
        (tx.migratedFrom).trimmedSat =
      tx.commitment.fundingValueSat

theorem CommitmentTx.migratedFrom_effectiveFee_eq (tx : CommitmentTx)
    (hbal : tx.commitment.totalOutputValue + tx.commitment.feeSat =
      tx.commitment.fundingValueSat) :
    (tx.migratedFrom).commitment.effectiveFeeSat =
      (tx.migratedFrom).commitment.feeSat +
        (tx.migratedFrom).trimmedSat

theorem CommitmentTx.migratedFrom_trimmedSat_eq_computed (tx : CommitmentTx) :
    (tx.migratedFrom).trimmedSat =
      tx.commitment.trimmedSat tx.dustLimitSat tx.netAmountSat

theorem CommitmentTx.migratedFrom_effectiveFee_val (tx : CommitmentTx) :
    (tx.migratedFrom).commitment.effectiveFeeSat =
      tx.commitment.fundingValueSat -
        (tx.migratedFrom).commitment.totalOutputValue
```

The second-stage fee is **not** part of `effectiveFeeSat`: it is withheld from
the gross HTLC output and paid later by the HTLC transaction
(`03-transactions.md:367`). The commitment fee receives only the gross value of
trimmed outputs (`03-transactions.md:309-311`, `:501`).

### 3.7 Net-based rich specification

```lean
theorem CommitmentTx.outputsNet_nonAnchor_value_ge_dust (tx : CommitmentTx)
    (hle : ∀ h, tx.netAmountSat h ≤ h.amountSat)
    {o : CommitmentTxOutput} (ho : o ∈ tx.outputsNet)
    (hl : o.kind ≠ .localAnchor) (hr : o.kind ≠ .remoteAnchor) :
    tx.dustLimitSat ≤ o.valueSat

theorem CommitmentTx.outputsNet_spec (tx : CommitmentTx)
    (hle : ∀ h, tx.netAmountSat h ≤ h.amountSat) :
    tx.outputsNet.Perm tx.outputsUnsortedNet ∧
    tx.outputsNet.Pairwise CommitmentTxOutput.le ∧
    (tx.outputsNet.map (fun o => o.valueSat)).Pairwise (· ≤ ·) ∧
    tx.outputsNet.Pairwise (fun a b =>
      a.valueSat = b.valueSat → a.scriptPubKey.le b.scriptPubKey) ∧
    tx.outputsNet.Pairwise (fun a b =>
      a.valueSat = b.valueSat → a.scriptPubKey = b.scriptPubKey →
        a.cltvExpiry ≤ b.cltvExpiry) ∧
    (tx.toLocalOutput = none ↔ tx.commitment.toLocalSat < tx.dustLimitSat) ∧
    (tx.toRemoteOutput = none ↔ tx.commitment.toRemoteSat < tx.dustLimitSat) ∧
    (∀ h ∈ tx.commitment.htlcs,
      tx.netAmountSat h < tx.dustLimitSat → tx.htlcOutputNet h = none) ∧
    (∀ h ∈ tx.commitment.htlcs, tx.dustLimitSat ≤ tx.netAmountSat h →
      CommitmentTxOutput.htlc h (tx.htlcScript h) ∈ tx.outputsNet) ∧
    (∀ o ∈ tx.outputsNet, o.kind ≠ .localAnchor → o.kind ≠ .remoteAnchor →
      tx.dustLimitSat ≤ o.valueSat)

theorem CommitmentTx.outputsNet_trims_iff_gross_threshold (tx : CommitmentTx)
    {anchors : Bool} {r : FeeRate} (hc : NetConsistent tx anchors r)
    {h : CommitmentHTLCOutput} (hmem : h ∈ tx.commitment.htlcs) :
    tx.htlcOutputNet h = none ↔
      h.amountSat < tx.dustLimitSat + htlcSecondStageFee anchors r h
```

### 3.8 Retained D12 and wave-4 results

```lean
theorem d12_output_ordering_fails :
    ¬ (∀ c : Commitment,
        (c.commitmentOutputs.map CommitmentOutput.value).Pairwise (· ≤ ·))

theorem d12_zero_value_htlc_emitted :
    CommitmentOutput.htlc .local 0 ∈
      LnLean.Proofs.WaveD.D12.zeroValueHtlcCommitment.commitmentOutputs

theorem d12_cltv_tiebreak_not_recoverable :
    LnLean.Proofs.WaveD.D12.cltvOrderLeft.htlcs ≠
        LnLean.Proofs.WaveD.D12.cltvOrderRight.htlcs ∧
      LnLean.Proofs.WaveD.D12.cltvOrderLeft.commitmentOutputs =
        LnLean.Proofs.WaveD.D12.cltvOrderRight.commitmentOutputs

theorem wave4_dust_trimming_not_perm :
    ¬ (CommitmentIntegration.legacyOutputs
          CommitmentIntegration.dustDemoTx).Perm
        CommitmentIntegration.dustDemoTx.commitment.commitmentOutputs

theorem wave4_richOutputs_refine_legacyCommitment_retained
    (tx : CommitmentTx) (holder : Direction) (number funding fee toLocal
      contestDelay : Nat) (anchors : Bool) (hs : List HTLCRecord)
    (hcommit : tx.commitment =
      CommitmentIntegration.netCommitmentOfRecords holder number funding fee
        toLocal contestDelay anchors 0 0 0 hs)
    (hdust : tx.dustLimitSat = 0)
    (hl : tx.commitment.toLocalSat ≠ 0)
    (hr : tx.commitment.toRemoteSat ≠ 0) :
    (CommitmentIntegration.legacyOutputs tx).Perm
      (CommitmentIntegration.legacyCommitmentOfRecords holder number funding fee
        toLocal contestDelay anchors hs).commitmentOutputs
```

The wave-4 conditional theorem is kept **verbatim**. The new
`migratedFrom_outputsNet_perm_commitmentOutputs` removes its zero-dust premise
by migrating the record instead of weakening the legacy refusal.

## 4. Why the refinement is exact

The chain is:

```text
outputsNet
  --(outputsNet_perm)-->                            outputsUnsortedNet
  --(map toCommitmentOutput)-->                     canonicalOutputs
  --(canonicalOutputs_eq_commitmentOutputs)-->      commitmentOutputs
```

- `outputsNet_refines_canonicalOutputs` is a `List.Perm` at an **arbitrary**
  dust limit because `canonicalOutputs` itself already applies the same net
  dust test; no record rewriting is needed.
- `canonicalOutputs_eq_commitmentOutputs_of_migrated` is an **equality** on a
  migrated record. `Migrated` encodes exactly the normal form produced by
  `migratedFrom`: zeroed non-HTLC outputs are below dust, and every remaining
  HTLC satisfies the net dust test.
- The only residual mismatch is the legacy convention that
  `Commitment.commitmentOutputs` omits zero-valued non-HTLC outputs. On a
  positive dust limit, "value = 0" and "value below dust" coincide only under
  `Migrated`; hence `migratedFrom_migrated` assumes `0 < dustLimitSat`.
- `List.Perm`, not equality, is the strongest true relation for the *sorted*
  rich list. D12's ordering refutation still holds.

## 5. Gross/net convention used

| Quantity | Source | Used for |
|---|---|---|
| gross HTLC commitment output | `CommitmentHTLCOutput.amountSat` | `CommitmentTxOutput.htlc`, `commitmentOutputs`, trimmed value |
| net second-stage value | `CommitmentTx.netAmountSat` | net dust test `net < dust` |
| second-stage fee | `htlcSecondStageFee anchors r h` | `net + fee = gross` (`NetConsistent`) |
| trimmed gross value | `Commitment.trimmedSat` / `CommitmentTx.trimmedSat` | added to commitment fee |
| effective commitment fee | `fundingValueSat - totalOutputValue` | base fee + trimmed gross |

BOLT anchors:

- `03-transactions.md:109-110`: amounts rounded down; the dust test is on the
  amount **minus the fees for the HTLC transaction**.
- `03-transactions.md:309-311`: a trimmed output is added to the commitment
  transaction fee.
- `03-transactions.md:367`: the HTLC-timeout/success output is
  `amount_msat / 1000 - fees`, i.e. the net value.
- `03-transactions.md:501`: the actual commitment fee may be higher than the
  base fee because of trimmed outputs.
- `02-peer-protocol.md:870`: `dust_limit_satoshis >= 354`, so
  `0 < dustLimitSat` is protocol-valid.

## 6. Axiom audit

Scratch file `/tmp/opencode/AuditGrossNet.lean` (not committed) ran
`#print axioms` on the headline results:

```text
map_outputsUnsortedNet_eq_canonicalOutputs          propext, Quot.sound
outputsNet_refines_canonicalOutputs                 propext, Quot.sound
canonicalOutputs_eq_commitmentOutputs_of_migrated   propext, Quot.sound
outputsNet_perm_commitmentOutputs_of_migrated       propext, Quot.sound
migratedFrom_migrated                               propext, Quot.sound
migratedFrom_outputsNet_perm_commitmentOutputs      propext, Quot.sound
migratedFrom_totalOutputValue_add_trimmedSat        propext, Quot.sound
migratedFrom_conservation                           propext, Quot.sound
migratedFrom_effectiveFee_eq                        propext, Quot.sound
outputsNet_spec                                     propext, Classical.choice, Quot.sound
outputsNet_trims_iff_gross_threshold                propext, Quot.sound
d12_output_ordering_fails                           propext, Quot.sound
d12_zero_value_htlc_emitted                         propext
d12_cltv_tiebreak_not_recoverable                   none
wave4_dust_trimming_not_perm                        propext, Quot.sound
wave4_richOutputs_refine_legacyCommitment_retained  propext, Quot.sound
```

No theorem depends on `sorryAx`, any user axiom, or any axiom outside
`propext`, `Quot.sound`, and `Classical.choice`. `Classical.choice` appears
only through the existing `sortOutputs`/`List.Pairwise` infrastructure, not
from a new choice principle.

## 7. Forbidden-construct grep

Command:

```sh
cd /home/ubuntu/ln-lean-repair
grep -nE '\b(sorry|axiom|admit|native_decide|unsafe|implemented_by)\b' \
  LnLean/Channel/Commitment.lean \
  LnLean/Proofs/Channel/CommitmentGrossNetTargets.lean
```

Observed output:

```text
NO_FORBIDDEN_TOKENS
```

## 8. Compatibility and migration sites

### 8.1 What is preserved unchanged

- `CommitmentHTLCOutput`, `Commitment`, and `CommitmentOutput` are untouched.
- `CommitmentTx`'s existing fields keep their names, types, and order;
  `netAmountSat` and `trimmedSat` are appended with defaults, so every record
  literal and every `{ tx with ... }` update still elaborates.
- `CommitmentTx.htlcOutput`, `CommitmentTx.outputs`, `CommitmentTx.outputs_spec`
  and all their existing lemmas keep their exact signatures and gross
  `amountSat` dust test.
- `Commitment.commitmentOutputs` keeps its exact shape (it emits gross
  `amountSat` after the field migration in §9).
- D12 and every wave-4 theorem remain valid and visible.

### 8.2 Exact construction sites in the repository

A repository-wide search found exactly two `CommitmentTx` record literals:

1. `LnLean/Proofs/Channel/CommitmentIntegrationTargets.lean:744`
   (`dustDemoTx`) — the wave-4 demo. It relies on the defaults, so it still
   type-checks; its `amountSat` is the demo's net value, so leaving
   `netAmountSat` at the default preserves its current semantics.
2. `LnLean/Proofs/Channel/CommitmentGrossNetTargets.lean:408`
   (`CommitmentTx.migratedFrom`) — the new migration constructor. It sets
   `trimmedSat` explicitly and leaves `netAmountSat` inherited from `tx`.

No other file constructs a `CommitmentTx` literally. Therefore **no
construction site had to be migrated for compilation**.

### 8.3 Remaining semantic migration (follow-up, not required for build)

To make the rich model BOLT-3-exact, consumers that currently treat
`amountSat` as the second-stage value must either:

- supply `netAmountSat` explicitly (gross `amountSat` + net projection), or
- keep the default (the safe zero-second-stage-fee / legacy convention).

The old consumers of the gross path are:

- `LnLean/Proofs/Channel/CommitmentIntegrationTargets.lean` — wave-4
  `legacyOutputs`, `trimmedValue`, `richOutputs_refine_legacyCommitment`;
- `LnLean/Proofs/Channel/CommitmentOrderTargets.lean` — `outputs_spec`,
  `mem_htlcOutput_iff`, `no_dust_htlc_output`.

Both continue to compile against the preserved old path. A follow-up that
wants the net dust test should call `CommitmentTx.outputsNet` /
`CommitmentTx.htlcOutputNet` (or migrate the record with
`CommitmentTx.migratedFrom`) and use
`CommitmentTx.outputsNet_trims_iff_gross_threshold` for the gross-threshold
reading.

### 8.4 Integration wiring (outside this lane)

The new module is intentionally **not** imported by `LnLean.lean` and is not
registered in `LnLean/Proofs/Obligations.lean`,
`LnLean/Proofs/Traceability.lean`, or `LnLean/Proofs/PhaseC3/AxiomAudit.lean`;
those files are outside lane ownership. The maintainer integration is:

1. add `import LnLean.Proofs.Channel.CommitmentGrossNetTargets` to
   `LnLean.lean` (or the appropriate aggregate module);
2. register the CH-01/CH-02/CH-03 target names in the obligations and
   traceability tables;
3. add the headline theorems to the axiom-audit list;
4. if desired, migrate the rich dust test in `CommitmentTx.htlcOutput` to
   `tx.netAmountSat` after auditing `CommitmentOrderTargets.lean` and
   `CommitmentIntegrationTargets.lean`; the new `outputsNet` path already
   provides the net semantics without that breaking change.

Until then the module is buildable on its own and all its results are available
under `LnLean.Proofs.Channel.CommitmentGrossNet`.

## 9. Exact `Types.lean` integration patch

The lane cannot edit `LnLean/Channel/Types.lean`. When ownership allows it,
the exact patch is:

```lean
structure CommitmentHTLCOutput where
  direction : Direction
  /-- Gross value carried by the commitment output. -/
  amountSat : Nat
  cltvExpiry : Height
  state : HTLCState
  /-- Net second-stage value; the default preserves every existing literal. -/
  netAmountSat : Nat := amountSat
deriving Repr, DecidableEq, BEq
```

```lean
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
  /-- Gross value removed by BOLT 3 trimming and added to the fee. -/
  trimmedSat : Nat := 0
deriving Repr, DecidableEq, BEq
```

**Name-collision note.** This lane already introduces a computed
`Commitment.trimmedSat (c) (dustLimitSat) (netAmountSat) : Nat`. A stored
`Commitment.trimmedSat : Nat` field would have the same name and cannot
coexist. The integration must do one of:

- rename the computed function to `Commitment.trimmedValueFor` (recommended;
  it is a *nominal* computation), keeping the stored field named
  `trimmedSat`; or
- name the stored field `trimmedTotalSat`, keeping the computed function.

Recommended follow-up edits in `Commitment.lean`:

```lean
-- after the Types.lean field lands, the rich projection delegates:
-- netAmountSat := fun h => h.netAmountSat
-- CommitmentTx.trimmedValue stays the computed nominal value:
--   tx.commitment.trimmedValueFor tx.dustLimitSat tx.netAmountSat
-- while the stored Commitment.trimmedSat is the value removed by an
-- applied migration (migratedFrom sets CommitmentTx.trimmedSat := tx.trimmedValue).
```

`Commitment.effectiveFeeSat` needs no rename: it is a function, not a proposed
stored field. The theorem `CommitmentTx.trimmedValue_eq_trimmedSat` becomes
`CommitmentTx.trimmedValue_eq_trimmedValueFor` after the function rename; the
accounting theorem `migratedFrom_trimmedSat_eq_computed` still relates the
stored `CommitmentTx.trimmedSat` to the computed nominal value, but it becomes
a proved equality on `migratedFrom` rather than a definitional `rfl`. All other
theorem signatures in this lane remain valid.

After the patch, construction sites must set `amountSat := gross` and
`netAmountSat := net`; sites that mean `gross = net` can omit both fields.
The only literal currently in the tree (`dustDemoTx`) still compiles
unchanged because of the defaults.

## 10. Scope caveats

- Script execution, signature checks, witnesses, sighash, and consensus
  validity are out of scope. Script bytes are the caller-supplied
  `CommitmentTx` fields.
- `option_anchors` second-stage fees are zero, as BOLT 3 prescribes; the
  anchor presence convention remains "both anchors iff `anchorOutputs`".
- `zero_fee_commitments` / `shared_anchor`, fee bumping, and CPFP economics are
  out of scope.
- The `0 < dustLimitSat` hypothesis on `migratedFrom_migrated` and
  `migratedFrom_outputsNet_perm_commitmentOutputs` is the BOLT 2 protocol
  domain (`dust_limit_satoshis >= 354`), not a model workaround.
- The refinement is a permutation, not equality, because the rich model sorts
  while `commitmentOutputs` emits group order; D12 shows equality/sortedness
  is false.
- The second-stage fee schedule is delegated to the wave-4 module
  (`CommitmentIntegration.htlcTimeoutFeeSat` / `htlcSuccessFeeSat`); this lane
  re-exports it and proves the net/gross threshold equivalence.
- No cross-implementation execution against rust-lightning is performed.

## 11. Reproduction checklist

```sh
cd /home/ubuntu/ln-lean-repair
export PATH=/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH

# 1. Required build (under the shared lock)
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Channel.Commitment \
    LnLean.Proofs.Channel.CommitmentGrossNetTargets

# 2. Axiom audit (scratch file, not committed)
LEAN_NUM_THREADS=1 lake env lean /tmp/opencode/AuditGrossNet.lean

# 3. Forbidden constructs
grep -nE '\b(sorry|axiom|admit|native_decide|unsafe|implemented_by)\b' \
  LnLean/Channel/Commitment.lean \
  LnLean/Proofs/Channel/CommitmentGrossNetTargets.lean
```
