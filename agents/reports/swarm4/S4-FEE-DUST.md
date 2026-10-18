# S4-FEE-DUST — second-stage fee, dust trimming, and the legacy commitment view

- Lane: `S4-FEE-DUST` (issues CH-01, CH-02)
- Branch: `repair/integrated`
- HEAD at start/finish: `f2123ef`
- Owned files:
  - `LnLean/Proofs/Channel/CommitmentIntegrationTargets.lean` (new)
  - `agents/reports/swarm4/S4-FEE-DUST.md` (this report)
- Read-only files consulted (not edited): `LnLean/Channel/Commitment.lean`,
  `LnLean/Channel/Types.lean`, `LnLean/Channel/Fee.lean`,
  `LnLean/Channel/HTLC.lean`, `LnLean/Proofs/WaveD/D12.lean`,
  `LnLean/Proofs/WaveD/D47.lean`, `LnLean/Proofs/Channel/CommitmentTxProps.lean`.

## 1. Result

The new module supplies the BOLT 3 second-stage fee as a function of the
negotiated feerate and `option_anchors`, the exact gross/net threshold
equivalence for dust trimming, a value-preserving legacy projection of the
rich `CommitmentTx`, the strongest true refinement relation to
`Commitment.commitmentOutputs` (`List.Perm`, not equality), and two explicit
BOLT 3 constructions with exact conservation and effective-fee accounting.

The two open issues are addressed as follows.

- **CH-01 (legacy path).** The legacy projection is
  `legacyOutputs tx = tx.outputs.map CommitmentTxOutput.toCommitmentOutput`.
  At `dustLimitSat = 0` and non-zero `to_local`/`to_remote`, this is a
  **permutation** of `tx.commitment.commitmentOutputs`
  (`legacyOutputs_perm_commitmentOutputs`).  Equality is false because the rich
  model sorts while the legacy function emits a fixed group order.  D12 is
  retained verbatim as `legacy_ordering_refuted`; a second restatement
  `legacy_zero_value_htlc_emitted` keeps the zero-valued HTLC counterexample
  visible.  The zero-dust hypothesis is proved necessary by
  `dust_trimming_not_perm`.
- **CH-02 (second-stage fee).** The fee is computed from the feerate:
  `htlcTimeoutFeeSat` uses weight 663, `htlcSuccessFeeSat` uses weight 703, and
  both are zero with `option_anchors` (`secondStageFeeAt_anchors`).  The exact
  value identity is `gross = net + withheld fee`, and the trimming threshold
  in gross terms is `dust_limit + second_stage_fee`.  The BOLT 3 construction
  proves that
  `emitted outputs + base fee + withheld second-stage fees + trimmed gross
  value = funding`.

D12 is *not* weakened: the unconditional legacy ordering theorem remains
refuted and the zero-valued HTLC is still emitted by `commitmentOutputs`.
The refinement theorem is conditional on exactly the hypotheses under which
the legacy reading is sound.

## 2. Required build

Command run exactly as specified (under `flock`):

```sh
cd /home/ubuntu/ln-lean-repair
export PATH=/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Proofs.Channel.CommitmentIntegrationTargets
```

Observed output:

```text
✔ [19/19] Built LnLean.Proofs.Channel.CommitmentIntegrationTargets (988ms)
Build completed successfully (19 jobs).
```

**Build RC: 0.**

An additional direct compile was also clean:

```sh
LEAN_NUM_THREADS=1 lake env lean \
  LnLean/Proofs/Channel/CommitmentIntegrationTargets.lean
# RC 0, no warnings
```

No full `lake build`, no `collect-obligations.py`, no git commit/push was run.

## 3. Exact signatures

Namespace:

```lean
namespace LnLean.Proofs.Channel.CommitmentIntegration
```

### 3.1 BOLT 3 second-stage fee

```lean
def htlcTimeoutWeight : Weight := ⟨663⟩
def htlcSuccessWeight : Weight := ⟨703⟩

theorem htlcTimeoutWeight_val : htlcTimeoutWeight.val = 663
theorem htlcSuccessWeight_val : htlcSuccessWeight.val = 703

def htlcTimeoutFeeSat (anchors : Bool) (r : FeeRate) : Nat :=
  if anchors then 0 else (feeForWeight r htlcTimeoutWeight).val

def htlcSuccessFeeSat (anchors : Bool) (r : FeeRate) : Nat :=
  if anchors then 0 else (feeForWeight r htlcSuccessWeight).val

theorem htlcTimeoutFeeSat_value (r : FeeRate) :
  htlcTimeoutFeeSat false r = r.msatPerKw * 663 / 1000

theorem htlcSuccessFeeSat_value (r : FeeRate) :
  htlcSuccessFeeSat false r = r.msatPerKw * 703 / 1000

theorem htlcTimeoutFeeSat_anchors (r : FeeRate) :
  htlcTimeoutFeeSat true r = 0

theorem htlcSuccessFeeSat_anchors (r : FeeRate) :
  htlcSuccessFeeSat true r = 0

def secondStageFeeAt (anchors : Bool) (r : FeeRate) (dir : Direction) : Nat :=
  secondStageFee dir (htlcTimeoutFeeSat anchors r) (htlcSuccessFeeSat anchors r)

theorem secondStageFeeAt_local (anchors : Bool) (r : FeeRate) :
  secondStageFeeAt anchors r .local = htlcTimeoutFeeSat anchors r

theorem secondStageFeeAt_remote (anchors : Bool) (r : FeeRate) :
  secondStageFeeAt anchors r .remote = htlcSuccessFeeSat anchors r

theorem secondStageFeeAt_anchors (r : FeeRate) (dir : Direction) :
  secondStageFeeAt true r dir = 0

theorem secondStageFeeAt_noAnchors (r : FeeRate) (dir : Direction) :
  secondStageFeeAt false r dir =
    if dir = .local then r.msatPerKw * 663 / 1000
    else r.msatPerKw * 703 / 1000
```

### 3.2 Per-output fee and gross value

```lean
def htlcFeeOf (timeoutFeeSat successFeeSat : Nat)
    (h : CommitmentHTLCOutput) : Nat :=
  secondStageFee h.direction timeoutFeeSat successFeeSat

theorem htlcFeeOf_local (t s : Nat) (h : CommitmentHTLCOutput)
    (hd : h.direction = .local) : htlcFeeOf t s h = t

theorem htlcFeeOf_remote (t s : Nat) (h : CommitmentHTLCOutput)
    (hd : h.direction = .remote) : htlcFeeOf t s h = s

def secondStageFeeTotal (timeoutFeeSat successFeeSat : Nat)
    (hs : List CommitmentHTLCOutput) : Nat :=
  (hs.map (htlcFeeOf timeoutFeeSat successFeeSat)).sum

theorem secondStageFeeTotal_nil (t s : Nat) :
  secondStageFeeTotal t s [] = 0

theorem secondStageFeeTotal_cons (t s : Nat) (h : CommitmentHTLCOutput)
    (hs : List CommitmentHTLCOutput) :
  secondStageFeeTotal t s (h :: hs) =
    htlcFeeOf t s h + secondStageFeeTotal t s hs

theorem secondStageFeeTotal_append (t s : Nat)
    (xs ys : List CommitmentHTLCOutput) :
  secondStageFeeTotal t s (xs ++ ys) =
    secondStageFeeTotal t s xs + secondStageFeeTotal t s ys

def grossHtlcValue (timeoutFeeSat successFeeSat : Nat)
    (h : CommitmentHTLCOutput) : Nat :=
  h.amountSat + htlcFeeOf timeoutFeeSat successFeeSat h

theorem grossHtlcValue_eq (t s : Nat) (h : CommitmentHTLCOutput) :
  grossHtlcValue t s h = h.amountSat + htlcFeeOf t s h

theorem grossHtlcValue_eq_of_net_add_fee {g : Nat} (t s : Nat)
    (h : CommitmentHTLCOutput)
    (hgross : h.amountSat + htlcFeeOf t s h = g) :
  grossHtlcValue t s h = g

def grossTotal (hs : List HTLCRecord) : Nat :=
  (hs.map (fun h => Msat.toSatFloor h.amountMsat)).sum
```

`CommitmentHTLCOutput.amountSat` is the **net** (post-second-stage-fee) value
in the current model.  `grossHtlcValue` recovers the gross amount by adding
the withheld fee back.

### 3.3 Legacy and net projections of an `HTLCRecord`

```lean
def legacyHtlcOutput (h : HTLCRecord) : CommitmentHTLCOutput :=
  { direction := h.direction
    amountSat := Msat.toSatFloor h.amountMsat
    cltvExpiry := h.cltvExpiry
    state := h.state }

def netHtlcOutput (timeoutFeeSat successFeeSat : Nat)
    (h : HTLCRecord) : CommitmentHTLCOutput :=
  { direction := h.direction
    amountSat := htlcOutputValue h timeoutFeeSat successFeeSat
    cltvExpiry := h.cltvExpiry
    state := h.state }

theorem legacyHtlcOutput_amountSat (h : HTLCRecord) :
  (legacyHtlcOutput h).amountSat = Msat.toSatFloor h.amountMsat

theorem legacyHtlcOutput_direction (h : HTLCRecord) :
  (legacyHtlcOutput h).direction = h.direction

theorem legacyHtlcOutput_cltvExpiry (h : HTLCRecord) :
  (legacyHtlcOutput h).cltvExpiry = h.cltvExpiry

theorem netHtlcOutput_amountSat (t s : Nat) (h : HTLCRecord) :
  (netHtlcOutput t s h).amountSat = htlcOutputValue h t s

theorem netHtlcOutput_direction (t s : Nat) (h : HTLCRecord) :
  (netHtlcOutput t s h).direction = h.direction

theorem netHtlcOutput_cltvExpiry (t s : Nat) (h : HTLCRecord) :
  (netHtlcOutput t s h).cltvExpiry = h.cltvExpiry

theorem htlcFeeOf_netHtlcOutput (t s : Nat) (h : HTLCRecord) :
  htlcFeeOf t s (netHtlcOutput t s h) = secondStageFee h.direction t s

theorem netHtlcOutput_eq_legacy_of_zero (h : HTLCRecord) :
  netHtlcOutput 0 0 h = legacyHtlcOutput h

theorem netHtlcOutput_add_fee (t s : Nat) (h : HTLCRecord)
    (hfee : secondStageFee h.direction t s ≤ Msat.toSatFloor h.amountMsat) :
  (netHtlcOutput t s h).amountSat +
      htlcFeeOf t s (netHtlcOutput t s h) =
    (legacyHtlcOutput h).amountSat

theorem htlcOutputsValue_map_legacy (hs : List HTLCRecord) :
  htlcOutputsValue (hs.map legacyHtlcOutput) = grossTotal hs

theorem htlcGroup_legacy_eq_net_add_fees (t s : Nat)
    (hs : List HTLCRecord)
    (hfees : ∀ h ∈ hs,
      secondStageFee h.direction t s ≤ Msat.toSatFloor h.amountMsat) :
  htlcOutputsValue (hs.map legacyHtlcOutput) =
    htlcOutputsValue (hs.map (netHtlcOutput t s)) +
      secondStageFeeTotal t s (hs.map (netHtlcOutput t s))

theorem htlcGroup_legacy_eq_net_of_zeroFee (hs : List HTLCRecord) :
  htlcOutputsValue (hs.map legacyHtlcOutput) =
    htlcOutputsValue (hs.map (netHtlcOutput 0 0))
```

### 3.4 Trimming threshold in gross terms

```lean
def htlcDustThreshold (dustLimitSat timeoutFeeSat successFeeSat : Nat)
    (h : CommitmentHTLCOutput) : Nat :=
  dustLimitSat + htlcFeeOf timeoutFeeSat successFeeSat h

theorem htlcDustThreshold_eq (d t s : Nat) (h : CommitmentHTLCOutput) :
  htlcDustThreshold d t s h = d + htlcFeeOf t s h

theorem net_value_lt_dust_iff_threshold {h : HTLCRecord} {d t s : Nat}
    (hd : 0 < d) :
  htlcOutputValue h t s < d ↔
    Msat.toSatFloor h.amountMsat < d + secondStageFee h.direction t s

theorem net_value_ge_dust_iff_threshold {h : HTLCRecord} {d t s : Nat}
    (hd : 0 < d) :
  d ≤ htlcOutputValue h t s ↔
    d + secondStageFee h.direction t s ≤ Msat.toSatFloor h.amountMsat

theorem isDustHTLC_iff_gross_lt_threshold {h : HTLCRecord} {d t s : Nat}
    (hd : 0 < d) :
  isDustHTLC h d t s = true ↔
    Msat.toSatFloor h.amountMsat < d + secondStageFee h.direction t s

theorem hasOutput_iff_threshold {h : HTLCRecord} {d t s : Nat}
    (hd : 0 < d) :
  hasOutput h d t s = true ↔
    d + secondStageFee h.direction t s ≤ Msat.toSatFloor h.amountMsat

theorem htlcOutput_net_none_iff (tx : CommitmentTx) (h : HTLCRecord)
    (t s : Nat) (hd : 0 < tx.dustLimitSat) :
  tx.htlcOutput (netHtlcOutput t s h) = none ↔
    Msat.toSatFloor h.amountMsat <
      tx.dustLimitSat + secondStageFee h.direction t s
```

### 3.5 Trim view and partition

```lean
def survivingRecords (dustLimitSat timeoutFeeSat successFeeSat : Nat)
    (hs : List HTLCRecord) : List HTLCRecord :=
  hs.filter (fun h => hasOutput h dustLimitSat timeoutFeeSat successFeeSat)

def trimmedRecords (dustLimitSat timeoutFeeSat successFeeSat : Nat)
    (hs : List HTLCRecord) : List HTLCRecord :=
  hs.filter (fun h => isDustHTLC h dustLimitSat timeoutFeeSat successFeeSat)

def survivingNetOutputs (dustLimitSat timeoutFeeSat successFeeSat : Nat)
    (hs : List HTLCRecord) : List CommitmentHTLCOutput :=
  (survivingRecords dustLimitSat timeoutFeeSat successFeeSat hs).map
    (netHtlcOutput timeoutFeeSat successFeeSat)

def survivorNetTotal (dustLimitSat timeoutFeeSat successFeeSat : Nat)
    (hs : List HTLCRecord) : Nat :=
  htlcOutputsValue
    (survivingNetOutputs dustLimitSat timeoutFeeSat successFeeSat hs)

def survivorFeeTotal (dustLimitSat timeoutFeeSat successFeeSat : Nat)
    (hs : List HTLCRecord) : Nat :=
  ((survivingRecords dustLimitSat timeoutFeeSat successFeeSat hs).map
    (fun h => secondStageFee h.direction timeoutFeeSat successFeeSat)).sum

def trimmedGrossTotal (dustLimitSat timeoutFeeSat successFeeSat : Nat)
    (hs : List HTLCRecord) : Nat :=
  ((trimmedRecords dustLimitSat timeoutFeeSat successFeeSat hs).map
    (fun h => Msat.toSatFloor h.amountMsat)).sum

theorem survivingRecords_zero (hs : List HTLCRecord) :
  survivingRecords 0 0 0 hs = hs

theorem survivingNetOutputs_zero (hs : List HTLCRecord) :
  survivingNetOutputs 0 0 0 hs = hs.map legacyHtlcOutput

theorem grossTotal_eq_partition (d t s : Nat) (hd : 0 < d)
    (hs : List HTLCRecord) :
  grossTotal hs =
    survivorNetTotal d t s hs + survivorFeeTotal d t s hs +
      trimmedGrossTotal d t s hs
```

This partition is the exact value accounting CH-02 asks for: every gross HTLC
amount is either paid to a surviving net output, withheld as that output's
second-stage fee, or trimmed and added to the commitment fee.

### 3.6 Legacy output view of the rich model

```lean
theorem toCommitmentOutput_value_of_nonAnchor (o : CommitmentTxOutput)
    (hl : o.kind ≠ .localAnchor) (hr : o.kind ≠ .remoteAnchor) :
  (o.toCommitmentOutput).value = o.valueSat

theorem outputs_toCommitmentOutput_value_eq (tx : CommitmentTx)
    {o : CommitmentTxOutput} (ho : o ∈ tx.outputs) :
  (o.toCommitmentOutput).value = o.valueSat

def legacyOutputs (tx : CommitmentTx) : List CommitmentOutput :=
  tx.outputs.map CommitmentTxOutput.toCommitmentOutput

def trimmedValue (tx : CommitmentTx) : Nat :=
  (if tx.dustLimitSat ≤ tx.commitment.toLocalSat then 0
    else tx.commitment.toLocalSat) +
  (if tx.dustLimitSat ≤ tx.commitment.toRemoteSat then 0
    else tx.commitment.toRemoteSat) +
  (tx.commitment.htlcs.map (fun h =>
    if tx.dustLimitSat ≤ h.amountSat then 0 else h.amountSat)).sum

theorem filterMap_htlc_valueSat_sum (tx : CommitmentTx)
    (hs : List CommitmentHTLCOutput) :
  ((hs.filterMap tx.htlcOutput).map (fun o => o.valueSat)).sum =
    (hs.map (fun h =>
      if tx.dustLimitSat ≤ h.amountSat then h.amountSat else 0)).sum

theorem kept_trimmed_value_split (d : Nat)
    (hs : List CommitmentHTLCOutput) :
  (hs.map (fun h => if d ≤ h.amountSat then h.amountSat else 0)).sum +
      (hs.map (fun h => if d ≤ h.amountSat then 0 else h.amountSat)).sum =
    (hs.map (fun h => h.amountSat)).sum

theorem outputsUnsorted_value_sum_add_trimmedValue (tx : CommitmentTx) :
  ((tx.outputsUnsorted.map CommitmentTxOutput.toCommitmentOutput).map
      CommitmentOutput.value).sum + trimmedValue tx =
    tx.commitment.totalOutputValue

theorem legacyOutputs_sum_add_trimmedValue (tx : CommitmentTx) :
  ((legacyOutputs tx).map CommitmentOutput.value).sum + trimmedValue tx =
    tx.commitment.totalOutputValue

theorem trimmedValue_eq_zero_of_dust_zero (tx : CommitmentTx)
    (hdust : tx.dustLimitSat = 0) : trimmedValue tx = 0

theorem legacyOutputs_sum_eq_totalOutputValue (tx : CommitmentTx)
    (hdust : tx.dustLimitSat = 0) :
  ((legacyOutputs tx).map CommitmentOutput.value).sum =
    tx.commitment.totalOutputValue

theorem legacyOutputs_values_sorted (tx : CommitmentTx) :
  ((legacyOutputs tx).map CommitmentOutput.value).Pairwise (· ≤ ·)

theorem legacyOutputs_perm_commitmentOutputs (tx : CommitmentTx)
    (hdust : tx.dustLimitSat = 0)
    (hl : tx.commitment.toLocalSat ≠ 0)
    (hr : tx.commitment.toRemoteSat ≠ 0) :
  (legacyOutputs tx).Perm tx.commitment.commitmentOutputs

theorem legacyOutputs_sum_eq_commitmentOutputs_sum (tx : CommitmentTx)
    (hdust : tx.dustLimitSat = 0) :
  ((legacyOutputs tx).map CommitmentOutput.value).sum =
    (tx.commitment.commitmentOutputs.map CommitmentOutput.value).sum
```

The relation is a **permutation**, not equality.  The rich list is sorted by
value/script/CLTV; the legacy list is emitted in group order.  A permutation
is the strongest relation that is actually true: it preserves the on-chain
output multiset while the rich model supplies the canonical order.  At
`dustLimitSat = 0` the sum is exactly `totalOutputValue`; this does not need
the non-zero-output hypotheses because an omitted zero-valued output
contributes zero.

### 3.7 Necessary hypotheses and retained D12 refutations

```lean
def dustDemoRecord : HTLCRecord :=
  { id := 0
    direction := .local
    amountMsat := ⟨500000⟩
    paymentHash := ⟨ByteArray.empty⟩
    cltvExpiry := 0
    state := .offered }

def dustDemoTx : CommitmentTx := ...

theorem dustDemoRecord_amountSat :
  (legacyHtlcOutput dustDemoRecord).amountSat = 500

theorem dustDemoTx_htlcOutput_none :
  dustDemoTx.htlcOutput (legacyHtlcOutput dustDemoRecord) = none

theorem dustDemoTx_outputs : dustDemoTx.outputs = []

theorem dustDemoTx_commitmentOutputs :
  dustDemoTx.commitment.commitmentOutputs =
    [CommitmentOutput.htlc .local 500]

theorem dust_trimming_not_perm :
  ¬ (legacyOutputs dustDemoTx).Perm
      dustDemoTx.commitment.commitmentOutputs

theorem legacy_ordering_refuted :
  ¬ (∀ c : Commitment,
      (c.commitmentOutputs.map CommitmentOutput.value).Pairwise (· ≤ ·)) :=
  LnLean.Proofs.WaveD.D12.waveD_d12_output_ordering_fails

theorem legacy_zero_value_htlc_emitted :
  CommitmentOutput.htlc .local 0 ∈
    LnLean.Proofs.WaveD.D12.zeroValueHtlcCommitment.commitmentOutputs :=
  LnLean.Proofs.WaveD.D12.waveD_d12_zero_value_htlc_emitted
```

`dust_trimming_not_perm` shows the zero-dust hypothesis is necessary: a
500-satoshi HTLC under a 1000-satoshi dust limit is trimmed by the rich model
but still emitted by `commitmentOutputs`.

### 3.8 Constructions, conservation, and refinement

```lean
def anchorTotal (anchors : Bool) : Nat :=
  if anchors then 2 * anchorOutputSat else 0

theorem anchorTotal_eq_if (anchors : Bool) :
  anchorTotal anchors = if anchors then 2 * anchorOutputSat else 0

theorem anchorTotal_eq_anchorOutputValue (c : Commitment) :
  c.anchorOutputValue = anchorTotal c.anchorOutputs

def legacyCommitmentOfRecords (holder : Direction) (number funding fee toLocal
    contestDelay : Nat) (anchors : Bool) (hs : List HTLCRecord) : Commitment :=
  { holder := holder
    commitmentNumber := number
    fundingValueSat := funding
    toLocalSat := toLocal
    toRemoteSat := funding - fee - toLocal - grossTotal hs - anchorTotal anchors
    htlcs := hs.map legacyHtlcOutput
    feeSat := fee
    contestDelay := contestDelay
    anchorOutputs := anchors }

def netCommitmentOfRecords (holder : Direction) (number funding fee toLocal
    contestDelay : Nat) (anchors : Bool) (d t s : Nat)
    (hs : List HTLCRecord) : Commitment :=
  { holder := holder
    commitmentNumber := number
    fundingValueSat := funding
    toLocalSat := toLocal
    toRemoteSat := funding - fee - toLocal - survivorNetTotal d t s hs -
      anchorTotal anchors
    htlcs := survivingNetOutputs d t s hs
    feeSat := fee
    contestDelay := contestDelay
    anchorOutputs := anchors }

def bolt3CommitmentOfRecords (holder : Direction) (number funding fee toLocal
    contestDelay : Nat) (anchors : Bool) (d t s : Nat)
    (hs : List HTLCRecord) : Commitment :=
  { holder := holder
    commitmentNumber := number
    fundingValueSat := funding
    toLocalSat := toLocal
    toRemoteSat := funding - fee - toLocal - grossTotal hs - anchorTotal anchors
    htlcs := survivingNetOutputs d t s hs
    feeSat := fee
    contestDelay := contestDelay
    anchorOutputs := anchors }

theorem legacyCommitmentOfRecords_conservation (holder : Direction)
    (number funding fee toLocal contestDelay : Nat) (anchors : Bool)
    (hs : List HTLCRecord)
    (hfit : fee + toLocal + grossTotal hs + anchorTotal anchors ≤ funding) :
  (legacyCommitmentOfRecords holder number funding fee toLocal contestDelay
      anchors hs).totalOutputValue + fee = funding

theorem netCommitmentOfRecords_conservation (holder : Direction)
    (number funding fee toLocal contestDelay : Nat) (anchors : Bool)
    (d t s : Nat) (hs : List HTLCRecord)
    (hfit : fee + toLocal + survivorNetTotal d t s hs +
      anchorTotal anchors ≤ funding) :
  (netCommitmentOfRecords holder number funding fee toLocal contestDelay
      anchors d t s hs).totalOutputValue + fee = funding

theorem bolt3CommitmentOfRecords_conservation (holder : Direction)
    (number funding fee toLocal contestDelay : Nat) (anchors : Bool)
    (d t s : Nat) (hs : List HTLCRecord) (hd : 0 < d)
    (hfit : fee + toLocal + grossTotal hs + anchorTotal anchors ≤ funding) :
  (bolt3CommitmentOfRecords holder number funding fee toLocal contestDelay
      anchors d t s hs).totalOutputValue + fee +
      survivorFeeTotal d t s hs + trimmedGrossTotal d t s hs = funding

theorem bolt3CommitmentOfRecords_zero_eq_legacy (holder : Direction)
    (number funding fee toLocal contestDelay : Nat) (anchors : Bool)
    (hs : List HTLCRecord) :
  bolt3CommitmentOfRecords holder number funding fee toLocal contestDelay
      anchors 0 0 0 hs =
    legacyCommitmentOfRecords holder number funding fee toLocal contestDelay
      anchors hs

theorem netCommitmentOfRecords_zero_eq_legacy (holder : Direction)
    (number funding fee toLocal contestDelay : Nat) (anchors : Bool)
    (hs : List HTLCRecord) :
  netCommitmentOfRecords holder number funding fee toLocal contestDelay
      anchors 0 0 0 hs =
    legacyCommitmentOfRecords holder number funding fee toLocal contestDelay
      anchors hs

theorem richOutputs_refine_legacyCommitment (tx : CommitmentTx)
    (holder : Direction) (number funding fee toLocal contestDelay : Nat)
    (anchors : Bool) (hs : List HTLCRecord)
    (hcommit : tx.commitment =
      netCommitmentOfRecords holder number funding fee toLocal contestDelay
        anchors 0 0 0 hs)
    (hdust : tx.dustLimitSat = 0)
    (hl : tx.commitment.toLocalSat ≠ 0)
    (hr : tx.commitment.toRemoteSat ≠ 0) :
  (legacyOutputs tx).Perm
    (legacyCommitmentOfRecords holder number funding fee toLocal contestDelay
      anchors hs).commitmentOutputs
```

`bolt3CommitmentOfRecords_conservation` is the CH-02 accounting theorem:
the effective fee `funding - totalOutputValue` is exactly
`base fee + withheld second-stage fees + trimmed gross value`.

`richOutputs_refine_legacyCommitment` is conditional on
`tx.commitment = netCommitmentOfRecords ... 0 0 0 hs`, i.e. zero dust and zero
second-stage fees.  That is exactly the regime in which the legacy
`Commitment` record is sound; outside it the legacy record has no place to
put the withheld fee.

## 4. Axiom audit

Scratch file `/tmp/opencode/axioms_s4.lean` (not part of the repository) ran
`#print axioms` on every exported theorem.  Results:

```text
htlcTimeoutFeeSat_value                                  no axioms
htlcSuccessFeeSat_value                                  no axioms
secondStageFeeAt_anchors                                 no axioms
secondStageFeeAt_noAnchors                               no axioms
grossTotal_eq_partition                                  propext, Quot.sound
legacyOutputs_perm_commitmentOutputs                     propext, Quot.sound
legacyOutputs_values_sorted                              propext, Classical.choice, Quot.sound
legacyOutputs_sum_add_trimmedValue                       propext, Quot.sound
legacyOutputs_sum_eq_totalOutputValue                    propext, Quot.sound
legacyOutputs_sum_eq_commitmentOutputs_sum               propext, Quot.sound
dust_trimming_not_perm                                   propext, Quot.sound
legacy_ordering_refuted                                  propext, Quot.sound
legacy_zero_value_htlc_emitted                           propext
legacyCommitmentOfRecords_conservation                   propext, Quot.sound
netCommitmentOfRecords_conservation                      propext, Quot.sound
bolt3CommitmentOfRecords_conservation                    propext, Quot.sound
bolt3CommitmentOfRecords_zero_eq_legacy                  propext, Quot.sound
netCommitmentOfRecords_zero_eq_legacy                    propext, Quot.sound
richOutputs_refine_legacyCommitment                      propext, Quot.sound
```

No theorem depends on `sorryAx`, `Classical.choice` beyond the standard
`List.Pairwise`/sort infrastructure, or any user axiom.  `legacyOutputs_values_sorted`
inherits `Classical.choice` from the existing `sortOutputs_pairwise` path in
`Commitment.lean`; it is not introduced by this lane.

## 5. Forbidden-construct grep

Command:

```sh
cd /home/ubuntu/ln-lean-repair
grep -nE '\b(sorry|axiom|admit|native_decide|unsafe|implemented_by)\b' \
  LnLean/Proofs/Channel/CommitmentIntegrationTargets.lean
```

Observed output:

```text
NO_FORBIDDEN_TOKENS
```

The same grep on this report is expected to match only the literal list of
forbidden names in this paragraph; the module itself has no match.

## 6. Why `List.Perm` and not equality

- `CommitmentTx.outputs` is `sortOutputs tx.outputsUnsorted`; it is sorted by
  `(value, script, CLTV)`.
- `Commitment.commitmentOutputs` emits `to_local`, then `to_remote`, then
  HTLCs in record order, then anchors.  It applies no sort.
- D12's `waveD_d12_output_ordering_fails` gives a concrete commitment whose
  legacy output values are not nondecreasing.  Therefore no equality or
  sortedness theorem at the `commitmentOutputs` level can be true.
- At `dustLimitSat = 0` and non-zero `to_local`/`to_remote`, the two lists have
  the same elements (the rich model may additionally emit a zero-valued
  `to_local`/`to_remote`, which the legacy function omits; the non-zero
  hypotheses exclude that case).  Hence `List.Perm` is the strongest true
  relation.
- The sum theorem `legacyOutputs_sum_eq_totalOutputValue` holds at zero dust
  without the non-zero hypotheses, because an omitted zero-valued output
  contributes zero.

## 7. Scope caveats

This module is value-and-kind arithmetic over the existing records.  It does
**not** model:

- Script execution, signature checks, witnesses, sighash, or the actual BOLT 3
  script templates.  Only the `scriptPubKey` bytes already carried by
  `CommitmentTx` are passed through.
- `option_anchors` second-stage fees are zero, as BOLT 3 prescribes.  Anchor
  presence remains the model's "both anchors iff `anchorOutputs`" convention;
  the single-anchor exception is out of scope, as in
  `CommitmentTx.outputs_spec`.
- `zero_fee_commitments` (`shared_anchor`), fee bumping, and CPFP economics.
- Consensus-level transaction validity, package limits, or mempool policy.
- The net/gross convention of the current `CommitmentHTLCOutput.amountSat`.
  In this module `amountSat` is treated as the **net** value that the rich
  model emits; `grossHtlcValue` recovers gross.  The module does not claim
  that this convention is BOLT-3-exact.  Section 8 gives the exact patch
  needed to make it exact.
- Cross-implementation equivalence with rust-lightning.  The docstring records
  the relevant `chan_utils.rs` anchors, but no Rust code is executed or
  extracted.
- The refinement `richOutputs_refine_legacyCommitment` is conditional on
  zero dust and zero second-stage fees.  It is not an unconditional
  equivalence between the rich and legacy models.

BOLT anchors used:

- BOLT 3 §Trimmed Outputs (`refs/bolts/03-transactions.md:305-354`):
  HTLC output omitted when `amount - htlc_fee < dust_limit_satoshis`;
  equality kept; trimmed value added to fee.
- BOLT 3 §Fee Calculation (`refs/bolts/03-transactions.md:464-535`):
  HTLC-timeout weight 663, HTLC-success weight 703 without anchors; both
  second-stage transactions pay zero fee with `option_anchors`.
- BOLT 3 §Offered HTLC Outputs / §Received HTLC Outputs
  (`refs/bolts/03-transactions.md:199-304`): surviving HTLC output value is
  the protocol amount net of the direction-dependent second-stage fee.
- rust-lightning `lightning/src/ln/chan_utils.rs:919-941`
  (`build_htlc_output` subtracts the second-stage fee) and `:1958-1975`
  (`build_htlc_outputs` uses `to_bitcoin_amount` for the commitment output).
  The two conventions differ by exactly the withheld second-stage fee; this
  module makes that difference explicit.

## 8. Integration patch needed

This lane is forbidden to edit `LnLean/Channel/Commitment.lean` or
`LnLean/Channel/Types.lean`, so the following is a **proposal**, not an
applied change.  It is the minimal patch that makes the commitment output
value BOLT-3-exact while keeping every existing record and D12 refutation
valid.

### 8.1 `LnLean/Channel/Types.lean`

Add a net-value field with a default that preserves all existing literals:

```lean
structure CommitmentHTLCOutput where
  direction : Direction
  /-- Gross value carried by the commitment output.  This is the BOLT 3
      `amount_msat` denominated in satoshis. -/
  amountSat : Nat
  cltvExpiry : Height
  state : HTLCState
  /-- Net value paid by the second-stage transaction.  The default keeps the
      current net-value convention for every existing record. -/
  netAmountSat : Nat := amountSat
deriving Repr, DecidableEq, BEq
```

Add the trimmed-value field to `Commitment` (default zero preserves existing
records):

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

### 8.2 `LnLean/Channel/Commitment.lean`

Change the trimming test to use the net value while the output keeps the gross
value:

```lean
def CommitmentTx.htlcOutput (tx : CommitmentTx) (h : CommitmentHTLCOutput) :
    Option CommitmentTxOutput :=
  if tx.dustLimitSat ≤ h.netAmountSat then
    some (CommitmentTxOutput.htlc h (tx.htlcScript h))
  else none
```

`CommitmentTxOutput.htlc` already sets `valueSat := h.amountSat`, so with
`amountSat` gross the commitment output is gross-faithful.
`Commitment.commitmentOutputs` already emits `h.amountSat`, so it needs no
change in shape; it now emits gross values.

Add the effective-fee view and the accounting obligation:

```lean
def Commitment.effectiveFeeSat (c : Commitment) : Nat :=
  c.fundingValueSat - c.totalOutputValue

theorem Commitment.effectiveFee_eq (c : Commitment) (t s : Nat)
    (hbal : c.totalOutputValue ≤ c.fundingValueSat)
    (hnet : ∀ h ∈ c.htlcs,
      h.netAmountSat + secondStageFee h.direction t s = h.amountSat) :
    c.effectiveFeeSat =
      c.feeSat + secondStageFeeTotal t s c.htlcs + c.trimmedSat := by
  -- Follow-up obligation; the proof is the same partition as
  -- `grossTotal_eq_partition` lifted to `Commitment`.
```

(The proof body above is a **proposal placeholder**, not repository code.
The follow-up lane must prove the obligation or state it as an explicit
hypothesis.)

### 8.3 Migration of legacy consumers

1. Construction sites that currently write
   `{ amountSat := net, ... }` must become
   `{ amountSat := gross, netAmountSat := net, ... }`.  Sites that intend
   `gross = net` can omit `netAmountSat` and keep current behavior.
2. Consumers that enumerate on-chain outputs keep calling
   `Commitment.commitmentOutputs`; after the patch it emits gross values.
3. Proofs that use `amountSat` simultaneously as the commitment value and as
   the second-stage value must either:
   - keep the default `netAmountSat = amountSat` (the current zero-fee
     regime), or
   - carry `hnet : h.netAmountSat + secondStageFee h.direction t s = h.amountSat`
     and rewrite with it.
4. The rich-model trimming lemmas
   (`CommitmentTx.nonAnchor_output_value_ge_dust`, `mem_htlcOutput_iff`,
   `htlcOutput_mem_outputs`) must be restated with `netAmountSat` in the dust
   test and `amountSat` in the emitted value.  The statements in this lane
   already separate the two roles (`netHtlcOutput` for trimming,
   `grossHtlcValue` for gross), so they are the template for that migration.
5. D12 and the legacy ordering refutations are unaffected: the patch changes
   values, not the fixed group order or the zero-valued-HTLC emission.

Representative consumer files to audit after the patch
(`grep -rl commitmentOutputs LnLean --include=*.lean`):

`LnLean/Proofs/Conservation.lean`,
`LnLean/Proofs/Channel/CommitmentTxProps.lean`,
`LnLean/Proofs/Channel/CommitmentOrderTargets.lean`,
`LnLean/Proofs/PhaseC3/FeeWeightDust.lean`,
`LnLean/Proofs/PhaseC3/EndToEndConservation.lean`,
`LnLean/Proofs/WaveD/D11.lean`, `D12.lean`, `D42.lean`, `D43.lean`,
`D46.lean`, `D47.lean`,
`LnLean/Proofs/WaveE/E45.lean`, `E48.lean`,
`LnLean/Proofs/Obligations.lean`, `LnLean/Proofs/Traceability.lean`,
`LnLean/Proofs/PhaseC3/AxiomAudit.lean`.

Until that patch lands, the current module's `legacyHtlcOutput` /
`netHtlcOutput` split is the correct local model: it makes the net/gross
difference explicit and proves exactly how much value the legacy convention
omits.

## 9. Reproduction checklist

```sh
cd /home/ubuntu/ln-lean-repair
export PATH=/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH

# 1. Direct compile
LEAN_NUM_THREADS=1 lake env lean \
  LnLean/Proofs/Channel/CommitmentIntegrationTargets.lean

# 2. Required build
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Proofs.Channel.CommitmentIntegrationTargets

# 3. Axiom audit (scratch file, not committed)
#    /tmp/opencode/axioms_s4.lean contains #print axioms for every export.
LEAN_NUM_THREADS=1 lake env lean /tmp/opencode/axioms_s4.lean

# 4. Forbidden constructs
grep -nE '\b(sorry|axiom|admit|native_decide|unsafe|implemented_by)\b' \
  LnLean/Proofs/Channel/CommitmentIntegrationTargets.lean
```
