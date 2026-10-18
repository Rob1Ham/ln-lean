# C01-COMMITMENT — commitment output nonnegativity and ordering

## 1. Scope and build evidence

Owned files only:

| File | Change |
|---|---|
| `LnLean/Channel/Commitment.lean` | appended model-level nonnegativity, sum, conservation-bound, and trimming theorems before `end LnLean.Channel`; no existing declaration or comment was modified |
| `agents/reports/C01-COMMITMENT.md` | this report |

No other Lean file, `Obligations.lean`, `Traceability.lean`, `scripts/`, or
`vendor/` was edited.

Build commands (one Lean process at a time under the shared lock):

```sh
cd /home/ubuntu/ln-lean-repair
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake env lean LnLean/Channel/Commitment.lean
# no output, RC 0

LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Channel.Commitment
# ✔ [11/11] Built LnLean.Channel.Commitment (845ms)
# Build completed successfully (11 jobs). RC 0
```

`lake build -j1 ...` is rejected by this workspace's Lake 5.0.0
(`error: unknown short option '-j'`), so the equivalent single-target build was
run without `-j`.

Downstream sanity checks, after the change (all RC 0):

```sh
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake env lean LnLean/Proofs/WaveD/D12.lean
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake env lean LnLean/Proofs/WaveE/E45.lean
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Proofs.Conservation LnLean.Proofs.PhaseC2.CommitmentAlgebra
# ✔ [14/14] ... Build completed successfully (14 jobs). RC 0
```

`grep -nE "sorry|axiom|admit|native_decide|unsafe|implemented_by"
LnLean/Channel/Commitment.lean` returns no matches (RC 1 from grep). No new
imports were added.

## 2. Catalog rows

| Row | Claim | Declared `leanTarget` | Status after this lane | Verdict |
|---|---|---|---|---|
| `LN-CH-002` | "No commitment output has a negative value and the output sum stays within the funding value." | `LnLean.Channel.Commitment.outputs_nonnegative` | `statementOnly` | **not promotion-ready as the exact claim**; the nonnegativity half is fully proved, the funding half is proved only under conservation. Details below. |
| `LN-CH-003` | "Commitment outputs are ordered by value then script, and dust HTLCs are trimmed." | `LnLean.Channel.Commitment.output_ordering` | `statementOnly` | **not promotion-ready**; D12 mechanically refutes the unconditional ordering claim and the model cannot represent the script/CLTV key. Model-level trimming facts were added, but the dust filter itself remains outside `commitmentOutputs`. |

### LN-CH-002 — why it stays `statementOnly`

The catalog claim is an unconditional conjunction.  Its first half is true
unconditionally in this model because every value field is a `Nat`: a negative
`CommitmentOutput.value` cannot be constructed.  Its second half is *not* a
consequence of the record type.  `Commitment` has no well-formedness
invariant tying `fundingValueSat` to `toLocalSat`/`toRemoteSat`/`htlcs`, and
`LnLean.Proofs.WaveD.D46` already mechanizes a model-legal record with
`fundingValueSat = 100` and `toLocalSat = 500` whose output sum exceeds
funding (`waveD_d46_unconditional_counterexample`).  Therefore the exact
unconditional target `outputs_nonnegative` was deliberately **not** declared:
doing so would either state something false or silently change the claim.
The true model-level results are named separately below, and the combined
conditional theorem states both halves under the BOLT 3 balance equation.

The proof layer's `CommitmentConserved` is definitionally
`c.totalOutputValue + c.feeSat = c.fundingValueSat`
(`LnLean/Proofs/Conservation.lean:90`).  Importing that module into
`LnLean/Channel/Commitment.lean` would invert the dependency, so the model
theorems take the equality as an explicit hypothesis.  No information is lost:
`CommitmentConserved` unfolds to exactly that equality.

### LN-CH-003 — why it stays `statementOnly`

`LnLean.Proofs.WaveD.D12` preserves and was rechecked:

* `waveD_d12_commitmentOutputs_not_value_sorted` and
  `waveD_d12_output_ordering_fails`: the model's fixed
  `to_local, to_remote, HTLCs, anchors` order is **not** value-sorted, so no
  unconditional `output_ordering` theorem was added.
* `waveD_d12_cltv_tiebreak_not_recoverable`: `CommitmentOutput` carries
  neither `scriptPubKey` nor HTLC `cltvExpiry`, so BOLT 3's
  `(value, script, cltv_expiry)` key is not representable on the model's output
  type.  The strongest true ordering result remains D12's external-key
  conditional `waveD_d12_output_ordering_conditional`.
* `waveD_d12_dust_htlc_trimmed`,
  `waveD_d12_nonDust_htlc_kept`,
  `waveD_d12_htlcOutput_value_ge_dust`, and
  `waveD_d12_htlc_output_present_iff`: the exact BOLT 3 dust filter over
  `HTLCRecord`.
* `waveD_d12_zero_value_htlc_emitted` and
  `waveD_d12_dust_trimming_requires_filter`: `commitmentOutputs` alone does
  **not** apply that filter.

This lane added only true model-level trimming facts (zero-valued
`to_local`/`to_remote` are trimmed, HTLC membership is verbatim, and a
pre-trimmed HTLC list yields no sub-dust HTLC output).  It did not duplicate or
weaken D12's counterexample or its conditional sorted theorem.

## 3. Declarations added

All are in `namespace LnLean.Channel`, appended after
`commitmentPair_toLocal_asymmetry` in `LnLean/Channel/Commitment.lean`
(the new section runs from the `LN-CH-002` doc comment through the last
theorem before `end LnLean.Channel`).

### Nonnegativity (first half of LN-CH-002)

| Declaration | Statement |
|---|---|
| `CommitmentOutput.value_nonneg` | `0 ≤ o.value` for every `o : CommitmentOutput` |
| `CommitmentOutput.value_nonneg_int` | `0 ≤ (o.value : Int)` |
| `Commitment.commitmentOutputs_value_nonneg` | `∀ o ∈ c.commitmentOutputs, 0 ≤ o.value` |
| `Commitment.commitmentOutputs_value_nonneg_int` | `∀ o ∈ c.commitmentOutputs, 0 ≤ (o.value : Int)` |
| `Commitment.commitmentOutputs_sum_nonneg` | `0 ≤ (c.commitmentOutputs.map CommitmentOutput.value).sum` |
| `Commitment.totalOutputValue_nonneg` | `0 ≤ c.totalOutputValue` |
| `Commitment.totalOutputValue_nonneg_int` | `0 ≤ (c.totalOutputValue : Int)` |

### Sum identity

| Declaration | Statement |
|---|---|
| `Commitment.commitmentOutputs_sum_eq_totalOutputValue` | `(c.commitmentOutputs.map CommitmentOutput.value).sum = c.totalOutputValue` |

This is the model-level form of the identity previously available only through
the proof-layer `outputsValue` wrapper
(`Commitment.outputsValue_commitmentOutputs` in
`LnLean/Proofs/Channel/CommitmentTxProps.lean`).  It is stated directly on
`List.sum`, so no proof module needs to be imported into the model.

### Conservation-conditional funding bound (second half of LN-CH-002)

| Declaration | Statement |
|---|---|
| `Commitment.totalOutputValue_le_funding_of_fee` | `c.totalOutputValue + c.feeSat = c.fundingValueSat → c.totalOutputValue ≤ c.fundingValueSat` |
| `Commitment.commitmentOutputs_sum_le_funding_of_fee` | same hypothesis → `(c.commitmentOutputs.map CommitmentOutput.value).sum ≤ c.fundingValueSat` |
| `Commitment.outputs_nonneg_and_sum_le_funding_of_fee` | same hypothesis → `(∀ o ∈ c.commitmentOutputs, 0 ≤ (o.value : Int)) ∧ (sum ≤ c.fundingValueSat)` |

### Model-level trimming facts (LN-CH-003)

| Declaration | Statement |
|---|---|
| `Commitment.toLocal_mem_commitmentOutputs_iff` | `CommitmentOutput.toLocal v ∈ c.commitmentOutputs ↔ v = c.toLocalSat ∧ c.toLocalSat ≠ 0` |
| `Commitment.toRemote_mem_commitmentOutputs_iff` | `CommitmentOutput.toRemote v ∈ c.commitmentOutputs ↔ v = c.toRemoteSat ∧ c.toRemoteSat ≠ 0` |
| `Commitment.toLocal_zero_not_mem` | `CommitmentOutput.toLocal 0 ∉ c.commitmentOutputs` |
| `Commitment.toRemote_zero_not_mem` | `CommitmentOutput.toRemote 0 ∉ c.commitmentOutputs` |
| `Commitment.htlc_mem_commitmentOutputs_iff` | `CommitmentOutput.htlc dir v ∈ c.commitmentOutputs ↔ ∃ h ∈ c.htlcs, h.direction = dir ∧ h.amountSat = v` |
| `Commitment.htlc_mem_commitmentOutputs_value_ge` | if `∀ h ∈ c.htlcs, dustLimitSat ≤ h.amountSat`, then every emitted HTLC output value is at least `dustLimitSat` |

## 4. Proof approach

* **Nonnegativity.**  `CommitmentOutput.value` returns a `Nat` in every
  constructor, so `Nat.zero_le _` closes the `Nat` forms.  The `Int` forms use
  `exact_mod_cast`.  This is structural, not a side condition on the record.
* **Sum identity.**  Unfold `commitmentOutputs` into its four `++` groups.
  Split `List.map`/`List.sum` over append (`List.map_append`,
  `List.sum_append`).  Each `if value = 0 then [] else [output]` group sums to
  the corresponding field by cases on the condition.  The HTLC group is an
  induction on `c.htlcs`, using `CommitmentOutput.value (htlc _ v) = v` and
  the definition of `htlcOutputsValue`.  The anchor group evaluates
  `330 + 330 = 2 * 330`.  Finally `unfold Commitment.totalOutputValue` and
  `omega`.
* **Funding bound.**  The hypothesis is exactly
  `totalOutputValue + feeSat = fundingValueSat`; since `feeSat : Nat`, `omega`
  derives `totalOutputValue ≤ fundingValueSat`.  The emitted-sum version
  rewrites with the sum identity.  The combined theorem pairs the
  unconditional `Int` nonnegativity result with this conditional bound.
* **Trimming iffs.**  Unfold `commitmentOutputs`, case-split on
  `toLocalSat = 0` / `toRemoteSat = 0`; constructor disjointness and
  injectivity eliminate the other three groups.  Zero-value absence is the
  `v = 0` instance.  HTLC membership case-splits on all three flags and uses
  `List.mem_map` plus constructor injectivity; the pre-trimmed dust corollary
  extracts the matching `h ∈ c.htlcs` and applies the hypothesis.

No `sorry`, `axiom`, `admit`, `native_decide`, `unsafe`, or
`@[implemented_by]` was used.  No Mathlib import was added.

## 5. Promotion verdict

* **LN-CH-002: `statementOnly`.**  The nonnegativity half is fully mechanized
  and the funding half is mechanized under the BOLT 3 balance equation.  The
  row should not be marked `proved` by the exact name `outputs_nonnegative`
  because the catalog sentence is an unconditional conjunction and the
  funding half is false without conservation (witness in D46).  If the catalog
  is willing to split the row or record the conservation premise explicitly,
  the two halves are promotion-ready as separate claims.
* **LN-CH-003: `statementOnly`.**  The ordering half is false of
  `commitmentOutputs` as written (D12 counterexample) and its script/CLTV key
  is absent from `CommitmentOutput`.  Only D12's conditional external-key
  repair is true.  The dust half is true for the separate `HTLCRecord` filter,
  not for `commitmentOutputs` alone.  This lane's model-level trimming lemmas
  are supporting facts, not a replacement for the exact claim.
