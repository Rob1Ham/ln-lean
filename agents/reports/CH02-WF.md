# CH02-WF — exact target for `LN-CH-002`

Lane: `CH02-WF` (worktree `/home/ubuntu/ln-lean-repair`, branch
`repair/integrated`, HEAD `0caec3d`). Scope: **`LN-CH-002` only**.

## Verdict

- **Promote `LN-CH-002` to `proved`** by pointing the catalog at the exact
  target `LnLean.Channel.Commitment.outputs_nonnegative`, which now exists.
- Promotion is **conditional on the BOLT 3 balance equation** supplied as an
  explicit hypothesis. The catalog sentence is faithfully realized as a
  conjunction whose second conjunct assumes
  `c.totalOutputValue + c.feeSat = c.fundingValueSat`; the first conjunct
  (nonnegative outputs) is unconditional. Do **not** advertise the sum bound
  as an unconditional record-level theorem (D46 refutes it).
- No `LN-CH-003` target was added. Its unconditional ordering claim is refuted
  by D12 and the model still lacks script/CLTV data.

## Files changed

- `LnLean/Channel/Commitment.lean` — additive: one docstring + the exact
  theorem `Commitment.outputs_nonnegative`, placed immediately after C01's
  `Commitment.outputs_nonneg_and_sum_le_funding_of_fee`. No existing
  declaration, comment, or import was changed.
- `agents/reports/CH02-WF.md` — this report.

Read-only, unchanged: `LnLean/Proofs/Obligations.lean`,
`LnLean/Proofs/Traceability.lean`, `LnLean/Proofs/WaveD/D12.lean`,
`LnLean/Proofs/WaveD/D46.lean`, scripts, vendor, docs, root imports.

The working tree also contains modifications to `LnLean/Channel/HTLC.lean`
and `LnLean/Proofs/Liveness.lean` and an untracked
`agents/status/REPAIR.status`. These are other lanes' work; this lane did not
touch them, and `git diff -- LnLean/Channel/Commitment.lean` contains only the
19-line addition described above.

## Exact signature

```lean
theorem LnLean.Channel.Commitment.outputs_nonnegative (c : LnLean.Channel.Commitment)
    (h : c.totalOutputValue + c.feeSat = c.fundingValueSat) :
    (∀ (o : LnLean.Channel.CommitmentOutput),
        o ∈ c.commitmentOutputs → 0 ≤ ↑o.value) ∧
      (List.map LnLean.Channel.CommitmentOutput.value c.commitmentOutputs).sum
        ≤ c.fundingValueSat
```

Proof term: `Commitment.outputs_nonneg_and_sum_le_funding_of_fee c h` — the C01
combined theorem. No new structure, definition, hypothesis, or tautological
restatement was introduced; the funding bound is not assumed as a conclusion.

`#check` output (from a temporary `/tmp/opencode/CheckCH02.lean`, not added to
the repository):

```
LnLean.Channel.Commitment.outputs_nonnegative (c : LnLean.Channel.Commitment)
  (h : c.totalOutputValue + c.feeSat = c.fundingValueSat) :
  (∀ (o : LnLean.Channel.CommitmentOutput), o ∈ c.commitmentOutputs → 0 ≤ ↑o.value) ∧
    (List.map LnLean.Channel.CommitmentOutput.value c.commitmentOutputs).sum ≤ c.fundingValueSat
```

## Axioms

`#print axioms LnLean.Channel.Commitment.outputs_nonnegative`:

```
'LnLean.Channel.Commitment.outputs_nonnegative' depends on axioms: [propext, Quot.sound]
```

Only Lean's standard `propext` / `Quot.sound`; no `sorryAx`, no custom axioms.
For reference, the C01 ingredients report the same footprint:
`commitmentOutputs_sum_le_funding_of_fee` depends on
`[propext, Quot.sound]`, and `commitmentOutputs_value_nonneg` depends on no
axioms.

No `sorry`, `axiom`, `admit`, `native_decide`, `unsafe`, or
`@[implemented_by]` was added.

## Build evidence

Commands run sequentially under the shared lock, one Lean process at a time:

```
export PATH=/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake env lean LnLean/Channel/Commitment.lean
# RC=0

LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Channel.Commitment
# ✔ [11/11] Built LnLean.Channel.Commitment (855ms)
# Build completed successfully (11 jobs).
# RC=0
```

The `#check` / `#print axioms` run in the same locked environment also returned
RC=0.

## Model gap and scope caveat

- `Commitment` is a plain record with no well-formedness invariant:
  `fundingValueSat`, `feeSat`, and the output fields are independent `Nat`s.
  The sum bound therefore cannot be stated unconditionally. D46's checked
  counterexample `waveD_d46_unconditional_counterexample` proves
  `¬ (∀ c : Commitment, c.totalOutputValue ≤ c.fundingValueSat)`.
- `commitmentPairOfBalances` emits the two 330-sat anchor outputs without
  debiting them from the funder, so the sum bound also fails for that builder
  with anchors enabled and zero fee. This is preserved in D46's
  `waveD_d46_pair_anchor_counterexample`.
- Nonnegativity is structural only in the channel model: output values are
  `Nat`. The L1 script-template layer `LnLean.Bitcoin.CommitmentOutput` uses a
  signed `BtcAmount`; E45 records a counterexample there. The new target is
  about `LnLean.Channel.CommitmentOutput`, as the catalog name requires.
- `CommitmentOutput` carries neither a script nor an HTLC expiry, so BOLT 3's
  `(value, script, cltv)` ordering key is not representable. D12's
  `waveD_d12_output_ordering_fails` refutes the unconditional ordering claim,
  and `waveD_d12_cltv_tiebreak_not_recoverable` records the erased key.
  `LN-CH-003` must remain `statementOnly` until the model gains script/CLTV
  data and the claim is restated conditionally.
- `commitmentOutputs` performs no dust filter on `c.htlcs`; it assumes
  pre-trimmed HTLCs. D12's `waveD_d12_dust_trimming_requires_filter` documents
  that gap. No `LN-CH-003` declaration was added here.

Both D12 and D46 counterexample modules were left untouched so the refutations
remain available and checkable.
