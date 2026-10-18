# SEC05-ECON — `LN-SEC-005` penalty economics

## Result

- Target: `LnLean.Proofs.Liveness.penalty_economical`
- Repository: `/home/ubuntu/ln-lean-repair`, branch `repair/integrated`,
  HEAD `0caec3d`
- Status: **wired and proved**. `Liveness` now imports
  `LnLean.Proofs.WaveD.D34` and restates the strongest true form of the
  catalog claim at the exact target name.
- Change is additive: one import line plus a new section 9 at the end of the
  file. No existing declaration, proof, or comment text was removed or
  altered.

## Files changed

| file | change |
|---|---|
| `LnLean/Proofs/Liveness.lean` | added `import LnLean.Proofs.WaveD.D34`; added section 9 with `penalty_economical`, `penalty_economical_at_spike`, `penalty_economical_at_base` |
| `agents/reports/SEC05-ECON.md` | this report |

No other file was touched. The unrelated in-tree changes to
`LnLean/Channel/Commitment.lean` and `LnLean/Channel/HTLC.lean` are other
lanes' work and were not modified, staged, or reverted.

## Import-cycle check

`D34` imports `LnLean.Security.Invariants`, `LnLean.Security.Model`,
`LnLean.Bitcoin.Laws`, `LnLean.Channel.Laws`, `LnLean.Routing.Laws`,
`LnLean.Channel.Fee`, `LnLean.Channel.Penalty`, and
`LnLean.Proofs.Security.ThreatModelProps`.

Computed the transitive import closure from
`LnLean/Proofs/WaveD/D34.lean`:

- closure size: **21** files
- `LnLean/Proofs/Liveness.lean` in that closure: **no**
- `LnLean/Proofs/WaveE.E35` in that closure: **no** (E35 is imported by
  `Liveness`, not by D34)
- closure size from `Liveness`: 25 files; the intersection with D34's closure
  is only foundational modules (`LnLean.Basic.Core`, `LnLean.Bitcoin.Seam`,
  `LnLean.Bitcoin.Laws`, `LnLean.Bitcoin.Funding`,
  `LnLean.Bitcoin.ScriptTemplates`, `LnLean.Channel.*`,
  `LnLean.Routing.*`, `LnLean.Security.Invariants`, `LnLean.Security.Model`).

Therefore `Liveness → D34` is acyclic. In particular, D34 does **not**
transitively import `Liveness`, `WaveE.E35`, `Proofs.Common`, or any other
`Proofs.*` module other than `Proofs.Security.ThreatModelProps`.

## Exact `#check` signatures

Checked with `lake env lean` on a scratch file importing
`LnLean.Proofs.Liveness`:

```lean
LnLean.Proofs.Liveness.penalty_economical (env : FeeEnvironment) (rMax : FeeRate) (w : Weight) (v : Msat)
  (hb : FeeScheduleBounded env rMax) (hecon : penaltyEconomical rMax w v) :
  penaltyEconomical (effectiveRate env) w v ∧ ∀ (h : Height), penaltyEconomical (env.atHeight h) w v

LnLean.Proofs.Liveness.penalty_economical_at_spike (env : FeeEnvironment) (rMax : FeeRate) (w : Weight) (v : Msat)
  {spikeHeight : Height} (hb : FeeScheduleBounded env rMax) (hs : env.spikeAt = some spikeHeight)
  (hecon : penaltyEconomical rMax w v) : penaltyEconomical (env.atHeight spikeHeight) w v

LnLean.Proofs.Liveness.penalty_economical_at_base (env : FeeEnvironment) (rMax : FeeRate) (w : Weight) (v : Msat)
  (hb : FeeScheduleBounded env rMax) (hecon : penaltyEconomical rMax w v) : penaltyEconomical env.base w v
```

Underlying D34 signatures used:

```lean
LnLean.Proofs.WaveD.D34.waveD_d34_economical_under_bounded_spike (env : FeeEnvironment) (rMax : FeeRate) (w : Weight)
  (v : Msat) (hb : FeeScheduleBounded env rMax) (h : penaltyEconomical rMax w v) :
  penaltyEconomical (effectiveRate env) w v

LnLean.Proofs.WaveD.D34.waveD_d34_economical_throughout_bounded_schedule (env : FeeEnvironment) (rMax : FeeRate)
  (w : Weight) (v : Msat) (hb : FeeScheduleBounded env rMax) (h : penaltyEconomical rMax w v) :
  penaltyEconomical env.base w v ∧ ∀ (h : Height), penaltyEconomical (env.atHeight h) w v

LnLean.Proofs.WaveD.D34.waveD_d34_economical_at_spike (env : FeeEnvironment) (rMax : FeeRate) (w : Weight) (v : Msat)
  {spikeHeight : Height} (hb : FeeScheduleBounded env rMax) (hs : env.spikeAt = some spikeHeight)
  (hecon : penaltyEconomical rMax w v) : penaltyEconomical (env.atHeight spikeHeight) w v

LnLean.Proofs.WaveD.D34.waveD_d34_unconditional_claim_false :
  ¬∀ (env : FeeEnvironment) (h : Height) (w : Weight) (v : Msat),
      env.spikeAt = some h → penaltyEconomical (env.atHeight h) w v
```

## `#print axioms`

```text
'LnLean.Proofs.Liveness.penalty_economical' depends on axioms: [propext, Quot.sound]
'LnLean.Proofs.Liveness.penalty_economical_at_spike' depends on axioms: [propext, Quot.sound]
'LnLean.Proofs.Liveness.penalty_economical_at_base' depends on axioms: [propext, Quot.sound]
```

Only Lean's standard quotient/propositional-extensionality axioms. No
`sorryAx`, no `Classical.choice`, no project axiom. The added source contains
no `sorry`, `axiom`, `admit`, `native_decide`, `unsafe`, or
`@[implemented_by]`.

## Build evidence

```text
$ LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
    lake env lean LnLean/Proofs/Liveness.lean
LEAN_RC=0

$ LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
    lake build LnLean.Proofs.Liveness
✔ [22/33] Built LnLean.Channel.Laws (681ms)
✔ [30/33] Built LnLean.Proofs.WaveE.E35 (670ms)
✔ [32/33] Built LnLean.Proofs.WaveD.D34 (700ms)
✔ [33/33] Built LnLean.Proofs.Liveness (1.3s)
Build completed successfully (33 jobs).
BUILD_RC=0
```

`git diff -- LnLean/Proofs/Liveness.lean agents/reports/SEC05-ECON.md` contains
only the import, section 9, and this report.

## Promotion verdict

**Promote `LN-SEC-005` to `proved`, conditional on
`FeeScheduleBounded env rMax` and `penaltyEconomical rMax w v`.**

The target name now resolves to a real theorem (it previously did not exist in
`Liveness`), it is faithful, and its conclusion is not assumed. Because this
lane owns neither `Obligations.lean` nor `Traceability.lean`, the catalog row
remains `.statementOnly` in the working tree; the integrator must flip
`LN-SEC-005` and add `penalty_economical` to `provedTable` /
`provedDeclarations` in the same change.

### Explicit scope caveat

This is **not** the unconditional sentence "a penalty transaction remains
economical under the modelled fee spike". It is the bounded-schedule form:

- the base rate **and every** `atHeight h` are at most `rMax.msatPerKw`;
- the penalty is economical at `rMax` for the chosen weight `w` and value `v`.

Without those hypotheses the claim is false in the model:
`waveD_d34_unconditional_claim_false` refutes the universal reading and
`waveD_d34_spike_breaks_valid_penalty` gives a concrete `penaltyValid`
transaction (1500 sat sweep, 500 sat fee) made uneconomical by a spike to
1,500,001 msat/kw at weight 1000. Any promotion text must retain the
bounded-schedule caveat; `penalty_economical` cannot be cited as an
unconditional economic-liveness result.

## Remaining model gap

1. `FeeScheduleBounded` is an **assumption**, not a theorem about the model:
   `FeeEnvironment.atHeight` is arbitrary and `spikeAt` is unbounded, so
   nothing forces a real fee environment to satisfy it. Adding the bound to
   `FeeEnvironment` (or restricting admissible environments) would make the
   catalog sentence closer to unconditional.
2. `penaltyValid` does not require fee sufficiency: `RevokedCommitment.penaltyFee`
   is an `Int` satoshi amount with no link to `FeeEnvironment`, and
   `PenaltyTx` has no weight field. Thus validity still does not imply
   economics, even at a bounded rate.
3. The value at stake `v` is a free parameter in the theorem; it is not
   connected to `d34AtStake` or to `PenaltyTx.sweep.value` inside this
   interface. A caller must instantiate `v` with the actual sweep value to
   obtain a statement about the concrete penalty.
4. "Economical" means positive millisatoshi net reward
   (`0 < penaltyNet r w v`), not profitability after BTC/fiat conversion,
   fee bumping, RBF, or mempool policy; none of those are modelled.
