# S01-SECURITY — LN-SEC-002 / 003 / 005 / 006

**Lane:** S01-SECURITY (proof lane)
**Repository:** `/home/ubuntu/ln-lean-repair`
**Branch:** `repair/integrated`
**Files changed by this lane:**
- `LnLean/Proofs/PhaseC2/GlobalConservation.lean` (additive: exact `global_conservation` target in namespace `LnLean.Proofs.Conservation`)
- `LnLean/Proofs/PhaseC3/SecurityGame.lean` (additive: exact `safety_async` target in namespace `LnLean.Proofs.Security`)
- `LnLean/Proofs/Liveness.lean` (additive: `import LnLean.Proofs.WaveE.E35` plus exact `watchtower_bridge` wrapper)
- `agents/reports/S01-SECURITY.md`

No `sorry`, `axiom`, `admit`, `native_decide`, `unsafe`, or
`@[implemented_by]` was added. No existing declaration was deleted or changed.
`Obligations.lean`, `Traceability.lean`, `scripts/`, `vendor/`, and other lanes'
files were not touched.

**Summary verdicts**

| row | exact target | promotion-ready | caveat |
|---|---|---|---|
| LN-SEC-002 | `LnLean.Proofs.Conservation.global_conservation` | **YES** for the multi-channel aggregate | The theorem does **not** cover an L1 spend set; that is a separate model (see below). |
| LN-SEC-003 | `LnLean.Proofs.Security.safety_async` | **YES** | Conditional on the explicit four-field `Assumptions P`. |
| LN-SEC-005 | `LnLean.Proofs.Liveness.penalty_economical` | **NO — remains `statementOnly`** | The unconditional claim is false in the current fee model; the missing hypothesis is a bound on the adversary's feerate schedule. |
| LN-SEC-006 | `LnLean.Proofs.Liveness.watchtower_bridge` | **YES** | Exact wrapper of the E35 theorem; requires a watchtower *report* (which implies `live`), because `live` alone is insufficient in the model. |

---

## LN-SEC-002 — global conservation

### Catalog row

From `LnLean/Proofs/Obligations.lean:352-357`:

| field | value |
|---|---|
| id | `LN-SEC-002` |
| claim | Across all channels and the L1 spend set, total value is conserved. |
| leanTarget | `LnLean.Proofs.Conservation.global_conservation` |
| status | `.statementOnly` (not modified by this lane) |
| boltdoc | BOLT 3 §Commitment Transaction |
| rlAnchor | `lightning/src/ln/chan_utils.rs:716` |

### Exact theorem statement

Verified by `#check` (scratch file `/tmp/opencode/btc-lean/check_s01.lean`):

```
LnLean.Proofs.Conservation.global_conservation
    (m : LnLean.Proofs.PhaseC2.MultiChannelLedger) (h : m.AllConserved) :
  m.totalValue + m.totalFee = m.totalFunding
```

Source (`LnLean/Proofs/PhaseC2/GlobalConservation.lean:344`):

```lean
theorem global_conservation (m : MultiChannelLedger) (h : m.AllConserved) :
    m.totalValue + m.totalFee = m.totalFunding :=
  MultiChannelLedger.totalValue_add_totalFee_eq_totalFunding m h
```

This is the strongest additive form: emitted output value plus commitment fees
is *exactly* total funding, not merely `≤`. `m.AllConserved` is the existing
predicate requiring every commitment in `m.channels` to satisfy
`totalOutputValue + feeSat = fundingValueSat`.

### Placement and namespace choice

The target is declared in `PhaseC2/GlobalConservation.lean` but inside
`namespace LnLean.Proofs.Conservation`, so the fully qualified name is exactly
the catalogued one. Placing the theorem in `Conservation.lean` itself is not
possible without a cycle: `GlobalConservation.lean` imports
`LnLean.Proofs.Conservation` (it reuses `CommitmentConserved`), so importing
the PhaseC2 module back from `Conservation.lean` would be cyclic. The file
contains a comment documenting this choice.

### Scope (important, do not overstate)

`MultiChannelLedger` is a list of commitment transactions with additive
`totalValue`, `totalFee`, and `totalFunding`; it has **no UTXO / L1 spend
component**. Therefore this theorem covers the "across all channels" half of
the catalog sentence only. The L1 spend set is modelled elsewhere
(`LnLean.Security.L1Ledger` for outpoints, and
`LnLean.Proofs.WaveD.D32` for a `Network` with `L1Spend` values and an explicit
`L1SpendsChannels` bridge), but there is no formal link from that `Network` to
`MultiChannelLedger`. No L1 claim is made by this theorem.

### Proof approach

Direct application of the existing
`MultiChannelLedger.totalValue_add_totalFee_eq_totalFunding`, which inducts over
the channel list and uses `omega` on each channel's balance equation. The
wrapper adds no assumptions and no axioms.

### Build evidence

- `lake env lean LnLean/Proofs/PhaseC2/GlobalConservation.lean` → `RC=0`
- `lake build LnLean.Proofs.PhaseC2.GlobalConservation ...` → `RC=0`
- `#check` resolves the exact fully-qualified name → `RC=0`
- `#print axioms` → `[propext, Quot.sound]` (Lean core only; no `sorryAx`)

---

## LN-SEC-003 — asynchronous safety without fairness

### Catalog row

From `LnLean/Proofs/Obligations.lean:358-363`:

| field | value |
|---|---|
| id | `LN-SEC-003` |
| claim | Safety holds under an asynchronous adversarial schedule (without a fairness hypothesis). |
| leanTarget | `LnLean.Proofs.Security.safety_async` |
| status | `.statementOnly` (not modified by this lane) |
| boltdoc | BOLT 2 §Message Retransmission |
| rlAnchor | `lightning/src/ln/channelmanager.rs:17831` |

### Exact theorem statement

Verified by `#check`:

```
LnLean.Proofs.Security.safety_async
    (P : LnLean.Proofs.PhaseC3.SecurityGame.GameParameters)
    (A : LnLean.Proofs.PhaseC3.SecurityGame.Assumptions P)
    (actions : List LnLean.Proofs.PhaseC3.SecurityGame.Action) :
  ¬ LnLean.Proofs.PhaseC3.SecurityGame.Wins P actions
```

Source (`LnLean/Proofs/PhaseC3/SecurityGame.lean:630`):

```lean
theorem safety_async (P : GameParameters) (A : Assumptions P) :
    ∀ actions : List Action, ¬ Wins P actions :=
  safe_of_assumptions P A
```

This is a real wrapper of the existing `safe_of_assumptions`; it does not
weaken the conclusion.

### Why "asynchronous" and "no fairness" are faithful

- The game's `Action` alphabet includes `networkDeliver (tag : Nat)`; `step`
  makes it a stutter, and `actions : List Action` is an arbitrary finite list,
  so the schedule may deliver any tags in any order, including none.
- The theorem quantifies over **all** finite action lists; there is no
  `Fair`, `NoLoss`, eventual-delivery, or GST/partial-synchrony hypothesis.
- The four model assumptions remain explicit hypotheses in `Assumptions P`:
  `sigUnforgeable : Crypto.EufCma P.verify`,
  `hashBinding : HashBinding P`,
  `timelockEnforced : TimelockEnforced P`,
  and `channelConserved : ChannelConserved P`. The wrapper does **not** claim
  these are theorems; a caller must supply them.

### Build evidence

- `lake env lean LnLean/Proofs/PhaseC3/SecurityGame.lean` → `RC=0`
- `lake build LnLean.Proofs.PhaseC3.SecurityGame ...` → `RC=0`
- `#check` resolves the exact fully-qualified name → `RC=0`
- `#print axioms` → `[propext, Quot.sound]`

---

## LN-SEC-006 — watchtower bridge

### Catalog row

From `LnLean/Proofs/Obligations.lean:376-381`:

| field | value |
|---|---|
| id | `LN-SEC-006` |
| claim | A breach is punished if some party has the revocation secret and a timely L1 transaction, given a live watchtower. |
| leanTarget | `LnLean.Proofs.Liveness.watchtower_bridge` |
| status | `.statementOnly` (not modified by this lane) |
| boltdoc | BOLT 5 §Revoked Transaction Close Handling |
| rlAnchor | `lightning/src/chain/channelmonitor.rs:5079` |

### Exact theorem statement

Verified by `#check`:

```
LnLean.Proofs.Liveness.watchtower_bridge
    (sh : LnLean.Channel.Shachain)
    (scheme : LnLean.Channel.RevocationScheme)
    (bridge : LnLean.Channel.L1ScriptBridge)
    (wt : LnLean.Channel.Watchtower)
    (c : LnLean.Channel.RevokedCommitment)
    (r : LnLean.Proofs.WaveE.E35.BreachResponse sh bridge c)
    (hreport : wt.reports c c.breachHeight) :
  LnLean.Proofs.WaveE.E35.BreachPunished bridge c r.tx r.confirm r.window ∧
    LnLean.Channel.punishable scheme c r.tx r.witness r.confirm r.window ∧
    wt.live
```

Source (`LnLean/Proofs/Liveness.lean:716`):

```lean
theorem watchtower_bridge (sh : Shachain) (scheme : RevocationScheme)
    (bridge : L1ScriptBridge) (wt : Watchtower) (c : RevokedCommitment)
    (r : BreachResponse sh bridge c)
    (hreport : wt.reports c c.breachHeight) :
    BreachPunished bridge c r.tx r.confirm r.window ∧
      punishable scheme c r.tx r.witness r.confirm r.window ∧
      wt.live :=
  waveE_e35_watchtower_bridge sh scheme bridge wt c r hreport
```

This is exactly the existing
`LnLean.Proofs.WaveE.E35.waveE_e35_watchtower_bridge` statement (the `#check`
outputs are textually identical), not a weakened restatement.

### Import-cycle check and placement

`LnLean/Proofs/Liveness.lean` now imports `LnLean.Proofs.WaveE.E35`. A
transitive import-closure scan over `LnLean/*.lean` found **no path from E35
back to `LnLean.Proofs.Liveness`** (E35 closure: 24 modules; none imports
Liveness). The import is therefore acyclic and the preferred `Liveness.lean`
wrapper was used instead of defining the target inside E35. The wrapper body is
a direct term application, so it also cannot diverge from the E35 theorem.

### Model caveat: `live` alone is not enough

`Watchtower` has only `live : Prop`, `reports : RevokedCommitment → Height →
Prop`, and the one-way law `reports → live`. The wrapper therefore takes the
explicit report hypothesis `wt.reports c c.breachHeight` and derives `wt.live`
from it. E35's `waveE_e35_live_watchtower_alone_does_not_punish` is a mechanized
counterexample showing a live tower need not report; the catalog phrase "given
a live watchtower" must be read together with the `BreachResponse`/report
hypotheses. `BreachResponse` itself carries the revocation-secret possession
(`holdsSecret`), the both-output penalty transaction, the sweep equation, the
timely confirmation, and bridge confirmation.

### Build evidence

- `lake env lean LnLean/Proofs/Liveness.lean` → `RC=0`
- `lake build LnLean.Proofs.Liveness ...` → `RC=0` (E35 and Liveness rebuilt)
- `#check` resolves the exact fully-qualified name and matches E35 → `RC=0`
- `#print axioms` → no axioms at all

### Documentation note

The pre-existing module docstring in `Liveness.lean` ("What is NOT modelled",
lines 102–104) still says that penalty economics and the watchtower bridge are
"outside this module's import allowlist". That sentence is now stale after the
additive E35 import. It was left untouched under the lane constraint "do not
delete or alter existing comments"; the new section comment documents the
import and its acyclicity.

---

## LN-SEC-005 — penalty economics (not promoted)

### Catalog row

From `LnLean/Proofs/Obligations.lean:370-375`:

| field | value |
|---|---|
| id | `LN-SEC-005` |
| claim | A penalty transaction remains economical under the modelled fee spike. |
| leanTarget | `LnLean.Proofs.Liveness.penalty_economical` |
| status | `.statementOnly` (**unchanged**) |
| boltdoc | BOLT 5 §Revoked Transaction Close Handling |
| rlAnchor | `lightning/src/chain/chaininterface.rs:350` |

**No `penalty_economical` declaration was added.** The row stays
`statementOnly` deliberately.

### Why not

The fee/economy model lives in `LnLean.Proofs.WaveD.D34`, not in E35. The
modelled environment is:

```lean
structure FeeEnvironment where
  base : FeeRate
  atHeight : Height → FeeRate
  spikeAt : Option Height
```

`atHeight` is an **arbitrary** function and `spikeAt` has **no bound**.
D34 proves that the unconditional reading is false:

- `waveD_d34_spike_can_break_economy : ∀ v, ∃ env w h,
  env.spikeAt = some h ∧ ¬ penaltyEconomical (env.atHeight h) w v`
- `waveD_d34_unconditional_claim_false` — the negation of the universal
  statement.
- `waveD_d34_spike_breaks_valid_penalty` — a concrete `penaltyValid` penalty
  (sweep 1500 sat, penalty fee 500 sat) is made uneconomical by a spike to
  1,500,001 msat/kw at weight 1000.

`LnLean.Proofs.WaveE.E35.waveE_e35_punishment_value_bound` is a *value* bound
(`c.toLocalValue - c.penaltyFee ≤ r.tx.sweep.value`), not a feerate/economy
statement; it cannot support the claim either.

### Precise missing model / hypothesis

The strongest true D34 result is conditional:

```lean
theorem waveD_d34_economical_under_bounded_spike
    (env : FeeEnvironment) (rMax : FeeRate) (w : Weight) (v : Msat)
    (hb : FeeScheduleBounded env rMax)
    (h : penaltyEconomical rMax w v) :
    penaltyEconomical (effectiveRate env) w v
```

where `FeeScheduleBounded env rMax` requires both
`env.base.msatPerKw ≤ rMax.msatPerKw` and
`∀ h, (env.atHeight h).msatPerKw ≤ rMax.msatPerKw`.

To make the catalog claim faithful, one of the following model changes is
needed:

1. add a feerate-schedule bound (the `LN-PENALTY-ECON` assumption) to the
   statement, i.e. `FeeScheduleBounded env rMax` plus
   `penaltyEconomical rMax w v`; or
2. restrict `FeeEnvironment` itself so that every admissible `atHeight`/`spikeAt`
   is below the break-even rate; and
3. link `RevokedCommitment.penaltyFee` / `PenaltyTx` weight to the fee model
   (currently D34's `penaltyValid` does not require fee sufficiency, and
   `PenaltyTx` has no weight field).

Without (1) or (2), the sentence "remains economical under the modelled fee
spike" is false in the model, so promoting the row would overstate the result.

---

## Build evidence

All commands were run from `/home/ubuntu/ln-lean-repair` with one Lean process
at a time under `flock /tmp/opencode/btc-lean/build.lock`
(`LEAN_NUM_THREADS=1`).

| command | RC |
|---|---|
| `lake env lean LnLean/Proofs/PhaseC2/GlobalConservation.lean` | 0 |
| `lake env lean LnLean/Proofs/PhaseC3/SecurityGame.lean` | 0 |
| `lake env lean LnLean/Proofs/Liveness.lean` | 0 |
| `lake build LnLean.Proofs.PhaseC2.GlobalConservation LnLean.Proofs.PhaseC3.SecurityGame LnLean.Proofs.Liveness` | 0 |
| `lake env lean /tmp/opencode/btc-lean/check_s01.lean` (`#check`/`#print`) | 0 |
| `lake env lean /tmp/opencode/btc-lean/axioms_s01.lean` (`#print axioms`) | 0 |

A subsequent repository-wide `lake build` returned `RC=1`, but the two failures
are in files modified by **other concurrent lanes**, not by this lane:

- `LnLean/Protocol/Peer.lean:402`: `Invalid name after end` (file is
  `M` in `git status`)
- `LnLean/Channel/Commitment.lean:347/422/428`: unsolved goals (file is
  `M` in `git status`)

Neither file is in this lane's allowed set, and both were already modified in
the shared working tree before this lane's edits. The three modules owned by
this lane built successfully (`RC=0`) before that repository-wide run; the
per-module evidence above is the authoritative evidence for this lane.

## Traceability / follow-up

- `LnLean/Proofs/Obligations.lean` and `LnLean/Proofs/Traceability.lean` were
  not edited. The orchestrator can flip LN-SEC-002, LN-SEC-003, and LN-SEC-006
  to `.proved` after review; LN-SEC-005 should remain `.statementOnly`.
- For LN-SEC-002, if the row text is kept literal ("and the L1 spend set"),
  either narrow it to "across all modelled channels" or add a bridge from
  `MultiChannelLedger` to `WaveD.D32.Network` / `L1Spend`. The current exact
  theorem does not claim the L1 half.
