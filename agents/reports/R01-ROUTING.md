# R01-ROUTING — exact catalog targets for `LN-RT-002` and `LN-RT-005`

## Scope

- `LnLean/Routing/Gossip.lean` — added the catalog target
  `LnLean.Routing.Gossip.update_monotone`.
- `LnLean/Routing/Route.lean` — added the catalog target
  `LnLean.Routing.Route.cltv_accumulates`, plus two supporting lemmas.
- No other Lean file, proof module, script, or vendored file was modified.
- No `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, or
  `@[implemented_by]` was introduced.

## Catalog rows

| Row | Claim | Catalog target | Before | After |
|---|---|---|---|---|
| `LN-RT-002` | A newer `channel_update` replaces an older one only if its timestamp is greater. | `LnLean.Routing.Gossip.update_monotone` | `statementOnly`, target absent | exact target declared and proved |
| `LN-RT-005` | The CLTV expiry at each hop increases by at least that hop's `cltv_expiry_delta`. | `LnLean.Routing.Route.cltv_accumulates` | `statementOnly`, target absent | exact target declared and proved |

## Exact theorem statements

### `LnLean.Routing.Gossip.update_monotone`

```lean
theorem update_monotone (s : GossipState) (u : ChannelUpdate) :
    s.latestUpdateTimestamp ≤ (s.applyUpdate u).latestUpdateTimestamp ∧
      (s.applyUpdate u ≠ s → s.latestUpdateTimestamp < u.timestamp)
```

Both required halves are present:

1. the stored newest timestamp never decreases under
   `GossipState.applyUpdate`;
2. if the update actually changes the store, then the old clock was strictly
   less than the update's timestamp. Consequently an older or equal timestamp
   cannot replace the stored update.

The theorem lives in `namespace LnLean.Routing` / `namespace Gossip`, giving the
exact fully-qualified name `LnLean.Routing.Gossip.update_monotone`. It is stated
for the model's store operation `GossipState.applyUpdate`, whose replacement
guard is exactly `s.latestUpdateTimestamp < u.timestamp`.

### `LnLean.Routing.Route.cltv_accumulates`

```lean
theorem cltv_accumulates (r : Route) (start : Nat) :
    start + r.totalCltv = r.endExpiry start ∧
      (∀ h ∈ r.hops, h.cltvDelta ≤ r.totalCltv) ∧
      (∀ (i : Nat) (hi : i < r.hops.length),
        (r.hops.take i).foldl (fun acc h => acc + h.cltvDelta) start +
            (r.hops[i]'hi).cltvDelta =
          (r.hops.take (i + 1)).foldl (fun acc h => acc + h.cltvDelta) start)
```

The three conjuncts are:

1. the final expiry from `start` is exactly `start` plus the route total:
   `start + r.totalCltv = r.endExpiry start`;
2. every hop's delta is covered by the route total:
   `h ∈ r.hops → h.cltvDelta ≤ r.totalCltv`;
3. the prefix/step form: after `i` hops, taking hop `i` next adds exactly
   that hop's `cltvDelta`. This directly yields the catalog's "at least that
   hop's `cltv_expiry_delta`" (the step is in fact an equality). No positivity
   hypothesis is needed because `cltvDelta : Nat`.

Supporting lemmas added in the same namespace:

```lean
theorem cltvDelta_le_sum {l : List Hop} {h : Hop} (hh : h ∈ l) :
    h.cltvDelta ≤ (l.map Hop.cltvDelta).sum

theorem cltvDelta_le_totalCltv (r : Route) {h : Hop} (hh : h ∈ r.hops) :
    h.cltvDelta ≤ r.totalCltv
```

## Proof approach

- `Gossip.update_monotone`: the first conjunct is the existing
  `GossipState.latestUpdateTimestamp_applyUpdate_ge`. For the second, split on
  whether `u.timestamp ≤ s.latestUpdateTimestamp`. In the stale branch,
  `GossipState.applyUpdate_stale` contradicts the hypothesis that the store
  changed; in the other branch, `Nat.lt_of_not_le` gives strict inequality.
  This is the same argument as
  `LnLean.Proofs.WaveD.D23.waveD_d23_replace_requires_greater`, now placed at
  the catalog's exact name in the model module (no proof module is imported by
  a model module).
- `Route.cltv_accumulates`:
  - conjunct 1 is `Route.foldl_add_eq_sum` applied to `r.hops`, folded into
    the definition of `Route.totalCltv`;
  - conjunct 2 follows from `cltvDelta_le_sum`, proved by list induction using
    `Nat.le_add_right` and `omega`;
  - conjunct 3 rewrites `List.take (i+1)` with
    `List.take_append_getElem hi`, then uses `List.foldl_append` and
    simplification. The result is the exact prefix recurrence for the left
    fold `Route.endExpiry`.

No proof module is imported into either model module; all proofs use only the
existing model definitions and core `List`/`Nat` lemmas.

## Verification

Scratch file `/tmp/opencode/btc-lean/ScratchR01.lean`:

```lean
import LnLean.Routing.Gossip
import LnLean.Routing.Route

#check LnLean.Routing.Gossip.update_monotone
#check LnLean.Routing.Route.cltv_accumulates
#check LnLean.Routing.Route.cltvDelta_le_totalCltv

#print axioms LnLean.Routing.Gossip.update_monotone
#print axioms LnLean.Routing.Route.cltv_accumulates
```

Observed output:

```text
LnLean.Routing.Gossip.update_monotone (s : LnLean.Routing.GossipState) (u : LnLean.Routing.ChannelUpdate) :
  s.latestUpdateTimestamp ≤ (s.applyUpdate u).latestUpdateTimestamp ∧
    (s.applyUpdate u ≠ s → s.latestUpdateTimestamp < u.timestamp)
LnLean.Routing.Route.cltv_accumulates (r : LnLean.Routing.Route) (start : Nat) :
  start + r.totalCltv = r.endExpiry start ∧
    (∀ (h : LnLean.Routing.Hop), h ∈ r.hops → h.cltvDelta ≤ r.totalCltv) ∧
      ∀ (i : Nat) (hi : i < r.hops.length),
        List.foldl (fun acc h => acc + h.cltvDelta) start (List.take i r.hops) + r.hops[i].cltvDelta =
          List.foldl (fun acc h => acc + h.cltvDelta) start (List.take (i + 1) r.hops)
LnLean.Routing.Route.cltvDelta_le_totalCltv (r : LnLean.Routing.Route) {h : LnLean.Routing.Hop} (hh : h ∈ r.hops) :
  h.cltvDelta ≤ r.totalCltv
'LnLean.Routing.Gossip.update_monotone' depends on axioms: [propext]
'LnLean.Routing.Route.cltv_accumulates' depends on axioms: [propext, Quot.sound]
```

No `sorryAx` appears in either axiom probe (only Lean's standard `propext` and
`Quot.sound`).

## Build evidence

One Lean process at a time, under the shared lock:

```sh
cd /home/ubuntu/ln-lean-repair
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake env lean LnLean/Routing/Gossip.lean
# RC 0, no output

LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake env lean LnLean/Routing/Route.lean
# RC 0, no output

LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Routing.Gossip LnLean.Routing.Route
# Build completed successfully (8 jobs).  RC 0
```

The requested `lake build -j1 ...` form is not accepted by this workspace's
Lake (`Lake version 5.0.0-src+eb6cafb`; `error: unknown short option '-j'`).
The equivalent serial build above was used instead; `LEAN_NUM_THREADS=1` keeps
it to one Lean process.

As a regression check, the proof modules that already reason about these
operations still build:

```sh
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Proofs.WaveD.D23 LnLean.Proofs.WaveE.E26
# Build completed successfully (13 jobs).  RC 0
```

The only warnings were pre-existing deprecation warnings in
`LnLean/Proofs/Routing/GossipProps.lean` (`if_pos`/`if_neg`); they are unrelated
to this lane and were not edited.

## Promotion verdicts

| Row | Verdict | Reason |
|---|---|---|
| `LN-RT-002` | **promotion-ready: yes** | Exact target exists, both the clock-monotonicity half and the "replacement requires a strictly greater timestamp" half are proved, and the declaration is sorry-free with only standard axioms. Model caveat: `GossipState` keeps one append-only global update list and a global clock; per-`(short_channel_id, direction)` replacement is the existing `GossipProps.ChannelView` proof-module refinement and is not imported here. This matches the catalog wording at the store-operation level. |
| `LN-RT-005` | **promotion-ready: yes** | Exact target exists and is stronger than the catalog minimum: total-expiry identity, per-hop delta covered by the total, and an exact per-hop prefix accumulation step. No positivity hypothesis is required. Sorry-free with only standard axioms. |

## Files changed

- `LnLean/Routing/Gossip.lean` — `LnLean.Routing.Gossip.update_monotone`.
- `LnLean/Routing/Route.lean` — `LnLean.Routing.Route.cltv_accumulates`,
  `LnLean.Routing.Route.cltvDelta_le_sum`,
  `LnLean.Routing.Route.cltvDelta_le_totalCltv`.
- `agents/reports/R01-ROUTING.md` — this report.
