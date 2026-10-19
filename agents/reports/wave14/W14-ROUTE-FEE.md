# W14-ROUTE-FEE — additive route fee-rounding and capacity/min-max layer

**Lane:** W14-ROUTE-FEE (Wave 14)
**Worktree:** `/home/ubuntu/ln-lean-waveh`
**Branch:** `wave-14/16`
**Base:** `a331b71`
**Status:** complete; scoped build green.

## 1. Scope

Implement the additive route fee-rounding (G13 / `REV-07`) and route
capacity/min-max usability (G14) layer from the Wave-13 review synthesis
(`agents/reports/wave13-review/R32-synthesis.md` §3 G13/G14, §4 T4 boundary
note; `docs/OPEN-ISSUES.md` rows `REV-04`/`REV-07`).

Nothing existing is redefined or weakened:

- `LnLean.Routing.Hop.ofEdge` still rounds the proportional term **up** and
  keeps every consumer (`ofEdge_node`, `ofEdge_scid`, `ofEdge_cltvDelta`,
  `ofEdge_fee_ge_base`, `constructRoute`, `routeValid`, ...).
- `LnLean.Routing.Route.routeValid` is untouched; it remains the per-hop
  predicate.
- `LnLean.Proofs.Routing.RouteBlindingProps.ofEdge_rounding_counterexample`
  (`RouteBlindingProps.lean:252-258`) is retained unchanged in its own module.
  This lane did not import, alter, rename, or delete it.
- `ChannelEdge`, `Graph`, `constructRoute`, `constructRoute_valid`, and
  `routeValid_edge_sound` are not edited. The capacity carrier is a separate
  wrapper.

## 2. Owned files

Only these files were created or modified:

- `LnLean/Proofs/Wave14/RouteFeeCapacity.lean`
- `agents/reports/wave14/W14-ROUTE-FEE.md`

No shared file, root import, audit file, catalog file, script, docs file, or
other lane's Lean module/report was edited.

## 3. Headline definitions and exact statements

All declarations live in namespace
`LnLean.Proofs.Wave14.RouteFeeCapacity` (the fee helper is in
`LnLean.Proofs.Wave14.RouteFeeCapacity.Hop`) and import only
`LnLean.Routing.Route`.

### 3.1 Truncating fee

```lean
def Hop.ofEdgeFloor (e : ChannelEdge) (amountMsat : Msat) : Hop :=
  { node := e.node2
    shortChannelId := e.shortChannelId
    feeMsat :=
      ⟨e.feeBaseMsat.val +
        amountMsat.val * e.feeProportionalMillionths / 1000000⟩
    cltvDelta := e.cltvDelta }
```

```lean
theorem Hop.ofEdgeFloor_fee_le_ofEdge_fee (e : ChannelEdge) (a : Msat) :
    (Hop.ofEdgeFloor e a).feeMsat.val ≤ (Hop.ofEdge e a).feeMsat.val

theorem Hop.ofEdgeFloor_fee_eq (e : ChannelEdge) (a : Msat) :
    (Hop.ofEdgeFloor e a).feeMsat.val =
      e.feeBaseMsat.val +
        a.val * e.feeProportionalMillionths / 1000000
```

`ofEdgeFloor` is the BOLT 7 formula with truncating division, matching LDK
datapoint D3 (`refs/rust-lightning/lightning/src/routing/router.rs:2639-2642`).
It is an additive definition; it is not a redefinition of `ofEdge`.

### 3.2 Concrete floor-vs-ceiling separation

Witness edge: `feeWitnessEdge`, with `feeBaseMsat = 0`,
`feeProportionalMillionths = 1000`, `capacitySat = 100`, `cltvDelta = 40`,
`enabled = true`.

```lean
theorem floor_vs_ceiling_separates :
    (Hop.ofEdge feeWitnessEdge ⟨1500⟩).feeMsat.val = 2 ∧
      (Hop.ofEdgeFloor feeWitnessEdge ⟨1500⟩).feeMsat.val = 1 ∧
      (Hop.ofEdgeFloor feeWitnessEdge ⟨1500⟩).feeMsat.val <
        (Hop.ofEdge feeWitnessEdge ⟨1500⟩).feeMsat.val

theorem floor_ceiling_gap_eq_one :
    (Hop.ofEdge feeWitnessEdge ⟨1500⟩).feeMsat.val =
      (Hop.ofEdgeFloor feeWitnessEdge ⟨1500⟩).feeMsat.val + 1
```

For `amount_msat = 1500` and `ppm = 1000`, the proportional product is
`1_500_000`: truncating division gives `1`, `ofEdge`'s
`(x + 999999) / 1000000` gives `2`. This is the concrete floor-vs-ceiling
separation that G13 said was missing; it does not claim that the full LDK
router arithmetic is reproduced.

### 3.3 Additive capacity carrier

`ChannelEdge` has `capacitySat` but no `htlc_minimum_msat` /
`htlc_maximum_msat`. The additive carrier is:

```lean
structure EdgeCapacity where
  edge : ChannelEdge
  capacityMsat : Msat
  htlcMinimumMsat : Msat
  htlcMaximumMsat : Msat
deriving Repr, DecidableEq, BEq

def capacityOfEdgeMsat (e : ChannelEdge) : Msat :=
  ⟨e.capacitySat * Msat.MSAT_PER_SAT⟩

def edgeUsableFor (c : EdgeCapacity) (amount : Msat) : Prop :=
  c.htlcMinimumMsat.val ≤ amount.val ∧
    amount.val ≤ c.htlcMaximumMsat.val ∧
    amount.val ≤ c.capacityMsat.val
```

`EdgeCapacity` is an additive carrier, **not** a replacement for
`ChannelEdge`; `Graph`, `findEdge`, `routeValid`, and `constructRoute` keep
using `ChannelEdge`. `capacityOfEdgeMsat` converts the existing
`capacitySat` field; the min/max values are caller-supplied BOLT 7
`channel_update` advertisements (the BOLT 7 `ChannelUpdate` record in
`LnLean/Routing/Gossip.lean` already carries those fields; this module does
not re-derive its signatures).

Route-level lift:

```lean
def routeCapacityValid (r : Route) (ces : List EdgeCapacity)
    (amounts : List Msat) : Prop :=
  ces.length = r.hops.length ∧
    amounts.length = r.hops.length ∧
      ∀ p ∈ ces.zip (r.hops.zip amounts),
        edgeUsableFor p.1 p.2.2 ∧
          p.1.edge.shortChannelId = p.2.1.shortChannelId
```

The explicit per-hop `amounts` list is deliberate: BOLT 4 carries a different
(upstream-larger) amount on each hop because each hop adds its fee, so a
single route-level amount would not be an end-to-end capacity claim.

Supporting lemmas:

```lean
theorem edgeUsableFor_min {c : EdgeCapacity} {a : Msat}
    (h : edgeUsableFor c a) : c.htlcMinimumMsat.val ≤ a.val

theorem edgeUsableFor_max {c : EdgeCapacity} {a : Msat}
    (h : edgeUsableFor c a) : a.val ≤ c.htlcMaximumMsat.val

theorem edgeUsableFor_capacity {c : EdgeCapacity} {a : Msat}
    (h : edgeUsableFor c a) : a.val ≤ c.capacityMsat.val

theorem edgeUsableFor_iff (c : EdgeCapacity) (a : Msat) :
    edgeUsableFor c a ↔
      c.htlcMinimumMsat.val ≤ a.val ∧
        a.val ≤ c.htlcMaximumMsat.val ∧
        a.val ≤ c.capacityMsat.val

theorem routeCapacityValid_usable {r : Route} {ces : List EdgeCapacity}
    {amounts : List Msat} (h : routeCapacityValid r ces amounts) :
    ∀ p ∈ ces.zip (r.hops.zip amounts), edgeUsableFor p.1 p.2.2

theorem routeCapacityValid_scid {r : Route} {ces : List EdgeCapacity}
    {amounts : List Msat} (h : routeCapacityValid r ces amounts) :
    ∀ p ∈ ces.zip (r.hops.zip amounts),
      p.1.edge.shortChannelId = p.2.1.shortChannelId
```

### 3.4 Acceptance and rejection

General rejection lemmas:

```lean
theorem amount_above_htlcMaximum_rejected (c : EdgeCapacity) (a : Msat)
    (h : c.htlcMaximumMsat.val < a.val) : ¬ edgeUsableFor c a

theorem amount_above_capacity_rejected (c : EdgeCapacity) (a : Msat)
    (h : c.capacityMsat.val < a.val) : ¬ edgeUsableFor c a

theorem amount_below_htlcMinimum_rejected (c : EdgeCapacity) (a : Msat)
    (h : a.val < c.htlcMinimumMsat.val) : ¬ edgeUsableFor c a
```

Concrete witnesses:

```lean
theorem in_range_amount_accepted :
    edgeUsableFor narrowCapacityEdge ⟨50000⟩ ∧
      0 < (50000 : Nat) ∧
      narrowCapacityEdge.htlcMinimumMsat.val < 50000 ∧
      50000 < narrowCapacityEdge.htlcMaximumMsat.val ∧
      50000 < narrowCapacityEdge.capacityMsat.val

theorem above_htlcMaximum_rejected_concrete :
    ¬ edgeUsableFor narrowCapacityEdge ⟨90000⟩ ∧
      (90000 : Nat) ≤ narrowCapacityEdge.capacityMsat.val ∧
      narrowCapacityEdge.htlcMaximumMsat.val < 90000

theorem above_capacity_rejected_concrete :
    ¬ edgeUsableFor wideCapacityEdge ⟨150000⟩ ∧
      (150000 : Nat) ≤ wideCapacityEdge.htlcMaximumMsat.val ∧
      wideCapacityEdge.capacityMsat.val < 150000

theorem below_htlcMinimum_rejected_concrete :
    ¬ edgeUsableFor narrowCapacityEdge ⟨500⟩ ∧
      0 < (500 : Nat) ∧
      (500 : Nat) < narrowCapacityEdge.htlcMinimumMsat.val
```

Route-level witnesses:

```lean
theorem routeCapacityValid_single_hop_accepts :
    routeCapacityValid
      (constructRoute [(feeWitnessEdge, ⟨50000⟩)] ⟨50000⟩)
      [narrowCapacityEdge] [⟨50000⟩]

theorem routeCapacityValid_single_hop_rejects_above_max :
    ¬ routeCapacityValid
      (constructRoute [(feeWitnessEdge, ⟨90000⟩)] ⟨90000⟩)
      [narrowCapacityEdge] [⟨90000⟩]

theorem routeCapacityValid_single_hop_rejects_above_capacity :
    ¬ routeCapacityValid
      (constructRoute [(feeWitnessEdge, ⟨150000⟩)] ⟨150000⟩)
      [wideCapacityEdge] [⟨150000⟩]

theorem routeCapacityValid_single_hop_rejects_below_min :
    ¬ routeCapacityValid
      (constructRoute [(feeWitnessEdge, ⟨500⟩)] ⟨500⟩)
      [narrowCapacityEdge] [⟨500⟩]
```

The `capacityMsat`/`htlcMaximumMsat` separation is isolated by construction:
`narrowCapacityEdge` has capacity `100_000` and max `80_000` (90 000 is
rejected by max, still within capacity); `wideCapacityEdge` has capacity
`100_000` and max `200_000` (150 000 is rejected by capacity, still within the
HTLC range).

## 4. Concrete non-vacuity witness and the theorem that uses it

- **In-range acceptance:** `narrowCapacityEdge` with min `1_000`, max
  `80_000`, capacity `100_000`; amount `50_000`. `in_range_amount_accepted`
  proves acceptance together with `min < 50000 < max` and
  `50000 < capacity`, so the accepted case is inhabited and not vacuous.
- **Above max rejection:** `above_htlcMaximum_rejected_concrete` uses the same
  edge and amount `90_000`; it also proves `90_000 ≤ capacity`, showing the
  rejection comes from the HTLC maximum, not the capacity bound.
- **Above capacity rejection:** `above_capacity_rejected_concrete` uses
  `wideCapacityEdge` and amount `150_000`; it proves
  `150_000 ≤ max`, showing the rejection comes from capacity.
- **Below min rejection:** `below_htlcMinimum_rejected_concrete` uses amount
  `500` with `0 < 500 < min = 1_000`.
- **Fee separation:** `floor_vs_ceiling_separates` and
  `floor_ceiling_gap_eq_one` use `feeWitnessEdge` and `amount = 1500`, with
  floor fee `1` and ceiling fee `2`.
- **Route level:** `routeCapacityValid_single_hop_accepts` and the three
  rejection theorems instantiate `constructRoute` on the same edge/amounts,
  so the route lift is exercised in both directions.

All concrete theorems are closed by `decide` over the decidable instances
`edgeUsableForDecidable` and `routeCapacityValidDecidable`.

## 5. Build command and result

```sh
cd /home/ubuntu/ln-lean-waveh
export PATH=/dev/shm/btc/elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
LEAN_NUM_THREADS=1 flock -w 3600 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Proofs.Wave14.RouteFeeCapacity
```

Result:

```text
ℹ [8/8] Built LnLean.Proofs.Wave14.RouteFeeCapacity (718ms)
Build completed successfully (8 jobs).
```

No `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, or
`@[implemented_by]` occurs in the module. Only the scoped module build was
run; no bare `lake build`, full gate, or network command was run.

## 6. `#print axioms` output

The module ends with:

```lean
#print axioms floor_vs_ceiling_separates
#print axioms Hop.ofEdgeFloor_fee_le_ofEdge_fee
#print axioms amount_above_htlcMaximum_rejected
#print axioms amount_above_capacity_rejected
#print axioms amount_below_htlcMinimum_rejected
#print axioms in_range_amount_accepted
#print axioms routeCapacityValid_single_hop_accepts
#print axioms routeCapacityValid_single_hop_rejects_above_max
```

Build output:

```text
info: LnLean/Proofs/Wave14/RouteFeeCapacity.lean:366:0: 'LnLean.Proofs.Wave14.RouteFeeCapacity.floor_vs_ceiling_separates' does not depend on any axioms
info: LnLean/Proofs/Wave14/RouteFeeCapacity.lean:367:0: 'LnLean.Proofs.Wave14.RouteFeeCapacity.Hop.ofEdgeFloor_fee_le_ofEdge_fee' depends on axioms: [propext]
info: LnLean/Proofs/Wave14/RouteFeeCapacity.lean:368:0: 'LnLean.Proofs.Wave14.RouteFeeCapacity.amount_above_htlcMaximum_rejected' does not depend on any axioms
info: LnLean/Proofs/Wave14/RouteFeeCapacity.lean:369:0: 'LnLean.Proofs.Wave14.RouteFeeCapacity.amount_above_capacity_rejected' does not depend on any axioms
info: LnLean/Proofs/Wave14/RouteFeeCapacity.lean:370:0: 'LnLean.Proofs.Wave14.RouteFeeCapacity.amount_below_htlcMinimum_rejected' does not depend on any axioms
info: LnLean/Proofs/Wave14/RouteFeeCapacity.lean:371:0: 'LnLean.Proofs.Wave14.RouteFeeCapacity.in_range_amount_accepted' does not depend on any axioms
info: LnLean/Proofs/Wave14/RouteFeeCapacity.lean:372:0: 'LnLean.Proofs.Wave14.RouteFeeCapacity.routeCapacityValid_single_hop_accepts' does not depend on any axioms
info: LnLean/Proofs/Wave14/RouteFeeCapacity.lean:373:0: 'LnLean.Proofs.Wave14.RouteFeeCapacity.routeCapacityValid_single_hop_rejects_above_max' does not depend on any axioms
```

Seven headlines are axiom-free; one depends only on `propext`. All are within
the allowed `propext` / `Quot.sound` / `Classical.choice` set.

## 7. Review gap closed or narrowed

**G13 / `REV-07`, fee-rounding half — narrowed.**

- The truncating BOLT 7 fee now exists as `Hop.ofEdgeFloor`, with
  `ofEdgeFloor_fee_le_ofEdge_fee` proving it never exceeds `ofEdge`'s ceiling.
- `floor_vs_ceiling_separates` supplies the concrete separation witness G13
  said was missing: at `amount_msat = 1500`, `ppm = 1000`, floor is `1` and
  ceiling is `2`.
- `ofEdge` itself is unchanged, and
  `RouteBlindingProps.ofEdge_rounding_counterexample` remains in place.

**G14 — narrowed by a carrier and admission witnesses, not closed.**

- `EdgeCapacity`, `capacityOfEdgeMsat`, `edgeUsableFor`, and
  `routeCapacityValid` provide the missing capacity / `htlc_minimum_msat` /
  `htlc_maximum_msat` carrier and route-level usability predicate.
- Concrete acceptance and three rejection modes are proved, with witnesses
  that isolate `htlc_maximum_msat` from capacity and vice versa.

**What remains narrow / external:**

- `routeCapacityValid` checks advertised ranges only. It does not model
  in-flight HTLC value, channel reserve, commitment fees, dust exposure, path
  scoring, route hints, MPP splitting, or the backwards fee/amount
  propagation of `find_route`. It is not a liquidity oracle and does not claim
  that an accepted route will succeed.
- The min/max values are caller-supplied advertisements; BOLT 7
  `channel_update` signature verification and freshness are outside this
  module (the `Gossip` layer has its own model).
- `routeValid` still has no capacity condition; this lane adds a separate
  predicate rather than changing the existing meaning. No production route
  consumer is rewired to `routeCapacityValid`.
- The fee floor is a per-hop formula at a caller-supplied amount; the full
  router's path-level arithmetic (fee spillover, base fees, path amount
  propagation) is not reproduced.

## 8. Shared-file changes for the integrator (stated, not applied)

1. **Root import:** add `import LnLean.Proofs.Wave14.RouteFeeCapacity` through
   the Wave 14 aggregator / `scripts/regen-root.sh`. This lane did not edit
   `LnLean.lean`.
2. **Axiom audit registry:** if Wave 14 headlines are enrolled in
   `LnLean/Proofs/PhaseC3/AxiomAudit.lean`, add these names and matching
   `#print axioms` lines:
   `floor_vs_ceiling_separates`, `Hop.ofEdgeFloor_fee_le_ofEdge_fee`,
   `amount_above_htlcMaximum_rejected`, `amount_above_capacity_rejected`,
   `amount_below_htlcMinimum_rejected`, `in_range_amount_accepted`,
   `routeCapacityValid_single_hop_accepts`,
   `routeCapacityValid_single_hop_rejects_above_max`.
   Expected audit result: seven axiom-free, one `propext`-only.
3. **Catalog / docs:** `docs/OPEN-ISSUES.md` `REV-07` can note that the floor
   fee and the concrete floor/ceiling separation now exist; `REV-04`/G14 can
   note that an additive capacity carrier exists while `routeValid` keeps its
   old per-hop meaning. No claim of production liquidity/scoring coverage.
4. **Optional docstring correction (not applied):** `Route.lean`'s
   "What is not modelled" list still says liquidity, capacity, and
   `htlc_maximum_msat` are unmodelled. That remains true of `routeValid` and
   `ChannelEdge`; if the integrator wants a pointer, it should say the
   additive layer is in `LnLean.Proofs.Wave14.RouteFeeCapacity`. This lane did
   not edit `Route.lean`.

## 9. Ownership confirmation

No shared or other-lane file was edited. Only the two owned paths in §2 were
written. No `git add`, `git commit`, `git push`, `git switch`, or other Git
write command was run. No network command was run.
