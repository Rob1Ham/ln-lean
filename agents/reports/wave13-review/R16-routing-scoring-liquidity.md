# R16 — Routing, scoring, pathfinding, and liquidity
**Status:** read-only review
**Pins:** LDK Node `fa123fed131e27ecc420b77fa7086fcf1ddaebb8`, LDK Server `c17dc11dde38f88c53457039ddf30c6b90a63ba2`
**Review branch:** `repair/integrated` (no branch, commit, or non-report file changes made)

## 1. Scope and current Lean surface

This lane covers route construction, route validity, fee/CLTV accumulation, the
finite graph and path enumerator, channel liquidity bounds, failure/success
scoring, and pathfinding-score persistence. It does not re-review onion
crypto/wire (`R09`), gossip admission/canonicalisation (`LN-RT-002`,
`LN-RT-006`), MPP recipient accounting (`LN-PM-004/005`), or HTLC forwarding
fees (`R07`). Those surfaces appear only where they constrain a routing claim.

Short verdict: **the tree has a correct list-arithmetic route calculus and a
finite graph enumerator, but no route selector, no scoring model, no
failure/success liquidity update, and no pathfinding persistence.** The two
catalog rows that touch this surface are true for their stated abstract types;
neither is a pathfinding or liquidity claim.

### 1.1 Catalog rows that touch this surface

| Row | Catalog claim | Exact Lean targets | What the target actually establishes |
|---|---|---|---|
| `LN-RT-001` | "A well-formed route is non-empty, connected end-to-end, and every hop has enough capacity." | `LnLean.Security.Route.wellFormed_nonempty`, `.wellFormed_connected`, `.wellFormed_capacity` (`LnLean/Security/Invariants.lean:367-380`) | Projections of `Route.WellFormed` (`:356-358`) over a **separate** abstract `Hop {src,dst,capacity,cltvDelta}` (`:334-340`). There is no `Graph`, no `short_channel_id`, no `enabled` flag, no fee, and no link from `Hop.capacity` to a BOLT 7 announcement. The "capacity" conjunct is a caller-supplied field of the same record, so any route can be made well-formed by choosing `capacity` large enough. The three theorems are definitional projections, not pathfinding or admission results. |
| `LN-RT-005` | "The CLTV expiry at each hop increases by at least that hop's `cltv_expiry_delta`." | `LnLean.Routing.Route.cltv_accumulates` (`LnLean/Routing/Route.lean:270-283`); supporting `Route.foldl_add_eq_sum`, `endExpiry_gt`, `endExpiry_gt'`, `cltvDelta_le_totalCltv` (`:194-253`); backward form in `LnLean.Proofs.Routing.RouteBlindingProps` `Route.cltvAt`, `cltvAt_succ`, `cltvAt_strict_anti` (`:260-364`) | Faithful finite list arithmetic: the forward fold is `start + Σ delta`; the per-step form is exact equality; the backward schedule strictly decreases downstream under positive deltas. It says nothing about the receiver's `min_final_cltv_expiry`, the route's maximum total CLTV, or whether a hop is usable. |

Relevant non-catalog proof modules:

* `LnLean/Proofs/Routing/RouteBlindingProps.lean` — fee sum, per-hop amount
  schedule, CLTV schedule, blinded-path projection. Its own scope note says
  route search, optimality, liquidity, `htlc_minimum_msat`/`htlc_maximum_msat`,
  MPP, and hints are **not** modelled (`:100-106`), and that `Hop.feeMsat` is
  not tied to the amount used in `Hop.ofEdge` (`:103-106`).
* `LnLean/Proofs/PhaseC3/CrossChannelRouting.lean` — `BackwardConserves`,
  `LiquidityModel`, `FeasiblePath`, and `routeValid` construction. The
  liquidity and capacity conjuncts are **preconditions supplied by the caller**
  (`:379-408`), not derived from graph state, balances, or gossip.
* `LnLean/Proofs/Payment/LiquidityProps.lean` — single-channel reserve and
  HTLC-cap algebra. It explicitly does not model the full LDK outbound-capacity
  formula and has no graph route connection (`:76-95`).
* `LnLean/Proofs/Routing/GraphProps.lean` — edge lookup, adjacency, simple-path
  soundness, and the `findEdge_zeroCapacity` counterexample (`:300-307`).

### 1.2 The two route types are not bridged

`LnLean.Routing.Route` (`Route.lean:130-133`) has `hops : List Hop`,
`amountMsat`, and `routeValid` requires only: non-empty, and for each hop some
enabled graph edge with the same `short_channel_id` and `node2 = hop.node`
(`:325-327`). It does **not** require:

* that hop `i`'s backing edge starts at hop `i-1`'s destination (connectivity),
* that the first hop starts at the payer,
* that the edge's capacity or `htlc_maximum_msat` covers the carried amount,
* that the fee declared in `Hop.feeMsat` is the fee computed from the carried
  amount,
* that the route stays under a total fee or total CLTV bound.

`LnLean.Security.Route` has `Connected`, but it is a different type with no
projection to or from `LnLean.Routing.Route` and no graph. This is the central
model-integrity gap: the catalog's "connected end-to-end" theorem does not
apply to the graph route type that `routeValid`, `constructRoute`, and
`FeasiblePath` use.

### 1.3 Concrete route-validity gap (counterexample exists in the current model)

Take a graph with two enabled, unrelated edges:

* `eA : 0 → 1` on `scid A`,
* `eB : 2 → 3` on `scid B`.

Let `r.hops = [⟨node 1, scid A, fee 0, delta 1⟩, ⟨node 3, scid B, fee 0, delta 1⟩]`.
Then `routeValid g r` holds — each hop has a backing enabled edge with the right
destination and `short_channel_id`. But the route is not a chain: `eA.node2 = 1`
and `eB.node1 = 2`, so there is no edge from the first hop's destination to the
second hop's source. Nothing in `routeValid` rejects this route. This is a
counterexample that any claim "`routeValid` ⇒ connected route" must preserve.

The same weakness appears one level down: `Graph.findEdge` returns the **first**
enabled edge between two nodes and ignores capacity, HTLC limits, fees, and CLTV
(`Graph.lean:167-168`; `GraphProps.findEdge_zeroCapacity` records the
zero-capacity case). With parallel channels this can select an unusable edge
even when a usable one exists.

## 2. LDK datapoints (with `file:line`)

All paths below are in the pinned read-only clones. LDK Node/Server are the
primary datapoints; the underlying `lightning` crate is pinned separately by the
tree at `fe4900930c6bd5786ec4203274d7cf312776a5a6` and is cited only where the
Node API delegates to it.

### 2.1 Route selection and per-edge checks

* LDK Node sends BOLT 11 payments through `ChannelManager::pay_for_bolt11_invoice`
  with a time-based retry strategy (`ldk-node/src/payment/bolt11.rs:218-240`,
  `:202-240`). The route parameters (`max_total_routing_fee_msat`,
  `max_total_cltv_expiry_delta`, `max_path_count`,
  `max_channel_saturation_power_of_half`) are caller-configurable
  (`:839-851`).
* The finite per-edge admission checks are in the router's
  `build_route_from_hops_internal`:
  * both directions must be enabled (`refs/rust-lightning/lightning/src/routing/router.rs:380-382`);
  * `amount_msat < htlc_minimum_msat` or `> htlc_maximum_msat` is rejected
    (`:384-386`);
  * `amount_msat > effective_capacity` is rejected (`:387-389`);
  * `fee > amount_msat / 2` is rejected (`:390-393`);
  * `cltv_so_far + edge_cltv + MIN_FINAL_CLTV_EXPIRY_DELTA >
    DEFAULT_MAX_TOTAL_CLTV_EXPIRY_DELTA` is rejected (`:394-397`), with
    `DEFAULT_MAX_TOTAL_CLTV_EXPIRY_DELTA = 1008` (`:1135`) and
    `MAX_PATH_LENGTH_ESTIMATE = 19` (`:1160`).
* The fee arithmetic is **truncating**, not ceiling:
  `base_msat + (amount_msat * proportional_millionths) / 1_000_000`
  (`router.rs:2639-2642`). Lean's `Hop.ofEdge` uses
  `(amount * ppm + 999_999) / 1_000_000` (`Route.lean:92-97`), i.e. ceiling.
  These differ by at most one msat and can differ on small amounts.
* The production search is a payee-to-payer Dijkstra-like walk, explicitly
  **not** a faithful Dijkstra: liquidity limits encountered later can reduce the
  value already assumed on earlier hops, and the code accepts that some
  liquidity-limited paths may be de-preferenced
  (`router.rs:2859-2888`). Candidate paths must carry at least 5% of the target
  value (`:2880-2883`), and the algorithm is not a shortest-path oracle.
  Therefore no Lean theorem should claim that LDK's `find_route` is optimal or
  complete.
* Fee-limit enforcement is a postcondition on the returned route:
  `Route::get_total_fees` and `debug_assert_route_meets_params`
  (`router.rs:845-878`), not a property of the per-edge predicate.

### 2.2 HTLC min/max windows

* `ChannelUpdateInfo` exposes `cltv_expiry_delta`, `htlc_minimum_msat`,
  `htlc_maximum_msat`, and `fees` per direction
  (`ldk-node/src/graph.rs:95-109`), with `capacity_sats` optional on the channel
  (`:73-74`).
* BOLT 7 requires `htlc_maximum_msat ≤ channel capacity` and
  `htlc_minimum_msat ≤ htlc_maximum_msat`
  (`refs/bolts/07-routing-gossip.md:505-508`, `:522-524`), and says a node
  SHOULD ignore a channel when `htlc_maximum_msat` exceeds capacity
  (`:567-573`).
* LDK Node's `RandomWalkStrategy` folds the tightest limits across the path:
  `route_least_htlc_upper_bound =
  min(first_hop_limit, htlc_maximum_msat ...)` and
  `route_greatest_htlc_lower_bound = max(first_hop_min, htlc_minimum_msat ...)`,
  returns `None` if `lower > upper`, and clamps the probe amount into that
  interval (`ldk-node/src/probing.rs:619-693`).
* The same module documents that probing exists because announced capacity is
  not live liquidity, and that use of an incapable channel can fail the whole
  payment (`probing.rs:8-18`). `RandomWalkStrategy` deliberately ignores the
  scorer (`:562-566`), so probing and scoring are distinct observables.
* Pre-flight probes are filtered by
  `available_liquidity < required_amount * probing_liquidity_limit_multiplier`
  (`ldk-node/src/payment/bolt11.rs:807-817`, `:853-856`;
  `src/probing.rs:438-441`, `:533-547`).

### 2.3 Failure/success scoring and the liquidity bounds

* The scorer is a `ProbabilisticScorer` over per-channel **lower and upper
  liquidity bounds**; failure lowers the upper bound, success/forwarding raises
  the lower bound, and the resulting success probability is
  `(upper - amount) / (upper - lower)` (`refs/rust-lightning/.../scoring.rs:455-476`).
  The bounds decay by half-life (`:473-476`, `:506-530`).
* `failed_at_channel a` sets the upper bound to `min(upper, a)` and resets the
  lower bound to `0` when `a < lower`
  (`scoring.rs:1642-1656`, `:1703-1709`).
* `failed_downstream a` sets the lower bound to `max(lower, a)`; if `a` exceeds
  the current upper bound it resets the upper bound to the channel capacity
  (`:1658-1673`, `:1710-1716`). Consequently the interval **need not shrink**:
  this operation can widen `upper` back to capacity.
* `successful a` sets `upper := max 0 (upper - a)` and resets `lower := 0` if the
  new upper is below it (`:1676-1687`, `:1698-1716`).
* `payment_path_failed(path, scid, t)` scores every hop before `scid` as
  `failed_downstream` and the named hop as `failed_at_channel`, then stops; it
  only learns for announced channels (`:1764-1810`). This is an attribution
  assumption over the reported failure index, not proved.
* The penalty is `-log10(success_probability)` weighted, with a
  `considered_impossible_penalty_msat` when the amount exceeds the upper bound
  and an early return at capacity (`:1506-1599`). The exact log approximation and
  the fee multipliers are implementation policy, not protocol constants.

### 2.4 Persistence, export, and merge

* The local scorer is read from the key-value store with
  `ProbabilisticScorer::read` and wrapped in `CombinedScorer`
  (`ldk-node/src/builder.rs:2100-2113`; `src/io/utils.rs:123-140`).
  External scores are read from a separate cache key and merged at start-up
  (`builder.rs:2115-2127`; `io/utils.rs:145-190`).
* `Node::export_pathfinding_scores` returns the stored scorer bytes
  (`ldk-node/src/lib.rs:2545-2563`); LDK Server exposes it as
  `ExportPathfindingScores` (`ldk-server/src/api/export_pathfinding_scores.rs:17-23`)
  and reports `latest_pathfinding_scores_sync_timestamp` in
  `GetNodeInfo` (`ldk-server/src/api/get_node_info.rs:76-77`).
* Background sync downloads `ChannelLiquidities`, persists them, merges them
  with `duration_since_epoch`, and records the sync timestamp
  (`ldk-node/src/scoring.rs:18-24`, `:53-102`; `:77-90`).
* `CombinedScorer::merge` decays both sides and, per `scid`, averages the
  min/max offsets with `a/2 + b/2 + ((a & 1) & (b & 1))`
  (`refs/rust-lightning/.../scoring.rs:1262-1270`, `:1881-1925`). That average
  is floor `(a+b)/2`; it is commutative but not idempotent when re-merging a
  different value, and it is not associative across three sources.

## 3. Gap matrix

| Behavior | Lean status | LDK evidence | Gap / counterexample | Priority |
|---|---|---|---|---|
| Route non-emptiness | covered faithfully | `router.rs:845-878` (path non-empty) | Both `Routing.Route.NonEmpty` and `Security.Route.WellFormed` prove it. No gap. | — |
| End-to-end connectivity of a graph route | **partially covered / contradicted at the graph layer** | `router.rs:2797-2888` builds connected paths; `Path` hops are a chain | `routeValid` checks each hop independently (`Route.lean:325-327`). The two-edge `0→1`, `2→3` witness is `routeValid` but not a chain. `Security.Route.Connected` is on a different type with no bridge. | **P0** |
| Per-hop capacity | **partially covered** | `router.rs:387-389` rejects amount > effective capacity | `FeasiblePath.capacity` and `LiquidityModel.withinCapacity` are caller-supplied preconditions (`CrossChannelRouting.lean:379-408`); `routeValid` ignores capacity. `Security.Route` capacity is an unconstrained field. | P1 |
| BOLT 7 `htlc_maximum_msat` | **missing at the route layer** | `router.rs:384-386`; `probing.rs:619-693`; BOLT 7 `:505-508`, `:567-573` | `ChannelUpdate` stores min/max (`Gossip.lean:155-168`) but `ChannelEdge` has neither, and no theorem uses them for routability. `ChannelUpdate.wellFormed` only checks min ≤ max (`:179-181`), not max ≤ capacity. | P1 |
| Fee formula | **contradicted (one-msat rounding)** | `router.rs:2639-2642` uses truncating division | `Hop.ofEdge` uses ceiling (`Route.lean:92-97`); `ofEdge_rounding_counterexample` (`RouteBlindingProps.lean:252-258`) already records the inverse-direction mismatch, but there is no direct Lean-vs-LDK fee theorem or witness. | P1 |
| Fee sanity bound `fee ≤ amount/2` | **missing** | `router.rs:390-393` | `FeasiblePath` has no fee bound. A one-hop plan with `base=1, ppm=1_000_000, amount=2` gives fee `3 > 1`, so `FeasiblePath` admits a plan LDK rejects. | P1 |
| Total routing-fee cap | missing | `router.rs:845-878`; `bolt11.rs:839-851` | No `max_total_routing_fee_msat` in the Lean route model. | P2 |
| CLTV accumulation | covered faithfully | `router.rs:394-397`; BOLT 7 `:1031-1047` | List arithmetic is correct (`cltv_accumulates`, `cltvAt_strict_anti`). Total-CLTV cap and `min_final_cltv_expiry` policy are missing. | P2 (extension) |
| Graph path enumeration | partial | `router.rs:2797-2888` | `simplePaths` is fuel-bounded, returns simple paths only, and is explicitly not complete (`Graph.lean:57-60`, `GraphProps.lean:78`). No path count/size bound. | P2 |
| Route selection / cost minimisation | **missing** | `router.rs:2859-2888` selects by fee + scorer penalty, with MPP splitting | No selector, no cost function, no candidate filter, no `max_path_count`, no saturation. `simplePaths` only enumerates. | P1 |
| Dijkstra optimality / completeness | **unmodelled / external** | `router.rs:2859-2888` explicitly says it is not a faithful Dijkstra | Do not claim `find_route` optimality. A Lean `selectRoute` can be optimal only over its own finite candidate list. | — |
| Failure scoring (`failed_at_channel`) | **missing** | `scoring.rs:1642-1656` | No liquidity-bound state, no failure event, no update theorem. | P1 |
| Downstream failure scoring (`failed_downstream`) | **missing** | `scoring.rs:1658-1673` | Same; also the non-monotone `upper := capacity` reset is a fidelity trap. | P1 |
| Success scoring | **missing** | `scoring.rs:1676-1687` | Same. | P1 |
| Decay / historical buckets | **unmodelled / external** | `scoring.rs:506-530`, `:867-960` | Real-time half-lives and exponentially decayed buckets; no time model. | — |
| Probability/penalty formula | **unmodelled / external** | `scoring.rs:455-476`, `:1506-1599` | Pickhardt–Richter probability, `log10` approximation, fee multipliers, manual node penalties. Only the qualitative monotonicity is modelable. | — |
| In-flight HTLC accounting | **missing** | `router.rs:492-560`; `scoring.rs:1506-1513` | No `inflight_htlc_msat`; a route can reuse liquidity already committed to in-flight HTLCs. | P1 |
| Pathfinding-score persistence/export/merge | **missing** | `lib.rs:2545-2563`; `scoring.rs:1262-1270`, `:1881-1925`; `builder.rs:2100-2127` | No encode/decode model, no merge algebra, no local-vs-external separation. | P2 |
| External score sync | **unmodelled / external** | `scoring.rs:18-24`, `:53-102`; `export_pathfinding_scores.rs:17-23` | HTTP download, cache key, timestamp freshness, trust in the provider. | — |
| Probing | **unmodelled / external** | `probing.rs:8-18`, `:471-547`, `:619-693` | Live HTLCs, locked liquidity, random strategies, privacy/DoS trade-offs. | — |
| MPP splitting / `max_path_count` / saturation | missing | `router.rs:2860-2888`, `:901-940`; `bolt11.rs:839-851` | Lean has recipient-side `MPPPlan`, not sender-side path splitting or saturation. | P2 |
| `findEdge` usable-edge choice | partial | `router.rs:380-393` | `findEdge` returns the first enabled edge and ignores capacity/HTLC/fee/CLTV; `findEdge_zeroCapacity` (`GraphProps.lean:300-307`) is the retained witness. | P1 |

## 4. Proposed targets

The names below are proposals; none exists in the tree today. All are additive
unless marked "model extension". Path suggestions are
`LnLean/Proofs/Routing/*.lean`; they must be root-imported and added to
`AxiomAudit` only by the parent.

### T1 — `LnLean.Proofs.Routing.RouteChainTargets.chainBacked_routeValid`
**Priority: P0. Fidelity risk: low. Feasibility: high. Model extension: no.**

```lean
namespace LnLean.Routing

/-- `r` is backed by a connected chain of enabled graph edges. -/
def Route.ChainBacked (g : Graph) (r : Route) : Prop :=
  ∃ es : List ChannelEdge,
    es.length = r.hops.length ∧
    (∀ i (hi : i < es.length),
      let e := es[i]'(by omega)
      let h := r.hops[i]'(by omega)
      e ∈ g.edges ∧ e.enabled = true ∧
      e.shortChannelId = h.shortChannelId ∧ e.node2 = h.node) ∧
    (∀ i (hi : i + 1 < es.length),
      (es[i]'(by omega)).node2 = (es[i+1]'(by omega)).node1)

theorem chainBacked_routeValid {g : Graph} {r : Route}
    (h : r.ChainBacked g) : routeValid g r

/-- The current predicate is strictly weaker. -/
theorem routeValid_not_chainBacked :
    ∃ (g : Graph) (r : Route), routeValid g r ∧ ¬ r.ChainBacked g
```

Hypotheses: none beyond the definitions. Non-vacuity: the existing
`demoGraph`/`demoPlan` one-hop plan satisfies `ChainBacked`; the two-edge
`0→1`, `2→3` witness satisfies `routeValid` but not `ChainBacked`.

Why faithful: LDK's `Path` is built by walking edges from the payer through each
hop's `public_key`/`short_channel_id`; connectivity is implicit in the search,
not re-checked in `debug_assert_route_meets_params`. `ChainBacked` makes that
implicit chain explicit and proves the exact gap in the current `routeValid`.
It does **not** redefine `routeValid` or `FeasiblePath`, so no existing theorem
is weakened.

### T2 — `LnLean.Proofs.Routing.FeeArithmeticTargets.ofEdge_fee_eq_ldk_or_succ`
**Priority: P1. Fidelity risk: low. Feasibility: trivial–high. Model extension: no.**

```lean
namespace LnLean.Routing

/-- LDK `compute_fees` (`router.rs:2639-2642`): truncating division. -/
def Hop.ldkFee (e : ChannelEdge) (a : Msat) : Nat :=
  e.feeBaseMsat.val + (a.val * e.feeProportionalMillionths) / 1_000_000

theorem ldkFee_le_ofEdge (e : ChannelEdge) (a : Msat) :
    Hop.ldkFee e a ≤ (Hop.ofEdge e a).feeMsat.val

theorem ofEdge_fee_eq_ldk_or_succ (e : ChannelEdge) (a : Msat) :
    (Hop.ofEdge e a).feeMsat.val = Hop.ldkFee e a ∨
    (Hop.ofEdge e a).feeMsat.val = Hop.ldkFee e a + 1

/-- Preserve the divergence as a checked witness, not a silent equality. -/
theorem ofEdge_fee_ldk_counterexample :
    ∃ (e : ChannelEdge) (a : Msat),
      (Hop.ofEdge e a).feeMsat.val = Hop.ldkFee e a + 1
```

Hypotheses: none (the base/ppm/amount are natural numbers; LDK's `checked_mul`
overflow is a separate range hypothesis if we model `u64` bounds).
Non-vacuity: `base=0, ppm=1, amount=1` gives Lean `1`, LDK `0`; `base=0,
ppm=1000, amount=1000` gives both `1`. Why faithful: it states the exact
ceiling-vs-truncation relation, not an equality. The existing
`ofEdge_rounding_counterexample` stays intact; this target adds the direct
LDK comparison that the catalog's fee/route claims lack.

### T3 — `LnLean.Proofs.Routing.ForwardableTargets.forwardable_iff_ldkChecks`
**Priority: P1. Fidelity risk: medium (policy constants). Feasibility: medium. Model extension: additive predicate.**

```lean
namespace LnLean.Routing

/-- The finite per-edge checks of `build_route_from_hops_internal`
    (`router.rs:380-397`), parameterised by the receiver/final CLTV policy. -/
def Forwardable (e : ChannelEdge) (cltvSoFar : Nat)
    (minFinal maxTotal : Nat) (a : Msat) : Prop :=
  e.enabled = true ∧
  a.val ≤ e.capacitySat * Msat.MSAT_PER_SAT ∧
  (Hop.ofEdge e a).feeMsat.val ≤ a.val / 2 ∧
  cltvSoFar + e.cltvDelta + minFinal ≤ maxTotal

theorem forwardable_capacity {e cltvSoFar minFinal maxTotal a}
    (h : Forwardable e cltvSoFar minFinal maxTotal a) :
    a.val ≤ e.capacitySat * Msat.MSAT_PER_SAT

theorem forwardable_fee_half {e cltvSoFar minFinal maxTotal a}
    (h : Forwardable e cltvSoFar minFinal maxTotal a) :
    (Hop.ofEdge e a).feeMsat.val ≤ a.val / 2

theorem forwardable_cltv {e cltvSoFar minFinal maxTotal a}
    (h : Forwardable e cltvSoFar minFinal maxTotal a) :
    cltvSoFar + e.cltvDelta + minFinal ≤ maxTotal

/-- The existing `FeasiblePath` does not imply these checks. -/
theorem feasiblePath_not_forwardable :
    ∃ (g : Graph) (L : LiquidityModel) (plan : FeasiblePath g L)
      (p : ChannelEdge × Msat),
      p ∈ plan.path ∧
      ¬ Forwardable p.1 0 3 1008 p.2
```

Hypotheses: `minFinal`/`maxTotal` are explicit policy parameters; instantiate
with `3`/`1008` only for the concrete LDK defaults. Non-vacuity: the
`demoPlan` satisfies `Forwardable` (fee zero, capacity 1000 msat, delta 40).
Counterexample witness: `base=1, ppm=1_000_000, amount=2` on a one-sat edge,
cltv delta positive, so the fee check fails. Why faithful: this is exactly the
router's conjunction, separated from route search. It is additive; it does not
strengthen `FeasiblePath` or change `routeValid`.

### T4 — `LnLean.Proofs.Routing.HtlcWindowTargets.feasibleAmount_iff_window`
**Priority: P1. Fidelity risk: low. Feasibility: medium. Model extension: no (new definitions only).**

```lean
namespace LnLean.Routing

/-- Tightest lower bound over a path of updates. -/
def pathHtlcLo (us : List ChannelUpdate) : Nat :=
  us.foldl (fun acc u => max acc u.htlcMinimumMsat.val) 0

/-- Tightest upper bound; `U64_MAX` models the absent/effectively-infinite cap. -/
def pathHtlcHi (us : List ChannelUpdate) : Nat :=
  us.foldl (fun acc u => min acc u.htlcMaximumMsat.val) U64_MAX

theorem feasibleAmount_iff_window (us : List ChannelUpdate) (a : Nat)
    (hne : us ≠ []) :
    (∀ u ∈ us, u.htlcMinimumMsat.val ≤ a ∧ a ≤ u.htlcMaximumMsat.val) ↔
      pathHtlcLo us ≤ a ∧ a ≤ pathHtlcHi us

/-- Two individually well-formed updates can still leave no feasible amount. -/
theorem pathHtlcWindow_empty_witness :
    ∃ us : List ChannelUpdate,
      us ≠ [] ∧
      (∀ u ∈ us, u.wellFormed) ∧
      pathHtlcHi us < pathHtlcLo us
```

Hypotheses: non-empty path for the iff (the empty case is vacuous but the
default window is not). Non-vacuity: `us` with `(min,max) = (10,1000),
(20,900), (30,800)` gives window `[30,800]`, and `500` satisfies all three.
Empty witness: `(10,20)` and `(100,200)` are both well-formed but the window is
empty. Why faithful: this is the exact fold LDK Node performs in
`probing.rs:619-693` and the per-edge check in `router.rs:384-386`. It also
records that per-hop `wellFormed` does not imply a feasible path amount, a
non-obvious and useful negative result.

### T5 — `LnLean.Proofs.Routing.RouteSelectionTargets.selectRoute_spec`
**Priority: P1. Fidelity risk: medium (scope must say "finite candidates, not LDK Dijkstra"). Feasibility: medium–high. Model extension: specification layer.**

```lean
namespace LnLean.Routing

/-- Deterministic argmin over a finite candidate list. -/
def selectRoute (cost : Route → Nat) : List Route → Option Route
  | [] => none
  | r :: rs =>
      match selectRoute cost rs with
      | none => some r
      | some best => some (if cost r ≤ cost best then r else best)

theorem selectRoute_spec {cost : Route → Nat} {cs : List Route} {r : Route}
    (h : selectRoute cost cs = some r) :
    r ∈ cs ∧ ∀ q ∈ cs, cost r ≤ cost q

theorem selectRoute_none_iff {cost : Route → Nat} {cs : List Route} :
    selectRoute cost cs = none ↔ cs = []

/-- Candidate generation is finite and filtered by `Forwardable`. -/
def candidateRoutes (g : Graph) (src dst : NodeId) (maxHops : Nat)
    (minFinal maxTotal : Nat) (a : Msat) : List Route :=
  -- `simplePaths` + `constructRoute` + `Forwardable` filter; exact API to be
  -- fixed by the implementer.

theorem selectedRoute_feasible {g src dst maxHops minFinal maxTotal a r}
    (h : selectRoute (routeCost g) (candidateRoutes g src dst maxHops
          minFinal maxTotal a) = some r) :
    routeValid g r ∧ r.ChainBacked g
```

Hypotheses: `cost` is a total function; `candidateRoutes` is finite by
construction (`simplePaths` is fuel-bounded). Non-vacuity: a two-path graph
with costs 10 and 20 selects 10; the `demoGraph` one-hop candidate selects the
demo route. Why faithful: it specifies a **sound and optimal selector over the
enumerated finite candidate set**, which is exactly what LDK's search
approximates. It must not be advertised as LDK's Dijkstra: `router.rs:2859-2888`
explicitly accepts de-preferenced liquidity-limited paths, and the candidate
enumerator is not complete. The scope note is part of the target.

### T6 — `LnLean.Proofs.Routing.LiquidityBoundsTargets.observe_*`
**Priority: P1. Fidelity risk: low for the update algebra; medium if mislabeled as the scorer. Feasibility: high. Model extension: yes (new finite state).**

```lean
namespace LnLean.Proofs.Routing

/-- Lower/upper liquidity bounds and channel capacity, all in msat. -/
structure Bounds where
  lo : Nat
  hi : Nat
  cap : Nat

def Bounds.ok (b : Bounds) : Prop := b.lo ≤ b.hi ∧ b.hi ≤ b.cap

/-- LDK `failed_at_channel` / `set_max_liquidity_msat` (`scoring.rs:1642-1656`,
    `:1703-1709`). -/
def Bounds.failAt (b : Bounds) (a : Nat) : Bounds :=
  { b with
    hi := min b.hi a
    lo := if a < b.lo then 0 else b.lo }

/-- LDK `failed_downstream` / `set_min_liquidity_msat` (`:1658-1673`,
    `:1710-1716`): note the upper bound resets to capacity when `a > hi`. -/
def Bounds.failDownstream (b : Bounds) (a : Nat) : Bounds :=
  { b with
    lo := max b.lo a
    hi := if b.hi < a then b.cap else b.hi }

/-- LDK `successful` (`:1676-1687`). -/
def Bounds.succeed (b : Bounds) (a : Nat) : Bounds :=
  { b with
    hi := b.hi - a
    lo := if b.hi - a < b.lo then 0 else b.lo }

theorem failAt_ok (b : Bounds) (a : Nat) (h : b.ok) : (b.failAt a).ok
theorem failDownstream_ok (b : Bounds) (a : Nat) (h : b.ok) (ha : a ≤ b.cap) :
    (b.failDownstream a).ok
theorem succeed_ok (b : Bounds) (a : Nat) (h : b.ok) : (b.succeed a).ok

theorem failAt_hi_le (b : Bounds) (a : Nat) : (b.failAt a).hi ≤ b.hi
theorem failDownstream_lo_ge (b : Bounds) (a : Nat) : b.lo ≤ (b.failDownstream a).lo

/-- The naive "bounds only tighten" claim is false. -/
theorem failDownstream_widens_hi :
    ∃ (b : Bounds) (a : Nat), b.ok ∧ b.hi < (b.failDownstream a).hi
```

Hypotheses: `a ≤ cap` for downstream preservation; the witness uses
`lo=100, hi=300, cap=1000, a=400`, giving `(400,1000)`. Non-vacuity:
`(100,1000,1000)` → `failAt 500 = (100,500)` → `succeed 200 = (100,300)` →
`failDownstream 400 = (400,1000)`. Why faithful: the formulas are the exact
integer operations LDK performs, not an invented scoring rule. It deliberately
does **not** claim the probability/penalty formula. The `failDownstream`
widening theorem preserves a real fidelity trap rather than hiding it.

### T7 — `LnLean.Proofs.Routing.ScoreMergeTargets.mergeOffset_between`
**Priority: P2. Fidelity risk: low. Feasibility: trivial. Model extension: no (new function only).**

```lean
namespace LnLean.Proofs.Routing

/-- LDK `ChannelLiquidity::merge` average (`scoring.rs:1262-1267`). -/
def mergeOffset (a b : Nat) : Nat := (a + b) / 2

theorem mergeOffset_between (a b : Nat) :
    min a b ≤ mergeOffset a b ∧ mergeOffset a b ≤ max a b

theorem mergeOffset_comm (a b : Nat) : mergeOffset a b = mergeOffset b a

/-- Re-merging the same external value is not idempotent in general. -/
theorem mergeOffset_not_idempotent :
    ∃ a b : Nat, mergeOffset (mergeOffset a b) b ≠ mergeOffset a b
```

Hypotheses: none. Non-vacuity: `mergeOffset 0 3 = 1`; `mergeOffset 1 3 = 2`.
Why faithful: it captures only the offset merge; it does not claim the full
`ChannelLiquidities` map merge, historical buckets, or decay. It is useful as a
warning against a persistence theorem that assumes idempotence.

### T8 — `LnLean.Proofs.Routing.ChannelUpdateTargets.wellFormed_allows_excess_htlcMax`
**Priority: P2. Fidelity risk: low. Feasibility: trivial. Model extension: no (counterexample + conditional bridge).**

```lean
namespace LnLean.Routing

/-- BOLT 7 `:567-573` says an update with `htlc_maximum_msat > capacity`
    should be ignored during route considerations. -/
theorem wellFormed_allows_excess_htlcMax :
    ∃ (u : ChannelUpdate) (capSat : Nat),
      u.wellFormed ∧ capSat * Msat.MSAT_PER_SAT < u.htlcMaximumMsat.val

/-- Conditional bridge: add the missing BOLT 7 capacity conjunct. -/
def ChannelUpdate.wellFormedForCapacity (u : ChannelUpdate) (capSat : Nat) : Prop :=
  u.wellFormed ∧ u.htlcMaximumMsat.val ≤ capSat * Msat.MSAT_PER_SAT

theorem wellFormedForCapacity_htlcMax {u : ChannelUpdate} {capSat : Nat}
    (h : u.wellFormedForCapacity capSat) :
    u.htlcMaximumMsat.val ≤ capSat * Msat.MSAT_PER_SAT
```

Hypotheses: none for the negative witness; capacity for the conditional form.
Non-vacuity: `timestamp=1, cltvDelta=1, min=0, max=1000, capSat=0` is
`wellFormed` and violates the BOLT 7 capacity rule. Why faithful: this records
that the current `wellFormed` (`Gossip.lean:179-181`) is intentionally weaker
than BOLT 7 and must not be used as a routing admission predicate without the
capacity conjunct.

## 5. Assumptions, counterexamples, and non-vacuity risks

### 5.1 Must-retain counterexamples

* `LnLean.Proofs.Routing.GraphProps.selfLoopEdge_not_connects`,
  `model_allows_self_loop`, `findEdge_zeroCapacity` (`:266-307`). Do not add a
  `Graph.WellFormed` field or an admission invariant that silently removes
  them; they are the evidence that `findEdge` is not a route selector.
* `LnLean.Proofs.Routing.RouteBlindingProps.ofEdge_rounding_counterexample`
  (`:252-258`). The new fee target must preserve it and add the direct
  Lean-vs-LDK witness, not replace it.
* `LnLean.Proofs.Payment.LiquidityProps` boundary notes (`:76-95`):
  `availableOutbound` is an upper bound that omits commitment fees, anchors,
  dust, and in-flight HTLCs. Do not state it equals LDK's
  `outbound_capacity_msat`.
* The new witnesses in T1–T8: disconnected `routeValid`, fee +1, non-forwardable
  `FeasiblePath`, empty HTLC window, downstream `hi` widening, non-idempotent
  merge, excess `htlc_maximum_msat`.

### 5.2 Non-vacuity witnesses to preserve

* `LnLean.Proofs.PhaseC3.CrossChannelRouting.demoEdge`, `demoGraph`,
  `demoLiquidity`, `demoPlan`, `demoPlan_route_valid`
  (`:578-620`) — the only concrete multi-hop-capable route witness today.
* `LnLean.Proofs.Routing.RouteBlindingProps.exampleRoute` and its `decide`
  facts (`:611-665`).
* Any new `selectRoute` target needs both a non-empty candidate witness and an
  empty-candidate `none` case; otherwise `selectRoute_spec` is vacuously true
  on `[]`.

### 5.3 Assumptions that must stay explicit

* **Failure attribution.** LDK scores the reported failing `short_channel_id`
  and every hop before it (`scoring.rs:1764-1810`). The model may assume an
  honest `FailureReport`; it must not prove that the reported hop is the
  responsible one.
* **Liquidity is unobservable.** Announced capacity is not live balance
  (`probing.rs:8-18`). `LiquidityModel.availableMsat` is an oracle; any
  theorem is conditional on it. Do not derive it from `capacitySat`.
* **External scores are trusted data.** `CombinedScorer::merge` averages local
  and external bounds (`scoring.rs:1904-1920`); the provider is unauthenticated
  in this model. No safety claim about a malicious provider follows.
* **Time/decay.** All half-lives are real-time and external. Do not state a
  decay theorem without a clock model.
* **LDK search is not optimal.** `router.rs:2859-2888` explicitly accepts
  de-preferenced paths and skips paths below 5% of the target. A Lean
  `selectRoute` optimality theorem is only about its own candidate list.
* **MPP/number of paths.** `max_path_count`, saturation power, and sender-side
  splitting are configuration/policy (`bolt11.rs:839-851`); they are not
  protocol invariants.

### 5.4 Proposals that would weaken or hide existing claims

* Do **not** redefine `routeValid` to include connectivity or capacity in place.
  That would change the meaning of `FeasiblePath.route_valid`,
  `constructRoute_valid`, `findEdge_route_valid`, and the `LN-RT-001` evidence.
  Add `ChainBacked`/`Forwardable` and prove bridges; leave the old predicate
  intact.
* Do **not** add `feeBound` or `htlc` fields to `FeasiblePath` and then reuse
  the existing `demoPlan` proof without re-checking it. `FeasiblePath` is a
  structure; strengthening its fields is a model change, not a free theorem.
* Do **not** replace `Hop.ofEdge`'s ceiling with truncation to "match LDK".
  That would invalidate `ofEdge_rounding_counterexample` and change every
  existing `totalFee` result. Add the comparison theorem and keep both
  semantics explicit.
* Do **not** claim `selectRoute` refines LDK's `find_route`. The best true
  statement is optimality over the finite enumerated candidates. Stating more
  would hide the non-Dijkstra caveat at `router.rs:2859-2888`.
* Do **not** claim `mergeOffset` is idempotent or associative. The
  non-idempotence witness is part of the model's honesty.
* Do **not** turn `LiquidityModel.availableMsat` into `capacitySat * 1000` by
  default and call the result "liquidity". That collapses the only genuinely
  unknown quantity into a gossip field.

## 6. Wave-13 recommendation

**Safe implementation lane: yes, but only for the finite fidelity layer.**
Targets T1, T2, T4, T6, and T8 are pure additive proofs over existing types or
small local records; they can be implemented in one or two proof modules with
no model weakening and no new axioms. T3 and T5 are also implementable but
require an explicit policy-parameter interface and a clear "finite candidates"
scope note; they should be a second, dependent step. T7 is a cheap P2 add-on.

Recommended order:

1. **T1 (P0)** — makes the graph route type honest before any selector work.
2. **T2 (P1)** — cheapest, highest-signal fidelity correction to the fee model.
3. **T4 (P1)** — exact HTLC-window algebra already present in LDK Node probing.
4. **T6 (P1)** — the finite failure/success update algebra, with the
   non-monotone witness.
5. **T3/T5 (P1)** — forwardable predicate and finite selection spec, after T1
   and T4 define the candidate route.
6. **T8/T7 (P2)** — retained negative results / persistence warning.

**External barrier (do not code as a proof target):** the probabilistic
scorer's probability/penalty formula, real-time decay, historical buckets,
in-flight HTLC state, live probing, external-score HTTP sync and provider trust,
and any claim that LDK's `find_route` is optimal/complete. These are either
probabilistic/network assumptions or out-of-model state. A finite Lean model
can describe the *update algebra* and the *shape* of the penalty monotonicity,
but not the success probability of a real channel.

**Catalog decision:** the catalog is closed at 51 rows / 294 targets. Do not add
a new row just for these targets. Attach T1/T2/T4/T6 as scope evidence to
`LN-RT-001`/`LN-RT-005` if the parent wants them in traceability, or introduce a
single `LN-RT-007` only if the parent accepts the finite-selection scope. The
real scoring/liquidity gap remains open regardless; it is not closable by a
finite proof lane.

## 7. Evidence and commands

Read-only inspection commands used (all run from `/home/ubuntu/ln-lean-repair`):

```sh
git -C /tmp/opencode/ldk-refs/ldk-node rev-parse HEAD
git -C /tmp/opencode/ldk-refs/ldk-server rev-parse HEAD
git -C refs/rust-lightning rev-parse HEAD

rg -n "LN-RT-00" LnLean/Proofs/Obligations.lean docs/THEOREM-INDEX.md docs/TRACEABILITY.md
sed -n '305,360p' LnLean/Proofs/Obligations.lean

sed -n '125,135p;320,330p;50,61p' LnLean/Routing/Route.lean
sed -n '330,385p' LnLean/Security/Invariants.lean
sed -n '150,200p' LnLean/Routing/Gossip.lean
sed -n '160,200p' LnLean/Routing/Graph.lean
sed -n '370,420p;490,520p;575,625p' LnLean/Proofs/PhaseC3/CrossChannelRouting.lean
sed -n '95,110p;250,260p' LnLean/Proofs/Routing/RouteBlindingProps.lean
sed -n '260,310p' LnLean/Proofs/Routing/GraphProps.lean
sed -n '70,100p;145,165p' LnLean/Proofs/Payment/LiquidityProps.lean

rg -n "fn find_route|fn compute_fees|MAX_PATH_LENGTH_ESTIMATE|DEFAULT_MAX_TOTAL_CLTV" \
  refs/rust-lightning/lightning/src/routing/router.rs
sed -n '380,400p;2637,2643p;2797,2895p' \
  refs/rust-lightning/lightning/src/routing/router.rs
sed -n '455,476p;1262,1270p;1506,1600p;1642,1716p;1764,1930p' \
  refs/rust-lightning/lightning/src/routing/scoring.rs

sed -n '1,30p;95,125p;533,547p;619,693p' /tmp/opencode/ldk-refs/ldk-node/src/probing.rs
sed -n '1,102p' /tmp/opencode/ldk-refs/ldk-node/src/scoring.rs
sed -n '202,240p;805,860p' /tmp/opencode/ldk-refs/ldk-node/src/payment/bolt11.rs
sed -n '2543,2564p' /tmp/opencode/ldk-refs/ldk-node/src/lib.rs
sed -n '2098,2136p' /tmp/opencode/ldk-refs/ldk-node/src/builder.rs
sed -n '95,110p' /tmp/opencode/ldk-refs/ldk-node/src/graph.rs
sed -n '1,24p' /tmp/opencode/ldk-refs/ldk-server/ldk-server/src/api/export_pathfinding_scores.rs
sed -n '20,80p' /tmp/opencode/ldk-refs/ldk-server/ldk-server/src/api/get_node_info.rs
```

No Lean build, no `cargo` test, and no file outside this report was modified.
The report is source-grounded only; the proposed targets are not claimed to
exist until a later implementation lane compiles them and the catalog checker
resolves the exact names.
