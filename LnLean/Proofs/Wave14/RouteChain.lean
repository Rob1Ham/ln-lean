import LnLean.Routing.Route

/-!
# LnLean.Proofs.Wave14.RouteChain

An additive, chain-backed route predicate for `LnLean.Routing.Route`
(Wave-13 review gap G12 / `REV-04`, R32 §4 T4).  The legacy carrier is not
changed:

* `LnLean.Routing.routeValid` still checks each hop independently against
  some enabled graph edge, with no adjacency condition;
* `routeValid_edge_sound` and `constructRoute_valid` keep their old
  statements.

The strengthened predicate is `ChainBacked`, and its production-facing
conjunction with route non-emptiness is `routeChainValid`:

* `ChainBacked g r` carries an explicit list `edges` of graph edges, one for
  each hop of `r`, such that
  - `edges` is non-empty and has exactly the hop count of `r`;
  - each `edges[i]` is a member of `g.edges`, is enabled, has the same
    `short_channel_id` as hop `i`, and ends at hop `i`'s node;
  - consecutive edges are adjacent: `edges[i].node2 = edges[i+1].node1`.
* `routeChainValid g r` is `r.NonEmpty ∧ ChainBacked g r`, so it refines
  `routeValid` (`routeChainValid_implies_routeValid`).

**The separation is real.**  `routeValid_not_chainBacked` exhibits a graph
with enabled edges `0→1` and `2→3` and a route with hops `[1, 3]`: every hop
is backed by an edge, but the two edges are not adjacent, so no chain witness
exists.  The source of the first edge is deliberately unconstrained (the
route does not carry its own source node), and the chain does not require
anything about the final node beyond the last hop's backing edge.

**Boundaries.**  This module is graph-level only.  It does not model route
capacity, `htlc_maximum_msat`, scoring, in-flight liquidity, or pathfinding
(R32 G14), and it does not claim that `routeValid` itself is connected.  A
chain witness is an existential edge list; it is not claimed to be unique,
and the module does not relate the witness' fee/CLTV fields to
`constructRoute`'s computed `Hop.ofEdge` arithmetic beyond the identity
already provided by `constructRoute`.  The positive witness
`connectedPath_chainBacked` uses `constructRoute` on a concrete two-edge
connected path (`0→1→2`) and is therefore not vacuous.

This file only closes the graph-connectivity half of G12.  Routing capacity,
scoring, and path search remain outside the carrier (see R32 §3 G14).

BOLT 4 describes a route as a sequence of hops, one channel per hop; a
sequence that skips from the destination of one channel to the source of an
unrelated channel is not a route.  R32 §4 T4 cites LDK's connected-path
construction (`refs/rust-lightning/lightning/src/routing/router.rs:2797-2888`);
this module is a structural graph theorem, not a claim about that implementation's
path search or fee arithmetic.
-/

namespace LnLean.Proofs.Wave14.RouteChain

set_option autoImplicit false

open LnLean
open LnLean.Routing

/-! ## Chain witnesses -/

/-- One link of a chain witness: `e` is a graph edge that is present in `g`,
enabled, uses the same `short_channel_id` as hop `h`, and ends at `h.node`. -/
def ChainLink (g : Graph) (e : ChannelEdge) (h : Hop) : Prop :=
  e ∈ g.edges ∧ e.enabled = true ∧
    e.shortChannelId = h.shortChannelId ∧ e.node2 = h.node

/-- A concrete chain witness for a route: exactly one graph edge per hop,
every edge present and enabled in `g`, every edge using the hop's
`short_channel_id` and ending at the hop's node, and every consecutive pair
adjacent (`edges[i].node2 = edges[i+1].node1`).  The first edge's source is
not constrained because a `Route` does not carry its own source node. -/
structure ChainWitness (g : Graph) (r : Route) where
  /-- The explicit chain of graph edges, one per hop. -/
  edges : List ChannelEdge
  /-- A chain witness is non-empty, matching the non-emptiness of a route. -/
  nonempty : edges ≠ []
  /-- The chain has exactly one edge per route hop. -/
  length_eq : edges.length = r.hops.length
  /-- Every edge is in the graph, enabled, and backs the corresponding hop. -/
  linked : ∀ (i : Nat) (hi : i < edges.length) (hj : i < r.hops.length),
    ChainLink g edges[i] r.hops[i]
  /-- Consecutive chain edges meet: `node2` of one is `node1` of the next. -/
  adjacent : ∀ (i : Nat) (hi : i + 1 < edges.length),
    edges[i].node2 = edges[i + 1].node1

/-- A route is chain-backed when a `ChainWitness` exists.  This is the
propositional reading of the explicit adjacent edge list. -/
def ChainBacked (g : Graph) (r : Route) : Prop :=
  Nonempty (ChainWitness g r)

/-- The production-facing chain-backed route predicate: the route is
non-empty and has an explicit adjacent, enabled edge chain in the graph.

This is strictly stronger than `LnLean.Routing.routeValid`; that legacy
per-hop predicate is deliberately left unchanged. -/
def routeChainValid (g : Graph) (r : Route) : Prop :=
  r.NonEmpty ∧ ChainBacked g r

/-- A chain witness entails route non-emptiness. -/
theorem chainBacked_nonempty {g : Graph} {r : Route} (h : ChainBacked g r) :
    r.NonEmpty := by
  obtain ⟨w⟩ := h
  intro hnil
  apply w.nonempty
  exact List.eq_nil_of_length_eq_zero (by rw [w.length_eq, hnil]; rfl)

/-- `routeChainValid` is exactly non-emptiness plus a chain witness. -/
theorem routeChainValid_iff_chainBacked {g : Graph} {r : Route} :
    routeChainValid g r ↔ ChainBacked g r :=
  ⟨fun h => h.2, fun h => ⟨chainBacked_nonempty h, h⟩⟩

/-! ## Refinement of the legacy per-hop predicate -/

/-- **Chain-backed validity refines per-hop validity.**  Every hop of a
chain-backed route is still backed by an enabled graph edge with the same
`short_channel_id` and destination, so the legacy `routeValid` holds.  The
converse is false; see `routeValid_not_chainBacked`. -/
theorem routeChainValid_implies_routeValid {g : Graph} {r : Route}
    (h : routeChainValid g r) : routeValid g r := by
  rcases h with ⟨hne, hchain⟩
  obtain ⟨w⟩ := hchain
  refine ⟨hne, ?_⟩
  intro hop hhop
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hhop
  have hi' : i < w.edges.length := by rw [w.length_eq]; exact hi
  have hlink := w.linked i hi' hi
  exact ⟨w.edges[i], hlink.1, hlink.2.1, hlink.2.2.1, hlink.2.2.2⟩

/-! ## Construction from a connected candidate path -/

/-- **A connected candidate edge path constructs a chain-backed route.**
The hypotheses are exactly the graph data needed for the chain: the path is
non-empty, every edge is a member of `g`, every edge is enabled, and
consecutive path edges are adjacent.  No capacity, scoring, or pathfinding
claim is made. -/
theorem constructRoute_chainBacked (g : Graph)
    (path : List (ChannelEdge × Msat)) (amountMsat : Msat)
    (hne : path ≠ [])
    (hmem : ∀ p ∈ path, p.1 ∈ g.edges)
    (hen : ∀ p ∈ path, p.1.enabled = true)
    (hconn : ∀ (i : Nat) (hi : i + 1 < path.length),
      path[i].1.node2 = path[i + 1].1.node1) :
    ChainBacked g (constructRoute path amountMsat) := by
  refine
    ⟨{ edges := path.map (fun p => p.1)
       nonempty := ?_
       length_eq := ?_
       linked := ?_
       adjacent := ?_ }⟩
  · intro hnil
    exact hne (List.map_eq_nil_iff.mp hnil)
  · simp [constructRoute]
  · intro i hi hj
    simp only [constructRoute_hops, List.getElem_map]
    exact ⟨hmem _ (List.getElem_mem _), hen _ (List.getElem_mem _), rfl, rfl⟩
  · intro i hi
    have hi' : i + 1 < path.length := by simpa using hi
    simpa using hconn i hi'

/-- The `routeChainValid` form of `constructRoute_chainBacked`; the extra
non-emptiness is the first conjunct of the production predicate. -/
theorem constructRoute_routeChainValid (g : Graph)
    (path : List (ChannelEdge × Msat)) (amountMsat : Msat)
    (hne : path ≠ [])
    (hmem : ∀ p ∈ path, p.1 ∈ g.edges)
    (hen : ∀ p ∈ path, p.1.enabled = true)
    (hconn : ∀ (i : Nat) (hi : i + 1 < path.length),
      path[i].1.node2 = path[i + 1].1.node1) :
    routeChainValid g (constructRoute path amountMsat) :=
  ⟨by simp [Route.NonEmpty, constructRoute, hne],
    constructRoute_chainBacked g path amountMsat hne hmem hen hconn⟩

/-! ## Concrete witnesses -/

/-- Opaque witness node with index `n`. -/
def node (n : Nat) : NodeId := ⟨n⟩

/-- A concrete enabled directed edge with `short_channel_id` `(0, 0, scid)`. -/
def witnessEdge (scid src dst : Nat) : ChannelEdge :=
  { shortChannelId := ⟨0, 0, scid⟩
    node1 := node src
    node2 := node dst
    capacitySat := 1_000_000
    feeBaseMsat := ⟨0⟩
    feeProportionalMillionths := 0
    cltvDelta := 1
    enabled := true }

/-- A concrete hop reaching node `n` over channel `(0, 0, scid)`. -/
def witnessHop (n scid : Nat) : Hop :=
  { node := node n
    shortChannelId := ⟨0, 0, scid⟩
    feeMsat := ⟨0⟩
    cltvDelta := 1 }

/-- The disconnected graph with enabled edges `0→1` and `2→3`. -/
def disjointGraph : Graph :=
  { edges := [witnessEdge 1 0 1, witnessEdge 2 2 3]
    nodes := [node 0, node 1, node 2, node 3] }

/-- The route with hops `[1, 3]`, one per disjoint edge. -/
def disjointRoute : Route :=
  { hops := [witnessHop 1 1, witnessHop 3 2]
    amountMsat := ⟨1000⟩ }

/-- The disconnected route passes the legacy per-hop `routeValid`. -/
theorem disjointRoute_routeValid : routeValid disjointGraph disjointRoute := by
  refine ⟨by simp [Route.NonEmpty, disjointRoute], ?_⟩
  intro h hh
  simp only [disjointRoute, List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl
  · exact ⟨witnessEdge 1 0 1, by simp [disjointGraph], rfl, rfl, rfl⟩
  · exact ⟨witnessEdge 2 2 3, by simp [disjointGraph], rfl, rfl, rfl⟩

/-- **Per-hop validity is not chain-backed.**  The route `[1, 3]` over the
disjoint enabled edges `0→1` and `2→3` passes `routeValid`, but no edge list
of length two can both back the hops and be adjacent: the only edge ending at
node `3` is `2→3`, so the first edge would have to end at `2`, while the
route's first hop is node `1`. -/
theorem disjointRoute_not_chainBacked : ¬ ChainBacked disjointGraph disjointRoute := by
  intro h
  obtain ⟨w⟩ := h
  have hlen2 : w.edges.length = 2 := by
    simpa [disjointRoute] using w.length_eq
  have h0 := w.linked 0 (by omega) (by simp [disjointRoute])
  have h1 := w.linked 1 (by omega) (by simp [disjointRoute])
  have hn0 : w.edges[0].node2 = node 1 := by
    simpa [disjointRoute, witnessHop, node] using h0.2.2.2
  have hn1 : w.edges[1].node2 = node 3 := by
    simpa [disjointRoute, witnessHop, node] using h1.2.2.2
  have he1 : w.edges[1] = witnessEdge 2 2 3 := by
    have hmem : w.edges[1] = witnessEdge 1 0 1 ∨
        w.edges[1] = witnessEdge 2 2 3 := by
      simpa [disjointGraph] using h1.1
    rcases hmem with hh | hh
    · rw [hh] at hn1
      simp [witnessEdge, node] at hn1
    · exact hh
  have hadj0 : w.edges[0].node2 = node 2 := by
    have hh := w.adjacent 0 (by omega)
    rw [he1] at hh
    simpa [witnessEdge, node] using hh
  have hh := hn0
  rw [hadj0] at hh
  simp [node] at hh

/-- The separation witness as an existential over graphs and routes. -/
theorem routeValid_not_chainBacked :
    ∃ (g : Graph) (r : Route), routeValid g r ∧ ¬ ChainBacked g r :=
  ⟨disjointGraph, disjointRoute, disjointRoute_routeValid,
    disjointRoute_not_chainBacked⟩

/-- The same separation stated for the production predicate
`routeChainValid`. -/
theorem routeValid_not_routeChainValid :
    ∃ (g : Graph) (r : Route), routeValid g r ∧ ¬ routeChainValid g r := by
  refine ⟨disjointGraph, disjointRoute, disjointRoute_routeValid, ?_⟩
  intro h
  exact disjointRoute_not_chainBacked h.2

/-- The connected graph `0→1→2`. -/
def connectedGraph : Graph :=
  { edges := [witnessEdge 1 0 1, witnessEdge 3 1 2]
    nodes := [node 0, node 1, node 2] }

/-- The concrete connected candidate path for `0→1→2`. -/
def connectedPath : List (ChannelEdge × Msat) :=
  [(witnessEdge 1 0 1, ⟨1000⟩), (witnessEdge 3 1 2, ⟨1000⟩)]

/-- **Positive non-vacuity witness.**  The concrete connected path
`0→1→2` constructs a chain-backed route in `connectedGraph`. -/
theorem connectedPath_chainBacked :
    ChainBacked connectedGraph (constructRoute connectedPath ⟨1000⟩) := by
  apply constructRoute_chainBacked
  · simp [connectedPath]
  · intro p hp
    simp only [connectedPath, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp [connectedGraph]
  · intro p hp
    simp only [connectedPath, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> rfl
  · intro i hi
    have hi2 : i + 1 < 2 := by simpa [connectedPath] using hi
    have hi0 : i = 0 := by omega
    subst hi0
    simp [connectedPath, witnessEdge, node]

/-- The positive witness satisfies the production predicate. -/
theorem connectedPath_routeChainValid :
    routeChainValid connectedGraph (constructRoute connectedPath ⟨1000⟩) :=
  ⟨by simp [Route.NonEmpty, constructRoute, connectedPath],
    connectedPath_chainBacked⟩

/-- The positive witness also satisfies the legacy `routeValid`, via the
refinement theorem. -/
theorem connectedPath_routeValid :
    routeValid connectedGraph (constructRoute connectedPath ⟨1000⟩) :=
  routeChainValid_implies_routeValid connectedPath_routeChainValid

/-! ## Axiom audit -/

#print axioms routeChainValid_implies_routeValid
#print axioms constructRoute_chainBacked
#print axioms routeValid_not_chainBacked
#print axioms routeValid_not_routeChainValid
#print axioms connectedPath_chainBacked
#print axioms connectedPath_routeChainValid

end LnLean.Proofs.Wave14.RouteChain
