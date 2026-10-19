# W14-ROUTE-CHAIN — chain-backed route predicate

**Lane:** W14-ROUTE-CHAIN (Wave 14)
**Worktree:** `/home/ubuntu/ln-lean-waveh`
**Branch:** `wave-14/16`
**Base:** `a331b71`
**Status:** complete; scoped build green.

## 1. Scope

Implement R32 §4 T4 / gap G12 (`docs/OPEN-ISSUES.md` row `REV-04`) as an
**additive** predicate: chain-backed route validity over
`LnLean.Routing.Route`, with no redefinition of `routeValid`.

The legacy carrier is unchanged:

- `LnLean.Routing.routeValid` still checks each hop independently against
  some enabled graph edge (`Route.lean:325-327`);
- `routeValid_edge_sound` and `constructRoute_valid` keep their old
  statements;
- `Route.lean` (and every other existing Lean module) was not edited.

The new carrier is `ChainWitness` / `ChainBacked`, and the production-facing
predicate is `routeChainValid`. A chain witness is an explicit list of graph
edges, one per hop, all present in the graph, all enabled, each using the
hop's `short_channel_id` and ending at the hop's node, with consecutive edges
adjacent (`edges[i].node2 = edges[i+1].node1`). The first edge's source is not
constrained because a `Route` does not carry its own source node.

**Explicit boundary.** This is a graph-connectivity predicate only. It does
not model capacity, `htlc_maximum_msat`, scoring, in-flight liquidity, or
pathfinding (R32 G14), and it does not claim that `routeValid` itself is
connected. A chain witness is existential, not unique. No new claim is made
about `Hop.ofEdge` fee/CLTV arithmetic (G13 is the separate route-fee lane).

## 2. Owned files

Only these files were created or modified:

- `LnLean/Proofs/Wave14/RouteChain.lean`
- `agents/reports/wave14/W14-ROUTE-CHAIN.md`

No shared file, root import, audit file, catalog file, script, docs file, or
other lane's Lean module/report was edited.

## 3. Headline definitions and exact statements

All declarations live in namespace
`LnLean.Proofs.Wave14.RouteChain` and import `LnLean.Routing.Route` (which
supplies `Graph`, `ChannelEdge`, `NodeId`, `Hop`, `Route`, `constructRoute`,
and `routeValid`).

```lean
def ChainLink (g : Graph) (e : ChannelEdge) (h : Hop) : Prop :=
  e ∈ g.edges ∧ e.enabled = true ∧
    e.shortChannelId = h.shortChannelId ∧ e.node2 = h.node

structure ChainWitness (g : Graph) (r : Route) where
  edges : List ChannelEdge
  nonempty : edges ≠ []
  length_eq : edges.length = r.hops.length
  linked : ∀ (i : Nat) (hi : i < edges.length) (hj : i < r.hops.length),
    ChainLink g edges[i] r.hops[i]
  adjacent : ∀ (i : Nat) (hi : i + 1 < edges.length),
    edges[i].node2 = edges[i + 1].node1

def ChainBacked (g : Graph) (r : Route) : Prop :=
  Nonempty (ChainWitness g r)

def routeChainValid (g : Graph) (r : Route) : Prop :=
  r.NonEmpty ∧ ChainBacked g r
```

`ChainWitness` is Type-valued because it carries the explicit edge list;
`ChainBacked` is the `Prop`-valued existence form used in implications and
negations.

Headline theorems:

```lean
theorem chainBacked_nonempty {g : Graph} {r : Route}
    (h : ChainBacked g r) : r.NonEmpty

theorem routeChainValid_iff_chainBacked {g : Graph} {r : Route} :
    routeChainValid g r ↔ ChainBacked g r

theorem routeChainValid_implies_routeValid {g : Graph} {r : Route}
    (h : routeChainValid g r) : routeValid g r

theorem constructRoute_chainBacked (g : Graph)
    (path : List (ChannelEdge × Msat)) (amountMsat : Msat)
    (hne : path ≠ [])
    (hmem : ∀ p ∈ path, p.1 ∈ g.edges)
    (hen : ∀ p ∈ path, p.1.enabled = true)
    (hconn : ∀ (i : Nat) (hi : i + 1 < path.length),
      path[i].1.node2 = path[i + 1].1.node1) :
    ChainBacked g (constructRoute path amountMsat)

theorem constructRoute_routeChainValid (g : Graph)
    (path : List (ChannelEdge × Msat)) (amountMsat : Msat)
    (hne : path ≠ []) (hmem : ∀ p ∈ path, p.1 ∈ g.edges)
    (hen : ∀ p ∈ path, p.1.enabled = true)
    (hconn : ∀ (i : Nat) (hi : i + 1 < path.length),
      path[i].1.node2 = path[i + 1].1.node1) :
    routeChainValid g (constructRoute path amountMsat)

theorem routeValid_not_chainBacked :
    ∃ (g : Graph) (r : Route), routeValid g r ∧ ¬ ChainBacked g r

theorem routeValid_not_routeChainValid :
    ∃ (g : Graph) (r : Route), routeValid g r ∧ ¬ routeChainValid g r
```

`routeChainValid_implies_routeValid` is the required refinement: the chain
supplies the same enabled, same-`short_channel_id`, same-destination edge for
each hop that `routeValid` asks for. `constructRoute_chainBacked` uses the
candidate path itself as the edge list; the non-emptiness hypothesis is used
for the witness' `nonempty` field, membership/enabled for `linked`, and
adjacency for `adjacent`.

## 4. Concrete non-vacuity witnesses and the theorems that use them

**Negative witness (the G12 counterexample).**

```lean
def node (n : Nat) : NodeId := ⟨n⟩

def witnessEdge (scid src dst : Nat) : ChannelEdge :=
  { shortChannelId := ⟨0, 0, scid⟩, node1 := node src, node2 := node dst,
    capacitySat := 1_000_000, feeBaseMsat := ⟨0⟩,
    feeProportionalMillionths := 0, cltvDelta := 1, enabled := true }

def disjointGraph : Graph :=
  { edges := [witnessEdge 1 0 1, witnessEdge 2 2 3]
    nodes := [node 0, node 1, node 2, node 3] }

def disjointRoute : Route :=
  { hops := [witnessHop 1 1, witnessHop 3 2], amountMsat := ⟨1000⟩ }
```

The graph has exactly the two enabled edges `0→1` (scid `(0,0,1)`) and
`2→3` (scid `(0,0,2)`). The route has hops `[1, 3]`, using those two scids.

- `disjointRoute_routeValid : routeValid disjointGraph disjointRoute` — each
  hop is backed by its matching enabled edge, so the legacy predicate holds.
- `disjointRoute_not_chainBacked : ¬ ChainBacked disjointGraph disjointRoute`
  — a length-two chain would need the second edge to end at node `3`, hence
  the second edge is `2→3`; adjacency then forces the first edge to end at
  node `2`, but the first hop is node `1`. No witness exists.
- `routeValid_not_chainBacked` packages exactly this graph/route pair.

**Positive witness (non-vacuity of `ChainBacked`).**

```lean
def connectedGraph : Graph :=
  { edges := [witnessEdge 1 0 1, witnessEdge 3 1 2] }

def connectedPath : List (ChannelEdge × Msat) :=
  [(witnessEdge 1 0 1, ⟨1000⟩), (witnessEdge 3 1 2, ⟨1000⟩)]
```

The two enabled edges form `0→1→2` and are adjacent. Theorems:

- `connectedPath_chainBacked :
  ChainBacked connectedGraph (constructRoute connectedPath ⟨1000⟩)` — applies
  `constructRoute_chainBacked` and discharges every hypothesis concretely.
- `connectedPath_routeChainValid` — the same witness satisfies the
  production predicate.
- `connectedPath_routeValid` — via `routeChainValid_implies_routeValid`,
  showing the refinement's premise is inhabited on the same witness.

The negative witness alone would only prove non-universality; the positive
witness proves the new predicate is not empty.

## 5. Build command and result

```sh
cd /home/ubuntu/ln-lean-waveh
export PATH=/dev/shm/btc/elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
LEAN_NUM_THREADS=1 flock -w 3600 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Proofs.Wave14.RouteChain
```

Result:

```text
ℹ [8/8] Built LnLean.Proofs.Wave14.RouteChain (953ms)
Build completed successfully (8 jobs).
```

No `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, or
`@[implemented_by]` occurs in the module. Only the scoped module build was
run; no bare `lake build`, full gate, or network command was run.

## 6. `#print axioms` output

The module ends with:

```lean
#print axioms routeChainValid_implies_routeValid
#print axioms constructRoute_chainBacked
#print axioms routeValid_not_chainBacked
#print axioms routeValid_not_routeChainValid
#print axioms connectedPath_chainBacked
#print axioms connectedPath_routeChainValid
```

Build output (lines are the final file's audit block):

```text
info: LnLean/Proofs/Wave14/RouteChain.lean:305:0: 'LnLean.Proofs.Wave14.RouteChain.routeChainValid_implies_routeValid' depends on axioms: [propext, Quot.sound]
info: LnLean/Proofs/Wave14/RouteChain.lean:306:0: 'LnLean.Proofs.Wave14.RouteChain.constructRoute_chainBacked' depends on axioms: [propext, Quot.sound]
info: LnLean/Proofs/Wave14/RouteChain.lean:307:0: 'LnLean.Proofs.Wave14.RouteChain.routeValid_not_chainBacked' depends on axioms: [propext, Quot.sound]
info: LnLean/Proofs/Wave14/RouteChain.lean:308:0: 'LnLean.Proofs.Wave14.RouteChain.routeValid_not_routeChainValid' depends on axioms: [propext, Quot.sound]
info: LnLean/Proofs/Wave14/RouteChain.lean:309:0: 'LnLean.Proofs.Wave14.RouteChain.connectedPath_chainBacked' depends on axioms: [propext, Quot.sound]
info: LnLean/Proofs/Wave14/RouteChain.lean:310:0: 'LnLean.Proofs.Wave14.RouteChain.connectedPath_routeChainValid' depends on axioms: [propext, Quot.sound]
```

All six headline theorems use only `propext` and `Quot.sound`, within the
allowed `propext` / `Quot.sound` / `Classical.choice` set. No
`Classical.choice` or `sorryAx` appears.

## 7. Review gap closed or narrowed

**G12 / `REV-04`, structural half — narrowed, not fully closed.**

- The missing carrier now exists: `ChainWitness` carries an explicit
  per-hop edge list with graph membership, enabledness, hop-target,
  `short_channel_id` agreement, and pairwise adjacency.
- `routeChainValid_implies_routeValid` proves the new predicate refines the
  retained per-hop predicate, so no old consumer is contradicted.
- `routeValid_not_chainBacked` records the original live defect permanently:
  `0→1` and `2→3` with hops `[1, 3]` pass `routeValid` but are not a chain.
- `constructRoute_chainBacked` proves connected candidate paths produce
  chain-backed routes; `connectedPath_chainBacked` gives a concrete positive
  witness.

**What remains narrow / external:**

- No existing consumer or docstring is rewired by this additive module.
  `routeValid` remains per-hop, and `Route.lean:321-324` still says it is
  "the graph-level check performed by `rust-lightning`'s router", which
  overstates the carrier. The integrator should reword that docstring and
  point at `routeChainValid` (not applied here: file ownership).
- Capacity, `htlc_maximum_msat`, scoring, and in-flight liquidity remain
  unmodelled (G14), and route-fee rounding remains the separate G13 lane.
- The chain predicate constrains channel identity and endpoint adjacency,
  not the actual fee/CLTV values carried by `Hop`; it inherits
  `constructRoute`'s `Hop.ofEdge` behaviour unchanged.
- `Route.WellFormed` in `LnLean.Proofs.Routing.RouteBlindingProps` (pairwise
  distinct `short_channel_id`s) is complementary and is neither imported nor
  changed here.

## 8. Shared-file changes for the integrator (stated, not applied)

1. **Root import:** add `import LnLean.Proofs.Wave14.RouteChain` via the
   Wave 14 aggregator / `scripts/regen-root.sh`. This lane did not edit
   `LnLean.lean`.
2. **Axiom audit registry:** if Wave 14 headlines are enrolled in
   `LnLean/Proofs/PhaseC3/AxiomAudit.lean`, add these six names with matching
   `#print axioms` lines:
   `routeChainValid_implies_routeValid`, `constructRoute_chainBacked`,
   `routeValid_not_chainBacked`, `routeValid_not_routeChainValid`,
   `connectedPath_chainBacked`, `connectedPath_routeChainValid`.
   Expected audit result: `[propext, Quot.sound]` only. The remaining named
   theorems (`chainBacked_nonempty`, `routeChainValid_iff_chainBacked`,
   `constructRoute_routeChainValid`, `disjointRoute_routeValid`,
   `disjointRoute_not_chainBacked`, `connectedPath_routeValid`) are available
   if the registry wants full module coverage.
3. **Docs / catalog:** update `docs/OPEN-ISSUES.md` row `REV-04` to point at
   `LnLean.Proofs.Wave14.RouteChain` and to state that the gap is the
   structural chain predicate, with consumers still on the legacy
   `routeValid` until rewired. Update `docs/TRACEABILITY.md` /
   `docs/THEOREM-INDEX.md` only through their generator or the normal
   catalog workflow.
4. **Existing-module docstring (recommended, not applied):**
   `LnLean/Routing/Route.lean:321-324` should say that `routeValid` is the
   per-hop check and that end-to-end adjacency is `routeChainValid` (or the
   equivalent new predicate). This lane did not edit `Route.lean`.

## 9. Ownership confirmation

No shared or other-lane file was edited. Only the two owned paths in §2 were
written. No `git add`, `git commit`, `git push`, `git switch`, or other Git
write command was run. No network command was run.
