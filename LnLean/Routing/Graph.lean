import LnLean.Basic.Core

/-!
# LnLean.Routing.Graph

The public-channel graph of BOLT 7, as a finite list of directed channel
edges.

English claim of this module:

* `NodeId` names a graph node, `ChannelEdge` is one *directed* announcement
  usable for forwarding, and `Graph` is a finite set of edges plus nodes.
* `Graph.neighbors`, `Graph.findEdge`, and `Graph.simplePaths` compute,
  respectively, the adjacent nodes, the first enabled edge between two
  nodes, and fuel-bounded simple paths from a source to a destination.
* The structural lemmas show that every value returned by `findEdge` really
  is an enabled edge of the graph with the requested endpoints, and that
  every path returned by `simplePaths` is non-empty and starts at the
  requested source.

BOLT sections:

* BOLT 7, "The `channel_announcement` Message" (a channel is identified by
  `short_channel_id`, has two `node_id`s, and carries a `capacity` in satoshis).
* BOLT 7, "The `channel_update` Message" (per-direction `fee_base_msat`,
  `fee_proportional_millionths`, `cltv_expiry_delta`, and the `disable`
  flag).
* BOLT 7, "Graph" / "Pseudo-Descriptions" (nodes are announced separately
  from channels; the graph is public and finite).
* BOLT 4, "Routing" (a route is a sequence of channels between nodes).

`rust-lightning` anchors (pinned commit `fe4900930c6bd5786ec4203274d7cf312776a5a6`;
line numbers are anchored to the symbol, see `agents/reports/A6.md` for the
pin-verification caveat):

* `lightning/src/routing/gossip.rs:583` — `pub struct ChannelInfo`, the
  per-channel record (`short_channel_id`, `node_one`, `node_two`, and the
  two directional `ChannelUpdate`s).
* `lightning/src/routing/gossip.rs:1130` — `NetworkGraph`, which owns
  `channels: BTreeMap<u64, ChannelInfo>` and `nodes: BTreeMap<PublicKey,
  NodeInfo>`.
* `lightning/src/routing/gossip.rs:1870` — `NetworkGraph::channel`
  (short-channel-id lookup).
* `lightning/src/routing/router.rs:3110` — `Router::find_route`, the
  production route search (Dijkstra-like), of which `simplePaths` is only
  the enumerable-path abstraction.

What is **not** modelled:

* BOLT 7 wire serialization, chain-hash filtering, and the `node_id`
  signature check (those live in `LnLean.Routing.Gossip` only as abstract
  predicates).
* Multi-part and blinded routes; the graph is a plain public graph.
* The per-direction fee *computation* against an amount. `ChannelEdge`
  stores the base fee and the proportional rate; applying the rate is in
  `LnLean.Routing.Route`.
* Dijkstra/A\* optimality, graph diameter, and connectivity. `simplePaths`
  is a fuel-bounded enumerator, not a shortest-path oracle. In particular
  `simplePaths` does **not** return all simple paths when `maxHops` is too
  small, and the model does not claim completeness.
* MPP, route hints, and private channels (no `channel_update`).
-/

namespace LnLean.Routing

set_option autoImplicit false

/-! ## Nodes and edges -/

/-- A graph node.

BOLT 7 identifies a node by its 33-byte `node_id` public key.  For the
graph algorithms we only need a small opaque identifier; the public key and
its announcement live in `LnLean.Routing.Gossip`.  This keeps the graph
algorithms independent of the byte-level key representation while remaining
faithful to the *structure* of the public graph. -/
structure NodeId where
  /-- Opaque node index.  Not the BOLT 7 wire `node_id`. -/
  index : Nat
deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq, Inhabited, Ord

/-- A directed channel edge, i.e. one direction of one `channel_announcement`
plus the matching `channel_update`.

`short_channel_id` is the BOLT 7 channel identifier.  `capacitySat` is the
BOLT 7 `capacity` (the funding output value, in satoshis).  `node1` is the
forwarding node and `node2` the next node; the reverse direction is a
separate `ChannelEdge` in the graph.  `feeBaseMsat` and
`feeProportionalMillionths` are BOLT 7's `fee_base_msat` and
`fee_proportional_millionths` for this direction; `cltvDelta` is
`cltv_expiry_delta`; `enabled` records that the direction is not disabled. -/
structure ChannelEdge where
  shortChannelId : ShortChannelId
  node1 : NodeId
  node2 : NodeId
  capacitySat : Nat
  feeBaseMsat : Msat
  feeProportionalMillionths : Nat
  cltvDelta : Nat
  enabled : Bool
deriving Repr, DecidableEq, BEq

namespace ChannelEdge

/-- The node at the other end of `e` from `n`, if `n` is an endpoint. -/
def other (e : ChannelEdge) (n : NodeId) : Option NodeId :=
  if e.node1 = n then some e.node2
  else if e.node2 = n then some e.node1
  else none

@[simp] theorem other_node1 (e : ChannelEdge) : e.other e.node1 = some e.node2 := by
  simp [other]

theorem other_node2 (e : ChannelEdge) (h : e.node1 ≠ e.node2) :
    e.other e.node2 = some e.node1 := by
  simp [other, h]

/-- A channel edge connects two distinct endpoints in the BOLT 7 model. -/
def Connects (e : ChannelEdge) : Prop := e.node1 ≠ e.node2

end ChannelEdge

/-! ## The graph -/

/-- A finite public-channel graph.  `nodes` is the announced node set;
`edges` is the announced directional edge set.  The two are kept separately
because BOLT 7 announces nodes independently of channels; no well-formedness
invariant forces every edge endpoint to be in `nodes` (that is an
obligation, not a definition). -/
structure Graph where
  edges : List ChannelEdge
  nodes : List NodeId
deriving Repr, DecidableEq, BEq

namespace Graph

/-- The empty graph. -/
def empty : Graph := ⟨[], []⟩

/-- Add one directed edge.  The endpoints are added to the node list; the
list may contain duplicates, which is harmless because `neighbors` and
`findEdge` only test membership. -/
def addEdge (g : Graph) (e : ChannelEdge) : Graph :=
  ⟨e :: g.edges, e.node1 :: e.node2 :: g.nodes⟩

/-- All nodes adjacent to `n` over an enabled edge.  The result may contain
duplicates when two channels connect the same pair; callers that need a set
must deduplicate. -/
def neighbors (g : Graph) (n : NodeId) : List NodeId :=
  g.edges.filterMap fun e =>
    if e.enabled = true then
      if e.node1 = n then some e.node2
      else if e.node2 = n then some e.node1
      else none
    else none

/-- First enabled edge in list order between two nodes. -/
def findEdgeIn : List ChannelEdge → NodeId → NodeId → Option ChannelEdge
  | [], _, _ => none
  | e :: es, fromNode, toNode =>
    if e.enabled = true ∧ e.node1 = fromNode ∧ e.node2 = toNode then some e
    else findEdgeIn es fromNode toNode

/-- `findEdge g a b` is the first enabled edge of `g` from `a` to `b`, if
any.  Linear scan is the model; production implementations index by
`short_channel_id` and by endpoint. -/
def findEdge (g : Graph) (fromNode toNode : NodeId) : Option ChannelEdge :=
  findEdgeIn g.edges fromNode toNode

/-- Membership test for a `short_channel_id`. -/
def hasEdge (g : Graph) (scid : ShortChannelId) : Bool :=
  g.edges.any fun e => e.shortChannelId == scid

/-- Fuel-bounded depth-first enumeration of simple paths from `current` to
`dst`.  `visited` is the prefix of the current path (including `current`);
nodes in `visited` are never revisited.  At most `fuel` further hops are
explored, so the recursion terminates structurally. -/
def simplePathsAux (g : Graph) (dst : NodeId) :
    Nat → List NodeId → NodeId → List (List NodeId)
  | 0, _, _ => []
  | fuel + 1, visited, current =>
    if current = dst then [[dst]]
    else
      (g.neighbors current).flatMap fun next =>
        if visited.contains next then []
        else (simplePathsAux g dst fuel (next :: visited) next).map
          (fun p => current :: p)

/-- Simple paths from `src` to `dst` with at most `maxHops` edges.  A
zero-length path is not returned: Lightning routes always have at least one
hop (BOLT 4 requires a `short_channel_id` and payload for every hop). -/
def simplePaths (g : Graph) (src dst : NodeId) (maxHops : Nat) :
    List (List NodeId) :=
  if src = dst then [] else simplePathsAux g dst maxHops [src] src

/-! ## Soundness of edge lookup -/

theorem findEdgeIn_mem {edges : List ChannelEdge} {fromNode toNode : NodeId}
    {e : ChannelEdge} (h : findEdgeIn edges fromNode toNode = some e) :
    e ∈ edges := by
  induction edges with
  | nil => simp [findEdgeIn] at h
  | cons x xs ih =>
    simp only [findEdgeIn] at h
    split at h
    · rename_i hc
      cases h
      exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (ih h)

theorem findEdgeIn_enabled {edges : List ChannelEdge} {fromNode toNode : NodeId}
    {e : ChannelEdge} (h : findEdgeIn edges fromNode toNode = some e) :
    e.enabled = true := by
  induction edges with
  | nil => simp [findEdgeIn] at h
  | cons x xs ih =>
    simp only [findEdgeIn] at h
    split at h
    · rename_i hc
      cases h
      exact hc.1
    · exact ih h

theorem findEdgeIn_endpoints {edges : List ChannelEdge} {fromNode toNode : NodeId}
    {e : ChannelEdge} (h : findEdgeIn edges fromNode toNode = some e) :
    e.node1 = fromNode ∧ e.node2 = toNode := by
  induction edges with
  | nil => simp [findEdgeIn] at h
  | cons x xs ih =>
    simp only [findEdgeIn] at h
    split at h
    · rename_i hc
      cases h
      exact ⟨hc.2.1, hc.2.2⟩
    · exact ih h

/-- **Edge lookup soundness.**  A successful `findEdge` returns an enabled
edge that is present in the graph and whose endpoints are the requested
ones.  This is the graph-level fact used by `routeValid`. -/
theorem findEdge_sound {g : Graph} {fromNode toNode : NodeId} {e : ChannelEdge}
    (h : g.findEdge fromNode toNode = some e) :
    e ∈ g.edges ∧ e.enabled = true ∧ e.node1 = fromNode ∧ e.node2 = toNode :=
  ⟨findEdgeIn_mem h, findEdgeIn_enabled h, (findEdgeIn_endpoints h).1,
    (findEdgeIn_endpoints h).2⟩

/-- `findEdge` only returns edges that are in the graph. -/
theorem findEdge_mem {g : Graph} {fromNode toNode : NodeId} {e : ChannelEdge}
    (h : g.findEdge fromNode toNode = some e) : e ∈ g.edges :=
  (findEdge_sound h).1

/-- `findEdge` only returns enabled edges. -/
theorem findEdge_enabled {g : Graph} {fromNode toNode : NodeId} {e : ChannelEdge}
    (h : g.findEdge fromNode toNode = some e) : e.enabled = true :=
  (findEdge_sound h).2.1

/-- `findEdge` only returns edges with the requested endpoints. -/
theorem findEdge_endpoints {g : Graph} {fromNode toNode : NodeId} {e : ChannelEdge}
    (h : g.findEdge fromNode toNode = some e) :
    e.node1 = fromNode ∧ e.node2 = toNode :=
  ⟨(findEdge_sound h).2.2.1, (findEdge_sound h).2.2.2⟩

/-- Adding an enabled edge makes it immediately findable in that direction.
This is a functional-correctness check on the linear scan. -/
theorem findEdge_addEdge_self (g : Graph) (e : ChannelEdge)
    (hen : e.enabled = true) :
    (g.addEdge e).findEdge e.node1 e.node2 = some e := by
  unfold addEdge findEdge findEdgeIn
  rw [ite_eq_left (show e.enabled = true ∧ e.node1 = e.node1 ∧ e.node2 = e.node2
    from ⟨hen, rfl, rfl⟩)]

/-! ## Structural properties of enumerated paths -/

theorem simplePathsAux_head {g : Graph} {dst : NodeId} {fuel : Nat}
    {visited : List NodeId} {current : NodeId} {p : List NodeId}
    (h : p ∈ simplePathsAux g dst fuel visited current) :
    p.head? = some current := by
  induction fuel generalizing visited current p with
  | zero => simp [simplePathsAux] at h
  | succ fuel ih =>
    simp only [simplePathsAux] at h
    split at h
    · rename_i hcur
      simp only [List.mem_singleton] at h
      subst h
      simp [hcur]
    · rcases List.mem_flatMap.mp h with ⟨next, _hnext, hp⟩
      split at hp
      · simp at hp
      · rcases List.mem_map.mp hp with ⟨q, hq, hpq⟩
        rw [← hpq]
        simp

/-- Every path returned by `simplePaths` is non-empty and starts at `src`. -/
theorem simplePaths_head {g : Graph} {src dst : NodeId} {maxHops : Nat}
    {p : List NodeId} (h : p ∈ simplePaths g src dst maxHops) :
    p.head? = some src := by
  unfold simplePaths at h
  split at h
  · simp at h
  · exact simplePathsAux_head h

/-- Every path returned by `simplePaths` is non-empty.  This is the graph
counterpart of the route non-emptiness law. -/
theorem simplePaths_ne_nil {g : Graph} {src dst : NodeId} {maxHops : Nat}
    {p : List NodeId} (h : p ∈ simplePaths g src dst maxHops) : p ≠ [] := by
  intro hnil
  have hhead := simplePaths_head h
  rw [hnil] at hhead
  simp at hhead

end Graph

end LnLean.Routing
