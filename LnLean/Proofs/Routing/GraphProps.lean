import LnLean.Routing.Graph

/-!
# LnLean.Proofs.Routing.GraphProps

English claim of this module:

* A successful `Graph.findEdge` returns an edge that is present in `g.edges`,
  has the requested endpoints, is enabled, and whose `short_channel_id` is
  recorded by `Graph.hasEdge`.  Edge lookup therefore cannot invent a
  channel that the graph does not contain.
* `Graph.neighbors` is exactly the set of nodes incident to `n` over an
  enabled edge.  On a reverse-closed (undirected) graph, adjacency is
  symmetric.  The raw model is directed, so symmetry is a *conditional*
  theorem, with `Graph.ReverseClosed` defined here.
* A `Graph.WellFormed` graph has no self-loop edge and only positive-capacity
  edges.  The raw `ChannelEdge` type enforces neither property: explicit
  counterexamples are proved below.  The corrected, conditional statements
  are the ones proved.
* Fee and CLTV fields are `Nat`, hence non-negative.  No fee *formula* is
  proved here; applying the proportional fee lives in
  `LnLean.Routing.Route`.
* Every path returned by `Graph.simplePaths` is non-empty and `List.Nodup`
  (no repeated node).  It is "simple" in exactly that sense; completeness
  of the enumerator and shortest-path optimality are not claimed.
* `Graph` is finite by representation: it is a pair of `List`s.  `edgeCount`
  and `nodeCount` are their lengths, and `addEdge` adds one edge and two
  node entries.
* `findEdge` is deterministic: for a fixed graph and endpoint pair the
  optional result is unique.
* `Graph.Walk` is the adjacency walk relation (an enabled edge in either
  orientation).  `simplePaths_walk` proves that every path returned by
  `simplePaths` is a walk, closing obligation `LN-GRAPH-001`.

BOLT sections:

* BOLT 7, "Definition of `short_channel_id`" (`refs/bolts/07-routing-gossip.md:37`):
  the channel identifier is the unique description of the funding output.
* BOLT 7, "The `channel_announcement` Message"
  (`refs/bolts/07-routing-gossip.md:189`): two distinct `node_id`s operate the
  channel and the capacity is the funding output value.
* BOLT 7, "The `channel_update` Message"
  (`refs/bolts/07-routing-gossip.md:520`): per-direction `fee_base_msat`,
  `fee_proportional_millionths`, `cltv_expiry_delta`, and `disable`.
* BOLT 7, "Graph": public nodes and channels form a finite graph.
* BOLT 4, "Routing": a route is a non-empty sequence of channels.

`rust-lightning` anchors at pinned commit
`fe4900930c6bd5786ec4203274d7cf312776a5a6` (from `refs/PINNED.md`):

* `lightning/src/routing/gossip.rs:1012` — `pub struct ChannelInfo`
  (`node_one`, `node_two`, `capacity_sats`, `one_to_two`, `two_to_one`).
* `lightning/src/routing/gossip.rs:906` — `pub struct ChannelUpdateInfo`
  (`fees`, `cltv_expiry_delta`, `enabled`).
* `lightning/src/routing/gossip.rs:187` — `pub struct NetworkGraph`
  (`channels` keyed by `short_channel_id`, `nodes` keyed by node id).
* `lightning/src/routing/gossip.rs:2697` — `NetworkGraph::channel`, the
  short-channel-id lookup.
* `lightning/src/routing/gossip.rs:2443` — `NetworkGraph::update_channel`,
  the per-direction update entry point.

What is **not** modelled:

* BOLT 7 wire serialization, chain-hash filtering, signature/UTXO admission,
  six-confirmation checks, and rate limits.  Those are abstract predicates in
  `LnLean.Routing.Gossip`; this module only reasons about an already built
  `Graph`.
* Node announcements.  `Graph.nodes` is a list without announcement data.
* Rejection of self-loops or zero-capacity channels at admission time, and
  the BOLT 7 lexicographic ordering of `node_id_1`/`node_id_2`.  The model
  permits self-loops and zero capacity; this file proves that it does and
  states the well-formedness predicate under which the routing laws hold.
* Deriving `capacitySat` from the on-chain funding output.  It is a stored
  `Nat` field here, not a checked UTXO value.
* Liquidity, HTLC min/max, and capacity-vs-amount checks.  `findEdge` returns
  the first enabled direction regardless of capacity.
* Fee computation, Dijkstra/A* shortest paths, route completeness, diameter,
  and connectivity.  `simplePaths` is a fuel-bounded enumerator.
* MPP, route hints, private channels, and blinded routes.
-/

namespace LnLean.Routing

set_option autoImplicit false

/-! ## Reverse-closed (undirected) graphs

The wave-A model stores *directed* edges.  A public channel normally appears
as two directions, one per `channel_update`; the predicate below states that
the reverse direction of every enabled edge is also present and enabled.
This is the model of the "undirected" graph used for adjacency symmetry. -/

/-- `g.ReverseClosed` holds when every enabled edge in `g` has an enabled
reverse edge in `g`.  It says nothing about disabled directions and nothing
about self-loops. -/
def Graph.ReverseClosed (g : Graph) : Prop :=
  ∀ e ∈ g.edges, e.enabled = true →
    ∃ e' ∈ g.edges, e'.enabled = true ∧ e'.node1 = e.node2 ∧ e'.node2 = e.node1

/-- The graph-level well-formedness invariant assumed by the routing laws:
every stored edge has two distinct endpoints and positive capacity.

The raw `ChannelEdge` structure does not enforce either conjunct; see
`selfLoopEdge_not_connects` and `findEdge_zeroCapacity` below. -/
def Graph.WellFormed (g : Graph) : Prop :=
  (∀ e ∈ g.edges, e.node1 ≠ e.node2) ∧ (∀ e ∈ g.edges, 0 < e.capacitySat)

/-! ## Adjacency -/

/-- Membership in `neighbors` characterised by the underlying edge.  This is
the exact semantics of the `filterMap` in `Graph.neighbors`, including the
self-loop corner case of the raw model. -/
theorem mem_neighbors_iff {g : Graph} {n m : NodeId} :
    m ∈ g.neighbors n ↔
      ∃ e ∈ g.edges, e.enabled = true ∧
        ((e.node1 = n ∧ e.node2 = m) ∨ (e.node2 = n ∧ e.node1 = m)) := by
  unfold Graph.neighbors
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨e, he, hf⟩
    refine ⟨e, he, ?_, ?_⟩
    · split at hf
      · rename_i hen
        split at hf
        · exact hen
        · split at hf
          · exact hen
          · simp at hf
      · simp at hf
    · split at hf
      · rename_i hen
        split at hf
        · rename_i h1
          left
          exact ⟨h1, by cases hf; rfl⟩
        · split at hf
          · rename_i h2
            right
            exact ⟨h2, by cases hf; rfl⟩
          · simp at hf
      · simp at hf
  · rintro ⟨e, he, hen, hend⟩
    refine ⟨e, he, ?_⟩
    rw [ite_eq_left hen]
    rcases hend with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [ite_eq_left h1]
      simp [h2]
    · by_cases h3 : e.node1 = n
      · rw [ite_eq_left h3]
        have hm : e.node2 = m := h1.trans (h3.symm.trans h2)
        simp [hm]
      · rw [ite_eq_right h3]
        rw [ite_eq_left h1]
        simp [h2]

/-- An enabled edge `e` makes its destination a neighbour of its source. -/
theorem mem_neighbors_of_edge {g : Graph} {e : ChannelEdge}
    (he : e ∈ g.edges) (hen : e.enabled = true) :
    e.node2 ∈ g.neighbors e.node1 := by
  rw [mem_neighbors_iff]
  exact ⟨e, he, hen, Or.inl ⟨rfl, rfl⟩⟩

/-- The same edge also makes its source a neighbour of its destination when
the edge is read from the other end.  This is the directed half of the
symmetry statement. -/
theorem mem_neighbors_of_edge_right {g : Graph} {e : ChannelEdge}
    (he : e ∈ g.edges) (hen : e.enabled = true) :
    e.node1 ∈ g.neighbors e.node2 := by
  rw [mem_neighbors_iff]
  exact ⟨e, he, hen, Or.inr ⟨rfl, rfl⟩⟩

/-- **Adjacency symmetry.**  On a reverse-closed graph, `a` is adjacent to
`b` iff `b` is adjacent to `a`.  The forward direction is proved; the
reverse direction is the same statement with `a` and `b` exchanged. -/
theorem neighbors_symm {g : Graph} (hrev : g.ReverseClosed) {a b : NodeId}
    (h : b ∈ g.neighbors a) : a ∈ g.neighbors b := by
  rw [mem_neighbors_iff] at h ⊢
  obtain ⟨e, he, hen, hend⟩ := h
  obtain ⟨e', he', hen', h1', h2'⟩ := hrev e he hen
  refine ⟨e', he', hen', ?_⟩
  rcases hend with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    exact ⟨h1'.trans h2, h2'.trans h1⟩
  · right
    exact ⟨h2'.trans h2, h1'.trans h1⟩

/-- Symmetry as an iff: on a reverse-closed graph the neighbour relation is
symmetric in both directions. -/
theorem neighbors_comm {g : Graph} (hrev : g.ReverseClosed) (a b : NodeId) :
    b ∈ g.neighbors a ↔ a ∈ g.neighbors b :=
  ⟨neighbors_symm hrev, neighbors_symm hrev⟩

/-! ## Edge lookup: channel presence, well-formedness, determinism -/

/-- A `short_channel_id` compares equal to itself.  The derived `BEq` for
`ShortChannelId` is not definitionally the identity, so this small lemma is
needed before `Graph.hasEdge` can be related to list membership. -/
theorem scid_beq_self (s : ShortChannelId) : (s == s) = true := by
  cases s with
  | mk block txIndex outputIndex =>
    show LnLean.instBEqShortChannelId.beq
        ⟨block, txIndex, outputIndex⟩
        ⟨block, txIndex, outputIndex⟩ = true
    simp [LnLean.instBEqShortChannelId.beq]

/-- List-level form of `hasEdge` soundness. -/
theorem any_scid_of_mem {edges : List ChannelEdge} {e : ChannelEdge}
    (h : e ∈ edges) :
    (edges.any fun x => x.shortChannelId == e.shortChannelId) = true := by
  induction edges with
  | nil => cases h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with rfl | h
    · simp [scid_beq_self]
    · simp [ih h]

/-- If an edge is in the list, `hasEdge` finds its `short_channel_id`. -/
theorem hasEdge_of_mem {g : Graph} {e : ChannelEdge} (h : e ∈ g.edges) :
    g.hasEdge e.shortChannelId = true := by
  simpa [Graph.hasEdge] using any_scid_of_mem h

/-- **`findEdge` only returns channels present under a `short_channel_id`.**
A successful lookup implies `g.hasEdge e.shortChannelId = true`. -/
theorem findEdge_hasEdge {g : Graph} {fromNode toNode : NodeId} {e : ChannelEdge}
    (h : g.findEdge fromNode toNode = some e) :
    g.hasEdge e.shortChannelId = true :=
  hasEdge_of_mem (Graph.findEdge_mem h)

/-- The same fact stated as membership in the list of announced ids. -/
theorem findEdge_scid_mem {g : Graph} {fromNode toNode : NodeId} {e : ChannelEdge}
    (h : g.findEdge fromNode toNode = some e) :
    e.shortChannelId ∈ g.edges.map (fun x => x.shortChannelId) :=
  List.mem_map.mpr ⟨e, Graph.findEdge_mem h, rfl⟩

/-- **No self-loop on a well-formed graph.**  Every edge returned by
`findEdge` has distinct endpoints.  This is conditional on
`Graph.WellFormed`; the raw model does not enforce it (next theorem). -/
theorem findEdge_noSelfLoop {g : Graph} (hwf : g.WellFormed)
    {fromNode toNode : NodeId} {e : ChannelEdge}
    (h : g.findEdge fromNode toNode = some e) : e.node1 ≠ e.node2 :=
  hwf.1 e (Graph.findEdge_mem h)

/-- **Positive capacity on a well-formed graph.**  Every edge returned by
`findEdge` has positive satoshi capacity.  Conditional on
`Graph.WellFormed`; the raw model does not enforce it (see
`findEdge_zeroCapacity`). -/
theorem findEdge_capacity_pos {g : Graph} (hwf : g.WellFormed)
    {fromNode toNode : NodeId} {e : ChannelEdge}
    (h : g.findEdge fromNode toNode = some e) : 0 < e.capacitySat :=
  hwf.2 e (Graph.findEdge_mem h)

/-- Positive satoshi capacity implies positive millisatoshi capacity. -/
theorem capacity_msat_pos {e : ChannelEdge} (h : 0 < e.capacitySat) :
    0 < e.capacitySat * Msat.MSAT_PER_SAT :=
  Nat.mul_pos h (by decide : 0 < Msat.MSAT_PER_SAT)

/-- Fee and CLTV fields are natural numbers, therefore non-negative.  This is
the complete content of "fees and CLTV are non-negative" in this model; no
fee formula is involved. -/
theorem fee_params_nonneg (e : ChannelEdge) :
    0 ≤ e.feeBaseMsat.val ∧ 0 ≤ e.feeProportionalMillionths ∧ 0 ≤ e.cltvDelta :=
  ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩

/-- A concrete self-loop edge.  It is enabled and is a perfectly valid
`ChannelEdge` value, which is why `Graph.WellFormed` must be assumed. -/
def selfLoopEdge : ChannelEdge where
  shortChannelId := ⟨0, 0, 0⟩
  node1 := ⟨0⟩
  node2 := ⟨0⟩
  capacitySat := 0
  feeBaseMsat := Msat.zero
  feeProportionalMillionths := 0
  cltvDelta := 0
  enabled := true

/-- The model's `ChannelEdge` does not require `Connects`. -/
theorem selfLoopEdge_not_connects : ¬ selfLoopEdge.Connects := by
  simp [ChannelEdge.Connects, selfLoopEdge]

/-- **Gap: the raw graph admits self-loops.**  A one-edge graph containing
`selfLoopEdge` is a valid `Graph`, so well-formedness is a real hypothesis
and not a consequence of the representation. -/
theorem model_allows_self_loop :
    ∃ (g : Graph) (e : ChannelEdge), e ∈ g.edges ∧ ¬ e.Connects :=
  ⟨⟨[selfLoopEdge], []⟩, selfLoopEdge, List.mem_singleton_self _, selfLoopEdge_not_connects⟩

/-- A concrete enabled edge with zero capacity. -/
def zeroCapacityEdge : ChannelEdge where
  shortChannelId := ⟨1, 0, 0⟩
  node1 := ⟨0⟩
  node2 := ⟨1⟩
  capacitySat := 0
  feeBaseMsat := Msat.zero
  feeProportionalMillionths := 0
  cltvDelta := 0
  enabled := true

/-- **Gap: `findEdge` does not check capacity.**  A zero-capacity edge is
returned successfully.  Capacity checks belong to route construction, not to
graph lookup. -/
theorem findEdge_zeroCapacity :
    ∃ (g : Graph) (fromNode toNode : NodeId) (e : ChannelEdge),
      g.findEdge fromNode toNode = some e ∧ e.capacitySat = 0 := by
  refine ⟨⟨[zeroCapacityEdge], []⟩, ⟨0⟩, ⟨1⟩, zeroCapacityEdge, ?_, rfl⟩
  simp [Graph.findEdge, Graph.findEdgeIn, zeroCapacityEdge]

/-- **Edge lookup is deterministic.**  Two successful scans of the same list
return the same edge. -/
theorem findEdgeIn_deterministic {edges : List ChannelEdge}
    {fromNode toNode : NodeId} {e₁ e₂ : ChannelEdge}
    (h₁ : Graph.findEdgeIn edges fromNode toNode = some e₁)
    (h₂ : Graph.findEdgeIn edges fromNode toNode = some e₂) : e₁ = e₂ := by
  rw [h₁] at h₂
  exact Option.some.inj h₂

/-- Graph-level form of determinism. -/
theorem findEdge_deterministic {g : Graph} {fromNode toNode : NodeId}
    {e₁ e₂ : ChannelEdge}
    (h₁ : g.findEdge fromNode toNode = some e₁)
    (h₂ : g.findEdge fromNode toNode = some e₂) : e₁ = e₂ :=
  findEdgeIn_deterministic h₁ h₂

/-! ## Finiteness by representation -/

/-- Number of stored directed edges. -/
def Graph.edgeCount (g : Graph) : Nat := g.edges.length

/-- Number of stored node entries (duplicates are not removed by `addEdge`). -/
def Graph.nodeCount (g : Graph) : Nat := g.nodes.length

theorem edgeCount_empty : Graph.empty.edgeCount = 0 := rfl

theorem nodeCount_empty : Graph.empty.nodeCount = 0 := rfl

/-- Adding an edge adds exactly one directed edge. -/
theorem edgeCount_addEdge (g : Graph) (e : ChannelEdge) :
    (g.addEdge e).edgeCount = g.edgeCount + 1 := rfl

/-- Adding an edge adds exactly two node entries (the two endpoints). -/
theorem nodeCount_addEdge (g : Graph) (e : ChannelEdge) :
    (g.addEdge e).nodeCount = g.nodeCount + 2 := by
  simp [Graph.nodeCount, Graph.addEdge]

/-- A graph with a findable edge has positive edge count.  This is the
finiteness witness used by callers: lookup cannot succeed on an empty edge
list. -/
theorem findEdge_edgeCount_pos {g : Graph} {fromNode toNode : NodeId}
    {e : ChannelEdge} (h : g.findEdge fromNode toNode = some e) :
    0 < g.edgeCount := by
  simpa [Graph.edgeCount] using List.length_pos_of_mem (Graph.findEdge_mem h)

/-! ## Simple paths: no repeated node, non-empty

`simplePathsAux` threads `visited` through the DFS.  The invariant proved
below is stronger than `Nodup` of the result:

* the head of the result is the current node;
* the tail never touches `visited`;
* `visited` itself is `Nodup` and contains the current node.

The last two conjuncts are what exclude revisiting an earlier node when the
recursive call prepends `current` to the child path.
-/

private theorem simplePathsAux_nodup_aux {g : Graph} {dst : NodeId} :
    ∀ (fuel : Nat) (visited : List NodeId) (current : NodeId) (p : List NodeId),
      visited.Nodup → current ∈ visited →
      p ∈ Graph.simplePathsAux g dst fuel visited current →
      p.Nodup ∧ p.head? = some current ∧ (∀ x ∈ p.tail, x ∉ visited) := by
  intro fuel
  induction fuel with
  | zero =>
    intro visited current p _ _ h
    simp [Graph.simplePathsAux] at h
  | succ fuel ih =>
    intro visited current p hnod hcur h
    simp only [Graph.simplePathsAux] at h
    split at h
    · rename_i hcurdst
      simp only [List.mem_singleton] at h
      subst h
      refine ⟨?_, ?_, ?_⟩
      · simp
      · simp [hcurdst]
      · intro x hx
        simp at hx
    · rcases List.mem_flatMap.mp h with ⟨next, _hnext, hp⟩
      by_cases hcontains : visited.contains next = true
      · rw [ite_eq_left hcontains] at hp
        simp at hp
      · rw [ite_eq_right hcontains] at hp
        rcases List.mem_map.mp hp with ⟨q, hq, rfl⟩
        have hnext_not : next ∉ visited := by
          intro hmem
          exact hcontains (List.contains_iff_mem.mpr hmem)
        have hnod' : (next :: visited).Nodup :=
          List.nodup_cons.mpr ⟨hnext_not, hnod⟩
        have hcur' : next ∈ next :: visited := List.mem_cons_self ..
        obtain ⟨hqnod, hqhead, hqavoid⟩ :=
          ih (next :: visited) next q hnod' hcur' hq
        cases q with
        | nil => simp at hqhead
        | cons next' q' =>
          have hnext'_eq : next' = next := by simpa using hqhead
          subst next'
          have hcur_ne_next : current ≠ next := by
            intro heq
            exact hnext_not (heq ▸ hcur)
          have hcur_not_q' : current ∉ q' := by
            intro hmem
            exact hqavoid current hmem (List.mem_cons_of_mem _ hcur)
          refine ⟨?_, ?_, ?_⟩
          · exact List.nodup_cons.mpr ⟨by
              intro hmem
              rcases List.mem_cons.mp hmem with heq | hmem'
              · exact hcur_ne_next heq
              · exact hcur_not_q' hmem', hqnod⟩
          · simp
          · intro x hx
            have hxq : x ∈ next :: q' := by simpa using hx
            rcases List.mem_cons.mp hxq with rfl | hxq'
            · exact hnext_not
            · intro hmem
              exact hqavoid x hxq' (List.mem_cons_of_mem _ hmem)

/-- **Simple paths have no repeated node.**  Every path enumerated by
`Graph.simplePaths` is `List.Nodup`. -/
theorem simplePaths_nodup {g : Graph} {src dst : NodeId} {maxHops : Nat}
    {p : List NodeId} (h : p ∈ Graph.simplePaths g src dst maxHops) :
    p.Nodup := by
  unfold Graph.simplePaths at h
  split at h
  · simp at h
  · exact (simplePathsAux_nodup_aux maxHops [src] src p (by simp)
      (List.mem_singleton_self src) h).1

/-- **Simple paths are non-empty.**  This restates the wave-A
`Graph.simplePaths_ne_nil` for the combined simple-path law. -/
theorem simplePaths_nonempty {g : Graph} {src dst : NodeId} {maxHops : Nat}
    {p : List NodeId} (h : p ∈ Graph.simplePaths g src dst maxHops) :
    p ≠ [] :=
  Graph.simplePaths_ne_nil h

/-- Combined form: a returned path is a non-empty, duplicate-free node list. -/
theorem simplePaths_simple {g : Graph} {src dst : NodeId} {maxHops : Nat}
    {p : List NodeId} (h : p ∈ Graph.simplePaths g src dst maxHops) :
    p.Nodup ∧ p ≠ [] :=
  ⟨simplePaths_nodup h, simplePaths_nonempty h⟩

/-! ## Walks: the remaining path obligation -/

/-- `g.Adjacent a b` holds when some enabled edge of `g` has endpoints `a`
and `b`, in either orientation.  This is the adjacency relation induced by
`Graph.neighbors`; it is deliberately not the forward directed edge relation,
because `neighbors` also returns the source of a stored direction. -/
def Graph.Adjacent (g : Graph) (a b : NodeId) : Prop :=
  ∃ e ∈ g.edges, e.enabled = true ∧
    ((e.node1 = a ∧ e.node2 = b) ∨ (e.node2 = a ∧ e.node1 = b))

/-- `neighbors` soundness restated as adjacency. -/
theorem adjacent_of_mem_neighbors {g : Graph} {a b : NodeId}
    (h : b ∈ g.neighbors a) : g.Adjacent a b :=
  mem_neighbors_iff.mp h

/-- `g.Walk p` holds when every consecutive pair in `p` is adjacent in `g`
(over an enabled edge, in either orientation).  This is the connectivity
property satisfied by `simplePaths`; see `simplePaths_walk`. -/
def Graph.Walk (g : Graph) : List NodeId → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => Graph.Adjacent g a b ∧ Graph.Walk g (b :: rest)

/-- **Enumerator soundness for walks.**  Every path produced by
`simplePathsAux` from `current` is a `Graph.Walk`.  The proof is an induction on
the fuel.  In the recursive branch, `List.mem_flatMap` exposes the chosen
neighbour `next ∈ g.neighbors current`, which `adjacent_of_mem_neighbors`
turns into the first adjacency step; `simplePathsAux_head` identifies the head
of the child path with `next`, so the inductive hypothesis supplies the rest. -/
private theorem simplePathsAux_walk {g : Graph} {dst : NodeId} :
    ∀ (fuel : Nat) (visited : List NodeId) (current : NodeId) (p : List NodeId),
      p ∈ Graph.simplePathsAux g dst fuel visited current → g.Walk p := by
  intro fuel
  induction fuel with
  | zero =>
    intro visited current p h
    simp [Graph.simplePathsAux] at h
  | succ fuel ih =>
    intro visited current p h
    simp only [Graph.simplePathsAux] at h
    split at h
    · rename_i hcurdst
      simp only [List.mem_singleton] at h
      subst h
      simp [Graph.Walk]
    · rcases List.mem_flatMap.mp h with ⟨next, hnext, hp⟩
      by_cases hcontains : visited.contains next = true
      · rw [ite_eq_left hcontains] at hp
        simp at hp
      · rw [ite_eq_right hcontains] at hp
        rcases List.mem_map.mp hp with ⟨q, hq, rfl⟩
        have hqwalk : g.Walk q := ih (next :: visited) next q hq
        have hqhead : q.head? = some next := Graph.simplePathsAux_head hq
        have hadj : g.Adjacent current next := adjacent_of_mem_neighbors hnext
        cases q with
        | nil => simp [Graph.Walk]
        | cons b rest =>
          have hb : b = next := by simpa using hqhead
          subst hb
          exact ⟨hadj, hqwalk⟩

/-- **`simplePaths` returns walks.**  Every path returned by
`Graph.simplePaths g src dst maxHops` is a `Walk` of enabled edges (in either
orientation).  This closes obligation `LN-GRAPH-001`. -/
theorem simplePaths_walk {g : Graph} {src dst : NodeId} {maxHops : Nat}
    {p : List NodeId} (h : p ∈ Graph.simplePaths g src dst maxHops) :
    g.Walk p := by
  unfold Graph.simplePaths at h
  split at h
  · simp at h
  · exact simplePathsAux_walk maxHops [src] src p h

end LnLean.Routing
