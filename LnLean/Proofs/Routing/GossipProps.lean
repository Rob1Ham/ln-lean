import LnLean.Routing.Gossip
import LnLean.Routing.Graph

/-!
# LnLean.Proofs.Routing.GossipProps

English claim of this module:

* `applyGossip` is a deterministic function of `(GossipState, GossipMessage)`;
  delivering the same `channel_update` twice is idempotent, and an update
  whose timestamp is not strictly greater than the stored clock does not
  replace anything.
* Once a strictly newer update has been accepted, every update whose
  timestamp is not greater than it is a no-op (`gossip_applyUpdate_absorb`):
  an older timestamp never overwrites a newer one.
* A `channel_update` with the BOLT 7 `disable` bit (bit 1 of
  `channel_flags`) set still materialises an edge in the graph projection,
  but that edge is not selectable: `Graph.findEdge` skips it, and returns
  `none` when every candidate edge is disabled.  A strictly newer update
  with the disable bit clear re-enables the edge.
* A `node_announcement` can update a node record's alias and timestamp but
  cannot change its `nodeId`; an announcement carrying a different node key
  is rejected by the model's byte-level equality check.
* A `channel_announcement` that passes the model's four-signature predicate
  binds its `short_channel_id` to exactly the two announced node keys and
  the announced capacity (`bindChannel_binds`).  Re-announcements that agree
  on the two keys preserve a store-level uniqueness predicate; a conflicting
  re-announcement is *not* rejected by the append-only wave-A store, which
  is recorded as an open obligation below.
* Signature checks are *conditional predicates*, never assumptions: every
  state change produced by `applyGossipChecked` entails the corresponding
  `signatureValid` proposition.  No theorem claims unforgeability (that is
  assumption C3/C4/C8 in `docs/ASSUMPTIONS.md`).

BOLT sections:

* BOLT 7, "The `channel_announcement` Message": `short_channel_id`,
  `node_id_1`, `node_id_2`, four signatures; the receiving node MUST verify
  the signatures before processing (`refs/bolts/07-routing-gossip.md:155`,
  `:178`, `:189`, `:199`, `:213`).
* BOLT 7, "The `channel_update` Message": `timestamp`, `channel_flags`
  bit 1 = `disable`, signature rules, the equal/lower-timestamp rules
  (`refs/bolts/07-routing-gossip.md:444`, `:460`, `:468`, `:517`, `:544`,
  `:551`, `:558`).
* BOLT 7, "The `node_announcement` Message": `node_id` and the
  "NOT previously known ... OR timestamp NOT greater" ignore rule
  (`refs/bolts/07-routing-gossip.md:382`).

`rust-lightning` anchors at pinned commit
`fe4900930c6bd5786ec4203274d7cf312776a5a6` (`refs/PINNED.md`); these line
numbers were checked against `refs/rust-lightning` on this box:

* `lightning/src/routing/gossip.rs:906` — `pub struct ChannelUpdateInfo`
  (`last_update`, `enabled`, fees, CLTV delta).
* `lightning/src/routing/gossip.rs:1012` — `pub struct ChannelInfo`
  (`node_one`, `node_two`, `capacity_sats`, `one_to_two`, `two_to_one`).
* `lightning/src/routing/gossip.rs:1534` — `pub struct NodeInfo`.
* `lightning/src/routing/gossip.rs:1881` — `update_node_from_announcement`
  (finds the node by `msg.contents.node_id`, then checks the timestamp).
* `lightning/src/routing/gossip.rs:1910` — `update_node_from_announcement_intern`
  (replaces `announcement_info`, keeps the node entry/key).
* `lightning/src/routing/gossip.rs:1973` — `update_channel_from_announcement`.
* `lightning/src/routing/gossip.rs:2443` — `NetworkGraph::update_channel`.
* `lightning/src/routing/gossip.rs:2474` — `update_channel_internal`;
  `:2478` computes `chan_enabled` from `channel_flags & (1 << 1)`, and
  `:2533`/`:2538` reject `last_update > timestamp` and
  `last_update == timestamp`.
* `lightning/src/routing/gossip.rs:515` — `verify_channel_announcement`
  (all four signatures).

What is explicitly **not** modelled:

* Wire encoding and the exact double-SHA256 signed byte ranges.  Digests are
  opaque `ByteArray`s and verifiers are abstract `SigVerifier`s.
* BOLT 7 chain-hash filtering, UTXO lookup, the six-confirmation rule, and
  the "capacity equals funding output value" check.  `capacitySat` is an
  unconstrained `Nat` in wave A; its positivity is an obligation below.
* Per-`(short_channel_id, direction)` update clocks.  Wave A keeps one
  global clock and this module's `ChannelView` keys only by
  `short_channel_id`; the `direction` bit of `channel_flags` is not decoded.
* The link between a graph `NodeId` and the BOLT 7 `node_id` public key:
  `ChannelAnnellation` carries both (`node1 : NodeId`, `nodeKey1 : PubKey`),
  but nothing in wave A proves that `nodeKey1` is the key controlled by
  `node1`.  Signature attribution is therefore an obligation below.
* Gossip rate limits, `gossip_queries`, peer dissemination, and any
  cryptographic unforgeability claim.
-/

namespace LnLean.Routing.GossipProps

open LnLean.Routing
open Classical

set_option autoImplicit false

/-! ## BOLT 7 `channel_flags` bits -/

/-- BOLT 7 bit 1 of `channel_flags` is the `disable` bit.  Only the two
whole-number bits are modelled; the remaining bits are ignored. -/
def disableFlagSet (channelFlags : Nat) : Bool :=
  (channelFlags / 2) % 2 == 1

/-- `channel_flags = 0`: direction 0, enabled. -/
theorem disableFlagSet_zero : disableFlagSet 0 = false := by decide

/-- `channel_flags = 1`: direction 1, enabled. -/
theorem disableFlagSet_one : disableFlagSet 1 = false := by decide

/-- `channel_flags = 2`: direction 0, disabled. -/
theorem disableFlagSet_two : disableFlagSet 2 = true := by decide

/-- `channel_flags = 3`: direction 1, disabled. -/
theorem disableFlagSet_three : disableFlagSet 3 = true := by decide

/-! ## Graph well-formedness -/

/-- A graph is well formed when every stored edge has two distinct endpoints
and a structurally valid `short_channel_id`.

This predicate is deliberately minimal: BOLT 7's capacity/UTXO checks are
not part of it (see the module docstring). -/
def graphWellFormed (g : Graph) : Prop :=
  ∀ e ∈ g.edges, e.node1 ≠ e.node2 ∧ e.shortChannelId.Valid

/-- The empty graph is well formed. -/
theorem graphWellFormed_empty : graphWellFormed Graph.empty := by
  intro e he
  simp [Graph.empty] at he

/-- Prepending an edge with distinct endpoints and a valid
`short_channel_id` preserves well-formedness. -/
theorem graphWellFormed_addEdge (g : Graph) (e : ChannelEdge)
    (hg : graphWellFormed g) (hne : e.node1 ≠ e.node2)
    (hscid : e.shortChannelId.Valid) :
    graphWellFormed (g.addEdge e) := by
  intro x hx
  simp only [Graph.addEdge, List.mem_cons] at hx
  rcases hx with rfl | hx
  · exact ⟨hne, hscid⟩
  · exact hg x hx

/-! ## Materialised channel views -/

/-- One directed channel as it appears in the routing graph, together with
the timestamp and disable flag of the newest accepted `channel_update`.

Wave A's `ChannelEdge` has no timestamp and no "current update" field, so
the proof layer keeps the clock here.  `node1`/`node2` are graph-level
`NodeId`s: the announcement-to-graph key map is not modelled (see the
docstring). -/
structure ChannelView where
  scid : ShortChannelId
  node1 : NodeId
  node2 : NodeId
  capacitySat : Nat
  feeBaseMsat : Msat
  feeProportionalMillionths : Nat
  cltvDelta : Nat
  /-- Newest accepted `channel_update` timestamp for this channel. -/
  timestamp : Timestamp
  /-- BOLT 7 `channel_flags` bit 1, decoded. -/
  disabled : Bool
deriving Repr, BEq, DecidableEq

namespace ChannelView

/-- The directed edge used for route search. -/
def edge (v : ChannelView) : ChannelEdge :=
  { shortChannelId := v.scid
    node1 := v.node1
    node2 := v.node2
    capacitySat := v.capacitySat
    feeBaseMsat := v.feeBaseMsat
    feeProportionalMillionths := v.feeProportionalMillionths
    cltvDelta := v.cltvDelta
    enabled := !v.disabled }

@[simp] theorem edge_scid (v : ChannelView) :
    v.edge.shortChannelId = v.scid := rfl

@[simp] theorem edge_node1 (v : ChannelView) : v.edge.node1 = v.node1 := rfl

@[simp] theorem edge_node2 (v : ChannelView) : v.edge.node2 = v.node2 := rfl

@[simp] theorem edge_enabled (v : ChannelView) :
    v.edge.enabled = !v.disabled := rfl

/-- Apply one `channel_update` to the view.

The update is accepted only when its `short_channel_id` matches and its
timestamp is strictly greater than the view's clock, which is the BOLT 7
replacement rule at per-channel granularity.  Equal timestamps do not
replace (BOLT 7: "SHOULD ignore this message"). -/
def applyUpdate (v : ChannelView) (u : ChannelUpdate) : ChannelView :=
  if v.scid = u.shortChannelId ∧ v.timestamp < u.timestamp then
    { v with
      feeBaseMsat := u.feeBaseMsat
      feeProportionalMillionths := u.feeProportionalMillionths
      cltvDelta := u.cltvDelta
      timestamp := u.timestamp
      disabled := disableFlagSet u.channelFlags }
  else v

/-- The channel identity is never changed by an update. -/
theorem applyUpdate_scid (v : ChannelView) (u : ChannelUpdate) :
    (v.applyUpdate u).scid = v.scid := by
  unfold applyUpdate
  split <;> rfl

/-- The source endpoint is never changed by an update. -/
theorem applyUpdate_node1 (v : ChannelView) (u : ChannelUpdate) :
    (v.applyUpdate u).node1 = v.node1 := by
  unfold applyUpdate
  split <;> rfl

/-- The destination endpoint is never changed by an update. -/
theorem applyUpdate_node2 (v : ChannelView) (u : ChannelUpdate) :
    (v.applyUpdate u).node2 = v.node2 := by
  unfold applyUpdate
  split <;> rfl

/-- The capacity is never changed by an update. -/
theorem applyUpdate_capacitySat (v : ChannelView) (u : ChannelUpdate) :
    (v.applyUpdate u).capacitySat = v.capacitySat := by
  unfold applyUpdate
  split <;> rfl

/-- An update that fails the match/timestamp guard leaves the view alone. -/
theorem applyUpdate_self_of_not (v : ChannelView) (u : ChannelUpdate)
    (h : ¬(v.scid = u.shortChannelId ∧ v.timestamp < u.timestamp)) :
    v.applyUpdate u = v := by
  unfold applyUpdate
  rw [if_neg h]

/-- A non-newer update (also for a different channel) is a no-op. -/
theorem applyUpdate_stale (v : ChannelView) (u : ChannelUpdate)
    (h : u.timestamp ≤ v.timestamp) : v.applyUpdate u = v := by
  apply applyUpdate_self_of_not
  rintro ⟨_, hlt⟩
  exact Nat.not_lt_of_le h hlt

/-- The view clock never decreases. -/
theorem applyUpdate_timestamp_ge (v : ChannelView) (u : ChannelUpdate) :
    v.timestamp ≤ (v.applyUpdate u).timestamp := by
  unfold applyUpdate
  split
  · rename_i h
    exact Nat.le_of_lt h.2
  · exact Nat.le_refl v.timestamp

/-- A matched, strictly newer update installs its timestamp. -/
theorem applyUpdate_newer_timestamp (v : ChannelView) (u : ChannelUpdate)
    (hscid : v.scid = u.shortChannelId) (h : v.timestamp < u.timestamp) :
    (v.applyUpdate u).timestamp = u.timestamp := by
  unfold applyUpdate
  rw [if_pos ⟨hscid, h⟩]

/-- A matched, strictly newer update installs its disable flag. -/
theorem applyUpdate_newer_disabled (v : ChannelView) (u : ChannelUpdate)
    (hscid : v.scid = u.shortChannelId) (h : v.timestamp < u.timestamp) :
    (v.applyUpdate u).disabled = disableFlagSet u.channelFlags := by
  unfold applyUpdate
  rw [if_pos ⟨hscid, h⟩]

/-- A newer update whose disable bit is set disables the edge. -/
theorem applyUpdate_newer_disables (v : ChannelView) (u : ChannelUpdate)
    (hscid : v.scid = u.shortChannelId) (h : v.timestamp < u.timestamp)
    (hset : disableFlagSet u.channelFlags = true) :
    (v.applyUpdate u).edge.enabled = false := by
  rw [edge_enabled, applyUpdate_newer_disabled v u hscid h, hset]
  rfl

/-- A newer update whose disable bit is clear re-enables the edge. -/
theorem applyUpdate_newer_enables (v : ChannelView) (u : ChannelUpdate)
    (hscid : v.scid = u.shortChannelId) (h : v.timestamp < u.timestamp)
    (hclear : disableFlagSet u.channelFlags = false) :
    (v.applyUpdate u).edge.enabled = true := by
  rw [edge_enabled, applyUpdate_newer_disabled v u hscid h, hclear]
  rfl

/-- Applying the same update twice is idempotent: the second copy is stale. -/
theorem applyUpdate_idempotent (v : ChannelView) (u : ChannelUpdate) :
    (v.applyUpdate u).applyUpdate u = v.applyUpdate u := by
  by_cases h : v.scid = u.shortChannelId ∧ v.timestamp < u.timestamp
  · have hle : u.timestamp ≤ (v.applyUpdate u).timestamp :=
      Nat.le_of_eq (applyUpdate_newer_timestamp v u h.1 h.2).symm
    exact applyUpdate_stale (v.applyUpdate u) u hle
  · rw [applyUpdate_self_of_not v u h]
    exact applyUpdate_self_of_not v u h

end ChannelView

/-! ## The graph projection of a view list -/

/-- Materialise a list of channel views as a `Graph`.  Disabled views stay in
the edge list; selectability is decided by `Graph.findEdge`. -/
def viewGraph (vs : List ChannelView) : Graph :=
  { edges := vs.map ChannelView.edge
    nodes := vs.flatMap fun v => [v.node1, v.node2] }

/-- If every view is well formed, so is its graph projection. -/
theorem viewGraph_wellFormed {vs : List ChannelView}
    (h : ∀ v ∈ vs, v.node1 ≠ v.node2 ∧ v.scid.Valid) :
    graphWellFormed (viewGraph vs) := by
  intro e he
  have he' : e ∈ vs.map ChannelView.edge := he
  rcases List.mem_map.mp he' with ⟨v, hv, rfl⟩
  exact h v hv

/-- Inverting the projection: a well-formed view graph has well-formed
views. -/
theorem viewGraph_wellFormed_inv {vs : List ChannelView}
    (h : graphWellFormed (viewGraph vs)) :
    ∀ v ∈ vs, v.node1 ≠ v.node2 ∧ v.scid.Valid := by
  intro v hv
  have hmem : v.edge ∈ (viewGraph vs).edges := by
    show v.edge ∈ vs.map ChannelView.edge
    exact List.mem_map.mpr ⟨v, hv, rfl⟩
  exact h v.edge hmem

/-- Every view's edge stays materialised after updating any view. -/
theorem viewGraph_mem_after_update (vs : List ChannelView) (v : ChannelView)
    (u : ChannelUpdate) (hv : v ∈ vs) :
    (v.applyUpdate u).edge ∈ (viewGraph (vs.map fun x => x.applyUpdate u)).edges := by
  show (v.applyUpdate u).edge ∈
    (vs.map fun x => x.applyUpdate u).map ChannelView.edge
  exact List.mem_map.mpr
    ⟨v.applyUpdate u, List.mem_map.mpr ⟨v, hv, rfl⟩, rfl⟩

/-! ## Selectability of disabled edges -/

/-- A linear scan over a list in which every edge is disabled finds nothing. -/
theorem findEdgeIn_none_of_all_disabled (edges : List ChannelEdge)
    (fromNode toNode : NodeId)
    (h : ∀ e ∈ edges, e.enabled = false) :
    Graph.findEdgeIn edges fromNode toNode = none := by
  induction edges with
  | nil => rfl
  | cons e es ih =>
    simp only [Graph.findEdgeIn]
    have he : e.enabled = false := h e (by simp)
    rw [if_neg]
    · exact ih (fun x hx => h x (by simp [hx]))
    · rintro ⟨hen, _, _⟩
      rw [he] at hen
      cases hen

/-- `findEdge` returns nothing when every edge is disabled. -/
theorem findEdge_none_of_all_disabled (g : Graph) (fromNode toNode : NodeId)
    (h : ∀ e ∈ g.edges, e.enabled = false) :
    g.findEdge fromNode toNode = none :=
  findEdgeIn_none_of_all_disabled g.edges fromNode toNode h

/-- **Disabled edges remain stored but are not selectable.**  Prepending a
disabled edge keeps it in the edge list, while the lookup skips it (and,
given the hypothesis, every other candidate). -/
theorem disabled_edge_retained_not_selectable (g : Graph) (e : ChannelEdge)
    (hg : ∀ x ∈ g.edges, x.enabled = false) (he : e.enabled = false) :
    e ∈ (g.addEdge e).edges ∧
      (g.addEdge e).findEdge e.node1 e.node2 = none := by
  constructor
  · simp [Graph.addEdge]
  · apply findEdge_none_of_all_disabled
    intro x hx
    simp only [Graph.addEdge, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact he
    · exact hg x hx

/-- The singleton-graph form of the disabled-edge law: the edge is in the
materialised graph and is not returned by `findEdge`. -/
theorem viewGraph_singleton_disabled_not_selectable (v : ChannelView)
    (h : v.disabled = true) :
    v.edge ∈ (viewGraph [v]).edges ∧
      (viewGraph [v]).findEdge v.node1 v.node2 = none := by
  have hgen : ∀ x ∈ (viewGraph [v]).edges, x.enabled = false := by
    intro x hx
    have hx' : x ∈ [v.edge] := hx
    rw [List.mem_singleton] at hx'
    subst hx'
    simp [ChannelView.edge, h]
  constructor
  · show v.edge ∈ [v.edge]
    simp
  · exact findEdge_none_of_all_disabled _ _ _ hgen

/-- A singleton view whose edge is enabled is found in one step. -/
theorem viewGraph_singleton_enabled_selectable (v : ChannelView)
    (h : v.edge.enabled = true) :
    (viewGraph [v]).findEdge v.node1 v.node2 = some v.edge := by
  rw [Graph.findEdge]
  show Graph.findEdgeIn [v.edge] v.node1 v.node2 = some v.edge
  simp only [Graph.findEdgeIn]
  rw [if_pos]
  exact ⟨h, rfl, rfl⟩

/-- A strictly newer update with the disable bit clear makes the edge
selectable again (BOLT 7 allows re-enabling a channel). -/
theorem update_reenables_edge (v : ChannelView) (u : ChannelUpdate)
    (hscid : v.scid = u.shortChannelId) (h : v.timestamp < u.timestamp)
    (hclear : disableFlagSet u.channelFlags = false) :
    (viewGraph [v.applyUpdate u]).findEdge (v.applyUpdate u).node1
        (v.applyUpdate u).node2 = some (v.applyUpdate u).edge :=
  viewGraph_singleton_enabled_selectable (v.applyUpdate u)
    (ChannelView.applyUpdate_newer_enables v u hscid h hclear)

/-! ## Store-level timestamp laws -/

/-- `applyUpdate` never changes the announcement list, so announcement
membership is unaffected by accepting or ignoring an update. -/
theorem applyUpdate_announcements (s : GossipState) (u : ChannelUpdate) :
    (s.applyUpdate u).announcements = s.announcements := by
  unfold GossipState.applyUpdate
  split <;> rfl

/-- Applying the same store update twice is idempotent.  The second delivery
is stale because the first either stored the update (so the clock is at
least its timestamp) or rejected it (so the clock already dominated it). -/
theorem gossip_applyUpdate_idempotent (s : GossipState) (u : ChannelUpdate) :
    (s.applyUpdate u).applyUpdate u = s.applyUpdate u := by
  by_cases h : s.latestUpdateTimestamp < u.timestamp
  · have hmem : u ∈ (s.applyUpdate u).updates := by
      rw [GossipState.applyUpdate_new s u h]
      exact List.mem_cons_self ..
    have hclk : u.timestamp ≤ (s.applyUpdate u).latestUpdateTimestamp :=
      mem_timestamp_le_latest hmem
    exact GossipState.applyUpdate_stale (s.applyUpdate u) u hclk
  · have hstale : s.applyUpdate u = s :=
      GossipState.applyUpdate_stale s u (Nat.le_of_not_lt h)
    rw [hstale]
    exact hstale

/-- **An older timestamp never replaces a newer one.**  After a strictly
newer update `u` is accepted, any `u'` with `u'.timestamp ≤ u.timestamp` is
a no-op on the resulting store. -/
theorem gossip_applyUpdate_absorb (s : GossipState) (u u' : ChannelUpdate)
    (h : s.latestUpdateTimestamp < u.timestamp)
    (h' : u'.timestamp ≤ u.timestamp) :
    (s.applyUpdate u).applyUpdate u' = s.applyUpdate u := by
  have hmem : u ∈ (s.applyUpdate u).updates := by
    rw [GossipState.applyUpdate_new s u h]
    exact List.mem_cons_self ..
  have hclk : u.timestamp ≤ (s.applyUpdate u).latestUpdateTimestamp :=
    mem_timestamp_le_latest hmem
  exact GossipState.applyUpdate_stale (s.applyUpdate u) u' (Nat.le_trans h' hclk)

/-- Message-level idempotence of a repeated `channel_update`. -/
theorem applyGossip_update_idempotent (s : GossipState) (u : ChannelUpdate) :
    applyGossip (applyGossip s (.channelUpdate u)) (.channelUpdate u) =
      applyGossip s (.channelUpdate u) :=
  gossip_applyUpdate_idempotent s u

/-- A store update has a determinate, case-by-case effect on the update
list: only a `channel_update` message can grow it. -/
theorem applyGossip_updates_eq (s : GossipState) (m : GossipMessage) :
    (applyGossip s m).updates =
      match m with
      | .channelAnnouncement _ => s.updates
      | .channelUpdate u => (s.applyUpdate u).updates
      | .nodeAnnouncement _ => s.updates := by
  cases m <;> rfl

/-- A store update has a determinate effect on the announcement list. -/
theorem applyGossip_announcements_eq (s : GossipState) (m : GossipMessage) :
    (applyGossip s m).announcements =
      match m with
      | .channelAnnouncement a => a :: s.announcements
      | .channelUpdate u => (s.applyUpdate u).announcements
      | .nodeAnnouncement _ => s.announcements := by
  cases m <;> rfl

/-- Announcements are never removed by any gossip message. -/
theorem applyGossip_announcement_mem (s : GossipState) (m : GossipMessage)
    {a : ChannelAnnellation} (h : a ∈ s.announcements) :
    a ∈ (applyGossip s m).announcements := by
  cases m with
  | channelAnnouncement a' => exact List.mem_cons_of_mem _ h
  | channelUpdate u =>
      show a ∈ (s.applyUpdate u).announcements
      rw [applyUpdate_announcements]
      exact h
  | nodeAnnouncement n => exact h

/-! ## Store-level uniqueness of channel bindings -/

/-- A gossip store has unique channel bindings when every pair of stored
announcements for the same `short_channel_id` agrees on both node keys.

This is the store invariant that a deduplicating BOLT 7 implementation is
expected to maintain.  Wave A's `applyGossip` is append-only and does not
enforce it; see `uniqueBindings_applyAnnouncement` for the compatible case
and the module docstring for the gap. -/
def uniqueBindings (s : GossipState) : Prop :=
  ∀ a ∈ s.announcements, ∀ b ∈ s.announcements,
    a.shortChannelId = b.shortChannelId → a.node1 = b.node1 ∧ a.node2 = b.node2

/-- The empty store has unique bindings. -/
theorem uniqueBindings_empty : uniqueBindings ⟨[], [], []⟩ := by
  intro a ha
  simp at ha

/-- Accepting an update does not disturb announcement uniqueness. -/
theorem uniqueBindings_applyUpdate (s : GossipState) (u : ChannelUpdate)
    (h : uniqueBindings s) : uniqueBindings (s.applyUpdate u) := by
  intro a ha b hb hscid
  rw [applyUpdate_announcements] at ha hb
  exact h a ha b hb hscid

/-- A node announcement does not disturb announcement uniqueness. -/
theorem uniqueBindings_applyNodeAnnouncement (s : GossipState)
    (n : NodeAnnouncement) (h : uniqueBindings s) :
    uniqueBindings (applyGossip s (.nodeAnnouncement n)) := by
  intro a ha b hb hscid
  exact h a ha b hb hscid

/-- **Compatible re-announcement preserves uniqueness.**  If the new
announcement agrees with every stored announcement for the same
`short_channel_id`, the append-only store keeps the invariant.  Without this
compatibility hypothesis a conflicting re-announcement breaks it; wave A has
no rejection rule for that case (recorded as an open item). -/
theorem uniqueBindings_applyAnnouncement (s : GossipState)
    (a : ChannelAnnellation) (h : uniqueBindings s)
    (hcompat : ∀ b ∈ s.announcements, b.shortChannelId = a.shortChannelId →
      b.node1 = a.node1 ∧ b.node2 = a.node2) :
    uniqueBindings (applyGossip s (.channelAnnouncement a)) := by
  intro x hx y hy hscid
  simp only [applyGossip, List.mem_cons] at hx hy
  rcases hx with rfl | hx
  · rcases hy with rfl | hy
    · exact ⟨rfl, rfl⟩
    · have hb := hcompat y hy hscid.symm
      exact ⟨hb.1.symm, hb.2.symm⟩
  · rcases hy with rfl | hy
    · exact hcompat x hx hscid
    · exact h x hx y hy hscid

/-! ## Node announcements cannot change a node id -/

/-- The proof layer's node record: the BOLT 7 node key plus the mutable
`node_announcement` metadata used by this module. -/
structure NodeRecord where
  /-- The BOLT 7 `node_id`; the record is keyed by it. -/
  nodeId : PubKey
  alias : ByteArray
  timestamp : Timestamp

namespace NodeRecord

/-- Apply a `node_announcement` to an existing record.  It is accepted only
when the signature verifies, the announced key equals the record key
(byte-level equality), and the timestamp is strictly newer. -/
noncomputable def applyAnnouncement (verify : SigVerifier) (r : NodeRecord)
    (n : NodeAnnouncement) : NodeRecord :=
  if n.signatureValid verify ∧ r.nodeId.bytes = n.nodeId.bytes ∧
      r.timestamp < n.timestamp then
    { r with alias := n.alias, timestamp := n.timestamp }
  else r

/-- **A node announcement cannot change an existing node id**, accepted or
not. -/
theorem applyAnnouncement_nodeId (verify : SigVerifier) (r : NodeRecord)
    (n : NodeAnnouncement) :
    (applyAnnouncement verify r n).nodeId = r.nodeId := by
  unfold applyAnnouncement
  split <;> rfl

/-- An announcement carrying a different node key is rejected. -/
theorem applyAnnouncement_rejects_other_node (verify : SigVerifier)
    (r : NodeRecord) (n : NodeAnnouncement)
    (h : r.nodeId.bytes ≠ n.nodeId.bytes) :
    applyAnnouncement verify r n = r := by
  unfold applyAnnouncement
  rw [if_neg]
  rintro ⟨_, hbytes, _⟩
  exact h hbytes

/-- Any accepted change requires the model's signature predicate. -/
theorem applyAnnouncement_change_requires_signature (verify : SigVerifier)
    (r : NodeRecord) (n : NodeAnnouncement)
    (h : applyAnnouncement verify r n ≠ r) :
    n.signatureValid verify := by
  apply Classical.byContradiction
  intro hsig
  apply h
  unfold applyAnnouncement
  rw [if_neg]
  rintro ⟨hs, _, _⟩
  exact hsig hs

end NodeRecord

/-! ## Channel announcements bind a `short_channel_id` -/

/-- The immutable binding extracted from a `channel_announcement`: the
`short_channel_id`, the two graph node ids, the two BOLT 7 node keys, and the
announced capacity. -/
structure ChannelBinding where
  scid : ShortChannelId
  /-- First graph node id from the announcement. -/
  node1 : NodeId
  /-- Second graph node id from the announcement. -/
  node2 : NodeId
  /-- BOLT 7 `node_id_1` key (signature verification key). -/
  nodeKey1 : PubKey
  /-- BOLT 7 `node_id_2` key (signature verification key). -/
  nodeKey2 : PubKey
  capacitySat : Nat

/-- Extract the binding only when all four BOLT 7 signatures verify. -/
noncomputable def bindChannel (verify : SigVerifier) (a : ChannelAnnellation) :
    Option ChannelBinding :=
  if a.signaturesValid verify then
    some { scid := a.shortChannelId, node1 := a.node1, node2 := a.node2,
           nodeKey1 := a.nodeKey1, nodeKey2 := a.nodeKey2,
           capacitySat := a.capacitySat }
  else none

/-- **A successful bind returns exactly the announced binding.** -/
theorem bindChannel_binds {verify : SigVerifier} {a : ChannelAnnellation}
    {b : ChannelBinding} (h : bindChannel verify a = some b) :
    b.scid = a.shortChannelId ∧ b.node1 = a.node1 ∧ b.node2 = a.node2 := by
  unfold bindChannel at h
  split at h
  · cases h
    exact ⟨rfl, rfl, rfl⟩
  · simp at h

/-- A successful bind entails all four signature checks. -/
theorem bindChannel_requires_signature {verify : SigVerifier}
    {a : ChannelAnnellation} {b : ChannelBinding}
    (h : bindChannel verify a = some b) : a.signaturesValid verify := by
  unfold bindChannel at h
  split at h
  · assumption
  · simp at h

/-- An announcement with a failed signature predicate is not bound. -/
theorem bindChannel_none_of_invalid {verify : SigVerifier}
    {a : ChannelAnnellation} (h : ¬ a.signaturesValid verify) :
    bindChannel verify a = none := by
  unfold bindChannel
  rw [if_neg h]

/-- A binding preserves distinctness of the two announced graph node ids. -/
theorem bindChannel_distinct {verify : SigVerifier} {a : ChannelAnnellation}
    {b : ChannelBinding} (h : bindChannel verify a = some b)
    (hne : a.node1 ≠ a.node2) : b.node1 ≠ b.node2 := by
  rcases bindChannel_binds h with ⟨_, h1, h2⟩
  exact fun hb => hne (h1.symm.trans (hb.trans h2))

/-- Materialise a channel binding as one directed edge.  An announcement
does not carry per-direction fees, so the fee fields start at zero; the
following `channel_update` fills them in through `ChannelView.applyUpdate`. -/
def ChannelBinding.edge (b : ChannelBinding) : ChannelEdge :=
  { shortChannelId := b.scid
    node1 := b.node1
    node2 := b.node2
    capacitySat := b.capacitySat
    feeBaseMsat := Msat.zero
    feeProportionalMillionths := 0
    cltvDelta := 0
    enabled := true }

/-- **Materialisation preserves well-formedness.**  A signature-checked
binding with distinct node ids and a valid `short_channel_id` becomes a
well-formed edge. -/
theorem announcement_materialises_wellFormed (verify : SigVerifier)
    (a : ChannelAnnellation) (b : ChannelBinding)
    (hbind : bindChannel verify a = some b)
    (hne : a.node1 ≠ a.node2) (hscid : a.shortChannelId.Valid) :
    graphWellFormed (Graph.empty.addEdge (ChannelBinding.edge b)) := by
  have hb := bindChannel_binds hbind
  apply graphWellFormed_addEdge
  · exact graphWellFormed_empty
  · exact bindChannel_distinct hbind hne
  · show b.scid.Valid
    rw [hb.1]
    exact hscid

/-! ## Signature-checked gossip application -/

/-- Accept one `channel_update` only if the model's signature predicate
holds.  This is the conditional check required by BOLT 7; it does *not*
assert that the verifier cannot be fooled (assumption C3/C4). -/
noncomputable def acceptChannelUpdate (verify : SigVerifier) (s : GossipState)
    (u : ChannelUpdate) : GossipState :=
  if u.signatureValid verify then s.applyUpdate u else s

/-- An invalid update is rejected outright. -/
theorem acceptChannelUpdate_rejects_invalid (verify : SigVerifier)
    (s : GossipState) (u : ChannelUpdate)
    (h : ¬ u.signatureValid verify) :
    acceptChannelUpdate verify s u = s := by
  unfold acceptChannelUpdate
  rw [if_neg h]

/-- Any accepted change requires the signature predicate. -/
theorem acceptChannelUpdate_change_requires_signature (verify : SigVerifier)
    (s : GossipState) (u : ChannelUpdate)
    (h : acceptChannelUpdate verify s u ≠ s) :
    u.signatureValid verify := by
  apply Classical.byContradiction
  intro hsig
  apply h
  unfold acceptChannelUpdate
  rw [if_neg hsig]

/-- Any accepted change also requires a strictly newer timestamp. -/
theorem acceptChannelUpdate_change_requires_newer (verify : SigVerifier)
    (s : GossipState) (u : ChannelUpdate)
    (h : acceptChannelUpdate verify s u ≠ s) :
    s.latestUpdateTimestamp < u.timestamp := by
  apply Classical.byContradiction
  intro hnot
  have hle : u.timestamp ≤ s.latestUpdateTimestamp := Nat.le_of_not_lt hnot
  apply h
  unfold acceptChannelUpdate
  split
  · exact GossipState.applyUpdate_stale s u hle
  · rfl

/-- **Soundness of update acceptance**: a change needs both a verifying
signature and a strictly newer timestamp. -/
theorem acceptChannelUpdate_sound (verify : SigVerifier) (s : GossipState)
    (u : ChannelUpdate) (h : acceptChannelUpdate verify s u ≠ s) :
    u.signatureValid verify ∧ s.latestUpdateTimestamp < u.timestamp :=
  ⟨acceptChannelUpdate_change_requires_signature verify s u h,
   acceptChannelUpdate_change_requires_newer verify s u h⟩

/-- A valid but stale update is a no-op. -/
theorem acceptChannelUpdate_stale (verify : SigVerifier) (s : GossipState)
    (u : ChannelUpdate) (hsig : u.signatureValid verify)
    (h : u.timestamp ≤ s.latestUpdateTimestamp) :
    acceptChannelUpdate verify s u = s := by
  unfold acceptChannelUpdate
  rw [if_pos hsig]
  exact GossipState.applyUpdate_stale s u h

/-- Checked store-level application of all three gossip messages.  Every
state change is gated by the corresponding `signatureValid` predicate. -/
noncomputable def applyGossipChecked (verify : SigVerifier) (s : GossipState) :
    GossipMessage → GossipState
  | .channelAnnouncement a =>
      if a.signaturesValid verify then applyGossip s (.channelAnnouncement a) else s
  | .channelUpdate u => acceptChannelUpdate verify s u
  | .nodeAnnouncement n =>
      if n.signatureValid verify then applyGossip s (.nodeAnnouncement n) else s

/-- An invalid channel announcement is not stored. -/
theorem applyGossipChecked_rejects_announcement (verify : SigVerifier)
    (s : GossipState) (a : ChannelAnnellation)
    (h : ¬ a.signaturesValid verify) :
    applyGossipChecked verify s (.channelAnnouncement a) = s := by
  simp [applyGossipChecked, h]

/-- A change caused by a `channel_announcement` requires all four
signature checks. -/
theorem applyGossipChecked_announcement_requires_signature
    (verify : SigVerifier) (s : GossipState) (a : ChannelAnnellation)
    (h : applyGossipChecked verify s (.channelAnnouncement a) ≠ s) :
    a.signaturesValid verify := by
  apply Classical.byContradiction
  intro hsig
  exact h (applyGossipChecked_rejects_announcement verify s a hsig)

/-- An invalid node announcement is not stored. -/
theorem applyGossipChecked_rejects_node (verify : SigVerifier)
    (s : GossipState) (n : NodeAnnouncement)
    (h : ¬ n.signatureValid verify) :
    applyGossipChecked verify s (.nodeAnnouncement n) = s := by
  simp [applyGossipChecked, h]

/-- A change caused by a `node_announcement` requires its signature. -/
theorem applyGossipChecked_node_requires_signature (verify : SigVerifier)
    (s : GossipState) (n : NodeAnnouncement)
    (h : applyGossipChecked verify s (.nodeAnnouncement n) ≠ s) :
    n.signatureValid verify := by
  apply Classical.byContradiction
  intro hsig
  exact h (applyGossipChecked_rejects_node verify s n hsig)

/-- On valid messages the checked step is exactly wave A's `applyGossip`
(updates via `acceptChannelUpdate`, which then equals `applyGossip`). -/
theorem applyGossipChecked_update_eq (verify : SigVerifier) (s : GossipState)
    (u : ChannelUpdate) (h : u.signatureValid verify) :
    applyGossipChecked verify s (.channelUpdate u) =
      applyGossip s (.channelUpdate u) := by
  simp [applyGossipChecked, acceptChannelUpdate, applyGossip, h]

/-! ## The network state and graph well-formedness -/

/-- A network state pairs the gossip store with the materialised channel
views.  This is the seam between the wave-A store (which has no graph) and
the route-search graph. -/
structure GossipNetwork where
  gossip : GossipState
  views : List ChannelView

namespace GossipNetwork

/-- The routing graph of a network state. -/
def graph (ns : GossipNetwork) : Graph := viewGraph ns.views

/-- Apply one message.  The store uses `applyGossipChecked`; the view list is
updated only for a verifying `channel_update`, by applying the same
per-channel replacement rule as `ChannelView.applyUpdate`.  Announcements
are recorded in the store; creating/inserting the two directional
`ChannelView`s (with their zero-fee defaults and direction keying) from an
announcement is left as an explicit obligation, because wave A has no
direction-keyed store. -/
noncomputable def applyMessage (verify : SigVerifier) (ns : GossipNetwork) :
    GossipMessage → GossipNetwork
  | .channelAnnouncement a =>
      { ns with gossip := applyGossipChecked verify ns.gossip (.channelAnnouncement a) }
  | .channelUpdate u =>
      { gossip := applyGossipChecked verify ns.gossip (.channelUpdate u)
        views := if u.signatureValid verify then
          ns.views.map fun v => v.applyUpdate u
        else ns.views }
  | .nodeAnnouncement n =>
      { ns with gossip := applyGossipChecked verify ns.gossip (.nodeAnnouncement n) }

/-- The store component of a network step is the checked store function:
deterministic by construction. -/
theorem applyMessage_gossip (verify : SigVerifier) (ns : GossipNetwork)
    (m : GossipMessage) :
    (ns.applyMessage verify m).gossip =
      applyGossipChecked verify ns.gossip m := by
  cases m <;> rfl

/-- A network step preserves the well-formedness of every channel view. -/
theorem applyMessage_views_wf (verify : SigVerifier) (ns : GossipNetwork)
    (m : GossipMessage)
    (h : ∀ v ∈ ns.views, v.node1 ≠ v.node2 ∧ v.scid.Valid) :
    ∀ v ∈ (ns.applyMessage verify m).views,
      v.node1 ≠ v.node2 ∧ v.scid.Valid := by
  cases m with
  | channelAnnouncement a => simpa [GossipNetwork.applyMessage] using h
  | nodeAnnouncement n => simpa [GossipNetwork.applyMessage] using h
  | channelUpdate u =>
      intro v hv
      simp only [GossipNetwork.applyMessage] at hv
      split at hv
      · rcases List.mem_map.mp hv with ⟨w, hw, rfl⟩
        exact ⟨by
            simpa [ChannelView.applyUpdate_node1, ChannelView.applyUpdate_node2]
              using (h w hw).1,
          by simpa [ChannelView.applyUpdate_scid] using (h w hw).2⟩
      · exact h v hv

/-- **`applyGossip` preserves graph well-formedness.**  The wave-A
`applyGossip` has no graph argument; the meaningful statement is at this
seam: the network step (whose store component is `applyGossipChecked`, equal
to `applyGossip` on valid messages) maps a well-formed materialised graph to
a well-formed materialised graph. -/
theorem applyMessage_preserves_graphWellFormed (verify : SigVerifier)
    (ns : GossipNetwork) (m : GossipMessage)
    (h : graphWellFormed ns.graph) :
    graphWellFormed (ns.applyMessage verify m).graph := by
  have hv : ∀ v ∈ ns.views, v.node1 ≠ v.node2 ∧ v.scid.Valid :=
    viewGraph_wellFormed_inv (by simpa [GossipNetwork.graph] using h)
  exact viewGraph_wellFormed (applyMessage_views_wf verify ns m hv)

end GossipNetwork

/-! ## Open obligations -/

/-- BOLT 7 takes the `node_id` used to verify a `channel_update` from the
matching `channel_announcement` (`refs/bolts/07-routing-gossip.md:544`).
Wave A's `ChannelUpdate.signingKey` is an independent field, so attribution
cannot be derived from the store. -/
-- OBLIGATION: LN-GOSSIP-001 an accepted channel_update is signed by one of the two announced node ids of its channel
theorem accepted_update_signing_key_announced (verify : SigVerifier)
    (s : GossipState) (u : ChannelUpdate)
    (h : acceptChannelUpdate verify s u ≠ s) :
    ∃ a ∈ s.announcements, a.shortChannelId = u.shortChannelId ∧
      (a.nodeKey1 = u.signingKey ∨ a.nodeKey2 = u.signingKey) := by
  sorry

/-- BOLT 7 defines `capacity` as the funding output value, which is positive
on L1.  Wave A stores `capacitySat : Nat` without a positivity invariant, so
the fact must be checked at admission. -/
-- OBLIGATION: LN-GOSSIP-002 an accepted channel announcement has a positive capacity
theorem bindChannel_capacity_positive {verify : SigVerifier}
    {a : ChannelAnnellation} {b : ChannelBinding}
    (h : bindChannel verify a = some b) : 0 < b.capacitySat := by
  sorry

/-- BOLT 7 gossip signatures are 64 bytes.  `GossipSignature.Valid` records
this, but the abstract `SigVerifier` interface does not require it, so the
length check is an admission obligation. -/
-- OBLIGATION: LN-GOSSIP-003 an accepted channel_update has a 64-byte signature
theorem accepted_update_signature_length (verify : SigVerifier)
    (s : GossipState) (u : ChannelUpdate)
    (h : acceptChannelUpdate verify s u ≠ s) :
    u.signature.Valid := by
  sorry

/-! ## Checked counterexamples to the remaining obligations

The three obligations above are **not** theorems of the current wave-A model:
the store does not relate `ChannelUpdate.signingKey` to a stored
`ChannelAnnellation` key, `ChannelAnnellation.capacitySat` is an unconstrained
`Nat`, and `SigVerifier` does not require `GossipSignature.Valid`.  The
`private` theorems below are complete, `sorry`-free proofs that each
universally quantified obligation is false.  They are private so they do not
extend the public API; the original `sorry` sites and their
`-- OBLIGATION:` markers are retained deliberately, because closing them
would require a model change (an admission guard or a new invariant), not a
proof of the current definitions. -/

/-- The all-accepting verifier: every signature verifies under every key. -/
private def acceptingVerifier : SigVerifier := fun _ _ _ => true

/-- The empty gossip store. -/
private def emptyGossipState : GossipState := ⟨[], [], []⟩

/-- An update with timestamp `1` and an empty (0-byte) signature, so it is
strictly newer than the empty store's clock but is not a 64-byte signature. -/
private def unannouncedUpdate : ChannelUpdate :=
  { shortChannelId := ⟨0, 0, 0⟩
    timestamp := 1
    messageFlags := 0
    channelFlags := 0
    cltvDelta := 1
    htlcMinimumMsat := Msat.zero
    feeBaseMsat := Msat.zero
    feeProportionalMillionths := 0
    htlcMaximumMsat := Msat.zero
    signingKey := ⟨ByteArray.empty⟩
    digest := ByteArray.empty
    signature := ⟨ByteArray.empty⟩ }

/-- The all-accepting verifier and the 0-byte-signature update really do
change the empty store, so the hypotheses of the three obligations are
satisfiable. -/
private theorem acceptingVerifier_changes_empty :
    acceptChannelUpdate acceptingVerifier emptyGossipState unannouncedUpdate ≠
      emptyGossipState := by
  intro h
  have hupd : (acceptChannelUpdate acceptingVerifier emptyGossipState
      unannouncedUpdate).updates = [unannouncedUpdate] := by
    simp [acceptChannelUpdate, acceptingVerifier,
      ChannelUpdate.signatureValid, signatureValid, emptyGossipState,
      GossipState.applyUpdate, GossipState.latestUpdateTimestamp,
      latestTimestamp, unannouncedUpdate]
  rw [h] at hupd
  simp [emptyGossipState] at hupd

/-- **LN-GOSSIP-001 is false.**  The update is accepted (its timestamp is
newer and the verifier accepts it) but the store contains no announcement at
all, so no announced node key can be attributed to it. -/
private theorem LN_GOSSIP_001_counterexample :
    ¬ (∀ (verify : SigVerifier) (s : GossipState) (u : ChannelUpdate),
        acceptChannelUpdate verify s u ≠ s →
          ∃ a ∈ s.announcements, a.shortChannelId = u.shortChannelId ∧
            (a.nodeKey1 = u.signingKey ∨ a.nodeKey2 = u.signingKey)) := by
  intro h
  have hex := h acceptingVerifier emptyGossipState unannouncedUpdate
    acceptingVerifier_changes_empty
  rcases hex with ⟨a, ha, _⟩
  simp [emptyGossipState] at ha

/-- **LN-GOSSIP-002 is false.**  A signature-valid announcement with
`capacitySat = 0` yields a binding whose capacity is zero. -/
private theorem LN_GOSSIP_002_counterexample :
    ¬ (∀ {verify : SigVerifier} {a : ChannelAnnellation}
        {b : ChannelBinding},
        bindChannel verify a = some b → 0 < b.capacitySat) := by
  intro h
  let a : ChannelAnnellation :=
    { shortChannelId := ⟨0, 0, 0⟩
      node1 := ⟨0⟩
      node2 := ⟨1⟩
      nodeKey1 := ⟨ByteArray.empty⟩
      nodeKey2 := ⟨ByteArray.empty⟩
      bitcoinKey1 := ⟨ByteArray.empty⟩
      bitcoinKey2 := ⟨ByteArray.empty⟩
      capacitySat := 0
      digest := ByteArray.empty
      nodeSignature1 := ⟨ByteArray.empty⟩
      nodeSignature2 := ⟨ByteArray.empty⟩
      bitcoinSignature1 := ⟨ByteArray.empty⟩
      bitcoinSignature2 := ⟨ByteArray.empty⟩ }
  let b : ChannelBinding :=
    { scid := ⟨0, 0, 0⟩
      node1 := ⟨0⟩
      node2 := ⟨1⟩
      nodeKey1 := ⟨ByteArray.empty⟩
      nodeKey2 := ⟨ByteArray.empty⟩
      capacitySat := 0 }
  have hbind : bindChannel acceptingVerifier a = some b := by
    simp [bindChannel, ChannelAnnellation.signaturesValid, signatureValid,
      acceptingVerifier, a, b]
  have hpos : 0 < b.capacitySat := h hbind
  simp [b] at hpos

/-- **LN-GOSSIP-003 is false.**  The 0-byte signature is accepted by the
abstract verifier, so acceptance gives no length bound. -/
private theorem LN_GOSSIP_003_counterexample :
    ¬ (∀ (verify : SigVerifier) (s : GossipState) (u : ChannelUpdate),
        acceptChannelUpdate verify s u ≠ s → u.signature.Valid) := by
  intro h
  have hvalid : unannouncedUpdate.signature.Valid :=
    h acceptingVerifier emptyGossipState unannouncedUpdate
      acceptingVerifier_changes_empty
  simp [unannouncedUpdate, GossipSignature.Valid] at hvalid

end LnLean.Routing.GossipProps
