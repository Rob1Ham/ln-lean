import LnLean.Routing.Graph
import LnLean.Routing.Gossip
import LnLean.Routing.Onion
import LnLean.Routing.Route

/-!
# LnLean.Routing.Laws

The proved law bundle for the BOLT 4/7 routing and onion model.

English claim of this module:

* Route construction is non-empty, the total fee is exactly the sum of hop
  fees, the total CLTV delta is exactly the sum of hop deltas, and the
  accumulated expiry strictly increases across a non-empty route with
  positive per-hop deltas.
* Edge lookup is sound: a successful `findEdge` returns an enabled edge of
  the graph with the requested endpoints, and a valid route has such an
  edge behind every hop.
* Gossip application never lowers the newest `channel_update` timestamp, a
  stale update is a no-op, and a strictly newer update is stored.
* Onion layer count equals hop count, peel-all visits exactly the sealed
  layers, opening a layer requires HMAC verification, opening removes
  exactly the head layer, terminal detection is equivalent to having no
  layers, and the failure packet is 290 bytes when its data fits the
  256-byte padding target.

Every theorem below is proved without `sorry`, axioms, `native_decide`,
`unsafe`, or `@[implemented_by]`.  The only quoted cryptographic facts are
`Prop`-valued assumptions (`OnionInterface.hmacBinding`, `SigVerifier`);
no theorem in this file proves them.

BOLT sections:

* BOLT 4, "Routing", "Onion Routing", "Failure Messages".
* BOLT 7, "The `channel_announcement` Message" and "The `channel_update`
  Message" (timestamp replacement rule, fee and CLTV fields).

`rust-lightning` anchors (pinned commit `fe4900930c6bd5786ec4203274d7cf312776a5a6`;
line numbers are anchored to the symbol, see `agents/reports/A6.md` for the
pin-verification caveat):

* `lightning/src/routing/router.rs:90` — `RouteHop` (fee and CLTV fields).
* `lightning/src/routing/router.rs:150` — `Route::get_total_fees`.
* `lightning/src/routing/gossip.rs:1596` — `NetworkGraph::update_channel`
  (timestamp monotonicity).
* `lightning/src/ln/onion_utils.rs:50` — `OnionPacket` (layer count and
  fixed packet size).
* `lightning/src/ln/onion_utils.rs:1300` — `encrypt_failure_packet`
  (290-byte failure packet).

What is **not** modelled or proved:

* Onion privacy, unlinkability, and HMAC unforgeability (assumption C8).
* Gossip signature unforgeability (C3/C4) and BOLT 7 wire validity.
* Route optimality, liquidity, and the backwards fee search.
* Completeness of `simplePaths` and any liveness property of gossip
  dissemination.
-/

namespace LnLean.Routing

set_option autoImplicit false

/-! ## Route laws -/

/-- **Route non-emptiness.**  Constructing a route from a non-empty path
yields a non-empty hop list. -/
theorem route_nonempty_law (e : ChannelEdge × Msat)
    (path : List (ChannelEdge × Msat)) (amountMsat : Msat) :
    (constructRoute (e :: path) amountMsat).hops ≠ [] :=
  constructRoute_nonempty e path amountMsat

/-- **Total fee is the sum of hop fees** (definitional reading of the
route's `totalFee`). -/
theorem route_totalFee_eq_sum (r : Route) :
    r.totalFee.val = (r.hops.map fun h => h.feeMsat.val).sum := rfl

/-- **Fees are additive** under route concatenation. -/
theorem route_totalFee_append (r₁ r₂ : Route) :
    (r₁.append r₂).totalFee.val = r₁.totalFee.val + r₂.totalFee.val :=
  Route.totalFee_append r₁ r₂

/-- **Total CLTV delta is the sum of hop deltas.** -/
theorem route_totalCltv_eq_sum (r : Route) :
    r.totalCltv = (r.hops.map Hop.cltvDelta).sum := rfl

/-- **CLTV deltas are additive** under route concatenation. -/
theorem route_totalCltv_append (r₁ r₂ : Route) :
    (r₁.append r₂).totalCltv = r₁.totalCltv + r₂.totalCltv :=
  Route.totalCltv_append r₁ r₂

/-- **CLTV strictly increases** across a non-empty route when every hop
charges a positive delta. -/
theorem route_cltv_strict (r : Route) (start : Nat) (hne : r.NonEmpty)
    (hpos : ∀ h ∈ r.hops, 0 < h.cltvDelta) :
    start < r.endExpiry start :=
  Route.endExpiry_gt' r start hne hpos

/-- The constructed route inherits strict CLTV growth from its candidate
path. -/
theorem constructedRoute_cltv_strict (path : List (ChannelEdge × Msat))
    (amountMsat : Msat) (start : Nat) (hne : path ≠ [])
    (hpos : ∀ p ∈ path, 0 < p.1.cltvDelta) :
    start < (constructRoute path amountMsat).endExpiry start := by
  apply Route.endExpiry_gt'
  · simp [Route.NonEmpty, constructRoute, hne]
  · intro h hh
    simp only [constructRoute_hops] at hh
    rcases List.mem_map.mp hh with ⟨⟨e, a⟩, hp, rfl⟩
    simpa using hpos (e, a) hp

/-- **Edge lookup soundness.**  A successful `findEdge` yields a member of
the graph, enabled, with the requested endpoints. -/
theorem edge_lookup_sound {g : Graph} {fromNode toNode : NodeId}
    {e : ChannelEdge} (h : g.findEdge fromNode toNode = some e) :
    e ∈ g.edges ∧ e.enabled = true ∧
      e.node1 = fromNode ∧ e.node2 = toNode :=
  Graph.findEdge_sound h

/-- Endpoint form of edge lookup soundness. -/
theorem edge_lookup_endpoints {g : Graph} {fromNode toNode : NodeId}
    {e : ChannelEdge} (h : g.findEdge fromNode toNode = some e) :
    e.node1 = fromNode ∧ e.node2 = toNode :=
  Graph.findEdge_endpoints h

/-- Adding an enabled edge makes it findable in that direction. -/
theorem edge_add_lookup (g : Graph) (e : ChannelEdge)
    (hen : e.enabled = true) :
    (g.addEdge e).findEdge e.node1 e.node2 = some e :=
  Graph.findEdge_addEdge_self g e hen

/-- **A valid route has an enabled graph edge behind every hop.** -/
theorem route_edges_sound {g : Graph} {r : Route} (h : routeValid g r) :
    ∀ hop ∈ r.hops, ∃ e ∈ g.edges,
      e.enabled = true ∧ e.shortChannelId = hop.shortChannelId ∧
        e.node2 = hop.node :=
  routeValid_edge_sound h

/-- A candidate path of enabled graph edges constructs a valid route. -/
theorem constructed_route_valid (g : Graph)
    (path : List (ChannelEdge × Msat)) (amountMsat : Msat) (hne : path ≠ [])
    (hmem : ∀ p ∈ path, p.1 ∈ g.edges)
    (hen : ∀ p ∈ path, p.1.enabled = true) :
    routeValid g (constructRoute path amountMsat) :=
  constructRoute_valid g path amountMsat hne hmem hen

/-! ## Gossip laws -/

/-- **Gossip timestamp monotonicity.**  No gossip message can lower the
newest stored `channel_update` timestamp. -/
theorem gossip_timestamp_monotone (s : GossipState) (m : GossipMessage) :
    s.latestUpdateTimestamp ≤ (applyGossip s m).latestUpdateTimestamp :=
  applyGossip_timestamp_monotone s m

/-- **Stale updates are ignored.**  An update whose timestamp is not greater
than the stored clock leaves the store unchanged. -/
theorem gossip_stale_noop (s : GossipState) (u : ChannelUpdate)
    (h : u.timestamp ≤ s.latestUpdateTimestamp) :
    applyGossip s (.channelUpdate u) = s :=
  applyGossip_stale_update s u h

/-- **Newer updates are stored.**  A strictly newer update becomes the head
of the update list. -/
theorem gossip_new_update_stored (s : GossipState) (u : ChannelUpdate)
    (h : s.latestUpdateTimestamp < u.timestamp) :
    (s.applyUpdate u).updates = u :: s.updates :=
  GossipState.applyUpdate_new s u h

/-- Every retained update's timestamp is at most the stored clock. -/
theorem gossip_mem_timestamp_le_latest {s : GossipState}
    {u : ChannelUpdate} (h : u ∈ s.updates) :
    u.timestamp ≤ s.latestUpdateTimestamp :=
  mem_timestamp_le_latest h

/-- A well-formed `channel_update` has a positive CLTV delta. -/
theorem gossip_update_cltv_pos {u : ChannelUpdate} (h : u.wellFormed) :
    0 < u.cltvDelta :=
  ChannelUpdate.wellFormed_cltvDelta_pos h

/-! ## Onion laws -/

/-- **Onion layer count equals hop count.** -/
theorem onion_layer_count_law (version : Nat) (ephemeralKey : PubKey)
    (hops : List OnionHop) (payload : ByteArray) :
    (sealLayers version ephemeralKey hops payload).layerCount = hops.length :=
  sealLayers_layerCount version ephemeralKey hops payload

/-- One seal adds exactly one layer. -/
theorem onion_sealLayer_count (version : Nat) (ephemeralKey : PubKey)
    (hop : OnionHop) (ciphertext hmac : ByteArray) (inner : OnionPacket) :
    (sealLayer version ephemeralKey hop ciphertext hmac inner).layerCount =
      inner.layerCount + 1 :=
  sealLayer_layerCount version ephemeralKey hop ciphertext hmac inner

/-- **Peel-all visits exactly the sealed layers**, so its length is the hop
count. -/
theorem onion_peel_all_law (version : Nat) (ephemeralKey : PubKey)
    (hops : List OnionHop) (payload : ByteArray) :
    (peelAll (sealLayers version ephemeralKey hops payload)).length =
      hops.length :=
  sealLayers_peelAll_length version ephemeralKey hops payload

/-- Peeling never fails. -/
theorem onion_peel_total (p : OnionPacket) : (peel p).isSome = true :=
  peel_isSome p

/-- **Terminal detection.**  A final payload is returned exactly when no
layers remain, and then it is the packet's `routingInfo`. -/
theorem onion_terminal_detection (p : OnionPacket) (payload : ByteArray) :
    peel p = some (.final payload) ↔
      p.layers = [] ∧ payload = p.routingInfo :=
  peel_final_iff p payload

/-- **Onion integrity, mechanical half.**  A successful `openLayer` entails
that the abstract HMAC verifier accepted the head layer.  The step from
verifier acceptance to authenticity is assumption C8 and is not proved. -/
theorem onion_open_requires_hmac {I : OnionInterface} {tag : ByteArray}
    {p : OnionPacket} {hop : OnionHop} {next : OnionPacket}
    (h : openLayer I tag p = some (hop, next)) :
    ∃ l ∈ p.layers, l.hop = hop ∧ I.verifyHmac tag l.hmac = true :=
  openLayer_verified h

/-- A successful open removes exactly the head layer. -/
theorem onion_open_removes_head {I : OnionInterface} {tag : ByteArray}
    {p : OnionPacket} {hop : OnionHop} {next : OnionPacket}
    (h : openLayer I tag p = some (hop, next)) :
    next.layers = p.layers.tail :=
  openLayer_next_layers h

/-- **Layer count is bounded by encoded size**: layers cannot be packed for
free. -/
theorem onion_layerCount_le_size (p : OnionPacket) :
    p.layers.length ≤ p.encodedSize :=
  layerCount_le_encodedSize p

/-- A hop payload that fits the 1300-byte budget has bounded layer size. -/
theorem onion_layer_size_bound (l : OnionLayer)
    (hc : l.ciphertext.size ≤ MAX_HOP_PAYLOAD)
    (hh : l.hmac.size = ONION_HMAC_LEN) :
    l.encodedSize ≤ MAX_HOP_PAYLOAD + 1 + ONION_HMAC_LEN :=
  OnionLayer.encodedSize_bound l hc hh

/-- The fixed BOLT 4 onion packet is 1366 bytes. -/
theorem onion_packet_wire_size (p : OnionPacket) :
    p.wireSize = 1366 := by
  rw [OnionPacket.wireSize_eq_ONION_PACKET_LEN, onion_packet_len_eq]

/-- **Failure packet size bound.**  A BOLT 4 failure message whose data fits
the 256-byte padding target produces a 290-byte packet. -/
theorem onion_error_size_bound (e : OnionError)
    (h : e.data.size ≤ ONION_ERROR_PAD) :
    e.packetSize = 290 :=
  OnionError.packetSize_eq_290 e h

end LnLean.Routing
