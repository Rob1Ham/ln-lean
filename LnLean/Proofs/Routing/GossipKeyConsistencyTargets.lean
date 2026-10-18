import LnLean.Proofs.Routing.GossipAttributionTargets

/-!
# LnLean.Proofs.Routing.GossipKeyConsistencyTargets

Wave-5 lane `S5-GOSSIP-ATTR2`, open issue `RT-01`.

Wave 4 (`LnLean.Proofs.Routing.GossipAttributionTargets`) added the
undirected admission gate `updateKeyAnnounced`: a `channel_update` must be
signed by *one of* the two node keys of a stored announcement for the same
`short_channel_id`.  That still leaves three gaps, all recorded in `RT-01`:

1. **Direction is not decoded.**  BOLT 7 `channel_flags` bit 0 selects the
   direction, and the update must be signed by the node that sends it:
   direction 0 by `node_1`, direction 1 by `node_2`
   (`refs/bolts/07-routing-gossip.md:544`).  Accepting either key lets the
   wrong endpoint sign an update.
2. **There is no `NodeId → PubKey` map.**  `ChannelAnnellation.node1` is an
   opaque graph identifier and `nodeKey1` is a wire key; without an explicit
   consistency invariant an admitted announcement can name a graph node that
   does not own the verifying key.
3. **Announcements are not deduplicated.**  The wave-A store is append-only,
   so two conflicting announcements can share one `short_channel_id` and
   attribute different keys.

This module closes (1) and (2) and gives a canonical view for (3):

* `admitGossipDirected` is an additional admission transition whose
  `channel_update` branch requires the signature predicate **and** the
  direction-keyed relation `GossipState.updateKeyAnnouncedDirectional`
  (added additively in `LnLean/Routing/Gossip.lean`).
* `ReachableDirected` closes that step over all three messages.
* `DirectedAdmitted` is the reachable invariant: every stored announcement
  verifies, every view is announcement-backed, and every stored update is
  signature-valid with a direction-correct announced key.
* `gossip_graph_edges_directional_key_endpoint` proves that every stored
  update of every graph edge is signed by exactly the endpoint selected by
  its direction, under the explicit `NodeKeyConsistent nodeKeyOf` map and the
  `CanonicalAnnouncements` invariant.
* `canonical_directional_attribution_unique` proves that duplicate or
  conflicting announcements cannot produce ambiguous key attribution once
  the canonical invariant holds.
* `conflicting_announcements_ambiguous_without_canonical` is the matching
  counterexample: without the invariant two same-channel announcements
  really do attribute different keys to the same direction.

What is **not** claimed:

* `SigVerifier` remains abstract.  Signature validity is the equation
  `verify key digest sig = true`; unforgeability is assumption C3/C4/C8.
* `NodeKeyConsistent` is an explicit invariant on the final store.  It is not
  derived from wave A, and `NodeId → PubKey` remains an admission-path
  obligation (`gossip_graph_edges_directional_key_endpoint` takes it as a
  hypothesis).
* The canonical view is a viewing operation.  Raw `applyGossip`,
  `GossipState.applyUpdate`, and the wave-4 `admitGossipAttributed` are
  unchanged; the raw store is still append-only, unfiltered, and
  undeduplicated (`raw_applyGossip_accepts_directionally_unattributed_update`
  re-exhibits the raw behaviour).
* Direction is decoded from `channel_flags % 2`; the model still does not
  model wire serialization, chain-hash filtering, UTXO confirmation, or
  gossip dissemination.

No `sorry`, no `axiom`, no `admit`, no `native_decide`, no `unsafe`, no
`@[implemented_by]`.
-/

namespace LnLean.Proofs.Routing.GossipKeyConsistencyTargets

open LnLean.Routing
open LnLean.Routing.GossipProps
open LnLean.Proofs.Routing.GossipTargets
open LnLean.Proofs.Routing.GossipAttributionTargets
open Classical

set_option autoImplicit false

/-! ## 1. Direction-keyed admission transition -/

/-- **Direction-keyed attributed gossip admission.**  Announcement and node
messages reuse the wave-4 `admitGossipAttributed` branches.  A
`channel_update` is admitted only when its abstract signature verifies *and*
its direction-selected signing key is attributed by a stored announcement for
the same channel.  The state effect is the wave-A update effect. -/
noncomputable def admitGossipDirected (verify : SigVerifier)
    (ns : GossipNetwork) : GossipMessage → GossipNetwork
  | .channelAnnouncement a => admitGossipAttributed verify ns (.channelAnnouncement a)
  | .channelUpdate u =>
      if u.signatureValid verify ∧ ns.gossip.updateKeyAnnouncedDirectional u then
        { gossip := applyGossip ns.gossip (.channelUpdate u)
          views := ns.views.map fun v => v.applyUpdate u }
      else ns
  | .nodeAnnouncement n => admitGossipAttributed verify ns (.nodeAnnouncement n)

/-- An announcement step is the wave-4 attributed announcement step. -/
@[simp] theorem admitGossipDirected_announcement (verify : SigVerifier)
    (ns : GossipNetwork) (a : ChannelAnnellation) :
    admitGossipDirected verify ns (.channelAnnouncement a) =
      admitGossipAttributed verify ns (.channelAnnouncement a) :=
  rfl

/-- A node-announcement step is the wave-4 attributed step. -/
@[simp] theorem admitGossipDirected_node (verify : SigVerifier)
    (ns : GossipNetwork) (n : NodeAnnouncement) :
    admitGossipDirected verify ns (.nodeAnnouncement n) =
      admitGossipAttributed verify ns (.nodeAnnouncement n) :=
  rfl

/-- A direction-correct attributed update is admitted with the wave-A update
effect. -/
@[simp] theorem admitGossipDirected_update_of_admitted (verify : SigVerifier)
    (ns : GossipNetwork) (u : ChannelUpdate)
    (hsig : u.signatureValid verify)
    (hk : ns.gossip.updateKeyAnnouncedDirectional u) :
    admitGossipDirected verify ns (.channelUpdate u) =
      { gossip := applyGossip ns.gossip (.channelUpdate u)
        views := ns.views.map fun v => v.applyUpdate u } := by
  simp [admitGossipDirected, hsig, hk]

/-- An update rejected by the directed gate is a no-op. -/
theorem admitGossipDirected_update_of_rejected (verify : SigVerifier)
    (ns : GossipNetwork) (u : ChannelUpdate)
    (h : ¬ (u.signatureValid verify ∧
      ns.gossip.updateKeyAnnouncedDirectional u)) :
    admitGossipDirected verify ns (.channelUpdate u) = ns := by
  simp [admitGossipDirected, h]

/-- A directionally unannounced update is rejected even when its signature
verifies. -/
theorem admitGossipDirected_update_of_unannounced (verify : SigVerifier)
    (ns : GossipNetwork) (u : ChannelUpdate)
    (hk : ¬ ns.gossip.updateKeyAnnouncedDirectional u) :
    admitGossipDirected verify ns (.channelUpdate u) = ns :=
  admitGossipDirected_update_of_rejected verify ns u (fun h => hk h.2)

/-- **Preservation of wave-4 admission.**  When the direction-keyed gate
holds, the directed step is exactly the wave-4 attributed step, because the
directional key set is a subset of the announced key set. -/
theorem admitGossipDirected_update_eq_attributed_of_directional
    (verify : SigVerifier) (ns : GossipNetwork) (u : ChannelUpdate)
    (hsig : u.signatureValid verify)
    (hk : ns.gossip.updateKeyAnnouncedDirectional u) :
    admitGossipDirected verify ns (.channelUpdate u) =
      admitGossipAttributed verify ns (.channelUpdate u) := by
  rw [admitGossipDirected_update_of_admitted verify ns u hsig hk,
    admitGossipAttributed_update_of_attributed verify ns u hsig
      (GossipState.updateKeyAnnouncedDirectional_implies_updateKeyAnnounced
        ns.gossip u hk)]

/-! ## 2. Directed reachability and its invariant -/

/-- Every stored update is signature-valid and direction-correctly
attributed. -/
def StoreUpdatesDirectionallyAttributed (verify : SigVerifier)
    (s : GossipState) : Prop :=
  ∀ u ∈ s.updates, u.signatureValid verify ∧
    s.updateKeyAnnouncedDirectional u

/-- The invariant of directed-reachable states: valid announcement store,
announcement-backed views, and direction-correct update attribution. -/
def DirectedAdmitted (verify : SigVerifier) (ns : GossipNetwork) : Prop :=
  StoreAnnouncementsValid verify ns.gossip ∧ ViewsBacked verify ns ∧
    StoreUpdatesDirectionallyAttributed verify ns.gossip

/-- A state is directed-reachable when it is obtained from the empty network
by a finite sequence of `admitGossipDirected` steps. -/
inductive ReachableDirected (verify : SigVerifier) : GossipNetwork → Prop
  | empty : ReachableDirected verify { gossip := ⟨[], [], []⟩, views := [] }
  | step {ns : GossipNetwork} {m : GossipMessage} :
      ReachableDirected verify ns →
        ReachableDirected verify (admitGossipDirected verify ns m)

/-! ### Preservation lemmas -/

/-- A generic transfer of direction-keyed update attribution along an
unchanged update list and a growing announcement list. -/
theorem storeUpdatesDirectionallyAttributed_mono {verify : SigVerifier}
    {s t : GossipState} (hupd : s.updates = t.updates)
    (hann : ∀ a ∈ s.announcements, a ∈ t.announcements)
    (h : StoreUpdatesDirectionallyAttributed verify s) :
    StoreUpdatesDirectionallyAttributed verify t := by
  intro u hu
  rw [← hupd] at hu
  rcases h u hu with ⟨hsig, hk⟩
  exact ⟨hsig, GossipState.updateKeyAnnouncedDirectional_mono hann hk⟩

/-- An announcement step of `admitGossip` leaves the update list unchanged. -/
theorem admitGossip_announcement_updates_eq (verify : SigVerifier)
    (ns : GossipNetwork) (a : ChannelAnnellation) :
    (admitGossip verify ns (.channelAnnouncement a)).gossip.updates =
      ns.gossip.updates := by
  by_cases h : a.signaturesValid verify
  · rw [admitGossip_announcement_of_valid verify ns a h]
    rfl
  · rw [admitGossip_announcement_of_invalid verify ns a h]

/-- A node-announcement step of `admitGossip` leaves the update list
unchanged. -/
theorem admitGossip_node_updates_eq (verify : SigVerifier)
    (ns : GossipNetwork) (n : NodeAnnouncement) :
    (admitGossip verify ns (.nodeAnnouncement n)).gossip.updates =
      ns.gossip.updates := by
  by_cases h : n.signatureValid verify
  · rw [admitGossip_node_of_valid verify ns n h]
    rfl
  · rw [admitGossip_node_of_invalid verify ns n h]

/-- An announcement step of `admitGossip` only grows the announcement list. -/
theorem admitGossip_announcement_announcements_mono (verify : SigVerifier)
    (ns : GossipNetwork) (a : ChannelAnnellation) :
    ∀ b ∈ ns.gossip.announcements,
      b ∈ (admitGossip verify ns (.channelAnnouncement a)).gossip.announcements := by
  intro b hb
  by_cases h : a.signaturesValid verify
  · rw [admitGossip_announcement_of_valid verify ns a h]
    exact List.mem_cons_of_mem _ hb
  · rw [admitGossip_announcement_of_invalid verify ns a h]
    exact hb

/-- A node-announcement step of `admitGossip` leaves announcements unchanged. -/
theorem admitGossip_node_announcements_mono (verify : SigVerifier)
    (ns : GossipNetwork) (n : NodeAnnouncement) :
    ∀ b ∈ ns.gossip.announcements,
      b ∈ (admitGossip verify ns (.nodeAnnouncement n)).gossip.announcements := by
  intro b hb
  by_cases h : n.signatureValid verify
  · rw [admitGossip_node_of_valid verify ns n h]
    exact hb
  · rw [admitGossip_node_of_invalid verify ns n h]
    exact hb

/-- An announcement step preserves direction-keyed update attribution. -/
theorem admitGossip_announcement_preserves_directional_updates
    (verify : SigVerifier) (ns : GossipNetwork) (a : ChannelAnnellation)
    (h : StoreUpdatesDirectionallyAttributed verify ns.gossip) :
    StoreUpdatesDirectionallyAttributed verify
      (admitGossip verify ns (.channelAnnouncement a)).gossip :=
  storeUpdatesDirectionallyAttributed_mono
    (admitGossip_announcement_updates_eq verify ns a).symm
    (admitGossip_announcement_announcements_mono verify ns a) h

/-- A node-announcement step preserves direction-keyed update attribution. -/
theorem admitGossip_node_preserves_directional_updates
    (verify : SigVerifier) (ns : GossipNetwork) (n : NodeAnnouncement)
    (h : StoreUpdatesDirectionallyAttributed verify ns.gossip) :
    StoreUpdatesDirectionallyAttributed verify
      (admitGossip verify ns (.nodeAnnouncement n)).gossip :=
  storeUpdatesDirectionallyAttributed_mono
    (admitGossip_node_updates_eq verify ns n).symm
    (admitGossip_node_announcements_mono verify ns n) h

/-- **A `channel_update` store step preserves direction-keyed attribution**
when the update itself passes the directed gate.  Old updates keep their
direction-correct witnesses because the announcement list is unchanged. -/
theorem applyGossip_update_preserves_directional_updates
    (verify : SigVerifier) (s : GossipState) (u : ChannelUpdate)
    (h : StoreUpdatesDirectionallyAttributed verify s)
    (hsig : u.signatureValid verify)
    (hk : s.updateKeyAnnouncedDirectional u) :
    StoreUpdatesDirectionallyAttributed verify
      (applyGossip s (.channelUpdate u)) := by
  intro v hv
  have hann : (applyGossip s (.channelUpdate u)).announcements =
      s.announcements := by
    show (s.applyUpdate u).announcements = s.announcements
    exact GossipState.applyUpdate_announcements s u
  have hmono : ∀ b ∈ s.announcements,
      b ∈ (applyGossip s (.channelUpdate u)).announcements := by
    intro b hb
    rw [hann]
    exact hb
  by_cases hnew : s.latestUpdateTimestamp < u.timestamp
  · have hupd : (applyGossip s (.channelUpdate u)).updates =
        u :: s.updates := by
      show (s.applyUpdate u).updates = u :: s.updates
      exact GossipState.applyUpdate_new s u hnew
    rw [hupd] at hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact ⟨hsig, GossipState.updateKeyAnnouncedDirectional_mono hmono hk⟩
    · rcases h v hv with ⟨hvsig, hvk⟩
      exact ⟨hvsig, GossipState.updateKeyAnnouncedDirectional_mono hmono hvk⟩
  · have hsame : (applyGossip s (.channelUpdate u)).updates = s.updates := by
      show (s.applyUpdate u).updates = s.updates
      rw [GossipState.applyUpdate_stale s u (Nat.le_of_not_lt hnew)]
    rw [hsame] at hv
    rcases h v hv with ⟨hvsig, hvk⟩
    exact ⟨hvsig, GossipState.updateKeyAnnouncedDirectional_mono hmono hvk⟩

/-- The full directed step preserves the invariant. -/
theorem admitGossipDirected_preserves (verify : SigVerifier)
    (ns : GossipNetwork) (m : GossipMessage)
    (h : DirectedAdmitted verify ns) :
    DirectedAdmitted verify (admitGossipDirected verify ns m) := by
  rcases h with ⟨hstore, hviews, hupdates⟩
  cases m with
  | channelAnnouncement a =>
      refine ⟨?_, ?_, ?_⟩
      · simpa [admitGossipDirected, admitGossipAttributed_announcement] using
          admitGossip_preserves_store verify ns (.channelAnnouncement a) hstore
      · simpa [admitGossipDirected, admitGossipAttributed_announcement] using
          admitGossip_preserves_views_backed verify ns (.channelAnnouncement a) hviews
      · simpa [admitGossipDirected, admitGossipAttributed_announcement] using
          admitGossip_announcement_preserves_directional_updates verify ns a hupdates
  | channelUpdate u =>
      by_cases hgate : u.signatureValid verify ∧
          ns.gossip.updateKeyAnnouncedDirectional u
      · rw [admitGossipDirected_update_of_admitted verify ns u hgate.1 hgate.2]
        exact ⟨attributed_update_preserves_store verify ns u hstore,
          attributed_update_preserves_views_backed verify ns u hviews,
          applyGossip_update_preserves_directional_updates verify ns.gossip u
            hupdates hgate.1 hgate.2⟩
      · rw [admitGossipDirected_update_of_rejected verify ns u hgate]
        exact ⟨hstore, hviews, hupdates⟩
  | nodeAnnouncement n =>
      refine ⟨?_, ?_, ?_⟩
      · simpa [admitGossipDirected, admitGossipAttributed_node] using
          admitGossip_preserves_store verify ns (.nodeAnnouncement n) hstore
      · simpa [admitGossipDirected, admitGossipAttributed_node] using
          admitGossip_preserves_views_backed verify ns (.nodeAnnouncement n) hviews
      · simpa [admitGossipDirected, admitGossipAttributed_node] using
          admitGossip_node_preserves_directional_updates verify ns n hupdates

/-- **The invariant of every directed-reachable state.** -/
theorem reachableDirected_invariant {verify : SigVerifier}
    {ns : GossipNetwork} (h : ReachableDirected verify ns) :
    DirectedAdmitted verify ns := by
  induction h with
  | empty =>
      refine ⟨?_, ?_, ?_⟩
      · intro a ha
        simp at ha
      · intro v hv
        simp at hv
      · intro u hu
        simp at hu
  | step _ ih =>
      exact admitGossipDirected_preserves verify _ _ ih

/-- Directed-reachable stores contain only verifying announcements. -/
theorem reachableDirected_store_valid {verify : SigVerifier}
    {ns : GossipNetwork} (h : ReachableDirected verify ns) :
    StoreAnnouncementsValid verify ns.gossip :=
  (reachableDirected_invariant h).1

/-- Directed-reachable views are announcement-backed. -/
theorem reachableDirected_views_backed {verify : SigVerifier}
    {ns : GossipNetwork} (h : ReachableDirected verify ns) :
    ViewsBacked verify ns :=
  (reachableDirected_invariant h).2.1

/-- Every stored update of a directed-reachable state is signature-valid and
direction-correctly attributed. -/
theorem reachableDirected_updates_directional {verify : SigVerifier}
    {ns : GossipNetwork} (h : ReachableDirected verify ns) :
    StoreUpdatesDirectionallyAttributed verify ns.gossip :=
  (reachableDirected_invariant h).2.2

/-- The wave-4 (undirected) attribution statement also holds for directed
reachability. -/
theorem reachableDirected_updates_attributed {verify : SigVerifier}
    {ns : GossipNetwork} (h : ReachableDirected verify ns) :
    StoreUpdatesAttributed verify ns.gossip := by
  intro u hu
  rcases reachableDirected_updates_directional h u hu with ⟨hsig, hk⟩
  exact ⟨hsig,
    GossipState.updateKeyAnnouncedDirectional_implies_updateKeyAnnounced
      ns.gossip u hk⟩

/-! ## 3. Direction key elimination and uniqueness -/

/-- A direction-correct attribution determines the update's signing key as
the selected announcement field. -/
theorem attributesKeyForDirection_key {a : ChannelAnnellation} {direction : Bool}
    {key : PubKey} (h : a.attributesKeyForDirection direction key) :
    key = (if direction then a.nodeKey2 else a.nodeKey1) := by
  by_cases hd : direction
  · rw [ChannelAnnellation.attributesKeyForDirection, ite_eq_left hd] at h
    simp [hd, h]
  · rw [ChannelAnnellation.attributesKeyForDirection, ite_eq_right hd] at h
    simp [hd, h]

/-- **No ambiguous attribution under the canonical invariant.**  If two
updates for the same channel and the same direction are both
direction-correctly attributed in a canonical store, their signing keys are
equal.  In particular, two announcement witnesses for one update cannot
disagree. -/
theorem canonical_directional_attribution_unique {s : GossipState}
    (hcanon : CanonicalAnnouncements s.announcements)
    {u v : ChannelUpdate} (hscid : u.shortChannelId = v.shortChannelId)
    (hdir : u.direction = v.direction)
    (hu : s.updateKeyAnnouncedDirectional u)
    (hv : s.updateKeyAnnouncedDirectional v) :
    u.signingKey = v.signingKey := by
  rcases hu with ⟨a, ha, hascid, hakey⟩
  rcases hv with ⟨b, hb, hbscid, hbkey⟩
  have hsame : a.shortChannelId = b.shortChannelId :=
    hascid.trans (hscid.trans hbscid.symm)
  have hab : a = b := hcanon a ha b hb hsame
  rw [hab] at hakey
  have h1 : u.signingKey =
      (if u.direction then b.nodeKey2 else b.nodeKey1) :=
    attributesKeyForDirection_key hakey
  have h2 : v.signingKey =
      (if v.direction then b.nodeKey2 else b.nodeKey1) :=
    attributesKeyForDirection_key hbkey
  rw [← hdir] at h2
  exact h1.trans h2.symm

/-- **Canonical announcements refine the wave-4 consistency hypothesis.**
The deduplicating invariant implies `AttributionConsistent`, so the wave-4
endpoint theorem can be instantiated from the canonical view. -/
theorem canonical_attributionConsistent {s : GossipState}
    (h : CanonicalAnnouncements s.announcements) :
    AttributionConsistent s := by
  intro a ha b hb hscid
  have hab : a = b := h a ha b hb hscid
  rw [hab]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- **Deduplicated canonical view cannot be ambiguous.**  The canonical view
always satisfies the canonical invariant, so directional attribution in the
view is unique without any hypothesis on the raw store. -/
theorem canonicalView_directional_attribution_unique (s : GossipState)
    {u v : ChannelUpdate} (hscid : u.shortChannelId = v.shortChannelId)
    (hdir : u.direction = v.direction)
    (hu : s.canonicalView.updateKeyAnnouncedDirectional u)
    (hv : s.canonicalView.updateKeyAnnouncedDirectional v) :
    u.signingKey = v.signingKey :=
  canonical_directional_attribution_unique
    (canonical_dedupAnnouncements s.announcements) hscid hdir hu hv

/-! ## 4. Endpoint key for reachable directed graph edges -/

/-- **The right endpoint key.**  In every directed-reachable state, under the
explicit `NodeId → PubKey` consistency invariant `NodeKeyConsistent` and the
canonical-announcement invariant, every stored update for a graph edge has a
verifying signature and is signed by exactly the endpoint selected by its
BOLT 7 direction:

* direction 0 (`false`, `node_1 → node_2`) is signed by `nodeKeyOf e.node1`;
* direction 1 (`true`, `node_2 → node_1`) is signed by `nodeKeyOf e.node2`.

No undirected alternative remains: the theorem says *the* selected endpoint
key, not merely one of the two. -/
theorem gossip_graph_edges_directional_key_endpoint
    (verify : SigVerifier) (ns : GossipNetwork) (nodeKeyOf : NodeId → PubKey)
    (h : ReachableDirected verify ns)
    (hcanon : CanonicalAnnouncements ns.gossip.announcements)
    (hnode : GossipState.NodeKeyConsistent nodeKeyOf ns.gossip) :
    ∀ e ∈ ns.graph.edges, ∀ u ∈ ns.gossip.updates,
      u.shortChannelId = e.shortChannelId →
        u.signatureValid verify ∧
          u.signingKey =
            (if u.direction then nodeKeyOf e.node2 else nodeKeyOf e.node1) := by
  intro e he u hu hscid
  have he' : e ∈ ns.views.map ChannelView.edge := he
  rcases List.mem_map.mp he' with ⟨v, hv, rfl⟩
  rcases reachableDirected_views_backed h v hv with
    ⟨b, hb, _hbsig, hbscid, hb1, hb2, _hbcap⟩
  rcases reachableDirected_updates_directional h u hu with ⟨husig, hk⟩
  rcases hk with ⟨a, ha, hascid, hakey⟩
  have hsame : a.shortChannelId = b.shortChannelId := by
    rw [hascid, hscid, ChannelView.edge_scid, hbscid]
  have hab : a = b := hcanon a ha b hb hsame
  rw [hab] at hakey
  have hkey : u.signingKey =
      (if u.direction then b.nodeKey2 else b.nodeKey1) :=
    attributesKeyForDirection_key hakey
  have hn := hnode b hb
  refine ⟨husig, ?_⟩
  rw [hkey]
  by_cases hdir : u.direction
  · rw [ite_eq_left hdir, ite_eq_left hdir]
    have hb2' : (v.edge).node2 = b.node2 := by
      simpa [ChannelView.edge] using hb2
    rw [hb2']
    exact hn.2.symm
  · rw [ite_eq_right hdir, ite_eq_right hdir]
    have hb1' : (v.edge).node1 = b.node1 := by
      simpa [ChannelView.edge] using hb1
    rw [hb1']
    exact hn.1.symm

/-- The edge-backing half remains available: every edge of a directed-reachable
state is backed by a valid stored announcement with exact endpoints and
capacity. -/
theorem directed_graph_edges_backed (verify : SigVerifier)
    (ns : GossipNetwork) (h : ReachableDirected verify ns) :
    ∀ e ∈ ns.graph.edges, ∃ a ∈ ns.gossip.announcements,
      announcementValid verify a ∧ e.shortChannelId = a.shortChannelId ∧
        e.node1 = a.node1 ∧ e.node2 = a.node2 ∧
          e.capacitySat = a.capacitySat := by
  intro e he
  have he' : e ∈ ns.views.map ChannelView.edge := he
  rcases List.mem_map.mp he' with ⟨v, hv, rfl⟩
  rcases reachableDirected_views_backed h v hv with
    ⟨a, ha, hsig, hscid, h1, h2, hcap⟩
  exact ⟨a, ha, hsig, hscid, h1, h2, hcap⟩

/-! ## 5. Concrete witnesses and counterexamples -/

private def acceptingVerifier : SigVerifier := fun _ _ _ => true

private def keyA : PubKey := ⟨ByteArray.mk #[1]⟩

private def keyB : PubKey := ⟨ByteArray.empty⟩

private def node0 : NodeId := ⟨0⟩

private def node1 : NodeId := ⟨1⟩

private def sampleScid : ShortChannelId := ⟨1, 2, 3⟩

private def emptySig : GossipSignature := ⟨ByteArray.empty⟩

private def emptyStore : GossipState := ⟨[], [], []⟩

private def emptyNetwork : GossipNetwork := { gossip := emptyStore, views := [] }

private def mkAnn (capacity : Nat) (k1 k2 : PubKey) : ChannelAnnellation :=
  { shortChannelId := sampleScid
    node1 := node0
    node2 := node1
    nodeKey1 := k1
    nodeKey2 := k2
    bitcoinKey1 := k1
    bitcoinKey2 := k2
    capacitySat := capacity
    digest := ByteArray.empty
    nodeSignature1 := emptySig
    nodeSignature2 := emptySig
    bitcoinSignature1 := emptySig
    bitcoinSignature2 := emptySig }

/-- Direction-0 announcement (signer `nodeKey1`). -/
private def annA : ChannelAnnellation := mkAnn 1000 keyA keyB

/-- A conflicting same-channel announcement whose first key is `keyB`. -/
private def annB : ChannelAnnellation := mkAnn 2000 keyB keyA

private def mkUpdate (flags : Nat) (k : PubKey) : ChannelUpdate :=
  { shortChannelId := sampleScid
    timestamp := 1
    messageFlags := 0
    channelFlags := flags
    cltvDelta := 1
    htlcMinimumMsat := Msat.zero
    feeBaseMsat := Msat.zero
    feeProportionalMillionths := 0
    htlcMaximumMsat := Msat.MAX
    signingKey := k
    digest := ByteArray.empty
    signature := emptySig }

private def updateDir0 (k : PubKey) : ChannelUpdate := mkUpdate 0 k

private theorem keyA_ne_keyB : keyA ≠ keyB := by
  intro h
  have hb := congrArg PubKey.bytes h
  have hs := congrArg ByteArray.size hb
  have h1 : keyA.bytes.size = 1 := by decide
  have h2 : keyB.bytes.size = 0 := rfl
  rw [h1, h2] at hs
  exact Nat.noConfusion hs

private theorem annA_valid :
    annA.signaturesValid acceptingVerifier := by
  simp [ChannelAnnellation.signaturesValid, signatureValid, acceptingVerifier]

private theorem annA_ne_annB : annA ≠ annB := by
  intro h
  have hc := congrArg ChannelAnnellation.capacitySat h
  simp [annA, annB, mkAnn] at hc

private theorem direction_dir0 (k : PubKey) :
    (updateDir0 k).direction = false := by
  rw [ChannelUpdate.direction_eq_false_iff]
  rfl

private theorem dir0_at_annA :
    annA.attributesKeyForDirection (updateDir0 keyA).direction
      (updateDir0 keyA).signingKey := by
  rw [direction_dir0]
  simp [ChannelAnnellation.attributesKeyForDirection, annA, mkAnn, updateDir0,
    mkUpdate]

private theorem dir0_at_annB :
    annB.attributesKeyForDirection (updateDir0 keyB).direction
      (updateDir0 keyB).signingKey := by
  rw [direction_dir0]
  simp [ChannelAnnellation.attributesKeyForDirection, annB, mkAnn, updateDir0,
    mkUpdate]

/-- The conflicting store: two distinct announcements for one channel. -/
private def conflictStore : GossipState := ⟨[annA, annB], [], []⟩

private theorem conflictStore_not_canonical :
    ¬ CanonicalAnnouncements conflictStore.announcements := by
  intro hc
  have ha : annA ∈ conflictStore.announcements := by simp [conflictStore]
  have hb : annB ∈ conflictStore.announcements := by simp [conflictStore]
  exact annA_ne_annB (hc annA ha annB hb rfl)

private theorem conflictStore_dirA :
    conflictStore.updateKeyAnnouncedDirectional (updateDir0 keyA) := by
  refine GossipState.updateKeyAnnouncedDirectional_of_mem (a := annA) ?_ rfl ?_
  · simp [conflictStore]
  · exact dir0_at_annA

private theorem conflictStore_dirB :
    conflictStore.updateKeyAnnouncedDirectional (updateDir0 keyB) := by
  refine GossipState.updateKeyAnnouncedDirectional_of_mem (a := annB) ?_ rfl ?_
  · simp [conflictStore]
  · exact dir0_at_annB

/-- **Conflicting announcements are ambiguous without the invariant.**  Two
same-`short_channel_id` announcements with swapped node keys attribute
different direction-0 signing keys.  This is exactly why
`canonical_directional_attribution_unique` needs `CanonicalAnnouncements`;
the raw append-only store does not provide it. -/
theorem conflicting_announcements_ambiguous_without_canonical :
    ∃ (s : GossipState) (u v : ChannelUpdate),
      ¬ CanonicalAnnouncements s.announcements ∧
        u.shortChannelId = v.shortChannelId ∧ u.direction = v.direction ∧
          s.updateKeyAnnouncedDirectional u ∧
            s.updateKeyAnnouncedDirectional v ∧ u.signingKey ≠ v.signingKey := by
  refine ⟨conflictStore, updateDir0 keyA, updateDir0 keyB,
    conflictStore_not_canonical, rfl, ?_, conflictStore_dirA,
    conflictStore_dirB, keyA_ne_keyB⟩
  rw [direction_dir0, direction_dir0]

/-- **The direction gate is strictly stronger than wave-4 attribution.**  In a
store holding only `annA`, an update with `channel_flags = 0` signed by
`nodeKey2` is undirected-attributed (the key is announced) but not
direction-correct (direction 0 requires `nodeKey1`). -/
theorem general_attribution_not_directional :
    ∃ (s : GossipState) (u : ChannelUpdate),
      s.updateKeyAnnounced u ∧ ¬ s.updateKeyAnnouncedDirectional u := by
  refine ⟨⟨[annA], [], []⟩, updateDir0 keyB, ?_, ?_⟩
  · refine GossipState.updateKeyAnnounced_of_mem (a := annA) ?_ rfl ?_
    · simp
    · exact Or.inr rfl
  · rintro ⟨a, ha, _hscid, hkey⟩
    simp at ha
    subst a
    rw [direction_dir0] at hkey
    rw [ChannelAnnellation.attributesKeyForDirection] at hkey
    simp [annA, mkAnn] at hkey
    exact keyA_ne_keyB hkey

/-! ### Non-vacuity of directed reachability -/

private noncomputable def announcedNetwork : GossipNetwork :=
  admitGossipAttributed acceptingVerifier emptyNetwork
    (.channelAnnouncement annA)

private noncomputable def directedNetwork : GossipNetwork :=
  admitGossipDirected acceptingVerifier announcedNetwork
    (.channelUpdate (updateDir0 keyA))

private theorem announcedNetwork_gossip :
    announcedNetwork.gossip =
      applyGossip emptyStore (.channelAnnouncement annA) := by
  unfold announcedNetwork
  rw [admitGossipAttributed_announcement]
  rw [admitGossip_announcement_of_valid acceptingVerifier emptyNetwork annA
    annA_valid]
  rfl

private theorem dir0_announced :
    announcedNetwork.gossip.updateKeyAnnouncedDirectional (updateDir0 keyA) := by
  rw [announcedNetwork_gossip]
  refine GossipState.updateKeyAnnouncedDirectional_of_mem (a := annA) ?_ rfl
    dir0_at_annA
  simp [applyGossip]

private theorem updateDir0_valid :
    (updateDir0 keyA).signatureValid acceptingVerifier := by
  simp [ChannelUpdate.signatureValid, signatureValid, acceptingVerifier]

private theorem updateDir0_mem_directedNetwork :
    updateDir0 keyA ∈ directedNetwork.gossip.updates := by
  unfold directedNetwork
  rw [admitGossipDirected_update_of_admitted acceptingVerifier announcedNetwork
    (updateDir0 keyA) updateDir0_valid dir0_announced]
  show updateDir0 keyA ∈
    (announcedNetwork.gossip.applyUpdate (updateDir0 keyA)).updates
  rw [GossipState.applyUpdate_new]
  · exact List.mem_cons_self ..
  · rw [announcedNetwork_gossip]
    simp [applyGossip, GossipState.latestUpdateTimestamp, latestTimestamp,
      emptyStore, updateDir0, mkUpdate]

private theorem directedNetwork_reachable :
    ReachableDirected acceptingVerifier directedNetwork := by
  unfold directedNetwork announcedNetwork
  exact ReachableDirected.step (m := .channelUpdate (updateDir0 keyA))
    (ReachableDirected.step (m := .channelAnnouncement annA)
      ReachableDirected.empty)

private theorem directedNetwork_announcements :
    directedNetwork.gossip.announcements = [annA] := by
  unfold directedNetwork
  rw [admitGossipDirected_update_of_admitted acceptingVerifier announcedNetwork
    (updateDir0 keyA) updateDir0_valid dir0_announced]
  show (announcedNetwork.gossip.applyUpdate (updateDir0 keyA)).announcements = [annA]
  rw [GossipState.applyUpdate_announcements, announcedNetwork_gossip]
  simp [applyGossip, emptyStore]

private def sampleNodeKeyOf : NodeId → PubKey := fun n =>
  if n = node0 then keyA else keyB

private theorem directedNetwork_canonical :
    CanonicalAnnouncements directedNetwork.gossip.announcements := by
  intro a ha b hb _hscid
  rw [directedNetwork_announcements] at ha hb
  simp at ha hb
  rw [ha, hb]

private theorem directedNetwork_nodeKeyConsistent :
    GossipState.NodeKeyConsistent sampleNodeKeyOf directedNetwork.gossip := by
  intro a ha
  rw [directedNetwork_announcements] at ha
  simp at ha
  subst a
  constructor
  · simp [annA, mkAnn, node0, sampleNodeKeyOf]
  · simp [annA, mkAnn, node0, node1, sampleNodeKeyOf]

private theorem directedNetwork_graph_nonempty :
    directedNetwork.graph.edges ≠ [] := by
  unfold directedNetwork
  rw [admitGossipDirected_update_of_admitted acceptingVerifier announcedNetwork
    (updateDir0 keyA) updateDir0_valid dir0_announced]
  have hv : admittedChannelView annA ∈ announcedNetwork.views := by
    unfold announcedNetwork
    rw [admitGossipAttributed_announcement,
      admitGossip_announcement_of_valid acceptingVerifier emptyNetwork annA
        annA_valid]
    simp
  intro hnil
  unfold GossipNetwork.graph viewGraph at hnil
  dsimp only at hnil
  have hmem : ((admittedChannelView annA).applyUpdate (updateDir0 keyA)).edge ∈
      (announcedNetwork.views.map fun v =>
        v.applyUpdate (updateDir0 keyA)).map ChannelView.edge :=
    List.mem_map.mpr
      ⟨_, List.mem_map.mpr ⟨_, hv, rfl⟩, rfl⟩
  rw [hnil] at hmem
  simp at hmem

/-- **Non-vacuity of the directed gate.**  There is a directed-reachable
state storing a signature-valid, direction-correct update. -/
theorem reachableDirected_stores_directional_update :
    ∃ (verify : SigVerifier) (ns : GossipNetwork) (u : ChannelUpdate),
      ReachableDirected verify ns ∧ u ∈ ns.gossip.updates ∧
        u.signatureValid verify ∧ ns.gossip.updateKeyAnnouncedDirectional u := by
  refine ⟨acceptingVerifier, directedNetwork, updateDir0 keyA,
    directedNetwork_reachable, updateDir0_mem_directedNetwork,
    updateDir0_valid, ?_⟩
  exact (reachableDirected_updates_directional directedNetwork_reachable
    (updateDir0 keyA) updateDir0_mem_directedNetwork).2

/-- **Non-vacuity of the endpoint theorem.**  The concrete directed-reachable
state has a non-empty graph, a canonical announcement store, a consistent
`NodeId → PubKey` map, and satisfies the directional endpoint statement. -/
theorem reachableDirected_directional_endpoint_witness :
    ∃ (verify : SigVerifier) (ns : GossipNetwork)
      (nodeKeyOf : NodeId → PubKey),
      ReachableDirected verify ns ∧ ns.graph.edges ≠ [] ∧
        CanonicalAnnouncements ns.gossip.announcements ∧
          GossipState.NodeKeyConsistent nodeKeyOf ns.gossip ∧
            ∀ e ∈ ns.graph.edges, ∀ u ∈ ns.gossip.updates,
              u.shortChannelId = e.shortChannelId →
                u.signatureValid verify ∧
                  u.signingKey =
                    (if u.direction then nodeKeyOf e.node2
                      else nodeKeyOf e.node1) := by
  refine ⟨acceptingVerifier, directedNetwork, sampleNodeKeyOf,
    directedNetwork_reachable, directedNetwork_graph_nonempty,
    directedNetwork_canonical, directedNetwork_nodeKeyConsistent, ?_⟩
  exact gossip_graph_edges_directional_key_endpoint acceptingVerifier
    directedNetwork sampleNodeKeyOf directedNetwork_reachable
    directedNetwork_canonical directedNetwork_nodeKeyConsistent

/-! ### The raw store is still unfiltered and undeduplicated -/

/-- **Raw `applyGossip` still accepts a directionally unattributed update.**
This is the wave-A raw-store caveat in direction-keyed form: the directed gate
rejects the update, while raw insertion stores it. -/
theorem raw_applyGossip_accepts_directionally_unattributed_update :
    ∃ (s : GossipState) (u : ChannelUpdate),
      ¬ s.updateKeyAnnouncedDirectional u ∧
        (applyGossip s (.channelUpdate u)).updates = u :: s.updates := by
  refine ⟨emptyStore, updateDir0 keyB, ?_, ?_⟩
  · rintro ⟨a, ha, _⟩
    simp [emptyStore] at ha
  · show (emptyStore.applyUpdate (updateDir0 keyB)).updates =
      updateDir0 keyB :: emptyStore.updates
    rw [GossipState.applyUpdate_new]
    simp [GossipState.latestUpdateTimestamp, latestTimestamp, emptyStore,
      updateDir0, mkUpdate]

/-- **Raw `applyGossip` still accepts a conflicting announcement.**  The raw
store remains append-only, so the canonical invariant is not an invariant of
`applyGossip`; it is a property of the explicit view/transition. -/
theorem raw_applyGossip_accepts_conflicting_announcement :
    ∃ (s : GossipState) (a : ChannelAnnellation),
      ¬ CanonicalAnnouncements
        (applyGossip s (.channelAnnouncement a)).announcements := by
  refine ⟨⟨[annB], [], []⟩, annA, ?_⟩
  intro hc
  have ha : annA ∈ (applyGossip ⟨[annB], [], []⟩
      (.channelAnnouncement annA)).announcements := by simp [applyGossip]
  have hb : annB ∈ (applyGossip ⟨[annB], [], []⟩
      (.channelAnnouncement annA)).announcements := by simp [applyGossip]
  exact annA_ne_annB (hc annA ha annB hb rfl)

end LnLean.Proofs.Routing.GossipKeyConsistencyTargets
