import LnLean.Proofs.Routing.GossipKeyConsistencyTargets

/-!
# LnLean.Proofs.Routing.GossipCanonicalTargets

Wave-6 lane `S6-GOSSIP-DERIVE`, open issues `RT-02` / `RT-01`.

Wave 5 (`GossipKeyConsistencyTargets`) proved direction-keyed attribution only
under two *explicit* hypotheses:

* `GossipState.NodeKeyConsistent nodeKeyOf` — an external `NodeId → PubKey`
  map agrees with every stored announcement;
* `CanonicalAnnouncements s.announcements` — at most one stored announcement
  per `short_channel_id`.

The raw store (`applyGossip`, `GossipState.applyUpdate`, the wave-4/5
attributed transitions) neither maintains the map nor deduplicates, so those
hypotheses were not derived from reachability.  This module closes that gap
with a **canonicalising admission transition**:

* `admitGossipCanonical` carries an explicit node-key registration map
  (`CanonicalNetwork.nodeKeyOf`) and a view list.
* A `channel_announcement` is admitted only if all four signatures verify, its
  endpoints are distinct, it is compatible with the existing node-key
  registrations (`GossipState.CompatibleWithStore`), and it still authorises
  every stored update for its channel (`UpdatesAuthorizedBy`).  On admission
  the announcement **replaces** the record for its `short_channel_id`
  (`insertReplacing`), its two nodes are registered (`bindNodeKeys`), and the
  view for that channel is replaced (`insertViewCanonical`).
* A `channel_update` is admitted only if its signature verifies, its
  direction-selected key is announced, and it is strictly newer than every
  stored update in its `(short_channel_id, direction)` slot
  (`UpdateSupersedes`).  It **replaces** the slot (`insertUpdateCanonical`)
  instead of appending.
* A `node_announcement` is the usual signature-gated append.

The reachability predicate `ReachableCanonical` closes this transition.  The
invariant `CanonicalAdmitted` is proved for every reachable state, and its
components are projected as:

* `reachableCanonical_nodeKeyConsistent` — `NodeKeyConsistent` is **derived**,
  not assumed;
* `reachableCanonical_canonical` — `CanonicalAnnouncements` is **derived**;
* `reachableCanonical_directional_key_endpoint` — the wave-5 endpoint theorem
  now holds with **no** `NodeKeyConsistent` or `CanonicalAnnouncements`
  hypotheses;
* `reachableCanonical_attribution_unique` — same-channel, same-direction
  stored updates have the same signing key, again without extra hypotheses.

Modelled supersession and rotation:

* `reachableCanonical_supersession_witness` exhibits a reachable state where a
  newer update in the same directional slot replaced the older one.
* `key_rotation_preserves_registration_invariants` proves that an explicit
  rotation of a registered node key preserves `NodeKeyConsistent` **and**
  canonicality when all announcements are rekeyed with it.
* `rotation_breaks_update_attribution` is the matching boundary witness:
  rotation changes the direction key without re-signing the stored update, so
  update attribution is *not* preserved.  Re-signing/resubmission is an
  explicit obligation, not a hidden theorem.

Preserved unchanged and re-exhibited: raw `applyGossip` is still append-only,
so the wave-4/5 counterexamples
(`raw_applyGossip_accepts_conflicting_announcement`,
`conflicting_announcements_ambiguous_without_canonical`,
`raw_applyGossip_accepts_directionally_unattributed_update`) still hold.  The
canonical transition's rejection of the conflicting announcement is proved
next to them.

What is **not** modelled or claimed:

* `SigVerifier` is still abstract; signature validity is
  `verify key digest sig = true`, and unforgeability is assumption C3/C4/C8.
* `CompatibleWithStore` is a node-key *registration* policy.  It forbids
  rebinding a node to a different key without an explicit rotation step; it
  does not model a timestamp/epoch, gossip dissemination, or re-signing.
* Announcement replacement can discard an old announcement record.  Stored
  updates for that channel are admitted only when the replacement still
  authorises them; otherwise the caller must drop/resubmit them.  This module
  does not model update resubmission.
* The view list is canonicalised by `short_channel_id`, but the model still
  does not build per-direction (two-view) channel records.
* No network, liveness, chain-hash, UTXO, or rate-limit claim.

No `sorry`, no `axiom`, no `admit`, no `native_decide`, no `unsafe`, no
`@[implemented_by]`.
-/

namespace LnLean.Proofs.Routing.GossipCanonicalTargets

open LnLean.Routing
open LnLean.Routing.GossipProps
open LnLean.Proofs.Routing.GossipTargets
open LnLean.Proofs.Routing.GossipKeyConsistencyTargets
open Classical

set_option autoImplicit false

/-! ## 1. Canonical network state and admission transition -/

/-- **The incoming announcement still authorises stored updates.**  Every
stored update for the incoming `short_channel_id` must be direction-correctly
attributed by the incoming announcement.  This is the condition that lets a
replacement announcement discard the old record without silently orphaning
stored updates. -/
def UpdatesAuthorizedBy (s : GossipState) (a : ChannelAnnellation) : Prop :=
  ∀ u ∈ s.updates, u.shortChannelId = a.shortChannelId →
    a.attributesKeyForDirection u.direction u.signingKey

/-- Replace the routing view for the incoming `short_channel_id`.  This mirrors
announcement replacement on the materialised view list. -/
def insertViewCanonical (v : ChannelView) (vs : List ChannelView) :
    List ChannelView :=
  v :: vs.filter (fun w => decide (w.scid ≠ v.scid))

/-- Exact membership after view replacement. -/
theorem mem_insertViewCanonical_iff {v w : ChannelView}
    {vs : List ChannelView} :
    w ∈ insertViewCanonical v vs ↔ w = v ∨ (w ∈ vs ∧ w.scid ≠ v.scid) := by
  simp [insertViewCanonical, List.mem_filter]

/-- A stored view for a different channel survives replacement. -/
theorem mem_insertViewCanonical_of_mem_of_ne {v w : ChannelView}
    {vs : List ChannelView} (hw : w ∈ vs) (hne : w.scid ≠ v.scid) :
    w ∈ insertViewCanonical v vs :=
  List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hw, decide_eq_true hne⟩)

/-- A canonical network state: the raw gossip store, its materialised views,
and the explicit graph-node to BOLT 7 key registration map. -/
structure CanonicalNetwork where
  /-- The wave-A gossip store (announcements, updates, node announcements). -/
  gossip : GossipState
  /-- Materialised routing views, exactly as in `GossipNetwork`. -/
  views : List ChannelView
  /-- The explicit node-key registration map that wave A did not have. -/
  nodeKeyOf : NodeId → PubKey

namespace CanonicalNetwork

/-- Forget the registration map, recovering the wave-A/5 network state. -/
def toNetwork (cs : CanonicalNetwork) : GossipNetwork :=
  { gossip := cs.gossip, views := cs.views }

/-- The routing graph of the projected network. -/
def graph (cs : CanonicalNetwork) : Graph :=
  cs.toNetwork.graph

end CanonicalNetwork

/-- **Canonicalising gossip admission.**  This is the `RT-02` transition.

* `channel_announcement`: signature-gated, endpoint-distinct,
  registration-compatible, update-authorising; it replaces the channel's
  announcement and view and registers both endpoint keys.
* `channel_update`: signature-gated, direction-attributed, strictly newer in
  its `(short_channel_id, direction)` slot; it replaces that slot.
* `node_announcement`: the usual signature-gated append.

The definition is `noncomputable` only because the registration gate compares
public keys (`Classical.propDecidable`); it is still a deterministic function
of the message and state. -/
noncomputable def admitGossipCanonical (verify : SigVerifier)
    (cs : CanonicalNetwork) : GossipMessage → CanonicalNetwork
  | .channelAnnouncement a =>
      if a.signaturesValid verify ∧ a.node1 ≠ a.node2 ∧
          cs.gossip.CompatibleWithStore a ∧
          UpdatesAuthorizedBy cs.gossip a then
        { gossip := { cs.gossip with
            announcements := insertReplacing a cs.gossip.announcements }
          views := insertViewCanonical (admittedChannelView a) cs.views
          nodeKeyOf := bindNodeKeys cs.nodeKeyOf a }
      else cs
  | .channelUpdate u =>
      if u.signatureValid verify ∧
          cs.gossip.updateKeyAnnouncedDirectional u ∧
          UpdateSupersedes u cs.gossip.updates then
        { gossip := { cs.gossip with
            updates := insertUpdateCanonical u cs.gossip.updates }
          views := cs.views.map fun v => v.applyUpdate u
          nodeKeyOf := cs.nodeKeyOf }
      else cs
  | .nodeAnnouncement n =>
      if n.signatureValid verify then
        { gossip := { cs.gossip with
            nodeAnnouncements := n :: cs.gossip.nodeAnnouncements }
          views := cs.views
          nodeKeyOf := cs.nodeKeyOf }
      else cs

/-! ## 2. Transition equations -/

/-- An announcement passing every canonical gate is admitted with replacement
semantics. -/
theorem admitGossipCanonical_announcement_of_admitted (verify : SigVerifier)
    (cs : CanonicalNetwork) (a : ChannelAnnellation)
    (h : a.signaturesValid verify ∧ a.node1 ≠ a.node2 ∧
      cs.gossip.CompatibleWithStore a ∧
      UpdatesAuthorizedBy cs.gossip a) :
    admitGossipCanonical verify cs (.channelAnnouncement a) =
      { gossip := { cs.gossip with
          announcements := insertReplacing a cs.gossip.announcements }
        views := insertViewCanonical (admittedChannelView a) cs.views
        nodeKeyOf := bindNodeKeys cs.nodeKeyOf a } := by
  simp [admitGossipCanonical, h]

/-- An announcement failing any canonical gate is a no-op. -/
theorem admitGossipCanonical_announcement_of_rejected (verify : SigVerifier)
    (cs : CanonicalNetwork) (a : ChannelAnnellation)
    (h : ¬ (a.signaturesValid verify ∧ a.node1 ≠ a.node2 ∧
      cs.gossip.CompatibleWithStore a ∧
      UpdatesAuthorizedBy cs.gossip a)) :
    admitGossipCanonical verify cs (.channelAnnouncement a) = cs := by
  simp [admitGossipCanonical, h]

/-- An update passing every canonical gate is admitted with slot replacement
semantics. -/
theorem admitGossipCanonical_update_of_admitted (verify : SigVerifier)
    (cs : CanonicalNetwork) (u : ChannelUpdate)
    (h : u.signatureValid verify ∧
      cs.gossip.updateKeyAnnouncedDirectional u ∧
      UpdateSupersedes u cs.gossip.updates) :
    admitGossipCanonical verify cs (.channelUpdate u) =
      { gossip := { cs.gossip with
          updates := insertUpdateCanonical u cs.gossip.updates }
        views := cs.views.map fun v => v.applyUpdate u
        nodeKeyOf := cs.nodeKeyOf } := by
  simp [admitGossipCanonical, h]

/-- An update failing any canonical gate is a no-op. -/
theorem admitGossipCanonical_update_of_rejected (verify : SigVerifier)
    (cs : CanonicalNetwork) (u : ChannelUpdate)
    (h : ¬ (u.signatureValid verify ∧
      cs.gossip.updateKeyAnnouncedDirectional u ∧
      UpdateSupersedes u cs.gossip.updates)) :
    admitGossipCanonical verify cs (.channelUpdate u) = cs := by
  simp [admitGossipCanonical, h]

/-- A verifying node announcement is appended. -/
theorem admitGossipCanonical_node_of_valid (verify : SigVerifier)
    (cs : CanonicalNetwork) (n : NodeAnnouncement)
    (h : n.signatureValid verify) :
    admitGossipCanonical verify cs (.nodeAnnouncement n) =
      { gossip := { cs.gossip with
          nodeAnnouncements := n :: cs.gossip.nodeAnnouncements }
        views := cs.views
        nodeKeyOf := cs.nodeKeyOf } := by
  simp [admitGossipCanonical, h]

/-- A node announcement failing the signature gate is a no-op. -/
theorem admitGossipCanonical_node_of_invalid (verify : SigVerifier)
    (cs : CanonicalNetwork) (n : NodeAnnouncement)
    (h : ¬ n.signatureValid verify) :
    admitGossipCanonical verify cs (.nodeAnnouncement n) = cs := by
  simp [admitGossipCanonical, h]

/-! ## 3. The reachable invariant -/

/-- Every component of the canonical store invariant. -/
structure CanonicalAdmitted (verify : SigVerifier) (cs : CanonicalNetwork) :
    Prop where
  /-- Every stored announcement passes all four BOLT 7 signature checks. -/
  storeValid : StoreAnnouncementsValid verify cs.gossip
  /-- Every materialised view is backed by a stored announcement. -/
  viewsBacked : ViewsBacked verify cs.toNetwork
  /-- Every stored update verifies and is direction-correctly attributed. -/
  updatesAttributed : StoreUpdatesDirectionallyAttributed verify cs.gossip
  /-- The carried `NodeId → PubKey` map agrees with every announcement. -/
  nodeKeys : GossipState.NodeKeyConsistent cs.nodeKeyOf cs.gossip
  /-- At most one stored announcement per `short_channel_id`. -/
  canonical : cs.gossip.Canonical

/-- A state is canonically reachable when it is obtained from an empty store
(with any initial registration map) by finitely many
`admitGossipCanonical` steps. -/
inductive ReachableCanonical (verify : SigVerifier) :
    CanonicalNetwork → Prop
  | empty (nodeKeyOf : NodeId → PubKey) :
      ReachableCanonical verify
        { gossip := ⟨[], [], []⟩, views := [], nodeKeyOf := nodeKeyOf }
  | step {cs : CanonicalNetwork} {m : GossipMessage} :
      ReachableCanonical verify cs →
        ReachableCanonical verify (admitGossipCanonical verify cs m)

/-! ### Transfer lemmas -/

/-- Directional attribution transfers along an unchanged announcement list. -/
theorem updateKeyAnnouncedDirectional_of_announcements_eq
    {s t : GossipState} (h : t.announcements = s.announcements)
    {u : ChannelUpdate} (hk : s.updateKeyAnnouncedDirectional u) :
    t.updateKeyAnnouncedDirectional u := by
  rcases hk with ⟨a, ha, hscid, hkey⟩
  exact ⟨a, h ▸ ha, hscid, hkey⟩

/-- Node-key consistency transfers along an unchanged announcement list. -/
theorem nodeKeyConsistent_of_announcements_eq {nodeKeyOf : NodeId → PubKey}
    {s t : GossipState} (h : t.announcements = s.announcements)
    (hc : GossipState.NodeKeyConsistent nodeKeyOf s) :
    GossipState.NodeKeyConsistent nodeKeyOf t := by
  intro a ha
  exact hc a (h ▸ ha)

/-! ### Announcement branch -/

/-- A canonical announcement step preserves every invariant component. -/
theorem admitGossipCanonical_announcement_preserves (verify : SigVerifier)
    (cs : CanonicalNetwork) (a : ChannelAnnellation)
    (hinv : CanonicalAdmitted verify cs)
    (hgate : a.signaturesValid verify ∧ a.node1 ≠ a.node2 ∧
      cs.gossip.CompatibleWithStore a ∧
      UpdatesAuthorizedBy cs.gossip a) :
    CanonicalAdmitted verify
      (admitGossipCanonical verify cs (.channelAnnouncement a)) := by
  rw [admitGossipCanonical_announcement_of_admitted verify cs a hgate]
  rcases hgate with ⟨hsig, hne, hcompat, hauth⟩
  rcases hinv with ⟨hstore, hviews, hupdates, hnode, hcanon⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro b hb
    rcases mem_insertReplacing_iff.mp hb with hba | ⟨hb, _⟩
    · rw [hba]
      exact hsig
    · exact hstore b hb
  · intro v hv
    rcases mem_insertViewCanonical_iff.mp hv with hva | ⟨hv, hvne⟩
    · subst v
      exact ⟨a, mem_insertReplacing_iff.mpr (Or.inl rfl), hsig,
        rfl, rfl, rfl, rfl⟩
    · rcases hviews v hv with ⟨b, hb, hbsig, hbscid, hb1, hb2, hbcap⟩
      refine ⟨b, mem_insertReplacing_of_mem_of_ne hb ?_, hbsig,
        hbscid, hb1, hb2, hbcap⟩
      intro hsame
      exact hvne (hbscid.trans hsame)
  · intro u hu
    rcases hupdates u hu with ⟨husig, hk⟩
    refine ⟨husig, ?_⟩
    rcases hk with ⟨b, hb, hbscid, hbkey⟩
    by_cases hsame : b.shortChannelId = a.shortChannelId
    · have hu_scid : u.shortChannelId = a.shortChannelId := by
        rw [← hbscid]
        exact hsame
      exact GossipState.updateKeyAnnouncedDirectional_of_mem
        (mem_insertReplacing_iff.mpr (Or.inl rfl)) hu_scid.symm
        (hauth u hu hu_scid)
    · exact GossipState.updateKeyAnnouncedDirectional_of_mem
        (mem_insertReplacing_of_mem_of_ne hb hsame) hbscid hbkey
  · exact nodeKeyConsistent_insertReplacing hnode hcompat hne
  · exact canonical_insertReplacing hcanon a

/-! ### Update branch -/

/-- A canonical update step preserves every invariant component.  The
replacement announcement list is unchanged, so old update witnesses survive;
the incoming update is gated by direction-keyed attribution. -/
theorem admitGossipCanonical_update_preserves (verify : SigVerifier)
    (cs : CanonicalNetwork) (u : ChannelUpdate)
    (hinv : CanonicalAdmitted verify cs)
    (hgate : u.signatureValid verify ∧
      cs.gossip.updateKeyAnnouncedDirectional u ∧
      UpdateSupersedes u cs.gossip.updates) :
    CanonicalAdmitted verify
      (admitGossipCanonical verify cs (.channelUpdate u)) := by
  rw [admitGossipCanonical_update_of_admitted verify cs u hgate]
  rcases hinv with ⟨hstore, hviews, hupdates, hnode, hcanon⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact hstore
  · intro v hv
    rcases List.mem_map.mp hv with ⟨w, hw, rfl⟩
    rcases hviews w hw with ⟨b, hb, hbsig, hbscid, hb1, hb2, hbcap⟩
    refine ⟨b, ?_, hbsig, ?_, ?_, ?_, ?_⟩
    · exact hb
    · rw [ChannelView.applyUpdate_scid]
      exact hbscid
    · rw [ChannelView.applyUpdate_node1]
      exact hb1
    · rw [ChannelView.applyUpdate_node2]
      exact hb2
    · rw [ChannelView.applyUpdate_capacitySat]
      exact hbcap
  · intro v hv
    rcases mem_insertUpdateCanonical_iff.mp hv with hvu | ⟨hvl, _⟩
    · subst v
      exact ⟨hgate.1,
        updateKeyAnnouncedDirectional_of_announcements_eq rfl hgate.2.1⟩
    · rcases hupdates v hvl with ⟨hvsig, hvk⟩
      exact ⟨hvsig,
        updateKeyAnnouncedDirectional_of_announcements_eq rfl hvk⟩
  · exact nodeKeyConsistent_of_announcements_eq rfl hnode
  · exact hcanon

/-! ### Node-announcement branch -/

/-- A canonical node-announcement step preserves every invariant component. -/
theorem admitGossipCanonical_node_preserves (verify : SigVerifier)
    (cs : CanonicalNetwork) (n : NodeAnnouncement)
    (hinv : CanonicalAdmitted verify cs) :
    CanonicalAdmitted verify
      (admitGossipCanonical verify cs (.nodeAnnouncement n)) := by
  by_cases hsig : n.signatureValid verify
  · rw [admitGossipCanonical_node_of_valid verify cs n hsig]
    rcases hinv with ⟨hstore, hviews, hupdates, hnode, hcanon⟩
    exact ⟨hstore, hviews, hupdates, hnode, hcanon⟩
  · rw [admitGossipCanonical_node_of_invalid verify cs n hsig]
    exact hinv

/-- The full canonical transition preserves the invariant. -/
theorem admitGossipCanonical_preserves (verify : SigVerifier)
    (cs : CanonicalNetwork) (m : GossipMessage)
    (hinv : CanonicalAdmitted verify cs) :
    CanonicalAdmitted verify (admitGossipCanonical verify cs m) := by
  cases m with
  | channelAnnouncement a =>
      by_cases hgate : a.signaturesValid verify ∧ a.node1 ≠ a.node2 ∧
          cs.gossip.CompatibleWithStore a ∧
          UpdatesAuthorizedBy cs.gossip a
      · exact admitGossipCanonical_announcement_preserves verify cs a hinv hgate
      · rw [admitGossipCanonical_announcement_of_rejected verify cs a hgate]
        exact hinv
  | channelUpdate u =>
      by_cases hgate : u.signatureValid verify ∧
          cs.gossip.updateKeyAnnouncedDirectional u ∧
          UpdateSupersedes u cs.gossip.updates
      · exact admitGossipCanonical_update_preserves verify cs u hinv hgate
      · rw [admitGossipCanonical_update_of_rejected verify cs u hgate]
        exact hinv
  | nodeAnnouncement n =>
      exact admitGossipCanonical_node_preserves verify cs n hinv

/-- **The invariant of every canonically reachable state.** -/
theorem reachableCanonical_invariant {verify : SigVerifier}
    {cs : CanonicalNetwork} (h : ReachableCanonical verify cs) :
    CanonicalAdmitted verify cs := by
  induction h with
  | empty nodeKeyOf =>
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro a ha
        simp at ha
      · intro v hv
        simp [CanonicalNetwork.toNetwork] at hv
      · intro u hu
        simp at hu
      · intro a ha
        simp at ha
      · intro a ha
        simp at ha
  | step _ ih =>
      exact admitGossipCanonical_preserves verify _ _ ih

/-! ## 4. Derived invariants -/

/-- **`NodeKeyConsistent` is derived from reachability**, not assumed. -/
theorem reachableCanonical_nodeKeyConsistent {verify : SigVerifier}
    {cs : CanonicalNetwork} (h : ReachableCanonical verify cs) :
    GossipState.NodeKeyConsistent cs.nodeKeyOf cs.gossip :=
  (reachableCanonical_invariant h).nodeKeys

/-- **`CanonicalAnnouncements` is derived from reachability**, not assumed. -/
theorem reachableCanonical_canonical {verify : SigVerifier}
    {cs : CanonicalNetwork} (h : ReachableCanonical verify cs) :
    CanonicalAnnouncements cs.gossip.announcements :=
  (reachableCanonical_invariant h).canonical

/-- Every stored announcement of a reachable canonical state verifies. -/
theorem reachableCanonical_store_valid {verify : SigVerifier}
    {cs : CanonicalNetwork} (h : ReachableCanonical verify cs) :
    StoreAnnouncementsValid verify cs.gossip :=
  (reachableCanonical_invariant h).storeValid

/-- Every view of a reachable canonical state is announcement-backed. -/
theorem reachableCanonical_views_backed {verify : SigVerifier}
    {cs : CanonicalNetwork} (h : ReachableCanonical verify cs) :
    ViewsBacked verify cs.toNetwork :=
  (reachableCanonical_invariant h).viewsBacked

/-- Every stored update of a reachable canonical state verifies and is
direction-correctly attributed. -/
theorem reachableCanonical_updates_directional {verify : SigVerifier}
    {cs : CanonicalNetwork} (h : ReachableCanonical verify cs) :
    StoreUpdatesDirectionallyAttributed verify cs.gossip :=
  (reachableCanonical_invariant h).updatesAttributed

/-! ## 5. Endpoint attribution without consistency hypotheses -/

/-- **Endpoint attribution from the canonical invariant alone.**  This is the
wave-5 endpoint theorem with `NodeKeyConsistent` and `CanonicalAnnouncements`
as *derived* inputs rather than caller-supplied hypotheses. -/
theorem canonical_endpoint_of_invariant
    (verify : SigVerifier) (cs : CanonicalNetwork)
    (hviews : ViewsBacked verify cs.toNetwork)
    (hupd : StoreUpdatesDirectionallyAttributed verify cs.gossip)
    (hcanon : CanonicalAnnouncements cs.gossip.announcements)
    (hnode : GossipState.NodeKeyConsistent cs.nodeKeyOf cs.gossip) :
    ∀ e ∈ cs.toNetwork.graph.edges, ∀ u ∈ cs.gossip.updates,
      u.shortChannelId = e.shortChannelId →
        u.signatureValid verify ∧
          u.signingKey =
            (if u.direction then cs.nodeKeyOf e.node2
              else cs.nodeKeyOf e.node1) := by
  intro e he u hu hscid
  have he' : e ∈ cs.views.map ChannelView.edge := he
  rcases List.mem_map.mp he' with ⟨v, hv, rfl⟩
  rcases hviews v hv with ⟨b, hb, _hbsig, hbscid, hb1, hb2, _hbcap⟩
  rcases hupd u hu with ⟨husig, hk⟩
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

/-- **`RT-01` endpoint theorem for canonically reachable states.**  Every
stored update for a graph edge is signed by exactly the endpoint selected by
its BOLT 7 direction.  No `NodeKeyConsistent` or `CanonicalAnnouncements`
hypothesis remains: both are derived by `reachableCanonical_invariant`. -/
theorem reachableCanonical_directional_key_endpoint
    (verify : SigVerifier) (cs : CanonicalNetwork)
    (h : ReachableCanonical verify cs) :
    ∀ e ∈ cs.toNetwork.graph.edges, ∀ u ∈ cs.gossip.updates,
      u.shortChannelId = e.shortChannelId →
        u.signatureValid verify ∧
          u.signingKey =
            (if u.direction then cs.nodeKeyOf e.node2
              else cs.nodeKeyOf e.node1) :=
  canonical_endpoint_of_invariant verify cs
    (reachableCanonical_views_backed h)
    (reachableCanonical_updates_directional h)
    (reachableCanonical_canonical h)
    (reachableCanonical_nodeKeyConsistent h)

/-- **No ambiguous attribution in a reachable canonical state.**  Two stored
updates for the same channel and direction have the same signing key.  This is
the wave-5 uniqueness result with canonicality derived from reachability. -/
theorem reachableCanonical_attribution_unique {verify : SigVerifier}
    {cs : CanonicalNetwork} (h : ReachableCanonical verify cs)
    {u v : ChannelUpdate} (hu : u ∈ cs.gossip.updates)
    (hv : v ∈ cs.gossip.updates)
    (hscid : u.shortChannelId = v.shortChannelId)
    (hdir : u.direction = v.direction) :
    u.signingKey = v.signingKey :=
  canonical_directional_attribution_unique
    (reachableCanonical_canonical h) hscid hdir
    (reachableCanonical_updates_directional h u hu).2
    (reachableCanonical_updates_directional h v hv).2

/-! ## 6. Explicit key rotation -/

/-- **Rotation preserves the two registration invariants.**  Rekeying one graph
node and every affected announcement keeps `NodeKeyConsistent` and
canonicality.  This statement is deliberately about registration only: it does
not claim that announcement signatures or stored-update attribution survive
rotation (see `rotation_breaks_update_attribution`). -/
theorem key_rotation_preserves_registration_invariants
    (verify : SigVerifier) (cs : CanonicalNetwork)
    (h : ReachableCanonical verify cs) (n : NodeId) (k : PubKey) :
    GossipState.NodeKeyConsistent (rotateNodeKey cs.nodeKeyOf n k)
        (rekeyStore cs.gossip n k) ∧
      CanonicalAnnouncements (rekeyStore cs.gossip n k).announcements :=
  ⟨nodeKeyConsistent_rekey
      (reachableCanonical_nodeKeyConsistent h) n k,
    canonical_rekey (reachableCanonical_canonical h) n k⟩

/-! ## 7. Preserved raw-store counterexamples -/

/-- The raw append-only store still accepts a conflicting announcement.  This
is the wave-5 counterexample, re-exported so the canonical transition cannot be
mistaken for a change to `applyGossip`. -/
theorem raw_store_still_not_canonical :
    ∃ (s : GossipState) (a : ChannelAnnellation),
      ¬ CanonicalAnnouncements
        (applyGossip s (.channelAnnouncement a)).announcements :=
  raw_applyGossip_accepts_conflicting_announcement

/-- Without a canonical selector, conflicting announcements remain ambiguous.
This is the wave-5 counterexample, re-exported unchanged. -/
theorem ambiguous_without_canonical_still_holds :
    ∃ (s : GossipState) (u v : ChannelUpdate),
      ¬ CanonicalAnnouncements s.announcements ∧
        u.shortChannelId = v.shortChannelId ∧ u.direction = v.direction ∧
          s.updateKeyAnnouncedDirectional u ∧
            s.updateKeyAnnouncedDirectional v ∧ u.signingKey ≠ v.signingKey :=
  conflicting_announcements_ambiguous_without_canonical

/-- Raw `applyGossip` still accepts a directionally unattributed update. -/
theorem raw_store_still_unfiltered :
    ∃ (s : GossipState) (u : ChannelUpdate),
      ¬ s.updateKeyAnnouncedDirectional u ∧
        (applyGossip s (.channelUpdate u)).updates = u :: s.updates :=
  raw_applyGossip_accepts_directionally_unattributed_update

/-! ## 8. Concrete witnesses -/

private def acceptingVerifier : SigVerifier := fun _ _ _ => true

/-- Byte length 1. -/
private def key1 : PubKey := ⟨ByteArray.mk #[1]⟩

/-- Byte length 0. -/
private def key2 : PubKey := ⟨ByteArray.empty⟩

/-- Byte length 2. -/
private def key3 : PubKey := ⟨ByteArray.mk #[1, 2]⟩

private def nodeA : NodeId := ⟨0⟩

private def nodeB : NodeId := ⟨1⟩

private def sampleScid : ShortChannelId := ⟨1, 2, 3⟩

private def emptySig : GossipSignature := ⟨ByteArray.empty⟩

private def emptyStore : GossipState := ⟨[], [], []⟩

private def mkAnn (capacity : Nat) (k1 k2 : PubKey) : ChannelAnnellation :=
  { shortChannelId := sampleScid
    node1 := nodeA
    node2 := nodeB
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

/-- The reference announcement: `nodeA ↦ key1`, `nodeB ↦ key2`. -/
private def ann1 : ChannelAnnellation := mkAnn 1000 key1 key2

/-- A conflicting re-announcement for the same channel: `nodeA ↦ key3`. -/
private def ann2 : ChannelAnnellation := mkAnn 2000 key3 key2

private def mkUpdate (timestamp : Nat) (k : PubKey) : ChannelUpdate :=
  { shortChannelId := sampleScid
    timestamp := timestamp
    messageFlags := 0
    channelFlags := 0
    cltvDelta := 1
    htlcMinimumMsat := Msat.zero
    feeBaseMsat := Msat.zero
    feeProportionalMillionths := 0
    htlcMaximumMsat := Msat.MAX
    signingKey := k
    digest := ByteArray.empty
    signature := emptySig }

/-- Direction-0 update, timestamp 1, signed by `key1`. -/
private def u0 : ChannelUpdate := mkUpdate 1 key1

/-- Direction-0 update, timestamp 2, signed by `key1`; supersedes `u0`. -/
private def u1 : ChannelUpdate := mkUpdate 2 key1

private theorem key1_ne_key2 : key1 ≠ key2 := by
  intro h
  have hs := congrArg (fun k => k.bytes.size) h
  have h1 : key1.bytes.size = 1 := by decide
  have h2 : key2.bytes.size = 0 := rfl
  rw [h1, h2] at hs
  exact Nat.noConfusion hs

private theorem key1_ne_key3 : key1 ≠ key3 := by
  intro h
  have hs := congrArg (fun k => k.bytes.size) h
  have h1 : key1.bytes.size = 1 := by decide
  have h3 : key3.bytes.size = 2 := by decide
  rw [h1, h3] at hs
  omega

private theorem nodeA_ne_nodeB : nodeA ≠ nodeB := by
  intro h
  have hi := congrArg NodeId.index h
  exact Nat.noConfusion hi

private theorem ann1_valid :
    ann1.signaturesValid acceptingVerifier := by
  simp [ChannelAnnellation.signaturesValid, signatureValid, acceptingVerifier]

private theorem ann2_valid :
    ann2.signaturesValid acceptingVerifier := by
  simp [ChannelAnnellation.signaturesValid, signatureValid, acceptingVerifier]

private theorem u0_valid : u0.signatureValid acceptingVerifier := by
  simp [ChannelUpdate.signatureValid, signatureValid, acceptingVerifier]

private theorem u1_valid : u1.signatureValid acceptingVerifier := by
  simp [ChannelUpdate.signatureValid, signatureValid, acceptingVerifier]

private def start : CanonicalNetwork :=
  { gossip := emptyStore, views := [], nodeKeyOf := fun _ => key2 }

private theorem start_compatible (a : ChannelAnnellation) :
    start.gossip.CompatibleWithStore a := by
  intro b hb
  simp [start, emptyStore] at hb

private theorem start_authorizes (a : ChannelAnnellation) :
    UpdatesAuthorizedBy start.gossip a := by
  intro u hu
  simp [start, emptyStore] at hu

private theorem ann1_gate :
    ann1.signaturesValid acceptingVerifier ∧ ann1.node1 ≠ ann1.node2 ∧
      start.gossip.CompatibleWithStore ann1 ∧
        UpdatesAuthorizedBy start.gossip ann1 :=
  ⟨ann1_valid, by simpa [ann1, mkAnn] using nodeA_ne_nodeB,
    start_compatible ann1, start_authorizes ann1⟩

private noncomputable def afterAnn : CanonicalNetwork :=
  admitGossipCanonical acceptingVerifier start (.channelAnnouncement ann1)

private theorem afterAnn_eq : afterAnn =
    { gossip := { start.gossip with announcements := [ann1] }
      views := [admittedChannelView ann1]
      nodeKeyOf := bindNodeKeys start.nodeKeyOf ann1 } := by
  unfold afterAnn
  rw [admitGossipCanonical_announcement_of_admitted acceptingVerifier start ann1
    ann1_gate]
  simp [insertReplacing, insertViewCanonical, start, emptyStore]

private theorem afterAnn_announcements : afterAnn.gossip.announcements = [ann1] := by
  rw [afterAnn_eq]

private theorem afterAnn_updates : afterAnn.gossip.updates = [] := by
  rw [afterAnn_eq]
  rfl

private theorem afterAnn_views : afterAnn.views = [admittedChannelView ann1] := by
  rw [afterAnn_eq]

private theorem afterAnn_reachable :
    ReachableCanonical acceptingVerifier afterAnn := by
  unfold afterAnn
  exact ReachableCanonical.step
    (ReachableCanonical.empty (fun _ => key2))

private theorem afterAnn_attributed_u0 :
    afterAnn.gossip.updateKeyAnnouncedDirectional u0 := by
  refine GossipState.updateKeyAnnouncedDirectional_of_mem (a := ann1) ?_ rfl ?_
  · rw [afterAnn_announcements]
    exact List.mem_singleton_self ann1
  · rw [ChannelUpdate.direction_of_channelFlags_zero (by rfl : u0.channelFlags = 0)]
    simp [ChannelAnnellation.attributesKeyForDirection, ann1, mkAnn, u0, mkUpdate]

private theorem afterAnn_attributed_u1 :
    afterAnn.gossip.updateKeyAnnouncedDirectional u1 := by
  refine GossipState.updateKeyAnnouncedDirectional_of_mem (a := ann1) ?_ rfl ?_
  · rw [afterAnn_announcements]
    exact List.mem_singleton_self ann1
  · rw [ChannelUpdate.direction_of_channelFlags_zero (by rfl : u1.channelFlags = 0)]
    simp [ChannelAnnellation.attributesKeyForDirection, ann1, mkAnn, u1, mkUpdate]

private theorem afterAnn_supersedes_u0 :
    UpdateSupersedes u0 afterAnn.gossip.updates := by
  intro v hv
  rw [afterAnn_updates] at hv
  simp at hv

private theorem u0_gate_afterAnn :
    u0.signatureValid acceptingVerifier ∧
      afterAnn.gossip.updateKeyAnnouncedDirectional u0 ∧
        UpdateSupersedes u0 afterAnn.gossip.updates :=
  ⟨u0_valid, afterAnn_attributed_u0, afterAnn_supersedes_u0⟩

private noncomputable def afterU0 : CanonicalNetwork :=
  admitGossipCanonical acceptingVerifier afterAnn (.channelUpdate u0)

private theorem afterU0_eq : afterU0 =
    { gossip := { afterAnn.gossip with updates := [u0] }
      views := afterAnn.views.map fun v => v.applyUpdate u0
      nodeKeyOf := afterAnn.nodeKeyOf } := by
  unfold afterU0
  rw [admitGossipCanonical_update_of_admitted acceptingVerifier afterAnn u0
    u0_gate_afterAnn]
  rw [afterAnn_updates]
  simp [insertUpdateCanonical]

private theorem afterU0_announcements :
    afterU0.gossip.announcements = [ann1] := by
  rw [afterU0_eq]
  simpa using afterAnn_announcements

private theorem afterU0_updates : afterU0.gossip.updates = [u0] := by
  rw [afterU0_eq]

private theorem afterU0_attributed_u1 :
    afterU0.gossip.updateKeyAnnouncedDirectional u1 :=
  updateKeyAnnouncedDirectional_of_announcements_eq
    (by rw [afterU0_announcements, afterAnn_announcements])
    afterAnn_attributed_u1

private theorem afterU0_supersedes_u1 :
    UpdateSupersedes u1 afterU0.gossip.updates := by
  intro v hv _hscid _hdir
  rw [afterU0_updates] at hv
  simp only [List.mem_singleton] at hv
  subst v
  simp [u0, u1, mkUpdate]

private theorem u1_gate_afterU0 :
    u1.signatureValid acceptingVerifier ∧
      afterU0.gossip.updateKeyAnnouncedDirectional u1 ∧
        UpdateSupersedes u1 afterU0.gossip.updates :=
  ⟨u1_valid, afterU0_attributed_u1, afterU0_supersedes_u1⟩

private noncomputable def afterU1 : CanonicalNetwork :=
  admitGossipCanonical acceptingVerifier afterU0 (.channelUpdate u1)

private theorem afterU1_eq : afterU1 =
    { gossip := { afterU0.gossip with updates := [u1] }
      views := afterU0.views.map fun v => v.applyUpdate u1
      nodeKeyOf := afterU0.nodeKeyOf } := by
  unfold afterU1
  rw [admitGossipCanonical_update_of_admitted acceptingVerifier afterU0 u1
    u1_gate_afterU0]
  rw [afterU0_updates]
  simp [insertUpdateCanonical, u0, u1, mkUpdate, ChannelUpdate.direction]

private theorem afterU1_reachable :
    ReachableCanonical acceptingVerifier afterU1 := by
  unfold afterU1 afterU0
  exact ReachableCanonical.step (ReachableCanonical.step afterAnn_reachable)

private theorem afterU1_updates : afterU1.gossip.updates = [u1] := by
  rw [afterU1_eq]

private theorem afterU1_announcements :
    afterU1.gossip.announcements = [ann1] := by
  rw [afterU1_eq]
  simpa using afterU0_announcements

private theorem u0_ne_u1 : u0 ≠ u1 := by
  intro h
  have ht := congrArg ChannelUpdate.timestamp h
  simp [u0, u1, mkUpdate] at ht

private theorem u0_not_mem_afterU1 : u0 ∉ afterU1.gossip.updates := by
  rw [afterU1_updates]
  simp [u0_ne_u1]

private theorem u1_mem_afterU1 : u1 ∈ afterU1.gossip.updates := by
  rw [afterU1_updates]
  exact List.mem_singleton_self u1

private theorem afterU1_views_ne_nil : afterU1.views ≠ [] := by
  rw [afterU1_eq, afterU0_eq, afterAnn_eq]
  simp

private theorem afterU1_graph_edges_ne_nil :
    afterU1.toNetwork.graph.edges ≠ [] := by
  intro hnil
  have hmap : afterU1.views.map ChannelView.edge = [] := hnil
  have hnil' : afterU1.views = [] := List.map_eq_nil_iff.mp hmap
  exact afterU1_views_ne_nil hnil'

/-- **Update supersession is real in a reachable canonical state.**  A newer
direction-0 update replaced the older one in the same
`(short_channel_id, direction)` slot: the newer update is stored, the older one
is gone, and both addressed the same channel and direction. -/
theorem reachableCanonical_supersession_witness :
    ∃ (verify : SigVerifier) (cs : CanonicalNetwork),
      ReachableCanonical verify cs ∧
        GossipState.NodeKeyConsistent cs.nodeKeyOf cs.gossip ∧
          CanonicalAnnouncements cs.gossip.announcements ∧
            (∃ u v : ChannelUpdate, u ∈ cs.gossip.updates ∧
              v ∉ cs.gossip.updates ∧
                u.shortChannelId = v.shortChannelId ∧
                  u.direction = v.direction ∧
                    v.timestamp < u.timestamp ∧ u.timestamp ≠ v.timestamp) := by
  refine ⟨acceptingVerifier, afterU1, afterU1_reachable,
    reachableCanonical_nodeKeyConsistent afterU1_reachable,
    reachableCanonical_canonical afterU1_reachable,
    ⟨u1, u0, u1_mem_afterU1, u0_not_mem_afterU1, rfl, rfl, ?_, ?_⟩⟩
  · simp [u0, u1, mkUpdate]
  · simp [u0, u1, mkUpdate]

/-- **The canonical transition rejects the conflicting re-announcement.**  The
same channel cannot be rebound from `key1` to `key3`; the state is unchanged.
This is the admission-side counterpart of the preserved wave-5 ambiguity
counterexample. -/
theorem canonical_admission_rejects_conflicting_announcement :
    ∃ (verify : SigVerifier) (cs : CanonicalNetwork) (a : ChannelAnnellation),
      ReachableCanonical verify cs ∧
        ¬ cs.gossip.CompatibleWithStore a ∧
          admitGossipCanonical verify cs (.channelAnnouncement a) = cs := by
  have hcompat : ¬ afterAnn.gossip.CompatibleWithStore ann2 := by
    intro hc
    have hmem : ann1 ∈ afterAnn.gossip.announcements := by
      rw [afterAnn_announcements]
      exact List.mem_singleton_self ann1
    have hkey : ann1.nodeKey1 = ann2.nodeKey1 := (hc ann1 hmem).1 rfl
    exact key1_ne_key3 hkey
  refine ⟨acceptingVerifier, afterAnn, ann2, afterAnn_reachable, hcompat, ?_⟩
  rw [admitGossipCanonical_announcement_of_rejected]
  rintro ⟨_, _, hc, _⟩
  exact hcompat hc

/-- **Non-vacuity of derived canonicality.**  A reachable canonical state has a
non-empty, canonical announcement store with a consistent registration map. -/
theorem reachableCanonical_stores_canonical_state :
    ∃ (verify : SigVerifier) (cs : CanonicalNetwork),
      ReachableCanonical verify cs ∧ cs.gossip.announcements ≠ [] ∧
        GossipState.NodeKeyConsistent cs.nodeKeyOf cs.gossip ∧
          CanonicalAnnouncements cs.gossip.announcements := by
  refine ⟨acceptingVerifier, afterU1, afterU1_reachable, ?_,
    reachableCanonical_nodeKeyConsistent afterU1_reachable,
    reachableCanonical_canonical afterU1_reachable⟩
  rw [afterU1_announcements]
  simp

/-- **Non-vacuity of the endpoint theorem.**  The reachable canonical state has
a non-empty graph and satisfies the direction-keyed endpoint statement with no
consistency hypotheses. -/
theorem reachableCanonical_directional_endpoint_witness :
    ∃ (verify : SigVerifier) (cs : CanonicalNetwork),
      ReachableCanonical verify cs ∧ cs.toNetwork.graph.edges ≠ [] ∧
        ∀ e ∈ cs.toNetwork.graph.edges, ∀ u ∈ cs.gossip.updates,
          u.shortChannelId = e.shortChannelId →
            u.signatureValid verify ∧
              u.signingKey =
                (if u.direction then cs.nodeKeyOf e.node2
                  else cs.nodeKeyOf e.node1) := by
  refine ⟨acceptingVerifier, afterU1, afterU1_reachable,
    afterU1_graph_edges_ne_nil, ?_⟩
  exact reachableCanonical_directional_key_endpoint acceptingVerifier afterU1
    afterU1_reachable

/-! ### Rotation boundary -/

private def sampleNodeKeyOf : NodeId → PubKey := fun n =>
  if n = nodeA then key1 else key2

private def rotationStore : GossipState := ⟨[ann1], [], []⟩

private theorem rotationStore_consistent :
    GossipState.NodeKeyConsistent sampleNodeKeyOf rotationStore := by
  intro a ha
  simp [rotationStore] at ha
  subst a
  constructor
  · simp [sampleNodeKeyOf, ann1, mkAnn, nodeA]
  · simp [sampleNodeKeyOf, ann1, mkAnn, nodeA, nodeB]

private theorem rotationStore_canonical :
    CanonicalAnnouncements rotationStore.announcements := by
  intro a ha b hb _hscid
  simp [rotationStore] at ha hb
  rw [ha, hb]

private theorem rotationStore_attributed_u0 :
    rotationStore.updateKeyAnnouncedDirectional u0 := by
  refine GossipState.updateKeyAnnouncedDirectional_of_mem (a := ann1) ?_ rfl ?_
  · simp [rotationStore]
  · rw [ChannelUpdate.direction_of_channelFlags_zero (by rfl : u0.channelFlags = 0)]
    simp [ChannelAnnellation.attributesKeyForDirection, ann1, mkAnn, u0, mkUpdate]

private theorem rotation_rekeyed_announcements :
    (rekeyStore rotationStore nodeA key3).announcements =
      [rekeyAnnouncement ann1 nodeA key3] := by
  simp [rekeyStore, rekeyAnnouncements, rotationStore]

private theorem rotation_not_attributed_u0 :
    ¬ (rekeyStore rotationStore nodeA key3).updateKeyAnnouncedDirectional u0 := by
  intro hk
  rcases hk with ⟨a, ha, _hscid, hkey⟩
  rw [rotation_rekeyed_announcements] at ha
  simp only [List.mem_singleton] at ha
  subst a
  rw [ChannelUpdate.direction_of_channelFlags_zero (by rfl : u0.channelFlags = 0),
    ChannelAnnellation.attributesKeyForDirection] at hkey
  simp [rekeyAnnouncement, ann1, mkAnn, u0, mkUpdate, nodeA] at hkey
  exact key1_ne_key3 hkey.symm

/-- **Rotation is registration-only.**  Rotating a registered node key keeps
`NodeKeyConsistent` and canonicality for the rekeyed store, but a stored update
signed by the old key is no longer direction-attributed.  Re-signing and
resubmission are explicit obligations, not hidden by the rotation lemma. -/
theorem rotation_breaks_update_attribution :
    ∃ (nodeKeyOf : NodeId → PubKey) (s : GossipState) (n : NodeId)
      (k : PubKey) (u : ChannelUpdate),
      GossipState.NodeKeyConsistent nodeKeyOf s ∧
        GossipState.NodeKeyConsistent (rotateNodeKey nodeKeyOf n k)
          (rekeyStore s n k) ∧
          CanonicalAnnouncements (rekeyStore s n k).announcements ∧
            s.updateKeyAnnouncedDirectional u ∧
              ¬ (rekeyStore s n k).updateKeyAnnouncedDirectional u := by
  refine ⟨sampleNodeKeyOf, rotationStore, nodeA, key3, u0,
    rotationStore_consistent, ?_, ?_, rotationStore_attributed_u0,
    rotation_not_attributed_u0⟩
  · exact nodeKeyConsistent_rekey rotationStore_consistent nodeA key3
  · exact canonical_rekey rotationStore_canonical nodeA key3

end LnLean.Proofs.Routing.GossipCanonicalTargets
