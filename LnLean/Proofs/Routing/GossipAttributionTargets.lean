import LnLean.Proofs.Routing.GossipTargets

/-!
# LnLean.Proofs.Routing.GossipAttributionTargets

Wave-4 lane `S4-GOSSIP-ATTR`, open issue `RT-01` (`LN-GOSSIP-001`, audit G19).

English claim of this module:

* BOLT 7 does not merely require a `channel_update` to carry *some* verifying
  signature; it requires the signature to be checked under a `node_id` taken
  from the matching `channel_announcement`
  (`refs/bolts/07-routing-gossip.md:544`).
* `GossipState.updateKeyAnnounced` (added additively in
  `LnLean/Routing/Gossip.lean`) is the explicit key-attribution relation: the
  update's `signingKey` is `node_id_1` or `node_id_2` of a stored
  announcement for the same `short_channel_id`.
* `admitGossipAttributed` is an admission transition whose `channel_update`
  branch requires **both** the abstract signature predicate and
  `updateKeyAnnounced`.  Its announcement and node branches are exactly the
  signature-gated branches of `LnLean.Proofs.Routing.GossipTargets.admitGossip`,
  so the S3-RT006 model and theorem are reused, not redefined.
* `ReachableAttributed` closes the attributed step over all three messages.

The main results:

* `reachableAttributed_updates_attributed`: in every attributed-reachable
  state, every stored `channel_update` has a verifying signature and an
  announced signing key.
* `gossip_graph_edges_update_attributed`: in every attributed-reachable state,
  every graph edge `e` and every stored update for `e.shortChannelId` has a
  verifying signature and a signing key attributed by a *valid* stored
  announcement for that channel.
* `gossip_graph_edges_update_key_endpoint`: under the explicit consistency
  hypotheses `AttributionConsistent` (announcements for one channel agree on
  graph endpoints **and** node keys) and `KeyAttribution nodeKeyOf` (the graph
  node owns the announced key), the update's signing key is exactly
  `nodeKeyOf e.node1` or `nodeKeyOf e.node2`.

What is **not** claimed:

* Raw `applyGossip` is untouched and remains unfiltered.  The S3-RT006
  theorem `gossip_graph_only_valid_announcements` and its raw-store caveat
  (`raw_store_not_filtered`, `raw_store_invariant_not_preserved`) still hold;
  `raw_applyGossip_accepts_unannounced_update` below re-exhibits the raw
  behaviour next to the attributed gate.
* `SigVerifier` is abstract.  Signature validity is the equation
  `verify key digest sig = true`, not unforgeability.  Key ownership is the
  explicit `KeyAttribution` hypothesis, not a theorem.
* The BOLT 7 direction bit (`channel_flags` bit 0) is not decoded by the
  model, so `attributesKey` accepts either announced node key.  The
  direction-keyed refinement remains an integration step (see the report).
* `AttributionConsistent` is a hypothesis on the final store, not an
  invariant of the admission transition: the wave-A store is append-only and
  does not reject a conflicting re-announcement for the same
  `short_channel_id` (see `GossipProps.uniqueBindings`).  It is stated
  explicitly so the endpoint-attribution theorem is not read as stronger
  than the model supports.

No `sorry`, no `axiom`, no `admit`, no `native_decide`, no `unsafe`, no
`@[implemented_by]`.
-/

namespace LnLean.Proofs.Routing.GossipAttributionTargets

open LnLean.Routing
open LnLean.Routing.GossipProps
open LnLean.Proofs.Routing.GossipTargets
open Classical

set_option autoImplicit false

/-! ## 1. The attributed admission transition -/

/-- **Attributed gossip admission.**  Announcement and node messages use the
S3-RT006 signature-gated step `admitGossip` unchanged.  A `channel_update` is
admitted only when its abstract signature verifies *and*
`GossipState.updateKeyAnnounced` holds for the current store; the resulting
view replacement is exactly the wave-A `ChannelView.applyUpdate` rule.

This is an additional transition.  It does not modify `applyGossip`,
`GossipState.applyUpdate`, `acceptChannelUpdate`, `applyGossipChecked`, or
`admitGossip`. -/
noncomputable def admitGossipAttributed (verify : SigVerifier) (ns : GossipNetwork) :
    GossipMessage → GossipNetwork
  | .channelAnnouncement a => admitGossip verify ns (.channelAnnouncement a)
  | .channelUpdate u =>
      if u.signatureValid verify ∧ ns.gossip.updateKeyAnnounced u then
        { gossip := applyGossip ns.gossip (.channelUpdate u)
          views := ns.views.map fun v => v.applyUpdate u }
      else ns
  | .nodeAnnouncement n => admitGossip verify ns (.nodeAnnouncement n)

/-- An announcement step is the S3-RT006 admission step. -/
@[simp] theorem admitGossipAttributed_announcement (verify : SigVerifier)
    (ns : GossipNetwork) (a : ChannelAnnellation) :
    admitGossipAttributed verify ns (.channelAnnouncement a) =
      admitGossip verify ns (.channelAnnouncement a) :=
  rfl

/-- A node-announcement step is the S3-RT006 admission step. -/
@[simp] theorem admitGossipAttributed_node (verify : SigVerifier)
    (ns : GossipNetwork) (n : NodeAnnouncement) :
    admitGossipAttributed verify ns (.nodeAnnouncement n) =
      admitGossip verify ns (.nodeAnnouncement n) :=
  rfl

/-- An attributed update (verifying signature and announced key) is admitted
with the wave-A update effect. -/
@[simp] theorem admitGossipAttributed_update_of_attributed (verify : SigVerifier)
    (ns : GossipNetwork) (u : ChannelUpdate)
    (hsig : u.signatureValid verify)
    (hk : ns.gossip.updateKeyAnnounced u) :
    admitGossipAttributed verify ns (.channelUpdate u) =
      { gossip := applyGossip ns.gossip (.channelUpdate u)
        views := ns.views.map fun v => v.applyUpdate u } := by
  simp [admitGossipAttributed, hsig, hk]

/-- An update that fails the attributed gate (bad signature or unannounced
key) is a no-op. -/
theorem admitGossipAttributed_update_of_rejected (verify : SigVerifier)
    (ns : GossipNetwork) (u : ChannelUpdate)
    (h : ¬ (u.signatureValid verify ∧ ns.gossip.updateKeyAnnounced u)) :
    admitGossipAttributed verify ns (.channelUpdate u) = ns := by
  simp [admitGossipAttributed, h]

/-- An update whose key was never announced is rejected, even when every
signature check succeeds. -/
theorem admitGossipAttributed_update_of_unannounced (verify : SigVerifier)
    (ns : GossipNetwork) (u : ChannelUpdate)
    (hk : ¬ ns.gossip.updateKeyAnnounced u) :
    admitGossipAttributed verify ns (.channelUpdate u) = ns :=
  admitGossipAttributed_update_of_rejected verify ns u (fun h => hk h.2)

/-- **Preservation of the S3-RT006 behaviour.**  When the update's key is
announced, the attributed step is exactly the signature-gated `admitGossip`
step; attribution is the only extra gate. -/
theorem admitGossipAttributed_eq_admitGossip_of_attributed
    (verify : SigVerifier) (ns : GossipNetwork) (u : ChannelUpdate)
    (hk : ns.gossip.updateKeyAnnounced u) :
    admitGossipAttributed verify ns (.channelUpdate u) =
      admitGossip verify ns (.channelUpdate u) := by
  by_cases hsig : u.signatureValid verify
  · rw [admitGossipAttributed_update_of_attributed verify ns u hsig hk,
      admitGossip_update_of_valid verify ns u hsig]
  · rw [admitGossip_update_of_invalid verify ns u hsig]
    exact admitGossipAttributed_update_of_rejected verify ns u
      (fun h => hsig h.1)

/-- The store component of an attributed announcement/node step is the
S3-RT006 checked store step. -/
theorem admitGossipAttributed_gossip_eq_checked (verify : SigVerifier)
    (ns : GossipNetwork) (m : GossipMessage) (hm : ¬ ∃ u, m = .channelUpdate u) :
    (admitGossipAttributed verify ns m).gossip =
      applyGossipChecked verify ns.gossip m := by
  cases m with
  | channelAnnouncement a =>
      exact admitGossip_gossip_eq verify ns (.channelAnnouncement a)
  | channelUpdate u => exact absurd ⟨u, rfl⟩ hm
  | nodeAnnouncement n =>
      exact admitGossip_gossip_eq verify ns (.nodeAnnouncement n)

/-! ## 2. Attributed reachability and its invariants -/

/-- A state is attributed-reachable when it is obtained from the empty
network by a finite sequence of `admitGossipAttributed` steps. -/
inductive ReachableAttributed (verify : SigVerifier) : GossipNetwork → Prop
  | empty : ReachableAttributed verify { gossip := ⟨[], [], []⟩, views := [] }
  | step {ns : GossipNetwork} {m : GossipMessage} :
      ReachableAttributed verify ns →
        ReachableAttributed verify (admitGossipAttributed verify ns m)

/-- Every stored update has a verifying signature and an announced signing
key. -/
def StoreUpdatesAttributed (verify : SigVerifier) (s : GossipState) : Prop :=
  ∀ u ∈ s.updates, u.signatureValid verify ∧ s.updateKeyAnnounced u

/-- The combined invariant of attributed-reachable states: the store holds
only valid announcements, every view is backed by one of them, and every
stored update is signature-valid with an announced key. -/
def AttributedAdmitted (verify : SigVerifier) (ns : GossipNetwork) : Prop :=
  StoreAnnouncementsValid verify ns.gossip ∧ ViewsBacked verify ns ∧
    StoreUpdatesAttributed verify ns.gossip

/-! ### Preservation lemmas for the reused `admitGossip` branches -/

/-- `admitGossip` preserves the announcement-store invariant (a restatement of
`applyGossipChecked_preserves_store` at the admission seam). -/
theorem admitGossip_preserves_store (verify : SigVerifier)
    (ns : GossipNetwork) (m : GossipMessage)
    (h : StoreAnnouncementsValid verify ns.gossip) :
    StoreAnnouncementsValid verify (admitGossip verify ns m).gossip := by
  rw [admitGossip_gossip_eq]
  exact applyGossipChecked_preserves_store verify ns.gossip m h

/-- `admitGossip` preserves the view-backing invariant.  This is the step case
of S3-RT006's `reachable_views_backed`, stated as a transition lemma. -/
theorem admitGossip_preserves_views_backed (verify : SigVerifier)
    (ns : GossipNetwork) (m : GossipMessage) (h : ViewsBacked verify ns) :
    ViewsBacked verify (admitGossip verify ns m) := by
  cases m with
  | channelAnnouncement a =>
      intro v hv
      by_cases hsig : a.signaturesValid verify
      · rw [admitGossip_announcement_of_valid verify ns a hsig] at hv ⊢
        rcases List.mem_cons.mp hv with rfl | hv
        · exact ⟨a, by simp [applyGossip], hsig, rfl, rfl, rfl, rfl⟩
        · rcases h v hv with ⟨b, hb, hbsig, hscid, h1, h2, hcap⟩
          exact ⟨b, by simp [applyGossip, hb], hbsig, hscid, h1, h2, hcap⟩
      · rw [admitGossip_announcement_of_invalid verify ns a hsig] at hv ⊢
        exact h v hv
  | channelUpdate u =>
      intro v hv
      by_cases hsig : u.signatureValid verify
      · rw [admitGossip_update_of_valid verify ns u hsig] at hv ⊢
        rcases List.mem_map.mp hv with ⟨w, hw, rfl⟩
        rcases h w hw with ⟨b, hb, hbsig, hscid, h1, h2, hcap⟩
        refine ⟨b, ?_, hbsig, ?_, ?_, ?_, ?_⟩
        · show b ∈ (ns.gossip.applyUpdate u).announcements
          rw [GossipState.applyUpdate_announcements]
          exact hb
        · rw [ChannelView.applyUpdate_scid]; exact hscid
        · rw [ChannelView.applyUpdate_node1]; exact h1
        · rw [ChannelView.applyUpdate_node2]; exact h2
        · rw [ChannelView.applyUpdate_capacitySat]; exact hcap
      · rw [admitGossip_update_of_invalid verify ns u hsig] at hv ⊢
        exact h v hv
  | nodeAnnouncement n =>
      intro v hv
      by_cases hsig : n.signatureValid verify
      · rw [admitGossip_node_of_valid verify ns n hsig] at hv ⊢
        rcases h v hv with ⟨b, hb, hbsig, hscid, h1, h2, hcap⟩
        exact ⟨b, by simpa [applyGossip] using hb, hbsig, hscid, h1, h2, hcap⟩
      · rw [admitGossip_node_of_invalid verify ns n hsig] at hv ⊢
        exact h v hv

/-- A `channel_announcement` step of `admitGossip` preserves update
attribution: the update list is unchanged and the announcement list grows, so
every old attribution witness remains present. -/
theorem admitGossip_announcement_preserves_updates (verify : SigVerifier)
    (ns : GossipNetwork) (a : ChannelAnnellation)
    (h : StoreUpdatesAttributed verify ns.gossip) :
    StoreUpdatesAttributed verify
      (admitGossip verify ns (.channelAnnouncement a)).gossip := by
  intro u hu
  by_cases hsig : a.signaturesValid verify
  · rw [admitGossip_announcement_of_valid verify ns a hsig] at hu
    rw [applyGossip_updates_eq] at hu
    rcases h u hu with ⟨husig, huk⟩
    refine ⟨husig, GossipState.updateKeyAnnounced_mono ?_ huk⟩
    intro b hb
    rw [admitGossip_announcement_of_valid verify ns a hsig,
      applyGossip_announcements_eq]
    exact List.mem_cons_of_mem a hb
  · rw [admitGossip_announcement_of_invalid verify ns a hsig] at hu ⊢
    exact h u hu

/-- A `node_announcement` step of `admitGossip` preserves update attribution:
neither the update list nor the announcement list changes. -/
theorem admitGossip_node_preserves_updates (verify : SigVerifier)
    (ns : GossipNetwork) (n : NodeAnnouncement)
    (h : StoreUpdatesAttributed verify ns.gossip) :
    StoreUpdatesAttributed verify
      (admitGossip verify ns (.nodeAnnouncement n)).gossip := by
  intro u hu
  by_cases hsig : n.signatureValid verify
  · rw [admitGossip_node_of_valid verify ns n hsig] at hu
    rw [applyGossip_updates_eq] at hu
    rcases h u hu with ⟨husig, huk⟩
    refine ⟨husig, GossipState.updateKeyAnnounced_mono ?_ huk⟩
    intro b hb
    rw [admitGossip_node_of_valid verify ns n hsig,
      applyGossip_announcements_eq]
    exact hb
  · rw [admitGossip_node_of_invalid verify ns n hsig] at hu ⊢
    exact h u hu

/-! ### The attributed `channel_update` branch -/

/-- An attributed update step preserves the view-backing invariant. -/
theorem attributed_update_preserves_views_backed (verify : SigVerifier)
    (ns : GossipNetwork) (u : ChannelUpdate) (h : ViewsBacked verify ns) :
    ViewsBacked verify
      { gossip := applyGossip ns.gossip (.channelUpdate u)
        views := ns.views.map fun v => v.applyUpdate u } := by
  intro v hv
  rcases List.mem_map.mp hv with ⟨w, hw, rfl⟩
  rcases h w hw with ⟨b, hb, hbsig, hscid, h1, h2, hcap⟩
  refine ⟨b, ?_, hbsig, ?_, ?_, ?_, ?_⟩
  · show b ∈ (ns.gossip.applyUpdate u).announcements
    rw [GossipState.applyUpdate_announcements]
    exact hb
  · rw [ChannelView.applyUpdate_scid]; exact hscid
  · rw [ChannelView.applyUpdate_node1]; exact h1
  · rw [ChannelView.applyUpdate_node2]; exact h2
  · rw [ChannelView.applyUpdate_capacitySat]; exact hcap

/-- **A `channel_update` store step preserves update attribution** when the
update itself passes the attributed gate.  This is the exact place where the
new admission check is used: the inserted update has both `u.signatureValid`
and `s.updateKeyAnnounced u`, while old updates keep their witnesses. -/
theorem applyGossip_update_preserves_updates (verify : SigVerifier)
    (s : GossipState) (u : ChannelUpdate)
    (h : StoreUpdatesAttributed verify s)
    (hsig : u.signatureValid verify) (hk : s.updateKeyAnnounced u) :
    StoreUpdatesAttributed verify (applyGossip s (.channelUpdate u)) := by
  intro v hv
  have hann : (applyGossip s (.channelUpdate u)).announcements = s.announcements := by
    show (s.applyUpdate u).announcements = s.announcements
    exact GossipState.applyUpdate_announcements s u
  have hmono : ∀ b ∈ s.announcements,
      b ∈ (applyGossip s (.channelUpdate u)).announcements := by
    intro b hb
    rw [hann]
    exact hb
  by_cases hnew : s.latestUpdateTimestamp < u.timestamp
  · have hupd : (applyGossip s (.channelUpdate u)).updates = u :: s.updates := by
      show (s.applyUpdate u).updates = u :: s.updates
      exact GossipState.applyUpdate_new s u hnew
    rw [hupd] at hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact ⟨hsig, GossipState.updateKeyAnnounced_mono hmono hk⟩
    · rcases h v hv with ⟨hvsig, hvk⟩
      exact ⟨hvsig, GossipState.updateKeyAnnounced_mono hmono hvk⟩
  · have hsame : (applyGossip s (.channelUpdate u)).updates = s.updates := by
      show (s.applyUpdate u).updates = s.updates
      rw [GossipState.applyUpdate_stale s u (Nat.le_of_not_lt hnew)]
    rw [hsame] at hv
    rcases h v hv with ⟨hvsig, hvk⟩
    exact ⟨hvsig, GossipState.updateKeyAnnounced_mono hmono hvk⟩

/-- An attributed update step preserves the announcement-store invariant. -/
theorem attributed_update_preserves_store (verify : SigVerifier)
    (ns : GossipNetwork) (u : ChannelUpdate)
    (h : StoreAnnouncementsValid verify ns.gossip) :
    StoreAnnouncementsValid verify
      (applyGossip ns.gossip (.channelUpdate u)) := by
  intro a ha
  have hann : (applyGossip ns.gossip (.channelUpdate u)).announcements =
      ns.gossip.announcements := by
    show (ns.gossip.applyUpdate u).announcements = ns.gossip.announcements
    exact GossipState.applyUpdate_announcements ns.gossip u
  rw [hann] at ha
  exact h a ha

/-- The full attributed step preserves the combined invariant. -/
theorem admitGossipAttributed_preserves (verify : SigVerifier)
    (ns : GossipNetwork) (m : GossipMessage) (h : AttributedAdmitted verify ns) :
    AttributedAdmitted verify (admitGossipAttributed verify ns m) := by
  rcases h with ⟨hstore, hviews, hupdates⟩
  cases m with
  | channelAnnouncement a =>
      exact ⟨admitGossip_preserves_store verify ns (.channelAnnouncement a) hstore,
        admitGossip_preserves_views_backed verify ns (.channelAnnouncement a) hviews,
        admitGossip_announcement_preserves_updates verify ns a hupdates⟩
  | channelUpdate u =>
      by_cases hgate : u.signatureValid verify ∧ ns.gossip.updateKeyAnnounced u
      · rw [admitGossipAttributed_update_of_attributed verify ns u hgate.1 hgate.2]
        exact ⟨attributed_update_preserves_store verify ns u hstore,
          attributed_update_preserves_views_backed verify ns u hviews,
          applyGossip_update_preserves_updates verify ns.gossip u hupdates
            hgate.1 hgate.2⟩
      · rw [admitGossipAttributed_update_of_rejected verify ns u hgate]
        exact ⟨hstore, hviews, hupdates⟩
  | nodeAnnouncement n =>
      exact ⟨admitGossip_preserves_store verify ns (.nodeAnnouncement n) hstore,
        admitGossip_preserves_views_backed verify ns (.nodeAnnouncement n) hviews,
        admitGossip_node_preserves_updates verify ns n hupdates⟩

/-- **The invariant of every attributed-reachable state.** -/
theorem reachableAttributed_invariant {verify : SigVerifier} {ns : GossipNetwork}
    (h : ReachableAttributed verify ns) : AttributedAdmitted verify ns := by
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
      exact admitGossipAttributed_preserves verify _ _ ih

/-- Reachable attributed states have a store in which every announcement
verifies (the S3-RT006 store invariant, preserved by the attributed path). -/
theorem reachableAttributed_store_valid {verify : SigVerifier}
    {ns : GossipNetwork} (h : ReachableAttributed verify ns) :
    StoreAnnouncementsValid verify ns.gossip :=
  (reachableAttributed_invariant h).1

/-- Reachable attributed states have only announcement-backed views. -/
theorem reachableAttributed_views_backed {verify : SigVerifier}
    {ns : GossipNetwork} (h : ReachableAttributed verify ns) :
    ViewsBacked verify ns :=
  (reachableAttributed_invariant h).2.1

/-- **Every stored update is signature-valid and attributed.**  In every
attributed-reachable state, each stored `channel_update` has a verifying
signature and a signing key that some stored announcement for the same channel
names as `nodeKey1` or `nodeKey2`. -/
theorem reachableAttributed_updates_attributed {verify : SigVerifier}
    {ns : GossipNetwork} (h : ReachableAttributed verify ns) :
    StoreUpdatesAttributed verify ns.gossip :=
  (reachableAttributed_invariant h).2.2

/-- The same statement with the attribution witness made explicit and shown
to be a *valid* announcement (validity follows from reachability, not from
the admission gate). -/
theorem reachableAttributed_updates_signed_by_valid_announcement
    {verify : SigVerifier} {ns : GossipNetwork}
    (h : ReachableAttributed verify ns) :
    ∀ u ∈ ns.gossip.updates,
      u.signatureValid verify ∧
        ∃ a ∈ ns.gossip.announcements,
          a.signaturesValid verify ∧ a.shortChannelId = u.shortChannelId ∧
            a.attributesKey u.signingKey := by
  intro u hu
  rcases reachableAttributed_updates_attributed h u hu with ⟨husig, huk⟩
  rcases huk with ⟨a, ha, hscid, hkey⟩
  exact ⟨husig, ⟨a, ha, reachableAttributed_store_valid h a ha, hscid, hkey⟩⟩

/-! ## 3. The graph-edge statements -/

/-- **`RT-01` graph target, attribution form.**  Every edge of the graph of an
attributed-reachable state is backed by a valid announcement (the S3-RT006
edge guarantee), and every stored update for that edge's channel is
signature-valid with a signing key attributed by a valid announcement for the
same `short_channel_id`.

The second conjunct is the new key-attribution content: the signature gate
alone (`admitGossip`) did not provide it. -/
theorem gossip_graph_edges_update_attributed (verify : SigVerifier)
    (ns : GossipNetwork) (h : ReachableAttributed verify ns) :
    ∀ e ∈ ns.graph.edges, ∀ u ∈ ns.gossip.updates,
      u.shortChannelId = e.shortChannelId →
        u.signatureValid verify ∧
          ∃ a ∈ ns.gossip.announcements,
            a.signaturesValid verify ∧ a.shortChannelId = e.shortChannelId ∧
              a.attributesKey u.signingKey := by
  intro e he u hu hscid
  rcases reachableAttributed_updates_attributed h u hu with ⟨husig, huk⟩
  rcases huk with ⟨a, ha, hascid, hkey⟩
  exact ⟨husig, ⟨a, ha, reachableAttributed_store_valid h a ha,
    hascid.trans hscid, hkey⟩⟩

/-- The edge itself is backed by a valid announcement with the exact
endpoints and capacity (S3-RT006's `gossip_graph_edges_backed`, instantiated
for the attributed transition). -/
theorem gossip_graph_edges_backed_attributed (verify : SigVerifier)
    (ns : GossipNetwork) (h : ReachableAttributed verify ns) :
    ∀ e ∈ ns.graph.edges, ∃ a ∈ ns.gossip.announcements,
      announcementValid verify a ∧ e.shortChannelId = a.shortChannelId ∧
        e.node1 = a.node1 ∧ e.node2 = a.node2 ∧
          e.capacitySat = a.capacitySat := by
  intro e he
  have he' : e ∈ ns.views.map ChannelView.edge := he
  rcases List.mem_map.mp he' with ⟨v, hv, rfl⟩
  rcases reachableAttributed_views_backed h v hv with
    ⟨a, ha, hsig, hscid, h1, h2, hcap⟩
  exact ⟨a, ha, hsig, hscid, h1, h2, hcap⟩

/-- Consistency of the announced data for one channel: any two stored
announcements with the same `short_channel_id` agree on both graph endpoints
and both BOLT 7 node keys.

This is an **explicit hypothesis**, not a transition invariant.  Wave A is
append-only and does not deduplicate announcements for a channel
(`GossipProps.uniqueBindings` records the weaker endpoint-only gap).  It is
needed only for the endpoint-level attribution theorem below, where the
update's key witness and the edge's backing announcement must be the same
channel binding. -/
def AttributionConsistent (s : GossipState) : Prop :=
  ∀ a ∈ s.announcements, ∀ b ∈ s.announcements,
    a.shortChannelId = b.shortChannelId →
      a.node1 = b.node1 ∧ a.node2 = b.node2 ∧
        a.nodeKey1 = b.nodeKey1 ∧ a.nodeKey2 = b.nodeKey2

/-- **Endpoint-level key attribution.**  Under the explicit hypotheses

* the store's announcements for one channel are `AttributionConsistent`, and
* every announcement's BOLT 7 keys are owned by its graph nodes
  (`KeyAttribution nodeKeyOf`, the missing `NodeId → PubKey` map of wave A),

the signing key of every stored update for an edge is exactly the announced
key of one of that edge's endpoints:

`u.signingKey = nodeKeyOf e.node1 ∨ u.signingKey = nodeKeyOf e.node2`.

Together with `u.signatureValid verify`, this is the "signed by the announced
node key" statement of `LN-GOSSIP-001`. -/
theorem gossip_graph_edges_update_key_endpoint (verify : SigVerifier)
    (ns : GossipNetwork) (nodeKeyOf : NodeId → PubKey)
    (h : ReachableAttributed verify ns)
    (hconsistent : AttributionConsistent ns.gossip)
    (hka : ∀ a ∈ ns.gossip.announcements, KeyAttribution nodeKeyOf a) :
    ∀ e ∈ ns.graph.edges, ∀ u ∈ ns.gossip.updates,
      u.shortChannelId = e.shortChannelId →
        u.signatureValid verify ∧
          (u.signingKey = nodeKeyOf e.node1 ∨
            u.signingKey = nodeKeyOf e.node2) := by
  intro e he u hu hscid
  have he' : e ∈ ns.views.map ChannelView.edge := he
  rcases List.mem_map.mp he' with ⟨v, hv, rfl⟩
  rcases reachableAttributed_views_backed h v hv with
    ⟨a, ha, hasig, hascid, h1, h2, hcap⟩
  rcases reachableAttributed_updates_attributed h u hu with ⟨husig, huk⟩
  rcases huk with ⟨b, hb, hbscid, hbkey⟩
  have hsame : b.shortChannelId = a.shortChannelId := by
    rw [hbscid]
    exact hscid.trans hascid
  rcases hconsistent b hb a ha hsame with ⟨hbn1, hbn2, hbk1, hbk2⟩
  have hka_a := hka a ha
  have hkey_a : u.signingKey = a.nodeKey1 ∨ u.signingKey = a.nodeKey2 := by
    rcases hbkey with hk | hk
    · exact Or.inl (hk.symm.trans hbk1)
    · exact Or.inr (hk.symm.trans hbk2)
  refine ⟨husig, ?_⟩
  rcases hkey_a with hk | hk
  · exact Or.inl (by
      rw [show (v.edge).node1 = a.node1 from h1]
      exact hk.trans hka_a.1.symm)
  · exact Or.inr (by
      rw [show (v.edge).node2 = a.node2 from h2]
      exact hk.trans hka_a.2.symm)

/-! ## 4. Relation to the existing predicates

The routing-level relation added in `LnLean/Routing/Gossip.lean` is
definitionally the wave-A proof-layer predicate from
`LnLean.Proofs.Routing.GossipProps` and the `ModelHardening.F05` spelling.
The bridge theorems make the integration mechanical: a caller may keep using
any of the three names. -/

/-- The routing-level `GossipState.updateKeyAnnounced` is exactly the
proof-layer `GossipProps.updateKeyAnnounced`. -/
theorem updateKeyAnnounced_iff_gossipProps (s : GossipState) (u : ChannelUpdate) :
    s.updateKeyAnnounced u ↔ GossipProps.updateKeyAnnounced s u :=
  Iff.rfl

/-- The routing-level relation, unfolded into the two announced-key
equalities used by the admission path. -/
theorem updateKeyAnnounced_iff_exists_key (s : GossipState) (u : ChannelUpdate) :
    s.updateKeyAnnounced u ↔
      ∃ a ∈ s.announcements, a.shortChannelId = u.shortChannelId ∧
        (a.nodeKey1 = u.signingKey ∨ a.nodeKey2 = u.signingKey) :=
  Iff.rfl

/-! ## 5. Non-vacuity and the raw/gated contrast -/

private def acceptingVerifier : SigVerifier := fun _ _ _ => true

private def keyA : PubKey := ⟨ByteArray.mk #[1]⟩

private def keyB : PubKey := ⟨ByteArray.mk #[2]⟩

private def sampleScid : ShortChannelId := ⟨1, 2, 3⟩

private def emptySig : GossipSignature := ⟨ByteArray.empty⟩

private def emptyStore : GossipState := ⟨[], [], []⟩

private def emptyNetwork : GossipNetwork := { gossip := emptyStore, views := [] }

private def sampleAnnouncement : ChannelAnnellation :=
  { shortChannelId := sampleScid
    node1 := ⟨0⟩
    node2 := ⟨1⟩
    nodeKey1 := keyA
    nodeKey2 := keyB
    bitcoinKey1 := keyA
    bitcoinKey2 := keyB
    capacitySat := 1000
    digest := ByteArray.empty
    nodeSignature1 := emptySig
    nodeSignature2 := emptySig
    bitcoinSignature1 := emptySig
    bitcoinSignature2 := emptySig }

private def sampleUpdate : ChannelUpdate :=
  { shortChannelId := sampleScid
    timestamp := 1
    messageFlags := 0
    channelFlags := 0
    cltvDelta := 1
    htlcMinimumMsat := Msat.zero
    feeBaseMsat := Msat.zero
    feeProportionalMillionths := 0
    htlcMaximumMsat := Msat.MAX
    signingKey := keyA
    digest := ByteArray.empty
    signature := emptySig }

private theorem sampleAnnouncement_valid :
    sampleAnnouncement.signaturesValid acceptingVerifier := by
  simp [ChannelAnnellation.signaturesValid, signatureValid, acceptingVerifier]

private noncomputable def announcedNetwork : GossipNetwork :=
  admitGossipAttributed acceptingVerifier emptyNetwork
    (.channelAnnouncement sampleAnnouncement)

private noncomputable def updatedNetwork : GossipNetwork :=
  admitGossipAttributed acceptingVerifier announcedNetwork (.channelUpdate sampleUpdate)

private theorem announcedNetwork_gossip :
    announcedNetwork.gossip =
      applyGossip emptyStore (.channelAnnouncement sampleAnnouncement) := by
  unfold announcedNetwork
  rw [admitGossipAttributed_announcement]
  rw [admitGossip_announcement_of_valid acceptingVerifier emptyNetwork
    sampleAnnouncement sampleAnnouncement_valid]
  rfl

private theorem sampleUpdate_announced_at_announcedNetwork :
    announcedNetwork.gossip.updateKeyAnnounced sampleUpdate := by
  rw [announcedNetwork_gossip]
  refine GossipState.updateKeyAnnounced_of_mem (a := sampleAnnouncement) ?_ rfl
    (Or.inl rfl)
  simp [applyGossip]

private theorem sampleUpdate_in_updatedNetwork :
    sampleUpdate ∈ updatedNetwork.gossip.updates := by
  unfold updatedNetwork
  rw [admitGossipAttributed_update_of_attributed acceptingVerifier
    announcedNetwork sampleUpdate (by
      simp [ChannelUpdate.signatureValid, signatureValid, acceptingVerifier])
    sampleUpdate_announced_at_announcedNetwork]
  show sampleUpdate ∈ (announcedNetwork.gossip.applyUpdate sampleUpdate).updates
  rw [GossipState.applyUpdate_new]
  · exact List.mem_cons_self ..
  · rw [announcedNetwork_gossip]
    simp [applyGossip, GossipState.latestUpdateTimestamp, latestTimestamp, emptyStore,
      sampleUpdate]

private theorem updatedNetwork_reachable :
    ReachableAttributed acceptingVerifier updatedNetwork := by
  unfold updatedNetwork announcedNetwork
  exact ReachableAttributed.step
    (ReachableAttributed.step ReachableAttributed.empty)

private theorem sampleUpdate_valid :
    sampleUpdate.signatureValid acceptingVerifier := by
  simp [ChannelUpdate.signatureValid, signatureValid, acceptingVerifier]

/-- **Non-vacuity of attributed admission.**  There is a genuinely reachable
attributed state that stores a signature-valid update whose signing key is
announced by a valid stored announcement. -/
theorem reachableAttributed_stores_attributed_update :
    ∃ (verify : SigVerifier) (ns : GossipNetwork) (u : ChannelUpdate),
      ReachableAttributed verify ns ∧ u ∈ ns.gossip.updates ∧
        u.signatureValid verify ∧ ns.gossip.updateKeyAnnounced u := by
  refine ⟨acceptingVerifier, updatedNetwork, sampleUpdate,
    updatedNetwork_reachable, sampleUpdate_in_updatedNetwork,
    sampleUpdate_valid, ?_⟩
  exact (reachableAttributed_updates_attributed updatedNetwork_reachable
    sampleUpdate sampleUpdate_in_updatedNetwork).2

/-- **Non-vacuity of the graph statement.**  The attributed-reachable witness
has a non-empty graph and its stored update satisfies the attributed edge
statement. -/
theorem reachableAttributed_graph_nonempty_and_attributed :
    ∃ (verify : SigVerifier) (ns : GossipNetwork),
      ReachableAttributed verify ns ∧ ns.graph.edges ≠ [] ∧
        ∀ e ∈ ns.graph.edges, ∀ u ∈ ns.gossip.updates,
          u.shortChannelId = e.shortChannelId →
            u.signatureValid verify ∧
              ∃ a ∈ ns.gossip.announcements,
                a.signaturesValid verify ∧
                  a.shortChannelId = e.shortChannelId ∧
                    a.attributesKey u.signingKey := by
  refine ⟨acceptingVerifier, updatedNetwork, updatedNetwork_reachable, ?_,
    gossip_graph_edges_update_attributed acceptingVerifier updatedNetwork
      updatedNetwork_reachable⟩
  have hv : admittedChannelView sampleAnnouncement ∈ announcedNetwork.views := by
    unfold announcedNetwork
    rw [admitGossipAttributed_announcement,
      admitGossip_announcement_of_valid acceptingVerifier emptyNetwork
        sampleAnnouncement sampleAnnouncement_valid]
    simp
  unfold updatedNetwork
  rw [admitGossipAttributed_update_of_attributed acceptingVerifier
    announcedNetwork sampleUpdate sampleUpdate_valid
    sampleUpdate_announced_at_announcedNetwork]
  intro hnil
  unfold GossipNetwork.graph viewGraph at hnil
  dsimp only at hnil
  have hmem : ((admittedChannelView sampleAnnouncement).applyUpdate sampleUpdate).edge ∈
      (announcedNetwork.views.map fun v => v.applyUpdate sampleUpdate).map
        ChannelView.edge :=
    List.mem_map.mpr
      ⟨_, List.mem_map.mpr ⟨_, hv, rfl⟩, rfl⟩
  rw [hnil] at hmem
  simp at hmem

/-- **The attributed gate rejects an unannounced update.**  With an
always-accepting verifier, an empty store, and an update whose key was never
announced, the attributed step is a no-op. -/
theorem unannounced_update_rejected :
    ∃ (verify : SigVerifier) (ns : GossipNetwork) (u : ChannelUpdate),
      ¬ ns.gossip.updateKeyAnnounced u ∧
        admitGossipAttributed verify ns (.channelUpdate u) = ns := by
  refine ⟨acceptingVerifier, emptyNetwork, sampleUpdate, ?_, ?_⟩
  · rintro ⟨a, ha, _⟩
    simp [emptyNetwork, emptyStore] at ha
  · exact admitGossipAttributed_update_of_unannounced acceptingVerifier
      emptyNetwork sampleUpdate (by
        rintro ⟨a, ha, _⟩
        simp [emptyNetwork, emptyStore] at ha)

/-- **Raw `applyGossip` is untouched.**  The same unannounced update is still
stored by the wave-A raw transition.  This preserves the S3-RT006 raw-store
caveat: attribution is an additional admission path, not a change to
`applyGossip` or its theorems. -/
theorem raw_applyGossip_accepts_unannounced_update :
    ∃ (s : GossipState) (u : ChannelUpdate),
      ¬ s.updateKeyAnnounced u ∧
        (applyGossip s (.channelUpdate u)).updates = u :: s.updates := by
  refine ⟨emptyStore, sampleUpdate, ?_, ?_⟩
  · rintro ⟨a, ha, _⟩
    simp [emptyStore] at ha
  · show (emptyStore.applyUpdate sampleUpdate).updates =
      sampleUpdate :: emptyStore.updates
    rw [GossipState.applyUpdate_new]
    simp [GossipState.latestUpdateTimestamp, latestTimestamp, emptyStore, sampleUpdate]

end LnLean.Proofs.Routing.GossipAttributionTargets
