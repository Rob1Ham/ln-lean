import LnLean.Proofs.Routing.GossipCanonicalTargets

/-!
# LnLean.Proofs.Routing.GossipRawRefinementTargets

Wave-7 lane `S7-RT-RAW`, open issue `RT-01`.

Wave 6 (`GossipCanonicalTargets`) supplied a canonicalising admission
transition `admitGossipCanonical` over a `CanonicalNetwork` (raw gossip store +
views + explicit `NodeId → PubKey` registration map).  That transition is
**not** a refinement of raw `applyGossip` as a function:

* raw `applyGossip` appends every announcement and every update;
* it has no signature gate, no node-key registration gate, and no per-direction
  supersession gate;
* its only clock is the single global `latestUpdateTimestamp`.

This module makes the strongest true statement instead.

## 1. A store-level canonical wrapper

`CanonicalStore` is the `CanonicalNetwork` projection that matters for the
store: the gossip state plus the node-key registration map.  Views are routing
materialisations, not store content, and are omitted.

`applyGossipCanonicalStore` is the same admission policy as
`admitGossipCanonical`, specialised to a store.  The theorems
`applyGossipCanonicalStore_gossip_toNetwork` and
`applyGossipCanonicalStore_nodeKeyOf_toNetwork` prove that it is *exactly* the
gossip/registration projection of the wave-6 transition, so this wrapper cannot
drift from the canonical path.

`ReachableCanonicalStore` closes the wrapper transition from the empty store.
Its invariant extends the wave-6 `CanonicalAdmitted` invariant with the
per-direction slot uniqueness that the canonical insertion maintains, and every
reachable store is in canonical selector shape.

## 2. The refinement square

For every message, on a store already in canonical selector shape, when the
canonical admission gates hold and the raw global clock admits the update,

  `canonicalStoreView (applyGossip s m) = (applyGossipCanonicalStore verify s m).gossip`.

This is the sharp refinement: observing a raw step through the canonical
selector is the canonical store step.  It needs the gates because otherwise the
canonical path is a no-op while the raw path mutates the store.

On the strictly smaller common domain where the incoming announcement has a
fresh `short_channel_id` or the incoming update has a fresh directional slot,
raw `applyGossip` and the canonical store step agree literally:

  `applyGossip s m = (applyGossipCanonicalStore verify s m).gossip`.

## 3. Boundary

`canonical_admission_strictly_weaker_than_raw_clock` exhibits a canonically
reachable store with announcements for two channels and a stored update on the
second.  A new update on the first channel, with a *lower* timestamp than the
global clock, is admitted by the canonical per-slot gate but ignored by the raw
global clock.  Hence the raw global clock is strictly stronger than the
canonical per-slot gate, and no theorem can identify the two transitions
without an extra hypothesis.

`no_canonical_preserving_raw_announcement_extension` records the matching
impossibility: no transition that keeps raw append semantics for
`channel_announcement` can preserve `CanonicalAnnouncements` from the empty
store, because raw append has no replacement step.

## 4. Preserved counterexamples

The raw-store conflict counterexamples of waves 4/5 are re-exported unchanged,
and the canonical transition's rejection of the conflicting announcement is
re-exported next to them.

No `sorry`, no `axiom`, no `admit`, no `native_decide`, no `unsafe`, no
`@[implemented_by]`.
-/

namespace LnLean.Proofs.Routing.GossipRawRefinementTargets

open LnLean.Routing
open LnLean.Routing.GossipProps
open LnLean.Proofs.Routing.GossipTargets
open LnLean.Proofs.Routing.GossipAttributionTargets
open LnLean.Proofs.Routing.GossipKeyConsistencyTargets
open LnLean.Proofs.Routing.GossipCanonicalTargets
open Classical

set_option autoImplicit false

/-! ## 1. The canonical store wrapper -/

/-- The store part of a canonical network: the raw gossip store and the
explicit `NodeId → PubKey` registration map.  Routing views are omitted because
they are derived materialisations, not store content. -/
structure CanonicalStore where
  /-- The gossip store (announcements, updates, node announcements). -/
  gossip : GossipState
  /-- The explicit node-key registration map. -/
  nodeKeyOf : NodeId → PubKey

namespace CanonicalStore

/-- Embed a store into a canonical network with no materialised views.  The
empty view list is irrelevant to every store transition; view irrelevance is
proved below. -/
def toNetwork (cs : CanonicalStore) : CanonicalNetwork :=
  { gossip := cs.gossip, views := [], nodeKeyOf := cs.nodeKeyOf }

end CanonicalStore

/-- **Store-level canonical admission.**  This is the wave-6
`admitGossipCanonical` policy restricted to the gossip store and registration
map: announcements are signature-gated, endpoint-distinct,
registration-compatible and update-authorising, and replace by channel;
updates are signature-gated, direction-attributed and strictly newer in their
per-direction slot, and replace that slot; node announcements are
signature-gated appends. -/
noncomputable def applyGossipCanonicalStore (verify : SigVerifier)
    (cs : CanonicalStore) : GossipMessage → CanonicalStore
  | .channelAnnouncement a =>
      if a.signaturesValid verify ∧ a.node1 ≠ a.node2 ∧
          cs.gossip.CompatibleWithStore a ∧
          UpdatesAuthorizedBy cs.gossip a then
        { gossip := { cs.gossip with
            announcements := insertReplacing a cs.gossip.announcements }
          nodeKeyOf := bindNodeKeys cs.nodeKeyOf a }
      else cs
  | .channelUpdate u =>
      if u.signatureValid verify ∧
          cs.gossip.updateKeyAnnouncedDirectional u ∧
          UpdateSupersedes u cs.gossip.updates then
        { gossip := { cs.gossip with
            updates := insertUpdateCanonical u cs.gossip.updates }
          nodeKeyOf := cs.nodeKeyOf }
      else cs
  | .nodeAnnouncement n =>
      if n.signatureValid verify then
        { gossip := { cs.gossip with
            nodeAnnouncements := n :: cs.gossip.nodeAnnouncements }
          nodeKeyOf := cs.nodeKeyOf }
      else cs

/-! ### Projection to the wave-6 transition -/

/-- The store wrapper's gossip projection is exactly the wave-6 canonical
transition's gossip projection.  The empty view list in `CanonicalStore.toNetwork`
does not affect the store. -/
theorem applyGossipCanonicalStore_gossip_toNetwork (verify : SigVerifier)
    (cs : CanonicalStore) (m : GossipMessage) :
    (applyGossipCanonicalStore verify cs m).gossip =
      (admitGossipCanonical verify cs.toNetwork m).gossip := by
  cases m with
  | channelAnnouncement a =>
      by_cases h : a.signaturesValid verify ∧ a.node1 ≠ a.node2 ∧
          cs.gossip.CompatibleWithStore a ∧
          UpdatesAuthorizedBy cs.gossip a
      · simp [applyGossipCanonicalStore, CanonicalStore.toNetwork,
          admitGossipCanonical, h]
      · simp [applyGossipCanonicalStore, CanonicalStore.toNetwork,
          admitGossipCanonical, h]
  | channelUpdate u =>
      by_cases h : u.signatureValid verify ∧
          cs.gossip.updateKeyAnnouncedDirectional u ∧
          UpdateSupersedes u cs.gossip.updates
      · simp [applyGossipCanonicalStore, CanonicalStore.toNetwork,
          admitGossipCanonical, h]
      · simp [applyGossipCanonicalStore, CanonicalStore.toNetwork,
          admitGossipCanonical, h]
  | nodeAnnouncement n =>
      by_cases h : n.signatureValid verify
      · simp [applyGossipCanonicalStore, CanonicalStore.toNetwork,
          admitGossipCanonical, h]
      · simp [applyGossipCanonicalStore, CanonicalStore.toNetwork,
          admitGossipCanonical, h]

/-- The store wrapper's registration projection is exactly the wave-6 canonical
transition's registration projection. -/
theorem applyGossipCanonicalStore_nodeKeyOf_toNetwork (verify : SigVerifier)
    (cs : CanonicalStore) (m : GossipMessage) :
    (applyGossipCanonicalStore verify cs m).nodeKeyOf =
      (admitGossipCanonical verify cs.toNetwork m).nodeKeyOf := by
  cases m with
  | channelAnnouncement a =>
      by_cases h : a.signaturesValid verify ∧ a.node1 ≠ a.node2 ∧
          cs.gossip.CompatibleWithStore a ∧
          UpdatesAuthorizedBy cs.gossip a
      · simp [applyGossipCanonicalStore, CanonicalStore.toNetwork,
          admitGossipCanonical, h]
      · simp [applyGossipCanonicalStore, CanonicalStore.toNetwork,
          admitGossipCanonical, h]
  | channelUpdate u =>
      by_cases h : u.signatureValid verify ∧
          cs.gossip.updateKeyAnnouncedDirectional u ∧
          UpdateSupersedes u cs.gossip.updates
      · simp [applyGossipCanonicalStore, CanonicalStore.toNetwork,
          admitGossipCanonical, h]
      · simp [applyGossipCanonicalStore, CanonicalStore.toNetwork,
          admitGossipCanonical, h]
  | nodeAnnouncement n =>
      by_cases h : n.signatureValid verify
      · simp [applyGossipCanonicalStore, CanonicalStore.toNetwork,
          admitGossipCanonical, h]
      · simp [applyGossipCanonicalStore, CanonicalStore.toNetwork,
          admitGossipCanonical, h]

/-! ### Transition equations -/

/-- An announcement passing every canonical gate replaces by channel and binds
both endpoint keys. -/
theorem applyGossipCanonicalStore_announcement_of_admitted
    (verify : SigVerifier) (cs : CanonicalStore) (a : ChannelAnnellation)
    (h : a.signaturesValid verify ∧ a.node1 ≠ a.node2 ∧
      cs.gossip.CompatibleWithStore a ∧ UpdatesAuthorizedBy cs.gossip a) :
    applyGossipCanonicalStore verify cs (.channelAnnouncement a) =
      { gossip := { cs.gossip with
          announcements := insertReplacing a cs.gossip.announcements }
        nodeKeyOf := bindNodeKeys cs.nodeKeyOf a } := by
  simp [applyGossipCanonicalStore, h]

/-- An announcement failing any canonical gate is a no-op. -/
theorem applyGossipCanonicalStore_announcement_of_rejected
    (verify : SigVerifier) (cs : CanonicalStore) (a : ChannelAnnellation)
    (h : ¬ (a.signaturesValid verify ∧ a.node1 ≠ a.node2 ∧
      cs.gossip.CompatibleWithStore a ∧ UpdatesAuthorizedBy cs.gossip a)) :
    applyGossipCanonicalStore verify cs (.channelAnnouncement a) = cs := by
  simp [applyGossipCanonicalStore, h]

/-- An update passing every canonical gate replaces its directional slot. -/
theorem applyGossipCanonicalStore_update_of_admitted
    (verify : SigVerifier) (cs : CanonicalStore) (u : ChannelUpdate)
    (h : u.signatureValid verify ∧
      cs.gossip.updateKeyAnnouncedDirectional u ∧
      UpdateSupersedes u cs.gossip.updates) :
    applyGossipCanonicalStore verify cs (.channelUpdate u) =
      { gossip := { cs.gossip with
          updates := insertUpdateCanonical u cs.gossip.updates }
        nodeKeyOf := cs.nodeKeyOf } := by
  simp [applyGossipCanonicalStore, h]

/-- An update failing any canonical gate is a no-op. -/
theorem applyGossipCanonicalStore_update_of_rejected
    (verify : SigVerifier) (cs : CanonicalStore) (u : ChannelUpdate)
    (h : ¬ (u.signatureValid verify ∧
      cs.gossip.updateKeyAnnouncedDirectional u ∧
      UpdateSupersedes u cs.gossip.updates)) :
    applyGossipCanonicalStore verify cs (.channelUpdate u) = cs := by
  simp [applyGossipCanonicalStore, h]

/-- A verifying node announcement is appended. -/
theorem applyGossipCanonicalStore_node_of_valid
    (verify : SigVerifier) (cs : CanonicalStore) (n : NodeAnnouncement)
    (h : n.signatureValid verify) :
    applyGossipCanonicalStore verify cs (.nodeAnnouncement n) =
      { gossip := { cs.gossip with
          nodeAnnouncements := n :: cs.gossip.nodeAnnouncements }
        nodeKeyOf := cs.nodeKeyOf } := by
  simp [applyGossipCanonicalStore, h]

/-- A node announcement failing the signature gate is a no-op. -/
theorem applyGossipCanonicalStore_node_of_invalid
    (verify : SigVerifier) (cs : CanonicalStore) (n : NodeAnnouncement)
    (h : ¬ n.signatureValid verify) :
    applyGossipCanonicalStore verify cs (.nodeAnnouncement n) = cs := by
  simp [applyGossipCanonicalStore, h]

/-! ## 2. Message-level admission and raw clock -/

/-- The canonical admission gates, as a message-indexed predicate.  It is
definitionally the condition used by `applyGossipCanonicalStore`. -/
def CanonicalMessageAdmitted (verify : SigVerifier) (cs : CanonicalStore) :
    GossipMessage → Prop
  | .channelAnnouncement a =>
      a.signaturesValid verify ∧ a.node1 ≠ a.node2 ∧
        cs.gossip.CompatibleWithStore a ∧ UpdatesAuthorizedBy cs.gossip a
  | .channelUpdate u =>
      u.signatureValid verify ∧
        cs.gossip.updateKeyAnnouncedDirectional u ∧
        UpdateSupersedes u cs.gossip.updates
  | .nodeAnnouncement n => n.signatureValid verify

/-- The raw store's own acceptance test.  Announcements and node announcements
are appended unconditionally; an update must beat the single global clock. -/
def RawClockAdmits (s : GossipState) : GossipMessage → Prop
  | .channelAnnouncement _ => True
  | .channelUpdate u => s.latestUpdateTimestamp < u.timestamp
  | .nodeAnnouncement _ => True

/-- Freshness of a message for the store.  An announcement is fresh when its
`short_channel_id` is absent; an update is fresh when its directional slot is
absent.  Node announcements are always appended by both paths. -/
def FreshMessage (s : GossipState) : GossipMessage → Prop
  | .channelAnnouncement a =>
      ∀ b ∈ s.announcements, b.shortChannelId ≠ a.shortChannelId
  | .channelUpdate u =>
      ∀ v ∈ s.updates,
        ¬ (v.shortChannelId = u.shortChannelId ∧ v.direction = u.direction)
  | .nodeAnnouncement _ => True

/-! ## 3. Reachability and the store invariant -/

/-- A store is canonically reachable when it is obtained from the empty store
(with an arbitrary initial registration map) by finitely many store-level
canonical admissions. -/
inductive ReachableCanonicalStore (verify : SigVerifier) :
    CanonicalStore → Prop
  | empty (nodeKeyOf : NodeId → PubKey) :
      ReachableCanonicalStore verify
        { gossip := ⟨[], [], []⟩, nodeKeyOf := nodeKeyOf }
  | step {cs : CanonicalStore} {m : GossipMessage} :
      ReachableCanonicalStore verify cs →
        ReachableCanonicalStore verify (applyGossipCanonicalStore verify cs m)

/-- The canonical transition's gossip projection does not depend on the
materialised views. -/
theorem admitGossipCanonical_gossip_view_irrel (verify : SigVerifier)
    (g : GossipState) (k : NodeId → PubKey) (vs₁ vs₂ : List ChannelView)
    (m : GossipMessage) :
    (admitGossipCanonical verify
        { gossip := g, views := vs₁, nodeKeyOf := k } m).gossip =
      (admitGossipCanonical verify
        { gossip := g, views := vs₂, nodeKeyOf := k } m).gossip := by
  cases m with
  | channelAnnouncement a =>
      by_cases h : a.signaturesValid verify ∧ a.node1 ≠ a.node2 ∧
          g.CompatibleWithStore a ∧ UpdatesAuthorizedBy g a
      · simp [admitGossipCanonical, h]
      · simp [admitGossipCanonical, h]
  | channelUpdate u =>
      by_cases h : u.signatureValid verify ∧
          g.updateKeyAnnouncedDirectional u ∧
          UpdateSupersedes u g.updates
      · simp [admitGossipCanonical, h]
      · simp [admitGossipCanonical, h]
  | nodeAnnouncement n =>
      by_cases h : n.signatureValid verify
      · simp [admitGossipCanonical, h]
      · simp [admitGossipCanonical, h]

/-- The canonical transition's registration projection does not depend on the
materialised views. -/
theorem admitGossipCanonical_nodeKeyOf_view_irrel (verify : SigVerifier)
    (g : GossipState) (k : NodeId → PubKey) (vs₁ vs₂ : List ChannelView)
    (m : GossipMessage) :
    (admitGossipCanonical verify
        { gossip := g, views := vs₁, nodeKeyOf := k } m).nodeKeyOf =
      (admitGossipCanonical verify
        { gossip := g, views := vs₂, nodeKeyOf := k } m).nodeKeyOf := by
  cases m with
  | channelAnnouncement a =>
      by_cases h : a.signaturesValid verify ∧ a.node1 ≠ a.node2 ∧
          g.CompatibleWithStore a ∧ UpdatesAuthorizedBy g a
      · simp [admitGossipCanonical, h]
      · simp [admitGossipCanonical, h]
  | channelUpdate u =>
      by_cases h : u.signatureValid verify ∧
          g.updateKeyAnnouncedDirectional u ∧
          UpdateSupersedes u g.updates
      · simp [admitGossipCanonical, h]
      · simp [admitGossipCanonical, h]
  | nodeAnnouncement n =>
      by_cases h : n.signatureValid verify
      · simp [admitGossipCanonical, h]
      · simp [admitGossipCanonical, h]

/-! ### Bridge to wave-6 reachability -/

/-- A canonically reachable store is the projection of a canonically reachable
network for some view list.  The view list is irrelevant to the store, which is
why the store wrapper can omit it. -/
theorem reachableCanonicalStore_toNetwork {verify : SigVerifier}
    {cs : CanonicalStore} (h : ReachableCanonicalStore verify cs) :
    ∃ views : List ChannelView, ReachableCanonical verify
      { gossip := cs.gossip, views := views, nodeKeyOf := cs.nodeKeyOf } := by
  induction h with
  | empty k => exact ⟨[], ReachableCanonical.empty k⟩
  | step h ih =>
      rename_i cs' m'
      rcases ih with ⟨views, hviews⟩
      let net := admitGossipCanonical verify
        { gossip := cs'.gossip, views := views, nodeKeyOf := cs'.nodeKeyOf } m'
      let net0 := admitGossipCanonical verify cs'.toNetwork m'
      have hg : net.gossip = net0.gossip :=
        admitGossipCanonical_gossip_view_irrel verify cs'.gossip cs'.nodeKeyOf views []
          m'
      have hk : net.nodeKeyOf = net0.nodeKeyOf :=
        admitGossipCanonical_nodeKeyOf_view_irrel verify cs'.gossip cs'.nodeKeyOf views
          [] m'
      have hnet : CanonicalNetwork.mk net0.gossip net.views net0.nodeKeyOf = net := by
        rcases net with ⟨g, v, k⟩
        simp_all
      refine ⟨net.views, ?_⟩
      rw [applyGossipCanonicalStore_gossip_toNetwork,
        applyGossipCanonicalStore_nodeKeyOf_toNetwork]
      exact hnet.symm ▸ (ReachableCanonical.step hviews (m := m'))

/-! ### Slot uniqueness of reachable canonical updates -/

/-- Announcement admission leaves the update list unchanged. -/
theorem admitGossipCanonical_announcement_updates (verify : SigVerifier)
    (cs : CanonicalNetwork) (a : ChannelAnnellation) :
    (admitGossipCanonical verify cs (.channelAnnouncement a)).gossip.updates =
      cs.gossip.updates := by
  by_cases h : a.signaturesValid verify ∧ a.node1 ≠ a.node2 ∧
      cs.gossip.CompatibleWithStore a ∧ UpdatesAuthorizedBy cs.gossip a
  · rw [admitGossipCanonical_announcement_of_admitted verify cs a h]
  · rw [admitGossipCanonical_announcement_of_rejected verify cs a h]

/-- Update admission either replaces the directional slot or is a no-op. -/
theorem admitGossipCanonical_update_updates (verify : SigVerifier)
    (cs : CanonicalNetwork) (u : ChannelUpdate) :
    (admitGossipCanonical verify cs (.channelUpdate u)).gossip.updates =
      if u.signatureValid verify ∧
          cs.gossip.updateKeyAnnouncedDirectional u ∧
          UpdateSupersedes u cs.gossip.updates then
        insertUpdateCanonical u cs.gossip.updates
      else cs.gossip.updates := by
  by_cases h : u.signatureValid verify ∧
      cs.gossip.updateKeyAnnouncedDirectional u ∧
      UpdateSupersedes u cs.gossip.updates
  · rw [admitGossipCanonical_update_of_admitted verify cs u h]
    simp [h]
  · rw [admitGossipCanonical_update_of_rejected verify cs u h]
    simp [h]

/-- Node-announcement admission leaves the update list unchanged. -/
theorem admitGossipCanonical_node_updates (verify : SigVerifier)
    (cs : CanonicalNetwork) (n : NodeAnnouncement) :
    (admitGossipCanonical verify cs (.nodeAnnouncement n)).gossip.updates =
      cs.gossip.updates := by
  by_cases h : n.signatureValid verify
  · rw [admitGossipCanonical_node_of_valid verify cs n h]
  · rw [admitGossipCanonical_node_of_invalid verify cs n h]

/-- **Every canonically reachable store has at most one update per directional
slot.**  The canonical update step uses `insertUpdateCanonical`; the other
branches do not touch the update list. -/
theorem reachableCanonical_updates_slotUnique {verify : SigVerifier}
    {cs : CanonicalNetwork} (h : ReachableCanonical verify cs) :
    UpdatesSlotUnique cs.gossip.updates := by
  induction h with
  | empty _ => exact updatesSlotUnique_nil
  | step h ih =>
      rename_i cs' m'
      cases m' with
      | channelAnnouncement a =>
          rw [admitGossipCanonical_announcement_updates]
          exact ih
      | channelUpdate u =>
          rw [admitGossipCanonical_update_updates]
          by_cases hg : u.signatureValid verify ∧
              cs'.gossip.updateKeyAnnouncedDirectional u ∧
              UpdateSupersedes u cs'.gossip.updates
          · simp only [hg]
            exact updatesSlotUnique_insertUpdateCanonical ih
          · simp only [hg]
            exact ih
      | nodeAnnouncement n =>
          rw [admitGossipCanonical_node_updates]
          exact ih

/-- The store-level canonical invariant: every component of the wave-6
`CanonicalAdmitted` invariant that concerns the store, plus the per-direction
slot uniqueness maintained by `insertUpdateCanonical`. -/
structure CanonicalStoreAdmitted (verify : SigVerifier)
    (cs : CanonicalStore) : Prop where
  /-- Every stored announcement passes all four signature checks. -/
  storeValid : StoreAnnouncementsValid verify cs.gossip
  /-- Every stored update verifies and is direction-correctly attributed. -/
  updatesAttributed : StoreUpdatesDirectionallyAttributed verify cs.gossip
  /-- The registration map agrees with every stored announcement. -/
  nodeKeys : GossipState.NodeKeyConsistent cs.nodeKeyOf cs.gossip
  /-- At most one stored announcement per `short_channel_id`. -/
  canonical : CanonicalAnnouncements cs.gossip.announcements
  /-- At most one stored update per directional slot. -/
  updatesSlotUnique : UpdatesSlotUnique cs.gossip.updates

/-- **The invariant of every canonically reachable store.** -/
theorem reachableCanonicalStore_invariant {verify : SigVerifier}
    {cs : CanonicalStore} (h : ReachableCanonicalStore verify cs) :
    CanonicalStoreAdmitted verify cs := by
  rcases reachableCanonicalStore_toNetwork h with ⟨views, hviews⟩
  have hinv := reachableCanonical_invariant hviews
  exact
    { storeValid := hinv.storeValid
      updatesAttributed := hinv.updatesAttributed
      nodeKeys := hinv.nodeKeys
      canonical := hinv.canonical
      updatesSlotUnique := reachableCanonical_updates_slotUnique hviews }

/-- Every stored announcement of a reachable canonical store verifies. -/
theorem reachableCanonicalStore_store_valid {verify : SigVerifier}
    {cs : CanonicalStore} (h : ReachableCanonicalStore verify cs) :
    StoreAnnouncementsValid verify cs.gossip :=
  (reachableCanonicalStore_invariant h).storeValid

/-- Every stored update of a reachable canonical store is direction-correctly
attributed.  This is the store-level directional-key theorem `RT-01` asks for:
no `NodeKeyConsistent` or `CanonicalAnnouncements` hypothesis is needed. -/
theorem reachableCanonicalStore_updates_directional {verify : SigVerifier}
    {cs : CanonicalStore} (h : ReachableCanonicalStore verify cs) :
    StoreUpdatesDirectionallyAttributed verify cs.gossip :=
  (reachableCanonicalStore_invariant h).updatesAttributed

/-- The registration map of a reachable canonical store is consistent with
every stored announcement. -/
theorem reachableCanonicalStore_nodeKeyConsistent {verify : SigVerifier}
    {cs : CanonicalStore} (h : ReachableCanonicalStore verify cs) :
    GossipState.NodeKeyConsistent cs.nodeKeyOf cs.gossip :=
  (reachableCanonicalStore_invariant h).nodeKeys

/-- A reachable canonical store has one announcement per channel. -/
theorem reachableCanonicalStore_canonical {verify : SigVerifier}
    {cs : CanonicalStore} (h : ReachableCanonicalStore verify cs) :
    CanonicalAnnouncements cs.gossip.announcements :=
  (reachableCanonicalStore_invariant h).canonical

/-- A reachable canonical store has at most one update per directional slot. -/
theorem reachableCanonicalStore_updates_slotUnique {verify : SigVerifier}
    {cs : CanonicalStore} (h : ReachableCanonicalStore verify cs) :
    UpdatesSlotUnique cs.gossip.updates :=
  (reachableCanonicalStore_invariant h).updatesSlotUnique

/-- **No ambiguous direction-key attribution in a reachable canonical store.**
Two stored updates for the same channel and direction have the same signing key.
This is the store-level uniqueness form of `RT-01`. -/
theorem reachableCanonicalStore_attribution_unique {verify : SigVerifier}
    {cs : CanonicalStore} (h : ReachableCanonicalStore verify cs)
    {u v : ChannelUpdate} (hu : u ∈ cs.gossip.updates)
    (hv : v ∈ cs.gossip.updates)
    (hscid : u.shortChannelId = v.shortChannelId)
    (hdir : u.direction = v.direction) :
    u.signingKey = v.signingKey :=
  canonical_directional_attribution_unique
    (reachableCanonicalStore_canonical h) hscid hdir
    (reachableCanonicalStore_updates_directional h u hu).2
    (reachableCanonicalStore_updates_directional h v hv).2

/-! ## 4. Reachable stores are in canonical selector shape -/

/-- Shape gives duplicate-free announcements. -/
theorem canonicalStoreShape_announcements_nodup {s : GossipState}
    (h : CanonicalStoreShape s) : s.announcements.Nodup := by
  have hnd := selectAnnouncements_nodup s.announcements
  rwa [h.1] at hnd

/-- Shape gives the canonical announcement invariant. -/
theorem canonicalStoreShape_announcements_canonical {s : GossipState}
    (h : CanonicalStoreShape s) : CanonicalAnnouncements s.announcements := by
  have hc := canonical_selectAnnouncements s.announcements
  rwa [h.1] at hc

/-- Shape gives duplicate-free updates. -/
theorem canonicalStoreShape_updates_nodup {s : GossipState}
    (h : CanonicalStoreShape s) : s.updates.Nodup := by
  have hnd := selectUpdates_nodup s.updates
  rwa [h.2] at hnd

/-- Shape gives per-direction slot uniqueness. -/
theorem canonicalStoreShape_updates_slotUnique {s : GossipState}
    (h : CanonicalStoreShape s) : UpdatesSlotUnique s.updates := by
  have hsu := updatesSlotUnique_selectUpdates s.updates
  rwa [h.2] at hsu

/-- **Announcement selection is the identity after replacing a channel in a
canonical-shaped store.** -/
theorem selectAnnouncements_insertReplacing_of_shape {s : GossipState}
    (h : CanonicalStoreShape s) (a : ChannelAnnellation) :
    selectAnnouncements (insertReplacing a s.announcements) =
      insertReplacing a s.announcements := by
  have hfilter_nd : (s.announcements.filter
      (fun b => decide (b.shortChannelId ≠ a.shortChannelId))).Nodup :=
    (canonicalStoreShape_announcements_nodup h).filter _
  have hfilter_canonical : CanonicalAnnouncements
      (s.announcements.filter
        (fun b => decide (b.shortChannelId ≠ a.shortChannelId))) := by
    intro x hx y hy hscid
    exact canonicalStoreShape_announcements_canonical h x
      (List.mem_filter.mp hx).1 y (List.mem_filter.mp hy).1 hscid
  unfold insertReplacing
  rw [selectAnnouncements_cons]
  rw [selectAnnouncements_of_nodup_canonical hfilter_nd hfilter_canonical]
  unfold insertReplacing
  rw [List.filter_eq_self.mpr]
  intro b hb
  exact (List.mem_filter.mp hb).2

/-- **Update selection is the identity after replacing a directional slot in a
canonical-shaped store.** -/
theorem selectUpdates_insertUpdateCanonical_of_shape {s : GossipState}
    (h : CanonicalStoreShape s) (u : ChannelUpdate) :
    selectUpdates (insertUpdateCanonical u s.updates) =
      insertUpdateCanonical u s.updates := by
  have hfilter_nd : (s.updates.filter (fun v => decide
      (¬ (v.shortChannelId = u.shortChannelId ∧
        v.direction = u.direction)))).Nodup :=
    (canonicalStoreShape_updates_nodup h).filter _
  have hfilter_slotUnique : UpdatesSlotUnique (s.updates.filter
      (fun v => decide (¬ (v.shortChannelId = u.shortChannelId ∧
        v.direction = u.direction)))) := by
    intro x hx y hy hscid hdir
    exact canonicalStoreShape_updates_slotUnique h x
      (List.mem_filter.mp hx).1 y (List.mem_filter.mp hy).1 hscid hdir
  unfold insertUpdateCanonical
  rw [selectUpdates_cons]
  rw [selectUpdates_of_nodup_slotUnique hfilter_nd hfilter_slotUnique]
  unfold insertUpdateCanonical
  rw [List.filter_eq_self.mpr]
  intro v hv
  exact (List.mem_filter.mp hv).2

/-- **Every canonically reachable store is already in canonical selector
shape.**  The two selectors are the identities on stores built by
`insertReplacing` and `insertUpdateCanonical`. -/
theorem reachableCanonicalStore_shape {verify : SigVerifier}
    {cs : CanonicalStore} (h : ReachableCanonicalStore verify cs) :
    CanonicalStoreShape cs.gossip := by
  induction h with
  | empty _ => exact ⟨rfl, rfl⟩
  | step h ih =>
      rename_i cs' m'
      cases m' with
      | channelAnnouncement a =>
          by_cases hg : a.signaturesValid verify ∧ a.node1 ≠ a.node2 ∧
              cs'.gossip.CompatibleWithStore a ∧
              UpdatesAuthorizedBy cs'.gossip a
          · rw [applyGossipCanonicalStore_announcement_of_admitted verify cs' a hg]
            refine ⟨?_, ?_⟩
            · simpa using selectAnnouncements_insertReplacing_of_shape ih a
            · simpa using ih.2
          · rw [applyGossipCanonicalStore_announcement_of_rejected verify cs' a hg]
            exact ih
      | channelUpdate u =>
          by_cases hg : u.signatureValid verify ∧
              cs'.gossip.updateKeyAnnouncedDirectional u ∧
              UpdateSupersedes u cs'.gossip.updates
          · rw [applyGossipCanonicalStore_update_of_admitted verify cs' u hg]
            refine ⟨?_, ?_⟩
            · simpa using ih.1
            · simpa using selectUpdates_insertUpdateCanonical_of_shape ih u
          · rw [applyGossipCanonicalStore_update_of_rejected verify cs' u hg]
            exact ih
      | nodeAnnouncement n =>
          by_cases hg : n.signatureValid verify
          · rw [applyGossipCanonicalStore_node_of_valid verify cs' n hg]
            simpa [CanonicalStoreShape] using ih
          · rw [applyGossipCanonicalStore_node_of_invalid verify cs' n hg]
            exact ih

/-! ## 5. The refinement square -/

/-- Inserting a fresh announcement is raw cons. -/
theorem insertReplacing_eq_cons_of_fresh {a : ChannelAnnellation}
    {l : List ChannelAnnellation}
    (h : ∀ b ∈ l, b.shortChannelId ≠ a.shortChannelId) :
    insertReplacing a l = a :: l := by
  unfold insertReplacing
  rw [List.filter_eq_self.mpr]
  intro b hb
  exact decide_eq_true (h b hb)

/-- Inserting a fresh directional slot is raw cons. -/
theorem insertUpdateCanonical_eq_cons_of_fresh {u : ChannelUpdate}
    {l : List ChannelUpdate}
    (h : ∀ v ∈ l,
      ¬ (v.shortChannelId = u.shortChannelId ∧ v.direction = u.direction)) :
    insertUpdateCanonical u l = u :: l := by
  unfold insertUpdateCanonical
  rw [List.filter_eq_self.mpr]
  intro v hv
  exact decide_eq_true (h v hv)

/-- **The sharp refinement theorem.**  On a store already in canonical selector
shape, if the canonical admission gates hold and the raw global clock admits the
update, then observing the raw step through the canonical selector is exactly
the canonical store step.

The three hypotheses are not removable:

* without `CanonicalStoreShape`, the selector would have to normalise records
  the raw step just appended;
* without the gates, the canonical step is a no-op while the raw step mutates
  the store;
* without `RawClockAdmits`, the raw update step is a no-op while the canonical
  per-slot gate can still admit the update. -/
theorem canonicalStoreView_applyGossip_eq_canonicalStore
    (verify : SigVerifier) (cs : CanonicalStore) (m : GossipMessage)
    (hshape : CanonicalStoreShape cs.gossip)
    (hgate : CanonicalMessageAdmitted verify cs m)
    (hclock : RawClockAdmits cs.gossip m) :
    canonicalStoreView (applyGossip cs.gossip m) =
      (applyGossipCanonicalStore verify cs m).gossip := by
  cases m with
  | channelAnnouncement a =>
      rw [applyGossipCanonicalStore_announcement_of_admitted verify cs a hgate]
      simp [canonicalStoreView, applyGossip, selectAnnouncements_cons,
        hshape.1, hshape.2]
  | channelUpdate u =>
      have hclock' : cs.gossip.latestUpdateTimestamp < u.timestamp := hclock
      rw [applyGossipCanonicalStore_update_of_admitted verify cs u hgate]
      simp [canonicalStoreView, applyGossip, GossipState.applyUpdate,
        hshape.1, hshape.2, selectUpdates_cons, hclock']
  | nodeAnnouncement n =>
      rw [applyGossipCanonicalStore_node_of_valid verify cs n hgate]
      simp [canonicalStoreView, applyGossip, hshape.1, hshape.2]

/-- **Literal agreement on the common domain.**  If the incoming channel or
directional slot is fresh, raw `applyGossip` and the canonical store step have
the same gossip store.  This is the strongest form in which the raw transition
is a refinement of the canonical one; freshness is exactly what raw append
semantics adds to replacement semantics. -/
theorem applyGossip_eq_canonicalStore_of_fresh
    (verify : SigVerifier) (cs : CanonicalStore) (m : GossipMessage)
    (hgate : CanonicalMessageAdmitted verify cs m)
    (hclock : RawClockAdmits cs.gossip m)
    (hfresh : FreshMessage cs.gossip m) :
    applyGossip cs.gossip m = (applyGossipCanonicalStore verify cs m).gossip := by
  cases m with
  | channelAnnouncement a =>
      rw [applyGossipCanonicalStore_announcement_of_admitted verify cs a hgate]
      simp [applyGossip, insertReplacing_eq_cons_of_fresh hfresh]
  | channelUpdate u =>
      have hclock' : cs.gossip.latestUpdateTimestamp < u.timestamp := hclock
      rw [applyGossipCanonicalStore_update_of_admitted verify cs u hgate]
      simp [applyGossip, GossipState.applyUpdate, hclock',
        insertUpdateCanonical_eq_cons_of_fresh hfresh]
  | nodeAnnouncement n =>
      rw [applyGossipCanonicalStore_node_of_valid verify cs n hgate]
      rfl

/-- The canonical store step preserves canonical selector shape. -/
theorem canonicalStoreShape_applyGossipCanonicalStore
    (verify : SigVerifier) (cs : CanonicalStore) (m : GossipMessage)
    (hshape : CanonicalStoreShape cs.gossip)
    (hgate : CanonicalMessageAdmitted verify cs m) :
    CanonicalStoreShape (applyGossipCanonicalStore verify cs m).gossip := by
  cases m with
  | channelAnnouncement a =>
      rw [applyGossipCanonicalStore_announcement_of_admitted verify cs a hgate]
      refine ⟨?_, ?_⟩
      · simpa using selectAnnouncements_insertReplacing_of_shape hshape a
      · simpa using hshape.2
  | channelUpdate u =>
      rw [applyGossipCanonicalStore_update_of_admitted verify cs u hgate]
      refine ⟨?_, ?_⟩
      · simpa using hshape.1
      · simpa using selectUpdates_insertUpdateCanonical_of_shape hshape u
  | nodeAnnouncement n =>
      rw [applyGossipCanonicalStore_node_of_valid verify cs n hgate]
      simpa [CanonicalStoreShape] using hshape

/-- Combining literal agreement with canonical shape: on the common domain the
canonical observation of the raw step is the raw step itself, and it equals the
canonical store step. -/
theorem canonicalStoreView_applyGossip_eq_of_fresh
    (verify : SigVerifier) (cs : CanonicalStore) (m : GossipMessage)
    (hshape : CanonicalStoreShape cs.gossip)
    (hgate : CanonicalMessageAdmitted verify cs m)
    (hclock : RawClockAdmits cs.gossip m)
    (hfresh : FreshMessage cs.gossip m) :
    canonicalStoreView (applyGossip cs.gossip m) =
      (applyGossipCanonicalStore verify cs m).gossip := by
  rw [applyGossip_eq_canonicalStore_of_fresh verify cs m hgate hclock hfresh]
  exact (canonicalStoreView_eq_self_iff _).mpr
    (canonicalStoreShape_applyGossipCanonicalStore verify cs m hshape hgate)

/-! ## 6. Boundary: the raw clock is strictly stronger -/

private def acceptAll : SigVerifier := fun _ _ _ => true

/-- Byte length 1. -/
private def kA : PubKey := ⟨ByteArray.mk #[1]⟩

/-- Byte length 0. -/
private def kB : PubKey := ⟨ByteArray.empty⟩

/-- Byte length 2. -/
private def kC : PubKey := ⟨ByteArray.mk #[1, 2]⟩

private def nA : NodeId := ⟨0⟩

private def nB : NodeId := ⟨1⟩

private def nC : NodeId := ⟨2⟩

private def nD : NodeId := ⟨3⟩

private def sc1 : ShortChannelId := ⟨1, 2, 3⟩

private def sc2 : ShortChannelId := ⟨4, 5, 6⟩

private def emptySig : GossipSignature := ⟨ByteArray.empty⟩

private def mkAnn (scid : ShortChannelId) (u v : NodeId) (ka kb : PubKey)
    (cap : Nat) : ChannelAnnellation :=
  { shortChannelId := scid
    node1 := u
    node2 := v
    nodeKey1 := ka
    nodeKey2 := kb
    bitcoinKey1 := ka
    bitcoinKey2 := kb
    capacitySat := cap
    digest := ByteArray.empty
    nodeSignature1 := emptySig
    nodeSignature2 := emptySig
    bitcoinSignature1 := emptySig
    bitcoinSignature2 := emptySig }

private def mkUpd (scid : ShortChannelId) (ts : Nat) (k : PubKey) :
    ChannelUpdate :=
  { shortChannelId := scid
    timestamp := ts
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

/-- Channel `sc1`, direction 0 key `kA`. -/
private def ann1 : ChannelAnnellation := mkAnn sc1 nA nB kA kB 1000

/-- Channel `sc2`, direction 0 key `kC`. -/
private def ann2 : ChannelAnnellation := mkAnn sc2 nC nD kC kB 2000

/-- A conflicting re-announcement of `sc1` that rebinds `nA` from `kA` to `kC`. -/
private def annConflict : ChannelAnnellation := mkAnn sc1 nA nB kC kB 1000

/-- Stored update on `sc2`, timestamp 10, signed by `kC`. -/
private def uHi : ChannelUpdate := mkUpd sc2 10 kC

/-- Incoming update on `sc1`, timestamp 5, signed by `kA`. -/
private def uLo : ChannelUpdate := mkUpd sc1 5 kA

private theorem ann1_valid : ann1.signaturesValid acceptAll := by
  simp [ChannelAnnellation.signaturesValid, signatureValid, acceptAll]

private theorem ann2_valid : ann2.signaturesValid acceptAll := by
  simp [ChannelAnnellation.signaturesValid, signatureValid, acceptAll]

private theorem uHi_valid : uHi.signatureValid acceptAll := by
  simp [ChannelUpdate.signatureValid, signatureValid, acceptAll]

private theorem uLo_valid : uLo.signatureValid acceptAll := by
  simp [ChannelUpdate.signatureValid, signatureValid, acceptAll]

private theorem nA_ne_nB : nA ≠ nB := by decide

private theorem nC_ne_nD : nC ≠ nD := by decide

private theorem sc1_ne_sc2 : sc1 ≠ sc2 := by decide

private def s0 : CanonicalStore :=
  { gossip := ⟨[], [], []⟩, nodeKeyOf := fun _ => kB }

private theorem s0_compat (a : ChannelAnnellation) :
    s0.gossip.CompatibleWithStore a := by
  intro b hb
  simp [s0] at hb

private theorem s0_auth (a : ChannelAnnellation) :
    UpdatesAuthorizedBy s0.gossip a := by
  intro u hu
  simp [s0] at hu

private theorem ann1_gate :
    CanonicalMessageAdmitted acceptAll s0 (.channelAnnouncement ann1) :=
  ⟨ann1_valid, by simpa [ann1, mkAnn] using nA_ne_nB,
    s0_compat ann1, s0_auth ann1⟩

private noncomputable def s1 : CanonicalStore :=
  applyGossipCanonicalStore acceptAll s0 (.channelAnnouncement ann1)

private theorem s1_announcements : s1.gossip.announcements = [ann1] := by
  rw [s1, applyGossipCanonicalStore_announcement_of_admitted acceptAll s0 ann1
    ann1_gate]
  simp [s0, insertReplacing]

private theorem s1_updates : s1.gossip.updates = [] := by
  rw [s1, applyGossipCanonicalStore_announcement_of_admitted acceptAll s0 ann1
    ann1_gate]
  simp [s0]

private theorem s1_compat_ann2 : s1.gossip.CompatibleWithStore ann2 := by
  intro b hb
  rw [s1_announcements] at hb
  simp only [List.mem_singleton] at hb
  subst b
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    intro h <;>
    simp [ann1, ann2, mkAnn, nA, nB, nC, nD] at h

private theorem s1_auth (a : ChannelAnnellation) :
    UpdatesAuthorizedBy s1.gossip a := by
  intro u hu
  rw [s1_updates] at hu
  simp at hu

private theorem ann2_gate :
    CanonicalMessageAdmitted acceptAll s1 (.channelAnnouncement ann2) :=
  ⟨ann2_valid, by simpa [ann2, mkAnn] using nC_ne_nD,
    s1_compat_ann2, s1_auth ann2⟩

private noncomputable def s2 : CanonicalStore :=
  applyGossipCanonicalStore acceptAll s1 (.channelAnnouncement ann2)

private theorem s2_announcements : s2.gossip.announcements = [ann2, ann1] := by
  rw [s2, applyGossipCanonicalStore_announcement_of_admitted acceptAll s1 ann2
    ann2_gate]
  rw [s1_announcements]
  simp [insertReplacing, ann1, ann2, mkAnn, sc1_ne_sc2]

private theorem s2_updates : s2.gossip.updates = [] := by
  rw [s2, applyGossipCanonicalStore_announcement_of_admitted acceptAll s1 ann2
    ann2_gate]
  simp [s1_updates]

private theorem s2_attributed_uHi :
    s2.gossip.updateKeyAnnouncedDirectional uHi := by
  refine GossipState.updateKeyAnnouncedDirectional_of_mem (a := ann2) ?_ rfl ?_
  · rw [s2_announcements]
    simp
  · rw [ChannelUpdate.direction_of_channelFlags_zero
      (by rfl : uHi.channelFlags = 0)]
    simpa [ann2, mkAnn, uHi, mkUpd] using
      (ChannelAnnellation.attributesKeyForDirection_node1 ann2)

private theorem s2_supersedes_uHi :
    UpdateSupersedes uHi s2.gossip.updates := by
  intro v hv
  rw [s2_updates] at hv
  simp at hv

private theorem uHi_gate :
    CanonicalMessageAdmitted acceptAll s2 (.channelUpdate uHi) :=
  ⟨uHi_valid, s2_attributed_uHi, s2_supersedes_uHi⟩

private noncomputable def s3 : CanonicalStore :=
  applyGossipCanonicalStore acceptAll s2 (.channelUpdate uHi)

private theorem s3_announcements : s3.gossip.announcements = [ann2, ann1] := by
  rw [s3, applyGossipCanonicalStore_update_of_admitted acceptAll s2 uHi uHi_gate]
  simp [s2_announcements]

private theorem s3_updates : s3.gossip.updates = [uHi] := by
  rw [s3, applyGossipCanonicalStore_update_of_admitted acceptAll s2 uHi uHi_gate]
  simp [s2_updates, insertUpdateCanonical]

private theorem s3_reachable : ReachableCanonicalStore acceptAll s3 := by
  unfold s3 s2 s1 s0
  exact ReachableCanonicalStore.step
    (ReachableCanonicalStore.step
      (ReachableCanonicalStore.step
        (ReachableCanonicalStore.empty (fun _ => kB))))

private theorem s3_attributed_uLo :
    s3.gossip.updateKeyAnnouncedDirectional uLo := by
  refine GossipState.updateKeyAnnouncedDirectional_of_mem (a := ann1) ?_ rfl ?_
  · rw [s3_announcements]
    simp
  · rw [ChannelUpdate.direction_of_channelFlags_zero
      (by rfl : uLo.channelFlags = 0)]
    simpa [ann1, mkAnn, uLo, mkUpd] using
      (ChannelAnnellation.attributesKeyForDirection_node1 ann1)

private theorem s3_supersedes_uLo :
    UpdateSupersedes uLo s3.gossip.updates := by
  intro v hv hscid _hdir
  rw [s3_updates] at hv
  simp only [List.mem_singleton] at hv
  subst v
  exact absurd hscid (by decide)

private theorem uLo_gate :
    CanonicalMessageAdmitted acceptAll s3 (.channelUpdate uLo) :=
  ⟨uLo_valid, s3_attributed_uLo, s3_supersedes_uLo⟩

private theorem s3_latest : s3.gossip.latestUpdateTimestamp = 10 := by
  rw [GossipState.latestUpdateTimestamp, s3_updates]
  simp [latestTimestamp, uHi, mkUpd]

private theorem uLo_not_raw_clock :
    ¬ RawClockAdmits s3.gossip (.channelUpdate uLo) := by
  simp [RawClockAdmits, s3_latest, uLo, mkUpd]

private theorem uLo_not_mem_s3 : uLo ∉ s3.gossip.updates := by
  rw [s3_updates]
  simp [uLo, uHi, mkUpd, sc1_ne_sc2]

private theorem uLo_ne_uHi : uLo ≠ uHi := by
  intro h
  have hscid := congrArg ChannelUpdate.shortChannelId h
  exact sc1_ne_sc2 (by simpa [uLo, uHi, mkUpd] using hscid)

/-- **Boundary: canonical per-slot admission is strictly weaker than the raw
global clock.**  In a canonically reachable store with announcements for two
channels and a stored update on the second, an update on the first channel with
a lower timestamp than the global clock is admitted by the canonical per-slot
gate (`UpdateSupersedes` is vacuous for the untouched slot) but ignored by raw
`GossipState.applyUpdate`.  Hence no theorem can identify the two transitions
without an extra hypothesis such as `RawClockAdmits` or freshness. -/
theorem canonical_admission_strictly_weaker_than_raw_clock :
    ∃ (verify : SigVerifier) (cs : CanonicalStore) (u : ChannelUpdate),
      ReachableCanonicalStore verify cs ∧
        CanonicalMessageAdmitted verify cs (.channelUpdate u) ∧
          ¬ RawClockAdmits cs.gossip (.channelUpdate u) ∧
            (applyGossipCanonicalStore verify cs (.channelUpdate u)).gossip.updates =
              u :: cs.gossip.updates ∧
              applyGossip cs.gossip (.channelUpdate u) = cs.gossip ∧
                u ∉ cs.gossip.updates := by
  refine ⟨acceptAll, s3, uLo, s3_reachable, uLo_gate, uLo_not_raw_clock, ?_, ?_,
    uLo_not_mem_s3⟩
  · rw [applyGossipCanonicalStore_update_of_admitted acceptAll s3 uLo uLo_gate]
    rw [insertUpdateCanonical_eq_cons_of_fresh]
    intro v hv
    rw [s3_updates] at hv
    simp only [List.mem_singleton] at hv
    subst v
    intro h
    exact sc1_ne_sc2 (by simpa [uLo, uHi, mkUpd] using h.1.symm)
  · rw [applyGossip]
    refine GossipState.applyUpdate_stale s3.gossip uLo ?_
    rw [s3_latest]
    simp [uLo, mkUpd]

private theorem kC_ne_kA : kC ≠ kA := by
  intro h
  have hs := congrArg (fun k => k.bytes.size) h
  have h1 : kC.bytes.size = 2 := by decide
  have h2 : kA.bytes.size = 1 := by decide
  rw [h1, h2] at hs
  omega

private theorem annConflict_ne_ann1 : annConflict ≠ ann1 := by
  intro h
  have hk := congrArg ChannelAnnellation.nodeKey1 h
  exact kC_ne_kA (by simpa [ann1, annConflict, mkAnn] using hk)

/-- **Impossibility of a canonical-preserving raw announcement extension.**  Any
transition that keeps raw append semantics for `channel_announcement` cannot
preserve `CanonicalAnnouncements` from the empty store: two conflicting
announcements for the same `short_channel_id` are both appended, while
canonicality demands a replacement step that raw append does not have. -/
theorem no_canonical_preserving_raw_announcement_extension :
    ¬ ∃ F : GossipState → GossipMessage → GossipState,
      (∀ (s : GossipState) (a : ChannelAnnellation),
        F s (.channelAnnouncement a) = applyGossip s (.channelAnnouncement a)) ∧
      (∀ s : GossipState, CanonicalAnnouncements s.announcements →
        ∀ m : GossipMessage,
          CanonicalAnnouncements (F s m).announcements) := by
  rintro ⟨F, hraw, hpres⟩
  have hempty : CanonicalAnnouncements ([] : List ChannelAnnellation) := by
    intro a ha
    simp at ha
  have h1 : CanonicalAnnouncements
      (F ⟨[], [], []⟩ (.channelAnnouncement ann1)).announcements :=
    hpres ⟨[], [], []⟩ hempty _
  have hstep1 : F ⟨[], [], []⟩ (.channelAnnouncement ann1) =
      (⟨[ann1], [], []⟩ : GossipState) := by
    rw [hraw]
    rfl
  have h2 : CanonicalAnnouncements
      (F (F ⟨[], [], []⟩ (.channelAnnouncement ann1))
        (.channelAnnouncement annConflict)).announcements :=
    hpres _ h1 _
  rw [hstep1, hraw] at h2
  simp [applyGossip] at h2
  have hsame : annConflict = ann1 :=
    h2 annConflict (by simp) ann1 (by simp) rfl
  exact annConflict_ne_ann1 hsame

/-- **The canonical selector resolves the conflict without changing raw
`applyGossip`.**  The conflicting raw store is not canonical, while its
canonical observation keeps exactly one record. -/
theorem canonicalStoreView_resolves_conflict :
    let s : GossipState := ⟨[annConflict, ann1], [], []⟩
    ¬ CanonicalAnnouncements s.announcements ∧
      CanonicalAnnouncements (canonicalStoreView s).announcements ∧
        (canonicalStoreView s).announcements = [annConflict] := by
  dsimp only
  have hnot : ¬ CanonicalAnnouncements
      ([annConflict, ann1] : List ChannelAnnellation) := by
    intro hc
    exact annConflict_ne_ann1 (hc annConflict (by simp) ann1 (by simp) rfl)
  refine ⟨hnot, canonical_selectAnnouncements _, ?_⟩
  simp [canonicalStoreView, selectAnnouncements, insertReplacing, ann1,
    annConflict, mkAnn]

/-! ## 7. Preserved counterexamples -/

/-- Raw `applyGossip` still accepts a conflicting announcement; the canonical
store wrapper does not change the raw transition. -/
theorem raw_conflicting_announcement_counterexample_preserved :
    ∃ (s : GossipState) (a : ChannelAnnellation),
      ¬ CanonicalAnnouncements
        (applyGossip s (.channelAnnouncement a)).announcements :=
  raw_applyGossip_accepts_conflicting_announcement

/-- Without a canonical selector, conflicting announcements remain ambiguous.
This is the wave-5 counterexample, unchanged. -/
theorem ambiguous_without_canonical_preserved :
    ∃ (s : GossipState) (u v : ChannelUpdate),
      ¬ CanonicalAnnouncements s.announcements ∧
        u.shortChannelId = v.shortChannelId ∧ u.direction = v.direction ∧
          s.updateKeyAnnouncedDirectional u ∧
            s.updateKeyAnnouncedDirectional v ∧ u.signingKey ≠ v.signingKey :=
  conflicting_announcements_ambiguous_without_canonical

/-- The wave-6 canonical transition still rejects the conflicting
re-announcement, proving that the counterexample is on the raw path only. -/
theorem canonical_conflicting_announcement_rejection_preserved :
    ∃ (verify : SigVerifier) (cs : CanonicalNetwork)
      (a : ChannelAnnellation),
      ReachableCanonical verify cs ∧
        ¬ cs.gossip.CompatibleWithStore a ∧
          admitGossipCanonical verify cs (.channelAnnouncement a) = cs :=
  canonical_admission_rejects_conflicting_announcement

end LnLean.Proofs.Routing.GossipRawRefinementTargets
