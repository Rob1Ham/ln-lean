import LnLean.Proofs.Routing.GossipStoreEpochTargets

/-!
# LnLean.Proofs.Routing.NodeCanonicalTargets

Wave-9 lane `S9-RT-NODE-CANON`, open issue `RT-02`.

Waves 6--8 canonicalised `channel_announcement` (replace by
`short_channel_id`) and `channel_update` (replace by
`(short_channel_id, direction)` slot), and wave 8 added a typed replacement
history and an epoch-indexed store.  Node announcements were deliberately left
out: both raw `applyGossip` and the canonical `applyGossipCanonicalStore`
**append** them, and `canonicalStoreView` does not select them
(`canonicalStoreView_nodeAnnouncements`).  This module closes that design gap
with an additive node-announcement canonicalisation layer; it does not edit the
core transition or the epoch module.

## Model

* `insertNodeCanonical n l` replaces every stored record with the incoming
  record's `nodeId`, then prepends the incoming record.
* `NodeSupersedes n l` is the BOLT 7 replacement gate for one node slot: every
  stored record with the same `nodeId` has a strictly smaller `timestamp`.
  Equal timestamps do not replace, matching BOLT 7's avoidance of a
  content/signature tie-breaker.
* `CanonicalNodeAnnouncements l` says at most one stored record per `nodeId`.
* `selectNodeAnnouncements` is the head-most (newest-arrival) selector; it is
  the node analogue of `selectAnnouncements` / `selectUpdates`.
* `canonicalNodeStoreView s` is `canonicalStoreView s` with the node list
  selected.  It always has canonical node records.
* `applyGossipNodeCanonical verify cs m` is the canonical store transition with
  the node branch replaced by signature-plus-timestamp-gated replacement.  The
  announcement and update branches are *definitionally* the wave-7 canonical
  store transition.
* `ReachableNodeCanonical` closes that transition; `NodeCanonicalAdmitted` is
  its invariant.

## Results

* `reachableNodeCanonical_invariant` derives, on every reachable state:
  canonical channel announcements, per-slot update uniqueness, directional
  update attribution, node-key consistency, valid node signatures, and
  `CanonicalNodeAnnouncements`.
* `reachableNodeCanonical_node_replacement` exhibits an actual reachable
  replacement: a strictly newer record removes the older record in the same
  node slot.
* `reachableNodeCanonical_rotation_keeps_both` exhibits the rotation boundary:
  two records for the same physical node but different `nodeId` keys are
  distinct canonical slots, so canonicalisation keeps both.  Rekeying the
  `NodeId → PubKey` registration map or the channel-announcement key fields
  (`rekeyStore`) does not touch the node layer
  (`applyGossipNodeCanonical_gossip_nodeKeyOf_irrel`,
  `canonicalNodeAnnouncements_rekeyStore`).
* `reachableNodeCanonical_equal_timestamp_tie_boundary` and
  `no_canonical_node_preserving_raw_node_extension` are the unrecoverable
  boundary: raw append plus any order-only selector cannot recover the BOLT 7
  timestamp winner when the winner is not the head record, and no transition
  that keeps raw append semantics for `node_announcement` can preserve
  canonicality from the empty store.
* `reachableNodeCanonical_node_slot_ignores_global_clock` is the per-slot /
  global-clock boundary: the node gate is per `nodeId` and ignores
  `latestUpdateTimestamp`, unlike the raw channel-update clock.
* The wave-7/8 raw non-refinement, per-slot/global-clock separation, and epoch
  squares are re-exported unchanged and are not weakened:
  `raw_nonrefinement_preserved`, `per_slot_global_clock_boundary_preserved`,
  `epoch_square_preserved`, `epoch_fold_store_square_preserved`.
  `epoch_square_lifts_to_node_canonical_view` shows the epoch square still
  holds with the node-canonical view on node-canonical raw folds.

What is **not** claimed:

* `NodeAnnouncement.nodeId` is treated as the BOLT 7 node key (a `PubKey` in this
  model); graph `NodeId` registration is a separate map.  Identity proofs that
  a rotated key belongs to the same physical node are out of scope.
* Chain-hash filtering, UTXO/channel-existence checks for node announcements,
  address parsing, and rate limits are not modelled.
* `SigVerifier` remains abstract; unforgeability remains assumptions C3/C4/C8.
* No network, liveness, or wire-version claim is made.

No `sorry`, no `axiom`, no `admit`, no `native_decide`, no `unsafe`, no
`@[implemented_by]`.
-/

namespace LnLean.Proofs.Routing.NodeCanonicalTargets

open LnLean.Routing
open LnLean.Routing.GossipProps
open LnLean.Proofs.Routing.GossipTargets
open LnLean.Proofs.Routing.GossipKeyConsistencyTargets
open LnLean.Proofs.Routing.GossipCanonicalTargets
open LnLean.Proofs.Routing.GossipRawRefinementTargets
open LnLean.Proofs.Routing.GossipStoreEpochTargets
open Classical

set_option autoImplicit false

/-! ## 1. Node-announcement replacement primitives -/

/-- **Replace-by-node insertion.**  Drop every stored node announcement with the
incoming record's `nodeId`, then prepend the incoming record.  This is the node
analogue of `insertReplacing` (channel id) and `insertUpdateCanonical`
(directional slot). -/
noncomputable def insertNodeCanonical (n : NodeAnnouncement)
    (l : List NodeAnnouncement) : List NodeAnnouncement :=
  n :: l.filter (fun m => decide (m.nodeId ≠ n.nodeId))

/-- **Exact membership after node replacement.**  A record is stored iff it is
the incoming record, or it was stored before for a different `nodeId`. -/
theorem mem_insertNodeCanonical_iff {n m : NodeAnnouncement}
    {l : List NodeAnnouncement} :
    m ∈ insertNodeCanonical n l ↔
      m = n ∨ (m ∈ l ∧ m.nodeId ≠ n.nodeId) := by
  simp [insertNodeCanonical, List.mem_filter]

/-- A stored record for a different node survives replacement. -/
theorem mem_insertNodeCanonical_of_mem_of_ne {n m : NodeAnnouncement}
    {l : List NodeAnnouncement} (hm : m ∈ l) (hne : m.nodeId ≠ n.nodeId) :
    m ∈ insertNodeCanonical n l :=
  List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hm, decide_eq_true hne⟩)

/-- Every non-incoming member after node replacement was stored before. -/
theorem mem_of_mem_insertNodeCanonical_of_ne {n m : NodeAnnouncement}
    {l : List NodeAnnouncement} (h : m ∈ insertNodeCanonical n l)
    (hne : m ≠ n) : m ∈ l := by
  rcases mem_insertNodeCanonical_iff.mp h with rfl | ⟨hm, _⟩
  · exact absurd rfl hne
  · exact hm

/-- **Canonical node announcements.**  No two stored records with the same
`nodeId` are distinct. -/
def CanonicalNodeAnnouncements (l : List NodeAnnouncement) : Prop :=
  ∀ a ∈ l, ∀ b ∈ l, a.nodeId = b.nodeId → a = b

/-- **BOLT 7 node-announcement replacement gate.**  Every stored record for the
incoming `nodeId` is strictly older.  A fresh `nodeId` satisfies this
vacuously; an equal timestamp does not replace. -/
def NodeSupersedes (n : NodeAnnouncement) (l : List NodeAnnouncement) : Prop :=
  ∀ m ∈ l, m.nodeId = n.nodeId → m.timestamp < n.timestamp

/-- **Node replacement preserves canonicality.**  The old record for the same
`nodeId` is removed, so exactly one record remains per node key. -/
theorem canonicalNodeAnnouncements_insertNodeCanonical
    {l : List NodeAnnouncement} (hc : CanonicalNodeAnnouncements l)
    (n : NodeAnnouncement) :
    CanonicalNodeAnnouncements (insertNodeCanonical n l) := by
  intro x hx y hy hkey
  rcases mem_insertNodeCanonical_iff.mp hx with rfl | ⟨hxl, hxn⟩
  · rcases mem_insertNodeCanonical_iff.mp hy with rfl | ⟨hyl, hyn⟩
    · rfl
    · exact absurd hkey.symm hyn
  · rcases mem_insertNodeCanonical_iff.mp hy with rfl | ⟨hyl, hyn⟩
    · exact absurd hkey hxn
    · exact hc x hxl y hyl hkey

/-- Inserting a fresh node id is raw cons. -/
theorem insertNodeCanonical_eq_cons_of_fresh {n : NodeAnnouncement}
    {l : List NodeAnnouncement}
    (h : ∀ m ∈ l, m.nodeId ≠ n.nodeId) :
    insertNodeCanonical n l = n :: l := by
  unfold insertNodeCanonical
  rw [List.filter_eq_self.mpr]
  intro m hm
  exact decide_eq_true (h m hm)

/-- **Head-most node selection.**  Keep the first (newest-arriving) record for
each `nodeId`.  This is the node analogue of `selectAnnouncements`. -/
noncomputable def selectNodeAnnouncements :
    List NodeAnnouncement → List NodeAnnouncement
  | [] => []
  | n :: l => insertNodeCanonical n (selectNodeAnnouncements l)

@[simp] theorem selectNodeAnnouncements_nil :
    selectNodeAnnouncements [] = [] := rfl

/-- Unfolding of the node selector at a cons. -/
theorem selectNodeAnnouncements_cons (n : NodeAnnouncement)
    (l : List NodeAnnouncement) :
    selectNodeAnnouncements (n :: l) =
      insertNodeCanonical n (selectNodeAnnouncements l) := rfl

/-- The selected node list has one record per `nodeId`. -/
theorem canonicalNodeAnnouncements_selectNodeAnnouncements
    (l : List NodeAnnouncement) :
    CanonicalNodeAnnouncements (selectNodeAnnouncements l) := by
  induction l with
  | nil =>
      intro a ha
      simp [selectNodeAnnouncements] at ha
  | cons n l ih =>
      rw [selectNodeAnnouncements_cons]
      exact canonicalNodeAnnouncements_insertNodeCanonical ih n

/-- Selection removes node records; it never invents one. -/
theorem mem_selectNodeAnnouncements {n : NodeAnnouncement}
    {l : List NodeAnnouncement} (h : n ∈ selectNodeAnnouncements l) :
    n ∈ l := by
  induction l with
  | nil => simp [selectNodeAnnouncements] at h
  | cons m l ih =>
      rw [selectNodeAnnouncements_cons] at h
      rcases mem_insertNodeCanonical_iff.mp h with hnm | ⟨hl, _⟩
      · rw [hnm]
        exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih hl)

/-- The selected node list has no duplicate records. -/
theorem selectNodeAnnouncements_nodup (l : List NodeAnnouncement) :
    (selectNodeAnnouncements l).Nodup := by
  induction l with
  | nil => simp [selectNodeAnnouncements]
  | cons n l ih =>
      rw [selectNodeAnnouncements_cons]
      unfold insertNodeCanonical
      rw [List.nodup_cons]
      refine ⟨?_, List.Pairwise.filter _ ih⟩
      intro hmem
      rcases List.mem_filter.mp hmem with ⟨_, hdec⟩
      exact (of_decide_eq_true hdec) rfl

/-- **Selection is the identity on a duplicate-free canonical node list.** -/
theorem selectNodeAnnouncements_of_nodup_canonical
    {l : List NodeAnnouncement} (hnd : l.Nodup)
    (hc : CanonicalNodeAnnouncements l) :
    selectNodeAnnouncements l = l := by
  induction l with
  | nil => rfl
  | cons n l ih =>
      have hndl : l.Nodup := (List.nodup_cons.mp hnd).2
      have hnotmem : n ∉ l := (List.nodup_cons.mp hnd).1
      have hcl : CanonicalNodeAnnouncements l := by
        intro x hx y hy hkey
        exact hc x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy) hkey
      rw [selectNodeAnnouncements_cons, ih hndl hcl]
      unfold insertNodeCanonical
      rw [List.filter_eq_self.mpr]
      intro m hm
      apply decide_eq_true
      intro hsame
      have hnm : n = m :=
        hc n (List.mem_cons_self ..) m (List.mem_cons_of_mem _ hm) hsame.symm
      exact hnotmem (hnm ▸ hm)

/-- **Node selection is idempotent.** -/
theorem selectNodeAnnouncements_idempotent (l : List NodeAnnouncement) :
    selectNodeAnnouncements (selectNodeAnnouncements l) =
      selectNodeAnnouncements l :=
  selectNodeAnnouncements_of_nodup_canonical
    (selectNodeAnnouncements_nodup l)
    (canonicalNodeAnnouncements_selectNodeAnnouncements l)

/-! ## 2. The node-canonical store view -/

/-- **Canonical node-announcement view of a raw store.**  Apply both existing
selectors and additionally keep one node record per `nodeId`.  This is the
node-announcement completion of `canonicalStoreView` for `RT-02`. -/
noncomputable def canonicalNodeStoreView (s : GossipState) : GossipState :=
  { canonicalStoreView s with
    nodeAnnouncements := selectNodeAnnouncements s.nodeAnnouncements }

@[simp] theorem canonicalNodeStoreView_announcements (s : GossipState) :
    (canonicalNodeStoreView s).announcements =
      selectAnnouncements s.announcements := rfl

@[simp] theorem canonicalNodeStoreView_updates (s : GossipState) :
    (canonicalNodeStoreView s).updates = selectUpdates s.updates := rfl

@[simp] theorem canonicalNodeStoreView_nodeAnnouncements (s : GossipState) :
    (canonicalNodeStoreView s).nodeAnnouncements =
      selectNodeAnnouncements s.nodeAnnouncements := rfl

/-- The node-canonical view always has one node record per key. -/
theorem canonicalNodeStoreView_nodeCanonical (s : GossipState) :
    CanonicalNodeAnnouncements (canonicalNodeStoreView s).nodeAnnouncements :=
  canonicalNodeAnnouncements_selectNodeAnnouncements s.nodeAnnouncements

/-- The node-canonical view still has one channel announcement per
`short_channel_id`. -/
theorem canonicalNodeStoreView_canonical (s : GossipState) :
    CanonicalAnnouncements (canonicalNodeStoreView s).announcements :=
  canonical_selectAnnouncements s.announcements

/-- The node-canonical view still has one update per directional slot. -/
theorem canonicalNodeStoreView_updates_slotUnique (s : GossipState) :
    UpdatesSlotUnique (canonicalNodeStoreView s).updates :=
  updatesSlotUnique_selectUpdates s.updates

/-- Selecting node records does not disturb node-key consistency: it only
removes channel announcements, and consistency is inherited by a sublist. -/
theorem nodeKeyConsistent_canonicalNodeStoreView {nodeKeyOf : NodeId → PubKey}
    {s : GossipState} (h : GossipState.NodeKeyConsistent nodeKeyOf s) :
    GossipState.NodeKeyConsistent nodeKeyOf (canonicalNodeStoreView s) := by
  refine GossipState.nodeKeyConsistent_mono ?_ h
  intro a ha
  exact mem_selectAnnouncements (by simpa [canonicalNodeStoreView] using ha)

/-- The node-canonical view is idempotent. -/
theorem canonicalNodeStoreView_idempotent (s : GossipState) :
    canonicalNodeStoreView (canonicalNodeStoreView s) =
      canonicalNodeStoreView s := by
  cases s with
  | mk ann upd node =>
      simp [canonicalNodeStoreView, canonicalStoreView,
        selectAnnouncements_idempotent, selectUpdates_idempotent,
        selectNodeAnnouncements_idempotent]

/-- On a store whose node list is already selector-fixed, the node-canonical
view is exactly the wave-7 canonical view. -/
theorem canonicalNodeStoreView_eq_canonicalStoreView_of_select_eq_self
    (s : GossipState)
    (h : selectNodeAnnouncements s.nodeAnnouncements = s.nodeAnnouncements) :
    canonicalNodeStoreView s = canonicalStoreView s := by
  cases s with
  | mk ann upd node =>
      simp [canonicalNodeStoreView, canonicalStoreView, h]

/-- A store's node list is already in node-canonical shape when selection is
the identity. -/
def NodeCanonicalShape (s : GossipState) : Prop :=
  selectNodeAnnouncements s.nodeAnnouncements = s.nodeAnnouncements

/-- `canonicalNodeStoreView` is the identity exactly on node-canonical-shaped
stores (with the existing channel/update selectors also fixed). -/
theorem canonicalNodeStoreView_eq_self_iff (s : GossipState) :
    canonicalNodeStoreView s = s ↔
      CanonicalStoreShape s ∧ NodeCanonicalShape s := by
  cases s with
  | mk ann upd node =>
      constructor
      · intro h
        have hann : selectAnnouncements ann = ann :=
          congrArg GossipState.announcements h
        have hupd : selectUpdates upd = upd :=
          congrArg GossipState.updates h
        have hnode : selectNodeAnnouncements node = node :=
          congrArg GossipState.nodeAnnouncements h
        exact ⟨⟨hann, hupd⟩, hnode⟩
      · rintro ⟨⟨hann, hupd⟩, hnode⟩
        have hnode' : selectNodeAnnouncements node = node := by
          simpa [NodeCanonicalShape] using hnode
        simp [canonicalNodeStoreView, canonicalStoreView, hann, hupd, hnode']

/-! ## 3. The node-canonical store transition -/

/-- **Node-canonical store transition.**  The announcement and update branches
are exactly the wave-7 canonical store transition.  The node branch is
signature-gated and additionally replaces only when the incoming timestamp
beats every stored record for the same `nodeId`. -/
noncomputable def applyGossipNodeCanonical (verify : SigVerifier)
    (cs : CanonicalStore) : GossipMessage → CanonicalStore
  | .channelAnnouncement a =>
      applyGossipCanonicalStore verify cs (.channelAnnouncement a)
  | .channelUpdate u =>
      applyGossipCanonicalStore verify cs (.channelUpdate u)
  | .nodeAnnouncement n =>
      if n.signatureValid verify ∧
          NodeSupersedes n cs.gossip.nodeAnnouncements then
        { gossip := { cs.gossip with
            nodeAnnouncements :=
              insertNodeCanonical n cs.gossip.nodeAnnouncements }
          nodeKeyOf := cs.nodeKeyOf }
      else cs

/-- The announcement branch is definitionally the wave-7 canonical transition. -/
theorem applyGossipNodeCanonical_announcement (verify : SigVerifier)
    (cs : CanonicalStore) (a : ChannelAnnellation) :
    applyGossipNodeCanonical verify cs (.channelAnnouncement a) =
      applyGossipCanonicalStore verify cs (.channelAnnouncement a) := rfl

/-- The update branch is definitionally the wave-7 canonical transition. -/
theorem applyGossipNodeCanonical_update (verify : SigVerifier)
    (cs : CanonicalStore) (u : ChannelUpdate) :
    applyGossipNodeCanonical verify cs (.channelUpdate u) =
      applyGossipCanonicalStore verify cs (.channelUpdate u) := rfl

/-- An admitted node announcement replaces its node slot. -/
theorem applyGossipNodeCanonical_node_of_admitted (verify : SigVerifier)
    (cs : CanonicalStore) (n : NodeAnnouncement)
    (h : n.signatureValid verify ∧
      NodeSupersedes n cs.gossip.nodeAnnouncements) :
    applyGossipNodeCanonical verify cs (.nodeAnnouncement n) =
      { gossip := { cs.gossip with
          nodeAnnouncements :=
            insertNodeCanonical n cs.gossip.nodeAnnouncements }
        nodeKeyOf := cs.nodeKeyOf } := by
  simp [applyGossipNodeCanonical, h]

/-- A rejected node announcement is a complete no-op. -/
theorem applyGossipNodeCanonical_node_of_rejected (verify : SigVerifier)
    (cs : CanonicalStore) (n : NodeAnnouncement)
    (h : ¬ (n.signatureValid verify ∧
      NodeSupersedes n cs.gossip.nodeAnnouncements)) :
    applyGossipNodeCanonical verify cs (.nodeAnnouncement n) = cs := by
  simp [applyGossipNodeCanonical, h]

/-- **Node canonicalisation agrees with the wave-7 transition on a fresh node
slot.**  If the incoming `nodeId` is absent, replacement and append coincide. -/
theorem applyGossipNodeCanonical_node_eq_canonicalStore_of_fresh
    (verify : SigVerifier) (cs : CanonicalStore) (n : NodeAnnouncement)
    (hfresh : ∀ m ∈ cs.gossip.nodeAnnouncements, m.nodeId ≠ n.nodeId)
    (hgate : n.signatureValid verify ∧
      NodeSupersedes n cs.gossip.nodeAnnouncements) :
    applyGossipNodeCanonical verify cs (.nodeAnnouncement n) =
      applyGossipCanonicalStore verify cs (.nodeAnnouncement n) := by
  rw [applyGossipNodeCanonical_node_of_admitted verify cs n hgate,
    applyGossipCanonicalStore_node_of_valid verify cs n hgate.1,
    insertNodeCanonical_eq_cons_of_fresh hfresh]

/-- The canonical announcement branch leaves node announcements unchanged. -/
@[simp] theorem applyGossipCanonicalStore_announcement_nodeAnnouncements
    (verify : SigVerifier) (cs : CanonicalStore) (a : ChannelAnnellation) :
    (applyGossipCanonicalStore verify cs (.channelAnnouncement a)).gossip.nodeAnnouncements =
      cs.gossip.nodeAnnouncements := by
  by_cases h : a.signaturesValid verify ∧ a.node1 ≠ a.node2 ∧
      cs.gossip.CompatibleWithStore a ∧ UpdatesAuthorizedBy cs.gossip a
  · rw [applyGossipCanonicalStore_announcement_of_admitted verify cs a h]
  · rw [applyGossipCanonicalStore_announcement_of_rejected verify cs a h]

/-- The canonical update branch leaves node announcements unchanged. -/
@[simp] theorem applyGossipCanonicalStore_update_nodeAnnouncements
    (verify : SigVerifier) (cs : CanonicalStore) (u : ChannelUpdate) :
    (applyGossipCanonicalStore verify cs (.channelUpdate u)).gossip.nodeAnnouncements =
      cs.gossip.nodeAnnouncements := by
  by_cases h : u.signatureValid verify ∧
      cs.gossip.updateKeyAnnouncedDirectional u ∧
        UpdateSupersedes u cs.gossip.updates
  · rw [applyGossipCanonicalStore_update_of_admitted verify cs u h]
  · rw [applyGossipCanonicalStore_update_of_rejected verify cs u h]

/-- The canonical node branch leaves channel announcements unchanged. -/
@[simp] theorem applyGossipCanonicalStore_node_announcements
    (verify : SigVerifier) (cs : CanonicalStore) (n : NodeAnnouncement) :
    (applyGossipCanonicalStore verify cs (.nodeAnnouncement n)).gossip.announcements =
      cs.gossip.announcements := by
  by_cases h : n.signatureValid verify
  · rw [applyGossipCanonicalStore_node_of_valid verify cs n h]
  · rw [applyGossipCanonicalStore_node_of_invalid verify cs n h]

/-- The canonical node branch leaves channel updates unchanged. -/
@[simp] theorem applyGossipCanonicalStore_node_updates
    (verify : SigVerifier) (cs : CanonicalStore) (n : NodeAnnouncement) :
    (applyGossipCanonicalStore verify cs (.nodeAnnouncement n)).gossip.updates =
      cs.gossip.updates := by
  by_cases h : n.signatureValid verify
  · rw [applyGossipCanonicalStore_node_of_valid verify cs n h]
  · rw [applyGossipCanonicalStore_node_of_invalid verify cs n h]

/-- Changing only the node-announcement list does not change the canonical store
invariant, which is a statement about channel announcements and updates. -/
theorem canonicalStoreAdmitted_nodeAnnouncements_irrel
    (verify : SigVerifier) (cs : CanonicalStore)
    (l : List NodeAnnouncement)
    (h : CanonicalStoreAdmitted verify cs) :
    CanonicalStoreAdmitted verify
      { gossip := { cs.gossip with nodeAnnouncements := l }
        nodeKeyOf := cs.nodeKeyOf } := by
  rcases h with ⟨hstore, hupdates, hnode, hcanon, hslots⟩
  exact ⟨hstore, hupdates, hnode, hcanon, hslots⟩

/-- Node canonicalisation never changes the channel-announcement list. -/
theorem applyGossipNodeCanonical_announcements (verify : SigVerifier)
    (cs : CanonicalStore) (m : GossipMessage) :
    (applyGossipNodeCanonical verify cs m).gossip.announcements =
      (applyGossipCanonicalStore verify cs m).gossip.announcements := by
  cases m with
  | channelAnnouncement a =>
      rw [applyGossipNodeCanonical_announcement]
  | channelUpdate u =>
      rw [applyGossipNodeCanonical_update]
  | nodeAnnouncement n =>
      by_cases h : n.signatureValid verify ∧
          NodeSupersedes n cs.gossip.nodeAnnouncements
      · rw [applyGossipNodeCanonical_node_of_admitted verify cs n h]
        simp [applyGossipCanonicalStore_node_announcements]
      · rw [applyGossipNodeCanonical_node_of_rejected verify cs n h]
        simp [applyGossipCanonicalStore_node_announcements]

/-- Node canonicalisation never changes the channel-update list. -/
theorem applyGossipNodeCanonical_updates (verify : SigVerifier)
    (cs : CanonicalStore) (m : GossipMessage) :
    (applyGossipNodeCanonical verify cs m).gossip.updates =
      (applyGossipCanonicalStore verify cs m).gossip.updates := by
  cases m with
  | channelAnnouncement a =>
      rw [applyGossipNodeCanonical_announcement]
  | channelUpdate u =>
      rw [applyGossipNodeCanonical_update]
  | nodeAnnouncement n =>
      by_cases h : n.signatureValid verify ∧
          NodeSupersedes n cs.gossip.nodeAnnouncements
      · rw [applyGossipNodeCanonical_node_of_admitted verify cs n h]
        simp [applyGossipCanonicalStore_node_updates]
      · rw [applyGossipNodeCanonical_node_of_rejected verify cs n h]
        simp [applyGossipCanonicalStore_node_updates]

/-- **The node-canonical transition ignores the `NodeId → PubKey` registration
map on its gossip component.**  Node replacement is keyed by the wire `nodeId`,
not by the graph registration map. -/
theorem applyGossipNodeCanonical_gossip_nodeKeyOf_irrel
    (verify : SigVerifier) (cs : CanonicalStore) (k : NodeId → PubKey)
    (m : GossipMessage) :
    (applyGossipNodeCanonical verify { cs with nodeKeyOf := k } m).gossip =
      (applyGossipNodeCanonical verify cs m).gossip := by
  cases m with
  | channelAnnouncement a =>
      rw [applyGossipNodeCanonical_announcement,
        applyGossipNodeCanonical_announcement]
      by_cases h : a.signaturesValid verify ∧ a.node1 ≠ a.node2 ∧
          cs.gossip.CompatibleWithStore a ∧ UpdatesAuthorizedBy cs.gossip a
      · simp [applyGossipCanonicalStore, h]
      · simp [applyGossipCanonicalStore, h]
  | channelUpdate u =>
      rw [applyGossipNodeCanonical_update,
        applyGossipNodeCanonical_update]
      by_cases h : u.signatureValid verify ∧
          cs.gossip.updateKeyAnnouncedDirectional u ∧
            UpdateSupersedes u cs.gossip.updates
      · simp [applyGossipCanonicalStore, h]
      · simp [applyGossipCanonicalStore, h]
  | nodeAnnouncement n =>
      by_cases h : n.signatureValid verify ∧
          NodeSupersedes n cs.gossip.nodeAnnouncements
      · simp [applyGossipNodeCanonical, h]
      · simp [applyGossipNodeCanonical, h]

/-! ## 4. Invariant: the canonical store plus valid, canonical node records -/

/-- Every stored node announcement verifies under the abstract verifier. -/
def StoreNodeAnnouncementsValid (verify : SigVerifier)
    (s : GossipState) : Prop :=
  ∀ n ∈ s.nodeAnnouncements, n.signatureValid verify

/-- The node-canonical store invariant: all wave-7 store components, valid node
records, and at most one node record per `nodeId`. -/
structure NodeCanonicalAdmitted (verify : SigVerifier)
    (cs : CanonicalStore) : Prop where
  /-- The wave-7 canonical store invariant. -/
  base : CanonicalStoreAdmitted verify cs
  /-- Every stored node announcement verifies. -/
  nodesValid : StoreNodeAnnouncementsValid verify cs.gossip
  /-- At most one stored node record per `nodeId`. -/
  nodesCanonical : CanonicalNodeAnnouncements cs.gossip.nodeAnnouncements

/-- **The wave-7 canonical store invariant is preserved by its own transition.**
This is the store-level counterpart of the wave-6 network preservation lemmas. -/
theorem canonicalStoreAdmitted_applyGossipCanonicalStore
    (verify : SigVerifier) (cs : CanonicalStore) (m : GossipMessage)
    (hinv : CanonicalStoreAdmitted verify cs) :
    CanonicalStoreAdmitted verify
      (applyGossipCanonicalStore verify cs m) := by
  rcases hinv with ⟨hstore, hupdates, hnode, hcanon, hslots⟩
  cases m with
  | channelAnnouncement a =>
      by_cases hg : a.signaturesValid verify ∧ a.node1 ≠ a.node2 ∧
          cs.gossip.CompatibleWithStore a ∧
            UpdatesAuthorizedBy cs.gossip a
      · rw [applyGossipCanonicalStore_announcement_of_admitted verify cs a hg]
        rcases hg with ⟨hsig, hne, hcompat, hauth⟩
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro b hb
          rcases mem_insertReplacing_iff.mp hb with hba | ⟨hb, _⟩
          · rw [hba]
            exact hsig
          · exact hstore b hb
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
        · exact hslots
      · rw [applyGossipCanonicalStore_announcement_of_rejected verify cs a hg]
        exact ⟨hstore, hupdates, hnode, hcanon, hslots⟩
  | channelUpdate u =>
      by_cases hg : u.signatureValid verify ∧
          cs.gossip.updateKeyAnnouncedDirectional u ∧
            UpdateSupersedes u cs.gossip.updates
      · rw [applyGossipCanonicalStore_update_of_admitted verify cs u hg]
        rcases hg with ⟨husig, hk, _hsup⟩
        refine ⟨hstore, ?_, hnode, hcanon, ?_⟩
        · intro v hv
          rcases mem_insertUpdateCanonical_iff.mp hv with hvu | ⟨hvl, _⟩
          · subst v
            exact ⟨husig,
              updateKeyAnnouncedDirectional_of_announcements_eq rfl hk⟩
          · rcases hupdates v hvl with ⟨hvsig, hvk⟩
            exact ⟨hvsig,
              updateKeyAnnouncedDirectional_of_announcements_eq rfl hvk⟩
        · exact updatesSlotUnique_insertUpdateCanonical hslots
      · rw [applyGossipCanonicalStore_update_of_rejected verify cs u hg]
        exact ⟨hstore, hupdates, hnode, hcanon, hslots⟩
  | nodeAnnouncement n =>
      by_cases hg : n.signatureValid verify
      · rw [applyGossipCanonicalStore_node_of_valid verify cs n hg]
        exact ⟨hstore, hupdates, hnode, hcanon, hslots⟩
      · rw [applyGossipCanonicalStore_node_of_invalid verify cs n hg]
        exact ⟨hstore, hupdates, hnode, hcanon, hslots⟩

/-- **The node-canonical transition preserves the whole invariant.** -/
theorem nodeCanonicalAdmitted_applyGossipNodeCanonical
    (verify : SigVerifier) (cs : CanonicalStore) (m : GossipMessage)
    (hinv : NodeCanonicalAdmitted verify cs) :
    NodeCanonicalAdmitted verify
      (applyGossipNodeCanonical verify cs m) := by
  rcases hinv with ⟨hbase, hnvalid, hncanon⟩
  cases m with
  | channelAnnouncement a =>
      rw [applyGossipNodeCanonical_announcement]
      refine ⟨canonicalStoreAdmitted_applyGossipCanonicalStore verify cs
          (.channelAnnouncement a) hbase, ?_, ?_⟩
      · unfold StoreNodeAnnouncementsValid
        rw [applyGossipCanonicalStore_announcement_nodeAnnouncements]
        exact hnvalid
      · unfold CanonicalNodeAnnouncements
        rw [applyGossipCanonicalStore_announcement_nodeAnnouncements]
        exact hncanon
  | channelUpdate u =>
      rw [applyGossipNodeCanonical_update]
      refine ⟨canonicalStoreAdmitted_applyGossipCanonicalStore verify cs
          (.channelUpdate u) hbase, ?_, ?_⟩
      · unfold StoreNodeAnnouncementsValid
        rw [applyGossipCanonicalStore_update_nodeAnnouncements]
        exact hnvalid
      · unfold CanonicalNodeAnnouncements
        rw [applyGossipCanonicalStore_update_nodeAnnouncements]
        exact hncanon
  | nodeAnnouncement n =>
      by_cases hg : n.signatureValid verify ∧
          NodeSupersedes n cs.gossip.nodeAnnouncements
      · rw [applyGossipNodeCanonical_node_of_admitted verify cs n hg]
        rcases hg with ⟨hsig, _hsup⟩
        refine ⟨?_, ?_, ?_⟩
        · exact canonicalStoreAdmitted_nodeAnnouncements_irrel verify cs
            (insertNodeCanonical n cs.gossip.nodeAnnouncements) hbase
        · intro m hm
          rcases mem_insertNodeCanonical_iff.mp hm with hmn | ⟨hml, _⟩
          · rw [hmn]
            exact hsig
          · exact hnvalid m hml
        · exact canonicalNodeAnnouncements_insertNodeCanonical hncanon n
      · rw [applyGossipNodeCanonical_node_of_rejected verify cs n hg]
        exact ⟨hbase, hnvalid, hncanon⟩

/-- A store is node-canonically reachable when it is obtained from the empty
store (with an arbitrary registration map) by finitely many
`applyGossipNodeCanonical` steps. -/
inductive ReachableNodeCanonical (verify : SigVerifier) :
    CanonicalStore → Prop
  | empty (nodeKeyOf : NodeId → PubKey) :
      ReachableNodeCanonical verify
        { gossip := ⟨[], [], []⟩, nodeKeyOf := nodeKeyOf }
  | step {cs : CanonicalStore} {m : GossipMessage} :
      ReachableNodeCanonical verify cs →
        ReachableNodeCanonical verify
          (applyGossipNodeCanonical verify cs m)

/-- **The invariant of every node-canonically reachable store.** -/
theorem reachableNodeCanonical_invariant {verify : SigVerifier}
    {cs : CanonicalStore} (h : ReachableNodeCanonical verify cs) :
    NodeCanonicalAdmitted verify cs := by
  induction h with
  | empty nodeKeyOf =>
      refine ⟨?_, ?_, ?_⟩
      · refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro a ha
          simp at ha
        · intro u hu
          simp at hu
        · intro a ha
          simp at ha
        · intro a ha
          simp at ha
        · exact updatesSlotUnique_nil
      · intro n hn
        simp at hn
      · intro a ha
        simp at ha
  | step _ ih =>
      exact nodeCanonicalAdmitted_applyGossipNodeCanonical verify _ _ ih

/-- Reachable node-canonical states have at most one node record per key. -/
theorem reachableNodeCanonical_nodesCanonical {verify : SigVerifier}
    {cs : CanonicalStore} (h : ReachableNodeCanonical verify cs) :
    CanonicalNodeAnnouncements cs.gossip.nodeAnnouncements :=
  (reachableNodeCanonical_invariant h).nodesCanonical

/-- Reachable node-canonical states store only verifying node records. -/
theorem reachableNodeCanonical_nodesValid {verify : SigVerifier}
    {cs : CanonicalStore} (h : ReachableNodeCanonical verify cs) :
    StoreNodeAnnouncementsValid verify cs.gossip :=
  (reachableNodeCanonical_invariant h).nodesValid

/-- Reachable node-canonical states keep the wave-7 store invariant. -/
theorem reachableNodeCanonical_store_invariant {verify : SigVerifier}
    {cs : CanonicalStore} (h : ReachableNodeCanonical verify cs) :
    CanonicalStoreAdmitted verify cs :=
  (reachableNodeCanonical_invariant h).base

/-- Reachable node-canonical states keep node-key consistency. -/
theorem reachableNodeCanonical_nodeKeyConsistent {verify : SigVerifier}
    {cs : CanonicalStore} (h : ReachableNodeCanonical verify cs) :
    GossipState.NodeKeyConsistent cs.nodeKeyOf cs.gossip :=
  (reachableNodeCanonical_store_invariant h).nodeKeys

/-- Reachable node-canonical states keep one channel announcement per
`short_channel_id`. -/
theorem reachableNodeCanonical_canonical {verify : SigVerifier}
    {cs : CanonicalStore} (h : ReachableNodeCanonical verify cs) :
    CanonicalAnnouncements cs.gossip.announcements :=
  (reachableNodeCanonical_store_invariant h).canonical

/-- Reachable node-canonical states keep per-slot update uniqueness. -/
theorem reachableNodeCanonical_updates_slotUnique {verify : SigVerifier}
    {cs : CanonicalStore} (h : ReachableNodeCanonical verify cs) :
    UpdatesSlotUnique cs.gossip.updates :=
  (reachableNodeCanonical_store_invariant h).updatesSlotUnique

/-! ## 5. Concrete reachable witnesses -/

private def acceptAll : SigVerifier := fun _ _ _ => true

/-- Byte length 1. -/
private def kA : PubKey := ⟨ByteArray.mk #[1]⟩

/-- Byte length 0. -/
private def kB : PubKey := ⟨ByteArray.empty⟩

private def nA : NodeId := ⟨0⟩

private def nB : NodeId := ⟨1⟩

private def sc1 : ShortChannelId := ⟨1, 2, 3⟩

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

private def aliasOne : ByteArray := ByteArray.mk #[1]

private def aliasTwo : ByteArray := ByteArray.mk #[1, 2]

private def mkNode (k : PubKey) (ts : Nat) (alias : ByteArray) :
    NodeAnnouncement :=
  { nodeId := k
    timestamp := ts
    rgbColor := ByteArray.empty
    alias := alias
    addresses := []
    digest := ByteArray.empty
    signature := emptySig }

private theorem kA_ne_kB : kA ≠ kB := by
  intro h
  have hs := congrArg (fun k => k.bytes.size) h
  have h1 : kA.bytes.size = 1 := by decide
  have h2 : kB.bytes.size = 0 := rfl
  rw [h1, h2] at hs
  exact Nat.noConfusion hs

private theorem aliasOne_ne_aliasTwo : aliasOne ≠ aliasTwo := by
  intro h
  have hs := congrArg (fun b => b.size) h
  have h1 : aliasOne.size = 1 := by decide
  have h2 : aliasTwo.size = 2 := by decide
  rw [h1, h2] at hs
  omega

private theorem nA_ne_nB : nA ≠ nB := by decide

/-- The reference node record: key `kA`, timestamp `10`. -/
private def nA1 : NodeAnnouncement := mkNode kA 10 aliasOne

/-- A strictly newer record for the same key: timestamp `20`. -/
private def nA2 : NodeAnnouncement := mkNode kA 20 aliasOne

/-- A same-timestamp record for the same key with different content. -/
private def nATie : NodeAnnouncement := mkNode kA 20 aliasTwo

/-- A different key, non-zero timestamp: a rotated node identity. -/
private def nB1 : NodeAnnouncement := mkNode kB 15 aliasOne

/-- A low-timestamp record for the same key as `nA`. -/
private def nLow : NodeAnnouncement := mkNode kA 5 aliasOne

private theorem nA2_ne_nATie : nA2 ≠ nATie := by
  intro h
  have ha := congrArg NodeAnnouncement.alias h
  exact aliasOne_ne_aliasTwo ha

private theorem nATie_ne_nA2 : nATie ≠ nA2 := fun h => nA2_ne_nATie h.symm

private theorem nA1_ne_nA2 : nA1 ≠ nA2 := by
  intro h
  have ht := congrArg NodeAnnouncement.timestamp h
  simp [nA1, nA2, mkNode] at ht

private theorem nA2_ne_nA1 : nA2 ≠ nA1 := fun h => nA1_ne_nA2 h.symm

private theorem nB1_ne_nA1 : nB1 ≠ nA1 := by
  intro h
  have hk := congrArg NodeAnnouncement.nodeId h
  exact kA_ne_kB (by simpa [nA1, nB1, mkNode] using hk.symm)

private theorem node_valid (n : NodeAnnouncement) :
    n.signatureValid acceptAll := by
  simp [NodeAnnouncement.signatureValid, signatureValid, acceptAll]

private theorem nA2_supersedes_nA1 : NodeSupersedes nA2 [nA1] := by
  intro m hm hnode
  simp only [List.mem_singleton] at hm
  subst m
  simp [nA1, nA2, mkNode]

private def ns0 : CanonicalStore :=
  { gossip := ⟨[], [], []⟩, nodeKeyOf := fun _ => kB }

private theorem gateNA1 : nA1.signatureValid acceptAll ∧
    NodeSupersedes nA1 ns0.gossip.nodeAnnouncements := by
  refine ⟨node_valid nA1, ?_⟩
  intro m hm
  simp [ns0] at hm

private noncomputable def ns1 : CanonicalStore :=
  applyGossipNodeCanonical acceptAll ns0 (.nodeAnnouncement nA1)

private theorem ns1_nodes : ns1.gossip.nodeAnnouncements = [nA1] := by
  rw [ns1, applyGossipNodeCanonical_node_of_admitted acceptAll ns0 nA1 gateNA1]
  simp [ns0, insertNodeCanonical]

private theorem ns1_reachable : ReachableNodeCanonical acceptAll ns1 := by
  unfold ns1
  exact ReachableNodeCanonical.step
    (ReachableNodeCanonical.empty (fun _ => kB))

private theorem gateNA2 : nA2.signatureValid acceptAll ∧
    NodeSupersedes nA2 ns1.gossip.nodeAnnouncements := by
  refine ⟨node_valid nA2, ?_⟩
  rw [ns1_nodes]
  exact nA2_supersedes_nA1

private noncomputable def ns2 : CanonicalStore :=
  applyGossipNodeCanonical acceptAll ns1 (.nodeAnnouncement nA2)

private theorem ns2_nodes : ns2.gossip.nodeAnnouncements = [nA2] := by
  rw [ns2, applyGossipNodeCanonical_node_of_admitted acceptAll ns1 nA2 gateNA2]
  rw [ns1_nodes]
  simp [insertNodeCanonical, nA1, nA2, mkNode]

private theorem ns2_reachable : ReachableNodeCanonical acceptAll ns2 := by
  unfold ns2
  exact ReachableNodeCanonical.step ns1_reachable

private theorem not_supersedes_tie :
    ¬ NodeSupersedes nATie ns2.gossip.nodeAnnouncements := by
  intro h
  rw [ns2_nodes] at h
  have hlt := h nA2 (by simp) rfl
  simp [nA2, nATie, mkNode] at hlt

private theorem not_gate_tie : ¬ (nATie.signatureValid acceptAll ∧
    NodeSupersedes nATie ns2.gossip.nodeAnnouncements) := by
  intro h
  exact not_supersedes_tie h.2

private noncomputable def nsTie : CanonicalStore :=
  applyGossipNodeCanonical acceptAll ns2 (.nodeAnnouncement nATie)

private theorem nsTie_eq_ns2 : nsTie = ns2 := by
  rw [nsTie, applyGossipNodeCanonical_node_of_rejected acceptAll ns2 nATie
    not_gate_tie]

private theorem nsTie_nodes : nsTie.gossip.nodeAnnouncements = [nA2] := by
  rw [nsTie_eq_ns2, ns2_nodes]

private theorem nsTie_reachable : ReachableNodeCanonical acceptAll nsTie := by
  unfold nsTie
  exact ReachableNodeCanonical.step ns2_reachable

private theorem nB1_supersedes_nA1 : NodeSupersedes nB1 [nA1] := by
  intro m hm hnode
  simp only [List.mem_singleton] at hm
  subst m
  exact absurd hnode kA_ne_kB

private theorem gateNB1 : nB1.signatureValid acceptAll ∧
    NodeSupersedes nB1 ns1.gossip.nodeAnnouncements := by
  refine ⟨node_valid nB1, ?_⟩
  rw [ns1_nodes]
  exact nB1_supersedes_nA1

private noncomputable def nsRot : CanonicalStore :=
  applyGossipNodeCanonical acceptAll ns1 (.nodeAnnouncement nB1)

private theorem nsRot_nodes : nsRot.gossip.nodeAnnouncements = [nB1, nA1] := by
  rw [nsRot, applyGossipNodeCanonical_node_of_admitted acceptAll ns1 nB1 gateNB1]
  rw [ns1_nodes]
  simp [insertNodeCanonical, nA1, nB1, mkNode, kA_ne_kB]

private theorem nsRot_reachable : ReachableNodeCanonical acceptAll nsRot := by
  unfold nsRot
  exact ReachableNodeCanonical.step ns1_reachable

/-! ## 6. Per-slot / global-clock boundary -/

private def annA : ChannelAnnellation := mkAnn sc1 nA nB kA kB 1000

private def u100 : ChannelUpdate := mkUpd sc1 100 kA

private theorem annA_valid : annA.signaturesValid acceptAll := by
  simp [ChannelAnnellation.signaturesValid, signatureValid, acceptAll]

private theorem u100_valid : u100.signatureValid acceptAll := by
  simp [ChannelUpdate.signatureValid, signatureValid, acceptAll]

private theorem gateAnnA :
    CanonicalMessageAdmitted acceptAll ns0 (.channelAnnouncement annA) := by
  simp [CanonicalMessageAdmitted, ChannelAnnellation.signaturesValid, signatureValid,
    acceptAll, annA, mkAnn, GossipState.CompatibleWithStore, UpdatesAuthorizedBy,
    nA_ne_nB, ns0]

private noncomputable def gs1 : CanonicalStore :=
  applyGossipNodeCanonical acceptAll ns0 (.channelAnnouncement annA)

private theorem gs1_ann : gs1.gossip.announcements = [annA] := by
  rw [gs1, applyGossipNodeCanonical_announcement,
    applyGossipCanonicalStore_announcement_of_admitted acceptAll ns0 annA gateAnnA]
  simp [ns0, insertReplacing]

private theorem gs1_upd : gs1.gossip.updates = [] := by
  rw [gs1, applyGossipNodeCanonical_announcement,
    applyGossipCanonicalStore_announcement_of_admitted acceptAll ns0 annA gateAnnA]
  simp [ns0]

private theorem gs1_nodes : gs1.gossip.nodeAnnouncements = [] := by
  rw [gs1, applyGossipNodeCanonical_announcement,
    applyGossipCanonicalStore_announcement_of_admitted acceptAll ns0 annA gateAnnA]
  simp [ns0]

private theorem gs1_attributed_u100 :
    gs1.gossip.updateKeyAnnouncedDirectional u100 := by
  refine GossipState.updateKeyAnnouncedDirectional_of_mem (a := annA) ?_ rfl ?_
  · rw [gs1_ann]
    simp
  · rw [ChannelUpdate.direction_of_channelFlags_zero
      (by rfl : u100.channelFlags = 0)]
    exact ChannelAnnellation.attributesKeyForDirection_node1 annA

private theorem gs1_supersedes_u100 :
    UpdateSupersedes u100 gs1.gossip.updates := by
  intro v hv
  rw [gs1_upd] at hv
  simp at hv

private theorem gateU100 :
    CanonicalMessageAdmitted acceptAll gs1 (.channelUpdate u100) :=
  ⟨u100_valid, gs1_attributed_u100, gs1_supersedes_u100⟩

private noncomputable def gs2 : CanonicalStore :=
  applyGossipNodeCanonical acceptAll gs1 (.channelUpdate u100)

private theorem gs2_upd : gs2.gossip.updates = [u100] := by
  rw [gs2, applyGossipNodeCanonical_update,
    applyGossipCanonicalStore_update_of_admitted acceptAll gs1 u100 gateU100]
  simp [gs1_upd, insertUpdateCanonical]

private theorem gs2_latest : gs2.gossip.latestUpdateTimestamp = 100 := by
  rw [GossipState.latestUpdateTimestamp, gs2_upd]
  simp [latestTimestamp, u100, mkUpd]

private theorem gs2_nodes : gs2.gossip.nodeAnnouncements = [] := by
  rw [gs2, applyGossipNodeCanonical_update,
    applyGossipCanonicalStore_update_of_admitted acceptAll gs1 u100 gateU100]
  exact gs1_nodes

private theorem gs2_reachable : ReachableNodeCanonical acceptAll gs2 := by
  unfold gs2 gs1
  exact ReachableNodeCanonical.step
    (ReachableNodeCanonical.step
      (ReachableNodeCanonical.empty (fun _ => kB)))

private theorem nLow_supersedes_empty :
    NodeSupersedes nLow gs2.gossip.nodeAnnouncements := by
  intro m hm
  rw [gs2_nodes] at hm
  simp at hm

private theorem gateNLow : nLow.signatureValid acceptAll ∧
    NodeSupersedes nLow gs2.gossip.nodeAnnouncements :=
  ⟨node_valid nLow, nLow_supersedes_empty⟩

private noncomputable def gs3 : CanonicalStore :=
  applyGossipNodeCanonical acceptAll gs2 (.nodeAnnouncement nLow)

private theorem gs3_nodes : gs3.gossip.nodeAnnouncements = [nLow] := by
  rw [gs3, applyGossipNodeCanonical_node_of_admitted acceptAll gs2 nLow gateNLow,
    gs2_nodes]
  simp [insertNodeCanonical]

/-! ## 7. Replacement and rotation -/

/-- **A reachable node-slot replacement is real.**  A strictly newer record
replaces the older record with the same `nodeId`: the newer one is stored and
the older one is gone. -/
theorem reachableNodeCanonical_node_replacement :
    ∃ (verify : SigVerifier) (cs : CanonicalStore)
      (nOld nNew : NodeAnnouncement),
      ReachableNodeCanonical verify cs ∧
        nOld.nodeId = nNew.nodeId ∧
          nOld.timestamp < nNew.timestamp ∧
            nNew ∈ cs.gossip.nodeAnnouncements ∧
              nOld ∉ cs.gossip.nodeAnnouncements := by
  refine ⟨acceptAll, ns2, nA1, nA2, ns2_reachable, rfl, ?_, ?_, ?_⟩
  · simp [nA1, nA2, mkNode]
  · rw [ns2_nodes]
    exact List.mem_singleton_self nA2
  · rw [ns2_nodes]
    simp [nA1_ne_nA2]

/-- **Rotation creates a distinct canonical slot, not a replacement.**  Two
records with different `nodeId` keys are kept side by side even when they name
the same physical node (same alias/addresses).  This is the node analogue of
the wave-6 registration-only rotation boundary. -/
theorem reachableNodeCanonical_rotation_keeps_both :
    ∃ (verify : SigVerifier) (cs : CanonicalStore)
      (nOld nNew : NodeAnnouncement),
      ReachableNodeCanonical verify cs ∧
        nOld.nodeId ≠ nNew.nodeId ∧
          nOld.alias = nNew.alias ∧
            nOld ∈ cs.gossip.nodeAnnouncements ∧
              nNew ∈ cs.gossip.nodeAnnouncements ∧
                CanonicalNodeAnnouncements cs.gossip.nodeAnnouncements := by
  refine ⟨acceptAll, nsRot, nA1, nB1, nsRot_reachable, ?_, ?_, ?_, ?_,
    reachableNodeCanonical_nodesCanonical nsRot_reachable⟩
  · intro h
    exact kA_ne_kB h
  · simp [nA1, nB1, mkNode]
  · rw [nsRot_nodes]
    simp
  · rw [nsRot_nodes]
    simp

/-- Rekeying the graph registration map does not change the gossip effect of
node canonicalisation. -/
theorem applyGossipNodeCanonical_gossip_rotateNodeKey
    (verify : SigVerifier) (cs : CanonicalStore) (n : NodeId) (k : PubKey)
    (m : GossipMessage) :
    (applyGossipNodeCanonical verify
        { cs with nodeKeyOf := rotateNodeKey cs.nodeKeyOf n k } m).gossip =
      (applyGossipNodeCanonical verify cs m).gossip :=
  applyGossipNodeCanonical_gossip_nodeKeyOf_irrel verify cs
    (rotateNodeKey cs.nodeKeyOf n k) m

/-- Rekeying channel announcements (the wave-6 `rekeyStore`) leaves the node
list untouched and therefore preserves node canonicality. -/
theorem canonicalNodeAnnouncements_rekeyStore {s : GossipState}
    (hc : CanonicalNodeAnnouncements s.nodeAnnouncements)
    (n : NodeId) (k : PubKey) :
    CanonicalNodeAnnouncements (rekeyStore s n k).nodeAnnouncements := by
  simpa [rekeyStore] using hc

/-- The reachable canonical node list survives channel-announcement rekeying. -/
theorem reachableNodeCanonical_rekeyStore {verify : SigVerifier}
    {cs : CanonicalStore} (h : ReachableNodeCanonical verify cs)
    (n : NodeId) (k : PubKey) :
    CanonicalNodeAnnouncements (rekeyStore cs.gossip n k).nodeAnnouncements :=
  canonicalNodeAnnouncements_rekeyStore
    (reachableNodeCanonical_nodesCanonical h) n k

/-! ## 8. The unrecoverable boundary -/

/-- **Equal-timestamp tie boundary.**  Two distinct records with the same
`nodeId` and the same timestamp cannot be ordered by the BOLT 7 gate: the
canonical transition keeps the first-arrived record, while raw append puts the
late record at the head and `selectNodeAnnouncements` then selects it.
Canonicalisation therefore does not recover a "true newest" owner of a tied
timestamp. -/
theorem reachableNodeCanonical_equal_timestamp_tie_boundary :
    ∃ (verify : SigVerifier) (cs : CanonicalStore)
      (nOld nTie : NodeAnnouncement),
      ReachableNodeCanonical verify cs ∧
        nOld ∈ cs.gossip.nodeAnnouncements ∧
          nTie ∉ cs.gossip.nodeAnnouncements ∧
            nOld.nodeId = nTie.nodeId ∧
              nOld.timestamp = nTie.timestamp ∧
                nOld ≠ nTie ∧
                  ¬ CanonicalNodeAnnouncements
                    (applyGossip cs.gossip (.nodeAnnouncement nTie)).nodeAnnouncements ∧
                    selectNodeAnnouncements
                        (applyGossip cs.gossip (.nodeAnnouncement nTie)).nodeAnnouncements =
                      [nTie] ∧
                      (canonicalNodeStoreView
                        (applyGossip cs.gossip (.nodeAnnouncement nTie))).nodeAnnouncements =
                        [nTie] ∧
                        cs.gossip.nodeAnnouncements = [nOld] := by
  refine ⟨acceptAll, ns2, nA2, nATie, ns2_reachable, ?_, ?_, rfl, rfl,
    nA2_ne_nATie, ?_, ?_, ?_, ns2_nodes⟩
  · rw [ns2_nodes]
    exact List.mem_singleton_self nA2
  · rw [ns2_nodes]
    simp [nATie_ne_nA2]
  · -- raw append produces `[nATie, nA2]`, which is not canonical
    rw [applyGossip]
    simp only [ns2_nodes]
    intro hc
    have hsame : nATie = nA2 := hc nATie (by simp) nA2 (by simp) rfl
    exact nA2_ne_nATie hsame.symm
  · -- head-most selection picks the late record
    rw [applyGossip]
    simp only [ns2_nodes]
    simp [selectNodeAnnouncements, insertNodeCanonical, nA2, nATie, mkNode]
  · rw [applyGossip]
    simp only [ns2_nodes]
    simp [canonicalNodeStoreView, canonicalStoreView, selectNodeAnnouncements,
      insertNodeCanonical, nA2, nATie, mkNode]

/-- **No canonical-node-preserving raw node extension.**  Any transition that
keeps raw append semantics for `node_announcement` cannot preserve
`CanonicalNodeAnnouncements` from the empty store: two distinct records for the
same `nodeId` are both appended, while canonicality demands a replacement step
that raw append does not have.  This is the node analogue of
`no_canonical_preserving_raw_announcement_extension`. -/
theorem no_canonical_node_preserving_raw_node_extension :
    ¬ ∃ F : GossipState → GossipMessage → GossipState,
      (∀ (s : GossipState) (n : NodeAnnouncement),
        F s (.nodeAnnouncement n) = applyGossip s (.nodeAnnouncement n)) ∧
      (∀ s : GossipState, CanonicalNodeAnnouncements s.nodeAnnouncements →
        ∀ m : GossipMessage,
          CanonicalNodeAnnouncements (F s m).nodeAnnouncements) := by
  rintro ⟨F, hraw, hpres⟩
  have hempty : CanonicalNodeAnnouncements ([] : List NodeAnnouncement) := by
    intro a ha
    simp at ha
  have h1 : CanonicalNodeAnnouncements
      (F ⟨[], [], []⟩ (.nodeAnnouncement nA2)).nodeAnnouncements :=
    hpres ⟨[], [], []⟩ hempty _
  have hstep1 : F ⟨[], [], []⟩ (.nodeAnnouncement nA2) =
      (⟨[], [], [nA2]⟩ : GossipState) := by
    rw [hraw]
    rfl
  have h2 : CanonicalNodeAnnouncements
      (F (F ⟨[], [], []⟩ (.nodeAnnouncement nA2))
        (.nodeAnnouncement nATie)).nodeAnnouncements :=
    hpres _ h1 _
  rw [hstep1, hraw] at h2
  simp [applyGossip] at h2
  have hsame : nATie = nA2 := h2 nATie (by simp) nA2 (by simp) rfl
  exact nA2_ne_nATie hsame.symm

/-- Raw `applyGossip` appends a same-node record even when the stored list is
canonical, so the existing `canonicalStoreView` still leaves a non-canonical
node list.  This is the exact `RT-02` gap that the node layer closes. -/
theorem canonicalStoreView_does_not_canonicalise_nodes :
    ∃ (s : GossipState) (n : NodeAnnouncement),
      CanonicalNodeAnnouncements s.nodeAnnouncements ∧
        ¬ CanonicalNodeAnnouncements
          (canonicalStoreView (applyGossip s (.nodeAnnouncement n))).nodeAnnouncements := by
  refine ⟨⟨[], [], [nA2]⟩, nATie, ?_, ?_⟩
  · intro a ha b hb hkey
    simp only [List.mem_singleton] at ha hb
    rw [ha, hb]
  · simp only [canonicalStoreView, applyGossip]
    intro hc
    have hsame : nATie = nA2 := hc nATie (by simp) nA2 (by simp) rfl
    exact nA2_ne_nATie hsame.symm

/-- **The node gate is per `nodeId`, not the raw global clock.**  A reachable
store can have a channel-update clock of `100` while a node announcement at
timestamp `5` is admitted because its own node slot is fresh. -/
theorem reachableNodeCanonical_node_slot_ignores_global_clock :
    ∃ (verify : SigVerifier) (cs : CanonicalStore) (n : NodeAnnouncement),
      ReachableNodeCanonical verify cs ∧
        cs.gossip.latestUpdateTimestamp = 100 ∧
          n.timestamp = 5 ∧
            NodeSupersedes n cs.gossip.nodeAnnouncements ∧
              (applyGossipNodeCanonical verify cs
                (.nodeAnnouncement n)).gossip.nodeAnnouncements = [n] ∧
                n.timestamp < cs.gossip.latestUpdateTimestamp := by
  refine ⟨acceptAll, gs2, nLow, gs2_reachable, gs2_latest, rfl,
    nLow_supersedes_empty, ?_, ?_⟩
  · exact gs3_nodes
  · simp [nLow, mkNode, gs2_latest]

/-! ## 9. Preserved wave-7/8 results -/

/-- Wave-7 raw non-refinement, re-exported unchanged: raw `applyGossip` still
accepts a conflicting announcement and is not a function refinement of
canonical admission. -/
theorem raw_nonrefinement_preserved :
    ∃ (s : GossipState) (a : ChannelAnnellation),
      ¬ CanonicalAnnouncements
        (applyGossip s (.channelAnnouncement a)).announcements :=
  GossipRawRefinementTargets.raw_conflicting_announcement_counterexample_preserved

/-- Wave-7 impossibility, re-exported unchanged: no raw-append extension of
`channel_announcement` preserves canonicality from the empty store. -/
theorem raw_announcement_extension_impossible_preserved :
    ¬ ∃ F : GossipState → GossipMessage → GossipState,
      (∀ (s : GossipState) (a : ChannelAnnellation),
        F s (.channelAnnouncement a) = applyGossip s (.channelAnnouncement a)) ∧
      (∀ s : GossipState, CanonicalAnnouncements s.announcements →
        ∀ m : GossipMessage,
          CanonicalAnnouncements (F s m).announcements) :=
  GossipRawRefinementTargets.no_canonical_preserving_raw_announcement_extension

/-- Wave-7 per-slot/global-clock separation, re-exported unchanged: the
canonical per-slot update gate is strictly weaker than the raw global clock. -/
theorem per_slot_global_clock_boundary_preserved :
    ∃ (verify : SigVerifier) (cs : CanonicalStore) (u : ChannelUpdate),
      ReachableCanonicalStore verify cs ∧
        CanonicalMessageAdmitted verify cs (.channelUpdate u) ∧
          ¬ RawClockAdmits cs.gossip (.channelUpdate u) ∧
            (applyGossipCanonicalStore verify cs (.channelUpdate u)).gossip.updates =
              u :: cs.gossip.updates ∧
              applyGossip cs.gossip (.channelUpdate u) = cs.gossip ∧
                u ∉ cs.gossip.updates :=
  GossipRawRefinementTargets.canonical_admission_strictly_weaker_than_raw_clock

/-- Wave-8 sequence-level epoch square, re-exported unchanged. -/
theorem epoch_square_preserved
    (verify : SigVerifier) (e : StoreEpoch) (s : GossipState)
    (msgs : List GossipMessage)
    (hobs : e.store.gossip = canonicalStoreView s)
    (hadm : EpochAdmittedAlong verify e msgs)
    (hraw : RawAdmittedAlong s msgs) :
    (epochFold verify e msgs).store.gossip =
      canonicalStoreView (rawFold s msgs) :=
  epochFold_gossip_eq_canonicalStoreView_rawFold verify e s msgs
    hobs hadm hraw

/-- Wave-8 unconditional epoch/canonical store square, re-exported unchanged. -/
theorem epoch_fold_store_square_preserved
    (verify : SigVerifier) (e : StoreEpoch) (msgs : List GossipMessage) :
    (epochFold verify e msgs).store =
      msgs.foldl (fun cs m => applyGossipCanonicalStore verify cs m) e.store :=
  StoreEpoch.epochFold_store_eq_foldl verify e msgs

/-- **The epoch square lifts to the node-canonical view on node-canonical raw
folds.**  When the raw fold's node list is duplicate-free and canonical, node
selection is the identity, so the node-canonical view is the wave-8 canonical
view and the epoch square is unchanged. -/
theorem epoch_square_lifts_to_node_canonical_view
    (verify : SigVerifier) (e : StoreEpoch) (s : GossipState)
    (msgs : List GossipMessage)
    (hobs : e.store.gossip = canonicalStoreView s)
    (hadm : EpochAdmittedAlong verify e msgs)
    (hraw : RawAdmittedAlong s msgs)
    (hnd : (rawFold s msgs).nodeAnnouncements.Nodup)
    (hnc : CanonicalNodeAnnouncements (rawFold s msgs).nodeAnnouncements) :
    (epochFold verify e msgs).store.gossip =
      canonicalNodeStoreView (rawFold s msgs) := by
  have hsel : selectNodeAnnouncements (rawFold s msgs).nodeAnnouncements =
      (rawFold s msgs).nodeAnnouncements :=
    selectNodeAnnouncements_of_nodup_canonical hnd hnc
  rw [canonicalNodeStoreView_eq_canonicalStoreView_of_select_eq_self _
    hsel]
  exact epoch_square_preserved verify e s msgs hobs hadm hraw

end LnLean.Proofs.Routing.NodeCanonicalTargets
