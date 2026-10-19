import LnLean.Proofs.Routing.NodeCanonicalTargets

/-!
# LnLean.Proofs.Routing.NodeIdentityTargets

Wave-10 lane `S10-RT-NODE-IDENTITY`, open issue `RT-02`.

Wave 9 (`NodeCanonicalTargets`) made node announcements canonical: one record
per wire `nodeId`, strict-timestamp replacement, a node-canonical view, a
node-canonical transition, and the `NodeCanonicalAdmitted` invariant.  It also
proved the rotation *boundary*: two records with different `nodeId`s occupy
different canonical slots and both survive.  It deliberately did not model
identity or linkage across such a rotation, nor wire-level node membership.

This module adds the next additive layer.  It does not edit `Gossip.lean`,
`NodeCanonicalTargets.lean`, or any shared file.

## Model

* `NodeAnnounced` / `NodeAnnouncedValid`: a wire node key is backed by a stored
  node announcement (and by a signature-valid one).
* `RotationWitness`: an *explicit input* carrying an old key, a new key, opaque
  out-of-band evidence, and the distinctness proof.  It is not read from the
  store.  `RotationWitness.rotateChannel` rewrites the two wire node-key fields
  of a channel announcement.
* `StoreOnly`: a relation on node keys is store-only when it depends only on
  which keys the node-announcement list currently backs.
* `WireMember` / `WireMemberCertified`: both wire node keys of a channel
  announcement are backed by stored (valid) node announcements.

## Results

* `no_oriented_store_only_link`: no antisymmetric store-only relation can hold
  between two distinct co-announced keys.  In particular the intended rotation
  direction `kA → kB` is not store-only
  (`concrete_intended_rotation_not_storeOnly`).  Orientation requires the
  external `RotationWitness`.
* `rotation_preserves_wireMember`: given a witness and a stored announcement
  for the new key, rewriting the old endpoint to the new key preserves wire
  membership.  The channel identity, graph endpoints, and capacity are
  unchanged; signatures are **not** preserved
  (`rotation_breaks_signatures`).
* `channelAnnouncement_admitted_of_wireMember`: under `NodeCanonicalAdmitted`,
  a certified wire-member announcement that passes the existing canonical
  channel gates is admitted, remains a wire member, and preserves the node
  invariant.
* `missing_endpoint_channel_admitted`: the existing core transition does not
  check wire membership.  A channel whose second endpoint has no node
  announcement is still admitted, so membership is an additive gate, not a
  consequence of `NodeCanonicalAdmitted`.
* `wireMember_applyGossipNodeCanonical`: node-key membership is monotone under
  the canonical node transition.  Same-key replacement supersedes the old
  record but never withdraws its key; rotation keeps both keys.

What is **not** claimed:

* The witness is opaque evidence, not a cryptographic proof.  No theorem says
  two different keys belong to the same physical node.
* `NodeAnnouncement.nodeId` is the BOLT 7 wire node key (`PubKey`); graph
  `NodeId` registration is a separate map.  Address parsing is not modelled.
* Channel `node1`/`node2` are graph indices; wire membership is stated on the
  announced key fields `nodeKey1`/`nodeKey2`, which are the BOLT 7 `node_id`
  values carried by `channel_announcement`.
* Chain-hash filtering, funding-outpoint/UTXO confirmation, node-announcement
  relay policy, and rate limits are not modelled.
* `SigVerifier` stays abstract; unforgeability remains assumptions C3/C4/C8.
* The core admission transition is not changed and does not enforce wire
  membership.  No full BOLT 7 gossip-validation claim is made.

Lean 4 core only, no Mathlib.  Allowed axioms: `propext`, `Quot.sound`,
`Classical.choice`.
-/

namespace LnLean.Proofs.Routing.NodeIdentityTargets

open LnLean.Routing
open LnLean.Routing.GossipProps
open LnLean.Proofs.Routing.GossipCanonicalTargets
open LnLean.Proofs.Routing.GossipRawRefinementTargets
open LnLean.Proofs.Routing.NodeCanonicalTargets
open Classical

set_option autoImplicit false

/-! ## 1. Node-announcement backing -/

/-- A wire node key is backed by the node-announcement list. -/
def NodeAnnouncedIn (l : List NodeAnnouncement) (k : PubKey) : Prop :=
  ∃ n ∈ l, n.nodeId = k

/-- A wire node key is backed by the store's node-announcement list. -/
def NodeAnnounced (s : GossipState) (k : PubKey) : Prop :=
  NodeAnnouncedIn s.nodeAnnouncements k

/-- A wire node key is backed by a signature-valid stored node announcement. -/
def NodeAnnouncedValid (verify : SigVerifier) (s : GossipState)
    (k : PubKey) : Prop :=
  ∃ n ∈ s.nodeAnnouncements, n.nodeId = k ∧ n.signatureValid verify

/-- A valid backing record is a backing record. -/
theorem nodeAnnounced_of_valid {verify : SigVerifier} {s : GossipState}
    {k : PubKey} (h : NodeAnnouncedValid verify s k) : NodeAnnounced s k := by
  rcases h with ⟨n, hn, hk, _⟩
  exact ⟨n, hn, hk⟩

/-- Backing is monotone in the node-announcement list. -/
theorem nodeAnnouncedIn_mono {l l' : List NodeAnnouncement} {k : PubKey}
    (hsub : ∀ n ∈ l, n ∈ l') (h : NodeAnnouncedIn l k) :
    NodeAnnouncedIn l' k := by
  rcases h with ⟨n, hn, hk⟩
  exact ⟨n, hsub n hn, hk⟩

/-- Backing is monotone in the store. -/
theorem nodeAnnounced_mono {s t : GossipState} {k : PubKey}
    (hsub : ∀ n ∈ s.nodeAnnouncements, n ∈ t.nodeAnnouncements)
    (h : NodeAnnounced s k) : NodeAnnounced t k :=
  nodeAnnouncedIn_mono hsub h

/-- **Node replacement never withdraws a key.**  Inserting `n` keeps the
incoming key and every previously backed key.  In particular a same-key
replacement keeps that key (with the new record) and a different-key rotation
keeps the old record as well. -/
theorem nodeAnnouncedIn_insertNodeCanonical_iff {n : NodeAnnouncement}
    {l : List NodeAnnouncement} {k : PubKey} :
    NodeAnnouncedIn (insertNodeCanonical n l) k ↔
      n.nodeId = k ∨ NodeAnnouncedIn l k := by
  constructor
  · rintro ⟨m, hm, hk⟩
    rcases mem_insertNodeCanonical_iff.mp hm with rfl | ⟨hml, _⟩
    · exact Or.inl hk
    · exact Or.inr ⟨m, hml, hk⟩
  · rintro (hk | ⟨m, hm, hk⟩)
    · exact ⟨n, List.mem_cons_self .., hk⟩
    · by_cases hsame : m.nodeId = n.nodeId
      · exact ⟨n, List.mem_cons_self .., hsame.symm.trans hk⟩
      · exact ⟨m, mem_insertNodeCanonical_of_mem_of_ne hm hsame, hk⟩

/-- Store form of `nodeAnnouncedIn_insertNodeCanonical_iff`. -/
theorem nodeAnnounced_insertNodeCanonical_iff (cs : CanonicalStore)
    (n : NodeAnnouncement) (k : PubKey) :
    NodeAnnounced
        { cs.gossip with
          nodeAnnouncements :=
            insertNodeCanonical n cs.gossip.nodeAnnouncements } k ↔
      n.nodeId = k ∨ NodeAnnounced cs.gossip k := by
  simpa [NodeAnnounced] using
    (nodeAnnouncedIn_insertNodeCanonical_iff
      (n := n) (l := cs.gossip.nodeAnnouncements) (k := k))

/-- A node key backed before a canonical gossip step is backed after it. -/
theorem nodeAnnounced_applyGossipNodeCanonical (verify : SigVerifier)
    (cs : CanonicalStore) (m : GossipMessage) {k : PubKey}
    (h : NodeAnnounced cs.gossip k) :
    NodeAnnounced (applyGossipNodeCanonical verify cs m).gossip k := by
  cases m with
  | channelAnnouncement a =>
      rw [applyGossipNodeCanonical_announcement]
      simpa [NodeAnnounced,
        applyGossipCanonicalStore_announcement_nodeAnnouncements] using h
  | channelUpdate u =>
      rw [applyGossipNodeCanonical_update]
      simpa [NodeAnnounced,
        applyGossipCanonicalStore_update_nodeAnnouncements] using h
  | nodeAnnouncement n =>
      by_cases hg : n.signatureValid verify ∧
          NodeSupersedes n cs.gossip.nodeAnnouncements
      · rw [applyGossipNodeCanonical_node_of_admitted verify cs n hg]
        exact (nodeAnnounced_insertNodeCanonical_iff cs n k).mpr (Or.inr h)
      · rw [applyGossipNodeCanonical_node_of_rejected verify cs n hg]
        exact h

/-- A signature-valid node key backing is preserved by a canonical gossip
step.  The node branch either keeps the old valid record (different key) or
installs the incoming valid record (same key). -/
theorem nodeAnnouncedValid_applyGossipNodeCanonical (verify : SigVerifier)
    (cs : CanonicalStore) (m : GossipMessage) {k : PubKey}
    (h : NodeAnnouncedValid verify cs.gossip k) :
    NodeAnnouncedValid verify
      (applyGossipNodeCanonical verify cs m).gossip k := by
  cases m with
  | channelAnnouncement a =>
      rw [applyGossipNodeCanonical_announcement]
      simpa [NodeAnnouncedValid,
        applyGossipCanonicalStore_announcement_nodeAnnouncements] using h
  | channelUpdate u =>
      rw [applyGossipNodeCanonical_update]
      simpa [NodeAnnouncedValid,
        applyGossipCanonicalStore_update_nodeAnnouncements] using h
  | nodeAnnouncement n =>
      by_cases hg : n.signatureValid verify ∧
          NodeSupersedes n cs.gossip.nodeAnnouncements
      · rw [applyGossipNodeCanonical_node_of_admitted verify cs n hg]
        rcases h with ⟨m, hm, hk, hvalid⟩
        by_cases hsame : n.nodeId = k
        · exact ⟨n, List.mem_cons_self .., hsame, hg.1⟩
        · have hne : m.nodeId ≠ n.nodeId := by
            intro hmn
            exact hsame (hmn.symm.trans hk)
          exact ⟨m, mem_insertNodeCanonical_of_mem_of_ne hm hne, hk, hvalid⟩
      · rw [applyGossipNodeCanonical_node_of_rejected verify cs n hg]
        exact h

/-- In a `NodeCanonicalAdmitted` store, every backed key has a valid backing
record. -/
theorem nodeAnnouncedValid_of_nodeCanonicalAdmitted {verify : SigVerifier}
    {cs : CanonicalStore} (h : NodeCanonicalAdmitted verify cs) {k : PubKey}
    (hk : NodeAnnounced cs.gossip k) :
    NodeAnnouncedValid verify cs.gossip k := by
  rcases hk with ⟨n, hn, hnk⟩
  exact ⟨n, hn, hnk, h.nodesValid n hn⟩

/-- Reachable node-canonical stores certify every backed key. -/
theorem reachable_nodeAnnouncedValid {verify : SigVerifier}
    {cs : CanonicalStore} (h : ReachableNodeCanonical verify cs) {k : PubKey}
    (hk : NodeAnnounced cs.gossip k) :
    NodeAnnouncedValid verify cs.gossip k :=
  nodeAnnouncedValid_of_nodeCanonicalAdmitted
    (reachableNodeCanonical_invariant h) hk

/-! ## 2. The store-only unlinkability boundary -/

/-- A relation on node keys is *store-only* when it depends only on which keys
the node-announcement list currently backs.  This is the information available
to a channel-backing or graph-membership check that has no external rotation
evidence. -/
def StoreOnly (s : GossipState) (R : PubKey → PubKey → Prop) : Prop :=
  ∀ x y x' y',
    (NodeAnnounced s x ↔ NodeAnnounced s x') →
    (NodeAnnounced s y ↔ NodeAnnounced s y') →
    (R x y ↔ R x' y')

/-- On two co-announced keys, every store-only relation is symmetric.  The
store cannot orient the pair. -/
theorem storeOnly_symm_of_coannounced {s : GossipState}
    {R : PubKey → PubKey → Prop} (hR : StoreOnly s R)
    {a b : PubKey} (ha : NodeAnnounced s a) (hb : NodeAnnounced s b) :
    R a b ↔ R b a := by
  refine hR a b b a ?_ ?_
  · exact ⟨fun _ => hb, fun _ => ha⟩
  · exact ⟨fun _ => ha, fun _ => hb⟩

/-- **No oriented store-only link.**  If `R` is store-only and antisymmetric,
it cannot hold between two distinct co-announced keys.  A rotation direction
therefore cannot be recovered from the node store's backing pattern alone; it
needs an explicit witness. -/
theorem no_oriented_store_only_link {s : GossipState}
    {R : PubKey → PubKey → Prop} (hR : StoreOnly s R)
    (hantisymm : ∀ x y, R x y → R y x → x = y)
    {a b : PubKey} (ha : NodeAnnounced s a) (hb : NodeAnnounced s b)
    (hne : a ≠ b) : ¬ R a b := by
  intro hab
  have hba : R b a := (storeOnly_symm_of_coannounced hR ha hb).mp hab
  exact hne (hantisymm a b hab hba)

/-- **Canonical distinct nodes have no oriented store link.**  Two canonical
node announcements with different wire keys are distinct records, and every
store-only relation between their keys is symmetric; an antisymmetric one is
impossible.  This is the negative boundary: canonicalisation preserves both
records but establishes no identity or succession. -/
theorem canonical_distinct_nodes_no_oriented_store_link
    {s : GossipState} {a b : NodeAnnouncement}
    (hc : CanonicalNodeAnnouncements s.nodeAnnouncements)
    (ha : a ∈ s.nodeAnnouncements) (hb : b ∈ s.nodeAnnouncements)
    (hne : a.nodeId ≠ b.nodeId) :
    a ≠ b ∧
      (∀ x ∈ s.nodeAnnouncements, x.nodeId = a.nodeId → x = a) ∧
      (∀ x ∈ s.nodeAnnouncements, x.nodeId = b.nodeId → x = b) ∧
      (∀ R : PubKey → PubKey → Prop, StoreOnly s R →
        (R a.nodeId b.nodeId ↔ R b.nodeId a.nodeId)) ∧
      (∀ R : PubKey → PubKey → Prop, StoreOnly s R →
        (∀ x y, R x y → R y x → x = y) →
        ¬ R a.nodeId b.nodeId) := by
  have ha' : NodeAnnounced s a.nodeId := ⟨a, ha, rfl⟩
  have hb' : NodeAnnounced s b.nodeId := ⟨b, hb, rfl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h
    exact hne (congrArg NodeAnnouncement.nodeId h)
  · intro x hx hxid
    exact hc x hx a ha hxid
  · intro x hx hxid
    exact hc x hx b hb hxid
  · intro R hR
    exact storeOnly_symm_of_coannounced hR ha' hb'
  · intro R hR hantisymm
    exact no_oriented_store_only_link hR hantisymm ha' hb' hne

/-! ## 3. Rotation witnesses and channel-endpoint rewriting -/

/-- **Explicit rotation/linkage witness.**  The evidence is an opaque input.
Nothing in the gossip store produces, validates, or authenticates it; in
particular this is not a proof that the two keys belong to one physical node.
The `distinct` field records that a rotation is between different wire keys. -/
structure RotationWitness where
  /-- The old wire `node_id`. -/
  oldId : PubKey
  /-- The new wire `node_id`. -/
  newId : PubKey
  /-- Out-of-band evidence.  Its meaning is deliberately not modelled. -/
  evidence : ByteArray
  /-- A rotation relates two different keys. -/
  distinct : oldId ≠ newId

namespace RotationWitness

/-- The witness relates `old` to `new` in that direction. -/
def Links (w : RotationWitness) (old new : PubKey) : Prop :=
  w.oldId = old ∧ w.newId = new

/-- Rewrite the old wire key to the new one; all other keys are unchanged. -/
noncomputable def mapKey (w : RotationWitness) (k : PubKey) : PubKey :=
  if k = w.oldId then w.newId else k

@[simp] theorem mapKey_old (w : RotationWitness) :
    w.mapKey w.oldId = w.newId := by
  simp [mapKey]

theorem mapKey_of_ne (w : RotationWitness) {k : PubKey}
    (h : k ≠ w.oldId) : w.mapKey k = k := by
  simp [mapKey, h]

theorem mapKey_new (w : RotationWitness) :
    w.mapKey w.newId = w.newId := by
  simp [mapKey, w.distinct.symm]

/-- Rewrite a channel announcement's two wire node-key fields.  The channel
identity, graph endpoints, capacity, digest, and signatures are untouched; a
production rotation must re-sign the record. -/
noncomputable def rotateChannel (w : RotationWitness)
    (a : ChannelAnnellation) : ChannelAnnellation :=
  { a with
    nodeKey1 := w.mapKey a.nodeKey1
    nodeKey2 := w.mapKey a.nodeKey2 }

@[simp] theorem rotateChannel_shortChannelId (w : RotationWitness)
    (a : ChannelAnnellation) :
    (w.rotateChannel a).shortChannelId = a.shortChannelId := rfl

@[simp] theorem rotateChannel_node1 (w : RotationWitness)
    (a : ChannelAnnellation) :
    (w.rotateChannel a).node1 = a.node1 := rfl

@[simp] theorem rotateChannel_node2 (w : RotationWitness)
    (a : ChannelAnnellation) :
    (w.rotateChannel a).node2 = a.node2 := rfl

@[simp] theorem rotateChannel_capacitySat (w : RotationWitness)
    (a : ChannelAnnellation) :
    (w.rotateChannel a).capacitySat = a.capacitySat := rfl

@[simp] theorem rotateChannel_nodeKey1 (w : RotationWitness)
    (a : ChannelAnnellation) :
    (w.rotateChannel a).nodeKey1 = w.mapKey a.nodeKey1 := rfl

@[simp] theorem rotateChannel_nodeKey2 (w : RotationWitness)
    (a : ChannelAnnellation) :
    (w.rotateChannel a).nodeKey2 = w.mapKey a.nodeKey2 := rfl

end RotationWitness

/-- **Rotation linkage.**  `RotationLink old new` holds only when an explicit
`RotationWitness` is supplied.  It is not a predicate over the gossip store, so
no store operation can establish it by itself. -/
def RotationLink (old new : PubKey) : Prop :=
  ∃ w : RotationWitness, w.Links old new

/-- Unfolding of `RotationLink`. -/
theorem rotationLink_iff {old new : PubKey} :
    RotationLink old new ↔
      ∃ w : RotationWitness, w.oldId = old ∧ w.newId = new :=
  Iff.rfl

/-! ## 4. Wire membership and its preservation -/

/-- **Wire membership.**  Both BOLT 7 `node_id` fields of a channel
announcement are backed by stored node announcements.  The graph indices
`node1`/`node2` are intentionally not used here; the wire carries the keys. -/
structure WireMember (s : GossipState) (a : ChannelAnnellation) : Prop where
  /-- The first wire node key is announced. -/
  first : NodeAnnounced s a.nodeKey1
  /-- The second wire node key is announced. -/
  second : NodeAnnounced s a.nodeKey2

/-- Wire membership with signature-valid node announcements. -/
structure WireMemberCertified (verify : SigVerifier) (s : GossipState)
    (a : ChannelAnnellation) : Prop where
  /-- The first wire node key has a valid announcement. -/
  first : NodeAnnouncedValid verify s a.nodeKey1
  /-- The second wire node key has a valid announcement. -/
  second : NodeAnnouncedValid verify s a.nodeKey2

/-- Certified wire membership implies wire membership. -/
theorem wireMember_of_certified {verify : SigVerifier} {s : GossipState}
    {a : ChannelAnnellation} (h : WireMemberCertified verify s a) :
    WireMember s a :=
  ⟨nodeAnnounced_of_valid h.first, nodeAnnounced_of_valid h.second⟩

/-- A reachable node-canonical store certifies every wire member. -/
theorem reachable_wireMemberCertified {verify : SigVerifier}
    {cs : CanonicalStore} (h : ReachableNodeCanonical verify cs)
    {a : ChannelAnnellation} (hm : WireMember cs.gossip a) :
    WireMemberCertified verify cs.gossip a :=
  ⟨reachable_nodeAnnouncedValid h hm.first,
    reachable_nodeAnnouncedValid h hm.second⟩

/-- **Wire membership is monotone under the canonical node transition.**  Node
replacement never withdraws a key, and both channel branches leave the node
list untouched.  Hence a channel that is a wire member stays a wire member
under later canonical gossip. -/
theorem wireMember_applyGossipNodeCanonical (verify : SigVerifier)
    (cs : CanonicalStore) (m : GossipMessage) {a : ChannelAnnellation}
    (hm : WireMember cs.gossip a) :
    WireMember (applyGossipNodeCanonical verify cs m).gossip a :=
  ⟨nodeAnnounced_applyGossipNodeCanonical verify cs m hm.first,
    nodeAnnounced_applyGossipNodeCanonical verify cs m hm.second⟩

/-- **Positive linkage under a supplied witness.**  If the new key is backed
and the channel is a wire member before rewriting, then rewriting the old
endpoint key to the new key preserves wire membership.  No store fact
manufactures the witness; this theorem consumes it as an input. -/
theorem rotation_preserves_wireMember (w : RotationWitness) {s : GossipState}
    {a : ChannelAnnellation} (hnew : NodeAnnounced s w.newId)
    (hm : WireMember s a) : WireMember s (w.rotateChannel a) := by
  rcases hm with ⟨h1, h2⟩
  constructor
  · show NodeAnnounced s (w.mapKey a.nodeKey1)
    unfold RotationWitness.mapKey
    split
    · exact hnew
    · exact h1
  · show NodeAnnounced s (w.mapKey a.nodeKey2)
    unfold RotationWitness.mapKey
    split
    · exact hnew
    · exact h2

/-- Certified form of `rotation_preserves_wireMember`: with valid backing for
both old and new keys, the rewritten channel remains a certified wire member.
This is the form consumed by the admission theorem. -/
theorem rotation_preserves_wireMemberCertified (verify : SigVerifier)
    (w : RotationWitness) {s : GossipState} {a : ChannelAnnellation}
    (hnew : NodeAnnouncedValid verify s w.newId)
    (hm : WireMemberCertified verify s a) :
    WireMemberCertified verify s (w.rotateChannel a) := by
  rcases hm with ⟨h1, h2⟩
  constructor
  · show NodeAnnouncedValid verify s (w.mapKey a.nodeKey1)
    unfold RotationWitness.mapKey
    split
    · exact hnew
    · exact h1
  · show NodeAnnouncedValid verify s (w.mapKey a.nodeKey2)
    unfold RotationWitness.mapKey
    split
    · exact hnew
    · exact h2

/-- The witness-driven rewrite preserves the channel identity, both graph
endpoints, and the announced capacity.  Only the two wire node keys move. -/
theorem rotation_preserves_channel_identity (w : RotationWitness)
    (a : ChannelAnnellation) :
    (w.rotateChannel a).shortChannelId = a.shortChannelId ∧
      (w.rotateChannel a).node1 = a.node1 ∧
      (w.rotateChannel a).node2 = a.node2 ∧
      (w.rotateChannel a).capacitySat = a.capacitySat :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ### Graph registration bridge -/

/-- A graph node is backed when its registered wire key has a node
announcement.  This is the graph-`NodeId` counterpart of `NodeAnnounced`; it
depends on the explicit registration map, not on the opaque graph index. -/
def GraphBacked (cs : CanonicalStore) (n : NodeId) : Prop :=
  NodeAnnounced cs.gossip (cs.nodeKeyOf n)

/-- Under `NodeKeyConsistent`, a wire-member channel's graph endpoints are both
backed.  This is the exact bridge from wire keys to graph `NodeId`s; it uses
the existing registration invariant rather than redefining endpoint identity. -/
theorem graphBacked_of_nodeKeyConsistent {cs : CanonicalStore}
    {a : ChannelAnnellation}
    (h : GossipState.NodeKeyConsistent cs.nodeKeyOf cs.gossip)
    (ha : a ∈ cs.gossip.announcements)
    (hm : WireMember cs.gossip a) :
    GraphBacked cs a.node1 ∧ GraphBacked cs a.node2 := by
  rcases h a ha with ⟨h1, h2⟩
  constructor
  · show NodeAnnounced cs.gossip (cs.nodeKeyOf a.node1)
    rw [h1]
    exact hm.first
  · show NodeAnnounced cs.gossip (cs.nodeKeyOf a.node2)
    rw [h2]
    exact hm.second

/-- **Registration-level positive linkage.**  Rotating graph node `n` to key
`k` preserves `GraphBacked` exactly when `k` is backed by a node announcement.
The theorem composes with the existing `rotateNodeKey`; it does not rewrite or
re-sign channel announcements. -/
theorem rotateNodeKey_preserves_graphBacked (cs : CanonicalStore)
    (n : NodeId) (k : PubKey) (hnew : NodeAnnounced cs.gossip k) :
    GraphBacked
      { cs with nodeKeyOf := rotateNodeKey cs.nodeKeyOf n k } n := by
  show NodeAnnounced
    { cs with nodeKeyOf := rotateNodeKey cs.nodeKeyOf n k }.gossip
      ({ cs with nodeKeyOf := rotateNodeKey cs.nodeKeyOf n k }.nodeKeyOf n)
  simpa [rotateNodeKey] using hnew

/-! ## 5. Concrete rotation witnesses -/

private def acceptAll : SigVerifier := fun _ _ _ => true

/-- Byte length 1. -/
private def kA : PubKey := ⟨ByteArray.mk #[1]⟩

/-- Byte length 0. -/
private def kB : PubKey := ⟨ByteArray.empty⟩

/-- A third key, used to show that rotation does not preserve signatures. -/
private def kC : PubKey := ⟨ByteArray.mk #[2, 3]⟩

private def nA : NodeId := ⟨0⟩

private def nB : NodeId := ⟨1⟩

private def sc1 : ShortChannelId := ⟨1, 2, 3⟩

private def emptySig : GossipSignature := ⟨ByteArray.empty⟩

private theorem kA_ne_kB : kA ≠ kB := by
  intro h
  have hs := congrArg (fun k : PubKey => k.bytes.size) h
  have h1 : kA.bytes.size = 1 := by decide
  have h2 : kB.bytes.size = 0 := rfl
  rw [h1, h2] at hs
  exact Nat.noConfusion hs

private theorem kA_ne_kC : kA ≠ kC := by
  intro h
  have hs := congrArg (fun k : PubKey => k.bytes.size) h
  have h1 : kA.bytes.size = 1 := by decide
  have h2 : kC.bytes.size = 2 := by decide
  rw [h1, h2] at hs
  omega

private theorem kB_ne_kC : kB ≠ kC := by
  intro h
  have hs := congrArg (fun k : PubKey => k.bytes.size) h
  have h1 : kB.bytes.size = 0 := rfl
  have h2 : kC.bytes.size = 2 := by decide
  rw [h1, h2] at hs
  omega

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

private def mkNode (k : PubKey) (ts : Nat) (alias : ByteArray) :
    NodeAnnouncement :=
  { nodeId := k
    timestamp := ts
    rgbColor := ByteArray.empty
    alias := alias
    addresses := []
    digest := ByteArray.empty
    signature := emptySig }

private theorem nA_ne_nB : nA ≠ nB := by decide

private def nA1 : NodeAnnouncement := mkNode kA 10 (ByteArray.mk #[1])

private def nA2 : NodeAnnouncement := mkNode kA 20 (ByteArray.mk #[1])

private def nB1 : NodeAnnouncement := mkNode kB 15 (ByteArray.mk #[1])

private theorem nA1_ne_nA2 : nA1 ≠ nA2 := by
  intro h
  have ht := congrArg NodeAnnouncement.timestamp h
  simp [nA1, nA2, mkNode] at ht

private def annA : ChannelAnnellation := mkAnn sc1 nA nB kA kB 1000

/-- The concrete old-to-new rotation witness. -/
private def rotAB : RotationWitness :=
  { oldId := kA
    newId := kB
    evidence := ByteArray.mk #[7]
    distinct := kA_ne_kB }

/-- The reversed witness, showing that orientation is not store data. -/
private def rotBA : RotationWitness :=
  { oldId := kB
    newId := kA
    evidence := ByteArray.mk #[8]
    distinct := kA_ne_kB.symm }

/-- A witness from the first key to the third key, used for the
signature-preservation counterexample. -/
private def rotAC : RotationWitness :=
  { oldId := kA
    newId := kC
    evidence := ByteArray.mk #[9]
    distinct := kA_ne_kC }

private theorem node_valid (n : NodeAnnouncement) :
    n.signatureValid acceptAll := by
  simp [NodeAnnouncement.signatureValid, signatureValid, acceptAll]

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

private theorem ns1_ann : ns1.gossip.announcements = [] := by
  rw [ns1, applyGossipNodeCanonical_node_of_admitted acceptAll ns0 nA1 gateNA1]
  simp [ns0]

private theorem ns1_upd : ns1.gossip.updates = [] := by
  rw [ns1, applyGossipNodeCanonical_node_of_admitted acceptAll ns0 nA1 gateNA1]
  simp [ns0]

private theorem ns1_reachable : ReachableNodeCanonical acceptAll ns1 := by
  unfold ns1
  exact ReachableNodeCanonical.step
    (ReachableNodeCanonical.empty (fun _ => kB))

private theorem gateNA2 : nA2.signatureValid acceptAll ∧
    NodeSupersedes nA2 ns1.gossip.nodeAnnouncements := by
  refine ⟨node_valid nA2, ?_⟩
  rw [ns1_nodes]
  intro m hm hk
  simp only [List.mem_singleton] at hm
  subst m
  simp [nA1, nA2, mkNode]

private noncomputable def ns2 : CanonicalStore :=
  applyGossipNodeCanonical acceptAll ns1 (.nodeAnnouncement nA2)

private theorem ns2_nodes : ns2.gossip.nodeAnnouncements = [nA2] := by
  rw [ns2, applyGossipNodeCanonical_node_of_admitted acceptAll ns1 nA2 gateNA2]
  rw [ns1_nodes]
  simp [insertNodeCanonical, nA1, nA2, mkNode]

private theorem nB1_supersedes_nA1 : NodeSupersedes nB1 [nA1] := by
  intro m hm hk
  simp only [List.mem_singleton] at hm
  subst m
  have hk' : kA = kB := by simpa [nA1, nB1, mkNode] using hk
  exact absurd hk' kA_ne_kB

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

private theorem kA_announced_nsRot : NodeAnnounced nsRot.gossip kA := by
  show ∃ n ∈ nsRot.gossip.nodeAnnouncements, n.nodeId = kA
  rw [nsRot_nodes]
  exact ⟨nA1, by simp, rfl⟩

private theorem kB_announced_nsRot : NodeAnnounced nsRot.gossip kB := by
  show ∃ n ∈ nsRot.gossip.nodeAnnouncements, n.nodeId = kB
  rw [nsRot_nodes]
  exact ⟨nB1, by simp, rfl⟩

private theorem kA_announced_ns1 : NodeAnnounced ns1.gossip kA := by
  show ∃ n ∈ ns1.gossip.nodeAnnouncements, n.nodeId = kA
  rw [ns1_nodes]
  exact ⟨nA1, by simp, rfl⟩

private theorem kB_not_announced_ns1 : ¬ NodeAnnounced ns1.gossip kB := by
  rintro ⟨n, hn, hk⟩
  rw [ns1_nodes] at hn
  simp only [List.mem_singleton] at hn
  subst n
  have hk' : kA = kB := by simpa [nA1, mkNode] using hk
  exact kA_ne_kB hk'

/-- **Concrete unlinkability.**  Both keys are announced in a reachable
canonical store, yet the intended orientation `kA → kB` is not a store-only
relation: the symmetric store-only shape cannot distinguish it from
`kB → kA`. -/
theorem concrete_intended_rotation_not_storeOnly :
    CanonicalNodeAnnouncements nsRot.gossip.nodeAnnouncements ∧
      NodeAnnounced nsRot.gossip kA ∧
      NodeAnnounced nsRot.gossip kB ∧
      ¬ StoreOnly nsRot.gossip (fun a b => a = kA ∧ b = kB) := by
  refine ⟨reachableNodeCanonical_nodesCanonical nsRot_reachable,
    kA_announced_nsRot, kB_announced_nsRot, ?_⟩
  intro hR
  have hs := (hR kA kB kB kA ?_ ?_).mp ⟨rfl, rfl⟩
  · exact kA_ne_kB hs.2
  · exact ⟨fun _ => kB_announced_nsRot, fun _ => kA_announced_nsRot⟩
  · exact ⟨fun _ => kA_announced_nsRot, fun _ => kB_announced_nsRot⟩

/-- The same reachable store supports both directions of an explicit witness;
the store alone selects neither. -/
theorem concrete_both_rotation_witnesses :
    (∃ w : RotationWitness, w.Links kA kB) ∧
      (∃ w : RotationWitness, w.Links kB kA) :=
  ⟨⟨rotAB, rfl, rfl⟩, ⟨rotBA, rfl, rfl⟩⟩

/-- The same reachable store supports both `RotationLink` directions.  This is
the positive counterpart of the store-only negative: linkage exists, but only
because a witness was supplied in each direction. -/
theorem concrete_rotationLink_both_directions :
    RotationLink kA kB ∧ RotationLink kB kA :=
  ⟨⟨rotAB, rfl, rfl⟩, ⟨rotBA, rfl, rfl⟩⟩

/-- **Same store, two rotation worlds.**  One reachable canonical store is
compatible with both orientations of the external witness.  Since the store is
literally the same object, no function of the store can distinguish the two
worlds. -/
theorem concrete_same_store_both_orientations :
    CanonicalNodeAnnouncements nsRot.gossip.nodeAnnouncements ∧
      NodeAnnounced nsRot.gossip kA ∧
        NodeAnnounced nsRot.gossip kB ∧
          (∃ w : RotationWitness, w.Links kA kB) ∧
            (∃ w : RotationWitness, w.Links kB kA) :=
  ⟨reachableNodeCanonical_nodesCanonical nsRot_reachable,
    kA_announced_nsRot, kB_announced_nsRot,
    ⟨rotAB, rfl, rfl⟩, ⟨rotBA, rfl, rfl⟩⟩

/-- **No store function selects both rotation worlds.**  A selector is any
function of the gossip store returning a key pair.  It cannot return both the
`kA → kB` and the `kB → kA` orientation on the same store.  This is the
non-identifiability form of the unlinkability boundary: the direction is not a
store fact at all. -/
theorem no_store_function_selects_both_rotation_worlds
    (s : GossipState) (f : GossipState → PubKey × PubKey)
    (w₁ w₂ : RotationWitness)
    (h₁ : f s = (w₁.oldId, w₁.newId))
    (h₂ : f s = (w₂.oldId, w₂.newId))
    (hne : w₁.oldId ≠ w₂.oldId) : False := by
  rw [h₁] at h₂
  have hfst : w₁.oldId = w₂.oldId := by
    simpa using congrArg Prod.fst h₂
  exact hne hfst

/-- Rotation keeps the old record: a different-key successor is a separate
canonical slot, so the old announcement remains stored. -/
theorem concrete_rotation_keeps_old_record :
    nA1 ∈ nsRot.gossip.nodeAnnouncements ∧
      nB1 ∈ nsRot.gossip.nodeAnnouncements := by
  rw [nsRot_nodes]
  exact ⟨by simp, by simp⟩

/-- Same-key supersession removes the old record.  Together with
`concrete_rotation_keeps_old_record` this makes the "old announcements may
remain until superseded" boundary precise. -/
theorem concrete_supersession_removes_old_record :
    nA1 ∉ ns2.gossip.nodeAnnouncements ∧
      nA2 ∈ ns2.gossip.nodeAnnouncements := by
  rw [ns2_nodes]
  exact ⟨by simp [nA1_ne_nA2], by simp⟩

/-- The concrete positive linkage: mapping the old key to the new key under
the supplied witness preserves wire membership of `annA`. -/
theorem concrete_rotation_preserves_wireMember :
    WireMember nsRot.gossip (rotAB.rotateChannel annA) :=
  rotation_preserves_wireMember rotAB kB_announced_nsRot
    ⟨kA_announced_nsRot, kB_announced_nsRot⟩

/-! ## 6. Rotation does not preserve signatures -/

/-- A verifier that accepts every key except `kC`. -/
private noncomputable def verifyNotC : SigVerifier :=
  fun k _ _ => decide (k ≠ kC)

private theorem verifyNotC_kA (d : ByteArray) (s : GossipSignature) :
    verifyNotC kA d s = true := by
  simp [verifyNotC, kA_ne_kC]

private theorem verifyNotC_kB (d : ByteArray) (s : GossipSignature) :
    verifyNotC kB d s = true := by
  simp [verifyNotC, kB_ne_kC]

/-- `annA` verifies under the key-sensitive verifier before rotation. -/
private theorem annA_signaturesValid_verifyNotC :
    annA.signaturesValid verifyNotC := by
  simp [ChannelAnnellation.signaturesValid, signatureValid, annA, mkAnn,
    verifyNotC, kA_ne_kC, kB_ne_kC]

/-- **Signatures are not preserved by rotation.**  Rewriting `kA` to `kC`
leaves `nodeSignature1` and the digest in place, but the signature is now
checked against `kC`, which this verifier rejects.  Membership is a
key-level relation; admission needs a fresh signature. -/
theorem rotation_breaks_signatures :
    ¬ (rotAC.rotateChannel annA).signaturesValid verifyNotC := by
  intro h
  have h1 := h.1
  have hk : (rotAC.rotateChannel annA).nodeKey1 = kC := by
    simp [rotAC, RotationWitness.rotateChannel, RotationWitness.mapKey,
      annA, mkAnn]
  rw [hk] at h1
  simp [signatureValid, verifyNotC] at h1

/-- **Signature validity is not a rotation invariant.**  There is a concrete
verifier, witness, and channel announcement that is signature-valid before the
rewrite and invalid after it.  Wire membership and channel identity are
preserved, but a production rotation must re-sign the rewritten record. -/
theorem rotation_not_signature_preserving :
    ∃ (verify : SigVerifier) (w : RotationWitness)
      (a : ChannelAnnellation),
      a.signaturesValid verify ∧ ¬ (w.rotateChannel a).signaturesValid verify :=
  ⟨verifyNotC, rotAC, annA, annA_signaturesValid_verifyNotC,
    rotation_breaks_signatures⟩

/-! ## 7. Wire-level admission and the missing-endpoint counterexample -/

/-- **Admission with certified wire membership.**  Under the node-canonical
invariant, a channel announcement that (a) passes the existing canonical
channel gates and (b) has both wire keys certified by stored node
announcements is admitted, stays a wire member, and preserves the invariant.

The membership hypothesis is *additive*: the existing transition does not
consume it.  The theorem shows the combined gate is consistent and
invariant-preserving; it does not claim the core transition enforces it. -/
theorem channelAnnouncement_admitted_of_wireMember (verify : SigVerifier)
    (cs : CanonicalStore) (a : ChannelAnnellation)
    (hinv : NodeCanonicalAdmitted verify cs)
    (hmem : WireMemberCertified verify cs.gossip a)
    (hgate : a.signaturesValid verify ∧ a.node1 ≠ a.node2 ∧
      cs.gossip.CompatibleWithStore a ∧ UpdatesAuthorizedBy cs.gossip a) :
    NodeCanonicalAdmitted verify
        (applyGossipNodeCanonical verify cs (.channelAnnouncement a)) ∧
      a ∈ (applyGossipNodeCanonical verify cs
        (.channelAnnouncement a)).gossip.announcements ∧
      WireMemberCertified verify
        (applyGossipNodeCanonical verify cs
          (.channelAnnouncement a)).gossip a := by
  refine ⟨nodeCanonicalAdmitted_applyGossipNodeCanonical verify cs
      (.channelAnnouncement a) hinv, ?_, ?_⟩
  · rw [applyGossipNodeCanonical_announcement,
      applyGossipCanonicalStore_announcement_of_admitted verify cs a hgate]
    exact mem_insertReplacing_iff.mpr (Or.inl rfl)
  · rcases hmem with ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · simpa [NodeAnnouncedValid, applyGossipNodeCanonical_announcement,
        applyGossipCanonicalStore_announcement_nodeAnnouncements] using h1
    · simpa [NodeAnnouncedValid, applyGossipNodeCanonical_announcement,
        applyGossipCanonicalStore_announcement_nodeAnnouncements] using h2

/-- The concrete channel announcement passes the existing canonical gates on
the empty store. -/
private theorem gateAnnA_ns0 :
    annA.signaturesValid acceptAll ∧ annA.node1 ≠ annA.node2 ∧
      ns0.gossip.CompatibleWithStore annA ∧
        UpdatesAuthorizedBy ns0.gossip annA := by
  simp [ChannelAnnellation.signaturesValid, signatureValid, acceptAll, annA,
    mkAnn, GossipState.CompatibleWithStore, UpdatesAuthorizedBy, nA_ne_nB, ns0]

/-- The same announcement passes the gates on `ns1`, where only `kA` is
backed. -/
private theorem gateAnnA_ns1 :
    annA.signaturesValid acceptAll ∧ annA.node1 ≠ annA.node2 ∧
      ns1.gossip.CompatibleWithStore annA ∧
        UpdatesAuthorizedBy ns1.gossip annA := by
  simp [ChannelAnnellation.signaturesValid, signatureValid, acceptAll, annA,
    mkAnn, GossipState.CompatibleWithStore, UpdatesAuthorizedBy, nA_ne_nB,
    ns1_ann, ns1_upd]

private theorem nsRot_ann : nsRot.gossip.announcements = [] := by
  rw [nsRot, applyGossipNodeCanonical_node_of_admitted acceptAll ns1 nB1 gateNB1]
  exact ns1_ann

private theorem nsRot_upd : nsRot.gossip.updates = [] := by
  rw [nsRot, applyGossipNodeCanonical_node_of_admitted acceptAll ns1 nB1 gateNB1]
  exact ns1_upd

/-- On `nsRot` both wire keys are backed, so `annA` passes the combined gate. -/
private theorem gateAnnA_nsRot :
    annA.signaturesValid acceptAll ∧ annA.node1 ≠ annA.node2 ∧
      nsRot.gossip.CompatibleWithStore annA ∧
        UpdatesAuthorizedBy nsRot.gossip annA := by
  simp [ChannelAnnellation.signaturesValid, signatureValid, acceptAll, annA,
    mkAnn, GossipState.CompatibleWithStore, UpdatesAuthorizedBy, nA_ne_nB,
    nsRot_ann, nsRot_upd]

private theorem wireMemberCertified_annA_nsRot :
    WireMemberCertified acceptAll nsRot.gossip annA :=
  ⟨reachable_nodeAnnouncedValid nsRot_reachable kA_announced_nsRot,
    reachable_nodeAnnouncedValid nsRot_reachable kB_announced_nsRot⟩

/-- **Concrete positive admission.**  A reachable node-canonical store that
backs both wire keys admits `annA`, keeps it as a certified wire member, and
preserves the node invariant.  This is a non-vacuous instance of
`channelAnnouncement_admitted_of_wireMember`. -/
theorem concrete_admission_with_wireMember :
    NodeCanonicalAdmitted acceptAll
        (applyGossipNodeCanonical acceptAll nsRot
          (.channelAnnouncement annA)) ∧
      annA ∈ (applyGossipNodeCanonical acceptAll nsRot
        (.channelAnnouncement annA)).gossip.announcements ∧
      WireMemberCertified acceptAll
        (applyGossipNodeCanonical acceptAll nsRot
          (.channelAnnouncement annA)).gossip annA :=
  channelAnnouncement_admitted_of_wireMember acceptAll nsRot annA
    (reachableNodeCanonical_invariant nsRot_reachable)
    wireMemberCertified_annA_nsRot gateAnnA_nsRot

/-- **Missing-endpoint counterexample.**  `ns1` backs only `kA`; `annA` names
`kA` and `kB`.  The second endpoint is missing, `annA` is not a wire member,
yet the existing canonical transition admits it.  Thus
`NodeCanonicalAdmitted` does not imply wire membership, and wire membership is
an additive check rather than a theorem of the core transition. -/
theorem missing_endpoint_channel_admitted :
    ∃ (verify : SigVerifier) (cs : CanonicalStore)
      (a : ChannelAnnellation),
      NodeCanonicalAdmitted verify cs ∧
        NodeAnnounced cs.gossip a.nodeKey1 ∧
          ¬ NodeAnnounced cs.gossip a.nodeKey2 ∧
            ¬ WireMember cs.gossip a ∧
              a ∈ (applyGossipNodeCanonical verify cs
                (.channelAnnouncement a)).gossip.announcements := by
  refine ⟨acceptAll, ns1, annA,
    reachableNodeCanonical_invariant ns1_reachable, ?_, ?_, ?_, ?_⟩
  · exact kA_announced_ns1
  · exact kB_not_announced_ns1
  · intro hm
    exact kB_not_announced_ns1 hm.second
  · rw [applyGossipNodeCanonical_announcement,
      applyGossipCanonicalStore_announcement_of_admitted acceptAll ns1 annA
        gateAnnA_ns1]
    exact mem_insertReplacing_iff.mpr (Or.inl rfl)

/-- A node-canonical store can satisfy the invariant without any wire
membership: the empty store is node-canonical but backs no channel
endpoints. -/
theorem nodeCanonicalAdmitted_not_wireMember :
    ∃ (verify : SigVerifier) (cs : CanonicalStore)
      (a : ChannelAnnellation),
      NodeCanonicalAdmitted verify cs ∧ ¬ WireMember cs.gossip a := by
  refine ⟨acceptAll, ns0, annA,
    reachableNodeCanonical_invariant
      (ReachableNodeCanonical.empty (fun _ => kB)), ?_⟩
  intro hm
  rcases hm.first with ⟨n, hn, _⟩
  simp [ns0] at hn

/-- The empty-store admission is a special case of the missing-endpoint
counterexample; it records the exact negative for `NodeCanonicalAdmitted`. -/
theorem empty_store_admits_unbacked_channel :
    annA ∈ (applyGossipNodeCanonical acceptAll ns0
      (.channelAnnouncement annA)).gossip.announcements := by
  rw [applyGossipNodeCanonical_announcement,
    applyGossipCanonicalStore_announcement_of_admitted acceptAll ns0 annA
      gateAnnA_ns0]
  exact mem_insertReplacing_iff.mpr (Or.inl rfl)

/-! ## 8. Linkage itself is not a store relation -/

/-- `RotationLink` is irreflexive: a witness always relates two distinct keys. -/
theorem rotationLink_irrefl (k : PubKey) : ¬ RotationLink k k := by
  rintro ⟨w, h1, h2⟩
  exact w.distinct (h1.trans h2.symm)

/-- **The linkage relation is not store-only.**  On the reachable store
`nsRot`, `RotationLink kA kB` holds but `RotationLink kA kA` does not, while
both `kA` and `kA` have the same backing status.  Hence no `StoreOnly`
relation can be the actual linkage relation.  This is the strongest form of
the negative: the witness is not merely hard to select from the store, it is
not the kind of object the store's backing pattern determines. -/
theorem concrete_rotationLink_not_storeOnly :
    ¬ StoreOnly nsRot.gossip (fun a b => RotationLink a b) := by
  intro hR
  have hiff := hR kA kB kA kA Iff.rfl
    (show (NodeAnnounced nsRot.gossip kB ↔
        NodeAnnounced nsRot.gossip kA) from
      ⟨fun _ => kA_announced_nsRot, fun _ => kB_announced_nsRot⟩)
  have htrue : RotationLink kA kB := ⟨rotAB, rfl, rfl⟩
  exact rotationLink_irrefl kA (hiff.mp htrue)

end LnLean.Proofs.Routing.NodeIdentityTargets
