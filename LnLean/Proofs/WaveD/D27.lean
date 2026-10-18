/-
# D27 — The gossip graph contains only channels with valid announcement
signatures

**Catalog claim.** `LN-RT-006`: the gossip graph contains only channels with
valid announcement signatures (BOLT 7 §The `channel_announcement` Message).

The wave-A model does **not** enforce this claim by construction:

* `GossipState.applyGossip` appends every `channel_announcement` to
  `announcements` without consulting any signature predicate.
* `Graph` is a bare list of `ChannelEdge`s and `ChannelEdge` carries no
  signature or announcement reference at all.
* `GossipNetwork.views` and `GossipState.announcements` are independent
  fields; nothing links a routing edge to the announcement that authorises
  it.

The faithful unconditional statement is therefore *false* in the raw model
(`waveD_d27_raw_applyGossip_admits_invalid`,
`waveD_d27_network_invariant_not_free` below are mechanised
counterexamples).  This module proves the strongest true forms:

1. `waveD_d27_applyGossipChecked_preserves`: the signature-gated store
   transition `applyGossipChecked` preserves the invariant "every stored
   announcement verifies under all four BOLT 7 signatures", for every
   message.
2. `waveD_d27_announcementGraph_only_valid`: the graph materialised from an
   announcement list contains only edges whose originating announcement is
   in the list and passes `signaturesValid`.
3. `waveD_d27_gossip_graph_only_valid_channels`: if the routing views are
   backed by stored announcements and the store invariant holds, then after
   any checked gossip message every edge of the network graph has a valid
   backing announcement.

The added hypothesis of (3) is `NetworkChannelsValid`: every view's
`(scid, node1, node2, capacity)` is copied from a stored announcement whose
four signatures verify.  Wave A has no field or constructor enforcing this
link, which is exactly the missing model invariant recorded in the report.

BOLT 7 requires the receiver to verify all four signatures of a
`channel_announcement` before processing it (`refs/bolts/07-routing-gossip.md`,
"the `channel_announcement` Message").  As in `LnLean.Routing.Gossip`, the
verifier is an abstract parameter: unforgeability is assumption C3/C4/C8 and
is never claimed here.

No `sorry`.
-/

import LnLean.Routing.Gossip
import LnLean.Routing.Graph
import LnLean.Routing.Laws
import LnLean.Routing.Onion
import LnLean.Routing.Route
import LnLean.Proofs.Routing.GossipProps

namespace LnLean.Proofs.WaveD.D27

set_option autoImplicit false

open LnLean.Routing
open LnLean.Routing.GossipProps

-- OBLIGATION: LN-WD-D27

/-! ## Announcement validity -/

/-- An announcement is valid when all four BOLT 7 signatures verify.  This is
a transparent alias for `ChannelAnnellation.signaturesValid`, named so that
the catalog claim can be stated directly. -/
def announcementValid (verify : SigVerifier) (a : ChannelAnnellation) : Prop :=
  a.signaturesValid verify

theorem waveD_d27_announcementValid_iff {verify : SigVerifier}
    {a : ChannelAnnellation} :
    announcementValid verify a ↔ a.signaturesValid verify :=
  Iff.rfl

/-- The store invariant behind the claim: every channel announcement held by
the gossip store has valid BOLT 7 signatures. -/
def AnnouncementsValid (verify : SigVerifier) (s : GossipState) : Prop :=
  ∀ a ∈ s.announcements, a.signaturesValid verify

/-- The empty store satisfies the invariant vacuously. -/
theorem waveD_d27_announcementsValid_empty (verify : SigVerifier) :
    AnnouncementsValid verify (⟨[], [], []⟩ : GossipState) := by
  intro a ha
  simp at ha

/-! ## The signature-gated store preserves the invariant -/

/-- A verifying `channel_announcement` is prepended to the announcement
list. -/
theorem waveD_d27_checked_channelAnnouncement_announcements
    (verify : SigVerifier) (s : GossipState) (a : ChannelAnnellation)
    (hsig : a.signaturesValid verify) :
    (applyGossipChecked verify s (.channelAnnouncement a)).announcements =
      a :: s.announcements := by
  simp [applyGossipChecked, applyGossip, hsig]

/-- A non-verifying `channel_announcement` leaves the announcement list
untouched. -/
theorem waveD_d27_checked_channelAnnouncement_announcements_invalid
    (verify : SigVerifier) (s : GossipState) (a : ChannelAnnellation)
    (hsig : ¬ a.signaturesValid verify) :
    (applyGossipChecked verify s (.channelAnnouncement a)).announcements =
      s.announcements := by
  simp [applyGossipChecked, hsig]

/-- A `channel_update` never changes the announcement list. -/
theorem waveD_d27_checked_channelUpdate_announcements
    (verify : SigVerifier) (s : GossipState) (u : ChannelUpdate) :
    (applyGossipChecked verify s (.channelUpdate u)).announcements =
      s.announcements := by
  simp only [applyGossipChecked, acceptChannelUpdate]
  split
  · exact applyUpdate_announcements s u
  · rfl

/-- A `node_announcement` never changes the announcement list. -/
theorem waveD_d27_checked_nodeAnnouncement_announcements
    (verify : SigVerifier) (s : GossipState) (n : NodeAnnouncement) :
    (applyGossipChecked verify s (.nodeAnnouncement n)).announcements =
      s.announcements := by
  simp only [applyGossipChecked]
  split <;> rfl

/-- **Checked gossip preserves announcement validity.**  Starting from a
store whose announcements all verify, every message accepted by the
signature-gated transition leaves the invariant intact. -/
theorem waveD_d27_applyGossipChecked_preserves (verify : SigVerifier)
    (s : GossipState) (m : GossipMessage)
    (h : AnnouncementsValid verify s) :
    AnnouncementsValid verify (applyGossipChecked verify s m) := by
  classical
  intro a ha
  cases m with
  | channelAnnouncement a0 =>
      by_cases hsig : a0.signaturesValid verify
      · rw [waveD_d27_checked_channelAnnouncement_announcements verify s a0 hsig]
          at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hsig
        · exact h a ha
      · rw [waveD_d27_checked_channelAnnouncement_announcements_invalid
          verify s a0 hsig] at ha
        exact h a ha
  | channelUpdate u =>
      rw [waveD_d27_checked_channelUpdate_announcements] at ha
      exact h a ha
  | nodeAnnouncement n =>
      rw [waveD_d27_checked_nodeAnnouncement_announcements] at ha
      exact h a ha

/-- The checked transition never forgets an announcement that was already
stored. -/
theorem waveD_d27_checked_announcement_mem (verify : SigVerifier)
    (s : GossipState) (m : GossipMessage) {a : ChannelAnnellation}
    (h : a ∈ s.announcements) :
    a ∈ (applyGossipChecked verify s m).announcements := by
  classical
  cases m with
  | channelAnnouncement a0 =>
      by_cases hsig : a0.signaturesValid verify
      · rw [waveD_d27_checked_channelAnnouncement_announcements verify s a0 hsig]
        exact List.mem_cons_of_mem _ h
      · rw [waveD_d27_checked_channelAnnouncement_announcements_invalid
          verify s a0 hsig]
        exact h
  | channelUpdate u =>
      rw [waveD_d27_checked_channelUpdate_announcements]
      exact h
  | nodeAnnouncement n =>
      rw [waveD_d27_checked_nodeAnnouncement_announcements]
      exact h

/-- The raw wave-A transition stores a valid announcement and preserves the
invariant, but this needs the validity of the *new* announcement as a
hypothesis: `applyGossip` itself does not check signatures. -/
theorem waveD_d27_applyGossip_preserves_of_valid (verify : SigVerifier)
    (s : GossipState) {a : ChannelAnnellation}
    (h : AnnouncementsValid verify s) (hsig : a.signaturesValid verify) :
    AnnouncementsValid verify (applyGossip s (.channelAnnouncement a)) := by
  intro b hb
  simp only [applyGossip, List.mem_cons] at hb
  rcases hb with rfl | hb
  · exact hsig
  · exact h b hb

/-! ## Graph materialisation from checked announcements -/

/-- The edges authorised by a list of announcements.  An announcement
contributes an edge only when `bindChannel` succeeds, which by
`bindChannel_requires_signature` means all four signatures verify. -/
noncomputable def announcementEdges (verify : SigVerifier)
    (l : List ChannelAnnellation) : List ChannelEdge :=
  l.filterMap fun a => (bindChannel verify a).map ChannelBinding.edge

/-- The graph materialised from a list of announcements, with unverified
announcements silently dropped. -/
noncomputable def announcementGraph (verify : SigVerifier)
    (l : List ChannelAnnellation) : Graph :=
  { edges := announcementEdges verify l
    nodes := (announcementEdges verify l).flatMap fun e => [e.node1, e.node2] }

/-- A successful bind copies the announced capacity.  `bindChannel_binds`
records the channel id and endpoints; capacity is needed separately for the
backing relation. -/
theorem waveD_d27_bindChannel_capacity {verify : SigVerifier}
    {a : ChannelAnnellation} {b : ChannelBinding}
    (h : bindChannel verify a = some b) : b.capacitySat = a.capacitySat := by
  unfold bindChannel at h
  split at h
  · cases h
    rfl
  · simp at h

/-- **Every materialised edge comes from a verifying announcement.**  The
witness is an announcement that really is in the list, passes the four
signature checks, and agrees with the edge on channel id, endpoints, and
capacity. -/
theorem waveD_d27_mem_announcementEdges {verify : SigVerifier}
    {l : List ChannelAnnellation} {e : ChannelEdge}
    (h : e ∈ announcementEdges verify l) :
    ∃ a ∈ l, a.signaturesValid verify ∧
      e.shortChannelId = a.shortChannelId ∧ e.node1 = a.node1 ∧
      e.node2 = a.node2 ∧ e.capacitySat = a.capacitySat := by
  unfold announcementEdges at h
  rcases List.mem_filterMap.mp h with ⟨a, ha, hmap⟩
  cases hbind : bindChannel verify a with
  | none => simp [hbind] at hmap
  | some b =>
      simp only [hbind, Option.map_some, Option.some.injEq] at hmap
      subst hmap
      have hb := bindChannel_binds hbind
      exact ⟨a, ha, bindChannel_requires_signature hbind,
        hb.1, hb.2.1, hb.2.2, waveD_d27_bindChannel_capacity hbind⟩

/-- **The announcement graph contains only valid channels.**  Every edge of
`announcementGraph verify l` is backed by an announcement in `l` whose four
BOLT 7 signatures verify. -/
theorem waveD_d27_announcementGraph_only_valid {verify : SigVerifier}
    {l : List ChannelAnnellation} {e : ChannelEdge}
    (h : e ∈ (announcementGraph verify l).edges) :
    ∃ a ∈ l, announcementValid verify a ∧
      e.shortChannelId = a.shortChannelId := by
  rcases waveD_d27_mem_announcementEdges h with
    ⟨a, ha, hsig, hscid, _⟩
  exact ⟨a, ha, hsig, hscid⟩

/-- The materialised graph is well formed whenever the valid announcements
have distinct endpoints and structurally valid `short_channel_id`s. -/
theorem waveD_d27_announcementGraph_wellFormed {verify : SigVerifier}
    {l : List ChannelAnnellation}
    (hne : ∀ a ∈ l, a.signaturesValid verify → a.node1 ≠ a.node2)
    (hscid : ∀ a ∈ l, a.signaturesValid verify → a.shortChannelId.Valid) :
    graphWellFormed (announcementGraph verify l) := by
  intro e he
  rcases waveD_d27_mem_announcementEdges he with
    ⟨a, ha, hsig, hscidEq, h1, h2, _⟩
  constructor
  · rw [h1, h2]
    exact hne a ha hsig
  · rw [hscidEq]
    exact hscid a ha hsig

/-! ## The network graph and its backing announcements -/

/-- **The missing link between routing views and gossip announcements.**
Every routing view is backed by a stored announcement whose four signatures
verify, and the view copies that announcement's channel identity and
capacity.  Wave A does not construct views this way and has no field forcing
the relation; it is the essential added hypothesis of this module. -/
def NetworkChannelsValid (verify : SigVerifier) (ns : GossipNetwork) : Prop :=
  ∀ v ∈ ns.views, ∃ a ∈ ns.gossip.announcements,
    a.signaturesValid verify ∧ v.scid = a.shortChannelId ∧
      v.node1 = a.node1 ∧ v.node2 = a.node2 ∧ v.capacitySat = a.capacitySat

/-- Checked gossip preserves the view-to-announcement backing relation.  The
proof uses only `applyGossipChecked`'s announcement gating and the fact that
a `channel_update` cannot change a view's channel identity. -/
theorem waveD_d27_applyMessage_preserves_network (verify : SigVerifier)
    (ns : GossipNetwork) (m : GossipMessage)
    (hviews : NetworkChannelsValid verify ns) :
    NetworkChannelsValid verify (ns.applyMessage verify m) := by
  classical
  intro v hv
  cases m with
  | channelAnnouncement a0 =>
      simp only [GossipNetwork.applyMessage] at hv
      obtain ⟨a, ha, hsig, hscid, h1, h2, hcap⟩ := hviews v hv
      exact ⟨a, waveD_d27_checked_announcement_mem verify ns.gossip
        (.channelAnnouncement a0) ha, hsig, hscid, h1, h2, hcap⟩
  | nodeAnnouncement n =>
      simp only [GossipNetwork.applyMessage] at hv
      obtain ⟨a, ha, hsig, hscid, h1, h2, hcap⟩ := hviews v hv
      exact ⟨a, waveD_d27_checked_announcement_mem verify ns.gossip
        (.nodeAnnouncement n) ha, hsig, hscid, h1, h2, hcap⟩
  | channelUpdate u =>
      simp only [GossipNetwork.applyMessage] at hv
      by_cases hsig : u.signatureValid verify
      · rw [ite_eq_left hsig] at hv
        rcases List.mem_map.mp hv with ⟨w, hw, rfl⟩
        obtain ⟨a, ha, hasig, hscid, h1, h2, hcap⟩ := hviews w hw
        have hmem : a ∈
            (ns.applyMessage verify (.channelUpdate u)).gossip.announcements := by
          rw [GossipNetwork.applyMessage_gossip]
          exact waveD_d27_checked_announcement_mem verify ns.gossip
            (.channelUpdate u) ha
        exact ⟨a, hmem, hasig,
          by rw [ChannelView.applyUpdate_scid]; exact hscid,
          by rw [ChannelView.applyUpdate_node1]; exact h1,
          by rw [ChannelView.applyUpdate_node2]; exact h2,
          by rw [ChannelView.applyUpdate_capacitySat]; exact hcap⟩
      · rw [ite_eq_right hsig] at hv
        obtain ⟨a, ha, hasig, hscid, h1, h2, hcap⟩ := hviews v hv
        have hmem : a ∈
            (ns.applyMessage verify (.channelUpdate u)).gossip.announcements := by
          rw [GossipNetwork.applyMessage_gossip]
          exact waveD_d27_checked_announcement_mem verify ns.gossip
            (.channelUpdate u) ha
        exact ⟨a, hmem, hasig, hscid, h1, h2, hcap⟩

/-- **Every edge of the network graph is backed by a valid announcement.**
This is the graph-level form of `LN-RT-006`. -/
theorem waveD_d27_graph_edges_only_valid (verify : SigVerifier)
    (ns : GossipNetwork) (hviews : NetworkChannelsValid verify ns) :
    ∀ e ∈ ns.graph.edges, ∃ a ∈ ns.gossip.announcements,
      a.signaturesValid verify ∧ e.shortChannelId = a.shortChannelId ∧
        e.node1 = a.node1 ∧ e.node2 = a.node2 := by
  intro e he
  have he' : e ∈ ns.views.map ChannelView.edge := he
  rcases List.mem_map.mp he' with ⟨v, hv, rfl⟩
  obtain ⟨a, ha, hsig, hscid, h1, h2, _⟩ := hviews v hv
  exact ⟨a, ha, hsig, hscid, h1, h2⟩

/-- **The gossip graph contains only channels with valid announcement
signatures** (catalog `LN-RT-006`), stated over reachable checked states.

Starting from a view set backed by four-signature-verified stored
announcements, any signature-gated gossip message yields a graph in which
every edge has a stored, verified backing announcement with the same
channel id. -/
theorem waveD_d27_gossip_graph_only_valid_channels (verify : SigVerifier)
    (ns : GossipNetwork) (m : GossipMessage)
    (hviews : NetworkChannelsValid verify ns) :
    ∀ e ∈ (ns.applyMessage verify m).graph.edges,
      ∃ a ∈ (ns.applyMessage verify m).gossip.announcements,
        a.signaturesValid verify ∧ e.shortChannelId = a.shortChannelId := by
  intro e he
  rcases waveD_d27_graph_edges_only_valid verify _
      (waveD_d27_applyMessage_preserves_network verify ns m hviews) e he with
    ⟨a, ha, hsig, hscid, _⟩
  exact ⟨a, ha, hsig, hscid⟩

/-! ## Counterexamples: the raw wave-A model does not enforce the claim -/

private def rejectAll : SigVerifier := fun _ _ _ => false

private def zeroKey : PubKey := ⟨ByteArray.empty⟩

private def emptySig : GossipSignature := ⟨ByteArray.empty⟩

private def zeroScid : ShortChannelId := ⟨0, 0, 0⟩

private def forgedAnnouncement : ChannelAnnellation :=
  { shortChannelId := zeroScid
    node1 := ⟨0⟩
    node2 := ⟨1⟩
    nodeKey1 := zeroKey
    nodeKey2 := zeroKey
    bitcoinKey1 := zeroKey
    bitcoinKey2 := zeroKey
    capacitySat := 0
    digest := ByteArray.empty
    nodeSignature1 := emptySig
    nodeSignature2 := emptySig
    bitcoinSignature1 := emptySig
    bitcoinSignature2 := emptySig }

private def emptyStore : GossipState := ⟨[], [], []⟩

private def zeroView : ChannelView :=
  { scid := zeroScid
    node1 := ⟨0⟩
    node2 := ⟨1⟩
    capacitySat := 0
    feeBaseMsat := Msat.zero
    feeProportionalMillionths := 0
    cltvDelta := 0
    timestamp := 0
    disabled := false }

private def unbackedNetwork : GossipNetwork :=
  { gossip := emptyStore, views := [zeroView] }

private theorem forged_not_valid :
    ¬ forgedAnnouncement.signaturesValid rejectAll := by
  simp [ChannelAnnellation.signaturesValid, signatureValid, rejectAll]

/-- **Raw `applyGossip` admits a forged announcement.**  With a verifier that
rejects everything, feeding a `channel_announcement` to the wave-A transition
nevertheless stores it, so the store invariant fails. -/
theorem waveD_d27_raw_applyGossip_admits_invalid :
    ¬ AnnouncementsValid rejectAll
        (applyGossip emptyStore (.channelAnnouncement forgedAnnouncement)) := by
  intro h
  exact forged_not_valid
    (h forgedAnnouncement (by simp [applyGossip, emptyStore]))

/-- The signature-gated transition rejects the same forged announcement, so
the invariant is preserved on the checked path. -/
theorem waveD_d27_checked_applyGossip_rejects_invalid :
    applyGossipChecked rejectAll emptyStore
        (.channelAnnouncement forgedAnnouncement) = emptyStore :=
  applyGossipChecked_rejects_announcement rejectAll emptyStore
    forgedAnnouncement forged_not_valid

/-- **The network graph invariant is not free.**  A network state with no
stored announcements still has one routing edge, so the backing relation
`NetworkChannelsValid` fails.  The raw model permits edges with no
`channel_announcement` at all. -/
theorem waveD_d27_network_invariant_not_free :
    ¬ NetworkChannelsValid rejectAll unbackedNetwork := by
  intro h
  obtain ⟨a, ha, _⟩ := h zeroView (by simp [unbackedNetwork])
  simp [unbackedNetwork, emptyStore] at ha

end LnLean.Proofs.WaveD.D27

/-! ## Catalog target alias

The catalog names `LnLean.Routing.Gossip.announcement_valid`; the model
module did not declare it.  As with the other wave-D catalog targets, the
declaration is supplied here as a transparent alias of the statement proved
in this module. -/

namespace LnLean.Routing

namespace Gossip

/-- **Announcement validity** (catalog target
`LnLean.Routing.Gossip.announcement_valid`, `LN-RT-006`): all four BOLT 7
signatures of a `channel_announcement` verify under the announced keys. -/
def announcement_valid (verify : SigVerifier) (a : ChannelAnnellation) : Prop :=
  LnLean.Proofs.WaveD.D27.announcementValid verify a

end Gossip

end LnLean.Routing
