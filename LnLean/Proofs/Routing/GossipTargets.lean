import LnLean.Proofs.Routing.GossipProps

/-!
# LnLean.Proofs.Routing.GossipTargets

Exact targets for catalog row `LN-RT-006`:

> The gossip graph contains only channels with valid announcement signatures.

## What the wave-A model does and does not enforce

Wave A has three separate facts that the English sentence conflates:

* `LnLean.Routing.applyGossip` appends every `channel_announcement` to the
  store **without any signature check** (see
  `raw_applyGossip_announcement_mem_iff` below: membership is exactly
  `a = a₀ ∨ a ∈ s.announcements`, with no validity conjunct).
* `LnLean.Proofs.Routing.GossipProps.applyGossipChecked` is the
  signature-gated store step: it checks `a.signaturesValid verify` first
  (`GossipProps.applyGossipChecked_rejects_announcement`).
* `LnLean.Routing.Gossip.GossipState` has **no graph**, and
  `LnLean.Routing.Gossip.GossipNetwork.views` is an unconstrained field.
  `GossipNetwork.applyMessage` never materialises a view from an admitted
  announcement, so the wave-A graph is not produced by the store at all.

Consequently the unconditional English claim is *false* for the raw store
step and is *not even well posed* for the raw graph: a `Graph` can contain an
edge with no announcement behind it.  This module therefore

1. proves the exact raw-store gap and its counterexample
   (`raw_applyGossip_admits_invalid_announcement`,
   `raw_store_not_filtered`);
2. gives the strongest exact characterization of the checked store step
   (`applyGossipChecked_announcement_mem_iff`, `admitAnnouncement_stores_iff`);
3. defines an explicit **admission model** (`admitGossip`) that checks the
   announcement signature before inserting the announcement *and* the
   corresponding channel view, and proves that every edge of the graph of
   every reachable state is backed by a stored announcement whose four BOLT 7
   signatures verify (`gossip_graph_only_valid_announcements`);
4. keeps the G19 key-attribution gap explicit: an accepted `channel_update`
   is *not* required by `acceptChannelUpdate` to be signed by one of the
   announced node keys, and a `channel_announcement`'s graph `NodeId` is not
   linked to its BOLT 7 `PubKey` (`g19_signature_only_gap`,
   `signature_valid_not_key_attribution`).  The required extra checks are
   `admitUpdateAttributed`'s `updateKeyAnnounced` conjunct and the
   `KeyAttribution` predicate.

## Trust boundary

The verifier `SigVerifier` is an abstract parameter.  "Valid announcement
signature" means exactly `ChannelAnnellation.signaturesValid verify`, i.e. the
four `verify key digest sig = true` equations.  No unforgeability, key
ownership, chain-hash filtering, or UTXO check is claimed; those are
assumption C3/C4/C8 and the BOLT 7 admission rules listed in
`LnLean/Routing/Gossip.lean`.  The graph statement is about *signature
validity*, not about key attribution; the latter is deliberately a separate,
missing admission check.

No `sorry`, no `axiom`, no `native_decide`, no `unsafe`.
-/

namespace LnLean.Proofs.Routing.GossipTargets

open LnLean.Routing
open LnLean.Routing.GossipProps
open Classical

set_option autoImplicit false

/-! ## 0. Concrete witnesses

These are used only for non-vacuity and gap counterexamples. -/

/-- A verifier that accepts every signature.  Used only for non-vacuity and
gap witnesses; it is not a model of a secure verifier. -/
private def acceptingVerifier : SigVerifier := fun _ _ _ => true

private def emptyStore : GossipState := ⟨[], [], []⟩

private def emptyNetwork : GossipNetwork := { gossip := emptyStore, views := [] }

private def emptySig : GossipSignature := ⟨ByteArray.empty⟩

private def zeroKey : PubKey := ⟨ByteArray.empty⟩

/-- A key different from `zeroKey` (its byte length is 1, not 0). -/
private def oddKey : PubKey := ⟨ByteArray.mk #[0]⟩

private def sampleScid : ShortChannelId := ⟨1, 2, 3⟩

private def sampleAnnouncement : ChannelAnnellation :=
  { shortChannelId := sampleScid
    node1 := ⟨0⟩
    node2 := ⟨1⟩
    nodeKey1 := zeroKey
    nodeKey2 := oddKey
    bitcoinKey1 := zeroKey
    bitcoinKey2 := oddKey
    capacitySat := 1000
    digest := ByteArray.empty
    nodeSignature1 := emptySig
    nodeSignature2 := emptySig
    bitcoinSignature1 := emptySig
    bitcoinSignature2 := emptySig }

private def zeroAnnouncement : ChannelAnnellation :=
  { shortChannelId := sampleScid
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
    signingKey := zeroKey
    digest := ByteArray.empty
    signature := emptySig }

private theorem sampleAnnouncement_valid :
    sampleAnnouncement.signaturesValid acceptingVerifier := by
  simp [ChannelAnnellation.signaturesValid, signatureValid, acceptingVerifier]

private theorem zeroAnnouncement_invalid :
    ¬ zeroAnnouncement.signaturesValid (fun _ _ _ => false) := by
  simp [ChannelAnnellation.signaturesValid, signatureValid]

private theorem sampleUpdate_unannounced :
    ¬ updateKeyAnnounced emptyStore sampleUpdate := by
  rintro ⟨a, ha, _⟩
  simp [emptyStore] at ha

/-! ## 1. The predicate, unfolded exactly -/

/-- Catalog spelling of announcement validity: all four BOLT 7 signatures of
a `channel_announcement` verify under the announced node and Bitcoin keys.
This is definitionally `ChannelAnnellation.signaturesValid`. -/
def announcementValid (verify : SigVerifier) (a : ChannelAnnellation) : Prop :=
  a.signaturesValid verify

/-- **Exact unfolding.**  Announcement validity is the conjunction of the four
verifier equations, with no extra conjunct hidden in a predicate. -/
theorem announcementValid_iff (verify : SigVerifier) (a : ChannelAnnellation) :
    announcementValid verify a ↔
      signatureValid verify a.nodeKey1 a.digest a.nodeSignature1 ∧
      signatureValid verify a.nodeKey2 a.digest a.nodeSignature2 ∧
      signatureValid verify a.bitcoinKey1 a.digest a.bitcoinSignature1 ∧
      signatureValid verify a.bitcoinKey2 a.digest a.bitcoinSignature2 :=
  Iff.rfl

/-- The store invariant behind the catalog claim: every stored
`channel_announcement` has four verifying BOLT 7 signatures. -/
def StoreAnnouncementsValid (verify : SigVerifier) (s : GossipState) : Prop :=
  ∀ a ∈ s.announcements, announcementValid verify a

/-! ## 2. The raw wave-A store step does not check signatures

`applyGossip` is the transition used by `GossipState` in wave A.  The two
theorems below are the exact statement of the gap: the announcement list
grows by the new announcement regardless of `signaturesValid`. -/

/-- **Exact raw-store membership.**  There is no signature condition in the
raw wave-A transition. -/
theorem raw_applyGossip_announcement_mem_iff (s : GossipState)
    (a₀ a : ChannelAnnellation) :
    a ∈ (applyGossip s (.channelAnnouncement a₀)).announcements ↔
      a = a₀ ∨ a ∈ s.announcements := by
  simp [applyGossip]

/-- The raw transition stores an announcement even when every signature
check fails. -/
theorem raw_applyGossip_admits_invalid_announcement (verify : SigVerifier)
    (s : GossipState) (a : ChannelAnnellation)
    (_h : ¬ announcementValid verify a) :
    a ∈ (applyGossip s (.channelAnnouncement a)).announcements := by
  rw [raw_applyGossip_announcement_mem_iff]
  exact Or.inl rfl

/-- **The raw store is not filtered by signatures.**  There is a verifier, a
store, and an announcement such that the announcement enters the raw store
while all four signature checks fail. -/
theorem raw_store_not_filtered :
    ∃ (verify : SigVerifier) (s : GossipState) (a : ChannelAnnellation),
      a ∈ (applyGossip s (.channelAnnouncement a)).announcements ∧
        ¬ announcementValid verify a := by
  refine ⟨fun _ _ _ => false, emptyStore, zeroAnnouncement, ?_, ?_⟩
  · exact raw_applyGossip_admits_invalid_announcement _ _ _ zeroAnnouncement_invalid
  · exact zeroAnnouncement_invalid

/-- The raw store can therefore violate the store-level invariant "every
stored announcement verifies". -/
theorem raw_store_invariant_not_preserved :
    ∃ (verify : SigVerifier) (s : GossipState) (a : ChannelAnnellation),
      ¬ StoreAnnouncementsValid verify
        (applyGossip s (.channelAnnouncement a)) := by
  refine ⟨fun _ _ _ => false, emptyStore, zeroAnnouncement, ?_⟩
  intro h
  exact zeroAnnouncement_invalid
    (h zeroAnnouncement (raw_applyGossip_admits_invalid_announcement _ _ _
      zeroAnnouncement_invalid))

/-! ## 3. The checked store step: exact characterization and admission model -/

/-- **Exact checked-store membership.**  The signature-gated transition
stores exactly `a₀` when `a₀` verifies, and otherwise stores nothing.  This is
the strongest exact characterization of the checked step's announcement list:
membership is `(a = a₀ ∧ a₀ valid) ∨ a ∈ s.announcements`. -/
theorem applyGossipChecked_announcement_mem_iff (verify : SigVerifier)
    (s : GossipState) (a₀ a : ChannelAnnellation) :
    a ∈ (applyGossipChecked verify s (.channelAnnouncement a₀)).announcements ↔
      (a = a₀ ∧ announcementValid verify a₀) ∨ a ∈ s.announcements := by
  by_cases h : a₀.signaturesValid verify
  · simp [applyGossipChecked, applyGossip, h, announcementValid]
  · simp [applyGossipChecked, h, announcementValid]

/-- A `channel_update` never changes the checked store's announcement list. -/
theorem applyGossipChecked_update_announcements (verify : SigVerifier)
    (s : GossipState) (u : ChannelUpdate) :
    (applyGossipChecked verify s (.channelUpdate u)).announcements =
      s.announcements := by
  simp only [applyGossipChecked, acceptChannelUpdate]
  split
  · exact applyUpdate_announcements s u
  · rfl

/-- A `node_announcement` never changes the checked store's announcement
list. -/
theorem applyGossipChecked_node_announcements (verify : SigVerifier)
    (s : GossipState) (n : NodeAnnouncement) :
    (applyGossipChecked verify s (.nodeAnnouncement n)).announcements =
      s.announcements := by
  simp only [applyGossipChecked]
  split <;> rfl

/-- The checked step preserves the store invariant.  This is the store half of
the admission theorem. -/
theorem applyGossipChecked_preserves_store (verify : SigVerifier)
    (s : GossipState) (m : GossipMessage)
    (h : StoreAnnouncementsValid verify s) :
    StoreAnnouncementsValid verify (applyGossipChecked verify s m) := by
  intro a ha
  cases m with
  | channelAnnouncement a₀ =>
      rcases (applyGossipChecked_announcement_mem_iff verify s a₀ a).mp ha with
        ⟨rfl, hsig⟩ | ha
      · exact hsig
      · exact h a ha
  | channelUpdate u =>
      rw [applyGossipChecked_update_announcements verify s u] at ha
      exact h a ha
  | nodeAnnouncement n =>
      rw [applyGossipChecked_node_announcements verify s n] at ha
      exact h a ha

/-- A standalone checked announcement-insertion step.  It is the
announcement branch of `applyGossipChecked`, named so that the admission
model can be stated without the three-way message dispatch. -/
noncomputable def admitAnnouncement (verify : SigVerifier) (s : GossipState)
    (a : ChannelAnnellation) : GossipState :=
  if a.signaturesValid verify then applyGossip s (.channelAnnouncement a) else s

/-- **Exact admission characterization.**  The step inserts the announcement
at the head of the store **iff** its four signatures verify.  The reverse
direction is not vacuous: a successful insertion strictly grows the list. -/
theorem admitAnnouncement_stores_iff (verify : SigVerifier) (s : GossipState)
    (a : ChannelAnnellation) :
    (admitAnnouncement verify s a).announcements = a :: s.announcements ↔
      announcementValid verify a := by
  constructor
  · intro h
    apply Classical.byContradiction
    intro hbad
    rw [admitAnnouncement,
      ite_eq_right (show ¬ a.signaturesValid verify from hbad)] at h
    have hlen := congrArg List.length h
    simp only [List.length_cons] at hlen
    exact Nat.succ_ne_self _ hlen.symm
  · intro hsig
    rw [admitAnnouncement,
      ite_eq_left (show a.signaturesValid verify from hsig)]
    rfl

/-- An invalid announcement is rejected: the store is unchanged. -/
theorem admitAnnouncement_eq_self_of_invalid (verify : SigVerifier)
    (s : GossipState) (a : ChannelAnnellation)
    (h : ¬ announcementValid verify a) :
    admitAnnouncement verify s a = s := by
  rw [admitAnnouncement,
    ite_eq_right (show ¬ a.signaturesValid verify from h)]

/-- A valid announcement is inserted at the head. -/
theorem admitAnnouncement_announcements_of_valid (verify : SigVerifier)
    (s : GossipState) (a : ChannelAnnellation)
    (h : announcementValid verify a) :
    (admitAnnouncement verify s a).announcements = a :: s.announcements :=
  (admitAnnouncement_stores_iff verify s a).mpr h

/-- **Admission changes the store iff the announcement verifies.**  This is
the exact "checked step" form of the catalog claim at store level. -/
theorem admitAnnouncement_changes_iff (verify : SigVerifier) (s : GossipState)
    (a : ChannelAnnellation) :
    admitAnnouncement verify s a ≠ s ↔ announcementValid verify a := by
  constructor
  · intro hchange
    apply Classical.byContradiction
    intro hbad
    exact hchange (admitAnnouncement_eq_self_of_invalid verify s a hbad)
  · intro hsig hsame
    have hvalid := admitAnnouncement_announcements_of_valid verify s a hsig
    have hsame' := congrArg GossipState.announcements hsame
    have hlen := congrArg List.length (hvalid.symm.trans hsame')
    simp only [List.length_cons] at hlen
    exact Nat.succ_ne_self _ hlen

/-! ## 4. Filtering at materialisation: announcement graphs

The wave-A graph projection `viewGraph` maps a list of `ChannelView`s without
consulting the announcements.  The following projection is the explicit
filtered one: an announcement contributes a view (and therefore an edge) only
when it verifies. -/

/-- The channel view that an admitted announcement contributes.  An
announcement carries no per-direction fees, so they start at zero; the later
`channel_update` fills them in (see `ChannelView.applyUpdate`). -/
def admittedChannelView (a : ChannelAnnellation) : ChannelView :=
  { scid := a.shortChannelId
    node1 := a.node1
    node2 := a.node2
    capacitySat := a.capacitySat
    feeBaseMsat := Msat.zero
    feeProportionalMillionths := 0
    cltvDelta := 0
    timestamp := 0
    disabled := false }

/-- The view contributed by an announcement, if and only if it verifies. -/
noncomputable def admittedView (verify : SigVerifier) (a : ChannelAnnellation) :
    Option ChannelView :=
  if a.signaturesValid verify then some (admittedChannelView a) else none

@[simp] theorem admittedView_of_valid (verify : SigVerifier)
    (a : ChannelAnnellation) (h : a.signaturesValid verify) :
    admittedView verify a = some (admittedChannelView a) := by
  rw [admittedView, ite_eq_left h]

@[simp] theorem admittedView_of_invalid (verify : SigVerifier)
    (a : ChannelAnnellation) (h : ¬ a.signaturesValid verify) :
    admittedView verify a = none := by
  rw [admittedView, ite_eq_right h]

/-- Exact characterization of the views contributed by a list of
announcements. -/
theorem mem_admittedViews_iff (verify : SigVerifier)
    (l : List ChannelAnnellation) (v : ChannelView) :
    v ∈ l.filterMap (admittedView verify) ↔
      ∃ a ∈ l, a.signaturesValid verify ∧ v = admittedChannelView a := by
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨a, ha, hv⟩
    by_cases hsig : a.signaturesValid verify
    · rw [admittedView_of_valid verify a hsig] at hv
      cases hv
      exact ⟨a, ha, hsig, rfl⟩
    · rw [admittedView_of_invalid verify a hsig] at hv
      simp at hv
  · rintro ⟨a, ha, hsig, rfl⟩
    exact ⟨a, ha, admittedView_of_valid verify a hsig⟩

/-- Materialise a list of announcements as a graph, dropping every
announcement whose four signatures do not verify. -/
noncomputable def announcementGraph (verify : SigVerifier)
    (l : List ChannelAnnellation) : Graph :=
  viewGraph (l.filterMap (admittedView verify))

/-- A `ChannelBinding` view of an announcement, used to state the materialised
edge exactly. -/
def ChannelBinding.ofAnnouncement (a : ChannelAnnellation) : ChannelBinding :=
  { scid := a.shortChannelId
    node1 := a.node1
    node2 := a.node2
    nodeKey1 := a.nodeKey1
    nodeKey2 := a.nodeKey2
    capacitySat := a.capacitySat }

@[simp] theorem admittedChannelView_edge (a : ChannelAnnellation) :
    (admittedChannelView a).edge = (ChannelBinding.ofAnnouncement a).edge :=
  rfl

/-- **Exact edge characterization of the filtered graph.**  An edge is
present iff it is the edge materialised from an announcement in the list that
passes all four signature checks. -/
theorem mem_announcementGraph_edges_iff (verify : SigVerifier)
    (l : List ChannelAnnellation) (e : ChannelEdge) :
    e ∈ (announcementGraph verify l).edges ↔
      ∃ a ∈ l, a.signaturesValid verify ∧
        e = (ChannelBinding.ofAnnouncement a).edge := by
  unfold announcementGraph
  constructor
  · intro he
    rcases List.mem_map.mp he with ⟨v, hv, rfl⟩
    rcases (mem_admittedViews_iff verify l v).mp hv with ⟨a, ha, hsig, rfl⟩
    exact ⟨a, ha, hsig, rfl⟩
  · rintro ⟨a, ha, hsig, rfl⟩
    apply List.mem_map.mpr
    refine ⟨admittedChannelView a, ?_, (admittedChannelView_edge a).symm⟩
    exact (mem_admittedViews_iff verify l (admittedChannelView a)).mpr
      ⟨a, ha, hsig, rfl⟩

/-- **The filtered announcement graph contains only channels with valid
announcement signatures.**  This is the graph-level claim for the explicit
filtering projection: unconditional in the announcement list. -/
theorem announcementGraph_only_valid (verify : SigVerifier)
    (l : List ChannelAnnellation) :
    ∀ e ∈ (announcementGraph verify l).edges,
      ∃ a ∈ l, announcementValid verify a ∧ e.shortChannelId = a.shortChannelId := by
  intro e he
  rcases (mem_announcementGraph_edges_iff verify l e).mp he with
    ⟨a, ha, hsig, rfl⟩
  exact ⟨a, ha, hsig, rfl⟩

/-- No announcement verifies, so the filtered graph has no edges. -/
theorem announcementGraph_edges_eq_nil_of_all_invalid (verify : SigVerifier)
    (l : List ChannelAnnellation)
    (h : ∀ a ∈ l, ¬ a.signaturesValid verify) :
    (announcementGraph verify l).edges = [] := by
  unfold announcementGraph viewGraph
  rw [List.map_eq_nil_iff, List.filterMap_eq_nil_iff]
  intro a ha
  exact admittedView_of_invalid verify a (h a ha)

/-- Non-vacuity of the filtered graph: a verifying announcement really
materialises its edge. -/
theorem announcementGraph_contains_valid_edge (verify : SigVerifier)
    (a : ChannelAnnellation) (h : a.signaturesValid verify) :
    (ChannelBinding.ofAnnouncement a).edge ∈
      (announcementGraph verify [a]).edges := by
  rw [mem_announcementGraph_edges_iff]
  exact ⟨a, by simp, h, rfl⟩

/-! ## 5. Network admission: the graph is built only from admitted
announcements

`admitGossip` is an explicit admission transition.  Unlike wave-A
`GossipNetwork.applyMessage`, a `channel_announcement` that passes the
signature check inserts its channel view into the routing graph.  The
`Reachable` predicate closes this step over all three gossip messages, so the
graph statement below is about states reachable from the empty network — not
about an arbitrary, unconstrained `GossipNetwork.views` field. -/

/-- Admission transition for one gossip message.

* `channel_announcement`: insert the announcement into the store and, only if
  its four signatures verify, insert the corresponding channel view.
* `channel_update`: insert into the checked store and apply the per-view
  replacement rule only if the update's signature verifies.
* `node_announcement`: insert into the checked store only if its signature
  verifies; it contributes no routing edge. -/
noncomputable def admitGossip (verify : SigVerifier) (ns : GossipNetwork) :
    GossipMessage → GossipNetwork
  | .channelAnnouncement a =>
      if a.signaturesValid verify then
        { gossip := applyGossip ns.gossip (.channelAnnouncement a)
          views := admittedChannelView a :: ns.views }
      else ns
  | .channelUpdate u =>
      if u.signatureValid verify then
        { gossip := applyGossip ns.gossip (.channelUpdate u)
          views := ns.views.map fun v => v.applyUpdate u }
      else ns
  | .nodeAnnouncement n =>
      if n.signatureValid verify then
        { gossip := applyGossip ns.gossip (.nodeAnnouncement n)
          views := ns.views }
      else ns

@[simp] theorem admitGossip_announcement_of_valid (verify : SigVerifier)
    (ns : GossipNetwork) (a : ChannelAnnellation)
    (h : a.signaturesValid verify) :
    admitGossip verify ns (.channelAnnouncement a) =
      { gossip := applyGossip ns.gossip (.channelAnnouncement a)
        views := admittedChannelView a :: ns.views } := by
  simp [admitGossip, h]

@[simp] theorem admitGossip_announcement_of_invalid (verify : SigVerifier)
    (ns : GossipNetwork) (a : ChannelAnnellation)
    (h : ¬ a.signaturesValid verify) :
    admitGossip verify ns (.channelAnnouncement a) = ns := by
  simp [admitGossip, h]

@[simp] theorem admitGossip_update_of_valid (verify : SigVerifier)
    (ns : GossipNetwork) (u : ChannelUpdate)
    (h : u.signatureValid verify) :
    admitGossip verify ns (.channelUpdate u) =
      { gossip := applyGossip ns.gossip (.channelUpdate u)
        views := ns.views.map fun v => v.applyUpdate u } := by
  simp [admitGossip, h]

@[simp] theorem admitGossip_update_of_invalid (verify : SigVerifier)
    (ns : GossipNetwork) (u : ChannelUpdate)
    (h : ¬ u.signatureValid verify) :
    admitGossip verify ns (.channelUpdate u) = ns := by
  simp [admitGossip, h]

@[simp] theorem admitGossip_node_of_valid (verify : SigVerifier)
    (ns : GossipNetwork) (n : NodeAnnouncement)
    (h : n.signatureValid verify) :
    admitGossip verify ns (.nodeAnnouncement n) =
      { gossip := applyGossip ns.gossip (.nodeAnnouncement n)
        views := ns.views } := by
  simp [admitGossip, h]

@[simp] theorem admitGossip_node_of_invalid (verify : SigVerifier)
    (ns : GossipNetwork) (n : NodeAnnouncement)
    (h : ¬ n.signatureValid verify) :
    admitGossip verify ns (.nodeAnnouncement n) = ns := by
  simp [admitGossip, h]

/-- The store component of the admission model is exactly the existing
signature-gated store step `GossipProps.applyGossipChecked`.  This pins the
admission model to the checked transition rather than to raw `applyGossip`. -/
theorem admitGossip_gossip_eq (verify : SigVerifier) (ns : GossipNetwork)
    (m : GossipMessage) :
    (admitGossip verify ns m).gossip =
      applyGossipChecked verify ns.gossip m := by
  cases m with
  | channelAnnouncement a =>
      by_cases h : a.signaturesValid verify
      · simp [admitGossip, applyGossipChecked, h]
      · simp [admitGossip, applyGossipChecked, h]
  | channelUpdate u =>
      by_cases h : u.signatureValid verify
      · simp only [admitGossip, h, applyGossipChecked, acceptChannelUpdate]
        rfl
      · simp [admitGossip, applyGossipChecked, acceptChannelUpdate, h]
  | nodeAnnouncement n =>
      by_cases h : n.signatureValid verify
      · simp [admitGossip, applyGossipChecked, h]
      · simp [admitGossip, applyGossipChecked, h]

/-- **Exact network admission membership.**  A `channel_announcement`
enters the admitted network's store exactly when it is the offered
announcement and that announcement verifies (or it was already stored). -/
theorem admitGossip_announcement_mem_iff (verify : SigVerifier)
    (ns : GossipNetwork) (a₀ a : ChannelAnnellation) :
    a ∈ (admitGossip verify ns (.channelAnnouncement a₀)).gossip.announcements ↔
      (a = a₀ ∧ announcementValid verify a₀) ∨ a ∈ ns.gossip.announcements := by
  rw [admitGossip_gossip_eq, applyGossipChecked_announcement_mem_iff]

/-- Non-vacuity of the checked store step: a verifying announcement really is
inserted at the head. -/
theorem admitAnnouncement_accepts_valid :
    ∃ (verify : SigVerifier) (s : GossipState) (a : ChannelAnnellation),
      announcementValid verify a ∧
        (admitAnnouncement verify s a).announcements = a :: s.announcements := by
  exact ⟨acceptingVerifier, emptyStore, sampleAnnouncement,
    sampleAnnouncement_valid,
    admitAnnouncement_announcements_of_valid acceptingVerifier emptyStore
      sampleAnnouncement sampleAnnouncement_valid⟩

/-- A state is reachable when it is obtained from the empty network by a
finite sequence of signature-gated `admitGossip` steps. -/
inductive Reachable (verify : SigVerifier) : GossipNetwork → Prop
  | empty : Reachable verify { gossip := ⟨[], [], []⟩, views := [] }
  | step {ns : GossipNetwork} {m : GossipMessage} :
      Reachable verify ns → Reachable verify (admitGossip verify ns m)

/-- Every routing view is backed by a stored announcement whose four
signatures verify.

This is *not* an extra hypothesis in the final theorem: `Reachable` builds
the views only through `admitGossip`, so the relation is a structural
invariant of reachable states. -/
def ViewsBacked (verify : SigVerifier) (ns : GossipNetwork) : Prop :=
  ∀ v ∈ ns.views, ∃ a ∈ ns.gossip.announcements,
    a.signaturesValid verify ∧ v.scid = a.shortChannelId ∧
      v.node1 = a.node1 ∧ v.node2 = a.node2 ∧
        v.capacitySat = a.capacitySat

/-- Reachable states have a store in which every announcement verifies. -/
theorem reachable_store_valid {verify : SigVerifier} {ns : GossipNetwork}
    (h : Reachable verify ns) : StoreAnnouncementsValid verify ns.gossip := by
  induction h with
  | empty =>
      intro a ha
      simp at ha
  | @step ns m hprev ih =>
      cases m with
      | channelAnnouncement a =>
          by_cases hsig : a.signaturesValid verify
          · have hann :
                (admitGossip verify ns (.channelAnnouncement a)).gossip.announcements =
                  a :: ns.gossip.announcements := by
              rw [admitGossip_announcement_of_valid verify ns a hsig]
              rfl
            intro b hb
            rw [hann] at hb
            rcases List.mem_cons.mp hb with rfl | hb
            · exact hsig
            · exact ih b hb
          · rw [admitGossip_announcement_of_invalid verify ns a hsig]
            exact ih
      | channelUpdate u =>
          by_cases hsig : u.signatureValid verify
          · have hann :
                (admitGossip verify ns (.channelUpdate u)).gossip.announcements =
                  ns.gossip.announcements := by
              rw [admitGossip_update_of_valid verify ns u hsig]
              show (ns.gossip.applyUpdate u).announcements = ns.gossip.announcements
              exact applyUpdate_announcements ns.gossip u
            intro b hb
            rw [hann] at hb
            exact ih b hb
          · rw [admitGossip_update_of_invalid verify ns u hsig]
            exact ih
      | nodeAnnouncement n =>
          by_cases hsig : n.signatureValid verify
          · have hann :
                (admitGossip verify ns (.nodeAnnouncement n)).gossip.announcements =
                  ns.gossip.announcements := by
              rw [admitGossip_node_of_valid verify ns n hsig]
              rfl
            intro b hb
            rw [hann] at hb
            exact ih b hb
          · rw [admitGossip_node_of_invalid verify ns n hsig]
            exact ih

/-- Reachable states have only announcement-backed views. -/
theorem reachable_views_backed {verify : SigVerifier} {ns : GossipNetwork}
    (h : Reachable verify ns) : ViewsBacked verify ns := by
  induction h with
  | empty =>
      intro v hv
      simp at hv
  | @step ns m hprev ih =>
      cases m with
      | channelAnnouncement a =>
          by_cases hsig : a.signaturesValid verify
          · rw [admitGossip_announcement_of_valid verify ns a hsig]
            intro v hv
            rcases List.mem_cons.mp hv with rfl | hv
            · have hmem : a ∈
                  (applyGossip ns.gossip (.channelAnnouncement a)).announcements := by
                exact List.mem_cons_self ..
              exact ⟨a, hmem, hsig, rfl, rfl, rfl, rfl⟩
            · rcases ih v hv with ⟨b, hb, hbsig, hscid, h1, h2, hcap⟩
              have hmem : b ∈
                  (applyGossip ns.gossip (.channelAnnouncement a)).announcements := by
                exact List.mem_cons_of_mem a hb
              exact ⟨b, hmem, hbsig, hscid, h1, h2, hcap⟩
          · rw [admitGossip_announcement_of_invalid verify ns a hsig]
            exact ih
      | channelUpdate u =>
          by_cases hsig : u.signatureValid verify
          · rw [admitGossip_update_of_valid verify ns u hsig]
            intro v hv
            rcases List.mem_map.mp hv with ⟨w, hw, rfl⟩
            rcases ih w hw with ⟨b, hb, hbsig, hscid, h1, h2, hcap⟩
            have hmem : b ∈
                (applyGossip ns.gossip (.channelUpdate u)).announcements := by
              show b ∈ (ns.gossip.applyUpdate u).announcements
              rw [applyUpdate_announcements]
              exact hb
            exact ⟨b, hmem, hbsig,
              by rw [ChannelView.applyUpdate_scid]; exact hscid,
              by rw [ChannelView.applyUpdate_node1]; exact h1,
              by rw [ChannelView.applyUpdate_node2]; exact h2,
              by rw [ChannelView.applyUpdate_capacitySat]; exact hcap⟩
          · rw [admitGossip_update_of_invalid verify ns u hsig]
            exact ih
      | nodeAnnouncement n =>
          by_cases hsig : n.signatureValid verify
          · rw [admitGossip_node_of_valid verify ns n hsig]
            intro v hv
            rcases ih v hv with ⟨b, hb, hbsig, hscid, h1, h2, hcap⟩
            have hmem : b ∈
                (applyGossip ns.gossip (.nodeAnnouncement n)).announcements := by
              exact hb
            exact ⟨b, hmem, hbsig, hscid, h1, h2, hcap⟩
          · rw [admitGossip_node_of_invalid verify ns n hsig]
            exact ih

/-- **If an announcement enters a reachable store, it verifies.**  Direct
"enters the store" form of the catalog claim. -/
theorem reachable_stored_announcement_valid {verify : SigVerifier}
    {ns : GossipNetwork} (h : Reachable verify ns) {a : ChannelAnnellation}
    (ha : a ∈ ns.gossip.announcements) : announcementValid verify a :=
  reachable_store_valid h a ha

/-- **`LN-RT-006`, graph-level exact target.**  Every edge of the routing
graph of a reachable admitted network is backed by a stored
`channel_announcement` whose four BOLT 7 signatures verify under the explicit
`SigVerifier` contract.

The word "reachable" is essential: wave-A `GossipNetwork.views` is an
unconstrained field, so the claim is false for an arbitrary network state (see
`arbitrary_network_edge_without_announcement`). -/
theorem gossip_graph_only_valid_announcements (verify : SigVerifier)
    (ns : GossipNetwork) (h : Reachable verify ns) :
    ∀ e ∈ ns.graph.edges,
      ∃ a ∈ ns.gossip.announcements,
        announcementValid verify a ∧ e.shortChannelId = a.shortChannelId := by
  intro e he
  have he' : e ∈ ns.views.map ChannelView.edge := he
  rcases List.mem_map.mp he' with ⟨v, hv, rfl⟩
  rcases reachable_views_backed h v hv with ⟨a, ha, hsig, hscid, _⟩
  exact ⟨a, ha, hsig, hscid⟩

/-- The same statement with the exact endpoint/capacity attribution: the edge
is the materialised view of the backing announcement. -/
theorem gossip_graph_edges_backed (verify : SigVerifier)
    (ns : GossipNetwork) (h : Reachable verify ns) :
    ∀ e ∈ ns.graph.edges, ∃ a ∈ ns.gossip.announcements,
      announcementValid verify a ∧ e.shortChannelId = a.shortChannelId ∧
        e.node1 = a.node1 ∧ e.node2 = a.node2 ∧
          e.capacitySat = a.capacitySat := by
  intro e he
  have he' : e ∈ ns.views.map ChannelView.edge := he
  rcases List.mem_map.mp he' with ⟨v, hv, rfl⟩
  rcases reachable_views_backed h v hv with ⟨a, ha, hsig, hscid, h1, h2, hcap⟩
  exact ⟨a, ha, hsig, hscid, h1, h2, hcap⟩

/-- An admitted announcement really becomes a graph edge: the admission step's
graph is the new channel edge prepended to the old graph. -/
theorem admitGossip_announcement_graph_edges (verify : SigVerifier)
    (ns : GossipNetwork) (a : ChannelAnnellation)
    (h : a.signaturesValid verify) :
    (admitGossip verify ns (.channelAnnouncement a)).graph.edges =
      (ChannelBinding.ofAnnouncement a).edge :: ns.graph.edges := by
  rw [admitGossip_announcement_of_valid verify ns a h]
  simp [GossipNetwork.graph, viewGraph, admittedChannelView,
    ChannelBinding.ofAnnouncement, ChannelBinding.edge, ChannelView.edge]

/-- Non-vacuity: there is a reachable state whose graph has an edge. -/
theorem reachable_graph_nonempty :
    ∃ (verify : SigVerifier) (ns : GossipNetwork),
      Reachable verify ns ∧ ns.graph.edges ≠ [] := by
  refine ⟨acceptingVerifier, admitGossip acceptingVerifier emptyNetwork
      (.channelAnnouncement sampleAnnouncement),
    Reachable.step Reachable.empty, ?_⟩
  rw [admitGossip_announcement_graph_edges acceptingVerifier emptyNetwork
    sampleAnnouncement sampleAnnouncement_valid]
  simp [emptyNetwork, GossipNetwork.graph, viewGraph]

/-- **The claim is not free in the raw model.**  A wave-A network state can
have a graph edge while its store is empty, so an arbitrary state does not
satisfy even the backing relation.  This is the graph half of the gap that
`Reachable` closes by construction. -/
theorem arbitrary_network_edge_without_announcement :
    ∃ ns : GossipNetwork, ns.gossip.announcements = [] ∧ ns.graph.edges ≠ [] := by
  refine ⟨{ gossip := emptyStore, views := [admittedChannelView sampleAnnouncement] },
    rfl, ?_⟩
  simp [GossipNetwork.graph, viewGraph]

/-! ## 6. G19: the key-attribution gap is kept explicit

`LN-GOSSIP-001` (audit G19) is the claim that an accepted `channel_update`
is signed by one of the two node keys announced for its channel.  The
signature-gated store accepts a *signature-valid* update regardless of which
key signed it, and `ChannelUpdate.signingKey` is an independent field.  The
predicate `updateKeyAnnounced` is the missing admission check; the theorems
below show that it is not implied by signature validity and that adding it
makes the attribution claim exact.

Separately, `ChannelAnnellation.node1 : NodeId` is an opaque graph identifier
and `nodeKey1 : PubKey` is a BOLT 7 wire key; wave A has no map between them.
`KeyAttribution` is the required external check, and
`signature_valid_not_key_attribution` shows that announcement signature
validity alone does not imply it. -/

/-- The extra admission check for `channel_update`: additionally require that
`u.signingKey` is one of the two node keys announced for `u.shortChannelId`.

This is exactly the BOLT 7 rule ("the `node_id` used to verify a
`channel_update` is taken from the matching `channel_announcement`") that wave
A's `acceptChannelUpdate` omits. -/
noncomputable def admitUpdateAttributed (verify : SigVerifier) (s : GossipState)
    (u : ChannelUpdate) : GossipState :=
  if u.signatureValid verify ∧ updateKeyAnnounced s u then s.applyUpdate u else s

/-- **The required admission check is sufficient.**  Any change made by
`admitUpdateAttributed` has both a verifying signature and an announced
signing key. -/
theorem admitUpdateAttributed_change_requires (verify : SigVerifier)
    (s : GossipState) (u : ChannelUpdate)
    (h : admitUpdateAttributed verify s u ≠ s) :
    u.signatureValid verify ∧ updateKeyAnnounced s u := by
  apply Classical.byContradiction
  intro hcon
  apply h
  rw [admitUpdateAttributed, ite_eq_right]
  intro hboth
  exact hcon ⟨hboth.1, hboth.2⟩

/-- **Signature-only admission is strictly weaker than key attribution.**
With an always-accepting verifier and an empty store, a `channel_update` whose
`signingKey` was never announced is accepted and changes the store.  This is
the mechanised G19 gap; the fix is the `updateKeyAnnounced` conjunct in
`admitUpdateAttributed`, not a larger proof about `acceptChannelUpdate`. -/
theorem g19_signature_only_gap :
    ∃ (verify : SigVerifier) (s : GossipState) (u : ChannelUpdate),
      acceptChannelUpdate verify s u ≠ s ∧ ¬ updateKeyAnnounced s u := by
  refine ⟨acceptingVerifier, emptyStore, sampleUpdate, ?_, sampleUpdate_unannounced⟩
  intro h
  have hu := congrArg GossipState.updates h
  simp [acceptChannelUpdate, GossipState.applyUpdate,
    GossipState.latestUpdateTimestamp, latestTimestamp, emptyStore, sampleUpdate,
    ChannelUpdate.signatureValid, signatureValid, acceptingVerifier] at hu

/-- **The required check rejects the same update.**  With the attributed
admission step the G19 witness is a no-op, because no announcement supplies
its signing key. -/
theorem g19_attributed_admission_rejects :
    ∃ (verify : SigVerifier) (s : GossipState) (u : ChannelUpdate),
      ¬ updateKeyAnnounced s u ∧ admitUpdateAttributed verify s u = s := by
  refine ⟨acceptingVerifier, emptyStore, sampleUpdate,
    sampleUpdate_unannounced, ?_⟩
  rw [admitUpdateAttributed, ite_eq_right]
  exact fun h => sampleUpdate_unannounced h.2

/-- External map from graph node identifiers to BOLT 7 public keys.  Wave A
does not provide one; a production admission path must. -/
def KeyAttribution (nodeKeyOf : NodeId → PubKey) (a : ChannelAnnellation) : Prop :=
  nodeKeyOf a.node1 = a.nodeKey1 ∧ nodeKeyOf a.node2 = a.nodeKey2

/-- **Announcement signature validity does not attribute keys to graph
nodes.**  Two independent fields (`node1 : NodeId`, `nodeKey1 : PubKey`) mean
that a verifying announcement can name a graph node that is not the owner of
the verifying key.  The catalog claim is about the signatures, not about this
link; closing the link needs the extra `KeyAttribution` check. -/
theorem signature_valid_not_key_attribution :
    ∃ (verify : SigVerifier) (nodeKeyOf : NodeId → PubKey)
      (a : ChannelAnnellation),
      a.signaturesValid verify ∧ ¬ KeyAttribution nodeKeyOf a := by
  refine ⟨acceptingVerifier, fun _ => zeroKey, sampleAnnouncement,
    sampleAnnouncement_valid, ?_⟩
  rintro ⟨_, h2⟩
  have hb := congrArg PubKey.bytes h2
  have hs := congrArg ByteArray.size hb
  have hodd : (ByteArray.mk #[0]).size = 1 := by decide
  simp [sampleAnnouncement, zeroKey, oddKey, hodd] at hs

end LnLean.Proofs.Routing.GossipTargets
