import LnLean.Routing.Gossip
import LnLean.Routing.Laws
import LnLean.Proofs.Routing.GossipProps

/-!
# F06 — Gossip positive-capacity admission

English claim of this module:

* BOLT 7 defines a public channel's `capacity` as the value of its funding
  output.  On Bitcoin L1 a funding output is nonzero, so every accepted
  `channel_announcement` must carry a *positive* capacity.  Wave A stores
  `capacitySat : Nat` without that invariant, and `GossipProps.bindChannel`
  copies the field unchanged (`LN-GOSSIP-002` / `LN-GOSSIP-CAP`).
* `positiveCapacity` names the missing admission condition on a capacity
  in satoshis.  `bindChannelPositive` is `bindChannel` gated by that check:
  it is the reusable admission rule, returning `none` for a zero-capacity
  announcement even when all four signatures verify.
* Every successful `bindChannelPositive` has `0 < capacitySat`
  (`bindChannelPositive_capacity_pos`), and the binding retains the
  announced `short_channel_id` and node endpoints
  (`bindChannelPositive_binds`).
* Positivity propagates through the graph projection:
  `graphPositiveCapacity` is preserved by `Graph.addEdge`, by
  `GossipProps.viewGraph`, by `ChannelView.applyUpdate`, and by a full
  `GossipNetwork.applyMessage` step.  A positive admitted binding therefore
  materialises into a graph whose edges all have positive capacity.
* The wave-A unconditional statement is **false** as written: a
  zero-capacity announcement with an always-accepting verifier binds
  successfully.  That faithful statement is therefore kept below as an
  explicitly marked open obligation, next to a mechanised zero-capacity
  counterexample and a proof that the new admission gate rejects exactly
  that announcement.

BOLT sections:

* BOLT 7, "The `channel_announcement` Message": the `capacity` field is the
  funding output value; a receiver validates the funding outpoint.
* BOLT 7, "Pseudo-Descriptions" / "Updating the gossip store": a received
  announcement is checked before it is entered into the store.

What is **not** modelled:

* The Bitcoin L1 check that the funding outpoint exists, is unspent, and has
  the announced value.  `positiveCapacity` is the arithmetic shadow of that
  check, not a substitute for UTXO validation.
* Direction-keyed channel stores, chain-hash filtering, and signature
  unforgeability (assumptions C3/C4 in `docs/ASSUMPTIONS.md`).  A verifier is
  still an arbitrary parameter; `bindChannelPositive` only adds the capacity
  gate.
-/

namespace LnLean.Proofs.ModelHardening.F06

open LnLean.Routing
open LnLean.Routing.GossipProps

set_option autoImplicit false

/-! ## The missing predicate -/

/-- BOLT 7's funding-value condition, as a reusable predicate: a capacity in
satoshis is positive.  A zero satoshi funding output is not a channel.

`abbrev` rather than `def` so that `Decidable` instance search sees through
the predicate at every admission use site. -/
abbrev positiveCapacity (capacitySat : Nat) : Prop :=
  0 < capacitySat

/-- An announcement satisfies the positive-capacity condition. -/
def announcementHasPositiveCapacity (a : ChannelAnnellation) : Prop :=
  positiveCapacity a.capacitySat

/-- A bound channel satisfies the positive-capacity condition. -/
def bindingHasPositiveCapacity (b : ChannelBinding) : Prop :=
  positiveCapacity b.capacitySat

/-- A materialised graph every of whose edges has positive capacity. -/
def graphPositiveCapacity (g : Graph) : Prop :=
  ∀ e ∈ g.edges, positiveCapacity e.capacitySat

/-- A list of channel views every of whose entries has positive capacity. -/
def viewsPositiveCapacity (vs : List ChannelView) : Prop :=
  ∀ v ∈ vs, positiveCapacity v.capacitySat

/-! ## Positive-capacity admission -/

/-- The positive-capacity admission gate around `GossipProps.bindChannel`.

BOLT 7's funding-value check is applied *before* the signature-checked bind:
a zero-capacity announcement is rejected even if all four signatures verify.
This is the smallest model repair for `LN-GOSSIP-002`; the wave-A
`bindChannel` is left untouched (model files are read-only in this wave). -/
noncomputable def bindChannelPositive (verify : SigVerifier)
    (a : ChannelAnnellation) : Option ChannelBinding :=
  if positiveCapacity a.capacitySat then bindChannel verify a else none

/-- **Admission soundness.**  A successful positive-capacity bind is exactly
a successful wave-A bind of an announcement whose capacity is positive. -/
theorem bindChannelPositive_sound {verify : SigVerifier}
    {a : ChannelAnnellation} {b : ChannelBinding}
    (h : bindChannelPositive verify a = some b) :
    positiveCapacity a.capacitySat ∧ bindChannel verify a = some b := by
  unfold bindChannelPositive at h
  split at h
  · rename_i hcap
    exact ⟨hcap, h⟩
  · simp at h

/-- Characterisation of the admission gate: it succeeds iff the announced
capacity is positive and the underlying bind succeeds. -/
theorem bindChannelPositive_eq_some_iff {verify : SigVerifier}
    {a : ChannelAnnellation} {b : ChannelBinding} :
    bindChannelPositive verify a = some b ↔
      positiveCapacity a.capacitySat ∧ bindChannel verify a = some b := by
  unfold bindChannelPositive
  by_cases hcap : positiveCapacity a.capacitySat
  · rw [ite_eq_left hcap]
    exact ⟨fun hb => ⟨hcap, hb⟩, fun hb => hb.2⟩
  · rw [ite_eq_right hcap]
    exact ⟨fun hb => by simp at hb, fun hb => absurd hb.1 hcap⟩

/-- On a positive-capacity announcement the gate is the wave-A bind. -/
theorem bindChannelPositive_eq_bindChannel_of_positive {verify : SigVerifier}
    {a : ChannelAnnellation} (h : positiveCapacity a.capacitySat) :
    bindChannelPositive verify a = bindChannel verify a := by
  unfold bindChannelPositive
  rw [ite_eq_left h]

/-- A non-positive announcement is rejected by the gate. -/
theorem bindChannelPositive_none_of_not_positive {verify : SigVerifier}
    {a : ChannelAnnellation} (h : ¬ positiveCapacity a.capacitySat) :
    bindChannelPositive verify a = none := by
  unfold bindChannelPositive
  rw [ite_eq_right h]

/-- **Positive-capacity preservation.**  Every successful positive-capacity
bind has `0 < capacitySat`.  This is the unconditional form of the target
obligation for the repaired admission rule. -/
theorem bindChannelPositive_capacity_pos {verify : SigVerifier}
    {a : ChannelAnnellation} {b : ChannelBinding}
    (h : bindChannelPositive verify a = some b) :
    positiveCapacity b.capacitySat := by
  have hs := bindChannelPositive_sound h
  have hcap : positiveCapacity a.capacitySat := hs.1
  rw [GossipProps.bindChannel_capacitySat hs.2]
  exact hcap

/-- The gate preserves the announced binding: same `short_channel_id` and
same endpoint node ids. -/
theorem bindChannelPositive_binds {verify : SigVerifier}
    {a : ChannelAnnellation} {b : ChannelBinding}
    (h : bindChannelPositive verify a = some b) :
    b.scid = a.shortChannelId ∧ b.node1 = a.node1 ∧ b.node2 = a.node2 :=
  GossipProps.bindChannel_binds (bindChannelPositive_sound h).2

/-- The gate is still signature-gated: every successful bind entails the
four BOLT 7 signature predicates. -/
theorem bindChannelPositive_requires_signature {verify : SigVerifier}
    {a : ChannelAnnellation} {b : ChannelBinding}
    (h : bindChannelPositive verify a = some b) :
    a.signaturesValid verify :=
  GossipProps.bindChannel_requires_signature (bindChannelPositive_sound h).2

/-- Conditional form for the *unchanged* wave-A `bindChannel`: an announcement
with positive capacity yields a positive binding.  This isolates the missing
check without adding hypotheses to the code path. -/
theorem bindChannel_capacity_pos_of_announced {verify : SigVerifier}
    {a : ChannelAnnellation} {b : ChannelBinding}
    (h : bindChannel verify a = some b)
    (hcap : positiveCapacity a.capacitySat) :
    positiveCapacity b.capacitySat := by
  rw [GossipProps.bindChannel_capacitySat h]
  exact hcap

/-! ## Propagation to the routing graph -/

/-- The empty graph has positive capacity vacuously. -/
theorem graphPositiveCapacity_empty : graphPositiveCapacity Graph.empty := by
  intro e he
  simp [Graph.empty] at he

/-- Adding an edge with positive capacity preserves the graph invariant. -/
theorem graphPositiveCapacity_addEdge (g : Graph) (e : ChannelEdge)
    (hg : graphPositiveCapacity g) (he : positiveCapacity e.capacitySat) :
    graphPositiveCapacity (g.addEdge e) := by
  intro x hx
  simp only [Graph.addEdge, List.mem_cons] at hx
  rcases hx with rfl | hx
  · exact he
  · exact hg x hx

/-- **Materialisation propagates positivity.**  If every view is positive,
every edge of the graph projection is positive. -/
theorem viewGraph_positiveCapacity {vs : List ChannelView}
    (h : viewsPositiveCapacity vs) :
    graphPositiveCapacity (viewGraph vs) := by
  intro e he
  have he' : e ∈ vs.map ChannelView.edge := he
  rcases List.mem_map.mp he' with ⟨v, hv, rfl⟩
  exact h v hv

/-- Inverting the projection: positivity of a materialised graph implies
positivity of every stored view. -/
theorem viewGraph_positiveCapacity_inv {vs : List ChannelView}
    (h : graphPositiveCapacity (viewGraph vs)) :
    viewsPositiveCapacity vs := by
  intro v hv
  have hmem : v.edge ∈ (viewGraph vs).edges := by
    show v.edge ∈ vs.map ChannelView.edge
    exact List.mem_map.mpr ⟨v, hv, rfl⟩
  exact h v.edge hmem

/-- `ChannelView.applyUpdate` never changes `capacitySat`, so it preserves
positivity. -/
theorem applyUpdate_positiveCapacity (v : ChannelView) (u : ChannelUpdate)
    (hv : positiveCapacity v.capacitySat) :
    positiveCapacity (v.applyUpdate u).capacitySat := by
  rw [ChannelView.applyUpdate_capacitySat]
  exact hv

/-- A `channel_update` applied to every view preserves graph positivity. -/
theorem viewGraph_positiveCapacity_after_update {vs : List ChannelView}
    (h : viewsPositiveCapacity vs) (u : ChannelUpdate) :
    graphPositiveCapacity (viewGraph (vs.map fun v => v.applyUpdate u)) := by
  apply viewGraph_positiveCapacity
  intro v hv
  rcases List.mem_map.mp hv with ⟨w, hw, rfl⟩
  exact applyUpdate_positiveCapacity w u (h w hw)

/-- The directed edge of a positive binding has positive capacity. -/
theorem binding_edge_positiveCapacity (b : ChannelBinding)
    (h : positiveCapacity b.capacitySat) :
    positiveCapacity b.edge.capacitySat := by
  simpa [ChannelBinding.edge] using h

/-- **An admitted binding materialises into a positive graph.** -/
theorem materialised_binding_positiveCapacity {verify : SigVerifier}
    {a : ChannelAnnellation} {b : ChannelBinding}
    (h : bindChannelPositive verify a = some b) :
    graphPositiveCapacity (Graph.empty.addEdge b.edge) := by
  apply graphPositiveCapacity_addEdge
  · exact graphPositiveCapacity_empty
  · exact binding_edge_positiveCapacity b (bindChannelPositive_capacity_pos h)

/-- Combined materialisation: a positive admitted announcement with distinct
endpoints and a valid `short_channel_id` produces a graph which is both
well formed (wave-A graph invariant) and capacity-positive. -/
theorem announcement_materialises_positiveCapacity (verify : SigVerifier)
    (a : ChannelAnnellation) (b : ChannelBinding)
    (hbind : bindChannelPositive verify a = some b)
    (hne : a.node1 ≠ a.node2) (hscid : a.shortChannelId.Valid) :
    graphWellFormed (Graph.empty.addEdge b.edge) ∧
      graphPositiveCapacity (Graph.empty.addEdge b.edge) := by
  constructor
  · exact GossipProps.announcement_materialises_wellFormed verify a b
      (bindChannelPositive_sound hbind).2 hne hscid
  · exact materialised_binding_positiveCapacity hbind

/-- **A full network step preserves graph positivity.**  Since
`GossipNetwork.applyMessage` changes channel data only through
`ChannelView.applyUpdate` (which fixes `capacitySat`), the invariant proved
on the view list lifts to the routing graph of the network state. -/
theorem applyMessage_graph_positiveCapacity (verify : SigVerifier)
    (ns : GossipNetwork) (m : GossipMessage)
    (h : graphPositiveCapacity ns.graph) :
    graphPositiveCapacity (ns.applyMessage verify m).graph := by
  have hv : viewsPositiveCapacity ns.views :=
    viewGraph_positiveCapacity_inv (by simpa [GossipNetwork.graph] using h)
  cases m with
  | channelAnnouncement a =>
      simpa [GossipNetwork.applyMessage, GossipNetwork.graph] using h
  | channelUpdate u =>
      by_cases hsig : u.signatureValid verify
      · have hstep : (ns.applyMessage verify (.channelUpdate u)).graph =
            viewGraph (ns.views.map fun v => v.applyUpdate u) := by
          simp [GossipNetwork.applyMessage, GossipNetwork.graph, hsig]
        rw [hstep]
        exact viewGraph_positiveCapacity_after_update hv u
      · have hstep : (ns.applyMessage verify (.channelUpdate u)).graph = ns.graph := by
          simp [GossipNetwork.applyMessage, GossipNetwork.graph, hsig]
        rw [hstep]
        exact h
  | nodeAnnouncement n =>
      simpa [GossipNetwork.applyMessage, GossipNetwork.graph] using h

/-! ## The zero-capacity counterexample

The wave-A `bindChannel` has no capacity check.  The following witnesses
make the gap exact: all four signatures verify, the announcement binds, and
the resulting capacity is zero.  The repaired gate rejects the same
announcement. -/

private def emptySig : GossipSignature := ⟨ByteArray.empty⟩

private def emptyKey : PubKey := ⟨ByteArray.empty⟩

private def zeroScid : ShortChannelId := ⟨0, 0, 0⟩

/-- A verifier that accepts every signature.  Used only to exhibit the
missing admission check, never as a proof assumption. -/
private def acceptAll : SigVerifier := fun _ _ _ => true

private def zeroCapacityAnn : ChannelAnnellation :=
  { shortChannelId := zeroScid
    node1 := ⟨0⟩
    node2 := ⟨1⟩
    nodeKey1 := emptyKey
    nodeKey2 := emptyKey
    bitcoinKey1 := emptyKey
    bitcoinKey2 := emptyKey
    capacitySat := 0
    digest := ByteArray.empty
    nodeSignature1 := emptySig
    nodeSignature2 := emptySig
    bitcoinSignature1 := emptySig
    bitcoinSignature2 := emptySig }

private def zeroCapacityBinding : ChannelBinding :=
  { scid := zeroScid
    node1 := ⟨0⟩
    node2 := ⟨1⟩
    nodeKey1 := emptyKey
    nodeKey2 := emptyKey
    capacitySat := 0 }

private theorem zeroCapacityAnn_signaturesValid :
    zeroCapacityAnn.signaturesValid acceptAll := by
  simp [ChannelAnnellation.signaturesValid, signatureValid, acceptAll]

private theorem bind_zeroCapacityAnn :
    bindChannel acceptAll zeroCapacityAnn = some zeroCapacityBinding := by
  unfold bindChannel
  rw [ite_eq_left zeroCapacityAnn_signaturesValid]
  rfl

/-- **Mechanised zero-capacity counterexample.**  The wave-A admission rule
binds an announcement whose funding capacity is zero. -/
theorem zero_capacity_bind_counterexample :
    ∃ (verify : SigVerifier) (a : ChannelAnnellation) (b : ChannelBinding),
      bindChannel verify a = some b ∧ b.capacitySat = 0 :=
  ⟨acceptAll, zeroCapacityAnn, zeroCapacityBinding, bind_zeroCapacityAnn, rfl⟩

/-- **The repaired gate rejects the counterexample.**  The same announcement
that wave-A `bindChannel` accepts is rejected by `bindChannelPositive`. -/
theorem positive_admission_rejects_zero_capacity :
    ∃ (verify : SigVerifier) (a : ChannelAnnellation),
      bindChannel verify a ≠ none ∧ bindChannelPositive verify a = none := by
  refine ⟨acceptAll, zeroCapacityAnn, ?_, ?_⟩
  · rw [bind_zeroCapacityAnn]
    simp
  · apply bindChannelPositive_none_of_not_positive
    simp [zeroCapacityAnn, positiveCapacity]

/-- **`LN-GOSSIP-002`, faithful unconditional statement (false in wave A).**
A successful `bindChannel` does *not* imply a positive capacity: the
announcement itself carries no admissibility invariant and the admission
path does not check it.  The counterexample above is mechanised, and
`bindChannelPositive_capacity_pos` proves the repaired statement. -/
theorem bindChannel_capacity_positive {verify : SigVerifier}
    {a : ChannelAnnellation} {b : ChannelBinding}
    (h : bindChannel verify a = some b) : positiveCapacity b.capacitySat := by
  -- OBLIGATION: LN-WF-F06
  sorry

end LnLean.Proofs.ModelHardening.F06
