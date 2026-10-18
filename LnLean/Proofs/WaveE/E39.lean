import LnLean.Routing.Gossip
import LnLean.Routing.Laws
import LnLean.Proofs.Routing.GossipProps

/-!
# LnLean.Proofs.WaveE.E39

Wave-E lane E39: BOLT 7 gossip capacity positivity (`LN-GOSSIP-002`).

BOLT 7 defines a channel's `capacity` as the value of the funding output
(`refs/bolts/07-routing-gossip.md`, "The `channel_announcement` Message").
A real Bitcoin funding output has a positive value, so every accepted
`channel_announcement` should bind a positive capacity.

The wave-A model stores `ChannelAnnellation.capacitySat : Nat` without an
invariant and `GossipProps.bindChannel` copies it unchanged.  Therefore the
unconditional catalog statement

> every successful `bindChannel` produces a binding with `0 < capacitySat`

is false: the zero-capacity announcement below binds successfully under an
accepting verifier.  This module does not hide that gap.  Instead it:

* defines the positive-capacity admission predicate `positiveCapacity` and
  the signature-and-capacity admission `admitsAnnouncement`;
* defines the guarded binding `bindChannelPositive`, which returns a binding
  only when both the four signature predicates and positivity hold;
* proves that a successful guarded binding has positive capacity, and that
  the guarded and unguarded bindings agree exactly on admitted announcements
  (`waveE_e39_bindChannelPositive_some_iff`);
* proves the exact conditional form of `LN-GOSSIP-002`: for an unguarded
  binding, `0 < b.capacitySat ↔ 0 < a.capacitySat`;
* mechanises the zero-capacity counterexample and shows that the guarded
  admission rejects that same announcement (`waveE_e39_zero_capacity_counterexample`);
* records that positivity is stable under `channel_update` application at
  the materialised-view and edge level.

Every proof in this file is closed using the standard Lean kernel; the
checked theorems depend only on `propext`, `Classical.choice`, and
`Quot.sound` (verified with `#print axioms`).  Cryptographic acceptance is
only the abstract `SigVerifier`; no unforgeability claim is made.

BOLT sections:

* BOLT 7, "The `channel_announcement` Message": `capacity` is the funding
  output value and is checked against the on-chain outpoint.
* BOLT 7, "Pseudo-Descriptions": signature-checked updates to the gossip
  store.

`rust-lightning` anchors (pinned commit
`fe4900930c6bd5786ec4203274d7cf312776a5a6`):

* `lightning/src/routing/gossip.rs:1012` — `ChannelInfo.capacity_sats`.
* `lightning/src/routing/gossip.rs:1973` — `update_channel_from_announcement`
  (the announcement is admitted before a `ChannelInfo` is created).
-/

-- OBLIGATION: LN-WE-E39

namespace LnLean.Proofs.WaveE.E39

open LnLean.Routing
open LnLean.Routing.GossipProps
open Classical

set_option autoImplicit false

/-! ## Positive-capacity admission -/

/-- BOLT 7 capacity positivity: the funding output value is positive. -/
def positiveCapacity (a : ChannelAnnellation) : Prop :=
  0 < a.capacitySat

/-- The binding-level form of capacity positivity. -/
def positiveBindingCapacity (b : ChannelBinding) : Prop :=
  0 < b.capacitySat

/-- A `channel_announcement` is admitted only when all four BOLT 7 signatures
verify *and* the announced capacity is positive.  This is the admission
check that wave A omits. -/
def admitsAnnouncement (verify : SigVerifier) (a : ChannelAnnellation) : Prop :=
  a.signaturesValid verify ∧ positiveCapacity a

theorem waveE_e39_admitsAnnouncement_iff {verify : SigVerifier}
    {a : ChannelAnnellation} :
    admitsAnnouncement verify a ↔ a.signaturesValid verify ∧ 0 < a.capacitySat :=
  Iff.rfl

/-- Admission entails the announced capacity is positive. -/
theorem waveE_e39_admits_positive {verify : SigVerifier}
    {a : ChannelAnnellation} (h : admitsAnnouncement verify a) :
    0 < a.capacitySat :=
  h.2

/-- Admission entails all four signature predicates. -/
theorem waveE_e39_admits_signatures {verify : SigVerifier}
    {a : ChannelAnnellation} (h : admitsAnnouncement verify a) :
    a.signaturesValid verify :=
  h.1

/-- Guarded binding: the wave-A `bindChannel` composed with the
positive-capacity admission.  A non-admitted announcement yields `none`
instead of a zero-capacity binding. -/
noncomputable def bindChannelPositive (verify : SigVerifier)
    (a : ChannelAnnellation) : Option ChannelBinding :=
  if admitsAnnouncement verify a then bindChannel verify a else none

/-- On an admitted announcement the guarded binder is exactly the wave-A
binder. -/
theorem waveE_e39_bindChannelPositive_eq_of_admits
    (verify : SigVerifier) (a : ChannelAnnellation)
    (h : admitsAnnouncement verify a) :
    bindChannelPositive verify a = bindChannel verify a := by
  unfold bindChannelPositive
  rw [ite_eq_left h]

/-- A non-admitted announcement is rejected by the guarded binder. -/
theorem waveE_e39_bindChannelPositive_none_of_not_admits
    (verify : SigVerifier) (a : ChannelAnnellation)
    (h : ¬ admitsAnnouncement verify a) :
    bindChannelPositive verify a = none := by
  unfold bindChannelPositive
  rw [ite_eq_right h]

/-- **Characterisation of guarded binding.**  The positive-capacity binder
returns `b` exactly when the announcement is admitted and the unguarded
binder also returns `b`.  The only difference from `bindChannel` is the
positivity gate. -/
theorem waveE_e39_bindChannelPositive_some_iff
    (verify : SigVerifier) (a : ChannelAnnellation) (b : ChannelBinding) :
    bindChannelPositive verify a = some b ↔
      admitsAnnouncement verify a ∧ bindChannel verify a = some b := by
  unfold bindChannelPositive
  by_cases h : admitsAnnouncement verify a
  · rw [ite_eq_left h]
    exact ⟨fun hb => ⟨h, hb⟩, fun hb => hb.2⟩
  · rw [ite_eq_right h]
    exact ⟨fun hb => absurd hb (by simp), fun hb => absurd hb.1 h⟩

/-! ## Successful binding preserves positivity -/

/-- **Positive-capacity preservation.**  A successful guarded binding has a
positive capacity. -/
theorem waveE_e39_positive_binding_capacity {verify : SigVerifier}
    {a : ChannelAnnellation} {b : ChannelBinding}
    (h : bindChannelPositive verify a = some b) :
    0 < b.capacitySat := by
  have hadm : admitsAnnouncement verify a :=
    (waveE_e39_bindChannelPositive_some_iff verify a b).mp h |>.1
  have hbind : bindChannel verify a = some b :=
    (waveE_e39_bindChannelPositive_some_iff verify a b).mp h |>.2
  exact bindChannel_capacity_positive_of_announced hbind hadm.2

/-- A successful guarded binding entails the announced signatures. -/
theorem waveE_e39_positive_binding_signatures {verify : SigVerifier}
    {a : ChannelAnnellation} {b : ChannelBinding}
    (h : bindChannelPositive verify a = some b) :
    a.signaturesValid verify :=
  (waveE_e39_bindChannelPositive_some_iff verify a b).mp h |>.1 |>.1

/-- A successful guarded binding entails the admission predicate. -/
theorem waveE_e39_positive_binding_admitted {verify : SigVerifier}
    {a : ChannelAnnellation} {b : ChannelBinding}
    (h : bindChannelPositive verify a = some b) :
    admitsAnnouncement verify a :=
  (waveE_e39_bindChannelPositive_some_iff verify a b).mp h |>.1

/-- A successful guarded binding returns exactly the announced identity and
capacity.  In particular, admission does not silently rewrite the binding. -/
theorem waveE_e39_positive_binding_fields {verify : SigVerifier}
    {a : ChannelAnnellation} {b : ChannelBinding}
    (h : bindChannelPositive verify a = some b) :
    b.scid = a.shortChannelId ∧ b.node1 = a.node1 ∧ b.node2 = a.node2 ∧
      b.capacitySat = a.capacitySat := by
  have hbind : bindChannel verify a = some b :=
    (waveE_e39_bindChannelPositive_some_iff verify a b).mp h |>.2
  exact ⟨(bindChannel_binds hbind).1, (bindChannel_binds hbind).2.1,
    (bindChannel_binds hbind).2.2, bindChannel_capacitySat hbind⟩

/-- **Exact conditional form of `LN-GOSSIP-002`.**  For any successful
unguarded binding, capacity positivity of the binding is equivalent to
capacity positivity of the announcement.  The missing admission is exactly
`0 < a.capacitySat`. -/
theorem waveE_e39_bindChannel_capacity_pos_iff
    {verify : SigVerifier} {a : ChannelAnnellation} {b : ChannelBinding}
    (h : bindChannel verify a = some b) :
    0 < b.capacitySat ↔ 0 < a.capacitySat := by
  rw [bindChannel_capacitySat h]

/-- The conditional theorem exhibited by the catalog: a positive announced
capacity makes every successful binding positive. -/
theorem waveE_e39_bindChannel_capacity_positive_of_announced
    {verify : SigVerifier} {a : ChannelAnnellation} {b : ChannelBinding}
    (h : bindChannel verify a = some b) (hcap : 0 < a.capacitySat) :
    0 < b.capacitySat :=
  (waveE_e39_bindChannel_capacity_pos_iff h).mpr hcap

/-! ## The zero-capacity counterexample -/

private def acceptingVerifier : SigVerifier := fun _ _ _ => true

private def emptySignature : GossipSignature := ⟨ByteArray.empty⟩

private def emptyKey : PubKey := ⟨ByteArray.empty⟩

private def zeroScid : ShortChannelId := ⟨0, 0, 0⟩

/-- A BOLT 7 `channel_announcement` whose advertised capacity is zero.  The
wave-A model permits this: `capacitySat` is an unconstrained `Nat`. -/
private def zeroCapacityAnnouncement : ChannelAnnellation :=
  { shortChannelId := zeroScid
    node1 := ⟨0⟩
    node2 := ⟨1⟩
    nodeKey1 := emptyKey
    nodeKey2 := emptyKey
    bitcoinKey1 := emptyKey
    bitcoinKey2 := emptyKey
    capacitySat := 0
    digest := ByteArray.empty
    nodeSignature1 := emptySignature
    nodeSignature2 := emptySignature
    bitcoinSignature1 := emptySignature
    bitcoinSignature2 := emptySignature }

/-- The binding extracted from `zeroCapacityAnnouncement`. -/
private def zeroCapacityBinding : ChannelBinding :=
  { scid := zeroScid
    node1 := ⟨0⟩
    node2 := ⟨1⟩
    nodeKey1 := emptyKey
    nodeKey2 := emptyKey
    capacitySat := 0 }

private theorem zeroCapacityAnnouncement_signatures :
    zeroCapacityAnnouncement.signaturesValid acceptingVerifier := by
  unfold ChannelAnnellation.signaturesValid
  simp [signatureValid, acceptingVerifier]

private theorem zeroCapacity_bindChannel :
    bindChannel acceptingVerifier zeroCapacityAnnouncement =
      some zeroCapacityBinding := by
  unfold bindChannel
  rw [ite_eq_left zeroCapacityAnnouncement_signatures]
  rfl

/-- **The unguarded wave-A binder accepts a zero-capacity channel.**  This is
the mechanised witness that the unconditional `LN-GOSSIP-002` statement is
false for the current model. -/
theorem waveE_e39_zero_capacity_binds :
    ∃ (verify : SigVerifier) (a : ChannelAnnellation) (b : ChannelBinding),
      bindChannel verify a = some b ∧ b.capacitySat = 0 := by
  exact ⟨acceptingVerifier, zeroCapacityAnnouncement, zeroCapacityBinding,
    zeroCapacity_bindChannel, rfl⟩

/-- **The unconditional catalog claim is false.**  No theorem can prove
capacity positivity for `bindChannel` alone without adding an admission
check, because an accepting verifier binds a zero-capacity announcement. -/
theorem waveE_e39_unconditional_capacity_positive_false :
    ¬ (∀ (verify : SigVerifier) (a : ChannelAnnellation)
        (b : ChannelBinding), bindChannel verify a = some b →
          0 < b.capacitySat) := by
  intro hall
  have hpos := hall acceptingVerifier zeroCapacityAnnouncement
    zeroCapacityBinding zeroCapacity_bindChannel
  have hz : zeroCapacityBinding.capacitySat = 0 := rfl
  rw [hz] at hpos
  exact Nat.lt_irrefl 0 hpos

/-- A zero-capacity announcement is not admitted. -/
theorem waveE_e39_zero_capacity_not_admitted :
    ¬ admitsAnnouncement acceptingVerifier zeroCapacityAnnouncement := by
  rintro ⟨_, hpos⟩
  exact Nat.lt_irrefl 0 hpos

/-- **The positive-capacity admission rejects the zero-capacity channel.** -/
theorem waveE_e39_zero_capacity_admission_rejected :
    bindChannelPositive acceptingVerifier zeroCapacityAnnouncement = none :=
  waveE_e39_bindChannelPositive_none_of_not_admits acceptingVerifier
    zeroCapacityAnnouncement waveE_e39_zero_capacity_not_admitted

/-- **Mechanised counterexample plus rejection.**  One and the same
announcement binds successfully through wave A's `bindChannel` with capacity
zero, while the positive-capacity admission turns it into `none`. -/
theorem waveE_e39_zero_capacity_counterexample :
    ∃ (verify : SigVerifier) (a : ChannelAnnellation) (b : ChannelBinding),
      bindChannel verify a = some b ∧ b.capacitySat = 0 ∧
        bindChannelPositive verify a = none := by
  exact ⟨acceptingVerifier, zeroCapacityAnnouncement, zeroCapacityBinding,
    zeroCapacity_bindChannel, rfl, waveE_e39_zero_capacity_admission_rejected⟩

/-- The guarded binder rejects exactly the zero-capacity witness while the
unguarded binder accepts it. -/
theorem waveE_e39_guarded_differs_from_unguarded :
    bindChannel acceptingVerifier zeroCapacityAnnouncement =
        some zeroCapacityBinding ∧
      bindChannelPositive acceptingVerifier zeroCapacityAnnouncement = none :=
  ⟨zeroCapacity_bindChannel, waveE_e39_zero_capacity_admission_rejected⟩

/-! ## Preservation into the routing graph -/

/-- A positively bound channel materialises with positive edge capacity. -/
theorem waveE_e39_positive_binding_edge_capacity {verify : SigVerifier}
    {a : ChannelAnnellation} {b : ChannelBinding}
    (h : bindChannelPositive verify a = some b) :
    0 < (ChannelBinding.edge b).capacitySat := by
  simpa [ChannelBinding.edge] using waveE_e39_positive_binding_capacity h

/-- A positive-capacity channel view keeps its capacity when a
`channel_update` is applied: BOLT 7 updates change fees, CLTV, and the
disable flag, never the funding capacity. -/
theorem waveE_e39_view_capacity_pos_applyUpdate (v : ChannelView)
    (u : ChannelUpdate) (h : 0 < v.capacitySat) :
    0 < (v.applyUpdate u).capacitySat := by
  rw [ChannelView.applyUpdate_capacitySat]
  exact h

/-- The materialised edge of a positive-capacity view has positive capacity,
so positivity established at admission survives the graph projection. -/
theorem waveE_e39_view_edge_capacity_pos (v : ChannelView)
    (h : 0 < v.capacitySat) :
    0 < v.edge.capacitySat := by
  simpa [ChannelView.edge] using h

end LnLean.Proofs.WaveE.E39
