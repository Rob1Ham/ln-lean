import LnLean.Proofs.Routing.GossipRawRefinementTargets

/-!
# H41 — supersession/rotation preservation across gossip epochs (`RT-01`, `RT-02`)

**English claim.**  The canonical gossip transition
(`admitGossipCanonical`, wave 6) and its store refinement
(`applyGossipCanonicalStore`, wave 7) are *admission* policies.  Neither has an
explicit epoch or generation counter, so "what happens in the next epoch?" is
not yet a Lean statement.  This module adds the smallest faithful model that
makes it one:

* `EpochNetwork` wraps a `CanonicalNetwork` with a `Nat` epoch counter.
  `epochAdmit` applies the unchanged canonical admission and increments the
  counter; `epochAdvance` increments it without a message; `epochRotate` is an
  explicit administrative key-rotation step at an epoch boundary.
* The epoch counter is **not** an admission clock.  `epochAdmit_network_eq`
  and `epoch_admission_epoch_independent` prove that the transition's effect
  is the canonical transition at the current store, independent of the epoch
  value.  The only freshness clocks remain (a) the per-slot timestamp gate
  `UpdateSupersedes` and (b) the raw global `latestUpdateTimestamp`, which
  `epochAdmit_clock_monotone` shows is non-decreasing on the canonical path.
* `ReachableEpoch` closes these three steps from the empty store.
  `reachableEpoch_invariant` proves the full `CanonicalAdmitted` invariant for
  every reachable epoch state, so the canonical reachable invariant is
  preserved across arbitrary epoch boundaries.

The target properties are then proved exactly:

* **Stale announcements/updates remain rejected.**
  `stale_update_not_supersedes` shows an update that is not strictly newer
  than a stored record in its `(short_channel_id, direction)` slot fails the
  supersession gate, hence is a no-op in *every* epoch
  (`stale_update_rejected_in_every_epoch`).  After a successful supersession,
  the older record stays rejected (`canonical_superseded_update_stays_rejected`,
  `epoch_supersession_preserves_stale_rejection`).  A pre-rotation
  announcement carrying the old node key is incompatible with the rotated
  store, hence rejected in every epoch
  (`stale_announcement_rejected_in_every_epoch`).
* **Current keys/announcements survive.**  Rotation keeps every announcement's
  `short_channel_id`, endpoints, and capacity
  (`rotation_preserves_announcement_identity`), and the rotated node's stored
  record carries the new key (`rotation_current_key_survives`); the concrete
  epoch witness re-exhibits both facts (`rotation_witness_*`).
* **The canonical reachable invariant is preserved.**
  `rotateNetwork_preserves_canonicalAdmitted` proves the rotation step
  preserves `CanonicalAdmitted` under the two exact obligations: the rekeyed
  announcements are re-signed (`StoreAnnouncementsValid`) and the stored
  updates are re-attributed/resubmitted
  (`StoreUpdatesDirectionallyAttributed`).  The empty-update corollary needs
  only the re-signing premise.  `reachableEpoch_invariant` lifts this to all
  reachable epoch states.

Clock/admission premises are stated, never hidden:

* `epochAdmit` uses exactly `CanonicalMessageAdmitted`; the epoch value is
  inert (`epoch_admission_epoch_independent`).
* An admitted canonical update requires a strictly newer timestamp in its own
  directional slot (`UpdateSupersedes`), not in the raw global clock; the two
  clocks are compared in the wave-7 boundary
  `canonical_admission_strictly_weaker_than_raw_clock`, retained below.
* The epoch counter does not imply message freshness: a stale message is not
  admitted merely because the epoch advanced
  (`stale_update_rejected_in_every_epoch`).

What is **not** modelled or claimed:

* The epoch counter is a local administrative generation, not a protocol wire
  field, wall-clock time, or BOLT 7 timestamp.
* Rotation is an explicit administrative transition, not a gossip message; it
  is **not** part of `admitGossipCanonical` and does not change the raw
  `applyGossip`.  The change of a registered key still requires re-signing and
  resubmission; `rotation_breaks_update_attribution` (wave 6) remains the
  boundary witness.
* No network dissemination, chain-hash filtering, UTXO confirmation, or
  cryptographic unforgeability is added.  `SigVerifier` stays abstract (C3).

No `sorry`, no `axiom`, no `admit`, no `native_decide`, no `unsafe`,
no `@[implemented_by]`.
-/

namespace LnLean.Proofs.WaveH.H41

open LnLean.Routing
open LnLean.Routing.GossipProps
open LnLean.Proofs.Routing.GossipTargets
open LnLean.Proofs.Routing.GossipAttributionTargets
open LnLean.Proofs.Routing.GossipKeyConsistencyTargets
open LnLean.Proofs.Routing.GossipCanonicalTargets
open LnLean.Proofs.Routing.GossipRawRefinementTargets

set_option autoImplicit false

/-! ## 1. Additive epoch wrapper -/

/-- A canonical network together with a local epoch/generation counter.

The counter is an administrative generation.  It is deliberately *not* fed
into admission; see `epochAdmit_network_eq`. -/
structure EpochNetwork where
  /-- The canonical store, materialised views, and key-registration map. -/
  network : CanonicalNetwork
  /-- Local epoch/generation number. -/
  epoch : Nat

/-- **Canonical admission in an epoch.**  Apply the unchanged wave-6 canonical
transition and advance the epoch counter by one.  A rejected message is still a
delivery: the store is unchanged but the epoch advances. -/
noncomputable def epochAdmit (verify : SigVerifier) (es : EpochNetwork)
    (m : GossipMessage) : EpochNetwork :=
  { network := admitGossipCanonical verify es.network m, epoch := es.epoch + 1 }

/-- Advance the epoch without delivering a message. -/
def epochAdvance (es : EpochNetwork) : EpochNetwork :=
  { es with epoch := es.epoch + 1 }

/-- **Administrative network rotation.**  Rotate the registration of one graph
node and rewrite every stored announcement's key field for that node.  The
view list is untouched (rotation changes keys, not channel identity).  This is
an epoch-boundary operation, not a gossip message. -/
def rotateNetwork (cs : CanonicalNetwork) (n : NodeId) (k : PubKey) :
    CanonicalNetwork :=
  { gossip := rekeyStore cs.gossip n k
    views := cs.views
    nodeKeyOf := rotateNodeKey cs.nodeKeyOf n k }

/-- **Rotation at an epoch boundary.**  The epoch advances by one. -/
def epochRotate (es : EpochNetwork) (n : NodeId) (k : PubKey) :
    EpochNetwork :=
  { network := rotateNetwork es.network n k, epoch := es.epoch + 1 }

@[simp] theorem epochAdmit_network (verify : SigVerifier) (es : EpochNetwork)
    (m : GossipMessage) :
    (epochAdmit verify es m).network = admitGossipCanonical verify es.network m :=
  rfl

@[simp] theorem epochAdmit_epoch (verify : SigVerifier) (es : EpochNetwork)
    (m : GossipMessage) :
    (epochAdmit verify es m).epoch = es.epoch + 1 :=
  rfl

@[simp] theorem epochAdvance_network (es : EpochNetwork) :
    (epochAdvance es).network = es.network :=
  rfl

@[simp] theorem epochAdvance_epoch (es : EpochNetwork) :
    (epochAdvance es).epoch = es.epoch + 1 :=
  rfl

@[simp] theorem epochRotate_network (es : EpochNetwork) (n : NodeId)
    (k : PubKey) :
    (epochRotate es n k).network = rotateNetwork es.network n k :=
  rfl

@[simp] theorem epochRotate_epoch (es : EpochNetwork) (n : NodeId)
    (k : PubKey) :
    (epochRotate es n k).epoch = es.epoch + 1 :=
  rfl

/-! ### Timestamp-clock lemmas (used by epoch admission monotonicity) -/

/-- A fold bounded pointwise by `B` is bounded by `B`. -/
theorem foldl_max_le {l : List ChannelUpdate} {a B : Nat}
    (ha : a ≤ B) (h : ∀ v ∈ l, v.timestamp ≤ B) :
    l.foldl (fun acc v => max acc v.timestamp) a ≤ B := by
  induction l generalizing a with
  | nil => exact ha
  | cons v vs ih =>
      simp only [List.foldl_cons]
      refine ih ?_ ?_
      · exact Nat.max_le.mpr ⟨ha, h v (List.mem_cons_self ..)⟩
      · intro w hw
        exact h w (List.mem_cons_of_mem v hw)

/-- `latestTimestamp` is bounded by any pointwise bound. -/
theorem latestTimestamp_le_of_forall_mem_le {l : List ChannelUpdate} {B : Nat}
    (h : ∀ v ∈ l, v.timestamp ≤ B) : latestTimestamp l ≤ B := by
  unfold latestTimestamp
  exact foldl_max_le (Nat.zero_le B) h

/-- **Supersession preserves the global timestamp clock.**  The canonical
replacement removes only records in the incoming slot, and every removed
record is strictly older than the incoming one by `UpdateSupersedes`. -/
theorem latestTimestamp_insertUpdateCanonical_ge {u : ChannelUpdate}
    {l : List ChannelUpdate} (h : UpdateSupersedes u l) :
    latestTimestamp l ≤ latestTimestamp (insertUpdateCanonical u l) := by
  change latestTimestamp l ≤
    latestTimestamp (u :: l.filter (fun v => decide
      (¬ (v.shortChannelId = u.shortChannelId ∧
        v.direction = u.direction))))
  have hmem : ∀ v ∈ l, v.timestamp ≤
      latestTimestamp (u :: l.filter (fun w => decide
        (¬ (w.shortChannelId = u.shortChannelId ∧
          w.direction = u.direction)))) := by
    intro v hv
    by_cases hsame : v.shortChannelId = u.shortChannelId ∧
        v.direction = u.direction
    · have hlt : v.timestamp < u.timestamp := h v hv hsame.1 hsame.2
      have hu : u.timestamp ≤ latestTimestamp (u :: l.filter (fun w => decide
          (¬ (w.shortChannelId = u.shortChannelId ∧
            w.direction = u.direction)))) :=
        mem_timestamp_le_latest (List.mem_cons_self ..)
      exact Nat.le_of_lt (Nat.lt_of_lt_of_le hlt hu)
    · have hvP : v ∈ l.filter (fun w => decide
          (¬ (w.shortChannelId = u.shortChannelId ∧
            w.direction = u.direction))) :=
        List.mem_filter.mpr ⟨hv, decide_eq_true hsame⟩
      have hle : v.timestamp ≤ latestTimestamp (l.filter (fun w => decide
          (¬ (w.shortChannelId = u.shortChannelId ∧
            w.direction = u.direction)))) :=
        mem_timestamp_le_latest hvP
      have hmono : latestTimestamp (l.filter (fun w => decide
          (¬ (w.shortChannelId = u.shortChannelId ∧
            w.direction = u.direction)))) ≤
          latestTimestamp (u :: l.filter (fun w => decide
            (¬ (w.shortChannelId = u.shortChannelId ∧
              w.direction = u.direction)))) := by
        simp only [latestTimestamp, List.foldl_cons]
        exact foldl_max_mono (l.filter (fun w => decide
          (¬ (w.shortChannelId = u.shortChannelId ∧
            w.direction = u.direction)))) (Nat.zero_le (max 0 u.timestamp))
      exact Nat.le_trans hle hmono
  exact latestTimestamp_le_of_forall_mem_le hmem

/-! ## 2. The epoch counter is not an admission clock -/

/-- **Admission is epoch-independent.**  The epoch value is not inspected by
the canonical gates: two states with the same network admit exactly the same
messages regardless of their epoch counters. -/
theorem epoch_admission_epoch_independent (verify : SigVerifier)
    (cs : CanonicalNetwork) (e₁ e₂ : Nat) (m : GossipMessage) :
    (epochAdmit verify ⟨cs, e₁⟩ m).network =
      (epochAdmit verify ⟨cs, e₂⟩ m).network :=
  rfl

/-- Delivering a message never decreases the gossip timestamp clock.  On the
update branch this uses the per-slot supersession gate, not the epoch
counter. -/
theorem epochAdmit_clock_monotone (verify : SigVerifier) (es : EpochNetwork)
    (m : GossipMessage) :
    es.network.gossip.latestUpdateTimestamp ≤
      (epochAdmit verify es m).network.gossip.latestUpdateTimestamp := by
  rw [epochAdmit_network]
  cases m with
  | channelAnnouncement a =>
      by_cases h : a.signaturesValid verify ∧ a.node1 ≠ a.node2 ∧
          es.network.gossip.CompatibleWithStore a ∧
            UpdatesAuthorizedBy es.network.gossip a
      · rw [admitGossipCanonical_announcement_of_admitted verify es.network a h]
        exact Nat.le_refl _
      · rw [admitGossipCanonical_announcement_of_rejected verify es.network a h]
        exact Nat.le_refl _
  | channelUpdate u =>
      by_cases h : u.signatureValid verify ∧
          es.network.gossip.updateKeyAnnouncedDirectional u ∧
            UpdateSupersedes u es.network.gossip.updates
      · rw [admitGossipCanonical_update_of_admitted verify es.network u h]
        exact latestTimestamp_insertUpdateCanonical_ge h.2.2
      · rw [admitGossipCanonical_update_of_rejected verify es.network u h]
        exact Nat.le_refl _
  | nodeAnnouncement n =>
      by_cases h : n.signatureValid verify
      · rw [admitGossipCanonical_node_of_valid verify es.network n h]
        exact Nat.le_refl _
      · rw [admitGossipCanonical_node_of_invalid verify es.network n h]
        exact Nat.le_refl _

/-- Advancing (or rotating) an epoch leaves the gossip clock unchanged. -/
theorem epochAdvance_clock_eq (es : EpochNetwork) :
    (epochAdvance es).network.gossip.latestUpdateTimestamp =
      es.network.gossip.latestUpdateTimestamp :=
  rfl

/-- Rotation rewrites announcement keys only; the update clock is unchanged. -/
theorem epochRotate_clock_eq (es : EpochNetwork) (n : NodeId) (k : PubKey) :
    (epochRotate es n k).network.gossip.latestUpdateTimestamp =
      es.network.gossip.latestUpdateTimestamp :=
  rfl

/-! ## 3. Timestamp clocks: supersession and stale rejection -/

/-- **Stale gate failure.**  If a stored record in the same directional slot
is at least as new as the candidate, the candidate does not supersede the
slot. -/
theorem stale_update_not_supersedes {u v : ChannelUpdate}
    {l : List ChannelUpdate} (hv : v ∈ l)
    (hscid : v.shortChannelId = u.shortChannelId)
    (hdir : v.direction = u.direction) (hts : u.timestamp ≤ v.timestamp) :
    ¬ UpdateSupersedes u l := by
  intro h
  have hlt := h v hv hscid hdir
  exact Nat.lt_irrefl v.timestamp (Nat.lt_of_lt_of_le hlt hts)

/-- A stale update is a no-op of the canonical transition, in any epoch. -/
theorem admitGossipCanonical_stale_update_eq (verify : SigVerifier)
    (cs : CanonicalNetwork) (u : ChannelUpdate)
    (hstale : ∃ v ∈ cs.gossip.updates,
      v.shortChannelId = u.shortChannelId ∧ v.direction = u.direction ∧
        u.timestamp ≤ v.timestamp) :
    admitGossipCanonical verify cs (.channelUpdate u) = cs := by
  rcases hstale with ⟨v, hv, hscid, hdir, hts⟩
  apply admitGossipCanonical_update_of_rejected
  rintro ⟨_, _, hsup⟩
  exact stale_update_not_supersedes hv hscid hdir hts hsup

/-- After a successful supersession, the replaced (older or equal) record still
fails the supersession gate for the new store: the incoming update itself is
stored in the slot. -/
theorem stale_update_not_supersedes_inserted {u v : ChannelUpdate}
    {l : List ChannelUpdate} (hscid : v.shortChannelId = u.shortChannelId)
    (hdir : v.direction = u.direction) (hts : v.timestamp ≤ u.timestamp) :
    ¬ UpdateSupersedes v (insertUpdateCanonical u l) := by
  intro h
  have hu : u ∈ insertUpdateCanonical u l := List.mem_cons_self ..
  have hlt := h u hu hscid.symm hdir.symm
  exact Nat.lt_irrefl u.timestamp (Nat.lt_of_lt_of_le hlt hts)

/-- **Supersession forbids a later stale overwrite.**  Once `u` is admitted in
its slot, any same-slot `v` with `v.timestamp ≤ u.timestamp` is rejected, so
the canonical transition is a no-op. -/
theorem canonical_superseded_update_stays_rejected (verify : SigVerifier)
    (cs : CanonicalNetwork) (u v : ChannelUpdate)
    (hgate : u.signatureValid verify ∧
      cs.gossip.updateKeyAnnouncedDirectional u ∧
        UpdateSupersedes u cs.gossip.updates)
    (hscid : v.shortChannelId = u.shortChannelId)
    (hdir : v.direction = u.direction) (hts : v.timestamp ≤ u.timestamp) :
    admitGossipCanonical verify
      (admitGossipCanonical verify cs (.channelUpdate u)) (.channelUpdate v) =
      admitGossipCanonical verify cs (.channelUpdate u) := by
  rw [admitGossipCanonical_update_of_admitted verify cs u hgate]
  apply admitGossipCanonical_update_of_rejected
  rintro ⟨_, _, hsup⟩
  exact stale_update_not_supersedes_inserted hscid hdir hts hsup

/-- Epoch form: a stale update delivered after a superseding epoch step leaves
the store at the superseded state. -/
theorem epoch_supersession_preserves_stale_rejection (verify : SigVerifier)
    (es : EpochNetwork) (u v : ChannelUpdate)
    (hgate : u.signatureValid verify ∧
      es.network.gossip.updateKeyAnnouncedDirectional u ∧
        UpdateSupersedes u es.network.gossip.updates)
    (hscid : v.shortChannelId = u.shortChannelId)
    (hdir : v.direction = u.direction) (hts : v.timestamp ≤ u.timestamp) :
    let es' := epochAdmit verify es (.channelUpdate u)
    (epochAdmit verify es' (.channelUpdate v)).network = es'.network := by
  dsimp only
  simp only [epochAdmit_network]
  exact canonical_superseded_update_stays_rejected verify es.network u v hgate
    hscid hdir hts

/-! ## 4. The reachable epoch invariant -/

/-- A state is reachable in the epoch model from the empty store by canonical
admissions, epoch advances, and explicit rotations.  A rotation carries its two
re-signing/re-attribution obligations as explicit premises. -/
inductive ReachableEpoch (verify : SigVerifier) : EpochNetwork → Prop
  | empty (nodeKeyOf : NodeId → PubKey) :
      ReachableEpoch verify
        { network := ⟨⟨[], [], []⟩, [], nodeKeyOf⟩, epoch := 0 }
  | deliver {es : EpochNetwork} {m : GossipMessage} :
      ReachableEpoch verify es →
        ReachableEpoch verify (epochAdmit verify es m)
  | advance {es : EpochNetwork} :
      ReachableEpoch verify es →
        ReachableEpoch verify (epochAdvance es)
  | rotate {es : EpochNetwork} {n : NodeId} {k : PubKey}
      (h : ReachableEpoch verify es)
      (hstore : StoreAnnouncementsValid verify (rekeyStore es.network.gossip n k))
      (hupdates : StoreUpdatesDirectionallyAttributed verify
        (rekeyStore es.network.gossip n k)) :
      ReachableEpoch verify (epochRotate es n k)

/-! ## 5. Rotation preserves the canonical invariant -/

/-- **Rotation preserves the full canonical invariant**, under exactly the
two rotation obligations: the rekeyed announcements are valid (re-signed), and
the stored updates are signature-valid and re-attributed under the rotated
keys (resubmitted or re-signed). -/
theorem rotateNetwork_preserves_canonicalAdmitted (verify : SigVerifier)
    (cs : CanonicalNetwork) (n : NodeId) (k : PubKey)
    (hinv : CanonicalAdmitted verify cs)
    (hstore : StoreAnnouncementsValid verify (rekeyStore cs.gossip n k))
    (hupdates : StoreUpdatesDirectionallyAttributed verify
      (rekeyStore cs.gossip n k)) :
    CanonicalAdmitted verify (rotateNetwork cs n k) := by
  rcases hinv with ⟨_hvalid, hviews, _hupd, hnode, hcanon⟩
  refine ⟨hstore, ?_, hupdates, ?_, ?_⟩
  · intro v hv
    rcases hviews v hv with ⟨b, hb, _hbsig, hscid, h1, h2, hcap⟩
    refine ⟨rekeyAnnouncement b n k, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show rekeyAnnouncement b n k ∈
        (rekeyStore cs.gossip n k).announcements
      rw [rekeyStore_announcements]
      exact List.mem_map_of_mem (f := fun a => rekeyAnnouncement a n k) hb
    · exact hstore _ (by
        rw [rekeyStore_announcements]
        exact List.mem_map_of_mem (f := fun a => rekeyAnnouncement a n k) hb)
    · rw [rekeyAnnouncement_shortChannelId]
      exact hscid
    · rw [rekeyAnnouncement_node1]
      exact h1
    · rw [rekeyAnnouncement_node2]
      exact h2
    · show v.capacitySat = b.capacitySat
      exact hcap
  · exact nodeKeyConsistent_rekey hnode n k
  · exact canonical_rekey hcanon n k

/-- A store with no updates satisfies the directional-attribution invariant
vacuously. -/
theorem storeUpdatesDirectionallyAttributed_of_updates_nil {verify : SigVerifier}
    {s : GossipState} (h : s.updates = []) :
    StoreUpdatesDirectionallyAttributed verify s := by
  intro u hu
  rw [h] at hu
  simp at hu

/-- **Rotation before any update needs only the re-signing premise.**  With an
empty update list the re-attribution obligation is vacuous. -/
theorem rotateNetwork_preserves_canonicalAdmitted_of_noUpdates
    (verify : SigVerifier) (cs : CanonicalNetwork) (n : NodeId) (k : PubKey)
    (hinv : CanonicalAdmitted verify cs) (hupd : cs.gossip.updates = [])
    (hstore : StoreAnnouncementsValid verify (rekeyStore cs.gossip n k)) :
    CanonicalAdmitted verify (rotateNetwork cs n k) :=
  rotateNetwork_preserves_canonicalAdmitted verify cs n k hinv hstore
    (storeUpdatesDirectionallyAttributed_of_updates_nil (by
      simp [rekeyStore, hupd]))

/-- **The invariant of every reachable epoch state.**  The epoch counter and
all epoch boundaries (delivery, silent advance, rotation) preserve the
canonical store invariant. -/
theorem reachableEpoch_invariant {verify : SigVerifier} {es : EpochNetwork}
    (h : ReachableEpoch verify es) :
    CanonicalAdmitted verify es.network := by
  induction h with
  | empty nodeKeyOf =>
      exact reachableCanonical_invariant
        (ReachableCanonical.empty (verify := verify) nodeKeyOf)
  | deliver _ ih =>
      exact admitGossipCanonical_preserves verify _ _ ih
  | advance _ ih =>
      exact ih
  | rotate _ hstore hupdates ih =>
      exact rotateNetwork_preserves_canonicalAdmitted verify _ _ _ ih hstore hupdates

/-- Reachable epoch states have a consistent node-key registration map. -/
theorem reachableEpoch_nodeKeyConsistent {verify : SigVerifier}
    {es : EpochNetwork} (h : ReachableEpoch verify es) :
    GossipState.NodeKeyConsistent es.network.nodeKeyOf es.network.gossip :=
  (reachableEpoch_invariant h).nodeKeys

/-- Reachable epoch states keep one announcement per channel. -/
theorem reachableEpoch_canonical {verify : SigVerifier} {es : EpochNetwork}
    (h : ReachableEpoch verify es) :
    CanonicalAnnouncements es.network.gossip.announcements :=
  (reachableEpoch_invariant h).canonical

/-- Reachable epoch states keep a signature-valid announcement store. -/
theorem reachableEpoch_store_valid {verify : SigVerifier} {es : EpochNetwork}
    (h : ReachableEpoch verify es) :
    StoreAnnouncementsValid verify es.network.gossip :=
  (reachableEpoch_invariant h).storeValid

/-- Reachable epoch states keep direction-correctly attributed updates. -/
theorem reachableEpoch_updates_directional {verify : SigVerifier}
    {es : EpochNetwork} (h : ReachableEpoch verify es) :
    StoreUpdatesDirectionallyAttributed verify es.network.gossip :=
  (reachableEpoch_invariant h).updatesAttributed

/-- The invariant is preserved by an explicit rotation out of a reachable
epoch state. -/
theorem reachableEpoch_rotate_invariant {verify : SigVerifier}
    {es : EpochNetwork} (h : ReachableEpoch verify es) {n : NodeId} {k : PubKey}
    (hstore : StoreAnnouncementsValid verify (rekeyStore es.network.gossip n k))
    (hupdates : StoreUpdatesDirectionallyAttributed verify
      (rekeyStore es.network.gossip n k)) :
    CanonicalAdmitted verify (epochRotate es n k).network :=
  rotateNetwork_preserves_canonicalAdmitted verify es.network n k
    (reachableEpoch_invariant h) hstore hupdates

/-! ## 6. Rotation keeps current keys/announcements -/

/-- Exact membership in a rekeyed announcement list. -/
theorem mem_rekeyAnnouncements_iff {b : ChannelAnnellation}
    {l : List ChannelAnnellation} {n : NodeId} {k : PubKey} :
    b ∈ rekeyAnnouncements l n k ↔
      ∃ a ∈ l, b = rekeyAnnouncement a n k := by
  constructor
  · intro hb
    rcases List.mem_map.mp hb with ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact List.mem_map_of_mem (f := fun a => rekeyAnnouncement a n k) ha

/-- Rekeying does not change the rotated node's first-position key when it is
not the announcement's first endpoint. -/
theorem rekeyAnnouncement_nodeKey1_of_ne {a : ChannelAnnellation}
    {n : NodeId} {k : PubKey} (h : a.node1 ≠ n) :
    (rekeyAnnouncement a n k).nodeKey1 = a.nodeKey1 := by
  simp [rekeyAnnouncement, h]

/-- Rekeying writes the new key into the first endpoint position. -/
theorem rekeyAnnouncement_nodeKey1_of_eq {a : ChannelAnnellation}
    {n : NodeId} {k : PubKey} (h : a.node1 = n) :
    (rekeyAnnouncement a n k).nodeKey1 = k := by
  simp [rekeyAnnouncement, h]

/-- Rekeying does not change the rotated node's second-position key when it is
not the announcement's second endpoint. -/
theorem rekeyAnnouncement_nodeKey2_of_ne {a : ChannelAnnellation}
    {n : NodeId} {k : PubKey} (h : a.node2 ≠ n) :
    (rekeyAnnouncement a n k).nodeKey2 = a.nodeKey2 := by
  simp [rekeyAnnouncement, h]

/-- Rekeying writes the new key into the second endpoint position. -/
theorem rekeyAnnouncement_nodeKey2_of_eq {a : ChannelAnnellation}
    {n : NodeId} {k : PubKey} (h : a.node2 = n) :
    (rekeyAnnouncement a n k).nodeKey2 = k := by
  simp [rekeyAnnouncement, h]

/-- An announcement that names the rotated node in neither endpoint is
unchanged by rekeying. -/
theorem rekeyAnnouncement_eq_self_of_ne {a : ChannelAnnellation}
    {n : NodeId} {k : PubKey} (h1 : a.node1 ≠ n) (h2 : a.node2 ≠ n) :
    rekeyAnnouncement a n k = a := by
  cases a with
  | mk scid u v ku kv b1 b2 cap dig s1 s2 s3 s4 =>
      simp [rekeyAnnouncement, h1, h2]

/-- Rekeying preserves the capacity field. -/
@[simp] theorem rekeyAnnouncement_capacitySat (a : ChannelAnnellation)
    (n : NodeId) (k : PubKey) :
    (rekeyAnnouncement a n k).capacitySat = a.capacitySat :=
  rfl

/-- **Announcement identity survives rotation.**  Every stored announcement has
a rekeyed record with the same channel id, endpoints, and capacity (only key
fields can change). -/
theorem rotation_preserves_announcement_identity {cs : CanonicalNetwork}
    {n : NodeId} {k : PubKey} {a : ChannelAnnellation}
    (ha : a ∈ cs.gossip.announcements) :
    ∃ b ∈ (rekeyStore cs.gossip n k).announcements,
      b.shortChannelId = a.shortChannelId ∧ b.node1 = a.node1 ∧
        b.node2 = a.node2 ∧ b.capacitySat = a.capacitySat := by
  refine ⟨rekeyAnnouncement a n k, ?_, ?_, ?_, ?_, ?_⟩
  · rw [rekeyStore_announcements]
    exact List.mem_map_of_mem (f := fun a => rekeyAnnouncement a n k) ha
  · rw [rekeyAnnouncement_shortChannelId]
  · rw [rekeyAnnouncement_node1]
  · rw [rekeyAnnouncement_node2]
  · rfl

/-- **The rotated node's current key survives.**  If an announcement names node
`n` at its first endpoint, the rotated store contains a record for the same
channel whose first key is the new key `k`. -/
theorem rotation_current_key_survives {cs : CanonicalNetwork}
    {n : NodeId} {k : PubKey} {a : ChannelAnnellation}
    (ha : a ∈ cs.gossip.announcements) (hn : a.node1 = n) :
    ∃ b ∈ (rekeyStore cs.gossip n k).announcements,
      b.node1 = n ∧ b.nodeKey1 = k := by
  refine ⟨rekeyAnnouncement a n k, ?_, ?_, ?_⟩
  · rw [rekeyStore_announcements]
    exact List.mem_map_of_mem (f := fun a => rekeyAnnouncement a n k) ha
  · rw [rekeyAnnouncement_node1, hn]
  · exact rekeyAnnouncement_nodeKey1_of_eq hn

/-- Second-endpoint form of `rotation_current_key_survives`. -/
theorem rotation_current_key_survives_node2 {cs : CanonicalNetwork}
    {n : NodeId} {k : PubKey} {a : ChannelAnnellation}
    (ha : a ∈ cs.gossip.announcements) (hn : a.node2 = n) :
    ∃ b ∈ (rekeyStore cs.gossip n k).announcements,
      b.node2 = n ∧ b.nodeKey2 = k := by
  refine ⟨rekeyAnnouncement a n k, ?_, ?_, ?_⟩
  · rw [rekeyStore_announcements]
    exact List.mem_map_of_mem (f := fun a => rekeyAnnouncement a n k) ha
  · rw [rekeyAnnouncement_node2, hn]
  · exact rekeyAnnouncement_nodeKey2_of_eq hn

/-! ## 7. Concrete epoch witnesses -/

private def acceptingVerifier : SigVerifier := fun _ _ _ => true

private def kOld : PubKey := ⟨ByteArray.mk #[1]⟩

private def kNew : PubKey := ⟨ByteArray.mk #[1, 2]⟩

private def kOther : PubKey := ⟨ByteArray.empty⟩

private def nodeA : NodeId := ⟨0⟩

private def nodeB : NodeId := ⟨1⟩

private def sampleScid : ShortChannelId := ⟨1, 2, 3⟩

private def emptySig : GossipSignature := ⟨ByteArray.empty⟩

private def mkAnn (k1 k2 : PubKey) : ChannelAnnellation :=
  { shortChannelId := sampleScid
    node1 := nodeA
    node2 := nodeB
    nodeKey1 := k1
    nodeKey2 := k2
    bitcoinKey1 := k1
    bitcoinKey2 := k2
    capacitySat := 1000
    digest := ByteArray.empty
    nodeSignature1 := emptySig
    nodeSignature2 := emptySig
    bitcoinSignature1 := emptySig
    bitcoinSignature2 := emptySig }

/-- The pre-rotation announcement: `nodeA ↦ kOld`, `nodeB ↦ kOther`. -/
private def annOld : ChannelAnnellation := mkAnn kOld kOther

/-- The post-rotation announcement: the rekeyed pre-rotation record. -/
private def annNew : ChannelAnnellation := rekeyAnnouncement annOld nodeA kNew

private def mkUpd (ts : Nat) (k : PubKey) : ChannelUpdate :=
  { shortChannelId := sampleScid
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

/-- Current update, timestamp 2. -/
private def uNew : ChannelUpdate := mkUpd 2 kOld

/-- Stale update, timestamp 1, same slot. -/
private def uStale : ChannelUpdate := mkUpd 1 kOld

private theorem keyNew_ne_keyOld : kNew ≠ kOld := by
  intro h
  have hs := congrArg (fun k => k.bytes.size) h
  have h1 : kNew.bytes.size = 2 := by decide
  have h2 : kOld.bytes.size = 1 := by decide
  rw [h1, h2] at hs
  omega

private theorem nodeA_ne_nodeB : nodeA ≠ nodeB := by decide

private theorem nodeB_ne_nodeA : nodeB ≠ nodeA := by decide

private theorem annOld_valid : annOld.signaturesValid acceptingVerifier := by
  simp [ChannelAnnellation.signaturesValid, signatureValid, acceptingVerifier]

private def start : CanonicalNetwork :=
  { gossip := ⟨[], [], []⟩, views := [], nodeKeyOf := fun _ => kOther }

private theorem start_compatible (a : ChannelAnnellation) :
    start.gossip.CompatibleWithStore a := by
  intro b hb
  simp [start] at hb

private theorem start_authorizes (a : ChannelAnnellation) :
    UpdatesAuthorizedBy start.gossip a := by
  intro u hu
  simp [start] at hu

private theorem annOld_gate :
    annOld.signaturesValid acceptingVerifier ∧ annOld.node1 ≠ annOld.node2 ∧
      start.gossip.CompatibleWithStore annOld ∧
        UpdatesAuthorizedBy start.gossip annOld :=
  ⟨annOld_valid, by simpa [annOld, mkAnn] using nodeA_ne_nodeB,
    start_compatible annOld, start_authorizes annOld⟩

private noncomputable def afterAnn : CanonicalNetwork :=
  admitGossipCanonical acceptingVerifier start (.channelAnnouncement annOld)

private theorem afterAnn_eq : afterAnn =
    { gossip := { start.gossip with announcements := [annOld] }
      views := [admittedChannelView annOld]
      nodeKeyOf := bindNodeKeys start.nodeKeyOf annOld } := by
  unfold afterAnn
  rw [admitGossipCanonical_announcement_of_admitted acceptingVerifier start annOld
    annOld_gate]
  simp [insertReplacing, insertViewCanonical, start]

private theorem afterAnn_announcements : afterAnn.gossip.announcements = [annOld] := by
  rw [afterAnn_eq]

private theorem afterAnn_updates : afterAnn.gossip.updates = [] := by
  rw [afterAnn_eq]
  rfl

private def emptyEpoch : EpochNetwork := { network := start, epoch := 0 }

private noncomputable def epochAfterAnn : EpochNetwork :=
  epochAdmit acceptingVerifier emptyEpoch (.channelAnnouncement annOld)

private theorem epochAfterAnn_network : epochAfterAnn.network = afterAnn := by
  unfold epochAfterAnn emptyEpoch afterAnn start
  rfl

private theorem rekey_annOld : rekeyAnnouncement annOld nodeA kNew = annNew :=
  rfl

private noncomputable def epochAfterUpdate : EpochNetwork :=
  epochAdmit acceptingVerifier epochAfterAnn (.channelUpdate uNew)

private noncomputable def rotatedEpoch : EpochNetwork :=
  epochRotate epochAfterAnn nodeA kNew

private theorem epochAfterAnn_attributed_uNew :
    epochAfterAnn.network.gossip.updateKeyAnnouncedDirectional uNew := by
  refine GossipState.updateKeyAnnouncedDirectional_of_mem (a := annOld) ?_ rfl ?_
  · rw [epochAfterAnn_network, afterAnn_announcements]
    exact List.mem_singleton_self annOld
  · rw [ChannelUpdate.direction_of_channelFlags_zero (by rfl : uNew.channelFlags = 0)]
    simp [ChannelAnnellation.attributesKeyForDirection, annOld, mkAnn, uNew, mkUpd]

private theorem uNew_gate :
    uNew.signatureValid acceptingVerifier ∧
      epochAfterAnn.network.gossip.updateKeyAnnouncedDirectional uNew ∧
        UpdateSupersedes uNew epochAfterAnn.network.gossip.updates := by
  refine ⟨?_, epochAfterAnn_attributed_uNew, ?_⟩
  · simp [ChannelUpdate.signatureValid, signatureValid, acceptingVerifier]
  · intro v hv
    rw [epochAfterAnn_network, afterAnn_updates] at hv
    simp at hv

private theorem epochAfterUpdate_updates :
    epochAfterUpdate.network.gossip.updates = [uNew] := by
  unfold epochAfterUpdate
  rw [epochAdmit_network]
  rw [admitGossipCanonical_update_of_admitted acceptingVerifier
    epochAfterAnn.network uNew uNew_gate]
  rw [epochAfterAnn_network, afterAnn_updates]
  simp [insertUpdateCanonical]

private theorem epochAfterUpdate_reachable :
    ReachableEpoch acceptingVerifier epochAfterUpdate := by
  unfold epochAfterUpdate
  exact ReachableEpoch.deliver (by
    unfold epochAfterAnn
    exact ReachableEpoch.deliver
      (ReachableEpoch.empty (fun _ => kOther)))

private theorem uStale_not_supersedes :
    ¬ UpdateSupersedes uStale epochAfterUpdate.network.gossip.updates := by
  rw [epochAfterUpdate_updates]
  intro h
  have hlt := h uNew (List.mem_singleton_self uNew) rfl rfl
  simp [uStale, uNew, mkUpd] at hlt

private theorem epochAfterUpdate_rejects_uStale :
    admitGossipCanonical acceptingVerifier epochAfterUpdate.network
      (.channelUpdate uStale) = epochAfterUpdate.network := by
  apply admitGossipCanonical_update_of_rejected
  rintro ⟨_, _, hsup⟩
  exact uStale_not_supersedes hsup

private theorem rotatedEpoch_reachable :
    ReachableEpoch acceptingVerifier rotatedEpoch := by
  unfold rotatedEpoch
  refine ReachableEpoch.rotate ?_ ?_ ?_
  · unfold epochAfterAnn
    exact ReachableEpoch.deliver
      (ReachableEpoch.empty (fun _ => kOther))
  · intro a _
    simp [announcementValid, ChannelAnnellation.signaturesValid,
      signatureValid, acceptingVerifier]
  · have hnil : (rekeyStore afterAnn.gossip nodeA kNew).updates = [] := by
      change afterAnn.gossip.updates = []
      exact afterAnn_updates
    exact storeUpdatesDirectionallyAttributed_of_updates_nil hnil

private theorem rotatedEpoch_network :
    rotatedEpoch.network = rotateNetwork afterAnn nodeA kNew := by
  unfold rotatedEpoch epochRotate
  rw [epochAfterAnn_network]

private theorem rotated_announcements :
    rotatedEpoch.network.gossip.announcements = [annNew] := by
  rw [rotatedEpoch_network]
  unfold rotateNetwork
  change (rekeyStore afterAnn.gossip nodeA kNew).announcements = [annNew]
  rw [rekeyStore_announcements, afterAnn_announcements]
  simp [rekeyAnnouncements, rekey_annOld]

/-- **Stale update rejection is epoch-independent.**  In a reachable epoch
state whose current slot record is `uNew` (timestamp 2), the older same-slot
`uStale` (timestamp 1) is rejected in every epoch: the epoch counter is not a
freshness clock. -/
theorem stale_update_rejected_in_every_epoch :
    ∃ (verify : SigVerifier) (es : EpochNetwork) (u v : ChannelUpdate),
      ReachableEpoch verify es ∧ v ∈ es.network.gossip.updates ∧
        v.shortChannelId = u.shortChannelId ∧ v.direction = u.direction ∧
          u.timestamp ≤ v.timestamp ∧
            (∀ e : Nat,
              (epochAdmit verify { es with epoch := e } (.channelUpdate u)).network =
                es.network) := by
  refine ⟨acceptingVerifier, epochAfterUpdate, uStale, uNew,
    epochAfterUpdate_reachable, ?_, rfl, rfl, ?_, ?_⟩
  · rw [epochAfterUpdate_updates]
    exact List.mem_singleton_self uNew
  · simp [uStale, uNew, mkUpd]
  · intro e
    simpa [epochAdmit] using epochAfterUpdate_rejects_uStale

/-- **A pre-rotation announcement stays rejected after rotation.**  The stored
record now carries `kNew` for `nodeA`, so an announcement still carrying the
old key `kOld` fails the registration-compatibility gate. -/
theorem stale_announcement_rejected_in_every_epoch :
    ∃ (verify : SigVerifier) (es : EpochNetwork) (a : ChannelAnnellation),
      ReachableEpoch verify es ∧
        (∀ e : Nat,
          (epochAdmit verify { es with epoch := e } (.channelAnnouncement a)).network =
            es.network) := by
  have hnot : ¬ rotatedEpoch.network.gossip.CompatibleWithStore annOld := by
    intro hc
    have hmem : annNew ∈ rotatedEpoch.network.gossip.announcements := by
      rw [rotated_announcements]
      exact List.mem_singleton_self annNew
    have hkey : annNew.nodeKey1 = annOld.nodeKey1 := (hc annNew hmem).1 rfl
    have hnew : annNew.nodeKey1 = kNew := by
      unfold annNew
      exact rekeyAnnouncement_nodeKey1_of_eq rfl
    have hold : annOld.nodeKey1 = kOld := rfl
    exact keyNew_ne_keyOld (hnew.symm.trans (hkey.trans hold))
  have hreject : admitGossipCanonical acceptingVerifier rotatedEpoch.network
      (.channelAnnouncement annOld) = rotatedEpoch.network := by
    apply admitGossipCanonical_announcement_of_rejected
    rintro ⟨_, _, hc, _⟩
    exact hnot hc
  refine ⟨acceptingVerifier, rotatedEpoch, annOld, rotatedEpoch_reachable, ?_⟩
  intro e
  simpa [epochAdmit] using hreject

/-- **Rotation witness: the current key survives.**  The rotated reachable
epoch state stores the announcement for the rotated node with the new key. -/
theorem rotation_current_key_witness :
    ∃ (verify : SigVerifier) (es : EpochNetwork) (n : NodeId) (k : PubKey),
      ReachableEpoch verify es ∧
        (∃ a ∈ es.network.gossip.announcements, a.node1 = n ∧ a.nodeKey1 = k) := by
  refine ⟨acceptingVerifier, rotatedEpoch, nodeA, kNew, rotatedEpoch_reachable,
    annNew, ?_, ?_, ?_⟩
  · rw [rotated_announcements]
    exact List.mem_singleton_self annNew
  · show annNew.node1 = nodeA
    unfold annNew
    rw [rekeyAnnouncement_node1]
    rfl
  · show annNew.nodeKey1 = kNew
    unfold annNew
    exact rekeyAnnouncement_nodeKey1_of_eq rfl

/-- **Rotation witness: a channel record survives with its identity.**  After
rotation the stored announcement still has two distinct endpoints and its
capacity; only key fields may have changed. -/
theorem rotation_identity_witness :
    ∃ (verify : SigVerifier) (es : EpochNetwork) (a : ChannelAnnellation),
      ReachableEpoch verify es ∧ a ∈ es.network.gossip.announcements ∧
        a.node1 ≠ a.node2 ∧ a.capacitySat = 1000 := by
  refine ⟨acceptingVerifier, rotatedEpoch, annNew, rotatedEpoch_reachable, ?_,
    ?_, rfl⟩
  · rw [rotated_announcements]
    exact List.mem_singleton_self annNew
  · simp [annNew, annOld, mkAnn, nodeA, nodeB]

/-- **Non-vacuity: a rotated reachable epoch state satisfies the full canonical
invariant.**  The witness has an announcement and no updates, so rotation needs
only the re-signing premise (discharged by the accepting verifier). -/
theorem rotatedEpoch_canonicalAdmitted :
    ∃ (verify : SigVerifier) (es : EpochNetwork),
      ReachableEpoch verify es ∧ CanonicalAdmitted verify es.network ∧
        es.network.gossip.announcements ≠ [] := by
  refine ⟨acceptingVerifier, rotatedEpoch, rotatedEpoch_reachable,
    reachableEpoch_invariant rotatedEpoch_reachable, ?_⟩
  rw [rotated_announcements]
  simp

/-! ## 8. Preserved wave-7 boundaries -/

/-- The raw global clock is still strictly stronger than the canonical per-slot
gate.  Epochs do not change either clock, so this boundary is preserved
unchanged from wave 7. -/
theorem canonical_admission_strictly_weaker_than_raw_clock_preserved :
    ∃ (verify : SigVerifier) (cs : CanonicalStore) (u : ChannelUpdate),
      ReachableCanonicalStore verify cs ∧
        CanonicalMessageAdmitted verify cs (.channelUpdate u) ∧
          ¬ RawClockAdmits cs.gossip (.channelUpdate u) ∧
            (applyGossipCanonicalStore verify cs (.channelUpdate u)).gossip.updates =
              u :: cs.gossip.updates ∧
              applyGossip cs.gossip (.channelUpdate u) = cs.gossip ∧
                u ∉ cs.gossip.updates :=
  canonical_admission_strictly_weaker_than_raw_clock

/-- Rotation still does not preserve update attribution without resubmission;
the wave-6 boundary witness is re-exported unchanged. -/
theorem rotation_breaks_update_attribution_preserved :
    ∃ (nodeKeyOf : NodeId → PubKey) (s : GossipState) (n : NodeId)
      (k : PubKey) (u : ChannelUpdate),
      GossipState.NodeKeyConsistent nodeKeyOf s ∧
        GossipState.NodeKeyConsistent (rotateNodeKey nodeKeyOf n k)
          (rekeyStore s n k) ∧
          CanonicalAnnouncements (rekeyStore s n k).announcements ∧
            s.updateKeyAnnouncedDirectional u ∧
              ¬ (rekeyStore s n k).updateKeyAnnouncedDirectional u :=
  rotation_breaks_update_attribution

end LnLean.Proofs.WaveH.H41
