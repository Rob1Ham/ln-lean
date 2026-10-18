# S7-RT-RAW — raw `applyGossip` refined against canonical store admission

**Lane:** `S7-RT-RAW`
**Issue:** `RT-01` (raw insertion vs canonical admission/store path)
**Worktree:** `/home/ubuntu/ln-lean-repair`
**Toolchain:** `leanprover/lean4:v4.35.0` (Lean `4.35.0`, no Mathlib)
**Owned files changed:**

* `LnLean/Routing/Gossip.lean` — additive only, `374` inserted / `0` deleted,
* `LnLean/Proofs/Routing/GossipRawRefinementTargets.lean` — new, `1125` lines,
* `agents/reports/swarm7/S7-RT-RAW.md` — this report.

No Git write was performed.  No shared file (`LnLean.lean`, `Obligations.lean`,
`Traceability.lean`, `AxiomAudit.lean`, `scripts/check-final.py`, shared docs,
other lanes' files, vendor sources) was edited.

## 1. Verdict

Raw `applyGossip` **cannot** be refined to the canonical admission transition as
a function while preserving canonical invariants.  It has no signature gate, no
node-key registration gate, and no per-`(short_channel_id, direction)` clock:
`GossipState.applyUpdate` compares only one global timestamp, and raw
announcements are appended forever.  The strongest true statement is therefore a
**canonical store wrapper plus a sharp refinement square**, not an equality of
raw and canonical transitions.

The new proof module supplies:

* `CanonicalStore` — the store projection of the wave-6 `CanonicalNetwork`
  (gossip state plus explicit `NodeId → PubKey` registration map; routing views
  omitted);
* `applyGossipCanonicalStore` — the same admission policy as
  `admitGossipCanonical`, specialised to that store.  Two projection theorems
  prove that its gossip/registration result is **exactly** the wave-6
  transition's projection, so the wrapper cannot drift from the canonical path;
* `ReachableCanonicalStore` and `CanonicalStoreAdmitted` — reachability and the
  store invariant, extending the wave-6 `CanonicalAdmitted` invariant with
  per-direction slot uniqueness;
* `reachableCanonicalStore_shape` — every reachable store is already in
  canonical selector shape (`selectAnnouncements` / `selectUpdates` are the
  identities);
* `canonicalStoreView_applyGossip_eq_canonicalStore` — **the refinement
  square**: on a canonically shaped store, with the canonical gates and the raw
  global clock, observing a raw step through `canonicalStoreView` is the
  canonical store step;
* `applyGossip_eq_canonicalStore_of_fresh` — literal agreement on the strictly
  smaller common domain where the incoming channel or directional slot is fresh;
* `canonical_admission_strictly_weaker_than_raw_clock` — a reachable boundary
  witness where the canonical per-slot gate accepts an update that the raw
  global clock ignores;
* `no_canonical_preserving_raw_announcement_extension` — an impossibility
  theorem: no transition keeping raw append semantics for
  `channel_announcement` can preserve `CanonicalAnnouncements` from the empty
  store.

The wave-4/5 conflicting-announcement counterexamples are re-exported unchanged,
and the wave-6 canonical rejection of the conflicting re-announcement is
re-exported next to them.  Raw `applyGossip`, `GossipState.applyUpdate`,
`canonicalView` (oldest-record-wins), every wave-A/5/6 statement, and the
`CanonicalNetwork` endpoint theorem keep their exact meaning.

## 2. Required build

Command (exactly the lane-prescribed form):

```sh
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Routing.Gossip \
    LnLean.Proofs.Routing.GossipRawRefinementTargets \
    LnLean.Proofs.Routing.GossipCanonicalTargets \
    LnLean.Proofs.Routing.GossipKeyConsistencyTargets
```

Result:

```text
✔ [10/13] Built LnLean.Proofs.Routing.GossipAttributionTargets
✔ [11/13] Built LnLean.Proofs.Routing.GossipKeyConsistencyTargets
✔ [12/13] Built LnLean.Proofs.Routing.GossipCanonicalTargets
✔ [13/13] Built LnLean.Proofs.Routing.GossipRawRefinementTargets
Build completed successfully (13 jobs).
RC=0
```

There are **no warnings** in `LnLean/Routing/Gossip.lean` or
`LnLean/Proofs/Routing/GossipRawRefinementTargets.lean`.  The only warnings in
the build are the pre-existing `if_pos`/`if_neg` deprecations in
`LnLean/Proofs/Routing/GossipProps.lean` (`12` warning headers).  No full
`lake build` was run.

## 3. Exact signatures

The following are the public declarations of
`LnLean.Proofs.Routing.GossipRawRefinementTargets`, with the namespace prefix
removed.  They are root-level in
`LnLean.Proofs.Routing.GossipRawRefinementTargets`.

### 3.1 Store wrapper and transition equations

```lean
structure CanonicalStore where
  gossip : GossipState
  nodeKeyOf : NodeId → PubKey

def CanonicalStore.toNetwork (cs : CanonicalStore) : CanonicalNetwork

noncomputable def applyGossipCanonicalStore (verify : SigVerifier)
    (cs : CanonicalStore) : GossipMessage → CanonicalStore

theorem applyGossipCanonicalStore_gossip_toNetwork (verify : SigVerifier)
    (cs : CanonicalStore) (m : GossipMessage) :
    (applyGossipCanonicalStore verify cs m).gossip =
      (admitGossipCanonical verify cs.toNetwork m).gossip

theorem applyGossipCanonicalStore_nodeKeyOf_toNetwork (verify : SigVerifier)
    (cs : CanonicalStore) (m : GossipMessage) :
    (applyGossipCanonicalStore verify cs m).nodeKeyOf =
      (admitGossipCanonical verify cs.toNetwork m).nodeKeyOf

theorem applyGossipCanonicalStore_announcement_of_admitted
    (verify : SigVerifier) (cs : CanonicalStore) (a : ChannelAnnellation)
    (h : a.signaturesValid verify ∧ a.node1 ≠ a.node2 ∧
      cs.gossip.CompatibleWithStore a ∧ UpdatesAuthorizedBy cs.gossip a) :
    applyGossipCanonicalStore verify cs (.channelAnnouncement a) =
      { gossip := { cs.gossip with
          announcements := insertReplacing a cs.gossip.announcements }
        nodeKeyOf := bindNodeKeys cs.nodeKeyOf a }

theorem applyGossipCanonicalStore_announcement_of_rejected
    (verify : SigVerifier) (cs : CanonicalStore) (a : ChannelAnnellation)
    (h : ¬ (a.signaturesValid verify ∧ a.node1 ≠ a.node2 ∧
      cs.gossip.CompatibleWithStore a ∧ UpdatesAuthorizedBy cs.gossip a)) :
    applyGossipCanonicalStore verify cs (.channelAnnouncement a) = cs

theorem applyGossipCanonicalStore_update_of_admitted
    (verify : SigVerifier) (cs : CanonicalStore) (u : ChannelUpdate)
    (h : u.signatureValid verify ∧
      cs.gossip.updateKeyAnnouncedDirectional u ∧
      UpdateSupersedes u cs.gossip.updates) :
    applyGossipCanonicalStore verify cs (.channelUpdate u) =
      { gossip := { cs.gossip with
          updates := insertUpdateCanonical u cs.gossip.updates }
        nodeKeyOf := cs.nodeKeyOf }

theorem applyGossipCanonicalStore_update_of_rejected
    (verify : SigVerifier) (cs : CanonicalStore) (u : ChannelUpdate)
    (h : ¬ (u.signatureValid verify ∧
      cs.gossip.updateKeyAnnouncedDirectional u ∧
      UpdateSupersedes u cs.gossip.updates)) :
    applyGossipCanonicalStore verify cs (.channelUpdate u) = cs

theorem applyGossipCanonicalStore_node_of_valid
    (verify : SigVerifier) (cs : CanonicalStore) (n : NodeAnnouncement)
    (h : n.signatureValid verify) :
    applyGossipCanonicalStore verify cs (.nodeAnnouncement n) =
      { gossip := { cs.gossip with
          nodeAnnouncements := n :: cs.gossip.nodeAnnouncements }
        nodeKeyOf := cs.nodeKeyOf }

theorem applyGossipCanonicalStore_node_of_invalid
    (verify : SigVerifier) (cs : CanonicalStore) (n : NodeAnnouncement)
    (h : ¬ n.signatureValid verify) :
    applyGossipCanonicalStore verify cs (.nodeAnnouncement n) = cs
```

### 3.2 Admission, raw clock, and freshness predicates

```lean
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

def RawClockAdmits (s : GossipState) : GossipMessage → Prop
  | .channelAnnouncement _ => True
  | .channelUpdate u => s.latestUpdateTimestamp < u.timestamp
  | .nodeAnnouncement _ => True

def FreshMessage (s : GossipState) : GossipMessage → Prop
  | .channelAnnouncement a =>
      ∀ b ∈ s.announcements, b.shortChannelId ≠ a.shortChannelId
  | .channelUpdate u =>
      ∀ v ∈ s.updates,
        ¬ (v.shortChannelId = u.shortChannelId ∧ v.direction = u.direction)
  | .nodeAnnouncement _ => True
```

### 3.3 Reachability, invariant, and store-level `RT-01` theorems

```lean
inductive ReachableCanonicalStore (verify : SigVerifier) :
    CanonicalStore → Prop
  | empty (nodeKeyOf : NodeId → PubKey) :
      ReachableCanonicalStore verify
        { gossip := ⟨[], [], []⟩, nodeKeyOf := nodeKeyOf }
  | step {cs : CanonicalStore} {m : GossipMessage} :
      ReachableCanonicalStore verify cs →
        ReachableCanonicalStore verify (applyGossipCanonicalStore verify cs m)

structure CanonicalStoreAdmitted (verify : SigVerifier)
    (cs : CanonicalStore) : Prop where
  storeValid : StoreAnnouncementsValid verify cs.gossip
  updatesAttributed : StoreUpdatesDirectionallyAttributed verify cs.gossip
  nodeKeys : GossipState.NodeKeyConsistent cs.nodeKeyOf cs.gossip
  canonical : CanonicalAnnouncements cs.gossip.announcements
  updatesSlotUnique : UpdatesSlotUnique cs.gossip.updates

theorem admitGossipCanonical_gossip_view_irrel (verify : SigVerifier)
    (g : GossipState) (k : NodeId → PubKey) (vs₁ vs₂ : List ChannelView)
    (m : GossipMessage) :
    (admitGossipCanonical verify
        { gossip := g, views := vs₁, nodeKeyOf := k } m).gossip =
      (admitGossipCanonical verify
        { gossip := g, views := vs₂, nodeKeyOf := k } m).gossip

theorem admitGossipCanonical_nodeKeyOf_view_irrel (verify : SigVerifier)
    (g : GossipState) (k : NodeId → PubKey) (vs₁ vs₂ : List ChannelView)
    (m : GossipMessage) :
    (admitGossipCanonical verify
        { gossip := g, views := vs₁, nodeKeyOf := k } m).nodeKeyOf =
      (admitGossipCanonical verify
        { gossip := g, views := vs₂, nodeKeyOf := k } m).nodeKeyOf

theorem reachableCanonicalStore_toNetwork {verify : SigVerifier}
    {cs : CanonicalStore} (h : ReachableCanonicalStore verify cs) :
    ∃ views : List ChannelView, ReachableCanonical verify
      { gossip := cs.gossip, views := views, nodeKeyOf := cs.nodeKeyOf }

theorem admitGossipCanonical_announcement_updates (verify : SigVerifier)
    (cs : CanonicalNetwork) (a : ChannelAnnellation) :
    (admitGossipCanonical verify cs (.channelAnnouncement a)).gossip.updates =
      cs.gossip.updates

theorem admitGossipCanonical_update_updates (verify : SigVerifier)
    (cs : CanonicalNetwork) (u : ChannelUpdate) :
    (admitGossipCanonical verify cs (.channelUpdate u)).gossip.updates =
      if u.signatureValid verify ∧
          cs.gossip.updateKeyAnnouncedDirectional u ∧
          UpdateSupersedes u cs.gossip.updates then
        insertUpdateCanonical u cs.gossip.updates
      else cs.gossip.updates

theorem admitGossipCanonical_node_updates (verify : SigVerifier)
    (cs : CanonicalNetwork) (n : NodeAnnouncement) :
    (admitGossipCanonical verify cs (.nodeAnnouncement n)).gossip.updates =
      cs.gossip.updates

theorem reachableCanonical_updates_slotUnique {verify : SigVerifier}
    {cs : CanonicalNetwork} (h : ReachableCanonical verify cs) :
    UpdatesSlotUnique cs.gossip.updates

theorem reachableCanonicalStore_invariant {verify : SigVerifier}
    {cs : CanonicalStore} (h : ReachableCanonicalStore verify cs) :
    CanonicalStoreAdmitted verify cs

theorem reachableCanonicalStore_store_valid {verify : SigVerifier}
    {cs : CanonicalStore} (h : ReachableCanonicalStore verify cs) :
    StoreAnnouncementsValid verify cs.gossip

theorem reachableCanonicalStore_updates_directional {verify : SigVerifier}
    {cs : CanonicalStore} (h : ReachableCanonicalStore verify cs) :
    StoreUpdatesDirectionallyAttributed verify cs.gossip

theorem reachableCanonicalStore_nodeKeyConsistent {verify : SigVerifier}
    {cs : CanonicalStore} (h : ReachableCanonicalStore verify cs) :
    GossipState.NodeKeyConsistent cs.nodeKeyOf cs.gossip

theorem reachableCanonicalStore_canonical {verify : SigVerifier}
    {cs : CanonicalStore} (h : ReachableCanonicalStore verify cs) :
    CanonicalAnnouncements cs.gossip.announcements

theorem reachableCanonicalStore_updates_slotUnique {verify : SigVerifier}
    {cs : CanonicalStore} (h : ReachableCanonicalStore verify cs) :
    UpdatesSlotUnique cs.gossip.updates

theorem reachableCanonicalStore_attribution_unique {verify : SigVerifier}
    {cs : CanonicalStore} (h : ReachableCanonicalStore verify cs)
    {u v : ChannelUpdate} (hu : u ∈ cs.gossip.updates)
    (hv : v ∈ cs.gossip.updates)
    (hscid : u.shortChannelId = v.shortChannelId)
    (hdir : u.direction = v.direction) :
    u.signingKey = v.signingKey
```

### 3.4 Shape and refinement square

```lean
theorem canonicalStoreShape_announcements_nodup {s : GossipState}
    (h : CanonicalStoreShape s) : s.announcements.Nodup

theorem canonicalStoreShape_announcements_canonical {s : GossipState}
    (h : CanonicalStoreShape s) : CanonicalAnnouncements s.announcements

theorem canonicalStoreShape_updates_nodup {s : GossipState}
    (h : CanonicalStoreShape s) : s.updates.Nodup

theorem canonicalStoreShape_updates_slotUnique {s : GossipState}
    (h : CanonicalStoreShape s) : UpdatesSlotUnique s.updates

theorem selectAnnouncements_insertReplacing_of_shape {s : GossipState}
    (h : CanonicalStoreShape s) (a : ChannelAnnellation) :
    selectAnnouncements (insertReplacing a s.announcements) =
      insertReplacing a s.announcements

theorem selectUpdates_insertUpdateCanonical_of_shape {s : GossipState}
    (h : CanonicalStoreShape s) (u : ChannelUpdate) :
    selectUpdates (insertUpdateCanonical u s.updates) =
      insertUpdateCanonical u s.updates

theorem reachableCanonicalStore_shape {verify : SigVerifier}
    {cs : CanonicalStore} (h : ReachableCanonicalStore verify cs) :
    CanonicalStoreShape cs.gossip

theorem insertReplacing_eq_cons_of_fresh {a : ChannelAnnellation}
    {l : List ChannelAnnellation}
    (h : ∀ b ∈ l, b.shortChannelId ≠ a.shortChannelId) :
    insertReplacing a l = a :: l

theorem insertUpdateCanonical_eq_cons_of_fresh {u : ChannelUpdate}
    {l : List ChannelUpdate}
    (h : ∀ v ∈ l,
      ¬ (v.shortChannelId = u.shortChannelId ∧ v.direction = u.direction)) :
    insertUpdateCanonical u l = u :: l

theorem canonicalStoreView_applyGossip_eq_canonicalStore
    (verify : SigVerifier) (cs : CanonicalStore) (m : GossipMessage)
    (hshape : CanonicalStoreShape cs.gossip)
    (hgate : CanonicalMessageAdmitted verify cs m)
    (hclock : RawClockAdmits cs.gossip m) :
    canonicalStoreView (applyGossip cs.gossip m) =
      (applyGossipCanonicalStore verify cs m).gossip

theorem applyGossip_eq_canonicalStore_of_fresh
    (verify : SigVerifier) (cs : CanonicalStore) (m : GossipMessage)
    (hgate : CanonicalMessageAdmitted verify cs m)
    (hclock : RawClockAdmits cs.gossip m)
    (hfresh : FreshMessage cs.gossip m) :
    applyGossip cs.gossip m =
      (applyGossipCanonicalStore verify cs m).gossip

theorem canonicalStoreShape_applyGossipCanonicalStore
    (verify : SigVerifier) (cs : CanonicalStore) (m : GossipMessage)
    (hshape : CanonicalStoreShape cs.gossip)
    (hgate : CanonicalMessageAdmitted verify cs m) :
    CanonicalStoreShape (applyGossipCanonicalStore verify cs m).gossip

theorem canonicalStoreView_applyGossip_eq_of_fresh
    (verify : SigVerifier) (cs : CanonicalStore) (m : GossipMessage)
    (hshape : CanonicalStoreShape cs.gossip)
    (hgate : CanonicalMessageAdmitted verify cs m)
    (hclock : RawClockAdmits cs.gossip m)
    (hfresh : FreshMessage cs.gossip m) :
    canonicalStoreView (applyGossip cs.gossip m) =
      (applyGossipCanonicalStore verify cs m).gossip
```

### 3.5 Boundary, impossibility, and preserved counterexamples

```lean
theorem canonical_admission_strictly_weaker_than_raw_clock :
    ∃ (verify : SigVerifier) (cs : CanonicalStore) (u : ChannelUpdate),
      ReachableCanonicalStore verify cs ∧
        CanonicalMessageAdmitted verify cs (.channelUpdate u) ∧
          ¬ RawClockAdmits cs.gossip (.channelUpdate u) ∧
            (applyGossipCanonicalStore verify cs (.channelUpdate u)).gossip.updates =
              u :: cs.gossip.updates ∧
              applyGossip cs.gossip (.channelUpdate u) = cs.gossip ∧
                u ∉ cs.gossip.updates

theorem no_canonical_preserving_raw_announcement_extension :
    ¬ ∃ F : GossipState → GossipMessage → GossipState,
      (∀ (s : GossipState) (a : ChannelAnnellation),
        F s (.channelAnnouncement a) = applyGossip s (.channelAnnouncement a)) ∧
      (∀ s : GossipState, CanonicalAnnouncements s.announcements →
        ∀ m : GossipMessage,
          CanonicalAnnouncements (F s m).announcements)

theorem canonicalStoreView_resolves_conflict :
    let s : GossipState := ⟨[annConflict, ann1], [], []⟩
    ¬ CanonicalAnnouncements s.announcements ∧
      CanonicalAnnouncements (canonicalStoreView s).announcements ∧
        (canonicalStoreView s).announcements = [annConflict]

theorem raw_conflicting_announcement_counterexample_preserved :
    ∃ (s : GossipState) (a : ChannelAnnellation),
      ¬ CanonicalAnnouncements
        (applyGossip s (.channelAnnouncement a)).announcements

theorem ambiguous_without_canonical_preserved :
    ∃ (s : GossipState) (u v : ChannelUpdate),
      ¬ CanonicalAnnouncements s.announcements ∧
        u.shortChannelId = v.shortChannelId ∧ u.direction = v.direction ∧
          s.updateKeyAnnouncedDirectional u ∧
            s.updateKeyAnnouncedDirectional v ∧ u.signingKey ≠ v.signingKey

theorem canonical_conflicting_announcement_rejection_preserved :
    ∃ (verify : SigVerifier) (cs : CanonicalNetwork)
      (a : ChannelAnnellation),
      ReachableCanonical verify cs ∧
        ¬ cs.gossip.CompatibleWithStore a ∧
          admitGossipCanonical verify cs (.channelAnnouncement a) = cs
```

`annConflict` and `ann1` in `canonicalStoreView_resolves_conflict` are private
concrete witnesses (two announcements with the same `short_channel_id` and
different endpoint keys); the statement is fully existential in content.

## 4. What is new in `LnLean/Routing/Gossip.lean`

The `374` added lines are one section inserted before `end LnLean.Routing`, after
the existing `insertUpdateCanonical_newest` theorem.  Nothing existing was
moved or changed; the rotation theorems `nodeKeyConsistent_rekey` and
`canonical_rekey` remain at their original location.

Added primitives:

* `UpdatesSlotUnique` and `updatesSlotUnique_nil`,
  `updatesSlotUnique_insertUpdateCanonical`;
* `selectUpdates` and `updatesSlotUnique_selectUpdates`,
  `mem_selectUpdates`, `exists_mem_selectUpdates_of_mem`, `selectUpdates_nodup`,
  `selectUpdates_of_nodup_slotUnique`, `selectUpdates_idempotent`;
* `selectAnnouncements` and `canonical_selectAnnouncements`,
  `mem_selectAnnouncements`, `exists_mem_selectAnnouncements_of_mem`,
  `selectAnnouncements_nodup`, `selectAnnouncements_of_nodup_canonical`,
  `selectAnnouncements_idempotent`;
* `canonicalStoreView` with component simp lemmas,
  `canonicalStoreView_canonical`, `canonicalStoreView_updates_slotUnique`,
  `canonicalStoreView_idempotent`;
* `CanonicalStoreShape`, `canonicalStoreView_eq_self_iff`,
  `canonicalStoreShape_of_nodup`;
* the three refinement-square lemmas
  `canonicalStoreView_applyGossip_announcements`,
  `canonicalStoreView_applyGossip_updates`,
  `canonicalStoreView_applyGossip_nodeAnnouncements`.

The existing oldest-record-wins selector `dedupAnnouncements` /
`canonicalView` is unchanged.  The new `selectAnnouncements` keeps the
head-most (newest) record because gossip lists are newest-first and because
`insertReplacing` is the canonical transition's replacement operation.

## 5. Axiom audit

Command:

```sh
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake env lean /tmp/opencode/s7rt_axioms.lean
```

Every audited theorem depends only on the allowed axioms `propext`,
`Quot.sound`, and `Classical.choice`.  Exact sets:

| Theorem | Axioms |
| --- | --- |
| `applyGossipCanonicalStore_gossip_toNetwork` | `propext`, `Classical.choice`, `Quot.sound` |
| `applyGossipCanonicalStore_nodeKeyOf_toNetwork` | `propext`, `Classical.choice`, `Quot.sound` |
| `reachableCanonical_updates_slotUnique` | `propext`, `Classical.choice`, `Quot.sound` |
| `reachableCanonicalStore_toNetwork` | `propext`, `Classical.choice`, `Quot.sound` |
| `reachableCanonicalStore_invariant` | `propext`, `Classical.choice`, `Quot.sound` |
| `reachableCanonicalStore_updates_directional` | `propext`, `Classical.choice`, `Quot.sound` |
| `reachableCanonicalStore_attribution_unique` | `propext`, `Classical.choice`, `Quot.sound` |
| `reachableCanonicalStore_shape` | `propext`, `Classical.choice`, `Quot.sound` |
| `canonicalStoreShape_applyGossipCanonicalStore` | `propext`, `Classical.choice`, `Quot.sound` |
| `canonicalStoreView_applyGossip_eq_canonicalStore` | `propext`, `Classical.choice`, `Quot.sound` |
| `applyGossip_eq_canonicalStore_of_fresh` | `propext`, `Classical.choice`, `Quot.sound` |
| `canonicalStoreView_applyGossip_eq_of_fresh` | `propext`, `Classical.choice`, `Quot.sound` |
| `canonical_admission_strictly_weaker_than_raw_clock` | `propext`, `Classical.choice`, `Quot.sound` |
| `no_canonical_preserving_raw_announcement_extension` | `propext`, `Quot.sound` |
| `canonicalStoreView_resolves_conflict` | `propext`, `Quot.sound` |
| `raw_conflicting_announcement_counterexample_preserved` | `propext` |
| `ambiguous_without_canonical_preserved` | `propext`, `Classical.choice`, `Quot.sound` |
| `canonical_conflicting_announcement_rejection_preserved` | `propext`, `Classical.choice`, `Quot.sound` |

No other axiom is used.

## 6. Forbidden-construct scan

```sh
grep -nE "\b(sorry|axiom|admit|native_decide|unsafe|implemented_by)\b" \
  LnLean/Routing/Gossip.lean \
  LnLean/Proofs/Routing/GossipRawRefinementTargets.lean
```

Matches are comments only:

* `LnLean/Routing/Gossip.lean:90` — pre-existing prose “never an axiom”;
* `LnLean/Proofs/Routing/GossipRawRefinementTargets.lean:76-77` — this
  module's own “No `sorry`, no `axiom`, …” declaration;
* `LnLean/Proofs/Routing/GossipRawRefinementTargets.lean:686` — prose
  “can still admit the update”.

There is no `sorry`, `axiom`, `admit`, `native_decide`, `unsafe`, or
`@[implemented_by]` in executable declaration bodies.  The only classical
choice is `Classical.propDecidable` inside the `noncomputable` canonical
transition, inherited from the wave-6 design.

## 7. Scope caveats

* **The wrapper excludes views.**  `CanonicalStore` carries only the gossip
  store and registration map; `CanonicalStore.toNetwork` uses `views := []`.
  `admitGossipCanonical_gossip_view_irrel` and
  `admitGossipCanonical_nodeKeyOf_view_irrel` prove that views do not affect
  the store projection.  The graph/endpoint theorem
  `reachableCanonical_directional_key_endpoint` remains a `CanonicalNetwork`
  statement, not a store statement.
* **The refinement is observational, not literal, in general.**
  `canonicalStoreView_applyGossip_eq_canonicalStore` concludes equality after
  `canonicalStoreView`.  Literal equality additionally needs `FreshMessage`;
  without freshness, raw append and canonical replacement differ by exactly the
  old same-channel/same-slot record.
* **The raw global clock is not a per-slot clock.**  The raw store has one
  `latestUpdateTimestamp`; the canonical gate is `UpdateSupersedes` on the
  incoming `(short_channel_id, direction)` slot.  The boundary theorem exhibits
  a reachable state where the canonical path accepts a lower-timestamp update
  on another channel while raw `applyUpdate` ignores it.  Consequently
  `RawClockAdmits` is a genuine extra hypothesis in the refinement square.
* **The impossibility theorem constrains announcements only.**  It says that
  keeping raw append semantics for `channel_announcement` precludes preserving
  `CanonicalAnnouncements` from the empty store.  It does not claim an
  impossibility for update/node behaviour, and it does not by itself rule out a
  transition that changes announcement semantics.
* **Node announcements are not canonicalised.**  `canonicalStoreView` leaves
  `nodeAnnouncements` untouched, matching wave 6 and the `RT-02` caveat.  A
  node-record replacement policy remains future work.
* **Admission policy is still the wave-6 model.**  `CompatibleWithStore` is a
  node-key registration policy, not a timestamp/epoch or gossip-dissemination
  model.  `UpdatesAuthorizedBy` is an explicit replacement-safety gate, not a
  statement about update resubmission.
* **No cryptographic claim.**  `SigVerifier` is abstract; signature validity is
  `verify key digest sig = true`, and unforgeability remains assumptions
  C3/C4/C8 in `docs/ASSUMPTIONS.md`.
* **No network/liveness/chain/UTXO/rate-limit claim.**

## 8. Integration steps (not performed; shared files are outside lane scope)

1. Add to the root aggregator (`LnLean.lean`):
   `import LnLean.Proofs.Routing.GossipRawRefinementTargets`.
2. If wave-7 integration tracks obligations/anchors, add entries for:
   `reachableCanonicalStore_invariant`,
   `reachableCanonicalStore_updates_directional`,
   `reachableCanonicalStore_attribution_unique`,
   `reachableCanonicalStore_shape`,
   `canonicalStoreView_applyGossip_eq_canonicalStore`,
   `applyGossip_eq_canonicalStore_of_fresh`,
   `canonical_admission_strictly_weaker_than_raw_clock`,
   `no_canonical_preserving_raw_announcement_extension`,
   `canonicalStoreView_resolves_conflict`.
3. Do **not** replace or alias raw `applyGossip` with
   `applyGossipCanonicalStore`; the impossibility theorem is the explicit reason.
   Use `reachableCanonicalStore_*` only for stores obtained through
   `ReachableCanonicalStore`.
4. If a later wave adds a per-slot clock to the raw store, replace
   `RawClockAdmits` with that per-slot condition and re-prove
   `canonicalStoreView_applyGossip_eq_canonicalStore`; the rest of the wrapper
   is clock-agnostic.
5. For graph-edge consumers, continue to use the wave-6
   `reachableCanonical_directional_key_endpoint`; the new store-level theorem is
   the attribution component, not a replacement for the view-backed endpoint
   statement.

## 9. Blockers

None.  The four prescribed modules build cleanly under the shared lock, the
axiom audit is within the allowed set, and no forbidden construct appears in a
declaration body.

## 10. Parent summary

* `RT-01` is resolved in the only sound direction: raw `applyGossip` is **not**
  a function refinement of canonical admission.  A store wrapper
  `applyGossipCanonicalStore` is proved to have exactly the wave-6 gossip/key
  projection, and the sharp refinement square holds on canonical-shaped stores
  under the admission gates and the raw global clock.
* Literal raw/canonical agreement is proved on the common fresh-channel /
  fresh-slot domain; the per-slot vs global-clock gap is exhibited by a
  reachable boundary witness, and an impossibility theorem rules out preserving
  canonical announcements while keeping raw announcement append semantics.
* Every reachable canonical store satisfies the extended invariant (signature
  validity, direction-keyed update attribution, node-key consistency,
  canonicality, slot uniqueness) with **no** caller-supplied consistency
  hypotheses; store-level attribution uniqueness is derived.
* All four required modules build (`13` jobs, `RC=0`); the new module and the
  additive `Gossip.lean` section are warning-free; all audited theorems use only
  `propext`, `Quot.sound`, and `Classical.choice`.
