# S6-GOSSIP-DERIVE — canonicalising gossip admission derives `RT-02` / `RT-01`

**Lane:** `S6-GOSSIP-DERIVE`
**Issues:** `RT-02` (canonicalising admission), `RT-01` (derived key attribution)
**Worktree:** `/home/ubuntu/ln-lean-repair`
**Base:** `repair/integrated` @ `201a0a0`
**Toolchain:** `leanprover/lean4:v4.35.0`
**Owned files changed:**

* `LnLean/Routing/Gossip.lean` — additive only, `339` inserted / `0` deleted,
* `LnLean/Proofs/Routing/GossipCanonicalTargets.lean` — new, `1007` lines,
* `agents/reports/swarm6/S6-GOSSIP-DERIVE.md` — this report.

No Git write was performed.

## 1. Verdict

`RT-02` is addressed by a new, explicit canonicalising admission transition
`admitGossipCanonical`.  Reachability under that transition is closed by
`ReachableCanonical`, and the invariant `CanonicalAdmitted` is proved for every
reachable state.  Both wave-5 hypotheses are now **derived**, not caller
supplied:

* `reachableCanonical_nodeKeyConsistent` produces
  `GossipState.NodeKeyConsistent cs.nodeKeyOf cs.gossip`;
* `reachableCanonical_canonical` produces
  `CanonicalAnnouncements cs.gossip.announcements`.

Consequently the wave-5 direction-keyed endpoint theorem is restated with **no**
consistency/canonicality hypotheses:

```lean
reachableCanonical_directional_key_endpoint :
  ReachableCanonical verify cs →
  ∀ e ∈ cs.toNetwork.graph.edges, ∀ u ∈ cs.gossip.updates,
    u.shortChannelId = e.shortChannelId →
      u.signatureValid verify ∧
        u.signingKey =
          (if u.direction then cs.nodeKeyOf e.node2
            else cs.nodeKeyOf e.node1)
```

Same-channel/same-direction stored updates also have a unique signing key
(`reachableCanonical_attribution_unique`), again with canonicality derived from
reachability.

The transition models:

* **Announcement supersession by `short_channel_id`** (`insertReplacing`), with
  the view replaced in step (`insertViewCanonical`) and both endpoint keys
  registered (`bindNodeKeys`).  Admission is gated on all four BOLT 7
  signatures, distinct endpoints, `CompatibleWithStore` (no node rebinding), and
  `UpdatesAuthorizedBy` (the replacement still authorises every stored update
  for that channel).
* **Update supersession by `(short_channel_id, direction)`**
  (`insertUpdateCanonical`), gated on signature validity, direction-keyed
  announcement attribution, and `UpdateSupersedes` (strictly newer timestamp).
* **Key rotation as a registration-only operation**
  (`rotateNodeKey` / `rekeyAnnouncement` / `rekeyStore`).  The positive
  registration theorem is paired with an explicit boundary theorem showing
  update attribution is *not* preserved unless the stored update is re-signed.

Raw `applyGossip`, `GossipState.applyUpdate`, and the wave-4/5 attributed
transitions are untouched.  The wave-4/5 counterexamples are re-exported by
reference and remain valid.

## 2. Required build

Command (exactly the lane-prescribed form):

```sh
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Routing.Gossip \
    LnLean.Proofs.Routing.GossipCanonicalTargets \
    LnLean.Proofs.Routing.GossipKeyConsistencyTargets
```

Result:

```text
✔ [12/12] Built LnLean.Proofs.Routing.GossipCanonicalTargets
Build completed successfully (12 jobs).
RC=0
```

`0` warnings in `LnLean/Routing/Gossip.lean` and
`LnLean/Proofs/Routing/GossipCanonicalTargets.lean`.  The only warnings in the
build are pre-existing `if_pos`/`if_neg` deprecations in
`LnLean/Proofs/Routing/GossipProps.lean`.  No full `lake build` was run.

## 3. Exact signatures

### 3.1 Additions to `LnLean/Routing/Gossip.lean`

All declarations below are root-level in `LnLean.Routing` (the `GossipState`
namespace is closed before `insertReplacing`).

```lean
def insertReplacing (a : ChannelAnnellation)
    (l : List ChannelAnnellation) : List ChannelAnnellation

theorem mem_insertReplacing_iff {a b : ChannelAnnellation}
    {l : List ChannelAnnellation} :
    b ∈ insertReplacing a l ↔
      b = a ∨ (b ∈ l ∧ b.shortChannelId ≠ a.shortChannelId)

theorem mem_insertReplacing_of_mem_of_ne {a b : ChannelAnnellation}
    {l : List ChannelAnnellation} (hb : b ∈ l)
    (hne : b.shortChannelId ≠ a.shortChannelId) :
    b ∈ insertReplacing a l

theorem mem_of_mem_insertReplacing_of_ne {a b : ChannelAnnellation}
    {l : List ChannelAnnellation} (h : b ∈ insertReplacing a l)
    (hne : b ≠ a) : b ∈ l

theorem canonical_insertReplacing {l : List ChannelAnnellation}
    (hc : CanonicalAnnouncements l) (a : ChannelAnnellation) :
    CanonicalAnnouncements (insertReplacing a l)

-- namespace GossipState
def CompatibleWithStore (s : GossipState) (a : ChannelAnnellation) : Prop :=
  ∀ b ∈ s.announcements,
    (b.node1 = a.node1 → b.nodeKey1 = a.nodeKey1) ∧
    (b.node2 = a.node1 → b.nodeKey2 = a.nodeKey1) ∧
    (b.node1 = a.node2 → b.nodeKey1 = a.nodeKey2) ∧
    (b.node2 = a.node2 → b.nodeKey2 = a.nodeKey2)
-- end GossipState

def NodeKeyAgreement (nodeKeyOf : NodeId → PubKey)
    (l : List ChannelAnnellation) : Prop :=
  ∀ a ∈ l, nodeKeyOf a.node1 = a.nodeKey1 ∧
    nodeKeyOf a.node2 = a.nodeKey2

theorem nodeKeyConsistent_iff_agreement (nodeKeyOf : NodeId → PubKey)
    (s : GossipState) :
    GossipState.NodeKeyConsistent nodeKeyOf s ↔
      NodeKeyAgreement nodeKeyOf s.announcements

def bindNodeKeys (nodeKeyOf : NodeId → PubKey) (a : ChannelAnnellation) :
    NodeId → PubKey :=
  fun n => if n = a.node1 then a.nodeKey1
    else if n = a.node2 then a.nodeKey2 else nodeKeyOf n

@[simp] theorem bindNodeKeys_node1 (nodeKeyOf : NodeId → PubKey)
    (a : ChannelAnnellation) :
    bindNodeKeys nodeKeyOf a a.node1 = a.nodeKey1

theorem bindNodeKeys_node2 (nodeKeyOf : NodeId → PubKey)
    (a : ChannelAnnellation) (h : a.node1 ≠ a.node2) :
    bindNodeKeys nodeKeyOf a a.node2 = a.nodeKey2

theorem bindNodeKeys_of_ne (nodeKeyOf : NodeId → PubKey)
    (a : ChannelAnnellation) {n : NodeId} (h1 : n ≠ a.node1)
    (h2 : n ≠ a.node2) :
    bindNodeKeys nodeKeyOf a n = nodeKeyOf n

theorem nodeKeyAgreement_insertReplacing {nodeKeyOf : NodeId → PubKey}
    {s : GossipState} {a : ChannelAnnellation}
    (hc : NodeKeyAgreement nodeKeyOf s.announcements)
    (hcompat : s.CompatibleWithStore a)
    (hne : a.node1 ≠ a.node2) :
    NodeKeyAgreement (bindNodeKeys nodeKeyOf a)
      (insertReplacing a s.announcements)

theorem nodeKeyConsistent_insertReplacing {nodeKeyOf : NodeId → PubKey}
    {s : GossipState} {a : ChannelAnnellation}
    (hc : GossipState.NodeKeyConsistent nodeKeyOf s)
    (hcompat : s.CompatibleWithStore a)
    (hne : a.node1 ≠ a.node2) :
    GossipState.NodeKeyConsistent (bindNodeKeys nodeKeyOf a)
      { s with announcements := insertReplacing a s.announcements }

def rotateNodeKey (nodeKeyOf : NodeId → PubKey) (n : NodeId) (k : PubKey) :
    NodeId → PubKey :=
  fun m => if m = n then k else nodeKeyOf m

def rekeyAnnouncement (a : ChannelAnnellation) (n : NodeId) (k : PubKey) :
    ChannelAnnellation :=
  { a with
    nodeKey1 := if a.node1 = n then k else a.nodeKey1
    nodeKey2 := if a.node2 = n then k else a.nodeKey2 }

def rekeyAnnouncements (l : List ChannelAnnellation) (n : NodeId)
    (k : PubKey) : List ChannelAnnellation

def rekeyStore (s : GossipState) (n : NodeId) (k : PubKey) : GossipState

@[simp] theorem rekeyStore_announcements (s : GossipState) (n : NodeId)
    (k : PubKey) :
    (rekeyStore s n k).announcements = rekeyAnnouncements s.announcements n k

theorem nodeKeyConsistent_rekey {nodeKeyOf : NodeId → PubKey}
    {s : GossipState} (h : GossipState.NodeKeyConsistent nodeKeyOf s)
    (n : NodeId) (k : PubKey) :
    GossipState.NodeKeyConsistent (rotateNodeKey nodeKeyOf n k)
      (rekeyStore s n k)

theorem canonical_rekey {l : List ChannelAnnellation}
    (hc : CanonicalAnnouncements l) (n : NodeId) (k : PubKey) :
    CanonicalAnnouncements (rekeyAnnouncements l n k)

def UpdateSupersedes (u : ChannelUpdate) (l : List ChannelUpdate) : Prop :=
  ∀ v ∈ l, v.shortChannelId = u.shortChannelId → v.direction = u.direction →
    v.timestamp < u.timestamp

def insertUpdateCanonical (u : ChannelUpdate) (l : List ChannelUpdate) :
    List ChannelUpdate :=
  u :: l.filter (fun v => decide (¬ (v.shortChannelId = u.shortChannelId ∧
    v.direction = u.direction)))

theorem mem_insertUpdateCanonical_iff {u v : ChannelUpdate}
    {l : List ChannelUpdate} :
    v ∈ insertUpdateCanonical u l ↔
      v = u ∨ (v ∈ l ∧ (v.shortChannelId ≠ u.shortChannelId ∨
        v.direction ≠ u.direction))

theorem insertUpdateCanonical_slot_unique (u : ChannelUpdate)
    (l : List ChannelUpdate) :
    ∀ v ∈ insertUpdateCanonical u l,
      v.shortChannelId = u.shortChannelId → v.direction = u.direction → v = u

theorem insertUpdateCanonical_newest {u : ChannelUpdate}
    {l : List ChannelUpdate} (_h : UpdateSupersedes u l) :
    ∀ v ∈ insertUpdateCanonical u l,
      v.shortChannelId = u.shortChannelId → v.direction = u.direction →
        v.timestamp ≤ u.timestamp
```

### 3.2 Transition and reachable invariant

```lean
structure CanonicalNetwork where
  gossip : GossipState
  views : List ChannelView
  nodeKeyOf : NodeId → PubKey

namespace CanonicalNetwork
def toNetwork (cs : CanonicalNetwork) : GossipNetwork
def graph (cs : CanonicalNetwork) : Graph
end CanonicalNetwork

def UpdatesAuthorizedBy (s : GossipState) (a : ChannelAnnellation) : Prop :=
  ∀ u ∈ s.updates, u.shortChannelId = a.shortChannelId →
    a.attributesKeyForDirection u.direction u.signingKey

def insertViewCanonical (v : ChannelView) (vs : List ChannelView) :
    List ChannelView

theorem mem_insertViewCanonical_iff {v w : ChannelView}
    {vs : List ChannelView} :
    w ∈ insertViewCanonical v vs ↔ w = v ∨ (w ∈ vs ∧ w.scid ≠ v.scid)

theorem mem_insertViewCanonical_of_mem_of_ne {v w : ChannelView}
    {vs : List ChannelView} (hw : w ∈ vs) (hne : w.scid ≠ v.scid) :
    w ∈ insertViewCanonical v vs

noncomputable def admitGossipCanonical (verify : SigVerifier)
    (cs : CanonicalNetwork) : GossipMessage → CanonicalNetwork
  | .channelAnnouncement a =>
      if a.signaturesValid verify ∧ a.node1 ≠ a.node2 ∧
          cs.gossip.CompatibleWithStore a ∧
          UpdatesAuthorizedBy cs.gossip a then
        { gossip := { cs.gossip with
            announcements := insertReplacing a cs.gossip.announcements }
          views := insertViewCanonical (admittedChannelView a) cs.views
          nodeKeyOf := bindNodeKeys cs.nodeKeyOf a }
      else cs
  | .channelUpdate u =>
      if u.signatureValid verify ∧
          cs.gossip.updateKeyAnnouncedDirectional u ∧
          UpdateSupersedes u cs.gossip.updates then
        { gossip := { cs.gossip with
            updates := insertUpdateCanonical u cs.gossip.updates }
          views := cs.views.map fun v => v.applyUpdate u
          nodeKeyOf := cs.nodeKeyOf }
      else cs
  | .nodeAnnouncement n =>
      if n.signatureValid verify then
        { gossip := { cs.gossip with
            nodeAnnouncements := n :: cs.gossip.nodeAnnouncements }
          views := cs.views
          nodeKeyOf := cs.nodeKeyOf }
      else cs
```

The four branch equations are public:

```lean
theorem admitGossipCanonical_announcement_of_admitted (verify : SigVerifier)
    (cs : CanonicalNetwork) (a : ChannelAnnellation)
    (h : a.signaturesValid verify ∧ a.node1 ≠ a.node2 ∧
      cs.gossip.CompatibleWithStore a ∧
      UpdatesAuthorizedBy cs.gossip a) :
    admitGossipCanonical verify cs (.channelAnnouncement a) =
      { gossip := { cs.gossip with
          announcements := insertReplacing a cs.gossip.announcements }
        views := insertViewCanonical (admittedChannelView a) cs.views
        nodeKeyOf := bindNodeKeys cs.nodeKeyOf a }

theorem admitGossipCanonical_announcement_of_rejected (verify : SigVerifier)
    (cs : CanonicalNetwork) (a : ChannelAnnellation)
    (h : ¬ (a.signaturesValid verify ∧ a.node1 ≠ a.node2 ∧
      cs.gossip.CompatibleWithStore a ∧
      UpdatesAuthorizedBy cs.gossip a)) :
    admitGossipCanonical verify cs (.channelAnnouncement a) = cs

theorem admitGossipCanonical_update_of_admitted (verify : SigVerifier)
    (cs : CanonicalNetwork) (u : ChannelUpdate)
    (h : u.signatureValid verify ∧
      cs.gossip.updateKeyAnnouncedDirectional u ∧
      UpdateSupersedes u cs.gossip.updates) :
    admitGossipCanonical verify cs (.channelUpdate u) =
      { gossip := { cs.gossip with
          updates := insertUpdateCanonical u cs.gossip.updates }
        views := cs.views.map fun v => v.applyUpdate u
        nodeKeyOf := cs.nodeKeyOf }

theorem admitGossipCanonical_update_of_rejected (verify : SigVerifier)
    (cs : CanonicalNetwork) (u : ChannelUpdate)
    (h : ¬ (u.signatureValid verify ∧
      cs.gossip.updateKeyAnnouncedDirectional u ∧
      UpdateSupersedes u cs.gossip.updates)) :
    admitGossipCanonical verify cs (.channelUpdate u) = cs

theorem admitGossipCanonical_node_of_valid (verify : SigVerifier)
    (cs : CanonicalNetwork) (n : NodeAnnouncement)
    (h : n.signatureValid verify) :
    admitGossipCanonical verify cs (.nodeAnnouncement n) =
      { gossip := { cs.gossip with
          nodeAnnouncements := n :: cs.gossip.nodeAnnouncements }
        views := cs.views
        nodeKeyOf := cs.nodeKeyOf }

theorem admitGossipCanonical_node_of_invalid (verify : SigVerifier)
    (cs : CanonicalNetwork) (n : NodeAnnouncement)
    (h : ¬ n.signatureValid verify) :
    admitGossipCanonical verify cs (.nodeAnnouncement n) = cs
```

```lean
structure CanonicalAdmitted (verify : SigVerifier) (cs : CanonicalNetwork) :
    Prop where
  storeValid : StoreAnnouncementsValid verify cs.gossip
  viewsBacked : ViewsBacked verify cs.toNetwork
  updatesAttributed : StoreUpdatesDirectionallyAttributed verify cs.gossip
  nodeKeys : GossipState.NodeKeyConsistent cs.nodeKeyOf cs.gossip
  canonical : cs.gossip.Canonical

inductive ReachableCanonical (verify : SigVerifier) :
    CanonicalNetwork → Prop
  | empty (nodeKeyOf : NodeId → PubKey) :
      ReachableCanonical verify
        { gossip := ⟨[], [], []⟩, views := [], nodeKeyOf := nodeKeyOf }
  | step {cs : CanonicalNetwork} {m : GossipMessage} :
      ReachableCanonical verify cs →
        ReachableCanonical verify (admitGossipCanonical verify cs m)

theorem updateKeyAnnouncedDirectional_of_announcements_eq
    {s t : GossipState} (h : t.announcements = s.announcements)
    {u : ChannelUpdate} (hk : s.updateKeyAnnouncedDirectional u) :
    t.updateKeyAnnouncedDirectional u

theorem nodeKeyConsistent_of_announcements_eq {nodeKeyOf : NodeId → PubKey}
    {s t : GossipState} (h : t.announcements = s.announcements)
    (hc : GossipState.NodeKeyConsistent nodeKeyOf s) :
    GossipState.NodeKeyConsistent nodeKeyOf t

theorem admitGossipCanonical_announcement_preserves (verify : SigVerifier)
    (cs : CanonicalNetwork) (a : ChannelAnnellation)
    (hinv : CanonicalAdmitted verify cs)
    (hgate : a.signaturesValid verify ∧ a.node1 ≠ a.node2 ∧
      cs.gossip.CompatibleWithStore a ∧
      UpdatesAuthorizedBy cs.gossip a) :
    CanonicalAdmitted verify
      (admitGossipCanonical verify cs (.channelAnnouncement a))

theorem admitGossipCanonical_update_preserves (verify : SigVerifier)
    (cs : CanonicalNetwork) (u : ChannelUpdate)
    (hinv : CanonicalAdmitted verify cs)
    (hgate : u.signatureValid verify ∧
      cs.gossip.updateKeyAnnouncedDirectional u ∧
      UpdateSupersedes u cs.gossip.updates) :
    CanonicalAdmitted verify
      (admitGossipCanonical verify cs (.channelUpdate u))

theorem admitGossipCanonical_node_preserves (verify : SigVerifier)
    (cs : CanonicalNetwork) (n : NodeAnnouncement)
    (hinv : CanonicalAdmitted verify cs) :
    CanonicalAdmitted verify
      (admitGossipCanonical verify cs (.nodeAnnouncement n))

theorem admitGossipCanonical_preserves (verify : SigVerifier)
    (cs : CanonicalNetwork) (m : GossipMessage)
    (hinv : CanonicalAdmitted verify cs) :
    CanonicalAdmitted verify (admitGossipCanonical verify cs m)

theorem reachableCanonical_invariant {verify : SigVerifier}
    {cs : CanonicalNetwork} (h : ReachableCanonical verify cs) :
    CanonicalAdmitted verify cs
```

### 3.3 Derived results

```lean
theorem reachableCanonical_nodeKeyConsistent {verify : SigVerifier}
    {cs : CanonicalNetwork} (h : ReachableCanonical verify cs) :
    GossipState.NodeKeyConsistent cs.nodeKeyOf cs.gossip

theorem reachableCanonical_canonical {verify : SigVerifier}
    {cs : CanonicalNetwork} (h : ReachableCanonical verify cs) :
    CanonicalAnnouncements cs.gossip.announcements

theorem reachableCanonical_store_valid {verify : SigVerifier}
    {cs : CanonicalNetwork} (h : ReachableCanonical verify cs) :
    StoreAnnouncementsValid verify cs.gossip

theorem reachableCanonical_views_backed {verify : SigVerifier}
    {cs : CanonicalNetwork} (h : ReachableCanonical verify cs) :
    ViewsBacked verify cs.toNetwork

theorem reachableCanonical_updates_directional {verify : SigVerifier}
    {cs : CanonicalNetwork} (h : ReachableCanonical verify cs) :
    StoreUpdatesDirectionallyAttributed verify cs.gossip

theorem canonical_endpoint_of_invariant
    (verify : SigVerifier) (cs : CanonicalNetwork)
    (hviews : ViewsBacked verify cs.toNetwork)
    (hupd : StoreUpdatesDirectionallyAttributed verify cs.gossip)
    (hcanon : CanonicalAnnouncements cs.gossip.announcements)
    (hnode : GossipState.NodeKeyConsistent cs.nodeKeyOf cs.gossip) :
    ∀ e ∈ cs.toNetwork.graph.edges, ∀ u ∈ cs.gossip.updates,
      u.shortChannelId = e.shortChannelId →
        u.signatureValid verify ∧
          u.signingKey =
            (if u.direction then cs.nodeKeyOf e.node2
              else cs.nodeKeyOf e.node1)

theorem reachableCanonical_directional_key_endpoint
    (verify : SigVerifier) (cs : CanonicalNetwork)
    (h : ReachableCanonical verify cs) :
    ∀ e ∈ cs.toNetwork.graph.edges, ∀ u ∈ cs.gossip.updates,
      u.shortChannelId = e.shortChannelId →
        u.signatureValid verify ∧
          u.signingKey =
            (if u.direction then cs.nodeKeyOf e.node2
              else cs.nodeKeyOf e.node1)

theorem reachableCanonical_attribution_unique {verify : SigVerifier}
    {cs : CanonicalNetwork} (h : ReachableCanonical verify cs)
    {u v : ChannelUpdate} (hu : u ∈ cs.gossip.updates)
    (hv : v ∈ cs.gossip.updates)
    (hscid : u.shortChannelId = v.shortChannelId)
    (hdir : u.direction = v.direction) :
    u.signingKey = v.signingKey
```

### 3.4 Rotation and non-vacuity witnesses

```lean
theorem key_rotation_preserves_registration_invariants
    (verify : SigVerifier) (cs : CanonicalNetwork)
    (h : ReachableCanonical verify cs) (n : NodeId) (k : PubKey) :
    GossipState.NodeKeyConsistent (rotateNodeKey cs.nodeKeyOf n k)
        (rekeyStore cs.gossip n k) ∧
      CanonicalAnnouncements (rekeyStore cs.gossip n k).announcements

theorem rotation_breaks_update_attribution :
    ∃ (nodeKeyOf : NodeId → PubKey) (s : GossipState) (n : NodeId)
      (k : PubKey) (u : ChannelUpdate),
      GossipState.NodeKeyConsistent nodeKeyOf s ∧
        GossipState.NodeKeyConsistent (rotateNodeKey nodeKeyOf n k)
          (rekeyStore s n k) ∧
          CanonicalAnnouncements (rekeyStore s n k).announcements ∧
            s.updateKeyAnnouncedDirectional u ∧
              ¬ (rekeyStore s n k).updateKeyAnnouncedDirectional u

theorem reachableCanonical_supersession_witness :
    ∃ (verify : SigVerifier) (cs : CanonicalNetwork),
      ReachableCanonical verify cs ∧
        GossipState.NodeKeyConsistent cs.nodeKeyOf cs.gossip ∧
          CanonicalAnnouncements cs.gossip.announcements ∧
            (∃ u v : ChannelUpdate, u ∈ cs.gossip.updates ∧
              v ∉ cs.gossip.updates ∧
                u.shortChannelId = v.shortChannelId ∧
                  u.direction = v.direction ∧
                    v.timestamp < u.timestamp ∧ u.timestamp ≠ v.timestamp)

theorem canonical_admission_rejects_conflicting_announcement :
    ∃ (verify : SigVerifier) (cs : CanonicalNetwork) (a : ChannelAnnellation),
      ReachableCanonical verify cs ∧
        ¬ cs.gossip.CompatibleWithStore a ∧
          admitGossipCanonical verify cs (.channelAnnouncement a) = cs

theorem reachableCanonical_stores_canonical_state :
    ∃ (verify : SigVerifier) (cs : CanonicalNetwork),
      ReachableCanonical verify cs ∧ cs.gossip.announcements ≠ [] ∧
        GossipState.NodeKeyConsistent cs.nodeKeyOf cs.gossip ∧
          CanonicalAnnouncements cs.gossip.announcements

theorem reachableCanonical_directional_endpoint_witness :
    ∃ (verify : SigVerifier) (cs : CanonicalNetwork),
      ReachableCanonical verify cs ∧ cs.toNetwork.graph.edges ≠ [] ∧
        ∀ e ∈ cs.toNetwork.graph.edges, ∀ u ∈ cs.gossip.updates,
          u.shortChannelId = e.shortChannelId →
            u.signatureValid verify ∧
              u.signingKey =
                (if u.direction then cs.nodeKeyOf e.node2
                  else cs.nodeKeyOf e.node1)
```

### 3.5 Preserved raw-store counterexamples

These are definitions by reference to the wave-4/5 results, not reproofs of a
changed transition:

```lean
theorem raw_store_still_not_canonical :
    ∃ (s : GossipState) (a : ChannelAnnellation),
      ¬ CanonicalAnnouncements
        (applyGossip s (.channelAnnouncement a)).announcements :=
  raw_applyGossip_accepts_conflicting_announcement

theorem ambiguous_without_canonical_still_holds :
    ∃ (s : GossipState) (u v : ChannelUpdate),
      ¬ CanonicalAnnouncements s.announcements ∧
        u.shortChannelId = v.shortChannelId ∧ u.direction = v.direction ∧
          s.updateKeyAnnouncedDirectional u ∧
            s.updateKeyAnnouncedDirectional v ∧ u.signingKey ≠ v.signingKey :=
  conflicting_announcements_ambiguous_without_canonical

theorem raw_store_still_unfiltered :
    ∃ (s : GossipState) (u : ChannelUpdate),
      ¬ s.updateKeyAnnouncedDirectional u ∧
        (applyGossip s (.channelUpdate u)).updates = u :: s.updates :=
  raw_applyGossip_accepts_directionally_unattributed_update
```

## 4. Axiom audit

Audit file: `/tmp/opencode/axcheck_s6_gossip.lean` (outside the repository).
Run with `lake env lean /tmp/opencode/axcheck_s6_gossip.lean`; exit code `0`.

Representative output:

```text
'LnLean.Routing.insertReplacing' does not depend on any axioms
'LnLean.Routing.nodeKeyConsistent_insertReplacing' depends on axioms: [propext, Quot.sound]
'LnLean.Routing.insertUpdateCanonical' does not depend on any axioms
'LnLean.Routing.insertUpdateCanonical_slot_unique' depends on axioms: [propext]
'LnLean.Routing.rotateNodeKey' does not depend on any axioms
'LnLean.Routing.nodeKeyConsistent_rekey' depends on axioms: [propext, Quot.sound]
'LnLean.Routing.canonical_rekey' depends on axioms: [propext, Quot.sound]
'...admitGossipCanonical' depends on axioms: [propext, Classical.choice, Quot.sound]
'...ReachableCanonical' depends on axioms: [propext, Classical.choice, Quot.sound]
'...reachableCanonical_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
'...reachableCanonical_nodeKeyConsistent' depends on axioms: [propext, Classical.choice, Quot.sound]
'...reachableCanonical_canonical' depends on axioms: [propext, Classical.choice, Quot.sound]
'...reachableCanonical_directional_key_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'...reachableCanonical_attribution_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'...key_rotation_preserves_registration_invariants' depends on axioms: [propext, Classical.choice, Quot.sound]
'...rotation_breaks_update_attribution' depends on axioms: [propext, Classical.choice, Quot.sound]
'...raw_store_still_not_canonical' depends on axioms: [propext]
'...raw_store_still_unfiltered' depends on axioms: [propext]
```

All audited declarations are within the allowed set
`{propext, Quot.sound, Classical.choice}`.  `Classical.choice` enters only
through `admitGossipCanonical`'s decidable comparison of public keys (the
`CompatibleWithStore` gate); no new axiom was introduced.

## 5. Forbidden-construct scan

```sh
grep -nwE "sorry|axiom|admit|native_decide|unsafe" \
  LnLean/Routing/Gossip.lean \
  LnLean/Proofs/Routing/GossipCanonicalTargets.lean
```

Only documentation hits:

* `Gossip.lean:90` — prose: “The function is a parameter, never an axiom.”
* `GossipCanonicalTargets.lean:85-86` — the lane-policy sentence in the module
  docstring.

No code occurrence of `sorry`, `admit`, `native_decide`, `unsafe`, or
`@[implemented_by]`.  Compiled-artifact check:

```text
strings .lake/build/lib/lean/LnLean/Routing/Gossip.olean | grep -c sorryAx
0
strings .lake/build/lib/lean/LnLean/Proofs/Routing/GossipCanonicalTargets.olean | grep -c sorryAx
0
```

## 6. Scope caveats

1. **The raw transition is unchanged.**  `applyGossip`, `GossipState.applyUpdate`,
   `applyUpdateAttributed`, `applyUpdateDirected`, and all wave-4/5 statements
   keep their exact signatures and append-only/filter-free behaviour.  The
   derived invariants hold for `ReachableCanonical`, not for arbitrary raw
   stores.  The three re-exported counterexamples make that explicit.

2. **Initial registration is arbitrary but fixed.**  `ReachableCanonical.empty`
   starts with any total `NodeId → PubKey` map and an empty store.  Consistency
   is then maintained by `CompatibleWithStore`/`bindNodeKeys`; the model does
   not prove that the initial map matches an out-of-band identity system.

3. **Signature gate is the existing abstract `SigVerifier`.**  Admission
   requires `signaturesValid` / `signatureValid`; actual ECDSA verification,
   BOLT 7 digest construction, and key ownership remain outside the model, as
   recorded in `docs/ASSUMPTIONS.md`.  The trust boundary is unchanged from
   waves 4/5.

4. **Announcement replacement is keyed by `short_channel_id` only.**  The gate
   `UpdatesAuthorizedBy` prevents a replacement from orphaning stored updates,
   but does not model chain/UTXO confirmation or capacity/endpoint
   re-validation beyond the announcement's own signature checks and endpoint
   distinctness.

5. **Node announcements are only signature-gated and append-only.**  They are
   not deduplicated, and they are not part of the `NodeId → PubKey`
   registration map.  `RT-02` concerns channel announcements; node-record
   canonicalisation remains future work.

6. **Rotation is registration-only.**  `rekeyAnnouncement` rewrites the two
   `nodeKey` fields but deliberately leaves the announcement signatures and
   digest untouched.  `key_rotation_preserves_registration_invariants` proves
   only `NodeKeyConsistent` and canonicality;
   `rotation_breaks_update_attribution` proves that a stored update signed by
   the old key stops being direction-attributed.  Re-signing and resubmission
   are explicit obligations, not hidden by the rotation theorem.

7. **Update supersession is per `(short_channel_id, direction)`.**  A newer
   update replaces that slot; the reverse direction and other channels are
   untouched.  Timestamps are `Nat` and the gate is strict `<`; timestamp
   wraparound and BOLT 7 `channel_flags` policy bits beyond direction are not
   modelled.

8. **`admitGossipCanonical` is `noncomputable`.**  It is a deterministic
   function of the state and message, but the registration gate compares
   `PubKey` values, so Lean synthesises `Classical.propDecidable`.  This is a
   representation choice, not an additional assumption; the axiom audit shows
   only `Classical.choice`.

9. **Views are canonicalised in step for channel announcements.**  Update
   admission maps `applyUpdate` over the existing views; it does not itself
   re-check view backing.  `CanonicalAdmitted.viewsBacked` is preserved by the
   update branch because the announcement list is unchanged and `applyUpdate`
   preserves the view's announcement identity.

## 7. Integration steps for the parent

1. **Root import.**  Add to `LnLean.lean`, next to
   `import LnLean.Proofs.Routing.GossipAttributionTargets`:

   ```lean
   import LnLean.Proofs.Routing.GossipCanonicalTargets
   ```

   The module imports `GossipKeyConsistencyTargets` (and transitively the
   wave-4/5 gossip modules), so no other new import is required for this lane.
   This lane did not edit `LnLean.lean`; the module builds green standalone.

2. **Catalog / traceability.**  Record `RT-02` as addressed by
   `reachableCanonical_invariant` (invariant closure),
   `reachableCanonical_nodeKeyConsistent`, and
   `reachableCanonical_canonical`.  For `RT-01`, target
   `reachableCanonical_directional_key_endpoint` as the main theorem and
   `reachableCanonical_attribution_unique` as the no-ambiguity companion.
   Keep `canonical_admission_rejects_conflicting_announcement`,
   `rotation_breaks_update_attribution`, and the three raw-store
   counterexamples as the boundary evidence.

3. **Audit module.**  Add `#print axioms` lines for at least
   `reachableCanonical_invariant`,
   `reachableCanonical_directional_key_endpoint`,
   `reachableCanonical_attribution_unique`,
   `key_rotation_preserves_registration_invariants`, and
   `rotation_breaks_update_attribution`.  The audit file used here is
   `/tmp/opencode/axcheck_s6_gossip.lean`.

4. **Suggested catalog scope note.**  “Reachable states of the canonicalising
   gossip transition maintain `NodeKeyConsistent` and
   `CanonicalAnnouncements` by construction: announcements replace by
   `short_channel_id` only when signature-valid, endpoint-distinct,
   registration-compatible, and still authorising stored updates; updates
   replace their `(short_channel_id, direction)` slot only when
   signature-valid, direction-attributed, and strictly newer.  The wave-5
   direction-keyed endpoint theorem therefore holds for reachable states with
   no consistency hypotheses.  Key rotation is modelled as registration only
   and does not preserve update attribution without re-signing.  Raw
   `applyGossip` remains append-only, unfiltered, and undeduplicated.”

5. **Generated indexes.**  Do not run `collect-obligations.py` or
   `collect-anchors.py` from this lane; the parent regenerates them after the
   root import and catalog edit.  No full `lake build` was run here.

6. **Relation to wave 5.**  This module is strictly additive on top of
   `GossipKeyConsistencyTargets`; it imports the wave-5 endpoint theorem and
   its counterexamples rather than weakening or restating them.  The wave-5
   hypotheses remain available as the conditional API
   (`canonical_endpoint_of_invariant`), while the reachable-state corollary
   removes them for canonical states.

## 8. Blockers

None.  The lane's build is green, the axiom audit is within policy, and the
forbidden-construct scan is clean.  All remaining items are integration steps
owned by the parent (root import, catalog/traceability/audit rows) or explicit
model boundaries listed in §6.

## 9. Parent summary

`S6-GOSSIP-DERIVE` closes `RT-02` with an additive canonicalising gossip
transition and derives both wave-5 invariants for reachable states.  The
direction-keyed `RT-01` endpoint theorem now holds for `ReachableCanonical`
without caller-supplied `NodeKeyConsistent` or `CanonicalAnnouncements`.
Announcements replace by `short_channel_id` under a four-part gate
(signatures, distinct endpoints, no rebinding, stored-update authorisation);
updates replace their directional slot only when signature-valid,
direction-attributed, and strictly newer.  Key rotation is registration-only,
with a mechanised boundary theorem showing re-signing is required to preserve
update attribution.  Raw `applyGossip` and all wave-4/5 counterexamples are
preserved unchanged.  Build `12/12` RC `0`; axiom audit only
`propext`/`Quot.sound`/`Classical.choice`; no forbidden constructs; no
blockers.  Parent action: root import, then catalog/traceability/audit updates.
