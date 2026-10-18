# S5-GOSSIP-ATTR2 — `RT-01`: direction-keyed signing, node-key consistency, announcement dedup

**Lane:** `S5-GOSSIP-ATTR2`
**Worktree:** `/home/ubuntu/ln-lean-repair`
**Branch / base:** `repair/integrated` @ `79a92ce` (wave-5 plan; code `74d6475`)
**Toolchain:** `leanprover/lean4:v4.35.0`
**Owned files changed:**

* `LnLean/Routing/Gossip.lean` (additive only, `511` inserted / `0` deleted),
* `LnLean/Proofs/Routing/GossipKeyConsistencyTargets.lean` (new),
* `agents/reports/swarm5/S5-GOSSIP-ATTR2.md` (this report, new).

## Verdict

The three remaining `RT-01` model gaps are addressed additively.

1. **Direction-keyed update signing.**
   `ChannelUpdate.direction` decodes BOLT 7 `channel_flags` bit 0, and
   `ChannelAnnellation.attributesKeyForDirection` selects `nodeKey1` for
   direction 0 and `nodeKey2` for direction 1.
   `GossipState.updateKeyAnnouncedDirectional` is the resulting strict
   refinement of the wave-4 undirected `updateKeyAnnounced`; the directed
   admission step `admitGossipDirected` uses it.

2. **`NodeId → PubKey` consistency.**
   `GossipState.NodeKeyConsistent nodeKeyOf` is the explicit invariant that a
   graph-node to wire-key map agrees with every stored announcement.  Under it
   (and the canonical-announcement invariant) the main theorem proves that a
   stored update for a reachable graph edge is signed by **the** endpoint key
   selected by its direction, not merely by one of the two keys.

3. **Announcement deduplication / canonical view.**
   `CanonicalAnnouncements`, `dedupAnnouncements`, and
   `GossipState.canonicalView` provide a store view with at most one
   announcement per `short_channel_id`.  The deduplicator is proved canonical,
   membership-preserving in both directions under the invariant, and
   attribution-preserving under the invariant.  A concrete counterexample
   shows that without the invariant, conflicting same-channel announcements
   really do attribute different direction-0 keys.

Preserved unchanged: raw `applyGossip`, `GossipState.applyUpdate`, the wave-4
`admitGossipAttributed` and `gossip_graph_edges_update_attributed`, and all raw
store counterexamples.  The raw store is still append-only, unfiltered, and
undeduplicated; the new module re-exhibits both raw gaps.

## 1. Exact additions to `LnLean/Routing/Gossip.lean`

All additions are appended after wave-4's `end GossipState`; no existing
signature or proof changed (`git diff --numstat` is `511 0`).

```lean
-- namespace ChannelUpdate
def direction (u : ChannelUpdate) : Bool :=
  u.channelFlags % 2 == 1

theorem direction_eq_true_iff (u : ChannelUpdate) :
    u.direction = true ↔ u.channelFlags % 2 = 1

theorem direction_eq_false_iff (u : ChannelUpdate) :
    u.direction = false ↔ u.channelFlags % 2 = 0

theorem direction_of_channelFlags_zero {u : ChannelUpdate}
    (h : u.channelFlags = 0) : u.direction = false

theorem direction_of_channelFlags_one {u : ChannelUpdate}
    (h : u.channelFlags = 1) : u.direction = true

-- namespace ChannelAnnellation
def attributesKeyForDirection (a : ChannelAnnellation) (direction : Bool)
    (key : PubKey) : Prop :=
  if direction then a.nodeKey2 = key else a.nodeKey1 = key

theorem attributesKeyForDirection_iff (a : ChannelAnnellation) (direction : Bool)
    (key : PubKey) :
    a.attributesKeyForDirection direction key ↔
      (direction = false ∧ a.nodeKey1 = key) ∨
        (direction = true ∧ a.nodeKey2 = key)

theorem attributesKeyForDirection_node1 (a : ChannelAnnellation) :
    a.attributesKeyForDirection false a.nodeKey1

theorem attributesKeyForDirection_node2 (a : ChannelAnnellation) :
    a.attributesKeyForDirection true a.nodeKey2

theorem attributesKeyForDirection_implies_attributesKey (a : ChannelAnnellation)
    (direction : Bool) (key : PubKey)
    (h : a.attributesKeyForDirection direction key) : a.attributesKey key

-- namespace GossipState
def updateKeyAnnouncedDirectional (s : GossipState) (u : ChannelUpdate) : Prop :=
  ∃ a ∈ s.announcements, a.shortChannelId = u.shortChannelId ∧
    a.attributesKeyForDirection u.direction u.signingKey

theorem updateKeyAnnouncedDirectional_iff (s : GossipState) (u : ChannelUpdate) :
    s.updateKeyAnnouncedDirectional u ↔
      ∃ a ∈ s.announcements, a.shortChannelId = u.shortChannelId ∧
        a.attributesKeyForDirection u.direction u.signingKey

theorem updateKeyAnnouncedDirectional_of_mem {s : GossipState}
    {u : ChannelUpdate} {a : ChannelAnnellation} (ha : a ∈ s.announcements)
    (hscid : a.shortChannelId = u.shortChannelId)
    (hkey : a.attributesKeyForDirection u.direction u.signingKey) :
    s.updateKeyAnnouncedDirectional u

theorem updateKeyAnnouncedDirectional_mono {s t : GossipState}
    {u : ChannelUpdate}
    (hsub : ∀ a ∈ s.announcements, a ∈ t.announcements)
    (h : s.updateKeyAnnouncedDirectional u) :
    t.updateKeyAnnouncedDirectional u

theorem updateKeyAnnouncedDirectional_implies_updateKeyAnnounced
    (s : GossipState) (u : ChannelUpdate)
    (h : s.updateKeyAnnouncedDirectional u) : s.updateKeyAnnounced u

theorem updateKeyAnnouncedDirectional_applyUpdate (s : GossipState)
    (u : ChannelUpdate) (h : s.updateKeyAnnouncedDirectional u) :
    (s.applyUpdate u).updateKeyAnnouncedDirectional u

noncomputable def applyUpdateDirected (s : GossipState) (verify : SigVerifier)
    (u : ChannelUpdate) : GossipState :=
  if u.signatureValid verify ∧ s.updateKeyAnnouncedDirectional u then
    s.applyUpdate u
  else s

theorem applyUpdateDirected_eq_applyUpdate_of_admitted (s : GossipState)
    (verify : SigVerifier) (u : ChannelUpdate)
    (hsig : u.signatureValid verify)
    (hk : s.updateKeyAnnouncedDirectional u) :
    s.applyUpdateDirected verify u = s.applyUpdate u

theorem applyUpdateDirected_eq_self_of_unannounced (s : GossipState)
    (verify : SigVerifier) (u : ChannelUpdate)
    (hk : ¬ s.updateKeyAnnouncedDirectional u) :
    s.applyUpdateDirected verify u = s

theorem applyUpdateDirected_change_requires (s : GossipState)
    (verify : SigVerifier) (u : ChannelUpdate)
    (h : s.applyUpdateDirected verify u ≠ s) :
    u.signatureValid verify ∧ s.updateKeyAnnouncedDirectional u

theorem applyUpdateDirected_change_requires_newer (s : GossipState)
    (verify : SigVerifier) (u : ChannelUpdate)
    (h : s.applyUpdateDirected verify u ≠ s) :
    s.latestUpdateTimestamp < u.timestamp

theorem applyUpdateDirected_announcements (s : GossipState)
    (verify : SigVerifier) (u : ChannelUpdate) :
    (s.applyUpdateDirected verify u).announcements = s.announcements

theorem updateKeyAnnouncedDirectional_applyUpdateDirected
    (s : GossipState) (verify : SigVerifier) (u : ChannelUpdate)
    (h : s.updateKeyAnnouncedDirectional u) :
    (s.applyUpdateDirected verify u).updateKeyAnnouncedDirectional u

theorem latestUpdateTimestamp_applyUpdateDirected_ge (s : GossipState)
    (verify : SigVerifier) (u : ChannelUpdate) :
    s.latestUpdateTimestamp ≤
      (s.applyUpdateDirected verify u).latestUpdateTimestamp

def NodeKeyConsistent (nodeKeyOf : NodeId → PubKey) (s : GossipState) : Prop :=
  ∀ a ∈ s.announcements, nodeKeyOf a.node1 = a.nodeKey1 ∧
    nodeKeyOf a.node2 = a.nodeKey2

theorem nodeKeyConsistent_empty (nodeKeyOf : NodeId → PubKey) :
    NodeKeyConsistent nodeKeyOf ⟨[], [], []⟩

theorem nodeKeyConsistent_mono {nodeKeyOf : NodeId → PubKey}
    {s t : GossipState}
    (hsub : ∀ a ∈ t.announcements, a ∈ s.announcements)
    (h : NodeKeyConsistent nodeKeyOf s) : NodeKeyConsistent nodeKeyOf t

theorem nodeKeyConsistent_applyUpdate {nodeKeyOf : NodeId → PubKey}
    (s : GossipState) (u : ChannelUpdate)
    (h : NodeKeyConsistent nodeKeyOf s) :
    NodeKeyConsistent nodeKeyOf (s.applyUpdate u)

theorem nodeKeyConsistent_node1_key_unique {nodeKeyOf : NodeId → PubKey}
    {s : GossipState} (h : NodeKeyConsistent nodeKeyOf s)
    {a b : ChannelAnnellation} (ha : a ∈ s.announcements)
    (hb : b ∈ s.announcements) (hnode : a.node1 = b.node1) :
    a.nodeKey1 = b.nodeKey1

theorem nodeKeyConsistent_node2_key_unique {nodeKeyOf : NodeId → PubKey}
    {s : GossipState} (h : NodeKeyConsistent nodeKeyOf s)
    {a b : ChannelAnnellation} (ha : a ∈ s.announcements)
    (hb : b ∈ s.announcements) (hnode : a.node2 = b.node2) :
    a.nodeKey2 = b.nodeKey2

-- namespace LnLean.Routing
def CanonicalAnnouncements (l : List ChannelAnnellation) : Prop :=
  ∀ a ∈ l, ∀ b ∈ l, a.shortChannelId = b.shortChannelId → a = b

def sameScid (a b : ChannelAnnellation) : Bool :=
  decide (a.shortChannelId = b.shortChannelId)

theorem sameScid_eq_true_iff (a b : ChannelAnnellation) :
    sameScid a b = true ↔ a.shortChannelId = b.shortChannelId

theorem sameScid_eq_false_iff (a b : ChannelAnnellation) :
    sameScid a b = false ↔ a.shortChannelId ≠ b.shortChannelId

def insertCanonical (a : ChannelAnnellation)
    (l : List ChannelAnnellation) : List ChannelAnnellation :=
  if l.any (sameScid a) then l else a :: l

theorem mem_insertCanonical_cases {a b : ChannelAnnellation}
    {l : List ChannelAnnellation} (h : b ∈ insertCanonical a l) :
    b = a ∨ b ∈ l

theorem mem_insertCanonical_of_mem {a b : ChannelAnnellation}
    {l : List ChannelAnnellation} (h : b ∈ l) :
    b ∈ insertCanonical a l

def dedupAnnouncements (l : List ChannelAnnellation) : List ChannelAnnellation :=
  l.foldr insertCanonical []

theorem dedupAnnouncements_cons (a : ChannelAnnellation)
    (l : List ChannelAnnellation) :
    dedupAnnouncements (a :: l) = insertCanonical a (dedupAnnouncements l)

theorem mem_of_mem_dedupAnnouncements {a : ChannelAnnellation}
    {l : List ChannelAnnellation} (h : a ∈ dedupAnnouncements l) : a ∈ l

theorem canonical_dedupAnnouncements (l : List ChannelAnnellation) :
    CanonicalAnnouncements (dedupAnnouncements l)

theorem mem_dedupAnnouncements_of_canonical {a : ChannelAnnellation}
    {l : List ChannelAnnellation} (hc : CanonicalAnnouncements l) (ha : a ∈ l) :
    a ∈ dedupAnnouncements l

-- namespace GossipState
def Canonical (s : GossipState) : Prop :=
  CanonicalAnnouncements s.announcements

def canonicalView (s : GossipState) : GossipState :=
  { s with announcements := dedupAnnouncements s.announcements }

@[simp] theorem canonicalView_announcements (s : GossipState) :
    s.canonicalView.announcements = dedupAnnouncements s.announcements

theorem canonicalView_canonical (s : GossipState) : s.canonicalView.Canonical

theorem updateKeyAnnounced_canonicalView (s : GossipState) (u : ChannelUpdate)
    (hc : s.Canonical) :
    s.canonicalView.updateKeyAnnounced u ↔ s.updateKeyAnnounced u

theorem updateKeyAnnouncedDirectional_canonicalView (s : GossipState)
    (u : ChannelUpdate) (hc : s.Canonical) :
    s.canonicalView.updateKeyAnnouncedDirectional u ↔
      s.updateKeyAnnouncedDirectional u
```

## 2. Exact main signatures in `GossipKeyConsistencyTargets.lean`

The module imports `LnLean.Proofs.Routing.GossipAttributionTargets`, so the
wave-4 transition and theorem are reused, not redefined.

```lean
noncomputable def admitGossipDirected (verify : SigVerifier)
    (ns : GossipNetwork) : GossipMessage → GossipNetwork
  | .channelAnnouncement a => admitGossipAttributed verify ns (.channelAnnouncement a)
  | .channelUpdate u =>
      if u.signatureValid verify ∧ ns.gossip.updateKeyAnnouncedDirectional u then
        { gossip := applyGossip ns.gossip (.channelUpdate u)
          views := ns.views.map fun v => v.applyUpdate u }
      else ns
  | .nodeAnnouncement n => admitGossipAttributed verify ns (.nodeAnnouncement n)

def StoreUpdatesDirectionallyAttributed (verify : SigVerifier)
    (s : GossipState) : Prop

def DirectedAdmitted (verify : SigVerifier) (ns : GossipNetwork) : Prop :=
  StoreAnnouncementsValid verify ns.gossip ∧ ViewsBacked verify ns ∧
    StoreUpdatesDirectionallyAttributed verify ns.gossip

inductive ReachableDirected (verify : SigVerifier) : GossipNetwork → Prop
  | empty : ReachableDirected verify { gossip := ⟨[], [], []⟩, views := [] }
  | step {ns : GossipNetwork} {m : GossipMessage} :
      ReachableDirected verify ns →
        ReachableDirected verify (admitGossipDirected verify ns m)

theorem admitGossipDirected_update_eq_attributed_of_directional
    (verify : SigVerifier) (ns : GossipNetwork) (u : ChannelUpdate)
    (hsig : u.signatureValid verify)
    (hk : ns.gossip.updateKeyAnnouncedDirectional u) :
    admitGossipDirected verify ns (.channelUpdate u) =
      admitGossipAttributed verify ns (.channelUpdate u)

theorem admitGossipDirected_preserves (verify : SigVerifier)
    (ns : GossipNetwork) (m : GossipMessage) (h : DirectedAdmitted verify ns) :
    DirectedAdmitted verify (admitGossipDirected verify ns m)

theorem reachableDirected_invariant {verify : SigVerifier}
    {ns : GossipNetwork} (h : ReachableDirected verify ns) :
    DirectedAdmitted verify ns

theorem reachableDirected_updates_directional {verify : SigVerifier}
    {ns : GossipNetwork} (h : ReachableDirected verify ns) :
    StoreUpdatesDirectionallyAttributed verify ns.gossip

theorem reachableDirected_updates_attributed {verify : SigVerifier}
    {ns : GossipNetwork} (h : ReachableDirected verify ns) :
    StoreUpdatesAttributed verify ns.gossip

theorem canonical_directional_attribution_unique {s : GossipState}
    (hcanon : CanonicalAnnouncements s.announcements)
    {u v : ChannelUpdate} (hscid : u.shortChannelId = v.shortChannelId)
    (hdir : u.direction = v.direction)
    (hu : s.updateKeyAnnouncedDirectional u)
    (hv : s.updateKeyAnnouncedDirectional v) :
    u.signingKey = v.signingKey

theorem canonical_attributionConsistent {s : GossipState}
    (h : CanonicalAnnouncements s.announcements) :
    AttributionConsistent s

theorem canonicalView_directional_attribution_unique (s : GossipState)
    {u v : ChannelUpdate} (hscid : u.shortChannelId = v.shortChannelId)
    (hdir : u.direction = v.direction)
    (hu : s.canonicalView.updateKeyAnnouncedDirectional u)
    (hv : s.canonicalView.updateKeyAnnouncedDirectional v) :
    u.signingKey = v.signingKey

theorem gossip_graph_edges_directional_key_endpoint
    (verify : SigVerifier) (ns : GossipNetwork) (nodeKeyOf : NodeId → PubKey)
    (h : ReachableDirected verify ns)
    (hcanon : CanonicalAnnouncements ns.gossip.announcements)
    (hnode : GossipState.NodeKeyConsistent nodeKeyOf ns.gossip) :
    ∀ e ∈ ns.graph.edges, ∀ u ∈ ns.gossip.updates,
      u.shortChannelId = e.shortChannelId →
        u.signatureValid verify ∧
          u.signingKey =
            (if u.direction then nodeKeyOf e.node2 else nodeKeyOf e.node1)

theorem conflicting_announcements_ambiguous_without_canonical :
    ∃ (s : GossipState) (u v : ChannelUpdate),
      ¬ CanonicalAnnouncements s.announcements ∧
        u.shortChannelId = v.shortChannelId ∧ u.direction = v.direction ∧
          s.updateKeyAnnouncedDirectional u ∧
            s.updateKeyAnnouncedDirectional v ∧ u.signingKey ≠ v.signingKey

theorem general_attribution_not_directional :
    ∃ (s : GossipState) (u : ChannelUpdate),
      s.updateKeyAnnounced u ∧ ¬ s.updateKeyAnnouncedDirectional u

theorem reachableDirected_stores_directional_update :
    ∃ (verify : SigVerifier) (ns : GossipNetwork) (u : ChannelUpdate),
      ReachableDirected verify ns ∧ u ∈ ns.gossip.updates ∧
        u.signatureValid verify ∧ ns.gossip.updateKeyAnnouncedDirectional u

theorem reachableDirected_directional_endpoint_witness :
    ∃ (verify : SigVerifier) (ns : GossipNetwork) (nodeKeyOf : NodeId → PubKey),
      ReachableDirected verify ns ∧ ns.graph.edges ≠ [] ∧
        CanonicalAnnouncements ns.gossip.announcements ∧
          GossipState.NodeKeyConsistent nodeKeyOf ns.gossip ∧
            ∀ e ∈ ns.graph.edges, ∀ u ∈ ns.gossip.updates,
              u.shortChannelId = e.shortChannelId →
                u.signatureValid verify ∧
                  u.signingKey =
                    (if u.direction then nodeKeyOf e.node2
                      else nodeKeyOf e.node1)

theorem raw_applyGossip_accepts_directionally_unattributed_update :
    ∃ (s : GossipState) (u : ChannelUpdate),
      ¬ s.updateKeyAnnouncedDirectional u ∧
        (applyGossip s (.channelUpdate u)).updates = u :: s.updates

theorem raw_applyGossip_accepts_conflicting_announcement :
    ∃ (s : GossipState) (a : ChannelAnnellation),
      ¬ CanonicalAnnouncements
        (applyGossip s (.channelAnnouncement a)).announcements
```

## 3. Build results

Commands (shared lock, no full `lake build`):

```sh
cd /home/ubuntu/ln-lean-repair
export PATH=/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Routing.Gossip LnLean.Proofs.Routing.GossipAttributionTargets \
    LnLean.Proofs.Routing.GossipKeyConsistencyTargets
```

Result: **RC 0**, `Build completed successfully (11 jobs)`.

| Target | Result |
|---|---|
| `LnLean.Routing.Gossip` | **RC 0** (built in the combined run) |
| `LnLean.Proofs.Routing.GossipAttributionTargets` (wave 4) | **RC 0**, replayed |
| `LnLean.Proofs.Routing.GossipKeyConsistencyTargets` (new) | **RC 0** |

The only warnings in the transcript come from the read-only
`LnLean/Proofs/Routing/GossipProps.lean` (`if_pos`/`if_neg` deprecations).
The two owned modules emit none after replacing the deprecated names in the
new code.

## 4. Axiom audit

Audit script outside the repo:
`/tmp/opencode/axcheck_s5_gossip_attr2.lean` (`#print axioms`).  All audited
lane declarations resolve within `{propext, Quot.sound, Classical.choice}`:

* **no axioms:** `attributesKeyForDirection_implies_attributesKey`,
  `updateKeyAnnouncedDirectional_implies_updateKeyAnnounced`,
  `updateKeyAnnouncedDirectional_mono`,
  `nodeKeyConsistent_node1_key_unique`,
  `nodeKeyConsistent_node2_key_unique`, `canonical_attributionConsistent`;
* **`[propext]` only:** `attributesKeyForDirection_iff`,
  `canonical_directional_attribution_unique`,
  `raw_applyGossip_accepts_directionally_unattributed_update`,
  `raw_applyGossip_accepts_conflicting_announcement`;
* **`[propext, Quot.sound]` only:** the dedup/canonical-view lemmas
  (`canonical_dedupAnnouncements`, `mem_dedupAnnouncements_of_canonical`,
  `canonicalView_canonical`, `updateKeyAnnouncedDirectional_canonicalView`,
  `canonicalView_directional_attribution_unique`);
* **subset of `[propext, Classical.choice, Quot.sound]`:** the directed
  transition, reachability invariant, endpoint theorem, ambiguity
  counterexample, and non-vacuity theorems, including
  `admitGossipDirected_preserves`, `reachableDirected_invariant`,
  `reachableDirected_updates_directional`, `reachableDirected_updates_attributed`,
  `gossip_graph_edges_directional_key_endpoint`,
  `conflicting_announcements_ambiguous_without_canonical`,
  `general_attribution_not_directional`,
  `reachableDirected_stores_directional_update`,
  `reachableDirected_directional_endpoint_witness`.

Preservation checks:

* `LnLean.Proofs.Routing.GossipAttributionTargets.gossip_graph_edges_update_attributed`
  — `[propext, Classical.choice, Quot.sound]`;
* `LnLean.Proofs.Routing.GossipAttributionTargets.raw_applyGossip_accepts_unannounced_update`
  — `[propext]`;
* `LnLean.Proofs.Routing.GossipTargets.raw_store_not_filtered` — `[propext]`;
* `LnLean.Routing.Gossip.update_monotone` — `[propext]`.

## 5. Forbidden-construct scan

```sh
grep -nE '(^|[^A-Za-z_])(sorry|admit|native_decide|unsafe|implemented_by)([^A-Za-z_]|$)' \
  LnLean/Routing/Gossip.lean LnLean/Proofs/Routing/GossipKeyConsistencyTargets.lean
grep -nE '^[[:space:]]*axiom[[:space:]]' \
  LnLean/Routing/Gossip.lean LnLean/Proofs/Routing/GossipKeyConsistencyTargets.lean
strings .lake/build/lib/lean/LnLean/Routing/Gossip.olean | grep -c sorryAx
strings .lake/build/lib/lean/LnLean/Proofs/Routing/GossipKeyConsistencyTargets.olean | grep -c sorryAx
```

Results:

* code-token scan: **no code occurrence**.  The only two matches are the
  docstring lines in the new module listing the prohibited constructs;
* `axiom` declarations: **none**;
* `sorryAx` in either `.olean`: **0** and **0**.

## 6. Scope caveats (do not drop when integrating)

1. **Direction is now decoded, but ownership is still explicit.**
   `attributesKeyForDirection` compares `u.signingKey` with the selected
   announcement field.  It does not prove cryptographic ownership,
   unforgeability, or that the BOLT 7 digest covers the required byte range;
   those remain the abstract `SigVerifier` contract and assumptions
   C3/C4/C8.
2. **`NodeKeyConsistent` is a hypothesis, not a transition invariant.**
   The endpoint theorem takes `GossipState.NodeKeyConsistent nodeKeyOf` and
   `CanonicalAnnouncements ns.gossip.announcements` explicitly.  The directed
   transition preserves the update-side invariant but does not construct the
   `NodeId → PubKey` map or reject a newly inconsistent announcement.  A
   production admission path must check the map when storing an announcement.
3. **`CanonicalAnnouncements` is not an invariant of raw `applyGossip`.**
   `raw_applyGossip_accepts_conflicting_announcement` shows the append-only
   raw store still admits conflicting same-channel announcements.  The
   canonical view removes them, and under the invariant the view preserves
   attribution exactly; the raw store does not.
4. **The canonical view keeps the last occurrence of a channel.**  Under
   `CanonicalAnnouncements` all same-channel records are equal, so the choice
   is immaterial; without the invariant, deduplication can discard a
   conflicting record, which is precisely why it is a view rather than a
   silent mutation of the raw store.
5. **The directed gate uses the pre-update store.**  An update arriving before
   its announcement is rejected; there is no buffering/retry model.  This is
   the same admission-policy choice as wave 4.
6. **`admitGossipDirected` announcement/node branches reuse
   `admitGossipAttributed` definitionally.**  Only the `channel_update` branch
   is new, so the S3-RT006 graph/edge results remain reusable.
7. **Raw `applyGossip` is untouched.**  `raw_applyGossip_accepts_directionally_unattributed_update`
   and the wave-4 `raw_applyGossip_accepts_unannounced_update` both still
   hold; production insertion through raw `applyGossip` re-opens the
   signature, attribution, direction, and dedup gaps.
8. **No network/liveness claim.**  Gossip dissemination, rate limits,
   `gossip_queries`, chain-hash filtering, and UTXO confirmation remain
   outside this model.

## 7. Integration steps for the parent

1. **Root import (required for the default build):** add

   ```lean
   import LnLean.Proofs.Routing.GossipKeyConsistencyTargets
   ```

   to `LnLean.lean` next to
   `import LnLean.Proofs.Routing.GossipAttributionTargets`.  This lane did not
   edit `LnLean.lean` (forbidden shared file); the module builds green without
   the root import.

2. **Catalog / traceability (parent-owned):** target
   `gossip_graph_edges_directional_key_endpoint` as the main `RT-01`
   direction-keyed statement, with secondary targets
   `canonical_directional_attribution_unique` (dedup/no-ambiguity),
   `conflicting_announcements_ambiguous_without_canonical` (the matching
   counterexample), and `canonical_dedupAnnouncements` /
   `updateKeyAnnouncedDirectional_canonicalView` (dedup view).  Add the module
   to `Proofs/Traceability.lean` and an `#print axioms` line to the audit
   module if new modules are recorded there.  Keep the `NodeKeyConsistent` and
   `CanonicalAnnouncements` hypotheses in the scope note; the theorem is not
   unconditional over an arbitrary store.

3. **Suggested scope note for the row:** "Every stored update for a graph edge
   of a directed-attributed-reachable state is signature-valid and is signed
   by exactly the endpoint selected by its BOLT 7 direction, under the
   explicit `NodeKeyConsistent` map and the canonical-announcement invariant.
   Deduplication/canonical view is proved attribution-preserving under that
   invariant; conflicting announcements are a mechanised counterexample
   without it.  Raw `applyGossip` remains unfiltered and undeduplicated."

4. **Generated indexes / status:** do not run `collect-obligations.py` or
   `collect-anchors.py` from this lane; the parent regenerates them after the
   root import and catalog edit.

5. **Relation to wave 4:** `updateKeyAnnouncedDirectional` strictly refines
   `updateKeyAnnounced` (`general_attribution_not_directional` is the strictness
   witness), and `CanonicalAnnouncements` implies wave-4
   `AttributionConsistent` (`canonical_attributionConsistent`).  No rewrite of
   the wave-4 module is needed; the new module imports and extends it.

## 8. Files not edited

Read-only in this lane (unchanged):

* `LnLean/Proofs/Routing/GossipAttributionTargets.lean` (wave-4 theorem and
  raw caveat preserved);
* `LnLean/Proofs/Routing/GossipTargets.lean`, `GossipProps.lean`,
  `ModelHardening/F05.lean`, `WaveD/D27.lean`, `WaveD/D38.lean`;
* `LnLean.lean`, `LnLean/Proofs/Obligations.lean`,
  `LnLean/Proofs/Traceability.lean`, `LnLean/Proofs/PhaseC3/AxiomAudit.lean`;
* shared docs, scripts, other lanes' files, and Git history.

No `git add`, `commit`, `push`, `checkout`, or `reset` was run.  No full
`lake build` was run.
