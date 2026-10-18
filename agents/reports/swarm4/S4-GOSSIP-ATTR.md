# S4-GOSSIP-ATTR — `RT-01`: gossip key attribution in `channel_update` admission

**Lane:** `S4-GOSSIP-ATTR`
**Worktree:** `/home/ubuntu/ln-lean-repair`
**Branch / base:** `repair/integrated` @ `47189fe`
**Toolchain:** `leanprover/lean4:v4.35.0`
**Owned files changed:**
`LnLean/Routing/Gossip.lean` (additive only),
`LnLean/Proofs/Routing/GossipAttributionTargets.lean` (new),
`agents/reports/swarm4/S4-GOSSIP-ATTR.md` (new)

## Verdict

`RT-01` is addressed at the model/admission level.  The routing model now has an
explicit key-attribution relation and an **additional** attributed admission
transition:

* `GossipState.updateKeyAnnounced s u`: some stored `channel_announcement` for
  `u.shortChannelId` names `u.signingKey` as `nodeKey1` or `nodeKey2`;
* `admitGossipAttributed verify ns`: a gossip admission step whose
  `channel_update` branch requires **both** `u.signatureValid verify` and
  `ns.gossip.updateKeyAnnounced u`;
* `ReachableAttributed verify ns`: attributed reachability from the empty
  network.

The main theorem is

```lean
theorem gossip_graph_edges_update_attributed (verify : SigVerifier)
    (ns : GossipNetwork) (h : ReachableAttributed verify ns) :
    ∀ e ∈ ns.graph.edges, ∀ u ∈ ns.gossip.updates,
      u.shortChannelId = e.shortChannelId →
        u.signatureValid verify ∧
          ∃ a ∈ ns.gossip.announcements,
            a.signaturesValid verify ∧ a.shortChannelId = e.shortChannelId ∧
              a.attributesKey u.signingKey
```

so every stored update for an admitted graph edge is signature-valid **and**
its signing key is attributed by a valid stored announcement for that edge's
channel.  The endpoint-level form

```lean
theorem gossip_graph_edges_update_key_endpoint (verify : SigVerifier)
    (ns : GossipNetwork) (nodeKeyOf : NodeId → PubKey)
    (h : ReachableAttributed verify ns)
    (hconsistent : AttributionConsistent ns.gossip)
    (hka : ∀ a ∈ ns.gossip.announcements, KeyAttribution nodeKeyOf a) :
    ∀ e ∈ ns.graph.edges, ∀ u ∈ ns.gossip.updates,
      u.shortChannelId = e.shortChannelId →
        u.signatureValid verify ∧
          (u.signingKey = nodeKeyOf e.node1 ∨
            u.signingKey = nodeKeyOf e.node2)
```

gives the literal "signed by the announced key of an endpoint" statement under
the explicit attribution hypotheses `AttributionConsistent` and
`KeyAttribution`.

Raw `applyGossip` and every existing theorem are untouched.  The S3-RT006
theorem `gossip_graph_only_valid_announcements` and the raw-store caveats
(`raw_store_not_filtered`, `raw_store_invariant_not_preserved`) still hold and
are re-checked by the axiom audit below.

## 1. Exact additions to `LnLean/Routing/Gossip.lean`

The section starts after `namespace Gossip` / `end Gossip`; no existing
declaration, signature, or proof was modified.

```lean
namespace ChannelAnnellation
def attributesKey (a : ChannelAnnellation) (key : PubKey) : Prop :=
  a.nodeKey1 = key ∨ a.nodeKey2 = key

theorem attributesKey_iff (a : ChannelAnnellation) (key : PubKey) :
    a.attributesKey key ↔ a.nodeKey1 = key ∨ a.nodeKey2 = key

theorem attributesKey_node1 (a : ChannelAnnellation) :
    a.attributesKey a.nodeKey1

theorem attributesKey_node2 (a : ChannelAnnellation) :
    a.attributesKey a.nodeKey2
end ChannelAnnellation

namespace GossipState
def updateKeyAnnounced (s : GossipState) (u : ChannelUpdate) : Prop :=
  ∃ a ∈ s.announcements, a.shortChannelId = u.shortChannelId ∧
    a.attributesKey u.signingKey

theorem updateKeyAnnounced_iff (s : GossipState) (u : ChannelUpdate) :
    s.updateKeyAnnounced u ↔
      ∃ a ∈ s.announcements, a.shortChannelId = u.shortChannelId ∧
        a.attributesKey u.signingKey

theorem updateKeyAnnounced_of_mem {s : GossipState} {u : ChannelUpdate}
    {a : ChannelAnnellation} (ha : a ∈ s.announcements)
    (hscid : a.shortChannelId = u.shortChannelId)
    (hkey : a.attributesKey u.signingKey) :
    s.updateKeyAnnounced u

theorem updateKeyAnnounced_mono {s t : GossipState} {u : ChannelUpdate}
    (hsub : ∀ a ∈ s.announcements, a ∈ t.announcements)
    (h : s.updateKeyAnnounced u) : t.updateKeyAnnounced u

theorem applyUpdate_announcements (s : GossipState) (u : ChannelUpdate) :
    (s.applyUpdate u).announcements = s.announcements

theorem updateKeyAnnounced_applyUpdate (s : GossipState) (u : ChannelUpdate)
    (h : s.updateKeyAnnounced u) :
    (s.applyUpdate u).updateKeyAnnounced u

noncomputable def applyUpdateAttributed (s : GossipState) (verify : SigVerifier)
    (u : ChannelUpdate) : GossipState :=
  if u.signatureValid verify ∧ s.updateKeyAnnounced u then s.applyUpdate u else s

theorem applyUpdateAttributed_eq_applyUpdate_of_admitted (s : GossipState)
    (verify : SigVerifier) (u : ChannelUpdate)
    (hsig : u.signatureValid verify) (hk : s.updateKeyAnnounced u) :
    s.applyUpdateAttributed verify u = s.applyUpdate u

theorem applyUpdateAttributed_eq_self_of_unannounced (s : GossipState)
    (verify : SigVerifier) (u : ChannelUpdate)
    (hk : ¬ s.updateKeyAnnounced u) :
    s.applyUpdateAttributed verify u = s

theorem applyUpdateAttributed_change_requires (s : GossipState)
    (verify : SigVerifier) (u : ChannelUpdate)
    (h : s.applyUpdateAttributed verify u ≠ s) :
    u.signatureValid verify ∧ s.updateKeyAnnounced u

theorem applyUpdateAttributed_change_requires_newer (s : GossipState)
    (verify : SigVerifier) (u : ChannelUpdate)
    (h : s.applyUpdateAttributed verify u ≠ s) :
    s.latestUpdateTimestamp < u.timestamp

theorem applyUpdateAttributed_announcements (s : GossipState)
    (verify : SigVerifier) (u : ChannelUpdate) :
    (s.applyUpdateAttributed verify u).announcements = s.announcements

theorem updateKeyAnnounced_applyUpdateAttributed (s : GossipState)
    (verify : SigVerifier) (u : ChannelUpdate) (h : s.updateKeyAnnounced u) :
    (s.applyUpdateAttributed verify u).updateKeyAnnounced u

theorem latestUpdateTimestamp_applyUpdateAttributed_ge (s : GossipState)
    (verify : SigVerifier) (u : ChannelUpdate) :
    s.latestUpdateTimestamp ≤
      (s.applyUpdateAttributed verify u).latestUpdateTimestamp
end GossipState
```

`applyUpdate` and `applyGossip` are not referenced by the new step except
through the existing `applyUpdate`; `applyGossip` itself is unchanged.

## 2. Exact additions to `GossipAttributionTargets.lean`

Imports: `LnLean.Proofs.Routing.GossipTargets` (hence `GossipProps`,
`Gossip`, `Graph`).

### Transition, invariants, reachability

```lean
noncomputable def admitGossipAttributed (verify : SigVerifier) (ns : GossipNetwork) :
    GossipMessage → GossipNetwork
  | .channelAnnouncement a => admitGossip verify ns (.channelAnnouncement a)
  | .channelUpdate u =>
      if u.signatureValid verify ∧ ns.gossip.updateKeyAnnounced u then
        { gossip := applyGossip ns.gossip (.channelUpdate u)
          views := ns.views.map fun v => v.applyUpdate u }
      else ns
  | .nodeAnnouncement n => admitGossip verify ns (.nodeAnnouncement n)

inductive ReachableAttributed (verify : SigVerifier) : GossipNetwork → Prop
  | empty : ReachableAttributed verify { gossip := ⟨[], [], []⟩, views := [] }
  | step {ns : GossipNetwork} {m : GossipMessage} :
      ReachableAttributed verify ns →
        ReachableAttributed verify (admitGossipAttributed verify ns m)

def StoreUpdatesAttributed (verify : SigVerifier) (s : GossipState) : Prop :=
  ∀ u ∈ s.updates, u.signatureValid verify ∧ s.updateKeyAnnounced u

def AttributedAdmitted (verify : SigVerifier) (ns : GossipNetwork) : Prop :=
  StoreAnnouncementsValid verify ns.gossip ∧ ViewsBacked verify ns ∧
    StoreUpdatesAttributed verify ns.gossip
```

Key transition lemmas (all exact):

```lean
theorem admitGossipAttributed_update_of_attributed (verify : SigVerifier)
    (ns : GossipNetwork) (u : ChannelUpdate)
    (hsig : u.signatureValid verify)
    (hk : ns.gossip.updateKeyAnnounced u) :
    admitGossipAttributed verify ns (.channelUpdate u) =
      { gossip := applyGossip ns.gossip (.channelUpdate u)
        views := ns.views.map fun v => v.applyUpdate u }

theorem admitGossipAttributed_update_of_unannounced (verify : SigVerifier)
    (ns : GossipNetwork) (u : ChannelUpdate)
    (hk : ¬ ns.gossip.updateKeyAnnounced u) :
    admitGossipAttributed verify ns (.channelUpdate u) = ns

theorem admitGossipAttributed_eq_admitGossip_of_attributed
    (verify : SigVerifier) (ns : GossipNetwork) (u : ChannelUpdate)
    (hk : ns.gossip.updateKeyAnnounced u) :
    admitGossipAttributed verify ns (.channelUpdate u) =
      admitGossip verify ns (.channelUpdate u)
```

The last theorem is the preservation statement for the S3-RT006 model: when
the key is announced, the attributed update step is exactly the old
signature-gated `admitGossip` step.  Announcement and node steps are
definitionally the S3-RT006 steps
(`admitGossipAttributed_announcement`, `admitGossipAttributed_node`).

### Reachable invariant and graph target

```lean
theorem reachableAttributed_invariant {verify : SigVerifier} {ns : GossipNetwork}
    (h : ReachableAttributed verify ns) : AttributedAdmitted verify ns

theorem reachableAttributed_store_valid {verify : SigVerifier}
    {ns : GossipNetwork} (h : ReachableAttributed verify ns) :
    StoreAnnouncementsValid verify ns.gossip

theorem reachableAttributed_views_backed {verify : SigVerifier}
    {ns : GossipNetwork} (h : ReachableAttributed verify ns) :
    ViewsBacked verify ns

theorem reachableAttributed_updates_attributed {verify : SigVerifier}
    {ns : GossipNetwork} (h : ReachableAttributed verify ns) :
    StoreUpdatesAttributed verify ns.gossip

theorem reachableAttributed_updates_signed_by_valid_announcement
    {verify : SigVerifier} {ns : GossipNetwork}
    (h : ReachableAttributed verify ns) :
    ∀ u ∈ ns.gossip.updates,
      u.signatureValid verify ∧
        ∃ a ∈ ns.gossip.announcements,
          a.signaturesValid verify ∧ a.shortChannelId = u.shortChannelId ∧
            a.attributesKey u.signingKey

theorem gossip_graph_edges_update_attributed (verify : SigVerifier)
    (ns : GossipNetwork) (h : ReachableAttributed verify ns) :
    ∀ e ∈ ns.graph.edges, ∀ u ∈ ns.gossip.updates,
      u.shortChannelId = e.shortChannelId →
        u.signatureValid verify ∧
          ∃ a ∈ ns.gossip.announcements,
            a.signaturesValid verify ∧ a.shortChannelId = e.shortChannelId ∧
              a.attributesKey u.signingKey

theorem gossip_graph_edges_backed_attributed (verify : SigVerifier)
    (ns : GossipNetwork) (h : ReachableAttributed verify ns) :
    ∀ e ∈ ns.graph.edges, ∃ a ∈ ns.gossip.announcements,
      announcementValid verify a ∧ e.shortChannelId = a.shortChannelId ∧
        e.node1 = a.node1 ∧ e.node2 = a.node2 ∧
          e.capacitySat = a.capacitySat
```

### Endpoint attribution hypotheses and theorem

```lean
def AttributionConsistent (s : GossipState) : Prop :=
  ∀ a ∈ s.announcements, ∀ b ∈ s.announcements,
    a.shortChannelId = b.shortChannelId →
      a.node1 = b.node1 ∧ a.node2 = b.node2 ∧
        a.nodeKey1 = b.nodeKey1 ∧ a.nodeKey2 = b.nodeKey2

theorem gossip_graph_edges_update_key_endpoint (verify : SigVerifier)
    (ns : GossipNetwork) (nodeKeyOf : NodeId → PubKey)
    (h : ReachableAttributed verify ns)
    (hconsistent : AttributionConsistent ns.gossip)
    (hka : ∀ a ∈ ns.gossip.announcements, KeyAttribution nodeKeyOf a) :
    ∀ e ∈ ns.graph.edges, ∀ u ∈ ns.gossip.updates,
      u.shortChannelId = e.shortChannelId →
        u.signatureValid verify ∧
          (u.signingKey = nodeKeyOf e.node1 ∨
            u.signingKey = nodeKeyOf e.node2)
```

`KeyAttribution` is the existing `NodeId → PubKey` map predicate from
`LnLean.Proofs.Routing.GossipTargets`; it is supplied as a hypothesis, not
constructed.

### Relation to existing predicates, non-vacuity, raw contrast

```lean
theorem updateKeyAnnounced_iff_gossipProps (s : GossipState) (u : ChannelUpdate) :
    s.updateKeyAnnounced u ↔ GossipProps.updateKeyAnnounced s u

theorem updateKeyAnnounced_iff_exists_key (s : GossipState) (u : ChannelUpdate) :
    s.updateKeyAnnounced u ↔
      ∃ a ∈ s.announcements, a.shortChannelId = u.shortChannelId ∧
        (a.nodeKey1 = u.signingKey ∨ a.nodeKey2 = u.signingKey)

theorem reachableAttributed_stores_attributed_update :
    ∃ (verify : SigVerifier) (ns : GossipNetwork) (u : ChannelUpdate),
      ReachableAttributed verify ns ∧ u ∈ ns.gossip.updates ∧
        u.signatureValid verify ∧ ns.gossip.updateKeyAnnounced u

theorem reachableAttributed_graph_nonempty_and_attributed :
    ∃ (verify : SigVerifier) (ns : GossipNetwork),
      ReachableAttributed verify ns ∧ ns.graph.edges ≠ [] ∧
        ∀ e ∈ ns.graph.edges, ∀ u ∈ ns.gossip.updates,
          u.shortChannelId = e.shortChannelId →
            u.signatureValid verify ∧
              ∃ a ∈ ns.gossip.announcements,
                a.signaturesValid verify ∧
                  a.shortChannelId = e.shortChannelId ∧
                    a.attributesKey u.signingKey

theorem unannounced_update_rejected :
    ∃ (verify : SigVerifier) (ns : GossipNetwork) (u : ChannelUpdate),
      ¬ ns.gossip.updateKeyAnnounced u ∧
        admitGossipAttributed verify ns (.channelUpdate u) = ns

theorem raw_applyGossip_accepts_unannounced_update :
    ∃ (s : GossipState) (u : ChannelUpdate),
      ¬ s.updateKeyAnnounced u ∧
        (applyGossip s (.channelUpdate u)).updates = u :: s.updates
```

The last theorem is the explicit raw/gated contrast: the same unannounced
update is still stored by raw `applyGossip`, while the attributed admission
rejects it.  S3-RT006's raw-store caveat therefore remains accurate.

## 3. Build results

Commands (shared lock, no full `lake build`):

```sh
cd /home/ubuntu/ln-lean-repair
export PATH=/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Routing.Gossip
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Proofs.Routing.GossipAttributionTargets
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Proofs.Routing.GossipTargets LnLean.Proofs.ModelHardening.F05 \
    LnLean.Proofs.WaveD.D27 LnLean.Proofs.WaveD.D38
```

| Target | Result |
|---|---|
| `LnLean.Routing.Gossip` | **RC 0**, `Build completed successfully (7 jobs)` |
| `LnLean.Proofs.Routing.GossipAttributionTargets` | **RC 0**, `Build completed successfully (10 jobs)` |
| `GossipTargets` + `F05` + `D27` + `D38` (direct downstream) | **RC 0**, `Build completed successfully (15 jobs)` |

No warning is emitted from either owned module.  The only warnings in the
transcript are the pre-existing `if_pos` / `if_neg` deprecation warnings in
the read-only `LnLean/Proofs/Routing/GossipProps.lean`.

## 4. Axiom audit

Audit script (outside the repo): `lake env lean /tmp/opencode/axcheck_gossip_attr.lean`.

All audited declarations (38 lane declarations plus three preservation checks)
resolve within the permitted set `{propext, Quot.sound, Classical.choice}`:

* no axioms: `attributesKey_iff`, `updateKeyAnnounced_iff`,
  `updateKeyAnnounced_of_mem`, `updateKeyAnnounced_mono`,
  `updateKeyAnnounced_applyUpdate`, `attributed_update_preserves_store`,
  `updateKeyAnnounced_iff_gossipProps`, `updateKeyAnnounced_iff_exists_key`;
* `[propext]` only: `applyGossip_update_preserves_updates`,
  `raw_applyGossip_accepts_unannounced_update`;
* `[propext, Quot.sound]` only: `attributed_update_preserves_views_backed`;
* all remaining public theorems (including `reachableAttributed_invariant`,
  `gossip_graph_edges_update_attributed`,
  `gossip_graph_edges_update_key_endpoint`,
  `reachableAttributed_graph_nonempty_and_attributed`,
  `reachableAttributed_updates_signed_by_valid_announcement`,
  `reachableAttributed_stores_attributed_update`,
  `unannounced_update_rejected`, and every `applyUpdateAttributed` lemma):
  subset of `[propext, Classical.choice, Quot.sound]`.

Preservation checks for the S3-RT006 target:

* `LnLean.Proofs.Routing.GossipTargets.gossip_graph_only_valid_announcements`
  — `[propext, Classical.choice, Quot.sound]`;
* `LnLean.Proofs.Routing.GossipTargets.raw_store_not_filtered` — `[propext]`;
* `LnLean.Routing.Gossip.update_monotone` — `[propext]`.

## 5. Forbidden-construct scan

```sh
grep -nE '(^|[^A-Za-z_])(sorry|admit|native_decide|unsafe|implemented_by)([^A-Za-z_]|$)' \
  LnLean/Routing/Gossip.lean LnLean/Proofs/Routing/GossipAttributionTargets.lean
grep -nE '^[[:space:]]*axiom[[:space:]]' \
  LnLean/Routing/Gossip.lean LnLean/Proofs/Routing/GossipAttributionTargets.lean
strings .lake/build/lib/lean/LnLean/Proofs/Routing/GossipAttributionTargets.olean | grep -c sorryAx
strings .lake/build/lib/lean/LnLean/Routing/Gossip.olean | grep -c sorryAx
```

Results:

* code-token scan: **no code occurrence**.  The only matches are the two
  docstring prose lines in the new module that list the prohibited constructs
  ("No `sorry`, no `axiom`, ...").
* `axiom` declarations: **none**.
* `sorryAx` in either `.olean`: **0** and **0**.

## 6. Scope caveats (do not drop when integrating)

1. **Attribution is key equality, not cryptographic ownership.**
   `updateKeyAnnounced` compares `u.signingKey` with `nodeKey1` / `nodeKey2`
   of a stored announcement for the same `short_channel_id`.  It does not
   prove that the key is controlled by the graph node, that the signature is
   unforgeable, or that the digest is the BOLT 7 double-SHA256 range.  Those
   remain assumptions C3/C4/C8 and the `SigVerifier` interface.
2. **The gate uses the pre-update store.**  If a `channel_update` arrives
   before the matching `channel_announcement`, the attributed step rejects it
   (no buffering/retry model).  BOLT 7 peers normally query/fetch the
   announcement first; this is an admission-policy choice, not a derived
   fact.
3. **Direction is not decoded.**  `attributesKey` accepts either announced
   node key, because the model does not decode `channel_flags` bit 0 into a
   direction→key map.  This is the same limitation as F05 and is recorded as
   follow-up work, not hidden in the theorem.
4. **The endpoint theorem has two explicit hypotheses.**  `AttributionConsistent`
   (announcements for one `short_channel_id` agree on endpoints *and* both
   node keys) is stronger than `GossipProps.uniqueBindings` (endpoints only).
   It is not a transition invariant: the wave-A store is append-only and does
   not reject a conflicting re-announcement.  It is stated as a hypothesis so
   the theorem is not read as stronger than the model supports.  The second
   hypothesis, `KeyAttribution nodeKeyOf`, is the missing `NodeId → PubKey`
   map; the model does not construct it.
5. **Raw `applyGossip` is unchanged.**  S3-RT006's
   `gossip_graph_only_valid_announcements`, `raw_store_not_filtered`, and
   `raw_store_invariant_not_preserved` are untouched and still valid.
   `raw_applyGossip_accepts_unannounced_update` re-exhibits the raw behaviour
   next to the attributed gate.  Any integration that routes production
   insertion through raw `applyGossip` re-opens both the signature and the
   attribution gaps.
6. **Announcement/node branches reuse S3-RT006.**  `admitGossipAttributed`
   delegates to `admitGossip` for `channel_announcement` and
   `node_announcement`; only the `channel_update` branch is new.  This keeps
   the S3 graph/edge results reusable and avoids a second admission model.
7. **The attributed store step does not require the witness announcement to
   verify.**  In a reachable attributed state every announcement verifies, so
   `reachableAttributed_updates_signed_by_valid_announcement` obtains the
   stronger witness.  For an arbitrary (non-reachable) store, the stronger
   gate is `ModelHardening.F05.UpdateKeyAdmissible`; use that predicate if a
   caller needs validity in the gate itself.
8. **No network/liveness claim.**  Gossip dissemination, rate limits,
   chain-hash filtering, and UTXO confirmation of the funding outpoint remain
   outside this model.

## 7. Integration steps for the parent

1. **Root import (required for the default build):** add

   ```lean
   import LnLean.Proofs.Routing.GossipAttributionTargets
   ```

   to `LnLean.lean` next to `import LnLean.Proofs.Routing.GossipTargets`.
   This lane did not edit `LnLean.lean` (forbidden shared file); the exact
   module builds green without it.

2. **Catalog / traceability (parent-owned):** if `RT-01` is to have a
   theorem row, target `gossip_graph_edges_update_attributed` (attribution
   statement) with secondary targets
   `reachableAttributed_updates_signed_by_valid_announcement` and
   `gossip_graph_edges_update_key_endpoint` (endpoint form, hypotheses
   included in the scope note).  Add the module to
   `Proofs/Traceability.lean` and an `#print axioms` line to
   `Proofs/PhaseC3/AxiomAudit.lean` if the project records new modules there.
   Do not mark `RT-01` closed on the basis of the attribution gate alone:
   direction-keyed attribution and the `NodeId → PubKey` map remain open.
3. **Suggested scope note for the row:** "Every stored update for a graph
   edge of an attributed-reachable state has a verifying signature and a
   signing key attributed by a valid stored announcement for the edge's
   `short_channel_id`; endpoint equality additionally assumes
   `AttributionConsistent` and `KeyAttribution nodeKeyOf`.  Raw `applyGossip`
   remains unfiltered."
4. **Generated indexes / status:** do not run `collect-obligations.py` or
   `collect-anchors.py` from this lane; the parent regenerates them after the
   root import and catalog edit.
5. **Optional consolidation:** `GossipProps.updateKeyAnnounced` and the new
   `GossipState.updateKeyAnnounced` are definitionally equal
   (`updateKeyAnnounced_iff_gossipProps`), and
   `ModelHardening.F05.UpdateKeyAnnounced` has the same body.  Keeping the
   routing-level name as the canonical model relation and the proof-layer
   names as compatibility aliases is recommended; no rewrite is required for
   this wave.

## 8. Files not edited

Read-only in this lane (unchanged):

* `LnLean/Proofs/Routing/GossipTargets.lean` (S3-RT006 target and raw caveats
  preserved);
* `LnLean/Proofs/Routing/GossipProps.lean`;
* `LnLean/Proofs/ModelHardening/F05.lean`;
* `LnLean/Proofs/WaveD/D27.lean`, `LnLean/Proofs/WaveD/D38.lean`;
* `LnLean.lean`, `LnLean/Proofs/Obligations.lean`,
  `LnLean/Proofs/Traceability.lean`, `LnLean/Proofs/PhaseC3/AxiomAudit.lean`;
* shared docs, scripts, other lanes' files, and Git history.

No `git add`, `commit`, `push`, `checkout`, or `reset` was run.  No full
`lake build` was run.
