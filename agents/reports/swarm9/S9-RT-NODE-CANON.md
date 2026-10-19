# S9-RT-NODE-CANON — node-announcement canonicalisation

**Lane:** `S9-RT-NODE-CANON`
**Issue:** `RT-02` (node-announcement canonicalisation)
**Worktree:** `/home/ubuntu/ln-lean-repair`
**Branch:** `repair/integrated` at `93fa943`
**Toolchain:** `leanprover/lean4:v4.35.0` (Lean `4.35.0`, no Mathlib)
**Owned files changed:**

* `LnLean/Proofs/Routing/NodeCanonicalTargets.lean` — new, `1295` lines,
* `agents/reports/swarm9/S9-RT-NODE-CANON.md` — this report.

No other file was created or modified by this lane. In particular
`LnLean/Routing/Gossip.lean`, `GossipStoreEpochTargets.lean`,
`GossipCanonicalTargets.lean`, root imports, `Obligations.lean`,
`Traceability.lean`, `AxiomAudit.lean`, the catalog, and all docs are untouched.
No commit or push was performed. (`git status` also shows unrelated pre-existing
worktree changes from other lanes; they were not touched.)

## 1. Objective and verdict

Wave 6 canonicalised channel announcements and channel updates; wave 8 added a
typed replacement/epoch layer. Node announcements were deliberately left as
raw appends by both `applyGossip` and `applyGossipCanonicalStore`, and
`canonicalStoreView` did not select them. `RT-02` is that gap.

This lane adds an **additive** node-canonicalisation layer in a new module:

* replace a stored node record by `nodeId` under a BOLT 7 strict-timestamp
  gate,
* prove the replacement and rotation behaviour on concrete reachable states,
* prove the per-slot/global-clock boundary and an unrecoverable equal-timestamp
  boundary, including an impossibility theorem for any raw-append-preserving
  node extension,
* re-export the wave-7 raw non-refinement and per-slot/global-clock results and
  the wave-8 epoch squares unchanged,
* lift the epoch square to the node-canonical view on node-canonical raw folds.

**Verdict:** complete for the modelled node canonicalisation layer. `RT-02`
should be **narrowed**, not closed: no claim is made that two different
`nodeId` keys belong to the same physical node, and no wire-level membership,
chain-existence, or rate-limit model is added.

## 2. Model

Namespace: `LnLean.Proofs.Routing.NodeCanonicalTargets`.

### 2.1 Replacement primitives

```lean
noncomputable def insertNodeCanonical (n : NodeAnnouncement)
    (l : List NodeAnnouncement) : List NodeAnnouncement :=
  n :: l.filter (fun m => decide (m.nodeId ≠ n.nodeId))

def CanonicalNodeAnnouncements (l : List NodeAnnouncement) : Prop :=
  ∀ a ∈ l, ∀ b ∈ l, a.nodeId = b.nodeId → a = b

def NodeSupersedes (n : NodeAnnouncement)
    (l : List NodeAnnouncement) : Prop :=
  ∀ m ∈ l, m.nodeId = n.nodeId → m.timestamp < n.timestamp

noncomputable def selectNodeAnnouncements :
    List NodeAnnouncement → List NodeAnnouncement
  | [] => []
  | n :: l => insertNodeCanonical n (selectNodeAnnouncements l)
```

`NodeSupersedes` is exactly the BOLT 7 per-node timestamp gate: fresh keys are
admitted vacuously, and an equal timestamp does **not** replace.

Basic laws:

```lean
theorem mem_insertNodeCanonical_iff
theorem mem_insertNodeCanonical_of_mem_of_ne
theorem mem_of_mem_insertNodeCanonical_of_ne
theorem canonicalNodeAnnouncements_insertNodeCanonical
theorem insertNodeCanonical_eq_cons_of_fresh
theorem selectNodeAnnouncements_cons
theorem canonicalNodeAnnouncements_selectNodeAnnouncements
theorem mem_selectNodeAnnouncements
theorem selectNodeAnnouncements_nodup
theorem selectNodeAnnouncements_of_nodup_canonical
theorem selectNodeAnnouncements_idempotent
```

### 2.2 Node-canonical view

```lean
noncomputable def canonicalNodeStoreView (s : GossipState) : GossipState :=
  { canonicalStoreView s with
    nodeAnnouncements := selectNodeAnnouncements s.nodeAnnouncements }

def NodeCanonicalShape (s : GossipState) : Prop :=
  selectNodeAnnouncements s.nodeAnnouncements = s.nodeAnnouncements
```

with the projection, canonicality, idempotence, and exact fixed-point laws:

```lean
theorem canonicalNodeStoreView_announcements
theorem canonicalNodeStoreView_updates
theorem canonicalNodeStoreView_nodeAnnouncements
theorem canonicalNodeStoreView_nodeCanonical
theorem canonicalNodeStoreView_canonical
theorem canonicalNodeStoreView_updates_slotUnique
theorem nodeKeyConsistent_canonicalNodeStoreView
theorem canonicalNodeStoreView_idempotent
theorem canonicalNodeStoreView_eq_canonicalStoreView_of_select_eq_self
theorem canonicalNodeStoreView_eq_self_iff
```

### 2.3 Transition

```lean
noncomputable def applyGossipNodeCanonical (verify : SigVerifier)
    (cs : CanonicalStore) : GossipMessage → CanonicalStore
  | .channelAnnouncement a =>
      applyGossipCanonicalStore verify cs (.channelAnnouncement a)
  | .channelUpdate u =>
      applyGossipCanonicalStore verify cs (.channelUpdate u)
  | .nodeAnnouncement n =>
      if n.signatureValid verify ∧
          NodeSupersedes n cs.gossip.nodeAnnouncements then
        { gossip := { cs.gossip with
            nodeAnnouncements :=
              insertNodeCanonical n cs.gossip.nodeAnnouncements }
          nodeKeyOf := cs.nodeKeyOf }
      else cs
```

The announcement and update branches are **definitionally** the wave-7
canonical transition; no existing transition is edited:

```lean
theorem applyGossipNodeCanonical_announcement
theorem applyGossipNodeCanonical_update
theorem applyGossipNodeCanonical_node_of_admitted
theorem applyGossipNodeCanonical_node_of_rejected
theorem applyGossipNodeCanonical_node_eq_canonicalStore_of_fresh
theorem applyGossipNodeCanonical_gossip_nodeKeyOf_irrel
theorem applyGossipNodeCanonical_announcements
theorem applyGossipNodeCanonical_updates
```

### 2.4 Invariant

```lean
def StoreNodeAnnouncementsValid (verify : SigVerifier)
    (s : GossipState) : Prop :=
  ∀ n ∈ s.nodeAnnouncements, n.signatureValid verify

structure NodeCanonicalAdmitted (verify : SigVerifier)
    (cs : CanonicalStore) : Prop where
  base : CanonicalStoreAdmitted verify cs
  nodesValid : StoreNodeAnnouncementsValid verify cs.gossip
  nodesCanonical : CanonicalNodeAnnouncements cs.gossip.nodeAnnouncements

inductive ReachableNodeCanonical (verify : SigVerifier) :
    CanonicalStore → Prop
  | empty (nodeKeyOf : NodeId → PubKey) :
      ReachableNodeCanonical verify
        { gossip := ⟨[], [], []⟩, nodeKeyOf := nodeKeyOf }
  | step {cs : CanonicalStore} {m : GossipMessage} :
      ReachableNodeCanonical verify cs →
        ReachableNodeCanonical verify
          (applyGossipNodeCanonical verify cs m)
```

Preservation and projections:

```lean
theorem canonicalStoreAdmitted_applyGossipCanonicalStore
theorem nodeCanonicalAdmitted_applyGossipNodeCanonical
theorem reachableNodeCanonical_invariant
theorem reachableNodeCanonical_nodesCanonical
theorem reachableNodeCanonical_nodesValid
theorem reachableNodeCanonical_store_invariant
theorem reachableNodeCanonical_nodeKeyConsistent
theorem reachableNodeCanonical_canonical
theorem reachableNodeCanonical_updates_slotUnique
```

## 3. Headline claims

### 3.1 Reachable replacement is real

```lean
theorem reachableNodeCanonical_node_replacement :
    ∃ (verify : SigVerifier) (cs : CanonicalStore)
      (nOld nNew : NodeAnnouncement),
      ReachableNodeCanonical verify cs ∧
        nOld.nodeId = nNew.nodeId ∧
          nOld.timestamp < nNew.timestamp ∧
            nNew ∈ cs.gossip.nodeAnnouncements ∧
              nOld ∉ cs.gossip.nodeAnnouncements
```

Witness: two-step reachable store with `nA1` (timestamp `10`) then `nA2`
(timestamp `20`) on the same `nodeId`; the stored list is `[nA2]`.

### 3.2 Rotation is a distinct slot, not a replacement

```lean
theorem reachableNodeCanonical_rotation_keeps_both :
    ∃ (verify : SigVerifier) (cs : CanonicalStore)
      (nOld nNew : NodeAnnouncement),
      ReachableNodeCanonical verify cs ∧
        nOld.nodeId ≠ nNew.nodeId ∧
          nOld.alias = nNew.alias ∧
            nOld ∈ cs.gossip.nodeAnnouncements ∧
              nNew ∈ cs.gossip.nodeAnnouncements ∧
                CanonicalNodeAnnouncements cs.gossip.nodeAnnouncements
```

Witness: `nA1` (`nodeId = kA`) and `nB1` (`nodeId = kB`) share the same alias
bytes, yet both survive because the canonical slot key is `nodeId`. This is the
node analogue of the wave-6 registration-only rotation boundary. The theorem
does **not** assert that `kA` and `kB` are the same physical identity; it proves
the model's observable behaviour when a rotation is presented as a new key.

Rekeying is orthogonal to the node layer:

```lean
theorem applyGossipNodeCanonical_gossip_rotateNodeKey
theorem canonicalNodeAnnouncements_rekeyStore
theorem reachableNodeCanonical_rekeyStore
```

`rotateNodeKey` on the `NodeId → PubKey` registration map and `rekeyStore` on
channel announcements leave `gossip`/node canonicality unchanged.

### 3.3 Equal-timestamp boundary is unrecoverable

```lean
theorem reachableNodeCanonical_equal_timestamp_tie_boundary :
    ∃ (verify : SigVerifier) (cs : CanonicalStore)
      (nOld nTie : NodeAnnouncement),
      ReachableNodeCanonical verify cs ∧
        nOld ∈ cs.gossip.nodeAnnouncements ∧
          nTie ∉ cs.gossip.nodeAnnouncements ∧
            nOld.nodeId = nTie.nodeId ∧
              nOld.timestamp = nTie.timestamp ∧
                nOld ≠ nTie ∧
                  ¬ CanonicalNodeAnnouncements
                    (applyGossip cs.gossip (.nodeAnnouncement nTie)).nodeAnnouncements ∧
                    selectNodeAnnouncements
                        (applyGossip cs.gossip (.nodeAnnouncement nTie)).nodeAnnouncements =
                      [nTie] ∧
                      (canonicalNodeStoreView
                        (applyGossip cs.gossip (.nodeAnnouncement nTie))).nodeAnnouncements =
                        [nTie] ∧
                        cs.gossip.nodeAnnouncements = [nOld]
```

With equal timestamps the BOLT 7 gate has no strict winner, so the canonical
transition keeps the first-arrived record; raw append puts the late record at
the head and the order-only selector picks it. No content/signature
tie-breaker is modelled, and no theorem claims one.

The matching impossibility result:

```lean
theorem no_canonical_node_preserving_raw_node_extension :
    ¬ ∃ F : GossipState → GossipMessage → GossipState,
      (∀ (s : GossipState) (n : NodeAnnouncement),
        F s (.nodeAnnouncement n) = applyGossip s (.nodeAnnouncement n)) ∧
      (∀ s : GossipState, CanonicalNodeAnnouncements s.nodeAnnouncements →
        ∀ m : GossipMessage,
          CanonicalNodeAnnouncements (F s m).nodeAnnouncements)
```

Any transition that keeps raw append semantics for node announcements cannot
preserve `CanonicalNodeAnnouncements` from the empty store.

This is the exact gap in the existing view:

```lean
theorem canonicalStoreView_does_not_canonicalise_nodes :
    ∃ (s : GossipState) (n : NodeAnnouncement),
      CanonicalNodeAnnouncements s.nodeAnnouncements ∧
        ¬ CanonicalNodeAnnouncements
          (canonicalStoreView (applyGossip s (.nodeAnnouncement n))).nodeAnnouncements
```

### 3.4 Per-slot / global-clock boundary

```lean
theorem reachableNodeCanonical_node_slot_ignores_global_clock :
    ∃ (verify : SigVerifier) (cs : CanonicalStore) (n : NodeAnnouncement),
      ReachableNodeCanonical verify cs ∧
        cs.gossip.latestUpdateTimestamp = 100 ∧
          n.timestamp = 5 ∧
            NodeSupersedes n cs.gossip.nodeAnnouncements ∧
              (applyGossipNodeCanonical verify cs
                (.nodeAnnouncement n)).gossip.nodeAnnouncements = [n] ∧
                n.timestamp < cs.gossip.latestUpdateTimestamp
```

A reachable store with a channel-update global clock of `100` admits a node
announcement at timestamp `5`, because the node gate is per `nodeId` and never
consults `latestUpdateTimestamp`. Node canonicalisation therefore does not
subsume or alter the raw global update clock.

## 4. Preserved wave-7/wave-8 results

All re-exports have the original statements (no weakening, no renaming):

```lean
theorem raw_nonrefinement_preserved
theorem raw_announcement_extension_impossible_preserved
theorem per_slot_global_clock_boundary_preserved
theorem epoch_square_preserved
theorem epoch_fold_store_square_preserved
theorem epoch_square_lifts_to_node_canonical_view
```

The last theorem is the only new statement in this group:

```lean
theorem epoch_square_lifts_to_node_canonical_view
    (verify : SigVerifier) (e : StoreEpoch) (s : GossipState)
    (msgs : List GossipMessage)
    (hobs : e.store.gossip = canonicalStoreView s)
    (hadm : EpochAdmittedAlong verify e msgs)
    (hraw : RawAdmittedAlong s msgs)
    (hnd : (rawFold s msgs).nodeAnnouncements.Nodup)
    (hnc : CanonicalNodeAnnouncements (rawFold s msgs).nodeAnnouncements) :
    (epochFold verify e msgs).store.gossip =
      canonicalNodeStoreView (rawFold s msgs)
```

The two extra hypotheses are exactly what makes node selection the identity;
the underlying epoch square is then used unchanged.

## 5. Validation

### 5.1 Required build

Command (exactly the lane-prescribed form, from `/home/ubuntu/ln-lean-repair`):

```sh
export PATH=/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Proofs.Routing.NodeCanonicalTargets
```

Result:

```text
Build completed successfully (15 jobs).
RC=0
```

No warning is emitted for `NodeCanonicalTargets.lean`. The only warnings in the
dependency closure are pre-existing linter warnings in
`GossipStoreEpochTargets.lean`. No full `lake build` was run.

### 5.2 Forbidden-construct scan

```sh
grep -nE '\b(sorry|axiom|admit|native_decide|unsafe)\b|implemented_by' \
  LnLean/Proofs/Routing/NodeCanonicalTargets.lean
```

The only matches are the two docstring lines that say the module contains none
of them. There are **0 code occurrences**. The successful build also confirms
that no `sorry` remains (Lean emits a declaration warning for `sorry`). No
`axiom`, `admit`, `native_decide`, `unsafe`, or `@[implemented_by]` is used.

### 5.3 Axiom audit

Audit file (external to the repository):

```lean
import LnLean.Proofs.Routing.NodeCanonicalTargets
open LnLean.Proofs.Routing.NodeCanonicalTargets
#print axioms <declaration>   -- 59 public declarations
```

Run command:

```sh
export PATH=/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake env lean /tmp/opencode/audit_node.lean
```

Result: all 59 audited declarations report only subsets of

```text
propext
Classical.choice
Quot.sound
```

Specifically, 53 use all three, 3 use `propext` + `Quot.sound`, 1 uses only
`propext`, and 2 (`canonicalStoreAdmitted_nodeAnnouncements_irrel`,
`canonicalNodeAnnouncements_rekeyStore`) use none. No `sorryAx`, no user
`axiom`, and no other axiom appears.

## 6. Gaps and trust boundary

* **Identity across rotation is not proved.** `NodeAnnouncement.nodeId` is
  treated as the BOLT 7 node key (`PubKey` in this model). Proving that a new
  `nodeId` belongs to the same physical node is out of scope; the rotation
  theorem only states that a different key is a different canonical slot.
* **Equal timestamps are order-dependent.** There is no signature/content
  tie-breaker, matching the absence of one in the modelled BOLT 7 gate. The
  impossibility theorem rules out recovering a timestamp winner with
  raw-append semantics.
* **Wire membership is not modelled.** The module does not check that node
  announcements came from the peer set, are associated with a known channel,
  or pass chain-hash/UTXO checks. Address parsing, rate limits, and
  `node_announcement` relay policy are also out of scope.
* **`SigVerifier` remains abstract.** Signature validity is a parameter;
  unforgeability remains assumptions C3/C4/C8 in `docs/ASSUMPTIONS.md`.
* **No network/liveness claim.** The result is a state-transition invariant on
  reachable canonical stores, not a propagation or convergence theorem.
* **Integration is not performed.** The module is not imported by the root or
  catalog; that is deliberately left to the integrator.

## 7. `RT-02` catalog-integration recommendation

Recommendation: **narrow `RT-02` to rotation identity and wire membership, and
change its evidence text to point at this module; do not close it.**

Suggested status text:

> `RT-02` — P1 — open (narrowed to rotation identity and wire-level membership).
> `NodeCanonicalTargets` adds node-announcement canonicalisation: replace by
> `nodeId`, BOLT 7 strict-timestamp supersession, `CanonicalNodeAnnouncements`,
> a node-canonical view, `applyGossipNodeCanonical`, `ReachableNodeCanonical`,
> and `NodeCanonicalAdmitted`. It proves reachable replacement and rotation
> witnesses, an equal-timestamp unrecoverable boundary, an impossibility theorem
> for raw-append-preserving node extensions, and the per-slot/global-clock
> separation; wave-7 raw non-refinement and wave-8 epoch squares are re-exported
> unchanged. Remaining: identity/linkage across a `nodeId` rotation, wire
> membership/chain-existence checks, address parsing, and rate limits.

If the catalog is updated in a later integration wave, the import to add is
`LnLean.Proofs.Routing.NodeCanonicalTargets`. No change to `Gossip.lean`,
`GossipStoreEpochTargets.lean`, or `GossipCanonicalTargets.lean` is required.

## 8. Summary

The node-canonicalisation layer is implemented additively in one new module,
builds with the prescribed locked command, uses no forbidden construct, and all
59 public declarations are axiom-clean apart from the allowed trio. The
replacement, rotation, equal-timestamp, raw-impossibility, and per-slot/global
clock boundaries are all covered by explicit theorems. `RT-02` is narrowed but
not closed: the remaining gap is identity across rotation and wire-level
membership, both outside this lane's model.
