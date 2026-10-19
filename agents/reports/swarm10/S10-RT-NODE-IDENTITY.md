# S10-RT-NODE-IDENTITY — rotation witnesses, unlinkability, and wire membership

**Lane:** `S10-RT-NODE-IDENTITY`
**Issue:** `RT-02` (identity/linkage across a node-ID rotation; wire-level membership)
**Recommended catalog row:** `LN-RT-002`
**Branch:** `repair/integrated`
**Launch HEAD:** `7988c93` (base `9158592`)
**Status:** complete; scoped build, forbidden-token scan, and public-theorem
axiom audit clean
**Owned files created:**

* `LnLean/Proofs/Routing/NodeIdentityTargets.lean` — new, `1007` lines,
* `agents/reports/swarm10/S10-RT-NODE-IDENTITY.md` — this report.

No other file was created or modified by this lane. In particular
`LnLean/Routing/Gossip.lean`, `NodeCanonicalTargets.lean`, root imports,
`Obligations.lean`, `Traceability.lean`, `AxiomAudit.lean`, the catalog, and
all docs are untouched. No commit or push was performed. Other lanes'
working-tree changes are present and untouched.

---

## 1. Objective and verdict

Wave 9 (`NodeCanonicalTargets`) made node announcements canonical and proved
the rotation *boundary*: two records with different `nodeId`s are separate
canonical slots and both survive. It deliberately left three questions open:

1. **No linkage without evidence.** Two canonical node announcements with
   different wire `nodeId`s must not be treated as the same physical node just
   because both are stored.
2. **Positive linkage with evidence.** If an old-to-new rotation witness is
   supplied, the old channel endpoint can be mapped to the new key while
   preserving the relevant membership property.
3. **Wire membership.** A `channel_announcement` should only be considered
   backed when both of its wire `node_id` fields have node announcements, and
   admission must be connected to `NodeCanonicalAdmitted` without pretending
   that the existing core transition checks this.

**Verdict:** all three are modelled additively and proved. The result is
deliberately narrow:

* the witness is **opaque supplied evidence**, not a cryptographic proof of
  common ownership;
* the unlinkability theorem is sharp for relations that depend only on the
  node store's **backing pattern**;
* wire membership is **node-announcement membership at the key level**, not
  on-chain channel existence;
* the core transition is unchanged and still does **not** enforce membership.

`RT-02` remains open for the parts listed in §9. It is narrowed, not closed.

---

## 2. Model

Namespace: `LnLean.Proofs.Routing.NodeIdentityTargets`.
Import: `LnLean.Proofs.Routing.NodeCanonicalTargets` only.

### 2.1 Node backing

```lean
def NodeAnnouncedIn (l : List NodeAnnouncement) (k : PubKey) : Prop :=
  ∃ n ∈ l, n.nodeId = k

def NodeAnnounced (s : GossipState) (k : PubKey) : Prop :=
  NodeAnnouncedIn s.nodeAnnouncements k

def NodeAnnouncedValid (verify : SigVerifier) (s : GossipState)
    (k : PubKey) : Prop :=
  ∃ n ∈ s.nodeAnnouncements, n.nodeId = k ∧ n.signatureValid verify
```

`NodeAnnouncement.nodeId` is the BOLT 7 wire `node_id` (`PubKey` in this
model). The graph `NodeId` is a separate opaque index; the registration map
`nodeKeyOf : NodeId → PubKey` is the bridge. Wire membership is stated on the
wire key fields `nodeKey1`/`nodeKey2`, which are the `node_id` values carried
by `channel_announcement`.

Core backing laws:

| Theorem | Line | Statement |
|---|---:|---|
| `nodeAnnounced_of_valid` | 101 | valid backing implies backing |
| `nodeAnnouncedIn_mono` | 107 | backing is monotone in the node list |
| `nodeAnnounced_mono` | 114 | backing is monotone in the store |
| `nodeAnnouncedIn_insertNodeCanonical_iff` | 123 | `NodeAnnouncedIn (insertNodeCanonical n l) k ↔ n.nodeId = k ∨ NodeAnnouncedIn l k` |
| `nodeAnnounced_insertNodeCanonical_iff` | 138 | store form of the same |
| `nodeAnnounced_applyGossipNodeCanonical` | 150 | backing is preserved by every canonical gossip step |
| `nodeAnnouncedValid_applyGossipNodeCanonical` | 174 | valid backing is preserved by every canonical gossip step |
| `nodeAnnouncedValid_of_nodeCanonicalAdmitted` | 204 | `NodeCanonicalAdmitted` certifies every backed key |
| `reachable_nodeAnnouncedValid` | 212 | the same on `ReachableNodeCanonical` states |

The key monotonicity theorem is precise: **canonical node replacement never
withdraws a key**. Same-key replacement removes the old *record* but keeps the
key (the new record carries it); different-key rotation keeps the old record
and the old key.

### 2.2 Rotation witness

```lean
structure RotationWitness where
  oldId : PubKey
  newId : PubKey
  evidence : ByteArray
  distinct : oldId ≠ newId
```

`evidence` is deliberately opaque. Nothing in `GossipState` produces,
validates, or authenticates it. The witness has no derivation rule from the
store; the model does not claim it is a cryptographic proof. A linkage claim
is the explicit proposition

```lean
def RotationWitness.Links (w) (old new : PubKey) : Prop :=
  w.oldId = old ∧ w.newId = new

def RotationLink (old new : PubKey) : Prop :=
  ∃ w : RotationWitness, w.Links old new
```

The witness rewrites the two wire key fields of a channel announcement:

```lean
noncomputable def RotationWitness.mapKey (w) (k : PubKey) : PubKey :=
  if k = w.oldId then w.newId else k

noncomputable def RotationWitness.rotateChannel
    (w : RotationWitness) (a : ChannelAnnellation) : ChannelAnnellation :=
  { a with
    nodeKey1 := w.mapKey a.nodeKey1
    nodeKey2 := w.mapKey a.nodeKey2 }
```

---

## 3. Negative result: no store-only orientation

### 3.1 The exact predicate

`StoreOnly s R` means `R` depends only on which wire keys the node list backs:

```lean
def StoreOnly (s : GossipState) (R : PubKey → PubKey → Prop) : Prop :=
  ∀ x y x' y',
    (NodeAnnounced s x ↔ NodeAnnounced s x') →
    (NodeAnnounced s y ↔ NodeAnnounced s y') →
    (R x y ↔ R x' y')
```

This is exactly the information available to a backing or graph-membership
check that has no external rotation evidence.

### 3.2 Sharp negative theorem

| Theorem | Line | Statement |
|---|---:|---|
| `storeOnly_symm_of_coannounced` | 234 | on two co-announced keys, every store-only relation is symmetric |
| `no_oriented_store_only_link` | 246 | no antisymmetric store-only relation holds between two distinct co-announced keys |
| `canonical_distinct_nodes_no_oriented_store_link` | 260 | on a canonical list, two records with different `nodeId`s are distinct, each key has a unique slot, every store-only relation is symmetric, and an antisymmetric one is impossible |
| `concrete_intended_rotation_not_storeOnly` | 716 | the intended orientation `(fun a b => a = kA ∧ b = kB)` is **not** store-only on a reachable canonical store |
| `concrete_same_store_both_orientations` | 747 | one reachable canonical store is compatible with both witness orientations |
| `no_store_function_selects_both_rotation_worlds` | 762 | no function of the store can return both orientations on the same store |
| `rotationLink_irrefl` | 987 | a witness never links a key to itself |
| `concrete_rotationLink_not_storeOnly` | 997 | the actual `RotationLink` relation is not store-only on a reachable canonical store |

The `no_store_function_selects_both_rotation_worlds` theorem is the
non-identifiability form. Since `s` is literally the same object in both
hypotheses, any selector `f : GossipState → PubKey × PubKey` has one value on
`s`; it cannot equal both `(old, new)` and `(new, old)`.

The last two rows close the stronger question: it is not merely hard to select
an orientation from the store, the linkage relation itself is not the kind of
object a backing pattern determines. `rotationLink_irrefl` records that a
witness always relates distinct keys, and `concrete_rotationLink_not_storeOnly`
uses the reachable store `nsRot` to show that `RotationLink kA kB` holds while
`RotationLink kA kA` does not, although `kA` and `kA` have identical backing
status. Hence no `StoreOnly` relation can coincide with `RotationLink`.

### 3.3 Concrete witnesses

The concrete keys are `kA` (1 byte), `kB` (0 bytes), and `kC` (2 bytes); the
concrete store `nsRot` is reachable by three canonical node steps and has

```lean
nsRot.gossip.nodeAnnouncements = [nB1, nA1]
kA ≠ kB
```

`nA1` is the old `kA` record, `nB1` the new `kB` record. Both are stored, and
both orientations have witnesses (`rotAB : kA → kB`, `rotBA : kB → kA`), so the
store cannot choose between them. The concrete intended orientation is proved
not to be `StoreOnly`.

---

## 4. Positive linkage with a supplied witness

### 4.1 Preserved properties

| Theorem | Line | Statement |
|---|---:|---|
| `rotation_preserves_wireMember` | 420 | if the new key is backed and the channel is a wire member, the rewritten channel is a wire member |
| `rotation_preserves_wireMemberCertified` | 439 | same with signature-valid backing for the new key |
| `rotation_preserves_channel_identity` | 459 | `shortChannelId`, graph `node1`/`node2`, and `capacitySat` are unchanged |
| `graphBacked_of_nodeKeyConsistent` | 478 | under `NodeKeyConsistent`, both graph endpoints of a wire-member channel are `GraphBacked` |
| `rotateNodeKey_preserves_graphBacked` | 497 | registration-level rotation preserves `GraphBacked` exactly when the new key is backed |

The positive theorem is an implication, not a store function: it consumes
`w : RotationWitness` and `hnew : NodeAnnounced s w.newId` as explicit inputs.
It maps the old endpoint key to the new key and preserves the membership
predicate. It does not claim that the store produced the witness.

### 4.2 Not preserved: signatures and old records

| Theorem | Line | Statement |
|---|---:|---|
| `rotation_breaks_signatures` | 821 | the concrete rewrite `kA → kC` invalidates the signature under a key-sensitive verifier |
| `rotation_not_signature_preserving` | 835 | there exist a verifier, witness, and channel valid before and invalid after the rewrite |
| `concrete_rotation_keeps_old_record` | 775 | a different-key rotation keeps both `nA1` and `nB1` stored |
| `concrete_supersession_removes_old_record` | 784 | same-key supersession removes the old record |

This makes the phrase "old announcements may remain until superseded" exact:

* rotation to a different key is a distinct canonical slot, so the old record
  and key remain;
* same-key replacement (`NodeSupersedes` with a strictly greater timestamp)
  removes the old record but keeps the key backed by the new record.

A production rotation must re-sign the rewritten channel. The model proves the
necessity of that step but does not model the re-signing digest/domain.

---

## 5. Wire membership and admission

### 5.1 Definition

```lean
structure WireMember (s : GossipState) (a : ChannelAnnellation) : Prop where
  first : NodeAnnounced s a.nodeKey1
  second : NodeAnnounced s a.nodeKey2

structure WireMemberCertified (verify : SigVerifier) (s : GossipState)
    (a : ChannelAnnellation) : Prop where
  first : NodeAnnouncedValid verify s a.nodeKey1
  second : NodeAnnouncedValid verify s a.nodeKey2
```

The endpoint predicate is on the wire `node_id` fields, not the opaque graph
indices. `graphBacked_of_nodeKeyConsistent` bridges the two under the existing
`NodeKeyConsistent` invariant.

### 5.2 Admission theorem

| Theorem | Line | Statement |
|---|---:|---|
| `wireMember_of_certified` | 392 | certified membership implies membership |
| `reachable_wireMemberCertified` | 398 | a reachable node-canonical store certifies every wire member |
| `wireMember_applyGossipNodeCanonical` | 409 | wire membership is monotone under the canonical node transition |
| `channelAnnouncement_admitted_of_wireMember` | 852 | under `NodeCanonicalAdmitted`, certified membership plus the existing canonical channel gates yields admission, preserved membership, and preserved invariant |
| `concrete_admission_with_wireMember` | 922 | non-vacuous concrete instance on `nsRot` |

The admission theorem is a **combined-gate** theorem. The membership hypothesis
is additive: the existing transition does not consume it. The theorem does not
say that `NodeCanonicalAdmitted` implies membership.

### 5.3 Missing-endpoint counterexample

| Theorem | Line | Statement |
|---|---:|---|
| `missing_endpoint_channel_admitted` | 940 | a reachable node-canonical store backs `kA` but not `kB`; `annA` names `kA`/`kB`; `annA` is admitted anyway |
| `nodeCanonicalAdmitted_not_wireMember` | 963 | `NodeCanonicalAdmitted` does not imply `WireMember` |
| `empty_store_admits_unbacked_channel` | 976 | the empty store admits a channel whose endpoints are unbacked |

This is the exact "connect, but do not overclaim" boundary: the canonical node
store is the right invariant for the *node* side, but the core channel
admission path still accepts an announcement with a missing endpoint. A future
production gate should add `WireMemberCertified` (or an equivalent) to the
channel-admission predicate and re-sign rotated announcements.

---

## 6. Validation

### 6.1 Required scoped build

Command, from `/home/ubuntu/ln-lean-repair`:

```sh
export PATH=/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Proofs.Routing.NodeIdentityTargets
```

Result:

```text
Build completed successfully (16 jobs).
RC=0
```

No warning is emitted for `LnLean/Proofs/Routing/NodeIdentityTargets.lean`
(zero matching lines in the build log). The 29 warning lines in the dependency
closure are pre-existing: 12 in `GossipProps.lean` (deprecated
`if_pos`/`if_neg`) and 17 in `GossipStoreEpochTargets.lean` (unused variables /
unused `simp` arguments).
No full `lake build` was run.

### 6.2 Forbidden-token scan

```sh
grep -nE '\b(sorry|axiom|admit|native_decide|unsafe)\b|implemented_by' \
  LnLean/Proofs/Routing/NodeIdentityTargets.lean
```

Result: **no matches**. There are zero code occurrences and zero docstring
occurrences of the forbidden tokens. The file also contains no `@[implemented_by]`.

### 6.3 Axiom audit

Audit file: `/tmp/opencode/audit_node_identity.lean` (external to the repo).

```lean
import LnLean.Proofs.Routing.NodeIdentityTargets
open LnLean.Proofs.Routing.NodeIdentityTargets
#print axioms <declaration>   -- all 47 public theorems
```

Result:

* 47 public theorems audited,
* 32 depend on `{propext, Classical.choice, Quot.sound}`,
* 14 depend on no axioms,
* 1 (`rotateNodeKey_preserves_graphBacked`) depends only on `propext`,
* no `sorryAx`, no user `axiom`, and no other axiom appears.

The audit includes all 47 public theorem declarations, including the
`RotationWitness.mapKey_*` and `RotationWitness.rotateChannel_*` lemmas.

### 6.4 Public theorem inventory (47)

`nodeAnnounced_of_valid`,
`nodeAnnouncedIn_mono`,
`nodeAnnounced_mono`,
`nodeAnnouncedIn_insertNodeCanonical_iff`,
`nodeAnnounced_insertNodeCanonical_iff`,
`nodeAnnounced_applyGossipNodeCanonical`,
`nodeAnnouncedValid_applyGossipNodeCanonical`,
`nodeAnnouncedValid_of_nodeCanonicalAdmitted`,
`reachable_nodeAnnouncedValid`,
`storeOnly_symm_of_coannounced`,
`no_oriented_store_only_link`,
`canonical_distinct_nodes_no_oriented_store_link`,
`RotationWitness.mapKey_old`,
`RotationWitness.mapKey_of_ne`,
`RotationWitness.mapKey_new`,
`RotationWitness.rotateChannel_shortChannelId`,
`RotationWitness.rotateChannel_node1`,
`RotationWitness.rotateChannel_node2`,
`RotationWitness.rotateChannel_capacitySat`,
`RotationWitness.rotateChannel_nodeKey1`,
`RotationWitness.rotateChannel_nodeKey2`,
`rotationLink_iff`,
`wireMember_of_certified`,
`reachable_wireMemberCertified`,
`wireMember_applyGossipNodeCanonical`,
`rotation_preserves_wireMember`,
`rotation_preserves_wireMemberCertified`,
`rotation_preserves_channel_identity`,
`graphBacked_of_nodeKeyConsistent`,
`rotateNodeKey_preserves_graphBacked`,
`concrete_intended_rotation_not_storeOnly`,
`concrete_both_rotation_witnesses`,
`concrete_rotationLink_both_directions`,
`concrete_same_store_both_orientations`,
`no_store_function_selects_both_rotation_worlds`,
`concrete_rotation_keeps_old_record`,
`concrete_supersession_removes_old_record`,
`concrete_rotation_preserves_wireMember`,
`rotation_breaks_signatures`,
`rotation_not_signature_preserving`,
`channelAnnouncement_admitted_of_wireMember`,
`concrete_admission_with_wireMember`,
`missing_endpoint_channel_admitted`,
`nodeCanonicalAdmitted_not_wireMember`,
`empty_store_admits_unbacked_channel`,
`rotationLink_irrefl`,
`concrete_rotationLink_not_storeOnly`.

---

## 7. Catalog integration recommendation (`LN-RT-002`)

Recommendation: **keep `LN-RT-002` `proved`, add
`LnLean.Proofs.Routing.NodeIdentityTargets` as evidence, and narrow the `RT-02`
issue text to the remaining boundaries in §9.** Do not add a new catalog row
unless the parent wants rotation/linkage as a separate routing target; the
existing `LN-RT-002` row already covers gossip replacement and node
canonicalisation.

Suggested target additions (headline set, not all 47):

```text
LnLean.Proofs.Routing.NodeIdentityTargets.canonical_distinct_nodes_no_oriented_store_link
LnLean.Proofs.Routing.NodeIdentityTargets.no_store_function_selects_both_rotation_worlds
LnLean.Proofs.Routing.NodeIdentityTargets.concrete_intended_rotation_not_storeOnly
LnLean.Proofs.Routing.NodeIdentityTargets.rotation_preserves_wireMember
LnLean.Proofs.Routing.NodeIdentityTargets.rotation_not_signature_preserving
LnLean.Proofs.Routing.NodeIdentityTargets.channelAnnouncement_admitted_of_wireMember
LnLean.Proofs.Routing.NodeIdentityTargets.missing_endpoint_channel_admitted
LnLean.Proofs.Routing.NodeIdentityTargets.wireMember_applyGossipNodeCanonical
LnLean.Proofs.Routing.NodeIdentityTargets.graphBacked_of_nodeKeyConsistent
```

Suggested `LN-RT-002` evidence text:

> Node announcements gain an additive identity/linkage layer. Canonical
> node announcements with different wire `nodeId`s are distinct slots, and no
> antisymmetric store-only relation can link them
> (`canonical_distinct_nodes_no_oriented_store_link`,
> `no_store_function_selects_both_rotation_worlds`). An explicit
> `RotationWitness` maps the old wire key to the new key and preserves wire
> membership (`rotation_preserves_wireMember`), while signatures are not
> preserved (`rotation_not_signature_preserving`). Wire membership requires
> both `channel_announcement` wire keys to have node announcements; the core
> transition does not enforce it (`missing_endpoint_channel_admitted`). Identity
> across rotation, chain existence, address parsing, and rate limits remain
> open.

If the parent adds root imports, the import is
`LnLean.Proofs.Routing.NodeIdentityTargets`. No change to `Gossip.lean`,
`NodeCanonicalTargets.lean`, or any catalog source file is required by this
lane.

---

## 8. Integration notes

* The module is **additive** and imports only
  `LnLean.Proofs.Routing.NodeCanonicalTargets`.
* No existing theorem statement is changed or weakened.
* The supported path remains `applyGossipNodeCanonical` /
  `ReachableNodeCanonical`; the new layer only reads the node list and the
  registration map.
* The concrete witnesses (`ns0`, `ns1`, `ns2`, `nsRot`, `annA`) are private to
  the module; the public theorems expose their existence, not the
  implementation details.
* `RotationWitness` is a `structure`, so downstream code can construct it but
  cannot derive it from `GossipState`. This is intentional.

---

## 9. Precise remaining boundary

The following are **not** modelled or proved; they remain `RT-02` follow-ups.

1. **Identity across rotation.** The witness is opaque. There is no
   cryptographic ownership proof, no key-history/consensus proof, and no
   theorem that `oldId` and `newId` belong to one physical node. The model only
   proves what follows *given* a witness. Address/alias equality is not
   identity evidence; the wave-9 rotation witness already shows two records
   with the same alias remain distinct slots.
2. **Wire-level chain existence / membership.** `WireMember` checks only that
   both wire `node_id` keys have node announcements in the store. It does not
   check the chain hash, the funding outpoint/UTXO, on-chain
   `channel_announcement` confirmation, or graph edge existence. A channel can
   therefore be a wire member while its funding transaction is unconfirmed or
   absent from the model.
3. **Address parsing.** `NodeAnnouncement.addresses : List ByteArray` is an
   opaque list. No length/type parsing, no IPv4/IPv6/Tor v3 validation, and no
   address-based identity or reachability is modelled.
4. **Rate limits and relay policy.** `gossip_queries`, peer dissemination,
   per-peer rate limits, and `node_announcement` relay policy are absent.
5. **Re-signing after rotation.** The model proves that the raw rewrite does
   not preserve signatures, but it does not model the BOLT 7 digest/domain or
   the re-signing procedure. A production rotation must re-sign; that step is
   an obligation, not a theorem.
6. **Equal-timestamp ties.** The wave-9 timestamp-tie boundary is unchanged:
   equal-timestamp records for the same `nodeId` have no strict winner, and
   canonicalisation keeps the first-arrived record.
7. **Abstract verifier.** `SigVerifier` is still a parameter; unforgeability
   remains assumptions C3/C4/C8 in `docs/ASSUMPTIONS.md`.
8. **No full BOLT 7 gossip validation claim.** The module proves a state-level
   invariant and a concrete admission counterexample; it does not claim
   complete BOLT 7 gossip validation or node-level interoperability.

---

## 10. Summary

The new module implements the requested rotation/linkage and wire-membership
layer in one additive Lean file:

* an explicit `RotationWitness`/`RotationLink` that is not derived from the
  store;
* a sharp negative: two canonical node announcements with different
  `nodeId`s have distinct slots and no antisymmetric store-only link; the same
  store is compatible with both witness directions and no store function
  selects both; the actual `RotationLink` relation is itself proved not
  store-only (`concrete_rotationLink_not_storeOnly`);
* a positive linkage theorem under a supplied witness, preserving wire
  membership while showing signatures and old records are not preserved;
* a wire-membership model with a combined admission theorem and a concrete
  missing-endpoint counterexample proving `NodeCanonicalAdmitted` does not
  imply membership;
* an explicit, honest boundary list (identity, chain existence, addresses,
  rate limits, re-signing, ties, abstract verifier, no full BOLT 7 claim).

The scoped build passes (`16 jobs`, RC 0), the forbidden-token scan is empty,
and all 47 public theorems are axiom-clean apart from the allowed trio.
