# S11-RT-NODE-CHAIN — signed rotation certificates, chains, re-signing, and replay gates

**Lane:** `S11-RT-NODE-CHAIN`
**Issue:** `RT-02` (identity across a `nodeId` rotation; signed evidence,
chains, re-signed channel announcements, rate/replay)
**Recommended catalog row:** `LN-RT-002`
**Branch:** `repair/integrated`
**Status:** complete; scoped build, forbidden-token scan, and 86-theorem axiom
audit clean

**Owned files created:**

* `LnLean/Proofs/Routing/NodeIdentityChainTargets.lean` — new, 1251 lines,
* `agents/reports/swarm11/S11-RT-NODE-CHAIN.md` — this report.

No existing Lean file, root import, catalog, traceability, audit, docs, script,
or test was edited by this lane. No commit or push was performed. Other lanes'
working-tree changes are present and untouched.

---

## 1. Objective and verdict

Wave 10 `NodeIdentityTargets` proved the store-only unlinkability boundary and
supplied an **opaque** `RotationWitness`, but explicitly left open:

1. a concrete signed rotation certificate (old key, new key, epoch, signature,
   signed message);
2. a transitive chain of certificates, with composition and an acyclicity
   boundary;
3. a re-signing model for a channel announcement after rotation, including the
   stale-signature failure;
4. a node-announcement timestamp/sequence rate-limit and replay model;
5. non-vacuity and concrete rejected cases;
6. exact obstruction results where the stronger claim is impossible.

All six are mechanized additively in the new module.

**Verdict.** The module is a faithful *evidence and admission* layer, not a
cryptographic identity proof. A certificate is signed only relative to an
explicit `SigVerifier`. Chains establish linkage, not physical ownership.
`RotationChain.Acyclic` is an extra predicate; distinct hops alone do **not**
exclude cycles (`hop_distinct_not_imply_acyclic`). A stale signature does
**not** authenticate a rewritten key (`signature_preservation_not_universal`).
The strongest true re-signing statement is conditional on an explicit fresh
four-way signature check (`SignedResignation`).

`RT-02` remains open for cryptography (key-binding/unforgeability), address
parsing, relay policy, and network-level rate limits. This lane narrows it; it
does not close it.

---

## 2. Verification evidence

**Build command (exact):**

```text
cd /home/ubuntu/ln-lean-repair && \
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Proofs.Routing.NodeIdentityChainTargets
```

**Result:** `Build completed successfully (19 jobs)`, RC 0.

**Forbidden-token scan on the owned module** (comments and strings stripped,
same policy as `scripts/check.py`):

```text
violations: 0
sorry=0 axiom=0 admit=0 native_decide=0 unsafe=0 implemented_by=0
```

**Axiom audit:** every public theorem was enumerated and checked with
`#print axioms` in a temporary file outside the repository. 86/86 theorems have
an output, and the only axiom names reported anywhere are:

```text
propext
Quot.sound
Classical.choice
```

No `sorryAx`, no project axiom, no `native_decide` axiom, no `implemented_by`.
The audit script is not committed.

---

## 3. Model

Namespace: `LnLean.Proofs.Routing.NodeIdentityChainTargets`.
Imports: `LnLean.Proofs.Routing.NodeIdentityTargets` and
`LnLean.Crypto.KeyModel`.

### 3.1 Signed rotation certificate

`rotationMessage` (line 112) is a tagged byte string over the old key, new
key, and epoch. `RotationCertificate` (line 118) stores:

```lean
structure RotationCertificate where
  oldId : PubKey
  newId : PubKey
  epoch : Nat
  message : ByteArray
  signature : GossipSignature
  distinct : oldId ≠ newId
  message_eq : message = rotationMessage oldId newId epoch
```

`SignedBy` / `Signed` (lines 137/142) are the abstract-verifier predicates.
`toWitness` (line 152) embeds a certificate into the wave-10 opaque
`RotationWitness`; the certificate therefore *implies* the opaque linkage, but
not conversely. This is made exact in §5.1.

### 3.2 Chains

`RotationChainLinked` (line 206) is the inductive transitive linkage:
empty at any key, or a certificate whose `oldId` matches the current start
prepended to a linked remainder. `RotationChain` (line 250) packages
`start`, `certs`, `finish`, and the linkage proof. `comp` (line 272) appends
two chains at a matching endpoint. `visited` (line 305) is
`start :: certs.map newId`; `Acyclic` (line 309) is `visited.Nodup`.
`Authenticated` (line 351) requires every certificate to pass the verifier.

### 3.3 Re-signing

`ResignedChannel` (line 413) carries the base announcement, the authorising
certificate, a new digest, and four replacement signatures. Its
`toAnnouncement` (line 433) rewrites only the two wire node keys and replaces
the digest/signature fields. `SignedResignation` (line 518) adds the explicit
proof that the rewritten record passes all four verifier checks. `admitted`
(line 543) connects it to the existing wave-10 canonical-channel admission
theorem.

### 3.4 Honest signing bridge

`keyModelVerifier` (line 568) lifts a `PrimitiveModel` ECDSA verifier to
`GossipSignature`. `signedCertificateOfSigner` (line 574) constructs a
certificate with `KeyModel.sign` from a seed, and
`signedCertificateOfSigner_signed` (line 589) proves it verifies under the
model's declared `correctOn` domain. No secret-key ownership or key-binding
claim is added.

### 3.5 Rate/replay gate

`NodeAnnouncementAdvert` (line 604) pairs an announcement with a sequence
number. `NodeRateState` (line 629) stores per-key last timestamp and last
sequence. `Accepts` (line 639) requires **both** strict inequalities.
`accept` (line 644) stamps the advert's values. `RateAdmitted` (line 752)
adds the signature check; `rateStep` (line 758) advances only on admission;
`rateFold` (line 813) folds a list.

---

## 4. Public theorem inventory

All names below are relative to
`LnLean.Proofs.Routing.NodeIdentityChainTargets.` unless a namespace is shown.
Line numbers are the declaration lines in the owned module.

### 4.1 Certificates and signed evidence

| Theorem | Line | Role |
|---|---:|---|
| `RotationCertificate.toWitness_oldId` | 158 | witness old key projection |
| `RotationCertificate.toWitness_newId` | 161 | witness new key projection |
| `RotationCertificate.toWitness_links` | 165 | witness links old to new |
| `RotationCertificate.signed_implies_link` | 170 | signed certificate implies `RotationLink` |
| `RotationCertificate.not_signedByNew_of_rejected` | 176 | explicit rejected new-key check gives `¬ SignedByNew` |
| `RotationCertificate.message_eq_rotationMessage` | 187 | stored message is the payload encoding |
| `RotationCertificate.toWitness_mapKey_old` | 192 | map rewrites the old key to the new key |
| `RotationCertificate.toWitness_mapKey_of_ne` | 197 | map leaves other keys unchanged |

### 4.2 Chain linkage and composition

| Theorem | Line | Role |
|---|---:|---|
| `RotationChainLinked.finish_eq_of_nil` | 219 | empty linkage has equal endpoints |
| `RotationChainLinked.append` | 226 | transitive-linkage composition |
| `RotationChainLinked.singleton` | 236 | one-certificate linkage |
| `RotationChainLinked.pair` | 241 | two-certificate linkage |
| `RotationChain.nil_start` | 280 | empty-chain start |
| `RotationChain.nil_finish` | 282 | empty-chain finish |
| `RotationChain.nil_certs` | 284 | empty-chain certificate list |
| `RotationChain.singleton_start` | 286 | singleton start |
| `RotationChain.singleton_finish` | 289 | singleton finish |
| `RotationChain.singleton_certs` | 292 | singleton list |
| `RotationChain.comp_start` | 295 | composition start |
| `RotationChain.comp_finish` | 298 | composition finish |
| `RotationChain.comp_certs` | 301 | composition concatenates certificates |
| `RotationChain.visited_nil` | 312 | visited keys of the empty chain |
| `RotationChain.visited_singleton` | 314 | visited keys of a singleton |
| `RotationChain.comp_visited` | 318 | visited keys of a composition |
| `RotationChain.acyclic_nil` | 325 | empty chain acyclic |
| `RotationChain.acyclic_singleton` | 330 | distinct singleton acyclic |
| `RotationChain.acyclic_no_revisit` | 340 | acyclicity is `Nodup` |
| `RotationChain.acyclic_start_not_mem_tail` | 345 | acyclic start is absent from the tail |
| `RotationChain.authenticated_nil` | 355 | empty chain authenticated |
| `RotationChain.authenticated_singleton_iff` | 361 | singleton authentication iff certificate signed |
| `RotationChain.authenticated_comp` | 373 | composition preserves authentication |
| `RotationChain.authenticated_hop_links` | 384 | every hop of an authenticated chain gives `RotationLink` |
| `chain_cycle_linked` | 397 | abstract two-hop cycle linkage |

### 4.3 Re-signing

| Theorem | Line | Role |
|---|---:|---|
| `ResignedChannel.toAnnouncement_shortChannelId` | 443 | identity preserved |
| `ResignedChannel.toAnnouncement_node1` | 446 | first graph endpoint preserved |
| `ResignedChannel.toAnnouncement_node2` | 449 | second graph endpoint preserved |
| `ResignedChannel.toAnnouncement_capacitySat` | 452 | capacity preserved |
| `ResignedChannel.toAnnouncement_nodeKey1` | 455 | first wire key is the rewrite |
| `ResignedChannel.toAnnouncement_nodeKey2` | 459 | second wire key is the rewrite |
| `ResignedChannel.toAnnouncement_digest` | 463 | digest replaced by the supplied digest |
| `ResignedChannel.preserves_identity` | 468 | combined identity/capacity preservation |
| `ResignedChannel.wireMember` | 479 | membership preserved under base membership + new-key backing |
| `ResignedChannel.not_wireMember_of_unbacked_new` | 500 | membership fails if the new key is unbacked |
| `ResignedChannel.graph_endpoints_preserved` | 509 | graph endpoints preserved |
| `SignedResignation.signaturesValid` | 527 | explicit four-way check exposed |
| `SignedResignation.wireMember` | 533 | membership with a signed resignation |
| `SignedResignation.admitted` | 543 | admission interface to `channelAnnouncement_admitted_of_wireMember` |
| `signedCertificateOfSigner_signed` | 589 | honest `KeyModel` certificate verifies |

### 4.4 Rate and replay

| Theorem | Line | Role |
|---|---:|---|
| `NodeAnnouncementAdvert.nodeId_mk` | 620 | advert node-key projection |
| `NodeAnnouncementAdvert.timestamp_mk` | 623 | advert timestamp projection |
| `NodeRateState.accepts_iff` | 652 | exact gate unfolding |
| `NodeRateState.accepted_timestamp_lt` | 659 | accepted timestamp strictly newer |
| `NodeRateState.accepted_sequence_lt` | 664 | accepted sequence strictly newer |
| `NodeRateState.accept_self_timestamp` | 669 | accept stamps own timestamp |
| `NodeRateState.accept_self_sequence` | 675 | accept stamps own sequence |
| `NodeRateState.accept_other_timestamp` | 681 | other keys unaffected (timestamp) |
| `NodeRateState.accept_other_sequence` | 687 | other keys unaffected (sequence) |
| `NodeRateState.timestamp_mono_accept` | 693 | accepted advert is timestamp-monotone |
| `NodeRateState.sequence_mono_accept` | 704 | accepted advert is sequence-monotone |
| `NodeRateState.replay_rejected` | 717 | same advert rejected after accept |
| `NodeRateState.same_timestamp_rejected` | 726 | same/older timestamp rejected |
| `NodeRateState.equal_sequence_rejected` | 734 | equal/older sequence rejected |
| `NodeRateState.acceptance_requires_both` | 742 | both strict gates are necessary |
| `rateStep_of_admitted` | 763 | admitted step advances |
| `rateStep_of_rejected` | 769 | rejected step is identity |
| `rateStep_of_bad_signature` | 775 | bad signature is identity |
| `rateStep_timestamp_mono` | 784 | step timestamp monotonicity |
| `rateStep_sequence_mono` | 794 | step sequence monotonicity |
| `rateStep_replay_rejected` | 805 | immediate replay rejected |
| `rateFold_nil` | 818 | empty fold |
| `rateFold_cons` | 821 | fold unfolding |
| `rateFold_timestamp_mono` | 827 | fold timestamp monotonicity |
| `rateFold_sequence_mono` | 837 | fold sequence monotonicity |
| `rateFold_replay_rejected` | 849 | replay rejected at any later fold point |

### 4.5 Non-vacuity, counterexamples, and exact obstructions

| Theorem | Line | Role |
|---|---:|---|
| `nonvacuity_witness` | 1092 | signed certificate + authenticated acyclic chain + rejected certificate |
| `opaque_link_not_authenticated` | 1106 | opaque witness exists; no certificate signed under `verifyNone` |
| `distinct_hops_not_acyclic` | 1120 | concrete cycle with every hop distinct but not acyclic |
| `hop_distinct_not_imply_acyclic` | 1128 | universal obstruction: hop distinctness does not imply acyclicity |
| `concrete_cycle_linked` | 1136 | concrete linked two-hop cycle returns to start |
| `old_signature_does_not_authenticate_new_keys` | 1144 | concrete stale-signature counterexample |
| `signature_preservation_not_universal` | 1157 | no universal rewrite-preserves-signature theorem |
| `opaque_link_not_imply_signed` | 1168 | opaque evidence does not imply authentication under `verifyNone` |
| `stale_resign_preserves_identity` | 1181 | stale rewrite preserves identity/endpoints/capacity |
| `concrete_rate_boundaries` | 1224 | accepted fresh advert and three rejected boundaries |
| `concrete_rateStep_replay` | 1234 | signed gate accepts then rejects replay |
| `concrete_rejected_cases` | 1242 | unsigned certificate and stale channel signature |

---

## 5. Key results in detail

### 5.1 Opaque evidence is strictly weaker than a signed certificate

`RotationCertificate.signed_implies_link` (line 170) shows that authenticated
evidence yields the wave-10 `RotationLink`. The converse is false in the exact
sense of `opaque_link_not_imply_signed` (line 1168):

```lean
¬ (∀ w : RotationWitness, RotationLink w.oldId w.newId →
    ∃ c : RotationCertificate,
      c.oldId = w.oldId ∧ c.newId = w.newId ∧ c.Signed verifyNone)
```

`opaque_link_not_authenticated` (line 1106) gives the same result
existentially and adds the concrete link `ckA → ckB`. The certificate is
therefore the correct evidence object; a witness alone is not.

### 5.2 Chain composition

`RotationChainLinked.append` (line 226) is the transitive composition theorem.
`RotationChain.comp` (line 272) packages it with endpoint equality, and
`comp_visited` (line 318) exposes the visited list. Authentication composes
(`authenticated_comp`, line 373), and every authenticated hop still supplies
only the opaque linkage (`authenticated_hop_links`, line 384).

### 5.3 Acyclicity is not a consequence of distinct hops

The concrete chain `chainCycle` is `ckA → ckB → ckA`. Every certificate
satisfies `oldId ≠ newId`, yet its visited list is `[ckA, ckB, ckA]`; hence it
is not acyclic. This is proved concretely (`distinct_hops_not_acyclic`, line
1120) and as a universal obstruction (`hop_distinct_not_imply_acyclic`, line
1128). An admission layer that needs acyclicity must carry
`RotationChain.Acyclic` (or an equivalent no-revisit check) as an explicit
condition. `acyclic_start_not_mem_tail` (line 345) is the direct `Nodup`
consequence used for that purpose.

### 5.4 Re-signing: the exact positive and negative statements

Positive: if the base announcement is a wire member and the new key is backed
by a node announcement, the rewritten record remains a wire member
(`ResignedChannel.wireMember`, line 479). If a fresh four-way signature check
is supplied, `SignedResignation` carries it (line 527) and the record can be
fed to the existing canonical admission theorem (line 543).

Negative 1: if the rewrite moves an endpoint to an unbacked new key, the
rewritten record is not a wire member
(`not_wireMember_of_unbacked_new`, line 500). A certificate is not a store
fact.

Negative 2: old signatures do not authenticate new keys
(`old_signature_does_not_authenticate_new_keys`, line 1144 and
`signature_preservation_not_universal`, line 1157). The concrete witness uses
keys of byte lengths 1, 0, and 2 (`ckA`, `ckB`, `ckC`), a verifier that rejects
only `ckC`, and a rewrite `ckA → ckC`. The base record verifies; the rewritten
first wire key is `ckC`; the retained old signature is rejected. Identity,
graph endpoints, and capacity are unchanged (`stale_resign_preserves_identity`,
line 1181), so the failure is exactly the key/signature mismatch.

### 5.5 Rate/replay

The gate is deliberately two-dimensional. `replay_rejected` (line 717) shows
that accepting an advert stamps both coordinates and therefore blocks the
same advert immediately. `same_timestamp_rejected` (line 726) and
`equal_sequence_rejected` (line 734) show that each strict inequality is
necessary: a larger sequence cannot rescue an equal timestamp, and a larger
timestamp cannot rescue an equal sequence.
`acceptance_requires_both` (line 742) records the conjunction.

`rateStep` gates advancement on the signature as well (`rateStep_of_admitted`,
line 763; `rateStep_of_bad_signature`, line 775). `rateFold_replay_rejected`
(line 849) proves that once an advert has advanced the state, replaying it at
any later point in a fold is rejected, using only monotonicity of the fold
(`rateFold_timestamp_mono`, line 827).

### 5.6 Non-vacuity

`nonvacuity_witness` (line 1092) bundles:

* `certAB.Signed verifyAll` — a concrete signed certificate,
* `chainAB.Authenticated verifyAll` — a concrete authenticated chain,
* `chainAB.Acyclic` — the chain is acyclic,
* `RotationLink ckA ckB` — its opaque linkage,
* `¬ certAB.Signed verifyNone` — a concrete rejected certificate.

`concrete_rate_boundaries` (line 1224) supplies a concrete accepted advert plus
three rejected boundaries. `concrete_rejected_cases` (line 1242) supplies the
unsigned certificate and the stale channel signature.

---

## 6. Assumptions and boundaries

* `SigVerifier` is an abstract function. Certificates and resignations are
  "signed" only relative to it. No unforgeability, EUF-CMA, or key-binding
  theorem is added.
* `RotationCertificate.message_eq` ties the stored message to the model
  encoding, but the encoding is not claimed injective. Certificate consumers
  use the payload fields, not message parsing.
* `RotationChain` establishes linkage only. It does not assert that two keys
  belong to one physical node. `RotationChain.Acyclic` is an extra admission
  predicate, not a theorem about all distinct-hop chains.
* `ResignedChannel` models the shape of a re-signed BOLT 7 record. It does not
  compute the double-SHA256 digest or a real secp256k1 signature. The
  `KeyModel` bridge proves only completeness on the declared `correctOn`
  domain.
* `NodeRateState` is a per-key `(timestamp, sequence)` gate. Peer quotas,
  token buckets, gossip-query limits, scheduling, and relay policy are out of
  scope.
* Chain-hash filtering, address parsing, UTXO/channel confirmation, and
  network dissemination remain out of scope.
* The core gossip transition is unchanged. `SignedResignation.admitted` calls
  the existing wave-10 theorem; it does not claim that the core transition
  checks wire membership or re-signing by itself.

---

## 7. Recommended `LN-RT-002` catalog targets

Suggested target list (all proved in this module; exact names can be copied
into the catalog):

1. `RotationCertificate.signed_implies_link`
2. `RotationCertificate.not_signedByNew_of_rejected`
3. `RotationChainLinked.append`
4. `RotationChain.comp_visited`
5. `RotationChain.authenticated_comp`
6. `RotationChain.authenticated_hop_links`
7. `RotationChain.acyclic_singleton`
8. `RotationChain.acyclic_start_not_mem_tail`
9. `hop_distinct_not_imply_acyclic`
10. `distinct_hops_not_acyclic`
11. `opaque_link_not_imply_signed`
12. `opaque_link_not_authenticated`
13. `ResignedChannel.wireMember`
14. `ResignedChannel.not_wireMember_of_unbacked_new`
15. `SignedResignation.signaturesValid`
16. `SignedResignation.admitted`
17. `old_signature_does_not_authenticate_new_keys`
18. `signature_preservation_not_universal`
19. `signedCertificateOfSigner_signed`
20. `NodeRateState.replay_rejected`
21. `NodeRateState.same_timestamp_rejected`
22. `NodeRateState.equal_sequence_rejected`
23. `rateStep_replay_rejected`
24. `rateFold_replay_rejected`
25. `nonvacuity_witness`
26. `concrete_rate_boundaries`
27. `concrete_rejected_cases`

Catalog wording should preserve the negative results: `LN-RT-002` should claim
signed certificate/chain/re-signing/replay *models and conditional theorems*,
not cryptographic identity or unconditional BOLT 7 gossip validation.

---

## 8. Integration notes

* The module is self-contained and builds directly with the command in §2. It
  is **not** added to `LnLean.lean` and no root import was edited, per lane
  ownership rules.
* It imports `LnLean.Crypto.KeyModel` only for the honest-signing bridge; no
  PR-01 hypothesis is re-exported as a theorem.
* It reuses, without weakening:
  * `RotationWitness`, `RotationLink`, `NodeAnnounced`, and `WireMember` from
    `NodeIdentityTargets`;
  * `ChannelAnnellation`, `SigVerifier`, `signatureValid`, and
    `NodeAnnouncement` from `LnLean.Routing.Gossip`;
  * `CanonicalStore`, `NodeCanonicalAdmitted`, and
    `applyGossipNodeCanonical` from the wave-9 node-canonical layer.
* No catalog, traceability, axiom-audit, or docs file was updated. The parent
  should add the root import and the `LN-RT-002` target rows if this lane is
  accepted.
* A repository-wide `scripts/check.py` run currently reports a pre-existing
  duplicate obligation id `LN-L1-003` between
  `Proofs/Security/ReorgTargets.lean` and
  `Proofs/Security/ChainFinalityTargets.lean`. This is unrelated to this lane;
  the owned module itself has zero forbidden tokens and zero `sorry`.
