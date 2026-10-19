/-
# LnLean.Proofs.Routing.NodeIdentityChainTargets

Wave-11 lane `S11-RT-NODE-CHAIN`, open issue `RT-02`.

Wave 10 (`NodeIdentityTargets`) proved that the canonical gossip store cannot
orient a rotation: an antisymmetric store-only relation is impossible between
two co-announced keys, and the positive direction needs an explicit
`RotationWitness` whose evidence is opaque.  That layer deliberately stopped
before a signed rotation certificate, a multi-hop chain, a re-signed channel
announcement, or a replay/rate gate.

This module adds those additive layers above `NodeIdentityTargets`.  It edits
no shared file and imports only the existing routing stack plus the PR-01 key
model.

## Model

* The signed rotation payload is encoded by `rotationMessage`, a tagged byte
  string over the old key, new key, and epoch; the certificate stores both the
  payload fields and that exact signed message.
* `RotationCertificate` carries the old key, new key, epoch, message, signature,
  the distinctness proof, and the proof that the stored message is the payload
  encoding.  `RotationCertificate.Signed` is the abstract verifier predicate.
* `RotationChainLinked` is an inductive transitive-linkage relation over a list
  of certificates.  `RotationChain` packages a start key, the certificates, the
  finish key, and the linkage proof.  `RotationChain.Acyclic` is `Nodup` on the
  visited-key list `[start, newId₁, …]`.
* `ResignedChannel` rewrites the two wire node-key fields of a channel
  announcement, replaces the digest and the four signature fields, and records
  the certificate that authorised the rewrite.  `SignedResignation` adds the
  explicit proof that the rewritten record passes all four verifier checks.
* `NodeRateState` / `NodeAnnouncementAdvert` model the per-node
  timestamp-plus-sequence replay gate.  `rateStep` advances the state only for
  a signature-valid, strictly newer advert.

## Results

* `RotationCertificate.signed_implies_link`: every signed certificate supplies
  the opaque linkage of the wave-10 layer.  The converse fails: with a
  rejecting verifier there is an opaque witness but no signed certificate
  (`opaque_link_not_authenticated`).
* `RotationChain.comp` proves chain composition; `comp_visited` exposes the
  visited keys.  `distinct_hops_not_acyclic` is the acyclicity boundary: every
  certificate in a two-hop cycle has `oldId ≠ newId`, yet the visited list
  repeats the start key.  Acyclicity is therefore an extra admission
  condition, not a consequence of certificate distinctness.
* `resigned_wireMember` requires both the old wire membership and an explicit
  backing for the new key; `rotation_to_unbacked_key_not_wireMember` is the
  matching negative.  `old_signature_does_not_authenticate_new_keys` is the
  concrete stale-signature counterexample: the pre-rotation record verifies,
  the rewrite preserves its key fields, and the old signature is rejected
  under the new key.
* `rateStep_of_admitted`, `rateStep_of_rejected`, `replay_rejected`,
  `same_timestamp_rejected`, and `equal_sequence_rejected` are the rate/replay
  results.  `rateFold_replay_rejected` lifts replay rejection to any later
  point in a fold.
* `nonvacuity_witness` and `concrete_rejected_cases` instantiate a signed
  certificate, a signed chain, a cycle witness, an accepted advert, and a
  rejected stale announcement.

## Boundaries (not claimed)

* `SigVerifier` remains abstract.  A certificate is "signed" only under an
  explicit verifier; no unforgeability or key-binding theorem is added here.
  `RotationCertificate` is evidence supplied out of band, not a store fact.
* `RotationChain` establishes linkage, not physical-node identity.  Distinct
  hops do not exclude cycles; an acyclic chain needs `RotationChain.Acyclic`
  (or an equivalent admission check).
* Re-signing models the *shape* of the new signed record.  It does not compute
  BOLT 7's double-SHA256 digest or a real ECDSA signature.  The honest-signing
  construction from `KeyModel` is included only as a completeness bridge.
* The rate model is a per-key `(timestamp, sequence)` gate.  It does not model
  peer quotas, token buckets, gossip-query rates, or network scheduling.
* Chain-hash filtering, address parsing, UTXO confirmation, and relay policy
  remain outside this module.

No `sorry`, no `axiom`, no `admit`, no `native_decide`, no `unsafe`, no
`@[implemented_by]`.
-/

import LnLean.Proofs.Routing.NodeIdentityTargets
import LnLean.Crypto.KeyModel

namespace LnLean.Proofs.Routing.NodeIdentityChainTargets

open LnLean
open LnLean.Routing
open LnLean.Routing.GossipProps
open LnLean.Crypto
open LnLean.Proofs.Routing.GossipCanonicalTargets
open LnLean.Proofs.Routing.GossipRawRefinementTargets
open LnLean.Proofs.Routing.NodeCanonicalTargets
open LnLean.Proofs.Routing.NodeIdentityTargets
open Classical

set_option autoImplicit false

/-! ## 1. Signed rotation payloads and certificates -/

/-- Domain-separation tag for a rotation message.  This is a model tag, not a
claim about the BOLT 7 wire encoding. -/
def rotationTag : ByteArray := ByteArray.mk #[0x52, 0x54, 0x01]

/-- The one-byte epoch stamp used by the model message.  The model deliberately
does not claim that this encoding is injective on all epochs; the certificate
also stores the payload fields, and every consumer uses those fields. -/
def epochByte (e : Nat) : ByteArray := ByteArray.mk #[e.toUInt8]

/-- The signed message of a rotation: tag, old key bytes, new key bytes, epoch
byte.  The message is opaque to the verifier, as in BOLT 7. -/
def rotationMessage (oldId newId : PubKey) (epoch : Nat) : ByteArray :=
  rotationTag ++ oldId.bytes ++ newId.bytes ++ epochByte epoch

/-- A signed rotation certificate.  It carries the old key, the new key, the
epoch, the exact signed message, the signature bytes, and the proof that a
rotation relates two different keys. -/
structure RotationCertificate where
  /-- The old wire `node_id`. -/
  oldId : PubKey
  /-- The new wire `node_id`. -/
  newId : PubKey
  /-- The rotation epoch/sequence number. -/
  epoch : Nat
  /-- The exact byte string signed by `oldId`. -/
  message : ByteArray
  /-- The signature bytes. -/
  signature : GossipSignature
  /-- A rotation relates two different keys. -/
  distinct : oldId ≠ newId
  /-- The stored message is the payload encoding. -/
  message_eq : message = rotationMessage oldId newId epoch

namespace RotationCertificate

/-- The abstract verifier accepts this certificate under signer `k`. -/
def SignedBy (verify : SigVerifier) (c : RotationCertificate)
    (k : PubKey) : Prop :=
  signatureValid verify k c.message c.signature

/-- The certificate is signed by its old key. -/
def Signed (verify : SigVerifier) (c : RotationCertificate) : Prop :=
  c.SignedBy verify c.oldId

/-- The signed certificate is not a signature by the new key.  This is a
definitional predicate, not a theorem: whether it fails is verifier-specific. -/
def SignedByNew (verify : SigVerifier) (c : RotationCertificate) : Prop :=
  c.SignedBy verify c.newId

/-- The certificate determines the wave-10 opaque witness.  The signed message
is the evidence; the verifier is not consulted. -/
def toWitness (c : RotationCertificate) : RotationWitness :=
  { oldId := c.oldId
    newId := c.newId
    evidence := c.message
    distinct := c.distinct }

@[simp] theorem toWitness_oldId (c : RotationCertificate) :
    c.toWitness.oldId = c.oldId := rfl

@[simp] theorem toWitness_newId (c : RotationCertificate) :
    c.toWitness.newId = c.newId := rfl

/-- A certificate's witness links its old and new keys. -/
theorem toWitness_links (c : RotationCertificate) :
    c.toWitness.Links c.oldId c.newId :=
  ⟨rfl, rfl⟩

/-- Every certificate yields the wave-10 opaque linkage. -/
theorem signed_implies_link (verify : SigVerifier) (c : RotationCertificate)
    (_h : c.Signed verify) : RotationLink c.oldId c.newId :=
  ⟨c.toWitness, rfl, rfl⟩

/-- A signature by the old key is not automatically a signature by the new
key.  The hypothesis is the exact failing check. -/
theorem not_signedByNew_of_rejected {verify : SigVerifier}
    {c : RotationCertificate}
    (h : verify c.newId c.message c.signature = false) :
    ¬ c.SignedByNew verify := by
  intro hs
  unfold SignedByNew RotationCertificate.SignedBy at hs
  have htrue : verify c.newId c.message c.signature = true := hs
  rw [h] at htrue
  exact Bool.noConfusion htrue

/-- Message equality exposed without reduction. -/
theorem message_eq_rotationMessage (c : RotationCertificate) :
    c.message = rotationMessage c.oldId c.newId c.epoch :=
  c.message_eq

/-- The certificate's witness rewrites exactly the recorded old key. -/
theorem toWitness_mapKey_old (c : RotationCertificate) :
    c.toWitness.mapKey c.oldId = c.newId := by
  simp [RotationWitness.mapKey, toWitness]

/-- The certificate's witness leaves other keys unchanged. -/
theorem toWitness_mapKey_of_ne (c : RotationCertificate) {k : PubKey}
    (h : k ≠ c.oldId) : c.toWitness.mapKey k = k := by
  simp [toWitness, RotationWitness.mapKey, h]

end RotationCertificate

/-! ## 2. Transitive rotation chains -/

/-- Transitive linkage of a certificate list from `start` to `finish`. -/
inductive RotationChainLinked : PubKey → List RotationCertificate → PubKey → Prop where
  /-- The empty chain links a key to itself. -/
  | nil (k : PubKey) : RotationChainLinked k [] k
  /-- Prepend a certificate whose old key matches the current start. -/
  | cons {a : PubKey} (c : RotationCertificate)
      {cs : List RotationCertificate} {b : PubKey}
      (hfrom : c.oldId = a)
      (rest : RotationChainLinked c.newId cs b) :
      RotationChainLinked a (c :: cs) b

namespace RotationChainLinked

/-- An empty linked list has equal endpoints. -/
theorem finish_eq_of_nil {a b : PubKey}
    (h : RotationChainLinked a [] b) : a = b := by
  cases h
  rfl

/-- **Chain composition.**  Appending two linked certificate lists preserves
transitive linkage. -/
theorem append {a b c : PubKey} {xs ys : List RotationCertificate}
    (hx : RotationChainLinked a xs b)
    (hy : RotationChainLinked b ys c) :
    RotationChainLinked a (xs ++ ys) c := by
  induction hx generalizing c with
  | nil k => exact hy
  | cons cert hfrom rest ih =>
      exact RotationChainLinked.cons cert hfrom (ih hy)

/-- A singleton list is linked from the certificate's old key to its new key. -/
theorem singleton (c : RotationCertificate) :
    RotationChainLinked c.oldId [c] c.newId :=
  RotationChainLinked.cons c rfl (RotationChainLinked.nil c.newId)

/-- A two-certificate chain composes definitionally. -/
theorem pair (c d : RotationCertificate) (h : c.newId = d.oldId) :
    RotationChainLinked c.oldId [c, d] d.newId :=
  RotationChainLinked.cons c rfl
    (RotationChainLinked.cons d h.symm (RotationChainLinked.nil d.newId))

end RotationChainLinked

/-- A rotation chain: start key, certificates, finish key, and the transitive
linkage proof. -/
structure RotationChain where
  /-- First key in the chain. -/
  start : PubKey
  /-- Certificates in order. -/
  certs : List RotationCertificate
  /-- Last key in the chain. -/
  finish : PubKey
  /-- Transitive linkage of the certificate list. -/
  linked : RotationChainLinked start certs finish

namespace RotationChain

/-- The empty chain at one key. -/
def nil (k : PubKey) : RotationChain :=
  ⟨k, [], k, RotationChainLinked.nil k⟩

/-- The one-certificate chain. -/
def singleton (c : RotationCertificate) : RotationChain :=
  ⟨c.oldId, [c], c.newId, RotationChainLinked.singleton c⟩

/-- **Composition of chains.**  The second chain must start where the first
finishes; the result concatenates the certificate lists. -/
def comp (x y : RotationChain) (h : x.finish = y.start) : RotationChain :=
  { start := x.start
    certs := x.certs ++ y.certs
    finish := y.finish
    linked := by
      have hy' : RotationChainLinked x.finish y.certs y.finish := h ▸ y.linked
      exact RotationChainLinked.append x.linked hy' }

@[simp] theorem nil_start (k : PubKey) : (nil k).start = k := rfl

@[simp] theorem nil_finish (k : PubKey) : (nil k).finish = k := rfl

@[simp] theorem nil_certs (k : PubKey) : (nil k).certs = [] := rfl

@[simp] theorem singleton_start (c : RotationCertificate) :
    (singleton c).start = c.oldId := rfl

@[simp] theorem singleton_finish (c : RotationCertificate) :
    (singleton c).finish = c.newId := rfl

@[simp] theorem singleton_certs (c : RotationCertificate) :
    (singleton c).certs = [c] := rfl

@[simp] theorem comp_start (x y : RotationChain) (h : x.finish = y.start) :
    (comp x y h).start = x.start := rfl

@[simp] theorem comp_finish (x y : RotationChain) (h : x.finish = y.start) :
    (comp x y h).finish = y.finish := rfl

@[simp] theorem comp_certs (x y : RotationChain) (h : x.finish = y.start) :
    (comp x y h).certs = x.certs ++ y.certs := rfl

/-- The keys visited by a chain, in order. -/
def visited (c : RotationChain) : List PubKey :=
  c.start :: c.certs.map RotationCertificate.newId

/-- A chain is acyclic when its visited-key list has no duplicate. -/
def Acyclic (c : RotationChain) : Prop :=
  c.visited.Nodup

@[simp] theorem visited_nil (k : PubKey) : (nil k).visited = [k] := rfl

@[simp] theorem visited_singleton (c : RotationCertificate) :
    (singleton c).visited = [c.oldId, c.newId] := rfl

/-- The visited keys of a composite chain expose both segments. -/
theorem comp_visited (x y : RotationChain) (h : x.finish = y.start) :
    (comp x y h).visited =
      x.start :: (x.certs.map RotationCertificate.newId ++
        y.certs.map RotationCertificate.newId) := by
  simp [visited, comp, List.map_append]

/-- The empty chain is acyclic. -/
theorem acyclic_nil (k : PubKey) : (nil k).Acyclic := by
  simp [Acyclic, visited]

/-- A singleton chain is acyclic exactly because the certificate is between
distinct keys. -/
theorem acyclic_singleton (c : RotationCertificate) :
    (singleton c).Acyclic := by
  unfold Acyclic visited singleton
  rw [List.map_cons, List.map_nil, List.nodup_cons]
  refine ⟨?_, by simp⟩
  intro hmem
  rcases List.mem_singleton.mp hmem with hEq
  exact c.distinct hEq

/-- An acyclic chain has no duplicate visited key. -/
theorem acyclic_no_revisit {c : RotationChain} (h : c.Acyclic) :
    c.visited.Nodup := h

/-- In an acyclic chain the start key does not occur in any later position.
This is the direct consequence of `Nodup` used by the admission layer. -/
theorem acyclic_start_not_mem_tail {c : RotationChain} (h : c.Acyclic) :
    c.start ∉ c.certs.map RotationCertificate.newId := by
  unfold Acyclic visited at h
  exact (List.nodup_cons.mp h).1

/-- Authenticated chains: every certificate passes the abstract verifier. -/
def Authenticated (verify : SigVerifier) (c : RotationChain) : Prop :=
  ∀ cert ∈ c.certs, cert.Signed verify

/-- The empty chain is authenticated by any verifier. -/
theorem authenticated_nil (verify : SigVerifier) (k : PubKey) :
    (nil k).Authenticated verify := by
  intro cert hcert
  simp [nil] at hcert

/-- A singleton chain is authenticated iff its certificate is signed. -/
theorem authenticated_singleton_iff (verify : SigVerifier)
    (c : RotationCertificate) :
    (singleton c).Authenticated verify ↔ c.Signed verify := by
  constructor
  · intro h
    exact h c (by simp [singleton])
  · intro h cert hcert
    simp [singleton] at hcert
    subst hcert
    exact h

/-- Chain composition preserves authentication. -/
theorem authenticated_comp (verify : SigVerifier) {x y : RotationChain}
    {h : x.finish = y.start}
    (hx : x.Authenticated verify) (hy : y.Authenticated verify) :
    (comp x y h).Authenticated verify := by
  intro cert hcert
  rw [comp_certs] at hcert
  rcases List.mem_append.mp hcert with hxmem | hymem
  · exact hx cert hxmem
  · exact hy cert hymem

/-- Every hop of an authenticated chain supplies an opaque linkage. -/
theorem authenticated_hop_links (verify : SigVerifier) {c : RotationChain}
    (hauth : c.Authenticated verify) {cert : RotationCertificate}
    (hmem : cert ∈ c.certs) :
    RotationLink cert.oldId cert.newId :=
  cert.signed_implies_link verify (hauth cert hmem)

end RotationChain

/-! ## 3. Distinctness and acyclicity boundaries -/

/-- A chain of two distinct hops can revisit the start key.  This is the exact
acyclicity boundary: `RotationCertificate.distinct` only says that each
*literal hop* changes keys. -/
theorem chain_cycle_linked {a b : PubKey} (c d : RotationCertificate)
    (hc : c.oldId = a) (hcn : c.newId = b)
    (hd : d.oldId = b) (hdn : d.newId = a) :
    RotationChainLinked a [c, d] a := by
  have hd' : d.oldId = c.newId := by rw [hd, ← hcn]
  have hchain : RotationChainLinked a [c, d] d.newId :=
    RotationChainLinked.cons c hc
      (RotationChainLinked.cons d hd' (RotationChainLinked.nil d.newId))
  rwa [hdn] at hchain

/-! ## 4. Re-signing a channel announcement after rotation -/

/-- A channel announcement rewritten under a certificate, with new digest and
four supplied signature fields.  The two wire node keys are the only key fields
that move; funding/Bitcoin keys are left untouched, as in the wave-10 witness
layer. -/
structure ResignedChannel where
  /-- The pre-rotation announcement. -/
  base : ChannelAnnellation
  /-- The certificate authorising the key rewrite. -/
  rotation : RotationCertificate
  /-- The digest of the rewritten announcement. -/
  digest : ByteArray
  /-- First node signature. -/
  nodeSignature1 : GossipSignature
  /-- Second node signature. -/
  nodeSignature2 : GossipSignature
  /-- First Bitcoin-key signature. -/
  bitcoinSignature1 : GossipSignature
  /-- Second Bitcoin-key signature. -/
  bitcoinSignature2 : GossipSignature

namespace ResignedChannel

/-- The signed rewritten announcement.  The rewrite and the replacement
signatures are explicit structure fields; nothing is inferred from the store. -/
noncomputable def toAnnouncement (r : ResignedChannel) : ChannelAnnellation :=
  { r.base with
    nodeKey1 := r.rotation.toWitness.mapKey r.base.nodeKey1
    nodeKey2 := r.rotation.toWitness.mapKey r.base.nodeKey2
    digest := r.digest
    nodeSignature1 := r.nodeSignature1
    nodeSignature2 := r.nodeSignature2
    bitcoinSignature1 := r.bitcoinSignature1
    bitcoinSignature2 := r.bitcoinSignature2 }

@[simp] theorem toAnnouncement_shortChannelId (r : ResignedChannel) :
    r.toAnnouncement.shortChannelId = r.base.shortChannelId := rfl

@[simp] theorem toAnnouncement_node1 (r : ResignedChannel) :
    r.toAnnouncement.node1 = r.base.node1 := rfl

@[simp] theorem toAnnouncement_node2 (r : ResignedChannel) :
    r.toAnnouncement.node2 = r.base.node2 := rfl

@[simp] theorem toAnnouncement_capacitySat (r : ResignedChannel) :
    r.toAnnouncement.capacitySat = r.base.capacitySat := rfl

@[simp] theorem toAnnouncement_nodeKey1 (r : ResignedChannel) :
    r.toAnnouncement.nodeKey1 =
      r.rotation.toWitness.mapKey r.base.nodeKey1 := rfl

@[simp] theorem toAnnouncement_nodeKey2 (r : ResignedChannel) :
    r.toAnnouncement.nodeKey2 =
      r.rotation.toWitness.mapKey r.base.nodeKey2 := rfl

@[simp] theorem toAnnouncement_digest (r : ResignedChannel) :
    r.toAnnouncement.digest = r.digest := rfl

/-- The rewrite preserves the channel identity, graph endpoints, and capacity.
Only the wire keys, digest, and signatures may differ. -/
theorem preserves_identity (r : ResignedChannel) :
    r.toAnnouncement.shortChannelId = r.base.shortChannelId ∧
      r.toAnnouncement.node1 = r.base.node1 ∧
      r.toAnnouncement.node2 = r.base.node2 ∧
      r.toAnnouncement.capacitySat = r.base.capacitySat :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **Positive wire membership under an explicit new-key backing.**  The old
announcement must already be a wire member and the new key must be announced.
The rewrite alone is not enough, and the certificate alone is not a store
fact. -/
theorem wireMember {s : GossipState} (r : ResignedChannel)
    (hbase : WireMember s r.base)
    (hnew : NodeAnnounced s r.rotation.newId) :
    WireMember s r.toAnnouncement := by
  rcases hbase with ⟨h1, h2⟩
  constructor
  · show NodeAnnounced s (r.rotation.toWitness.mapKey r.base.nodeKey1)
    unfold RotationWitness.mapKey
    split
    · exact hnew
    · exact h1
  · show NodeAnnounced s (r.rotation.toWitness.mapKey r.base.nodeKey2)
    unfold RotationWitness.mapKey
    split
    · exact hnew
    · exact h2

/-- **Negative wire-membership boundary.**  If the rewrite moves an endpoint
to the new key and that key is not backed by a node announcement, the rewritten
channel is not a wire member.  This is the "explicit rewrite" half of the
requirement: membership does not follow from the certificate. -/
theorem not_wireMember_of_unbacked_new {s : GossipState} (r : ResignedChannel)
    (hnot : ¬ NodeAnnounced s r.rotation.newId)
    (hmove : r.rotation.toWitness.mapKey r.base.nodeKey1 = r.rotation.newId) :
    ¬ WireMember s r.toAnnouncement := by
  intro hm
  exact hnot (by
    simpa [toAnnouncement, hmove] using hm.first)

/-- Graph-level identity is preserved by the rewrite. -/
theorem graph_endpoints_preserved (r : ResignedChannel) :
    r.toAnnouncement.node1 = r.base.node1 ∧
      r.toAnnouncement.node2 = r.base.node2 :=
  ⟨rfl, rfl⟩

end ResignedChannel

/-- A re-signed channel with an explicit proof that the rewritten record passes
all four verifier checks. -/
structure SignedResignation (verify : SigVerifier) where
  /-- The rewritten record and its certificate. -/
  resigned : ResignedChannel
  /-- The explicit four-way signature check on the rewritten record. -/
  signed : resigned.toAnnouncement.signaturesValid verify

namespace SignedResignation

/-- The signed record verifies. -/
theorem signaturesValid {verify : SigVerifier} (r : SignedResignation verify) :
    r.resigned.toAnnouncement.signaturesValid verify :=
  r.signed

/-- A signed resignation preserves wire membership under an explicit new-key
backing. -/
theorem wireMember {verify : SigVerifier} {s : GossipState}
    (r : SignedResignation verify) (hbase : WireMember s r.resigned.base)
    (hnew : NodeAnnounced s r.resigned.rotation.newId) :
    WireMember s r.resigned.toAnnouncement :=
  r.resigned.wireMember hbase hnew

/-- The signed resignation passes the existing canonical-channel gate when the
two remaining structural gates are supplied.  This is the exact interface to
the wave-10 admission theorem; it does not claim the core transition enforces
anything by itself. -/
theorem admitted {verify : SigVerifier} {cs : CanonicalStore}
    (r : SignedResignation verify) (hinv : NodeCanonicalAdmitted verify cs)
    (hmem : WireMemberCertified verify cs.gossip r.resigned.toAnnouncement)
    (hne : r.resigned.toAnnouncement.node1 ≠ r.resigned.toAnnouncement.node2)
    (hcompat : cs.gossip.CompatibleWithStore r.resigned.toAnnouncement)
    (hauth : UpdatesAuthorizedBy cs.gossip r.resigned.toAnnouncement) :
    NodeCanonicalAdmitted verify
        (applyGossipNodeCanonical verify cs
          (.channelAnnouncement r.resigned.toAnnouncement)) ∧
      r.resigned.toAnnouncement ∈
        (applyGossipNodeCanonical verify cs
          (.channelAnnouncement r.resigned.toAnnouncement)).gossip.announcements ∧
      WireMemberCertified verify
        (applyGossipNodeCanonical verify cs
          (.channelAnnouncement r.resigned.toAnnouncement)).gossip
        r.resigned.toAnnouncement :=
  channelAnnouncement_admitted_of_wireMember verify cs
    r.resigned.toAnnouncement hinv hmem
    ⟨r.signed, hne, hcompat, hauth⟩

end SignedResignation

/-! ## 5. Honest re-signing via the PR-01 key model -/

/-- The verifier induced by a `PrimitiveModel` on gossip signature bytes. -/
def keyModelVerifier (M : PrimitiveModel) : SigVerifier :=
  fun k msg sig => M.ecdsaVerify k msg ⟨sig.bytes⟩

/-- A certificate produced by an honest `KeyModel` signer.  The signer's
generated public key is required to be the certificate's old key, and the
message must lie in the model's declared signing domain. -/
noncomputable def signedCertificateOfSigner {M : PrimitiveModel}
    (K : KeyModel M) (seed : ByteArray) (newId : PubKey) (epoch : Nat)
    (hne : K.publicOfSeed seed ≠ newId)
    (_hcorrect : K.correctOn (rotationMessage (K.publicOfSeed seed) newId epoch)) :
    RotationCertificate :=
  { oldId := K.publicOfSeed seed
    newId := newId
    epoch := epoch
    message := rotationMessage (K.publicOfSeed seed) newId epoch
    signature := ⟨(K.sign (K.secretOfSeed seed)
      (rotationMessage (K.publicOfSeed seed) newId epoch)).bytes⟩
    distinct := hne
    message_eq := rfl }

/-- The honest certificate verifies under the key model's ECDSA verifier. -/
theorem signedCertificateOfSigner_signed {M : PrimitiveModel}
    (K : KeyModel M) (seed : ByteArray) (newId : PubKey) (epoch : Nat)
    (hne : K.publicOfSeed seed ≠ newId)
    (hcorrect : K.correctOn (rotationMessage (K.publicOfSeed seed) newId epoch)) :
    (signedCertificateOfSigner K seed newId epoch hne hcorrect).Signed
      (keyModelVerifier M) := by
  unfold RotationCertificate.Signed RotationCertificate.SignedBy
    signedCertificateOfSigner keyModelVerifier signatureValid
  simpa using K.verifies_seed seed hcorrect

/-! ## 6. Node-announcement rate limits and replay -/

/-- A replayable node-announcement advert: the announcement plus the model's
sequence number.  BOLT 7's timestamp is carried by the announcement itself; the
extra sequence makes the equal-timestamp boundary explicit. -/
structure NodeAnnouncementAdvert where
  /-- The announced record. -/
  announcement : NodeAnnouncement
  /-- The per-node sequence number. -/
  sequence : Nat

namespace NodeAnnouncementAdvert

/-- The wire node key of the advert. -/
def nodeId (a : NodeAnnouncementAdvert) : PubKey :=
  a.announcement.nodeId

/-- The advertised BOLT 7 timestamp. -/
def timestamp (a : NodeAnnouncementAdvert) : Timestamp :=
  a.announcement.timestamp

@[simp] theorem nodeId_mk (n : NodeAnnouncement) (s : Nat) :
    (⟨n, s⟩ : NodeAnnouncementAdvert).nodeId = n.nodeId := rfl

@[simp] theorem timestamp_mk (n : NodeAnnouncement) (s : Nat) :
    (⟨n, s⟩ : NodeAnnouncementAdvert).timestamp = n.timestamp := rfl

end NodeAnnouncementAdvert

/-- Per-node rate/replay state: the last accepted timestamp and sequence. -/
structure NodeRateState where
  /-- Last accepted timestamp per node key. -/
  lastTimestamp : PubKey → Timestamp
  /-- Last accepted sequence per node key. -/
  lastSequence : PubKey → Nat

namespace NodeRateState

/-- The gate accepts an advert only when both coordinates are strictly newer
than the last accepted values for that node key. -/
def Accepts (st : NodeRateState) (a : NodeAnnouncementAdvert) : Prop :=
  st.lastTimestamp a.nodeId < a.timestamp ∧
    st.lastSequence a.nodeId < a.sequence

/-- Advance the per-node clock after an accepted advert. -/
noncomputable def accept (st : NodeRateState) (a : NodeAnnouncementAdvert) :
    NodeRateState :=
  { lastTimestamp := fun k =>
      if k = a.nodeId then a.timestamp else st.lastTimestamp k
    lastSequence := fun k =>
      if k = a.nodeId then a.sequence else st.lastSequence k }

/-- Exact unfolding of the gate. -/
theorem accepts_iff (st : NodeRateState) (a : NodeAnnouncementAdvert) :
    st.Accepts a ↔
      st.lastTimestamp a.nodeId < a.timestamp ∧
        st.lastSequence a.nodeId < a.sequence :=
  Iff.rfl

/-- Acceptance implies a strictly newer timestamp. -/
theorem accepted_timestamp_lt {st : NodeRateState} {a : NodeAnnouncementAdvert}
    (h : st.Accepts a) : st.lastTimestamp a.nodeId < a.timestamp :=
  h.1

/-- Acceptance implies a strictly newer sequence. -/
theorem accepted_sequence_lt {st : NodeRateState} {a : NodeAnnouncementAdvert}
    (h : st.Accepts a) : st.lastSequence a.nodeId < a.sequence :=
  h.2

/-- The accepted advert stamps its own timestamp. -/
@[simp] theorem accept_self_timestamp (st : NodeRateState)
    (a : NodeAnnouncementAdvert) :
    (st.accept a).lastTimestamp a.nodeId = a.timestamp := by
  simp [accept]

/-- The accepted advert stamps its own sequence. -/
@[simp] theorem accept_self_sequence (st : NodeRateState)
    (a : NodeAnnouncementAdvert) :
    (st.accept a).lastSequence a.nodeId = a.sequence := by
  simp [accept]

/-- Acceptance is independent for a different node key. -/
theorem accept_other_timestamp {st : NodeRateState}
    {a : NodeAnnouncementAdvert} {k : PubKey} (h : k ≠ a.nodeId) :
    (st.accept a).lastTimestamp k = st.lastTimestamp k := by
  simp [accept, h]

/-- Sequence acceptance is independent for a different node key. -/
theorem accept_other_sequence {st : NodeRateState}
    {a : NodeAnnouncementAdvert} {k : PubKey} (h : k ≠ a.nodeId) :
    (st.accept a).lastSequence k = st.lastSequence k := by
  simp [accept, h]

/-- An accepted advert is timestamp-monotone at every key. -/
theorem timestamp_mono_accept (st : NodeRateState)
    (a : NodeAnnouncementAdvert) (h : st.Accepts a) (k : PubKey) :
    st.lastTimestamp k ≤ (st.accept a).lastTimestamp k := by
  by_cases hk : k = a.nodeId
  · subst hk
    rw [accept_self_timestamp]
    exact Nat.le_of_lt h.1
  · rw [accept_other_timestamp hk]
    exact Nat.le_refl _

/-- An accepted advert is sequence-monotone at every key. -/
theorem sequence_mono_accept (st : NodeRateState)
    (a : NodeAnnouncementAdvert) (h : st.Accepts a) (k : PubKey) :
    st.lastSequence k ≤ (st.accept a).lastSequence k := by
  by_cases hk : k = a.nodeId
  · subst hk
    rw [accept_self_sequence]
    exact Nat.le_of_lt h.2
  · rw [accept_other_sequence hk]
    exact Nat.le_refl _

/-- **Replay rejection.**  After accepting `a`, the same advert is rejected.
Both coordinates are stamped to the advert's values, so the required strict
inequalities fail. -/
theorem replay_rejected (st : NodeRateState) (a : NodeAnnouncementAdvert) :
    ¬ (st.accept a).Accepts a := by
  intro h
  have hts := h.1
  rw [accept_self_timestamp] at hts
  exact Nat.lt_irrefl _ hts

/-- **Same-timestamp boundary.**  An advert whose timestamp is not strictly
newer is rejected even if its sequence is larger. -/
theorem same_timestamp_rejected {st : NodeRateState}
    {a : NodeAnnouncementAdvert} (h : a.timestamp ≤ st.lastTimestamp a.nodeId) :
    ¬ st.Accepts a := by
  intro ha
  exact Nat.not_lt_of_le h ha.1

/-- **Equal-sequence boundary.**  An advert whose sequence is not strictly
newer is rejected even if its timestamp is larger. -/
theorem equal_sequence_rejected {st : NodeRateState}
    {a : NodeAnnouncementAdvert} (h : a.sequence ≤ st.lastSequence a.nodeId) :
    ¬ st.Accepts a := by
  intro ha
  exact Nat.not_lt_of_le h ha.2

/-- The two gates are necessary: dropping either coordinate admits a replay or
a same-timestamp update.  This is the combined boundary statement. -/
theorem acceptance_requires_both (st : NodeRateState)
    (a : NodeAnnouncementAdvert) :
    st.Accepts a →
      st.lastTimestamp a.nodeId < a.timestamp ∧
        st.lastSequence a.nodeId < a.sequence :=
  fun h => h

end NodeRateState

/-- A gate that requires both a valid signature and the rate condition. -/
def RateAdmitted (verify : SigVerifier) (st : NodeRateState)
    (a : NodeAnnouncementAdvert) : Prop :=
  a.announcement.signatureValid verify ∧ st.Accepts a

/-- One rate step.  A rejected advert leaves the state unchanged; an admitted
advert advances the per-node clocks. -/
noncomputable def rateStep (verify : SigVerifier) (st : NodeRateState)
    (a : NodeAnnouncementAdvert) : NodeRateState :=
  if RateAdmitted verify st a then st.accept a else st

/-- An admitted advert advances the state. -/
theorem rateStep_of_admitted {verify : SigVerifier} {st : NodeRateState}
    {a : NodeAnnouncementAdvert} (h : RateAdmitted verify st a) :
    rateStep verify st a = st.accept a := by
  simp [rateStep, h]

/-- A rejected advert leaves the state unchanged. -/
theorem rateStep_of_rejected {verify : SigVerifier} {st : NodeRateState}
    {a : NodeAnnouncementAdvert} (h : ¬ RateAdmitted verify st a) :
    rateStep verify st a = st := by
  simp [rateStep, h]

/-- A bad signature leaves the state unchanged. -/
theorem rateStep_of_bad_signature {verify : SigVerifier} {st : NodeRateState}
    {a : NodeAnnouncementAdvert}
    (h : ¬ a.announcement.signatureValid verify) :
    rateStep verify st a = st := by
  apply rateStep_of_rejected
  intro hr
  exact h hr.1

/-- An admitted step is timestamp-monotone. -/
theorem rateStep_timestamp_mono {verify : SigVerifier} {st : NodeRateState}
    (a : NodeAnnouncementAdvert) (k : PubKey) :
    st.lastTimestamp k ≤ (rateStep verify st a).lastTimestamp k := by
  by_cases h : RateAdmitted verify st a
  · rw [rateStep_of_admitted h]
    exact NodeRateState.timestamp_mono_accept st a h.2 k
  · rw [rateStep_of_rejected h]
    exact Nat.le_refl _

/-- An admitted step is sequence-monotone. -/
theorem rateStep_sequence_mono {verify : SigVerifier} {st : NodeRateState}
    (a : NodeAnnouncementAdvert) (k : PubKey) :
    st.lastSequence k ≤ (rateStep verify st a).lastSequence k := by
  by_cases h : RateAdmitted verify st a
  · rw [rateStep_of_admitted h]
    exact NodeRateState.sequence_mono_accept st a h.2 k
  · rw [rateStep_of_rejected h]
    exact Nat.le_refl _

/-- A valid advert accepted in one step is rejected by any later step of the
same advert.  This is the state-level replay theorem for the signed gate. -/
theorem rateStep_replay_rejected {verify : SigVerifier} {st : NodeRateState}
    {a : NodeAnnouncementAdvert} (h : RateAdmitted verify st a) :
    ¬ RateAdmitted verify (rateStep verify st a) a := by
  rw [rateStep_of_admitted h]
  intro hr
  exact NodeRateState.replay_rejected st a hr.2

/-- Fold a list of adverts through the signed rate gate. -/
noncomputable def rateFold (verify : SigVerifier) (st : NodeRateState) :
    List NodeAnnouncementAdvert → NodeRateState
  | [] => st
  | a :: as => rateFold verify (rateStep verify st a) as

@[simp] theorem rateFold_nil (verify : SigVerifier) (st : NodeRateState) :
    rateFold verify st [] = st := rfl

@[simp] theorem rateFold_cons (verify : SigVerifier) (st : NodeRateState)
    (a : NodeAnnouncementAdvert) (as : List NodeAnnouncementAdvert) :
    rateFold verify st (a :: as) = rateFold verify (rateStep verify st a) as :=
  rfl

/-- A fold never decreases a node's timestamp. -/
theorem rateFold_timestamp_mono (verify : SigVerifier) (st : NodeRateState)
    (as : List NodeAnnouncementAdvert) (k : PubKey) :
    st.lastTimestamp k ≤ (rateFold verify st as).lastTimestamp k := by
  induction as generalizing st with
  | nil => exact Nat.le_refl _
  | cons a as ih =>
      rw [rateFold_cons]
      exact Nat.le_trans (rateStep_timestamp_mono a k) (ih (rateStep verify st a))

/-- A fold never decreases a node's sequence. -/
theorem rateFold_sequence_mono (verify : SigVerifier) (st : NodeRateState)
    (as : List NodeAnnouncementAdvert) (k : PubKey) :
    st.lastSequence k ≤ (rateFold verify st as).lastSequence k := by
  induction as generalizing st with
  | nil => exact Nat.le_refl _
  | cons a as ih =>
      rw [rateFold_cons]
      exact Nat.le_trans (rateStep_sequence_mono a k) (ih (rateStep verify st a))

/-- **Replay rejection at any later point in a fold.**  Once an advert has
advanced the state, replaying it later (with the same node, timestamp, and
sequence) can never be admitted. -/
theorem rateFold_replay_rejected (verify : SigVerifier) (st : NodeRateState)
    (a : NodeAnnouncementAdvert) (as : List NodeAnnouncementAdvert)
    (h : RateAdmitted verify st a) :
    ¬ RateAdmitted verify (rateFold verify (rateStep verify st a) as) a := by
  intro hr
  have hstep_ts : a.timestamp ≤
      (rateStep verify st a).lastTimestamp a.nodeId := by
    rw [rateStep_of_admitted h, NodeRateState.accept_self_timestamp]
    exact Nat.le_refl _
  have hfold_ts :=
    rateFold_timestamp_mono verify (rateStep verify st a) as a.nodeId
  have hts' : a.timestamp ≤
      (rateFold verify (rateStep verify st a) as).lastTimestamp a.nodeId :=
    Nat.le_trans hstep_ts hfold_ts
  exact NodeRateState.same_timestamp_rejected hts' hr.2

/-! ## 7. Concrete witnesses -/

private def ckA : PubKey := ⟨ByteArray.mk #[1]⟩

private def ckB : PubKey := ⟨ByteArray.empty⟩

private def ckC : PubKey := ⟨ByteArray.mk #[2, 3]⟩

private theorem ckA_ne_ckB : ckA ≠ ckB := by
  intro h
  have hs := congrArg (fun k : PubKey => k.bytes.size) h
  have h1 : ckA.bytes.size = 1 := by decide
  have h2 : ckB.bytes.size = 0 := rfl
  rw [h1, h2] at hs
  omega

private theorem ckB_ne_ckA : ckB ≠ ckA := ckA_ne_ckB.symm

private theorem ckA_ne_ckC : ckA ≠ ckC := by
  intro h
  have hs := congrArg (fun k : PubKey => k.bytes.size) h
  have h1 : ckA.bytes.size = 1 := by decide
  have h2 : ckC.bytes.size = 2 := by decide
  rw [h1, h2] at hs
  omega

private theorem ckC_ne_ckA : ckC ≠ ckA := ckA_ne_ckC.symm

private theorem ckB_ne_ckC : ckB ≠ ckC := by
  intro h
  have hs := congrArg (fun k : PubKey => k.bytes.size) h
  have h1 : ckB.bytes.size = 0 := rfl
  have h2 : ckC.bytes.size = 2 := by decide
  rw [h1, h2] at hs
  omega

private def verifyAll : SigVerifier := fun _ _ _ => true

private def verifyNone : SigVerifier := fun _ _ _ => false

private noncomputable def verifyNotC : SigVerifier :=
  fun k _ _ => decide (k ≠ ckC)

private theorem verifyAll_ckA (d : ByteArray) (s : GossipSignature) :
    verifyAll ckA d s = true := rfl

private theorem verifyAll_ckB (d : ByteArray) (s : GossipSignature) :
    verifyAll ckB d s = true := rfl

private theorem verifyNone_false (k : PubKey) (d : ByteArray)
    (s : GossipSignature) : verifyNone k d s = false := rfl

private theorem verifyNotC_ckA (d : ByteArray) (s : GossipSignature) :
    verifyNotC ckA d s = true := by
  simp [verifyNotC, ckA_ne_ckC]

private theorem verifyNotC_ckB (d : ByteArray) (s : GossipSignature) :
    verifyNotC ckB d s = true := by
  simp [verifyNotC, ckB_ne_ckC]

private theorem verifyNotC_ckC (d : ByteArray) (s : GossipSignature) :
    verifyNotC ckC d s = false := by
  simp [verifyNotC]

private def cnA : NodeId := ⟨0⟩

private def cnB : NodeId := ⟨1⟩

private def cscid : ShortChannelId := ⟨1, 2, 3⟩

private def cemptySig : GossipSignature := ⟨ByteArray.empty⟩

private theorem cnA_ne_cnB : cnA ≠ cnB := by decide

private def cmkAnn (scid : ShortChannelId) (u v : NodeId)
    (ka kb : PubKey) (cap : Nat) : ChannelAnnellation :=
  { shortChannelId := scid
    node1 := u
    node2 := v
    nodeKey1 := ka
    nodeKey2 := kb
    bitcoinKey1 := ka
    bitcoinKey2 := kb
    capacitySat := cap
    digest := ByteArray.empty
    nodeSignature1 := cemptySig
    nodeSignature2 := cemptySig
    bitcoinSignature1 := cemptySig
    bitcoinSignature2 := cemptySig }

private def cmkNode (k : PubKey) (ts : Nat) (alias : ByteArray) :
    NodeAnnouncement :=
  { nodeId := k
    timestamp := ts
    rgbColor := ByteArray.empty
    alias := alias
    addresses := []
    digest := ByteArray.empty
    signature := cemptySig }

private def cannAB : ChannelAnnellation :=
  cmkAnn cscid cnA cnB ckA ckB 1000

private def cnA1 : NodeAnnouncement := cmkNode ckA 10 (ByteArray.mk #[1])

private def cnB1 : NodeAnnouncement := cmkNode ckB 15 (ByteArray.mk #[2])

private def certAB : RotationCertificate :=
  { oldId := ckA
    newId := ckB
    epoch := 0
    message := rotationMessage ckA ckB 0
    signature := cemptySig
    distinct := ckA_ne_ckB
    message_eq := rfl }

private def certBA : RotationCertificate :=
  { oldId := ckB
    newId := ckA
    epoch := 1
    message := rotationMessage ckB ckA 1
    signature := cemptySig
    distinct := ckB_ne_ckA
    message_eq := rfl }

private def certAC : RotationCertificate :=
  { oldId := ckA
    newId := ckC
    epoch := 2
    message := rotationMessage ckA ckC 2
    signature := cemptySig
    distinct := ckA_ne_ckC
    message_eq := rfl }

private theorem certAB_signed_verifyAll : certAB.Signed verifyAll := by
  simp [RotationCertificate.Signed, RotationCertificate.SignedBy,
    signatureValid, verifyAll]

private theorem certAB_not_signed_verifyNone :
    ¬ certAB.Signed verifyNone := by
  simp [RotationCertificate.Signed, RotationCertificate.SignedBy,
    signatureValid, verifyNone]

private theorem certBA_signed_verifyAll : certBA.Signed verifyAll := by
  simp [RotationCertificate.Signed, RotationCertificate.SignedBy,
    signatureValid, verifyAll]

private theorem certAC_signed_verifyNotC : certAC.Signed verifyNotC := by
  simp [RotationCertificate.Signed, RotationCertificate.SignedBy,
    signatureValid, verifyNotC_ckA, certAC]

private theorem certAC_not_signedByNew_verifyNotC :
    ¬ certAC.SignedByNew verifyNotC := by
  unfold RotationCertificate.SignedByNew
  unfold RotationCertificate.SignedBy
  simp [signatureValid, verifyNotC_ckC, certAC]

private def chainAB : RotationChain := RotationChain.singleton certAB

private def chainBA : RotationChain := RotationChain.singleton certBA

private def chainCycle : RotationChain :=
  RotationChain.comp chainAB chainBA rfl

private theorem chainAB_acyclic : chainAB.Acyclic :=
  RotationChain.acyclic_singleton certAB

private theorem chainAB_authenticated : chainAB.Authenticated verifyAll :=
  (RotationChain.authenticated_singleton_iff verifyAll certAB).mpr
    certAB_signed_verifyAll

private theorem chainCycle_certs : chainCycle.certs = [certAB, certBA] := rfl

private theorem chainCycle_visited : chainCycle.visited = [ckA, ckB, ckA] := by
  simp [chainCycle, RotationChain.visited, chainAB, chainBA,
    certAB, certBA, RotationChain.singleton]

private theorem chainCycle_not_acyclic : ¬ chainCycle.Acyclic := by
  unfold RotationChain.Acyclic
  rw [chainCycle_visited]
  intro h
  have hnot : ckA ∉ [ckB, ckA] := (List.nodup_cons.mp h).1
  exact hnot (List.mem_cons_of_mem _ (List.mem_cons_self ..))

private theorem chainCycle_hops_distinct :
    ∀ c ∈ chainCycle.certs, c.oldId ≠ c.newId := by
  intro c hc
  rw [chainCycle_certs] at hc
  rcases List.mem_cons.mp hc with rfl | hc
  · exact ckA_ne_ckB
  · rw [List.mem_singleton] at hc
    subst hc
    exact ckB_ne_ckA

private def staleResign : ResignedChannel :=
  { base := cannAB
    rotation := certAC
    digest := cannAB.digest
    nodeSignature1 := cannAB.nodeSignature1
    nodeSignature2 := cannAB.nodeSignature2
    bitcoinSignature1 := cannAB.bitcoinSignature1
    bitcoinSignature2 := cannAB.bitcoinSignature2 }

private theorem cannAB_signaturesValid_verifyNotC :
    cannAB.signaturesValid verifyNotC := by
  simp [ChannelAnnellation.signaturesValid, signatureValid, verifyNotC_ckA,
    verifyNotC_ckB, cannAB, cmkAnn]

private theorem staleResign_not_signaturesValid :
    ¬ staleResign.toAnnouncement.signaturesValid verifyNotC := by
  intro h
  have h1 := h.1
  have hk : staleResign.toAnnouncement.nodeKey1 = ckC := by
    simp [staleResign, ResignedChannel.toAnnouncement, certAC,
      RotationCertificate.toWitness, RotationWitness.mapKey, cannAB, cmkAnn]
  rw [hk] at h1
  simp [signatureValid, verifyNotC] at h1

private theorem staleResign_first_key :
    staleResign.toAnnouncement.nodeKey1 = staleResign.rotation.newId := by
  simp [staleResign, ResignedChannel.toAnnouncement, certAC,
    RotationCertificate.toWitness, RotationWitness.mapKey, cannAB, cmkAnn]

/-- **Non-vacuity: a signed certificate, a signed chain, and a rejected one.**
The same concrete data shows the positive and negative sides: `certAB` verifies
under `verifyAll`, `chainAB` is authenticated and acyclic, while `verifyNone`
rejects the certificate. -/
theorem nonvacuity_witness :
    certAB.Signed verifyAll ∧
      chainAB.Authenticated verifyAll ∧
        chainAB.Acyclic ∧
          RotationLink ckA ckB ∧
            ¬ certAB.Signed verifyNone :=
  ⟨certAB_signed_verifyAll, chainAB_authenticated, chainAB_acyclic,
    certAB.signed_implies_link verifyAll certAB_signed_verifyAll,
    certAB_not_signed_verifyNone⟩

/-- **Opaque evidence is weaker than a signed certificate.**  With a rejecting
verifier there is an explicit rotation witness (hence a `RotationLink`) but no
signed certificate for that link.  This is the exact sense in which the wave-10
witness is weaker: it carries bytes, not authentication. -/
theorem opaque_link_not_authenticated :
    ∃ w : RotationWitness,
      RotationLink w.oldId w.newId ∧
        ¬ ∃ c : RotationCertificate,
          c.oldId = w.oldId ∧ c.newId = w.newId ∧ c.Signed verifyNone := by
  refine ⟨certAB.toWitness, certAB.signed_implies_link verifyAll
    certAB_signed_verifyAll, ?_⟩
  · rintro ⟨c, hc1, hc2, hs⟩
    -- Every `Signed verifyNone` certificate is impossible by definition.
    simp [RotationCertificate.Signed, RotationCertificate.SignedBy,
      signatureValid, verifyNone] at hs

/-- **Distinct hops do not imply acyclicity.**  Each certificate in the cycle
is between different keys, but the visited list repeats `ckA`. -/
theorem distinct_hops_not_acyclic :
    (∀ c ∈ chainCycle.certs, c.oldId ≠ c.newId) ∧
      ¬ chainCycle.Acyclic :=
  ⟨chainCycle_hops_distinct, chainCycle_not_acyclic⟩

/-- **Exact obstruction: hop distinctness is not a chain acyclicity invariant.**
No predicate that only checks `oldId ≠ newId` on each certificate can imply
`RotationChain.Acyclic`; the two-hop cycle is a counterexample. -/
theorem hop_distinct_not_imply_acyclic :
    ¬ (∀ c : RotationChain,
        (∀ cert ∈ c.certs, cert.oldId ≠ cert.newId) → c.Acyclic) := by
  intro h
  exact distinct_hops_not_acyclic.2
    (h chainCycle distinct_hops_not_acyclic.1)

/-- The concrete two-hop cycle is linked and returns to its start. -/
theorem concrete_cycle_linked :
    RotationChainLinked ckA [certAB, certBA] ckA ∧
      chainCycle.finish = chainCycle.start :=
  ⟨RotationChainLinked.pair certAB certBA rfl, rfl⟩

/-- The concrete stale-signature counterexample.  `cannAB` verifies before the
rewrite, the rewritten first wire key is the certificate's new key `ckC`, and
the old signature is rejected under `ckC`. -/
theorem old_signature_does_not_authenticate_new_keys :
    ∃ (verify : SigVerifier) (r : ResignedChannel),
      r.base.signaturesValid verify ∧
        r.toAnnouncement.nodeKey1 = r.rotation.newId ∧
          ¬ r.toAnnouncement.signaturesValid verify :=
  ⟨verifyNotC, staleResign, cannAB_signaturesValid_verifyNotC,
    staleResign_first_key, staleResign_not_signaturesValid⟩

/-- **Exact obstruction: signatures are not a rewrite invariant.**  No theorem
of the form "a valid pre-rotation record stays valid after the key rewrite"
can hold for all verifiers and rewrites; the stale-signature witness refutes the
universal form.  The strongest true statement is the conditional
`SignedResignation` layer, which requires the fresh four-way check. -/
theorem signature_preservation_not_universal :
    ¬ (∀ (verify : SigVerifier) (r : ResignedChannel),
        r.base.signaturesValid verify →
          r.toAnnouncement.signaturesValid verify) := by
  intro h
  exact staleResign_not_signaturesValid
    (h verifyNotC staleResign cannAB_signaturesValid_verifyNotC)

/-- **Exact obstruction: opaque evidence does not imply authentication.**  No
function that only consumes an opaque `RotationWitness` can manufacture a
certificate signed under a rejecting verifier. -/
theorem opaque_link_not_imply_signed :
    ¬ (∀ w : RotationWitness, RotationLink w.oldId w.newId →
        ∃ c : RotationCertificate,
          c.oldId = w.oldId ∧ c.newId = w.newId ∧ c.Signed verifyNone) := by
  intro h
  rcases h certAB.toWitness
      (certAB.signed_implies_link verifyAll certAB_signed_verifyAll) with
    ⟨c, _hcOld, _hcNew, hs⟩
  simp [RotationCertificate.Signed, RotationCertificate.SignedBy,
    signatureValid, verifyNone] at hs

/-- The concrete rewritten channel still preserves identity and graph
endpoints, so the failure is exactly the signature/key mismatch. -/
theorem stale_resign_preserves_identity :
    staleResign.toAnnouncement.shortChannelId = cannAB.shortChannelId ∧
      staleResign.toAnnouncement.node1 = cannAB.node1 ∧
      staleResign.toAnnouncement.node2 = cannAB.node2 ∧
      staleResign.toAnnouncement.capacitySat = cannAB.capacitySat :=
  staleResign.preserves_identity

/-- Concrete rate state: everything starts at zero. -/
private def rate0 : NodeRateState :=
  { lastTimestamp := fun _ => 0, lastSequence := fun _ => 0 }

private def advA : NodeAnnouncementAdvert :=
  { announcement := cnA1, sequence := 1 }

private def advA_later : NodeAnnouncementAdvert :=
  { announcement := cnA1, sequence := 2 }

private def advA_sameSeq : NodeAnnouncementAdvert :=
  { announcement := cmkNode ckA 11 (ByteArray.mk #[1]), sequence := 1 }

private theorem advA_accepted : rate0.Accepts advA := by
  simp [NodeRateState.Accepts, rate0, advA, cnA1, cmkNode, NodeAnnouncementAdvert.nodeId,
    NodeAnnouncementAdvert.timestamp]

private theorem advA_replay_rejected :
    ¬ (rate0.accept advA).Accepts advA :=
  NodeRateState.replay_rejected rate0 advA

private theorem advA_same_timestamp_rejected :
    ¬ (rate0.accept advA).Accepts advA_later := by
  apply NodeRateState.same_timestamp_rejected
  simp [NodeRateState.accept, advA_later, advA, cnA1, cmkNode,
    NodeAnnouncementAdvert.nodeId, NodeAnnouncementAdvert.timestamp]

private theorem advA_equal_sequence_rejected :
    ¬ (rate0.accept advA).Accepts advA_sameSeq := by
  apply NodeRateState.equal_sequence_rejected
  simp [NodeRateState.accept, advA_sameSeq, advA, cnA1, cmkNode,
    NodeAnnouncementAdvert.nodeId, NodeAnnouncementAdvert.timestamp]

/-- **Concrete rate/replay boundary witnesses.**  The fresh advert is accepted;
the same advert replayed, a later timestamp with the same sequence, and an
equal timestamp with a later sequence are all rejected. -/
theorem concrete_rate_boundaries :
    rate0.Accepts advA ∧
      ¬ (rate0.accept advA).Accepts advA ∧
        ¬ (rate0.accept advA).Accepts advA_later ∧
          ¬ (rate0.accept advA).Accepts advA_sameSeq :=
  ⟨advA_accepted, advA_replay_rejected, advA_same_timestamp_rejected,
    advA_equal_sequence_rejected⟩

/-- The concrete signed gate accepts the fresh advert and then rejects its
replay. -/
theorem concrete_rateStep_replay :
    RateAdmitted verifyAll rate0 advA ∧
      ¬ RateAdmitted verifyAll (rateStep verifyAll rate0 advA) advA := by
  refine ⟨⟨by rfl, advA_accepted⟩, ?_⟩
  exact rateStep_replay_rejected ⟨by rfl, advA_accepted⟩

/-- The concrete rejected cases: an unsigned certificate and a stale channel
signature. -/
theorem concrete_rejected_cases :
    (¬ certAB.Signed verifyNone) ∧
      (∃ (verify : SigVerifier) (r : ResignedChannel),
        r.base.signaturesValid verify ∧
          ¬ r.toAnnouncement.signaturesValid verify) :=
  ⟨certAB_not_signed_verifyNone,
    ⟨verifyNotC, staleResign, cannAB_signaturesValid_verifyNotC,
      staleResign_not_signaturesValid⟩⟩

end LnLean.Proofs.Routing.NodeIdentityChainTargets
