/-
# A mechanized non-vacuity audit for the core catalog structures

**English claim.**  This module does *not* prove that the Lightning protocol is
inhabited, and it does not prove that every catalog theorem has a non-vacuous
instance.  It audits a precise, finite list of core structures and predicates
used by the catalog and records a constructive witness for each audited item.
Where the current interface is intentionally vacuous, the module proves the
emptiness or the absence of an accepting witness instead of inventing one.

The audit has four parts.

1. **Positive witnesses.**  Explicit values inhabit `Commitment`,
   `CommitmentTx`, `GossipState`, `OpenChannel`, `CoverageWitness`,
   `RotationWitness`, `HandshakeState`, `PrimitiveModel`, `KeyModel`,
   `AcceptChannel`, and the predicate `StoredAccept`.  The basic validity
   predicates (`ChannelId.Valid`, `PubKey.Valid`, `PaymentHash.Valid`,
   `GossipSignature.Valid`), the canonical positive digest domains
   (`Canonical33`, `CanonicalDigest32`), and a non-vacuous signature interface
   (`EufCma` plus an accepted input) are also witnessed.
2. **Vacuity results.**  The concrete `withVendorEcdsa` model is a legitimate
   `PrimitiveModel`, but under its own C3 hypothesis its verifier is the
   constant-`false` function.  `withVendorEcdsa_accepts_nothing` and
   `withVendorEcdsa_funding_uninhabited` record that the model value exists
   while its funding/verification relation has no witness.  Independently,
   `DigestBindsMod` has no witness for any tag, and `Canonical33 nBytes33` is
   false.  `BridgedFundingWitness` is a structure that cannot be inhabited at
   all under the vendor bridge: any such value would contradict
   `bridged_model_totalReject`.
3. **Negative and boundary witnesses.**  A concrete one-signature
   `CommitmentSigned` wire has no `CoverageWitness` that decodes to `some []`;
   the empty gossip store announces no key; and the canonical-domain repair
   excludes exactly the bad `nBytes33` suffix.
4. **A registry.**  `witnessRegistry` is a list of records, each carrying the
   actual proposition and its proof.  `witnessRegistry_sound` proves every
   registered proposition, and `witnessRegistry_ids_nodup` proves the audited
   ids are distinct.

**Scope warning.**  These witnesses are *existence* results at the model
interface.  They do not imply that a catalog theorem is non-vacuous merely
because its carrier type is inhabited.  `witness_not_universal` states the
separation explicitly: a `Commitment` exists, while `DigestBindsMod` has no
witness for any tag.  The registry records exactly the audited items, not the
whole catalog.

**Not modelled.**  secp256k1 arithmetic, real key generation, hash
preimages/collisions, an execution engine, or a protocol run.  The concrete
`PrimitiveModel` below is a total, structurally lawful model chosen to make
the signature interface non-vacuous; it is not a cryptographic implementation.
-/

import LnLean.Basic.Core
import LnLean.Channel.Types
import LnLean.Channel.Commitment
import LnLean.Routing.Gossip
import LnLean.Protocol.Handshake
import LnLean.Crypto.Model
import LnLean.Crypto.KeyModel
import LnLean.Crypto.Sig
import LnLean.Proofs.Crypto.EcdsaProps
import LnLean.Proofs.Crypto.KeyModelTargets
import LnLean.Proofs.Routing.NodeIdentityTargets
import LnLean.Proofs.Channel.CoverageWitnessTargets
import LnLean.Proofs.Bitcoin.EcdsaBridgeTargets
import LnLean.Proofs.Bitcoin.EcdsaConcreteTargets
import LnLean.Proofs.Bitcoin.EcdsaDomainTargets

namespace LnLean.Proofs.Model.NonVacuityTargets

set_option autoImplicit false
set_option maxHeartbeats 1000000

open LnLean
open LnLean.Channel
open LnLean.Protocol
open LnLean.Crypto
open LnLean.Routing
open LnLean.Proofs.Crypto.KeyModelTargets
open LnLean.Proofs.Routing.NodeIdentityTargets
open LnLean.Proofs.Channel.CoverageWitnessTargets
open LnLean.Proofs.Bitcoin.EcdsaBridgeTargets
open LnLean.Proofs.Bitcoin.EcdsaConcreteTargets
open LnLean.Proofs.Bitcoin.EcdsaDomainTargets

/-! ## 0. Two concrete public keys -/

/-- The empty public-key byte string, used as the "old" audit key. -/
def key0 : PubKey := ⟨ByteArray.empty⟩

/-- The one-byte public key `0x01`, used as the "new" audit key. -/
def key1 : PubKey := ⟨ByteArray.mk #[0x01]⟩

/-! ## 1. A concrete, non-vacuous primitive model -/

/-- The audit hash is the identity on 32-byte inputs and the all-zero 32-byte
string elsewhere.  It has the required output width and is collision resistant
on the 32-byte domain, which is the exact C1 shape used by the model. -/
def auditHash (b : ByteArray) : ByteArray :=
  if b.size = 32 then b else zeros 32

/-- `auditHash` always returns 32 bytes. -/
theorem auditHash_size (b : ByteArray) : (auditHash b).size = 32 := by
  unfold auditHash
  split
  · assumption
  · exact zeros_size 32

/-- `auditHash` is collision resistant on 32-byte inputs. -/
theorem auditHash_collisionResistant : CollisionResistant auditHash := by
  intro x y hx hy h
  unfold auditHash at h
  rw [if_pos hx, if_pos hy] at h
  exact h

/-- The signature interface used by the audit model: it accepts exactly the
empty message, under every key and every signature.  This is a total `Bool`
function, not a cryptographic verifier. -/
def auditEcdsaVerify (_pk : PubKey) (msg : ByteArray) (_sig : EcdsaSig) : Bool :=
  decide (msg = ByteArray.empty)

/-- The audit verifier satisfies C3 (`EufCma`) *non-vacuously*: two accepted
messages must both be the empty message. -/
theorem auditEcdsa_eufCma : EufCma auditEcdsaVerify := by
  intro _pk m₁ m₂ _sig h₁ h₂
  have h₁' : m₁ = ByteArray.empty := of_decide_eq_true h₁
  have h₂' : m₂ = ByteArray.empty := of_decide_eq_true h₂
  rw [h₁', h₂']

/-- The Schnorr half of the audit verifier: the same message-bound decision as
`auditEcdsaVerify`, at the `SchnorrSig` type. -/
def auditSchnorrVerify (_pk : PubKey) (msg : ByteArray) (_sig : SchnorrSig) : Bool :=
  decide (msg = ByteArray.empty)

/-- The audit Schnorr verifier satisfies C3 non-vacuously. -/
theorem auditSchnorr_eufCma : EufCma auditSchnorrVerify := by
  intro _pk m₁ m₂ _sig h₁ h₂
  have h₁' : m₁ = ByteArray.empty := of_decide_eq_true h₁
  have h₂' : m₂ = ByteArray.empty := of_decide_eq_true h₂
  rw [h₁', h₂']

/-- A complete `PrimitiveModel` with a non-vacuous ECDSA interface.  The other
primitives are trivial total functions; the structural width and AEAD laws are
proved, not assumed as extra hypotheses. -/
def auditModel : PrimitiveModel where
  sha256 := auditHash
  hash160 := fun _ => zeros 20
  ecdsaVerify := auditEcdsaVerify
  schnorrVerify := auditSchnorrVerify
  ecdh := fun _ _ => zeros 32
  hkdf := fun _ _ _ => zeros 32
  aeadSeal := fun _ _ plaintext => plaintext
  aeadOpen := fun _ _ ciphertext => some ciphertext
  hmacSha256 := fun _ _ => zeros 32
  sha256_size := auditHash_size
  hash160_size := fun _ => zeros_size 20
  hmac_size := fun _ _ => zeros_size 32
  sha256_collisionResistant := auditHash_collisionResistant
  ecdsa_eufCma := auditEcdsa_eufCma
  schnorr_eufCma := auditSchnorr_eufCma
  aead_indCca := by
    refine ⟨?_, ?_⟩
    · intro _k _n _p
      rfl
    · intro _k _n c p h
      exact (Option.some.inj h).symm

/-- The audit model accepts the empty message. -/
theorem auditModel_accepts_empty :
    auditModel.ecdsaVerify ⟨ByteArray.empty⟩ ByteArray.empty
      ⟨ByteArray.empty⟩ = true := by
  simp [auditModel, auditEcdsaVerify]

/-- The audit model rejects every non-empty message. -/
theorem auditModel_rejects_nonempty {msg : ByteArray}
    (h : msg ≠ ByteArray.empty) :
    auditModel.ecdsaVerify ⟨ByteArray.empty⟩ msg ⟨ByteArray.empty⟩ = false := by
  simp [auditModel, auditEcdsaVerify, h]

/-- Replacing a model's verifier by the constant-`false` function preserves
the `PrimitiveModel` structure.  The resulting C3 field is vacuous. -/
def vacuousEcdsaModel (M : PrimitiveModel) : PrimitiveModel :=
  { M with
    ecdsaVerify := fun _ _ _ => false
    ecdsa_eufCma := by
      intro _pk _m₁ _m₂ _sig h₁ _h₂
      exact absurd h₁ (by simp) }

/-- The vacuous model still satisfies the C3 field. -/
theorem vacuousEcdsaModel_eufCma (M : PrimitiveModel) :
    EufCma (vacuousEcdsaModel M).ecdsaVerify :=
  (vacuousEcdsaModel M).ecdsa_eufCma

/-- The vacuous model accepts no input at all. -/
theorem vacuousEcdsaModel_accepts_nothing (M : PrimitiveModel) :
    ¬ ∃ (pk : PubKey) (msg : ByteArray) (sig : EcdsaSig),
      (vacuousEcdsaModel M).ecdsaVerify pk msg sig = true := by
  rintro ⟨pk, msg, sig, h⟩
  have hf : (vacuousEcdsaModel M).ecdsaVerify pk msg sig = false := rfl
  rw [hf] at h
  exact Bool.false_ne_true h

/-! ## 2. Positive witnesses for core structures -/

/-- A small, conserved commitment record: `600 + 300 + 100 = 1000`. -/
def commitmentWitness : Commitment :=
  { holder := .local
    commitmentNumber := 0
    fundingValueSat := 1000
    toLocalSat := 600
    toRemoteSat := 300
    htlcs := []
    feeSat := 100
    contestDelay := 144
    anchorOutputs := false }

/-- An explicit `Commitment` witness with the value equation. -/
theorem commitment_witness :
    ∃ c : Commitment,
      c.fundingValueSat = 1000 ∧ c.toLocalSat = 600 ∧
        c.toRemoteSat = 300 ∧ c.feeSat = 100 ∧
        c.toLocalSat + c.toRemoteSat + c.feeSat = c.fundingValueSat :=
  ⟨commitmentWitness, rfl, rfl, rfl, rfl, by decide⟩

instance commitmentInhabited : Inhabited Commitment :=
  ⟨commitmentWitness⟩

/-- A commitment transaction over the witness commitment, with explicit
script fields and the identity HTLC-script function. -/
def commitmentTxWitness : CommitmentTx :=
  { commitment := commitmentWitness
    dustLimitSat := 0
    toLocalScript := ⟨[0x51]⟩
    toRemoteScript := ⟨[0x52]⟩
    localAnchorScript := ⟨[0x53]⟩
    remoteAnchorScript := ⟨[0x54]⟩
    htlcScript := fun _ => ⟨[0x55]⟩ }

/-- An explicit `CommitmentTx` witness. -/
theorem commitmentTx_witness :
    ∃ tx : CommitmentTx,
      tx.commitment = commitmentWitness ∧ tx.dustLimitSat = 0 ∧
        tx.toLocalOutput.isSome = true := by
  refine ⟨commitmentTxWitness, rfl, rfl, ?_⟩
  simp [commitmentTxWitness, CommitmentTx.toLocalOutput, commitmentWitness]

instance commitmentTxInhabited : Inhabited CommitmentTx :=
  ⟨commitmentTxWitness⟩

/-- The empty gossip store: no announcements, no updates, no node records. -/
def gossipStateWitness : GossipState :=
  { announcements := [], updates := [], nodeAnnouncements := [] }

/-- An explicit `GossipState` witness, with the zero replacement clock. -/
theorem gossipState_witness :
    ∃ s : GossipState,
      s.announcements = [] ∧ s.updates = [] ∧
        s.nodeAnnouncements = [] ∧ s.latestUpdateTimestamp = 0 :=
  ⟨gossipStateWitness, rfl, rfl, rfl, rfl⟩

instance gossipStateInhabited : Inhabited GossipState :=
  ⟨gossipStateWitness⟩

/-- A concrete node announcement for the first audit key. -/
def gossipNodeAnnouncement : NodeAnnouncement :=
  { nodeId := key0
    timestamp := 1
    rgbColor := ByteArray.empty
    alias := ByteArray.empty
    addresses := []
    digest := zeros 32
    signature := ⟨zeros 64⟩ }

/-- A gossip store containing exactly one node announcement. -/
def gossipStateNode : GossipState :=
  { announcements := [], updates := [],
    nodeAnnouncements := [gossipNodeAnnouncement] }

/-- The node-announcement predicate `NodeAnnounced` is non-vacuous on a
concrete store. -/
theorem gossipState_nodeAnnounced : NodeAnnounced gossipStateNode key0 := by
  refine ⟨gossipNodeAnnouncement, ?_, rfl⟩
  simp [gossipStateNode]

/-- The empty store has no announcement for `key0`, which is the boundary
case for the same predicate. -/
theorem gossipStateWitness_not_nodeAnnounced :
    ¬ NodeAnnounced gossipStateWitness key0 := by
  rintro ⟨n, hn, _hkey⟩
  simpa [gossipStateWitness] using hn

/-- A concrete `open_channel` payload. -/
def openChannelWitness : OpenChannel :=
  { temporaryChannelId := ChannelId.zero
    fundingSatoshis := 1000
    pushMsat := ⟨0⟩
    fundingPubKey := key0 }

/-- An explicit `OpenChannel` witness. -/
theorem openChannel_witness :
    ∃ o : OpenChannel,
      o.fundingSatoshis = 1000 ∧ o.pushMsat = ⟨0⟩ ∧
        o.fundingPubKey = key0 :=
  ⟨openChannelWitness, rfl, rfl, rfl⟩

instance openChannelInhabited : Inhabited OpenChannel :=
  ⟨openChannelWitness⟩

/-- One concrete signed HTLC row, used to make the coverage witness
non-empty. -/
def coverageEntry : SignedHtlcEntry :=
  { htlcId := 1
    amount := ⟨1000⟩
    paymentHash := ⟨zeros 32⟩
    direction := .local
    htlcState := .offered
    cltvExpiry := 100
    signedDataDigest := zeros 32
    signature := ⟨zeros 64⟩ }

/-- A non-empty coverage witness. -/
def coverageWitnessWitness : CoverageWitness :=
  { entries := [coverageEntry] }

/-- An explicit `CoverageWitness` witness with one row. -/
theorem coverageWitness_witness :
    ∃ w : CoverageWitness, w.entries.length = 1 :=
  ⟨coverageWitnessWitness, rfl⟩

instance coverageWitnessInhabited : Inhabited CoverageWitness :=
  ⟨coverageWitnessWitness⟩

/-- The empty and one-byte keys are distinct. -/
theorem key0_ne_key1 : key0 ≠ key1 := by
  intro h
  have hs := congrArg (fun k : PubKey => k.bytes.size) h
  have h0 : key0.bytes.size = 0 := rfl
  have h1 : key1.bytes.size = 1 := by decide
  rw [h0, h1] at hs
  omega

/-- An explicit old-to-new rotation witness. -/
def rotationWitnessWitness : RotationWitness :=
  { oldId := key0
    newId := key1
    evidence := zeros 8
    distinct := key0_ne_key1 }

/-- An explicit `RotationWitness` witness and its linkage. -/
theorem rotationWitness_witness :
    ∃ w : RotationWitness,
      w.oldId = key0 ∧ w.newId = key1 ∧ w.Links key0 key1 :=
  ⟨rotationWitnessWitness, rfl, rfl, rfl, rfl⟩

instance rotationWitnessInhabited : Inhabited RotationWitness :=
  ⟨rotationWitnessWitness⟩

/-- An explicit `HandshakeState` witness: the initial state is reachable and
not ready. -/
theorem handshakeState_witness :
    ∃ s : HandshakeState, Reachable s ∧ s.ready = false :=
  ⟨HandshakeState.initial, Reachable.initial, rfl⟩

instance handshakeStateInhabited : Inhabited HandshakeState :=
  ⟨HandshakeState.initial⟩

/-- An explicit `PrimitiveModel` witness with a non-vacuous ECDSA interface. -/
theorem primitiveModel_witness :
    ∃ M : PrimitiveModel,
      EufCma M.ecdsaVerify ∧
        (∃ (pk : PubKey) (msg : ByteArray) (sig : EcdsaSig),
          M.ecdsaVerify pk msg sig = true) :=
  ⟨auditModel, auditModel.ecdsa_eufCma,
    ⟨⟨ByteArray.empty⟩, ByteArray.empty, ⟨ByteArray.empty⟩,
      auditModel_accepts_empty⟩⟩

instance primitiveModelInhabited : Inhabited PrimitiveModel :=
  ⟨auditModel⟩

/-- The funding message used by the pinned key-model witnesses. -/
def pinnedMessage : ByteArray := fundingTag ++ ByteArray.empty

/-- An explicit `KeyModel` witness with a generated owned pair. -/
theorem keyModel_witness :
    ∃ (M : PrimitiveModel) (K : KeyModel M) (seed : ByteArray),
      K.Owns (K.publicOfSeed seed) (K.secretOfSeed seed) :=
  ⟨pinnedModel auditModel key0 pinnedMessage,
    pinnedKeyModel auditModel key0 pinnedMessage, ByteArray.empty,
    LnLean.Crypto.KeyModel.owns_generated
      (pinnedKeyModel auditModel key0 pinnedMessage) ByteArray.empty⟩

/-- An explicit `AcceptChannel` witness advertising `key0`. -/
theorem acceptChannel_witness :
    ∃ m : AcceptChannel, m.fundingPubKey = key0 :=
  ⟨acceptChannelWithFundingKey key0, rfl⟩

/-- The handshake state that records the audit `accept_channel` payload. -/
def storedAcceptState : HandshakeState :=
  { HandshakeState.initial with
    acceptChannel? := some (acceptChannelWithFundingKey key0)
    acceptReceived := true }

/-- An explicit `StoredAccept` witness: the state records the payload, the
payload advertises the generated key, and the milestone is set. -/
theorem storedAccept_witness :
    ∃ (M : PrimitiveModel) (K : KeyModel M) (seed : ByteArray)
      (s : HandshakeState) (m : AcceptChannel),
      StoredAccept K seed s m ∧ s.acceptReceived = true := by
  refine ⟨pinnedModel auditModel key0 pinnedMessage,
    pinnedKeyModel auditModel key0 pinnedMessage, ByteArray.empty,
    storedAcceptState, acceptChannelWithFundingKey key0, ?_, rfl⟩
  constructor
  · rfl
  · rfl

/-! ## 3. Positive witnesses for validity predicates and domains -/

/-- The zero channel id is valid. -/
theorem channelId_valid_witness : ∃ c : ChannelId, c.Valid :=
  ⟨ChannelId.zero, ChannelId.zero_valid⟩

/-- A 33-byte public key is valid. -/
theorem pubKey_valid_witness : ∃ p : PubKey, p.Valid :=
  ⟨⟨zeros 33⟩, zeros_size 33⟩

/-- A 32-byte payment hash is valid. -/
theorem paymentHash_valid_witness : ∃ h : PaymentHash, h.Valid :=
  ⟨⟨zeros 32⟩, zeros_size 32⟩

/-- A 64-byte gossip signature is valid. -/
theorem gossipSignature_valid_witness :
    ∃ s : GossipSignature, s.Valid :=
  ⟨⟨zeros 64⟩, zeros_size 64⟩

/-- The canonical 33-byte positive domain is inhabited. -/
theorem canonical33_witness : ∃ m : ByteArray, Canonical33 m :=
  ⟨zeros 33, canonical33_zeros⟩

/-- The canonical 32-byte digest domain is inhabited. -/
theorem canonical32_witness :
    ∃ m : ByteArray, CanonicalDigest32 m :=
  ⟨zeros 32, canonical32_zeros⟩

/-- The canonical domain gives a positive `DigestBindsModOn` witness: every
tag binds on the value-reduced 33-byte domain. -/
theorem canonicalDomain_binds :
    DigestBindsModOn Canonical33 fundingTag :=
  digestBindsModOn_canonical33 fundingTag

/-- The `EufCma` interface itself has a non-vacuous witness: the audit
verifier is C3 and accepts at least one input. -/
theorem eufCma_nonvacuous_witness :
    ∃ v : PubKey → ByteArray → EcdsaSig → Bool,
      EufCma v ∧
        (∃ (pk : PubKey) (msg : ByteArray) (sig : EcdsaSig),
          v pk msg sig = true) :=
  ⟨auditModel.ecdsaVerify, auditModel.ecdsa_eufCma,
    ⟨⟨ByteArray.empty⟩, ByteArray.empty, ⟨ByteArray.empty⟩,
      auditModel_accepts_empty⟩⟩

/-! ## 4. Negative and boundary witnesses -/

/-- A legacy `commitment_signed` record with one HTLC signature. -/
def oneSigWire : CommitmentSigned :=
  { channelId := ChannelId.zero
    signature := ⟨zeros 64⟩
    htlcSignatures := [⟨zeros 64⟩] }

/-- No coverage witness decodes the one-signature wire to the empty output
list: the wire count forces one row, and one row produces one output. -/
theorem oneSigWire_no_empty_decode :
    ¬ ∃ w : CoverageWitness, decodeCoverage oneSigWire w = some [] := by
  rintro ⟨w, hw⟩
  unfold decodeCoverage at hw
  by_cases hlen : oneSigWire.htlcSignatures.length = w.entries.length
  · rw [if_pos hlen] at hw
    have hmap : w.entries.map SignedHtlcEntry.toCommitmentHtlcOutput = [] :=
      Option.some.inj hw
    have hzero : w.entries.length = 0 := by
      have := congrArg List.length hmap
      simpa using this
    have hone : oneSigWire.htlcSignatures.length = 1 := rfl
    rw [hone] at hlen
    omega
  · rw [if_neg hlen] at hw
    cases hw

/-- The funding-tag digest predicate has no witness. -/
theorem fundingTag_digestBindsMod_empty :
    ¬ DigestBindsMod fundingTag :=
  not_digestBindsMod_fundingTag

/-- No tag whatsoever satisfies `DigestBindsMod` on the untyped interface. -/
theorem digestBindsMod_uninhabited :
    ¬ ∃ tag : ByteArray, DigestBindsMod tag :=
  no_digestBindsMod_anywhere

/-- The canonical-domain repair excludes exactly the bad `nBytes33` suffix. -/
theorem nBytes33_not_canonical : ¬ Canonical33 nBytes33 :=
  not_canonical33_nBytes33

/-- A structure that cannot be inhabited under the vendor bridge: a bridged
model has a total-rejecting verifier, so no checked funding witness exists. -/
structure BridgedFundingWitness where
  model : PrimitiveModel
  bridge : VendorEcdsaBridge model
  key : PubKey
  tx : ByteArray
  sig : EcdsaSig
  checked : verifyFundingChecked model key tx sig = true

/-- `BridgedFundingWitness` is empty. -/
theorem bridgedFundingWitness_uninhabited :
    ¬ Nonempty BridgedFundingWitness := by
  rintro ⟨w⟩
  have hf : w.model.ecdsaVerify w.key (fundingTag ++ w.tx) w.sig = false :=
    bridged_model_totalReject w.model w.bridge w.key (fundingTag ++ w.tx) w.sig
  have hchk := w.checked
  unfold verifyFundingChecked verifyFunding at hchk
  rw [hf] at hchk
  simp at hchk

/-- At `withVendorEcdsa`, the checked funding relation has no witness.  The
model value exists; the relation is empty. -/
theorem withVendorEcdsa_funding_uninhabited :
    ∀ (M₀ : PrimitiveModel) (hEuf : EufCma vendorVerify),
      ¬ ∃ (key : PubKey) (tx : ByteArray) (sig : EcdsaSig),
        verifyFundingChecked (withVendorEcdsa M₀ hEuf) key tx sig = true := by
  intro M₀ hEuf
  rintro ⟨key, tx, sig, hchk⟩
  have hf := withVendorEcdsa_no_funding M₀ hEuf key tx sig
  rw [hf] at hchk
  exact Bool.false_ne_true hchk

/-- At `withVendorEcdsa`, the verifier accepts nothing. -/
theorem withVendorEcdsa_accepts_nothing :
    ∀ (M₀ : PrimitiveModel) (hEuf : EufCma vendorVerify),
      ¬ ∃ (pk : PubKey) (msg : ByteArray) (sig : EcdsaSig),
        (withVendorEcdsa M₀ hEuf).ecdsaVerify pk msg sig = true := by
  intro M₀ hEuf
  rintro ⟨pk, msg, sig, h⟩
  have hf := withVendorEcdsa_totalReject M₀ hEuf pk msg sig
  rw [hf] at h
  exact Bool.false_ne_true h

/-- C3 at the concrete vendored verifier is exactly the absence of any
accepted input. -/
theorem vendorVerify_no_acceptance_of_eufCma
    (hEuf : EufCma vendorVerify) :
    ¬ ∃ (pk : PubKey) (msg : ByteArray) (sig : EcdsaSig),
      vendorVerify pk msg sig = true := by
  rintro ⟨pk, msg, sig, h⟩
  have hf := (eufCma_vendorVerify_iff_totalReject.mp hEuf) pk msg sig
  rw [hf] at h
  exact Bool.false_ne_true h

/-- The model value `withVendorEcdsa` exists under its C3 hypothesis, even
though its verification relation is empty.  This separates inhabitancy of the
model type from inhabitancy of the protocol relation. -/
theorem withVendorEcdsa_value_exists
    (M₀ : PrimitiveModel) (hEuf : EufCma vendorVerify) :
    ∃ M : PrimitiveModel, M = withVendorEcdsa M₀ hEuf :=
  ⟨withVendorEcdsa M₀ hEuf, rfl⟩

/-! ## 5. Separation and scope -/

/-- Two models satisfy the same C3 field; one accepts an input, the other
accepts nothing.  A witness for a signature interface therefore does not
establish that every model/relation at that interface is inhabited. -/
theorem vacuous_nonvacuous_separation :
    EufCma auditModel.ecdsaVerify ∧
      (∃ (pk : PubKey) (msg : ByteArray) (sig : EcdsaSig),
        auditModel.ecdsaVerify pk msg sig = true) ∧
      EufCma (vacuousEcdsaModel auditModel).ecdsaVerify ∧
      (¬ ∃ (pk : PubKey) (msg : ByteArray) (sig : EcdsaSig),
        (vacuousEcdsaModel auditModel).ecdsaVerify pk msg sig = true) :=
  ⟨auditModel.ecdsa_eufCma,
    ⟨⟨ByteArray.empty⟩, ByteArray.empty, ⟨ByteArray.empty⟩,
      auditModel_accepts_empty⟩,
    vacuousEcdsaModel_eufCma auditModel,
    vacuousEcdsaModel_accepts_nothing auditModel⟩

/-- A witness for one carrier type does not repair an unrelated empty
predicate.  This is the scope statement for the whole audit: existence of a
`Commitment` does not imply existence of a `DigestBindsMod` tag. -/
theorem witness_not_universal :
    (∃ c : Commitment, c.fundingValueSat = 1000) ∧
      (¬ ∃ tag : ByteArray, DigestBindsMod tag) :=
  ⟨⟨commitmentWitness, rfl⟩, digestBindsMod_uninhabited⟩

/-! ## 6. The witness registry -/

/-- Stable identifiers for the audited items. -/
inductive WitnessId where
  | commitment
  | commitmentTx
  | gossipState
  | gossipNodeAnnounced
  | openChannel
  | coverageWitness
  | coverageNoEmptyDecode
  | rotationWitness
  | handshakeState
  | primitiveModel
  | keyModel
  | acceptChannel
  | storedAccept
  | channelIdValid
  | pubKeyValid
  | paymentHashValid
  | gossipSignatureValid
  | canonical33
  | canonical32
  | canonicalBinding
  | eufCmaNonvacuous
  | gossipEmptyNoAnnouncement
  | fundingTagDigestEmpty
  | digestBindsModEmpty
  | nBytes33NotCanonical
  | bridgedFundingEmpty
  | withVendorFundingEmpty
  | withVendorAcceptsNothing
  | vacuousNonvacuous
  | scopeSeparation
deriving Repr, DecidableEq, BEq

/-- The audit classification of a registered item. -/
inductive WitnessKind where
  | structure
  | predicate
  | positiveDomain
  | signatureInterface
  | negativeBoundary
  | vacuity
  | separation
deriving Repr, DecidableEq, BEq

/-- One registry record.  The `statement` field is the actual proposition and
`proof` is its proof, so the registry is a sound dependent list, not a table of
names. -/
structure AuditedWitness where
  id : WitnessId
  kind : WitnessKind
  theoremName : String
  statement : Prop
  proof : statement

/-- The audited witness registry.  Each entry is a public theorem of this
module; the `proof` field is checked by the kernel. -/
def witnessRegistry : List AuditedWitness :=
  [ { id := .commitment, kind := .structure,
      theoremName := "commitment_witness",
      statement := ∃ c : Commitment,
        c.fundingValueSat = 1000 ∧ c.toLocalSat = 600 ∧
          c.toRemoteSat = 300 ∧ c.feeSat = 100 ∧
          c.toLocalSat + c.toRemoteSat + c.feeSat = c.fundingValueSat,
      proof := commitment_witness }
  , { id := .commitmentTx, kind := .structure,
      theoremName := "commitmentTx_witness",
      statement := ∃ tx : CommitmentTx,
        tx.commitment = commitmentWitness ∧ tx.dustLimitSat = 0 ∧
          tx.toLocalOutput.isSome = true,
      proof := commitmentTx_witness }
  , { id := .gossipState, kind := .structure,
      theoremName := "gossipState_witness",
      statement := ∃ s : GossipState,
        s.announcements = [] ∧ s.updates = [] ∧
          s.nodeAnnouncements = [] ∧ s.latestUpdateTimestamp = 0,
      proof := gossipState_witness }
  , { id := .gossipNodeAnnounced, kind := .predicate,
      theoremName := "gossipState_nodeAnnounced",
      statement := NodeAnnounced gossipStateNode key0,
      proof := gossipState_nodeAnnounced }
  , { id := .openChannel, kind := .structure,
      theoremName := "openChannel_witness",
      statement := ∃ o : OpenChannel,
        o.fundingSatoshis = 1000 ∧ o.pushMsat = ⟨0⟩ ∧
          o.fundingPubKey = key0,
      proof := openChannel_witness }
  , { id := .coverageWitness, kind := .structure,
      theoremName := "coverageWitness_witness",
      statement := ∃ w : CoverageWitness, w.entries.length = 1,
      proof := coverageWitness_witness }
  , { id := .coverageNoEmptyDecode, kind := .negativeBoundary,
      theoremName := "oneSigWire_no_empty_decode",
      statement := ¬ ∃ w : CoverageWitness,
        decodeCoverage oneSigWire w = some [],
      proof := oneSigWire_no_empty_decode }
  , { id := .rotationWitness, kind := .structure,
      theoremName := "rotationWitness_witness",
      statement := ∃ w : RotationWitness,
        w.oldId = key0 ∧ w.newId = key1 ∧ w.Links key0 key1,
      proof := rotationWitness_witness }
  , { id := .handshakeState, kind := .structure,
      theoremName := "handshakeState_witness",
      statement := ∃ s : HandshakeState, Reachable s ∧ s.ready = false,
      proof := handshakeState_witness }
  , { id := .primitiveModel, kind := .structure,
      theoremName := "primitiveModel_witness",
      statement := ∃ M : PrimitiveModel,
        EufCma M.ecdsaVerify ∧
          (∃ (pk : PubKey) (msg : ByteArray) (sig : EcdsaSig),
            M.ecdsaVerify pk msg sig = true),
      proof := primitiveModel_witness }
  , { id := .keyModel, kind := .structure,
      theoremName := "keyModel_witness",
      statement := ∃ (M : PrimitiveModel) (K : KeyModel M) (seed : ByteArray),
        K.Owns (K.publicOfSeed seed) (K.secretOfSeed seed),
      proof := keyModel_witness }
  , { id := .acceptChannel, kind := .structure,
      theoremName := "acceptChannel_witness",
      statement := ∃ m : AcceptChannel, m.fundingPubKey = key0,
      proof := acceptChannel_witness }
  , { id := .storedAccept, kind := .predicate,
      theoremName := "storedAccept_witness",
      statement := ∃ (M : PrimitiveModel) (K : KeyModel M) (seed : ByteArray)
        (s : HandshakeState) (m : AcceptChannel),
        StoredAccept K seed s m ∧ s.acceptReceived = true,
      proof := storedAccept_witness }
  , { id := .channelIdValid, kind := .predicate,
      theoremName := "channelId_valid_witness",
      statement := ∃ c : ChannelId, c.Valid,
      proof := channelId_valid_witness }
  , { id := .pubKeyValid, kind := .predicate,
      theoremName := "pubKey_valid_witness",
      statement := ∃ p : PubKey, p.Valid,
      proof := pubKey_valid_witness }
  , { id := .paymentHashValid, kind := .predicate,
      theoremName := "paymentHash_valid_witness",
      statement := ∃ h : PaymentHash, h.Valid,
      proof := paymentHash_valid_witness }
  , { id := .gossipSignatureValid, kind := .predicate,
      theoremName := "gossipSignature_valid_witness",
      statement := ∃ s : GossipSignature, s.Valid,
      proof := gossipSignature_valid_witness }
  , { id := .canonical33, kind := .positiveDomain,
      theoremName := "canonical33_witness",
      statement := ∃ m : ByteArray, Canonical33 m,
      proof := canonical33_witness }
  , { id := .canonical32, kind := .positiveDomain,
      theoremName := "canonical32_witness",
      statement := ∃ m : ByteArray, CanonicalDigest32 m,
      proof := canonical32_witness }
  , { id := .canonicalBinding, kind := .positiveDomain,
      theoremName := "canonicalDomain_binds",
      statement := DigestBindsModOn Canonical33 fundingTag,
      proof := canonicalDomain_binds }
  , { id := .eufCmaNonvacuous, kind := .signatureInterface,
      theoremName := "eufCma_nonvacuous_witness",
      statement := ∃ v : PubKey → ByteArray → EcdsaSig → Bool,
        EufCma v ∧
          (∃ (pk : PubKey) (msg : ByteArray) (sig : EcdsaSig),
            v pk msg sig = true),
      proof := eufCma_nonvacuous_witness }
  , { id := .gossipEmptyNoAnnouncement, kind := .negativeBoundary,
      theoremName := "gossipStateWitness_not_nodeAnnounced",
      statement := ¬ NodeAnnounced gossipStateWitness key0,
      proof := gossipStateWitness_not_nodeAnnounced }
  , { id := .fundingTagDigestEmpty, kind := .negativeBoundary,
      theoremName := "fundingTag_digestBindsMod_empty",
      statement := ¬ DigestBindsMod fundingTag,
      proof := fundingTag_digestBindsMod_empty }
  , { id := .digestBindsModEmpty, kind := .negativeBoundary,
      theoremName := "digestBindsMod_uninhabited",
      statement := ¬ ∃ tag : ByteArray, DigestBindsMod tag,
      proof := digestBindsMod_uninhabited }
  , { id := .nBytes33NotCanonical, kind := .negativeBoundary,
      theoremName := "nBytes33_not_canonical",
      statement := ¬ Canonical33 nBytes33,
      proof := nBytes33_not_canonical }
  , { id := .bridgedFundingEmpty, kind := .vacuity,
      theoremName := "bridgedFundingWitness_uninhabited",
      statement := ¬ Nonempty BridgedFundingWitness,
      proof := bridgedFundingWitness_uninhabited }
  , { id := .withVendorFundingEmpty, kind := .vacuity,
      theoremName := "withVendorEcdsa_funding_uninhabited",
      statement := ∀ (M₀ : PrimitiveModel) (hEuf : EufCma vendorVerify),
        ¬ ∃ (key : PubKey) (tx : ByteArray) (sig : EcdsaSig),
          verifyFundingChecked (withVendorEcdsa M₀ hEuf) key tx sig = true,
      proof := withVendorEcdsa_funding_uninhabited }
  , { id := .withVendorAcceptsNothing, kind := .vacuity,
      theoremName := "withVendorEcdsa_accepts_nothing",
      statement := ∀ (M₀ : PrimitiveModel) (hEuf : EufCma vendorVerify),
        ¬ ∃ (pk : PubKey) (msg : ByteArray) (sig : EcdsaSig),
          (withVendorEcdsa M₀ hEuf).ecdsaVerify pk msg sig = true,
      proof := withVendorEcdsa_accepts_nothing }
  , { id := .vacuousNonvacuous, kind := .separation,
      theoremName := "vacuous_nonvacuous_separation",
      statement := EufCma auditModel.ecdsaVerify ∧
        (∃ (pk : PubKey) (msg : ByteArray) (sig : EcdsaSig),
          auditModel.ecdsaVerify pk msg sig = true) ∧
        EufCma (vacuousEcdsaModel auditModel).ecdsaVerify ∧
        (¬ ∃ (pk : PubKey) (msg : ByteArray) (sig : EcdsaSig),
          (vacuousEcdsaModel auditModel).ecdsaVerify pk msg sig = true),
      proof := vacuous_nonvacuous_separation }
  , { id := .scopeSeparation, kind := .separation,
      theoremName := "witness_not_universal",
      statement := (∃ c : Commitment, c.fundingValueSat = 1000) ∧
        (¬ ∃ tag : ByteArray, DigestBindsMod tag),
      proof := witness_not_universal }
  ]

/-- The registry contains exactly 30 audited items. -/
theorem witnessRegistry_length : witnessRegistry.length = 30 := rfl

/-- Every registered proposition has a proof.  This is the mechanized
soundness statement for the registry. -/
theorem witnessRegistry_sound :
    ∀ e ∈ witnessRegistry, e.statement :=
  fun e _ => e.proof

/-- The projection of the registry to its stable ids. -/
def witnessRegistryIds : List WitnessId :=
  witnessRegistry.map (fun e => e.id)

/-- The projected registry has 30 ids. -/
theorem witnessRegistryIds_length : witnessRegistryIds.length = 30 := rfl

/-- The audited ids are pairwise distinct. -/
theorem witnessRegistryIds_nodup : witnessRegistryIds.Nodup := by
  decide

/-- The registry is non-empty. -/
theorem witnessRegistry_ne_nil : witnessRegistry ≠ [] := by
  decide

/-- The registry contains no duplicate ids. -/
theorem witnessRegistry_ids_nodup :
    (witnessRegistry.map (fun e => e.id)).Nodup :=
  witnessRegistryIds_nodup

end LnLean.Proofs.Model.NonVacuityTargets
