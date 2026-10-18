import LnLean.Routing.Gossip
import LnLean.Crypto.Sig
import LnLean.Proofs.Routing.GossipProps

/-!
# Model hardening F07 — gossip signature-validity admission

**Target.**  Parent obligation `LN-GOSSIP-SIG`: a length-respecting (`Valid`)
signature-verifier contract for BOLT 7 gossip, the theorem that accepted
`channel_update` / `channel_announcement` / `node_announcement` messages carry
64-byte signatures under that contract, and a mechanized counterexample showing
that the wave-A model does not enforce the length without the contract.

**English claim.**

* BOLT 1 defines the `signature` wire type as 64 bytes; BOLT 7 uses it for the
  four `channel_announcement` signatures, the `channel_update` signature, and
  the `node_announcement` signature.
* `lengthRespecting verify` is the admission contract on the abstract
  `SigVerifier`: if it accepts `(key, digest, sig)`, then `sig` is a `Valid`
  (64-byte) `GossipSignature`.
* Under that contract, every signature of an accepted gossip message is 64
  bytes.  The gate is the existing `applyGossipChecked` /
  `acceptChannelUpdate` admission path, which already requires the
  `signatureValid` predicates but not the byte length.
* The contract is not implied by the wave-A model: the always-accepting
  verifier accepts an empty signature, so the unconditional length claim is
  false.  The faithful unconditional statement is retained below with one
  `sorry`, next to the obligation marker, together with a concrete
  counterexample.

**BOLT sections.**  BOLT 1 §Lightning Message Format (`signature` is 64
bytes); BOLT 7 §The `channel_announcement` Message (four signatures),
§The `channel_update` Message (one signature), §The `node_announcement`
Message (one signature).

**Not modelled.**  Wire encoding and the double-SHA256 signed byte ranges.
Only the byte length is checked; no cryptographic unforgeability claim is
made (that remains assumption C3/C4/C8 in `docs/ASSUMPTIONS.md`).
-/

namespace LnLean.Proofs.ModelHardening.F07

open LnLean
open LnLean.Routing
open LnLean.Routing.GossipProps

set_option autoImplicit false

/-! ## The length-respecting verifier contract -/

/-- **The missing admission contract for `LN-GOSSIP-SIG`.**  A verifier
respects the BOLT 1/7 signature wire type when every signature it accepts is a
64-byte `GossipSignature`.  This is a `Prop` about the abstract `SigVerifier`,
not an axiom: every theorem that needs it takes it as a hypothesis. -/
def lengthRespecting (verify : SigVerifier) : Prop :=
  ∀ (key : PubKey) (digest : ByteArray) (sig : GossipSignature),
    verify key digest sig = true → sig.Valid

/-- Unpack the contract at one verification site. -/
theorem valid_of_lengthRespecting {verify : SigVerifier}
    (hl : lengthRespecting verify) {key : PubKey} {digest : ByteArray}
    {sig : GossipSignature} (h : verify key digest sig = true) : sig.Valid :=
  hl key digest sig h

/-! ## Per-message signature-length predicates -/

/-- All four BOLT 7 `channel_announcement` signatures are 64 bytes. -/
def channelAnnouncementSignatures64 (a : ChannelAnnellation) : Prop :=
  a.nodeSignature1.Valid ∧ a.nodeSignature2.Valid ∧
    a.bitcoinSignature1.Valid ∧ a.bitcoinSignature2.Valid

/-- The BOLT 7 `channel_update` signature is 64 bytes. -/
def channelUpdateSignature64 (u : ChannelUpdate) : Prop := u.signature.Valid

/-- The BOLT 7 `node_announcement` signature is 64 bytes. -/
def nodeAnnouncementSignature64 (n : NodeAnnouncement) : Prop :=
  n.signature.Valid

/-- Every signature carried by a gossip message is 64 bytes. -/
def gossipMessageSignatures64 : GossipMessage → Prop
  | .channelAnnouncement a => channelAnnouncementSignatures64 a
  | .channelUpdate u => channelUpdateSignature64 u
  | .nodeAnnouncement n => nodeAnnouncementSignature64 n

/-! ## The contract implies 64-byte signatures at each admission site -/

/-- A fully verified announcement has four 64-byte signatures under the
contract. -/
theorem announcement_signatures64_of_signaturesValid {verify : SigVerifier}
    (hl : lengthRespecting verify) {a : ChannelAnnellation}
    (h : a.signaturesValid verify) : channelAnnouncementSignatures64 a := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hl a.nodeKey1 a.digest a.nodeSignature1 h.1
  · exact hl a.nodeKey2 a.digest a.nodeSignature2 h.2.1
  · exact hl a.bitcoinKey1 a.digest a.bitcoinSignature1 h.2.2.1
  · exact hl a.bitcoinKey2 a.digest a.bitcoinSignature2 h.2.2.2

/-- **Accepted `channel_update` signatures are 64 bytes.**  The update passes
`acceptChannelUpdate`, which requires the model's `signatureValid` predicate;
the length contract supplies the missing byte-length consequence. -/
theorem accepted_update_signature_64 {verify : SigVerifier}
    (hl : lengthRespecting verify) (s : GossipState) (u : ChannelUpdate)
    (h : acceptChannelUpdate verify s u ≠ s) : u.signature.Valid :=
  hl u.signingKey u.digest u.signature
    (acceptChannelUpdate_change_requires_signature verify s u h)

/-- **Accepted `channel_announcement` signatures are 64 bytes.** -/
theorem accepted_announcement_signatures_64 {verify : SigVerifier}
    (hl : lengthRespecting verify) (s : GossipState) (a : ChannelAnnellation)
    (h : applyGossipChecked verify s (.channelAnnouncement a) ≠ s) :
    channelAnnouncementSignatures64 a :=
  announcement_signatures64_of_signaturesValid hl
    (applyGossipChecked_announcement_requires_signature verify s a h)

/-- **Accepted `node_announcement` signatures are 64 bytes.** -/
theorem accepted_node_announcement_signature_64 {verify : SigVerifier}
    (hl : lengthRespecting verify) (s : GossipState) (n : NodeAnnouncement)
    (h : applyGossipChecked verify s (.nodeAnnouncement n) ≠ s) :
    n.signature.Valid :=
  hl n.nodeId n.digest n.signature
    (applyGossipChecked_node_requires_signature verify s n h)

/-- **Accepted gossip messages carry only 64-byte signatures**, conditional on
the length-respecting contract.  This is the strongest true form of the
`LN-GOSSIP-SIG` claim for the signature-gated admission path. -/
theorem accepted_message_signatures_64_of_lengthRespecting
    {verify : SigVerifier} (hl : lengthRespecting verify) (s : GossipState)
    (m : GossipMessage) (h : applyGossipChecked verify s m ≠ s) :
    gossipMessageSignatures64 m := by
  cases m with
  | channelAnnouncement a => exact accepted_announcement_signatures_64 hl s a h
  | channelUpdate u => exact accepted_update_signature_64 hl s u h
  | nodeAnnouncement n => exact accepted_node_announcement_signature_64 hl s n h

/-- The same result for the announcement-binding path: a successful
`bindChannel` produces four 64-byte signatures under the contract. -/
theorem bound_announcement_signatures_64 {verify : SigVerifier}
    (hl : lengthRespecting verify) {a : ChannelAnnellation}
    {b : ChannelBinding} (h : bindChannel verify a = some b) :
    channelAnnouncementSignatures64 a :=
  announcement_signatures64_of_signaturesValid hl (bindChannel_requires_signature h)

/-! ## Faithful unconditional statement (false in the wave-A model) -/

/-- **Faithful unconditional form of `LN-GOSSIP-SIG`.**  Every signature of an
accepted gossip message is 64 bytes, with no hypothesis on the verifier.  This
is false in the wave-A model, because `SigVerifier` is an arbitrary function:
`accepted_message_signatures_64_counterexample` below exhibits an
always-accepting verifier and an empty signature.  The missing admission is
exactly `lengthRespecting` (or, equivalently, a byte-length check in
`acceptChannelUpdate` / `applyGossipChecked`). -/
-- OBLIGATION: LN-WF-F07 every signature of an accepted gossip message is 64 bytes (missing admission: the abstract SigVerifier need not respect GossipSignature.Valid; see accepted_message_signatures_64_counterexample)
theorem accepted_message_signatures_64 (verify : SigVerifier) (s : GossipState)
    (m : GossipMessage) (h : applyGossipChecked verify s m ≠ s) :
    gossipMessageSignatures64 m := by
  sorry

/-! ## Mechanized counterexample: the always-accepting verifier -/

private def emptySig : GossipSignature := ⟨ByteArray.empty⟩

private def emptyKey : PubKey := ⟨ByteArray.empty⟩

private def emptyScid : ShortChannelId := ⟨0, 0, 0⟩

/-- A verifier that accepts every signature.  It witnesses the missing
byte-length admission; it deliberately does not satisfy `lengthRespecting`. -/
private def acceptAll : SigVerifier := fun _ _ _ => true

private def emptyState : GossipState := ⟨[], [], []⟩

private def emptyUpdate : ChannelUpdate :=
  { shortChannelId := emptyScid
    timestamp := 1
    messageFlags := 0
    channelFlags := 0
    cltvDelta := 1
    htlcMinimumMsat := Msat.zero
    feeBaseMsat := Msat.zero
    feeProportionalMillionths := 0
    htlcMaximumMsat := Msat.MAX
    signingKey := emptyKey
    digest := ByteArray.empty
    signature := emptySig }

private def emptyAnnouncement : ChannelAnnellation :=
  { shortChannelId := emptyScid
    node1 := ⟨0⟩
    node2 := ⟨1⟩
    nodeKey1 := emptyKey
    nodeKey2 := emptyKey
    bitcoinKey1 := emptyKey
    bitcoinKey2 := emptyKey
    capacitySat := 1
    digest := ByteArray.empty
    nodeSignature1 := emptySig
    nodeSignature2 := emptySig
    bitcoinSignature1 := emptySig
    bitcoinSignature2 := emptySig }

private theorem emptySig_not_valid : ¬ emptySig.Valid := by
  simp [emptySig, GossipSignature.Valid]

/-- `acceptAll` violates the proposed contract. -/
theorem acceptAll_not_lengthRespecting : ¬ lengthRespecting acceptAll := by
  intro hl
  exact emptySig_not_valid (hl emptyKey ByteArray.empty emptySig (by rfl))

/-- Accepting the empty-signature update really changes the store. -/
private theorem acceptAll_emptyUpdate_changes :
    acceptChannelUpdate acceptAll emptyState emptyUpdate ≠ emptyState := by
  intro h
  have hu := congrArg GossipState.updates h
  simp [acceptChannelUpdate, GossipState.applyUpdate,
    GossipState.latestUpdateTimestamp, latestTimestamp, emptyState, emptyUpdate,
    ChannelUpdate.signatureValid, signatureValid, acceptAll] at hu

/-- Accepting the empty-signature announcement really changes the store. -/
private theorem acceptAll_emptyAnnouncement_changes :
    applyGossipChecked acceptAll emptyState (.channelAnnouncement emptyAnnouncement) ≠
      emptyState := by
  intro h
  have ha := congrArg GossipState.announcements h
  simp [applyGossipChecked, applyGossip, ChannelAnnellation.signaturesValid,
    signatureValid, acceptAll, emptyState] at ha

/-- **Counterexample to the unconditional update claim.**  The always-accepting
verifier accepts a `channel_update` whose signature is empty. -/
theorem accepted_update_signature_64_counterexample :
    ∃ (verify : SigVerifier) (s : GossipState) (u : ChannelUpdate),
      acceptChannelUpdate verify s u ≠ s ∧ ¬ u.signature.Valid :=
  ⟨acceptAll, emptyState, emptyUpdate, acceptAll_emptyUpdate_changes,
    by simpa [emptyUpdate] using emptySig_not_valid⟩

/-- **Counterexample to the unconditional message claim.**  The
always-accepting verifier stores a `channel_announcement` all of whose four
signatures are empty. -/
theorem accepted_message_signatures_64_counterexample :
    ∃ (verify : SigVerifier) (s : GossipState) (m : GossipMessage),
      applyGossipChecked verify s m ≠ s ∧ ¬ gossipMessageSignatures64 m := by
  refine ⟨acceptAll, emptyState, .channelAnnouncement emptyAnnouncement,
    acceptAll_emptyAnnouncement_changes, ?_⟩
  simp [gossipMessageSignatures64, channelAnnouncementSignatures64,
    emptyAnnouncement, emptySig, GossipSignature.Valid]

/-- The counterexample verifier cannot satisfy the contract, so the
conditional theorems above are not vacuous consequences of a definition that
every verifier meets. -/
theorem lengthRespecting_not_universal :
    ¬ ∀ verify : SigVerifier, lengthRespecting verify := by
  intro h
  exact acceptAll_not_lengthRespecting (h acceptAll)

end LnLean.Proofs.ModelHardening.F07
