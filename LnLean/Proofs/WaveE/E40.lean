/-
# E40 — Gossip signature validity (LN-GOSSIP-003)

**English claim.**  BOLT 7 gossip signatures are 64-byte compact ECDSA
signatures.  The wave-A model records the length as
`GossipSignature.Valid` (`s.bytes.size = 64`) but leaves the verifier
`SigVerifier` completely abstract, so `signatureValid` does not imply
`Valid`: an always-accepting verifier accepts a zero-byte signature.

This module:

* defines the missing admission contract `LengthRespecting verify`, i.e. a
  verifier only accepts 64-byte signatures;
* defines `lengthChecked verify`, the verifier wrapper that enforces the
  contract structurally, and proves it satisfies `LengthRespecting`;
* proves the conditional 64-byte theorem for accepted `channel_update`s,
  for the four `channel_announcement` signatures, and for the
  `node_announcement` signature (unconditional for `lengthChecked`);
* proves that the contract is *exactly* the missing hypothesis: the
  unconditional update statement is equivalent to `LengthRespecting verify`;
* mechanises the counterexample: an always-accepting verifier accepts an
  update carrying an empty signature, and that acceptance really changes the
  store.

BOLT 7: `channel_announcement` (`refs/bolts/07-routing-gossip.md:155-213`),
`channel_update` (`:444`, `:544-558`), `node_announcement` (`:382`).  BOLT 1
defines the 64-byte `signature` wire type.  Unforgeability is **not** claimed
here; that is assumption C3/C4/C8 in `docs/ASSUMPTIONS.md`.

The wave-A model, its checked application functions, and the store laws live
in `LnLean.Routing.Gossip` and `LnLean.Proofs.Routing.GossipProps`; this
module adds only the length contract and its consequences.
-/

import LnLean.Routing.Gossip
import LnLean.Crypto.Sig
import LnLean.Proofs.Routing.GossipProps

namespace LnLean.Proofs.WaveE.E40

open LnLean.Routing
open LnLean.Routing.GossipProps

set_option autoImplicit false

/-! ## The length-respecting verifier contract -/

/-- **The missing admission contract for `LN-GOSSIP-003`.**  A verifier is
length-respecting when every signature it accepts is a 64-byte BOLT 7
signature.  This is the exact property that the abstract `SigVerifier`
function type does not provide. -/
def LengthRespecting (verify : SigVerifier) : Prop :=
  ∀ (key : PubKey) (digest : ByteArray) (sig : GossipSignature),
    verify key digest sig = true → sig.Valid

/-- Enforce the 64-byte wire rule in the verifier itself.  The wrapper checks
the length before delegating to the underlying verifier, so it satisfies
`LengthRespecting` by construction. -/
def lengthChecked (verify : SigVerifier) : SigVerifier :=
  fun key digest sig => verify key digest sig && (sig.bytes.size == 64)

/-- `GossipSignature.Valid` is decidable, and a 64-byte test is the same
predicate. -/
theorem waveE_e40_valid_iff_size_eq (sig : GossipSignature) :
    sig.Valid ↔ sig.bytes.size = 64 :=
  Iff.rfl

/-- The length-checking wrapper only accepts signatures that the underlying
verifier accepts.  (Sanity law: wrapping cannot turn a rejection into an
acceptance.) -/
theorem waveE_e40_lengthChecked_sound {verify : SigVerifier} {key : PubKey}
    {digest : ByteArray} {sig : GossipSignature}
    (h : lengthChecked verify key digest sig = true) :
    verify key digest sig = true := by
  unfold lengthChecked at h
  exact (Bool.and_eq_true ..).mp h |>.1

/-- **`lengthChecked` is length-respecting.**  This is the reusable guard
that closes `LN-GOSSIP-003` at the admission boundary. -/
theorem waveE_e40_lengthChecked_lengthRespecting (verify : SigVerifier) :
    LengthRespecting (lengthChecked verify) := by
  intro key digest sig h
  unfold lengthChecked at h
  have hs := (Bool.and_eq_true ..).mp h
  simpa [GossipSignature.Valid] using hs.2

/-! ## Concrete witnesses

These are used both for the counterexample and for the necessity direction
of the contract equivalence below.
-/

/-- A verifier that accepts every signature.  Used only to expose the
wave-A admission gap; it is not a model of any real signature scheme. -/
def acceptAll : SigVerifier := fun _ _ _ => true

/-- The zero-byte signature. -/
def emptySig : GossipSignature := ⟨ByteArray.empty⟩

/-- An empty public key. -/
def zeroKey : PubKey := ⟨ByteArray.empty⟩

/-- The zero `short_channel_id`. -/
def zeroScid : ShortChannelId := ⟨0, 0, 0⟩

/-- The empty gossip store. -/
def emptyState : GossipState := ⟨[], [], []⟩

/-- A synthetic `channel_update` with a chosen key, digest, and signature.
Its timestamp is `1`, so it is newer than the empty store's clock. -/
def mkUpdate (key : PubKey) (digest : ByteArray) (sig : GossipSignature) :
    ChannelUpdate :=
  { shortChannelId := zeroScid
    timestamp := 1
    messageFlags := 0
    channelFlags := 0
    cltvDelta := 1
    htlcMinimumMsat := Msat.zero
    feeBaseMsat := Msat.zero
    feeProportionalMillionths := 0
    htlcMaximumMsat := Msat.MAX
    signingKey := key
    digest := digest
    signature := sig }

/-- The synthetic update with an empty key, empty digest, and empty
signature. -/
def emptySigUpdate : ChannelUpdate :=
  mkUpdate zeroKey ByteArray.empty emptySig

/-- A verifying update with timestamp `1` is accepted into the empty store
whenever its signature verifies. -/
theorem waveE_e40_acceptChannelUpdate_mkUpdate_ne (verify : SigVerifier)
    (key : PubKey) (digest : ByteArray) (sig : GossipSignature)
    (hsig : verify key digest sig = true) :
    acceptChannelUpdate verify emptyState (mkUpdate key digest sig) ≠
      emptyState := by
  intro heq
  have hvalid : (mkUpdate key digest sig).signatureValid verify := by
    simpa [ChannelUpdate.signatureValid, signatureValid, mkUpdate] using hsig
  have hnew : emptyState.latestUpdateTimestamp <
      (mkUpdate key digest sig).timestamp := by
    simp [emptyState, mkUpdate, GossipState.latestUpdateTimestamp, latestTimestamp]
  have hupd := GossipState.applyUpdate_new emptyState
    (mkUpdate key digest sig) hnew
  have hu := congrArg GossipState.updates heq
  unfold acceptChannelUpdate at hu
  rw [ite_eq_left hvalid, hupd] at hu
  simp [emptyState] at hu

/-! ## Accepted `channel_update`s -/

-- REPAIRED: the unconditional `waveE_e40_accepted_update_signature_length` is
-- false for an arbitrary `SigVerifier`; see the retained counterexample
-- `waveE_e40_empty_signature_accepted_counterexample`.  The strongest true
-- replacement is `waveE_e40_accepted_update_signature_length_iff_lengthRespecting`
-- (acceptance implies a 64-byte signature exactly under `LengthRespecting`);
-- its forward direction is the conditional
-- `waveE_e40_accepted_update_signature_length_of_length_respecting`.

/-- **Conditional 64-byte theorem for `channel_update`.**  Under a
length-respecting verifier, acceptance implies a 64-byte signature.  The
only added hypothesis is the contract `LengthRespecting verify`; acceptance
already entails `signatureValid` by `acceptChannelUpdate_sound`. -/
theorem waveE_e40_accepted_update_signature_length_of_length_respecting
    (verify : SigVerifier) (hlen : LengthRespecting verify)
    (s : GossipState) (u : ChannelUpdate)
    (h : acceptChannelUpdate verify s u ≠ s) :
    u.signature.Valid :=
  hlen u.signingKey u.digest u.signature
    (acceptChannelUpdate_change_requires_signature verify s u h)

/-- **The unconditional statement is equivalent to the contract.**  On the
wave-A model the missing hypothesis is not merely sufficient but necessary:
if every accepted update has a 64-byte signature, then the verifier is
length-respecting.  (The witness update has timestamp `1`, so it is accepted
into the empty store as soon as the verifier accepts it.)

This is the precise statement of "the only missing ingredient is a
length-respecting verifier". -/
theorem waveE_e40_accepted_update_signature_length_iff_lengthRespecting
    (verify : SigVerifier) :
    LengthRespecting verify ↔
      ∀ (s : GossipState) (u : ChannelUpdate),
        acceptChannelUpdate verify s u ≠ s → u.signature.Valid := by
  constructor
  · intro hlen s u h
    exact waveE_e40_accepted_update_signature_length_of_length_respecting
      verify hlen s u h
  · intro hacc key digest sig hsig
    exact hacc emptyState (mkUpdate key digest sig)
      (waveE_e40_acceptChannelUpdate_mkUpdate_ne verify key digest sig hsig)

/-- **Unconditional 64-byte theorem for the guarding verifier.**  With
`lengthChecked`, every accepted update has a 64-byte signature, with no
extra hypothesis. -/
theorem waveE_e40_accepted_update_signature_length_lengthChecked
    (verify : SigVerifier) (s : GossipState) (u : ChannelUpdate)
    (h : acceptChannelUpdate (lengthChecked verify) s u ≠ s) :
    u.signature.Valid :=
  waveE_e40_accepted_update_signature_length_of_length_respecting
    (lengthChecked verify) (waveE_e40_lengthChecked_lengthRespecting verify) s u h

/-- A length-checked verifier rejects a non-64-byte signature outright, so
such an update cannot change the store. -/
theorem waveE_e40_acceptChannelUpdate_lengthChecked_rejects
    (verify : SigVerifier) (s : GossipState) (u : ChannelUpdate)
    (h : ¬ u.signature.Valid) :
    acceptChannelUpdate (lengthChecked verify) s u = s := by
  apply acceptChannelUpdate_rejects_invalid
  intro hsig
  exact h (waveE_e40_lengthChecked_lengthRespecting verify u.signingKey u.digest
    u.signature hsig)

/-! ## Accepted `channel_announcement`s and `node_announcement`s -/

/-- **Conditional 64-byte theorem for all four `channel_announcement`
signatures.**  A length-respecting verifier makes every accepted
announcement carry four 64-byte signatures. -/
theorem waveE_e40_accepted_announcement_signatures_length_of_length_respecting
    (verify : SigVerifier) (hlen : LengthRespecting verify)
    (s : GossipState) (a : ChannelAnnellation)
    (h : applyGossipChecked verify s (.channelAnnouncement a) ≠ s) :
    a.nodeSignature1.Valid ∧ a.nodeSignature2.Valid ∧
      a.bitcoinSignature1.Valid ∧ a.bitcoinSignature2.Valid := by
  have hs := applyGossipChecked_announcement_requires_signature verify s a h
  rcases hs with ⟨h1, h2, h3, h4⟩
  exact ⟨hlen a.nodeKey1 a.digest a.nodeSignature1 h1,
    hlen a.nodeKey2 a.digest a.nodeSignature2 h2,
    hlen a.bitcoinKey1 a.digest a.bitcoinSignature1 h3,
    hlen a.bitcoinKey2 a.digest a.bitcoinSignature2 h4⟩

/-- Unconditional form for the guarding verifier. -/
theorem waveE_e40_accepted_announcement_signatures_length_lengthChecked
    (verify : SigVerifier) (s : GossipState) (a : ChannelAnnellation)
    (h : applyGossipChecked (lengthChecked verify) s
      (.channelAnnouncement a) ≠ s) :
    a.nodeSignature1.Valid ∧ a.nodeSignature2.Valid ∧
      a.bitcoinSignature1.Valid ∧ a.bitcoinSignature2.Valid :=
  waveE_e40_accepted_announcement_signatures_length_of_length_respecting
    (lengthChecked verify) (waveE_e40_lengthChecked_lengthRespecting verify) s a h

/-- **Conditional 64-byte theorem for `node_announcement`.** -/
theorem waveE_e40_accepted_node_announcement_signature_length_of_length_respecting
    (verify : SigVerifier) (hlen : LengthRespecting verify)
    (s : GossipState) (n : NodeAnnouncement)
    (h : applyGossipChecked verify s (.nodeAnnouncement n) ≠ s) :
    n.signature.Valid :=
  hlen n.nodeId n.digest n.signature
    (applyGossipChecked_node_requires_signature verify s n h)

/-- Unconditional form for the guarding verifier. -/
theorem waveE_e40_accepted_node_announcement_signature_length_lengthChecked
    (verify : SigVerifier) (s : GossipState) (n : NodeAnnouncement)
    (h : applyGossipChecked (lengthChecked verify) s
      (.nodeAnnouncement n) ≠ s) :
    n.signature.Valid :=
  waveE_e40_accepted_node_announcement_signature_length_of_length_respecting
    (lengthChecked verify) (waveE_e40_lengthChecked_lengthRespecting verify) s n h

/-! ## Mechanised counterexample

The witnesses are defined above.  Here we prove that `acceptAll` accepts the
empty-signature update, that acceptance really changes the store, and that
the length-checking guard rejects the same update.
-/

/-- `acceptAll` accepts the empty signature, so it is not
length-respecting. -/
theorem waveE_e40_acceptAll_not_lengthRespecting :
    ¬ LengthRespecting acceptAll := by
  intro hlen
  have hv := hlen zeroKey ByteArray.empty emptySig (by simp [acceptAll])
  simp [emptySig, GossipSignature.Valid] at hv

/-- **`acceptAll` accepts the empty-signature update, and the store really
changes.**  This is the wave-A counterexample body: acceptance means
`updates = [emptySigUpdate]`, not the empty list. -/
theorem waveE_e40_acceptAll_emptySigUpdate_changes :
    acceptChannelUpdate acceptAll emptyState emptySigUpdate ≠ emptyState :=
  waveE_e40_acceptChannelUpdate_mkUpdate_ne acceptAll zeroKey ByteArray.empty emptySig
    (by simp [acceptAll])

/-- **Counterexample to `LN-GOSSIP-003`.**  There is a verifier, a store,
and an accepted update whose signature is not 64 bytes.  The verifier is
necessarily not length-respecting (`waveE_e40_acceptAll_not_lengthRespecting`),
which identifies the missing hypothesis exactly. -/
theorem waveE_e40_empty_signature_accepted_counterexample :
    ∃ (verify : SigVerifier) (s : GossipState) (u : ChannelUpdate),
      acceptChannelUpdate verify s u ≠ s ∧ ¬ u.signature.Valid ∧
        ¬ LengthRespecting verify := by
  refine ⟨acceptAll, emptyState, emptySigUpdate,
    waveE_e40_acceptAll_emptySigUpdate_changes, ?_,
    waveE_e40_acceptAll_not_lengthRespecting⟩
  simp [emptySigUpdate, mkUpdate, emptySig, GossipSignature.Valid]

/-- The counterexample survives the length-checking wrapper: adding the guard
turns acceptance into rejection.  The empty-signature update is a no-op under
`lengthChecked`. -/
theorem waveE_e40_lengthChecked_rejects_emptySigUpdate :
    acceptChannelUpdate (lengthChecked acceptAll) emptyState emptySigUpdate =
      emptyState :=
  waveE_e40_acceptChannelUpdate_lengthChecked_rejects acceptAll emptyState
    emptySigUpdate (by
      simp [emptySigUpdate, mkUpdate, emptySig, GossipSignature.Valid])

end LnLean.Proofs.WaveE.E40
