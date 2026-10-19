import LnLean.Crypto.Noise
import LnLean.Proofs.Protocol.TransportAuthTargets

/-!
# A model-level BOLT 8/Noise transport binding (`L1-03`, wave 11)

**English claim.**  `TransportAuthTargets` isolates the explicit
`SessionKeyBinding` law: the key a transport claims to have authenticated for a
session must equal the `funding_pubkey` advertised in the delivered
`open_channel`.  That module deliberately stops at the interface.  It does not
say what a transport session *is*, how session keys are derived, how a frame is
accepted, or why an accepted frame should be attributed to the session peer.

This module supplies an **additive, model-level** BOLT 8/Noise-shaped layer.
It does not edit `Crypto/Noise.lean`, `TransportAuthTargets.lean`, any core
handshake file, or any existing import.  It is *not* an implementation of Noise
and it makes **no computational-security claim**.

## What is modelled

* `NoiseHandshake` records the `Noise_XK`-shaped static keys, ephemeral keys,
  and handshake transcript.  `NoiseSession` records a local role and the two
  directional `SessionKey`s.
* `SessionKey` is an opaque value: a `Nat` identity, opaque material bytes, the
  transcript it was derived from, the peer static key bound into that
  transcript, and the role.  `deriveKey` is the only constructor used by the
  positive layer, and its projection laws are explicit.
* `NoiseHandshakeSound s` is the explicit derivation assumption: the session's
  send/receive keys are exactly `deriveKey` of its handshake and role.  It does
  not assert secrecy, freshness, or that a real Noise handshake occurred.
* `TransportFrame` carries a session id, a nonce counter, ciphertext, and a MAC.
  `AeadAccept C k f` is the abstract acceptance relation of a
  `TransportCrypto` model.
* `AeadUnforgeable C` says every accepted frame is one the key's owner could
  have produced.  `AeadKeyBinding C` says two keys that accept the same frame
  agree on the peer key.  `NonceFresh w f` says the frame nonce has not been
  seen in the receiver window.
* `AeadUnforgeable` plus `NoiseHandshakeSound` prove that an accepted frame is
  produced under the session key and hence is bound to the session peer static
  key (`accepted_frame_bound_to_peer`).  If that peer static key equals the
  advertised funding key, the explicit `SessionKeyBinding` follows.
* The receive rule `recv` checks both `AeadAccept` and `NonceFresh`; a frame is
  rejected when its nonce is already in the window.  `recvLoose`, which drops
  the freshness check, is the mechanised replay counterexample.

## What is *not* claimed

Nothing here claims confidentiality, IND-CCA security, real ChaCha20-Poly1305,
real HKDF/ECDH, key ownership, or that a concrete Noise implementation exists.
`TransportCrypto` is an abstract relation; the concrete `strictCrypto` /
`looseCrypto` instances are finite model witnesses used to separate the
positive laws from the counterexamples.  In `strictCrypto`, `produced` is
definitionally `accept`, so `AeadUnforgeable` is true for the *model*, not for a
real AEAD.

## BOLT anchors

* BOLT 8 §"Noise Protocol Instantiation": `Noise_XK`, static and ephemeral
  keys, handshake hash.
* BOLT 8 §"Encrypting and Sending Messages" / §"Receiving and Decrypting
  Messages": per-direction keys, 12-byte nonce counters, authenticated
  encryption.
* BOLT 2 §"The `open_channel` Message": `funding_pubkey` is advertised, not
  proved.
-/

namespace LnLean.Proofs.Protocol.NoiseTransportTargets

set_option autoImplicit false

open LnLean
open LnLean.Crypto
open LnLean.Protocol
open LnLean.Bitcoin
open LnLean.Proofs.Bitcoin.FundingScriptTargets
open LnLean.Proofs.Bitcoin.FundingAuthTargets
open LnLean.Proofs.Protocol.OpenChannelWireTargets
open LnLean.Proofs.Protocol.OpenChannelRoutingTargets
open LnLean.Proofs.Protocol.TransportAuthTargets
open Classical

noncomputable section

/-! ## 1. Handshake, roles, and the opaque session-key schedule -/

/-- The two directions of a BOLT 8 session.  This is the existing
`LnLean.Crypto.NoiseRole`; the equations below only add the local operations
needed by this module. -/
abbrev Role := NoiseRole

/-- Direction flip.  A session's receive key is derived with the opposite role,
which is exactly how BOLT 8 obtains the two per-direction keys. -/
def roleFlip : NoiseRole → NoiseRole
  | .initiator => .responder
  | .responder => .initiator

@[simp] theorem roleFlip_flip (r : NoiseRole) : roleFlip (roleFlip r) = r := by
  cases r <;> rfl

/-- Numeric role tag used only to keep the two opaque key identities distinct
in the model. -/
def roleCode : NoiseRole → Nat
  | .initiator => 0
  | .responder => 1

/-- Byte tag appended to the transcript in the opaque key material. -/
def roleTag : NoiseRole → UInt8
  | .initiator => 1
  | .responder => 2

/-- A `Noise_XK`-shaped handshake record.  The static and ephemeral keys and the
transcript are the only fields; no ECDH, HKDF, or signature operation is
interpreted. -/
structure NoiseHandshake where
  /-- BOLT 8 uses `Noise_XK` exclusively. -/
  pattern : HandshakePattern
  /-- The initiator's long-term static key. -/
  initiatorStatic : PubKey
  /-- The responder's long-term static key. -/
  responderStatic : PubKey
  /-- The initiator's ephemeral key. -/
  initiatorEphemeral : PubKey
  /-- The responder's ephemeral key. -/
  responderEphemeral : PubKey
  /-- Opaque handshake transcript / handshake hash bytes. -/
  transcript : ByteArray
deriving Repr, BEq

/-- The static key of the *other* party, from the point of view of a role.  For
an initiator this is the responder's static key; for a responder it is the
initiator's static key. -/
def NoiseHandshake.peerStaticOf (h : NoiseHandshake) : NoiseRole → PubKey
  | .initiator => h.responderStatic
  | .responder => h.initiatorStatic

/-- A directional session key.  The fields are opaque model data:
`material` is not a real ChaCha20-Poly1305 key, `id` is a model identity, and
`peer` is the static key bound into the derivation.  No secrecy is claimed. -/
structure SessionKey where
  /-- Opaque model identity for this directional key. -/
  id : Nat
  /-- Opaque key material (a transcript tag in the model). -/
  material : ByteArray
  /-- The handshake transcript this key is derived from. -/
  transcript : ByteArray
  /-- The peer static key bound into the derivation. -/
  peer : PubKey
  /-- The role that owns this key. -/
  role : NoiseRole
deriving Repr, BEq

/-- The explicit key-derivation law.  Both directions are obtained by applying
this deterministic function to the handshake and the owning role.  The peer
static key is part of the derived value, modelling the fact that the Noise
handshake hash binds the static keys. -/
def deriveKey (h : NoiseHandshake) (r : NoiseRole) : SessionKey where
  id := h.transcript.size * 2 + roleCode r
  material := h.transcript.push (roleTag r)
  transcript := h.transcript
  peer := h.peerStaticOf r
  role := r

@[simp] theorem deriveKey_id (h : NoiseHandshake) (r : NoiseRole) :
    (deriveKey h r).id = h.transcript.size * 2 + roleCode r := rfl

@[simp] theorem deriveKey_material (h : NoiseHandshake) (r : NoiseRole) :
    (deriveKey h r).material = h.transcript.push (roleTag r) := rfl

@[simp] theorem deriveKey_transcript (h : NoiseHandshake) (r : NoiseRole) :
    (deriveKey h r).transcript = h.transcript := rfl

@[simp] theorem deriveKey_peer (h : NoiseHandshake) (r : NoiseRole) :
    (deriveKey h r).peer = h.peerStaticOf r := rfl

@[simp] theorem deriveKey_role (h : NoiseHandshake) (r : NoiseRole) :
    (deriveKey h r).role = r := rfl

/-- Determinism of the derivation law. -/
theorem deriveKey_deterministic {h₁ h₂ : NoiseHandshake} {r₁ r₂ : NoiseRole}
    (hh : h₁ = h₂) (hr : r₁ = r₂) :
    deriveKey h₁ r₁ = deriveKey h₂ r₂ := by
  rw [hh, hr]

/-- Two sessions with the same handshake and role derive the same key. -/
theorem deriveKey_congr {h₁ h₂ : NoiseHandshake} (hh : h₁ = h₂) (r : NoiseRole) :
    deriveKey h₁ r = deriveKey h₂ r := by
  rw [hh]

/-- Distinct roles on the same handshake have distinct opaque key identities.
This is a model-side identity fact, not a cryptographic separation claim. -/
theorem deriveKey_id_initiator_ne_responder (h : NoiseHandshake) :
    (deriveKey h .initiator).id ≠ (deriveKey h .responder).id := by
  simp [deriveKey, roleCode]

/-- A local handshake view.  `role` is the endpoint's role; `sendKey` and
`recvKey` are the two directional keys. -/
structure NoiseSession where
  /-- The shared handshake record. -/
  handshake : NoiseHandshake
  /-- This endpoint's role. -/
  role : NoiseRole
  /-- The key used to authenticate outbound frames. -/
  sendKey : SessionKey
  /-- The key used to authenticate inbound frames. -/
  recvKey : SessionKey
deriving Repr, BEq

/-- The static key of the session peer.  This is the identity the transport
claims, and the value that must match `open_channel.funding_pubkey`. -/
def NoiseSession.peerStatic (s : NoiseSession) : PubKey :=
  s.handshake.peerStaticOf s.role

/-- This endpoint's own static key. -/
def NoiseSession.ownStatic (s : NoiseSession) : PubKey :=
  s.handshake.peerStaticOf (roleFlip s.role)

/-- **The explicit handshake-soundness assumption.**  The session keys are
exactly the deterministic derivation from the handshake and the session role.
This is the only handshake law the positive direction consumes; it does not
assert that the transcript was honestly produced, that the peer holds the
static secret, or that the keys are secret. -/
structure NoiseHandshakeSound (s : NoiseSession) : Prop where
  /-- The send key is derived from the handshake at the session role. -/
  sendKey_derived : s.sendKey = deriveKey s.handshake s.role
  /-- The receive key is derived from the handshake at the opposite role. -/
  recvKey_derived : s.recvKey = deriveKey s.handshake (roleFlip s.role)

/-- The peer static key is exactly the `peer` field of the derived send key. -/
theorem session_sendKey_peer (s : NoiseSession) (h : NoiseHandshakeSound s) :
    s.sendKey.peer = s.peerStatic := by
  rw [h.sendKey_derived]
  rfl

/-- The receive key's `peer` field is this endpoint's own static key, since the
opposite role derives it from the local static key.  This records the
directionality of the schedule and is not an attribution claim. -/
theorem session_recvKey_peer (s : NoiseSession) (h : NoiseHandshakeSound s) :
    s.recvKey.peer = s.ownStatic := by
  rw [h.recvKey_derived]
  rfl

/-- The two views of one handshake agree.  This is the structural content of a
completed `Noise_XK` transcript at the model level. -/
structure NoiseHandshakeAgreement (a b : NoiseHandshake) : Prop where
  /-- Both views see the same initiator static key. -/
  initiatorStatic_eq : a.initiatorStatic = b.initiatorStatic
  /-- Both views see the same responder static key. -/
  responderStatic_eq : a.responderStatic = b.responderStatic
  /-- Both views see the same initiator ephemeral key. -/
  initiatorEphemeral_eq : a.initiatorEphemeral = b.initiatorEphemeral
  /-- Both views see the same responder ephemeral key. -/
  responderEphemeral_eq : a.responderEphemeral = b.responderEphemeral
  /-- Both views see the same transcript. -/
  transcript_eq : a.transcript = b.transcript

/-- Agreement identifies the transcript. -/
theorem handshakeAgreement_transcript {a b : NoiseHandshake}
    (h : NoiseHandshakeAgreement a b) : a.transcript = b.transcript :=
  h.transcript_eq

/-- Agreement identifies the peer static key at either role. -/
theorem handshakeAgreement_peerStatic {a b : NoiseHandshake}
    (h : NoiseHandshakeAgreement a b) (r : NoiseRole) :
    a.peerStaticOf r = b.peerStaticOf r := by
  cases r
  · exact h.responderStatic_eq
  · exact h.initiatorStatic_eq

/-- Under agreement, the two directional derivations agree. -/
theorem deriveKey_eq_of_agreement {a b : NoiseHandshake}
    (h : NoiseHandshakeAgreement a b) (r : NoiseRole) :
    deriveKey a r = deriveKey b r := by
  cases r
  · simp [deriveKey, NoiseHandshake.peerStaticOf,
      h.transcript_eq, h.responderStatic_eq]
  · simp [deriveKey, NoiseHandshake.peerStaticOf,
      h.transcript_eq, h.initiatorStatic_eq]

/-! ## 2. Transport frames and the abstract AEAD interface -/

/-- The MAC field of a transport frame.  `keyId` and `peer` are model-side
identifiers that let the concrete instances distinguish keys; `tag` is the
opaque authentication tag.  Real Poly1305 tags are not modelled. -/
structure Mac where
  /-- Model identity of the MAC key. -/
  keyId : Nat
  /-- Model peer identity carried by this MAC instance. -/
  peer : PubKey
  /-- Opaque authentication tag value. -/
  tag : Nat
deriving Repr, BEq

/-- One BOLT 8 transport frame: session id, nonce counter, ciphertext, and MAC.
The plaintext is deliberately absent: this module reasons about delivery and
attribution, not about payload contents. -/
structure TransportFrame where
  /-- The session this frame belongs to. -/
  sessionId : Nat
  /-- The 64-bit nonce counter (as a `Nat` in the model). -/
  nonce : Nat
  /-- Opaque ciphertext bytes. -/
  ciphertext : ByteArray
  /-- The frame MAC. -/
  mac : Mac
deriving Repr, BEq

/-- The model tag function: nonce plus ciphertext length.  This is an opaque
toy function used only to make the finite counterexamples compute. -/
def tagOf (f : TransportFrame) : Nat :=
  f.nonce + f.ciphertext.size

/-- A model of the post-handshake AEAD interface.  `accept` is the acceptance
relation; `produced` is the provenance relation "some holder of this key could
have emitted this frame".  Neither is a real AEAD algorithm. -/
structure TransportCrypto where
  /-- Abstract frame acceptance. -/
  accept : SessionKey → TransportFrame → Prop
  /-- Abstract frame provenance. -/
  produced : SessionKey → TransportFrame → Prop

/-- The `AeadAccept` relation, exposed under the name used by the report. -/
abbrev AeadAccept (C : TransportCrypto) (k : SessionKey)
    (f : TransportFrame) : Prop :=
  C.accept k f

/-- **The explicit AEAD unforgeability law.**  Every accepted frame is one the
key's holder could have produced.  This is the model-level replacement for an
AEAD authenticity game; it is an assumption, not a theorem about ChaCha20-
Poly1305. -/
def AeadUnforgeable (C : TransportCrypto) : Prop :=
  ∀ (k : SessionKey) (f : TransportFrame),
    AeadAccept C k f → C.produced k f

/-- **The explicit key-binding law for acceptance.**  Two keys that accept the
same frame agree on the peer static key.  This is what a real AEAD's wrong-key
rejection supplies in the honest case; here it is isolated so the key
substitution counterexample can drop it. -/
def AeadKeyBinding (C : TransportCrypto) : Prop :=
  ∀ (k₁ k₂ : SessionKey) (f : TransportFrame),
    AeadAccept C k₁ f → AeadAccept C k₂ f → k₁.peer = k₂.peer

/-- The receiver's replay window.  `seen` is the list of accepted nonces. -/
structure ReceiveWindow where
  /-- Nonces already accepted on this session. -/
  seen : List Nat
deriving Repr, BEq

/-- **The freshness predicate.**  The frame nonce has not occurred in the
receiver's seen-nonce window. -/
def NonceFresh (w : ReceiveWindow) (f : TransportFrame) : Prop :=
  f.nonce ∉ w.seen

/-! ## 3. The receiver window, replay, and nonce freshness -/

/-- Accept one frame and advance the replay window.  Acceptance requires both
`AeadAccept` and `NonceFresh`.  The rule is propositional, so no decidability
instance for the abstract acceptance relation is needed. -/
def recv (C : TransportCrypto) (w : ReceiveWindow) (k : SessionKey)
    (f : TransportFrame) : Option ReceiveWindow :=
  if _h : AeadAccept C k f ∧ NonceFresh w f then
    some { seen := f.nonce :: w.seen }
  else
    none

/-- A successful receive implies AEAD acceptance. -/
theorem recv_requires_accept {C : TransportCrypto} {w : ReceiveWindow}
    {k : SessionKey} {f : TransportFrame} {w' : ReceiveWindow}
    (h : recv C w k f = some w') :
    AeadAccept C k f := by
  unfold recv at h
  split at h
  · rename_i hg
    exact hg.1
  · cases h

/-- A successful receive implies nonce freshness. -/
theorem recv_requires_fresh {C : TransportCrypto} {w : ReceiveWindow}
    {k : SessionKey} {f : TransportFrame} {w' : ReceiveWindow}
    (h : recv C w k f = some w') :
    NonceFresh w f := by
  unfold recv at h
  split at h
  · rename_i hg
    exact hg.2
  · cases h

/-- A successful receive records the frame nonce in the new window. -/
theorem recv_seen {C : TransportCrypto} {w : ReceiveWindow}
    {k : SessionKey} {f : TransportFrame} {w' : ReceiveWindow}
    (h : recv C w k f = some w') :
    f.nonce ∈ w'.seen := by
  unfold recv at h
  split at h
  · rename_i _hg
    cases h
    simp
  · cases h

/-- A non-fresh frame is rejected, independently of acceptance. -/
theorem recv_none_of_not_fresh (C : TransportCrypto) (w : ReceiveWindow)
    (k : SessionKey) (f : TransportFrame) (h : ¬ NonceFresh w f) :
    recv C w k f = none := by
  unfold recv
  rw [dite_eq_right]
  intro hg
  exact h hg.2

/-- **Replay is rejected with freshness.**  Once a frame has been accepted, the
same frame is rejected by the next receive. -/
theorem replay_rejected_with_freshness {C : TransportCrypto} {w : ReceiveWindow}
    {k : SessionKey} {f : TransportFrame} {w' : ReceiveWindow}
    (h : recv C w k f = some w') :
    recv C w' k f = none := by
  apply recv_none_of_not_fresh
  intro hfresh
  exact hfresh (recv_seen h)

/-- Adding the current nonce to the window makes the frame non-fresh. -/
theorem nonceFresh_cons_self_false (w : ReceiveWindow) (f : TransportFrame) :
    ¬ NonceFresh { seen := f.nonce :: w.seen } f := by
  simp [NonceFresh]

/-- Freshness is preserved when a *different* nonce is added to the window. -/
theorem nonceFresh_cons_of_ne {w : ReceiveWindow} {f g : TransportFrame}
    (hne : g.nonce ≠ f.nonce) (hf : NonceFresh w f) :
    NonceFresh { seen := g.nonce :: w.seen } f := by
  intro hmem
  rcases List.mem_cons.mp hmem with heq | hmem
  · exact hne heq.symm
  · exact hf hmem

/-- **The freshness-free receiver used for the replay counterexample.**  It
checks only `AeadAccept` and leaves the window unchanged. -/
def recvLoose (C : TransportCrypto) (w : ReceiveWindow) (k : SessionKey)
    (f : TransportFrame) : Option ReceiveWindow :=
  if _h : AeadAccept C k f then some w else none

/-- The loose receiver accepts any accepted frame and returns the unchanged
window. -/
theorem recvLoose_accept {C : TransportCrypto} {w : ReceiveWindow}
    {k : SessionKey} {f : TransportFrame} (h : AeadAccept C k f) :
    recvLoose C w k f = some w := by
  unfold recvLoose
  exact dite_eq_left h

/-! ## 4. Accepted frames are bound to the session peer static key -/

/-- Under `AeadUnforgeable`, acceptance yields provenance under the same key. -/
theorem accepted_implies_produced (C : TransportCrypto)
    (hU : AeadUnforgeable C) (k : SessionKey) (f : TransportFrame)
    (hacc : AeadAccept C k f) :
    C.produced k f :=
  hU k f hacc

/-- **The central transport binding.**  If the session is sound and the frame is
accepted under its send key, then the frame was produced under that key, and
that key's peer field is the session peer static key.  This is the model-level
answer to "what does an authenticated frame bind?": it binds the key, and the
key binds the peer static key by the derivation law. -/
theorem accepted_frame_bound_to_peer (C : TransportCrypto)
    (hU : AeadUnforgeable C) (s : NoiseSession) (hS : NoiseHandshakeSound s)
    (f : TransportFrame) (hacc : AeadAccept C s.sendKey f) :
    C.produced s.sendKey f ∧ s.sendKey.peer = s.peerStatic :=
  ⟨accepted_implies_produced C hU s.sendKey f hacc,
    session_sendKey_peer s hS⟩

/-- Under the additional `AeadKeyBinding` law, *any* key that accepts the frame
has the session peer static key, not only the session's own send key. -/
theorem accepted_frame_peer_unique (C : TransportCrypto)
    (hB : AeadKeyBinding C) (s : NoiseSession) (hS : NoiseHandshakeSound s)
    (f : TransportFrame) (hacc : AeadAccept C s.sendKey f) :
    ∀ k : SessionKey, AeadAccept C k f → k.peer = s.peerStatic := by
  intro k hk
  exact (hB k s.sendKey f hk hacc).trans (session_sendKey_peer s hS)

/-- Consequently a key with a different peer cannot accept the same frame under
`AeadKeyBinding`.  This is the abstract wrong-peer rejection. -/
theorem accepted_frame_other_peer_rejected (C : TransportCrypto)
    (hB : AeadKeyBinding C) (s : NoiseSession) (hS : NoiseHandshakeSound s)
    (f : TransportFrame) (hacc : AeadAccept C s.sendKey f) {k : SessionKey}
    (hne : k.peer ≠ s.peerStatic) :
    ¬ AeadAccept C k f := by
  intro hk
  exact hne (accepted_frame_peer_unique C hB s hS f hacc k hk)

/-! ## 5. Concrete finite crypto instances -/

/-- Seal a frame under a key.  `mac.peer` is filled from the key, so the strict
instance can reject a substituted peer. -/
def sealFrame (k : SessionKey) (sessionId nonce : Nat) (ct : ByteArray) :
    TransportFrame where
  sessionId := sessionId
  nonce := nonce
  ciphertext := ct
  mac := { keyId := k.id, peer := k.peer, tag := nonce + ct.size }

/-- The loose acceptance relation: it checks the key identity and tag but
deliberately ignores the peer static key. -/
def looseAccept (k : SessionKey) (f : TransportFrame) : Prop :=
  f.mac.keyId = k.id ∧ f.mac.tag = tagOf f

/-- The strict acceptance relation: it also checks the peer static key. -/
def strictAccept (k : SessionKey) (f : TransportFrame) : Prop :=
  f.mac.keyId = k.id ∧ f.mac.peer = k.peer ∧ f.mac.tag = tagOf f

/-- A crypto model that does not bind the peer key. -/
def looseCrypto : TransportCrypto where
  accept := looseAccept
  produced := looseAccept

/-- A crypto model that binds the peer key in the MAC. -/
def strictCrypto : TransportCrypto where
  accept := strictAccept
  produced := strictAccept

/-- Sealing under a key is accepted by the strict model. -/
theorem strictCrypto_accept_seal (k : SessionKey) (sessionId nonce : Nat)
    (ct : ByteArray) :
    AeadAccept strictCrypto k (sealFrame k sessionId nonce ct) := by
  simp [AeadAccept, strictCrypto, strictAccept, sealFrame, tagOf]

/-- Sealing under a key is accepted by the loose model. -/
theorem looseCrypto_accept_seal (k : SessionKey) (sessionId nonce : Nat)
    (ct : ByteArray) :
    AeadAccept looseCrypto k (sealFrame k sessionId nonce ct) := by
  simp [AeadAccept, looseCrypto, looseAccept, sealFrame, tagOf]

/-- The strict model satisfies the explicit unforgeability law.  This is a
finite model fact: `produced` is definitionally `accept`, so it says nothing
about a real AEAD. -/
theorem strictCrypto_unforgeable : AeadUnforgeable strictCrypto :=
  fun _ _ h => h

/-- The loose model also satisfies unforgeability; its failure is key binding,
not provenance. -/
theorem looseCrypto_unforgeable : AeadUnforgeable looseCrypto :=
  fun _ _ h => h

/-- The strict model satisfies `AeadKeyBinding`. -/
theorem strictCrypto_keyBinding : AeadKeyBinding strictCrypto := by
  intro k₁ k₂ f h₁ h₂
  exact h₁.2.1.symm.trans h₂.2.1

/-- The strict model rejects a substituted peer key. -/
theorem strictCrypto_wrong_peer_rejected {k₁ k₂ : SessionKey}
    {f : TransportFrame} (hne : k₁.peer ≠ k₂.peer)
    (h : AeadAccept strictCrypto k₁ f) :
    ¬ AeadAccept strictCrypto k₂ f := by
  intro h₂
  exact hne (h.2.1.symm.trans h₂.2.1)

/-- The loose model rejects a frame under a different key identity. -/
theorem looseCrypto_wrong_key_rejected {k₁ k₂ : SessionKey}
    {f : TransportFrame} (hne : k₁.id ≠ k₂.id)
    (h : AeadAccept looseCrypto k₁ f) :
    ¬ AeadAccept looseCrypto k₂ f := by
  intro h₂
  exact hne (h.1.symm.trans h₂.1)

/-! ## 6. Composition with `TransportAuthTargets` -/

/-- An `open_channel` payload delivered over a Noise session.  The wire record is
unchanged; the peer identity comes only from the handshake. -/
structure NoiseDelivery where
  /-- The receiving session. -/
  session : NoiseSession
  /-- The unchanged type-32 payload. -/
  wire : OpenChannelWire
deriving Repr, BEq

/-- The `TransportAuthTargets` session induced by a Noise session.  The session
id is the transcript length and the established flag is set, because the
positive layer reasons about frames accepted *after* a completed handshake. -/
def NoiseDelivery.toTransportSession (d : NoiseDelivery) : TransportSession where
  sessionId := d.session.handshake.transcript.size
  peerKey := d.session.peerStatic
  established := true

/-- The `TransportAuthTargets` delivery induced by a Noise delivery. -/
def NoiseDelivery.toAuthenticatedDelivery (d : NoiseDelivery) :
    AuthenticatedDelivery where
  session := d.toTransportSession
  wire := d.wire

@[simp] theorem toAuthenticatedDelivery_session (d : NoiseDelivery) :
    d.toAuthenticatedDelivery.session = d.toTransportSession := rfl

@[simp] theorem toAuthenticatedDelivery_wire (d : NoiseDelivery) :
    d.toAuthenticatedDelivery.wire = d.wire := rfl

/-- The induced session is authenticated by construction.  This records the
modelling boundary: `TransportAuthenticated` is a flag, not a proof that a real
handshake occurred. -/
theorem toAuthenticatedDelivery_authenticated (d : NoiseDelivery) :
    TransportAuthenticated d.toAuthenticatedDelivery := rfl

/-- The `TransportAuthTargets` key-binding law is exactly equality of the Noise
session peer static key and the advertised funding key. -/
theorem sessionKeyBinding_iff_peerStatic_eq (d : NoiseDelivery) :
    SessionKeyBinding d.toAuthenticatedDelivery ↔
      d.session.peerStatic = d.wire.fundingPubKey :=
  Iff.rfl

/-- The explicit peer/advertisement equality yields `SessionKeyBinding`. -/
theorem peerStatic_eq_funding_yields_sessionKeyBinding (d : NoiseDelivery)
    (hadv : d.session.peerStatic = d.wire.fundingPubKey) :
    SessionKeyBinding d.toAuthenticatedDelivery :=
  (sessionKeyBinding_iff_peerStatic_eq d).2 hadv

/-- Conversely, `SessionKeyBinding` is exactly the peer/advertisement equality.
No cryptographic conclusion is hidden in the bridge. -/
theorem sessionKeyBinding_yields_peerStatic_eq (d : NoiseDelivery)
    (h : SessionKeyBinding d.toAuthenticatedDelivery) :
    d.session.peerStatic = d.wire.fundingPubKey :=
  (sessionKeyBinding_iff_peerStatic_eq d).1 h

/-- **Accepted frame -> `SessionKeyBinding`.**  Soundness, unforgeability, and
the explicit peer/advertisement equality yield the wave-10 key-binding law. -/
theorem accepted_frame_yields_sessionKeyBinding (C : TransportCrypto)
    (hU : AeadUnforgeable C) (d : NoiseDelivery)
    (_hS : NoiseHandshakeSound d.session) (f : TransportFrame)
    (hacc : AeadAccept C d.session.sendKey f)
    (hadv : d.session.peerStatic = d.wire.fundingPubKey) :
    C.produced d.session.sendKey f ∧
      SessionKeyBinding d.toAuthenticatedDelivery :=
  ⟨accepted_implies_produced C hU d.session.sendKey f hacc,
    peerStatic_eq_funding_yields_sessionKeyBinding d hadv⟩

/-- **Accepted frame -> attributed delivery.**  The bridge to the wave-9/10
`EnvelopeAttributed` predicate, through the unchanged
`TransportAuthTargets` theorem. -/
theorem accepted_frame_attributed_delivery (C : TransportCrypto)
    (hU : AeadUnforgeable C) (d : NoiseDelivery)
    (hS : NoiseHandshakeSound d.session) (f : TransportFrame)
    (hacc : AeadAccept C d.session.sendKey f)
    (hadv : d.session.peerStatic = d.wire.fundingPubKey) :
    C.produced d.session.sendKey f ∧
      SessionKeyBinding d.toAuthenticatedDelivery ∧
      EnvelopeAttributed d.toAuthenticatedDelivery.envelope := by
  obtain ⟨hprod, hbind⟩ :=
    accepted_frame_yields_sessionKeyBinding C hU d hS f hacc hadv
  exact ⟨hprod, hbind,
    TransportAuthTargets.envelopeAttributed_of_sessionKeyBinding
      d.toAuthenticatedDelivery hbind⟩

/-- **Accepted frame -> routed `funding_created`.**  The attributed delivery
composes with the wave-9 route and the unchanged accept/funding handshake. -/
theorem accepted_frame_reaches_fundingCreated (C : TransportCrypto)
    (hU : AeadUnforgeable C) (d : NoiseDelivery)
    (hS : NoiseHandshakeSound d.session) (f : TransportFrame)
    (hacc : AeadAccept C d.session.sendKey f)
    (hadv : d.session.peerStatic = d.wire.fundingPubKey) (a : AcceptChannel) :
    EnvelopeAttributed d.toAuthenticatedDelivery.envelope ∧
      OpenRouteReachable
        (afterOpenRoute d.toAuthenticatedDelivery.envelope) ∧
      ∃ s1 s2 : HandshakeState,
        handshakeStepRecvAccept
            (afterOpenRoute d.toAuthenticatedDelivery.envelope).peer.handshake
            a = some s1 ∧
          handshakeStep s1 .sendFundingCreated = some s2 ∧
          s1.acceptChannel? = some a ∧
          s2.acceptReceived = true := by
  have hbind :=
    (accepted_frame_yields_sessionKeyBinding C hU d hS f hacc hadv).2
  exact TransportAuthTargets.authenticated_delivery_reaches_fundingCreated
    d.toAuthenticatedDelivery a
    (toAuthenticatedDelivery_authenticated d) hbind

/-- **Accepted frame -> funding construction.**  The same route reaches a
reachable `FundingPhase` and the hash-linked P2WSH output. -/
theorem accepted_frame_reaches_funding (C : TransportCrypto)
    (hU : AeadUnforgeable C) (d : NoiseDelivery)
    (hS : NoiseHandshakeSound d.session) (f : TransportFrame)
    (hacc : AeadAccept C d.session.sendKey f)
    (hadv : d.session.peerStatic = d.wire.fundingPubKey)
    (a : AcceptChannel) (H : ByteArray → ByteArray) :
    EnvelopeAttributed d.toAuthenticatedDelivery.envelope ∧
      OpenRouteReachable
        (afterOpenRoute d.toAuthenticatedDelivery.envelope) ∧
      FundingReachable (acceptorPhaseAfter d.wire a) ∧
      FundingScriptHashLinked H (d.wire.toFundingParams H a) := by
  have hbind :=
    (accepted_frame_yields_sessionKeyBinding C hU d hS f hacc hadv).2
  obtain ⟨h1, h2, h3, h4, _h5⟩ :=
    TransportAuthTargets.authenticated_open_reaches_funding
      d.toAuthenticatedDelivery a H
      (toAuthenticatedDelivery_authenticated d) hbind
  exact ⟨h1, h2, h3, h4⟩

/-- **Accepted frame -> key in the funding script.**  The session peer static
key is the constructed local funding key and occurs in the witness script. -/
theorem accepted_frame_key_in_funding_script (C : TransportCrypto)
    (hU : AeadUnforgeable C) (d : NoiseDelivery)
    (hS : NoiseHandshakeSound d.session) (f : TransportFrame)
    (hacc : AeadAccept C d.session.sendKey f)
    (hadv : d.session.peerStatic = d.wire.fundingPubKey)
    (a : AcceptChannel) (H : ByteArray → ByteArray) :
    d.session.peerStatic = (d.wire.toFundingNegotiation a).localFundingKey ∧
      KeyInScript (d.wire.toFundingParams H a).witnessScript.bytes
        d.session.peerStatic := by
  have hbind :=
    (accepted_frame_yields_sessionKeyBinding C hU d hS f hacc hadv).2
  exact TransportAuthTargets.authenticated_key_in_funding_script
    d.toAuthenticatedDelivery a H
    (toAuthenticatedDelivery_authenticated d) hbind

/-! ## 7. Concrete keys and the finite counterexamples -/

private def bytesOf (n : Nat) (b : UInt8) : ByteArray :=
  ByteArray.mk (List.replicate n b).toArray

private theorem bytesOf_size (n : Nat) (b : UInt8) :
    (bytesOf n b).size = n := by
  simp [bytesOf, ByteArray.size]

private def pub33 (b : UInt8) : PubKey := ⟨bytesOf 33 b⟩

private theorem pub33_valid (b : UInt8) : (pub33 b).Valid := by
  simp [PubKey.Valid, pub33, bytesOf_size]

private theorem pub33_zero_ne_one : pub33 0 ≠ pub33 1 := by
  intro h
  have hb : (pub33 0).bytes = (pub33 1).bytes := congrArg PubKey.bytes h
  have h0 : (pub33 0).bytes[0]? = some (0 : UInt8) := by
    simp only [pub33, bytesOf]
    decide
  have h1 : (pub33 1).bytes[0]? = some (1 : UInt8) := by
    simp only [pub33, bytesOf]
    decide
  rw [hb] at h0
  rw [h0] at h1
  exact absurd (Option.some.inj h1) (by decide)

/-- A concrete handshake transcript. -/
private def demoTranscript : ByteArray :=
  ByteArray.mk (List.replicate 32 (7 : UInt8)).toArray

/-- A concrete `Noise_XK`-shaped handshake whose peer static key is
`pub33 0`. -/
private def demoHandshake : NoiseHandshake where
  pattern := HandshakePattern.XK
  initiatorStatic := pub33 0
  responderStatic := pub33 0
  initiatorEphemeral := pub33 1
  responderEphemeral := pub33 2
  transcript := demoTranscript

/-- The initiator session derived from `demoHandshake`. -/
private def demoSession : NoiseSession where
  handshake := demoHandshake
  role := .initiator
  sendKey := deriveKey demoHandshake .initiator
  recvKey := deriveKey demoHandshake .responder

private theorem demoSession_sound : NoiseHandshakeSound demoSession :=
  ⟨rfl, rfl⟩

/-- The concrete frame sealed under the demo send key at nonce `0`. -/
private def demoFrame : TransportFrame :=
  sealFrame demoSession.sendKey 17 0 ByteArray.empty

/-- A concrete wire record with the given funding key.  The other fields are
neutral; only `fundingPubKey` matters here. -/
private def demoWire (k : PubKey) : OpenChannelWire where
  temporaryChannelId := ChannelId.zero
  fundingSatoshis := 0
  pushMsat := ⟨0⟩
  dustLimitSatoshis := 0
  maxHtlcValueInFlightMsat := 0
  channelReserveSatoshis := 0
  htlcMinimumMsat := 0
  feeratePerKw := 0
  toSelfDelay := 0
  maxAcceptedHtlcs := 0
  fundingPubKey := k
  revocationBasepoint := k
  paymentBasepoint := k
  delayedPaymentBasepoint := k
  htlcBasepoint := k
  firstPerCommitmentPoint := k
  channelFlags := 0
  shutdownScriptpubkey := ByteArray.empty

private theorem demoWire_wellFormed {k : PubKey} (hk : k.Valid) :
    wellFormed (.openChannel (demoWire k)) := by
  apply wellFormed_openChannel_of
  · exact ChannelId.zero_valid
  · intro p hp
    have hp' : p = k := by
      simpa [demoWire, pubKeys] using hp
    rw [hp']
    exact hk

/-- The concrete attributed delivery: the handshake peer static key equals the
advertised funding key `pub33 0`. -/
def demoDelivery : NoiseDelivery where
  session := demoSession
  wire := demoWire (pub33 0)

/-- The concrete unattributed delivery: the same wire, but the handshake peer
static key is `pub33 1`. -/
private def demoUnattributedHandshake : NoiseHandshake :=
  { demoHandshake with responderStatic := pub33 1 }

private def demoUnattributedSession : NoiseSession where
  handshake := demoUnattributedHandshake
  role := .initiator
  sendKey := deriveKey demoUnattributedHandshake .initiator
  recvKey := deriveKey demoUnattributedHandshake .responder

private theorem demoUnattributedSession_sound :
    NoiseHandshakeSound demoUnattributedSession :=
  ⟨rfl, rfl⟩

def demoUnattributedDelivery : NoiseDelivery where
  session := demoUnattributedSession
  wire := demoWire (pub33 0)

private def demoUnattributedFrame : TransportFrame :=
  sealFrame demoUnattributedSession.sendKey 18 0 ByteArray.empty

private theorem demoUnattributedDelivery_not_bound :
    ¬ SessionKeyBinding demoUnattributedDelivery.toAuthenticatedDelivery := by
  intro hbind
  have hkey : pub33 1 = pub33 0 := by
    simpa [SessionKeyBinding, demoUnattributedDelivery,
      NoiseDelivery.toAuthenticatedDelivery, NoiseDelivery.toTransportSession,
      demoUnattributedSession, demoUnattributedHandshake, demoHandshake,
      NoiseSession.peerStatic, NoiseHandshake.peerStaticOf, demoWire] using hbind
  exact pub33_zero_ne_one hkey.symm

private theorem demoDelivery_bound :
    SessionKeyBinding demoDelivery.toAuthenticatedDelivery := rfl

/-- The first substituted key: identity `7`, peer `pub33 0`. -/
private def substKeyA : SessionKey where
  id := 7
  material := ByteArray.empty
  transcript := ByteArray.empty
  peer := pub33 0
  role := .initiator

/-- The second substituted key: the same identity and tag, a different peer. -/
private def substKeyB : SessionKey :=
  { substKeyA with peer := pub33 1 }

/-- The frame accepted by both substituted keys in the loose model. -/
private def substFrame : TransportFrame where
  sessionId := 7
  nonce := 0
  ciphertext := ByteArray.empty
  mac := { keyId := 7, peer := pub33 0, tag := 0 }

private theorem substKeyA_accepts :
    AeadAccept looseCrypto substKeyA substFrame := by
  simp [AeadAccept, looseCrypto, looseAccept, substKeyA, substFrame, tagOf]

private theorem substKeyB_accepts :
    AeadAccept looseCrypto substKeyB substFrame := by
  simp [AeadAccept, looseCrypto, looseAccept, substKeyA, substKeyB,
    substFrame, tagOf]

private theorem substKey_peer_ne : substKeyA.peer ≠ substKeyB.peer := by
  simpa [substKeyA, substKeyB] using pub33_zero_ne_one

/-- **Key substitution without peer binding.**  Two `SessionKey`s with the same
opaque identity and different peer keys both accept the same frame in the loose
model.  This is the mechanistic reason `AeadKeyBinding` cannot be dropped from
`accepted_frame_peer_unique`. -/
theorem key_substitution_without_peer_binding :
    ∃ (C : TransportCrypto) (k₁ k₂ : SessionKey) (f : TransportFrame),
      AeadAccept C k₁ f ∧ AeadAccept C k₂ f ∧ k₁.peer ≠ k₂.peer :=
  ⟨looseCrypto, substKeyA, substKeyB, substFrame,
    substKeyA_accepts, substKeyB_accepts, substKey_peer_ne⟩

/-- The loose model does **not** satisfy the explicit key-binding law. -/
theorem looseCrypto_not_keyBinding : ¬ AeadKeyBinding looseCrypto := by
  intro hB
  exact substKey_peer_ne
    (hB substKeyA substKeyB substFrame substKeyA_accepts substKeyB_accepts)

/-- **Replay without nonce freshness.**  The loose receiver accepts the same
frame twice and returns the unchanged window each time. -/
theorem replay_accepted_without_nonce_freshness :
    ∃ (C : TransportCrypto) (w : ReceiveWindow) (k : SessionKey)
      (f : TransportFrame) (w₁ w₂ : ReceiveWindow),
      recvLoose C w k f = some w₁ ∧ recvLoose C w₁ k f = some w₂ := by
  let k : SessionKey :=
    { id := 9
      material := ByteArray.empty
      transcript := ByteArray.empty
      peer := pub33 0
      role := .initiator }
  let f : TransportFrame := sealFrame k 19 0 ByteArray.empty
  have hacc : AeadAccept looseCrypto k f :=
    looseCrypto_accept_seal k 19 0 ByteArray.empty
  refine ⟨looseCrypto, ⟨[]⟩, k, f, ⟨[]⟩, ⟨[]⟩, ?_, ?_⟩
  · exact recvLoose_accept hacc
  · exact recvLoose_accept hacc

/-! ## 8. The payload-only boundary -/

/-- Acceptance under a sound session does not by itself yield
`SessionKeyBinding`: the explicit peer/advertisement equality is still needed. -/
theorem acceptance_not_attribution :
    ∃ (C : TransportCrypto) (d : NoiseDelivery) (f : TransportFrame),
      AeadUnforgeable C ∧ NoiseHandshakeSound d.session ∧
        AeadAccept C d.session.sendKey f ∧
        ¬ SessionKeyBinding d.toAuthenticatedDelivery := by
  refine ⟨strictCrypto, demoUnattributedDelivery, demoUnattributedFrame,
    strictCrypto_unforgeable, demoUnattributedSession_sound, ?_, ?_⟩
  · exact strictCrypto_accept_seal demoUnattributedSession.sendKey
      18 0 ByteArray.empty
  · exact demoUnattributedDelivery_not_bound

/-- The same `open_channel` payload can arrive over two sound Noise sessions with
different peer static keys; only one yields `SessionKeyBinding`.  This preserves
the exact `TransportAuthTargets.transport_auth_not_from_wire` boundary. -/
theorem noise_does_not_authenticate_payload :
    ∃ d₁ d₂ : NoiseDelivery,
      d₁.wire = d₂.wire ∧
        NoiseHandshakeSound d₁.session ∧
        NoiseHandshakeSound d₂.session ∧
        SessionKeyBinding d₁.toAuthenticatedDelivery ∧
        ¬ SessionKeyBinding d₂.toAuthenticatedDelivery := by
  refine ⟨demoDelivery, demoUnattributedDelivery, rfl,
    demoSession_sound, demoUnattributedSession_sound, ?_, ?_⟩
  · exact demoDelivery_bound
  · exact demoUnattributedDelivery_not_bound

/-- **No peer function of the wire.**  There is no function from the type-32
payload to the Noise peer static key that is correct for every delivery. -/
theorem noise_peer_not_from_wire :
    ¬ ∃ f : OpenChannelWire → PubKey,
        ∀ d : NoiseDelivery, f d.wire = d.session.peerStatic := by
  rintro ⟨f, hf⟩
  have h₁ := hf demoDelivery
  have h₂ := hf demoUnattributedDelivery
  have hw : demoDelivery.wire = demoUnattributedDelivery.wire := rfl
  rw [hw] at h₁
  have hpeers : demoDelivery.session.peerStatic =
      demoUnattributedDelivery.session.peerStatic := h₁.symm.trans h₂
  have hbad : pub33 0 = pub33 1 := by
    simpa [demoDelivery, demoUnattributedDelivery, demoSession,
      demoUnattributedSession, demoUnattributedHandshake, demoHandshake,
      NoiseSession.peerStatic, NoiseHandshake.peerStaticOf] using hpeers
  exact pub33_zero_ne_one hbad

/-- **No attribution predicate of the wire.**  No function of the payload alone
can decide `SessionKeyBinding` for all delivered openings. -/
theorem no_wire_session_binding_function :
    ¬ ∃ f : OpenChannelWire → Prop,
        ∀ d : NoiseDelivery,
          f d.wire ↔ SessionKeyBinding d.toAuthenticatedDelivery := by
  rintro ⟨f, hf⟩
  have h₁ := hf demoDelivery
  have h₂ := hf demoUnattributedDelivery
  have hw : demoDelivery.wire = demoUnattributedDelivery.wire := rfl
  have hfA : f demoUnattributedDelivery.wire := by
    rw [← hw]
    exact h₁.2 demoDelivery_bound
  exact demoUnattributedDelivery_not_bound (h₂.1 hfA)

/-- The opening payload carries no signature, so even an accepted frame gives no
proof of key ownership. -/
theorem accepted_frame_wire_carries_no_signature (d : NoiseDelivery) :
    signatures (.openChannel d.wire) = [] :=
  wire_carries_no_signature d.wire

/-- An accepted frame over an authenticated session still advertises an
arbitrary valid funding key: `SessionKeyBinding` remains a separate hypothesis.
This is the key-ownership boundary, not a consequence of AEAD acceptance. -/
theorem accepted_frame_advertised_key_independent (d : NoiseDelivery)
    {k : PubKey} (hk : k.Valid) :
    ∃ d' : NoiseDelivery,
      d'.session = d.session ∧ d'.wire.fundingPubKey = k ∧
        wellFormed (.openChannel d'.wire) :=
  ⟨{ d with wire := demoWire k }, rfl, rfl, demoWire_wellFormed hk⟩

/-! ## 9. Non-vacuity -/

theorem concrete_delivery_authenticated :
    TransportAuthenticated demoDelivery.toAuthenticatedDelivery := rfl

theorem concrete_delivery_bound :
    SessionKeyBinding demoDelivery.toAuthenticatedDelivery := rfl

theorem concrete_frame_accepted :
    AeadAccept strictCrypto demoSession.sendKey demoFrame := by
  simpa [demoFrame] using
    strictCrypto_accept_seal demoSession.sendKey 17 0 ByteArray.empty

theorem concrete_frame_fresh :
    NonceFresh { seen := [] } demoFrame := by
  simp [NonceFresh, demoFrame, sealFrame]

/-- The concrete frame is bound to the demo peer static key. -/
theorem concrete_frame_peer_bound :
    strictCrypto.produced demoSession.sendKey demoFrame ∧
      demoSession.sendKey.peer = demoSession.peerStatic :=
  accepted_frame_bound_to_peer strictCrypto strictCrypto_unforgeable
    demoSession demoSession_sound demoFrame concrete_frame_accepted

/-- The concrete delivery is attributed through the `TransportAuthTargets`
bridge. -/
theorem concrete_delivery_attributed :
    EnvelopeAttributed demoDelivery.toAuthenticatedDelivery.envelope :=
  TransportAuthTargets.envelopeAttributed_of_sessionKeyBinding
    demoDelivery.toAuthenticatedDelivery concrete_delivery_bound

/-- **Non-vacuity of the Noise transport layer.**  There are a concrete crypto
model satisfying both explicit acceptance laws, a concrete sound handshake and
session, an accepted fresh frame, and a delivery that is key-bound and
attributed. -/
theorem noise_transport_nonvacuous :
    ∃ (C : TransportCrypto) (d : NoiseDelivery) (f : TransportFrame),
      AeadUnforgeable C ∧ AeadKeyBinding C ∧
        NoiseHandshakeSound d.session ∧ AeadAccept C d.session.sendKey f ∧
        NonceFresh { seen := [] } f ∧
        SessionKeyBinding d.toAuthenticatedDelivery ∧
        EnvelopeAttributed d.toAuthenticatedDelivery.envelope := by
  refine ⟨strictCrypto, demoDelivery, demoFrame, strictCrypto_unforgeable,
    strictCrypto_keyBinding, demoSession_sound, concrete_frame_accepted,
    concrete_frame_fresh, concrete_delivery_bound, concrete_delivery_attributed⟩

/-- **Non-vacuity of the full route.**  The concrete accepted delivery reaches
`funding_created` and the hash-linked funding construction. -/
theorem concrete_accepted_frame_route (a : AcceptChannel)
    (H : ByteArray → ByteArray) :
    ∃ (C : TransportCrypto) (d : NoiseDelivery) (f : TransportFrame),
      AeadUnforgeable C ∧ NoiseHandshakeSound d.session ∧
        AeadAccept C d.session.sendKey f ∧
        EnvelopeAttributed d.toAuthenticatedDelivery.envelope ∧
        OpenRouteReachable (afterOpenRoute d.toAuthenticatedDelivery.envelope) ∧
        FundingReachable (acceptorPhaseAfter d.wire a) ∧
        FundingScriptHashLinked H (d.wire.toFundingParams H a) := by
  have hacc := concrete_frame_accepted
  have hbind :=
    (accepted_frame_yields_sessionKeyBinding strictCrypto
      strictCrypto_unforgeable demoDelivery demoSession_sound demoFrame hacc rfl).2
  refine ⟨strictCrypto, demoDelivery, demoFrame, strictCrypto_unforgeable,
    demoSession_sound, hacc, ?_, ?_, ?_, ?_⟩
  · exact TransportAuthTargets.envelopeAttributed_of_sessionKeyBinding
      demoDelivery.toAuthenticatedDelivery hbind
  · exact (openRoute_initial_to_fundingCreated
      demoDelivery.toAuthenticatedDelivery.envelope a).1
  · exact acceptorPhaseAfter_reachable demoDelivery.wire a
  · exact demoDelivery.wire.toFundingParams_hash_linked H a

/-! ## 10. Summary -/

/-- Bundled reading of the wave-11 Noise transport layer:

1. session keys are derived from the handshake and carry the peer static key;
2. accepted frames are produced under the session key and bound to the peer;
3. peer/advertisement equality yields `SessionKeyBinding` and attribution;
4. the attributed delivery reaches `funding_created` and the funding output;
5. without nonce freshness the same frame is accepted twice;
6. without peer key binding a substituted peer key is accepted;
7. the wire alone determines neither the peer key nor attribution. -/
theorem noise_transport_summary :
    (∀ (C : TransportCrypto) (s : NoiseSession),
        AeadUnforgeable C → NoiseHandshakeSound s →
        ∀ f : TransportFrame, AeadAccept C s.sendKey f →
          C.produced s.sendKey f ∧ s.sendKey.peer = s.peerStatic) ∧
      (∀ (C : TransportCrypto) (d : NoiseDelivery),
        AeadUnforgeable C → NoiseHandshakeSound d.session →
        d.session.peerStatic = d.wire.fundingPubKey →
        ∀ f : TransportFrame, AeadAccept C d.session.sendKey f →
          SessionKeyBinding d.toAuthenticatedDelivery ∧
            EnvelopeAttributed d.toAuthenticatedDelivery.envelope) ∧
      (∃ (C : TransportCrypto) (w : ReceiveWindow) (k : SessionKey)
          (f : TransportFrame) (w₁ w₂ : ReceiveWindow),
        recvLoose C w k f = some w₁ ∧ recvLoose C w₁ k f = some w₂) ∧
      (∃ (C : TransportCrypto) (k₁ k₂ : SessionKey) (f : TransportFrame),
        AeadAccept C k₁ f ∧ AeadAccept C k₂ f ∧ k₁.peer ≠ k₂.peer) ∧
      (¬ ∃ f : OpenChannelWire → PubKey,
        ∀ d : NoiseDelivery, f d.wire = d.session.peerStatic) ∧
      (∀ d : NoiseDelivery, signatures (.openChannel d.wire) = []) := by
  refine ⟨?_, ?_, replay_accepted_without_nonce_freshness,
    key_substitution_without_peer_binding, noise_peer_not_from_wire,
    accepted_frame_wire_carries_no_signature⟩
  · intro C s hU hS f hacc
    exact accepted_frame_bound_to_peer C hU s hS f hacc
  · intro C d hU hS hadv f hacc
    obtain ⟨-, hbind, hattr⟩ :=
      accepted_frame_attributed_delivery C hU d hS f hacc hadv
    exact ⟨hbind, hattr⟩

end

end LnLean.Proofs.Protocol.NoiseTransportTargets
