# S11-L1-NOISE-AUTH — model-level BOLT 8/Noise transport binding

**Lane:** `S11-L1-NOISE-AUTH`
**Issue:** `L1-03` (transport authentication / C3 / `SessionKeyBinding`)
**Recommended catalog row:** `LN-PR-001` (primary type-32 `open_channel` row)
**Branch:** `repair/integrated`
**Status:** complete; scoped build, forbidden-token scan, and public-theorem
axiom audit clean
**Owned files created:** `LnLean/Proofs/Protocol/NoiseTransportTargets.lean`,
`agents/reports/swarm11/S11-L1-NOISE-AUTH.md`
**Files edited outside the owned set:** none. No commit, push, root import,
catalog, traceability, audit, docs, script, or test edit.

---

## 1. Objective

`TransportAuthTargets` separated an authenticated transport session from the
explicit `SessionKeyBinding` law, but it did not model a BOLT 8/Noise session,
did not derive session keys, and did not model frame acceptance. `L1-03` still
recorded that no Noise/MAC implementation exists.

This lane adds an **additive, model-level** BOLT 8/Noise-shaped layer that:

1. models `NoiseHandshake` / `NoiseSession` with initiator and responder static
   keys, ephemeral keys, a handshake transcript, and two directional opaque
   session keys with explicit derivation laws;
2. models `TransportFrame` (session id, nonce, ciphertext, MAC) and an
   `AeadAccept` relation over a `TransportCrypto` interface;
3. states the explicit assumptions `NoiseHandshakeSound`, `AeadUnforgeable`,
   `AeadKeyBinding`, and `NonceFresh`;
4. proves that an accepted frame is produced under the session send key and is
   bound to the session peer static key, and that the peer/advertisement
   equality yields `SessionKeyBinding`, attribution, and the routed funding
   result;
5. mechanises replay without freshness, wrong-peer rejection, key substitution,
   payload-only non-attribution, and a concrete non-vacuity witness.

No real Noise implementation, confidentiality property, computational AEAD, or
key-ownership theorem is claimed.

## 2. Answer in one paragraph

A Noise session is a `NoiseHandshake` plus a local role and two directional
`SessionKey`s. Each key is derived deterministically from the handshake
transcript and carries the peer static key as model associated data
(`deriveKey`). A frame is accepted only when the abstract `AeadAccept` relation
accepts it. Under `NoiseHandshakeSound` (the session keys are exactly the
derivations) and `AeadUnforgeable` (acceptance implies provenance under the
key), an accepted frame is produced under the session send key, whose `peer`
projection is the session peer static key. If that peer static key equals
`open_channel.funding_pubkey`, the wave-10 `SessionKeyBinding` follows, hence
`EnvelopeAttributed`, the wave-9 `open_channel → accept_channel →
funding_created` route, and the hash-linked funding construction. The receive
rule adds `NonceFresh`; dropping it makes replay acceptance provable. Dropping
`AeadKeyBinding` makes a same-key-id/different-peer substitution provable. The
wire still determines neither the peer key nor attribution.

## 3. Exact model and line references

Namespace:

```lean
LnLean.Proofs.Protocol.NoiseTransportTargets
```

Imports:

```lean
import LnLean.Crypto.Noise
import LnLean.Proofs.Protocol.TransportAuthTargets
```

Model definitions:

| Declaration | Line | Role |
|---|---:|---|
| `roleFlip`, `roleCode`, `roleTag` | 93, 102, 107 | direction and opaque-tag helpers |
| `NoiseHandshake` | 114 | `Noise_XK`-shaped static/ephemeral keys and transcript |
| `NoiseHandshake.peerStaticOf` | 132 | peer static key from a role |
| `SessionKey` | 139 | opaque key id, material, transcript, peer static key, role |
| `deriveKey` | 156 | the explicit derivation law |
| `deriveKey_id` / `_material` / `_transcript` / `_peer` / `_role` | 163–175 | derivation projections |
| `NoiseSession` | 197 | handshake, role, send key, recv key |
| `NoiseSession.peerStatic` / `ownStatic` | 210, 214 | peer and local static views |
| `NoiseHandshakeSound` | 222 | explicit derivation assumption |
| `NoiseHandshakeAgreement` | 244 | two-view structural agreement |
| `Mac` | 284 | key id, peer static key, opaque tag |
| `TransportFrame` | 296 | session id, nonce, ciphertext, MAC |
| `tagOf` | 309 | finite model tag function |
| `TransportCrypto` | 315 | abstract `accept` / `produced` relations |
| `AeadAccept` | 322 | acceptance relation |
| `AeadUnforgeable` | 330 | explicit acceptance/provenance law |
| `AeadKeyBinding` | 338 | explicit cross-key peer law |
| `ReceiveWindow` / `NonceFresh` | 343, 350 | replay window and freshness |
| `recv` | 358 | freshness-checking receiver |
| `recvLoose` | 434 | freshness-free counterexample receiver |
| `sealFrame`, `looseAccept`, `strictAccept` | 490, 499, 503 | finite frame operations |
| `looseCrypto`, `strictCrypto` | 507, 512 | finite crypto instances |
| `NoiseDelivery` | 564 | Noise session plus unchanged `OpenChannelWire` |
| `NoiseDelivery.toTransportSession` / `toAuthenticatedDelivery` | 574, 580 | bridge to `TransportAuthTargets` |

The `SessionKey.peer` field is the model's associated-data binding. It is a
structural model of the Noise handshake hash binding the static keys, **not** a
claim that the key is secret or that a real HKDF derived it. `mac.peer` and
`mac.keyId` likewise are finite model identifiers, not Poly1305 output.

## 4. Assumptions (explicit and minimal)

| Assumption | Line | Meaning | Not claimed |
|---|---:|---|---|
| `NoiseHandshakeSound s` | 222 | `s.sendKey = deriveKey s.handshake s.role` and `s.recvKey = deriveKey s.handshake (roleFlip s.role)` | honest transcript, peer possession, secrecy |
| `AeadUnforgeable C` | 330 | `AeadAccept C k f → C.produced k f` | real AEAD authenticity or a game reduction |
| `AeadKeyBinding C` | 338 | two keys accepting one frame agree on `peer` | needed only for the strongest peer-uniqueness statement |
| `NonceFresh w f` | 350 | `f.nonce ∉ w.seen` | global uniqueness of nonces |
| `AeadAccept C k f` | 322 | abstract frame acceptance | ChaCha20-Poly1305, IND-CCA, confidentiality |

`AeadUnforgeable` and `AeadKeyBinding` are hypotheses, not theorems about the
model's finite `strictCrypto`; in `strictCrypto` both `accept` and `produced`
are the same finite relation, which is why the non-vacuity instance is honest
and uninteresting cryptographically.

## 5. Positive results

### 5.1 Key derivation

```lean
roleFlip_flip                          -- line 97
deriveKey_id                           -- line 163
deriveKey_material                     -- line 166
deriveKey_transcript                   -- line 169
deriveKey_peer                         -- line 172
deriveKey_role                         -- line 175
deriveKey_deterministic                -- line 179
deriveKey_congr                        -- line 185
deriveKey_id_initiator_ne_responder    -- line 191
session_sendKey_peer                   -- line 229
session_recvKey_peer                   -- line 237
handshakeAgreement_transcript          -- line 257
handshakeAgreement_peerStatic          -- line 262
deriveKey_eq_of_agreement              -- line 270
```

`session_sendKey_peer` is the key derivation-to-peer link:

```lean
theorem session_sendKey_peer (s : NoiseSession)
    (h : NoiseHandshakeSound s) :
    s.sendKey.peer = s.peerStatic
```

### 5.2 Frame acceptance and peer binding

```lean
accepted_implies_produced              -- line 449
accepted_frame_bound_to_peer           -- line 460
accepted_frame_peer_unique             -- line 469
accepted_frame_other_peer_rejected     -- line 478
strictCrypto_accept_seal               -- line 517
looseCrypto_accept_seal                -- line 523
strictCrypto_unforgeable               -- line 531
looseCrypto_unforgeable                -- line 536
strictCrypto_keyBinding                -- line 540
strictCrypto_wrong_peer_rejected       -- line 545
looseCrypto_wrong_key_rejected         -- line 553
```

The central theorem is:

```lean
theorem accepted_frame_bound_to_peer (C : TransportCrypto)
    (hU : AeadUnforgeable C) (s : NoiseSession)
    (hS : NoiseHandshakeSound s) (f : TransportFrame)
    (hacc : AeadAccept C s.sendKey f) :
    C.produced s.sendKey f ∧ s.sendKey.peer = s.peerStatic
```

`accepted_frame_peer_unique` strengthens this from "the session send key" to
"any accepting key" under `AeadKeyBinding`.

### 5.3 Freshness and replay

```lean
recv_requires_accept                   -- line 366
recv_requires_fresh                    -- line 377
recv_seen                              -- line 388
recv_none_of_not_fresh                 -- line 400
replay_rejected_with_freshness         -- line 410
nonceFresh_cons_self_false             -- line 419
nonceFresh_cons_of_ne                  -- line 424
recvLoose_accept                       -- line 440
```

`replay_rejected_with_freshness` is the positive freshness result:
after a successful `recv`, the same frame is rejected by the next `recv`.

### 5.4 `SessionKeyBinding` and composition with `TransportAuthTargets`

```lean
toAuthenticatedDelivery_session        -- line 585
toAuthenticatedDelivery_wire           -- line 588
toAuthenticatedDelivery_authenticated  -- line 594
sessionKeyBinding_iff_peerStatic_eq    -- line 599
peerStatic_eq_funding_yields_sessionKeyBinding -- line 605
sessionKeyBinding_yields_peerStatic_eq -- line 612
accepted_frame_yields_sessionKeyBinding -- line 619
accepted_frame_attributed_delivery     -- line 632
accepted_frame_reaches_fundingCreated  -- line 648
accepted_frame_reaches_funding         -- line 671
accepted_frame_key_in_funding_script   -- line 692
```

The bridge is exact, not a redefinition:

```lean
theorem sessionKeyBinding_iff_peerStatic_eq (d : NoiseDelivery) :
    SessionKeyBinding d.toAuthenticatedDelivery ↔
      d.session.peerStatic = d.wire.fundingPubKey
```

The composition theorems use the unchanged wave-9/10 theorems
`TransportAuthTargets.envelopeAttributed_of_sessionKeyBinding`,
`authenticated_delivery_reaches_fundingCreated`,
`authenticated_open_reaches_funding`, and
`authenticated_key_in_funding_script`.

## 6. Mechanised counterexamples and obstructions

### 6.1 Key substitution without peer binding

`key_substitution_without_peer_binding` (line 870) exhibits one
`TransportCrypto` and two `SessionKey`s with the same opaque id and different
`peer` fields that both accept the same frame. `looseCrypto_not_keyBinding`
(line 877) proves the loose instance violates `AeadKeyBinding`. This is the
mechanised reason `accepted_frame_peer_unique` needs that explicit law.

### 6.2 Replay without nonce freshness

`replay_accepted_without_nonce_freshness` (line 884) exhibits a crypto model,
window, key, frame, and two successful `recvLoose` steps on the *same* frame.
The freshness-checking rule rejects it (`replay_rejected_with_freshness`, line
410). The difference is exactly `NonceFresh`; no AEAD weakness is asserted.

### 6.3 Wrong-peer rejection

`strictCrypto_wrong_peer_rejected` (line 545) proves that when two keys have
different `peer` fields, a frame accepted by the first is rejected by the
second in `strictCrypto`. Abstractly,
`accepted_frame_other_peer_rejected` (line 478) proves the same from
`AeadKeyBinding`.

### 6.4 Payload-only attribution remains impossible

`acceptance_not_attribution` (line 905): a sound session with an accepted frame
still need not satisfy `SessionKeyBinding`. The peer/advertisement equality is
an extra hypothesis.

`noise_does_not_authenticate_payload` (line 919): the same wire is delivered by
two sound sessions with different peer static keys; only one delivery is
bound. This is the exact wave-10 `transport_auth_not_from_wire` boundary lifted
to the Noise layer.

`noise_peer_not_from_wire` (line 933) and `no_wire_session_binding_function`
(line 951): there is no function of the type-32 payload that returns the Noise
peer key, or decides `SessionKeyBinding`, for every delivery.

`accepted_frame_wire_carries_no_signature` (line 966): an accepted frame gives
no ECDSA proof-of-possession evidence; key ownership remains `C3`/`PR-01`.

### 6.5 Non-vacuity

`noise_transport_nonvacuous` (line 1015) provides a concrete
`strictCrypto` instance satisfying `AeadUnforgeable` and `AeadKeyBinding`, a
concrete sound handshake/session, a fresh accepted frame, `SessionKeyBinding`,
and `EnvelopeAttributed`.

`concrete_accepted_frame_route` (line 1028) additionally reaches
`funding_created`, `FundingPhase`, and the hash-linked funding construction for
an arbitrary `AcceptChannel` and hash function.

The other non-vacuity witnesses are `concrete_delivery_authenticated` (982),
`concrete_delivery_bound` (985), `concrete_frame_accepted` (988),
`concrete_frame_fresh` (993), `concrete_frame_peer_bound` (998), and
`concrete_delivery_attributed` (1006).

## 7. Build and audit

Build command (exact):

```bash
cd /home/ubuntu/ln-lean-repair && \
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Proofs.Protocol.NoiseTransportTargets
```

Result: **RC 0**, `✔ [24/24] Built
LnLean.Proofs.Protocol.NoiseTransportTargets (1.2s)`, "Build completed
successfully (24 jobs)." No warnings on the final build.

Forbidden-token scan:

```bash
grep -nE "sorry|axiom|admit|native_decide|unsafe|implemented_by" \
  LnLean/Proofs/Protocol/NoiseTransportTargets.lean
```

Result: **clean** (no matches).

Axiom audit: an import-only script issued `#print axioms` for **all 62 public
theorems** in the module. Result:

* 33 theorems: `does not depend on any axioms`;
* 29 theorems: depend only on `propext`, `Quot.sound`, and/or
  `Classical.choice`;
* no `sorryAx`, no `axiom`, no unexpected constant.

The `Classical.choice`/`propext`/`Quot.sound` uses come from the classical
receiver definitions (`recv`, `recvLoose`) and propositional structure, not
from any new axiom.

## 8. What is not claimed

This module does **not** claim:

* a real `Noise_XK` implementation, ECDH, HKDF, ChaCha20-Poly1305, or
  Poly1305;
* confidentiality, IND-CCA security, computational secrecy, or key
  indistinguishability;
* key ownership or proof of possession from `funding_pubkey`;
* that the finite `strictCrypto`/`looseCrypto` instances model a real AEAD;
* that the handshake transcript was honestly produced;
* that `AeadUnforgeable` or `AeadKeyBinding` follow from C3/C1.

`strictCrypto` is a finite witness used to separate the positive laws from the
counterexamples. It satisfies `AeadUnforgeable` because `produced` is
definitionally `accept`; it is not evidence about a real AEAD.

## 9. Recommended catalog target list

### `LN-PR-001` (primary; recommended)

Add the following targets to the `LN-PR-001` row (in addition to the existing
wave-9/10 targets):

Positive/transport:

* `LnLean.Proofs.Protocol.NoiseTransportTargets.accepted_frame_bound_to_peer`
* `LnLean.Proofs.Protocol.NoiseTransportTargets.sessionKeyBinding_iff_peerStatic_eq`
* `LnLean.Proofs.Protocol.NoiseTransportTargets.accepted_frame_yields_sessionKeyBinding`
* `LnLean.Proofs.Protocol.NoiseTransportTargets.accepted_frame_attributed_delivery`
* `LnLean.Proofs.Protocol.NoiseTransportTargets.accepted_frame_reaches_fundingCreated`
* `LnLean.Proofs.Protocol.NoiseTransportTargets.accepted_frame_reaches_funding`
* `LnLean.Proofs.Protocol.NoiseTransportTargets.accepted_frame_key_in_funding_script`
* `LnLean.Proofs.Protocol.NoiseTransportTargets.noise_transport_summary`

Freshness:

* `LnLean.Proofs.Protocol.NoiseTransportTargets.replay_rejected_with_freshness`
* `LnLean.Proofs.Protocol.NoiseTransportTargets.replay_accepted_without_nonce_freshness`

Negative boundaries:

* `LnLean.Proofs.Protocol.NoiseTransportTargets.key_substitution_without_peer_binding`
* `LnLean.Proofs.Protocol.NoiseTransportTargets.acceptance_not_attribution`
* `LnLean.Proofs.Protocol.NoiseTransportTargets.noise_does_not_authenticate_payload`
* `LnLean.Proofs.Protocol.NoiseTransportTargets.noise_peer_not_from_wire`
* `LnLean.Proofs.Protocol.NoiseTransportTargets.no_wire_session_binding_function`
* `LnLean.Proofs.Protocol.NoiseTransportTargets.accepted_frame_wire_carries_no_signature`

Non-vacuity:

* `LnLean.Proofs.Protocol.NoiseTransportTargets.noise_transport_nonvacuous`
* `LnLean.Proofs.Protocol.NoiseTransportTargets.concrete_accepted_frame_route`

Suggested updated row text: *"A model-level BOLT 8/Noise session derives
directional keys from the handshake transcript and peer static key; under
explicit `NoiseHandshakeSound`/`AeadUnforgeable` an accepted frame is bound to
the session peer, and peer/advertisement equality yields `SessionKeyBinding`,
attribution, and the routed `funding_created`/funding result. `NonceFresh` is
required for replay rejection; dropping `AeadKeyBinding` admits key
substitution. The wire alone still determines neither the peer nor
attribution, and no real Noise/AEAD/confidentiality claim is made."*

### `LN-L1-003`

**Do not add these targets to `LN-L1-003`.** That row is the reorg/common-tip
row (`ReorgTargets.reorg_preserves_channel_safety`,
`deep_reorg_separate_failure_mode`); transport authentication is not part of its
statement. If a separate L1 transport row is wanted, create a new row rather
than overloading `LN-L1-003`. The issue tracker spelling `L1-03` maps to the
transport/`LN-PR-001` evidence, not to `LN-L1-003`.

## 10. Integration notes for the parent

* No root import was edited. To include this module in the root build, the
  parent must add `import LnLean.Proofs.Protocol.NoiseTransportTargets` to the
  appropriate root aggregator; this lane intentionally did not touch it.
* No catalog, traceability, audit, docs, script, or test file was edited.
* The module imports only `LnLean.Crypto.Noise` and
  `LnLean.Proofs.Protocol.TransportAuthTargets`; it does not depend on any new
  core patch.
* The exact boundary to keep visible in catalog prose is: acceptance +
  soundness + unforgeability give peer binding; `SessionKeyBinding` additionally
  needs peer static key = advertised funding key; key ownership still needs
  C3/`PR-01`.
