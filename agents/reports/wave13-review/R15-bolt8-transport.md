# R15 — BOLT 8 transport, Noise, and TLS/API security
**Status:** read-only review
**Pins:** LDK Node `fa123fed131e27ecc420b77fa7086fcf1ddaebb8`, LDK Server `c17dc11dde38f88c53457039ddf30c6b90a63ba2`

## 1. Scope and current Lean surface

### 1.1 Catalog placement

There is **no dedicated BOLT 8 / Noise catalog row**. The transport claims live
under the `LN-PR-001` (`open_channel`) row, with one secondary citation under
`LN-SEC-007`:

| Location | Text / anchor | What it actually covers |
|---|---|---|
| `docs/THEOREM-INDEX.md:62` | `LN-PR-001`, “Protocol / peer” | BOLT 2 `open_channel` bounds, wire projection, routing, and the wave-9/10/11 transport-attribution layer. The target list includes `NoiseTransportTargets.accepted_frame_bound_to_peer`, `accepted_frame_attributed_delivery`, `accepted_frame_reaches_fundingCreated`, the replay/counterexample targets, and `noise_transport_nonvacuous`. |
| `docs/THEOREM-INDEX.md:87` | `LN-SEC-007`, “Security / proofs” | A non-vacuity witness registry. Its targets are all `NonVacuityTargets.*`; the BOLT 8 mention is a citation, not a Noise theorem. |
| `docs/TRACEABILITY.md:41` | `LN-PR-001` | Anchor is only “BOLT 2 §The open_channel Message”; no BOLT 8 section is named. |
| `docs/TRACEABILITY.md:66` | `LN-SEC-007` | Anchors “BOLT 3 §Commitment Transaction; BOLT 8 §Handshake”, but the cited Lean targets are `NonVacuityTargets.*`. |
| `docs/THEOREM-INDEX.md:333-335` | wave-11 note | Says `LN-PR-001` “adds `NoiseTransportTargets`: a Noise_XK-shaped handshake/session model, AEAD acceptance/provenance, nonce freshness/replay, and a derived `SessionKeyBinding`; computational security remains explicit.” |

The row is honest that `TransportAuthenticated` is a flag, that
`SessionKeyBinding` is an explicit equality, and that this is not a real
Noise_XK/AEAD or EUF-CMA claim. The findings below are therefore not that the
catalog overclaims computational security. They are that (i) the positive
theorem is about the wrong direction, and (ii) the equality it derives is a
funding-key equality, not a node-id/transport-peer equality.

Consequences:

* A reader who searches the catalog for “BOLT 8” finds only the `LN-SEC-007`
  non-vacuity citation. There is no row whose claim is “BOLT 8 transport
  authentication”.
* The BOLT 8 material is subordinate prose and target names under a BOLT 2
  opening-message row. The row’s headline claim remains `open_channel` bounds
  and routing.
* There is no catalogue row at all for TLS, gRPC, macaroons, request binding, or
  Tor routing. Those behaviours are outside the current traceability surface.

### 1.2 Declarations and exact claim surface

The central module is `LnLean/Proofs/Protocol/NoiseTransportTargets.lean`
(1,092 lines). Its declarations are:

| Declaration | Lines | Exact content |
|---|---|---|
| `NoiseHandshake` | 114–127 | Pattern, initiator/responder static keys, initiator/responder ephemeral keys, opaque transcript bytes. No handshake acts, no signatures, no ECDH result. |
| `SessionKey` | 139–150 | Opaque `id`, `material`, `transcript`, `peer : PubKey`, `role`. |
| `deriveKey` | 156–161 | `id := transcript.size * 2 + roleCode r`; `material := transcript.push (roleTag r)`; `peer := h.peerStaticOf r`. The peer field is **defined** by the handshake role, not derived cryptographically. |
| `NoiseSession` | 197–206 | `handshake`, `role`, `sendKey` (“key used to authenticate outbound frames”), `recvKey` (“key used to authenticate inbound frames”). |
| `NoiseSession.peerStatic` / `ownStatic` | 208–215 | Peer static via `peerStaticOf role`; own static via `peerStaticOf (roleFlip role)`. The docstring at 208–209 says this is “the value that must match `open_channel.funding_pubkey`”, which is the conflation at issue. |
| `NoiseHandshakeSound` | 222–226 | Only `sendKey = deriveKey handshake role` and `recvKey = deriveKey handshake (roleFlip role)`. It does **not** assert transcript honesty, key possession, ECDH, HKDF, or a real handshake. |
| `session_sendKey_peer` | 229–232 | `s.sendKey.peer = s.peerStatic` (structural, from `deriveKey`). |
| `session_recvKey_peer` | 237–240 | `s.recvKey.peer = s.ownStatic` — explicitly “not an attribution claim”. |
| `NoiseHandshakeAgreement` | 244–254 | Two views agree on both statics, both ephemerals, and transcript. |
| `TransportFrame` | 296–305 | `sessionId`, `nonce`, `ciphertext`, `mac`. No plaintext, no length, no associated data. |
| `tagOf` | 309–310 | Toy tag: `nonce + ciphertext.size`. |
| `AeadUnforgeable` | 330–332 | `∀ k f, accept k f → produced k f`. An explicit assumption. |
| `AeadKeyBinding` | 338–340 | Two keys accepting the same frame agree on `peer`. An explicit assumption. |
| `NonceFresh` | 350–351 | `f.nonce ∉ w.seen` — set membership only, not “next expected nonce”. |
| `recv` | 358–363 | Accept iff `AeadAccept` and `NonceFresh`; append nonce to `seen`. No session-id check, no nonce-order check. |
| `recvLoose` | 434–436 | Accept iff `AeadAccept`; leaves the window unchanged. |
| `accepted_frame_bound_to_peer` | 460–465 | `AeadAccept C s.sendKey f` plus `AeadUnforgeable` gives `C.produced s.sendKey f ∧ s.sendKey.peer = s.peerStatic`. |
| `accepted_frame_peer_unique` | 469–474 | Adds `AeadKeyBinding` to make **any** accepting key have the session peer. |
| `NoiseDelivery` | 564–569 | `session : NoiseSession` documented as “The receiving session”, plus the unchanged type-32 `wire`. |
| `NoiseDelivery.toTransportSession` | 574–577 | `sessionId := transcript.size`, `peerKey := session.peerStatic`, `established := true`. |
| `sessionKeyBinding_iff_peerStatic_eq` | 599–602 | `SessionKeyBinding d ↔ d.session.peerStatic = d.wire.fundingPubKey`, by `Iff.rfl`. |
| `accepted_frame_yields_sessionKeyBinding` | 619–627 | Consumes `AeadAccept C d.session.sendKey f` and the explicit `peerStatic = fundingPubKey`; concludes `produced sendKey f` and `SessionKeyBinding`. |
| `accepted_frame_attributed_delivery` | 632–644 | Adds `EnvelopeAttributed` through `TransportAuthTargets`. |
| `accepted_frame_reaches_fundingCreated` | 648–667 | Adds the wave-9 route to `funding_created`. |
| Negative targets | 870–962 | `key_substitution_without_peer_binding`, `replay_accepted_without_nonce_freshness`, `acceptance_not_attribution`, `noise_does_not_authenticate_payload`, `noise_peer_not_from_wire`, `no_wire_session_binding_function`. |
| `accepted_frame_advertised_key_independent` | 973–978 | For any valid `k`, an accepted delivery can advertise `fundingPubKey = k` while keeping the same session. |
| `noise_transport_nonvacuous` | 1015–1024 | Concrete witness using `strictCrypto`, `demoDelivery`, `demoFrame`. |
| `noise_transport_summary` | 1061–1089 | Bundles the positive, replay, key-substitution, no-wire-peer, and no-signature statements. |

The supporting surfaces are also narrower than their names suggest:

* `LnLean/Crypto/Noise.lean:57-65` defines `NoiseState` with byte-array
  `sendKey`/`recvKey` and `sendNonce`/`recvNonce`, but `transportEncrypt`
  (92–95) and `transportDecrypt` (99–103) increment the nonce **once per
  message**. BOLT 8 increments twice per message: once for the 18-byte encrypted
  length and once for the body (`refs/bolts/08-transport.md:452-487`). There is
  no rekey at 1000 (`:489-507`).
* `LnLean/Wire/Message.lean:367-371` defines `Transport.transportFrame` as
  plaintext `type || transportLength || payload`. It has no encrypted length,
  no 16-byte Poly1305 tag, and no 65,569-byte packet bound.
* `LnLean/Proofs/Protocol/TransportAuthTargets.lean:150-151` defines
  `TransportAuthenticated` as the Boolean `established = true`, and `:164-165`
  defines `SessionKeyBinding` as `peerKey = fundingPubKey`.
* `LnLean/Crypto/Noise.lean:141-146` defines `AuthenticatedChannel` with a
  `peer : PubKey` field but the only law is `recv (send m) = some m`. Nothing
  connects `peer` to `recv`; the ideal-channel interface itself assumes
  attribution.
* `LnLean/Proofs/Bitcoin/FundingAuthTargets.lean:430-444` defines
  `PeerIdentity` with a single `key : PubKey` and `OpenChannelAttributed` as
  `sender.key = o.fundingPubKey`. There is no node-id type anywhere in the
  transport path, so the funding-key equality is the only peer identity the
  model can express.
* `LnLean/Proofs/Routing/NodeAddressTargets.lean:24-30` models BOLT 7 address
  syntax only and explicitly excludes DNS resolution, Tor hostname resolution,
  reachability, and P2P framing.

### 1.3 The sharp current-model defect: send key used for a receiving delivery

`NoiseDelivery.session` is documented as the **receiving** session
(`NoiseTransportTargets.lean:564-566`). Every positive delivery theorem accepts
the frame under `d.session.sendKey`:

* `accepted_frame_yields_sessionKeyBinding` (`:619-627`)
* `accepted_frame_attributed_delivery` (`:632-644`)
* `accepted_frame_reaches_fundingCreated` (`:648-667`)
* `accepted_frame_reaches_funding` (`:671-688`)
* `accepted_frame_key_in_funding_script` (`:692-705`)
* `noise_transport_summary` (`:1061-1071`)

But `session_recvKey_peer` (`:237-240`) proves `recvKey.peer = ownStatic`, and
`recv` (`:358-363`) is never used by any delivery theorem. Thus:

* the positive layer proves provenance under the **local send key**;
* `recvKey` cannot yield `recvKey.peer = peerStatic` in general;
* the model never proves that the remote peer’s `sendKey` equals the local
  `recvKey`;
* `NoiseDelivery.toTransportSession.peerKey := session.peerStatic` still
  attributes the delivery to the remote peer despite the accepted frame being
  under the local send key.

This is not a cosmetic naming issue. Either the docstring is wrong (then the
theorem is about a local outbound frame and says nothing about delivered inbound
frames), or the key choice is wrong (then the statement is false for `recvKey`).
In neither reading does the positive layer establish inbound peer binding. A
concrete mechanizable counterexample already exists in the module’s own
witnesses:
`demoUnattributedSession` has `initiatorStatic = pub33 0`,
`responderStatic = pub33 1`, `role = initiator` (`:740-746`, `:802-809`), so
`recvKey.peer = ownStatic = pub33 0` while `peerStatic = pub33 1`. The frame
`sealFrame demoUnattributedSession.recvKey 18 0 ByteArray.empty` is accepted by
`strictCrypto` (`strictCrypto_accept_seal`, `:517-520`) and has
`f.mac.peer = pub33 0 ≠ peerStatic = pub33 1`. Substituting `recvKey` into
`accepted_frame_bound_to_peer` would therefore be **false**.

### 1.4 What is explicitly not modelled

The module says this itself (`NoiseTransportTargets.lean:46-54`): no
confidentiality, IND-CCA, real ChaCha20-Poly1305, real HKDF/ECDH, key ownership,
or concrete Noise implementation. Beyond that statement, the following are also
absent:

* the three-act `Noise_XK` transcript and signature/Proof-of-Possession over the
  static key;
* encrypted length headers, per-message MAC bytes, padding, and packet-size
  limits;
* nonce ordering, two-nonce-per-message consumption, nonce exhaustion, and
  rekeying;
* TLS server authentication, certificate pinning, client authentication, gRPC,
  macaroons, request binding, and Tor routing.

The module is also disconnected from `Crypto/Noise.lean`’s actual transport
functions. It imports `Crypto.Noise` only for `HandshakePattern`/`NoiseRole`; it
never mentions `NoiseState`, `transportEncrypt`, `transportDecrypt`, or
`PrimitiveModel` (verified by `rg`). The C5–C7 primitives
(`docs/ASSUMPTIONS.md:19-21`) are therefore not connected to the abstract
`TransportCrypto` relation at all. This is why `AeadUnforgeable` can be true in
`strictCrypto` while saying nothing about ChaCha20-Poly1305.

## 2. LDK datapoints (with `file:line`)

Reference roots: `/tmp/opencode/ldk-refs/ldk-node`,
`/tmp/opencode/ldk-refs/ldk-server`, and the repo’s pinned
`refs/rust-lightning` at `fe4900930c6bd5786ec4203274d7cf312776a5a6`.

| # | Behaviour | Evidence | Relevance to the Lean model |
|---|---|---|---|
| D1 | Public `connect` takes an **expected `node_id`** and passes it to the connection manager. | `ldk-node/src/lib.rs:1324-1341` (signature and `connect_peer_if_necessary(con_node_id, con_addr)`); `src/connection.rs:115-118` logs `node_id@addr`; `:215-219` passes `node_id` to `lightning_net_tokio::connect_outbound`. | The Lean model has no “expected peer” field on a connection attempt and no rejection theorem for a handshake that presents a different static key. |
| D2 | The outbound Noise handshake is constructed with the expected node id as the remote static key. | `refs/rust-lightning/lightning/src/ln/peer_handler.rs:1424-1430` (`new_outbound_connection(their_node_id, …)`, `PeerChannelEncryptor::new_outbound(their_node_id, …)`). | This is the real source of “transport peer = node id” on outbound. The Lean `peerStatic` is just a handshake field. |
| D3 | Inbound setup has **no expected node id**; the peer identity is learned from the completed handshake. | `ldk-node/src/lib.rs:549-552` calls `lightning_net_tokio::setup_inbound(peer_mgr, tcp_stream)` with no expected key; `refs/rust-lightning/lightning/src/ln/peer_handler.rs:1487-1503` creates `new_inbound(&self.node_signer)` and stores `their_node_id: None`. | The Lean model is closer to inbound: `peerStatic` is whatever the handshake asserts. It does not model the outbound expected-peer check at all. |
| D4 | `node_id()` is the channel manager’s node id, not a funding key. | `ldk-node/src/lib.rs:1046-1047` (`self.channel_manager.get_our_node_id()`). | BOLT 8’s static key is usually the `nodeid` (`refs/bolts/08-transport.md:70`, `:151`), while BOLT 2’s `funding_pubkey` is the 2-of-2 multisig key (`refs/bolts/02-peer-protocol.md:755`). The Lean `SessionKeyBinding` equates the transport peer with `fundingPubKey`, conflating these two roles. |
| D5 | Outbound `.onion` uses the configured Tor SOCKS proxy; `.onion` V2 is rejected; clearnet is not proxied. | `ldk-node/src/connection.rs:121-127` (OnionV2 unsupported), `:129-170` (OnionV3 requires `tor_proxy_config` and calls `tor_connect_outbound`); `ldk-server/docs/tor.md:3-9` (only outbound `.onion` peers), `:21-32`, `:34-37` (inbound hidden service is manual). | The Lean address layer models only BOLT 7 descriptor syntax (`NodeAddressTargets.lean:24-30`); routing, proxy use, and privacy are unmodelled. |
| D6 | TLS is a **self-signed ECDSA P-256 server certificate**, generated on first startup and stored as `tls.crt`/`tls.key`. | `ldk-server/src/util/tls.rs:51-72` (get-or-generate), `:114-141` (P-256 key, CN/SAN hosts `localhost`, `127.0.0.1`); `docs/api-guide.md:120-124`. | No Lean TLS model. Server identity is established by out-of-band certificate pinning, not by the Lightning node id. |
| D7 | The TLS server does **not** request a client certificate. | `ldk-server/src/util/tls.rs:414-420` (`with_no_client_auth()`, `with_single_cert`, ALPN `h2`). | There is no mTLS client identity to bind to a node id or funding key. The Lean model has no TLS client-auth analogue. |
| D8 | Client authentication is an application-layer macaroon, independent of TLS client identity. | `ldk-server/docs/api-guide.md:16-25` (hex v2 macaroon in the `macaroon` header; “All requests use TLS”); `docs/request-binding.md:9-15` (reusable macaroon, per-request proof, HMAC-SHA256 chain). | The Lean model has no macaroon, HMAC chain, or API principal. `PrimitiveModel.hmacSha256` has only a size law (`Crypto/Model.lean:115-116`); `HmacPrf` is explicitly vacuous/uninhabited (`:84-92`). |
| D9 | Request binding is a final caveat `request = <unix-seconds> <RpcMethod> <body-sha256>`, over the exact gRPC frame + protobuf bytes. | `ldk-server/docs/request-binding.md:20-37` (grammar), `:39-50` (body bytes: `00 || 4-byte big-endian length || protobuf`), `:61-70` (max 32 caveats, timestamp ±60 s, method/body hash/policy/revocation checks). | Completely unmodelled. A faithful model would need a parser plus a cryptographic body-hash binding assumption; the latter is not derivable from `sha256_collisionResistant`, which is only on 32-byte inputs (`Crypto/Model.lean:53-57`). |
| D10 | A request token is **not single-use**; an identical request can be replayed while the token is valid. | `ldk-server/docs/request-binding.md:71-73`; `docs/api-guide.md:46-47`. | Contrasts with the Lean `NonceFresh`/`replay_rejected_with_freshness` layer, which is a per-frame replay window, not an API request-replay defence. Different layer, different guarantee. |
| D11 | BOLT 8 encrypts the 2-byte length and the message body with separate AEAD operations and increments the nonce twice per message; keys rotate at 1000. | `refs/bolts/08-transport.md:452-487`, `:489-507`; `refs/rust-lightning/lightning/src/ln/peer_channel_encryptor.rs:518-544` (two `sn += 1`), `:585-626` (two `rn += 1`), `:527-532`/`:590-595` (rekey at 1000). | `LnLean/Crypto/Noise.lean:92-103` increments once per message, and `NoiseTransportTargets` has no encrypted length, MAC, or rekey. |

## 3. Gap matrix

Status vocabulary: **covered faithfully**, **partially covered**, **missing**,
**contradicted** (a model counterexample exists), **unmodelled/external**.

| Behaviour | Lean status | LDK evidence | Gap / counterexample | Priority |
|---|---|---|---|---|
| Outbound connection is pinned to an expected node id | **missing** | D1, D2 | No `ExpectedPeer` in `NoiseSession`/`NoiseDelivery`. `peerStatic` is an unconstrained handshake field. A session with any `peerStatic` is accepted and can be attributed if it equals the wire funding key. | P1 |
| Inbound peer identity is learned from the handshake, not from the payload | **partially covered** | D3 | `NoiseSession.peerStatic` (`:210-211`) and `noise_peer_not_from_wire` (`:933-947`) capture “not from the wire”, but there is no theorem that the static key was proven by the handshake. `NoiseHandshakeSound` is only a derivation equality. | P1 |
| Attribution is not determined by the wire payload | **covered faithfully** | BOLT 1 §Lightning Message Format; BOLT 2 `open_channel` has no sender field; `FundingAuthTargets.lean:475-491` | `noise_peer_not_from_wire` (`:933-947`) and `no_wire_session_binding_function` (`:951-962`) are correct negatives and should be preserved. | P2 |
| Exact duplicate-frame replay is rejected | **covered faithfully** (for the model’s window) | D11 | `replay_rejected_with_freshness` (`:410-416`) is correct for `recv`; the limitation is the loose `recvLoose` and the absence of nonce ordering, not this theorem. | P2 |
| Transport peer is the BOLT 8 static key / node id | **partially covered / conflated** | D4; BOLT 8 `:70`, `:151`; BOLT 2 `:755` | `SessionKeyBinding` is exactly `peerKey = fundingPubKey` (`TransportAuthTargets.lean:164-165`; `NoiseTransportTargets.lean:599-602`). BOLT 8’s static key is usually the node id; BOLT 2’s funding key is a separate multisig key. The model has no `nodeId` field and no theorem separating the two roles. T3 supplies the missing separation as additive witnesses. | P0 |
| Accepted **inbound** frame is bound to the peer static key | **contradicted** | D2, D3; BOLT 8 per-direction keys `:362-369`, `:396-403` | All positive delivery theorems accept under `d.session.sendKey` while `NoiseDelivery` is documented as the receiving session (`:564-566`). `session_recvKey_peer` gives `recvKey.peer = ownStatic` (`:237-240`). `demoUnattributedSession` gives an accepted `recvKey` frame with `mac.peer = pub33 0 ≠ peerStatic = pub33 1`. | P0 |
| Frame is bound to its session id | **missing** | D3, D11 | `TransportFrame.sessionId` exists (`:298`) but `AeadAccept`, `strictAccept` (`:503-504`), and `recv` (`:358-363`) never inspect it. A frame sealed for session 17 is accepted by a session whose transcript-derived id is 32 (`demoSession.sessionId = 32`). | P1 |
| Replay is rejected | **partially covered** | D11 | `replay_rejected_with_freshness` (`:410-416`) rejects an exact previously seen nonce. `recv` accepts skipped/out-of-order nonces from an empty window and has no `nextNonce`; `recvLoose` (`:434-436`) is the deliberately loose counterexample. | P1 |
| Nonce schedule matches BOLT 8 (two increments, rekey) | **missing** | D11 | `Crypto/Noise.lean:92-103` increments one per message; no length/body split; no 1000-message rotation. `NoiseTransportTargets` nonces are arbitrary `Nat`s, disconnected from `NoiseState`. | P1 |
| Encrypted length header and per-message MAC are modelled | **missing** | D11; BOLT 8 `:447-450` (max 65,569 bytes) | `Wire/Message.lean:367-371` is plaintext `type || length || payload`. No 18-byte encrypted length, no 16-byte tag, no 65,569-byte bound. | P1 |
| Handshake transcript / ECDH / HKDF / static-key possession | **unmodelled** | D2, D3; BOLT 8 `:67`, `:82`, `:151` | `deriveKey` (`:156-161`) uses `transcript.size` and a role tag; it ignores the ephemeral keys entirely. `NoiseHandshakeSound` (`:222-226`) asserts only that the stored keys equal that function. No ECDH, HKDF, signature, or proof of possession. | P1 |
| Noise layer consumes the actual Noise/AEAD interface | **missing** | D11; C5–C7 at `docs/ASSUMPTIONS.md:19-21` | `NoiseTransportTargets` imports `Crypto.Noise` only for `HandshakePattern`/`NoiseRole`; it never references `NoiseState`, `transportEncrypt`, `transportDecrypt`, or `PrimitiveModel`. `TransportCrypto` is an independent abstract relation. | P1 |
| AEAD acceptance has ciphertext integrity | **partially covered / assumption** | D11 | `AeadUnforgeable` (`:330-332`) is an explicit assumption. `strictCrypto` sets `produced := accept` (`:512-514`), and `strictAccept` (`:503-504`) checks only `keyId`, `peer`, and `tag = nonce + ciphertext.size`; two frames with the same nonce/size and different ciphertext are both accepted. | P1 |
| Key ownership / advertised `funding_pubkey` is proved | **missing / external** | BOLT 2 `:755`, `:809`; D4 | `accepted_frame_advertised_key_independent` (`:973-978`) shows any valid funding key can be advertised under the same accepted session. `accepted_frame_wire_carries_no_signature` (`:966-968`) shows the payload carries no signature. | P0 |
| TLS server authentication and certificate pinning | **unmodelled** | D6 | No Lean TLS or certificate model. The server certificate is self-signed and clients must pin it (`api-guide.md:122-124`). | P2 |
| TLS client authentication | **unmodelled** | D7, D8 | `with_no_client_auth()` (`tls.rs:417`). Client identity is a macaroon, not a certificate. | P2 |
| API request binding (method/body/time) | **unmodelled** | D9, D10 | No parser, caveat grammar, HMAC chain, timestamp, or body-hash model. `sha256_collisionResistant` is only on 32-byte preimages, so it cannot support arbitrary gRPC body binding. | P2 |
| Tor routing / privacy boundary | **unmodelled** | D5 | `NodeAddressTargets` models descriptor syntax only (`:24-30`). No outbound `.onion`-only policy, proxy failure, or inbound hidden-service behaviour. | P2 |

## 4. Proposed targets

All proposed targets are **additive**. None weakens an existing theorem. The
first two are the only ones I would consider for a bounded fidelity lane; the
rest are either interface completions or explicitly external.

### T1 — `NoiseTransportTargets.recv_frame_bound_to_remotePeer` (P0)

**Statement shape**

```lean
theorem recvKey_eq_remoteSendKey
    {a b : NoiseSession}
    (ha : NoiseHandshakeSound a) (hb : NoiseHandshakeSound b)
    (hrole : b.role = roleFlip a.role)
    (hagr : NoiseHandshakeAgreement a.handshake b.handshake) :
    a.recvKey = b.sendKey := by
  rw [ha.recvKey_derived, hb.sendKey_derived, hrole]
  exact deriveKey_eq_of_agreement hagr (roleFlip a.role)

theorem recv_frame_bound_to_remotePeer
    (C : TransportCrypto) (hU : AeadUnforgeable C)
    (a b : NoiseSession)
    (ha : NoiseHandshakeSound a) (hb : NoiseHandshakeSound b)
    (hrole : b.role = roleFlip a.role)
    (hagr : NoiseHandshakeAgreement a.handshake b.handshake)
    (f : TransportFrame) (hacc : AeadAccept C a.recvKey f) :
    C.produced b.sendKey f ∧ b.sendKey.peer = b.peerStatic := by
  rw [recvKey_eq_remoteSendKey ha hb hrole hagr] at hacc
  exact accepted_frame_bound_to_peer C hU b hb f hacc
```

**Hypotheses.** Two sound session views of one agreed handshake, with opposite
roles. These are exactly the data a real completed `Noise_XK` handshake gives
both endpoints; they are not available in the current one-session model.

**Non-vacuity witness.** Use a handshake with `initiatorStatic = pub33 0` and
`responderStatic = pub33 1` (unlike `demoHandshake`, which sets both to
`pub33 0` at `:742-743`). Let `a` be the initiator view and `b` the responder
view; seal under `a.recvKey`. Then `a.recvKey = b.sendKey`,
`b.sendKey.peer = pub33 1 = b.peerStatic`.

**Why it is faithful.** It corrects the send/receive direction without
pretending to prove real AEAD unforgeability. It still keeps
`AeadUnforgeable` explicit. It also exposes the missing cross-view agreement
law, which the current positive theorems silently assume. To replace the catalog
claim, the delivery bridge should be restated over a received frame and the
remote view; the existing `accepted_frame_attributed_delivery` should then be
re-labelled as a local/send-key statement, not cited for inbound attribution.

**Cost / risk.** Low: one helper and one theorem, reusing
`deriveKey_eq_of_agreement` (`:270-277`). Fidelity risk: still structural
because `deriveKey` puts `peer` in the key; label it a model extension, not a
cryptographic authentication result.

### T2 — `NoiseTransportTargets.recvKey_not_peerStatic_witness` (P0, preservation)

**Statement shape**

```lean
theorem recvKey_not_peerStatic_witness :
    ∃ (C : TransportCrypto) (s : NoiseSession) (f : TransportFrame),
      NoiseHandshakeSound s ∧
        AeadAccept C s.recvKey f ∧
        s.recvKey.peer ≠ s.peerStatic
```

**Witness.** `C = strictCrypto`, `s = demoUnattributedSession`,
`f = sealFrame s.recvKey 18 0 ByteArray.empty`. `strictCrypto_accept_seal`
gives acceptance; `s.recvKey.peer = pub33 0`, `s.peerStatic = pub33 1`, and
`pub33_zero_ne_one` (`:721-732`) gives disequality.

**Why it is faithful.** This is the counterexample that prevents a naive “fix”
of substituting `recvKey` into `accepted_frame_bound_to_peer`. It must be
preserved next to T1, and it should replace the degenerate non-vacuity witness
for the receive direction.

**Cost / risk.** Very low. No new definitions. **Label:** preservation
counterexample; no new assumption.

### T3 — `NoiseTransportTargets.nodeId_fundingKey_independent` (P1)

**Statement shape**

```lean
def TransportNodeBinding (d : NoiseDelivery) (nodeId : PubKey) : Prop :=
  d.session.peerStatic = nodeId

theorem transportNodeBinding_not_sessionKeyBinding :
    ∃ (d : NoiseDelivery) (nodeId : PubKey),
      TransportNodeBinding d nodeId ∧
        ¬ SessionKeyBinding d.toAuthenticatedDelivery

theorem sessionKeyBinding_not_transportNodeBinding :
    ∃ (d : NoiseDelivery) (nodeId : PubKey),
      SessionKeyBinding d.toAuthenticatedDelivery ∧
        ¬ TransportNodeBinding d nodeId

theorem nodeId_fundingKey_independent :
    (∃ (d : NoiseDelivery) (nodeId : PubKey),
      TransportNodeBinding d nodeId ∧
        ¬ SessionKeyBinding d.toAuthenticatedDelivery) ∧
    (∃ (d : NoiseDelivery) (nodeId : PubKey),
      SessionKeyBinding d.toAuthenticatedDelivery ∧
        ¬ TransportNodeBinding d nodeId) :=
  ⟨transportNodeBinding_not_sessionKeyBinding,
    sessionKeyBinding_not_transportNodeBinding⟩
```

**Witnesses.** For the first, `demoUnattributedDelivery` with
`nodeId = pub33 1` (peer static 1, advertised funding 0). For the second,
`demoDelivery` with `nodeId = pub33 1` (peer static 0 = funding 0, but node
binding fails).

**Why it is faithful.** BOLT 8’s static key is “usually the `nodeid`”
(`refs/bolts/08-transport.md:70`); BOLT 2’s `funding_pubkey` is the 2-of-2
multisig key (`refs/bolts/02-peer-protocol.md:755`). LDK Node exposes
`node_id()` from the channel manager, not from the funding key
(`ldk-node/src/lib.rs:1046-1047`). The two equalities are independent
hypotheses in reality; the current model has only the funding one.

**Cost / risk.** Low: two definitions and two witnesses. It does **not** change
`SessionKeyBinding`, so the 20+ `LN-PR-001` target names and downstream
attribution theorems keep their current meaning. Label: model extension
(naming/interface), not a security proof.

### T4 — `NoiseTransportTargets.recvStrict` and ordering lemmas (P1)

**Statement shape**

```lean
def recvStrict (C : TransportCrypto) (w : ReceiveWindow) (expected : Nat)
    (k : SessionKey) (f : TransportFrame) : Option (ReceiveWindow × Nat) :=
  if _h : AeadAccept C k f ∧ f.nonce = expected then
    some ({ seen := f.nonce :: w.seen }, expected + 1)
  else
    none

theorem recvStrict_rejects_skipped
    (C : TransportCrypto) (w : ReceiveWindow) (expected : Nat)
    (k : SessionKey) (f : TransportFrame) (hne : f.nonce ≠ expected) :
    recvStrict C w expected k f = none

theorem recv_accepts_out_of_order :
    ∃ (C : TransportCrypto) (w : ReceiveWindow) (k : SessionKey)
      (f : TransportFrame) (w' : ReceiveWindow),
      recv C w k f = some w' ∧ f.nonce ≠ 0
```

**Non-vacuity.** `recvStrict` accepts `sealFrame k sid expected ct` and returns
`expected + 1`. The `recv_accepts_out_of_order` witness uses nonce 5 from an
empty window in `strictCrypto`.

**Why it is faithful.** BOLT 8 consumes the length nonce and the body nonce
separately and increments the counter after each (`08-transport.md:462-469`,
`:477-487`); LDK does the same in `peer_channel_encryptor.rs:534-544` and
`:597-622`. The current `NonceFresh` is only “not seen before”, so a receiver
can accept nonce 5 before nonce 0. This target adds the expected-next check as
an **optional strict receiver** and preserves the permissive `recv` plus its
counterexample.

**Cost / risk.** Low. The two-nonce-per-message schedule is a separate change
to `Crypto/Noise.lean` and should **not** be folded into this target without
maintainer sign-off, because it changes `transportEncrypt`/`transportDecrypt`
semantics. **Label:** model extension (optional strict receiver); the existing
permissive `recv` remains the default.

### T5 — `NoiseTransportTargets.outboundExpectedPeer_mismatch_rejected` (P2)

**Statement shape**

```lean
structure OutboundAttempt where
  expected : PubKey
  session : NoiseSession

def OutboundAttempt.accepts (C : TransportCrypto) (a : OutboundAttempt)
    (f : TransportFrame) : Prop :=
  a.session.peerStatic = a.expected ∧ AeadAccept C a.session.sendKey f

theorem outboundExpectedPeer_mismatch_rejected
    (C : TransportCrypto) (a : OutboundAttempt) (f : TransportFrame)
    (h : a.session.peerStatic ≠ a.expected) :
    ¬ a.accepts C f
```

**Witness.** A session with `peerStatic = pub33 1` and `expected = pub33 0`;
`strictCrypto` seals a frame, and the mismatch conjunct fails.

**Why it is faithful.** This is exactly the LDK outbound contract (`D1`, `D2`).
It is deliberately an interface predicate, not a cryptographic theorem: the
real security comes from `PeerChannelEncryptor::new_outbound` using the expected
node id as the remote static key.

**Cost / risk.** Very low, but it adds little beyond naming the hypothesis.
Priority P2; useful only if the catalog is going to claim outbound peer pinning.
**Label:** interface/model extension; the security content remains external.

### T6 — `NoiseTransportTargets.frame_sessionId_bound` (P2)

**Statement shape**

```lean
def NoiseSession.sessionId (s : NoiseSession) : Nat :=
  s.handshake.transcript.size

def FrameForSession (s : NoiseSession) (f : TransportFrame) : Prop :=
  f.sessionId = s.sessionId

theorem sessionId_not_checked :
    ∃ (C : TransportCrypto) (s : NoiseSession) (f : TransportFrame),
      AeadAccept C s.sendKey f ∧ ¬ FrameForSession s f
```

**Witness.** `demoSession` has transcript size 32; `sealFrame demoSession.sendKey
17 0 ByteArray.empty` is accepted but `17 ≠ 32`.

**Why it is faithful.** `TransportFrame.sessionId` currently has no semantics;
a real transport must not accept a frame from another session. This is a small
but real interface gap. Priority P2. **Label:** interface/model extension.

### T7 — `NoiseTransportTargets.deriveKey_ignores_ephemerals` (P2, scope)

**Statement shape**

```lean
theorem deriveKey_ignores_ephemerals
    (h : NoiseHandshake) (r : NoiseRole) (e₁ e₂ : PubKey) :
    deriveKey { h with initiatorEphemeral := e₁ } r =
      deriveKey { h with initiatorEphemeral := e₂ } r := rfl
```

(And the analogous responder-ephemeral statement.)

**Why it is faithful.** It mechanically records that the key schedule is not a
Noise/HKDF/ECDH schedule: only `transcript.size` and the role tag enter the
key, so two handshakes differing only in ephemeral keys derive the same
`SessionKey`. This is a **scope negative**, not a repair. It should be cited by
`NoiseHandshakeSound` so no reader mistakes it for handshake authentication.

**Cost / risk.** Trivial. It deliberately makes the model look weaker; that is
the point. Priority P2. **Label:** scope negative; no new assumption.

### T8 — `RequestBindingTargets.parseProof_renderProof` (new module, P2, external)

**Statement shape**

```lean
structure RequestProof where
  timestamp : Nat
  method : String
  bodyHash : ByteArray

def renderProof : RequestProof → String
def parseProof : String → Option RequestProof

theorem parseProof_renderProof (p : RequestProof) :
    parseProof (renderProof p) = some p

theorem renderProof_injective : Function.Injective renderProof
```

**Why it is faithful.** It would model only the exact grammar
`request = <unix-seconds> <RpcMethod> <body-sha256>` and its injective
rendering (`ldk-server/docs/request-binding.md:20-37`). It would **not** prove
that the server checks the timestamp, the method, or the body hash, nor that
the HMAC chain is unforgeable. Those are separate assumptions/games.

**Cost / risk.** Medium (new parser/String library surface), but low security
value for `L1-03`. The body-hash binding cannot be derived from
`PrimitiveModel.sha256_collisionResistant` because that law is restricted to
32-byte inputs (`Crypto/Model.lean:53-57`); a 10 MiB body domain would require a
computational collision-resistance game, not an injectivity law. Label:
external/separate lane.

## 5. Assumptions, counterexamples, and non-vacuity risks

### 5.1 Counterexamples that must be preserved

| Target | Line | What it prevents |
|---|---|---|
| `replay_accepted_without_nonce_freshness` | `:884-899` | Dropping `NonceFresh` from `recv`. |
| `key_substitution_without_peer_binding` | `:870-874` | Dropping `AeadKeyBinding` from `accepted_frame_peer_unique`. |
| `looseCrypto_not_keyBinding` | `:877-880` | Treating the loose acceptance relation as peer-binding. |
| `acceptance_not_attribution` | `:905-914` | Concluding `SessionKeyBinding` from AEAD acceptance plus soundness. |
| `noise_does_not_authenticate_payload` | `:919-929` | Deriving attribution from the wire. |
| `noise_peer_not_from_wire` | `:933-947` | Any payload-only peer function. |
| `no_wire_session_binding_function` | `:951-962` | Any payload-only attribution predicate. |
| `accepted_frame_advertised_key_independent` | `:973-978` | Concluding key ownership from transport acceptance. |
| `accepted_frame_wire_carries_no_signature` | `:966-968` | Treating `open_channel` as self-authenticating. |

`noise_transport_nonvacuous` (`:1015-1024`) must remain, but it is not a
sufficient non-vacuity witness for the receive direction: `demoHandshake` sets
`initiatorStatic = responderStatic = pub33 0` (`:742-743`), and `demoWire` sets
`fundingPubKey`, all four basepoints, and `firstPerCommitmentPoint` to the same
`k` (`:775-780`). That collapses node id, funding key, and all per-channel keys
into one value, hiding exactly the distinctions this review is about. A
non-degenerate witness (T1/T2/T3) is required before claiming the receive and
node/funding layers are non-vacuous.

### 5.2 Assumptions that must not be hidden

* **`AeadUnforgeable` is an assumption, not a theorem.** `strictCrypto_unforgeable`
  (`:531-532`) is `fun _ _ h => h` because `produced := accept`. It says
  nothing about ChaCha20-Poly1305. `AeadKeyBinding` is likewise explicit
  (`:540-542`).
* **`NoiseHandshakeSound` is only a derivation equality.** It does not say the
  peer holds the static secret, that the transcript was honestly produced, or
  that the handshake used ECDH/HKDF. T7 makes this visible.
* **`deriveKey` puts `peer` into the key by definition.** Therefore
  `session_sendKey_peer` and `accepted_frame_bound_to_peer` are largely
  structural projections. They must not be cited as “the handshake authenticated
  the peer”.
* **`TransportAuthenticated` is a Boolean flag.** `toAuthenticatedDelivery_authenticated`
  (`:594-595`) is `rfl`; `TransportAuthTargets.lean:150-151` is the definition.
  It is not evidence that a handshake occurred.
* **`SessionKeyBinding` is exactly `peerKey = fundingPubKey`.** It is not node-id
  authentication, and it does not imply key ownership. The catalog row already
  says this (`docs/THEOREM-INDEX.md:62`), but the name invites the stronger
  reading.
* **`authenticated_frame` attribution is conditional on the explicit
  peer/advertisement equality.** `sessionKeyBinding_iff_peerStatic_eq`
  (`:599-602`) is `Iff.rfl`; there is no cryptographic bridge.
* **The network assumption says only “a peer identity”.**
  `docs/ASSUMPTIONS.md:112-113` treats the transport as an ideal authenticated
  channel with a peer identity. It does not say that identity is the
  `funding_pubkey`; that equality is a separate modelling decision encoded in
  `SessionKeyBinding`.

### 5.3 Proposals that would weaken or mislead

1. **Do not replace `sendKey` with `recvKey` in `accepted_frame_bound_to_peer`.**
   The resulting statement is false; T2 is the counterexample. Add T1’s
   two-session view instead.
2. **Do not drop `AeadUnforgeable` or `AeadKeyBinding`.** The existing
   counterexamples (`:870-880`) show both are needed for the uniqueness claims.
3. **Do not rename `SessionKeyBinding` to a node-id binding in place.** The
   current equality is used by the entire `LN-PR-001` target list and by
   `TransportAuthTargets`/`OpenChannelRoutingTargets`. Add T3’s separate
   `TransportNodeBinding` and keep the existing law explicit.
4. **Do not claim `NoiseHandshakeSound` implies handshake authentication.** T7
   shows the key schedule ignores ephemerals; there is no signature or
   proof-of-possession.
5. **Do not treat `strictCrypto` as an AEAD model.** `strictAccept` checks only
   key identity, peer, and `nonce + size`; ciphertext bytes are unconstrained.
   A frame with the same nonce/size and different ciphertext is accepted. This
   is a fidelity gap, not a security proof.
6. **Do not derive request binding from `sha256_collisionResistant`.** The law
   is only for 32-byte inputs (`Crypto/Model.lean:53-57`); gRPC bodies are
   arbitrary-length. A body-hash binding claim needs a separate computational
   assumption or a finite-execution admission.
7. **Do not describe LDK Server TLS as client-authenticated.** The server uses
   `with_no_client_auth()` (`tls.rs:417`); clients authenticate with macaroons.
   Server authentication depends on certificate pinning (`api-guide.md:122-124`).
8. **Do not describe `NonceFresh` as BOLT 8 nonce ordering.** It is a
   set-membership replay filter; `recv` accepts out-of-order nonces and the
   one-increment-per-message model does not match BOLT 8’s two increments.

## 6. Wave-13 recommendation

**Verdict: defer; treat `L1-03` as an external/human barrier.** There is no safe
security implementation lane that closes the current gap. The real requirement
is a concrete Noise_XK + AEAD implementation with key ownership and a
computational authentication argument; adding more finite models around the
existing `deriveKey`/`strictCrypto` definitions would repeat the wave-12
conclusion (`agents/reports/swarm12/S12-POST-INTEGRATION-AUDIT.md:61`, `:68-77`).
`docs/OPEN-ISSUES.md:49` already records `L1-03` as blocked for exactly these
reasons (real Noise/AEAD + key ownership external; model-level flag/equality
only).

What is worth doing, **only if the parent explicitly overrides the S12
“no wave-13 proof lane” decision**, is a small additive fidelity lane:

1. **T1 + T2** — supply the correct receive-direction theorem and preserve its
   counterexample, then stop citing the send-key delivery theorem for inbound
   attribution. This is the single highest-value change because the current
   positive theorem is directionally wrong for a receiving session.
2. **T4** — add an optional strict receiver with expected-next-nonce semantics,
   keeping the permissive `recv` and its replay counterexample.
3. **T3** — add the node-id/funding-key separation as naming and witnesses, not
   as a replacement for `SessionKeyBinding`.

Do **not** include T5, T6, T7, or T8 in a security lane. T5/T6 are interface
completeness; T7 is a scope negative; T8 is a separate API-security model with
an external cryptographic assumption. None closes `L1-03`.

For the LDK Server surface: TLS, macaroons, request binding, and Tor are a
different trust boundary from BOLT 8 peer transport. They should be recorded as
**out of scope for `L1-03`** and, if pursued, handled in a separate lane with a
clear statement that TLS server authentication is certificate-pinning-based and
client authentication is macaroon-based, not mTLS.

**Top proposed target:** `NoiseTransportTargets.recv_frame_bound_to_remotePeer`
(T1), paired with `recvKey_not_peerStatic_witness` (T2).

## 7. Evidence and commands

All inspection was read-only. No Lean, docs, scripts, tests, vendor, or other
lane’s report was edited. No branch, commit, rebase, or push was performed. No
`cargo` test or whole-tree build was run.

### 7.1 Pins verified

| Repository | Command | Result |
|---|---|---|
| `ln-lean` | `git rev-parse --short HEAD` | `f7f0628` |
| LDK Node | `git -C /tmp/opencode/ldk-refs/ldk-node rev-parse HEAD` | `fa123fed131e27ecc420b77fa7086fcf1ddaebb8` |
| LDK Server | `git -C /tmp/opencode/ldk-refs/ldk-server rev-parse HEAD` | `c17dc11dde38f88c53457039ddf30c6b90a63ba2` |
| rust-lightning | `git -C refs/rust-lightning rev-parse --short=12 HEAD` | `fe4900930c6b` |

### 7.2 Commands used

```bash
# Catalog / traceability placement
grep -n '^| `LN-PR-001`' docs/THEOREM-INDEX.md docs/TRACEABILITY.md
grep -n '^| `LN-SEC-007`' docs/THEOREM-INDEX.md docs/TRACEABILITY.md
nl -ba docs/THEOREM-INDEX.md | sed -n '55,90p;325,340p'
nl -ba docs/TRACEABILITY.md | sed -n '35,70p'

# Lean claim surface
nl -ba LnLean/Proofs/Protocol/NoiseTransportTargets.lean | sed -n '1,260p'
nl -ba LnLean/Proofs/Protocol/NoiseTransportTargets.lean | sed -n '260,520p'
nl -ba LnLean/Proofs/Protocol/NoiseTransportTargets.lean | sed -n '520,720p'
nl -ba LnLean/Proofs/Protocol/NoiseTransportTargets.lean | sed -n '720,1092p'
nl -ba LnLean/Proofs/Protocol/TransportAuthTargets.lean | sed -n '1,230p'
nl -ba LnLean/Crypto/Noise.lean | sed -n '1,160p'
nl -ba LnLean/Crypto/Model.lean | sed -n '50,125p'
nl -ba LnLean/Wire/Message.lean | sed -n '350,380p;500,545p'
nl -ba LnLean/Proofs/Bitcoin/FundingAuthTargets.lean | sed -n '425,500p'
nl -ba LnLean/Proofs/Routing/NodeAddressTargets.lean | sed -n '20,35p'

# LDK Node / LDK Server datapoints
nl -ba /tmp/opencode/ldk-refs/ldk-node/src/lib.rs | sed -n '540,560p;1038,1052p;1315,1350p'
nl -ba /tmp/opencode/ldk-refs/ldk-node/src/connection.rs | sed -n '100,180p;200,240p'
nl -ba /tmp/opencode/ldk-refs/ldk-server/ldk-server/src/util/tls.rs | sed -n '45,80p;110,145p;395,425p'
nl -ba /tmp/opencode/ldk-refs/ldk-server/docs/request-binding.md | sed -n '1,90p'
nl -ba /tmp/opencode/ldk-refs/ldk-server/docs/tor.md | sed -n '1,45p'
nl -ba /tmp/opencode/ldk-refs/ldk-server/docs/api-guide.md | sed -n '10,55p;115,135p'

# BOLT anchors and rust-lightning framing
nl -ba refs/bolts/08-transport.md | sed -n '60,75p;150,155p;365,410p;447,510p'
nl -ba refs/bolts/02-peer-protocol.md | sed -n '748,815p'
nl -ba refs/rust-lightning/lightning/src/ln/peer_handler.rs | sed -n '1424,1460p;1487,1520p'
nl -ba refs/rust-lightning/lightning-net-tokio/src/lib.rs | sed -n '470,500p'
nl -ba refs/rust-lightning/lightning/src/ln/peer_channel_encryptor.rs | sed -n '510,555p;585,630p'

# Module hygiene and interface connectivity
rg -n "sorry|admit|axiom|native_decide" LnLean/Proofs/Protocol/NoiseTransportTargets.lean
rg -n "^(theorem|def|structure|abbrev) " LnLean/Proofs/Protocol/NoiseTransportTargets.lean
rg -n "PrimitiveModel|NoiseState|transportEncrypt|transportDecrypt" LnLean/Proofs/Protocol/NoiseTransportTargets.lean
```

The `sorry`/`admit`/`axiom`/`native_decide` scan returned no matches in the
reviewed module. No `lake` build was run.

### 7.3 Key evidence index

| Claim | Evidence |
|---|---|
| No dedicated BOLT 8 catalog row | `docs/THEOREM-INDEX.md:62`, `:87`; `docs/TRACEABILITY.md:41`, `:66` |
| `SessionKeyBinding` is `peerKey = fundingPubKey` | `TransportAuthTargets.lean:164-165`; `NoiseTransportTargets.lean:599-602` |
| Positive delivery uses `sendKey` | `NoiseTransportTargets.lean:619-627`, `:632-644`, `:648-667`, `:671-688`, `:692-705` |
| Receiving session documented | `NoiseTransportTargets.lean:564-566` |
| `recvKey.peer = ownStatic` | `NoiseTransportTargets.lean:237-240` |
| Degenerate non-vacuity witness | `NoiseTransportTargets.lean:740-746`, `:764-780` |
| `strictCrypto` has `produced := accept` | `NoiseTransportTargets.lean:512-514`, `:531-537` |
| `deriveKey` ignores ephemerals | `NoiseTransportTargets.lean:156-161` |
| One nonce increment per message | `Crypto/Noise.lean:92-103` |
| BOLT 8 two increments + rekey | `refs/bolts/08-transport.md:452-487`, `:489-507`; `peer_channel_encryptor.rs:534-544`, `:597-622` |
| Plaintext transport framing | `Wire/Message.lean:367-371` |
| LDK outbound expected node id | `ldk-node/src/lib.rs:1324-1341`; `src/connection.rs:215-219`; `peer_handler.rs:1424-1430` |
| LDK inbound has no expected id | `ldk-node/src/lib.rs:549-552`; `peer_handler.rs:1487-1503` |
| LDK Server TLS is server-only | `tls.rs:414-420`; `api-guide.md:120-124` |
| Request binding grammar / no single use | `request-binding.md:20-37`, `:61-73` |
| Tor only outbound `.onion` | `tor.md:3-9`, `:21-37`; `connection.rs:121-170` |

### 7.4 Working-tree status

At review time the worktree already contained untracked files from other lanes
and wave-13 orchestration (`agents/briefs/wave13-review/`,
`agents/reports/wave13-review/`, `agents/status/`, `agents/swarm/WAVE-13-REVIEW.*`,
`scripts/gen-review-wave-13.py`, `scripts/launch-review-wave-13.sh`). This lane
added only `agents/reports/wave13-review/R15-bolt8-transport.md`.
