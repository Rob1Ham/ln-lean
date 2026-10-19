# R21 — LDK Server API surface, auth, macaroons, and request binding
**Status:** read-only review
**Pins:** LDK Node `fa123fed131e27ecc420b77fa7086fcf1ddaebb8`, LDK Server `c17dc11dde38f88c53457039ddf30c6b90a63ba2`

## 1. Scope and current Lean surface

**There is no Lean claim about the LDK Server API, macaroons, request binding, gRPC,
or API TLS.** The catalog is 51 BOLT/peer-protocol obligations with 294 resolved
targets (`docs/THEOREM-INDEX.md:3-11`, `docs/TRACEABILITY.md:3-6`). The nearest
rows are `LN-PR-001` (peer `open_channel` transport attribution) and `LN-PR-003`
(invoice / stored-accept attribution); neither is an operator-API claim
(`docs/TRACEABILITY.md:41,43`).

Exact negative searches over `LnLean/**/*.lean`:

| Pattern | Files |
|---|---:|
| `macaroon` | 0 |
| `time-before` | 0 |
| `GetNodeInfo` | 0 |
| `CreateMacaroon` | 0 |
| `permissions` | 0 |
| `gRPC` | 0 |
| `TLS` | 0 |
| `api.LightningNode` | 0 |

There is no `LnLean.Proofs.Server` namespace and no `ApiAuth` module. The only
auth-shaped Lean declarations are about other surfaces:

* `LnLean.Proofs.Protocol.TransportAuthTargets.TransportAuthenticated`
  (`TransportAuthTargets.lean:150`) is literally the flag
  `session.established = true`; `SessionKeyBinding`
  (`TransportAuthTargets.lean:164`) is key equality. Neither mentions HTTP,
  gRPC, a client identity, or a bearer credential.
* `transport_authenticated_attributed` (`TransportAuthTargets.lean:211`),
  `transport_auth_not_from_wire` (`:475`), and
  `authenticated_delivery_no_signature` (`:562`) are about a delivered BOLT 2
  `open_channel`, not about an API request.
* `LnLean.Proofs.Protocol.NoiseTransportTargets.replay_rejected_with_freshness`
  (`NoiseTransportTargets.lean:410`) and
  `accepted_frame_bound_to_peer` (`:460`) are BOLT 8/Noise receive-window
  theorems. The module explicitly disclaims real Noise/AEAD security
  (`NoiseTransportTargets.lean:30-44`).
* `LnLean.Payment.verify_authorized_under_assumption`
  (`LnLean/Proofs/Payment/InvoiceProps.lean:472`) is conditional invoice-signature
  authorization, not API authorization.

**Current trust-boundary text does not cover this surface.** `docs/ASSUMPTIONS.md`
says only that peer messages are authenticated by the Noise transport and treated
as an ideal authenticated channel (`:108-113`), and the TCB is exactly C1–C8 plus
the Lean kernel / `btc-lean` (`:149-152`). `docs/CHARTER.md:64-76` lists only
cryptographic primitives and the L1 seam. The normative rule is that an unlisted
assumption is a bug, not a convenience (`docs/ASSUMPTIONS.md:3-6`). Therefore any
future API-auth theorem must either stay purely structural or add a named
assumption to the normative TCB; it cannot borrow C1/C8 or the Noise layer.

**No counterexample or non-vacuity obligation currently exists for this surface.**
The 51-row catalog has no row to weaken, so this is a missing-surface report, not
a repair of an existing false theorem.

## 2. LDK datapoints (with `file:line`)

### 2.1 API surface

* The server exposes **55 RPCs**. The authorization test enumerates all 55 and
  compares them to the `rpc` declarations in the proto
  (`ldk-server/src/macaroons/authorization.rs:24-97`; first `rpc` at
  `ldk-server-grpc/src/proto/api.proto:1249`). The production mapping is
  `method_authorization` (`ldk-server-grpc/src/permissions.rs:157-239`).
* Transport is gRPC over HTTP/2 with TLS, service prefix
  `/api.LightningNode/` (`docs/api-guide.md:8-14`;
  `ldk-server/src/service.rs:108-110`).
* The gRPC listener is always wrapped in a `tokio_rustls::TlsAcceptor`
  (`ldk-server/src/main.rs:399-413`, accept loop `:727-744`); TLS setup failure
  exits the process (`:407-411`).
* Request body limit is 10 MiB (`ldk-server/src/service.rs:113`), enforced both
  from `content-length` and by a `Limited` body (`:576-606`, `:633-645`).

### 2.2 Macaroon envelope and signature

* A request carries a hex-encoded v2 macaroon in the `macaroon` header, with no
  `Bearer` prefix (`docs/api-guide.md:16-25`; header read at
  `ldk-server/src/service.rs:615`).
* Limits: 4096 binary bytes and 32 first-party caveats
  (`ldk-server-macaroons/src/macaroon.rs:19-22`); hex transport may use either
  case (`docs/request-binding.md:63-65`).
* Parsing rejects unknown fields, third-party caveats, trailing bytes, duplicate
  identifiers, empty caveats, overlong varints, and noncanonical lengths
  (`macaroon.rs:231-270`; negative cases `:411-436`).
* Signature verification recomputes the HMAC-SHA256 chain from
  `HMAC("macaroons-key-generator", root_key)` over identifier and caveats, using
  a constant-time comparison (`macaroon.rs:130-202`, `:273-281`). The token
  identifier is explicitly **untrusted** and is only a root-key selector
  (`macaroon.rs:146-149`; lookup at `ldk-server/src/macaroons/store.rs:172-188`).

### 2.3 Request binding

* The final caveat is `request = <unix-seconds> <RpcMethod> <body-sha256>`
  (`docs/request-binding.md:20-37`; `docs/api-guide.md:31-49`).
* Rendering and parsing are canonical: decimal timestamp without leading zeros or
  sign, method 1–128 ASCII alphanumerics without service/path, exactly 64 lowercase
  hex characters, no extra fields or whitespace (`macaroon.rs:61-104`;
  rejection vectors `:335-370`).
* The digest is SHA-256 of the exact gRPC body, including the five-byte frame
  header `00 || protobuf_length_be32 || protobuf` (`docs/request-binding.md:39-50`;
  `macaroon.rs:46-59`). The empty `GetNodeInfo` vector at Unix time `1800000000`
  has digest `8855508a…c6839a4` (`docs/request-binding.md:52-59`; verified locally
  with `printf '\0\0\0\0\0' | sha256sum`; reference token at
  `ldk-server-macaroons/tests/data/macaroons-v2.txt:9`).
* Exactly one proof is required, in the final caveat position
  (`docs/request-binding.md:35-37`; split-last at
  `store.rs:195-199`). A request proof in any preceding position is an unknown
  condition and is denied (`store.rs:204-206`). A request-bound token cannot be
  used as a reusable credential, and a reusable credential must reserve space for
  the proof (`ldk-server-macaroons/src/credential.rs:14-23`, `:31-41`).
* The server checks method and timestamp **before** reading the body, then checks
  timestamp, method, body hash, revocation, and policy expiry **after** reading
  the body and before dispatch (`store.rs:190-208`, `:210-233`;
  `service.rs:615-646`). Rejected requests do not poll the body
  (`service.rs:718-747`); expiry during a slow body read is rejected
  (`service.rs:829-872`).

### 2.4 Policy caveats and permissions

* `permissions = …` intersects with the current set; a non-admin token cannot
  gain `admin` by adding `permissions = admin`
  (`ldk-server/src/macaroons/policy.rs:77-84`; test
  `ldk-server/src/macaroons/store/tests/requests.rs:44-70`).
* `time-before = τ` is strict: `now >= τ` rejects (`policy.rs:85-93`);
  malformed or noncanonical values are rejected (`:86-90`; test
  `requests.rs:70-77`).
* `method = X` allows `X` and `GetPermissions`, but not another RPC
  (`policy.rs:94-98`). `GetPermissions` still requires a valid, unexpired
  macaroon (`docs/api-guide.md:61-62`; test `requests.rs:128-161`).
* `admin` is all-permissions within mapped RPCs, but an unmapped RPC returns
  `UNIMPLEMENTED` even for admin (`docs/api-guide.md:92-94`;
  `service.rs:625-630`; test `service.rs:726-736`).
* The permission set is 19 strings including `admin`; the mapping is a finite
  total function with `Permission`, `AuthenticatedOnly`, and `Unknown`
  (`ldk-server-grpc/src/permissions.rs:31-71`, `:157-239`).

### 2.5 Delegation and revocation

* `CreateMacaroon` creates a new root with a fresh secret and ID, inherits the
  caller's caveats, and rejects requested permissions the caller's effective
  permissions do not contain unless the caller is admin
  (`store.rs:264-315`, especially `:271-297`; `policy.rs:142-158`).
* Request proofs are **not** inherited by children; `method = CreateMacaroon`
  is not inherited either (`requests.rs:233-255`; `docs/request-binding.md:35-37`).
* `RevokeMacaroon` revokes by 32-hex ID, removes the root from memory and disk,
  and refuses to revoke the final unrestricted admin (`store.rs:324-380`,
  especially `:341-357`).
* Derived copies share the identifier and are all revoked; separately created
  child roots have distinct identifiers and survive the parent's revocation
  (`docs/api-guide.md:76-82`; same-id test `requests.rs:112-124`).
* Revocation and expiry block new requests but do **not** close existing event
  streams (`docs/api-guide.md:84-85`; end-to-end test
  `e2e-tests/tests/macaroons.rs:309-337`).

### 2.6 Replay

* The request binding is not single-use. The same token/method/body is accepted
  repeatedly while its timestamp is fresh (`docs/api-guide.md:46-47`;
  `docs/request-binding.md:71-73`; deliberate two-use test
  `requests.rs:164-187`, comment at `:171-172`).
* Freshness is `|now - timestamp| <= 60`; exact boundaries 940/1000/1060 at
  `now = 1000` pass, 939 and 1061 fail (`policy.rs:61-66`, `:176-182`;
  service-level offsets `service.rs:679-716`).

### 2.7 TLS and at-rest trust

* TLS is mandatory for the gRPC endpoint; the default certificate is self-signed
  ECDSA P-256, stored as `<storage_dir>/tls.crt` with key at `tls.key`
  (`ldk-server/src/util/tls.rs:51-72`, `:114-140`;
  `docs/api-guide.md:120-127`; `docs/operations.md:105-110`).
* The Rust client pins the supplied server certificate as a root and configures
  `with_no_client_auth`, i.e. there is no client certificate/identity
  (`ldk-server-client/src/client.rs:121-135`, `:852-866`). Authority is the
  bearer macaroon, not a client principal.
* Root keys live in `<network_dir>/macaroons/roots/` with the admin token in
  `admin.macaroon`; files are written with mode `0400`
  (`ldk-server/src/macaroons/persistence.rs:85-125`;
  `docs/operations.md:71-89`). Backups of old roots can restore revoked access
  (`docs/operations.md:84-87`), which is an operational/at-rest assumption, not
  an API-auth theorem.

## 3. Gap matrix

Priority key: **P0** would invalidate a current claim; **P1** is a core auth
invariant worth mechanizing if this surface enters scope; **P2** is secondary,
operational, or external. There is no P0 because no current Lean claim names this
surface.

| Behavior | Lean status | LDK evidence | Gap / counterexample | Priority |
|---|---|---|---|---|
| 55-RPC method dispatch / service path | missing | `authorization.rs:24-97`, `api.proto:1249`, `service.rs:108-110` | No Lean operation inventory or path/method relation; 55 rows are test-only. | P2 |
| v2 macaroon parsing and 4096-byte / 32-caveat bounds | missing | `macaroon.rs:19-22`, `:117-123`, `:231-270` | No model of bounded v2 decoding or canonical rejection. | P2 |
| HMAC signature chain / root-key lookup | missing / external | `macaroon.rs:130-202`, `:273-281`; `store.rs:172-188` | No Lean macaroon MAC assumption; C8 is onion finite-execution binding only (`ASSUMPTIONS.md:22,66-75`). | P1 |
| Request-caveat grammar and canonical rendering | missing | `request-binding.md:20-37`; `macaroon.rs:61-104` | No parser/model; leading zero, sign, uppercase digest, extra field, newline are unmodelled. | P1 |
| Final-caveat position and no reuse as credential | missing | `request-binding.md:35-37`; `store.rs:195-206`; `credential.rs:14-23` | No theorem that a request proof must be final and is not inherited. | P1 |
| Method binding | missing | `store.rs:200-203`, `:219-222` | No theorem that a token bound to `GetNodeInfo` cannot authorize `GetBalances`. | P1 |
| Body-hash binding | missing / external | `macaroon.rs:46-59`; `store.rs:219-222`; `request-binding.md:39-50` | C1 is only 32-byte-preimage collision resistance (`ASSUMPTIONS.md:15,48-64`); it cannot bind arbitrary gRPC bodies. A global `PreimageResistant` hypothesis is uninhabited. | P1 |
| Timestamp tolerance ±60 s, checked before and after body | missing | `policy.rs:61-66`; `store.rs:203,219`; `service.rs:829-872` | No freshness predicate or TOCTOU/recheck theorem. | P1 |
| Replay of an identical request | missing; **contradicted if generalized from Noise** | `api-guide.md:46-47`; `request-binding.md:71-73`; `requests.rs:164-187` | Identical request accepted twice in-window. `NoiseTransportTargets.replay_rejected_with_freshness` has a receive-window state that the API path does not have; it must not be cited for the API. | P1 |
| Permission attenuation / admin non-escalation | missing | `policy.rs:77-84`; `requests.rs:44-70` | No subset theorem; adding `permissions = admin` to a non-admin token must not add `admin`. | P1 |
| CreateMacaroon delegation subset and caveat inheritance | missing | `store.rs:264-315`; `requests.rs:233-255` | No theorem that a child cannot exceed issuer permissions or expiry, or that request proofs are dropped. | P2 |
| Revoke by ID, same-ID copies vs distinct children, final-admin guard | missing | `store.rs:324-380`; `api-guide.md:76-82`; `requests.rs:112-124` | No theorem; the surprising negative is that a distinct child survives parent revocation. | P2 |
| GetPermissions authenticated-only; unknown RPC fail-closed | missing | `policy.rs:94-98`; `service.rs:625-630`; `api-guide.md:61-62,92-94` | No theorem that `GetPermissions` bypasses only method restrictions or that unknown methods are denied even for admin. | P2 |
| TLS server authentication / no client identity / bearer authority | unmodelled / external | `main.rs:399-413`, `:727-744`; `tls.rs:51-72`; `client.rs:852-866` | No Lean TLS model, no client principal. The existing Noise model is peer-to-peer and explicitly not a real Noise implementation. | P1 |
| Root-key / TLS-key at rest, backup restores revoked access | unmodelled / external | `persistence.rs:85-125`; `operations.md:71-89,105-110` | Filesystem permissions and backup rollback are deployment assumptions, not API protocol behavior. | P2 |
| Existing event streams survive revoke/expiry | missing; intentional negative | `api-guide.md:84-85`; `e2e-tests/tests/macaroons.rs:309-337` | A naive model that equates revocation with stream closure would contradict the test. | P2 |
| Peer Noise transport auth / replay freshness | covered faithfully (different surface) | `TransportAuthTargets.lean:150-211`; `NoiseTransportTargets.lean:410-460` | Covers BOLT 8 peer frames with an explicit receive window; **not** HTTP/gRPC or macaroon auth. | — |

## 4. Proposed targets

All targets below are **new work**, not present in the tree. They would live in a
new module such as `LnLean/Proofs/Server/ApiAuthTargets.lean` and a new
`LnLean/Proofs/Server/ApiTrustBoundary.lean` for the external interface. Adding a
catalog row or root import is a parent/integrator decision; this lane does not
propose editing `LnLean.lean`, the catalog, or the TCB file.

### A1 — `LnLean.Proofs.Server.ApiAuthTargets.requestCaveat_parse_render`

**Priority:** P1. **Kind:** model extension (pure).

Statement shape:

```lean
theorem requestCaveat_parse_render
    (b : RequestBinding)
    (hm : ValidMethod b.method)
    (ht : b.timestamp ≤ u64Max)
    (hd : ValidLowerHex32 b.bodyDigest) :
    parseRequestCaveat (renderRequestCaveat b) = some b

theorem requestCaveat_render_injective :
    ∀ b₁ b₂, ValidBinding b₁ → ValidBinding b₂ →
      renderRequestCaveat b₁ = renderRequestCaveat b₂ → b₁ = b₂

theorem requestCaveat_rejects_noncanonical :
    parseRequestCaveat "request = 0123 GetNodeInfo <64hex>" = none ∧
    parseRequestCaveat "request = +123 GetNodeInfo <64hex>" = none ∧
    parseRequestCaveat "request = 123 GetNodeInfo <64HEX>" = none ∧
    parseRequestCaveat ("request = 123 GetNodeInfo " ++ hex ++ " extra") = none
```

**Hypotheses:** `ValidMethod` = 1–128 ASCII alphanumeric; `ValidLowerHex32` = 64
lowercase hex characters; timestamp in `[0, 2^64-1]` with canonical decimal
digits; exactly three fields and no whitespace.

**Non-vacuity:** the published vector
`request = 1800000000 GetNodeInfo 8855508a…c6839a4`
(`docs/request-binding.md:55`) and the signed reference token
(`macaroons-v2.txt:9`). Negative witnesses are the parser's own rejection cases
(`macaroon.rs:345-363`).

**Why faithful:** it is a direct model of `RequestBinding::caveat`/`parse`
(`macaroon.rs:61-104`). **Fidelity risk:** Lean `String`/`Nat` must not silently
accept non-ASCII, leading zeros, or values above `u64`; those are the main proof
obligations. **Feasibility:** high; pure list/string reasoning.

### A2 — `LnLean.Proofs.Server.ApiAuthTargets.accepted_request_body_unique`

**Priority:** P1. **Kind:** model extension plus an explicit finite cryptographic
admission.

Statement shape:

```lean
def BodyDigestBindsOn (D : Body → Digest32) (bodies : List Body) : Prop :=
  ∀ b₁ ∈ bodies, ∀ b₂ ∈ bodies, D b₁ = D b₂ → b₁ = b₂

theorem accepted_request_body_unique
    (D : Body → Digest32)
    (s : Store) (tok : Macaroon) (m : String) (now : Nat)
    (bodies : List Body) (b b' : Body)
    (hbinds : BodyDigestBindsOn D bodies)
    (h : Accepts s tok m b now) (h' : Accepts s tok m b' now)
    (hb : b ∈ bodies) (hb' : b' ∈ bodies) :
    b' = b
```

**Hypotheses:** `Accepts` includes signature verification, final request proof,
method equality, freshness, policy, and `matches_body`; `bodies` is the finite
set of candidate request bodies for the execution.

**Non-vacuity:** use a toy finite encoding with `Body := Bool`,
`Digest32 := Bool`, and `D := id`. Then `BodyDigestBindsOn D [true, false]`
holds; the conclusion is derived from that hypothesis plus the membership and
acceptance facts, not assumed. The real reference vector supplies an external
SHA-256 datapoint, not a Lean computation. The theorem must not assume
`PreimageResistant sha256`: that predicate is uninhabited with `sha256_size`
(`LnLean/Crypto/Model.lean:58-66`; `docs/ASSUMPTIONS.md:56-64`).

**Why faithful:** `finish_request_at` rejects when
`!request.binding.matches_body(body)` (`store.rs:219-222`), and the proof is
exactly the finite-execution binding shape already used by C8
(`ASSUMPTIONS.md:66-75`). **Fidelity risk:** high if the assumption is stated
globally or called SHA-256 security. **Feasibility:** medium-high, assuming a
small `Body`/`Digest32` model; the real hash is external.

### A3 — `LnLean.Proofs.Server.ApiAuthTargets.replay_witness` and `stale_request_rejected`

**Priority:** P1. **Kind:** model extension (pure state/time).

Statement shape:

```lean
def Fresh (now ts : Nat) : Prop := absDiff now ts ≤ 60

theorem stale_request_rejected
    (s : Store) (tok : Macaroon) (m : String) (body : Body)
    (b : RequestBinding) (now : Nat)
    (h : 60 < absDiff now b.timestamp) :
    ¬ Accepts s tok m body now

theorem replay_witness :
    ∃ (s : Store) (tok : Macaroon) (b : RequestBinding) (body : Body)
      (t t' : Nat),
      t ≠ t' ∧ Fresh t b.timestamp ∧ Fresh t' b.timestamp ∧
      Accepts s tok b.method body t ∧ Accepts s tok b.method body t'
```

**Hypotheses:** for the replay witness, no `time-before` caveat (or both times
before expiry), an existing root, a valid signature, and a matching body. For
the stale theorem, only the freshness condition is relevant; the other checks
must also be present in `Accepts`.

**Non-vacuity:** use `t = 1800000000`, `t' = 1800000001` with the published
empty-`GetNodeInfo` vector; `t = 1800000061` is stale relative to
`1800000000`. The source test deliberately accepts the same header twice
(`requests.rs:171-175`).

**Why faithful:** `check_request_timestamp` uses
`now.abs_diff(timestamp) > 60` (`policy.rs:61-66`), and `finish_request_at`
rechecks it (`store.rs:219`). There is no nonce/used-set in the API path, unlike
`NoiseTransportTargets.recv` (`NoiseTransportTargets.lean:355-416`). **Fidelity
risk:** model `Nat` as `u64`-bounded, and do not present the witness as a
vulnerability; it is intended behavior (`api-guide.md:46-47`). **Feasibility:**
high.

### A4 — `LnLean.Proofs.Server.ApiAuthTargets.attenuate_permissions_subset`

**Priority:** P1. **Kind:** model extension (pure).

Statement shape:

```lean
theorem attenuate_permissions_subset
    (base : List Permission) (cs : List Caveat) (c : Caveat)
    (hc : ValidPolicyCaveat c) :
    Subset (effectivePermissions base (cs ++ [c]))
            (effectivePermissions base cs)

theorem attenuate_admin_not_escalation
    (base : List Permission) (cs : List Caveat)
    (h : admin ∉ effectivePermissions base cs) :
    admin ∉ effectivePermissions base (cs ++ [Caveat.permissions [admin]])
```

**Hypotheses:** `effectivePermissions` implements the source rule: if current
contains `admin`, replace by the caveat's allowed set; otherwise retain only
intersecting permissions; a non-admin caveat containing `admin` is ignored
(`policy.rs:77-84`). `ValidPolicyCaveat` rejects unknown permissions, mixed
admin sets, and empty permission lists (`policy.rs:126-140`).

**Non-vacuity:** a `node:read` token plus `permissions = admin` remains unable to
create an admin child (`requests.rs:44-70`). A disjoint `permissions =
invoices:create` caveat yields the empty set rather than escalation (same test).

**Why faithful:** it is the exact set operation in `check_caveat_at`.
**Fidelity risk:** source comments claim the conditions are idempotent and
order-independent (`store.rs:239-243`); do not assume that, prove it or fix a
canonical order. **Feasibility:** high.

### A5 — `LnLean.Proofs.Server.ApiAuthTargets.createRoot_delegation_invariants`

**Priority:** P2. **Kind:** model extension (pure store relation).

Statement shape:

```lean
theorem createRoot_permissions_subset
    (h : Creates s issuer child s') :
    Subset child.permissions (effectivePermissions issuer) ∨
      admin ∈ effectivePermissions issuer

theorem createRoot_inherits_caveats
    (h : Creates s issuer child s') :
    child.caveats = issuer.caveats

theorem createRoot_drops_request_proof
    (h : Creates s issuer child s') :
    ∀ c ∈ child.caveats, ¬ IsRequestCaveat c
```

**Hypotheses:** `Creates` models the successful path of `create_root`, including
`management_permissions`, permission validation, name/ID uniqueness, and the
issuer-must-still-exist check (`store.rs:264-315`; `policy.rs:142-158`).

**Non-vacuity:** the e2e manager → child → grandchild flow retains the manager's
expiry and drops `request = ` and `method = CreateMacaroon`
(`requests.rs:233-255`; `e2e-tests/tests/macaroons.rs:228-276`). A manager with
only `channels:manage` cannot create a `payments:send` child
(`requests.rs:40-70`).

**Why faithful:** child permissions are exactly the requested set
(`store.rs:269-277`) and the subset check is at `:288-297`. **Fidelity risk:**
the Lean relation must not claim filesystem durability or multi-process
atomicity; those are outside the model. **Feasibility:** medium.

### A6 — `LnLean.Proofs.Server.ApiAuthTargets.revoke_scope_invariants`

**Priority:** P2. **Kind:** model extension (pure admission relation); stream
lifetime is an explicit external/negative boundary.

Statement shape:

```lean
theorem revoke_blocks_same_id
    (h : Revokes s id s') (hc : c.id = id) :
    ¬ Accepts s' c m body now

theorem revoke_preserves_distinct_id
    (h : Revokes s id s') (hc : c.id ≠ id) :
    Accepts s' c m body now ↔ Accepts s c m body now

theorem final_admin_revoke_rejected
    (h : UnrestrictedAdmin c)
    (honly : ∀ d ∈ s.roots, UnrestrictedAdmin d → d.id = c.id) :
    ¬ Revokes s c.id s'
```

**Hypotheses:** `Revokes` includes the `macaroons:manage` check, the
permission-subset check, the target-exists check, and the final-admin guard
(`store.rs:324-380`). `Accepts` is new-request admission only.

**Non-vacuity:** revoking a reader ID invalidates both the reusable token and
same-ID derived copies (`requests.rs:112-124`); a separately created child has a
distinct ID and survives (`api-guide.md:78-82`); the final unrestricted admin
guard is at `store.rs:353-356`. The stream test opens a subscription, revokes,
reconnects (fails), and still receives an event on the existing stream
(`e2e-tests/tests/macaroons.rs:309-337`).

**Why faithful:** the store removes exactly `id` from the roots map
(`store.rs:368`) and rechecks presence after body read (`store.rs:225`).
**Fidelity risk:** do not add a theorem that revocation closes streams; the
source is the opposite. **Feasibility:** medium.

### A7 — `LnLean.Proofs.Server.ApiAuthTargets.method_authorization_fail_closed`

**Priority:** P2. **Kind:** model extension (finite table).

Statement shape:

```lean
theorem unknown_method_rejected
    (h : methodAuthorization m = .unknown) :
    ¬ Authorized s tok m

theorem getPermissions_authenticated_only
    (h : Authenticated s tok now) :
    Authorized s tok getPermissions

theorem getPermissions_bypasses_method_not_auth
    (h : tok.caveats.contains (.method "GetNodeInfo")) :
    Authorized s tok getPermissions ∧
    ¬ Authorized s tok "GetBalances"
```

**Hypotheses:** `Authorized` includes signature, freshness, revocation, policy
expiry, and the method caveat; `getPermissions` is the special
`AuthenticatedOnly` method (`permissions.rs:231-239`).

**Non-vacuity:** a `method = GetNodeInfo` token can call `GetPermissions` but not
`GetBalances` (`requests.rs:128-161`); a reader token is denied `OnchainSend`
(`service.rs:726-736`); admin plus `UnmappedMethod` returns `UNIMPLEMENTED`
(same test; `api-guide.md:92-94`).

**Why faithful:** the source mapping is a total `match` with `_ => Unknown`
(`permissions.rs:157-239`) and the service checks `Unknown` before dispatch
(`service.rs:618-630`). **Fidelity risk:** the Lean table can drift from the
proto; encode all 55 rows and prove `Nodup`/totality, or generate the table from
a checked source list. **Feasibility:** high but tedious.

### A8 — `LnLean.Proofs.Server.ApiTrustBoundary` (external assumption, not a theorem)

**Priority:** P2. **Kind:** external assumption interface.

Statement shape:

```lean
structure ApiTrustBoundary where
  serverCertificatePinned : Prop
  tlsConfidential : Prop
  noClientCertificateIdentity : Prop
  rootKeysSecretAtRest : Prop
  -- No field is proved here, and no field is a Lean axiom.
```

A conditional wrapper may state:

```lean
theorem api_acceptance_conditional_on_boundary
    (B : ApiTrustBoundary) (h : Accepts s tok req now) :
    B.serverCertificatePinned → B.rootKeysSecretAtRest →
      AuthorizedRequest s tok req now
```

**Hypotheses:** the caller must supply `B`; this is an interface, not a proof of
TLS or key secrecy. **Non-vacuity:** two clients with the same macaroon have the
same authority because the client library uses `with_no_client_auth`
(`client.rs:852-866`); the server certificate is self-signed and pinned
(`api-guide.md:120-127`). **Why faithful:** it makes the trust boundary explicit
instead of hiding it in a theorem named “secure”. **Fidelity risk:** high if
presented as a security result. **Feasibility:** only as an assumption record;
there is no Lean TLS model in this tree.

## 5. Assumptions, counterexamples, and non-vacuity risks

### 5.1 Do not borrow C1 for body binding

C1 is `CollisionResistant sha256` on **32-byte payment preimages**, not global
injectivity (`docs/ASSUMPTIONS.md:15,48-64`; `LnLean/Crypto/Model.lean:58-66`).
A request body is an arbitrary gRPC byte string. Assuming
`PreimageResistant sha256` globally is inconsistent with `sha256_size` and is
refuted by `LnLean.Proofs.Crypto.Sha256Props.preimageResistant_vacuous`.
Therefore A2 must use a finite `BodyDigestBindsOn` admission and say so, or
remain external. A theorem taking global SHA-256 injectivity would be vacuous,
not stronger.

### 5.2 Do not borrow C8 for macaroon forgery

C8 is `HmacBindsOn hmac mu msgs` on the finite list of onion
`hop_payloads || associated_data` values (`docs/ASSUMPTIONS.md:66-75`). Global
HMAC injectivity is refuted by `hmacPrf_vacuous`
(`LnLean/Proofs/WaveD/D07.lean:122`; `LnLean/Crypto/Model.lean:84-92`). A concrete
model separation to preserve: define `hmacOnionOnly` to return distinct tags on
two onion messages and `zeros 32` everywhere else. It satisfies `HmacBindsOn`
on the onion pair but maps two distinct macaroon caveats to the same tag, so C8
cannot imply macaroon caveat binding. A future macaroon theorem needs its own
named MAC assumption or an opaque signature relation, not C8.

### 5.3 Do not transfer the Noise replay theorem to the API

`NoiseTransportTargets.replay_rejected_with_freshness`
(`NoiseTransportTargets.lean:410-416`) depends on a `ReceiveWindow` that records
accepted nonces. The API acceptance path has no used-set
(`store.rs:190-233`; `requests.rs:171-175`). The API counterexample is the
published two-use test and A3's replay witness. Conversely,
`NoiseTransportTargets.replay_accepted_without_nonce_freshness`
(`:884`) is a peer-model negative, not an API theorem.

### 5.4 Preserve these negative/boundary results

If A1–A7 are implemented, keep all of the following explicitly, not as comments
that can be optimized away:

* `attenuate_admin_not_escalation`: a non-admin token adding
  `permissions = admin` does not gain admin (`policy.rs:82-84`).
* `revoke_preserves_distinct_id`: a separately created child survives parent
  revocation because its ID differs (`api-guide.md:78-82`).
* `stream_survives_revocation`: revocation/expiry blocks new requests but does
  not close an existing event stream (`e2e-tests/tests/macaroons.rs:309-337`).
* `replay_witness`: identical requests are replayable in the ±60 s window
  (`api-guide.md:46-47`; `requests.rs:171-175`).
* `unknown_method_rejected`: unmapped RPCs are `UNIMPLEMENTED` even for admin
  (`service.rs:625-630`).
* `getPermissions_bypasses_method_not_auth`: method restrictions do not make
  `GetPermissions` unauthenticated (`policy.rs:94-98`).
* `request_proof_not_inherited`: `request = ` is dropped from children
  (`requests.rs:240-255`).
* `final_admin_revoke_rejected`: the last unrestricted admin cannot be revoked
  (`store.rs:353-356`).

### 5.5 Non-vacuity and reference-vector caveats

* The published vector's timestamp `1800000000` is fixed for format checks
  (`docs/request-binding.md:58-59`). A Lean witness must set `now` to that fixed
  value; it must not read a real clock, or the witness is stale.
* The reference token uses test-only root material
  (`macaroons-v2.txt:1-2`). It is a format witness, not production key material.
* The empty `GetNodeInfo` digest was independently verified:
  `printf '\0\0\0\0\0' | sha256sum` gives
  `8855508aade16ec573d21e6a485dfd0a7624085c1a14b5ecdd6485de0c6839a4`.
* If a target models `u64` as unbounded `Nat`, it can accept
  `18446744073709551616`, which the Rust parser rejects
  (`macaroon.rs:80-87`; `docs/request-binding.md:31`). Keep the bound explicit.
* Do not weaken `TransportAuthTargets`/`NoiseTransportTargets` to make an API
  theorem go through. They are already explicit about being model-level flags,
  not real Noise/AEAD (`TransportAuthTargets.lean:26-38`;
  `NoiseTransportTargets.lean:30-44`).

## 6. Wave-13 recommendation

**No safe implementation lane exists for wave 13/14 under the current charter.**
The current catalog has no server-API row, the trust-boundary document lists no
API/TLS/macaroon/at-rest assumption (`docs/ASSUMPTIONS.md:149-152`), and the
existing Noise results are not about HTTP/gRPC. Adding a theorem here would either
be purely structural (and should not be advertised as API security) or would
require new unlisted assumptions, which the normative TCB rule forbids
(`docs/ASSUMPTIONS.md:3-6`).

Recommended disposition:

1. **Record an explicit barrier**, not a new catalog claim: LDK Server API auth
   is an external/unmodelled surface in `ln-lean`; the trust boundary is TLS
   server authentication plus a bearer macaroon, with no client identity.
2. **If the maintainer extends scope**, authorize one P2 pure module containing
   A1, A3, A4, and A7 only. These are direct, source-faithful finite models with
   high feasibility and no crypto overclaim. A2, A5, A6, and A8 should remain
   conditional/external until the TCB is extended and reviewed.
3. **Do not add a catalog row or `proved` status** for API auth in wave 13. The
   honest status is “unmodelled/external”; the current 51/51 catalog is not
   evidence for this surface.
4. **If only one thing is implemented**, implement
   `attenuate_permissions_subset` (A4) plus its negative escalation witness. It
   is the clearest auth invariant that is fully formalizable without inventing a
   TLS or HMAC assumption.

## 7. Evidence and commands

Read-only inspection performed in `/home/ubuntu/ln-lean-repair` and the pinned
clones. No Lean or Cargo build was run; no files outside this report were edited.

```sh
cd /home/ubuntu/ln-lean-repair
git rev-parse HEAD
rg -n -i "macaroon|caveat|time-before|GetNodeInfo|CreateMacaroon|permissions|gRPC|TLS|api.LightningNode" LnLean --glob '*.lean'
rg -n "LnLean\\.Proofs\\.Server|Server\\.Api|ApiAuth" . --glob '!agents/logs/**'
rg -n "theorem replay_rejected_with_freshness|theorem accepted_frame_bound_to_peer" LnLean/Proofs/Protocol/NoiseTransportTargets.lean
rg -n "TransportAuthenticated|SessionKeyBinding|transport_authenticated_attributed" LnLean/Proofs/Protocol/TransportAuthTargets.lean

git -C /tmp/opencode/ldk-refs/ldk-server rev-parse HEAD
sed -n '1,80p' /tmp/opencode/ldk-refs/ldk-server/docs/request-binding.md
sed -n '1,140p' /tmp/opencode/ldk-refs/ldk-server/docs/api-guide.md
sed -n '46,104p' /tmp/opencode/ldk-refs/ldk-server/ldk-server-macaroons/src/macaroon.rs
sed -n '130,233p' /tmp/opencode/ldk-refs/ldk-server/ldk-server-macaroons/src/macaroon.rs
sed -n '61,158p' /tmp/opencode/ldk-refs/ldk-server/ldk-server/src/macaroons/policy.rs
sed -n '172,380p' /tmp/opencode/ldk-refs/ldk-server/ldk-server/src/macaroons/store.rs
sed -n '608,646p' /tmp/opencode/ldk-refs/ldk-server/ldk-server/src/service.rs
sed -n '157,239p' /tmp/opencode/ldk-refs/ldk-server/ldk-server-grpc/src/permissions.rs
sed -n '51,140p' /tmp/opencode/ldk-refs/ldk-server/ldk-server/src/util/tls.rs
sed -n '399,413p' /tmp/opencode/ldk-refs/ldk-server/ldk-server/src/main.rs
sed -n '121,135p;852,866p' /tmp/opencode/ldk-refs/ldk-server/ldk-server-client/src/client.rs
sed -n '164,187p;233,255p;309,337p' /tmp/opencode/ldk-refs/ldk-server/ldk-server/src/macaroons/store/tests/requests.rs /tmp/opencode/ldk-refs/ldk-server/e2e-tests/tests/macaroons.rs

printf '\0\0\0\0\0' | sha256sum
```

Key negative counts at the reviewed tree: 0 Lean files mention `macaroon`,
`time-before`, `GetNodeInfo`, `CreateMacaroon`, `permissions`, `gRPC`, `TLS`, or
`api.LightningNode`; there is no `LnLean.Proofs.Server` namespace. The 51-row
catalog and 294 targets are unchanged by this review.
