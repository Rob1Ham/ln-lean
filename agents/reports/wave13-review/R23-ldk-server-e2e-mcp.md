# R23 — LDK Server e2e tests, MCP, gRPC, and CLI/client

**Status:** read-only review
**Pins:** LDK Node `fa123fed131e27ecc420b77fa7086fcf1ddaebb8`, LDK Server `c17dc11dde38f88c53457039ddf30c6b90a63ba2`

## 1. Scope and current Lean surface

This lane reviews the pinned LDK Server test and API surface: `e2e-tests/`
(regtest, MCP, macaroon, config, PostgreSQL), `ldk-server-mcp/`,
`ldk-server-grpc/`, `ldk-server-cli/`, and `ldk-server-client/`. The question is
narrow: which behavioral assertions in those suites are deterministic and
stable enough to become pinned differential fixtures for the Lean conformance
suite, and which are live-only, infrastructure-specific, or external.

### 1.1 Existing catalogue claim surface

There is **no Lean module for LDK Server, MCP, gRPC, macaroons, request binding,
CLI parsing, or server event projection**. The server API is not mentioned in
`docs/THEOREM-INDEX.md`; the closest rows are:

| Claim | What it actually covers | Relevance to this lane |
|---|---|---|
| `LN-PR-001` (`docs/THEOREM-INDEX.md:62`) | BOLT 2 `open_channel` bounds, routed funding, transport attribution, Noise-shaped delivery. | Only the *channel-establishment* half of the server lifecycle; no server API, event stream, or auth. |
| `LN-SEC-007` (`docs/THEOREM-INDEX.md:87`) | Non-vacuity witness registry. | Nothing server-specific. |
| `CONF-01` (`docs/OPEN-ISSUES.md:68`) | P2, open: five live BOLT 2 payload rows, finite/public-API comparison, “not node-level interop.” | Confirms the existing conformance programme deliberately stops at finite wire rows. |
| `CONF-02`, `CONF-03` (same file) | Closed live rust-lightning transcript and promoted transport framing. | The harness is a rust-lightning differential harness, not a general server-API harness. |

The current conformance surface is therefore a set of finite BOLT 1/2/8 wire
vectors:

* `LnLean/Proofs/ConformanceTargets.lean` — BigSize/TLV `decide` vectors.
* `LnLean/Proofs/ConformanceDiffTargets.lean` — transport framing, finite BOLT 2
  payloads, and the rust-lightning differential fixtures.
* `tests/conformance/vectors.json` — 61 BigSize/TLV, 16 framing, 9
  decoder-boundary cases.
* `tests/conformance/rust-lightning/fixtures.json` — 26 BigSize + 3 TLV + 4 wire
  rows, five live BOLT 2 payloads, 22/22 mutation controls, 200 Lean references
  (`docs/OPEN-ISSUES.md:68`).

### 1.2 Why LDK Server fixtures are not drop-in

`scripts/check-conformance.py:74-78` hard-codes the differential document, the
source checkout, the live probe, the lock file, and the transcript schema:

```python
DEFAULT_DIFF = ROOT / "tests" / "conformance" / "rust-lightning" / "fixtures.json"
DEFAULT_SOURCE = ROOT / "refs" / "rust-lightning"
LIVE_PROBE = ROOT / "tests" / "conformance" / "rust-lightning" / "live_probe.rs"
LIVE_LOCK = ROOT / "tests" / "conformance" / "rust-lightning" / "pinned" / "Cargo.lock"
LIVE_TRANSCRIPT_SCHEMA = "lnlean.rust-lightning.live-transcript.v1"
```

The differential checks require the
`lnlean.rust-lightning.differential.v1` schema and the `fe49009` pin
(`scripts/check-conformance.py:944-966`); the Lean cross-check is built around
the wire-vector syntax (`tests/conformance/README.md:1-10`, “Adding a vector
means adding the JSON row, the corresponding theorem(s) …”). LDK Server has a
different repository, a different pin (`c17dc11d…`), no `refs/ldk-server`
checkout in this worktree, and no `bytes [...]` payload shape. A server suite
needs either a second checker or a generalized schema; it cannot be appended to
`fixtures.json`.

### 1.3 Existing model boundaries that matter here

* `LnLean/Channel/State.lean:67-78` has ten `ProtocolEvent` constructors
  (`openChannel` … `closingSigned`). There is no `ChannelPending`,
  `ChannelReady`, `ChannelClosed`, funding outpoint, closure initiator, or
  reason kind. The server event stream is not the protocol event vocabulary.
* `LnLean/Proofs/Protocol/HandshakeProps.lean:127-138` defines
  `finalChannelId o = ⟨o.txid⟩`; the documented gap at `:89` is that BOLT 2's
  big-endian XOR with `funding_output_index` is deliberately omitted. The
  outpoint index is retained but not observable in the id.
* R15 already covers macaroons, request binding, gRPC, and TLS as
  “**Completely unmodelled**”, P2, and proposes a `RequestBindingTargets` parser
  target (`agents/reports/wave13-review/R15-bolt8-transport.md:205-208` and
  `T8`). R23 must not present that as a new finding or a higher-priority lane.
* No existing Lean theorem makes a claim about MCP, JSON-RPC, macaroon
  authorization, CLI parsing, or server events. Consequently this lane cannot
  *contradict* the catalogue; it can only add scope or leave an explicit gap.

## 2. LDK datapoints (with `file:line`)

### 2.1 Test-suite shape: almost everything is live-only

| ID | Datapoint | Evidence | Determinism |
|---|---|---|---|
| D1 | The e2e suites contain 84 test functions across `config.rs`, `e2e.rs`, `macaroons.rs`, `mcp.rs`, `postgres.rs`. 82 construct or delegate to `TestBitcoind`; the two exceptions are a pure CLI/library derivation test and a pure balance-arithmetic test. | Counts from the `#[test]`/`#[tokio::test]` attributes (84 total; 82 live, 2 pure); `e2e-tests/tests/config.rs:17`, `e2e.rs:712`, `macaroons.rs:284`, `mcp.rs:36`, `postgres.rs:83`. | **Live-only**, except D2–D3. |
| D2 | Offline macaroon derivation: library `derive_macaroon(secret, caveats)` must equal the CLI's `derive-macaroon` output for root `"test root"`, id `"test-id"`, and caveats `permissions = node:read`, `method = GetNodeInfo`. | `e2e-tests/tests/macaroons.rs:283-307`. | **Deterministic** (no chain, no network), but needs the built CLI. |
| D3 | Exact channel-funds arithmetic across fee changes: `919_014 + 327 = 919_341 = 919_057 + 284`; a one-satoshi loss must fail. | `e2e-tests/tests/postgres.rs:82-103`. | **Deterministic pure function**, but not a server protocol behavior. |
| D4 | PostgreSQL tests are ignored without `POSTGRES_CONNECTION_STRING`; the remaining tests start a regtest `bitcoind`, servers, mine blocks, and wait for asynchronous events. | `e2e-tests/tests/postgres.rs:106+` and the `#[ignore]` gates; `e2e-tests/src/lib.rs` (`TestBitcoind`, `LdkServerHandle`). | **Live-only / infrastructure.** |

### 2.2 MCP JSON-RPC envelope and dispatch

| ID | Datapoint | Evidence | Determinism |
|---|---|---|---|
| D5 | JSON-RPC error constants: `-32700` parse, `-32601` method-not-found, `-32602` invalid params, `-32603` internal, `-32001` authentication, `-32002` permission. | `ldk-server-mcp/src/protocol.rs:14-19`. | Deterministic. |
| D6 | Error category strings: “Invalid params”, “Internal error”, “Authentication error”, “Permission denied”, default “Error”. | `ldk-server-mcp/src/protocol.rs:39-47`. | Deterministic. |
| D7 | `LdkServerErrorCode` mapping: invalid-request → invalid-params; auth → authentication; authorization → permission; lightning / internal-server / internal → internal. The mapping is total but **not injective**. | `ldk-server-mcp/src/protocol.rs:50-62`; client enum `ldk-server-client/src/error.rs:43-58`. | Deterministic. |
| D8 | Malformed JSON responds with `id: null`, code `-32700`, message `"Parse error"`. Notifications (no `id`) are silently dropped. | `ldk-server-mcp/src/main.rs:95-115`; test `ldk-server-mcp/tests/integration.rs:535-547`; notification test `:420-445`. | Deterministic. |
| D9 | Unknown method returns `-32601` and `"Method not found: <method>"`; `tools/call` without `name` returns `-32602`; `ping` returns `{}`; `initialize` returns the fixed `protocolVersion = "2025-11-25"` and reports `serverInfo.name = "ldk-server-mcp"`, `version = "0.1.0"`. | `ldk-server-mcp/src/main.rs:118-163`; `ldk-server-mcp/src/mcp.rs:12-14`; tests `ldk-server-mcp/tests/integration.rs:147-168`, `:236-252`. | Deterministic. |
| D10 | Server constants: MCP protocol version `"2025-11-25"`, server name, server version. | `ldk-server-mcp/src/mcp.rs:12-14`. | Deterministic, version-specific. |

### 2.3 Tool surface and visibility

| ID | Datapoint | Evidence | Determinism |
|---|---|---|---|
| D11 | Exactly 54 MCP tools, with a literal expected-name list. | `ldk-server-mcp/tests/integration.rs:14-70` (`NUM_TOOLS = 54`). | Deterministic. |
| D12 | Every unary RPC in `ldk-server-grpc/src/proto/api.proto` has an MCP tool, and the tool set equals the snake_case image of the unary RPC names. Streaming RPCs are excluded. | `ldk-server-mcp/tests/integration.rs:171-226`; the textual CamelCase→snake_case conversion is at `:197-216`. | Deterministic, but source-text-derived. |
| D13 | Tool schemas are non-trivial: `onchain_bump_fee` requires `payment_id` and has `fee_rate_sat_per_vb.minimum = 1`; `bump_channel_funding_fee` requires `user_channel_id` and `counterparty_node_id` and has exactly two properties. | `ldk-server-mcp/tests/integration.rs:218-234`. | Deterministic. |
| D14 | `retain_allowed_tools` hides tools the caller cannot call. “Hidden tools stay callable so that a stale list still gets the server's permission error rather than an unknown tool error.” | `ldk-server-mcp/src/tools/mod.rs:79-84`. | Deterministic; **visibility is advisory, not authorization**. |
| D15 | `macaroon_allows`: `AuthenticatedOnly` is always allowed; `Unknown` is never allowed; `Permission(p)` requires `admin` or `p` **and** all `method = …` caveats to match. | `ldk-server-mcp/src/tools/mod.rs:108-127`. | Deterministic. |
| D16 | With no permissions, `tools/list` contains only `get_permissions`; with `node:read`, exactly `export_pathfinding_scores`, `get_balances`, `get_node_info`, `get_permissions`; admin sees every tool; a `method = GetBalances` caveat leaves `get_balances` and `get_permissions`. | `ldk-server-mcp/src/tools/mod.rs:593-625`; live mirror at `e2e-tests/tests/mcp.rs:50-63`. | Deterministic. |
| D17 | Every tool maps to a known RPC method; the registry asserts `rpc_methods.len() == tools.len()` and spot-checks `get_permissions` and `bolt11_receive_for_hash`. | `ldk-server-mcp/src/tools/mod.rs:576-591`. | Deterministic. |

### 2.4 Permissions, presets, and method authorization

| ID | Datapoint | Evidence | Determinism |
|---|---|---|---|
| D18 | 19 permission strings: `admin`, `node:read`, `onchain:receive`, `onchain:send`, `invoices:create`, `payments:read`, `payments:claim`, `payments:send`, `channels:read`, `channels:manage`, `channels:force_close`, `peers:read`, `peers:manage`, `messages:sign`, `messages:verify`, `graph:read`, `utilities:read`, `events:read`, `macaroons:manage`. | `ldk-server-grpc/src/permissions.rs:31-49`, `ALL_PERMISSIONS` at `:52-73`. | Deterministic. |
| D19 | Three presets: `readonly` (8 permissions), `invoice` (11), `admin` (only `admin`). Preset names are exact lowercase strings; unknown names are rejected. | `ldk-server-grpc/src/permissions.rs:75-99`, `:106-133`. | Deterministic. |
| D20 | `method_authorization` maps each RPC name to `Permission(p)`, `AuthenticatedOnly`, or `Unknown`. `get_permissions` is `AuthenticatedOnly`; `SubscribeEvents` is `events:read`; unknown methods are rejected. | `ldk-server-grpc/src/permissions.rs:157-225`. | Deterministic. |

### 2.5 Macaroon caveats and bounds

| ID | Datapoint | Evidence | Determinism |
|---|---|---|---|
| D21 | Request timestamp tolerance is exactly ±60 seconds, inclusive: `now.abs_diff(timestamp) > 60` fails; 940/1000/1060 pass at `now = 1000`; 0/939/1061/`u64::MAX` fail. | `ldk-server/src/macaroons/policy.rs:61-66`; exact-bound test `:176-181`. | Deterministic. |
| D22 | `permissions = …` narrows: an admin token is replaced by the caveat set; a non-admin token intersects with the caveat set. A non-admin token with a `permissions = admin` caveat is **left unchanged**, not escalated and not rejected. | `ldk-server/src/macaroons/policy.rs:74-85`, `:126-140`. | Deterministic. |
| D23 | `time-before = …` requires canonical decimal text (`value == expiry.to_string()`), and rejects when `now >= expiry` (strict at equality). | `ldk-server/src/macaroons/policy.rs:85-94`. | Deterministic. |
| D24 | `method = …` restricts the RPC, with an explicit exception: a holder may always call `GetPermissions` to inspect its own restrictions. Unknown caveats are rejected. | `ldk-server/src/macaroons/policy.rs:94-101`. | Deterministic. |
| D25 | Macaroon v2 limits: 4096 bytes, 32 first-party caveats, 128-byte request method, request-binding caveat format `request = <timestamp> <method> <body-sha256-hex>`. A reusable token must reserve capacity for one request caveat, so it must have fewer than 32 caveats before binding. | `ldk-server-macaroons/src/macaroon.rs:20-32`, `:47-98`, `:163-186`. | Deterministic. |
| D26 | v2 codec rejects wrong version, oversized tokens, unknown fields, third-party caveats, and trailing bytes; `from_hex` bounds the hex length before decoding. | `ldk-server-macaroons/src/macaroon.rs:117-126`, `:205-270`. | Deterministic. |
| D27 | Request binding hashes the exact gRPC body including its frame header; the server checks method, body hash, and timestamp. | `ldk-server-macaroons/src/macaroon.rs:47-98`; R15 D9–D10. | Deterministic grammar; **cryptographic binding external** (R15 §1.4). |

### 2.6 gRPC framing and CLI/client behavior

| ID | Datapoint | Evidence | Determinism |
|---|---|---|---|
| D28 | gRPC frame: 1-byte compressed flag, 4-byte big-endian length, payload. Rejection classes: body < 5 → invalid-argument; flag ≠ 0 → unimplemented; declared length > body → invalid-argument; trailing data → invalid-argument. | `ldk-server-grpc/src/grpc.rs:43-80`; tests `:355-390`. | Deterministic. |
| D29 | `ErrorCode` wire enum: `UnknownError = 0`, `InvalidRequestError = 1`, `AuthError = 2`, `LightningError = 3`, `InternalServerError = 4`; the client adds a synthetic `AuthorizationError` that has no wire enum value. | `ldk-server-grpc/src/error.rs:42-58`; `ldk-server-client/src/error.rs:43-58`. | Deterministic. |
| D30 | CLI amounts accept `<n>sat`, `<n>sats`, `<n>msat`, `<n>msats`; reject bare numbers, empty strings, suffixes without a number, negatives, decimals, and sat overflow (`u64::MAX sat`); `to_sat` rejects non-multiples of 1000 msat. | `ldk-server-cli/src/types.rs:43-117`; tests `:168-235`. | Deterministic. |
| D31 | `AmountOrAll` accepts `"all"` after `trim()`, while `Amount` does **not** trim; so `" all "` is `All`, but `" 5sat "` is invalid. | `ldk-server-cli/src/types.rs:121-147`. | Deterministic edge case. |
| D32 | CLI payment wait: subscribe before send; ignore non-matching payment ids; `PaymentSuccessful` is success, `PaymentFailed` is exit 2, timeout is exit 3 with a latest-details fetch, and event-stream end is an internal transport error. | `ldk-server-cli/src/pay_wait.rs:16-19`, `:47-92`, `:106-160`. | Deterministic as a state machine; **timing/live stream external**. |

### 2.7 Server event lifecycle (live-only)

| ID | Datapoint | Evidence | Determinism |
|---|---|---|---|
| D33 | Pending event: `user_channel_id` matches, `counterparty_node_id` set, `funding_txo` is some, `reason` is none, closure initiator unspecified, `former_temporary_channel_id` non-empty and **not equal** to `channel_id`. | `e2e-tests/tests/e2e.rs:752-765`. | Live-only, sampled. |
| D34 | Ready event: `funding_txo` is some, reason none, initiator unspecified. | `e2e-tests/tests/e2e.rs:804-825`. | Live-only. |
| D35 | Closed event: `funding_txo` is none, a `ChannelStateChangeReasonKind` is present (locally/legacy cooperative, or force-close variants), and `closure_initiator` is `Local` or `Remote`. | `e2e-tests/tests/e2e.rs:846-877` (cooperative), `:1021-1050` (force close). | Live-only. |
| D36 | The force-close variant reuses the same pending/ready/closed shape and additionally checks funding txid stability from the pending outpoint. | `e2e-tests/tests/e2e.rs:881-1050`. | Live-only. |

## 3. Gap matrix

| Behavior | Lean status | LDK evidence | Gap / counterexample | Priority |
|---|---|---|---|---|
| MCP JSON-RPC error code table and categories | **unmodelled** | D5–D7 (`protocol.rs:14-19`, `:39-62`) | No JSON-RPC, MCP, or `LdkServerErrorCode` model. The table is total but not injective: lightning, internal-server, and internal all map to `-32603`. `-32700` has no server-error preimage because it is emitted by the parser (`main.rs:105`). | P2 |
| MCP initialize/ping/notification/malformed behavior | **unmodelled** | D8–D10 (`main.rs:95-163`; `integration.rs:147-168`, `:420-445`, `:535-547`) | No stdio framing, request-id, notification, or “no response” model. A notification is dropped *after* parsing; malformed JSON still returns a response with `id: null`. | P2 |
| 54-tool surface and unary-RPC bijection | **unmodelled** | D11–D13 (`integration.rs:14-70`, `:171-234`) | No tool registry, proto descriptor, or naming model. The test derives snake_case textually, not from protobuf descriptors. Tool count and names are pin-specific. | P2 |
| Permission-filtered `tools/list` | **unmodelled** | D14–D17 (`tools/mod.rs:79-127`, `:576-625`; `mcp.rs:50-63`) | No macaroon view, permission set, or method-caveat filter. Visibility is advisory: hidden tools remain callable. A “hidden” theorem must not be read as “denied.” | P2 |
| Permission names, presets, and RPC→permission mapping | **unmodelled** | D18–D20 (`permissions.rs:31-99`, `:157-225`) | No permission lattice, preset, or method-authorization relation. `admin` is a superuser; presets are fixed; `get_permissions` is authenticated-only; `SubscribeEvents` is streaming-only. | P2 |
| Macaroon permission/time/method caveats | **unmodelled** | D21–D24 (`policy.rs:61-101`, `:176-181`) | No caveat evaluator. Counterexamples that must be preserved: non-admin `permissions = admin` is a no-op (not escalation, not error); `time-before` rejects at `now == expiry`; `method` caveat exempts `GetPermissions`. | P2 |
| Macaroon size/count/request-binding grammar | **unmodelled** | D25–D27 (`macaroon.rs:20-32`, `:47-98`, `:117-126`, `:163-270`) | R15 already declares this unmodelled and proposes the parser round-trip (`R15 T8`). No new claim should be made here; HMAC/SHA-256 binding remains external. | P2 (cross-ref R15) |
| gRPC frame decode and status classes | **unmodelled** | D28 (`grpc.rs:43-80`, `:355-390`) | No gRPC framing model. This is HTTP/2-adjacent infrastructure, not Lightning protocol; finite and easy, but low value. | P2 |
| gRPC/client error enum | **unmodelled** | D29 (`error.rs:42-58`; client `error.rs:43-58`) | `UnknownError = 0` has no client variant; `AuthorizationError` is client-synthetic. Any mapping theorem must state where the extra variant comes from. | P2 |
| CLI amount parsing | **unmodelled** | D30–D31 (`types.rs:43-147`, `:168-235`) | No parser. Edge cases: `" all "` is valid but `" 5sat "` is not; `u64::from_str` accepts a leading `+`; sat overflow is checked. Low protocol value. | P2 |
| CLI payment-wait state machine | **unmodelled** | D32 (`pay_wait.rs:16-19`, `:47-92`, `:106-160`) | No event stream, payment-id filter, deadline, or exit-code model. A matching `PaymentFailed` is a terminal result, not a transport error. | P2 |
| Server channel event lifecycle (`funding_txo`, initiator, reason, temp id) | **unmodelled; live-only** | D33–D36 (`e2e.rs:712-1050`) | `ProtocolEvent` (`Channel/State.lean:67-78`) has no `ChannelPending`/`ChannelReady`/`ChannelClosed`, no funding outpoint, no closure initiator. The `former_temporary_channel_id ≠ channel_id` assertion is a sampled probabilistic fact, not a universal law: both are 32-byte identifiers, so a collision is possible. | P2 (defer) |
| BOLT 2 `channel_id = txid XOR output_index` | **partial; preserved known gap** | `HandshakeProps.lean:89`, `:127-138`; BOLT 2 §1015–1028 | `finalChannelId o = ⟨o.txid⟩`; output index is erased. Two outpoints with the same txid and different indexes are identified. This is the prerequisite for any event-id or id-stability claim. | P1 in a protocol lane; **P2 here** |

**No contradictions.** No current Lean theorem states a server-auth, MCP, CLI, or
event-projection claim, so this lane cannot refute the catalogue. The only
sharp defect it touches is the already-documented `finalChannelId` output-index
omission, which is a model boundary rather than a false server claim.

## 4. Proposed targets

All targets are additive. None weakens an existing theorem. All are P2 for this
lane: they improve the server-API surface, not BOLT wire conformance. The first
three form a coherent, bounded “server auth/envelope” lane; the rest are
defer-or-reject. Proposed namespace: `LnLean.Proofs.Server` (new module), except
T5, which belongs to the existing handshake/protocol layer.

### T1 — `Server.Mcp.errorCode_table` (P2)

**Statement shape**

```lean
inductive RpcErrorCode
  | parseError | methodNotFound | invalidParams | internal
  | authentication | permissionDenied

inductive ServerErrorCode
  | invalidRequest | auth | authorization | lightning | internalServer | internal

def ServerErrorCode.toRpc : ServerErrorCode → RpcErrorCode
  | .invalidRequest   => .invalidParams
  | .auth             => .authentication
  | .authorization    => .permissionDenied
  | .lightning        => .internal
  | .internalServer   => .internal
  | .internal         => .internal

theorem toRpc_auth :
    ServerErrorCode.toRpc .auth = .authentication := rfl

theorem toRpc_not_injective :
    ServerErrorCode.toRpc .lightning =
      ServerErrorCode.toRpc .internalServer := rfl

theorem parseError_no_server_preimage :
    ∀ e : ServerErrorCode, ServerErrorCode.toRpc e ≠ .parseError := by
  intro e; cases e <;> decide
```

**Hypotheses.** The table is transcribed from `protocol.rs:50-62`; `-32700` is
emitted only by the JSON parser (`main.rs:105`), not by a server error.

**Non-vacuity witness.** `toRpc_not_injective` is inhabited by the three-way
collapse to `-32603`; `parseError_no_server_preimage` is inhabited by all six
constructors.

**Why faithful.** This is literally the pinned mapping, including the lossy
collapse, and it records that parse errors are outside the server-error domain.
It is a drift detector, not a protocol theorem.

**Fidelity risk.** High only if the code changes; the pin makes it exact.
**Feasibility.** Very high (`decide`/`rfl`).
**Label.** Model extension; no external assumption.

### T2 — `Server.ToolSurface.unary_tool_bijection` (P2)

**Statement shape**

```lean
structure ToolSpec where
  name : String
  rpc  : String

def registry : List ToolSpec := [...]          -- 54 literal rows
def protoUnaryRpcs : List String := [...]      -- 54 literal unary RPC names
def snakeCase : String → String := ...

theorem tools_length : registry.length = 54 := by decide

theorem unary_tool_bijection :
    (registry.map (·.name)).mergeSort =
      (protoUnaryRpcs.map snakeCase).mergeSort := by decide

theorem streaming_rpc_has_no_tool :
    "subscribe_events" ∉ registry.map (·.name) := by decide
```

**Hypotheses.** `registry` and `protoUnaryRpcs` are committed literal
transcriptions of `integration.rs:15-70` and `api.proto`; the snake_case
conversion is the same textual rule as `integration.rs:197-216`. There is no
protobuf reflection.

**Non-vacuity witness.** `get_permissions` is present, `subscribe_events` is
absent, and the list length is 54. A broken conversion (e.g. failing to split
`Bolt11` into `bolt11`) makes the equality fail.

**Why faithful.** The Rust test asserts exactly this equality. It pins the MCP
surface to the unary RPC surface.

**Fidelity risk.** The literal tables can drift; the textual conversion is not
descriptor-derived. This is a pin-specific surface check, not a spec claim.
**Feasibility.** Medium (large literals; `decide` on strings is workable but
better normalized via `List String` comparison).
**Label.** Model extension; no external assumption.

### T3 — `Server.Authorization.visibleTools_eq_filter` (P2, top target)

**Statement shape**

```lean
structure MacaroonView where
  perms   : Finset Permission
  caveats : List Caveat

def allowed (m : MacaroonView) (t : ToolSpec) : Bool :=
  match methodAuthorization t.rpc with
  | .authenticatedOnly => true
  | .unknown           => false
  | .permission p      =>
      (p ∈ m.perms ∨ admin ∈ m.perms) &&
      m.caveats.all (fun c =>
        match c with
        | .method rpc => rpc = t.rpc
        | _           => true)

theorem visibleTools_eq_filter (m : MacaroonView) :
    visibleTools m = registry.filter (allowed m) := rfl

theorem empty_permissions_only_self :
    visibleTools ⟨∅, []⟩ = [getPermissionsTool] := by decide

theorem admin_sees_all :
    visibleTools ⟨{admin}, []⟩ = registry := by decide

theorem method_caveat_keeps_self :
    getPermissionsTool ∈ visibleTools ⟨{admin}, [.method "GetBalances"]⟩ := by decide
```

**Hypotheses.** `allowed` mirrors `macaroon_allows` (`tools/mod.rs:108-127`),
which itself mirrors the server check; the caveat `method` values are RPC names
(`GetBalances`, not tool names). `visibleTools` is the filtered registry.

**Non-vacuity witness.** The three `decide` facts are exactly the Rust unit
tests at `tools/mod.rs:603-625`: empty permissions see only `get_permissions`;
a `node:read` token sees four tools; a `method = GetBalances` token sees
`get_balances` and `get_permissions`. The last witness is the important one:
the `get_permissions` exception is not vacuous.

**Why faithful.** It captures the server's advertised tool visibility,
including the “hidden but callable” caveat. It does **not** claim that hiding a
tool denies it.

**Fidelity risk.** `allowed` is a *mirror* of a mirror: the ground truth is the
server's auth path, not `tools/mod.rs`. A drift between the mirror and the
server would not be caught by the theorem. This must be stated in the module
docstring.
**Feasibility.** High (finite registry, finite permission set; no crypto).
**Label.** Model extension; no external assumption, but a mirror-fidelity
assumption.

### T4 — `Server.Macaroon.caveat_narrows_permissions` (P2, cross-ref R15)

**Statement shape**

```lean
inductive Caveat
  | permissions (P : Finset Permission)
  | timeBefore (t : Nat)
  | method (rpc : String)
  | unknown

def applyCaveat (c : Caveat) (rpc : String) (P : Finset Permission) (now : Nat) :
    Except AuthError (Finset Permission)

theorem permissions_narrows_nonadmin
    (h : admin ∉ P)
    (hok : applyCaveat (.permissions A) rpc P now = .ok P') : P' ⊆ P

theorem admin_permissions_caveat_replaces
    (h : admin ∈ P) :
    applyCaveat (.permissions A) rpc P now = .ok A

theorem nonadmin_admin_caveat_noop
    (h : admin ∉ P) :
    applyCaveat (.permissions {admin}) rpc P now = .ok P

theorem time_before_admits_iff :
    (∃ P', applyCaveat (.timeBefore t) rpc P now = .ok P') ↔ now < t

theorem method_caveat_exempts_self
    (m : String) (h : rpc = GetPermissions) :
    applyCaveat (.method m) rpc P now = .ok P
```

**Hypotheses.** `validate_permissions` has already rejected empty sets, unknown
permissions, and mixed `admin` + other permissions at mint time. Caveats are
evaluated in order. HMAC verification and request-binding freshness are
separate (R15).

**Non-vacuity witness.** `{node:read}` + `permissions = payments:send` yields
the empty set (an `ok`, not an error); `{admin}` + `permissions = {node:read}`
yields `{node:read}`; a non-admin `{node:read}` + `permissions = {admin}`
yields `{node:read}` unchanged; `time-before = 1000` at `now = 1000` fails;
`method = GetNodeInfo` still permits `GetPermissions`. All are direct
consequences of `policy.rs:74-101`.

**Why faithful.** This is the exact narrowing semantics, including the two
surprising non-escalation cases.

**Fidelity risk.** The model deliberately omits signature verification and
request-body binding; it must not be read as an authentication theorem.
**Feasibility.** High (pure finite sets and `Nat` comparisons).
**Label.** Model extension; crypto external (cross-ref R15 T8).

### T5 — `HandshakeProps.channelIdV1_outputIndex` (P2, cross-lane prerequisite)

**Statement shape**

```lean
def xorLastTwo (txid : ByteArray) (index : Nat) : ByteArray := ...
def channelIdV1 (o : FundingOutpoint) : ChannelId :=
  ⟨xorLastTwo o.txid o.outputIndex⟩

theorem channelIdV1_injective
    {o₁ o₂ : FundingOutpoint}
    (h₁ : o₁.outputIndex < 65536) (h₂ : o₂.outputIndex < 65536)
    (t₁ : o₁.txid.size = 32) (t₂ : o₂.txid.size = 32)
    (h : channelIdV1 o₁ = channelIdV1 o₂) : o₁ = o₂

theorem finalChannelId_collapses_outputIndex
    (txid : ByteArray) :
    finalChannelId ⟨txid, 0⟩ = finalChannelId ⟨txid, 1⟩ := rfl
```

**Hypotheses.** `outputIndex < 65536` (BOLT 2's `funding_output_index` is a
`u16`); the txid is 32 bytes. The XOR is applied big-endian to the last two
bytes, per BOLT 2 §1015–1028 and LDK `types.rs:42-54`.

**Non-vacuity witness.** The same txid with indexes 0 and 1 is identified by the
current `finalChannelId` but separated by `channelIdV1`. The injectivity theorem
is false without the `< 65536` bound, so the bound is doing real work.

**Why faithful.** It repairs the exact gap documented at
`HandshakeProps.lean:89`. It is a prerequisite for any event-id theorem: the
e2e suite checks id stability across pending/ready/closed, but the model cannot
currently distinguish two funding outputs of the same transaction.

**Fidelity risk.** Low; the derivation is BOLT 2-mandated. It touches existing
handshake theorems, so it belongs to the handshake/protocol owner (R05), not to
a server-only lane. **Do not double-count this as an R23 delivery.**
**Feasibility.** Medium (`ByteArray` last-two-byte update; existing
`finalChannelId_injective` remains a corollary for the txid component).
**Label.** Model extension; no external assumption.

### T6 — `Server.Cli.waitForTerminal_matching` (P2, defer)

**Statement shape**

```lean
inductive WaitOutcome
  | success (p : Payment)
  | failed (p : Payment)
  | timedOut (p : Option Payment)
  | transport (e : ServerError)

inductive WaitState
  | waiting
  | done (o : WaitOutcome)

def feed (pid : PaymentId) (deadline : Option Nat) (now : Nat)
    (s : WaitState) (ev : Option Event) : WaitState

theorem nonmatching_ignored
    (h : ev.paymentId ≠ pid) :
    feed pid deadline now .waiting (some ev) = .waiting

theorem success_terminal
    (h : ev = .paymentSuccessful pid p) :
    feed pid deadline now .waiting (some ev) = .done (.success p)

theorem stream_end_is_transport
    (h : deadline = none) :
    feed pid none now .waiting none = .done (.transport (.internal "event stream ended"))

theorem timeout_fetches_latest
    (h : deadline = some d) (h' : now ≥ d) :
    feed pid (some d) now .waiting none = .done (.timedOut (fetchLatest pid))
```

**Hypotheses.** The event stream is not replayed; `fetchLatest` is an abstract
lookup; time is a `Nat`, not wall-clock. `PaymentSuccessful`/`PaymentFailed`
are the only terminal events.

**Non-vacuity witness.** A `PaymentSuccessful` for a different id is ignored; a
matching `PaymentFailed` is `failed`, not `transport`; `None` is `transport`
with the exact “event stream ended before …” message; a timed-out wait with no
details is `timedOut none`.

**Why faithful.** It mirrors `pay_wait.rs:106-160`, including the distinction
between a failed payment (exit 2) and a timeout (exit 3).

**Fidelity risk.** Timing and stream liveness are abstracted; the real CLI can
block indefinitely when `timeout = none`.
**Feasibility.** Medium (state machine is simple, but the proof is not
protocol-relevant).
**Label.** Model extension; live timing external.

### T7 — `Server.Grpc.decodeFrame_bounds` (P2, defer)

**Statement shape**

```lean
inductive GrpcError | invalidArgument | unimplemented | internal

def decodeFrame (b : ByteArray) : Except GrpcError ByteArray
def declaredLen (b : ByteArray) : Nat := ...

theorem short_rejected (h : b.size < 5) : decodeFrame b = .error .invalidArgument

theorem compressed_unimplemented (h : b.get! 0 = 1) :
    decodeFrame b = .error .unimplemented

theorem length_exceeds_body (h : 5 + declaredLen b > b.size) :
    decodeFrame b = .error .invalidArgument

theorem trailing_rejected (h : 5 + declaredLen b < b.size) :
    decodeFrame b = .error .invalidArgument

theorem frame_roundtrip (p : ByteArray) :
    decodeFrame (frame p) = .ok p
```

**Hypotheses.** `len` is the big-endian `u32` at bytes 1–4; compression is not
supported and is signalled as `UNIMPLEMENTED`, not `INVALID_ARGUMENT`.

**Non-vacuity witness.** The four Rust tests at `grpc.rs:355-390`: 3-byte input,
compressed flag 1, declared 10 with 2 present, and a trailing byte. The
round-trip is the positive case.

**Why faithful.** It is the production framing function (`grpc.rs:43-80`), not
the test-only mock service.

**Fidelity risk.** Very low, but this is generic gRPC infra, not Lightning
conformance. It adds little to the catalogue.
**Feasibility.** High.
**Label.** Model extension; no external assumption.

## 5. Assumptions, counterexamples, and non-vacuity risks

1. **The pin is the oracle, not the MCP/JSON-RPC spec.** Constants such as
   `protocolVersion = "2025-11-25"`, 54 tools, 19 permissions, and three presets
   are pinned implementation facts. A target must be labelled
   “LDK Server `c17dc11d` behavior,” not “MCP conformance.”

2. **Visibility is not authorization.** `tools/mod.rs:79-84` says hidden tools
   remain callable so a stale list gets a permission error rather than an
   unknown-tool error. T3 must not be cited as a denial theorem.

3. **`macaroon_allows` is a mirror of a mirror.** The ground truth is the
   server's auth path; `tools/mod.rs` re-implements it for filtering, and the
   proposed Lean `allowed` would re-implement that. A proof about the mirror
   does not prove the server. This is the largest fidelity risk in T3.

4. **Admin is a superuser, but `admin` must be alone.** `validate_permissions`
   rejects `admin` mixed with other permissions (`policy.rs:126-140`). A
   non-admin token with a `permissions = admin` caveat is left unchanged, not
   escalated (`policy.rs:80-84`). Both facts are non-vacuous and easy to get
   wrong.

5. **Time bounds are asymmetric.** Request timestamps are inclusive at ±60
   (`abs_diff > 60` fails); `time-before` is strict at equality (`now >= expiry`
   fails). `time-before` also rejects non-canonical decimal text, so `"01000"`
   and `"+1000"` are errors even though they parse as `1000`.

6. **Macaroon limits reserve a slot.** `MAX_CAVEATS = 32` and
   `attenuate` rejects at `len >= 32`; `check_request_capacity` also rejects at
   `len >= 32` because one request-binding caveat must fit. A reusable token
   therefore has at most 31 pre-existing caveats. A theorem that says “32
   caveats are usable” would be wrong for the request-bound path.

7. **The event assertions are sampled live behavior.** The pending/ready/closed
   checks require regtest, mining, and asynchronous waits. The
   `former_temporary_channel_id ≠ channel_id` assertion
   (`e2e.rs:760-765`) is not a universal theorem: both are 32-byte identifiers,
   and a collision is possible. It is a test of sampled randomness, not a
   safety invariant. Any Lean event model must preserve this as an explicit
   probabilistic/external boundary.

8. **The current `finalChannelId` erases the output index.** The e2e id-stability
   checks cannot be faithfully modeled until T5 (or an equivalent repair) lands.
   Until then, the model can prove agreement on the funding txid but not on the
   full outpoint (`HandshakeProps.lean:30-36`, `:195-211`).

9. **CLI parser edge cases are surprising.** `AmountOrAll` trims only for
   `"all"`; `Amount` does not trim. Rust's `u64::from_str` accepts a leading
   `+`, so `+5sat` is accepted while `" 5sat "` is rejected. Suffix parsing is
   ordered longest-first (`msats`, `msat`, `sats`, `sat`), so `"5msats"` is
   millisatoshis, not `5m` + `sats`.

10. **The gRPC status enum is not the client enum.** `UnknownError = 0` has no
    `LdkServerErrorCode` variant; the client synthesizes `AuthorizationError`.
    Any total mapping theorem must state which side owns the extra constructor.
    The test-only mock service in `grpc.rs:543-665` is not production behavior
    and must not be used as the oracle for status mapping.

11. **PostgreSQL and multi-node tests are external.** They need a live database
    and/or two regtest nodes; they are not fixture material. `test_offline_
    macaroon_derivation` is deterministic but exercises HMAC output, which the
    Lean model does not implement.

## 6. Wave-13 recommendation

**Do not open a P0/P1 implementation lane from R23.** No current Lean theorem
can be wrong about the server API, because the server API is not modelled. The
e2e suite is 82/84 live-only, and the two deterministic tests are a CLI/library
derivation check and a balance-arithmetic check, neither of which is a BOLT
conformance oracle. Treat node-level e2e, channel lifecycle under regtest,
MCP-over-live-server, PostgreSQL persistence, and gRPC-over-TLS as an
**external/human barrier**, consistent with `CONF-01`'s “not node-level interop”
caveat.

If the parent wants to broaden the conformance programme beyond BOLT wire
vectors, the only defensible bounded lane is a **new P2 “LDK Server API”
catalogue item**, not an extension of `CONF-01`:

* Implement **T1 + T3 + T4** as one small `LnLean.Proofs.Server` module:
  JSON-RPC error table, the literal 54-tool registry and visibility filter, and
  macaroon caveat narrowing. Use T2's literal registry data but keep the
  unary-RPC bijection theorem optional. These targets are deterministic, have
  direct Rust unit-test witnesses, and need no chain or network.
* Add a separate `tests/conformance/ldk-server/` suite with a new schema
  (e.g. `lnlean.ldk-server.differential.v1`) and a source pin note for
  `c17dc11d…`. Do **not** append server rows to
  `tests/conformance/rust-lightning/fixtures.json`; the checker is
  rust-lightning-specific (`scripts/check-conformance.py:74-78`, `:944-966`).
* Keep T2 and T7 as optional drift detectors; they are surface/infra checks,
  not protocol theorems.
* Defer T5 to the handshake/protocol owner (R05) and cross-reference it there.
  Do not land it twice.
* Reject T6 as a Lean target; the CLI wait is a UI convenience state machine,
  and its live timing is external.

Recommended verdict: **defer** the whole server-API lane to wave 14 (or a
dedicated server-conformance wave), with **T3** as the top target if the parent
chooses to proceed. No code, Lean, script, test, or vendor edits were made in
this review.

## 7. Evidence and commands

Read-only inspection performed in `/home/ubuntu/ln-lean-repair` and the pinned
checkout `/tmp/opencode/ldk-refs/ldk-server`:

```sh
git -C /tmp/opencode/ldk-refs/ldk-server rev-parse HEAD
# c17dc11dde38f88c53457039ddf30c6b90a63ba2

git -C /home/ubuntu/ln-lean-repair rev-parse --abbrev-ref HEAD
# repair/integrated

ls refs
# PINNED.md  bolts  btc-lean  rust-lightning   (no refs/ldk-server)

grep -n 'NUM_TOOLS\|EXPECTED_TOOLS\|test_initialize\|test_tools_list\|test_ping\|test_malformed_json' \
  /tmp/opencode/ldk-refs/ldk-server/ldk-server-mcp/tests/integration.rs
# 14: NUM_TOOLS = 54; 15-70 expected names; 147 initialize; 171 tools/list; 236 ping; 535 malformed

grep -n 'PARSE_ERROR\|METHOD_NOT_FOUND\|INVALID_PARAMS\|INTERNAL_ERROR\|AUTHENTICATION_ERROR\|PERMISSION_DENIED' \
  /tmp/opencode/ldk-refs/ldk-server/ldk-server-mcp/src/protocol.rs
# 14-19 constants; 39-62 category and mapping

grep -n 'ALL_PERMISSIONS\|READONLY_PERMISSIONS\|INVOICE_PERMISSIONS\|fn method_authorization' \
  /tmp/opencode/ldk-refs/ldk-server/ldk-server-grpc/src/permissions.rs
# 52-73 19 permissions; 75-99 presets; 157-225 method mapping

grep -n 'REQUEST_TIMESTAMP_TOLERANCE_SECS\|fn check_caveat_at\|fn validate_permissions' \
  /tmp/opencode/ldk-refs/ldk-server/ldk-server/src/macaroons/policy.rs
# 26/61-66 timestamp; 74-103 caveats; 126-140 permission validation

grep -n 'MAX_MACAROON_BYTES\|MAX_CAVEATS\|REQUEST_CAVEAT_PREFIX\|fn check_request_capacity' \
  /tmp/opencode/ldk-refs/ldk-server/ldk-server-macaroons/src/macaroon.rs
# 20-32 limits; 62-98 request caveat; 180-186 capacity

grep -n 'fn amount_parsing_and_conversion\|fn pay_and_wait\|fn wait_for_terminal_event' \
  /tmp/opencode/ldk-refs/ldk-server/ldk-server-cli/src/types.rs \
  /tmp/opencode/ldk-refs/ldk-server/ldk-server-cli/src/pay_wait.rs
# types.rs:173; pay_wait.rs:47 and :106

grep -n 'fn test_subscribe_events_channel_state_lifecycle' \
  /tmp/opencode/ldk-refs/ldk-server/e2e-tests/tests/e2e.rs
# 712 cooperative; 881 force-close

grep -n 'fn test_offline_macaroon_derivation\|fn test_channel_funds_preserve' \
  /tmp/opencode/ldk-refs/ldk-server/e2e-tests/tests/macaroons.rs \
  /tmp/opencode/ldk-refs/ldk-server/e2e-tests/tests/postgres.rs
# macaroons.rs:284; postgres.rs:83

grep -n 'DEFAULT_DIFF\|DEFAULT_SOURCE\|LIVE_TRANSCRIPT_SCHEMA' \
  /home/ubuntu/ln-lean-repair/scripts/check-conformance.py
# 74-78 rust-lightning-specific harness constants

grep -n 'finalChannelId\|outputIndex' \
  /home/ubuntu/ln-lean-repair/LnLean/Proofs/Protocol/HandshakeProps.lean
# 89 scope note; 111-138 outpoint and txid-only derivation
```

No `lake build`, `cargo test`, network access, or whole-tree build was run. No
file outside this report was created or modified.
