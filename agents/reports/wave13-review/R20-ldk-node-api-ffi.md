# R20 — LDK Node public API, FFI, and bindings compatibility
**Status:** read-only review
**Pins:** LDK Node `fa123fed131e27ecc420b77fa7086fcf1ddaebb8`, LDK Server `c17dc11dde38f88c53457039ddf30c6b90a63ba2`

Review tip: `repair/integrated` in `/home/ubuntu/ln-lean-repair`. No Lean,
catalog, test, vendor, docs, script, or other-lane file was modified. Only this
report was created. No `lake build`, no `cargo test`, and no network access were
used; commands are listed in §7.

---

## 1. Scope and current Lean surface

### 1.1 There is no node-API row and no node-API model

`rg` over `LnLean/`, `docs/`, `tests/`, and `scripts/` finds **no** occurrence of
`NodeConfig`, `NodeStatus`, `NodeError`, `BuildError`, `PageToken`, `uniffi`,
`ldk_node`, or an FFI/binding declaration. The theorem catalog has no row for
node lifecycle, builder configuration, public-API error mapping, FFI string
codecs, or binding compatibility. The relevant catalog and module facts are
therefore *adjacent*, not covering:

| Adjacent Lean artifact | What it actually states | Why it is not coverage |
|---|---|---|
| `LN-CR-004` — `LnLean.Wire.decode_encode` (`docs/THEOREM-INDEX.md:46`) | BigSize encode/decode are inverse on canonical encodings | BOLT wire encoding, not the hex/decimal string codecs at the FFI boundary |
| `LN-CR-005` — `LnLean.Wire.TLVStream.wellFormed_iff_pairwise` (`docs/THEOREM-INDEX.md:47`) | TLV well-formedness iff pairwise strictly increasing types | TLV record layout, not builder/list-length validation |
| `LN-CR-006` — `LnLean.Wire.Message.decode_length` (`docs/THEOREM-INDEX.md:48`) | A Lightning frame's declared length matches consumed payload | Wire frame length, not gRPC framing or the event-queue `u16` prefix |
| `LN-PM-007` — `InvoiceWireTargets.parse_print` (`docs/THEOREM-INDEX.md:80`) | Pre-bech32 BOLT 11 field-list round trip | Invoice fields, not `PaymentId`/`ChannelId`/`NodeAlias` boundary codecs |
| `LnLean.Routing.Gossip.NodeAnnouncement.alias : ByteArray` (`LnLean/Routing/Gossip.lean:200-210`) | An opaque byte array carried in a node announcement; `GossipProps` can update it (`LnLean/Proofs/Routing/GossipProps.lean:546-558`) | No length bound, trim, NUL, display projection, or FFI lift/lower; unrelated to the FFI `NodeAlias` codec |
| `LnLean.Proofs.PhaseC3.PersistenceRecovery` | Channel/peer snapshot and replay (`PersistenceRecovery.lean:1-70,108-170`) | Different carrier (channel state, not the persisted event queue or a paginated object store) |

The existing green state therefore says nothing about "start twice",
"stop twice", "event handled twice", "alias accepted then displayed",
"payment id parsed as a channel id", or "gRPC status mapped to a client error".
No named theorem in the tree is a node-API contract theorem under a different
name.

### 1.2 The documented boundary excludes the natural implementation lane

- `docs/SCOPE.md:20-28` puts "bit-exact BOLT serialization and differential
  conformance", "a verified implementation extracted to Rust", and related
  implementation work outside the scaffold.
- `docs/CHARTER.md:11-14` states the repository is "**not** a re-implementation
  of `rust-lightning`"; it is a mathematical model anchored to BOLTs and
  `rust-lightning` source locations.
- The catalog is property-oriented (safety/liveness of the protocol), not an
  ABI or binding-conformance suite.

A faithful model of LDK Node's public API is possible as a *small contract
model*, but it would be a **new, non-catalog surface** and cannot be presented
as Rust refinement. That classification drives §6.

### 1.3 What "coverage" would have to mean here

For this lane, covered faithfully requires all of:

1. a carrier with the same observable states/inputs (running flag, config,
   queue, token, wire string);
2. a transition/function whose result matches the LDK behavior, including
   error identity;
3. a theorem whose hypotheses are explicit and whose conclusion is not vacuous;
4. a witness/counterexample showing the interesting branch is reachable.

No item in §3 currently satisfies all four. Most are `missing` or `partially
covered`; one is `contradicted` if Node and Server events are unified (a shared
ack model is false for Server). Reusing the opaque alias carrier or the
channel-snapshot persistence carrier would also produce false claims, which is
why they are recorded as adjacent only.

---

## 2. LDK datapoints (with `file:line`)

### 2.1 Node lifecycle and status

- `Node::start` takes the running write-lock, returns `Error::AlreadyRunning`
  if already true, and on any `start_inner` failure calls `self.shutdown()`
  before returning the error (`ldk-node/src/lib.rs:304-318`). Success sets
  `*is_running_lock = true` only at the end of startup (`lib.rs:884`).
- `Node::stop` returns `Error::NotRunning` if the flag is false and sets it
  false only after `shutdown()` (`lib.rs:891-902`).
- `Node::status` copies `is_running` and `config.network` and reads current
  best block/metrics (`lib.rs:951-983`); `NodeStatus` is a record with
  `is_running`, `network`, best block, optional sync timestamps, and node
  features (`lib.rs:2609-2645`).
- `Node::config` returns `self.config.as_ref().clone()` (`lib.rs:985`), i.e. a
  build-time snapshot; there is no mutator on the built node.
- Integration tests assert `start` twice → `AlreadyRunning` and `stop` twice →
  `NotRunning` (`ldk-node/tests/integration_tests_rust.rs:1758,1780,1783,1786`).
- The running gate is **per method, not global**: `unstarted_node_rejects_live_node_apis`
  builds a node without `start`, asserts `bolt11_payment().receive(...)`
  succeeds (`src/builder.rs:2784-2845`, especially the `receive(...).unwrap()`),
  while send/splice/close/connect/sync paths return `NotRunning` (`builder.rs:2816-2900`).
  `Node::stop` docs say "most API methods" return `NotRunning`
  (`lib.rs:889-890`), not all.

### 2.2 Events: peek/ack and persistence

- `next_event` clones the queue front (`ldk-node/src/event.rs:452-455`);
  `next_event`/`next_event_async`/`wait_next_event` all document that the same
  event is returned until `event_handled` (`lib.rs:997-1029`).
- `event_handled` pops the front unconditionally, with **no check that a peek
  occurred** (`event.rs:461-466`), then persists. `event_handled` on an empty
  queue returns `Ok(())`.
- Therefore two acks without an intervening peek drop the next *undelivered*
  event. This is an observable API behavior, not a crash.
- The persisted queue writes `(self.0.len() as u16)` before the elements
  (`event.rs:531-540`) and reads a `u16` length (`event.rs:522`). A queue of
  65,536 events encodes a zero length prefix; the payload is not round-tripped.

### 2.3 Builder/config validation and announcement readiness

- `set_listening_addresses` rejects length > 100 with
  `BuildError::InvalidListeningAddresses`; `set_announcement_addresses` rejects
  > 100 with `InvalidAnnouncementAddresses`; both return before assignment
  (`ldk-node/src/builder.rs:614-644`).
- `set_tor_config` rejects an OnionV2/OnionV3 proxy with
  `InvalidTorProxyAddress` (`builder.rs:646-660`).
- `set_node_alias` calls `sanitize_alias` (`builder.rs:663`), which trims,
  rejects > 32 **bytes**, then zero-pads to `[u8; 32]`
  (`builder.rs:2683-2693`). It accepts embedded NUL and bytes after the NUL.
- `may_announce_channel` returns `Ok` iff `node_alias.is_some()` and
  `listening_addresses` is `Some` and non-empty; otherwise
  `MissingNodeAlias`, `MissingListeningAddresses`, or
  `MissingAliasAndAddresses` (`ldk-node/src/config.rs:549-559`).
- At build time, if announcement addresses are set, `MissingNodeAlias` is
  mapped to `InvalidNodeAlias`, every other announce error to
  `InvalidListeningAddresses`; if only an alias is set, it maps to
  `InvalidListeningAddresses` (`builder.rs:1530-1556`). The mapping is
  many-to-one and condition-dependent.
- `open_announced_channel` and `open_announced_channel_with_all` first check
  running, then map **all three** `may_announce_channel` errors to
  `Error::ChannelCreationFailed` (`lib.rs:1612-1627`, `lib.rs:1698-1712`).

### 2.4 FFI string codecs and binding types

- `hex_utils::to_vec` rejects odd length and any non-hex byte; accepts upper-
  and lower-case hex (`ldk-node/src/hex_utils.rs:10-35`). `to_string` emits
  lower-case (`hex_utils.rs:37-44`).
- `PaymentId` is `hex_utils::to_vec` followed by `try_into::<[u8; 32]>`
  (`src/ffi/types.rs:1052-1066`). `PaymentHash` uses `Sha256::from_str`
  (`types.rs:1088-1102`). `PaymentPreimage`/`PaymentSecret` are 32-byte hex
  (`types.rs:1104-1134`). `ChannelId` requires exactly 32 decoded bytes
  (`types.rs:1136-1151`).
- `UserChannelId` uses `u128::from_str` — **decimal**, not hex — and lowers via
  `to_string` (`types.rs:1153-1160`).
- `NodeAlias` lift is `sanitize_alias`; lower is `Display`
  (`types.rs:1300-1308`). `Display` truncates at the first NUL
  (`refs/rust-lightning/lightning/src/routing/gossip.rs:1500-1517`).
- The UDL declares all of `PaymentId`, `ForwardedPaymentId`, `PaymentHash`,
  `PaymentPreimage`, `PaymentSecret`, `ChannelId`, `UserChannelId`, and
  `NodeAlias` as `[Custom] typedef string`
  (`ldk-node/bindings/ldk_node.udl:370-391,408`). There is no type tag at the
  string boundary.
- The sanitize test with a NUL-sandwiched alias asserts the display equals the
  prefix while the `NodeAlias` values differ
  (`ldk-node/src/builder.rs:2945-2961`), so `lift(lower(a)) ≠ a` for that
  alias.

### 2.5 Error surface

- `NodeError` is `pub use error::Error as NodeError` (`lib.rs:141`). The Rust
  `Error` enum has **67 variants** (`src/error.rs`, `rg -c '^\t[A-Z][A-Za-z0-9]+,'`
  = 67).
- The UDL `[Error] enum NodeError` has the same 67 names in the same order
  (`bindings/ldk_node.udl:149-218`; compared mechanically in §7). This is a
  binding-parity datapoint, not a theorem.
- `AlreadyRunning`, `NotRunning`, `InvalidNodeAlias`, `InvalidListeningAddresses`,
  `InvalidAnnouncementAddresses`, `InvalidTorProxyAddress`, `InvalidPageToken`,
  `ChannelCreationFailed`, and the `Invalid*` codec errors are distinct
  variants; collapsing them at a call site is a real loss of information.

### 2.6 Payment and peer idempotence

- `payment(id)` returns `Ok(None)` when the payment is unknown; it errors only
  if the store read fails (`lib.rs:2353-2356`).
- `remove_payment` delegates to the wallet store (`lib.rs:2358-2360`,
  `src/wallet/mod.rs:3227-3235`), which delegates to `KVStore::remove`. The
  rust-lightning contract says removal "Returns successfully if no data will be
  stored ... independently of whether it was present before"
  (`refs/rust-lightning/lightning/src/util/persist.rs:186-191`).
- `disconnect` logs and ignores a peer-store removal failure, then always
  returns `Ok(())` (`lib.rs:1356-1379`); absent-peer disconnect is effectively
  idempotent. `connect` can still fail with `ConnectionFailed`.

### 2.7 Pagination

- `PaymentDetailsPage` is newest-created-first; a short page does **not** mean
  the last page; callers must iterate until `next_page_token = None`
  (`ldk-node/src/payment/store.rs:47-58`).
- `list_page` does not hold the mutation lock across reads; objects
  created/removed during pagination may or may not be observed, and a page is
  not a point-in-time snapshot (`src/data_store.rs:495-560`, quotation at
  `:498-511`).
- Tests cover reverse creation order (`data_store.rs:1951-1969`), update not
  reordering (`:1971-1986`), token survives restart (`:1988`), no repeats after
  removals + restart (`:2016`), skipping a concurrently removed key (`:2084`),
  `PersistenceFailed` (`:2103`), and malformed token → `InvalidPageToken`
  (`:2110-2120`).

### 2.8 LDK Server client: errors, framing, size limits

- Client constructor is `Result<Self, String>` and parses the macaroon and TLS
  certificate first (`ldk-server/ldk-server-client/src/client.rs:118-135`); this
  is a **separate error domain** from `LdkServerError`.
- `grpc_code_to_error` maps status 3 → `InvalidRequestError`, 9 →
  `LightningError`, 13 → `InternalServerError`, 14 → `InternalError`
  ("stream became unavailable"), 7 → `AuthorizationError`, 16 → `AuthError`,
  and every unknown status → `InternalError`
  (`ldk-server-client/src/client.rs:696-712`). Status 0 is treated as success
  and ignored (`client.rs:722-728`).
- Server `ldk_error_to_grpc_status` maps the **five** server codes
  `InvalidRequestError`, `AuthError`, `AuthorizationError`, `LightningError`,
  `InternalServerError` to statuses 3, 16, 7, 9, 13
  (`ldk-server/ldk-server/src/service.rs:650-657`). `InternalError` is a
  client-only code (`ldk-server-client/src/error.rs:44-75`).
- The composition is non-injective: 14 and every unrecognized status map to
  `InternalError`; the server never emits 14.
- Unary responses are capped at 10 MiB and each stream message at 4 MiB
  (`client.rs:97-102`); a unary body of exactly the cap is accepted and cap+1
  rejected (`client.rs:682-694`, tests `:904-917`). Stream compression flag ≠ 0
  or oversize → `InternalError` (`client.rs:753-790`).
- gRPC framing is a 5-byte header: 1 compressed-flag byte + big-endian `u32`
  length (`ldk-server/ldk-server-grpc/src/grpc.rs:44-80`). Decode rejects <5
  bytes, compressed ≠ 0, declared length overrunning the body, and trailing
  bytes; encode writes flag 0 and the length (`grpc.rs:85-95`).

### 2.9 Node events vs Server events are different contracts

- LDK Node: durable queue, same event replayed until `event_handled`, explicit
  ack (`ldk-node/src/lib.rs:997-1029`).
- LDK Server `SubscribeEvents`: "best-effort", events are not persisted for
  subscribers, **cannot be replayed after reconnecting, and have no client
  acknowledgement**; a bounded capacity-1024 broadcast channel drops events for
  slow subscribers (`ldk-server/docs/api-guide.md:331-340`). BOLT 12 payer-proof
  guidance repeats "Events are not replayed" (`api-guide.md:370`), and
  `PaymentClaimable` notifications are best-effort/not replayed
  (`api-guide.md:404`).
- A single "event ack" model applied to both is therefore **contradicted** by
  the Server contract.

### 2.10 External cryptographic/authentication assumptions

- Macaroon request binding is method + body + time; client and server clocks
  must be within 60 s; the same request may be replayed while the token is
  valid (`ldk-server/docs/api-guide.md:40-48`; `docs/request-binding.md:68-71`).
- TLS certificate validation is done by the HTTP client; `sign_message` /
  `verify_signature` are ECDSA over secp256k1 (`ldk-node/src/lib.rs:2535-2543`).
- Real Noise/AEAD transport and macaroon HMAC unforgeability are not mechanized
  in this repository; they must remain explicit external assumptions.

---

## 3. Gap matrix

Status legend: **missing** = no Lean declaration; **partially covered** = an
adjacent carrier states something weaker/different; **contradicted** = reusing
the adjacent carrier (or a universal claim across APIs) would be false;
**unmodelled/external** = not mechanizable here without a new cryptographic/ABI
assumption.

| Behavior | Lean status | LDK evidence | Gap / counterexample | Priority |
|---|---|---|---|---|
| `start` on a running node → `AlreadyRunning`; `stop` on a stopped node → `NotRunning` | missing | `lib.rs:304-318,891-902`; tests `integration_tests_rust.rs:1758,1780,1783,1786` | No runtime/running carrier; no idempotence or error-identity statement | P1 |
| Failed `start` winds down spawned tasks and returns the error | missing | `lib.rs:313-318`; test `failed_start_winds_down_background_tasks` (`integration_tests_rust.rs:1835`) | Abstract state can model "still stopped"; task cleanup is an implementation effect, not modelled | P2 |
| Per-method running gate, not a global "all APIs stopped" gate | missing | `builder.rs:2784-2900` (`receive` succeeds unstarted; send etc. → `NotRunning`) | A naive global gate is **contradicted**: invoice creation is legal before `start` | P1 |
| `next_event` repeats the same event until `event_handled` | missing | `lib.rs:997-1029`; `event.rs:452-455` | No queue carrier; no peek/ack relation | P1 |
| `event_handled` without a preceding peek pops the front | missing | `event.rs:461-466` | Double-ack drops the next undelivered event; `ack [] = Ok` | P1 |
| Event queue persistence uses a `u16` length prefix | missing | `event.rs:522,531-540` | 65,536 events encode length 0; `decode(encode q) ≠ q` | P2 |
| Builder rejects >100 listening/announcement addresses before assignment | missing | `builder.rs:614-644` | No list-size bound; no "error leaves prior config unchanged" statement | P2 |
| Builder rejects onion Tor proxy | missing | `builder.rs:646-660` | No address-class predicate or error identity | P2 |
| Alias ≤32 **bytes**, trimmed, zero-padded; embedded NUL accepted | partially covered (opaque `alias : ByteArray`, `Gossip.lean:200-210`) | `builder.rs:2683-2693`; test `builder.rs:2945-2961` | Opaque byte array has no validation; it also admits >32 bytes, so reuse would be **contradicted** | P1 |
| `NodeAlias` Display truncates at first NUL; lift/lower is not an identity | missing | `ffi/types.rs:1300-1308`; `gossip.rs:1500-1517` | Counterexample: `"I💖LDK-Node!\0⚡"` lowers to `"I💖LDK-Node!"`; re-lift differs | P1 |
| `may_announce_channel` truth table (alias × nonempty listening) | missing | `config.rs:549-559` | No config predicate or `Open` admission theorem | P1 |
| Build-time announce-error mapping is conditional and many-to-one | missing | `builder.rs:1530-1556` | `MissingNodeAlias` → `InvalidNodeAlias` only when announcement addresses are set | P2 |
| `open_announced_channel` collapses all three announce errors to `ChannelCreationFailed` | missing | `lib.rs:1612-1627,1698-1712` | Non-injective error collapse; callers cannot recover the missing field | P1 |
| FFI hex codecs accept mixed case, reject odd/non-hex, normalize to lowercase | missing | `hex_utils.rs:10-44`; `ffi/types.rs:1052-1151` | No `decode∘encode = id`/injectivity/odd-length theorem | P1 |
| 32-byte string types are structurally interchangeable at the boundary | missing | UDL `:370-391`; `ffi/types.rs:1052-1151` | `PaymentId`, `PaymentHash`, `ChannelId` share one 64-hex-char shape; no type tag | P2 |
| `UserChannelId` is decimal, not hex | missing | `ffi/types.rs:1153-1160` | A 32-digit decimal string is a valid `u128` id; the grammar is disjoint from `ChannelId`'s 64-hex-char grammar | P2 |
| `NodeError` Rust ↔ UDL variant parity (67 names/order) | missing | `error.rs` (67); `ldk_node.udl:149-218` | No mechanical binding-parity check in-tree; a drift would be silent | P2 |
| `payment` unknown id → `Ok(None)` | missing | `lib.rs:2353-2356` | No optional-result contract; "unknown" vs "store failure" not separated | P2 |
| `remove_payment`/`disconnect` absent-target idempotence | missing | `wallet/mod.rs:3227-3235`; `persist.rs:186-191`; `lib.rs:1356-1379` | No idempotence theorem; contrast with `AlreadyRunning`/`NotRunning` | P2 |
| Pagination is newest-first, no repeats under quiescence, short page ≠ last | missing | `payment/store.rs:47-58`; `data_store.rs:495-560`; tests `:1951-2120` | No store/creation-order model; token semantics unmodelled | P2 |
| Pagination is not a snapshot under concurrent mutation | missing | `data_store.rs:498-511` | A "snapshot" theorem would be **contradicted**; must carry a quiescence hypothesis or a may/may-not observation relation | P2 |
| `NodeStatus.is_running` agrees with the lifecycle flag and `config()` is stable | missing | `lib.rs:951-983`, `985`, `2609-2645` | No coherence theorem between status/config/build | P2 |
| Server gRPC status → `LdkServerErrorCode` mapping | missing | `client.rs:696-712` | Unknown/14 both → `InternalError`; non-injective on all statuses | P1 |
| Server `LdkServerErrorCode` → gRPC status mapping | missing | `service.rs:650-657` | Only 5 codes have a server image; `InternalError` is client-only | P2 |
| gRPC frame encode/decode and size limits | missing | `grpc.rs:44-95`; `client.rs:97-102,682-694,753-790` | No frame round-trip, short/trailing/compressed rejection, or cap theorem | P2 |
| Node events (ack/replay) vs Server events (best-effort/no ack) | contradicted (if unified) | `lib.rs:997-1029` vs `api-guide.md:331-340,370,404` | One shared ack model is false for Server; must be two carriers or a parameterized policy | P1 |
| Macaroon binding, TLS validation, ECDSA, Noise/AEAD | unmodelled/external | `api-guide.md:40-48`; `lib.rs:2535-2543` | Cannot be mechanized here without a cryptographic model; state as explicit assumptions | — (external) |

---

## 4. Proposed targets

All names below are **proposed** and do not exist today. Priorities are relative
to this API surface, not a recommendation to admit a catalog row. Unless stated
otherwise, a target is a **model extension** (new definitions/theorems), not an
external assumption. Every target must carry a non-vacuity witness; the witness
is listed.

### T1 — `LnLean.NodeApi.Lifecycle.start_stop_guard` (P1)

**Statement shape**

```lean
structure Runtime where
  running : Bool

def start (s : Runtime) : Except NodeError Runtime
def stop  (s : Runtime) : Except NodeError Runtime

theorem start_alreadyRunning (s : Runtime) (h : s.running = true) :
    start s = .error .alreadyRunning

theorem stop_notRunning (s : Runtime) (h : s.running = false) :
    stop s = .error .notRunning

theorem start_stop_roundtrip (s : Runtime) (h : s.running = false) :
    ∃ s', start s = .ok s' ∧ s'.running = true ∧
          stop s' = .ok { s' with running := false }

theorem start_failure_preserves_stopped (s : Runtime) (e : NodeError)
    (hRun : s.running = false) (hStart : start s = .error e) :
    s.running = false   -- atomic model: a failed start does not mutate s
```

**Hypotheses / boundary.** `start`/`stop` are atomic at this abstraction. The
real `start_inner` spawns tasks before it can fail; `lib.rs:313-318` winds them
down, but task cleanup is not observable in `Runtime`. State that explicitly as
an implementation refinement gap, not as a theorem.

**Non-vacuity witness.** `s := { running := false }` satisfies
`start s = .ok { running := true }` and `stop` then returns the stopped state.
`{ running := true }` witnesses `AlreadyRunning`.

**Why faithful.** Directly mirrors `lib.rs:304-318,891-902`, including error
identity and the success-only flag assignment at `lib.rs:884`.

**Fidelity risk / feasibility.** Low risk, high feasibility (finite state,
`decide`-able). Risk is only that it looks stronger than it is if the task
rollback is silently omitted; the boundary note prevents that.

**Classification.** Model extension (new `NodeApi` contract module).

### T2 — `LnLean.NodeApi.Config.announce_gate` (P1)

**Statement shape**

```lean
structure Config where
  nodeAlias : Option NodeAlias
  listeningAddresses : Option (List SocketAddress)

inductive AnnounceError
  | missingNodeAlias | missingListeningAddresses | missingAliasAndAddresses

def nonemptyListening (c : Config) : Bool
def mayAnnounce (c : Config) : Except AnnounceError Unit
def openAnnounced (running : Bool) (c : Config) : Except NodeError UserChannelId

theorem mayAnnounce_iff (c : Config) :
    mayAnnounce c = .ok () ↔
      c.nodeAlias.isSome = true ∧ nonemptyListening c = true

theorem openAnnounced_rejects (c : Config) (e : AnnounceError)
    (hRun : running = true) (h : mayAnnounce c = .error e) :
    openAnnounced running c = .error .channelCreationFailed

theorem openAnnounced_error_collapse (running : Bool) (hRun : running = true) :
    ∃ c₁ c₂, mayAnnounce c₁ ≠ mayAnnounce c₂ ∧
      openAnnounced running c₁ = .error .channelCreationFailed ∧
      openAnnounced running c₂ = .error .channelCreationFailed
```

**Hypotheses.** `openAnnounced` first requires `running = true`; the collapse
theorem fixes a running node so the announce branch is the only difference.
`Config` is the build-time snapshot (`lib.rs:985`), not a mutable runtime
config.

**Non-vacuity witness.** Alias present + `[addr]` → `mayAnnounce = .ok ()` and
`openAnnounced` proceeds; alias present + `[]` → `MissingListeningAddresses` and
`ChannelCreationFailed`.

**Why faithful.** The truth table is exactly `config.rs:549-559`; the collapse is
exactly `lib.rs:1612-1627,1698-1712`. The build-time conditional mapping
(`builder.rs:1530-1556`) can be a separate lemma over the same predicate.

**Fidelity risk / feasibility.** Low/medium. The only fidelity trap is treating
"announcement addresses set" as the gate; the actual gate is
`listening_addresses`, and announcement addresses are only the build-time error
selector. Encode that distinction.

**Classification.** Model extension.

### T3 — `LnLean.NodeApi.FFI.FixedWidthHex` (P1)

**Statement shape**

```lean
def decodeHex (s : String) : Option (List UInt8)          -- rejects odd/non-hex
def encodeHex (bs : List UInt8) : String                   -- lowercase
def decodeHex32 (s : String) : Option (Vector UInt8 32)
def encodeHex32 (v : Vector UInt8 32) : String

theorem decodeHex_encodeHex (bs : List UInt8) :
    decodeHex (encodeHex bs) = some bs

theorem decodeHex32_encodeHex32 (v : Vector UInt8 32) :
    decodeHex32 (encodeHex32 v) = some v

theorem encodeHex_injective : Function.Injective encodeHex

theorem decodeHex_odd_length (s : String) (h : s.length % 2 = 1) :
    decodeHex s = none

theorem decodeHex_accepts_uppercase (bs : List UInt8) :
    decodeHex (String.map Char.toUpper (encodeHex bs)) = some bs

theorem codecs_are_type_erasing :
    ∀ s, decodePaymentId s = decodePaymentHash s ∧
         decodePaymentId s = decodeChannelId s
```

**Hypotheses.** The last theorem is definitional if the three 32-byte types
share a decoder; if separate definitions are used, prove the sets equal. This is
the formal statement of the UDL `typedef string` hazard, not a claim that LDK
intends type confusion.

**Non-vacuity witness.** `bs = [0x00, 0x01, …, 0x1f]` round-trips;
`"0"` and `"zz"` are rejected; `"AA"` is accepted and lowers to `"aa"`.

**Why faithful.** Mirrors `hex_utils.rs:10-44` and
`ffi/types.rs:1052-1151`. Note `PaymentHash` goes through `Sha256::from_str`,
which is also 32-byte hex; the shape matches.

**Fidelity risk / feasibility.** Low/medium. Risk is the opposite claim: LDK's
`Sha256::from_str` may reject uppercase or have a different accepted grammar.
The report observed `hex_utils` acceptance; do not assert `Sha256` grammar
without a separate check. Keep the shared-decoder theorem scoped to types that
actually use `hex_utils`.

**Classification.** Model extension.

### T4 — `LnLean.NodeApi.FFI.NodeAliasProjection` (P1)

**Statement shape**

```lean
structure NodeAlias where
  bytes : Vector UInt8 32

def sanitizeAlias (s : String) : Except NodeError NodeAlias
def displayAlias (a : NodeAlias) : String       -- truncates at first 0 byte

theorem sanitizeAlias_length (s : String) (a : NodeAlias)
    (h : sanitizeAlias s = .ok a) :
    a.bytes.length = 32

theorem sanitizeAlias_byte_bound (s : String) (a : NodeAlias)
    (h : sanitizeAlias s = .ok a) :
    s.trim.utf8ByteSize ≤ 32

theorem display_sanitize_of_nulFree (s : String)
    (h : ¬ s.contains '\0') :
    (displayAlias <$> sanitizeAlias s) = .ok s.trim

theorem sanitize_display_not_identity :
    ∃ a : NodeAlias, sanitizeAlias (displayAlias a) ≠ .ok a
```

**Non-vacuity / counterexample.** `s := "I💖LDK-Node!\0⚡"` sanitizes to a
32-byte value whose display is `"I💖LDK-Node!"`; re-sanitizing produces a
different alias (`builder.rs:2945-2961`). A 32-character string of 4-byte
code points exceeds 32 bytes and is rejected — this is the byte-vs-char
counterexample.

**Why faithful.** Matches `sanitize_alias` (`builder.rs:2683-2693`) and
`Display` (`gossip.rs:1500-1517`). The NUL-free round-trip is the strongest
true positive statement; the negative theorem preserves the exact boundary.

**Fidelity risk / feasibility.** Low/medium. `String.trim` and `contains` need
a small literal model; no Unicode normalization claim. Do **not** state
`display(sanitize s) = s` unconditionally — it is false.

**Classification.** Model extension.

### T5 — `LnLean.NodeApi.Events.QueueAck` (P2; hand off to R18)

**Statement shape**

```lean
abbrev EventQueue := List Event

def peek (q : EventQueue) : Option Event := q.head?
def ack  (q : EventQueue) : Except NodeError EventQueue
  | []      => .ok []
  | _ :: tl => .ok tl

theorem peek_ack_advances (e : Event) (tl : EventQueue) :
    peek (e :: tl) = some e ∧
    (ack (e :: tl)).map peek = .ok (peek tl)

theorem ack_twice_drops_next (e₁ e₂ : Event) :
    (ack [e₁, e₂]).bind ack = .ok []

theorem ack_empty_ok : ack [] = .ok []

def encodeQueue (q : EventQueue) : ByteArray   -- writes (q.length : UInt16)
def decodeQueue (b : ByteArray) : Option EventQueue

theorem queue_len_truncates (q : EventQueue) (h : q.length ≥ 65536) :
    decodeQueue (encodeQueue q) ≠ some q
```

**Non-vacuity / counterexample.** `[e₁, e₂]` witnesses double-ack dropping
`e₂`; a 65,536-element queue witnesses the `u16` truncation
(`event.rs:522,531-540`). `ack [] = .ok []` is a real success, not an error.

**Why faithful.** Mirrors `event.rs:452-466` and `lib.rs:997-1029`. The
persistence length prefix is exactly the `u16` write/read pair.

**Fidelity risk / feasibility.** Low, but **overlaps R18
(`ldk-node-events-runtime`)**, which owns event-loop ordering/recovery. R20
should propose this as a handoff and not duplicate R18's ordering/restart
theorems.

**Classification.** Model extension; queue persistence is a subset of R18's
surface.

### T6 — `LnLean.NodeApi.Pagination.PageOrder` (P2)

**Statement shape**

```lean
structure Store where
  order : List Key            -- ascending creation order
  pageSize : Nat

def listPage (st : Store) (tok : Option PageToken) : Except StoreError Page
def Quiescent (st : Store) : Prop   -- no add/remove/update during traversal

theorem listPage_newest_first (st : Store) (h : Quiescent st) :
    (listAll st).map (·.key) = st.order.reverse

theorem short_page_not_last :
    ∃ (st : Store) (tok : Option PageToken) (p : Page),
      listPage st tok = .ok p ∧
      p.items.length < st.pageSize ∧ p.next ≠ none

theorem next_none_iff_exhausted (st : Store) (h : Quiescent st)
    (tok : Option PageToken) :
    (listPage st tok).map (·.next) = .ok none ↔
      (listPage st tok).map (·.items.length) = .ok (remainingCount st tok)

theorem concurrent_addition_changes_page :
    ∃ (st st' : Store) (tok : Option PageToken),
      st.order <+: st'.order ∧
      (listPage st tok).map (·.items) ≠
        (listPage st' tok).map (·.items)
```

**Hypotheses.** The positive order/no-repeat theorem carries `Quiescent`;
without it, `data_store.rs:498-511` explicitly denies a snapshot. The
"short page" theorem is unconditional and is the API's "don't stop early"
warning.

**Non-vacuity witness.** Three pages of sizes `pageSize, pageSize, 25` with
ascending inserts (`data_store.rs:1951-1969`); an updated oldest object stays in
place (`:1971-1986`).

**Fidelity risk / feasibility.** Medium. The store semantics (creation order,
token = backend cursor) must be modelled abstractly; the theorem is not a claim
about any particular KV backend. A token model that assumes server-issued
opaque cursors is required.

**Classification.** Model extension.

### T7 — `LnLean.ServerClient.ErrorMapping.StatusMap` (P1)

**Statement shape**

```lean
inductive LdkServerErrorCode
  | invalidRequest | auth | authorization | lightning | internalServer | internal

def statusToCode : Nat → LdkServerErrorCode
def codeToStatus : LdkServerErrorCode → Option Nat
def headersToError : Option (Nat × String) → Option LdkServerError

theorem server_image_roundtrip (c : LdkServerErrorCode) (n : Nat)
    (h : codeToStatus c = some n) :
    statusToCode n = c

theorem statusToCode_not_injective :
    statusToCode 14 = statusToCode 2

theorem unknown_status_collapses (n : Nat)
    (h : n ∉ [3, 7, 9, 13, 14, 16]) :
    statusToCode n = .internal

theorem status_zero_no_error :
    headersToError (some (0, "")) = none   -- status 0 is success, not a code
```

**Non-vacuity / counterexample.** 3 → `InvalidRequestError`, 16 → `AuthError`,
9 → `LightningError`; 14 and an arbitrary unknown status both →
`InternalError`, proving non-injectivity (`client.rs:696-712`). Status 0 is
ignored (`client.rs:722-728`).

**Why faithful.** Direct transcription of the client match arms and the server's
five-code image (`service.rs:650-657`). The asymmetry (client-only
`InternalError`) is preserved.

**Fidelity risk / feasibility.** Low. The only care point is that "unknown
status" is a catch-all, so the theorem must quantify over all naturals outside
the listed set, not just one example.

**Classification.** Model extension; R21 owns macaroons/auth and should not be
duplicated.

### T8 — `LnLean.ServerClient.Grpc.Frame` (P2)

**Statement shape**

```lean
def encodeFrame (p : ByteArray) : ByteArray
def decodeFrame (b : ByteArray) : Except GrpcStatus ByteArray

theorem decode_encode (p : ByteArray) (h : p.size < 2 ^ 32) :
    decodeFrame (encodeFrame p) = .ok p

theorem decode_short (b : ByteArray) (h : b.size < 5) :
    decodeFrame b = .error .invalidArgument

theorem decode_trailing (p junk : ByteArray) (h : junk.size > 0) :
    decodeFrame (encodeFrame p ++ junk) = .error .invalidArgument

def encodeFrameWithFlag (flag : UInt8) (p : ByteArray) : ByteArray

theorem decode_compressed (flag : UInt8) (p : ByteArray) (h : flag ≠ 0) :
    decodeFrame (encodeFrameWithFlag flag p) = .error .unimplemented

theorem unary_cap_accepts_exact :
    checkUnaryLen (10 * 1024 * 1024) = .ok ()

theorem unary_cap_rejects_succ :
    checkUnaryLen (10 * 1024 * 1024 + 1) = .error .internal
```

**Non-vacuity / counterexample.** Empty payload encodes to `00 00 00 00 00`
and decodes to `[]`; a 4-byte body is short; one trailing byte is rejected;
flag `01` is compressed/unsupported (`grpc.rs:44-80`). The cap theorem is the
`> limit` boundary from `client.rs:682-694` (exactly at the cap is accepted).

**Fidelity risk / feasibility.** Low/medium. `ByteArray` size and indexing are
easy; the `u32` overflow hypothesis is necessary because encode asserts
`≤ u32::MAX`.

**Classification.** Model extension.

---

## 5. Assumptions, counterexamples, and non-vacuity risks

### 5.1 Assumptions that must stay explicit

1. **No Rust/FFI refinement.** These targets model observable contracts, not
   the Rust implementation, UniFFI code generation, ABI layout, or the
   Kotlin/Swift/Python binding generators. A passing Lean theorem must never be
   described as "the bindings are correct".
2. **No cryptographic mechanization.** Macaroon HMAC request binding, TLS
   certificate validation, the ±60 s clock window, replay-while-valid, ECDSA
   sign/verify, and Noise/AEAD are external (`api-guide.md:40-48`;
   `lib.rs:2535-2543`). Targets T1–T8 must not depend on their truth.
3. **Atomic lifecycle abstraction.** T1 models `start` atomically; the real
   implementation spawns background tasks and winds them down on failure
   (`lib.rs:313-318`). That cleanup is an implementation refinement obligation,
   not a modelled transition.
4. **Opaque store/token.** T6 treats page tokens as backend-issued opaque
   cursors; it does not model any specific KV backend's pagination.
5. **Quiescence.** T6's order/no-repeat theorem is only true under
   `Quiescent`; `data_store.rs:498-511` explicitly rejects a snapshot reading.
6. **Event policy is per-API.** Node and Server events are not the same
   contract (§2.9); a shared ack model is false as a universal claim. The two
   policies must be separate carriers, or a single carrier must be parameterized
   by an event-delivery policy whose Server instance has no ack/replay.

### 5.2 Counterexamples that must be preserved

- **Alias NUL sandwich.** `sanitizeAlias("I💖LDK-Node!\0⚡")` and
  `sanitizeAlias("I💖LDK-Node!")` are different `NodeAlias` values with the same
  `Display`; `lift(lower(a)) ≠ a` (`builder.rs:2945-2961`). Any unconditional
  round-trip theorem is false.
- **Alias byte/char bound.** A string of at most 32 Unicode scalar values can
  exceed 32 UTF-8 bytes and be rejected (`builder.rs:2683-2693`). The bound is
  bytes, not characters.
- **Double ack.** `ack [e₁, e₂]` twice yields `[]`, dropping `e₂` before it was
  ever returned (`event.rs:461-466`). `event_handled` does not require a peek.
- **`u16` queue length.** 65,536 queued events serialize a zero length prefix;
  the queue does not round-trip (`event.rs:522,531-540`).
- **Announcement error collapse.** All three `AnnounceError`s become
  `ChannelCreationFailed` in `open_announced_channel`
  (`lib.rs:1612-1627,1698-1712`); build-time mapping is a different,
  conditional many-to-one map (`builder.rs:1530-1556`).
- **Pagination is not a snapshot.** Concurrent additions/removals may or may not
  be observed, and updates may reflect different moments
  (`data_store.rs:498-511`). A short page can still have a next token
  (`payment/store.rs:47-58`).
- **gRPC status collapse.** Status 14 and every unknown status both map to
  `InternalError`; the server only emits five codes
  (`client.rs:696-712`; `service.rs:650-657`).
- **Node vs Server events.** Node replays until ack; Server is best-effort, not
  persisted, not replayed, no ack, and drops on a full capacity-1024 channel
  (`lib.rs:997-1029`; `api-guide.md:331-340`).
- **Type erasure at the string boundary.** `PaymentId`, `PaymentHash`,
  `ChannelId` are all `typedef string` in the UDL
  (`ldk_node.udl:370-391`), so a 64-hex-char value valid for one is valid for
  the others; no runtime tag distinguishes them.
- **Constructor error domain.** `LdkServerClient::new` returns
  `Result<Self, String>`, not `LdkServerError` (`client.rs:118-135`); do not
  fold it into T7.

### 5.3 Non-vacuity and anti-weakening rules

- Every target in §4 has an explicit witness; a theorem with an unsatisfiable
  hypothesis (e.g. `h : s.running = true ∧ s.running = false`) must be rejected
  in review.
- Do **not** state a global "all API methods require running": the LDK test
  proves invoice creation works unstarted (`builder.rs:2784-2845`).
- Do **not** state "remove absent key is an error": the KV contract says it
  succeeds (`persist.rs:186-191`).
- Do **not** state "verify_signature proves payment/authenticity": it is an
  ECDSA bit, not a payment relation; the existing payment rows already
  distinguish signature from payment (`LN-PM-002`).
- Do **not** weaken `LN-CR-004/005/006` or `LN-PM-007` by reusing their names
  for FFI/gRPC contracts; the carriers and error types differ.

---

## 6. Wave-13 recommendation

**No core wave-13 implementation lane for the verification charter.** The
public API/FFI/binding surface has no catalog row, no Lean carrier, and no
in-scope theorem; `docs/SCOPE.md:20-28` and `docs/CHARTER.md:11-14` explicitly
exclude bit-exact serialization and a verified Rust extraction. Adding a node-API
lane to the catalog would be a scope change, not a gap fill.

**Safe conditional option (only if the maintainer explicitly extends scope):**
admit a single **non-catalog** contract module, `LnLean.NodeApi`, containing
T1, T2, T3, and T4 (plus T7 in a sibling `LnLean.ServerClient.ErrorMapping`),
with:

- no `docs/THEOREM-INDEX.md` row claiming protocol coverage;
- no Rust-refinement or binding-conformance claim in the docstring;
- all §5.1 assumptions stated in the module header;
- explicit counterexamples from §5.2 retained as theorems/tests;
- T5 handed to **R18** (events/runtime) and auth/macaroon work left to **R21**;
- T6/T8 deferred until a store/gRPC carrier is justified by another lane.

**Otherwise: defer / external.** The honest disposition is:

- **external/human barrier:** FFI ABI stability, UniFFI-generated binding
  behavior, language-specific type mappings, and Rust implementation
  refinement;
- **defer:** pagination, gRPC framing, and queue-persistence size limits until
  a consumer lane needs them;
- **do not claim:** "LDK Node API compatibility is verified" from any theorem
  in this repository.

If the parent insists on a wave-13 deliverable despite the charter, the smallest
defensible one is **T1** (`start_stop_guard`) plus its two error-identity
theorems, clearly labelled a contract model.

---

## 7. Evidence and commands

All commands were read-only. No `lake build`, no `cargo test`, no network, no
edits outside this report.

```sh
# Pins and branch state
git -C /home/ubuntu/ln-lean-repair status --short --branch
git -C /tmp/opencode/ldk-refs/ldk-node rev-parse HEAD
git -C /tmp/opencode/ldk-refs/ldk-server rev-parse HEAD

# No node-API/FFI surface in Lean/docs/tests/scripts
rg -n "NodeConfig|NodeStatus|NodeError|BuildError|PageToken|NodeAlias|ldk_node|uniffi|FFI" \
  LnLean docs tests scripts

# Lifecycle, events, config, FFI, errors, pagination
sed -n '296,325p;880,905p;945,1035p;1348,1385p;1605,1630p;1695,1715p;2345,2365p;2528,2550p;2609,2650p' \
  /tmp/opencode/ldk-refs/ldk-node/src/lib.rs
sed -n '440,475p;515,550p' /tmp/opencode/ldk-refs/ldk-node/src/event.rs
sed -n '600,675p;1520,1560p;2675,2700p;2775,2865p;2940,2965p' \
  /tmp/opencode/ldk-refs/ldk-node/src/builder.rs
sed -n '540,565p' /tmp/opencode/ldk-refs/ldk-node/src/config.rs
sed -n '1,60p' /tmp/opencode/ldk-refs/ldk-node/src/hex_utils.rs
sed -n '1045,1165p;1295,1320p;3180,3200p' /tmp/opencode/ldk-refs/ldk-node/src/ffi/types.rs
sed -n '45,130p;140,220p;365,395p;405,410p' /tmp/opencode/ldk-refs/ldk-node/bindings/ldk_node.udl
sed -n '1,80p' /tmp/opencode/ldk-refs/ldk-node/src/error.rs
sed -n '490,565p;1948,1995p;2100,2120p' /tmp/opencode/ldk-refs/ldk-node/src/data_store.rs
sed -n '40,62p' /tmp/opencode/ldk-refs/ldk-node/src/payment/store.rs
sed -n '3220,3240p' /tmp/opencode/ldk-refs/ldk-node/src/wallet/mod.rs

# LDK Server client, framing, error mapping, event semantics
sed -n '90,135p;676,735p;748,795p' /tmp/opencode/ldk-refs/ldk-server/ldk-server-client/src/client.rs
sed -n '1,80p' /tmp/opencode/ldk-refs/ldk-server/ldk-server-client/src/error.rs
sed -n '40,100p' /tmp/opencode/ldk-refs/ldk-server/ldk-server-grpc/src/grpc.rs
sed -n '640,665p' /tmp/opencode/ldk-refs/ldk-server/ldk-server/src/service.rs
sed -n '40,52p;325,340p;362,376p;396,412p' /tmp/opencode/ldk-refs/ldk-server/docs/api-guide.md
sed -n '60,75p' /tmp/opencode/ldk-refs/ldk-server/docs/request-binding.md

# Adjacent Lean carriers
sed -n '190,215p' /home/ubuntu/ln-lean-repair/LnLean/Routing/Gossip.lean
sed -n '540,562p' /home/ubuntu/ln-lean-repair/LnLean/Proofs/Routing/GossipProps.lean
sed -n '1,75p;105,170p' /home/ubuntu/ln-lean-repair/LnLean/Proofs/PhaseC3/PersistenceRecovery.lean
sed -n '15,32p' /home/ubuntu/ln-lean-repair/docs/SCOPE.md
sed -n '8,38p' /home/ubuntu/ln-lean-repair/docs/CHARTER.md
sed -n '44,50p;74,82p' /home/ubuntu/ln-lean-repair/docs/THEOREM-INDEX.md

# NodeError <=> UDL parity (67 variants, same order)
rg -c $'^\t[A-Z][A-Za-z0-9]+,' /tmp/opencode/ldk-refs/ldk-node/src/error.rs
python3 - <<'PY'
import re
rust = open('/tmp/opencode/ldk-refs/ldk-node/src/error.rs').read()
udl = open('/tmp/opencode/ldk-refs/ldk-node/bindings/ldk_node.udl').read()
r = re.findall(r'^\t([A-Z][A-Za-z0-9]+),', rust, re.M)
block = udl[udl.index('enum NodeError'):]
u = re.findall(r'^\t"([A-Z][A-Za-z0-9]+)",', block[:block.index('};')], re.M)
print(len(r), len(u), r == u)  # 67 67 True
PY
```

**Not run:** `lake build`, `cargo build`, `cargo test`, any network fetch, any
command that writes outside this report.
