# R22 — LDK Server config, TLS, Tor, metrics, and operations

**Status:** read-only review
**Pins:** LDK Node `fa123fed131e27ecc420b77fa7086fcf1ddaebb8`, LDK Server `c17dc11dde38f88c53457039ddf30c6b90a63ba2`
**Audited tree:** `repair/integrated` at `f7f062817c185cd70004bb26c652deb99c6fd4bd`
**Mode:** inspection only; no Lean, docs, scripts, tests, vendor, or other-lane edits.

## 1. Scope and current Lean surface

### 1.1 Catalog placement

There is **no operations/configuration catalog row**. The 51-row catalog has no
claim for `node.network`, TLS, Tor, metrics, storage namespaces, config
precedence, systemd, or certificate lifecycle. The nearest rows are about
protocol data that the configuration affects:

| Location | Row / claim | What it actually covers | What it does not cover |
|---|---|---|---|
| `docs/THEOREM-INDEX.md:62` | `LN-PR-001`, BOLT 2 `open_channel` | Funding bounds, wire projection, routed open, transport attribution | `chain_hash` selection or rejection |
| `docs/THEOREM-INDEX.md:69` | `LN-RT-002`, BOLT 7 gossip/addresses | Channel-update timestamps, node canonicalisation, rotation, address descriptor syntax | Tor routing, proxy use, inbound hidden service |
| `docs/TRACEABILITY.md:42` | `LN-PR-001` anchor | Only “BOLT 2 §The open_channel Message” | No BOLT 1/2 network-selection claim |
| `docs/TRACEABILITY.md:48` | `LN-RT-002` anchor | BOLT 7 `channel_update` / gossip | No TLS, Tor, metrics, or ops row |

The absence is consistent with `docs/SCOPE.md:20-28`, which lists no
deployment/configuration layer, and with `docs/ASSUMPTIONS.md:105-118`, whose
“network assumptions” are adversarial scheduling and an ideal authenticated
transport, not node configuration.

### 1.2 Exact declaration surface relevant to this lane

| Surface | Declaration / lines | Exact content |
|---|---|---|
| Chain identifier | `ChainHash` (`LnLean/Basic/Core.lean:194-197`), `ChainHash.Valid` (`:199`) | Opaque `ByteArray`; validity is **only** `bytes.size = 32`. |
| Mainnet constant | `ChainHash.bitcoinMainnet` (`LnLean/Basic/Core.lean:201-206`) | A mainnet genesis literal. It is **unused** elsewhere in `LnLean/` outside WaveH witness/validity uses; no testnet/signet/regtest/testnet4 constants exist. |
| Invoice network enum | `LnLean.Payment.Invoice.Network` (`LnLean/Payment/Invoice.lean:97-104`), `hrpPrefix` (`:108-114`), `code` (`:116-126`) | Four constructors: `mainnet`, `testnet`, `signet`, `regtest`. No `testnet4`, no genesis hash, no storage or wire semantics. |
| Funding projection | `Handshake.OpenChannel` (`LnLean/Protocol/Handshake.lean:835-846`) | Deliberately omits `chain_hash`; the comment says it is a “network-wide connection parameter”. |
| Wire payload | `Messages.Msg.openChannel` (`LnLean/Protocol/Messages.lean:88-93`, `:400-412`) | `chain_hash` omitted; model length `321`; the comment records the real 319/323/355 variants. |
| Wire-complete WaveH records | `OpenChannelMsg.wellFormed` (`LnLean/Proofs/WaveH/H17.lean:440-451`), `wellFormed_chainHash` (`:457-459`); `WireValid` (`H14.lean:130-149`) | Includes `chain_hash`, but only constrains its **width**: `m.chainHash.size = 32`. No equality to a configured network. |
| Address syntax | `NodeAddressTargets` (`LnLean/Proofs/Routing/NodeAddressTargets.lean:24-30`) | BOLT 7 descriptor syntax only; explicitly excludes DNS resolution, Tor hostname resolution, reachability, and P2P framing. |
| TLS / metrics / config | — | No declarations at all. |

**Consequence:** the only thing the Lean tree can say about network selection
today is “a 32-byte chain hash is present.” It cannot say that the hash matches
the selected network, that the selected network matches the chain source, or
that a wrong-network `open_channel` is rejected. This is the central gap for
this lane.

### 1.3 What this lane did not re-review

R15 (`agents/reports/wave13-review/R15-bolt8-transport.md`) already established
that TLS server authentication, TLS client authentication, macaroons, and
request binding are unmodelled, and that the TLS server uses
`with_no_client_auth()`. This report does not repeat that analysis. It focuses
on the **configuration and operational predicates** around those mechanisms:
which network is selected, how TLS material is created/bound, where Tor applies,
and where metrics are exposed.

## 2. LDK datapoints (with `file:line`)

Reference roots: `/tmp/opencode/ldk-refs/ldk-node`,
`/tmp/opencode/ldk-refs/ldk-server`, and the tree’s pinned
`refs/rust-lightning` at `fe4900930c6bd5786ec4203274d7cf312776a5a6`.
LDK Node’s own `Cargo.toml:89` pins rust-lightning to
`d7a980641c6325ddda5072a0f470ef8392676cf5`; line anchors below are from the
tree’s `fe49009` copy unless explicitly labelled.

| # | Behaviour | Evidence | Relevance |
|---|---|---|---|
| D1 | Configuration precedence is CLI > `LDK_SERVER_*` env > TOML > defaults. | `ldk-server/docs/configuration.md:7-14`; `ldk-server/src/util/config.rs:1428-1453` (`merge_toml` then `merge_args`); env attributes at `:1160-1413`; override test `:2775-2799`. | A stale or attacker-writable TOML file cannot override an explicit CLI/env security choice. The model has no effective-config function. |
| D2 | `node.network` is required and selects the per-network storage directory. | `util/config.rs:430`; `main.rs:108-113` (`bitcoin/`, `testnet/`, `testnet4/`, `signet/`, `regtest/`). | Network selection is both a protocol and a state-location choice. |
| D3 | Exactly one chain source must be configured; the source is independent of `node.network`. | `util/config.rs:482-499`. The code counts `bitcoind` / `electrum` / `esplora` sources; it never compares the selected network to the backend’s chain. | A mainnet-configured node can be pointed at a regtest/signet backend at the config layer. |
| D4 | rust-lightning derives the wire `chain_hash` from the node’s network, and rejects inbound `open_channel` whose `chain_hash` differs. | `refs/rust-lightning/lightning/src/ln/channelmanager.rs:3963` (`ChainHash::using_genesis_block(params.network)`), `:4224` (outbound `get_open_channel(self.chain_hash)`), `:12324-12328` (`if common_fields.chain_hash != self.chain_hash` → “Unknown genesis block hash”). BOLT 2 requires the same: `refs/bolts/02-peer-protocol.md:717-719`, `:802`, `:858`. | This is a real, protocol-mandated safety check that the Lean `open_channel` model cannot state. |
| D5 | LDK Node’s only explicit network check is the persisted wallet network, not the chain source. | `ldk-node/src/builder.rs:1766-1789` (`check_network(config.network)`, `BuildError::NetworkMismatch`); `:1810-1826` only guards a missing chain tip. No chain-source `getblockchaininfo.chain` comparison was found. | `NetworkMismatch` protects a single storage directory from network switching; it does not prove the node and backend are on the same chain. |
| D6 | SQLite state is per-network; the mnemonic is shared at the storage root. | `main.rs:108-113`, `:154-157`; `docs/configuration.md:252-278`; `docs/operations.md:221-230`. | Different `node.network` values do not share the per-network SQLite file. |
| D7 | PostgreSQL storage is **not** automatically network-scoped. | `util/config.rs:587-612` (only connection string/db/table/certificate); `docs/operations.md:225-226` (“not automatically isolated by network; configure a distinct database or table”). | Two networks can share one PostgreSQL table if the operator does so. The config layer does not reject it. |
| D8 | TLS is a self-signed ECDSA P-256 server certificate, generated on first startup; key is written `0400`; SANs always include `localhost` and `127.0.0.1` plus configured `hosts`. | `util/tls.rs:51-73`; `:114-145` (`hosts` initialization at `:119-120`, key mode `:139`, cert write `:141`); `docs/configuration.md:163-172`; `docs/api-guide.md:122-124`. | Server identity is a pin, not the Lightning node id. The default SAN set is loopback-only. |
| D9 | The TLS server does **not** request a client certificate; ALPN is `h2`. | `util/tls.rs:414-421` (`with_no_client_auth()`, `with_single_cert`, `alpn_protocols = [b"h2"]`). | There is no mTLS principal to bind to a node id or macaroon. |
| D10 | `tls.hosts` is passed through unvalidated and is not coupled to the gRPC bind address or announcement address. | `util/config.rs:99-103`, `:248-254`, `:718-724` (stores `tls_config` verbatim); `util/tls.rs:119-120`, `:268-298` (any non-IP string becomes a DNS SAN). `config.rs:432-436` parses the bind address separately. | An operator can bind `0.0.0.0:3536` with the default SAN set; remote clients cannot verify the certificate unless a matching host was added. |
| D11 | TLS material setup is not atomic with respect to partial files. | `util/tls.rs:56-62` (if either file missing, call generate); `:139-142` (`write_new` for key, then `fs::write` for cert); `util/mod.rs:41-48` (`create_new`, refuses an existing file). | If the key exists but the cert is missing, `write_new` fails and startup exits. If the cert exists but the key is missing, a new key is written and the existing cert is overwritten by a self-signed cert. |
| D12 | SIGHUP reopens the log file only; TLS/config/certificate reload requires restart. | `main.rs:762-773`; `docs/configuration.md:160-161`; `docs/operations.md:142-143`. | Renewal correctness is operational; there is no hot-reload model. |
| D13 | Tor is outbound and OnionV3-only; OnionV2 is rejected; clearnet is direct; the proxy itself may not be an onion address. | `ldk-node/src/connection.rs:120-128` (OnionV2 unsupported), `:129-191` (OnionV3 requires proxy, `tor_connect_outbound`), `:193-220` (all other addresses use direct `connect_outbound`); `builder.rs:641-656`, `:1551-1558` (proxy onion rejected); `docs/tor.md:3-9`, `:21-32`. | A faithful routing-mode model is small. Privacy and DNS leakage are not proved. |
| D14 | Inbound Tor hidden service is external; LDK Server only announces an address it is given. | `docs/tor.md:34-37`, `:39-94`; `util/config.rs:455-470` parses announcement addresses syntactically; no check that the onion port maps to `listening_addresses`. | Announcement/port binding is an operator responsibility, not a checked invariant. |
| D15 | Metrics are served at `GET /metrics` on the gRPC bind address, over the same TLS/h2 listener, with optional static Basic Auth; disabled → 404. | `util/config.rs:33`, `:432-436`, `:680-699`; `main.rs:368-397` (poll loop and precomputed Basic header), `:399-414` (one listener), `:733-744` (same service); `service.rs:146-184` (path check before gRPC validation; 401 or 200); `docs/operations.md:154-195`; `docs/api-guide.md:357-366`. | Metrics expose balances and counts. TLS is not an access-control boundary because the cert is self-signed and clients may skip verification; Basic Auth is optional and static. |
| D16 | `[metrics] enabled=true` with only one of username/password is rejected; `poll_metrics_interval=0` is rejected. | `util/config.rs:680-699`; tests `:2926-3008`. | The config layer enforces pair-or-none, not “auth is mandatory.” |
| D17 | systemd `READY=1` is sent after listener bind and TLS setup; `STOPPING=1` is sent before `node.stop()`. | `main.rs:399-416`, `:754-775`; `util/systemd.rs:19-62`; `docs/operations.md:8-20`; sample unit `contrib/ldk-server.service:7-15`. | Readiness is a process-lifecycle claim, not a node-sync or backup claim. |
| D18 | Config parsing rejects unknown fields and caps the config file at 1 MiB. | `util/config.rs:31`, `:753-755` (`deny_unknown_fields`), `:1437-1446`; tests `:1953-1966`, `:2598-2624`. | This is a finite, checkable parser behavior; it is still outside the Lean model. |

## 3. Gap matrix

Status vocabulary: **covered faithfully**, **partially covered**, **missing**,
**contradicted**, **unmodelled/external**.

| Behavior | Lean status | LDK evidence | Gap / counterexample | Priority |
|---|---|---|---|---|
| `node.network` is a required, explicit selection | **missing** | D1, D2 | No `ServerConfig`/`loadConfig` model; `Invoice.Network` is a BOLT 11 enum, not a node config. | P1 |
| `open_channel.chain_hash` equals the selected network genesis | **missing** | D4; BOLT 2 MUST at `02-peer-protocol.md:802`, receiver failure at `:858` | `ChainHash.Valid` is width-only (`Core.lean:199`); `wellFormed` is width-only (`H17.lean:444-451`); `OpenChannel` omits the field (`Handshake.lean:835-846`). The model cannot state the real rejection. | P1 |
| Wrong-network `open_channel` is rejected | **missing** | D4 | No `acceptsOpen` relation. A 32-byte all-zero hash is `ChainHash.Valid` and `wellFormed`, although it is not mainnet/testnet/etc. | P1 |
| Node network and chain-source network agree | **unmodelled/external** | D3, D5 | `load_config` accepts independent `network` and chain-source fields. `NetworkMismatch` only compares the persisted wallet network. No `getblockchaininfo.chain` check was found. | P1 |
| SQLite state is isolated per network | **partially covered** (by deployment layout, not Lean) | D6 | No Lean storage model; the code layout is per-network. | P2 |
| PostgreSQL state is isolated per network | **contradicted at the config layer** | D7 | `PostgresStorageConfig` has no network field; two networks may use the same `connection_string/db_name/kv_table_name`. | P2 |
| TLS server identity is self-signed and pinned | **unmodelled/external** | D8; R15 D6 | No certificate, key, SAN, or pinning model. Clients must pin out of band. | P2 |
| TLS certificate SANs cover the host clients use | **missing** | D8, D10 | Default SANs are `localhost`/`127.0.0.1`; `hosts` is unvalidated and not coupled to `grpc_service_address`. | P2 |
| TLS client authentication exists | **contradicted by implementation / unmodelled** | D9; R15 D7 | `with_no_client_auth()`. Client identity is a macaroon, not a certificate. | P2 |
| TLS material lifecycle is safe on partial files | **missing** | D11 | Key-only → startup error; cert-only → key created and cert overwritten. The docs’ “if no certificate exists, regenerate” is not the whole behavior. | P2 |
| Tor applies only to outbound OnionV3 peers | **missing** | D13; R15 D5 | `NodeAddressTargets` models descriptor syntax only; no routing-mode predicate. | P2 |
| Inbound hidden service and announced onion port are bound | **unmodelled/external** | D14 | Manual Tor config; no code check. | P2 |
| Metrics exposure requires auth or network restriction | **unmodelled/external** | D15, D16 | Metrics are enabled with optional static Basic Auth; no per-client authorization, rate limit, or IP allowlist. | P2 |
| Config precedence / unknown fields / size bounds | **missing** | D1, D18 | No effective-config or parser model. | P2 |
| systemd readiness and shutdown ordering | **unmodelled/external** | D17 | Process-manager contract only; not a protocol property. | P2 |

## 4. Proposed targets

All targets below are **additive**. None changes an existing declaration or
the meaning of a current catalog row. The first two are the only ones I would
consider for a bounded implementation lane; the rest are low-value or
deployment-adjacent.

### T1 — Network selection binds the wire `chain_hash` (P1)

**Proposed name:** `LnLean.Proofs.Ops.NetworkSelection.chainHash_eq_selectedNetwork`

**Statement shape**

```lean
namespace LnLean.Proofs.Ops.NetworkSelection

inductive BitcoinNetwork
  | mainnet | testnet | testnet4 | signet | regtest

/-- Genesis hash selected by the node configuration. -/
def genesisHash : BitcoinNetwork → ChainHash

theorem genesisHash_injective : Function.Injective genesisHash

/-- Additive acceptance relation; it does not change `wellFormed`. -/
def acceptsOpen (n : BitcoinNetwork) (m : OpenChannelMsg) : Prop :=
  wellFormed m ∧ m.chainHash = genesisHash n

theorem acceptsOpen_chainHash_eq
    {n : BitcoinNetwork} {m : OpenChannelMsg}
    (h : acceptsOpen n m) : m.chainHash = genesisHash n

theorem wrongChainHash_rejected
    {n n' : BitcoinNetwork} {m : OpenChannelMsg}
    (h : acceptsOpen n m) (hne : n ≠ n') :
    ¬ acceptsOpen n' m
```

**Hypotheses.** `genesisHash_injective` over the five concrete constants;
`wellFormed` remains the existing width/domain predicate; the wire record must
be the WaveH `OpenChannelMsg` that actually carries `chain_hash`, not the
trimmed `Handshake.OpenChannel`.

**Non-vacuity / counterexample to preserve.** The existing width-only predicate
must remain reachable by a wrong hash:

```lean
theorem wellFormed_not_networkBound :
    ∃ m : OpenChannelMsg, wellFormed m ∧ m.chainHash ≠ genesisHash .mainnet
```

Witness: `m.chainHash := ⟨List.replicate 32 0⟩`; `wellFormed` holds by width,
and the all-zero hash is not `ChainHash.bitcoinMainnet`. This is the exact gap
the new relation closes. A positive witness uses
`m.chainHash := ChainHash.bitcoinMainnet` with `n = .mainnet`; a second
positive witness uses the regtest constant.

**Why it is faithful.** BOLT 2 says the sender MUST use the chain’s hash and
the receiver MUST fail an unknown chain (`refs/bolts/02-peer-protocol.md:802`,
`:858`); rust-lightning derives it from the network and enforces equality
(`channelmanager.rs:3963`, `:12324-12328`). This is protocol behavior, not a
deployment preference.

**Fidelity risk / feasibility.** Low-to-medium: the hash constants are finite
data; the risk is transcribing a wrong genesis literal. Feasibility is high
with `decide`/`rfl` on byte lists and no new dependencies. **Label:** model
extension.

### T2 — Chain source does not determine the node network (P1)

**Proposed name:** `LnLean.Proofs.Ops.NetworkSelection.chainSource_not_networkDetermining`

**Statement shape**

```lean
structure ChainSourceCfg where
  kind : ChainSourceKind       -- rpc | electrum | esplora
  endpoint : String

structure RawConfig where
  network : Option BitcoinNetwork
  source  : Option ChainSourceCfg
  -- other fields omitted from the statement

def loadConfig (r : RawConfig) : Option ServerConfig

theorem chainSource_not_networkDetermining :
    ∃ (r₁ r₂ : RawConfig) (c₁ c₂ : ServerConfig),
      r₁.source = r₂.source ∧
      c₁.network ≠ c₂.network ∧
      loadConfig r₁ = some c₁ ∧
      loadConfig r₂ = some c₂
```

**Hypotheses.** `loadConfig` models only the acceptance rules observed in
`util/config.rs`: `network` is required (`:430`), exactly one chain source is
required (`:482-499`), and the source fields never inspect `network`.

**Non-vacuity witness.** Same `bitcoind` RPC endpoint
(`127.0.0.1:18443`, user/password) with `network = regtest` and
`network = mainnet`; both are accepted because the source count is one and the
network is a separate field. The persisted-wallet `NetworkMismatch` path is not
involved on a fresh store.

**Why it is faithful.** It is a negative result about the configuration layer,
matching the absence of a chain-field check. It does **not** claim the node can
sync a mismatched backend; it says the config does not prevent the attempt.
**Fidelity risk / feasibility.** Medium: `loadConfig` is a model, not extracted
Rust. Keep the witness tied to concrete TOML values and cite the exact guard
lines. Feasibility high. **Label:** model extension plus an explicit external
assumption for actual chain agreement.

### T3 — PostgreSQL storage is not network-scoped (P2)

**Proposed name:** `LnLean.Proofs.Ops.StorageNamespace.postgres_not_networkScoped`

**Statement shape**

```lean
structure StorageCfg where
  network : BitcoinNetwork
  backend : Backend
    -- Sqlite
    -- Postgres (connectionString, dbName, kvTable, certificate)

structure ServerConfig where
  network : BitcoinNetwork
  storage : StorageCfg
  -- ...

theorem postgres_not_networkScoped :
    ∃ (c₁ c₂ : ServerConfig),
      c₁.network ≠ c₂.network ∧
      c₁.storage.backend = c₂.storage.backend ∧
      isPostgres c₁.storage.backend ∧
      acceptsConfig c₁ ∧ acceptsConfig c₂
```

**Hypotheses.** `acceptsConfig` follows the observed config rules; PostgreSQL
identity is exactly `(connection_string, db_name, kv_table_name)` and has no
network component (`util/config.rs:587-612`).

**Non-vacuity witness.** Same PostgreSQL connection string, `db_name`,
`kv_table_name`, and certificate, with `node.network = mainnet` and
`node.network = regtest`; both are accepted. Contrast with SQLite, where the
network subdirectory is part of the path (`main.rs:108-113`).

**Why it is faithful.** The code and operations guide agree that PostgreSQL is
not isolated (`docs/operations.md:225-226`); the only defense is operator
discipline. **Fidelity risk / feasibility.** Low; it is a structural absence
theorem. **Label:** model extension (negative result), with the safety
consequence stated as an assumption: shared state can collide across networks.

### T4 — Default TLS SANs do not cover a remote bind (P2)

**Proposed name:** `LnLean.Proofs.Ops.TlsIdentity.defaultSANs_not_cover_remoteHost`

**Statement shape**

```lean
def defaultSANs : List String := ["localhost", "127.0.0.1"]

def certCovers (sans : List String) (host : String) : Prop := host ∈ sans

structure TlsCfg where
  certPath : Option String
  keyPath  : Option String
  hosts    : List String

theorem defaultSANs_cover_loopback :
    certCovers defaultSANs "localhost" ∧ certCovers defaultSANs "127.0.0.1"

theorem defaultSANs_do_not_cover_remote :
    ¬ certCovers defaultSANs "ldk.example.com"

theorem remote_bind_without_hosts_not_covered
    (hhosts : c.hosts = []) (hbind : c.grpcHost = "0.0.0.0") :
    ¬ certCovers (defaultSANs ++ c.hosts) "ldk.example.com"
```

**Hypotheses.** The client verification contract
`TlsClientRequiresSAN : TlsCfg → String → Prop` (an explicit external
assumption that the client checks the SAN against the host it dialed). The
server-side generation behavior is exactly `defaultSANs ++ hosts`
(`util/tls.rs:119-120`).

**Non-vacuity witness.** `localhost` is covered; `ldk.example.com` is not.
The docs’ recommended remote flow adds the hostname to `[tls] hosts`
(`docs/operations.md:206-219`), which is precisely the missing predicate.

**Why it is faithful.** It models only the certificate SAN set and the
configuration coupling, not cryptography or trust roots. **Fidelity risk /
feasibility.** Medium: client verification is external, and host matching has
wildcard/IDNA edge cases not modelled. **Label:** model extension plus external
client-verification assumption.

### T5 — TLS material lifecycle on partial files (P2)

**Proposed name:** `LnLean.Proofs.Ops.TlsIdentity.tlsSetup_cases`

**Statement shape**

```lean
inductive TlsFiles
  | none | certOnly | keyOnly | both

inductive TlsError
  | keyAlreadyExists | readFailed | loadFailed

def setupTls : TlsFiles → Result TlsMaterial TlsError

theorem tlsSetup_cases :
    setupTls .none      = .ok generated ∧
    setupTls .certOnly  = .ok generated ∧
    setupTls .keyOnly   = .error .keyAlreadyExists ∧
    setupTls .both      = .ok loaded
```

**Hypotheses.** `setupTls` models only file presence and the two write
operations in `util/tls.rs:56-62`, `:139-142`; `write_new` refuses an existing
path (`util/mod.rs:41-48`); the actual process exits on the error path
(`main.rs:403-412`).

**Non-vacuity witness.** `keyOnly` is the concrete key-present/cert-missing
case. `certOnly` is the cert-present/key-missing case, which succeeds but
overwrites the existing cert. Both are reachable from the documented default
paths.

**Why it is faithful.** It captures a real startup/liveness behavior and the
non-atomicity that the prose glosses over. **Fidelity risk / feasibility.**
Low-medium: the model abstracts `fs::write` overwrite semantics and process
exit. **Label:** model extension (filesystem abstraction).

### T6 — Tor outbound routing mode (P2)

**Proposed name:** `LnLean.Proofs.Ops.TorBinding.onionV3_only_via_proxy`

**Statement shape**

```lean
inductive PeerAddr
  | clearnet (host : String) (port : Nat)
  | onionV2 (host : String) (port : Nat)
  | onionV3 (host : String) (port : Nat)

inductive Route
  | direct
  | viaProxy (proxy : String)
  | fail

def routePeer (tor : Option String) : PeerAddr → Route

theorem clearnet_direct :
    routePeer tor (.clearnet h p) = .direct

theorem onionV3_requires_proxy :
    routePeer none (.onionV3 h p) = .fail

theorem onionV3_via_configured_proxy :
    routePeer (some proxy) (.onionV3 h p) = .viaProxy proxy

theorem onionV2_rejected :
    routePeer tor (.onionV2 h p) = .fail

theorem onion_proxy_rejected :
    isOnionAddress proxy → setTorConfig (some proxy) = .error
```

**Hypotheses.** The routing table follows the match arms in
`ldk-node/src/connection.rs:120-220`; `setTorConfig` follows
`builder.rs:646-656`. DNS resolution and proxy reachability are abstracted.

**Non-vacuity witness.** `routePeer (some "127.0.0.1:9050") (.onionV3 ...) =
.viaProxy "127.0.0.1:9050"`; `routePeer none (.clearnet ...) = .direct`;
`routePeer (some p) (.onionV2 ...) = .fail`.

**Why it is faithful.** It is the exact LDK Node outbound policy and directly
matches `docs/tor.md:3-9`, `:21-32`. It does not claim privacy: clearnet DNS
and Electrum/Esplora/RGS traffic are outside it. **Fidelity risk /
feasibility.** Low; tiny finite model. **Label:** model extension.

### T7 — Metrics exposure predicate (P2, optional / low value)

**Proposed name:** `LnLean.Proofs.Ops.MetricsExposure.unauthenticated_readable`

**Statement shape**

```lean
structure MetricsCfg where
  enabled : Bool
  auth    : Option (String × String)
  bind    : SocketAddr

def readableBy (c : MetricsCfg) (client : Client) : Prop :=
  c.enabled = true ∧
  (c.auth = none ∨ client.authorized c) ∧
  reachable c.bind client

theorem unauthenticated_metrics_readable
    (h : c.enabled = true) (ha : c.auth = none)
    (hr : reachable c.bind client) :
    readableBy c client
```

**Hypotheses.** The path check and 401/200 branches of
`service.rs:146-184`; the static Basic header of `main.rs:390-397`; the
same-listener bind of `main.rs:399-414`.

**Non-vacuity witness.** `enabled = true`, `auth = none`, `bind = 0.0.0.0:3536`.
The default `enabled = false` and the default `127.0.0.1:3536` are the safe
witnesses.

**Why it is faithful but weak.** It is an exact predicate over the code, but it
adds almost no protocol assurance. The meaningful statement is a deployment
assumption: “the operator must restrict reachability or configure Basic Auth.”
I recommend **not** adding this to the catalog; document it instead. **Label:**
external/deployment assumption (optional model extension).

### Target summary

| Target | Priority | Kind | Fidelity risk | Feasibility |
|---|---|---|---|---|
| T1 `chainHash_eq_selectedNetwork` | P1 | model extension | Low–medium (constants) | High |
| T2 `chainSource_not_networkDetermining` | P1 | negative + external | Medium (`loadConfig` model) | High |
| T3 `postgres_not_networkScoped` | P2 | negative | Low | High |
| T4 `defaultSANs_not_cover_remoteHost` | P2 | model extension + external | Medium (client verification) | High |
| T5 `tlsSetup_cases` | P2 | model extension | Low–medium (FS abstraction) | High |
| T6 `onionV3_only_via_proxy` | P2 | model extension | Low | High |
| T7 `unauthenticated_metrics_readable` | P2 | deployment assumption | Low, but low value | High |

## 5. Assumptions, counterexamples, and non-vacuity risks

### 5.1 Counterexamples that must be preserved

1. **`ChainHash.Valid` is width-only.** `LnLean/Basic/Core.lean:199` and
   `H17.lean:444-451` accept any 32-byte value. The all-zero 32-byte hash is
   `wellFormed` and is not the mainnet genesis. Any T1 implementation must keep
   this witness; do not strengthen `ChainHash.Valid` or `wellFormed` in place.
2. **`Handshake.OpenChannel` deliberately omits `chain_hash`.** Its funding
   theorem (`FundingAuthTargets`, `FundingLinkTargets`) depends on the trimmed
   projection. Do not add a `chainHash` field to that structure; add the
   agreement at the `OpenChannelMsg`/acceptance layer instead.
3. **`NodeAddressTargets` models Tor v2 syntax.** It accepts a deprecated Tor v2
   descriptor even though outbound OnionV2 connections fail
   (`connection.rs:121-127`). Preserve the syntax-vs-connectability gap; do not
   “fix” the address parser to reject v2 unless the BOLT 7 claim is also
   restated.
4. **`NodeAddressTargets` is not a reachability or DNS model.** Its own scope
   note (`:24-30`) excludes resolution and routing. T6 must be a separate
   routing-mode layer, not a reinterpretation of the address theorems.
5. **PostgreSQL sharing is accepted.** T3’s witness is a deliberate negative;
   do not turn it into a theorem that PostgreSQL is automatically isolated.
6. **TLS is server-only.** `with_no_client_auth()` (`tls.rs:417`) must stay
   explicit. Do not write a theorem whose English reading is “TLS authenticates
   the client” or “TLS identity is the Lightning node id.”
7. **Metrics can be unauthenticated.** The safe default is loopback bind plus
   metrics disabled. Do not claim Basic Auth is mandatory; `[metrics]` allows
   `enabled = true` with no credentials (`config.rs:680-699`).
8. **R15’s read-direction counterexample** (`demoUnattributedSession` and the
   send/recv key issue) is independent of this lane and must not be disturbed by
   any TLS/Tor refactor.

### 5.2 Assumptions that should remain explicit

* `ChainSourceAgrees (cfg) (chain)` — the actual Bitcoin Core/Electrum/Esplora
  backend is on the same chain as `node.network`. The config layer does not
  prove it (D3/D5).
* `TlsClientRequiresSAN` — the client verifies the certificate SAN against the
  host it dialed, and pins the self-signed certificate out of band (D8).
* `MetricsNetworkRestricted` — either the bind is loopback/firewalled or the
  operator configures Basic Auth. The server does not enforce this (D15).
* `TorDaemonReachable` — the configured SOCKS proxy exists and is reachable;
  `connection.rs:138-158` only resolves/looks it up at connect time.
* `HiddenServicePortMatchesAnnouncement` — the Tor hidden-service port maps to
  `listening_addresses` (D14); LDK Server cannot check it.
* `PostgresNamespaceDisjoint` — the operator uses distinct databases/tables for
  distinct networks (D7).

### 5.3 Proposals that would weaken or hide

* **Do not** redefine `ChainHash.Valid` as “equals one of the five genesis
  hashes.” That would silently change H13/H14/H17 wire lemmas and the
  `LN-PR-001` target set.
* **Do not** change `Messages.Msg.openChannel` or `Handshake.OpenChannel` to
  add `chain_hash`; use the WaveH wire record plus a new acceptance predicate.
* **Do not** replace T2 with a theorem that `loadConfig` proves chain agreement.
  That is false for the observed code. Keep it as an external hypothesis and a
  negative config result.
* **Do not** claim T4 proves TLS authentication. It proves only that the
  default SAN list omits a remote host; trust roots, pinning, and the TLS
  handshake remain external.
* **Do not** claim T6 proves anonymity. It proves only the outbound routing
  table; clearnet DNS, Electrum/Esplora/RGS, and inbound hidden-service traffic
  are outside.
* **Do not** promote T7 to a catalog row with a security-sounding title. It is
  a deployment predicate, not a protocol invariant.

## 6. Wave-13 recommendation

**No core proof lane.** The remaining work in this surface is not a P0/P1
protocol gap that a wave-13 proof lane can close. It is a mix of:

* one genuinely protocol-visible missing claim (T1: `chain_hash`/network
  binding), which is additive and cheap but still does not prove the backend
  chain agrees (T2);
* configuration/storage invariants (T2, T3) that are useful negative results
  but depend on a model of `load_config`;
* deployment/TLS/Tor/metrics behavior (T4–T7) that is either an external
  assumption or a low-value finite predicate.

**Safe implementation option for wave 14.** If the maintainer wants runtime
configuration claims, open **one** bounded, additive module
`LnLean/Proofs/Ops/DeploymentConfigTargets.lean` containing T1, T2, T3, and T6.
It must not edit `ChainHash`, `OpenChannel`, `Messages`, `Handshake`, or any
existing catalog row. It should add no catalog row unless the parent explicitly
wants an `LN-OPS-*` deployment row with a scope note saying “configuration
layer, not BOLT protocol.”

**Otherwise: defer and treat as external.** TLS identity/pinning, Tor hidden
service, metrics exposure policy, PostgreSQL namespace choice, and systemd
readiness are **human/deployment barriers**, not proof targets. They should be
documented as explicit assumptions in the trust boundary, not promoted into
the Lightning safety claim. This matches the wave-12 post-integration verdict
(`agents/reports/swarm12/S12-POST-INTEGRATION-AUDIT.md:68-77`): no new wave-13
proof lane, and external barriers remain external.

**What the parent should not do.** Do not describe the current tree as having a
proved “network selection” or “TLS identity” property. It has neither; the only
`chain_hash` claim is a 32-byte width check.

## 7. Evidence and commands

All commands were read-only. No Lean build was run; no cargo test was run; no
file outside this report was modified.

```sh
# pins and audited tree
git -C /tmp/opencode/ldk-refs/ldk-node rev-parse HEAD
# fa123fed131e27ecc420b77fa7086fcf1ddaebb8
git -C /tmp/opencode/ldk-refs/ldk-server rev-parse HEAD
# c17dc11dde38f88c53457039ddf30c6b90a63ba2
cd /home/ubuntu/ln-lean-repair
git rev-parse --abbrev-ref HEAD   # repair/integrated
git rev-parse HEAD                # f7f062817c185cd70004bb26c652deb99c6fd4bd

# catalog surface
python3 scripts/check-catalog.py --audit | tail -20
# summary: rows=51 proved=51 statementOnly=0 targets=294
#          unresolved=0 proved_failures=0 declarations=11898
# OK: every catalog target resolves exactly and every proved row is sorry-free

# Lean surface
rg -n "structure ChainHash|ChainHash.Valid|bitcoinMainnet" LnLean/Basic/Core.lean
rg -n "chain_hash|chainHash" LnLean/Protocol LnLean/Proofs/WaveH LnLean/Proofs/Protocol
rg -n "NodeAddressTargets|resolution|reachability" LnLean/Proofs/Routing/NodeAddressTargets.lean

# LDK Server configuration / TLS / metrics / systemd
rg -n "pub struct Config|pub struct TlsConfig|pub struct TorConfig|grpc_service|metrics_|tls_config|proxy_address" \
  /tmp/opencode/ldk-refs/ldk-server/ldk-server/src/util/config.rs
rg -n "get_or_generate_tls_config|generate_self_signed_cert|with_no_client_auth|alpn_protocols" \
  /tmp/opencode/ldk-refs/ldk-server/ldk-server/src/util/tls.rs
rg -n "GET_METRICS_PATH|metrics_auth_header|Unauthorized|gather_metrics" \
  /tmp/opencode/ldk-refs/ldk-server/ldk-server/src/service.rs \
  /tmp/opencode/ldk-refs/ldk-server/ldk-server/src/main.rs
rg -n "notify_ready|notify_stopping|SIGHUP|SIGTERM" \
  /tmp/opencode/ldk-refs/ldk-server/ldk-server/src/main.rs \
  /tmp/opencode/ldk-refs/ldk-server/ldk-server/src/util/systemd.rs

# LDK Node Tor / network mismatch
rg -n "OnionV2|OnionV3|tor_connect_outbound|connect_outbound" \
  /tmp/opencode/ldk-refs/ldk-node/src/connection.rs
rg -n "set_tor_config|InvalidTorProxyAddress|NetworkMismatch|check_network" \
  /tmp/opencode/ldk-refs/ldk-node/src/builder.rs

# BOLT 2 chain hash requirement and rust-lightning enforcement
rg -n "chain_hash" /home/ubuntu/ln-lean-repair/refs/bolts/02-peer-protocol.md
rg -n "using_genesis_block|chain_hash != self.chain_hash" \
  /home/ubuntu/ln-lean-repair/refs/rust-lightning/lightning/src/ln/channelmanager.rs
```

**Line-anchor note.** `refs/rust-lightning` is pinned at `fe49009`; LDK Node
`fa123fe` depends on `d7a98064` (`ldk-node/Cargo.toml:89`). The BOLT and
rust-lightning citations above are from the tree’s `refs/` copy, not from a
second clone. LDK Node/Server citations are from the pinned clones named in
`agents/reports/wave13-review/LDK-REFS.md`.
