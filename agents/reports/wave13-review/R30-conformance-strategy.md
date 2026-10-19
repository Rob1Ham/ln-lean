# R30 — Conformance strategy for LDK Node and LDK Server

**Status:** read-only review
**Pins:** LDK Node `fa123fed131e27ecc420b77fa7086fcf1ddaebb8`, LDK Server `c17dc11dde38f88c53457039ddf30c6b90a63ba2`

## 1. Scope and current Lean surface

This lane asks a narrow question: which deterministic, public-API behaviours in
the pinned LDK Node and LDK Server trees can be added to `ln-lean`'s conformance
suite as faithful fixtures, and which behaviours must stay live, external, or
unmodelled. It does not implement any fixture or theorem.

### 1.1 Exact catalogue status

Conformance is **not a catalogue row**. It is the open issue `CONF-01`
(`docs/OPEN-ISSUES.md:68`, priority P2, status “open (five live message rows;
additional encodings remain)”). `CONF-02` (live rust-lightning differential) and
`CONF-03` (promoted transport framing) are closed in the same file. There is no
`LN-CONF-*` entry in `docs/THEOREM-INDEX.md`; the closest row is `LN-PR-001`
(`docs/THEOREM-INDEX.md:62`), which covers BOLT 2 channel establishment, not the
conformance harness. Consequently the catalogue gate does not audit
conformance completeness, and a green `scripts/check-conformance.py` is not a
catalogue claim.

The committed suite currently consists of:

| Surface | Evidence | Current size |
|---|---|---|
| BigSize/TLV vectors | `tests/conformance/vectors.json`; `LnLean/Proofs/ConformanceTargets.lean` | 61 expectations (12 BigSize encode, 25 BigSize decode, 24 TLV); 86 theorem declarations |
| Transport framing and boundaries | `tests/conformance/vectors.json`; `LnLean/Proofs/ConformanceDiffTargets.lean` | 16 cases (6 accept, 10 reject), 9 length boundaries |
| BOLT 2 payload/field vectors | `tests/conformance/vectors.json`; `ConformanceDiffTargets.lean` | 6 vectors (`open_channel` 2, `accept_channel` 2, `commitment_signed` 1, `update_add_htlc` 1) |
| Pinned rust-lightning differential | `tests/conformance/rust-lightning/fixtures.json` | 26 BigSize, 3 TLV, 4 wire, 5 live BOLT 2 message fixtures |
| Lean cross-references | `scripts/check-conformance.py` | 200 theorem references |
| Mutation controls | `scripts/check-conformance.py` | 22/22 detected |
| Live transcript | `tests/conformance/rust-lightning/live-transcript.json` | SHA-256 prefix `a47b2aa4a2e1` |

The last verified run in this lane is recorded in §7. The suite is explicitly
“vector/differential conformance, not a full implementation test”
(`tests/conformance/README.md:1-10`), and the five live BOLT 2 payloads are
“finite/public-API conformance, not node-level interop”
(`docs/OPEN-ISSUES.md:68`; `agents/reports/swarm12/S12-POST-INTEGRATION-AUDIT.md:25-29`).

### 1.2 What the checker actually verifies

`scripts/check-conformance.py` is an independent Python validator, but its Lean
cross-check is **syntactic**. `lean_theorems` scans the two target modules with
the regex `^theorem\s+([A-Za-z0-9_']+)` (`:1011-1016`, `:1201-1208`);
`byte_literals` extracts `bytes [...]` literals (`:1210-1216`); and
`check_lean_sync` (`:1229-1288`) only requires that the expected theorem name
exists and that the expected hex literal or decision text appears in the theorem
block. It never invokes `lake`, never elaborates a declaration, and never checks
the kernel. A passing checker therefore means “the JSON and the theorem text
agree”, not “Lean proved the vector”.

The differential half is also specific to rust-lightning. `DEFAULT_DIFF`,
`DEFAULT_SOURCE`, `LIVE_PROBE`, `LIVE_LOCK`, and `LIVE_TRANSCRIPT_SCHEMA` are
hard-coded (`scripts/check-conformance.py:74-78`), and the schema is
`lnlean.rust-lightning.differential.v1` with the `fe49009` pin (`:944-966`).
There is no `refs/ldk-node` or `refs/ldk-server` provenance path in the checker.
LDK Node/Server fixtures cannot be appended to `fixtures.json` without either a
second checker or a schema/pin dispatch; R23 already records this at
`agents/reports/wave13-review/R23-ldk-server-e2e-mcp.md` §1.2.

### 1.3 Existing Lean carriers that matter

| Carrier | Location | What it does | What it does not do |
|---|---|---|---|
| `FeatureVector` | `LnLean/Proofs/Protocol/FeaturesProps.lean:133-170` | `bits : Nat → Bool`, `byteLen : Nat`, `Bounded`, `requires`, `offersOptional`, `supports` | No byte array, no wire order, no codec instance |
| `FeatureCodec` | `FeaturesProps.lean:480-500` | Abstract `decode`/`encode` with `byteLen_eq` and `decode_bounded` | Deliberately unimplemented; `decoded_bit_lt_wire` is conditional on any codec |
| BOLT 11 pre-bech32 fields | `LnLean/Proofs/Payment/InvoiceWireTargets.lean` (`featureBits` `:206-210`, `encodeFeatures` `:237-238`) | Fixed-order `p,s,n,x,c,9,r*` field printing/parsing | Fixed-width feature field; no PaymentDetails persistence, no LDK event/config |
| Invoice semantics | `LnLean/Payment/Invoice.lean:197-210` | Semantic invoice record, `Valid`, `verify` | No bech32 string, no LDK Node payment store |
| Protocol events | `LnLean/Channel/State.lean:67-78` | Ten peer-protocol `ProtocolEvent` constructors | Not LDK Node's persisted `Event` enum; no variant TLV ids, no event queue |
| Transport framing | `LnLean/Wire/Message.lean`; `Wire.Transport` | BOLT 8 length/frame/decoder model | No LDK Node/Server persistence codec |

`LnLean/Proofs/PhaseC2/FeatureClosure.lean:68-78` states the boundary
explicitly: byte-level encoding and the big-endian/little-endian reversal are
**not modelled**, and the proofs are pointwise over `Nat → Bool`. There is no
Lean module for LDK Node `Event`, `PaymentDetails`, `ChannelConfig`, LDK Server
`build_channel_config_from_proto`, request binding, or server e2e behaviour.

### 1.4 Deterministic versus live

The classification used throughout this report is:

* **Deterministic public-API fixture** — fixed input, fixed output, no
  bitcoind, no network, no timing, reproducible offline from a pinned checkout
  and a pinned lock file. Public traits/functions are preferred over private
  implementation detail.
* **Deterministic source-derived fixture** — fixed semantic table transcribed
  from a pinned private function (for example
  `build_channel_config_from_proto`), with the fidelity risk stated and no live
  probe claim.
* **Live/network/chain test** — needs regtest `bitcoind`, a running LDK Server,
  TLS/macaroon transport, asynchronous event delivery, or wall-clock timing.
  These may be recorded as evidence but cannot become unconditional Lean
  theorems.
* **External** — depends on a cryptographic primitive (SHA-256, HMAC, HKDF,
  signatures), a consensus/chain policy, or a production decoder that the model
  does not contain.

### 1.5 Cross-lane boundaries

To avoid duplicating other wave-13 lanes:

* **R15 T8** owns `RequestBindingTargets.parseProof_renderProof` and the
  macaroon/request-binding model. This report treats request binding as a
  deterministic grammar fixture family only, and does not propose a competing
  target.
* **R10 T5** owns BOLT 9 feature pairing and minimal-width `9` field semantics
  in BOLT 11 invoices. This report proposes only a shared concrete
  `FeatureCodec` foundation; it does not replace or reinterpret R10 T5.
* **R17** owns the LDK Node builder/persistence surface; **R18** owns event
  queue runtime ordering, crash windows, and dispatch; **R23** owns server
  e2e/MCP/gRPC determinism; **R24** owns server payment/channel API semantics.
  This report adds codec/configuration *conformance* targets, not those runtime
  or API contracts.
* **R21/R23** already cover macaroon policy and authorization. This report does
  not re-scope them.

## 2. LDK datapoints (with `file:line`)

### 2.1 LDK Node event queue: a persisted, versioned TLV format

| ID | Datapoint | Evidence | Classification |
|---|---|---|---|
| D1 | `Event` is a ten-variant enum; variant tags are 0–9 (`PaymentSuccessful` 0, `PaymentFailed` 1, `PaymentReceived` 2, `ChannelReady` 3, `ChannelPending` 4, `ChannelClosed` 5, `PaymentClaimable` 6, `PaymentForwarded` 7, `SpliceNegotiated` 8, `SpliceNegotiationFailed` 9). | `ldk-node/src/event.rs:129` (enum start), `:333-411` (`impl_writeable_tlv_based_enum!`) | Deterministic, public enum/wire format |
| D2 | `ChannelReady` writes TLV 0 `channel_id` required, 1 `counterparty_node_id` optional, 2 `user_channel_id` required, 3 `funding_txo` optional. | `event.rs:352-357` | Deterministic |
| D3 | `ChannelClosed` writes TLV 0 `channel_id` required, 1 `counterparty_node_id` required, 2 `user_channel_id` required, 3 `reason` upgradable-option. | `event.rs:365-370` | Deterministic |
| D4 | `PaymentForwarded` reads legacy TLV 0,1,2,3,4,6 but never writes them; writes 8 `total_fee_earned_msat` optional, 10 `skimmed_fee_msat` optional, 12 `claim_from_onchain_tx` required, 14 `outbound_amount_forwarded_msat` default 0, 15 `prev_htlcs` default-vector, 17 `next_htlcs` default-vector. | `event.rs:378-405` | Deterministic; legacy compatibility |
| D5 | The queue outer format is a `u16` count followed by each event's own `Writeable` encoding; read allocates that many events. | `event.rs:505-538` (`EventQueueDeserWrapper`/`EventQueueSerWrapper`) | Deterministic |
| D6 | A `ChannelReady` event with `ChannelId([23;32])`, `UserChannelId(2323)`, no counterparty, no funding outpoint survives queue persistence and repeated reads until `event_handled`. | `event.rs:2846-2876` (`event_queue_persistence`) | Deterministic in-memory store; no chain |
| D7 | Legacy `ChannelClosed` with a counterparty is accepted; the same event **without** a counterparty is rejected. | `event.rs:2935-2980` | Deterministic; a necessary-condition counterexample |
| D8 | Legacy `PaymentForwarded` with type 14 absent normalizes `outbound_amount_forwarded_msat` to `Some(0)`; a legacy multi-HTLC forward (2 prev, 1 next) survives. | `event.rs:2982-3053`; round-trip at `:3056-3067` | Deterministic; normalization, not identity |

### 2.2 LDK Node `PaymentDetails`: gross-on-disk / net-in-memory

| ID | Datapoint | Evidence | Classification |
|---|---|---|---|
| D9 | `PaymentDetails` has `amount_msat : Option<u64>`, `fee_paid_msat : Option<u64>`, direction, status, and a `PaymentKind` that may carry `counterparty_skimmed_fee_msat`. | `ldk-node/src/payment/store.rs:63-89`; `PaymentKind::Bolt11` at `:549-564` | Deterministic |
| D10 | On write, **only pending inbound BOLT 11** records add the counterparty-skimmed fee to the amount with `saturating_add` before encoding TLV 6. | `store.rs:106-135` (condition at `:112-122`, `:119`) | Deterministic |
| D11 | On read, **only pending inbound BOLT 11** records subtract the fee with `saturating_sub`. Completed/outbound records are not adjusted. | `store.rs:139-207` (condition at `:191-203`, `:197`) | Deterministic |
| D12 | The comment states the compatibility contract: pending BOLT 11 amounts were historically gross on disk, so reads must subtract exactly once “including after a restart”. | `store.rs:110-113` | Deterministic |
| D13 | Legacy records with no `kind_opt` reconstruct `Bolt11` when a secret is present and `Spontaneous` otherwise; the pre-v0.2.1 `hash` is re-created from the payment id. | `store.rs:160-185` | Deterministic |
| D14 | Seven recorded vectors: pending 100000/fee1000 → decoded 99000/persisted 100000; pending 100000/fee100000 → 0/100000; pending 100000/fee150000 → 0/150000; pending 100000/no fee → 100000/100000; pending no amount/fee1000 → none/none; succeeded 99000/fee1000 → 99000/99000; failed 100000/fee1000 → 100000/100000. | `store.rs:818-872` (`v0_7_pending_bolt11_amounts_roundtrip_as_net`) | Deterministic |
| D15 | Overflow vector: net 100, fee `u64::MAX - 50` → write succeeds, persisted amount saturates to `u64::MAX`, read yields 50; a second cycle is stable. | `store.rs:876-891` (`pending_bolt11_amount_overflow_remains_writable`) | Deterministic; **round-trip is not identity** |

### 2.3 Channel configuration: absent-field preservation and a `u16` bound

| ID | Datapoint | Evidence | Classification |
|---|---|---|---|
| D16 | LDK's `ChannelConfig` defaults are proportional fee 0, base fee 1000 msat, `cltv_expiry_delta` 72, `max_dust_htlc_exposure` `FeeRateMultiplier(10000)`, force-close max fee 1000 sat, `accept_underpaying_htlcs` false. | `refs/rust-lightning/lightning/src/util/config.rs:658-669` | Deterministic |
| D17 | LDK Node's `ChannelConfig` is a public six-field mirror of LDK's struct; `Default` delegates to `LdkChannelConfig::default()`. | `ldk-node/src/config.rs:789-857` | Deterministic |
| D18 | LDK Server's `UpdateChannelConfig` handler requires the channel to exist, obtains its **current** config from `list_channels`, then calls `build_channel_config_from_proto(current_config, request.channel_config)`. | `ldk-server/src/api/update_channel_config.rs:25-66` | Deterministic shape; channel lookup is live |
| D19 | `build_channel_config_from_proto` uses `unwrap_or(current)` for proportional fee, base fee, force-close max fee, and `accept_underpaying_htlcs`; absent fields preserve the current value. | `ldk-server/src/api/mod.rs:97-135` | Deterministic source-derived |
| D20 | `cltv_expiry_delta` is `u16::try_from`-checked: absent preserves current; present values above `u16::MAX` are `InvalidRequestError`. `max_dust_htlc_exposure` is a proto `oneof`; absent preserves current. | `ldk-server/src/api/mod.rs:115-135`; proto fields at `ldk-server-grpc/src/types.rs:805-860` | Deterministic source-derived |
| D21 | The handler has a `FIXME: Use ldk/ldk-node's partial config update api.`; the current full-replacement construction is the reason absent fields preserve by construction. | `update_channel_config.rs:32-34` | Fidelity caveat |

### 2.4 Feature bit mapping and proto projection

| ID | Datapoint | Evidence | Classification |
|---|---|---|---|
| D22 | LDK's internal feature flags are little-endian byte arrays; the wire `Writeable` is length-prefixed and **big-endian** (`write_be` reverses the bytes). | `refs/rust-lightning/lightning/src/ln/features.rs:24-48` | Deterministic public API |
| D23 | Within an internal `le_flags` byte, bits are LSB-first: feature bit `n` is `le_flags[n/8]` with mask `1 << (n%8)`; required bits are even, optional bits odd. On the wire the byte order is reversed, so wire byte index is `len-1 - n/8`. `define_feature!(9, VariableLengthOnion)` means required 8/optional 9; `15` means 14/15; `17` means 16/17. | `lightning-types/src/features.rs:276-356`, `:464-506`; `lightning/src/ln/features.rs:24-48` | Deterministic |
| D24 | LDK Server's `features_to_proto` iterates `le_flags` and computes `bit_number = byte_idx * 8 + bit_pos`, with `is_required = bit_number % 2 == 0`; unknown bits are skipped. | `ldk-server/src/util/proto_adapter.rs:663-698` | Deterministic source-derived |
| D25 | A live LDK Server BOLT 11 decode expects feature entry key `"8"` = `VariableLengthOnion` required, `"14"` = `PaymentSecret` required, `"17"` = `BasicMPP` **optional**. | `ldk-server/e2e-tests/tests/e2e.rs:274-296` | Deterministic assertion, but harness is live |

### 2.5 Request binding grammar (cross-referenced, not re-proposed)

| ID | Datapoint | Evidence | Classification |
|---|---|---|---|
| D26 | Limits: 4096-byte token, 32 first-party caveats, 128-byte method, 60-second timestamp tolerance, request caveat prefix `request = `. | `ldk-server/ldk-server-macaroons/src/macaroon.rs:20-32` | Deterministic |
| D27 | `RequestBinding::caveat` renders `request = <timestamp> <method> <64 lowercase hex>`; `parse` requires canonical decimal timestamp, ASCII-alphanumeric nonempty method ≤128 bytes, exactly 64 lowercase hex digits, and no extra fields. | `macaroon.rs:47-98` | Deterministic grammar |
| D28 | Canonical test: `123 GetNodeInfo` + `ab`×32; rejects leading-zero/`+`/overflow/negative timestamps, double space, empty/slash/129-byte methods, uppercase/`zz` digests, extra field, newline, truncation, wrong prefix, invalid UTF-8. | `macaroon.rs:335-370` | Deterministic grammar; SHA-256/HMAC binding external |

### 2.6 Live/network/chain-only surface

| ID | Datapoint | Evidence | Classification |
|---|---|---|---|
| D29 | Channel lifecycle e2e: pending event has `funding_txo = some`, no reason, non-empty temporary id; ready event has `funding_txo = some`; closed event has `funding_txo = none`, a reason kind, and a local/remote initiator. | `ldk-server/e2e-tests/tests/e2e.rs:752-877`; R23 D33–D36 | **Live-only** (bitcoind + async) |
| D30 | Force-close e2e reuses the same shape and checks funding txid stability from the pending outpoint. | `e2e.rs:881-1050` | **Live-only** |
| D31 | 82 of 84 server e2e test functions construct `TestBitcoind`; only macaroon derivation and balance arithmetic are pure. | R23 D1–D4 (`e2e-tests/tests/*.rs`) | **Live-only**, except two pure tests |
| D32 | BOLT 11 invoice decode assertions (`destination`, `payment_hash`, `amount_msat`, `description`, `expiry`, `currency`, `payment_secret`, features) run through a live server CLI. | `e2e.rs:260-300` | Live harness; the underlying decode is deterministic but owned by R10 |

## 3. Gap matrix

Legend: **M** missing, **P** partial, **U** unmodelled, **X** external/live,
**C** covered faithfully.

| Behavior | Lean status | LDK evidence | Gap / counterexample | Priority |
|---|---|---|---|---|
| LDK Node `Event` variant TLV codec | **M** | D1–D5 (`event.rs:129`, `:333-411`, `:505-538`) | No Lean `Event`, variant tag table, required/optional TLV schema, or queue `u16` framing. The peer-protocol `ProtocolEvent` (`State.lean:67-78`) is a different vocabulary. | P1 |
| Legacy `ChannelClosed` counterparty requirement | **M** | D7 (`event.rs:2935-2980`) | A decoder that treats missing type 1 as `None` would accept a record LDK rejects. This is a necessary-condition counterexample, not a preference. | P1 |
| Legacy `PaymentForwarded` type-14 default | **M** | D8 (`event.rs:2982-3053`) | Missing type 14 must become `Some(0)`, not `None`; a generic “absent optional = none” decoder is wrong here. | P1 |
| `PaymentDetails` gross/net amount normalization | **M** | D9–D15 (`store.rs:106-135`, `:139-207`, `:818-891`) | No `PaymentDetails` carrier and no round-trip law. The overflow vector proves the round-trip is **not** identity: `100 + (MAX−50)` → persisted `MAX` → decoded `50`. | P1 |
| `PaymentDetails` legacy kind reconstruction | **M** | D13 (`store.rs:160-185`) | No rule for “no `kind_opt` + secret present → Bolt11; else Spontaneous”; also the v0.2.1 hash/id identity is unmodelled. | P2 |
| Server channel-config update/default/validation | **M** | D16–D21 (`api/mod.rs:97-135`; `update_channel_config.rs:25-66`) | No `ChannelConfig`, no absent-field preservation, no `u16` bound, no `oneof` handling. A naive protobuf default would zero absent fields and violate the handler's `unwrap_or(current)` semantics. | P2 |
| Feature-bit byte codec | **P (abstract)** | D22–D25 (`features.rs:24-48`; `proto_adapter.rs:663-698`) | `FeatureCodec` is an unimplemented seam (`FeaturesProps.lean:480-500`); `FeatureClosure.lean:68-78` explicitly excludes byte order. The byte reversal and LSB-first bit numbering are the main traps. R10 T5 owns BOLT 11 pairing/minimal width. | P1 |
| Request-binding grammar | **U (owned by R15 T8)** | D26–D28 (`macaroon.rs:20-98`, `:335-370`) | No parser/renderer. The grammar is deterministic, but HMAC-SHA256 binding is external (`Crypto/Model.lean:84-92`, `:115-116`; R15 D8). Do not duplicate R15 T8. | P2 |
| BOLT 11 bech32 decode | **P (owned by R10)** | D25, D32 (`e2e.rs:260-300`) | `InvoiceWireTargets` is pre-bech32 only; no HRP/checksum/data-part decoder or payee recovery. R10 T3/T5 own this. Do not add a second invoice codec here. | P1 (R10) |
| Live event/channel/payment lifecycle | **X** | D29–D32 (`e2e.rs:752-1050`, `:260-300`) | Needs regtest chain, running server, async delivery, timing. Sampled assertions cannot become universal Lean theorems. | P2 |
| Existing BOLT 2 live payload rows | **C** | `docs/OPEN-ISSUES.md:68`; checker output | Five payloads (`channel_ready`, `open_channel`, `accept_channel`, `funding_created`, `funding_signed`) are covered by finite/public-API fixtures. Not node-level interop. | — |

## 4. Proposed targets

All targets are additive and live under
`LnLean/Proofs/Conformance/`. None changes an existing theorem, the abstract
`FeatureCodec`, `FeatureVector`, `Invoice`, `Step`, or any catalogue claim. No
target is P0: no LDK datapoint contradicts a green catalogue statement. The
gaps are missing or partial scope, not a false existing claim. The proposed
names are fully qualified; the module paths are suggestions, not edits.

### T1 — Persisted event TLV codec (P1, model extension)

**Module:** `LnLean/Proofs/Conformance/LdkEventCodec.lean`

**Proposed names**

```lean
LnLean.Proofs.Conformance.LdkEventCodec.event_encode_decode
LnLean.Proofs.Conformance.LdkEventCodec.eventQueue_encode_decode
LnLean.Proofs.Conformance.LdkEventCodec.legacyChannelClosed_requires_counterparty
LnLean.Proofs.Conformance.LdkEventCodec.legacyPaymentForwarded_defaults_zero
```

**Statement shape**

```lean
namespace LnLean.Proofs.Conformance.LdkEventCodec

structure HtlcLocator where
  channelId     : ByteArray
  amountMsat    : Option Nat
  userChannelId : Option Nat
  nodeId        : Option ByteArray

inductive Event where
  | channelReady (channelId : ByteArray) (userChannelId : Nat)
      (counterpartyNodeId : Option ByteArray) (fundingTxo : Option ByteArray)
  | channelClosed (channelId : ByteArray) (counterpartyNodeId : ByteArray)
      (userChannelId : Nat) (reason : Option ByteArray)
  | paymentForwarded (prevHtlcs nextHtlcs : List HtlcLocator)
      (totalFeeEarnedMsat skimmedFeeMsat : Option Nat)
      (claimFromOnchainTx : Bool) (outboundAmountForwardedMsat : Nat)

def encodeEvent : Event → ByteArray
def decodeEvent : ByteArray → Option Event
def encodeQueue (q : List Event) : ByteArray
def decodeQueue : ByteArray → Option (List Event)

def CanonicalEvent (e : Event) : Prop := ...
def CanonicalQueue (q : List Event) : Prop :=
  q.length ≤ 65535 ∧ ∀ e ∈ q, CanonicalEvent e

theorem event_encode_decode (e : Event) (h : CanonicalEvent e) :
    decodeEvent (encodeEvent e) = some e

theorem eventQueue_encode_decode (q : List Event) (h : CanonicalQueue q) :
    decodeQueue (encodeQueue q) = some q

theorem legacyChannelClosed_requires_counterparty
    (b : ByteArray) (h : IsLegacyChannelClosed b) :
    decodeEvent b = none

theorem legacyPaymentForwarded_defaults_zero
    (b : ByteArray) (h : IsLegacyForwardedMissingOutbound b) :
    ∃ prev next total skimmed claim,
      decodeEvent b =
        some (.paymentForwarded prev next total skimmed claim 0)
```

**Hypotheses.** `CanonicalEvent` requires a known variant tag (3/5/7 in this
slice), ascending unique TLV type ids, all required fields present with the
pinned widths, and no trailing bytes. `CanonicalQueue` adds `length ≤ 65535`.
The legacy predicates encode the exact absence patterns from D7/D8: for
`ChannelClosed`, type 1 absent; for `PaymentForwarded`, type 14 absent while the
other required fields are present.

**Non-vacuity witnesses.** `ChannelReady` with
`channelId = 23×32`, `userChannelId = 2323`, `none`, `none`
(`event.rs:2850-2856`); `ChannelClosed` with `channelId = 42×32`,
`userChannelId = 4242`, counterparty
`0279be667e…f81798`, reason `none` (`event.rs:2935-2963`); `PaymentForwarded`
with one prev and one next locator, `total = some 200`, `skimmed = none`,
`claim = false`, `outbound = 800` (`event.rs:3056-3067`).

**Why faithful.** The variant ids and TLV schemas are copied from the
macro-expanded enum (D1–D5); the tests already pin the three legacy behaviours.
**Fidelity risk:** this is a three-variant slice, not the full ten-variant
`Event`; `upgradable_option`, `optional_vec`, and the `HTLCLocator` defaults are
simplified, and public keys/outpoints are modelled as byte arrays without curve
or consensus validation. The report must not claim a full `Event` codec.
**Feasibility:** medium — `ByteArray` TLV recursion plus `decide` for fixed
vectors; `eventQueue_encode_decode` needs a list induction and the `u16` bound.
**Classification:** model extension; no external cryptographic assumption.

### T2 — `PaymentDetails` amount normalization (P1, model extension; top target)

**Module:** `LnLean/Proofs/Conformance/LdkPaymentCodec.lean`

**Proposed names**

```lean
LnLean.Proofs.Conformance.LdkPaymentCodec.pendingAmount_normalized
LnLean.Proofs.Conformance.LdkPaymentCodec.pendingAmount_idempotent
LnLean.Proofs.Conformance.LdkPaymentCodec.legacyGross_decodes_net
LnLean.Proofs.Conformance.LdkPaymentCodec.legacyGross_clamps_to_zero
LnLean.Proofs.Conformance.LdkPaymentCodec.pendingAmount_not_identity
LnLean.Proofs.Conformance.LdkPaymentCodec.legacyKind_reconstruction
```

**Statement shape**

```lean
namespace LnLean.Proofs.Conformance.LdkPaymentCodec

inductive Direction | inbound | outbound
inductive Status    | pending | succeeded | failed

abbrev U64Max : Nat := 2 ^ 64 - 1

inductive LegacyKind | bolt11 | spontaneous | explicit

def decodeLegacyKind (kindOpt secret : Option ByteArray) : LegacyKind :=
  match kindOpt with
  | some _ => .explicit
  | none => if secret.isSome then .bolt11 else .spontaneous

def persistedAmount (d : Direction) (s : Status)
    (amount fee : Option Nat) : Option Nat :=
  if d = .inbound ∧ s = .pending then
    match amount, fee with
    | some a, some f => some (min U64Max (a + f))
    | _, _ => amount
  else amount

def decodedAmount (d : Direction) (s : Status)
    (persisted fee : Option Nat) : Option Nat :=
  if d = .inbound ∧ s = .pending then
    match persisted, fee with
    | some p, some f => some (p - f)
    | _, _ => persisted
  else persisted

theorem pendingAmount_normalized (a f : Nat) (h : a + f ≤ U64Max) :
    decodedAmount .inbound .pending
      (persistedAmount .inbound .pending (some a) (some f)) (some f) = some a

theorem pendingAmount_idempotent (a f : Nat) :
    let p := persistedAmount .inbound .pending (some a) (some f)
    decodedAmount .inbound .pending
      (persistedAmount .inbound .pending
        (decodedAmount .inbound .pending p (some f)) (some f)) (some f)
      = decodedAmount .inbound .pending p (some f)

theorem legacyGross_decodes_net (gross fee : Nat) (h : fee ≤ gross) :
    decodedAmount .inbound .pending (some gross) (some fee) = some (gross - fee)

theorem legacyGross_clamps_to_zero (gross fee : Nat) (h : gross ≤ fee) :
    decodedAmount .inbound .pending (some gross) (some fee) = some 0

theorem pendingAmount_not_identity :
    ∃ a f : Nat,
      decodedAmount .inbound .pending
        (persistedAmount .inbound .pending (some a) (some f)) (some f) ≠ some a

theorem legacyKind_reconstruction (secret : Option ByteArray) :
    decodeLegacyKind none secret =
      if secret.isSome then .bolt11 else .spontaneous
```

**Hypotheses.** The normalized law needs `a + f ≤ U64Max`; the idempotence law
does not. `legacyGross_decodes_net` needs `fee ≤ gross` because the read uses
truncating subtraction; `legacyGross_clamps_to_zero` covers the other side of
that split. `legacyKind_reconstruction` models only the
`Bolt11`/`Spontaneous` fallback, not the full `PaymentKind` enum.

**Non-vacuity witnesses.**

* `(a,f) = (100000, 1000)` → persisted `100000`, decoded `99000`.
* `(gross,fee) = (100000, 150000)` → decoded `0`, re-persisted `150000`.
* `(a,f) = (100, U64Max−50)` → persisted `U64Max`, decoded `50`; this is the
  `pendingAmount_not_identity` witness and is copied from `store.rs:876-891`.
* `(a,f) = (99000, 1000)`, `Status.succeeded` → unchanged (`store.rs:850-860`).

**Why faithful.** The predicates `direction = inbound ∧ status = pending` and
the `saturating_add`/`saturating_sub` pair are the exact code at `store.rs:112-122`
and `:191-203`. The tests at `:818-891` already pin every vector above.
**Fidelity risk:** this models the **amount field only**, not the full
`PaymentDetails` TLV layout, `PaymentKind` enum, id/preimage/secret/timestamp
fields, or the `kind_opt`/hash fallback. Do not call it a full payment codec.
**Feasibility:** high — `Nat` arithmetic, `omega`/`simp`, and the overflow
witness by `decide`/`norm_num`.
**Classification:** model extension; no external assumption.

### T3 — Channel-config update semantics (P2, model extension)

**Module:** `LnLean/Proofs/Conformance/LdkChannelConfig.lean`

**Proposed names**

```lean
LnLean.Proofs.Conformance.LdkChannelConfig.update_absent_preserves
LnLean.Proofs.Conformance.LdkChannelConfig.update_partial_preserves_others
LnLean.Proofs.Conformance.LdkChannelConfig.update_cltv_max
LnLean.Proofs.Conformance.LdkChannelConfig.update_cltv_out_of_range
```

**Statement shape**

```lean
namespace LnLean.Proofs.Conformance.LdkChannelConfig

inductive MaxDust
  | fixedLimitMsat (limit : Nat)
  | feeRateMultiplier (multiplier : Nat)

structure ChannelConfig where
  feeProportionalMillionths : Nat
  feeBaseMsat                : Nat
  cltvExpiryDelta            : Nat
  maxDust                    : MaxDust
  forceCloseMaxFeeSat        : Nat
  acceptUnderpayingHtlcs     : Bool

structure ProtoChannelConfig where
  feeProportionalMillionths : Option Nat
  feeBaseMsat                : Option Nat
  cltvExpiryDelta            : Option Nat
  maxDust                    : Option MaxDust
  forceCloseMaxFeeSat        : Option Nat
  acceptUnderpayingHtlcs     : Option Bool
deriving Inhabited

def applyUpdate (current : ChannelConfig) (u : ProtoChannelConfig) :
    Option ChannelConfig :=
  match u.cltvExpiryDelta with
  | some n => if n ≤ 65535 then
      some { current with
        feeProportionalMillionths := u.feeProportionalMillionths.getD current.feeProportionalMillionths
        feeBaseMsat := u.feeBaseMsat.getD current.feeBaseMsat
        cltvExpiryDelta := n
        maxDust := u.maxDust.getD current.maxDust
        forceCloseMaxFeeSat := u.forceCloseMaxFeeSat.getD current.forceCloseMaxFeeSat
        acceptUnderpayingHtlcs := u.acceptUnderpayingHtlcs.getD current.acceptUnderpayingHtlcs }
    else none
  | none => some { current with
      feeProportionalMillionths := u.feeProportionalMillionths.getD current.feeProportionalMillionths
      feeBaseMsat := u.feeBaseMsat.getD current.feeBaseMsat
      maxDust := u.maxDust.getD current.maxDust
      forceCloseMaxFeeSat := u.forceCloseMaxFeeSat.getD current.forceCloseMaxFeeSat
      acceptUnderpayingHtlcs := u.acceptUnderpayingHtlcs.getD current.acceptUnderpayingHtlcs }

theorem update_absent_preserves (c : ChannelConfig) :
    applyUpdate c {} = some c

theorem update_partial_preserves_others
    (c : ChannelConfig) (u : ProtoChannelConfig)
    (h : u.feeProportionalMillionths = some 42)
    (hcltv : u.cltvExpiryDelta = none) :
    ∃ c', applyUpdate c u = some c' ∧
      c'.feeProportionalMillionths = 42 ∧ c'.cltvExpiryDelta = c.cltvExpiryDelta

theorem update_cltv_max (c : ChannelConfig) :
    applyUpdate c { cltvExpiryDelta := some 65535 } =
      some { c with cltvExpiryDelta := 65535 }

theorem update_cltv_out_of_range (c : ChannelConfig) (n : Nat) (h : 65535 < n) :
    applyUpdate c { cltvExpiryDelta := some n } = none
```

**Hypotheses.** `applyUpdate` takes the current config explicitly, matching the
handler's `unwrap_or(current)` construction. `update_cltv_out_of_range` needs
`n > 65535`; the max-witness theorem pins the inclusive bound.

**Non-vacuity witness.** The default config from
`refs/rust-lightning/lightning/src/util/config.rs:658-669`:
`(0, 1000, 72, FeeRateMultiplier 10000, 1000, false)`. The all-absent update is
`some` of exactly that record.

**Why faithful.** The function is a direct transcription of
`ldk-server/src/api/mod.rs:97-135`, including the `u16::try_from` bound and the
`oneof`-absent preservation. **Fidelity risk:** the server handler first looks
up the channel and parses `counterparty_node_id`
(`update_channel_config.rs:25-52`); those effects are not modelled, and the
`FIXME` at `:32-34` could later switch to LDK's partial update API, changing the
absent-field proof obligation. **Feasibility:** high — pure record update,
`split`/`simp`. **Classification:** model extension; no external assumption.

### T4 — Concrete feature byte codec (P1, model extension + pinned wire-layout fact)

**Module:** `LnLean/Proofs/Conformance/LdkFeatureCodec.lean`

**Proposed names**

```lean
LnLean.Proofs.Conformance.LdkFeatureCodec.decode_encodePadded
LnLean.Proofs.Conformance.LdkFeatureCodec.ldk_bitNumber
LnLean.Proofs.Conformance.LdkFeatureCodec.e2e_invoice_features
LnLean.Proofs.Conformance.LdkFeatureCodec.endianness_matters
```

**Statement shape**

```lean
namespace LnLean.Proofs.Conformance.LdkFeatureCodec

open LnLean.Proofs.Protocol

-- `b` is the wire byte array, in the order LDK writes it.
def bitNumber (width byteIdx bitPos : Nat) : Nat :=
  (width - 1 - byteIdx) * 8 + bitPos

def decode (b : ByteArray) : FeatureVector := ...

def encodePadded (f : FeatureVector) (width : Nat) : ByteArray := ...

theorem decode_encodePadded (f : FeatureVector) (width : Nat)
    (hb : f.Bounded) (hw : f.byteLen = width) :
    decode (encodePadded f width) = f

theorem ldk_bitNumber (width byteIdx bitPos : Nat)
    (hb : byteIdx < width) (hp : bitPos < 8) :
    bitNumber width byteIdx bitPos < 8 * width

theorem e2e_invoice_features :
    (decode #[0x02, 0x41, 0x00]).requires 4 = true ∧
    (decode #[0x02, 0x41, 0x00]).requires 7 = true ∧
    (decode #[0x02, 0x41, 0x00]).offersOptional 8 = true

theorem endianness_matters :
    (decode #[0x01, 0x00]).hasBit 8 = true ∧
    (decode #[0x00, 0x01]).hasBit 0 = true ∧
    (decode #[0x00, 0x01]).hasBit 8 = false
```

**Hypotheses.** `decode_encodePadded` requires the vector to be `Bounded` and
the chosen width to equal `f.byteLen`. It is a **padded-width** round-trip; it
does not claim LDK strips trailing zero bytes or that BOLT 11's `9` field uses a
minimal width. R10 T5 owns minimal-width/pairing. The `u16` length prefix that
LDK's `Writeable` places before the feature bytes is stripped by the fixture
driver; this target is the feature payload, not the length-prefixed message.

**Non-vacuity witnesses.** The e2e vector `02 41 00` has bits 8, 14, 17; feature
numbers 4 (`VariableLengthOnion` required), 7 (`PaymentSecret` required), and 8
(`BasicMPP` optional). The empty vector and the high-bit vector (bit 255 in a
32-byte array) are additional witnesses. `endianness_matters` is the
counterexample to a naive little-endian byte mapping.

**Why faithful.** `write_be` reverses `le_flags`
(`lightning/src/ln/features.rs:24-33`), and `features_to_proto` uses
`byte_idx * 8 + bit_pos` over `le_flags`
(`ldk-server/src/util/proto_adapter.rs:663-698`). The e2e expectations at
`ldk-server/e2e-tests/tests/e2e.rs:274-296` pin the three names/parities.
**Fidelity risk:** the byte order is the trap; the existing `FeatureCodec` doc
comment says “big-endian byte packing” (`FeaturesProps.lean:480-486`) but the
bit numbering inside each byte is LSB-first. A codec that reverses the bits
instead of the bytes will pass a naive round-trip and fail the e2e vector.
**Feasibility:** medium — `ByteArray`/`Nat.testBit` arithmetic, `funext`, and
`decide` for the finite witnesses. **Classification:** model extension; the
wire layout is an external pinned fact, not a cryptographic assumption.

### T5 — Request-binding grammar (P2, defer to R15 T8; external boundary)

**Module:** do **not** add a competing module. R15 T8 owns
`LnLean.Proofs.Protocol.RequestBindingTargets` and proposes
`parseProof_renderProof` (`agents/reports/wave13-review/R15-bolt8-transport.md`
§T8).

If a conformance-only slice is later wanted, the names should be:

```lean
LnLean.Proofs.Conformance.RequestBindingGrammar.parse_render
LnLean.Proofs.Conformance.RequestBindingGrammar.parse_rejects_leading_zero
LnLean.Proofs.Conformance.RequestBindingGrammar.parse_rejects_bad_digest
LnLean.Proofs.Conformance.RequestBindingGrammar.parse_rejects_bad_method
```

**Statement shape.** `parse (render b) = some b` for `Valid b`; rejection
theorems for the exact `macaroon.rs:335-370` invalid strings.

**Why this is not a new target now.** The grammar is deterministic and
fixture-friendly (D26–D28), but the security-relevant claim is the HMAC-SHA256
chain, which is external (`Crypto/Model.lean:84-92`, `:115-116`; R15 D8).
Duplicating R15 T8 would create two names for one contract. **Classification:**
model extension for the grammar, **external assumption** for the binding.
**Priority:** P2. **Feasibility:** medium. **Recommendation:** defer.

## 5. Assumptions, counterexamples, and non-vacuity risks

### 5.1 Counterexamples that must remain visible

| Counterexample | Why it matters | Must not be “fixed” by |
|---|---|---|
| `PaymentDetails` overflow: net `100`, fee `MAX−50` → persisted `MAX` → decoded `50` | The write/read pair is intentionally not an identity on overflow. A theorem that assumes `a+f ≤ MAX` must say so, and a separate non-identity theorem must preserve the witness. | Replacing `saturating_add` with checked addition, or claiming a total round-trip |
| Legacy gross vector: `100000`/`150000` → decoded `0`, persisted `150000` | A fee larger than the gross amount clamps at zero; the record stays readable and re-persists with the full fee. Completed/outbound records are not adjusted at all. | Rejecting the record, allowing a negative amount, or applying the fee adjustment unconditionally |
| Legacy `ChannelClosed` without counterparty is rejected | Missing type 1 is not `None`; it is a decode error. | A generic “optional absent → none” decoder |
| Legacy `PaymentForwarded` without type 14 becomes `Some(0)` | Missing type 14 has an explicit default, unlike a generic optional. | Treating every absent optional as `none` |
| Feature bytes `01 00` vs `00 01` encode different bits | The wire is big-endian while the bit index is LSB-first. | Reversing bits instead of bytes, or vice versa |
| `cltv_expiry_delta = 65536` is rejected | The bound is inclusive at 65535; an unchecked cast would wrap to 0. | `UInt16` truncation or “default to 65535” |
| Absent channel-config fields preserve the **current** config | The server builds a full config from the current one; protobuf zero values are not the defaults. | Treating `None` as `0`/`false` |
| Live e2e lifecycle assertions are sampled | They depend on bitcoind, async delivery, and timing. | Promoting a sampled assertion to a universal theorem |

### 5.2 Non-vacuity requirements

Every proposed target must ship with at least one closed witness in the same
module:

* T1: the `ChannelReady`, `ChannelClosed`, `PaymentForwarded`, and queue
  witnesses from D6–D8; the legacy rejection/default witnesses must be
  separate theorems, not hypotheses.
* T2: the seven vectors from D14 plus the D15 overflow witness; the
  `pendingAmount_not_identity` existential must be inhabited by
  `(100, MAX−50)`.
* T3: the default config witness from D16; an all-absent update; a one-field
  update; the `65535`/`65536` pair.
* T4: the e2e `02 41 00` vector, the empty vector, and the `01 00`/`00 01`
  endianness pair.

A target whose only inhabitant is the empty event/queue/config is not
acceptable. `decide`-only theorems are acceptable for finite vectors, as in the
existing conformance modules, provided the corresponding generic law (if
claimed) is proved separately.

### 5.3 What must not be claimed

* **Not** a full LDK Node `Event` codec: the slice covers three variants.
* **Not** a full `PaymentDetails` serializer: only the amount normalization and
  the legacy BOLT 11/Spontaneous fallback.
* **Not** full channel-config RPC behaviour: channel lookup, counterparty
  parsing, and `update_channel_config` are not modelled.
* **Not** a full BOLT 9 feature table or BOLT 11 bech32 decoder: R10 T5/T3 own
  those; this module only supplies a byte-level foundation.
* **Not** request-binding security: the grammar is not the HMAC chain.
* **Not** node-level interoperability: the live suite remains evidence, not a
  theorem.
* **Not** a stronger result than the checker can audit: the Python checker is
  syntactic and does not run Lean (§1.2). New theorem names must be built in a
  module-only `lake build` and, where possible, audited with `#print axioms`.

### 5.4 Axiom and scope discipline

Existing conformance modules use only kernel reduction and the allowed axioms
(`propext`, `Quot.sound`, `Classical.choice`). The new targets should follow the
same discipline. `funext` is already used in this tree and is acceptable for
`FeatureVector` extensionality. No new axiom, `sorry`, `native_decide`, or
`implemented_by` should be introduced. The abstract `FeatureCodec` and
`FeatureVector` must not be weakened to make a concrete instance easier; add the
instance beside them.

## 6. Wave-13 recommendation

### 6.1 Verdict

**Implement a narrow, additive conformance lane; do not treat the whole surface
as external.** The safest first increment is **T2 + T3 + T4**:

1. **T2** (`LdkPaymentCodec`) is the top target: pure arithmetic, exact source
   transcription, a sharp overflow counterexample, and no crypto or network.
2. **T3** (`LdkChannelConfig`) is the second: pure record update, exact
   absent-field and `u16` semantics, high feasibility.
3. **T4** (`LdkFeatureCodec`) is the shared foundation; it unblocks the server
   feature projection and gives R10 T5 a byte-level base without replacing it.

**T1** (event codec) is valuable but larger: it needs a TLV recursive decoder and
a carefully scoped three-variant slice. Schedule it as the second increment, not
the first. **T5** (request binding) should be deferred to R15 T8; **BOLT 11
bech32** to R10; **live interop** and **HMAC/SHA-256** remain external.

This is a safe implementation lane because it adds modules and fixtures without
changing any existing theorem or catalogue row. It should not be called a
`CONF-01` closure: the five live BOLT 2 rows stay as they are, and the new
targets cover additional encodings only.

### 6.2 Fixture families and mutation controls

A second, additive fixture tree is recommended:

```text
tests/conformance/ldk/
  README.md
  fixtures.json                 # schema: lnlean.ldk.differential.v1
  generate.py                   # deterministic re-derivation / verification
  probe/                        # pinned Cargo.lock + public-API probe (optional)
  live-transcript.json          # only for the live-probe subset
```

`scripts/check-conformance.py` should not be bent to accept a second pin and
schema by editing its hard-coded constants. Either add a `--ldk` mode with a
schema dispatch or add `scripts/check-ldk-conformance.py`; share the mutation
validator, but keep the rust-lightning provenance and pin checks separate. R23
§1.2 reaches the same conclusion for server fixtures.

| Family | Contents | Determinism | Mutation controls |
|---|---|---|---|
| **F1 `ldk-node.event`** | `ChannelReady` canonical bytes; `ChannelClosed` with/without counterparty; `PaymentForwarded` with/without type 14; multi-HTLC forward; one-event queue with `u16` count; empty queue | Deterministic public `Writeable`/`Readable`; no chain | 1. flip variant tag 3→5; 2. delete required type 2; 3. shorten a TLV length by one; 4. duplicate a type id; 5. drop legacy counterparty; 6. set queue count 1→2 with one event; 7. insert unknown type and require skip-or-reject per the declared policy |
| **F2 `ldk-node.payment`** | Seven vectors from D14; overflow vector D15; non-pending/outbound unchanged; legacy no-kind + secret → Bolt11; legacy no-kind + no secret → Spontaneous | Deterministic public `Writeable`/`Readable`; no chain | 1. remove the saturating clamp; 2. add the fee twice; 3. subtract the fee twice; 4. apply the adjustment to `Succeeded`; 5. apply it to `Outbound`; 6. swap `counterparty_skimmed_fee_msat` with `fee_paid_msat`; 7. make the second write add the fee again (idempotence break) |
| **F3 `ldk-server.channel-config`** | Default config; all-absent update; each field present alone; `cltv` 0, 1, 65535 accept and 65536 reject; both max-dust variants; bool true/false | Deterministic **source-derived** from `build_channel_config_from_proto`; no live probe (function is `pub(crate)`) | 1. absent→0 instead of preserve; 2. bound 65535→65534; 3. truncate 65536→0 instead of reject; 4. absent max-dust→FixedLimit 0; 5. absent bool→false; 6. swap fee fields; 7. ignore present fields |
| **F4 `ldk.features`** | Empty; bit 8 required (`0100`); bit 14 required (`4000`); bit 17 optional (`020000`); e2e `024100`; high bit 255; both bits of a pair set | Deterministic public `Bolt11InvoiceFeatures`/`InitFeatures` `Writeable` (or source-derived if the probe is not built) | 1. remove byte reversal; 2. swap required/optional parity; 3. trim/keep a trailing zero byte (width control); 4. reverse bits within a byte; 5. length prefix 3→2; 6. set both pair bits (codec may accept; BOLT 9 well-formedness must reject — do not conflate) |
| **F5 `ldk-server.request-binding`** | Canonical `123 GetNodeInfo` + `ab`×32; max `u64` + 128×`X` + `ff`×32; the invalid list from D28 | Deterministic grammar; HMAC external | 1. leading-zero timestamp; 2. uppercase digest; 3. 129-byte method; 4. extra field; 5. double space; 6. wrong prefix. **Defer with R15 T8.** |

**Live-only, not fixture families:** channel pending/ready/closed and force-close
(D29–D30), server startup/TLS/macaroon/MCP/PostgreSQL (D31), and live BOLT 11
decode (D32). Record these in a live transcript if needed, but do not turn them
into Lean theorems.

### 6.3 Implementation order and gates

1. **T2** (`LdkPaymentCodec`) — highest value per line; add the D14/D15 vectors
   and the non-identity theorem.
2. **T3** (`LdkChannelConfig`) — pure, independent; add the default/absent/bound
   matrix.
3. **T4** (`LdkFeatureCodec`) — shared foundation; add the e2e vector and the
   endianness counterexample.
4. **T1** (`LdkEventCodec`) — second increment; start with `ChannelReady` and
   the two legacy laws before the full three-variant round-trip.
5. **F1–F4 fixture documents** — only after the corresponding Lean targets
   compile. Add the checker mode in the same change as the first fixture
   document, not later.
6. **Do not** change `CONF-01` to closed. Update its evidence sentence and keep
   it open for the remaining live/interop surface.

Module-only build gate (no whole-tree build, no network):

```sh
export PATH=/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Proofs.Conformance.LdkPaymentCodec \
    LnLean.Proofs.Conformance.LdkChannelConfig \
    LnLean.Proofs.Conformance.LdkFeatureCodec
```

The event target, once written, adds
`LnLean.Proofs.Conformance.LdkEventCodec` to that list. The existing
`scripts/check-conformance.py` remains the gate for the rust-lightning suite;
the new checker is additive.

### 6.4 External/human barriers

* **HMAC-SHA256 request binding** — a real cryptographic binding is external;
  the grammar is not the security claim (R15 §1.4).
* **BOLT 11 bech32/checksum/payee recovery** — R10 owns it; do not duplicate.
* **Live channel/payment lifecycle** — bitcoind, server processes, async event
  delivery, timing; sampled assertions are not universal laws.
* **Full `Event`/`PaymentDetails` serializers** — large macro-generated enums;
  the proposed slices are deliberately partial.
* **Server `build_channel_config_from_proto` live probe** — the function is
  `pub(crate)`; a live probe would need a test-only export or a server e2e run.
  The F3 family is source-derived and must say so.

## 7. Evidence and commands

All commands below were run read-only from `/home/ubuntu/ln-lean-repair` on
branch `repair/integrated` at `f7f0628`. No Lean, docs, scripts, tests, vendor,
or other reports were edited; only this file was written. No cargo test that
fetches the network was run, and no whole-tree build was run.

### 7.1 Suite status

```sh
python3 scripts/check-conformance.py
```

Observed output (tail):

```text
vectors: 12 BigSize encode, 25 BigSize decode, 24 TLV
checks:  61 vector expectations validated
BOLT 1 Appendix A anchors: 26 published entries matched
TLV: 22 enforced cases, 2 declared not-modelled gaps
framing: 16 cases (6 accept, 10 reject), 9 length boundaries
messages: 6 BOLT 2 payload/field vectors
differential: 26 rust-lightning BigSize, 3 TLV, 4 wire, 5 BOLT 2 message fixtures
live evidence: ... transcript sha256 a47b2aa4a2e1
provenance: 5 pinned rust-lightning source files verified (HEAD verified)
Lean sync: 200 theorem references checked ...
promoted transport: 13/13 theorems, 6/6 definitions checked
mutation controls: 22/22 detected
RESULT: PASS (vector/differential conformance, not a full implementation test)
```

```sh
python3 tests/conformance/rust-lightning/generate.py --check
```

Observed output:

```text
fixtures: 26 BigSize, 3 TLV, 4 wire, 5 message match the pinned source
provenance: 5 source files verified at fe49009
live cargo test: recorded in tests/conformance/rust-lightning/live-transcript.json (a47b2aa4a2e1)
```

### 7.2 Source inspection

Key reads used for the datapoints:

```sh
sed -n '100,220p' /tmp/opencode/ldk-refs/ldk-node/src/payment/store.rs
sed -n '320,420p' /tmp/opencode/ldk-refs/ldk-node/src/event.rs
sed -n '495,560p' /tmp/opencode/ldk-refs/ldk-node/src/event.rs
sed -n '2840,3068p' /tmp/opencode/ldk-refs/ldk-node/src/event.rs
sed -n '780,900p' /tmp/opencode/ldk-refs/ldk-node/src/config.rs
sed -n '80,140p' /tmp/opencode/ldk-refs/ldk-server/ldk-server/src/api/mod.rs
sed -n '1,80p' /tmp/opencode/ldk-refs/ldk-server/ldk-server/src/api/update_channel_config.rs
sed -n '655,705p' /tmp/opencode/ldk-refs/ldk-server/ldk-server/src/util/proto_adapter.rs
sed -n '260,300p' /tmp/opencode/ldk-refs/ldk-server/e2e-tests/tests/e2e.rs
sed -n '18,105p' /tmp/opencode/ldk-refs/ldk-server/ldk-server-macaroons/src/macaroon.rs
sed -n '330,375p' /tmp/opencode/ldk-refs/ldk-server/ldk-server-macaroons/src/macaroon.rs
sed -n '650,700p' refs/rust-lightning/lightning/src/util/config.rs
sed -n '20,100p' refs/rust-lightning/lightning/src/ln/features.rs
sed -n '270,360p' refs/rust-lightning/lightning-types/src/features.rs
sed -n '1201,1290p' scripts/check-conformance.py
```

### 7.3 Repository state

```sh
git rev-parse --short HEAD   # f7f0628
git branch --show-current    # repair/integrated
```

`git status --short` shows this report plus the pre-existing lane artefacts;
no tracked file was modified by this review.

### 7.4 Pin note

`agents/reports/wave13-review/LDK-REFS.md` records the LDK reference paths and
pins. The rust-lightning source used for the feature/config defaults is the
worktree checkout `refs/rust-lightning` at `fe49009`
(`docs/OPEN-ISSUES.md:68`, `CONF-02`). The LDK Node and LDK Server checkouts are
the read-only clones under `/tmp/opencode/ldk-refs/`.
