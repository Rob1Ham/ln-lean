# R13 — BOLT 7 gossip validation, store, and epochs

**Status:** read-only review
**Pins:** LDK Node `fa123fed131e27ecc420b77fa7086fcf1ddaebb8`, LDK Server `c17dc11dde38f88c53457039ddf30c6b90a63ba2`

## 1. Scope and current Lean surface

This lane covers the public BOLT 7 gossip path: `channel_announcement`,
`channel_update`, `node_announcement`, the resulting routing graph, and the
store/epoch layer. It does **not** cover the private-channel path, gossip
queries, peer dissemination, or the Lightning wire codec except where those
are needed to state a validation gap.

The current Lean surface has seven layers. They are adjacent, but only the
canonical/epoch layers are connected by a refinement theorem, and that
refinement is about *store shape*, not about LDK's validation or graph policy.

| Layer | Main declarations | What it actually claims | What it does not claim |
|---|---|---|---|
| Wire records | `ChannelAnnellation` (`LnLean/Routing/Gossip.lean:108-122`), `ChannelUpdate` (`:155-168`), `NodeAnnouncement` (`:200-208`) | The BOLT 7 fields that the model keeps, including four announcement signatures and one update signature | No `chain_hash` field on either announcement or update (`:108-122`, `:155-168`); no wire encoding; no funding-script/UTXO data |
| Raw store | `GossipState` (`:272-276`), `GossipState.applyUpdate` (`:287-290`), `applyGossip` (`:328-331`) | Append-only lists; one global update clock; stale updates are ignored | No signature filter, no announcement dedup, no per-direction clock. The docstring at `:268-271` says the production `(scid, direction)` key is deliberately not modelled |
| Canonical admission | `admitGossipCanonical` (`LnLean/Proofs/Routing/GossipCanonicalTargets.lean:162-188`), `applyGossipCanonicalStore` (`LnLean/Proofs/Routing/GossipRawRefinementTargets.lean:120-145`) | Four-signature announcement gate; `node1 ≠ node2`; node-key registration compatibility; update authorisation; strict per-slot timestamp replacement; replacement by `scid` / `(scid, direction)` | No `wellFormed` gate, no `dont_forward`, no freshness window, no `htlc_maximum_msat` bound, no sorted wire keys, no distinct Bitcoin keys, no positive capacity, no chain/UTXO check |
| Materialised views | `ChannelView` (`LnLean/Proofs/Routing/GossipProps.lean:153-165`), `admittedChannelView` (`LnLean/Proofs/Routing/GossipTargets.lean:340-349`), `viewGraph` (`GossipProps.lean:299-301`) | One view per announced channel; `applyUpdate` checks only `scid` and timestamp (`GossipProps.lean:196-204`) | No direction field; no second view; no `htlc_minimum_msat`/`htlc_maximum_msat`; before any update the view is already enabled with zero fees and `cltvDelta = 0` |
| Node canonicalisation | `NodeSupersedes` (`LnLean/Proofs/Routing/NodeCanonicalTargets.lean:137-138`), `applyGossipNodeCanonical` (`:348-361`) | Additive signature-plus-strict-timestamp node replacement | The core `admitGossipCanonical` / `applyGossipCanonicalStore` still append nodes; neither requires the node key to be known from a channel announcement |
| Epoch/replacement history | `StoreEpoch` (`LnLean/Proofs/Routing/GossipStoreEpochTargets.lean:128-146`), `epochStep` (`:209-222`), `epochFold` (`:312`) | In-memory epoch counter, typed replacement events, canonical-store square (`epochFold_store_eq_foldl` `:342`; `epochFold_gossip_eq_canonicalStoreView_rawFold` `:877`) | No serialization, no durable store, no replay of persisted bytes; not LDK persistence |
| Address parsing | `NodeAddressTargets` (`LnLean/Proofs/Routing/NodeAddressTargets.lean`) | Byte-level BOLT 7 `addrlen` blob, typed descriptors, nonzero ports, ascending type order, at most one DNS name | It is disconnected from `NodeAnnouncement.addresses` and from admission; DNS/Tor resolution and reachability are out of scope |

Catalog status is narrow and should not be read as coverage of this lane:

* `LN-RT-002` is `Gossip.update_monotone` plus the canonical/node/epoch layers
  (`docs/THEOREM-INDEX.md:69`; `docs/TRACEABILITY.md:48`). It is a
  timestamp/replacement and store-shape claim, not a claim that LDK accepts
  the same messages.
* `LN-RT-006` is `GossipTargets.gossip_graph_only_valid_announcements`
  (`docs/THEOREM-INDEX.md:73`; `GossipTargets.lean:713`). It says every edge
  is backed by a four-signature-valid announcement. It does **not** say the
  edge has a valid matching `channel_update`, has the correct direction, or
  has the correct fee/CLTV/HTLC bounds.
* `LN-GOSSIP-001`, `LN-GOSSIP-002`, and `LN-GOSSIP-003` are module-prose
  claims in `GossipProps.lean:944-1061`, not catalog rows. They are refuted in
  the raw model and retained only in conditional form.

Three negative facts organise the rest of this report.

1. **The materialised view is direction-blind.** `ChannelView` has no
   direction field (`GossipProps.lean:153-165`), and
   `ChannelView.applyUpdate` guards only on `v.scid = u.shortChannelId` and
   `v.timestamp < u.timestamp` (`:196-204`). A correctly attributed
   direction-1 update can therefore overwrite the single forward view.
   `admitGossipCanonical` does this by mapping the update over every view
   (`GossipCanonicalTargets.lean:179`), and `admitGossipDirected` does the
   same (`GossipKeyConsistencyTargets.lean:85-110`). The direction-keyed
   store is correct; the view is not.
2. **An announcement is immediately routable.** `admittedChannelView` sets
   `feeBaseMsat = 0`, `feeProportionalMillionths = 0`, `cltvDelta = 0`,
   `timestamp = 0`, and `disabled = false` (`GossipTargets.lean:340-349`).
   `ChannelView.edge` maps that to `enabled := true` (`GossipProps.lean:170-178`),
   and `Graph.findEdge` selects enabled edges (`LnLean/Routing/Graph.lean:158-170`).
   LDK stores `one_to_two: Option<ChannelUpdateInfo>` and
   `two_to_one: Option<ChannelUpdateInfo>` and refuses a directed view unless
   both are present (`refs/rust-lightning/lightning/src/routing/gossip.rs:1012-1055`).
3. **Canonical admission is not LDK validation.** The canonical gate is
   signatures + distinct graph endpoints + registration + update
   authorisation (`GossipCanonicalTargets.lean:164-180`). It never calls
   `ChannelUpdate.wellFormed` (`Gossip.lean:179-181`), never inspects
   `message_flags` bit 1, and has no chain/UTXO/capacity/confirmation input.

## 2. LDK datapoints (with `file:line`)

LDK Node/Server refs are under `/tmp/opencode/ldk-refs/`; rust-lightning and
BOLT refs are under `refs/` in this repository. The local rust-lightning pin
is `fe4900930c6bd5786ec4203274d7cf312776a5a6`. LDK Node pins rust-lightning
`d7a980641c6325ddda5072a0f470ef8392676cf5`
(`/tmp/opencode/ldk-refs/ldk-node/Cargo.toml:89`), so rust-lightning citations
below are behavioural references, not the exact ldk-node dependency.

### 2.1 The graph view is explicitly two-directional

* LDK's `ChannelInfo` stores both directions as separate optional records:
  `one_to_two: Option<ChannelUpdateInfo>` and
  `two_to_one: Option<ChannelUpdateInfo>`
  (`refs/rust-lightning/lightning/src/routing/gossip.rs:1012-1034`).
  `ChannelInfo::as_directed_to` returns `None` if either direction is
  missing, then selects `two_to_one` for traffic to `node_one` and
  `one_to_two` for traffic to `node_two` (`:1046-1055`).
* LDK Node's public wrapper exposes the same shape:
  `NetworkGraph::channel(short_channel_id) -> Option<ChannelInfo>` returns a
  record with `node_one`, `one_to_two`, `node_two`, `two_to_one`, and
  `capacity_sats: Option<u64>`
  (`/tmp/opencode/ldk-refs/ldk-node/src/graph.rs:42`, `:64-75`).
  `ChannelUpdateInfo` carries `last_update`, `enabled`, `cltv_expiry_delta`,
  `htlc_minimum_msat`, `htlc_maximum_msat`, and fees (`:95-115`).
* LDK Server's graph API projects both directions without merging them:
  `graph_channel_to_proto` sets `node_one`, `node_two`, `capacity_sats`,
  `one_to_two`, and `two_to_one`
  (`/tmp/opencode/ldk-refs/ldk-server/ldk-server/src/util/proto_adapter.rs:624-631`;
  proto fields at
  `/tmp/opencode/ldk-refs/ldk-server/ldk-server-grpc/src/proto/types.proto:1064-1080`).
  `graph_get_channel` returns a not-found error when the `scid` is absent
  (`/tmp/opencode/ldk-refs/ldk-server/ldk-server/src/api/graph_get_channel.rs:19-34`),
  and `graph_list_channels` lists graph keys only
  (`.../graph_list_channels.rs:17-23`).
* The e2e helper treats a remote channel as routable only when **both**
  directions exist and are enabled:
  `channel.one_to_two.as_ref().is_some_and(|u| u.enabled) &&
  channel.two_to_one.as_ref().is_some_and(|u| u.enabled)`
  (`/tmp/opencode/ldk-refs/ldk-server/e2e-tests/src/lib.rs:1207-1212`).
  The preceding comment notes that a peer update can arrive before our own
  announcement and be dropped; local channels are handled by live channel
  state instead (`:1198-1206`).

Consequence: “one channel has two directional policies, each optional until
its `channel_update` arrives” is a first-class LDK graph invariant. Lean's
single `ChannelView` cannot express it.

### 2.2 Channel announcement validation

* Four signatures are verified over the double-SHA256 of the announcement
  contents, using `node_id_1`, `node_id_2`, `bitcoin_key_1`, and
  `bitcoin_key_2` (`refs/rust-lightning/lightning/src/routing/gossip.rs:515-546`).
* The pre-validation gate rejects `node_id_1 >= node_id_2` (sorted order),
  equal Bitcoin keys, and a `chain_hash` that is not the graph's chain
  (`:2122-2145`). The comments/errors are explicit:
  “node_ids in channel_announcements must be sorted” (`:2126-2131`),
  “Channel announcement node had a channel with itself” (`:2133-2138`), and
  “chain hash does not match genesis hash” (`:2140-2145`).
* Existing-channel handling distinguishes chain-validated duplicates from
  unvalidated ones; without a UTXO lookup an unvalidated duplicate is
  ignored (`.gossip.rs:2147-2173`). Removed-channel/removed-node blacklists
  are checked before insertion (`:2189-2201`).
* Capacity is not trusted from the message. It is `utxo_value.map(|a|
  a.to_sat())` after `check_channel_announcement` (`:2201`, `:2220`); the
  result is `capacity_sats: Option<u64>` (`:1028`). If no `UtxoLookup` is
  configured, capacity remains `None`.
* LDK Node constructs the P2P gossip sync with an optional UTXO verifier from
  the chain source (`/tmp/opencode/ldk-refs/ldk-node/src/gossip.rs:37-52`);
  without a chain source the verifier is `None`. RGS uses
  `RapidGossipSync` without a UTXO lookup (`:56-60`, `:93`).
* BOLT 7 requires `node_id_1` to be the lexicographically lesser compressed
  key, `bitcoin_key_1`/`bitcoin_key_2` to be the funding keys, and the
  funding output to be P2WSH (`refs/bolts/07-routing-gossip.md:189-203`).
  Receivers must ignore unsorted ids (`:213-215`), an unknown chain
  (`:224-226`), a wrong/spent output (`:219-223`), and an output with fewer
  than six confirmations unless it is close (`:226-233`).

### 2.3 Channel update validation and policy

* The P2P handler rejects `dont_forward` before touching the graph:
  “Ignore channel updates with dont_forward bit set - these are for private
  channels and shouldn't be gossiped or stored in the network graph”
  (`refs/rust-lightning/lightning/src/routing/gossip.rs:551-565`). The bit
  is bit 1 of `message_flags`; BOLT 7 defines it at `:475`, and requires
  private-channel updates to set it and not forward them (`:491-495`).
* `update_channel_internal` rejects a mismatched `chain_hash`
  (`:2474-2481`), a timestamp older than two weeks or more than one day in
  the future (`:2483-2511`), and `htlc_maximum_msat > MAX_VALUE_MSAT`
  (`:2517-2523`). These are `std`/non-test checks; tests deliberately bypass
  the age window.
* It selects the directional slot from `channel_flags & 1`: bit 0 means
  `one_to_two`, bit 1 means `two_to_one`
  (`:2533-2538`, `:2583-2587`). The node key used for signature verification
  is the corresponding `node_one` or `node_two` (`:2583-2598`).
* It rejects a `channel_update` for an unknown channel
  (“Couldn't find channel for update”, `:2575-2579`) and checks that
  `htlc_maximum_msat` is at most `capacity_sats * 1000` when capacity is
  known (`:2544-2560`). A capacity above `MAX_VALUE_MSAT / 1000` is also
  treated as bogus (`:2550-2558`).
* BOLT 7 receiving rules are explicit: unknown `chain_hash` -> ignore
  (`refs/bolts/07-routing-gossip.md:548-550`); equal timestamp -> ignore or
  blacklist (`:551-558`); lower timestamp -> ignore (`:558-560`);
  unreasonably future timestamp -> may discard (`:561-563`);
  `htlc_maximum_msat < htlc_minimum_msat` -> ignore for routing (`:567-568`);
  `htlc_maximum_msat > capacity` -> ignore for routing (`:569-571`).
* The origin rules also require `timestamp > 0` and greater than any
  previous update for the channel (`:517-519`), `must_be_one` bit 0
  (`:525-527`), and `htlc_maximum_msat <= capacity` (`:505-507`). LDK's
  receiver does not reject `must_be_one = 0`; it does reject `dont_forward`.

### 2.4 Node announcement validation

* LDK verifies the node signature over the double-SHA256 of the contents
  using `node_id` (`refs/rust-lightning/lightning/src/routing/gossip.rs:497-513`).
* The node entry must already exist. `update_node_from_announcement_intern`
  matches on `nodes.get_mut(&msg.node_id)`; `None` returns
  “No existing channels for node_announcement”
  (`:1910-1938`). The comment on `update_node_from_announcement` says “For
  an already known node (from channel announcements)” (`:1881-1884`).
* A stored node record is replaced only by a strictly newer timestamp;
  equal or older timestamps are duplicate/ignored errors
  (`:1940-1949`). BOLT 7 requires the node id to be previously known from a
  `channel_announcement` and the timestamp to be greater than the
  last-received one (`refs/bolts/07-routing-gossip.md:381-384`).
* Address parsing is a separate BOLT 7 field: ascending descriptor types,
  nonzero ports, at most one type-5 DNS name
  (`refs/bolts/07-routing-gossip.md:341-371`). Lean models this in
  `NodeAddressTargets` but does not connect it to the admission path.

### 2.5 Persistence

* LDK Node reads a persisted graph with `NetworkGraph::read(...)` from the
  `NETWORK_GRAPH_PERSISTENCE_*` namespace
  (`/tmp/opencode/ldk-refs/ldk-node/src/io/utils.rs:102-120`), and the
  builder calls `read_network_graph` during startup
  (`/tmp/opencode/ldk-refs/ldk-node/src/builder.rs:2019`).
* The background processor writes `network_graph.encode()` to the
  persister (`refs/rust-lightning/lightning-background-processor/src/lib.rs:1273-1289`;
  also `:1427-1434`). The persisted graph is the same two-directional
  `ChannelInfo` structure, not a flattened list of edges.
* Lean has no graph codec and no persistence relation. `StoreEpoch`
  (`GossipStoreEpochTargets.lean:128-146`) is an in-memory event history; it
  does not encode or decode bytes and does not prove that a restarted graph
  equals the pre-restart graph.

## 3. Gap matrix

| Behavior | Lean status | LDK evidence | Gap / counterexample | Priority |
|---|---|---|---|---|
| `channel_announcement` four-signature gate | partially covered | `gossip.rs:515-546`; canonical gate `GossipCanonicalTargets.lean:164-167` | The gate exists, but `SigVerifier` is abstract and a 64-byte length check is not required; `accepted_update_signature_length_counterexample` (`GossipProps.lean:1047-1051`) shows the verifier can accept an empty signature. Unforgeability is C3/C4/C8 | P1/external |
| `node_id_1` / `node_id_2` distinct | covered at graph level | `gossip.rs:2126-2131`; BOLT 7 `:213-215` | `a.node1 ≠ a.node2` is checked (`GossipCanonicalTargets.lean:165`). This is a graph `NodeId` distinctness, not wire `nodeKey1 ≠ nodeKey2` | P2 |
| Sorted wire node keys (`node_id_1 < node_id_2`) | missing | `gossip.rs:2125-2131`; BOLT 7 `:189-191` | No order predicate on `PubKey`. A channel with `nodeKey1 > nodeKey2`, or even `nodeKey1 = nodeKey2`, passes if `node1 ≠ node2` | P1 |
| Distinct Bitcoin keys | missing | `gossip.rs:2133-2138`; BOLT 7 `:192-194` | `bitcoinKey1 = bitcoinKey2` is admitted; no gate compares them | P1 |
| `chain_hash` matches the graph | unmodelled/external | `gossip.rs:2140-2145`; BOLT 7 `:224-226` | Neither `ChannelAnnellation` nor `ChannelUpdate` has a `chain_hash` field | P2 external |
| Funding UTXO exists, is P2WSH, unspent | unmodelled/external | `gossip.rs:2201-2231`; BOLT 7 `:219-226` | No UTXO/funding-script/chain state. `ChannelAnnellation` carries only `capacitySat : Nat` | P2 external |
| Six confirmations | unmodelled/external | BOLT 7 `:207-233`; LDK's UTXO check via `chain_source` (`ldk-node/src/gossip.rs:37-52`) | No block height or confirmation relation | P2 external |
| Capacity is the funding output value, positive | missing | `gossip.rs:2220`; `bindChannel_capacity_positive_counterexample` (`GossipProps.lean:1015-1023`) | `capacitySat` is an unconstrained `Nat`; zero-capacity announcements bind and are admitted | P1 |
| Duplicate/conflicting `scid` | partially covered | `gossip.rs:2147-2173` | Canonical replacement keeps one record per `scid` (`insertReplacing`), but it has no chain-validated duplicate policy or removed-channel blacklist. Raw `applyGossip` still appends conflicts (`raw_applyGossip_accepts_conflicting_announcement`, `GossipKeyConsistencyTargets.lean:807-817`) | P1/P2 |
| `channel_update` signature and direction-selected key | covered faithfully (canonical) | `gossip.rs:2583-2598`; `ChannelUpdate.direction` (`Gossip.lean:606-607`), `attributesKeyForDirection` (`:645-647`), `updateKeyAnnouncedDirectional` (`:694-698`) | The canonical gate requires a direction-correct announced key. It does not inspect the signing key's curve/length; the verifier is abstract | P2 |
| `channel_update` requires a prior `channel_announcement` | covered for public channels; private path missing | `gossip.rs:2575-2579`; BOLT 7 `:534-540` | `updateKeyAnnouncedDirectional` requires an announcement. LDK also accepts updates for its own non-public channels; Lean has no private/own-channel path | P2 |
| `dont_forward` bit 1 of `message_flags` | missing | `gossip.rs:551-565`; BOLT 7 `:475`, `:491-495` | `messageFlags` is stored raw (`Gossip.lean:158`) but no admission gate rejects bit 1. A validly signed update with `messageFlags = 2` is admitted | P1 |
| `ChannelUpdate.wellFormed` (timestamp > 0, `cltvDelta > 0`, min <= max) | predicate only, not enforced | BOLT 7 `:517-524`; LDK `gossip.rs:2517-2523` and `:2544-2560` | `wellFormed` is defined (`Gossip.lean:179-181`) and has projection lemmas (`:183-190`), but no transition calls it. A timestamp-0 or `cltvDelta = 0` update can be admitted if a slot is empty | P1 |
| Strict per-slot timestamp replacement | covered faithfully (canonical) | `gossip.rs:2533-2538`; BOLT 7 `:551-560` | `UpdateSupersedes` rejects equal/lower timestamps in the same slot and `insertUpdateCanonical` replaces that slot (`Gossip.lean:1355-1366`). The raw store instead uses one global clock, which over-rejects (`canonical_admission_strictly_weaker_than_raw_clock`, `GossipRawRefinementTargets.lean:1008-1028`) | P2 |
| Update timestamp freshness window (2 weeks / 1 day) | missing | `gossip.rs:2483-2511`; BOLT 7 `:577-579` | No `now` parameter, no stale/future predicate. The model accepts arbitrarily old/future timestamps as long as they beat the slot clock | P1 |
| `htlc_maximum_msat <= MAX_VALUE_MSAT` | missing | `gossip.rs:2517-2523` | `Msat` is an unbounded `Nat` wrapper in the model; no admission bound. `Msat.MAX` exists (`LnLean/Basic/Core.lean:42`) but is not enforced | P1 |
| `htlc_maximum_msat <= capacity * 1000` | missing | `gossip.rs:2544-2560`; BOLT 7 `:505-507`, `:569-571` | No lookup from an update to the channel's capacity in the admission gate. Existing fixtures use `capacitySat = 1000` and `htlcMaximumMsat = Msat.MAX`, which would violate the bound | P1 |
| Two directional views per channel | **contradicted** | `gossip.rs:1012-1055`; `ldk-node/src/graph.rs:64-75`; proto `types.proto:1064-1080` | `admittedChannelView` creates one view (`GossipTargets.lean:340-349`). A direction-1 update overwrites the single node1->node2 view because `ChannelView.applyUpdate` ignores direction (`GossipProps.lean:196-204`). There is no node2->node1 edge | P0 |
| Channel usable only after a matching direction update | **contradicted** | `gossip.rs:1046-1055`; e2e `es/src/lib.rs:1207-1212` | `admittedChannelView` is immediately `enabled = true`, fee 0, `cltvDelta = 0`, timestamp 0 (`GossipTargets.lean:340-349`; `GossipProps.lean:170-178`). `findEdge` selects it (`Graph.lean:158-170`) before any update exists. LDK has `None` until the direction arrives | P0 |
| HTLC min/max in the routing graph | missing | `ChannelUpdateInfo.htlc_minimum_msat`/`htlc_maximum_msat` (`ldk-node/src/graph.rs:104-108`; rust-lightning `gossip.rs:906-925`) | `ChannelView` and `ChannelEdge` have no HTLC bounds at all; even a correctly matched update loses them. Route search cannot enforce BOLT 7 min/max | P1 |
| Per-direction disable flag | **contradicted** | `gossip.rs:2533-2538`, `:2474-2482`; `ChannelUpdateInfo.enabled` (`ldk-node/src/graph.rs:100`) | `disableFlagSet` is decoded (`GossipProps.lean:100-103`) but applied to the one direction-blind view. A direction-1 `disable` disables the forward edge and leaves no reverse edge | P0/P1 |
| `node_announcement` signature | partially covered | `gossip.rs:497-513`; `applyGossipCanonicalStore` node branch (`GossipRawRefinementTargets.lean:136-143`) | Signature-gated, but abstract verifier and no 64-byte length requirement. The core canonical store appends nodes without timestamp canonicalisation; the additive `applyGossipNodeCanonical` adds strict timestamp replacement (`NodeCanonicalTargets.lean:348-361`) | P2 |
| Node key must be known from a `channel_announcement` | missing | `gossip.rs:1910-1938`; BOLT 7 `:381-384` | `NodeSupersedes` is vacuously true for a fresh node id (`NodeCanonicalTargets.lean:137-138`), so any valid node announcement is admitted into an empty store. There is no `ChannelAnnouncedKey` gate | P1 |
| Node timestamp strictly newer per node | partially covered | `gossip.rs:1940-1949`; BOLT 7 `:381-384` | `NodeCanonicalTargets` proves strict replacement, but the core `admitGossipCanonical` still appends node announcements without a timestamp gate (`GossipCanonicalTargets.lean:182-188`). The proof layer is additive, not the supported core transition | P2 |
| Address parsing/canonicality | covered separately | BOLT 7 `:341-371`; `NodeAddressTargets.lean:482-530` | Byte-level parser and round-trip/injectivity are proved, but `NodeAnnouncement.addresses` is still `List ByteArray` and admission never calls the parser. No DNS/Tor resolution/reachability | P2 |
| Persisted graph round-trip | unmodelled/external | `ldk-node/src/io/utils.rs:102-120`; `lightning-background-processor/src/lib.rs:1273-1289` | No `NetworkGraph.encode`/`read` analogue, no byte codec, no restart theorem. `StoreEpoch` is in-memory only | P2 external |
| Epoch/replacement history | covered as a model | `GossipStoreEpochTargets.lean:128-146`, `:342`, `:877` | The epoch fold equals the canonical store fold, and the raw/canonical square holds under explicit hypotheses. This is not persistence and does not validate messages | P2 |
| Gossip queries, rate limits, private channels, peer dissemination | unmodelled/external | BOLT 7 `:634-836`; `gossip.rs:551-565` (private updates) | No query state, rate limiter, private-channel path, or peer identity. Do not claim these from `LN-RT-002`/`LN-RT-006` | P2 external |

### 3.1 The direction-keyed theorem is not direction-keyed policy

`gossip_graph_edges_directional_key_endpoint`
(`GossipKeyConsistencyTargets.lean:445-481`) proves that every stored update
of every graph edge is signed by the endpoint selected by that update's
direction. It is a real and useful key-attribution theorem. It is **not**
coverage of the graph policy gap, because it quantifies over all updates of
the channel and says nothing about which update supplied the edge's
`feeBaseMsat`, `feeProportionalMillionths`, `cltvDelta`, or `enabled` flag.

Concrete scenario:

* `u0` is direction 0 (`channel_flags = 0`), fee base 100, timestamp 10,
  signed by `nodeKey1`.
* `u1` is direction 1 (`channel_flags = 1`), fee base 900, timestamp 11,
  signed by `nodeKey2`.
* The single view is `node1 -> node2`. Applying `u0` then `u1` leaves the
  view `node1 -> node2` with fee base 900. The theorem still holds for both
  updates, because both keys match their directions. The forward edge now
  charges the reverse direction's fee.

That is why the view fix (T1/T2) is independent of the key-attribution layer
and cannot be discharged by citing `LN-RT-002` or the directional-endpoint
theorem.

## 4. Proposed targets

The statement shapes below are proposals, not compiled code. They are ordered
by safety of implementation. T1 is additive and preserves every existing
definition and theorem. T2-T6 are additive wrappers or new fields and require
a fixture/audit pass before they can be wired into the core transition. T7-T8
are external-interface targets and should not be turned into axioms.

### T1. `LnLean.Proofs.Routing.GossipProps.ChannelView.applyUpdateDirected_direction_mismatch_eq_self`

**Priority:** P0 — **Kind:** additive model extension — **Feasibility:** high —
**Fidelity risk:** low.

**Statement shape.**

```lean
namespace LnLean.Proofs.Routing.GossipProps
namespace ChannelView

/-- Direction-aware policy application.  `dir = false` is direction 0
(`node1 -> node2`); `dir = true` is direction 1 (`node2 -> node1`). -/
def applyUpdateDirected (v : ChannelView) (dir : Bool) (u : ChannelUpdate) :
    ChannelView :=
  if v.scid = u.shortChannelId ∧ dir = u.direction ∧
      v.timestamp < u.timestamp then
    { v with
      feeBaseMsat := u.feeBaseMsat
      feeProportionalMillionths := u.feeProportionalMillionths
      cltvDelta := u.cltvDelta
      timestamp := u.timestamp
      disabled := disableFlagSet u.channelFlags }
  else v

/-- A reverse-direction update cannot change a forward view. -/
theorem applyUpdateDirected_direction_mismatch_eq_self
    (v : ChannelView) (dir : Bool) (u : ChannelUpdate)
    (hdir : dir ≠ u.direction) :
    v.applyUpdateDirected dir u = v

/-- On a matching direction, the new operation is exactly the old one. -/
theorem applyUpdateDirected_eq_applyUpdate
    (v : ChannelView) (dir : Bool) (u : ChannelUpdate)
    (hdir : dir = u.direction) :
    v.applyUpdateDirected dir u = v.applyUpdate u

/-- The current direction-blind operation really does overwrite the view. -/
theorem applyUpdate_direction_blind_counterexample :
    ∃ (v : ChannelView) (u : ChannelUpdate),
      u.direction = true ∧ v.applyUpdate u ≠ v ∧
        v.applyUpdateDirected false u = v
```

**Hypotheses.** None for the no-op law. The counterexample needs a view with
`timestamp = 0`, `scid = s`, and an update with `scid = s`, `timestamp = 1`,
`channelFlags = 1`, and a fee different from the view's.

**Non-vacuity witness.** Let `v` be `admittedChannelView a` for an
announcement `a` with `node1 ≠ node2`. Let `u` be a direction-1 update with
`feeBaseMsat = ⟨900⟩`, `timestamp = 1`. Then `v.applyUpdate u` has
`feeBaseMsat = 900` and still `node1 -> node2`; `v.applyUpdateDirected false u
= v`. The witness is non-vacuous in both directions: the mismatch law is
satisfied, and the old behaviour is demonstrably different.

**Why faithful.** It is the minimal transcription of LDK's directional slot
selection (`gossip.rs:2533-2538`, `:2583-2587`) and of
`ChannelInfo.one_to_two`/`two_to_one` (`:1012-1034`). It does not change
`applyUpdate`, so every existing theorem and counterexample is preserved.

**Weakening/assumption flags.** This target deliberately does **not** change
`ChannelView.applyUpdate`; it adds a parallel operation. Wiring it into
`admitGossipCanonical` or `admitGossipDirected` is a separate coordinated
change. Do not claim T1 fixes the graph by itself: the single-view
materialisation is T2/T3.

### T2. `LnLean.Proofs.Routing.GossipTargets.twoSidedViews_edges_both_directions`

**Priority:** P0 — **Kind:** additive materialisation extension —
**Feasibility:** medium — **Fidelity risk:** low.

**Statement shape.**

```lean
namespace LnLean.Proofs.Routing.GossipTargets

/-- The reverse endpoint view.  The channel identity and capacity are shared;
the direction is encoded by the endpoint order, as in LDK. -/
def reverseView (v : ChannelView) : ChannelView :=
  { v with node1 := v.node2, node2 := v.node1 }

/-- Both directions of an admitted announcement.  Both start with no live
policy; T3 supplies the "update present" flag. -/
def twoSidedViews (a : ChannelAnnellation) : List ChannelView :=
  [admittedChannelView a, reverseView (admittedChannelView a)]

theorem twoSidedViews_edges_both_directions
    (a : ChannelAnnellation) (hne : a.node1 ≠ a.node2) :
    (admittedChannelView a).edge ∈ (viewGraph (twoSidedViews a)).edges ∧
    (reverseView (admittedChannelView a)).edge ∈
      (viewGraph (twoSidedViews a)).edges ∧
    (reverseView (admittedChannelView a)).edge.node1 = a.node2 ∧
    (reverseView (admittedChannelView a)).edge.node2 = a.node1

theorem twoSidedViews_apply_direction
    (a : ChannelAnnellation) (u : ChannelUpdate)
    (hscid : u.shortChannelId = a.shortChannelId) :
    (* direction 0 changes only the forward view; direction 1 only the reverse *)
    ...
```

**Hypotheses.** `a.node1 ≠ a.node2` for distinct endpoints; a valid
`short_channel_id` if the graph well-formedness theorem is composed. The
`apply` law additionally needs the matching-direction hypothesis from T1.

**Non-vacuity witness.** A sample announcement with two distinct graph nodes
and `capacitySat = 1000` yields a two-element view list and two edges with
opposite endpoints. Applying a direction-0 update changes only the first;
applying a direction-1 update changes only the second.

**Why faithful.** LDK's `ChannelInfo` is exactly two optional directed
records (`gossip.rs:1012-1034`), and the public API exposes them separately
(`ldk-node/src/graph.rs:64-75`; proto `types.proto:1064-1080`). The
`Graph.ReverseClosed` predicate (`LnLean/Proofs/Routing/GraphProps.lean:89-101`)
is currently an assumption used by routing laws; `twoSidedViews` is the
materialisation that can eventually derive it.

**Weakening/assumption flags.** `reverseView` swaps graph `NodeId`s, not wire
`PubKey`s. That is correct for the graph layer only if `NodeId` naming is
consistent with the announcement's wire keys; the existing
`NodeKeyConsistent` map (`Gossip.lean:1172-1184`) is the bridge. Do not
reuse the same `ChannelView` in both directions without a direction field:
the endpoint swap alone does not protect `applyUpdate` from a reverse update,
which is why T1 is still needed.

### T3. `LnLean.Proofs.Routing.GossipProps.admittedChannelView_not_live_before_update`

**Priority:** P0/P1 — **Kind:** model extension (new field) —
**Feasibility:** medium — **Fidelity risk:** low.

**Statement shape.**

```lean
structure ChannelView where
  ...
  /-- `none` until a matching `channel_update` is admitted. -/
  lastUpdate : Option Timestamp := none

def edge (v : ChannelView) : ChannelEdge :=
  { shortChannelId := v.scid
    node1 := v.node1
    node2 := v.node2
    capacitySat := v.capacitySat
    feeBaseMsat := v.feeBaseMsat
    feeProportionalMillionths := v.feeProportionalMillionths
    cltvDelta := v.cltvDelta
    enabled := v.lastUpdate.isSome && !v.disabled }

theorem admittedChannelView_not_live (a : ChannelAnnellation) :
    (admittedChannelView a).lastUpdate = none ∧
      (admittedChannelView a).edge.enabled = false

theorem viewGraph_announcement_not_routable
    (a : ChannelAnnellation) (hne : a.node1 ≠ a.node2) :
    (viewGraph [admittedChannelView a]).findEdge a.node1 a.node2 = none

theorem applyUpdate_makes_live
    (v : ChannelView) (u : ChannelUpdate)
    (hscid : v.scid = u.shortChannelId)
    (hnew : v.timestamp < u.timestamp)
    (hdir : v.direction = u.direction) :
    (v.applyUpdate u).lastUpdate = some u.timestamp ∧
      (v.applyUpdate u).edge.enabled = !disableFlagSet u.channelFlags
```

**Hypotheses.** The live law needs a direction field or a per-direction
wrapper (T1); without it, `lastUpdate` is still direction-blind.

**Non-vacuity witness.** `admittedChannelView a` has `lastUpdate = none` and
`findEdge a.node1 a.node2 = none`, while a direction-0 update with timestamp
1 makes `findEdge` return `some` and fee base equal to the update's fee.
LDK's `as_directed_to` returns `None` when either direction is missing
(`gossip.rs:1046-1055`), and the e2e helper requires both directions to be
enabled (`e2e-tests/src/lib.rs:1207-1212`).

**Why faithful.** It models LDK's optional `ChannelUpdateInfo` pair and
removes the current zero-fee, zero-CLTV enabled edge that exists before any
policy is learned.

**Weakening/assumption flags.** Adding `lastUpdate` to `ChannelView` changes
the `edge` result and may invalidate routing/security theorems that assume an
announced edge is immediately selectable. This is a coordinated migration:
update every construction site, restate the route-feasibility hypotheses, and
keep an explicit witness that the pre-update edge is present in the edge list
but not selectable. Do not replace `timestamp : Timestamp` with
`lastUpdate : Option Timestamp` in one step; keep both during migration.

### T4. `LnLean.Proofs.Routing.GossipCanonicalTargets.validated_update_rejects_dont_forward`

**Priority:** P1 — **Kind:** additive validated transition —
**Feasibility:** medium — **Fidelity risk:** low-medium.

**Statement shape.**

```lean
namespace LnLean.Proofs.Routing.GossipCanonicalTargets

def ChannelUpdate.policySane (u : ChannelUpdate) : Prop :=
  u.wellFormed ∧
    u.messageFlags / 2 % 2 = 0 ∧
    u.htlcMaximumMsat.val ≤ Msat.MAX.val

/-- Freshness is a time-relative policy, not a protocol invariant. -/
def ChannelUpdate.policySaneAt (now : Timestamp) (u : ChannelUpdate) : Prop :=
  u.policySane ∧
    now - 14 * 24 * 60 * 60 ≤ u.timestamp ∧
    u.timestamp ≤ now + 24 * 60 * 60

noncomputable def applyUpdatePolicyChecked (verify : SigVerifier)
    (cs : CanonicalStore) (u : ChannelUpdate) : CanonicalStore :=
  if u.signatureValid verify ∧ cs.gossip.updateKeyAnnouncedDirectional u ∧
      UpdateSupersedes u cs.gossip.updates ∧ u.policySane then
    (* insertUpdateCanonical ... *)
    ...
  else cs

theorem validated_update_rejects_dont_forward
    (verify : SigVerifier) (cs : CanonicalStore) (u : ChannelUpdate)
    (hdont : u.messageFlags / 2 % 2 = 1) :
    applyUpdatePolicyChecked verify cs u = cs

theorem validated_update_rejects_malformed
    (verify : SigVerifier) (cs : CanonicalStore) (u : ChannelUpdate)
    (hbad : ¬ u.wellFormed) :
    applyUpdatePolicyChecked verify cs u = cs

theorem validated_update_rejects_oversized_htlc_max
    (verify : SigVerifier) (cs : CanonicalStore) (u : ChannelUpdate)
    (hbig : Msat.MAX.val < u.htlcMaximumMsat.val) :
    applyUpdatePolicyChecked verify cs u = cs
```

Add the capacity-relative companion separately:

```lean
theorem validated_update_rejects_htlc_max_above_capacity
    (verify : SigVerifier) (cs : CanonicalStore) (u : ChannelUpdate)
    (a : ChannelAnnellation)
    (ha : a ∈ cs.gossip.announcements)
    (hscid : a.shortChannelId = u.shortChannelId)
    (hcap : 0 < a.capacitySat)
    (hbig : a.capacitySat * 1000 < u.htlcMaximumMsat.val) :
    applyUpdatePolicyChecked verify cs u = cs
```

**Hypotheses.** The rejection laws need the gate condition and the stored
announcement for the capacity-relative version. `policySaneAt` needs a `now`
parameter; it is a client policy, not a BOLT-consensus theorem.

**Non-vacuity witness.** A positive update with `messageFlags = 0`,
`timestamp = 1`, `cltvDelta = 1`, `htlcMinimumMsat = 0`,
`htlcMaximumMsat = 1000`, valid signature, and direction-correct key is
accepted. A negative update with `messageFlags = 2` is rejected. The existing
`u0`/`u1` fixtures (`GossipCanonicalTargets.lean:648-666`) satisfy
`wellFormed`, `messageFlags = 0`, and `htlcMaximumMsat = Msat.MAX`, so they
survive the `policySane` gate; they do **not** satisfy the capacity-relative
gate, because their `capacitySat = 1000` and `Msat.MAX` is far above
`1000 * 1000`.

**Why faithful.** It transcribes the LDK P2P rejection
(`gossip.rs:551-565`), the `wellFormed` conditions (`Gossip.lean:179-181`;
BOLT 7 `:517-524`), the `MAX_VALUE_MSAT` check (`gossip.rs:2517-2523`), and
the freshness window (`gossip.rs:2483-2511`). It deliberately does **not**
require `message_flags` bit 0 (`must_be_one`), because LDK's receiver does
not reject bit 0 = 0; requiring it would break all existing fixtures that use
`messageFlags = 0`.

**Weakening/assumption flags.** `policySane` is stronger than the current
admission and will reject messages the model previously accepted. Keep the
old `applyGossipCanonicalStore` and add the checked wrapper; do not silently
change the core transition. The capacity-relative gate needs a fixture
migration (set `htlcMaximumMsat` relative to `capacitySat` or raise the
capacity). Freshness needs a clock model; do not add an unconstrained `now`
that makes the theorem vacuous.

### T5. `LnLean.Proofs.Routing.GossipCanonicalTargets.announcement_rejects_unsorted_node_keys`

**Priority:** P1 — **Kind:** additive structural gate —
**Feasibility:** medium — **Fidelity risk:** low-medium.

**Statement shape.**

```lean
namespace LnLean.Proofs.Routing.GossipCanonicalTargets

/-- Lexicographic order on 33-byte compressed keys, matching BOLT 7's
"sorted in ascending lexicographic order". -/
def bytesLt : List UInt8 → List UInt8 → Prop
  | [], [] => False
  | [], _ :: _ => True
  | _ :: _, [] => False
  | x :: xs, y :: ys => x < y ∨ (x = y ∧ bytesLt xs ys)

def PubKey.lexLt (a b : PubKey) : Prop :=
  bytesLt a.bytes.toList b.bytes.toList

def ChannelAnnellation.structurallyAdmissible (a : ChannelAnnellation) : Prop :=
  a.nodeKey1.lexLt a.nodeKey2 ∧
    a.bitcoinKey1 ≠ a.bitcoinKey2 ∧
    0 < a.capacitySat

theorem announcement_rejects_unsorted_node_keys
    (verify : SigVerifier) (cs : CanonicalStore) (a : ChannelAnnellation)
    (hgate : a.signaturesValid verify ∧ a.node1 ≠ a.node2 ∧
      cs.gossip.CompatibleWithStore a ∧ UpdatesAuthorizedBy cs.gossip a)
    (hunsorted : ¬ a.nodeKey1.lexLt a.nodeKey2) :
    admitAnnouncementChecked verify cs a = cs

theorem announcement_rejects_equal_bitcoin_keys ... 
theorem announcement_rejects_zero_capacity ...
```

**Hypotheses.** The negative laws assume every other gate passes, so the
rejection is attributable to the new structural predicate. The positive
witness needs `nodeKey1.lexLt nodeKey2`, `bitcoinKey1 ≠ bitcoinKey2`, and
`0 < capacitySat`.

**Non-vacuity witness.** Use two 33-byte keys with known lexicographic order
(e.g. first byte `0x02` then `0x03`) and distinct Bitcoin keys; the
announcement is accepted. Flip the node keys and it is rejected. Set
`bitcoinKey1 = bitcoinKey2` and it is rejected. Set `capacitySat = 0` and it
is rejected; `bindChannel_capacity_positive_counterexample`
(`GossipProps.lean:1015-1023`) already exhibits the current zero-capacity
admission.

**Why faithful.** It transcribes LDK's sortedness check
(`gossip.rs:2125-2131`), equal-Bitcoin-key check (`:2133-2138`), and
positive/UTXO-derived capacity (`:2201-2231`), plus BOLT 7
`:189-203`. It also closes the gap between graph `node1 ≠ node2` and wire
`nodeKey1 ≠ nodeKey2`; the current gate only checks the former.

**Weakening/assumption flags.** `NodeId` is an opaque graph index
(`Graph.lean:77-82`), so sortedness must be stated on `PubKey`, not on
`NodeId`. Adding `capacitySat > 0` may break existing fixtures with
`capacitySat = 0`; audit them. The chain/UTXO part of capacity equality is
not provable here and remains T7.

### T6. `LnLean.Proofs.Routing.NodeCanonicalTargets.node_admission_requires_channel_announced_key`

**Priority:** P1 — **Kind:** additive validated transition —
**Feasibility:** high — **Fidelity risk:** low-medium.

**Statement shape.**

```lean
namespace LnLean.Proofs.Routing.NodeCanonicalTargets

/-- The node key appears in a stored channel announcement. -/
def ChannelAnnouncedKey (s : GossipState) (k : PubKey) : Prop :=
  ∃ a ∈ s.announcements, a.nodeKey1 = k ∨ a.nodeKey2 = k

noncomputable def applyGossipNodeCanonicalChecked (verify : SigVerifier)
    (cs : CanonicalStore) : GossipMessage → CanonicalStore
  | .channelAnnouncement a => applyGossipCanonicalStore verify cs (.channelAnnouncement a)
  | .channelUpdate u => applyGossipCanonicalStore verify cs (.channelUpdate u)
  | .nodeAnnouncement n =>
      if n.signatureValid verify ∧
          NodeSupersedes n cs.gossip.nodeAnnouncements ∧
          ChannelAnnouncedKey cs.gossip n.nodeId then
        { gossip := { cs.gossip with
            nodeAnnouncements := insertNodeCanonical n cs.gossip.nodeAnnouncements }
          nodeKeyOf := cs.nodeKeyOf }
      else cs

theorem node_admission_requires_channel_announced_key
    (verify : SigVerifier) (cs : CanonicalStore) (n : NodeAnnouncement)
    (h : applyGossipNodeCanonicalChecked verify cs (.nodeAnnouncement n) ≠ cs) :
    ChannelAnnouncedKey cs.gossip n.nodeId

theorem node_admission_rejects_unknown_node
    (verify : SigVerifier) (n : NodeAnnouncement)
    (hvalid : n.signatureValid verify)
    (hunknown : ¬ ChannelAnnouncedKey ⟨[], [], []⟩ n.nodeId) :
    applyGossipNodeCanonicalChecked verify
      { gossip := ⟨[], [], []⟩, nodeKeyOf := fun _ => n.nodeId } (.nodeAnnouncement n) =
        { gossip := ⟨[], [], []⟩, nodeKeyOf := fun _ => n.nodeId }
```

**Hypotheses.** The rejection witness uses the empty store; the acceptance
witness uses a stored announcement whose `nodeKey1` or `nodeKey2` equals
`n.nodeId`, plus `NodeSupersedes`.

**Non-vacuity witness.** With `n.nodeId = key1` and a valid signature, the
empty store rejects `n`; after admitting an announcement containing `key1`,
the same `n` is admitted. This is non-vacuous in both directions. The
existing `missing_endpoint_channel_admitted` counterexample
(`NodeIdentityTargets.lean:940-963`) shows the *converse* gap: a channel can
be admitted without node announcements for its endpoints. The two gaps are
distinct and both should be preserved.

**Why faithful.** BOLT 7 says a node announcement is ignored if the node id
is not previously known from a `channel_announcement`
(`refs/bolts/07-routing-gossip.md:381-384`), and LDK returns
“No existing channels for node_announcement” when the node entry is absent
(`gossip.rs:1925-1938`). LDK may hold the message in `pending_checks` for a
later channel announcement, so “reject now” is a client policy choice; the
model can state the no-op branch and document the queueing alternative.

**Weakening/assumption flags.** This rejects node announcements that the
current `applyGossipNodeCanonical` accepts with a fresh node id. Audit the
existing node witnesses (`nA1`, `nB1`, rotation cases) because some may
admit a node before its channel. Keep the un-checked transition for
compatibility and add the checked one; do not silently change the core.
`ChannelAnnouncedKey` is a wire-key predicate; do not confuse it with
`NodeAnnounced`, which means a node *announcement* already exists
(`NodeIdentityTargets.lean:88-99`).

### T7. `LnLean.Proofs.Routing.ChainAdmission.announcement_requires_chain_evidence`

**Priority:** P2 — **Kind:** external interface / model extension —
**Feasibility:** low in wave 13 — **Fidelity risk:** high.

**Statement shape.**

```lean
namespace LnLean.Proofs.Routing.ChainAdmission

/-- The chain facts that LDK obtains from its `UtxoLookup`. -/
structure ChainEvidence where
  chainHash : ByteArray
  confirmations : ShortChannelId → Nat
  fundingScriptOk : ShortChannelId → PubKey → PubKey → Prop
  capacitySat : ShortChannelId → Option Nat

def ChannelAnnellation.chainAdmissible
    (chain : ChainEvidence) (a : ChannelAnnellation) : Prop :=
  chain.chainHash = a.chainHash ∧
    6 ≤ chain.confirmations a.shortChannelId ∧
    chain.fundingScriptOk a.shortChannelId a.bitcoinKey1 a.bitcoinKey2 ∧
    chain.capacitySat a.shortChannelId = some a.capacitySat

theorem admitted_announcement_requires_chain_evidence
    (chain : ChainEvidence) (cs : CanonicalStore) (a : ChannelAnnellation)
    (h : admitAnnouncementWithChain chain cs a ≠ cs) :
    a.chainAdmissible chain
```

This requires adding `chainHash : ByteArray` to `ChannelAnnellation` and
`ChannelUpdate`; neither has one today (`Gossip.lean:108-122`, `:155-168`).

**Hypotheses.** `chain` is an explicit model parameter, not an axiom.
`chainHash`, `confirmations`, `fundingScriptOk`, and `capacitySat` are the
fields LDK obtains from its chain source/`UtxoLookup`.

**Non-vacuity witness.** An abstract `ChainEvidence` with the matching chain
hash, six confirmations, a successful funding-script predicate, and the
announcement's capacity admits the announcement; flipping any field rejects
it. This is an interface witness, not a proof about Bitcoin.

**Why faithful.** It exposes exactly the facts LDK uses: chain-hash match
(`gossip.rs:2140-2145`), UTXO/P2WSH/capacity (`:2201-2231`), and the six
confirmation policy (BOLT 7 `:207-233`). It also covers the update chain-hash
check (`gossip.rs:2474-2481`) if the same `ChainEvidence.chainHash` is used.

**Weakening/assumption flags.** This is an external/human barrier, not a
safe wave-13 theorem. Do not introduce `ChainEvidence` as an axiom or claim
that a UTXO exists without a chain model. `capacitySat : Option Nat` is
required for LDK fidelity because LDK uses `None` when no lookup is
available (`gossip.rs:1028`, `:2220`); the current `Nat` field cannot
represent “unknown”.

### T8. `LnLean.Proofs.Routing.GossipPersistence.decode_encode_preserves_two_sided_graph`

**Priority:** P2 — **Kind:** external assumption/codec specification —
**Feasibility:** low in wave 13 — **Fidelity risk:** high.

**Statement shape.**

```lean
namespace LnLean.Proofs.Routing.GossipPersistence

structure GraphSnapshot where
  announcements : List ChannelAnnellation
  channels : List (ShortChannelId × ChannelView × ChannelView)
  nodes : List NodeAnnouncement

def encode : GraphSnapshot → ByteArray
def decode : ByteArray → Option GraphSnapshot

theorem decode_encode (g : GraphSnapshot) :
    decode (encode g) = some g

theorem decode_encode_preserves_two_sided_graph (g : GraphSnapshot) :
    ∃ g', decode (encode g) = some g' ∧
      g'.channels.map (fun c => c.1) = g.channels.map (fun c => c.1)
```

**Hypotheses.** None in the abstract law; the real obligation is that
`encode`/`decode` match LDK's `NetworkGraph` TLV encoding, including both
directions, optional updates, and node records.

**Non-vacuity witness.** A snapshot with one announcement, two directional
views (one disabled), and one node announcement must round-trip with both
directions and the disabled bit intact.

**Why faithful.** LDK Node reads `NetworkGraph::read` from the persisted
namespace (`/tmp/opencode/ldk-refs/ldk-node/src/io/utils.rs:102-120`) and the
background processor writes `network_graph.encode()`
(`refs/rust-lightning/lightning-background-processor/src/lib.rs:1273-1289`).
The persisted object is the two-directional `ChannelInfo` graph, not a
flattened edge list.

**Weakening/assumption flags.** This is a specification of an external
codec, not a theorem that Lean can prove from the current model. Do not add
`decode_encode` as an axiom and cite it as coverage. Either implement a real
codec module with a concrete encoding or record the round-trip as an explicit
external assumption in `docs/ASSUMPTIONS.md`. `StoreEpoch` is not a
persistence layer; its fold laws (`GossipStoreEpochTargets.lean:342`, `:877`)
say nothing about bytes or restart.

## 5. Assumptions, counterexamples, and non-vacuity risks

### Counterexamples that must be preserved

* `accepted_update_signing_key_announced_counterexample`
  (`GossipProps.lean:961-966`): the raw verifier can accept an update whose
  signing key was never announced. The canonical path now has
  `updateKeyAnnouncedDirectional`; do not delete the raw witness.
* `bindChannel_capacity_positive_counterexample`
  (`GossipProps.lean:1015-1023`): zero-capacity announcements bind. T5 adds
  the positive-capacity gate; keep the old witness for the un-checked path.
* `accepted_update_signature_length_counterexample`
  (`GossipProps.lean:1047-1051`): the abstract verifier accepts an empty
  signature. T4 does not fix this; a length-checking verifier or a
  `GossipSignature.Valid` hypothesis is still required.
* `raw_applyGossip_admits_invalid_announcement`
  (`GossipTargets.lean:187-...`): the raw store is unfiltered.
* `canonical_admission_strictly_weaker_than_raw_clock`
  (`GossipRawRefinementTargets.lean:1008-1028`): canonical per-slot
  admission accepts an update the raw global clock rejects. Do not identify
  the two transitions.
* `no_canonical_preserving_raw_announcement_extension`
  (`GossipRawRefinementTargets.lean:1050-1072`): raw append cannot preserve
  `CanonicalAnnouncements`.
* `raw_conflicting_announcement_counterexample_preserved`
  (`GossipRawRefinementTargets.lean:1099-1103`).
* `missing_endpoint_channel_admitted`
  (`NodeIdentityTargets.lean:940-963`): a channel can be admitted without
  node announcements for both endpoints. This is the converse of T6 and must
  remain visible.
* `reachableCanonical_supersession_witness`
  (`GossipCanonicalTargets.lean:874-889`) and
  `reachableNodeCanonical_node_replacement`
  (`NodeCanonicalTargets.lean:1041-...`): the replacement laws are
  non-vacuous.

### New counterexamples this report relies on

* **Direction-blind view overwrite.** `v = admittedChannelView a`, `u` has
  `direction = true`, `scid = a.shortChannelId`, `timestamp = 1`, fee base
  900. `v.applyUpdate u` changes the `node1 -> node2` view to fee 900.
  LDK stores the update in `two_to_one` and leaves `one_to_two` absent
  (`gossip.rs:1012-1034`, `:2583-2587`).
* **Pre-update zero-fee routability.** `admittedChannelView a` has
  `enabled = true`, fee 0, `cltvDelta = 0`, timestamp 0; `findEdge` selects
  it (`GossipProps.lean:170-178`, `Graph.lean:158-170`). LDK's
  `as_directed_to` returns `None` until both `ChannelUpdateInfo`s exist
  (`gossip.rs:1046-1055`).
* **`dont_forward` accepted.** A valid update with
  `messageFlags = 1 | (1 << 1)` passes the canonical gate because no branch
  inspects bit 1. LDK rejects it (`gossip.rs:551-565`).
* **Malformed update accepted.** A valid update with `timestamp = 0`,
  `cltvDelta = 0`, or `htlcMinimumMsat > htlcMaximumMsat` passes the
  canonical gate; `wellFormed` is never called. The existing `u0`/`u1`
  fixtures satisfy `wellFormed`, but the gate does not require it.
* **Unsorted/equal announcement keys accepted.** `nodeKey1 = nodeKey2` passes
  the canonical gate as long as graph `node1 ≠ node2`; `bitcoinKey1 =
  bitcoinKey2` and `capacitySat = 0` also pass.
* **Node announcement without a channel accepted.** With an empty store and
  a valid signature, `applyGossipNodeCanonical` admits any fresh
  `nodeId`; `NodeSupersedes` is vacuously true
  (`NodeCanonicalTargets.lean:137-138`, `:348-361`).

### Hidden assumptions and scope boundaries

* **`SigVerifier` is arbitrary.** `signatureValid verify key digest sig` is
  just `verify ... = true` (`Gossip.lean:93-98`). Unforgeability is C3/C4/C8
  (`docs/ASSUMPTIONS.md:17-22`); the 64-byte `GossipSignature.Valid` is not
  required by the verifier (`GossipProps.lean:1047-1051`). Any claim about
  “valid signature” must say which hypothesis it uses.
* **`Nat` is not `u64`.** `Timestamp`, `Msat`, `capacitySat`, and flags are
  unbounded `Nat`s. LDK uses `u32`/`u64` and `checked_*`/saturating
  arithmetic in places. The `MAX_VALUE_MSAT` and capacity bounds are the
  visible top-of-range obligations (T4).
* **Capacity is not the funding output.** `capacitySat : Nat` is a message
  field, not a chain-derived value; LDK uses `Option<u64>` and derives it
  from `utxo_value` (`gossip.rs:2201-2231`). The model cannot express
  “unknown capacity” until T7.
* **Graph `NodeId` is opaque.** `NodeId` is an index, not a BOLT 7 public
  key (`Graph.lean:77-82`). Sortedness and key distinctness must be stated on
  `PubKey`; `NodeKeyConsistent` (`Gossip.lean:1172-1184`) is the bridge
  between graph indices and wire keys.
* **Raw store vs canonical store.** `applyGossip` is append-only and uses a
  global clock (`Gossip.lean:287-290`, `:328-331`). The canonical transition
  is the supported path. Do not cite raw-store theorems as validation
  coverage, and do not identify the two clocks (`canonical_admission_strictly_weaker_than_raw_clock`).
* **Node canonicalisation is additive.** `canonicalStoreView` leaves node
  announcements untouched (`Gossip.lean:1875-1877`), and the core
  `applyGossipCanonicalStore` appends them (`GossipRawRefinementTargets.lean:136-143`).
  The wave-9/10/11 `NodeCanonicalTargets`/`NodeIdentityTargets` layers are
  additive and are not the transition used by the canonical store square.
* **Epoch is not persistence.** `StoreEpoch` records in-memory replacement
  events and version maps (`GossipStoreEpochTargets.lean:128-146`); it has no
  byte codec, no restart relation, and no durability. The epoch/canonical
  square is a model-shape theorem.
* **`Graph.ReverseClosed` is an assumption.** It is a predicate
  (`GraphProps.lean:89-101`), not a consequence of `admittedChannelView`.
  Routing laws that assume it do not derive it from two directional
  announcements.
* **`Graph.WellFormed` positive capacity is an assumption.** It is a
  predicate (`GraphProps.lean:99-101`), not derived from the announcement
  gate; T5 would derive the `0 < capacitySat` half for the checked path.
* **Private channels are not modelled.** LDK accepts own-channel updates even
  when non-public (`gossip.rs:551-565`; BOLT 7 `:534-540`); Lean's
  announcement-key gate rejects updates without a `channel_announcement`.
  This is a deliberate public-graph restriction, not full LDK coverage.
* **Gossip queries/rate limits/dissemination are out of scope.** BOLT 7
  `:634-836`; no Lean model. Do not add them as “covered by LN-RT-002”.

### Weakening/assumption flags for the proposals

* **T1** is additive but parallel. Wiring it into the canonical transition
  changes which updates affect views; audit every theorem that uses
  `ChannelView.applyUpdate` (`GossipProps.lean:196-291`,
  `GossipTargets.lean:470-500`, `GossipKeyConsistencyTargets.lean:85-110`).
* **T2** adds a reverse view. `insertViewCanonical` replaces by `scid`
  (`GossipCanonicalTargets.lean:112-114`), so inserting two views requires a
  new replacement operation that removes both old directions. Do not reuse
  the one-view insertion.
* **T3** changes `edge.enabled`. Any route theorem that assumes an announced
  edge is selectable will need a “live update” hypothesis. This is a
  correctness improvement, not a weakening, but it is a migration.
* **T4** rejects more messages. Keep the old transition and add a checked
  wrapper; do not silently tighten the core gate. The capacity-relative
  companion requires fixture changes because `Msat.MAX` exceeds
  `capacitySat * 1000` in the existing tests.
* **T5** rejects more announcements. Existing zero-capacity/unsorted
  witnesses must be moved to the un-checked path or updated. `NodeId`
  distinctness is not a substitute for wire-key sortedness.
* **T6** rejects fresh node announcements. Existing node-canonical witnesses
  may admit a node before a channel; audit them. Keep
  `missing_endpoint_channel_admitted` as the converse witness.
* **T7/T8** must remain explicit external assumptions or interfaces. Do not
  add axioms, and do not claim a chain/codec proof from the current model.

## 6. Wave-13 recommendation

**Verdict: there is a safe additive view-direction lane, but the core
validation and persistence lane is not safe for wave 13.**

* **Implement now: T1.**
  `ChannelView.applyUpdateDirected` plus
  `applyUpdateDirected_direction_mismatch_eq_self`,
  `applyUpdateDirected_eq_applyUpdate`, and the direction-blind
  counterexample. It touches no existing definition, preserves every
  existing theorem and counterexample, and closes the most concrete
  direction bug in the graph seam. It is the only target in this report that
  can land without a coordinated migration.
* **Implement as an additive materialisation, if the lane has room: T2.**
  `twoSidedViews` plus the two-edge theorem and the direction-specific
  update law. Keep it parallel to `admittedChannelView`; do not change
  `insertViewCanonical` yet. This makes the missing reverse edge explicit and
  gives T3 a place to attach the “update present” flag.
* **Defer to wave 14 with a coordinated migration: T3, T4, T5, T6.**
  T3 changes `ChannelView`/`ChannelEdge` and the meaning of `enabled`; T4 and
  T5 tighten admission and invalidate some fixtures; T6 tightens node
  admission and may invalidate node witnesses. They should be one reviewed
  migration PR with:
  * a new `ChannelView.lastUpdate : Option Timestamp` (or a two-sided
    `ChannelRecord`) and an `edge.enabled` law;
  * a checked update transition that enforces `wellFormed`,
    `dont_forward`, `MAX_VALUE_MSAT`, and optionally the freshness window and
    capacity bound;
  * a checked announcement transition that enforces sorted wire keys,
    distinct Bitcoin keys, and positive capacity;
  * a checked node transition that requires a channel-announced key;
  * explicit witnesses that the old un-checked path still accepts the old
    counterexamples.
* **Treat as external/human barrier: T7 and T8.**
  Chain hash, UTXO/P2WSH, six confirmations, and `Option<u64>` capacity need
  a chain model or an explicit `ChainEvidence` interface. Persistence needs a
  real `NetworkGraph`-compatible codec and a restart relation. Neither is a
  safe Lean-only wave-13 target; both should be recorded in
  `docs/ASSUMPTIONS.md` if they are assumed.
* **Do not claim** that `LN-RT-002` or `LN-RT-006` covers direction,
  pre-update routability, `dont_forward`, sortedness, capacity, node
  existence, or persistence. `LN-RT-002` is a timestamp/replacement/store
  shape claim; `LN-RT-006` is an announcement-backing claim. The directional
  key-attribution theorem is real but does not select the graph policy.

There is no P0 consensus-safety lane here. The P0/P1 items are routing and
economic fidelity: a reverse update can change the forward fee/disable flag,
and an announcement can create a routable zero-fee edge before any policy is
learned. Those are correctness bugs in the model, not fund-loss proofs.

## 7. Evidence and commands

Read-only inputs used:

* Lane brief: `agents/briefs/wave13-review/R13.md`.
* Protocol/context: `docs/AGENT-PROTOCOL.md`, `docs/OPEN-ISSUES.md`
  (`RT-01`, `RT-02`), `docs/THEOREM-INDEX.md` (`LN-RT-002`, `LN-RT-006`),
  `docs/TRACEABILITY.md`, `docs/ASSUMPTIONS.md`,
  `agents/TODO-REPAIR.md`, `agents/reports/swarm12/S12-POST-INTEGRATION-AUDIT.md`,
  `agents/reports/wave13-review/LDK-REFS.md`.
* Lean surface: `LnLean/Routing/Gossip.lean`,
  `LnLean/Routing/Graph.lean`,
  `LnLean/Proofs/Routing/GossipProps.lean`,
  `LnLean/Proofs/Routing/GossipTargets.lean`,
  `LnLean/Proofs/Routing/GossipCanonicalTargets.lean`,
  `LnLean/Proofs/Routing/GossipRawRefinementTargets.lean`,
  `LnLean/Proofs/Routing/GossipStoreEpochTargets.lean`,
  `LnLean/Proofs/Routing/GossipKeyConsistencyTargets.lean`,
  `LnLean/Proofs/Routing/GossipAttributionTargets.lean`,
  `LnLean/Proofs/Routing/NodeCanonicalTargets.lean`,
  `LnLean/Proofs/Routing/NodeIdentityTargets.lean`,
  `LnLean/Proofs/Routing/NodeIdentityChainTargets.lean`,
  `LnLean/Proofs/Routing/NodeAddressTargets.lean`,
  `LnLean/Proofs/Routing/GraphProps.lean`,
  `LnLean/Basic/Core.lean`.
* LDK Node: `src/graph.rs`, `src/gossip.rs`, `src/io/utils.rs`,
  `src/builder.rs`.
* LDK Server: `ldk-server/src/api/graph_get_channel.rs`,
  `ldk-server/src/api/graph_list_channels.rs`,
  `ldk-server/src/api/graph_get_node.rs`,
  `ldk-server/src/api/graph_list_nodes.rs`,
  `ldk-server/src/util/proto_adapter.rs`,
  `ldk-server-grpc/src/proto/types.proto`,
  `e2e-tests/src/lib.rs`.
* rust-lightning: `lightning/src/routing/gossip.rs`,
  `lightning-background-processor/src/lib.rs`.
* BOLT 7: `refs/bolts/07-routing-gossip.md`.

Commands used (read-only):

```text
rg -n "..." LnLean docs agents
grep -n "..." <Lean file> <LDK file>
sed -n '...' <Lean file>
sed -n '...' <LDK file>
wc -l <Lean files>
git -C /home/ubuntu/ln-lean-repair status --short
git -C /home/ubuntu/ln-lean-repair rev-parse --short HEAD
git -C /tmp/opencode/ldk-refs/ldk-node rev-parse --short HEAD
git -C /tmp/opencode/ldk-refs/ldk-server rev-parse --short HEAD
git -C /home/ubuntu/ln-lean-repair/refs/rust-lightning rev-parse --short HEAD
```

No Lean build, no `lake` elaboration, no cargo test, and no code/doc edits
were performed. Only this report was written. The working tree already
contained untracked `agents/briefs/wave13-review/`,
`agents/reports/wave13-review/`, and wave-13 status/swarm files; nothing else
was modified.
