# R14 — BOLT 7 node announcements, addresses, chain hash, rotation

**Status:** read-only review
**Pins:** LDK Node `fa123fed131e27ecc420b77fa7086fcf1ddaebb8`, LDK Server `c17dc11dde38f88c53457039ddf30c6b90a63ba2`

## 1. Scope and current Lean surface

This lane covers the BOLT 7 `node_announcement` as a **received, validated,
stored and replaced** object: the `node_id` admission rule, timestamp ordering,
`features`/`flen`, `rgb_color`, `alias`, the `addrlen`-framed address field, the
indirect chain-hash binding, and the Lean rotation/certificate extension. It
does not re-review wire signature bytes (the digest is opaque), gossip queries,
peer dissemination, pathfinding, or the `channel_update` timestamp law except
where a node-announcement theorem is catalogued under the same row.

### 1.1 Catalog row

`LN-RT-002` is titled “BOLT 7 §The channel_update Message”, but its `leanTarget`
list has been extended over waves 9–12 with every node-announcement,
rotation, identity and address target. The row now mixes three claim families:

* the channel-update timestamp law (`Gossip.update_monotone`,
  `replacedUpdates_timestamp_lt`, the store-epoch square);
* the node-canonical replacement layer (`NodeCanonicalTargets`);
* the identity/rotation/address layers (`NodeIdentityTargets`,
  `NodeIdentityChainTargets`, `NodeAddressTargets`).

The catalog’s own scope sentence
(`docs/THEOREM-INDEX.md:69`) is accurate: identity across rotation,
chain-existence policy, and a production gossip/rotation pipeline remain open.
What the row does **not** say, and this report adds, is that LDK’s
known-node admission rule and address-field forward-compatibility are also
outside the mechanized surface.

### 1.2 Core node-announcement record

`LnLean/Routing/Gossip.lean:200-208` defines:

```lean
structure NodeAnnouncement where
  nodeId : PubKey
  timestamp : Timestamp
  rgbColor : ByteArray
  alias : ByteArray
  addresses : List ByteArray
  digest : ByteArray
  signature : GossipSignature
```

There is **no** `features` field, no `flen`, no `addrlen`, no alias width or
UTF-8 constraint, and `addresses` is an unparsed list of blobs. The module’s
scope note (`Gossip.lean:54-61`) explicitly disclaims chain-hash filtering,
UTXO verification of the funding outpoint, address parsing, and gossip rate
limits. Note the anchor drift: the note cites rust-lightning
`fe4900930c6bd5786ec4203274d7cf312776a5a6`, while LDK Node `fa123fe`
depends on `d7a980641c6325ddda5072a0f470ef8392676cf5`
(`/tmp/opencode/ldk-refs/ldk-node/Cargo.toml:89`). All LDK citations below use
`d7a98064` via `git show` from `refs/rust-lightning`; its line numbers differ
from the older `fe49009` anchors in the Lean comments.

### 1.3 Current claim surface

| Layer | Declarations | What is actually claimed | What is not claimed |
|---|---|---|---|
| Core record | `NodeAnnouncement` (`Gossip.lean:200-208`), `signatureValid` (`:212-213`) | Opaque signed record; signature is an abstract verifier predicate | No `features`, `flen`, `addrlen`, alias shape, address shape, or real digest |
| Canonical replacement | `insertNodeCanonical` (`NodeCanonicalTargets.lean:103-107`), `NodeSupersedes` (`:137-139`), `CanonicalNodeAnnouncements` (`:131-132`), `applyGossipNodeCanonical` (`:348-361`) | Signature-gated replace-by-node, strictly newer timestamp only; fresh `nodeId` vacuously supersedes | No admission prerequisite; a node with no channel is accepted |
| Node-canonical invariant | `NodeCanonicalAdmitted` (`:534-540`), reachability and replacement theorems; equal-timestamp boundary (`:1114`) | One record per `nodeId`, valid signatures, strict-timestamp behaviour | Does not imply `WireMember`; `missing_endpoint_channel_admitted` proves the gap |
| Identity/rotation | `RotationWitness` (`NodeIdentityTargets.lean:293-301`), `WireMember` (`:377-382`), `rotation_preserves_wireMember` (`:420`), `rotation_not_signature_preserving` (`:835`) | An opaque out-of-band witness rewrites endpoint keys and preserves wire membership; it does not authenticate or preserve signatures | No LDK/BOLT 7 rotation message, no cryptographic linkage, no certificate semantics |
| Rotation chains | `RotationChain`, invented message/certificate (`NodeIdentityChainTargets.lean:103-132`), `epochByte` (`:108`), per-node sequence gate (`NodeRateState` `:629-641`) | A model-internal authenticated chain and re-signing protocol; per-node timestamp+sequence replay limit | No counterpart in BOLT 7 or LDK; sequence is not a wire field; epoch encoding is not injective |
| Address parser | `Port` (`NodeAddressTargets.lean:109-113`), `Address` (`:280-286`), `decodeAddresses` (`:681-689`), `parseAddressList` (`:642-659`) | Exact `u16 addrlen` framing, typed known descriptors, fixed widths, nonzero ports, ascending order, at most one DNS, canonical round-trip/injectivity, explicit rejection lemmas | Unknown-tag forward-compatibility, excess address data, per-descriptor zero-port ignore, LDK hostname charset, receiver leniency |

`missing_endpoint_channel_admitted` (`NodeIdentityTargets.lean:940-960`) is the
key existing negative result: the core transition admits a channel announcement
whose second endpoint has no node announcement. `ns0`/`ns1`
(`NodeCanonicalTargets.lean:851-870`) are the non-vacuity witnesses that make
the unknown-node admission gap reachable: `ns1` is built by applying
`applyGossipNodeCanonical` to a node announcement for a key with no channel.

## 2. LDK datapoints (with `file:line`)

All paths are under the local read-only clone. Citations of the form
`refs/rust-lightning@d7a98064:...` were read with
`git -C refs/rust-lightning show d7a98064:path` (the checkout HEAD is
`fe49009`, so plain file reads would give shifted lines).

### 2.1 Admission, timestamp and pending validation

* `refs/rust-lightning@d7a98064:lightning/src/routing/gossip.rs:1882-1898`
  — `NetworkGraph::update_node_from_announcement` first rejects a duplicate
  with the same timestamp, then verifies the signature, then enters the
  internal update.
* `.../gossip.rs:1911-1924` — `update_node_from_announcement_intern`: if
  `nodes.get_mut(&msg.node_id)` returns `None`, LDK calls
  `check_hold_pending_node_announcement` and returns
  `"No existing channels for node_announcement"`. This is the known-node gate:
  a node announcement is only accepted if the node was previously created from
  a `channel_announcement`.
* `.../gossip.rs:1925-1940` — for an existing node, an older **or equal**
  timestamp is ignored (`"Update older than last processed update"`,
  `"Update had the same timestamp..."`). This matches Lean `NodeSupersedes`
  (`NodeCanonicalTargets.lean:137-139`).
* `.../gossip.rs:2090-2105` — channel-announcement processing creates a
  `NodeInfo { channels, announcement_info: None, ... }` for each endpoint.
  This is how a node becomes “known” before any node announcement arrives.
* `refs/rust-lightning@d7a98064:lightning/src/routing/utxo.rs:246-294`
  — `check_hold_pending_node_announcement` stores the announcement per pending
  channel endpoint, keeping the newer timestamp
  (`latest_node_announce_a`/`_b`), and returns
  `"Awaiting channel_announcement validation to accept node_announcement"`.
* `.../utxo.rs:527-571` — on resolution, the held node announcements are taken
  from `latest_node_announce_a`/`_b` and replayed through the graph.
* `.../utxo.rs:411-415` — when `utxo_lookup` is `None`, channel announcements
  are “tentatively accept[ed]”. LDK Node sets `UtxoLookup = None` unless the
  `chain-bitcoind` feature is enabled
  (`/tmp/opencode/ldk-refs/ldk-node/src/gossip.rs:40-49`). Pending-node
  behaviour is therefore **configuration-dependent**, not a universal rule.

### 2.2 Fields and public exposure

* `refs/rust-lightning@d7a98064:lightning/src/ln/msgs.rs:1395-1417` —
  `UnsignedNodeAnnouncement` carries `features : NodeFeatures`, `timestamp`,
  `node_id`, `rgb : [u8;3]`, `alias : NodeAlias`, `addresses :
  Vec<SocketAddress>`, `excess_address_data`, and `excess_data`.
* `.../msgs.rs:1419-1440` — the signed `NodeAnnouncement` wraps the signature
  plus these contents.
* `refs/rust-lightning@d7a98064:lightning/src/routing/gossip.rs:1394-1440`
  — `NodeAnnouncementInfo` exposes `features()`, `last_update()`, `rgb()`,
  `alias()`, and `addresses()`. The `features` and `rgb` accessors are part of
  the same public surface as alias/addresses, not optional extras.
* `refs/rust-lightning@d7a98064:lightning/src/routing/gossip.rs:1498-1530`
  — `NodeAlias(pub [u8;32])`; `Display` truncates at the first NUL and replaces
  non-UTF-8/control bytes for display. Storage remains the full 32 bytes.
* `refs/rust-lightning@d7a98064:lightning/src/util/ser.rs:1746-1748`
  — the LDK hostname predicate is length ≤ 255 and every character is ASCII
  alphanumeric or one of `.`, `_`, `-`.

### 2.3 Address decode, excess data, and ports

* `refs/rust-lightning@d7a98064:lightning/src/ln/msgs.rs:4356-4383`
  — `LengthReadable for UnsignedNodeAnnouncement` reads `features`, timestamp,
  node id, rgb, alias, then `addr_len` and a descriptor loop. A known
  descriptor that overruns `addr_len` is `BadLengthDescriptor`; an unknown
  descriptor tag returns `Ok(Err(tag))`.
* `.../msgs.rs:4384-4400` — on an unknown tag LDK stops parsing, stores the
  tag plus the remaining `addr_len` bytes as `excess_address_data`, and appends
  any post-`addrlen` bytes to `excess_data`. It does **not** reject the
  announcement.
* `.../msgs.rs:4336-4344` — the writer emits
  `addr_len + excess_address_data.len()` as the on-wire length, then known
  descriptors followed by the excess bytes. The excess tail is inside the
  signed address field.
* `.../msgs.rs:1046-1093` — `SocketAddress` variants: IPv4 (4+2), IPv6
  (16+2), deprecated OnionV2 (12 bytes, no port), OnionV3 (35+2), Hostname
  (length-prefixed + 2). The decoder reads the port as an ordinary `u16`; it
  does not reject zero.
* `refs/bolts/07-routing-gossip.md:349` (origin) — “MUST NOT create an address
  descriptor with `port` equal to 0”; `:379-380` (receiver) — “if `port` is
  equal to 0: SHOULD ignore that address descriptor.” Zero is an encoder
  prohibition and a receiver drop rule, not a message-level decode failure.
* `refs/bolts/07-routing-gossip.md:355-395` — receiver rules: ignore the first
  unknown descriptor; ignore the message if `node_id` is not previously known
  from a `channel_announcement` **or** the timestamp is not greater; ignore
  additional type-5 DNS data and do not forward.

### 2.4 Chain-hash binding

* `refs/rust-lightning@d7a98064:lightning/src/routing/gossip.rs:2174-2179`
  — the chain check is on `channel_announcement`:
  `"Channel announcement chain hash does not match genesis hash"`.
* `.../gossip.rs:2473-2477` — the same check on `channel_update`.
* `.../gossip.rs:190-192`, `:448-450` — the graph stores its own
  `chain_hash`, set from the genesis block on construction (`:1786`).
* `refs/rust-lightning@d7a98064:lightning/src/ln/msgs.rs:1395-1417` —
  `node_announcement` has **no** chain-hash field. Chain binding reaches node
  announcements only indirectly: a node becomes known through a
  chain-checked channel announcement, and the node announcement is then
  accepted for that key.

### 2.5 LDK Node and LDK Server client behaviour

* `/tmp/opencode/ldk-refs/ldk-node/src/config.rs:285-302` — public announcing
  requires `node_alias` and non-empty `listening_addresses`;
  `announcement_addresses` overrides what is announced.
* `.../config.rs:549-559` — `may_announce_channel` returns
  `MissingAliasAndAddresses` / `MissingListeningAddresses` / `MissingNodeAlias`
  before any broadcast.
* `/tmp/opencode/ldk-refs/ldk-node/src/lib.rs:609-672` — periodic node
  announcement loop: requires an announced, ready channel and at least one
  connected peer; chooses `announcement_addresses` else
  `listening_addresses`; broadcasts `[0;3]` as rgb and the alias. This is an
  outbound policy that the Lean receive model does not represent.
* `/tmp/opencode/ldk-refs/ldk-node/src/graph.rs:125-175` — the UniFFI
  `NodeAnnouncementInfo` exposes only `last_update`, `alias`, and `addresses`
  (it drops `features` and `rgb` at this binding layer).
* `/tmp/opencode/ldk-refs/ldk-server/ldk-server/src/util/proto_adapter.rs:635-655`
  — the Server adapter does expose `features`, `rgb`, `alias`, `last_update`,
  and `addresses`.
* `/tmp/opencode/ldk-refs/ldk-server/ldk-server/src/api/get_node_info.rs:23-70`
  and `.../graph_get_node.rs:23-44` — the node’s own announcement addresses and
  the graph’s `NodeInfo` are user-visible; an unknown `node_id` in
  `graph_get_node` is an `InvalidRequestError`.

## 3. Gap matrix

| Behavior | Lean status | LDK evidence | Gap / counterexample | Priority |
|---|---|---|---|---|
| Admission requires a node previously known from a `channel_announcement` | **Missing / contradicted** | `gossip.rs@d7a98064:1911-1924`; BOLT `07-routing-gossip.md:381-384` | `applyGossipNodeCanonical` (`NodeCanonicalTargets.lean:348-361`) gates only on signature + `NodeSupersedes`; `ns1` (`:860-870`) is a reachable store holding `nA1` for a key with no channel. A fresh `nodeId` satisfies `NodeSupersedes` vacuously (`:137-139`). | P0 |
| Node announcement for a key with a pending channel is held, then replayed | **Missing** | `utxo.rs@d7a98064:246-294`, `:527-571`; `utxo.rs:411-415` for the `None` case | No pending-node queue, no per-endpoint latest-timestamp retention, no replay after channel validation. Because LDK Node may run with `UtxoLookup = None` (`ldk-node/src/gossip.rs:40-49`), this must be modelled as a policy variant, not a universal gate. | P1 |
| Strict timestamp: older or equal does not replace | **Covered faithfully** | `gossip.rs@d7a98064:1925-1940` | `NodeSupersedes` uses `m.timestamp < n.timestamp`; `reachableNodeCanonical_equal_timestamp_tie_boundary` (`NodeCanonicalTargets.lean:1114`) records the equal-timestamp boundary. No gap. | — |
| Extra per-node `sequence` gate | **Contradicted (model extension)** | LDK checks only `timestamp`; no sequence field in `UnsignedNodeAnnouncement` (`msgs.rs:1395-1417`) | `NodeRateState.Accepts` (`NodeIdentityChainTargets.lean:639-641`) requires both timestamp and sequence to increase. A timestamp-newer announcement with a non-increasing sequence is rejected by Lean but accepted by LDK. Do not wire this gate into admission. | P1 |
| `features` and `flen` on the signed announcement | **Missing** | `msgs.rs@d7a98064:1395-1417`; `gossip.rs:1394-1399`; BOLT `:351-354`, `:368-372` | `NodeAnnouncement` (`Gossip.lean:200-208`) has no `features` or `flen`. Unknown-even-bit connect/route policy (`FeaturesProps.rejects_unknown_even`, `FeaturesProps.lean:259`) cannot be applied to a node announcement. | P1 |
| `rgb_color` exact 3 bytes | **Partially covered** | `msgs.rs:1400-1403` (`[u8;3]`); BOLT `:300-303` | Lean stores an unbounded `ByteArray`; no length law. Low risk because the field does not affect routing. | P2 |
| `alias` 32 bytes, valid UTF-8, trailing zero bytes | **Missing** | `gossip.rs@d7a98064:1498-1530`; BOLT `:341-342` | Lean `alias : ByteArray` is unrestricted: no width, no UTF-8, no trailing-zero normal form. LDK storage is exactly 32 bytes and display truncates at the first NUL. | P2 |
| Address field is `u16 addrlen` framing with exact known widths | **Covered faithfully for canonical lists** | `msgs.rs@d7a98064:4356-4383`; BOLT `:316-334` | `decodeAddresses` (`NodeAddressTargets.lean:681-689`) requires the prefix to equal the remaining bytes and all descriptors to parse. Round-trip/injectivity/rejection theorems are present. | — |
| Unknown address descriptor / excess address data is retained | **Contradicted (receiver policy)** | `msgs.rs@d7a98064:4375-4400`; BOLT `:373-374` | `AddressType.ofTag` returns `none` and `parse_unknown_type` (`NodeAddressTargets.lean:546-555`) rejects the whole message. LDK stops at the first unknown tag and stores the signed tail as `excess_address_data`; BOLT says “SHOULD ignore the first address descriptor that does NOT match”, not reject the announcement. | P1 |
| Zero-port descriptor is ignored, not a message error | **Contradicted** | `msgs.rs:1046-1093` decodes a normal `u16`; BOLT `:379-380` | `Port` (`NodeAddressTargets.lean:109-113`) has a `nonzero` field and `Port.parse` (`:133-147`) returns `none` on zero. `Address.parse` then fails, so the whole address list is rejected; the receiver rule is per-descriptor drop. | P2 |
| DNS hostname character set | **Partially covered** | `ser.rs@d7a98064:1746-1748` alphanumeric + `.` `_` `-`; BOLT `:324-327` ASCII + Punycode | `AsciiBytes` (`NodeAddressTargets.lean:201-203`) admits spaces, controls and every byte < 0x80, so `dns_non_ascii_rejected` (`:583-592`) is weaker than LDK’s acceptance set. Note BOLT only requires ASCII; the narrower set is an LDK interop choice, not a BOLT MUST. | P2 |
| At most one type-5 DNS descriptor; ascending order | **Covered, but stricter than BOLT receiver** | BOLT `:355`, `:393-395` (ignore additional data, do not forward) | `WellOrderedAddressList` (`NodeAddressTargets.lean:629-631`) rejects an unsorted list or two DNS entries at decode. BOLT says ignore the extra DNS data rather than reject the message. This is a deliberate canonical-encoder/isolated-field model, not a receiver model. | P2 |
| Chain-hash filtering of node announcements | **Unmodelled / external** | `gossip.rs@d7a98064:2174-2179` (channel only); node announcement has no chain field | Lean disclaims chain filtering (`Gossip.lean:54-59`). The indirect route is a channel announcement; there is no `node_announcement.chain_hash` to model. | External |
| UTXO/funding-outpoint and on-chain channel confirmation | **Unmodelled / external** | `utxo.rs@d7a98064:380-415`; BOLT `:381-384` | No chain source, no UTXO lookup, no funding-script check. LDK itself makes this optional (`UtxoLookup = None`). | External |
| Identity across a `nodeId` rotation | **Model extension, no LDK/BOLT 7 counterpart** | No rotation message in BOLT 7; LDK has no rotation primitive in this surface | `RotationWitness.evidence` is opaque (`NodeIdentityTargets.lean:293-301`); `RotationChain` invents a message/certificate (`NodeIdentityChainTargets.lean:103-132`). These are useful model hypotheses, not fidelity targets. | External |
| Epoch encoding in rotation certificates | **Internal defect, documented** | No LDK counterpart | `epochByte` (`NodeIdentityChainTargets.lean:108`) uses `toUInt8`, so epochs 0 and 256 produce the same signed bytes; `:105-108` notes the non-injectivity but it is not mechanized. | P2 |
| Outbound announce policy / periodic rebroadcast | **Missing** | `ldk-node/src/lib.rs:609-672`; `config.rs:549-559` | Lean has no node-announcement creation, alias/address readiness gate, peer-count gate, or periodic broadcast. This is a client-policy layer, not a receive-path theorem. | External |
| One-DNS relay suppression and excess-size relay limits | **Missing** | `gossip.rs@d7a98064:1942-1946`, `:72` (`MAX_EXCESS_BYTES_FOR_RELAY = 1024`) | Lean has no relay decision, no `excess_data`/`excess_address_data` size bound, and no “do not forward additional type-5” rule. | External |

## 4. Proposed targets

The proposals are **additive**. None changes `NodeAnnouncement`,
`applyGossipNodeCanonical`, `NodeSupersedes`, `decodeAddresses`, or an existing
theorem. This is required so that the reachable counterexamples in
`NodeCanonicalTargets` and the rejection theorems in `NodeAddressTargets`
remain true.

### T1 — `LnLean.Proofs.Routing.NodeAdmissionTargets.node_admission_requires_known_node` (P0)

```lean
def NodeKnownFromChannel (s : GossipState) (k : PubKey) : Prop :=
  ∃ a ∈ s.announcements, a.nodeKey1 = k ∨ a.nodeKey2 = k

noncomputable def applyGossipNodeAdmission (verify : SigVerifier)
    (cs : CanonicalStore) : GossipMessage → CanonicalStore
  | .nodeAnnouncement n =>
      if n.signatureValid verify ∧
          NodeKnownFromChannel cs.gossip n.nodeId ∧
            NodeSupersedes n cs.gossip.nodeAnnouncements then
        { gossip := { cs.gossip with
            nodeAnnouncements :=
              insertNodeCanonical n cs.gossip.nodeAnnouncements }
          nodeKeyOf := cs.nodeKeyOf }
      else cs
  | m => applyGossipNodeCanonical verify cs m

theorem node_admission_requires_known_node
    (verify : SigVerifier) (cs : CanonicalStore) (n : NodeAnnouncement)
    (h : ¬ NodeKnownFromChannel cs.gossip n.nodeId) :
    applyGossipNodeAdmission verify cs (.nodeAnnouncement n) = cs

theorem node_admission_known_agrees
    (verify : SigVerifier) (cs : CanonicalStore) (n : NodeAnnouncement)
    (h : NodeKnownFromChannel cs.gossip n.nodeId) :
    applyGossipNodeAdmission verify cs (.nodeAnnouncement n) =
      applyGossipNodeCanonical verify cs (.nodeAnnouncement n)
```

Hypotheses: none beyond the definitions; `NodeKnownFromChannel` is intentionally
membership in the canonical announcement store, not “chain-validated channel”.
LDK creates the node entry when a channel announcement is accepted — tentatively
when no UTXO source exists (`utxo.rs@d7a98064:411-415`), after resolution
otherwise — and only then admits node announcements. On reachable stores the
existing `CanonicalStoreAdmitted` invariant supplies the signature/admission
premises, so the predicate does not need to re-check them.

Non-vacuity: the existing `ns0`/`ns1` construction
(`NodeCanonicalTargets.lean:851-870`) is the rejection witness — `nA1` is
admitted by the old function and rejected by the new one. A known-node witness
is a store containing one channel announcement naming `n.nodeId`; this is not
vacuous because `ns1` already shows the old path can hold a node record for a
key with no channel.

Why faithful: `gossip.rs@d7a98064:1911-1924` rejects exactly when the node map
has no key; `gossip.rs:2090-2105` creates the key from a channel announcement.

### T2 — `LnLean.Proofs.Routing.NodeAdmissionTargets.pending_node_replay` (P1)

```lean
structure PendingNodeQueue where
  held : List (PubKey × NodeAnnouncement)

def holdPendingNode (q : PendingNodeQueue) (n : NodeAnnouncement) :
    PendingNodeQueue
def replayPendingFor (k : PubKey) (q : PendingNodeQueue)
    (cs : CanonicalStore) : CanonicalStore

-- Holding a message only updates the queue, never the visible store.
def applyPendingNode (q : PendingNodeQueue) (cs : CanonicalStore)
    (n : NodeAnnouncement) : PendingNodeQueue × CanonicalStore :=
  (holdPendingNode q n, cs)

theorem pending_node_does_not_change_store
    (q : PendingNodeQueue) (cs : CanonicalStore) (n : NodeAnnouncement) :
    (applyPendingNode q cs n).2 = cs

theorem pending_node_replayed_after_channel
    (verify : SigVerifier) (cs : CanonicalStore) (q : PendingNodeQueue)
    (n : NodeAnnouncement)
    (hknown : NodeKnownFromChannel cs.gossip n.nodeId)
    (hheld : n ∈ q.held.map Prod.snd) :
    n ∈ (replayPendingFor n.nodeId q cs).gossip.nodeAnnouncements
```

Hypotheses: a pending channel endpoint exists for `n.nodeId`; the queue retains
only the greatest timestamp per `(nodeId, channel)` endpoint, matching
`latest_node_announce_a`/`_b` (`utxo.rs@d7a98064:246-294`). The `None`
UTXO-source case is a separate admission mode, not part of this queue.

Non-vacuity: hold `nA1` before adding `annA`; replay after the channel exists
must produce the same node list as the direct path. The negative half must show
the held record is not visible while pending.

Why faithful: the queue is only a withholding/replay mechanism; it must not
itself make an unknown node visible, otherwise it would collapse T1.

### T3 — `LnLean.Proofs.Routing.NodeAddressTargets.decodeAddressPrefix_excess` (P1)

```lean
def decodeAddressPrefix : List UInt8 → Option (List Address × List UInt8)

theorem decodeAddressPrefix_complete {l : List UInt8} {as : List Address}
    (h : decodeAddresses l = some as) :
    decodeAddressPrefix l = some (as, [])

theorem decodeAddressPrefix_stops_at_unknown
    {as : List Address} {t : UInt8} {tail : List UInt8}
    (hcanon : CanonicalAddressList as)
    (ht : AddressType.ofTag t = none) :
    decodeAddressPrefix (encodeAddressBlob as ++ t :: tail) =
      some (as, t :: tail)
```

The second theorem’s result is the signed excess tail; a companion
`decodeAddressPrefix_excess_length` should show it is exactly the remaining
`addrlen - consumed` bytes. Do **not** redefine `decodeAddresses`: its exactness
and rejection theorems are the canonical-origin model and must stay.

Non-vacuity: append an unknown tag (for example `6`) plus one byte after a
canonical `[ipv4Witness]` blob. The existing `witnessList_roundtrip` proves the
known prefix; the new theorem proves the tail is retained rather than `none`.

Why faithful: `msgs.rs@d7a98064:4375-4400` stops at the first unknown descriptor
and stores the tag plus the rest as `excess_address_data`.

### T4 — `LnLean.Proofs.Routing.NodeAddressTargets.hostname_charset` (P2)

```lean
def HostnameByte (b : UInt8) : Prop :=
  (0x30 ≤ b.toNat ∧ b.toNat ≤ 0x39) ∨
  (0x41 ≤ b.toNat ∧ b.toNat ≤ 0x5a) ∨
  (0x61 ≤ b.toNat ∧ b.toNat ≤ 0x7a) ∨
  b = 0x2e ∨ b = 0x5f ∨ b = 0x2d

def HostnameBytes (l : List UInt8) : Prop := ∀ b ∈ l, HostnameByte b

theorem hostname_space_rejected : ¬ HostnameBytes [0x20]
theorem hostname_example_accepted :
    HostnameBytes [0x65, 0x78, 0x61, 0x6d, 0x70, 0x6c, 0x65]
theorem hostname_charset_implies_ascii
    {l : List UInt8} (h : HostnameBytes l) : AsciiBytes l
```

`HostnameBytes` is a predicate layered on top of the existing `Address.dns`
constructor; it does not replace the `hascii` witness, so no existing address
proof changes. A strict decoder (`decodeHostnameStrict`) may be added later if
the parser must reject spaces at decode time.

Non-vacuity: `dnsWitness` (`NodeAddressTargets.lean:789-792`, host
`"example"`) satisfies the charset; a host containing `0x20` does not.

Why faithful: `ser.rs@d7a98064:1746-1748`. Caveat: BOLT only requires ASCII and
Punycode (`07-routing-gossip.md:324-327`), so this target is LDK interop, not a
BOLT conformance strengthening. State that in the docstring.

### T5 — `LnLean.Proofs.Routing.NodeAddressTargets.zero_port_descriptor_dropped` (P2)

```lean
-- Raw port is a Nat so that zero is representable before the `Port` refinement.
structure RawDescriptor where
  kind : AddressType
  data : List UInt8
  wirePort : Nat

def RawDescriptor.parse : List UInt8 → Option (RawDescriptor × List UInt8)
def RawDescriptor.WellFormed (d : RawDescriptor) : Prop
def RawDescriptor.toAddress : RawDescriptor → Option Address

theorem zero_port_descriptor_dropped
    (d : RawDescriptor) (hzero : d.wirePort = 0) :
    d.toAddress = none

theorem nonzero_port_descriptor_kept
    (d : RawDescriptor) (hnz : d.wirePort ≠ 0) (hvalid : d.WellFormed) :
    ∃ a, d.toAddress = some a
```

A `decodeAddressPrefixLenient` can then map `RawDescriptor.toAddress` over the
parsed list, silently dropping `none`s, and return the excess tail separately.
The two theorems state the receiver policy at the raw layer: zero is dropped
before the `Port` refinement, while a well-formed nonzero descriptor survives.

Because `Port` cannot hold zero, this target needs the raw descriptor layer or
a decoder that returns `Option (Address × Nat)`. The cheaper and safer form is a
theorem on a new `decodeAddressPrefixLenient` that yields
`(knownAddresses, excess)` and drops raw port-zero descriptors before
constructing `Address`. Keep `Port` and all existing nonzero lemmas unchanged.

Non-vacuity: the raw bytes for type 1 with port `00 00` are dropped while the
same descriptor with port `00 01` is kept.

Why faithful: BOLT `07-routing-gossip.md:379-380` says ignore the descriptor;
LDK decodes the port without a zero check (`msgs.rs@d7a98064:1046-1093`).

### T6 — `LnLean.Proofs.Routing.NodeAliasTargets.valid_alias_normal_form` (P2)

```lean
def ValidAlias (a : ByteArray) : Prop :=
  a.size = 32 ∧
    ∃ (prefix : List UInt8),
      prefix.length ≤ 32 ∧
        (∀ b ∈ prefix, b ≠ 0) ∧
          a.toList = prefix ++ List.replicate (32 - prefix.length) 0

theorem validAlias_trailing_zero_normal_form
    (a : ByteArray) (h : ValidAlias a) :
    ∃ prefix, a.toList = prefix ++ List.replicate (32 - prefix.length) 0

theorem alias_wrong_width_rejected
    (a : ByteArray) (h : a.size ≠ 32) : ¬ ValidAlias a
```

Non-vacuity: the all-zero 32-byte alias is valid; a 33-byte alias is not;
`"example" ++ zeros` is valid. UTF-8 validity of `prefix` is a separate
`String.validUTF8`-style predicate if the project’s byte API provides one.

Why faithful: BOLT `:341-342` requires a 32-byte valid-UTF-8 alias with trailing
zeros; LDK stores `[u8;32]` (`gossip.rs@d7a98064:1498`). Keep display
truncation out of `ValidAlias`; it is a rendering rule, not a wire rule.

### T7 — `LnLean.Proofs.Routing.NodeIdentityChainTargets.sequence_gate_divergence` (P1)

```lean
def LdkTimestampAccepts (st : NodeRateState) (a : NodeAnnouncementAdvert) : Prop :=
  st.lastTimestamp a.nodeId < a.timestamp

theorem rate_gate_implies_timestamp_newer
    (st : NodeRateState) (a : NodeAnnouncementAdvert) :
    NodeRateState.Accepts st a → LdkTimestampAccepts st a
  := fun h => h.1

theorem rate_gate_strictly_stronger
    (st : NodeRateState) (a : NodeAnnouncementAdvert)
    (hts : LdkTimestampAccepts st a)
    (hseq : a.sequence ≤ st.lastSequence a.nodeId) :
    LdkTimestampAccepts st a ∧ ¬ NodeRateState.Accepts st a
```

`rate_gate_implies_timestamp_newer` says the Lean gate is at least as strict as
LDK; `rate_gate_strictly_stronger` exhibits an announcement LDK accepts and the
sequence gate rejects. The target should also record that `sequence` has no
field in `UnsignedNodeAnnouncement` (`msgs.rs@d7a98064:1395-1417`), so
`Accepts` must never be used as the `applyGossipNodeAdmission` gate.

Non-vacuity: choose `lastTimestamp = 10`, `lastSequence = 5`, announcement
timestamp `11`, sequence `5`; `TimestampNewer` holds and `Accepts` fails.

Why faithful: this is a counterexample-preservation target, not a new protocol
rule. It prevents a later wave from “strengthening” admission with a gate LDK
does not have.

### T8 — `LnLean.Proofs.Routing.NodeFeaturesTargets.node_features_policy` (P1, defer)

```lean
structure NodeAnnouncementFeatures where
  bits : LnLean.Proofs.Protocol.FeatureVector

def NodeFeaturesAcceptable (known : KnownFeatures)
    (f : NodeAnnouncementFeatures) : Prop :=
  LnLean.Proofs.Protocol.Accepts known f.bits

theorem unknown_even_node_features_not_routable
    (known : KnownFeatures) (f : NodeAnnouncementFeatures)
    (n : Nat) (hk : known n = false) (hr : f.bits.requires n = true) :
    ¬ NodeFeaturesAcceptable known f
```

The proof is the existing `FeaturesProps.rejects_unknown_even`
(`FeaturesProps.lean:259-263`) applied to `f.bits`. This is a **shadow record**,
not a change to `NodeAnnouncement`. It lets the existing feature machinery be
stated over node announcements without touching the core record or the opaque
digest. A later wave can add the real `features`/`flen` fields and a
signed-encoding theorem; that is a core model change and should not be smuggled
into wave 13.

Non-vacuity: reuse the concrete feature vectors from `FeaturesProps`; a known
even bit is acceptable, an unknown even bit is not.

Why faithful: `msgs.rs@d7a98064:1395-1401`; BOLT `:351-354`, `:368-372` (unknown even bits:
do not connect, do not route through; unless the invoice has the same bit, do
not pay to). The exact “unless invoice” exception is a policy branch that
should be explicit, not hidden in a boolean.

## 5. Assumptions, counterexamples, and non-vacuity risks

1. **Do not repair `applyGossipNodeCanonical` in place.** `ns1`
   (`NodeCanonicalTargets.lean:860-870`) and
   `missing_endpoint_channel_admitted` (`NodeIdentityTargets.lean:940-960`)
   are reachable only because the old function admits an unknown node. Adding
   the known-node gate to the old function would make those theorems false or
   force a rewrite of the non-vacuity story. T1 must be a new wrapper.
2. **`NodeSupersedes` is not an admission rule.** It is vacuous for a fresh
   `nodeId` by design (`NodeCanonicalTargets.lean:137-139`), which is why the
   unknown-node witness exists. Any theorem of the form
   “`NodeSupersedes` implies admissible” is false under BOLT/LDK.
3. **`WireMember` is not the admission gate.** `WireMember`
   (`NodeIdentityTargets.lean:377-382`) requires **both** channel endpoints to
   have node announcements. LDK’s gate only requires the announcing node to be
   known from some channel; `missing_endpoint_channel_admitted` is the
   opposite-direction gap. Keep the two predicates separate.
4. **Chain validation is configuration-dependent.** LDK Node sets
   `UtxoLookup = None` without `chain-bitcoind`
   (`ldk-node/src/gossip.rs:40-49`), and rust-lightning then tentatively accepts
   channel announcements (`utxo.rs@d7a98064:411-415`). A `NodeKnownFromChannel`
   predicate that demands a chain-validated channel would model a stricter
   policy than the pinned client can run. If a chain-validated variant is
   wanted, make it an explicit parameter, not the default.
5. **No `node_announcement.chain_hash`.** The chain hash belongs to
   `channel_announcement` (`gossip.rs@d7a98064:2174-2179`). Adding a chain field
   to the node record would invent a wire field and would not be BOLT 7.
6. **Rotation evidence is opaque.** `RotationWitness.evidence` is a `ByteArray`
   with deliberately unmodelled meaning (`NodeIdentityTargets.lean:293-301`);
   `RotationChain` invents its message/certificate format
   (`NodeIdentityChainTargets.lean:103-132`). No theorem in this lane may claim
   cryptographic identity, ownership, or LDK compatibility for either.
7. **Epoch non-injectivity is a real defect.** `epochByte e = ByteArray.mk
   #[e.toUInt8]` (`NodeIdentityChainTargets.lean:108`) maps 0 and 256 to the
   same signed bytes, so two distinct epochs can produce identical
   certificates. This is documented nearby but not mechanized. If the rotation
   layer is retained, add `epochByte_injective_of_lt_256` and a concrete
   `epochByte 0 = epochByte 256` counterexample, or switch to a 4-byte epoch
   encoding as an explicitly non-wire model change. This is independent of the
   LDK fidelity question and should not block T1–T3.
8. **Sequence rate gate contradicts LDK.** `NodeRateState.Accepts`
   (`NodeIdentityChainTargets.lean:639-641`) uses an extra `sequence` field
   that BOLT 7 does not carry. Keep it as a model-extension gate for the
   invented rotation protocol, never for `node_announcement` admission.
9. **Absolute `addrlen` is stricter than the receiver.** `decodeAddresses`
   rejects a field whose prefix overstates or understates the remaining bytes
   (`NodeAddressTargets.lean:681-689`). BOLT’s receiver rule only warns on
   insufficient `addrlen` (`07-routing-gossip.md:375-378`), and LDK retains an
   excess tail. T3 adds a prefix decoder; it must not weaken
   `decodeAddresses_addrlen_mismatch` (`:716`).
10. **Alias display normalization is not wire validity.** LDK `Display`
    truncates at the first NUL and sanitizes control bytes
    (`gossip.rs@d7a98064:1500-1530`), but storage remains the full 32 bytes.
    `ValidAlias` must govern the wire/storage shape, not the display string.
11. **Hostname charset is an LDK choice.** BOLT requires ASCII plus Punycode;
    LDK narrows to alphanumeric and `.` `_` `-`
    (`ser.rs@d7a98064:1746-1748`). T4 must say which fidelity target it serves,
    otherwise it will look like an unjustified strengthening of BOLT.
12. **Outbound policy is not receive-path fidelity.** LDK Node’s alias/address
    readiness and 30-second broadcast loop
    (`ldk-node/src/lib.rs:609-672`, `config.rs:549-559`) are client behaviour.
    Modelling them would require a node-announcement constructor and a clock;
    neither exists in the current core, and neither is needed for T1–T3.

## 6. Wave-13 recommendation

**Implement a narrow, additive wave-13 slice; do not claim `RT-02` closure.**

* **Implement in wave 13:** T1 (known-node admission wrapper), T3 (address
  prefix/excess decoder), and T7 (sequence-gate divergence). These are small,
  local, additive, and each has a concrete non-vacuity or counterexample
  witness. They do not touch the core record or any existing theorem.
* **Implement only if capacity remains:** T2 (pending-node queue) and T8
  (shadow feature-policy record). T2 is the most valuable remaining behaviour
  but needs a queue/replay abstraction and a careful “not visible while
  pending” invariant. T8 is a policy statement, not a wire model.
* **Defer to wave 14 or leave as explicit model extensions:** T4 (strict LDK
  hostname charset), T5 (zero-port drop), T6 (alias normal form), and the
  `epochByte` injectivity fix. These improve fidelity but are either narrower
  than BOLT or belong to the invented rotation layer.
* **Treat as external / human barrier:** cryptographic rotation identity and
  certificate chains, chain-existence and UTXO policy, a production
  gossip/rotation pipeline, outbound announce policy, and relay/excess-size
  limits. There is no safe Lean-only theorem that closes these; LDK itself
  makes chain validation optional and has no rotation primitive.
* **Preserve:** `ns1`, `missing_endpoint_channel_admitted`, the equal-timestamp
  boundary, `decodeAddresses` rejection theorems, and
  `rotation_not_signature_preserving`. A wave-13 change that makes any of these
  false is out of scope, even if it looks like a stronger admission rule.
* **Gate:** compile only the new/changed modules with `lake env lean`; do not
  build the whole tree, do not run cargo tests, and do not fetch network
  dependencies.

Bottom line: the pinned LDK surface supports a narrow admission/address-field
slice, but the high-value security claims in `LN-RT-002` remain conditional.
Wave 13 should add the wrapper and the excess decoder, keep the existing
counterexamples, and record rotation identity, chain/UTXO policy, features
encoding, and the production pipeline as external or wave-14 work.

## 7. Evidence and commands

Read-only inspection only; the worktree is `repair/integrated` at `f7f0628`
with no edits from this lane.

```sh
# Lean surface
rg -n "structure NodeAnnouncement|def NodeSupersedes|def applyGossipNodeCanonical" \
  LnLean/Routing/Gossip.lean LnLean/Proofs/Routing/NodeCanonicalTargets.lean
rg -n "structure Port|def decodeAddresses|theorem parse_unknown_type|def AsciiBytes" \
  LnLean/Proofs/Routing/NodeAddressTargets.lean
rg -n "structure RotationWitness|structure WireMember|theorem missing_endpoint_channel_admitted" \
  LnLean/Proofs/Routing/NodeIdentityTargets.lean
rg -n "def epochByte|structure NodeRateState|def Accepts" \
  LnLean/Proofs/Routing/NodeIdentityChainTargets.lean

# Catalog and scope
sed -n '45,52p' docs/TRACEABILITY.md
sed -n '60,72p' docs/THEOREM-INDEX.md
sed -n '30,42p;60,70p' docs/OPEN-ISSUES.md

# Pinned LDK (rust-lightning rev comes from ldk-node/Cargo.toml:89)
git -C refs/rust-lightning cat-file -t d7a980641c6325ddda5072a0f470ef8392676cf5
git -C refs/rust-lightning show d7a98064:lightning/src/routing/gossip.rs | \
  sed -n '1882,1946p;2090,2105p;2174,2179p'
git -C refs/rust-lightning show d7a98064:lightning/src/routing/utxo.rs | \
  sed -n '246,294p;411,415p;527,571p'
git -C refs/rust-lightning show d7a98064:lightning/src/ln/msgs.rs | \
  sed -n '1395,1440p;4336,4400p'
git -C refs/rust-lightning show d7a98064:lightning/src/util/ser.rs | \
  sed -n '1746,1748p'

# LDK Node / Server client surface
sed -n '285,302p;549,559p' /tmp/opencode/ldk-refs/ldk-node/src/config.rs
sed -n '609,672p' /tmp/opencode/ldk-refs/ldk-node/src/lib.rs
sed -n '125,175p' /tmp/opencode/ldk-refs/ldk-node/src/graph.rs
sed -n '635,655p' /tmp/opencode/ldk-refs/ldk-server/ldk-server/src/util/proto_adapter.rs
sed -n '23,70p' /tmp/opencode/ldk-refs/ldk-server/ldk-server/src/api/get_node_info.rs
sed -n '23,44p' /tmp/opencode/ldk-refs/ldk-server/ldk-server/src/api/graph_get_node.rs

# BOLT 7
sed -n '287,395p' refs/bolts/07-routing-gossip.md
```

Pin note: `refs/rust-lightning` is checked out at `fe49009`, so direct reads of
that worktree give the older anchor lines quoted in `Gossip.lean:40-61`; every
LDK citation above was taken from `d7a98064`, the rev in
`/tmp/opencode/ldk-refs/ldk-node/Cargo.toml:89`.
