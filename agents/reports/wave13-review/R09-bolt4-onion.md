# R09 — BOLT 4 onion construction, processing, and errors
**Status:** read-only review
**Pins:** LDK Node `fa123fed131e27ecc420b77fa7086fcf1ddaebb8`, LDK Server `c17dc11dde38f88c53457039ddf30c6b90a63ba2`
**Review branch:** `repair/integrated` (no branch, commit, or non-report file changes made)

## 1. Scope and current Lean surface

This lane covers the BOLT 4 onion packet: packet and `hop_payloads` structure,
per-hop payload TLVs and construction, decryption/peel semantics, forwarding
checks, return packets and failure codes, `path_key`, and route blinding. It
does not re-review route selection (`LN-RT-001`), CLTV/fee arithmetic as a
graph problem (`LN-RT-005`), BOLT 11 encoding (`LN-PM-003`), commitment
mechanics, or transport. Those surfaces appear only where they constrain an
onion claim.

The short verdict is: **the current onion model is a structural skeleton, not
a BOLT 4 wire or processing model.** It has useful non-vacuous layer-count and
branch laws, but it does not decode or construct a BOLT 4 payload TLV, does not
perform Sphinx decryption or HMAC computation, does not implement BOLT 4 failure
codes or the exact return layout, and does not model route blinding or
`path_key` at all. The existing catalog rows are true for the skeleton; they do
not establish BOLT 4 conformance.

### 1.1 Catalog claims that touch this surface

| Row | Catalog claim | Actual Lean target | What it does and does not cover |
|---|---|---|---|
| `LN-RT-003` | "Peeling one onion layer exposes the next hop or a terminal payload, never both." | `LnLean.Routing.Onion.peel_deterministic` (`LnLean/Routing/Onion.lean:488-515`) | Proves an exhaustive/ exclusive split of the model's two `OnionPayload` constructors. The split is by `p.layers = []`, not by BOLT 4's all-zero `next_hmac`; no HMAC, version, key, payload TLV, or decryption is involved. |
| `LN-RT-004` | "An onion layer with an invalid HMAC is rejected rather than forwarded." | `LnLean.Routing.Onion.hmac_sound` (`Onion.lean:517-536`), with `openLayer_verified` (`:322-335`) and `openLayer_reject` (`:354-365`) | True only for a caller that uses `openLayer I tag p` and supplies a tag. `verifyHmac` is an arbitrary field of `OnionInterface`; the model never computes `HMAC256(mu, hop_payloads || associated_data)`. The raw `peel` ignores the check, as `D25.waveD_d25_peel_bypasses_hmac` records. |
| `LN-CR-003` | 32-byte onion HMAC tags, and finite-execution C8 binding of hop payloads. | `LnLean.Crypto.Hash.onionHmacTag_size_and_bindsOn` | A conditional cryptographic contract over an abstract model. It is not a wire/onion-conformance theorem and does not connect a parsed BOLT 4 packet to a decryption result. |
| `LN-RT-005` | The CLTV expiry at each hop increases by at least the hop's `cltv_expiry_delta`. | `LnLean.Routing.Route.cltv_accumulates` | Route arithmetic only. The onion model stores `cltvDelta`, not BOLT 4's absolute `outgoing_cltv_value`, and `sealRoute` does not construct per-hop payloads from the route's amount/CLTV schedule. |
| `LN-PM-003` | "The final onion payload's payment secret matches the invoice's payment secret." | Existing invoice targets, plus `LnLean.Proofs.ModelHardening.F13.accepted_secret_eq` (`F13.lean:118-122`) | `FinalPayload` (`F13.lean:76-85`) is a separate record and `FinalPayloadAcceptedFor` (`:96-101`) is a hypothesis, not a decoder. No theorem connects `peel`/`OnionHop` to `FinalPayload`, and `F13.unconstrained_accept_not_match` (`:229-236`) preserves the unconstrained counterexample. |

There is **no catalog row** for BOLT 4 payload TLVs, failure-code data layouts,
return-path processing, route-blinding wire format, `path_key`, or the checked
peel contract. `RouteBlindingProps` exists and is imported, but it is not a
catalog claim.

### 1.2 The packet record is a layer list, not a BOLT 4 packet

`OnionHop` (`LnLean/Routing/Onion.lean:122-127`) is:

```lean
structure OnionHop where
  node : NodeId
  shortChannelId : ShortChannelId
  amountMsat : Msat
  cltvDelta : Nat
```

`OnionPacket` (`:158-164`) is:

```lean
structure OnionPacket where
  version : Nat
  ephemeralKey : PubKey
  routingInfo : ByteArray
  layers : List OnionLayer
  hmac : ByteArray
```

Each `OnionLayer` (`:131-135`) carries a decoded `hop`, a `ciphertext`, and a
per-layer `hmac`. This differs from BOLT 4 in several material ways:

1. BOLT 4's `hop_payloads` is a 1300-byte byte field containing a BigSize
   length, payload, 32-byte `next_hmac`, repeated per hop, plus filler. The
   model stores a `List OnionLayer`; a successful `peel` simply removes the
   head (`peel_cons`, `:258-261`).
2. BOLT 4 has one outer packet HMAC and an inner `next_hmac` per layer. The
   model has both `OnionPacket.hmac` and `OnionLayer.hmac`, but `peel` reads
   neither and `openLayer` compares only the layer field with a caller-supplied
   `tag` (`:305-312`).
3. `version : Nat` is unconstrained; `peel` and `openLayer` never inspect it.
   BOLT 4 requires version `0x00` and says a reader MUST fail otherwise
   (`refs/bolts/04-onion-routing.md:163`, `:918-920`).
4. `ephemeralKey : PubKey` is structurally a byte holder. `PubKey.Valid` is
   only `bytes.size = 33` (`LnLean/Basic/Core.lean:166`); no secp256k1 point
   validity is required, and neither `peel` nor `openLayer` checks it.
5. `OnionHop.cltvDelta` is a relative delta. BOLT 4's payload carries the
   absolute `outgoing_cltv_value` (`04-onion-routing.md:198-200`, `:232-240`).
   There is no theorem converting `Route.cltvAt` into this field.
6. `OnionHop.amountMsat` is a caller-supplied amount. `sealRoute`
   (`LnLean/Proofs/Routing/OnionProps.lean:132-136`) fills every hop with
   `r.amountMsat`, not BOLT 4's per-hop fee-adjusted `amt_to_forward`. A route
   with any nonzero hop fee is therefore a concrete counterexample to reading
   `sealRoute` as BOLT 4 construction.

### 1.3 Peeling, opening, and terminal detection

`peel` (`Onion.lean:245-251`) is total:

```lean
def peel (p : OnionPacket) : Option OnionPayload :=
  match p.layers with
  | [] => some (.final p.routingInfo)
  | l :: ls => some (.forward l.hop { p with layers := ls })
```

`peel_deterministic` proves the two branches are exhaustive and exclusive.
That is a real law about this representation, and `E24`/`O01` correctly treat
it as structural. It is not the BOLT 4 terminal rule. BOLT 4 says the reader
extracts `next_hmac` from `unwrapped_payloads` and is final exactly when
`next_hmac` is all-zero (`04-onion-routing.md:951-963`). The model has no
`next_hmac` field with that meaning. Conversely, every non-empty layer list
peels forward, regardless of any HMAC value (`peel_cons`), so "layers = [] iff
final" is a model convention, not a consequence of BOLT 4.

`openLayer` (`Onion.lean:297-312`) introduces an abstract interface:

```lean
structure OnionInterface where
  verifyHmac : ByteArray → ByteArray → Bool
  hmacBinding : Prop
```

The interface has no notion of key derivation, associated data, path key,
version, public-key validity, or replay. A successful open proves only that the
opaque verifier returned `true` for the supplied `tag`. `hmac_sound` is thus a
conditional statement about the model's checked step, not a statement that a
BOLT 4 packet with an invalid computed HMAC is rejected. The raw peel
counterexample is mechanized at
`LnLean/Proofs/WaveD/D25.lean:232-241`:

```lean
theorem waveD_d25_peel_bypasses_hmac :
    MacInvalid rejectingInterface ByteArray.empty sampleLayer ∧
      (∃ next, peel samplePacket = some (.forward sampleHop next)) ∧
      openLayer rejectingInterface ByteArray.empty samplePacket = none
```

### 1.4 Failure packets and errors

`OnionError` (`Onion.lean:443-446`) is a coarse `ErrorCode` plus opaque bytes.
`ErrorCode` (`Basic/Core.lean:246-261`) has 14 constructors, including
`protocol`, `funding`, `update`, and `internal`, which are **not** BOLT 4
failure codes. It has no numeric wire values. The BOLT 4 code table has 24
assigned codes with flag bits `BADONION`, `PERM`, `NODE`, and `UPDATE`
(`04-onion-routing.md:1273-1450`), and many codes carry typed data.

`OnionError.packetSize` (`Onion.lean:454-456`) is
`2 + data.size + (256 - data.size) + 32 = 290` when the data fits. The actual
BOLT 4 return packet is `hmac(32) || failure_len(2) || failuremsg ||
pad_len(2) || pad` (`04-onion-routing.md:1059-1069`), and the spec requires
`failure_len + pad_len >= 256` (`:1136-1143`). Thus the **minimum** spec packet
is 292 bytes, and it is exactly 292 only when the sum is 256. The repository
records the divergence honestly:
`bolt4FailurePacketSize_eq` (`OnionProps.lean:477-484`) gives 292, and
`bolt4FailurePacketSize_eq_model_add_two` (`:486-493`) proves the model omits
exactly two bytes (`pad_len`).

`sealError`/`parseError` (`LnLean/Proofs/PhaseC3/OnionError.lean:203-206`,
`:271-279`) prove structural round trips for the model's
`failure_len || padded-message || hmac` order. They explicitly do **not**
model BOLT 4's leading HMAC, `pad_len`, failure code, TLV payload, return-path
obfuscation, or the 32768-byte truncation rule (`OnionError.lean:70-87`).

### 1.5 Messages and route blinding

`UpdateAddHtlc` (`LnLean/Protocol/Messages.lean:198-205`) has no
`path_key`/`blinding_point` field for the BOLT 2 type-0 TLV
(`refs/bolts/02-peer-protocol.md:2783-2796`). `UpdateFailHtlc` (`:215-219`)
stores `reason : ByteArray` and does not decode the return packet.
`Msg` (`:268-289`) has no `update_fail_malformed_htlc` constructor at all,
although BOLT 2 defines one with `sha256_of_onion` and `failure_code`
(`02-peer-protocol.md:2942-2970`).

`RouteBlindingProps` (`LnLean/Proofs/Routing/RouteBlindingProps.lean`) is the
only blinding surface. Its `BlindedHop` (`:437-443`) has `realNode`,
`blindedNodeId`, `shortChannelId`, `terms`, and `encryptedRecipientData`.
`exposed` (`:450-451`) returns only `(blindedNodeId, encryptedRecipientData)`;
`BlindedPath` (`:473-478`) has `introduction`, `firstPathKey`, `hops`, and
`amountMsat`; `exposedWire` (`:485-487`) returns
`(introduction, firstPathKey, hops.map exposed)`.

That is a useful non-interference abstraction, but it is not BOLT 4's wire
format. BOLT 4's `blinded_path` is
`first_node_id: sciddir_or_pubkey || first_path_key: point || num_hops: byte ||
path`, and each `blinded_path_hop` is `blinded_node_id: point ||
enclen: u16 || encrypted_recipient_data`
(`04-onion-routing.md:442-455`). The model has no `num_hops` field, no
`enclen`, no `sciddir_or_pubkey` sum type, no ECDH, no `rho`/`mu` keys, no
ChaCha20-Poly1305, no `next_path_key_override`, and no `path_key` state. The
module's own "What is explicitly not modelled" section
(`RouteBlindingProps.lean:84-119`) says exactly this. Its fee/CLTV preservation
theorems are about a creator-side `Route`, not about a BOLT 4 blinded onion.

### 1.6 What remains true and non-vacuous

The skeleton is not vacuous:

* `sealLayers_layerCount` (`Onion.lean:205-209`) and
  `sealRoute_layerCount` (`OnionProps.lean:138-142`) have inhabited witnesses
  for zero, one, and multiple hops.
* `peel_deterministic` has both branches inhabited: the empty-layer branch and
  the non-empty `sealLayers` branch.
* `openLayer_verified` has a concrete accepting interface witness in
  `D25` (the `MacValid`/`verifyingInterface` path), and
  `waveD_d25_peel_bypasses_hmac` supplies the rejecting-interface witness.
* `OnionError.packetSize_eq_290` has the empty-data witness
  (`packetSize_empty`, `Onion.lean:470-474`).
* `RouteBlindingProps` has concrete `BlindedPath` values in its preservation
  theorems; those witnesses preserve the fee/CLTV abstraction, not BOLT 4
  confidentiality.

The problem is fidelity, not vacuity. A theorem can be true of the skeleton and
false of a BOLT 4 implementation if it is cited as a wire-conformance claim.

## 2. LDK datapoints (with `file:line`)

All LDK citations below are read-only inspection of the pinned clones. The
public LDK Node/LDK Server surface is intentionally high-level; the onion
internals are delegated to rust-lightning. The local `refs/rust-lightning`
tree is commit `fe4900930c6bd5786ec4203274d7cf312776a5a6`, while LDK Node's
`Cargo.toml:89-98` pins rust-lightning
`d7a980641c6325ddda5072a0f470ef8392676cf5`. The rust-lightning line anchors
are therefore **behavioral anchors, not exact dependency line numbers**. The
BOLT and LDK Node/Server anchors are exact for this review.

### 2.1 The public LDK Node surface does not expose onion processing

* `ldk-node/src/message_handler.rs:21-81` is the
  `NodeCustomMessageHandler`. It implements `CustomMessageReader` and
  `CustomMessageHandler` for `RawLSPSMessage` (LSPS0 liquidity messages). Its
  `handle_custom_message` (`:54-58`) forwards to the liquidity manager. This is
  not an onion packet handler and has no BOLT 4 payload processing.
* `ldk-node/src/connection.rs:78-112` handles idempotent peer connection and
  deduplicates concurrent connect attempts. `:121-131` handles `OnionV2`/
  `OnionV3` socket addresses; the only mention of "onion" is transport
  addressing, not onion routing. No per-hop processing is surfaced.
* `ldk-node/src/ffi/types.rs:2038-2046` and `:2370-2378` expose only
  `supports_route_blinding()` / `requires_route_blinding()` feature checks.
  There is no public route-blinding construction or decryption API in this
  surface.
* `ldk-node/src/payment/spontaneous.rs:95-107` builds
  `RecipientOnionFields` with `with_custom_tlvs` and rejects spec-defined
  custom values. `:181-213` exposes send-with-custom-TLV APIs. This proves the
  public API can add recipient TLVs, but it does not expose the full payload
  layout or per-hop construction.
* `ldk-node/src/payment/bolt11.rs:221` reads `invoice.payment_secret()`;
  `:254` and `:282` store it in `PaymentKind::Bolt11`. The payment secret is a
  public invoice/payment fact, not a decoded onion payload.
* `ldk-node/src/event.rs:156-171` exposes `PaymentFailed { reason :
  Option<PaymentFailureReason> }`; `:1609-1654` persists that high-level
  reason. It is a payment-level classification, not a BOLT 4 `failure_code`.
* `ldk-node/src/event.rs:992-1001` inspects incoming `onion_fields` for an
  unknown even custom TLV and calls
  `fail_htlc_backwards_with_reason(..., FailureCode::InvalidOnionPayload(...))`.
  This is the clearest public evidence that unknown even TLV handling is a real
  processing requirement, though the event only exposes the resulting custom
  records/claimable payment, not the onion bytes.
* `ldk-node/src/event.rs:1175-1177` and `:1523-1524` surface received
  `custom_tlvs` in payment events. They do not expose `amt_to_forward`,
  `outgoing_cltv_value`, `encrypted_recipient_data`, or `current_path_key`.
* `ldk-node/src/payment/forwarding.rs:95-132` and
  `ldk-node/src/payment/forwarding_store.rs:70-107` expose forwarded amounts,
  channel/node identifiers, fees, and timestamps. They do not expose failure
  codes or onion payload fields.

### 2.2 LDK Server surfaces only high-level forwarding/payment facts

* `ldk-server/ldk-server/src/api/spontaneous_send.rs:45-73` accepts caller
  custom TLVs and chooses `send_with_custom_tlvs` or
  `send_with_preimage_and_custom_tlvs`. This is a construction input, not a
  BOLT 4 conformance surface.
* `ldk-server/ldk-server/src/api/get_forwarded_payment_details.rs:20-25`
  returns a `ForwardedPayment`; the adapter at
  `ldk-server/src/util/proto_adapter.rs:507-525` copies channel IDs, node IDs,
  amounts, fees, `claim_from_onchain_tx`, and timestamp. No failure code,
  failure data, or onion payload is present.
* `ldk-server/ldk-server/src/main.rs:930-954` maps
  `PaymentFailureReason` values (`RecipientRejected`, `RetriesExhausted`,
  `RouteNotFound`, `BlindedPathCreationFailed`, ...). These are origin-side
  payment outcomes, not BOLT 4 hop failure codes.
* `ldk-server/ldk-server/src/api/decode_offer.rs:73-105` exposes a
  BOLT 12 offer's blinded path as `introduction_node`, `blinding_point`, and
  `num_hops`. It does not expose per-hop `blinded_node_id`, `enclen`, or
  `encrypted_recipient_data`. Even the server API therefore stops short of the
  BOLT 4 blinded-path wire record.
* `ldk-server/ldk-server/src/api/bolt11_receive.rs:34-36` and
  `decode_invoice.rs:35`, `:98` echo `payment_secret` from a BOLT 11 invoice.
  This is invoice data, not final-hop onion decoding.

### 2.3 rust-lightning behavior anchors (with pin caveat)

These are the closest concrete processing anchors. They are read from
`refs/rust-lightning` at `fe490093...`; LDK Node pins `d7a98064...`, so line
numbers may drift in the dependency.

* `lightning/src/ln/msgs.rs:738-760` — `UpdateAddHTLC` has
  `blinding_point: Option<PublicKey>`, the type-0 `path_key` TLV. The Lean
  `UpdateAddHtlc` has no such field.
* `lightning/src/ln/msgs.rs:865-891` — `UpdateFailHTLC.reason` is an opaque
  byte blob, and `UpdateFailMalformedHTLC` has `sha256_of_onion` plus
  `failure_code: u16`. Lean has only the opaque `UpdateFailHtlc.reason` and no
  malformed variant.
* `lightning/src/ln/msgs.rs:2741-2761` — `OnionPacket` has `version`,
  `public_key: Result<PublicKey, secp256k1::Error>`, `hop_data: [u8; 20*65]`,
  and `hmac: [u8; 32]`. The `Result` is deliberate so a bogus key still
  produces a BOLT 4 error response. Lean's `ephemeralKey : PubKey` is neither
  validated nor error-producing.
* `lightning/src/ln/onion_payment.rs:505-590` — `peel_payment_onion` decodes,
  distinguishes forward/blinded-forward/dummy/final, checks incoming CLTV, and
  returns `InboundHTLCErr` with a `LocalHTLCFailureReason`. This is the
  processing shape the Lean `OnionPayload.forward/final` abstraction omits.
* `lightning/src/ln/onion_utils.rs:1639-1795` —
  `LocalHTLCFailureReason` enumerates `TemporaryNodeFailure`,
  `PermanentNodeFailure`, `InvalidOnionVersion`, `InvalidOnionHMAC`,
  `InvalidOnionKey`, `TemporaryChannelFailure`, `PermanentChannelFailure`,
  `RequiredChannelFeature`, `UnknownNextPeer`, `AmountBelowMinimum`,
  `FeeInsufficient`, `IncorrectCLTVExpiry`, `CLTVExpiryTooSoon`,
  `IncorrectPaymentDetails`, `FinalIncorrectCLTVExpiry`,
  `FinalIncorrectHTLCAmount`, `ChannelDisabled`, `CLTVExpiryTooFar`,
  `InvalidOnionPayload`, `MPPTimeout`, and `InvalidOnionBlinding`. It also has
  an `UnknownFailureCode { code }` escape. Lean's `ErrorCode` is much coarser
  and includes non-BOLT4 names.

### 2.4 BOLT 4 and BOLT 2 anchors

The following are the primary specifications used for the gap matrix:

* Packet structure and version: `04-onion-routing.md:138-163`.
* `hop_payloads` repeated length/payload/hmac and filler: `:165-187`.
* Payload TLV types 2, 4, 6, 8, 10, 12, 16, 18: `:189-219`.
* Writer and reader requirements, including unknown even types,
  final-only `payment_data`, `payment_metadata`, and blinded-path fields:
  `:246-344`.
* Route-blinding wire format and crypto requirements: `:442-455`,
  `:485-545`.
* Onion decryption: version/key/replay checks, HMAC over
  `hop_payloads || associated_data`, BigSize payload length, all-zero
  `next_hmac` terminal test, next-key blinding: `:907-963`.
* Return packet layout, `failure_len + pad_len >= 256`, and the 32768-byte
  limit: `:1039-1077`, `:1136-1143`, `:1187-1189`.
* Failure code flags and 24 code definitions: `:1257-1450`.
* Failure selection rules, including `invalid_onion_blinding`:
  `:1452-1556`.
* Receiving failure codes and PERM/NODE/UPDATE behavior: `:1575-1606`.
* BOLT 2 `update_add_htlc` and type-0 `path_key`: `02-peer-protocol.md:2783-2796`;
  associated-data/`path_key` decryption requirements: `:2834-2874`.
* BOLT 2 `update_fail_htlc`/`update_fail_malformed_htlc`: `:2942-2970`;
  `invalid_onion_blinding` failure handling: `:2981-3020`.

### 2.5 Datapoints derived from the sources

1. LDK explicitly carries `payment_hash` as the onion HMAC associated data
   (BOLT 2 `:2864-2874`); Lean's `openLayer` takes an arbitrary `tag` and has
   no associated-data parameter.
2. LDK distinguishes `InvalidOnionVersion`, `InvalidOnionHMAC`,
   `InvalidOnionKey`, `InvalidOnionPayload`, and `InvalidOnionBlinding`; Lean
   `ErrorCode` collapses these into `invalidOnion`, `invalidOnionHmac`, and
   `invalidOnionKey`, with no separate payload/blinding constructors.
3. LDK's `UpdateAddHTLC` has a `blinding_point` option; Lean's message record
   does not. BOLT 2 requires `path_key` when relaying inside a blinded route
   (`02-peer-protocol.md:2834-2844`).
4. LDK's public `onion_fields` handling rejects unknown even TLVs as
   `InvalidOnionPayload` (`event.rs:992-1001`); Lean's `Wire.TLV` has no
   unknown-even policy (`LnLean/Wire/TLV.lean:19-27`).
5. LDK's failure-reason enum is the 24-code BOLT table plus local extensions;
   Lean's `ErrorCode` is a 14-constructor local taxonomy.
6. The server's forwarded-payment adapter exposes no failure code, so an API
   observer cannot reconstruct BOLT 4 failure behavior from LDK Server.
7. LDK Server's offer decoder exposes only `num_hops` for a blinded path, not
   the individual blinded hops. BOLT 4's wire record is richer, and Lean's
   `exposedWire` also omits `num_hops` and `enclen`.
8. rust-lightning's `OnionPacket.public_key` is a `Result` so malformed keys
   still fail with a protocol error; Lean treats the key as always present and
   never fails.
9. rust-lightning's `peel_payment_onion` returns a typed `InboundHTLCErr`;
   Lean's `peel` returns an `Option` that is always `some` and cannot represent
   a BOLT 4 processing failure.
10. BOLT 4's return packet is at least 292 bytes with the recommended 256-byte
    padded message; Lean's 290-byte model omits `pad_len` and reverses the
    HMAC/header order.

## 3. Gap matrix

Statuses use the lane vocabulary: **covered faithfully**, **partially
covered**, **missing**, **contradicted** (with a witness), and
**unmodelled/external**. A missing behavior is not automatically a false
theorem; it is a fidelity/completeness gap for any claim that cites the onion
model as BOLT 4 conformance.

| Behavior | Lean status | LDK / BOLT evidence | Gap / counterexample | Priority |
|---|---|---|---|---|
| Fixed 1366-byte packet size | covered faithfully for the constant only | BOLT 4 `:138-163`; `Onion.lean:83-101`; `OnionProps.lean:450-458` | `wireSize` is always 1366, but it ignores `hop_payloads` contents, ciphertext, and filler. No theorem serialises a real packet. | P2 |
| Version must be 0 and is checked by the reader | missing | BOLT 4 `:163`, `:918-920`; rust-lightning `msgs.rs:2741-2756` | `version : Nat`; `peel` and `openLayer` never inspect it. A packet with `version = 99` still peels/open-checks. | **P0** |
| Public key must be a valid secp256k1 point | missing | BOLT 4 `:921-922`; rust-lightning `msgs.rs:2741-2756` (`Result<PublicKey, _>`) | `PubKey.Valid` only checks 33 bytes (`Core.lean:166`); no point validation or invalid-key failure path. | **P0** |
| Hop payload TLV types 2/4/6/8/10/12/16/18 | missing | BOLT 4 `:189-219`; LDK custom-TLV surface `spontaneous.rs:95-107`; `event.rs:1175-1177` | `OnionHop` has four semantic fields and no TLV stream. `Wire.TLV` is generic and has no hop-payload schema. | **P0** |
| Payload length must be at least 2; BigSize truncation rejected | missing | BOLT 4 `:187`, `:944-950`; `Wire/BigSize.lean:200-215` | `sealLayers` uses opaque `ByteArray` layers; no per-layer BigSize length or truncation check. | P1 |
| Per-hop `amt_to_forward` is fee-adjusted downstream | contradicted as a construction claim | BOLT 4 `:224-230`; `OnionProps.lean:109-116`, `:132-136` | `sealRoute` uses `r.amountMsat` for every hop. Any route with a nonzero fee is a counterexample to reading the sealed payload as BOLT 4 amounts. | **P0** |
| Per-hop payload carries absolute `outgoing_cltv_value` | contradicted/partially covered | BOLT 4 `:198-200`, `:232-240`; `Onion.lean:122-127` | `OnionHop.cltvDelta` is a delta, not an absolute expiry. `Route.cltvAt` exists but is not connected to onion construction. | **P0** |
| HMAC is computed as `HMAC(mu, hop_payloads || associated_data)` | partially covered; raw peel contradicted | BOLT 4 `:935-940`; BOLT 2 `:2864-2874`; `Onion.lean:297-312` | `openLayer` uses an arbitrary `verifyHmac tag l.hmac`; no key derivation, associated data, or constant-time comparison. Raw `peel` bypasses even that (`D25:232-241`). | **P0** |
| A previously received onion HMAC is rejected for a payment | missing | BOLT 4 `:923-928` | No replay set or seen-HMAC state. The same layer can be opened repeatedly. | P1 |
| Final node is detected by all-zero `next_hmac` | contradicted as a correspondence claim | BOLT 4 `:951-963`; `Onion.lean:245-251`, `:488-515` | The model detects finality by `layers = []`. Every non-empty layer peels forward (`peel_cons`), regardless of any `next_hmac` value; the model has no `next_hmac` field. | **P0** |
| Forwarding checks: next channel, fee, expiry, current height | missing | BOLT 4 `:315-344`; rust-lightning `onion_payment.rs:505-590` | `peel` returns a hop without checking incoming amount/CLTV against the payload, channel existence, or expiry bounds. | **P0** |
| Final checks: amount/CLTV, `total_msat`, payment secret | partially covered outside the onion; missing inside | BOLT 4 `:329-344`, `:1528-1556`; `F13.lean:76-101`; `F13.lean:229-250` | `FinalPayload` and `accepted_secret_eq` are disconnected from `peel`. `unconstrained_accept_not_match` shows unconstrained acceptance does not imply matching. | **P0** |
| `payment_data` type 8 with secret + total | missing in onion model | BOLT 4 `:204-207`; `F13.lean:76-85` | The fields exist only in `FinalPayload`; there is no TLV decoder or bridge theorem. | P1 |
| `payment_metadata` type 16 | missing | BOLT 4 `:214-216`, `:300-307`; LDK public custom records | No `OnionHop` field. The writer requirement to include it on every final HTLC is not modelled. | P1 |
| `encrypted_recipient_data` type 10 | missing as data; no decryption | BOLT 4 `:208-210`, `:248-344`; `RouteBlindingProps` caveats `:84-119` | `BlindedHop.encryptedRecipientData` is a creator-side byte blob; no `OnionHop` field, no decryption, no allowed-features/constraint checks. | P1 |
| `current_path_key` type 12 and `path_key` type 0 | missing | BOLT 4 `:211-213`, `:270-318`; BOLT 2 `:2783-2796`, `:2834-2874`; rust-lightning `msgs.rs:738-760` | `UpdateAddHtlc` has no `path_key`; `OnionHop` has no `current_path_key`; no rule rejects both/neither or returns `invalid_onion_blinding`. | **P0** |
| `total_amount_msat` type 18 and MPP final checks | missing | BOLT 4 `:217-219`, `:339-344`, `:350-430`; `LN-PM-004/005` | No field in `OnionHop`; MPP theorems operate on payment state, not on a decoded payload. | P1 |
| Unknown even TLVs are rejected; unknown odd ignored | missing at onion layer | BOLT 4 `:246-344`; LDK `event.rs:992-1001`; `Wire/TLV.lean:19-27` | `Wire.TLV` explicitly does not model known-type/even-odd policy. `decodeHopPayload` does not exist. | **P0** |
| Blinded path wire record (`sciddir_or_pubkey`, `num_hops`, `enclen`) | partially covered / no catalog row | BOLT 4 `:442-455`; `RouteBlindingProps.lean:437-487`; LDK Server `decode_offer.rs:73-105` | `exposedWire` lacks `num_hops`, `enclen`, and the `sciddir_or_pubkey` introduction sum type. It is not a wire encoding. | P1 |
| Route-blinding ECDH/tweak/AEAD | unmodelled/external | BOLT 4 `:497-545`; `RouteBlindingProps.lean:84-119`; assumptions C5-C7 | No blinding function, `rho_i`, `path_key` chain, or ChaCha20-Poly1305. Structural non-interference is not computational unlinkability. | P1 (external) |
| Return packet exact layout | contradicted as a BOLT 4 encoding | BOLT 4 `:1059-1069`; `Onion.lean:450-456`; `OnionProps.lean:477-493`; `OnionError.lean:199-206` | Model is `failure_len || padded-msg || hmac` and 290 bytes; BOLT 4 is `hmac || failure_len || failuremsg || pad_len || pad` and at least 292. The 2-byte gap is mechanized. | **P0** |
| `failure_len + pad_len >= 256`, `pad_len`, 32768 limit | partially covered / wrong shape | BOLT 4 `:1136-1143`, `:1039-1052`; `OnionProps.lean:495-507` | The model only proves its own 290-byte arithmetic and a bound for data <= 256. It does not encode `pad_len`, the lower bound, or truncation of oversized return packets. | P1 |
| BOLT 4 failure-code table and typed data | missing/contradicted as taxonomy | BOLT 4 `:1257-1450`; `Core.lean:246-261`; rust-lightning `onion_utils.rs:1639-1795` | Missing codes include `temporary_node_failure`, `permanent_node_failure`, `required_node_feature_missing`, `invalid_onion_version`, `invalid_onion_hmac`, `invalid_onion_key`, `temporary_channel_failure`, `permanent_channel_failure`, `required_channel_feature_missing`, `unknown_next_peer`, `amount_below_minimum`, `fee_insufficient`, `incorrect_cltv_expiry`, `expiry_too_soon`, `incorrect_or_unknown_payment_details`, `final_incorrect_cltv_expiry`, `final_incorrect_htlc_amount`, `channel_disabled`, `expiry_too_far`, `invalid_onion_payload`, `mpp_timeout`, `invalid_onion_blinding`, and the tied code-2/15/18/19/22 data. Existing `protocol`/`funding`/`update`/`internal` are not BOLT 4 codes. | **P0** |
| Return-path origin processing (PERM/NODE/UPDATE, extra bytes) | missing | BOLT 4 `:1575-1606`; LDK `main.rs:930-954` only exposes high-level reasons | No `failuremsg` parser, no flag classification, no per-hop attribution, no retry/policy behavior. | P1 |
| `update_fail_malformed_htlc` | missing | BOLT 2 `:2942-2970`; rust-lightning `msgs.rs:879-891` | `Msg` has no constructor; `UpdateFailHtlc.reason` is opaque. | P1 |
| Payment-secret / invoice binding at final peel | partially covered outside the onion | BOLT 4 `:339-344`, `:1528-1545`; `F13.lean:76-122`, `:229-250` | `FinalPayloadAcceptedFor` is a hypothesis and `FinalPayload` is never produced by `peel`. The unconditional counterexample remains. | P1 |
| Onion privacy/unlinkability, ciphertext confidentiality | unmodelled/external | BOLT 4 `:907-963`, `:497-545`; module caveats `Onion.lean:58-78`, `RouteBlindingProps.lean:84-119` | No ECDH/HKDF/ChaCha20-Poly1305 or computational privacy proof. Do not claim these from the skeleton. | P2 |

## 4. Proposed targets

The targets below are **statement shapes for wave-14 scoping**, not claims that
they compile as written. Each is classified as **model extension** (new
records/relations/TLV code in Lean) or **external assumption** (a
cryptographic, chain-height, or transport fact supplied as a hypothesis). No
target is proof-only in the sense of deriving the missing BOLT 4 semantics from
the current skeleton.

### T1 — `LnLean.Proofs.Routing.OnionTargets.checkedPeel_contract`

**Priority:** P0. **Classification:** model extension. **Fidelity risk:**
medium (the abstract crypto boundary must stay explicit). **Feasibility:**
medium; it changes `OnionPacket`/`OnionLayer` and every existing onion proof.

**Statement shape:**

```lean
structure PeelContext where
  associatedData : ByteArray
  pathKey : Option PubKey
  seenHmacs : List ByteArray

structure OnionLayer where
  -- existing fields plus the BOLT 4 next_hmac extracted from hop_payloads
  hop : OnionHop
  ciphertext : ByteArray
  nextHmac : ByteArray

inductive PeelOutcome
  | forward (hop : OnionHop) (next : OnionPacket)
  | final (payload : HopPayload)
  | fail (code : Bolt4FailureCode)

def checkedPeel (I : OnionInterface) (ctx : PeelContext)
    (p : OnionPacket) : PeelOutcome := ...

theorem checkedPeel_forward_sound
    {I : OnionInterface} {ctx : PeelContext} {p : OnionPacket}
    {hop : OnionHop} {next : OnionPacket}
    (h : checkedPeel I ctx p = .forward hop next) :
    p.version = 0 ∧ p.ephemeralKey.Valid ∧
    I.verifyHmac (hmacKey ctx) (hopPayloads p ++ ctx.associatedData) p.hmac = true ∧
    next.nextHmac ≠ allZero 32 ∧
    p.hmac ∉ ctx.seenHmacs
```

**Hypotheses:** `pathKey`, `associatedData`, and `seenHmacs` are explicit
context fields; the replay check takes BOLT 4's abort branch (preimage unknown);
`p.version` is the packet's BOLT 4 version field; `hmacKey` is
derived through the abstract C5/C6/C8 interface, not assumed to be SHA-256;
`p.ephemeralKey.Valid` means a real
secp256k1 point check, not the current 33-byte size check; `next.nextHmac` is
extracted from the unwrapped layer; `HopPayload` is T2's decoded payload.

**Non-vacuity witness:** a two-layer packet with version 0, a valid point, an
`hmac` not in `seenHmacs`, and a nonzero `nextHmac` returns `.forward`.
**Negative witnesses:** version 99 returns `.fail .invalidOnionVersion`; an
invalid point returns `.fail .invalidOnionKey`; an `hmac` already in
`seenHmacs` returns `.fail` (the BOLT 4 replay check); an all-zero `nextHmac`
returns `.final`; a rejected HMAC returns `.fail .invalidOnionHmac`.

**Why faithful:** BOLT 4 requires exactly these reader checks
(`:918-963`), and BOLT 2 requires `payment_hash` as associated data
(`:2864-2874`). The target does not prove forgery resistance; it makes the
cryptographic premise a named interface and proves the structural contract.

**Preservation:** keep `peel_deterministic` and `waveD_d25_peel_bypasses_hmac`
visible. Do not replace the old `peel` with `checkedPeel` and delete the raw
counterexample; the old result should remain as a documented structural
relation.

### T2 — `LnLean.Proofs.Routing.OnionTargets.hopPayload_tlv_sound`

**Priority:** P0. **Classification:** model extension (new TLV schema and
decoder). **Fidelity risk:** medium (unknown-even policy and final-only fields
must be exact). **Feasibility:** medium; `Wire.TLV` and `Wire.BigSize` provide
most of the encoding machinery.

**Statement shape:**

```lean
structure HopPayload where
  amtToForward : Option Msat
  outgoingCltvValue : Option Nat
  shortChannelId : Option ShortChannelId
  paymentData : Option (PaymentSecret × Msat)
  encryptedRecipientData : Option ByteArray
  currentPathKey : Option PubKey
  paymentMetadata : Option ByteArray
  totalAmountMsat : Option Msat

def decodeHopPayload (b : ByteArray) : Option HopPayload := ...
def encodeHopPayload (p : HopPayload) : ByteArray := ...

theorem hopPayload_tlv_sound {b : ByteArray} {p : HopPayload}
    (h : decodeHopPayload b = some p) :
    noUnknownEven (decodeTLV b) ∧
    (p.isForward → p.amtToForward.isSome ∧ p.outgoingCltvValue.isSome ∧
      p.shortChannelId.isSome ∧ p.paymentData.isNone) ∧
    (p.isFinal → p.shortChannelId.isNone ∧ p.amtToForward.isSome ∧
      p.outgoingCltvValue.isSome ∧ p.totalAmountMsat.isSome) ∧
    payloadLengthAtLeastTwo b

theorem hopPayload_roundtrip (p : HopPayload) (h : p.WellFormed) :
    decodeHopPayload (encodeHopPayload p) = some p
```

**Hypotheses:** the stream is canonical and sorted (`TLVStream.WellFormed`);
the known-type map is exactly types 2, 4, 6, 8, 10, 12, 16, 18; unknown even
types are rejected and unknown odd types are ignored; `payment_data` is
final-only; `encrypted_recipient_data`/`current_path_key` follow the blinding
rules; field widths are BOLT 4 `tu64`/`tu32`/`point`/`32*byte`.

**Non-vacuity witness:** encode a final payload with `amt_to_forward`,
`outgoing_cltv_value`, `payment_data`, and `total_amount_msat`; decode it back.
**Negative witnesses:** an unknown even type decodes to `none`; an intermediate
payload containing `payment_data` decodes to `none`; type 2 with a three-byte
value decodes to `none`; a length 0/1 prefix decodes to `none`.

**Why faithful:** this is the exact BOLT 4 payload schema and the writer/reader
requirements (`:189-344`). It reuses `Wire.BigSize` and `Wire.TLV` rather than
inventing a second encoding. It preserves the existing generic TLV laws and
does not claim that `encrypted_recipient_data` is decryptable.

### T3 — `LnLean.Proofs.Routing.OnionTargets.failureCode_wire_table`

**Priority:** P1. **Classification:** model extension. **Fidelity risk:** low
(the table is static and spec-pinned). **Feasibility:** high.

**Statement shape:**

```lean
inductive Bolt4FailureCode
  | temporaryNodeFailure | permanentNodeFailure | requiredNodeFeatureMissing
  | invalidOnionVersion | invalidOnionHmac | invalidOnionKey
  | temporaryChannelFailure | permanentChannelFailure
  | requiredChannelFeatureMissing | unknownNextPeer
  | amountBelowMinimum | feeInsufficient | incorrectCltvExpiry
  | expiryTooSoon | incorrectOrUnknownPaymentDetails
  | finalIncorrectCltvExpiry | finalIncorrectHtlcAmount
  | channelDisabled | expiryTooFar | invalidOnionPayload
  | mppTimeout | invalidOnionBlinding

def Bolt4FailureCode.toNat : Bolt4FailureCode → Nat := ...
def Bolt4FailureCode.flags : Bolt4FailureCode → FailureFlags := ...

theorem failureCode_wire_table :
    (Bolt4FailureCode.temporaryNodeFailure.toNat = 0x2002) ∧
    (Bolt4FailureCode.permanentNodeFailure.toNat = 0x4002) ∧
    ... ∧
    (Bolt4FailureCode.invalidOnionBlinding.toNat = 0x8000 ||| 0x4000 ||| 24)
```

**Hypotheses:** numeric values are the BOLT 4 constants, including flag bits
`0x8000 BADONION`, `0x4000 PERM`, `0x2000 NODE`, `0x1000 UPDATE`; each code's
data layout is a typed record, not an opaque `ByteArray`.

**Non-vacuity witness:** all 22 named BOLT 4 codes plus the historical aliases
(`incorrect_payment_amount` = PERM|16, `final_expiry_too_soon` = 17) are
inhabited and map to distinct tuples where the spec assigns distinct values.
**Negative witness:** an unknown code decodes to an explicit `unknown` result,
not to `invalidOnion` or `internal`; `ErrorCode.protocol` cannot be assigned a
BOLT 4 numeric value.

**Why faithful:** BOLT 4 names the flags and all codes at `:1273-1450`; LDK's
`LocalHTLCFailureReason` mirrors them (`onion_utils.rs:1639-1795`). This target
does not model retry policy; it only makes the code table and data layout
sound.

### T4 — `LnLean.Proofs.Routing.OnionTargets.failureReturnPacket_roundtrip`

**Priority:** P1. **Classification:** model extension + external assumption
(return-path keys/obfuscation). **Fidelity risk:** medium. **Feasibility:**
medium; it needs a new byte-level encoder and decoder, but no new crypto proof.

**Statement shape:**

```lean
structure FailureReturn where
  hmac : ByteArray        -- 32 bytes
  failureMsg : ByteArray
  pad : ByteArray

def encodeFailureReturn (r : FailureReturn) : ByteArray :=
  r.hmac ++ u16be r.failureMsg.size ++ r.failureMsg ++
  u16be r.pad.size ++ r.pad

theorem failureReturnPacket_length {r : FailureReturn}
    (hpad : 256 ≤ r.failureMsg.size + r.pad.size) :
    (encodeFailureReturn r).size ≥ 292 ∧
      (encodeFailureReturn r).size ≤ 32768

theorem failureReturnPacket_roundtrip (r : FailureReturn)
    (hpad : 256 ≤ r.failureMsg.size + r.pad.size)
    (hlen : r.failureMsg.size < 65536 ∧ r.pad.size < 65536) :
    decodeFailureReturn (encodeFailureReturn r) = some r
```

**Hypotheses:** `failure_len` and `pad_len` are `u16`; `failure_len + pad_len
>= 256`; the total is at most 32768; HMAC authenticity is the C8 hypothesis,
not a proved property; obfuscation/decryption is outside the codec.

**Non-vacuity witness:** a failure message of 4 bytes plus 252 bytes of pad
gives exactly 292 bytes; a 256-byte failure message plus zero pad also gives
292. **Negative witness:** a 100-byte message plus 100-byte pad is rejected
(< 256); a 32765-byte total with a 40-byte header exceeds the limit.

**Why faithful:** the field order and constraints are exactly BOLT 4
`:1059-1069`, `:1136-1143`; the 32768 limit is `:1039-1052`. The target
corrects the model's 290-byte/`pad_len`-free story without pretending to prove
return-path confidentiality.

### T5 — `LnLean.Proofs.Routing.OnionTargets.blindedPath_wire_roundtrip`

**Priority:** P1/P2. **Classification:** model extension. **Fidelity risk:**
medium (introduction sum type and length encoding). **Feasibility:**
medium-high; it is a fixed wire record plus generic BigSize/serialisation laws.

**Statement shape:**

```lean
inductive IntroductionNode
  | nodeId (p : PubKey)
  | directedScid (dir : Direction) (scid : ShortChannelId)

structure BlindedPathWire where
  firstNodeId : IntroductionNode
  firstPathKey : PubKey
  hops : List BlindedPathHop

structure BlindedPathHop where
  blindedNodeId : PubKey
  encryptedRecipientData : ByteArray

def encodeBlindedPath (b : BlindedPathWire) : ByteArray :=
  encodeIntroduction b.firstNodeId ++ b.firstPathKey.bytes ++
  [b.hops.length.toUInt8] ++ b.hops.map encodeBlindedHop |>.flatten

theorem blindedPath_wire_roundtrip (b : BlindedPathWire)
    (hlen : b.hops.length ≤ 255)
    (henc : ∀ h ∈ b.hops, h.encryptedRecipientData.size ≤ 65535) :
    decodeBlindedPath (encodeBlindedPath b) = some b
```

**Hypotheses:** `num_hops` is one byte, `enclen` is `u16`, point fields are
33-byte compressed keys, and `sciddir_or_pubkey` is a two-constructor sum type;
`encrypted_recipient_data` content is opaque and its decryption remains T6/
external.

**Non-vacuity witness:** one-hop path with a `NodeId` introduction and one
32-byte encrypted blob; one-hop path with a directed-SCID introduction and a
64KiB blob boundary. **Negative witnesses:** 256 hops is not encodable in
`num_hops`; a 65536-byte `enclen` is rejected; a 32-byte point is rejected.

**Why faithful:** the record layout is BOLT 4 `:442-455`. It repairs the
current `exposedWire` omission of `num_hops` and `enclen` and models the
introduction selector as a sum type. It explicitly does not claim
unlinkability or decryptability; those stay external.

### T6 — `LnLean.Proofs.Routing.OnionTargets.pathKey_binding`

**Priority:** P1. **Classification:** model extension. **Fidelity risk:**
medium. **Feasibility:** high once T1/T2/T5 exist.

**Statement shape:**

```lean
structure AddHtlcContext where
  updateAddPathKey : Option PubKey
  payloadCurrentPathKey : Option PubKey
  isFinal : Bool

def pathKeyConflict (c : AddHtlcContext) : Prop :=
  (c.updateAddPathKey.isSome ∧ c.payloadCurrentPathKey.isSome) ∨
  (c.updateAddPathKey.isNone ∧ c.payloadCurrentPathKey.isNone ∧ ¬ c.isFinal)

theorem pathKey_conflict_rejected {c : AddHtlcContext}
    (h : pathKeyConflict c) :
    processAddHtlc c = .fail .invalidOnionBlinding

theorem pathKey_forward_uses_current_path_key
    {c : AddHtlcContext} {next : OnionPacket}
    (hnf : ¬ c.isFinal)
    (h : processAddHtlc c = .forward next) :
    next.pathKey = c.payloadCurrentPathKey
```

**Hypotheses:** the type-0 `path_key` comes from `update_add_htlc`; type-12
`current_path_key` comes from the decrypted payload; a forwarding node must
not receive both; a final node may receive `current_path_key`; all local or
downstream errors on a blinded path become `invalid_onion_blinding`.

**Non-vacuity witness:** a forwarding hop with `path_key = none` and a payload
`current_path_key = some k` derives the next key from `k`; a non-blinded
forwarding hop with both absent is accepted. **Negative witnesses:** both
present; both absent on a non-final hop; a `path_key`-bearing HTLC that
produces a local error returns `invalid_onion_blinding`.

**Why faithful:** BOLT 4 `:270-318` and `:1452-1482`; BOLT 2
`:2834-2874`, `:2981-3020`; rust-lightning `msgs.rs:738-760`. This target makes
explicit the rule that currently has no Lean representation at all.

### T7 — `LnLean.Proofs.Routing.OnionTargets.finalPeel_bridges_FinalPayload`

**Priority:** P1. **Classification:** model extension/refinement (bridge from
decoded onion to `F13.FinalPayload`) + external invoice data. **Fidelity
risk:** low-medium (the bridge must not assume acceptance). **Feasibility:**
high, because `F13` already supplies the admission predicate and witnesses.

**Statement shape:**

```lean
structure DecodedFinal where
  amountMsat : Msat
  cltvValue : Nat
  totalMsat : Msat
  paymentSecret : PaymentSecret

def toFinalPayload (f : DecodedFinal) : F13.FinalPayload := ...

theorem finalPeel_bridges_FinalPayload
    {p : OnionPacket} {f : DecodedFinal} {i : Invoice}
    (hpeel : checkedPeel I ctx p = .final f)
    (hacc : F13.FinalPayloadAcceptedFor (toFinalPayload f) i) :
    (toFinalPayload f).paymentSecret = i.paymentSecret ∧
      (toFinalPayload f).amtToForward = f.amountMsat
```

**Hypotheses:** T1 yields a final decoded payload; T2 has already checked that
the final-only fields are present; `FinalPayloadAcceptedFor` is supplied by
the final node's invoice/session policy. The bridge does not assume
`payment_secret` equality as a definitional consequence of the payload shape.

**Non-vacuity witness:** `FinalPayload.forInvoice` plus a final payload carrying
the invoice's secret satisfies the bridge; `F13.accepted_secret_eq` composes.
**Negative witness:** `F13.unconstrained_accept_not_match` remains true, and a
payload with a different secret is rejected by `FinalPayloadAcceptedFor`.

**Why faithful:** BOLT 4 requires final-node secret matching and amount/CLTV
checks (`:339-344`, `:1528-1545`); `F13` already models the secret half
(`:76-101`). This target connects the existing islands; it does not make
`LN-PM-003` unconditional.

## 5. Assumptions, counterexamples, and non-vacuity risks

### 5.1 Counterexamples that must remain visible

| Witness | Location | Why it matters |
|---|---|---|
| `waveD_d25_peel_bypasses_hmac` | `LnLean/Proofs/WaveD/D25.lean:232-241` | Shows raw `peel` forwards under an always-rejecting verifier while `openLayer` rejects. Any new checked-peel target must preserve this as a counterexample against the raw relation. |
| `peel_cons` | `LnLean/Routing/Onion.lean:258-261` | Shows every non-empty layer list peels forward, independent of HMAC, version, or key. This is the concrete gap between the model's finality test and BOLT 4's all-zero `next_hmac`. |
| `sealRoute` amount flattening | `LnLean/Proofs/Routing/OnionProps.lean:132-136` | A route with nonzero hop fees gets the same `amountMsat` at every layer, contradicting BOLT 4's fee-adjusted `amt_to_forward`. Do not cite `sealRoute` as payload construction without a new target. |
| `bolt4FailurePacketSize_eq_model_add_two` | `LnLean/Proofs/Routing/OnionProps.lean:486-493` | Mechanizes the 2-byte `pad_len` omission. A proposal that relabels the 290-byte model as BOLT 4 must not delete this theorem. |
| `unconstrained_accept_not_match` / `two_accepted_payloads_distinct_secrets` | `LnLean/Proofs/ModelHardening/F13.lean:229-250` | Keeps the unconstrained final-payload counterexample alive; T7 must require `FinalPayloadAcceptedFor`, not assume it. |
| `exposed_realNode_irrelevant` / `exposed_terms_irrelevant` | `LnLean/Proofs/Routing/RouteBlindingProps.lean:453-466` | Preserve the structural non-interference witnesses while adding `num_hops`/`enclen`; do not claim they prove BOLT 4 confidentiality. |
| `ofEdge_rounding_counterexample` | `RouteBlindingProps.lean:392-401` | Preserve the route fee/rounding counterexample; a T5 wire target must not quietly assume exact fee composition. |

### 5.2 Assumptions that must stay explicit

1. **ECDH, HKDF, ChaCha20-Poly1305, and HMAC.** C5-C8 remain named
   assumptions. `OnionInterface.verifyHmac` is not HMAC-SHA256, and
   `OnionInterface.hmacBinding` is a `Prop`, not an axiom
   (`Onion.lean:294-301`). T1/T4/T6 must keep these as hypotheses. No target in
   this report proves onion confidentiality, unforgeability, or
   unlinkability.
2. **Valid secp256k1 points.** BOLT 4 requires a valid `public_key` and errors
   on an invalid one (`04-onion-routing.md:921-922`). The current
   `PubKey.Valid` is only a 33-byte size check (`Core.lean:166`). A target that
   uses `PubKey.Valid` without a real curve check would hide an external
   assumption.
3. **Associated data.** BOLT 2 requires `payment_hash` as associated data
   (`02-peer-protocol.md:2864-2874`). Any `checkedPeel` without an
   `associatedData` parameter is not a BOLT 4 payment-onion contract.
4. **Current block height.** Final CLTV checks use `current_block_height`
   (`04-onion-routing.md:339-344`). T1/T2 must take a height or an explicit
   `ChainView`; they must not assume the height is correct or fresh.
5. **Return-path keys and obfuscation.** The `um`/`ammag` return keys are
   derived from the forward shared secret (`:1054-1077`). T4 can prove the
   codec and length laws without deriving those keys; it cannot claim return
   confidentiality or origin attribution.
6. **Unknown even/odd TLV policy.** BOLT 4 and LDK reject unknown even types
   (`:246-344`; `event.rs:992-1001`). `Wire.TLV` explicitly leaves this
   unmodelled (`Wire/TLV.lean:19-27`). T2 must add the policy, not assume the
   generic parser enforces it.
7. **Invoice/session policy.** A`, F13.FinalPayloadAcceptedFor` is the
   admission rule, not a consequence of the payload bytes. T7 must keep it as
   a hypothesis and preserve `F13`'s counterexample.
8. **Route construction and channel state.** The onion model has no channel
   graph, liquidity, fee policy, or `htlc_minimum_msat`/`max_htlc_value`
   state. Forwarding checks in T1/T6 can be stated only relative to an
   explicit channel view.

### 5.3 Claims that must not be strengthened or hidden

* Do **not** delete or rename `waveD_d25_peel_bypasses_hmac` to make a new
  `checkedPeel` look unconditional. Keep the raw `peel` as a documented
  structural relation and prove the counterexample against it.
* Do **not** define `checkedPeel` so that its success constructor carries the
  conclusion (`version = 0`, HMAC accepted, `nextHmac ≠ 0`) as a field without
  proving those facts from the packet and context. That would make the target
  vacuous.
* Do **not** define `HopPayload` with `paymentData` always present or
  `shortChannelId` always present. BOLT 4 requires final/forward asymmetry;
  the negative witnesses in T2 must remain inhabitable.
* Do **not** make `pathKeyConflict` false by construction (for example by
  setting one option to `none` in the record constructor). T6 must include
  both conflict witnesses.
* Do **not** call the 290-byte model "292 bytes" or "BOLT 4 exact". Keep
  `bolt4FailurePacketSize_eq_model_add_two`; state the exact layout and the
  `failure_len + pad_len >= 256` lower bound.
* Do **not** map the 14 `ErrorCode` constructors onto BOLT 4 numbers by
  convention. `protocol`, `funding`, `update`, and `internal` have no BOLT 4
  numeric values and must not be silently assigned one.
* Do **not** infer `LN-PM-003` unconditionally from T7. The bridge remains
  conditional on `FinalPayloadAcceptedFor`; `F13` already records the
  refutation of the unconditional reading.
* Do **not** strengthen `LN-RT-003`/`LN-RT-004` catalog prose to say
  "BOLT 4 decryption" or "BOLT 4 HMAC verification". Their current scope is
  structural peel / abstract checked rejection, and that scope must be visible
  in any catalog update.

### 5.4 Non-vacuity plan for the new targets

Each target needs at least one positive and one negative witness:

* **T1:** positive two-hop forward and one-hop final; negative wrong version,
  invalid key, replay, bad HMAC, and malformed payload.
* **T2:** positive final payload with `payment_data`/`total_amount_msat`;
  positive forward payload without `payment_data`; negative unknown even,
  duplicate type, wrong width, missing required field, and forward
  `payment_data`.
* **T3:** positive each code's numeric value and typed data; negative unknown
  code and malformed data length.
* **T4:** positive 292-byte minimal packet and 32768-byte boundary; negative
  under-256 pad and over-32768 total.
* **T5:** positive node-id and directed-SCID introductions; negative 256 hops,
  `enclen` overflow, and short point.
* **T6:** positive forward with one path key and final with
  `current_path_key`; negative both/neither and blinded local error.
* **T7:** positive `FinalPayload.forInvoice`; negative mismatched secret
  retained by the `F13` counterexample.

## 6. Wave-13 recommendation

**Recommendation: do not implement BOLT 4 conformance in wave 13. Defer to a
wave-14 model-extension lane after maintainer design approval; treat the
cryptographic onion and blinding internals as an explicit external/human
barrier.**

Reasons:

1. **The current catalog claims are true only at skeleton scope.** `LN-RT-003`
   is a branch law over a layer list, and `LN-RT-004` is an abstract checked
   rejection law. `LN-CR-003` is a conditional HMAC contract. None of them
   can be upgraded to BOLT 4 wire conformance by proof work alone; they need
   new packet/payload/error records.
2. **The highest-value gaps are model extensions, not proofs.** Version/key
   validation, payload TLVs, absolute CLTV, fee-adjusted amounts, failure
   codes, `pad_len`, `path_key`, and blinded-path fields are absent from the
   types. Adding them changes `OnionPacket`, `OnionLayer`, `OnionHop`,
   `UpdateAddHtlc`, `UpdateFailHtlc`, `Msg`, and `ErrorCode`.
3. **Cryptography is not a Lean proof obligation available here.** ECDH, HKDF,
   ChaCha20-Poly1305, HMAC-SHA256, and secp256k1 point validity are external
   assumptions C5-C8. A wave-13 implementation that tried to close them would
   either add axioms or hide them in an opaque interface, which the existing
   model deliberately avoids (`Onion.lean:294-301`,
   `RouteBlindingProps.lean:84-119`).
4. **The LDK public surface is too thin to serve as a conformance oracle.**
   LDK Node exposes custom TLVs, payment secrets, and high-level payment
   failures; LDK Server exposes forwarded amounts and blinded-path metadata.
   Neither exposes the per-hop payload, failure bytes, or `path_key` state.
   The report therefore uses BOLT 4/2 as the primary behavior source and
   rust-lightning only as a caveated implementation anchor.

**If the parent authorizes one wave-14 implementation target, choose T1
(`checkedPeel_contract`).** It is the narrowest change that makes
`LN-RT-003`/`LN-RT-004` honest: it adds the missing version/key/replay/
associated-data/all-zero-`next_hmac` contract while keeping C8 explicit and
preserving the raw-peel counterexample. T2 (`hopPayload_tlv_sound`) is the
necessary companion: T1 cannot be meaningful without a decoded payload.
T3/T5 are low-risk static-table/wire-record targets. T4/T6/T7 should follow
only after T1/T2 and after the parent decides how much return-path and invoice
policy belongs in the model.

Suggested sequence, if model work is authorized:

* **Step 0 (human/design review):** approve the record changes and the
  `checkedPeel` abstraction boundary. No proofs merge before this.
* **Step 1 (P0):** T1 plus T2. Add the checked peel contract and the payload
  TLV schema; retain all existing skeleton theorems as legacy/structural
  results.
* **Step 2 (P1):** T3 and T5. Add the static failure-code table and the exact
  blinded-path wire record; do not add crypto proofs.
* **Step 3 (P1):** T4 and T6. Add the return-packet codec and path-key rules;
  keep return obfuscation and key derivation as explicit external hypotheses.
* **Step 4 (P1):** T7. Bridge final peels to `F13.FinalPayload` only through
  `FinalPayloadAcceptedFor`.
* **Step 5:** update catalog scope notes for `LN-RT-003`, `LN-RT-004`, and
  `LN-CR-003`. Do not mark any BOLT 4 conformance row proved until its target
  exists and its non-vacuity witnesses are in the tree.

**External/human barrier (do not schedule as Lean implementation):** Sphinx
key derivation, ECDH, ChaCha20-Poly1305, HMAC forgery resistance, secp256k1
point validation, onion privacy/unlinkability, return-path confidentiality, and
BOLT 4 error-retry policy are cryptographic or operational assumptions. They
must remain named hypotheses or explicit non-goals, not axioms or "proved"
claims.

## 7. Evidence and commands

### 7.1 Pins verified

```sh
git -C /tmp/opencode/ldk-refs/ldk-node rev-parse HEAD
# fa123fed131e27ecc420b77fa7086fcf1ddaebb8
git -C /tmp/opencode/ldk-refs/ldk-server rev-parse HEAD
# c17dc11dde38f88c53457039ddf30c6b90a63ba2
git rev-parse --short HEAD
# f7f0628
```

`ldk-node/Cargo.toml:89-98` pins rust-lightning
`d7a980641c6325ddda5072a0f470ef8392676cf5`. The local
`refs/rust-lightning` tree is `fe4900930c6bd5786ec4203274d7cf312776a5a6`;
all rust-lightning line anchors above therefore carry the caveat stated in
section 2.

### 7.2 Lean commands and files inspected

```sh
rg -n "structure OnionHop|structure OnionPacket|def peel |def openLayer|theorem peel_deterministic|theorem hmac_sound" \
  LnLean/Routing/Onion.lean
rg -n "sealRoute|bolt4FailurePacketSize|recorded_error_bounded" \
  LnLean/Proofs/Routing/OnionProps.lean
rg -n "sealError|parseError|HmacBinding" \
  LnLean/Proofs/PhaseC3/OnionError.lean
rg -n "structure BlindedPath|structure BlindedHop|exposedWire|toRouteUsing" \
  LnLean/Proofs/Routing/RouteBlindingProps.lean
rg -n "structure FinalPayload|FinalPayloadAcceptedFor|UnconstrainedFinalAccept" \
  LnLean/Proofs/ModelHardening/F13.lean
rg -n "structure UpdateAddHtlc|structure UpdateFailHtlc|inductive Msg" \
  LnLean/Protocol/Messages.lean
rg -n "inductive ErrorCode" LnLean/Basic/Core.lean
rg -n "decodeTLV|parseRecord|WellFormed|SortedTypes" \
  LnLean/Wire/TLV.lean
rg -n "def encode|def decode|decodePayload" LnLean/Wire/BigSize.lean
rg -n "peel_bypasses_hmac|samplePacket" LnLean/Proofs/WaveD/D25.lean
rg -n "onion|peel" LnLean/Proofs/WaveE/E24.lean LnLean/Routing/Laws.lean
python3 scripts/check-catalog.py --audit
# rows=51 proved=51 statementOnly=0 targets=294 unresolved=0
# proved_failures=0 duplicate_ids=0 candidates=0 declarations=11898
# OK: every catalog target resolves exactly and every proved row is sorry-free.
```

Files read in full or in relevant sections:

* `docs/AGENT-PROTOCOL.md`, `docs/OPEN-ISSUES.md`, `docs/THEOREM-INDEX.md`,
  `docs/TRACEABILITY.md`, `agents/TODO-REPAIR.md`,
  `agents/reports/swarm12/S12-POST-INTEGRATION-AUDIT.md`,
  `agents/reports/wave13-review/LDK-REFS.md`.
* `LnLean/Routing/Onion.lean`, `LnLean/Routing/Route.lean`,
  `LnLean/Routing/Laws.lean`, `LnLean/Proofs/Routing/OnionProps.lean`,
  `LnLean/Proofs/PhaseC2/OnionLayers.lean`,
  `LnLean/Proofs/PhaseC3/OnionError.lean`,
  `LnLean/Proofs/Routing/RouteBlindingProps.lean`.
* `LnLean/Protocol/Messages.lean`, `LnLean/Basic/Core.lean`,
  `LnLean/Wire/TLV.lean`, `LnLean/Wire/BigSize.lean`,
  `LnLean/Payment/HTLC.lean`, `LnLean/Proofs/ModelHardening/F13.lean`,
  `LnLean/Proofs/PhaseC3/ConformanceVectors.lean`,
  `LnLean/Proofs/ConformanceDiffTargets.lean`,
  `LnLean/Proofs/WaveD/D25.lean`, `LnLean/Proofs/WaveE/E24.lean`,
  `LnLean/Proofs/CryptoTargets.lean`.

### 7.3 LDK and BOLT commands and files inspected

```sh
rg -n "custom_tlvs|payment_secret|PaymentFailureReason|onion_fields|forwarded" \
  /tmp/opencode/ldk-refs/ldk-node/src/payment/spontaneous.rs \
  /tmp/opencode/ldk-refs/ldk-node/src/payment/bolt11.rs \
  /tmp/opencode/ldk-refs/ldk-node/src/event.rs \
  /tmp/opencode/ldk-refs/ldk-node/src/payment/forwarding.rs \
  /tmp/opencode/ldk-refs/ldk-node/src/payment/forwarding_store.rs
rg -n "custom_tlvs|path_key|blinded|forwarded|payment_failure_reason" \
  /tmp/opencode/ldk-refs/ldk-server/ldk-server/src/api \
  /tmp/opencode/ldk-refs/ldk-server/ldk-server/src/util/proto_adapter.rs \
  /tmp/opencode/ldk-refs/ldk-server/ldk-server/src/main.rs
rg -n "OnionV2|OnionV3|NodeCustomMessageHandler|handle_custom_message" \
  /tmp/opencode/ldk-refs/ldk-node/src/connection.rs \
  /tmp/opencode/ldk-refs/ldk-node/src/message_handler.rs
rg -n "OnionPacket|UpdateAddHTLC|UpdateFailHTLC|LocalHTLCFailureReason|peel_payment_onion" \
  refs/rust-lightning/lightning/src/ln/msgs.rs \
  refs/rust-lightning/lightning/src/ln/onion_utils.rs \
  refs/rust-lightning/lightning/src/ln/onion_payment.rs
rg -n "Packet Structure|payload format|Onion Decryption|Route Blinding|Returning Errors|Failure Messages|Receiving Failure Codes" \
  refs/bolts/04-onion-routing.md
rg -n "update_add_htlc|path_key|update_fail_htlc|update_fail_malformed_htlc|associated_data" \
  refs/bolts/02-peer-protocol.md
```

LDK Node files inspected: `src/message_handler.rs`, `src/connection.rs`,
`src/payment/spontaneous.rs`, `src/payment/bolt11.rs`, `src/event.rs`,
`src/payment/forwarding.rs`, `src/payment/forwarding_store.rs`,
`src/payment/asynchronous/static_invoice_store.rs`, `src/ffi/types.rs`,
`Cargo.toml`.

LDK Server files inspected: `ldk-server/src/api/bolt11_send.rs`,
`ldk-server/src/api/spontaneous_send.rs`,
`ldk-server/src/api/get_forwarded_payment_details.rs`,
`ldk-server/src/api/decode_offer.rs`,
`ldk-server/src/api/decode_invoice.rs`,
`ldk-server/src/util/proto_adapter.rs`, `ldk-server/src/main.rs`.

### 7.4 Constraints observed

* No branch switch, creation, rebase, commit, or push.
* No Lean, docs, script, test, vendor, or other lane report edits.
* The only file written by this lane is
  `agents/reports/wave13-review/R09-bolt4-onion.md`.
* No cargo tests and no network access.
* No whole-tree build was run; catalog audit and read-only inspection only.
