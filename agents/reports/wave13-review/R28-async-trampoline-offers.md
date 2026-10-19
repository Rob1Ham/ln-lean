# R28 — Async payments, trampoline, onion messages, and unified BOLT 12
**Status:** read-only review
**Pins:** LDK Node `fa123fed131e27ecc420b77fa7086fcf1ddaebb8`, LDK Server `c17dc11dde38f88c53457039ddf30c6b90a63ba2`

## 1. Scope and current Lean surface

This lane covers the *unified payment* surface (BIP 21 / BOLT 11 / BOLT 12
dispatch), onion-message envelopes and reply paths, async payments over static
invoices, human-readable names (HRN / BIP 353), and the trampoline feature
surface. It is deliberately **not** a second BOLT 12 TLV lane (R11), a second
BOLT 4 HTLC-packet lane (R09), a duplicate-payment-store lane (R12), a routing
lane (R16), or an event-runtime lane (R18).

**Short verdict: there is no Lean model of any of these behaviours.** Searches
over `LnLean/` find no `trampoline`, `async payment`, `bolt12`, `offer`,
`unified`, `onion_message`, `static_invoice`, or `hrn` carrier. The nearest
surfaces are structural and must not be read as protocol coverage:

| Existing carrier | Location | What it actually models |
|---|---|---|
| `OnionPacket`, `OnionHop`, `OnionLayer`, `peel`, `openLayer` | `LnLean/Routing/Onion.lean:122-169`, `:248-251`, `:297-312` | A list of opaque layers with a structural peel and an arbitrary HMAC verifier. This is the BOLT 4 *HTLC* onion skeleton, not `onion_message`. |
| `Onion.peel_deterministic`, `Onion.hmac_sound` | `LnLean/Routing/Onion.lean:498-545` | Peel determinism and checked-HMAC rejection. Raw `peel` intentionally bypasses HMAC; the `D25` counterexample is retained. |
| `BlindedHop`, `BlindedPath`, `toRouteUsing`, `toRealRoute` | `LnLean/Proofs/Routing/RouteBlindingProps.lean:437-487`, `:504-579` | A creator-side structural blinded path with real nodes and plaintext terms; no `num_hops`, ECDH, `path_id`, reply path, or onion-message use. |
| `Invoice` (BOLT 11), `Invoice.Valid`, `Invoice.verify`, `amountSatisfies` | `LnLean/Payment/Invoice.lean:197-207`, `:238-250`, `:252-255`, `:277-282` | BOLT 11 payment fields and the BOLT 4 final-amount rule. `Invoice.lean:98` states "BOLT 12 offers are out of scope." |
| `FeatureVector` and adjacent even/odd pair laws | `LnLean/Proofs/Protocol/FeaturesProps.lean:133-163` | Generic feature-bit semantics. Bit 57 (`option_trampoline_routing`) is not named anywhere. |
| `F16.AsyncSystem`, `AsyncInvariant`, `FairlyScheduled` | `LnLean/Proofs/ModelHardening/F16.lean:75-110`, `:114-173` | A labelled asynchronous transition system and an unfair-schedule safety theorem. This is *scheduling*, not async payments, message queues, or hold/release. |
| `safety_async` | `LnLean/Proofs/ModelHardening/F16.lean` (catalog `LN-SEC-003`) | Safety under arbitrary finite adversarial action lists. It has no payment, invoice, or onion-message state. |

Catalog surface: `docs/THEOREM-INDEX.md` has 51 rows. The only rows that touch
this lane are `LN-RT-003`/`LN-RT-004` (onion peel/HMAC), `LN-PM-001`/`002`/
`003`/`007` (BOLT 11 invoice fields and wire codec), `LN-PR-006` (feature
intersection), and `LN-SEC-003` (async scheduling). There is **no** row for
BOLT 12 offers, unified payments, onion messages, async payments, static
invoices, trampoline, or HRN. The catalog is 51/51 proved and has 294 resolved
targets; this report does not retarget it.

Scope contradiction to preserve: `docs/ANCHORS-GENERATED.md:131` lists
`LnLean/Payment/Invoice.lean` as a BOLT 12 anchor. That line is generated from
the out-of-scope sentence at `Invoice.lean:98`, not from a BOLT 12 theorem.
`docs/SCOPE.md:24` excludes "BOLT 12 offers and blinded paths beyond a stub
interface", and `docs/ASSUMPTIONS.md:144` lists BOLT 12 as future work. Any
proposal that treats the anchor as coverage is false. `docs/OPEN-ISSUES.md`
and `docs/TRACEABILITY.md` contain no row for async payments, trampoline,
onion messages, unified payments, or BOLT 12 (`rg` returns no matches), so
this lane cannot inherit an existing obligation or hidden assumption from
those documents.

## 2. LDK datapoints (with `file:line`)

All LDK Node citations are against `fa123fed131e27ecc420b77fa7086fcf1ddaebb8`.
LDK Server citations are against `c17dc11dde38f88c53457039ddf30c6b90a63ba2`.

### 2.1 Unified receive: one amount, three optional payment rails

`ldk-node/src/payment/unified.rs:135-175` is the whole receive path:

* `:138` converts `amount_sats` with `checked_mul(1_000)` and returns
  `Error::InvalidAmount` on overflow. This is the only arithmetic guard.
* `:140` creates the on-chain address first; failure is fatal
  (`WalletOperationFailed`).
* `:142-152` tries to create a BOLT 12 offer for `amount_msats`; failure is
  logged and the offer is simply omitted (`None`).
* `:154-166` tries to create a BOLT 11 invoice for the same `amount_msats`,
  description, and expiry; failure is logged and the invoice is omitted.
* `:168-173` builds `Extras { bolt11_invoice, bolt12_offer }`, sets the URI
  top-level amount to `amount_sats`, and sets the message to the description.
* `:467-483` serialises the `lightning=` and `lno=` values in uppercase;
  `:494-499` and `:532-541` are the BIP 21 extras serializer/parser.
* Integration test `tests/integration_tests_rust.rs:5113-5160`
  (`generate_bip21_uri`) proves the graceful-omission behaviour: before any
  channel, the URI has `bitcoin:` and `lightning=` but no `lno=`; after a
  channel, all three are present.
* Test `tests/integration_tests_rust.rs:5163-5171`
  (`unified_receive_rejects_msat_overflow`) asserts
  `receive(u64::MAX, "asdf", 4_000) = Err(InvalidAmount)`.

The important invariant is **same amount across rails**: the on-chain URI
amount is in sats, while the BOLT 11 invoice and BOLT 12 offer carry
`amount_msats = sats * 1000`. The Lean model has no unified URI and no
cross-rail amount theorem.

### 2.2 Unified send: fixed order, fatal aborts, no double pay

`ldk-node/src/payment/unified.rs:191-412` is the send path:

* `:195-197` returns `NotRunning` before parsing anything.
* `:205-223` parses a BIP 21 URI or BIP 353 HRN with a resolution timeout
  (`HRN_RESOLUTION_TIMEOUT_SECS`).
* `:225-244` for `ConfigurableAmount`, requires a caller-supplied amount;
  converts to `BPIAmount` and calls `set_amount`.
* `:246-262` for `FixedAmount`, rejects only when the caller amount is
  *less than* the URI's `max_amount`; larger amounts are accepted.
* `:266-270` sorts methods by `Bolt12 => 0`, `Bolt11 => 1`, `OnChain => 2`.
  The order is therefore BOLT 12, then BOLT 11, then on-chain.
* `:274-350` BOLT 12 leg: on `Ok` return `Bolt12`; on `DuplicatePayment`
  return the error (`:331-333`); on `NotRunning` return the error
  (`:336-338`); on `PersistenceFailed` return the error (`:343-345`); any
  other error falls through to BOLT 11 (`:347-349`).
* `:352-381` BOLT 11 leg: identical success/fatal/fall-through policy, with
  on-chain as the next fallback.
* `:383-410` on-chain leg: requires an amount (`onchain_payment_amount`),
  checks `is_running`, and returns the txid.
* `:411` returns `PaymentSendingFailed` if no method is payable.

The two comments at `:329-330` and `:340-342` state the reason for the abort:
falling back after a `DuplicatePayment` or a `PersistenceFailed` could pay the
same offer/invoice twice. This is the central safety property of the surface.

Integration test `tests/integration_tests_rust.rs:5260-5418`
(`unified_send_receive_bip21_uri`) exercises it:

* `:5300-5320` a full URI pays via BOLT 12.
* `:5322-5340` stripping `&lno=` falls back to BOLT 11.
* `:5342-5355` resending the same BOLT 11 URI must return
  `DuplicatePayment`, not fall back on-chain (regression for LDK Node
  issue #1033).
* `:5357-5375` stripping `&lightning=` falls back on-chain.
* `:5378-5418` arming a payment-store write failure on the BOLT 11 leg must
  return `PersistenceFailed` and must **not** broadcast an on-chain payment.

### 2.3 BOLT 12 send/receive amount rules and async role

`ldk-node/src/payment/bolt12.rs`:

* `:126-151` `send_using_amount_inner`: a fixed `offer_amount_msat` is read
  from the offer; unsupported currencies fail; `amount_msat <
  offer_amount_msat` returns `InvalidAmount`. There is no upper bound (unlike
  BOLT 11's `amountSatisfies`, which is `a <= paid <= 2*a`).
* `:297-321` plain `send` rejects a zero-amount offer with `InvalidOffer` and
  requires `send_using_amount`.
* `:233-267` `receive_inner` builds an offer with `amount_msats`,
  description, optional absolute expiry, and optional non-zero quantity
  (`:251-259` rejects `quantity = 0`).
* `:270-286` `blinded_paths_for_async_recipient_internal` requires
  `AsyncPaymentsRole::Server`, otherwise `AsyncPaymentServicesDisabled`.
* `:635-655` `receive_async` returns the offer only if the static-invoice
  server paths were set and the static invoice was interactively built;
  `:667-678` sets those paths; `:686-692` exposes the recipient paths.
* Test `tests/integration_tests_rust.rs:4740-4757` checks that
  `send_using_amount` with less than the offer amount errors.

`ldk-node/src/builder.rs:2149-2156` sets the async roles:

* `Server`: `accept_forwards_to_priv_channels = true` and
  `enable_htlc_hold = true`.
* `Client`: `hold_outbound_htlcs_at_next_hop = true`.

This is only role configuration. It is not a hold/release state machine.

### 2.4 Async messages, mailbox, and static-invoice storage

Async payments are carried as onion messages. The message vocabulary is in
`refs/rust-lightning/lightning/src/onion_message/async_payments.rs`:

* `:23-28` TLV types: `OfferPathsRequest` 75540, `OfferPaths` 75542,
  `ServeStaticInvoice` 75544, `StaticInvoicePersisted` 75546,
  `HeldHtlcAvailable` 72, `ReleaseHeldHtlc` 74.
* `:40-115` the `AsyncPaymentsMessageHandler` contract. `context` is
  authenticated as coming from a blinded path the node created; the handler
  returns `Option<(Reply, ResponseInstruction)>` for the request/response
  messages.
* `:136-238` the `AsyncPaymentsMessage` enum and payload records. The flow is
  `OfferPathsRequest -> OfferPaths -> ServeStaticInvoice ->
  StaticInvoicePersisted -> HeldHtlcAvailable -> ReleaseHeldHtlc`.
* `HeldHtlcAvailable` says the HTLC is held upstream; `ReleaseHeldHtlc`
  releases the corresponding inbound HTLC.
* `ServeStaticInvoice.forward_invoice_request_path` must have its
  introduction node set to the static-invoice server or one of its peers,
  for DoS protection.

`ldk-node/src/payment/asynchronous/om_mailbox.rs:7-63` is the mailbox:

* `:11-12` limits: `MAX_MESSAGES_PER_PEER = 30`, `MAX_PEERS = 300`.
* `:19-39` on interception, appends to the peer queue and drops the oldest
  message when the peer queue is full; evicts the peer with the longest queue
  when the peer limit is exceeded.
* `:41-51` on peer connect, drains the queue.

`ldk-node/src/event.rs:2468-2499` wires
`OnionMessageIntercepted`/`OnionMessagePeerConnected` to that mailbox.
`ldk-node/src/event.rs:2501-2560` handles `PersistStaticInvoice` and
`StaticInvoiceRequested`: persistence failure replays the event; a missing
static invoice is a no-op; a found invoice is sent through
`respond_to_static_invoice_request(invoice, reply_path, invoice_request,
invoice_request_path)`.

`ldk-node/src/payment/asynchronous/static_invoice_store.rs:74-150`:

* `:74-110` `handle_static_invoice_requested` checks a request rate limit,
  reads `static_invoices/<sha256(recipient_id)>/<invoice_slot>`, parses the
  persisted invoice, and returns `None` on `NotFound`.
* `:111-143` `handle_persist_static_invoice` checks a persist rate limit and
  writes the invoice plus request path.
* `:145-150` the storage location is `sha256(recipient_id)` and a five-digit
  invoice slot.
* `ldk-node/src/payment/asynchronous/rate_limiter.rs:26,38-60` is a
  leaky-bucket limiter with `MAX_USERS = 10_000`; it uses `Instant::now()`.

`ldk-node/tests/integration_tests_rust.rs:4882-5015` (`async_payment`) builds
a four-node sender/LSP/receiver topology, obtains recipient paths from the
receiver LSP, calls `receive_async`, stops the receiver, pays the offer, waits
for the HTLC to be held, restarts the receiver, and expects success. This is
the only end-to-end async-payment evidence in the pinned tree.

### 2.5 Static invoices do not support recipient-side payer proofs

`ldk-node/src/event.rs:146-155` documents that a paid BOLT 12 invoice is
useful for proof of payment because `payment_hash = sha256(payment_preimage)`,
but static invoices (async payments) **do not** support proof of payment
because the payment hash is not derived from a preimage known only to the
recipient. The LDK Server gRPC request documents the same limitation at
`ldk-server-grpc/src/api.rs:699` ("Static invoices used for async payments
cannot be proven"); `ldk-server/src/api/bolt12_create_payer_proof.rs` is the
thin handler that forwards the invoice/preimage to
`create_payer_proof`.

This is a negative protocol fact, not a missing theorem. A future Lean target
may record it, but it must not reuse the BOLT 11 `preimageCommits` shape as if
a static invoice had a recipient-only preimage.

### 2.6 Onion-message envelope and admission rules

`refs/bolts/04-onion-routing.md:1700-1840` is the normative section:

* `:1700-1713` onion messages query for invoices and use the same Sphinx form
  as HTLC onions, with payload length implied by the total length.
* `:1715-1718` "Onion messages are unreliable ... no error returned from
  intermediary nodes." This is a liveness/robustness fact, not an HTLC failure
  packet.
* `:1720` all onion messages use route blinding.
* `:1721-1750` `onion_message` type 513 and `onion_message_packet`
  (`version`, `public_key`, `onionmsg_payloads`, `hmac`).
* `:1751-1760` `onionmsg_tlv`: `reply_path` (2), `encrypted_recipient_data`
  (4), `invoice_request` (64), `invoice` (66), `invoice_error` (68). Types 64
  and above are final-hop only.
* `:1780-1795` writer rules: non-final nodes carry only
  `encrypted_recipient_data`; a final node permitted to reply sets
  `reply_path.path_key`, `reply_path.first_node_id`, and per-hop blinded node
  ids; otherwise it MUST NOT set `reply_path`.
* `:1805-1810` reader must ignore a message whose decryption fails, whose TLV
  is malformed/unknown-even, or whose `allowed_features` check fails.
* `:1811-1823` non-final node: reject extra TLV fields and a `path_id`; require
  `next_node_id` or a known `short_channel_id`; forward with the next
  `path_key`.
* `:1828-1835` final node: a `path_id` matching a previously published
  `reply_path` is accepted only if the message is a reply to that previous
  onion; an unknown/unset `path_id` is treated independently; more than one
  payload field is ignored.
* `:1837-1840` a reply must use the `reply_path` and its `first_node_id` /
  `path_key`.

`refs/bolts/09-features.md:51,60` assigns `option_onion_messages` (38/39) and
`option_onion_messages_only_channels` (66/67). `:73` is the "do not set both
bits" rule.

The current `OnionPacket` model has no `onionmsg_tlv`, no `path_id`, no
`reply_path`, no final-hop payload union, and no `allowed_features` gate. R09
covers the HTLC packet and route-blinding crypto; this lane covers the
message-envelope admission and reply binding that sit above it.

### 2.7 Trampoline is a feature bit plus event-list semantics

* `refs/rust-lightning/lightning-types/src/features.rs:72-73` describes
  trampoline as "supports receiving and forwarding Trampoline payments" and
  points at BOLT PR 836.
* `:684-692` assigns feature bit 57 with the `Trampoline` context,
  `set_trampoline_routing_optional`, `set_trampoline_routing_required`,
  `supports_trampoline_routing`, and `requires_trampoline_routing`.
* `ldk-node/src/event.rs:186-194` says `PaymentForwarded.prev_htlcs` and
  `next_htlcs` contain a single HTLC for source-routed payments and **may
  contain multiple HTLCs when we acted as a trampoline router**.
* `ldk-node/src/event.rs:1936-1947` handles multiple `next_htlcs` for a
  trampoline forward and warns that a skimmed fee may be double-counted.

There is no trampoline path construction, no trampoline onion payload, and no
trampoline-specific fee theorem in LDK Node. The pinned BOLT clone has no
trampoline specification (it is BOLT PR 836); `refs/bolts` is at
`1aadb719b4007c4cea0ba6e36b08c4fb53788dee`.

### 2.8 LDK Server and pin caveats

`ldk-server/src/api/unified_send.rs:20-41` is a thin dispatch: it builds route
parameters, calls `node.unified_payment().send(...)`, and maps the result to
`Txid`, `Bolt11PaymentId`, or `Bolt12PaymentId`. There is no additional
ordering or async logic.

`ldk-server/src/api/bolt12_send.rs:22-45` chooses plain `send` when
`amount_msat` is absent and `send_using_amount` when it is present.
`ldk-server/src/api/bolt12_receive.rs:22-46` rejects `quantity` without a
fixed amount as a server-policy error (not a BOLT 12 requirement) and returns
`offer.id()` as an LDK bookkeeping identifier. R11 owns the offer/invoice TLV
and `OfferId` analysis; this lane only uses the dispatch shape.

Two pin caveats matter:

* The pinned LDK Server's `Cargo.lock:1382-1384` resolves `ldk-node` at
  `179b4b263762155a7ff515ddad7e757a80807fd5`, not at the `fa123fed` revision
  used for the LDK Node citations above. Treat LDK Server as a behavioural
  anchor only, and do not attribute `fa123fed` line numbers to it.
* LDK Node's `Cargo.toml:89-100` resolves rust-lightning at
  `d7a980641c6325ddda5072a0f470ef8392676cf5`; the local
  `refs/rust-lightning` clone is `fe4900930c6bd5786ec4203274d7cf312776a5a6`.
  The async-payment and trampoline citations from `refs/rust-lightning` are
  therefore behavioural anchors, not the exact dependency of the pinned LDK
  Node.

## 3. Gap matrix

Status vocabulary: **covered faithfully**, **partially covered**, **missing**,
**contradicted**, **unmodelled/external**.

| Behavior | Lean status | LDK evidence | Gap / counterexample | Priority |
|---|---|---|---|---|
| BOLT 11 invoice record, field-list codec, signature projection | covered faithfully **for its stated pre-bech32 scope** | `Invoice.lean:197-250`; `InvoiceWireTargets.lean`; `LN-PM-001/002/003/007` | No BOLT 12, unified, or static-invoice semantics. `signatureOnly_no_preimage` is a BOLT 11 separation, not a payer-proof model. | P2 (reference) |
| Structural onion peel determinism and checked HMAC rejection | covered faithfully **as a structural skeleton** | `Onion.lean:248-251`, `:498-545`; `LN-RT-003/004` | No `onionmsg_tlv`, no `path_id`, no reply path, no hop TLV. R09 owns the packet gap; do not read this as `onion_message`. | P2 (reference) |
| Unified receive converts sats to msats with overflow check | missing | `unified.rs:138`; test `integration_tests_rust.rs:5163-5171` | No unified receive function. A `Nat` model without an explicit bound would "prove" `sats * 1000` for every `sats` and miss the `u64` rejection. | **P0** |
| Unified receive keeps top-level sats and BOLT 11/BOLT 12 msat amounts equal | missing | `unified.rs:140-171`; test `:5113-5160` | BOLT 11 `Invoice.amount` is msat (`Invoice.lean:197-207`); no carrier ties it to a URI `amount_sats` or to a BOLT 12 offer. | **P0** |
| Unified receive omits a failed component instead of failing the URI | missing | `unified.rs:142-166`; test `:5113-5160` | No component-option model and no failure-isolation theorem. | P1 |
| BOLT 12 `send_using_amount` requires `amount >= offer.amount` | missing (R11 owns offer TLV) | `bolt12.rs:137-151`; test `:4740-4757` | No `Offer` record. Do **not** reuse `Invoice.amountSatisfies` (`Invoice.lean:277-282`), whose rule is `a <= paid <= 2*a`; BOLT 12 has no upper bound here. | P1 |
| Zero-amount offer rejected by plain `send` | missing (R11 owns offer TLV) | `bolt12.rs:297-321` | No amount-mode (fixed vs zero) carrier. | P1 |
| Unified send order is BOLT 12, BOLT 11, on-chain | missing | `unified.rs:266-270`; test `:5300-5375` | No method list, no sublist/order predicate. | **P0** |
| Fatal send errors abort instead of falling through | missing; **contradicted** by a naive "all errors fall through" model | `unified.rs:331-345`, `:362-376`; test `:5342-5418` | Counterexample to naive fallback: `DuplicatePayment` on BOLT 12 must not try BOLT 11; `PersistenceFailed` on BOLT 11 must not try on-chain. | **P0** |
| At most one payment method initiates a payment | missing | `unified.rs:274-410`; test `:5300-5418` | No `calls`/trace model. Existing `PaymentSession` is single-payment and does not represent a method list. | **P0** |
| Fixed-amount URI rejects a user amount below the URI maximum | missing | `unified.rs:246-262` | No URI amount comparison; note the policy is "less than", not "not equal". | P1 |
| On-chain fallback requires an amount and a running node | missing | `unified.rs:383-410` | No method-level amount/state precondition. | P1 |
| BIP 353 / HRN resolution is a payment-instruction oracle | unmodelled/external | `unified.rs:205-264`; `hrn.rs:14-52` | DNS/DNSSEC/LNURL resolution and timeouts are external. An HRN is not a payment proof. | P2 |
| `onion_message` type 513 envelope and `onionmsg_tlv` schema | missing | BOLT 4 `:1721-1760` | `OnionPacket` is an HTLC-payload layer list; it has no message type, `path_key`, or `onionmsg_tlv`. | P1 |
| Onion messages are unreliable and produce no intermediary error | unmodelled/external | BOLT 4 `:1715-1718` | No drop/forward system. `F16.AsyncSystem` can express a drop schedule but has no onion-message state. | P2 |
| Intermediate onion message carries only `encrypted_recipient_data` and no `path_id` | missing | BOLT 4 `:1811-1823` | No admission predicate and no message payload union. | P1 |
| Final onion message carries at most one payload field (64/66/68) | missing | BOLT 4 `:1834-1835` | No payload-field classifier; a naive "at most one TLV" rule would wrongly reject a coexisting `reply_path`. | P1 |
| Reply path construction and `path_id` binding | missing | BOLT 4 `:1787-1795`, `:1828-1840`; `RouteBlindingProps.lean:473-487` | `BlindedPath` has no `path_id`, no reply history, and no `first_node_id`/`path_key` reply rule. | P1 |
| Unknown-even TLV and `allowed_features` rejection | missing | BOLT 4 `:1805-1810`; `LnLean/Wire/TLV.lean:19-27` | Generic `Wire.TLV` explicitly does not model known-type/even-odd policy. | P1 |
| Async role configuration (`hold`/`accept_forwards`) | unmodelled/external | `builder.rs:2149-2156` | No role or channel-config carrier; `F16.AsyncSystem` is scheduling only. | P2 |
| Static-invoice hold/release/claim state machine | missing | `event.rs:2501-2560`; `async_payments.rs:40-115`; test `:4882-5015` | No `held`/`released`/`claimed` state, no authenticated-release precondition, no at-most-once release. | P1 |
| Async offer is ready only after `StaticInvoicePersisted` | missing | `bolt12.rs:635-655`; `async_payments.rs:136-238` | No offer-readiness predicate. | P1 |
| Static invoice payer proof | **contradicted** if claimed from BOLT 11 | `event.rs:146-155`; `ldk-server-grpc/src/api.rs:699` | Static-invoice payment hash is not derived from a recipient-only preimage. `signatureOnly_no_preimage` is a BOLT 11 separation result, not a proof model. | P2 (external) |
| Onion mailbox queue limits and oldest-message eviction | missing | `om_mailbox.rs:11-39` | No queue or eviction model; a finite-list model is possible but is an implementation policy, not a protocol theorem. | P2 |
| Static-invoice store rate limits and path layout | unmodelled/external | `static_invoice_store.rs:74-150`; `rate_limiter.rs:26,38-60` | `Instant::now()` and leaky-bucket state are external; the storage path is an implementation fact. | P2 |
| Trampoline feature bit 57 | partially covered (generic only) | `lightning-types/src/features.rs:684-692`; `FeaturesProps.lean:133-163` | `FeatureVector.supports` applies to any `n`, but no declaration names bit 57 or states the trampoline gate. | P2 |
| Trampoline multi-HTLC forward and fee accounting | unmodelled/external | `event.rs:186-194`, `:1936-1947` | No trampoline route or multi-HTLC forward model. The event is a reporting surface, not a protocol construction. | P2 |
| BOLT 12 offer/invoice TLV, payer proof, refunds | missing (R11 owns) | see R11 | Do not duplicate R11. Only the *unified dispatch* and *amount coupling* are in this lane. | P1/P0 in R11 |
| Structural blinded path | partially covered | `RouteBlindingProps.lean:437-487` | No `num_hops`, `enclen`, ECDH, `path_id`, or onion-message path. R09 owns the crypto/wire gap. | P1 |
| Asynchronous scheduling safety | partially covered | `F16.lean:75-110`, `:114-173`; `LN-SEC-003` | Proves safety under an unfair schedule for an abstract system. It does not prove liveness of async payments; the hold/release flow needs fairness or a timeout. | P2 |

## 4. Proposed targets

The module names below do not exist. They are bounded proposals for a future
proof wave, not catalog rows. Each is a **model extension** unless explicitly
marked external.

### T1 — `LnLean.Proofs.Payment.UnifiedPaymentTargets.unified_send_no_double_pay`

**Priority:** P0. **Classification:** model extension. **Feasibility:** high
(pure list induction; no crypto, no TLV, no persistence).

**Statement shape.**

```lean
namespace LnLean.Proofs.Payment.UnifiedPaymentTargets

inductive Method | bolt12 | bolt11 | onchain
  deriving DecidableEq, Repr

inductive Attempt
  | sent (m : Method)
  | benignFailure (m : Method)
  | fatal (e : Error)

inductive Outcome
  | success (m : Method)
  | aborted (e : Error)
  | exhausted

def canonicalOrder : List Method := [.bolt12, .bolt11, .onchain]

def methodRank : Method → Nat
  | .bolt12 => 0
  | .bolt11 => 1
  | .onchain => 2

def calls : List Method → (Method → Attempt) → List Method
  | [], _ => []
  | m :: rest, attempt =>
      match attempt m with
      | .sent _ => [m]
      | .fatal _ => [m]
      | .benignFailure _ => m :: calls rest attempt

def run : List Method → (Method → Attempt) → Outcome
  | [], _ => .exhausted
  | m :: rest, attempt =>
      match attempt m with
      | .sent _ => .success m
      | .fatal e => .aborted e
      | .benignFailure _ => run rest attempt

theorem unified_send_calls_follow_canonical_order
    (ms : List Method) (attempt : Method → Attempt)
    (h : ms <+ canonicalOrder) :
    (calls ms attempt).Pairwise
      (fun m n => methodRank m < methodRank n)

theorem unified_send_at_most_one_sent
    (ms : List Method) (attempt : Method → Attempt)
    (h : ms <+ canonicalOrder) :
    ((calls ms attempt).filter
      (fun m => match attempt m with | .sent _ => true | _ => false)).length ≤ 1

theorem unified_send_stops_at_fatal
    (ms : List Method) (attempt : Method → Attempt) (e : Error)
    (h : run ms attempt = .aborted e) :
    ∃ pre m post,
      ms = pre ++ m :: post ∧
      attempt m = .fatal e ∧
      calls ms attempt = pre ++ [m]

theorem unified_send_success_is_first_sent
    (ms : List Method) (attempt : Method → Attempt) (m : Method)
    (h : run ms attempt = .success m) :
    attempt m = .sent m ∧
    ∀ n ∈ calls ms attempt, n ≠ m → attempt n ≠ .sent n

/-- The named summary target: canonical order, at most one sent method, fatal
abort with no later call, and a successful method is the first sent one. -/
theorem unified_send_no_double_pay
    (ms : List Method) (attempt : Method → Attempt)
    (h : ms <+ canonicalOrder) :
    (calls ms attempt).Pairwise
        (fun m n => methodRank m < methodRank n) ∧
      ((calls ms attempt).filter
        (fun m => match attempt m with | .sent _ => true | _ => false)).length ≤ 1 ∧
      (∀ e, run ms attempt = .aborted e →
        ∃ pre m post,
          ms = pre ++ m :: post ∧
          attempt m = .fatal e ∧
          calls ms attempt = pre ++ [m]) ∧
      (∀ m, run ms attempt = .success m →
        attempt m = .sent m ∧
        ∀ n ∈ calls ms attempt, n ≠ m → attempt n ≠ .sent n)
```

**Hypotheses.** `ms` is a duplicate-free sublist of the canonical order; each
`attempt m` is the *whole* outcome of one method (there is no concurrency and
no retry inside a method); `fatal` is exactly `{DuplicatePayment,
PersistenceFailed, NotRunning}` and every other error is `benignFailure`. The
last premise is a behavioural reading of `unified.rs:331-376`; it is not
derived from Lean.

**Non-vacuity witnesses.** (a) `ms = canonicalOrder`, `attempt .bolt12 =
benignFailure`, `attempt .bolt11 = sent`, so `run = .success .bolt11` and
`calls = [.bolt12, .bolt11]`. (b) `attempt .bolt12 = fatal .duplicatePayment`,
so `run = .aborted` and `calls = [.bolt12]`; the on-chain method is never
called. (c) `ms = [.onchain]` with `sent .onchain` is a one-method success.
(d) A negative witness: `ms = [.bolt12, .bolt11]`, `attempt .bolt12 = sent`,
`attempt .bolt11 = sent`; the trace is `calls = [.bolt12]`, so the second
method is never called. A trace with two called `.sent` methods is excluded by
`unified_send_at_most_one_sent`; do not weaken it to "two attempts may both
succeed" just because the total `attempt` function still assigns `sent` to the
uncalled method.

**Why faithful.** The order and the fatal-error policy are exactly the two
facts LDK Node relies on to avoid double payment (`unified.rs:266-270`,
`:329-349`). The model deliberately does not claim that a method's internal
send is atomic; that is R12's store/record window (`R12` §T4).

**Fidelity risk.** Medium. `Attempt` compresses a full async `send` into one
constructor. `NotRunning` is treated as fatal even though it is checked before
each leg; the model should make it a precondition, not an outcome, if a later
revision needs the distinction. Do not add a theorem saying a benign failure
implies no HTLC was sent; that requires the store model.

### T2 — `LnLean.Proofs.Payment.UnifiedPaymentTargets.unified_receive_amount_consistent`

**Priority:** P0. **Classification:** model extension. **Feasibility:** high
(arithmetic and option propagation).

**Statement shape.**

```lean
structure Bolt12OfferStub where
  amountMsat : Nat

structure UnifiedUri where
  amountSats : Nat
  bolt11 : Option Invoice
  bolt12 : Option Bolt12OfferStub
  onchain : Address

def receiveUnified (sats : Nat) (description : String) (expiry : Nat)
    : Except Error UnifiedUri

theorem unified_receive_amount_consistent
    (sats : Nat) (description : String) (expiry : Nat)
    (hno : sats * 1000 ≤ 2 ^ 64 - 1) :
    ∃ u,
      receiveUnified sats description expiry = .ok u ∧
      u.amountSats = sats ∧
      (∀ i ∈ u.bolt11, i.amount = some ⟨sats * 1000⟩) ∧
      (∀ o ∈ u.bolt12, o.amountMsat = sats * 1000)

theorem unified_receive_overflow_rejected
    (sats : Nat) (description : String) (expiry : Nat)
    (hover : 2 ^ 64 - 1 < sats * 1000) :
    receiveUnified sats description expiry = .error .invalidAmount

theorem unified_receive_omission_preserves_amount
    (sats : Nat) (description : String) (expiry : Nat) (u : UnifiedUri)
    (h : receiveUnified sats description expiry = .ok u)
    (hno12 : u.bolt12 = none) :
    u.amountSats = sats ∧
    (∀ i ∈ u.bolt11, i.amount = some ⟨sats * 1000⟩)
```

**Hypotheses.** `sats * 1000` is evaluated in `Nat`, with the explicit
`2^64 - 1` bound standing for the `u64` check at `unified.rs:138`; on-chain
address generation succeeds; BOLT 11/BOLT 12 component failures are modelled as
`none`; `expiry` fits the implementation's `u32`. `Bolt12OfferStub` is a local
`{ amountMsat : Nat }` carrier until R11's `Bolt12Offer` exists; the target
must be retargeted, not duplicated, when R11 lands. The omission theorem is the
test-observed case where `lno=` is absent but the top-level amount and the
BOLT 11 amount are still the requested value (`unified.rs:142-166`; test
`:5113-5160`).

**Non-vacuity witnesses.** (a) `sats = 100000`, channels present: both
components are `some` and both amounts are `100000000`. (b) `sats = 100000`,
channels absent: `bolt12 = none`, `bolt11 = some`, top-level amount still
`100000`. (c) `sats = 2^64 / 1000 + 1`: overflow error. (d) A negative
witness: a `UnifiedUri` with `amountSats = 100000` and a BOLT 11 component of
`100000001` msat is excluded.

**Why faithful.** It is the exact invariant a BIP 21 consumer needs: one
requested amount, three rails that must not disagree. It matches
`unified.rs:138-171` and tests `:5113-5171`.

**Fidelity risk.** Medium-low. The real function also uppercases the
`lightning=`/`lno=` strings (`unified.rs:467-483`); this target does not model
string case, so it must not be read as a URI-codec theorem. `expiry` is passed
to BOLT 11 but the offer only uses it if non-`None` in some paths; the target
should parameterise component expiry separately rather than assume both rails
use the same rule.

### T3 — `LnLean.Proofs.Routing.OnionMessageTargets.onionMessage_admission`

**Priority:** P1. **Classification:** model extension. **Feasibility:**
medium (new payload union and admission predicate; no crypto).

**Statement shape.**

```lean
namespace LnLean.Proofs.Routing.OnionMessageTargets

inductive Payload
  | replyPath (p : BlindedPath)
  | encryptedRecipientData (b : ByteArray)
  | invoiceRequest (b : ByteArray)
  | invoice (b : ByteArray)
  | invoiceError (b : ByteArray)

def Payload.isPayloadField : Payload → Bool
  | .invoiceRequest _ | .invoice _ | .invoiceError _ => true
  | _ => false

structure Message where
  payloads : List Payload
  pathId : Option ByteArray

structure AdmissionContext where
  isFinal : Bool
  pathIdPublished : Bool
  isReply : Bool
  pathIdMatches : Bool
  decrypted : Bool
  tlvWellFormed : Bool
  allowedFeaturesOk : Bool

-- The body conjoins the `decrypted`/`tlvWellFormed`/`allowedFeaturesOk`
-- gates with the intermediate and final reader rules stated below. It is
-- deliberately left abstract at this scoping stage.
def admissible (c : AdmissionContext) (m : Message) : Prop := ...

theorem onionMessage_intermediate_admission
    (c : AdmissionContext) (m : Message)
    (h : admissible c m) (hf : c.isFinal = false) :
    (∀ p ∈ m.payloads, ∃ b, p = .encryptedRecipientData b) ∧
    m.pathId = none

theorem onionMessage_final_single_payload
    (c : AdmissionContext) (m : Message)
    (h : admissible c m) (hf : c.isFinal = true) :
    (m.payloads.filter Payload.isPayloadField).length ≤ 1

/-- The named summary target: both the intermediate-shape and final-single-
payload reader rules hold for every admitted message. -/
theorem onionMessage_admission
    (c : AdmissionContext) (m : Message)
    (h : admissible c m) :
    (c.isFinal = false →
      (∀ p ∈ m.payloads, ∃ b, p = .encryptedRecipientData b) ∧
      m.pathId = none) ∧
    (c.isFinal = true →
      (m.payloads.filter Payload.isPayloadField).length ≤ 1)
```

**Hypotheses.** Decryption and TLV well-formedness already succeeded; unknown
even types and `allowed_features` were checked (these are hypotheses, not
re-proved); `isFinal` is supplied by the onion layer; `BlindedPath` is the
structural carrier from `RouteBlindingProps.lean:473-487`. The model does not
claim that `admissible` is complete with respect to BOLT 4.

**Non-vacuity witnesses.** (a) Final message with one `invoiceRequest` and a
`replyPath` is admitted; the filter counts one payload field. (b) Final
message with `invoiceRequest` and `invoice` is rejected. (c) Intermediate
message with only `encryptedRecipientData` is admitted. (d) Intermediate
message with a `replyPath` is rejected. (e) A final message with a
`path_id` is not automatically rejected (the `path_id` rule is T4).

**Why faithful.** These are the two unconditional reader rules that do not
depend on history: non-final payload shape and final single-payload
(`04-onion-routing.md:1811-1835`). The `reply_path` exception is modelled by
keeping `replyPath` outside `isPayloadField`.

**Fidelity risk.** Medium-high. The real `onionmsg_tlv` is a TLV stream, not a
list; a list model can accidentally admit duplicate unknown-odd fields or
combine duplicate `reply_path` records. The target should either use the
existing `Wire.TLV` shape or state a `CanonicalPayloads` hypothesis. Do not
claim route-blinding authentication from this target.

### T4 — `LnLean.Proofs.Routing.OnionMessageTargets.onionMessage_replyPath_binding`

**Priority:** P1. **Classification:** model extension plus an external
authentication assumption. **Feasibility:** medium; needs a published-path
history and an opaque `path_id` map.

**Statement shape.**

```lean
structure ReplyPath where
  firstNodeId : NodeId
  pathKey : PubKey
  hops : List BlindedHop
  pathId : ByteArray

-- The body requires a non-empty `firstNodeId`/`pathKey` pairing, at least one
-- hop, and per-hop blinded node ids and encrypted recipient data.
def replyPathWellFormed (p : ReplyPath) : Prop := ...

def replyAuthenticatedByPublishedPath
    (published : List ReplyPath) (m : Message) : Prop :=
  ∃ p ∈ published, m.pathId = some p.pathId

theorem onionMessage_replyPath_wellFormed
    (c : AdmissionContext) (m : Message) (p : ReplyPath)
    (h : admissible c m) (hf : c.isFinal = true)
    (hp : Payload.replyPath p ∈ m.payloads) :
    replyPathWellFormed p

theorem onionMessage_publishedPath_reply_bound
    (published : List ReplyPath) (c : AdmissionContext) (m : Message)
    (h : admissible c m) (hf : c.isFinal = true)
    (hpub : replyAuthenticatedByPublishedPath published m) :
    c.pathIdPublished = true ∧ c.pathIdMatches = true ∧ c.isReply = true

theorem onionMessage_unknownPathId_not_authenticated
    (published : List ReplyPath) (c : AdmissionContext) (m : Message)
    (h : admissible c m) (hf : c.isFinal = true)
    (hnone : m.pathId = none) :
    ¬ replyAuthenticatedByPublishedPath published m

/-- The named summary target: a well-formed reply path plus the
published-path/`path_id` admission rule. -/
theorem onionMessage_replyPath_binding
    (published : List ReplyPath) (c : AdmissionContext) (m : Message)
    (h : admissible c m) (hf : c.isFinal = true) :
    (∀ p : ReplyPath, Payload.replyPath p ∈ m.payloads →
      replyPathWellFormed p) ∧
    (replyAuthenticatedByPublishedPath published m →
      c.pathIdPublished = true ∧ c.pathIdMatches = true ∧ c.isReply = true)
```

**Hypotheses.** `published` is the node's own list of reply paths; a `path_id`
match is an opaque equality, not a cryptographic authentication; the onion
layer has already authenticated the message as coming from a blinded path the
node created (`async_payments.rs:40-44` is the analogous contract). Without
that external assumption, `isReply` is only a local flag.

**Non-vacuity witnesses.** (a) `published = [p]`, `m.pathId = some p.pathId`,
`isReply = true`: admitted and bound. (b) Same path id, `isReply = false`:
rejected by the BOLT 4 rule. (c) `m.pathId = none`: admitted as an independent
message but not authenticated by a published path. (d) A reply path with
`firstNodeId` not equal to the unblinded introduction node is rejected by
`replyPathWellFormed`.

**Why faithful.** It captures the difference between "unknown/unset path_id"
and "matches a path we published" in `04-onion-routing.md:1828-1840`.
**Fidelity risk.** High if `path_id` is treated as a bearer token. BOLT 4
allows the creator to store a secret in `path_id` and verify context
(`:512`, `:545`); the Lean model must keep that as an explicit
`PathIdSecret`/history assumption, not as an equality oracle. Do not claim
reply unlinkability or ECDH authentication.

### T5 — `LnLean.Proofs.Payment.AsyncPaymentTargets.asyncHoldRelease_stateMachine`

**Priority:** P1, but **defer to wave 14**. **Classification:** model
extension. **Feasibility:** medium; a small state machine is easy, but tying
it to the actual store and timer semantics is not.

**Statement shape.**

```lean
namespace LnLean.Proofs.Payment.AsyncPaymentTargets

inductive Role | client | server

inductive AsyncState
  | noOffer
  | offerReady
  | invoiceServed
  | htlcHeld
  | released
  | claimed
  | failed

structure AsyncOffer where
  offerId : ByteArray

structure AsyncRecipient where
  role : Role
  staticInvoicePersisted : Bool
  held : Bool
  released : Bool
  claimed : Bool

def receiveAsync (r : AsyncRecipient) : Option AsyncOffer

def holdHtlc : AsyncState → Option AsyncState
  | .invoiceServed => some .htlcHeld
  | _ => none

def releaseHtlc : AsyncState → Bool → Option AsyncState
  | .htlcHeld, true => some .released
  | _, _ => none

def claimHtlc : AsyncState → Option AsyncState
  | .released => some .claimed
  | _ => none

theorem async_release_only_from_held
    (s s' : AsyncState) (auth : Bool)
    (h : releaseHtlc s auth = some s') :
    s = .htlcHeld

theorem async_release_requires_authentication
    (s s' : AsyncState)
    (h : releaseHtlc s false = some s') : False

theorem async_release_at_most_once
    (s : AsyncState) (h : s = .released) :
    releaseHtlc s true = none

theorem async_claim_only_after_release
    (s s' : AsyncState) (h : claimHtlc s = some s') :
    s = .released

theorem async_offer_requires_persisted_static_invoice
    (r : AsyncRecipient) (o : AsyncOffer)
    (h : receiveAsync r = some o) :
    r.staticInvoicePersisted = true

/-- The named summary target: release is only from `htlcHeld`, only with
authentication, at most once, and claim is only after release. -/
theorem asyncHoldRelease_stateMachine :
    (∀ (s s' : AsyncState) (auth : Bool),
      releaseHtlc s auth = some s' → s = .htlcHeld) ∧
    (∀ (s s' : AsyncState),
      releaseHtlc s false = some s' → False) ∧
    (∀ s : AsyncState, s = .released → releaseHtlc s true = none) ∧
    (∀ (s s' : AsyncState),
      claimHtlc s = some s' → s = .released)
```

**Hypotheses.** One recipient, one invoice slot, one HTLC; `auth` abstracts
the authenticated onion-message context (`HeldHtlcAvailable` /
`ReleaseHeldHtlc`); no crash or restart between transitions; `releaseHtlc`
does not model the upstream HTLC's actual claim/fail. The state machine is a
safety skeleton, not a liveness result: a recipient that stays offline forever
leaves the HTLC held, and `F16.FairlyScheduled` would be needed for eventual
release.

**Non-vacuity witnesses.** (a) `invoiceServed -> htlcHeld -> released ->
claimed` is a five-state path. (b) `releaseHtlc .htlcHeld false = none`.
(c) `releaseHtlc .released true = none` (double release). (d)
`claimHtlc .htlcHeld = none`. (e) `receiveAsync` with
`staticInvoicePersisted = false` returns `none` (negative witness).

**Why faithful.** It mirrors the message flow in `async_payments.rs:40-238`
and the role/hold configuration in `builder.rs:2149-2156`, and it preserves
the "no claimant proof" fact separately (T6). **Fidelity risk.** High: the
real flow spans a static-invoice server, an LSP, and an often-offline
recipient; `releaseHtlc` authorization is a cryptographic/onion assumption,
not a Bool. Do not use this target to claim that an async payment is safe
against a malicious LSP or that a held HTLC cannot be double-released by two
messages; those need a message-history model.

### T6 — `LnLean.Proofs.Payment.AsyncPaymentTargets.staticInvoice_no_recipient_only_preimage`

**Priority:** P2. **Classification:** external assumption / anti-overclaim
lemma, not a proof of a protocol property. **Feasibility:** low as a theorem;
high as a documentation constraint.

**Statement shape (schema-level negative result).**

```lean
structure StaticInvoice where
  paymentHash : PaymentHash
  recipientId : RecipientId
  invoiceSlot : Nat
  serverSecret : ServerSecret

-- Schematic: the real derivation uses a server-held secret, not the
-- recipient's preimage. The exact hash function is an external assumption.
def StaticInvoice.derivedHash (s : StaticInvoice) : PaymentHash := ...

theorem staticInvoice_no_recipient_only_preimage
    (s : StaticInvoice) (sha256 : Preimage → PaymentHash)
    (hderived : s.paymentHash = s.derivedHash)
    (hno : ¬ RecipientCanDerive s.recipientId s.invoiceSlot s.serverSecret) :
    ¬ ∃ p : Preimage,
      RecipientCanKnow p ∧ sha256 p = s.paymentHash
```

**Hypotheses.** `RecipientCanDerive` and `RecipientCanKnow` are explicit
abstract predicates, not cryptographic facts. The theorem is only as strong
as the assumption that the static-invoice hash depends on a server secret the
recipient does not know. **Non-vacuity witnesses.** A BOLT 11 invoice with a
recipient-known preimage satisfies the positive analogue; a static invoice
whose hash is `H(recipient_id, slot, server_secret)` with the secret withheld
does not. **Why faithful.** It records `event.rs:146-155` and prevents a
future lane from reusing `Invoice.preimageCommits` (`Invoice.lean:285-287`)
for static invoices. **Fidelity risk.** Very high; this must not be presented
as a cryptographic theorem. If it cannot be stated without inventing a key
model, keep it as an explicit external note and do not add a theorem.

### T7 — `LnLean.Proofs.Routing.TrampolineTargets.trampoline_feature_gate`

**Priority:** P2. **Classification:** model extension for the feature bit;
external for the protocol. **Feasibility:** trivial for the bit, not feasible
for a trampoline path model from the pinned sources.

**Statement shape.**

```lean
namespace LnLean.Proofs.Routing.TrampolineTargets

def trampolineFeature : Nat := 57

def supportsTrampoline (f : FeatureVector) : Bool :=
  f.supports trampolineFeature

theorem trampoline_required_implies_supported
    (f : FeatureVector)
    (h : f.requires trampolineFeature = true) :
    supportsTrampoline f = true

theorem trampoline_optional_implies_supported
    (f : FeatureVector)
    (h : f.offersOptional trampolineFeature = true) :
    supportsTrampoline f = true

/-- The named summary target: both the required and optional bit-57 forms
imply `supportsTrampoline`. -/
theorem trampoline_feature_gate (f : FeatureVector) :
    (f.requires trampolineFeature = true → supportsTrampoline f = true) ∧
    (f.offersOptional trampolineFeature = true → supportsTrampoline f = true)

-- There is deliberately no `trampoline_advertisement_is_not_a_route`
-- theorem: the model has no `TrampolineRoute` carrier, and a `True`
-- placeholder would be vacuous.
```

The useful content is the bit-57 instantiation and the explicit statement
that the pinned sources provide no trampoline path construction.
**Non-vacuity witness.** `f` with bit 57 set
and all other bits false satisfies `supportsTrampoline`; `f` with bit 56 set
does not. **Fidelity risk.** Low for the bit, very high for any attempt to
model multi-HTLC trampoline forwarding from `event.rs:186-194` alone. Treat
the latter as external.

## 5. Assumptions, counterexamples, and non-vacuity risks

### 5.1 Existing results that must not be weakened

* **`Onion.peel_deterministic` and the `D25` counterexample.** Raw `peel` is
  structural and bypasses HMAC (`Onion.lean:264`, `:498-527`;
  `LnLean/Proofs/WaveD/D25.lean`). A new onion-message model must not redefine
  `peel` to consult an HMAC or delete `waveD_d25_peel_bypasses_hmac`.
* **`Onion.hmac_sound`.** It is a statement about `openLayer`, not `peel`
  (`Onion.lean:529-545`). Do not restate it as "invalid HMAC implies the
  packet is not forwarded" without the `openLayer` premise.
* **`Invoice.signature_valid` / `signatureOnly_no_preimage`.** Signature
  validity is not payment (`LN-PM-002`; `InvoiceWireTargets.lean:1108-1145`).
  Do not use it as a static-invoice proof.
* **`Invoice.amountSatisfies`.** The BOLT 11/BOLT 4 rule is
  `a <= paid <= 2*a` (`Invoice.lean:277-282`). BOLT 12
  `send_using_amount` is `offer_amount <= paid` with no upper bound
  (`bolt12.rs:137-151`). Reusing the BOLT 11 predicate for BOLT 12 would be a
  silent weakening/strengthening error.
* **`MPP.settle` exact sum.** `LN-PM-004`/`LN-PM-005` intentionally require
  an exact sum, while BOLT 4 permits `>= total_msat`; R12 retains the
  counterexample. Do not "fix" it by weakening the existing theorem.
* **`F16` unfair-schedule safety.** `dropAllSchedule` /
  `dropAllAdversary` (`F16.lean:245-254`) witness that the safety theorem does
  not assume delivery. Do not add a fairness hypothesis to the existing
  theorem; state a separate liveness target if needed.
* **`RouteBlindingProps` structural non-interference.** `exposed_realNode_irrelevant`
  and `exposedWire_eq_of_exposed_hops` (`:455-500`) are structural, not
  cryptographic unlinkability. Do not cite them as ECDH/AEAD privacy.

### 5.2 New assumptions that must stay explicit

* **Fatal-error classification.** T1's `fatal` set is a reading of
  `unified.rs:331-376`; if LDK changes the classification, the theorem must be
  re-parameterised.
* **Amount width.** T2's `2^64 - 1` bound is the implementation's `u64`, not
  a BOLT-wide axiom. `Nat` arithmetic alone cannot express the rejection.
* **TLV canonicality.** T3's list model needs a `CanonicalPayloads`
  hypothesis (no duplicate records, sorted types) or a `Wire.TLV`-based
  representation. Without it, the "at most one payload" theorem is about a
  list, not a TLV stream.
* **`path_id` history.** T4's `published` list is a local history. A
  `path_id` equality is not an authentication proof; the onion layer's
  blinded-path context is the external assumption.
* **Hold/release authentication.** T5's `auth : Bool` stands for a verified
  `HeldHtlcAvailable`/`ReleaseHeldHtlc` context from a blinded path the node
  created. It is not a signature check.
* **Static-invoice key knowledge.** T6's `RecipientCanKnow`/`CanDerive` are
  abstract. Do not present T6 as a cryptographic impossibility result.
* **Trampoline.** Bit 57 is the only pinned fact. BOLT PR 836 is not in the
  pinned BOLT clone; a trampoline path model would be a new specification
  model, not a refinement of an existing one.
* **HRN / BIP 353.** DNS, DNSSEC, LNURL, and the resolution timeout are
  external oracles. A resolved HRN is an input to the unified send, not a
  payment proof.

### 5.3 Non-vacuity plan

Every proposed target must ship at least one concrete inhabitant and one
negative witness:

| Target | Positive witness | Negative witness |
|---|---|---|
| T1 | `[.bolt12, .bolt11]` with benign/sent outcomes | fatal at BOLT 12 never calls on-chain |
| T2 | `sats = 100000`, both components present | `sats * 1000 > 2^64 - 1` rejects |
| T3 | final `invoiceRequest` + `replyPath` admitted | two payload fields rejected |
| T4 | published `path_id` + `isReply` admitted | same `path_id` + `isReply = false` rejected |
| T5 | `invoiceServed -> htlcHeld -> released -> claimed` | double release / claim before release rejected |
| T6 | BOLT 11 recipient-known preimage (positive analogue) | static invoice with server-secret hash |
| T7 | bit 57 set | bit 56 set does not satisfy `supportsTrampoline` |

The non-vacuity witnesses must be definitions or `example` theorems in the
same module, not comments. If a target cannot produce a negative witness, it
is probably a restatement of its definition.

### 5.4 Claims that must not be made

* Do not claim BOLT 12 is covered because `docs/ANCHORS-GENERATED.md:131`
  names it; the anchor is false (`Invoice.lean:98`).
* Do not claim onion-message reliability or error reporting; BOLT 4
  `:1715-1718` says the opposite.
* Do not claim static-invoice payer proofs; `event.rs:151-155` says the hash
  is not recipient-preimage-derived.
* Do not claim trampoline routing from feature bit 57 or from the
  `PaymentForwarded` multi-HTLC report.
* Do not claim ECDH/AEAD/privacy from the structural `BlindedPath`; R09 owns
  that external gap.
* Do not claim BIP 353 resolution is authenticated by Lean; DNSSEC is
  external.

## 6. Wave-13 recommendation

`agents/reports/swarm12/S12-POST-INTEGRATION-AUDIT.md` §4 says no wave-13
proof lane is launched and the only proposed model extension is the typed
digest change. This lane does not overturn that decision. If the parent
reopens a bounded wave-13/14 lane, the recommendation is:

* **Implement now (P0, safe): T1 and T2.** Both are pure list/arithmetic
  models with no new cryptography, no TLV decoder, and no store dependency.
  Put them in one new module,
  `LnLean/Proofs/Payment/UnifiedPaymentTargets.lean`, with the non-vacuity
  witnesses inline. Do not add a catalog row unless the parent explicitly
  asks for one; the catalog is already 51/51 and this is a target, not an
  obligation.
* **Implement next (P1, after R09/R11 substrate): T3 and T4.** They need a
  canonical `onionmsg_tlv` representation shared with R09's TLV work and
  R11's offer/invoice dispatch. Do not duplicate either lane's schema.
* **Defer (wave 14): T5.** The hold/release state machine is small, but its
  connection to the static-invoice store, the onion mailbox, and the
  authenticated message context is not. A standalone Bool `auth` would
  overclaim safety against a malicious LSP.
* **Treat as external/human barrier: T6 and T7.** T6 is an anti-overclaim
  fact about static-invoice proofs; T7 is a feature-bit instantiation with no
  pinned trampoline specification. Do not create a trampoline path model from
  `event.rs` alone.
* **No catalog retarget.** Do not add BOLT 12/async/trampoline rows to
  `docs/THEOREM-INDEX.md` or `docs/TRACEABILITY.md` in this lane.
* **Top target for the parent:** T1
  `unified_send_no_double_pay`. It is the highest-value bounded safety
  property (the exact regression LDK Node fixed in issue #1033) and the least
  dependent on missing protocol models.

## 7. Evidence and commands

### 7.1 Pins verified

```sh
git -C /tmp/opencode/ldk-refs/ldk-node rev-parse HEAD
# fa123fed131e27ecc420b77fa7086fcf1ddaebb8
git -C /tmp/opencode/ldk-refs/ldk-server rev-parse HEAD
# c17dc11dde38f88c53457039ddf30c6b90a63ba2
git -C /home/ubuntu/ln-lean-repair rev-parse --abbrev-ref HEAD
# repair/integrated
git -C /home/ubuntu/ln-lean-repair rev-parse HEAD
# f7f062817c185cd70004bb26c652deb99c6fd4bd
```

Reference pins used for behavioural anchors:

```sh
git -C /home/ubuntu/ln-lean-repair/refs/rust-lightning rev-parse HEAD
# fe4900930c6bd5786ec4203274d7cf312776a5a6
git -C /home/ubuntu/ln-lean-repair/refs/bolts rev-parse HEAD
# 1aadb719b4007c4cea0ba6e36b08c4fb53788dee
```

LDK Node's rust-lightning dependency is pinned at
`d7a980641c6325ddda5072a0f470ef8392676cf5` in
`/tmp/opencode/ldk-refs/ldk-node/Cargo.toml:89-100`. LDK Server's
`Cargo.lock:1382-1384` pins `ldk-node` at
`179b4b263762155a7ff515ddad7e757a80807fd5`.

### 7.2 Lean surface searches

```sh
rg -n "trampoline|async payment|async_payments|bolt12|BOLT 12|offer|unified|onion_message|static_invoice|hrn" LnLean/
# no model carriers; matches are comments, "offered" HTLC prose, and the
# out-of-scope sentence at LnLean/Payment/Invoice.lean:98

rg -n "BOLT 12|bolt12|offer" docs/THEOREM-INDEX.md docs/TRACEABILITY.md docs/SCOPE.md docs/ASSUMPTIONS.md
# docs/SCOPE.md:24 out of scope; docs/ASSUMPTIONS.md:144 future work;
# no catalog row

rg -n "theorem|structure|def" LnLean/Routing/Onion.lean
rg -n "BlindedPath|BlindedHop|theorem" LnLean/Proofs/Routing/RouteBlindingProps.lean
rg -n "structure FeatureVector|def supports|def requires" LnLean/Proofs/Protocol/FeaturesProps.lean
rg -n "structure AsyncSystem|def run|AsyncInvariant|FairlyScheduled" LnLean/Proofs/ModelHardening/F16.lean
```

### 7.3 LDK evidence commands

```sh
sed -n '135,412p' /tmp/opencode/ldk-refs/ldk-node/src/payment/unified.rs
sed -n '467,551p' /tmp/opencode/ldk-refs/ldk-node/src/payment/unified.rs
sed -n '126,300p' /tmp/opencode/ldk-refs/ldk-node/src/payment/bolt12.rs
sed -n '635,692p' /tmp/opencode/ldk-refs/ldk-node/src/payment/bolt12.rs
sed -n '2140,2160p' /tmp/opencode/ldk-refs/ldk-node/src/builder.rs
sed -n '146,194p' /tmp/opencode/ldk-refs/ldk-node/src/event.rs
sed -n '2468,2560p' /tmp/opencode/ldk-refs/ldk-node/src/event.rs
sed -n '1,64p' /tmp/opencode/ldk-refs/ldk-node/src/payment/asynchronous/om_mailbox.rs
sed -n '60,155p' /tmp/opencode/ldk-refs/ldk-node/src/payment/asynchronous/static_invoice_store.rs
sed -n '4882,5015p' /tmp/opencode/ldk-refs/ldk-node/tests/integration_tests_rust.rs
sed -n '5113,5171p' /tmp/opencode/ldk-refs/ldk-node/tests/integration_tests_rust.rs
sed -n '5260,5418p' /tmp/opencode/ldk-refs/ldk-node/tests/integration_tests_rust.rs
sed -n '20,41p' /tmp/opencode/ldk-refs/ldk-server/ldk-server/src/api/unified_send.rs
sed -n '1700,1840p' /home/ubuntu/ln-lean-repair/refs/bolts/04-onion-routing.md
sed -n '23,238p' /home/ubuntu/ln-lean-repair/refs/rust-lightning/lightning/src/onion_message/async_payments.rs
rg -n "Trampoline|57" /home/ubuntu/ln-lean-repair/refs/rust-lightning/lightning-types/src/features.rs
```

### 7.4 Read-only constraints observed

No Lean, docs, scripts, tests, vendor, or other lane report was edited. No
cargo test or whole-tree build was run. The only write is this report.
