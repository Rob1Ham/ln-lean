# R24 — LDK Server payment, channel, and on-chain API semantics
**Status:** read-only review
**Pins:** LDK Node `fa123fed131e27ecc420b77fa7086fcf1ddaebb8`, LDK Server `c17dc11dde38f88c53457039ddf30c6b90a63ba2`

Review tip: `f7f062817c185cd70004bb26c652deb99c6fd4bd` (`repair/integrated`).
No Lean, catalog, test, vendor, or other-lane file was modified. Commands are
listed in §7; no `lake build`, no `cargo test`, and no network access.

---

## 1. Scope and current Lean surface

### 1.1 What the catalog currently claims

The catalog has no LDK Server API row. Its payment and channel rows are
protocol/invariant claims:

| Row | Target(s) | What is actually stated |
|---|---|---|
| `LN-PM-001`–`003` | `Invoice.consistent_hash`, `Invoice.consistent_amount`, `Invoice.signature_valid`, `Invoice.payment_secret_match` | Invoice construction, signature, and payment-secret binding (`LnLean/Proofs/Obligations.lean:357-376`; `docs/THEOREM-INDEX.md:74-76`). |
| `LN-PM-004` | `MppPayment.settle_requires_sum` | A **standalone** `MppPayment.settle` returns `some` only when `partsSum = total` (`LnLean/Security/Invariants.lean:440-454`; catalog wording at `LnLean/Proofs/Obligations.lean:377-381`). |
| `LN-PM-005` | `MPP.running_total_bound` | An exact-sum plan has every prefix at or below the target (`LnLean/Payment/MPP.lean:169-180`). |
| `LN-PM-006`–`007` | keysend preimage binding, invoice field-list codec | Neither is a server payment-record or retry claim (`LnLean/Proofs/Obligations.lean:389-400`). |
| `LN-CH-001`–`007` | ledger, commitment, reserve, HTLC, fee, aggregate coverage | Channel mechanics, not the `ListChannels` projection (`LnLean/Proofs/Obligations.lean:168-217`). |
| `LN-PR-001`–`006` | open-channel routing/auth, `channel_ready_gate`, reestablish, features | Peer-protocol claims; `channel_ready_gate` is only `HandshakeState.ready` (`LnLean/Proofs/WaveD/D18.lean:331-336`). |

The catalog is green at those scopes (`docs/THEOREM-INDEX.md:74-80`,
`docs/TRACEABILITY.md:53-59`). It does **not** claim that a server payment
record is absorbing, that a server send is duplicate-free, that a claim amount
is exact, that `list_channels.is_usable` follows from `phase = normal`, or
that on-chain RBF preserves the recipient.

### 1.2 Carriers actually present

1. **Outbound session carrier** — `LnLean/Payment/HTLC.lean`
   * `PaymentState` is `pending | succeeded | failed` (`:64-69`).
   * `PaymentSession` has hash, target, parts, state (`:102-108`).
   * `settle` is a no-op on any terminal state (`:132-153`), mechanized as
     `settle_terminal` (`:148-153`).
   * The module says it models LDK's outbound state machine reduced to three
     states (`:6-13`), but it has no `PaymentId`, store, direction, kind,
     timestamp, fee, or event layer. The preimage is deliberately absent
     (`:46-53`).
2. **Conservative MPP carrier** — `LnLean/Payment/MPP.lean`
   * `mppComplete` is non-empty and **exact-sum** (`:141-146`); the module
     explicitly notes BOLT 4 permits `sum ≥ total` and records the overpay
     obligation as future work (`:59-69`).
   * `MppPayment.settle` is the standalone exact-sum settlement
     (`LnLean/Security/Invariants.lean:425-454`).
3. **Invoice amount window** — `Invoice.amountSatisfies` is the BOLT 4
   `a ≤ paid ≤ 2*a` window (`LnLean/Payment/Invoice.lean:273-280`;
   exact characterization at `LnLean/Proofs/Payment/InvoiceProps.lean:228-241`).
   This is a receiver-side window, not the server's send-amount rule.
4. **Channel lifecycle carrier** — `Channel` has `channelId`, funding outpoint,
   value, endpoints, one `phase`, commitment counters, balances, HTLCs
   (`LnLean/Channel/Types.lean:159-175`). `Step` has one `fundingLocked` event
   from `awaitingLockin` to `normal` (`LnLean/Channel/State.lean:86-127`);
   `shutdown` requires `normal` and `closingSigned` requires `shuttingDown`
   (`:122-127`); nothing follows `closed` (`:178-182`). There is no
   confirmations field, peer-connected bit, `is_channel_ready`, `is_usable`,
   shutdown-state projection, user channel id, or force-close transition.
5. **Open-channel wire vs projection** — `OpenChannelWire` carries
   `channelFlags` and `channelReserveSatoshis`
   (`LnLean/Protocol/Messages.lean:102-139`), but `Handshake.OpenChannel`
   deliberately drops `channel_flags` and the reserve
   (`LnLean/Protocol/Handshake.lean:835-849`). The zero-reserve API mode has no
   Lean carrier.
6. **Handshake readiness** — `HandshakeState.ready` means both
   `channel_ready` flags are set (`LnLean/Protocol/Handshake.lean:111-130`),
   and `channel_ready_gate` restates that (`LnLean/Proofs/WaveD/D18.lean:331-336`).
   There is no theorem linking it to `Channel.phase = normal`. In fact the
   channel model admits a two-event trace to `normal` that omits
   `fundingSigned` (`LnLean/Proofs/Channel/StateMachineProps.lean:361-389`).
7. **No on-chain payment carrier** — no `OnchainPayment`, `PaymentId`-vs-`Txid`
   record, RBF transition, or recipient-preservation theorem exists.

### 1.3 Negative surface (searched, not assumed)

`rg -ni` over `LnLean/**/*.lean` finds no `PaymentDetails`, `PaymentStore`,
`LdkServerApi`, `claim_for_id`, `fail_for_id`, `is_usable`,
`channel_shutdown_state`, `disable_counterparty_reserve`, `user_channel_id`,
`bump_fee_rbf`, or server `ListPayments`/`ListChannels` model. `channelFlags`
exists only as a wire/gossip bit, not as the server open-mode matrix.

Consequently this is a **missing-surface review**, not a repair of a false
catalog theorem. The one place where a projection of an existing carrier would
be false is the absorbing `PaymentSession.settle` versus the server's
unconditional status overwrite (§2.1 D5/D6, §3 row 6).

---

## 2. LDK datapoints (with `file:line`)

Paths below are relative to `/tmp/opencode/ldk-refs/ldk-server` unless prefixed
with `ldk-node/`.

### 2.0 First-class finding: the server's node pin is not the review pin

LDK Server `c17dc11d…` depends on ldk-node
`179b4b263762155a7ff515ddad7e757a80807fd5`, not the review's `fa123fed…`:

* `ldk-server/Cargo.toml:16`;
* `ldk-server/Cargo.lock:1384`;
* e2e lock at `e2e-tests/Cargo.lock:1298`.

The review clone cannot resolve that revision:
`git -C /tmp/opencode/ldk-refs/ldk-node cat-file -e
179b4b2…^{commit}` exits 128. This is not cosmetic. The server calls a
**three-argument** `claim_for_id(payment_id, claimable_amount_msat, preimage)`
at `ldk-server/src/api/bolt11_claim_for_id.rs:34`, while the review-pinned node
exposes a **two-argument** `claim_for_id(payment_id, preimage)` at
`ldk-node/src/payment/bolt11.rs:424-426`. The exact amount-check implementation
in the server's node revision therefore cannot be source-grounded from the
provided clones.

Every `[node:fa]` row below is evidence from the review clone, not proof about
the server's `179b4b2` dependency. Server handlers, proto contracts, and e2e
tests are pinned-server evidence; they are marked `[server]`.

### 2.1 Payment API

| # | Behaviour | Datapoint | Citation |
|---|---|---|---|
| D1 | `Bolt11Send` selects `send` when `amount_msat` is absent and `send_using_amount` when present; returns the node payment id. | `handle_bolt11_send_request` | `ldk-server/src/api/bolt11_send.rs:23-39` |
| D2 | `Bolt11SendUnderpaying` is a separate RPC and calls `send_using_amount_underpaying` with a required amount. | handler | `ldk-server/src/api/bolt11_send.rs:42-57`; proto `ldk-server-grpc/src/proto/api.proto:386-408` |
| D3 | Explicit send amount must be at least the fixed invoice amount; overpay is allowed. Underpaying requires a fixed-amount invoice and `amount < invoice_amount`. | `[node:fa]` `send_using_amount`, `send_using_amount_underpaying` | `ldk-node/src/payment/bolt11.rs:335-360`, `:362-405` |
| D4 | The proto's amount rule is a **lower bound** on explicit send, and underpaying must be strictly below the invoice amount. | request docs | `api.proto:369-372`, `:386-396` |
| D5 | BOLT 11 `PaymentId` is the invoice payment hash. The duplicate guard rejects only `Pending` and `Succeeded`; `Failed` is admitted, then `insert(Pending)` overwrites the record. | `[node:fa]` send path | `ldk-node/src/payment/bolt11.rs:207-215`, `:257-266`; overwrite `ldk-node/src/data_store.rs:346-353` |
| D6 | A synchronous send failure inserts a `Failed` record and then returns `PaymentSendingFailed`; `DuplicatePayment` is a separate error. | `[node:fa]` send failure | `ldk-node/src/payment/bolt11.rs:274-297`; server error mapping `ldk-server/src/api/error.rs:107-123` |
| D7 | The server handler propagates the send error with `?`, so a failed send can both leave a record and return a gRPC error. The e2e test verifies that a no-route send leaves a BOLT 11 record; it does **not** assert the record's status. | e2e | `e2e-tests/tests/e2e.rs:601-613` |
| D8 | `PaymentDetails` has optional amount/fee, direction, status, and update timestamp. Status update is a plain overwrite, not a transition relation. | `[node:fa]` store | `ldk-node/src/payment/store.rs:60-91`, `:335-337` |
| D9 | `PaymentSent` writes `Succeeded` unconditionally. Late `PaymentFailed` is ignored only for outbound Lightning payments already `Succeeded`. | `[node:fa]` event handling | `ldk-node/src/event.rs:1550-1564`, `:1609-1622` |
| D10 | `Bolt11FailForId` parses a 32-byte id and calls `fail_for_id`; the node checks only that the record exists and is a BOLT 11 payment, then writes `Failed` **before** calling `fail_htlc_backwards`. There is no status or direction guard. | `[server]` handler; `[node:fa]` fail path | `ldk-server/src/api/bolt11_fail_for_id.rs:17-24`; `ldk-node/src/payment/bolt11.rs:477-531` (status write `:504-509`, channel action `:530`) |
| D11 | `Bolt11ClaimForId` parses a 32-byte id and a 32-byte hex preimage; an omitted amount becomes `u64::MAX`, i.e. the amount check is skipped. | `[server]` handler | `ldk-server/src/api/bolt11_claim_for_id.rs:20-34` |
| D12 | The proto states the claim amount is **not** exact: values below the stored amount less any skimmed fee are rejected, larger values pass, and omission skips the check. | proto contract | `api.proto:218-235` (especially `:226-231`) |
| D13 | The pinned node's claim path checks known payment, BOLT 11 kind, and `SHA256(preimage) = payment_hash`, then calls `claim_funds`; it does not check status or direction. | `[node:fa]` | `ldk-node/src/payment/bolt11.rs:424-465` |
| D14 | E2E rejects a wrong preimage and an amount one millisecond below the 10,000,000 msat claimable amount. | `[server]` e2e | `e2e-tests/tests/e2e.rs:2079-2095` |
| D15 | Unknown manual-fail id is an `InvalidRequestError`; manual fail does not require HTLC expiry. | `[server]` e2e and proto | `e2e-tests/tests/e2e.rs:2155-2162`; `api.proto:240-250` |
| D16 | The receive RPCs separate auto-claim (`Bolt11Receive`) from manual claim/fail (`Bolt11ReceiveForHash`); the latter is explicitly manual. | proto comments | `api.proto:151-190` |
| D17 | BOLT 4 completes basic MPP when the set total is at least `total_msat`; it does not require exact equality. | protocol | `refs/bolts/04-onion-routing.md:382-404` |
| D18 | LDK's underpaying send declares the invoice total but sends less; this is an extension requiring a receiver configured to accept underpaying HTLCs. | `[node:fa]` docs | `ldk-node/src/payment/bolt11.rs:362-405` |

### 2.2 Channel API

| # | Behaviour | Datapoint | Citation |
|---|---|---|---|
| D19 | `OpenChannel` requires a node pubkey, address, and exactly one amount (channel amount or all funds). | handler/proto | `ldk-server/src/api/open_channel.rs:23-36`; `api.proto:576-594`; `ldk-server/src/api/mod.rs:67-74` |
| D20 | `announce_channel` and `disable_counterparty_reserve` are independent request flags, and setting both is rejected with `InvalidRequestError`. All other three combinations dispatch to distinct node constructors. | handler | `ldk-server/src/api/open_channel.rs:38-89` (rejection `:83-88`); proto `api.proto:602-606` |
| D21 | BOLT 2 `channel_flags` bit 0 is `announce_channel`; the zero-reserve mode is not this bit. | BOLT 2 | `refs/bolts/02-peer-protocol.md:769-770`; the wire record `LnLean/Protocol/Messages.lean:135-136` |
| D22 | `CloseChannel` takes a decimal `user_channel_id` and a counterparty node id, parses both, and calls `close_channel`; `ForceCloseChannel` is a separate RPC with an optional reason. | handler/proto | `ldk-server/src/api/close_channel.rs:23-47`; `api.proto:698-724` |
| D23 | `ListChannels` projects `confirmations_required`, `confirmations`, `is_outbound`, `is_channel_ready`, `is_usable`, `is_announced`, `channel_shutdown_state`, and more from `ChannelDetails`. | server projection | `ldk-server/src/util/proto_adapter.rs:103-152`; handler `ldk-server/src/api/list_channels.rs:18-24` |
| D24 | Proto semantics: `is_channel_ready` means both parties exchanged `channel_ready` and the channel is not shutting down; `is_usable` is a **strict superset** that also requires the peer to be connected and no shutdown negotiation. | proto docs | `ldk-server-grpc/src/proto/types.proto:583-593`; shutdown state `:671-674` |
| D25 | BOLT 2 says the accepter should wait for `minimum_depth` before sending `channel_ready`; a channel can therefore be funded/negotiating and not ready at zero confirmations. | BOLT 2 | `refs/bolts/02-peer-protocol.md:1050-1073` |

### 2.3 Payment listing, lookup, and on-chain API

| # | Behaviour | Datapoint | Citation |
|---|---|---|---|
| D26 | `ListPayments` passes an opaque `page_token` to the node and returns the node's `next_page_token`. | server handler | `ldk-server/src/api/list_payments.rs:19-29` |
| D27 | The pagination contract is opaque: omitted token means first page; a non-`None` next token does not by itself prove more records exist; clients must not assume a page size. | proto contract | `api.proto:751-783` |
| D28 | `GetPaymentDetails` parses a 32-byte id and returns an optional payment (`None` if absent). | handler/proto | `ldk-server/src/api/get_payment_details.rs:18-26`; `api.proto:737-749` |
| D29 | Payment ids are parsed as fixed-width hex; a bad length or non-hex value is an invalid request. | parser | `ldk-server/src/api/mod.rs:86-94` |
| D30 | `OnchainSend` validates the address against the configured network, rejects a zero fee rate, requires amount or all-funds, and returns a txid. | handler/proto | `ldk-server/src/api/onchain_send.rs:25-45`; `ldk-server/src/api/mod.rs:67-84`; `api.proto:104-130` |
| D31 | `OnchainBumpFee` takes a payment id (not a txid) and an optional absolute fee rate; only unconfirmed outbound on-chain non-channel-funding payments are eligible, the fee must rise, and the recipient amount is preserved. | handler/proto; `[node:fa]` wallet | `ldk-server/src/api/onchain_bump_fee.rs:18-24`; `api.proto:132-149`; `ldk-node/src/wallet/mod.rs:3371-3505` (guards `:3379-3492`, fee `:3497-3514`) |
| D32 | E2E checks that a lower fee is rejected, a higher fee replaces the transaction, the recipient output value is unchanged, and the old tx leaves the mempool. | `[server]` e2e | `e2e-tests/tests/e2e.rs:495-524`; `e2e-tests/src/lib.rs:904-919` |
| D33 | E2E asserts `payment.payment_id != original_txid` for one random transaction; this is a sample, not a universal byte-order law. | `[server]` e2e | `e2e-tests/tests/e2e.rs:492-493` |

---

## 3. Gap matrix

Legend: **C** covered faithfully, **P** partially covered, **M** missing,
**X** contradicted at a stated projection, **E** unmodelled/external.
Priority is about a future server/API lane, not an existing catalog failure.

| Behavior | Lean status | LDK evidence | Gap / counterexample | Priority |
|---|---|---|---|---|
| Node pin used by the server | **M** (evidence defect) | D0; `ldk-server/Cargo.toml:16`, `Cargo.lock:1384` | Server uses ldk-node `179b4b2…`; review clone is `fa123fed…`. The `claim_for_id` arities differ. No implementation-level server-API theorem is source-grounded until the pins match. | **P0** for any server conformance claim |
| Send amount modes (invoice / explicit / underpaying) | **M** | D1–D4 | Lean has invoice amount and an `amountSatisfies` receiver window, but no API mode relation. The server's explicit amount is a floor; underpaying is a separate extension. | P1 |
| Explicit send above `2*invoice` | **P** | D3–D4; `Invoice.amountSatisfies` at `Invoice.lean:277-280` | The send handler enforces only `amount >= invoice`; the model's receiver window is `invoice <= paid <= 2*invoice`. A payload of `2*invoice + 1` is accepted by the send path but fails `amountSatisfies`. This is a projection mismatch, not a false invoice theorem. | P1 |
| Duplicate send and retry after failure | **M** (lifecycle), **X** for `Keysend.retry` if reused as a server retry | D5; `LnLean/Proofs/Payment/KeysendProps.lean:249-255`, `:299-301` | The node rejects only `Pending`/`Succeeded`; `Failed` is retryable and `insert` overwrites. The existing `Keysend.retry` resets **any** state, including `succeeded`, and `retry_pending` proves it. R12 owns the store/duplicate target; do not duplicate it in R24. | P1 |
| Failed send still records a payment | **M** | D6–D7 | Lean has no store and no “error returned, record retained” state. `PaymentSession.settle` can model a failed attempt, but it has no payment id or persistence. The e2e test proves only that a record exists. | P1 |
| Payment status projection and status regression | **X** at the projection boundary | D8–D10, D12–D13; `LnLean/Payment/HTLC.lean:132-153` | `fail_for_id` writes `Failed` unconditionally, before the HTLC action, with no status or direction guard. A `Succeeded` BOLT 11 record becomes `Failed`; `PaymentSent` likewise writes `Succeeded` without a transition guard. `PaymentSession.settle` is absorbing: `settle_terminal` proves a `Succeeded` session cannot become `Failed`. Any theorem that projects `settle` to the API status is therefore contradicted. | **P1, top** |
| Manual fail vs HTLC timeout | **P / ambiguous** | D10, D15; `LnLean/Security/Invariants.lean:231-240` | `HtlcRecord.fail` requires `cltvExpiry ≤ height`; the API manual fail does not require expiry and only rejects unknown/non-BOLT11 ids. The model has no explicit “claim rejected” transition. Do not use `HtlcRecord.fail` as the manual-fail model. | P1 |
| Claim preimage check | **C conditional** | D11–D14 | The `SHA256(preimage) = payment_hash` relation is the same shape as `HtlcRecord.fulfill_sound` (`Invariants.lean:220-229`), but the server claim is a record-level operation with no status/direction guard. The binding is covered; the API transition is not. | P2 |
| Claim amount is a lower bound, not exact | **M / X if `MppPayment.settle` is used as the claim gate** | D11–D14, D17 | Omitted amount becomes `u64::MAX`; larger values pass; one-below is rejected. The model's only settlement rule is exact-sum. An overpay claim is accepted by the API but rejected by an exact gate. | P1 |
| Inbound receive auto-claim vs manual claim | **M** | D16; `LnLean/Payment/HTLC.lean:46-53` | No inbound claim state, no `PaymentClaimable`, no “auto-claimed” mode. The session carrier is outbound-only in its preimage/claim story. | P2 |
| `ListPayments` pagination / `GetPaymentDetails` lookup | **M** | D26–D29 | No payment store, page token, or optional-lookup model. The opaque-token contract is not an ordered-list slice and cannot be assumed to be one. | P2 |
| Open-channel mode matrix | **M** | D19–D21 | The API forbids `announce_channel ∧ disable_counterparty_reserve`; `OpenChannelWire` carries `channelFlags`/reserve but `Handshake.OpenChannel` drops both. No Lean relation states the forbidden pair. | P2 |
| Close-channel identity and force close | **M** | D22; `LnLean/Channel/State.lean:122-127`, `:178-182` | The API requires `(user_channel_id, counterparty_node_id)`; Lean identifies by `ChannelId`/funding outpoint and has no user id or force-close event. `no_step_from_closed` is a peer-protocol result, not the API lookup/error behavior. | P2 |
| `ListChannels` readiness/usable projection | **X at the projection boundary** | D23–D25; `LnLean/Channel/Types.lean:159-175`; `LnLean/Channel/State.lean:99-101` | The API exposes `confirmations`, `is_channel_ready`, `is_usable`, and shutdown state. Lean `Channel.phase = normal` has no confirmations or peer-connectivity information; a model cannot derive `is_channel_ready` or `is_usable` from it. `fundingLocked` is a single event to `normal`, not evidence of both `channel_ready` messages. | P1 |
| MPP exact-sum claim vs BOLT 4 `sum ≥ total` | **P (conservative)** | D17–D18; `LnLean/Payment/MPP.lean:141-146`; `LnLean/Security/Invariants.lean:440-454` | `mppComplete` and `MppPayment.settle` require equality, while BOLT 4 fulfils at `≥ total_msat`. The exact theorem is true of its carrier, but the catalog English claim is narrower than the protocol. R12 T5 already proposes the additive `settleGe` repair. The LDK underpaying send is a **different** extension (declare full total, send less), not evidence for overpay. | P1 |
| On-chain send/receive | **E** | D30 | No wallet/UTXO/balance carrier in this model; R04 owns the wallet surface. | P2 |
| On-chain RBF and recipient preservation | **E** | D31–D33 | No on-chain payment record, payment-id/txid distinction, unconfirmed/outbound/funding guards, or replacement transition. The e2e `payment_id != txid` assertion is a sampled observation and must not become a universal theorem. | P2 |

Summary: the green catalog is not wrong about its own carriers. The material
delta is that the server has a **mutable payment record** and a **channel
projection** with more state than the Lean carriers. The sharpest concrete
contradiction is `fail_for_id` status regression versus `settle_terminal`; the
largest missing surfaces are the payment store and the channel view.

---

## 4. Proposed targets

All targets are additive. Proposed location:
`LnLean/Proofs/Protocol/LdkServerApiTargets.lean` (new module; one root import
when accepted). None changes `PaymentSession.settle`, `MppPayment.settle`,
`mppComplete`, `HtlcRecord.fail`, `Step`, `channel_ready_gate`, or any existing
theorem.

### T1 — `failForId_regresses_succeeded` (P1, top target)

**Proposed names**

```lean
LnLean.Proofs.Protocol.LdkServerApiTargets.ApiPaymentKind
LnLean.Proofs.Protocol.LdkServerApiTargets.PaymentRecord
LnLean.Proofs.Protocol.LdkServerApiTargets.markFailed
LnLean.Proofs.Protocol.LdkServerApiTargets.paymentSessionOfRecord
LnLean.Proofs.Protocol.LdkServerApiTargets.failForId_regresses_succeeded
LnLean.Proofs.Protocol.LdkServerApiTargets.recordFail_neq_settle
```

**Statement shape**

```lean
inductive ApiPaymentKind where
  | bolt11
  | other

structure PaymentRecord where
  id     : PaymentHash
  kind   : ApiPaymentKind
  status : PaymentState

def markFailed (r : PaymentRecord) : PaymentRecord :=
  { r with status := .failed }

def paymentSessionOfRecord (r : PaymentRecord) : PaymentSession :=
  { paymentHash := r.id, target := ⟨0⟩, parts := [], state := r.status }

theorem failForId_regresses_succeeded
    (r : PaymentRecord) (hk : r.kind = .bolt11) (hs : r.status = .succeeded) :
    (markFailed r).status = .failed ∧ markFailed r ≠ r

theorem recordFail_neq_settle
    (r : PaymentRecord) (hk : r.kind = .bolt11) (hs : r.status = .succeeded) :
    paymentSessionOfRecord (markFailed r) ≠
      PaymentSession.settle (paymentSessionOfRecord r) .failed
```

**Hypotheses and non-vacuity.** `r := ⟨paymentHash, .bolt11, .succeeded⟩`.
`failForId_regresses_succeeded` is immediate by `rfl`; `recordFail_neq_settle`
uses `PaymentSession.settle_terminal` on the right and observes the changed
left status. The witness satisfies `hk` and `hs`, so the target is not vacuous.

**Why faithful.** The server fail handler checks only that the record exists
and is BOLT 11, then writes `Failed` before the channel action
(`ldk-node/src/payment/bolt11.rs:477-509`; server wrapper
`ldk-server/src/api/bolt11_fail_for_id.rs:17-24`). There is no status,
direction, or `PaymentClaimable` guard. This target is a **negative
divergence theorem**, not a desired invariant; it must not be used to “fix”
`settle`. It gives R12's store status layer a directly named server-side
counterexample.

**Fidelity risk.** Medium only because the target abstracts away kind-specific
event handling; `hk` retains the actual kind guard. The status write itself is
exactly the pinned server/node behavior. `PaymentSent`'s `Failed → Succeeded`
direction is separate and R12 owns it; do not add a second unguarded rewrite
here.

**Feasibility.** High. **Type:** model extension + counterexample. **Priority:**
P1.

---

### T2 — `sendMode_floor_not_bolt4_window` (P1)

**Proposed names**

```lean
LnLean.Proofs.Protocol.LdkServerApiTargets.SendMode
LnLean.Proofs.Protocol.LdkServerApiTargets.SendView
LnLean.Proofs.Protocol.LdkServerApiTargets.SendView.accepted
LnLean.Proofs.Protocol.LdkServerApiTargets.sendMode_floor_not_bolt4Window
LnLean.Proofs.Protocol.LdkServerApiTargets.underpay_requires_below
```

**Statement shape**

```lean
inductive SendMode where
  | invoiceAmount
  | explicit (amount : Nat)
  | underpaying (amount : Nat)

structure SendView where
  invoiceAmount : Option Nat
  mode          : SendMode

def SendView.accepted : SendView → Bool
  | ⟨none,   .invoiceAmount⟩     => false
  | ⟨some _, .invoiceAmount⟩     => true
  | ⟨none,   .explicit _⟩        => false
  | ⟨some a, .explicit p⟩        => a ≤ p
  | ⟨none,   .underpaying _⟩     => false
  | ⟨some a, .underpaying p⟩     => p < a

def bolt4Window (invoice paid : Nat) : Prop :=
  invoice ≤ paid ∧ paid ≤ 2 * invoice

theorem sendMode_floor_not_bolt4Window :
    ∃ v : SendView,
      v.accepted = true ∧ v.invoiceAmount = some 100 ∧
      v.mode = .explicit 300 ∧ ¬ bolt4Window 100 300

theorem underpay_requires_below
    (v : SendView) (a p : Nat)
    (h : v.invoiceAmount = some a) (hm : v.mode = .underpaying p)
    (ha : v.accepted = true) : p < a
```

**Non-vacuity.** The explicit witness is `invoiceAmount = 100`,
`mode = .explicit 300`; `accepted = true` while `bolt4Window 100 300` is false.
The underpaying witness is `100` vs `60`, which satisfies `p < a`.

**Why faithful.** `bolt11_send.rs:31-36` selects the send mode exactly as the
view does; the `[node:fa]` send path requires `amount >= invoice` and permits
overpay (`bolt11.rs:335-360`), while underpaying requires a fixed invoice and
`amount < invoice` (`:362-405`). The target makes the API floor and the
receiver-side BOLT 4 window visibly different. It is not a replacement for
`Invoice.amountSatisfies`; it is the missing send-side relation.

**Fidelity risk.** Medium: this is `[node:fa]` evidence under the server's
different node pin. The server handler itself is pinned and exact. Do not claim
the API rejects `2*invoice + 1`; it only fails to enforce the receiver window.

**Feasibility.** High. **Type:** model extension. **Priority:** P1.

---

### T3 — `claimAmount_lowerBound` (P1, pin-blocked for implementation fidelity)

**Proposed names**

```lean
LnLean.Proofs.Protocol.LdkServerApiTargets.ClaimAmountView
LnLean.Proofs.Protocol.LdkServerApiTargets.ClaimAmountView.minClaimable
LnLean.Proofs.Protocol.LdkServerApiTargets.ClaimAmountView.accepted
LnLean.Proofs.Protocol.LdkServerApiTargets.claimAmount_lowerBound
LnLean.Proofs.Protocol.LdkServerApiTargets.claimAmount_overpay_witness
LnLean.Proofs.Protocol.LdkServerApiTargets.claimAmount_omitted
```

**Statement shape**

```lean
structure ClaimAmountView where
  stored      : Nat
  skimmed     : Nat
  supplied    : Option Nat
  skim_le     : skimmed ≤ stored

def ClaimAmountView.minClaimable (v : ClaimAmountView) : Nat :=
  v.stored - v.skimmed

def ClaimAmountView.accepted (v : ClaimAmountView) : Bool :=
  match v.supplied with
  | none   => true
  | some a => v.minClaimable ≤ a

theorem claimAmount_lowerBound (v : ClaimAmountView) (a : Nat) :
    v.supplied = some a →
      (v.accepted = true ↔ v.minClaimable ≤ a)

theorem claimAmount_overpay_witness :
    ∃ v : ClaimAmountView,
      v.accepted = true ∧ v.supplied = some (v.stored + 1)

theorem claimAmount_omitted (v : ClaimAmountView) :
    v.supplied = none → v.accepted = true
```

**Non-vacuity.** `stored = 100`, `skimmed = 0`, and supplied `99` gives
`accepted = false`; supplied `100` and `120` give `true`; `none` gives `true`.

**Why faithful.** The API contract is exactly a lower-bound check: “rejects a
value below its stored payment amount, less any skimmed fee. A larger value
passes” (`api.proto:226-231`); the handler substitutes `u64::MAX` for omission
(`bolt11_claim_for_id.rs:33`); the e2e boundary is `9,999,999` rejected versus
`10,000,000` expected (`e2e.rs:2082-2094`). The target models the **documented
contract**, not the unknown `179b4b2` arithmetic.

**Fidelity risk.** High for implementation-level claims: the server's node pin
is not available, so the exact `stored - skimmed` formula and underflow/rounding
behavior cannot be verified. The contract wording supports the lower-bound
shape, but not an exact implementation theorem. **Do not** silently strengthen
this to “exactly `stored - skimmed`”.

**Feasibility.** High arithmetic; **disposition: defer** until the server pin
is matched or the parent explicitly accepts contract-level scope. **Type:**
contract-level model extension; pin-blocked for exact fidelity. **Priority:**
P1.

---

### T4 — `openMode_exclusive` (P2)

**Proposed names**

```lean
LnLean.Proofs.Protocol.LdkServerApiTargets.OpenModeView
LnLean.Proofs.Protocol.LdkServerApiTargets.OpenModeView.admissible
LnLean.Proofs.Protocol.LdkServerApiTargets.openMode_exclusive
LnLean.Proofs.Protocol.LdkServerApiTargets.openMode_other_three
```

**Statement shape**

```lean
structure OpenModeView where
  announce                  : Bool
  disableCounterpartyReserve : Bool

def OpenModeView.admissible (m : OpenModeView) : Prop :=
  ¬ (m.announce = true ∧ m.disableCounterpartyReserve = true)

theorem openMode_exclusive (m : OpenModeView)
    (ha : m.announce = true) (hd : m.disableCounterpartyReserve = true) :
    ¬ m.admissible

theorem openMode_other_three (a d : Bool)
    (h : ¬ (a = true ∧ d = true)) :
    OpenModeView.admissible ⟨a, d⟩
```

**Non-vacuity.** `(false,false)`, `(true,false)`, and `(false,true)` all satisfy
`admissible`; `(true,true)` is the rejected witness. This is satisfiable, not a
vacuous implication.

**Why faithful.** The server's mode match rejects exactly this pair and routes
the other three to `open_channel`, `open_announced_channel`, or
`open_0reserve_channel` (`ldk-server/src/api/open_channel.rs:38-89`). The
request docs state the same restriction (`api.proto:602-606`). The target is
deliberately API-only: BOLT 2's `channel_flags` bit 0 is `announce_channel`
(`02-peer-protocol.md:769-770`), while zero-reserve is a channel-type choice,
not a wire flag, so no wire projection is claimed.

**Fidelity risk.** Low. **Feasibility.** High. **Type:** model extension.
**Priority:** P2.

---

### T5 — `serverChannel_usable_implies_ready` and readiness witnesses (P1)

**Proposed names**

```lean
LnLean.Proofs.Protocol.LdkServerApiTargets.ServerChannelView
LnLean.Proofs.Protocol.LdkServerApiTargets.ServerChannelView.WellFormed
LnLean.Proofs.Protocol.LdkServerApiTargets.serverChannel_usable_implies_ready
LnLean.Proofs.Protocol.LdkServerApiTargets.normal_not_ready_witness
LnLean.Proofs.Protocol.LdkServerApiTargets.ready_not_usable_witness
```

**Statement shape**

```lean
structure ServerChannelView where
  channel               : Channel
  handshake             : HandshakeState
  confirmationsRequired : Nat
  confirmations         : Nat
  peerConnected         : Bool
  isChannelReady        : Bool
  isUsable              : Bool

def ServerChannelView.WellFormed (v : ServerChannelView) : Prop :=
  (v.isChannelReady = true ↔
    v.handshake.ready = true ∧
      v.confirmationsRequired ≤ v.confirmations ∧
      v.channel.phase ≠ .shuttingDown ∧ v.channel.phase ≠ .closed) ∧
  (v.isUsable = true ↔
    v.isChannelReady = true ∧ v.peerConnected = true ∧
      v.channel.phase ≠ .shuttingDown ∧ v.channel.phase ≠ .closed)

theorem serverChannel_usable_implies_ready
    (v : ServerChannelView) (h : v.WellFormed) (hu : v.isUsable = true) :
    v.isChannelReady = true

theorem normal_not_ready_witness :
    ∃ v : ServerChannelView,
      v.WellFormed ∧ v.channel.phase = .normal ∧
      v.isChannelReady = false ∧ v.isUsable = false

theorem ready_not_usable_witness :
    ∃ v : ServerChannelView,
      v.WellFormed ∧ v.isChannelReady = true ∧ v.isUsable = false
```

**Non-vacuity.** For `normal_not_ready_witness`, take a normal-phase `Channel`,
`handshake = HandshakeState.initial` (so `ready = false`), confirmations `0`,
required `6`, peer connected, and both flags `false`. For
`ready_not_usable_witness`, take `handshake` with both `channel_ready` flags
set, confirmations `6`, required `6`, `peerConnected = false`,
`isChannelReady = true`, `isUsable = false`. Both satisfy `WellFormed`.

**Why faithful.** The proto says `is_channel_ready` is both `channel_ready`
messages plus no shutdown (`types.proto:583-593`), and `is_usable` is a strict
superset adding peer connectivity and no shutdown negotiation (`:589-593`).
`HandshakeState.ready` already has that both-flags meaning
(`Handshake.lean:111-130`). The model deliberately does **not** claim that
`Channel.phase = normal` determines the API fields; that is the point of the
negative witness and of the existing
`channelReady_reachable_without_fundingSigned`
(`StateMachineProps.lean:361-389`), which must be preserved.

**Fidelity risk.** Medium: `ServerChannelView` is a projection model, not the
server's `ChannelDetails`. It should be populated from the proto fields, not
from an invented “server state”. **Feasibility.** High. **Type:** model
extension. **Priority:** P1.

### 4.1 Fixture candidates (deferred, not authored here)

These are conformance ideas, not Lean files. R23 already established that the
existing `tests/conformance/rust-lightning/fixtures.json` schema and checker
are rust-lightning-specific (`scripts/check-conformance.py:70-78`; R23
§6 at `agents/reports/wave13-review/R23-ldk-server-e2e-mcp.md:598-602`).
Do not append server rows there.

| Id | Fixture | Kind |
|---|---|---|
| F1 | `fail_for_id` after a succeeded record; assert the API/store status does not regress | live server or store unit test; new schema |
| F2 | `claim_for_id` amount `stored-1`, `stored`, `stored+1`, omitted; plus wrong preimage | live server |
| F3 | send modes: fixed invoice, zero-amount invoice, explicit overpay, underpaying valid/invalid | live server |
| F4 | open-channel matrix: `(announce, disable_reserve)` four combinations and missing amount | request-level or live server |
| F5 | `list_channels` before/after readiness: `phase`, confirmations, `is_channel_ready`, `is_usable`, shutdown state | live server |
| F6 | RBF lower fee rejected, higher fee accepted, recipient preserved, old tx evicted | live chain; external/R04 |
| F7 | unknown fail id, absent `get_payment_details`, opaque `page_token` round-trip | live server |

F1–F5 need a new `lnlean.ldk-server.differential.v1`-style schema and a pin note
for `c17dc11d…`; F6–F7 are live/external. None is a substitute for the Lean
targets above.

---

## 5. Assumptions, counterexamples, and non-vacuity risks

1. **Pin mismatch is an evidence barrier, not a footnote.** The server's
   `179b4b2` node revision is absent. Any claim about the exact claim-amount
   formula, `PaymentDetails` event timing, or internal duplicate guard at that
   revision is an assumption until the pin is synchronized. The server handler,
   proto, and e2e are still pinned evidence for the API boundary.
2. **Do not change `PaymentSession.settle` to overwrite status.** That would
   falsify `settle_terminal`/`settle_idempotent` and hide the server
   divergence. T1 is additive and preserves the existing absorbing theorem as
   the contrast case.
3. **Preserve the concrete counterexamples.** In particular:
   * `PaymentSession.settle_terminal` (`HTLC.lean:148-153`) versus
     `failForId_regresses_succeeded`;
   * `MppPayment.settle_requires_sum` (`Invariants.lean:448-454`) versus the
     claim lower-bound witness;
   * `channelReady_reachable_without_fundingSigned`
     (`StateMachineProps.lean:381-389`);
   * `mppComplete` exact-sum and its over-total counterexample;
   * `no_step_from_closed` (`State.lean:179-182`).
4. **Do not claim `is_usable` from `Channel.phase`.** The proto calls
   `is_usable` a strict superset of ready and adds peer connectivity and
   shutdown state. The normal-phase-not-ready and ready-not-usable witnesses
   are required non-vacuity anchors.
5. **Do not claim `PaymentId ≠ txid` universally.** The e2e assertion is one
   sampled transaction (`e2e.rs:493`). A byte-reversal or palindromic txid can
   collapse the two representations; the safe claim is about the server's
   documented distinction, not an arithmetic inequality.
6. **Do not merge BOLT 4 overpay with LDK underpaying.** BOLT 4 permits a set
   total `≥ total_msat` (`04-onion-routing.md:382-404`); the LDK underpaying API
   declares the full total and sends less, requiring receiver configuration
   (`bolt11.rs:362-405`). R12 T5 owns the additive `settleGe` repair for the
   former. R24 does not duplicate it.
7. **Do not use `HtlcRecord.fail` as the manual-fail transition.** It is a
   timeout rule with `cltvExpiry ≤ height` (`Invariants.lean:231-240`), while
   `fail_for_id` has no expiry guard. If a claim-rejection carrier is added, it
   should be separate and should not weaken the timeout theorem.
8. **T3 is contract-level unless the pin is fixed.** The proto wording and
   handler default support a lower-bound relation; they do not establish the
   exact `179b4b2` implementation. Do not publish an implementation-fidelity
   claim from the current clone.
9. **No vacuous implications.** Each target above has an explicit witness:
   T1 a succeeded BOLT 11 record; T2 `100/300`; T3 `100/0/{99,100,120,None}`;
   T4 the four mode pairs; T5 the initial-handshake normal view and the
   disconnected ready view.
10. **External boundaries.** On-chain wallet/RBF, live regtest, real
    persistence, and node-level interop remain external (R04/R23). A green
    Lean target about a view record is not a live server conformance result.

---

## 6. Wave-13 recommendation

### 6.1 Verdict

**A narrow, safe implementation lane exists for T1 only.** The broader server
API surface should be deferred to a dedicated server-conformance wave, and the
on-chain/RBF surface is external.

* **Implement in wave 13 (safe, additive):** T1
  (`failForId_regresses_succeeded`, `recordFail_neq_settle`) in a new
  `LnLean/Proofs/Protocol/LdkServerApiTargets.lean`. It changes no existing
  carrier, needs no server process, and directly documents the one sharp
  divergence between the server's mutable payment record and
  `settle_terminal`.
* **Correct `LN-PM-004` by cross-reference, not by weakening:** the catalog
  wording “parts summing exactly” is narrower than BOLT 4's `≥ total_msat`
  rule. R12 T5 already proposes the additive `settleGe` theorem. The parent
  should land that under R12 and either amend the row's prose to say
  “exact-sum conservative form” or add the overpay target. Do **not** delete
  or weaken `settle_requires_sum`; do not duplicate R12 T5 in R24.
* **Defer to wave 14 (or a server-API catalogue item):** T2, T3, T4, T5 and
  F1–F5. They need a server-API issue id, a new module, and a separate
  differential schema. T2/T3 are pin-sensitive; T3's exact implementation is
  blocked on the `179b4b2` node revision.
* **External / human barrier:** server e2e/regtest, live channel readiness,
  PostgreSQL persistence, on-chain send/RBF/wallet, and node-level interop.
  T1 does not close any of these. Do not claim LDK Server conformance from this
  report.

### 6.2 Why not a larger wave-13 lane

R23 already recommends deferring the whole server-API lane and notes that the
e2e suite is almost entirely live-only
(`agents/reports/wave13-review/R23-ldk-server-e2e-mcp.md:610-613`). R24 adds
one narrower reason: the server's own node pin is not the review pin, so the
highest-fidelity API target (claim amount) cannot be implemented honestly yet.
Implementing T2/T5 as if `fa123fed` were the server dependency would create a
theorem about the wrong revision.

### 6.3 Disposition table

| Item | Disposition |
|---|---|
| T1 status regression | **Implement** in wave 13 |
| `LN-PM-004` prose / overpay correction | **Cross-reference R12 T5**; do not duplicate |
| T2 send modes | **Defer** (pin-sensitive API model) |
| T3 claim amount lower bound | **Defer / pin-blocked** for implementation fidelity; contract-level only |
| T4 open mode matrix | **Defer** to server-API wave |
| T5 channel readiness view | **Defer** to server-API wave |
| F1–F5 | **Defer**; new schema and live harness needed |
| F6–F7 / on-chain RBF / wallet | **External** (R04/R23) |

---

## 7. Evidence and commands

All inspection was read-only in `/home/ubuntu/ln-lean-repair` and the pinned
clones. No `lake build`, no `cargo test`, and no network access were used.

### 7.1 Pins and review tip

```sh
git -C /tmp/opencode/ldk-node rev-parse HEAD
# fa123fed131e27ecc420b77fa7086fcf1ddaebb8

git -C /tmp/opencode/ldk-server rev-parse HEAD
# c17dc11dde38f88c53457039ddf30c6b90a63ba2

git -C /home/ubuntu/ln-lean-repair rev-parse HEAD
# f7f062817c185cd70004bb26c652deb99c6fd4bd
```

### 7.2 The pin mismatch

```sh
grep -n 'ldk-node' /tmp/opencode/ldk-refs/ldk-server/ldk-server/Cargo.toml
# 16: ldk-node = { git = ..., rev = "179b4b263762155a7ff515ddad7e757a80807fd5", ... }

grep -n -A4 -B1 'name = "ldk-node"' /tmp/opencode/ldk-refs/ldk-server/Cargo.lock
# 1382-1384: version 0.8.0+git, source ...rev=179b4b2...#179b4b2...

git -C /tmp/opencode/ldk-refs/ldk-node cat-file -e \
  179b4b263762155a7ff515ddad7e757a80807fd5^{commit}
# fatal: Not a valid object name; rc=128

nl -ba /tmp/opencode/ldk-refs/ldk-server/ldk-server/src/api/bolt11_claim_for_id.rs
# 33: unwrap_or(u64::MAX)
# 34: claim_for_id(payment_id, claimable_amount_msat, preimage)

nl -ba /tmp/opencode/ldk-refs/ldk-node/src/payment/bolt11.rs | sed -n '424,426p'
# pub fn claim_for_id(&self, payment_id: PaymentId, preimage: PaymentPreimage)
```

### 7.3 Lean surface checks

```sh
rg -n 'PaymentDetails|PaymentStore|LdkServerApi|claim_for_id|fail_for_id|is_usable|channel_shutdown_state|disable_counterparty_reserve|user_channel_id|bump_fee_rbf' LnLean --glob '*.lean'
# no matches (the negative surface in §1.3)

nl -ba LnLean/Payment/HTLC.lean | sed -n '64,153p'
nl -ba LnLean/Payment/MPP.lean | sed -n '59,69p;141,180p'
nl -ba LnLean/Security/Invariants.lean | sed -n '218,240p;425,454p'
nl -ba LnLean/Channel/Types.lean | sed -n '159,175p'
nl -ba LnLean/Channel/State.lean | sed -n '86,127p;178,182p'
nl -ba LnLean/Protocol/Messages.lean | sed -n '102,139p'
nl -ba LnLean/Protocol/Handshake.lean | sed -n '111,130p;835,849p'
nl -ba LnLean/Proofs/Channel/StateMachineProps.lean | sed -n '361,389p'
nl -ba LnLean/Proofs/WaveD/D18.lean | sed -n '331,336p'
nl -ba LnLean/Proofs/Obligations.lean | sed -n '168,217p;357,400p'
```

### 7.4 Server/proto/e2e checks

```sh
nl -ba /tmp/opencode/ldk-refs/ldk-server/ldk-server/src/api/bolt11_send.rs
nl -ba /tmp/opencode/ldk-refs/ldk-server/ldk-server/src/api/bolt11_fail_for_id.rs
nl -ba /tmp/opencode/ldk-refs/ldk-server/ldk-server/src/api/open_channel.rs
nl -ba /tmp/opencode/ldk-refs/ldk-server/ldk-server/src/api/close_channel.rs
nl -ba /tmp/opencode/ldk-refs/ldk-server/ldk-server/src/api/onchain_send.rs
nl -ba /tmp/opencode/ldk-refs/ldk-server/ldk-server/src/api/onchain_bump_fee.rs
nl -ba /tmp/opencode/ldk-refs/ldk-server/ldk-server/src/api/list_payments.rs
nl -ba /tmp/opencode/ldk-refs/ldk-server/ldk-server/src/api/get_payment_details.rs
nl -ba /tmp/opencode/ldk-refs/ldk-server/ldk-server/src/util/proto_adapter.rs | sed -n '89,210p'
nl -ba /tmp/opencode/ldk-refs/ldk-server/ldk-server-grpc/src/proto/api.proto | sed -n '92,150p;218,250p;359,408p;576,724p;751,783p'
nl -ba /tmp/opencode/ldk-refs/ldk-server/ldk-server-grpc/src/proto/types.proto | sed -n '1,30p;271,290p;521,692p;714,721p'
nl -ba /tmp/opencode/ldk-refs/ldk-server/e2e-tests/tests/e2e.rs | sed -n '492,524p;601,613p;2079,2095p;2155,2162p'
nl -ba /tmp/opencode/ldk-refs/ldk-server/e2e-tests/src/lib.rs | sed -n '904,919p'
```

### 7.5 Node internals used only as `[node:fa]` evidence

```sh
nl -ba /tmp/opencode/ldk-refs/ldk-node/src/payment/bolt11.rs | sed -n '207,297p;335,405p;424,531p'
nl -ba /tmp/opencode/ldk-refs/ldk-node/src/payment/store.rs | sed -n '60,91p;225,255p;335,337p'
nl -ba /tmp/opencode/ldk-refs/ldk-node/src/data_store.rs | sed -n '346,353p'
nl -ba /tmp/opencode/ldk-refs/ldk-node/src/event.rs | sed -n '1470,1508p;1550,1564p;1609,1622p'
nl -ba /tmp/opencode/ldk-refs/ldk-node/src/wallet/mod.rs | sed -n '3371,3505p'
```

No file outside
`agents/reports/wave13-review/R24-ldk-server-payment-channel-api.md` was
created or modified.
