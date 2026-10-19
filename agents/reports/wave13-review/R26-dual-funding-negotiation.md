# R26 — Dual funding, interactive tx, and channel negotiation

**Status:** read-only review
**Pins:** LDK Node `fa123fed131e27ecc420b77fa7086fcf1ddaebb8`, LDK Server `c17dc11dde38f88c53457039ddf30c6b90a63ba2`
**Review branch:** `repair/integrated` at `f7f0628` (no branch, commit, or non-report file changes made)
**Core rust-lightning anchor:** `refs/rust-lightning` at pinned `d7a980641c6325ddda5072a0f470ef8392676cf5`

## 1. Scope and current Lean surface

This lane covers BOLT 2 v2 channel establishment: `open_channel2` /
`accept_channel2`, per-side funding contributions, the interactive-transaction
message family (`tx_add_input`, `tx_add_output`, `tx_remove_*`, `tx_complete`,
`tx_signatures`, `tx_abort`), the `tx_complete` funding-output check, and the
feature-28 (`option_dual_fund`) gate on v1 `open_channel`. It does **not**
re-review the v1 lifecycle (R05), splice-specific quiescence/promotion (R25),
commitment mechanics, signatures, or L1 transaction validity except where they
constrain a negotiation statement.

The review question is: **does the current single-funder phase machine cover
any of this, and what is the smallest faithful extension?** The answer is that
v1 construction is covered, but dual funding is neither represented nor
implemented end to end in the pinned public LDK APIs; full interactive tx is an
external barrier. A small non-representability/scoping slice is safe.

### 1.1 Explicit exclusions already in the tree

Dual funding is deliberately excluded, not merely unfinished:

| Location | Statement |
|---|---|
| `docs/SCOPE.md:23` | “Splicing, dual funding, channel factories, eltoo, Taproot-native channels.” are out of scope. |
| `LnLean/Channel/Types.lean:41-43` | Multi-party channels, splicing, dual funding, zero-fee commitments, and Taproot-native channels are not modelled. |
| `LnLean/Channel/State.lean:51` | “Splicing, quiescence, dual funding, and `option_simple_close`.” are not modelled. |
| `LnLean/Protocol/Messages.lean:60-63` | `open_channel2` is deliberately absent from `Msg`; the model covers v1 `open_channel` type 32. |
| `docs/THEOREM-INDEX.md` / `docs/TRACEABILITY.md` | There is **no** `LN-*` row for dual funding or interactive tx. `LN-PR-001` is v1 type 32; `LN-PR-006` is generic feature intersection. |
| `docs/OPEN-ISSUES.md` | No row tracks dual funding; the governing decision remains the `SCOPE.md` exclusion. |

`agents/reports/swarm12/S12-POST-INTEGRATION-AUDIT.md:69-76` also declines to
launch a wave-13 proof lane. This lane therefore has no existing claim to
strengthen: any dual-funding theorem is new surface.

### 1.2 The current Lean surface is v1 single-funder

| Layer | Current shape | Consequence for v2 |
|---|---|---|
| `OpenChannel` (`LnLean/Protocol/Handshake.lean:840-850`) | `temporaryChannelId`, `fundingSatoshis`, `pushMsat`, `fundingPubKey`. | No accepter contribution; the opener supplies the whole capacity. |
| `OpenChannel.toFundingNegotiation` (`Handshake.lean:858-865`) | Sets `fundingSatoshis := o.fundingSatoshis`, `pushMsat := o.pushMsat`, keys from open/accept. | A v2 total must be squeezed into `fundingSatoshis`; the per-side split has nowhere to go. |
| `FundingPhase` (`Handshake.lean:935-989`) | Four optional messages: `openSent`, `openReceived`, `acceptSent`, `acceptReceived`. | No `open_channel2`, no interactive-tx round, no contribution fields. |
| `fundingStep` / `FundingReachable` (`Handshake.lean:1002-1016`) | One deterministic transition per v1 message; reachability is the closure. | Extending it to v2 means new events and state, not a new hypothesis on the existing ones. |
| `FundingNegotiation` (`LnLean/Bitcoin/Funding.lean:240-253`) | Exactly `fundingSatoshis`, `pushMsat`, two keys, temporary/final id. | Cannot store `openContribution` and `acceptContribution` separately. `pushMsat` does not exist in v2. |
| `Channel` (`LnLean/Channel/Types.lean:162-175`) | One `funding` outpoint and one `fundingValue`. | No per-side balance origin, no pending interactive-tx candidate. |
| `ProtocolEvent` / `Step` (`LnLean/Channel/State.lean:67-127`) | Ten v1 events; `openChannel` and `acceptChannel` are identity steps in `negotiating`. | No v2 event, no abort, no contribution accounting. |
| `MsgKind` / `wireType` / `kindOfType?` (`LnLean/Protocol/Messages.lean:292-359`, `:365-385`) | Types 1, 16–19, 32–39, 128–136 only. | Types 64/65/66/67/70/71/74 are unknown and cannot be decoded. |
| v1 decoder test (`LnLean/Proofs/WaveH/H18.lean:438-441`) | `decodeFrame_wrong_type_64 : decodeFrame (frameBytes 64 ...) = none`. | This is a v1 non-acceptance test, not v2 coverage. |
| `feature_intersection` (`LnLean/Proofs/ProtocolTargets.lean:84-99`) | Generic negotiated-feature intersection under the BOLT 1 survival hypothesis. | It never mentions bit 28 or rejects v1 open; do not cite it as dual-fund support. |

The only “both sides” artifact is
`fundingReachable_negotiation_witness` (`Handshake.lean:1097-1101`), and its
witness uses zero amounts and the same key on both sides (`:1102-1121`). It
proves the v1 phase is non-vacuous; it is not a dual-funding witness.

### 1.3 What the existing arithmetic does and does not establish

* `FundingProps.capacity_eq_funder_plus_push` (`LnLean/Proofs/Bitcoin/FundingProps.lean:279-283`)
  states `capacity = (capacity - push) + push` under the v1 `WellFormed`
  hypothesis `push_msat <= funding_satoshis * 1000`. It is a v1 identity about
  a single funder's push. Retargeting it as “dual-funding capacity” would be a
  category error: v2 has no `push_msat`, and capacity is the sum of two
  contributions.
* `FundingAuthTargets.funding_output_ignores_fundingSatoshis`
  (`LnLean/Proofs/Bitcoin/FundingAuthTargets.lean:523-527`) shows the P2WSH
  output commits only to the funding keys. It does **not** bind either
  contribution; that is why v2 needs an explicit `tx_complete` check.
* `FundingAuthTargets.same_message_distinct_senders`
  (`:475-487`) shows a message payload does not determine its sender. A v2
  `tx_add_input` message would inherit that limit: serial parity is not
  ownership authentication.
* `FundingNegotiation` and `step_fundingValue_eq`
  (`LnLean/Proofs/Channel/StateTransitionTargets.lean:417-419`) make funding
  value immutable along `Step`. Any v2 event that changes funding must be a
  separate relation, not a new `Step` constructor.

### 1.4 Boundary with adjacent lanes

R05 already owns the v1 handshake/lifecycle gaps (identity `acceptChannel`,
missing depth/abort/timeout, `channel_ready` bridge). R25 already owns splice
interactive-tx construction, `tx_complete`, `tx_abort`, and matching-lock
promotion. This report references those results and does **not** re-derive
them. The v2-specific delta is the contribution split, the v2 message/feature
gate, and the fact that the pinned public LDK APIs do not expose outbound dual
funding at all.

## 2. LDK datapoints (with `file:line`)

All citations are read-only inspection of the pinned clones. “LDK Node” is the
public node API, “LDK Server” the gRPC surface, and rust-lightning the core
implementation at the rev declared by LDK Node `Cargo.toml:89-98`.

### 2.1 LDK Node public API: single-funder only

* `ldk-node/src/lib.rs:1374-1500` — `open_channel_inner` takes one
  `channel_amount_sats: FundingAmount` and one optional
  `push_to_counterparty_msat`. There is no second contribution parameter.
* `lib.rs:1455` and `:1464` — it calls
  `create_channel_to_trusted_peer_0reserve` or `create_channel`, both v1
  entry points.
* `lib.rs:1576`, `:1627`, `:1665`, `:1712`, `:1756`, `:1794` — all public
  `open_channel*` wrappers delegate to the same single-funder helper.
* `lib.rs:1953`, `:1990`, `:2022`, `:2116` — `splice_in`,
  `splice_in_with_all`, `splice_out`, and `bump_channel_funding_fee` are the
  only public interactive-funding operations. They are splice operations, not
  channel establishment v2.
* No public `open_channel2`, `accept_channel2`, `tx_add_input`,
  `tx_add_output`, `tx_complete`, or `tx_abort` symbol exists in
  `ldk-node/src` (verified by `rg`).
* `ldk-node/src/event.rs:1725-1733` — the `OpenChannelRequest` handler binds
  `channel_negotiation_type: _`, i.e. it discards the V1/V2 discriminator.
* `event.rs:1824-1839` — it then calls `accept_inbound_channel` or
  `accept_inbound_channel_from_trusted_peer`; there is no
  `accept_inbound_channel_v2` path. A v2 request cannot be accepted as v2 by
  the pinned node.
* `ldk-node/src/ffi/types.rs:2058-2065` and `:2410-2417` — the only
  dual-fund bindings are `supports_dual_fund` / `requires_dual_fund`
  feature-bit queries. They expose peer capability, not negotiation.
* `ldk-node/src/wallet/mod.rs:2615-2683`, `:2787` — `InteractiveFunding` is a
  wallet transaction classification for a round the node signed. It is not a
  channel-open API and does not create a v2 negotiation.

### 2.2 LDK Server: no dual-fund RPC

* `ldk-server-grpc/src/proto/api.proto:578-607` — `OpenChannelRequest` has one
  `channel_amount_sats` / `all_funds` choice plus an optional
  `push_to_counterparty_msat`. There is no contribution field and no
  `open_channel2` request.
* `api.proto:1292` — the only open RPC is `OpenChannel(OpenChannelRequest)`.
  `:1294-1296` adds `SpliceIn` / `SpliceOut` / `BumpChannelFundingFee`; these
  belong to R25.
* `ldk-server-grpc/src/proto/types.proto:150-155` and
  `ldk-server-grpc/src/types.rs:252-263` — `InteractiveFunding` is documented
  as “An interactively-negotiated funding transaction: a splice, or (once
  supported) a V2 dual-funded channel open.” The phrase “once supported” is
  decisive: the enum is a transaction-classification label, not a protocol
  path.
* `ldk-server/src/util/proto_adapter.rs:253-259` — it adapts
  `LdkTransactionType::InteractiveFunding { channels }` into the proto label.
  It does not negotiate a channel.

### 2.3 Pinned rust-lightning core (`d7a980`): inbound skeleton, zero contribution

* `lightning/src/ln/channelmanager.rs:18123-18125` — bit 28 is set only when
  `config.enable_dual_funded_channels` is true. The default path does not
  advertise dual funding.
* `channelmanager.rs:17036-17041` — inbound `open_channel_v2` is rejected with
  “Dual-funded channels not supported” unless `init_features().supports_dual_fund()`.
* `channelmanager.rs:11651-11675` — an inbound V2 message reaches
  `PendingV2Channel::new_inbound` and produces `SendAcceptChannelV2`.
* `channel.rs:16325-16333` — `PendingV2Channel::new_inbound` hardcodes
  `our_funding_contribution = SignedAmount::ZERO` and
  `our_funding_inputs = Vec::new()`, with `TODO(dual_funding): Allow
  contributions, pass intended amount and inputs`.
* `channel.rs:16483-16484` — the generated `accept_channel2.funding_satoshis`
  is `our_funding_contribution.to_sat()`, i.e. zero on this path.
* `channel.rs:7174-7186` — `get_v2_channel_reserve_satoshis` fixes the reserve
  at `max(channel_value / 100, dust_limit)`, or zero for 0-reserve.
* `channelmanager.rs:3969-3982` — the public outbound `create_channel` always
  calls `create_channel_internal`; `:4057` constructs `OutboundV1Channel::new`.
  There is no public outbound V2 constructor call.
* `channel.rs:16176-16178` — `PendingV2Channel::new_outbound` is
  `#[allow(dead_code)]` with `TODO(dual_funding): Remove once creating V2
  channels is enabled`.
* `lightning/src/ln/mod.rs:48-49` — `interactivetxs` is itself
  `#[allow(dead_code)]` behind the same TODO.
* `lightning/src/ln/msgs.rs:295-308` (`OpenChannelV2`), `:375-386`
  (`AcceptChannelV2`), `:500-515` (`TxAddInput`), `:521-535`
  (`TxAddOutput`), `:560-568` (`TxComplete`), `:570-582`
  (`TxSignatures`), `:615-624` (`TxAbort`), and
  `lightning/src/ln/wire.rs:549-604` (types 64/65/66/67/70/71/72/73/74) — the wire
  vocabulary exists in core, but the establishing path is dead or
  zero-contribution.

**Consequence:** the pinned public LDK refs cannot open a genuine dual-funded
channel. The core has an inbound parsing/accept skeleton that contributes zero
funds and inputs, and an outbound implementation that is unreachable. Any Lean
claim of “LDK dual funding covered” would be false at this pin.

### 2.4 BOLT anchors

* `refs/bolts/02-peer-protocol.md:112` — for channel establishment v2 the
  initiator is the peer sending `open_channel2`; `:141-145` — construction
  completes only after both nodes send and receive consecutive `tx_complete`.
* `:204-228` — `tx_add_input` must use unique `serial_id`s; the initiator MUST
  send even ids and the non-initiator MUST send odd ids; the receiver MUST fail
  on wrong parity. `:296-311` applies the same parity rule to outputs.
* `:367-405` — on `tx_complete`, the accepter MUST fail unless the funding
  output value equals the sum of `open_channel2.funding_satoshis` and
  `accept_channel2.funding_satoshis`; limits are 252 inputs/outputs and
  400,000 weight.
* `:583-621` — `tx_abort` cancels an in-progress negotiation; a peer that has
  not sent `tx_signatures` SHOULD forget the negotiation and reset.
* `:1174-1266` — `open_channel2` fields, no `push_msat` (`:1260`), no
  `channel_reserve_satoshis`; the reserve is derived from the total
  (`:1254-1258`).
* `:1269-1330` — `accept_channel2` fields; the accepter MAY set
  `funding_satoshis` to zero (`:1312`); reserve is 1% of
  `open.funding_satoshis + accept.funding_satoshis`, at least `dust_limit`
  (`:1325-1330`).
* `:1332-1370` — funding composition; the opener must add the funding output,
  and the accepter checks the sum on `tx_complete` (`:1363-1370`).
* `:845-846` — for v1 `open_channel`, if `option_dual_fund` has been
  negotiated, the receiving node MUST fail the channel. `:1217-1218` — the
  opening node MUST NOT send `open_channel` after negotiating `option_dual_fund`.
* `refs/bolts/09-features.md:48` — bit 28/29 is `option_dual_fund`, “Use v2 of
  channel open, enables dual funding”.

## 3. Gap matrix

Status vocabulary is the lane’s required set: **covered faithfully**,
**partially covered**, **missing**, **contradicted**, **unmodelled-external**.
“Missing” means absent from the current Lean vocabulary; it is not by itself a
soundness bug, but it is a completeness gap for any claim that the model covers
v2 establishment.

| Behavior | Lean status | LDK / BOLT evidence | Gap / counterexample | Priority |
|---|---|---|---|---|
| v1 `open_channel` / `accept_channel` funding construction | covered faithfully | `Handshake.lean:840-865`; `Funding.lean:240-253`; `OpenChannelWireTargets.lean:438-453`; BOLT 2 `:680-846` | The construction is v1 and non-vacuous (`fundingReachable_negotiation_witness`, `:1097`). It does not carry a second contribution. | — |
| v1 `open_channel` / `accept_channel` lifecycle | partially covered | `State.lean:88-93`; R05 §1.2 | Both events are identity steps in `negotiating`; accept is not a premise for `fundingCreated`. R05 owns this. | P1 (R05) |
| `open_channel2` / `accept_channel2` messages and state | missing | BOLT 2 `:1174-1330`; `channelmanager.rs:11651`; `msgs.rs:295`, `:375` | `Msg` has no type 64/65; `FundingPhase` has no contribution fields; `FundingNegotiation` has no split. | **P1** |
| Per-side contribution split and initial balances | missing | BOLT 2 `:1332-1370`; `channel.rs:16331-16333` | `FundingNegotiation` stores one `fundingSatoshis` plus v1 `pushMsat`. T1 below exhibits two distinct splits with the same projection. | **P1** |
| `push_msat` semantics in v2 | contradicted if the v1 projection is reused | BOLT 2 `:1260` (“`push_msat` has been omitted”); `Funding.lean:243-246` | Reusing `toFundingNegotiation` would invent a push field and assign the whole total to the opener. The projection is not a v2 model. | **P1** |
| Capacity equals sum of both contributions | missing | BOLT 2 `:1363-1370`; `channel.rs:16329-16333` | No theorem relates a v2 total to two contributions. `capacity_eq_funder_plus_push` is v1 push arithmetic, not this. | **P1** |
| v2 channel reserve (1% of total, max dust) | missing | BOLT 2 `:1254-1258`, `:1325-1330`; `channel.rs:7174-7186` | The v1 model keeps a per-side `channelReserveSatoshis` on the wire (`Messages.lean:143-158`). The v2 rule depends only on the total. | P2 |
| `tx_complete` funding-output sum and limits | missing | BOLT 2 `:367-405`, `:1363-1370` | No `tx_complete`, no output identity, no 252/400k bounds. Splice has a different `tx_complete` path (R25). | **P1** |
| Two-sided completion (both sent and received) | missing | BOLT 2 `:141-145`; R25 T5 for the splice analogue | No interactive-tx state, so “one side said complete” cannot be distinguished from “both did”. | P1 |
| Interactive tx input/output construction, fees, prevtx validity, confirmed-input/RBF rules | unmodelled-external | BOLT 2 `:100-621`; `msgs.rs:500-624`; R25 §5.1 | The model should abstract the result as “negotiated” or “aborted”; it should not prove PSBT/script/fee validity. | P2 (external) |
| `serial_id` uniqueness and parity | missing | BOLT 2 `:204-228`, `:305-311` | No serial ids. The parity law is cheap to model and is a useful non-collision invariant. | P2 |
| `tx_abort` / RBF restart | unmodelled-external | BOLT 2 `:583-621`; R25 §2.4 | No abort or RBF state in `Channel`/`ProtocolEvent`; the chain/package side is external. | P2 (external) |
| Feature bit 28 negotiation and v1-open rejection | partially covered (generic only) | BOLT 9 `:48`; BOLT 2 `:845-846`, `:1217-1218`; `ProtocolTargets.lean:84-99` | `feature_intersection` is a generic bit-set law under a survival hypothesis. It has no bit-28 predicate and no v1-open rejection theorem. | **P1** |
| Inbound V2 request at the public node API | unmodelled-external (client gap) | `ldk-node/src/event.rs:1725-1733` discards `channel_negotiation_type`; `:1824-1839` calls the v1 accept | The pinned node has no v2 accept path. “Inbound dual-fund event exists” must not be read as “node supports v2”. | P2 |
| Outbound dual funding at the public API | unmodelled-external (absent) | `ldk-node/src/lib.rs:1374-1500`, `:1455`, `:1464`; `api.proto:578-607` | Single amount plus push only. Core `new_outbound` is dead code (`channel.rs:16176-16178`). | P2 |
| Reconnect / persistence of an in-progress v2 negotiation | unmodelled-external | BOLT 2 `:583-621`; R25 §5.1; `ChannelReestablishProps` scope | No per-negotiation persistence or reestablish map. A bounded model must assume externally recovered state. | P2 (external) |
| Signature/ownership of contributed inputs | unmodelled-external | `same_message_distinct_senders` (`FundingAuthTargets.lean:475-487`); BOLT 2 `:220-245` | Payloads do not identify senders; `tx_signatures` validity and key ownership remain external. | P2 (external) |

## 4. Proposed targets

The targets below are **statement shapes for wave-14 scoping**, not compiling
Lean. They deliberately live in a new module, for example
`LnLean.Proofs.Protocol.DualFundingTargets`, and add a **sidecar** v2 record.
They do not edit `Channel`, `ChannelPhase`, `ProtocolEvent`, `Step`,
`FundingNegotiation`, or the v1 wire vocabulary.

### 4.0 Model sketch

```lean
/-- Local, minimal v2 negotiation. Interactive-tx inputs/outputs are abstracted. -/
structure V2Negotiation where
  temporaryChannelId : ChannelId
  openContribution   : BtcAmount   -- open_channel2.funding_satoshis
  acceptContribution : BtcAmount   -- accept_channel2.funding_satoshis
  openFundingKey     : PubKey
  acceptFundingKey   : PubKey
  dustLimit          : Nat

/-- Projection into the existing v1-shaped record. It is intentionally lossy. -/
def V2Negotiation.toFundingNegotiation (v : V2Negotiation) : FundingNegotiation :=
  { fundingSatoshis := v.openContribution + v.acceptContribution
    pushMsat := ⟨0⟩
    localFundingKey := v.openFundingKey
    remoteFundingKey := v.acceptFundingKey
    temporaryChannelId := v.temporaryChannelId }

/-- v2 has no per-side reserve field; the reserve is a function of the total. -/
def v2ChannelReserveSatoshis (total dust : Nat) (is0 : Bool) : Nat :=
  if is0 then 0 else max (total / 100) dust
```

The sidecar keeps `V2Negotiation` separate from `FundingNegotiation` precisely
because the latter cannot represent the split. `toFundingNegotiation` exists
only to make the loss of information theorem meaningful.

### T1 — `LnLean.Proofs.Protocol.DualFundingTargets.v2_contribution_split_not_injective`

**Priority:** P1. **Classification:** model extension (lossy projection).
**Fidelity risk:** low. **Feasibility:** high. **Top target.**

```lean
theorem v2_contribution_split_not_injective :
    ∃ a b : V2Negotiation,
      a ≠ b ∧ a.toFundingNegotiation = b.toFundingNegotiation
```

**Hypotheses:** `a` and `b` have the same temporary id and funding keys; both
totals are equal and positive; `a.acceptContribution = 0`,
`b.openContribution = b.acceptContribution = total / 2`. No well-formedness
hypothesis beyond the total.

**Non-vacuity witness:** `a = (100_000, 0)`, `b = (50_000, 50_000)` with total
`100_000`; `a ≠ b` by the contribution fields, while both projections have
`fundingSatoshis = 100_000`, `pushMsat = 0`, and the same keys.

**Why faithful:** BOLT 2 `:1312` explicitly allows the accepter to
contribute zero, and `:1363-1370` makes the funding output the sum of the two
contributions. The existing `FundingNegotiation` has no split field and no v2
push. The theorem records the exact information the current model loses; it is
a negative representability result, not a claim that either split is invalid.

**Non-weakening:** do not prove this with `a = b` or with both contributions
zero. The two splits must be distinct and each must be individually admissible.

### T2 — `LnLean.Proofs.Protocol.DualFundingTargets.v2_zero_accept_contribution_valid`

**Priority:** P1. **Classification:** model extension (non-vacuity guard).
**Fidelity risk:** low. **Feasibility:** high.

```lean
theorem v2_zero_accept_contribution_valid :
    ∃ v : V2Negotiation,
      v.WellFormedV2 ∧ v.acceptContribution = 0 ∧
      0 < v.openContribution
```

**Hypotheses:** `WellFormedV2` requires positive total capacity above dust and
valid keys; it **must not** require both contributions to be positive.

**Non-vacuity witness:** `openContribution = 100_000`, `acceptContribution = 0`.

**Why faithful:** BOLT 2 `:1312` says the accepting node MAY respond with
`funding_satoshis` zero; pinned LDK’s inbound skeleton actually does exactly
that (`channel.rs:16331-16333`, `:16483-16484`). This target prevents a stronger
but false “both sides contribute” specification from becoming the model’s
definition of well-formedness.

### T3 — `LnLean.Proofs.Protocol.DualFundingTargets.v2_funding_output_eq_sum_of_contributions`

**Priority:** P1. **Classification:** model extension + external tx
construction. **Fidelity risk:** medium. **Feasibility:** medium.

```lean
theorem v2_funding_output_eq_sum_of_contributions
    {v : V2Negotiation} {tx : FundingTx}
    (h : AcceptsTxComplete v tx) :
    tx.fundingOutputValue = v.openContribution + v.acceptContribution
```

**Hypotheses:** `AcceptsTxComplete` encodes the accepter’s BOLT 2 check on
receipt of consecutive `tx_complete`s: exactly one funding output is
identified, its value is the sum of both contributions, and it is at least the
dust limit. `FundingTx` is an abstract record (outpoint + output value); input
ownership, script validity, fees, and weight are not modelled.

**Non-vacuity witness:** `v = (60_000, 40_000)`, `tx.fundingOutputValue =
100_000`; negative witness: `tx.fundingOutputValue = 90_000` has no
`AcceptsTxComplete` derivation.

**Why faithful:** BOLT 2 `:1363-1370` makes this an explicit accepter MUST.
The pinned core’s zero-contribution skeleton (`channel.rs:16329-16333`) is
consistent with the equation but is not evidence that a nonzero path is
implemented.

**Non-weakening:** do not assume the output sum as a hypothesis; derive it from
`AcceptsTxComplete`. Do not quantify over all outputs without an output
identity premise.

### T4 — `LnLean.Proofs.Protocol.DualFundingTargets.v2_complete_requires_both_sides`

**Priority:** P1/P2. **Classification:** model extension (interactive-tx
sidecar). **Fidelity risk:** low. **Feasibility:** medium.

```lean
theorem v2_complete_requires_both_sides {s : V2TxState}
    (h : V2TxReachable s) (hc : s.phase = .complete) :
    s.sentComplete = true ∧ s.receivedComplete = true
```

**Hypotheses:** `V2TxState` records `sentComplete`, `receivedComplete`, and a
phase; only the `recvComplete` event can set `.complete`, and only when
`sentComplete = true`. `V2TxReachable` is the closure of the sidecar steps.

**Non-vacuity witness:** send `tx_add_input`, receive `tx_add_input`, send
`tx_complete`, receive `tx_complete` → `.complete`. **Negative witness:** send
`tx_complete` and stop; no `.complete` derivation.

**Why faithful:** BOLT 2 `:141-145` requires consecutive `tx_complete`s. This
is the v2-establishment analogue of R25 T5’s two-lock rule; it is stated over a
separate v2 state so it neither duplicates nor weakens the splice theorem.

### T5 — `LnLean.Proofs.Protocol.DualFundingTargets.v1_open_rejected_when_dual_fund_negotiated`

**Priority:** P2. **Classification:** model extension (feature predicate +
admission gate). **Fidelity risk:** low. **Feasibility:** medium.

```lean
theorem v1_open_rejected_when_dual_fund_negotiated
    (f : NegotiatedFeatures) (o : OpenChannel) (h : f.dualFund = true) :
    ¬ AcceptsV1Open f o
```

**Hypotheses:** `f.dualFund` is true exactly when bit 28 was negotiated;
`AcceptsV1Open` is the v1 admission predicate. The theorem must not assume
`AcceptsV1Open → f.dualFund = false`; that would restate the conclusion.

**Non-vacuity witness:** `f.dualFund = true` and a well-formed v1 `OpenChannel`
payload; the admission relation has no derivation. **Negative witness:** with
`f.dualFund = false`, the ordinary v1 open remains admissible.

**Why faithful:** BOLT 2 `:845-846` says the receiver MUST fail a v1
`open_channel` if `option_dual_fund` was negotiated, and `:1217-1218` says the
opener MUST NOT send one. The current model has no bit-28 predicate; the
generic `feature_intersection` theorem is not a gate.

### T6 — `LnLean.Proofs.Protocol.DualFundingTargets.tx_serial_id_parity_disjoint`

**Priority:** P2. **Classification:** model extension (interactive-tx
vocabulary). **Fidelity risk:** low. **Feasibility:** high.

```lean
theorem tx_serial_id_parity_disjoint
    (I J : Finset Nat)
    (hI : ∀ x ∈ I, x % 2 = 0)
    (hJ : ∀ x ∈ J, x % 2 = 1) :
    Disjoint I J
```

**Hypotheses:** `I` is the set of initiator-added input/output serial ids, `J`
the non-initiator’s; every id is a `u64` value represented as `Nat`. The
theorem covers input and output parity jointly; it does **not** prove
uniqueness within a set or the 4096-message cap.

**Non-vacuity witness:** `I = {0, 2}`, `J = {1, 3}`; disjoint. **Negative
witness:** `0 ∈ J` is rejected by `hJ`.

**Why faithful:** BOLT 2 `:220-228` and `:305-311` mandate even initiator ids
and odd non-initiator ids, and receivers MUST fail wrong parity. The parity
split is what makes collision-free assembly possible; it is not an ownership
claim (`same_message_distinct_senders` still applies).

### T7 — `LnLean.Proofs.Protocol.DualFundingTargets.v2_reserve_independent_of_split`

**Priority:** P2. **Classification:** model extension (arithmetic
specification). **Fidelity risk:** low. **Feasibility:** high.

```lean
theorem v2_reserve_independent_of_split
    (o a o' a' dust : Nat)
    (h : o + a = o' + a') :
    v2ChannelReserveSatoshis (o + a) dust false =
      v2ChannelReserveSatoshis (o' + a') dust false

theorem v2_reserve_ge_dust
    (total dust : Nat) (h : dust ≤ total) :
    dust ≤ v2ChannelReserveSatoshis total dust false
```

**Hypotheses:** v2 has no per-side `channel_reserve_satoshis`; the reserve is
`max(total / 100, dust)`, with `total = o + a`. `is0 = false` (the 0-reserve
path is a trusted-peer option and is not the default).

**Non-vacuity witness:** `(o,a) = (100_000, 0)` and `(o',a') = (50_000,
50_000)` both give `max(1_000, dust)`. **Negative witness:** the v1 per-side
field would give different answers for the two splits, so it cannot be reused.

**Why faithful:** BOLT 2 `:1254-1258`, `:1325-1330` defines the reserve from the total;
pinned LDK implements the same formula at `channel.rs:7174-7186`. The theorem
complements T1: the reserve cannot recover the split, so the split must be
stored separately.

## 5. Assumptions, counterexamples, and non-vacuity risks

### 5.1 Counterexamples and scope artifacts that must remain visible

| Witness / artifact | Location | Why it matters |
|---|---|---|
| `fundingReachable_negotiation_witness` | `Handshake.lean:1097-1101` | Zero-value, same-key v1 witness. It proves v1 non-vacuity only; do not cite it as a v2 witness. |
| `funding_output_ignores_fundingSatoshis` | `FundingAuthTargets.lean:523-527` | The output commits only to keys. Contribution values need the `tx_complete` check, not the P2WSH script. |
| `same_message_distinct_senders` | `FundingAuthTargets.lean:475-487` | A v2 `tx_add_input` payload does not authenticate its sender; parity is not identity. |
| `capacity_eq_funder_plus_push` | `FundingProps.lean:279-283` | A v1 push identity. It is not dual-funding capacity and cannot be retargeted. |
| `capacity_independent_of_push` | `FundingProps.lean:287-288` | “Push does not change capacity” does not imply “contributions do not change capacity” in v2. |
| `decodeFrame_wrong_type_64` | `WaveH/H18.lean:439-440` | A v1 decoder rejection of type 64. It is not a v2 acceptance/negotiation theorem. |
| LDK Node `channel_negotiation_type: _` | `ldk-node/src/event.rs:1725-1733` | The pinned public node discards the V1/V2 discriminator; no public v2 inbound path exists. |
| LDK `InteractiveFunding` label | `types.proto:150-155`; `types.rs:252-263` | A wallet transaction classification, explicitly “once supported”, not a negotiation API. |
| Dead outbound V2 constructor | `channel.rs:16176-16178` | The core outbound path is unreachable; do not infer implementation coverage from symbol existence. |
| Zero-contribution inbound V2 | `channel.rs:16331-16333`, `:16483-16484` | The only live V2 accept path contributes no funds and no inputs. |

If T1/T2 add a sidecar, keep the existing v1 witness and `decodeFrame_wrong_type_64`
unchanged. They are regression witnesses for the v1 surface, not obstacles to
remove.

### 5.2 Assumptions that must stay explicit

1. **Feature negotiation.** Whether bit 28 was negotiated is an external
   handshake fact. `feature_intersection` only gives a generic intersection
   under the survival hypothesis (`ProtocolTargets.lean:84-99`); it does not
   imply a dual-fund channel was chosen.
2. **Interactive transaction construction.** Input selection, prevtx validity,
   scriptPubKey shape, sequence/RBF, fee responsibility, confirmed-input
   requirements, the 252 input/output caps, and the 400,000-weight cap are
   external. T3 abstracts them behind `AcceptsTxComplete`.
3. **Funding output identity.** T3 needs an explicit “this output is the
   channel funding output” premise. Without it, the sum law is ambiguous in a
   multi-output transaction.
4. **Off-chain state recovery.** A restart can lose an in-progress negotiation;
   BOLT 2 `:583-621` says to forget it before `tx_signatures`. The sidecar
   assumes externally recovered state and does not prove persistence.
5. **Signatures and key ownership.** `tx_signatures` validity and input
   ownership are external; the model only records that a round was signed.
6. **Chain confirmation.** Funding confirmation, depth, and outpoint derivation
   remain external, as in R05.
7. **API asynchrony.** `OpenChannel`/`open_channel` returning an id is not a
   completed channel (`api.proto:1292`; `lib.rs:1374-1500`). Do not state a
   “normal on API return” theorem.

### 5.3 Non-weakening and non-hiding rules

* **Do not add a v2 constructor to `Step` that changes `fundingValue`.** It
  would falsify `step_fundingValue_eq` (`StateTransitionTargets.lean:417-419`)
  and break `GlobalConservation.ConservedTransition`
  (`GlobalConservation.lean:226-228`). Use the sidecar and a separately named
  relation.
* **Do not retarget `capacity_eq_funder_plus_push` as dual-funding coverage.**
  It is v1 arithmetic with a `push_msat` premise that v2 does not have. A
  rename would hide the missing contribution split.
* **Do not define `WellFormedV2` with `0 < acceptContribution`.** T2 and BOLT 2
  `:1312` refute it; pinned LDK’s own accept path uses zero.
* **Do not prove T1 with equal splits or zero totals.** The theorem must
  exhibit two distinct, individually admissible splits whose projections
  coincide. Otherwise it is vacuous.
* **Do not prove T3 by assuming the output value equals the sum.** That
  assumption is the conclusion; it must follow from `AcceptsTxComplete`.
* **Do not weaken `decodeFrame_wrong_type_64` or delete the v1 witness.** v1
  rejection remains correct; it simply is not v2 coverage.
* **Do not treat `feature_intersection` as bit-28 behavior.** It is a generic
  support-set law and has no dual-fund semantics.
* **Do not treat the `InteractiveFunding` enum or the dead `new_outbound`
  constructor as protocol support.** The first is a wallet label, the second is
  unreachable code.
* **Do not change `docs/SCOPE.md` as part of this review.** Any scope change is
  a parent/maintainer decision.

## 6. Wave-13 recommendation

**Recommendation: defer implementation; treat full dual funding / interactive
tx as external and unmodelled. Do not add v2 to the main channel machine in
wave 13.**

Reasons:

1. **No public pinned path to model.** LDK Node and LDK Server expose a single
   funder amount plus push (`lib.rs:1374-1500`; `api.proto:578-607`). The core
   inbound V2 skeleton contributes zero funds and inputs
   (`channel.rs:16331-16333`), and outbound V2 is dead code (`:16176-16178`).
   End-to-end dual funding is not implemented at this pin, so an “LDK-faithful”
   Lean model would have no positive behavior to match.
2. **The current state cannot represent the split.** `FundingNegotiation` has
   one value plus v1 push; `Channel` has one funding value. T1 is a
   non-representability theorem, not a missing arithmetic lemma.
3. **The cheap, faithful slice is scoping, not protocol.** T1/T2 (and
   optionally T5–T7) are small sidecar statements that make the gap explicit
   and prevent false coverage claims. They do not require changing `Channel`,
   `Step`, `ProtocolEvent`, or `FundingNegotiation`.
4. **The expensive part is genuinely external.** Interactive tx construction,
   input ownership, fees, RBF, persistence, and chain confirmation are outside
   the current model and outside any wave-13 proof budget.

**Top proposed target:** `v2_contribution_split_not_injective` (T1). It is the
smallest faithful statement that shows why the v1 single-funder record cannot
be reused for v2, and it has a concrete two-split witness.

**If the parent authorizes a wave-14 sidecar:** implement T1 and T2 first in a
new module with the `V2Negotiation` sketch, no edits to existing definitions.
Add T3 only with an explicit abstract `FundingTx`/`AcceptsTxComplete` contract.
Add T5–T7 as optional small gates. Do **not** claim “dual funding is modelled”;
state that per-side contributions, `tx_complete`, reserve arithmetic, and
serial-id parity are modelled in isolation, while interactive tx, ownership,
fees, RBF, persistence, and confirmation remain external.

**If the parent needs a single decision:** mark dual funding as an
external/deferred barrier and keep the v1 theorems as the model’s actual
coverage. That is more honest than a v2-shaped theorem that silently assumes
the missing contribution split.

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

LDK Node `Cargo.toml:89-98` declares the core rev
`d7a980641c6325ddda5072a0f470ef8392676cf5`. The workspace
`refs/rust-lightning` checkout has tip `fe4900930c6bd5786ec4203274d7cf312776a5a6`;
core citations were read with
`git -C refs/rust-lightning show d7a980...:lightning/src/ln/<file>`.
Line numbers can drift by a few lines between the two revisions; the paths and
symbol names are stable.

### 7.2 Lean commands and files inspected

```sh
rg -n -i "dual.fund|dual_fund|open_channel2|interactivetx|interactive tx" docs LnLean agents/TODO-REPAIR.md
rg -n "structure OpenChannel where|def toFundingNegotiation|structure FundingPhase|def fundingStep|inductive FundingReachable|fundingReachable_negotiation_witness" LnLean/Protocol/Handshake.lean
rg -n "structure FundingNegotiation|structure FundingParams" LnLean/Bitcoin/Funding.lean
rg -n "inductive ProtocolEvent|inductive Step|Splicing, quiescence|def phaseRank" LnLean/Channel/State.lean
rg -n "structure Channel where|Multi-party channels" LnLean/Channel/Types.lean
rg -n "inductive MsgKind|def wireType|def kindOfType|open_channel2 is deliberately" LnLean/Protocol/Messages.lean
rg -n "decodeFrame_wrong_type_64" LnLean/Proofs/WaveH/H18.lean
rg -n "capacity_eq_funder_plus_push|capacity_independent_of_push" LnLean/Proofs/Bitcoin/FundingProps.lean
rg -n "same_message_distinct_senders|funding_output_ignores_fundingSatoshis" LnLean/Proofs/Bitcoin/FundingAuthTargets.lean
rg -n "step_fundingValue_eq|ledgerValue_step|updateStep_preserves_ledger" LnLean/Proofs/Channel/StateTransitionTargets.lean
rg -n "ConservedTransition" LnLean/Proofs/PhaseC2/GlobalConservation.lean
rg -n "feature_intersection" LnLean/Proofs/ProtocolTargets.lean
rg -n "openChannelWire_end_to_end" LnLean/Proofs/Protocol/OpenChannelWireTargets.lean
rg -n "routed_open_to_funding_construction" LnLean/Proofs/Protocol/OpenChannelRoutingTargets.lean
```

Files read in full or relevant sections:

* `docs/AGENT-PROTOCOL.md`, `docs/OPEN-ISSUES.md`,
  `docs/THEOREM-INDEX.md`, `docs/TRACEABILITY.md`, `docs/SCOPE.md`,
  `agents/TODO-REPAIR.md`,
  `agents/reports/swarm12/S12-POST-INTEGRATION-AUDIT.md`,
  `agents/reports/wave13-review/LDK-REFS.md`.
* `LnLean/Protocol/Handshake.lean`, `LnLean/Protocol/Messages.lean`,
  `LnLean/Bitcoin/Funding.lean`, `LnLean/Channel/Types.lean`,
  `LnLean/Channel/State.lean`, `LnLean/Basic/Core.lean`.
* `LnLean/Proofs/Bitcoin/FundingProps.lean`,
  `LnLean/Proofs/Bitcoin/FundingAuthTargets.lean`,
  `LnLean/Proofs/Protocol/OpenChannelWireTargets.lean`,
  `LnLean/Proofs/Protocol/OpenChannelRoutingTargets.lean`,
  `LnLean/Proofs/ProtocolTargets.lean`,
  `LnLean/Proofs/Channel/StateTransitionTargets.lean`,
  `LnLean/Proofs/PhaseC2/GlobalConservation.lean`,
  `LnLean/Proofs/WaveH/H18.lean`.
* Adjacent reports `R05-channel-lifecycle.md` and `R25-splicing.md` were read
  to avoid duplicating their v1-lifecycle and splice-interactive-tx results.

### 7.3 LDK commands and files inspected

```sh
rg -n "open_channel_inner|create_channel|create_channel_to_trusted_peer_0reserve|splice_in" \
  /tmp/opencode/ldk-refs/ldk-node/src/lib.rs
rg -n "channel_negotiation_type|accept_inbound_channel|OpenChannelRequest" \
  /tmp/opencode/ldk-refs/ldk-node/src/event.rs
rg -n "dual_fund|supports_dual_fund|requires_dual_fund" \
  /tmp/opencode/ldk-refs/ldk-node/src/ffi/types.rs
rg -n -i "dual_fund|open_channel2|accept_channel2|interactive" \
  /tmp/opencode/ldk-refs/ldk-node/src --include='*.rs'
rg -n -i "dual_fund|open_channel2|accept_channel2" \
  /tmp/opencode/ldk-refs/ldk-server --include='*.rs' --include='*.proto'
rg -n "OpenChannelRequest|rpc OpenChannel|SpliceIn" \
  /tmp/opencode/ldk-refs/ldk-server/ldk-server-grpc/src/proto/api.proto
rg -n "InteractiveFunding|once supported|V2" \
  /tmp/opencode/ldk-refs/ldk-server/ldk-server-grpc/src/proto/types.proto \
  /tmp/opencode/ldk-refs/ldk-server/ldk-server-grpc/src/types.rs
```

Core (pinned `d7a980`) commands:

```sh
git -C refs/rust-lightning show d7a980641c6325ddda5072a0f470ef8392676cf5:lightning/src/ln/channel.rs \
  | rg -n "new_inbound|new_outbound|our_funding_contribution|our_funding_inputs|get_v2_channel_reserve_satoshis|funding_satoshis:"
git -C refs/rust-lightning show d7a980641c6325ddda5072a0f470ef8392676cf5:lightning/src/ln/channelmanager.rs \
  | rg -n "handle_open_channel_v2|PendingV2Channel::new_inbound|InboundChannelFunds::DualFunded|create_channel|set_dual_fund_optional"
git -C refs/rust-lightning show d7a980641c6325ddda5072a0f470ef8392676cf5:lightning/src/ln/msgs.rs \
  | rg -n "pub struct (OpenChannelV2|AcceptChannelV2|TxAddInput|TxAddOutput|TxComplete|TxSignatures|TxAbort)"
git -C refs/rust-lightning show d7a980641c6325ddda5072a0f470ef8392676cf5:lightning/src/ln/wire.rs \
  | rg -n "impl Encode for msgs::(OpenChannelV2|AcceptChannelV2|TxAddInput|TxAddOutput|TxComplete|TxSignatures|TxAbort)"
```

BOLT commands:

```sh
rg -n "open_channel2|accept_channel2|tx_complete|tx_abort|serial_id|option_dual_fund" \
  refs/bolts/02-peer-protocol.md refs/bolts/09-features.md
```

LDK Server files inspected: `ldk-server-grpc/src/proto/api.proto`,
`ldk-server-grpc/src/proto/types.proto`, `ldk-server-grpc/src/types.rs`,
`ldk-server/src/util/proto_adapter.rs`. LDK Node files inspected:
`src/lib.rs`, `src/event.rs`, `src/ffi/types.rs`, `src/wallet/mod.rs`.

### 7.4 Constraints observed

* No branch switch, creation, rebase, commit, or push.
* No Lean, docs, script, test, vendor, or other lane report edits.
* The only file written by this lane is
  `agents/reports/wave13-review/R26-dual-funding-negotiation.md`.
* No cargo tests, no network access, and no full-tree build.
