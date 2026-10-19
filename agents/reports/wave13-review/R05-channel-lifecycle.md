# R05 — Channel lifecycle and peer/funding handshake
**Status:** read-only review
**Pins:** LDK Node `fa123fed131e27ecc420b77fa7086fcf1ddaebb8`, LDK Server `c17dc11dde38f88c53457039ddf30c6b90a63ba2`
**Review branch:** `repair/integrated` (no branch, commit, or non-report file changes made)

## 1. Scope and current Lean surface

This lane covers the BOLT 2 channel-establishment lifecycle from `open_channel`
through `channel_ready`, and the failure/abort/reconnect paths that can
interrupt it. It does **not** re-review funding-script cryptography
(`LN-L1-001`), signature attribution (`LN-PR-003`), transaction relay, or HTLC
commitment mechanics except where they constrain a lifecycle transition.

### 1.1 Catalog claims that touch this surface

| Row | Catalog claim | Actual Lean target | What it does and does not cover |
|---|---|---|---|
| `LN-PR-001` | `open_channel` bounds and routed delivery reach `funding_created` | `LnLean.Protocol.Handshake.open_bounds`; `OpenChannelWireTargets.openChannelWire_end_to_end`; `OpenChannelRoutingTargets.openRoute_initial_to_fundingCreated` | Covers wire bounds, construction, and an attributed route to `funding_created`. It does not connect the route to `Channel.phase`, and does not model accept/funding rejection. |
| `LN-PR-002` | "The channel enters normal operation only after both channel_ready messages." | `LnLean.Protocol.Handshake.channel_ready_gate` (`LnLean/Proofs/WaveD/D18.lean:331-336`) | The theorem is definitional over `HandshakeState`: `s.ready = true ↔ s.channelReadySent = true ∧ s.channelReadyReceived = true`. It has no link to `Channel.phase = normal` and no per-message channel state. |
| `LN-PR-003` | `funding_signed` carries a valid funding signature under explicit signing/key hypotheses | `LnLean.Protocol.Handshake.funding_signed_signing_contract`; `LnLean.Proofs.Channel.SighashTargets.funding_and_commitment_signing_contract` | Covers signature semantics and attribution, not the ordering of `funding_signed` relative to `channel_ready`. |
| `LN-CH-001` | Ledger transitions conserve funding | `LnLean.Security.Ledger.step_conserves` | Orthogonal to the lifecycle; it does not assert phase ordering. |
| `LN-CH-002` | Commitment outputs are non-negative and bounded | `LnLean.Channel.Commitment.outputs_nonnegative` | Orthogonal to the lifecycle. |

### 1.2 Channel phase machine

`ChannelPhase` has five constructors: `negotiating`, `awaitingLockin`,
`normal`, `shuttingDown`, `closed` (`LnLean/Basic/Core.lean:235-241`).
The `Channel` record (`LnLean/Channel/Types.lean:162-175`) carries only
`phase`, the two commitment counters, balances, and HTLCs. It has **no**
funding-depth field, no `funding_signed`-seen flag, no per-direction
`channel_ready` flags, no error/failed flag, and no creation height.

`ProtocolEvent` (`LnLean/Channel/State.lean:67-78`) has exactly ten
constructors: `openChannel`, `acceptChannel`, `fundingCreated`,
`fundingSigned`, `fundingLocked`, `commitmentSigned`, `revokeAndAck`,
`updateFee`, `shutdown`, `closingSigned`. `Step` (`State.lean:86-127`)
implements only legal, forward transitions:

* `openChannel` and `acceptChannel` are identity steps in `negotiating`.
* `fundingCreated` moves `negotiating → awaitingLockin`.
* `fundingSigned` is an **identity step** in `awaitingLockin`; it records
  nothing.
* `fundingLocked` moves `awaitingLockin → normal` with no other premise.
* `shutdown` is legal **only** from `normal`; `closingSigned` moves
  `shuttingDown → closed`.
* There is no constructor for `error`, `channel_reestablish`, abort,
  unfunded cooperative close, funding timeout, disconnect, or retry.

`phaseRank` (`State.lean:157-162`) is monotone along `Step`
(`step_phaseRank_le`), so the current machine cannot represent a phase
regression. `no_step_from_closed` makes `closed` absorbing.

The exact channel-level counterexamples are already in the tree:

* `trace_channelReady_without_fundingSigned`
  (`LnLean/Proofs/Channel/StateMachineProps.lean:364-370`): the two-event
  trace `[.fundingCreated, .fundingLocked]` reaches `normal`.
* `fundingSigned_not_mem_channelReady_trace` (`:372-374`).
* `channelReady_reachable_without_fundingSigned` (`:381-390`): there is a
  reachable `normal` channel whose trace omits `fundingSigned`.

The comment at `:378-380` says the corrected ordering premise "would need a
new `Channel` field recording that `funding_signed` was seen." That is a
model-extension requirement, not a proof-only gap.

### 1.3 Handshake and funding-negotiation layers

`HandshakeState` (`LnLean/Protocol/Handshake.lean:78-99`) has the ten
milestone flags plus `acceptChannel?`. `ready` is
`s.channelReadySent && s.channelReadyReceived` (`:113-114`). The handshake
machine **does** encode the ordering gap that the channel machine lacks:

* `HandshakeState.Inv` (`:117-123`) states that any `channel_ready`
  (sent or received) implies `funding_signed` (sent or received).
* `canSendChannelReady` and `canRecvChannelReady` (`:182-189`) require
  `fundingSignedSent ∨ fundingSignedReceived`.
* `handshakeStep_inv` and `reachable_inv` (`:268`, `:342-344`) preserve
  the invariant.

`FundingPhase` (`LnLean/Protocol/Handshake.lean:935-989`) is a separate
four-message machine (`sendOpen`, `recvOpen`, `sendAccept`, `recvAccept`;
`fundingStep` at `:1002-1010`). It records the funding keys but has no
`funding_created`/`funding_signed`/`channel_ready` stage and no failure path.
It is not connected to `Channel.phase`.

### 1.4 Error, reconnect, persistence, and liveness layers

* `ErrorProps` (`LnLean/Proofs/Protocol/ErrorProps.lean`) proves that a fatal
  BOLT 1 `error` maps a `ChannelView` to `closed`
  (`applyMsg_error`, `applyToChannel_error_matching`, `:192-252`). But it
  explicitly says `ChannelView` is a two-field projection disconnected from
  `Channel.State`, and connecting `closed` to the state machine is "an open
  refinement" (`:65-67`). It also says no shutdown attempt, retry, timeout,
  or connection teardown is modelled (`:69-77`).
* `ChannelReestablishProps` (`LnLean/Proofs/Protocol/ChannelReestablishProps.lean`)
  proves counter monotonicity and retransmission laws over `ChannelRecord`/
  `PeerState`. It states that `PeerState.receive` has no error/close result,
  neither `PeerState` nor `Channel` has an error phase, and "fail the channel"
  is not modelled (`:98-103`). `shutdown`/`closing_signed` retransmission and
  `next_funding` are out of scope (`:104-106`).
* `Liveness` (`LnLean/Proofs/Liveness.lean`) proves the conditional
  lock-in liveness `fair_awaitingLockin_eventually_normal`, the reconnect
  retention result `reconnect_preserves_channelReady` (`:573-582`), and
  `reconnect_resend_completes_lockin` (`:585-598`). Its "What is NOT
  modelled" section is decisive for this lane: no wall clock/timers, **no
  `Msg → ProtocolEvent` mapping**, **no joint peer/channel transition**, no
  lossy-link fairness, and no HTLC event in `Channel.Step` (`:83-105`).
* `PersistenceRecovery` (`LnLean/Proofs/PhaseC3/PersistenceRecovery.lean`)
  proves `ready_snapshot_reaches_normal` (`:661-668`) only under the
  hypothesis `s.ready = true → c.phase = awaitingLockin`. The comment at
  `:655-660` says `Liveness` does not map `Msg.channelReady` to
  `ProtocolEvent.fundingLocked`; the caller must supply that bridge.

**Bottom line for section 1:** the handshake layer has good local ordering
laws and the channel layer has good local transition laws, but there is no
joint state relation, no message-to-event map, and no failure/timeout/abort
path. The most important lifecycle claim (`LN-PR-002`) is only proved inside
`HandshakeState`, not for the `Channel` machine that defines `normal`.

## 2. LDK datapoints (with `file:line`)

All LDK citations are read-only inspection of the pinned clones. LDK Node is
the public node API; LDK Server is the gRPC surface; rust-lightning is the
pinned `refs/rust-lightning` tree used by the repo for behavioral anchors.

### 2.1 Connect, disconnect, and retry

* `ldk-node/src/connection.rs:78-84` — `connect_peer_if_necessary` returns
  `Ok(())` immediately if the peer is already connected. Connection is
  idempotent, not a lifecycle event.
* `connection.rs:86-112` — `do_connect_peer` deduplicates concurrent attempts
  by subscribing to a pending connection; duplicate attempts do not create
  duplicate peers.
* `connection.rs:124-230` — `do_connect_peer_internal` resolves addresses and
  tries each socket address; failure is reported as `Error::ConnectionFailed`.
* `connection.rs:245-274` — `await_connection` loops until the peer appears or
  the connection-closed future resolves. There is **no timeout** in this
  loop; a caller can wait indefinitely.
* `ldk-node/src/lib.rs:1324-1354` — `connect` blocks on
  `connect_peer_if_necessary`, then optionally persists the peer.
* `lib.rs:1356-1374` — `disconnect` removes the peer from the peer store and
  calls `disconnect_by_node_id`; it does not report per-channel closure.
* `lib.rs:2476-2500` — `list_peers` reports connected and known-offline peers
  with `is_persisted`/`is_connected`, i.e. connectivity is a separate
  dimension from channel phase.

### 2.2 Open channel is synchronous at the API boundary, asynchronous in state

* `ldk-server/src/api/open_channel.rs:23-93` — `handle_open_channel` parses the
  request, calls one of the `open_*_channel` variants, and returns
  `OpenChannelResponse { user_channel_id }`. The call returns once the channel
  has been created locally; it does **not** wait for `accept_channel`,
  funding confirmation, or `channel_ready`.
* `ldk-server/src/api/error.rs:107-123` — `ChannelCreationFailed` and
  `ConnectionFailed` are mapped to `LdkServerErrorCode::LightningError`.
  These are synchronous API failures, distinct from later asynchronous
  closure events.
* `ldk-node/src/lib.rs:1374-1500` — `open_channel_inner` first calls
  `connect_peer_if_necessary`, checks funds, builds a user config, then calls
  `create_channel*`. The returned `UserChannelId` identifies a channel that is
  still pending.
* `lib.rs:1566-1655` — the public `open_channel`/`open_channel_with_all`
  wrappers delegate to `open_channel_inner`.

### 2.3 Funding confirmation, readiness, and usability

* `ldk-node/src/types.rs:555-575` — `ChannelDetails` exposes
  `confirmations_required` (selected by the fundee; `None` for an outbound
  channel until accept), `confirmations`, `is_channel_ready`, and
  `is_usable`.
  * `is_channel_ready`: both parties have exchanged `channel_ready` **and**
    the channel is not currently being shut down (`:565-570`).
  * `is_usable`: a strict superset that also requires the peer to be
    connected and the channel not to be negotiating shutdown (`:571-574`).
* `rust-lightning/lightning/src/ln/channel.rs:799-819` — the internal
  `ChannelState` is a five-state enum: `NegotiatingFunding`,
  `FundingNegotiated`, `AwaitingChannelReady`, `ChannelReady`,
  `ShutdownComplete`. This is finer than Lean's five phases: it separates
  "awaiting `funding_signed`" (`FundingNegotiated`) from "awaiting funding
  confirmation / `channel_ready`" (`AwaitingChannelReady`).
* `channel.rs:12185-12210` — `check_get_channel_ready` returns `None` unless
  `check_funding_meets_minimum_depth` passes; only then does it set
  `our_channel_ready` or promote `AwaitingChannelReady` to `ChannelReady`.
* `channel.rs:1467` — `FUNDING_CONF_DEADLINE_BLOCKS: u32 = 2016`, "the one
  suggested in BOLT 2."
* `channel.rs:12721-12731` — for an inbound channel with no funding
  confirmation at `channel_creation_height + FUNDING_CONF_DEADLINE_BLOCKS`,
  LDK returns `ClosureReason::FundingTimedOut`.

### 2.4 Asynchronous lifecycle events and closure reasons

* `ldk-node/src/event.rs:258-303` — `ChannelPending`, `ChannelReady`, and
  `ChannelClosed` are distinct events. `ChannelPending` carries the funding
  outpoint; `ChannelReady` is emitted when a new channel is ready or a splice
  completes; `ChannelClosed` carries an optional `ClosureReason`.
* `event.rs:2260-2280` — `DiscardFunding` is a separate event for a funding
  transaction that will never be broadcast.
* `rust-lightning/lightning/src/events/mod.rs:578-615` — `ClosureReason`
  includes `FundingTimedOut` (`:583`), `DisconnectedPeer` (`:599`),
  `CounterpartyCoopClosedUnfundedChannel` (`:608`), and
  `LocallyCoopClosedUnfundedChannel` (`:614`).
  * `FundingTimedOut`: funding failed to confirm in time, or the counterparty
    failed to fund in time.
  * `DisconnectedPeer`: the peer disconnected **prior to funding completing**;
    the spec mandates forgetting the channel entirely.
  * The two `*CoopClosedUnfundedChannel` variants: a cooperative close of a
    channel that was never funded; the channel is immediately closed.

### 2.5 BOLT 2 anchors

* `refs/bolts/02-peer-protocol.md:1046-1049` — `channel_ready` indicates
  sufficient confirmations; "Once both nodes have sent this, the channel
  enters normal operating mode."
* `:1068-1093` — sender requirements: the non-opener SHOULD wait for
  `minimum_depth`; the opener is free to send at any time; the coinbase case
  requires 100 blocks.
* `:1099-1101` — the non-funding node SHOULD forget the channel if it does
  not see the correct funding transaction after 2016 blocks.
* `:1108` — from the wait for `channel_ready` onward, either node MAY send
  `error` and fail the channel after a reasonable timeout.
* `:2152` — a node MAY send `shutdown` before `channel_ready`, i.e. before
  `minimum_depth`; but it MUST NOT send `shutdown` before `funding_created`
  (funder) or `funding_signed` (fundee).
* `:3484-3495` — on reconnect, if `next_commitment_number` is 1 on both sides,
  the node MUST retransmit `channel_ready`; a zero `next_commitment_number`
  means the channel must be failed.

## 3. Gap matrix

Statuses use the lane's required vocabulary. "Missing" means the behavior is
absent from the current `Step`/`ProtocolEvent` vocabulary; because `Step` is
intentionally a legal-transition relation, a missing constructor is not by
itself a soundness bug, but it is a completeness gap for any claim that the
model covers the lifecycle.

| Behavior | Lean status | LDK / BOLT evidence | Gap / counterexample | Priority |
|---|---|---|---|---|
| `open_channel` → `accept_channel` negotiation | partially covered | `ldk-server/api/open_channel.rs:23-93`; BOLT 2 `:629-640`, `:908-980`; `OpenChannelRoutingTargets.openRoute_initial_to_fundingCreated` | `openChannel`/`acceptChannel` are identity steps in `negotiating`; `Channel` records neither message, so "accept received" is not a premise for `fundingCreated`. `FundingPhase` records it, but is not linked to `Channel.phase`. | P1 |
| `funding_created` requires a valid accept | partially covered | BOLT 2 `:968-1000`; `OpenChannelWireTargets.acceptKey_bound_before_fundingCreated_wire` | The wire/construction layer proves accept-key binding, but any `negotiating` `Channel` can take `Step.fundingCreated`. There is no state-level "accept seen" guard. | P1 |
| `funding_signed` precedes `channel_ready` / lock-in | partially covered at handshake; **missing at channel** | BOLT 2 `:1068-1093`; `Handshake.lean:182-189` (`canSendChannelReady` requires `fundingSigned*`); `Handshake.lean:117-123` (`Inv`) | Channel-level `Step.fundingSigned` is a no-op. `channelReady_reachable_without_fundingSigned` (`StateMachineProps.lean:381-390`) is a concrete reachable-`normal` counterexample omitting `fundingSigned`. `trace_channelReady_without_fundingSigned` (`:364-370`) is the witness. | **P0** |
| `normal` requires **both** `channel_ready` messages | contradicted under a global reading; partially covered at handshake | BOLT 2 `:1046-1049`; `D18.lean:331-336`; `ldk-node/types.rs:565-570` | `channel_ready_gate` is only `HandshakeState.ready ↔ sent ∧ received`; it is definitional and never mentions `Channel.phase`. The channel machine has a single `fundingLocked` event and no sent/received flags, so `normal` is reachable after one event. This contradicts `LN-PR-002` if that row is read as a global claim. | **P0** |
| Funding confirmation / `minimum_depth` before lock-in | missing | BOLT 2 `:1068-1093`; `channel.rs:12185-12210`; `ldk-node/types.rs:559-568` | `AcceptChannel.minimumDepth` exists on the wire (`Messages.lean:143-158`, field `:149`) but is dropped by `Channel`. `Step.fundingLocked` has no depth premise. | P1 |
| Funding timeout after 2016 blocks | missing (external timer) | BOLT 2 `:1099-1101`; `channel.rs:1467`, `:12721-12731`; `events/mod.rs:583` | No height/creation field and no timeout event. `Liveness` explicitly has no wall clock or timers (`:83-89`). | P1 |
| Fatal `error` fails the channel | missing at the state machine | BOLT 1 `:384-398`; `ErrorProps.lean:65-77`, `:192-252`; `events/mod.rs:578-615` | `ErrorProps` maps `ChannelView` to `closed`, but `ChannelView` is disconnected from `Channel.State`; `ProtocolEvent` has no `error` constructor. | P1 |
| `shutdown` before `channel_ready` / unfunded abort | missing | BOLT 2 `:2152`; `events/mod.rs:608-615` (`*CoopClosedUnfundedChannel`) | `Step.shutdown` is legal only from `normal` (`State.lean:122-124`). There is no abort/unfunded-close transition from `negotiating` or `awaitingLockin`. | P1 |
| Disconnect during funding | unmodelled-external | `events/mod.rs:594-599` (`DisconnectedPeer`); `ldk-node/connection.rs:78-112`; `event.rs:2260` (`DiscardFunding`) | `Channel.Step` has no disconnect event; `Liveness` has no joint peer/channel transition (`:92-98`). LDK's `DisconnectedPeer` mandates forgetting the channel. | P2 |
| `channel_reestablish` / retransmission | partially covered (counters); missing (lifecycle) | BOLT 2 `:3484-3495`; `ChannelReestablishProps.lean:98-103`; `Liveness.lean:573-598` | Counters and retransmission are proved over `ChannelRecord`/`PeerState`; there is no `Channel` receive step, no fail-on-zero transition, and no phase effect. | P2 |
| Dynamic usability can regress | unmodelled-external | `ldk-node/types.rs:571-574` (`is_usable` requires connected and not negotiating shutdown) | Lean `phaseRank` is monotone (`State.lean:164-171`); `normal` can never become "connected=false" or "shutting down" without a phase change. Connection usability is a separate dimension. | P2 |
| API-open succeeds before lifecycle completes | unmodelled-external | `ldk-server/api/open_channel.rs:23-93`; `ldk-node/event.rs:258-303` | `open_channel` returns a `user_channel_id` synchronously; `ChannelPending`/`ChannelReady`/`ChannelClosed` arrive asynchronously. Lean has a single `Step` relation and no event queue/API boundary. | P2 |
| Phase regression | unmodelled-external (monotonicity is a model artifact) | `ldk-node/types.rs:571-574`; `channel.rs:799-819` | `phaseRank` is monotone and `closed` is absorbing (`no_step_from_closed`). Any model that adds reconnect/reopen or dynamic usability cannot keep the unconditional monotonicity theorem. | P2 |

## 4. Proposed targets

The targets below are **not** claimed to compile as written; they are statement
shapes for wave-14 scoping. Each is tagged with the required classification:
**model extension** (new fields/constructors/relations in Lean) or **external
assumption** (chain height, timer, transport, or peer behavior supplied as an
explicit hypothesis). No target is proof-only except the small T7/T8 receive
step.

### T1 — `LnLean.Proofs.Channel.LifecycleTargets.funding_signed_before_lockin`

**Priority:** P0. **Classification:** model extension (new `Channel` field).
**Fidelity risk:** low. **Feasibility:** medium (record change ripples through
`witnessChannel`, `step?`, `Step` case splits, and every trace theorem).

```lean
-- Add `fundingSignedSeen : Bool` to `Channel`, initially false.
-- `Step.fundingSigned` sets it; `Step.fundingLocked` requires it.
theorem funding_signed_before_lockin {c d : Channel} {es : List ProtocolEvent}
    (h : Trace c es d) (hd : d.phase = ChannelPhase.normal) :
    d.fundingSignedSeen = true
```

**Hypotheses:** `Trace` uses the extended `Step`; `fundingSigned` is the only
event that sets the flag; `fundingLocked` has the flag as a constructor
premise. **Non-vacuity witness:** `[.fundingCreated, .fundingSigned,
.fundingLocked]` reaches `normal` with `fundingSignedSeen = true`. **Negative
witness:** `[.fundingCreated, .fundingLocked]` must be rejected; this replaces
the current positive counterexample. **Why faithful:** BOLT 2 requires
`funding_signed` before `channel_ready`, and `HandshakeState.canSendChannelReady`
already enforces exactly this at the handshake layer. The channel machine is
the outlier.

**Non-vacuity preservation:** do not delete
`channelReady_reachable_without_fundingSigned`. Keep it as a theorem about an
explicitly named permissive/legacy relation (for example `LegacyStep`) so the
old counterexample remains a regression witness rather than silently
disappearing.

### T2 — `LnLean.Proofs.Protocol.LifecycleTargets.joint_reachable_lifecycle_bridge`

**Priority:** P0 (strategic). **Classification:** model extension (joint
handshake/channel relation). **Fidelity risk:** high. **Feasibility:** low to
medium; this is the largest proposal.

```lean
def LifecycleBridged (h : HandshakeState) (c : Channel) : Prop :=
  (c.phase = ChannelPhase.normal → h.ready = true) ∧
  (h.ready = true → c.phase = ChannelPhase.awaitingLockin ∨
                     c.phase = ChannelPhase.normal)

theorem joint_reachable_lifecycle_bridge
    {h : HandshakeState} {c : Channel}
    (hr : JointReachable (HandshakeState.initial, c₀) (h, c)) :
    LifecycleBridged h c
```

**Hypotheses:** a new `JointStep` relation maps each `send`/`recv` message to
both `handshakeStep` and `Channel.Step`; `c₀` is the initial channel; the
joint relation preserves the bridge. **Non-vacuity witness:** the happy-path
joint trace `open_channel`, `accept_channel`, `funding_created`,
`funding_signed`, `channel_ready` (send and receive). **Why faithful:** it
transports the existing `channel_ready_gate` and `HandshakeState.Inv` to the
channel phase without assuming the conclusion. It also makes the `ready` →
`normal` direction explicit; the reverse (`normal` → `ready`) is the safety
direction that `LN-PR-002` actually needs.

**Fidelity risk:** a joint machine can easily duplicate or diverge from the
existing `PeerState`/`ChannelRecord` layer. Require a maintainer-approved
design before implementation. Do not weaken `LifecycleBridged` to a bare
hypothesis `c.phase = normal → h.ready = true`; that would restate the target.

### T3 — `LnLean.Proofs.Channel.LifecycleTargets.funding_locked_requires_depth`

**Priority:** P1. **Classification:** model extension + external chain data.
**Fidelity risk:** medium (opener asymmetry). **Feasibility:** medium.

```lean
-- Add `fundingDepth requiredDepth : Nat` to `Channel`.
-- `requiredDepth` is populated from `AcceptChannel.minimumDepth`.
theorem funding_locked_requires_depth {c c' : Channel}
    (h : Step c ProtocolEvent.fundingLocked c') :
    c.requiredDepth ≤ c.fundingDepth
```

**Hypotheses:** depth is supplied by an explicit `ChainView`/oracle; the
accepter path requires `minimumDepth`, the opener path may use a weaker guard
(BOLT 2 says the opener is free to send early). **Non-vacuity witness:**
`requiredDepth = 6`, `fundingDepth = 6`; negative: `fundingDepth = 0` with
`requiredDepth = 6` is rejected. **Why faithful:** it matches BOLT 2
`:1068-1093` and LDK `check_get_channel_ready`
(`channel.rs:12185-12210`). **Caution:** do not state a universal
"`fundingLocked` requires depth" without the opener/fundee case split; that
would contradict BOLT 2's opener allowance. This is a model extension plus an
external chain-data assumption, not a pure Lean proof.

### T4 — `LnLean.Proofs.Protocol.LifecycleTargets.error_reaches_closed`

**Priority:** P1. **Classification:** model extension (new `ProtocolEvent`
constructor). **Fidelity risk:** low. **Feasibility:** medium.

```lean
-- Add `ProtocolEvent.error (e : ErrorMsg)` and a `Step.error` constructor
-- from every non-closed phase to `closed`.
theorem error_from_any_live_phase (c : Channel) (e : ErrorMsg)
    (h : c.phase ≠ ChannelPhase.closed) :
    ∃ c', Step c (.error e) c' ∧ c'.phase = ChannelPhase.closed
```

**Hypotheses:** the error's `channel_id` matches; the all-zero broadcast form
is peer-scoped (the current `ErrorProps` list model). **Non-vacuity witness:**
an `error` from `negotiating`, `awaitingLockin`, `normal`, and `shuttingDown`.
**Why faithful:** BOLT 1 `:384-398` says a received `error` MUST fail the
referred channel; `ErrorProps.applyToChannel_error_matching`
(`:249-252`) already proves the `ChannelView` version. The target is the
missing refinement from `ChannelView` to `Channel.State`. **Non-vacuity
preservation:** keep
`handleInbound_error_unknown_ignored` and
`applyToChannel_error_preserves_other` to ensure the new constructor does not
close unrelated channels.

### T5 — `LnLean.Proofs.Channel.LifecycleTargets.unfunded_abort_reaches_closed`

**Priority:** P1. **Classification:** model extension. **Fidelity risk:**
medium (the `negotiating` phase conflates pre- and post-`funding_signed`
states). **Feasibility:** medium.

```lean
-- Add `ProtocolEvent.abort` / `unfundedClose`, legal from
-- `negotiating` and `awaitingLockin`; extend `shutdown` to
-- `awaitingLockin` only when `fundingSignedSeen = true`.
theorem unfunded_abort_reaches_closed {c c' : Channel}
    (h : Step c ProtocolEvent.abort c') :
    c'.phase = ChannelPhase.closed

theorem shutdown_before_channel_ready_legal {c c' : Channel}
    (h : Step c ProtocolEvent.shutdown c') :
    c.phase = ChannelPhase.normal ∨ c.phase = ChannelPhase.awaitingLockin
```

**Hypotheses:** `abort` is local/peer-initiated and does not require a
`closing_signed` dance; `shutdown` from `awaitingLockin` requires
`fundingSignedSeen` in the first version. **Non-vacuity witness:**
`awaitingLockin → shutdown → shuttingDown → closed`;
`negotiating → abort → closed`. **Why faithful:** BOLT 2 `:2152` explicitly
allows `shutdown` before `channel_ready`, and LDK exposes
`CounterpartyCoopClosedUnfundedChannel` / `LocallyCoopClosedUnfundedChannel`
(`events/mod.rs:608-615`). **Risk:** the current `negotiating` phase cannot
distinguish "before `funding_created`" from "after `funding_signed`"; a guard
on `fundingSignedSeen` is required to avoid making an illegal early `shutdown`
legal. That guard is conservative: BOLT 2 also allows a **funder** to send
`shutdown` after `funding_created` but before `funding_signed`, which the
role-free model cannot distinguish. Record that as a deliberate
under-approximation; a role field would recover the funder's legal early
shutdown.

### T6 — `LnLean.Proofs.Channel.LifecycleTargets.funding_timeout_reaches_closed`

**Priority:** P1/P2. **Classification:** external assumption (timer/height) +
model extension. **Fidelity risk:** medium. **Feasibility:** medium.

```lean
-- `TimeoutStep` is a separate relation driven by an explicit block height.
theorem funding_timeout_reaches_closed
    (c : Channel) (creation height : Nat)
    (hphase : c.phase = ChannelPhase.negotiating ∨
              c.phase = ChannelPhase.awaitingLockin)
    (hdeadline : creation + 2016 ≤ height) :
    ∃ c', TimeoutStep c c' ∧ c'.phase = ChannelPhase.closed
```

**Hypotheses:** `creation` is the channel-creation height; `height` is the
observed tip; the channel has no confirmed funding outpoint; the timeout is
2016 blocks. A role/funding premise must distinguish the fundee's "forget the
channel" rule from the funder's "counterparty failed to fund" timeout.
**Non-vacuity witness:** `height = creation + 2016`; negative:
`height = creation + 2015` does not fire. **Why faithful:** BOLT 2
`:1099-1101` and LDK `FUNDING_CONF_DEADLINE_BLOCKS`/`FundingTimedOut`
(`channel.rs:1467`, `:12721-12731`; `events/mod.rs:583`). **External
assumption:** the model must not claim the timer fires; it only proves the
conditional transition. `Liveness` already establishes the pattern of explicit
`HonestTimer`/`NoLoss` hypotheses (`:27-39`).

### T7 — `LnLean.Proofs.Protocol.LifecycleTargets.reestablish_preserves_phase`

**Priority:** P2. **Classification:** model extension (small joint receive
step); the closest target to proof-only. **Fidelity risk:** low.
**Feasibility:** high.

```lean
theorem reestablish_preserves_phase {c c' : Channel} (r : ChannelReestablish)
    (h : ReceiveStep c (.channelReestablish r) c')
    (hnz : r.nextCommitmentNumber ≠ 0) :
    c'.phase = c.phase
```

**Hypotheses:** `ReceiveStep` is a new small relation for inbound messages;
`closed` rejects all receives; the zero-counter case is handled by T8.
**Non-vacuity witness:** a nonzero `channel_reestablish` in `awaitingLockin`,
`normal`, and `shuttingDown` leaves the phase unchanged. **Why faithful:**
BOLT 2 `:3484-3495` retransmission is counter-level, not a lifecycle
transition; `ChannelReestablishProps` already proves the counter half.
**Non-vacuity preservation:** keep `reconnect_preserves_channelReady` and
`reconnect_resend_completes_lockin` unchanged; T7 should compose with them,
not replace them.

### T8 — `LnLean.Proofs.Protocol.LifecycleTargets.reestablish_zero_fails_channel`

**Priority:** P1/P2. **Classification:** model extension (failure transition
from the receive step). **Fidelity risk:** low. **Feasibility:** high, given
T7's `ReceiveStep`.

```lean
theorem reestablish_zero_fails_channel {c c' : Channel}
    (r : ChannelReestablish)
    (hz : r.nextCommitmentNumber = 0)
    (h : ReceiveStep c (.channelReestablish r) c') :
    c'.phase = ChannelPhase.closed
```

**Hypotheses:** the peer reports `next_commitment_number = 0`; the channel is
not already closed. **Non-vacuity witness:** a zero-counter reestablish closes
the channel; a nonzero reestablish does not (T7). **Why faithful:** BOLT 2
`:3484-3486` says a zero `next_commitment_number` MUST immediately fail the
channel and broadcast the latest commitment transaction.
`ChannelReestablishProps` currently models this only as
`ReestablishRejected`, not as a lifecycle transition (`:98-103`). The target
does not model the broadcast itself; that remains an external on-chain action.

## 5. Assumptions, counterexamples, and non-vacuity risks

### 5.1 Counterexamples that must remain visible

| Witness | Location | Why it matters |
|---|---|---|
| `trace_channelReady_without_fundingSigned` | `StateMachineProps.lean:364-370` | Shows the current two-event path to `normal`; it is the regression witness for T1. |
| `fundingSigned_not_mem_channelReady_trace` | `:372-374` | Makes the omission explicit, not accidental. |
| `channelReady_reachable_without_fundingSigned` | `:381-390` | The strongest existing refutation of a global `funding_signed`-before-`channel_ready` claim. |
| `not_eventually_normal_without_fundingLocked` | `Liveness.lean:431-...` | Shows fairness is necessary; do not add a `fundingLocked`-free liveness shortcut. |
| `inconsistent_snapshot_rolls_back` | `PersistenceRecovery.lean:618-...` | Keeps the persistence rollback behavior non-vacuous. |
| `reconnect_preserves_channelReady` | `Liveness.lean:573-582` | Keeps reconnect retention independent of any new phase bridge. |
| `reconnect_resend_completes_lockin` | `Liveness.lean:585-598` | Keeps the retransmission/legality split explicit. |

If T1 changes `Channel` or `Step`, the old positive counterexamples can no
longer be stated over the new relation. The correct move is to retain a
documented permissive/legacy relation and prove the old counterexample against
it; deleting the witness outright would hide a regression.

### 5.2 Assumptions that must stay explicit

1. **Chain depth and confirmation.** `fundingDepth`, `requiredDepth`, and the
   2016-block deadline are external chain facts. `AcceptChannel.minimumDepth`
   is already on the wire (`Messages.lean:143-158`) but absent from
   `Channel`; T3/T6 must supply it as an explicit parameter, not an axiom.
2. **Timer/height.** `Liveness` has no wall clock (`:83-89`). T6 must follow
   the existing `HonestTimer`/`NoLoss` style: prove the conditional transition,
   not that the timer fires.
3. **Transport/peer liveness.** `DisconnectedPeer` and `DiscardFunding`
   depend on the peer connection and the funding pipeline
   (`connection.rs:78-112`; `event.rs:2260`). These are external events, not
   channel protocol steps.
4. **Message-to-event mapping.** `Liveness` explicitly has no
   `Msg → ProtocolEvent` function (`:89-92`). T2/T7 must add a named mapping
   or a `ReceiveStep` relation; a proof cannot conjure it from `Msg`.
5. **API asynchrony.** `open_channel` returning a `user_channel_id` is not a
   lifecycle completion (`ldk-server/api/open_channel.rs:23-93`). Any theorem
   that treats the API return as "channel normal" is unsound relative to LDK.
6. **Opener/fundee asymmetry.** BOLT 2 lets the opener send `channel_ready`
   early but requires the accepter to wait for `minimum_depth`
   (`:1068-1093`). A universal depth premise would be over-strong.

### 5.3 Claims that must not be strengthened by assumption

* Do **not** prove `normal → HandshakeState.ready` by adding a hypothesis that
  is exactly that implication. T2's `LifecycleBridged` must be an invariant of
  a joint relation, not a restatement of the conclusion.
* Do **not** strengthen `channel_ready_gate` by adding `Channel.phase` to its
  statement without a joint state; the current theorem is definitional and
  says nothing about the channel machine.
* Do **not** make `phaseRank` non-monotone just to model usability regression.
  `is_usable` is a separate connection dimension; keep the phase machine
  monotone and model usability as an external predicate if needed.
* Do **not** delete `channelReady_reachable_without_fundingSigned` or
  `trace_channelReady_without_fundingSigned` to make T1 easier; retain them as
  legacy counterexamples.
* Do **not** add error/timeout/abort constructors to `ProtocolEvent` without
  updating `step?`, `step?_sound`, `step?_complete`, `no_step_from_closed`, and
  `step_phaseRank_le`; the ripple is the main feasibility cost.

## 6. Wave-13 recommendation

**Recommendation: defer implementation; treat the lifecycle bridge as an
explicit model-extension / external-data barrier, not a wave-13 proof lane.**

Reasons:

1. The two P0 issues are not proof gaps. `LN-PR-002` is only true inside
   `HandshakeState`; the channel machine lacks the fields and events needed to
   state it. `funding_signed` ordering has a concrete channel-level
   counterexample (`channelReady_reachable_without_fundingSigned`). Closing
   either requires changing `Channel`, `ProtocolEvent`, or adding a joint
   relation.
2. The P1 issues (depth, timeout, error, unfunded abort) require either new
   state fields/constructors or external chain/timer/transport facts. A
   wave-13 "proof-only" attempt would either be vacuous (hypothesis restates
   the conclusion) or would silently assume the missing behavior.
3. The existing layers are individually healthy: handshake ordering
   (`HandshakeState.Inv`), counter/retransmission laws
   (`ChannelReestablishProps`), error projection (`ErrorProps`), and
   conditional persistence (`ready_snapshot_reaches_normal`) are all proved.
   The gap is integration, not local theorem failure.

**If one target must be chosen first, choose T1
(`funding_signed_before_lockin`).** It is the narrowest change that removes a
concrete channel-level counterexample, it mirrors an invariant the handshake
machine already has, and it does not require a chain/timer/transport oracle.
T2 is the strategic follow-up that makes `LN-PR-002` a global lifecycle claim;
it is not a substitute for T1.

Suggested wave-14 sequence, if the parent authorizes model work:

* **Step 1 (design + approval):** approve the `Channel` field additions and the
  `ProtocolEvent` extension. No proofs merge before this.
* **Step 2 (T1):** add `fundingSignedSeen`, prove the channel-level ordering
  invariant, and retain the legacy counterexample. This is the narrowest
  high-value change.
* **Step 3 (T2):** add the joint `HandshakeState`/`Channel` relation and prove
  `LifecycleBridged` is preserved. Only then may `LN-PR-002` be cited as a
  global lifecycle claim.
* **Step 4 (T3–T6):** add depth, error, abort, and timeout as separate
  extensions with explicit external hypotheses. Do not bundle them into the
  T1/T2 patch.
* **Step 5 (T7/T8):** add the small `ReceiveStep` for `channel_reestablish`,
  prove phase preservation for nonzero counters and fail-on-zero, and compose
  with the existing reconnect theorems.

If the parent needs a wave-13 deliverable despite this, the only defensible
one is a **design note plus the T1 statement shape**, not a merged proof. The
lane should be recorded as an external/human barrier for chain depth, timers,
and transport disconnect events.

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

### 7.2 Lean commands and files inspected

```sh
rg -n "ProtocolEvent|inductive Step|phaseRank" LnLean/Channel/State.lean
rg -n "ChannelPhase|structure Channel" LnLean/Basic/Core.lean LnLean/Channel/Types.lean
rg -n "HandshakeState|def ready|canSendChannelReady|FundingPhase|fundingStep" LnLean/Protocol/Handshake.lean
rg -n "trace_channelReady_without_fundingSigned|channelReady_reachable_without_fundingSigned" LnLean/Proofs/Channel/StateMachineProps.lean
rg -n "channel_ready_gate" LnLean/Proofs/WaveD/D18.lean
rg -n "ready_snapshot_reaches_normal" LnLean/Proofs/PhaseC3/PersistenceRecovery.lean
rg -n "reconnect_preserves_channelReady|reconnect_resend_completes_lockin|not_eventually_normal_without_fundingLocked" LnLean/Proofs/Liveness.lean
rg -n "What is NOT modelled|ChannelView|open refinement" LnLean/Proofs/Protocol/ErrorProps.lean
rg -n "fail the channel|not modelled" LnLean/Proofs/Protocol/ChannelReestablishProps.lean
```

Files read in full or in relevant sections:

* `docs/AGENT-PROTOCOL.md`, `docs/OPEN-ISSUES.md`, `docs/THEOREM-INDEX.md`,
  `docs/TRACEABILITY.md`, `agents/TODO-REPAIR.md`,
  `agents/reports/swarm12/S12-POST-INTEGRATION-AUDIT.md`,
  `agents/reports/wave13-review/LDK-REFS.md`.
* `LnLean/Basic/Core.lean`, `LnLean/Channel/State.lean`,
  `LnLean/Channel/Types.lean`, `LnLean/Protocol/Handshake.lean`,
  `LnLean/Protocol/Messages.lean`, `LnLean/Protocol/Peer.lean`.
* `LnLean/Proofs/Channel/StateMachineProps.lean`,
  `LnLean/Proofs/Protocol/ErrorProps.lean`,
  `LnLean/Proofs/Protocol/ChannelReestablishProps.lean`,
  `LnLean/Proofs/WaveD/D18.lean`, `LnLean/Proofs/Liveness.lean`,
  `LnLean/Proofs/PhaseC3/PersistenceRecovery.lean`.

### 7.3 LDK commands and files inspected

```sh
rg -n "connect_peer_if_necessary|do_connect_peer|await_connection" \
  /tmp/opencode/ldk-refs/ldk-node/src/connection.rs
rg -n "pub fn connect|pub fn disconnect|fn open_channel_inner|pub fn open_channel|pub fn list_peers" \
  /tmp/opencode/ldk-refs/ldk-node/src/lib.rs
rg -n "confirmations_required|is_channel_ready|is_usable" \
  /tmp/opencode/ldk-refs/ldk-node/src/types.rs
rg -n "ChannelPending|ChannelReady|ChannelClosed|DiscardFunding" \
  /tmp/opencode/ldk-refs/ldk-node/src/event.rs
rg -n "FUNDING_CONF_DEADLINE_BLOCKS|check_get_channel_ready|FundingTimedOut" \
  refs/rust-lightning/lightning/src/ln/channel.rs
rg -n "FundingTimedOut|DisconnectedPeer|CoopClosedUnfundedChannel" \
  refs/rust-lightning/lightning/src/events/mod.rs
rg -n "channel_ready|shutdown|2016|minimum_depth" \
  refs/bolts/02-peer-protocol.md
```

LDK Server files inspected: `api/open_channel.rs`, `api/connect_peer.rs`,
`api/disconnect_peer.rs`, `api/list_peers.rs`, `api/error.rs`.

### 7.4 Constraints observed

* No branch switch, creation, rebase, commit, or push.
* No Lean, docs, script, test, vendor, or other lane report edits.
* The only file written by this lane is
  `agents/reports/wave13-review/R05-channel-lifecycle.md`.
* No cargo tests and no network access.
