# R25 — Splicing: quiescence, splice lifecycle, and funding replacement

**Status:** read-only review
**Pins:** LDK Node `fa123fed131e27ecc420b77fa7086fcf1ddaebb8`, LDK Server `c17dc11dde38f88c53457039ddf30c6b90a63ba2`
**Review branch:** `repair/integrated` at `f7f062817c185cd70004bb26c652deb99c6fd4bd` (no branch, commit, or non-report file changes made)
**Core rust-lightning anchor:** `refs/rust-lightning` at `fe4900930c6bd5786ec4203274d7cf312776a5a6`

## 1. Scope and current Lean surface

This lane covers BOLT 2 draft channel splicing: `stfu` quiescence,
`splice_init` / `splice_ack`, the splice-funding negotiation, the
post-`tx_signatures` operational-but-pending period, and final promotion by
exchanging matching `splice_locked` messages. It does **not** re-review the
interactive-transaction construction rules, PSBT/signature details, RBF
package relay, L1 script/fee mechanics, or persistence, except where those
constrain a lifecycle or accounting statement.

The review question is narrow: **can the current Lean channel model represent
LDK splicing faithfully, or is a model extension or an explicit external
barrier required?** The answer below is that end-to-end splicing is not
representable today, but a bounded additive lifecycle/accounting slice is
feasible without changing the existing channel relation.

### 1.1 Explicit scope exclusions already in the tree

Splicing is not merely unimplemented; it is deliberately excluded:

| Location | Statement |
|---|---|
| `docs/SCOPE.md:23` | “Splicing, dual funding, channel factories, eltoo, Taproot-native channels.” are out of scope. |
| `docs/CHARTER.md:38` | “Multi-party channel factories, splicing, or eltoo” are explicitly excluded. |
| `LnLean/Channel/Types.lean:41` | Multi-party channels, splicing, dual funding, zero-fee commitments are not modelled. |
| `LnLean/Channel/State.lean:51` | “Splicing, quiescence, dual funding, and `option_simple_close`.” are not modelled. |
| `LnLean/Proofs/PhaseC2/GlobalConservation.lean:42-44` | Splicing/channel resizing would change a channel’s funding value; the conservation step theorem therefore requires funding preservation. |

There is no `LN-*` catalog row for splicing in `docs/THEOREM-INDEX.md`,
`docs/TRACEABILITY.md`, or `docs/OPEN-ISSUES.md`; the only documentation hits
for “splice” are the scope exclusions above and generic TLV anchors. Thus a
wave-13 report cannot point at an existing claim to strengthen. Any splice
claim is new surface.

### 1.2 The current Lean channel surface

| Layer | Current shape | Consequence for splicing |
|---|---|---|
| `Channel` record | `funding : FundingOutpoint` and `fundingValue : Msat` are single fields that no `Step` changes (`LnLean/Channel/Types.lean:162-175`). | There is nowhere to keep the active pre-splice funding alongside a pending candidate. A splice cannot be represented as “old funding remains live while candidate confirms” without a new sidecar or a versioned record. |
| `ChannelPhase` | Exactly five constructors: `negotiating`, `awaitingLockin`, `normal`, `shuttingDown`, `closed` (`LnLean/Basic/Core.lean:235-240`). | Quiescence is temporary and enters/leaves `normal`; it cannot be a monotone phase in the current machine. There is no `awaitingSpliceLock` phase. |
| `ProtocolEvent` | Ten constructors, from `openChannel` through `closingSigned` (`LnLean/Channel/State.lean:67-80`). | No `stfu`, `spliceInit`, `spliceAck`, `spliceLocked`, `txAbort`, or splice-commitment event. |
| `Step` | Legal forward transitions only; every constructor uses `{ c with ... }` to change phase, counters, or feerate (`LnLean/Channel/State.lean:86-127`). | No constructor changes `funding` or `fundingValue`. A funding-changing splice event would be a new relation, not a new `Step` case. |
| Funding preservation | `step_fundingValue_eq` proves every `Step` preserves `fundingValue` by `cases h <;> rfl` (`LnLean/Proofs/Channel/StateTransitionTargets.lean:417-419`); the folded-layer copy is `ProtocolEventFoldTargets.lean:101-103`. | Adding a funding-changing constructor to `Step` would make this theorem false. It is a load-bearing invariant, not an incidental lemma. |
| Ledger conservation | `ledgerValue_step` uses `step_fundingValue_eq` (`StateTransitionTargets.lean:405-415`); `updateStep_preserves_ledger` composes it (`:421-436`). `GlobalConservation.ConservedTransition` requires `c'.fundingValueSat = c.fundingValueSat` (`LnLean/Proofs/PhaseC2/GlobalConservation.lean:226-228`). | The multi-channel conservation layer is correct only for funding-preserving transitions. Splice support must be additive, or the conservation layer must be explicitly versioned. |
| Wire vocabulary | `MsgKind`/`Msg` have no splice or `stfu` constructors (`LnLean/Protocol/Messages.lean:292-299`); `wireType` lists only the existing subset (types 1, 16–19, 32–39, 128–136) (`:340-359`); `kindOfType?` returns `none` for 77, 80, and 81 (`:365-385`). | Splice messages cannot be decoded or constructed. Type 77 (`splice_locked`), 80 (`splice_init`), 81 (`splice_ack`), and type 2 (`stfu`) are all unknown. |
| TLV layer | The only splice reference is an anchor comment: “extensions (splice messages)” (`LnLean/Wire/TLV.lean:23`; `LnLean/Proofs/Wire/TLVTargets.lean:49`). | The TLV parser is generic; it does not model the `splice_init_tlvs` or `splice_ack_tlvs` records. |

### 1.3 The model barrier

The current model is a **single-funding, monotone lifecycle** model. Splicing
requires four things it deliberately does not have:

1. **A sidecar lifecycle.** Quiescence and splice negotiation are orthogonal
   to `ChannelPhase`. They must be represented as a separate state/relation,
   or `phaseRank` monotonicity and `no_step_from_closed` must be reworked.
2. **Two funding identities at once.** While a splice is pending, the old
   funding outpoint/value remains active and observable, and a candidate
   funding outpoint/value exists but is not yet active. A single `funding`
   field cannot express this.
3. **Signed contributions.** Contributions may be positive or negative, and
   the resulting capacity/balance equations are arithmetic over signed
   amounts. A `Nat`-only balance update cannot represent splice-out without
   side conditions.
4. **A promotion gate.** LDK promotes the candidate only after it has both
   sent and received `splice_locked` for the same txid. The current `Step`
   relation has no notion of “sent lock”, “received lock”, or “candidate”.

This is a model-extension barrier, not a proof gap inside the existing
theorems. The bounded target in §4 keeps the existing `Channel`/`Step` fixed
and proves the splice lifecycle over a separate relation.

## 2. LDK datapoints (with `file:line`)

All LDK citations are read-only inspection of the pinned clones. LDK Node is
the public node API; LDK Server is the gRPC surface; rust-lightning core
anchors are from the repository’s `refs/rust-lightning` tree.

### 2.1 LDK Node API

* `ldk-node/src/lib.rs:1953` — `Node::splice_in(user_channel_id,
  counterparty_node_id, splice_amount_sats, min_fee_rate) -> Result<(), Error>`.
* `ldk-node/src/lib.rs:1990` — `Node::splice_in_with_all`, which uses all
  available confirmed on-chain funds.
* `ldk-node/src/lib.rs:2022` — `Node::splice_out`, which sends spliced-out
  funds to an on-chain address.
* `ldk-node/src/lib.rs:2116` — `Node::bump_channel_funding_fee`, which
  RBF-replaces a pending splice transaction.
* `ldk-node/src/lib.rs:1806-1934` — `splice_in_inner`; it resolves the
  channel, computes the maximum splice-in amount, checks on-chain funds
  (`:1874`), calls `splice_channel` (`:1878`), and rejects a second local
  contribution while one is pending (`:1884-1889`).
* `ldk-node/src/lib.rs:2037-2040` — `splice_out` rejects a splice amount
  greater than `outbound_capacity_msat`.
* `ldk-node/src/lib.rs:1938-1941` and `:2004-2007` — the API documentation
  states the key fidelity fact: once negotiation is complete, “the channel
  remains operational while waiting for a new funding transaction to
  confirm.”
* `ldk-node/src/lib.rs:2108-2110` — fee bumping replaces the in-flight
  splice transaction (RBF); it errors if no splice is pending.

### 2.2 LDK Node events and channel details

* `ldk-node/src/event.rs:306-319` — `SpliceNegotiated { channel_id,
  user_channel_id, counterparty_node_id, new_funding_txo }`; emitted when a
  splice with local inputs/outputs has been negotiated and the funding
  transaction is pending confirmation.
* `ldk-node/src/event.rs:320-329` — `SpliceNegotiationFailed`; emitted when
  the local side’s splice negotiation round fails.
* `ldk-node/src/event.rs:276-293` — `ChannelReady` is emitted for a newly
  established channel and for a spliced channel with the new funding output;
  `funding_txo` is the current funding output and may change after a splice.
* `ldk-node/src/event.rs:258-269` — `ChannelPending` is for a new channel,
  not for a splice. A splice does not create a second logical channel.
* `ldk-node/src/types.rs:448-450` — `ChannelDetails` docs: “When a channel is
  spliced, most fields continue to refer to the original pre-splice channel
  state until the splice transaction reaches sufficient confirmations to be
  locked (and we exchange `splice_locked` messages with our peer).”
* `ldk-node/src/types.rs:467-470` — `funding_txo` stays pre-splice until both
  `splice_locked` messages are exchanged.
* `ldk-node/src/types.rs:476-478`, `:489-493`, `:504-507`, `:523-526` — the
  redeem script, `short_channel_id`, SCID aliases, and `channel_value_sats`
  follow the same pre-splice-until-locked rule.
* `ldk-node/src/types.rs:566-568` — `is_channel_ready` is true only after
  both parties exchanged `channel_ready` and the channel is not shutting down.
* `ldk-node/src/types.rs:592-593` — `next_splice_out_maximum_sat` exposes the
  maximum next splice-out from the local balance; it is a live splice-specific
  capacity field, not a replacement for `channel_value_sats`.

### 2.3 LDK Server API

* `ldk-server/ldk-server/src/api/splice_channel.rs:27-43` —
  `handle_splice_in_request` maps either an exact `splice_amount_sats` or
  `AllFunds` to `splice_in` / `splice_in_with_all` and returns an empty
  `SpliceInResponse` immediately.
* `ldk-server/ldk-server/src/api/splice_channel.rs:45-72` —
  `handle_splice_out_request` resolves an address (or allocates a wallet
  address), calls `splice_out`, and returns the destination address.
* `ldk-server/ldk-server/src/api/splice_channel.rs:76-82` —
  `handle_bump_channel_funding_fee_request` initiates an asynchronous RBF fee
  bump and returns immediately.
* `ldk-server/ldk-server-grpc/src/proto/api.proto:618-637` — `SpliceInRequest`
  / `SpliceInResponse`; `:641-659` — `SpliceOutRequest` / `SpliceOutResponse`;
  `:665-677` — `BumpChannelFundingFeeRequest` / response.
* `ldk-server/ldk-server-grpc/src/proto/api.proto:1293-1299` — the RPC
  methods `SpliceIn`, `SpliceOut`, and `BumpChannelFundingFee`. These are
  asynchronous commands, not completion notifications.
* `ldk-server/ldk-server-grpc/src/proto/events.proto:14-15`, `:129-144` —
  `SpliceNegotiated` and `SpliceNegotiationFailed` event envelopes.
* `ldk-server/ldk-server-grpc/src/proto/types.proto:150` — the server’s
  `Channel` type describes an interactively negotiated funding transaction
  (a splice, or eventually V2 channel establishment).

### 2.4 rust-lightning core splice behavior

**Messages and wire types**

* `refs/rust-lightning/lightning/src/ln/msgs.rs:462-476` — `SpliceInit`
  fields: `channel_id`, signed `funding_contribution_satoshis`, feerate,
  locktime, funding pubkey, optional `require_confirmed_inputs`.
* `msgs.rs:482-492` — `SpliceAck` fields: `channel_id`, signed contribution,
  funding pubkey, optional `require_confirmed_inputs`.
* `msgs.rs:498-503` — `SpliceLocked` fields: `channel_id`, `splice_txid`.
* `msgs.rs:3034-3055` — the three message writeable/encoding shapes.
* `lightning/src/ln/wire.rs:557-568` — `SpliceInit` type 80, `SpliceAck` type
  81, `SpliceLocked` type 77. The source comment notes the draft history
  (previously 74/75).

**Quiescence gates**

* `lightning/src/ln/channel.rs:8373-8376` — reject `update_add_htlc` while
  quiescent (“Got add HTLC message while quiescent”).
* `channel.rs:8643-8649` — reject `update_fulfill_htlc` while quiescent.
* `channel.rs:9016-9021` — reject `commitment_signed` while quiescent.
* `channel.rs:9420-9425` — reject `revoke_and_ack` while quiescent.
* `channel.rs:10407-10410` — reject `update_fee` while quiescent.
* `channel.rs:788-792` and `:982` — `is_quiescent` is a channel-state flag
  attached to `ChannelReady`, not a separate lifecycle phase.

**Splice validation**

* `channel.rs:13756-13798` — `validate_splice_init` rejects a non-live
  channel, a non-quiescent channel (`:13766-13768`), a second pending splice
  (`:13770-13775`), a zero contribution from the initiator (`:13777-13782`),
  and a missing current commitment point (`:13784-13788`).
* `channel.rs:14320-14348` — `validate_splice_ack` requires a pending splice
  and validates the acceptor’s contribution through
  `validate_splice_contributions`.
* `channel.rs:2819-2849` — contribution validation computes post-splice
  `value_to_self_msat`, counterparty value, and `post_channel_value_sat`
  using signed contributions.
* `channel.rs:2915-2938` — the post-splice funding scope carries the updated
  `value_to_self_msat` and per-side commitment balances.

**Promotion and lock handling**

* `channel.rs:12259-12290` — `maybe_promote_splice_funding` requires a sent
  txid and a received txid; it logs a warning and returns `None` on a
  mismatch, and waits if the received txid is absent.
* `channel.rs:12348-12352` — promotion swaps `self.funding` with the promoted
  candidate funding.
* `channel.rs:14481-14525` — `splice_locked` rejects an unknown txid with
  `ChannelError::close`, records `received_funding_txid`, and only proceeds
  when a sent txid exists.
* `channelmanager.rs:4740-4755` — `SpliceNegotiated` is emitted from the
  shutdown/failure path with the negotiated funding outpoint;
  `channelmanager.rs:3576-3582` — `ChannelReady` carries the current funding
  outpoint after promotion.

### 2.5 BOLT 2 draft anchors

* `refs/bolts/02-peer-protocol.md:1498-1548` — `stfu` quiescence handshake;
  `:1518` forbids update messages after `stfu`, and `:1521-1525` defines
  quiescence as bilateral.
* `refs/bolts/02-peer-protocol.md:1560-1636` — the splice lifecycle diagram:
  `splice_init`/`splice_ack`, `tx_add_input`/`tx_add_output`/`tx_complete`,
  `commit_sig`, `tx_signatures`, `<RESUME CHANNEL>`, optional RBF, and final
  `splice_locked` exchange.
* `:1668-1675` — sender preconditions: quiescent, quiescence initiator,
  after both `channel_ready`, no other splice being negotiated, no other
  negotiated splice whose `splice_locked` has not been sent and received,
  and no prior `shutdown`.
* `:1663-1680` — `funding_contribution_satoshis` is positive for splice-in
  and negative for splice-out, matching the sender’s balance change.
* `:1793-1800` — the new channel funding output amount is the previous
  channel capacity with both `splice_init` and `splice_ack` contributions
  applied.
* `:1810-1813` — each side’s new channel balance is its previous balance plus
  its own contribution.
* `:1843-1847` — the splice commitment transaction uses the same feerate and
  the same `commitment_number` as the existing commitment transaction.
* `:1977-2035` — after signing, operations return to normal while waiting for
  confirmation; the node tracks multiple commitment transactions, and the
  splice completes when both sides exchange `splice_locked` with a matching
  txid.

## 3. Gap matrix

Status vocabulary: **missing** means absent from the current Lean vocabulary;
**partially covered** means a related theorem exists but does not cover the
splice behavior; **unmodelled-external** means the behavior depends on an
external system (chain, signatures, transport, persistence) that the model
should not pretend to prove.

| Behavior | Lean status | LDK / BOLT evidence | Gap / counterexample | Priority |
|---|---|---|---|---|
| Public splice API (`splice_in`, `splice_in_with_all`, `splice_out`, fee bump) | missing | `ldk-node/src/lib.rs:1953`, `:1990`, `:2022`, `:2116`; server `splice_channel.rs:27`, `:45`, `:76` | No Lean API boundary or command/event split. The server returns immediately while the splice is still asynchronous. | P2 |
| Quiescence (`stfu`) gate | missing | BOLT `:1498-1548`; `channel.rs:8373`, `8643`, `9016`, `9420`, `10407`; `channel.rs:788-792`, `:982` | `ProtocolEvent` has no `stfu`; `Channel` has no quiescent flag; `ChannelPhase` cannot represent temporary quiescence without breaking monotonicity. | **P0** |
| Splice wire messages and type IDs | missing | `msgs.rs:462`, `:482`, `:498`; `wire.rs:557-568` | `MsgKind`/`Msg` have no splice constructors; `wireType` has no 77/80/81; `kindOfType?` maps them to `none` (`Messages.lean:340-385`). | **P0** |
| `splice_init` preconditions (quiescent, after `channel_ready`, no prior shutdown) | missing | BOLT `:1668-1675`; `channel.rs:13756-13788` | No event constructor and no precondition. The existing `Step` has no splice state to guard. | **P0** |
| One negotiated splice at a time / pending candidate | missing | BOLT `:1671-1673`; `channel.rs:13770-13775`; `ldk-node/src/lib.rs:1884-1889` | `Channel` has no `pendingSplice` or candidate set. A second splice cannot be rejected because the first cannot be recorded. | **P0** |
| Signed splice contributions and bounds | missing | BOLT `:1663-1680`; `channel.rs:2819-2849`; `ldk-node/src/lib.rs:2037-2040` | `Channel.balance` updates are `Nat`-based and no splice contribution type exists. Splice-out requires signed arithmetic and reserve/min-value checks. | P1 |
| Interactive transaction construction (`tx_add_input`, `tx_add_output`, `tx_complete`, `tx_abort`) | unmodelled-external | BOLT `:1647-1765`, `:583-621`; `msgs.rs:509`, `:530`, `:569`, `:624` | The model should abstract this as “negotiated”/“aborted”, not re-prove transaction construction or PSBT validity. | P2 (external) |
| RBF / multiple negotiated candidates / package relay | unmodelled-external | BOLT `:1636`, `:1977-2000`; `ldk-node/src/lib.rs:2108-2116`; `channel.rs:12259-12352` | A bounded single-candidate model is a deliberate under-approximation. RBF safety and candidate ancestry require a separate model. | P2 (external) |
| Active funding replacement and candidate funding | missing | `Channel.funding`/`fundingValue` (`Types.lean:162-175`); BOLT `:1793-1800`; `channel.rs:12348-12352` | One funding field cannot hold both the active pre-splice funding and the pending candidate. Adding a splice event to `Step` would falsify `step_fundingValue_eq` (`StateTransitionTargets.lean:417-419`). | **P0** |
| Pre-lock observability (old funding/SCID/value stay visible) | missing | `ldk-node/src/types.rs:448-450`, `:467-470`, `:523-526`; BOLT `:1565-1569` | The model has no “pending but not active” funding state. A model that swaps `funding` immediately on `splice_ack` is unfaithful to LDK. | **P0** |
| Matching-lock promotion | missing | BOLT `:2014-2035`; `channel.rs:12259-12290`, `:14481-14525` | No sent/received lock fields, no candidate txid, and no promotion step. LDK promotes only when both locks match; mismatch warns and does not promote; unknown txid closes. | **P0** |
| Capacity accounting after splice | partially covered | BOLT `:1793-1800`; `channel.rs:2842-2849` | Existing conservation is only for funding-preserving transitions (`GlobalConservation.lean:226-228`). No theorem states `newCapacity = oldCapacity + both contributions`. | P1 |
| Balance accounting after splice | partially covered | BOLT `:1810-1813`; `channel.rs:2827-2840`, `:2915-2938` | Existing balance lemmas cover HTLC add/fail/fulfill, not signed splice contributions. No theorem states each side’s balance increases by its own contribution. | P1 |
| Same commitment number for the splice commitment | missing | BOLT `:1843-1847` | Reusing `Step.commitmentSigned` would increment counters (`State.lean:104-110`), contradicting the draft. A splice-specific signing event must preserve the counters. | P1 |
| Multiple commitment transactions during pending confirmation | unmodelled-external | BOLT `:1977-2000` | `Channel` carries one `funding` and one commitment record. The model cannot represent “payments must be valid for all splice transactions.” | P2 (external) |
| Splice confirmation depth / `splice_locked` trigger | unmodelled-external | BOLT `:2020-2035`; `channel.rs:14481-14525` | Chain depth is external. The model can prove the conditional transition “given a depth oracle, lock is sendable”, not that the chain confirms. | P2 (external) |
| Abort / negotiation failure | missing | `event.rs:320-329`; `channel.rs:13770-13788`, `:14320-14348`; BOLT `:1766` | No `tx_abort` or `SpliceNegotiationFailed` event. The model cannot state “abort preserves funding and returns to idle.” | P1 |
| Restart / reestablish / persistence of a pending splice | unmodelled-external | `ldk-node/src/lib.rs:368-381`; BOLT `:1565-1569` | Persistence is outside `Channel.Step`; a bounded lifecycle model should assume an externally recovered pending-splice state, not prove recovery. | P2 (external) |
| API/event boundary (`SpliceNegotiated` / `SpliceNegotiationFailed`) | unmodelled-external | `event.rs:306-329`; `events.proto:129-144` | Lean has no event queue or async API boundary. As in R05, API return must not be treated as splice completion. | P2 (external) |

## 4. Proposed targets

The targets below are **statement shapes for wave-14 scoping**, not compiling
Lean. They deliberately live in a new module, for example
`LnLean.Proofs.Channel.SpliceLifecycleTargets`, and assume a sidecar state
rather than editing `Channel`, `ChannelPhase`, `ProtocolEvent`, or `Step`.

### 4.0 Model sketch

```lean
-- Sidecar state; the underlying Channel remains in ChannelPhase.normal.
inductive SplicePhase
  | idle
  | negotiating        -- splice_init/ack exchanged, funding not built
  | negotiated         -- interactive tx complete, not signed
  | signed             -- commit_sig / tx_signatures exchanged
  | awaitingLock       -- operational again, waiting for confirmations
  | locked             -- both splice_locked exchanged, funding promoted

structure FundingCandidate where
  txid : Bytes32
  funding : FundingOutpoint
  value : Nat

structure SpliceState where
  phase : SplicePhase
  quiescent : Bool
  activeFunding : FundingOutpoint
  activeValue : Nat
  candidate : Option FundingCandidate
  ours theirs : Int                     -- signed satoshis
  sentLockTxid receivedLockTxid : Option Bytes32
  localBalance remoteBalance : Nat
  localCommitmentNumber remoteCommitmentNumber : Nat  -- mirrors of Channel counters
```

`SpliceStep : SpliceState → SpliceEvent → SpliceState → Prop` contains
`stfuSent`, `stfuReceived`, `spliceInit`, `spliceAck`, `txComplete`,
`spliceCommitSigned`, `txSignatures`, `sendSpliceLocked`,
`recvSpliceLocked`, `promote`, `abort`, and `closeUnknownLock`. The
underlying `Channel` is unchanged throughout; only `promote` is allowed to
change `activeFunding`/`activeValue`.

### T1 — `LnLean.Proofs.Channel.SpliceLifecycleTargets.splice_wire_vocabulary`

**Priority:** P2. **Classification:** model extension (wire vocabulary).
**Fidelity risk:** low. **Feasibility:** high, but not on the critical path
for the sidecar.

```lean
-- Extend MsgKind/Msg with stfu (2), spliceLocked (77), spliceInit (80),
-- spliceAck (81); make wireType and kindOfType? round-trip.
theorem splice_wire_types :
    wireType .stfu = 2 ∧
    wireType .spliceLocked = 77 ∧
    wireType .spliceInit = 80 ∧
    wireType .spliceAck = 81

theorem splice_kindOfType_roundtrip (k : MsgKind)
    (h : k = .stfu ∨ k = .spliceLocked ∨ k = .spliceInit ∨ k = .spliceAck) :
    kindOfType? (wireType k) = some k
```

**Hypotheses:** the message constructors carry the BOLT draft fields; `Msg`
still has no custom-message escape hatch. **Non-vacuity witness:** concrete
round trips for 2, 77, 80, and 81. **Why faithful:** the type IDs are the
`Encode::TYPE` constants in `wire.rs:557-568` and the BOLT draft labels
(`:1649`, `:1716`, `:2007`). **Caveat:** this target only adds vocabulary; it
does not prove that any splice event is legal. Keep it separate from T2–T7.

### T2 — `LnLean.Proofs.Channel.SpliceLifecycleTargets.splice_init_requires_quiescence`

**Priority:** P0. **Classification:** model extension (sidecar state).
**Fidelity risk:** low. **Feasibility:** high.

```lean
theorem splice_init_requires_quiescence {s s' : SpliceState} {init : SpliceInit}
    (h : SpliceStep s (.spliceInit init) s') :
    s.quiescent = true ∧ s.phase = .idle
```

**Hypotheses:** `spliceInit` is the only event that enters `.negotiating`;
quiescence is set only by the bilateral `stfu` exchange, not by a local flag
toggle. **Non-vacuity witness:**
`s0 --stfuSent--> s1 --stfuReceived--> s2 --spliceInit--> s3`, with
`s2.quiescent = true` and `s2.phase = .idle`. **Negative witness:** a
`spliceInit` from a non-quiescent state has no derivation. **Why faithful:**
BOLT `:1668-1670` and LDK `validate_splice_init`
(`channel.rs:13756-13768`) both require quiescence; BOLT `:1518` forbids
update messages after `stfu`. **Design constraint:** quiescence must not be a
`ChannelPhase`; it is temporary and would break `phaseRank` monotonicity
(`State.lean:157-171`).

### T3 — `LnLean.Proofs.Channel.SpliceLifecycleTargets.no_second_splice_when_pending`

**Priority:** P0. **Classification:** model extension (sidecar state).
**Fidelity risk:** low. **Feasibility:** high.

```lean
theorem no_second_splice_when_pending {s s' : SpliceState} {init : SpliceInit}
    (hp : s.phase ≠ .idle) :
    ¬ SpliceStep s (.spliceInit init) s'
```

**Hypotheses:** `.negotiating`, `.negotiated`, `.signed`, and `.awaitingLock`
all count as pending; only `.idle` accepts a new `splice_init`. **Non-vacuity
witness:** after one `splice_init`, a second `splice_init` is rejected while
the first is in `.negotiating`. **Why faithful:** BOLT `:1671-1673` says
“MUST NOT send `splice_init` while another splice is being negotiated” and
“MUST NOT send ... if another splice has been negotiated but `splice_locked`
has not been sent and received”; LDK rejects `pending_splice.is_some()`
(`channel.rs:13770-13775`) and LDK Node rejects a prior local contribution
(`lib.rs:1884-1889`, `:2058-2063`).

### T4 — `LnLean.Proofs.Channel.SpliceLifecycleTargets.funding_preserved_until_promotion`

**Priority:** P0. **Classification:** model extension (sidecar state).
**Fidelity risk:** low. **Feasibility:** high. **This is the top target.**

```lean
theorem funding_preserved_until_promotion {s s' : SpliceState} {e : SpliceEvent}
    (h : SpliceStep s e s') (he : e ≠ .promote) :
    s'.activeFunding = s.activeFunding ∧ s'.activeValue = s.activeValue
```

**Hypotheses:** every step except `promote` leaves the active funding and
value untouched; `abort` and `closeUnknownLock` are included, so they cannot
silently change funding. **Non-vacuity witnesses:** (a) the happy path
through `.awaitingLock` still has the old active funding; (b) an `abort` from
`.negotiated` returns to `.idle` with the same active funding. **Negative
witness:** only `promote` may change the active funding. **Why faithful:**
LDK Node documents that `funding_txo`, `channel_value_sats`, and the SCID
fields stay pre-splice until both `splice_locked` messages are exchanged
(`types.rs:448-450`, `:467-470`, `:523-526`); BOLT says the old funding
remains until the splice completes (`:1565-1569`, `:1977-2035`). This target
also protects the existing conservation layer: because the sidecar never
changes `Channel.fundingValue`, `step_fundingValue_eq` and
`GlobalConservation.ConservedTransition` remain true without modification.

### T5 — `LnLean.Proofs.Channel.SpliceLifecycleTargets.promotion_requires_matching_locks`

**Priority:** P0. **Classification:** model extension (sidecar state).
**Fidelity risk:** low. **Feasibility:** medium.

```lean
theorem promotion_requires_matching_locks {s s' : SpliceState}
    (h : SpliceStep s .promote s') :
    ∃ cand txid,
      s.candidate = some cand ∧
      s.sentLockTxid = some txid ∧
      s.receivedLockTxid = some txid ∧
      cand.txid = txid

theorem promotion_uses_candidate_funding {s s' : SpliceState}
    (h : SpliceStep s .promote s') :
    ∃ cand, s.candidate = some cand ∧
      s'.activeFunding = cand.funding ∧
      s'.activeValue = cand.value
```

**Hypotheses:** `sendSpliceLocked` and `recvSpliceLocked` only record a txid
that matches a negotiated candidate; `recvSpliceLocked` with an unknown txid
is a `closeUnknownLock`, not a promotion; a received txid that differs from
the sent txid leaves the state pending and does not promote. **Non-vacuity
witness:** negotiate candidate `txid`, exchange both `splice_locked(txid)`,
then `promote`; the result has the candidate outpoint/value. **Negative
witness:** `sentLockTxid = some a`, `receivedLockTxid = some b` with `a ≠ b`
has no `promote` derivation. **Why faithful:** LDK requires both a sent and a
received txid and returns `None` on mismatch (`channel.rs:12259-12290`); it
closes on an unknown txid (`:14481-14499`); BOLT says the splice completes
when both sides send `splice_locked` for the same transaction (`:2014-2035`).

### T6 — `LnLean.Proofs.Channel.SpliceLifecycleTargets.promote_capacity`

**Priority:** P1. **Classification:** model extension + arithmetic.
**Fidelity risk:** medium (signed contributions / minimum value).
**Feasibility:** medium.

```lean
theorem promote_capacity {s s' : SpliceState}
    (h : SpliceStep s .promote s')
    (hmin : MIN_CHANNEL_VALUE_SATOSHIS ≤ s'.activeValue) :
    (s'.activeValue : Int) =
      (s.activeValue : Int) + s.ours + s.theirs
```

**Hypotheses:** `activeValue` is the previous channel capacity in satoshis;
`ours` and `theirs` are the signed `splice_init`/`splice_ack`
contributions; no other output changes the channel funding output. The
minimum-value/reserve checks are explicit hypotheses from
`validate_splice_contributions` (`channel.rs:2842-2870`), not axioms.
**Non-vacuity witness:** previous capacity `1_000_000`, `ours = +100_000`,
`theirs = -50_000`, new capacity `1_050_000`. **Negative witness:** a
negative new capacity has no derivation. **Why faithful:** BOLT `:1793-1800`
and LDK `:2842-2849` define the post-splice channel value exactly as the
previous value plus both signed contributions.

### T7 — `LnLean.Proofs.Channel.SpliceLifecycleTargets.promote_balance_components`

**Priority:** P1. **Classification:** model extension + arithmetic.
**Fidelity risk:** medium (reserve and pending-HTLC side conditions).
**Feasibility:** medium.

```lean
theorem promote_balance_components {s s' : SpliceState}
    (h : SpliceStep s .promote s') :
    (s'.localBalance : Int) = (s.localBalance : Int) + s.ours ∧
    (s'.remoteBalance : Int) = (s.remoteBalance : Int) + s.theirs

theorem promote_balance_total {s s' : SpliceState}
    (h : SpliceStep s .promote s')
    (hsum : s.localBalance + s.remoteBalance = s.activeValue) :
    s'.localBalance + s'.remoteBalance = s'.activeValue
```

**Hypotheses:** the abstract balance excludes pending HTLCs and commitment
fees; contributions are bounded so neither balance falls below its reserve and
the channel keeps at least one output. **Non-vacuity witness:** previous
balances `600_000 / 400_000`, contributions `+100_000 / -50_000`, new
balances `700_000 / 350_000`, new value `1_050_000`. **Why faithful:** BOLT
`:1810-1813` says each side’s new balance is its previous balance plus its own
contribution; LDK computes the same componentwise values
(`channel.rs:2827-2840`, `:2915-2938`). **Caveat:** if pending HTLCs or
commitment fees are included, the simple sum theorem needs an explicit
adjustment term; do not state it unconditionally.

### T8 — `LnLean.Proofs.Channel.SpliceLifecycleTargets.splice_signing_keeps_commitment_number`

**Priority:** P1. **Classification:** model extension (splice-specific
signing event). **Fidelity risk:** low. **Feasibility:** high.

```lean
theorem splice_signing_keeps_commitment_number {s s' : SpliceState}
    (h : SpliceStep s .spliceCommitSigned s') :
    s'.localCommitmentNumber = s.localCommitmentNumber ∧
    s'.remoteCommitmentNumber = s.remoteCommitmentNumber
```

**Hypotheses:** `spliceCommitSigned` is a distinct event from the normal
`ProtocolEvent.commitmentSigned`; the splice commitment uses the existing
commitment number. **Non-vacuity witness:** counters `5/5` before and after
the splice signing exchange. **Negative witness:** `Step.commitmentSigned`
increments `remoteCommitmentNumber` (`State.lean:104-110`), so it cannot be
reused for the splice commitment. **Why faithful:** BOLT `:1843-1847`
requires the same feerate and same `commitment_number` as the existing
commitment transaction.

## 5. Assumptions, counterexamples, and non-vacuity risks

### 5.1 Assumptions that must stay explicit

1. **Chain confirmation and depth.** The model may prove “if a candidate has
   acceptable depth, `splice_locked` is sendable”, but it must not prove that
   the chain confirms. `splice_locked` is triggered by acceptable depth per
   BOLT `:2020-2035`; LDK’s `splice_locked` path (`channel.rs:14481-14525`)
   is the conditional transition, not a chain oracle.
2. **Interactive transaction construction.** `tx_add_input`,
   `tx_add_output`, `tx_complete`, and `tx_abort` are abstracted. The model
   does not prove PSBT validity, fee adequacy, input ownership, or package
   relay. Those are external to the lifecycle/accounting slice.
3. **Signatures.** `commit_sig` and `tx_signatures` are abstracted to a
   “signed” state. The model does not prove ECDSA validity or signature
   attribution; those belong to the signature lanes.
4. **RBF and multiple candidates.** LDK can replace a pending splice and can
   have multiple negotiated candidates. The bounded model has one candidate.
   Do not claim RBF safety, candidate ancestry, or package-relay liveness.
5. **Persistence and reconnect.** A restart may recover or drop pending
   splice state (`ldk-node/src/lib.rs:368-381`). The sidecar model assumes an
   externally supplied recovered state; it does not prove persistence or
   reestablishment.
6. **API asynchrony.** `splice_in`/`splice_out` return after the command is
   accepted (`splice_channel.rs:27-43`, `:45-72`). `SpliceNegotiated` and
   `ChannelReady` arrive later (`event.rs:306-329`, `:276-293`). A theorem
   that treats the API return as “splice complete” is unsound relative to
   LDK.
7. **Reserve/minimum-value parameters.** The reserve and minimum channel
   value are explicit hypotheses supplied by the caller; the model should not
   bake in a particular implementation constant.

### 5.2 Barriers and counterexamples that must remain visible

| Witness / barrier | Location | Why it matters |
|---|---|---|
| `step_fundingValue_eq` | `StateTransitionTargets.lean:417-419`; `ProtocolEventFoldTargets.lean:101-103` | Any splice constructor added to `Step` that changes `fundingValue` falsifies this theorem. The sidecar design exists to avoid that. |
| `ConservedTransition` requires equal funding | `GlobalConservation.lean:226-228` | The multi-channel conservation theorem would also fail for a funding-changing `Step`. Do not weaken it to accommodate a splice event. |
| `ledgerValue_step` / `updateStep_preserves_ledger` | `StateTransitionTargets.lean:405-415`, `:421-436` | These compose funding preservation into the ledger account. A splice extension must either keep `Step` fixed or introduce a versioned ledger relation. |
| Single `Channel.funding` field | `Types.lean:162-175` | The model cannot express “old funding active, candidate pending” in one record. A sidecar or versioned record is required. |
| `phaseRank` monotonicity and `no_step_from_closed` | `State.lean:157-171`, `:179-183` | Quiescence is temporary; making it a phase would break monotonicity. Keep quiescence in the sidecar. |
| Stale `ChannelDetails` before lock | `ldk-node/src/types.rs:448-450`, `:467-470` | This is intentional LDK behavior, not a bug. A model that immediately exposes the new funding is unfaithful. |
| Channel remains operational after `tx_signatures` | `ldk-node/src/lib.rs:1938-1941`; BOLT `:1565-1569`, `:1977-2000` | A model that stops HTLCs until `splice_locked` is too strong. The sidecar must allow the underlying `Channel` to remain `normal`. |
| Mismatched `splice_locked` does not promote | `channel.rs:12259-12290` | LDK logs a warning and returns `None`; it does not promote a mismatched candidate. The model must not make mismatch equivalent to success. |
| Unknown `splice_locked` closes | `channel.rs:14481-14499` | BOLT says warning/error; LDK closes. This is a failure transition, not a no-op. |
| Prior local contribution rejected | `ldk-node/src/lib.rs:1884-1889` | A second local splice contribution is rejected while one is pending; the model needs an explicit pending state to state this. |

### 5.3 Non-vacuity and non-weakening rules

* Every target above must come with a concrete trace and numeric witness, not
  just a “there exists a state” argument. The happy path must include the
  pre-lock period and the matching-lock promotion.
* The negative witnesses for T2, T3, T4, T5, and T6 are part of the model’s
  value: they show that illegal transitions have no derivation.
* Do **not** prove `promotion_requires_matching_locks` by adding a hypothesis
  that already says the locks match. The conclusion must follow from the
  `SpliceStep` constructors.
* Do **not** prove `promote_capacity` with `ours + theirs = 0` or with both
  contributions zero; that would be vacuous. Use at least one positive and
  one negative contribution, plus a pure splice-in witness.
* Do **not** delete or weaken `step_fundingValue_eq`,
  `ledgerValue_step`, `updateStep_preserves_ledger`, or
  `GlobalConservation.ConservedTransition`. If a future full model needs
  funding-changing `Step`, introduce a separately named relation and
  re-prove the conservation layer against it.
* Do **not** update `docs/SCOPE.md` or `docs/CHARTER.md` as part of this
  review. Any scope change is a parent/maintainer decision.

## 6. Wave-13 recommendation

**Verdict: implement a bounded additive lifecycle/accounting slice; defer
main-model integration; treat the rest as an explicit external barrier.**

This is not an end-to-end splicing claim. The recommended wave-14 slice is:

1. **Add a new sidecar module** (`LnLean.Proofs.Channel.SpliceLifecycleTargets`)
   with `SplicePhase`, `SpliceState`, `SpliceEvent`, and `SpliceStep`. Do not
   edit `Channel`, `ChannelPhase`, `ProtocolEvent`, or `Step`.
2. **Prove T2, T3, and T4 first.** These are the narrowest, highest-value
   results: quiescence gates `splice_init`, a pending splice blocks a second
   one, and the active funding is preserved until promotion. T4 is the top
   target because it makes the splice layer compatible with the existing
   conservation theorems instead of invalidating them.
3. **Then prove T5.** Matching sent/received `splice_locked` is the central
   LDK fidelity condition; without it the model would promote too early or
   on the wrong candidate.
4. **Then prove T6/T7/T8.** Capacity and balance accounting plus the
   same-commitment-number rule. Keep the arithmetic signed and make reserve
   and minimum-value checks explicit hypotheses.
5. **Add T1 only if the wire vocabulary is needed by the implementation.**
   The sidecar can be useful without changing `Msg`; T1 is a separate wiring
   task, not a prerequisite for the lifecycle proofs.

**Defer:** integrating splice into `Channel`/`ProtocolEvent`/`Step`, changing
`GlobalConservation`, and adding a general “channel V2” record. Those require
a maintainer-approved design because they would either falsify existing
theorems or force a versioned conservation layer.

**External barrier:** interactive-transaction construction, PSBT/signature
validity, RBF/package relay, L1 confirmation/depth, persistence/reconnect,
and API event delivery. A bounded model should state these as explicit
hypotheses or side conditions, not axioms, and should not claim end-to-end
splicing liveness or safety.

**If the parent needs a single wave-13/14 deliverable:** ship the sidecar
module with T2–T5 and a non-vacuity trace. Record the remaining splice
surface as deferred/external in the wave-14 plan. Do not claim the current
Lean model “supports splicing.”

## 7. Evidence and commands

### 7.1 Pins verified

```sh
git -C /tmp/opencode/ldk-refs/ldk-node rev-parse HEAD
# fa123fed131e27ecc420b77fa7086fcf1ddaebb8
git -C /tmp/opencode/ldk-refs/ldk-server rev-parse HEAD
# c17dc11dde38f88c53457039ddf30c6b90a63ba2
git -C refs/rust-lightning rev-parse HEAD
# fe4900930c6bd5786ec4203274d7cf312776a5a6
git rev-parse --short HEAD
# f7f0628
```

The LDK Node `Cargo.toml:89-100` declares rust-lightning rev
`d7a980641c6325ddda5072a0f470ef8392676cf5`. The core citations above use the
workspace `refs/rust-lightning` checkout at `fe49009`; the splice APIs and
behavior were spot-checked at `d7a9806` (`channel.rs` promotion starts at
`:12277`, `msgs.rs` `SpliceInit` at `:453`, `wire.rs` `SpliceInit` at
`:557`). Line numbers can differ by a few lines between the two revisions;
the cited paths and symbol names are stable.

### 7.2 Lean commands and files inspected

```sh
rg -n -i "splic" docs/SCOPE.md docs/CHARTER.md LnLean
rg -n "inductive ProtocolEvent|inductive Step|Splicing, quiescence|def phaseRank|no_step_from_closed" \
  LnLean/Channel/State.lean
rg -n "structure Channel where|funding :|fundingValue :|Splicing" LnLean/Channel/Types.lean
rg -n "inductive ChannelPhase" LnLean/Basic/Core.lean
rg -n "step_fundingValue_eq|ledgerValue_step|updateStep_preserves_ledger" \
  LnLean/Proofs/Channel/StateTransitionTargets.lean \
  LnLean/Proofs/Channel/ProtocolEventFoldTargets.lean
rg -n "Splicing and channel resizing|ConservedTransition|fundingValueSat" \
  LnLean/Proofs/PhaseC2/GlobalConservation.lean
rg -n "inductive MsgKind|def wireType|def kindOfType" LnLean/Protocol/Messages.lean
rg -n "splice" LnLean/Wire/TLV.lean LnLean/Proofs/Wire/TLVTargets.lean
```

Files read in full or in relevant sections:

* `docs/AGENT-PROTOCOL.md`, `docs/OPEN-ISSUES.md`, `docs/THEOREM-INDEX.md`,
  `docs/TRACEABILITY.md`, `docs/SCOPE.md`, `docs/CHARTER.md`,
  `agents/TODO-REPAIR.md`, `agents/reports/swarm12/S12-POST-INTEGRATION-AUDIT.md`,
  `agents/reports/wave13-review/LDK-REFS.md`.
* `LnLean/Basic/Core.lean`, `LnLean/Channel/State.lean`,
  `LnLean/Channel/Types.lean`, `LnLean/Protocol/Messages.lean`,
  `LnLean/Wire/TLV.lean`.
* `LnLean/Proofs/Channel/StateTransitionTargets.lean`,
  `LnLean/Proofs/Channel/ProtocolEventFoldTargets.lean`,
  `LnLean/Proofs/PhaseC2/GlobalConservation.lean`,
  `LnLean/Proofs/Wire/TLVTargets.lean`.

### 7.3 LDK commands and files inspected

```sh
rg -n "splice_in|splice_in_with_all|splice_out|bump_channel_funding_fee|splice_in_inner" \
  /tmp/opencode/ldk-refs/ldk-node/src/lib.rs
rg -n "SpliceNegotiated|SpliceNegotiationFailed|ChannelReady|ChannelPending" \
  /tmp/opencode/ldk-refs/ldk-node/src/event.rs
rg -n "When a channel is spliced|funding_txo|channel_value_sats|next_splice_out_maximum_sat|is_channel_ready" \
  /tmp/opencode/ldk-refs/ldk-node/src/types.rs
rg -n "handle_splice_in_request|handle_splice_out_request|handle_bump_channel_funding_fee_request" \
  /tmp/opencode/ldk-refs/ldk-server/ldk-server/src/api/splice_channel.rs
rg -n -i "splice" \
  /tmp/opencode/ldk-refs/ldk-server/ldk-server-grpc/src/proto/api.proto \
  /tmp/opencode/ldk-refs/ldk-server/ldk-server-grpc/src/proto/events.proto \
  /tmp/opencode/ldk-refs/ldk-server/ldk-server-grpc/src/proto/types.proto
rg -n "SpliceInit|SpliceAck|SpliceLocked" \
  refs/rust-lightning/lightning/src/ln/msgs.rs
rg -n "SpliceInit|SpliceAck|SpliceLocked" \
  refs/rust-lightning/lightning/src/ln/wire.rs
rg -n "is_quiescent|validate_splice_init|validate_splice_ack|maybe_promote_splice_funding|splice_locked" \
  refs/rust-lightning/lightning/src/ln/channel.rs
rg -n "splice|quiescen|stfu|splice_locked" refs/bolts/02-peer-protocol.md
```

LDK Server files inspected: `api/splice_channel.rs`, `api/error.rs`,
`ldk-server-grpc/src/proto/api.proto`, `events.proto`, `types.proto`.
LDK Node files inspected: `src/lib.rs`, `src/event.rs`, `src/types.rs`.
Core files inspected: `lightning/src/ln/msgs.rs`,
`lightning/src/ln/wire.rs`, `lightning/src/ln/channel.rs`,
`lightning/src/ln/channelmanager.rs`.

### 7.4 Constraints observed

* No branch switch, creation, rebase, commit, or push.
* No Lean, docs, script, test, vendor, or other lane report edits.
* The only file written by this lane is
  `agents/reports/wave13-review/R25-splicing.md`.
* No cargo tests and no network access.
