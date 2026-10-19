# R18 — LDK Node events, background processing, and message dispatch
**Status:** read-only review
**Pins:** LDK Node `fa123fed131e27ecc420b77fa7086fcf1ddaebb8`, LDK Server `c17dc11dde38f88c53457039ddf30c6b90a63ba2`

Review tip: `f7f062817c185cd70004bb26c652deb99c6fd4bd` (`repair/integrated`).
No Lean, catalog, test, vendor, or other-lane file was modified. No `lake build`,
no `cargo test`, no network access. Read-only commands are listed in §7.

---

## 1. Scope and current Lean surface

### 1.1 Catalog coverage

`docs/THEOREM-INDEX.md` contains **51** `LN-*` rows (counted with
`grep -cE` over `docs/THEOREM-INDEX.md`).
No row names an event loop, event queue, background processor, message
dispatcher, event acknowledgement, event persistence, retry scheduler, or
runtime. The nearest rows are about *message* semantics, not *event/runtime*
semantics:

| Row | Target | What it actually states | Why it is not event-loop coverage |
|---|---|---|---|
| `LN-PR-002` | `LnLean.Protocol.Handshake.channel_ready_gate` (catalog name; proved in `LnLean.Proofs.WaveD.D18:334`) | Both `channel_ready` messages are required before normal operation | Handshake gate, not scheduling or delivery |
| `LN-PR-005` | `LnLean.Protocol.Peer.reestablish_no_rollback` (`Peer.lean:384`) | `resend` returns the retained copy; `advanceReceived` never lowers either BOLT 2 counter | Retransmission buffer only; no event queue, no ack, no duplicate delivery |
| `LN-CH-004` | `LnLean.Security.advance_monotone` | A committed update never decreases the commitment number | Monotonicity of a counter, not receipt idempotency |
| `LN-SEC-005/006` | `LnLean.Proofs.Liveness.penalty_economical`, `watchtower_bridge` (`Liveness.lean:763,717`) | Penalty economics and watchtower bridge | Security liveness, not the event scheduler |
| `LN-CR-006` | `LnLean.Wire.Message.decode_length` | A frame's declared length matches the consumed payload | Framing, not dispatch |

`LnLean/Proofs/PhaseC3/PersistenceRecovery.lean` is root-imported
(`LnLean.lean:134`) but is **not** a catalog row. Its own header limits it to
channel commitment counters, the live HTLC set, and `channel_ready`
(`PersistenceRecovery.lean:8-27`); it explicitly has no timers, retransmission
scheduling, fsync, or message-to-event bridge.

### 1.2 Lean carriers that exist

1. **Channel event/fold layer** — `LnLean/Channel/State.lean`
   - `ProtocolEvent` has ten constructors (`State.lean:67-78`).
   - `Step c e c'` is the unguarded transition relation (`State.lean:86-135`).
   - `Reachable` is its reflexive-transitive closure (`State.lean:133`).
   - `UpdateEvent` / `UpdateStep` are the additive HTLC update layer
     (`State.lean:398,414`).
   - `DanceEvent` / `GuardedStep` add the commitment-dance guard
     (`State.lean:487,591`).
2. **Peer/message layer** — `LnLean/Protocol/Peer.lean`
   - `ChannelRecord` stores `channelId`, `reestablish`, and the last retained
     retransmittable message of each kind (`Peer.lean:91-99`).
   - `advanceReceived` advances the reestablish counters on
     `commitment_signed` / `revoke_and_ack` (`Peer.lean:127-131`).
   - `send` / `receive` / `resend` (`Peer.lean:194,213,232`).
   - `LossyLink` explicitly models drop, duplicate, and reorder
     (`Peer.lean:237-248`).
   - The module states that it has **no timer, retry counter, or automatic
     retransmission** (`Peer.lean:66-67`).
3. **Reestablish/idempotency layer** — `LnLean/Proofs/Protocol/ChannelReestablishProps.lean`
   - The existing wave-A `advanceReceived` is **not idempotent**:
     `duplicate_commitmentSigned_advances_twice` (`:382-391`).
   - A numbered refinement exists and is proved idempotent, but is not used by
     `PeerState.receive`: `advanceReceivedNumbered` (`:395-399`) and
     `advanceReceivedNumbered_idempotent` (`:403-409`).
   - `receive_counters_monotone` (`:420`) lifts the *monotone* part to
     `PeerState`, but not idempotency.
4. **Scheduler scaffold** — `LnLean/Proofs/Liveness.lean`
   - `runList`, `runPrefix`, `NoLoss`, `Fair` (`:260-311`).
   - `fair_awaitingLockin_eventually_normal` (`:387-403`) is an honest
     schedule/fairness theorem about `ProtocolEvent`, but it does not model an
     event queue, event payloads, or acknowledgement.
5. **Persistence/replay scaffold** — `LnLean/Proofs/PhaseC3/PersistenceRecovery.lean`
   - `Persisted` / `Snapshot` (`:118-205`).
   - `applyMsg` / `replay` (`:305-318`).
   - `replay_append`, `replay_no_rollback`, `restore_replay_suffix`
     (`:329,381,395`).
   - `applyMsg` advances `commitmentSigned` unconditionally
     (`:306-307`), so `replay` is **not** a duplicate-free event handler.
6. **Dispatch/scoping fragments**
   - `ErrorProps.applyToChannel` / `handleInbound` (`:213-274`) model
     channel-id scoping and show that an unknown-channel error is ignored at
     the *state* layer. They do not model the LDK reply.
   - `Protocol/Laws.pong_reply_bounded` (`:112-115`) proves a pong payload
     fits the framing bound. It does not connect a received `ping` to an
     emitted `pong`.

### 1.3 What is absent (searched, not assumed)

`grep -rniE 'event.?queue|next_event|event_handled|background.?processor|processBatch|handle_event|receipt|subscriber|broadcast|runtime' LnLean --include='*.lean'`
finds no event-queue/runtime declarations. The matches are unrelated:
payment retry prose (`Payment/HTLC.lean:49`), payment settlement idempotence
(`Payment/Laws.lean:225`), gossip update idempotence
(`Routing/Gossip.lean:1752`), and node-announcement replay rejection
(`Proofs/Routing/NodeIdentityChainTargets.lean:717`).

In particular, there is no Lean declaration named `EventQueue`, `EventId`,
`Receipt`, `next_event`, `event_handled`, `EventBatch`, `ProcessBatch`,
`BackgroundProcessor`, or `PendingConnections`. There is no bridge from an
event queue to `Step`/`Reachable`, and no model of:

- FIFO queue order, front-until-ack, or positional ack;
- the `add_event` / `event_handled` persist-before/after ordering;
- batch stopping at `ReplayEvent`;
- ldk-server subscriber fan-out, lag, or client acknowledgement;
- ping/pong reply generation or unknown-channel error replies;
- single-flight concurrent `connect`.

The only replay that exists is `PersistenceRecovery.replay`, a channel-message
fold over `Persisted`, not an event queue.

---

## 2. LDK datapoints (with `file:line`)

### 2.1 LDK Node event queue: FIFO, front-until-ack, positional ack

- The queue is `Arc<Mutex<VecDeque<Event>>>` (`ldk-node/src/event.rs:421`).
- `add_event` does `push_back(event)` **before** persisting the encoded queue
  (`event.rs:437-444`).
- `next_event` returns `front().cloned()` (`event.rs:452-455`); the async
  future polls the same front and returns it again while the queue is
  non-empty (`event.rs:548-560`).
- `event_handled` does `pop_front()` **before** persisting
  (`event.rs:461-468`). It is a positional pop, not a keyed acknowledgement:
  it does not check which event the caller handled.
- The public API states the same-event-until-ack contract
  (`ldk-node/src/lib.rs:1005` and `:1017`: “this will always return the same
  event until handling is confirmed via `Node::event_handled`”).
- `event_handled` persists the queue and returns `Err` on persistence failure
  (`event.rs:461-474`, `476-493`); `lib.rs:1031-1039` maps that to a node
  error. A second `event_handled` after one `next_event` therefore pops the
  *next queued* event (if another one exists), not the same one.

**Concrete implications.** The queue is FIFO and does not deduplicate.
`add_event` pushes the same event twice if called twice. `event_handled`
cannot distinguish “the caller handled the front event” from “the caller
called ack again”; the API relies on caller discipline.

### 2.2 Persistence crash windows

- `add_event` pushes to memory, then `persist_queue`; on write failure it logs
  and returns `Err` (`event.rs:476-493`). The in-memory queue has already
  changed.
- `event_handled` pops from memory, then persists; on write failure the
  on-disk queue is the old queue (`event.rs:461-474`).
- The LDK Node event handler maps a queue-push failure to `ReplayEvent`
  (`event.rs:1978-1981`), which asks the ChannelManager to replay the event on
  the next invocation.

So two distinct windows exist:

1. **Add window:** a failed persist leaves the event in memory; a replay adds
   it again → duplicate pending event.
2. **Ack window:** a failed persist after pop leaves the event on disk; a
   restart reloads it → duplicate delivery after restart.

Neither is an exactly-once guarantee. The code order is the evidence; there is
no transaction around memory and KVStore.

### 2.3 Background processor

- LDK Node spawns the background processor with `process_events_async`
  (`ldk-node/src/lib.rs:777-800`; the handle lives in
  `runtime.rs:157-166`).
- The background loop calls `process_pending_events_async` for the
  ChannelManager, ChainMonitor, and OnionMessenger
  (`lightning-background-processor/src/lib.rs:1037-1041`).
- `process_events_body` clones the pending event list, handles events **in
  order**, stops on the first `Err`, and drains only
  `num_handled_events` (`lightning/src/ln/channelmanager.rs:3702-3726`). The
  comment is explicit: on error, unhandled events are replayed on the next
  invocation (`:3714-3718`).
- The LDK Node handler returns `Result<(), ReplayEvent>` (`event.rs:804`) and
  uses `ReplayEvent` for queue-push failures (`event.rs:1978-1981`).

This is an **at-least-once, prefix-ordered** batch contract: a failed event
and every event after it are retained; no event after a failure is handled in
that invocation.

### 2.4 ldk-server delivery is explicitly best-effort

- Event fan-out is a bounded `tokio::sync::broadcast` channel of capacity 1024
  (`ldk-server/src/main.rs:320`).
- With zero subscribers, `send_payment_event` marks the event handled and
  returns without sending it (`main.rs:847-852`).
- After a successful send attempt it still calls `event_handled`
  (`main.rs:860-873`); a send failure only logs “skipping event”.
- A lagging subscriber gets `RecvError::Lagged` and the service simply
  `continue`s, skipping the missed events (`service.rs:472-474`).
- The API guide states the contract: not persisted, no replay after
  reconnect, no client acknowledgement, bounded 1024, slow/disconnected
  clients miss events (`docs/api-guide.md:329-339`).

Therefore “event delivered to a client” is **not** a property of the LDK
Server API, and cannot be a Lean theorem without an external delivery/ack
assumption.

### 2.5 Message dispatch

- **Ping/pong:** a received `Ping` with `ponglen < 65532` enqueues a `Pong`
  with `byteslen = ponglen` (`peer_handler.rs:2430-2435`). A `Pong` resets the
  liveness counters (`:2437-2440`). This is a transport reply, not a channel
  state transition.
- **Unknown channel:** the generic `no_such_channel_for_peer` path builds a
  `send_err_msg_no_close` (`channelmanager.rs:1220-1226`). A
  `channel_reestablish` for an unknown channel is special-cased with a
  defensive bogus reestablish response (`:14107-14127`).
- **Custom messages:** `NodeCustomMessageHandler` reads a `RawLSPSMessage` and
  forwards it to the liquidity manager (`ldk-node/src/message_handler.rs:37-58`).
- **Concurrent connects:** `register_or_subscribe_pending_connection` inserts a
  vacant `node_id` as the owner and returns `None`; an occupied entry returns
  a `oneshot::Receiver` and does not dial again (`connection.rs:277-293`).
  The result is propagated to all subscribers (`:295-305`); the guard removes
  the entry when abandoned (`:45-46`, `:107-111`).

### 2.6 What LDK does *not* do

- It does not attach an id or key to queued events; `EventQueue` stores bare
  `Event` values (`event.rs:421`).
- It does not deduplicate `add_event` calls.
- It does not acknowledge a specific event; `event_handled` is a positional
  pop.
- It does not retry a failed event after a crash without replaying the
  persisted queue; the persistence layer is the only durable record.
- ldk-server does not persist events for subscribers, replay, or wait for a
  client ack (`api-guide.md:330-333`).

---

## 3. Gap matrix

| Behavior | Lean status | LDK evidence | Gap / counterexample | Priority |
|---|---|---|---|---|
| FIFO queue, front-until-ack | **Missing** | `event.rs:421,437-455`; `lib.rs:1005,1017` | No `EventQueue`; no theorem that `next` is stable across enqueues and changes only on ack | P1 |
| Positional ack / double-ack | **Missing** | `event.rs:461-468` | `event_handled` pops the front without checking identity; a second ack drops the next event. No Lean counterexample or keyed refinement | P1 |
| Add-before-persist / ack-before-persist | **Missing** | `event.rs:437-468`; `event.rs:1978-1981` | No crash-window model; no theorem that persistence failure duplicates or replays an event | P1 |
| Batch stop-on-`ReplayEvent` | **Missing** | `channelmanager.rs:3702-3726`; `lib.rs:777-800` | `Liveness.runPrefix` schedules `ProtocolEvent`s, not event batches; no “handled prefix / retained suffix” theorem | P0 |
| Duplicate `commitment_signed` receipt | **Contradicted** at the `PeerState` counter layer; **partial** at the guarded layer | BOLT 2 dedups by the implicit commitment number; `Msg.commitmentSigned` carries none | `duplicate_commitmentSigned_advances_twice` (`ChannelReestablishProps.lean:386-391`) proves two receipts advance twice. The refinement `advanceReceivedNumbered` is idempotent (`:395-409`) but unused. `guarded_no_double_commitmentSigned` (`ProtocolEventFoldTargets.lean:765`) excludes the double-sign only in the guarded relation | P0 |
| Duplicate `revoke_and_ack` / duplicate update messages | **Unmodelled** | `advanceReceived` only guards `revoke_and_ack` by counter order (`Peer.lean:127-131`) | No general receipt key or per-message duplicate rule; no event-level dedup | P1 |
| Event application idempotency (`add_event` side) | **Missing** | `event.rs:804`, `:1187`, `:1527`, etc. | No model of `handle_event`’s store/event-queue effects; no theorem that a replayed event is absorbed | P1 |
| `PersistenceRecovery.replay` duplicate-free | **Contradicted if read as event replay** | `channelmanager.rs:3702-3726` is at-least-once | `applyMsg` increments on every `commitmentSigned` (`PersistenceRecovery.lean:305-307`); `restore_replay_suffix` (`:395`) says replay of `pre ++ post`, not de-duplicated handling | P1 |
| Ping → pong reply | **Missing** | `peer_handler.rs:2430-2435` | `PeerState.receive` returns `some s` for a connection-level `ping` (`Peer.lean:222-224`) and emits no message. `pong_reply_bounded` (`Protocol/Laws.lean:112-115`) is framing only | P1 |
| Unknown-channel dispatch | **Partial / contradicted** | `channelmanager.rs:1220-1226` sends an error; `:14107-14127` special-cases reestablish | `receive_channel_requires_channel` (`Peer.lean:283-286`) returns `none`, dropping the message; `ErrorProps.handleInbound_error_unknown_ignored` (`:263-274`) only says the state is unchanged | P2 |
| Concurrent `connect` single-flight | **Missing** | `connection.rs:277-293,295-305` | No `PendingConnections` model; no at-most-one-owner theorem | P2 |
| ldk-server subscriber delivery / replay / ack | **External** | `main.rs:320,847-873`; `service.rs:472-474`; `api-guide.md:329-339` | No Lean claim, and the public contract is explicitly best-effort; cannot be proved without delivery/ack assumptions | External |
| Runtime scheduling / tokio fairness | **External** | `runtime.rs:34-110,157-166`; `lib.rs:777-800` | `Liveness.Fair` is a schedule parameter (`Liveness.lean:306-311`), not a tokio scheduler theorem; no concurrency model | External |

**Reading the table.** “Missing” means no declaration exists. “Partial” means a
similarly named theorem exists but proves only a projection (state unchanged,
framing bound, counter monotone). “Contradicted” means the current model’s
behavior differs from LDK; it is not automatically a bug in Lean—it is a
fidelity boundary that must be stated, not hidden.

---

## 4. Proposed targets

The following are additive. None replaces or weakens an existing theorem.
Suggested files:

- `LnLean/Protocol/EventRuntime.lean` — queue, batch, crash-window, dispatch
  models (no proofs).
- `LnLean/Proofs/Protocol/EventRuntimeTargets.lean` — proofs, importing
  `EventRuntime` and `ChannelReestablishProps`.
- `LnLean/Proofs/Protocol/ChannelReestablishProps.lean` — add the keyed
  `receiveNumbered` refinement next to the existing `advanceReceivedNumbered`.
- `LnLean/Protocol/ConnectionRuntime.lean` and
  `LnLean/Proofs/Protocol/ConnectionRuntimeTargets.lean` — T7 only; this is a
  node-runtime model, not a channel/protocol theorem.

A new catalog row (proposed `LN-PR-007`, “Event receipt, queue acknowledgement,
and batch replay”) would be appropriate only after the targets are proved; do
not add it in this read-only lane.

**Carrier note.** `Event` in the code blocks below is a new opaque carrier
standing for LDK Node’s `lightning::events::Event`; the Lean tree has no such
type today (`grep -rnE 'structure Event|inductive Event|abbrev Event' LnLean --include='*.lean'` finds only
unrelated game-theory structures). The implementation lane must add a minimal
`Event` carrier or parameterize T1/T3/T4 over an arbitrary type; it must not
pretend an LDK event type already exists.

---

### T1 — Event queue FIFO and positional-ack counterexample (P1)

**Proposed fully-qualified names**

- `LnLean.Protocol.EventRuntime.EventQueue`
- `LnLean.Protocol.EventRuntime.enqueue`
- `LnLean.Protocol.EventRuntime.front?`
- `LnLean.Protocol.EventRuntime.ack`
- `LnLean.Proofs.Protocol.EventRuntimeTargets.front?_enqueue_of_nonempty`
- `LnLean.Proofs.Protocol.EventRuntimeTargets.front?_enqueue_of_empty`
- `LnLean.Proofs.Protocol.EventRuntimeTargets.ack_enqueue`
- `LnLean.Proofs.Protocol.EventRuntimeTargets.ack_empty`
- `LnLean.Proofs.Protocol.EventRuntimeTargets.double_ack_drops_next`

**Statement shape**

```lean
structure EventQueue where
  pending : List Event

def enqueue (q : EventQueue) (e : Event) : EventQueue :=
  { q with pending := q.pending ++ [e] }

def front? (q : EventQueue) : Option Event :=
  q.pending.head?

def ack (q : EventQueue) : Option EventQueue :=
  match q.pending with
  | [] => none
  | _ :: rest => some { q with pending := rest }

theorem front?_enqueue_of_nonempty (q : EventQueue) (e : Event)
    (h : q.pending ≠ []) : front? (enqueue q e) = front? q

theorem front?_enqueue_of_empty (q : EventQueue) (e : Event)
    (h : q.pending = []) : front? (enqueue q e) = some e

theorem ack_enqueue (q : EventQueue) (e : Event)
    (h : q.pending = []) : ack (enqueue q e) = some q

theorem ack_empty (q : EventQueue) (h : q.pending = []) : ack q = none

/-- A second positional ack removes the *next* event, not the one the caller
just handled.  This is the counterexample that prevents an unconditional
“ack is idempotent” theorem. -/
theorem double_ack_drops_next (e₁ e₂ : Event) (rest : List Event) :
    ∃ q', ack { pending := e₁ :: e₂ :: rest } = some q' ∧
      ack q' = some { pending := rest }
```

**Hypotheses.** None beyond the queue shape. `ack` is deliberately the
positional LDK operation, not a keyed one.

**Non-vacuity witness.** `q := { pending := [] }`, `e := .ping ⟨0, ByteArray.empty⟩`;
`front?_enqueue_of_empty` gives `some e`, `ack_enqueue` gives `some q`. For the
counterexample, `q := { pending := [e₁, e₂] }`; two acks leave `pending = []`.

**Why it is faithful.** It is a literal `VecDeque`/`front`/`pop_front` model
(`event.rs:421-474`) and the documented front-until-ack contract
(`lib.rs:1005`). It also makes the missing key explicit: if the parent wants
“ack the event I handled”, that is a *new* keyed operation, not a theorem
about LDK’s `event_handled`.

**Fidelity risk / feasibility.** Low / very high: list lemmas only.
**Classification:** model extension. **Priority:** P1.

---

### T2 — Keyed, idempotent `commitment_signed` receipt (P0)

**Proposed fully-qualified names**

- `LnLean.Proofs.Protocol.ChannelReestablishProps.receiveNumbered`
- `...receiveNumbered_idempotent`
- `...receiveNumbered_advances_once`
- `...receiveNumbered_stale_noop`
- `...receiveNumbered_other_channel`

**Statement shape**

```lean
/-- A `receive` variant for a `commitment_signed` whose BOLT 2 commitment
number is supplied by the dispatcher/reestablish layer.  Other messages
delegate to the existing `receive`. -/
def receiveNumbered (s : PeerState) (cid : ChannelId) (m : Msg) (k : Nat) :
    Option PeerState :=
  match s.transport with
  | .down => none
  | .up =>
      match m with
      | .commitmentSigned _ =>
          match findChannel s cid with
          | some c =>
              some (updateChannel s cid (fun _ => c.advanceReceivedNumbered k))
          | none => none
      | _ => receive s m

/-- Re-delivering the same numbered `commitment_signed` is absorbed. -/
theorem receiveNumbered_idempotent
    {s s' : PeerState} {cid : ChannelId} {cs : CommitmentSigned} {k : Nat}
    (h : receiveNumbered s cid (.commitmentSigned cs) k = some s') :
    receiveNumbered s' cid (.commitmentSigned cs) k = some s'

/-- The first delivery still advances exactly one commitment number. -/
theorem receiveNumbered_advances_once
    {s s' : PeerState} {cid : ChannelId} {cs : CommitmentSigned} {k : Nat}
    {c : ChannelRecord}
    (h : receiveNumbered s cid (.commitmentSigned cs) k = some s')
    (hc : findChannel s cid = some c)
    (hk : k = c.reestablish.nextCommitmentNumber) :
    ∃ c', findChannel s' cid = some c' ∧
      c'.reestablish.nextCommitmentNumber =
        c.reestablish.nextCommitmentNumber + 1

/-- A stale (already consumed) number is a no-op. -/
theorem receiveNumbered_stale_noop
    {s s' : PeerState} {cid : ChannelId} {cs : CommitmentSigned} {k : Nat}
    {c : ChannelRecord}
    (h : receiveNumbered s cid (.commitmentSigned cs) k = some s')
    (hc : findChannel s cid = some c)
    (hk : k ≠ c.reestablish.nextCommitmentNumber) :
    findChannel s' cid = some c

/-- Other channels are untouched. -/
theorem receiveNumbered_other_channel
    {s s' : PeerState} {cid cid' : ChannelId} {cs : CommitmentSigned} {k : Nat}
    (h : receiveNumbered s cid (.commitmentSigned cs) k = some s')
    (hne : cid' ≠ cid) :
    findChannel s' cid' = findChannel s cid'
```

**Hypotheses.** The key `k` is **not** carried by `Msg.commitmentSigned`; it
must come from the dispatcher/reestablish state. That is the central external
assumption (A1). The theorem is stated over a known channel and an up
transport. `receiveNumbered` delegates every non-`commitment_signed` message
to `receive`, so it cannot silently change unrelated behavior.

**Non-vacuity witness.** Take `c` from `ChannelReestablishProps.sampleChannel`
(`:508`) and set `k = c.reestablish.nextCommitmentNumber`. The first
application advances (`receiveNumbered_advances_once`); the second is absorbed
(`receiveNumbered_idempotent`). `k = next + 1` gives the stale no-op.

**Why it is faithful.** LDK rejects a replayed `commitment_signed` by the
channel's expected commitment number; BOLT 2 dedups by the implicit commitment
number. The existing `advanceReceivedNumbered_idempotent`
(`ChannelReestablishProps.lean:403-409`) already proves the record-level
refinement; T2 lifts it to `PeerState` without changing `advanceReceived`.
The existing negative theorem `duplicate_commitmentSigned_advances_twice`
(`:386-391`) is retained as the statement about the unrefined model.

**Fidelity risk.** Medium: the key source is external, and the live LDK
channel also rejects duplicates by its in-flight commitment state, not only by
a number. The theorem should be read as “if the dispatcher supplies the
expected number, receipt is idempotent”, not “all duplicate C-S are rejected
by `PeerState` alone”. `PeerState.receive` itself stays unchanged; integrating
`receiveNumbered` into the default dispatcher would require the key source and
would alter existing `receive` theorems, so that integration is explicitly
out of scope for this additive target.

**Feasibility.** High: reuse `advanceReceivedNumbered_idempotent` plus the
existing `findChannel_updateChannel_of_channelId` lemma
(`ChannelReestablishProps.lean:255`). **Classification:** model extension with
an explicit external key-source hypothesis. **Priority:** P0.

---

### T3 — Background batch: prefix order and stop-on-replay (P0/P1)

**Proposed fully-qualified names**

- `LnLean.Protocol.EventRuntime.HandleOutcome`
- `LnLean.Protocol.EventRuntime.processBatch`
- `LnLean.Proofs.Protocol.EventRuntimeTargets.processBatch_replay`
- `...processBatch_handled`
- `...processBatch_stops`
- `...processBatch_at_least_once`

**Statement shape**

```lean
inductive HandleOutcome where
  | handled
  | replay
deriving DecidableEq, Repr

/-- Returns the retained suffix and the number of events handled from the
front.  This mirrors `num_handled_events` and `drain(..num_handled_events)`. -/
def processBatch (h : Event → HandleOutcome) : List Event → List Event × Nat
  | [] => ([], 0)
  | e :: es =>
      match h e with
      | .handled =>
          let (rest, n) := processBatch h es
          (rest, n + 1)
      | .replay => (e :: es, 0)

theorem processBatch_replay (h : Event → HandleOutcome) (e : Event)
    (es : List Event) (he : h e = .replay) :
    processBatch h (e :: es) = (e :: es, 0)

theorem processBatch_handled (h : Event → HandleOutcome) (e : Event)
    (es : List Event) (he : h e = .handled) :
    processBatch h (e :: es) =
      let (rest, n) := processBatch h es
      (rest, n + 1)

/-- Once the first event is replayed, no later event is handled in this
invocation. -/
theorem processBatch_stops (h : Event → HandleOutcome) (e : Event)
    (es : List Event) (he : h e = .replay) :
    (processBatch h (e :: es)).2 = 0

/-- At-least-once: every input event is either retained or classified as
handled.  This is the positive content of LDK’s replay contract. -/
theorem processBatch_at_least_once (h : Event → HandleOutcome)
    (es : List Event) (e : Event) (hmem : e ∈ es) :
    e ∈ (processBatch h es).1 ∨ h e = .handled
```

**Hypotheses.** `h` is a pure classification for one invocation. Real
`handle_event` has side effects and may fail transiently; the theorem is about
the batch control flow, not about the handler’s internal atomicity (A5).

**Non-vacuity witness.** `h := fun _ => .handled`, `es = [e₁, e₂]` gives
`([], 2)`. `h := fun _ => .replay` gives `([e₁, e₂], 0)`. A mixed handler
`h e₁ = .handled`, `h e₂ = .replay` gives `([e₂], 1)` and
`processBatch_stops` for `e₂`.

**Why it is faithful.** This is exactly the `process_events_body` loop:
ordered clone, stop on `Err`, drain the handled prefix, retry the rest
(`channelmanager.rs:3702-3726`). It also matches LDK Node’s
`ReplayEvent`-on-push-failure behavior (`event.rs:1978-1981`).

**Fidelity risk.** Low: the control flow is small and explicit. The model does
not claim the handler is idempotent; it claims the batch never skips an event
after a failure. **Feasibility.** Very high. **Classification:** model
extension. **Priority:** P0/P1.

---

### T4 — Persistence crash-window counterexamples and atomic ack (P1)

**Proposed fully-qualified names**

- `LnLean.Protocol.EventRuntime.DurableQueue`
- `LnLean.Protocol.EventRuntime.addEvent`
- `LnLean.Protocol.EventRuntime.ackEvent`
- `LnLean.Proofs.Protocol.EventRuntimeTargets.addEvent_failure_mem_ahead`
- `...addEvent_retry_after_failure_duplicates`
- `...ackEvent_failure_disk_still_front`
- `...atomicAck_removes_front`

**Statement shape**

```lean
structure DurableQueue where
  mem  : List Event
  disk : List Event

def enqueue (q : DurableQueue) (e : Event) : DurableQueue :=
  { q with mem := q.mem ++ [e] }

def persist (q : DurableQueue) : DurableQueue :=
  { q with disk := q.mem }

def ackMem (q : DurableQueue) : DurableQueue :=
  match q.mem with
  | [] => q
  | _ :: rest => { q with mem := rest }

/-- `ok = false` abstracts a failed KVStore write. -/
def addEvent (q : DurableQueue) (e : Event) (ok : Bool) : DurableQueue :=
  if ok then persist (enqueue q e) else enqueue q e

def ackEvent (q : DurableQueue) (ok : Bool) : DurableQueue :=
  if ok then persist (ackMem q) else ackMem q

/-- The add window: memory is ahead of disk after a failed write. -/
theorem addEvent_failure_mem_ahead (q : DurableQueue) (e : Event)
    (h : q.disk = q.mem) :
    (addEvent q e false).mem = q.mem ++ [e] ∧
      (addEvent q e false).disk = q.mem

/-- Replaying the same event after the failed add duplicates it. -/
theorem addEvent_retry_after_failure_duplicates (q : DurableQueue) (e : Event)
    (h : q.disk = q.mem) :
    (addEvent (addEvent q e false) e true).disk = q.mem ++ [e, e]

/-- The ack window: the event is gone from memory but still on disk. -/
theorem ackEvent_failure_disk_still_front (q : DurableQueue) (e : Event)
    (rest : List Event) (hmem : q.mem = e :: rest) (hdisk : q.disk = q.mem) :
    (ackEvent q false).mem = rest ∧
      (ackEvent q false).disk = e :: rest

/-- What atomicity would buy: the acked front is absent from both copies. -/
theorem atomicAck_removes_front (q : DurableQueue) (e : Event)
    (rest : List Event) (hmem : q.mem = e :: rest) (hnot : e ∉ rest) :
    let q' := persist (ackMem q)
    e ∉ q'.mem ∧ e ∉ q'.disk
```

**Hypotheses.** `ok = false` is an abstract failed write, not a proof that
KVStore fails. `q.disk = q.mem` is the quiescent precondition before the
operation. The atomic-ack theorem is a *conditional* positive: atomic update
of memory and disk removes the event from both.

**Non-vacuity witness.** `q := { mem := [e], disk := [e] }`. A failed add
leaves `mem = [e, e]`, `disk = [e]`; a retry duplicates. A failed ack leaves
`mem = []`, `disk = [e]`; restart re-delivers `e`.

**Why it is faithful.** It encodes the exact ordering of
`event.rs:437-474`: push then persist for add; pop then persist for ack. The
`ReplayEvent` mapping at `event.rs:1978-1981` supplies the retry that makes
the duplicate concrete. The theorem is a **warning**, not a claim that LDK
Node is wrong: the code may accept at-least-once and rely on event handlers
being idempotent.

**Fidelity risk.** Medium: `Bool` abstracts write failure; real KVStore errors
may be transient or permanent. The model does not claim which. **Feasibility.**
Very high. **Classification:** model extension; atomicity is an external
assumption (A2). **Priority:** P1.

---

### T5 — Ping/pong reply at the dispatch boundary (P1)

**Proposed fully-qualified names**

- `LnLean.Protocol.EventRuntime.pongFor`
- `LnLean.Protocol.EventRuntime.receiveReply?`
- `LnLean.Proofs.Protocol.EventRuntimeTargets.receiveReply?_ping`
- `...receiveReply?_ping_cutoff`
- `...receiveReply?_ping_state`
- `...pongFor_bounded`

**Statement shape**

```lean
def pongFor (p : Ping) : Msg :=
  .pong { ignored := ⟨(List.replicate p.numPongBytes (0 : UInt8)).toArray⟩ }

/-- A dispatch result: the new peer state and the messages to enqueue. -/
def receiveReply? (s : PeerState) (m : Msg) : Option (PeerState × List Msg) :=
  match s.transport with
  | .down => none
  | .up =>
      match m with
      | .ping p =>
          if p.numPongBytes < 65532 then some (s, [pongFor p])
          else some (s, [])
      | .pong _ => some (s, [])
      | _ => (receive s m).map (fun s' => (s', []))

theorem receiveReply?_ping (s : PeerState) (p : Ping)
    (h : s.transport = .up) (hlen : p.numPongBytes < 65532) :
    receiveReply? s (.ping p) = some (s, [pongFor p])

theorem receiveReply?_ping_cutoff (s : PeerState) (p : Ping)
    (h : s.transport = .up) (hlen : ¬ p.numPongBytes < 65532) :
    receiveReply? s (.ping p) = some (s, [])

/-- The new state is exactly what the existing `receive` returns for ping. -/
theorem receiveReply?_ping_state (s : PeerState) (p : Ping)
    (h : s.transport = .up) :
    (receiveReply? s (.ping p)).map Prod.fst = receive s (.ping p)

/-- The generated pong respects the framing bound; this reuses the existing
`pong_reply_bounded`. -/
theorem pongFor_bounded (p : Ping) (h : p.numPongBytes < 65532) :
    msgLength (pongFor p) ≤ 65535
```

**Hypotheses.** `s.transport = .up`; the BOLT 1 cutoff is strict
(`< 65532`), exactly as `peer_handler.rs:2431`. The pong payload is
zero-filled of length `numPongBytes`, matching `byteslen = ponglen`
(`:2432`).

**Non-vacuity witness.** `p := { numPongBytes := 0, ignored := ByteArray.empty }`
yields `pongFor p = .pong { ignored := #[] }` and `receiveReply?_ping` applies.
`p.numPongBytes = 65532` gives the cutoff branch and `[]`.

**Why it is faithful.** It models the actual transport reply, which the
current `receive` cannot express because it returns only `Option PeerState`.
The existing `receive` is unchanged; T5 is a wrapper. `pongFor_bounded` is
the bridge to the already-proved `pong_reply_bounded`
(`Protocol/Laws.lean:112-115`), so the new target does not duplicate framing
arithmetic.

**Fidelity risk.** Low/medium: no pong timer state, no disconnect-on-missing-
pong behavior (`peer_handler.rs:3575-3663`); those remain external. The
target is only “receive ping → emit pong”, not liveness. **Feasibility.**
High. **Classification:** model extension. **Priority:** P1.

---

### T6 — Unknown-channel dispatch emits an error (P2)

**Proposed fully-qualified names**

- `LnLean.Protocol.EventRuntime.errorFor`
- `LnLean.Protocol.EventRuntime.unknownChannelReply?`
- `LnLean.Proofs.Protocol.EventRuntimeTargets.unknownChannelReply?_emits_error`
- `...unknownChannelReply?_no_error_for_known`
- `...unknownChannelReply?_state_unchanged`

**Statement shape**

```lean
def errorFor (cid : ChannelId) : Msg :=
  .error { channelId := cid, data := ByteArray.empty }

/-- The reply-only projection of dispatch for an unknown channel.  The
`channel_reestablish` special case is deliberately excluded (see §5). -/
def unknownChannelReply? (s : PeerState) (m : Msg) : Option (List Msg) :=
  match channelId? m with
  | none => some []
  | some cid =>
      match findChannel s cid with
      | some _ => some []
      | none =>
          if m.kind = .channelReestablish then some []
          else some [errorFor cid]

theorem unknownChannelReply?_emits_error (s : PeerState) (m : Msg)
    (cid : ChannelId) (hc : channelId? m = some cid)
    (hf : findChannel s cid = none) (hk : m.kind ≠ .channelReestablish) :
    unknownChannelReply? s m = some [errorFor cid]

theorem unknownChannelReply?_no_error_for_known (s : PeerState) (m : Msg)
    (cid : ChannelId) (hc : channelId? m = some cid)
    (hc' : findChannel s cid ≠ none) :
    unknownChannelReply? s m = some []
```

**Hypotheses.** The message is channel-directed and is not
`channel_reestablish`. The generic LDK path is
`no_such_channel_for_peer` → `send_err_msg_no_close`
(`channelmanager.rs:1220-1226`). The special reestablish response
(`:14107-14127`) is not modelled here.

**Non-vacuity witness.** `m := .commitmentSigned cs`, `cid` absent from
`s.channels`; the result is `[errorFor cid]`. A known `cid` gives `[]`.

**Why it is faithful.** It captures the *dispatch reply* that
`receive_channel_requires_channel` (`Peer.lean:283-286`) currently drops. The
state component stays unchanged, matching the “no close” action. The exact
error string and the reestablish special case are out of scope.

**Fidelity risk.** Medium/high: LDK has per-message behavior (`Ignore`,
`Warning`, `Error`, disconnect) and the reestablish special case; a single
generic error theorem could overgeneralize if the hypotheses are dropped.
**Feasibility.** High for the narrow statement. **Classification:** model
extension. **Priority:** P2.

---

### T7 — Concurrent connect single-flight (P2)

**Proposed fully-qualified names**

- `LnLean.Protocol.ConnectionRuntime.PendingConnections`
- `LnLean.Protocol.ConnectionRuntime.register`
- `LnLean.Proofs.Protocol.ConnectionRuntimeTargets.register_first_is_owner`
- `...register_second_is_subscriber`
- `...register_at_most_one_owner`

**Statement shape**

```lean
structure PendingConnections where
  entries : List PubKey  -- one entry per `node_id` currently being dialed

def ownerCount (p : PendingConnections) (pk : PubKey) : Nat :=
  (p.entries.filter (fun k => k = pk)).length

def register (p : PendingConnections) (pk : PubKey) :
    PendingConnections × Bool :=
  if p.entries.any (fun k => k = pk) then (p, false)
  else ({ entries := p.entries ++ [pk] }, true)

theorem register_first_is_owner (p : PendingConnections) (pk : PubKey)
    (h : ownerCount p pk = 0) : (register p pk).2 = true

theorem register_second_is_subscriber (p : PendingConnections) (pk : PubKey)
    (h : ownerCount p pk = 1) : (register p pk).2 = false

theorem register_at_most_one_owner (p : PendingConnections) (pk : PubKey) :
    ownerCount (register p pk).1 pk ≤ 1
```

**Hypotheses.** A single-threaded abstraction of the `Mutex<HashMap<...>>`
critical section; no task interleaving, cancellation, or failure. The
`Bool` says “this caller should dial”, not “the dial succeeded”.

**Non-vacuity witness.** `p := { entries := [] }`, `pk` arbitrary: first
register returns `true`, second returns `false` and does not add a duplicate.
`ownerCount` is `1` after the first and remains `1` after many subscribers.

**Why it is faithful.** It mirrors `register_or_subscribe_pending_connection`
(`connection.rs:277-293`): vacant → insert owner and return `None`; occupied →
subscribe and return a receiver. `propagate_result_to_subscribers`
(`:295-305`) is the result fan-out; the guard (`:45-46,107-111`) is the
abandonment cleanup.

**Fidelity risk.** Medium: the real code has a lock, `oneshot` channels,
cancellation, and a guard that can remove the entry; the model assumes the
lock serializes. **Feasibility.** High. **Classification:** model extension at
the node-runtime boundary, not a protocol theorem. **Priority:** P2.

---

## 5. Assumptions, counterexamples, and non-vacuity risks

### 5.1 Existing theorems that must not be weakened or hidden

These are load-bearing negatives. A proposal that “fixes” them by changing the
underlying relation must be rejected; add a refinement instead.

| Declaration | Location | Why it must stay |
|---|---|---|
| `duplicate_commitmentSigned_advances_twice` | `ChannelReestablishProps.lean:386` | Proves the wave-A `advanceReceived` is not idempotent. T2 must keep it as the unrefined negative witness and add `receiveNumbered` beside it |
| `advanceReceivedNumbered_idempotent` | `ChannelReestablishProps.lean:403` | The positive refinement; T2 reuses it. Do not replace the wave-A model with it silently |
| `receive_counters_monotone` | `ChannelReestablishProps.lean:420` | The existing lift to `PeerState`; T2 must not contradict it |
| `reachable_counters_inconsistent` | `ChannelReestablishProps.lean:528` | Proves `Step.revokeAndAck` can run twice without a preceding `commitment_signed`; do not “fix” `Step` by adding the guard as a theorem |
| `literal_round_fold_refuted` | `ProtocolEventFoldTargets.lean:634` | Proves the dance guard cannot be folded into `Step` as an equality; keep `Step ⊇ GuardedStep` |
| `literal_revoke_fold_refuted` | `ProtocolEventFoldTargets.lean:645` | Same for the revocation guard |
| `fold_cannot_both_preserve_balance_and_carry_add` | `ProtocolEventFoldTargets.lean:696` | A `Step`-shaped fold cannot both preserve balance and accept an affordable add |
| `fold_cannot_both_preserve_htlcs_and_carry_add` | `ProtocolEventFoldTargets.lean:712` | The HTLC-list form |
| `unguarded_double_commitmentSigned_breaks_ordering_retained` | `ProtocolEventFoldTargets.lean:742` | The retained wave-6 counterexample; the guard layer must not erase it |
| `unguarded_revokeAndAck_from_idle_breaks_ordering_retained` | `ProtocolEventFoldTargets.lean:749` | Same |
| `unguarded_step_signs_revoked_commitment_retained` | `ProtocolEventFoldTargets.lean:754` | Same |
| `guarded_no_double_commitmentSigned` | `ProtocolEventFoldTargets.lean:765` | The guarded relation’s positive exclusion; do not collapse it into `Step` |

The important nuance for this lane: the model already has a **guarded**
channel layer that excludes a double `commitment_signed`
(`guarded_no_double_commitmentSigned`), but `PeerState.receive` operates on
`ChannelRecord` and does not use the guard. T2 closes that specific gap at the
receipt layer without touching `Step` or `GuardedStep`.

### 5.2 Non-vacuity witnesses for the new targets

- **T1:** `{ pending := [] }` and `{ pending := [e₁, e₂] }`; both `front?` and
  `ack` reduce definitionally.
- **T2:** `sampleChannel` (`ChannelReestablishProps.lean:508`) with
  `k = nextCommitmentNumber`; first application advances, second is absorbed.
  `k = next + 1` exercises the stale branch.
- **T3:** all-`handled`, all-`replay`, and one-handled-then-replay batches.
- **T4:** `{ mem := [e], disk := [e] }` with `ok = false` for both add and ack.
- **T5:** `numPongBytes = 0` (reply) and `numPongBytes = 65532` (cutoff).
- **T6:** `commitmentSigned` addressed to an absent `cid`.
- **T7:** empty `PendingConnections`, then two `register` calls for the same
  `pk`.

### 5.3 Assumptions (explicit, not axioms)

- **A1 — receipt key source.** `Msg.commitmentSigned` does not carry a
  commitment number (the module docstring says so at
  `ChannelReestablishProps.lean:93-98`). T2’s `k` must be supplied by the
  dispatcher/reestablish state. If `k` is guessed or fixed, the theorem is
  either vacuous or unsound. This is the main external assumption and must
  appear as an explicit hypothesis, never as an axiom.
- **A2 — persistence atomicity.** A duplicate-free transitive claim across a
  crash needs an atomic update of memory+disk or an idempotent event
  application. LDK Node’s `add_event`/`event_handled` order does not provide
  it (`event.rs:437-474`). T4’s negative theorems are the honest boundary.
- **A3 — client delivery.** ldk-server explicitly has no replay and no client
  ack (`api-guide.md:330-333`; `service.rs:472-474`). No Lean theorem should
  claim “the client received the event”; at most “the server enqueued it”.
- **A4 — concurrency.** T1–T7 are single-threaded list/`Option` models. The
  real code uses `Mutex`, `tokio` tasks, `oneshot`, and a `VecDeque`; T7
  abstracts the lock, and none of the targets model interleaving.
- **A5 — handler purity.** T3’s `h : Event → HandleOutcome` is a pure
  classification. Real `handle_event` writes stores, can fail transiently,
  and is not proved idempotent. T3 is a control-flow theorem, not an
  end-to-end event-effect theorem.
- **A6 — runtime scheduling.** `Liveness.Fair` is a schedule parameter
  (`Liveness.lean:306-311`), not a tokio fairness or timer theorem. No target
  here claims that the background processor eventually runs.

### 5.4 Counterexamples that refute stronger claims

These should be stated as theorems or retained as explicit negatives; do not
state their negations as targets.

1. **`ack` is not keyed/idempotent.** With `pending = [e₁, e₂]`, two
   `event_handled` calls pop both; a second ack after one `next_event` drops
   `e₂`. This refutes “ack is idempotent” for the positional LDK operation
   (`event.rs:461-468`).
2. **`add_event` does not deduplicate.** Enqueuing the same `Event` twice
   leaves two copies; there is no key comparison (`event.rs:437-444`).
3. **A failed ack replays after restart.** `pop_front` before
   `persist_queue` leaves the old queue on disk (`event.rs:461-468`); the
   restart re-delivers the event. This refutes “ack is crash-safe” without
   A2.
4. **A failed add duplicates on retry.** `push_back` before
   `persist_queue`, plus `ReplayEvent` on failure (`event.rs:1978-1981`),
   leaves the event in memory and re-adds it on replay.
5. **`processBatch` handles no event after the first replay.** This is the
   intended at-least-once behavior, but it refutes “the whole batch is always
   processed” (`channelmanager.rs:3714-3718`).
6. **`PersistenceRecovery.replay` is not duplicate-free.** `applyMsg`
   increments on every `commitmentSigned` (`:305-307`); `restore_replay_suffix`
   is an equality to full replay, not to deduplicated handling. It should not
   be cited as event-receipt idempotency.
7. **`receive` drops an unknown channel.** `receive_channel_requires_channel`
   returns `none` (`Peer.lean:283-286`), whereas LDK sends an error
   (`channelmanager.rs:1220-1226`). The Lean behavior is a state-layer
   projection, not a faithful dispatch result.
8. **`receive` does not reply to ping.** It returns `some s` for `ping`
   (`Peer.lean:222-224`), while LDK emits a pong
   (`peer_handler.rs:2430-2435`). The existing `pong_reply_bounded` is only a
   framing theorem.

---

## 6. Wave-13 recommendation

### 6.1 Implement (narrow, additive)

A single additive lane is safe and useful:

1. **`LnLean/Protocol/EventRuntime.lean`** — the queue, batch, durable-queue,
   ping/pong reply, and unknown-channel reply *definitions* (T1, T3, T4, T5,
   T6).
2. **`LnLean/Proofs/Protocol/EventRuntimeTargets.lean`** — the corresponding
   theorems, importing `ChannelReestablishProps`.
3. **`LnLean/Proofs/Protocol/ChannelReestablishProps.lean`** — add T2’s
   `receiveNumbered` and its four theorems next to `advanceReceivedNumbered`.
4. Optionally add T7 in a separate `ConnectionRuntime` module; it is not a
   protocol theorem and should not be mixed into the channel namespace.

The highest-value, lowest-risk order is:

- **P0:** T2 (`receiveNumbered`/idempotence) and T3 (`processBatch`).
- **P1:** T1 (queue/ack, including `double_ack_drops_next`) and T4 (crash
  windows; explicitly negative).
- **P1:** T5 (ping/pong) because it reuses `pong_reply_bounded` and is small.
- **P2:** T6 (unknown-channel reply) and T7 (single-flight).

Do **not** change `advanceReceived`, `Step`, `GuardedStep`, `receive`, or
`PersistenceRecovery.replay` to make the new targets true. Add refinements and
keep the retained counterexamples.

### 6.2 Defer

- Full event-to-action/store application idempotency. It needs a model of
  `EventHandler.handle_event`’s per-event store writes and the event types it
  emits; the current Lean tree has no event/store layer for this.
- Exact unknown-channel behavior per message type (including the
  `channel_reestablish` defensive response and disconnect actions).
- Ping timeout / disconnect-on-missing-pong. T5 models only the immediate
  reply, not the liveness loop.
- Single-flight connect beyond the single-threaded abstraction.

### 6.3 Treat as external / human barrier

The following cannot be honestly mechanized from the current model and public
LDK APIs without new external assumptions:

- Tokio task scheduling, wakeups, `Mutex` contention, and cancellation.
- The atomicity of `EventQueue.mem` and KVStore persistence (A2).
- ldk-server subscriber fan-out, bounded-channel lag, replay, and client
  acknowledgement (A3).
- Any claim that an event was *delivered to a client* or *handled exactly
  once* end-to-end.
- The real `EventHandler.handle_event` side-effect semantics (A5).

Wave 13 should therefore claim only **receipt/queue/batch control-flow
properties**, not runtime or delivery fidelity. The report’s top target is T2:
it is the only proposal that both targets a concrete existing gap
(`duplicate_commitmentSigned_advances_twice`) and reuses an already-proved
refinement (`advanceReceivedNumbered_idempotent`), while retaining the
negative theorem unchanged.

### 6.4 Gate suggestions for the implementation lane

- No new `axiom`, `admit`, `native_decide`, `unsafe`, or
  `@[implemented_by]`.
- `#print axioms` on every new target; all should be empty or only the
  standard kernel axioms.
- `lake env lean LnLean/Protocol/EventRuntime.lean` and
  `lake env lean LnLean/Proofs/Protocol/EventRuntimeTargets.lean` only; do not
  run a full tree build for this lane.
- Add the new targets to `docs/THEOREM-INDEX.md` only after they are proved;
  do not add a row that claims runtime fidelity.
- Keep the existing 51 rows and all counterexamples unchanged.

---

## 7. Evidence and commands

All commands were read-only. No branch switch, commit, `cargo`, `lake build`,
or network access was performed.

```text
$ pwd
/home/ubuntu/ln-lean-repair

$ git rev-parse HEAD
f7f062817c185cd70004bb26c652deb99c6fd4bd
$ git branch --show-current
repair/integrated

$ git -C /tmp/opencode/ldk-refs/ldk-node rev-parse HEAD
fa123fed131e27ecc420b77fa7086fcf1ddaebb8
$ git -C /tmp/opencode/ldk-refs/ldk-server rev-parse HEAD
c17dc11dde38f88c53457039ddf30c6b90a63ba2

$ grep -cE '^\| `LN-' docs/THEOREM-INDEX.md
51
$ grep -nE '^\| `LN-(CH|PR|RT)-' docs/THEOREM-INDEX.md | head -30
... rows LN-CH-001..007, LN-PR-001..006, LN-RT-001..006 ...

$ grep -niE 'event.?queue|background.?processor|dispatch|event_loop|retry|idempoten|replay|runtime' LnLean --include='*.lean'
... only payment/gossip idempotence and node-announcement replay; no event queue ...

$ grep -nE 'process_events_body|ReplayEvent|replay' refs/rust-lightning/lightning/src/ln/channelmanager.rs
... 3663, 3702-3726, 3714-3718 ...

$ grep -nE 'fn add_event|fn handle_event|fn event_handled|fn next_event|persist_queue' \
    /tmp/opencode/ldk-refs/ldk-node/src/event.rs
... 421, 437-474, 476-493, 548-560, 804 ...

$ grep -nE 'register_or_subscribe_pending_connection|propagate_result_to_subscribers' \
    /tmp/opencode/ldk-refs/ldk-node/src/connection.rs
... 277-293, 295-305 ...

$ grep -nE 'receiver_count|event_handled|broadcast::channel|Lagged' \
    /tmp/opencode/ldk-refs/ldk-server/ldk-server/src/main.rs \
    /tmp/opencode/ldk-refs/ldk-server/ldk-server/src/service.rs
... 320, 847-873, 472-474 ...
```

Key files read (Lean):

- `LnLean/Channel/State.lean` — `ProtocolEvent`, `Step`, `Reachable`,
  `UpdateEvent`, `UpdateStep`, `DanceEvent`, `GuardedStep`.
- `LnLean/Protocol/Peer.lean` — `ChannelRecord`, `advanceReceived`,
  `PeerState`, `send`, `receive`, `resend`, `LossyLink`,
  `reestablish_no_rollback`.
- `LnLean/Proofs/Protocol/ChannelReestablishProps.lean` —
  `duplicate_commitmentSigned_advances_twice`, `advanceReceivedNumbered`,
  `advanceReceivedNumbered_idempotent`, `receive_counters_monotone`,
  `reachable_counters_inconsistent`.
- `LnLean/Proofs/Channel/ProtocolEventFoldTargets.lean` —
  `literal_round_fold_refuted`, `literal_revoke_fold_refuted`,
  `guarded_no_double_commitmentSigned`, the two fold-impossibility theorems,
  and the retained counterexamples.
- `LnLean/Proofs/Protocol/ErrorProps.lean` — `applyToChannel`,
  `handleInbound`, unknown-channel state scoping.
- `LnLean/Proofs/Liveness.lean` — `runList`, `runPrefix`, `Fair`,
  `fair_awaitingLockin_eventually_normal`.
- `LnLean/Proofs/PhaseC3/PersistenceRecovery.lean` — `Persisted`, `Snapshot`,
  `applyMsg`, `replay`, `replay_no_rollback`, `restore_replay_suffix`.
- `LnLean/Protocol/Messages.lean` — `Ping`, `Pong`, `Msg`, `channelId?`.
- `LnLean/Protocol/Laws.lean` — `pong_reply_bounded`, `ping_bounded`.

Key files read (pinned LDK):

- LDK Node: `src/event.rs`, `src/lib.rs`, `src/runtime.rs`,
  `src/connection.rs`, `src/message_handler.rs`.
- LDK Server: `ldk-server/src/main.rs`, `ldk-server/src/service.rs`,
  `docs/api-guide.md`.
- rust-lightning: `lightning/src/ln/channelmanager.rs`,
  `lightning/src/ln/peer_handler.rs`,
  `lightning-background-processor/src/lib.rs`.

**Not run:** `lake build`, any `cargo` command, any test suite, any network
fetch. The proposed code blocks are statement shapes, not compiled code; they
intentionally omit proof bodies and some imports.
