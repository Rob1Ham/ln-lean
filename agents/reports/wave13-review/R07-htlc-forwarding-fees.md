# R07 — HTLC add/fulfill/fail, forwarding, and fee accounting

**Status:** read-only review
**Pins:** LDK Node `fa123fed131e27ecc420b77fa7086fcf1ddaebb8`, LDK Server `c17dc11dde38f88c53457039ddf30c6b90a63ba2`

## 1. Scope and current Lean surface

This lane covers four things that LDK treats as one lifecycle but Lean keeps in
separate layers:

1. the per-channel `update_add_htlc` / `update_fulfill_htlc` /
   `update_fail_htlc` transitions;
2. the node-level act of forwarding an inbound HTLC on one channel to an
   outbound HTLC on another channel;
3. forwarding-fee accounting, both at route level and at the persisted
   per-channel / per-forward record level;
4. failure reasons and their propagation.

The current Lean surface has four layers, and they are not connected by any
end-to-end refinement theorem.

| Layer | Main declarations | What it actually claims | What it does not claim |
|---|---|---|---|
| Wire messages | `UpdateAddHtlc` (`LnLean/Protocol/Messages.lean:198-205`), `UpdateFulfillHtlc` (`:208-212`), `UpdateFailHtlc` (`:215-219`) | BOLT 2 payloads, including `htlc_id`; `UpdateFailHtlc.reason` is opaque `ByteArray` | No failure-code semantics, no onion-failure decryption, no linkage to channel state |
| Per-channel state machine | `AffordableAdd` (`LnLean/Channel/State.lean:300-316`), `updateAddHtlc` (`:323-341`), `failHtlcAt` (`:358-373`), `fulfillHtlcAt` (`:378-393`), `UpdateEvent` (`:398-404`), `UpdateStep` (`:414-438`), `UpdateReachable` (`:441-446`) | A single `Channel` moves to a successor on one update message; ledger conservation is proved per channel (`LnLean/Proofs/Channel/StateTransitionTargets.lean:425-442`) | No `htlc_id` in `Channel.HTLC` (`LnLean/Channel/Types.lean:142-148`); settlement selects by list index; no second channel, no forwarding pair, no failure reason |
| Executable id/record model | `HTLCRecord` (`LnLean/Channel/HTLC.lean:76-89`), `HtlcBook.allocate` (`:836-844`), `HtlcBook.add` (`:869-873`), `MAX_ACCEPTED_HTLCS` (`:69`) | Per-sender id allocation, id uniqueness, executable add/fulfill/fail guards; `MAX_ACCEPTED_HTLCS = 483` is defined | `HTLCRecord`/`HtlcBook` are not connected to `Channel`/`UpdateStep`; `MAX_ACCEPTED_HTLCS` is never used in a guard |
| Route/fee arithmetic | `Hop.ofEdge` (`LnLean/Routing/Route.lean:92-97`), `Route.totalFee` (`:141-142`), `BackwardConserves` (`LnLean/Proofs/PhaseC3/CrossChannelRouting.lean:119-123`), `forwardFeeTotal` (`:156-157`), `sender_eq_last_add_forwardFees` (`:470-473`), `sender_le_last_add_totalFee` (`:478-482`) | Per-hop amount conservation, telescoping sender/fee identity, route total fee | `FeasiblePath`/`LiquidityModel` contain no `Channel` (`CrossChannelRouting.lean:379-407`); no actual claimed amount, no forwarding record, no failure path |

The central negative fact is simple: **no Lean declaration relates an inbound
HTLC on one channel to an outbound HTLC on another channel.** `UpdateStep` is
typed `Channel → UpdateEvent → Channel → Prop` (`State.lean:414-415`), and
`UpdateReachable` closes only that one-channel relation (`:441-446`).
`CrossChannelRouting` is a route-plan arithmetic layer: its `FeasiblePath`
(`:387-407`) carries a list of `(ChannelEdge × Msat)` pairs and graph/liquidity
preconditions, not channel states, HTLC ids, or settlement events. Its own
scope note says fee rounding against LDK is not modelled (`:75-87`).

Catalog status is correspondingly narrow:

* `LN-HT-001` is `LnLean.Security.HtlcRecord.fulfill_sound`
  (`docs/TRACEABILITY.md:35`;
  `LnLean/Security/Invariants.lean:220-229`).
* `LN-HT-002` is `LnLean.Security.HtlcRecord.fail_only_after_expiry`
  (`docs/TRACEABILITY.md:36`; `Security/Invariants.lean:244-249`).
* `LN-HT-003` is `LnLean.Channel.HTLC.amount_conservation`
  (`docs/TRACEABILITY.md:37`).
* `LN-HT-004` is the `HTLC` id-uniqueness family (`docs/TRACEABILITY.md:38`).
* `LN-RT-005` is CLTV accumulation only (`LnLean/Proofs/WaveE/E26.lean:10-11`).

There is **no catalog row** for forwarding lifecycle, forwarding fees, or
forwarding records, and `CrossChannelRouting` is not in the theorem index. No
row should be added until a target is proved and anchored.

Three distinctions matter for the rest of this report:

* `LnLean.Channel.HTLC` (`Types.lean:142-148`) has no `id`; `HTLCRecord`
  (`Channel/HTLC.lean:76-89`) has one. LDK forwarding records are keyed by
  `(channel_id, htlc_id)` (`forwarding_store.rs:402-407`). The current
  `UpdateStep` cannot produce that key.
* `HtlcRecord.fail` / `fail_only_after_expiry` is the **on-chain timeout**
  transition (`Security/Invariants.lean:231-249`). It is not the off-chain
  `update_fail_htlc` transition, which `UpdateStep.update_fail_htlc`
  (`State.lean:435-438`) correctly treats as immediately available and carries
  no reason. `LN-HT-002` must not be cited as coverage of failure forwarding.
* `UpdateStep.update_fulfill_htlc` checks `p.Valid` and
  `hashFn p.bytes = h.paymentHash.bytes` (`State.lean:428-432`), but the
  successor `fulfillHtlcAt` (`:378-393`) does not store the preimage. The
  `Security.HtlcRecord` model does store it (`Security/Invariants.lean:195-201,
  211-216`), but that model is not connected to `Channel`.

## 2. LDK datapoints (with `file:line`)

LDK refs below are under the pinned clones
`/tmp/opencode/ldk-refs/ldk-node` and `/tmp/opencode/ldk-refs/ldk-server`;
`rust-lightning` and BOLT refs are under `refs/` in this repository.

### 2.1 Forwarding event and the fee identity

* `rust-lightning/lightning/src/ln/channelmanager.rs:10905-10947` is the
  authoritative source-routed forwarding claim path. The fee is
  `total_fee_earned_msat = htlc_claim_value_msat
  .and_then(|claimed| claimed.checked_sub(forwarded_htlc_value_msat))`
  (`:10910-10911`). If the claim value is known but the subtraction underflows,
  the node logs “we paid out more than we took in” and the fee is `None`
  (`:10912-10915`). `skimmed_fee_msat` is asserted to be included in the total
  (`:10917-10919`). The emitted event carries one inbound and one outbound
  locator for source-routed payments (`:10924-10937`).
* `ldk-node/src/event.rs:184-219` documents `PaymentForwarded`.
  `total_fee_earned_msat` is `Option<u64>`: if the incoming channel was
  force-closed, on-chain fees are not yet known and the field is `None`
  (`:201-204`). `skimmed_fee_msat` is “the share of the total fee ... withheld
  in addition to the forwarding fee” (`:205-213`).
  `outbound_amount_forwarded_msat` is the amount after the fee is deducted
  (`:217-218`).

Consequence: for a successful, source-routed forward with a known fee, the
identity is `inbound_claimed = outbound_forwarded + fee`. It is not an
unconditional law. LDK explicitly permits the intercepted-HTLC case where the
node pays out more than it took in; such a forward has `total_fee_earned_msat =
None` and is not persisted (`forwarding_store.rs:220-233`).

### 2.2 Persisted forwarding records

* `ldk-node/src/payment/forwarding.rs:95-100` states the eligibility rule:
  “A forward is recorded only when it consisted of exactly one incoming and one
  outgoing HTLC and LDK reported a total fee.” Unknown fee (incoming
  force-close) means no record at all.
* `ForwardedPaymentDetails` (`forwarding.rs:103-133`) carries
  `inbound_amount_forwarded_msat` (`:119`), `total_fee_earned_msat` (`:121`),
  `skimmed_fee_msat` (`:126`), `claim_from_onchain_tx` (`:128`), and
  `outbound_amount_forwarded_msat` (`:130`). `skimmed_fee_msat` is a share of
  the total, not an additive amount (`:122-126`).
* `ldk-node/src/payment/forwarding_store.rs:219-233` is the actual guard:
  a forward is tracked only if `[prev_htlc]`, `[next_htlc]`,
  `Some(fee_earned_msat)`, and `Some(prev_htlc_id)` all match. Otherwise it is
  skipped and logged (`:226-232`).
* `:235` builds the stable id from the **incoming** `(channel_id, htlc_id)`;
  `:402-407` is `sha256(channel_id_32_bytes || htlc_id_8_bytes)`. Replay
  markers are checked before writing (`:236-241`) and inserted after the writes
  (`:315-322`). Details are stored only in `Detailed` mode (`:242-243`,
  `:291-313`).
* `:248-249` computes `inbound_amount_msat =
  outbound_amount_forwarded_msat.saturating_add(fee_earned_msat)`, i.e. the
  persisted inbound value is the outbound value plus the fee.
* `:253-266` updates the outbound channel’s stats: outbound count 1, outbound
  amount `outbound_amount_forwarded_msat`, fee `Some(0)`, and
  `onchain_claims_count` from `claim_from_onchain_tx`. `:272-285` updates the
  inbound channel’s stats: inbound count 1, inbound amount, fee
  `Some(fee_earned_msat)`, skim, and onchain count 0. This is the authoritative
  fee-attribution rule: **fees belong to the incoming channel**, and on-chain
  claims belong to the outgoing channel.
* `ldk-node/src/payment/forwarding.rs:154-187` documents the same attribution
  (`:167-172`), warns that skim is not additive (`:174-178`), and documents
  `onchain_claims_count` as outgoing-only (`:179-182`).
* Tests: `forwarding_store.rs:1597-1663` records a 110/100/10 forward twice and
  asserts exactly one detail, inbound amount 110, inbound fee 10, outbound fee
  0, outbound on-chain count 1. `:1665-1706` repeats the replay test in `Stats`
  mode and asserts no detail records. `:1708-1766` feeds two inbound HTLCs and,
  separately, a `None` fee; both are skipped.
* End-to-end: `ldk-server/e2e-tests/tests/e2e.rs:1783-2021`. It asserts one
  inbound and one outbound locator and a known fee (`:1880-1882`), persisted
  before the event is visible (`:1884-1891`), per-channel stats with fee on the
  incoming channel and zero on the outgoing channel (`:1907-1929`), detail
  fields (`:1978-1985`), and field-equal reload after restart
  (`:1990-2020`).

### 2.3 Fee arithmetic

* `rust-lightning/lightning/src/routing/router.rs:2639-2642` is LDK’s fee
  formula:
  `amount_msat.checked_mul(proportional_millionths)
  .and_then(|part| base_msat.checked_add(part / 1_000_000))`.
  The proportional term **floors**.
* `router.rs:776-785` (`Path::fee_msat`) excludes the last hop’s full payment
  value from the fee sum.
* Lean’s `Hop.ofEdge` (`Route.lean:83-97`) uses
  `base + (amount * ppm + 999999) / 1_000_000`, i.e. it **ceils**. The doc
  explicitly says this is a conservative over-estimate and does not claim to
  match `rust-lightning` (`:86-91`).
* Counterexample: `base = 0`, `ppm = 1000`, `amount = 1500`. Lean gives
  `(1_500_000 + 999_999) / 1_000_000 = 2`; LDK gives
  `1_500_000 / 1_000_000 = 1`. The existing
  `ofEdge_rounding_counterexample` (`LnLean/Proofs/Routing/RouteBlindingProps.lean:252-258`)
  is a different gap (the inverse forwarded-amount formula at 1000/1000), and
  must be retained separately.
* BOLT 7 leaves the division rounding to the implementation
  (`Route.lean:86-91`). Therefore a floor-fee theorem is an **LDK refinement**,
  not a BOLT-unique law.

### 2.4 Failure reasons

* `Messages.lean:215-219`: `UpdateFailHtlc.reason : ByteArray` is opaque. The
  wire does not expose a typed code to the Lean state machine.
* `rust-lightning/.../channelmanager.rs:1153-1184` defines the public
  `FailureCode` enum; `onion_utils.rs:1639-1708` defines the richer internal
  `LocalHTLCFailureReason`; `onion_utils.rs:2019-2026` defines
  `HTLCFailReason` as either a pre-built `OnionErrorPacket` or a local
  `Reason { data, failure_reason }`.
* On the forwarding path, `channelmanager.rs:10001-10115` takes
  `HTLCSource::PreviousHopData`, calls `get_htlc_forward_failure` with the
  incoming packet shared secret (`:10095-10105`), and emits
  `HTLCHandlingFailed { failure_type, failure_reason }` (`:10107-10115`).
* `channelmanager.rs:15303-15333` re-encrypts the failure packet under the
  **incoming** channel’s `incoming_packet_shared_secret`; for a blinded
  introduction-node failure it substitutes `InvalidOnionBlinding` rather than
  relaying the original code (`:15310-15319`).
* The Lean `OnionError` structure (`LnLean/Routing/Onion.lean:443-446`) has a
  typed `ErrorCode` field, and `OnionError.packetSize` is modelled
  (`:450-474`), but `OnionError.code` is not connected to
  `UpdateFailHtlc.reason`, `UpdateEvent.failHtlc`, or any relay relation.
  `OnionError.lean:59-69` explicitly excludes the failure code, TLV encoding,
  attribution data, and the ChaCha20/HKDF return-path obfuscation.

Consequence: “the failure code propagates” is not a copy of a field. It is a
decode/decide/re-encode operation with per-channel shared secrets and BOLT 4 TLV
semantics. A faithful Lean theorem needs an explicit codec/crypto interface,
not just an enum.

### 2.5 Add guards, ids, and `max_accepted_htlcs`

* BOLT 2 `refs/bolts/02-peer-protocol.md:739-742`: “`max_htlc_value_in_flight_msat`
  is a cap on total value of outstanding HTLCs **offered by the remote node**”.
  `:2826-2833` requires `id` to start at 0 and increase by 1 per offer, and
  `:2849-2852` rejects more than the receiver’s `max_accepted_htlcs` offered
  HTLCs.
* `rust-lightning/.../channel.rs:5854-5870` implements this directionally:
  `inbound_htlcs_count = remote_htlcs.iter().filter(|htlc| !htlc.outbound).count()`
  and `inbound_htlcs_value_msat` is the same filtered sum. It rejects when the
  count exceeds `holder_max_accepted_htlcs` (`:5860`) or the value exceeds
  `holder_max_htlc_value_in_flight_msat` (`:5866-5870`).
* LDK validates the negotiated `max_accepted_htlcs` at open/accept time:
  non-zero and at most `max_htlcs(channel_type)` (`channel.rs:4253-4261`,
  `:5271-5274`; `resource_manager.rs:720-726`). `max_htlcs` is 483 for
  non-zero-fee-commitment channels and 114 for zero-fee-commitment channels
  (`chan_utils.rs:60-72`), and each participant may set a lower value (`:64`).
  Lean’s `MAX_ACCEPTED_HTLCS = 483` is only the non-zero-fee ceiling, not a
  universal bound.
* Lean’s `AffordableAdd.withinInFlight` (`State.lean:315-316`) uses
  `pendingHtlcValueOf c` (`:266-269`), which sums **both** offered and received
  pending HTLCs. `HtlcBook.add` (`Channel/HTLC.lean:869-873`) also passes
  `b.totalInFlight` (`:830-831`), the same global sum. Both over-count the
  opposite direction relative to BOLT 2/LDK.
* `MAX_ACCEPTED_HTLCS` (`Channel/HTLC.lean:69`) is unused; `ChannelParams`
  (`Types.lean:77-92`) has no `maxAcceptedHtlcs` field, even though
  `OpenChannel`/`AcceptChannel` wire records carry it
  (`Messages.lean:112,122,151`). There is no conversion from the wire record to
  `ChannelParams`.

## 3. Gap matrix

| Behavior | Lean status | LDK evidence | Gap / counterexample | Priority |
|---|---|---|---|---|
| `update_add_htlc`: positive amount, minimum, CLTV bound, reserve, offered-balance coverage | covered faithfully per channel | BOLT 2 `:2822-2831`; LDK `channel.rs:5860-5890` | No commitment-fee / anchor-cost affordability check in `AffordableAdd`; `fitsOffered`/`leavesReserve` are only a simplified balance check | P2 |
| `max_htlc_value_in_flight_msat` is directional | **contradicted (over-rejection)** | BOLT 2 `:739-742`, `:2829`, `:2850`; LDK `channel.rs:5854-5870` | Counterexample: one pending **local-offered** 100 msat HTLC, local `maxHtlcValue = 100`; a remote add of 1 msat is rejected by Lean (`100 + 1 > 100`) but accepted by LDK (remote inbound value `0 + 1 ≤ 100`). Same bug in `HtlcBook.add` | P1 |
| `max_accepted_htlcs` count guard | missing | BOLT 2 `:2826-2828`, `:2849-2852`; LDK `channel.rs:5860` | `MAX_ACCEPTED_HTLCS = 483` is defined but unused; `ChannelParams` has no field; no theorem bounds pending count. A peer can add an unbounded number of HTLCs in the model | P1 |
| HTLC id / keying | partially covered | BOLT 2 `:2828-2833`; LDK `forwarding_store.rs:402-407` | Wire has `htlcId`; `HTLCRecord`/`HtlcBook` allocate per-sender ids; `Channel.HTLC`/`UpdateStep` use list indices and have no id. No refinement between `HTLCRecord` and `HTLC` | P1 |
| `update_fulfill_htlc`: preimage guard and receiver credit | covered faithfully per channel | BOLT 2 `:2920`, `:3004`; LDK `channelmanager.rs:10881-10903` | `UpdateStep` checks `p.Valid` and hash, and `balanceVal_fulfillHtlcAt` credits the receiver; but the successor does not store `preimage`, and `Security.HtlcRecord` is a disconnected model | P2 |
| `update_fail_htlc`: refund to offering side | covered faithfully per channel | BOLT 2 `:2944-2960`; LDK `channel.rs:8671` | `failHtlcAt` refunds the offering side and has no expiry guard (correct for off-chain failure); no reason field. `LN-HT-002` is the on-chain timeout, not this transition | P2 |
| Cross-channel forwarding lifecycle (inbound → outbound) | missing | LDK `channelmanager.rs:10905-10947`; `event.rs:184-219` | No Lean type relates two channels; `UpdateStep` is single-channel; `CrossChannelRouting` is path arithmetic with no channel state. No atomic pair transition, no rollback | P1 |
| Forwarding fee identity `inbound = outbound + fee` | missing | LDK `channelmanager.rs:10910-10911`; `forwarding_store.rs:248-249`; e2e `:1978-1985` | No theorem over channel states. `CrossChannelRouting` proves an advertised-fee telescoping identity (`:470-482`), not actual claimed minus forwarded value | P1 |
| Route-level fee conservation | partially covered | `router.rs:776-785`, `:2639-2642`; BOLT 7 `:975-981` | `BackwardConserves`, `sender_eq_last_add_forwardFees`, `total_fee_eq_sum` are internally consistent, but use ceiling fees and the first-hop convention documented at `CrossChannelRouting.lean:75-84`; no exact LDK floor | P1 |
| Fee attribution to incoming channel / per-channel stats | missing | LDK `forwarding_store.rs:253-289`; `forwarding.rs:154-187`; e2e `:1907-1929` | No `ChannelForwardingStats`, no inbound/outbound counters, no fee attribution, no on-chain claim attribution | P2 |
| Persisted forwarding record + replay marker | unmodelled/external | LDK `forwarding_store.rs:219-325`, tests `:1597-1766`; e2e `:1884-1891` | No store, no stable id, no replay marker, no `Detailed`/`Stats` modes, no persistence-before-event ordering | P2 |
| Failure reason/code and propagation | missing/unmodelled | LDK `channelmanager.rs:10001-10115`, `:15303-15333`; `onion_utils.rs:1639-1708`, `:2019-2026`; BOLT 4 failure packet | `UpdateFailHtlc.reason` is opaque; `OnionError.code` is disconnected; no decode/relay/re-encrypt, no TLV/attribution, no blinded-failure substitution | P2 / external |
| Unknown-fee, multi-HTLC, missing-id forwards are skipped | unmodelled/external | LDK `forwarding_store.rs:220-233`; tests `:1708-1766` | No eligibility predicate or “no record” theorem; current model has no place to state the skip | P2 |
| Persistence-before-event ordering | unmodelled/external | LDK `event.rs:1958-1978`; e2e `:1884-1891` | No event queue or persistence ordering in Lean | P2 |
| `u64` checked/saturating arithmetic | partially covered | LDK `router.rs:2640-2641` (checked), `forwarding_store.rs:249` (`saturating_add`), `channelmanager.rs:10910-10911` (`checked_sub`) | Lean uses unbounded `Nat`; any exact accounting theorem needs no-overflow/saturation hypotheses | P2 |
| On-chain claim and skim accounting | missing | LDK `forwarding_store.rs:262,281`; `forwarding.rs:174-182` | No `claim_from_onchain_tx`, `onchain_claims_count`, or skim-subset invariant; risk of double-counting skim if added naively | P2 |

## 4. Proposed targets

The targets below are ordered by safety of implementation, not by importance.
T1 is additive; T2–T4 change core types/guards and need a coordinated migration;
T5–T7 are a new cross-channel model and should be a wave-14 design item.

### T1. `LnLean.Routing.Hop.ofEdgeFloor_eq_ldk_compute_fees`

**Priority:** P1 — **Kind:** additive model extension — **Feasibility:** high —
**Fidelity risk:** low if stated as an LDK refinement, not a BOLT-unique law.

**Statement shape.**

```lean
namespace LnLean.Routing

/-- LDK `compute_fees`: `base_msat + amount_msat * ppm / 1_000_000`
(floor division).  This is deliberately a separate constructor; it does not
silently change `Hop.ofEdge`. -/
def Hop.ofEdgeFloor (e : ChannelEdge) (a : Msat) : Hop :=
  { node := e.node2
    shortChannelId := e.shortChannelId
    feeMsat := ⟨e.feeBaseMsat.val +
      a.val * e.feeProportionalMillionths / 1_000_000⟩
    cltvDelta := e.cltvDelta }

theorem ofEdgeFloor_fee_eq_ldk_compute_fees (e : ChannelEdge) (a : Msat) :
    (Hop.ofEdgeFloor e a).feeMsat.val =
      e.feeBaseMsat.val + a.val * e.feeProportionalMillionths / 1_000_000 := rfl

theorem ofEdgeFloor_le_ofEdge (e : ChannelEdge) (a : Msat) :
    (Hop.ofEdgeFloor e a).feeMsat.val ≤ (Hop.ofEdge e a).feeMsat.val

theorem ofEdge_eq_floor_iff_dvd (e : ChannelEdge) (a : Msat) :
    (Hop.ofEdge e a).feeMsat.val = (Hop.ofEdgeFloor e a).feeMsat.val ↔
      1_000_000 ∣ a.val * e.feeProportionalMillionths

/-- Counterexample that must be retained: 1500 msat at 1000 ppm. -/
theorem ofEdge_ceil_counterexample :
    ∃ (e : ChannelEdge) (a : Msat),
      e.feeBaseMsat = Msat.zero ∧ e.feeProportionalMillionths = 1000 ∧
      a.val = 1500 ∧
      (Hop.ofEdge e a).feeMsat.val = 2 ∧
      (Hop.ofEdgeFloor e a).feeMsat.val = 1
```

**Hypotheses.** None for the `Nat` identities. For a `u64` refinement, add
`a.val * e.feeProportionalMillionths < 2 ^ 64` and
`e.feeBaseMsat.val + ... < 2 ^ 64`, mirroring LDK’s `checked_mul` /
`checked_add`.

**Non-vacuity.** The 1500/1000 witness above is non-vacuous (Lean 2, LDK 1).
The exact-divisibility case `a = 2_000_000`, `ppm = 1000` gives fee 2000 in
both, so the equality theorem is not vacuous. The existing
`ofEdge_rounding_counterexample` must be kept as a separate witness.

**Why faithful.** It is a definitional transcription of
`router.rs:2639-2642`, and the monotonicity/divisibility lemmas explain exactly
when the existing ceiling constructor agrees. It does not claim BOLT 7 mandates
flooring; BOLT 7 leaves rounding implementation-defined.

**Weakening/assumption flags.** Do not redefine `Hop.ofEdge` to floor in place:
`CrossChannelRouting`’s witnesses and `ofEdge_fee_ge_base` are stated for the
ceiling constructor. Add the floor constructor and state explicitly that the
ceiling is a conservative payer-side over-estimate, not LDK’s actual fee.

### T2. `LnLean.Proofs.Channel.StateTransitionTargets.affordableAdd_inFlight_directional`

**Priority:** P1 — **Kind:** model correction/refinement — **Feasibility:**
medium (touches E37) — **Fidelity risk:** low.

**Statement shape.**

```lean
/-- Pending value of HTLCs offered in one direction only.  BOLT 2
`max_htlc_value_in_flight_msat` caps "outstanding HTLCs offered by the remote
node", not both directions. -/
def pendingHtlcValueFor (c : Channel) (dir : Direction) : Nat :=
  ((c.htlcs.filter (fun h =>
      (h.state = .offered ∨ h.state = .received) ∧ h.direction = dir)).map
    (fun h => h.amount.val)).sum

theorem pendingHtlcValueFor_le_pendingHtlcValueOf (c : Channel) (dir : Direction) :
    pendingHtlcValueFor c dir ≤ pendingHtlcValueOf c

/-- The BOLT-correct guard.  `AffordableAdd` is kept as the stronger,
over-rejecting predicate. -/
structure AffordableAddDirectional (c : Channel) (dir : Direction) (amount : Msat)
    (cltvExpiry : Height) : Prop where
  positive : 0 < amount.val
  cltvBelowMaximum : cltvExpiry < MAX_CLTV_EXPIRY
  atLeastHtlcMinimum : (receiverParams c dir).htlcMinimum.val ≤ amount.val
  fitsOffered : amount.val ≤ (offeredBalance c dir).val
  leavesReserve :
    offeringReserveSat c dir * Msat.MSAT_PER_SAT + amount.val ≤
      (offeredBalance c dir).val
  withinInFlight :
    pendingHtlcValueFor c dir + amount.val ≤ (receiverParams c dir).maxHtlcValue.val

theorem affordableAdd_implies_directional
    (h : AffordableAdd c dir amount cltv) : AffordableAddDirectional c dir amount cltv

/-- Strictness: the old guard rejects an add LDK accepts. -/
theorem directional_strict_counterexample :
    ∃ (c : Channel) (amount : Msat) (cltv : Height),
      AffordableAddDirectional c .remote amount cltv ∧
      ¬ AffordableAdd c .remote amount cltv
```

**Hypotheses.** For the strictness witness: `c` has exactly one pending
local-offered HTLC of 100 msat; `c.localEndpoint.params.maxHtlcValue = 100`;
both settled balances 1000 msat; reserves 0; `htlcMinimum = 0`; `cltv <
MAX_CLTV_EXPIRY`; the added remote amount is 1 msat. Then the old guard sees
`pendingHtlcValueOf c + 1 = 101 > 100`, while the directional guard sees
`pendingHtlcValueFor c .remote + 1 = 1 ≤ 100`.

**Non-vacuity.** The same witness proves the new predicate is satisfiable
(`AffordableAddDirectional` holds) and the old one is not. The converse
inclusion `AffordableAdd → AffordableAddDirectional` is proved by
`pendingHtlcValueFor_le_pendingHtlcValueOf`, so the refinement is not a
vacuous disjunction.

**Why faithful.** BOLT 2 `:739-742` and `:2829`/`:2850` are explicit that the
cap is on HTLCs offered by the remote; LDK implements exactly that filter at
`channel.rs:5854-5870`.

**Weakening/assumption flags.** This **weakens** `AffordableAdd.withinInFlight`
(the new guard accepts more). Keep the old theorem
`updateAddHtlc_inFlight_le` and restate it directionally; do not delete the old
`AffordableAdd` or its E37 bridge. The coordinated change must update
`affordableAdd_implies_e37` (`StateTransitionTargets.lean:357-364`) and
`updateAddHtlc_inFlight_le` (`:543-548`), and must add the strictness
counterexample so the weakening is visible in the theorem index rather than
hidden.

### T3. `LnLean.Proofs.Channel.StateTransitionTargets.updateAdd_respects_maxAcceptedHtlcs`

**Priority:** P1 — **Kind:** model extension — **Feasibility:** medium —
**Fidelity risk:** low.

**Statement shape.**

```lean
structure ChannelParams where
  ...
  /-- BOLT 2 `max_accepted_htlcs`; must be in `[1, 483]`. -/
  maxAcceptedHtlcs : Nat := 483

def pendingHtlcCountFor (c : Channel) (dir : Direction) : Nat :=
  (c.htlcs.filter (fun h =>
    (h.state = .offered ∨ h.state = .received) ∧ h.direction = dir)).length

/-- Added to `AffordableAddDirectional` (or to `AffordableAdd` after the T2
migration). -/
withinAcceptedCount :
  pendingHtlcCountFor c dir + 1 ≤ (receiverParams c dir).maxAcceptedHtlcs

theorem updateAdd_respects_maxAcceptedHtlcs
    {hashFn : ByteArray → ByteArray} {c c' : Channel}
    {dir : Direction} {amount : Msat} {ph : PaymentHash} {cltv : Height}
    (hstep : UpdateStep hashFn c (.addHtlc dir amount ph cltv) c') :
    pendingHtlcCountFor c' dir ≤ (receiverParams c dir).maxAcceptedHtlcs
```

Also apply the same guard in `HtlcBook.add` (`Channel/HTLC.lean:869-873`), and
prove `HtlcBook.WF` includes `1 ≤ maxAcceptedHtlcs ∧ maxAcceptedHtlcs ≤
channelMaxHtlcs channelType`, where `channelMaxHtlcs` is 483 or 114
(`chan_utils.rs:60-72`; LDK `channel.rs:4253-4261`, `:5271-5274`). If the model
does not carry a channel type, record `≤ MAX_ACCEPTED_HTLCS` as an explicit
simplification rather than an LDK-exact bound.

**Hypotheses.** The step already carries `hphase = normal` and the affordability
guard. Add `WF` for the negotiated bound. For the rejection witness, use
`maxAcceptedHtlcs = 1` and a channel with one pending HTLC in the same
direction.

**Non-vacuity.** Positive witness: `maxAcceptedHtlcs = 483`, empty channel,
one add accepted; count 1 ≤ 483. Rejection witness: `maxAcceptedHtlcs = 1`,
one pending HTLC, second add fails the count guard. LDK’s 483 cap is enforced at
open/accept, not just at add, so the `WF` field is essential.

**Why faithful.** BOLT 2 `:2849-2852` and LDK `channel.rs:5860` make the count
bound explicit; the field is already on the wire (`Messages.lean:112,122,151`)
but missing from the negotiated `ChannelParams`.

**Weakening/assumption flags.** Adding a field with default 483 silently gives
every existing construction site a 483 cap; this is acceptable only if
`ChannelParams.WF` rejects 0 and values above the channel-type bound. That bound
is not universally 483: `chan_utils.rs:60-72` gives 114 for zero-fee-commitment
channels. `ChannelParams` currently has `anchorOutputs` but no zero-fee flag, so
either carry the bound explicitly or state the 483 simplification. Do not add
the field without the `WF` invariant, or the model will accept channels LDK
rejects.

### T4. `LnLean.Proofs.Channel.StateTransitionTargets.updateFulfill_stores_preimage`

**Priority:** P2 — **Kind:** model extension/refinement — **Feasibility:**
medium — **Fidelity risk:** low.

**Statement shape.**

```lean
structure HTLC where
  direction : Direction
  amount : Msat
  paymentHash : PaymentHash
  cltvExpiry : Height
  state : HTLCState
  /-- The preimage learned at fulfilment; `none` while pending. -/
  preimage : Option Preimage := none

/-- Preimage-recording variant; `UpdateStep.update_fulfill_htlc` uses this. -/
def fulfillHtlcAtWithPreimage (c : Channel) (i : Nat) (p : Preimage) : Channel := ...

theorem fulfillHtlcAtWithPreimage_fulfilled_has_preimage
    (c : Channel) (i : Nat) (h : HTLC) (p : Preimage)
    (hi : c.htlcs[i]? = some h) (hp : h.isPending) :
    ∃ h', (fulfillHtlcAtWithPreimage c i p).htlcs[i]? = some h' ∧
      h'.state = .fulfilled ∧ h'.preimage = some p

theorem fulfillHtlcAtWithPreimage_ledger
    (c : Channel) (i : Nat) (h : HTLC) (p : Preimage) (fee : Msat)
    (hi : c.htlcs[i]? = some h) (hp : h.isPending) :
    ledgerValue (fulfillHtlcAtWithPreimage c i p) fee = ledgerValue c fee
```

**Hypotheses.** The `UpdateStep` constructor keeps `p.Valid` and
`hashFn p.bytes = h.paymentHash.bytes` (`State.lean:428-432`). The state lemma
needs only the lookup and pending hypotheses. Add a bridge
`toHtlcRecord : HTLC → Option Security.HtlcRecord` that preserves
`paymentHash`, `preimage`, and `state`, and prove
`fulfillHtlcAtWithPreimage_preimage_sound` from
`Security.HtlcRecord.fulfill_sound`.

**Non-vacuity.** Take a 32-byte `p` with `hashFn p.bytes = ph`, a pending
received HTLC with `paymentHash = ph`, and the existing
`UpdateStep.update_fulfill_htlc` witness. The post-state stores `some p`; the
current `HTLC` has no field, so the current model cannot state this witness at
all.

**Why faithful.** BOLT 2 `update_fulfill_htlc` carries the preimage
(`Messages.lean:208-212`), and LDK’s claim path uses it
(`channelmanager.rs:10881-10903`). Storing it in the channel state is the
minimal refinement needed to connect `LN-HT-001` to the state machine.

**Weakening/assumption flags.** Adding a field to `HTLC` changes many
construction sites and may change `BEq`/`Repr` output. Keep the old
`fulfillHtlcAt` and prove the new variant has the same state/balance effect, so
existing theorems and witnesses are preserved. Do not claim preimage secrecy or
hash-function security; this is a state-refinement target only.

### T5. `LnLean.Proofs.PhaseC3.Forwarding.ForwardPair.settle_delta_eq_fee`

**Priority:** P1 — **Kind:** new cross-channel model extension — **Feasibility:**
medium — **Fidelity risk:** medium-high (explicit linkage assumptions).

**Statement shape.**

```lean
namespace LnLean.Proofs.PhaseC3.Forwarding

structure ForwardPair where
  inbound : Channel
  outbound : Channel
  inIdx : Nat
  outIdx : Nat
  inHtlc : HTLC
  outHtlc : HTLC
  fee : Nat
  in_lookup : inbound.htlcs[inIdx]? = some inHtlc
  out_lookup : outbound.htlcs[outIdx]? = some outHtlc
  in_received : inHtlc.direction = .remote
  out_offered : outHtlc.direction = .local
  sameHash : inHtlc.paymentHash = outHtlc.paymentHash
  amount_link : inHtlc.amount.val = outHtlc.amount.val + fee
  out_le_in : outHtlc.amount.val ≤ inHtlc.amount.val
  pending_in : inHtlc.isPending
  pending_out : outHtlc.isPending

/-- Settling both sides increases the node's local balance across the pair by
exactly the forwarding fee.  The outbound debit happened at add time. -/
theorem ForwardPair.settle_delta_eq_fee (p : ForwardPair) :
    (fulfillHtlcAt p.inbound p.inIdx).balance.localBalance.val +
      (fulfillHtlcAt p.outbound p.outIdx).balance.localBalance.val =
    p.inbound.balance.localBalance.val +
      p.outbound.balance.localBalance.val + p.fee

/-- A failed outbound HTLC refunds the offering side; the settle path above is
the only fee-earning path. -/
theorem ForwardPair.fail_outbound_refunds (p : ForwardPair) :
    (failHtlcAt p.outbound p.outIdx).balance.localBalance.val =
      p.outbound.balance.localBalance.val + p.outHtlc.amount.val
```

A full-lifecycle corollary composes `settle_delta_eq_fee` with
`balanceVal_updateAddHtlc` (`StateTransitionTargets.lean:282-292`) to show that
starting from the pre-add outbound channel, the net local balance change is
`fee`.

**Hypotheses.** The `ForwardPair` fields are the linkage assumptions: one
inbound received HTLC, one outbound offered HTLC, same payment hash, both
pending, `inbound = outbound + fee`, and `outbound ≤ inbound`. For the
full-lifecycle version, add `AffordableAdd outbound0 .local aOut cltv` and
`p.outbound = updateAddHtlc outbound0 .local aOut ph cltv`.

**Non-vacuity.** Inbound 110 msat, outbound 100 msat, fee 10 msat, both
balances 1000 msat, reserves 0. After settle, inbound local +110 and outbound
local unchanged; the sum increases by 110 = 100 + 10. Boundary witness:
100/100/0. Counterexample/restriction: outbound 110, inbound 100 would require
`fee = -10`; LDK permits this for intercepted HTLCs and reports
`total_fee_earned_msat = None` (`channelmanager.rs:10912-10915`), so
`ForwardPair` deliberately models only **fee-known, single-in/single-out**
forwards.

**Why faithful.** It is the channel-state version of LDK’s
`claimed - forwarded` identity (`channelmanager.rs:10910-10911`) and the
persisted `inbound = outbound + fee` identity
(`forwarding_store.rs:248-249`), restricted to the cases LDK actually records.

**Weakening/assumption flags.** `sameHash` is necessary but not sufficient for
a real forward: LDK keys the record by `(channel_id, htlc_id)`, and duplicate
payment hashes can exist. The pair must be an explicit **assumption-carrying**
model, not a derivation from wire data. Do not claim atomicity or rollback:
there is no multi-channel transition relation yet. Do not drop `out_le_in`;
without it the “fee” is negative and the LDK record path is not applicable.

### T6. `LnLean.Proofs.PhaseC3.Forwarding.forwardStats_fee_attributed_to_incoming`

**Priority:** P2 — **Kind:** model extension — **Feasibility:** high —
**Fidelity risk:** low.

**Statement shape.**

```lean
structure ChannelForwardingStats where
  inboundCount : Nat
  outboundCount : Nat
  inboundAmount : Nat
  outboundAmount : Nat
  feeEarned : Nat
  skimmedFee : Nat
  onchainClaims : Nat

def applyForward (inStats outStats : ChannelForwardingStats)
    (f : ForwardPair) (skim : Nat) (claimedOnchain : Bool) :
    ChannelForwardingStats × ChannelForwardingStats := ...

theorem forwardStats_fee_attributed_to_incoming
    (inStats outStats : ChannelForwardingStats) (f : ForwardPair)
    (skim : Nat) (claimedOnchain : Bool)
    (hskim : skim ≤ f.fee)
    (hsub : inStats.skimmedFee ≤ inStats.feeEarned) :
    let (i', o') := applyForward inStats outStats f skim claimedOnchain
    i'.inboundCount = inStats.inboundCount + 1 ∧
    i'.inboundAmount = inStats.inboundAmount + f.inHtlc.amount.val ∧
    i'.feeEarned = inStats.feeEarned + f.fee ∧
    i'.skimmedFee = inStats.skimmedFee + skim ∧
    i'.skimmedFee ≤ i'.feeEarned ∧
    o'.outboundCount = outStats.outboundCount + 1 ∧
    o'.outboundAmount = outStats.outboundAmount + f.outHtlc.amount.val ∧
    o'.feeEarned = outStats.feeEarned ∧
    o'.onchainClaims = outStats.onchainClaims + (if claimedOnchain then 1 else 0)
```

**Hypotheses.** `skim ≤ fee` captures “skim is a share of the total, not an
addition” (`forwarding.rs:122-126`). `claimedOnchain` is a parameter matching
`claim_from_onchain_tx`. For a `u64` model, add `saturating_add` equivalence
and no-overflow hypotheses.

**Non-vacuity.** 110/100/10 with `skim = 2`: inbound fee 10, inbound skim 2,
outbound fee 0, outbound on-chain count 1 when `claimedOnchain = true`; this is
exactly the test at `forwarding_store.rs:1597-1663` and the e2e attribution at
`:1907-1929`.

**Why faithful.** It transcribes the two directional stat updates at
`forwarding_store.rs:253-289` and the documented attribution at
`forwarding.rs:167-182`.

**Weakening/assumption flags.** Do not model `total_fee_earned_msat` as
`feeEarned + skimmedFee`; skim is already inside `feeEarned`. If the model
carries `Option` fees for unknown cases, preserve the `None` branch rather than
defaulting to 0; LDK distinguishes “unknown” from “zero” in some paths.

### T7. `LnLean.Proofs.PhaseC3.Forwarding.recordForward_eligible_sound`

**Priority:** P2 — **Kind:** model extension (LDK Node client semantics) —
**Feasibility:** medium — **Fidelity risk:** low-medium.

**Statement shape.**

```lean
structure ForwardCandidate where
  prevHtlcs : List HTLCLocator
  nextHtlcs : List HTLCLocator
  totalFeeEarned : Option Nat
  prevHtlcId : Option Nat

def Eligible (c : ForwardCandidate) : Prop :=
  c.prevHtlcs.length = 1 ∧ c.nextHtlcs.length = 1 ∧
    c.totalFeeEarned.isSome ∧ c.prevHtlcId.isSome

def recordForward (s : ForwardStore) (c : ForwardCandidate) : ForwardStore :=
  if Eligible c then insertRecord s c else s

theorem recordForward_eligible_sound
    (s s' : ForwardStore) (c : ForwardCandidate)
    (h : recordForward s c = s') (hne : s' ≠ s) :
    Eligible c

theorem recordForward_ineligible_noop
    (s : ForwardStore) (c : ForwardCandidate) (h : ¬ Eligible c) :
    recordForward s c = s

theorem recordForward_replay_idempotent
    (s : ForwardStore) (c : ForwardCandidate) (h : Eligible c) :
    recordForward (recordForward s c) c = recordForward s c
```

Add `forwardedPaymentId : ChannelId → Nat → ForwardedPaymentId` with the
32-byte channel id and 8-byte htlc id encoding, and prove it is injective for
htlc ids below `2 ^ 64`.

**Hypotheses.** `ForwardCandidate` carries the LDK guard inputs. `ForwardStore`
must include a replay-marker set keyed by `forwardedPaymentId`, a details map
(populated only in `Detailed` mode), and per-channel stats. `Eligible` is the
exact conjunction at `forwarding_store.rs:220-233`.

**Non-vacuity.** Positive witness: single in/out, `fee = Some 10`, `prevHtlcId
= Some 7`; `recordForward` inserts one record. Replay witness: call twice; the
second call sees the marker and leaves the store unchanged, matching
`forwarding_store.rs:1632-1633`. Negative witnesses: two inbound HTLCs and
`totalFeeEarned = None`; both leave the store unchanged, matching
`:1708-1766`.

**Why faithful.** It mirrors the public LDK Node client policy, not a BOLT
consensus rule. The tests and e2e path cited above assert exactly these
behaviors.

**Weakening/assumption flags.** This is a **client-semantics** model. Do not
add it to the protocol catalog as if it were a Lightning consensus theorem. Do
not model “persist before event” as a consequence of `recordForward`; that is a
separate ordering property (`event.rs:1958-1978`) and needs an event-queue model
or an external assumption.

## 5. Assumptions, counterexamples, and non-vacuity risks

### Counterexamples that must be preserved or added

* **Ceiling-vs-floor fee.** New 1500/1000 witness: Lean `Hop.ofEdge` = 2,
  LDK `compute_fees` = 1 (`Route.lean:92-97`; `router.rs:2639-2642`). Keep the
  existing `ofEdge_rounding_counterexample` (`RouteBlindingProps.lean:252-258`)
  as a separate inverse-amount gap; merging the two would hide one of them.
* **Direction-blind in-flight guard.** One pending local-offered 100 msat,
  local `maxHtlcValue = 100`, remote add 1 msat: Lean rejects, LDK/BOLT accept.
  This applies to both `Channel.AffordableAdd.withinInFlight`
  (`State.lean:315-316`) and `HtlcBook.add` (`Channel/HTLC.lean:869-873`).
* **Unbounded accepted-HLTC count.** With `MAX_ACCEPTED_HTLCS` unused and no
  `ChannelParams.maxAcceptedHtlcs`, a sequence of adds can exceed 483; LDK
  rejects at `channel.rs:5860`.
* **Underpay / negative fee.** LDK explicitly permits paying out more than it
  took in for intercepted HTLCs and reports `None` (`channelmanager.rs:10912-10915`);
  a theorem asserting `inbound ≥ outbound` unconditionally is false for that
  case. `ForwardPair.out_le_in` is a deliberate restriction to recorded
  forwards.
* **Unknown fee / multi-HTLC / missing id.** LDK skips these entirely
  (`forwarding_store.rs:220-233`; test `:1708-1766`). Any record model must have
  a “no record” branch, not a default-zero record.
* **Replay.** Recording the same `(channel_id, htlc_id)` twice must not double
  count (`forwarding_store.rs:236-241,315-322`; test `:1632-1633`).

### Hidden assumptions and scope boundaries

* **`Nat` vs `u64`.** Lean accounting is unbounded; LDK uses `checked_mul` /
  `checked_add` (`router.rs:2640-2641`), `checked_sub`
  (`channelmanager.rs:10910-10911`), and `saturating_add`
  (`forwarding_store.rs:249`). Exact theorems need explicit no-overflow or
  saturation hypotheses; otherwise they are not LDK-faithful at the top of the
  range.
* **Per-channel ledger is conditional.** `updateStep_preserves_ledger`
  (`StateTransitionTargets.lean:425-442`) assumes
  `ledgerValue c fee = c.fundingValue.val`. It is not a global invariant and
  says nothing about a second channel.
* **Preimage/hash model.** `UpdateStep.update_fulfill_htlc` uses a
  caller-supplied `hashFn` and `p.Valid` (`State.lean:428-432`). Do not upgrade
  this to cryptographic soundness; `HtlcRecord.fulfill_sound`
  (`Security/Invariants.lean:220-229`) is conditional on the same hash
  relation.
* **Route first-hop convention.** `Route.totalFee` includes the first hop’s
  advertised fee; `forwardFeeTotal` drops it (`CrossChannelRouting.lean:154-157,
  303-321`). LDK `Path::fee_msat` excludes the last hop
  (`router.rs:776-785`). Every new fee theorem must state which convention it
  uses; the existing note is at `CrossChannelRouting.lean:75-84`.
* **Liquidity/capacity are parameters.** `LiquidityModel` is a structure field,
  not an axiom (`CrossChannelRouting.lean:379-382`), and `FeasiblePath` attests
  graph membership and liquidity (`:387-407`). Do not confuse these with actual
  channel balances; there is no derivation from `Channel.State`.
* **ForwardPair is assumption-carrying.** `sameHash`, `amount_link`, and
  `out_le_in` are not derived from the wire. In particular, equal payment
  hashes do not prove the same payment (duplicate hashes are possible), and LDK
  keys on `(channel_id, htlc_id)`, not on the hash.
* **Failure reasons are cryptographic/client facts.** `UpdateFailHtlc.reason`
  is re-encrypted per incoming channel (`channelmanager.rs:15303-15333`), and
  blinded failures may be substituted. `OnionError.code` is a model enum
  (`Onion.lean:443-446`), not the wire code. A theorem that “the code
  propagates” needs a codec/crypto interface and BOLT 4 TLV semantics.
* **Persistence/event ordering is LDK Node client policy.** `record_forward`
  before `add_event` (`event.rs:1958-1978`) is an implementation ordering, not
  a protocol law. It should be an external assumption or a separate client
  model, not a corollary of the channel state machine.
* **On-chain/skim accounting.** `skimmed_fee_msat` is a subset of
  `total_fee_earned_msat` (`forwarding.rs:122-126,174-178`); adding them
  double-counts. `onchain_claims_count` belongs to the outgoing channel
  (`:179-182`, `forwarding_store.rs:262,281`).
* **`max_accepted_htlcs` is channel-type dependent.** LDK’s bound is 483 for
  non-zero-fee-commitment channels and 114 for zero-fee-commitment channels
  (`chan_utils.rs:60-72`). `MAX_ACCEPTED_HTLCS = 483` is only a ceiling; a
  theorem that assumes 483 for every channel is weaker than LDK’s actual guard
  and must say so.

### Existing witnesses that must not be weakened

* `CrossChannelRouting.demoPlan` and `demoPlan_route_valid`
  (`CrossChannelRouting.lean:599-619`) witness a non-vacuous feasible path.
* `ofEdge_rounding_counterexample` (`RouteBlindingProps.lean:252-258`).
* `cross_direction_duplicate_tagged` and the `LN-HT-004` counterexample family
  (`docs/OPEN-ISSUES.md:64`).
* `duplicate_htlc_count_coverage_not_binding`
  (`ProtocolCoverageTargets.lean:195-213`), which shows coverage is not
  binding on the HTLC set.
* The `literal_round_fold_refuted` / `literal_revoke_fold_refuted` family
  (`docs/OPEN-ISSUES.md:72`), which constrain any “fold the update layer into
  `Step`” proposal.

## 6. Wave-13 recommendation

**Verdict: a small safe fee-refinement lane exists, but the core forwarding
lane does not.**

* **Implement now (safe, additive, wave 13): T1.**
  `Hop.ofEdgeFloor` + equality/monotonicity/divisibility + the 1500/1000
  counterexample. It touches no existing type, preserves `Hop.ofEdge`, and
  closes a real economic-accounting fidelity gap. It is the only target in this
  report that can be landed without a coordinated migration.
* **Defer to wave 14 with maintainer sign-off: T2, T3, T4.**
  These change `ChannelParams`, `Channel.HTLC`, `AffordableAdd`, and
  `UpdateStep`, and T2 additionally touches the E37 exposure theorem and the
  axiom audit. They should be one coordinated migration PR that keeps the old
  `AffordableAdd`/`updateAddHtlc_inFlight_le` theorems (restated directionally
  where needed) and adds the strictness counterexample. They are fidelity/DoS
  fixes, not a forwarding model.
* **Defer to a dedicated wave-14 design: T5, T6, T7.**
  A real forwarding model needs a new cross-channel module with explicit
  linkage assumptions, stable `(channel_id, htlc_id)` keys, stats, records, and
  replay. It should not be bolted onto `CrossChannelRouting`: that module’s
  elaboration peak was already a 12–19 GiB / SIGKILL problem before `CCR01`
  brought it to ~1.7 GiB (`agents/TODO-REPAIR.md:54-57`). Keep the new module
  separate and do not add catalog rows until the targets are proved and
  anchored.
* **Treat as external/human barrier: failure-reason propagation, persistence
  ordering, replay-store durability.**
  The failure path needs a BOLT 4 failure-packet codec with per-channel shared
  secrets and TLV attribution (`channelmanager.rs:10001-10115,15303-15333`;
  `OnionError.lean:59-69`), and the persistence ordering is LDK Node client
  policy (`event.rs:1958-1978`). These are not safe wave-13 Lean targets; they
  need an explicit interface/spec and a human decision about what is being
  assumed.

**Do not claim** that `LN-HT-001`/`LN-HT-002` cover forwarding, or that
`CrossChannelRouting` covers forwarding fees. Neither does. There is no P0
consensus-safety lane in this surface; the P1 items are economic-accounting and
interop fidelity, plus the 483-HTLC exposure bound.

## 7. Evidence and commands

Read-only inputs used:

* Lane brief: `agents/briefs/wave13-review/R07.md`.
* Protocol/context: `docs/AGENT-PROTOCOL.md`, `docs/OPEN-ISSUES.md`,
  `docs/THEOREM-INDEX.md`, `docs/TRACEABILITY.md`, `agents/TODO-REPAIR.md`,
  `agents/reports/swarm12/S12-POST-INTEGRATION-AUDIT.md`,
  `agents/reports/wave13-review/LDK-REFS.md`.
* Lean surface: `LnLean/Proofs/PhaseC3/CrossChannelRouting.lean`,
  `LnLean/Proofs/PhaseC3/OnionError.lean`,
  `LnLean/Proofs/PhaseC3/EndToEndConservation.lean`,
  `LnLean/Channel/State.lean`, `LnLean/Channel/HTLC.lean`,
  `LnLean/Channel/Types.lean`, `LnLean/Channel/Fee.lean`,
  `LnLean/Routing/Route.lean`, `LnLean/Routing/Onion.lean`,
  `LnLean/Proofs/Channel/StateTransitionTargets.lean`,
  `LnLean/Proofs/Channel/HTLCProps.lean`,
  `LnLean/Proofs/ProtocolCoverageTargets.lean`,
  `LnLean/Proofs/Routing/RouteBlindingProps.lean`,
  `LnLean/Proofs/WaveE/E26.lean`, `LnLean/Proofs/WaveE/E37.lean`,
  `LnLean/Security/Invariants.lean`, `LnLean/Protocol/Messages.lean`.
* LDK Node: `src/payment/forwarding.rs`, `src/payment/forwarding_store.rs`,
  `src/event.rs`.
* LDK Server: `ldk-server/src/api/get_forwarded_payment_details.rs`,
  `ldk-server/src/api/list_forwarded_payments.rs`,
  `ldk-server/src/api/get_channel_forwarding_stats.rs`,
  `e2e-tests/tests/e2e.rs`.
* `rust-lightning`: `lightning/src/routing/router.rs`,
  `lightning/src/ln/channel.rs`,
  `lightning/src/ln/channelmanager.rs`,
  `lightning/src/ln/onion_utils.rs`.
* BOLT 2: `refs/bolts/02-peer-protocol.md:739-742, 2822-2852`.

Commands used (read-only):

```text
rg -n "forward|Forward|Fee|fee|HTLC|htlc" docs agents LnLean
sed -n '...' <Lean file>        # exact declaration/hypothesis inspection
sed -n '...' <LDK file>         # exact behavior/test inspection
git -C /home/ubuntu/ln-lean-repair status --short
```

No Lean build, no cargo test, and no code/doc edits were performed. Only this
report was written. The working tree already contained untracked
`agents/briefs/wave13-review/` and `agents/reports/wave13-review/` entries;
nothing else was modified.
