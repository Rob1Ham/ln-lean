# R32 — Wave-13 synthesis: repair, assurance, and deferred extensions

**Status:** read-only synthesis. The only file written by this lane is this
report. No Lean, docs, scripts, tests, vendor, branch, or other-report changes
were made; no build and no network command was run.

**Pins:** LDK Node `fa123fed131e27ecc420b77fa7086fcf1ddaebb8`; LDK Server
`c17dc11dde38f88c53457039ddf30c6b90a63ba2` (both in
`/tmp/opencode/ldk-refs/`); rust-lightning `fe4900930c6bd5786ec4203274d7cf312776a5a6`;
BOLTs `1aadb719b4007c4cea0ba6e36b08c4fb53788dee`. LDK Server's own
`ldk-server/Cargo.toml:16` pins `ldk-node 179b4b2…`, which is **not** the
review clone (`fa123fed…`); every server-conformance statement inherits that
pin mismatch.

**Evidence labels.** `[V]` means this lane re-checked the declaration or the
pinned line directly. `[R]` means the claim is taken from an R01–R31 report and
was not independently re-derived. The gap matrix deliberately separates a
*false consumer claim* from a *narrower-than-BOLT model* and from *missing
coverage*; conflating those three was the most common defect in the wave-13
reports.

---

## 1. Scope and current Lean surface

The catalog is 51 rows, 51 marked `proved`, 0 `statementOnly`
(`LnLean/Proofs/Obligations.lean:458-459`). The row count is not the coverage
count:

| Measure | Value | Evidence |
|---|---:|---|
| Catalog rows | 51 | `Obligations.lean:458` `[V]` |
| Target occurrences in `leanTarget` strings | 294 | direct parse of `Obligations.lean` `[V]` |
| Unique target declarations | 282 | direct parse `[V]` |
| Duplicate target names | 12 | all are `EcdsaConcreteTargets`/`EcdsaDomainTargets` names shared by `LN-L1-001` and `LN-L1-004` `[V]` |
| `#print axioms` commands | 393 | `LnLean/Proofs/PhaseC3/AxiomAudit.lean:117-570` `[V]` |
| `auditedTheorems` registry names | 435 | `AxiomAudit.lean:579-1016`, length theorem `:1018` `[V]` |
| Registry names without a print command | 42 | set difference `[V]` |
| Unique catalog targets without a print command | 72 | set difference `[V]` |
| Unique catalog targets absent from `auditedTheorems` | 35 | set difference `[V]` |
| `provedDeclarations` snapshot in `Traceability` | 282 | `LnLean/Proofs/Traceability.lean:335` `[V]` |

The current proof surface is therefore "51 named rows with 282 distinct
declarations", not "294 distinct theorems", and "393 printed axiom audits over
a 435-name registry", not "435 audited theorems". `auditedTheorems_length`
checks only the literal list length; it ties neither the registry to the print
commands nor the catalog to either (`R31:135-137`).

The relevant carriers are split across layers:

* `LnLean/Channel/State.lean` — executable `updateAddHtlc`, the
  `AffordableAdd` predicate, and the pooled `pendingHtlcValueOf`
  (`:266-269`, `:300-316`).
* `LnLean/Proofs/Payment/LiquidityProps.lean` — `reserveMsat` (`:110-111`),
  `availableOutbound` (`:152-153`), and the executable `addHtlc?`
  (`:376-384`). Its guards are directionally correct for the in-flight cap but
  inverted for the reserve.
* `LnLean/Channel/Commitment.lean` — legacy `commitmentOutputs` and
  `commitmentPairOfBalances` (`:380-410`), plus the rich `CommitmentTx` model
  with gross and net output paths (`outputsUnsorted`, `outputsNet`,
  `htlcOutputNet`).
* `LnLean/Proofs/Channel/CommitmentOrderTargets.lean:89-108` — the catalog
  `output_ordering` theorem, which is about `CommitmentTx`, not the legacy
  `commitmentOutputs`.
* `LnLean/Protocol/Peer.lean:127-139` — non-idempotent `advanceReceived`;
  `LnLean/Proofs/Protocol/ChannelReestablishProps.lean:386-405` — the
  duplicate-advance theorem and the numbered `advanceReceivedNumbered`
  refinement.
* `LnLean/Protocol/Peer.lean:213` (receipt dispatcher) and
  `LnLean/Proofs/Protocol/ChannelReestablishProps.lean:282-295` (extracted
  non-handshake branch, `c.advanceReceived m`).
* `LnLean/Routing/Route.lean:325-327` — per-hop `routeValid`, with no
  adjacency condition.
* `LnLean/Proofs/Payment/KeysendProps.lean:252-255`, `:300-301` — a retry that
  resets any state, including `succeeded`.

Not modelled or not production-wired: payment store / duplicate admission,
route capacity and scoring, zero-fee and shared-anchor commitments, splice and
dual-funding funding mutation, BOLT 12/async/trampoline wire state, LDK Server
API/macaroon/status semantics. These are named in the matrix but are not
wave-13 repair targets.

---

## 2. LDK datapoints (with `file:line`)

All paths below are relative to `/tmp/opencode/ldk-refs/`, except
`refs/rust-lightning` and `refs/bolts`, which are in this repository. `[V]`
means the line was re-read in the pinned tree.

| # | Datapoint | Pinned evidence | Consequence for this report |
|---:|---|---|---|
| D1 | `channel_reserve_satoshis` is the reserve the **peer** must keep; the local side applies the remote endpoint's advertised value | BOLT 2 `refs/bolts/02-peer-protocol.md:730-741`, `:884-887` `[V]`; LDK `refs/rust-lightning/lightning/src/ln/channel.rs:6552-6605` `[V]` | `LiquidityProps.reserveMsat` uses the wrong endpoint; `ReserveProps.localReserveSat` and `State.offeringReserveSat` use the correct one. |
| D2 | `max_htlc_value_in_flight_msat` bounds the value **offered by the sender in that direction**, not the sum of both directions | BOLT 2 `02-peer-protocol.md:739-742` `[V]`; LDK `channel.rs:5854-5870` filters `!htlc.outbound` `[V]` | `State.pendingHtlcValueOf` is pooled; BOLT 2 and LDK are directional. |
| D3 | Route fees use truncating division | `refs/rust-lightning/lightning/src/routing/router.rs:2639-2642` `[V]` | `Hop.ofEdge` rounds up (`Route.lean:92-97`); no direct Lean-vs-LDK fee theorem exists. |
| D4 | A multi-part set completes when its total is **at least** `total_msat` | BOLT 4 `refs/bolts/04-onion-routing.md:383-385` `[V]` | Lean's `mppComplete`/`MppPayment.settle` require exact equality; over-strict, not false. |
| D5 | On an anchored commitment the funder pays the two 330-sat anchor outputs; the 1124 WU basis applies only to the zero-fee anchor form | BOLT 3 `refs/bolts/03-transactions.md:321-326` `[V]`; `refs/rust-lightning/lightning/src/ln/chan_utils.rs:280-283` `[V]` | `commitmentPairOfBalances` omits the 660-sat debit; the corrected constructor exists but is unused. |
| D6 | A duplicate keysend with the same payment hash is rejected while the stored payment is `Pending` or `Succeeded` | `ldk-node/src/payment/spontaneous.rs:67-73` `[V]` | `Keysend.retry` resets `succeeded` to `pending`; no payment-store admission predicate exists. |
| D7 | Unified sends treat several send failures as fatal and do not silently fall back | `ldk-node/src/payment/unified.rs:266-270`, `:331-345` `[V]` | The Lean dispatch model has no fatal-error class; a unified-send target would be a wave-14 extension. |
| D8 | Server `fail_for_id` writes `Failed` without a status/direction guard; node `bolt11_fail_for_id` does not restore a prior success | `ldk-server/ldk-server/src/api/bolt11_fail_for_id.rs` `[R]`; `ldk-node/src/payment/bolt11.rs:477-531` `[V]` | A projection from `PaymentSession.settle` would be contradicted by the API; the model's absorbing `settle` is not the server transition. |
| D9 | Server's ldk-node dependency is `179b4b2…`, not the review pin `fa123fed…`; `claim_for_id` arity differs | `ldk-server/Cargo.toml:16` `[V]` | No server-conformance claim is source-grounded until the pins are aligned; this is an external/build decision. |
| D10 | Node announcements are admitted only for a known node | `refs/rust-lightning/lightning/src/routing/gossip.rs:1910-1938` `[V]` | The Lean canonical node layer is a separate model; no production pipeline is claimed. |
| D11 | Gossip direction is a first-class `(scid, direction)` record | `refs/rust-lightning/lightning/src/routing/gossip.rs:1031-1040` `[V]` | Canonical-layer coverage is faithful; the raw `Gossip.applyUpdate` remains a global clock (documented). |
| D12 | BOLT 3 ordering key is value, then script, then CLTV, with dust trimming | `refs/bolts/03-transactions.md:704-730` `[V]`; `:330-348` `[V]` | `CommitmentTx.outputs` implements this; legacy `commitmentOutputs` does not, and D12's counterexample must stay. |

---

## 3. Gap matrix

Status vocabulary: **false consumer claim** = the named wrapper/consumer
accepts or emits behaviour the protocol rejects (a counterexample exists);
**narrower model** = the Lean theorem is true of its carrier but the carrier
is deliberately narrower than BOLT/LDK; **missing carrier** = no object exists
on which to state the property; **definitional/restatement** = the theorem is
a projection or hypothesis restatement and must not be cited as an independent
safety result; **metadata** = count, traceability, or anchor defect.

| ID | Behaviour | Lean carrier and status | Evidence / counterexample | Severity | Lane |
|---|---|---|---|---|---|
| G01 | Local/remote reserve direction | **false consumer claim.** `reserveMsat` uses `localEndpoint` (`LiquidityProps.lean:110-111`); `reserveOf .local` inherits it (`:133-135`); `addHtlc?` input `:376-384`; `ReserveProps.localReserveSat` (`:103-104`) and `State.offeringReserveSat` (`:281-282`) are correct | Local reserve 0, peer reserve 1 sat, local balance 1000 msat, HTLC 1000 msat: `addHtlc?` returns `some`; BOLT 2 D1 rejects. `availableOutbound` reports 1000 msat spendable when the true value is 0. `[V]` for declarations; witness `[R19:281-283]` | P0 | W13-LIQ |
| G02 | Directional in-flight cap | **false consumer claim / narrower model.** `pendingHtlcValueOf` sums both directions (`State.lean:266-269`); `AffordableAdd.withinInFlight` uses it (`:315-316`); `D14.inFlightMsat` and `E37.pendingValue` have the same bug `[R]` | Remote-offered pending 600, new local 500, cap 1000: pooled guard rejects; BOLT 2 D2 and `LiquidityProps.addHtlc?` (directional `sumByDirection`) accept. `[V]` for state declarations; witness `[R19:287]` | P0 | W13-LIQ |
| G03 | In-flight counts only pending HTLCs | **false consumer claim.** `LiquidityProps.sumByDirection` (`:295-298`) sums terminal as well as pending entries | A settled 600-msat local HTLC plus a 500-msat add is rejected under a 1000 cap although nothing is in flight. `[R19:287]` | P1 | W13-LIQ |
| G04 | Full BOLT 2 add guard | **carrier split / missing refinement.** `addHtlc?` checks only cap and reserve, accepts amount 0, below `htlc_minimum`, and `cltv ≥ 500000000`; it prepends. `AffordableAdd` has the missing guards and `updateAddHtlc` appends. No theorem links the two | Concrete zero/min/CLTV witnesses are admitted by `addHtlc?`; `[R19:284,286]`. This is the same behaviour under two incompatible predicates | P1 | W13-LIQ |
| G05 | Funder pays anchor outputs | **false consumer claim.** `commitmentPairOfBalances` subtracts only `fee` (`Commitment.lean:387-398`); `waveF_f04_counterexample_660` proves output sum + fee = funding + 660; corrected `commitmentPairWithAnchorDebit` exists at `F04.lean:246` but has no production consumer | Witness: 60 000/40 000 split, fee 1000, anchors true → 100 660. `[V]` `F04.lean:222-226` | P0 | W13-ANCHOR |
| G06 | Single-anchor exception | **missing carrier.** `Commitment.commitmentOutputs` emits both anchors whenever `anchorOutputs = true` (`Commitment.lean:113-114`); `CommitmentTx.localAnchorOutput`/`remoteAnchorOutput` each emit their 330-sat output whenever the flag is true, with no single-anchor case (`:914-922`). No exact-presence theorem | `toLocalSat = 0`, `toRemoteSat = 50 000`, no HTLCs, dust 330 → model emits 660 sat of anchors; BOLT 3 emits one 330-sat output. `[R06:193]` | P0 | W14 (ANCHOR extension) |
| G07 | Net (second-stage) dust test in the consumed path | **narrower model / consumer mismatch.** `output_ordering` tests gross `amountSat` (`CommitmentOrderTargets.lean:89-108`); the exact net path `htlcOutputNet`/`outputsNet` exists (`Commitment.lean:951-970`) and has its own spec, but the legacy consumer reads gross value | Gross 1000, second-stage fee 167, dust 900: gross path keeps, net path trims. `[R06:194]` | P0 | W14 (ANCHOR consumer) |
| G08 | MPP completion at `≥ total_msat` | **narrower model.** `mppComplete` exact (`MPP.lean:144-146`); `MppPayment.settle` exact (`Security/Invariants.lean:441-446`); BOLT 4 D4 permits overpay | `parts = [120]`, `total = 100`: Lean `none`, protocol fulfil. `settle_requires_sum` is true of its carrier; do not call it false | P1 | W14 (PAY) |
| G09 | Numbered `commitment_signed` receipt is idempotent | **missing consumer.** `advanceReceivedNumbered` is idempotent (`ChannelReestablishProps.lean:395-405`), but `receive`'s non-handshake branch applies `advanceReceived` (`Protocol/Peer.lean:213`; extracted at `ChannelReestablishProps.lean:282-295`), so replaying the same message advances twice (`:386-390`) | Replay: old counter +2, numbered refinement +1. `[V]` | P0 | W13-STATE |
| G10 | Keysend retry does not reset a success | **false consumer claim.** `Keysend.retry` resets any state (`KeysendProps.lean:252-255`); `retry_pending` proves it for a succeeded record (`:300-301`) | Succeeded keysend → old retry `pending`; LDK D6 rejects the duplicate. `[V]` | P0 | W13-PAY |
| G11 | Duplicate send admission | **missing carrier.** No payment store, no `PaymentId`, no admission predicate; two `create` calls with the same preimage/hash both settle `succeeded` | Two identical keysends: both `settle .succeeded`; `settle_terminal` is per-record only. `[R12:166-168]` | P0 | W13-PAY |
| G12 | Route is chain-backed end-to-end | **false consumer claim.** `routeValid` checks each hop independently (`Route.lean:325-327`); no adjacency or edge-chain condition | Edges `0→1` and `2→3`; route hops `[1,3]` passes `routeValid` but is not a chain. `[V]` `Route.lean`; witness `[R16:205]` | P0 | W13-ROUTE |
| G13 | Fee rounding matches LDK | **narrower model.** `Hop.ofEdge` rounds up (`Route.lean:92-97`); LDK floors (D3). `ofEdge_rounding_counterexample` records the inverse direction | A direct floor/ceil separation witness is still missing. `[R16:208]` | P1 | W14 (ROUTE) |
| G14 | Route capacity, `htlc_maximum_msat`, scoring, in-flight liquidity | **missing carrier.** `routeValid` ignores capacity; `ChannelEdge` has no min/max HTLC fields; no scoring state; no `inflight_htlc_msat` | LDK `router.rs:380-397`, `:492-560`; BOLT 7 `:505-508` `[R16:206-220]` | P1 | W14 (ROUTE) |
| G15 | `update_fee` legality | **narrower model.** `Step.updateFee` only requires `phase = normal` (`State.lean:117-121`); `checkedFeeUpdate` is not wired in | Non-funder and arbitrary-feerate updates are valid `Step`s. `[R06:196]` | P1 | W14 (ANCHOR/FEE) |
| G16 | Zero-fee and `shared_anchor` commitments | **missing carrier.** No `zeroFee`/`commitmentVersion`/`sharedAnchor` field; no feerate-0 policy | BOLT 3 `:178-195`, `:305-311`; explicitly not modelled. `[R06:195]` | P1 | W14 (ANCHOR extension) |
| G17 | Stale snapshot restore | **definitional/restatement.** `Stale` is "misses a reachable later state"; `stale_snapshot_rolls_back` returns `h.2` (`PersistenceRecovery.lean:505-517`) and never applies `restore` | No theorem connects a stale snapshot to a restore result or to a latest-prefix selector. `[V]` | P1 | W13-STATE |
| G18 | Partial synchrony delivery | **definitional/restatement.** `PartiallySynchronous` is exactly `∀ m, gst ≤ send → DeliveredWithin …`; `partial_synchrony_delivers` is `hps m hm` (`Security/Invariants.lean:483-492`) | Without the hypothesis, `latency := fun _ => none` is a counterexample. `[V]` `Invariants.lean:483-492`; `[R31:130]` | P0 (claim) | W13-ASSURANCE |
| G19 | `channel_ready` as LDK readiness/usability | **definitional flag.** `channel_ready_gate` is the two-flag conjunction (`D18.lean:334`); `channelReady_reachable_without_fundingSigned` shows the separate state-machine path (`StateMachineProps.lean:381`); no confirmations/peer-connectivity fields | Must not be cited as `is_channel_ready`, `is_usable`, or splice readiness. `[R31:124-127]` | P1 | W13-ASSURANCE |
| G20 | Catalog/axiom counts | **metadata.** 294 occurrences vs 282 unique; 393 prints vs 435 registry; 72 catalog targets unprinted; 35 absent from registry; `auditedTheorems_length` checks only 435 | Direct set arithmetic in §1. `[V]`; `[R31:135-136]` | P0 | W13-ASSURANCE |
| G21 | Traceability checks declaration text/module | **metadata.** `proved_decls_in_snapshot` checks ID membership only; it never compares `DeclEntry.text`/`module` with `TargetEntry.text`/`modules` | Current data has 0 mismatches, but no kernel check preserves it. `[R31:137]` | P0 | W13-ASSURANCE |
| G22 | Anchor checker checks relevance | **metadata.** `scripts/verify-anchors.py:1-52` checks file existence and line bound only; `unanchored_rows=2` is a prose false positive at `docs/TRACEABILITY.md:11,74` | `LN-SEC-004` points at `handle_channel_reestablish`. `[R31:139]` | P1 | W13-ASSURANCE |
| G23 | Server conformance is source-grounded | **external/evidence defect.** Server pins ldk-node `179b4b2…` (`Cargo.toml:16`); review pin is `fa123fed…`; `claim_for_id` arities differ | Any server theorem is pin-blocked. `[V]` `Cargo.toml:16`; `[R24:178]` | P0 (server only) | External |
| G24 | API status does not regress | **narrower model / projection mismatch.** `PaymentSession.settle` is absorbing, but server `fail_for_id` writes `Failed` unconditionally and `PaymentSent` writes `Succeeded` without a guard | A succeeded BOLT 11 record becomes failed; cannot project `settle` to API status. `[R24:183]` | P1 | W14 (SERVER) |
| G25 | Unified send fatal-error class | **missing carrier.** No fatal-vs-retryable distinction; keysend fallback/duplicate handling is absent | LDK D7. `[R28]` | P1 | W14 (PAY/UNIFIED) |
| G26 | Splice and dual-funding funding mutation | **external/model change.** `Step` never changes funding (`StateTransitionTargets.lean:417` `step_fundingValue_eq`); adding a funding-changing constructor would falsify that theorem and `ConservedTransition` | Requires a sidecar model plus maintainer sign-off, not a wave-13 patch. `[V]` `:417`; `[R25,R26]` | P0 (external) | W14 / blocked |
| G27 | BOLT 12, async, trampoline, invoice wire | **missing carrier / external maturity.** Semantic invoice record and pre-bech32 codec only; no offer/async/trampoline state machine | `[R10,R11,R28]` | P2 | W14 (conditional) |
| G28 | Documentation drift | **metadata.** `Obligations.lean:76` still says "48-obligation catalog"; docs say "294 resolved targets" without "occurrences" | Direct read. `[V]` | P2 | W13-ASSURANCE |

**Deduplication note.** G01 and G03/G04 are the same "two admission predicates"
defect seen from the reserve, in-flight, and full-guard sides; they are kept
separate because they need separate witnesses and separate acceptance tests.
G05/G06/G07 are the anchor family but have different fixes (debit, exact
presence, net-dust consumer) and must not be collapsed into one "anchor" row.
G09/G10/G11 are all "replay/duplicate" issues but live on different carriers
(channel receipt, keysend record, payment store); only G09 is a channel-state
theorem.

---

## 4. Proposed targets

Eight targets are proposed: seven Lean theorems/definitions and one hybrid
assurance gate (its Lean half is a membership theorem; its runtime half is a
script, because "Lean actually printed this name" is not expressible as a
kernel proposition). None requires editing an existing theorem statement.

**Ranking (risk-adjusted):**

| Rank | Target | Lane | Type | Priority | Why |
|---:|---|---|---|---|---|
| 1 | T1 reserve direction + corrected outbound/inbound | W13-LIQ | model correction, additive | P0 | Live unsound acceptance; small proof; no external dependency |
| 2 | T2 directional pending in-flight | W13-LIQ | model correction, additive | P0 | Live false rejection; overlaps T1's carrier split |
| 3 | T4 chain-backed route | W13-ROUTE | additive predicate | P0 | Live false route-validity claim; witness already clear |
| 4 | T3 production anchor-debit consumer | W13-ANCHOR | integration of existing proof | P0 | Real 660-sat conservation bug; proof already mechanized |
| 5 | T6 duplicate admission + guarded retry | W13-PAY | model extension | P0 | Duplicate-payment safety; needs a small store carrier |
| 6 | T5 numbered receipt path | W13-STATE | model extension | P0 | Replay double-advance; explicit number is a model extension |
| 7 | T8 catalog/axiom coverage gate | W13-ASSURANCE | assurance | P0 | Current counts overstate coverage; no protocol risk |
| 8 | T7 stale-snapshot consumer theorem | W13-STATE | documentation/consumer | P1 | Mostly prevents misuse; low novelty, consider docs-only |

### T1 — Reserve direction and corrected liquidity

**FQNs (proposed):**
`LnLean.Proofs.Payment.LiquidityRepair.localReserveMsat`,
`LnLean.Proofs.Payment.LiquidityRepair.availableOutboundCorrected`,
`LnLean.Proofs.Payment.LiquidityRepair.reserve_direction_separates`,
`LnLean.Proofs.Payment.LiquidityRepair.addHtlcCorrected?`.

**Statement shape:**

```lean
def localReserveMsat (c : Channel) : Nat :=
  c.remoteEndpoint.params.channelReserveSat * Msat.MSAT_PER_SAT

def availableOutboundCorrected (c : Channel) : Nat :=
  outboundLiquidity c - localReserveMsat c

def remoteReserveMsatCorrected (c : Channel) : Nat :=
  c.localEndpoint.params.channelReserveSat * Msat.MSAT_PER_SAT

def availableInboundCorrected (c : Channel) : Nat :=
  inboundLiquidity c - remoteReserveMsatCorrected c

theorem reserve_direction_separates :
    ∃ c : Channel,
      reserveMsat c = 0 ∧ localReserveMsat c = 1000 ∧
      availableOutbound c = 1000 ∧ availableOutboundCorrected c = 0
```

`addHtlcCorrected?` uses the corrected reserve side, a direction-filtered
pending sum (T2), and the full `AffordableAdd` guard set (positive, CLTV bound,
`htlc_minimum`, offered balance, reserve, in-flight).

**Hypotheses:** none for the separation theorem; `addHtlcCorrected?` needs the
usual `ChannelParams` well-formedness only where the caller wants a
refinement, not for the reserve arithmetic.

**Non-vacuity witness:** the `Channel` with `localEndpoint.channelReserveSat = 0`,
`remoteEndpoint.channelReserveSat = 1`, `localBalance = 1000 msat`,
`remoteBalance = 0`, empty HTLC list. `decide` closes both the equality and the
`addHtlcCorrected? = none` half. A second witness with both reserves 0 shows
the corrected predicate is not empty.

**Fidelity:** BOLT 2 D1; LDK's `get_available_balances_for_scope` direction.
The corrected value is still an **upper bound** on LDK outbound capacity, not
an equality: it omits commitment fees, anchor values, dust, and in-flight
subtraction (`LiquidityProps.lean:76-81`). State that boundary in the module
docstring.

**Feasibility:** high. Pure definitions, `omega`/`decide`, no new imports.

**Model extension vs external:** additive model correction, local to Lean.
No external assumption.

**Weakening/vacuity flag:** do **not** redefine `reserveMsat`,
`availableOutbound`, `reserveOf`, `MeetsReserve`, or `planFits` in place. The
old definitions have true theorems about the old carrier; changing them would
silently change the meaning of `addHtlc?` and the `planFits` corollaries.
Retain the old names with a docstring "reserve side is inverted; use
`*Corrected`", and prove `reserveMsat_eq_localEndpoint` explicitly so the
legacy reading is auditable. This target does not weaken any existing theorem.

### T2 — Directional pending in-flight

**FQNs (proposed):**
`LnLean.Proofs.Channel.StateRepair.pendingHtlcValueInDirection`,
`LnLean.Proofs.Channel.StateRepair.WithinInFlightDirectional`,
`LnLean.Proofs.Channel.StateRepair.directional_inFlight_separates`,
`LnLean.Proofs.Channel.StateRepair.updateAddHtlc_preserves_directionalCap`.

**Statement shape:**

```lean
def pendingHtlcValueInDirection (c : Channel) (dir : Direction) : Nat :=
  ((c.htlcs.filter (fun h =>
      h.direction = dir ∧
      (h.state = .offered ∨ h.state = .received))).map
    (fun h => h.amount.val)).sum

def WithinInFlightDirectional (c : Channel) (dir : Direction)
    (amount : Msat) : Prop :=
  pendingHtlcValueInDirection c dir + amount.val ≤
    (receiverParams c dir).maxHtlcValue.val

theorem directional_inFlight_separates :
    ∃ (c : Channel) (dir : Direction) (amount : Msat),
      WithinInFlightDirectional c dir amount ∧
      ¬ (pendingHtlcValueOf c + amount.val ≤
          (receiverParams c dir).maxHtlcValue.val)

theorem updateAddHtlc_preserves_directionalCap
    (h : AffordableAddDirectional c dir amount cltv) :
    pendingHtlcValueInDirection (updateAddHtlc c dir amount ph cltv) dir ≤
      (receiverParams c dir).maxHtlcValue.val
```

`AffordableAddDirectional` is a new structure (or a new field in a new
predicate) combining the correct reserve of `AffordableAdd` with the
directional, pending-only cap.

**Hypotheses:** `receiverParams` is the receiving endpoint; the direction is
the sender's direction. The witness needs no well-formedness.

**Non-vacuity witness:** remote-offered pending 600 msat, local add 500 msat,
receiver cap 1000 msat. Directional: `0 + 500 ≤ 1000` accepts; pooled:
`600 + 500 > 1000` rejects. A second witness with a settled local HTLC proves
the pending-only filter matters (G03).

**Fidelity:** BOLT 2 D2 and LDK's `!htlc.outbound` filter. The theorem is about
the receiver's advertised cap, not a global channel cap.

**Feasibility:** high. `List.filter`/`sum` arithmetic plus the existing
`updateAddHtlc` lemmas.

**Model extension vs external:** additive model correction; no external
assumption.

**Weakening/vacuity flag:** **do not** redefine `pendingHtlcValueOf`,
`AffordableAdd.withinInFlight`, `D14.inFlightMsat`, or `E37.pendingValue`.
Directional admission is strictly weaker than pooled admission, so a
directional predicate does **not** imply the old pooled one; downstream proofs
that need the pooled bound must keep using `AffordableAdd`. Existing
`AffordableAdd` theorems remain true. Mark the old predicate "conservative but
not BOLT-2-faithful" rather than deleting it.

### T3 — Production anchor-debit consumer

**FQNs (proposed):**
`LnLean.Proofs.Channel.CommitmentAnchorTargets.commitmentPairCanonical`,
`LnLean.Proofs.Channel.CommitmentAnchorTargets.commitmentPairCanonical_conserved`,
`LnLean.Proofs.Channel.CommitmentAnchorTargets.commitmentPairCanonical_eq_legacy_of_noAnchors`,
`LnLean.Proofs.Channel.CommitmentAnchorTargets.legacy_anchor_overfunds_660`.

**Statement shape:**

```lean
def commitmentPairCanonical (localParams remoteParams : ChannelParams)
    (b : Balance) (fee number : Nat) (funder : Direction) : CommitmentPair :=
  LnLean.Proofs.ModelHardening.F04.commitmentPairWithAnchorDebit
    localParams remoteParams b fee number funder

theorem commitmentPairCanonical_conserved
    (hL : funderDebitSat fee localParams.anchorOutputs ≤
      (if funder = Direction.local then b.localBalance.val else b.remoteBalance.val))
    (hR : funderDebitSat fee remoteParams.anchorOutputs ≤
      (if funder = Direction.local then b.localBalance.val else b.remoteBalance.val)) :
    let p := commitmentPairCanonical localParams remoteParams b fee number funder
    p.localCommitment.totalOutputValue + fee = p.localCommitment.fundingValueSat ∧
    p.remoteCommitment.totalOutputValue + fee = p.remoteCommitment.fundingValueSat

theorem commitmentPairCanonical_eq_legacy_of_noAnchors
    (hL : localParams.anchorOutputs = false)
    (hR : remoteParams.anchorOutputs = false) :
    commitmentPairCanonical localParams remoteParams b fee number funder =
      commitmentPairOfBalances localParams remoteParams b fee number funder

theorem legacy_anchor_overfunds_660 :
    let p := commitmentPairOfBalances
      (waveF_f04_counterexampleParams true)
      (waveF_f04_counterexampleParams true)
      waveF_f04_counterexampleBalance 1000 0 Direction.local
    p.localCommitment.totalOutputValue + 1000 = 100_000 + 660
```

The conservation proof is already `waveF_f04_corrected_conservation`
(`F04.lean:270-291`); this target promotes it behind a production-facing name
and adds the behaviour-preserving no-anchor alias. No new arithmetic is needed.

**Hypotheses:** `fee + 660 ≤ funder balance` when the relevant commitment has
anchors, separately for each endpoint (the two commitments can disagree).
Without those hypotheses the corrected constructor's `Nat` subtraction
truncates and the theorem is not claimed.

**Non-vacuity witness:** `waveF_f04_counterexampleBalance` (60 000/40 000),
`fee = 1000`, both endpoints anchored; `funderDebitSat 1000 true = 1660`, which
is ≤ 60 000. Both corrected commitments conserve; the legacy local commitment
is 100 660.

**Fidelity:** BOLT 3 D5; the 1124 WU basis applies only to the zero-fee anchor
form (`chan_utils.rs:280-283`). Do not generalize this target to a literal
serialized-weight claim.

**Feasibility:** medium-low integration, high proof reuse. The theorem exists;
the work is module placement, aliases, and consumer tests.

**Model extension vs external:** fidelity repair / integration. No external
assumption.

**Weakening/vacuity flag:** do **not** change `commitmentPairOfBalances` in
place. `commitmentPairOfBalances_conserved` (`Conservation.lean:451-466`) is
guarded by both `anchorOutputs = false`; changing the constructor would
invalidate `waveF_f04_counterexample_660`, `commitmentPair_anchorCounterexample`,
and the H27/H28 retention theorems. Add `commitmentPairCanonical`, deprecate
the legacy constructor for anchored parameters, and keep every counterexample.
This target adds a consumer, it does not weaken the old theorem.

### T4 — Chain-backed route validity

**FQNs (proposed):**
`LnLean.Proofs.Routing.RouteChain.ChainBacked`,
`LnLean.Proofs.Routing.RouteChain.routeValid_not_chainBacked`,
`LnLean.Proofs.Routing.RouteChain.constructRoute_chainBacked`.

**Statement shape:**

```lean
def ChainBacked (g : Graph) (r : Route) : Prop :=
  ∃ es : List ChannelEdge,
    es.length = r.hops.length ∧
    (∀ (i : Nat) (hi : i < es.length),
      es[i] ∈ g.edges ∧ es[i].enabled = true ∧
      es[i].node2 = r.hops[i].node) ∧
    (∀ (i : Nat) (hi : i + 1 < es.length),
      es[i].node2 = es[i + 1].node1)

theorem routeValid_not_chainBacked :
    ∃ (g : Graph) (r : Route), routeValid g r ∧ ¬ ChainBacked g r

theorem constructRoute_chainBacked
    (path : List (ChannelEdge × Msat))
    (hne : path ≠ [])
    (hmem : ∀ p ∈ path, p.1 ∈ g.edges)
    (hen : ∀ p ∈ path, p.1.enabled = true)
    (hconn : ∀ (i : Nat) (hi : i + 1 < path.length),
      path[i].1.node2 = path[i + 1].1.node1) :
    ChainBacked g (constructRoute path amountMsat)
```

**Hypotheses:** the existence form needs only the edge list; the construction
form needs non-emptiness, graph membership, enabled edges, and adjacent
`node2 = node1`.

**Non-vacuity witness:** graph edges `e1 : 0→1`, `e2 : 2→3`, both enabled;
route hops `[1, 3]` (one hop per edge). `routeValid` holds because each hop has
a backing edge; `ChainBacked` fails because `e1.node2 = 1 ≠ 2 = e2.node1`.
A positive witness is `constructRoute [e1, e3]` with `e1 : 0→1`, `e3 : 1→2`.

**Fidelity:** LDK's router builds connected paths (`router.rs:2797-2888`);
BOLT 7 route hops are a chain. The theorem is graph-level, not a claim about
capacity or scoring.

**Feasibility:** high. New definitions and list induction; no changes to
`Route.lean`.

**Model extension vs external:** additive predicate. No external assumption.

**Weakening/vacuity flag:** **do not** redefine `routeValid`. It is the
per-hop predicate with true consumers (`routeValid_edge_sound`,
`constructRoute_valid`). Add `routeChainValid` as the stronger production
predicate and prove `routeChainValid → routeValid`; retain the separation
witness permanently. Do not claim `routeValid` is "connected"; the current
docstring should be corrected.

### T5 — Numbered receipt idempotence

**FQNs (proposed):**
`LnLean.Proofs.Protocol.ChannelReestablishRepair.receiveNumbered?`,
`LnLean.Proofs.Protocol.ChannelReestablishRepair.receiveNumbered_idempotent`,
`LnLean.Proofs.Protocol.ChannelReestablishRepair.receiveNumbered_eq_receive_of_expected`,
`LnLean.Proofs.Protocol.ChannelReestablishRepair.replay_does_not_double_advance`.

**Statement shape:**

```lean
def receiveNumbered? (s : PeerState) (m : Msg) (commitmentNumber : Nat) :
    Option PeerState :=
  -- non-handshake branch: find the addressed channel and apply
  -- ChannelRecord.advanceReceivedNumbered c commitmentNumber
  ...

theorem receiveNumbered_idempotent
    (s s' : PeerState) (m : Msg) (k : Nat)
    (h : receiveNumbered? s m k = some s') :
    receiveNumbered? s' m k = some s'

theorem replay_does_not_double_advance
    (c : ChannelRecord) (m : CommitmentSigned) :
    (advanceReceivedNumbered c c.reestablish.nextCommitmentNumber)
        .reestablish.nextCommitmentNumber =
      c.reestablish.nextCommitmentNumber + 1
```

(The final shape should use the existing `Option` monad and `findChannel`
plumbing from `ChannelReestablishProps`; the point is the explicit number
parameter, not a new wire message.)

**Hypotheses:** the caller supplies the commitment number that the message
claims. For the equality-with-`receive` theorem, that number must equal
`c.reestablish.nextCommitmentNumber`; otherwise the numbered path is a no-op
and the theorem must say so, not silently accept.

**Non-vacuity witness:** replay the same `commitment_signed` twice. The
existing `duplicate_commitmentSigned_advances_twice` gives `+2`; the numbered
path gives `+1`. A message with a wrong number leaves the counter unchanged
and does not advance.

**Fidelity:** BOLT 2 deduplicates `commitment_signed` by the implicit
commitment number; LDK's `handle_channel_reestablish` and commitment dance
reject a retransmission already consumed. The wire message does not carry the
number, so this is explicitly a model extension at the receipt boundary.

**Feasibility:** medium. The record-level idempotence is already proved; the
work is the `PeerState`/`findChannel` adapter and the no-op branch.

**Model extension vs external:** model extension (explicit number). The wire
protocol assumption is external and must be documented.

**Weakening/vacuity flag:** do **not** change `advanceReceived` or delete
`duplicate_commitmentSigned_advances_twice`. The old unnumbered path remains
the wire-faithful (but non-idempotent) transition; the numbered path is an
additional adapter. Do not claim the wire carries the number.

### T6 — Duplicate payment admission and guarded keysend retry

**FQNs (proposed):**
`LnLean.Proofs.Payment.PaymentAdmission.PaymentStore`,
`LnLean.Proofs.Payment.PaymentAdmission.admitSend`,
`LnLean.Proofs.Payment.PaymentAdmission.duplicate_send_rejected`,
`LnLean.Proofs.Payment.PaymentAdmission.two_identical_keysends_not_both_succeed`,
`LnLean.Proofs.Payment.KeysendRetryRepair.retryIfNotSucceeded`,
`LnLean.Proofs.Payment.KeysendRetryRepair.retryIfNotSucceeded_succeeded`,
`LnLean.Proofs.Payment.KeysendRetryRepair.retryIfNotSucceeded_failed`.

**Statement shape:**

```lean
structure PaymentStore where
  entries : List (PaymentHash × PaymentStatus)

def admitSend (st : PaymentStore) (ph : PaymentHash) : Bool :=
  match st.lookup ph with
  | some .pending => false
  | some .succeeded => false
  | _ => true

theorem duplicate_send_rejected
    (st : PaymentStore) (ph : PaymentHash) (h : st.lookup ph = some .succeeded) :
    admitSend st ph = false

theorem two_identical_keysends_not_both_succeed
    (k₁ k₂ : Keysend) (h : k₁.paymentHash = k₂.paymentHash)
    (h₁ : k₁.session.state = .pending) :
    admitSend { entries := [(k₁.paymentHash, k₁.session.state)] }
      k₂.paymentHash = false

def retryIfNotSucceeded (k : Keysend) : Keysend :=
  if k.session.state = .succeeded then k
  else { k with session := { k.session with state := .pending } }

theorem retryIfNotSucceeded_succeeded
    (k : Keysend) (h : k.session.state = .succeeded) :
    retryIfNotSucceeded k = k

theorem retryIfNotSucceeded_failed
    (k : Keysend) (h : k.session.state = .failed) :
    (retryIfNotSucceeded k).session.state = .pending
```

**Hypotheses:** a finite store with a lookup function; a `Failed` entry is
retryable, `Pending`/`Succeeded` are not. The store is a model, not a
persistence proof.

**Non-vacuity witness:** `k₁ = k₂ = create sha256 pre 1000 cltv 18`; both
`pending`; the store records `k₁` as succeeded; `admitSend` rejects `k₂`.
For retry: a succeeded keysend; old `retry` gives `pending`, new gives
`succeeded`.

**Fidelity:** LDK Node D6 (`spontaneous.rs:67-73`) and the BOLT 11 duplicate
rule. Failing entries are retryable, matching `PaymentStatus::Failed`
overwrite semantics (`[R12:169-171]`).

**Feasibility:** high-medium. The store is a list with decidable equality;
the retry theorems are `rfl`/`by_cases`. No persistence, crash, or event layer.

**Model extension vs external:** model extension. Store durability and
send/record atomicity remain external/human (`R12:172`).

**Weakening/vacuity flag:** **do not** replace `Keysend.retry` or
`retry_pending`. They are true theorems of the old record; deleting them would
hide the divergence from LDK. Add `retryIfNotSucceeded` and retain a named
theorem `retry_resets_succeeded` documenting the old behaviour. Do not claim
`admitSend` prevents duplicate payments across a crash or a second process.

### T7 — Stale-snapshot restore consumer (low novelty)

**FQNs (proposed):**
`LnLean.Proofs.PhaseC3.PersistenceRecovery.stale_snapshot_restore_loses_update`,
`LnLean.Proofs.PhaseC3.PersistenceRecovery.stale_snapshot_not_latest`.

**Statement shape:**

```lean
theorem stale_snapshot_restore_loses_update
    {s : Snapshot} {c : Channel} {r : ChannelRecord} (h : Stale s c r) :
    ∃ c', Reachable c c' ∧
      s.restore.localCommitmentNumber < c'.localCommitmentNumber

theorem stale_snapshot_not_latest
    {s : Snapshot} {c : Channel} {r : ChannelRecord} (h : Stale s c r) :
    ¬ (∀ c', Reachable c c' →
        c'.localCommitmentNumber ≤ s.localCommitmentNumber)
```

**Hypotheses:** `Stale` already contains `Consistent s c r` and a reachable
later state. No new atomic-snapshot assumption.

**Non-vacuity witness:** a channel at local counter 1, a snapshot at 3 that
is consistent with an intermediate state, and a reachable state at 5. Restore
yields 3, which is `< 5`; the latest-prefix predicate fails.

**Fidelity:** this is the crash/recovery warning in `R17`; the theorem does
not prove durability. `RecoveryPoint.replays_full_history` remains the
positive result under the atomic-snapshot assumption.

**Feasibility:** high, but **novelty is low**: both statements are direct
consequences of `h.2` plus `rfl` on `restore`. Its value is naming and
consumer discipline, not new mathematics.

**Model extension vs external:** documentation/consumer theorem. Atomic
snapshot storage and fsync ordering remain external.

**Weakening/vacuity flag:** keep `stale_snapshot_rolls_back` but rewrite its
docstring: it does **not** apply `restore` and does not prove that restore
rolls back. If reviewers judge a near-definitional theorem not worth a build
lane, make this target docs-only and remove T7 from the wave. Do not delete
`recovery_no_rollback_committed`, which is the real no-rollback result.

### T8 — Catalog/axiom coverage gate (hybrid)

**Lean FQN (proposed):**
`LnLean.Proofs.Assurance.CatalogAudit.catalog_targets_subset_audited`.
**Runtime gate (proposed):** `scripts/check-axiom-coverage.py` plus a manifest
under `agents/status/` (implementation-owned; not this review).

**Statement shape:**

```lean
def catalogTargetNames : List String :=
  obligations.flatMap (fun o =>
    o.leanTarget.splitOn ";" |>.map String.trim |>.filter (· ≠ ""))

theorem catalog_targets_subset_audited :
    ∀ t ∈ catalogTargetNames,
      t ∈ auditedTheorems.map (fun n => n.toString) := by
  decide
```

The script half asserts, from the actual build transcript:

1. the set of names in `#print axioms` commands equals `auditedTheorems`;
2. every unique catalog target occurs in that printed set;
3. every `provedDeclarations` entry's `text` and `module` match the catalog
   `targetTable` entry it indexes, not merely that the ID exists;
4. every catalog `rlAnchor` resolves to a real line and is semantically
   reviewed (the current existence-only check is insufficient);
5. the recorded counts in `docs/THEOREM-INDEX.md` and `docs/TRACEABILITY.md`
   are generated from the same manifest.

**Hypotheses:** none for the Lean membership check; the script assumes it runs
after a successful build and parses the exact `#print axioms` lines.

**Non-vacuity witness:** today the theorem fails for 35 catalog names absent
from `auditedTheorems` (e.g. any of the 35 in the set difference); the script
fails for 72 unprinted targets. After the lane adds the names and prints, the
theorem holds and the script passes. A negative fixture that removes one
`#print axioms` line must make the script fail.

**Fidelity:** R31's audit; the `AxiomAudit` policy permits only `propext`,
`Quot.sound`, and `Classical.choice`. This target does not prove any protocol
behaviour.

**Feasibility:** medium. The Lean membership proof is a generated-list check;
the script is the real work and must be deterministic/offline.

**Model extension vs external:** assurance only. No new protocol assumption.

**Weakening/vacuity flag:** do **not** "fix" the count by trimming the
registry to 393, deleting unprinted names, or changing
`auditedTheorems_length` without reconciling the print commands. That would
make the literal easier while reducing coverage. Add/print names, or remove
only names that are genuinely not targets, with a recorded rationale. The
final registry length may be 465 or 470 depending on whether the 5 stale
registry-only names are printed or removed; do not hard-code a number in the
report or docs before that decision.

---

## 5. Assumptions, counterexamples, and non-vacuity risks

### 5.1 Retained counterexamples (must not be deleted)

| Witness | Where | What it shows |
|---|---|---|
| `waveF_f04_counterexample_660` | `LnLean/Proofs/ModelHardening/F04.lean:222-226` | Anchored legacy pair overfunds by 660 sat |
| `commitmentPair_anchorCounterexample` | `LnLean/Proofs/Conservation.lean:488-495` | Guarded conservation theorem cannot be strengthened to anchors without the debit |
| `waveD_d12_output_ordering_fails` | `LnLean/Proofs/WaveD/D12.lean:99` | Legacy `commitmentOutputs` is neither sorted nor dust-trimmed |
| `duplicate_commitmentSigned_advances_twice` | `ChannelReestablishProps.lean:386-390` | Unnumbered replay advances `+2` |
| `routeValid_not_chainBacked` (proposed) | W13-ROUTE | Per-hop validity is not a chain |
| `retry_pending` | `KeysendProps.lean:300-301` | Old retry resets a succeeded session |
| `ofEdge_rounding_counterexample` | `RouteBlindingProps.lean:252-258` (reported) | Ceiling vs truncating division |
| `channelReady_reachable_without_fundingSigned` | `StateMachineProps.lean:381` | A `channelReady` path not tied to `funding_signed`; do not cite as a handshake necessity theorem |
| MPP overpay | constructed in G08: `parts = [120]`, `total = 100` | Exact-sum gate rejects a protocol-permitted fulfilment |
| Net-dust mismatch | T8/G07: gross 1000, fee 167, dust 900 | Gross path keeps; net path trims |
| Partial-synchrony counterexample | `Invariants.lean:483-492` with `latency := fun _ => none` | The theorem is its hypothesis |

### 5.2 Non-vacuity requirements for the proposed targets

* Every target except T8 has an explicit inhabited witness in §4. The
  separation theorems are existential over concrete `Channel`, `Route`, or
  `Keysend` values, so they cannot be satisfied by an empty type.
* T1/T2 witnesses must saturate the arithmetic without `Nat` truncation;
  the chosen values (1000/1000, 600/500/1000) do so.
* T3 must exhibit both an anchored and a non-anchored parameter pair; the
  no-anchor alias alone would be vacuous for the debit claim.
* T4 must exhibit both a failing route and a passing chain; the `[1,3]` route
  alone would only prove non-universality.
* T5 must exhibit a fresh number (advance), a duplicate number (no-op), and a
  wrong number (no-op); one branch is not enough.
* T6 must exhibit `Pending`, `Succeeded`, and `Failed` store entries. A
  theorem quantified only over `Succeeded` does not establish retry
  behaviour.
* T7 must exhibit a stale snapshot and a later reachable state; otherwise
  `Stale` is empty.
* T8's script must include a negative fixture (remove one audit line); a gate
  that cannot fail is not an assurance gate.

### 5.3 Fidelity and scope risks

1. **Caller-supplied script/dust data.** `CommitmentTx` does not derive
   scripts from funding keys and takes the owner's dust limit as a parameter
   (`CommitmentOrderTargets.lean:54-62`). Any target here inherits those
   hypotheses. Do not describe `output_ordering` as a BOLT-3-exact production
   theorem.
2. **Reserve model is an upper bound.** `availableOutboundCorrected` still
   omits fees, anchors, dust, and in-flight; it is not LDK's capacity
   equality.
3. **Payment store is a model.** T6 does not prove persistence, fsync order,
   or cross-process admission. Those remain external.
4. **Explicit commitment number.** T5 changes the receipt interface; the
   wire does not carry the number. The theorem is about a model adapter, not
   BOLT 2 wire bytes.
5. **Pin drift.** Server claims inherit `179b4b2…` vs `fa123fed…`; no target
   in this report closes that. Do not use the server API as evidence for a
   Lean theorem until the pin is aligned.
6. **Anchor weight.** The 1124 WU figure is the fee basis for the zero-fee
   anchor form, not the literal serialized weight (`chan_utils.rs:280-283`).
   T3 is a value-conservation theorem, not a weight theorem.
7. **Specification wording.** `settle_requires_sum` and `mppComplete` are true
   of an exact-sum carrier but narrower than BOLT 4. Reword the catalog, add
   `settleGe` in a later wave; do not mark the existing theorem false.
8. **Do not overclaim `partial_synchrony_delivers`.** Rename/reword it as a
   hypothesis restatement or add a non-circular delivery model with an
   explicit oracle; the current form is not a liveness theorem.
9. **Do not overclaim `channel_ready_gate`.** It is a two-flag definitional
   result; confirmation depth, peer connectivity, shutdown, and splice
   readiness are separate carriers.

### 5.4 Proposals explicitly rejected as vacuous or weakening

* Replacing `AffordableAdd.withinInFlight` with the directional predicate in
  place: would break consumers that need the pooled bound and would silently
  change the meaning of existing theorems.
* Replacing `reserveMsat` in place: would change `addHtlc?`, `planFits`, and
  `MeetsReserve` without retaining the old carrier; the corrected definition
  must be additive.
* Replacing `Keysend.retry` in place: would delete the divergence witness and
  make `retry_pending` unstateable.
* Adding a funding-changing `Step` constructor for splice/dual funding:
  falsifies `step_fundingValue_eq` (`StateTransitionTargets.lean:417`) and the
  conservation embedding. This needs a sidecar model and maintainer sign-off.
* "Fixing" the axiom count by trimming the registry: reduces assurance while
  making the literal pass.
* Adding a "no double spend" theorem over a payment store that has no
  persistence: true only within one process and one in-memory list; label it
  as such.
* Proving `routeValid` is connected by changing its definition: breaks
  `routeValid_edge_sound` and `constructRoute_valid`; add a stronger predicate
  instead.

---

## 6. Wave-13 recommendation

### 6.1 Verdict on S12

S12's sentence "No new tractable P0/P1 proof lane was found"
(`S12-POST-INTEGRATION-AUDIT.md:55`) is **correct for closing the eight
remaining P0/P1 rows** (L1-01/L1-07, L1-02, L1-03, PR-01, PR-02, RT-02,
OPS-02, OPS-03). It is **not** correct if read as "no safe wave-13 work
exists". The wave-13 reports found a different class of work: live consumer
defects and assurance overstatements in already-proved rows, none of which
requires the external barriers to move. A bounded **repair + assurance** wave
is justified. Do not launch a protocol-extension wave.

### 6.2 Lanes and exclusive ownership

All lanes create new files only; no lane edits another lane's files. The
generated root is regenerated once by the integrator with
`scripts/regen-root.sh`; it is not hand-edited. Acceptance commands run under
the shared build lock, exact module only, no network.

| Lane | Targets | Exclusive new files | Acceptance tests |
|---|---|---|---|
| **W13-LIQ** | T1, T2, G03/G04 witnesses | `LnLean/Proofs/Payment/LiquidityRepair.lean`, `LnLean/Proofs/Channel/StateRepair.lean` | `lake build LnLean.Proofs.Payment.LiquidityRepair`; `#print axioms` for both headlines = `[propext, Classical.choice, Quot.sound]`; `reserve_direction_separates` and `directional_inFlight_separates` close by `decide`; old `reserveMsat_eq`, `addHtlc?_some_conditions`, `AffordableAdd` still compile; no `sorry`/`native_decide` |
| **W13-ANCHOR** | T3, G05/G06/G07 retention | `LnLean/Proofs/Channel/CommitmentAnchorTargets.lean` | Corrected conservation with `fee + 660 ≤ funder`; no-anchor alias by `rfl`; `waveF_f04_counterexample_660` and `commitmentPair_anchorCounterexample` still typecheck; legacy pair unchanged |
| **W13-PAY** | T6, G10/G11 | `LnLean/Proofs/Payment/PaymentAdmission.lean`, `LnLean/Proofs/Payment/KeysendRetryRepair.lean` | `duplicate_send_rejected` for `Pending` and `Succeeded`; `retryIfNotSucceeded_succeeded` and `_failed`; old `retry_pending` retained; no store-persistence claim in docstring |
| **W13-STATE** | T5, T7, G09/G17 | `LnLean/Proofs/Protocol/ChannelReestablishRepair.lean`, `LnLean/Proofs/PhaseC3/PersistenceRecoveryRepair.lean` | `receiveNumbered_idempotent` for fresh/duplicate/wrong number; `duplicate_commitmentSigned_advances_twice` retained; stale-restore theorem has a concrete witness; `stale_snapshot_rolls_back` docstring corrected |
| **W13-ROUTE** | T4, G12 | `LnLean/Proofs/Routing/RouteChain.lean` | `routeValid_not_chainBacked` witness; `constructRoute_chainBacked`; `routeChainValid → routeValid`; `routeValid_edge_sound` unchanged |
| **W13-ASSURANCE** | T8, G18–G22, G28; integration | `LnLean/Proofs/Assurance/CatalogAudit.lean`, `scripts/check-axiom-coverage.py`, manifest; integrator owns `LnLean/Proofs/Wave13.lean` and the regen-root run | All 282 unique catalog targets printed; registry/print set reconciled; `provedDeclarations` text/module equality checked; negative fixture fails; docs counts generated; `Obligations.lean:76` corrected to 51; `partial_synchrony_delivers`/`channel_ready_gate` docstrings and catalog wording relabelled as hypothesis/flag results |

**Why T4 is in wave 13, not wave 14.** The chain predicate is a small,
self-contained addition with a concrete witness and no external dependency. It
does not require capacity, scoring, or pathfinding. Leaving it out would keep
a known P0 claim ("connected end-to-end") false for another wave.

**Why G08 (MPP ≥) is deferred.** `settle_requires_sum` is a true theorem of a
narrower carrier. Adding `settleGe` is additive but touches the MPP
settlement/liveness layer; it is better done with the payment store lane in a
wave-14 payment extension than mixed into the wave-13 repair lane.

### 6.3 Wave-14 conditional lanes (do not start in wave 13)

| Lane | Scope | Entry condition |
|---|---|---|
| W14-ROUTE | fee floor/ceil theorem, capacity, `htlc_maximum_msat`, `findEdge` usability, scoring, in-flight liquidity, path selection | T4 landed; policy constants agreed |
| W14-ANCHOR | single-anchor exact presence, net-dust production consumer, zero-fee/`shared_anchor`, `update_fee` legality | T3 landed; maintainer accepts a version/zero-fee model extension |
| W14-PAY | MPP `settleGe`, mixed `total_msat`, `htlc_id`, inbound claim, store/event persistence | T6 landed; BOLT 4 semantic choice recorded |
| W14-SERVER | `fail_for_id` status projection, claim amount lower bound, open-mode matrix, readiness/usability projection | LDK Server pin aligned to `fa123fed…` (or a new recorded pin) |
| W14-SPLICE | splice/dual-funding funding mutation, quiescence, interactive tx | Maintainer approves a funding-changing sidecar and preserves `step_fundingValue_eq` |
| W14-OFFER | BOLT 12/async/trampoline/onion messages, unified send fatal errors | External spec/implementation maturity; no BOLT anchor for async yet |

### 6.4 Stop conditions

Stop a lane and report rather than forcing a proof if:

* the only way to state the target is to change an existing predicate's
  meaning or a retained counterexample;
* the target needs `Step` to change funding;
* the target needs a real cryptographic verifier, Noise/AEAD, EUF-CMA, or a
  production persistence source;
* the server claim depends on the `179b4b2…` pin;
* a lane would need to edit `LnLean.lean`, `lakefile.lean`, `vendor/`,
  `refs/`, or another lane's report.

---

## 7. Evidence and commands

### 7.1 Pins and counts

```sh
git -C /tmp/opencode/ldk-refs/ldk-node rev-parse HEAD
# fa123fed131e27ecc420b77fa7086fcf1ddaebb8
git -C /tmp/opencode/ldk-refs/ldk-server rev-parse HEAD
# c17dc11dde38f88c53457039ddf30c6b90a63ba2

python3 - <<'PY'
import re
s = open('LnLean/Proofs/Obligations.lean').read()
rows = re.findall(r'leanTarget := "(.*?)"', s, re.S)
toks = [t.strip() for r in rows for t in r.split(';') if t.strip()]
print(len(rows), len(toks), len(set(toks)))          # 51 294 282
PY

python3 - <<'PY'
import re
p = open('LnLean/Proofs/PhaseC3/AxiomAudit.lean').read()
printed = set(re.findall(r'#print axioms ([\w\.]+)', p))
body = p[p.index('def auditedTheorems'):p.index('theorem auditedTheorems_length')]
reg = set(re.findall(r'`([\w\.]+)', body))
print(len(printed), len(reg), len(reg - printed))    # 393 435 42
PY
```

The second script's `reg` is the `auditedTheorems` literal. For the catalog
coverage counts, compare the 282 unique targets with `printed` and `reg`:
72 not printed, 35 absent from the registry, 247 present.

### 7.2 Declaration checks (read-only)

```sh
grep -n "def reserveMsat\|def availableOutbound\|def addHtlc?" \
  LnLean/Proofs/Payment/LiquidityProps.lean
grep -n "def pendingHtlcValueOf\|structure AffordableAdd\|withinInFlight" \
  LnLean/Channel/State.lean
grep -n "def commitmentPairOfBalances\|def commitmentPairWithAnchorDebit\|660" \
  LnLean/Channel/Commitment.lean LnLean/Proofs/ModelHardening/F04.lean
grep -n "theorem output_ordering\|def outputsNet\|def htlcOutputNet" \
  LnLean/Proofs/Channel/CommitmentOrderTargets.lean LnLean/Channel/Commitment.lean
grep -n "advanceReceivedNumbered\|duplicate_commitmentSigned_advances_twice" \
  LnLean/Proofs/Protocol/ChannelReestablishProps.lean
grep -n "def routeValid\|def ofEdge" LnLean/Routing/Route.lean
grep -n "def retry\|retry_pending" LnLean/Proofs/Payment/KeysendProps.lean
grep -n "stale_snapshot_rolls_back\|def Stale" \
  LnLean/Proofs/PhaseC3/PersistenceRecovery.lean
grep -n "def auditedTheorems\|auditedTheorems_length" \
  LnLean/Proofs/PhaseC3/AxiomAudit.lean
grep -n "def provedDeclarations\|proved_decls_in_snapshot" \
  LnLean/Proofs/Traceability.lean
```

### 7.3 Pinned LDK checks

```sh
sed -n '730,742p' refs/bolts/02-peer-protocol.md
sed -n '884,887p'  refs/bolts/02-peer-protocol.md
sed -n '383,385p'  refs/bolts/04-onion-routing.md
sed -n '321,326p'  refs/bolts/03-transactions.md
sed -n '5854,5870p' refs/rust-lightning/lightning/src/ln/channel.rs
sed -n '6552,6605p' refs/rust-lightning/lightning/src/ln/channel.rs
sed -n '2639,2642p' refs/rust-lightning/lightning/src/routing/router.rs
sed -n '2797,2888p' refs/rust-lightning/lightning/src/routing/router.rs
sed -n '67,73p'     /tmp/opencode/ldk-refs/ldk-node/src/payment/spontaneous.rs
sed -n '266,270p'   /tmp/opencode/ldk-refs/ldk-node/src/payment/unified.rs
sed -n '331,345p'   /tmp/opencode/ldk-refs/ldk-node/src/payment/unified.rs
sed -n '16p'        /tmp/opencode/ldk-refs/ldk-server/Cargo.toml
```

### 7.4 Wave-13 build protocol (for the implementation wave, not this review)

```sh
export PATH=/dev/shm/btc/elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
flock -w 900 /tmp/ln-build.lock lake build LnLean.Proofs.Payment.LiquidityRepair
flock -w 900 /tmp/ln-build.lock lake build LnLean.Proofs.Channel.CommitmentAnchorTargets
flock -w 900 /tmp/ln-build.lock lake build LnLean.Proofs.Payment.PaymentAdmission
flock -w 900 /tmp/ln-build.lock lake build LnLean.Proofs.Protocol.ChannelReestablishRepair
flock -w 900 /tmp/ln-build.lock lake build LnLean.Proofs.Routing.RouteChain
flock -w 900 /tmp/ln-build.lock lake build LnLean.Proofs.Assurance.CatalogAudit
```

Do not run a bare `lake build`. Do not run these in this review lane; they are
listed so the wave-13 acceptance tests are reproducible.

### 7.5 What this report did not do

* Did not run `lake build`, `cargo test`, or any network fetch.
* Did not edit Lean, docs, scripts, tests, vendor, catalog, or another report.
* Did not validate the `179b4b2…` server dependency or any server e2e claim.
* Did not mechanize any proposed target; all new FQNs and statements are
  proposals, not existing declarations.
* Did not re-derive every R01–R31 datapoint; `[R]` marks the ones taken from
  the lane reports and `[V]` marks direct checks.
