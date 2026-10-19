# R29 — Catalog coverage matrix against LDK behavior

**Status:** read-only review
**Pins:** LDK Node `fa123fed131e27ecc420b77fa7086fcf1ddaebb8`, LDK Server `c17dc11dde38f88c53457039ddf30c6b90a63ba2`
**Review branch:** `repair/integrated` at `f7f062817c185cd70004bb26c652deb99c6fd4bd` (no branch, commit, or non-report file changes made)
**Core rust-lightning anchor:** `refs/rust-lightning` at `fe4900930c6bd5786ec4203274d7cf312776a5a6`; BOLT anchor `refs/bolts` at `1aadb719b4007c4cea0ba6e36b08c4fb53788dee`

## 1. Scope and current Lean surface

This lane maps the 51-row `ln-lean` catalog to the behavior surfaces exposed by
LDK Node and LDK Server. It does not re-prove anything and does not edit the
catalog. The question is narrower than "is the tree green?":

> For each catalog row, does the named Lean declaration actually entail the
> English claim, and which high-value LDK behaviors have no row at all?

The short answer is that the catalog is **green but not claim-complete**. It is
a metadata list of 51 `Obligation` records (`LnLean/Proofs/Obligations.lean:55-77`).
`status := .proved` is checked by `scripts/check-catalog.py` as "the exact named
declaration exists and its body is sorry-free" (`scripts/check-catalog.py:4-26`),
not as "the declaration's statement entails the row's English claim." Several
rows therefore name a true theorem whose statement is materially narrower,
broader, or differently scoped than the row text.

### 1.1 Catalog counts and metadata drift

| Quantity | Value | Source |
|---|---:|---|
| Catalog rows | 51 | `obligations_length` at `LnLean/Proofs/Obligations.lean:458` |
| Rows marked `proved` | 51 | `docs/THEOREM-INDEX.md:22-31`; `docs/TRACEABILITY.md` |
| Target strings | 294 | parsed from `leanTarget` fields |
| Unique target strings | 282 | same parse |
| Domains | 8 | 6 L1, 6 crypto/wire, 7 channel, 6 HTLC, 6 protocol, 6 routing, 7 payment, 7 security |

One concrete metadata defect: the docstring above the list still says
"The 48-obligation catalog" (`LnLean/Proofs/Obligations.lean:76`), while the
length theorem and both generated docs say 51. This is harmless to the build,
but it is a useful signal that the catalog has been extended without a
claim-level audit.

### 1.2 Catalog layer surface

| Layer | Main catalog rows | Representative declarations | What is actually claimed |
|---|---|---|---|
| L1 / chain | `LN-L1-001`–`006` | `fundingScriptPubKey_eq_p2wsh_twoOfTwo`, `commitmentBaseWeight_model_target`, `ChainFinalityTargets.*` | Constructed scripts/weights and a finite conditional finality model; the concrete ECDSA/amount context stays explicit |
| Crypto / wire | `LN-CR-001`–`006` | `paymentHash_sha256_contract`, `commitmentSig_contract`, `decode_encode`, `TLVStream.wellFormed_iff_pairwise`, `Message.decode_length` | Algebraic contracts under C1/C3/C8 and exact encoders; no computational reductions |
| Channel / commitment | `LN-CH-001`–`007` | `Ledger.step_conserves`, `Commitment.outputs_nonnegative`, `Commitment.output_ordering`, `Fee.commitmentSigningGate_rejected_iff_*`, `Reserve.bounds`, `HtlcAggregate.*` | A fixed-funding ledger, rich commitment-output model, fee gate, reserve/exposure, aggregate coverage |
| HTLC / revocation | `LN-HT-001`–`006` | `HtlcRecord.fulfill_sound`, `HtlcRecord.fail_only_after_expiry`, `HTLC.amount_conservation`, `HTLC.tagged_id_unique_of_reachable`, `revoked_commitment_is_old`, `breach_penalty_spends_both` | Preimage soundness, on-chain timeout guard, one-channel amount/id accounting, revocation predicates |
| Protocol / peer | `LN-PR-001`–`006` | `Handshake.open_bounds`, `channel_ready_gate`, `funding_signed_signing_contract`, `ProtocolWireTargets.*`, `Peer.reestablish_no_rollback`, `feature_intersection` | Handshake/peer state machines under transport/signing hypotheses |
| Routing / onion | `LN-RT-001`–`006` | `Route.wellFormed_*`, `Gossip.update_monotone`, `Onion.peel_deterministic`, `Onion.hmac_sound`, `Route.cltv_accumulates`, `GossipTargets.gossip_graph_only_valid_announcements` | Route arithmetic, onion structure, gossip monotonicity/signature gating |
| Payments | `LN-PM-001`–`007` | `Invoice.consistent_hash`, `Invoice.signature_valid`, `payment_secret_match`, `MppPayment.settle_requires_sum`, `MPP.running_total_bound`, `Keysend.preimage_binding`, `InvoiceWireTargets.parse_print` | Parsed-invoice fields, keysend, and a conservative exact-sum MPP scaffold |
| Security / proofs | `LN-SEC-001`–`007` | `L1Ledger.spend_preserves_noDoubleSpend`, `Conservation.global_conservation`, `Security.safety_async`, `partial_synchrony_delivers`, `Liveness.penalty_economical`, `Liveness.watchtower_bridge`, `NonVacuityTargets.*` | One-spend, multi-channel conservation, conditional game, penalty/watchtower interfaces, non-vacuity registry |

### 1.3 High-value proved surface that has no catalog row

These modules are root-imported and sorry-free but are not named by any
`leanTarget`. They are the cheapest candidates for promotion.

| Module | Key declarations | Why it matters for LDK coverage |
|---|---|---|
| `LnLean/Proofs/PhaseC3/CloseConservation.lean` | `cooperativeClose_conserved:224`, `unilateralClose_conserved:269`, `closePaths_totals_agree:370`, `concrete_cooperative_close_conserved:446`, `concrete_unilateral_close_conserved:457` | LDK exposes both cooperative close and force close (`ldk-node/src/lib.rs:2239`, `:2261`); the tree already proves both conserve the funding value, but no row records it |
| `LnLean/Proofs/PhaseC3/PersistenceRecovery.lean` | `restore_replay_suffix:395`, `recovery_no_rollback_reestablish:577`, `recovery_retains_channelReady:591`, `inconsistent_snapshot_rolls_back:618` | BOLT 2 `channel_reestablish` recovery; LDK Node persists channel/node state and replays (`ldk-node/src/event.rs:417-531`) |
| `LnLean/Proofs/Routing/RouteBlindingProps.lean` | `Route.amountAt:375`, `Route.amountAt_zero:385`, `Route.amountAt_succ:391`, `Route.amountAt_last:400`, `blinded_real_amountAt` | BOLT 4 route blinding and the per-hop amount schedule; no row |
| `LnLean/Proofs/Payment/LiquidityProps.lean` | `outbound_add_inbound_eq_total:198`, `conserved_total_le_capacity:234`, `availableOutbound_le_capacity:257`, `addHtlc?_some_meetsReserve:452` | Reserve/liquidity behavior behind `LN-CH-006`, but the row targets `Channel.Reserve.bounds` only |
| `LnLean/Proofs/Payment/KeysendProps.lean` | `create_valid:238`, `settle_valid:286`, `settle_succeeded_reveals:324`, `reveal_requires_success:336` | Keysend lifecycle; `LN-PM-006` targets only `Keysend.preimage_binding` |
| `LnLean/Proofs/ModelHardening/F14.lean` | `RunningTotalBound`, `PartFits`, `runningTotalBound_add:81`, `overTotal_counterexample:216`, `overTotal_not_complete:261` | Already mechanizes the over-total counterexample that the catalog's `LN-PM-005` wording ignores |

### 1.4 Explicit exclusions already in the tree

| Surface | Where excluded | Consequence |
|---|---|---|
| BOLT 12 offers/refunds | `LnLean/Payment/Invoice.lean:98` ("BOLT 12 offers are out of scope") | Any BOLT 12 row is a new subsystem, not a strengthening |
| Splicing / dual funding | `docs/SCOPE.md:23`, `docs/CHARTER.md:38`, `LnLean/Channel/Types.lean:41`, `LnLean/Channel/State.lean:51`; R25 §1.1 | Cannot be represented by the single fixed `Channel.funding` field |
| Watchtower implementation | No `watchtower` implementation in either pinned LDK ref; only monitor-persistence comments in `refs/rust-lightning/.../channelmonitor.rs` | `LN-SEC-006` remains an external service contract |
| Real Noise/AEAD, secp256k1, computational reductions | `docs/OPEN-ISSUES.md` `L1-03`, `PR-01`, `CR-01` | Conditional models only |

## 2. LDK datapoints (with `file:line`)

All paths below are inside the pinned read-only clones. LDK Node is the public
node API; LDK Server is the gRPC/macaroon surface; rust-lightning/BOLT anchors
give the protocol rule the model is supposed to track.

### 2.1 LDK Node public API

| Behavior | Evidence |
|---|---|
| Durable event queue; same event until `event_handled` | `ldk-node/src/lib.rs:997` (`next_event` doc: "always return the same event until handling is confirmed"), `:1031` (`event_handled`), `ldk-node/src/event.rs:417-531` (persisted `EventQueue`, `persist_queue`, `ReadableArgs`) |
| `PaymentClaimable` carries amount and deadline | `ldk-node/src/event.rs:246-260` (`claimable_amount_msat`, `claim_deadline`) |
| Immediate fail for unknown required TLV / duplicate / unknown payment | `ldk-node/src/event.rs:1005-1010` (bad TLV), `:1049-1053` (duplicate), `:1120-1127` (unknown BOLT 11) |
| Claim checks SHA-256(preimage) = payment hash | `ldk-node/src/payment/bolt11.rs:424` (`claim_for_id`), `:453-461` (hash comparison), `:477` (`fail_for_id`) |
| Forwarded payment carries fee/skim/trampoline sets | `ldk-node/src/event.rs:184-215` (`PaymentForwarded`, `total_fee_earned_msat`, `skimmed_fee_msat`, multi `prev_htlcs`/`next_htlcs`) |
| Splice in/out | `ldk-node/src/lib.rs:1953` (`splice_in`), `:1990` (`splice_in_with_all`), `:2022` (`splice_out`) |
| Cooperative / force close | `ldk-node/src/lib.rs:2239` (`close_channel`), `:2261` (`force_close_channel`) |
| BOLT 12 send/receive/refund/async | `ldk-node/src/payment/bolt12.rs:297` (`send`), `:509` (`receive`), `:548` (`request_refund_payment`), `:568` (`initiate_refund`), `:646` (`receive_async`) |
| On-chain RBF with reserve preservation | `ldk-node/src/wallet/mod.rs:3371` (`bump_fee_rbf`), `:3605-3615` (reserve check before additional fee) |
| LSPS2 JIT channels | `ldk-node/src/liquidity/client/lsps2.rs:59` (`lsps2_receive_to_jit_channel`), `:139` (`lsps2_receive_variable_amount_to_jit_channel`), `:343` (`lsps2_create_jit_invoice`); `ldk-node/src/liquidity/mod.rs:26-35`, `:392-424` |
| Persistence backend migration | `ldk-node/src/builder.rs:790` (v2 format migration), `:800` (`open_or_migrate_fs_store`); `ldk-node/src/lib.rs:2422-2423` (payment order not preserved across backend migration) |

### 2.2 LDK Server (gRPC, auth, events)

| Behavior | Evidence |
|---|---|
| Stable permissions + admin override | `ldk-server/ldk-server/src/macaroons/policy.rs:33` (`is_admin`), `:37-39` (`allows` = admin or permission) |
| `permissions` caveat: admin is replaced, non-admin intersects | `.../policy.rs:77-83` |
| `time-before` caveat | `.../policy.rs:85-92` |
| `method` caveat | `.../policy.rs:94-98` |
| Request proof binds timestamp/method/body hash; same request replayable | `ldk-server/docs/request-binding.md:23-33` (format), `:68-72` ("An identical request can still be replayed while the token is valid; there is no single-use check") |
| Auth applies when subscription starts; revocation does not close it | `ldk-server/ldk-server/src/service.rs:447` ("Authorization applies when the subscription starts; revocation does not close it") |
| `SubscribeEvents` best-effort, no persistence/replay/ack, bounded 1024, lag drops events | `ldk-server/docs/api-guide.md:330-341`; `ldk-server/ldk-server/src/service.rs:464-473` (`broadcast::error::RecvError::Lagged(_) => continue`) |
| Manual claim amount is a lower bound, not exact | `ldk-server/docs/api-guide.md:398-404` |
| Held payment fails backward at `claim_deadline` | `ldk-server/docs/api-guide.md:403-407` |

### 2.3 Decisive protocol semantics

| Rule | Evidence |
|---|---|
| MPP payee may receive total **≥** `total_msat` | `refs/bolts/04-onion-routing.md:383-385` ("equal to or greater than `total_msat`"), `:426-431` ("nodes are allowed to pay more than the `total_msat` they specified") |
| LDK's crossing predicate | `refs/rust-lightning/lightning/src/ln/functional_tests.rs:7318` (`amount_received >= total_msat && amount_received - current_path_amount < total_msat`) |
| Off-chain fail has no CLTV check | `refs/rust-lightning/lightning/src/ln/channelmanager.rs:9878` (`fail_htlc_backwards` calls `fail_htlc_backwards_with_reason` directly) |
| Event delivery is distinct from persistence | LDK Node queue (`lib.rs:997-1031`) vs Server stream (`api-guide.md:330-341`) |

## 3. Gap matrix

Status legend: **faithful** = the declaration entails the row claim under its
explicit hypotheses, at the model's abstraction level; **partial** = only a
strictly narrower or differently scoped statement is proved; **contradicted** =
a concrete LDK/BOLT behavior or a retained counterexample falsifies the row as
worded; **missing** = no row and no statement; **external** = the remaining
obligation is outside this Lean model.

### 3.1 Covered faithfully at the model level

| Behavior | Lean status | LDK evidence | Gap / counterexample | Priority |
|---|---|---|---|---|
| BigSize/TLV/frame decoding | faithful: `LN-CR-004/005/006` | same wire vocabulary in `LnLean/Protocol/Messages.lean`; BOLT 1 | Exact encoders, but no live-node decoder; model-level only | P2 |
| Commitment output nonnegativity, ordering, trimming | faithful: `LN-CH-002/003` | BOLT 3 outputs; LDK `chan_utils.rs` anchors | Legacy output function is refuted by D12; the rich model is the covered path | P1 |
| Commitment fee gate | faithful: `LN-CH-005` | BOLT 3 feerate/weight | Exact iff on the modelled gate | P1 |
| Reserve/exposure bounds | faithful: `LN-CH-006` | BOLT 2 `channel_reserve_satoshis`, `max_htlc_value_in_flight_msat` | Row targets `Channel.Reserve.bounds`; `LiquidityProps` is the richer uncatalogued form | P1 |
| Aggregate second-stage coverage | faithful: `LN-CH-007` | BOLT 3 HTLC second stage | Conditional on no-duplication/distinct commitments | P1 |
| Commitment counter monotonicity | faithful: `LN-CH-004` | BOLT 2 | None within the model | P2 |
| Fulfilment preimage soundness | faithful: `LN-HT-001` | `bolt11.rs:453-461` SHA-256 check | `HashFn` is a parameter; C1 supplies collision resistance | P1 |
| HTLC amount conservation | faithful: `LN-HT-003` | BOLT 3 balance equation | One-channel ledger only | P1 |
| HTLC id uniqueness | faithful: `LN-HT-004` | BOLT 2 per-sender counters | Untagged global uniqueness needs explicit cross-direction disjointness | P1 |
| Revocation/penalty predicates | faithful: `LN-HT-005/006` | BOLT 5 | Penalty is a spend predicate, not script execution | P1 |
| `channel_ready` gate | faithful: `LN-PR-002` | BOLT 2 | None | P2 |
| `channel_reestablish` no rollback | faithful: `LN-PR-005` + `PersistenceRecovery:577` | BOLT 2 retransmission | Snapshot model, not KVStore atomicity | P1 |
| Feature intersection | faithful: `LN-PR-006` | BOLT 1/9 | None | P2 |
| Route non-emptiness/connected/capacity | faithful: `LN-RT-001` | BOLT 4/7 | Capacity is a route-level model | P2 |
| Onion peel determinism / HMAC rejection | faithful: `LN-RT-003/004` | BOLT 4 | Structural peel and finite C8 admission | P1 |
| CLTV accumulation | faithful: `LN-RT-005` | BOLT 4 | None | P2 |
| Invoice hash/amount/secret | faithful: `LN-PM-001/003` | BOLT 11 `p`/`s` fields | Parsed record, not bech32 | P1 |
| Keysend preimage binding | faithful: `LN-PM-006` + `KeysendProps` | keysend TLV | `KeysendProps` lifecycle is uncatalogued | P1 |
| BOLT 11 field parser/printer | faithful: `LN-PM-007` | BOLT 11 field list | Explicitly pre-bech32/HRP/checksum | P2 |
| No double spend on a fresh outpoint | faithful: `LN-SEC-001` | L1 spend set | One-spend model only | P1 |

### 3.2 Partially covered (row text is broader than the statement)

| Behavior | Lean status | LDK evidence | Gap / counterexample | Priority |
|---|---|---|---|---|
| P2WSH/2-of-2 funding and `to_local` execution | partial: `LN-L1-001/004` | BOLT 2/3; LDK script templates | Conditional on `VendorEcdsaBridge`, C3, typed digest; `withVendorEcdsa_no_funding` shows the concrete model is total-rejecting at the untyped interface. The row itself discloses this. | P0 external |
| Ledger conservation | partial: `LN-CH-001` | BOLT 3; LDK commitment accounting | `step_conserves` covers only `LedgerOp`; `Ledger.funding` is fixed by construction (`LnLean/Security/Invariants.lean:54-56`). Splicing changes funding, so the row is not a claim about all channel value changes. | P1 |
| `open_channel` sender attribution | partial: `LN-PR-001` | BOLT 8 / LDK transport | `TransportAuthenticated` is a session flag; `SessionKeyBinding` is an explicit equality. `wire_payload_does_not_determine_sender`/`no_wire_sender_function` already retain the negative boundary. No real Noise_XK/AEAD. | P0 external |
| `funding_signed`/`commitment_signed` signing | partial: `LN-PR-003/004` | BOLT 2/3 | C3 + `KeyBinding`/`PopKeySoundOn`/`PopExtractionOn`; `selfSigModel` is a toy witness; no real EUF-CMA extraction | P0 external |
| BOLT 11 invoice signature | partial: `LN-PM-002` | BOLT 11 `n`/signature | Model projection under C3; `signature_only_verifies` intentionally separates verification from payment | P1 external |
| Global conservation | partial: `LN-SEC-002` | BOLT 3; L1 ledger | `global_conservation` covers `MultiChannelLedger.channels`; its own scope note says it has **no** L1 spend set (`LnLean/Proofs/PhaseC2/GlobalConservation.lean:328-333`). The row says "across all channels and the L1 spend set." | P1 |
| Asynchronous safety | partial: `LN-SEC-003` | BOLT 5 / game model | Conditional on four `Assumptions P` (`sigUnforgeable`, `hashBinding`, `timelockEnforced`, `channelConserved`), `SecurityGame.lean:144-148` | P2 |
| Penalty economics | partial: `LN-SEC-005` | BOLT 5 | Conditional on `FeeScheduleBounded`; the unconditional spike claim is refuted (`waveD_d34_unconditional_claim_false`) | P2 |
| Non-vacuity registry | partial: `LN-SEC-007` | model audit | The row itself says `witnessRegistry_sound` is a dependent-list projection, not a catalog-wide audit | P2 |
| Gossip supersession/signature gating | partial: `LN-RT-002/006` | BOLT 7 | Epoch/node-canonical lifts depend on `Nodup`/`CanonicalNodeAnnouncements`; raw `applyGossip` is unfiltered | P1 |
| Route fee/amount arithmetic | partial: uncatalogued `Route.amountAt` / `totalFee` | BOLT 4 per-hop fees | Arithmetic is exact, but no forwarding record, no actual claimed amount, no LDK fee-rounding refinement; `ofEdge_rounding_counterexample` retains the gap | P1 |
| Persistence and restart | partial: `PersistenceRecovery` | LDK Node `builder.rs:790/800`, `lib.rs:2422`; BOLT 2 reestablish | Snapshot/replay model; does not model KVStore atomicity, fs migration, or payment-order changes across backends | P1 |

### 3.3 Contradicted (concrete counterexample or decisive LDK behavior)

| Behavior | Lean status | LDK evidence | Gap / counterexample | Priority |
|---|---|---|---|---|
| MPP settlement requires an **exact** sum | contradicted: `LN-PM-004` → `MppPayment.settle_requires_sum` | BOLT 4 `04-onion-routing.md:383-385`; LDK `functional_tests.rs:7318` | Counterexample: `total = 100`, parts `[60, 60]`. BOLT 4 allows 120 ≥ 100; LDK's predicate is `amount_received >= total_msat`. `MppPayment.settle` (`Security/Invariants.lean:440-446`) returns `none`, so the model declares an allowed payment unsettleable. | **P0** |
| Each additional MPP part keeps the running total **≤** `total_msat` | contradicted as worded: `LN-PM-005` → `MPP.running_total_bound` | BOLT 4 `04-onion-routing.md:426-431`; F14 `overTotal_counterexample:216` | `running_total_bound` is true only under `mppComplete` (exact sum). The catalog claim omits that hypothesis. F14 already proves the unconditional form false with `overTotalPlan` (100, `[60,60]`). The faithful split is sender-side `PartFits` vs recipient-side `≥`. | **P0** |
| An HTLC is failed **only** at/after CLTV expiry | contradicted as worded: `LN-HT-002` → `HtlcRecord.fail_only_after_expiry` | `ldk-node/src/event.rs:1005-1010`, `:1049-1053`, `:1120-1127`; `channelmanager.rs:9878` | Counterexample: bad required TLV or duplicate payment at `height = 50`, `cltvExpiry = 100`. LDK fails the HTLC backward immediately; no CLTV guard. The theorem is a valid **on-chain timeout** lemma, not a universal failure law. | **P0** |
| "After GST every message is delivered within delta" is a liveness result | tautological: `LN-SEC-004` → `partial_synchrony_delivers` | BOLT 1 framing; scheduling model | The theorem body is exactly the hypothesis `hps m hm` (`Security/Invariants.lean:488-492`). It has zero independent content and must not be counted as an eventual-delivery theorem. Not false, but vacuous coverage. | P2 |
| Funding is fixed for channel life | contradicted by splicing: `LnLean/Security/Invariants.lean:54-56` + `step_conserves` | `ldk-node/src/lib.rs:1953/2022` | No `LedgerOp` changes `funding`; a splice-in/out changes the active funding value. The old model cannot represent a supported LDK operation. New sidecar relation required; do not mutate `Ledger`. | P2 model extension |

### 3.4 Missing high-value behaviors

| Behavior | Lean status | LDK evidence | Gap / counterexample | Priority |
|---|---|---|---|---|
| BOLT 12 offers/refunds/static invoices | missing, out of scope | `bolt12.rs:297/509/548/568/646` | `Invoice.lean:98` excludes BOLT 12. New subsystem: offer/invoice/refund objects, payer proofs, blinded message paths, async receive. | P2 external |
| Splicing lifecycle and funding replacement | missing, contradicted by fixed funding | `lib.rs:1953/2022`; R25 | Quiescence, splice negotiation, pending funding, `splice_locked` promotion all absent; `Channel.fundingValue` is preserved by every `Step`. | P2 model extension |
| Macaroon auth, caveats, request binding | missing | `policy.rs:33-98`; `request-binding.md:23-72` | No permissions/method/time caveats, no admin override, no proof binding, no replay-within-window fact. | P1 |
| Server event delivery vs durable queue | missing | `lib.rs:997-1031`; `api-guide.md:330-341`; `service.rs:464-473` | No model of "same event until ack", persisted queue, best-effort stream, bounded lag, or no-replay-after-reconnect. | P1 |
| Held payment claim/deadline | missing | `api-guide.md:398-407`; `event.rs:246-260` | No `claim_deadline`, lower-bound claim, or automatic backward fail. | P1 |
| KVStore persistence/version migration | missing | `builder.rs:790/800`; `lib.rs:2422` | `PersistenceRecovery` models snapshot/replay, not atomic durable storage or backend migration. | P2 external |
| LSPS2 JIT channel open/fee | missing | `liquidity/client/lsps2.rs:59/139/343` | No JIT invoice, opening-fee params, or provider interaction. | P2 external |
| Async payments / trampoline | missing | `bolt12.rs:646`; `event.rs:184-215` | No static-invoice server, async payer role, or multi-HTLD forwarding sets. | P2 external |
| On-chain RBF fee bump | missing | `wallet/mod.rs:3371/3605` | No RBF transition, no reserve-preserving additional-fee check. | P2 external |
| Forwarding lifecycle and fee accounting | missing | `event.rs:184-215`, `:1970` | R07 records no catalog row. `CrossChannelRouting` is route arithmetic only; no inbound→outbound record, no `total_fee_earned_msat`, no skim. | P1 |
| Cooperative/unilateral close row | missing row, already proved | `lib.rs:2239/2261`; `CloseConservation:224/269/370` | High-value theorem exists but is invisible to the catalog. | P1 |
| Route blinding row | missing row, already proved | BOLT 4 route blinding; `RouteBlindingProps:375-410` | `Route.amountAt` schedule and blinded-path projection are uncatalogued. | P1 |
| Watchtower service | external | No implementation in pinned refs | `LN-SEC-006` requires a `BreachResponse` and `wt.reports`; no tower implementation exists. | P2 external |

### 3.5 External / out-of-model

| Behavior | Why it is external | Where recorded |
|---|---|---|
| Concrete secp256k1 / EUF-CMA | Untyped `ByteArray` bridge is total-rejecting; typed digest or concrete verifier is a model change | `docs/OPEN-ISSUES.md` `L1-01`, `L1-07`, `PR-01` |
| Real Noise_XK/AEAD | `TransportAuthenticated` is a flag; `SessionKeyBinding` is an equality | `docs/OPEN-ISSUES.md` `L1-03` |
| Computational reductions | C1/C3/C8 are algebraic; no probability/complexity model | `docs/OPEN-ISSUES.md` `CR-01`; `docs/CRYPTO-LIMITS.md` |
| PoW/probabilistic chain finality | Finite-graph/bounded-depth model only | `docs/OPEN-ISSUES.md` `L1-06` |
| LSPS2 provider/JIT server | LDK liquidity client/service is a separate protocol stack | `ldk-node/src/liquidity/**` |
| BOLT 12 ecosystem/async server | Offers, refunds, payer proofs, static invoices | `ldk-node/src/payment/bolt12.rs` |
| Watchtower | No tower implementation | `LnLean/Proofs/Liveness.lean:717` |
| Server ops/config/license | Release and legal decisions | `docs/OPEN-ISSUES.md` `OPS-02`, `OPS-03` |

## 4. Proposed targets

Eight targets are proposed. Targets 1–4 are suitable for a narrow wave-13/14
implementation lane. Targets 5–8 should be deferred or chartered separately;
they are runtime/server surfaces or model extensions, not repairs of an
existing claim.

### 4.1 `LnLean.Payment.MPP.claimable_on_threshold_crossing` — P0, implement

**Why.** BOLT 4 and LDK settle on `sum ≥ total_msat`, not exact equality. The
current model only has the conservative exact-sum `mppComplete`.

**Statement shape.**

```lean
namespace LnLean.Payment.MPP

/-- Recipient-side claimability: BOLT 4 permits total received ≥ total_msat. -/
def Claimable (plan : MPPPlan) (collected : List MPPPart) : Prop :=
  plan.parts ≠ [] ∧ plan.target.val ≤ sumParts collected

theorem claimable_of_complete {plan : MPPPlan} (h : mppComplete plan) :
    Claimable plan plan.parts

theorem claimable_mono {plan : MPPPlan} {c d : List MPPPart}
    (h : Claimable plan c) (hsub : List.Sublist c d) :
    Claimable plan d

theorem claimable_on_threshold_crossing {plan : MPPPlan}
    {collected : List MPPPart} {p : MPPPart}
    (hsub : List.Sublist (collected ++ [p]) plan.parts)
    (h : Claimable plan (collected ++ [p]))
    (hprev : ¬ Claimable plan collected) :
    sumParts collected < plan.target.val ∧
      plan.target.val ≤ sumParts (collected ++ [p])

theorem overpay_claimable_not_complete :
    ∃ (plan : MPPPlan) (collected : List MPPPart),
      Claimable plan collected ∧ ¬ mppComplete plan
```

**Hypotheses.** `plan.parts ≠ []`; shared `paymentHash`/`paymentSecret` are
already fields of `MPPPlan`. No new cryptographic hypothesis.

**Non-vacuity witness.** `overTotalPlan` from
`LnLean/Proofs/ModelHardening/F14.lean:196` (`target = 100`,
`parts = [60, 60]`) satisfies `Claimable` and refutes `mppComplete`. The exact
plan `[40, 60]` satisfies both.

**Why faithful.** Matches `refs/bolts/04-onion-routing.md:383-385` and
`functional_tests.rs:7318`. The "first crossing" conjunct captures LDK's
`amount_received - current_path_amount < total_msat` transition. Scope note:
BOLT 4's "no individual HTLC below the difference between total paid and
`total_msat`" rule is a sender-side routing constraint and is **not** modelled
here; `Claimable` is recipient-side only.

**Do not change** `mppComplete`, `MppPayment.settle`, or
`running_total_bound`. Redefining `mppComplete` as `≥` would falsify
`running_total_bound` and the F14 exact-bound lemmas. Keep exact completeness
as a conservative special case and add `Claimable` beside it.

### 4.2 `LnLean.Security.HtlcRecord.failWith` + `badOnion_fail_before_expiry` — P0, implement

**Why.** `fail_only_after_expiry` is an on-chain timeout lemma. LDK fails
off-chain for policy reasons with no CLTV check.

**Statement shape.**

```lean
namespace LnLean.Security

inductive FailReason where
  | expiry
  | badOnion
  | duplicate
  | unknownPayment

def HtlcRecord.failWith (h : HtlcRecord) (r : FailReason) (height : Height) :
    Option HtlcRecord :=
  match r with
  | .expiry => h.fail height
  | .badOnion | .duplicate | .unknownPayment =>
      some { h with state := .failed }

/-- Existing on-chain timeout theorem, unchanged. -/
theorem expiry_fail_only_after_expiry (h h' : HtlcRecord) (height : Height)
    (hstep : h.failWith .expiry height = some h') : h.cltvExpiry ≤ height

/-- Off-chain policy failure is not bounded by CLTV. -/
theorem badOnion_fail_before_expiry :
    ∃ (h h' : HtlcRecord) (height : Height),
      height < h.cltvExpiry ∧ h.failWith .badOnion height = some h'
```

**Hypotheses.** None beyond the record fields; the witness uses
`cltvExpiry = 100`, `height = 50`.

**Non-vacuity witness.** The witness above; `fail_only_after_expiry` remains
available for the `.expiry` constructor and for `HtlcRecord.fail`.

**Why faithful.** `event.rs:1005-1010` (bad required TLV),
`:1049-1053` (duplicate), `:1120-1127` (unknown payment),
`channelmanager.rs:9878` (`fail_htlc_backwards` has no CLTV guard).

**Do not** delete or weaken `HtlcRecord.fail`/`fail_only_after_expiry`. The
catalog row must be reworded to "an on-chain timeout failure occurs only at or
after CLTV expiry; off-chain policy failures may occur earlier."

### 4.3 Catalog row `LN-CH-008` — close conservation — P1, promote

**Why.** Both close paths already conserve the funding value, but no catalog
row records it.

**Targets (already proved).**

* `LnLean.Proofs.PhaseC3.CloseConservation.cooperativeClose_conserved:224`
* `LnLean.Proofs.PhaseC3.CloseConservation.unilateralClose_conserved:269`
* `LnLean.Proofs.PhaseC3.CloseConservation.closePaths_totals_agree:370`
* `LnLean.Proofs.PhaseC3.CloseConservation.concrete_cooperative_close_conserved:446`
* `LnLean.Proofs.PhaseC3.CloseConservation.concrete_unilateral_close_conserved:457`

**Statement shape (promotion wrapper, optional).**

```lean
theorem close_conserves_funding
    (b : Balance) (fee : Nat) (funder : Direction)
    (h : fee ≤ funderBalance b funder) :
    (cooperativeClose b fee funder).totalOutputValue +
      (cooperativeClose b fee funder).closingFeeSat =
    b.localSat + b.remoteSat
```

This is exactly `cooperativeClose_outputs_add_fee:214`; the unilateral form is
`unilateralClose_conserved`. The row only needs to name the existing exact
targets.

**Non-vacuity witness.** `concrete_cooperative_close_conserved`
(`60000 + 39000 + 1000 = 100000`) and
`concrete_unilateral_close_conserved` (one 5000-sat HTLC, fee 1000, funding
100000).

**Why faithful.** BOLT 2 `closing_signed` and BOLT 3 commitment outputs;
`ldk-node/src/lib.rs:2239/2261` expose both paths. Scope note: this is a
satoshi-level close model, not a composition with `MultiChannelLedger`.

### 4.4 Catalog row `LN-PR-007` — persistence recovery — P1, promote

**Why.** BOLT 2 reestablish/recovery is proved in an uncatalogued module.

**Targets (already proved).**

* `PersistenceRecovery.restore_replay_suffix:395`
* `PersistenceRecovery.recovery_no_rollback_reestablish:577`
* `PersistenceRecovery.recovery_retains_channelReady:591`
* `PersistenceRecovery.inconsistent_snapshot_rolls_back:618`

**Statement shape (existing).**

```lean
theorem restore_replay_suffix {eff : HtlcEffect} {init : Persisted}
    {pre post : List Msg} {s : Snapshot}
    (hcons : s = Snapshot.ofPersisted (replay eff pre init)) :
    replay eff post s.restore = replay eff (pre ++ post) init
```

**Hypotheses.** `RecoveryPoint.consistent` and `Snapshot.Consistent`; these are
explicit propositions, never axioms.

**Non-vacuity witness.** `inconsistent_snapshot_rolls_back` is the retained
negative witness; `recovery_retains_channelReady` is the positive one.

**Why faithful.** BOLT 2 `channel_reestablish`; LDK Node's persisted event
queue and builder migration show the runtime analog. Scope note: this is not a
KVStore atomicity or fs-migration theorem.

### 4.5 `LnLean.Protocol.ServerAuth.attenuation_only_narrows` — P1, defer

**Why.** LDK Server's macaroon model has a clean monotonicity law: derived
caveats only narrow. No Lean row exists.

**Statement shape.**

```lean
namespace LnLean.Protocol.ServerAuth

/-- The distinguished admin permission.  LDK Server's admin check is
membership of `admin` in the permission set (`policy.rs:33-39`). -/
def adminPermission : Permission := ⟨"admin"⟩

structure Macaroon where
  permissions : Finset Permission
  method : Option RpcMethod
  expiresAt : Option Nat

def Macaroon.isAdmin (m : Macaroon) : Prop :=
  adminPermission ∈ m.permissions

def Macaroon.allows (m : Macaroon) (now : Nat) (meth : RpcMethod)
    (p : Permission) : Prop :=
  (m.isAdmin ∨ p ∈ m.permissions) ∧
    (m.method = none ∨ m.method = some meth) ∧
    (m.expiresAt = none ∨ now < m.expiresAt)

/-- LDK semantics: an admin root is replaced by the allowed set; a
non-admin root is intersected with it (`policy.rs:77-83`). -/
def Macaroon.attenuate (m : Macaroon) (s : Finset Permission) : Macaroon :=
  if m.isAdmin then { m with permissions := s }
  else { m with permissions := m.permissions ∩ s }

theorem attenuation_only_narrows (m : Macaroon) (s : Finset Permission)
    (now : Nat) (meth : RpcMethod) (p : Permission)
    (hall : (m.attenuate s).allows now meth p) :
    m.allows now meth p

theorem attenuation_strict_witness :
    ∃ (m : Macaroon) (s : Finset Permission) (now : Nat)
      (meth : RpcMethod) (p : Permission),
      m.allows now meth p ∧ ¬ (m.attenuate s).allows now meth p
```

**Hypotheses.** `Permission`/`RpcMethod` finite types; the HMAC chain and root
key are **not** modelled. This is caveat monotonicity, not unforgeability.

**Non-vacuity witness.** Root `permissions := {admin, close}` allows `close`.
Attenuate to `{send}`: the derived token is non-admin and allows only `send`,
so it does not allow `close`. A second witness shows `send` is allowed by both,
so attenuation is not vacuously empty.

**Why faithful.** `policy.rs:33-39` (admin or permission), `:77-83` (admin
replaced, non-admin intersection), `:85-98` (time/method caveats).

**Replay caveat.** `request-binding.md:68-72` says identical requests are
replayable within the 60-second window. If modelled, it must be a negative
theorem (`request_proof_not_single_use`), never a claim of replay protection.

### 4.6 `LnLean.Payment.Held.claim_lower_bound` — P2, defer

**Statement shape.**

```lean
namespace LnLean.Payment.Held

structure HeldPayment where
  amount : Msat
  deadline : Option Height
  state : HeldState

def HeldPayment.claim (h : HeldPayment) (amt : Msat) (now : Height) :
    Option HeldPayment :=
  if h.state = .pending ∧
      (∀ d, h.deadline = some d → now ≤ d) ∧
      h.amount.val ≤ amt.val
  then some { h with state := .claimed }
  else none

theorem claim_amount_lower_bound {h h' : HeldPayment} {amt : Msat}
    {now : Height} (hstep : h.claim amt now = some h') :
    h.amount.val ≤ amt.val

theorem no_claim_after_deadline {h h' : HeldPayment} {amt : Msat}
    {now d : Height} (hd : h.deadline = some d) (hnow : d < now) :
    h.claim amt now = none
```

**Hypotheses.** `deadline` is an optional height; `claim` is a lower-bound
check only.

**Non-vacuity witness.** `amount = 100`, `amt = 150`, `now = 50`,
`deadline = 100` → claim succeeds; `now = 101` → `none`.

**Why faithful.** `api-guide.md:398-404` ("lower-bound check ... not an exact
amount check ... A larger supplied amount passes") and `:403-407`
(`claim_deadline` auto-fail).

### 4.7 `LnLean.Runtime.EventQueue.ack_stable` — P2, defer

**Statement shape.**

```lean
namespace LnLean.Runtime.EventQueue

structure DurableQueue where
  front : Option Event
  handled : Bool

inductive QueueStep : DurableQueue → DurableQueue → Prop
  | ack (q : DurableQueue) (e : Event) (h : q.front = some e) :
      QueueStep q { q with front := none, handled := true }
  | push (q : DurableQueue) (e : Event) (h : q.front = none) :
      QueueStep q { q with front := some e }

/-- A front is cleared only by the ack transition. -/
theorem only_ack_clears_front (q q' : DurableQueue)
    (h : QueueStep q q') (hclear : q'.front = none) :
    q'.handled = true

structure BestEffortStream where
  sent : List Event
  delivered : List Event
  hsub : List.Sublist delivered sent

theorem lag_can_drop :
    ∃ s : BestEffortStream, s.delivered ≠ s.sent
```

**Hypotheses.** Abstract `Event`; no network or scheduling model. The queue
has only two transitions (`ack`, `push`); the theorem shows the ack flag is
necessary to clear the front.

**Non-vacuity witness.** `sent = [e1, e2]`, `delivered = [e1]`; the lag path in
`service.rs:472-473` is the concrete justification.

**Why faithful.** `lib.rs:997-1031` (durable queue, same event until
`event_handled`) versus `api-guide.md:330-341` (server stream best-effort, no
persistence/replay/ack, bounded 1024, lag drops).

### 4.8 `LnLean.Channel.Splice.spliceIn_preserves_worldValue` — P2, defer/model extension

**Why.** Splicing is supported by LDK Node but deliberately excluded by the
current single-funding model. This target is a sidecar model, not a change to
`Channel`/`Step`.

**Statement shape.**

```lean
namespace LnLean.Channel.Splice

structure SpliceState where
  activeFunding : Msat
  pendingFunding : Option Msat
  quiescent : Bool
  pendingIn : Bool
  pendingOut : Bool

def SpliceState.worldValue (s : SpliceState) : Nat :=
  s.activeFunding.val + (s.pendingFunding.map Msat.val).getD 0

def spliceIn (s : SpliceState) (a : Msat) : Option SpliceState :=
  if s.quiescent then
    some { s with pendingFunding := some ⟨s.worldValue + a.val⟩ }
  else none

theorem spliceIn_preserves_worldValue {s s' : SpliceState} {a : Msat}
    (h : spliceIn s a = some s') : s'.worldValue = s.worldValue + a.val

theorem no_ledgerOp_changes_funding (l l' : Ledger) (op : LedgerOp)
    (h : l.step op = some l') : l'.funding = l.funding
```

**Hypotheses.** `quiescent = true`; `pendingFunding` is a candidate, not active
capacity. The `WorldValue` definition is illustrative; the lane should settle
the active/pending accounting before proving it.

**Non-vacuity witness.** Active 100000, splice-in 50000 → world value 150000;
the old `Ledger` path cannot change `funding` (`no_ledgerOp_changes_funding`).

**Why faithful.** `lib.rs:1953/2022` and R25's model barrier. This is a model
extension, not a repair; it needs maintainer sign-off because it changes the
meaning of channel funding.

## 5. Assumptions, counterexamples, and non-vacuity risks

### 5.1 Assumptions that must stay visible

| Assumption | Where | What it hides |
|---|---|---|
| C1 collision resistance on 32-byte preimages | `docs/ASSUMPTIONS.md`; `LN-CR-001` | Not a global SHA-256 injectivity or preimage-resistance theorem |
| C3 ECDSA EUF-CMA | `LN-CR-002`, `LN-PR-003/004` | No real secp256k1; `withVendorEcdsa_no_funding` shows total rejection at the untyped bridge |
| C8 finite-execution HMAC binding | `LN-CR-003` | Not a global PRF claim; `hmacPrf_vacuous` retains the negative |
| `SessionKeyBinding` / `TransportAuthenticated` | `LN-PR-001`, `L1-03` | Not real Noise_XK/AEAD authentication |
| `Assumptions P` (4 fields) | `LN-SEC-003`, `SecurityGame.lean:144-148` | Deterministic game, not a computational reduction |
| `FeeScheduleBounded` | `LN-SEC-005` | Unconditional spike claim is false (`waveD_d34_unconditional_claim_false`) |
| `BreachResponse` + `wt.reports` | `LN-SEC-006`, `Liveness.lean:717-724` | No watchtower implementation; the report supplies the penalty tx/confirmation |
| `Snapshot.Consistent` / `RecoveryPoint.consistent` | `PersistenceRecovery` | Not KVStore atomicity or fs migration |
| `PopKeySoundOn` / `PopExtractionOn` / `KeyBinding` | `LN-PR-003` | No real EUF-CMA extraction or key ownership |
| `ExtensionConsumerLaw` | `LN-PR-004` | Production coverage source still external |
| `Nodup` / `CanonicalNodeAnnouncements` | `LN-RT-002/006` | Raw `applyGossip` remains unfiltered |
| `mppComplete` exact sum | `LN-PM-004/005` | The overpay case is excluded by construction, not proved |
| `Ledger.funding` fixed | `LN-CH-001` | Splicing cannot be represented |
| `HtlcRecord.fail` expiry guard | `LN-HT-002` | Covers on-chain timeout only, not off-chain policy fail |

### 5.2 Counterexamples and witnesses to preserve

* `overTotalPlan` / `overTotal_counterexample` (`F14:196-229`): target 100,
  parts `[60, 60]`. This is the decisive MPP overpay witness.
* `concrete_cooperative_close_conserved` and
  `concrete_unilateral_close_conserved` (`CloseConservation:446/457`): positive
  close non-vacuity.
* `inconsistent_snapshot_rolls_back` (`PersistenceRecovery:618`): persistence
  negative witness.
* `cross_direction_duplicate_tagged` (`LN-HT-004`): untagged id uniqueness is
  false without cross-direction disjointness.
* `legacy_projection_not_determine_htlc_coverage`,
  `wire_admits_distinct_coverage_witnesses` (`LN-PR-004`): the legacy wire is
  insufficient.
* `ofEdge_rounding_counterexample`: route fee rounding gap.
* `not_digestBindsMod_any_tag`, `no_digestBindsMod_anywhere`,
  `withVendorEcdsa_no_funding`: the untyped EC bridge is not a real verifier.
* `partial_synchrony_delivers`: itself the tautology witness; do not cite it as
  liveness.

### 5.3 Proposals that would weaken or hide

| Proposal | Consequence | Verdict |
|---|---|---|
| Redefine `mppComplete` as `sum ≥ target` | `MPP.running_total_bound` becomes false; F14 exact-bound lemmas break | **Reject.** Add `Claimable` beside it. |
| Drop `mppComplete` from `running_total_bound` | The statement is false (`overTotal_counterexample`) | **Reject.** Keep the hypothesis. |
| Change `MppPayment.settle` to accept `≥` | `settle_requires_sum` becomes a different theorem; downstream `settle_preserves_sum` must change | **Reject in this lane.** Add a separate `Claimable` model and reword the row. |
| Add a funding-changing constructor to `Step` | `step_fundingValue_eq`, `ledgerValue_step`, `step_conserves` become false | **Reject.** Use a sidecar splice relation (T8). |
| Delete `HtlcRecord.fail`/`fail_only_after_expiry` | Loses the on-chain timeout lemma and its non-vacuity | **Reject.** Add `FailReason` beside it. |
| Claim `global_conservation` covers the L1 spend set | The theorem has no UTXO/spend component; `GlobalConservation:328-333` says so | **Reject.** Reword `LN-SEC-002` or split the row. |
| Count `partial_synchrony_delivers` as liveness | It is the hypothesis restated | **Reject.** Reword `LN-SEC-004` as a definitional projection. |
| Claim `CloseConservation` composes with `MultiChannelLedger` | Different satoshi-level model; no bridge theorem | **Reject unless bridged.** Keep the scope note. |
| Claim macaroon monotonicity proves HMAC unforgeability | The HMAC chain/root key are unmodelled | **Reject.** Model caveats only. |

## 6. Wave-13 recommendation

**This lane does yield a safe, narrow implementation lane — but not a broad
"coverage" lane.**

### 6.1 Implement in wave 13/14 (P0/P1, additive)

1. **MPP claimability (T1).** Add `Claimable` and the threshold-crossing/overpay
   theorems in `LnLean/Payment/MPP.lean` or a new `LnLean/Proofs/Payment/MPPClaim.lean`.
   Reword `LN-PM-004` to "a settled MPP has parts summing to **at least** the
   advertised total" and `LN-PM-005` to the guarded/sender-side form. Keep
   `mppComplete`, `settle`, `running_total_bound`, and the F14 counterexample.
2. **HTLC failure scope (T2).** Add `FailReason`/`failWith` and the off-chain
   counterexample; reword `LN-HT-002` to the on-chain timeout scope. Keep
   `fail_only_after_expiry`.
3. **Promote close conservation (T3)** as `LN-CH-008` using the existing
   declarations. No new proof is required unless the catalog checker wants a
   single wrapper name.
4. **Promote persistence recovery (T4)** as `LN-PR-007` using the existing
   declarations. Keep the `Consistent` hypotheses visible.

Expected catalog effect: 51 → 53 rows (two promotions), with three rows
reworded (`LN-PM-004`, `LN-PM-005`, `LN-HT-002`). If the parent prefers not to
change row count, fold the close/persistence targets into
`LN-CH-001`/`LN-PR-005` instead; the important part is that the statements
become visible.

### 6.2 Defer to a separately chartered lane

* **T5 macaroon auth** — small, faithful, but a server-auth model, not BOLT.
  Launch it only with an explicit server-model charter.
* **T6 held payments** and **T7 event queues** — runtime semantics; they belong
  with the LDK Node/Server behavioral lane, not the protocol catalog.
* **T8 splicing** — requires maintainer sign-off because it changes the meaning
  of channel funding. Do not mutate `Channel`/`Ledger` in a repair lane.

### 6.3 Treat as external

Do not create Lean rows for real secp256k1/EUF-CMA, Noise_XK/AEAD,
computational reductions, PoW finality, watchtower services, LSPS2 provider
operation, BOLT 12 offers/refunds/async payments, or on-chain RBF. These are
either new protocol stacks or external implementations. Record them in
`docs/OPEN-ISSUES.md` as barriers, not as `statementOnly` rows that will never
close.

### 6.4 Process recommendation

The catalog checker proves name resolution and sorry-freeness, not claim
strength. Add a lightweight claim-vs-statement review to each promotion:

* quote the English claim and the exact theorem statement side by side;
* list every hypothesis in the theorem and say which word of the claim it
  corresponds to;
* keep a counterexample or witness for each non-trivial scope narrowing;
* reject any row whose claim uses "exactly", "only", or "all" unless the
  statement has the corresponding universal/exact form.

This is the cheapest way to prevent another `LN-PM-004`/`LN-HT-002` situation.

## 7. Evidence and commands

### 7.1 Pin verification

```sh
git -C /tmp/opencode/ldk-refs/ldk-node rev-parse HEAD
# fa123fed131e27ecc420b77fa7086fcf1ddaebb8
git -C /tmp/opencode/ldk-refs/ldk-server rev-parse HEAD
# c17dc11dde38f88c53457039ddf30c6b90a63ba2
git -C /home/ubuntu/ln-lean-repair rev-parse HEAD
# f7f062817c185cd70004bb26c652deb99c6fd4bd
```

### 7.2 Catalog extraction

```sh
cd /home/ubuntu/ln-lean-repair
python3 scripts/check-catalog.py
# summary: rows=51 proved=51 statementOnly=0 targets=294
#          unresolved=0 proved_failures=0 declarations=11898
python3 - <<'PY'
import re, collections
src = open('LnLean/Proofs/Obligations.lean').read()
rows = re.findall(
    r'\{ id := "(LN-[A-Z0-9-]+)", domain := \.(\w+),\s*'
    r'claim := "(.*?)",\s*leanTarget := "(.*?)",\s*status := \.(\w+)',
    src, re.S)
targets = [t.strip() for r in rows for t in r[3].split(';') if t.strip()]
print(len(rows), len(targets), len(set(targets)))
print(collections.Counter(r[1] for r in rows))
PY
```

### 7.3 Statement and evidence inspection

```sh
rg -n 'theorem Ledger.step_conserves|structure Ledger|theorem partial_synchrony_delivers' \
  LnLean/Security/Invariants.lean
rg -n 'def mppComplete|theorem running_total_bound' LnLean/Payment/MPP.lean
rg -n 'overTotal_counterexample|overTotalPlan' LnLean/Proofs/ModelHardening/F14.lean
rg -n 'cooperativeClose_conserved|unilateralClose_conserved|closePaths_totals_agree' \
  LnLean/Proofs/PhaseC3/CloseConservation.lean
rg -n 'restore_replay_suffix|recovery_no_rollback_reestablish' \
  LnLean/Proofs/PhaseC3/PersistenceRecovery.lean
rg -n 'def Route.amountAt|theorem Route.amountAt' \
  LnLean/Proofs/Routing/RouteBlindingProps.lean
```

### 7.4 LDK evidence

```sh
sed -n '380,390p' refs/bolts/04-onion-routing.md
sed -n '424,433p' refs/bolts/04-onion-routing.md
sed -n '7314,7322p' refs/rust-lightning/lightning/src/ln/functional_tests.rs
sed -n '9870,9890p' refs/rust-lightning/lightning/src/ln/channelmanager.rs
sed -n '990,1035p' /tmp/opencode/ldk-refs/ldk-node/src/lib.rs
sed -n '1000,1058p' /tmp/opencode/ldk-refs/ldk-node/src/event.rs
sed -n '25,105p' /tmp/opencode/ldk-refs/ldk-server/ldk-server/src/macaroons/policy.rs
sed -n '325,345p' /tmp/opencode/ldk-refs/ldk-server/docs/api-guide.md
sed -n '395,408p' /tmp/opencode/ldk-refs/ldk-server/docs/api-guide.md
sed -n '437,480p' /tmp/opencode/ldk-refs/ldk-server/ldk-server/src/service.rs
```

### 7.5 What was not run

No `lake build`, `lake env lean`, `cargo test`, or cargo fetch was run. All
inspection was read-only `git`, `rg`, `sed`, `wc`, `ls`, and Python parsing.
No file outside this report was modified.
