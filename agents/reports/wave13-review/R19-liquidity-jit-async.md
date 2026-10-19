# R19 — Liquidity, LSPS, JIT channels, and async payments
**Status:** read-only review
**Pins:** LDK Node `fa123fed131e27ecc420b77fa7086fcf1ddaebb8`, LDK Server `c17dc11dde38f88c53457039ddf30c6b90a63ba2`
**Review branch:** `repair/integrated` (no branch, commit, or non-report file changes made)

## 1. Scope and current Lean surface

This lane covers single-channel liquidity accounting, the BOLT 2
`update_add_htlc` reserve/in-flight guards, LSPS2/JIT channel acquisition,
on-chain anchor reserves, and asynchronous-payment storage/rate-limit
behavior. It does **not** re-review route construction (`R16`), BOLT 11
wire encoding (`R10`), BOLT 12 offers (`R11`), MPP recipient accounting
(`R12`), channel lifecycle (`R05`), or wallet UTXO selection (`R04`). Those
surfaces appear only where they constrain a liquidity claim.

Short verdict: **the tree contains a real but internally inconsistent
single-channel liquidity calculus, and no model at all of LSPS2, JIT
channels, on-chain anchor reserves, or async payments.** The inconsistency
is not a missing proof: two root-imported guards accept different updates
for the same channel, and the `LiquidityProps` reserve convention is the
opposite of BOLT 2 and of every other reserve module in the tree.

### 1.1 Current claim surface

| Module | Relevant declarations | Catalog status | What it actually establishes |
|---|---|---|---|
| `LnLean/Proofs/Payment/LiquidityProps.lean` | `reserveMsat` `:110`, `remoteReserveMsat` `:114`, `reserveOf` `:133`, `availableOutbound` `:152`, `availableInbound` `:156`, `sumByDirection` `:295`, `maxHtlcValue` `:328`, `addHtlc?` `:376`, `step_preserves_balance` `:567`, `planFits` `:618` | Root-imported (`LnLean.lean:107`, `Common.lean:63`); **no catalog row**, no theorem-index or traceability entry, not in `AxiomAudit` | Balance complementarity and a per-direction in-flight algebra. **Both** reserve sides are inverted: `reserveMsat` uses `localEndpoint` (`:110-111`) and `remoteReserveMsat` uses `remoteEndpoint` (`:114-115`), while BOLT 2 requires the opposite in each case. Consequently `availableOutbound`, `availableInbound`, `MeetsReserve`, `MeetsRemoteReserve`, `planFits`, and both branches of `addHtlc?` use the advertiser's own reserve rather than the reserve the peer requires. `sumByDirection` is per-direction but sums every HTLC regardless of state, including terminal ones. `addHtlc?` also omits the positive-amount, `htlc_minimum_msat`, and CLTV checks. |
| `LnLean/Channel/State.lean` | `pendingHtlcValueOf` `:266`, `offeringReserveSat` `:280`, `receiverParams` `:285`, `AffordableAdd` `:300`, `updateAddHtlc` `:323`, `UpdateStep` `:414` | Used by `StateTransitionTargets`, `E37`, `D14`; no catalog row of its own | Correct peer-advertised reserve guard, but `withinInFlight` sums **both** directions (`pendingHtlcValueOf + amount`). BOLT 2 and LDK cap only the HTLCs offered in the relevant direction. The `update_add_htlc` constructor is therefore over-strict. |
| `LnLean/Proofs/Channel/ReserveProps.lean` | `localReserveSat` `:103`, `remoteReserveSat` `:108`, `ReserveInvariant` `:118` | No catalog row; root-imported (`LnLean.lean:68`) | The BOLT-correct reserve convention: `localReserveSat c = c.remoteEndpoint.params.channelReserveSat`, `remoteReserveSat c = c.localEndpoint.params.channelReserveSat`. This is the reference definition the rest of the tree should use. |
| `LnLean/Proofs/ModelHardening/F11.lean` | `waveF_f11_inFlightFor` `:129`, `waveF_f11_capFor` `:139`, `waveF_f11_Admissible` `:172`, preservation `:258` and `:306`, negative witness `:344` | Root-imported (`LnLean.lean:97`, `Common.lean:54`); **not catalogued or axiom-audited** | The most complete add predicate in the tree for the modelled parameters: correct peer reserve, per-direction in-flight, positive amount, `htlc_minimum_msat`, and CLTV. It still omits the `max_accepted_htlcs` count cap, which `ChannelParams` does not carry. It is effectively orphaned: no catalog row and no bridge from `State.AffordableAdd` or `LiquidityProps.addHtlc?`. |
| `LnLean/Proofs/WaveD/D14.lean` | `offeringReserveGuard` `:206`, `inFlightMsat` `:231`, `htlcCap` `:237`, `AdmissibleAdd` `:248`, `bounds` `:406` | Evidence for `LN-CH-006` | Correct reserve side and the dust-exposure arithmetic. The in-flight guard is pooled over both directions, so the row's "admissible update" is narrower than BOLT 2. The `bounds` theorem itself is true because the guard is stronger than necessary. |
| `LnLean/Proofs/WaveE/E37.lean` | `pendingValue` `:88`, `AffordableCommittedAdd` `:163` | Used by `StateTransitionTargets` | Local-only add model with the correct reserve (`localReserveSat`) but a pooled `pendingValue` cap. Sound but incomplete with respect to BOLT 2. |
| `LnLean/Proofs/Channel/StateTransitionTargets.lean` | `pendingHtlcValueOf_updateAddHtlc` `:247`, `committedAdd_eq_updateAddHtlc` `:351`, `affordableAdd_implies_e37` `:357`, `updateStep_preserves_reserve` `:575` | No catalog row | Mechanized ledger/reserve preservation for the additive `UpdateStep` layer. It inherits the pooled in-flight guard from `State` and `E37`. |
| `LnLean/Proofs/Channel/ProtocolEventFoldTargets.lean` | `affordable_add_changes_balance` `:656`, `fold_cannot_both_preserve_balance_and_carry_add` `:696`, `fold_cannot_both_preserve_htlcs_and_carry_add` `:712` | No catalog row | The correct boundary: `Step` cannot be made to carry an affordable add without falsifying the balance/HTLC invariants that `LiquidityProps`, `D14`, and `F03` rely on. This must be retained. |
| `LnLean/Proofs/Payment/InvoiceWireTargets.lean` | `WireFields.routeHints` `:480-497` | `LN-PM-007` evidence | BOLT 11 tagged-field wire model with route hints and `min_final_cltv_expiry`. There is no payment-metadata field and no LSPS2 fee-promise semantics. |
| Async/LSPS/JIT module | — | — | No `LnLean/Liquidity`, no LSPS2, no JIT, no async-payment, no anchor-reserve declarations. Grep for `lsps`, `jit`, `opening_fee`, `intercept_scid`, `mailbox`, `static_invoice`, `anchor reserve`, and `unified` over `LnLean/**/*.lean` returns no hits. |

### 1.2 Catalog reality

The only catalog row that touches this lane is `LN-CH-006`
(`LnLean/Proofs/Obligations.lean:205-209`):

> "HTLC exposure and channel reserve bounds are respected by admissible
> updates." — `LnLean.Channel.Reserve.bounds`

`docs/THEOREM-INDEX.md:54` and `docs/TRACEABILITY.md:33` repeat that row.
The row is true for D14's `AdmissibleAdd`, but its guard is not the BOLT 2
guard: `D14.inFlightMsat` (`:231-232`) sums both directions. Therefore the
row should not be read as "the model enforces the BOLT 2 in-flight rule".
`LiquidityProps` and `F11` have no catalog row, no theorem-index entry, no
traceability anchor, and no `#print axioms` line in
`LnLean/Proofs/PhaseC3/AxiomAudit.lean`. Their theorems are real Lean
theorems, but they are outside the audited claim surface.

The payment rows `LN-PM-001..007` (`Obligations.lean:357-405`) cover invoice
hashing/signatures/wire fields and MPP sum bounds. `LN-PM-004/005` do not
mention liquidity, JIT, or in-flight HTLCs. There is no row for LSPS2, JIT
channels, anchor reserves, unified send, or async payments.

### 1.3 The convention conflict in one table

| Module | What the local side must keep | What the remote side must keep | In-flight cap |
|---|---|---|---|
| `LiquidityProps` | `localEndpoint.params.channelReserveSat` — **wrong side** | `remoteEndpoint.params.channelReserveSat` — **wrong side** | per direction — correct |
| `State.AffordableAdd` | `remoteEndpoint.params.channelReserveSat` — correct | `localEndpoint.params.channelReserveSat` — correct | pooled — **wrong** |
| `D14.AdmissibleAdd` | `localReserveSat = remoteEndpoint` — correct | `remoteReserveSat = localEndpoint` — correct | pooled — **wrong** |
| `E37.AffordableCommittedAdd` | `localReserveSat = remoteEndpoint` — correct | not modelled | pooled — **wrong** |
| `F11.waveF_f11_Admissible` | `localReserveSat = remoteEndpoint` — correct | `remoteReserveSat = localEndpoint` — correct | per direction — correct |

`ReserveProps.localReserveSat` (`:103-104`) and
`State.offeringReserveSat` (`:280-282`) already encode the BOLT-correct
mapping. The root cause of the `LiquidityProps` error is visible in the
field documentation: `ChannelParams.channelReserveSat` is described as
"the minimum balance kept on this side" (`Types.lean:80-81`), and the module
docstring says "Each side must keep `channel_reserve_satoshis` ... in its own
balance" (`LiquidityProps.lean:9-17`). BOLT 2 says the opposite: the value is
"the minimum amount that the other node is to keep as a direct payment"
(`refs/bolts/02-peer-protocol.md:734-737`; rationale at `:884-887`). The
comment is therefore part of the defect, not just the code.

## 2. LDK datapoints (with `file:line`)

Unless stated otherwise, paths are in the pinned read-only clones. The
repository's own rust-lightning anchor is
`fe4900930c6bd5786ec4203274d7cf312776a5a6`; LDK Node pins its
`lightning`/`lightning-liquidity` dependencies to
`d7a980641c6325ddda5072a0f470ef8392676cf5`
(`/tmp/opencode/ldk-refs/ldk-node/Cargo.toml:89-98`). The local
`lightning-liquidity` snapshot used for `compute_opening_fee` has no `.git`;
the authoritative pin is the `Cargo.toml` line, not the snapshot.

### 2.1 JIT receive API and invoice construction

* LDK Node exposes fixed-amount, variable-amount, and `_for_hash` JIT
  receive calls (`ldk-node/src/payment/bolt11.rs:649-803`). The inner
  dispatcher chooses `lsps2_receive_to_jit_channel` for a fixed amount and
  `lsps2_receive_variable_amount_to_jit_channel` for a variable amount
  (`:128-167`).
* The returned object is an ordinary BOLT 11 invoice. The route hint uses
  the LSP's `intercept_scid`, zero fees, the LSP's `cltv_expiry_delta`, and
  no HTLC min/max (`ldk-node/src/liquidity/client/lsps2.rs:384-397`).
  `min_final_cltv_expiry_delta` is `MIN_FINAL_CLTV_EXPIRY_DELTA + 2`
  (`:353`).
* The invoice's payment metadata is `LSPS2Parameters` with
  `max_total_opening_fee_msat = Some(chosen_fee)` for fixed-amount invoices,
  or `max_proportional_opening_fee_ppm_msat = Some(chosen_ppm)` for
  variable-amount invoices (`client/lsps2.rs:113-136`, `:180-186`). The
  "max" field carries the selected menu fee, not the user's limit.
* The `_for_hash` variants require the caller to handle `PaymentClaimable`
  manually: the node emits the event, and the caller **must** claim via
  `claim_for_id` when it has the preimage, or immediately `fail_for_id`
  otherwise; reusing a payment hash is explicitly unsafe
  (`payment/bolt11.rs:630-640`, `:687-700`). The fee-skim check is performed
  in the event handler before the payment is surfaced: a skim above the
  invoice metadata limit, or a skim without valid LSPS2 metadata, causes
  `fail_claimable_payment` (`ldk-node/src/event.rs:1058-1105`).
* The integration test confirms the fee skim and channel-size chain:
  `service_fee_msat = jit_amount_msat * channel_opening_fee_ppm / 1_000_000`,
  `expected_channel_size_sat = (received + received *
  over_provisioning_ppm / 1_000_000) / 1000`, and
  `counterparty_skimmed_fee_msat = Some(service_fee_msat)`
  (`tests/integration_tests_rust.rs:5519-5554`). A payer that re-signs a
  smaller invoice is rejected: the service emits `PaymentFailed` and the
  client never emits `PaymentClaimable`
  (`tests/integration_tests_rust.rs:5571-5618`).
* The multi-LSP test confirms cheapest-offer selection independent of
  registration order (`tests/integration_tests_rust.rs:7009-7096`).
* LDK Server is a thin API mapping only: it converts the description and
  forwards to `receive_via_jit_channel`, `..._for_hash`, or the
  variable-amount variant
  (`ldk-server/src/api/bolt11_receive_via_jit_channel.rs:28-95`).

### 2.2 LSPS2 client fee selection

* The client gathers all LSPS2 offers, flattens each opening-fee menu,
  filters entries by `min_payment_size_msat ≤ amount ≤
  max_payment_size_msat`, computes the fee, and selects the first minimum
  with `min_by_key` (`ldk-node/src/liquidity/client/lsps2.rs:64-104`).
* `compute_opening_fee` is `max(ceil(payment * proportional / 1_000_000),
  min_fee_msat)`; it returns `None` on `u64` multiplication overflow
  (`lightning-liquidity/src/lsps2/utils.rs:60-68` at the ldk-node pin;
  the local snapshot root is
  `/tmp/opencode/rl-live/rust-lightning/`, and later
  `lightning-liquidity/...` citations are relative to it).
  The client drops `None` offers via `filter_map` (`client/lsps2.rs:86-90`).
* The fixed-amount path checks the user's absolute fee limit only after
  choosing the cheapest offer: `min_total_fee_msat >
  max_total_lsp_fee_limit_msat` returns `Error::LiquidityFeeTooHigh`
  (`client/lsps2.rs:97-104`).
* The variable-amount path is different: it does not filter by payment-size
  window (there is no amount), selects by the **proportional ppm alone**
  (`:149-159`), and checks only
  `max_proportional_lsp_fee_limit_ppm_msat` (`:166-173`). A higher-ppm offer
  can therefore have a lower absolute fee at a given amount; the variable
  path does not optimize absolute fee.
* The service also enforces its own `min_payment_size_msat` /
  `max_payment_size_msat` on the buy request
  (`ldk-node/src/liquidity/service/lsps2.rs:340-372`).
* At the protocol helper
  (`lightning-liquidity/src/lsps2/service.rs`), the actual skim is also
  `compute_opening_fee(expected_payment_size_msat, min_fee_msat,
  proportional)`, and `amt_to_forward_msat =
  expected_payment_size_msat.saturating_sub(opening_fee_msat)`. The channel
  is opened only if `total_expected_outbound_amount_msat >=
  expected_payment_size_msat` and `amt_to_forward_msat > 0`, i.e. the fee
  is strictly less than the payment (`:257-275` at the ldk-node pin);
  forwarding additionally requires
  `skimmed_fee_msat >= opening_fee_msat` (`:436-458`).

### 2.3 LSPS2 service channel-size arithmetic

* The service configuration carries `channel_opening_fee_ppm`,
  `channel_over_provisioning_ppm`, `min_channel_opening_fee_msat`,
  `min_payment_size_msat`, `max_payment_size_msat`,
  `client_trusts_lsp`, and `disable_client_reserve`
  (`ldk-node/src/liquidity/service/lsps2.rs:55-108`).
* On `OpenChannel`, it computes
  `over_provisioning_msat = amt_to_forward_msat * over_provisioning_ppm /
  1_000_000` and `channel_amount_sats = (amt_to_forward_msat +
  over_provisioning_msat) / 1000` — both truncating integer divisions
  (`:447-451`).
* It then computes `cur_anchor_reserve_sats =
  total_anchor_channels_reserve_sats(...)`, `spendable_amount_sats =
  wallet.get_spendable_amount_sats(cur_anchor_reserve_sats)`,
  `additional_reserve_required = new_channel_anchor_reserve_sats(...)`,
  and rejects if `spendable_amount_sats < channel_amount_sats +
  additional_reserve_required` (`:452-473`).
* The channel amount is therefore not guaranteed to cover the forwarded
  payment. With `amt_to_forward_msat = 1001` and zero over-provisioning,
  `channel_amount_sats = 1` (1000 msat), which is less than the amount to
  forward. Even at 100,000 ppm over-provisioning, 1001 msat yields 100 msat
  of over-provisioning, 1101 msat total, and still a 1-sat channel. The
  service's funds check does not detect this; it only checks that the wallet
  can fund the computed (possibly undersized) channel plus the reserve.

### 2.4 On-chain anchor reserve and unified send

* `OnchainSendAmount` distinguishes `ExactRetainingReserve`,
  `AllRetainingReserve`, and `AllDrainingReserve`
  (`ldk-node/src/wallet/mod.rs:84-86`).
* The public single send always uses `ExactRetainingReserve` with the
  current anchor reserve (`payment/onchain.rs:44-53`).
  `send_all_to_address(retain_reserves = true)` uses
  `AllRetainingReserve`; `retain_reserves = false` uses
  `AllDrainingReserve` and is documented as potentially dangerous for open
  anchor channels (`payment/onchain.rs:91-116`).
* `trusted_spendable` is reduced by the total anchor reserve:
  `spendable = trusted_spendable - total_anchor_channels_reserve_sats`
  (`wallet/mod.rs:1995-2009`). The exact send re-checks
  `spendable_amount_sats < amount_sats + tx_fee_sats` and returns
  `InsufficientFunds` (`wallet/mod.rs:2261-2280`). The all-retaining path
  re-checks the drain amount against the same spendable figure
  (`:2281-2298`). The all-draining path has no reserve check
  (`:2337-2342`).
* The total reserve is the number of eligible channels times
  `per_channel_reserve_sats`. Eligibility excludes peers in
  `trusted_peers_no_reserve`, channels whose shutdown is complete, and
  non-anchor channel types (`ldk-node/src/lib.rs:2717-2734`).
  `new_channel_anchor_reserve_sats` returns zero for non-anchor channels and
  trusted peers, otherwise `per_channel_reserve_sats` (`:2736-2758`).
* The integration tests confirm the arithmetic: with a 25,000-sat
  `per_channel_reserve_sats`, a fully spent on-chain balance leaves
  `total_anchor_channels_reserve_sats` equal to 25,000 (or 24,999 after
  rounding) and `spendable_onchain_balance_sats = 0`
  (`tests/integration_tests_rust.rs:6835-6920`); after a splice, the
  remaining on-chain balance stays near the reserve (`:6978-7005`).
* Unified send parses BIP 21/BIP 353 instructions, sorts methods as BOLT 12
  first, BOLT 11 second, on-chain third, tries them in that order, and
  returns an on-chain txid only after a fallback-eligible Lightning failure
  (`ldk-node/src/payment/unified.rs:191-410`; ordering at `:284-298`,
  results at `:327`, `:358`, `:405`). `DuplicatePayment`, `NotRunning`, and
  `PersistenceFailed` abort instead of falling through, to avoid a double
  payment. The server is a thin mapping
  (`ldk-server/src/api/unified_send.rs:20-39`).

### 2.5 Asynchronous payments

* Async payments are experimental and role-configured at the builder
  (`ldk-node/src/builder.rs:665-681`; `AsyncPaymentsRole::Server` requires
  announced channels). The receive side is a BOLT 12 offer built against a
  static-invoice server (`payment/bolt12.rs:635-680`), with blinded paths
  configured via `set_paths_to_static_invoice_server` (`:681-717`).
* The mailbox keeps at most 30 messages per peer and 300 peers; on a full
  per-peer queue it drops the oldest message, and on the peer limit it
  evicts the peer with the longest queue
  (`payment/asynchronous/om_mailbox.rs:12-33`).
* Static invoices are keyed by `sha256(recipient_id)` in a secondary
  namespace and a five-digit `invoice_slot` key; both get and persist are
  rate-limited (`payment/asynchronous/static_invoice_store.rs:43-45`,
  `:64-143`).
* The rate limiter is a leaky bucket with capacity 5, refill every 100 ms,
  and max idle 600 s, with at most 10,000 tracked users and garbage
  collection of idle buckets (`payment/asynchronous/rate_limiter.rs:13-26`,
  `:34-76`).
* LDK Server exposes only the async-payments **role** in configuration
  (`ldk-server/src/util/config.rs:79`; `main.rs:235`); it has no async
  receive/mailbox/static-invoice API. The 45 API handlers include JIT and
  unified send but no async-payment endpoint.

### 2.6 BOLT anchors

* BOLT 2 defines `channel_reserve_satoshis` as the minimum the **other**
  node must keep (`refs/bolts/02-peer-protocol.md:734-737`), and the
  rationale confirms "The *channel reserve* is specified by the peer's
  `channel_reserve_satoshis`" (`:884-887`).
* `max_htlc_value_in_flight_msat` is "a cap on total value of outstanding
  HTLCs offered by the remote node" (`:739-741`), i.e. one direction.
* A sender MUST offer an amount greater than zero, MUST NOT offer below the
  receiving node's `htlc_minimum_msat`, and MUST set `cltv_expiry <
  500000000` (`:2815-2830`).
* The async-payments flow is not in the pinned BOLT tree; the LDK Node
  builder points to the draft at `lightning/bolts` PR 1149
  (`builder.rs:668-669`). It is therefore a draft/implementation surface,
  not a stable BOLT anchor.

## 3. Gap matrix

| Behavior | Lean status | LDK evidence | Gap / counterexample | Priority |
|---|---|---|---|---|
| Outbound/inbound complementarity | covered faithfully | not protocol-specific | `outbound_add_inbound_eq_total` (`LiquidityProps.lean:198-199`) and `inbound_eq_total_sub_outbound` (`:203-206`) are exact. | — |
| Local reserve convention | **contradicted** | BOLT 2 `:734-737`, `:884-887`; `ReserveProps.lean:103-104` | `LiquidityProps.reserveMsat` uses `localEndpoint` (`:110-111`). With local reserve 0, peer reserve 1 sat, local balance 1000 msat, local HTLC 1000 msat, and peer `maxHtlcValue` 1000 msat, `LiquidityProps.addHtlc?` returns `some`, while `State.AffordableAdd.leavesReserve` is false (`1 * 1000 + 1000 ≤ 1000` fails). BOLT 2 rejects the add. | **P0** |
| Remote reserve convention | **contradicted** | BOLT 2 `:734-737`; `ReserveProps.lean:108-109` | `reserveOf c .remote = remoteReserveMsat = remoteEndpoint.params.channelReserveSat` (`:114-115`, `:133-135`) is the reserve the remote endpoint advertised for the local side, not the reserve the peer must keep. The correct side is `localEndpoint.params.channelReserveSat`. Symmetric counterexample: local reserve 1000 sat, peer reserve 0, remote balance 1000 sat; the peer must keep 1,000,000 msat and has exactly 1,000,000, while `availableInbound` reports 1,000,000 available because it subtracts 0. | **P0** |
| `availableOutbound` / `availableInbound` | **contradicted for both** | BOLT 2 `:734-737`; LDK `get_available_balances_for_scope` (`refs/rust-lightning/lightning/src/ln/channel.rs:6552-6605`) | `availableOutbound = localBalance - reserveMsat` (`:152-153`) subtracts the wrong reserve. With local reserve 0, peer reserve 1000 sat, local balance 1000 sat, `availableOutbound = 1,000,000 msat` but the true spendable amount is 0. `availableInbound` (`:156-157`) is wrong for the mirror reason: with local reserve 1000 sat, peer reserve 0, remote balance 1000 sat, it reports 1,000,000 msat although the peer must keep all 1,000,000. `planFits` (`:618-620`) inherits the outbound error, so a 1,000,000-msat MPP plan passes although every part would violate the peer's reserve. | **P0** |
| `addHtlc?` positive amount / `htlc_minimum_msat` / CLTV | **partially covered / contradicted** | BOLT 2 `:2815-2830`; `State.AffordableAdd` `:302-307` | `addHtlc?` checks only the in-flight cap and reserve (`:376-384`). It accepts `amount = 0`, `amount < receiver htlcMinimum`, and `cltvExpiry ≥ 500000000`, all of which BOLT 2 forbids. `AffordableAdd` has the missing checks; the executable function does not. | **P1** |
| HTLC count cap `max_accepted_htlcs` | **missing / unmodelled parameter** | BOLT 2 `:2825-2827`; `Types.lean:80-87` | `ChannelParams` has no `max_accepted_htlcs`, so none of `AffordableAdd`, `D14.AdmissibleAdd`, `E37.AffordableCommittedAdd`, or `F11.waveF_f11_Admissible` enforces the count cap. Do not claim any of them is the full BOLT 2 add predicate. | P2 (model extension) |
| `addHtlc?` vs `updateAddHtlc` refinement | **missing / unbridged** | BOLT 2 `:2815-2830`; `State.lean:323-341` | `addHtlc?` prepends (`h :: c.htlcs`, `:380-382`); `updateAddHtlc` appends (`c.htlcs ++ [h]`, `:334-339`). No theorem links them. For `c.htlcs = [x]`, adding `h` gives `[h, x]` versus `[x, h]`; the states are permutation-equivalent but not equal. There is no `addHtlc? = some c' → c' = updateAddHtlc ...` theorem. | **P1** |
| Per-direction in-flight cap | **contradicted in `State`/`D14`/`E37`; directionally correct but not pending-only in `LiquidityProps`; faithful in `F11`** | BOLT 2 `:739-741`; LDK `channel.rs:5861-5871` filters `!htlc.outbound` before comparing to `holder_max_htlc_value_in_flight_msat` | `State.pendingHtlcValueOf` sums both directions (`:266-269`), and `AffordableAdd.withinInFlight` uses it (`:315-316`). With an existing remote-offered 600-msat HTLC, a 1000-msat receiver cap, and a new local 500-msat HTLC, BOLT 2 allows the add (local-offered total 0 + 500 ≤ 1000) and `LiquidityProps.addHtlc?` returns `some`; `AffordableAdd` rejects it (600 + 500 > 1000). `D14.inFlightMsat` (`:231-232`) and `E37.pendingValue` (`:88-96`) have the same pooled bug. `F11.waveF_f11_inFlightFor` (`:129-133`) is per-direction and pending-only. `LiquidityProps.sumByDirection` (`:295-298`) is per-direction but sums terminal as well as pending HTLCs; a settled 600-msat local HTLC plus a new 500-msat local HTLC is rejected under a 1000-msat cap although nothing is in flight. | **P0** (pooled); **P1** (terminal overcount) |
| Pooled ledger conservation | covered faithfully | BOLT 3 conservation, not a cap | `pendingHtlcValueOf` is the right quantity for `ledgerValue` and `E37` conservation; it is the wrong quantity for the per-direction cap. Keep it for the ledger, add a directional projection for the cap. | — |
| Reserve preservation by `Step` | covered but unit-like | BOLT 2 `:884-887` | `step_preserves_meetsReserve` (`LiquidityProps.lean:577-581`) is true because `Step` leaves balances unchanged. It does not establish that an add preserves the reserve; `StateTransitionTargets.updateStep_preserves_reserve` (`:575`) does, conditional on `AffordableAdd`. | P2 |
| MPP `planFits` | partially covered | BOLT 4 MPP; BOLT 7 `short_channel_id` | `planFits` is channel-agnostic by design (`:91-93`) and uses the wrong outbound reserve. It also has no `htlc_minimum_msat`, no in-flight subtraction, and no path/channel resolution. | P1 |
| JIT invoice construction | **missing at the semantic layer**; partial BOLT 11 shape | `bolt11.rs:128-167`, `:649-803`; `client/lsps2.rs:343-397` | The tree can represent BOLT 11 route hints (`InvoiceWireTargets.lean:480-497`) and `min_final_cltv_expiry`, but not LSPS2 payment metadata, the fee promise, the `intercept_scid` route hint, or the `MIN_FINAL_CLTV_EXPIRY_DELTA + 2` rule. A JIT invoice is not a new wire type, so a model must not invent one. | P2 |
| JIT manual claim/fail | **missing adapter** | `bolt11.rs:630-640`, `:687-700` | `Payment.settle`/`settle_terminal_fixed` (`LnLean/Payment/HTLC.lean:136-159`, `LnLean/Payment/Laws.lean:225-243`) already prove settle-once/absorbing, but there is no adapter from the JIT `PaymentClaimable` event to that session state, and no proof that `claim_for_id` and `fail_for_id` are mutually exclusive. | P2 |
| LSPS2 client fee selection | **missing** | `client/lsps2.rs:64-104`, `:113-136`, `:140-190`; `lightning-liquidity/src/lsps2/utils.rs:60-68` | No finite offer menu, no payment-size window, no `compute_opening_fee`, no cheapest selection, no absolute fee-limit check, no distinction between the fixed-amount (absolute fee) and variable-amount (ppm-only) paths. | P1 (finite model) |
| LSPS2 service channel arithmetic | **missing** | `service/lsps2.rs:447-473`; `lightning-liquidity/src/lsps2/service.rs:248-285` | No over-provisioning arithmetic, no floor-division channel amount, no funds/reserve check, and no `amt_to_forward > 0` condition. The floor can produce a channel smaller than the forwarded payment. | P2 |
| On-chain anchor-reserve exact spend | **missing** | `wallet/mod.rs:84-86`, `:1995-2009`, `:2261-2280`; `lib.rs:2717-2758`; `onchain.rs:44-53` | No model of `trusted_spendable - reserve`, the exact amount+fee check, the eligible-channel count, or `new_channel_anchor_reserve_sats`. The arithmetic is finite and faithful. | P2 |
| On-chain all-draining spend | **missing** | `onchain.rs:91-116`; `wallet/mod.rs:2337-2342` | No model of the dangerous `retain_reserves = false` path, which can spend the anchor reserve. A finite counterexample is available. | P2 |
| Unified send routing/fallback | **missing / external** | `unified.rs:191-410`; `ldk-server/api/unified_send.rs:20-39` | Method ordering (BOLT 12, BOLT 11, on-chain), amount checks, and fallback are control-flow policy. A finite model can describe the order but not the asynchronous failures that trigger fallback. | — |
| Async mailbox / static-invoice store / rate limiter | **missing** | `om_mailbox.rs:12-33`; `static_invoice_store.rs:43-145`; `rate_limiter.rs:13-76` | No mailbox bounds, no eviction policy, no key scheme, no leaky-bucket model. These are implementation policies; the SHA-256 key and real clock are external. | P2 |
| Async payment protocol safety/liveness | **unmodelled / external** | `builder.rs:665-681`; `payment/bolt12.rs:635-717`; draft PR 1149 | The async-payments state machine, static-invoice-server interaction, blinded-path privacy, offline delivery, and timers are not modelled. Experimental; no BOLT anchor. | — |
| LSP fee promise / trust model | **unmodelled / external** | `lightning-liquidity/src/lsps2/utils.rs:20-58` (`is_valid_opening_fee_params`, expiry); `service/lsps2.rs:89-107` (`client_trusts_lsp`, `disable_client_reserve`) | The HMAC promise, `valid_until`, `min_lifetime`, `max_client_to_self_delay`, and the two trust models are cryptographic/time/policy assumptions. Do not claim JIT safety from the fee arithmetic alone. | — |

## 4. Proposed targets

The names below are proposals; none exists in the tree today. They are
additive unless marked "model correction". Path suggestions are given for
the parent; only the parent should root-import them or add them to
`AxiomAudit`.

### T1 — `LnLean.Proofs.Payment.LiquidityReserveTargets.reserveOf_eq_offeringReserve`
**Priority: P0. Fidelity risk: low. Feasibility: high. Model correction: yes.**

Repair the two reserve definitions in `LiquidityProps` to the BOLT-correct
side, then prove the bridge to the already-correct `State`/`ReserveProps`
convention:

```lean
namespace LnLean.Proofs.Payment

/-- The reserve the peer advertised, i.e. the reserve this side must keep. -/
def reserveMsat (c : Channel) : Nat :=
  c.remoteEndpoint.params.channelReserveSat * Msat.MSAT_PER_SAT

/-- The reserve the local side advertised, i.e. the reserve the peer must keep. -/
def remoteReserveMsat (c : Channel) : Nat :=
  c.localEndpoint.params.channelReserveSat * Msat.MSAT_PER_SAT

theorem reserveOf_eq_offeringReserve (c : Channel) (d : Direction) :
    reserveOf c d = offeringReserveSat c d * Msat.MSAT_PER_SAT := by
  cases d <;> rfl

theorem addHtlc?_some_meetsPeerReserve {c c' : Channel} {h : HTLC}
    (hs : addHtlc? c h = some c') :
    match h.direction with
    | .local =>
        c.remoteEndpoint.params.channelReserveSat * Msat.MSAT_PER_SAT ≤
          c'.balance.localBalance.val
    | .remote =>
        c.localEndpoint.params.channelReserveSat * Msat.MSAT_PER_SAT ≤
          c'.balance.remoteBalance.val

/-- Regression witness: the old `.local` side accepted an add that violates
    the peer's advertised reserve. -/
def legacyReserveMsat (c : Channel) : Nat :=
  c.localEndpoint.params.channelReserveSat * Msat.MSAT_PER_SAT

theorem legacy_reserve_accepts_violation :
    ∃ (c : Channel) (h : HTLC),
      h.direction = .local ∧
      sumByDirection h.direction c.htlcs + h.amount.val ≤
        maxHtlcValue c h.direction ∧
      legacyReserveMsat c + h.amount.val ≤ c.balance.localBalance.val ∧
      offeringReserveSat c h.direction * Msat.MSAT_PER_SAT + h.amount.val >
        c.balance.localBalance.val
```

Hypotheses: none beyond `h.direction` in the witness. Non-vacuity:
`localEndpoint.channelReserveSat = 0`, `remoteEndpoint.channelReserveSat = 1`,
`localBalance = 1000`, `h.amount = 1000`, `remoteEndpoint.maxHtlcValue =
1000`, `c.htlcs = []`. The old condition `0 + 1000 ≤ 1000` holds; the
BOLT condition `1000 + 1000 ≤ 1000` fails.

Why faithful: BOLT 2 `:734-737` and `:884-887` fix the semantics; the
correct mapping is already in `ReserveProps.lean:103-109` and
`State.offeringReserveSat:280-282`. This is a one-line-per-definition
correction plus a regression witness, not a new proof technique. It also
fixes `availableOutbound`, `availableInbound`, `MeetsReserve`,
`MeetsRemoteReserve`, and `planFits` automatically. The module docstring
(`:9-17`) and `Types.lean:80-81` must be corrected in the same change so
the wrong convention cannot recur.

### T2 — `LnLean.Proofs.Channel.InFlightDirectionTargets.affordableAdd_iff_bolt2_value_guards`
**Priority: P0. Fidelity risk: low. Feasibility: high. Model correction: yes.**

Add a directional projection and use it in `AffordableAdd` (and, as a
dependent change, `D14.AdmissibleAdd` and `E37.AffordableCommittedAdd`):

```lean
namespace LnLean.Channel

/-- Pending value offered by `d`, excluding settled HTLCs. -/
def pendingHtlcValueFor (c : Channel) (d : Direction) : Nat :=
  ((c.htlcs.filter (fun h =>
      h.direction = d ∧
        (h.state = HTLCState.offered ∨ h.state = HTLCState.received))).map
    (fun h => h.amount.val)).sum

theorem pendingHtlcValueOf_eq_add (c : Channel) :
    pendingHtlcValueOf c =
      pendingHtlcValueFor c .local + pendingHtlcValueFor c .remote

structure AffordableAdd (c : Channel) (dir : Direction) (amount : Msat)
    (cltvExpiry : Height) : Prop where
  positive : 0 < amount.val
  cltvBelowMaximum : cltvExpiry < MAX_CLTV_EXPIRY
  atLeastHtlcMinimum : (receiverParams c dir).htlcMinimum.val ≤ amount.val
  fitsOffered : amount.val ≤ (offeredBalance c dir).val
  leavesReserve :
    offeringReserveSat c dir * Msat.MSAT_PER_SAT + amount.val ≤
      (offeredBalance c dir).val
  withinInFlight :
    pendingHtlcValueFor c dir + amount.val ≤
      (receiverParams c dir).maxHtlcValue.val

theorem affordableAdd_iff_bolt2_value_guards (c : Channel) (dir : Direction)
    (amount : Msat) (cltv : Height) :
    AffordableAdd c dir amount cltv ↔
      (0 < amount.val ∧ cltv < MAX_CLTV_EXPIRY ∧
       (receiverParams c dir).htlcMinimum.val ≤ amount.val ∧
       amount.val ≤ (offeredBalance c dir).val ∧
       offeringReserveSat c dir * Msat.MSAT_PER_SAT + amount.val ≤
         (offeredBalance c dir).val ∧
       pendingHtlcValueFor c dir + amount.val ≤
         (receiverParams c dir).maxHtlcValue.val)

/-- The pooled guard is strictly stronger than BOLT 2. -/
theorem pooled_guard_rejects_bolt2_add :
    ∃ (c : Channel) (dir : Direction) (amount : Msat) (cltv : Height),
      0 < amount.val ∧ cltv < MAX_CLTV_EXPIRY ∧
      (receiverParams c dir).htlcMinimum.val ≤ amount.val ∧
      amount.val ≤ (offeredBalance c dir).val ∧
      offeringReserveSat c dir * Msat.MSAT_PER_SAT + amount.val ≤
        (offeredBalance c dir).val ∧
      pendingHtlcValueFor c dir + amount.val ≤
        (receiverParams c dir).maxHtlcValue.val ∧
      (receiverParams c dir).maxHtlcValue.val <
        pendingHtlcValueOf c + amount.val
```

Non-vacuity: an existing remote-offered 600-msat HTLC, a 1000-msat receiver
cap, and a new local 500-msat HTLC. BOLT 2 and `pendingHtlcValueFor c .local`
give `0 + 500 ≤ 1000`; the pooled guard gives `600 + 500 > 1000`. A positive
witness is the same channel with no remote HTLC: both guards accept 500.

Why faithful: BOLT 2 `:739-741` and LDK `channel.rs:5861-5871` filter
`!htlc.outbound` before comparing to `holder_max_htlc_value_in_flight_msat`.
`F11.waveF_f11_inFlightFor` (`:129-133`) already has the correct
implementation; the bridge target should prove
`AffordableAdd c dir amount cltv ↔ waveF_f11_Admissible c u` under
`c.phase = .normal`, with `u` carrying the same direction/amount/hash/CLTV.
This makes `F11` the reference predicate instead of an orphan. Keep the
pooled `pendingHtlcValueOf` for `ledgerValue` conservation; do not delete
it. The name says `value_guards` deliberately: BOLT 2's
`max_accepted_htlcs` count cap is not modelled (see §5.3), so this target
does not prove full `update_add_htlc` completeness.

### T3 — `LnLean.Proofs.Channel.AddRefinementTargets.addHtlc?_isSome_iff_affordableAdd`
**Priority: P1. Fidelity risk: low. Feasibility: medium. Model correction: yes.**

Make the executable add function the exact counterpart of
`AffordableAdd` and `updateAddHtlc`:

```lean
namespace LnLean.Proofs.Channel

def addHtlc? (c : Channel) (h : HTLC) : Option Channel :=
  if 0 < h.amount.val ∧ h.cltvExpiry < MAX_CLTV_EXPIRY ∧
     (receiverParams c h.direction).htlcMinimum.val ≤ h.amount.val ∧
     h.amount.val ≤ (offeredBalance c h.direction).val ∧
     offeringReserveSat c h.direction * Msat.MSAT_PER_SAT + h.amount.val ≤
       (offeredBalance c h.direction).val ∧
     pendingHtlcValueFor c h.direction + h.amount.val ≤
       (receiverParams c h.direction).maxHtlcValue.val
  then some (updateAddHtlc c h.direction h.amount h.paymentHash h.cltvExpiry)
  else none

theorem addHtlc?_isSome_iff_affordableAdd (c : Channel) (h : HTLC) :
    (addHtlc? c h).isSome ↔
      AffordableAdd c h.direction h.amount h.cltvExpiry

theorem addHtlc?_some_eq_updateAddHtlc {c c' : Channel} {h : HTLC}
    (hs : addHtlc? c h = some c') :
    c' = updateAddHtlc c h.direction h.amount h.paymentHash h.cltvExpiry
```

Hypotheses: none for the iff; `amount ≤ offeredBalance` and the reserve
guard are both retained explicitly so the executable predicate and the
`Prop` are definitionally aligned. Non-vacuity: the D14/F11 test channel
with a 500-msat local add satisfies all six guards and yields exactly
`updateAddHtlc`. Negative witness: the old `addHtlc?` accepted `amount = 0`
and `cltv = MAX_CLTV_EXPIRY`; the new one returns `none`.

Why faithful: BOLT 2 `:2815-2830` requires positive amount,
`htlc_minimum_msat`, and `cltv_expiry < 500000000`; `AffordableAdd` already
has them, but `LiquidityProps.addHtlc?` does not. The append change aligns
the list shape with `updateAddHtlc` (`State.lean:334-339`); the old prepend
(`LiquidityProps.lean:380-382`) is order-agnostic for the only external
consumer, `LnLean.Proofs.WaveH.H43.addHtlc?_some_mem` and its
`admitted_payment_eventually_included` corollary. Those proofs use
membership, not list position, but must be re-elaborated after
`addHtlc?_some_shape` changes. No catalog row depends on the old prepend
order. Mechanically, keep `LnLean.Proofs.Payment.addHtlc?` as a
definitional wrapper (or re-export) around the single guarded
implementation, so H43's import path and `(c, h)` signature stay stable
while the list order and guards change. This target removes the two
competing add paths rather than adding a third. It still does not enforce
BOLT 2's `max_accepted_htlcs` count cap; that remains the separate model
extension noted in §5.3.

### T4 — `LnLean.Proofs.Liquidity.LSPS2ClientTargets.selectCheapest_spec`
**Priority: P1. Fidelity risk: low for the finite menu; model extension: yes.**

Model the fixed-amount client path as a finite list of LSP offers:

```lean
namespace LnLean.Proofs.Liquidity.LSPS2

structure FeeParams where
  minPaymentSizeMsat : Nat
  maxPaymentSizeMsat : Nat
  minFeeMsat : Nat
  proportionalPpm : Nat

def inWindow (p : FeeParams) (amount : Nat) : Prop :=
  p.minPaymentSizeMsat ≤ amount ∧ amount ≤ p.maxPaymentSizeMsat

def openingFee (amount minFee ppm : Nat) : Nat :=
  max ((amount * ppm + 999_999) / 1_000_000) minFee

def openingFee? (amount minFee ppm : Nat) : Option Nat :=
  if amount * ppm ≤ U64_MAX then some (openingFee amount minFee ppm) else none

def selectCheapest (offers : List (PubKey × FeeParams)) (amount : Nat) :
    Option (PubKey × Nat × FeeParams)

theorem selectCheapest_spec {offers amount lsp fee p}
    (h : selectCheapest offers amount = some (lsp, fee, p)) :
    (lsp, p) ∈ offers ∧ inWindow p amount ∧
    fee = openingFee amount p.minFeeMsat p.proportionalPpm ∧
    ∀ q ∈ offers, inWindow q amount →
      fee ≤ openingFee amount q.minFeeMsat q.proportionalPpm

theorem openingFee_ge_minFee ...
theorem feeLimit_accepts_iff ...
theorem variablePath_not_fee_optimal :
    ∃ (o₁ o₂ : PubKey × FeeParams) (amount : Nat),
      inWindow o₂.2 amount ∧
      o₂.2.proportionalPpm < o₁.2.proportionalPpm ∧
      openingFee amount o₁.2.minFeeMsat o₁.2.proportionalPpm <
        openingFee amount o₂.2.minFeeMsat o₂.2.proportionalPpm
```

Hypotheses: for `openingFee?` the `u64` multiplication bound; for the
selection theorem, every eligible offer's product is in range. Non-vacuity:
offers `(minFee 10, ppm 10_000)` and `(minFee 5, ppm 20_000)` at
`amount = 100_000_000` give `1_000_000` and `2_000_000`, selecting the
first; this matches `tests/integration_tests_rust.rs:7009-7096`. The
fee-limit witness is `limit = 999_999` (rejects) versus `1_000_000`
(accepts).

Why faithful: it is exactly the `filter` + `compute_opening_fee` +
`min_by_key` chain at `client/lsps2.rs:64-104`, with ceiling division and
the minimum-fee floor from `lightning-liquidity/src/lsps2/utils.rs:60-68`.
It deliberately does **not**
model the HMAC fee promise, expiry, LSP authenticity, or the variable-path
behavior. The variable-path theorem records that selecting minimum ppm is
not the same as selecting minimum absolute fee
(`client/lsps2.rs:149-173`), so no theorem may claim global fee optimality.

### T5 — `LnLean.Proofs.Liquidity.LSPS2ServiceTargets.channelAmount_covers_iff`
**Priority: P2. Fidelity risk: low. Model extension: yes.**

Model the service's channel-size arithmetic with truncating division:

```lean
namespace LnLean.Proofs.Liquidity.LSPS2

def overProvisioningMsat (amt ppm : Nat) : Nat := amt * ppm / 1_000_000

def channelAmountSats (amt ppm : Nat) : Nat :=
  (amt + overProvisioningMsat amt ppm) / 1000

theorem channelAmount_covers_iff (amt ppm : Nat) :
    1000 * channelAmountSats amt ppm ≥ amt ↔
      (1000 - amt % 1000) % 1000 ≤ overProvisioningMsat amt ppm

theorem channelAmount_short_witness :
    channelAmountSats 1001 0 = 1 ∧ 1000 * 1 < 1001

def requiredFundsSats (channel additionalReserve : Nat) : Nat :=
  channel + additionalReserve

theorem insufficientFunds_iff (spendable channel additionalReserve : Nat) :
    spendable < requiredFundsSats channel additionalReserve ↔
      ¬ (spendable ≥ requiredFundsSats channel additionalReserve)
```

Hypotheses: none; all arithmetic is `Nat`. Non-vacuity: `amt = 1001`,
`ppm = 0` gives a 1-sat channel (1000 msat) that cannot carry 1001 msat;
`amt = 1001`, `ppm = 100_000` gives 100 msat of over-provisioning, 1101
msat total, still a 1-sat channel. A positive case is `amt = 2001`,
`ppm = 500_000`, which gives 3 sats and covers 2001 msat.

Why faithful: `service/lsps2.rs:447-473` uses exactly these truncating
operations and the `spendable < channel_amount + additional_reserve`
check. The target does **not** claim that LDK opens a usable channel; it
records the arithmetic condition under which the computed channel could
cover the forwarded amount. It must use `amt_to_forward_msat` (after the
opening fee), not the original invoice amount, following
`lightning-liquidity/src/lsps2/service.rs:257-275`. The trust-model flags
(`client_trusts_lsp`, `disable_client_reserve`, `service/lsps2.rs:89-107`)
remain external.

### T6 — `LnLean.Proofs.Liquidity.AnchorReserveTargets.exactSend_preserves_reserve`
**Priority: P2. Fidelity risk: low. Model extension: yes.**

Model the finite on-chain arithmetic:

```lean
namespace LnLean.Proofs.Liquidity.AnchorReserve

structure AnchorChan where
  isAnchor : Bool
  trustedNoReserve : Bool
  shutdownComplete : Bool

def totalAnchorReserveSats (cs : List AnchorChan) (per : Nat) : Nat :=
  (cs.filter (fun c =>
    c.isAnchor && !c.trustedNoReserve && !c.shutdownComplete)).length * per

def spendableOnchain (trusted reserve : Nat) : Nat := trusted - reserve

theorem totalAnchorReserve_eq_count_mul ...
theorem spendableOnchain_eq_sub (h : reserve ≤ trusted) ...
theorem exactSend_preserves_reserve
    (h : reserve + amount + fee ≤ trusted) :
    reserve ≤ trusted - (amount + fee)

/-- `send_all_to_address(retain_reserves = false)` sends the whole trusted
    balance and leaves zero, so a positive reserve is not preserved. -/
def spendAll (trusted : Nat) : Nat := trusted

theorem drain_ignores_reserve (trusted reserve : Nat) (hr : 0 < reserve) :
    trusted - spendAll trusted < reserve := by
  simp [spendAll, hr]

theorem newChannelReserve_zero_of_nonAnchor ...
theorem newChannelReserve_zero_of_trustedPeer ...
```

Hypotheses: `reserve + amount + fee ≤ trusted` for the exact send (this is
the arithmetic form of `spendable ≥ amount + fee` when `reserve ≤ trusted`);
`0 < reserve` for the drain witness. Non-vacuity: `trusted = 100_000`,
`reserve = 25_000`, `amount = 50_000`, `fee = 1_000` is accepted and leaves
49,000 ≥ 25,000. The drain witness with the same numbers sends 100,000 and
leaves 0 < 25,000.

Why faithful: `wallet/mod.rs:1995-2009` defines spendable as
`trusted_spendable - total_anchor_channels_reserve_sats`; `:2261-2280`
rejects when spendable is below amount + fee; `lib.rs:2717-2758` defines the
eligible-channel count and the new-channel reserve. The model deliberately
does not model coin selection, fee estimation, untrusted pending balance, or
the anchor output's actual spendability. `trusted_spendable` and the fee are
inputs, not derived quantities.

### T7 — `LnLean.Proofs.Liquidity.AsyncMailboxTargets.enqueue_len_le`
**Priority: P2, but external/deferred. Fidelity risk: medium (implementation policy). Model extension: yes.**

Model the finite mailbox and rate-limiter policies:

```lean
namespace LnLean.Proofs.Liquidity.Async

structure Mailbox where
  queues : List (PeerId × List Message)

def enqueue (m : Mailbox) (p : PeerId) (msg : Message) : Mailbox

theorem enqueue_perPeer_len_le_30 ...
theorem enqueue_peer_count_le_300 ...
theorem enqueue_evicts_longest_witness ...

structure Bucket where
  tokens : Nat
  lastRefill : Nat

def refill (b : Bucket) (elapsedTicks : Nat) : Bucket
theorem refill_tokens_le_capacity ...
theorem empty_bucket_rejects ...
```

Hypotheses: a discrete tick model for the rate limiter; the static-invoice
key scheme (`sha256(recipient_id)` plus five-digit slot) is an assumption,
not a proved hash property. Non-vacuity: 31 pushes to one peer leave 30
messages and drop the oldest; 301 peers trigger the longest-queue eviction;
a bucket with 0 tokens rejects until a refill tick. Why faithful: the
constants and policies are exactly `om_mailbox.rs:12-33`,
`static_invoice_store.rs:43-145`, and `rate_limiter.rs:13-76`. This target
does **not** establish async-payment safety, offline delivery, or
static-invoice-server correctness; those remain external.

## 5. Assumptions, counterexamples, and non-vacuity risks

### 5.1 Must-retain counterexamples and boundaries

* `LnLean.Proofs.Channel.ProtocolEventFoldTargets.affordable_add_changes_balance`
  (`:656-670`), `fold_cannot_both_preserve_balance_and_carry_add`
  (`:696-710`), and `fold_cannot_both_preserve_htlcs_and_carry_add`
  (`:712-726`). Do not "fix" the liquidity contradiction by folding add into
  `Step`; that would falsify `LiquidityProps.step_preserves_balance`,
  `D14.waveD_d14_step_balance`, and the balance half of
  `F03.step_preserves_ledgerBalanced`. The additive `UpdateStep` layer is
  the correct boundary.
* `LnLean.Proofs.WaveD.D14.waveD_d14_counterexample_step_ignores_reserve`
  (`:634`) and `...step_ignores_exposure` (`:647`), plus
  `waveD_d14_step_cannot_repair_reserve` (`:496`) and
  `...cannot_repair_exposure` (`:523`). These show that `Step` alone cannot
  repair a bad channel; keep them.
* `LnLean.Proofs.ModelHardening.F11.waveF_f11_inadmissible_update_breaks_reserve`
  (`:344-354`). This is the negative witness for an add that passes the
  amount/min/CLTV/in-flight checks but still breaks the reserve; it must
  remain valid under the corrected reserve convention.
* `LnLean.Proofs.Payment.LiquidityProps.addHtlc?_some_shape` (`:387-396`),
  `addHtlc?_isNone` (`:410-420`), and
  `addHtlc?_some_meetsReserveOn` (`:438-450`). The repair must update
  `addHtlc?_some_shape` to the append shape and `addHtlc?_isNone` to the
  six-guard predicate; keep a complete `isSome`/`isNone` characterization,
  not merely a one-way soundness lemma.
* `LnLean.Proofs.Channel.ReserveProps.reserve_not_always_within_capacity`
  (`:155-171`) and the `Step` preservation results (`:176-190`). A reserve
  larger than capacity remains representable; do not add a well-formedness
  field that silently removes this witness.
* `LnLean.Proofs.Payment.InvoiceWireTargets` route-hint round trips
  (`:473-474`, `:721-722`). A JIT model must add metadata/fee semantics
  without changing the BOLT 11 wire model or its canonicality claims.

### 5.2 Non-vacuity witnesses to preserve or add

* `LnLean.Proofs.WaveE.E37.testChannel` and the other concrete channels
  used by `D14`/`F11` are the existing non-vacuous base cases. The T1/T2
  repair must keep at least one concrete channel where `AffordableAdd`,
  `addHtlc?`, and `waveF_f11_Admissible` all accept the same update.
* T1: the 0/1-sat reserve witness above and its mirror (local reserve 1,
  peer reserve 0). It is deliberately asymmetric so a future "both reserves
  are equal" simplification cannot hide the bug.
* T2: the 600-msat remote / 500-msat local / 1000-msat cap witness. Keep
  both the accepted per-direction case and the rejected pooled case.
* T3: the 500-msat D14/F11 channel, the old zero-amount/bad-CLTV
  rejection witness, and a settled-HTLC overcount witness.
* T4: the two-offer menu above, in both registration orders; the
  cheapest-LSP integration test already exercises both orders.
* T5: the 1001-msat short-channel witness and the 2001-msat positive case.
* T6: the 100,000/25,000/50,000/1,000 exact-spend case and the same case
  under `AllDrainingReserve`.
* T7: the 31st-message, 301st-peer, and empty-bucket cases.

### 5.3 Assumptions that must stay explicit

* **Reserve side.** `ChannelParams.channelReserveSat` is the value the
  advertising endpoint requires the *other* endpoint to keep
  (BOLT 2 `:734-737`). If the tree ever intended a different convention, it
  must rename the field and update `ReserveProps`, `State`, `D14`, `E37`,
  and `F11` together; a local fix in `LiquidityProps` alone would leave the
  tree inconsistent. The BOLT reading is not optional.
* **In-flight side.** `max_htlc_value_in_flight_msat` caps HTLCs offered by
  the remote node (BOLT 2 `:739-741`; LDK `channel.rs:5861-5871`), so it is
  per direction. The pooled quantity is only the ledger's pending value.
* **Pending set.** `State.pendingHtlcValueOf`, `D14.inFlightMsat`,
  `E37.pendingValue`, and `F11.waveF_f11_inFlightFor` count only
  `offered`/`received` HTLCs and exclude terminal ones.
  `LiquidityProps.sumByDirection` counts every entry in `c.htlcs`, so it is
  not a pending-only sum; T2/T3 must replace its use in the cap with the
  pending-filtered projection. LDK additionally excludes holding-cell and
  local-announced HTLCs (`channel.rs:5836-5848`); the Lean model is a
  pending-only abstraction, not LDK's exact in-flight set.
* **HTLC count cap.** `ChannelParams` has no `max_accepted_htlcs` field, so
  T1–T3 close the value, minimum, CLTV, reserve, and in-flight guards but not
  BOLT 2's count cap (`:2825-2827`). Adding the field and its opening
  handshake bound is a separate model extension; do not claim any corrected
  predicate is the full BOLT 2 add predicate.
* **Outbound capacity.** `availableOutbound` still omits commitment fees,
  anchors, dust, and in-flight HTLCs even after the reserve fix
  (`LiquidityProps.lean:76-81`). Do not state it equals LDK's
  `outbound_capacity_msat`; the reserve fix only removes the side error.
* **JIT/LSPS trust.** The fee promise HMAC, `valid_until`, `min_lifetime`,
  `max_client_to_self_delay`, LSP authenticity, `client_trusts_lsp`, and
  `disable_client_reserve` are external cryptographic/time/policy
  assumptions (`lightning-liquidity/src/lsps2/utils.rs:20-58`;
  `service/lsps2.rs:89-107`). No finite
  arithmetic model proves JIT safety.
* **On-chain reserve.** `trusted_spendable` is an opaque wallet input;
  coin selection, fee estimation, and anchor-output spendability are
  external. The model proves only the arithmetic preservation conditional
  on an accepted send.
* **Async payments.** The async flow is experimental and anchored to a
  draft PR, not a BOLT. Persistence, real clocks, networking, blinded-path
  privacy, and static-invoice-server liveness are external. Mailbox and
  rate-limiter bounds are implementation policies, not protocol safety.
* **Selection ties.** Rust `min_by_key` returns the first minimum. T4 must
  model that tie rule; otherwise a "cheapest" theorem is false for equal
  fees. The integration test's order-reversal check is evidence for the
  policy, not a proof of uniqueness.

### 5.4 Proposals that would weaken or hide existing claims

* Do **not** redefine `reserveMsat` in a new module while leaving the old
  definition in place. Two names for the same quantity with opposite sides
  is the current defect; the fix must replace the definition and update its
  consumers.
* Do **not** weaken `AffordableAdd` to the pooled guard "for compatibility".
  The pooled guard rejects BOLT-legal adds; keeping it as the executable
  guard makes `UpdateStep` incomplete and contradicts `LiquidityProps` and
  `F11`.
* Do **not** strengthen `AffordableAdd` with a full commitment-fee/anchor
  model in the same change. That is a separate model extension; the reserve
  and in-flight repairs should be independently reviewable.
* Do **not** change `Step` to carry `update_add_htlc`. The fold
  impossibility theorems are the mechanized reason the additive
  `UpdateStep` exists; a literal fold would falsify retained results.
* Do **not** claim `availableOutbound` is LDK's outbound capacity, or that
  `planFits` is sufficient for a real MPP send. It is a channel-local upper
  bound after the reserve fix, nothing more.
* Do **not** model a JIT invoice as a new wire message. It is a BOLT 11
  invoice with a route hint and LSPS2 metadata; the wire model already has
  the route-hint shape, but not the metadata/fee-promise semantics.
* Do **not** claim LSPS2 fee selection is globally optimal. The fixed-amount
  path selects the minimum absolute fee over a finite menu; the
  variable-amount path selects minimum ppm and ignores the absolute fee.
* Do **not** claim async mailbox/rate-limit bounds imply payment safety or
  liveness. They are finite implementation invariants under a discrete
  clock.
* Do **not** add an ontology or new axiom to make the reserve side "both
  ways correct". BOLT 2 has one direction; the model must choose it.

## 6. Wave-13 recommendation

**Implement only a narrow repair lane; defer the finite LSPS2/anchor models;
treat the async protocol and production JIT/LSPS behavior as external.**

This recommendation is deliberately narrower than "launch a liquidity proof
lane". The tree does not need new protocol mathematics for the P0 defects:
it needs `LiquidityProps` to use the reserve side already encoded in
`ReserveProps`/`State`, and `State.AffordableAdd`/`D14`/`E37` to use the
per-direction in-flight function already encoded in `F11`. That is a
model correction plus bridges, not a new proof development.

Recommended order:

1. **T1 (P0)** — reserve convention repair. This is the smallest change with
   the largest blast-radius correction: it fixes `MeetsReserve`,
   `MeetsRemoteReserve`, `availableOutbound`, `availableInbound`, both
   branches of `addHtlc?`, and `planFits` at once. Keep the regression
   witness.
2. **T2 (P0)** — per-direction in-flight repair and the `F11` bridge. This
   makes `UpdateStep` accept the BOLT-legal updates it currently rejects and
   gives the tree one reference predicate.
3. **T3 (P1)** — complete the value/min/CLTV guards in `addHtlc?` and
   align it with `updateAddHtlc`. After T1/T2 this is mostly proof plumbing;
   it removes the last competing add path.
4. **T4/T5 (P1/P2)** — LSPS2 client selection and service channel-size
   arithmetic. These are safe finite extensions with clear external
   boundaries, but they do not close a catalogued claim and should wait for
   spare capacity.
5. **T6 (P2)** — anchor-reserve arithmetic. Small, faithful, and useful as a
   negative result for `retain_reserves = false`; defer unless the parent
   wants an on-chain reserve slice.
6. **T7 (P2)** — async mailbox/rate-limiter bounds. Defer; the protocol is
   experimental and the model would be implementation policy, not safety.

Reconciliation with `S12-POST-INTEGRATION-AUDIT`: S12 says no wave-13 proof
lane was launched and the only proposed extension was the typed-digest
change. R19 does **not** propose a new protocol proof lane. T1–T3 are
corrections to existing, root-imported declarations that currently disagree
with each other and with BOLT 2. If the parent treats the S12 freeze as
absolute, the correct fallback is to record T1/T2 as P0 known model defects
in `docs/OPEN-ISSUES.md` and suppress any reading of `LN-CH-006` as a
per-direction in-flight theorem; do not add proof modules under a freeze.
If the parent reopens a narrow repair window, T1–T3 are the only items that
should enter it.

Catalog decision: the catalog is closed at 51 rows / 294 targets (S12 §2;
R16). Do not add a new row for T1–T7. If T1–T3 land, attach them as scope
evidence to `LN-CH-006` or record them in `OPEN-ISSUES` without changing the
row count. `LiquidityProps` and `F11` must be added to `AxiomAudit` only if
the parent wants their theorems in the audited surface; otherwise their
absence should remain explicit in the report.

Acceptance criteria for T1–T3, if implemented:

* exact module builds under the shared lock, no `sorry`, no new axioms;
* `AxiomAudit` still permits only `propext`, `Quot.sound`, and
  `Classical.choice`;
* the T1 and T2 regression witnesses are mechanized, not prose-only;
* `LnLean.Proofs.WaveH.H43.addHtlc?_some_mem` and
  `admitted_payment_eventually_included` still compile against the
  append-based shape (membership is order-agnostic);
* `rg "localEndpoint.params.channelReserveSat" LnLean/Proofs/Payment` no
  longer appears in `reserveMsat`, `availableOutbound`, or the local branch
  of `addHtlc?` (the corrected `remoteReserveMsat` legitimately uses the
  local endpoint for the remote side's reserve);
* `rg "remoteEndpoint.params.channelReserveSat" LnLean/Proofs/Payment` no
  longer appears in `remoteReserveMsat`, `availableInbound`, or the remote
  branch of `addHtlc?` (the corrected `reserveMsat` legitimately uses the
  remote endpoint for the local side's reserve);
* `rg "pendingHtlcValueOf" LnLean/Channel/State.lean` appears only in the
  ledger/equality lemmas, not in `AffordableAdd.withinInFlight`;
* `F11.waveF_f11_Admissible` and `State.AffordableAdd` are bridged by a
  theorem, not merely documented as equivalent.

**External barrier (do not code as a proof target):** real LSPS2/JIT
liveness, LSP fee-promise HMAC/expiry, LSP selection trust, static-invoice
server availability, async-payment delivery/privacy, on-chain coin
selection/fee estimation, and the unified-send fallback's asynchronous
failure behavior. These are protocol/implementation assumptions, not finite
arithmetic facts.

## 7. Evidence and commands

Read-only inspection commands used (all run from
`/home/ubuntu/ln-lean-repair` unless noted):

```sh
git status --short
git log --oneline -1
git -C /tmp/opencode/ldk-refs/ldk-node rev-parse HEAD
git -C /tmp/opencode/ldk-refs/ldk-server rev-parse HEAD
git -C refs/rust-lightning rev-parse HEAD

rg -n "reserveMsat|availableOutbound|sumByDirection|pendingHtlcValueOf|def addHtlc" \
  LnLean/Proofs/Payment/LiquidityProps.lean LnLean/Channel/State.lean
rg -n "localReserveSat|remoteReserveSat|channelReserveSat" \
  LnLean/Proofs/Channel/ReserveProps.lean
rg -n "waveF_f11_Admissible|waveF_f11_inFlightFor|waveF_f11_capFor" \
  LnLean/Proofs/ModelHardening/F11.lean
rg -n "AffordableAdd|inFlightMsat|offeringReserveGuard" LnLean/Proofs/WaveD/D14.lean
sed -n '75,90p' LnLean/Channel/Types.lean

rg -n "LiquidityProps|F11|ReserveProps" \
  LnLean/Proofs/Obligations.lean docs/THEOREM-INDEX.md docs/TRACEABILITY.md \
  LnLean/Proofs/PhaseC3/AxiomAudit.lean LnLean.lean LnLean/Proofs/Common.lean
rg -n "LN-CH-006|LN-PM-00" LnLean/Proofs/Obligations.lean

rg -n "receive_via_jit_channel|manual_claim|claim_for_id|fail_for_id" \
  /tmp/opencode/ldk-refs/ldk-node/src/payment/bolt11.rs
rg -n "min_payment_size_msat|max_payment_size_msat|compute_opening_fee|min_by_key|max_total_opening_fee" \
  /tmp/opencode/ldk-refs/ldk-node/src/liquidity/client/lsps2.rs
rg -n "over_provisioning|channel_amount_sats|additional_reserve|spendable_amount" \
  /tmp/opencode/ldk-refs/ldk-node/src/liquidity/service/lsps2.rs
rg -n "ExactRetainingReserve|AllDrainingReserve|spendable_onchain|total_anchor_channels_reserve" \
  /tmp/opencode/ldk-refs/ldk-node/src/wallet/mod.rs \
  /tmp/opencode/ldk-refs/ldk-node/src/payment/onchain.rs \
  /tmp/opencode/ldk-refs/ldk-node/src/lib.rs
rg -n "MAX_MESSAGES_PER_PEER|MAX_PEERS|RATE_LIMITER|sha256|invoice_slot" \
  /tmp/opencode/ldk-refs/ldk-node/src/payment/asynchronous
rg -n "async_payments|receive_async|static_invoice" \
  /tmp/opencode/ldk-refs/ldk-node/src/payment/bolt12.rs \
  /tmp/opencode/ldk-refs/ldk-node/src/builder.rs

sed -n '725,745p;878,900p;2815,2832p' refs/bolts/02-peer-protocol.md
sed -n '5858,5878p' refs/rust-lightning/lightning/src/ln/channel.rs
sed -n '5519,5554p;5571,5618p;6835,6920p;6978,7005p;7009,7096p' \
  /tmp/opencode/ldk-refs/ldk-node/tests/integration_tests_rust.rs
sed -n '60,68p' /tmp/opencode/rl-live/rust-lightning/lightning-liquidity/src/lsps2/utils.rs
sed -n '248,285p;438,458p' \
  /tmp/opencode/rl-live/rust-lightning/lightning-liquidity/src/lsps2/service.rs
sed -n '28,95p' /tmp/opencode/ldk-refs/ldk-server/ldk-server/src/api/bolt11_receive_via_jit_channel.rs
sed -n '20,39p' /tmp/opencode/ldk-refs/ldk-server/ldk-server/src/api/unified_send.rs
```

No Lean build, no `cargo` test, and no file outside this report was
modified. The report is source-grounded only; the proposed targets are not
claimed to exist until a later implementation lane compiles them and the
catalog checker resolves the exact names. The worktree's untracked
`.opencode/`, `agents/briefs/wave13-review/`, other lane reports, status
files, and wave-13 scripts were not touched.
