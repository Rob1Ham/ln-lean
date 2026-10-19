# R04 — On-chain wallet, UTXOs, balances, and coin control

**Status:** read-only review (no code, Lean, docs, tests, vendor, or other-report edits)
**Pins:** LDK Node `fa123fed131e27ecc420b77fa7086fcf1ddaebb8`, LDK Server `c17dc11dde38f88c53457039ddf30c6b90a63ba2`
**Worktree:** `/home/ubuntu/ln-lean-repair` at `f7f062817c185cd70004bb26c652deb99c6fd4bd` on `repair/integrated`
**Lane verdict:** the full surface is **not** implementable as a production-equivalence claim in wave 13. Two small, self-contained model extensions (T1, T4) are safe if the parent authorises a new wallet lane; the rest should be deferred or handled by R03.

---

## 1. Scope and current Lean surface

### 1.1 What this lane reviewed

This lane asks whether the Lean tree can state, and prove, the correspondence between:

- an on-chain wallet's **total value**, **trusted-spendable value**, and **reported anchor reserve**;
- the wallet's **owned UTXO inventory**, its **confirmed-only** coin-selection interface, and its **change** output/persistence contract;
- the **Lightning-side claimable balance** projection, including the close-candidate sentinel and the zero-weighted HTLC variants;
- **on-chain payment confirmation status** (pending → succeeded, and regression under reorg), and
- the **sweep lifecycle** for funds moving from a closed channel into the wallet.

The review is about *what the model can claim*, not about adding a wallet implementation. It is also **not** a re-review of chain finality: R03 (`agents/reports/wave13-review/R03-l1-chain-sync-finality.md`) owns the tip/reorg/membership surface, and this report cross-references it rather than duplicating it.

### 1.2 The catalog surface

`LnLean/Proofs/Obligations.lean:80-115` defines exactly six L1 rows. Their subjects are:

| Row | Subject | Wallet/UTXO relevance |
|---|---|---|
| `LN-L1-001` | P2WSH funding script, hash link, sighash seam | none: funding *output construction*, not the wallet that owns it |
| `LN-L1-002` | `fundingOutput_moneyRange` (seam → btc-lean `MoneyRange`) | a value predicate on one output, not a balance |
| `LN-L1-003` | bounded-reorg channel safety and deep-reorg failure mode | confirmation *policy* only; no wallet state |
| `LN-L1-004` | `to_local` CSV/revocation witness script | none |
| `LN-L1-005` | anchor output = 330 sats | the *constant* used by reserve policy, not the reserve |
| `LN-L1-006` | commitment base weight 724/1124 + 172/HTLC | fee arithmetic, not wallet fee payment |

There is **no** catalog row for on-chain wallet balance, spendable balance, owned UTXOs, coin selection, change, anchor reserve funding, sweep status, or on-chain payment status. A search of the catalog for `wallet`, `utxo`, `balance`, `coin selection`, `change`, `sweep`, and `spendable` returns no additional L1/security row.

`LN-SEC-002` is the only row whose prose mentions the L1 value ledger, and its explicit scope note (`Obligations.lean:410-417`) says:

> `global_conservation` covers the multi-channel ledger only. The L1 spend-set half is modelled separately in D32 and is not asserted.

The named target resolves to `LnLean.Proofs.PhaseC2.GlobalConservation.global_conservation` (`LnLean/Proofs/PhaseC2/GlobalConservation.lean:344`), which is a multi-channel commitment ledger theorem. It does not mention a wallet, an unspent set, or a balance. Reading `LN-SEC-002` as covering on-chain wallet conservation would be an over-read.

### 1.3 Adjacent Lean vocabulary that exists and must be acknowledged

The absence of a wallet model is not the absence of all relevant machinery. Four existing artefacts are close enough that a careless proposal would either duplicate or contradict them.

**(a) `L1Ledger` — outpoint spend-set discipline.**
`LnLean/Security/Invariants.lean:156-165`:

```lean
structure OutRef where
  txid : Nat
  index : Nat

structure L1Ledger where
  spent : List OutRef
  height : Height
```

`NoDoubleSpend` is `spent.Nodup` (`:168-169`), and `spend_preserves_noDoubleSpend` (`:180-184`) preserves it **only under an explicit freshness hypothesis** `o ∉ l.spent`. The ledger has **no unspent set and no values**. It therefore cannot express "the wallet owns these coins", "these coins sum to this balance", or "this transaction consumed exactly these coins".

**(b) `D32` — value-bearing spend set.**
`LnLean/Proofs/WaveD/D32.lean:104-150` adds `L1Spend` (`spentOutpoint`, `inputValueSat`, `outputValueSat`, `feeSat`), `L1Spend.Conserves`, and `L1SpendSet` with `AllConserved`, totals, and `NoDoubleSpend` on the projected outpoints. `waveD_d32_l1SpendSet_conserved` (`:181-186`) and `waveD_d32_global_conservation` (`:388-397`) give value conservation **conditional on every spend conserving and on a funding bridge**. This is reusable as a *fee law*, but it is a spend-set ledger, not an inventory: it records only what was spent, never what remains.

**(c) Vendor `Bitcoin.Ledger.UtxoSet` and `Bitcoin.Conservation.single_tx_conservation`.**
`vendor/btc-lean-core/Bitcoin/Ledger/Utxo.lean:22-31` defines `Coin` and `UtxoSet := OutPoint → Option Coin`. `single_tx_conservation` (`vendor/btc-lean-core/Bitcoin/Conservation/Interface.lean:96-110`) proves `totalIn = totalOut + fee → fee ≥ 0` under `InputAuth`, existence, `MoneyRange`, and `totalOut ≤ totalIn`.

Two limits matter:

- `applyTx` (`Utxo.lean:46-52`) inserts every new coin at `OutPoint.null` with the comment *"placeholder key = OutPoint.null; real key = (txid, k) once txid lands (M1)"*. It therefore **cannot** model a txid-keyed wallet inventory or change-outpoint provenance.
- `single_tx_conservation` is a *per-transaction* fee law; it says nothing about a wallet's remaining balance, change, or reserve.

**(d) Off-chain channel reserve laws and confirmation arithmetic.**
`LnLean/Proofs/Channel/ReserveProps.lean:103-133` defines `localReserveSat`, `remoteReserveSat`, `ReserveWithinCapacity`, `ReserveInvariant`, and `ChannelHtlcBounds`; `:206-216` proves spending the local balance preserves the local reserve. These are **channel** reserves (BOLT 2), not the wallet's **anchor-channel emergency reserve**. The names are similar and the quantities are different; conflating them would be a fidelity error.

`LnLean/Proofs/Security/ReorgTargets.lean:84-95` gives `antiReorgDelay := 6`, `confirmationCount tip h := tip + 1 - h`, and `reorgSurvives r tip h := r.depth < confirmationCount tip h`; `:162-177` gives `OnchainFact` and `OnchainFact.settled` (`antiReorgDelay ≤ confirmations tip`). These provide the arithmetic for a payment-status target but no transaction state to regress.

### 1.4 Precise statement of the gap

The Lean tree currently has **no declaration** of the form:

- `WalletBalance` (total / trusted-spendable / reserve);
- `OwnedUtxo` or a wallet inventory with confirmation flags;
- a coin-selection relation or a change predicate;
- a wallet-level conservation theorem tying an inventory to a spend;
- an on-chain payment status type with a reorg transition;
- a sweep-status state machine.

No existing theorem is weakened or contradicted by this gap: the wallet surface is simply outside the current claim set. The rest of this report proposes what a *bounded* extension could claim, and what it must not claim.

---

## 2. LDK datapoints (with `file:line`)

All LDK Node citations are against the pinned clone `/tmp/opencode/ldk-refs/ldk-node`; all LDK Server citations against `/tmp/opencode/ldk-refs/ldk-server`. rust-lightning citations are corroborating source (see §7.2 for the pin caveat).

### 2.1 The public balance record

`src/balance.rs:21-67` defines `BalanceDetails`:

- `total_onchain_balance_sats` (`:23-24`) — "The total balance of our on-chain wallet."
- `spendable_onchain_balance_sats` (`:27-29`) — "sufficiently confirmed funds, minus `total_anchor_channels_reserve_sats`."
- `total_anchor_channels_reserve_sats` (`:30-32`) — "the share of our total balance that we retain as an emergency reserve".
- `total_lightning_balance_sats` (`:41-43`) — "The total balance that we would be able to claim across all our Lightning channels", explicitly excluding balances "we are unsure if we are able to claim".
- `lightning_balances` (`:55-56`) — the detailed enum list.
- `pending_balances_from_channel_closures` (`:59-66`) — swept balances, with the explicit caveat that they "might or might not already be accounted for in `total_onchain_balance_sats`".

The last caveat is important: the sum `total_onchain + pending_sweeps` is **not** a conservation identity, because the same sats can appear in both views.

The server projection is a direct copy of these four scalars (`ldk-server/src/api/get_balances.rs:20-30`), so the gRPC surface adds no semantics of its own.

### 2.2 `total`, `spendable`, and the reserve clamp

`src/wallet/mod.rs:1994-2003`:

```rust
fn get_balances_inner(
    &self, balance: Balance, total_anchor_channels_reserve_sats: u64,
) -> Result<(u64, u64), Error> {
    let (total, spendable) = (
        balance.total().to_sat(),
        balance.trusted_spendable().to_sat().saturating_sub(total_anchor_channels_reserve_sats),
    );
    Ok((total, spendable))
}
```

So `spendable = max(trusted_spendable − cur_reserve, 0)` with saturating subtraction. `trusted_spendable` is BDK's confirmation- and trust-filtered view; the model does **not** derive it.

`src/lib.rs:2363-2405` assembles the record, and the reported reserve is clamped:

```rust
let total_anchor_channels_reserve_sats =
    std::cmp::min(cur_anchor_reserve_sats, total_onchain_balance_sats);
```

(`lib.rs:2368-2369`). This clamp is why `spendable + reportedReserve = total` is **false** in general. When `cur_reserve > total`, both `spendable` and the gap collapse (`spendable = 0`, `reportedReserve = total`), so the identity holds trivially and hides the over-reservation. When `trusted_spendable < total` and `cur_reserve ≤ trusted_spendable`, `spendable + reportedReserve = trusted_spendable < total`: funds exist but are neither spendable nor reported as reserve (e.g. unconfirmed change).

Concrete arithmetic witnesses from the pinned tests:

- premine with no channels: `spendable = premine` (`tests/integration_tests_rust.rs:2227-2228`);
- after opening an anchor channel: `spendable = 0` while the funds still exist (`:2266`);
- send-all retaining the reserve: `total = reserve_amount_sat`, `spendable = 0` (`:2281-2282`);
- send-all draining: `total = 0` (`:2123-2124`).

### 2.3 The anchor reserve is a policy count, not a wallet fact

`src/lib.rs:2717-2734`:

```rust
pub(crate) fn total_anchor_channels_reserve_sats(
    channel_manager: &ChannelManager, config: &Config,
) -> u64 {
    channel_manager.list_channels().into_iter()
        .filter(|c| {
            !config.anchor_channels_config.trusted_peers_no_reserve.contains(&c.counterparty.node_id)
                && c.channel_shutdown_state.map_or(true, |s| s != ChannelShutdownState::ShutdownComplete)
                && c.channel_type.as_ref().map_or(true, requires_anchor_channel_type)
        })
        .count() as u64
        * config.anchor_channels_config.per_channel_reserve_sats
}
```

Consequences that a Lean model must carry as parameters, not prove:

- The reserve is `count(eligible channels) × per_channel_reserve_sats`.
- Eligibility depends on **configuration** (`trusted_peers_no_reserve`, `per_channel_reserve_sats`) and on channel *type*/shutdown state, not on the wallet's coins.
- The reserve can exceed the wallet's total; the report clamps it.
- `total_anchor_channels_reserve_sats` is recomputed at read time; there is no invariant tying it to a previously reserved set of outpoints. The wallet does **not** earmark UTXOs for the reserve.

### 2.4 Lightning-side balance projection and the zero weights

`src/lib.rs:2384-2393` sums per-monitor balances:

```rust
for ldk_balance in monitor.get_claimable_balances() {
    total_lightning_balance_sats += ldk_balance.claimable_amount_satoshis();
    lightning_balances.push(LightningBalance::from_ldk_balance(...));
}
```

`claimable_amount_satoshis` is rust-lightning's method (`lightning/src/chain/channelmonitor.rs:1027-1039`). Its weights are:

| Variant | Reported amount |
|---|---|
| `ClaimableOnChannelClose` | candidate selected by `confirmed_balance_candidate_index` (see §2.5) |
| `ClaimableAwaitingConfirmations` | `amount_satoshis` |
| `ContentiousClaimable` | `amount_satoshis` |
| `CounterpartyRevokedOutputClaimable` | `amount_satoshis` |
| `MaybeTimeoutClaimableHTLC { outbound_payment: true }` | **0** |
| `MaybeTimeoutClaimableHTLC { outbound_payment: false }` | `amount_satoshis` |
| `MaybePreimageClaimableHTLC` | **0** |

The doc comment at `balance.rs:41-43` says the total excludes "balances that we are unsure if we are able to claim"; the zero weights are the mechanism. Therefore

```
total_lightning ≠ Σ detail.amount_satoshis
```

is the faithful statement: the sum over **all** detail amounts double-counts the zero-weighted variants. A Lean target must use the weighted sum (T2), and must not use the naive sum.

### 2.5 The close-candidate sentinel: index 0 means "candidate 0", not "no candidate"

`src/balance.rs:234-243`:

```rust
// When confirmed_balance_candidate_index is 0, no specific alternative
// funding has been confirmed yet, so use the last candidate (most current
// splice/RBF attempt), matching LDK's claimable_amount_satoshis behavior.
let balance = if confirmed_balance_candidate_index != 0 {
    &balance_candidates[confirmed_balance_candidate_index]
} else {
    balance_candidates.last()
        .expect("balance_candidates always contains at least the current funding")
};
```

This is **faithful to rust-lightning's arithmetic** (`channelmonitor.rs:1032-1036` does exactly `if idx != 0 { candidates[idx] } else { candidates.last() }`). But the *meaning* of index 0 is different from the comment's paraphrase. rust-lightning's field docs (`channelmonitor.rs:886-893`) say the index "point[s] to the confirmed entry"; the construction (`channelmonitor.rs:3245-3258`) returns the index of the funding scope that is confirmed, using `alternative_funding_confirmed`, and falls back to index 0 when no alternative is confirmed. When a splice is pending and **unconfirmed**, index 0 is the confirmed pre-splice funding; `candidates.last()` is the latest **unconfirmed** splice/RBF attempt.

So:

- `confirmed_balance_candidate_index = 0` does **not** mean "there are no candidates"; there is always at least the current funding.
- The reported `ClaimableOnChannelClose` amount can be the *last* candidate's amount, which may be an unconfirmed splice/RBF attempt.
- `LightningBalance::ClaimableOnChannelClose`'s own doc says the values are "only based on the confirmed state of the channel" (`balance.rs:73-75`). That sentence and the `last()` choice are in tension when multiple candidates exist.

This is a **reporting-semantics** finding, not an LDK Node bug: the upstream library makes the same choice. A Lean model should encode the sentinel arithmetic and preserve the counterexample, not "fix" either implementation.

### 2.6 The owned-UTXO inventory

`src/wallet/mod.rs:2437-2510` (`list_confirmed_utxos_inner`) builds the spendable inventory:

- `transactions().filter(|t| t.chain_position.is_confirmed())` (`:2440-2444`);
- `list_unspent().filter(|u| confirmed_txs.contains(&u.outpoint.txid))` (`:2445-2446`);
- only witness v0 (P2WPKH) and v1 (P2TR) scripts are accepted (`:2449-2505`); other versions are logged and skipped.

The inventory is therefore **derived**: an output is "owned and confirmed" iff the wallet knows the funding transaction, BDK marks it confirmed, it is unspent, and its script is a supported witness program. There is no Lean analogue.

The corroborating invariant check at `:1981-1985` asserts that `list_confirmed_utxos` is non-empty when anchor spending is needed, but this is a `debug_assert!`, not a consensus rule.

### 2.7 Confirmed-only coin selection (the splice path) and change

`src/wallet/mod.rs:2350-2435` is the `CoinSelectionSource` implementation used by splicing (`:3973-3981`). It is the only path that explicitly calls:

```rust
tx_builder.exclude_unconfirmed();
```

(`:2383`). The contract is:

1. Foreign `must_spend` inputs are added (`:2369-2381`).
2. `must_pay_to` outputs are added (`:2383`).
3. Unconfirmed UTXOs are excluded (`:2383`).
4. The selected inputs are filtered to drop every `must_spend` outpoint (`:2392-2404`), so the returned `confirmed_utxos` are the *wallet-funded* inputs only.
5. More than `must_pay_to.len() + 1` outputs is an error (`:2406-2413`).
6. Change is found **structurally** as the single output not equal to any must-pay output (`:2415-2418`).
7. The staged changeset is persisted **only if** `change_output.is_some()` (`:2419-2432`).

Two distinct facts follow, and they must not be merged:

- **Confirmed-only applies to splice coin selection, not to ordinary sends.** `send_to_address` (`:2170-2288`) builds a normal BDK transaction and never calls `exclude_unconfirmed`; ordinary sends may therefore spend unconfirmed change. A blanket theorem "all wallet spends are confirmed-only" would be false.
- **Change detection is structural, not semantic.** If the extra output happens to equal a must-pay `TxOut` (same script and value), `find` returns `None` even though `outputs.len() = must_pay_to.len() + 1`. The changeset is then not persisted on this path. This is a constructed but well-typed counterexample; its practical probability is low, but a Lean contract must state the distinctness hypothesis or the counterexample.

Ordinary sends are different: after building and reserve-checking, `send_to_address` persists `take_staged()` unconditionally (`:2306-2310`), so change from a normal send is persisted regardless of whether a change output was created.

### 2.8 Send modes and reserve guards

`src/wallet/mod.rs:2170-2288` dispatches on `OnchainSendAmount`:

| Mode | Builder | Guard |
|---|---|---|
| `ExactRetainingReserve { amount_sats, .. }` | `add_recipient(amount).fee_rate(...)` | `spendable ≥ amount + tx_fee` (`:2244-2266`) |
| `AllRetainingReserve { cur_anchor_reserve_sats }` **and** `cur_anchor_reserve_sats > DUST_LIMIT_SATS` | `get_max_drain_amount(... reserve ...)`, then `fee_absolute` | `spendable ≥ sent − received` (`:2270-2288`) |
| `AllRetainingReserve { cur_anchor_reserve_sats: ≤ 546 }` | falls through to `drain_wallet().drain_to(...)` (`:2202-2210`) | none |
| `AllDrainingReserve` | `drain_wallet().drain_to(...)` | none (`_ => {}`, `:2288`) |

`DUST_LIMIT_SATS = 546` (`src/wallet/mod.rs:99`), and the branch predicate is `cur_anchor_reserve_sats > DUST_LIMIT_SATS` (`:2194`). The fall-through is a real edge: **"retain reserves" with a reserve of 0–546 sats drains the wallet completely**, exactly like `AllDrainingReserve`.

The server's `AllFunds` path hardcodes retention:

```rust
Amount::AllFunds(_) => {
    context.node.onchain_payment().send_all_to_address(&address, true, fee_rate)?
}
```

(`ldk-server/src/api/onchain_send.rs:40-42`), where the `true` is `retain_reserves` (`ldk-node/src/payment/onchain.rs:101-125`). So the *server* cannot reach the drain-all branch through `AllFunds`, but the *node API* can. For the exact path the public API takes only an amount; `send_to_address_inner` recomputes `total_anchor_channels_reserve_sats` and passes it as `ExactRetainingReserve` (`ldk-node/src/payment/onchain.rs:46-53`), so the guard uses the current policy reserve rather than a caller-supplied one.

### 2.9 On-chain payment confirmation status and reorg

`src/payment/store.rs:401` defines `PaymentStatus`; `:685` defines `ConfirmationStatus`. The wallet event handler at `src/wallet/mod.rs:553-561` computes:

```rust
let payment_status = if cur_height >= confirmation_height + ANTI_REORG_DELAY - 1 {
    PaymentStatus::Succeeded
} else {
    PaymentStatus::Pending
};
```

With `ANTI_REORG_DELAY = 6` (`channelmonitor.rs:347`), this is `tip + 1 ≥ conf + 6`, i.e. six confirmations counting the confirmation block.

Regression is real. `WalletEvent::TxUnconfirmed` (`:775-828`) does two different things:

- for a **funding** record, `apply_funding_status_update_locked(..., ConfirmationStatus::Unconfirmed)` only updates the confirmation status (`:787-795`);
- for a **non-funding/ordinary** payment, `create_payment_from_tx(..., PaymentStatus::Pending, ConfirmationStatus::Unconfirmed)` rewrites the record to `Pending`/`Unconfirmed` (`:810-826`).

The pinned integration test `reorged_onchain_payment_returns_to_unconfirmed` (`tests/integration_tests_rust.rs:2137-2200`) demonstrates exactly this: both nodes report `PaymentStatus::Pending` with `ConfirmationStatus::Confirmed` after one block, then `PaymentStatus::Pending` with `ConfirmationStatus::Unconfirmed` after a one-block reorg.

Therefore **payment status is not monotone**, and a Lean target must not claim `Succeeded → always Succeeded`.

### 2.10 Sweep lifecycle

`src/balance.rs:318-356` defines three states:

```
PendingBroadcast { channel_id, amount_satoshis }
BroadcastAwaitingConfirmation { channel_id, latest_broadcast_height,
                                latest_spending_txid, amount_satoshis }
AwaitingThresholdConfirmations { channel_id, latest_spending_txid,
                                 confirmation_hash, confirmation_height,
                                 amount_satoshis }
```

`balance.rs:357-399` maps rust-lightning's `OutputSpendStatus` (`PendingInitialBroadcast`, `PendingFirstConfirmation`, `PendingThresholdConfirmations`) into these three constructors. The mapping is **total** over the three statuses, but the amount comes from `value_from_descriptor(&output_info.descriptor)` in every branch, so the model's amount is invariant across transitions.

Pruning is `PRUNE_DELAY_BLOCKS = ARCHIVAL_DELAY_BLOCKS + ANTI_REORG_DELAY = 4032 + 6 = 4038` (`rust-lightning/lightning/src/util/sweep.rs:47`), applied as `cur_height >= confirmation_height + PRUNE_DELAY_BLOCKS - 1` (`sweep.rs:636`). The sweep test at `tests/integration_tests_rust.rs:944-958` witnesses the `BroadcastAwaitingConfirmation` state and its `latest_spending_txid`; the recovery test around `:958-1000` witnesses that a node that did not record the sweep has no such entry.

A reorg can move a tracked output from `PendingThresholdConfirmations` back to a first-confirmation state: rust-lightning's `OutputSpendStatus::unconfirmed` rewrites that state to `PendingFirstConfirmation` (`sweep.rs:220-240`), and `transaction_unconfirmed` applies it to every output at or above the unconfirmed height (`sweep.rs:817-833`); ldk-node then reports `BroadcastAwaitingConfirmation` again (`balance.rs:364-378`). The public `PendingSweepBalance` enum has no separate `Unconfirmed` variant, so the regression is represented by the status transition, not by a new constructor. This is a modelling constraint, not a claim that sweeps are monotone.

---

## 3. Gap matrix

| Behavior | Lean status | LDK evidence | Gap / counterexample | Priority |
|---|---|---|---|---|
| Total on-chain wallet value | **Missing.** No `WalletBalance`/inventory declaration. | `balance.rs:21-24`; `wallet/mod.rs:1994-2003` | No theorem relates a coin list to `total`. T1 takes `total` as an input; T7 defines inventory total; the identification `total = Σ owned UTXOs` is an explicit assumption, not proved. | P0 |
| `spendable = trusted − reserve` with saturating subtraction | **Missing.** | `wallet/mod.rs:1998-2001` | No Lean declaration of `trustedSpendable`, `curReserve`, or `spendable`. | P0 |
| Reported reserve `min(cur, total)` | **Missing.** | `lib.rs:2368-2369` | `spendable + reserve = total` is **false** when `trusted < total`; when `cur > total` it holds only because both sides collapse (`spendable = 0`, `reserve = total`). | P0 |
| Anchor reserve = eligible-channel count × per-channel constant | **Unmodelled/external.** | `lib.rs:2717-2734` | Eligibility depends on config and channel type; no wallet-side earmarking. | P1 |
| `total_lightning` weighted sum | **Missing.** | `lib.rs:2384-2393`; `channelmonitor.rs:1027-1039` | `Σ detail.amount` over all variants is **wrong**: outbound `MaybeTimeout` and all `MaybePreimage` contribute 0. | P1 |
| Close-candidate sentinel | **Missing.** | `balance.rs:234-243`; `channelmonitor.rs:886-893`, `:1032-1036`, `:3245-3258` | Index 0 → `last()` can report an unconfirmed splice/RBF candidate; docs say "confirmed state only". Counterexample `[100, 200]`, idx 0 → 200. | P1 |
| Owned-UTXO inventory with confirmation flags | **Missing.** | `wallet/mod.rs:2437-2510` | Vendor `applyTx` writes `OutPoint.null`, so it cannot key coins by txid. | P1 |
| Confirmed-only splice coin selection | **Missing.** | `wallet/mod.rs:2383` | Only the splice/`CoinSelectionSource` path excludes unconfirmed; ordinary `send_to_address` does not. | P0 |
| `confirmed_utxos` excludes `must_spend` | **Missing.** | `wallet/mod.rs:2392-2404` | A theorem returning all selected inputs would double-count foreign inputs. | P1 |
| Change detection and changeset persistence | **Missing.** | `wallet/mod.rs:2406-2432`; `:2306-2310` | Structural `find` fails when change equals a must-pay `TxOut`; then `change_set` is not persisted on the splice path. | P0 |
| Wallet inventory conservation across a spend | **Partial vocabulary, missing theorem.** `L1SpendSet` conserves spend sets; vendor `single_tx_conservation` conserves one tx. | `D32.lean:104-150`, `:181-186`; `Interface.lean:96-110` | Neither says the *remaining* wallet value drops by exactly the fee. `L1SpendSet` has no unspent remainder; vendor `applyTx` is key-broken. | P2 |
| No double spend | **Covered conditionally.** | `Invariants.lean:168-184` | Freshness is an explicit hypothesis; a wallet-level competing-claim theorem cannot drop it. | P1 |
| RBF / competing claim | **Partial; contradicted if unconditional.** | `payment/onchain.rs:134` (`bump_fee_rbf`); `wallet/mod.rs:830` (`TxReplaced`) | Two valid spends of the same outpoint are possible before one confirms; `L1Ledger.NoDoubleSpend` would be false if both were admitted. Keep the freshness condition. | P1 |
| On-chain payment status `Succeeded` threshold | **Missing; overlaps R03.** | `wallet/mod.rs:553-561`; `ReorgTargets.lean:84-95` | Model has confirmation arithmetic but no payment status type. | P2 |
| Payment status monotonicity | **Contradicted.** | `wallet/mod.rs:775-828`; test `:2137-2200` | `TxUnconfirmed` rewrites ordinary payments to `Pending`/`Unconfirmed`. | P2 |
| Sweep three-state lifecycle | **Missing.** | `balance.rs:318-399` | No Lean state machine; amount invariance across states is unstated. | P2 |
| Sweep prune after 4038 confirmations | **Missing.** | `sweep.rs:47`, `:636` | No theorem; `PRUNE_DELAY_BLOCKS` is a rust-lightning constant. | P2 |
| Send-mode reserve guards | **Missing.** | `wallet/mod.rs:2244-2288` | `AllDrainingReserve` has no guard; `AllRetainingReserve` with reserve ≤ 546 falls through to full drain. | P1 |
| Server `AllFunds` retains reserves | **Unmodelled/external.** | `onchain_send.rs:40-42`; `onchain.rs:101-125` | A source-level conformance fact, not a Lean theorem. | P2 |

**Reading the matrix.** "Missing" means no declaration exists; "partial vocabulary" means reusable definitions exist but do not state the behavior; "contradicted" means a plausible unconditional statement has a concrete counterexample in the pinned source. No row is "covered faithfully" for the wallet surface.

---

## 4. Proposed targets

The eight targets below are ordered by dependency and priority. Names are proposals; the parent may rename them to fit the module layout. Statement shapes are deliberately small and proof-oriented; they are **not** production-equivalence claims.

Proposed module layout (new files only, if authorised):

- `LnLean/Wallet/Balance.lean` — T1, T2, T3
- `LnLean/Wallet/CoinSelect.lean` — T4, T7
- `LnLean/Wallet/Sweep.lean` — T5
- `LnLean/Wallet/OnchainPayment.lean` — T6
- `LnLean/Wallet/Send.lean` — T8
- proofs under `LnLean/Proofs/Wallet/`

### T1 — Balance / reserve partition (P0)

**Fully-qualified name:** `LnLean.Wallet.Balance.spendable_add_reportedReserve_le_total`
(companion: `LnLean.Wallet.Balance.spendable_eq_total_sub_reserve`)

**Statement shape:**

```lean
structure WalletBalance where
  total            : Nat
  trustedSpendable : Nat
  curReserve       : Nat

def WalletBalance.spendable (b : WalletBalance) : Nat :=
  b.trustedSpendable - b.curReserve

def WalletBalance.reportedReserve (b : WalletBalance) : Nat :=
  min b.curReserve b.total

theorem spendable_add_reportedReserve_le_total (b : WalletBalance)
    (hT : b.trustedSpendable ≤ b.total) :
    b.spendable + b.reportedReserve ≤ b.total

theorem spendable_eq_total_sub_reserve (b : WalletBalance)
    (hT : b.trustedSpendable = b.total) (hR : b.curReserve ≤ b.total) :
    b.spendable = b.total - b.reportedReserve
```

**Hypotheses:** `trustedSpendable ≤ total` is the only substantive one. It is a wallet-interface assumption: `trusted_spendable()` is a subset of `total()` in BDK's view. The theorem does **not** derive it from an inventory.

**Non-vacuity witness:** `⟨100, 100, 30⟩` gives `spendable = 70`, `reportedReserve = 30`, `70 + 30 ≤ 100`. A second witness `⟨10, 10, 50⟩` gives `spendable = 0`, `reportedReserve = 10`, so the inequality is strict-or-equal at the clamp. A third `⟨100, 40, 30⟩` gives `spendable = 10`, `reportedReserve = 30`, `40 ≤ 100`, showing why the equality needs `trusted = total`.

**Why faithful:** it is exactly `get_balances_inner` (`wallet/mod.rs:1998-2001`) and the clamp (`lib.rs:2368-2369`), with `Nat` saturating subtraction matching `saturating_sub`. The inequality direction is the strongest statement that is true without extra assumptions.

**Fidelity risk:** low for the arithmetic; medium for the interpretation of `trustedSpendable` and `total`. Both are **inputs**, so the theorem can be true while LDK's `trusted_spendable` is wrong, and it does not prove `total = Σ owned UTXO values`. The inventory bridge is T7; the identification `WalletBalance.total = Wallet.total` must be stated as a modelling equation, not silently assumed. Say so in the module doc.

**Classification:** model extension (new structure). No external assumption beyond `trustedSpendable ≤ total`.

**Feasibility:** high; `omega`/`simp` on `Nat` and `min`.

---

### T2 — Weighted Lightning total (P1)

**Fully-qualified name:** `LnLean.Wallet.Balance.totalLightning_eq_sum_weight`

**Statement shape:**

```lean
inductive LnBalance where
  | claimableOnClose                  (amount : Nat)
  | claimableAwaitingConfirmations    (amount : Nat)
  | contentiousClaimable              (amount : Nat)
  | counterpartyRevokedOutputClaimable (amount : Nat)
  | maybeTimeoutClaimableHTLC         (amount : Nat) (outbound : Bool)
  | maybePreimageClaimableHTLC        (amount : Nat)

def LnBalance.weight : LnBalance → Nat
  | .claimableOnClose a                  => a
  | .claimableAwaitingConfirmations a    => a
  | .contentiousClaimable a              => a
  | .counterpartyRevokedOutputClaimable a => a
  | .maybeTimeoutClaimableHTLC a true    => 0
  | .maybeTimeoutClaimableHTLC a false   => a
  | .maybePreimageClaimableHTLC _        => 0

def totalLightning (bs : List LnBalance) : Nat :=
  (bs.map LnBalance.weight).sum

theorem totalLightning_eq_sum_weight (bs : List LnBalance) :
    totalLightning bs = (bs.map LnBalance.weight).sum := rfl

theorem totalLightning_le_sum_amounts (bs : List LnBalance) :
    totalLightning bs ≤ (bs.map LnBalance.amount).sum
```

with `LnBalance.amount` returning the stored amount in every constructor.

**Hypotheses:** none beyond the list. The theorem is definitional; the value is in fixing the weights.

**Non-vacuity witness:** `[maybeTimeout 100 true, maybeTimeout 100 false, maybePreimage 50]` gives total 100, while the naive sum is 250 — so `totalLightning_le_sum_amounts` is strict. Adding `claimableOnClose 7` gives total 107.

**Why faithful:** it mirrors `claimable_amount_satoshis` (`channelmonitor.rs:1027-1039`) and the sum in `lib.rs:2384-2393`. It deliberately does **not** claim `total = Σ details`; the inequality is the honest statement.

**Fidelity risk:** medium: `claimableOnClose`'s amount is abstracted (T3 supplies the sentinel). The model does not reproduce rust-lightning's per-channel monitor aggregation, only the weight algebra.

**Classification:** model extension.

**Feasibility:** high.

---

### T3 — Close-candidate sentinel (P1)

**Fully-qualified name:** `LnLean.Wallet.Balance.closeCandidate_zero_uses_last`
(companions: `closeCandidate_nonzero`, `closeCandidate_zero_can_overstate`)

**Statement shape:**

```lean
def closeCandidateAmount (candidates : List Nat) (confirmedIdx : Nat) : Nat :=
  if confirmedIdx ≠ 0 then candidates.getD confirmedIdx 0
  else candidates.getLast?.getD 0

theorem closeCandidate_zero_uses_last (c : List Nat) (h : c ≠ []) :
    closeCandidateAmount c 0 = c.getLast h

theorem closeCandidate_nonzero (c : List Nat) (i : Nat)
    (hi : i ≠ 0) (h : i < c.length) :
    closeCandidateAmount c i = c[i]

theorem closeCandidate_zero_can_overstate :
    ∃ c : List Nat, c ≠ [] ∧
      closeCandidateAmount c 0 ≠ c.headD 0
```

The third theorem is the important one: with `c = [100, 200]`, `closeCandidateAmount c 0 = 200` while `c.headD 0 = 100`. Frame it as a **reporting** possibility, not a bug.

**Hypotheses:** at the call site, `confirmedIdx ≠ 0` must be accompanied by `confirmedIdx < candidates.length`, because the Rust code indexes directly and panics otherwise. The model should take `getD` or an explicit bound; do not silently totalise away the panic without a hypothesis.

**Non-vacuity witness:** `[100, 200]` as above; `[100]` gives 100 whether index 0 selects the head or the last, because they coincide — showing the single-candidate case is unaffected.

**Why faithful:** mirrors `balance.rs:234-243` and `channelmonitor.rs:1032-1036` exactly. It also makes the docs/code tension explicit: `ClaimableOnChannelClose` says "confirmed state only" (`balance.rs:73-75`), while `last()` may be the unconfirmed pending splice.

**Fidelity risk:** medium-high. The model has no funding-candidate provenance; `confirmedIdx` is an uninterpreted `Nat` and the list is a list of amounts. It cannot prove that `last()` is unconfirmed — only that it *can* differ from the confirmed head. Do not phrase the target as "the reported balance is wrong"; phrase it as "the sentinel selection is non-injective and may select a non-head candidate".

**Classification:** model extension + explicit doc caveat. The upstream choice is external behaviour, not an assumption we may silently replace.

**Feasibility:** high (list lemmas), but the specification must be worded carefully.

---

### T4 — Confirmed-UTXO selection and change contract (P0)

**Fully-qualified name:** `LnLean.Wallet.CoinSelect.selectConfirmed_only_confirmed`
(companions: `selectConfirmed_change_sound`, `selectConfirmed_change_complete`, `change_ambiguity_counterexample`)

**Statement shape:**

```lean
structure Outpoint where
  txid : Nat
  vout : Nat
deriving DecidableEq, Repr

structure Utxo where
  outpoint  : Outpoint
  value     : Nat
  confirmed : Bool
deriving DecidableEq, Repr

structure Selection where
  inputs  : List Utxo
  outputs : List Nat
  change  : Option Nat
  fee     : Nat

-- `select` is an abstract BDK coin-selection oracle.
def selectConfirmed
    (u : List Utxo) (mustSpend : List Outpoint)
    (mustPay : List Nat) (feeRate : Nat) : Option Selection := ...

theorem selectConfirmed_only_confirmed
    (u : List Utxo) (ms : List Outpoint) (mp : List Nat) (fr : Nat)
    (s : Selection) (h : selectConfirmed u ms mp fr = some s) :
    ∀ x ∈ s.inputs, x.confirmed = true

theorem selectConfirmed_excludes_mustSpend
    (u : List Utxo) (ms : List Outpoint) (mp : List Nat) (fr : Nat)
    (s : Selection) (h : selectConfirmed u ms mp fr = some s) :
    ∀ x ∈ s.inputs, x.outpoint ∉ ms

theorem selectConfirmed_change_sound
    (u : List Utxo) (ms : List Outpoint) (mp : List Nat) (fr : Nat)
    (s : Selection) (h : selectConfirmed u ms mp fr = some s) :
    s.change.isSome → s.outputs.length = mp.length + 1

theorem selectConfirmed_change_complete
    (u : List Utxo) (ms : List Outpoint) (mp : List Nat) (fr : Nat)
    (s : Selection) (h : selectConfirmed u ms mp fr = some s)
    (hlen : s.outputs.length = mp.length + 1)
    (hdisjoint : ∀ o ∈ s.outputs, o ∉ mp) :
    s.change.isSome

theorem change_ambiguity_counterexample :
    ∃ (u : List Utxo) (ms : List Outpoint) (mp : List Nat) (s : Selection),
      selectConfirmed u ms mp 1 = some s ∧
      s.outputs.length = mp.length + 1 ∧
      s.change = none
```

**Hypotheses:**

- `selectConfirmed` is a *model* of the post-processing contract, not of BDK's branch-and-bound. The abstract oracle `select` is a parameter; the theorems constrain its **outputs**, not its optimality.
- `change_complete` needs output distinctness (`hdisjoint`), which is exactly the `.find` predicate in the Rust code.
- `change_sound` is unconditional on distinctness because `change = some` implies an extra output was found.

**Non-vacuity witness:** `u = [u1(100, confirmed), u2(50, confirmed), u3(80, unconfirmed)]`, `ms = []`, `mp = [70]`, fee 10. A valid selection uses `u1`, emits `[70, 20]`, `change = some 20`. `selectConfirmed_only_confirmed` holds; `u3` is never selected. For the counterexample: `mp = [20]` and change output `20` gives `outputs = [20, 20]`, `find` returns `none`, so `change = none` despite two outputs. For `excludes_mustSpend`: `ms = [u1.outpoint]` and `outputs = [70]`; the returned `inputs` must not contain `u1` even though BDK used it as a foreign input.

**Why faithful:** items 1–7 of §2.7 are the Rust control flow. The model's `outputs` are values only; scripts are abstracted, so the distinctness hypothesis is on values (the real predicate is on `TxOut` script+value). State that abstraction in the doc.

**Fidelity risk:** medium. `selectConfirmed` must be written so it is not vacuously `none`: include at least one concrete instance that returns `some` (the witness). Without that, all four theorems are vacuous. The oracle abstraction also means the model cannot claim BDK selects a *minimal* or *optimal* input set.

**Classification:** model extension with an abstract selection oracle; no external assumption.

**Feasibility:** high. This is the best-value target in the report: small state, concrete control flow, and a genuine counterexample.

---

### T5 — Sweep lifecycle and prune (P2)

**Fully-qualified name:** `LnLean.Wallet.Sweep.prune_after_delay`
(companions: `sweep_status_total`, `sweep_amount_invariant`)

**Statement shape:**

```lean
inductive SweepStatus where
  | pendingBroadcast
  | broadcastAwaitingConfirmation (broadcastHeight : Nat)
  | awaitingThresholdConfirmations (confirmationHeight : Nat)

structure TrackedOutput where
  amount : Nat
  status : SweepStatus

def shouldPrune (pruneDelay tip : Nat) : TrackedOutput → Bool
  | ⟨_, .awaitingThresholdConfirmations h⟩ => decide (h + pruneDelay - 1 ≤ tip)
  | _ => false

def sweepPass (pruneDelay tip : Nat) (outs : List TrackedOutput) : List TrackedOutput :=
  outs.filter (fun o => !shouldPrune pruneDelay tip o)

theorem prune_after_delay
    (pruneDelay tip h : Nat) (amount : Nat)
    (hle : h + pruneDelay - 1 ≤ tip) :
    sweepPass pruneDelay tip [⟨amount, .awaitingThresholdConfirmations h⟩] = []

theorem retained_before_delay
    (pruneDelay tip h : Nat) (amount : Nat)
    (hlt : tip < h + pruneDelay - 1) :
    sweepPass pruneDelay tip [⟨amount, .awaitingThresholdConfirmations h⟩] =
      [⟨amount, .awaitingThresholdConfirmations h⟩]

theorem sweep_amount_invariant
    (o : TrackedOutput) (o' : TrackedOutput)
    (h : step o = some o') :
    o'.amount = o.amount
```

**Hypotheses:** `pruneDelay = 4038` is an external constant; state the theorem for a parameter `pruneDelay` and add a separate conformance lemma `pruneDelay_eq : PRUNE_DELAY_BLOCKS = 4038`. The height arithmetic uses `Nat` saturating subtraction, so `h + pruneDelay - 1` matches the Rust expression only when `pruneDelay ≥ 1`; add `0 < pruneDelay`.

**Non-vacuity witness:** `h = 100`, `pruneDelay = 4038`: at `tip = 4137` the output is pruned; at `tip = 4136` it is retained. The amount invariance witness is the `PendingBroadcast → BroadcastAwaitingConfirmation` transition, which keeps `amount` unchanged (`balance.rs:357-399`).

**Why faithful:** the three constructors and the prune condition are the pinned `PendingSweepBalance` and `sweep.rs:636`. The `step` relation abstracts the sweeper's internal tx replacement; the amount invariance is the only thing the public enum actually guarantees.

**Fidelity risk:** medium. The real sweeper can rebroadcast and replace the spending transaction, and a reorg can regress the state; the model captures height-based pruning, not rebroadcast strategy. The amount is derived from the descriptor and is invariant in the pinned mapping, but the model cannot prove the descriptor/value link.

**Classification:** model extension + one external constant (`PRUNE_DELAY_BLOCKS`).

**Feasibility:** high for the prune arithmetic; medium for the `step` relation if it is given real transition semantics.

---

### T6 — On-chain payment status and reorg regression (P2; coordinate with R03)

**Fully-qualified name:** `LnLean.Wallet.OnchainPayment.succeeded_iff_antiReorgDepth`
(companion: `txUnconfirmed_regresses_status`)

**Statement shape:**

```lean
inductive PayStatus where
  | pending
  | succeeded

def statusAt (antiReorg tip conf : Nat) : PayStatus :=
  if tip ≥ conf + antiReorg - 1 then .succeeded else .pending

theorem succeeded_iff_antiReorgDepth
    (antiReorg tip conf : Nat) (h : 0 < antiReorg) :
    statusAt antiReorg tip conf = .succeeded ↔ conf + antiReorg ≤ tip + 1

theorem txUnconfirmed_regresses_status :
    ∃ (p p' : PaymentRecord),
      p.status = .succeeded ∧ step .txUnconfirmed p = some p' ∧
      p'.status = .pending ∧ p'.confirmation = .unconfirmed
```

**Hypotheses:** `0 < antiReorg`; the payment record must distinguish funding from ordinary payments, because the pinned code treats them differently (`wallet/mod.rs:787-795` vs `:810-826`). The `step` relation needs a `kind : PaymentKind` field and a branch on it.

**Non-vacuity witness:** `conf = 100`, `tip = 105`, `antiReorg = 6`: `106 ≤ 106`, so `succeeded`; `tip = 104` gives `pending`. The regression witness is the pinned test sequence: confirmed at height 1, then reorged to unconfirmed (`tests/integration_tests_rust.rs:2160-2200`).

**Why faithful:** the threshold is `wallet/mod.rs:553-561`; the regression is `:775-828`. It is the balance-facing link between R03's chain model and a payment record.

**Fidelity risk:** medium. This overlaps R03's T1/T5 (`R03-l1-chain-sync-finality.md:280,494`), which own transaction membership and finality. **Do not implement both.** Recommendation: R03 owns the chain/state-machine theorem; this lane should at most add `statusAt` as a two-line corollary, or drop T6 entirely.

**Classification:** model extension, but **duplicative** unless scoped to the arithmetic link.

**Feasibility:** high; low marginal value.

---

### T7 — Wallet inventory conservation (P2)

**Fully-qualified name:** `LnLean.Wallet.Inventory.total_after_spend`
(companions: `spend_preserves_inventory_nodup`, `wallet_outpoints_disjoint`)

**Statement shape:**

```lean
structure Wallet where
  utxos : List Utxo

def Wallet.total (w : Wallet) : Nat := (w.utxos.map (·.value)).sum

def Wallet.spend (w : Wallet) (s : Selection) (changeCoins : List Utxo) : Wallet :=
  { utxos := w.utxos.filter (fun u => u.outpoint ∉ s.inputs.map (·.outpoint)) ++ changeCoins }

theorem total_after_spend
    (w : Wallet) (s : Selection) (changeCoins : List Utxo) (paid : Nat)
    (hsub : ∀ x ∈ s.inputs, x ∈ w.utxos)
    (hnodup : (s.inputs.map (·.outpoint)).Nodup)
    (hwalletNodup : (w.utxos.map (·.outpoint)).Nodup)
    (hcons : (s.inputs.map (·.value)).sum =
             (changeCoins.map (·.value)).sum + paid + s.fee) :
    (w.spend s changeCoins).total + s.fee + paid = w.total
```

**Hypotheses:** `hsub` (the selected inputs are owned), `hnodup` (no double spend within the tx), `hwalletNodup` (the inventory has no duplicate outpoints, so `filter` removes each input exactly once), and `hcons` (the per-transaction value law over **wallet-owned** outputs, the external payment, and the fee). `changeCoins` is the wallet-owned remainder only; `paid` is the total value sent to external recipients. The fee law is exactly what `single_tx_conservation` provides in spirit; the target can either assume `hcons` or derive it from the vendor theorem plus a `totalIn/totalOut` bridge.

**Non-vacuity witness:** wallet `[100, 50]`, spend `100`, change `20`, `paid = 70`, fee `10`: `total = 150`; after = `50 + 20 = 70`; `70 + 10 + 70 = 150`. A second witness with no change: wallet `[100]`, change `[]`, `paid = 90`, fee `10`; after = `0`, and `0 + 10 + 90 = 100`. A third witness with two inputs (`[100, 50]`, spend both, change `[120]`, `paid = 0`, fee `30`) gives `120 + 30 + 0 = 150`, so the theorem is not restricted to one input.

**Why faithful:** it is the wallet-level analogue of value conservation, and it does not reuse the broken vendor `applyTx` (`OutPoint.null`). The outpoint filter is the real ownership update; `changeCoins` must carry real `(txid, vout)` keys. The naive `after + fee = before` is **false** for a payment, because `paid` also leaves the wallet; `paid` must be explicit.

**Fidelity risk:** medium-low. It is a *model*; it does not prove that BDK's inventory and the descriptor-derived `changeCoins` agree, nor that `trusted_spendable` is a subset of `total`. It also does not model which input pays the fee; `hcons` is a total-value equation, not a per-input attribution. The `paid` parameter is not linked to the transaction's recipient outputs, so a caller could instantiate it inconsistently; the module doc must state that link.

**Classification:** model extension; `hcons` is an explicit per-tx assumption (or a bridge to vendor `single_tx_conservation`).

**Feasibility:** high (`List` sum algebra).

---

### T8 — Send-mode reserve guards (P1)

**Fully-qualified name:** `LnLean.Wallet.Send.guard_preserves_reported_reserve`
(companions: `allDraining_leaves_reserve_unfunded`, `retaining_dust_fallthrough`)

**Statement shape:**

```lean
inductive SendMode where
  | exact        (amount : Nat)
  | allRetaining (reserve : Nat)
  | allDraining

def guard (b : WalletBalance) (fee : Nat) : SendMode → Bool
  | .exact a        => decide (b.spendable ≥ a + fee)
  | .allRetaining r => decide (b.spendable ≥ b.total - min r b.total)
  | .allDraining    => true

theorem exact_guard_preserves_reserve
    (b : WalletBalance) (a fee : Nat)
    (hT : b.trustedSpendable ≤ b.total)
    (h : guard b fee (.exact a) = true) :
    a + fee + b.reportedReserve ≤ b.total

theorem retaining_guard_preserves_reserve
    (b : WalletBalance) (r drain : Nat)
    (h : guard b 0 (.allRetaining r) = true)
    (hdrain : drain = b.total - min r b.total) :
    drain + min r b.total ≤ b.total

def drained (b : WalletBalance) : WalletBalance :=
  { b with total := 0, trustedSpendable := 0 }

theorem allDraining_leaves_reserve_unfunded :
    ∃ b : WalletBalance, b.curReserve > 0 ∧
      guard b 0 .allDraining = true ∧
      (drained b).total = 0 ∧ (drained b).reportedReserve = 0
```

The last theorem is the negative one: after `allDraining`, the wallet reports total 0 and reserve 0, so a separate **requirement** predicate `ReserveRequired b := b.curReserve > 0` (or a channel-count obligation evaluated outside the wallet) is not met. Keep the requirement separate from the report; do not define `ReserveRequired` as `reportedReserve > 0`, because the report clamps to the total and would make the counterexample vanish.

**Hypotheses:** the `allRetaining` guard compares `spendable` to the PSBT's `sent - received` (`wallet/mod.rs:2274-2279`), which is intended to equal the post-reserve drain but is not definitionally `spendable`. The model's `b.total - min r b.total` is an idealisation; add a hypothesis that the PSBT drain equals the modelled drain.

**Non-vacuity witness:** `b = ⟨1000, 1000, 1000⟩` (anchor channel open, all funds reserved): `spendable = 0`, so `exact 1` fails and `allRetaining` drains 0; `allDraining` is `true` and `drained b` has total 0. The test witness is `node_b.list_balances().total_onchain_balance_sats = reserve_amount_sat` after retaining (`tests/integration_tests_rust.rs:2281-2282`) versus `total = 0` after draining (`:2123-2124`).

**Why faithful:** it encodes the two guards that exist and the one that does not. The `allDraining` branch is intentionally unguarded in the pinned code (`wallet/mod.rs:2288`), and the server hardcodes `retain_reserves = true` (`onchain_send.rs:40-42`), so the unguarded branch is reachable only through the node API.

**Fidelity risk:** medium. The model's `reportedReserve` is a *report*, not a funded earmark; the theorem says "the report is not breached", not "the anchor reserve is actually spendable". The ≥ 546 fall-through (`wallet/mod.rs:2202-2210`) must be a separate counterexample, not hidden:

```lean
theorem retaining_dust_fallthrough :
    ∃ (r : Nat), r ≤ 546 ∧
      -- the builder branch is the drain-all branch
      branch r = .drainAll
```

**Classification:** model extension; the server hardcode is an external conformance fact.

**Feasibility:** high for the guard algebra; medium for the PSBT drain equality.

---

### Target summary

| # | Name | Priority | Fidelity risk | Feasibility | Classification |
|---|---|---|---|---|---|
| T1 | `LnLean.Wallet.Balance.spendable_add_reportedReserve_le_total` | **P0** | Low (arity) / medium (input meaning) | High | Model extension |
| T4 | `LnLean.Wallet.CoinSelect.selectConfirmed_only_confirmed` | **P0** | Medium (oracle abstraction) | High | Model extension |
| T2 | `LnLean.Wallet.Balance.totalLightning_eq_sum_weight` | P1 | Medium | High | Model extension |
| T3 | `LnLean.Wallet.Balance.closeCandidate_zero_uses_last` | P1 | Medium-high (provenance absent) | High | Model extension + doc caveat |
| T8 | `LnLean.Wallet.Send.guard_preserves_reported_reserve` | P1 | Medium (report vs funded reserve) | Medium | Model extension |
| T5 | `LnLean.Wallet.Sweep.prune_after_delay` | P2 | Medium | High/medium | Model extension + external constant |
| T6 | `LnLean.Wallet.OnchainPayment.succeeded_iff_antiReorgDepth` | P2 | Medium | High | Model extension, **overlaps R03** |
| T7 | `LnLean.Wallet.Inventory.total_after_spend` | P2 | Medium-low | High | Model extension + explicit value hypothesis (`fee` + `paid`) |

---

## 5. Assumptions, counterexamples, and non-vacuity risks

### 5.1 Existing witnesses that must be preserved

The new lane must not displace or weaken:

- **Channel reserve laws.** `ReserveProps` witnesses (`reserve_not_always_within_capacity` at `:157`, `step_preserves_reserveInvariant` at `:182`) stay as they are. The wallet anchor reserve is a **different** quantity; do not reuse `localReserveSat`.
- **L1 no-double-spend.** `L1Ledger.spend_preserves_noDoubleSpend` (`Invariants.lean:180-184`) keeps the explicit `fresh` hypothesis. A wallet-level theorem that admits two competing spends would make the corresponding `NoDoubleSpend` false.
- **D32 value conservation.** `waveD_d32_l1SpendSet_conserved` (`D32.lean:181-186`) and `waveD_d32_global_conservation` (`:388-397`) keep their `AllConserved` and `L1SpendsChannels` hypotheses. The wallet inventory theorem is a different theorem, not a replacement.
- **Vendor conservation.** `single_tx_conservation` (`Interface.lean:96-110`) keeps `hle : totalOut ≤ totalIn`; it is not a non-negative-fee theorem without it.
- **Integration witnesses.** The premine/channel-open/send-all assertions (`tests/integration_tests_rust.rs:2227-2285`), the sweep state witness (`:944-958`), and the reorg witness (`:2137-2200`) are the non-vacuity anchors for T1/T5/T6/T8. A target whose model cannot reproduce at least one of these numbers should be rejected.

### 5.2 Counterexamples that must stay visible

1. **RBF / competing claim.** Before one of two conflicting spends confirms, both can be valid relay candidates. `L1Ledger.NoDoubleSpend` is preserved only because the model admits the *fresh* spend as the state transition; a wallet-level "no two spends of the same outpoint exist" theorem is false without a freshness/confirmation side condition. `TxReplaced` (`wallet/mod.rs:830+`) is the concrete event.
2. **Change ambiguity.** `outputs = [20, 20]` with `mustPay = [20]` gives `outputs.length = mustPay.length + 1` but `find` returns `none` (`wallet/mod.rs:2415-2418`). The changeset is then not persisted on the splice path.
3. **All-draining reserve breach.** `AllDrainingReserve` has no guard (`wallet/mod.rs:2288`); `send_all_to_address(..., false, ...)` drains the wallet even with open anchor channels (`payment/onchain.rs:101-125`). The integration test's `total = 0` assertion (`tests/integration_tests_rust.rs:2123-2124`) is the witness.
4. **Retaining-dust fall-through.** `AllRetainingReserve` with `cur_anchor_reserve_sats ≤ 546` takes the `drain_wallet` branch (`wallet/mod.rs:2202-2210`), so "retain" does not retain.
5. **Reserve clamp.** `cur_reserve > total` gives `spendable = 0` and `reportedReserve = total` (`wallet/mod.rs:1998-2001`, `lib.rs:2368-2369`); `spendable + reserve = total` then holds only because both sides collapse. With `trusted < total` it fails.
6. **Pending-splice sentinel.** `candidates = [confirmed 100, pending 200]`, `confirmedIdx = 0` → reported 200 (`balance.rs:234-243`, `channelmonitor.rs:1032-1036`). The `ClaimableOnChannelClose` doc's "confirmed state only" (`balance.rs:73-75`) is not what the arithmetic computes.
7. **Naive Lightning sum.** `[outbound MaybeTimeout 100, inbound MaybeTimeout 100, MaybePreimage 50]` sums to 250 but `total_lightning = 100`.
8. **Payment-status regression.** Confirmed → unconfirmed after a one-block reorg (`wallet/mod.rs:775-828`, test `:2137-2200`).
9. **Vendor inventory key.** `applyTx` inserts at `OutPoint.null` (`Utxo.lean:46-52`), so it cannot witness a two-UTXO wallet with distinct outpoints.
10. **Sweep amount is not a balance.** `pending_balances_from_channel_closures` may or may not already be in `total_onchain_balance_sats` (`balance.rs:59-66`); summing the two views is not conservation.

### 5.3 Proposals that would weaken or hide an assumption

Reject any of the following:

- `spendable + reportedReserve = total` **unconditionally** (false when `trusted < total`; at the clamp it holds only because both sides collapse). Use `≤`, with equality under `trusted = total ∧ cur ≤ total`.
- `total_lightning = Σ detail.amount_satoshis` (false because of the zero weights).
- `PaymentStatus` is monotone (false under `TxUnconfirmed`).
- "All wallet spends are confirmed-only" (only the splice `CoinSelectionSource` calls `exclude_unconfirmed`; `send_to_address` does not).
- "Change is persisted whenever `outputs = mustPay + 1`" (false without distinctness; the `.find` is structural).
- "The wallet owns exactly the confirmed UTXOs" (the wallet also holds unconfirmed change and may hold non-witness outputs; `list_confirmed_utxos_inner` filters both).
- "The close balance is the confirmed candidate" (index 0 selects `last()`; the two differ when a splice is pending).
- "The anchor reserve is funded by specific UTXOs" (it is a read-time count × constant; no earmarking).
- Reusing vendor `applyTx` as if it keyed coins by txid (it does not).
- `after + fee = before` for an ordinary on-chain payment: the external recipient value `paid` also leaves the wallet. The conservation is `after + fee + paid = before` (T7).
- Treating `pending_balances_from_channel_closures` as additive to `total_onchain` (the doc says otherwise).

### 5.4 External assumptions (not Lean theorems)

These must be named as assumptions or conformance facts, never proved inside the lane:

- **BDK coin selection** returns a valid, fee-sufficient selection over the wallet's confirmed coins. T4 constrains the *post-processing*, not BDK's optimality.
- **`trusted_spendable`** is a faithful subset of `total` and reflects the intended confirmation policy. T1 assumes `trusted ≤ total`.
- **`total` is the sum of the owned UTXOs.** T1 treats `total` as an input; T7 proves the inventory-side sum. The equation `WalletBalance.total = Wallet.total` is a modelling identification, not a theorem about BDK.
- **`claimable_amount_satoshis`** and the candidate ordering are rust-lightning behaviour. T2/T3 model them; they do not verify them.
- **Anchor reserve policy** (`trusted_peers_no_reserve`, `per_channel_reserve_sats`, channel-type eligibility) is configuration, not consensus.
- **`PRUNE_DELAY_BLOCKS = 4038`** and `ANTI_REORG_DELAY = 6` are rust-lightning constants; the Lean theorems should take them as parameters plus a `= 4038`/`= 6` conformance lemma.
- **Chain tip, reorg depth, and transaction membership** are R03's domain. T6 must not assume them silently.
- **Wallet persistence durability** (the changeset write succeeds and survives a crash) is outside the model. The splice path's conditional persistence (§2.7) is a *code* property; a Lean model can state "if persisted then change is present", not "persistence always happens".

---

## 6. Wave-13 recommendation

**Recommendation: DEFER the full lane; authorise at most a bounded T1 + T4 model extension, and only under a new wallet-lane owner.**

Reasons:

1. **No catalog home.** There is no `LN-L1-007` or wallet-domain row. Adding one is a catalog/doc change outside this read-only lane. The parent should decide whether the new surface belongs under `LN-L1` (on-chain wallet) or a new `LN-WALLET` domain; do not silently attach it to `LN-SEC-002`, whose scope note explicitly excludes the L1 half.
2. **The highest-value targets are small.** T1 is arithmetic; T4 is a post-processing contract with one genuine counterexample. Both are self-contained, have concrete witnesses, and do not require the vendor tree or a chain model. They are the only targets I would call safe for wave 13.
3. **The rest either duplicate R03 or are external.** T6 overlaps R03's confirmation/finality work; T5/T7/T8 are useful but lower value and need more model scaffolding (a real `step` relation, a PSBT drain equality, a sweep transition system).
4. **Production equivalence is not achievable here.** The model can state the *reporting contract* and the *reserve partition*, but it cannot prove that BDK's `trusted_spendable`, rust-lightning's candidate ordering, or the anchor reserve policy are correct. Any claim of "LDK wallet balance is verified" would be false.

**If the parent authorises implementation (wave 13):**

- Implement **T1** and **T4** only, as `LnLean.Wallet.Balance` and `LnLean.Wallet.CoinSelect`, with the witnesses in §4.
- Add **T2** and **T3** only if the same author also wants the Lightning projection; they are cheap but T3 needs careful doc wording.
- Defer **T5–T8**. Do not open T6 in this lane; hand it to R03.
- Add a `docs/OPEN-ISSUES.md` note that the wallet surface is a *new* lane, and do **not** mark any external P0/P1 as closed.
- Do not edit `Obligations.lean` in the implementation PR without an explicit catalog-owner decision.

**If the parent does not authorise a new lane:** record this report as an explicit external/human barrier. The gap is real but not a regression; the existing theorems remain sound.

---

## 7. Evidence and commands

### 7.1 Repository state

```
branch : repair/integrated
HEAD   : f7f062817c185cd70004bb26c652deb99c6fd4bd
status : no tracked modifications; agents/reports/wave13-review/ untracked (pre-existing)
```

No Lean, docs, scripts, tests, vendor, or other reports were edited. The only write in this lane is this file.

### 7.2 Pinned reference heads

```
LDK Node   : /tmp/opencode/ldk-refs/ldk-node   @ fa123fed131e27ecc420b77fa7086fcf1ddaebb8
LDK Server : /tmp/opencode/ldk-refs/ldk-server @ c17dc11dde38f88c53457039ddf30c6b90a63ba2
```

`agents/reports/wave13-review/LDK-REFS.md` records the pin note. The local rust-lightning source used for corroboration is `/tmp/opencode/rl-live/rust-lightning`; its checkout is not a git repository, and its revision is **not** asserted to equal LDK Node's `Cargo.lock` pin. The claimable-weight and prune-constant citations are therefore **corroborating**, not the exact ldk-node dependency. The ldk-node `Cargo.toml`/`Cargo.lock` pin should be checked before any implementation cites rust-lightning line numbers as normative.

### 7.3 Read-only checks performed

```bash
# Lean surface
rg -n "LN-L1-00|wallet|utxo|spendable|balance" LnLean/Proofs/Obligations.lean
sed -n '78,120p'  LnLean/Proofs/Obligations.lean
sed -n '150,200p' LnLean/Security/Invariants.lean
sed -n '100,200p' LnLean/Proofs/WaveD/D32.lean
sed -n '380,400p' LnLean/Proofs/WaveD/D32.lean
sed -n '80,100p'  LnLean/Proofs/Security/ReorgTargets.lean
sed -n '155,185p' LnLean/Proofs/Security/ReorgTargets.lean
sed -n '100,135p' LnLean/Proofs/Channel/ReserveProps.lean
sed -n '20,55p'   vendor/btc-lean-core/Bitcoin/Ledger/Utxo.lean
sed -n '90,115p'  vendor/btc-lean-core/Bitcoin/Conservation/Interface.lean

# LDK Node
sed -n '20,70p'    ldk-node/src/balance.rs
sed -n '220,250p'  ldk-node/src/balance.rs
sed -n '310,400p'  ldk-node/src/balance.rs
sed -n '1985,2010p' ldk-node/src/wallet/mod.rs
sed -n '540,570p'  ldk-node/src/wallet/mod.rs
sed -n '770,835p'  ldk-node/src/wallet/mod.rs
sed -n '2165,2350p' ldk-node/src/wallet/mod.rs
sed -n '2345,2440p' ldk-node/src/wallet/mod.rs
sed -n '2437,2520p' ldk-node/src/wallet/mod.rs
sed -n '2355,2410p' ldk-node/src/lib.rs
sed -n '2700,2740p' ldk-node/src/lib.rs
sed -n '70,135p'   ldk-node/src/payment/onchain.rs
sed -n '935,965p'  ldk-node/tests/integration_tests_rust.rs
sed -n '2060,2130p' ldk-node/tests/integration_tests_rust.rs
sed -n '2130,2205p' ldk-node/tests/integration_tests_rust.rs
sed -n '2220,2290p' ldk-node/tests/integration_tests_rust.rs

# LDK Server
sed -n '1,60p'   ldk-server/ldk-server/src/api/onchain_send.rs
sed -n '20,30p'  ldk-server/ldk-server/src/api/get_balances.rs

# rust-lightning corroboration
sed -n '870,900p'   rust-lightning/lightning/src/chain/channelmonitor.rs
sed -n '1015,1045p' rust-lightning/lightning/src/chain/channelmonitor.rs
sed -n '3240,3260p' rust-lightning/lightning/src/chain/channelmonitor.rs
sed -n '344,353p'   rust-lightning/lightning/src/chain/channelmonitor.rs
sed -n '44,50p'     rust-lightning/lightning/src/util/sweep.rs
sed -n '630,640p'   rust-lightning/lightning/src/util/sweep.rs
```

No `lake build`, `cargo test`, network fetch, or worktree-changing command was run.

### 7.4 Primary references

- BOLT 3 §Funding Transaction Output; BOLT 3 §to_local / anchor outputs (already cited by `LN-L1-001`/`004`/`005`).
- BOLT 5 §Recommendations for Efficient Implementation (`ANTI_REORG_DELAY` semantics; corroborated by `ReorgTargets.lean:77-95`).
- LDK Node `BalanceDetails` docs (`src/balance.rs:21-67`) and `PendingSweepBalance` docs (`:318-356`).
- LDK Node wallet event handling (`src/wallet/mod.rs:553-561`, `:775-828`).
- LDK Node coin selection (`src/wallet/mod.rs:2350-2435`) and ordinary send (`:2170-2288`).
- rust-lightning `Balance::claimable_amount_satoshis` (`channelmonitor.rs:1027-1039`) and candidate construction (`:3245-3258`).
- rust-lightning `PRUNE_DELAY_BLOCKS` (`sweep.rs:47`) and prune condition (`:636`).

### 7.5 Review boundary

This report does **not** claim:

- that LDK Node or LDK Server has a bug;
- that the Lean model is unsound or incomplete in a way that weakens an existing theorem;
- that any of T1–T8 is implemented, proved, or in the catalog;
- that the pinned rust-lightning checkout equals LDK Node's dependency revision.

It claims only that the wallet surface is **unmodelled**, that the listed LDK behaviors are the concrete ones a future model must reproduce or explicitly assume, and that T1/T4 are the only targets small enough and well-witnessed enough to consider for wave 13.
