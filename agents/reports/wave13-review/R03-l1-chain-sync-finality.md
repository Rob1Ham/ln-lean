# R03 — Chain sync, confirmations, reorgs, and finality

**Status:** read-only review
**Pins:** LDK Node `fa123fed131e27ecc420b77fa7086fcf1ddaebb8`, LDK Server `c17dc11dde38f88c53457039ddf30c6b90a63ba2`
**Scope:** catalog row `LN-L1-003`, open issue `L1-06`, and the chain-source / confirmation / reorg surface of LDK Node and LDK Server. This report scopes work; it does not implement it.
**Owned deliverable:** `agents/reports/wave13-review/R03-l1-chain-sync-finality.md` only.

## 1. Scope and current Lean surface

`LN-L1-003` is marked `proved` in `docs/THEOREM-INDEX.md:39` and
`docs/TRACEABILITY.md:18`, while `L1-06` remains open at P2 because the result
is conditional on a common tip and a bounded reorg depth and because no
PoW/probabilistic chain model exists (`docs/OPEN-ISSUES.md:52`). Those two
statements are consistent: the Lean theorems prove a finite, conditional
arithmetic statement. The review question is whether the *named* objects —
transaction confirmation, canonical tip, chain source, stale view, and
finality — mean what the catalog sentence suggests.

The brief's path `LnLean/Proofs/Bitcoin/ReorgTargets.lean` is stale. There is
no such file and no `LnLean/Bitcoin/` chain/reorg module. The actual modules
are:

| Layer | Module | What it proves | What it does not model |
|---|---|---|---|
| Abstract channel reorg | `LnLean/Proofs/Security/ReorgTargets.lean` | `antiReorgDelay = 6`; confirmation-count arithmetic; `SameChain`; `Observations.SafeAt`; budget-relative retention and channel-safety preservation | A block graph, transaction inclusion, chainwork, source failure, or ledger rollback |
| Finite block graph | `LnLean/Proofs/Security/ChainFinalityTargets.lean` | `Block`/`Chain`; `WellFormed`; `bounded_depth_finality`; `ConfirmedTx`; `UniqueCanonicalTip`; bridges to `ReorgTargets` | Transaction membership, work-based tip choice, `Active`/`ValidFork`, sync liveness |
| Per-tip arithmetic | `LnLean/Proofs/WaveD/D02.lean` | The same confirmation arithmetic on `ChannelReorgState`; `no_finite_confirmation_depth` | A live chain or cumulative multi-reorg budget |
| Concrete common-tip instance | `LnLean/Proofs/WaveH/H45.lean` | A nonempty facts instance, the budget/depth boundary, and `OutOfReachOf` vs `SafeAt` | Chain-source behavior |
| Model vocabulary | `LnLean/Security/Model.lean` | `Reorg { fromHeight, depth, newTip }`; `ChainView { height, tip, lastReorg }`; `Adversary.reorgAllowed` | Any semantics for `tip`, `newTip`, or `lastReorg` |
| Vendored chainwork | `vendor/btc-lean-core/Bitcoin/Block/Index.lean` | `workOf`, `chainWork`, `Tip`, `betterThan`, `mostWork?`, `reorgPlan`, `reorgTo` | Not imported by the finality layer |

Both `ChainFinalityTargets` and `ReorgTargets` are root-imported
(`LnLean.lean:164-165`). The review scanned them for `sorry`, `admit`, and
`axiom`; none were found. That is a text scan, not a replacement for a kernel
build.

### 1.1 `ReorgTargets`: the conditional channel-safety theorem

The module fixes `antiReorgDelay : Nat := 6` (`ReorgTargets.lean:84`) and
`confirmationCount tip h := tip + 1 - h` (`:89`). A depth-`r.depth` reorg
retains height `h` exactly when `r.depth < confirmationCount tip h`
(`:94-95`). `SameChain` is only height plus tip bytes (`:120-121`), and
`Observations.SafeAt` is:

* `o.ledger.Conserves`, and
* every fact `e ∈ o.facts` satisfies `a.reorgBudget < e.confirmations v.height`
  (`:191-194`).

`reorg_preserves_channel_safety` (`:299-315`) assumes `SameChain v w`,
`o.SafeAt v a`, and `a.reorgAllowed r`, and concludes both retention and
`SafeAt` at the second view. `reorg_preserves_channel_safety_within_anti_reorg_delay`
(`:322-333`) turns `a.reorgBudget < 6` plus all facts settled into that
hypothesis. The negative results are load-bearing:

* `deep_reorg_separate_failure_mode` (`:427-450`) exhibits a settled channel
  that loses a fact to any reorg of depth at least six;
* `deep_reorg_not_allowed` (`:452-462`) shows that reorg is outside the
  depth-five budget;
* `safety_not_unconditional` (`:464-495`) refutes the unconditional reading;
* `common_tip_needed` (`:498-515`) and
  `safety_judgement_needs_common_tip` (`:517-537`) show that `SameChain` and
  the common tip are hypotheses, not derivable facts.

### 1.2 `ChainFinalityTargets`: the finite graph

`Block` has only `hash`, `parent`, and `height` (`ChainFinalityTargets.lean:63-67`).
`Chain` is a list indexed by height (`:72-74`). `ConfirmedAtDepth c h d` is
`d < c.confirmations h`, i.e. at least `d + 1` confirmations (`:90-100`).
`bounded_depth_finality` (`:256-269`) is the arithmetic core: a common
ancestor plus `c.length - a.length ≤ d` plus confirmation at depth `d` forces
the block at height `h` to be equal on both chains.

`WellFormed` (`:133-134`) is defined but is not a hypothesis of
`bounded_depth_finality`, `confirmed_tx_not_reorged`, or `OnChain`. The
theorems reason about list positions, not validated block heights. A chain
whose `Block.height` field disagrees with its list index still satisfies
`OnChain` and the finality arithmetic; all concrete witnesses in the module
are well formed, but a future consumer must not assume the finality theorem
validates linkage or height claims.

`ConfirmedTx` has `txid`, `blockHash`, and `height` (`:294-298`), but
`OnChain` only checks that the block at that height exists and has the recorded
hash (`:304-305`). `confirmed_tx_not_reorged` (`:331-338`) transfers the block
equality from `bounded_depth_finality`; it never uses `t.txid`. In the whole
file, `txid` occurs only in the structure and in the three witness literals
(`:295`, `:532`, `:536`, `:691`); no proof eliminates or reasons about it.

`UniqueCanonicalTip` (`:342-345`) is length-maximality plus "equal length
implies equal block list". It does not mention chainwork, difficulty, or a
tie-break. `unique_tip_finality` (`:362-372`) therefore combines a real
bounded-depth argument with a *length-based* family assumption.

The graph layer has a bridge section (`:374-502`), but it is a bridge of
predicates, not of the two named semantics:

* `sameChain_view_of_length_eq` (`:391-397`) makes any two equal-length chains
  `SameChain` when they are given the same opaque tip tag;
* `reorgSurvives_iff_chain_prefix` (`:409-415`) and
  `outOfReachOf_iff_chain_prefix` (`:447-465`) identify the abstract
  confirmation arithmetic with graph height arithmetic;
* `chain_finality_and_retention` (`:488-502`) pairs `Retains` with block
  equality for facts in `o.facts`, but the `Retains` half comes from
  `reorg_retains_of_depth_bound` (height arithmetic), and the block-equality
  half comes from `retained_fact_of_commonAncestor_depth`. It does not prove
  `ConfirmedTx.OnChain` implies any `OnchainFact` membership.

### 1.3 The unbridged seams

There are four separate seams:

1. **Transaction identity vs block identity.** `Block` has no transaction set,
   so `OnChain` cannot mention `txid`.
2. **Abstract view vs block content.** `Chain.view` (`:381-383`) sets
   `height := c.tipHeight` and `tip :=` a caller-supplied byte array. Any two
   equal-length chains can be `SameChain` under one tag, regardless of their
   blocks.
3. **Reorg retention vs ledger.** `applyReorgAt_ledger_eq` (`ReorgTargets.lean:232-234`)
   is `rfl`: the ledger is unchanged by construction. `Retains` only says the
   ledger field is equal and the fact list does not shrink (`:227-228`).
4. **Static view vs live sync.** `SafeAt` is a predicate on an already observed
   view. Nothing in Lean says that view is current, reachable, or sourced from
   the same chain as another node.

## 2. LDK datapoints (with `file:line`)

### 2.1 One configured chain source, with different trust levels

LDK Server requires exactly one of `[bitcoind]`, `[electrum]`, or `[esplora]`
(`/tmp/opencode/ldk-refs/ldk-server/docs/configuration.md:174-188`). Bitcoind is
described as "Recommended. Most reliable and private option"; Electrum
"relies on a trusted third-party server for chain data"; Esplora is "not
recommended for production use" (`:178-188`). The same document warns that
with Electrum or Esplora, "LDK cannot verify Lightning gossip messages against
the blockchain" (`:186-188`). Server startup maps exactly one `ChainSource` to
one builder call (`ldk-server/src/main.rs:176-221`; bitcoind RPC/REST at
`:187-205`, Electrum at `:207-213`, Esplora at `:214-220`).

LDK Node's internal enum has the same three variants
(`ldk-node/src/chain/mod.rs:156-170`). `is_transaction_based` is `true` for
Esplora and Electrum and `false` for Bitcoind (`:364-372`), which changes the
sync path.

The Lean `ChainView.tip` is an opaque `ByteArray` (`Model.lean:114-118`). It has
no source, no authentication, and no trust level. Any theorem that assumes a
common tip is therefore also assuming agreement with whatever source produced
that tip.

### 2.2 Background syncing can fail silently and leave a stale view

`Node::sync_wallets` first calls `update_fee_rate_estimates().await?` and only
then syncs the Lightning and on-chain wallets
(`ldk-node/src/lib.rs:2202-2225`; fee estimate at `:2213-2221`). In the manual
`sync_wallets` path, a fee-estimation failure therefore aborts the tip update
before any wallet sync, even though fee estimation is not a chain-tip fact.

The background loop is more permissive: every sync branch discards the result
with `let _ = ...` (`ldk-node/src/chain/mod.rs:528`, `:531`, `:534`). A failed
tip poll, wallet sync, or fee update is logged only if the callee logs it; the
loop continues to the next interval. Default intervals are 80 seconds for the
on-chain wallet and 30 seconds for the Lightning wallet
(`ldk-node/src/config.rs:28-30`; documented at `:590-592`, wired at `:615-617`).
The public status field is the "best block to which our Lightning wallet is
currently synced" (`ldk-node/src/lib.rs:2614-2615`), not the network tip. The
optional `latest_*_sync_timestamp` fields (`:2616-2625`) record success, but
the Lean model has no such timestamp or staleness predicate.

For the Bitcoind path, `poll_and_update_listeners_inner` only writes the new
tip on `Ok((ChainTip::Better(tip), true))` (`ldk-node/src/chain/bitcoind.rs:481-515`;
the write is at `:506-511`). Any other `Ok` shape is ignored, and an error
returns `Error::TxSyncFailed` (`:512-515`). Header validation is done at startup
through `validate_best_block_header` (`:427`). The point for Lean is not that
LDK fails to validate headers; it is that a local view can remain at an older
tip while the network has moved, and the Lean layer has no state for that.

### 2.3 A valid old fork is not the active tip

`bitcoind_rest_follows_valid_reorg` (`ldk-node/tests/reorg_test.rs:21-73`)
invalidates two blocks, generates three replacement blocks, and then
`reconsiderblock`s the old branch. Bitcoin Core reports the old tip as
`ChainTipsStatus::ValidFork` and the replacement as `Active` (`:47-60`). The
node must sync to the replacement hash and height (`:62-72`). This is a direct
witness that "valid" and "canonical" are different predicates.

The property test uses `reorg_depth in 1..=6usize` (`tests/reorg_test.rs:94`).
It funds channels, mines seven blocks (`:155-156`), invalidates and regenerates
`reorg_depth` blocks (`:120-123`, called at `:158-159`), and requires the
funding to remain confirmed across the deepest reorg. The test's boundary
therefore is: seven confirmations on the funding block survive a reorg of at
most six blocks. `ReorgTargets` and `ChainFinalityTargets` can prove that
arithmetic, but neither models the `ValidFork`/`Active` distinction.

### 2.4 Confirmation status is a transaction-level state machine

`PaymentKind::Onchain` includes `txid` and a `ConfirmationStatus`
(`ldk-node/src/payment/store.rs:524-536`). The enum is:

* `Confirmed { block_hash, height, timestamp }`;
* `Unconfirmed` (`store.rs:685-696`).

The doc comment says on-chain payments "will be considered pending until the
respective transaction has reached `ANTI_REORG_DELAY` confirmations"
(`store.rs:527-530`). Graduation checks `cur_height >= confirmation_height +
ANTI_REORG_DELAY - 1` (`ldk-node/src/wallet/mod.rs:556-558`), which is six
confirmations at tip `height + 5`; the `ChainTipChanged` path repeats the same
inequality (`:683-710`). `TxUnconfirmed` writes `ConfirmationStatus::Unconfirmed`
(`wallet/mod.rs:775-790`), and the integration test
`reorged_onchain_payment_returns_to_unconfirmed`
(`tests/integration_tests_rust.rs:2137-2198`) demonstrates a confirmed on-chain
payment becoming `Unconfirmed` after a one-block reorg (`:2160-2197`).

`funding_payment_graduates_without_channel_ready`
(`tests/integration_tests_rust.rs:3480-3528`) is a useful liveness datapoint:
node A syncs alone while node B stays behind; the funding payment is
`Succeeded` purely from wallet sync reaching `ANTI_REORG_DELAY`
(`:3503-3528`). Graduation is not driven by the Lightning `ChannelReady` event.
That is a concrete case where one node's local view is ahead of another's, and
the payment state depends on the local view.

### 2.5 "Six" is not the only threshold

`ANTI_REORG_DELAY` is the on-chain *payment* graduation threshold, but LDK
exposes other confirmation-dependent states:

* `ClaimableAwaitingConfirmations { confirmation_height, ... }` for a closed
  channel balance awaiting confirmations (`ldk-node/src/balance.rs:131-145`);
* `AwaitingThresholdConfirmations { confirmation_hash, confirmation_height, ... }`
  for a sweep awaiting threshold confirmations, pruned after
  `PRUNE_DELAY_BLOCKS` (`balance.rs:341-355`);
* a provenance path that requires an anchor to be buried past
  `2 * ANTI_REORG_DELAY` (`wallet/mod.rs:1127`).

These are not all the same policy as the single `antiReorgDelay = 6` applied to
every `OnchainFact`. The model's uniform threshold is faithful for the channel
monitor's anti-reorg delay, but not for every on-chain balance or sweep state.

### 2.6 Chainwork exists in the vendor tree but is not connected

`vendor/btc-lean-core/Bitcoin/Block/Index.lean` already has:

* `workOf` (`:50`), the compact-bits work function;
* `chainWork` (`:70`), the genesis-first fold;
* `Tip { hash, chainWork, sequence }` (`:96-100`);
* `betterThan` (`:107-109`), higher work first and lower `sequence` on a tie;
* `mostWork?` (`:125`) and `reorgPlan`/`TipState.reorgTo` (`:220`, `:333`).

`ChainFinalityTargets` imports none of this. Its `UniqueCanonicalTip` is
length-maximal, so a shorter heavier chain is not selected even though
`mostWork?` would select it. LDK Node itself consumes `ChainTip::Better` from
the backend (`ldk-node/src/chain/bitcoind.rs:506-511`); it does not implement a
separate chainwork rule in the Lean sense.

## 3. Gap matrix

| Behavior | Lean status | LDK evidence | Gap / counterexample | Priority |
|---|---|---|---|---|
| Confirmation count and depth arithmetic | **Covered faithfully.** `Chain.confirmations = length - h`, `ConfirmedAtDepth d := d < confirmations` (`ChainFinalityTargets.lean:90-100`); `confirmationCount = tip + 1 - h`, `reorgSurvives` (`ReorgTargets.lean:89-95`); same in `D02:96-120`. `not_survives_at_depth` (`ReorgTargets.lean:106-112`), `deep_boundary_is_sharp` (`ChainFinalityTargets.lean:759-770`), `sharp_depth_boundary` (`H45:422-434`). | On-chain payment graduates at `cur_height >= confirmation_height + ANTI_REORG_DELAY - 1` (`wallet/mod.rs:556-558`, `:683-710`); pending until six confirmations (`payment/store.rs:527-530`). | The off-by-one is aligned: six confirmations means tip `h + 5`. No arithmetic gap. Caveat: every count is at a *local* view. | P2 (no implementation needed) |
| Transaction inclusion (`txid` is actually in the block) | **Missing / contradicted as a transaction claim.** `Block` has no transaction list (`:63-67`); `OnChain` checks only `blockAt height = blockHash` (`:304-305`); `txid` is unused in every proof (only `:295`, `:532`, `:536`, `:691`). | `ConfirmationStatus::Confirmed { block_hash, height }` is a transaction status (`payment/store.rs:685-696`); the on-chain payment carries `txid` (`:524-536`); the reorg test keys on txid (`integration_tests_rust.rs:2160-2197`). | A `ConfirmedTx { txid := 999, blockHash := 100, height := 0 }` is `OnChain smallChain` by definition. `confirmed_tx_not_reorged` proves block-identity survival, not that the transaction is in the block. No Merkle root/commitment. | **P1** |
| Confirmed ↔ unconfirmed transition after a reorg | **Missing.** `ConfirmedTx` has no status (`:294-298`); `applyReorgAt` filters facts (`ReorgTargets.lean:221-223`); there is no `Unconfirmed` constructor or rollback theorem. | `ConfirmationStatus::{Confirmed, Unconfirmed}` (`payment/store.rs:685-696`); `TxUnconfirmed` writes `Unconfirmed` (`wallet/mod.rs:775-790`); `reorged_onchain_payment_returns_to_unconfirmed` (`integration_tests_rust.rs:2137-2198`). | Reorging a fact out of `o.facts` is not the same as returning a transaction to `Unconfirmed`; the model has no transaction state to transition. | **P1** |
| Reorg depth, fork point, and common ancestor | **Partially covered.** `CommonAncestor`/`PrefixOf`/`ReorgWithin` and `bounded_depth_finality` (`:104-120`, `:256-288`); `Reorg` carries only `fromHeight`, `depth`, `newTip` (`Model.lean:72-76`). `WellFormed` (`:133-134`) is not a hypothesis of the finality theorem. | Reorg depth 1..=6 is exercised by invalidating and regenerating tip blocks (`tests/reorg_test.rs:94`, `:120-123`, `:155-159`); the valid old fork stays `ValidFork` while the replacement is `Active` (`:21-73`). | One-shot pair of finite chains; no replacement chain sequence, no cumulative depth over repeated reorgs, no new-tip height. `applyReorgAt` evaluates survival at the observed tip, not at the replacement tip. The graph theorem uses list position as height, so a non-`WellFormed` `Block.height` is not rejected. | P2 |
| Common tip and `SameChain` | **Partially covered / semantic trap.** `SameChain` is height + tip (`ReorgTargets.lean:120-121`); `Chain.view` takes an arbitrary tip tag (`ChainFinalityTargets.lean:381-383`); `sameChain_view_of_length_eq` equates equal-length chains (`:391-397`). | `current_best_block` is the locally synced tip (`lib.rs:2614-2615`); background failures are swallowed (`chain/mod.rs:528-534`); a lagging or failed node need not share the tip. | `smallChain` and `otherChain` both have length three, yet `smallTx` is absent from `otherChain` (`:638-647`). They satisfy `SameChain` under one tag. `chain_finality_and_retention` never invokes `reorg_preserves_channel_safety`, so there is no theorem that `ConfirmedTx.OnChain` implies `Observations.SafeAt`. | **P1** |
| Unique canonical tip / chainwork | **Contradicted as a consensus model.** `UniqueCanonicalTip` is length-maximal plus equal-length-equal-blocks (`:342-345`); `unique_tip_finality` uses it (`:362-372`). | Vendor `workOf`/`chainWork`/`Tip`/`betterThan`/`mostWork?` (`Block/Index.lean:50`, `:70`, `:96-109`, `:125`); LDK follows the backend's `ChainTip::Better` (`bitcoind.rs:506-511`). | A length-three chain with total work 3 and a length-two chain with total work 20: `UniqueCanonicalTip` selects the former, `mostWork?` selects the latter. No difficulty adjustment or sequence tie-break in the finality layer. | **P1** |
| `Active` vs `ValidFork` and stale tips | **Missing.** No fork-status predicate; `lastReorg` is an uninterpreted option (`Model.lean:114-118`) and is not used in survival. `common_tip_needed` only shows disagreement is possible (`ReorgTargets.lean:498-515`). | The old branch remains `ValidFork`; the replacement is `Active` (`tests/reorg_test.rs:47-72`). A node can keep an old `current_best_block` until its next successful sync (`lib.rs:2614-2615`). | No `Active`/`ValidFork` state machine and no stale-view relation. A stale view can satisfy `SafeAt` at a height the canonical chain no longer has. | **P1** |
| Chain-source failure and eventual sync | **Unmodelled / external.** `SafeAt` is static; there is no time, trace, retry, or failure state. `common_tip_needed` is a possibility result, not an interface. | Background loop discards errors (`chain/mod.rs:528`, `:531`, `:534`); `sync_wallets` aborts on fee-estimate failure (`lib.rs:2213-2221`); Bitcoind ignores non-`Better` successes (`bitcoind.rs:506-511`); intervals 30/80 seconds (`config.rs:28-30`, `:590-592`). | No theorem can derive `SameChain` from "both nodes run the same software"; the common tip remains an external assumption. | **P1** (external) |
| Chain-source trust and provenance | **Unmodelled / external.** `ChainView.tip` is opaque bytes; no source, signature, or trust field (`Model.lean:114-118`). | LDK Server requires exactly one of bitcoind/electrum/esplora (`docs/configuration.md:174-188`); Electrum/Esplora are trusted third parties (`:183-188`); startup selects one (`main.rs:176-221`). | The model cannot distinguish a bitcoind tip from an Electrum/Esplora tip, or express the trusted-third-party assumption. | P2 (external) |
| Confirmation thresholds for claims, sweeps, and pruning | **Partially covered.** One `antiReorgDelay = 6` applies to every `OnchainFact` (`ReorgTargets.lean:84`, `:176-177`); `OnchainFact` has only height and amount (`:162-165`). | Payment graduation at six (`payment/store.rs:527-530`); `ClaimableAwaitingConfirmations` (`balance.rs:131-145`); `AwaitingThresholdConfirmations` (`:341-355`); `PRUNE_DELAY_BLOCKS` (`:343`); `2 * ANTI_REORG_DELAY` provenance (`wallet/mod.rs:1127`). | No per-fact policy. A sweep or claim with a threshold above six is treated as settled at six, which is too strong. | P2 |
| Ledger rollback on reorg | **Partially covered with a scope assumption / contradicted for funding-stage.** `applyReorgAt_ledger_eq` is `rfl` (`ReorgTargets.lean:232-234`); `Retains` only equates the ledger field and keeps facts (`:227-228`); D02 explicitly says the ledger is assumed unchanged (`D02:62-68`). | `TxUnconfirmed` writes `Unconfirmed` (`wallet/mod.rs:775-790`); the reorged payment test changes confirmed to unconfirmed (`integration_tests_rust.rs:2137-2198`); balances are confirmation-dependent (`balance.rs:131-145`, `:341-355`). | No rollback of an unconfirmed funding/claim, and no connection between `OnchainFact` eviction and a ledger change. The in-channel ledger is intentionally outside this model, but the catalog sentence can be read too broadly. | P2 |
| PoW / probabilistic finality | **Unmodelled / external.** `UniqueCanonicalTip` has no probability or work (`:342-345`); `D02.no_finite_confirmation_depth` (`D02:398-411`) shows no finite depth defeats an unbounded reorg. | LDK delegates best-chain selection to the backend; no probabilistic finality API is exposed in the pinned paths. | No hashrate, difficulty, attack-probability, or economic-finality model. This is the substance of open `L1-06`. | P2 (external) |

## 4. Proposed targets

These are proposals only. They are ordered by fidelity value, not by
implementation order. None is a claim that the existing theorems are false;
the existing proofs are sound for their stated definitions. The targets either
strengthen a definition to match its name, expose a missing bridge, or add a
conformance/negative witness.

| # | Proposed fully-qualified name | Priority | Classification | Fidelity risk | Feasibility |
|---|---|---|---|---|---|
| T1 | `LnLean.Proofs.Security.ChainFinalityTargets.confirmed_tx_membership_finality` | **P1** | Model extension (schema change) | Medium: membership only, not validity/Merkle | High (mechanical) |
| T2 | `LnLean.Proofs.Security.ChainFinalityTargets.onChain_of_local_prefix` | P2 | Bridge lemma (no new assumption) | Low | High |
| T3 | `LnLean.Proofs.Security.ReorgTargets.safeAt_iff_all_allowed_outOfReach` | P2 | Bridge lemma (no new assumption) | Low | High |
| T4 | `LnLean.Proofs.Security.ChainFinalityTargets.shorter_heavier_tip_wins` | **P1** | Model extension (new predicate/witness) | Medium: abstract work, no difficulty adjustment | Medium |
| T5 | `LnLean.Proofs.Security.ReorgTargets.safeForPolicy_retains` | P2 | Model extension (new policy record) | Medium: LDK threshold mapping is external | Medium |
| T6 | `LnLean.Proofs.WaveH.H45.ldk_seven_confirmation_six_deep` | P2 | Conformance witness (no new assumption) | Low | High |
| T7 | `LnLean.Proofs.Security.ReorgTargets.stale_view_can_satisfy_safeAt` | P2 | Interface + external liveness assumption | Medium: the flag is not a failure model | High |
| T8 | `LnLean.Proofs.Security.ChainFinalityTargets.sameChain_view_length_only` | **P1** | Guard theorem (no new assumption) | Low | High |

### T1 — Transaction-membership finality (top target)

**Proposed name:**
`LnLean.Proofs.Security.ChainFinalityTargets.confirmed_tx_membership_finality`.

**Statement shape:**

```lean
structure Block where
  hash : Nat
  parent : Option Nat
  height : Nat
  txids : List Nat

def ConfirmedTx.OnChain (t : ConfirmedTx) (c : Chain) : Prop :=
  ∃ b : Block, c.blockAt t.height = some b ∧
    b.hash = t.blockHash ∧ t.txid ∈ b.txids

theorem confirmed_tx_membership_finality
    {a c c' : Chain} {t : ConfirmedTx} {d : Nat}
    (ht : t.OnChain c)
    (hanc : Chain.CommonAncestor a c c')
    (hdepth : c.length - a.length ≤ d)
    (hconf : c.ConfirmedAtDepth t.height d) :
    t.OnChain c' := by
  -- `bounded_depth_finality` gives equality of the block at `t.height`;
  -- `onChain_of_blockAt_eq` must now also carry `t.txid ∈ b.txids`.
  -- proof obligation (proposal only; not compiled)
```

**Hypotheses:** exactly the existing finality hypotheses, with `OnChain`
strengthened to require transaction membership in the same block. `Block`
must carry a transaction list (or an equivalent concrete relation) because
`hash` alone is an opaque `Nat` and cannot encode contents.

**Non-vacuity witness:** add `txids := [7]` to the genesis block of
`smallChain`, `smallAlt`, and `smallPrefix`; `txids := [8]` to `smallChain`'s
tip block; and `txids := []` to `smallAlt`'s tip block and to `otherChain`'s
genesis block. Then `smallTx` remains `OnChain smallChain` and
`OnChain smallPrefix`, `smallTx_not_reorged` still transfers to `smallAlt`,
and `smallTx_rejected_without_prefix` still rejects `otherChain`. Add
`txids := [42]` to `deepChain`'s block 103 and `[]` to `deepFork`'s block 203;
`deepTx_not_on_fork` remains true. The existing `smallTipTx_rejected` still
works because `smallTipTx` is at height two and its tip block is not shared.

**Why faithful:** it makes the noun "transaction" in `confirmed_tx_not_reorged`
real: the conclusion says the same transaction id is in the block at that
height on the competing chain, not merely that a block with the same opaque
hash is present. It is still not transaction *validity*: no script, input,
output, or Merkle commitment is modelled. State that explicitly.

**Fidelity risk:** medium. A list of `Nat` transaction ids is a membership
oracle, not a block commitment. If T1 is implemented without a Merkle root or
at least an explicit `BlockTxSet` relation, a future reader could mistake it
for consensus inclusion. The report recommends the weaker membership reading
only.

**Feasibility:** high. The change is local to `Block`, `blk`, `OnChain`, the
witness definitions, and the `onChain_of_blockAt_eq` helper. `bounded_depth_finality`
is unaffected because it reasons about `blockAt` equality, not block fields.

**Classification:** model extension (schema change), not an external
assumption. It does not close `L1-06`.

### T2 — Local lagging-view transfer below the fork point

**Proposed name:**
`LnLean.Proofs.Security.ChainFinalityTargets.onChain_of_local_prefix`.

**Statement shape:**

```lean
theorem onChain_of_local_prefix
    {t : ConfirmedTx} {c c' : Chain}
    (hp : c'.PrefixOf c) (ht : t.OnChain c') :
    t.OnChain c := by
  -- `hp` gives `c.blocks = c'.blocks ++ rest`; the block at `t.height`
  -- is the same block on both chains.
  -- proof obligation (proposal only; not compiled)
```

**Hypotheses:** `c'` is a block-list prefix of canonical `c`, and `t` is
already on `c'`. No `WellFormed` hypothesis is needed for the block lookup;
`OnChain c'` supplies the height witness.

**Non-vacuity witness:** `smallPrefix` is a prefix of both `smallChain` and
`smallAlt` (`:565-573`), and `smallTx` is on `smallPrefix` at height zero.
The theorem transfers a genuinely shorter local view (length two) to a longer
canonical chain (length three). A local view that has seen a competing block at
the same height is not a prefix; `smallTipTx_onChain smallChain` plus
`smallTipTx_rejected` (`:611-636`) is the negative witness.

**Why faithful:** it captures the safe half of lagging: if a node's local
chain is a prefix of the canonical chain, confirmations below its tip are still
confirmations on the canonical chain, and a reorg above its tip does not
invalidate them. It deliberately does not claim the converse: a node on a
stale branch that is not a prefix can report a fact the canonical chain has
evicted.

**Fidelity risk:** low. The only semantic caveat is that `PrefixOf` is a list
prefix, not a time-ordered sync relation; the theorem says nothing about
whether the node will ever catch up.

**Feasibility:** high. It is a short list-prefix lemma and reuses the existing
witnesses.

**Classification:** bridge lemma using existing structures; no new assumption.

### T3 — Per-reorg reach vs whole-budget safety

**Proposed name:**
`LnLean.Proofs.Security.ReorgTargets.safeAt_iff_all_allowed_outOfReach`.

**Statement shape:**

```lean
theorem safeAt_iff_all_allowed_outOfReach
    {o : Observations} {v : ChainView} {a : Adversary} :
    o.SafeAt v a ↔
      o.ledger.Conserves ∧
        ∀ r : Reorg, a.reorgAllowed r → o.OutOfReachOf v r := by
  constructor
  · intro hsafe r hallowed
    exact fun e he => fact_survives_of_safeAt he hsafe hallowed
  · intro h
    refine ⟨h.1, ?_⟩
    intro e he
    -- instantiate `h.2` at depth `a.reorgBudget`, which is allowed by `le_rfl`
    exact h.2 { fromHeight := v.height, depth := a.reorgBudget,
                newTip := ByteArray.empty } (Nat.le_refl _) e he
```

**Hypotheses:** none beyond the definitions. The backward direction needs a
reorg of depth exactly `a.reorgBudget`; `fromHeight` and `newTip` are
irrelevant to `reorgAllowed` and `OutOfReachOf`.

**Non-vacuity witness:** `settledObservations` and `budgetFiveAdversary`
(`ReorgTargets.lean:339-368`) instantiate both sides. The existing
`outOfReach_not_sufficient_for_budget` (`H45:436-457`) remains true: it assumes
`OutOfReachOf` for *one* reorg, while T3 requires it for *every allowed*
reorg. This is the point of the target.

**Why faithful:** `reorg_preserves_channel_safety` is stated with the uniform
budget; `reorg_retains_of_depth_bound` is stated with one reorg. T3 records
exactly the missing equivalence and prevents a reader from thinking the
per-reorg theorem is the budget theorem. It does not identify a replacement
chain; it is still depth arithmetic.

**Fidelity risk:** low. It may be too easy to read as "all reorgs are
modelled"; the statement quantifies over the model's `Reorg` record, which has
only depth semantics.

**Feasibility:** high. It is a direct consequence of existing definitions.

**Classification:** bridge lemma; no new assumption.

### T4 — Length-maximal tip vs chainwork-maximal tip

**Proposed name:**
`LnLean.Proofs.Security.ChainFinalityTargets.shorter_heavier_tip_wins`
(with a companion `length_max_and_work_max_differ`).

**Statement shape:**

```lean
def Chain.workWith (w : Block → Nat) (c : Chain) : Nat :=
  (c.blocks.map w).sum

def UniqueCanonicalTipByWork (w : Block → Nat) (chains : List Chain)
    (c : Chain) : Prop :=
  c ∈ chains ∧
    ∀ c' ∈ chains,
      c'.workWith w ≤ c.workWith w ∧
        (c'.workWith w = c.workWith w → c'.blocks = c.blocks)

theorem shorter_heavier_tip_wins :
    ∃ (w : Block → Nat) (chains : List Chain) (cLen cWork : Chain),
      UniqueCanonicalTip chains cLen ∧
        UniqueCanonicalTipByWork w chains cWork ∧
        cWork.length < cLen.length ∧
        cLen.workWith w < cWork.workWith w := by
  -- two chains: one longer with less total work, one shorter with more.
  -- proof obligation (proposal only; not compiled)

-- Companion: `length_max_and_work_max_differ` follows immediately,
-- because `cWork.length < cLen.length` gives `cWork ≠ cLen`.
```

**Hypotheses:** `w` is an abstract per-block work function. The intended
instantiation is the vendor `Bitcoin.Block.Index.workOf` composed with a
block's `bits`, not an arbitrary function; the target keeps `w` explicit so
the model does not silently claim a difficulty model.

**Non-vacuity witness:** construct a length-three chain whose three blocks
each have work 1 and a length-two chain whose two blocks each have work 10.
`UniqueCanonicalTip` selects the length-three chain; `UniqueCanonicalTipByWork`
selects the length-two chain. Both families are finite and both witnesses are
well formed. This is exactly the shorter-heavier case that a length-based
predicate cannot represent.

**Why faithful:** Bitcoin's best-chain rule is chainwork first, with a
sequence tie-break, not raw length. `Bitcoin.Block.Index.betterThan`
(`:107-109`) and `mostWork?` (`:125`) already encode that rule. The target
does not replace `UniqueCanonicalTip`; it adds a second predicate and proves
they can disagree, preserving the existing `unique_tip_finality` as a
length-only result.

**Fidelity risk:** medium. Abstract work is not a difficulty-adjustment model,
and a concrete `workOf` instantiation would still need block `bits`. The
equal-work branch of `UniqueCanonicalTipByWork` is a finite-family uniqueness
assumption, not the vendor `sequence` tie-break. Do not call T4 a PoW model.
The safe claim is: "the current length-max predicate is not the consensus tip
rule; the vendor chainwork layer is the right building block."

**Feasibility:** medium. The witness is easy; wiring `bits`/`workOf` and
importing the vendor module is more work. The companion theorem can be done
first with abstract `w`.

**Classification:** model extension (new predicate and witness), not an
external assumption; the actual PoW/difficulty model remains external.

### T5 — Per-fact confirmation policy

**Proposed name:**
`LnLean.Proofs.Security.ReorgTargets.safeForPolicy_retains`.

**Statement shape:**

```lean
structure ConfirmationPolicy where
  requiredDepth : OnchainFact → Nat

def Observations.SafeForPolicy (p : ConfirmationPolicy)
    (o : Observations) (v : ChainView) (a : Adversary) : Prop :=
  o.ledger.Conserves ∧
    ∀ e ∈ o.facts,
      a.reorgBudget < p.requiredDepth e ∧
        p.requiredDepth e ≤ e.confirmations v.height

theorem safeForPolicy_retains
    {p : ConfirmationPolicy} {o : Observations} {v : ChainView}
    {a : Adversary} {r : Reorg}
    (hsafe : o.SafeForPolicy p v a)
    (hallowed : a.reorgAllowed r) :
    Retains o (o.applyReorgAt v.height r) ∧
      (o.applyReorgAt v.height r).SafeForPolicy p v a := by
  -- proof obligation (proposal only; not compiled)
```

**Hypotheses:** a policy maps each fact to its required depth; safety requires
the adversary's whole budget to be below that required depth and the fact to
have at least that many confirmations. The policy is intended to satisfy
`1 ≤ requiredDepth e` for every fact; zero-confirmation channels are a
separate trusted-peer policy, not a zero-depth instance of this theorem. The
existing uniform theorem is the special case
`p.requiredDepth := fun _ => antiReorgDelay`.

**Non-vacuity witness:** instantiate `p` with six for a funding fact and with
a larger value for a sweep/claim fact. The six-confirmation `settledObservations`
witness still satisfies the policy with `requiredDepth = 6`. A fact with
`requiredDepth = 7` at six confirmations fails the policy; that is the
negative witness that the uniform policy misses.

**Why faithful:** LDK's on-chain payment graduation uses
`ANTI_REORG_DELAY = 6` (`payment/store.rs:527-530`), but
`ClaimableAwaitingConfirmations` (`balance.rs:131-145`),
`AwaitingThresholdConfirmations` (`:341-355`), `PRUNE_DELAY_BLOCKS` (`:343`),
and the `2 * ANTI_REORG_DELAY` provenance path (`wallet/mod.rs:1127`) are not
the same threshold. A single constant applied to every fact is a
simplification.

**Fidelity risk:** medium. The policy mapping is a parameter, not extracted
from LDK; a wrong mapping could be worse than the uniform approximation. Keep
the mapping explicit and cite the exact LDK threshold for each fact kind.

**Feasibility:** medium. Adding a structure and a generalized theorem is
mechanical, but retrofitting `OnchainFact` with a kind or policy field touches
all witnesses. A side map `requiredDepth : OnchainFact → Nat` avoids changing
the structure at the cost of a less canonical interface.

**Classification:** model extension; the LDK threshold values are an external
conformance input, not proved in Lean.

### T6 — The LDK seven-confirmation / six-deep boundary

**Proposed name:**
`LnLean.Proofs.WaveH.H45.ldk_seven_confirmation_six_deep`.

**Statement shape:**

```lean
theorem ldk_seven_confirmation_six_deep (h : Height) :
    confirmationCount (h + 6) h = 7 ∧
      reorgSurvives
        { fromHeight := h + 6, depth := 6, newTip := ByteArray.empty }
        (h + 6) h ∧
      ¬ reorgSurvives
        { fromHeight := h + 6, depth := 7, newTip := ByteArray.empty }
        (h + 6) h := by
  -- `confirmationCount (h+6) h = h+6+1-h = 7`; `6 < 7`; `¬ 7 < 7`.
  -- proof obligation (proposal only; not compiled)
```

**Hypotheses:** none beyond `h : Height`. The statement is the arithmetic of
a funding block at height `h` with six blocks on top (seven confirmations).

**Non-vacuity witness:** `h := 0`; all three conjuncts reduce to `decide`.
The existing `deep_boundary_is_sharp` (`ChainFinalityTargets.lean:759-770`)
and `not_survives_at_depth` (`ReorgTargets.lean:106-112`) remain the abstract
boundary; T6 is the LDK-test-shaped instance.

**Why faithful:** the pinned `reorg_test` funds channels, mines seven blocks,
and reorgs at most six blocks (`tests/reorg_test.rs:94`, `:120-123`,
`:155-159`). The theorem states exactly why the funding block survives at
seven confirmations and would be evicted at eight. It does not claim the test
covers the whole protocol, and it does not turn six into a consensus rule.

**Fidelity risk:** low. The only risk is reading the seven/six pair as a
universal LDK finality threshold; the test itself comments that the funding
must stay confirmed across the deepest reorg, not that six is safe in general.

**Feasibility:** high. One arithmetic theorem with `omega`/`decide`.

**Classification:** conformance witness; no new assumption.

### T7 — Stale-view interface (negative)

**Proposed name:**
`LnLean.Proofs.Security.ReorgTargets.stale_view_can_satisfy_safeAt`.

**Statement shape:**

```lean
structure SyncState where
  view : ChainView
  lastSuccess : Option Nat

theorem stale_view_can_satisfy_safeAt :
    ∃ (s : SyncState) (canonical : ChainView)
      (o : Observations) (a : Adversary),
      s.lastSuccess = none ∧ ¬ SameChain s.view canonical ∧
        o.SafeAt s.view a ∧ ¬ o.SafeAt canonical a := by
  -- reuse the `safety_judgement_needs_common_tip` witness:
  -- view height 10 vs canonical height 6, budget 8.
  -- proof obligation (proposal only; not compiled)
```

**Hypotheses:** a `SyncState` with an optional last-success timestamp, and a
canonical view. The theorem asserts existence, not that a particular RPC call
failed.

**Non-vacuity witness:** `settledObservations` with a fact at height zero, a
stale/forked view at height 10, canonical at height 6, and a budget of 8. The
fact has 11 confirmations on the stale view and 7 on canonical; `SafeAt` holds
at 10 and fails at 6. This is exactly `safety_judgement_needs_common_tip`
(`:517-537`) with the sync state made explicit.

**Why faithful:** it records the operational fact from section 2.2: a local
`current_best_block` can lag or sit on an old branch, and the background loop
swallows failures. The theorem is deliberately negative: it shows the model
cannot derive a common tip from "the node is running." The positive liveness
statement ("a healthy node eventually syncs") must remain an external
assumption.

**Fidelity risk:** medium. `lastSuccess : Option Nat` is uninterpreted; the
theorem does not connect it to a real failure or a timeout. That is the
intended boundary, but it must be labelled as an interface, not a failure
model.

**Feasibility:** high. It reuses an existing witness and adds one structure.

**Classification:** model extension plus an explicit external liveness
assumption. Do not encode eventual sync as an axiom.

### T8 — `SameChain` is not block-content equality

**Proposed name:**
`LnLean.Proofs.Security.ChainFinalityTargets.sameChain_view_length_only`.

**Statement shape:**

```lean
theorem sameChain_view_length_only :
    ∃ (c c' : Chain) (tip : ByteArray),
      c.length = c'.length ∧ c.blocks ≠ c'.blocks ∧
        SameChain (c.view tip none) (c'.view tip none) := by
  -- `smallChain` and `otherChain` both have length 3; `smallTx` is absent
  -- from `otherChain`; `sameChain_view_of_length_eq` gives `SameChain`.
  -- proof obligation (proposal only; not compiled)
```

**Hypotheses:** none. The witness uses `smallChain`, `otherChain`
(`ChainFinalityTargets.lean:511-544`), and `chainTipTag` (`:378`).

**Non-vacuity witness:** `smallChain` has blocks `100,101,102`; `otherChain`
has `900,901,902`; both length three; `smallTx_rejected_without_prefix`
(`:638-647`) proves the genesis transaction is absent from `otherChain`.
`sameChain_view_of_length_eq` (`:391-397`) gives `SameChain` for any common
tip tag. The two chains are genuinely different, so this is not a reflexive
case.

**Why faithful:** it is a guard on the existing bridge. `sameChain_view_of_length_eq`
is true for the abstract `ChainView` (height plus opaque tip), but it must not
be used to transfer block content or transaction membership. A semantic bridge
needs `c.blocks = c'.blocks` or `SharesPrefix`, not `SameChain` alone. The
theorem keeps the existing bridge and adds the missing counterexample next to
it.

**Fidelity risk:** low. It does not weaken `sameChain_view_of_length_eq`; it
prevents a future theorem from treating that bridge as more than it is.

**Feasibility:** high. One existential theorem using existing witnesses.

**Classification:** guard theorem; no new assumption.

## 5. Assumptions, counterexamples, and non-vacuity risks

### 5.1 Existing witnesses that must be preserved

| Witness | What it establishes | Do not remove or make vacuous |
|---|---|---|
| `smallTx_not_reorged` (`ChainFinalityTargets.lean:597`) + `smallAlt_ne_smallChain` (`:602`) | A non-reflexive positive survival: a genesis transaction survives a one-block tip replacement. | If `OnChain` is strengthened for T1, keep `smallTx` present in the shared genesis block. |
| `smallTipTx_rejected` (`:624-636`) | A tip transaction is not confirmed at depth two and is absent from the alternative chain. | Keep the height-two witness; do not make every `OnChain` true by default. |
| `smallTx_rejected_without_prefix` (`:638-647`) | Without a common ancestor, the same transaction is absent from an unrelated chain. | This is the negative control for every `SameChain`/prefix bridge. |
| `deep_reorg_evicts` (`:748-757`) | A depth-two transaction is evicted by a depth-three fork. | The depth bound must remain necessary. |
| `deep_boundary_is_sharp` (`:759-770`) | Three confirmations is the exact boundary for depth three. | Keep the off-by-one explicit. |
| `depth_bound_necessary` (`:772-784`) | The negation of the finality conclusion with the depth hypothesis removed. | Do not weaken `hdepth` in the main theorem to make a target easier. |
| `safety_not_unconditional` (`ReorgTargets.lean:464-495`) | `OnchainSafeAt` plus an allowed depth-six reorg can evict a fact. | Do not replace the budget-relative `SafeAt` with a six-confirmation predicate. |
| `deep_reorg_separate_failure_mode` (`:427-450`) and `deep_reorg_not_allowed` (`:452-462`) | Deep reorgs are a separate failure mode, outside the depth-five budget. | Keep the distinction between "evicted" and "not allowed." |
| `common_tip_needed` (`:498-515`) and `safety_judgement_needs_common_tip` (`:517-537`) | `SameChain` and the common tip are load-bearing. | Do not derive them from a `SyncState` flag or an axiom. |
| `outOfReach_not_sufficient_for_budget` (`H45:436-457`) | One reorg's `OutOfReachOf` does not imply whole-budget `SafeAt`. | T3 must strengthen, not contradict, this. |
| `sharp_depth_boundary` (`H45:422-434`) and `channel_reorg_within_antiReorgDelay` (`:507-525`) | The concrete budget/depth boundary and the within-delay instance. | Keep the depth-five vs depth-six distinction. |
| `no_finite_confirmation_depth` (`D02:398-411`) | No finite confirmation count defeats an unbounded reorg. | Do not claim probabilistic finality from a finite depth. |

### 5.2 Concrete counterexamples to keep visible

1. **Arbitrary txid.** By `OnChain`'s definition (`ChainFinalityTargets.lean:304-305`),
   `{ txid := 999, blockHash := 100, height := 0 }` is on `smallChain` even
   though `smallChain` has no transaction list. This is the strongest single
   argument that the current theorem is block identity, not transaction
   inclusion.
2. **Equal-length unrelated chains.** `smallChain` and `otherChain` both have
   length three, but `smallTx` is absent from `otherChain`
   (`:638-647`). `sameChain_view_of_length_eq` (`:391-397`) still makes their
   views `SameChain` under one tag. This is the counterexample that T8
   mechanizes.
3. **Shorter heavier chain.** A length-three chain with per-block work 1 has
   total work 3; a length-two chain with per-block work 10 has total work 20.
   `UniqueCanonicalTip` selects the former; `mostWork?` selects the latter.
   This is the counterexample behind T4.
4. **Stale view.** At view height 10 a height-zero fact has 11 confirmations;
   at canonical height 6 it has 7. A budget of 8 is safe at the first and
   unsafe at the second (`safety_judgement_needs_common_tip`). The stale view
   can be the one a node keeps after a failed sync or a shorter/heavier reorg.
5. **Seven vs six.** A funding block at height `h` with tip `h + 6` has seven
   confirmations; a depth-six reorg retains it, a depth-seven reorg does not
   (T6). This matches the pinned `reorg_test` but is not a universal rule.
6. **Confirmed to unconfirmed.** A one-block reorg returns an on-chain payment
   from `Confirmed` to `Unconfirmed`
   (`integration_tests_rust.rs:2137-2198`). The Lean `applyReorgAt` only
   filters facts; it has no status transition.

### 5.3 Proposals that would weaken or hide an assumption

* **T1 must strengthen, not weaken, `OnChain`.** If `Block.txids` is added with
  a default `[]`, every existing witness becomes false unless the witness
  blocks are updated. Do not define `OnChain` as `True`, as block-hash only,
  or as "some block at this height"; that would preserve the current gap under
  a new name.
* **T1 must not claim Merkle inclusion.** A `txids : List Nat` field is a
  membership table, not a commitment. If the implementation wants a consensus
  claim, it needs a Merkle root and a proof, which is a much larger external
  target.
* **T4 must not replace `UniqueCanonicalTip` silently.** Keep the existing
  predicate and `unique_tip_finality`; add `UniqueCanonicalTipByWork` and prove
  the two can disagree. Do not call abstract `w` a difficulty model.
* **T5 must not hard-code six for every fact.** If a `requiredDepth` field is
  added, default it to `antiReorgDelay` and prove the old theorem as the
  special case. Do not change `antiReorgDelay = 6` or the existing boundary
  witnesses.
* **T7 must not become an axiom.** `lastSuccess` is an interface, not a
  liveness proof. Do not add `EventualSync : Prop` as an axiom or a `True`
  field.
* **T8 must not weaken `sameChain_view_of_length_eq`.** It is a useful
  height/tip bridge; the guard theorem only prevents its misuse as a
  block-content bridge.
* **Do not delete the negatives.** `smallTx_rejected_without_prefix`,
  `deep_reorg_evicts`, `depth_bound_necessary`, `safety_not_unconditional`,
  `common_tip_needed`, and `outOfReach_not_sufficient_for_budget` are the
  non-vacuity and boundary controls. A target that needs them removed is not a
  repair.

### 5.4 External assumptions (not Lean theorems)

* **A1 — Common tip / eventual sync.** Two nodes can be assumed to converge to
  the same view only under an explicit liveness and source-honesty assumption.
  The pinned background loop can swallow failures (`chain/mod.rs:528-534`), so
  this is not derivable from the code.
* **A2 — Chain-source honesty and availability.** Bitcoind, Electrum, and
  Esplora are not equivalent trust anchors (`ldk-server/docs/configuration.md:174-188`).
  The model has no source field.
* **A3 — PoW / probabilistic finality.** No hashrate, difficulty, or economic
  finality is modelled. `L1-06` remains open at P2 (`docs/OPEN-ISSUES.md:52`).
* **A4 — Transaction validity and Merkle inclusion.** `txid` membership is not
  script validity, input availability, or a Merkle proof.
* **A5 — LDK threshold policy.** The per-fact required depths are operational
  constants, not proved consensus rules.
* **A6 — Consensus tie-break.** `betterThan`/`mostWork?` exist in the vendor
  tree, but the finality layer does not import them; the exact sequence
  tie-break remains outside the model.

## 6. Wave-13 recommendation

**No P0 proof hole was found.** `LN-L1-003` is a sound conditional result; the
existing theorems are non-vacuous and the negatives are sharp. The issue is
fidelity of names and missing interfaces, not an inconsistency.

**Do not open a new P0/P1 proof wave.** This is consistent with the wave-12
audit's "No new tractable P0/P1 proof lane was found"
(`agents/reports/swarm12/S12-POST-INTEGRATION-AUDIT.md:53-55`). `L1-06` should
remain open at P2; T1–T8 do not close it. The P1 labels on T1, T4, and T8 are
*fidelity* priorities, not a claim that a new P0/P1 proof obligation exists;
the proposed lane is P2-scoped in the wave process sense.

**If a narrow wave-13/14 lane is authorized, scope it as follows:**

1. **Implement T1 (transaction-membership finality) and T8 (the `SameChain`
   guard) first.** These are the two changes that make the headline nouns
   honest without pretending to model consensus. T1 is P1 fidelity, but it is
   a local schema/definition repair, not a new P0/P1 proof lane.
2. **Add T2, T3, and T6 as low-risk P2 bridges/conformance witnesses.** They
   are short, reuse existing witnesses, and make lagging views, per-reorg vs
   budget, and the LDK seven/six boundary explicit.
3. **Defer T4 and T5.** Both require new predicates/policy records and touch
   the meaning of the canonical tip or confirmation threshold. They need a
   maintainer decision on whether chainwork and per-fact policy are in scope.
4. **Treat T7 as an interface, not a proof of liveness.** If it is added, label
   A1/A2 as external and do not encode eventual sync as an axiom.
5. **Keep A1–A6 external.** PoW/probabilistic finality, chain-source trust,
   transaction validity, and the real LDK threshold policy are not tractable
   finite-model lemmas.

**Acceptance criteria for the narrow lane:**

* No new `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, or
  `@[implemented_by]`.
* `#print axioms` for the existing `LN-L1-003` targets is unchanged.
* `smallTx_not_reorged`, `smallTipTx_rejected`,
  `smallTx_rejected_without_prefix`, `deep_reorg_evicts`,
  `deep_boundary_is_sharp`, `depth_bound_necessary`,
  `safety_not_unconditional`, `common_tip_needed`,
  `outOfReach_not_sufficient_for_budget`, and
  `no_finite_confirmation_depth` still compile and remain non-vacuous.
* T1's `OnChain` requires `t.txid ∈ b.txids`; a `txid := 999` witness is no
  longer accepted.
* T8's counterexample is next to `sameChain_view_of_length_eq` and no theorem
  uses `SameChain` to claim block or transaction equality.
* `antiReorgDelay = 6` and the `not_survives_at_depth` boundary are unchanged.

## 7. Evidence and commands

### 7.1 Repository state

```text
$ git -C /home/ubuntu/ln-lean-repair rev-parse --abbrev-ref HEAD
repair/integrated
$ git -C /home/ubuntu/ln-lean-repair status --porcelain=v1
?? .opencode/
?? agents/briefs/wave13-review/
?? agents/reports/wave13-review/
?? agents/status/REPAIR.status
?? agents/status/wave13-review.status
?? agents/swarm/WAVE-13-REVIEW.json
?? agents/swarm/WAVE-13-REVIEW.md
?? scripts/gen-review-wave-13.py
?? scripts/launch-review-wave-13.sh
```

No tracked file was modified. The only untracked review infrastructure was
already present; this report is the only file written by this lane.

### 7.2 Pinned reference heads

```text
$ git -C /tmp/opencode/ldk-refs/ldk-node rev-parse HEAD
fa123fed131e27ecc420b77fa7086fcf1ddaebb8
$ git -C /tmp/opencode/ldk-refs/ldk-server rev-parse HEAD
c17dc11dde38f88c53457039ddf30c6b90a63ba2
```

These match the lane pin table in
`agents/reports/wave13-review/LDK-REFS.md`.

### 7.3 Read-only checks performed

* `rg -n "^(theorem|lemma|def|structure|inductive|abbrev|instance) "` over
  `ChainFinalityTargets.lean`, `ReorgTargets.lean`, `WaveH/H45.lean`, and
  `WaveD/D02.lean` to map the declaration surface.
* `rg -n "\\bsorry\\b|\\badmit\\b|^axiom |^axioms "` over the same four
  modules; no matches.
* `rg -n "txid"` over `ChainFinalityTargets.lean`; only the structure field and
  the three witness literals, no proof use.
* `rg -n` over the pinned LDK Node/Server trees for `ANTI_REORG_DELAY`,
  `ConfirmationStatus`, `ChainSourceKind`, `current_best_block`,
  `update_fee_rate_estimates`, `ChainTip::Better`, `reorg`, `ValidFork`,
  `Active`, and the chain-source configuration.
* `git diff --stat` and `git status --porcelain=v1` in the review worktree.
* No `lake build`, no `cargo test`, and no network fetch were run. The report
  is source- and declaration-grounded, not a fresh kernel build.

### 7.4 Primary references

| Claim | Lean reference | LDK reference |
|---|---|---|
| Confirmation arithmetic | `ChainFinalityTargets.lean:90-100`; `ReorgTargets.lean:89-95`; `D02:96-120` | `wallet/mod.rs:556-558`, `:683-710`; `payment/store.rs:527-530` |
| Transaction membership | `ChainFinalityTargets.lean:63-67`, `:294-305`, `:331-338` | `payment/store.rs:524-536`, `:685-696`; `integration_tests_rust.rs:2137-2198` |
| Reorg depth/fork | `ChainFinalityTargets.lean:104-120`, `:256-288`; `Model.lean:72-76` | `tests/reorg_test.rs:21-73`, `:94`, `:120-123`, `:155-159` |
| Common tip/`SameChain` | `ReorgTargets.lean:120-121`, `:191-194`, `:299-315`; `ChainFinalityTargets.lean:381-397` | `lib.rs:2614-2625`; `chain/mod.rs:528-534` |
| Unique tip/chainwork | `ChainFinalityTargets.lean:342-345`; `vendor/.../Block/Index.lean:50`, `:70`, `:96-109`, `:125` | `bitcoind.rs:506-511` |
| Confirmed/unconfirmed | `ReorgTargets.lean:221-234`; `ChainFinalityTargets.lean:294-305` | `payment/store.rs:685-696`; `wallet/mod.rs:775-790`; `integration_tests_rust.rs:2137-2198` |
| Thresholds | `ReorgTargets.lean:84`, `:162-177` | `payment/store.rs:527-530`; `balance.rs:131-145`, `:341-355`; `wallet/mod.rs:1127` |
| Chain source/trust | `Model.lean:114-118` (opaque tip) | `ldk-server/docs/configuration.md:174-188`; `ldk-server/src/main.rs:176-221`; `chain/mod.rs:156-170`, `:364-372` |
| Source failure/liveness | (no Lean state) | `chain/mod.rs:528-534`; `lib.rs:2213-2221`; `config.rs:28-30`, `:590-592` |
| Existing boundary witnesses | `ChainFinalityTargets.lean:597-647`, `:748-784`; `ReorgTargets.lean:427-537`; `H45:422-457`, `:507-525`; `D02:398-411` | `tests/reorg_test.rs:94`, `:155-159` |

### 7.5 Review boundary

This report does not claim that the finite graph is a Bitcoin consensus model.
It does not claim that `ConfirmedTx.OnChain` is transaction inclusion, that
`UniqueCanonicalTip` is chainwork, that `SameChain` is block-content equality,
or that `applyReorgAt` is ledger rollback. Those are precisely the gaps the
targets and external assumptions are meant to keep visible.
