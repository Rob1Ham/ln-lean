# R02 — L1 transaction construction, sighash, PSBT, fees, and weight
**Status:** read-only review
**Pins:** LDK Node `fa123fed131e27ecc420b77fa7086fcf1ddaebb8`, LDK Server `c17dc11dde38f88c53457039ddf30c6b90a63ba2`
**Review branch:** `repair/integrated` at `f7f0628` (no branch, commit, or non-report file changes made)

## 1. Scope and current Lean surface

This lane covers the L1 transaction-construction boundary around a channel:
funding-transaction construction and change, BIP 143 witness-v0 sighash,
PSBT use, wallet coin selection, on-chain send/drain and anchor reserve,
fee estimation, RBF/CPFP fee bumping, package broadcast ordering, and the
commitment fee/weight/dust model.  It does **not** re-review the channel
lifecycle, script execution, ECDSA attribution, routing, or the HTLC state
machine except where they constrain the fee/weight claims.

### 1.1 Catalog rows that actually touch this surface

| Row | Catalog claim | Existing Lean target | What is really covered |
|---|---|---|---|
| `LN-L1-006` | Commitment base weight is BOLT 3's fee-basis `724` / `1124`, plus `172` per untrimmed HTLC, with the anchor serialization gap explicit (`docs/THEOREM-INDEX.md:42`, `docs/TRACEABILITY.md:21`) | `LnLean.Proofs.Bitcoin.commitmentBaseWeight_model_target` (`LnLean/Proofs/Bitcoin/WeightTargets.lean:312-326`) | Exact BOLT 3 fee-basis constants and per-HTLC increment; exact non-anchor serialization; the anchor serialization is `1116 + 172*k`, eight WU below the fee basis. |
| `LN-CH-003` | BOLT 3 output ordering and trimming (`docs/THEOREM-INDEX.md:51`, `docs/TRACEABILITY.md:30`) | `LnLean.Channel.Commitment.output_ordering` (`LnLean/Proofs/Channel/CommitmentOrderTargets.lean:89-106`) | Rich `CommitmentTx` model: permutation of the trimmed list, value/script/CLTV ordering, dust exclusion, anchor exemption.  The legacy `commitmentOutputs` function remains refuted by D12. |
| `LN-CH-005` | A commitment is rejected before signing exactly when its fee is insufficient (`docs/THEOREM-INDEX.md:53`, `docs/TRACEABILITY.md:32`) | `LnLean.Channel.Fee.commitmentSigningGate_rejected_iff_insufficient` (`LnLean/Proofs/Channel/FeeTargets.lean:225-238`) | Exact iff between the local pre-signature gate and the BOLT 3 base-fee predicate; the gate is a policy precondition, not relay/mempool simulation. |

Adjacent covered pieces used by this lane:

* **BIP 143 digest construction is exact.**  `LnLean/Bitcoin/Sighash.lean`
  defines the ten consensus fields, serializers, `ofTx`, `digest`, and the
  out-of-range guard (`:34-39`, `:350-391`), and proves byte equality to the
  vendored encoder (`:478-500`).  The scope note is explicit: the spent
  outpoint/amount and transaction validity are context hypotheses, not derived
  (`:48-61`); the C1/C3 cryptographic assumptions are not used here.
* **Funding output construction is covered only as an output.**  The model
  fixes P2WSH over the ordered 2-of-2 witness script and the funding value
  (`LnLean/Bitcoin/Funding.lean:10-17`, `LnLean/Bitcoin/Seam.lean:103-120`).
  It explicitly excludes funding-transaction construction, fee payment, and
  RBF (`LnLean/Bitcoin/Funding.lean:32-40`; also
  `LnLean/Proofs/Bitcoin/FundingProps.lean:71-79`).
* **Commitment fee/weight/dust is a model-level surface.**  `feeForWeight`
  is the floor-divided BOLT 3 fee (`LnLean/Channel/Fee.lean:49-56`);
  `feeSufficient` is a comparison against it (`:89-95`); `isDust` is the
  strict negotiated-dust comparison (`:141-150`).  Weight is
  `724`/`1124 + 172*k` (`LnLean/Channel/Commitment.lean:55-73`), with the
  fee computed from the record's own weight (`:322-331`).  The module excludes
  Core dust-relay policy, fee estimation, RBF, and anchor CPFP (`:31-38`).
* **Anchor value/count and HTLC second-stage weights are covered for the
  modelled template.**  `anchorValue = 330` (`LnLean/Bitcoin/Seam.lean:124-127`);
  both anchors in the zero-HTLC template and the 660-sat total are proved
  (`LnLean/Proofs/Bitcoin/AnchorProps.lean:148-189`); HTLC-timeout/success
  weights `663`/`703` and zero second-stage fees under anchors are proved
  (`LnLean/Proofs/Channel/CommitmentIntegrationTargets.lean:106-136`).  The
  single-anchor dust exception, `shared_anchor`, P2A, and CPFP economics are
  explicitly out of scope (`AnchorProps.lean:62-77`;
  `CommitmentIntegrationTargets.lean:75-94`).

### 1.2 Namespace status

There is **no** `LnLean.Proofs.Bitcoin.TxConstruction` namespace and no Lean
definition of a wallet UTXO, coin selection, funding transaction plan, PSBT,
change output, anchor reserve, fee estimator, RBF replacement, CPFP package, or
package ordering.  `rg` over `LnLean/` returns only exclusion notes (listed in
§7).  Any target below is therefore a new additive model extension, not a
restatement of an existing theorem.

## 2. LDK datapoints (with `file:line`)

Paths are relative to the pinned clones.  These are external datapoints, not
proof dependencies.

### 2.1 Funding transaction, PSBT, and change

* `ldk-node/src/event.rs:806-836` handles `FundingGenerationReady`, sets
  `nLockTime` to the current height to discourage fee sniping (`:817-819`),
  and calls `create_funding_transaction`.
* `ldk-node/src/wallet/mod.rs:1704-1752` builds a BDK `TxBuilder` with the
  funding recipient, `fee_rate`, and `nlocktime`; finishes a PSBT; signs it;
  persists the change set; and extracts the final transaction.  The PSBT is an
  internal BDK object and is not returned.
* `ldk-node/src/wallet/mod.rs:1747-1752` is the only public result: the
  extracted transaction.  There is no public PSBT handoff in this path.

### 2.2 On-chain send, drain, and anchor reserve

* `ldk-node/src/payment/onchain.rs:75-84` sends an exact amount while
  respecting the anchor reserve; `:101-118` sends all funds either retaining or
  draining reserves; `:134-149` exposes RBF bumping.
* `ldk-node/src/wallet/mod.rs:1994-2000` computes spendable balance as
  `trusted_spendable - total_anchor_channels_reserve_sats` with saturating
  subtraction.
* `ldk-node/src/wallet/mod.rs:2011-2030` builds a drain PSBT and adds a
  reserve output **only** when `cur_anchor_reserve_sats > DUST_LIMIT_SATS`
  (`:2016-2020`).
* `ldk-node/src/wallet/mod.rs:2193-2225` applies the same guard to
  `AllRetainingReserve`; when the reserve is at or below the constant it falls
  through to `AllDrainingReserve` and drains all funds (`:2220-2224`).
* `ldk-node/src/wallet/mod.rs:99` defines `DUST_LIMIT_SATS = 546`; it is used
  at `:2016`, `:2100`, and `:2194` as an LDK wallet/drain/reserve threshold,
  not as the negotiated channel `dust_limit_satoshis`.
* `ldk-node/src/lib.rs:2717-2734` computes the total reserve as the number of
  untrusted, still-open anchor channels times `per_channel_reserve_sats`;
  `:2736-2748` returns zero for non-anchor channels or trusted peers.
* `ldk-node/src/config.rs:38` sets the default per-channel reserve to `25,000`
  sats; `:449-455` and `:490-513` document/return that default and the
  `trusted_peers_no_reserve` exception.

### 2.3 Coin selection and change

* `ldk-node/src/wallet/mod.rs:2350-2434` (`select_confirmed_utxos`) builds a
  BDK transaction with foreign `must_spend` inputs, adds `must_pay_to`
  recipients, applies `fee_rate`, calls `exclude_unconfirmed`, and rejects more
  than one change output (`:2406-2413`).  It returns selected confirmed UTXOs
  and at most one change output.  This is a relational selection result, not a
  documented selection algorithm.

### 2.4 Fee estimation

* `ldk-node/src/fee_estimator.rs:61-75` returns the cached estimate for a
  confirmation target, falling back to a per-target constant and enforcing
  `FEERATE_FLOOR_SATS_PER_KW`.
* `:87-102` gives confirmation targets (6 blocks for on-chain payment, 12 for
  channel funding, and LDK-specific targets).
* `:104-123` gives fallback rates (`5,000` sat/kwu on-chain, `1,000` sat/kwu
  funding, and LDK-specific values).
* `:168-188` caps funding/splice fee bumps at `1.5x` the funding estimate and
  chooses `max(current estimate, RBF minimum)` as the target, returning
  `none` when the minimum exceeds the cap.

### 2.5 RBF

* `ldk-node/src/wallet/mod.rs:3371-3425` accepts an RBF request only for an
  unconfirmed outbound on-chain payment, and refuses transactions owned by a
  channel or spending non-wallet inputs (`:3425-3480`).
* `:3502-3514` computes the minimum replacement rate as
  `old_fee_rate.to_sat_per_kwu() + INCREMENTAL_RELAY_FEE_SAT_PER_1000_WEIGHT`
  and takes the maximum with the current estimate.
* `:3550-3577` retries BDK at a higher required rate but caps that retry at
  `1.5x` the target (`:3554-3560`).
* `:3586-3619` rejects the bump when the additional fee would cut into the
  anchor reserve.

### 2.6 CPFP, anchor bumps, and package broadcast

* `ldk-node/src/event.rs:2384-2408` routes `BumpTransactionEvent` to the LDK
  bump handler; `ChannelClose` is skipped for trusted peers (`:2391-2403`),
  while `HTLCResolution` is always handled (`:2405`).  The actual CPFP
  transaction construction lives in the upstream `lightning` dependency, not in
  this repository.
* `ldk-node/src/tx_broadcaster.rs:20-35` defines a broadcast package as the
  transactions from one `broadcast_transactions` call (or one wallet
  transaction); `:78-103` sorts parents before a child by
  `any_spends_from_package`, with debug assertions that all package parents are
  spent by the child and there are no grandparents (`:97-100`).
* `ldk-node/src/chain/mod.rs:669-672` passes the sorted package to the chain
  source "parents before their child so a CPFP package a chain source submits
  one transaction at a time is still accepted."
* Bitcoind submits the package through `submitpackage`
  (`ldk-node/src/chain/bitcoind.rs:932-961`); Esplora's package path is gated
  on all transactions being v3 (`ldk-node/src/chain/esplora.rs:473-485`).

### 2.7 Server RPC surface

* `ldk-server/ldk-server/src/api/onchain_send.rs:22-45` validates an address
  and fee rate, then calls `send_to_address` or `send_all_to_address`.
* `ldk-server/ldk-server/src/api/onchain_bump_fee.rs:18-24` parses a payment id
  and fee rate, then calls `bump_fee_rbf`.
* `ldk-server/ldk-server/src/api/onchain_receive.rs:17-23` returns a fresh
  address only.  There is no PSBT construction, signing, or inspection RPC in
  these on-chain endpoints.

## 3. Gap matrix

Status vocabulary: **covered faithfully**, **partially covered**, **missing**,
**contradicted**, **unmodelled/external**.  "Covered" below always means the
named Lean theorem actually proves the stated behavior, not that a
similarly-named theorem exists.

| Behavior | Lean status | LDK evidence | Gap / counterexample | Priority |
|---|---|---|---|---|
| BIP 143 witness-v0 preimage/digest for a known transaction | **Covered faithfully** (construction only) | `wallet/mod.rs:1704-1752` builds and signs a real funding tx; the digest model is independent of wallet | Exact bytes and vendor equality (`Sighash.lean:350-500`), but spent amount/outpoint and tx validity are hypotheses (`:48-61`); no concrete ECDSA/UTXO context. | P1 context |
| Funding output script and 330-sat anchor value | **Covered faithfully** (output/template) | `event.rs:825-836`; `Seam.lean:103-127` | No funding *transaction*; only the output and value are modelled. | P1 |
| Funding transaction construction, change, and PSBT | **Missing / unmodelled** | `wallet/mod.rs:1704-1752` (PSBT, sign, extract), `:1747-1752` | No `FundingPlan`, change output, wallet input list, PSBT, or fee partition in Lean.  PSBT is an internal BDK artifact with no public RPC (`onchain_receive.rs:17-23`). | P1 |
| Confirmed-UTXO coin selection and at-most-one change | **Missing** | `wallet/mod.rs:2350-2434` (`exclude_unconfirmed`, foreign inputs, one change) | No UTXO set, confirmation predicate, selection relation, or change-count theorem.  The model's `FundingParams.WellFormed` says nothing about the wallet. | P1/P2 |
| On-chain send/drain and anchor reserve | **Missing** | `wallet/mod.rs:1994-2000`, `:2011-2030`, `:2193-2225`; `lib.rs:2717-2748`; `config.rs:38`, `:449-455` | No reserve arithmetic.  A naive "always retain reserve" claim is **contradicted** by `:2194` when `reserve <= 546`; the code drains all. | P1 |
| Fee estimator, fallback, and floor | **Unmodelled/external** | `fee_estimator.rs:61-75`, `:87-123` | The Lean feerate is an input (`Fee.lean:34-35`); no cache, target, fallback, or floor semantics.  This is chain-policy input, not a protocol theorem. | P2 |
| Commitment base fee and pre-signature gate | **Covered faithfully** | `wallet/mod.rs:3502-3514` is RBF, not the commitment gate; Lean gate is `FeeTargets.lean:202-238` | Exact iff for the model's base fee and own weight; no relay/mempool claim (`FeeTargets.lean:40-52`). | P1 |
| Commitment weight `724`/`1124 + 172*k` as BOLT 3 fee basis | **Covered faithfully** (fee basis) | `wallet/mod.rs` uses BDK weights, not these constants; Lean is BOLT 3 | `1124` is a negotiated fee basis, not literal serialization: `1116 + 172*k` (`WeightTargets.lean:337-355`; `H33.lean:457-522`). | P1 |
| Actual anchor serialization weight | **Partially covered** | no single LDK constant; BDK computes weight | Exact `1116 + 172*k` and the 8 WU gap are proved, but witness-signature length is still an assumed `224` component (`WeightTargets.lean:46-81`). | P2 |
| Commitment output ordering and dust trimming | **Covered faithfully** in `CommitmentTx`; **contradicted** for legacy `commitmentOutputs` | `wallet/mod.rs` does not construct commitment outputs | `CommitmentOrderTargets.lean:89-106` proves the rich model.  D12's `unconditional_ordering_refuted` (`:63-69`) and `cltv_tiebreak_not_recoverable` (`:71-77`) must remain. | P1 |
| Anchor outputs: value, count, fee treatment | **Covered faithfully** for the zero-HTLC two-anchor template; **partially covered** for edge cases | `wallet/mod.rs:2016-2020` uses anchors; actual anchor spend is upstream | `AnchorProps.lean:62-77` explicitly excludes the single-anchor dust exception, `shared_anchor`/P2A, and CPFP economics. | P2 |
| RBF replacement | **Missing / external policy** | `wallet/mod.rs:3371-3425`, `:3502-3514`, `:3550-3577`, `:3586-3619` | No RBF model.  The local arithmetic (`old + incremental`, 1.5x cap, reserve check) can be modelled; BIP125 absolute-fee/conflict/descendant policy is external. | P2 |
| CPFP and anchor bump | **Missing / external** | `event.rs:2384-2408`; upstream `lightning` bump handler | No parent/child package, package feerate, or anchor-spend model.  Trusted-peer skip and HTLC-resolution routing are local behavior. | P2 |
| Package broadcast ordering | **Missing** | `tx_broadcaster.rs:20-35`, `:78-103`; `chain/mod.rs:669-672` | No package type, parent-before-child relation, or `submitpackage` model.  The Rust debug assertions are not a theorem. | P2 |
| Wallet dust `546` vs negotiated channel dust | **Missing; contradicted if identified** | `wallet/mod.rs:99`, `:2016`, `:2100`, `:2194`; channel dust is `ChannelParams.dustLimitSat` | Lean only has `isDust dustLimitSat` (`Fee.lean:141-150`).  `546` is an LDK drain/reserve threshold, not the channel dust limit.  Witness: 400 sats is dust at 546 and non-dust at 354. | P2 |
| Server on-chain RPCs / PSBT exposure | **Unmodelled/external** | `onchain_send.rs:22-45`, `onchain_bump_fee.rs:18-24`, `onchain_receive.rs:17-23` | Thin wrappers around node/wallet calls; no PSBT RPC.  Server behavior is an API surface, not a Lean target. | External |

## 4. Proposed targets

All targets are **additive** and belong in a new module
`LnLean/Proofs/Bitcoin/TxConstructionTargets.lean` under
`LnLean.Proofs.Bitcoin.TxConstruction`.  They must not replace or weaken the
existing `FundingParams.WellFormed`, `commitmentBaseWeight`,
`Fee.commitmentSigningGate`, `isDust`, or `CommitmentTx` APIs.  Statement
shapes below are specifications for a later lane; they are not claimed to
compile as written.

### 4.1 P1 — `fundingTx_value_partition`

**Fully-qualified name:**
`LnLean.Proofs.Bitcoin.TxConstruction.fundingTx_value_partition`

**Statement shape:**
```lean
structure WalletUtxo where
  outpoint : OutPoint
  valueSat : Nat
  confirmed : Bool

structure FundingPlan where
  inputs : List WalletUtxo
  fundingSat : Nat
  changeSat : Nat
  feeSat : Nat
  fundingScript : Script
  changeScript? : Option Script

def FundingPlan.totalInput (p : FundingPlan) : Nat :=
  (p.inputs.map (fun u => u.valueSat)).sum

def FundingPlan.WellFormed (p : FundingPlan) : Prop :=
  (∀ u ∈ p.inputs, u.confirmed = true) ∧
  (p.inputs.map (fun u => u.outpoint)).Pairwise (fun a b => a ≠ b) ∧
  p.totalInput = p.fundingSat + p.changeSat + p.feeSat ∧
  p.fundingSat ≤ Bitcoin.Data.MAX_MONEY ∧
  p.changeSat ≤ Bitcoin.Data.MAX_MONEY ∧
  (p.changeScript?.isSome ↔ 0 < p.changeSat)

theorem fundingTx_value_partition
    (p : FundingPlan) (r : FeeRate) (w : Weight) (h : p.WellFormed)
    (hfee : r.msatPerKw * w.val ≤ p.feeSat * 1000) :
    p.totalInput = p.fundingSat + p.changeSat + p.feeSat ∧
    p.fundingSat + p.feeSat ≤ p.totalInput ∧
    p.changeSat = p.totalInput - p.fundingSat - p.feeSat ∧
    (p.changeSat = 0 → p.totalInput = p.fundingSat + p.feeSat) ∧
    Fee.feeSufficient r w ⟨p.feeSat * 1000⟩
```

**Hypotheses:** all selected inputs are marked confirmed; input outpoints are
pairwise distinct; the funding, change, and fee values exactly partition the
input total; values are in `MoneyRange`; a change script is present exactly when
change is positive; the declared fee covers the declared weight at the
declared rate.

**Non-vacuity witness:** one confirmed 100,000-sat input, `fundingSat = 60,000`,
`changeSat = 39,000`, `feeSat = 1,000`; `feeSufficient` holds at
`r = ⟨1000⟩`, `w = ⟨1000⟩`.  A second witness has `changeSat = 0` and a
`none` change script.

**Why it is faithful:** LDK's actual path adds one funding recipient, lets BDK
choose wallet inputs/change, signs the PSBT, and extracts the transaction
(`wallet/mod.rs:1712-1752`).  Any extracted Bitcoin transaction must satisfy the
value partition; this target makes that accounting and the confirmed-input
premise explicit.  It intentionally does **not** claim BDK's selection,
signature validity, fee estimation, or PSBT semantics.

**Priority:** P1.  **Fidelity risk:** medium (abstracts scripts and weights;
`confirmed` is a model flag).  **Feasibility:** high (list/arithmetic lemmas
only).  **Type:** model extension, not an external assumption.

**Weakening check:** do not fold this predicate into
`FundingParams.WellFormed`; the existing `fundingOutput_moneyRange` and
`fee_not_bounded_by_funding_wellformedness` remain unchanged.  In particular,
this target must not be used to claim that a well-formed funding value bounds
the fee; `WeightProps.lean:370-382` is the retained counterexample.

### 4.2 P2 — `selectConfirmedUtxos_sound`

**Fully-qualified name:**
`LnLean.Proofs.Bitcoin.TxConstruction.selectConfirmedUtxos_sound`

**Statement shape:** define a minimal, explicitly *non-BDK* selector:
```lean
def selectConfirmed : Nat → List WalletUtxo → Option (List WalletUtxo)

theorem selectConfirmedUtxos_sound
    (target : Nat) (utxos : List WalletUtxo) {sel : List WalletUtxo}
    (h : selectConfirmed target utxos = some sel) :
    (∀ u ∈ sel, u.confirmed = true) ∧
    (∀ u ∈ sel, u ∈ utxos) ∧
    (∀ u ∈ sel, ∀ v ∈ sel, u.outpoint = v.outpoint → u = v) ∧
    target ≤ (sel.map (fun u => u.valueSat)).sum
```
A companion completeness statement:
```lean
theorem selectConfirmed_complete
    (target : Nat) (utxos : List WalletUtxo)
    (h : target ≤ ((utxos.filter (fun u => u.confirmed)).map (fun u => u.valueSat)).sum) :
    ∃ sel, selectConfirmed target utxos = some sel
```

**Hypotheses:** target is the funding amount plus the required fee; the
selector only considers `confirmed = true` entries; input list is finite.

**Non-vacuity witness:** `utxos = [confirmed 60,000; unconfirmed 100,000]`,
target `50,000`; the selector returns the 60,000-sat UTXO and never the
unconfirmed one.  A second witness has exactly enough confirmed value and
returns `some`; a third has insufficient confirmed value and returns `none`.

**Why it is faithful:** LDK's `select_confirmed_utxos` calls
`exclude_unconfirmed` and returns only confirmed wallet UTXOs
(`wallet/mod.rs:2350-2434`).  The target models that necessary condition and
the at-most-one-change discipline, but **not** BDK's branch-and-bound
algorithm.  It is a soundness theorem for a simplified selector, not an
equivalence claim.

**Priority:** P2.  **Fidelity risk:** high if read as a BDK refinement; low if
kept as a confirmed-only soundness lemma.  **Feasibility:** medium (induction
over the UTXO list).  **Type:** model extension; BDK selection remains
external.

**Weakening check:** do not state that the selector is complete for arbitrary
UTXOs; the `confirmed` filter is load-bearing.  The `none` case must remain a
witness, not be hidden by a totalization that invents value.

### 4.3 P1 — `drain_retains_anchor_reserve`

**Fully-qualified name:**
`LnLean.Proofs.Bitcoin.TxConstruction.drain_retains_anchor_reserve`

**Statement shape:**
```lean
structure DrainPlan where
  inputSat : Nat
  feeSat : Nat
  drainSat : Nat
  reserveSat : Nat
  walletDustLimit : Nat

def DrainPlan.reserveOutput (p : DrainPlan) : Nat :=
  if p.walletDustLimit < p.reserveSat then p.reserveSat else 0

def DrainPlan.WellFormed (p : DrainPlan) : Prop :=
  p.inputSat = p.drainSat + p.feeSat + p.reserveOutput

theorem drain_retains_anchor_reserve
    (p : DrainPlan) (h : p.WellFormed)
    (hres : p.walletDustLimit < p.reserveSat) :
    p.inputSat = p.drainSat + p.feeSat + p.reserveSat ∧
    p.reserveSat > 0 ∧
    p.drainSat ≤ p.inputSat

theorem drain_drops_subdust_reserve
    (p : DrainPlan) (h : p.WellFormed)
    (hres : p.reserveSat ≤ p.walletDustLimit) :
    p.inputSat = p.drainSat + p.feeSat
```

**Hypotheses:** `walletDustLimit` is the LDK policy constant `546`; the reserve
is the per-channel total from `total_anchor_channels_reserve_sats`; the plan is
for the `AllRetainingReserve` branch.

**Non-vacuity witness:** `inputSat = 100,000`, `feeSat = 1,000`,
`reserveSat = 25,000`, `walletDustLimit = 546`, `drainSat = 74,000`; the
reserve output is present.  Counterexample witness for the second theorem:
`reserveSat = 546`, `drainSat = 99,000`; LDK falls through to full drain and
does **not** retain the reserve.

**Why it is faithful:** `get_balances_inner` subtracts the reserve
(`wallet/mod.rs:1994-2000`), and `build_drain_psbt`/`send_to_address` add the
reserve output only when `reserve > 546` (`:2011-2030`, `:2193-2225`).  The
second theorem is the essential counterexample to an unconditional
"retain the reserve" claim.

**Priority:** P1.  **Fidelity risk:** medium (local branch only; BDK fee and
UTXO selection abstracted).  **Feasibility:** high.  **Type:** model extension;
the `546` policy constant is an LDK datapoint, not a consensus theorem.

**Weakening check:** do not state `reserveSat > 0 → reserve is retained`; the
subdust case refutes it.  Do not conflate `walletDustLimit` with the channel's
negotiated dust limit.

### 4.4 P2 — `walletDust_ne_channelDust`

**Fully-qualified name:**
`LnLean.Proofs.Bitcoin.TxConstruction.walletDust_ne_channelDust`

**Statement shape:**
```lean
def walletDustLimit : Nat := 546

theorem walletDust_ne_channelDust :
    walletDustLimit = 546 ∧
    ∃ channelDust : Nat,
      channelDust ≠ walletDustLimit ∧
      LnLean.Channel.Fee.isDust walletDustLimit 400 ∧
      ¬ LnLean.Channel.Fee.isDust channelDust 400
```

**Hypotheses:** none beyond the concrete `isDust` definition
(`Fee.lean:141-150`); the witness chooses `channelDust = 354`.

**Non-vacuity witness:** `400 < 546` is true, while `400 < 354` is false.
`decide` closes the theorem.

**Why it is faithful:** LDK Node uses `546` only as a wallet drain/reserve
threshold (`wallet/mod.rs:99`, `:2016`, `:2100`, `:2194`); the channel dust
limit is the negotiated `ChannelParams.dustLimitSat` (`Types.lean:78-105`).
The target is a separation lemma, not a claim that `546` is Bitcoin Core's
relay dust threshold for every output type.

**Priority:** P2.  **Fidelity risk:** low.  **Feasibility:** trivial.
**Type:** model extension / interface lemma.

**Weakening check:** do not replace `ChannelParams.dustLimitSat` with `546` or
add a global `walletDustLimit = channelDustLimit` axiom.  The existing
`isDust_self`/equality-is-not-dust boundary (`Fee.lean:156-157`) must remain.

### 4.5 P2 — `rbf_replacement_rate_strict`

**Fully-qualified name:**
`LnLean.Proofs.Bitcoin.TxConstruction.rbf_replacement_rate_strict`

**Statement shape:**
```lean
def rbfDefaultRate (oldRate estimate incremental : Nat) : Nat :=
  max (oldRate + incremental) estimate

theorem rbf_replacement_rate_strict
    (oldRate estimate incremental : Nat)
    (hinc : 0 < incremental) :
    oldRate < rbfDefaultRate oldRate estimate incremental ∧
    oldRate + incremental ≤ rbfDefaultRate oldRate estimate incremental
```

**Hypotheses:** the old rate is `calculate_fee_rate old_tx`; the call uses the
default path (no user-supplied rate); `incremental` is the incremental relay
fee, positive.  The theorem is about the *target* rate, not BDK acceptance.

**Non-vacuity witness:** `oldRate = 253`, `incremental = 25`,
`estimate = 100`; result `278`, and `253 < 278`.  The 253/278 pair matches the
pinned RBF splice test (`fee_estimator.rs:195-199`); the wallet path uses
`old + INCREMENTAL_RELAY_FEE` (`wallet/mod.rs:3502-3514`).

**Why it is faithful:** it is exactly the local minimum-rate arithmetic LDK
computes before calling BDK.  It does **not** claim the replacement pays a
higher absolute fee, conflicts with the old transaction, has no new unconfirmed
inputs, or is accepted under BIP125; those are external mempool policy.

**Priority:** P2.  **Fidelity risk:** low for arithmetic, high if misread as a
BIP125-validity theorem.  **Feasibility:** trivial.  **Type:** model extension;
replacement policy external.

**Weakening check:** keep `hinc : 0 < incremental`; with `incremental = 0` the
strict conclusion is false for a lower estimate.  Do not derive
`Fee.feeSufficient` for the old transaction from this theorem.

### 4.6 P2 — `cpfp_package_fee_sufficient`

**Fully-qualified name:**
`LnLean.Proofs.Bitcoin.TxConstruction.cpfp_package_fee_sufficient`

**Statement shape:**
```lean
def packageRequiredFee (r : FeeRate) (parentWeight childWeight : Weight) : Msat :=
  ⟨(r.msatPerKw * (parentWeight.val + childWeight.val) + 999) / 1000⟩

def packagePaidFee (parentFee childFee : Msat) : Msat :=
  ⟨parentFee.val + childFee.val⟩

def packageFeeSufficient
    (r : FeeRate) (pw cw : Weight) (pf cf : Msat) : Prop :=
  (packageRequiredFee r pw cw).val ≤ (packagePaidFee pf cf).val

theorem cpfp_package_fee_sufficient
    (r : FeeRate) (pw cw : Weight) (pf : Msat)
    (h : pf.val ≤ (packageRequiredFee r pw cw).val) :
    packageFeeSufficient r pw cw pf
      ⟨(packageRequiredFee r pw cw).val - pf.val⟩
```

**Hypotheses:** parent and child weights are declared; parent fee is at most
the package requirement; the child pays the residual; the package is exactly
the parent plus one child.  No assumption about anchor script validity or
mempool acceptance.

**Non-vacuity witness:** parent weight `1116`, parent fee `0`, child weight
`500`, target `⟨1000⟩` msat/kw; package requirement is `1616` msat, child pays
`1616` msat.  A second witness has a nonzero parent fee and a smaller child
fee.

**Why it is faithful:** it captures the standard CPFP package-feerate
arithmetic: the child may subsidize the parent only through the package total.
It does **not** model TRUC/P2A, ephemeral dust, ancestor/descendant limits,
package relay, or the upstream LDK anchor-spend construction
(`event.rs:2384-2408`; `AnchorProps.lean:62-77`).

**Priority:** P2.  **Fidelity risk:** medium (simple package feerate only).
**Feasibility:** medium (floor/ceiling arithmetic; use `Nat` carefully).
**Type:** model extension; package relay policy external.

**Weakening check:** do not state that a sufficient package fee implies the
parent is relayable or the child is a valid anchor spend.  The theorem must not
hide the `pf ≤ required` premise; an overpaying parent is a separate case.

### 4.7 P2 — `package_parent_before_child`

**Fully-qualified name:**
`LnLean.Proofs.Bitcoin.TxConstruction.package_parent_before_child`

**Statement shape:** use an abstract package row so the theorem is about
ordering, not transaction serialization:
```lean
structure PackageTx where
  id : Nat
  spends : List Nat

def TopologicallyOrdered (l : List PackageTx) : Prop :=
  ∀ (i j : Nat) (hi : i < l.length) (hj : j < l.length),
    l[j].id ∈ l[i].spends → j < i

theorem package_parent_before_child
    (parents : List PackageTx) (child : PackageTx)
    (hids : (parents.map (fun p => p.id)).Nodup)
    (hchild : ∀ pid ∈ child.spends, ∃ p ∈ parents, p.id = pid)
    (hnoGrand : ∀ p ∈ parents, p.spends = []) :
    TopologicallyOrdered (parents ++ [child])
```

**Hypotheses:** parent ids are distinct; every package input of the child names
a parent; parents do not spend another package transaction (no grandparents);
the package is the LDK shape of several parents plus one child.

**Non-vacuity witness:** parents `[{id := 1, spends := []}, {id := 2, spends := []}]`,
child `{id := 3, spends := [1, 2]}`; `parents ++ [child]` is topologically
ordered.

**Why it is faithful:** `tx_broadcaster.rs:78-103` sorts by
`any_spends_from_package` and debug-asserts exactly one child and no
grandparents; `chain/mod.rs:669-672` relies on parents-before-child delivery.
The target proves the local ordering obligation, not `submitpackage`
acceptance or mempool package limits.

**Priority:** P2.  **Fidelity risk:** low for the ordering relation; the Rust
sort's stability and debug assertions are implementation details, not proved
here.  **Feasibility:** low/medium (list-index reasoning).  **Type:** model
extension; package relay external.

**Weakening check:** do not drop `hnoGrand` to make the theorem easier; a
grandparent chain is exactly what the LDK debug assertion excludes.  Do not
claim the theorem for arbitrary package sizes.

### 4.8 Not proposed

No target is proposed for **PSBT/BIP174**, **BDK wallet internals**, **fee
estimation**, **BIP125 full validity**, **TRUC/P2A**, **ephemeral dust**, or
**package relay**.  These are not small arithmetic extensions: they require an
external wallet/mempool/relay model, and a theorem over a locally invented
policy would hide the assumption rather than close the gap.

## 5. Assumptions, counterexamples, and non-vacuity risks

### 5.1 Existing results that must not be weakened

* `LnLean.Bitcoin.fundingOutput_moneyRange` and
  `FundingParams.WellFormed`: a new `FundingPlan.WellFormed` is additive; do not
  redefine the existing predicate.
* `LnLean.Proofs.Bitcoin.fee_not_bounded_by_funding_wellformedness`
  (`WeightProps.lean:370-382`): well-formed funding value does **not** bound
  the fee.  Any `fundingTx_value_partition` proposal must keep the explicit
  fee-sufficiency hypothesis; it must not manufacture a fee bound from
  `MoneyRange`.
* `LnLean.Channel.Fee.commitmentSigningGate_rejected_iff_insufficient`
  (`FeeTargets.lean:225-238`) and its normal-phase form: do not add RBF/CPFP
  conditions to the gate or weaken the iff to a one-way implication.
* `sampleCommitment` (`FeeTargets.lean:503-535`): keep the 724-weight,
  1-sat-fee witness that signs at `⟨1000⟩` and rejects at `⟨2000⟩`.
* `boundaryTx`/`fundedTx` (`HtlcAggregateTargets.lean:828-895`): keep the
  rejected/funded pair over the same aggregate rows.  This is the non-vacuity
  witness for fee/weight accounting.
* `witnessAggregate` (`HtlcAggregateTargets.lean:740-767`): keep the two-row,
  three-sat coverage witness.
* `weightTargets_serializedWeight_anchor_gap`
  (`WeightTargets.lean:348-355`) and H33
  `anchor_literal_weight_neq_fee_basis`/`anchor_gap_retained`
  (`H33.lean:457-522`): `1124 + 172*k` is the fee basis; the literal anchor
  serialization is `1116 + 172*k`.  Do not "fix" the model by replacing either
  side.
* D12 `unconditional_ordering_refuted` and
  `cltv_tiebreak_not_recoverable`
  (`CommitmentOrderTargets.lean:63-77`): the legacy `commitmentOutputs`
  function is not ordered and loses the CLTV tiebreak.  The rich
  `CommitmentTx` theorem is the only ordering claim.
* `fee_not_bounded_by_funding_wellformedness` also blocks any proposal that
  would make `FundingParams.WellFormed` imply `FeeBudget`; the two are
  independent.

### 5.2 New assumptions introduced by the proposals

| Assumption | Where it appears | Why it is explicit |
|---|---|---|
| `WalletUtxo.confirmed` is a model flag | `fundingTx_value_partition`, `selectConfirmedUtxos_sound` | It is not chain finality or reorg resistance.  `LN-L1-003`/`L1-06` own that separate boundary. |
| Inputs are pairwise distinct | `FundingPlan.WellFormed` | Prevents a double-spend-shaped plan; it is not a consensus check. |
| `walletDustLimit = 546` is an LDK policy constant | `drain_retains_anchor_reserve`, `walletDust_ne_channelDust` | It is not Core's relay dust threshold and not the channel's negotiated `dust_limit_satoshis`. |
| Reserve is the total untrusted-anchor reserve | `DrainPlan` | `lib.rs:2717-2734` multiplies open untrusted anchor channels by 25,000; trusted peers are zero (`:2736-2748`). |
| RBF theorem is about the default target rate | `rbf_replacement_rate_strict` | A user-supplied rate bypasses `max`; BDK may reject it. |
| CPFP theorem is a two-transaction package | `cpfp_package_fee_sufficient` | No TRUC/P2A, no package relay, no anchor script semantics. |
| Package has one child and no grandparents | `package_parent_before_child` | Mirrors the LDK debug assertions, not a general DAG theorem. |

### 5.3 Non-vacuity risks

* `FundingPlan.WellFormed` could be vacuous if `changeScript?` and positive
  change are never simultaneously satisfiable.  The concrete 60,000/39,000/1,000
  witness must be proved `WellFormed` with a concrete change script.
* `DrainPlan.WellFormed` must have both a `reserve > 546` witness and a
  `reserve <= 546` witness; otherwise the "retains" theorem could be vacuously
  true at the only inhabited point.
* `selectConfirmed` needs a `some` witness and a `none` witness.  The `none`
  case is important: it prevents a totalized selector from inventing funds.
* `rbf_replacement_rate_strict` is false at `incremental = 0` when the estimate
  is lower than the old rate.  The positivity hypothesis is load-bearing.
* `cpfp_package_fee_sufficient` has a floor/ceiling boundary: the child fee is
  a residual, and an overpaying parent makes the residual zero.  Both a
  zero-parent-fee and a nonzero-parent-fee witness should be retained.
* `package_parent_before_child` must include a witness where the input list is
  not already parent-first, so the theorem is not merely `rfl` on a sorted
  literal.
* `walletDust_ne_channelDust` is a concrete witness, not a universal
  independence claim; do not generalize it to "all wallet thresholds differ
  from all channel limits."

### 5.4 Proposals that would hide an assumption (reject)

* Treating `1124` as the literal serialization weight.  Reject; use the H33
  fee-basis interpretation.
* Treating `546` as `ChannelParams.dustLimitSat`.  Reject; use the separation
  witness.
* Treating the local RBF rate arithmetic as BIP125 validity.  Reject; keep
  absolute-fee/conflict/descendant policy external.
* Treating package fee arithmetic as `submitpackage` acceptance.  Reject; keep
  relay policy external.
* Treating a PSBT as an opaque `ByteArray` and proving a round-trip without
  roles, signatures, or UTXO commitments.  Reject; no PSBT target is proposed.
* Replacing `commitmentSigningGate_rejected_iff_insufficient` with a
  sufficiency-only theorem to make room for CPFP/RBF.  Reject; the iff is a
  catalog target.

## 6. Wave-13 recommendation

**Do not implement any of these targets in wave 13.**  This lane is a
source-grounded scoping review.  The current tree is green at `f7f0628`, and
there is no existing wallet/UTXO/mempool model to extend safely without
introducing a large new abstraction and several external assumptions.

**Wave 14, only if the parent wants a small additive lane:**

1. `fundingTx_value_partition` — P1, highest value, small arithmetic/list
   model, directly addresses the missing funding-transaction layer.
2. `drain_retains_anchor_reserve` plus the `reserve <= 546` counterexample —
   P1, small and catches a real LDK branch.
3. `walletDust_ne_channelDust` — P2, trivial but prevents a serious
   conflation.
4. `selectConfirmedUtxos_sound` — P2, only if the lane explicitly accepts that
   it is a simplified confirmed-only selector, not BDK.

**Defer to an external/human barrier:** PSBT/BIP174, BDK coin selection and
change policy, chain fee estimation, BIP125 full replacement policy, anchor
CPFP/TRUC/P2A, package relay, and `submitpackage` acceptance.  These are not
formalized by the local arithmetic targets and should not be advertised as
covered.

**Catalog impact:** do not silently extend `LN-L1-006` (weight) or `LN-CH-005`
(fee gate) to cover funding construction.  If the wave-14 lane lands, add a new
row through the normal catalog process (for example an `LN-L1-*` funding
transaction-construction row) rather than relabeling an existing theorem.

**Top proposed target:** `fundingTx_value_partition`.  It is the smallest
target that turns the largest missing behavior — funding transaction
construction and change — into an explicit, non-vacuous model obligation while
preserving every existing theorem and leaving PSBT/BDK policy external.

## 7. Evidence and commands

### 7.1 Pins and tree state

```sh
git rev-parse HEAD
# f7f062817c185cd70004bb26c652deb99c6fd4bd

git -C /tmp/opencode/ldk-refs/ldk-node rev-parse HEAD
# fa123fed131e27ecc420b77fa7086fcf1ddaebb8

git -C /tmp/opencode/ldk-refs/ldk-server rev-parse HEAD
# c17dc11dde38f88c53457039ddf30c6b90a63ba2

git status --short
# only pre-existing untracked review scaffolding/status files; this report is the only new file
```

### 7.2 Lean inspection commands

```sh
rg -n 'LN-L1-006|LN-CH-003|LN-CH-005' docs/THEOREM-INDEX.md docs/TRACEABILITY.md
rg -n '724|1124|172|weight' LnLean/Bitcoin/Seam.lean LnLean/Channel/Commitment.lean
rg -n 'feeForWeight|feeSufficient|isDust|commitmentSigningGate' \
  LnLean/Channel/Fee.lean LnLean/Proofs/Channel/FeeTargets.lean
rg -n 'weightTargets_serializedWeight_anchor_gap|anchorLiteralWeight|anchor_gap_retained' \
  LnLean/Proofs/Bitcoin/WeightTargets.lean LnLean/Proofs/WaveH/H33.lean
rg -n 'sighashWitnessV0|ofTx|bL_encode_ofTx' LnLean/Bitcoin/Sighash.lean
rg -n 'output_ordering|unconditional_ordering_refuted|cltv_tiebreak_not_recoverable' \
  LnLean/Proofs/Channel/CommitmentOrderTargets.lean
rg -n 'fundingTx|PSBT|coin selection|RBF|CPFP|package relay|fee estimation|walletDust' LnLean
# no definitions; only exclusion notes in Channel/Fee.lean, FeeTargets.lean,
# AnchorProps.lean, CommitmentIntegrationTargets.lean, FeeWeightDust.lean, etc.
```

### 7.3 LDK inspection commands

```sh
rg -n 'create_funding_transaction|build_tx|extract_tx|DUST_LIMIT_SATS' \
  /tmp/opencode/ldk-refs/ldk-node/src/wallet/mod.rs
rg -n 'select_confirmed_utxos|exclude_unconfirmed|change_output' \
  /tmp/opencode/ldk-refs/ldk-node/src/wallet/mod.rs
rg -n 'send_to_address|AllRetainingReserve|AllDrainingReserve|get_balances_inner' \
  /tmp/opencode/ldk-refs/ldk-node/src/wallet/mod.rs \
  /tmp/opencode/ldk-refs/ldk-node/src/payment/onchain.rs
rg -n 'bump_fee_rbf|BIP 125|INCREMENTAL_RELAY_FEE|1.5x|additional_fee_sats' \
  /tmp/opencode/ldk-refs/ldk-node/src/wallet/mod.rs
rg -n 'sort_parents_child_package_topologically|any_spends_from_package|submitpackage' \
  /tmp/opencode/ldk-refs/ldk-node/src/tx_broadcaster.rs \
  /tmp/opencode/ldk-refs/ldk-node/src/chain/mod.rs \
  /tmp/opencode/ldk-refs/ldk-node/src/chain/bitcoind.rs \
  /tmp/opencode/ldk-refs/ldk-node/src/chain/esplora.rs
rg -n 'handle_onchain_send_request|handle_onchain_bump_fee_request|handle_onchain_receive_request' \
  /tmp/opencode/ldk-refs/ldk-server/ldk-server/src/api
```

### 7.4 What was not run

No Lean build, `lake build`, `cargo test`, external network fetch, or mutation
of the pinned clones was performed.  The report is based on source inspection
and exact line citations only.  No Lean/docs/scripts/tests/vendor file outside
this report was edited.
