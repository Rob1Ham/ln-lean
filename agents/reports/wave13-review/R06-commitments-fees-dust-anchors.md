# R06 — Commitment state, fees, dust, and anchor outputs
**Status:** read-only review
**Pins:** LDK Node `fa123fed131e27ecc420b77fa7086fcf1ddaebb8`, LDK Server `c17dc11dde38f88c53457039ddf30c6b90a63ba2`

Review base: `repair/integrated` at `f7f0628`; BOLTs at
`1aadb719b4007c4cea0ba6e36b08c4fb53788dee`. No Lean, docs, tests, vendor,
branches, or other lanes' reports were modified. The only write in this lane is
this file.

## 1. Scope and current Lean surface

This lane covers commitment output construction, the commitment base fee,
HTLC-second-stage fees and trimming, dust limits and dust exposure, the
`update_fee` transition, zero-fee commitments, and anchor outputs (value,
presence, CPFP/reserve implications). The catalog rows that touch this surface
are:

| Row | Named catalog target(s) | Current reading |
|---|---|---|
| `LN-L1-005` | `LnLean.Bitcoin.anchorValue_eq` | Anchor value is exactly 330 sat. Proved and faithful. |
| `LN-L1-006` | `LnLean.Proofs.Bitcoin.commitmentBaseWeight_model_target` | 724/1124 fee basis plus 172 per untrimmed HTLC; the 8 WU serialization gap is explicit. Proved. |
| `LN-CH-002` | `LnLean.Channel.Commitment.outputs_nonnegative` | Nonnegativity is structural; the funding bound needs the BOLT 3 balance equation. Proved under that equation; D46 keeps the unconditional counterexample. |
| `LN-CH-003` | `LnLean.Channel.Commitment.output_ordering` plus net/migration targets | The rich model has both a gross and a net dust path. The catalog's first-named ordering target and the actual sighash consumer use the gross path. Partially covered. |
| `LN-CH-005` | `commitmentSigningGate_rejected_iff_insufficient`; `_iff_no_checkedSigning` | Exact fee gate at the commitment record and the D13 checked relation. The production `State.Step` does not carry the gate. Faithful for the stated claim, with that scope caveat. |
| `LN-CH-006` | `LnLean.Channel.Reserve.bounds` | Admissible-add reserve and exposure bounds. `ExposurePolicy` is proof-layer only; `State.Step` does not enforce it. |
| `LN-CH-007` | `HtlcAggregate` targets | Aggregate second-stage coverage and weight/fee accounting; outside the main anchor-presence question but shares the 663/703 weight surface. |

The concrete Lean surface inspected:

- `LnLean/Channel/Types.lean:188-207` defines `CommitmentHTLCOutput` with
  **gross** `amountSat` and **net** `netAmountSat` (default identity) and says
  the dust test is on the net value; `:209-211` fixes `anchorOutputSat = 330`;
  `:236-256` defines the stored `Commitment.trimmedTotalSat` and documents
  that it is the **gross** value removed by trimming.
- `LnLean/Channel/Commitment.lean:109-114` is the legacy
  `Commitment.commitmentOutputs`: it trims `to_local`/`to_remote` only on
  `= 0` and emits **both** anchors whenever `anchorOutputs = true`.
  `:322-324` makes `Commitment.weight` the BOLT 3 expected weight.
  `:380-402` is the canonical `commitmentPairOfBalances`: the funder's own
  output is reduced by `fee` only, not by the anchor values.
- `LnLean/Channel/Commitment.lean:914-922` makes each anchor present exactly
  when `anchorOutputs = true`; `:927-937` builds the gross/rich output list;
  `:951-970` builds the net/BOLT-3 exact list `outputsNet`.
- `LnLean/Proofs/Channel/CommitmentOrderTargets.lean:89-108` is the catalog
  `output_ordering`. Its HTLC premises test `h.amountSat < dustLimitSat` and
  `dustLimitSat ≤ h.amountSat`; anchors are unconditional.
- `LnLean/Proofs/Channel/CommitmentGrossNetTargets.lean:687-711` is
  `CommitmentTx.outputsNet_spec`; `:716-721` is
  `outputsNet_trims_iff_gross_threshold`; `:110-164` defines
  `htlcSecondStageFee` and `NetConsistent`.
- `LnLean/Proofs/Channel/CommitmentTypesTargets.lean:448` is
  `migrateNet_trims_iff_gross_threshold`.
- `LnLean/Proofs/ModelHardening/F04.lean:41-65` defines `anchorDebitSat` and
  `funderDebitSat`; `:222-226` proves the legacy 660-sat overfunding witness;
  `:246-262` defines `commitmentPairWithAnchorDebit`; `:276-313` proves
  corrected conservation and the anchor-debit rule. The corrected constructor
  has **no production consumer**.
- `LnLean/Proofs/Channel/CommitmentTxProps.lean:435-445` records
  `LN-COMMIT-005` and proves `commitmentPair_conservation_anchors_gap`.
- `LnLean/Channel/State.lean:117-121` is `Step.updateFee`; its only premise is
  `phase = normal`.
- `LnLean/Proofs/Channel/FeeProps.lean:132-134` is `checkedFeeUpdate`; it is a
  proof-layer function, not a constructor of `Step`.
- `LnLean/Proofs/WaveD/D14.lean:83-90` defines `ExposurePolicy`;
  `:112-120` defines `dustContribution` (trimmed HTLC value only);
  `:406-417` is `Reserve.bounds`.
- `LnLean/Proofs/Bitcoin/WeightTargets.lean:351-355` proves the exact
  `serialized + 8 = 1124` anchor gap.

The important structural fact is that the repository has **three** commitment
output surfaces, with different fidelity:

1. `Commitment.commitmentOutputs` — legacy list, no real dust filter, both
   anchors unconditional. This is what `SighashTargets.viewOfState` and the
   coverage consumer read.
2. `CommitmentTx.outputs` — rich list, `to_local`/`to_remote` trimmed by dust,
   HTLCs tested on gross `amountSat`, both anchors unconditional.
3. `CommitmentTx.outputsNet` — rich list, HTLCs tested on net
   `netAmountSat`, with `outputsNet_spec` and the exact gross-threshold
   equivalence already proved.

The net path is therefore **mechanized but not canonical**. That distinction
drives most of this report.

## 2. LDK datapoints (with `file:line`)

### 2.1 Anchor reserve, CPFP, and fee spikes

- LDK Node keeps a **25,000 sat per-channel on-chain reserve** for anchor
  channels: `ldk-node/src/config.rs:38`
  (`DEFAULT_ANCHOR_PER_CHANNEL_RESERVE_SATS = 25_000`), `:452-455` (default
  table: `trusted_peers_no_reserve = []`, `per_channel_reserve_sats = 25000`,
  `enable_zero_fee_commitments = false`), `:487-490` (the reserve may or may
  not suffice depending on the fee market at closure), `:510-513` (defaults).
- The reserve is maintained per anchor channel unless the counterparty is in
  `trusted_peers_no_reserve`:
  `ldk-node/src/lib.rs:2717-2734` (`total_anchor_channels_reserve_sats`) and
  `:2736-2748` (`new_channel_anchor_reserve_sats`).
- Fee bumping is **CPFP at broadcast time**, not a caller-supplied close
  feerate: `ldk-node/src/types.rs:416-444` describes `ReserveType::Adaptive`
  (“fee-bump commitment transactions via CPFP at broadcast time”; the
  pre-signed commitment fee may be insufficient; the reserve covers it),
  `TrustedPeersNoReserve`, and `Legacy` (“commitment transaction fees are
  pre-committed at channel open time”).
- The close and force-close RPCs carry **no feerate**:
  `ldk-server-grpc/src/proto/api.proto:700-707` (`CloseChannelRequest` has only
  `user_channel_id` and `counterparty_node_id`), `:714-721`
  (`ForceCloseChannelRequest` adds only `force_close_reason`); handlers at
  `ldk-server/src/api/close_channel.rs:23-46` pass those fields only.
- LDK exposes the negotiated commitment/HTLC feerate as data, not as a close
  parameter: `ldk-node/src/types.rs:538-541`
  (`feerate_sat_per_1000_weight`), and the same field in
  `ldk-server-grpc/src/proto/types.proto:552-554`.
- A separate force-close fee cap exists:
  `ldk-node/src/config.rs:809-819` (`max_dust_htlc_exposure`,
  `force_close_avoidance_max_fee_satoshis`), exposed through
  `ldk-server-grpc/src/proto/types.proto:712-720` and parsed in
  `ldk-server/src/api/mod.rs:122-136`.

### 2.2 Zero-fee commitments

- When enabled, LDK Node will **first attempt**
  `option_zero_fee_commitments`, then fall back to
  `option_anchors_zero_fee_htlc_tx` and `option_static_remotekey`:
  `ldk-node/src/config.rs:491-505`; the feature defaults to `false` at
  `:512-513`.
- The feature is wired into the handshake config:
  `ldk-node/src/config.rs:568-571`
  (`negotiate_anchor_zero_fee_commitments =
  enable_zero_fee_commitments`).
- Negotiation is conditional on peer support:
  `ldk-node/src/lib.rs:237-243`
  (`supports_anchors_zero_fee_htlc_tx()` or, if enabled,
  `supports_anchor_zero_fee_commitments()`), and channel-type detection at
  `:245-247`.
- Zero-fee channels “remove all commitment feerate negotiation” and source
  “all the fees required to confirm the commitment from the anchor reserve of
  the channel closer at the time of force-close”; the chain source must support
  `submitpackage`, TRUC, P2A, and ephemeral dust (`config.rs:493-498`).

### 2.3 Dust exposure

- `max_dust_htlc_exposure` is a per-channel limit on loss to on-chain fees,
  “including in-flight HTLCs which are burned to fees as they are too small to
  claim on-chain and fees on commitment transaction(s) broadcasted by our
  counterparty in excess of our own fee estimate”
  (`ldk-node/src/config.rs:809-814`).
- The policy type is either a fixed millisatoshi limit or a feerate
  multiplier: `ldk-node/src/config.rs:859-879`
  (`MaxDustHTLCExposure::FixedLimit { limit_msat }` /
  `FeeRateMultiplier { multiplier }`).
- `current_dust_exposure_msat` is “the maximum of the dust exposure on the
  holder and counterparty commitment transactions. It includes pending HTLCs
  below the dust threshold and the portion of commitment transaction fees that
  contributes to dust exposure” (`ldk-node/src/types.rs:628-638`).
- The server exposes the same policy through
  `ldk-server-grpc/src/proto/types.proto:722-736` and
  `ldk-server/src/api/mod.rs:96-109`; `update_channel_config` can change it at
  runtime (`ldk-server/src/api/update_channel_config.rs:22-62`).

### 2.4 BOLT 3 / BOLT 2 semantics used below

- Anchor presence: both anchors are always added **except** when there are no
  HTLCs and one party's commitment output is below dust; then only the anchor
  for the output that materializes is added
  (`refs/bolts/03-transactions.md:150-153`).
- Shared anchor: version-3/zero-fee commitments add a P2A `OP_1 <0x4e73>`
  output with standard dust limit 240 sat; if the input-minus-other-outputs
  difference is below 240, the anchor takes that value and the commitment pays
  no on-chain fee; otherwise the anchor is 240 and the remainder goes to fees
  (`refs/bolts/03-transactions.md:178-195`).
- Trimmed outputs go to the commitment fee, or to the shared anchor under
  zero-fee (`refs/bolts/03-transactions.md:305-311`); for HTLCs the test uses
  the amount minus the second-stage fee (`:336-348`).
- Anchor debit: the base fee and both anchor values must be subtracted from the
  funder's output (`refs/bolts/03-transactions.md:321-326`).
- Expected weights: commitment 724/1124, HTLC-timeout 663/666, HTLC-success
  703/706 for no-anchor/anchor (`refs/bolts/03-transactions.md:491-498`); the
  second-stage fees are 0 under anchors or zero-fee (`:505-513`).
- `update_fee` is sent only by the fee payer, is forbidden under zero-fee, and
  is rejected if the sender is not responsible for the fee
  (`refs/bolts/02-peer-protocol.md:3252-3253`, `:3275-3283`); affordability is
  a `SHOULD`/`MAY` policy, not a hard sender rule (`:3259-3263`,
  `:3306-3310`). A feerate increase can trim multiple HTLCs
  (`:3285-3293`) and dust exposure is the BOLT 2 policy
  (`:2726-2766`).

## 3. Gap matrix

| Behavior | Lean status | LDK evidence | Gap / counterexample | Priority |
|---|---|---|---|---|
| Funder pays the two anchor outputs on both commitments | **contradicted** | `types.rs:416-444`; BOLT 3 `03-transactions.md:321-326` | `commitmentPairOfBalances` subtracts only `fee` (`Commitment.lean:387-398`). F04 proves output sum + fee = funding **+ 660** (`F04.lean:222-226`; `CommitmentTxProps.lean:435-445`, `LN-COMMIT-005`). The corrected `commitmentPairWithAnchorDebit` exists but is unused. | **P0** |
| Single-anchor exception: no HTLCs and one commitment output below dust | **contradicted** | BOLT 3 `03-transactions.md:150-153` | `Commitment.commitmentOutputs` emits both anchors whenever `anchorOutputs = true` (`Commitment.lean:113-114`); `localAnchorOutput`/`remoteAnchorOutput` are unconditional on `anchorOutputs` (`:914-922`). Witness: `toLocalSat = 0`, `toRemoteSat = 50_000`, no HTLCs, dust 330 → model emits two anchors (660 sat); BOLT emits one (330 sat). Disclosed as `LN-COMMIT-004` (`CommitmentTxProps.lean:463`) but never mechanized. | **P0** |
| HTLC dust test uses net value (`gross - second-stage fee`) | **partially covered** | BOLT 3 `03-transactions.md:336-348`; LDK `types.rs:628-638` | The exact net path exists: `htlcOutputNet` (`Commitment.lean:951-957`), `outputsNet` (`:966-970`), `outputsNet_spec` (`CommitmentGrossNetTargets.lean:687-711`), `outputsNet_trims_iff_gross_threshold` (`:716-721`). But the catalog row `LN-CH-003` first names `output_ordering` (`CommitmentOrderTargets.lean:89-108`), which tests gross `amountSat`, and the sighash consumer reads `commitmentOutputs`. Witness: gross 1000, second-stage fee 167, dust 900 → gross path keeps (1000 ≥ 900), net path trims (833 < 900; equivalently 1000 < 1067). | **P0** |
| Zero-fee commitments and `shared_anchor` | **missing** | BOLT 3 `03-transactions.md:178-195`, `:305-311`, `:464-475`; LDK `config.rs:491-505`, `:512-513`; `lib.rs:237-243` | No `zeroFee`/`commitmentVersion` field, no `sharedAnchor` output, no feerate-0 policy, no redirection of trimmed value. Explicitly “NOT modelled” in `Commitment.lean:42` and `FeeProps.lean:55-57`. | **P1** |
| `update_fee` only from the fee payer; forbidden under zero-fee; feerate bounds | **partially covered / missing** | BOLT 2 `02-peer-protocol.md:3252-3253`, `:3275-3283`; LDK `config.rs:493-498` | `Step.updateFee` has only `phase = normal` as a premise (`State.lean:117-121`); it accepts a non-funder update and any feerate. `checkedFeeUpdate` (`FeeProps.lean:132-134`) checks only fee sufficiency and is not wired into `Step`. No zero-fee prohibition. Witness: a non-funder `updateFee` is a valid `Step` today. | **P1** |
| Dust exposure includes counterparty commitment-fee excess | **partially covered** | LDK `types.rs:628-638`; `config.rs:809-814`, `:859-879`; BOLT 2 `02-peer-protocol.md:2726-2766` | `ExposurePolicy` is a proof-layer parameter (`D14.lean:83-90`), not a `ChannelParams` field; `dustContribution` counts only trimmed HTLC value (`:112-120`), not the fee-excess component; `Step` does not enforce exposure. `Reserve.bounds` (`:406-417`) is about `AdmissibleAdd`, not `Step`. | **P2** |
| Anchor reserve, CPFP, fee spikes | **unmodelled / external** | LDK `config.rs:38`, `:452-455`, `:487-490`, `:510-513`; `lib.rs:2717-2748`; `types.rs:416-444`; close API `api.proto:700-721` | No CPFP, no 25,000-sat reserve, no trusted-peer/no-reserve distinction, no pre-anchor-vs-anchor fee timing. Close/force-close carry no feerate. This is node policy plus a mempool/package-relay model; it is not a BOLT arithmetic rule. | **P2 / external** |
| Anchor HTLC second-stage weights 666/706 | **partially covered** | BOLT 3 `03-transactions.md:495-498`, `:505-513` | Only `htlcTimeoutWeight = 663` and `htlcSuccessWeight = 703` are defined (`CommitmentIntegrationTargets.lean:107-124`); the anchor variants are absent. The anchor **fee** is correctly 0 (`htlcSecondStageFee_anchors`); the missing part is the weight, relevant to serialized/CPFP accounting. | **P2** |
| 1124 anchor fee basis vs 1116 + 8 WU serialization | **covered faithfully, with explicit gap** | BOLT 3 `03-transactions.md:491-498`; LDK `types.rs:538-541` | `WeightTargets.lean:351-355` proves `serialized + 8 = 1124`; the 8 WU is the Appendix A `count_tx_out` difference. No new target; do not claim 1124 is the literal serialized weight. | scope note |
| Base fee gate (LN-CH-005) | **covered faithfully (proof-layer relation)** | BOLT 3 `03-transactions.md:503-522`; BOLT 2 `02-peer-protocol.md:3256-3266` | `commitmentSigningGate_rejected_iff_insufficient` is exact for the recorded `feeSat` and expected weight. `_iff_no_checkedSigning` is about D13 `waveD_d13_FeeCheckedStep`, not the production `Step`. No production fee gate exists. | scope note |
| Output nonnegativity and funding bound (LN-CH-002) | **covered faithfully under the balance equation** | BOLT 3 `03-transactions.md:321-348` | Nonnegativity is structural (`Nat`); the funding bound needs `totalOutputValue + feeSat = fundingValueSat`. D46 retains the unconditional counterexample. | no action |
| Reserve / in-flight bounds (LN-CH-006) | **partially covered, correctly scoped** | BOLT 2 `02-peer-protocol.md:2726-2766`; LDK `config.rs:809-814` | `Reserve.bounds` is proved for `AdmissibleAdd` (`D14.lean:406-417`), with policy and second-stage fees as explicit inputs. `Step` never adds HTLCs or changes balances (`D14.lean` notes this), so the theorem is not a production-transition invariant. | scope note |

## 4. Proposed targets

Seven targets are proposed. Each is additive: none replaces an existing
theorem, and none is allowed to hide a hypothesis. Priorities are P0 (fixes a
proved contradiction or a mis-cited BOLT 3 claim), P1 (required for LDK-level
compatibility), P2 (smaller or policy/external).

### T1 — Corrected anchor-debit pair (P0)

**Fully-qualified name:**
`LnLean.Proofs.Channel.CommitmentAnchorTargets.commitmentPairWithAnchorDebit_conserves`

Promote `anchorDebitSat`, `funderDebitSat`, `Commitment.FunderDebited`,
`CommitmentPair.AnchorDebitRule`, and `commitmentPairWithAnchorDebit` from
`LnLean.Proofs.ModelHardening.F04` into `LnLean.Channel.Commitment` (or a
production alias with the same bodies), and add:

```lean
theorem commitmentPairWithAnchorDebit_conserves
    (localParams remoteParams : ChannelParams) (b : Balance)
    (fee number : Nat) (funder : Direction)
    (hL : fee + anchorDebitSat localParams.anchorOutputs ≤
      (if funder = .local then b.localSat else b.remoteSat))
    (hR : fee + anchorDebitSat remoteParams.anchorOutputs ≤
      (if funder = .local then b.localSat else b.remoteSat)) :
    let p := commitmentPairWithAnchorDebit localParams remoteParams b fee number funder
    p.localCommitment.totalOutputValue + fee = p.localCommitment.fundingValueSat ∧
      p.remoteCommitment.totalOutputValue + fee = p.remoteCommitment.fundingValueSat ∧
      p.AnchorDebitRule b funder

theorem commitmentPairWithAnchorDebit_eq_legacy_of_noAnchors
    (localParams remoteParams : ChannelParams) (b : Balance)
    (fee number : Nat) (funder : Direction)
    (hL : localParams.anchorOutputs = false)
    (hR : remoteParams.anchorOutputs = false) :
    commitmentPairWithAnchorDebit localParams remoteParams b fee number funder =
      commitmentPairOfBalances localParams remoteParams b fee number funder
```

**Hypotheses.** Each commitment's funder debit `fee + 330 * anchors` is at most
the funder's own satoshi balance; this is BOLT 3's affordability condition and
avoids `Nat` truncation. The two flags are separate because the two endpoints
can disagree on `anchorOutputs`.

**Non-vacuity witness.** `b = ⟨50_000_000, 50_000_000⟩` msat, `fee = 1000`,
`number = 0`, `funder = .local`, both anchor flags `true`: debit is `1660`,
which is `≤ 50_000`; outputs are `48_340 + 50_000 + 660 = 99_000`, plus fee
`1000 = 100_000`. The anchor-free specialization with `fee = 1000` gives
`49_000 + 50_000 + 1000 = 100_000` and must be definitionally the legacy pair.
The existing `waveF_f04_counterexample_660` remains the failure witness for
the old constructor.

**Why faithful.** BOLT 3 `03-transactions.md:321-326` requires both anchor
values to be subtracted from the funder's output on both commitments. The
corrected constructor applies `funderDebitSat fee flag` per commitment, exactly
as F04 proves; the bridge shows the change is a strict extension, not a
reinterpretation of anchor-free channels.

**Fidelity risk.** Low. The only modelling choice is per-commitment
`anchorOutputs`, which BOLT 3 permits because the two endpoints negotiate the
feature; the theorem states both flags separately rather than assuming they
agree. No external assumption beyond the funder's affordability.

**Type / feasibility.** Model extension, additive; high feasibility because
F04 already contains the definition and the `omega` proofs. **Do not** change
`commitmentPairOfBalances` in place: `commitmentPair_fee_owner_local/remote`,
`commitmentPair_output_values_swap`, and
`commitmentPair_conservation_noAnchors` assume the fee-only debit, and
`commitmentPair_conservation_anchors_gap` must remain as the explicit gap
record.

### T2 — Exact anchor presence (P0)

**Fully-qualified name:**
`LnLean.Proofs.Channel.CommitmentAnchorTargets.anchorPresence_eq_bolt3`

Define an additive `CommitmentTx.anchorPresence : List CommitmentTxOutput` and
an `outputsUnsortedBolt3` that uses it. Statement shape:

```lean
theorem anchorPresence_eq_bolt3 (tx : CommitmentTx) :
    tx.anchorPresence =
      if tx.commitment.anchorOutputs = false then []
      else if tx.commitment.htlcs = [] ∧
              tx.toLocalOutput = none ∧ tx.toRemoteOutput ≠ none then
        [CommitmentTxOutput.remoteAnchor tx.remoteAnchorScript]
      else if tx.commitment.htlcs = [] ∧
              tx.toRemoteOutput = none ∧ tx.toLocalOutput ≠ none then
        [CommitmentTxOutput.localAnchor tx.localAnchorScript]
      else
        [CommitmentTxOutput.localAnchor tx.localAnchorScript,
         CommitmentTxOutput.remoteAnchor tx.remoteAnchorScript]

theorem anchorPresence_value (tx : CommitmentTx) :
    (tx.anchorPresence.map CommitmentTxOutput.valueSat).sum =
      if tx.anchorPresence.length = 0 then 0
      else if tx.anchorPresence.length = 1 then 330
      else 660
```

**Hypotheses.** None for the definitional presence theorem; the exception
branches require `htlcs = []` and **exactly one** of `toLocalOutput` /
`toRemoteOutput` absent, which is the BOLT 3 condition. The dust/materialization
test is the same `toLocalOutput = none ↔ toLocalSat < dustLimitSat` used by
`outputs_spec`, so the two decisions cannot drift.

**Non-vacuity witness.** `toLocalSat = 0`, `toRemoteSat = 50_000`,
`dustLimitSat = 330`, `htlcs = []`, `anchorOutputs = true` → presence is
`[remoteAnchor]`, value 330. With both outputs above dust → both anchors,
value 660. The current model's `commitmentOutputs` returns two anchors in the
first case, so the counterexample is immediate; `zeroHtlcCommitment_last_two_anchors`
only covers the both-nonzero case and is not contradicted.

**Why faithful.** BOLT 3 `03-transactions.md:150-153`: both anchors are always
added except when there are no HTLCs and one party's commitment output is below
dust; then only the materializing output's anchor is added. This is exactly the
three-way case split above.

**Fidelity risk.** Medium. BOLT 3 does not spell out the both-outputs-absent
case, so the definition restricts the exception to exactly one absent output
and keeps the both-absent case in the two-anchor branch; that is an explicit
modelling choice, not a proved BOLT requirement. The materialization test must
be `CommitmentTx`'s dust test, not the legacy `= 0` test.

**Type / feasibility.** Model extension, additive; high feasibility. Do not
change `localAnchorOutput`/`remoteAnchorOutput` or `outputs_spec`; add the new
presence function and prove a bridge that both-anchor presence is unchanged in
the no-exception case. Note that BOLT 3's expected-weight formula still assumes
both anchors (`03-transactions.md:489-494`), so the single-anchor case changes
the **value** and actual serialized weight (330 sat / 172 WU) but not the
negotiated fee basis `1124`; T2 must not silently change `Commitment.weight`.

### T3 — Canonical net-dust ordering target (P0)

**Fully-qualified name:**
`LnLean.Proofs.Channel.CommitmentNetDust.output_ordering_net`

Add a net analogue of the catalog target, bundling `outputsNet_spec` with the
exact BOLT 3 gross threshold and the identity bridge:

```lean
theorem output_ordering_net (tx : CommitmentTx)
    (hle : ∀ h, tx.netAmountSat h ≤ h.amountSat)
    {anchors : Bool} {r : FeeRate} (hc : NetConsistent tx anchors r) :
    tx.outputsNet.Perm tx.outputsUnsortedNet ∧
    tx.outputsNet.Pairwise CommitmentTxOutput.le ∧
    (tx.outputsNet.map (fun o => o.valueSat)).Pairwise (· ≤ ·) ∧
    (∀ h ∈ tx.commitment.htlcs,
      tx.htlcOutputNet h = none ↔
        h.amountSat < tx.dustLimitSat + htlcSecondStageFee anchors r h) ∧
    (∀ h ∈ tx.commitment.htlcs,
      tx.dustLimitSat ≤ tx.netAmountSat h →
        CommitmentTxOutput.htlc h (tx.htlcScript h) ∈ tx.outputsNet) ∧
    (∀ o ∈ tx.outputsNet, o.kind ≠ .localAnchor → o.kind ≠ .remoteAnchor →
      tx.dustLimitSat ≤ o.valueSat)

theorem outputs_eq_outputsNet_of_identity (tx : CommitmentTx)
    (h : ∀ h, tx.netAmountSat h = h.amountSat) :
    tx.outputs = tx.outputsNet
```

**Hypotheses.** `hle` (net never exceeds gross) and `NetConsistent tx anchors r`
(`net + second-stage fee = gross` for every HTLC). The latter is the genuine
BOLT 3 relation; it must be supplied explicitly for nonzero second-stage fees.
`NetConsistent` is **not** discharged by the default `netAmountSat := amountSat`
unless the fee is 0; a non-vacuity instance must set the net field explicitly.

**Non-vacuity witness.** `dustLimitSat = 900`, `anchors = false`,
`r = ⟨253⟩` (msat/kw), one offered HTLC with gross `1000` and
`netAmountSat = 833`. The timeout fee is `253 * 663 / 1000 = 167`, so
`NetConsistent` holds. `htlcOutput h = some` (1000 ≥ 900) but
`htlcOutputNet h = none` (833 < 900), and the gross threshold
`1000 < 900 + 167 = 1067` also trims. A survivor with gross `1200` and net
`1033` is kept by both. This is the precise divergence the gross-only catalog
target misses.

**Why faithful.** BOLT 3 `03-transactions.md:336-348` trims an HTLC when
`amount - second-stage fee < dust_limit`; `outputsNet_spec` already proves the
net construction and `outputsNet_trims_iff_gross_threshold` proves the exact
equivalence. T3 makes that the named BOLT 3 ordering target and re-points
`LN-CH-003` to it, while retaining `output_ordering` as the legacy/gross
surface.

**Fidelity risk.** Medium. The risk is not the arithmetic but the premise:
`NetConsistent` must be supplied with explicit net values, not discharged by
the default identity. The consumer refinement stays `Perm`; claiming equality
between the sorted net list and the legacy list would overstate BOLT 3 and is
excluded.

**Type / feasibility.** Proof-layer target plus catalog re-point; high
feasibility (the components exist). **No weakening:** keep
`output_ordering`, `d12_output_ordering_fails`,
`wave4_dust_trimming_not_perm`, and
`legacyCoverage_not_preserved_by_net_migration` / `..._at_site`. The
consumer boundary remains `List.Perm`, not equality; do not claim the sorted
legacy list equals `commitmentOutputs`.

### T4 — Checked `update_fee` legality (P1)

**Fully-qualified name:**
`LnLean.Proofs.Channel.FeeUpdate.feeUpdateChecked_exists_iff`

Add an additive checked relation, parallel to D13's fee-checked signing
relation, rather than altering `Step`:

```lean
inductive FeeUpdateCheckedStep (r : FeeRate) (isFunder zeroFee : Bool)
    (w : Weight) (paid : Msat) : Channel → Channel → Prop
  | apply (c : Channel) (hphase : c.phase = ChannelPhase.normal)
      (hf : isFunder = true) (hz : zeroFee = false)
      (hpaid : feeSufficient r w paid) :
      FeeUpdateCheckedStep r isFunder zeroFee w paid c
        { c with localEndpoint :=
            { c.localEndpoint with
              params := { c.localEndpoint.params with feerate := r } } }

theorem feeUpdateChecked_exists_iff
    (c : Channel) (r : FeeRate) (w : Weight) (paid : Msat)
    (isFunder zeroFee : Bool) :
    (∃ c', FeeUpdateCheckedStep r isFunder zeroFee w paid c c') ↔
      c.phase = ChannelPhase.normal ∧ isFunder = true ∧ zeroFee = false ∧
        feeSufficient r w paid
```

**Hypotheses.** `w` is the weight of the commitment being repriced and `paid`
the funder's available fee; the caller supplies `isFunder` and `zeroFee`
because `Channel` currently has no funder-role or zero-fee field. The
affordability/race rule (`02-peer-protocol.md:3259-3263`, `:3306-3310`) is a
`SHOULD`/`MAY` policy, so it is deliberately **not** part of the hard iff;
it can be added as a separate policy predicate.

**Non-vacuity witness.** `r = ⟨1000⟩`, `w = ⟨724⟩`, `paid = ⟨724⟩`,
`isFunder = true`, `zeroFee = false`, `c.phase = normal` → a derivation
exists. `isFunder = false` or `paid = ⟨723⟩` → no derivation. The existing
`checkedFeeUpdate` lemmas (`FeeProps.lean:138-180`) provide the arithmetic
core.

**Why faithful.** BOLT 2 `02-peer-protocol.md:3252-3253` says the message is
sent by the fee payer; `:3275-3283` forbids it under zero-fee and rejects a
non-payer. The relation states exactly those hard conditions plus the fee
sufficiency condition already used by LN-CH-005.

**Fidelity risk.** Medium-high. `isFunder` and `zeroFee` are caller-supplied
Booleans because `Channel` has no funder-role or zero-fee field; the theorem
therefore does not prove that the production state knows these facts. The
affordability/race rule is a `SHOULD`/`MAY` policy and is deliberately excluded
from the hard iff.

**Type / feasibility.** Model extension plus explicit external assumptions
(`isFunder`, `zeroFee`); medium feasibility. **Do not** add these premises to
`Step.updateFee` in place: that removes reachable behaviours and can make
existing existence/reachability theorems vacuous or force a broad audit. If a
later lane does restrict `Step`, it must re-prove the reachability surface and
state the funder role in `Channel`. T4 depends on T5 for a faithful `zeroFee`
field rather than a caller-supplied Boolean.

### T5 — Zero-fee `shared_anchor` value and conservation (P1)

**Fully-qualified name:**
`LnLean.Proofs.Channel.ZeroFeeCommitment.sharedAnchorValue_spec`

Use a standalone proof-layer structure (do **not** add a constructor to
`CommitmentOutput`, which is exhaustively matched in existing proofs):

```lean
structure ZeroFeeCommitment where
  fundingSat : Nat
  outputsSat : Nat
  hle : outputsSat ≤ fundingSat
  feerate : FeeRate
  hzero : feerate.msatPerKw = 0

def ZeroFeeCommitment.sharedAnchorValue (z : ZeroFeeCommitment) : Nat :=
  min 240 (z.fundingSat - z.outputsSat)

def ZeroFeeCommitment.feeContribution (z : ZeroFeeCommitment) : Nat :=
  z.fundingSat - z.outputsSat - z.sharedAnchorValue

theorem sharedAnchorValue_spec (z : ZeroFeeCommitment) :
    z.sharedAnchorValue = min 240 (z.fundingSat - z.outputsSat) ∧
    (z.fundingSat - z.outputsSat < 240 →
      z.sharedAnchorValue = z.fundingSat - z.outputsSat ∧
        z.feeContribution = 0) ∧
    (240 ≤ z.fundingSat - z.outputsSat →
      z.sharedAnchorValue = 240 ∧
        z.feeContribution = z.fundingSat - z.outputsSat - 240) ∧
    z.outputsSat + z.sharedAnchorValue + z.feeContribution = z.fundingSat
```

**Hypotheses.** `outputsSat ≤ fundingSat` avoids `Nat` truncation;
`feerate.msatPerKw = 0` is the zero-fee condition. The structure's `outputsSat`
is the sum of all non-shared-anchor outputs, including trimmed-value
redirection if the caller wants to model it; the theorem does not invent that
redirection.

**Non-vacuity witness.** `fundingSat = 100_000`, `outputsSat = 99_761` →
difference 239, anchor 239, fee contribution 0 (ephemeral-dust case).
`outputsSat = 99_760` → difference 240, anchor 240, fee 0.
`outputsSat = 99_000` → difference 1000, anchor 240, fee 760.

**Why faithful.** BOLT 3 `03-transactions.md:178-195` defines exactly this
`min 240 difference` rule and the two regimes; `:305-311` redirects trimmed
value to the shared anchor under zero-fee; `:464-475` sets `feerate_per_kw = 0`
and requires CPFP. LDK exposes the feature and its default off-state at
`config.rs:491-505`, `:512-513`, and `lib.rs:237-243`.

**Fidelity risk.** Medium. The value arithmetic is faithful, but the
version-3 transaction, P2A script execution, and ephemeral-dust relay rules are
external; the target does not prove a valid zero-fee commitment transaction.
The `outputsSat` input must include any trimmed-value redirection if the caller
wants the BOLT 3 “trimmed value to shared anchor” behavior.

**Type / feasibility.** Model extension; medium feasibility. Version-3
transaction rules, P2A script execution, and the “ephemeral dust” relay rule
are external to this arithmetic and must remain explicit in the module docs.
Do not claim a full zero-fee commitment transaction from this target.

### T6 — Dust exposure including fee excess (P2)

**Fully-qualified name:**
`LnLean.Proofs.Channel.DustExposure.dustExposureWithFees_eq_trimmed_plus_excess`

Additive definition and theorems over the existing `ExposurePolicy`:

```lean
def dustExposureWithFees (c : Channel) (p : ExposurePolicy)
    (feeExcessMsat : Nat) : Nat :=
  max (localExposure c p) (remoteExposure c p) + feeExcessMsat

theorem dustExposureWithFees_eq_trimmed_plus_excess
    (c : Channel) (p : ExposurePolicy) (feeExcessMsat : Nat) :
    dustExposureWithFees c p feeExcessMsat =
      max (localExposure c p) (remoteExposure c p) + feeExcessMsat

theorem dustExposureWithFees_ge_trimmed
    (c : Channel) (p : ExposurePolicy) (feeExcessMsat : Nat) :
    max (localExposure c p) (remoteExposure c p) ≤
      dustExposureWithFees c p feeExcessMsat

theorem dustExposureWithFees_strict_witness
    (c : Channel) (p : ExposurePolicy) (feeExcessMsat : Nat)
    (h : 0 < feeExcessMsat) :
    max (localExposure c p) (remoteExposure c p) <
      dustExposureWithFees c p feeExcessMsat
```

**Hypotheses.** `feeExcessMsat` is the portion of the counterparty commitment
fee above our own estimate; `0 < feeExcessMsat` only for the strict witness.
The theorem is deliberately parameterized because the exact LDK formula is not
in the pinned public surface.

**Non-vacuity witness.** A channel with no live HTLCs has
`localExposure = remoteExposure = 0`; `feeExcessMsat = 500` gives old exposure
0 and new exposure 500. This shows the existing `dustContribution` is a lower
bound, not the full LDK quantity.

**Why faithful (conditionally).** LDK `types.rs:628-638` says
`current_dust_exposure_msat` is the maximum over the two commitments and
includes “the portion of commitment transaction fees that contributes to dust
exposure”; `config.rs:809-814` repeats the fee-excess component. BOLT 2
`:2726-2743` describes the trimmed-HTLC exposure and the `update_fee` increase
path. The exact fee-excess arithmetic is **not** in the pinned LDK Node/Server
references, so this target is conditional on an explicit external formula.

**Fidelity risk.** High. The public LDK description fixes the qualitative
components but not the exact fee-excess formula; treating `feeExcessMsat` as a
free input is honest but does not prove LDK compatibility. The target must not
be cited as the LDK `current_dust_exposure_msat` definition.

**Type / feasibility.** Model extension plus external assumption; medium
feasibility. Keep `ExposurePolicy`, `dustContribution`, `Reserve.bounds`, and
`waveD_d14_exposure_mono_fees` unchanged; T6 adds a term, it does not replace
the proved lower bound. Do not claim `Step` enforces exposure.

### T7 — Anchor second-stage weights (P2)

**Fully-qualified name:**
`LnLean.Proofs.Channel.HtlcWeight.anchorSecondStageWeights_spec`

Additive constants next to the existing 663/703 definitions:

```lean
def htlcTimeoutWeightAnchors : Weight := ⟨666⟩
def htlcSuccessWeightAnchors : Weight := ⟨706⟩

theorem anchorSecondStageWeights_spec :
    htlcTimeoutWeightAnchors.val = 666 ∧
    htlcSuccessWeightAnchors.val = 706 ∧
    htlcTimeoutWeight.val = 663 ∧
    htlcSuccessWeight.val = 703 ∧
    (∀ r : FeeRate,
      htlcTimeoutFeeSat true r = 0 ∧ htlcSuccessFeeSat true r = 0)
```

**Hypotheses.** None; the constants are BOLT 3 literals. The zero-fee conjunct
is already `htlcSecondStageFee_anchors`.

**Non-vacuity witness.** `666 ≠ 663` and `706 ≠ 703`; the existing
`htlcTimeoutWeight_val` / `htlcSuccessWeight_val` remain 663/703. The anchor
fee theorem remains 0, so there is no hidden fee change.

**Why faithful.** BOLT 3 `03-transactions.md:495-498` states the anchor
second-stage weights as 666/706 and `:505-513` states their fees are 0. The
weights matter for serialized/CPFP accounting, not for the anchor second-stage
fee, which is already zero. Do not claim a fee effect.

**Fidelity risk.** Low. The constants are literal BOLT 3 values; the only
risk is using them as fee-bearing weights when `htlcSecondStageFee_anchors`
already fixes the fee at 0.

**Type / feasibility.** Additive constants; high feasibility. No existing
theorem weakened.

## 5. Assumptions, counterexamples, and non-vacuity risks

### 5.1 Counterexamples that must be preserved

- `d12_output_ordering_fails`, `d12_zero_value_htlc_emitted`, and
  `d12_cltv_tiebreak_not_recoverable` (`CommitmentGrossNetTargets.lean`
  §8): the legacy `commitmentOutputs` is not unconditionally sorted and loses
  CLTV information. T2/T3 must not “repair” this by changing the legacy list
  in place.
- `wave4_dust_trimming_not_perm`: the legacy list and the trimmed rich list
  are not permutations at zero dust. T3 keeps the no-trim/normal-form
  hypotheses.
- `legacyCoverage_not_preserved_by_net_migration` and
  `legacyCoverage_not_preserved_at_site`: coverage is not preserved by net
  migration without the normal-form premise. T3 must keep `Migrated` /
  `UsesRecordNet` explicit.
- `waveF_f04_counterexample_660` and
  `commitmentPair_conservation_anchors_gap`: the old pair overfunds anchored
  commitments by exactly 660. T1 adds a corrected constructor; it must not
  delete the old gap theorem or restate it as if the old constructor were
  fixed.
- `waveD_d14_step_balance` and the surrounding `Step` limits: no `Step`
  changes balances or adds HTLCs. T4/T6 must not pretend the production
  transition enforces reserve/exposure/funder rules.
- `waveD_d14_exposure_mono_fees`: raising either second-stage fee cannot lower
  exposure. T6 may add a fee-excess term, but must not weaken this monotonicity.
- `weightTargets_serializedWeight_anchor_gap`: `1116 + 172k + 8 = 1124 + 172k`.
  No target may claim 1124 is the literal serialized weight.
- `zeroHtlcCommitment_last_two_anchors`: true under its `toLocal ≠ 0` and
  `toRemote ≠ 0` hypotheses. T2 must not cite it as a universal both-anchor
  claim.

### 5.2 Non-vacuity risks

- **T1:** the affordability hypotheses can be unsatisfiable for small
  balances. The witness uses `fee = 1000` and `50_000` sat per side, so
  `fee + 660 ≤ balance`; the anchor-free specialization must be checked
  definitionally.
- **T2:** the exception branch needs `dustLimitSat > 0` and exactly one output
  absent. With `dustLimitSat = 0` or both outputs absent, the branch is not
  the BOLT 3 case. The witness uses `dustLimitSat = 330`, `toLocalSat = 0`,
  `toRemoteSat = 50_000`.
- **T3:** `NetConsistent` is vacuous under the default
  `netAmountSat := amountSat` whenever the second-stage fee is nonzero. The
  witness must set `netAmountSat = 833` explicitly. This is the single most
  important non-vacuity trap in this lane: a theorem quantified over “any
  `CommitmentTx`” can be true but never exercise the net test if every caller
  leaves the default.
- **T4:** `isFunder` and `zeroFee` are caller-supplied Booleans; the theorem is
  non-vacuous only if both `true`/`false` instances are exhibited. They are
  **not** derived from `Channel`, so T4 does not prove that a real channel
  knows who the funder is.
- **T5:** `outputsSat ≤ fundingSat` is required; without it, `Nat` subtraction
  truncates and the “difference” is not the BOLT 3 difference. The witness
  covers 239/240/1000.
- **T6:** `feeExcessMsat > 0` is required for the strict witness; with
  `feeExcessMsat = 0` the new quantity equals the old lower bound.
- **T7:** the constants are trivially distinct; the only risk is citing them as
  fee-bearing weights when the anchor fee is 0.

### 5.3 No-weakening / no-hidden-assumption audit

| Proposal | Existing theorem at risk | Required treatment |
|---|---|---|
| T1 promotes `commitmentPairWithAnchorDebit` | `commitmentPair_fee_owner_local/remote`, `commitmentPair_output_values_swap`, `commitmentPair_conservation_noAnchors`, `commitmentPair_conservation_anchors_gap` | Keep `commitmentPairOfBalances` unchanged. Add the corrected constructor and the anchor-free bridge. A future “canonical swap” must restate the fee-owner theorems with `fee + anchorDebit` in a separate audited change. |
| T2 adds `anchorPresence` | `outputs_spec`, `nonAnchor_output_value_ge_dust`, `zeroHtlcCommitment_last_two_anchors` | Do not alter `localAnchorOutput`/`remoteAnchorOutput` or `outputs`. Prove the new function agrees in the no-exception case. |
| T3 names `output_ordering_net` | `output_ordering`, D12, `wave4_dust_trimming_not_perm`, `legacyCoverage_not_preserved_*` | Keep the gross target as legacy; re-point the catalog and consumer only for the net/BOLT-3 claim. Keep `Perm`, not equality, at the sorted boundary. |
| T4 adds `FeeUpdateCheckedStep` | `Step.updateFee`, all `Step` reachability/existence results | Do not restrict `Step.updateFee` in place. If a later lane does, re-audit the reachable set and state the funder role in `Channel`. |
| T5 adds `ZeroFeeCommitment` | `CommitmentOutput` exhaustive matches, `commitmentOutputs` | Use a standalone structure. Adding a `sharedAnchor` constructor to `CommitmentOutput` is an API-breaking change and must be coordinated, not smuggled into this lane. |
| T6 adds fee excess | `ExposurePolicy`, `dustContribution`, `Reserve.bounds`, `waveD_d14_exposure_mono_fees` | Keep the old lower bound. Treat the fee-excess formula as an explicit external input; do not claim `Step` enforcement. |
| T7 adds anchor weights | `htlcTimeoutWeight`, `htlcSuccessWeight`, `htlcSecondStageFee_anchors` | Keep the no-anchor constants unchanged; state that the anchor fee is still 0. |

The one proposal that would **hide** an assumption if implemented naively is
T3: replacing `output_ordering` with `outputsNet` without a `NetConsistent`
premise would silently assume `net = gross` (or a zero second-stage fee). The
correct shape is the explicit `NetConsistent` hypothesis above. The one
proposal that would **weaken** existing results if implemented carelessly is
T1: changing `commitmentPairOfBalances` globally would falsify the fee-owner
lemmas; the additive constructor is required.

## 6. Wave-13 recommendation

**Implement (safe, additive lane):** T1, T2, T3, and T7.

- T1 is the top priority. It closes a proved contradiction with a small,
  already-mechanized definition and does not touch the canonical constructor.
- T2 is the second priority. It mechanizes `LN-COMMIT-004` and makes the
  single-anchor value/weight accounting exact; keep the old both-anchor
  functions and add the three-way presence function.
- T3 is a catalog and proof-surface correction. The net proofs already exist;
  the work is to make them the named BOLT 3 target, add the identity bridge,
  and re-point `LN-CH-003`/consumer citations. Keep the legacy gross target and
  all D12/no-trim counterexamples.
- T7 is a low-risk constant addition; fold it into the T1/T2 lane if desired.

**Defer pending model/API review:** T4 and T5.

- T4 needs a real funder role and a zero-fee flag in `Channel`, or an explicit
  policy layer. Do not “fix” `Step.updateFee` by adding preconditions without
  auditing reachability and the existing `Step` theorems.
- T5 needs a decision on whether `CommitmentOutput` gains a `sharedAnchor`
  constructor (breaking) or whether the zero-fee model stays standalone. The
  arithmetic is small; the API decision is not.

**Treat as external / human barrier:** anchor reserve and CPFP, fee spikes,
zero-fee version-3/ephemeral-dust relay semantics, and the exact LDK
`current_dust_exposure_msat` fee-excess formula.

- The 25,000-sat reserve, `trusted_peers_no_reserve`, and force-close fee cap
  are LDK node policy (`config.rs:38`, `:452-455`, `:487-490`, `:512-513`;
  `lib.rs:2717-2748`; `types.rs:416-444`), not BOLT arithmetic. A faithful
  theorem would need an on-chain fee/mempool/package-relay model and a
  trusted-peer policy model. Do not encode 25,000 as a protocol constant.
- `CloseChannelRequest` / `ForceCloseChannelRequest` carry no feerate
  (`api.proto:700-721`), so “fee at close” is a broadcast/CPFP policy, not a
  close-call parameter. The model should not add a close feerate field.
- The exact dust-exposure fee-excess formula is only described at the public
  API level (`types.rs:628-638`, `config.rs:809-814`); the pinned clones do
  not expose the internal formula. Keep T6 conditional or defer it.
- Zero-fee commitments are supported but default off (`config.rs:512-513`);
  they are not a P0 compatibility requirement. The P2A/version-3/ephemeral
  dust rules are Bitcoin relay policy, not commitment-value arithmetic.

**Boundary answer.** This lane yields a safe implementation lane for the
anchor-debit and single-anchor value/weight fixes (T1/T2), and a safe
catalog/proof-surface correction for net dust (T3). It does **not** yield a
safe implementation lane for CPFP/anchor-reserve behavior, zero-fee channel
construction, or LDK's exact dust-exposure formula without a human/API decision
and an external chain/fee model.

## 7. Evidence and commands

Read-only inspection performed from `/home/ubuntu/ln-lean-repair`:

```sh
git rev-parse --short HEAD                      # f7f0628
git branch --show-current                        # repair/integrated
git -C /tmp/opencode/ldk-refs/ldk-node rev-parse HEAD
# fa123fed131e27ecc420b77fa7086fcf1ddaebb8
git -C /tmp/opencode/ldk-refs/ldk-server rev-parse HEAD
# c17dc11dde38f88c53457039ddf30c6b90a63ba2
git -C refs/bolts rev-parse --short HEAD        # 1aadb71
rg -n "commitmentOutputs|commitmentPairOfBalances|outputsNet|anchorOutputSat" \
  LnLean/Channel/Commitment.lean LnLean/Channel/Types.lean
rg -n "outputsNet_spec|outputsNet_trims_iff_gross_threshold|NetConsistent" \
  LnLean/Proofs/Channel/CommitmentGrossNetTargets.lean
rg -n "anchorDebitSat|funderDebitSat|commitmentPairWithAnchorDebit|660" \
  LnLean/Proofs/ModelHardening/F04.lean
rg -n "Step.updateFee|checkedFeeUpdate|ExposurePolicy|dustContribution" \
  LnLean/Channel/State.lean LnLean/Proofs/Channel/FeeProps.lean \
  LnLean/Proofs/WaveD/D14.lean
rg -n "DEFAULT_ANCHOR_PER_CHANNEL_RESERVE_SATS|enable_zero_fee_commitments|max_dust_htlc_exposure|force_close_avoidance" \
  /tmp/opencode/ldk-refs/ldk-node/src/config.rs
rg -n "ReserveType|current_dust_exposure_msat|feerate_sat_per_1000_weight" \
  /tmp/opencode/ldk-refs/ldk-node/src/types.rs
rg -n "message CloseChannelRequest|message ForceCloseChannelRequest" \
  -A 12 /tmp/opencode/ldk-refs/ldk-server/ldk-server-grpc/src/proto/api.proto
rg -n "max_dust_htlc_exposure|force_close_avoidance_max_fee_satoshis" \
  /tmp/opencode/ldk-refs/ldk-server/ldk-server-grpc/src/proto/types.proto \
  /tmp/opencode/ldk-refs/ldk-server/ldk-server/src/api/mod.rs
```

Additional exact line anchors used in this report:

- Lean: `LnLean/Channel/Commitment.lean:42`, `:109-114`, `:126-127`,
  `:322-324`, `:380-402`, `:914-922`, `:927-937`, `:951-970`;
  `LnLean/Channel/Types.lean:188-207`, `:209-211`, `:236-256`;
  `LnLean/Channel/State.lean:117-121`;
  `LnLean/Proofs/Channel/CommitmentOrderTargets.lean:89-108`;
  `LnLean/Proofs/Channel/CommitmentGrossNetTargets.lean:110-164`, `:687-721`;
  `LnLean/Proofs/Channel/CommitmentTypesTargets.lean:448`;
  `LnLean/Proofs/Channel/FeeProps.lean:132-180`;
  `LnLean/Proofs/Channel/FeeTargets.lean:206-245`, `:452-478`;
  `LnLean/Proofs/ModelHardening/F04.lean:41-65`, `:222-226`, `:246-313`;
  `LnLean/Proofs/Channel/CommitmentTxProps.lean:435-445`, `:463`;
  `LnLean/Proofs/WaveD/D14.lean:83-90`, `:112-120`, `:406-417`;
  `LnLean/Proofs/Bitcoin/WeightTargets.lean:351-355`;
  `LnLean/Proofs/Channel/CommitmentIntegrationTargets.lean:107-124`.
- BOLT 3: `refs/bolts/03-transactions.md:150-153`, `:178-195`,
  `:305-311`, `:321-326`, `:336-348`, `:464-475`, `:489-498`,
  `:503-513`.
- BOLT 2: `refs/bolts/02-peer-protocol.md:2726-2766`, `:3250-3266`,
  `:3273-3310`.
- LDK Node: `src/config.rs:38`, `:452-455`, `:487-490`, `:491-505`,
  `:510-513`, `:568-571`, `:809-819`, `:859-879`;
  `src/lib.rs:237-247`, `:2717-2748`;
  `src/types.rs:416-444`, `:538-541`, `:618`, `:628-638`.
- LDK Server: `ldk-server-grpc/src/proto/api.proto:700-721`;
  `ldk-server-grpc/src/proto/types.proto:552-554`, `:676-680`,
  `:696-737`; `ldk-server/src/api/close_channel.rs:23-46`;
  `ldk-server/src/api/update_channel_config.rs:22-62`;
  `ldk-server/src/api/mod.rs:96-136`.

No `lake build`, `cargo test`, or network-fetching command was run. No file
outside `agents/reports/wave13-review/R06-commitments-fees-dust-anchors.md`
was created or modified.
