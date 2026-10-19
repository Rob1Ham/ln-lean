# R27 — Anchor channels, zero-fee commitments, and commitment upgrades
**Status:** read-only review
**Pins:** LDK Node `fa123fed131e27ecc420b77fa7086fcf1ddaebb8`, LDK Server `c17dc11dde38f88c53457039ddf30c6b90a63ba2`

Review base: `repair/integrated` at `f7f0628`; BOLTs at
`1aadb719b4007c4cea0ba6e36b08c4fb53788dee`; rust-lightning at
`fe4900930c6bd5786ec4203274d7cf312776a5a6`. No Lean, docs, tests, vendor,
scripts, branches, or other lanes' reports were modified. The only write in
this lane is this file.

## 1. Scope and current Lean surface

This lane covers the negotiation and lifetime of the anchor/zero-fee
commitment format, the format-dependent fee gate, the zero-fee maximum-HLTC
cap, and the boundary between protocol arithmetic and anchor-reserve/CPFP node
policy. It does **not** re-open the P0 anchor-debit or anchor-presence defects:
those are already owned by R06 (`R06-commitments-fees-dust-anchors.md` T1, T2,
and T3), and R06 T5 owns the shared-anchor value arithmetic. R27 adds the
format/feature layer that those targets do not cover.

The catalog rows touched by this surface are:

| Row | Named catalog target(s) | Current reading |
|---|---|---|
| `LN-L1-005` | `LnLean.Bitcoin.anchorValue_eq` | Proved; keyed anchor value is exactly 330 sat. |
| `LN-L1-006` | `LnLean.Proofs.Bitcoin.commitmentBaseWeight_model_target` | Proved; 724/1124 fee basis plus 172 per untrimmed HTLC; the 8 WU serialization gap is explicit. |
| `LN-CH-002` | `LnLean.Channel.Commitment.outputs_nonnegative` | Proved under the BOLT 3 balance equation; D46 keeps the unconditional counterexample. |
| `LN-CH-003` | `output_ordering`, net-migration and consumer targets | Partially covered; the legacy output function is still refuted by D12. |
| `LN-CH-005` | `commitmentSigningGate_rejected_iff_insufficient`; `commitmentSigningGate_rejected_iff_no_checkedSigning` | Exact for the recorded `feeSat` and expected weight; the production `Step` does not carry the gate and the gate has no format argument. |
| `LN-CH-006` | `LnLean.Channel.Reserve.bounds` | Proof-layer policy; `Step` does not enforce it. |
| `LN-CH-007` | `HtlcAggregate` targets | Aggregate second-stage coverage; outside the format-selection question. |

The concrete Lean surface inspected:

- `ChannelParams` (`LnLean/Channel/Types.lean:77-92`) has one format-relevant
  field, `anchorOutputs : Bool` (`:91`). There is no `zeroFee`, `sharedAnchor`,
  `CommitmentFormat`, `channelType`, or `maxAcceptedHtlcs` field. The module
  explicitly lists "zero-fee commitments" as **not modelled**
  (`Types.lean:42-43`).
- `Commitment.commitmentOutputs` (`LnLean/Channel/Commitment.lean:109-114`)
  emits `localAnchor` and `remoteAnchor` together whenever `anchorOutputs =
  true`; `Commitment.anchorOutputValue` is `2 * 330 = 660` in that case
  (`:126-127`). The BOLT 3 single-anchor dust exception is not represented;
  `AnchorProps.lean:70-77` explicitly limits its result to the
  both-outputs-present template.
- `zeroHtlcCommitment` (`Commitment.lean:351-362`) *does* debit the two anchors
  (`toRemoteSat := funding - fee - toLocal - anchorTotal`), but the canonical
  pair constructor does not use it.
- `commitmentPairOfBalances` (`Commitment.lean:380-402`) subtracts only `fee`
  from the funder's output. The checked counterexample is
  `commitmentPair_anchorCounterexample` (`LnLean/Proofs/Conservation.lean:490-497`);
  the general gap is `waveF_f04_legacy_anchor_gap`
  (`LnLean/Proofs/ModelHardening/F04.lean:114-130`) and the refutation is
  `waveF_f04_legacy_anchor_not_conserves` (`:139-178`). The corrected
  `commitmentPairWithAnchorDebit` (`F04.lean:246-271`) has no production
  consumer.
- `commitmentSigningGate` (`LnLean/Proofs/Channel/FeeTargets.lean:206-210`)
  checks `feeSufficient r c.weight (commitmentFeePaidMsat c)` and ignores the
  commitment format. The headline theorem
  `commitmentSigningGate_rejected_iff_insufficient` is at `:225-232`. The only
  zero-fee result is `waveD_d13_zero_rate_sufficient`
  (`LnLean/Proofs/WaveD/D13.lean:377-380`), which covers `r = 0`; there is no
  theorem that exempts a zero-fee *format* from a nonzero nominal rate.
- `Commitment.weight` (`Commitment.lean:323-324`) is
  `commitmentWeight c.anchorOutputs c.htlcs.length`, and
  `commitmentBaseWeight` (`:57-59`) returns 1124 whenever `anchorOutputs =
  true`. It has no format parameter, so it cannot distinguish
  `anchors_zero_fee_htlc_tx` from `zero_fee_commitments`.
- The feature model is `FeatureVector` (`LnLean/Proofs/Protocol/FeaturesProps.lean:133-157`);
  `supports n` is the OR of the two paired bits (`:151-153`).
  `staticRemoteKeyFeature = 6` (`:513`) and `anchorsFeature = 11` (`:516`) map
  to bits 12/13 and 22/23. There is **no** `zero_fee_commitments` feature
  (bits 40/41, feature number 20) and no format selector. `mutualSupport` is
  defined at `:276-278`; BOLT 1's asymmetric `negotiated` rule is at `:287-292`.
  `DependenciesSatisfied` is at `:443-446`.
- `MAX_ACCEPTED_HTLCS : Nat := 483` is defined at
  `LnLean/Channel/HTLC.lean:69` but has no production consumer. `addHTLC`
  (`:343-355`) guards only positive amount, in-flight value, and CLTV; it does
  not count HTLCs and has no format parameter. The wire messages do carry the
  field: `OpenChannelWire.maxAcceptedHtlcs`
  (`LnLean/Protocol/Messages.lean:122`) and
  `AcceptChannel.maxAcceptedHtlcs` (`:151`), but neither is connected to
  `ChannelParams`.
- `Step.updateFee` (`LnLean/Channel/State.lean:117-121`) has only
  `phase = normal` as a premise; it permits a non-funder update and a nonzero
  rate under a zero-fee commitment. `Step` itself (`:86-127`) never changes
  `anchorOutputs` on either endpoint, although it does change `feerate` on the
  local endpoint. `Reachable` is at `:133-137`.
- The only "zero-fee" commitment literal is `zeroHtlcZeroFeeCommitment`
  (`LnLean/Proofs/ProtocolCoverageTargets.lean:457-460`, built with
  `withFormulaFee ⟨0⟩` at `:234`). It is a commitment at feerate zero, not a
  negotiated format or a feature model.
- There is no commitment-format upgrade event, field, or theorem anywhere in
  `LnLean/Channel`, `LnLean/Protocol`, or `LnLean/Proofs/Channel`. The only
  occurrences of "upgrade" in `LnLean` are unrelated proof comments
  (`SighashViewBindingTargets.lean:333`, `StateMachineProps.lean:329`,
  `EcdsaConcreteTargets.lean:614`).

## 2. LDK datapoints (with `file:line`)

### 2.1 Anchor channels, reserve, and CPFP

- The per-channel anchor reserve is 25,000 sat:
  `ldk-node/src/config.rs:38`
  (`DEFAULT_ANCHOR_PER_CHANNEL_RESERVE_SATS = 25_000`).
- The reserve is an emergency reserve for spending anchor outputs and HTLC
  transactions after closure; it may or may not suffice depending on the fee
  market (`config.rs:472-490`). The `AnchorChannelsConfig` defaults are
  `trusted_peers_no_reserve = []`, `per_channel_reserve_sats = 25000`, and
  `enable_zero_fee_commitments = false` (`:509-514`).
- The total reserve counts anchor-type channels (or channels whose negotiated
  type is not yet known, because the filter defaults `None` to true), excluding
  trusted peers and channels whose shutdown is complete:
  `ldk-node/src/lib.rs:2717-2734` (`total_anchor_channels_reserve_sats`),
  using `requires_anchor_channel_type` (`:245-247`). A new channel's reserve is
  zero for non-anchor channels and for trusted peers, otherwise the configured
  per-channel amount (`:2736-2748`).
- Opening checks `amount + reserve <= spendable`:
  `lib.rs:1510-1545` (`check_sufficient_onchain_funds`), with the reserve
  computed at `:1500-1507` and the new-channel path at `:1530-1538`.
- The reserve/CPFP behavior is classified as `ReserveType::Adaptive`,
  `TrustedPeersNoReserve`, or `Legacy`
  (`ldk-node/src/types.rs:411-444`). `Adaptive` says the commitment fee may be
  insufficient and the broadcaster supplies additional funds via CPFP;
  `Legacy` says commitment fees were pre-committed at open. `ChannelDetails`
  exposes both `reserve_type` and the negotiated `channel_type`
  (`types.rs:615-623`), but only as read-only data.
- At close, LDK Node handles `BumpTransactionEvent::ChannelClose` and skips the
  bump for trusted peers (`ldk-node/src/event.rs:2389-2410`). The close and
  force-close RPCs carry no feerate:
  `ldk-server-grpc/src/api.rs:949-960` (`CloseChannelRequest` has only
  `user_channel_id` and `counterparty_node_id`) and `:971-985`
  (`ForceCloseChannelRequest` adds only `force_close_reason`); handlers at
  `ldk-server/src/api/close_channel.rs:23-44` pass only those fields.
- A separate force-close fee cap exists:
  `ldk-server/src/api/mod.rs:131-135` reads
  `force_close_avoidance_max_fee_satoshis`; the field is exposed in
  `ldk-server-grpc/src/types.rs:830-832`. This is not a close feerate.
- LDK Server mirrors the reservation state as data:
  `ldk-server-grpc/src/types.rs:1770-1783` (`ReserveType`) and
  `ldk-server-grpc/src/api.rs:1319-1331` (`GetBalancesResponse` exposes
  `total_anchor_channels_reserve_sats`).

### 2.2 Zero-fee configuration and feature negotiation

- Zero-fee commitments are opt-in and default to `false`:
  `ldk-node/src/config.rs:505` (field), `:509-514` (default). The field's
  documentation states the preference order: first
  `option_zero_fee_commitments`, then `option_anchors_zero_fee_htlc_tx`, then
  `option_static_remotekey`, as supported by the peer (`:491-505`). It also
  states that zero-fee channels remove commitment-feerate negotiation entirely
  and source confirmation fees from the closer's anchor reserve.
- The flag is wired into the handshake config:
  `config.rs:568-571`
  (`negotiate_anchor_zero_fee_commitments =
  enable_zero_fee_commitments`).
- Peer-type selection is conditional on advertised support:
  `ldk-node/src/lib.rs:237-243`
  (`supports_anchors_zero_fee_htlc_tx()` or, if enabled,
  `supports_anchor_zero_fee_commitments()`), and channel-type detection is
  `:245-247`.
- When zero-fee is enabled, or any live monitor/manager owns a zero-fee
  channel, the chain source must support package submission, TRUC, P2A, and
  ephemeral dust: `lib.rs:336-360` (`zero_fee_commitments_support_required`),
  `:388-395` (passing it into `initialize_wallets`), and
  `ldk-node/src/chain/mod.rs:646-664`
  (`validate_zero_fee_commitments_support_if_required`). The Bitcoin Core
  backend requires v29 or newer:
  `ldk-node/src/chain/bitcoind.rs:233-254`, specifically `:249-254`.
- LDK Server exposes only a node-level zero-fee switch:
  `ldk-server/src/util/config.rs:80` (field), `:200-201` (merge),
  `:354-355` (CLI), `:740` (default `false`), and `:1316-1319`
  (`LDK_SERVER_NODE_ENABLE_ZERO_FEE_COMMITMENTS`); `ldk-server/src/main.rs:160-161`
  copies it into `ldk_node_config.anchor_channels_config`.
- The server's open request has **no** channel-type/format field:
  `ldk-server-grpc/src/api.rs:767-806`. Its `channel_config` is
  `ldk_server_grpc::types::ChannelConfig` (forwarding, CLTV, dust, force-close
  avoidance; `types.rs:812-832`), not `ChannelTypeFeatures`. The amount oneof
  only distinguishes an exact amount from "all funds" (`api.rs:808-820`).
- The server's update request changes only `ChannelConfig`:
  `ldk-server-grpc/src/api.rs:924-934`; the handler
  `ldk-server/src/api/update_channel_config.rs:22-62` builds a new
  `ChannelConfig` and calls `update_channel_config`. It has no format or
  channel-type mutator.
- The negotiated channel type is exposed read-only:
  `ldk-server/src/util/proto_adapter.rs:90-96` converts
  `ChannelDetails.channel_type` into proto features, and `:150` writes it into
  the response. This is a report field, not an input.

### 2.3 Close paths and the absence of an in-place upgrade

- `CloseChannelRequest` and `ForceCloseChannelRequest` carry no commitment
  format, feerate, or channel-type field
  (`ldk-server-grpc/src/api.rs:949-960`, `:971-985`). The handlers
  (`ldk-server/src/api/close_channel.rs:23-44`) call `close_channel` or
  `force_close_channel` with only the identifiers and reason.
- `OpenChannelRequest` has no format field (`api.rs:767-806`), and
  `UpdateChannelConfigRequest` has no format field (`:924-934`). Combined with
  the read-only `ChannelDetails.channel_type` (`ldk-node/src/types.rs:619-623`;
  server adapter `:90-96`), the public LDK Node/Server surface exposes **no
  in-place commitment-format upgrade**. A different format means a new
  channel; the negotiated type is fixed for the channel's lifetime by BOLT 2
  (`refs/bolts/02-peer-protocol.md:1043-1044`).

### 2.4 BOLT semantics used below

- Both peers MUST use the negotiated `channel_type` for all commitment
  transactions (`refs/bolts/02-peer-protocol.md:1025`), and it determines the
  format for the channel's total lifetime (`:1043-1044`). The defined basic types
  are `option_static_remotekey` (bit 12), `option_anchors` plus static
  remotekey (bits 22 and 12), and `zero_fee_commitments` (bit 40)
  (`:786-793`).
- For zero-fee, `open_channel` MUST set `feerate_per_kw` to 0 (`:823-824`),
  and the receiver MUST fail if `max_accepted_htlcs > 114` or
  `feerate_per_kw != 0`; without zero-fee the cap is 483 (`:861-865`). The
  rationale is the v3 10kvB limit and the 483 message-size/penalty bound
  (`:2888-2895`).
- `update_fee` is sent only by the fee payer; under zero-fee, nodes MUST NOT
  send it and the receiver MUST fail the channel (`:3252-3253`, `:3275-3283`,
  `:3298-3299`).
- BOLT 3's shared anchor is P2A `OP_1 <0x4e73>` with standard dust 240 sat;
  if input minus other outputs is below 240, the anchor takes that value and
  the commitment pays no fee; otherwise the anchor is 240 and the remainder is
  fee (`refs/bolts/03-transactions.md:178-195`). Trimmed value goes to the
  shared anchor under zero-fee (`:305-311`). The feerate is 0 under zero-fee
  (`:471`), the base fee MUST be 0 (`:519`), and the shared-anchor amount is
  taken from trimmed outputs (`:563-570`).
- BOLT 9 assigns `option_anchors` to bits 22/23 (`refs/bolts/09-features.md:45`)
  and `zero_fee_commitments` to bits 40/41 with dependency
  `option_channel_type` (`:52`, `:73-74`).
- rust-lightning corroborates the client behavior: `max_htlcs` is 114 only
  for `supports_anchor_zero_fee_commitments()` and 483 otherwise
  (`refs/rust-lightning/lightning/src/ln/chan_utils.rs:63-70`);
  `commitment_tx_base_weight` returns 1124 only for
  `supports_anchors_zero_fee_htlc_tx()` and 724 otherwise (`:280-283`);
  `selected_commitment_sat_per_1000_weight` returns 0 for
  `supports_anchor_zero_fee_commitments()` (`:323-334`); and
  `second_stage_tx_fees_sat` returns `(0, 0)` for both anchor variants
  (`:297-312`).

## 3. Gap matrix

| Behavior | Lean status | LDK evidence | Gap / counterexample | Priority |
|---|---|---|---|---|
| Keyed anchor value is exactly 330 sat | **covered faithfully** | `AnchorProps.lean:189`; `Seam.lean:127`; catalog `LN-L1-005` | No gap. `anchor_deduction_two` (`AnchorProps.lean:390-395`) composes it for two anchors. | none |
| Both keyed anchors are present, with the BOLT 3 single-anchor dust exception | **partially covered** | `Commitment.lean:109-114`; BOLT 3 `03-transactions.md:150-153`; `AnchorProps.lean:70-77` | `commitmentOutputs` emits both anchors whenever `anchorOutputs = true`; with `toLocalSat = 0`, `toRemoteSat = 50_000`, no HTLCs, dust 330, BOLT emits one anchor (330), the model emits two (660). R06 T2 owns this; do not duplicate. | R06 P0 |
| Funder pays the two 330-sat anchors on both commitments | **contradicted** | `Commitment.lean:380-402`; `Conservation.lean:490-497`; `F04.lean:114-130`, `:139-178`; BOLT 3 `:321-326` | `commitmentPairOfBalances` subtracts only `fee`; output sum plus fee exceeds funding by 660. `commitmentPairWithAnchorDebit` (`F04.lean:246-271`) is correct but unused. R06 T1 owns this. | R06 P0 |
| Shared anchor P2A output and `min(240, input - outputs)` | **missing** | BOLT 3 `03-transactions.md:178-195`, `:305-311`; `Commitment.lean:42`; `AnchorProps.lean:74-77` | No `sharedAnchor` output kind, no P2A script, no 240-sat rule, no redirection of trimmed value. R06 T5 owns the value arithmetic; R27 does not duplicate it. | R06 P1 |
| Zero-fee format exempts the commitment base fee at a nonzero nominal rate | **partially covered** | `FeeTargets.lean:206-210`; `D13.lean:377-380`; BOLT 3 `:471`, `:519`; BOLT 2 `:823-824` | The gate is format-blind; `feeSat = 0` at `r > 0` is rejected even when the negotiated format is zero-fee. The only zero-fee result is at `r = 0`. R27 T2. | P1 |
| Zero-fee commitment weight is 724, not the keyed-anchor 1124 | **partially covered** | `Commitment.lean:323-324`, `:57-59`; LDK `chan_utils.rs:280-283`, `:323-334`; BOLT 3 `:491-494` | `Commitment.weight` keys only on `anchorOutputs`, so a zero-fee commitment with anchors is weighed as 1124 even though LDK selects the 724 base for 0FC. This overstates the fee basis and any CPFP/weight accounting. R27 T3. | P2 |
| Three feature pairs (40/41, 22/23, 12/13) with legacy fallback | **missing** | `FeaturesProps.lean:513-516`, `:151-153`; `config.rs:491-505`; BOLT 9 `09-features.md:45`, `:52`; BOLT 2 `:786-793` | No zero-fee feature constant, no `CommitmentFormat`, no two-peer selector, and no theorem that the selected format is the one both peers support. `commitmentTemplate` is one-peer and has no 0FC branch. R27 T1. | P1 |
| `zero_fee_commitments` requires `option_channel_type` | **missing** | BOLT 9 `09-features.md:52`, `:73-74`; `FeaturesProps.lean:443-446` | The dependency table is not instantiated; even after adding feature 20, nothing forces feature 22 (`option_channel_type`) support. R27 T1 dependency theorem. | P1 |
| Maximum accepted HTLCs: 114 for zero-fee, 483 otherwise | **missing** | `HTLC.lean:69`; `Messages.lean:122`, `:151`; BOLT 2 `:861-865`, `:2888-2895`; LDK `chan_utils.rs:63-70` | `MAX_ACCEPTED_HTLCS` is 483 and unused; `addHTLC` does not count records and has no format parameter; the wire field is not connected to `ChannelParams`. R27 T4. | P2 |
| `update_fee` is forbidden under zero-fee and from the non-funder | **contradicted** | `State.lean:117-121`; BOLT 2 `:3252-3253`, `:3275-3283` | `Step.updateFee` accepts any sender and any rate; there is no zero-fee guard. Counterexample: for any normal-phase `c`, `Step.updateFee c h r` with `r ≠ 0` is derivable, and `Step` has no zero-fee or fee-payer premise. R06 T4 owns the checked relation; R27 records the contradiction and does not duplicate it. | R06 P1 |
| Commitment format is fixed for the channel's lifetime; no in-place upgrade | **partially covered** | `State.lean:86-127`; `types.rs:619-623`; server `api.rs:767-806`, `:924-934`, `:949-985`; BOLT 2 `:1043-1044` | `Step` preserves `anchorOutputs` but there is no format field to preserve, and `updateFee` changes the feerate. LDK exposes no format mutator, so an in-place upgrade is absent by construction. R27 T5 proves the modeled invariant only. | P2 |
| Anchor reserve, CPFP, package relay, fee spikes | **unmodelled / external** | `config.rs:38`, `:472-514`; `lib.rs:2717-2748`, `:1510-1545`; `types.rs:411-444`; `event.rs:2389-2410`; BOLT 3 `:178-195` | No 25,000-sat reserve, no trusted-peer exclusion, no CPFP bump event, no package/TRUC/ephemeral-dust model, no close feerate. This is node policy plus mempool/package relay, not a BOLT arithmetic rule. R27 T6 is explicitly non-protocol. | P2 (external) |
| `1124` fee basis vs `1116 + 8` serialized weight | **covered faithfully** | `WeightTargets.lean:351-355`; `H33.lean:528-534`; BOLT 3 `:491-494` | The 8 WU gap is explicit in `weightTargets_serializedWeight_anchor_gap`; `anchor_literal_weight_neq_fee_basis` refutes the literal reading. No new target; do not let T3 redefine 1124 as a serialized weight. | none |

## 4. Proposed targets

Six targets are proposed. All are additive. T1–T5 are proof-layer model
extensions; T6 is a policy arithmetic target that must remain explicitly
external to the protocol development. No target changes
`commitmentPairOfBalances`, `commitmentOutputs`, `Commitment.weight`,
`Step.updateFee`, or `MAX_ACCEPTED_HTLCS` in place. The code blocks below are
proposed statement shapes, not compiled declarations.

### T1 — Four-way commitment-format selection (P1)

**Fully-qualified name:**
`LnLean.Proofs.Channel.CommitmentFormatTargets.selectCommitmentFormat_eq_zeroFee_iff`

Add a shared proof-layer module (suggested:
`LnLean/Proofs/Channel/CommitmentFormatTargets.lean`) with:

```lean
inductive CommitmentFormat where
  | legacy
  | staticRemoteKey
  | anchorsZeroFeeHtlc
  | zeroFee
  deriving Repr, DecidableEq, BEq

def zeroFeeCommitmentsFeature : Nat := 20   -- bits 40/41
def channelTypeFeature : Nat := 22          -- bits 44/45

def featureDependencies : Nat → List Nat
  | 20 => [22]   -- zero_fee_commitments -> option_channel_type
  | 11 => [6]    -- option_anchors -> option_static_remotekey
  | _  => []

/-- Both peers support the feature.  This is deliberately `mutualSupport`,
not BOLT 1's asymmetric `negotiated` rule.  `allowZeroFee` is the local
`enable_zero_fee_commitments` policy, not a peer feature. -/
def selectCommitmentFormat (allowZeroFee : Bool) (lcl rmt : FeatureVector) :
    CommitmentFormat :=
  if allowZeroFee && mutualSupport lcl rmt zeroFeeCommitmentsFeature then .zeroFee
  else if mutualSupport lcl rmt anchorsFeature then .anchorsZeroFeeHtlc
  else if mutualSupport lcl rmt staticRemoteKeyFeature then .staticRemoteKey
  else .legacy

theorem selectCommitmentFormat_eq_zeroFee_iff
    (allowZeroFee : Bool) (lcl rmt : FeatureVector)
    (henabled : allowZeroFee = true) :
    selectCommitmentFormat allowZeroFee lcl rmt = .zeroFee ↔
      mutualSupport lcl rmt zeroFeeCommitmentsFeature = true

theorem selectCommitmentFormat_no_zeroFee
    (allowZeroFee : Bool) (lcl rmt : FeatureVector)
    (hdisabled : allowZeroFee = false) :
    selectCommitmentFormat allowZeroFee lcl rmt ≠ .zeroFee

theorem selectCommitmentFormat_eq_anchors_iff
    (allowZeroFee : Bool) (lcl rmt : FeatureVector)
    (h0 : mutualSupport lcl rmt zeroFeeCommitmentsFeature = false) :
    selectCommitmentFormat allowZeroFee lcl rmt = .anchorsZeroFeeHtlc ↔
      mutualSupport lcl rmt anchorsFeature = true

theorem selectCommitmentFormat_eq_staticRemoteKey_iff
    (allowZeroFee : Bool) (lcl rmt : FeatureVector)
    (h0 : mutualSupport lcl rmt zeroFeeCommitmentsFeature = false)
    (ha : mutualSupport lcl rmt anchorsFeature = false) :
    selectCommitmentFormat allowZeroFee lcl rmt = .staticRemoteKey ↔
      mutualSupport lcl rmt staticRemoteKeyFeature = true

theorem zeroFee_selection_implies_channelType
    (allowZeroFee : Bool) (lcl rmt : FeatureVector)
    (henabled : allowZeroFee = true)
    (hl : DependenciesSatisfied featureDependencies lcl)
    (hr : DependenciesSatisfied featureDependencies rmt)
    (h : selectCommitmentFormat allowZeroFee lcl rmt = .zeroFee) :
    lcl.supports channelTypeFeature = true ∧
      rmt.supports channelTypeFeature = true
```

**Hypotheses.** The zero-fee iff carries the local policy premise
`henabled : allowZeroFee = true`; without it the stated iff is false, because
`allowZeroFee = false` with mutual support for feature 20 makes the left side
false and the right side true. The anchor/static iffs carry the explicit
exclusion of the higher-priority feature; without those premises the iff is
false. The dependency theorem takes the concrete dependency table, the local
policy premise, and `DependenciesSatisfied` for both peers. The table is a
modeling choice: `option_channel_type` is `ASSUMED` in BOLT 9, so the table
is not a BOLT theorem.

**Non-vacuity witness.** Start from `emptyVector`
(`FeaturesProps.lean:326-329`) and use `setRequired` (`:597-604`). With
`allowZeroFee := true`, `lcl = rmt = setRequired (setRequired emptyVector 20) 11`
selects `.zeroFee`. Removing feature 20 from `rmt` selects
`.anchorsZeroFeeHtlc` (both still support 11). Removing 11 as well but setting
6 on both selects `.staticRemoteKey`. With none of 20, 11, 6 supported, the
result is `.legacy`. Thus all four branches are reachable. With
`allowZeroFee := false` and the same feature vectors,
`selectCommitmentFormat_no_zeroFee` shows the 0FC branch is unreachable even
when both peers advertise feature 20.

**Why faithful.** BOLT 9 puts `option_anchors` at bits 22/23 and
`zero_fee_commitments` at bits 40/41; BOLT 2 defines the corresponding basic
channel types (`02-peer-protocol.md:786-793`). LDK Node documents exactly the
precedence in `config.rs:491-495`. The selector uses `mutualSupport`, which is
the right "both peers support" test for a channel type, rather than the
asymmetric `negotiated` rule.

**Fidelity risk.** Medium-low. The precedence order is LDK Node policy, not a
BOLT-mandated ordering; the theorem proves what the model selects, not what
the peer actually sent on the wire. `allowZeroFee` models LDK Node's
`enable_zero_fee_commitments` opt-in (`config.rs:505`, `:509-514`), and the
zero-fee theorem must keep `henabled`; dropping it would hide the local policy
assumption and would make the model select 0FC from peer support alone.
`supports` collapses required and optional bits, so the model cannot
distinguish "both required" from "one required, one optional"; that is
acceptable for `channel_type`, which is a set of supported features. The
dependency table is a modeling assumption and must be named as such. The
selector itself does not check feature 22; `zeroFee_selection_implies_channelType`
only concludes it under `DependenciesSatisfied` for both peers, so a
production selector must either check the dependency or carry that
hypothesis.

**Type / feasibility.** Model extension, additive; high feasibility (new
definitions plus `by_cases`/`simp` proofs). Do not modify `FeatureVector`,
`mutualSupport`, or `commitmentTemplate`. The existing
`commitmentTemplate` (`FeaturesProps.lean:529-533`) is a **one-peer**
`to_remote` script gate (anchors over static-remotekey over legacy) and has no
zero-fee branch; T1 is a **two-peer channel-format** selector. The
`.staticRemoteKey` and `.legacy` branches must agree with
`commitmentTemplate` whenever feature 20 is absent, and T1 must not be cited
as replacing the script-template theorem.

### T2 — Format-aware zero-fee fee gate (P1)

**Fully-qualified name:**
`LnLean.Proofs.Channel.ZeroFeeCommitment.zeroFee_gate_accepts_and_legacy_rejects`

Add a wrapper, not a replacement, around the existing gate:

```lean
def commitmentSigningGateFor (format : CommitmentFormat) (r : FeeRate)
    (c : Commitment) : SigningVerdict :=
  match format with
  | .zeroFee => .sign c
  | _ => commitmentSigningGate r c

theorem commitmentSigningGateFor_legacy_eq (r : FeeRate) (c : Commitment) :
    commitmentSigningGateFor .legacy r c = commitmentSigningGate r c := rfl

theorem zeroFee_gate_accepts_and_legacy_rejects
    (r : FeeRate) (c : Commitment)
    (hzero : c.feeSat = 0)
    (hreq : 0 < r.msatPerKw * c.weight.val / 1000) :
    (commitmentSigningGateFor .zeroFee r c).emitsSignature = true ∧
      (commitmentSigningGateFor .legacy r c).emitsSignature = false ∧
      (commitmentSigningGateFor .anchorsZeroFeeHtlc r c).emitsSignature = false
```

**Hypotheses.** `c.feeSat = 0` is the zero-fee commitment condition;
`0 < r.msatPerKw * c.weight.val / 1000` says the legacy required fee is
positive, so the legacy branch really rejects. The `r = 0` case is deliberately
excluded from the discrimination: there the existing
`waveD_d13_zero_rate_sufficient` and `waveD_d13_zero_rate_gate_signs` already
show the legacy gate signs, and T2 must remain consistent with them.

**Non-vacuity witness.** Take
`c := zeroHtlcCommitment .local 0 100_000 50_000 0 144 false`
(`Commitment.lean:351-362`), so `c.feeSat = 0` and `c.weight.val = 724`.
With `r = ⟨253⟩`, `253 * 724 / 1000 = 183 > 0`: the zero-fee format signs,
while the legacy and keyed-anchor formats reject. With `r = ⟨0⟩`, the legacy
gate signs, matching the existing D13 theorem.

**Why faithful.** BOLT 3 says the base commitment fee MUST be 0 when
`zero_fee_commitments` applies (`03-transactions.md:519`) and the feerate is 0
(`:471`); BOLT 2 requires `feerate_per_kw = 0` at open (`02-peer-protocol.md:823-824`).
A zero-fee format therefore has no base-fee rejection. The wrapper is exactly
that exemption for the base-fee gate. It does not claim signature validity,
relay validity, or a valid v3/P2A transaction.

**Fidelity risk.** Medium. The `.zeroFee => .sign c` branch is unconditional
in `r`; it must be scoped as "the base-fee gate is exempt", not "the
commitment is valid at any feerate." The separate open-channel rule
`feerate_per_kw = 0` is not enforced by this gate. The branch also does not
check that the commitment actually carries a shared anchor or a zero fee
(`hzero` is a theorem hypothesis, not a gate check); a production caller must
establish it.

**Type / feasibility.** Model extension, additive; high feasibility. **Do not**
change `commitmentSigningGate`: that would make the checked theorem
`commitmentSigningGate_rejected_iff_insufficient`
(`FeeTargets.lean:225-232`) false at `feeSat = 0`, `r > 0`, and would weaken
`LN-CH-005`. The wrapper plus the legacy-equality lemma is the safe extension.

### T3 — Format-aware commitment base weight (P2)

**Fully-qualified name:**
`LnLean.Proofs.Channel.CommitmentFormatTargets.commitmentWeightFor_eq`

Add an additive weight function; leave `Commitment.weight` unchanged:

```lean
def commitmentBaseWeightFor : CommitmentFormat → Nat
  | .anchorsZeroFeeHtlc => 1124
  | _ => 724

def commitmentWeightFor (format : CommitmentFormat) (numHtlcs : Nat) : Weight :=
  ⟨commitmentBaseWeightFor format + commitmentHtlcWeight * numHtlcs⟩

theorem commitmentWeightFor_eq (format : CommitmentFormat) (numHtlcs : Nat) :
    (commitmentWeightFor format numHtlcs).val =
      (if format = .anchorsZeroFeeHtlc then 1124 else 724) +
        commitmentHtlcWeight * numHtlcs

theorem commitmentWeightFor_anchors_eq (numHtlcs : Nat) :
    commitmentWeightFor .anchorsZeroFeeHtlc numHtlcs =
      commitmentWeight true numHtlcs

theorem commitmentWeightFor_zeroFee_eq_724 (numHtlcs : Nat) :
    commitmentWeightFor .zeroFee numHtlcs =
      ⟨724 + commitmentHtlcWeight * numHtlcs⟩

theorem zeroFee_weight_ne_keyedAnchor (numHtlcs : Nat) :
    commitmentWeightFor .zeroFee numHtlcs ≠
      commitmentWeight true numHtlcs
```

**Hypotheses.** None for the arithmetic. The `format` argument is trusted: a
caller must establish it through T1 (or an equivalent negotiated-format
witness), not infer it from `anchorOutputs`. The 724 choice for `.zeroFee` is
an implementation-derived assumption, not a BOLT 3 literal: BOLT 3's expected
weight table only distinguishes "no `option_anchors`" (724) from
"`option_anchors`" (1124), while zero-fee is a separate channel type.

**Non-vacuity witness.** `numHtlcs = 0`: `commitmentWeightFor .zeroFee 0 =
724`, while `commitmentWeight true 0 = 1124`; the theorem
`zeroFee_weight_ne_keyedAnchor 0` is a checked inequality. `numHtlcs = 2`
gives 1068 vs 1468 (with `commitmentHtlcWeight = 172`).

**Why faithful (conditionally).** LDK's
`commitment_tx_base_weight` returns 1124 only for
`supports_anchors_zero_fee_htlc_tx()` and 724 otherwise
(`refs/rust-lightning/lightning/src/ln/chan_utils.rs:280-283`); its
`selected_commitment_sat_per_1000_weight` returns 0 for zero-fee (`:323-334`).
BOLT 3 does not give a separate zero-fee expected-weight line, so the 724
choice is a pinned-implementation compatibility assumption. The theorem must
not be cited as a BOLT 3 constant.

**Fidelity risk.** Medium-high. The real zero-fee commitment has a P2A shared
anchor and v3 rules that the 724 base weight may not fully account for; the
target is a model-extension arithmetic target, not a serialized-weight proof.
It also must not disturb `weightTargets_serializedWeight_anchor_gap` or
`anchor_literal_weight_neq_fee_basis`.

**Type / feasibility.** Model extension plus an explicit
implementation/external assumption for the 724 zero-fee choice; high
arithmetic feasibility, medium fidelity. Do not change `commitmentBaseWeight`
or `Commitment.weight` in place; many existing theorems depend on the
`anchorOutputs`-only signature.

### T4 — Maximum accepted HTLCs: 114/483 (P2)

**Fully-qualified name:**
`LnLean.Proofs.Channel.ZeroFeeCommitment.maxAcceptedHtlcsFor_eq`

```lean
def maxAcceptedHtlcsFor : CommitmentFormat → Nat
  | .zeroFee => 114
  | _ => 483

theorem maxAcceptedHtlcsFor_eq (format : CommitmentFormat) :
    maxAcceptedHtlcsFor format =
      if format = .zeroFee then 114 else 483

def MaxAcceptedHtlcsBound (format : CommitmentFormat) (n : Nat) : Prop :=
  n ≤ maxAcceptedHtlcsFor format

theorem maxAcceptedHtlcsBound_zeroFee_iff (n : Nat) :
    MaxAcceptedHtlcsBound .zeroFee n ↔ n ≤ 114
theorem maxAcceptedHtlcsBound_legacy_iff (n : Nat) :
    MaxAcceptedHtlcsBound .legacy n ↔ n ≤ 483

theorem acceptChannel_rejects_over_format_cap
    (format : CommitmentFormat) (m : AcceptChannel)
    (h : maxAcceptedHtlcsFor format < m.maxAcceptedHtlcs) :
    ¬ MaxAcceptedHtlcsBound format m.maxAcceptedHtlcs
```

**Hypotheses.** None for the arithmetic; `m` is a decoded `AcceptChannel`
(`Messages.lean:143-157`), and `format` is a trusted caller argument (T1
supplies the negotiated format). The same predicate applies to
`OpenChannelWire.maxAcceptedHtlcs` (`:122`). The cap is a message-field bound, not
a `ChannelParams` or `Step` invariant, because neither stores the negotiated
cap and `addHTLC` does not count records.

**Non-vacuity witness.** `format = .zeroFee` accepts 114 and rejects 115;
`format = .anchorsZeroFeeHtlc` accepts 483 and rejects 484. The existing
`MAX_ACCEPTED_HTLCS = 483` remains the legacy constant. An
`AcceptChannel` with `maxAcceptedHtlcs := 115` and `format = .zeroFee` is
rejected by `acceptChannel_rejects_over_format_cap`.

**Why faithful.** BOLT 2 is literal: if `channel_type` includes
`zero_fee_commitments`, the receiver MUST fail when `max_accepted_htlcs > 114`
or `feerate_per_kw != 0`; otherwise it MUST fail above 483
(`02-peer-protocol.md:861-865`). LDK corroborates 114/483
(`chan_utils.rs:63-70`). The rationale is the v3 10kvB limit
(`02-peer-protocol.md:2888-2895`).

**Fidelity risk.** Low for the arithmetic; medium for scope. The 114-vs-483
split is exact, but the theorem does not prove the v3 10kvB bound, does not
connect the cap to `addHTLC`, and does not enforce it in `Step`. The `AcceptChannel`
record is a wire record; a decoded message can still carry an over-cap value
and the predicate is the rejection condition.

**Type / feasibility.** Model extension, additive; high feasibility. Do not
replace `MAX_ACCEPTED_HTLCS` with 114 or change `addHTLC`'s signature in this
lane.

### T5 — Anchor format is preserved by the modeled transition relation (P2)

**Fully-qualified name:**
`LnLean.Proofs.Channel.CommitmentFormatTargets.step_preserves_anchorOutputs`

```lean
theorem step_preserves_anchorOutputs {c c' : Channel} {e : ProtocolEvent}
    (h : Step c e c') :
    c'.localEndpoint.params.anchorOutputs =
        c.localEndpoint.params.anchorOutputs ∧
      c'.remoteEndpoint.params.anchorOutputs =
        c.remoteEndpoint.params.anchorOutputs := by
  cases h <;> simp [ChannelParams.anchorOutputs]

theorem Reachable.anchorOutputs_eq {a b : Channel} (h : Reachable a b) :
    b.localEndpoint.params.anchorOutputs =
        a.localEndpoint.params.anchorOutputs ∧
      b.remoteEndpoint.params.anchorOutputs =
        a.remoteEndpoint.params.anchorOutputs := by
  induction h with
  | refl => exact ⟨rfl, rfl⟩
  | step _ hs ih =>
      exact ⟨(step_preserves_anchorOutputs hs).1.trans ih.1,
             (step_preserves_anchorOutputs hs).2.trans ih.2⟩
```

**Hypotheses.** None; the proof is a case split on `Step`. The theorem is
about the two endpoint flags separately because the endpoints may disagree in
the model (as they can in `commitmentPairOfBalances`).

**Non-vacuity witness.** `Step.updateFee c h r` changes the local feerate but
preserves both anchor bits; a reachable sequence
`openChannel → fundingCreated → fundingSigned → fundingLocked →
updateFee` reaches a normal-phase channel with the same anchor flags. A
counterexample to the stronger claim: `Step.updateFee` changes
`localEndpoint.params.feerate`, so `Step` does **not** preserve the whole
`ChannelParams` record.

**Why faithful (scope-limited).** BOLT 2 says the negotiated `channel_type`
determines the commitment format for the total lifetime of the channel
(`02-peer-protocol.md:1043-1044`), and both peers must use it for all commitments
(`:1025`). `anchorOutputs` is the only format bit in the current model, so its
invariance is the model-level shadow of that rule. LDK Node/Server expose the
negotiated type only as read-only data and provide no mutator
(`ldk-node/src/types.rs:619-623`; `ldk-server/src/util/proto_adapter.rs:90-96`,
`:150`; `ldk-server-grpc/src/api.rs:924-934`).

**Fidelity risk.** Medium-high. The model has no `CommitmentFormat` or
`zeroFee` field, so this theorem does **not** prove the full lifetime rule for
zero-fee commitments, and it does not forbid `update_fee` under zero-fee
(that is R06 T4). It also does not create an upgrade event; the absence of
such an event is a separate model fact. Do not state "no in-place 0FC upgrade
is proved" from T5 alone.

**Type / feasibility.** Proof-layer theorem, no model extension; high
feasibility. It is a corollary of the existing `Step` cases, not a change to
`Step`.

### T6 — Anchor reserve policy arithmetic (P2, external/non-protocol)

**Fully-qualified name:**
`LnLean.Proofs.Channel.AnchorReservePolicy.totalAnchorReserve_eq`

This is an optional policy module, not a protocol target:

```lean
structure AnchorReserveChannel where
  isAnchor : Bool
  isTrusted : Bool
  isShutdownComplete : Bool

def totalAnchorReserve (perChannel : Nat)
    (cs : List AnchorReserveChannel) : Nat :=
  perChannel * (cs.filter (fun c =>
    c.isAnchor && !c.isTrusted && !c.isShutdownComplete)).length

theorem totalAnchorReserve_eq (perChannel : Nat)
    (cs : List AnchorReserveChannel) :
    totalAnchorReserve perChannel cs =
      perChannel * (cs.filter (fun c =>
        c.isAnchor && !c.isTrusted && !c.isShutdownComplete)).length

theorem newChannelReserve_eq (perChannel : Nat) (isAnchor isTrusted : Bool) :
    (if isAnchor && !isTrusted then perChannel else 0) =
      (if isAnchor then (if isTrusted then 0 else perChannel) else 0)
```

**Hypotheses.** `perChannel` is the configured reserve (25,000 sat by
default); `isAnchor`, `isTrusted`, and `isShutdownComplete` are caller-supplied
classifications. The channel-type `None` case and the exact LDK shutdown-state
semantics are not modeled.

**Non-vacuity witness.** Three channels: one untrusted live anchor, one
trusted anchor, one legacy; the reserve is `25_000`. A shutdown-complete anchor
is excluded; a trusted anchor contributes 0. The new-channel lemma gives
25,000 for an untrusted anchor and 0 for a trusted or non-anchor channel.

**Why faithful (conditionally).** LDK Node's
`total_anchor_channels_reserve_sats` filters trusted peers, shutdown-complete
channels, and non-anchor channel types, then multiplies the count by the
per-channel reserve (`lib.rs:2717-2734`); `new_channel_anchor_reserve_sats`
returns 0 for non-anchor and trusted peers (`:2736-2748`). The default is
25,000 (`config.rs:38`, `:509-514`). This is **node policy**, not a BOLT
arithmetic rule. CPFP, package relay, TRUC, P2A, ephemeral dust, and the fee
market remain external.

**Fidelity risk.** Medium-high. The simplification of `channel_type = None`
to a Boolean and the omission of the live-monitor/splicing states mean this is
not the LDK function. It must never be cited as a protocol theorem or used to
satisfy a `LN-*` claim.

**Type / feasibility.** External assumption/policy model; high arithmetic
feasibility, low protocol value. Recommend keeping it out of the protocol
module and, if implemented, placing it in a clearly named policy module.

## 5. Assumptions, counterexamples, and non-vacuity risks

### 5.1 Counterexamples and theorems that must be preserved

- `commitmentPair_anchorCounterexample` (`Conservation.lean:490-497`),
  `waveF_f04_legacy_anchor_gap` / `waveF_f04_legacy_anchor_not_conserves`
  (`F04.lean:114-130`, `:139-178`), and
  `waveF_f04_counterexample_not_conserves` (`F04.lean:230-236`) must remain.
  R06 T1 owns the corrected constructor; R27 must not "fix" the legacy
  constructor or delete the gap.
- `anchors_present_iff_negotiated` (`AnchorProps.lean:108-110`) and
  `anchor_deduction_two` (`:390-395`) must remain. T1's format selection is
  about feature vectors, not output presence; do not conflate the two.
- `anchor_literal_weight_neq_fee_basis`, `anchor_literal_weight_claim_refuted`
  (`H33.lean:528-534`), and `weightTargets_serializedWeight_anchor_gap`
  (`WeightTargets.lean:351-355`) must remain. T3 adds a format-aware base
  weight; it must not redefine the 1124 fee basis as a literal serialization
  weight or erase the 8 WU gap.
- `waveD_d13_zero_rate_sufficient` and `waveD_d13_zero_rate_gate_signs`
  (`D13.lean:377-384`) must remain. T2 must agree at `r = 0`; that is why the
  discrimination theorem carries `hreq`.
- `commitmentSigningGate_rejected_iff_insufficient`
  (`FeeTargets.lean:225-232`) and
  `commitmentSigningGate_rejected_iff_no_checkedSigning` (`:452-463`) must
  remain. T2 must not alter the existing gate or its error code.
- `d12_output_ordering_fails`, `wave4_dust_trimming_not_perm`, and
  `legacyCoverage_not_preserved_by_net_migration` (R06 §5.1) must remain;
  R27 does not touch the output-order or net-migration surface.
- `MAX_ACCEPTED_HTLCS = 483` (`HTLC.lean:69`) must remain as the non-zero-fee
  constant. T4 adds a format-indexed function; it must not replace the
  constant globally.

### 5.2 Non-vacuity witnesses

- **T1:** all four branches are reachable using `setRequired` on
  `emptyVector` with `allowZeroFee = true`; `allowZeroFee = false` plus
  feature 20 on both peers witnesses `selectCommitmentFormat_no_zeroFee`. The
  exclusions in the anchor/static iffs are necessary: without them, a
  zero-fee-supporting pair would also satisfy the right-hand side of the
  anchor iff, so the iff would be false.
- **T2:** `c := zeroHtlcCommitment .local 0 100_000 50_000 0 144 false`,
  `r = ⟨253⟩`, `feeSat = 0`, weight 724; zero-fee signs, legacy and
  anchors-zero-fee-htlc reject. At `r = ⟨0⟩`, legacy signs, so `hreq` cannot be
  dropped.
- **T3:** `numHtlcs = 0` gives 724 for zero-fee and 1124 for
  `anchorsZeroFeeHtlc`; `numHtlcs = 2` gives 1068 vs 1468. The inequality
  witness is independent of the `anchorOutputs` field.
- **T4:** 114 accepted / 115 rejected for zero-fee; 483 accepted / 484
  rejected for the anchor and legacy formats.
- **T5:** `Step.updateFee` preserves both anchor flags while changing the
  feerate; a reachable normal-phase sequence demonstrates the `Reachable`
  version.
- **T6:** one untrusted live anchor contributes 25,000; a trusted anchor, a
  legacy channel, and a shutdown-complete anchor contribute 0.

### 5.3 Hidden-assumption and weakening flags

- **T1 must not use `negotiated` as the channel-type test.** BOLT 1's
  `negotiated` is `lcl.requires n || (lcl.supports n && rmt.supports n)`
  (`FeaturesProps.lean:287-292`), so a locally required feature is selected
  even when the peer does not support it. Using it would hide the peer-support
  assumption and make the zero-fee iff false. Use `mutualSupport`.
- **T1 must not drop the local zero-fee policy premise.** LDK Node negotiates
  0FC first only when `enable_zero_fee_commitments = true` (`config.rs:505`,
  `:509-514`); support for feature 20 alone does not mean the node wants it.
  The `allowZeroFee` argument and the `henabled` hypothesis carry that
  premise, which is a local policy assumption, not a BOLT rule. Dropping
  `henabled` would hide the assumption and make the zero-fee branch
  unconditional on configuration.
- **T1 must not claim the selected format was actually negotiated on the
  wire.** The theorem is about advertised support only; the channel-type TLV
  and the actual `open_channel`/`accept_channel` exchange are outside the
  model.
- **T2 must not be read as a full zero-fee validity theorem.** The gate only
  exempts the base fee. The open-channel `feerate_per_kw = 0` rule, the shared
  anchor output, the v3 transaction, P2A execution, ephemeral dust, TRUC, and
  CPFP are external. A production caller must establish `hzero` and the
  zero-fee format independently.
- **T2 must not replace `commitmentSigningGate`.** Replacing it would make
  `commitmentSigningGate_rejected_iff_insufficient` false for a zero-fee
  commitment at a nonzero rate and would weaken `LN-CH-005`. The wrapper and
  the `commitmentSigningGateFor_legacy_eq` bridge preserve the old theorem.
- **T3 must not change `Commitment.weight`.** Its signature is consumed by
  `commitmentFee_mono_htlcs`, `commitmentWeight_anchor_delta`, and the fee
  targets. Add `commitmentWeightFor` and a bridge only for
  `.anchorsZeroFeeHtlc`.
- **T4 must not be cited as a `Step` invariant.** The cap lives in the wire
  messages, not in `ChannelParams`; `addHTLC` does not enforce it. The target
  proves the message-bound arithmetic, not that the channel cannot exceed it.
- **T5 must not claim full format lifetime.** `anchorOutputs` invariance is
  necessary but not sufficient: there is no `zeroFee` field and `updateFee`
  changes the feerate. The full BOLT 2 lifetime rule for zero-fee requires a
  `CommitmentFormat` field (T1) or an explicit format witness, plus the R06 T4
  prohibition on `update_fee`.
- **T5 must not claim an in-place upgrade exists or is forbidden by a
  transition.** The model has no upgrade event; the absence is a modeling fact,
  not a theorem about a rejected transition.
- **T6 must not be cited as a protocol theorem.** It is node policy. The
  close/force-close API carries no feerate, and the BumpTransaction/CPFP path
  is external.

## 6. Wave-13 recommendation

**Implement (bounded P1 lane).** T1 and T2 should be implemented together in a
new proof-layer module, with no changes to `ChannelParams`, `Channel`,
`Commitment`, `Step`, or `commitmentSigningGate`. T1 supplies the
`CommitmentFormat` vocabulary and the config-aware, `mutualSupport`-based
selector (`allowZeroFee` plus `henabled`); T2 supplies the format-aware
base-fee gate and the legacy-equality bridge. This
is safe, additive, and directly grounded in BOLT 9, BOLT 2, BOLT 3, and LDK
Node's documented preference order. The module docstring must state the two
scope limits: selection is from advertised support plus the local
`allowZeroFee` policy, and the zero-fee gate is a base-fee exemption only.

**Defer (P2).** T3 (724 vs 1124 format-aware weight), T4 (114/483 cap), and
T5 (anchor-bit invariance) are small, additive follow-ups. T3 has the highest
fidelity risk because BOLT 3 does not give a separate zero-fee expected-weight
line; it should carry the LDK implementation assumption explicitly. T4 is
arithmetic but does not close the `addHTLC`/`Step` enforcement gap. T5 is a
useful model fact but does not prove full format lifetime.

**Treat as external.** T6 (anchor reserve/CPFP/package relay) is node policy
and mempool/package-relay behavior. Do not implement it in the protocol lane
and do not use it to satisfy a catalog row. If a policy module is desired, keep
it separate and label it non-protocol.

**Do not do in this lane.** Do not change `commitmentPairOfBalances`,
`commitmentOutputs`, or `Commitment.weight` in place; R06 T1/T2/T3/T5 own the
P0/P1 anchor and shared-anchor repairs. Do not wire `commitmentSigningGate`
into production `Step`; R06 T4/D13 own the checked-transition work and the
reachability audit. Do not add an in-place commitment-format upgrade event;
LDK exposes no such operation, and BOLT 2 fixes the type for the channel's
lifetime.

**Bottom line.** R27 yields a safe P1 implementation lane for T1+T2 and
P2 follow-ups for T3–T5. The anchor-reserve/CPFP surface remains an explicit
external barrier, not a Lean protocol target.

## 7. Evidence and commands

All inspection was read-only. The following commands were run from
`/home/ubuntu/ln-lean-repair` unless noted:

```sh
git rev-parse --abbrev-ref HEAD
git rev-parse HEAD
git -C /tmp/opencode/ldk-refs/ldk-node rev-parse HEAD
git -C /tmp/opencode/ldk-refs/ldk-server rev-parse HEAD
git -C refs/bolts rev-parse HEAD
git -C refs/rust-lightning rev-parse HEAD

rg -n "anchorOutputs|zeroFee|sharedAnchor|CommitmentFormat|channelType|MAX_ACCEPTED_HTLCS" \
  LnLean/Channel LnLean/Protocol LnLean/Proofs
rg -n "commitmentSigningGate|feeInsufficient|waveD_d13_zero_rate" \
  LnLean/Proofs/Channel/FeeTargets.lean LnLean/Proofs/WaveD/D13.lean
rg -n "mutualSupport|negotiated|DependenciesSatisfied|anchorsFeature|staticRemoteKeyFeature" \
  LnLean/Proofs/Protocol/FeaturesProps.lean
rg -n "commitmentPairOfBalances|commitmentOutputs|anchorOutputValue|zeroHtlcCommitment" \
  LnLean/Channel/Commitment.lean LnLean/Proofs/Conservation.lean
rg -n "enable_zero_fee_commitments|per_channel_reserve_sats|total_anchor_channels_reserve_sats" \
  /tmp/opencode/ldk-refs/ldk-node/src/config.rs \
  /tmp/opencode/ldk-refs/ldk-node/src/lib.rs
rg -n "zero_fee|channel_type|ChannelConfig|OpenChannelRequest|UpdateChannelConfigRequest" \
  /tmp/opencode/ldk-refs/ldk-server/ldk-server/src \
  /tmp/opencode/ldk-refs/ldk-server/ldk-server-grpc/src
rg -n "zero_fee_commitments|max_accepted_htlcs|channel_type|update_fee" \
  refs/bolts/02-peer-protocol.md refs/bolts/03-transactions.md refs/bolts/09-features.md
rg -n "max_htlcs|commitment_tx_base_weight|selected_commitment_sat_per_1000_weight|second_stage_tx_fees_sat" \
  refs/rust-lightning/lightning/src/ln/chan_utils.rs
```

No Lean build, `lake` invocation, cargo test, or network access was used. The
pinned clones were not modified. The only written path is
`agents/reports/wave13-review/R27-anchor-zero-fee-upgrades.md`.

Primary evidence index:

- Lean: `LnLean/Channel/Types.lean:77-92`, `:162-174`, `:209`, `:245-258`;
  `LnLean/Channel/Commitment.lean:57-59`, `:109-127`, `:323-324`, `:351-402`;
  `LnLean/Channel/State.lean:86-137`; `LnLean/Channel/HTLC.lean:63-69`,
  `:343-355`; `LnLean/Proofs/Channel/FeeTargets.lean:206-232`, `:452-463`;
  `LnLean/Proofs/WaveD/D13.lean:377-384`;
  `LnLean/Proofs/Conservation.lean:451-497`;
  `LnLean/Proofs/ModelHardening/F04.lean:114-130`, `:139-178`, `:246-313`;
  `LnLean/Proofs/Protocol/FeaturesProps.lean:133-157`, `:276-292`,
  `:443-446`, `:513-516`, `:597-604`;
  `LnLean/Proofs/Bitcoin/AnchorProps.lean:70-77`, `:92-110`, `:189`, `:390-395`;
  `LnLean/Proofs/Bitcoin/WeightTargets.lean:351-355`;
  `LnLean/Proofs/WaveH/H33.lean:528-534`;
  `LnLean/Protocol/Messages.lean:100-157`;
  `LnLean/Proofs/ProtocolCoverageTargets.lean:234`, `:457-460`.
- LDK Node: `src/config.rs:38`, `:315-318`, `:432-505`, `:509-514`,
  `:568-571`; `src/lib.rs:237-247`, `:336-360`, `:388-395`, `:1500-1545`,
  `:2717-2748`; `src/types.rs:411-444`, `:615-623`; `src/event.rs:2389-2410`;
  `src/chain/mod.rs:646-664`; `src/chain/bitcoind.rs:233-254`.
- LDK Server: `ldk-server/src/util/config.rs:80`, `:200-201`, `:354-355`,
  `:740`, `:1316-1319`; `ldk-server/src/main.rs:160-161`;
  `ldk-server/src/api/close_channel.rs:23-44`;
  `ldk-server/src/api/update_channel_config.rs:22-62`;
  `ldk-server/src/api/mod.rs:131-135`;
  `ldk-server/src/util/proto_adapter.rs:90-96`, `:150`;
  `ldk-server-grpc/src/api.rs:767-820`, `:924-934`, `:949-985`, `:1319-1331`;
  `ldk-server-grpc/src/types.rs:812-832`, `:1770-1783`.
- BOLTs: `refs/bolts/02-peer-protocol.md:786-793`, `:1025`, `:1043-1044`,
  `:823-824`, `:861-865`, `:2888-2895`, `:3252-3253`, `:3275-3283`,
  `:3298-3299`; `refs/bolts/03-transactions.md:150-153`, `:178-195`,
  `:305-311`, `:321-326`, `:471`, `:491-494`, `:519`, `:563-570`;
  `refs/bolts/09-features.md:45`, `:52`, `:73-74`.
- rust-lightning: `lightning/src/ln/chan_utils.rs:63-70`, `:280-283`,
  `:297-312`, `:323-334`.
