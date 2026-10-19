#!/usr/bin/env python3
"""Generate the read-only 32-lane wave-13 review briefs.

The generated briefs are intentionally review-only.  Each lane may write exactly
one report under agents/reports/wave13-review/ and nothing else.  The launch
script runs 8 lanes at a time; R32 is the synthesis lane and runs after R01-R31.
"""
from __future__ import annotations

import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BRIEFS = ROOT / "agents" / "briefs" / "wave13-review"
REPORTS = ROOT / "agents" / "reports" / "wave13-review"
LDK_NODE = "/tmp/opencode/ldk-refs/ldk-node"
LDK_SERVER = "/tmp/opencode/ldk-refs/ldk-server"
LDK_NODE_PIN = "fa123fed131e27ecc420b77fa7086fcf1ddaebb8"
LDK_SERVER_PIN = "c17dc11dde38f88c53457039ddf30c6b90a63ba2"

LANES = [
    {
        "id": "R01",
        "slug": "l1-script-ec-boundary",
        "title": "L1 script, interpreter, and EC-verifier boundary",
        "lean": "`LnLean/Bitcoin/` and `LnLean/Proofs/Bitcoin/`, especially the interpreter, sighash, spend, and ECDSA bridge targets",
        "ldk": "ldk-node `src/wallet/`, `src/chain/`, `src/tx_broadcaster.rs`; ldk-server `ldk-server/src/api/onchain_*.rs` and `src/api/sign_message.rs`",
        "focus": "Audit the remaining L1-01/L1-02/L1-07 barriers against the concrete on-chain wallet and transaction paths exposed by LDK Node and LDK Server. Identify whether LDK provides a concrete verifier/amount/context boundary that the Lean model could mirror, and where the current untyped ByteArray interface remains the blocker. Distinguish model-level repair from external secp256k1 or consensus assumptions; do not propose a fake concrete bridge.",
    },
    {
        "id": "R02",
        "slug": "l1-tx-sighash-fees",
        "title": "L1 transaction construction, sighash, PSBT, fees, and weight",
        "lean": "`LnLean/Bitcoin/`, `LnLean/Proofs/Bitcoin/`, and the commitment/fee/weight modules",
        "ldk": "ldk-node `src/wallet/`, `src/tx_broadcaster.rs`, `src/fee_estimator.rs`; ldk-server `onchain_send.rs`, `onchain_bump_fee.rs`, `onchain_receive.rs`",
        "focus": "Map LDK Node/Server transaction construction, fee bumping, coin selection, and PSBT/weight behavior to the current Lean sighash/weight/commitment model. Find concrete behaviors (RBF, CPFP, fee estimation, change, dust, UTXO management) that are not represented and propose faithful target statements or explicit external barriers.",
    },
    {
        "id": "R03",
        "slug": "l1-chain-sync-finality",
        "title": "Chain sync, confirmations, reorgs, and finality",
        "lean": "`LnLean/Proofs/Security/ChainFinalityTargets.lean`, `LnLean/Proofs/Bitcoin/ReorgTargets.lean`, `LnLean/Proofs/Bitcoin/` chain modules",
        "ldk": "ldk-node `src/chain/bitcoind.rs`, `electrum.rs`, `esplora.rs`, `src/chain/mod.rs`; ldk-server `docs/configuration.md` and chain-source config",
        "focus": "Compare the finite block-graph finality model with the actual chain-source/confirmation/reorg behavior in LDK Node and Server. Identify missing confirmation-depth, reorg, chain-tip, stale-block, and chain-source-failure semantics; distinguish tractable model extensions from PoW/probabilistic or live-chain assumptions.",
    },
    {
        "id": "R04",
        "slug": "l1-wallet-utxo-balance",
        "title": "On-chain wallet, UTXOs, balances, and coin control",
        "lean": "`LnLean/Bitcoin/` wallet/balance/UTXO modules and the on-chain payment targets",
        "ldk": "ldk-node `src/wallet/`, `src/balance.rs`, `src/wallet/payment_stores.rs`; ldk-server `get_balances.rs`, `onchain_receive.rs`, `onchain_send.rs`",
        "focus": "Inventory LDK Node/Server wallet state, spendable/claimable balances, UTXO reservation, change, and confirmation behavior. Compare with the Lean balance/UTXO model and propose concrete consistency, conservation, and lifecycle targets that are not currently claimed.",
    },
    {
        "id": "R05",
        "slug": "channel-lifecycle",
        "title": "Channel lifecycle and peer/funding handshake",
        "lean": "`LnLean/Proofs/Channel/`, `LnLean/Proofs/Protocol/`, funding phase and open/accept targets",
        "ldk": "ldk-node `src/builder.rs`, `src/config.rs`, `src/connection.rs`; ldk-server `open_channel.rs`, `connect_peer.rs`, `disconnect_peer.rs`, `list_peers.rs`",
        "focus": "Map the full open/accept/funding_created/funding_signed/channel_ready lifecycle, including failure/abort paths, to the current Lean phase machine. Identify missing transition, error, timeout, and retry behaviors and propose the strongest safe targets.",
    },
    {
        "id": "R06",
        "slug": "commitments-fees-dust-anchors",
        "title": "Commitment state, fees, dust, and anchor outputs",
        "lean": "`LnLean/Proofs/Channel/` commitment, fee, dust, HTLC aggregate, and anchor-related modules",
        "ldk": "ldk-node `src/config.rs`, `src/event.rs`, channel config paths; ldk-server `update_channel_config.rs`, `close_channel.rs`",
        "focus": "Compare commitment fee/dust/trim/anchor behavior with LDK Node/Server configuration and channel semantics. Find concrete behavioral deltas (anchor channels, zero-fee commitments, dust limits, fee spikes, counterparty fee) and define faithful hypotheses/targets rather than weakening existing fee results.",
    },
    {
        "id": "R07",
        "slug": "htlc-forwarding-fees",
        "title": "HTLC add/fulfill/fail, forwarding, and fee accounting",
        "lean": "`LnLean/Proofs/Channel/`, `LnLean/Proofs/ProtocolCoverageTargets.lean`, forwarding and fee modules",
        "ldk": "ldk-node `src/payment/forwarding.rs`, `forwarding_store.rs`, `src/event.rs`; ldk-server `get_forwarded_payment_details.rs`, `list_forwarded_payments.rs`, `get_channel_forwarding_stats.rs`",
        "focus": "Map LDK's HTLC forwarding lifecycle, forwarding fee accounting, failure reasons, and persisted forwarding records to the Lean HTLC/coverage/fee model. Identify missing behaviors and propose exact targets with non-vacuity witnesses.",
    },
    {
        "id": "R08",
        "slug": "close-revocation-watchtower",
        "title": "Close, force-close, revocation, watchtowers, and backup",
        "lean": "`LnLean/Proofs/Channel/`, `LnLean/Proofs/Security/`, revocation and watchtower modules",
        "ldk": "ldk-node `src/chain/`, `src/event.rs`, `src/wallet/`, `src/io/`; ldk-server `close_channel.rs`, `docs/operations.md`",
        "focus": "Inventory cooperative/force close, revoked-state punishment, watchtower, and backup/recovery behavior in LDK Node/Server. Compare with current Lean revocation/watchtower results; identify missing state, timing, and persistence semantics.",
    },
    {
        "id": "R09",
        "slug": "bolt4-onion",
        "title": "BOLT 4 onion construction, processing, and errors",
        "lean": "`LnLean/Proofs/Onion/`, wire/message modules, and onion-related conformance targets",
        "ldk": "ldk-node `src/message_handler.rs`, `src/connection.rs`; ldk-server `bolt11_send.rs`, `spontaneous_send.rs`, forwarding APIs",
        "focus": "Compare BOLT 4 onion payload construction, per-hop processing, failure messages, and blinding behavior against the Lean onion model. Identify missing message/error/TLV cases and propose faithful targets.",
    },
    {
        "id": "R10",
        "slug": "bolt11-invoices",
        "title": "BOLT 11 invoice parse/create/sign/verify/expiry",
        "lean": "`LnLean/Proofs/Payment/InvoiceWireTargets.lean` and invoice/sighash/payment targets",
        "ldk": "ldk-node `src/payment/bolt11.rs`; ldk-server `bolt11_receive.rs`, `bolt11_send.rs`, `decode_invoice.rs`, `bolt11_claim_for_id.rs`, `bolt11_fail_for_id.rs`",
        "focus": "Map BOLT 11 field handling, bech32, signatures, expiry, fallback addresses, and receive/claim/fail state to the Lean invoice model. Identify exact missing behaviors and proposed targets; retain malformed/duplicate/signature separation results.",
    },
    {
        "id": "R11",
        "slug": "bolt12-offers",
        "title": "BOLT 12 offers, invoice requests, refunds, and payer proofs",
        "lean": "Payment/BOLT 12 modules and offer-related targets, if present",
        "ldk": "ldk-node `src/payment/bolt12.rs`; ldk-server `bolt12_receive.rs`, `bolt12_send.rs`, `bolt12_refund.rs`, `bolt12_create_payer_proof.rs`, `decode_offer.rs`",
        "focus": "Scope the BOLT 12 surface in LDK Node/Server and compare it to current Lean coverage. Identify the highest-value faithful model slice (offer/invoice-request/refund/payer-proof/replay) and the external cryptographic assumptions.",
    },
    {
        "id": "R12",
        "slug": "payment-lifecycle",
        "title": "Payment lifecycle, retries, MPP, keysend, and probing",
        "lean": "`LnLean/Proofs/Payment/`, payment state, probing, and conformance modules",
        "ldk": "ldk-node `src/payment/`, `src/payment/pending_payment_store.rs`, `src/payment/store.rs`, `src/probing.rs`, `src/payment/spontaneous.rs`; ldk-server payment APIs",
        "focus": "Compare payment lifecycle/idempotency/retry/MPP/keysend/probing behavior with the Lean payment state model. Identify missing states, persistence, and duplicate-payment behavior; propose concrete targets and counterexamples.",
    },
    {
        "id": "R13",
        "slug": "bolt7-gossip-store",
        "title": "BOLT 7 gossip validation, store, and epochs",
        "lean": "`LnLean/Proofs/Routing/`, `LnLean/Routing/`, gossip canonical/epoch targets",
        "ldk": "ldk-node `src/gossip.rs`, `src/graph.rs`; ldk-server `graph_list_nodes.rs`, `graph_list_channels.rs`, `graph_get_node.rs`, `graph_get_channel.rs`",
        "focus": "Map LDK gossip message validation, signature/timestamp checks, channel policy updates, and graph views to the Lean canonical/epoch model. Identify missing validation and persistence behaviors and propose targets.",
    },
    {
        "id": "R14",
        "slug": "bolt7-node-announcements",
        "title": "BOLT 7 node announcements, addresses, chain hash, rotation",
        "lean": "`LnLean/Proofs/Routing/NodeAddressTargets.lean`, `NodeIdentityTargets.lean`, `NodeIdentityChainTargets.lean`, `GossipCanonicalTargets.lean`",
        "ldk": "ldk-node `src/gossip.rs`, `src/graph.rs`; ldk-server `get_node_info.rs`, `graph_get_node.rs`",
        "focus": "Compare the new address parser and rotation/chain model against LDK's node-announcement handling. Find concrete chain-hash, address admission, timestamp, feature, alias, and rotation behaviors not modelled, and decide whether a safe wave-13 slice exists.",
    },
    {
        "id": "R15",
        "slug": "bolt8-transport",
        "title": "BOLT 8 transport, Noise, and TLS/API security",
        "lean": "`LnLean/Proofs/Protocol/NoiseTransportTargets.lean`, transport-auth targets, wire transport modules",
        "ldk": "ldk-node `src/connection.rs`; ldk-server `docs/tor.md`, `src/util/tls.rs`, `src/util/config.rs`, `docs/request-binding.md`",
        "focus": "Compare the Noise-shaped Lean model with LDK Node connection behavior and LDK Server TLS/Tor/request-binding. Identify whether any transport-authentication behavior is tractable without a real Noise/AEAD implementation, and record the exact external boundary.",
    },
    {
        "id": "R16",
        "slug": "routing-scoring-liquidity",
        "title": "Routing, scoring, pathfinding, and liquidity",
        "lean": "`LnLean/Proofs/Routing/`, routing graph/pathfinding/score modules",
        "ldk": "ldk-node `src/scoring.rs`, `src/runtime.rs`, `src/graph.rs`, `src/probing.rs`; ldk-server `export_pathfinding_scores.rs`, `get_node_info.rs`",
        "focus": "Map LDK's scoring/pathfinding/liquidity behavior to the Lean routing model. Identify missing route selection, failure scoring, liquidity constraints, and pathfinding persistence; distinguish tractable finite models from external probabilistic/network assumptions.",
    },
    {
        "id": "R17",
        "slug": "ldk-node-builder-persistence",
        "title": "LDK Node builder, config, persistence, data store, and restart",
        "lean": "No direct Lean counterpart; use current persistence/restart and node-config claims",
        "ldk": "ldk-node `src/builder.rs`, `src/config.rs`, `src/data_store.rs`, `src/io/`, `src/peer_store.rs`, `src/wallet/persist.rs`",
        "focus": "Inventory LDK Node's builder/config/persistence/restart behavior and identify which persistence invariants the Lean tree actually models. Propose a faithful restart/recovery target slice or mark it external.",
    },
    {
        "id": "R18",
        "slug": "ldk-node-events-runtime",
        "title": "LDK Node events, background processing, and message dispatch",
        "lean": "Current event/reachability/fold models and any message dispatch claims",
        "ldk": "ldk-node `src/event.rs`, `src/runtime.rs`, `src/message_handler.rs`, `src/connection.rs`, `src/lib.rs`",
        "focus": "Compare LDK Node's event loop, background processor, message handler, and event-to-action behavior with the Lean event/fold model. Identify missing event ordering, idempotency, and recovery semantics; propose targets if tractable.",
    },
    {
        "id": "R19",
        "slug": "liquidity-jit-async",
        "title": "Liquidity, LSPS, JIT channels, and async payments",
        "lean": "`LnLean/Proofs/Channel/`, liquidity/async payment modules if present",
        "ldk": "ldk-node `src/liquidity/mod.rs`, `src/payment/hrn.rs`, `src/payment/onchain.rs`; ldk-server `bolt11_receive_via_jit_channel.rs`, `unified_send.rs`",
        "focus": "Scope LDK Node/Server liquidity, JIT channel, LSPS, and async payment behavior. Identify the smallest faithful model slice, its security assumptions, and whether it belongs in wave 13 or is blocked on protocol/implementation details.",
    },
    {
        "id": "R20",
        "slug": "ldk-node-api-ffi",
        "title": "LDK Node public API, FFI, and bindings compatibility",
        "lean": "Current node-config/API claims and docs, if any",
        "ldk": "ldk-node `src/lib.rs`, `src/types.rs`, `src/ffi/`, `bindings/`; ldk-server `ldk-server-client/`",
        "focus": "Inventory the public API surface and FFI/binding behavior that a formal model would need to preserve. Identify API-level invariants (idempotency, error mapping, serialization) that are testable and not currently modelled.",
    },
    {
        "id": "R21",
        "slug": "ldk-server-api-auth",
        "title": "LDK Server API surface, auth, macaroons, and request binding",
        "lean": "Any API/auth/request-binding claims; current trust-boundary docs",
        "ldk": "ldk-server `ldk-server/src/api/`, `ldk-server-macaroons/`, `docs/api-guide.md`, `docs/request-binding.md`",
        "focus": "Map server API operations, macaroon authorization, TLS, and request-binding behavior. Identify formalizable auth invariants, replay/expiry behavior, and gaps in current Lean trust-boundary claims.",
    },
    {
        "id": "R22",
        "slug": "ldk-server-ops-config",
        "title": "LDK Server config, TLS, Tor, metrics, and operations",
        "lean": "Current docs/trust assumptions; no direct counterpart",
        "ldk": "ldk-server `ldk-server/src/util/config.rs`, `tls.rs`, `metrics.rs`, `systemd.rs`, `docs/configuration.md`, `docs/operations.md`, `docs/tor.md`",
        "focus": "Inventory operational/configuration behavior and identify which safety invariants (network selection, TLS identity, Tor binding, metrics exposure) deserve faithful model targets versus deployment assumptions.",
    },
    {
        "id": "R23",
        "slug": "ldk-server-e2e-mcp",
        "title": "LDK Server e2e tests, MCP, gRPC, and CLI/client",
        "lean": "Conformance/test strategy; current harness capabilities",
        "ldk": "ldk-server `e2e-tests/`, `ldk-server-mcp/`, `ldk-server-grpc/`, `ldk-server-cli/`, `ldk-server-client/`",
        "focus": "Extract behavioral assertions from the e2e/MCP/gRPC/CLI suites that could become pinned differential fixtures for the Lean conformance suite. Identify which tests are live-only, non-deterministic, or require network/chain infrastructure.",
    },
    {
        "id": "R24",
        "slug": "ldk-server-payment-channel-api",
        "title": "LDK Server payment, channel, and on-chain API semantics",
        "lean": "Payment/channel/on-chain model and conformance targets",
        "ldk": "ldk-server `ldk-server/src/api/bolt11_*.rs`, `open_channel.rs`, `close_channel.rs`, `onchain_*.rs`, `list_payments.rs`, `get_payment_details.rs`",
        "focus": "Compare request/response and state-transition semantics of the server's payment/channel/on-chain APIs with the Lean model. Identify concrete behavioral deltas and high-value conformance fixtures.",
    },
    {
        "id": "R25",
        "slug": "splicing",
        "title": "Splicing",
        "lean": "Channel type/state modules; check for splice coverage",
        "ldk": "ldk-server `splice_channel.rs`; ldk-node/ldk core splice paths discovered by search",
        "focus": "Scope the splicing lifecycle and wire/state behavior exposed by LDK. Determine whether the current Lean channel model can represent splice-in/splice-out faithfully, and propose a bounded target slice or an explicit external barrier.",
    },
    {
        "id": "R26",
        "slug": "dual-funding-negotiation",
        "title": "Dual funding, interactive tx, and channel negotiation",
        "lean": "Channel funding/negotiation modules",
        "ldk": "ldk-node/ldk-server paths discovered by search (`dual`, `interactive`, `tx_negotiation`, `open_channel`)",
        "focus": "Scope dual-funding/interactive-transaction/channel-negotiation behavior in the pinned LDK refs. Compare with the current single-funder phase machine and propose the smallest faithful extension or mark it out of scope.",
    },
    {
        "id": "R27",
        "slug": "anchor-zero-fee-upgrades",
        "title": "Anchor channels, zero-fee commitments, and commitment upgrades",
        "lean": "Commitment/fee/script modules",
        "ldk": "ldk-node config/event/channel paths; ldk-server channel config/close paths",
        "focus": "Search the pinned refs for anchor-output, zero-fee, and commitment-upgrade behavior. Identify whether current Lean fee/commitment results cover it, and propose target statements with explicit feature/config hypotheses.",
    },
    {
        "id": "R28",
        "slug": "async-trampoline-offers",
        "title": "Async payments, trampoline, onion messages, and unified BOLT 12",
        "lean": "Payment/onion/offer modules and any async/trampoline coverage",
        "ldk": "ldk-node `src/payment/hrn.rs`, `src/payment/bolt12.rs`, `src/payment/unified.rs`; ldk-server `unified_send.rs`, `bolt12_*.rs`",
        "focus": "Scope the async/trampoline/onion-message/unified-offer surface. Identify the most valuable bounded model slice and the protocol/cryptographic assumptions that prevent closing it now.",
    },
    {
        "id": "R29",
        "slug": "catalog-coverage-matrix",
        "title": "Catalog coverage matrix against LDK behavior",
        "lean": "`LnLean/Proofs/Obligations.lean`, `docs/THEOREM-INDEX.md`, `docs/TRACEABILITY.md`, all `LnLean/Proofs/` modules",
        "ldk": "Both pinned LDK refs, README/docs/API surfaces",
        "focus": "Build a coverage matrix from the 51 catalog rows to the behavior surfaces exposed by LDK Node/Server. Identify rows whose scope notes are too narrow/too broad, missing high-value rows, and rows that cannot be closed without external implementation. Do not edit the catalog.",
    },
    {
        "id": "R30",
        "slug": "conformance-strategy",
        "title": "Conformance strategy for LDK Node and LDK Server",
        "lean": "`tests/conformance/`, `scripts/check-conformance.py`, `ConformanceTargets.lean`, `ConformanceDiffTargets.lean`",
        "ldk": "Both pinned refs; especially ldk-server e2e tests, ldk-node tests, API docs",
        "focus": "Design a concrete, offline/pinned expansion of the conformance suite using LDK Node/Server as datapoints. Separate deterministic public-API fixtures from live/network/chain tests; propose fixture families, mutation controls, and Lean target shapes.",
    },
    {
        "id": "R31",
        "slug": "nonvacuity-assurance",
        "title": "Non-vacuity, traceability, axiom, and assumption review",
        "lean": "`LnLean/Proofs/Traceability.lean`, `PhaseC3/AxiomAudit.lean`, `docs/OPEN-ISSUES.md`, `agents/reports/swarm12/`",
        "ldk": "No direct dependency; use LDK behavior as a reality check on model scope",
        "focus": "Adversarially review the current 51-row/294-target tree for vacuity, circularity, overstatement, and traceability blind spots introduced by the ID-indexed Traceability refactor. Check whether proposed LDK-derived behaviors would weaken or strengthen existing claims. Do not edit code.",
    },
    {
        "id": "R32",
        "slug": "synthesis",
        "title": "Synthesis and wave-13/14 roadmap",
        "lean": "All 31 review reports plus current docs/catalog",
        "ldk": "Pinned LDK refs and reports",
        "focus": "Read all completed R01-R31 reports. Deduplicate findings, rank safe implementation lanes by fidelity/feasibility/impact, separate external barriers from human decisions, and produce a concrete wave-13/14 plan with disjoint file ownership and acceptance tests. Flag any proposal that would be vacuous or would weaken an existing statement.",
    },
]


def prompt(lane: dict) -> str:
    lane_id = lane["id"]
    report = f"agents/reports/wave13-review/{lane_id}-{lane['slug']}.md"
    is_synthesis = lane_id == "R32"
    read_reports = (
        "\nRead every report in `agents/reports/wave13-review/` except your own before writing."
        if is_synthesis
        else ""
    )
    return f"""You are {lane_id}, one of 32 READ-ONLY review lanes for `ln-lean`, a Lean 4 formal model of the Lightning Network.

WORKDIR: `/home/ubuntu/ln-lean-repair`
BRANCH: `repair/integrated` is checked out. Do not switch, create, rebase, commit, or push branches. Other lanes read the same worktree. Never edit files outside your owned report.

PINNED LDK REFERENCES (read-only clones):
- LDK Node: `{LDK_NODE}` at `{LDK_NODE_PIN}`
- LDK Server: `{LDK_SERVER}` at `{LDK_SERVER_PIN}`
- Pin/evidence note: `agents/reports/wave13-review/LDK-REFS.md`

MISSION: scope remaining work, not implement it. Produce a concrete, source-grounded gap report for your assigned surface.

OWNED WRITE PATH (only this file):
- `{report}`

You may run read-only inspection commands (`rg`, `sed`, `git -C ...`, `find`, `lake env lean` only if strictly read-only) but do not edit Lean, docs, scripts, tests, vendor, or another lane's report. Do not run cargo tests that fetch network dependencies. Do not build the whole tree.

READ FIRST:
1. `docs/AGENT-PROTOCOL.md`
2. `docs/OPEN-ISSUES.md`
3. `docs/THEOREM-INDEX.md`
4. `docs/TRACEABILITY.md`
5. `agents/TODO-REPAIR.md`
6. the relevant Lean modules: {lane['lean']}
7. the relevant pinned LDK paths: {lane['ldk']}
8. `agents/reports/swarm12/S12-POST-INTEGRATION-AUDIT.md`
{read_reports}

FOCUS:
{lane['focus']}

METHOD:
1. Map the current Lean claim surface: exact catalog row(s), declaration names, hypotheses, counterexamples, and scope notes. Use `rg` against the catalog and modules; do not trust prose alone.
2. Extract concrete behavior from the pinned LDK refs with exact `file:line` citations. Prefer public API/client behavior and tests over internal implementation detail.
3. Classify each behavior as: covered faithfully, partially covered, missing, contradicted (state a counterexample), or unmodelled/external. Do not call a behavior covered just because a similarly named theorem exists.
4. Propose 3-8 named Lean targets with explicit statement shapes and hypotheses. For each: priority (P0/P1/P2), fidelity risk, feasibility, and whether it is a model extension or an external assumption.
5. Identify non-vacuity witnesses or counterexamples that must be preserved. Explicitly flag any proposal that would weaken an existing theorem or hide an assumption.
6. Decide whether this lane yields a safe implementation lane for wave 13/14, or only an explicit external/human barrier.
{'' if not is_synthesis else '7. Synthesize R01-R31: deduplicate, rank, and produce a disjoint lane plan with owned files and gate criteria. Do not merely concatenate summaries.'}

REPORT FORMAT (Markdown):
# {lane_id} — {lane['title']}
**Status:** read-only review
**Pins:** LDK Node `{LDK_NODE_PIN}`, LDK Server `{LDK_SERVER_PIN}`
## 1. Scope and current Lean surface
## 2. LDK datapoints (with `file:line`)
## 3. Gap matrix
| Behavior | Lean status | LDK evidence | Gap / counterexample | Priority |
## 4. Proposed targets
For each target: proposed fully-qualified Lean name, statement shape, hypotheses, non-vacuity witness, and why it is faithful.
## 5. Assumptions, counterexamples, and non-vacuity risks
## 6. Wave-13 recommendation
## 7. Evidence and commands

FINAL MESSAGE: at most 12 lines. Report path, top 3 findings, top proposed target, and whether the parent should implement, defer, or treat as external. No code edits.
"""


def main() -> None:
    BRIEFS.mkdir(parents=True, exist_ok=True)
    REPORTS.mkdir(parents=True, exist_ok=True)
    manifest = []
    for lane in LANES:
        path = BRIEFS / f"{lane['id']}.md"
        path.write_text(prompt(lane), encoding="utf-8")
        manifest.append(
            {
                "id": lane["id"],
                "slug": lane["slug"],
                "title": lane["title"],
                "brief": str(path.relative_to(ROOT)),
                "report": f"agents/reports/wave13-review/{lane['id']}-{lane['slug']}.md",
            }
        )
    (ROOT / "agents" / "swarm" / "WAVE-13-REVIEW.json").write_text(
        json.dumps(
            {
                "wave": "wave13-review",
                "base": "f7f0628",
                "ldk_node": {"path": LDK_NODE, "commit": LDK_NODE_PIN},
                "ldk_server": {"path": LDK_SERVER, "commit": LDK_SERVER_PIN},
                "concurrency": 8,
                "lanes": manifest,
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )
    refs = f"""# Pinned LDK review references

These repositories are read-only external datapoints for the 32-lane wave-13
review. They are **not** vendored into `ln-lean` and are not proof dependencies.

| Repository | Commit | Local path |
|---|---|---|
| `lightningdevkit/ldk-node` | `{LDK_NODE_PIN}` | `{LDK_NODE}` |
| `lightningdevkit/ldk-server` | `{LDK_SERVER_PIN}` | `{LDK_SERVER}` |

Reproduce the pins:

```sh
git -C {LDK_NODE} rev-parse HEAD
git -C {LDK_SERVER} rev-parse HEAD
```

Rules for review lanes: read-only inspection; no network; no cargo tests that
fetch; no edits to the pinned clones.
"""
    (REPORTS / "LDK-REFS.md").write_text(refs, encoding="utf-8")
    print(f"wrote {len(LANES)} briefs to {BRIEFS}")
    print(f"manifest: {ROOT / 'agents' / 'swarm' / 'WAVE-13-REVIEW.json'}")


if __name__ == "__main__":
    main()
