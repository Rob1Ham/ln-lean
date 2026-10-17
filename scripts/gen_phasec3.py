#!/usr/bin/env python3
"""Generate the 8 phase-C3 agent briefs."""
import pathlib

OUT = pathlib.Path("/home/ubuntu/ln-lean-stage-phasec3/agents/briefs")
OUT.mkdir(parents=True, exist_ok=True)

COMMON = """You are {{NAME}}, one of eight phase-C3 composition agents for
`ln-lean`. A second worker also edits the repository; this lane owns only
`LnLean/Proofs/PhaseC3/` on branch `phase-c3`.

WORKDIR: /home/ubuntu/ln-lean-phasec3
Read first: docs/PHASE-C3-LANES.md, docs/AGENT-PROTOCOL.md,
docs/THEOREM-INDEX.md, docs/TRACEABILITY.md, and the source modules below.
Use `#check`/`#print` to confirm names.

TARGET: {{TARGET}}
MODULE: {{MODULE}}

MISSION
{{MISSION}}

RULES
- Edit only TARGET and agents/reports/{{NAME}}.md.
- Do not edit any existing module, `LnLean.lean`, `lakefile.lean`, `docs/`,
  `refs/`, or `vendor/`.
- No `axiom`, `admit`, `native_decide`, `unsafe`, or `@[implemented_by]`.
- Make every L1/crypto/network bridge an explicit structure field or theorem
  hypothesis; never introduce it as an axiom.
- `sorry` only with an adjacent `-- OBLIGATION: PC3-...` marker naming the
  missing bridge. At least one named theorem must be fully proved.
- Import `LnLean`; declare `set_option autoImplicit false`.

BUILD:
  export PATH=/dev/shm/btc/elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
  cd /home/ubuntu/ln-lean-phasec3
  flock -w 900 /tmp/ln-build.lock lake build {{MODULE}}

COMMIT:
  cd /home/ubuntu/ln-lean-phasec3
  MSG="[{{NAME}}] {{SHORT}}" ./scripts/phasec3-commit.sh {{NAME}} \\
    {{TARGET}} agents/reports/{{NAME}}.md

REPORT agents/reports/{{NAME}}.md: theorem table (proved/conditional),
build RC, remaining obligations with the exact missing field, and reproduce
commands. Final chat message <= 10 lines.

DETAILS
{{DETAILS}}
"""

JOBS = {
"PC37": dict(target="LnLean/Proofs/PhaseC3/EndToEndConservation.lean",
 module="LnLean.Proofs.PhaseC3.EndToEndConservation", short="end-to-end value conservation",
 mission="""Compose the L1 funding output, the channel ledger, and payment
settlement into one conservation theorem. Define a small `EndToEndState`
holding the funding value, channel ledger, and settled payments; define
`TotalValue`. Prove that a funded channel plus conserved channel steps plus
an HTLC settlement preserves `TotalValue`, and that no sequence of these
steps creates value. Include the fee bucket explicitly.""",
 details="""Sources: `LnLean/Bitcoin/Seam.lean` (`FundingOutput`),
`LnLean/Proofs/Conservation.lean` (`ChannelLedger`,
`ledger_no_value_creation`, `settleHTLCOutputAt_conserved`),
`LnLean/Payment/HTLC.lean`. Use `omega`; state the L1 funding link as a
structure field `fundingValue` with an equality hypothesis, not an axiom. At
least two named theorems, one for a single step and one for a list/run."""),

"PC38": dict(target="LnLean/Proofs/PhaseC3/WatchtowerBreach.lean",
 module="LnLean.Proofs.PhaseC3.WatchtowerBreach", short="watchtower breach remedy composition",
 mission="""Prove the end-to-end breach remedy: if a revoked commitment is
published, a watchtower detects it before the contest delay expires, and its
penalty transaction is accepted by the L1 bridge, then the honest party
recovers the contested value and the breacher cannot spend it. Make the
detection-time and bridge-acceptance assumptions explicit fields.""",
 details="""Sources: `LnLean/Channel/Penalty.lean` (`RevokedCommitment`,
`breachDetected`, `PenaltyTx`, `penaltyValid`, `L1ScriptBridge`,
`timelyL1Confirmation`, `punished_not_breacher_spendable`),
`LnLean/Proofs/Channel/PenaltyProps.lean`,
`LnLean/Proofs/Channel/BreachProps.lean`. Prove the time-bound composition;
do not re-prove the atomic penalty lemmas."""),

"PC39": dict(target="LnLean/Proofs/PhaseC3/FeeWeightDust.lean",
 module="LnLean.Proofs.PhaseC3.FeeWeightDust", short="fee/weight/dust output bounds",
 mission="""Prove that a commitment whose fee is at least `feeRate * weight`
and whose HTLCs below the dust limit are trimmed has non-negative output
values and a total output value at most the funding value. Relate the weight
to the number of HTLC outputs and prove monotonicity in the HTLC count. State
the feerate and dust preconditions exactly.""",
 details="""Sources: `LnLean/Channel/Commitment.lean`
(`commitmentWeight`, `commitmentFee`, `commitmentOutputs`,
`Commitment.totalOutputValue`), `LnLean/Channel/Fee.lean`,
`LnLean/Proofs/Channel/FeeProps.lean`, `LnLean/Channel/HTLCLaws.lean`
(`dust_value_lt`, `nonDust_value_ge`), `LnLean/Proofs/Channel/CommitmentTxProps.lean`.
Use `omega` and list induction."""),

"PC40": dict(target="LnLean/Proofs/PhaseC3/InvoiceParser.lean",
 module="LnLean.Proofs.PhaseC3.InvoiceParser", short="BOLT11 tag parser round-trip",
 mission="""On the modelled invoice subset, define a canonical tag list and
prove that encoding then parsing returns the original list (or state the
canonicality precondition that makes it true). Cover the payment-hash,
payment-secret, description, and expiry tags. Prove fixed data lengths and
tag-code injectivity. Do not assume bech32 correctness beyond the model.""",
 details="""Sources: `LnLean/Payment/Invoice.lean` (`Tag`, `fixedDataLength`,
`code_injective`, `Valid`, `Invoice`), `LnLean/Proofs/Payment/InvoiceProps.lean`,
`LnLean/Wire/BigSize.lean`. Add a local `encodeTag`/`parseTags` pair in the
new file if the model has no parser; prove the round-trip for that pair and
document the correspondence."""),

"PC41": dict(target="LnLean/Proofs/PhaseC3/OnionError.lean",
 module="LnLean.Proofs.PhaseC3.OnionError", short="onion failure packet composition",
 mission="""Prove the failure-packet structural laws: the encoded error packet is
290 bytes when its data fits the 256-byte pad, parsing a packet produced by
`sealError` returns the original data under the HMAC binding hypothesis, and
an invalid HMAC is rejected. Keep the HMAC assumption an explicit
`Prop`-valued hypothesis; do not prove it.""",
 details="""Sources: `LnLean/Routing/Onion.lean`
(`ONION_ERROR_PACKET_LEN`, `ONION_ERROR_PAD`, `ONION_ERROR_HMAC_LEN`,
`OnionInterface`, `sealLayer`, `peel`),
`LnLean/Proofs/Routing/OnionProps.lean`, `LnLean/Crypto/Hash.lean`.
If the model has no `sealError`, define it in the new file and state the
correspondence to BOLT 4."""),

"PC42": dict(target="LnLean/Proofs/PhaseC3/PersistenceRecovery.lean",
 module="LnLean.Proofs.PhaseC3.PersistenceRecovery", short="persisted channel recovery",
 mission="""Model persistence as a snapshot of the channel counters, HTLC set,
and ready flag. Prove that restoring a snapshot and replaying a suffix of
messages yields the same counters and ready state as replaying the full
history, and that recovery never rolls back a committed counter. State the
snapshot-consistency precondition explicitly.""",
 details="""Sources: `LnLean/Proofs/Liveness.lean` (`ChannelRecord`,
`recordSent_lastSent`, `advanceReceived_lastSent`,
`foldl_advanceReceived_lastSent`, `reconnect_preserves_channelReady`),
`LnLean/Protocol/Messages.lean`, `LnLean/Proofs/Protocol/ChannelReestablishProps.lean`.
Add a small `Snapshot` structure in the new file; prove append/replay
associativity and the no-rollback theorem."""),

"PC43": dict(target="LnLean/Proofs/PhaseC3/SecurityGame.lean",
 module="LnLean.Proofs.PhaseC3.SecurityGame", short="adversary win implies assumption failure",
 mission="""Formalize a small safety game: an adversary chooses L1/network actions
and wins if it creates value, steals a contested output, or makes two
conflicting commitments final. Prove that any winning strategy implies the
failure of at least one explicit assumption (signature unforgeability,
hash binding, L1 timelock enforcement, or channel conservation). Structure
the result as a disjunction of assumption failures, not as a new axiom.""",
 details="""Sources: `LnLean/Security/Model.lean`, `LnLean/Security/Invariants.lean`,
`LnLean/Proofs/Security/ThreatModelProps.lean`,
`LnLean/Channel/Penalty.lean`, `LnLean/Proofs/Conservation.lean`,
`LnLean/Crypto/Model.lean`. Keep the game finite and decidable where
possible; prove the implication by case analysis."""),

"PC44": dict(target="LnLean/Proofs/PhaseC3/CrossChannelRouting.lean",
 module="LnLean.Proofs.PhaseC3.CrossChannelRouting", short="multi-hop route conservation",
 mission="""Compose route construction with the channel fee/amount model: for a
valid path, the amount at each hop plus that hop's fee equals the amount at
the previous hop, the total fee is the sum of hop fees, and the sender's
amount is at most the sum of forward amounts. Prove that CLTV increases at
every hop with a positive delta and that a valid route is non-empty. State
liquidity/capacity preconditions explicitly.""",
 details="""Sources: `LnLean/Routing/Route.lean`
(`totalFee_append`, `totalCltv_append`, `endExpiry_gt`,
`constructRoute_totalFee`, `routeValid_edge_sound`),
`LnLean/Routing/Graph.lean`, `LnLean/Proofs/Routing/GraphProps.lean`,
`LnLean/Proofs/Payment/LiquidityProps.lean`. Use list induction and `omega`;
do not assume channel capacity without a hypothesis."""),
}

for name, j in JOBS.items():
    text = COMMON
    for k, v in {"NAME": name, "TARGET": j["target"], "MODULE": j["module"],
                 "SHORT": j["short"], "MISSION": j["mission"].strip(),
                 "DETAILS": j["details"].strip()}.items():
        text = text.replace("{{" + k + "}}", v)
    (OUT / f"{name}.md").write_text(text, encoding="utf-8")
    print(name, len(text))
