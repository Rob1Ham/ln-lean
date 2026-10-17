#!/usr/bin/env python3
"""Generate the 20 phase-C2 agent briefs."""
import pathlib

OUT = pathlib.Path("/home/ubuntu/ln-lean-stage-phasec2/agents/briefs")
OUT.mkdir(parents=True, exist_ok=True)

COMMON = """You are {{NAME}}, one of twenty phase-C2 agents for `ln-lean`.
A second box works on the same GitHub repository. This box owns the
`phase-c2` branch; the worktree is isolated from `main`.

WORKDIR: /home/ubuntu/ln-lean-phasec2   (branch `phase-c2`, based on `phase-c`)
Read first: docs/PHASE-C2-LANES.md, docs/AGENT-PROTOCOL.md,
docs/THEOREM-INDEX.md, docs/TRACEABILITY.md, and the source modules named
below. Use `#check`/`#print` to confirm names; do not guess.

TARGET: {{TARGET}}
MODE: {{MODE}}

MISSION
{{MISSION}}

RULES
- Do not edit any file outside TARGET and agents/reports/{{NAME}}.md.
- Do not change the lakefile, imports of existing modules, or `LnLean.lean`.
- No `axiom`, `admit`, `native_decide`, `unsafe`, `@[implemented_by]`.
- A `sorry` may remain only with an adjacent `-- OBLIGATION: PC2-...` marker
  giving the exact missing bridge. Do not hide a `sorry` in a helper.
- Never weaken an existing theorem statement. If a statement is false,
  prove a counterexample and state the strongest true conditional form.
- The new module must import `LnLean` (unless a narrower import is clearly
  sufficient) and declare `set_option autoImplicit false`.

BUILD (shared lock, exact module):
  export PATH=/dev/shm/btc/elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
  cd /home/ubuntu/ln-lean-phasec2
  flock -w 900 /tmp/ln-build.lock lake build {{MODULE}}

COMMIT (only target and report):
  cd /home/ubuntu/ln-lean-phasec2
  MSG="[{{NAME}}] {{SHORT}}" ./scripts/phasec2-commit.sh {{NAME}} \\
    {{TARGET}} agents/reports/{{NAME}}.md

REPORT agents/reports/{{NAME}}.md:
- exact theorem names, statements (one line each), and proved/conditional status;
- `grep -c '\\bsorry\\b'` before/after for TARGET;
- build command and RC;
- any remaining sorry: why blocked and the smallest next step;
- references to the source theorem(s) used and any newly discovered gap.
Final chat message <= 10 lines. Do not claim a proof unless the module
builds and the target theorem has no `sorry`.

DETAILS
{{DETAILS}}
"""

JOBS = {
"PC17": dict(mode="REPAIR an existing file", target="LnLean/Proofs/Bitcoin/FundingProps.lean",
 module="LnLean.Proofs.Bitcoin.FundingProps", short="remove refuted unconditional funding parse claim",
 mission="""`witnessScript_parse_eq_none` is **false as stated** (the file already
contains `witnessScript_parse_ne_none_counterexample` and the proved
conditional `witnessScript_parse_eq_none_of_wellFormed`). Remove only the
refuted unconditional theorem and its now-stale docstring paragraph; keep
the counterexample, the conditional theorem, and their proofs. The file must
end with zero `sorry`. Do not change the conditional statement.""",
 details="""Search `grep -R 'witnessScript_parse_eq_none' LnLean docs` before removing;
report any external references instead of editing them. Rebuild the module
and confirm `grep -c '\\bsorry\\b'` is 0. This is an honest model repair, not
a proof of the false claim."""),

"PC18": dict(mode="REPAIR an existing file", target="LnLean/Proofs/Channel/ReserveProps.lean",
 module="LnLean.Proofs.Channel.ReserveProps", short="remove refuted unconditional reserve claim",
 mission="""`committed_update_preserves_ledger` is **false as stated** because
`spendLocalBalance` uses truncated `Nat` subtraction; the file already has
`committed_update_preserves_ledger_counterexample` and the conditional
`committed_update_preserves_ledger_of_le`. Remove only the refuted
unconditional theorem and stale docstring text, keep the counterexample and
conditional proof, and finish with zero `sorry` in the file.""",
 details="""Check `grep -R 'committed_update_preserves_ledger' LnLean docs`; report
external references. Rebuild and confirm zero sorries. Do not weaken the
conditional theorem."""),

"PC19": dict(mode="REPAIR an existing file", target="LnLean/Proofs/Routing/GossipProps.lean",
 module="LnLean.Proofs.Routing.GossipProps", short="remove refuted gossip admission claims",
 mission="""Three obligations in this file are model/admission gaps with
counterexamples already proved in the same file:
`accepted_update_signing_key_announced`, `bindChannel_capacity_positive`,
`accepted_update_signature_length`. Remove the three refuted unconditional
theorems and their stale docstrings, but keep every counterexample and every
conditional replacement. Finish with zero `sorry` in the file. If a theorem
is actually provable from the existing hypotheses, prove it instead and
explain why the counterexample does not apply.""",
 details="""Read the whole `Open obligations` section first. `grep -R` each removed
name in `LnLean docs` and report references. Rebuild the module; zero
sorries. Do not delete counterexamples or conditional theorems."""),

"PC20": dict(mode="NEW module", target="LnLean/Proofs/PhaseC2/GlobalConservation.lean",
 module="LnLean.Proofs.PhaseC2.GlobalConservation", short="multi-channel ledger conservation",
 mission="""Lift the single-commitment conservation result to a ledger of
channels. Define a small `MultiChannelLedger` (a list of channel ledgers or
an additive total) in the new file, define its total value and fee, and prove
`multiLedger_no_value_creation`: if every channel is conserved and a step
changes only one channel by a conserved transition, total value plus fees is
unchanged. Also prove the append/cons decomposition for the total.""",
 details="""Sources: `LnLean/Proofs/Conservation.lean` (`ChannelLedger`,
`ledger_no_value_creation`, `conserved_no_value_creation`),
`LnLean/Channel/Types.lean`. Keep the new definitions minimal and use
`List` induction plus `omega`. At least two fully proved named theorems."""),

"PC21": dict(mode="NEW module", target="LnLean/Proofs/PhaseC2/CommitmentAlgebra.lean",
 module="LnLean.Proofs.PhaseC2.CommitmentAlgebra", short="commitment output decomposition",
 mission="""Prove the output algebra of a commitment: `totalOutputValue` equals
to-local + to-remote + anchor outputs + sum of HTLC outputs, and under
`CommitmentConserved` it equals funding minus fee. Prove the anchor/no-anchor
and zero-HTLC specializations. State any equality that needs a precondition
with exactly that precondition.""",
 details="""Sources: `LnLean/Channel/Commitment.lean`
(`Commitment.totalOutputValue_eq`, `commitmentOutputs`, `htlcOutputValue`,
`anchorOutputValue`), `LnLean/Proofs/Conservation.lean`
(`CommitmentConserved`, `conserved_fee_eq_residual`). Use `simp` and
`List.sum_append`; add local helper lemmas if needed."""),

"PC22": dict(mode="NEW module", target="LnLean/Proofs/PhaseC2/HTLCPartition.lean",
 module="LnLean.Proofs.PhaseC2.HTLCPartition", short="HTLC state partition and value conservation",
 mission="""Prove that the pending HTLC list partitions by state into
offered/received (and settled/removed are disjoint), that the sum over the
partition equals the sum over the whole list, and that adding an offered
HTLC increases the in-flight bucket by exactly its amount. Prove the
settled-plus-in-flight identity used by `ReserveProps`.""",
 details="""Sources: `LnLean/Channel/HTLC.lean`,
`LnLean/Proofs/Channel/ReserveProps.lean` (`htlcInFlightValue`,
`inFlightSum_append_offered`), `LnLean/Channel/HTLCLaws.lean`. `List.filter`
+ `List.map` + `List.sum_append`; induction on the list; `omega`."""),

"PC23": dict(mode="NEW module", target="LnLean/Proofs/PhaseC2/HTLCUniqueIds.lean",
 module="LnLean.Proofs.PhaseC2.HTLCUniqueIds", short="HTLC id freshness and non-reuse",
 mission="""Prove that adding an HTLC with an id not already present preserves
`List.Nodup` of ids, that removing one preserves it, and that an id removed
from the live set cannot reappear in the live set without an explicit add.
State the freshness precondition explicitly. Include an `addHTLC` wrapper
if the existing model exposes one.""",
 details="""Sources: `LnLean/Channel/HTLC.lean`, `LnLean/Channel/HTLCLaws.lean`
(`htlcSet_sound`, `htlcSet_length_le`), `LnLean/Proofs/Channel/HTLCProps.lean`.
Use list induction and decidable equality on ids."""),

"PC24": dict(mode="NEW module", target="LnLean/Proofs/PhaseC2/RevocationNumber.lean",
 module="LnLean.Proofs.PhaseC2.RevocationNumber", short="revocation point determines commitment number",
 mission="""Under the shachain injectivity hypothesis already present in the
model, prove that a published per-commitment point/secret identifies at most
one commitment number, and that `RevocationStore.isRevoked` is monotone in
the stored index. Relate the secret index to the commitment number via the
existing `revocationSecret`/`MAX_COMMITMENT_NUMBER` definitions. State the
injectivity hypothesis explicitly if it is not a theorem.""",
 details="""Sources: `LnLean/Channel/Revocation.lean`
(`revocationSecret_injective`, `revoked_monotone`, `isRevoked`,
`provideSecret`, `MAX_COMMITMENT_NUMBER`), `LnLean/Proofs/Channel/RevocationProps.lean`.
Do not assume collision resistance of a hash unless it is an explicit
hypothesis."""),

"PC25": dict(mode="NEW module", target="LnLean/Proofs/PhaseC2/PenaltyDoubleSpend.lean",
 module="LnLean.Proofs.PhaseC2.PenaltyDoubleSpend", short="penalty transaction exclusive spend",
 mission="""Compose the penalty model into an exclusive-spend theorem: a
`PenaltyTx` valid against a revoked commitment spends both contested outputs,
and after a timely confirmation no `BreacherSpend` of those outpoints is
accepted by the same L1 bridge. Use the existing `L1ScriptBridge` and
`punishable`/`penaltyValid` predicates; make the bridge assumptions explicit
as structure fields or hypotheses.""",
 details="""Sources: `LnLean/Channel/Penalty.lean`
(`PenaltyTx`, `penaltySpendsBoth`, `BreacherSpend`, `penaltyValid`,
`L1ScriptBridge`, `punished_not_breacher_spendable`),
`LnLean/Proofs/Channel/PenaltyProps.lean`. Prove the composition; do not
re-prove the existing atomic lemmas."""),

"PC26": dict(mode="NEW module", target="LnLean/Proofs/PhaseC2/CltvAccumulation.lean",
 module="LnLean.Proofs.PhaseC2.CltvAccumulation", short="route CLTV accumulation",
 mission="""Prove that `Route.endExpiry` and `Route.totalCltv` are monotone in
the hop list and strictly increase when a hop with positive `cltvDelta` is
prepended/appended. Prove the `constructRoute` CLTV equals the sum of hop
deltas plus the start height, and that reversing a route reverses the
accumulation order (or state the correct orientation explicitly).""",
 details="""Sources: `LnLean/Routing/Route.lean`
(`expiryAfter_strict`, `totalCltv_append`, `endExpiry_append`,
`endExpiry_gt`, `constructRoute_totalFee`), `LnLean/Routing/Graph.lean`.
Use list induction and `omega`; avoid `Nat` truncation surprises."""),

"PC27": dict(mode="NEW module", target="LnLean/Proofs/PhaseC2/OnionLayers.lean",
 module="LnLean.Proofs.PhaseC2.OnionLayers", short="onion seal/peel layer laws",
 mission="""Prove the structural layer laws: `sealLayers` preserves the number
of layers, `peel` on a nonempty sealed packet returns `some`, and peeling a
forward layer decreases `layerCount` by one. Prove `wireSize` is constant
`1366` for every packet. If `peel`'s payload requires a cryptographic
assumption, isolate it as an explicit hypothesis rather than an axiom.""",
 details="""Sources: `LnLean/Routing/Onion.lean`
(`sealLayer_layerCount`, `sealLayers_layerCount`, `peel_nil`, `peel_cons`,
`peel_forward_layers`, `wireSize_eq_ONION_PACKET_LEN`),
`LnLean/Proofs/Routing/OnionProps.lean`."""),

"PC28": dict(mode="NEW module", target="LnLean/Proofs/PhaseC2/MPPPrefix.lean",
 module="LnLean.Proofs.PhaseC2.MPPPrefix", short="MPP prefix sums and atomicity",
 mission="""Prove prefix-sum monotonicity for `MPPPlan.parts`, that a part's
amount is at most the total, that `mppComplete` is equivalent to the sum of
parts equalling the plan amount, and that `mppAtomic` holds for the
all-success and all-failure outcome lists. State any uniqueness/binding
hypothesis on the payment secret explicitly.""",
 details="""Sources: `LnLean/Payment/MPP.lean`
(`sumParts_append`, `amount_le_sumParts`, `mppComplete`, `mppAtomic`,
`bindsSecret_unique`), `LnLean/Proofs/Payment/MPPProps.lean`. Use list
induction; `omega` for the arithmetic."""),

"PC29": dict(mode="NEW module", target="LnLean/Proofs/PhaseC2/InvoiceBinding.lean",
 module="LnLean.Proofs.PhaseC2.InvoiceBinding", short="invoice amount and hash binding",
 mission="""Prove that `amountSatisfies` pins the paid amount to the invoice
amount (for the exact-payment predicate), that a preimage determines at most
one payment hash under an injective hash hypothesis, and that a valid
invoice's `expiresAt` is monotone in the expiry parameter. State the hash
injectivity/preimage-resistance hypothesis explicitly.""",
 details="""Sources: `LnLean/Payment/Invoice.lean`
(`amountSatisfies`, `preimageCommits`, `expiresAtWith`, `Valid`,
`verify`), `LnLean/Proofs/Payment/InvoiceProps.lean`,
`LnLean/Crypto/Hash.lean`. Do not assume SHA-256 injectivity."""),

"PC30": dict(mode="NEW module", target="LnLean/Proofs/PhaseC2/FeatureClosure.lean",
 module="LnLean.Proofs.PhaseC2.FeatureClosure", short="feature negotiation closure",
 mission="""Locate the feature-vector definitions (search for `Features`,
`Accepts`, `intersection` under `LnLean/Protocol` and
`LnLean/Proofs/Protocol`). Prove that the intersection of two accepted
feature sets is accepted, that negotiation is idempotent and commutative,
and that an optional feature cannot become required by intersection. If the
wave-A model lacks a required-bit predicate, define it in the new file and
state the theorem over that definition.""",
 details="""Sources: `LnLean/Proofs/Protocol/FeaturesProps.lean`,
`LnLean/Protocol/Laws.lean`, `LnLean/Protocol/Messages.lean`. Prove the
bitwise/pointwise core; no `Nat.land` axioms. At least two named theorems."""),

"PC31": dict(mode="NEW module", target="LnLean/Proofs/PhaseC2/ReestablishRange.lean",
 module="LnLean.Proofs.PhaseC2.ReestablishRange", short="reestablish retransmission range",
 mission="""Prove that the retransmission window after `channel_reestablish`
is finite, that the sent/received counters are monotone across reconnect,
and that the set of messages eligible for retransmission is a subset of the
bounded recent-message buffer. Combine the existing counter and
`retransmittable` predicates; make buffer-size assumptions explicit.""",
 details="""Sources: `LnLean/Proofs/Protocol/ChannelReestablishProps.lean`,
`LnLean/Proofs/Liveness.lean` (`retransmittable`, `recordSent_lastSent`,
`advanceReceived_lastSent`, `foldl_advanceReceived_lastSent`,
`reconnect_preserves_channelReady`), `LnLean/Protocol/Messages.lean`."""),

"PC32": dict(mode="NEW module", target="LnLean/Proofs/PhaseC2/LivenessDelivery.lean",
 module="LnLean.Proofs.PhaseC2.LivenessDelivery", short="end-to-end eventual HTLC resolution",
 mission="""Compose the channel-liveness and HTLC-liveness results: under a
fair scheduler and an honest timer, a pending HTLC in a channel that reaches
`normal` is eventually fulfilled or timed out. Prove the composition as a
single theorem, with the fairness/timer hypotheses explicit. Also prove the
contrapositive: if a pending HTLC never resolves, the scheduler is not fair
or the timer is not honest.""",
 details="""Sources: `LnLean/Proofs/Liveness.lean`
(`fair_awaitingLockin_eventually_normal`, `pending_htlc_eventually_resolved`,
`eventual_delivery_or_timeout_resolves`, `Eventually`, `Fair`,
`HonestTimer`), `LnLean/Proofs/Channel/StateMachineProps.lean`. Do not
redefine the existing predicates."""),

"PC33": dict(mode="NEW module", target="LnLean/Proofs/PhaseC2/FundingBridge.lean",
 module="LnLean.Proofs.PhaseC2.FundingBridge", short="L1 funding output spendability bridge",
 mission="""Formalize the funding-output bridge: a `FundingOutput` whose
`scriptPubKey` is the P2WSH of the 2-of-2 witness script is spendable by a
witness containing both funding signatures, provided both keys sign the
funding transaction. Use the vendored `Bitcoin` semantics read-only; do not
edit `vendor/`. If the concrete interpreter cannot parse
`OP_CHECKMULTISIG`, state the bridge as an explicit `FundingSpendBridge`
structure with the script-semantics obligation as a field and prove the
composition from it.""",
 details="""Sources: `LnLean/Bitcoin/Seam.lean` (`FundingOutput`, `p2wsh`,
`fundingScriptPubKey`, `moneyRange`), `LnLean/Bitcoin/Funding.lean`,
`LnLean/Proofs/Bitcoin/FundingProps.lean`, `vendor/btc-lean-core/Bitcoin/`.
Keep all vendor files byte-identical (read-only)."""),

"PC34": dict(mode="NEW module", target="LnLean/Proofs/PhaseC2/CommitmentBridge.lean",
 module="LnLean.Proofs.PhaseC2.CommitmentBridge", short="L1 commitment output bridge",
 mission="""Formalize spendability of the to-local and to-remote commitment
outputs: the to-local branch requires the revocation key or the holder's
signature after the CSV delay; the to-remote branch requires the remote
signature. Prove the script-shape and size lemmas and the conditional
spendability composition, using an explicit bridge hypothesis for the L1
interpreter. Do not edit `vendor/`.""",
 details="""Sources: `LnLean/Bitcoin/Seam.lean` (`toLocalScript`, `toRemoteScript`,
`p2wsh`), `LnLean/Channel/Commitment.lean`,
`LnLean/Proofs/Channel/CommitmentTxProps.lean`,
`LnLean/Proofs/Channel/BreachProps.lean`."""),

"PC35": dict(mode="NEW module", target="LnLean/Proofs/PhaseC2/HTLCBridge.lean",
 module="LnLean.Proofs.PhaseC2.HTLCBridge", short="L1 HTLC output bridge",
 mission="""Formalize the two HTLC script paths: the payment-hash branch is
spendable with a preimage matching the hash and the recipient signature; the
timeout branch is spendable after `cltvExpiry` with the sender signature.
Prove that the two branches are disjoint under a collision-resistant hash
hypothesis and that the script template encodes the payment hash and CLTV
injectively (reuse the phase-C injectivity lemmas). Keep the L1 interpreter
obligation explicit.""",
 details="""Sources: `LnLean/Bitcoin/Seam.lean` (`htlcBranchScript`,
`htlcBranch_nonempty`, `p2wsh`), `LnLean/Proofs/Bitcoin/ScriptProps.lean`,
`LnLean/Proofs/Channel/HTLCProps.lean`, `LnLean/Channel/HTLC.lean`."""),

"PC36": dict(mode="NEW module", target="LnLean/Proofs/PhaseC2/PenaltyBridge.lean",
 module="LnLean.Proofs.PhaseC2.PenaltyBridge", short="L1 penalty output bridge",
 mission="""Connect the penalty model to the L1 script bridge: after a breach,
the honest party's penalty transaction spends both contested outputs to a
single output controlled by the honest party; prove the value bound and the
exclusive-spend composition from the bridge's `spends` and `accepted`
predicates. Make the L1 acceptance obligation a structure field, not an
axiom. Reuse `Penalty.penaltyValid_*` and `penaltySpendsBoth`.""",
 details="""Sources: `LnLean/Channel/Penalty.lean`
(`L1ScriptBridge`, `penaltyValid_spends`, `penaltyValid_sweep`,
`penaltyObligation_punishable`, `punished_not_breacher_spendable`),
`LnLean/Proofs/Channel/PenaltyProps.lean`, `LnLean/Bitcoin/Seam.lean`."""),
}

for name, j in JOBS.items():
    text = COMMON
    for k, v in {
        "NAME": name, "MODE": j["mode"], "TARGET": j["target"],
        "MISSION": j["mission"].strip(), "MODULE": j["module"],
        "SHORT": j["short"], "DETAILS": j["details"].strip(),
    }.items():
        text = text.replace("{{" + k + "}}", v)
    (OUT / f"{name}.md").write_text(text, encoding="utf-8")
    print(name, len(text))
