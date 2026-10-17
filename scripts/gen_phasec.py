#!/usr/bin/env python3
"""Generate the 16 phase-C agent briefs."""
import pathlib

OUT = pathlib.Path("/home/ubuntu/ln-lean-stage-phasec/agents/briefs")
OUT.mkdir(parents=True, exist_ok=True)

COMMON = """You are {name}, one of sixteen phase-C proof agents for `ln-lean`.
You are working in a dedicated worktree so a second box can work on the
same GitHub repository without clobbering your files.

WORKDIR: /home/ubuntu/ln-lean-phasec   (branch `phase-c`, based on `origin/main`)
Read first: docs/PHASE-C-LANES.md, docs/AGENT-PROTOCOL.md, docs/ROADMAP.md,
the target file, and the wave-A module it imports.

TARGET FILE (the only Lean file you may edit):
  {target}

MISSION
Remove `sorry` from the target file by proving the listed theorem(s), or
prove a strictly stronger/corrected conditional form plus a counterexample
when the current statement is false. Never weaken a statement silently.

Theorems / obligation sites:
{theorems}

METHOD
1. Read the whole theorem and the definitions it depends on. Reproduce the
   exact goal with `set_option pp.all true` or `#check` before editing.
2. Add small helper lemmas *in the same file* if needed. Prove with Lean
   core (`simp`, `omega`, `induction`, `cases`, `rfl`, `decide`, `ext`).
   No mathlib.
3. Replace `sorry` only with a complete proof of the same statement. If a
   statement is false or blocked by an absent model invariant, do NOT fake
   it: leave the `sorry`, keep/refresh the `-- OBLIGATION:` marker with the
   exact missing bridge, and prove the strongest true conditional version
   you can as a separate theorem with a docstring.
4. Do not change existing definitions, theorem statements, imports, or
   namespace. Do not edit any other file (except your report).
5. No `axiom`, `admit`, `native_decide`, `unsafe`, or `@[implemented_by]`.
   `set_option autoImplicit false` is already in the file.

BUILD (exact module, shared lock):
  export PATH=/dev/shm/btc/elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
  cd /home/ubuntu/ln-lean-phasec
  flock -w 900 /tmp/ln-build.lock lake build {module}

COMMIT (only target + report):
  cd /home/ubuntu/ln-lean-phasec
  MSG="[{name}] {short}" ./scripts/phasec-commit.sh {name} \\
    {target} agents/reports/{name}.md

REPORT agents/reports/{name}.md:
- sorry count before/after (`grep -c '\\bsorry\\b' {target}`);
- table: theorem | status (proved / still sorry) | new helper lemmas;
- exact build RC;
- for any remaining sorry: why it is blocked, and the next smallest step;
- reproduction commands.
Do not claim a theorem is proved unless the `sorry` at that site is gone and
the module builds. Final chat message <= 10 lines.

HINTS
{hints}
"""

JOBS = {
"PC01": dict(target="LnLean/Proofs/Conservation.lean", module="LnLean.Proofs.Conservation",
 short="commitment conservation under HTLC settlement",
 theorems="""`settleHTLCOutputErase_conserved` (line ~627). Given
`CommitmentConserved c`, `h ∈ c.htlcs`, and `CommitmentHTLCOutput h`, prove
settling one HTLC output preserves `CommitmentConserved`. The missing step
is that erasing exactly one output subtracts exactly its value from the
output sum, including duplicate-valued outputs. Inspect
`settleHTLCOutputErase`, `CommitmentConserved`, `htlcOutputValue`, and the
existing list-sum lemmas in this file.""",
 hints="List induction over `c.htlcs`; use `List.sum_erase`-style lemmas if present, otherwise prove a local one. Watch duplicate values: erase by position/id, not by value. `omega` for the final arithmetic."),

"PC02": dict(target="LnLean/Proofs/Bitcoin/FundingProps.lean", module="LnLean.Proofs.Bitcoin.FundingProps",
 short="funding capacity and parse obligations",
 theorems="""(1) `channelCapacityMsat_le_MSAT_MAX` (line ~296): capacity in msat
is bounded by `Msat.MAX` for `p.WellFormed`. This is Int/Nat arithmetic.
(2) `witnessScript_parse_eq_none` (line ~421): the L1 parser rejects the
2-of-2 witness script because `ScriptInstr` lacks `OP_CHECKMULTISIG`.
Check whether this reduces by `rfl`/`decide`; if the parser is opaque, leave
the obligation with the exact missing constructor.""",
 hints="For (1), unfold `channelCapacityMsat`, `FundingParams.WellFormed`, `Msat.MAX`; `omega` or `norm_num` with the 21M bound. For (2), inspect `Bitcoin.Data.Script.parse`/`decodeOp` and try `rfl`; do not add a parser constructor."),

"PC03": dict(target="LnLean/Proofs/Bitcoin/AnchorProps.lean", module="LnLean.Proofs.Bitcoin.AnchorProps",
 short="anchor script injectivity",
 theorems="""(1) `anchorWitnessScript_key_injective` (line ~444): equal anchor
witness scripts imply equal funding keys. Needs ByteArray append/prefix
cancellation.
(2) `localAnchor_hash_ne_remoteAnchor_hash` (line ~454): under a
collision-resistant `sha256` and distinct funding keys, the two anchor
program hashes differ. Use (1) plus the hash hypothesis.""",
 hints="Prove ByteArray append-cancellation or use `ByteArray.ext` + `List` lemmas. `anchorWitnessScript` is a fixed prefix ++ key bytes; derive key equality by extensionality. For (2), `intro h; exact hkeys ((1) ...)`."),

"PC04": dict(target="LnLean/Proofs/Bitcoin/ScriptProps.lean", module="LnLean.Proofs.Bitcoin.ScriptProps",
 short="script number and HTLC binding injectivity",
 theorems="""(1) `pushScriptNum32_injective` (line ~697): fixed-width 4-byte
little-endian push is injective below 2^32.
(2) `receivedHtlcWitnessScript_cltv_injective` (line ~705): distinct CLTV
values give distinct scripts.
(3) `offeredHtlcWitnessScript_paymentHash_injective` (line ~717): distinct
20-byte payment hashes give distinct scripts.""",
 hints="Prove (1) by reading the four bytes back out (`ByteArray.get!`/`extract`) and `omega`; then (2) follows from (1) and append cancellation, (3) from append cancellation. `pushUInt32LE`/`pushScriptNum32` definitions are in the wave-A file."),

"PC05": dict(target="LnLean/Proofs/Wire/TLVProps.lean", module="LnLean.Proofs.Wire.TLVProps",
 short="canonical TLV round-trip",
 theorems="""`decodeTLV_encodeTLV` (line ~288): for a canonical `TLVStream`,
`decodeTLV (encodeTLV s) = some s`. The parser accepts duplicates, so the
`Canonical` hypothesis is essential. Read `encodeTLV`, `decodeTLV`,
`TLVStream.Canonical`, and the existing BigSize round-trip lemmas.""",
 hints="Structural induction on the stream/list. For each record, use the BigSize encode/decode lemma already proved in `Wire/BigSize.lean`; then reassemble the list. Keep the canonical sortedness hypothesis available for the parser's choice."),

"PC06": dict(target="LnLean/Proofs/Crypto/Sha256Props.lean", module="LnLean.Proofs.Crypto.Sha256Props",
 short="no injective 32-byte hash",
 theorems="""`no_injective_hash_into_32_bytes` (line ~329): no `H : ByteArray →
ByteArray` with all outputs 32 bytes is `PreimageResistant` (in the strong
injective sense used in this file). This is a cardinality argument over
`ByteArray`.""",
 hints="If `PreimageResistant` is defined as injectivity, derive an injection from an infinite/uncountable domain into a finite set of 2^256 byte strings. Lean core may not have the cardinality lemma; if it does not, leave the sorry with an exact missing lemma (e.g. `ByteArray` cardinality) and prove the finite-image version you can."),

"PC07": dict(target="LnLean/Proofs/Crypto/EcdsaProps.lean", module="LnLean.Proofs.Crypto.EcdsaProps",
 short="DER parser refinement",
 theorems="""(1) `derFullOK_imp_wireSigOK` (line ~549): full DER acceptance plus
length 71–73 implies the envelope predicate.
(2) `derFullOK_length_exact` (line ~557): a full DER parse yields
`rLen`, `sLen` with `b.size = 7 + rLen + sLen`.""",
 hints="Unfold `derFullOK`, `wireSigOK`, and the byte-offset predicates. These are Nat/ByteArray arithmetic facts; `omega` after establishing the offsets. Do not change the predicates."),

"PC08": dict(target="LnLean/Proofs/Channel/HTLCProps.lean", module="LnLean.Proofs.Channel.HTLCProps",
 short="HTLC live-set laws",
 theorems="""(1) `htlcSet_removeFromSet_comm` (line ~423): removing an id
commutes with filtering to live HTLC records.
(2) `totalHtlcValue_le_length_mul` (line ~429): a pointwise bound `m`
bounds the total in-flight value by `length * m`.""",
 hints="(1) induction on the list; case on id equality and live state. (2) induction on the list; `simp [totalHtlcValue]`; `omega` with `hbound`. `List.sum_le_card_nsmul`-style lemmas may not exist—prove a local induction."),

"PC09": dict(target="LnLean/Proofs/Channel/ReserveProps.lean", module="LnLean.Proofs.Channel.ReserveProps",
 short="committed update conservation",
 theorems="""The theorem at line ~555 with obligation `LN-CH-101`: a committed
update adding one local HTLC preserves
`balance.total + htlcInFlightValue + fee = fundingValue` in the successor
channel `c'`. Read the exact statement and the update function it uses.""",
 hints="Unfold the update and the in-flight sum; the new HTLC contributes exactly its amount, and the settled balance drops by the same amount. `omega` after `simp`."),

"PC10": dict(target="LnLean/Proofs/Channel/StateMachineProps.lean", module="LnLean.Proofs.Channel.StateMachineProps",
 short="fundingLocked appears on the path to normal",
 theorems="""`trace_to_normal_contains_fundingLocked` (line ~395): any trace
from a `negotiating` channel to a `normal` channel contains the
`fundingLocked` protocol event.""",
 hints="Induct on the `Trace` derivation. Use the `Step` constructors and the phase-rank lemma already in the file (`phase_rank`/monotonicity). The only step into `normal` from below must be `fundingLocked`."),

"PC11": dict(target="LnLean/Proofs/Protocol/ChannelReestablishProps.lean", module="LnLean.Proofs.Protocol.ChannelReestablishProps",
 short="reestablish counter preservation and monotonicity",
 theorems="""(1) `receive_channelReestablish_preserves_counters` (line ~232).
(2) `receive_counters_monotone` (line ~341).
Both need the list lemma
`findChannel (updateChannel s cid f) cid = some (f c)`.""",
 hints="Prove the `findChannel`/`updateChannel` lookup lemma by list induction (with decidable channel-id equality). Then unfold `receive` for the relevant message constructors and use the lemma. Watch messages that do not address `cid`."),

"PC12": dict(target="LnLean/Proofs/Protocol/FeaturesProps.lean", module="LnLean.Proofs.Protocol.FeaturesProps",
 short="feature intersection preserves acceptance",
 theorems="""`accepts_intersection_of_accepts` (line ~463): if feature vectors
`f` and `g` are accepted by `known`, their bitwise intersection is accepted.
The key fact is that AND cannot introduce an unknown required bit.""",
 hints="Unfold `Accepts`, `intersection`, and the feature-vector representation. Prove pointwise over bits/indices; `Nat.land_le`/bit lemmas may help. If required bits are a predicate over indices, show the AND bit is ≤ each input bit."),

"PC13": dict(target="LnLean/Proofs/Routing/GraphProps.lean", module="LnLean.Proofs.Routing.GraphProps",
 short="simplePaths are walks",
 theorems="""`simplePaths_walk` (line ~475): every path returned by
`Graph.simplePaths g src dst maxHops` is a `Walk` of enabled edges.""",
 hints="Induct on the `simplePaths` recursion / fuel. Each cons step must expose the `Adjacent` proof produced by the generator. Use the `Walk` constructors in the file."),

"PC14": dict(target="LnLean/Proofs/Routing/GossipProps.lean", module="LnLean.Proofs.Routing.GossipProps",
 short="gossip admission obligations",
 theorems="""(1) `accepted_update_signing_key_announced` (line ~872).
(2) `bindChannel_capacity_positive` (line ~883).
(3) `accepted_update_signature_length` (line ~892).
All three are marked as model/admission gaps in their docstrings.""",
 hints="Check whether any is actually derivable. If the wave-A model truly lacks the invariant (signingKey independent; capacity unconstrained; verifier abstract), do not fake it: keep the sorry, sharpen the docstring/marker with the exact missing field or admission check, and prove the strongest conditional version as a new theorem. This agent may legitimately close 0 sorries; honesty is the deliverable."),

"PC15": dict(target="LnLean/Proofs/Payment/MPPProps.lean", module="LnLean.Proofs.Payment.MPPProps",
 short="MPP running total",
 theorems="""The theorem at line ~648 with the MPP running-total obligation.
Read the exact statement and the plan/part definitions. Prove the prefix-sum
or total bound it states.""",
 hints="Induct on the parts list or use the accumulator invariant already stated. `omega` for the arithmetic; watch `Nat` subtraction."),

"PC16": dict(target="LnLean/Proofs/Payment/KeysendProps.lean", module="LnLean.Proofs.Payment.KeysendProps",
 short="keysend consistency",
 theorems="""The theorem at line ~444 with the keysend obligation. Read the
exact statement: it connects the keysend preimage, payment hash, amount, and
CLTV in the model.""",
 hints="Unfold `keysendToHtlc`/`keysendValid`; `simp` then `omega` or `rfl`. If it depends on the cryptographic hash function, keep the conditional hypothesis explicit."),
}

for name, j in JOBS.items():
    text = COMMON.format(name=name, short=j["short"], target=j["target"],
                         module=j["module"], theorems=j["theorems"].strip(),
                         hints=j["hints"].strip())
    (OUT / f"{name}.md").write_text(text, encoding="utf-8")
    print(name, len(text))
