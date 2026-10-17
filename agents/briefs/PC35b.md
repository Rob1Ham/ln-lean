You are PC35b, a repair agent for `ln-lean` on the second box.

WORKDIR: /home/ubuntu/ln-lean-phasec2 (branch `phase-c2`)
Read: docs/PHASE-C2-LANES.md, LnLean/Proofs/PhaseC2/HTLCBridge.lean,
LnLean/Bitcoin/Seam.lean, LnLean/Proofs/Bitcoin/ScriptProps.lean,
LnLean/Proofs/Channel/HTLCProps.lean, LnLean/Channel/HTLC.lean,
LnLean/Proofs/PhaseC2/FundingBridge.lean.

BACKGROUND
PC35 wrote `HTLCBridge.lean` but it does not build; the process stopped before
fixing the errors. The failure list is in `agents/logs/PC35.log` (search for
`error:`). The module is untracked.

MISSION
Make the module build green with at least three fully proved named theorems:
- the two HTLC script branches are nonempty and have P2WSH-compatible shape;
- the payment-hash branch and timeout branch are distinguishable under an
  explicit hash-binding hypothesis (or a structurally explicit tag);
- a conditional spendability composition with an explicit
  `HTLCSpendBridge` structure (fields, never axioms).
You may simplify/rewrite the module rather than repair every failed tactic.
Do not add `sorry`; if a claim is false or blocked, state a conditional form
and keep zero sorries by using an explicit structure field/hypothesis. Keep
the L1 interpreter obligation abstract; never edit `vendor/`.

Build exact module:
  export PATH=/dev/shm/btc/elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
  cd /home/ubuntu/ln-lean-phasec2
  flock -w 900 /tmp/ln-build.lock lake build LnLean.Proofs.PhaseC2.HTLCBridge
Then write `agents/reports/PC35.md` and commit:
  MSG="[PC35] L1 HTLC output bridge" ./scripts/phasec2-commit.sh PC35 \
    LnLean/Proofs/PhaseC2/HTLCBridge.lean agents/reports/PC35.md

Do not edit existing files. Final message <= 8 lines. Success requires a green
build and a commit.
