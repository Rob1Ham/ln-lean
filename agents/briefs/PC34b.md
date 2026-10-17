You are PC34b, a focused bridge-proof agent for `ln-lean` on the second box.

WORKDIR: /home/ubuntu/ln-lean-phasec2 (branch `phase-c2`)
Read: docs/PHASE-C2-LANES.md, LnLean/Bitcoin/Seam.lean,
LnLean/Channel/Commitment.lean, LnLean/Proofs/Channel/CommitmentTxProps.lean,
LnLean/Proofs/Channel/BreachProps.lean, LnLean/Proofs/PhaseC2/FundingBridge.lean,
LnLean/Proofs/PhaseC2/PenaltyBridge.lean.

BACKGROUND
The original PC34 agent spent its time reading the vendored L1 interpreter and
did not write a module. Do not repeat that. Keep the bridge abstract and
explicit; never edit `vendor/`.

MISSION
Create `LnLean/Proofs/PhaseC2/CommitmentBridge.lean` with:
- a small `CommitmentL1Bridge` structure with explicit fields
  `spends : Tx → OutPoint → Prop`, `accepted : Tx → Prop`,
  `controls : Script → Prop`, and the bridge laws you actually use;
- proved script-shape/size lemmas for `toLocalScript` and `toRemoteScript`
  (e.g. P2WSH size, nonempty template, CSV field presence where the model
  exposes it);
- a conditional spendability composition: a to-local spend accepted by the
  bridge is controlled by the honest holder after the contest delay or by the
  revocation key; a to-remote spend is controlled by the remote holder;
- at least three named theorems fully proved, no `sorry`, no `axiom`.
If a property is not derivable from the wave-A model, state the strongest
true conditional form with the missing field explicit and mark it
`-- OBLIGATION: PC2-COMMIT-...` only if a `sorry` is unavoidable. Prefer zero
sorries by making the missing law a structure field.

Build exact module:
  export PATH=/dev/shm/btc/elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
  cd /home/ubuntu/ln-lean-phasec2
  flock -w 900 /tmp/ln-build.lock lake build LnLean.Proofs.PhaseC2.CommitmentBridge
Then write `agents/reports/PC34.md` and commit:
  MSG="[PC34] L1 commitment output bridge" ./scripts/phasec2-commit.sh PC34 \
    LnLean/Proofs/PhaseC2/CommitmentBridge.lean agents/reports/PC34.md

Do not edit existing files. Final message <= 8 lines. Success requires a green
build and a commit.
