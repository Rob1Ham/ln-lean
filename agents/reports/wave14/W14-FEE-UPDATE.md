# W14-FEE-UPDATE — checked `update_fee` legality and a zero-fee/shared-anchor carrier

## 1. Lane and scope

- **Lane:** `W14-FEE-UPDATE` (Wave 14).
- **Worktree / branch / base:** `/home/ubuntu/ln-lean-waveh`, `wave-14/16`, `a331b71`.
- **Scope:** additive channel-level legality wrapper for BOLT 2
  `update_fee`, reusing the existing `checkedFeeUpdate` affordability check,
  plus an additive `CommitmentVersion` / zero-fee / `shared_anchor` sidecar.
- **Not changed:** `LnLean.Channel.State.Step`, its `updateFee` constructor,
  `LnLean.Channel.Fee.updateFee` / `updateChannelFee`,
  `LnLean.Channel.Commitment.commitmentFee`, and every retained
  counterexample.  The old unguarded `Step.updateFee` path remains and is
  explicitly shown to still admit the insufficient update.

## 2. Owned files

Only these two files were written:

- `LnLean/Proofs/Wave14/FeeUpdateLegality.lean`
- `agents/reports/wave14/W14-FEE-UPDATE.md`

No shared file, catalogue file, docs file, script, or other lane's file was
edited.

## 3. Headline definitions and theorems

All names are in namespace
`LnLean.Proofs.Wave14.FeeUpdateLegality`.

### Definitions

```lean
structure FeeUpdateRequest where
  sender : Direction
  rate : FeeRate
  weight : Weight
  paid : Msat

inductive CommitmentVersion where
  | v2
  | v3ZeroFee

def baseFeeFor (version : CommitmentVersion) (r : FeeRate) (w : Weight) : Msat
def anchorCountFor (version : CommitmentVersion) (anchors : Bool) : Nat
def sharedAnchorAmount (remainingSat : Nat) : Nat

structure CommitmentVersionCarrier where
  version : CommitmentVersion
  anchors : Bool
  feerate : FeeRate
  weight : Weight

def FeeUpdateAllowed (c : Channel) (version : CommitmentVersion)
    (funder : Direction) (req : FeeUpdateRequest) : Prop :=
  c.phase = ChannelPhase.normal ∧
  version = CommitmentVersion.v2 ∧
  req.sender = funder ∧
  feeSufficient req.rate req.weight req.paid

def checkedFeeStep (c : Channel) (version : CommitmentVersion)
    (funder : Direction) (req : FeeUpdateRequest) : Option Channel
```

`checkedFeeStep` checks phase / version / funder, then delegates the fee
affordability part to `LnLean.Proofs.Channel.FeeProps.checkedFeeUpdate`.
On success it returns exactly `updateChannelFee c req.rate`, i.e. the
successor of `Step.updateFee`.

`baseFeeFor` is `feeForWeight r w` on `v2` and `Msat.zero` on `v3ZeroFee`;
`anchorCountFor` is `2`/`0` on `v2` depending on the anchor flag and `1` on
`v3ZeroFee`; `sharedAnchorAmount n = if n < 240 then n else 240`.

### Headline theorem statements

```lean
theorem checkedFeeStep_some_iff {c c' : Channel}
    {version : CommitmentVersion} {funder : Direction}
    {req : FeeUpdateRequest} :
    checkedFeeStep c version funder req = some c' ↔
      FeeUpdateAllowed c version funder req ∧
        c' = updateChannelFee c req.rate

theorem checkedFeeStep_refines_updateFee {c c' : Channel}
    {version : CommitmentVersion} {funder : Direction}
    {req : FeeUpdateRequest}
    (h : checkedFeeStep c version funder req = some c') :
    Step c (ProtocolEvent.updateFee req.rate) c'

theorem checkedFeeStep_feerate ... :
    c'.localEndpoint.params.feerate = req.rate

theorem checkedFeeStep_phase ... : c'.phase = c.phase

theorem checkedFeeStep_sufficient ... :
    feeSufficient req.rate req.weight req.paid

theorem checkedFeeStep_sound ... :
    req.sender = funder ∧ feeSufficient req.rate req.weight req.paid

theorem nonFunder_update_not_allowed {c : Channel}
    {version : CommitmentVersion} {funder : Direction}
    {req : FeeUpdateRequest} (hne : req.sender ≠ funder) :
    ¬ FeeUpdateAllowed c version funder req

theorem nonFunder_checkedFeeStep_none ... (hne : req.sender ≠ funder) :
    checkedFeeStep c version funder req = none

theorem insufficient_update_rejected {c : Channel}
    {version : CommitmentVersion} {funder : Direction}
    {req : FeeUpdateRequest}
    (h : ¬ feeSufficient req.rate req.weight req.paid) :
    checkedFeeStep c version funder req = none

theorem zeroFee_update_not_allowed {c : Channel} {funder : Direction}
    {req : FeeUpdateRequest} :
    ¬ FeeUpdateAllowed c CommitmentVersion.v3ZeroFee funder req

theorem zeroFee_checkedFeeStep_none ... :
    checkedFeeStep c CommitmentVersion.v3ZeroFee funder req = none

theorem baseFeeFor_v2_commitmentFee (r : FeeRate) (c : Commitment) :
    baseFeeFor .v2 r c.weight = commitmentFee r c

theorem baseFeeFor_v3 (r : FeeRate) (w : Weight) :
    baseFeeFor .v3ZeroFee r w = Msat.zero

theorem anchorCountFor_v3 (anchors : Bool) :
    anchorCountFor .v3ZeroFee anchors = 1

theorem sharedAnchorAmount_le (remainingSat : Nat) :
    sharedAnchorAmount remainingSat ≤ 240
```

## 4. Concrete non-vacuity witnesses

The demo channel is a normal-phase, zero-HTLC channel.  The valid request has
weight `724` (`commitmentWeight false 0`), rate `1000` msat/kw, and paid fee
`1000` msat, so the required `724` msat is covered.  The insufficient request
uses rate `2000` msat/kw at the same weight and paid fee; the required
`1448` msat is not covered.

```lean
theorem demo_valid_update_allowed :
    FeeUpdateAllowed demoChannel CommitmentVersion.v2 Direction.local
      demoValidRequest := by decide

theorem demo_valid_update_step :
    checkedFeeStep demoChannel CommitmentVersion.v2 Direction.local
        demoValidRequest =
      some (updateChannelFee demoChannel ⟨1000⟩)

theorem demo_valid_update_refines_Step :
    ∃ c' : Channel,
      Step demoChannel (ProtocolEvent.updateFee ⟨1000⟩) c' ∧
        c' = updateChannelFee demoChannel ⟨1000⟩

theorem demo_insufficient_update_rejected :
    checkedFeeStep demoChannel CommitmentVersion.v2 Direction.local
        demoInsufficientRequest = none

theorem demo_nonFunder_update_rejected :
    checkedFeeStep demoChannel CommitmentVersion.v2 Direction.local
        demoNonFunderRequest = none

theorem demo_zeroFee_update_rejected :
    checkedFeeStep demoChannel CommitmentVersion.v3ZeroFee Direction.local
        demoValidRequest = none
```

The unguarded path is retained as an explicit separation:

```lean
theorem unguarded_updateFee_admits_insufficient :
    ∃ c' : Channel,
      Step demoChannel (ProtocolEvent.updateFee ⟨2000⟩) c'
```

The zero-fee carrier witness is `zeroFeeWitness`
(`version := v3ZeroFee`, `feerate := 0`, `anchors := false`):

```lean
theorem zeroFee_sharedAnchor_separates :
    zeroFeeWitness.version = CommitmentVersion.v3ZeroFee ∧
      zeroFeeWitness.baseFee = Msat.zero ∧
      zeroFeeWitness.anchorCount = 1 ∧
      legacyAnchoredWitness.anchorCount = 2

theorem sharedAnchorAmount_witnesses :
    sharedAnchorAmount 0 = 0 ∧ sharedAnchorAmount 1000 = 240
```

## 5. Build command and result

```sh
cd /home/ubuntu/ln-lean-waveh
export PATH=/dev/shm/btc/elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
LEAN_NUM_THREADS=1 flock -w 3600 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Proofs.Wave14.FeeUpdateLegality
```

Result:

```
⚠ [15/15] Built LnLean.Proofs.Wave14.FeeUpdateLegality (860ms)
Build completed successfully (15 jobs).
```

The only warnings are Lean deprecation notices for `if_pos`/`if_neg` in the
wrapper proofs.  There are no `sorry`, `axiom`, `admit`, `native_decide`,
`unsafe`, or `@[implemented_by]` uses.

## 6. `#print axioms` output

```
info: 'LnLean.Proofs.Wave14.FeeUpdateLegality.checkedFeeStep_some_iff' depends on axioms: [propext]
info: 'LnLean.Proofs.Wave14.FeeUpdateLegality.checkedFeeStep_refines_updateFee' depends on axioms: [propext]
info: 'LnLean.Proofs.Wave14.FeeUpdateLegality.nonFunder_update_not_allowed' does not depend on any axioms
info: 'LnLean.Proofs.Wave14.FeeUpdateLegality.insufficient_update_rejected' does not depend on any axioms
info: 'LnLean.Proofs.Wave14.FeeUpdateLegality.zeroFee_update_not_allowed' does not depend on any axioms
info: 'LnLean.Proofs.Wave14.FeeUpdateLegality.demo_valid_update_allowed' does not depend on any axioms
info: 'LnLean.Proofs.Wave14.FeeUpdateLegality.demo_valid_update_refines_Step' depends on axioms: [propext]
info: 'LnLean.Proofs.Wave14.FeeUpdateLegality.demo_insufficient_update_rejected' does not depend on any axioms
info: 'LnLean.Proofs.Wave14.FeeUpdateLegality.demo_nonFunder_update_rejected' does not depend on any axioms
info: 'LnLean.Proofs.Wave14.FeeUpdateLegality.unguarded_updateFee_admits_insufficient' does not depend on any axioms
info: 'LnLean.Proofs.Wave14.FeeUpdateLegality.zeroFee_sharedAnchor_separates' does not depend on any axioms
```

Only `propext` appears, which is inside the allowed set.  No headline theorem
uses `Classical.choice`, `Quot.sound`, or `sorryAx`.

## 7. Gap status

- **G15 (`update_fee` legality), narrowed to a checked wrapper.**  The lane
  now has a machine-checked predicate and executable wrapper that require
  normal phase, the declared funder, a non-zero-fee version, and paid-fee
  sufficiency; it proves non-funder rejection, insufficient-fee rejection,
  zero-fee rejection, soundness, and refinement to `Step.updateFee`.
  Remaining boundary: `Step.updateFee` itself is deliberately unchanged, so
  a direct `Step` derivation can still be built without the wrapper.  The
  `Channel` record has no funder field; `funder` is a caller-supplied
  local-view parameter.  Both facts are stated in the module docstring and
  are not hidden.
- **G16 (zero-fee / `shared_anchor`), partially narrowed.**  The additive
  sidecar provides a version tag, a zero base fee, an exact anchor count, the
  `min(remaining, 240)` shared-anchor amount rule, and concrete witnesses.
  It is **not** wired into `Commitment`, `ChannelParams`, `Step`, or the
  catalogue `commitmentFee`.  Single-anchor exact presence and the net-dust
  consumer remain the separate W14-ANCHOR-PRESENCE lane's territory.

Nothing in this lane claims LDK equality, reserve affordability, dust
exposure, relay policy, or wire-level `update_fee` handling.

## 8. Shared-file changes for the integrator (not applied)

1. **Root import.**  Add `import LnLean.Proofs.Wave14.FeeUpdateLegality` to
   the generated root (`LnLean/Proofs/Wave14.lean` or the regen-root output)
   via `scripts/regen-root.sh`; do not hand-edit the generated file.
2. **Axiom audit.**  If the lane is promoted into the audited catalogue, add
   the eleven names listed in §6 to `auditedTheorems` and add matching
   `#print axioms` lines in `LnLean/Proofs/PhaseC3/AxiomAudit.lean`.
3. **Catalogue / docs.**  If a catalogue row is desired, map G15 to
   `checkedFeeStep_refines_updateFee`, `nonFunder_update_not_allowed`,
   `insufficient_update_rejected` and G16 to
   `zeroFee_sharedAnchor_separates`, with wording: "wrapper-level
   `update_fee` legality; `Step.updateFee` unchanged" and "zero-fee/shared
   anchor sidecar; `commitmentFee` unchanged; not wired into `Step`".  Do
   not describe the sidecar as a full zero-fee commitment implementation.
4. **No other shared change is required.**  No existing Lean module, script,
   test, or docs file needs a semantic edit for this module to build.

## 9. No shared or other-lane file edited

Confirmed.  The only writes were
`LnLean/Proofs/Wave14/FeeUpdateLegality.lean` and this report.  The
pre-existing untracked files under `LnLean/Proofs/Wave14/`,
`agents/reports/wave14/`, `agents/swarm/WAVE-14.md`, and
`scripts/check-assurance-coverage.py` were not modified by this lane.
