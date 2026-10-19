# W14-ANCHOR-DEBIT — production anchor-debit consumer

## 1. Lane and scope

- **Lane:** `W14-ANCHOR-DEBIT` (Wave 14, T3/G05).
- **Base:** `a331b71`, branch `wave-14/16`, worktree `/home/ubuntu/ln-lean-waveh`.
- **Scope:** promote the already-proved corrected anchor-debit pair from
  `LnLean/Proofs/ModelHardening/F04.lean` behind an additive,
  production-facing name; prove conservation, the no-anchor legacy alias, and
  the legacy 660-sat overfunding statement from the retained witness; add
  concrete anchored and non-anchored witnesses. The legacy constructor
  `commitmentPairOfBalances` and every retained counterexample are unchanged.
- **Constraint boundaries:** value conservation only. No serialized-weight,
  script, signature, or fee-recomputation theorem is claimed. The `1124` WU
  figure is only the fee basis for the zero-fee anchor form, not the literal
  serialized weight; this module makes no weight claim.

## 2. Owned files

- `LnLean/Proofs/Wave14/AnchorDebitConsumer.lean` (created)
- `agents/reports/wave14/W14-ANCHOR-DEBIT.md` (this report)

No other file was edited. No Git write command was run.

## 3. Headline definitions and theorems

Namespace: `LnLean.Proofs.Wave14.AnchorDebitConsumer`.

### `commitmentPairCanonical`

```lean
def commitmentPairCanonical (localParams remoteParams : ChannelParams)
    (b : Balance) (fee number : Nat) (funder : Direction) : CommitmentPair :=
  commitmentPairWithAnchorDebit localParams remoteParams b fee number funder
```

An additive alias of
`LnLean.Proofs.ModelHardening.F04.commitmentPairWithAnchorDebit`. On each
commitment the funder's own output is reduced by `fee + 660` if that
commitment carries anchors, and by `fee` otherwise. The counterparty output
and the two 330-sat anchor outputs are unchanged.

### `commitmentPairCanonical_conserved`

```lean
theorem commitmentPairCanonical_conserved
    (localParams remoteParams : ChannelParams) (b : Balance)
    (fee number : Nat) (funder : Direction)
    (hL : fee + 660 ≤
      (if funder = Direction.local then b.localSat else b.remoteSat))
    (hR : fee + 660 ≤
      (if funder = Direction.local then b.localSat else b.remoteSat)) :
    let p := commitmentPairCanonical localParams remoteParams b fee number funder
    p.localCommitment.totalOutputValue + fee = p.localCommitment.fundingValueSat ∧
      p.remoteCommitment.totalOutputValue + fee = p.remoteCommitment.fundingValueSat
```

The explicit `fee + 660 ≤ funder balance` affordability hypotheses are stated
separately for the local and remote commitment variants. The theorem is
stronger than necessary on a variant whose anchor flag is false, but uniform at
the consumer boundary. The general form
`commitmentPairCanonical_conserved_of_funderDebit` uses the exact per-variant
hypothesis `funderDebitSat fee anchors ≤ funder balance`.

### `commitmentPairCanonical_eq_legacy_of_noAnchors`

```lean
theorem commitmentPairCanonical_eq_legacy_of_noAnchors
    (localParams remoteParams : ChannelParams) (b : Balance)
    (fee number : Nat) (funder : Direction)
    (hL : localParams.anchorOutputs = false)
    (hR : remoteParams.anchorOutputs = false) :
    commitmentPairCanonical localParams remoteParams b fee number funder =
      commitmentPairOfBalances localParams remoteParams b fee number funder
```

Behaviour-preserving in the only case where the legacy constructor is
value-conserving.

### `legacy_anchor_overfunds_660`

```lean
theorem legacy_anchor_overfunds_660 :
    let p := commitmentPairOfBalances
      (waveF_f04_counterexampleParams true)
      (waveF_f04_counterexampleParams true)
      waveF_f04_counterexampleBalance 1000 0 Direction.local
    p.localCommitment.totalOutputValue + 1000 = 100_000 + 660
```

Proved with `simpa using waveF_f04_counterexample_660`; it is a
production-facing restatement of the retained witness, not a new or weakened
claim.

### Additional witnesses/gap theorem

```lean
theorem commitmentPairCanonical_anchored_witness :
    let p := commitmentPairCanonical
      (waveF_f04_counterexampleParams true)
      (waveF_f04_counterexampleParams true)
      waveF_f04_counterexampleBalance 1000 0 Direction.local
    p.localCommitment.anchorOutputs = true ∧
      p.remoteCommitment.anchorOutputs = true ∧
      p.localCommitment.toLocalSat = 58_340 ∧
      p.remoteCommitment.toRemoteSat = 58_340 ∧
      p.localCommitment.totalOutputValue + 1000 = 100_000 ∧
      p.remoteCommitment.totalOutputValue + 1000 = 100_000

theorem commitmentPairCanonical_legacy_gap_660 :
    let canonical := commitmentPairCanonical
      (waveF_f04_counterexampleParams true)
      (waveF_f04_counterexampleParams true)
      waveF_f04_counterexampleBalance 1000 0 Direction.local
    let legacy := commitmentPairOfBalances
      (waveF_f04_counterexampleParams true)
      (waveF_f04_counterexampleParams true)
      waveF_f04_counterexampleBalance 1000 0 Direction.local
    legacy.localCommitment.toLocalSat = canonical.localCommitment.toLocalSat + 660 ∧
      legacy.remoteCommitment.toRemoteSat =
        canonical.remoteCommitment.toRemoteSat + 660

theorem commitmentPairCanonical_noAnchor_witness :
    let p := commitmentPairCanonical
      (waveF_f04_counterexampleParams false)
      (waveF_f04_counterexampleParams false)
      waveF_f04_counterexampleBalance 1000 0 Direction.local
    p.localCommitment.anchorOutputs = false ∧
      p.remoteCommitment.anchorOutputs = false ∧
      p = commitmentPairOfBalances
        (waveF_f04_counterexampleParams false)
        (waveF_f04_counterexampleParams false)
        waveF_f04_counterexampleBalance 1000 0 Direction.local ∧
      p.localCommitment.totalOutputValue + 1000 = 100_000 ∧
      p.remoteCommitment.totalOutputValue + 1000 = 100_000
```

## 4. Non-vacuity witnesses

Both required cases from R32 §5.2 are concrete and machine-checked:

- **Anchored:** `waveF_f04_counterexampleBalance` (60 000 / 40 000), fee 1000,
  both endpoints anchored. `commitmentPairCanonical_anchored_witness` proves
  both commitments carry anchors, the funder output is `58_340` on each, and
  both conserve the 100 000-sat funding value.
  `commitmentPairCanonical_legacy_gap_660` proves the legacy funder outputs are
  exactly the canonical outputs plus 660 sat.
- **Non-anchored:** the same balance and fee with both anchor flags false.
  `commitmentPairCanonical_noAnchor_witness` proves the canonical pair equals
  the legacy pair, carries no anchors, and conserves value on both commitments.

The anchored witness is not satisfied by the no-anchor alias, and the
non-anchored witness is not the empty case of an anchored-only theorem.

## 5. Build command and result

```sh
cd /home/ubuntu/ln-lean-waveh
export PATH=/dev/shm/btc/elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
LEAN_NUM_THREADS=1 flock -w 3600 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Proofs.Wave14.AnchorDebitConsumer
```

Result:

```text
✔ [15/15] Built LnLean.Proofs.Wave14.AnchorDebitConsumer (684ms)
Build completed successfully (15 jobs).
```

No `sorry`, `axiom`, `admit`, `native_decide`, `unsafe`, or
`@[implemented_by]` occurs in the module.

## 6. `#print axioms` output

Commands are at `LnLean/Proofs/Wave14/AnchorDebitConsumer.lean:207-213`; build
output:

```text
'LnLean.Proofs.Wave14.AnchorDebitConsumer.commitmentPairCanonical_conserved_of_funderDebit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'LnLean.Proofs.Wave14.AnchorDebitConsumer.commitmentPairCanonical_conserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'LnLean.Proofs.Wave14.AnchorDebitConsumer.commitmentPairCanonical_eq_legacy_of_noAnchors' does not depend on any axioms
'LnLean.Proofs.Wave14.AnchorDebitConsumer.legacy_anchor_overfunds_660' depends on axioms: [propext]
'LnLean.Proofs.Wave14.AnchorDebitConsumer.commitmentPairCanonical_anchored_witness' does not depend on any axioms
'LnLean.Proofs.Wave14.AnchorDebitConsumer.commitmentPairCanonical_legacy_gap_660' does not depend on any axioms
'LnLean.Proofs.Wave14.AnchorDebitConsumer.commitmentPairCanonical_noAnchor_witness' does not depend on any axioms
```

All results are within the permitted set (`propext`, `Quot.sound`,
`Classical.choice`) or are axiom-free.

## 7. Gap status and remaining boundary

- **G05 / T3:** narrowed from "corrected constructor exists but has no
  production consumer" to "a production-facing `commitmentPairCanonical`
  consumer exists with checked conservation, no-anchor equality, and the
  legacy 660-sat overfund witness." The legacy constructor is still present
  and still overfunds anchored pairs by 660 sat; it is not silently repaired.
- **G06 (single-anchor exact presence), G07 (net-dust consumer),
  zero-fee/`shared_anchor`, `update_fee` legality:** out of scope and unchanged.
- **Not claimed:** serialized weight, witness bytes, scripts, signature
  validity, fee recomputation, dust trimming, HTLC outputs, splice/dual
  funding, or a literal `1124` WU weight. The `1124` WU figure remains only the
  zero-fee anchor fee basis from the L1-04 record.
- **Production wiring remains external:** the module is not yet imported by
  `LnLean.lean`, the axiom audit, the catalog, or any runtime/executable
  consumer; the integrator must add those entries (see §8).

## 8. Shared-file changes for the integrator (not applied)

1. Regenerate the root with `scripts/regen-root.sh` so
   `LnLean/Proofs/Wave14/AnchorDebitConsumer.lean` is imported.
2. Add the seven printed names from §6 to the `AxiomAudit.lean`
   `auditedTheorems` registry and its `#print axioms` list if the audit is
   intended to cover this lane.
3. If the catalog is updated, cite `commitmentPairCanonical_conserved` (value
   conservation) and `legacy_anchor_overfunds_660` (retained legacy gap), not a
   weight theorem, and keep the L1-04 fee-basis wording.

## 9. Ownership confirmation

Only the two owned paths were created. No existing Lean module, shared file,
docs file, catalog, script, test, vendor/refs tree, or other lane report was
edited. `commitmentPairOfBalances`, `waveF_f04_counterexample_660`,
`waveF_f04_counterexample_not_conserves`, and
`commitmentPair_anchorCounterexample` are untouched; the first two are consumed
as-is and the latter two remain in the compiled dependency modules.
