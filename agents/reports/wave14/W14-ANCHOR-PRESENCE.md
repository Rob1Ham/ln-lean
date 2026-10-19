# W14-ANCHOR-PRESENCE — exact anchor presence and net-dust consumer

## 1. Lane and scope

- **Lane:** `W14-ANCHOR-PRESENCE` (Wave 14).
- **Worktree / branch / base:** `/home/ubuntu/ln-lean-waveh`, `wave-14/16`, `a331b71`.
- **Scope:** additive exact-presence and net-dust consumer layer for anchor
  outputs on `CommitmentTx`. The lane defines an exact anchor-presence
  predicate/function, proves the BOLT 3 single-anchor exception for a
  concrete witness, and mechanizes the gross-vs-net dust mismatch witness.
- **No changes** to `Commitment.commitmentOutputs`, `CommitmentTx` semantics,
  `CommitmentTx.outputs`, `CommitmentTx.outputsNet`,
  `CommitmentTx.localAnchorOutput`, `CommitmentTx.remoteAnchorOutput`, or the
  catalog theorem `output_ordering`.

## 2. Owned files

Only these two files were written:

- `LnLean/Proofs/Wave14/AnchorPresenceConsumer.lean`
- `agents/reports/wave14/W14-ANCHOR-PRESENCE.md`

## 3. Headline definitions and theorems

All names are in namespace
`LnLean.Proofs.Wave14.AnchorPresenceConsumer`.

### Definitions

```lean
def hasUntrimmedHtlcNet (tx : CommitmentTx) : Prop :=
  ∃ h ∈ tx.commitment.htlcs, tx.dustLimitSat ≤ tx.netAmountSat h

def anchorNeeded (tx : CommitmentTx) : Direction → Prop
  | .local =>
      tx.dustLimitSat ≤ tx.commitment.toLocalSat ∨ hasUntrimmedHtlcNet tx
  | .remote =>
      tx.dustLimitSat ≤ tx.commitment.toRemoteSat ∨ hasUntrimmedHtlcNet tx

def localAnchorPresent (tx : CommitmentTx) : Bool
def remoteAnchorPresent (tx : CommitmentTx) : Bool
def localAnchorOutputExact (tx : CommitmentTx) : Option CommitmentTxOutput
def remoteAnchorOutputExact (tx : CommitmentTx) : Option CommitmentTxOutput
def outputsUnsortedExact (tx : CommitmentTx) : List CommitmentTxOutput
def outputsExact (tx : CommitmentTx) : List CommitmentTxOutput
```

The executable presence functions are the `Bool` encodings of
`anchorNeeded tx .local` / `anchorNeeded tx .remote`, conjoined with
`tx.commitment.anchorOutputs`. The exact output lists are the
`CommitmentTx.outputsUnsortedNet` construction with the two legacy
always-on anchor fields replaced by the exact presence fields; the non-anchor
and HTLC parts are unchanged.

### Headline theorems and exact statements

```lean
theorem exactAnchorPresence_spec (tx : CommitmentTx) :
    (localAnchorOutputExact tx ≠ none ↔
      tx.commitment.anchorOutputs = true ∧
        (tx.dustLimitSat ≤ tx.commitment.toLocalSat ∨
          hasUntrimmedHtlcNet tx)) ∧
    (remoteAnchorOutputExact tx ≠ none ↔
      tx.commitment.anchorOutputs = true ∧
        (tx.dustLimitSat ≤ tx.commitment.toRemoteSat ∨
          hasUntrimmedHtlcNet tx)) ∧
    (tx.commitment.anchorOutputs = false →
      localAnchorOutputExact tx = none ∧
        remoteAnchorOutputExact tx = none)

theorem exactAnchors_eq_legacy_of_both_needed (tx : CommitmentTx)
    (hflag : tx.commitment.anchorOutputs = true)
    (hl : tx.dustLimitSat ≤ tx.commitment.toLocalSat)
    (hr : tx.dustLimitSat ≤ tx.commitment.toRemoteSat) :
    localAnchorOutputExact tx = tx.localAnchorOutput ∧
      remoteAnchorOutputExact tx = tx.remoteAnchorOutput

theorem singleAnchor_case :
    singleAnchorTx.commitment.anchorOutputs = true ∧
      singleAnchorTx.commitment.toLocalSat = 0 ∧
      singleAnchorTx.commitment.htlcs = [] ∧
      singleAnchorTx.dustLimitSat = 330 ∧
      localAnchorOutputExact singleAnchorTx = none ∧
      remoteAnchorOutputExact singleAnchorTx =
        some (CommitmentTxOutput.remoteAnchor singleAnchorTx.remoteAnchorScript) ∧
      (outputsUnsortedExact singleAnchorTx |>.filter isAnchorOutput).length = 1 ∧
      (singleAnchorTx.outputsUnsorted.filter isAnchorOutput).length = 2 ∧
      ((outputsUnsortedExact singleAnchorTx).map (fun o => o.valueSat)).sum = 50_330 ∧
      (singleAnchorTx.outputsUnsorted.map (fun o => o.valueSat)).sum = 50_660

theorem netDust_mismatch :
    netDustGross = 1000 ∧
      netDustSecondStageFee = 167 ∧
      netDustLimit = 900 ∧
      netDustNet = 833 ∧
      netDustTx.htlcOutput netDustHtlc ≠ none ∧
      netDustTx.htlcOutputNet netDustHtlc = none ∧
      CommitmentTxOutput.htlc netDustHtlc
          (netDustTx.htlcScript netDustHtlc) ∈ netDustTx.outputs ∧
      CommitmentTxOutput.htlc netDustHtlc
          (netDustTx.htlcScript netDustHtlc) ∉ netDustTx.outputsNet
```

Supporting lemmas include `hasUntrimmedHtlcNetB_iff`,
`localAnchorPresent_eq_true_iff`, `remoteAnchorPresent_eq_true_iff`,
`localAnchorOutputExact_eq_some_iff`, `remoteAnchorOutputExact_eq_some_iff`,
the two `_ne_none_iff` lemmas, and `outputsExact_perm`.

## 4. Concrete non-vacuity witnesses

### Single-anchor witness

`singleAnchorTx` is a closed `CommitmentTx` value:

- `commitment.toLocalSat = 0`;
- `commitment.toRemoteSat = 50_000`;
- `commitment.htlcs = []`;
- `dustLimitSat = 330`;
- `commitment.anchorOutputs = true`.

The theorem `singleAnchor_case` proves all of the following:

- the exact local anchor is absent (`localAnchorOutputExact singleAnchorTx = none`);
- the exact remote anchor is the 330-sat remote anchor;
- the exact unsorted output list contains exactly **one** anchor;
- the legacy rich unsorted list contains **two** anchors;
- the exact output value is `50_330` sat;
- the legacy rich output value is `50_660` sat.

So the witness is not vacuous: one side is genuinely trimmed, the other is
genuinely used, and the exact/legacy separation is a concrete 330-sat value
difference.

### Net-dust witness

`netDustTx` carries one HTLC with:

- gross `amountSat = 1000`;
- second-stage fee `167`;
- net `netAmountSat = 833`;
- owner's dust limit `900`;
- no anchors and no `to_local`/`to_remote` output.

The theorem `netDust_mismatch` proves:

- `netDustNet = 833`;
- `htlcOutput` (gross consumer) is not `none`;
- `htlcOutputNet` (net path) is `none`;
- the HTLC output **is** in `netDustTx.outputs` (the existing gross list);
- the HTLC output **is not** in `netDustTx.outputsNet` (the existing net list).

The statement uses the existing `CommitmentTx.htlcOutput`,
`CommitmentTx.htlcOutputNet`, `CommitmentTx.outputs`, and
`CommitmentTx.outputsNet` definitions. It does not redefine `output_ordering`
or `outputsNet`.

## 5. Build

Command (under the shared build lock, only the scoped module):

```sh
cd /home/ubuntu/ln-lean-waveh
export PATH=/dev/shm/btc/elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
LEAN_NUM_THREADS=1 flock -w 3600 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Proofs.Wave14.AnchorPresenceConsumer
```

Result:

```text
Build completed successfully (12 jobs).
```

No `sorry`, `axiom`, `admit`, `native_decide`, `unsafe`, or
`@[implemented_by]` occurs in the module (the only textual `axiom` is the
required `#print axioms` commands).

## 6. `#print axioms` output

```text
info: LnLean/Proofs/Wave14/AnchorPresenceConsumer.lean:409:0: 'LnLean.Proofs.Wave14.AnchorPresenceConsumer.exactAnchorPresence_spec' depends on axioms: [propext, Quot.sound]
info: LnLean/Proofs/Wave14/AnchorPresenceConsumer.lean:410:0: 'LnLean.Proofs.Wave14.AnchorPresenceConsumer.singleAnchor_case' depends on axioms: [propext]
info: LnLean/Proofs/Wave14/AnchorPresenceConsumer.lean:411:0: 'LnLean.Proofs.Wave14.AnchorPresenceConsumer.netDust_mismatch' depends on axioms: [propext, Quot.sound]
info: LnLean/Proofs/Wave14/AnchorPresenceConsumer.lean:412:0: 'LnLean.Proofs.Wave14.AnchorPresenceConsumer.exactAnchors_eq_legacy_of_both_needed' depends on axioms: [propext, Quot.sound]
```

Only `propext`, `Quot.sound`, and `Classical.choice` are permitted; the
observed output uses `propext` and `Quot.sound` only (no `Classical.choice`,
no `sorryAx`).

## 7. Review gap status

This lane addresses R32 §4 T3's anchor family, specifically the two
consumer-side gaps split out in R32 §3:

- **G06 single-anchor exception — narrowed.** The exact BOLT 3 presence rule
  is now defined and proved for the additive `CommitmentTx` carrier, including
  a concrete `to_local = 0`, no-HTLC, one-anchor witness. The legacy rich
  functions `CommitmentTx.localAnchorOutput` / `remoteAnchorOutput` and the
  existing `CommitmentTx.outputsUnsorted` / `outputs` still emit both anchors
  whenever the flag is true. Closing G06 at the production consumer requires
  wiring `localAnchorOutputExact` / `remoteAnchorOutputExact` (or
  `outputsExact`) into the existing consumers, which is intentionally **not**
  done here because it would change existing `CommitmentTx` output semantics.
- **G07 net-dust consumer mismatch — narrowed/mechanized.** The gross-vs-net
  separation (gross 1000, second-stage fee 167, dust 900) is now a concrete,
  kernel-checked witness over the existing definitions. The catalog theorem
  `output_ordering` still consumes the gross `CommitmentTx.outputs`; no
  statement in this lane claims otherwise. Switching that consumer to
  `outputsNet` remains an integration change.

**Remaining external/narrow boundaries:**

- `CommitmentTx` still takes the owner's `dustLimitSat` and script bytes as
  caller-supplied fields. This lane inherits the model's existing
  caller-supplied-script limitation.
- `zero_fee_commitments` and `shared_anchor` are not modelled.
- The exact anchor presence uses the **net** HTLC dust test
  (`netAmountSat`), matching `outputsNet`; a caller leaving the default
  identity net projection gets the legacy gross-equals-net behaviour.
- The 660-sat funder anchor debit (G05) is a separate target and is not
  restated here.

**Retained counterexamples:** `waveD_d12_output_ordering_fails`,
`waveD_d12_cltv_tiebreak_not_recoverable`, and
`waveD_d12_dust_trimming_requires_filter` are untouched and still typecheck;
the gross/net distinction in `CommitmentTx.outputs` versus
`CommitmentTx.outputsNet` is unchanged and is the subject of the new mismatch
witness.

## 8. Shared-file changes for the integrator (not applied)

The lane did not edit shared files. The integrator should:

1. Add `import LnLean.Proofs.Wave14.AnchorPresenceConsumer` to the generated
   Wave 14 root (`LnLean/Proofs/Wave14.lean`), or run `scripts/regen-root.sh`.
2. Decide whether to add the four headline names to
   `LnLean/Proofs/PhaseC3/AxiomAudit.lean` (`#print axioms` commands and
   `auditedTheorems`). The lane already prints them locally; the global audit
   registry was not edited.
3. If desired, update the G06/G07 wording in `docs/OPEN-ISSUES.md` to say the
   exact-presence and net-dust **models and witnesses** exist additively,
   while the production `outputs` consumer is still gross and still emits both
   anchors. Do not mark G06/G07 fully closed.
4. If a catalog row is desired for the lane, add a separate row rather than
   changing `LN-CH-003`/`output_ordering`; the existing catalog theorem keeps
   its gross semantics.

## 9. Ownership confirmation

No shared file, existing Lean module, script, test, `docs/` file, catalog
entry, or other lane's report was edited. `git status` shows only untracked
Wave 14 lane files created by the parallel lanes plus this lane's two owned
files; no tracked file was modified.
