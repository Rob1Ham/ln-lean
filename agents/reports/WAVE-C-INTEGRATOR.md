# Wave-C integrator report

- Date: `2026-10-17`
- Branch: `wave-c/235`
- Base: `b891a59` (`main` after wave B)
- Agents: **16/16 exited with RC 0**
- Per-file module builds: **16/16 RC 0**
- Full root build: **77 jobs, RC 0**
- Policy gate: `check.sh` **OK** (`files=69 obligations=32 sorry_in_proofs=5`)
- Vendor integrity: **OK**
- Remaining `sorry` sites: **5** (down from 25)
- Proof declarations after integration: **1563**

Wave C was one agent per proof file.  Every agent's own file builds, and the
full root build passes on the resulting branch.  No model module and no
existing theorem/lemma statement was changed; `check-wave-c.py` compares
against `b891a59` and enforces both rules.

## Integration note

The other box's `phase-c` lane finished after the first comparison.  Its
final head is `cb3a125` (`PC02` closed the second `FundingProps` site), so
both lanes finished at **20/25** closed and **5** open.  The final branch is
a whole-file selection:

- the 13 files closed by Wave C keep their `wave-c/235` versions;
- the three files that remain open (`FundingProps`, `ReserveProps`,
  `GossipProps`) use the `phase-c` versions, because they add proved
  conditional forms and mechanized counterexamples while leaving the same
  five statements open;
- no theorem body from one lane was merged into the other lane's file.

## Per-file result

| Unit | File | Baseline | Final | Source |
|---|---|---:|---:|---|
| C01 | `LnLean/Proofs/Bitcoin/AnchorProps.lean` | 2 | 0 | wave-c |
| C02 | `LnLean/Proofs/Bitcoin/FundingProps.lean` | 2 | 1 | phase-c |
| C03 | `LnLean/Proofs/Bitcoin/ScriptProps.lean` | 3 | 0 | wave-c |
| C04 | `LnLean/Proofs/Channel/HTLCProps.lean` | 2 | 0 | wave-c |
| C05 | `LnLean/Proofs/Channel/ReserveProps.lean` | 1 | 1 | phase-c |
| C06 | `LnLean/Proofs/Channel/StateMachineProps.lean` | 1 | 0 | wave-c |
| C07 | `LnLean/Proofs/Conservation.lean` | 1 | 0 | wave-c |
| C08 | `LnLean/Proofs/Crypto/EcdsaProps.lean` | 2 | 0 | wave-c |
| C09 | `LnLean/Proofs/Crypto/Sha256Props.lean` | 1 | 0 | wave-c |
| C10 | `LnLean/Proofs/Payment/KeysendProps.lean` | 1 | 0 | wave-c |
| C11 | `LnLean/Proofs/Payment/MPPProps.lean` | 1 | 0 | wave-c |
| C12 | `LnLean/Proofs/Protocol/ChannelReestablishProps.lean` | 2 | 0 | wave-c |
| C13 | `LnLean/Proofs/Protocol/FeaturesProps.lean` | 1 | 0 | wave-c |
| C14 | `LnLean/Proofs/Routing/GossipProps.lean` | 3 | 3 | phase-c |
| C15 | `LnLean/Proofs/Routing/GraphProps.lean` | 1 | 0 | wave-c |
| C16 | `LnLean/Proofs/Wire/TLVProps.lean` | 1 | 0 | wave-c |
| **Total** | | **25** | **5** | **20 closed** |

`ScriptProps` and `GraphProps` retain their original `-- OBLIGATION:`
markers for traceability even though the `sorry` sites are gone.  A marker
without a `sorry` is a proved-or-retained target, not an open proof.

## Remaining obligations

| Obligation | Site | Why it remains open |
|---|---|---|
| `LN-FUND-001` | `FundingProps.lean:679` | The literal statement `witnessScript.parse = none` is **false** for the current parser; `PC02` mechanised the `some [...]` counterexample and proved `witnessScript_parse_eq_none_of_wellFormed`. The fix is a well-formedness/range hypothesis, not a proof of the current statement. |
| `LN-CH-101` | `ReserveProps.lean:604` | The unguarded ledger statement is **false** under truncated subtraction. `PC09` mechanised the counterexample and proved `committed_update_preserves_ledger_of_le` under the BOLT 2 affordability guard; the original statement and marker are retained. |
| `LN-GOSSIP-001` | `GossipProps.lean:958` | The signing key is not linked to an announced node key. `PC14` proved a conditional admission form and mechanised the counterexample. |
| `LN-GOSSIP-002` | `GossipProps.lean:1016` | `ChannelAnnellation.capacitySat` is unconstrained. `PC14` proved a conditional positive-capacity form and mechanised the counterexample. |
| `LN-GOSSIP-003` | `GossipProps.lean:1050` | `SigVerifier` does not require `GossipSignature.Valid`. `PC14` proved a conditional length-respecting form and mechanised the counterexample. |

These are model gaps, not unfinished tactic scripts.  Closing them honestly
requires adding the missing invariants/guards to the model or proving a
corrected statement, whichever the project chooses.

## Cross-lane comparison

The other box independently ran 16 `phase-c` agents on the same files.  At
its final head `cb3a125`, it also closed **20/25** sites and left the same
**5** open (`FundingProps` 1, `ReserveProps` 1, `GossipProps` 3).

The tie was resolved per file:

- For the three open files, the `phase-c` versions add proved conditional
  theorems (`witnessScript_parse_eq_none_of_wellFormed`,
  `committed_update_preserves_ledger_of_le`, and the three
  `*_of_*` gossip admission lemmas) plus mechanized counterexamples, so they
  are retained.
- For the 13 closed files, the Wave-C versions are retained; each exact
  module builds, and `check-wave-c.py` confirms no statement was removed.
- Whole files were selected; no two competing proof bodies were merged into
  one theorem.

No file from `/home/ubuntu/ln-lean-phasec` was edited, and no history on
`phase-c` or `main` was rewritten.  The selected files were read from
`phase-c` under the isolation rules in `agents/WAVE-C-PLAN.md`.

## Gate commands

```sh
export PATH=/dev/shm/btc/elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
cd /home/ubuntu/ln-lean

python3 scripts/check-wave-c.py --build
./scripts/integrate-c.sh
./scripts/finalize.sh
```

Expected final summary:

```text
wave-c final sorry sites: 5 (closed 20)
check-wave-c: OK
check: OK
```

## Commits

The 16 Wave-C agent commits are on `wave-c/235`:

```text
69ea346 [C13] close proof obligations in FeaturesProps
0d76c24 [C10] close proof obligations in KeysendProps
0874188 [C15] close proof obligations in GraphProps
2c1f985 [C04] close proof obligations in HTLCProps
d6cf8a5 [C01] close proof obligations in AnchorProps
ad96c06 [C08] close proof obligations in EcdsaProps
db06785 [C06] close proof obligations in StateMachineProps
53beccc [C05] close proof obligations in ReserveProps
0cd10d3 [C03] close proof obligations in ScriptProps
03df878 [C11] close proof obligations in MPPProps
685abc1 [C14] close proof obligations in GossipProps
aac4fd2 [C12] close proof obligations in ChannelReestablishProps
7e81e19 [C07] close proof obligations in Conservation
184b4de [C16] close proof obligations in TLVProps
cfb0907 [C09] close proof obligations in Sha256Props
6d71ce3 [C02] close proof obligations in FundingProps
```

The initial integration commit is `dfaa998`; the hybrid whole-file update is
the current tip of `wave-c/235`.  The other lane's final head is `cb3a125`.
