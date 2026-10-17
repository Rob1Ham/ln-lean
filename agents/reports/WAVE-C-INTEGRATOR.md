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

Wave C was one agent per proof file.  Every agent's own file builds, and the
full root build passes on the resulting branch.  No model module and no
existing theorem/lemma statement was changed; `check-wave-c.py` compares
against `b891a59` and enforces both rules.

## Per-file result

| Unit | File | Baseline | Final | Result |
|---|---|---:|---:|---|
| C01 | `LnLean/Proofs/Bitcoin/AnchorProps.lean` | 2 | 0 | closed |
| C02 | `LnLean/Proofs/Bitcoin/FundingProps.lean` | 2 | 1 | 1 open |
| C03 | `LnLean/Proofs/Bitcoin/ScriptProps.lean` | 3 | 0 | closed |
| C04 | `LnLean/Proofs/Channel/HTLCProps.lean` | 2 | 0 | closed |
| C05 | `LnLean/Proofs/Channel/ReserveProps.lean` | 1 | 1 | 1 open |
| C06 | `LnLean/Proofs/Channel/StateMachineProps.lean` | 1 | 0 | closed |
| C07 | `LnLean/Proofs/Conservation.lean` | 1 | 0 | closed |
| C08 | `LnLean/Proofs/Crypto/EcdsaProps.lean` | 2 | 0 | closed |
| C09 | `LnLean/Proofs/Crypto/Sha256Props.lean` | 1 | 0 | closed |
| C10 | `LnLean/Proofs/Payment/KeysendProps.lean` | 1 | 0 | closed |
| C11 | `LnLean/Proofs/Payment/MPPProps.lean` | 1 | 0 | closed |
| C12 | `LnLean/Proofs/Protocol/ChannelReestablishProps.lean` | 2 | 0 | closed |
| C13 | `LnLean/Proofs/Protocol/FeaturesProps.lean` | 1 | 0 | closed |
| C14 | `LnLean/Proofs/Routing/GossipProps.lean` | 3 | 3 | 3 open |
| C15 | `LnLean/Proofs/Routing/GraphProps.lean` | 1 | 0 | closed |
| C16 | `LnLean/Proofs/Wire/TLVProps.lean` | 1 | 0 | closed |
| **Total** | | **25** | **5** | **20 closed** |

`ScriptProps` and `GraphProps` retain their original `-- OBLIGATION:`
markers for traceability even though the `sorry` sites are gone.  A marker
without a `sorry` is a proved-or-retained target, not an open proof.

## Remaining obligations

| Obligation | Site | Why it remains open |
|---|---|---|
| `LN-FUND-001` | `FundingProps.lean:456` | The literal statement `witnessScript.parse = none` is **false** for the current parser; C02 mechanised the `some [...]` counterexample. The fix is a well-formedness/range hypothesis, not a proof of the current statement. |
| `LN-CH-101` | `ReserveProps.lean:586` | The unguarded ledger statement is **false** under truncated subtraction. C05 added and proved the guarded companion `committed_update_preserves_ledger_of_guard`; the original statement and marker are retained. |
| `LN-GOSSIP-001` | `GossipProps.lean:878` | The signing key is not linked to an announced node key. C14 mechanised the negation as `LN_GOSSIP_001_counterexample`. |
| `LN-GOSSIP-002` | `GossipProps.lean:887` | `ChannelAnnellation.capacitySat` is unconstrained. C14 mechanised the negation as `LN_GOSSIP_002_counterexample`. |
| `LN-GOSSIP-003` | `GossipProps.lean:897` | `SigVerifier` does not require `GossipSignature.Valid`. C14 mechanised the negation as `LN_GOSSIP_003_counterexample`. |

These are model gaps, not unfinished tactic scripts.  Closing them honestly
requires adding the missing invariants/guards to the model or proving a
corrected statement, whichever the project chooses.

## Cross-lane comparison

The other box independently ran 16 `phase-c` agents on the same files.  Its
`phase-c` head at comparison time was `2ccfca1`; it closed **19/25** sites and
left **6** open (`FundingProps` 2, `ReserveProps` 1, `GossipProps` 3).

Decision: **use the `wave-c/235` version for all 16 files.**

- `FundingProps`: `wave-c/235` has 1 open, `phase-c` has 2.  Wave C is strictly better.
- `ReserveProps`: both have the same single open obligation; the Wave-C version
  also contains the proved guarded companion, so it is retained.
- `GossipProps`: both have the same three false statements; the Wave-C version
  contains the private, `sorry`-free counterexamples and is retained.
- The other 13 files are closed in both lanes and all build here.  Keeping one
  coherent lane avoids mixing two different proof bodies in one file.

No file from `/home/ubuntu/ln-lean-phasec` was copied or merged, and no history
on `phase-c` or `main` was rewritten.

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

## Agent commits

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
