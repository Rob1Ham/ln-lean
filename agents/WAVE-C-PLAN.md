# Wave C — proof closure

This wave removes the remaining `sorry` sites from the two-wave scaffold.  It
is intentionally separate from the other box's `phase-c` work.

## Branch and isolation

* This box (`.235`) owns branch **`wave-c/235`**, based on `main` at
  `b891a59`.
* The other box (`.110`) owns its own clone at
  `/home/ubuntu/ln-lean-phasec` and its own `phase-c` branch.  No agent on
  this box may edit that tree, branch, or its uncommitted files.
* `main` is not written by this wave.  Integration is done on
  `wave-c/235`; a pull request or explicit merge is a separate decision.

## Work split

One agent per proof file, so no two agents write the same file.  The 25
remaining `sorry` sites are distributed as follows.

| Agent | File | Module | Open obligations |
|---|---|---|---|
| C01 | `LnLean/Proofs/Bitcoin/AnchorProps.lean` | `LnLean.Proofs.Bitcoin.AnchorProps` | `LN-ANCHOR-007`, `LN-ANCHOR-008` |
| C02 | `LnLean/Proofs/Bitcoin/FundingProps.lean` | `LnLean.Proofs.Bitcoin.FundingProps` | `LN-FUND-001`, `LN-FUND-002` |
| C03 | `LnLean/Proofs/Bitcoin/ScriptProps.lean` | `LnLean.Proofs.Bitcoin.ScriptProps` | `LN-SCRIPT-001`, `LN-SCRIPT-002`, `LN-SCRIPT-003` |
| C04 | `LnLean/Proofs/Channel/HTLCProps.lean` | `LnLean.Proofs.Channel.HTLCProps` | `LN-HTLCRecord-010`, `LN-HTLCRecord-011` |
| C05 | `LnLean/Proofs/Channel/ReserveProps.lean` | `LnLean.Proofs.Channel.ReserveProps` | `LN-CH-101` |
| C06 | `LnLean/Proofs/Channel/StateMachineProps.lean` | `LnLean.Proofs.Channel.StateMachineProps` | `LN-CH-010` |
| C07 | `LnLean/Proofs/Conservation.lean` | `LnLean.Proofs.Conservation` | `LN-CONS-004` |
| C08 | `LnLean/Proofs/Crypto/EcdsaProps.lean` | `LnLean.Proofs.Crypto.EcdsaProps` | `LN-ECDSA-001`, `LN-ECDSA-002` |
| C09 | `LnLean/Proofs/Crypto/Sha256Props.lean` | `LnLean.Proofs.Crypto.Sha256Props` | `LN-CR-007` |
| C10 | `LnLean/Proofs/Payment/KeysendProps.lean` | `LnLean.Proofs.Payment.KeysendProps` | `LN-KS-001` |
| C11 | `LnLean/Proofs/Payment/MPPProps.lean` | `LnLean.Proofs.Payment.MPPProps` | `LN-PAY-MPP-001` |
| C12 | `LnLean/Proofs/Protocol/ChannelReestablishProps.lean` | `LnLean.Proofs.Protocol.ChannelReestablishProps` | `LN-REEST-001`, `LN-REEST-002` |
| C13 | `LnLean/Proofs/Protocol/FeaturesProps.lean` | `LnLean.Proofs.Protocol.FeaturesProps` | `LN-FEAT-012` |
| C14 | `LnLean/Proofs/Routing/GossipProps.lean` | `LnLean.Proofs.Routing.GossipProps` | `LN-GOSSIP-001`, `LN-GOSSIP-002`, `LN-GOSSIP-003` |
| C15 | `LnLean/Proofs/Routing/GraphProps.lean` | `LnLean.Proofs.Routing.GraphProps` | `LN-GRAPH-001` |
| C16 | `LnLean/Proofs/Wire/TLVProps.lean` | `LnLean.Proofs.Wire.TLVProps` | `LN-WIRE-001` |

## Success criterion

A unit is **closed** when its owned file builds and contains zero `sorry`.

Rules:

* Do not change theorem statements to make them easier.  If a statement is
  false for the current model, keep the original `sorry` + marker, document
  the counterexample or missing model field, and report it.
* You may add helper definitions/lemmas in the same file.  They must be
  used, or clearly documented.
* No new `sorry`, `axiom`, `admit`, `native_decide`, `unsafe`,
  `@[implemented_by]`, or Mathlib.
* Do not import another proof module; keep the existing import set.
* A partial unit must still leave its file compiling.  Report the exact
  remaining goal instead of leaving a broken file.

## Integration

The integrator builds each exact module, then regenerates `LnLean.lean` and
runs the full `lake build`.  Only green units are retained in the final
branch commit.  The final gate is:

```sh
./scripts/verify-vendor.sh
python3 scripts/verify-anchors.py
./scripts/check.sh
python3 scripts/check-wave-a.py --build
python3 scripts/check-wave-b.py --build
./scripts/finalize.sh
```

## Other-box coordination

* Other box: `/home/ubuntu/ln-lean-phasec`, branch `phase-c`.
* This box: `/home/ubuntu/ln-lean`, branch `wave-c/235`.
* Never force-push `main`; never rewrite another branch's history.
* If `main` advances, rebase `wave-c/235` before requesting a merge and
  re-run the full gate.

### Observed overlap

The other box launched its own 16 `PC` agents at `2026-10-17T23:04:32Z`
on the same 16 files.  Both lanes are therefore independent attempts at the
same obligations.  Integration must compare per file (remaining `sorry`
count, build verdict, statement preservation) and keep **one** version per
file; do not merge two competing bodies into the same theorem.

`scripts/compare-proof-attempts.py` prints the comparison once
`origin/phase-c` is fetched.  A file with a lower `sorry` count is the
candidate; ties require a green exact-module build and a statement check.

