# Phase-C lanes

The repository is worked on by more than one box. To avoid clobbering, this
document declares the lane owned by **`sensitive-isolated-box-2`**
(`172.31.96.235`).

## Lane `phase-c` (this box)

* Worktree: `/home/ubuntu/ln-lean-phasec`
* Branch: `phase-c`, based on `origin/main` at `b891a59`
* Scope: replace the 25 `sorry` sites in the files listed below with real
  proofs where the current model permits it; otherwise keep the `sorry`
  with an `-- OBLIGATION:` marker and record the exact missing bridge.
* **Only the 16 files below are owned by this lane.** No new modules, no
  dependency changes, no edits to `LnLean.lean`, `lakefile.lean`, `docs/`,
  `refs/`, or `vendor/`.
* Every agent commits only its target file and `agents/reports/PCxx.md`.
* The branch is pushed as `origin/phase-c`; it is not force-pushed. The
  integrator merges it into `main` only after a green full build.

## File ownership

| Agent | Target file | `sorry` sites |
|---|---|---:|
| PC01 | `LnLean/Proofs/Conservation.lean` | 1 |
| PC02 | `LnLean/Proofs/Bitcoin/FundingProps.lean` | 2 |
| PC03 | `LnLean/Proofs/Bitcoin/AnchorProps.lean` | 2 |
| PC04 | `LnLean/Proofs/Bitcoin/ScriptProps.lean` | 3 |
| PC05 | `LnLean/Proofs/Wire/TLVProps.lean` | 1 |
| PC06 | `LnLean/Proofs/Crypto/Sha256Props.lean` | 1 |
| PC07 | `LnLean/Proofs/Crypto/EcdsaProps.lean` | 2 |
| PC08 | `LnLean/Proofs/Channel/HTLCProps.lean` | 2 |
| PC09 | `LnLean/Proofs/Channel/ReserveProps.lean` | 1 |
| PC10 | `LnLean/Proofs/Channel/StateMachineProps.lean` | 1 |
| PC11 | `LnLean/Proofs/Protocol/ChannelReestablishProps.lean` | 2 |
| PC12 | `LnLean/Proofs/Protocol/FeaturesProps.lean` | 1 |
| PC13 | `LnLean/Proofs/Routing/GraphProps.lean` | 1 |
| PC14 | `LnLean/Proofs/Routing/GossipProps.lean` | 3 |
| PC15 | `LnLean/Proofs/Payment/MPPProps.lean` | 1 |
| PC16 | `LnLean/Proofs/Payment/KeysendProps.lean` | 1 |

## Rules for merging with the other box

1. Do not force-push `main` or `phase-c`.
2. Before merging, fetch `origin/main` and rebase `phase-c` on it. A conflict
   in a file this lane owns is resolved in favour of the lane's *proved*
   version only if the full build is green; otherwise keep the other side
   and re-open the obligation.
3. A `sorry` may be removed only when the replacement is a complete proof of
   the same statement (or a documented, strictly stronger conditional
   statement). Removing a marker without a proof is forbidden.
4. Report counts must match `grep -c '\bsorry\b'` on the owned file.
