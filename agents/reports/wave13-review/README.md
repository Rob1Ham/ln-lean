# Wave 13 review — LDK-backed remaining-work scope

**Base:** `f7f062817c185cd70004bb26c652deb99c6fd4bd`
(`repair/integrated`)
**Mode:** read-only review; no Lean or catalog edits by the 32 lanes.
**Pins:** `lightningdevkit/ldk-node@fa123fed131e27ecc420b77fa7086fcf1ddaebb8`,
`lightningdevkit/ldk-server@c17dc11dde38f88c53457039ddf30c6b90a63ba2`.
**Synthesis:** `R32-synthesis.md` is the authoritative ranked result. This file
is a short index and should not be read as a replacement for R32 or the lane
reports.

## What changed in the review

The wave did not find a new way through the known L1/Noise/EUF-CMA/source
barriers. It did find a different class of tractable work: **live consumers and
assurance metadata that overstate or misapply already-proved model results.**
These are model-level repair targets; they do not require a concrete secp256k1
verifier, a real Noise implementation, or a production coverage source.

## Top P0 findings

| Id | Finding | Primary evidence |
|---|---|---|
| `REV-01` | `LiquidityProps.reserveMsat` uses the local endpoint rather than the peer-advertised reserve; `reserveOf .local` and `addHtlc?` inherit the wrong direction. `pendingHtlcValueOf` pools both directions, so `AffordableAdd.withinInFlight` is not the BOLT 2 directional cap. `addHtlc?` also admits zero/minimum/CLTV-invalid HTLCs and sums terminal HTLCs. | `LiquidityProps.lean:110-111,133-135,295-298,376-384`; `State.lean:266-269,315-316`; BOLT 2 `02-peer-protocol.md:730-742`; R19, R32 §3 G01–G04 |
| `REV-02` | The legacy `commitmentPairOfBalances` subtracts only the fee; an anchored pair overfunds by the two 330-sat anchors. The corrected constructor exists but has no production consumer. `commitmentOutputs` always emits both anchors, and the consumed gross-dust path differs from the exact net path. | `Commitment.lean:113-114,380-410,914-922,951-970`; `ModelHardening/F04.lean:222-226`; BOLT 3 `03-transactions.md:321-326`; R06, R32 §3 G05–G07 |
| `REV-03` | `receive` replays the unnumbered `advanceReceived`; the numbered idempotent refinement is not wired. `Keysend.retry` resets `succeeded` to `pending`, and there is no payment-store duplicate admission predicate, so a duplicate keysend can settle twice. | `Protocol/Peer.lean:213`; `ChannelReestablishProps.lean:282-295,386-405`; `KeysendProps.lean:252-255,300-301`; `ldk-node/src/payment/spontaneous.rs:67-73`; R12, R31, R32 §3 G09–G11 |
| `REV-04` | `routeValid` checks every hop independently against some enabled edge; there is no adjacency/edge-chain condition. Two disjoint edges can satisfy it, despite the docstring claiming graph-level end-to-end validity. | `Routing/Route.lean:325-327`; R16, R32 §3 G12 |
| `REV-05` | The assurance counts are occurrence/registry counts, not coverage: 294 target occurrences vs 282 unique declarations; 393 `#print axioms` commands vs a 435-name registry; 72 unique catalog targets are unprinted and 35 are absent from the registry. `Traceability` checks declaration IDs, not declaration text/module equality. | `Obligations.lean:458-459`; `AxiomAudit.lean:117-570,579-1018`; `Traceability.lean:830-900`; R31, R32 §1, §3 G20–G22 |

## Recommended wave 13 (repair + assurance)

R32 §6.2 gives exclusive new files and acceptance tests. The bounded lanes are:

| Lane | Scope |
|---|---|
| `W13-LIQ` | Additive corrected reserve/directional in-flight/full HTLC admission; retain the old carriers and counterexamples. |
| `W13-ANCHOR` | Additive anchored conservation with the 660-sat funder debit; retain the legacy pair and refutation witnesses. |
| `W13-PAY` | Payment-store duplicate admission and a guarded keysend retry; retain `retry_pending`. |
| `W13-STATE` | Wire the numbered `commitment_signed` receipt and correct the stale-snapshot consumer. |
| `W13-ROUTE` | Add a chain-backed route predicate, its witness, and refinement to `routeValid` without changing `routeValid`. |
| `W13-ASSURANCE` | Reconcile the axiom print set and registry; enforce target text/module equality; correct the definitional/hypothesis-restatement wording. |

Wave 14 conditional work: route capacity/scoring, single-anchor/net-dust,
zero-fee/shared-anchor, MPP `≥ total_msat`, LDK Server status projection,
splicing/dual funding, and BOLT 12/async/trampoline. Those are not wave-13
repair patches; see R32 §6.3 for entry conditions.

## What not to claim

- Do not call the 294 target occurrences 294 unique theorems.
- Do not call the 435-name registry 435 audited theorems.
- Do not call `addHtlc?`, `commitmentPairOfBalances`, `Keysend.retry`, or
  `routeValid` production-faithful without the repair lanes.
- Do not use LDK Server API behavior as Lean evidence until its `ldk-node` pin
  is aligned (`ldk-server/Cargo.toml:16` currently names `179b4b2…`).

## Lane reports

`R01`–`R31` are evidence/gap reports; `R32-synthesis.md` is the deduplicated
roadmap. `LDK-REFS.md` records the pinned read-only clones. The launch tooling
is `scripts/gen-review-wave-13.py` and `scripts/launch-review-wave-13.sh`.
