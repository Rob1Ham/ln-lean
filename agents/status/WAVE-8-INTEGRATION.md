# Wave 8 / Wave H integration report

**Remote base:** `e3e0aa8` (`[DOCS] record hosted CI verification for OPS-01`)
**Wave H base:** `50d78ed`
**Worktree:** `/home/ubuntu/ln-lean-waveh`
**Branch:** `wave-h/48`
**Merge commit:** the commit containing this report merges `origin/repair/integrated`
into the Wave H branch; status commits may advance the tip.
**Push:** non-force to `origin/repair/integrated`; the remote was not rewritten.

## Gate

Run with `/tmp/opencode/waveh-gate.sh`; log at `/tmp/opencode/waveh-gate.log`.

| Check | Result |
|---|---|
| Full build | **RC 0**, `Build completed successfully (295 jobs)` |
| Policy checker | **RC 0**, `files=256 obligations=82 sorry_in_proofs=0`, `check: OK` |
| Selection/root | **RC 0**, 256 Lean files, 254 root imports |
| Catalog strict | **RC 0**, 48/48 proved, 100 targets, 0 unresolved, 0 proved failures |
| Conformance | **RC 0**, 175 Lean references, 13/13 mutation controls, 6 BOLT 2 vectors, live 26 BigSize + 3 TLV + 4 wire |
| Anchors | **RC 0**, `anchors=309 bad=0 unanchored_rows=2` |
| Vendor | **RC 0**, `OK (149 files)` from public `btc-lean` `4f5c4f8` |
| Axiom audit | **RC 0**, 227 audited theorems; only `propext`, `Quot.sound`, `Classical.choice` |
| Generated index | 218 proof files, 81 markers, 8228 declarations, 0 `sorry` sites |
| Exact `sorry` scan | **0 matches** |

## What was merged

The remote branch already contained the public-core bump and eight wave-8
residual lanes (`TxValidTransferTargets`, `HtlcPreimageTargets`,
`OpenChannelWireTargets`, `AcceptPayloadTargets`,
`CommitmentConsumerSitesTargets`, `EcdsaBridgeTargets`,
`ConformanceDiffTargets`, `GossipStoreEpochTargets`). The Wave H branch adds
**45 independent proof modules** under `LnLean/Proofs/WaveH/`; no remote
changes were reverted.

### Kept Wave H modules (45)

`H01 H02 H03 H04 H05 H06 H07 H08 H09 H10 H11 H12 H13 H14 H15 H16 H17 H18
H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34 H35 H36 H37
H38 H39 H40 H41 H42 H43 H44 H45`

Each module has a report under `agents/reports/wave8/`. H46–H48 are artifact
lanes and have no Lean module.

## Merge resolutions

* `LnLean.lean` — regenerated from the merged 256-file tree; 254 root imports.
* `scripts/check-final.py` — `EXPECTED_LEAN_FILES = 256`.
* `LnLean/Proofs/PhaseC3/AxiomAudit.lean` — union of the remote wave-8 pins
  and the 12 Wave H pins; `auditedTheorems.length = 227`.
* `vendor/btc-lean-core` — provisioned from public `btc-lean` `4f5c4f8` with
  `scripts/fetch-vendor.sh --from-git --force`; 149-file manifest verified.
* `LnLean/Proofs/WaveH/H20.lean` — adapted to the remote `HandshakeState`
  change that removed `DecidableEq`; the concrete witness transitions are now
  proved by definitional equality instead of `decide`.
* `docs/` and `agents/swarm/WAVE-8.md` — remote status preserved, with the
  Wave H 48-lane results appended.

## Wave H results

* **H01/H04/H06/H30/H31/H32** — unconditional per-input
  `txCheckerFor (some amount) = realCheckerOf`, concrete one-input P2WSH
  `scriptLaneTx`/`txVerdictFull` composition, exact `csv < 32768` and
  `MINIMALDATA` boundaries, and funding/revocation checker instances.
* **H07/H08/H09/H11/H12/H37** — HTLC BIP 143 preimage/digest equality, four
  BOLT 3 witness scripts with exact scriptCode synthesis, serialization-domain
  and framing boundaries; independently confirms `PR-05`.
* **H13–H22** — **319-byte** BOLT 2 type-32 `open_channel` mandatory payload
  (correcting the earlier 313-byte sketch), 270-byte `accept_channel`, and the
  additive stored-accept/PoP contract.
* **H23–H28** — commitment consumer/view adapters, downstream accounting, and
  the construction-site coverage-loss counterexample.
* **H33/H34** — closes `L1-04` (witness weight `1116 + 172*k`, fee basis
  `1124 + 172*k`, the 8 WU is `count_tx_out`) and `L1-05` (71-byte script
  injectivity counterexample plus a domain-separated commitment).
* **H39–H45** — epoch-gossip projection/supersession, concrete
  schedule/fairness liveness, lossless reduction arithmetic/separations, and
  conditional reorg preservation.
* **H46–H48** — vendor artifact verifier, clean-checkout dry run, and release
  decision support.

## Scope

This is a model/proof integration, not a full Lightning verification or a
release. The concrete EC positive witness, transport attribution for
`open_channel`, registration/proof-of-possession game, arbitrary-preimage and
wire-only coverage, computational reductions, unconditional network liveness,
and release packaging remain open. See `docs/OPEN-ISSUES.md`.
