# Final status — integrated D/E/F scaffold

**Repo:** `/home/ubuntu/ln-lean-final`
**Branch:** `final/integrated` (base `a9f8d87`)
**Toolchain:** `leanprover/lean4:v4.35.0`
**L1 dependency:** read-only snapshot of `btc-lean/spec/core`
**L2 reference:** `rust-lightning` `fe4900930c6bd5786ec4203274d7cf312776a5a6`
**Spec reference:** `lightning/bolts` `1aadb719b4007c4cea0ba6e36b08c4fb53788dee`

## Waves

| Wave | Agents | Result |
|---|---:|---|
| A — model scaffolding | 8 | 8/8 exited 0; 35/35 modules built |
| B — proof scaffolding | 32 | 32/32 modules present |
| C — proof closure | 16 | 20/25 obligations closed; 5 documented open |
| D — independent attempts | 48 | 48/48 modules and reports; 2 open sites |
| E — independent attempts | 48 | 48/48 modules and reports; 2 open sites |
| F — model hardening | 16 | 16/16 modules and reports; 10 open sites |
| G — read-only audit | 32 | 32/32 reports; selection manifest |

## Final gate

```text
selection:        63 whole files (33 D + 15 E + 15 F)
Lean files:       132 (69 base + 63 selected)
root imports:     132
full build:       Build completed successfully (140 jobs), RC 0
vendor integrity: OK (119 files)
anchors:          288 checked, 0 bad
policy check:     OK
markers:          95, 0 duplicate ids
catalog:          48 rows (13 proved, 35 statementOnly)
sorry sites:      15, all under LnLean/Proofs/ with adjacent markers
```

The final tree keeps one whole-file D/E version per catalog slot.  D14 is
kept and E14 excluded (duplicate `LnLean.Channel.Reserve.bounds`).  F10 is
excluded from the final tree; it remains on `wave-f/16`.

## Remaining open sites

- 5 base Wave-C sites: `FundingProps` (`LN-FUND-001`), `ReserveProps`
  (`LN-CH-101`), and `GossipProps` (`LN-GOSSIP-001/002/003`).
- `WaveE/E40` (`LN-WE-E40`): false unconditional signature-length admission.
- 9 F sites: `F03`, `F04`, `F05`, `F06`, `F07`, `F09`, `F13`, `F14`, `F15`.

Each is a false or underspecified unconditional statement adjacent to its
marker, with a proved conditional/counterexample companion.  See
`docs/WAVE-STATUS.md` and `agents/reports/FINAL-INTEGRATOR.md`.

## What is modelled

| Domain | Modules |
|---|---|
| Shared vocabulary | `LnLean/Basic/Core.lean` |
| Bitcoin L1 seam | `LnLean/Bitcoin/{Seam,Funding,ScriptTemplates,Laws}.lean` |
| Crypto interface | `LnLean/Crypto/{Model,Hash,Sig,Noise}.lean` |
| BOLT 1 wire | `LnLean/Wire/{BigSize,TLV,Message}.lean` |
| Channel | `LnLean/Channel/{Types,State,Commitment,Fee,Laws}.lean` |
| HTLC/revocation | `LnLean/Channel/{HTLC,Revocation,Penalty,HTLCLaws}.lean` |
| Peer protocol | `LnLean/Protocol/{Handshake,Peer,Messages,Laws}.lean` |
| Routing/onion | `LnLean/Routing/{Graph,Gossip,Onion,Route,Laws}.lean` |
| Payments | `LnLean/Payment/{Invoice,HTLC,MPP,Laws}.lean` |
| Security/catalog | `LnLean/Security/{Model,Invariants}.lean`, `LnLean/Proofs/Obligations.lean` |
| D/E proof lanes | `LnLean/Proofs/{WaveD,WaveE}/` |
| Model hardening | `LnLean/Proofs/ModelHardening/` |

## Trust boundary

Cryptographic primitives are a `PrimitiveModel` interface with assumed
properties as `Prop` fields (C1–C8 in `docs/ASSUMPTIONS.md`).  Bitcoin L1
semantics are consumed from `vendor/btc-lean-core`, never redefined and never
edited.  Network and liveness results are conditional on explicit partial-
synchrony/fairness hypotheses.

## Reproduce

```sh
export PATH=/dev/shm/btc/elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
cd /home/ubuntu/ln-lean-final
python3 scripts/check-final.py
./scripts/verify-vendor.sh
python3 scripts/verify-anchors.py
./scripts/check.sh
flock -w 1800 /tmp/ln-build.lock lake build
python3 scripts/collect-obligations.py
python3 scripts/collect-anchors.py
```

## Next phase

1. Close the 15 open sites in dependency order; do not weaken the statements.
2. Add the missing model fields identified by D/E/F (funding hash bridge,
   commitment conservation/anchor debit, script/CLTV output identity, gossip
   admission, `Step.update_add_htlc`, watchtower penalty bridge).
3. Add the L1 script-spendability bridge proofs.
4. Run differential conformance against `rust-lightning`/BOLT vectors.
5. Promote catalog rows from `statementOnly` to `proved` only when the named
   target has no `sorry`.
