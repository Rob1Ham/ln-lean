# Integrator report

- repository: `/home/ubuntu/ln-lean`
- HEAD: `dfaa998f9c9f170f0807e04458a72d403d9b86fb` ([LN-WAVE-C] integrate 20/25 proof closures, lane comparison, and final report)
- wave A: **8/8** agents exited, gate: `A-GREEN 2026-10-17T22:35:33Z
modules=35
vendor=ok
check=ok`
- wave B: **32/32** agents exited, **31** with RC 0 (B02 exited 130 after writing its module; the module builds)
- wave C: **16/16** agents exited, **16** with RC 0; 20/25 obligations closed, **5** open
- vendor integrity: **OK**
- full build: **0**

## Tree counts

- Lean files: **69** (36 model, 33 proof)
- model declarations: **1075**
- proof declarations: **1563**
- wave-A catalog rows: **48** (13 proved, 35 statement-only)
- wave-B `-- OBLIGATION:` markers: **32**
- `sorry` sites under `Proofs/`: **5**

## Remaining `sorry` sites

| File | Line |
|---|---:|
| `LnLean/Proofs/Bitcoin/FundingProps.lean` | 679 |
| `LnLean/Proofs/Channel/ReserveProps.lean` | 604 |
| `LnLean/Proofs/Routing/GossipProps.lean` | 958 |
| `LnLean/Proofs/Routing/GossipProps.lean` | 1016 |
| `LnLean/Proofs/Routing/GossipProps.lean` | 1050 |

## Wave-B files

| File | Declarations | Obligation markers |
|---|---:|---:|
| `LnLean/Proofs/Bitcoin/AnchorProps.lean` | 48 | 0 |
| `LnLean/Proofs/Bitcoin/FundingProps.lean` | 40 | 1 |
| `LnLean/Proofs/Bitcoin/ScriptProps.lean` | 63 | 3 |
| `LnLean/Proofs/Bitcoin/WeightProps.lean` | 47 | 0 |
| `LnLean/Proofs/Channel/BreachProps.lean` | 28 | 19 |
| `LnLean/Proofs/Channel/CommitmentTxProps.lean` | 50 | 4 |
| `LnLean/Proofs/Channel/FeeProps.lean` | 32 | 0 |
| `LnLean/Proofs/Channel/HTLCProps.lean` | 44 | 0 |
| `LnLean/Proofs/Channel/PenaltyProps.lean` | 28 | 0 |
| `LnLean/Proofs/Channel/ReserveProps.lean` | 58 | 1 |
| `LnLean/Proofs/Channel/RevocationProps.lean` | 27 | 0 |
| `LnLean/Proofs/Channel/StateMachineProps.lean` | 28 | 0 |
| `LnLean/Proofs/Conservation.lean` | 53 | 0 |
| `LnLean/Proofs/Crypto/EcdsaProps.lean` | 53 | 0 |
| `LnLean/Proofs/Crypto/SchnorrProps.lean` | 50 | 0 |
| `LnLean/Proofs/Crypto/Sha256Props.lean` | 26 | 0 |
| `LnLean/Proofs/Liveness.lean` | 47 | 0 |
| `LnLean/Proofs/Payment/InvoiceProps.lean` | 42 | 0 |
| `LnLean/Proofs/Payment/KeysendProps.lean` | 65 | 0 |
| `LnLean/Proofs/Payment/LiquidityProps.lean` | 64 | 0 |
| `LnLean/Proofs/Payment/MPPProps.lean` | 64 | 0 |
| `LnLean/Proofs/Protocol/ChannelReestablishProps.lean` | 54 | 0 |
| `LnLean/Proofs/Protocol/ErrorProps.lean` | 39 | 0 |
| `LnLean/Proofs/Protocol/FeaturesProps.lean` | 75 | 0 |
| `LnLean/Proofs/Protocol/HandshakeProps.lean` | 40 | 0 |
| `LnLean/Proofs/Routing/GossipProps.lean` | 83 | 3 |
| `LnLean/Proofs/Routing/GraphProps.lean` | 37 | 1 |
| `LnLean/Proofs/Routing/OnionProps.lean` | 40 | 0 |
| `LnLean/Proofs/Routing/RouteBlindingProps.lean` | 66 | 0 |
| `LnLean/Proofs/Security/ThreatModelProps.lean` | 85 | 0 |
| `LnLean/Proofs/Traceability.lean` | 54 | 0 |
| `LnLean/Proofs/Wire/TLVProps.lean` | 26 | 0 |

## Status records

```
START wave=A agents=8 2026-10-17T22:17:11Z
A1 exit=0 2026-10-17T22:26:43Z
A3 exit=0 2026-10-17T22:27:06Z
A7 exit=0 2026-10-17T22:27:19Z
A4 exit=0 2026-10-17T22:27:28Z
A8 exit=0 2026-10-17T22:28:35Z
A5 exit=0 2026-10-17T22:28:59Z
A6 exit=0 2026-10-17T22:30:46Z
A2 exit=0 2026-10-17T22:34:00Z
DONE wave=A 2026-10-17T22:34:00Z
START wave=B agents=32 2026-10-17T22:27:54Z
B14 exit=0 2026-10-17T22:36:47Z
B15 exit=0 2026-10-17T22:37:13Z
B11 exit=0 2026-10-17T22:37:26Z
B08 exit=0 2026-10-17T22:37:46Z
B13 exit=0 2026-10-17T22:38:29Z
B04 exit=0 2026-10-17T22:38:44Z
B10 exit=0 2026-10-17T22:38:51Z
B27 exit=0 2026-10-17T22:39:26Z
B16 exit=0 2026-10-17T22:40:07Z
B20 exit=0 2026-10-17T22:40:13Z
B07 exit=0 2026-10-17T22:40:14Z
B17 exit=0 2026-10-17T22:40:16Z
B03 exit=0 2026-10-17T22:40:34Z
B12 exit=0 2026-10-17T22:40:38Z
B23 exit=0 2026-10-17T22:40:41Z
B32 exit=0 2026-10-17T22:40:41Z
B01 exit=0 2026-10-17T22:40:41Z
B26 exit=0 2026-10-17T22:40:49Z
B25 exit=0 2026-10-17T22:41:01Z
B05 exit=0 2026-10-17T22:41:13Z
B19 exit=0 2026-10-17T22:41:15Z
B09 exit=0 2026-10-17T22:41:21Z
B21 exit=0 2026-10-17T22:41:27Z
B28 exit=0 2026-10-17T22:41:28Z
B06 exit=0 2026-10-17T22:41:41Z
B18 exit=0 2026-10-17T22:41:45Z
B30 exit=0 2026-10-17T22:42:10Z
B31 exit=0 2026-10-17T22:42:20Z
B22 exit=0 2026-10-17T22:42:27Z
B24 exit=0 2026-10-17T22:42:43Z
B29 exit=0 2026-10-17T22:43:03Z
B02 exit=130 2026-10-17T22:44:07Z
C13 exit=0 2026-10-17T23:05:17Z
C10 exit=0 2026-10-17T23:05:19Z
C15 exit=0 2026-10-17T23:05:35Z
C04 exit=0 2026-10-17T23:05:47Z
C01 exit=0 2026-10-17T23:05:54Z
C08 exit=0 2026-10-17T23:06:37Z
C06 exit=0 2026-10-17T23:06:42Z
C11 exit=0 2026-10-17T23:07:00Z
C03 exit=0 2026-10-17T23:07:02Z
C05 exit=0 2026-10-17T23:07:03Z
C14 exit=0 2026-10-17T23:07:59Z
C12 exit=0 2026-10-17T23:08:00Z
C07 exit=0 2026-10-17T23:08:10Z
C16 exit=0 2026-10-17T23:08:30Z
C09 exit=0 2026-10-17T23:08:51Z
C02 exit=0 2026-10-17T23:10:05Z
```

## Honest limits

This is a scaffold.  Wave C closed 20 of the 25 wave-B `sorry` sites;
the remaining sites are either false as stated for the current model or
need a missing model field (see the individual `C` reports).  The wave-A
catalog is metadata; most rows are
`statementOnly`.  Wave-B files add theorem statements and obligation
markers, and many contain `sorry`.  Cryptographic facts are `Prop`
hypotheses, not axioms.  The report does not upgrade an obligation to a
proof: only a build with no `sorry` at that site would.

## Reproduce

```sh
export PATH=/dev/shm/btc/elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
cd /home/ubuntu/ln-lean
./scripts/verify-vendor.sh
./scripts/check.sh
python3 scripts/collect-obligations.py
python3 scripts/collect-anchors.py
flock -w 1800 /tmp/ln-build.lock lake build
```
