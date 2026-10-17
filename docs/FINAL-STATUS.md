# Final status — two-wave LN scaffold

**Host:** `sensitive-isolated-box-2` (172.31.96.235, 48 vCPU, 185 GiB)
**Repo:** `/home/ubuntu/ln-lean`
**Toolchain:** `leanprover/lean4:v4.35.0`
**L1 dependency:** read-only snapshot of `btc-lean/spec/core` (`fd58ef10`)
**L2 reference:** `rust-lightning` `fe4900930c6bd5786ec4203274d7cf312776a5a6`
**Spec reference:** `lightning/bolts` `1aadb719b4007c4cea0ba6e36b08c4fb53788dee`

## Waves

| Wave | Agents | Result |
|---|---:|---|
| A — model scaffolding | 8 | 8/8 exited 0; 35/35 modules built |
| B — proof scaffolding | 32 | 32/32 exited (31 RC 0, B02 hit its 1 h cap after writing its file); 32/32 modules present |

## Integration gate

```
vendor integrity: OK (byte-identical to the L1 snapshot)
policy check:     OK (no axiom/admit/native_decide/unsafe; no sorry in model modules)
full build:       Build completed successfully (77 jobs)
Lean files:       69 (36 model + 33 proof)
declarations:     1541 (proof-side scan)
obligations:      48 marked, 48 catalog rows, 0 duplicate ids
sorry sites:      25, all under LnLean/Proofs/ with obligation markers
```

The full-library build is green. This is a **scaffold**: theorem statements,
definitions, obligation ids, and partial proofs. It is not a completed
Lightning safety proof.

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
| Proof scaffolding | `LnLean/Proofs/{Bitcoin,Crypto,Wire,Channel,Protocol,Routing,Payment,Security}` |

## Trust boundary

Cryptographic primitives are a `PrimitiveModel` interface with assumed
properties as `Prop` fields (C1–C8 in `docs/ASSUMPTIONS.md`). Bitcoin L1
semantics are consumed from `vendor/btc-lean-core`, never redefined and never
edited. Network and liveness results are conditional on explicit partial-
synchrony/fairness hypotheses.

## Reproduce

```sh
export PATH=/dev/shm/btc/elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
cd /home/ubuntu/ln-lean
./scripts/verify-vendor.sh
./scripts/check.sh
flock -w 1800 /tmp/ln-build.lock lake build
python3 scripts/collect-obligations.py
python3 scripts/collect-anchors.py
```

## Next phase (C)

1. Close the 25 `sorry` sites in dependency order: conservation → HTLC →
   revocation/penalty → state machine → routing/onion → payments → liveness.
2. Replace crypto `Prop` hypotheses with either a proved instantiation or an
   explicit axiom audit naming C1–C8.
3. Add the L1 script-spendability bridge proofs for funding, commitment,
   HTLC, and penalty outputs.
4. Add differential conformance against `rust-lightning`/BOLT vectors.
5. Run the axiom fingerprint audit and promote catalog rows from
   `statementOnly` to `proved` only when the `sorry` at the named target is
   gone.
