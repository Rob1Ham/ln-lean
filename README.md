# ln-lean

A Lean 4 formal model and proof scaffold for the Lightning Network, layered
on the existing `btc-lean` Bitcoin L1 formalization.

**This is a model-level proof tree, not a completed verification of Lightning.**
The tree compiles, every catalog row names a sorry-free theorem, and the
definitions are anchored to BOLTs and `rust-lightning`. The remaining
full-verification gaps — L1 script execution, computational cryptography,
wire completeness, conformance, and public release packaging — are tracked in
[`docs/OPEN-ISSUES.md`](docs/OPEN-ISSUES.md).

At the proof-wave 9 gate, the integrated `repair/integrated` tree has:

* **261 Lean files** under `LnLean/` — 38 executable model modules and 223
  proof modules;
* **259 root imports** in `LnLean.lean` (the `Proofs.All` and `Proofs.PhaseC2`
  aggregators are intentionally not root-imported);
* **48 catalog obligations: 48 `proved`, 0 `statement-only`**;
* **0 actual `sorry` sites** in the proof tree;
* a full build of **300 jobs, RC 0**;

A `proved` row means the named declaration exists and is sorry-free. It does
not mean the English sentence is unconditionally true: several rows keep
explicit model, cryptographic, or L1 hypotheses, and the row's scope note is
part of its meaning. See `docs/THEOREM-INDEX.md`, `docs/TRACEABILITY.md`, and
the lane reports under `agents/reports/`.

## Status

| Metric | Value |
|---|---:|
| Catalog rows | 48 |
| `proved` | 48 |
| Catalog targets | 142 |
| `statement-only` | 0 |
| Unresolved/planned targets | 0 |
| Actual `sorry` terms | 0 |
| Lean files | 261 |
| Root imports | 259 |
| Full build | 300 jobs, RC 0 |
| Audited headline theorems | 269 |
| Conformance vectors | 61 base + 16 framing + 9 boundaries; 33 differential fixtures; live 26 BigSize + 3 TLV + 4 wire + 1 BOLT 2 `channel_ready` payload; 180 Lean refs; 14/14 mutation controls |

The strict catalog audit is now green:

```text
rows=48 proved=48 statementOnly=0 targets=142 unresolved=0
proved_failures=0 duplicate_ids=0 candidates=0 declarations=10742
```

The remaining work is no longer catalog promotion. It is the harder bridge from
the model to spendable Bitcoin scripts, real cryptographic reductions, wire
completeness, conformance vectors, and a reproducible public release. The
living priority list and wave assignments are in `docs/OPEN-ISSUES.md`; the
swarm protocol is in `docs/SWARM-LOOP.md`.

## Layout

```text
LnLean/Basic/Core.lean      shared vocabulary (msat, ids, direction, errors)
LnLean/Bitcoin/Seam.lean    L1 aliases + funding/commitment scripts
LnLean/Crypto/              primitive model, hash/signature specifications
LnLean/Wire/                BigSize, TLV, message framing
LnLean/Channel/             state machine, commitments, HTLC, revocation
LnLean/Protocol/            handshake, peer, features, errors
LnLean/Routing/             graph, gossip, onion, route construction
LnLean/Payment/             invoices, MPP, keysend, liquidity
LnLean/Security/            threat model and invariant catalog
LnLean/Proofs/              223 proof modules: obligation modules, theorem
                            statements, WaveD (33), WaveE (15),
                            ModelHardening (15), PhaseC2 (17), PhaseC3 (12),
                            and the proof-wave 3/4/5/6/7/8/9 target modules
```

`LnLean/Proofs/All.lean` and `LnLean/Proofs/PhaseC2.lean` are convenience
aggregators and are excluded from the root import set to avoid duplicating the
import graph.

## Build

The repository pins `leanprover/lean4:v4.35.0` in `lean-toolchain`; elan
installs the matching toolchain automatically.

```sh
cd /home/ubuntu/ln-lean-repair
lake build
```

If `lake` is not on `PATH`, add elan's bin directory first:

```sh
export PATH="$HOME/.elan/bin:$PATH"
```

When several agents share one checkout, serialize builds with the shared lock:

```sh
flock -w 1800 /tmp/opencode/btc-lean/build.lock lake build
```

Per-module (the normal agent path):

```sh
flock -w 1800 /tmp/opencode/btc-lean/build.lock lake build LnLean.Channel.Commitment
```

## Checks

```sh
./scripts/check.sh                    # files=261 obligations=82 sorry_in_proofs=0
python3 scripts/check-final.py        # 261 files, 259 root imports, D=33 E=15 F=15
python3 scripts/check-catalog.py --audit
                                      # rows=48 proved=48 statementOnly=0 targets=142
python3 scripts/check-conformance.py  # 61 base + 16 framing + 9 boundaries, 33 differential fixtures, live evidence
python3 scripts/verify-anchors.py     # anchors=306 bad=0 unanchored_rows=2
./scripts/verify-vendor.sh            # 149-file L1 snapshot checksums
./scripts/regen-root.sh               # regenerate LnLean.lean from the module tree
```

`verify-anchors.py` requires the pinned `refs/rust-lightning` checkout, and
`verify-vendor.sh` requires the read-only `vendor/btc-lean-core` snapshot.
`check.sh`, `check-final.py`, and `check-catalog.py` are source-level checks and
need neither.

## References

* `refs/rust-lightning` — pinned rust-lightning implementation
  (`fe4900930c6bd5786ec4203274d7cf312776a5a6`).
* `refs/bolts` — BOLT specifications
  (`1aadb719b4007c4cea0ba6e36b08c4fb53788dee`).
* `vendor/btc-lean-core` — read-only Bitcoin L1 Lean model snapshot from the
  public `btc-lean` `spec/core` at
  `4f5c4f858fb9ca0743042644453cfa92d30dd271` (149 files).
* `refs/PINNED.md` — full pin and provenance record.

## Release status

There is no `LICENSE` file yet. Choosing a license is a maintainer decision,
not an automation decision. No release tag has been cut, and `main` has not
been merged into `repair/integrated`.

The public CI workflow `.github/workflows/ci.yml` runs the source-level gates,
the BigSize/TLV conformance checker, and the anchor check. Its full-build job
now fetches the exact public `btc-lean` commit `4f5c4f8`, copies `spec/core`
into the gitignored vendor path, and verifies every file against
`vendor/VENDOR-SHA256` before building. An explicitly configured checksummed
archive can still override the public fetch for offline or self-hosted runs.
`docs/RELEASE-CHECKLIST.md` and `docs/LICENSE-DECISION.md` record the remaining
release decisions (`OPS-02`, `OPS-03`).

## Documentation

* `docs/OPEN-ISSUES.md` — living roadmap of every known open issue and wave lane.
* `docs/SWARM-LOOP.md` — how the 8-agent waves are selected, integrated, gated,
  committed, and repeated.
* `docs/CHARTER.md` — goals, non-goals, phases.
* `docs/ARCHITECTURE.md` — module graph and modelling decisions.
* `docs/ASSUMPTIONS.md` — cryptographic/L1/network TCB.
* `docs/SCOPE.md` — in/out of scope.
* `docs/THEOREM-INDEX.md` — every obligation, target, status, and scope caveat.
* `docs/TRACEABILITY.md` — obligation -> BOLT -> rust-lightning anchors.
* `docs/ROADMAP.md` — historical Phase-C plan and remaining bridge work.
* `docs/WAVE-STATUS.md` — agent waves, gate, and reproduce commands.
* `docs/FINAL-STATUS.md` — proof-wave gate record and release caveats.
* `docs/RELEASE-CHECKLIST.md` — pre-tag gates and human decisions.
* `docs/LICENSE-DECISION.md` — neutral license decision matrix.
* `docs/CRYPTO-LIMITS.md` — computational-security limits and reduction gaps.
* `tests/conformance/README.md` — BigSize/TLV vector format and scope.
* `agents/status/FINAL-SELECTION.md` — one-file-per-slot selection manifest.
* `docs/OBLIGATIONS-GENERATED.md` — generated obligation/marker index.
* `docs/ANCHORS-GENERATED.md` — generated BOLT/LDK anchor index.
