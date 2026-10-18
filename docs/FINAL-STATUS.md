# Final status — Lightning repair tree

**Repository:** `/home/ubuntu/ln-lean-repair`
**Branch:** `repair/integrated`
**Gate HEAD:** this proof-wave 4 working tree; the following status commit
records the exact hash. Proof-wave 3 code was `0c99c92`; wave 4 launched from
`47189fe`.
**Catalog state:** **48 `proved` / 0 `statementOnly` / 0 unresolved / 61
targets**.
**Remote refs:** push is non-force to `origin/repair/integrated`. `origin/main`
is not touched by this work. `origin/repair/pubbump` remains a separate
compatibility branch.
**Toolchain:** `leanprover/lean4:v4.35.0`
**L1 build dependency:** read-only `vendor/btc-lean-core` snapshot
`f95080638ae571a3664f4f41b9b6f6b4cfa7c5eb`
**L1 public reference:** `https://github.com/Rob1Ham/btc-lean`
`main@4f5c4f858fb9ca0743042644453cfa92d30dd271` (review only; not imported)
**Spec / client references:** `lightning/bolts`
`1aadb719b4007c4cea0ba6e36b08c4fb53788dee`; `rust-lightning`
`fe4900930c6bd5786ec4203274d7cf312776a5a6`

This file describes **this repair repository**, not the older
`ln-lean-final` / `final/integrated` tree. The earlier final tree (132 Lean
files, 15 open `sorry` sites, vacuous global crypto assumptions) is the
starting point of the repair, not its result.

## What this tree is

A Lean 4 formal model and proof scaffold for the Lightning Network on top of a
read-only `btc-lean` Bitcoin L1 model. It is not a completed proof of
Lightning, and it is not a conformance-tested implementation.

Proof-wave 3 integrated eleven disjoint lanes. It retargeted and promoted the
last eleven catalog rows, so every catalog row now names an exact,
sorry-free theorem. Proof-wave 4 added six bridge/vector modules and
strengthened two catalog targets without changing the 48-row count.

* `LnLean/Proofs/Bitcoin/FundingScriptTargets.lean`
* `LnLean/Proofs/Bitcoin/ToLocalScriptTargets.lean`
* `LnLean/Proofs/Bitcoin/WeightTargets.lean`
* `LnLean/Proofs/Channel/CommitmentOrderTargets.lean`
* `LnLean/Proofs/Channel/FeeTargets.lean`
* `LnLean/Proofs/ProtocolCoverageTargets.lean`
* `LnLean/Proofs/ProtocolSigningTargets.lean`
* `LnLean/Proofs/Routing/GossipTargets.lean`
* `LnLean/Proofs/Security/ReorgTargets.lean`
* `LnLean/Proofs/Wire/TLVTargets.lean`
* `LnLean/Proofs/Bitcoin/SpendTargets.lean`
* `LnLean/Proofs/Channel/CommitmentIntegrationTargets.lean`
* `LnLean/Proofs/Channel/HtlcGlobalIdTargets.lean`
* `LnLean/Proofs/ConformanceTargets.lean`
* `LnLean/Proofs/ProtocolWireTargets.lean`
* `LnLean/Proofs/Routing/GossipAttributionTargets.lean`

The model/support additions are `HtlcBook`/reachability/per-sender ids and
alone direction-tagged `HTLCTag` namespace in `LnLean/Channel/HTLC.lean`, the
rich `CommitmentTx` output model in `LnLean/Channel/Commitment.lean`, the full
BOLT 3 `toLocalScriptFull` model plus delay bytes in
`LnLean/Bitcoin/Seam.lean`, `CommitmentSignedFull` in
`LnLean/Protocol/Messages.lean`, and the attributed gossip transition in
`LnLean/Routing/Gossip.lean`. Existing legacy declarations are preserved;
mechanized counterexamples such as D12 and the cross-direction HTLC duplicate
are retained.

## Verified state

| Check | Command | Result |
|---|---|---|
| Full build | `LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock lake build` | **RC 0**, `Build completed successfully (188 jobs).` |
| Actual `sorry` | `grep -RInE '^[[:space:]]*sorry[[:space:]]*$' LnLean --include='*.lean'` | **0 matches** (grep RC 1: no lines) |
| Policy checker | `./scripts/check.sh` | **RC 0**, `files=182 obligations=82 sorry_in_proofs=0`, `check: OK` |
| Selection/root checker | `python3 scripts/check-final.py` | **RC 0**, `selected: D=33 E=15 F=15 total=63`, 182 Lean files, 180 root imports |
| Vendor integrity | `./scripts/verify-vendor.sh` | **RC 0**, `OK (119 files)` |
| Anchors | `python3 scripts/verify-anchors.py` | **RC 0**, `anchors=299 bad=0 unanchored_rows=2` |
| Catalog, strict | `python3 scripts/check-catalog.py --audit` | **RC 0**, 48 proved, 0 statement-only, 61 targets, 0 unresolved, 0 proved failures, 0 candidates |
| Catalog, planned-aware | `python3 scripts/check-catalog.py --allow-planned` | **RC 0**, `rows=48 proved=48 statementOnly=0 planned=0 proved_failures=0` |
| Axiom audit | `lake build LnLean.Proofs.PhaseC3.AxiomAudit` | **RC 0**, 101 audited theorems; only `propext`, `Quot.sound`, `Classical.choice` |
| Generated index | `python3 scripts/collect-obligations.py` | `146` proof files, `81` markers, `48` catalog rows, `4834` declarations, `0` `sorry` sites |
| Conformance | `python3 scripts/check-conformance.py` | **RC 0**, 61 BigSize/TLV vectors, 86 Lean theorem checks, 2 declared model gaps |

Tree size: **182 Lean files** under `LnLean/`, **180** root imports in
`LnLean.lean`; `LnLean.Proofs.All` and the `LnLean.Proofs.PhaseC2` aggregator
are not root-imported. The full build covers 188 Lake jobs.

The `sorry` grep result is exact: **there are no lines consisting only of
`sorry` (modulo whitespace) in any `LnLean/**/*.lean` file.** Prose mentions of
`sorry` in comments are not proof terms.

## Catalog promotions and scope caveats

All 48 rows are `proved`, but a `proved` row means the named declaration exists
and is sorry-free. Several rows keep explicit model, cryptographic, or L1
hypotheses; the scope caveat is part of the row's meaning.

| Row | Exact target(s) | Scope caveat |
|---|---|---|
| `LN-L1-001` | `FundingScriptTargets.fundingScriptPubKey_eq_p2wsh_twoOfTwo` | Witness-script hash link plus finite pair-level C1 admission; no P2WSH interpreter bridge |
| `LN-L1-003` | `ReorgTargets.reorg_preserves_channel_safety`, `deep_reorg_separate_failure_mode` | Common tip, common-prefix arithmetic, bounded-depth invariant; deep reorg is a separate failure mode |
| `LN-L1-004` | `ToLocalScriptTargets.toLocalScriptFull_carries_csv_and_revocationKey`, `..._commits_delay_and_revocationKey`, `commitmentOutputs_toLocal_commits_delay_and_revocationKey` | Full two-branch byte template; no `OP_IF`/`OP_CSV`/`OP_CHECKSIG` execution semantics |
| `LN-L1-006` | `WeightTargets.commitmentBaseWeight_model_target` | BOLT 3 fee-basis constants `724`/`1124` and `172` per untrimmed HTLC; exact 8 WU anchor serialization gap retained |
| `LN-CR-005` | `TLVStream.wellFormed_iff_pairwise`, `wellFormed_record_type_unique` | Exact theorem-level characterization; out-of-domain counterexample retained |
| `LN-CH-003` | `Commitment.output_ordering` | Rich `CommitmentTx` model with script/dust/CLTV; D12 still refutes legacy `commitmentOutputs` |
| `LN-CH-005` | `Fee.commitmentSigningGate_rejected_iff_insufficient`, `..._iff_no_checkedSigning` | Exact fee gate; normal-phase transition form explicit |
| `LN-HT-004` | `HTLC.dir_id_unique`, `id_unique_of_reachable_cross`, `tagged_id_unique_of_reachable`, `tagged_ids_nodup_of_reachable`, `cross_direction_duplicate_tagged` | Per-sender uniqueness; direction-tagged ids are globally unique; the untagged global claim needs `CrossDisjoint` and is otherwise refuted |
| `LN-PR-003` | `Handshake.funding_signed_signing_contract` | Conditional on `FundingSigningLaw` + `KeyBinding`; C3 alone is insufficient |
| `LN-PR-004` | `ProtocolWireTargets.commitment_signed_full_covers_exact`, `protocol_wire_summary` | `CommitmentSignedFull` production relation + BOLT 3 value equations; no sighash serializer/C3 derivation, and wire-only negative results retained |
| `LN-RT-006` | `GossipTargets.gossip_graph_only_valid_announcements` | Reachable signature-gated `admitGossip` states; raw `applyGossip` remains unfiltered; G19 key attribution separate |

The earlier proof-wave promotions remain valid with their existing caveats
(`LN-CR-001/002/003`, `LN-CH-002`, `LN-HT-003`, `LN-PR-001`, `LN-PR-006`,
`LN-SEC-005`, and the wave-1 rows). Full notes are in
`docs/THEOREM-INDEX.md` and the reports under `agents/reports/`.

## Trust boundary

### C1 — SHA-256

`PrimitiveModel` has no global preimage-resistance field. C1 is 32-byte
payment-preimage collision resistance plus a finite, explicitly admitted
pair-level collision-free condition where a construction needs it. It is not a
global injectivity axiom and does not by itself bind arbitrary 71-byte funding
witness scripts.

### C3 — signatures

C3 is an exact algebraic signing/verification contract plus message binding
and domain separation. It does not prove signing completeness, key attribution,
or EUF-CMA. `LN-PR-003` keeps those as explicit hypotheses.

### C7/C8 — onion

C7 is the deterministic onion construction; C8 is finite-message HMAC binding.
Global HMAC PRF security is not claimed, and the D07 counterexample remains.

### L1 scripts

Scripts are byte templates plus an explicit, abstract stack-machine model in
`SpendTargets.lean`. The new model proves conditional 2-of-2 funding and
`to_local` revocation/delayed spend theorems under `InterpreterLaws`, and its
serializer is proved equal to the seam templates. It is not a consensus
interpreter: sighash is a parameter, CHECKMULTISIG is 2-of-2, NULLDUMMY is
ignored, and CSV/CLTV are abstract laws. The vendored tree contains a real
interpreter (`Bitcoin/Interpreter/Defs.lean`) that is not yet imported;
connecting it is `L1-01`/`L1-02` next step. `MODEL-01` remains open.

### Network / liveness

Safety results quantify over the modelled schedules; liveness results keep
fairness, fee-schedule, or watchtower hypotheses explicit. Computational
cryptographic reductions and full network semantics are not modelled.

## What remains open

The catalog is closed, but the repository is not release-ready. The living list
is [`docs/OPEN-ISSUES.md`](OPEN-ISSUES.md). The P0 blockers are:

* `OPS-01` — public CI still cannot build from a clean checkout, but the
  `fetch-vendor.sh` path and publication recipe are now tested (mitigated);
* `OPS-02` — no `LICENSE`; a neutral decision matrix is ready;
* `OPS-03` — no release tag and `main` is behind; a release checklist is ready;
* `L1-01`/`L1-02` — conditional execution model exists, but the vendored
  interpreter/sighash bridge is not connected.

Wave 4 narrowed other gaps: `PR-02` now has a full signed commitment record
with a conditional exact-coverage theorem; `CH-01`/`CH-02` have a second-stage
fee/dust/legacy-view module; `HT-01` has a direction-tagged global id
namespace; `RT-01` has an attributed gossip transition; and `CONF-01` has a
61-vector BigSize/TLV suite. These remain open in part because the wire model
is not extended with every derived field and the conformance suite is not a
differential implementation test.

Also open: C1/C3/C8 computational reductions, the BOLT 3 sighash serializer,
the gross/net second-stage commitment patch (`CH-03`), differential
conformance (`CONF-02`), the missing `Step.update_add_htlc` constructor
(`MODEL-02`), and the vendor interpreter bridge (`L1-07`).

## Reproduce

```sh
export PATH=/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
cd /home/ubuntu/ln-lean-repair

LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock lake build
grep -RInE '^[[:space:]]*sorry[[:space:]]*$' LnLean --include='*.lean' || true

./scripts/check.sh
python3 scripts/check-final.py
python3 scripts/check-catalog.py --audit
python3 scripts/check-catalog.py --allow-planned
python3 scripts/check-conformance.py
python3 scripts/verify-anchors.py
./scripts/verify-vendor.sh
```

Do not run `scripts/collect-obligations.py` merely to inspect status: it
rewrites `docs/OBLIGATIONS-GENERATED.md` and
`agents/status/obligations.json`. Regenerate them deliberately as part of an
integration commit.

## Not claimed

- No theorem here is a proof of Lightning Network security, Bitcoin consensus,
  or computational cryptographic hardness.
- A green build and zero actual `sorry` terms do not imply the catalog rows are
  unconditional statements of the English claims. The scope caveats above are
  part of their meaning.
- The conformance suite is vector conformance for BigSize/TLV, not a full
  implementation or differential `rust-lightning` test.
- The 30 proof-wave promotions (eleven in wave 1, eight in wave 2, eleven in
  wave 3) are exact model-level targets; wave 4 strengthens targets rather
  than adding rows. Describing any of this as full protocol verification would
  be false.
