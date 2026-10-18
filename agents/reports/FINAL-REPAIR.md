# FINAL-REPAIR — integration narrative

**Repository:** `/home/ubuntu/ln-lean-repair`
**Branch:** `repair/integrated`
**Gate HEAD:** `2e743673052a41cdf9640a7e19a1207227066a6c`
**Toolchain:** `leanprover/lean4:v4.35.0`
**Author:** D02 (integration documentation lane), finalized by the integration lane
**Status:** repair + proof-wave 1 + proof-wave 2 lanes complete;
**proof-wave 2 gate PASS**
**Commit/push:** integrated commit `2e74367`; pushed non-force to
`origin/repair/integrated`.

## 1. Starting point

The repair starts from the old green `final/integrated` tree (132 Lean files,
140-job build RC 0, **15** open `sorry` sites). That tree also carried two
inconsistent global crypto assumptions:

- `sha256_preimageResistant` together with the 32-byte output-width field,
  making every `M : PrimitiveModel` theorem vacuous; and
- `hmac_prf`, the same pigeonhole obstruction for HMAC.

The repair branch is **not** that tree. It adds the 17 Phase-C2 and 12 Phase-C3
modules, replaces the five refuted Wave-C sites, removes the ten remaining
refuted unconditional sites, repairs the crypto interface, adds the exact
catalog checker, and pins the public L1 reference.

## 2. What changed

### 2.1 Model and proof modules

- **Phase-C2 (17 modules):** `CltvAccumulation`, `CommitmentAlgebra`,
  `CommitmentBridge`, `FeatureClosure`, `FundingBridge`, `GlobalConservation`,
  `HTLCBridge`, `HTLCPartition`, `HTLCUniqueIds`, `InvoiceBinding`,
  `LivenessDelivery`, `MPPPrefix`, `OnionLayers`, `PenaltyBridge`,
  `PenaltyDoubleSpend`, `ReestablishRange`, `RevocationNumber`.
- **Phase-C3 (12 modules):** `AxiomAudit`, `CloseConservation`,
  `ConformanceVectors`, `CrossChannelRouting`, `EndToEndConservation`,
  `FeeWeightDust`, `InvoiceParser`, `OnionError`, `PersistenceRecovery`,
  `SecurityGame`, `WatchtowerBreach`, `WatchtowerLiveness`.
- The five refuted Wave-C sites (`FundingProps`, `ReserveProps`,
  `GossipProps`) were replaced by the C2 repaired files, removing five open
  sites.
- `LnLean.Proofs.Common` was added so C2/C3 modules can share the base without
  a root import cycle.

### 2.2 `R01`–`R10`: refuted sites

Each lane removed one false unconditional declaration and its
`-- OBLIGATION:` marker, retained the mechanized counterexample, and retained
the strongest conditional or admitted-step replacement. No statement was
weakened to `True`, no axiom was added, and no negative result was deleted.

| Lane | File | Removed | Retained strongest form |
|---|---|---|---|
| R01 | `WaveE/E40.lean` | `waveE_e40_accepted_update_signature_length` | `waveE_e40_accepted_update_signature_length_of_length_respecting`, `..._iff_lengthRespecting` |
| R02 | `ModelHardening/F03.lean` | `committedUpdate_preserves_ledger_unconditional` | `committedUpdate_preserves_ledger` (`Affordable` hypothesis) |
| R03 | `ModelHardening/F04.lean` | `waveF_f04_legacy_unconditional_conservation` | `waveF_f04_corrected_conservation` |
| R04 | `ModelHardening/F05.lean` | `waveF_f05_accepted_update_key_announced` | `admitChannelUpdate_change_key_announced_after` |
| R05 | `ModelHardening/F06.lean` | `bindChannel_capacity_positive` | `bindChannelPositive_capacity_pos`, `bindChannel_capacity_pos_of_announced` |
| R06 | `ModelHardening/F07.lean` | `accepted_message_signatures_64` | `accepted_message_signatures_64_of_lengthRespecting` |
| R07 | `ModelHardening/F09.lean` | `dust_trim_preserves_conservation` | `conservation_of_dustFeeAccounted` |
| R08 | `ModelHardening/F13.lean` | `waveF_f13_unconditional_secret_match` | `accepted_secret_eq` |
| R09 | `ModelHardening/F14.lean` | `waveF_f14_running_total_bound` | `runningTotalBound_add` with `PartFits` |
| R10 | `ModelHardening/F15.lean` | `unconditional_settle_reveals_committed` | `bound_settle_reveals_committed` |

The full 170-job build covers all repaired modules; no separate module-level
build is needed to reproduce the result.

### 2.3 `M01`: SHA-256 interface

`PrimitiveModel` no longer contains `sha256_preimageResistant`. It retains:

```lean
sha256_size : ∀ b, (sha256 b).size = 32
sha256_collisionResistant : CollisionResistant sha256
```

where `CollisionResistant` is injectivity on the 32-byte payment-preimage
domain. `LnLean.Proofs.Crypto.Sha256Props.preimageResistant_vacuous` remains as
a **negative theorem**: no 32-byte-output hash is globally injective. It no
longer contradicts the structure. `rejectAllEcdsa` and the C1 text in
`docs/ASSUMPTIONS.md` were updated. No `sorry` or axiom was added.

The structure is no longer forced uninhabited by a contradictory field pair.
D02 did not add a named Lean witness term; the claim here is consistency of the
interface plus the negative theorem, not a formal `Nonempty` instance.

### 2.4 `M02`: HMAC interface and finite C8

`PrimitiveModel` no longer contains `hmac_prf`. It retains only
`hmac_size : ∀ k m, (hmacSha256 k m).size = 32`.

`LnLean.Proofs.WaveD.D07.hmacPrf_vacuous` proves

```lean
hmacPrf_vacuous (M : PrimitiveModel) (k : ByteArray) :
    ¬ HmacPrf M.hmacSha256
```

by applying the fixed-key pigeonhole argument to `m ↦ M.hmacSha256 k m`.

C8 is now finite-execution tag binding:

```lean
HmacBindsOn hmac mu msgs :=
  ∀ m₁ ∈ msgs, ∀ m₂ ∈ msgs, hmac mu m₁ = hmac mu m₂ → m₁ = m₂
```

D07's uniqueness, no-reuse, and `openWithHmac_layer_authentic` theorems take
`HmacBindsOn` plus explicit membership hypotheses for the concatenations
involved. `hmacOnionInterface M mu msgs` stores the finite contract. The
contract is satisfiable (`hmacBindsOn_singleton`,
`hmacBindsOn_of_pairwise_tags`); it does not assert global injectivity.

### 2.5 `K01` / `K02`: catalog mechanics

`scripts/check-catalog.py` (wrapper `scripts/check-catalog.sh`) parses
`LnLean/Proofs/Obligations.lean`, resolves every `leanTarget` against an exact
fully-qualified declaration map, strips comments and strings before looking
for `sorry`, and marks a row `proved` only when every target is a
`sorry`-free theorem/lemma. It reports promotion candidates but never edits
the catalog.

K02 promoted five exact candidates and corrected two stale targets. Its counts
were **18 `proved` / 30 `statementOnly`** out of 48 rows; proof-wave 1
superseded them with **29 / 19**, and proof-wave 2 with **37 / 11**. At the
proof-wave 2 gate the strict audit still exits 1 because the one planned
`statementOnly` target (`LN-CH-003`) does not exist; `--allow-planned` exits 0
and reports it as `PLANNED`, never as proved. The three exact-but-retained
candidates (`LN-HT-004`, `LN-PR-003`, `LN-PR-004`) are intentionally left as
`statementOnly`. The fifth K02 promotion is `LN-CR-004`
(`LnLean.Wire.decode_encode`); its target was first corrected from the stale
`LnLean.Wire.BigSize.decode_encode`.

### 2.6 `L01`: public L1 reference

- Public reference: `Rob1Ham/btc-lean` `main@4f5c4f8`.
- Build dependency remains `vendor/btc-lean-core` `f950806`, a separate
  lineage that is not in public history.
- `refs/btc-lean` is an untracked, git-excluded symlink to the local public
  clone; it must not be committed.
- `scripts/check-public-reference.sh` verifies the clone origin, HEAD, tag,
  `spec/core` count, the absence of a public build dependency, and vendor
  integrity offline (RC 0).
- `docs/BTC-LEAN-PUBLIC.md` records the 87-path diff audit. Only
  `Bitcoin.Data.Basic`, `Data.Script`, `Data.Tx`, and a one-word `RuleAttr`
  docstring differ in the imported closure; the public `spec/core` is not
  imported.

### 2.7 `CCR01`: elaboration blowup

`LnLean.Proofs.PhaseC3.CrossChannelRouting` previously peaked at 12–19 GiB and
was SIGKILLed by a local watchdog. The cause was the induction motive generated
by `lastAmount`'s overlapping-pattern recursion combined with a nested-pattern
theorem.

The repair defines `lastAmount` as `(forwardAmounts path).getLastD 0` and proves
`backwardConserves_sender_eq_last_add_feeSum` by ordinary induction on the
tail, finishing with `ac_rfl`. The statement and downstream results are
unchanged. The module now builds in ~1.3–1.5 s at ~1.7 GiB peak.

### 2.8 Proof-wave lanes

Eight disjoint lanes added exact targets and retained the model gaps where no
faithful exact declaration exists.

| Lane | Result |
|---|---|
| `W01` | `LN-CR-006` `Wire.Message.decode_length`: declared length equals the consumed payload size, with exact tail and frame-size conjuncts |
| `R01` | `LN-RT-002` `Gossip.update_monotone` (clock monotonicity + replacement requires a greater timestamp); `LN-RT-005` `Route.cltv_accumulates` (total and per-hop prefix accumulation) |
| `O01` | `LN-RT-003` `Onion.peel_deterministic`; `LN-RT-004` `Onion.hmac_sound` for the checked `openLayer` path (D25 raw-`peel` counterexample retained) |
| `P01` | `LN-PR-005` `Peer.reestablish_no_rollback`; D17/E19/E20/FeatureClosure retargets documented for the other protocol rows |
| `M01` | `LN-PM-002` `Invoice.signature_valid` (model projection from `Invoice.verify`; C3 remains an assumption); `LN-PM-005` `MPP.running_total_bound` |
| `S01` | `LN-SEC-002` `Conservation.global_conservation` (multi-channel only); `LN-SEC-003` `Security.safety_async` (four explicit assumptions); `LN-SEC-006` `Liveness.watchtower_bridge` (requires a report) |
| `H01` | No exact target: `LN-HT-003/004` need a balance/fee ledger or per-sender id counters. Added the offered/received/trimmed partition and live-id insert/filter/uniqueness invariants; retained the duplicate-id counterexample |
| `C01` | No exact target: `LN-CH-002` needs the conservation premise; `LN-CH-003` is refuted unconditionally by D12. Added nonnegativity, sum, and trimming lemmas; retained D46/D12 counterexamples |

The lane reports are `agents/reports/W01-WIRE.md`, `R01-ROUTING.md`,
`O01-ONION.md`, `P01-PROTOCOL.md`, `M01-PAYMENTS.md`, `S01-SECURITY.md`,
`H01-HTLC.md`, and `C01-COMMITMENT.md`.

### 2.9 Proof-wave 2 lanes

Five more disjoint lanes extended the model and promoted eight exact targets:

| Lane | Result |
|---|---|
| `SEC05-ECON` | `LN-SEC-005` `Liveness.penalty_economical` under `FeeScheduleBounded`; the D34 unconditional spike counterexample remains |
| `CH02-WF` | `LN-CH-002` `Commitment.outputs_nonnegative`: nonnegativity plus the funding bound under `totalOutputValue + feeSat = fundingValueSat`; D46 remains |
| `HT-LEDGER` | `LN-HT-003` `HTLC.amount_conservation` under `ledger + totalHtlcValue (htlcSet hs) = funding`; `LN-HT-004` retained because `id_unique` assumes `liveHtlcIdsNodup` |
| `PR-WRAPPERS` | `LN-PR-001` `Handshake.open_bounds`; `LN-PR-006` `Handshake.feature_intersection` under BOLT 1 survival and support-set intersection. `LN-PR-003/004` retained as conditional characterizations |
| `CR-RETARGET` | Retargeted `LN-CR-001/002/003` from `PrimitiveModel` fields to `CryptoTargets` contracts: C1 preimage uniqueness; C3 message binding plus domain separation; 32-byte HMAC tag plus finite-execution C8 binding |

The new modules are `LnLean/Proofs/ProtocolTargets.lean` and
`LnLean/Proofs/CryptoTargets.lean`; both are root-imported and audited in
`PhaseC3/AxiomAudit.lean`. The lane reports are `SEC05-ECON.md`,
`CH02-WF.md`, `HT03-HT04-LEDGER.md`, `PR-WRAPPERS.md`, and
`CR-RETARGET.md`.

## 3. What is actually checked

At the proof-wave 2 gate:

```text
flock -w 1800 /tmp/opencode/btc-lean/build.lock lake build
  -> Build completed successfully (172 jobs).  RC 0

grep -RInE '^[[:space:]]*sorry[[:space:]]*$' LnLean --include='*.lean'
  -> no output; 0 matches; grep RC 1

./scripts/verify-vendor.sh
  -> verify-vendor: OK (119 files).  RC 0

python3 scripts/verify-anchors.py
  -> anchors=298 bad=0 unanchored_rows=2; verify-anchors: OK.  RC 0

./scripts/check.sh
  -> files=166 obligations=81 sorry_in_proofs=0; check: OK.  RC 0

python3 scripts/check-final.py
  -> selected D=33 E=15 F=15; 166 Lean files; 164 root imports; OK.  RC 0

./scripts/check-public-reference.sh
  -> check-public-reference: OK (offline).  RC 0

python3 scripts/check-catalog.py --allow-planned
  -> rows=48 proved=37 statementOnly=11 planned=1 proved_failures=0
     duplicate_ids=0 candidates=3; RC 0

python3 scripts/check-catalog.py --audit
  -> RC 1: 1 unresolved planned statementOnly target (LN-CH-003);
     0 proved failures; 3 exact-but-retained candidates

lake build LnLean.Proofs.Traceability
  -> Build completed successfully (10 jobs).  RC 0
```

Tree size: 166 Lean files, 164 root imports. `LnLean.Proofs.All` and the
`PhaseC2` aggregator are not root-imported; the full build covers 172 jobs.

Actual `sorry` terms: **zero**. `sorry` appears only in comments/prose.

## 4. What is proved

- Every Lean module in the tree builds under the pinned toolchain (172 jobs,
  RC 0).
- No proof body contains `sorry`, `admit`, `axiom`, `constant`, `opaque`,
  `native_decide`, `unsafe`, or `@[implemented_by]` in executable code.
- The 37 catalog `proved` rows name exact declarations that exist and are
  `sorry`-free in their source bodies.
- The mechanical C1/C8 facts: 32-byte widths, hash-lock equality, verifier
  equality, stored-tag extraction, and the pigeonhole negative results.
- The repaired conditional theorems listed in §2.2, under their explicit
  hypotheses.
- The C2/C3 module theorems (conservation, bridges, onion layers, penalties,
  watchtower composition, conformance vectors, etc.) build as part of the
  full tree.

This is **not** a proof of Lightning security. It is a sorry-free Lean tree of
conditional/algebraic results plus 11 tracked statement-only claims. The newer
promotions keep their scope caveats: `LN-CR-001/002/003` are conditional crypto
contracts; `LN-CH-002` uses the balance equation; `LN-HT-003` uses the ledger
invariant; `LN-PR-006` is support-set intersection under survival;
`LN-SEC-005` is bounded-schedule only; `LN-RT-004` is checked-`openLayer` only;
`LN-PM-002` is a verification projection; `LN-SEC-002` has no L1 spend-set
bridge; `LN-SEC-003` keeps four assumptions; and `LN-SEC-006` requires a
watchtower report.

## 5. What remains conditional or planned

- 1 `statementOnly` row names a planned declaration not present in the tree:
  `LN-CH-003`. D12 refutes unconditional output ordering and the model has no
  script/CLTV ordering key.
- 3 `statementOnly` rows have exact targets but are deliberately retained:
  `LN-HT-004` assumes the live-id uniqueness it claims; `LN-PR-003/004`
  characterize or assume their predicates. The checker reports them as
  promotion candidates, but the integration lane does not flip them.
- 7 `statementOnly` rows resolve exactly but are not theorem/lemma candidates
  (all seven name `def`s or predicate `def`s).
- 11 rows remain `statementOnly` in total.
- C1 is exact algebraic injectivity on 32-byte inputs, stronger than
  computational collision hardness; no reduction is proved.
- C8 is a finite-execution admission supplied by the caller; computational PRF
  security, tag-collision probability, and forgery resistance are outside the
  model.
- L1 spendability is conditional on `FundingSpendBridge`, `HTLCSpendBridge`,
  and `PenaltyL1Bridge`, and on script-checker / sighash / C1 hypotheses.
  `toLocalScript` is a flat seam fragment, not the full BOLT 3 witness script.
- Network liveness is conditional on partial synchrony/fairness. The watchtower
  bridge requires a report (which implies liveness), not `live` alone. Penalty
  economics remains unproved; the unbounded fee model has a D34 counterexample.
- Deep-reorg behaviour (`LN-CHAIN-REORG`) is a separate obligation.
- No differential conformance against `rust-lightning` or BOLT vectors is
  claimed.
- The public `btc-lean` tree is not imported; no theorem is checked against it.

## 6. Residual risks / final-gate findings

1. **Proof-wave 2 gate PASS at the commit recorded above.** The earlier
   `check.sh` doc-comment false positive and the stale 132-file
   `check-final.py` assumption are fixed. Both checkers are RC 0 at the
   proof-wave 2 HEAD.
2. **Catalog strict mode remains RC 1 by design.** One unresolved planned
   `statementOnly` target (`LN-CH-003`) remains. `--allow-planned` is RC 0 and
   never promotes it; it is the mode used by the final gate, with the strict
   audit retained as the planning report. The three exact-but-retained
   candidates are a deliberate scope decision, not a checker failure.
3. **Public/vendor lineage mismatch.** A vendor bump is a separate deliberate
   change; the public clone must never become a build dependency. The green
   isolated compatibility branch `repair/pubbump` records the public
   `spec/core` bump but is intentionally not merged here.
4. **`refs/btc-lean` must not be committed.** It is an untracked, git-excluded
   symlink.

## 7. Exact commands

```sh
export PATH=/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
cd /home/ubuntu/ln-lean-repair

flock -w 3600 /tmp/ln-build.lock lake build LnLean
grep -RInE '^[[:space:]]*sorry[[:space:]]*$' LnLean --include='*.lean' || true

./scripts/verify-vendor.sh
python3 scripts/verify-anchors.py
./scripts/check.sh
python3 scripts/check-catalog.py --audit
python3 scripts/check-catalog.py --allow-planned
./scripts/check-public-reference.sh

# Optional, K02-owned generated outputs; rewrites files:
# python3 scripts/collect-obligations.py
```

Module-level reproducers are in the individual lane reports
(`agents/reports/R01.md` … `R10.md`, `M01.md`, `M02.md`,
`K01.md`, `K02.md`, `L01.md`, `CCR01.md`).

## 8. Honest summary

The repair removed the two vacuous global crypto assumptions, removed all ten
remaining refuted unconditional headlines without hiding them behind `True` or
axioms, eliminated every actual `sorry` term, fixed the catalog checker and the
`CrossChannelRouting` blowup, and pinned the public L1 reference. Proof-wave 1
added eleven exact catalog targets; proof-wave 2 added eight more across crypto,
commitment, HTLC, protocol, and penalty economics. The result is a sorry-free
Lean tree with 37 exact catalog rows proved and 11 rows tracked as
statement-only (1 unresolved planned target, 3 exact-but-retained, 7 definition
targets).

It is still a conditional scaffold. Zero `sorry` is not zero assumptions: C1
and C8 are explicit finite/algebraic boundaries, L1 spendability depends on the
Phase-C2 bridges, and computational cryptographic security is not modelled. The
proof-wave 2 gate is recorded above, and the branch is pushed non-force to
`origin/repair/integrated`.
