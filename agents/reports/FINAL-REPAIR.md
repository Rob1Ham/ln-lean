# FINAL-REPAIR — integration narrative

**Repository:** `/home/ubuntu/ln-lean-repair`
**Branch:** `repair/integrated`
**HEAD:** `68c236da89b6063dd884799453f076bdc006de2f`
**Toolchain:** `leanprover/lean4:v4.35.0`
**Author:** D02 (integration documentation lane), finalized by the integration lane
**Status:** repair lanes complete; **final gate PASS at this HEAD**
**Commit/push:** integrated commit `68c236d`; push is the remaining action.

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

K02 promoted five exact candidates and corrected two stale targets. Final
counts are **18 `proved` / 30 `statementOnly`** out of 48 rows. The strict
audit still exits 1 because 23 planned `statementOnly` targets do not exist;
`--allow-planned` exits 0 and reports them as `PLANNED`, never as proved. The
fifth promotion is `LN-CR-004` (`LnLean.Wire.decode_encode`); its target was
first corrected from the stale `LnLean.Wire.BigSize.decode_encode`.

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

## 3. What is actually checked

At the committed final HEAD `68c236d` (G01 gate):

```text
flock -w 3600 /tmp/ln-build.lock lake build LnLean
  -> Build completed successfully (170 jobs).  RC 0

grep -RInE '^[[:space:]]*sorry[[:space:]]*$' LnLean --include='*.lean'
  -> no output; 0 matches; grep RC 1

./scripts/verify-vendor.sh
  -> verify-vendor: OK (119 files).  RC 0

python3 scripts/verify-anchors.py
  -> anchors=298 bad=0 unanchored_rows=2; verify-anchors: OK.  RC 0

./scripts/check.sh
  -> files=164 obligations=81 sorry_in_proofs=0; check: OK.  RC 0

python3 scripts/check-final.py
  -> selected D=33 E=15 F=15; 164 Lean files; 162 root imports; OK.  RC 0

./scripts/check-public-reference.sh
  -> check-public-reference: OK (offline).  RC 0

python3 scripts/check-catalog.py --allow-planned
  -> rows=48 proved=18 statementOnly=30 planned=23 proved_failures=0
     duplicate_ids=0 candidates=0; RC 0

python3 scripts/check-catalog.py --audit
  -> RC 1: 23 unresolved planned statementOnly targets; 0 proved failures
```

Tree size: 164 Lean files, 162 root imports. `LnLean.Proofs.All` and the
`PhaseC2` aggregator are not root-imported; the full build still covers 170
jobs.

Actual `sorry` terms: **zero**. Fifteen files contain the word `sorry` only in
comments/prose.

## 4. What is proved

- Every Lean module in the tree builds under the pinned toolchain (170 jobs,
  RC 0).
- No proof body contains `sorry`, `admit`, `axiom`, `constant`, `opaque`,
  `native_decide`, `unsafe`, or `@[implemented_by]` in executable code.
- The 18 catalog `proved` rows name exact declarations that exist and are
  `sorry`-free in their source bodies.
- The mechanical C1/C8 facts: 32-byte widths, hash-lock equality, verifier
  equality, stored-tag extraction, and the pigeonhole negative results.
- The repaired conditional theorems listed in §2.2, under their explicit
  hypotheses.
- The C2/C3 module theorems (conservation, bridges, onion layers, penalties,
  watchtower composition, conformance vectors, etc.) build as part of the
  full tree.

This is **not** a proof of Lightning security. It is a sorry-free Lean tree of
conditional/algebraic results plus 30 tracked statement-only claims.

## 5. What remains conditional or planned

- 23 `statementOnly` rows name planned declarations not present in the tree.
- 7 `statementOnly` rows resolve exactly but are not theorem/lemma candidates
  (six `def`s; `LN-CR-005` is a predicate `def`). No promotion candidate
  remains.
- C1 is exact algebraic injectivity on 32-byte inputs, stronger than
  computational collision hardness; no reduction is proved.
- C8 is a finite-execution admission supplied by the caller; computational PRF
  security, tag-collision probability, and forgery resistance are outside the
  model.
- L1 spendability is conditional on `FundingSpendBridge`, `HTLCSpendBridge`,
  and `PenaltyL1Bridge`, and on script-checker / sighash / C1 hypotheses.
  `toLocalScript` is a flat seam fragment, not the full BOLT 3 witness script.
- Network liveness is conditional on partial synchrony/fairness; watchtower
  liveness and penalty economics are assumptions.
- Deep-reorg behaviour (`LN-CHAIN-REORG`) is a separate obligation.
- No differential conformance against `rust-lightning` or BOLT vectors is
  claimed.
- The public `btc-lean` tree is not imported; no theorem is checked against it.

## 6. Residual risks / final-gate findings

1. **Final gate PASS at `68c236d`.** The earlier `check.sh` doc-comment false
   positive and the stale 132-file `check-final.py` assumption are fixed and
   committed. Both checkers are RC 0 at the final HEAD.
2. **Catalog strict mode remains RC 1 by design.** 23 unresolved planned
   `statementOnly` targets remain. `--allow-planned` is RC 0 and never promotes
   them; it is the mode used by the final gate, with the strict audit retained
   as the planning report.
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
`CrossChannelRouting` blowup, and pinned the public L1 reference. The result is
a 170-job RC 0 Lean tree with 18 exact catalog rows proved and 30 rows tracked
as statement-only.

It is still a conditional scaffold. Zero `sorry` is not zero assumptions: C1
and C8 are explicit finite/algebraic boundaries, L1 spendability depends on the
Phase-C2 bridges, and computational cryptographic security is not modelled. The
final gate is green at `68c236d`; the non-force push is the remaining action.
