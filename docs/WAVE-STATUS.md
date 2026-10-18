# Wave status — repair branch

**Repository:** `/home/ubuntu/ln-lean-repair`
**Branch:** `repair/integrated`
**HEAD:** `d5b8e9422c257f80c70c9100c2a092b676c89c23`
**Working tree:** K02's catalog promotion (`18 proved / 30 statementOnly`) and
regenerated index are uncommitted; `HEAD` is still `d5b8e94`.
**Toolchain:** `leanprover/lean4:v4.35.0`

This file describes the repair branch. The historical wave tables below are
the input to the repair; they are not a claim that the old final tree is the
current result.

## Current state

| Metric | Value |
|---|---|
| Lean files under `LnLean/` | **164** |
| Root imports in `LnLean.lean` | **162** (`LnLean.Proofs.All` and the `PhaseC2` aggregator are not root-imported) |
| Full build | **RC 0**, `Build completed successfully (170 jobs)` |
| Actual `sorry` lines | **0** (`grep -RInE '^[[:space:]]*sorry[[:space:]]*$' LnLean --include='*.lean'` → no matches, grep RC 1) |
| Proof files with the word `sorry` in prose | 15 (comments only, not proof terms) |
| Catalog rows | **48** |
| Catalog `proved` | **18** |
| Catalog `statementOnly` | **30** (23 planned/unresolved targets, 7 exact non-promotable) |
| Vendor snapshot | **OK**, 119 files |
| Anchors | **298 checked, 0 bad**, 2 unanchored rows |
| Generated obligation index | 128 proof files, 80 markers, 4135 declarations, 0 `sorry` sites |
| Public L1 pin | `Rob1Ham/btc-lean` `main@4f5c4f8` |
| Build dependency | `vendor/btc-lean-core` `f950806` |

The exact `sorry` result is **zero matching lines**. Fifteen files mention
`sorry` in documentation prose (for example “proved without `sorry`”); those
are not `sorry` terms.

### Pre-gate check status

- `lake build LnLean` — RC 0.
- `verify-vendor.sh` — RC 0.
- `verify-anchors.py` — RC 0.
- `check-public-reference.sh` — RC 0.
- `check-catalog.py --allow-planned` — RC 0
  (`rows=48 proved=18 statementOnly=30 planned=23 proved_failures=0`).
- `check-catalog.py --audit` (strict) — RC 1: the 23 planned
  `statementOnly` targets are errors in strict mode; no `proved` row fails.
- `check.sh` — **RC 0**: `files=164 obligations=81 sorry_in_proofs=0`,
  `check: OK`. An earlier raw-text false positive on a doc-comment occurrence
  of `sorry` in `LnLean/Proofs/ModelHardening/F13.lean:257` was fixed by
  making that pass comment-aware.

The final gate has **not** been declared; G01 owns it. No commit or push was
made by D02.

## Repair lanes completed

| Lane | Purpose | Output |
|---|---|---|
| `M01` | Make the SHA-256 interface consistent | Removed global `sha256_preimageResistant`; kept `sha256_size` and `sha256_collisionResistant`; retained `preimageResistant_vacuous` as a negative theorem |
| `M02` | Replace impossible global HMAC injectivity | Removed `hmac_prf`; proved `hmacPrf_vacuous`; C8 is finite-message `HmacBindsOn` in D07 |
| `K01` | Exact catalog checking | `scripts/check-catalog.py` / `.sh`; exact target resolution, `sorry`-free `proved` rows, promotion audit |
| `L01` | Public `btc-lean` reference | Pinned `main@4f5c4f8`; documented the 87-path vendor/public diff; added `scripts/check-public-reference.sh` |
| `CCR01` | Fix `CrossChannelRouting` blowup | Replaced overlapping/nested-pattern recursion; module RC 0 at ~1.7 GiB peak (was 12–19 GiB) |
| `R01`–`R10` | Repair the ten remaining refuted sites | Removed each false unconditional declaration plus marker; kept the counterexample and conditional replacement |

### Repaired sites

| Lane | Site | Removed claim | Retained strongest form |
|---|---|---|---|
| `R01` | `WaveE/E40` | `waveE_e40_accepted_update_signature_length` | `..._of_length_respecting` / `..._iff_lengthRespecting` |
| `R02` | `ModelHardening/F03` | `committedUpdate_preserves_ledger_unconditional` | `committedUpdate_preserves_ledger` |
| `R03` | `ModelHardening/F04` | `waveF_f04_legacy_unconditional_conservation` | `waveF_f04_corrected_conservation` |
| `R04` | `ModelHardening/F05` | `waveF_f05_accepted_update_key_announced` | `admitChannelUpdate_change_key_announced_after` |
| `R05` | `ModelHardening/F06` | `bindChannel_capacity_positive` | `bindChannelPositive_capacity_pos` / `bindChannel_capacity_pos_of_announced` |
| `R06` | `ModelHardening/F07` | `accepted_message_signatures_64` | `accepted_message_signatures_64_of_lengthRespecting` |
| `R07` | `ModelHardening/F09` | `dust_trim_preserves_conservation` | `conservation_of_dustFeeAccounted` |
| `R08` | `ModelHardening/F13` | `waveF_f13_unconditional_secret_match` | `accepted_secret_eq` |
| `R09` | `ModelHardening/F14` | `waveF_f14_running_total_bound` | `runningTotalBound_add` with `PartFits` |
| `R10` | `ModelHardening/F15` | `unconditional_settle_reveals_committed` | `bound_settle_reveals_committed` |

Each repair is a removal of a refuted unconditional headline, not a proof of
that headline. The negative/counterexample result and the conditional or
admitted-step replacement were retained and build without `sorry`.

## Catalog promotion (K02)

K02 promoted five K01 candidates:

| Id | Exact target | Module |
|---|---|---|
| `LN-CH-006` | `LnLean.Channel.Reserve.bounds` | `LnLean.Proofs.WaveD.D14` |
| `LN-PR-002` | `LnLean.Protocol.Handshake.channel_ready_gate` | `LnLean.Proofs.WaveD.D18` |
| `LN-PM-003` | `LnLean.Payment.Invoice.payment_secret_match` | `LnLean.Proofs.WaveD.D29` |
| `LN-PM-006` | `LnLean.Payment.Keysend.preimage_binding` | `LnLean.Proofs.WaveE.E31` |
| `LN-CR-004` | `LnLean.Wire.decode_encode` | `LnLean.Wire.BigSize` |

K02 also corrected two stale targets:

- `LN-CR-004`: `LnLean.Wire.BigSize.decode_encode` →
  `LnLean.Wire.decode_encode` (then promoted)
- `LN-CR-005`: `LnLean.Wire.TLV.WellFormed` →
  `LnLean.Wire.TLVStream.WellFormed`

`LN-CR-005` remains `statementOnly` because it is a predicate `def`, so it
cannot be promoted under the theorem/lemma rule. No promotion candidate
remains.

## Historical waves (repair input)

| Wave | Agents | Purpose | Output |
|---|---:|---|---|
| A | 8 | executable model modules, one per domain | `LnLean/{Bitcoin,Crypto,Wire,Channel,Protocol,Routing,Payment,Security}/` |
| B | 32 | proof statements and obligation markers | `LnLean/Proofs/**` |
| C | 16 | close remaining obligations | `wave-c/235` |
| D | 48 | independent proof attempts for 48 catalog targets | `wave-d/48` |
| E | 48 | second independent attempt | `wave-e/48` |
| F | 16 | model-hardening invariants and counterexamples | `wave-f/16` |
| G | 32 | read-only pairwise and cross-cutting audits | `wave-g/audit` |

The old `final/integrated` tree selected 132 Lean files (69 base + 33 D + 15 E
+ 15 F), had a 140-job build RC 0, and retained 15 `sorry` sites. The repair
branch adds the 17 Phase-C2 and 12 Phase-C3 modules and the repair lanes above;
it is **not** the old final tree.

## Trust boundary

### C1 / SHA-256

C1 is collision/second-preimage resistance on the 32-byte payment-preimage
domain (`CollisionResistant`), not global injectivity on arbitrary byte
strings. The global form is refuted by
`preimageResistant_vacuous`; it is not a `PrimitiveModel` field. Theorems over
`M : PrimitiveModel` are therefore **not vacuous** because of SHA-256.

C1 is an exact algebraic law, stronger than computational collision hardness.
No reduction is claimed.

### C8 / HMAC

C8 is the finite-execution predicate `HmacBindsOn hmac mu msgs` over the
messages of one onion peel. Global `HmacPrf` is refuted by `hmacPrf_vacuous`
and is not a field. The finite contract is satisfiable (singleton or pairwise
distinct tags); the caller supplies the finite list and evidence.

Computational HMAC security, PRF distinguishing advantage, and forgery
probability are outside the model. See `docs/HMAC-LIMITS.md` and
`docs/ASSUMPTIONS.md`.

### L1 and network

- The build uses the read-only vendor snapshot `f950806`; it is not an
  ancestor of public `btc-lean` `main@4f5c4f8`.
- The public `spec/core` is not imported and no theorem is checked against it.
- L1 spendability is conditional on the Phase-C2 bridge structures and
  explicit script/sighash/C1 hypotheses.
- Network liveness is conditional on partial synchrony and fairness; watchtower
  liveness and penalty economics are assumptions, not theorems.

## Known non-closures / planned work

- 23 `statementOnly` rows name declarations not yet present.
- 6 `statementOnly` rows name `def`s, not theorems.
- `LN-L1-004`: `toLocalScript` is a flat seam fragment, not the full BOLT 3
  two-branch witness script.
- `LN-PR-004`: both D20/E20 remain negative/conditional.
- `LN-SEC-003`: the named catalog declaration does not exist.
- `LN-SEC-005`: D34's at-stake field is post-fee; the uneconomical-penalty
  counterexample was withdrawn.
- `LN-CH-101`: there is no `Step.update_add_htlc` constructor; E37 models the
  affordability arithmetic on successor functions.
- `LN-GOSSIP-002`: the raw `applyGossip` path remains unguarded; E39 proves
  the guarded store result.
- `LN-CHAIN-REORG`: deep-reorg behaviour remains a separate obligation.
- No differential conformance against `rust-lightning`/BOLT vectors is
  claimed.

## Integrity

- `vendor/btc-lean-core/` is a read-only snapshot of `btc-lean` `spec/core` at
  `f95080638ae571a3664f4f41b9b6f6b4cfa7c5eb`. Source files are mode `0444`;
  `vendor/VENDOR-SHA256` lists 119 files and is checked by
  `scripts/verify-vendor.sh`. Vendor sources were not edited.
- `refs/rust-lightning` is pinned at
  `fe4900930c6bd5786ec4203274d7cf312776a5a6`.
- `refs/bolts` is pinned at
  `1aadb719b4007c4cea0ba6e36b08c4fb53788dee`.
- `refs/btc-lean` is an untracked, git-excluded symlink to
  `/home/ubuntu/btc-lean-public`; never commit it.

## Reproduce

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
```

`scripts/collect-obligations.py` rewrites generated documentation and is owned
by K02; do not run it just to inspect status.

## Honest status

An obligation is a named claim, not a proof. Zero actual `sorry` terms means
there are no unfinished proof bodies; it does **not** mean the 30
`statementOnly` rows are proved. Cryptographic correctness is conditional on
the interface fields in `PrimitiveModel` and on the finite C8 admission; it is
never asserted as an axiom. L1 correctness is conditional on the vendor seam
and the Phase-C2 bridges. The final gate and any push remain pending G01.
