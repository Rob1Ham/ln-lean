# Final status — Lightning repair tree

**Repository:** `/home/ubuntu/ln-lean-repair`
**Branch:** `repair/integrated`
**Gate HEAD:** `d2769d20d01e2b69e170e1dafcd2e29e1df888d2` (`[PROOF] add
eight-lane exact targets, promote 11 catalog rows`)
**Catalog state:** proof-wave tree: 29 `proved` / 19 `statementOnly`.
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
Lightning and it is not a conformance-tested implementation.

The repair branch adds the Phase-C2 and Phase-C3 modules, replaces the five
refuted Wave-C sites (`FundingProps`, `ReserveProps`, `GossipProps`), repairs
the ten remaining false/underspecified sites `R01`–`R10`, makes the crypto
interface consistent (`M01`, `M02`), adds the exact catalog checker (`K01`),
pins the public L1 reference (`L01`), and fixes the `CrossChannelRouting`
elaboration blowup (`CCR01`).

The proof-wave round runs eight disjoint lanes (`W01`, `R01`, `O01`, `H01`,
`C01`, `P01`, `M01`, `S01`) and promotes eleven exact catalog rows. The new
exact targets are in message framing, reestablish retransmission, gossip/route/
onion semantics, invoice/MPP payments, and security/liveness. The lanes that
could not state a faithful exact target did not fabricate one: `H01` and `C01`
added partition/trimming/id invariants plus retained counterexamples, and `P01`
documented the D17/E19/E20/FeatureClosure retargets for the remaining protocol
rows. Conditional promotions and scope caveats are recorded in
`docs/THEOREM-INDEX.md` and the per-lane reports.

## Verified state

Commands were run by G01 at the committed HEAD above. The branch was then
pushed non-force to `origin/repair/integrated`; no existing branch was
rewritten.

| Check | Command | Result |
|---|---|---|
| Full build | `flock -w 1800 /tmp/opencode/btc-lean/build.lock lake build` | **RC 0**, `Build completed successfully (170 jobs).` |
| Actual `sorry` | `grep -RInE '^[[:space:]]*sorry[[:space:]]*$' LnLean --include='*.lean'` | **0 matches** (grep RC 1: no lines) |
| Policy checker | `./scripts/check.sh` | **RC 0**, `files=164 obligations=81 sorry_in_proofs=0`, `check: OK` |
| Selection/root checker | `python3 scripts/check-final.py` | **RC 0**, `selected: D=33 E=15 F=15 total=63`, 164 Lean files, 162 root imports |
| Vendor integrity | `./scripts/verify-vendor.sh` | **RC 0**, `OK (119 files)` |
| Anchors | `python3 scripts/verify-anchors.py` | **RC 0**, `anchors=298 bad=0 unanchored_rows=2` |
| Catalog, strict | `python3 scripts/check-catalog.py --audit` | **RC 1**, 12 unresolved planned `statementOnly` targets, 0 `proved` failures |
| Catalog, planned-aware | `python3 scripts/check-catalog.py --allow-planned` | **RC 0**, `rows=48 proved=29 statementOnly=19 planned=12 proved_failures=0 candidates=0` |
| Traceability build | `lake build LnLean.Proofs.Traceability` | **RC 0**, 10 jobs |
| Public-reference pin | `./scripts/check-public-reference.sh` | **RC 0**, public HEAD/tag/vendor checks OK |
| Generated index | `docs/OBLIGATIONS-GENERATED.md` (regenerated) | `128` proof files, `80` markers, `48` catalog rows, `0` `sorry` sites |

Tree size: **164 Lean files** under `LnLean/`, **162** root imports in
`LnLean.lean`; `LnLean.Proofs.All` and the `LnLean.Proofs.PhaseC2` aggregator
are not root-imported. The full build covers 170 Lake jobs.

The `sorry` grep result is exact: **there are no lines consisting only of
`sorry` (modulo whitespace) in any `LnLean/**/*.lean` file.** Fifteen files
still contain the word `sorry` inside prose/comments; those are not proof
terms.

## Repair lanes completed

| Lane | Scope | Result |
|---|---|---|
| `R01`–`R10` | The ten remaining refuted/underspecified sites | Each refuted unconditional declaration and its marker removed; counterexample retained; conditional/admitted-step replacement retained; module builds RC 0 |
| `M01` | SHA-256 field in `PrimitiveModel` | Removed global `sha256_preimageResistant`; kept `sha256_size` and `sha256_collisionResistant`; `preimageResistant_vacuous` retained as a negative theorem |
| `M02` | HMAC field in `PrimitiveModel` | Removed global `hmac_prf`; `hmacPrf_vacuous` proves the global predicate impossible; C8 is finite-execution `HmacBindsOn`; D07 positive theorems take the finite contract |
| `K01` | Catalog checker | Added `scripts/check-catalog.py` / `.sh`: exact target resolution, `sorry`-free `proved` rows, promotion audit |
| `L01` | Public L1 reference | Pinned public `btc-lean` `main@4f5c4f8`; audited the 87-path vendor/public diff; added offline pin check |
| `CCR01` | `CrossChannelRouting` | Rewrote `lastAmount` and the telescoping-fee proof; module RC 0 at ~1.7 GiB peak instead of 12–19 GiB |

### Proof-wave lanes

| Lane | Scope | Exact promotions / retained gaps |
|---|---|---|
| `W01` | Wire message framing | `LN-CR-006` `Wire.Message.decode_length` |
| `R01` | Gossip and route | `LN-RT-002` `Gossip.update_monotone`, `LN-RT-005` `Route.cltv_accumulates` |
| `O01` | Onion peel/HMAC | `LN-RT-003` `Onion.peel_deterministic`, `LN-RT-004` `Onion.hmac_sound` (checked `openLayer`; D25 raw-peel counterexample preserved) |
| `P01` | Protocol reestablish | `LN-PR-005` `Peer.reestablish_no_rollback`; `LN-PR-001/003/004/006` left statement-only with D17/E19/E20/FeatureClosure retargets |
| `M01` | Invoice and MPP | `LN-PM-002` `Invoice.signature_valid`, `LN-PM-005` `MPP.running_total_bound` |
| `S01` | Security and liveness | `LN-SEC-002` `Conservation.global_conservation`, `LN-SEC-003` `Security.safety_async`, `LN-SEC-006` `Liveness.watchtower_bridge`; `LN-SEC-005` remains statement-only |
| `H01` | HTLC partition and live ids | No exact target: `LN-HT-003/004` need a balance/fee ledger or per-sender id counters; partition and insertion/filter invariants added, counterexamples retained |
| `C01` | Commitment outputs | No exact target: `LN-CH-002` needs the conservation premise; `LN-CH-003` is refuted unconditionally by D12; nonnegativity, sum, and trimming lemmas added |

`R01`–`R10` repaired these declarations:

| Lane | Removed unconditional/refuted declaration | Strongest retained replacement |
|---|---|---|
| `R01` | `waveE_e40_accepted_update_signature_length` | `waveE_e40_accepted_update_signature_length_of_length_respecting` |
| `R02` | `committedUpdate_preserves_ledger_unconditional` | `committedUpdate_preserves_ledger` (explicit `Affordable` hypothesis) |
| `R03` | `waveF_f04_legacy_unconditional_conservation` | `waveF_f04_corrected_conservation` (funder-debit hypotheses) |
| `R04` | `waveF_f05_accepted_update_key_announced` | `admitChannelUpdate_change_key_announced_after` |
| `R05` | `bindChannel_capacity_positive` | `bindChannelPositive_capacity_pos`, `bindChannel_capacity_pos_of_announced` |
| `R06` | `accepted_message_signatures_64` | `accepted_message_signatures_64_of_lengthRespecting` |
| `R07` | `dust_trim_preserves_conservation` | `conservation_of_dustFeeAccounted` |
| `R08` | `waveF_f13_unconditional_secret_match` | `accepted_secret_eq` |
| `R09` | `waveF_f14_running_total_bound` | `runningTotalBound_add` (with `PartFits`) |
| `R10` | `unconditional_settle_reveals_committed` | `bound_settle_reveals_committed` |

In every case the mechanized counterexample/negative theorem was kept. The
repair removes a false headline; it does not prove the refuted statement.

## Catalog status

The proof-wave counts are:

- **48 catalog rows**
- **29 `proved`**
- **19 `statementOnly`**
- **12** `statementOnly` rows name a planned declaration that does not yet
  exist (reported as `PLANNED` by `--allow-planned`)
- **7** `statementOnly` rows resolve exactly but are not theorem/lemma
  promotion candidates (all seven name `def`s or predicate `def`s).
- **0** promotion candidates remain.

The eleven proof-wave promotions are `LN-CR-006`, `LN-PR-005`,
`LN-RT-002`, `LN-RT-003`, `LN-RT-004`, `LN-RT-005`, `LN-PM-002`,
`LN-PM-005`, `LN-SEC-002`, `LN-SEC-003`, and `LN-SEC-006`. Each exact target
is a theorem with no `sorry` in its source body. The earlier five promoted
rows (`LN-CH-006`, `LN-PR-002`, `LN-PM-003`, `LN-PM-006`, `LN-CR-004`) remain
proved. `LN-CR-004` and `LN-CR-005` targets were corrected to the declarations
that actually exist (`LnLean.Wire.decode_encode`,
`LnLean.Wire.TLVStream.WellFormed`).

The newer promotions carry explicit scope caveats: `LN-RT-004` is the checked
`openLayer` path and raw `peel` retains the D25 HMAC counterexample;
`LN-PM-002` is a model-level projection from `Invoice.verify` and does not
prove ECDSA soundness; `LN-SEC-002` covers the multi-channel ledger but not an
L1 spend set; `LN-SEC-003` keeps the four explicit `Assumptions P`; and
`LN-SEC-006` requires `wt.reports`, not merely `wt.live`.

A `proved` row means the named Lean declaration exists and is sorry-free. It
does **not** mean the English claim is fully captured by that declaration;
that semantic check remains human review. A `statementOnly` row is a tracked
future theorem, not a result.

## Trust boundary

### C1 — SHA-256

`PrimitiveModel` no longer contains a global preimage-resistance field. C1 is

```lean
CollisionResistant H :=
  ∀ x y, x.size = 32 → y.size = 32 → H x = H y → x = y
```

applied to `M.sha256`. This is exact algebraic collision/second-preimage
resistance on the 32-byte payment-preimage domain used by Lightning. It is
**stronger** than a computational “no efficient collision finder” statement,
and no computational reduction is claimed.

Global injectivity `PreimageResistant H := ∀ x y, H x = H y → x = y` is not a
model field. `LnLean.Proofs.Crypto.Sha256Props.preimageResistant_vacuous`
proves that no 32-byte-output hash satisfies it. That theorem is a retained
negative result; it no longer contradicts `PrimitiveModel`, and theorems over
`M : PrimitiveModel` are not vacuous for this reason.

### C8 — HMAC-SHA256

C8 is the finite-execution admission

```lean
HmacBindsOn hmac mu msgs :=
  ∀ m₁ ∈ msgs, ∀ m₂ ∈ msgs, hmac mu m₁ = hmac mu m₂ → m₁ = m₂
```

where `msgs` is the finite list of `hop_payloads || associated_data` values in
one onion execution. Global HMAC injectivity `HmacPrf` is not a model field;
`LnLean.Proofs.WaveD.D07.hmacPrf_vacuous` proves it is impossible with the
32-byte output-width field. The finite contract is satisfiable: it holds by
construction on a singleton (`hmacBindsOn_singleton`) or whenever the finite
tags are pairwise distinct.

The caller must supply `msgs` and evidence that `HmacBindsOn` holds for that
execution. Tag-collision resistance, PRF distinguishing advantage, forgery
probability, and computational reductions are **outside the model**. The
mechanical facts (32-byte tag width, verifier equality, stored-tag extraction)
are proved unconditionally.

### Bitcoin L1

The build consumes `vendor/btc-lean-core` at `f950806`, a read-only snapshot
that is **not an ancestor of public `btc-lean` history**. The authoritative
public reference is `Rob1Ham/btc-lean` `main@4f5c4f8`; it is pinned for review
and is not imported by `lakefile.lean`.

The current build imports only `Bitcoin.Data.Basic`, `Bitcoin.Data.Script`,
`Bitcoin.Data.Tx`, and `Bitcoin.RuleAttr`. No theorem in this tree is checked
against the public `spec/core`. L1 spendability remains conditional on the
Phase-C2 bridge structures (`FundingSpendBridge`, `HTLCSpendBridge`,
`PenaltyL1Bridge`) and on explicit script-checker / sighash / C1 hypotheses.
`toLocalScript` is still a flat seam fragment, not the full BOLT 3 two-branch
witness script.

### Network, economics, liveness

Network results are conditional on explicit scheduling/fairness hypotheses.
Partial synchrony (delivery within `Δ` after GST) is always a hypothesis, never
an axiom. The watchtower bridge requires the tower to report the breach (which
implies liveness); `live` alone is insufficient. Penalty economics remains
unproved: the current unbounded fee model has a D34 counterexample, and a
bounded-feerate-schedule model is still needed.

## What remains conditional or planned

- **12 planned `statementOnly` targets** do not yet have declarations in this
  tree: `LN-CR-001/002/003`, `LN-CH-002/003`, `LN-HT-003/004`,
  `LN-PR-001/003/004/006`, and `LN-SEC-005`.
- **7 `statementOnly` rows** name `def`s or predicate `def`s rather than
  theorems, so the theorem/lemma rule cannot promote them.
- **19 rows remain `statementOnly`** in total; a green build and zero
  `sorry` sites do not make them proved.
- **L1 spendability** is conditional on the Phase-C2 bridge fields and on
  script/sighash semantics that are not imported from the public L1 tree.
- **Computational cryptography** (collision finding, PRF security, EUF-CMA,
  IND-CCA, CDH) is not modelled; the model uses exact algebraic laws as
  over-approximations.
- **No differential conformance** against `rust-lightning` or BOLT test
  vectors is claimed.
- **Full BOLT 3 script interpreter bridge** is not present; `LN-L1-004` is
  recorded as a flat seam fragment.
- **Deep-reorg behaviour** is a separate obligation (`LN-CHAIN-REORG`), not a
  proved property of this tree.

## Residual risks / final-gate findings

1. **The proof-wave gate is green at the commit recorded above.** The full
   build, vendor, anchors, `check.sh`, `check-final.py`, the planned-aware
   catalog audit, `LnLean.Proofs.Traceability`, and the exact `sorry` scan all
   returned the results in the table above.
2. **Catalog strict mode is RC 1 by design.** The 12 unresolved
   `statementOnly` targets are reported as errors by `--audit`;
   `--allow-planned` is RC 0 and keeps them `PLANNED`, never `proved`. The
   committed gate uses `--allow-planned`; the strict audit remains available
   as the planning report.
3. **Public/vendor lineage mismatch.** The vendor snapshot `f950806` is not in
   public `btc-lean` history; a future vendor bump is a separate deliberate
   change, not part of this repair. A green isolated compatibility branch
   (`repair/pubbump`) records the public `spec/core` bump but is intentionally
   not merged here.
4. **`refs/btc-lean` is an untracked symlink.** It is git-excluded and must
   not be committed.

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

Do not run `scripts/collect-obligations.py` merely to inspect status: it
rewrites `docs/OBLIGATIONS-GENERATED.md` and
`agents/status/obligations.json`. K02 owns that generated output.

## Not claimed

- No theorem here is a proof of Lightning Network security, of Bitcoin
  consensus, or of computational cryptographic hardness.
- A green build and zero actual `sorry` terms do not imply the 19
  `statementOnly` rows are proved.
- The eleven proof-wave promotions are exact model-level targets; the
  conditional caveats in this file and in `docs/THEOREM-INDEX.md` are part of
  their meaning and must not be dropped when citing them.
