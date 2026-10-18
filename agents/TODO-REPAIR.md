# Repair TODO — integrated Lightning proof tree

**Worktree:** `/home/ubuntu/ln-lean-repair`
**Branch:** `repair/integrated` (from `final/integrated@af6caae`)
**Toolchain:** `leanprover/lean4:v4.35.0`
**L1 public reference:** `https://github.com/Rob1Ham/btc-lean` (`main@4f5c4f8`)
**Vendor L1 snapshot:** `f950806` (read-only; retained for build compatibility)

## Baseline (done)

- [x] Branch from the green `final/integrated` tree (132 modules, 15 open sites).
- [x] Add the 17 C2 repair modules and 12 C3 composition modules (29 total).
- [x] Replace the five refuted Wave-C sites with the C2 repaired files:
  `FundingProps`, `ReserveProps`, `GossipProps` (5 → 0 sites there).
- [x] Add `LnLean.Proofs.Common` so C2/C3 can share the base without a root import cycle.
- [x] Full root build: **170 jobs, RC 0**.
- [x] Remaining actual `sorry` sites: **10** (`WaveE/E40` + `F03,F04,F05,F06,F07,F09,F13,F14,F15`).

## R1 — Repair the ten remaining false/underspecified sites (0 `sorry` target)

Each site already has a mechanized counterexample and a proved conditional or
admitted-step replacement. The repair is to remove the refuted unconditional
declaration and its open marker, keeping the counterexample and conditional
form. Do **not** turn a false claim into `True`, do not add axioms, and do not
delete the negative result.

- [x] R01 — `LnLean/Proofs/WaveE/E40.lean` — `waveE_e40_accepted_update_signature_length`
- [x] R02 — `LnLean/Proofs/ModelHardening/F03.lean` — `committedUpdate_preserves_ledger_unconditional`
- [x] R03 — `LnLean/Proofs/ModelHardening/F04.lean` — `waveF_f04_legacy_unconditional_conservation`
- [x] R04 — `LnLean/Proofs/ModelHardening/F05.lean` — `waveF_f05_accepted_update_key_announced`
- [x] R05 — `LnLean/Proofs/ModelHardening/F06.lean` — `bindChannel_capacity_positive`
- [x] R06 — `LnLean/Proofs/ModelHardening/F07.lean` — `accepted_message_signatures_64`
- [x] R07 — `LnLean/Proofs/ModelHardening/F09.lean` — `dust_trim_preserves_conservation`
- [x] R08 — `LnLean/Proofs/ModelHardening/F13.lean` — `waveF_f13_unconditional_secret_match`
- [x] R09 — `LnLean/Proofs/ModelHardening/F14.lean` — `waveF_f14_running_total_bound`
- [x] R10 — `LnLean/Proofs/ModelHardening/F15.lean` — `unconditional_settle_reveals_committed`

## R2 — Crypto model consistency

- [x] `M01` — remove the globally inconsistent `sha256_preimageResistant` field
  from `PrimitiveModel`; retain the 32-byte `CollisionResistant` assumption and
  the non-vacuous `preimageResistant_vacuous` negative theorem. Update
  `rejectAllEcdsa` and all downstream uses. Result: the contradictory field pair
  is gone, `PrimitiveModel` is no longer forced uninhabited, SHA-256 headlines
  are no longer vacuous, and no `sorry` is added.

- [x] `M02` — remove the impossible global `hmac_prf` field from
  `PrimitiveModel`; retain only `hmac_size`; prove `hmacPrf_vacuous`; replace
  D07's global `HmacPrf` hypothesis with finite-message `HmacBindsOn`. Update
  `rejectAllEcdsa`, `docs/HMAC-LIMITS.md`, and the C8 text in
  `docs/ASSUMPTIONS.md`. No `sorry` or axiom is added.

- [x] `CCR01` — remove the `CrossChannelRouting` elaboration blowup by
  rewriting `lastAmount` as `(forwardAmounts path).getLastD 0` and proving
  `backwardConserves_sender_eq_last_add_feeSum` by ordinary list induction.
  Module RC 0 at ~1.7 GiB peak (previously 12–19 GiB / SIGKILL).

## R3 — Catalog mechanics

- [x] `K01` — add a source-level checker that resolves every catalog
  `leanTarget` exactly, rejects stale/missing names, and only marks a row
  `proved` when the exact declaration is a theorem/lemma with no `sorry` in its
  body. Keep `statementOnly` otherwise. Publish the candidate/decision table.

## R4 — Public `btc-lean` reference

- [x] `L01` — pin `refs/PINNED.md` and `docs/L1-PIN.md` to the public
  `Rob1Ham/btc-lean` repository; record `main@4f5c4f8`; add
  `refs/btc-lean -> /home/ubuntu/btc-lean-public` as a read-only reference;
  audit the 87-file vendor/public diff and the public script model. Do not
  edit `vendor/btc-lean-core`.

## R5 — Final gate

- [x] Full build with zero actual `sorry` in `LnLean/` — RC 0, 170 jobs,
  `sorry_in_proofs=0`.
- [x] Vendor integrity and anchor checks pass — 119 vendor files, 298 anchors,
  0 bad.
- [x] `scripts/check.sh` / policy checker passes — RC 0.
- [x] `python3 scripts/check-final.py` passes — 164 Lean files, 162 root
  imports.
- [x] Catalog checker passes and reports exact counts — 18 proved / 30
  statementOnly, 23 planned, 0 proved failures; `--allow-planned` RC 0.
- [x] Update `docs/FINAL-STATUS.md`, `docs/WAVE-STATUS.md`, and
  `agents/reports/FINAL-REPAIR.md` at final HEAD `68c236d`.
- [x] Non-force push of `repair/integrated` to `origin`; new remote branch
  created, no rewrite of `main` or another worker's branch. The isolated
  `repair/pubbump` compatibility branch was also pushed separately.

## R6 — Proof-wave round (done)

Supersedes the R5 catalog counts. Eight disjoint lanes ran against the green
repair tree; the catalog now has exact targets for eleven additional rows.

- [x] `W01` — `LN-CR-006` `LnLean.Wire.Message.decode_length`.
- [x] `R01` — `LN-RT-002` `Gossip.update_monotone`, `LN-RT-005`
  `Route.cltv_accumulates`.
- [x] `O01` — `LN-RT-003` `Onion.peel_deterministic`, `LN-RT-004`
  `Onion.hmac_sound` (checked `openLayer`; raw-`peel` D25 counterexample
  retained).
- [x] `P01` — `LN-PR-005` `Peer.reestablish_no_rollback`; D17/E19/E20/
  FeatureClosure retargets documented for the other protocol rows.
- [x] `M01` — `LN-PM-002` `Invoice.signature_valid` (model projection; C3
  remains an assumption), `LN-PM-005` `MPP.running_total_bound`.
- [x] `S01` — `LN-SEC-002` `Conservation.global_conservation` (multi-channel
  only), `LN-SEC-003` `Security.safety_async` (explicit `Assumptions P`),
  `LN-SEC-006` `Liveness.watchtower_bridge` (requires a report).
- [x] `H01` — no fake exact target; added HTLC partition and live-id
  invariants, retained the unconditional-id counterexample.
- [x] `C01` — no fake exact target; added commitment nonnegativity/sum/
  trimming lemmas, retained D46/D12 counterexamples.
- [x] At the end of R6: **29 proved / 19 statementOnly**, **12 planned**, 0
  promotion candidates.
- [x] Full build **170 jobs RC 0**; `check.sh`, `check-final.py`, vendor,
  anchors, public-reference, and planned-aware catalog audit all RC 0.
- [x] Commit and non-force push to `origin/repair/integrated`.

## R7 — Proof-wave 2 (done)

Five disjoint lanes extended the model and promoted eight more exact targets.

- [x] `SEC05-ECON` — `LN-SEC-005` `Liveness.penalty_economical` under
  `FeeScheduleBounded`; unconditional D34 spike counterexample retained.
- [x] `CH02-WF` — `LN-CH-002` `Commitment.outputs_nonnegative` under the BOLT 3
  balance equation; D46 retained.
- [x] `HT-LEDGER` — `LN-HT-003` `HTLC.amount_conservation` under the explicit
  ledger invariant; `LN-HT-004` deliberately retained.
- [x] `PR-WRAPPERS` — `LN-PR-001` `Handshake.open_bounds` and `LN-PR-006`
  `Handshake.feature_intersection` (support-set intersection, BOLT 1 survival).
  `LN-PR-003/004` deliberately retained as conditional characterizations.
- [x] `CR-RETARGET` — retargeted `LN-CR-001/002/003` from `PrimitiveModel`
  fields to `CryptoTargets` conditional contracts; D05/D07 counterexamples
  retained.
- [x] New modules `LnLean/Proofs/ProtocolTargets.lean` and
  `LnLean/Proofs/CryptoTargets.lean`; root imports and `AxiomAudit` extended.
- [x] Catalog: **37 proved / 11 statementOnly**, **1 planned** (`LN-CH-003`),
  3 exact-but-retained, 7 definition targets.
- [x] Full gate and non-force push after integration.

### Remaining planned/statement-only gaps

- `LN-CH-003`: unconditional ordering is false (D12); script/CLTV key absent.
  This is the only unresolved planned target.
- `LN-HT-004`: exact `id_unique` assumes `liveHtlcIdsNodup`; promoting it would
  assume the claimed uniqueness. Needs a model-level id allocator or per-sender
  counters that proves the invariant from insertion.
- `LN-PR-003`: wrapper is an iff characterization; the literal validity claim
  needs signing completeness and key binding.
- `LN-PR-004`: wrapper assumes the coverage predicate; it does not establish
  coverage from the wire record.
- Seven definition-target rows (`LN-L1-001/003/004/006`, `LN-CR-005`,
  `LN-CH-005`, `LN-RT-006`) are not theorem/lemma promotions.

## Commands

```sh
export PATH=/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
cd /home/ubuntu/ln-lean-repair
flock -w 1800 /tmp/ln-build.lock lake build LnLean
./scripts/verify-vendor.sh
python3 scripts/verify-anchors.py
./scripts/check.sh
python3 scripts/check-final.py
python3 scripts/check-catalog.py --allow-planned
```
