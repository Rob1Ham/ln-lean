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

- [ ] R01 — `LnLean/Proofs/WaveE/E40.lean` — `waveE_e40_accepted_update_signature_length`
- [ ] R02 — `LnLean/Proofs/ModelHardening/F03.lean` — `committedUpdate_preserves_ledger_unconditional`
- [ ] R03 — `LnLean/Proofs/ModelHardening/F04.lean` — `waveF_f04_legacy_unconditional_conservation`
- [ ] R04 — `LnLean/Proofs/ModelHardening/F05.lean` — `waveF_f05_accepted_update_key_announced`
- [ ] R05 — `LnLean/Proofs/ModelHardening/F06.lean` — `bindChannel_capacity_positive`
- [ ] R06 — `LnLean/Proofs/ModelHardening/F07.lean` — `accepted_message_signatures_64`
- [ ] R07 — `LnLean/Proofs/ModelHardening/F09.lean` — `dust_trim_preserves_conservation`
- [ ] R08 — `LnLean/Proofs/ModelHardening/F13.lean` — `waveF_f13_unconditional_secret_match`
- [ ] R09 — `LnLean/Proofs/ModelHardening/F14.lean` — `waveF_f14_running_total_bound`
- [ ] R10 — `LnLean/Proofs/ModelHardening/F15.lean` — `unconditional_settle_reveals_committed`

## R2 — Crypto model consistency

- [ ] `M01` — remove the globally inconsistent `sha256_preimageResistant` field
  from `PrimitiveModel`; retain the 32-byte `CollisionResistant` assumption and
  the non-vacuous `preimageResistant_vacuous` negative theorem. Update
  `rejectAllEcdsa` and all downstream uses. Result: `PrimitiveModel` is
  inhabited, SHA-256 headlines are no longer vacuous, and no `sorry` is added.

## R3 — Catalog mechanics

- [ ] `K01` — add a source-level checker that resolves every catalog
  `leanTarget` exactly, rejects stale/missing names, and only marks a row
  `proved` when the exact declaration is a theorem/lemma with no `sorry` in its
  body. Keep `statementOnly` otherwise. Publish the candidate/decision table.

## R4 — Public `btc-lean` reference

- [ ] `L01` — pin `refs/PINNED.md` and `docs/L1-PIN.md` to the public
  `Rob1Ham/btc-lean` repository; record `main@4f5c4f8`; add
  `refs/btc-lean -> /home/ubuntu/btc-lean-public` as a read-only reference;
  audit the 87-file vendor/public diff and the public script model. Do not
  edit `vendor/btc-lean-core`.

## R5 — Final gate

- [ ] Full build with zero actual `sorry` in `LnLean/`.
- [ ] Vendor integrity and anchor checks pass.
- [ ] `scripts/check.sh` / policy checker passes.
- [ ] Catalog checker passes and reports exact proved/statementOnly counts.
- [ ] Update `docs/FINAL-STATUS.md`, `docs/WAVE-STATUS.md`, and
  `agents/reports/FINAL-REPAIR.md` at the exact final HEAD.
- [ ] Non-force merge/push of `repair/integrated` to the remote; never rewrite
  `main` or the other worker's branches.

## Commands

```sh
export PATH=/dev/shm/btc/elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
cd /home/ubuntu/ln-lean-repair
flock -w 1800 /tmp/ln-build.lock lake build
./scripts/verify-vendor.sh
python3 scripts/verify-anchors.py
./scripts/check.sh
```
