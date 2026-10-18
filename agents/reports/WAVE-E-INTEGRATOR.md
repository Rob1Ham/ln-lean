# Wave-E integrator report

## Result

- Branch: `wave-e/48`
- Base: `6b451f9`
- Modules: **48/48**
- Reports: **48/48**
- Proof declarations: **1,177**
- Remaining `sorry` sites: **2**
  - `LnLean/Proofs/WaveE/E27.lean:341` — `LN-WE-E27` (gossip announcement admission)
  - `LnLean/Proofs/WaveE/E40.lean:167` — `LN-WE-E40` (gossip signature length admission)
- Both are the faithful unconditional statement adjacent to the obligation
  marker, with proved conditional/negative companions.

## Gate evidence

```text
python3 scripts/check-wave-e.py --strict --build   -> OK, 48/48 exact builds
./scripts/regen-root.sh                            -> root regenerated
lake build                                        -> RC 0, 125 jobs
verify-vendor.sh                                  -> OK (119 files)
check.sh                                          -> OK
verify-anchors.py                                 -> OK
```

## Integration decisions

- The first gate run exposed hard-coded `/home/ubuntu/ln-lean` paths in
  `regen-root.sh`, `check.sh`, `verify-vendor.sh`, and the index/anchor
  collectors.  Those scripts now resolve the repository root from their own
  location; the first run was discarded and the gate was rerun against the E
  worktree (125 jobs).
- The canonical E03 module was used; the isolated `E03Alt` replacement was
  removed after the canonical module landed green with its report.
- E01, E03, E43, and E47 reports all landed before the gate.
- No model, vendor, or existing proof file was edited.
- No Wave-E module imports another Wave-E module; the lane was kept independent
  of Wave D throughout.

## Model gaps surfaced

- Funding requires `witnessScriptHash = SHA256(witnessScript.bytes)` as an
  explicit bridge.
- Commitment outputs lack script bytes, script identity, and HTLC `cltv_expiry`,
  so BOLT 3 ordering/CLTV tie-breaks are not representable.
- `Commitment` lacks a conservation invariant tying outputs and fee to funding;
  anchor construction does not debit both anchors.
- `funding_signed` and `commitment_signed` are not signature/funding-tx gated.
- Gossip lacks announced-key, positive-capacity, and length-respecting verifier
  admission.
- The L1 ledger has no value field; global value conservation needs an explicit
  valuation.
- `Watchtower` has no `live → reports → confirmed penalty` bridge.

## Reproduction

```sh
cd /home/ubuntu/ln-lean-wavee
python3 scripts/check-wave-e.py --strict --build
./scripts/integrate-e.sh
```
