# Wave-F integrator report

## Result

- Branch: `wave-f/16`
- Base: `a9f8d87`
- Modules: **16/16**
- Reports: **16/16**
- Proof declarations: **475**
- Remaining `sorry` sites: **10**
  - `F03`, `F04`, `F05`, `F06`, `F07`, `F09`, `F10`, `F13`, `F14`, `F15`
- Each open site is the faithful false/underspecified statement retained next
  to its `LN-WF-Fxx` marker, with a proved conditional or counterexample
  companion.

## Gate evidence

```text
python3 scripts/check-wave-f.py --strict --build   -> OK, 16/16 exact builds
./scripts/regen-root.sh                            -> root regenerated
lake build                                         -> RC 0, 93 jobs
verify-vendor.sh                                   -> OK (119 files)
check.sh                                           -> OK, 15 proof sorry sites
verify-anchors.py                                  -> OK
```

## Integration decisions

- The first F gate reached a green 93-job build but failed the policy check on
  `F10.lean:473`, where the marker was inline after `sorry`.  The marker was
  moved to its own line (comment-only); the rerun is green.
- `F10` remains excluded from the final combined tree by the Wave-G selection
  because its premise has a Msat/Nat mismatch and its marker was the only
  uncollectable one.  The module still builds and is retained on this branch.
- F is additive model-hardening work: no selected D/E module imports an F
  module.  The final tree imports the selected F modules directly.
- No model, vendor, or existing proof file was edited.
- Gate and index scripts now resolve the repository root from their own
  location.  `wave-f/.lake` and `refs/rust-lightning` are host-local symlinks
  and are not committed.

## Model gaps addressed

- Funding hash bridge (`F01`) and funding script parser safety (`F02`).
- Commitment conservation, anchor debit, dust/fee accounting, and output
  sorting (`F03`, `F04`, `F08`, `F09`).
- Gossip announced-key, positive-capacity, and signature admission
  (`F05`, `F06`, `F07`).
- Pre-sign fee gate (`F10`), HTLC exposure/reserve (`F11`).
- `channel_reestablish` no-rollback (`F12`).
- Payment-secret binding, MPP running-total bound, settlement preimage, and
  async safety/liveness (`F13`, `F14`, `F15`, `F16`).

## Reproduction

```sh
cd /home/ubuntu/ln-lean-wavef
python3 scripts/check-wave-f.py --strict --build
./scripts/integrate-f.sh
```
