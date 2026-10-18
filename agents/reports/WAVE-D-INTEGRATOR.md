# Wave-D integrator report

## Result

- Branch: `wave-d/48`
- Base: `a9f8d87`
- Modules: **48/48**
- Reports: **48/48**
- Proof declarations: **1,244**
- Remaining `sorry` sites: **2**
  - `LnLean/Proofs/WaveD/D37.lean:286` — `LN-WD-D37` (affordability guard)
  - `LnLean/Proofs/WaveD/D39.lean:73` — `LN-WD-D39` (gossip positive-capacity admission)
- Both open sites are the faithful false/underspecified statement adjacent to their
  obligation markers; each has a proved conditional/negative companion.

## Gate evidence

```text
python3 scripts/check-wave-d.py --strict --build   -> OK, 48/48 exact builds
./scripts/regen-root.sh                            -> 126 root imports
lake build                                         -> RC 0, 126 jobs
verify-vendor.sh                                   -> OK (119 files)
check.sh                                           -> OK
verify-anchors.py                                  -> OK
```

## Integration decisions

- D37 originally failed its exact build with `maximum recursion depth has been
  reached` and had no report.  An interim `D37Alt` replacement was prepared and
  built, but the original D37 agent then recovered the canonical module and
  report.  The interim replacement was discarded; the final canonical `D37`
  builds RC 0 with one documented `sorry`.
- No model, vendor, or existing proof file was edited.
- No Wave-D module imports another Wave-D module.

## Model gaps surfaced

The lane's negative results identify the remaining model-hardening work rather
than hiding it:

- `witnessScriptHash = SHA256(witnessScript.bytes)` is not a model invariant.
- Commitment outputs carry no script bytes, script identity, or HTLC
  `cltv_expiry`, so BOLT 3 ordering and CLTV tie-breaks are not representable.
- `Commitment` has no conservation invariant tying `totalOutputValue + fee` to
  `fundingValue`; anchors are not debited by the pair constructor.
- `PeerState.send` is not signature/funding-tx gated for `funding_signed`.
- `Gossip.bindChannel` has no announced-key, positive-capacity, or
  length-respecting signature admission.
- The L1 ledger has no satoshi value field, so the global value-conservation
  bridge needs an explicit valuation.

## Reproduction

```sh
cd /home/ubuntu/ln-lean
python3 scripts/check-wave-d.py --strict --build
./scripts/integrate-d.sh
```
