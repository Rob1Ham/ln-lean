# Wire conformance vectors (BigSize and TLV)

**This is vector conformance, not a full implementation test.** The files here
check a finite set of BOLT 1 encoded byte strings and the Lean model's
accept/reject decisions. They do not cover IO, allocation limits,
message-specific TLV value decoding, namespace/known-type policy, or
byte-for-byte equivalence with a running rust-lightning node.

## Files

| Path | Role |
|---|---|
| `tests/conformance/vectors.json` | authoritative vector set |
| `scripts/check-conformance.py` | independent validator and Lean cross-check |
| `LnLean/Proofs/ConformanceTargets.lean` | `decide` theorems for every vector |
| `agents/reports/swarm4/S4-CONFORMANCE.md` | lane report with exact results |

## Run

```sh
python3 scripts/check-conformance.py
```

Exit status is 0 on success, 1 on a vector or Lean-sync mismatch, and 2 on
usage/IO. `--verbose` prints every vector; `--no-lean` skips the theorem
cross-check.

The matching Lean build is module-only:

```sh
export PATH=/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Proofs.ConformanceTargets
```

## JSON shape

`bigsize.encode` rows carry `value`, `bytes`, and `length`; `bigsize.decode`
rows carry `bytes` and `expect` (`ok` with `value`/`consumed`, or `reject` with
`reason`). `tlv.cases` rows carry the input `bytes`, a `parser` decision and
records, a separate `admission` decision, the BOLT `spec` decision, and a
`model_scope`:

| `model_scope` | Meaning |
|---|---|
| `enforced` | parser and admission match BOLT for the modelled property |
| `enforced-by-admission` | structural parser accepts; strict-ordering admission rejects |
| `not-modelled:<name>` | the model's decision differs from BOLT; the gap is explicit |

Every row names the Lean theorem(s) that state the same expectation. Adding a
vector means adding the JSON row, the corresponding theorem(s) in
`LnLean/Proofs/ConformanceTargets.lean`, and re-running the checker and the
module build. The checker verifies that the theorem exists and that its first
`bytes [...]` literal is the vector input.

## Sources

BOLT 1 Appendix A (BigSize) and Appendix B (TLV), pinned at
`refs/bolts/01-messaging.md` commit `1aadb719b4007c4cea0ba6e36b08c4fb53788dee`.
The rust-lightning canonicality anchor is
`lightning/src/util/ser.rs:442-490` at commit
`fe4900930c6bd5786ec4203274d7cf312776a5a6`.
