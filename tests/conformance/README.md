# Wire conformance vectors (BigSize, TLV, and transport framing)

**This is vector/differential conformance, not a full implementation test.**  The
files here check a finite set of BOLT 1 encoded byte strings, the BOLT 8
transport frame, and pinned rust-lightning fixtures against the Lean model's
accept/reject decisions.  They do not cover IO, allocation limits,
message-specific TLV value decoding, namespace/known-type policy, Noise
encryption, or byte-for-byte equivalence with a running rust-lightning node.

## Files

| Path | Role |
|---|---|
| `tests/conformance/vectors.json` | authoritative BigSize, TLV, and framing vector set |
| `tests/conformance/rust-lightning/fixtures.json` | pinned rust-lightning differential fixtures and generation metadata |
| `tests/conformance/rust-lightning/generate.py` | deterministic pinned-source fixture re-derivation/verification and optional live cargo run |
| `tests/conformance/rust-lightning/README.md` | fixture provenance and offline runner notes |
| `scripts/check-conformance.py` | independent validator, promoted-model/provenance checks, Lean cross-check, and mutation controls |
| `LnLean/Wire/Message.lean` | payload-only frame **and** the promoted `LnLean.Wire.Transport` BOLT 8 model |
| `LnLean/Proofs/ConformanceTargets.lean` | `decide` theorems for every BigSize/TLV vector |
| `LnLean/Proofs/ConformanceDiffTargets.lean` | framing/differential vector theorems; imports the promoted transport model |
| `agents/reports/swarm4/S4-CONFORMANCE.md` | wave-4 lane report |
| `agents/reports/swarm5/S5-CONF-DIFF.md` | wave-5 framing/differential lane report |

## Run

```sh
python3 scripts/check-conformance.py
```

Exit status is 0 on success, 1 on a vector, framing, differential, provenance,
or Lean-sync mismatch, and 2 on usage/IO.  `--verbose` prints every vector;
`--no-lean` skips the theorem cross-check; `--no-diff` skips the rust-lightning
fixtures; `--no-self-test` skips the in-memory mutation controls.
`--no-provenance` skips the pinned-source SHA-256/HEAD check; by default the
checker verifies `refs/rust-lightning` when that checkout is present and prints
a skip line when it is not.  The checker is stdlib-only and needs no network or
Rust toolchain.

The fixture transcription itself can be re-derived and checked deterministically
against the pinned source (also offline):

```sh
python3 tests/conformance/rust-lightning/generate.py --check
```

`--write` rewrites the derived fixture fields; `--live` runs the two pinned
`cargo test` filters with `--offline` in a disposable copy and exits 4 on
failure.  A live attempt here failed on the incomplete offline cache
(`no matching package named backtrace`), so no live result is claimed; the
committed fixtures remain source-verified transcriptions.

The matching Lean build is module-only:

```sh
export PATH=/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Wire.Message LnLean.Proofs.ConformanceTargets \
    LnLean.Proofs.ConformanceDiffTargets
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

Every row names the Lean theorem(s) that state the same expectation.  Adding a
vector means adding the JSON row, the corresponding theorem(s) in the Lean
modules, and re-running the checker and the module build.  The checker verifies
that the theorem exists and that its first `bytes [...]` literal is the vector
input.

### Transport framing

The BOLT 8 transport frame is `type || transport_length || payload`, where
`transport_length = 2 + payload.size` counts the type and the payload.  This is
**not** the model's abstract payload-only `LnLean.Wire.frame`
(`type || payload.size || payload`).  The transport model is promoted to
`LnLean.Wire.Transport` in `LnLean/Wire/Message.lean`:
`Transport.transportFrame` and `Transport.unframeTransport` are the BOLT 8
encoder/decoder, while `Wire.frame`/`Wire.unframe` remain payload-only.
`Wire.unframe` rejects every transport frame; the generic theorem
`Transport.unframe_transportFrame_eq_none` records that boundary, so callers
cannot silently use the wrong decoder.

`framing.cases` rows are either complete valid frames (`type`, `payload`,
`declared_length`, `frame`) or malformed/truncated byte strings with an exact
rejection reason.  The `framing.boundaries` table pins payload lengths `0, 1,
252, 253, 256, 65532, 65533, 65534, 65535`, the two-byte header bytes, the frame
size, and whether the transport length fits.  At payload `65534` the transport
length is `65536`, which the fixed two-byte header truncates to `0000`; such a
message must be rejected by the size check, never framed.

### rust-lightning differential fixtures

`fixtures.json` records the pinned commit, per-file SHA-256 hashes, source
line ranges, the rust-lightning result, the model result, and the Lean theorem
that states the model's expectation.  BigSize fixtures preserve rust-lightning's
`InvalidValue`/`ShortRead` distinction (the model collapses both to `none`).
The TLV fixture set includes one declared `not-modelled:namespace-policy` gap:
rust-lightning rejects an unknown even type that the model accepts.  Wire
fixtures pin `LN_MAX_MSG_LEN = 65535` and the length-header convention.  The
fixtures are committed JSON and run offline; they are not a live Rust run.

The `generation` object records the deterministic path:
`tests/conformance/rust-lightning/generate.py` re-extracts the pinned unit-test
literals and compares every derived field, and `scripts/check-conformance.py`
verifies the recorded source hashes/HEAD when `refs/rust-lightning` is present.
The metadata says `live_cargo_test: false`; a future lane may only flip it after
`generate.py --live` actually succeeds and records a transcript hash.

## Sources

BOLT 1 Appendix A (BigSize), Appendix B (TLV), and §Lightning Message Format,
pinned at `refs/bolts/01-messaging.md` commit
`1aadb719b4007c4cea0ba6e36b08c4fb53788dee`.
BOLT 8 §Lightning Message Specification, pinned at
`refs/bolts/08-transport.md` (same boltd commit): the length prefix encodes the
total Lightning message length, maximum `65535`.
The rust-lightning canon is commit `fe4900930c6bd5786ec4203274d7cf312776a5a6`
(`lightning/src/util/ser.rs:442-490` for BigSize canonicality;
`lightning/src/ln/peer_channel_encryptor.rs:36,518-540` for the transport
length).
