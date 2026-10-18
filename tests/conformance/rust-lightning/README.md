# Pinned rust-lightning differential fixtures and live harness

**Scope.**  These are committed, finite fixtures transcribed from the pinned
rust-lightning source at commit
`fe4900930c6bd5786ec4203274d7cf312776a5a6` (`refs/rust-lightning`).  They are
replayed by `scripts/check-conformance.py` without a network connection and
without a Rust toolchain.  `generate.py --live` additionally exercises the
pinned rust-lightning library through its public API and records the comparison
in `live-transcript.json`.  This is still **not** a full implementation test and
not a differential run against a rust-lightning node.

## Files

| Path | Role |
|---|---|
| `fixtures.json` | committed fixtures, provenance hashes, live-run metadata, and Lean theorem references |
| `generate.py` | deterministic pinned-source re-derivation/verification and the live cargo/probe harness |
| `live_probe.rs` | public-API probe copied into the disposable checkout by `--live` |
| `pinned/Cargo.lock` | pinned dependency graph for `cargo --offline --locked` |
| `live-transcript.json` | recorded live comparison and its provenance hashes |

`fixtures.json` records the commit, the SHA-256 of each source file used, and
the exact source lines.  The fixtures cover three behaviours:

1. **BigSize** (`lightning/src/util/ser.rs:1857-1901`, unit test
   `bigsize_encoding_decoding`): the eight canonical encode/decode values and
   all ten error inputs, split into rust-lightning's `InvalidValue`
   (non-minimal) and `ShortRead` (truncated/empty) classes.  The Lean model
   collapses both error classes to `none`; the fixture preserves the Rust class
   explicitly.
2. **TLV** (`lightning/src/util/ser_macros.rs:2047-2071`, unit test
   `retired_tlvs_skipped_on_read`): a four-record strictly increasing stream
   accepted by the message-specific reader, an unknown even type rejected with
   `UnknownRequiredFeature`, and a truncated record rejected with `ShortRead`.
   The unknown-even case is marked `not-modelled:namespace-policy` because the
   model has no even/odd policy; it is a declared gap, not a conformance claim.
3. **Wire framing** (`lightning/src/ln/peer_channel_encryptor.rs:36,518-540`
   and `lightning/src/ln/wire.rs:251-265`): the encrypted two-byte length
   header is `msgbuf.len() - 16 - 2`, i.e. the type plus payload, bounded by
   `LN_MAX_MSG_LEN = u16::MAX = 65535`.  This is the BOLT 8 transport length,
   not the model's payload-only length.

## Run

```sh
python3 scripts/check-conformance.py
python3 tests/conformance/rust-lightning/generate.py --check
```

The checker validates `fixtures.json` together with the BOLT vectors and the
Lean theorem cross-check, verifies the pinned source hashes/HEAD when
`refs/rust-lightning` is present, and — when `generation.live_cargo_test` is
true — verifies the transcript hash and the transcript's fixture-row, probe,
lockfile, and pinned-commit provenance:

```text
differential: 26 rust-lightning BigSize, 3 TLV, 4 wire fixtures (pinned fe49009, offline)
differential TLV: 2 enforced, 1 declared not-modelled gaps
fixture generation: live-cargo-test (live cargo test: yes)
live evidence: 26 BigSize + 3 TLV compared against rust-lightning, 4 wire via live LN_MAX_MSG_LEN; transcript sha256 3dd7a98fc102
provenance: 4 pinned rust-lightning source files verified (HEAD verified)
```

`--no-diff` skips these fixtures; `--no-lean` skips the theorem cross-check;
`--no-self-test` skips the in-memory mutation controls; `--no-provenance` skips
the optional pinned-source check.

`generate.py --check` (the default) verifies the four provenance hashes,
re-extracts the literal arrays and TLV stream from the pinned unit tests, and
fails if any committed derived field differs.  `generate.py --write` rewrites
those fields deterministically; running it on the committed file is a no-op.

## Live run

```sh
python3 tests/conformance/rust-lightning/generate.py --live
```

`--live` copies the pinned checkout to a disposable temp directory (never
writing `Cargo.lock`/`target` into `refs/`), installs the committed
`pinned/Cargo.lock` and `live_probe.rs`, and runs:

1. the two pinned unit tests with `cargo test --offline --locked`;
2. `live_probe.rs` with `cargo run --offline --locked`; the probe uses only the
   public `BigSize` `Readable`/`Writeable` impls, the exported
   `decode_tlv_stream!` macro, and `LN_MAX_MSG_LEN`, then prints one result per
   fixture input;
3. a field-by-field comparison of the live results with `fixtures.json`.

The probe compares all 26 BigSize rows and all 3 TLV rows.  The 4 wire rows are
checked against the live `LN_MAX_MSG_LEN = 65535`; their length-header
arithmetic remains the pinned-source check in `extract_wire` (the constant is
public, the header computation is not exposed as an API).  On success the
script writes `live-transcript.json` (deterministic JSON: pinned commit,
fixture-row digest, probe/lockfile hashes, cargo/rustc versions, per-test
results, comparison counts, and command/result digests) and prints its SHA-256.
On any cargo or comparison failure it exits non-zero and writes no transcript.

The committed transcript was produced with:

```text
cargo 1.99.0 (5f94df478 2026-08-27)
rustc 1.99.0 (b940084d7 2026-09-28)
```

The cargo registry cache is a machine-level artifact, not part of this tree.
On a machine without the pinned crates, run the one-time bootstrap:

```sh
python3 tests/conformance/rust-lightning/generate.py --live --fetch --record
```

`--fetch` performs an online `cargo fetch --locked` to complete the cache; the
subsequent tests and probe still run with `--offline --locked`.  `--record`
writes the successful transcript hash into `fixtures.json` (fixture rows are
unchanged).  Without `--fetch` and without a complete cache, `--live` exits 4
with the cargo resolution error and claims nothing.

## How the fixtures were produced

They were transcribed manually from the pinned unit tests and the length-header
code, and `generate.py --check` re-extracts every derived value from those same
pinned literals, so the committed file is reproducible and any drift is a hard
failure.  The `generation` object now records `mode = live-cargo-test`,
`live_cargo_test = true`, and the transcript hash; the live run independently
confirmed the 26 BigSize and 3 TLV rows and the live `LN_MAX_MSG_LEN`.

The wire fixture's `header` field is the plaintext two-byte value passed as
AEAD associated data in rust-lightning; the real transport encrypts that header
and appends MACs.  Noise encryption is out of scope.
