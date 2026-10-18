# Wire conformance vectors (BigSize, TLV, transport framing, BOLT 2 payloads)

**This is vector/differential conformance, not a full implementation test.**  The
files here check a finite set of BOLT 1 encoded byte strings, the BOLT 8
transport frame, a finite set of BOLT 2 message payload/field vectors
(`open_channel`, `accept_channel`, `commitment_signed`, `update_add_htlc`), and
pinned rust-lightning fixtures against the Lean model's decisions.  They do not
cover IO, allocation limits, message-specific TLV value decoding,
namespace/known-type policy, Noise encryption, signature validity, sender
identity, or byte-for-byte equivalence with a running rust-lightning node.

## Files

| Path | Role |
|---|---|
| `tests/conformance/vectors.json` | authoritative BigSize, TLV, framing, and BOLT 2 message-payload vector set |
| `tests/conformance/rust-lightning/fixtures.json` | pinned rust-lightning differential fixtures, live-run metadata, and generation provenance |
| `tests/conformance/rust-lightning/generate.py` | deterministic pinned-source fixture re-derivation/verification and the live cargo/probe harness |
| `tests/conformance/rust-lightning/live_probe.rs` | public-API Rust probe copied into the disposable checkout by `--live` |
| `tests/conformance/rust-lightning/pinned/Cargo.lock` | pinned dependency graph used by `cargo --offline --locked` |
| `tests/conformance/rust-lightning/live-transcript.json` | recorded live-run comparison (SHA-256 pinned from `fixtures.json`) |
| `tests/conformance/rust-lightning/README.md` | fixture/live-run provenance and harness notes |
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

`--write` rewrites the derived fixture fields; running it on the committed file
is a no-op.  `--live` copies the pinned checkout to a disposable directory,
installs `pinned/Cargo.lock` and `live_probe.rs`, runs the two pinned unit tests
and the public-API probe with `cargo test/run --offline --locked`, compares
every BigSize/TLV fixture field with the live result, checks the wire fixtures
against the live `LN_MAX_MSG_LEN`, and writes `live-transcript.json`.  It never
claims success on failure.

The cargo cache is a machine-level artifact.  On a machine without the pinned
crates, `--fetch` performs one online `cargo fetch --locked` to complete the
cache, then the same `--offline --locked` run follows; `--record` writes the
successful transcript hash into `fixtures.json`:

```sh
python3 tests/conformance/rust-lightning/generate.py --live --fetch --record
```

The committed transcript was produced with cargo/rustc `1.99.0`.  The actual
test/run commands are offline; only the optional `--fetch` bootstrap uses the
network.  Without a complete cache, `--live` exits 4 and writes no transcript.

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

### BOLT 2 message payloads

`messages.cases` holds six finite payload vectors from the pinned BOLT 2
layouts: two `open_channel` (type 32; 319-byte base and 343-byte type-0
`upfront_shutdown_script` TLV), two `accept_channel` (type 33; 270-byte base and
306-byte TLV), one `commitment_signed` (type 132; 226 bytes with two 64-byte
HTLC signatures), and one `update_add_htlc` (type 128; 1450 bytes with a
1366-byte onion).  Each row carries an ordered field table with byte offsets,
widths, and values, the concatenated payload, the transport header
(`transport_length = 2 + payload.size`), and the type-plus-header frame prefix.

The row bytes are independent fixtures: `open_channel` uses a local
`OpenChannelWire` record in `LnLean/Proofs/ConformanceDiffTargets.lean`, not
`LnLean.Protocol.Messages.Msg.openChannel`, and the other records are not
serializers from `Messages.lean`.  The checker rebuilds each payload from its
field table, validates the TLV envelope, recomputes the lengths and header, and
cross-checks the named Lean `decide` theorems.  The exact payload-equality
theorem is present for five rows; the 1450-byte `update_add_htlc` row pins
length, transport, header, and frame prefix only, and declares that omission in
its `lean.payload` field.  These vectors do **not** claim signature validity,
sender identity, handshake routing, or a live rust-lightning message
serialization comparison.

### rust-lightning differential fixtures

`fixtures.json` records the pinned commit, per-file SHA-256 hashes, source
line ranges, the rust-lightning result, the model result, and the Lean theorem
that states the model's expectation.  BigSize fixtures preserve rust-lightning's
`InvalidValue`/`ShortRead` distinction (the model collapses both to `none`).
The TLV fixture set includes one declared `not-modelled:namespace-policy` gap:
rust-lightning rejects an unknown even type that the model accepts.  Wire
fixtures pin `LN_MAX_MSG_LEN = 65535` and the length-header convention.  The
fixtures are committed JSON and are replayed offline by the checker.

The `generation` object records the live path:
`tests/conformance/rust-lightning/generate.py` re-extracts the pinned unit-test
literals, `--live` runs the pinned tests and the `live_probe.rs` public-API
probe under `cargo --offline --locked`, and `live-transcript.json` records the
per-group comparison (26 BigSize, 3 TLV, 4 wire) plus the pinned source, probe,
and lockfile hashes.  `scripts/check-conformance.py` verifies the transcript
hash and its provenance whenever `live_cargo_test` is true.  The live run does
not change the offline checker: every fixture row is still re-derived from the
pinned source and replayed without a Rust toolchain.

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
