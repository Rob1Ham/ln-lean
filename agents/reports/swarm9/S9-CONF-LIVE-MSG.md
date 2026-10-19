# S9-CONF-LIVE-MSG — live BOLT 2 message row

**Lane:** `S9-CONF-LIVE-MSG`
**Issue:** `CONF-01`
**Base:** `repair/integrated` at `50e8b5c` (wave-9 launch from `10d18a1`)
**Status:** complete; the pinned offline harness supports the row, so no blocker
fallback was needed.

## Objective

Add a live BOLT 2 message row to the pinned rust-lightning differential harness
if the pinned checkout can exercise it **offline**.  The row must encode real
message fields through rust-lightning, not merely add another finite vector.
Preserve the existing 175 Lean theorem references, 13/13 mutation controls, six
`vectors.json` BOLT 2 message vectors, and declared-gap accounting.

## Outcome

The pinned rust-lightning checkout
`fe4900930c6bd5786ec4203274d7cf312776a5a6` supports this offline.  Its pinned
unit test `ln::msgs::tests::encoding_channel_ready` constructs a public
`ChannelReady` (BOLT 2 type 36) and compares the public `Writeable` encoding to
an exact target.  The live probe now constructs the same public struct from
command-line field values and calls the pinned `Writeable::encode`, and the
transcript compares that live payload byte-for-byte with the committed fixture.

The live row is therefore a real field-encoding comparison, not a replay of a
finite Python/Lean vector.  It is still **not** node-level interop (see
boundary below).

## Exact row / claims

Fixture id: `rust_msg_channel_ready_encoding`

| Field | Value |
|---|---|
| BOLT 2 message | `channel_ready` |
| type | `36` (`0x0024`) |
| channel id | `0202020202020202020202020202020202020202020202020202020202020202` (32 bytes) |
| next per-commitment point | `031b84c5567b126440995d3ed5aaba0565d71e1834604819ff9c17f5e9d5dd078f` (33-byte compressed point; public key for the all-`0x01` secret) |
| `short_channel_id_alias` | `None` (type-1 TLV absent) |
| payload | `0202020202020202020202020202020202020202020202020202020202020202031b84c5567b126440995d3ed5aaba0565d71e1834604819ff9c17f5e9d5dd078f` (65 bytes) |
| payload length | `65` |
| transport length | `67` (`2 + 65`) |
| transport header | `0043` |
| type + header prefix | `00240043` |

Pinned-source anchors:

- `lightning/src/ln/msgs.rs:431-443` — `ChannelReady` fields.
- `lightning/src/ln/msgs.rs:3239-3243` — BOLT 2 `channel_ready` field order
  (`channel_id`, `next_per_commitment_point`, optional type-1 alias TLV).
- `lightning/src/ln/msgs.rs:5672-5682` — pinned unit test
  `encoding_channel_ready` and its exact 65-byte target.
- `lightning/src/ln/msgs.rs` SHA-256:
  `75bc3698ab6e5595dcb02de23dceb52e37a25cd31621947387054fab2461a4f8`.

Lean theorems (new, all closed by `decide`):

- `diff_msg_channel_ready_payload`
- `diff_msg_channel_ready_length`
- `diff_msg_channel_ready_transport`
- `diff_msg_channel_ready_header`
- `diff_msg_channel_ready_frame_prefix`

## Artifacts changed (owned paths only)

- `tests/conformance/rust-lightning/fixtures.json`
  - new `fixtures.messages` group with the row above;
  - new `msgs.rs` provenance entry (five source files total);
  - updated live transcript hash and live-generation note.
- `tests/conformance/rust-lightning/live_probe.rs`
  - command `B <id> <alias|-> <channel_id> <point>` constructs a public
    `ChannelReady` and calls its pinned `Writeable::encode`.
- `tests/conformance/rust-lightning/generate.py`
  - re-extracts the `encoding_channel_ready` target from the pinned source;
  - derives the message row fields/lengths/header;
  - runs the new pinned test in `LIVE_TESTS`;
  - sends `B` probe commands and compares the live payload;
  - records `messages` in transcript comparison counts.
- `tests/conformance/rust-lightning/live-transcript.json`
  - regenerated offline; now includes the `encoding_channel_ready` pass and
    `messages: 1`.
- `scripts/check-conformance.py`
  - validates the differential message row, its field table/payload/lengths,
    its Lean references, and the transcript message count;
  - adds one mutation control for the new row.
- `LnLean/Proofs/ConformanceDiffTargets.lean`
  - adds `ChannelReadyWire`, the channel_ready field abbreviations/fixture, and
    the five theorems above.
- `tests/conformance/README.md`
- `tests/conformance/rust-lightning/README.md`

No forbidden/shared files were edited.  The other untracked wave-9 modules and
`agents/TODO-REPAIR.md` visible in `git status` belong to other lanes and were
not touched by this lane.

## Validation (exact)

### 1. Checker

```sh
python3 scripts/check-conformance.py
```

Exact output:

```text
vectors: 12 BigSize encode, 25 BigSize decode, 24 TLV
checks:  61 vector expectations validated
BOLT 1 Appendix A anchors: 26 published entries matched
TLV: 22 enforced cases, 2 declared not-modelled gaps
framing: 16 cases (6 accept, 10 reject), 9 length boundaries
messages: 6 BOLT 2 payload/field vectors (accept_channel 2, commitment_signed 1, open_channel 2, update_add_htlc 1)
differential: 26 rust-lightning BigSize, 3 TLV, 4 wire, 1 BOLT 2 message fixtures (pinned fe49009, offline)
differential TLV: 2 enforced, 1 declared not-modelled gaps
fixture generation: live-cargo-test (live cargo test: yes)
live evidence: 26 BigSize + 3 TLV compared against rust-lightning, 4 wire via live LN_MAX_MSG_LEN, 1 BOLT 2 channel_ready payload encoded live; transcript sha256 105920ff8e46
provenance: 5 pinned rust-lightning source files verified (HEAD verified)
Lean sync: 180 theorem references checked in LnLean/Proofs/ConformanceTargets.lean, LnLean/Proofs/ConformanceDiffTargets.lean
promoted transport: 13/13 theorems, 6/6 definitions checked in LnLean/Wire/Message.lean
mutation controls: 14/14 detected
RESULT: PASS (vector/differential conformance, not a full implementation test)
```

Exit status: `0`.

Preserved/updated accounting:

- six `vectors.json` BOLT 2 message vectors unchanged
  (`accept_channel 2`, `commitment_signed 1`, `open_channel 2`,
  `update_add_htlc 1`);
- the existing 175 Lean references all remain; five new references make
  `180`;
- the existing 13 mutation controls all remain; one new control makes
  `14/14` detected;
- declared gaps unchanged: vectors `22 enforced / 2 not-modelled`; differential
  TLV `2 enforced / 1 not-modelled`;
- promoted transport unchanged: `13/13` theorems, `6/6` definitions.

### 2. Deterministic fixture re-derivation

```sh
python3 tests/conformance/rust-lightning/generate.py --check
```

Exact output:

```text
fixtures: 26 BigSize, 3 TLV, 4 wire, 1 message match the pinned source
provenance: 5 source files verified at fe49009
live cargo test: recorded in tests/conformance/rust-lightning/live-transcript.json (105920ff8e46)
```

Exit status: `0`.

### 3. Offline live run (used to regenerate the transcript)

```sh
python3 tests/conformance/rust-lightning/generate.py --live --record
```

Relevant exact output:

```text
fixtures: 26 BigSize, 3 TLV, 4 wire, 1 message match the pinned source
provenance: 5 source files verified at fe49009
+ cargo test --offline --locked -p lightning --lib util::ser::tests::bigsize_encoding_decoding
+ cargo test --offline --locked -p lightning --lib util::ser_macros::tests::retired_tlvs_skipped_on_read
+ cargo test --offline --locked -p lightning --lib ln::msgs::tests::encoding_channel_ready
+ cargo run --offline --locked -p lightning --example lnlean_conformance_probe
live: 26 BigSize and 3 TLV fixtures agree with rust-lightning; 1 BOLT 2 channel_ready payload(s) encoded live; wire: 4 checked against live LN_MAX_MSG_LEN=65535
live transcript: /home/ubuntu/ln-lean-repair/tests/conformance/rust-lightning/live-transcript.json (105920ff8e460f80c9c6701d0c9c51b1d227587138ad56d7eaa9a794b3dc57dc)
recorded live transcript tests/conformance/rust-lightning/live-transcript.json in /home/ubuntu/ln-lean-repair/tests/conformance/rust-lightning/fixtures.json
```

Exit status: `0`.  No `--fetch` was used; all cargo commands were
`--offline --locked`.  Toolchain recorded in the transcript:
cargo `1.99.0 (5f94df478 2026-08-27)`, rustc `1.99.0 (b940084d7 2026-09-28)`.

### 4. Lean module build

```sh
export PATH=/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock lake build LnLean.Proofs.ConformanceDiffTargets
```

Exact output:

```text
Build completed successfully (11 jobs).
```

Exit status: `0`.

## Live / finite boundary

**Live (what the harness actually ran):**

- the pinned rust-lightning unit test `ln::msgs::tests::encoding_channel_ready`;
- a public-API probe that constructs `ChannelReady` from a 32-byte channel id,
  a 33-byte compressed point, and an optional alias, then calls the pinned
  `Writeable` implementation;
- a byte-for-byte comparison of the resulting 65-byte payload with the fixture,
  plus the live `LN_MAX_MSG_LEN = 65535` check for the wire rows.

**Finite / out of scope:**

- one message type and one field set per row; the committed row uses no alias
  TLV (the probe supports an alias, but no separate alias fixture is committed);
- no node-level interop, transport/Noise encryption, MACs, dispatch, full
  message decoding, signature validity, or semantic validation;
- wire header arithmetic remains a pinned-source check; only `LN_MAX_MSG_LEN`
  is probed live;
- the transcript is committed evidence checked by hash, not a Lean proof;
- this remains vector/differential conformance, **not** a full implementation
  test.

## Catalog-integration recommendation for `CONF-01`

The outstanding `CONF-01` next action ("Add the live BOLT 2 message row when
the pinned client can run offline") is now satisfied for `channel_ready`.
Recommended parent integration:

1. Add/retain the fixture identifier `rust_msg_channel_ready_encoding` as the
   `CONF-01` live-message evidence target, with the five theorem references
   `diff_msg_channel_ready_payload`, `diff_msg_channel_ready_length`,
   `diff_msg_channel_ready_transport`, `diff_msg_channel_ready_header`, and
   `diff_msg_channel_ready_frame_prefix`.
2. Update the `CONF-01` row to state: live BOLT 2 `channel_ready` (type 36)
   field encoding is compared against pinned rust-lightning `Writeable` output
   under `cargo --offline --locked`; counts are 6 finite message vectors, 1 live
   differential message row, 180 Lean references, 14/14 mutation controls, with
   the existing 2/1 declared gaps unchanged.
3. Do **not** describe this as full implementation or node-level conformance.
   Keep the finite/public-API caveat and leave `CONF-02`'s non-node caveat
   intact.  If the catalog requires a status, close the specific live-row
   action while retaining the P2 "additional encodings / node interop" boundary
   as future work rather than claiming complete protocol conformance.

## Summary

The offline pinned harness supports a genuine live BOLT 2 message encoding.
`S9-CONF-LIVE-MSG` adds the `channel_ready` (type 36) row, exercises the public
rust-lightning `Writeable` implementation, commits the regenerated transcript,
and keeps all existing vectors, mutation controls, finite counts, and declared
gaps green.  Lane complete; no blocker.
