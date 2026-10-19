# S10-CONF-LIVE-MSGS — additional live BOLT 2 message row (`open_channel`)

**Issue:** `CONF-01`
**Branch:** `repair/integrated`
**Launch HEAD:** `7988c93` (base `9158592`)
**Status:** complete; no commit or push.

## Result

Added one additional live BOLT 2 message row, encoded through the pinned
rust-lightning `Writeable` implementation under `cargo --offline --locked`:

* **`open_channel` (BOLT type 32)**, base case of the pinned unit test
  `ln::msgs::tests::encoding_open_channel` →
  `do_encoding_open_channel(false, false, false)`.
* 319-byte payload, transport length **321**, header **`0141`**, frame prefix
  **`00200141`**.
* The probe constructs the public `OpenChannel` /
  `CommonOpenChannelFields` structs and calls `message.encode()`; it does not
  call the private test helper and does not copy the encoding.
* `cargo test --offline --locked` passed all four pinned unit tests, including
  `encoding_open_channel`, and the probe ran with
  `cargo run --offline --locked` against the committed 188-package
  `pinned/Cargo.lock`. No network was used for the final run (the local cargo
  cache was sufficient).

The existing `channel_ready` (type 36) live row, all BigSize/TLV/wire rows, and
all finite BOLT 2 vectors are preserved unchanged.

## Fixture row

New differential fixture id: **`rust_msg_open_channel_encoding`**
(`tests/conformance/rust-lightning/fixtures.json`).

Source anchor: `ln/msgs.rs:5098-5188` (`do_encoding_open_channel`), called by
`ln::msgs::tests::encoding_open_channel`.

Construction (all values re-extracted by `generate.py` from the pinned unit
test target literal):

| Field | Value |
|---|---|
| `chain_hash` | `6fe28c0ab6f1b372c1a6a246ae63f74f931e8365e15a089c68d6190000000000` |
| `temporary_channel_id` | `0202…0202` (32 bytes) |
| `funding_satoshis` | `1311768467284833366` |
| `push_msat` | `2536655962884945560` |
| `dust_limit_satoshis` | `3608586615801332854` |
| `max_htlc_value_in_flight_msat` | `8517154655701053848` |
| `channel_reserve_satoshis` | `8665828695742877976` |
| `htlc_minimum_msat` | `2316138423780173` |
| `feerate_per_kw` | `821716` |
| `to_self_delay` | `49340` |
| `max_accepted_htlcs` | `49340` |
| `channel_flags` | `0x00` |
| `shutdown_scriptpubkey` / `channel_type` | absent (no TLVs) |

The 18-field table (offsets 0…318) is generated deterministically by
`extract_open_channel` and checked field-by-field by `check_diff_message`.

Payload (319 bytes, live result equals the pinned unit-test target and the
committed fixture):

```text
6fe28c0ab6f1b372c1a6a246ae63f74f931e8365e15a089c68d6190000000000
0202020202020202020202020202020202020202020202020202020202020202
1234567890123456233403289122369832144668701144767633030896203198
784335490624111800083a840000034d000c89d4c0bcc0bc
031b84c5567b126440995d3ed5aaba0565d71e1834604819ff9c17f5e9d5dd078f
024d4b6cd1361032ca9bd2aeb9d900aa4d45d9ead80ac9423374c451a7254d0766
02531fe6068134503d2723133227c867ac8fa6c83c537e9a44c3c5bdbdcb1fe337
03462779ad4aad39514614751a71085f2f10e1c7a593e4e030efb5b8721ce55b0b
0362c0a046dacce86ddd0343c6d3c7c79c2208ba0d9c9cf24a6d046d21d21f90f7
03f006a18d5653c4edf5391ff23a61f03ff83d237e880ee61187fa9f379a028e0a
00
```

## Lean theorems (`LnLean/Proofs/ConformanceDiffTargets.lean`)

All five follow the `channel_ready` pattern, use the existing
`Wire.Transport` model, and are closed by `decide`:

| Theorem | Statement |
|---|---|
| `diff_msg_open_channel_payload` | exact 319-byte payload |
| `diff_msg_open_channel_length` | `payload.size = 319` |
| `diff_msg_open_channel_transport` | `Transport.transportLength ⟨32, payload⟩ = 321` |
| `diff_msg_open_channel_header` | `Transport.lengthHeader … = bytes [0x01, 0x41]` |
| `diff_msg_open_channel_frame_prefix` | `u16BE 32 ++ lengthHeader … = bytes [0x00, 0x20, 0x01, 0x41]` |

The fixture reuses the module's existing `OpenChannelWire` record and the new
`openChannelLiveFixture` abbreviation. No shared model or catalog file was
edited.

## Checker updates

`scripts/check-conformance.py`:

* `DIFF_MESSAGE_TYPES` now admits `open_channel` (type 32) in addition to
  `channel_ready` (type 36), with per-message construction-key and field-order
  validation via the existing `check_message_field` reference.
* Construction values are cross-checked against every field value/bytes.
* `LIVE_TEST_NAMES` includes `ln::msgs::tests::encoding_open_channel`.
* Two mutation controls were added (open_channel construction value changed;
  open_channel payload byte changed), raising the suite from 14 to **16**
  controls.
* Output wording now names both live message rows.

`tests/conformance/rust-lightning/generate.py`:

* Re-extracts both pinned targets; `extract_open_channel` reconstructs the
  319-byte base target from the pinned chain-hash/fixed-body/zero-flags
  literals and splits/validates all 18 fields.
* Probe command dispatch adds `O` for `open_channel`.
* Pinned unit tests are invoked with `-- --exact`; this is required because the
  filter `encoding_open_channel` is a substring of `encoding_open_channelv2`.
* Provenance line range/use updated for `msgs.rs` (SHA-256 unchanged).

`tests/conformance/rust-lightning/live_probe.rs`:

* New public-API `encode_open_channel` using `OpenChannel`,
  `CommonOpenChannelFields`, `ChainHash::using_genesis_block(Network::Bitcoin)`,
  `ChannelId`, and `PublicKey::from_slice`; command `O`.

`tests/conformance/rust-lightning/README.md` and the Lean module header were
updated to describe both live rows. No `docs/` file was touched.

## Validation

```text
$ python3 scripts/check-conformance.py
differential: 26 rust-lightning BigSize, 3 TLV, 4 wire, 2 BOLT 2 message fixtures (pinned fe49009, offline)
differential TLV: 2 enforced, 1 declared not-modelled gaps
fixture generation: live-cargo-test (live cargo test: yes)
live evidence: 26 BigSize + 3 TLV compared against rust-lightning, 4 wire via live LN_MAX_MSG_LEN, 2 BOLT 2 message payload(s) (channel_ready, open_channel) encoded live; transcript sha256 9c6b664d7ac4
provenance: 5 pinned rust-lightning source files verified (HEAD verified)
Lean sync: 185 theorem references checked in LnLean/Proofs/ConformanceTargets.lean, LnLean/Proofs/ConformanceDiffTargets.lean
promoted transport: 13/13 theorems, 6/6 definitions checked in LnLean/Wire/Message.lean
mutation controls: 16/16 detected
RESULT: PASS (vector/differential conformance, not a full implementation test)
```

Scoped Lean build:

```text
$ LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
    lake build LnLean.Proofs.ConformanceDiffTargets
✔ [11/11] Built LnLean.Proofs.ConformanceDiffTargets (56s)
Build completed successfully (11 jobs).
```

Forbidden-construct scan of the owned Lean file:

```text
$ grep -nE "\b(sorry|axiom|admit|native_decide|unsafe)\b|implemented_by" \
    LnLean/Proofs/ConformanceDiffTargets.lean
(no matches)
```

## Live transcript / hash pinning

`tests/conformance/rust-lightning/live-transcript.json` (SHA-256
**`9c6b664d7ac43a8746482815105201d369135d38d411e0660c58a525335c7b62`**):

| Field | Value |
|---|---|
| `pinned_commit` | `fe4900930c6bd5786ec4203274d7cf312776a5a6` |
| `fixture_rows_sha256` | `a361078af15af2fb8e8eef737b57aece9a5355027b26868a8a3ac360814c879a` |
| `probe_sha256` | `17c1e5c4acc34ec6f751729ba58bc1e6846a1ae4ede37739f8ed57d441d1ebe6` |
| `cargo_lock_sha256` | `856914ef1e21687d610769bad5c2476f97184c61781c4f7dfcc21a82f9010fa1` |
| `commands_sha256` | `359e029f0f232d246029ac6ed58814dcb1a0f5c324547e17595fd3d96282becc` |
| `results_sha256` | `c699e760cc7378c544b14b03f61d8f8a5fef190fd588967ab42996989d3243d8` |
| `comparisons` | `{bigsize: 26, tlv: 3, wire: 4, messages: 2}` |
| tests | all four pinned tests `ok`, 1 passed / 0 failed each |

Toolchain: `cargo 1.99.0 (5f94df478 2026-08-27)`,
`rustc 1.99.0 (b940084d7 2026-09-28)`.

The prior transcript hash was `105920ff8e46…`; the new hash is expected because
the fixture rows, probe, commands, and test list changed.

## Precise scope / caveat

This is a **finite, public-API differential comparison** of one pinned
construction per message against the pinned rust-lightning `Writeable` impl.
It is **not** node-level interop and not full protocol conformance: it does not
exercise Noise encryption, the 16-byte MACs, message dispatch, full message
decoders, arbitrary-message serialization, signature validity, or BOLT 2 state
machines. The 319-byte `open_channel` row is the no-TLV base case only; the
optional `upfront_shutdown_script`/`channel_type` TLVs are covered only by the
existing finite vectors. The live transcript is evidence, not a proof; the
mechanized claims remain the five `decide` theorems above over the finite
payload.
