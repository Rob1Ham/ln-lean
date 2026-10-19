# S11-CONF-MESSAGES — live BOLT 2 `accept_channel` differential row

**Lane:** `S11-CONF-MESSAGES`  
**Branch:** `repair/integrated`  
**Issue:** `CONF-01` (additional live message encodings)  
**Pinned source:** rust-lightning `fe4900930c6bd5786ec4203274d7cf312776a5a6`  
**Scope:** finite/public-API conformance only; **not** node-level interop.

## 1. Result

Added one new live BOLT 2 message row through the pinned public rust-lightning
`Writeable` API:

| Field | Value |
|---|---|
| Message | `accept_channel` |
| BOLT 2 type | `33` (`0x0021`) |
| Fixture id | `rust_msg_accept_channel_encoding` |
| Pinned unit test | `ln::msgs::tests::encoding_accept_channel` |
| Pinned construction | `do_encoding_accept_channel(false)` |
| Payload length | `270` bytes |
| Transport length | `272` (`2 + payload`) |
| Transport header | `0110` |
| Frame prefix | `00210110` (`type || header`) |
| Optional TLVs | none (`shutdown_scriptpubkey = None`, `channel_type = None`) |

The probe constructs the public `AcceptChannel` / `CommonAcceptChannelFields`
structs with the pinned test's all-`0x02` `temporary_channel_id`, pinned numeric
fields, and six real compressed points, then calls the pinned `Writeable`
implementation. The live encoding matches the pinned unit-test target
byte-for-byte.

All pre-existing rows are preserved: 26 BigSize, 3 TLV, 4 wire, and the
`channel_ready` (type 36) and `open_channel` (type 32) live rows.

## 2. Lean targets

Namespace: `LnLean.Proofs.Conformance.Diff` (lines 1147-1190 of
`LnLean/Proofs/ConformanceDiffTargets.lean`). All five are closed by `decide`:

| Target | Statement |
|---|---|
| `diff_msg_accept_channel_length` | `acceptChannelLiveFixture.payload.size = 270` |
| `diff_msg_accept_channel_transport` | `Transport.transportLength ⟨33, ...⟩ = 272` |
| `diff_msg_accept_channel_header` | `Transport.lengthHeader ⟨33, ...⟩ = bytes [0x01, 0x10]` |
| `diff_msg_accept_channel_frame_prefix` | `u16BE 33 ++ ... = bytes [0x00, 0x21, 0x01, 0x10]` |
| `diff_msg_accept_channel_payload` | `acceptChannelLiveFixture.payload = bytes [...270 bytes...]` |

The fixture row maps to these names under the `lean` object. No `sorry`,
`axiom`, `admit`, `native_decide`, `unsafe`, or `@[implemented_by]` was added.

## 3. Mutation controls

The checker's in-memory mutation suite increased from **16/16** to **18/18**.
The two new controls target the new row specifically:

1. `differential accept_channel payload byte changed` — flips the last payload
   byte; field/payload concatenation and length checks must reject it.
2. `differential accept_channel construction value changed` — increments
   `minimum_depth`; the construction-vs-field equality check must reject it.

Result: `mutation controls: 18/18 detected`.

## 4. Transcript and counts

- Live transcript: `tests/conformance/rust-lightning/live-transcript.json`
- Transcript SHA-256:
  `2677d760420fd934d1226825c5ce475697237787230947add967c133ee1df1a3`
- Fixture-row digest recorded in the transcript:
  `67db39d91e27c90e2ef3b4af9fa7f05721d744d0b5f13659a888f158cbf54608`
- Probe SHA-256:
  `8011be5b7413a6e84f0dc5f255bd0f90409e3147f1277739465491cdd0b0e0d2`
- Lockfile SHA-256 (unchanged):
  `856914ef1e21687d610769bad5c2476f97184c61781c4f7dfcc21a82f9010fa1`
- Live comparisons: `26 BigSize + 3 TLV + 4 wire + 3 BOLT 2 messages`
- Pinned cargo tests: `5/5` pass (BigSize, TLV, `channel_ready`,
  `open_channel`, `accept_channel`)
- Lean theorem references checked: **190** (was 185; +5)
- Vector message rows: 6 (`open_channel` 2, `accept_channel` 2,
  `commitment_signed` 1, `update_add_htlc` 1)
- Differential message fixtures: **3**

## 5. Commands run

```sh
python3 tests/conformance/rust-lightning/generate.py --check
python3 tests/conformance/rust-lightning/generate.py --live --record
python3 scripts/check-conformance.py
lake build LnLean.Proofs.ConformanceDiffTargets
```

`generate.py --live --record` ran, inside a disposable copy of the pinned
checkout with the committed 188-package `pinned/Cargo.lock`:

```sh
cargo test --offline --locked -p lightning --lib \
  util::ser::tests::bigsize_encoding_decoding -- --exact
cargo test --offline --locked -p lightning --lib \
  util::ser_macros::tests::retired_tlvs_skipped_on_read -- --exact
cargo test --offline --locked -p lightning --lib \
  ln::msgs::tests::encoding_channel_ready -- --exact
cargo test --offline --locked -p lightning --lib \
  ln::msgs::tests::encoding_open_channel -- --exact
cargo test --offline --locked -p lightning --lib \
  ln::msgs::tests::encoding_accept_channel -- --exact
cargo run --offline --locked -p lightning --example lnlean_conformance_probe
```

All cargo commands used `--offline --locked`; no network was used for the final
runs. Results:

- `generate.py --check`: PASS (26 BigSize, 3 TLV, 4 wire, 3 messages).
- `check-conformance.py`: PASS (61 vectors, 16 framing, 9 boundaries, 190 Lean
  references, 18/18 mutations).
- `lake build LnLean.Proofs.ConformanceDiffTargets`: PASS, 11 jobs, RC 0.

## 6. Changed files

- `tests/conformance/rust-lightning/live_probe.rs`
- `tests/conformance/rust-lightning/fixtures.json`
- `tests/conformance/rust-lightning/generate.py`
- `tests/conformance/rust-lightning/README.md`
- `tests/conformance/rust-lightning/live-transcript.json`
- `scripts/check-conformance.py`
- `LnLean/Proofs/ConformanceDiffTargets.lean`
- `agents/reports/swarm11/S11-CONF-MESSAGES.md` (this report)

No root import, catalog, traceability, audit, docs, or other Lean module was
edited. No commit or push was performed.

## 7. Remaining gaps

- This is finite/public-API conformance, not a full implementation test and not
  node-level interop.
- Only the no-TLV `accept_channel` base case is covered. The optional type-0
  `upfront_shutdown_script` and type-1 `channel_type` TLVs remain uncovered for
  this row; `open_channel` already has a separate finite TLV vector.
- The BOLT 8 header arithmetic is still checked against the pinned source, not
  exposed by the public API; only `LN_MAX_MSG_LEN` is probed live.
- Noise encryption/MACs, dispatch, full decoders, and arbitrary-message
  serialization remain out of scope.
- The row checks encoding only; it makes no signature-validity or channel-state
  claim.
