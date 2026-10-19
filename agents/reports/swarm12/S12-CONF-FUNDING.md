# S12-CONF-FUNDING — live BOLT 2 `funding_created` and `funding_signed` differential rows

**Lane:** `S12-CONF-FUNDING`  
**Branch:** `repair/integrated`  
**Issue:** `CONF-01` (additional live message encodings)  
**Pinned source:** rust-lightning `fe4900930c6bd5786ec4203274d7cf312776a5a6`  
**Scope:** finite/public-API conformance only; **not** node-level interop.

## 1. Result

Both requested messages are supported by the pinned public API, so both are
implemented. There is **no public-API blocker**.

| Field | `funding_created` | `funding_signed` |
|---|---|---|
| BOLT 2 type | `34` (`0x0022`) | `35` (`0x0023`) |
| Fixture id | `rust_msg_funding_created_encoding` | `rust_msg_funding_signed_encoding` |
| Pinned unit test | `ln::msgs::tests::encoding_funding_created` | `ln::msgs::tests::encoding_funding_signed` |
| Payload length | `130` bytes | `96` bytes |
| Transport length | `132` (`2 + payload`) | `98` (`2 + payload`) |
| Transport header | `0084` | `0062` |
| Frame prefix | `00220084` (`type \|\| header`) | `00230062` |
| Optional TLVs | none | none |

`live_probe.rs` constructs the public `FundingCreated` / `FundingSigned`
structs from `lightning::ln::msgs` and calls the pinned `Writeable` impls. The
funding txid is built with the public `Txid::from_byte_array`; the compact
signature with the public `Signature::from_compact`. The live encoding matches
the pinned unit-test target byte-for-byte for both messages.

All pre-existing rows are preserved: 26 BigSize, 3 TLV, 4 wire, and the
`channel_ready` (type 36), `open_channel` (type 32), and `accept_channel`
(type 33) live rows.

## 2. Exact field values

`funding_created` construction:

| Field | Offset | Length | Value |
|---|---:|---:|---|
| `temporary_channel_id` | 0 | 32 | `0202020202020202020202020202020202020202020202020202020202020202` |
| `funding_txid` | 32 | 32 | `6e96fe9f8b0ddcd729ba03cfafa5a27b050b39d354dd980814268dfa9a44d4c2` |
| `funding_output_index` | 64 | 2 | `255` (`00ff`) |
| `signature` | 66 | 64 | `d977cb9b53d93a6ff64bb5f1e158b4094b66e798fb12911168a3ccdf80a83096340a6a95da0ae8d9f776528eecdbb747eb6b545495a4319ed5378e35b21e073a` |

`funding_created` payload (130 bytes):

```text
0202020202020202020202020202020202020202020202020202020202020202
6e96fe9f8b0ddcd729ba03cfafa5a27b050b39d354dd980814268dfa9a44d4c2
00ff
d977cb9b53d93a6ff64bb5f1e158b4094b66e798fb12911168a3ccdf80a83096
340a6a95da0ae8d9f776528eecdbb747eb6b545495a4319ed5378e35b21e073a
```

`funding_signed` construction:

| Field | Offset | Length | Value |
|---|---:|---:|---|
| `channel_id` | 0 | 32 | `0202020202020202020202020202020202020202020202020202020202020202` |
| `signature` | 32 | 64 | `d977cb9b53d93a6ff64bb5f1e158b4094b66e798fb12911168a3ccdf80a83096340a6a95da0ae8d9f776528eecdbb747eb6b545495a4319ed5378e35b21e073a` |

`funding_signed` payload (96 bytes):

```text
0202020202020202020202020202020202020202020202020202020202020202
d977cb9b53d93a6ff64bb5f1e158b4094b66e798fb12911168a3ccdf80a83096
340a6a95da0ae8d9f776528eecdbb747eb6b545495a4319ed5378e35b21e073a
```

Both targets are re-extracted by `generate.py --check` from the pinned unit-test
literals; `funding_txid` is checked as the reverse of the pinned
`Txid::from_str` display string.

## 3. Lean targets

Namespace: `LnLean.Proofs.Conformance.Diff` in
`LnLean/Proofs/ConformanceDiffTargets.lean`. All ten are closed by `decide`
and follow the existing `accept_channel`/`channel_ready` pattern.

| Target | Statement |
|---|---|
| `diff_msg_funding_created_length` | `fundingCreatedFixture.payload.size = 130` |
| `diff_msg_funding_created_transport` | `Transport.transportLength ⟨34, fundingCreatedFixture.payload⟩ = 132` |
| `diff_msg_funding_created_header` | `Transport.lengthHeader ⟨34, ...⟩ = bytes [0x00, 0x84]` |
| `diff_msg_funding_created_frame_prefix` | `u16BE 34 ++ Transport.lengthHeader ⟨34, ...⟩ = bytes [0x00, 0x22, 0x00, 0x84]` |
| `diff_msg_funding_created_payload` | `fundingCreatedFixture.payload = bytes [...130 bytes...]` |
| `diff_msg_funding_signed_length` | `fundingSignedFixture.payload.size = 96` |
| `diff_msg_funding_signed_transport` | `Transport.transportLength ⟨35, fundingSignedFixture.payload⟩ = 98` |
| `diff_msg_funding_signed_header` | `Transport.lengthHeader ⟨35, ...⟩ = bytes [0x00, 0x62]` |
| `diff_msg_funding_signed_frame_prefix` | `u16BE 35 ++ Transport.lengthHeader ⟨35, ...⟩ = bytes [0x00, 0x23, 0x00, 0x62]` |
| `diff_msg_funding_signed_payload` | `fundingSignedFixture.payload = bytes [...96 bytes...]` |

New records/abbreviations: `FundingCreatedWire`, `FundingSignedWire`,
`fundingChannelId`, `fundingCreatedTxid`, `fundingSignature`,
`fundingCreatedFixture`, `fundingSignedFixture`. No `sorry`, `axiom`, `admit`,
`native_decide`, `unsafe`, or `@[implemented_by]` was added.

## 4. Harness and checker updates

`tests/conformance/rust-lightning/live_probe.rs`:

* Imports public `FundingCreated`, `FundingSigned`, `Txid`, and the secp256k1
  `Signature`.
* Adds public-API encoders and probe commands `F` (`funding_created`) and `S`
  (`funding_signed`).

`tests/conformance/rust-lightning/generate.py`:

* Adds `extract_funding_created` and `extract_funding_signed`, including pinned
  field-order, length, and target-literal checks.
* Adds the two pinned tests to `LIVE_TESTS`; the live run now invokes **seven**
  `cargo test --offline --locked -- --exact` commands.
* Rebuilds probe stdin deterministically for the two new rows.
* Updates the provenance line range/use for `msgs.rs` (SHA-256 unchanged) and
  the live-run note.

`scripts/check-conformance.py`:

* `LIVE_TEST_NAMES` now includes `encoding_funding_created` and
  `encoding_funding_signed`.
* `DIFF_MESSAGE_TYPES` / `DIFF_MESSAGE_CONSTRUCTION_KEYS` /
  `MESSAGE_REQUIRED_FIELDS` admit types 34 and 35 with exact field order.
* Mutation controls added for both new rows:
  `funding_created` payload byte changed, `funding_created`
  `funding_output_index` changed, `funding_signed` payload byte changed, and
  `funding_signed` construction signature changed.
* The mutation suite increased from **18/18** to **22/22**.

`tests/conformance/rust-lightning/README.md` and the Lean module header were
updated to describe the five live message rows and the seven pinned tests.

## 5. Transcript and counts

- Live transcript: `tests/conformance/rust-lightning/live-transcript.json`
- Transcript SHA-256:
  `a47b2aa4a2e16f519efa451c0090262f1ebba80a3999fda8668ee554f2dbc892`
- Fixture-row digest: `1d5ed91c1342a66b69fc228e71ea68565756632d54dd25bfa46f3b90b57c0c14`
- Probe SHA-256: `822f3ba08ecac0961d0aeda8aa3bcb2aa94b8cd7393fb2d104eb434ccc392ccc`
- Lockfile SHA-256 (unchanged):
  `856914ef1e21687d610769bad5c2476f97184c61781c4f7dfcc21a82f9010fa1`
- `commands_sha256`: `0d750db69b41247baffc1d36621f545061c28ff654fd03007d8a6d3df69e3f5e`
- `results_sha256`: `9e0bde546cb1f7b7e8a4f3aca6c88fac5246334f2d21dd2a1b859d4f5fab8ac3`
- Live comparisons: `26 BigSize + 3 TLV + 4 wire + 5 BOLT 2 messages`
- Pinned cargo tests: **7/7** pass (`bigsize`, TLV, `funding_created`,
  `funding_signed`, `channel_ready`, `open_channel`, `accept_channel`)
- Differential message fixtures: **5**
- Lean theorem references checked: **200** (was 190; +10)
- Mutation controls: **22/22 detected**
- Toolchain: `cargo 1.99.0 (5f94df478 2026-08-27)`,
  `rustc 1.99.0 (b940084d7 2026-09-28)`

## 6. Commands run and exact results

```sh
python3 tests/conformance/rust-lightning/generate.py --check
python3 tests/conformance/rust-lightning/generate.py --live --record
python3 scripts/check-conformance.py
lake build LnLean.Proofs.ConformanceDiffTargets
```

Live run (disposable copy, committed `pinned/Cargo.lock`, all cargo commands
`--offline --locked`, no network used for the final run):

```text
+ cargo test --offline --locked -p lightning --lib util::ser::tests::bigsize_encoding_decoding -- --exact
+ cargo test --offline --locked -p lightning --lib util::ser_macros::tests::retired_tlvs_skipped_on_read -- --exact
+ cargo test --offline --locked -p lightning --lib ln::msgs::tests::encoding_funding_created -- --exact
+ cargo test --offline --locked -p lightning --lib ln::msgs::tests::encoding_funding_signed -- --exact
+ cargo test --offline --locked -p lightning --lib ln::msgs::tests::encoding_channel_ready -- --exact
+ cargo test --offline --locked -p lightning --lib ln::msgs::tests::encoding_open_channel -- --exact
+ cargo test --offline --locked -p lightning --lib ln::msgs::tests::encoding_accept_channel -- --exact
+ cargo run --offline --locked -p lightning --example lnlean_conformance_probe
live: 26 BigSize and 3 TLV fixtures agree with rust-lightning; 5 BOLT 2 message payload(s) encoded live (funding_created, funding_signed, channel_ready, open_channel, accept_channel); wire: 4 checked against live LN_MAX_MSG_LEN=65535
live transcript: /home/ubuntu/ln-lean-repair/tests/conformance/rust-lightning/live-transcript.json (a47b2aa4a2e16f519efa451c0090262f1ebba80a3999fda8668ee554f2dbc892)
```

Exact checker result:

```text
vectors: 12 BigSize encode, 25 BigSize decode, 24 TLV
checks:  61 vector expectations validated
BOLT 1 Appendix A anchors: 26 published entries matched
TLV: 22 enforced cases, 2 declared not-modelled gaps
framing: 16 cases (6 accept, 10 reject), 9 length boundaries
messages: 6 BOLT 2 payload/field vectors (accept_channel 2, commitment_signed 1, open_channel 2, update_add_htlc 1)
differential: 26 rust-lightning BigSize, 3 TLV, 4 wire, 5 BOLT 2 message fixtures (pinned fe49009, offline)
differential TLV: 2 enforced, 1 declared not-modelled gaps
fixture generation: live-cargo-test (live cargo test: yes)
live evidence: 26 BigSize + 3 TLV compared against rust-lightning, 4 wire via live LN_MAX_MSG_LEN, 5 BOLT 2 message payload(s) (funding_created, funding_signed, channel_ready, open_channel, accept_channel) encoded live; transcript sha256 a47b2aa4a2e1
provenance: 5 pinned rust-lightning source files verified (HEAD verified)
Lean sync: 200 theorem references checked in LnLean/Proofs/ConformanceTargets.lean, LnLean/Proofs/ConformanceDiffTargets.lean
promoted transport: 13/13 theorems, 6/6 definitions checked in LnLean/Wire/Message.lean
mutation controls: 22/22 detected
RESULT: PASS (vector/differential conformance, not a full implementation test)
```

Scoped Lean build:

```text
✔ [11/11] Built LnLean.Proofs.ConformanceDiffTargets (67s)
Build completed successfully (11 jobs).
```

## 7. Changed files (owned paths only)

- `tests/conformance/rust-lightning/live_probe.rs`
- `tests/conformance/rust-lightning/fixtures.json`
- `tests/conformance/rust-lightning/generate.py`
- `tests/conformance/rust-lightning/README.md`
- `tests/conformance/rust-lightning/live-transcript.json`
- `scripts/check-conformance.py`
- `LnLean/Proofs/ConformanceDiffTargets.lean`
- `agents/reports/swarm12/S12-CONF-FUNDING.md` (this report)

No catalog, traceability, root import, docs, audit, or other proof module was
edited. No commit or push was performed.

## 8. Precise scope / caveat

This is a **finite, public-API differential comparison** of one pinned
construction per message against the pinned rust-lightning `Writeable` impls.
It is **not** node-level interop and not full protocol conformance: it does not
exercise Noise encryption, the 16-byte MACs, message dispatch, full message
decoders, arbitrary-message serialization, signature validity, or BOLT 2 state
machines. The rows cover encoding only. The live transcript is evidence, not a
proof; the mechanized claims remain the ten `decide` theorems above over the
finite payloads.

## 9. Catalog-target recommendation for `CONF-01`

Recommend the parent keep **`CONF-01` open** as finite/public-API conformance,
and update its evidence pointer rather than close it:

* Add `funding_created` (type 34) and `funding_signed` (type 35) to the
  `CONF-01` live-message evidence list, alongside `channel_ready`,
  `open_channel`, and `accept_channel`.
* Record the new counts: **5** differential BOLT 2 message rows, **200** Lean
  theorem references, **22/22** mutation controls, and transcript
  `a47b2aa4a2e1…`.
* If the catalog tracks per-message targets, the new target names are the ten
  `diff_msg_funding_created_*` and `diff_msg_funding_signed_*` theorems above.
* Keep the explicit caveat that this is pinned `Writeable` encoding evidence,
  not node interop or a full implementation test. This lane narrows the
  `CONF-01` gap but does not by itself establish full protocol conformance.
