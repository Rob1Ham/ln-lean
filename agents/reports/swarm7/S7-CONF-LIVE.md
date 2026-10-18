# S7-CONF-LIVE — pinned cargo cache, live rust-lightning comparison, and recorded transcript

**Lane:** `S7-CONF-LIVE`
**Issues:** `CONF-02`, `CONF-01`
**Branch / base:** `repair/integrated` @ `3180581` (wave 7 launch)
**Toolchain:** Lean `leanprover/lean4:v4.35.0`; live Rust `cargo 1.99.0
(5f94df478 2026-08-27)` / `rustc 1.99.0 (b940084d7 2026-09-28)`
**Status: complete (live run recorded).** The pinned cargo cache was completed
and `cargo test --offline --locked` now runs; both pinned rust-lightning unit
tests pass, a public-API probe compares all 26 BigSize and all 3 TLV fixtures
field-by-field against live rust-lightning output, and the 4 wire fixtures are
checked against the live `LN_MAX_MSG_LEN`. The run is recorded in a
deterministic transcript whose SHA-256 is pinned from `fixtures.json` and
verified by the checker. All existing counts stay green: 61 base + 16 framing +
9 boundary checks, 33 fixtures, 146 Lean references, 9/9 mutation controls.
No Lean theorem was added or changed; no forbidden construct was introduced and
no Git write was made.

---

## 1. Files

| Path | Role |
|---|---|
| `tests/conformance/rust-lightning/generate.py` | deterministic source re-derivation plus the live cargo/probe harness (`--live`, `--fetch`, `--record`, `--transcript`) |
| `tests/conformance/rust-lightning/live_probe.rs` | public-API Rust probe copied into the disposable checkout by `--live` |
| `tests/conformance/rust-lightning/pinned/Cargo.lock` | pinned dependency graph used by `cargo --offline --locked` |
| `tests/conformance/rust-lightning/live-transcript.json` | recorded live comparison and its provenance digests |
| `tests/conformance/rust-lightning/fixtures.json` | fixture rows unchanged; `generation` now records the live run/transcript hash; `lane` updated |
| `tests/conformance/rust-lightning/README.md` | live harness, lockfile, transcript, cache-bootstrap, and scope documentation |
| `tests/conformance/README.md` | run commands and live/offline boundary documentation |
| `tests/conformance/vectors.json` | lane/issue/scope metadata updated (no vector rows changed) |
| `scripts/check-conformance.py` | verifies the live transcript hash and its provenance; one mutation control upgraded |
| `LnLean/Proofs/ConformanceDiffTargets.lean` | module docstring only (no declaration or proof change) |
| `agents/reports/swarm7/S7-CONF-LIVE.md` | this report |

No forbidden file was edited. `LnLean/Wire/Message.lean`, `LnLean.lean`,
`Obligations.lean`, `Traceability.lean`, `AxiomAudit.lean`,
`scripts/check-final.py`, other lanes' files, shared docs outside
`tests/conformance/README.md`, and vendor sources (`refs/rust-lightning`,
`vendor/**`) were not touched. The cargo cache lives under `~/.cargo`, outside
the tree.

---

## 2. Why the wave-6 live attempt failed and what changed

The wave-6 `--live` path ran `cargo test --offline` against a cache that had no
crates.io index entry for `backtrace`. Cargo resolves that optional dependency
(`lightning/Cargo.toml:50`) while building the workspace lock graph, so the run
died before compiling:

```text
error: no matching package named `backtrace` found
location searched: crates.io index
required by package `lightning v0.3.0+git (.../rust-lightning/lightning)`
```

This lane completed the cache with a single online `cargo fetch --locked` and
then made the live path reproducible and offline:

1. **Pinned lockfile.** `pinned/Cargo.lock` (188 packages, SHA-256
   `856914ef1e21687d610769bad5c2476f97184c61781c4f7dfcc21a82f9010fa1`) is
   copied into the disposable checkout, and every live command uses
   `--locked`. It pins the exact dependency graph, including the `backtrace`
   entry, but the cache itself remains a machine-level artifact.
2. **Disposable checkout.** The vendored `refs/rust-lightning` symlink is never
   written; the script copies it (excluding `.git`/`target`) to a temp dir.
   `Cargo.lock` and the probe are installed only in that copy.
3. **Public-API probe.** `live_probe.rs` is placed in
   `lightning/examples/lnlean_conformance_probe.rs` of the copy. It uses only
   `BigSize`'s public `Readable`/`Writeable` impls, the exported
   `decode_tlv_stream!` macro, and the publicly re-exported
   `lightning::ln::LN_MAX_MSG_LEN`; it does not copy or reimplement the code
   under test.
4. **Direct comparison.** The probe consumes a TSV command stream generated
   from the committed fixtures and emits one TSV result per command; the script
   compares every field with `fixtures.json`.
5. **Deterministic transcript.** On success it writes JSON containing the
   pinned commit, fixture-row digest, probe/lock digests, cargo/rustc versions,
   per-test pass counts, comparison counts, and command/result digests. No
   timestamps or paths are recorded, so rerunning the same toolchain produces a
   byte-identical transcript (verified: the second run produced the same
   `3dd7a98f…` hash).
6. **Offline baseline retained.** `--check`, the checker, and the committed
   fixture replay still need no network and no Rust toolchain.

### 2.1 Cache bootstrap vs. the actual run

`--fetch` is the only online action: it runs `cargo fetch --locked` in the
disposable copy. The two `cargo test` commands and the `cargo run` probe remain
`--offline --locked`. Without a complete cache and without `--fetch`, the
script exits 4 with the cargo error and writes no transcript. This was verified
with `CARGO_HOME=/tmp/opencode/empty-cargo` (see §3.4).

---

## 3. Live run evidence

### 3.1 Exact command and output

```sh
python3 tests/conformance/rust-lightning/generate.py --live --fetch --record
```

Relevant output (paths abbreviated):

```text
fixtures: 26 BigSize, 3 TLV, 4 wire match the pinned source
provenance: 4 source files verified at fe49009
completing the cargo cache (one online fetch; the run below is --offline):
+ cargo fetch --locked
+ cargo test --offline --locked -p lightning --lib util::ser::tests::bigsize_encoding_decoding
+ cargo test --offline --locked -p lightning --lib util::ser_macros::tests::retired_tlvs_skipped_on_read
+ cargo run --offline --locked -p lightning --example lnlean_conformance_probe
live: 26 BigSize and 3 TLV fixtures agree with rust-lightning; wire: 4 checked against live LN_MAX_MSG_LEN=65535
live transcript: .../live-transcript.json (3dd7a98fc102cb7840c52944977b56ae5656acea7846c1a4a3b86e43d6db8fe6)
recorded live transcript tests/conformance/rust-lightning/live-transcript.json in fixtures.json
```

Both unit tests report `test result: ok. 1 passed; 0 failed` (1648 filtered
out). The probe emits 30 result lines: 26 BigSize, 3 TLV, and one
`LN_MAX_MSG_LEN`. The four wire rows use that live constant for `fits`; the
header arithmetic `msgbuf.len() - 16 - 2` is still the pinned-source string
check in `extract_wire`, because rust-lightning does not expose that computation
as public API.

### 3.2 Probe protocol

| Input line | Meaning | Output after `LNLEAN\t` |
|---|---|---|
| `E <id> <u64>` | encode a `BigSize` | `<id>\tok\t<hex>` |
| `D <id> <hex>` | decode a `BigSize` | `<id>\tok\t<value>\t<consumed>` or `<id>\t<error-class>` |
| `T <id> retired <hex>` | pinned retired/unlisted TLV readers | `<id>\taccept\t<a>\t<b>` or `<id>\t<error-class>` |
| `T <id> unlisted <hex>` | pinned unlisted-even reader | same |
| `M` | live maximum | `LN_MAX_MSG_LEN\t65535` |

Error classes are `invalid-value`, `short-read`, `unknown-required-feature`;
anything else is `other-error` and fails the comparison.

### 3.3 Transcript contents (`live-transcript.json`)

```json
{
  "schema": "lnlean.rust-lightning.live-transcript.v1",
  "pinned_commit": "fe4900930c6bd5786ec4203274d7cf312776a5a6",
  "fixture_rows_sha256": "c2c82b81…c4e1ca",
  "probe_sha256": "bf96ed9d…5431aa",
  "cargo_lock_sha256": "856914ef…010fa1",
  "toolchain": {"cargo": "cargo 1.99.0 …", "rustc": "rustc 1.99.0 …"},
  "tests": [
    {"name": "util::ser::tests::bigsize_encoding_decoding", "result": "ok", "passed": 1, "failed": 0},
    {"name": "util::ser_macros::tests::retired_tlvs_skipped_on_read", "result": "ok", "passed": 1, "failed": 0}
  ],
  "comparisons": {"bigsize": 26, "tlv": 3, "wire": 4},
  "wire_basis": "live LN_MAX_MSG_LEN; the length-header arithmetic remains the pinned-source check in extract_wire",
  "commands_sha256": "fd2d8871…a40b87",
  "results_sha256": "9d561d87…d82cbb"
}
```

`fixture_rows_sha256` hashes only the fixture rows (not `generation`), so
recording the transcript does not invalidate it. The committed transaction hash
is `3dd7a98fc102cb7840c52944977b56ae5656acea7846c1a4a3b86e43d6db8fe6`.

### 3.4 Negative controls exercised

| Control | Result |
|---|---|
| Empty `CARGO_HOME`, `--live`, fresh integration | RC 4, `no matching package named backtrace`, **no transcript written** |
| Forged `generation.live_transcript_sha256` in a fixture copy | Checker RC 1: `live transcript sha256 3dd7a98… != recorded 000…` |
| In-memory probe result mutated (`253 -> 254`) | `compare_live` reports `bigsize[rust_bigsize_decode_253]: live ['ok','254','3'] != fixture ['ok','253','3']` |
| `generate.py --write` on the committed file | byte-for-byte no-op |
| Repeat `--live --fetch --record` | identical transcript hash `3dd7a98f…` |

---

## 4. Checker changes and counts

`python3 scripts/check-conformance.py` → RC 0:

```text
vectors: 12 BigSize encode, 25 BigSize decode, 24 TLV
checks:  61 vector expectations validated
BOLT 1 Appendix A anchors: 26 published entries matched
TLV: 22 enforced cases, 2 declared not-modelled gaps
framing: 16 cases (6 accept, 10 reject), 9 length boundaries
differential: 26 rust-lightning BigSize, 3 TLV, 4 wire fixtures (pinned fe49009, offline)
differential TLV: 2 enforced, 1 declared not-modelled gaps
fixture generation: live-cargo-test (live cargo test: yes)
live evidence: 26 BigSize + 3 TLV compared against rust-lightning, 4 wire via live LN_MAX_MSG_LEN; transcript sha256 3dd7a98fc102
provenance: 4 pinned rust-lightning source files verified (HEAD verified)
Lean sync: 146 theorem references checked in LnLean/Proofs/ConformanceTargets.lean, LnLean/Proofs/ConformanceDiffTargets.lean
promoted transport: 13/13 theorems, 6/6 definitions checked in LnLean/Wire/Message.lean
mutation controls: 9/9 detected
RESULT: PASS (vector/differential conformance, not a full implementation test)
```

Count changes relative to the wave-6 gate:

| Item | Before | After |
|---|---:|---:|
| base vector expectations | 61 | 61 (unchanged) |
| framing cases / boundaries | 16 / 9 | 16 / 9 (unchanged) |
| rust-lightning fixtures | 26 + 3 + 4 = 33 | 33 (unchanged) |
| Lean theorem references | 146 | 146 (unchanged) |
| promoted transport checks | 13 thm + 6 def | 13 + 6 (unchanged) |
| pinned provenance files | 4 | 4 (unchanged, HEAD verified) |
| mutation controls | 9 | 9 (unchanged count) |
| live transcript checks | 0 | new `live evidence` line + transcript hash/provenance verification |

New checker helpers:

```python
def fixture_rows_digest(doc: dict[str, Any]) -> str
def check_live_transcript(generation: dict[str, Any], doc: dict[str, Any]) -> None
def check_generation(doc: dict[str, Any]) -> bool
```

When `generation.live_cargo_test` is true, `check_generation` requires
`mode == "live-cargo-test"`, a 64-hex `live_transcript_sha256`, an existing
transcript whose bytes hash to that value, the transcript schema, the pinned
commit, the fixture-row digest, the probe and lockfile digests, the exact
`{"bigsize": 26, "tlv": 3, "wire": 4}` counts, and a clean 1/0 pass for both
pinned test names. The wave-6 mutation control that flipped
`live_cargo_test = true` was upgraded (still one control) to forge the
transcript hash instead, because the committed flag is now legitimately true;
9/9 remains. `--no-lean` still reports 7/7, preserving the documented
Lean-dependent-control skip.

---

## 5. Build, axiom audit, and forbidden-construct scan

### 5.1 Module build (shared lock)

```sh
export PATH=/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Proofs.ConformanceDiffTargets
```

Result: `Build completed successfully (11 jobs).` RC 0. No full `lake build`
was run.

### 5.2 `#print axioms` (scratch file in `/tmp/opencode`, not in the tree)

21 declarations checked (5 promoted transport theorems, the compatibility
delegation, and 15 concrete differential/framing theorems):

| Axioms | Declarations |
|---|---:|
| none | 4 (`diff_bigsize_decode_253`, `diff_bigsize_reject_noncanonical_253`, `diff_wire_max_length`, `diff_wire_over_max_length`) |
| `propext` | 2 (`diff_tlv_unknown_even_2_admission`, `diff_tlv_truncated_2_decode`) |
| `propext`, `Quot.sound` | 12 |
| `propext`, `Classical.choice`, `Quot.sound` | 3 (`fits_iff_payload`, `boundary_fits_65533`, `boundary_not_fits_65534`) |

No `sorryAx`, no user axiom, no `native_decide`, no `unsafe`, no
`implemented_by`. Every axiom is in the allowed set.

### 5.3 Forbidden-construct scan

```sh
grep -RInE '\bsorry\b|\baxiom\b|\badmit\b|native_decide|@\[implemented_by\]|\bunsafe\b' \
  LnLean/Proofs/ConformanceDiffTargets.lean scripts/check-conformance.py \
  tests/conformance --include='*.lean' --include='*.py' --include='*.rs' --include='*.json'
```

No matches (grep RC 1).

### 5.4 Lean signatures kept

No declaration was added or changed. The module still contains the 56
framing/differential theorems and the wave-6 compatibility delegation; the
following representative signatures are unchanged:

```lean
theorem Transport.unframe_transportFrame_eq_none (m : WireMessage) :
    unframe (Transport.transportFrame m) = none

theorem boundary_fits_65533 (m : WireMessage) (h : m.payload.size = 65533) :
    m.fits

theorem boundary_not_fits_65534 (m : WireMessage) (h : m.payload.size = 65534) :
    ¬ m.fits

theorem boundary_frame_65533_roundtrip (m : WireMessage)
    (h : m.payload.size = 65533) :
    unframeTransport (Transport.transportFrame m) = some m

theorem diff_tlv_retired_skipped_decode :
    decodeTLV (bytes [0x02, 0x04, 0xff, 0xff, 0xff, 0xff, …]) = …

theorem diff_tlv_unknown_even_2_admission :
    decodeAdmissible (bytes [0x02, 0x04, 0xff, 0xff, 0xff, 0xff]) = true

theorem diff_wire_max_length : declaredForPayload 65533 = 65535

theorem diff_wire_over_max_length : declaredForPayload 65534 = 65536
```

The only Lean edit is the module docstring, which now states that the checker
is offline and that the optional live harness records a transcript as evidence
for the same finite rows, not as a new model theorem.

---

## 6. Scope caveats

1. **The live comparison is finite and public-API only.** It covers the 26
   BigSize rows and 3 TLV rows. It does not exercise private functions, message
   bodies, dispatch, or any behaviour outside those inputs.
2. **The wire row is only partly live.** `LN_MAX_MSG_LEN` is read live and used
   for `fits`; the `msgbuf.len() - 16 - 2` header computation is not public, so
   it remains the pinned-source string/arithmetic check in `extract_wire`.
   Noise encryption, MACs, and the real ciphertext header are out of scope.
3. **Not a node-level differential.** No rust-lightning node, channel, or
   network is started. The probe links the pinned library into a disposable
   example binary; that is stronger than a transcription but weaker than an
   end-to-end interoperability run.
4. **The transcript is evidence, not proof.** It is hash-pinned to the
   committed fixtures, probe, and lockfile, and the checker rejects missing,
   mismatched, or internally inconsistent transcripts. A determined forger
   could still fabricate a self-consistent JSON file without running cargo;
   per `docs/ASSUMPTIONS.md`, a differential runner is evidence and not in the
   TCB.
5. **The cache is machine-level.** `pinned/Cargo.lock` pins the graph, but the
   crate sources/index live in `~/.cargo`. A clean machine needs one
   `--live --fetch` bootstrap (network) or a pre-populated cache; the actual
   tests are always `--offline --locked`. The transcript records the exact
   cargo/rustc versions used.
6. **The TLV namespace gap is unchanged.** The model still accepts an unknown
   even type that rust-lightning rejects with `UnknownRequiredFeature`; it is
   the declared `not-modelled:namespace-policy` gap, not a conformance claim.
7. **No new vectors were added.** `CONF-01`'s "add more encodings" half is not
   addressed; only its live-differential-path half is.
8. **Full gate is parent-owned.** No full build, catalog, anchor, or
   `check-final.py` claim is made here.

---

## 7. Integration steps (for the parent)

1. **No root-import change.** `LnLean.lean` already imports
   `LnLean.Proofs.ConformanceDiffTargets`; no new Lean module exists.
2. **Commit the new harness files.** Add
   `tests/conformance/rust-lightning/live_probe.rs`,
   `tests/conformance/rust-lightning/pinned/Cargo.lock`, and
   `tests/conformance/rust-lightning/live-transcript.json` together with the
   modified `fixtures.json`, `generate.py`, READMEs, `vectors.json`, checker,
   and `ConformanceDiffTargets.lean` docstring.
3. **CI.** Keep `python3 scripts/check-conformance.py` as the mandatory gate.
   Optionally add `python3 tests/conformance/rust-lightning/generate.py --check`
   (stdlib-only, offline). Do **not** put `--live` in ordinary CI: it needs the
   Rust toolchain and a complete cache. If a CI runner has both, a separate
   non-blocking live job can run `--live` without `--record` and compare its
   transcript hash with the committed one; a differing toolchain will change
   the transcript, so treat that as informational unless the job also runs
   `--record` deliberately.
4. **Issue status.** `CONF-02` can be closed as "live offline run recorded"
   with the exact caveat that the wire header arithmetic remains source-derived
   and the comparison is finite/public-API. `CONF-01` stays open for new
   encodings, but its "live differential path" next action is now satisfied.
   Do not describe either as node-level interoperability.
5. **Shared docs.** Update the gate table's
   `fixture generation` line to `live-cargo-test (live cargo test: yes)` and
   add the `live evidence` line. No counts change.
6. **Cache reproducibility.** If the tree must be reproducible without network,
   publish the pinned crate cache (or a vendored cargo source replacement) as a
   separate artifact; the committed lockfile alone is not a cache.

---

## 8. Blockers / narrowed results

| Item | Effect |
|---|---|
| `msgbuf.len() - 16 - 2` is private | Wire rows use the live public `LN_MAX_MSG_LEN` but the header arithmetic stays a pinned-source check. |
| Cache is outside the tree | A clean machine needs one `--fetch` (network) or a pre-populated cache before `--offline` works. |
| Transcript is not attested | Self-consistent JSON can be fabricated; it is evidence pinned to committed inputs, not proof of execution. |
| No node/interop run | This is a library-level differential, not an end-to-end Lightning test. |
| `docs/OPEN-ISSUES.md` and shared generated indexes are parent-owned | The lane cannot record the status/gate edits. |

---

## 9. Summary

| Question | Answer |
|---|---|
| Pinned cargo cache completed? | Yes, via one `cargo fetch --locked`; subsequent commands are `--offline --locked` |
| Pinned dependency graph committed? | Yes, `pinned/Cargo.lock` (`856914ef…`) |
| `cargo test --offline` run? | Yes, both pinned unit tests pass 1/1 under `--offline --locked` |
| Live rust-lightning output compared with fixtures? | Yes: 26 BigSize + 3 TLV field-by-field; 4 wire via live `LN_MAX_MSG_LEN` |
| Live result recorded? | Yes, `live-transcript.json`, SHA-256 `3dd7a98f…` |
| Checker verifies the live claim? | Yes, transcript hash + fixture/probe/lock/commit provenance + test/count checks |
| 61 + 16 + 9 checks / 33 fixtures / 146 Lean refs green? | Yes, unchanged |
| Mutation controls? | 9/9 detected; forged-transcript control added (count unchanged) |
| Module build / checker RC? | 0 / 0 |
| Forbidden constructs? | None; axioms only `propext`, `Quot.sound`, `Classical.choice` |
| New Lean theorems? | None; docstring-only edit to `ConformanceDiffTargets.lean` |

**Final line for the parent:** S7-CONF-LIVE completes the pinned offline cache
path, adds a committed `Cargo.lock` + public-API `live_probe.rs`, runs both
pinned rust-lightning tests under `cargo --offline --locked`, compares all 26
BigSize and 3 TLV fixtures against live output and all 4 wire fixtures against
the live `LN_MAX_MSG_LEN`, and records a deterministic transcript
(`3dd7a98f…`) that the checker verifies. All prior counts (61 + 16 + 9, 33
fixtures, 146 Lean references, 9/9 mutation controls) stay green; `CONF-02` can
close with the wire-arithmetic/public-API caveat, while `CONF-01` remains open
only for additional encodings.
