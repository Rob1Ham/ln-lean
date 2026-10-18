# S5-CONF-DIFF — transport framing and pinned rust-lightning differentials

**Lane:** `S5-CONF-DIFF`
**Issues:** `CONF-02` (new differential harness), `CONF-01` (extend vector suite)
**Branch / base:** `repair/integrated` @ `79a92ce` (code at `74d6475`)
**Toolchain:** `leanprover/lean4:v4.35.0`
**Status: complete.** Checklist, differential fixtures, Lean framing reference,
checker extension, and mutation controls are in place. Module build RC 0
(11 jobs), checker RC 0, existing 61 BigSize/TLV vector expectations unchanged
and green, forbidden-construct grep clean.

**Scope statement (important).** This is **vector/differential conformance, not
a full implementation test**. It checks a finite set of BOLT 1/BOLT 8 byte
strings and committed rust-lightning fixtures against the Lean model's
accept/reject decisions. It does not run a rust-lightning node, does not cover
Noise encryption/MACs, IO, allocation bounds, message bodies, or TLV
namespace/known-type policy.

---

## 1. Files

| Path | Role |
|---|---|
| `LnLean/Proofs/ConformanceDiffTargets.lean` | new transport-framing reference model and differential `decide` theorems |
| `tests/conformance/vectors.json` | existing 61 BigSize/TLV expectations unchanged; new `framing` object with 16 cases and 9 boundaries |
| `tests/conformance/rust-lightning/fixtures.json` | new pinned rust-lightning fixtures (26 BigSize, 3 TLV, 4 wire) |
| `tests/conformance/rust-lightning/README.md` | provenance, source hashes, offline-run caveat |
| `tests/conformance/README.md` | updated format/run documentation |
| `scripts/check-conformance.py` | framing/differential validation, multi-module Lean sync, 7 mutation controls |
| `agents/reports/swarm5/S5-CONF-DIFF.md` | this report |

No forbidden file was edited. `git status` shows only the owned paths above from
this lane; the modified model files and other new modules in the worktree belong
to other wave-5 lanes.

---

## 2. The framing reconciliation

There are two different two-byte fields:

| Convention | Bytes | Length value |
|---|---|---|
| model `LnLean.Wire.frame` | `type \|\| length \|\| payload` | `payload.size` (payload-only) |
| BOLT 8 transport frame | `type \|\| length \|\| payload` | `2 + payload.size` (whole Lightning message) |

BOLT 8 §Lightning Message Specification (pinned `refs/bolts/08-transport.md`
lines 416–450): each message is prefixed by a two-byte big-endian integer
encoding "the total length of the following Lightning message", maximum
`65535`. rust-lightning implements exactly that at
`lightning/src/ln/peer_channel_encryptor.rs:518-540`:

```rust
let msg_len = msgbuf.len() - 16 - 2;          // after the 18-byte length/MAC slot
if msg_len > LN_MAX_MSG_LEN { ... }           // LN_MAX_MSG_LEN = u16::MAX = 65535
...
&(msg_len as u16).to_be_bytes(),               // AEAD associated data
```

The new module documents and repairs the convention in a clearly separate
namespace, `LnLean.Proofs.Conformance.Diff.Transport`:

```lean
def transportLength (m : WireMessage) : Nat := 2 + m.payload.size
def transportFrame (m : WireMessage) : ByteArray :=
  u16BE m.type.toNat ++ lengthHeader m ++ m.payload
```

`Transport.transportLength` is definitionally `WireMessage.messageSize`.
`Transport.transportFrame` is `type || (payload.size + 2) || payload`.

**Exact decoder gap.**  The production model has only the payload-only decoder
`Wire.unframe`; it does not have a BOLT 8 transport decoder.  Its length check
compares the declared field with the payload length, so it cannot accept the
transport convention (two bytes larger).  The concrete witness is:

```lean
theorem payload_decoder_rejects_transport_frame :
    Wire.unframe
        (Transport.transportFrame ⟨16, bytes [0x01, 0x02, 0x03, 0x04]⟩) = none

theorem payload_decoder_accepts_model_frame :
    Wire.unframe (Wire.frame ⟨16, bytes [0x01, 0x02, 0x03, 0x04]⟩) =
      some ⟨16, bytes [0x01, 0x02, 0x03, 0x04]⟩
```

The `Transport` namespace is a conformance reference decoder, not a promoted
production path.  It rejects short headers, declared lengths below `2`,
truncated payloads, and trailing bytes.  Promoting it into
`LnLean/Wire/Message.lean` is an optional follow-up for the parent (see §8).

---

## 3. Framing vectors

`tests/conformance/vectors.json` keeps the 12 BigSize encode, 25 BigSize decode,
and 24 TLV rows byte-for-byte unchanged (`61` expectations).  It adds:

### 3.1 Complete valid frames (6)

| Id | Type | Payload | Declared | Frame |
|---|---:|---|---:|---|
| `frame_init_empty` | 16 | empty | 2 | `00100002` |
| `frame_init_four` | 16 | `01020304` | 6 | `0010000601020304` |
| `frame_type_zero` | 0 | `aabb` | 4 | `00000004aabb` |
| `frame_type_255` | 255 | `ff` | 3 | `00ff0003ff` |
| `frame_type_256` | 256 | empty | 2 | `01000002` |
| `frame_type_custom_65535` | 65535 | `2a` | 3 | `ffff00032a` |

### 3.2 Malformed/truncated frames (10)

| Id | Bytes | Rejection |
|---|---|---|
| `frame_empty` | empty | `missing-header` |
| `frame_short_header` | `001000` | `missing-header` |
| `frame_length_zero` | `00100000` | `length-too-small` |
| `frame_length_one` | `00100001` | `length-too-small` |
| `frame_truncated_declared_three` | `00100003` | `truncated` |
| `frame_truncated_declared_four_short` | `00100004aa` | `truncated` |
| `frame_trailing_one` | `00100002aa` | `trailing-bytes` |
| `frame_trailing_two` | `00100003aabb` | `trailing-bytes` |
| `frame_max_truncated` | `0010ffff` | `truncated` |
| `frame_zero_type_zero_length` | `00000000` | `length-too-small` |

### 3.3 Length boundaries (9)

The checker computes `declared = 2 + payload_length`, the fixed two-byte
header (`declared mod 65536`, big-endian), `frame_size = 4 + payload_length`,
and `fits = declared <= 65535` for every row.

| Payload length | Declared | Header | Frame size | Fits |
|---:|---:|---|---:|---|
| 0 | 2 | `0002` | 4 | yes |
| 1 | 3 | `0003` | 5 | yes |
| 252 | 254 | `00fe` | 256 | yes |
| 253 | 255 | `00ff` | 257 | yes |
| 256 | 258 | `0102` | 260 | yes |
| 65532 | 65534 | `fffe` | 65536 | yes |
| 65533 | 65535 | `ffff` | 65537 | yes |
| 65534 | 65536 | `0000` | 65538 | **no** |
| 65535 | 65537 | `0001` | 65539 | **no** |

The `65534`/`65535` rows are the important overflow controls: `u16BE` truncates
`65536` to `00 00` and `65537` to `00 01`.  The size check must reject such a
message before framing; the model proves `header_65536_truncates` and the
generic `boundary_not_fits_65534`.

---

## 4. Pinned rust-lightning differential fixtures

`tests/conformance/rust-lightning/fixtures.json` pins commit
`fe4900930c6bd5786ec4203274d7cf312776a5a6` and records per-file SHA-256 hashes
and source lines.  33 fixtures:

| Group | Count | Source |
|---|---:|---|
| BigSize | 26 | `lightning/src/util/ser.rs:1857-1901`, unit test `bigsize_encoding_decoding` |
| TLV | 3 | `lightning/src/util/ser_macros.rs:2047-2071`, unit test `retired_tlvs_skipped_on_read` |
| Wire | 4 | `lightning/src/ln/peer_channel_encryptor.rs:36,518-540`; `lightning/src/ln/wire.rs:251-265` |

Key behaviours pinned:

1. **BigSize.**  The eight canonical values and all ten error inputs from the
   rust-lightning unit test.  The fixture preserves rust-lightning's
   `InvalidValue` (non-minimal) versus `ShortRead` (truncated/empty) classes;
   the Lean model returns `none` for both.  The fixture records that collapse
   explicitly rather than pretending the model distinguishes the classes.
2. **TLV.**  The four-record strictly increasing stream
   `0204ffffffff0308deadbeef1badbeef0502123407041bad1dea` is accepted by the
   rust-lightning message-specific reader and by the model.  An unknown even
   type `0204ffffffff` is rejected by rust-lightning with
   `UnknownRequiredFeature` but accepted by the model: this is a measured
   `not-modelled:namespace-policy` differential gap.  A truncated record
   `0204ffff` is `ShortRead` in rust-lightning and rejected by the model.
3. **Wire.**  `init` (`type = 16`) with empty/four-byte payloads pins transport
   lengths `2`/`6`; the maximum legal length `65535` is accepted; `65536` is
   rejected by `LN_MAX_MSG_LEN` and does not fit the two-byte header.

The runner is fully offline: it loads the committed JSON only.  It does not
invoke `cargo`, clone sources, or contact the network.  Fixtures were
transcribed from the pinned unit tests/code, not generated by a live
differential process; the source hashes are the reproducibility anchor and
`tests/conformance/rust-lightning/README.md` states this explicitly.  A live
`cargo test --offline` generation run was attempted in the reference clone but
the local cache lacks the `backtrace` crate; that does not affect the committed
fixtures or the offline checker.

---

## 5. Checker

`python3 scripts/check-conformance.py` validates all four layers and runs
in-memory mutation controls.  Exact final output:

```text
vectors: 12 BigSize encode, 25 BigSize decode, 24 TLV
checks:  61 vector expectations validated
BOLT 1 Appendix A anchors: 26 published entries matched
TLV: 22 enforced cases, 2 declared not-modelled gaps
framing: 16 cases (6 accept, 10 reject), 9 length boundaries
differential: 26 rust-lightning BigSize, 3 TLV, 4 wire fixtures (pinned fe49009, offline)
differential TLV: 2 enforced, 1 declared not-modelled gaps
Lean sync: 146 theorem references checked in LnLean/Proofs/ConformanceTargets.lean, LnLean/Proofs/ConformanceDiffTargets.lean
mutation controls: 7/7 detected
RESULT: PASS (vector/differential conformance, not a full implementation test)
```

The existing first lines (`61` vectors, `26` BOLT Appendix A anchors, `22`
enforced / `2` TLV gaps) are unchanged.

**Mutation controls (7/7 detected, default run):**

1. framing valid case `declared_length + 1`;
2. framing reject reason changed;
3. framing boundary `fits` flipped;
4. differential BigSize bytes changed;
5. differential wire transport length `+1`;
6. differential TLV record value changed;
7. framing Lean theorem reference removed.

Options: `--verbose`, `--no-lean`, `--no-diff`, `--no-self-test`,
`--vectors PATH`, `--diff-fixtures PATH`, and repeatable `--lean-file PATH`.
`--lean-file` keeps the old single-module behaviour; the default is both Lean
modules.  Exit status remains 0 pass / 1 mismatch / 2 usage-IO.

---

## 6. Lean module

Build:

```sh
cd /home/ubuntu/ln-lean-repair
export PATH=/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Proofs.ConformanceDiffTargets
```

Result: `Build completed successfully (11 jobs)`, RC 0.  The unchanged
`LnLean.Proofs.ConformanceTargets` also builds in the same lock (12 jobs total).

The module has **65 theorems** (plus definitions/helpers).  Small vectors are
closed by kernel `decide`; the large boundaries use the proved length lemmas so
no 65K-byte array is reduced.  Representative signatures:

```lean
-- transport frame and size
theorem transportLength_eq_messageSize (m : WireMessage) :
    Transport.transportLength m = m.messageSize

theorem transportFrame_size (m : WireMessage) :
    (Transport.transportFrame m).size = 4 + m.payload.size

theorem fits_iff_transportLength (m : WireMessage) :
    m.fits ↔ Transport.transportLength m ≤ MAX_MESSAGE_SIZE

-- round trip and declared-length law
theorem unframeTransport_transportFrame (m : WireMessage)
    (h : m.payload.size < 65534) :
    unframeTransport (Transport.transportFrame m) = some m

theorem decode_transport_length (b : ByteArray) (m : WireMessage)
    (h : unframeTransport b = some m) :
    declaredTransportLength? b = some m.messageSize ∧
      (bytesToList b).drop 4 = bytesToList m.payload ∧
      b.size = 4 + m.payload.size

-- exact model-decoder gap
theorem payload_decoder_rejects_transport_frame :
    Wire.unframe
        (Transport.transportFrame ⟨16, bytes [0x01, 0x02, 0x03, 0x04]⟩) = none

-- concrete framing vectors
theorem frame_init_four :
    Transport.transportFrame ⟨16, bytes [0x01, 0x02, 0x03, 0x04]⟩ =
      bytes [0x00, 0x10, 0x00, 0x06, 0x01, 0x02, 0x03, 0x04]

theorem frame_reject_trailing_byte :
    unframeTransport (bytes [0x00, 0x10, 0x00, 0x02, 0xaa]) = none

-- boundaries and header truncation
theorem boundary_declared_65533 : declaredForPayload 65533 = 65535
theorem boundary_declared_65534 : declaredForPayload 65534 = 65536
theorem header_65536_truncates : u16BE 65536 = bytes [0x00, 0x00]
theorem boundary_fits_65533 (m : WireMessage) (h : m.payload.size = 65533) :
    m.fits
theorem boundary_not_fits_65534 (m : WireMessage) (h : m.payload.size = 65534) :
    ¬ m.fits

-- rust-lightning differential targets
theorem diff_bigsize_decode_65535 :
    Wire.decode (bytes [0xfd, 0xff, 0xff]) = some (65535, 3)
theorem diff_tlv_unknown_even_2_decode :
    decodeTLV (bytes [0x02, 0x04, 0xff, 0xff, 0xff, 0xff]) =
      some (TLVStream.mk [⟨2, bytes [0xff, 0xff, 0xff, 0xff]⟩])
theorem diff_tlv_unknown_even_2_admission :
    decodeAdmissible (bytes [0x02, 0x04, 0xff, 0xff, 0xff, 0xff]) = true
theorem diff_wire_max_length : declaredForPayload 65533 = 65535
```

`diff_tlv_unknown_even_2_admission` states the model's **actual** decision for
the declared namespace gap; it is not a conformance claim.

### Axiom audit

`#print axioms` over all 65 theorems (scratch file under `/tmp/opencode`, not in
the tree):

| Axioms | Declarations |
|---|---:|
| none | 22 |
| `propext` | 17 |
| `propext`, `Quot.sound` | 21 |
| `propext`, `Classical.choice`, `Quot.sound` | 5 |

No `sorryAx`, no user axiom, no `native_decide`/`unsafe`/`implemented_by`.

### Forbidden-construct scan

```sh
grep -RInE '\bsorry\b|\baxiom\b|\badmit\b|native_decide|@\[implemented_by\]|\bunsafe\b' \
  tests/conformance scripts/check-conformance.py LnLean/Proofs/ConformanceDiffTargets.lean
```

Result: no matches (grep RC 1).

---

## 7. Scope caveats

1. **Not a live differential run.**  The rust-lightning fixtures are committed
   JSON transcribed from the pinned unit tests/code.  Running `cargo test` is
   optional and outside the offline checker; the fixture file records the
   commit, source lines, and SHA-256 hashes so drift is detectable.
2. **No Noise layer.**  The length header is modelled as plaintext, exactly as
   in the model's abstract frame.  BOLT 8 encrypts it and adds MACs/tags; those
   are outside this lane.
3. **Production decoder gap retained.**  `LnLean/Wire/Message.lean` has no BOLT 8
   transport encoder/decoder.  The `Transport` namespace is a conformance
   reference only; `Wire.unframe` still reads payload-only frames.
4. **TLV namespace gap retained.**  The model accepts unknown even types; the
   rust-lightning fixture records `UnknownRequiredFeature` as a declared
   `not-modelled` gap.  Known-type value minimality remains unmodelled too.
5. **Finite set.**  61 legacy vectors + 16 framing cases + 9 boundaries + 33
   differential fixtures is a smoke/conformance set, not an exhaustive proof over
   all byte strings.  The universal results remain in the model modules.
6. **Message bodies and dispatch** are not modelled; only the envelope and a
   type-16 example are framed.

---

## 8. Integration steps (for the parent)

1. **Root import.**  Add to `LnLean.lean` (shared file, not edited here):

   ```lean
   import LnLean.Proofs.ConformanceDiffTargets
   ```

   The module builds on its own and imports root-imported modules only.
2. **CI is already wired.**  `.github/workflows/ci.yml:57` runs
   `python3 scripts/check-conformance.py`, so the new framing/differential
   checks and mutation controls run with no workflow change.  The script is
   stdlib-only and offline.
3. **Optional production promotion.**  If BOLT 8 framing should become part of
   the production model, move `Transport.transportLength`/`transportFrame`/
   `unframeTransport` from the conformance module into `LnLean/Wire/Message.lean`
   (a forbidden file for this lane) and keep the same theorem names.  Until
   then the exact gap is stated in §2.
4. **Shared docs are stale.**  `README.md`, `docs/FINAL-STATUS.md`, and
   `docs/WAVE-STATUS.md` still say "61 BigSize/TLV vectors"; update them with
   the new `framing`/`differential` counts when recording the gate.  This lane
   did not edit shared docs.
5. **Catalog.**  No `Obligations.lean`/`Traceability.lean` row is needed:
   `CONF-01`/`CONF-02` are conformance deliverables, not catalog theorem rows.
   Closing text can name `LnLean.Proofs.ConformanceDiffTargets` (65 theorems),
   `tests/conformance/vectors.json` (`framing`), and
   `tests/conformance/rust-lightning/fixtures.json`.

---

## 9. Summary

| Question | Answer |
|---|---|
| Payload-only vs transport length reconciled? | Yes: `Transport.transportLength = 2 + payload.size`; `Wire.frame` documented as payload-only |
| Framing vectors? | 16 cases (6 valid, 10 malformed/truncated) + 9 boundary lengths |
| Pinned rust-lightning fixtures? | 26 BigSize + 3 TLV + 4 wire, commit `fe49009`, offline runner |
| Lean framing theorems? | 65 total; `decide` for concrete vectors, proved length lemmas for boundaries |
| Existing 61-vector suite green? | Yes, unchanged |
| Checker mutation controls? | 7/7 detected on every default run |
| Build / checker RC? | 0 / 0 |
| Forbidden constructs? | none; axioms limited to `propext`, `Quot.sound`, `Classical.choice` |
| Full implementation test? | **No.** Finite vector/differential conformance only |
