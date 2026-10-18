# S8-CONF-ENCODINGS — wider BOLT encodings in the finite conformance suite (`CONF-01`)

- Lane: `S8-CONF-ENCODINGS`
- Issue: `CONF-01` (with `CONF-02` live/offline status preserved)
- Branch: `repair/integrated`
- Base: `3953c8c` (wave 8 launch)
- Date: 2026-10-18

## 1. Verdict

**Applied and green.**  The finite conformance suite now has six deterministic
BOLT 2 payload/field vectors:

- `open_channel` type 32 — 319-byte base and 343-byte
  `upfront_shutdown_script` TLV;
- `accept_channel` type 33 — 270-byte base and 306-byte TLV;
- `commitment_signed` type 132 — 226 bytes with two 64-byte HTLC signatures;
- `update_add_htlc` type 128 — 1450 bytes with a 1366-byte onion.

Each row has a complete ordered field table (offset, width/kind, value/hex), the
concatenated payload, the BOLT 8 transport length/header, and the
type-plus-header frame prefix.  `scripts/check-conformance.py` independently
rebuilds each payload from the fields, validates the TLV envelope, recomputes
the lengths/header, cross-checks the named Lean `decide` theorems, and detects
four new mutation classes.  The Lean module builds and the checker passes:

```text
Build completed successfully (11 jobs).                  (RC 0)
messages: 6 BOLT 2 payload/field vectors
          (accept_channel 2, commitment_signed 1, open_channel 2, update_add_htlc 1)
Lean sync: 175 theorem references checked
mutation controls: 13/13 detected
RESULT: PASS (vector/differential conformance, not a full implementation test)
```

This closes the *finite-vector* encoding gap requested by `CONF-01`; it does not
close `CONF-01` as a whole.  The suite still has no live rust-lightning message
serialization row, no signature/sender validation, and no node-level interop
claim (see §9–§10).

Owned files only were edited.  No `LnLean.lean`, `Obligations.lean`,
`Traceability.lean`, `AxiomAudit.lean`, `Wire/Message.lean`, docs, or vendor file
was touched.  No Git write command was run.

## 2. Exact files changed

| File | Change |
|---|---|
| `LnLean/Proofs/ConformanceDiffTargets.lean` | **+518**: local BOLT 2 wire records/helpers, six fixtures, 29 `decide` theorems, `maxRecDepth 10000`. |
| `tests/conformance/vectors.json` | **+730/−4**: new `messages` section, BOLT 2 source metadata, updated lane/issue/scope/model note. Existing BigSize/TLV/framing rows and the live transcript hash are unchanged. |
| `scripts/check-conformance.py` | **+288/−6**: message field/payload/TLV validation, Lean sync, verbose output, counts, four mutation controls. |
| `tests/conformance/README.md` | **+31/−6**: documents the BOLT 2 message section and its non-claims. |
| `agents/reports/swarm8/S8-CONF-ENCODINGS.md` | This report. |

`LnLean.lean` already imports `LnLean.Proofs.ConformanceDiffTargets` (line 64),
so no root-import change is needed.  No owned downstream proof file changed.

The concurrent `S8-L1-OPENCHANNEL-WIRE` lane added
`LnLean.Protocol.OpenChannelWire` / `Msg.openChannel` to `Messages.lean`.  This
lane did **not** import or depend on that constructor: the conformance record is
`LnLean.Proofs.Conformance.Diff.OpenChannelWire`, a separate local structure.
The two names live in different namespaces and do not collide.

## 3. Message vectors

| Vector id | Message | Type | Payload | Transport | Header | Frame prefix |
|---|---|---:|---:|---:|---|---|
| `msg_open_channel_base` | `open_channel` | 32 | 319 | 321 | `0141` | `00200141` |
| `msg_open_channel_upfront_shutdown` | `open_channel` | 32 | 343 | 345 | `0159` | `00200159` |
| `msg_accept_channel_base` | `accept_channel` | 33 | 270 | 272 | `0110` | `00210110` |
| `msg_accept_channel_upfront_shutdown` | `accept_channel` | 33 | 306 | 308 | `0134` | `00210134` |
| `msg_commitment_signed_two_htlcs` | `commitment_signed` | 132 | 226 | 228 | `00e4` | `008400e4` |
| `msg_update_add_htlc_base` | `update_add_htlc` | 128 | 1450 | 1452 | `05ac` | `008005ac` |

The length derivations are the pinned BOLT 2 field sums:

```text
open_channel base:
  chain_hash 32 + temporary_channel_id 32 + six u64 (48)
  + feerate_per_kw 4 + two u16 (4) + six points (198) + channel_flags 1 = 319
open_channel + type-0 TLV:
  319 + BigSize(type 0)=1 + BigSize(len 22)=1 + 22-byte script = 343
accept_channel base:
  temporary_channel_id 32 + four u64 (32) + minimum_depth 4
  + two u16 (4) + six points (198) = 270
accept_channel + type-0 TLV:
  270 + 1 + 1 + 34-byte script = 306
commitment_signed:
  channel_id 32 + signature 64 + num_htlcs u16 2 + 2*64 HTLC sigs = 226
update_add_htlc:
  channel_id 32 + id 8 + amount_msat 8 + payment_hash 32
  + cltv_expiry 4 + onion_routing_packet 1366 = 1450
```

The field order is taken from the pinned `refs/bolts/02-peer-protocol.md`:
`open_channel` at lines 680–706, `accept_channel` at 907–938,
`update_add_htlc` at 2772–2800, and `commitment_signed` at 3097–3115.  The
`chain_hash` is the BOLT 0 mainnet value used directly (not reversed).  Keys and
signatures are synthetic fixed-width filled points/signatures; they are encoding
fixtures, not valid secp256k1 objects.

The two TLV rows use the model's own `Wire.encode` BigSize encoder for the type
and length prefix.  The `open_channel` script is a 22-byte synthetic P2WPKH-style
value and the `accept_channel` script is a 34-byte synthetic P2WSH-style value,
so both canonical BigSize length branches above 252 are not exercised by these
rows (the BigSize suite already does that separately).

## 4. Lean model and theorems

### 4.1 Local records instead of `Protocol.Messages`

The lane requirement was to avoid depending on the other wave-8 lane's
type-32 `Msg.openChannel`.  `ConformanceDiffTargets.lean` therefore defines four
local records and payload functions:

- `OpenChannelWire.payload`
- `AcceptChannelWire.payload`
- `CommitmentSignedWire.payload`
- `UpdateAddHtlcWire.payload`

They mirror BOLT 2 field order and fixed widths.  `upfrontShutdownScript` is an
`Option ByteArray` encoded as TLV type 0, `commitment_signed` uses
`u16BE htlcSignatures.length` plus folded 64-byte signatures, and
`update_add_htlc` uses a raw 1366-byte onion.

### 4.2 Why `abbrev` and `maxRecDepth`

`decide` initially failed on named `def` fixtures/helpers because the kernel did
not unfold them for the byte comparison.  Converting the fixtures and helpers to
`abbrev` made the finite structures reducible, and `set_option maxRecDepth 10000`
covers the 1450-byte `update_add_htlc` reduction.  `prefix` is a reserved Lean
token, so the point helper parameter is named `pfx`.

### 4.3 Theorems (29)

For each of the first five rows: payload equality, payload length, transport
length, transport header, and frame prefix (5 × 5 = 25).  For
`update_add_htlc`: length, transport, header, and frame prefix (4), because a
1450-byte literal payload-equality statement would be unwieldy and adds no
encoding information beyond the field table plus the recomputed length.  The
JSON row leaves `lean.payload` as `null`; the checker requires a payload theorem
for every other message name and tolerates the omission only for
`update_add_htlc`.

```lean
LnLean.Proofs.Conformance.Diff.msg_open_channel_base_payload
LnLean.Proofs.Conformance.Diff.msg_open_channel_base_length
LnLean.Proofs.Conformance.Diff.msg_open_channel_base_transport
LnLean.Proofs.Conformance.Diff.msg_open_channel_base_header
LnLean.Proofs.Conformance.Diff.msg_open_channel_base_frame_prefix

LnLean.Proofs.Conformance.Diff.msg_open_channel_upfront_shutdown_payload
LnLean.Proofs.Conformance.Diff.msg_open_channel_upfront_shutdown_length
LnLean.Proofs.Conformance.Diff.msg_open_channel_upfront_shutdown_transport
LnLean.Proofs.Conformance.Diff.msg_open_channel_upfront_shutdown_header
LnLean.Proofs.Conformance.Diff.msg_open_channel_upfront_shutdown_frame_prefix

LnLean.Proofs.Conformance.Diff.msg_accept_channel_base_payload
LnLean.Proofs.Conformance.Diff.msg_accept_channel_base_length
LnLean.Proofs.Conformance.Diff.msg_accept_channel_base_transport
LnLean.Proofs.Conformance.Diff.msg_accept_channel_base_header
LnLean.Proofs.Conformance.Diff.msg_accept_channel_base_frame_prefix

LnLean.Proofs.Conformance.Diff.msg_accept_channel_upfront_shutdown_payload
LnLean.Proofs.Conformance.Diff.msg_accept_channel_upfront_shutdown_length
LnLean.Proofs.Conformance.Diff.msg_accept_channel_upfront_shutdown_transport
LnLean.Proofs.Conformance.Diff.msg_accept_channel_upfront_shutdown_header
LnLean.Proofs.Conformance.Diff.msg_accept_channel_upfront_shutdown_frame_prefix

LnLean.Proofs.Conformance.Diff.msg_commitment_signed_two_htlcs_payload
LnLean.Proofs.Conformance.Diff.msg_commitment_signed_two_htlcs_length
LnLean.Proofs.Conformance.Diff.msg_commitment_signed_two_htlcs_transport
LnLean.Proofs.Conformance.Diff.msg_commitment_signed_two_htlcs_header
LnLean.Proofs.Conformance.Diff.msg_commitment_signed_two_htlcs_frame_prefix

LnLean.Proofs.Conformance.Diff.msg_update_add_htlc_base_length
LnLean.Proofs.Conformance.Diff.msg_update_add_htlc_base_transport
LnLean.Proofs.Conformance.Diff.msg_update_add_htlc_base_header
LnLean.Proofs.Conformance.Diff.msg_update_add_htlc_base_frame_prefix
```

All are kernel-checked `decide` theorems over concrete bytes; none is an axiom,
a serializer correctness claim, or a statement about arbitrary messages.

## 5. Build result

Command (shared lock, single thread):

```sh
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Proofs.ConformanceDiffTargets
```

Result:

```text
Build completed successfully (11 jobs).
RC=0
```

This is a module build, not a full-tree build.  The module is already imported
by `LnLean.lean`, so a full build would exercise it too; this lane did not
rebuild the whole tree to avoid competing with other lanes.

## 6. Axiom result

`#print axioms` was run on all 29 new theorems from a temporary file outside the
repository (no source edit).  Command:

```sh
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake env lean /tmp/opencode/s8_conf_axioms.lean
```

Summary:

| Theorem group | Axioms |
|---|---|
| All six `*_length` theorems | none |
| All six `*_transport` theorems | none |
| All five `*_payload` theorems | `[propext, Quot.sound]` |
| All six `*_header` theorems | `[propext, Quot.sound]` |
| All six `*_frame_prefix` theorems | `[propext, Quot.sound]` |

Every result is a subset of `{propext, Quot.sound, Classical.choice}`.  No
`Classical.choice` appears, and no `sorryAx` or new axiom appears.

## 7. Forbidden-construct scan

Scanned the changed source/vector files for `sorry`, `axiom`, `admit`,
`native_decide`, `unsafe`, and `@[implemented_by]`:

| File | Result |
|---|---|
| `LnLean/Proofs/ConformanceDiffTargets.lean` | clean |
| `tests/conformance/vectors.json` | clean |
| `scripts/check-conformance.py` | clean |

No new declaration of any forbidden construct was introduced.  No new Lean
import was added: the module already imports `LnLean.Proofs.Wire.TLVTargets`
and the promoted transport model.

## 8. Checker result and mutation controls

Command:

```sh
python3 scripts/check-conformance.py
```

Output (tail):

```text
vectors: 12 BigSize encode, 25 BigSize decode, 24 TLV
checks:  61 vector expectations validated
BOLT 1 Appendix A anchors: 26 published entries matched
TLV: 22 enforced cases, 2 declared not-modelled gaps
framing: 16 cases (6 accept, 10 reject), 9 length boundaries
messages: 6 BOLT 2 payload/field vectors (accept_channel 2, commitment_signed 1, open_channel 2, update_add_htlc 1)
differential: 26 rust-lightning BigSize, 3 TLV, 4 wire fixtures (pinned fe49009, offline)
differential TLV: 2 enforced, 1 declared not-modelled gaps
fixture generation: live-cargo-test (live cargo test: yes)
live evidence: 26 BigSize + 3 TLV compared against rust-lightning, 4 wire via live LN_MAX_MSG_LEN; transcript sha256 3dd7a98fc102
provenance: 4 pinned rust-lightning source files verified (HEAD verified)
Lean sync: 175 theorem references checked in LnLean/Proofs/ConformanceTargets.lean, LnLean/Proofs/ConformanceDiffTargets.lean
promoted transport: 13/13 theorems, 6/6 definitions checked in LnLean/Wire/Message.lean
mutation controls: 13/13 detected
RESULT: PASS (vector/differential conformance, not a full implementation test)
RC=0
```

The message checker enforces:

- exact field-name order for each message (optional type-0 TLV for
  `open_channel`/`accept_channel`; one `htlc_signature_<i>` per `num_htlcs`);
- exact byte offsets, contiguous field coverage, and the declared length;
- integer value/hex agreement for `u8`/`u16`/`u32`/`u64`;
- 33-byte `02`/`03` points, 64-byte signatures, and the TLV type/length/value
  envelope;
- reassembled payload equals the row payload;
- `transport_length = 2 + payload.size`, its two-byte header, and the
  `type || header` frame prefix;
- the named Lean theorem exists, concludes the right length/transport value,
  and mentions the right payload/header/prefix bytes.

Four new mutation controls (all detected):

1. a field byte changed without updating the payload;
2. a field offset shifted by one;
3. `transport_length` increased by one;
4. a named message Lean theorem removed.

Existing checks, vectors, hashes, live transcript rows, and declared TLV gaps
are unchanged.  `Lean sync` rose from 146 to 175 references because of the 29
new message theorem references.

## 9. Live differential status

No live message row was added in this lane.  The pinned harness **does** run
offline and reproduces the committed transcript hash
`3dd7a98fc102cb7840c52944977b56ae5656acea7846c1a4a3b86e43d6db8fe6`, but its
`live_probe.rs` currently covers BigSize encode/decode, the TLV reader, and
`LN_MAX_MSG_LEN` only.  It does not encode/decode the full BOLT 2 message
structs.

Adding live `open_channel`/`accept_channel` rows would therefore require a new
public-API probe path, a new transcript, a new transcript hash, and updates to
the checker's differential counts.  That was not attempted here: a genuine run
would be required, and a source-only JSON row without a fresh genuine transcript
would weaken the existing `CONF-02` evidence.  The six message rows are
explicitly finite local fixtures, not live rust-lightning comparisons.

This is the main residual `CONF-01` item and is recorded as a gap rather than
claimed as covered.

## 10. Caveats and non-claims

1. **Finite vectors only.**  Six concrete payloads and their lengths are
   checked.  There is no theorem that an arbitrary BOLT 2 message serializes
   correctly, and no decoder round-trip theorem for these records.
2. **No node-level interop claim.**  The suite is not a running-node test and
   does not claim byte-for-byte equivalence with rust-lightning or any other
   implementation.
3. **Synthetic keys/signatures.**  The 33-byte points and 64-byte signatures are
   filled byte patterns.  The vectors check layout and width, not secp256k1
   validity, DER/low-S rules, or signature verification.
4. **No sender identity or handshake routing.**  A payload encoding says nothing
   about who sent it or how `open_channel`/`accept_channel` enter the handshake
   state machine.
5. **TLV coverage is narrow.**  Only type 0 `upfront_shutdown_script` is
   exercised, with 1-byte type and 1-byte length BigSize encodings.  Other
   `open_channel_tlvs` / `accept_channel_tlvs` types, `channel_type`, and
   `commitment_signed_tlvs` are not modelled.
6. **`update_add_htlc` has no payload-equality theorem.**  Its 1450-byte row is
   pinned by the JSON field table plus length/transport/header/prefix theorems.
   This is declared in the row rather than hidden.
7. **The `open_channel` length differs from the other lane's model.**  This
   suite includes `chain_hash` and therefore pins 319/343 payload bytes.  The
   `S8-L1-OPENCHANNEL-WIRE` model uses a 313-byte no-`chain_hash` convention
   (with a documented 313/321 arithmetic discrepancy).  The two are separate
   artifacts; this report does not resolve that model decision.
8. **Mainnet `chain_hash` only.**  Testnet/regtest chain hashes are not
   separately vectored.

## 11. Integration steps (parent only)

1. **No root import is needed.**  `LnLean.lean` already imports
   `LnLean.Proofs.ConformanceDiffTargets`.  The added declarations are picked up
   by the existing import.
2. **Docs.**  Update `docs/OPEN-ISSUES.md` `CONF-01` to record that finite
   `open_channel`/`accept_channel`/`commitment_signed`/`update_add_htlc`
   payload/field rows now exist, with six rows and four mutation classes, and
   that a live message-serialization row remains open.  Keep `CONF-02` as-is;
   its transcript/hash and live evidence were not changed.
3. **Catalog/audit (if desired).**  The 29 new theorem names are listed in §4.3.
   If the parent registers conformance targets in `Obligations.lean` /
   `Traceability.lean` / `AxiomAudit.lean`, the five `*_payload` names are the
   strongest byte-level targets; the length/transport/header/prefix names are
   framing targets.
4. **Do not describe `CONF-01` as closed.**  The finite encoding gap is
   mitigated; live message serialization, signature/sender validation, and
   arbitrary-message correctness are still open.

## 12. Blockers

- **No proof or build blocker.**  The module builds, the checker passes, all 29
  theorems are axiom-clean, and no forbidden construct was introduced.
- **Live message rows are a genuine-run dependency.**  The existing offline
  harness is unchanged and green, but extending it needs a new probe path and a
  new transcript/hash; a fabricated or source-only "live" row would be worse
  than the explicit gap.
- **Root/catalog/docs are parent-owned.**  This lane could not edit
  `LnLean.lean`, `Obligations.lean`, `Traceability.lean`, `AxiomAudit.lean`, or
  `docs/OPEN-ISSUES.md`.  The exact integration text is above.

## 13. `CONF-01` roadmap recommendation

Recommended status: **`open (mitigated; finite encoding coverage integrated)`**.

Suggested next-wave candidates:

1. **`S9-CONF-LIVE-MSGS` — live rust-lightning message serialization.**  Extend
   `live_probe.rs` to construct and `Writeable`-encode pinned `OpenChannel`,
   `AcceptChannel`, `CommitmentSigned`, and `UpdateAddHTLC` values, add the
   resulting rows to `fixtures.json`, regenerate `live-transcript.json`, update
   the transcript hash and differential counts, and only then claim a live
   message-serialization comparison.
2. **`S9-CONF-DECODE` — decode/round-trip vectors.**  Add finite decode cases
   and rejection cases (truncated fixed fields, wrong TLV lengths, invalid point
   prefixes) if the model gains message-level decoders.
3. **`S9-CONF-TLV-MSGS` — message-specific TLVs.**  Cover `channel_type`,
   `commitment_signed_tlvs`, and `update_add_htlc_tlvs` only after the model
   distinguishes known/unknown/required TLV policy.
4. Keep `CONF-02` focused on BigSize/TLV/transport live evidence.  Do not fold
   the new finite message rows into its live count without a real probe run.
