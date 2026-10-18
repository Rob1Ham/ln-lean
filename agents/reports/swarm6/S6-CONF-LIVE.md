# S6-CONF-LIVE — promoted transport framing and pinned fixture verification

**Lane:** `S6-CONF-LIVE`
**Issues:** `CONF-03`, `CONF-02`
**Branch / base:** `repair/integrated` @ `201a0a0` (wave 6 launch)
**Toolchain:** `leanprover/lean4:v4.35.0`
**Status: complete (narrowed).** The BOLT 8 transport model is promoted into
`LnLean/Wire/Message.lean` under `LnLean.Wire.Transport` with the wave-5
theorem names; the payload-only production decoder is unchanged and its
rejection of transport frames is now a generic theorem. The 61 base vectors,
16 framing cases, 9 boundaries, and 33 pinned rust-lightning fixtures remain
green. A deterministic pinned-source fixture re-derivation/verification path was
added. **No live `cargo test` result is claimed:** a live attempt failed on the
incomplete offline cache before compiling.

---

## 1. Files

| Path | Role |
|---|---|
| `LnLean/Wire/Message.lean` | promoted `LnLean.Wire.Transport` model (`transportLength`, `transportFrame`, `unframeTransport`, length/round-trip/declared-length laws, payload-decoder boundary) |
| `LnLean/Proofs/ConformanceDiffTargets.lean` | keeps finite framing/differential vectors; imports the promoted model; one delegation for the wave-5 `AxiomAudit` path |
| `tests/conformance/rust-lightning/generate.py` | new deterministic pinned-source fixture re-derivation/verification and isolated optional live cargo runner |
| `tests/conformance/rust-lightning/fixtures.json` | adds `generation` metadata; fixture rows unchanged |
| `tests/conformance/rust-lightning/README.md` | provenance, generation, and honest live-run documentation |
| `tests/conformance/README.md` | promoted-model boundary, new run commands, checker options |
| `tests/conformance/vectors.json` | lane/issue metadata and model-source note updated; vector rows unchanged |
| `scripts/check-conformance.py` | promoted-model existence check, provenance verification, generation metadata check, 9 mutation controls |
| `agents/reports/swarm6/S6-CONF-LIVE.md` | this report |

No forbidden file was edited. `LnLean.lean`, `Obligations.lean`,
`Traceability.lean`, `AxiomAudit.lean`, `scripts/check-final.py`, other lanes'
files, shared docs, and vendor sources were not touched. No Git write was made.
Other modified/untracked files in `git status` belong to parallel wave-6 lanes.

---

## 2. Promotion and the exact decoder boundary

### 2.1 Two length conventions, two names

| Convention | Definition | Length field |
|---|---|---|
| model payload-only frame | `LnLean.Wire.frame` / `Wire.unframe` | `payload.size` |
| BOLT 8 transport frame | `LnLean.Wire.Transport.transportFrame` / `unframeTransport` | `2 + payload.size` |

The BOLT 8 model was moved verbatim (same theorem names) from
`LnLean.Proofs.Conformance.Diff.Transport` into `LnLean.Wire.Transport`:

```lean
def transportLength (m : WireMessage) : Nat := 2 + m.payload.size
def lengthHeader (m : WireMessage) : ByteArray := u16BE (transportLength m)
def transportFrame (m : WireMessage) : ByteArray :=
  u16BE m.type.toNat ++ lengthHeader m ++ m.payload

def unframeTransportList : List UInt8 → Option WireMessage
def unframeTransport (b : ByteArray) : Option WireMessage
def declaredTransportLength? (b : ByteArray) : Option Nat
```

`LnLean.Wire.unframe` is deliberately **not** changed. The boundary is now a
generic theorem, not a comment:

```lean
theorem Transport.unframe_transportFrame_eq_none (m : WireMessage) :
    unframe (Transport.transportFrame m) = none
```

It proves that the payload-only decoder rejects the transport frame for *every*
message, including the truncated-header cases at payload `65534`/`65535`. The
concrete wave-5 witness `payload_decoder_rejects_transport_frame` now derives
from it instead of `decide`.

### 2.2 Exact promoted signatures

```lean
LnLean.Wire.Transport.transportLength (m : WireMessage) : Nat
LnLean.Wire.Transport.transportFrame (m : WireMessage) : ByteArray
LnLean.Wire.Transport.unframeTransport (b : ByteArray) : Option WireMessage
LnLean.Wire.Transport.declaredTransportLength? (b : ByteArray) : Option Nat

theorem Transport.transportLength_eq_messageSize (m : WireMessage) :
    Transport.transportLength m = m.messageSize

theorem Transport.transportFrame_header_eq (m : WireMessage) :
    Transport.transportFrame m =
      u16BE m.type.toNat ++ u16BE (m.payload.size + 2) ++ m.payload

theorem Transport.transportFrame_size (m : WireMessage) :
    (Transport.transportFrame m).size = 4 + m.payload.size

theorem Transport.transportFrame_size_eq (m : WireMessage) :
    (Transport.transportFrame m).size = m.messageSize + 2

theorem Transport.fits_iff_transportLength (m : WireMessage) :
    m.fits ↔ Transport.transportLength m ≤ MAX_MESSAGE_SIZE

theorem Transport.fits_iff_payload (m : WireMessage) :
    m.fits ↔ m.payload.size ≤ 65533

theorem Transport.unframeTransportList_eq_some_iff (l : List UInt8) (m : WireMessage) :
    Transport.unframeTransportList l = some m ↔
      ∃ a b c d rest, l = a :: b :: c :: d :: rest ∧
        u16Nat c d = rest.length + 2 ∧
        m = ⟨u16FromBytes a b, rest.toByteArray⟩

theorem Transport.unframeTransport_transportFrame (m : WireMessage)
    (h : m.payload.size < 65534) :
    Transport.unframeTransport (Transport.transportFrame m) = some m

theorem Transport.unframeTransport_transportFrame_of_fits (m : WireMessage)
    (h : m.fits) :
    Transport.unframeTransport (Transport.transportFrame m) = some m

theorem Transport.decode_transport_length (b : ByteArray) (m : WireMessage)
    (h : Transport.unframeTransport b = some m) :
    Transport.declaredTransportLength? b = some m.messageSize ∧
      (bytesToList b).drop 4 = bytesToList m.payload ∧
      b.size = 4 + m.payload.size

theorem Transport.bytesToList_u16BE_mod (n : Nat) :
    bytesToList (u16BE n) =
      [((n / 256) % 256).toUInt8, (n % 256).toUInt8]

theorem Transport.u16Nat_u16BE_mod (n : Nat) :
    u16Nat ((n / 256) % 256).toUInt8 (n % 256).toUInt8 = n % 65536

theorem Transport.unframe_transportFrame_eq_none (m : WireMessage) :
    unframe (Transport.transportFrame m) = none
```

The conformance module keeps the same short names visible via `open Transport`
and keeps all concrete vector theorem names (`frame_init_four`,
`frame_reject_trailing_byte`, `boundary_declared_65533`,
`diff_wire_max_length`, …).

### 2.3 `AxiomAudit` compatibility

`LnLean/Proofs/PhaseC3/AxiomAudit.lean` references the wave-5 fully-qualified
path `LnLean.Proofs.Conformance.Diff.Transport.transportFrame_size`. That path
is preserved by a one-line delegation at the end of
`ConformanceDiffTargets.lean`; the real proof is
`LnLean.Wire.Transport.transportFrame_size`. `#print axioms` on the delegated
path succeeds (see §4). The parent may replace the audit reference with
`LnLean.Wire.Transport.transportFrame_size` and delete the delegation; that is
an exact two-line integration patch outside this lane's ownership.

---

## 3. Build and checker results

### 3.1 Module build

```sh
cd /home/ubuntu/ln-lean-repair
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Wire.Message LnLean.Proofs.ConformanceDiffTargets
```

Result: `Build completed successfully (11 jobs).` RC 0. No full `lake build`
was run.

### 3.2 Checker

`python3 scripts/check-conformance.py` → RC 0. Exact output:

```text
vectors: 12 BigSize encode, 25 BigSize decode, 24 TLV
checks:  61 vector expectations validated
BOLT 1 Appendix A anchors: 26 published entries matched
TLV: 22 enforced cases, 2 declared not-modelled gaps
framing: 16 cases (6 accept, 10 reject), 9 length boundaries
differential: 26 rust-lightning BigSize, 3 TLV, 4 wire fixtures (pinned fe49009, offline)
differential TLV: 2 enforced, 1 declared not-modelled gaps
fixture generation: transcribed-from-pinned-source (live cargo test: no)
provenance: 4 pinned rust-lightning source files verified (HEAD verified)
Lean sync: 146 theorem references checked in LnLean/Proofs/ConformanceTargets.lean, LnLean/Proofs/ConformanceDiffTargets.lean
promoted transport: 13/13 theorems, 6/6 definitions checked in LnLean/Wire/Message.lean
mutation controls: 9/9 detected
RESULT: PASS (vector/differential conformance, not a full implementation test)
```

Count changes relative to the wave-5 gate:

| Item | Before | After |
|---|---:|---:|
| base vector expectations | 61 | 61 (unchanged) |
| framing cases | 16 (6/10) | 16 (6/10) (unchanged) |
| framing boundaries | 9 | 9 (unchanged) |
| rust-lightning fixtures | 26 + 3 + 4 = 33 | 33 (unchanged) |
| Lean vector theorem references | 146 | 146 (unchanged) |
| promoted transport checks | 0 | 13 theorems + 6 definitions |
| pinned provenance files | 0 | 4 |
| mutation controls | 7 | 9 |

The two new mutation controls are (a) removing a promoted transport theorem and
(b) claiming a live run without a transcript. The existing seven are unchanged.
`--no-lean` intentionally reports 7/7 because the two Lean-dependent controls
are skipped with the Lean checks. The checker also asserts at the source level
that `unframeList` still compares the declared field with `rest.length` and
`unframeTransportList` compares it with `rest.length + 2`, so a future edit
cannot silently swap the two decoders.

### 3.3 Deterministic fixture path

`python3 tests/conformance/rust-lightning/generate.py --check` → RC 0:

```text
fixtures: 26 BigSize, 3 TLV, 4 wire match the pinned source
provenance: 4 source files verified at fe49009
live cargo test: not run (use --live; no live result is claimed)
```

The script verifies the four recorded SHA-256 hashes and the checkout HEAD
(`fe4900930c6bd5786ec4203274d7cf312776a5a6`), re-extracts the literal arrays
from `bigsize_encoding_decoding` and `retired_tlvs_skipped_on_read`, derives the
wire length rows, and compares every derived field. A deliberately mutated copy
(`wire[0].transport_length + 1`) fails RC 1 with
`fixtures.wire[0].transport_length: 2 != 3`. `--write` on a copy of the
committed file is byte-for-byte identical (no-op), so the path is deterministic.

`--live` copies the pinned checkout to a disposable temp directory, runs the
two pinned tests with `cargo test --offline`, and returns 4 on any failure
without modifying `fixtures.json` or claiming success. It was attempted and
failed before compiling:

```text
error: no matching package named `backtrace` found
location searched: crates.io index
required by package `lightning v0.3.0+git (.../rust-lightning/lightning)`
...
LIVE RUN FAILED: cargo returned 101; the offline cache is incomplete or a
pinned test failed. No live result is claimed.
```

Script RC was 4. The checkout here is a shared `refs/` symlink; the disposable
copy avoided mutating it. This reproduces the wave-5 `backtrace` gap and is why
the offline transcriptions are retained.

---

## 4. Axiom audit

Scratch file under `/tmp/opencode` (not in the tree), importing
`LnLean.Proofs.ConformanceDiffTargets`, with `#print axioms` over the 13
promoted theorems and 9 representative Diff theorems:

| Axioms | Declarations |
|---|---:|
| none | 2 |
| `propext` | 4 |
| `propext`, `Quot.sound` | 13 |
| `propext`, `Classical.choice`, `Quot.sound` | 3 |

No `sorryAx`, no user axiom, no `native_decide`/`unsafe`/`implemented_by`.
Every reported axiom is in the allowed set.

### Forbidden-construct scan

```sh
grep -RInE '\bsorry\b|\baxiom\b|\badmit\b|native_decide|@\[implemented_by\]|\bunsafe\b' \
  LnLean/Wire/Message.lean LnLean/Proofs/ConformanceDiffTargets.lean \
  tests/conformance scripts/check-conformance.py
```

Result: no matches (grep RC 1).

---

## 5. Scope caveats

1. **No live differential run.** The fixtures remain committed transcriptions,
   now deterministically re-derived from the pinned source literals. They are
   not output from a running rust-lightning node. The `generation` block says
   `live_cargo_test: false`; a future lane may only flip it after a real
   `--live` success with a transcript hash.
2. **Transport is still plaintext and one-frame.** BOLT 8 Noise encryption,
   the 16-byte MACs, AEAD associated data, multiple frames per buffer, message
   bodies, and dispatch are outside the model. `unframeTransport` accepts
   exactly one complete frame and rejects trailing bytes.
3. **The new boundary theorem is a model statement.** It proves that the
   model's payload-only `Wire.unframe` rejects the model's transport frame;
   it does not assert anything about rust-lightning's decoder.
4. **`unframeTransport` length policy.** Its declared field must equal
   `payload.size + 2`; because the field is 16 bits this also rejects a payload
   above `65533` (no matching declared value exists) and any declared value
   below `2`. It does not separately re-check `≤ 65535`; the equality and the
   16-bit field imply it.
5. **TLV namespace gap retained.** The model still accepts unknown even types;
   rust-lightning rejects them with `UnknownRequiredFeature`. That is a
   declared `not-modelled:namespace-policy` gap, not a conformance claim.
6. **Finite vectors.** 61 base + 16 framing + 9 boundaries + 33 differential
   fixtures is a smoke/conformance set, not an exhaustive proof over all byte
   strings. The universal model results remain the Lean theorems.
7. **No full build/gate run.** Per lane rules only the two modules and the
   checker were run. Catalog/anchor regeneration and `check-final.py` belong to
   the parent.

---

## 6. Integration steps (for the parent)

1. **No root-import change is needed.** `LnLean.lean` already imports
   `LnLean.Wire.Message` (line 191) and `LnLean.Proofs.ConformanceDiffTargets`
   (line 53). The promoted model is reached through both.
2. **Optional `AxiomAudit` cleanup.** Replace
   `LnLean.Proofs.Conformance.Diff.Transport.transportFrame_size` with
   `LnLean.Wire.Transport.transportFrame_size` in
   `LnLean/Proofs/PhaseC3/AxiomAudit.lean:227`, then delete the delegation
   theorem at the end of `ConformanceDiffTargets.lean`. The delegation is
   already present so the current audit path still resolves.
3. **Regenerate generated artifacts.** `docs/OBLIGATIONS-GENERATED.md` currently
   records the transport definitions at `ConformanceDiffTargets.lean:77-151`;
   after this lane they live in `LnLean/Wire/Message.lean`. Run
   `collect-obligations.py`/`collect-anchors.py` (parent-owned) and update the
   anchor/declaration indexes. The theorem names are unchanged.
4. **Shared status docs.** Update `README.md`, `docs/FINAL-STATUS.md`, and
   `docs/WAVE-STATUS.md` to say: transport model promoted to
   `LnLean.Wire.Transport`; checker now also reports provenance/promoted-model
   checks and 9 mutation controls; fixtures remain offline transcriptions.
5. **Issue status.** `CONF-03` is addressed for the model/path (promotion plus
   deterministic verification); the live-regeneration half remains open.
   `CONF-02` remains open because no live rust-lightning differential run
   succeeded. Do not close either as a live-conformance claim.
6. **CI (optional but recommended).** Add a step after
   `python3 scripts/check-conformance.py`:
   `python3 tests/conformance/rust-lightning/generate.py --check`.
   It is stdlib-only and offline; it verifies provenance only when
   `refs/rust-lightning` is present.
7. **Live cargo.** When a complete offline cache is available, run
   `python3 tests/conformance/rust-lightning/generate.py --live` in a disposable
   checkout/copy. Only after both pinned tests pass should
   `fixtures.json.generation.live_cargo_test` be set true with a recorded
   transcript hash.

---

## 7. Blockers / narrowed results

| Blocker | Effect |
|---|---|
| No successful live `cargo test` in this environment (`no matching package named backtrace`, script RC 4) | Fixtures stay offline transcriptions (now source-derived). `CONF-02` is not closed as live differential conformance. |
| `AxiomAudit.lean` is outside lane ownership | Old fully-qualified audit path kept alive by a one-line delegation; parent should switch to the promoted name. |
| Generated declaration indexes are parent-owned | `docs/OBLIGATIONS-GENERATED.md` is stale until the parent regenerates it. |
| Full gate is parent-owned | No full build, catalog, anchor, or `check-final.py` claim from this lane. |

---

## 8. Summary

| Question | Answer |
|---|---|
| Transport model promoted into `Wire/Message.lean`? | Yes, `LnLean.Wire.Transport` with the wave-5 theorem names |
| Is payload-only `Wire.unframe` weakened? | No; unchanged, and a generic theorem proves it rejects every transport frame |
| New transport decoder clearly named? | Yes, `Transport.unframeTransport` (and `transportFrame`) |
| 61 base vectors green? | Yes, unchanged |
| 16 framing cases + 9 boundaries green? | Yes, unchanged |
| 33 rust-lightning fixtures green? | Yes, unchanged |
| Deterministic fixture generation/verification? | Yes, `generate.py --check`; `--write` is a no-op on the committed file |
| Live cargo run claimed? | **No.** `--live` was attempted and failed on the offline cache; it never claims success on failure |
| Module build / checker RC? | 0 / 0 |
| Forbidden constructs? | none; axioms only `propext`, `Quot.sound`, `Classical.choice` |

**Final line for the parent:** S6-CONF-LIVE promotes the BOLT 8 transport frame
and decoder into `LnLean.Wire.Transport` (13 theorems, 6 definitions) while
keeping `Wire.unframe` payload-only and proving the rejection boundary; all
61 + 16 + 33 existing expectations stay green, the checker adds provenance and
promoted-model checks (9/9 mutation controls), and the pinned-source fixture path
is reproducible offline. The only unresolved half is a real live `cargo test`
run: the attempt failed on the offline `backtrace` cache gap, so no live result
is claimed.
