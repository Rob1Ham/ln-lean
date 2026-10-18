# W01-WIRE — LN-CR-006 declared length law

**Lane:** W01-WIRE (proof lane)
**Repository:** `/home/ubuntu/ln-lean-repair`
**Branch:** `repair/integrated`
**Files changed by this lane:** `LnLean/Wire/Message.lean` (additive only, +84 lines), `agents/reports/W01-WIRE.md`
**Verdict:** **PROMOTION-READY** — exact target exists, is sorry-free, and is proved about the real `unframe` decoder.

## Catalog row

From `LnLean/Proofs/Obligations.lean:148-153`:

| field | value |
|---|---|
| id | `LN-CR-006` |
| domain | `.cryptoWire` |
| claim | A Lightning message frame's declared length matches the payload actually consumed. |
| leanTarget | `LnLean.Wire.Message.decode_length` |
| status | `.statementOnly` (unchanged by this lane) |
| boltdoc | BOLT 1 §Lightning Message Format |
| rlAnchor | `lightning/src/ln/peer_handler.rs:331` |

`LnLean/Proofs/Traceability.lean:224` already maps the target to module
`LnLean.Wire.Message`; it did not need editing and was not touched.

## Exact theorem statement

Produced by `#check` against the built module (scratch file
`/tmp/opencode/btc-lean/W01WireCheck.lean`):

```
LnLean.Wire.Message.decode_length (b : ByteArray) (m : LnLean.Wire.WireMessage)
    (h : LnLean.Wire.unframe b = some m) :
  LnLean.Wire.Message.declaredLength? b = some m.payload.size ∧
    List.drop 4 (LnLean.Wire.bytesToList b) = LnLean.Wire.bytesToList m.payload ∧
    b.size = 4 + m.payload.size
```

Source form (`LnLean/Wire/Message.lean:305`):

```lean
theorem decode_length (b : ByteArray) (m : WireMessage) (h : unframe b = some m) :
    declaredLength? b = some m.payload.size ∧
      (bytesToList b).drop 4 = bytesToList m.payload ∧
      b.size = 4 + m.payload.size
```

This covers all three required facts, under the single hypothesis of a
successful decode:

1. the two-byte big-endian declared length equals `m.payload.size`;
2. the consumed payload is exactly the bytes after the four-byte
   `type || length` header (`drop 4`);
3. the whole frame is `4 + m.payload.size` bytes, i.e. no input byte is
   unaccounted for.

The statement is not a tautology or a weakened restatement: it is a
conjunction of three non-trivial facts about the existing `unframe`, and it
is consistent with the decoder's rejection behaviour (a frame whose declared
length disagrees with the bytes present yields `none`, already proved in
`Proofs/WaveD/D10` as `waveD_d10_decode_wrong_length_none`).

## Additions (all inside `namespace LnLean.Wire`, new `namespace Message`)

- `LnLean.Wire.Message.declaredLength? : ByteArray → Option Nat` (line 260) —
  reads the two length bytes (`bytesToList b` positions 3–4) as `u16Nat`;
  `none` for inputs shorter than the four-byte header. Self-contained in the
  model file, so the model does not depend on any proof module.
- `LnLean.Wire.Message.unframeList_eq_some_iff` (line 268) — decoder
  inversion: `unframeList l = some m` iff `l` splits as
  `a :: b :: c :: d :: rest` with `rest.length = u16Nat c d` and
  `m = ⟨u16FromBytes a b, rest.toByteArray⟩`.
- `LnLean.Wire.Message.decode_length` (line 305) — the target theorem.
- `namespace Message` opens at line 255 and closes at line 328; nothing
  existing was deleted, renamed, or edited.

No new Lean file was created in the repository; the only scratch file is
`/tmp/opencode/btc-lean/W01WireCheck.lean`, outside the repo. No root-import
or aggregator changes were made.

## Proof approach

The proof is self-contained and reuses the wave-A framing lemmas only
(`bytesToList_append`, `bytesToList_u16BE`, `bytesToList_toByteArray`,
`bytesToList_length`, `List.size_toByteArray`, `u16Nat`), plus `omega`. The
model file does **not** import `LnLean.Proofs.WaveD.D10`; D10's proof ideas
were reproduced locally, which is why an inversion lemma is added in the
`Message` namespace instead of being imported.

1. Unfold `unframe` to `unframeList (bytesToList b)`.
2. Invert the decode with `unframeList_eq_some_iff`, obtaining header bytes
   `a bty` (type), `c d` (length), tail `rest`, the equality
   `bytesToList b = a :: bty :: c :: d :: rest`, the decoder side condition
   `rest.length = u16Nat c d`, and `m = ⟨u16FromBytes a bty, rest.toByteArray⟩`.
3. Substitute `m`, then discharge the three conjuncts:
   - `declaredLength? b` reduces by `hb` to `some (u16Nat c d)`; rewriting with
     `List.size_toByteArray` and `hlen` gives `some rest.toByteArray.size`;
   - `(bytesToList b).drop 4 = rest` by `hb` and `simp`, and
     `rest = bytesToList rest.toByteArray` by `bytesToList_toByteArray`;
   - `b.size = (bytesToList b).length` by `bytesToList_length`, then
     `hb` + `List.length_cons` gives `rest.length + 4`, and
     `List.size_toByteArray` + `omega` close `4 + rest.toByteArray.size`.

No `sorry`, `axiom`, `admit`, `native_decide`, `unsafe`, or
`@[implemented_by]` was introduced. `#print axioms` reports only
`propext` and `Quot.sound`:

```
'LnLean.Wire.Message.decode_length' depends on axioms: [propext, Quot.sound]
'LnLean.Wire.Message.unframeList_eq_some_iff' depends on axioms: [propext]
```

## Build evidence

All Lean runs used one process at a time under
`flock -w 1800 /tmp/opencode/btc-lean/build.lock`, with
`LEAN_NUM_THREADS=1`. No OOM, SIGKILL, or memory pressure was observed; the
module build took 734 ms (`[7/7]`) because dependencies were already built.

| # | Command | RC | Output |
|---|---|---|---|
| 1 | `lake env lean LnLean/Wire/Message.lean` | **0** | no diagnostics |
| 2 | `lake build LnLean.Wire.Message` | **0** | `✔ [7/7] Built LnLean.Wire.Message (734ms)`, `Build completed successfully (7 jobs).` |
| 3 | `lake env lean /tmp/opencode/btc-lean/W01WireCheck.lean` | **0** | exact `#check` signature above; axioms `[propext, Quot.sound]` |
| 4 | `python3 scripts/check-catalog.py --audit --allow-planned` | **0** | row resolves; `candidates=9`, `unresolved=0`, `proved_failures=0` |

Catalog checker detail for the row:

```
LN-CR-006   statementOnly  theorem    no     LnLean.Wire.Message   LnLean.Wire.Message.decode_length
Promotion candidates (statementOnly, exact target, theorem/lemma, no sorry)
LN-CR-006: theorem LnLean.Wire.Message.decode_length @ LnLean.Wire.Message:305
```

**Toolchain note (deviation, not a proof failure).** The prescribed
`lake build -j1 LnLean.Wire.Message` cannot be parsed by this Lake
(`Lake version 5.0.0-src+eb6cafb`): it returns RC 1 with
`error: unknown short option '-j'` before doing any work, and this Lake
exposes no `--jobs` flag in `lake build --help`. The equivalent build was run
as `LEAN_NUM_THREADS=1 flock … lake build LnLean.Wire.Message` (one Lean
process, RC 0, command 2 above). This is a CLI-version mismatch only.

## Promotion verdict

**Promotion-ready.** Recommended parent action (outside this lane's
permissions): set `LN-CR-006.status` from `.statementOnly` to `.proved` in
`LnLean/Proofs/Obligations.lean` and regenerate the docs/obligation status
artifacts. The target name is exact, the declaration is a theorem, it is
sorry-free, it resolves in module `LnLean.Wire.Message` as Traceability
already claims, and its statement is the catalog claim (declared length =
payload actually consumed, payload = post-header tail, frame size = 4 +
payload).
