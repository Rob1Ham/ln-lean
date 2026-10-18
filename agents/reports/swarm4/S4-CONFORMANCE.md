# S4-CONFORMANCE — BOLT 1 BigSize/TLV conformance vectors

**Lane:** `S4-CONFORMANCE`
**Issue:** `CONF-01` (P2, open)
**Branch / base:** `repair/integrated` @ `47189fe`
**Toolchain:** `leanprover/lean4:v4.35.0`
**Files created:**

| File | Purpose |
|---|---|
| `tests/conformance/vectors.json` | machine-readable BigSize and TLV vectors |
| `tests/conformance/README.md` | fixture format, run command, and scope caveat |
| `scripts/check-conformance.py` | dependency-free validator + Lean cross-check |
| `LnLean/Proofs/ConformanceTargets.lean` | 86 `decide` theorems for the same vectors |
| `agents/reports/swarm4/S4-CONFORMANCE.md` | this report |

**Status: complete.** Module build RC 0 (11 jobs). Checker RC 0. No `sorry`,
`axiom`, `admit`, `native_decide`, `unsafe`, or `@[implemented_by]`. The only
axioms in the audit are `propext` and `Quot.sound`. No forbidden file was
edited; no Git write command was run.

**Scope statement (important).** This is **vector conformance, not a full
implementation test**. It checks a finite set of encoded byte strings and the
model's accept/reject decisions. It does not check IO, allocation bounds,
message-specific TLV value semantics, namespace/known-type policy, or
byte-for-byte equivalence with a running rust-lightning node.

---

## 1. Result

| Item | Result |
|---|---|
| BigSize encode vectors | 12 canonical values, including every BOLT 1 Appendix A encoding vector |
| BigSize decode vectors | 25: 12 accepted (value + consumed) and 13 rejected |
| TLV vectors | 24: 7 sorted/empty, 4 duplicate/out-of-order, 6 out-of-domain/non-canonical, 5 truncated, 2 declared model gaps |
| BOLT Appendix A anchors independently re-checked | 26 published entries |
| Python checker | `RESULT: PASS`, exit 0 |
| Lean vector theorems | 86, all closed by `decide` |
| Lean build | `✔ [11/11] Built LnLean.Proofs.ConformanceTargets (851ms)`; `Build completed successfully (11 jobs)` |
| Axiom audit | 26 theorems: no axioms; 35: `propext`; 25: `propext`, `Quot.sound` |
| Forbidden-construct scan | no matches |

The pre-existing `LnLean/Proofs/PhaseC3/ConformanceVectors.lean` already checks
six BigSize values and one abstract message frame with `simp`/`rfl`. This lane
does **not** edit it; the new module is additive and covers all BigSize
boundaries, rejects, TLV, and the machine-readable/checker layer that the
earlier module lacks.

---

## 2. Exact BigSize vectors

### 2.1 Canonical encodings

All rows are `Wire.encode value = bytes (...)`, proved by `decide`. `len` is
the expected encoded length.

| Id | Value | Bytes | Len | Lean theorem |
|---|---:|---|---:|---|
| `bigsize_encode_zero` | 0 | `00` | 1 | `bigsize_encode_zero` |
| `bigsize_encode_one` | 1 | `01` | 1 | `bigsize_encode_one` |
| `bigsize_encode_one_byte_high` | 252 | `fc` | 1 | `bigsize_encode_one_byte_high` |
| `bigsize_encode_two_byte_low` | 253 | `fd00fd` | 3 | `bigsize_encode_two_byte_low` |
| `bigsize_encode_two_byte_254` | 254 | `fd00fe` | 3 | `bigsize_encode_two_byte_254` |
| `bigsize_encode_two_byte_255` | 255 | `fd00ff` | 3 | `bigsize_encode_two_byte_255` |
| `bigsize_encode_two_byte_256` | 256 | `fd0100` | 3 | `bigsize_encode_two_byte_256` |
| `bigsize_encode_two_byte_high` | 65535 | `fdffff` | 3 | `bigsize_encode_two_byte_high` |
| `bigsize_encode_four_byte_low` | 65536 | `fe00010000` | 5 | `bigsize_encode_four_byte_low` |
| `bigsize_encode_four_byte_high` | 4294967295 | `feffffffff` | 5 | `bigsize_encode_four_byte_high` |
| `bigsize_encode_eight_byte_low` | 4294967296 | `ff0000000100000000` | 9 | `bigsize_encode_eight_byte_low` |
| `bigsize_encode_eight_byte_high` | 18446744073709551615 | `ffffffffffffffffff` | 9 | `bigsize_encode_eight_byte_high` |

The summary theorem

```lean
theorem bigsize_encode_lengths :
    (Wire.encode 0).size = 1 ∧ (Wire.encode 252).size = 1 ∧
    (Wire.encode 253).size = 3 ∧ (Wire.encode 65535).size = 3 ∧
    (Wire.encode 65536).size = 5 ∧ (Wire.encode 4294967295).size = 5 ∧
    (Wire.encode 4294967296).size = 9 ∧
    (Wire.encode 18446744073709551615).size = 9
```

pins the 1/3/5/9 length classes.

### 2.2 Accepted decodes

All rows are `Wire.decode (bytes ...) = some (value, consumed)`.

| Id | Bytes | Expected | Lean theorem |
|---|---|---|---|
| `bigsize_decode_zero` | `00` | `(0, 1)` | `bigsize_decode_zero` |
| `bigsize_decode_one_byte_high` | `fc` | `(252, 1)` | `bigsize_decode_one_byte_high` |
| `bigsize_decode_two_byte_low` | `fd00fd` | `(253, 3)` | `bigsize_decode_two_byte_low` |
| `bigsize_decode_two_byte_254` | `fd00fe` | `(254, 3)` | `bigsize_decode_two_byte_254` |
| `bigsize_decode_two_byte_255` | `fd00ff` | `(255, 3)` | `bigsize_decode_two_byte_255` |
| `bigsize_decode_two_byte_256` | `fd0100` | `(256, 3)` | `bigsize_decode_two_byte_256` |
| `bigsize_decode_two_byte_high` | `fdffff` | `(65535, 3)` | `bigsize_decode_two_byte_high` |
| `bigsize_decode_four_byte_low` | `fe00010000` | `(65536, 5)` | `bigsize_decode_four_byte_low` |
| `bigsize_decode_four_byte_high` | `feffffffff` | `(4294967295, 5)` | `bigsize_decode_four_byte_high` |
| `bigsize_decode_eight_byte_low` | `ff0000000100000000` | `(4294967296, 9)` | `bigsize_decode_eight_byte_low` |
| `bigsize_decode_eight_byte_high` | `ffffffffffffffffff` | `(18446744073709551615, 9)` | `bigsize_decode_eight_byte_high` |
| `bigsize_decode_trailing_ignored` | `00ff` | `(0, 1)` | `bigsize_decode_trailing_ignored` |

`bigsize_decode_trailing_ignored` documents streaming behaviour: trailing bytes
are left for the next field rather than rejected.

### 2.3 Rejected decodes

All rows are `Wire.decode (bytes ...) = none`.

| Id | Bytes | Reason | Source | Lean theorem |
|---|---|---|---|---|
| `bigsize_reject_noncanonical_two` | `fd00fc` | non-canonical | BOLT App. A | `bigsize_reject_noncanonical_two` |
| `bigsize_reject_noncanonical_two_zero` | `fd0000` | non-canonical | 0xfd class of zero | `bigsize_reject_noncanonical_two_zero` |
| `bigsize_reject_noncanonical_four` | `fe0000ffff` | non-canonical | BOLT App. A | `bigsize_reject_noncanonical_four` |
| `bigsize_reject_noncanonical_four_zero` | `fe00000000` | non-canonical | 0xfe class of zero | `bigsize_reject_noncanonical_four_zero` |
| `bigsize_reject_noncanonical_eight` | `ff00000000ffffffff` | non-canonical | BOLT App. A | `bigsize_reject_noncanonical_eight` |
| `bigsize_reject_noncanonical_eight_zero` | `ff0000000000000000` | non-canonical | 0xff class of zero | `bigsize_reject_noncanonical_eight_zero` |
| `bigsize_reject_short_two` | `fd00` | short read | BOLT App. A | `bigsize_reject_short_two` |
| `bigsize_reject_short_four` | `feffff` | short read | BOLT App. A | `bigsize_reject_short_four` |
| `bigsize_reject_short_eight` | `ffffffffff` | short read | BOLT App. A | `bigsize_reject_short_eight` |
| `bigsize_reject_empty` | `` | empty input | BOLT App. A | `bigsize_reject_empty` |
| `bigsize_reject_tag_only_two` | `fd` | short read | BOLT App. A | `bigsize_reject_tag_only_two` |
| `bigsize_reject_tag_only_four` | `fe` | short read | BOLT App. A | `bigsize_reject_tag_only_four` |
| `bigsize_reject_tag_only_eight` | `ff` | short read | BOLT App. A | `bigsize_reject_tag_only_eight` |

---

## 3. Exact TLV vectors

Columns: `parser` is the structural `decodeTLV` decision, `admission` is
`decodeAdmissible` (parser + strict ordering), `spec` is the BOLT 1 decision
under the relevant namespace, and `scope` is how the model relates to it.
Every case has a `_decode` and `_admission` theorem by prefixing its id.

| Id | Bytes | Parser | Admission | Spec | Scope |
|---|---|---|---|---|---|
| `tlv_empty` | `` | accept `[]` | accept | accept | enforced |
| `tlv_sorted_single` | `01012a` | accept `[(1,2a)]` | accept | accept | enforced |
| `tlv_sorted_two` | `01012a02022b2c` | accept `[(1,2a),(2,2b2c)]` | accept | accept | enforced |
| `tlv_sorted_three_254` | `01000201fffd00fe020226` | accept `[(1,),(2,ff),(254,0226)]` | accept | accept | enforced |
| `tlv_type_65535` | `fdffff00` | accept `[(65535,)]` | accept | accept | enforced |
| `tlv_type_65536` | `fe0001000000` | accept `[(65536,)]` | accept | accept | enforced |
| `tlv_max_type` | `ffffffffffffffffff00` | accept `[(2^64-1,)]` | accept | accept | enforced |
| `tlv_duplicate_type` | `01012a01012b` | accept `[(1,2a),(1,2b)]` | **reject** | reject | enforced-by-admission |
| `tlv_out_of_order` | `02012a01012b` | accept `[(2,2a),(1,2b)]` | **reject** | reject | enforced-by-admission |
| `tlv_bolt_unsorted_1f_0f` | `1f000f012a` | accept `[(31,),(15,2a)]` | **reject** | reject | enforced-by-admission |
| `tlv_bolt_duplicate_1f` | `1f001f012a` | accept `[(31,),(31,2a)]` | **reject** | reject | enforced-by-admission |
| `tlv_out_of_domain_type_2_64` | `ff000000000000000000` | reject (non-canonical) | reject | reject | enforced |
| `tlv_out_of_domain_length_2_64` | `01ff0000000000000000` | reject (non-canonical) | reject | reject | enforced |
| `tlv_noncanonical_type_fe_zero` | `fe0000000000` | reject (non-canonical) | reject | reject | enforced |
| `tlv_noncanonical_length_fd_zero` | `01fd0000` | reject (non-canonical) | reject | reject | enforced |
| `tlv_truncated_type_fd` | `fd` | reject (short read) | reject | reject | enforced |
| `tlv_truncated_type_fd01` | `fd01` | reject (short read) | reject | reject | enforced |
| `tlv_missing_length` | `fd0101` | reject (missing length) | reject | reject | enforced |
| `tlv_truncated_length_fd` | `0ffd` | reject (short read) | reject | reject | enforced |
| `tlv_truncated_length_fd26` | `0ffd26` | reject (short read) | reject | reject | enforced |
| `tlv_truncated_value` | `0ffd2602` | reject (value truncated) | reject | reject | enforced |
| `tlv_value_truncated_small` | `01032a2b` | reject (value truncated) | reject | reject | enforced |
| `tlv_unknown_even_12` | `1200` | accept `[(18,)]` | accept | **reject** | **not-modelled:namespace-policy** |
| `tlv_known_type_nonminimal_value` | `01020001` | accept `[(1,0001)]` | accept | **reject** | **not-modelled:known-type-length** |

The 22 `enforced` / `enforced-by-admission` rows match BOLT 1. The two
`not-modelled` rows are deliberate gap witnesses:

1. **Unknown even type.** BOLT 1 Appendix B requires `12 00` to be rejected as
   an unknown even namespace type. `LnLean/Wire/TLV.lean` has no namespace
   parameter and no even/odd policy, so it accepts. The theorem
   `tlv_unknown_even_12_decode/_admission` records the model's actual decision
   and does **not** claim conformance.
2. **Known-type value minimality.** BOLT 1 Appendix B requires `01 02 0001` to
   be rejected because the `n1` `tlv1` `tu64 amount_msat` is not minimally
   encoded. The model treats TLV values as opaque bytes, so it accepts. Same
   treatment: actual-decision theorems only.

### 3.1 TLV parser/admission split

The four duplicate/out-of-order rows are the exact evidence that
`decodeTLV` is structural-only. For example:

```lean
theorem tlv_duplicate_type_decode :
    decodeTLV (bytes [0x01, 0x01, 0x2a, 0x01, 0x01, 0x2b]) =
      some (TLVStream.mk [⟨1, bytes [0x2a]⟩, ⟨1, bytes [0x2b]⟩])

theorem tlv_duplicate_type_admission :
    decodeAdmissible (bytes [0x01, 0x01, 0x2a, 0x01, 0x01, 0x2b]) = false
```

`decodeAdmissible` comes from the pre-existing
`LnLean/Proofs/Wire/TLVTargets.lean`; this lane does not redefine or edit it.
No theorem `decodeTLV b = some s → s.WellFormed` exists, and these vectors are
the concrete refutation. BOLT ordering is enforced by the admission layer, not
by the parser.

---

## 4. Python checker

`scripts/check-conformance.py` is dependency-free (stdlib only). It:

1. Re-implements BigSize `encode`/`decode` independently and recomputes every
   vector.
2. Re-implements the structural TLV parser and a separate strict-ordering
   admission check, mirroring the Lean split.
3. Re-checks the 26 BOLT 1 Appendix A published entries from a hard-coded
   table copied from `refs/bolts/01-messaging.md`, so a typo in the JSON is
   caught even if the reference implementation and JSON drifted together.
4. Cross-checks every vector's `lean` theorem name against
   `LnLean/Proofs/ConformanceTargets.lean`, including that the first `bytes
   [...]` literal is the input and that encode/`some (v, n)`/`none`/admission
   conclusions appear in the statement.

Exact output:

```text
$ python3 scripts/check-conformance.py
vectors: 12 BigSize encode, 25 BigSize decode, 24 TLV
checks:  61 vector expectations validated
BOLT 1 Appendix A anchors: 26 published entries matched
TLV: 22 enforced cases, 2 declared not-modelled gaps
Lean sync: 85 theorem references checked in LnLean/Proofs/ConformanceTargets.lean
RESULT: PASS (vector conformance, not a full implementation test)
```

`--verbose` prints every vector; `--no-lean` skips the Lean cross-check;
`--vectors PATH` and `--lean-file PATH` override the defaults. The script is
cwd-independent and exits 0/1/2 for pass/mismatch/usage-IO.

**Negative controls (checker is not vacuous).** Three temporary mutations under
`/tmp/opencode` were each detected with exit 1:

```text
FAIL: bigsize.encode[bigsize_encode_two_byte_low]: bytes fd00fe != reference fd00fd
FAIL: tlv.cases[tlv_duplicate_type]: admission accept != reject
FAIL: lean[tlv_no_such_theorem]: theorem not declared
```

---

## 5. Lean module and build

`LnLean/Proofs/ConformanceTargets.lean` imports
`LnLean.Wire.BigSize`, `LnLean.Wire.TLV`, and
`LnLean.Proofs.Wire.TLVTargets`, and defines a single helper:

```lean
def bytes (l : List UInt8) : ByteArray := l.toByteArray
```

All 86 theorems are in namespace `LnLean.Proofs.Conformance` and are closed by
kernel `decide` (no `native_decide`). Signature families:

```lean
-- BigSize canonical encoding
theorem bigsize_encode_zero : Wire.encode 0 = bytes [0x00]
theorem bigsize_encode_eight_byte_high :
    Wire.encode 18446744073709551615 =
      bytes [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]

-- BigSize accepted decode
theorem bigsize_decode_two_byte_low :
    Wire.decode (bytes [0xfd, 0x00, 0xfd]) = some (253, 3)

-- BigSize rejected decode
theorem bigsize_reject_noncanonical_two :
    Wire.decode (bytes [0xfd, 0x00, 0xfc]) = none

-- TLV structural parse
theorem tlv_sorted_two_decode :
    decodeTLV (bytes [0x01, 0x01, 0x2a, 0x02, 0x02, 0x2b, 0x2c]) =
      some (TLVStream.mk [⟨1, bytes [0x2a]⟩, ⟨2, bytes [0x2b, 0x2c]⟩])

-- TLV ordering admission
theorem tlv_sorted_two_admission :
    decodeAdmissible (bytes [0x01, 0x01, 0x2a, 0x02, 0x02, 0x2b, 0x2c]) = true

-- Declared gap, actual model decision only
theorem tlv_unknown_even_12_admission :
    decodeAdmissible (bytes [0x12, 0x00]) = true
```

The complete id → theorem mapping is in `vectors.json` (`lean` fields for
BigSize, `lean.decode` / `lean.admission` for TLV). The count is 86 = 13
BigSize encode/summary + 25 BigSize decode + 48 TLV (24 × 2).

Build command (exact lane command):

```sh
cd /home/ubuntu/ln-lean-repair
export PATH=/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Proofs.ConformanceTargets
```

Result:

```text
✔ [11/11] Built LnLean.Proofs.ConformanceTargets (851ms)
Build completed successfully (11 jobs).
build-rc=0
```

A repeat invocation is cached and still reports `Build completed successfully
(11 jobs)` with RC 0.

---

## 6. Axiom audit

A scratch file under `/tmp/opencode/s4conf` (not in the tree) imported the
module and ran `#print axioms` for all 86 theorem names. Exact distribution:

| Axioms | Declarations |
|---|---:|
| none | 26 |
| `propext` | 35 |
| `propext`, `Quot.sound` | 25 |

No declaration depends on `Classical.choice`, `sorryAx`, or any user axiom.
`decide` here is kernel reduction over closed concrete values, not
`native_decide`.

---

## 7. Forbidden-construct scan

Command:

```sh
grep -RInE '\bsorry\b|\baxiom\b|\badmit\b|native_decide|@\[implemented_by\]|\bunsafe\b' \
  tests/conformance scripts/check-conformance.py LnLean/Proofs/ConformanceTargets.lean
```

Result: `no matches`.

`git status` shows only the three new owned paths from this lane
(`LnLean/Proofs/ConformanceTargets.lean`, `scripts/check-conformance.py`,
`tests/conformance/`); the modified model files and other new modules in the
worktree belong to other lanes and were not touched.

---

## 8. Gaps and limits (exact, not hidden)

1. **`decodeTLV` does not enforce ordering.** The vectors `tlv_duplicate_type`,
   `tlv_out_of_order`, `tlv_bolt_unsorted_1f_0f`, and
   `tlv_bolt_duplicate_1f` prove the parser accepts them and
   `decodeAdmissible` rejects them. A production decoder must call the
   admission layer; `LnLean/Wire/TLV.lean` is read-only for this lane.
2. **No namespace/known-type layer.** `tlv_unknown_even_12` and
   `tlv_known_type_nonminimal_value` are accepted by the model but rejected by
   BOLT 1. The JSON marks them `not-modelled`; the Lean theorems state only the
   model's actual decision.
3. **No differential execution against rust-lightning.** The anchors and the
   BOLT text are the source of truth; no Rust fixture runner was built. A
   future lane would need pinned rust-lightning binaries or generated fixtures.
4. **Out-of-domain values are not representable.** `Wire.encode` truncates at
   `2^64`; the type/length `2^64` vectors exercise the resulting non-minimal
   `0xff || 0^8` bytes and both layers reject them. Larger values cannot be
   encoded by this model at all.
5. **Message framing is intentionally not in this vector set.** The model's
   `frame` is `type || length || payload` with `length = payload.size`, whereas
   the BOLT 1 transport length covers type plus payload. `PhaseC3.ConformanceVectors`
   already records the model's abstract frame; treating it as BOLT wire
   conformance would overclaim.
6. **Finite vector set.** 61 expectations is a conformance smoke test, not an
   exhaustive proof over all byte strings. The generic theorems in
   `LnLean/Wire/BigSize.lean` and `LnLean/Proofs/Wire/TLVProps.lean` remain the
   universal results.

---

## 9. Integration steps (for the parent)

1. **Root import.** Add one line to `LnLean.lean` (shared file, not edited here):

   ```lean
   import LnLean.Proofs.ConformanceTargets
   ```

   Place it after `import LnLean.Proofs.Common` (or regenerate the root with
   `scripts/regen-root.sh`, also shared). The module already builds on its own
   and imports only root-imported modules.
2. **Run the checker in the gate.** Add `python3 scripts/check-conformance.py`
   to the repository check script or CI job owned by `S4-VENDOR-CI`/release.
   It is stdlib-only and takes well under a second.
3. **No catalog edit required.** `CONF-01` is not a theorem-catalog row; the
   deliverables are the fixture set, the runner, and the new proof module.
   Closing text can name `tests/conformance/vectors.json`,
   `scripts/check-conformance.py`, and
   `LnLean.Proofs.ConformanceTargets` (86 `decide` theorems). No
   `Obligations.lean` or `Traceability.lean` change is needed.
4. **Optional CI artifact.** The checker's PASS line is stable and can be
   captured as a release-gate log; it explicitly prints that this is vector
   conformance, not an implementation test.

---

## 10. Summary

| Question | Answer |
|---|---|
| Concrete BigSize vectors? | 12 canonical encode, 25 decode (12 accept + 13 reject), all BOLT Appendix A entries included |
| Concrete TLV vectors? | 24 cases: empty, sorted, duplicate, out-of-order, out-of-domain, non-canonical, truncated |
| Runnable checker? | `python3 scripts/check-conformance.py`, RC 0, catches mutated vectors and missing Lean theorems |
| Lean vector theorems? | 86, all `decide`, module build RC 0 (11 jobs) |
| Axioms? | none / `propext` / `propext`+`Quot.sound` only |
| Forbidden constructs? | none |
| Is this a full implementation test? | **No.** Finite vector conformance only |
| Remaining model gaps? | parser does not enforce ordering (admission does); no namespace/known-type policy; no rust-lightning differential run; abstract message framing deliberately excluded |
