# S10-PR-COVERAGE-WITNESS — the `commitment_signed` coverage witness (`PR-02`)

**Lane:** `S10-PR-COVERAGE-WITNESS`
**Issue:** `PR-02` (P1, open/mitigated: the legacy `CommitmentSigned` wire record lacks per-HTLC coverage data)
**Base:** `repair/integrated` at launch HEAD `7988c93` (base `9158592`)
**Status:** complete — scoped build green, no `sorry`/forbidden tokens, no shared files edited, no commit/push

## 1. Objective

Attack `PR-02` by characterizing the missing `commitment_signed` coverage data
as a **witness**, rather than assuming it is derivable from the legacy wire
record. The lane was asked to:

1. define a `CoverageWitness` carrying the missing per-HTLC data and a
   constructive `decodeCoverage : CommitmentSigned → CoverageWitness → …`
   whose canonical instance returns the full record's exact coverage;
2. prove a legacy-only impossibility with the decoder types;
3. prove witness necessity (a dropped amount/payment-hash row admits two
   records with the same reduced witness and different coverage, or an exact
   minimality statement), keeping the counterexample concrete;
4. state the exact residual wire/decoder boundary without claiming the legacy
   wire is sufficient.

## 2. Artifacts

| Path | Kind | Notes |
|---|---|---|
| `LnLean/Proofs/Channel/CoverageWitnessTargets.lean` | new Lean module (owned) | Additive; imports `PreimageCoverageTargets`; 409 lines. |
| `agents/reports/swarm10/S10-PR-COVERAGE-WITNESS.md` | new report (owned) | This file. |

No edits were made to `PreimageCoverageTargets.lean`, `Messages.lean`,
`Commitment.lean`, `LnLean.lean`, `Obligations.lean`, `Traceability.lean`,
`AxiomAudit.lean`, docs, the catalog, or any other lane's files.

## 3. Design

### 3.1 The witness

```lean
structure CoverageWitness where
  entries : List SignedHtlcEntry
```

`SignedHtlcEntry` is the existing additive record in
`LnLean/Protocol/Messages.lean`: per-HTLC id, millisatoshi amount, payment
hash, direction, lifecycle state, `cltv_expiry`, signed-data digest, and the
DER HTLC signature. The legacy `CommitmentSigned` carries only the bare
signature list; the witness is the per-entry association of those signatures
with the identification and amount data.

The witness deliberately does **not** carry the commitment number, fee, or
commitment digest: those are not needed to recover the HTLC output list, and
`no_legacy_only_coverage_decoder` is about the output list. They remain part of
`CommitmentSignedFull` for the fee/state theorems in `ProtocolWireTargets`.

Canonical extraction:

```lean
def witnessOfFull (f : CommitmentSignedFull) : CoverageWitness :=
  { entries := f.htlcEntries }

def coverageOfFull (f : CommitmentSignedFull) : List CommitmentHTLCOutput :=
  f.htlcEntries.map SignedHtlcEntry.toCommitmentHtlcOutput
```

`SignedHtlcEntry.toCommitmentHtlcOutput` applies BOLT 3's millisatoshi →
satoshi floor, so `coverageOfFull f` is exactly the list of commitment outputs
the signed entries describe.

### 3.2 Wire compatibility

```lean
def wireCompatible (m : CommitmentSigned) (w : CoverageWitness) : Prop :=
  m.htlcSignatures = w.entries.map (fun e => e.signature)
```

This is the only part of a witness that the legacy record can cross-check. The
identification and amount rows have no wire image. `wireCompatible_length`
derives one signature per row; `wireCompatible_toCommitmentSigned` proves the
canonical witness is compatible by `rfl`.

### 3.3 The decoder

```lean
def decodeCoverage (m : CommitmentSigned) (w : CoverageWitness) :
    Option (List CommitmentHTLCOutput) :=
  if m.htlcSignatures.length = w.entries.length then
    some (w.entries.map SignedHtlcEntry.toCommitmentHtlcOutput)
  else
    none
```

The wire contributes the only consistency condition it can: the HTLC-signature
count must equal the number of witness rows. The per-HTLC data comes from the
witness. The decoder is **not** a message-authentication check; witness
provenance is an explicit out-of-band input (see §6).

## 4. Exact claims and theorem names

All names are in namespace
`LnLean.Proofs.Channel.CoverageWitnessTargets`.

### 4.1 Canonical correctness

* `witnessOfFull_entries` — `(witnessOfFull f).entries = f.htlcEntries`. No
  axioms.
* `wireCompatible_toCommitmentSigned` — the canonical witness is
  wire-compatible with `f.toCommitmentSigned`. No axioms.
* `wireCompatible_length` — compatibility implies
  `m.htlcSignatures.length = w.entries.length`.
* **`decodeCoverage_canonical`** —

  ```text
  decodeCoverage f.toCommitmentSigned (witnessOfFull f)
    = some (coverageOfFull f)
  ```

  for every `f : CommitmentSignedFull`. This is the requested constructive
  decoder correctness theorem: the legacy projection plus the canonical witness
  returns exactly the full record's coverage.
* `decodeCoverage_eq_some_iff` — exact characterization: the decoder succeeds
  iff the wire signature count matches the witness row count, and the result is
  the witness's output projection.
* `decodeCoverage_sound` — a successful decode implies
  `m.htlcSignatures.length = outs.length` (one wire signature per decoded
  output).
* `decodeCoverage_of_wireCompatible` — full wire compatibility (not just
  length) always decodes.
* `decodeCoverage_covers` — if the decoder returns `outs` and
  `c.htlcs = outs`, then `CoversHtlcOutputs m c` holds. This connects the new
  witness decoder to the existing `PR-02` coverage predicate.

### 4.2 Legacy-only impossibility

Concrete counterexample:

```lean
def witnessEntryA : SignedHtlcEntry :=
  { htlcId := 1, amount := ⟨1000⟩, paymentHash := ⟨ByteArray.empty⟩,
    direction := .local, htlcState := .offered, cltvExpiry := 100,
    signedDataDigest := ByteArray.empty, signature := witnessSig }

def witnessEntryB : SignedHtlcEntry :=
  { witnessEntryA with amount := ⟨2000⟩ }
```

`witnessFullA` / `witnessFullB` wrap the two entries with the same channel id
and commitment signature.

* `witness_full_same_projection` — the two full records have **equal**
  `CommitmentSigned` projections (same channel id, commitment signature, and
  `[witnessSig]` HTLC-signature list).
* `witness_full_coverage_ne` — their covered output lists differ: 1 sat versus
  2 sat after the BOLT 3 floor. Proved by kernel computation.
* **`no_legacy_only_coverage_decoder`** —

  ```text
  ¬ ∃ decode : CommitmentSigned → List CommitmentHTLCOutput,
      ∀ f : CommitmentSignedFull,
        decode f.toCommitmentSigned = coverageOfFull f
  ```

  This restates the existing negative with the decoder types and a concrete
  full-record pair.
* **`no_legacy_only_witness_selector`** — even a function that chooses an
  arbitrary witness from the wire cannot decode every full record correctly:
  both full records project to the same wire, so the selector returns the same
  witness for both.

### 4.3 Witness necessity and exact minimality

* `reducedIdent` / `CoverageWitness.withoutAmount` — erase the millisatoshi
  amount from every witness row, keeping id, payment hash, direction, state,
  and expiry.
* `witness_full_same_reduced_witness` — the amount-erased witnesses of
  `witnessFullA` and `witnessFullB` are equal.
* **`amount_is_necessary`** — there exist two witnesses with the same
  amount-erased data such that `decodeCoverage` against the *same* legacy wire
  returns different output lists. The amount row is load-bearing, not
  decoration.
* **`toCommitmentHtlcOutput_eq_iff`** — exact minimal determining tuple:

  ```text
  e₁.toCommitmentHtlcOutput = e₂.toCommitmentHtlcOutput
    ↔ e₁.direction = e₂.direction
      ∧ e₁.amount.toSatFloor = e₂.amount.toSatFloor
      ∧ e₁.cltvExpiry = e₂.cltvExpiry
      ∧ e₁.htlcState = e₂.htlcState
  ```

  `htlcId`, `paymentHash`, `signedDataDigest`, and `signature` do not enter the
  output projection. This is the precise minimality statement: the coverage
  list is determined by exactly those four row components, while the legacy
  wire carries none of them.
* `toCommitmentHtlcOutput_update_htlcId`,
  `toCommitmentHtlcOutput_update_paymentHash`,
  `toCommitmentHtlcOutput_update_digest`,
  `toCommitmentHtlcOutput_update_signature` — the four ignored fields,
  individually, by `rfl`.

The payment hash is still required to identify an HTLC for state
reconciliation; it is simply not part of the *output-list* projection. The
amount is the required row because it changes the satoshi value of the covered
output.

### 4.4 Residual boundary

* **`wire_admits_distinct_coverage_witnesses`** —

  ```text
  ∃ (m : CommitmentSigned) (w₁ w₂ : CoverageWitness),
    wireCompatible m w₁ ∧ wireCompatible m w₂ ∧
      decodeCoverage m w₁ ≠ decodeCoverage m w₂
  ```

  Both witnesses are compatible with the same legacy message, yet decode
  differently. The wire cannot select the witness.
* `wire_cannot_select_witness` — no wire-compatible selector of a witness can
  be correct for every full record.
* `coverage_witness_summary` — bundles the four headline results: canonical
  decoding, legacy-only impossibility, same-wire distinct witnesses, and amount
  necessity.

## 5. Validation

### 5.1 Scoped build

Command:

```sh
export PATH=/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Proofs.Channel.CoverageWitnessTargets
```

Result:

```text
Build completed successfully (52 jobs).
```

No errors and no warnings from
`LnLean/Proofs/Channel/CoverageWitnessTargets.lean`.

### 5.2 Axiom audit

Every public theorem was audited with `#print axioms` in a temporary file
outside the repository. Allowed set: `propext`, `Quot.sound`,
`Classical.choice`.

| Theorem | Axioms |
|---|---|
| `witnessOfFull_entries` | none |
| `wireCompatible_toCommitmentSigned` | none |
| `wireCompatible_length` | `propext` |
| `decodeCoverage_canonical` | `propext` |
| `decodeCoverage_eq_some_iff` | `propext` |
| `decodeCoverage_sound` | `propext` |
| `decodeCoverage_of_wireCompatible` | `propext` |
| `decodeCoverage_covers` | `propext`, `Quot.sound` |
| `witness_full_same_projection` | `propext` |
| `witness_full_coverage_ne` | `propext` |
| `no_legacy_only_coverage_decoder` | `propext` |
| `no_legacy_only_witness_selector` | `propext` |
| `witness_full_same_reduced_witness` | `propext` |
| `amount_is_necessary` | `propext` |
| `toCommitmentHtlcOutput_eq_iff` | `propext` |
| `toCommitmentHtlcOutput_update_htlcId` | none |
| `toCommitmentHtlcOutput_update_paymentHash` | none |
| `toCommitmentHtlcOutput_update_digest` | none |
| `toCommitmentHtlcOutput_update_signature` | none |
| `wire_admits_distinct_coverage_witnesses` | `propext` |
| `wire_cannot_select_witness` | `propext` |
| `coverage_witness_summary` | `propext` |

No theorem uses `Classical.choice`. No axiom outside the allowed set appears.

### 5.3 Forbidden-token scan

```sh
grep -nE '\b(sorry|admit|axiom|native_decide|unsafe)\b|implemented_by' \
  LnLean/Proofs/Channel/CoverageWitnessTargets.lean
```

Result: no matches. The module uses Lean 4 core only (no mathlib), with
`set_option autoImplicit false` and the exact namespace
`LnLean.Proofs.Channel.CoverageWitnessTargets`.

## 6. Precise remaining wire/decoder boundary

The formal result is a **decoder with an explicit witness input**, not a
wire-only decoder:

* `decodeCoverage m w` is correct on the canonical witness
  (`decodeCoverage_canonical`), and it is sound for the wire count
  (`decodeCoverage_sound`).
* No `CommitmentSigned → List CommitmentHTLCOutput` function is correct for
  every full record (`no_legacy_only_coverage_decoder`).
* The same wire message admits two wire-compatible witnesses that decode
  differently (`wire_admits_distinct_coverage_witnesses`), so the witness
  cannot be selected from the legacy bytes.
* The amount row is necessary (`amount_is_necessary`); the exact output
  projection is determined by direction, floored amount, expiry, and lifecycle
  state (`toCommitmentHtlcOutput_eq_iff`).

Therefore a production decoder needs one of:

1. an **out-of-band / full-record source** for the per-HTLC rows (the local
   signer's `CommitmentSignedFull`, the commitment state, or a persisted
   message log), plus an explicit provenance/authentication assumption for that
   source; or
2. a **protocol change** that carries the witness (per-HTLC identification,
   amount, expiry, and state) on the wire or in a negotiated extension.

The legacy `commitment_signed` wire is **not** sufficient, and this lane does
not claim that it is. The theorem `decodeCoverage_covers` transfers only after
the witness is supplied; it is not a wire-only coverage theorem. Likewise the
decoder does not authenticate the witness: a malicious or stale witness can
still decode to a plausible but wrong output list, so a production integration
must pair this decoder with the existing signature/digest and state-reachability
checks.

What remains open for `PR-02` is exactly the production provenance of the
witness (or the protocol encoding change), not an algebraic gap in the
coverage projection. The finite negative results and the concrete
counterexamples are retained; no unconditional wire-only coverage claim is
made.

## 7. Catalog integration recommendation (`LN-PR-004`)

`LN-PR-004` currently lists the `PreimageCoverageTargets` results and ends with
"wire-only legacy coverage remains negative." Recommend the parent:

1. Add the module to the root import set (`LnLean.lean`):

   ```lean
   import LnLean.Proofs.Channel.CoverageWitnessTargets
   ```

2. Append these exact targets to the `LN-PR-004` `leanTarget` string in
   `LnLean/Proofs/Obligations.lean` (and in the generated
   `agents/status/obligations.json` row):

   ```text
   LnLean.Proofs.Channel.CoverageWitnessTargets.decodeCoverage_canonical;
   LnLean.Proofs.Channel.CoverageWitnessTargets.decodeCoverage_covers;
   LnLean.Proofs.Channel.CoverageWitnessTargets.no_legacy_only_coverage_decoder;
   LnLean.Proofs.Channel.CoverageWitnessTargets.no_legacy_only_witness_selector;
   LnLean.Proofs.Channel.CoverageWitnessTargets.wire_admits_distinct_coverage_witnesses;
   LnLean.Proofs.Channel.CoverageWitnessTargets.amount_is_necessary;
   LnLean.Proofs.Channel.CoverageWitnessTargets.toCommitmentHtlcOutput_eq_iff;
   LnLean.Proofs.Channel.CoverageWitnessTargets.coverage_witness_summary
   ```

3. Append to the `LN-PR-004` claim (after the existing final sentence):

   > The missing legacy-wire data is characterized as a per-HTLC coverage
   > witness: the canonical witness decodes exactly to the full record's
   > coverage, no legacy-only decoder or wire-compatible witness selector is
   > correct for all full records, the amount row is necessary, and the same
   > legacy message admits distinct decoding witnesses. A production decoder
   > therefore requires an out-of-band/full-record source or a protocol change;
   > the legacy wire alone is not sufficient.

4. Add the public theorems to `AxiomAudit.lean` (same list; all are
   `propext`/`Quot.sound`/none, so the allowed-axiom gate stays green).

5. Add the module to the `LN-PR-004` traceability target list in
   `LnLean/Proofs/Traceability.lean`.

This is a recommendation only: the lane did not edit the catalog,
`Obligations.lean`, `Traceability.lean`, `AxiomAudit.lean`, docs, or
`LnLean.lean`, and did not commit or push.
