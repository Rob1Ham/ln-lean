# S9-PR-ARBITRARY-PREIMAGE — arbitrary-preimage coverage and the eight field hypotheses (`PR-02`)

**Lane:** `S9-PR-ARBITRARY-PREIMAGE`
**Issue:** `PR-02` (P1, open/mitigated: `CommitmentSigned` wire record lacks data for wire-only coverage)
**Base:** `repair/integrated` at `50e8b5c`
**Status:** complete (scoped build green; no shared files edited; no commit/push)

## 1. Objective

Characterize what a wire-only observer can and cannot recover from the BOLT 3
preimage path, make the eight arbitrary-preimage field hypotheses explicit, and
prove:

1. a conditional coverage theorem under exactly those hypotheses;
2. a mechanized negative when a needed hypothesis is dropped;
3. the display-order txid and 20-byte hash-image / amount boundaries,

without silently identifying an arbitrary `Bip143Preimage` with the
transaction-derived `Bip143Preimage.ofTx`.

## 2. Artifacts

| Path | Kind | Notes |
|---|---|---|
| `LnLean/Proofs/Channel/PreimageCoverageTargets.lean` | new Lean module (owned) | Additive; imports `HtlcPreimageTargets`; no edit to any existing file. |
| `agents/reports/swarm9/S9-PR-ARBITRARY-PREIMAGE.md` | new report (owned) | This file. |

No edits were made to `HtlcPreimageTargets.lean`, `SighashTargets.lean`,
`LnLean.lean`, `Obligations.lean`, `Traceability.lean`, `AxiomAudit.lean`, the
catalog, docs, or Git state.

## 3. Exact claims and theorem names

All theorem names below are in namespace
`LnLean.Proofs.Channel.PreimageCoverageTargets`.

### 3.1 The eight explicit field hypotheses

`structure FieldAgreement (p : Bip143Preimage) (tx : Tx) (nIn : Nat) (amount : Amount) : Prop`
has exactly eight fields, matching the eight hypotheses of
`LnLean.Bitcoin.Sighash.bL_encode_eq_bip143MsgL`:

1. `version_eq`
2. `hashPrevouts_eq`
3. `hashSequence_eq`
4. `outpoint_eq` (32-byte txid and 4-byte index)
5. `sequence_eq`
6. `hashOutputs_eq`
7. `locktime_eq`
8. `amount_eq`

Key theorems:

* `FieldAgreement.outpoint_toPreimage` — repackages the txid/index pair as the
  `OutPoint` equality consumed by the core encoder lemma.
* `ofTx_satisfies_fieldAgreement` — the transaction-derived preimage satisfies
  all eight; the hypotheses are non-vacuous.
* **`fieldAgreement_iff_eq_ofTx_and_amount`** — the exact characterization:

  ```text
  FieldAgreement p tx nIn amount
    ↔ p = Bip143Preimage.ofTx tx nIn p.scriptCode p.sighashType p.amountSat
        ∧ (p.amountSat.toNat : Int) = amount
  ```

  This is the mechanized statement that the eight hypotheses are precisely
  "being the transaction-derived preimage plus the amount context"; no field
  is silently identified.
* `fieldAgreement_iff_eq_ofTx` — self-amount corollary.

### 3.2 Conditional coverage under exactly those hypotheses

* **`FieldAgreement.bytes_eq`** — under `FieldAgreement p tx nIn amount`:

  ```text
  bL p.preimageBytes
    = Bitcoin.SigHash.bip143MsgL tx nIn (bL p.scriptCode) p.sighashType amount
  ```

  The proof goes through `Bip143Preimage.preimageBytes_eq_encode` and the core
  `LnLean.Bitcoin.Sighash.bL_encode_eq_bip143MsgL`; no hypothesis is added or
  hidden.
* `FieldAgreement.digest_eq` — the same equality after the vendored
  double-SHA-256.
* `FieldAgreement.digest_eq_vendor` — for in-range `nIn`, the arbitrary
  preimage's model digest is exactly
  `Bitcoin.SigHash.signatureHashBip143Impl tx nIn (bL p.scriptCode) p.sighashType amount`.
* `PreimageSignatureCovers` / `WireSignatureCovers` — the arbitrary-preimage
  and exact-wire verification predicates.
* **`wireSignatureCovers_of_preimage`** — conditional wire-only coverage
  transfer: a signature valid over the arbitrary preimage's digest is valid
  over the exact wire transaction's digest exactly when the eight fields
  agree.

### 3.3 Dropped-hypothesis counterexamples (mechanized)

The wire in the witnesses uses `SIGHASH_NONE | ANYONECANPAY` (`0x82`) so all
three BIP 143 sub-hashes are the zero vector and the bytes are kernel-decidable
without evaluating SHA-256.

* `counterTx` — concrete one-input transaction with `nLockTime = 5`.
* `counterPreimageLocktime` — agrees on seven fields, records
  `nLockTime = 0`.
* `counterPreimageLocktime_seven` — proves the seven other hypotheses hold.
* `counterPreimageLocktime_not_fieldAgreement` — the dropped hypothesis is
  false on the witness.
* **`counterPreimageLocktime_bytes_ne`** — the conditional byte equality
  fails: `nLockTime` is necessary.
* `counterPreimageAmount` — same construction with `amountSat = 1` while the
  wire amount context is `0`.
* `counterPreimageAmount_not_fieldAgreement` and
  **`counterPreimageAmount_bytes_ne`** — the amount hypothesis is independently
  necessary.

### 3.4 Wire-only record coverage

* `wire_projection_signature_count` —
  `f.toCommitmentSigned.htlcSignatures.length = f.htlcEntries.length`.
* `coverage_pins_only_htlc_count` — under `CoversHtlcOutputs`, the legacy wire
  projection pins the HTLC-output *count* and nothing more.
* **`legacy_projection_not_determine_htlc_coverage`** — two
  `CommitmentSignedFull` records with the same legacy `CommitmentSigned`
  projection (same signature list) but different HTLC output data. Thus even a
  full record is not a coverage decoder if only its legacy projection is
  available.
* `legacy_wire_cannot_determine_coverage` — the existing legacy no-decoder
  negative is preserved verbatim.

### 3.5 `scriptCode` and the 20-byte hash-image boundary

* **`fieldAgreement_scriptCode_free`** — changing only `scriptCode` preserves
  all eight hypotheses. BIP 143 and the vendored encoder treat the spent
  witness script as caller context, so the 20-byte HASH160 images inside a
  BOLT 3 HTLC witness script are not wire-derived by `FieldAgreement`.
* `hash160_image_boundary` — for `HtlcSpend.WellFormed`, the revocation and
  payment HASH160 images are 20 bytes, the HTLC keys 33 bytes, and the
  synthesized success/timeout scriptCodes are 143/136 bytes. These are explicit
  context fields, not preimage fields.

### 3.6 Display-order txid boundary

* `displayTx` / `displayOrderPreimage` — a transaction-derived preimage whose
  outpoint is replaced by its display-order (byte-reversed) form.
* `internalOrderPreimage_fieldAgreement` — the internal-order construction
  satisfies all eight hypotheses.
* **`displayOrderPreimage_not_fieldAgreement`** — the display-order outpoint
  violates the outpoint hypothesis (uses the non-palindromic
  `vectorAsymmetricTxid` and `displayTxid_not_identity_witness`).
* `displayOrderPreimage_ne_ofTx` — consequently the display-order preimage is
  not the transaction-derived one.
* `fieldAgreement_outpoint_verbatim` — the preimage outpoint is exactly the
  wire txid in **internal** order; the preimage and vendored encoder insert it
  verbatim and never reverse it.

### 3.7 Amount boundary: gross spent value, not produced output value

* **`vectorHtlcSpend_amount_is_gross`** — the preimage amount is `7000` sat
  while `successWire.valueSat` is `3485` sat (the second-stage fee is withheld).
* `htlcSpend_amount_context` — the preimage records `s.amountSat`, while the
  produced output's `valueSat` is `s.paidValueSat =
  s.amountSat - s.secondStageFeeSat`.

### 3.8 Bundled summary

* **`preimage_coverage_summary`** — conjunctions of: the exact equivalence,
  conditional byte equality, signature-coverage transfer, the two
  dropped-hypothesis negatives, the legacy-projection negative, the
  display-order negative, and the gross/produced amount witness.

## 4. Validation

Toolchain path and shared lock were used as required.

```bash
cd /home/ubuntu/ln-lean-repair
export PATH=/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Proofs.Channel.PreimageCoverageTargets
```

Result:

```text
Build completed successfully (51 jobs).
```

Axiom audit (separate `lake env lean` checks; all printed dependencies):

```text
fieldAgreement_iff_eq_ofTx_and_amount : propext, Classical.choice, Quot.sound
FieldAgreement.bytes_eq              : propext, Classical.choice, Quot.sound
FieldAgreement.digest_eq_vendor      : propext, Classical.choice, Quot.sound
wireSignatureCovers_of_preimage      : propext, Classical.choice, Quot.sound
counterPreimageLocktime_bytes_ne     : propext, Classical.choice, Quot.sound
counterPreimageAmount_bytes_ne       : propext, Classical.choice, Quot.sound
legacy_projection_not_determine_htlc_coverage : propext
displayOrderPreimage_not_fieldAgreement       : propext, Classical.choice, Quot.sound
preimage_coverage_summary            : propext, Classical.choice, Quot.sound
```

No `sorry`, `axiom`, `admit`, `native_decide`, `unsafe`, or
`@[implemented_by]` appears in the module (grep checked). The only axioms used
are the allowed `propext`, `Quot.sound`, and `Classical.choice`.

## 5. Explicit gaps / trust boundary

* **Byte equality, not signature binding.** `FieldAgreement.bytes_eq` and
  `wireSignatureCovers_of_preimage` transfer a verification result; they do not
  claim digest injectivity, collision resistance, or unforgeability. C1/C3 are
  not used.
* **`scriptCode` remains context.** The eight hypotheses do not constrain the
  spent witness script. In particular the 20-byte HASH160 images and the
  before-image/preimage relation are supplied by the caller
  (`HtlcSpend.WellFormed` only fixes sizes). No RIPEMD160 bridge is claimed.
* **Amount is the gross spent HTLC value.** It is not derived from
  `HtlcWire.valueSat`; identifying them would be unsound and is explicitly
  separated by `vectorHtlcSpend_amount_is_gross`.
* **Display conversion is a caller obligation.** The preimage uses internal
  byte order; a display-order txid must be converted with `internalTxid`
  (byte reversal) before it is placed in the wire/preimage.
* **Wire-only coverage is still conditional.** The legacy `CommitmentSigned`
  projection has no decoder to a commitment; the negative results in §3.4 are
  preserved. The positive transfer is conditional on `FieldAgreement` and on
  the verifier result supplied by the caller.
* **No new core changes.** The module is entirely additive; importing
  `LnLean.Proofs.Channel.HtlcPreimageTargets` was sufficient.

## 6. Catalog-integration recommendation for `PR-02`

Recommended parent integration (parent-owned files only):

1. Add to `LnLean.lean` immediately after line 58
   (`import LnLean.Proofs.Channel.HtlcPreimageTargets`):

   ```lean
   import LnLean.Proofs.Channel.PreimageCoverageTargets
   ```

2. Extend the existing `PR-02` target list in `Obligations.lean` /
   `Traceability.lean` (the row currently cites
   `HtlcPreimageTargets.htlc_preimage_target_summary`) with the following
   theorem references, all in
   `LnLean.Proofs.Channel.PreimageCoverageTargets`:

   ```text
   fieldAgreement_iff_eq_ofTx_and_amount
   FieldAgreement.bytes_eq
   FieldAgreement.digest_eq_vendor
   wireSignatureCovers_of_preimage
   counterPreimageLocktime_bytes_ne
   counterPreimageAmount_bytes_ne
   legacy_projection_not_determine_htlc_coverage
   fieldAgreement_scriptCode_free
   hash160_image_boundary
   displayOrderPreimage_not_fieldAgreement
   vectorHtlcSpend_amount_is_gross
   preimage_coverage_summary
   ```

3. Add the same theorem names to `AxiomAudit.lean` (all use only the allowed
   axioms).
4. Suggested updated `PR-02` evidence text: "arbitrary-preimage field
   hypotheses explicit and complete; conditional byte/digest/signature
   transfer mechanized; dropped-locktime and dropped-amount counterexamples;
   legacy wire-only coverage remains negative; display-order and 20-byte
   hash-image/amount boundaries retained." Do not close `PR-02` fully: the
   legacy wire projection still has no decoder, and the arbitrary-preimage
   identification remains conditional.
5. No core hook or shared-file patch is needed. If the parent wants a single
   catalog-level theorem, cite `preimage_coverage_summary`.

## 7. Summary

* **Objective met:** wire-only coverage is characterized as exactly the eight
  field agreements plus the amount context; arbitrary preimages are never
  silently identified with transaction-derived ones.
* **Files:** `LnLean/Proofs/Channel/PreimageCoverageTargets.lean`,
  `agents/reports/swarm9/S9-PR-ARBITRARY-PREIMAGE.md`.
* **Main theorem names:** `fieldAgreement_iff_eq_ofTx_and_amount`,
  `FieldAgreement.bytes_eq`, `FieldAgreement.digest_eq_vendor`,
  `wireSignatureCovers_of_preimage`, `counterPreimageLocktime_bytes_ne`,
  `counterPreimageAmount_bytes_ne`,
  `legacy_projection_not_determine_htlc_coverage`,
  `fieldAgreement_scriptCode_free`, `hash160_image_boundary`,
  `displayOrderPreimage_not_fieldAgreement`,
  `vectorHtlcSpend_amount_is_gross`, `preimage_coverage_summary`.
* **Build:** `lake build LnLean.Proofs.Channel.PreimageCoverageTargets`
  completed successfully (51 jobs); allowed-axiom audit green.
* **Lane status:** **complete**.
