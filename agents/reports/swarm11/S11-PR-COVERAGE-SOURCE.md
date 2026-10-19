# S11-PR-COVERAGE-SOURCE — coverage sources for the missing `commitment_signed` data (`PR-02`)

**Lane:** `S11-PR-COVERAGE-SOURCE`
**Issue:** `PR-02` (P1, open: the legacy `CommitmentSigned` wire record lacks
per-HTLC coverage data)
**Branch:** `repair/integrated`
**Status:** complete — scoped build green, no `sorry`/forbidden tokens, no
shared file edited, no commit or push

## 1. Objective

Extend the wave-10 witness result (`CoverageWitnessTargets.lean`) into an
explicit **source/interface model** for the data a `commitment_signed` coverage
consumer needs but the legacy wire does not carry. The lane was asked to:

1. define a coverage-source type with a full-record source, an out-of-band
   witness source, and a protocol-extension source;
2. give a canonical decoder from each source to the legacy coverage projection,
   prove the full-record source exact, and prove the legacy wire alone has no
   source;
3. model a `ProtocolExtension` with the minimum per-HTLC fields and prove that
   extension plus legacy wire determines coverage under explicit field-binding
   hypotheses;
4. separate sources: the wire cannot select between distinct witnesses, and an
   out-of-band witness is not authenticated by the wire without an explicit
   binding law;
5. supply a realizable non-vacuity witness and at least one rejected/
   counterexample case;
6. preserve the strongest true conditional statements without claiming a
   protocol change or a production decoder.

## 2. Artifacts

| Path | Kind | Notes |
|---|---|---|
| `LnLean/Proofs/Channel/CoverageSourceTargets.lean` | new Lean module (owned) | 1077 lines; 66 public theorems; imports `CoverageWitnessTargets`. |
| `agents/reports/swarm11/S11-PR-COVERAGE-SOURCE.md` | new report (owned) | This file. |

No edits were made to `Messages.lean`, `Commitment.lean`, `Types.lean`,
`CoverageWitnessTargets.lean`, `PreimageCoverageTargets.lean`,
`ProtocolWireTargets.lean`, `LnLean.lean`, `Obligations.lean`,
`Traceability.lean`, `AxiomAudit.lean`, docs, the catalog, scripts, or tests.

## 3. Design

### 3.1 `ProtocolExtension`

The extension is the smallest per-HTLC record that, together with the legacy
wire, determines the covered output list. One row is:

```lean
structure HtlcCoverageFields where
  amount : Msat
  cltvExpiry : Height
  paymentHash : PaymentHash
  direction : Direction
  htlcState : HTLCState
  scriptTag : HtlcScriptTag
```

`HtlcScriptTag` (`offered`/`received`) abstracts the BOLT 3 second-stage script
family; it does not encode the 143/136-byte script. The channel-level record is

```lean
structure ProtocolExtension where
  channelId : ChannelId
  rows : List HtlcCoverageFields
```

with `ProtocolExtension.toCoverage : List CommitmentHTLCOutput` applying the
same BOLT 3 satoshi floor as `SignedHtlcEntry.toCommitmentHtlcOutput`.

The extension deliberately has **no signature field**: the legacy wire already
carries one `HTLC_signature` per row. `decodeSource` checks only the row count;
no signature verification is added or claimed.

### 3.2 Field binding

`RowBinds r e` is the explicit per-row agreement law: same amount, same
`cltv_expiry`, same payment hash image, same direction, same lifecycle state,
and a script tag equal to the state's family convention. `RowsBind` lifts it to
two ordered lists; `ExtensionBinds ext f` adds the channel-id equation.

Coverage equality is **derived** row by row:

```lean
theorem RowBinds.output_eq : r.toCommitmentHtlcOutput = e.toCommitmentHtlcOutput
theorem RowsBind.coverage_eq :
  rs.map HtlcCoverageFields.toCommitmentHtlcOutput =
    es.map SignedHtlcEntry.toCommitmentHtlcOutput
theorem ExtensionBinds.coverage_eq : ext.toCoverage = coverageOfFull f
```

### 3.3 Sources

```lean
inductive CoverageSource where
  | fullRecord (record : CommitmentSignedFull)
  | outOfBand (witness : OutOfBandWitness)
  | protocolExtension (extension : ProtocolExtension)
```

`OutOfBandWitness` carries `entries : List SignedHtlcEntry` and an explicit
`origin : WitnessOrigin` (`localSigner`, `persistedTranscript`,
`untrustedPeer`). `OutOfBandBinding m o` is the explicit law
`wireCompatible m o.toWitness ∧ TrustedOrigin o.origin`; it is **not** derived
from the wire. `TrustedOrigin` is a model policy, not cryptographic
authentication.

### 3.4 Decoder

```lean
def decodeSource (m : CommitmentSigned) :
    CoverageSource → Option (List CommitmentHTLCOutput)
  | .fullRecord f => decodeCoverage m (witnessOfFull f)
  | .outOfBand o => decodeCoverage m o.toWitness
  | .protocolExtension ext =>
      if m.htlcSignatures.length = ext.rows.length then
        some ext.toCoverage
      else none
```

The full-record and out-of-band cases reuse the wave-10 `decodeCoverage`; the
extension case checks the only wire-derivable condition (row count). The wire
never supplies identification data in any branch.

### 3.5 Canonical extension of every full record

`extensionOfFull f` maps each `SignedHtlcEntry` to an `HtlcCoverageFields` row
and sets `scriptTag := HtlcScriptTag.ofState e.htlcState`.
`extensionOfFull_binds` proves the canonical extension is field-bound to `f`,
and `decodeSource_extensionOfFull_canonical` proves it decodes exactly. This
makes the extension source realizable for **every** full record, not just the
concrete example.

## 4. Exact claims and theorem names

All names below are in namespace
`LnLean.Proofs.Channel.CoverageSourceTargets` unless a inner namespace is
shown. Line numbers refer to the module.

### 4.1 Extension model and field binding

| Theorem | Line | Statement / assumptions |
|---|---|---|
| `HtlcScriptTag.ofState_offered` | 126 | live offered tag is definitional. |
| `HtlcScriptTag.ofState_received` | 129 | live received tag is definitional. |
| `HtlcScriptTag.ofState_toState` | 133 | `ofState t.toState = t` for both tags. |
| `HtlcCoverageFields.toCommitmentHtlcOutput_direction` | 174 | projection field equation. |
| `HtlcCoverageFields.toCommitmentHtlcOutput_amountSat` | 177 | projection uses `amount.toSatFloor`. |
| `HtlcCoverageFields.toCommitmentHtlcOutput_cltvExpiry` | 180 | projection field equation. |
| `HtlcCoverageFields.toCommitmentHtlcOutput_state` | 183 | projection field equation. |
| `HtlcCoverageFields.toCommitmentHtlcOutput_update_paymentHash` | 190 | hash image is not in the output projection. |
| `HtlcCoverageFields.toCommitmentHtlcOutput_update_scriptTag` | 198 | script tag is not in the output projection. |
| `HtlcCoverageFields.toCommitmentHtlcOutput_eq_iff` | 207 | exact tuple: direction, floored amount, expiry, state; hash/tag ignored. |
| `ProtocolExtension.toCoverage_length` | 244 | extension coverage length = row count. |
| `RowBinds.output_eq` | 275 | row binding implies equal output projection. |
| `RowsBind.cons_inv` | 294 | inversion of one bound cons cell. |
| `RowsBind.length_eq` | 302 | bound lists have equal length. |
| `RowsBind.coverage_eq` | 311 | bound lists have equal coverage maps. |
| `ExtensionBinds.channelId_agrees` | 334 | bound channel id. |
| `ExtensionBinds.rowCount` | 339 | extension row count = entry count. |
| `ExtensionBinds.coverage_eq` | 348 | field binding determines coverage. |

### 4.2 Sources and the binding law

| Theorem | Line | Statement / assumptions |
|---|---|---|
| `OutOfBandWitness.toWitness_entries` | 391 | projection to the wave-10 witness. |
| `trustedOrigin_localSigner` | 404 | local signer is trusted. |
| `trustedOrigin_persistedTranscript` | 406 | persisted transcript is trusted. |
| `not_trustedOrigin_untrustedPeer` | 409 | untrusted peer is not trusted. |
| `outOfBandBinding_wireCompatible` | 419 | binding implies wire compatibility. |
| `outOfBandBinding_trustedOrigin` | 425 | binding implies a trusted origin. |
| `trusted_origin_binding` | 433 | wire compatibility + trusted origin give binding (explicit law). |
| `out_of_band_binding_iff` | 439 | definitional characterization of binding. |
| `fullSource_eq` | 467 | full-record source constructor. |
| `outOfBandSource_eq` | 470 | out-of-band source constructor. |
| `extensionSource_eq` | 473 | extension source constructor. |

### 4.3 Decoder correctness

| Theorem | Line | Statement / assumptions |
|---|---|---|
| **`decodeSource_fullRecord_exact`** | 499 | no hypotheses: `decodeSource f.toCommitmentSigned (.fullRecord f) = some (coverageOfFull f)`. |
| `decodeSource_fullRecord_eq_decodeCoverage` | 504 | full-record branch is the wave-10 decoder. |
| **`decodeSource_outOfBand_canonical`** | 511 | for any origin tag, the witness with `f.htlcEntries` decodes exactly. |
| `decodeSource_outOfBand_of_wireCompatible` | 519 | `wireCompatible m o.toWitness` implies success with `o.entries`' outputs. |
| `decodeSource_outOfBand_eq_decodeCoverage` | 527 | out-of-band branch is the wave-10 decoder. |
| `decodeSource_protocolExtension` | 532 | assumes `m.htlcSignatures.length = ext.rows.length`. |
| `decodeSource_protocolExtension_none` | 540 | assumes the two counts differ. |
| `decodeSource_protocolExtension_eq_some_iff` | 549 | success iff row counts match and output = `ext.toCoverage`. |
| `decodeSource_covers` | 562 | successful decode + `c.htlcs = outs` gives `CoversHtlcOutputs m c`. |
| **`extension_plus_wire_determines_coverage`** | 585 | assumes `m = f.toCommitmentSigned`, wire/source row-count equality, and `ExtensionBinds ext f`; concludes exact coverage. |
| `extension_plus_wire_covers` | 596 | the same three hypotheses plus `c.htlcs = coverageOfFull f` give `CoversHtlcOutputs m c`. |
| `extensionOfFull_rows_bind` | 630 | canonical rows bind every entry list. |
| `extensionOfFull_binds` | 639 | canonical extension binds every full record. |
| `extensionOfFull_coverage` | 645 | canonical extension coverage equals the record coverage. |
| **`decodeSource_extensionOfFull_canonical`** | 653 | canonical extension source decodes exactly for every full record. |

### 4.4 Source separation

| Theorem | Line | Statement / assumptions |
|---|---|---|
| **`no_wire_determined_source`** | 675 | no `CommitmentSigned → CoverageSource` decodes every full record correctly. |
| **`no_wire_source_selector`** | 695 | no wire function recovers `.fullRecord f` for every full record (opaque source selection is impossible). |
| **`wire_admits_distinct_out_of_band_witnesses`** | 714 | same wire, two trusted-origin witnesses, different entries, different decodes. |
| `out_of_band_origin_irrelevant_to_decode` | 759 | changing the origin tag does not change the decode. |
| **`wireCompatible_not_out_of_band_binding`** | 769 | same wire-compatible entries with `untrustedPeer` origin satisfy no binding law. |
| **`no_wire_witness_authenticator`** | 784 | no wire-only Boolean authenticator is both complete for the canonical witness and sound for every full record. |

### 4.5 Non-vacuity, rejected cases, and field necessity

| Theorem | Line | Statement / assumptions |
|---|---|---|
| `exampleExtension_binds_fullA` | 824 | concrete extension binds `witnessFullA`. |
| `exampleExtension_coverage` | 828 | concrete extension coverage = record coverage. |
| `exampleExtension_decodes` | 833 | concrete extension decodes against the concrete wire. |
| **`exampleExtension_nonvacuous`** | 842 | closed conjunction: binds, nonempty coverage, decodes. |
| `exampleExtension_rowCount` | 854 | one extension row = one wire HTLC signature. |
| **`mismatchedAmountExtension_not_binds`** | 876 | 2000 msat row is rejected against the 1000 msat record. |
| `mismatchedAmountExtension_coverage_ne` | 891 | rejected extension also has different coverage. |
| **`mismatchedTagExtension_not_binds`** | 913 | received-tag row is rejected for an offered entry. |
| `mismatchedTagExtension_coverage_eq` | 928 | the rejected tag variant still has the correct coverage (tag is bound separately). |
| **`emptyWire_rejects_extension`** | 940 | zero-signature wire rejects a one-row extension. |
| `extension_amount_binding_necessary` | 949 | same expiry/hash/direction/state/tag, different amount ⇒ different coverage. |
| `extension_cltv_binding_necessary` | 970 | same amount/hash/direction/state/tag, different expiry ⇒ different coverage. |
| `extension_direction_binding_necessary` | 990 | same amount/expiry/hash/state/tag, different direction ⇒ different coverage. |
| `paymentHash_binding_separate_from_coverage` | 1009 | hash image is bound but not in the output projection. |
| `scriptTag_binding_separate_from_coverage` | 1016 | script tag is bound but not in the output projection. |
| **`coverage_source_summary`** | 1041 | bundles exactness, conditional extension determinacy, non-vacuity, no wire source, distinct witnesses, and missing authentication. |

## 5. Non-vacuity and counterexamples

### 5.1 Realizable extension

`exampleRow` is `extensionRowOfEntry witnessEntryA`; `exampleExtension` is
`extensionOfFull witnessFullA`. The closed theorem
`exampleExtension_nonvacuous` establishes, with no hypotheses:

```lean
ExtensionBinds exampleExtension witnessFullA ∧
exampleExtension.toCoverage ≠ [] ∧
decodeSource witnessFullA.toCommitmentSigned
  (.protocolExtension exampleExtension) = some (coverageOfFull witnessFullA)
```

The generic construction `extensionOfFull` and
`decodeSource_extensionOfFull_canonical` extend this to every
`CommitmentSignedFull`. This is non-vacuous: the wave-10 concrete record has one
HTLC of 1000 msat, and the extension's row count matches its one wire
`HTLC_signature`.

### 5.2 Rejected amount

`mismatchedAmountRow` changes only `amount` from `⟨1000⟩` to `⟨2000⟩` under the
same channel id, hash image, direction, expiry, state, and tag.
`mismatchedAmountExtension_not_binds` proves `ExtensionBinds` fails (the
binding equation would force `2000 = 1000`), and
`mismatchedAmountExtension_coverage_ne` proves the decoded output differs
(1 sat vs 2 sat after the floor). This is the substantive counterexample: the
extension is not accepted merely because its shape and channel id are right.

### 5.3 Rejected script tag, same coverage

`mismatchedTagRow` changes only `scriptTag` from `offered` to `received`.
`mismatchedTagExtension_not_binds` rejects it, while
`mismatchedTagExtension_coverage_eq` proves its covered output list is still the
record's coverage. The tag is therefore an authentication/script-selection
field, not an output-value field; this is exactly why `RowBinds` binds it
separately.

### 5.4 Rejected wire count

`emptyWire` has no HTLC signatures. `emptyWire_rejects_extension` proves the
one-row extension decoder returns `none`; the general theorem
`decodeSource_protocolExtension_none` covers every mismatched count.

### 5.5 Imported wave-10 counterexample pair

The separation theorems reuse `witnessFullA`/`witnessFullB` from
`CoverageWitnessTargets`: the two full records have the same legacy projection
(`witness_full_same_projection`) and different coverage
(`witness_full_coverage_ne`). They are the concrete witnesses for
`no_wire_determined_source`, `no_wire_source_selector`,
`wire_admits_distinct_out_of_band_witnesses`, and
`no_wire_witness_authenticator`.

## 6. Validation

### 6.1 Scoped build

Command (exact lane command):

```sh
cd /home/ubuntu/ln-lean-repair && \
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Proofs.Channel.CoverageSourceTargets
```

Result:

```text
Build completed successfully (53 jobs).
```

The only warnings in the build log are pre-existing deprecation warnings from
dependency modules (`Bitcoin/Serialization/Interface.lean`,
`LnLean/Bitcoin/Sighash.lean`); the new module emits no warnings.

### 6.2 Forbidden-token scan

```sh
grep -nE '\b(sorry|admit|axiom|native_decide|unsafe)\b|implemented_by' \
  LnLean/Proofs/Channel/CoverageSourceTargets.lean
```

Result: no matches.

### 6.3 Axiom audit

Every one of the 66 public theorems was audited with `#print axioms` in a
temporary file outside the repository. Allowed set: `propext`, `Quot.sound`,
`Classical.choice`.

* 31 theorems depend on **no axioms**.
* 32 theorems depend on `propext` only.
* 3 theorems depend on `propext` and `Quot.sound`:
  `decodeSource_covers`, `extension_plus_wire_covers`,
  `mismatchedAmountExtension_not_binds`.
* No theorem uses `Classical.choice`.
* No axiom outside the allowed set appears.

No-axiom theorems (31):

```text
HtlcScriptTag.ofState_offered; HtlcScriptTag.ofState_received;
HtlcScriptTag.ofState_toState;
HtlcCoverageFields.toCommitmentHtlcOutput_direction;
HtlcCoverageFields.toCommitmentHtlcOutput_amountSat;
HtlcCoverageFields.toCommitmentHtlcOutput_cltvExpiry;
HtlcCoverageFields.toCommitmentHtlcOutput_state;
HtlcCoverageFields.toCommitmentHtlcOutput_update_paymentHash;
HtlcCoverageFields.toCommitmentHtlcOutput_update_scriptTag;
RowsBind.cons_inv; ExtensionBinds.channelId_agrees;
OutOfBandWitness.toWitness_entries;
trustedOrigin_localSigner; trustedOrigin_persistedTranscript;
not_trustedOrigin_untrustedPeer;
outOfBandBinding_wireCompatible; outOfBandBinding_trustedOrigin;
trusted_origin_binding; out_of_band_binding_iff;
fullSource_eq; outOfBandSource_eq; extensionSource_eq;
decodeSource_fullRecord_eq_decodeCoverage;
decodeSource_outOfBand_eq_decodeCoverage;
extensionOfFull_rows_bind; extensionOfFull_binds;
out_of_band_origin_irrelevant_to_decode;
wireCompatible_not_out_of_band_binding;
exampleExtension_binds_fullA;
paymentHash_binding_separate_from_coverage;
scriptTag_binding_separate_from_coverage
```

`propext`-only theorems (32):

```text
HtlcCoverageFields.toCommitmentHtlcOutput_eq_iff;
ProtocolExtension.toCoverage_length; RowBinds.output_eq;
RowsBind.length_eq; RowsBind.coverage_eq;
ExtensionBinds.rowCount; ExtensionBinds.coverage_eq;
decodeSource_fullRecord_exact; decodeSource_outOfBand_canonical;
decodeSource_outOfBand_of_wireCompatible;
decodeSource_protocolExtension; decodeSource_protocolExtension_none;
decodeSource_protocolExtension_eq_some_iff;
extension_plus_wire_determines_coverage; extensionOfFull_coverage;
decodeSource_extensionOfFull_canonical;
no_wire_determined_source; no_wire_source_selector;
wire_admits_distinct_out_of_band_witnesses;
no_wire_witness_authenticator;
exampleExtension_coverage; exampleExtension_decodes;
exampleExtension_nonvacuous; exampleExtension_rowCount;
mismatchedAmountExtension_coverage_ne;
mismatchedTagExtension_not_binds; mismatchedTagExtension_coverage_eq;
emptyWire_rejects_extension;
extension_amount_binding_necessary; extension_cltv_binding_necessary;
extension_direction_binding_necessary;
coverage_source_summary
```

`propext` + `Quot.sound` (3):

```text
decodeSource_covers; extension_plus_wire_covers;
mismatchedAmountExtension_not_binds
```

## 7. Precise scope and remaining boundary

This module adds a **source/interface model**, not a production decoder and not
a protocol change.

1. `ProtocolExtension` is a specification of the minimum fields needed for
   determinate coverage. It is not a BOLT 2 message, TLV, or negotiated
   extension, and no wire encoding is claimed.
2. `HtlcScriptTag` is a script-family tag, not script bytes. The model has no
   BOLT 3 script encoder; key-dependent 143/136-byte scripts remain outside the
   model.
3. `ExtensionBinds` is an explicit field-agreement hypothesis. It is not
   derived from the legacy wire or from signatures. `extension_plus_wire_*`
   theorems are conditional on it.
4. `decodeSource` checks only source/wire row counts. It does not verify ECDSA
   signatures, commitment digests, or BOLT 3 sighashes; those remain the
   existing signature/digest obligations.
5. `WitnessOrigin` is a policy tag, not a cryptographic authentication proof.
   `OutOfBandBinding` is supplied explicitly; `wireCompatible_not_out_of_band_binding`
   proves the wire does not imply it.
6. The payment hash is bound by `RowBinds` but is not part of the output
   projection. It remains necessary for HTLC identity and second-stage script
   selection (`paymentHash_binding_separate_from_coverage`).
7. The terminal-state convention in `HtlcScriptTag.ofState` is total by
   convention; only `offered`/`received` have live commitment outputs. No claim
   is made about scripts for terminal states.
8. `no_wire_determined_source` and `no_wire_source_selector` are the strongest
   true wire-only negatives at this interface. They do not say a source cannot
   be supplied; they say it cannot be recovered from the legacy wire alone.

What remains open for `PR-02` is the production provenance of the source (or a
future protocol encoding that carries the extension fields). The algebraic
coverage projection and the source-interface separation are now explicit; the
legacy wire alone is still not sufficient.

## 8. Integration recommendation for `LN-PR-004`

`LN-PR-004` currently records the wave-10 witness results and ends with
"wire-only legacy coverage remains negative". Recommended parent actions:

1. Add the module to the root import set:

   ```lean
   import LnLean.Proofs.Channel.CoverageSourceTargets
   ```

2. Append these targets to the `LN-PR-004` `leanTarget` list (and the generated
   `agents/status/obligations.json` row):

   ```text
   LnLean.Proofs.Channel.CoverageSourceTargets.decodeSource_fullRecord_exact;
   LnLean.Proofs.Channel.CoverageSourceTargets.decodeSource_outOfBand_canonical;
   LnLean.Proofs.Channel.CoverageSourceTargets.decodeSource_extensionOfFull_canonical;
   LnLean.Proofs.Channel.CoverageSourceTargets.extension_plus_wire_determines_coverage;
   LnLean.Proofs.Channel.CoverageSourceTargets.extension_plus_wire_covers;
   LnLean.Proofs.Channel.CoverageSourceTargets.no_wire_determined_source;
   LnLean.Proofs.Channel.CoverageSourceTargets.no_wire_source_selector;
   LnLean.Proofs.Channel.CoverageSourceTargets.wire_admits_distinct_out_of_band_witnesses;
   LnLean.Proofs.Channel.CoverageSourceTargets.wireCompatible_not_out_of_band_binding;
   LnLean.Proofs.Channel.CoverageSourceTargets.no_wire_witness_authenticator;
   LnLean.Proofs.Channel.CoverageSourceTargets.exampleExtension_nonvacuous;
   LnLean.Proofs.Channel.CoverageSourceTargets.mismatchedAmountExtension_not_binds;
   LnLean.Proofs.Channel.CoverageSourceTargets.coverage_source_summary
   ```

3. Append to the `LN-PR-004` claim:

   > The missing legacy-wire data is modelled as an explicit coverage source:
   > the full-record source decodes exactly, an out-of-band witness decodes
   > under wire compatibility, and a field-bound `ProtocolExtension` plus the
   > legacy wire determines coverage. No wire-only function recovers the
   > source, the same wire admits distinct out-of-band witnesses, and wire
   > compatibility does not authenticate a witness without an explicit
   > binding law. The extension is a specification, not a wire encoding; a
   > production decoder and any protocol change remain future work.

4. Add all 66 public theorems to `AxiomAudit.lean` (they use only `propext`,
   `Quot.sound`, or no axioms, so the allowed-axiom gate stays green).

5. Add the module to the `LN-PR-004` traceability target list in
   `LnLean/Proofs/Traceability.lean`.

`PR-02` should remain **open**: this lane narrows the gap to source provenance
and conditional extension determinacy; it does not close the production
decoder or protocol-change gap.

## 9. Compliance

* One new Lean file and one new report only.
* No existing file, root import, catalog, traceability, audit, docs, script, or
  test was edited.
* No commit or push.
* No `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, or
  `@[implemented_by]` appears in the new module.
