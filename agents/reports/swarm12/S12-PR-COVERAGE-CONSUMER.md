# S12-PR-COVERAGE-CONSUMER — consumer contracts for `commitment_signed` coverage

**Lane:** `S12-PR-COVERAGE-CONSUMER`
**Catalog row:** `LN-PR-004` (commitment_signed coverage). The earlier lane brief
used the label `PR-02`; the parent correction establishes that the catalog row
is `LN-PR-004`, and this report uses that identifier throughout. No shared
catalog, docs, obligations, traceability, or audit file was edited.
**Base:** `repair/integrated`
**Status:** complete — scoped build green, no forbidden tokens, no
`Classical.choice`, no shared files edited, no commit/push.

## 1. Objective

Add a model-level **consumer contract** for the existing `CoverageSource`
model of `commitment_signed` coverage:

1. define a consumer structure that composes with `CoverageSource`, rather than
   replacing it;
2. prove a full-record source yields a consumer exact for every produced full
   record;
3. restate the legacy-wire impossibility at consumer level without weakening
   it;
4. prove protocol extension plus wire determines a consumer only under an
   explicit binding law, and state that law exactly;
5. prove source separation and give a closed, non-vacuous consumer witness;
6. keep the production boundary honest: no production decoder, no wire change,
   no claim that BOLT 2 changed.

## 2. Artifacts

| Path | Kind | Notes |
|---|---|---|
| `LnLean/Proofs/Channel/CoverageConsumerTargets.lean` | new Lean module (owned) | Imports `CoverageSourceTargets`; 582 lines. |
| `agents/reports/swarm12/S12-PR-COVERAGE-CONSUMER.md` | new report (owned) | This file. |

No other file was modified. In particular, `Obligations.lean`,
`Traceability.lean`, `LnLean.lean`, `AxiomAudit.lean`, docs, scripts, tests,
and the catalog were not edited.

## 3. Design

### 3.1 The consumer composes with `CoverageSource`

```lean
structure CoverageConsumer where
  wire : CommitmentSigned
  source : CoverageSource
  outputs : List CommitmentHTLCOutput
  decodes : decodeSource wire source = some outputs
```

The `source` field is the existing wave-12 `CoverageSource`; the `wire` field is
the legacy `CommitmentSigned`; `outputs` is the exact covered list; and
`decodes` is a proof that the canonical `decodeSource` accepts the pair. A
consumer is therefore a certificate, not an unchecked pair.

Two projections complete the contract:

```lean
def CoverageConsumer.CorrectFor (k : CoverageConsumer)
    (f : CommitmentSignedFull) : Prop :=
  k.wire = f.toCommitmentSigned ∧ k.outputs = coverageOfFull f

def CoverageConsumer.Covers (k : CoverageConsumer)
    (c : Commitment) : Prop :=
  k.outputs = c.htlcs
```

`CoverageConsumer.coversHtlcOutputs` transfers `Covers` to the existing
`CoversHtlcOutputs` predicate through `decodeSource_covers`, so the consumer
contract is connected to the prior wire-coverage model rather than parallel to
it.

### 3.2 Full-record consumer

`fullRecordConsumer f` is built from `.fullRecord f` and
`decodeSource_fullRecord_exact`. It is exact for `f` unconditionally:
`(fullRecordConsumer f).CorrectFor f`. `fullRecordConsumer_covers` additionally
turns any commitment `c` with `c.htlcs = coverageOfFull f` into
`CoversHtlcOutputs f.toCommitmentSigned c`.

`outOfBandConsumer f origin` is the analogous canonical out-of-band consumer.
The origin tag is carried as data and does not alter the decoded list.

### 3.3 Extension consumer law

The extension cannot determine a consumer from the wire row count alone. The
module states the exact law:

```lean
structure ExtensionConsumerLaw (ext : ProtocolExtension)
    (m : CommitmentSigned) (f : CommitmentSignedFull) : Prop where
  wire_eq : m = f.toCommitmentSigned
  rowCount_eq : m.htlcSignatures.length = ext.rows.length
  binds : ExtensionBinds ext f
```

`ExtensionBinds ext f` is the existing wave-12 law:

```text
ext.channelId = f.channelId
RowsBind ext.rows f.htlcEntries
```

and `RowsBind` means, pointwise for each extension row `r` and signed entry
`e`, exactly:

```text
r.amount = e.amount
r.cltvExpiry = e.cltvExpiry
r.paymentHash = e.paymentHash
r.direction = e.direction
r.htlcState = e.htlcState
r.scriptTag = HtlcScriptTag.ofState e.htlcState
```

`rowBinds_iff` restates this six-field expansion. `extensionConsumerLaw_iff`
states the law as the exact conjunction of wire equality, row-count equality,
and `ExtensionBinds`; `extensionConsumerLaw_fields` unpacks it to the channel
id and row list. `ExtensionBinds` is a *sufficient explicit law*, not something
the legacy wire can supply; `extension_rowCount_not_determining` proves the
row-count check alone is insufficient.

## 4. Public definitions

All names below are in namespace
`LnLean.Proofs.Channel.CoverageConsumerTargets`.

| # | Fully-qualified name | Kind / body summary |
|---|---|---|
| 1 | `CoverageConsumer` | structure: `wire`, `source : CoverageSource`, `outputs`, `decodes` |
| 2 | `CoverageConsumer.CorrectFor` | `k.wire = f.toCommitmentSigned ∧ k.outputs = coverageOfFull f` |
| 3 | `CoverageConsumer.Covers` | `k.outputs = c.htlcs` |
| 4 | `fullRecordConsumer` | `.fullRecord f`, outputs `coverageOfFull f`, exact decode proof |
| 5 | `outOfBandConsumer` | `.outOfBand { entries := f.htlcEntries, origin }`, exact decode proof |
| 6 | `ExtensionConsumerLaw` | structure: `wire_eq`, `rowCount_eq`, `binds : ExtensionBinds ext f` |
| 7 | `extensionConsumer` | consumer from an `ExtensionConsumerLaw` |
| 8 | `exampleWire` | `witnessFullA.toCommitmentSigned` (one HTLC signature) |
| 9 | `exampleCommitmentA` | commitment with `htlcs := coverageOfFull witnessFullA` |
| 10 | `exampleCommitmentB` | commitment with `htlcs := coverageOfFull witnessFullB` |
| 11 | `exampleFullConsumer` | `fullRecordConsumer witnessFullA` |
| 12 | `exampleOutOfBandWitnessB` | `{ entries := witnessFullB.htlcEntries, origin := .localSigner }` |
| 13 | `exampleOutOfBandConsumerB` | out-of-band consumer over `exampleWire`, outputs of B |
| 14 | `exampleExtensionConsumerA` | extension consumer over `exampleWire`, canonical extension of A |

Counts: **12 definitions + 2 structures**, plus **29 public theorems**.

## 5. Public theorems with exact statements

Every name below is fully qualified. The statements are reproduced exactly as
they appear in the module, with the module namespace omitted only from the
bodies (all free names resolve in
`LnLean.Proofs.Channel.CoverageConsumerTargets`).

1. `LnLean.Proofs.Channel.CoverageConsumerTargets.CoverageConsumer.coversHtlcOutputs`

```text
{k : CoverageConsumer} {c : Commitment} (h : k.Covers c) :
  CoversHtlcOutputs k.wire c
```

2. `LnLean.Proofs.Channel.CoverageConsumerTargets.fullRecordConsumer_source`

```text
(f : CommitmentSignedFull) : (fullRecordConsumer f).source = .fullRecord f
```

3. `LnLean.Proofs.Channel.CoverageConsumerTargets.fullRecordConsumer_outputs`

```text
(f : CommitmentSignedFull) : (fullRecordConsumer f).outputs = coverageOfFull f
```

4. `LnLean.Proofs.Channel.CoverageConsumerTargets.fullRecordConsumer_correct`

```text
(f : CommitmentSignedFull) : (fullRecordConsumer f).CorrectFor f
```

5. `LnLean.Proofs.Channel.CoverageConsumerTargets.fullRecordConsumer_covers`

```text
(f : CommitmentSignedFull) (c : Commitment)
  (hc : c.htlcs = coverageOfFull f) :
  (fullRecordConsumer f).Covers c ∧ CoversHtlcOutputs f.toCommitmentSigned c
```

6. `LnLean.Proofs.Channel.CoverageConsumerTargets.outOfBandConsumer_correct`

```text
(f : CommitmentSignedFull) (origin : WitnessOrigin) :
  (outOfBandConsumer f origin).CorrectFor f
```

7. `LnLean.Proofs.Channel.CoverageConsumerTargets.outOfBandConsumer_source`

```text
(f : CommitmentSignedFull) (origin : WitnessOrigin) :
  (outOfBandConsumer f origin).source =
    .outOfBand { entries := f.htlcEntries, origin := origin }
```

8. `LnLean.Proofs.Channel.CoverageConsumerTargets.no_wire_determined_consumer`

```text
¬ ∃ consume : CommitmentSigned → CoverageConsumer,
    ∀ f : CommitmentSignedFull,
      (consume f.toCommitmentSigned).CorrectFor f
```

9. `LnLean.Proofs.Channel.CoverageConsumerTargets.no_wire_determined_fullRecord_consumer`

```text
¬ ∃ consume : CommitmentSigned → CoverageConsumer,
    ∀ f : CommitmentSignedFull,
      (consume f.toCommitmentSigned).source = CoverageSource.fullRecord f
```

10. `LnLean.Proofs.Channel.CoverageConsumerTargets.extensionConsumerLaw_iff`

```text
(ext : ProtocolExtension) (m : CommitmentSigned) (f : CommitmentSignedFull) :
  ExtensionConsumerLaw ext m f ↔
    m = f.toCommitmentSigned ∧
      m.htlcSignatures.length = ext.rows.length ∧
        ExtensionBinds ext f
```

11. `LnLean.Proofs.Channel.CoverageConsumerTargets.extensionConsumerLaw_fields`

```text
{ext : ProtocolExtension} {m : CommitmentSigned} {f : CommitmentSignedFull}
  (h : ExtensionConsumerLaw ext m f) :
  m = f.toCommitmentSigned ∧
    m.htlcSignatures.length = ext.rows.length ∧
      ext.channelId = f.channelId ∧
        RowsBind ext.rows f.htlcEntries
```

12. `LnLean.Proofs.Channel.CoverageConsumerTargets.rowBinds_iff`

```text
(r : HtlcCoverageFields) (e : SignedHtlcEntry) :
  RowBinds r e ↔
    r.amount = e.amount ∧
      r.cltvExpiry = e.cltvExpiry ∧
        r.paymentHash = e.paymentHash ∧
          r.direction = e.direction ∧
            r.htlcState = e.htlcState ∧
              r.scriptTag = HtlcScriptTag.ofState e.htlcState
```

13. `LnLean.Proofs.Channel.CoverageConsumerTargets.extensionConsumer_source`

```text
{ext : ProtocolExtension} {m : CommitmentSigned} {f : CommitmentSignedFull}
  (h : ExtensionConsumerLaw ext m f) :
  (extensionConsumer h).source = .protocolExtension ext
```

14. `LnLean.Proofs.Channel.CoverageConsumerTargets.extensionConsumer_outputs`

```text
{ext : ProtocolExtension} {m : CommitmentSigned} {f : CommitmentSignedFull}
  (h : ExtensionConsumerLaw ext m f) :
  (extensionConsumer h).outputs = coverageOfFull f
```

15. `LnLean.Proofs.Channel.CoverageConsumerTargets.extension_consumer_determines`

```text
{ext : ProtocolExtension} {m : CommitmentSigned} {f : CommitmentSignedFull}
  (h : ExtensionConsumerLaw ext m f) :
  (extensionConsumer h).source = .protocolExtension ext ∧
    (extensionConsumer h).outputs = coverageOfFull f ∧
      (extensionConsumer h).CorrectFor f
```

16. `LnLean.Proofs.Channel.CoverageConsumerTargets.extensionConsumer_covers`

```text
{ext : ProtocolExtension} {m : CommitmentSigned} {f : CommitmentSignedFull}
  (h : ExtensionConsumerLaw ext m f) (c : Commitment)
  (hc : c.htlcs = coverageOfFull f) :
  (extensionConsumer h).Covers c ∧ CoversHtlcOutputs m c
```

17. `LnLean.Proofs.Channel.CoverageConsumerTargets.extensionConsumerLaw_coverage_eq`

```text
{ext : ProtocolExtension} {m : CommitmentSigned} {f : CommitmentSignedFull}
  (h : ExtensionConsumerLaw ext m f) :
  ext.toCoverage = coverageOfFull f
```

18. `LnLean.Proofs.Channel.CoverageConsumerTargets.extension_rowCount_not_determining`

```text
∃ (m : CommitmentSigned) (ext₁ ext₂ : ProtocolExtension),
  m.htlcSignatures.length = ext₁.rows.length ∧
    m.htlcSignatures.length = ext₂.rows.length ∧
      decodeSource m (.protocolExtension ext₁) ≠
        decodeSource m (.protocolExtension ext₂)
```

19. `LnLean.Proofs.Channel.CoverageConsumerTargets.fullRecordSource_ne_outOfBandSource`

```text
(f : CommitmentSignedFull) (o : OutOfBandWitness) :
  CoverageSource.fullRecord f ≠ CoverageSource.outOfBand o
```

20. `LnLean.Proofs.Channel.CoverageConsumerTargets.fullRecordSource_ne_extensionSource`

```text
(f : CommitmentSignedFull) (ext : ProtocolExtension) :
  CoverageSource.fullRecord f ≠ CoverageSource.protocolExtension ext
```

21. `LnLean.Proofs.Channel.CoverageConsumerTargets.outOfBandSource_ne_extensionSource`

```text
(o : OutOfBandWitness) (ext : ProtocolExtension) :
  CoverageSource.outOfBand o ≠ CoverageSource.protocolExtension ext
```

22. `LnLean.Proofs.Channel.CoverageConsumerTargets.exampleFullConsumer_correct`

```text
exampleFullConsumer.CorrectFor witnessFullA
```

23. `LnLean.Proofs.Channel.CoverageConsumerTargets.exampleOutOfBandConsumerB_correct`

```text
exampleOutOfBandConsumerB.CorrectFor witnessFullB
```

24. `LnLean.Proofs.Channel.CoverageConsumerTargets.exampleExtensionConsumerA_correct`

```text
exampleExtensionConsumerA.CorrectFor witnessFullA
```

25. `LnLean.Proofs.Channel.CoverageConsumerTargets.exampleFullConsumer_covers`

```text
exampleFullConsumer.outputs ≠ [] ∧
  exampleFullConsumer.Covers exampleCommitmentA ∧
    CoversHtlcOutputs exampleWire exampleCommitmentA
```

26. `LnLean.Proofs.Channel.CoverageConsumerTargets.example_full_extension_separation`

```text
exampleFullConsumer.wire = exampleExtensionConsumerA.wire ∧
  exampleFullConsumer.outputs = exampleExtensionConsumerA.outputs ∧
    exampleFullConsumer.source ≠ exampleExtensionConsumerA.source
```

27. `LnLean.Proofs.Channel.CoverageConsumerTargets.example_full_outOfBand_separation`

```text
exampleFullConsumer.wire = exampleOutOfBandConsumerB.wire ∧
  exampleFullConsumer.source ≠ exampleOutOfBandConsumerB.source ∧
    exampleFullConsumer.outputs ≠ exampleOutOfBandConsumerB.outputs
```

28. `LnLean.Proofs.Channel.CoverageConsumerTargets.exampleOutOfBandConsumerB_covers`

```text
exampleOutOfBandConsumerB.Covers exampleCommitmentB ∧
  CoversHtlcOutputs exampleWire exampleCommitmentB
```

29. `LnLean.Proofs.Channel.CoverageConsumerTargets.coverage_consumer_summary`

```text
(∀ f : CommitmentSignedFull, (fullRecordConsumer f).CorrectFor f) ∧
  (¬ ∃ consume : CommitmentSigned → CoverageConsumer,
      ∀ f : CommitmentSignedFull,
        (consume f.toCommitmentSigned).CorrectFor f) ∧
    (¬ ∃ consume : CommitmentSigned → CoverageConsumer,
        ∀ f : CommitmentSignedFull,
          (consume f.toCommitmentSigned).source = .fullRecord f) ∧
      (∀ (ext : ProtocolExtension) (m : CommitmentSigned)
          (f : CommitmentSignedFull) (h : ExtensionConsumerLaw ext m f),
          (extensionConsumer h).CorrectFor f) ∧
        (∃ (m : CommitmentSigned) (ext₁ ext₂ : ProtocolExtension),
          m.htlcSignatures.length = ext₁.rows.length ∧
            m.htlcSignatures.length = ext₂.rows.length ∧
              decodeSource m (.protocolExtension ext₁) ≠
                decodeSource m (.protocolExtension ext₂)) ∧
          (exampleFullConsumer.outputs ≠ [] ∧
            exampleFullConsumer.Covers exampleCommitmentA) ∧
            (exampleFullConsumer.wire = exampleOutOfBandConsumerB.wire ∧
              exampleFullConsumer.source ≠
                exampleOutOfBandConsumerB.source ∧
                  exampleFullConsumer.outputs ≠
                    exampleOutOfBandConsumerB.outputs)
```

The summary's extension conjunct is the consumer-level restatement of
`extension_consumer_determines`; the negative conjuncts are the consumer-level
forms of the existing wave-12 impossibilities.

## 6. Concrete non-vacuous witnesses

`witnessFullA` and `witnessFullB` are the existing counterexample full records:
one offered HTLC, `amount = 1000 msat` versus `2000 msat`, same signature and
same legacy projection. Their covered output lists are:

```text
coverageOfFull witnessFullA = [⟨.local, 1 sat, 100, .offered, 1 sat⟩]
coverageOfFull witnessFullB = [⟨.local, 2 sat, 100, .offered, 2 sat⟩]
```

where the fields are direction, floored `amountSat`, `cltvExpiry`, state, and
`netAmountSat` (the default `amountSat` projection).

The concrete values in the module are:

* `exampleWire = witnessFullA.toCommitmentSigned`, with one
  `HTLC_signature` and no per-HTLC identification data.
* `exampleCommitmentA.htlcs = coverageOfFull witnessFullA` and
  `exampleCommitmentB.htlcs = coverageOfFull witnessFullB`.
* `exampleFullConsumer` uses `.fullRecord witnessFullA` and is exact for
  `witnessFullA`.
* `exampleOutOfBandConsumerB` uses `.outOfBand` with
  `witnessFullB.htlcEntries` and origin `.localSigner` over the **same**
  `exampleWire`; it is exact for `witnessFullB` because the two legacy
  projections are equal.
* `exampleExtensionConsumerA` uses `.protocolExtension
  (extensionOfFull witnessFullA)` over the **same** wire and is exact for
  `witnessFullA`.

Closed facts include:

```text
exampleFullConsumer.outputs ≠ []
exampleFullConsumer.Covers exampleCommitmentA
CoversHtlcOutputs exampleWire exampleCommitmentA
exampleFullConsumer.wire = exampleOutOfBandConsumerB.wire
exampleFullConsumer.source ≠ exampleOutOfBandConsumerB.source
exampleFullConsumer.outputs ≠ exampleOutOfBandConsumerB.outputs
exampleFullConsumer.wire = exampleExtensionConsumerA.wire
exampleFullConsumer.outputs = exampleExtensionConsumerA.outputs
exampleFullConsumer.source ≠ exampleExtensionConsumerA.source
```

Thus the consumer model is non-vacuous, and the examples exercise all three
source constructors.

## 7. Validation

### 7.1 Scoped build

Command (pinned toolchain and lock, run from
`/home/ubuntu/ln-lean-repair`):

```sh
export PATH=/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Proofs.Channel.CoverageConsumerTargets
```

Result:

```text
Build completed successfully (54 jobs).
```

The only warnings in the scoped build come from the pre-existing imported
`LnLean/Bitcoin/Sighash.lean` `if_neg`-family deprecation notices; there were
no errors or warnings from `CoverageConsumerTargets.lean`.

### 7.2 Forbidden-token scan

```sh
grep -nE '\b(sorry|admit|axiom|native_decide|unsafe)\b|implemented_by' \
  LnLean/Proofs/Channel/CoverageConsumerTargets.lean
```

Result: no matches. The module uses `set_option autoImplicit false` and the
exact namespace
`LnLean.Proofs.Channel.CoverageConsumerTargets`.

### 7.3 Axiom / constructivity audit

`#print axioms` was run for all 29 public theorems in a temporary file outside
the repository. No theorem depends on `Classical.choice` or on any axiom beyond
`propext` and `Quot.sound`. Specifically:

* no axioms: `extensionConsumerLaw_iff`, `extensionConsumerLaw_fields`,
  `rowBinds_iff`, `fullRecordSource_ne_outOfBandSource`,
  `fullRecordSource_ne_extensionSource`, `outOfBandSource_ne_extensionSource`;
* `propext` only: the remaining correctness and separation theorems except the
  six theorems below;
* `propext`, `Quot.sound`: `CoverageConsumer.coversHtlcOutputs`,
  `fullRecordConsumer_covers`, `extensionConsumer_covers`,
  `exampleFullConsumer_covers`, `exampleOutOfBandConsumerB_covers`, and
  `coverage_consumer_summary`.

No nonconstructive existence is used: every existential theorem
(`extension_rowCount_not_determining`) is proved with explicit concrete
witnesses.

## 8. Catalog-target recommendation for LN-PR-004

**Recommendation:** retarget the `LN-PR-004` model-level obligation to this
module's `coverage_consumer_summary`, with
`fullRecordConsumer_correct`, `no_wire_determined_consumer`,
`extension_consumer_determines`, `extension_rowCount_not_determining`, and
`exampleFullConsumer_covers` as the named supporting theorems.

The recommended catalog reading is:

> A `commitment_signed` consumer is exact when it is paired with a
> full-record/out-of-band coverage source (`fullRecordConsumer_correct`). The
> legacy wire alone cannot determine such a consumer
> (`no_wire_determined_consumer`,
> `no_wire_determined_fullRecord_consumer`). A protocol extension plus the wire
> determines the consumer exactly under the explicit `ExtensionConsumerLaw`
> (`wire_eq`, `rowCount_eq`, `ExtensionBinds`); the wire row-count check alone
> does not (`extension_rowCount_not_determining`). Production coverage therefore
> still requires an out-of-band/full-record source or a protocol change.

**Closure status:** the model-level consumer contract can be treated as closed
for `LN-PR-004` in the same conditional sense as the existing source/witness
lanes: the full-record positive, the wire impossibility, the conditional
extension law, source separation, and concrete non-vacuity are all mechanized.
The **production** claim must remain open: this module does not provide a
production decoder, does not encode or negotiate the extension on the wire, and
does not claim BOLT 2 was changed. The residual requirement is exactly a
production out-of-band/full-record source with an explicit binding law, or a
protocol change carrying the missing per-HTLC rows.

## 9. Honest boundary

* No wire encoding is defined or changed.
* No production decoder is claimed; `decodeSource` is the existing model-level
  decoder, and `CoverageConsumer` is a model-level certificate.
* `ExtensionConsumerLaw` is a specification and a hypothesis, not a received
  message property. `extension_rowCount_not_determining` shows why the wire
  cannot supply it.
* The binding law is field agreement, not cryptographic authentication. The
  existing origin tag remains data, not a signature.
* The concrete witnesses use the existing 1000/2000-msat counterexample pair;
  their coverage difference (1 sat versus 2 sat) is kernel-checked.
