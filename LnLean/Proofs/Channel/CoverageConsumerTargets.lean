/-
# Consumer contracts for `commitment_signed` coverage (`LN-PR-004`)

BOLT 2's `commitment_signed` (type 132) carries a channel id, one commitment
signature, and one `HTLC_signature` per untrimmed HTLC output.  It carries no
commitment number, no digest, no fee, and no per-HTLC identification data, so
the legacy record cannot determine what it covers
(`LnLean.Proofs.ProtocolCoverageTargets.no_wire_determined_coverage`,
`no_coverage_htlc_selector`, and
`LnLean.Proofs.Channel.PreimageCoverageTargets.legacy_projection_not_determine_htlc_coverage`).

Wave 10 (`LnLean.Proofs.Channel.CoverageWitnessTargets`) characterized the
missing data as a per-HTLC `CoverageWitness`.  The existing source module
(`LnLean.Proofs.Channel.CoverageSourceTargets`) made the *source* explicit:
`CoverageSource` is a full signer record, a tagged out-of-band witness, or a
protocol extension, and `decodeSource` is the canonical decoder from a legacy
wire record plus a source to the covered output list.

This module adds the **consumer-facing contract** layer.  It deliberately
*composes with* `CoverageSource` rather than replacing it:

* `CoverageConsumer` is a concrete consumption of a legacy wire record and an
  existing `CoverageSource`, together with the decoded output list and a proof
  that the decoder returns it.
* `CoverageConsumer.CorrectFor` says the consumer's wire is the projection of
  a full record and its outputs are exactly that record's coverage.
* `CoverageConsumer.Covers` transfers an accepted consumer to a concrete
  `Commitment`, yielding the existing `CoversHtlcOutputs` predicate.

The main results are:

* `fullRecordConsumer_correct` — the full-record source yields a consumer that
  is exact for every produced full record, unconditionally.
* `no_wire_determined_consumer` — no function from the legacy wire alone
  produces a consumer that is exact for every full record.
* `no_wire_determined_fullRecord_consumer` — no wire function even returns the
  full-record source for every full record.
* `extension_consumer_determines` — protocol extension plus wire determines a
  consumer only under the explicit `ExtensionConsumerLaw`, whose fields are
  `wire_eq`, `rowCount_eq`, and `ExtensionBinds` (channel id plus the
  field-by-field `RowsBind` law).
* `extension_rowCount_not_determining` — the wire row-count check alone does
  not select the extension: two extension sources match the same wire count
  and decode differently.
* `example_full_outOfBand_separation` and
  `example_full_extension_separation` — concrete consumers over the *same*
  wire with different sources and, respectively, different and equal output
  lists.
* `exampleFullConsumer_covers` — a closed, non-vacuous consumer whose outputs
  are nonempty and which covers the concrete commitment output list.

## Honest boundary

`CoverageConsumer` is a model-level contract.  It does not construct a
production decoder, does not add a wire field, and does not claim that BOLT 2
was changed.  Because the legacy `commitment_signed` has no per-HTLC coverage
data, production coverage still requires an out-of-band/full-record source
whose binding is supplied explicitly, or a protocol change that carries the
missing rows.  The negative results below are not weakened.

Anchors: BOLT 2 §"Committing Updates So Far" (`commitment_signed`, type 132),
BOLT 2 §"Updating the Commitment"; BOLT 3 §"Commitment Transaction" /
§"HTLC Outputs"; `LnLean/Protocol/Messages.lean` (`CommitmentSigned`,
`SignedHtlcEntry`, `CommitmentSignedFull`), `LnLean/Channel/Types.lean`
(`Commitment`, `CommitmentHTLCOutput`),
`LnLean/Proofs/Channel/CoverageWitnessTargets.lean`,
`LnLean/Proofs/Channel/CoverageSourceTargets.lean`, and
`LnLean/Proofs/ProtocolCoverageTargets.lean`.
-/

import LnLean.Proofs.Channel.CoverageSourceTargets

namespace LnLean.Proofs.Channel.CoverageConsumerTargets

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open LnLean
open LnLean.Channel
open LnLean.Protocol
open LnLean.Proofs
open LnLean.Proofs.ProtocolCoverageTargets
open LnLean.Proofs.Channel.CoverageWitnessTargets
open LnLean.Proofs.Channel.CoverageSourceTargets

/-! ## 1. The consumer contract

A consumer is not a new source: it *uses* an existing `CoverageSource` against
a legacy wire record.  The `decodes` field records the accepted decode, so a
consumer value is a certificate, not a unchecked pair.  The decoded outputs are
kept explicit because a `Commitment` also carries balance fields that are not
part of coverage. -/

/-- A consumer-facing coverage contract.  `wire` is the legacy
`commitment_signed`; `source` is one of the existing `CoverageSource`
constructors; `outputs` is the exact covered commitment-output list; and
`decodes` is the proof that the canonical source decoder returns `outputs`. -/
structure CoverageConsumer where
  /-- The legacy `commitment_signed` record being consumed. -/
  wire : CommitmentSigned
  /-- The existing coverage source composed with the wire. -/
  source : CoverageSource
  /-- The covered commitment-output list the consumer commits to. -/
  outputs : List CommitmentHTLCOutput
  /-- The decoder accepts this wire/source pair and returns `outputs`. -/
  decodes : decodeSource wire source = some outputs

namespace CoverageConsumer

/-- The consumer is exact for a full record when it consumes that record's
legacy projection and decodes to exactly the record's coverage. -/
def CorrectFor (k : CoverageConsumer) (f : CommitmentSignedFull) : Prop :=
  k.wire = f.toCommitmentSigned ∧ k.outputs = coverageOfFull f

/-- The consumer covers a concrete commitment when its decoded outputs are
exactly that commitment's HTLC output list. -/
def Covers (k : CoverageConsumer) (c : Commitment) : Prop :=
  k.outputs = c.htlcs

/-- An accepted consumer transfers to the existing wire-coverage predicate.
This is the bridge from the consumer contract to `CoversHtlcOutputs`. -/
theorem coversHtlcOutputs {k : CoverageConsumer} {c : Commitment}
    (h : k.Covers c) : CoversHtlcOutputs k.wire c :=
  decodeSource_covers k.decodes h.symm

end CoverageConsumer

/-! ## 2. The full-record source gives an exact consumer

The full-record source is unconditional: every `CommitmentSignedFull` has a
consumer whose wire is the record's own legacy projection and whose outputs are
exactly the record's covered HTLC output list. -/

/-- The consumer built from the full-record source of a produced record. -/
def fullRecordConsumer (f : CommitmentSignedFull) : CoverageConsumer where
  wire := f.toCommitmentSigned
  source := .fullRecord f
  outputs := coverageOfFull f
  decodes := decodeSource_fullRecord_exact f

/-- The full-record consumer uses the full-record source. -/
theorem fullRecordConsumer_source (f : CommitmentSignedFull) :
    (fullRecordConsumer f).source = .fullRecord f := rfl

/-- The full-record consumer's outputs are exactly the record's coverage. -/
theorem fullRecordConsumer_outputs (f : CommitmentSignedFull) :
    (fullRecordConsumer f).outputs = coverageOfFull f := rfl

/-- **The full-record source yields an exact consumer for every produced
record.**  Both the wire equality and the exact output equality are
unconditional. -/
theorem fullRecordConsumer_correct (f : CommitmentSignedFull) :
    (fullRecordConsumer f).CorrectFor f :=
  ⟨rfl, rfl⟩

/-- The full-record consumer covers any commitment whose HTLC list is the
record's exact coverage, hence satisfies the existing wire-coverage
predicate. -/
theorem fullRecordConsumer_covers (f : CommitmentSignedFull) (c : Commitment)
    (hc : c.htlcs = coverageOfFull f) :
    (fullRecordConsumer f).Covers c ∧
      CoversHtlcOutputs f.toCommitmentSigned c :=
  ⟨hc.symm, CoverageConsumer.coversHtlcOutputs
    (k := fullRecordConsumer f) hc.symm⟩

/-- The canonical out-of-band consumer: the same exact outputs, with an
explicit origin tag.  The tag is data; it does not change what is decoded. -/
def outOfBandConsumer (f : CommitmentSignedFull)
    (origin : WitnessOrigin) : CoverageConsumer where
  wire := f.toCommitmentSigned
  source := .outOfBand { entries := f.htlcEntries, origin := origin }
  outputs := coverageOfFull f
  decodes := decodeSource_outOfBand_canonical f origin

/-- The canonical out-of-band consumer is exact for the source record. -/
theorem outOfBandConsumer_correct (f : CommitmentSignedFull)
    (origin : WitnessOrigin) :
    (outOfBandConsumer f origin).CorrectFor f :=
  ⟨rfl, rfl⟩

/-- The out-of-band consumer uses the out-of-band source constructor. -/
theorem outOfBandConsumer_source (f : CommitmentSignedFull)
    (origin : WitnessOrigin) :
    (outOfBandConsumer f origin).source =
      .outOfBand { entries := f.htlcEntries, origin := origin } := rfl

/-! ## 3. The legacy wire alone cannot determine a consumer

The negative is the consumer-level restatement of the wave-12 source
impossibility.  The two concrete full records `witnessFullA` and
`witnessFullB` have the same legacy projection but different coverage, so any
consumer selected from the wire must return two different output lists from the
same wire. -/

/-- **No wire-determined consumer.**  There is no function from the legacy
`commitment_signed` alone that produces a consumer exact for every full
record.  This uses the same `witnessFullA`/`witnessFullB` counterexample as
`no_wire_determined_source`; the consumer's decode certificate does not make
the impossible selection possible. -/
theorem no_wire_determined_consumer :
    ¬ ∃ consume : CommitmentSigned → CoverageConsumer,
        ∀ f : CommitmentSignedFull,
          (consume f.toCommitmentSigned).CorrectFor f := by
  rintro ⟨consume, hconsume⟩
  have hA := hconsume witnessFullA
  have hB := hconsume witnessFullB
  have hsame : consume witnessFullA.toCommitmentSigned =
      consume witnessFullB.toCommitmentSigned := by
    rw [witness_full_same_projection]
  rw [hsame] at hA
  have hcov : coverageOfFull witnessFullA = coverageOfFull witnessFullB :=
    hA.2.symm.trans hB.2
  exact witness_full_coverage_ne hcov

/-- **No wire-determined full-record consumer.**  Even the source identity
`.fullRecord f` cannot be recovered from the wire: the same projection belongs
to two distinct full records whose coverages differ. -/
theorem no_wire_determined_fullRecord_consumer :
    ¬ ∃ consume : CommitmentSigned → CoverageConsumer,
        ∀ f : CommitmentSignedFull,
          (consume f.toCommitmentSigned).source =
            CoverageSource.fullRecord f := by
  rintro ⟨consume, hconsume⟩
  have hA := hconsume witnessFullA
  have hB := hconsume witnessFullB
  have hsame : consume witnessFullA.toCommitmentSigned =
      consume witnessFullB.toCommitmentSigned := by
    rw [witness_full_same_projection]
  rw [hsame] at hA
  have hsrc : CoverageSource.fullRecord witnessFullA =
      CoverageSource.fullRecord witnessFullB :=
    hA.symm.trans hB
  have hAB : witnessFullA = witnessFullB :=
    CoverageSource.fullRecord.inj hsrc
  exact witness_full_coverage_ne (congrArg coverageOfFull hAB)

/-! ## 4. Protocol extension plus wire: the explicit binding law

The extension source is usable only when the extension actually describes the
full record.  `ExtensionConsumerLaw` makes that requirement explicit.  Its
third field is the wave-12 `ExtensionBinds` law, which is a channel-id equality
plus the per-row `RowsBind` agreement on amount, `cltv_expiry`, payment hash,
direction, lifecycle state, and script-family tag. -/

/-- **The exact protocol-extension consumer law.**  A legacy wire `m`, an
extension `ext`, and a full record `f` determine a consumer when

1. `m` is the legacy projection of `f`;
2. the wire HTLC-signature count equals the extension row count; and
3. `ExtensionBinds ext f` holds (channel id plus row-by-row field binding).

Condition (3) is not derivable from (1) and (2): see
`extension_rowCount_not_determining`. -/
structure ExtensionConsumerLaw (ext : ProtocolExtension)
    (m : CommitmentSigned) (f : CommitmentSignedFull) : Prop where
  /-- The wire is the full record's legacy projection. -/
  wire_eq : m = f.toCommitmentSigned
  /-- The only wire-side check: one signature per extension row. -/
  rowCount_eq : m.htlcSignatures.length = ext.rows.length
  /-- The explicit field-by-field binding of the extension to the record. -/
  binds : ExtensionBinds ext f

/-- The law is exactly the conjunction of its three fields. -/
theorem extensionConsumerLaw_iff (ext : ProtocolExtension)
    (m : CommitmentSigned) (f : CommitmentSignedFull) :
    ExtensionConsumerLaw ext m f ↔
      m = f.toCommitmentSigned ∧
        m.htlcSignatures.length = ext.rows.length ∧
          ExtensionBinds ext f :=
  ⟨fun h => ⟨h.wire_eq, h.rowCount_eq, h.binds⟩,
    fun h => ⟨h.1, h.2.1, h.2.2⟩⟩

/-- The law unpacked to the extension's channel id and the row list law. -/
theorem extensionConsumerLaw_fields {ext : ProtocolExtension}
    {m : CommitmentSigned} {f : CommitmentSignedFull}
    (h : ExtensionConsumerLaw ext m f) :
    m = f.toCommitmentSigned ∧
      m.htlcSignatures.length = ext.rows.length ∧
        ext.channelId = f.channelId ∧
          RowsBind ext.rows f.htlcEntries :=
  ⟨h.wire_eq, h.rowCount_eq, h.binds.channelId_eq, h.binds.rows_bind⟩

/-- The per-row binding law, expanded to its six field equations.  This is the
exact content of the third field of `ExtensionConsumerLaw`. -/
theorem rowBinds_iff (r : HtlcCoverageFields) (e : SignedHtlcEntry) :
    RowBinds r e ↔
      r.amount = e.amount ∧
        r.cltvExpiry = e.cltvExpiry ∧
          r.paymentHash = e.paymentHash ∧
            r.direction = e.direction ∧
              r.htlcState = e.htlcState ∧
                r.scriptTag = HtlcScriptTag.ofState e.htlcState :=
  ⟨fun h => ⟨h.amount_eq, h.cltv_eq, h.hash_eq, h.direction_eq,
      h.state_eq, h.tag_eq⟩,
    fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
      h.2.2.2.2.2⟩⟩

/-- The consumer determined by an explicit extension binding law. -/
def extensionConsumer {ext : ProtocolExtension} {m : CommitmentSigned}
    {f : CommitmentSignedFull} (h : ExtensionConsumerLaw ext m f) :
    CoverageConsumer where
  wire := m
  source := .protocolExtension ext
  outputs := coverageOfFull f
  decodes :=
    extension_plus_wire_determines_coverage h.wire_eq h.rowCount_eq h.binds

/-- The extension consumer uses the protocol-extension source. -/
theorem extensionConsumer_source {ext : ProtocolExtension}
    {m : CommitmentSigned} {f : CommitmentSignedFull}
    (h : ExtensionConsumerLaw ext m f) :
    (extensionConsumer h).source = .protocolExtension ext := rfl

/-- The extension consumer's outputs are the full record's exact coverage. -/
theorem extensionConsumer_outputs {ext : ProtocolExtension}
    {m : CommitmentSigned} {f : CommitmentSignedFull}
    (h : ExtensionConsumerLaw ext m f) :
    (extensionConsumer h).outputs = coverageOfFull f := rfl

/-- **Protocol-extension plus wire determines the consumer under the explicit
binding law.**  The law is not assumed by the decoder: it is a hypothesis that
supplies the missing field agreement. -/
theorem extension_consumer_determines {ext : ProtocolExtension}
    {m : CommitmentSigned} {f : CommitmentSignedFull}
    (h : ExtensionConsumerLaw ext m f) :
    (extensionConsumer h).source = .protocolExtension ext ∧
      (extensionConsumer h).outputs = coverageOfFull f ∧
        (extensionConsumer h).CorrectFor f :=
  ⟨rfl, rfl, ⟨h.wire_eq, rfl⟩⟩

/-- The extension consumer covers a commitment whose HTLC list is the full
record's coverage. -/
theorem extensionConsumer_covers {ext : ProtocolExtension}
    {m : CommitmentSigned} {f : CommitmentSignedFull}
    (h : ExtensionConsumerLaw ext m f) (c : Commitment)
    (hc : c.htlcs = coverageOfFull f) :
    (extensionConsumer h).Covers c ∧ CoversHtlcOutputs m c :=
  ⟨hc.symm, CoverageConsumer.coversHtlcOutputs
    (k := extensionConsumer h) hc.symm⟩

/-- The binding law's field agreement is sufficient to identify the
extension's own coverage with the record's coverage. -/
theorem extensionConsumerLaw_coverage_eq {ext : ProtocolExtension}
    {m : CommitmentSigned} {f : CommitmentSignedFull}
    (h : ExtensionConsumerLaw ext m f) :
    ext.toCoverage = coverageOfFull f :=
  h.binds.coverage_eq

/-- **The row-count check alone does not determine the extension.**  Two
different extension sources match the same legacy wire's HTLC-signature count
and decode to different output lists.  The wire can only count; it cannot
supply the field binding. -/
theorem extension_rowCount_not_determining :
    ∃ (m : CommitmentSigned) (ext₁ ext₂ : ProtocolExtension),
      m.htlcSignatures.length = ext₁.rows.length ∧
        m.htlcSignatures.length = ext₂.rows.length ∧
          decodeSource m (.protocolExtension ext₁) ≠
            decodeSource m (.protocolExtension ext₂) := by
  refine ⟨witnessFullA.toCommitmentSigned,
    extensionOfFull witnessFullA, extensionOfFull witnessFullB, ?_, ?_, ?_⟩
  · simp [extensionOfFull, witnessFullA, CommitmentSignedFull.toCommitmentSigned]
  · simp [extensionOfFull, witnessFullB, witnessFullA,
      CommitmentSignedFull.toCommitmentSigned]
  · rw [decodeSource_extensionOfFull_canonical witnessFullA]
    have hB : decodeSource witnessFullA.toCommitmentSigned
        (.protocolExtension (extensionOfFull witnessFullB)) =
        some (coverageOfFull witnessFullB) := by
      rw [witness_full_same_projection]
      exact decodeSource_extensionOfFull_canonical witnessFullB
    rw [hB]
    intro h
    exact witness_full_coverage_ne (Option.some.inj h)

/-! ## 5. Source separation and concrete non-vacuous consumers

The three source constructors are pairwise distinct, and concrete consumers
over the same wire can use different sources.  The first pair has the same
outputs but distinct source identity; the second pair has different outputs
and is exact for two different full records with the same wire. -/

/-- `fullRecord` and `outOfBand` are distinct source constructors. -/
theorem fullRecordSource_ne_outOfBandSource (f : CommitmentSignedFull)
    (o : OutOfBandWitness) :
    CoverageSource.fullRecord f ≠ CoverageSource.outOfBand o := by
  intro h
  cases h

/-- `fullRecord` and `protocolExtension` are distinct source constructors. -/
theorem fullRecordSource_ne_extensionSource (f : CommitmentSignedFull)
    (ext : ProtocolExtension) :
    CoverageSource.fullRecord f ≠ CoverageSource.protocolExtension ext := by
  intro h
  cases h

/-- `outOfBand` and `protocolExtension` are distinct source constructors. -/
theorem outOfBandSource_ne_extensionSource (o : OutOfBandWitness)
    (ext : ProtocolExtension) :
    CoverageSource.outOfBand o ≠ CoverageSource.protocolExtension ext := by
  intro h
  cases h

/-- The concrete wire used by all example consumers: the legacy projection of
the first counterexample record. -/
def exampleWire : CommitmentSigned :=
  witnessFullA.toCommitmentSigned

/-- The concrete commitment whose HTLC list is the first record's coverage. -/
def exampleCommitmentA : Commitment where
  holder := .local
  commitmentNumber := 0
  fundingValueSat := 1000
  toLocalSat := 1000
  toRemoteSat := 0
  htlcs := coverageOfFull witnessFullA
  feeSat := 0
  contestDelay := 144
  anchorOutputs := false
  trimmedTotalSat := 0

/-- The concrete commitment whose HTLC list is the second record's coverage. -/
def exampleCommitmentB : Commitment where
  holder := .local
  commitmentNumber := 0
  fundingValueSat := 2000
  toLocalSat := 2000
  toRemoteSat := 0
  htlcs := coverageOfFull witnessFullB
  feeSat := 0
  contestDelay := 144
  anchorOutputs := false
  trimmedTotalSat := 0

/-- A concrete full-record consumer: one HTLC, 1000 msat → 1 sat. -/
def exampleFullConsumer : CoverageConsumer :=
  fullRecordConsumer witnessFullA

/-- The concrete out-of-band witness for the second record. -/
def exampleOutOfBandWitnessB : OutOfBandWitness where
  entries := witnessFullB.htlcEntries
  origin := .localSigner

/-- A concrete out-of-band consumer over the *same* wire, carrying the second
record's entries.  It is exact for `witnessFullB`, whose legacy projection is
the same wire. -/
def exampleOutOfBandConsumerB : CoverageConsumer where
  wire := exampleWire
  source := CoverageSource.outOfBand exampleOutOfBandWitnessB
  outputs := coverageOfFull witnessFullB
  decodes := by
    have hw : wireCompatible exampleWire
        (witnessOfFull witnessFullB) := by
      rw [exampleWire, witness_full_same_projection]
      exact wireCompatible_toCommitmentSigned witnessFullB
    have h := decodeSource_outOfBand_of_wireCompatible
      (m := exampleWire) (o := exampleOutOfBandWitnessB) hw
    simpa [coverageOfFull, OutOfBandWitness.toWitness,
      exampleOutOfBandWitnessB] using h

/-- A concrete extension consumer over the same wire, using the canonical
extension of the first record and the explicit binding law. -/
def exampleExtensionConsumerA : CoverageConsumer :=
  extensionConsumer
    (ext := extensionOfFull witnessFullA)
    (m := exampleWire)
    (f := witnessFullA)
    { wire_eq := rfl
      rowCount_eq := by
        simp [exampleWire, extensionOfFull, witnessFullA,
          CommitmentSignedFull.toCommitmentSigned]
      binds := extensionOfFull_binds witnessFullA }
/-- The concrete full-record consumer is exact for the first record. -/
theorem exampleFullConsumer_correct :
    exampleFullConsumer.CorrectFor witnessFullA :=
  fullRecordConsumer_correct witnessFullA

/-- The concrete out-of-band consumer is exact for the second record, even
though its wire is the first record's projection: the projections are equal. -/
theorem exampleOutOfBandConsumerB_correct :
    exampleOutOfBandConsumerB.CorrectFor witnessFullB :=
  ⟨witness_full_same_projection, rfl⟩

/-- The concrete extension consumer is exact for the first record. -/
theorem exampleExtensionConsumerA_correct :
    exampleExtensionConsumerA.CorrectFor witnessFullA :=
  ⟨rfl, rfl⟩

/-- **The concrete full-record consumer is non-vacuous and covers the concrete
commitment exactly.**  No hypothesis is assumed: the outputs are nonempty and
the existing wire-coverage predicate holds. -/
theorem exampleFullConsumer_covers :
    exampleFullConsumer.outputs ≠ [] ∧
      exampleFullConsumer.Covers exampleCommitmentA ∧
        CoversHtlcOutputs exampleWire exampleCommitmentA := by
  refine ⟨?_, ?_, ?_⟩
  · simp [exampleFullConsumer, fullRecordConsumer, coverageOfFull,
      witnessFullA]
  · rfl
  · exact CoverageConsumer.coversHtlcOutputs
      (k := exampleFullConsumer) (c := exampleCommitmentA) rfl

/-- **Source separation with equal outputs.**  The full-record and canonical
extension consumers consume the same wire and decode to the same output list,
but their source constructors differ.  Coverage is therefore not source
identity. -/
theorem example_full_extension_separation :
    exampleFullConsumer.wire = exampleExtensionConsumerA.wire ∧
      exampleFullConsumer.outputs = exampleExtensionConsumerA.outputs ∧
        exampleFullConsumer.source ≠ exampleExtensionConsumerA.source := by
  refine ⟨rfl, rfl, ?_⟩
  intro h
  cases h

/-- **Source separation with different outputs.**  Two consumers over the same
wire use different sources and decode to different output lists.  This is the
consumer-level form of the residual wire boundary: the wire cannot select the
source. -/
theorem example_full_outOfBand_separation :
    exampleFullConsumer.wire = exampleOutOfBandConsumerB.wire ∧
      exampleFullConsumer.source ≠ exampleOutOfBandConsumerB.source ∧
        exampleFullConsumer.outputs ≠ exampleOutOfBandConsumerB.outputs := by
  refine ⟨rfl, ?_, ?_⟩
  · intro h
    cases h
  · exact witness_full_coverage_ne

/-- The concrete out-of-band consumer covers the second concrete commitment
exactly, using the same wire as the first consumer. -/
theorem exampleOutOfBandConsumerB_covers :
    exampleOutOfBandConsumerB.Covers exampleCommitmentB ∧
      CoversHtlcOutputs exampleWire exampleCommitmentB :=
  ⟨rfl, CoverageConsumer.coversHtlcOutputs
    (k := exampleOutOfBandConsumerB) (c := exampleCommitmentB) rfl⟩

/-! ## 6. Summary -/

/-- Bundled faithful reading of the consumer-contract lane (LN-PR-004).

1. The full-record source yields an exact consumer for every produced record.
2. No function from the legacy wire alone produces a consumer exact for every
   full record, and none recovers the full-record source.
3. Protocol extension plus wire determines a consumer exactly under the
   explicit `ExtensionConsumerLaw` (`wire_eq`, `rowCount_eq`, `ExtensionBinds`).
4. The wire row-count check alone does not determine the extension.
5. The source constructors are separated, and the concrete one-HTLC consumer is
   non-vacuous and covers its concrete commitment.
6. The three source constructors are pairwise distinct.

The positive extension conjunct is conditional on the binding law.  This module
does not claim a production decoder or a wire change. -/
theorem coverage_consumer_summary :
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
                        exampleOutOfBandConsumerB.outputs) :=
  ⟨fullRecordConsumer_correct,
    no_wire_determined_consumer,
    no_wire_determined_fullRecord_consumer,
    fun _ext _m _f h => extension_consumer_determines h |>.2.2,
    extension_rowCount_not_determining,
    ⟨exampleFullConsumer_covers.1, exampleFullConsumer_covers.2.1⟩,
    example_full_outOfBand_separation⟩

end LnLean.Proofs.Channel.CoverageConsumerTargets
