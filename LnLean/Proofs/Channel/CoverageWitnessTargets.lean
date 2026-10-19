/-
# The `commitment_signed` coverage witness (`PR-02`)

BOLT 2's `commitment_signed` (type 132) carries only `channel_id`, one
commitment-transaction `signature`, and one `HTLC_signature` per untrimmed HTLC
output (`LnLean.Protocol.Messages.CommitmentSigned`).  It carries no commitment
number, no commitment digest, no fee, and no per-HTLC identification data, so
the legacy record cannot determine what it covers
(`LnLean.Proofs.ProtocolCoverageTargets.no_wire_determined_coverage`,
`no_coverage_htlc_selector`, and
`LnLean.Proofs.Channel.PreimageCoverageTargets.legacy_projection_not_determine_htlc_coverage`).

This module characterizes exactly what is missing as a **witness**:

* `CoverageWitness` carries the per-HTLC rows (`SignedHtlcEntry`) that the
  legacy wire record omits.
* `witnessOfFull` extracts the canonical witness from a
  `CommitmentSignedFull`, and `decodeCoverage` decodes a legacy record plus a
  witness to the covered `CommitmentHTLCOutput` list.  The decoder checks the
  only wire-derivable consistency condition: one HTLC signature per witness
  row.  `decodeCoverage_canonical` proves the canonical witness decodes to the
  full record's exact coverage; `decodeCoverage_covers` transfers the result to
  `CoversHtlcOutputs`.
* `no_legacy_only_coverage_decoder` restates the negative with the decoder
  types: no function of `CommitmentSigned` alone recovers coverage for every
  full record.
* `amount_is_necessary` / `witness_full_same_reduced_witness` show the amount
  row is load-bearing: two records with the same amount-erased witness have
  different coverage.  `toCommitmentHtlcOutput_eq_iff` states the exact
  minimal determining tuple (direction, floored amount, expiry, lifecycle
  state); `htlcId`, `paymentHash`, `signedDataDigest`, and `signature` do not
  affect the output projection.
* `wire_admits_distinct_coverage_witnesses` records the residual boundary: the
  legacy wire is compatible with two witnesses that decode differently, so the
  wire cannot select the witness.  A production decoder therefore needs an
  out-of-band/full-record source (or a protocol change that carries the
  witness); this module does **not** claim the legacy wire is sufficient.

Anchors: BOLT 2 §"Committing Updates So Far" (`commitment_signed` type 132),
BOLT 3 §"Commitment Transaction" / §"HTLC Outputs";
`LnLean/Protocol/Messages.lean` (`CommitmentSigned`, `SignedHtlcEntry`,
`CommitmentSignedFull`), `LnLean/Channel/Types.lean` (`CommitmentHTLCOutput`,
`Commitment`), `LnLean/Proofs/ProtocolWireTargets.lean`,
`LnLean/Proofs/ProtocolCoverageTargets.lean`, and
`LnLean/Proofs/Channel/PreimageCoverageTargets.lean`.
-/

import LnLean.Proofs.Channel.PreimageCoverageTargets

namespace LnLean.Proofs.Channel.CoverageWitnessTargets

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open LnLean
open LnLean.Protocol
open LnLean.Channel
open LnLean.Proofs
open LnLean.Proofs.ProtocolCoverageTargets

/-! ## 1. The witness and the canonical extraction -/

/-- The data that `commitment_signed` omits and that a coverage decoder needs
alongside the legacy record: one signed entry per HTLC output, in commitment
order.  The entries are precisely the `SignedHtlcEntry` rows of a
`CommitmentSignedFull`; no commitment number, fee, or digest is included,
because those are not needed to recover the covered output list. -/
structure CoverageWitness where
  /-- One signed HTLC row per untrimmed HTLC output, in commitment order. -/
  entries : List SignedHtlcEntry
deriving Repr, BEq

/-- The canonical witness of a full record: forget everything except the
per-HTLC rows. -/
def witnessOfFull (f : CommitmentSignedFull) : CoverageWitness :=
  { entries := f.htlcEntries }

@[simp] theorem witnessOfFull_entries (f : CommitmentSignedFull) :
    (witnessOfFull f).entries = f.htlcEntries := rfl

/-- The exact coverage of a full record: the commitment outputs its signed
entries describe.  BOLT 3 floors millisatoshis to satoshis in
`SignedHtlcEntry.toCommitmentHtlcOutput`, so this is the output list the
commitment transaction emits. -/
def coverageOfFull (f : CommitmentSignedFull) : List CommitmentHTLCOutput :=
  f.htlcEntries.map SignedHtlcEntry.toCommitmentHtlcOutput

/-- A witness is wire-compatible when its per-entry signatures are exactly the
legacy `HTLC_signature` list.  This is the only part of a witness that the
legacy record can cross-check; the identification and amount data have no wire
image. -/
def wireCompatible (m : CommitmentSigned) (w : CoverageWitness) : Prop :=
  m.htlcSignatures = w.entries.map (fun e => e.signature)

/-- The canonical witness is wire-compatible with the legacy projection. -/
theorem wireCompatible_toCommitmentSigned (f : CommitmentSignedFull) :
    wireCompatible f.toCommitmentSigned (witnessOfFull f) := rfl

/-- Wire compatibility fixes the number of rows: one signature per entry. -/
theorem wireCompatible_length {m : CommitmentSigned} {w : CoverageWitness}
    (h : wireCompatible m w) :
    m.htlcSignatures.length = w.entries.length := by
  rw [h]
  simp

/-! ## 2. The constructive decoder -/

/-- Decode the covered HTLC outputs from the legacy record and a witness.

The wire contributes the only consistency check it can: the number of
`HTLC_signature` entries must match the number of witness rows.  The per-HTLC
identification and amount data come from the witness, never from the wire. -/
def decodeCoverage (m : CommitmentSigned) (w : CoverageWitness) :
    Option (List CommitmentHTLCOutput) :=
  if m.htlcSignatures.length = w.entries.length then
    some (w.entries.map SignedHtlcEntry.toCommitmentHtlcOutput)
  else
    none

/-- **Decoder correctness on the canonical witness.**  For every full record,
the legacy projection plus the extracted witness decodes to exactly the full
record's covered HTLC output list. -/
theorem decodeCoverage_canonical (f : CommitmentSignedFull) :
    decodeCoverage f.toCommitmentSigned (witnessOfFull f) =
      some (coverageOfFull f) := by
  unfold decodeCoverage coverageOfFull witnessOfFull
    CommitmentSignedFull.toCommitmentSigned
  simp

/-- Exact characterization of the decoder: it succeeds exactly on
length-compatible witnesses and returns their output projection. -/
theorem decodeCoverage_eq_some_iff (m : CommitmentSigned)
    (w : CoverageWitness) (outs : List CommitmentHTLCOutput) :
    decodeCoverage m w = some outs ↔
      m.htlcSignatures.length = w.entries.length ∧
        w.entries.map SignedHtlcEntry.toCommitmentHtlcOutput = outs := by
  unfold decodeCoverage
  by_cases h : m.htlcSignatures.length = w.entries.length
  · simp [h]
  · simp [h]

/-- A successful decode implies the legacy wire has one signature per decoded
output.  This is the wire-side soundness condition. -/
theorem decodeCoverage_sound {m : CommitmentSigned} {w : CoverageWitness}
    {outs : List CommitmentHTLCOutput}
    (h : decodeCoverage m w = some outs) :
    m.htlcSignatures.length = outs.length := by
  obtain ⟨hlen, houts⟩ := (decodeCoverage_eq_some_iff m w outs).1 h
  rw [← houts, List.length_map, hlen]

/-- A wire-compatible witness always decodes; compatibility is stronger than
the length guard. -/
theorem decodeCoverage_of_wireCompatible {m : CommitmentSigned}
    {w : CoverageWitness} (h : wireCompatible m w) :
    decodeCoverage m w =
      some (w.entries.map SignedHtlcEntry.toCommitmentHtlcOutput) := by
  unfold decodeCoverage
  simp [wireCompatible_length h]

/-- **Decoded coverage is the existing wire coverage predicate.**  If the
decoder returns `outs` and a commitment's HTLC list is exactly `outs`, then the
legacy record covers that commitment in the sense of `CoversHtlcOutputs`. -/
theorem decodeCoverage_covers {m : CommitmentSigned} {w : CoverageWitness}
    {outs : List CommitmentHTLCOutput} {c : Commitment}
    (h : decodeCoverage m w = some outs) (hc : c.htlcs = outs) :
    CoversHtlcOutputs m c := by
  unfold CoversHtlcOutputs
  rw [Commitment.htlcOutputCount_commitmentOutputs, hc]
  exact decodeCoverage_sound h

/-! ## 3. Legacy-only impossibility with the decoder types -/

/-- A concrete HTLC signature shared by the counterexample records. -/
def witnessSig : EcdsaSig := ⟨ByteArray.empty⟩

/-- The counterexample entry: one local offered HTLC of 1000 msat. -/
def witnessEntryA : SignedHtlcEntry :=
  { htlcId := 1
    amount := ⟨1000⟩
    paymentHash := ⟨ByteArray.empty⟩
    direction := .local
    htlcState := .offered
    cltvExpiry := 100
    signedDataDigest := ByteArray.empty
    signature := witnessSig }

/-- The same entry with only the amount changed to 2000 msat. -/
def witnessEntryB : SignedHtlcEntry :=
  { witnessEntryA with amount := ⟨2000⟩ }

/-- Full record A. -/
def witnessFullA : CommitmentSignedFull :=
  { channelId := ChannelId.zero
    commitmentNumber := 0
    feePaid := ⟨0⟩
    commitmentDigest := ByteArray.empty
    commitmentSignature := witnessSig
    htlcEntries := [witnessEntryA] }

/-- Full record B. -/
def witnessFullB : CommitmentSignedFull :=
  { witnessFullA with htlcEntries := [witnessEntryB] }

/-- The two full records have the same legacy `commitment_signed` projection:
same channel id, same commitment signature, same HTLC-signature list. -/
theorem witness_full_same_projection :
    witnessFullA.toCommitmentSigned = witnessFullB.toCommitmentSigned := by
  simp [witnessFullA, witnessFullB, witnessEntryA, witnessEntryB,
    CommitmentSignedFull.toCommitmentSigned]

/-- Their coverage differs: 1 sat versus 2 sat after the BOLT 3 floor. -/
theorem witness_full_coverage_ne :
    coverageOfFull witnessFullA ≠ coverageOfFull witnessFullB := by
  simp [coverageOfFull, witnessFullA, witnessFullB, witnessEntryA,
    witnessEntryB, SignedHtlcEntry.toCommitmentHtlcOutput]
  decide

/-- **No legacy-only coverage decoder.**  There is no function from
`CommitmentSigned` alone that returns the exact covered HTLC output list for
every full record.  The two concrete records above have the same wire
projection but different coverage. -/
theorem no_legacy_only_coverage_decoder :
    ¬ ∃ decode : CommitmentSigned → List CommitmentHTLCOutput,
        ∀ f : CommitmentSignedFull,
          decode f.toCommitmentSigned = coverageOfFull f := by
  rintro ⟨decode, hdecode⟩
  have hsame : decode witnessFullA.toCommitmentSigned =
      decode witnessFullB.toCommitmentSigned := by
    rw [witness_full_same_projection]
  have hA := hdecode witnessFullA
  have hB := hdecode witnessFullB
  exact witness_full_coverage_ne (hA.symm.trans (hsame.trans hB))

/-- **No legacy-only witness selector.**  Even a function that chooses an
arbitrary witness from the wire cannot be correct for every full record: both
full records project to the same wire, so the selector must return the same
witness for both. -/
theorem no_legacy_only_witness_selector :
    ¬ ∃ choose : CommitmentSigned → CoverageWitness,
        ∀ f : CommitmentSignedFull,
          decodeCoverage f.toCommitmentSigned (choose f.toCommitmentSigned) =
            some (coverageOfFull f) := by
  rintro ⟨choose, hchoose⟩
  have hA := hchoose witnessFullA
  have hB := hchoose witnessFullB
  rw [witness_full_same_projection] at hA
  have hEq : some (coverageOfFull witnessFullA) =
      some (coverageOfFull witnessFullB) := hA.symm.trans hB
  exact witness_full_coverage_ne (by simpa using hEq)

/-! ## 4. Witness necessity: the amount row is load-bearing -/

/-- The amount-erased identification row of a witness entry.  This is the data
that survives when the millisatoshi amount is dropped. -/
def reducedIdent (e : SignedHtlcEntry) :
    Nat × PaymentHash × Direction × HTLCState × Nat :=
  (e.htlcId, e.paymentHash, e.direction, e.htlcState, e.cltvExpiry)

/-- The witness with the amount row dropped. -/
def CoverageWitness.withoutAmount (w : CoverageWitness) :
    List (Nat × PaymentHash × Direction × HTLCState × Nat) :=
  w.entries.map reducedIdent

/-- The two counterexample witnesses become equal once amounts are erased, but
their coverage differs.  Hence the amount row is necessary, not decoration. -/
theorem witness_full_same_reduced_witness :
    (witnessOfFull witnessFullA).withoutAmount =
      (witnessOfFull witnessFullB).withoutAmount := by
  simp [CoverageWitness.withoutAmount, reducedIdent, witnessOfFull,
    witnessFullA, witnessFullB, witnessEntryA, witnessEntryB]

/-- **The amount field is necessary.**  Two full records have the same
amount-erased witness, yet decoding them (with the same legacy wire) yields
different HTLC output lists. -/
theorem amount_is_necessary :
    ∃ w₁ w₂ : CoverageWitness,
      w₁.withoutAmount = w₂.withoutAmount ∧
        decodeCoverage witnessFullA.toCommitmentSigned w₁ ≠
          decodeCoverage witnessFullA.toCommitmentSigned w₂ := by
  refine ⟨witnessOfFull witnessFullA, witnessOfFull witnessFullB,
    witness_full_same_reduced_witness, ?_⟩
  have hA := decodeCoverage_canonical witnessFullA
  have hB := decodeCoverage_canonical witnessFullB
  rw [← witness_full_same_projection] at hB
  rw [hA, hB]
  intro h
  exact witness_full_coverage_ne (by simpa using h)

/-- **Exact minimal determining tuple for coverage.**  Two signed entries
project to the same `CommitmentHTLCOutput` exactly when they agree on
direction, the floored satoshi amount, `cltv_expiry`, and lifecycle state.
The HTLC id, payment hash, signed-data digest, and signature do not enter the
output projection. -/
theorem toCommitmentHtlcOutput_eq_iff (e₁ e₂ : SignedHtlcEntry) :
    e₁.toCommitmentHtlcOutput = e₂.toCommitmentHtlcOutput ↔
      e₁.direction = e₂.direction ∧
        e₁.amount.toSatFloor = e₂.amount.toSatFloor ∧
          e₁.cltvExpiry = e₂.cltvExpiry ∧
            e₁.htlcState = e₂.htlcState := by
  constructor
  · intro h
    have h' : e₁.direction = e₂.direction ∧
        e₁.amount.toSatFloor = e₂.amount.toSatFloor ∧
          e₁.cltvExpiry = e₂.cltvExpiry ∧
            e₁.htlcState = e₂.htlcState ∧
              e₁.amount.toSatFloor = e₂.amount.toSatFloor := by
      simpa [SignedHtlcEntry.toCommitmentHtlcOutput,
        CommitmentHTLCOutput.mk.injEq] using h
    exact ⟨h'.1, h'.2.1, h'.2.2.1, h'.2.2.2.1⟩
  · rintro ⟨hd, ha, hc, hs⟩
    simp [SignedHtlcEntry.toCommitmentHtlcOutput, hd, ha, hc, hs]

/-- The HTLC id does not affect the covered output. -/
theorem toCommitmentHtlcOutput_update_htlcId (e : SignedHtlcEntry) (n : Nat) :
    ({ e with htlcId := n } : SignedHtlcEntry).toCommitmentHtlcOutput =
      e.toCommitmentHtlcOutput := rfl

/-- The payment hash does not affect the covered output.  It is still needed to
identify the HTLC for state reconciliation, but not for the output list. -/
theorem toCommitmentHtlcOutput_update_paymentHash
    (e : SignedHtlcEntry) (h : PaymentHash) :
    ({ e with paymentHash := h } : SignedHtlcEntry).toCommitmentHtlcOutput =
      e.toCommitmentHtlcOutput := rfl

/-- The signed-data digest does not affect the covered output. -/
theorem toCommitmentHtlcOutput_update_digest
    (e : SignedHtlcEntry) (d : ByteArray) :
    ({ e with signedDataDigest := d } : SignedHtlcEntry).toCommitmentHtlcOutput =
      e.toCommitmentHtlcOutput := rfl

/-- The signature does not affect the covered output; it only cross-checks the
legacy HTLC-signature list through `wireCompatible`. -/
theorem toCommitmentHtlcOutput_update_signature
    (e : SignedHtlcEntry) (s : EcdsaSig) :
    ({ e with signature := s } : SignedHtlcEntry).toCommitmentHtlcOutput =
      e.toCommitmentHtlcOutput := rfl

/-! ## 5. The residual wire boundary -/

/-- **The legacy wire admits two witnesses with different coverage.**  Both
witnesses are wire-compatible with the same `commitment_signed`, but decode to
different output lists.  The wire cannot select the witness, which is exactly
why the decoder takes one as an argument. -/
theorem wire_admits_distinct_coverage_witnesses :
    ∃ (m : CommitmentSigned) (w₁ w₂ : CoverageWitness),
      wireCompatible m w₁ ∧ wireCompatible m w₂ ∧
        decodeCoverage m w₁ ≠ decodeCoverage m w₂ := by
  refine ⟨witnessFullA.toCommitmentSigned, witnessOfFull witnessFullA,
    witnessOfFull witnessFullB, ?_, ?_, ?_⟩
  · exact wireCompatible_toCommitmentSigned witnessFullA
  · rw [witness_full_same_projection]
    exact wireCompatible_toCommitmentSigned witnessFullB
  · have hA := decodeCoverage_canonical witnessFullA
    have hB := decodeCoverage_canonical witnessFullB
    rw [← witness_full_same_projection] at hB
    rw [hA, hB]
    intro h
    exact witness_full_coverage_ne (by simpa using h)

/-- No selector of a wire-compatible witness can decode every full record
correctly.  This is the witness-level restatement of
`no_legacy_only_witness_selector`. -/
theorem wire_cannot_select_witness :
    ¬ ∃ choose : CommitmentSigned → CoverageWitness,
        (∀ m : CommitmentSigned, wireCompatible m (choose m)) ∧
          ∀ f : CommitmentSignedFull,
            decodeCoverage f.toCommitmentSigned (choose f.toCommitmentSigned) =
              some (coverageOfFull f) := by
  rintro ⟨choose, _hw, hchoose⟩
  have hA := hchoose witnessFullA
  have hB := hchoose witnessFullB
  rw [witness_full_same_projection] at hA
  have hEq : some (coverageOfFull witnessFullA) =
      some (coverageOfFull witnessFullB) := hA.symm.trans hB
  exact witness_full_coverage_ne (by simpa using hEq)

/-! ## 6. Summary -/

/-- Bundled faithful reading of the lane:

1. The canonical witness decodes to the full record's exact coverage.
2. No decoder from the legacy record alone is correct for every full record.
3. The legacy wire is compatible with two witnesses that decode differently,
   so it cannot select the witness.
4. Erasing the amount row identifies two records with different coverage, and
   the exact output-determining tuple is direction/floor(amount)/expiry/state.

The last two conjuncts are the residual boundary: a production decoder needs
the witness from an out-of-band/full-record source or a protocol change.  The
legacy `commitment_signed` wire is not sufficient and is not claimed to be. -/
theorem coverage_witness_summary :
    (∀ f : CommitmentSignedFull,
      decodeCoverage f.toCommitmentSigned (witnessOfFull f) =
        some (coverageOfFull f)) ∧
      (¬ ∃ decode : CommitmentSigned → List CommitmentHTLCOutput,
        ∀ f : CommitmentSignedFull,
          decode f.toCommitmentSigned = coverageOfFull f) ∧
      (∃ (m : CommitmentSigned) (w₁ w₂ : CoverageWitness),
        wireCompatible m w₁ ∧ wireCompatible m w₂ ∧
          decodeCoverage m w₁ ≠ decodeCoverage m w₂) ∧
      (∃ w₁ w₂ : CoverageWitness,
        w₁.withoutAmount = w₂.withoutAmount ∧
          decodeCoverage witnessFullA.toCommitmentSigned w₁ ≠
            decodeCoverage witnessFullA.toCommitmentSigned w₂) :=
  ⟨decodeCoverage_canonical, no_legacy_only_coverage_decoder,
    wire_admits_distinct_coverage_witnesses, amount_is_necessary⟩

end LnLean.Proofs.Channel.CoverageWitnessTargets
