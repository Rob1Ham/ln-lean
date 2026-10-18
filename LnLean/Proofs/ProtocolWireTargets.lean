/-
# Protocol wire targets — the full `commitment_signed` record (PR-02)

**Catalog issue (PR-02).**  The legacy `CommitmentSigned` wire record has no
commitment number, no commitment-transaction digest, no fee, and no per-HTLC
identification data, so it cannot determine what it covers.  The mechanized
negative results are in `LnLean.Proofs.ProtocolCoverageTargets`
(`no_wire_determined_coverage`, `no_coverage_htlc_selector`).

**Result of this module.**  `LnLean.Protocol.CommitmentSignedFull` adds the
missing signer-side data to the wave-A record without changing
`CommitmentSigned` (the projection is
`CommitmentSignedFull.toCommitmentSigned`).  On top of that record this module

1. defines an explicit channel state (`SignedState`) whose HTLC descriptors
   carry the id, millisatoshi amount, payment hash, direction, lifecycle tag,
   expiry, and signed-data digest, and whose projection
   `SignedState.toCommitment` is definitionally the `Commitment` the full
   record signs;
2. defines the explicit production relation `ProducedFrom f st sigAt`: the
   record's channel id, commitment number, fee, and commitment digest agree
   with the state, and its HTLC entries are exactly the state's HTLCs signed
   by the per-HTLC family `sigAt`;
3. proves, **without assuming coverage**, that under `ProducedFrom` and the
   two BOLT 3 value equations
   (`CommitmentConserved` and `FeeIsFundingResidual`), the record's signed
   entries map exactly onto the current commitment HTLC set, its wire
   projection carries exactly one signature per HTLC output, the fee equals
   the BOLT 3 formula fee, and the commitment number and digest are the
   state's;
4. constructs an honest full record from a state, proves it satisfies
   `ProducedFrom`, and proves the projection is a `wellFormed` legacy message
   under the BOLT 1 size bounds;
5. preserves the legacy negative results and proves that the projection
   forgets the added data (same legacy wire record, different fee, different
   commitment number) and that count-level coverage is strictly weaker than
   exact entry coverage.

## Scope

`ProducedFrom` is a *signed-data* relation, not a cryptographic check.  The
model has no BOLT 3 sighash serializer and no ECDSA verification for
commitments (C3 is only used elsewhere), so `sigAt` and the two digests
(`commitmentDigest`, `signedDataDigest`) are explicit data.  The theorem
states what follows from an honestly produced record; it does not prove that
a received wire message was produced this way.

The `Commitment` model records `feeSat` in the same unit that
`commitmentFee` returns (millisatoshis), while `totalOutputValue` is in
satoshis; this module inherits that existing convention from
`LnLean.Proofs.Conservation` and `LnLean.Proofs.ProtocolCoverageTargets` and
does not change it.

## Anchors

* BOLT 2 §"Committing Updates So Far" (type 132) and §"Completing the
  Transition" (type 133): one commitment signature plus one signature per
  untrimmed HTLC output.
* BOLT 3 §"Commitment Transaction" and §"Fees": output set, weight, floored
  fee, and the fee as the funding residual.
* Model: `LnLean/Protocol/Messages.lean` (`SignedHtlcEntry`,
  `CommitmentSignedFull`, `toCommitmentSigned`),
  `LnLean/Channel/Commitment.lean` (`Commitment`, `commitmentFee`,
  `commitmentOutputs`), `LnLean/Proofs/Channel/CommitmentTxProps.lean`
  (`htlcOutputCount`), `LnLean/Proofs/ProtocolCoverageTargets.lean`.
-/

import LnLean.Protocol.Messages
import LnLean.Channel.Commitment
import LnLean.Channel.Fee
import LnLean.Proofs.Channel.CommitmentTxProps
import LnLean.Proofs.Conservation
import LnLean.Proofs.ProtocolCoverageTargets

namespace LnLean.Proofs.ProtocolWireTargets

set_option autoImplicit false

open LnLean
open LnLean.Protocol
open LnLean.Channel
open LnLean.Proofs
open LnLean.Proofs.WaveE.E20
open LnLean.Proofs.ProtocolCoverageTargets

/-! ## 1. State-side HTLC descriptors -/

/-- The state-side counterpart of `SignedHtlcEntry`: the same identification
data plus the HTLC lifecycle tag, but no signature.  The signed-data digest is
part of the state because it is determined by the BOLT 3 second-stage
transaction, not by the wire encoding. -/
structure SignedHtlc where
  htlcId : Nat
  amount : Msat
  paymentHash : PaymentHash
  direction : Direction
  htlcState : HTLCState
  cltvExpiry : Height
  signedDataDigest : ByteArray
deriving Repr, BEq

namespace SignedHtlc

/-- Fill in the signature to obtain the wire entry for this HTLC. -/
def toEntry (h : SignedHtlc) (signature : EcdsaSig) : SignedHtlcEntry where
  htlcId := h.htlcId
  amount := h.amount
  paymentHash := h.paymentHash
  direction := h.direction
  htlcState := h.htlcState
  cltvExpiry := h.cltvExpiry
  signedDataDigest := h.signedDataDigest
  signature := signature

/-- The commitment output this HTLC produces (BOLT 3 satoshi floor). -/
def toCommitmentHtlcOutput (h : SignedHtlc) : CommitmentHTLCOutput where
  direction := h.direction
  amountSat := h.amount.toSatFloor
  cltvExpiry := h.cltvExpiry
  state := h.htlcState

@[simp] theorem toEntry_signature (h : SignedHtlc) (s : EcdsaSig) :
    (h.toEntry s).signature = s := rfl

@[simp] theorem toEntry_htlcId (h : SignedHtlc) (s : EcdsaSig) :
    (h.toEntry s).htlcId = h.htlcId := rfl

@[simp] theorem toEntry_digest (h : SignedHtlc) (s : EcdsaSig) :
    (h.toEntry s).signedDataDigest = h.signedDataDigest := rfl

@[simp] theorem toEntry_toCommitmentHtlcOutput (h : SignedHtlc)
    (s : EcdsaSig) :
    (h.toEntry s).toCommitmentHtlcOutput = h.toCommitmentHtlcOutput := rfl

/-- The identification tuple of a state-side HTLC. -/
def ident (h : SignedHtlc) : Nat × Msat × PaymentHash × Direction × Nat :=
  (h.htlcId, h.amount, h.paymentHash, h.direction, h.cltvExpiry)

@[simp] theorem toEntry_ident (h : SignedHtlc) (s : EcdsaSig) :
    (h.toEntry s).ident = h.ident := rfl

/-- Mapping entries back to their outputs is the same as mapping the
descriptors directly. -/
theorem map_toEntry_toCommitmentHtlcOutput (l : List SignedHtlc)
    (sigAt : SignedHtlc → EcdsaSig) :
    (l.map (fun h => h.toEntry (sigAt h))).map
        SignedHtlcEntry.toCommitmentHtlcOutput =
      l.map SignedHtlc.toCommitmentHtlcOutput := by
  induction l with
  | nil => rfl
  | cons h t ih => simp [ih]

/-- The wire signature list of the image is the signature family itself. -/
theorem map_toEntry_signature (l : List SignedHtlc)
    (sigAt : SignedHtlc → EcdsaSig) :
    (l.map (fun h => h.toEntry (sigAt h))).map (fun e => e.signature) =
      l.map sigAt := by
  induction l with
  | nil => rfl
  | cons h t ih => simp [ih]

/-- The signed-data digests are preserved by the entry mapping. -/
theorem map_toEntry_digest (l : List SignedHtlc)
    (sigAt : SignedHtlc → EcdsaSig) :
    (l.map (fun h => h.toEntry (sigAt h))).map (fun e => e.signedDataDigest) =
      l.map (fun h => h.signedDataDigest) := by
  induction l with
  | nil => rfl
  | cons h t ih => simp [ih]

/-- The full identification tuples are preserved by the entry mapping. -/
theorem map_toEntry_ident (l : List SignedHtlc)
    (sigAt : SignedHtlc → EcdsaSig) :
    (l.map (fun h => h.toEntry (sigAt h))).map SignedHtlcEntry.ident =
      l.map SignedHtlc.ident := by
  induction l with
  | nil => rfl
  | cons h t ih => simp [ih]

end SignedHtlc

/-! ## 2. The explicit channel state -/

/-- The signer-side channel state that a full `commitment_signed` signs: the
commitment-transaction balance fields, the negotiated feerate, the
commitment-transaction digest, and the HTLC descriptors in commitment order.
`toCommitment` is the `Commitment` record these fields determine. -/
structure SignedState where
  channelId : ChannelId
  holder : Direction
  commitmentNumber : Nat
  fundingValueSat : Nat
  toLocalSat : Nat
  toRemoteSat : Nat
  feeSat : Nat
  contestDelay : Nat
  anchorOutputs : Bool
  feerate : FeeRate
  commitmentDigest : ByteArray
  htlcs : List SignedHtlc
deriving Repr, BEq

/-- The commitment transaction the state describes.  Its HTLC list is
*defined* to be the descriptor projection, so "the signed entries cover the
current HTLC set" is a statement about the same list the commitment emits. -/
def SignedState.toCommitment (st : SignedState) : Commitment where
  holder := st.holder
  commitmentNumber := st.commitmentNumber
  fundingValueSat := st.fundingValueSat
  toLocalSat := st.toLocalSat
  toRemoteSat := st.toRemoteSat
  htlcs := st.htlcs.map SignedHtlc.toCommitmentHtlcOutput
  feeSat := st.feeSat
  contestDelay := st.contestDelay
  anchorOutputs := st.anchorOutputs

@[simp] theorem SignedState.toCommitment_htlcs (st : SignedState) :
    st.toCommitment.htlcs = st.htlcs.map SignedHtlc.toCommitmentHtlcOutput := rfl

@[simp] theorem SignedState.toCommitment_htlcs_length (st : SignedState) :
    st.toCommitment.htlcs.length = st.htlcs.length := by
  simp

@[simp] theorem SignedState.toCommitment_commitmentNumber (st : SignedState) :
    st.toCommitment.commitmentNumber = st.commitmentNumber := rfl

@[simp] theorem SignedState.toCommitment_feeSat (st : SignedState) :
    st.toCommitment.feeSat = st.feeSat := rfl

/-! ## 3. The production relation -/

/-- `f` was produced from the state `st` by signing each state HTLC with
`sigAt`.  Every field is an explicit equation; in particular the fee and the
commitment number are related to the state, and the per-HTLC identification
data and signed-data digests are those of the state's HTLCs. -/
structure ProducedFrom (f : CommitmentSignedFull) (st : SignedState)
    (sigAt : SignedHtlc → EcdsaSig) : Prop where
  channelId_eq : f.channelId = st.channelId
  commitmentNumber_eq : f.commitmentNumber = st.commitmentNumber
  feePaid_eq : f.feePaid.val = st.feeSat
  commitmentDigest_eq : f.commitmentDigest = st.commitmentDigest
  htlcEntries_eq : f.htlcEntries = st.htlcs.map (fun h => h.toEntry (sigAt h))

/-- Under `ProducedFrom`, the signed entries project exactly onto the
commitment's current HTLC outputs. -/
theorem ProducedFrom.entries_map_output {f : CommitmentSignedFull}
    {st : SignedState} {sigAt : SignedHtlc → EcdsaSig}
    (h : ProducedFrom f st sigAt) :
    f.htlcEntries.map SignedHtlcEntry.toCommitmentHtlcOutput =
      st.toCommitment.htlcs := by
  rw [h.htlcEntries_eq, SignedHtlc.map_toEntry_toCommitmentHtlcOutput]
  rfl

/-- Under `ProducedFrom`, the legacy wire HTLC-signature list is the image of
the state's HTLC descriptors under `sigAt`.  This is the per-entry form of the
signed-data relation; it is strictly stronger than a length equality. -/
theorem ProducedFrom.entries_signatures {f : CommitmentSignedFull}
    {st : SignedState} {sigAt : SignedHtlc → EcdsaSig}
    (h : ProducedFrom f st sigAt) :
    f.toCommitmentSigned.htlcSignatures = st.htlcs.map sigAt := by
  change f.htlcEntries.map (fun e => e.signature) = st.htlcs.map sigAt
  rw [h.htlcEntries_eq, SignedHtlc.map_toEntry_signature]

/-- Under `ProducedFrom`, the entries carry exactly the state's signed-data
digests. -/
theorem ProducedFrom.entries_digests {f : CommitmentSignedFull}
    {st : SignedState} {sigAt : SignedHtlc → EcdsaSig}
    (h : ProducedFrom f st sigAt) :
    f.htlcEntries.map (fun e => e.signedDataDigest) =
      st.htlcs.map (fun h => h.signedDataDigest) := by
  rw [h.htlcEntries_eq, SignedHtlc.map_toEntry_digest]

/-- Under `ProducedFrom`, the entry count is the state's HTLC count. -/
theorem ProducedFrom.entry_count {f : CommitmentSignedFull}
    {st : SignedState} {sigAt : SignedHtlc → EcdsaSig}
    (h : ProducedFrom f st sigAt) :
    f.htlcEntries.length = st.htlcs.length := by
  rw [h.htlcEntries_eq, List.length_map]

/-- Under `ProducedFrom`, the entries carry exactly the state's HTLC
identification data, including the millisatoshi amounts and payment hashes
that the commitment output projection floors away. -/
theorem ProducedFrom.entry_metadata {f : CommitmentSignedFull}
    {st : SignedState} {sigAt : SignedHtlc → EcdsaSig}
    (h : ProducedFrom f st sigAt) :
    f.htlcEntries.map SignedHtlcEntry.ident =
      st.htlcs.map SignedHtlc.ident := by
  rw [h.htlcEntries_eq]
  exact SignedHtlc.map_toEntry_ident st.htlcs sigAt

/-! ## 4. Conditional coverage -/

/-- **PR-02, positive direction.**  If a full record was produced from the
state and the BOLT 3 value equations hold for the commitment the state
describes, then its signed entries cover exactly the current HTLC set and the
fee is exactly the floored BOLT 3 formula fee.

The hypotheses are not the conclusion: `hprod` is a field-by-field
production relation (including the signed-data family `sigAt`), `hcons` is
the balance equation, and `hres` says the formula fee is the funding residual.
Coverage, the fee equality, the commitment number, and the digest are all
derived. -/
theorem commitment_signed_full_covers
    (f : CommitmentSignedFull) (st : SignedState)
    (sigAt : SignedHtlc → EcdsaSig)
    (hprod : ProducedFrom f st sigAt)
    (hcons : CommitmentConserved st.toCommitment)
    (hres : FeeIsFundingResidual st.feerate st.toCommitment) :
    f.htlcEntries.map SignedHtlcEntry.toCommitmentHtlcOutput =
        st.toCommitment.htlcs ∧
      f.toCommitmentSigned.htlcSignatures.length =
        st.toCommitment.htlcs.length ∧
      CoversHtlcOutputs f.toCommitmentSigned st.toCommitment ∧
      f.feePaid.val = (commitmentFee st.feerate st.toCommitment).val ∧
      f.commitmentNumber = st.toCommitment.commitmentNumber ∧
      f.commitmentDigest = st.commitmentDigest ∧
      waveE_e20_commitment_signed_covers
        f.toCommitmentSigned st.feerate st.toCommitment ∧
      f.htlcEntries.map SignedHtlcEntry.ident =
        st.htlcs.map SignedHtlc.ident := by
  have hdesc : f.htlcEntries.map SignedHtlcEntry.toCommitmentHtlcOutput =
      st.toCommitment.htlcs := hprod.entries_map_output
  have hlen : f.toCommitmentSigned.htlcSignatures.length =
      st.toCommitment.htlcs.length := by
    rw [hprod.entries_signatures]
    simp
  have hfee : f.feePaid.val =
      (commitmentFee st.feerate st.toCommitment).val := by
    unfold CommitmentConserved at hcons
    unfold FeeIsFundingResidual at hres
    simp only [SignedState.toCommitment_feeSat] at hcons ⊢
    rw [hprod.feePaid_eq]
    omega
  have hcoversFee : waveE_e20_covers_fee st.feerate st.toCommitment := by
    unfold waveE_e20_covers_fee
    simp only [SignedState.toCommitment_feeSat]
    rw [← hprod.feePaid_eq]
    exact hfee
  refine ⟨hdesc, hlen, ?_, hfee, ?_, hprod.commitmentDigest_eq,
    ⟨hlen, hcoversFee⟩, hprod.entry_metadata⟩
  · unfold CoversHtlcOutputs
    rw [hlen, Commitment.htlcOutputCount_commitmentOutputs]
  · rw [hprod.commitmentNumber_eq]
    rfl

/-- The exact catalog-shaped corollary: the legacy wire projection of an
honestly produced full record carries exactly `#htlcs + 1` signatures and
pays the BOLT 3 formula fee. -/
theorem commitment_signed_full_covers_exact
    (f : CommitmentSignedFull) (st : SignedState)
    (sigAt : SignedHtlc → EcdsaSig)
    (hprod : ProducedFrom f st sigAt)
    (hcons : CommitmentConserved st.toCommitment)
    (hres : FeeIsFundingResidual st.feerate st.toCommitment) :
    f.toCommitmentSigned.htlcSignatures.length = st.toCommitment.htlcs.length ∧
      (signatures (.commitmentSigned f.toCommitmentSigned)).length =
        st.toCommitment.htlcs.length + 1 ∧
      f.feePaid.val = (commitmentFee st.feerate st.toCommitment).val ∧
      waveE_e20_commitment_signed_covers
        f.toCommitmentSigned st.feerate st.toCommitment := by
  have h := commitment_signed_full_covers f st sigAt hprod hcons hres
  exact ⟨h.2.1, by rw [waveE_e20_signature_count, h.2.1], h.2.2.2.1, h.2.2.2.2.2.2.1⟩

/-! ## 5. Honest construction and well-formedness -/

/-- The honest full record for a state: the supplied commitment signature and
the per-HTLC signature family applied to the state's HTLCs.  The fee and
commitment number are copied from the state by construction. -/
def commitmentSignedFullOfState (st : SignedState) (commitSig : EcdsaSig)
    (sigAt : SignedHtlc → EcdsaSig) : CommitmentSignedFull where
  channelId := st.channelId
  commitmentNumber := st.commitmentNumber
  feePaid := ⟨st.feeSat⟩
  commitmentDigest := st.commitmentDigest
  commitmentSignature := commitSig
  htlcEntries := st.htlcs.map (fun h => h.toEntry (sigAt h))

/-- The honest record is produced from the state it was built from. -/
theorem producedFrom_commitmentSignedFullOfState (st : SignedState)
    (commitSig : EcdsaSig) (sigAt : SignedHtlc → EcdsaSig) :
    ProducedFrom (commitmentSignedFullOfState st commitSig sigAt) st sigAt :=
  { channelId_eq := rfl
    commitmentNumber_eq := rfl
    feePaid_eq := rfl
    commitmentDigest_eq := rfl
    htlcEntries_eq := rfl }

/-- The projection of an honestly produced full record is a `wellFormed`
legacy `commitment_signed` when its channel id, signatures, and payload fit
BOLT 1's bounds.  Thus the extension does not produce records the legacy
decoder would reject for structural reasons. -/
theorem wellFormed_toCommitmentSigned (f : CommitmentSignedFull)
    (hcid : f.channelId.Valid)
    (hcommit : f.commitmentSignature.bytes.size ≤ 73)
    (hentries : ∀ e ∈ f.htlcEntries, e.signature.bytes.size ≤ 73)
    (hlen : 34 + f.commitmentSignature.bytes.size +
        sigListLen (f.htlcEntries.map (fun e => e.signature)) ≤ 65535) :
    wellFormed (.commitmentSigned f.toCommitmentSigned) := by
  refine ⟨?_, ?_, ?_, trivial⟩
  · simpa [CommitmentSignedFull.msgLength_toCommitmentSigned, sigLen] using hlen
  · refine ⟨?_, ?_⟩
    · intro c hc
      simp [channelId?, CommitmentSignedFull.toCommitmentSigned] at hc
      subst hc
      exact hcid
    · intro p hp
      simp [pubKeys] at hp
  · unfold sigsValid
    intro s hs
    rw [CommitmentSignedFull.signatures_toCommitmentSigned] at hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact hcommit
    · rw [List.mem_map] at hs
      obtain ⟨e, he, rfl⟩ := hs
      exact hentries e he

/-! ## 6. Non-vacuity: a concrete conserving state -/

/-- A concrete one-HTLC state whose fee is the BOLT 3 formula fee and whose
outputs plus fee exactly exhaust the funding value.  `amount = 1000 msat`
floors to one satoshi. -/
def exampleSignedState : SignedState where
  channelId := ChannelId.zero
  holder := .local
  commitmentNumber := 0
  fundingValueSat := 20897
  toLocalSat := 10000
  toRemoteSat := 10000
  feeSat := 896
  contestDelay := 144
  anchorOutputs := false
  feerate := ⟨1000⟩
  commitmentDigest := ByteArray.empty
  htlcs := [{ htlcId := 1
              amount := ⟨1000⟩
              paymentHash := ⟨ByteArray.empty⟩
              direction := .local
              htlcState := .offered
              cltvExpiry := 100
              signedDataDigest := ByteArray.empty }]

theorem exampleSignedState_conserved :
    CommitmentConserved exampleSignedState.toCommitment := by
  unfold CommitmentConserved
  decide

theorem exampleSignedState_residual :
    FeeIsFundingResidual exampleSignedState.feerate
      exampleSignedState.toCommitment := by
  unfold FeeIsFundingResidual
  decide

/-- The conditional theorem is instantiated: the honest record for the
concrete state covers its HTLC set and pays the formula fee. -/
theorem example_commitment_signed_full_covers
    (commitSig : EcdsaSig) (sigAt : SignedHtlc → EcdsaSig) :
    (commitmentSignedFullOfState exampleSignedState commitSig sigAt).htlcEntries.map
        SignedHtlcEntry.toCommitmentHtlcOutput =
        exampleSignedState.toCommitment.htlcs ∧
      (commitmentSignedFullOfState exampleSignedState commitSig sigAt).feePaid.val =
        (commitmentFee exampleSignedState.feerate
          exampleSignedState.toCommitment).val := by
  have h := commitment_signed_full_covers
    (commitmentSignedFullOfState exampleSignedState commitSig sigAt)
    exampleSignedState sigAt
    (producedFrom_commitmentSignedFullOfState exampleSignedState commitSig sigAt)
    exampleSignedState_conserved exampleSignedState_residual
  exact ⟨h.1, h.2.2.2.1⟩

/-! ## 7. Negative results and projection limits -/

/-- The legacy wire record alone still cannot determine coverage: the
S3/S4-PR004 no-decoder theorem is preserved unchanged. -/
theorem legacy_wire_cannot_determine_coverage :
    ¬ ∃ g : CommitmentSigned → Commitment,
        ∀ (m : CommitmentSigned) (r : FeeRate),
          waveE_e20_commitment_signed_covers m r (g m) :=
  no_wire_determined_coverage

/-- The legacy wire record alone still cannot select the HTLC set: the
S3/S4-PR004 counterexample is preserved unchanged. -/
theorem legacy_wire_cannot_select_htlc_set :
    ¬ ∃ g : CommitmentSigned → List CommitmentHTLCOutput,
        ∀ (m : CommitmentSigned) (c : Commitment),
          waveE_e20_covers_htlcs m c → c.htlcs = g m :=
  no_coverage_htlc_selector

/-- Build a full record from an arbitrary legacy record and arbitrary added
data (no production claim). -/
def fullOfWire (m : CommitmentSigned) (number : Nat) (fee : Msat)
    (digest : ByteArray) (entries : List SignedHtlcEntry) :
    CommitmentSignedFull where
  channelId := m.channelId
  commitmentNumber := number
  feePaid := fee
  commitmentDigest := digest
  commitmentSignature := m.signature
  htlcEntries := entries

@[simp] theorem fullOfWire_toCommitmentSigned (m : CommitmentSigned)
    (number : Nat) (fee : Msat) (digest : ByteArray)
    (entries : List SignedHtlcEntry) :
    (fullOfWire m number fee digest entries).toCommitmentSigned =
      { m with htlcSignatures := entries.map (fun e => e.signature) } := rfl

/-- **The projection is lossy.**  Two full records with the same legacy wire
projection can disagree on the fee and the commitment number.  Hence the
added fields are necessary data, not a consequence of the wire record. -/
theorem projection_forgets_fee_and_number :
    ∃ f g : CommitmentSignedFull,
      f.toCommitmentSigned = g.toCommitmentSigned ∧
        f.feePaid ≠ g.feePaid ∧ f.commitmentNumber ≠ g.commitmentNumber := by
  let m : CommitmentSigned := waveE_e20_emptyCommitmentSigned
  refine ⟨fullOfWire m 0 ⟨0⟩ ByteArray.empty [],
    fullOfWire m 1 ⟨1⟩ ByteArray.empty [], ?_, ?_, ?_⟩
  · rfl
  · decide
  · decide

/-- **The projection is lossy at entry granularity.**  Two full records with
the same legacy wire projection can disagree on the HTLC ids of their signed
entries (the wire only carries the signatures). -/
theorem projection_forgets_entry_metadata :
    ∃ f g : CommitmentSignedFull,
      f.toCommitmentSigned = g.toCommitmentSigned ∧
        f.htlcEntries ≠ g.htlcEntries := by
  let e0 : SignedHtlcEntry :=
    { htlcId := 0
      amount := ⟨0⟩
      paymentHash := ⟨ByteArray.empty⟩
      direction := .local
      htlcState := .offered
      cltvExpiry := 0
      signedDataDigest := ByteArray.empty
      signature := ⟨ByteArray.empty⟩ }
  let e1 : SignedHtlcEntry := { e0 with htlcId := 1 }
  let m : CommitmentSigned := waveE_e20_emptyCommitmentSigned
  refine ⟨fullOfWire m 0 ⟨0⟩ ByteArray.empty [e0],
    fullOfWire m 0 ⟨0⟩ ByteArray.empty [e1], ?_, ?_⟩
  · rfl
  · intro h
    have hhead := congrArg (fun l : List SignedHtlcEntry => l[0]?) h
    have hsome : some e0 = some e1 := by
      simpa [fullOfWire] using hhead
    have heq : e0 = e1 := Option.some.inj hsome
    have hid := congrArg (fun e : SignedHtlcEntry => e.htlcId) heq
    simp [e0, e1] at hid

/-- A full record whose entry count matches a one-HTLC state but whose entry
describes a different amount.  Count-level coverage therefore does not imply
exact coverage; the identification data is load-bearing. -/
def mismatchedEntry : SignedHtlcEntry where
  htlcId := 1
  amount := ⟨2000⟩
  paymentHash := ⟨ByteArray.empty⟩
  direction := .local
  htlcState := .offered
  cltvExpiry := 100
  signedDataDigest := ByteArray.empty
  signature := ⟨ByteArray.empty⟩

def mismatchedFull : CommitmentSignedFull where
  channelId := ChannelId.zero
  commitmentNumber := 0
  feePaid := ⟨0⟩
  commitmentDigest := ByteArray.empty
  commitmentSignature := ⟨ByteArray.empty⟩
  htlcEntries := [mismatchedEntry]

/-- **Count coverage is strictly weaker than exact coverage.**  The record's
wire signature count equals the state's HTLC-output count, but its entries do
not project onto the state's HTLC set. -/
theorem count_coverage_not_exact_coverage :
    mismatchedFull.toCommitmentSigned.htlcSignatures.length =
        exampleSignedState.toCommitment.htlcs.length ∧
      mismatchedFull.htlcEntries.map SignedHtlcEntry.toCommitmentHtlcOutput ≠
        exampleSignedState.toCommitment.htlcs := by
  constructor
  · simp [mismatchedFull, CommitmentSignedFull.toCommitmentSigned,
      exampleSignedState, SignedState.toCommitment]
  · decide

/-- **Well-formedness still does not imply coverage.**  The empty legacy
record is accepted by the decoder, and it is the projection of a full record;
that full record covers no one-HTLC commitment at feerate zero. -/
theorem wellFormed_full_can_fail_coverage :
    ∃ f : CommitmentSignedFull,
      f.toCommitmentSigned = waveE_e20_emptyCommitmentSigned ∧
        wellFormed (.commitmentSigned f.toCommitmentSigned) ∧
        ¬ waveE_e20_commitment_signed_covers f.toCommitmentSigned ⟨0⟩
            (waveE_e20_commitmentWith 1 0) := by
  let f : CommitmentSignedFull :=
    fullOfWire waveE_e20_emptyCommitmentSigned 0 ⟨0⟩ ByteArray.empty []
  have hproj : f.toCommitmentSigned = waveE_e20_emptyCommitmentSigned := by
    simp [f, fullOfWire, CommitmentSignedFull.toCommitmentSigned,
      waveE_e20_emptyCommitmentSigned]
  refine ⟨f, hproj, ?_, ?_⟩
  · rw [hproj]
    exact wellFormed_message_can_fail_coverage.1
  · rw [hproj]
    exact wellFormed_message_can_fail_coverage.2

/-! ## 8. Summary -/

/-- Bundled faithful reading of PR-02.

1. Any full record produced from a state, with the BOLT 3 value equations,
   covers exactly that state's HTLC set and pays the formula fee.
2. The honest constructor always satisfies the production relation.
3. The legacy wire record alone still determines neither the fee/commitment
   nor the HTLC set.
4. The projection of the full record onto the legacy record forgets the fee
   and commitment number, so those fields must be state data. -/
theorem protocol_wire_summary :
    (∀ (f : CommitmentSignedFull) (st : SignedState)
        (sigAt : SignedHtlc → EcdsaSig),
        ProducedFrom f st sigAt →
        CommitmentConserved st.toCommitment →
        FeeIsFundingResidual st.feerate st.toCommitment →
        f.htlcEntries.map SignedHtlcEntry.toCommitmentHtlcOutput =
            st.toCommitment.htlcs ∧
          f.toCommitmentSigned.htlcSignatures.length =
            st.toCommitment.htlcs.length ∧
          f.feePaid.val = (commitmentFee st.feerate st.toCommitment).val ∧
          waveE_e20_commitment_signed_covers
            f.toCommitmentSigned st.feerate st.toCommitment) ∧
      (∀ (st : SignedState) (commitSig : EcdsaSig)
          (sigAt : SignedHtlc → EcdsaSig),
        ProducedFrom (commitmentSignedFullOfState st commitSig sigAt) st sigAt) ∧
      (¬ ∃ g : CommitmentSigned → Commitment,
          ∀ (m : CommitmentSigned) (r : FeeRate),
            waveE_e20_commitment_signed_covers m r (g m)) ∧
      (¬ ∃ g : CommitmentSigned → List CommitmentHTLCOutput,
          ∀ (m : CommitmentSigned) (c : Commitment),
            waveE_e20_covers_htlcs m c → c.htlcs = g m) ∧
      (∃ f g : CommitmentSignedFull,
          f.toCommitmentSigned = g.toCommitmentSigned ∧
            f.feePaid ≠ g.feePaid) :=
  ⟨fun f st sigAt hprod hcons hres =>
      ⟨(commitment_signed_full_covers f st sigAt hprod hcons hres).1,
        (commitment_signed_full_covers f st sigAt hprod hcons hres).2.1,
        (commitment_signed_full_covers f st sigAt hprod hcons hres).2.2.2.1,
        (commitment_signed_full_covers f st sigAt hprod hcons hres).2.2.2.2.2.2.1⟩,
    producedFrom_commitmentSignedFullOfState,
    legacy_wire_cannot_determine_coverage,
    legacy_wire_cannot_select_htlc_set,
    ⟨projection_forgets_fee_and_number.choose,
      projection_forgets_fee_and_number.choose_spec.choose,
      projection_forgets_fee_and_number.choose_spec.choose_spec.1,
      projection_forgets_fee_and_number.choose_spec.choose_spec.2.1⟩⟩

end LnLean.Proofs.ProtocolWireTargets
