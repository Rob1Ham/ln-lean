/-
# Protocol coverage targets — faithful narrowing of LN-PR-004

**Catalog claim (LN-PR-004).**  A `commitment_signed` covers exactly the
current HTLC set and fee.

**Result of this module.**  The claim is *not* derivable from the wave-A wire
record, and this module does not assume it.  Instead it

1. links E20's positional coverage predicate to the actual HTLC outputs of a
   commitment transaction (`CoversHtlcOutputs`);
2. states the exact signed-data relation the wire record can carry
   (`HtlcSignaturesMatch`: the HTLC-signature list is the image of the
   commitment's HTLC list under a per-HTLC signature family);
3. proves the positive direction from that relation plus the two BOLT 3 value
   equations for the commitment state (conservation and formula fee as the
   funding residual), with **no coverage hypothesis**;
4. constructs an honest wire record from a commitment state and proves it
   covers that state, including well-formedness under the BOLT 1 size bounds;
5. proves the negative results that pin the gap:
   * no total function `CommitmentSigned → Commitment` makes the whole
     coverage predicate true for every feerate (the fee is not on the wire);
   * no selector recovers the HTLC *set* from a covering message (only its
     cardinality is constrained);
   * positional count coverage is strictly weaker than per-output signature
     binding when the HTLC list repeats an output;
   * a well-formed message can cover no non-empty commitment at all.

## Exact missing wire data

BOLT 2's `commitment_signed` (type 132) carries only `channel_id`, one
`signature` over the commitment transaction, and one `HTLC_signature` per
untrimmed HTLC output.  It carries

* **no commitment number and no commitment-transaction digest** — so nothing
  in the record ties `signature` to a particular `Commitment`;
* **no HTLC identifier, direction, amount, or expiry** — so the HTLC *set*
  cannot be recovered, only its cardinality;
* **no feerate and no fee** — the fee is an off-wire fact about the
  commitment transaction.

The first gap is the cryptographic one: binding `signature` to a commitment
requires the BOLT 3 commitment sighash serialization and C3 verification.
`LnLean.Proofs.WaveE.E06` supplies that interface with the sighash as an
*explicit parameter*; the model has no `Commitment → ByteArray` serializer.
The second gap is witnessed by `no_coverage_htlc_selector`.  The third gap is
narrowed positively: the *required* fee is a function of the wire HTLC-signature
count and the negotiated `option_anchors` flag
(`requiredFee_eq_of_wire_count`), and is not an independent wire field.

## Anchors

* BOLT 2 §"Committing Updates So Far" (`refs/bolts/02-peer-protocol.md`,
  pinned `1aadb719b4007c4cea0ba6e36b08c4fb53788dee`): type 132 layout, one
  signature for the remote commitment transaction plus one per HTLC output.
* BOLT 3 §"Commitment Transaction" and §"Fees"
  (`refs/bolts/03-transactions.md`): output set, weight `724 + 172 * #htlcs`
  (or `1124 + 172 * #htlcs` with anchors), floor-divided fee, and the fee as
  the residual of the funding value after outputs.
* Model: `LnLean/Protocol/Messages.lean` (`CommitmentSigned`, `msgLength`,
  `signatures`, `wellFormed`), `LnLean/Channel/Commitment.lean`
  (`Commitment`, `commitmentFee`), `LnLean/Proofs/Channel/CommitmentTxProps.lean`
  (`htlcOutputCount`), `LnLean/Proofs/WaveE/E20.lean` (the coverage predicate
  and its counterexamples).

## What is NOT claimed

* No signature verification is performed: `signature` and `htlcSignatures`
  remain opaque bytes.  `HtlcSignaturesMatch` is a *signed-data* hypothesis,
  not a theorem about ECDSA.
* No `CommitmentSigned → Commitment` decoder is asserted to exist; the
  negative results show that the wire record alone determines neither the
  fee nor the HTLC set.
* The constructed message is the honest signer's message *for a supplied
  state*; it is not a claim that every received message was so constructed.
-/

import LnLean.Protocol.Messages
import LnLean.Channel.Commitment
import LnLean.Proofs.Channel.CommitmentTxProps
import LnLean.Proofs.Conservation
import LnLean.Proofs.WaveE.E20

namespace LnLean.Proofs.ProtocolCoverageTargets

set_option autoImplicit false

open LnLean
open LnLean.Protocol
open LnLean.Channel
open LnLean.Proofs
open LnLean.Proofs.WaveE.E20

/-! ## 1. Coverage of the emitted HTLC outputs -/

/-- BOLT 2 coverage stated on the commitment *transaction* rather than on the
`htlcs` field: the wire carries one HTLC signature per emitted HTLC output.

This is the same proposition as E20's `waveE_e20_covers_htlcs`
(`coversHtlcOutputs_iff_waveE`), but it names the output list, which is what
the signatures are actually over. -/
def CoversHtlcOutputs (m : CommitmentSigned) (c : Commitment) : Prop :=
  m.htlcSignatures.length = htlcOutputCount c.commitmentOutputs

/-- The output-list reading and E20's `htlcs`-field reading agree, because
`commitmentOutputs` emits exactly one `htlc` output per surviving HTLC. -/
theorem coversHtlcOutputs_iff_waveE (m : CommitmentSigned) (c : Commitment) :
    CoversHtlcOutputs m c ↔ waveE_e20_covers_htlcs m c := by
  unfold CoversHtlcOutputs waveE_e20_covers_htlcs
  rw [Commitment.htlcOutputCount_commitmentOutputs]

/-- Under coverage of the emitted outputs, the wire has exactly one signature
per untrimmed HTLC output of the commitment. -/
theorem coversHtlcOutputs_iff_length (m : CommitmentSigned) (c : Commitment) :
    CoversHtlcOutputs m c ↔ m.htlcSignatures.length = c.htlcs.length := by
  unfold CoversHtlcOutputs
  rw [Commitment.htlcOutputCount_commitmentOutputs]

/-! ## 2. Wire-side consequences (no commitment state needed) -/

/-- A `commitment_signed` always carries one more signature than its
HTLC-signature list: the signature over the commitment transaction. -/
theorem signature_count (m : CommitmentSigned) :
    (signatures (.commitmentSigned m)).length = m.htlcSignatures.length + 1 :=
  waveE_e20_signature_count m

/-- The wire signature list is exactly the commitment signature followed by
the HTLC signatures, with no additional entries. -/
theorem signatures_eq (m : CommitmentSigned) :
    signatures (.commitmentSigned m) = m.signature :: m.htlcSignatures := rfl

/-- Exact payload accounting: `32 + 2 + sigLen + sigListLen`. -/
theorem msgLength_eq (m : CommitmentSigned) :
    msgLength (.commitmentSigned m) =
      34 + sigLen m.signature + sigListLen m.htlcSignatures := rfl

/-- **The required fee is determined by the wire record** once the negotiated
`option_anchors` flag is known: coverage of the HTLC outputs pins the number of
HTLC outputs, hence the commitment weight, hence the floored BOLT 3 fee.  No
fee field is needed on the wire. -/
theorem requiredFee_eq_of_wire_count
    (m : CommitmentSigned) (c : Commitment) (r : FeeRate)
    (hc : waveE_e20_covers_htlcs m c) :
    (commitmentFee r c).val =
      (feeForWeight r
        (commitmentWeight c.anchorOutputs m.htlcSignatures.length)).val := by
  unfold waveE_e20_covers_htlcs at hc
  unfold commitmentFee Commitment.weight
  rw [← hc]

/-- Two commitments with the same HTLC-output count and the same
`option_anchors` flag require the same floored fee at any feerate. -/
theorem commitmentFee_eq_of_count_eq {c₁ c₂ : Commitment} {r : FeeRate}
    (h : c₁.htlcs.length = c₂.htlcs.length)
    (ha : c₁.anchorOutputs = c₂.anchorOutputs) :
    (commitmentFee r c₁).val = (commitmentFee r c₂).val := by
  unfold commitmentFee Commitment.weight
  rw [h, ha]

/-! ## 3. The missing signed-data relation -/

/-- The HTLC-signature list is the image of the commitment's HTLC-output list
under a per-output signature family.  This is strictly more than E20's
positional count: it says *which* signature belongs to *which* HTLC output.

This relation is not on the wire.  It is the signed-data interface that a
BOLT 3 `HTLC_signature` list must satisfy: entry `i` is the signature over the
second-stage transaction of commitment output `i`.  The model has no
`CommitmentHTLCOutput → ByteArray` sighash serializer, so the relation is an
explicit parameter `sigAt` rather than a verifier call. -/
def HtlcSignaturesMatch (m : CommitmentSigned) (c : Commitment)
    (sigAt : CommitmentHTLCOutput → EcdsaSig) : Prop :=
  m.htlcSignatures = c.htlcs.map sigAt

/-- Per-output binding implies positional count coverage. -/
theorem coversHtlcs_of_match {m : CommitmentSigned} {c : Commitment}
    {sigAt : CommitmentHTLCOutput → EcdsaSig}
    (h : HtlcSignaturesMatch m c sigAt) :
    waveE_e20_covers_htlcs m c := by
  unfold HtlcSignaturesMatch at h
  unfold waveE_e20_covers_htlcs
  rw [h, List.length_map]

/-- The per-output relation also gives index-level access: the signature at
wire position `i` is exactly the signature assigned to HTLC output `i`. -/
theorem htlc_signature_at_index {m : CommitmentSigned} {c : Commitment}
    {sigAt : CommitmentHTLCOutput → EcdsaSig}
    (h : HtlcSignaturesMatch m c sigAt) (i : Nat)
    (hi : i < c.htlcs.length) :
    m.htlcSignatures[i]? = some (sigAt c.htlcs[i]) := by
  unfold HtlcSignaturesMatch at h
  rw [h, List.getElem?_map, List.getElem?_eq_getElem hi]
  rfl

/-- A commitment with a repeated HTLC output and two distinct signatures:
the positional count matches, but no per-output signature family can produce
the wire list.  Thus E20's equal-length predicate is strictly weaker than
"one signature bound to each output" and does not identify the HTLC *set*. -/
def duplicateHtlcCommitment : Commitment :=
  waveE_e20_commitmentWith 2 0

/-- The wire record with two distinct HTLC signatures. -/
def duplicateHtlcMessage : CommitmentSigned where
  channelId := ChannelId.zero
  signature := ⟨ByteArray.empty⟩
  htlcSignatures := [⟨ByteArray.empty⟩, ⟨ByteArray.mk #[1]⟩]

theorem duplicate_htlc_count_coverage_not_binding :
    waveE_e20_covers_htlcs duplicateHtlcMessage duplicateHtlcCommitment ∧
      ∀ sigAt : CommitmentHTLCOutput → EcdsaSig,
        ¬ HtlcSignaturesMatch duplicateHtlcMessage duplicateHtlcCommitment sigAt := by
  constructor
  · unfold waveE_e20_covers_htlcs
    simp [duplicateHtlcMessage, duplicateHtlcCommitment,
      waveE_e20_commitmentWith]
  · intro sigAt hm
    unfold HtlcSignaturesMatch at hm
    have h0 := congrArg (fun l : List EcdsaSig => l[0]?) hm
    have h1 := congrArg (fun l : List EcdsaSig => l[1]?) hm
    simp [duplicateHtlcMessage, duplicateHtlcCommitment,
      waveE_e20_commitmentWith] at h0 h1
    have hsz0 := congrArg (fun s : EcdsaSig => s.bytes.size) h0
    have hsz1 := congrArg (fun s : EcdsaSig => s.bytes.size) h1
    have hone : (ByteArray.mk #[1]).size = 1 := by decide
    simp at hsz0
    rw [hone] at hsz1
    omega

/-! ## 4. Honest construction from a commitment state -/

/-- The BOLT 3 formula fee, set as the commitment's fee.  This is the
construction half of "the fee is the residual": the caller supplies the
commitment outputs and this function sets `feeSat` to the formula value. -/
def withFormulaFee (r : FeeRate) (c : Commitment) : Commitment :=
  { c with feeSat := (commitmentFee r c).val }

@[simp] theorem withFormulaFee_fee (r : FeeRate) (c : Commitment) :
    (withFormulaFee r c).feeSat = (commitmentFee r c).val := rfl

@[simp] theorem withFormulaFee_htlcs (r : FeeRate) (c : Commitment) :
    (withFormulaFee r c).htlcs = c.htlcs := rfl

@[simp] theorem withFormulaFee_anchorOutputs (r : FeeRate) (c : Commitment) :
    (withFormulaFee r c).anchorOutputs = c.anchorOutputs := rfl

theorem commitmentFee_withFormulaFee (r : FeeRate) (c : Commitment) :
    commitmentFee r (withFormulaFee r c) = commitmentFee r c := rfl

/-- The canonical-fee commitment satisfies the BOLT 3 fee equation by
construction. -/
theorem coversFee_withFormulaFee (r : FeeRate) (c : Commitment) :
    waveE_e20_covers_fee r (withFormulaFee r c) := by
  unfold waveE_e20_covers_fee
  rw [commitmentFee_withFormulaFee]
  rfl

/-- The honest `commitment_signed` built from a commitment state: the channel
id and commitment signature are supplied, and the HTLC-signature list is the
per-output signature family applied to the commitment's HTLC outputs. -/
def commitmentSignedOfState (channelId : ChannelId) (commitSig : EcdsaSig)
    (sigAt : CommitmentHTLCOutput → EcdsaSig) (c : Commitment) :
    CommitmentSigned where
  channelId := channelId
  signature := commitSig
  htlcSignatures := c.htlcs.map sigAt

@[simp] theorem commitmentSignedOfState_htlcSignatures
    (channelId : ChannelId) (commitSig : EcdsaSig)
    (sigAt : CommitmentHTLCOutput → EcdsaSig) (c : Commitment) :
    (commitmentSignedOfState channelId commitSig sigAt c).htlcSignatures =
      c.htlcs.map sigAt := rfl

@[simp] theorem commitmentSignedOfState_signatures
    (channelId : ChannelId) (commitSig : EcdsaSig)
    (sigAt : CommitmentHTLCOutput → EcdsaSig) (c : Commitment) :
    signatures (.commitmentSigned
        (commitmentSignedOfState channelId commitSig sigAt c)) =
      commitSig :: c.htlcs.map sigAt := rfl

/-- The constructed message covers the state it was built from. -/
theorem commitment_signed_covers_constructed
    (channelId : ChannelId) (commitSig : EcdsaSig)
    (sigAt : CommitmentHTLCOutput → EcdsaSig) (r : FeeRate)
    (c : Commitment) :
    waveE_e20_commitment_signed_covers
      (commitmentSignedOfState channelId commitSig sigAt
        (withFormulaFee r c)) r (withFormulaFee r c) := by
  refine ⟨?_, coversFee_withFormulaFee r c⟩
  exact coversHtlcs_of_match (by
    unfold HtlcSignaturesMatch commitmentSignedOfState
    rfl)

/-- The constructed message has exactly the BOLT 2 shape and passes the
wave-A decoder bounds when the supplied signatures are DER-sized and the
payload fits BOLT 1's two-byte length field.  This shows the construction is
not vacuous: coverage is compatible with `wellFormed`. -/
theorem wellFormed_commitmentSignedOfState
    (channelId : ChannelId) (hchannel : channelId.Valid)
    (commitSig : EcdsaSig)
    (sigAt : CommitmentHTLCOutput → EcdsaSig) (c : Commitment)
    (hcommit : commitSig.bytes.size ≤ 73)
    (hhtlcs : ∀ s ∈ c.htlcs.map sigAt, s.bytes.size ≤ 73)
    (hlen : 34 + commitSig.bytes.size + sigListLen (c.htlcs.map sigAt) ≤ 65535) :
    wellFormed (.commitmentSigned
      (commitmentSignedOfState channelId commitSig sigAt c)) := by
  refine ⟨?_, ?_, ?_, trivial⟩
  · simpa [msgLength, sigLen, commitmentSignedOfState] using hlen
  · refine ⟨?_, ?_⟩
    · intro c' hc'
      simp [channelId?, commitmentSignedOfState] at hc'
      subst hc'
      exact hchannel
    · intro p hp
      simp [pubKeys] at hp
  · unfold sigsValid
    intro s hs
    rw [commitmentSignedOfState_signatures] at hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact hcommit
    · exact hhtlcs s hs

/-! ## 5. Derivation from state equations (without assuming coverage) -/

/-- The formula fee is exactly the funding residual after the outputs: the
BOLT 3 construction equation, stated on the commitment state.  It mentions
neither `c.feeSat` nor the coverage predicate. -/
def FeeIsFundingResidual (r : FeeRate) (c : Commitment) : Prop :=
  c.totalOutputValue + (commitmentFee r c).val = c.fundingValueSat

/-- Conservation plus the residual equation force the commitment's fee to be
the BOLT 3 formula fee.  This is the fee half of LN-PR-004 derived from two
independent state equations, not assumed. -/
theorem coversFee_of_conserved_of_residual
    (r : FeeRate) (c : Commitment)
    (hcons : CommitmentConserved c)
    (hres : FeeIsFundingResidual r c) :
    waveE_e20_covers_fee r c := by
  unfold CommitmentConserved at hcons
  unfold FeeIsFundingResidual at hres
  unfold waveE_e20_covers_fee
  omega

/-- **LN-PR-004, positive direction.**  A wire record whose HTLC-signature
list is the per-output image of the commitment's HTLC outputs, together with
the BOLT 3 conservation equation and the formula-fee residual equation for
the commitment state, covers exactly that HTLC set and pays exactly the
formula fee.

The hypotheses are not the conclusion: `hsigs` is a list identity about *which
signature signs which output*; `hcons` and `hres` are value equations about
the commitment.  `waveE_e20_commitment_signed_covers` is the conjunction of a
length equality and a fee equality, neither of which is assumed. -/
theorem commitment_signed_covers_of_state
    (m : CommitmentSigned) (r : FeeRate) (c : Commitment)
    (sigAt : CommitmentHTLCOutput → EcdsaSig)
    (hsigs : HtlcSignaturesMatch m c sigAt)
    (hcons : CommitmentConserved c)
    (hres : FeeIsFundingResidual r c) :
    waveE_e20_commitment_signed_covers m r c :=
  ⟨coversHtlcs_of_match hsigs, coversFee_of_conserved_of_residual r c hcons hres⟩

/-- **Catalog-shaped form of the positive direction.**  Under the same
non-circular hypotheses, plus BOLT 1 well-formedness, the exact bundled
conclusion of the old wrapper holds: the HTLC-signature count matches the
HTLC-output count, the wire carries `#htlcs + 1` signatures, the payload is
bounded by `34 + 73 + 73 * #htlcs`, and the fee is the formula fee. -/
theorem commitment_signed_covers_exact_of_state
    (m : CommitmentSigned) (r : FeeRate) (c : Commitment)
    (sigAt : CommitmentHTLCOutput → EcdsaSig)
    (hsigs : HtlcSignaturesMatch m c sigAt)
    (hcons : CommitmentConserved c)
    (hres : FeeIsFundingResidual r c)
    (hwf : wellFormed (.commitmentSigned m)) :
    m.htlcSignatures.length = c.htlcs.length ∧
      (signatures (.commitmentSigned m)).length = c.htlcs.length + 1 ∧
      msgLength (.commitmentSigned m) ≤ 34 + 73 + 73 * c.htlcs.length ∧
      c.feeSat = (commitmentFee r c).val :=
  waveE_e20_commitment_signed_covers_exact m r c
    (commitment_signed_covers_of_state m r c sigAt hsigs hcons hres) hwf

/-! ## 6. Negative results: what the wire record cannot determine -/

/-- A one-HTLC-signature message used by the non-derivability theorem. -/
def oneHtlcSigMessage : CommitmentSigned where
  channelId := ChannelId.zero
  signature := ⟨ByteArray.empty⟩
  htlcSignatures := [⟨ByteArray.empty⟩]

/-- **No total wire-to-commitment decoder satisfies coverage for every
feerate.**  The `commitment_signed` record has no fee and no feerate field;
a fixed commitment `f m` has a fixed `feeSat`, while the BOLT 3 formula fee
grows with the feerate.  Hence the fee half of LN-PR-004 is not a property of
the wire record alone, which is exactly why the positive theorem takes the
commitment state and its value equations as parameters. -/
theorem no_wire_determined_coverage :
    ¬ ∃ f : CommitmentSigned → Commitment,
        ∀ (m : CommitmentSigned) (r : FeeRate),
          waveE_e20_commitment_signed_covers m r (f m) := by
  rintro ⟨f, hf⟩
  let c : Commitment := f oneHtlcSigMessage
  have hcount : c.htlcs.length = 1 := by
    have h := (hf oneHtlcSigMessage ⟨0⟩).1
    unfold waveE_e20_covers_htlcs at h
    dsimp only [c]
    simpa [oneHtlcSigMessage] using h.symm
  have hfee0 : c.feeSat = 0 := by
    have h := (hf oneHtlcSigMessage ⟨0⟩).2
    unfold waveE_e20_covers_fee at h
    simpa [commitmentFee, feeForWeight] using h
  have hbig : (commitmentFee ⟨1000000⟩ c).val = 1000 * c.weight.val := by
    unfold commitmentFee feeForWeight
    have hmul : 1000000 * c.weight.val = 1000 * (1000 * c.weight.val) := by
      show (1000 * 1000) * c.weight.val = 1000 * (1000 * c.weight.val)
      rw [Nat.mul_assoc]
    rw [hmul]
    exact Nat.mul_div_right (1000 * c.weight.val) (by decide : 0 < 1000)
  have hfeeBig : c.feeSat = 1000 * c.weight.val := by
    have h := (hf oneHtlcSigMessage ⟨1000000⟩).2
    unfold waveE_e20_covers_fee at h
    rw [hbig] at h
    exact h
  have hw : 0 < c.weight.val := by
    unfold Commitment.weight commitmentWeight commitmentBaseWeight
      commitmentHtlcWeight
    rw [hcount]
    cases c.anchorOutputs <;> simp <;> decide
  omega

/-- **No selector recovers the HTLC set from a covering message.**  E20's
counterexample gives one message covering two commitments with different HTLC
lists, so any function from messages to HTLC lists that is correct on all
covered commitments would have to return both lists. -/
theorem no_coverage_htlc_selector :
    ¬ ∃ f : CommitmentSigned → List CommitmentHTLCOutput,
        ∀ (m : CommitmentSigned) (c : Commitment),
          waveE_e20_covers_htlcs m c → c.htlcs = f m := by
  rintro ⟨f, hf⟩
  obtain ⟨m, c₁, c₂, hne, hc₁, hc₂⟩ :=
    waveE_e20_same_message_different_htlc_sets
  apply hne
  rw [hf m c₁ hc₁, hf m c₂ hc₂]

/-- **A well-formed message need not cover any non-empty commitment.**  The
empty-signature message is accepted by the decoder (DER lengths only), but it
cannot cover a commitment with one HTLC output.  Thus `wellFormed` does not
imply coverage either. -/
theorem wellFormed_message_can_fail_coverage :
    wellFormed (.commitmentSigned waveE_e20_emptyCommitmentSigned) ∧
      ¬ waveE_e20_commitment_signed_covers
          waveE_e20_emptyCommitmentSigned ⟨0⟩
          (waveE_e20_commitmentWith 1 0) :=
  ⟨waveE_e20_wellFormed_empty_signatures,
    waveE_e20_empty_signatures_do_not_cover ⟨0⟩ _
      (by simp [waveE_e20_commitmentWith])⟩

/-- A commitment with no HTLCs and canonical zero fee at feerate zero. -/
def zeroHtlcZeroFeeCommitment : Commitment :=
  withFormulaFee ⟨0⟩ (waveE_e20_commitmentWith 0 0)

/-- **The same well-formed wire record is compatible with different fees.**
The empty-signature message covers the canonical zero-fee commitment but not
the same commitment with `feeSat = 1`; both commitments have the same HTLC
set (empty) and the same output count.  So the fee half of coverage is a
statement about the off-wire commitment state, not about the message. -/
theorem same_message_different_fees :
    ∃ (m : CommitmentSigned) (c₁ c₂ : Commitment),
      c₁.feeSat ≠ c₂.feeSat ∧
        waveE_e20_commitment_signed_covers m ⟨0⟩ c₁ ∧
        ¬ waveE_e20_commitment_signed_covers m ⟨0⟩ c₂ := by
  let c₁ : Commitment := zeroHtlcZeroFeeCommitment
  let c₂ : Commitment := { c₁ with feeSat := 1 }
  have hfee1 : c₁.feeSat = 0 := by
    unfold c₁ zeroHtlcZeroFeeCommitment withFormulaFee commitmentFee
      feeForWeight
    simp
  refine ⟨waveE_e20_emptyCommitmentSigned, c₁, c₂, ?_, ?_, ?_⟩
  · rw [hfee1]
    simp [c₂]
  · refine ⟨?_, ?_⟩
    · dsimp only [c₁, zeroHtlcZeroFeeCommitment]
      simp [waveE_e20_covers_htlcs, waveE_e20_emptyCommitmentSigned,
        waveE_e20_commitmentWith, withFormulaFee]
    · dsimp only [c₁, zeroHtlcZeroFeeCommitment]
      exact coversFee_withFormulaFee ⟨0⟩ (waveE_e20_commitmentWith 0 0)
  · intro hc
    have hcov := hc.2
    unfold waveE_e20_covers_fee at hcov
    have hfee : (commitmentFee ⟨0⟩ c₂).val = 0 := by
      unfold commitmentFee feeForWeight
      simp
    simp [c₂, hfee] at hcov

/-! ## 7. Summary -/

/-- Bundled faithful reading of LN-PR-004.  The positive direction is
`commitment_signed_covers_of_state` (with `hsigs`, `hcons`, `hres` as the
explicit bridges); the wire record alone determines neither the fee nor the
HTLC set, and well-formedness does not force coverage.

This is the theorem-level statement a retargeted LN-PR-004 should cite: it
does not assume `waveE_e20_commitment_signed_covers`, and its negative
conjuncts are the precise remaining gaps. -/
theorem commitment_signed_coverage_summary :
    (∀ (m : CommitmentSigned) (r : FeeRate) (c : Commitment)
        (sigAt : CommitmentHTLCOutput → EcdsaSig),
        HtlcSignaturesMatch m c sigAt →
        CommitmentConserved c →
        FeeIsFundingResidual r c →
        waveE_e20_commitment_signed_covers m r c) ∧
      (∀ (channelId : ChannelId) (commitSig : EcdsaSig)
          (sigAt : CommitmentHTLCOutput → EcdsaSig) (r : FeeRate)
          (c : Commitment),
        waveE_e20_commitment_signed_covers
          (commitmentSignedOfState channelId commitSig sigAt
            (withFormulaFee r c)) r (withFormulaFee r c)) ∧
      (¬ ∃ f : CommitmentSigned → Commitment,
          ∀ (m : CommitmentSigned) (r : FeeRate),
            waveE_e20_commitment_signed_covers m r (f m)) ∧
      (¬ ∃ f : CommitmentSigned → List CommitmentHTLCOutput,
          ∀ (m : CommitmentSigned) (c : Commitment),
            waveE_e20_covers_htlcs m c → c.htlcs = f m) :=
  ⟨commitment_signed_covers_of_state,
    commitment_signed_covers_constructed,
    no_wire_determined_coverage,
    no_coverage_htlc_selector⟩

end LnLean.Proofs.ProtocolCoverageTargets
