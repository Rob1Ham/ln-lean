/-
# Arbitrary-preimage coverage and the eight field hypotheses (`PR-02`)

This module makes the `PR-02` boundary explicit rather than folding an
arbitrary BIP 143 preimage into a transaction-derived one.

## The eight field hypotheses

`FieldAgreement p tx nIn amount` is the eight-field context under which an
arbitrary `Bip143Preimage` is *exactly* the transaction-derived preimage of
`tx`:

1. `version`
2. `hashPrevouts`
3. `hashSequence`
4. `outpoint` (32-byte txid and 4-byte index, together)
5. `nSequence`
6. `hashOutputs`
7. `nLockTime`
8. `amount`

These are precisely the hypotheses of
`LnLean.Bitcoin.Sighash.bL_encode_eq_bip143MsgL`, restated on the exact-wire
`Bip143Preimage` of `SighashTargets` §13.  The main characterization is

```text
FieldAgreement p tx nIn amount
  ↔ p = Bip143Preimage.ofTx tx nIn p.scriptCode p.sighashType p.amountSat
      ∧ (p.amountSat.toNat : Int) = amount
```

so "wire-only coverage" is not taken as primitive: it is equivalent to the
preimage being the transaction-derived one plus the amount context.

## What is proved

* `FieldAgreement.bytes_eq`: the conditional byte equality with the vendored
  `Bitcoin.SigHash.bip143MsgL`.
* `FieldAgreement.digest_eq` and `FieldAgreement.digest_eq_vendor`: the digest
  (and the vendored `signatureHashBip143Impl` for in-range `nIn`) under the
  hypotheses.
* `wireSignatureCovers_of_preimage`: a signature over an arbitrary preimage's
  digest transfers to the exact wire transaction digest exactly under the
  eight hypotheses.  This is the wire-only coverage transfer; there is no
  silent identification of the two preimages.
* `counterPreimageLocktime_bytes_ne`: dropping the `nLockTime` hypothesis
  breaks the byte equality on a concrete, decidable witness.
* `legacy_projection_not_determine_htlc_coverage`: the legacy
  `CommitmentSigned` projection still does not determine the HTLC outputs,
  even when it comes from a `CommitmentSignedFull`; the wire only pins the
  signature *count* (`coverage_pins_only_htlc_count`).
* `fieldAgreement_scriptCode_free`: the eight hypotheses do **not** constrain
  `scriptCode`, so the 20-byte HASH160 images and the spent script are
  explicit context, not wire-derived.
* Display-order txid: the preimage outpoint field is the internal-order wire
  field; a display-order value fails `FieldAgreement`
  (`displayOrderPreimage_not_fieldAgreement`).
* Amount: the preimage amount is the gross spent HTLC value, not the produced
  second-stage output value (`vectorHtlcSpend_amount_is_gross`).

## What is not proved

* No collision resistance / digest injectivity.  Byte equality is proved, not
  signature binding; `wireSignatureCovers_of_preimage` is a transfer of a
  verification result, not an unforgeability claim.
* `scriptCode` is an opaque parameter.  This module does not derive it from
  keys or from the 20-byte images; `HtlcSpend.WellFormed` keeps those images
  as explicit 20-byte inputs.
* The legacy `CommitmentSigned` record has no decoder to a commitment; the
  negative results are retained, not weakened.

Anchors: BIP 143 §3–6; BOLT 3 §"Commitment Transaction" and §"HTLC Outputs";
`LnLean/Bitcoin/Sighash.lean` (`bL_encode_eq_bip143MsgL`),
`LnLean/Proofs/Channel/SighashTargets.lean` §13 (`Bip143Preimage`),
`LnLean/Proofs/Channel/HtlcPreimageTargets.lean` (`HtlcSpend`,
`displayTxid`, `internalTxid`).
-/

import LnLean.Proofs.Channel.HtlcPreimageTargets

namespace LnLean.Proofs.Channel.PreimageCoverageTargets

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open LnLean
open LnLean.Channel
open LnLean.Protocol
open LnLean.Proofs
open LnLean.Proofs.ProtocolCoverageTargets
open LnLean.Proofs.WaveE.E20
open LnLean.Proofs.Channel.SighashTargets
open LnLean.Proofs.Channel.HtlcPreimageTargets
open Bitcoin.Data
open Bitcoin.Serialization

/-! ## 1. The eight explicit field hypotheses -/

/-- **The eight field-agreement hypotheses.**  An arbitrary preimage `p`
records exactly the wire data of `tx` at input `nIn` and the spent `amount`:
version, the three BIP 143 sub-hashes, the outpoint (txid and index),
`nSequence`, `nLockTime`, and the amount.  `scriptCode` is deliberately not a
hypothesis: it is free context in BIP 143 (and in the vendored encoder). -/
structure FieldAgreement (p : Bip143Preimage) (tx : Bitcoin.Data.Tx) (nIn : Nat)
    (amount : Bitcoin.Data.Amount) : Prop where
  /-- Field 1: transaction version. -/
  version_eq : p.version = tx.version.toUInt32
  /-- Field 2: `hashPrevouts`. -/
  hashPrevouts_eq :
    bL p.hashPrevouts = Bitcoin.SigHash.hashPrevoutsL tx p.sighashType
  /-- Field 3: `hashSequence`. -/
  hashSequence_eq :
    bL p.hashSequence = Bitcoin.SigHash.hashSequenceL tx p.sighashType
  /-- Field 4: the outpoint, txid and index. -/
  outpoint_eq :
    p.outpointTxid =
        (tx.vin.getD nIn LnLean.Bitcoin.Sighash.dummyTxIn).prevout.hash ∧
      p.outpointIndex =
        (tx.vin.getD nIn LnLean.Bitcoin.Sighash.dummyTxIn).prevout.n
  /-- Field 5: the signing input's `nSequence`. -/
  sequence_eq :
    p.sequence = (tx.vin.getD nIn LnLean.Bitcoin.Sighash.dummyTxIn).sequence
  /-- Field 6: `hashOutputs`. -/
  hashOutputs_eq :
    bL p.hashOutputs = Bitcoin.SigHash.hashOutputsL tx nIn p.sighashType
  /-- Field 7: `nLockTime`. -/
  locktime_eq : p.locktime = tx.locktime
  /-- Field 8: the spent amount (only its non-negative `Nat` image enters the
  serialized preimage). -/
  amount_eq : (p.amountSat.toNat : Int) = amount

/-- The outpoint hypothesis, packaged as the `OutPoint` equality used by the
core encoder lemma. -/
theorem FieldAgreement.outpoint_toPreimage {p : Bip143Preimage}
    {tx : Bitcoin.Data.Tx} {nIn : Nat} {amount : Bitcoin.Data.Amount}
    (h : FieldAgreement p tx nIn amount) :
    p.toPreimage.outpoint =
      (tx.vin.getD nIn LnLean.Bitcoin.Sighash.dummyTxIn).prevout := by
  obtain ⟨htxid, hidx⟩ := h.outpoint_eq
  simp [Bip143Preimage.toPreimage, htxid, hidx]

/-- **The transaction-derived preimage satisfies all eight hypotheses.**  This
is the non-vacuous direction: the hypotheses are not an extra assumption on
the honest construction. -/
theorem ofTx_satisfies_fieldAgreement (tx : Bitcoin.Data.Tx) (nIn : Nat)
    (scriptCode : ByteArray) (ht : UInt32) (amountSat : UInt64) :
    FieldAgreement (Bip143Preimage.ofTx tx nIn scriptCode ht amountSat) tx nIn
      ((amountSat.toNat : Int)) := by
  refine
    { version_eq := rfl
      hashPrevouts_eq := ?_
      hashSequence_eq := ?_
      outpoint_eq := ⟨rfl, rfl⟩
      sequence_eq := rfl
      hashOutputs_eq := ?_
      locktime_eq := rfl
      amount_eq := rfl }
  · simp [Bip143Preimage.ofTx, LnLean.Bitcoin.Sighash.bL_hashPrevoutsOf]
  · simp [Bip143Preimage.ofTx, LnLean.Bitcoin.Sighash.bL_hashSequenceOf]
  · simp [Bip143Preimage.ofTx, LnLean.Bitcoin.Sighash.bL_hashOutputsOf]

/-- **The eight hypotheses are exactly the transaction-derived fields (plus
the amount context).**  The forward direction recovers the fields; the reverse
direction shows the hypotheses add nothing beyond being `ofTx` and the amount
equality.  This is the precise sense in which the hypotheses are complete. -/
theorem fieldAgreement_iff_eq_ofTx_and_amount (p : Bip143Preimage)
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Bitcoin.Data.Amount) :
    FieldAgreement p tx nIn amount ↔
      p = Bip143Preimage.ofTx tx nIn p.scriptCode p.sighashType p.amountSat ∧
        (p.amountSat.toNat : Int) = amount := by
  constructor
  · intro h
    refine ⟨?_, h.amount_eq⟩
    cases p with
    | mk version hprev hseq otx oi sc amt seq hout lock ht =>
      have hprev' : hprev = LnLean.Bitcoin.Sighash.hashPrevoutsOf tx ht := by
        apply bL_inj
        rw [h.hashPrevouts_eq, LnLean.Bitcoin.Sighash.bL_hashPrevoutsOf]
      have hseq' : hseq = LnLean.Bitcoin.Sighash.hashSequenceOf tx ht := by
        apply bL_inj
        rw [h.hashSequence_eq, LnLean.Bitcoin.Sighash.bL_hashSequenceOf]
      have hout' : hout = LnLean.Bitcoin.Sighash.hashOutputsOf tx nIn ht := by
        apply bL_inj
        rw [h.hashOutputs_eq, LnLean.Bitcoin.Sighash.bL_hashOutputsOf]
      obtain ⟨hotx, hoi⟩ := h.outpoint_eq
      simp only [Bip143Preimage.ofTx]
      rw [Bip143Preimage.mk.injEq]
      exact ⟨h.version_eq, hprev', hseq', hotx, hoi, rfl, rfl,
        h.sequence_eq, hout', h.locktime_eq, rfl⟩
  · rintro ⟨hp, hamt⟩
    have h := ofTx_satisfies_fieldAgreement tx nIn p.scriptCode
      p.sighashType p.amountSat
    rw [hp]
    rwa [hamt] at h

/-- Self-amount corollary: with the amount fixed to the preimage's own value,
the hypotheses are exactly `p = ofTx …`. -/
theorem fieldAgreement_iff_eq_ofTx (p : Bip143Preimage) (tx : Bitcoin.Data.Tx)
    (nIn : Nat) :
    FieldAgreement p tx nIn (p.amountSat.toNat : Int) ↔
      p = Bip143Preimage.ofTx tx nIn p.scriptCode p.sighashType p.amountSat := by
  rw [fieldAgreement_iff_eq_ofTx_and_amount]
  exact ⟨fun h => h.1, fun h => ⟨h, rfl⟩⟩

/-! ## 2. Conditional byte, digest, and signature coverage -/

/-- **Conditional wire-only byte coverage.**  Under exactly the eight field
hypotheses, an arbitrary preimage is byte-equal to the vendored BIP 143
preimage of the wire transaction. -/
theorem FieldAgreement.bytes_eq {p : Bip143Preimage} {tx : Bitcoin.Data.Tx}
    {nIn : Nat} {amount : Bitcoin.Data.Amount}
    (h : FieldAgreement p tx nIn amount) :
    bL p.preimageBytes =
      Bitcoin.SigHash.bip143MsgL tx nIn (bL p.scriptCode) p.sighashType amount := by
  rw [Bip143Preimage.preimageBytes_eq_encode]
  exact LnLean.Bitcoin.Sighash.bL_encode_eq_bip143MsgL p.toPreimage tx nIn amount
    h.version_eq h.hashPrevouts_eq h.hashSequence_eq h.outpoint_toPreimage
    h.sequence_eq h.hashOutputs_eq h.locktime_eq h.amount_eq

/-- The same equality at the vendored double-SHA-256 digest. -/
theorem FieldAgreement.digest_eq {p : Bip143Preimage} {tx : Bitcoin.Data.Tx}
    {nIn : Nat} {amount : Bitcoin.Data.Amount}
    (h : FieldAgreement p tx nIn amount) :
    Bitcoin.SigHash.dshaL (bL p.preimageBytes) =
      Bitcoin.SigHash.dshaL
        (Bitcoin.SigHash.bip143MsgL tx nIn (bL p.scriptCode) p.sighashType
          amount) := by
  rw [h.bytes_eq]

/-- For an in-range input the arbitrary preimage's model digest is the
vendored `signatureHashBip143Impl` of the wire transaction.  The amount context
is used exactly as recorded by the eighth hypothesis. -/
theorem FieldAgreement.digest_eq_vendor {p : Bip143Preimage}
    {tx : Bitcoin.Data.Tx} {nIn : Nat} {amount : Bitcoin.Data.Amount}
    (h : FieldAgreement p tx nIn amount) (hr : nIn < tx.vin.length) :
    LnLean.Bitcoin.Sighash.digest p.toPreimage =
      Bitcoin.SigHash.signatureHashBip143Impl tx nIn (bL p.scriptCode)
        p.sighashType amount := by
  have hamt : (p.amountSat.toNat : Int) = amount := h.amount_eq
  have hfa : FieldAgreement p tx nIn ((p.amountSat.toNat : Int)) := by
    simpa [← hamt] using h
  have hp : p =
      Bip143Preimage.ofTx tx nIn p.scriptCode p.sighashType p.amountSat :=
    (fieldAgreement_iff_eq_ofTx p tx nIn).1 hfa
  rw [hp]
  rw [Bip143Preimage.digest_eq_sighashWitnessV0_ofTx tx nIn p.scriptCode
    p.sighashType p.amountSat hr]
  exact congrArg
    (fun a => Bitcoin.SigHash.signatureHashBip143Impl tx nIn
      (bL p.scriptCode) p.sighashType a) hamt

/-- A signature verifying over an arbitrary preimage's digest. -/
def PreimageSignatureCovers
    (verify : PubKey → ByteArray → EcdsaSig → Bool)
    (pk : PubKey) (domain : ByteArray) (p : Bip143Preimage)
    (sig : EcdsaSig) : Prop :=
  verify pk (domain ++ Bitcoin.SigHash.dshaL (bL p.preimageBytes)) sig = true

/-- A signature verifying over the exact wire transaction's vendored BIP 143
digest.  This is the wire-only object: no arbitrary preimage remains. -/
def WireSignatureCovers
    (verify : PubKey → ByteArray → EcdsaSig → Bool)
    (pk : PubKey) (domain : ByteArray) (tx : Bitcoin.Data.Tx) (nIn : Nat)
    (scriptCode : ByteArray) (ht : UInt32) (amount : Bitcoin.Data.Amount)
    (sig : EcdsaSig) : Prop :=
  verify pk
    (domain ++ Bitcoin.SigHash.dshaL
      (Bitcoin.SigHash.bip143MsgL tx nIn (bL scriptCode) ht amount)) sig = true

/-- **Conditional wire-only coverage transfer.**  If an arbitrary preimage
records the eight wire fields and a signature verifies over that preimage's
digest, then the *same* verification holds over the exact wire transaction's
digest.  The hypotheses are load-bearing; see the counterexample below. -/
theorem wireSignatureCovers_of_preimage
    {verify : PubKey → ByteArray → EcdsaSig → Bool} {pk : PubKey}
    {domain : ByteArray} {p : Bip143Preimage} {sig : EcdsaSig}
    {tx : Bitcoin.Data.Tx} {nIn : Nat} {amount : Bitcoin.Data.Amount}
    (h : FieldAgreement p tx nIn amount)
    (hp : PreimageSignatureCovers verify pk domain p sig) :
    WireSignatureCovers verify pk domain tx nIn p.scriptCode p.sighashType
      amount sig := by
  unfold PreimageSignatureCovers at hp
  unfold WireSignatureCovers
  rw [← h.bytes_eq]
  exact hp

/-! ## 3. A dropped hypothesis: the `nLockTime` counterexample -/

/-- Concrete wire transaction used for the counterexample.  `SIGHASH_NONE |
ANYONECANPAY` (`0x82`) makes all three sub-hashes the BIP 143 zero vector, so
the bytes are kernel-decidable without evaluating SHA-256. -/
def counterTx : Bitcoin.Data.Tx :=
  { version := 2
    vin := [{ prevout := ⟨Bitcoin.Data.zeroBytes 32, 0⟩,
              scriptSig := Script.empty, sequence := 0 }]
    vout := []
    locktime := 5
    witness := [[]] }

/-- The counterexample preimage agrees with `counterTx` on seven fields but
records `nLockTime = 0` instead of `5`. -/
def counterPreimageLocktime : Bip143Preimage :=
  { version := 2
    hashPrevouts := LnLean.Bitcoin.Sighash.zeroHash
    hashSequence := LnLean.Bitcoin.Sighash.zeroHash
    outpointTxid := Bitcoin.Data.zeroBytes 32
    outpointIndex := 0
    scriptCode := ByteArray.empty
    amountSat := 0
    sequence := 0
    hashOutputs := LnLean.Bitcoin.Sighash.zeroHash
    locktime := 0
    sighashType := 0x82 }

/-- The seven hypotheses other than `nLockTime` hold on the witness. -/
theorem counterPreimageLocktime_seven :
    counterPreimageLocktime.version = counterTx.version.toUInt32 ∧
      bL counterPreimageLocktime.hashPrevouts =
        Bitcoin.SigHash.hashPrevoutsL counterTx 0x82 ∧
      bL counterPreimageLocktime.hashSequence =
        Bitcoin.SigHash.hashSequenceL counterTx 0x82 ∧
      (counterPreimageLocktime.outpointTxid =
          (counterTx.vin.getD 0 LnLean.Bitcoin.Sighash.dummyTxIn).prevout.hash ∧
        counterPreimageLocktime.outpointIndex =
          (counterTx.vin.getD 0 LnLean.Bitcoin.Sighash.dummyTxIn).prevout.n) ∧
      counterPreimageLocktime.sequence =
        (counterTx.vin.getD 0 LnLean.Bitcoin.Sighash.dummyTxIn).sequence ∧
      bL counterPreimageLocktime.hashOutputs =
        Bitcoin.SigHash.hashOutputsL counterTx 0 0x82 ∧
      (counterPreimageLocktime.amountSat.toNat : Int) = (0 : Int) := by
  decide

/-- Dropping `nLockTime` breaks `FieldAgreement`. -/
theorem counterPreimageLocktime_not_fieldAgreement :
    ¬ FieldAgreement counterPreimageLocktime counterTx 0 (0 : Int) := by
  intro h
  have hl := h.locktime_eq
  simp [counterPreimageLocktime, counterTx] at hl

/-- **Mechanized dropped-hypothesis negative.**  With all seven other fields
agreeing, the byte equality with the vendored encoder still fails.  The
`nLockTime` hypothesis is therefore necessary, not decorative. -/
theorem counterPreimageLocktime_bytes_ne :
    bL counterPreimageLocktime.preimageBytes ≠
      Bitcoin.SigHash.bip143MsgL counterTx 0
        (bL counterPreimageLocktime.scriptCode)
        counterPreimageLocktime.sighashType (0 : Int) := by
  decide

/-- The amount variant: all seven other fields agree with `counterTx`, but the
preimage records one satoshi while the wire context says zero. -/
def counterPreimageAmount : Bip143Preimage :=
  { counterPreimageLocktime with amountSat := 1, locktime := 5 }

/-- Dropping the amount hypothesis breaks `FieldAgreement`. -/
theorem counterPreimageAmount_not_fieldAgreement :
    ¬ FieldAgreement counterPreimageAmount counterTx 0 (0 : Int) := by
  intro h
  have ha := h.amount_eq
  simp [counterPreimageAmount, counterPreimageLocktime] at ha

/-- **The amount hypothesis is necessary too.**  With the other seven fields
agreeing, changing the spent amount changes the vendored preimage. -/
theorem counterPreimageAmount_bytes_ne :
    bL counterPreimageAmount.preimageBytes ≠
      Bitcoin.SigHash.bip143MsgL counterTx 0
        (bL counterPreimageAmount.scriptCode)
        counterPreimageAmount.sighashType (0 : Int) := by
  decide

/-! ## 4. Wire-only record coverage: what the legacy projection determines -/

/-- The legacy wire projection preserves exactly the number of HTLC
signatures; the per-entry identification data is forgotten. -/
@[simp] theorem wire_projection_signature_count (f : CommitmentSignedFull) :
    f.toCommitmentSigned.htlcSignatures.length = f.htlcEntries.length := by
  simp [CommitmentSignedFull.toCommitmentSigned]

/-- Under wire coverage the legacy record pins the *number* of HTLC outputs
(one signature per untrimmed output), and hence the number of signed entries.
It does not pin their values. -/
theorem coverage_pins_only_htlc_count (f : CommitmentSignedFull)
    (c : Commitment) (h : CoversHtlcOutputs f.toCommitmentSigned c) :
    c.htlcs.length = f.htlcEntries.length := by
  unfold CoversHtlcOutputs at h
  rw [Commitment.htlcOutputCount_commitmentOutputs] at h
  rw [wire_projection_signature_count] at h
  exact h.symm

/-- Two full records with the *same* legacy `CommitmentSigned` projection but
different HTLC output data.  The wire projection carries the same signature
list (hence the same count), so the difference is invisible on the legacy
wire record. -/
def sameSignature : EcdsaSig := ⟨ByteArray.empty⟩

def recordEntryA : SignedHtlcEntry :=
  { htlcId := 1
    amount := ⟨1000⟩
    paymentHash := ⟨ByteArray.empty⟩
    direction := .local
    htlcState := .offered
    cltvExpiry := 100
    signedDataDigest := ByteArray.empty
    signature := sameSignature }

def recordEntryB : SignedHtlcEntry :=
  { recordEntryA with amount := ⟨2000⟩ }

def recordFullA : CommitmentSignedFull :=
  { channelId := ChannelId.zero
    commitmentNumber := 0
    feePaid := ⟨0⟩
    commitmentDigest := ByteArray.empty
    commitmentSignature := sameSignature
    htlcEntries := [recordEntryA] }

def recordFullB : CommitmentSignedFull :=
  { recordFullA with htlcEntries := [recordEntryB] }

/-- **The legacy projection is not a coverage decoder, even for a full record.**
Same `commitment_signed` wire bytes (same signature list), different HTLC
outputs.  This complements the existing legacy no-decoder theorems: adding the
full record does not help if only its legacy projection is available. -/
theorem legacy_projection_not_determine_htlc_coverage :
    ∃ f₁ f₂ : CommitmentSignedFull,
      f₁.toCommitmentSigned = f₂.toCommitmentSigned ∧
        f₁.htlcEntries.map SignedHtlcEntry.toCommitmentHtlcOutput ≠
          f₂.htlcEntries.map SignedHtlcEntry.toCommitmentHtlcOutput := by
  refine ⟨recordFullA, recordFullB, ?_, ?_⟩
  · simp [recordFullA, recordFullB, recordEntryA, recordEntryB,
      CommitmentSignedFull.toCommitmentSigned]
  · simp [recordFullA, recordFullB, recordEntryA, recordEntryB,
      SignedHtlcEntry.toCommitmentHtlcOutput]
    decide

/-- The legacy no-decoder negative is preserved verbatim. -/
theorem legacy_wire_cannot_determine_coverage :
    ¬ ∃ g : CommitmentSigned → Commitment,
        ∀ (m : CommitmentSigned) (r : FeeRate),
          waveE_e20_commitment_signed_covers m r (g m) :=
  LnLean.Proofs.ProtocolWireTargets.legacy_wire_cannot_determine_coverage

/-! ## 5. The `scriptCode` and 20-byte hash-image boundary -/

/-- **The eight hypotheses leave `scriptCode` free.**  Updating only
`scriptCode` preserves every field hypothesis, because BIP 143 (and the
vendored encoder) treat the spent witness script as caller context.  In
particular the 20-byte HASH160 images inside a BOLT 3 HTLC witness script are
not wire-derived by this theorem. -/
theorem fieldAgreement_scriptCode_free (p : Bip143Preimage)
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Bitcoin.Data.Amount)
    (h : FieldAgreement p tx nIn amount) (sc₁ sc₂ : ByteArray)
    (hne : sc₁ ≠ sc₂) :
    FieldAgreement { p with scriptCode := sc₁ } tx nIn amount ∧
      FieldAgreement { p with scriptCode := sc₂ } tx nIn amount ∧
        ({ p with scriptCode := sc₁ } : Bip143Preimage).scriptCode ≠
          { p with scriptCode := sc₂ }.scriptCode := by
  refine ⟨?_, ?_, ?_⟩
  · exact
      { version_eq := h.version_eq
        hashPrevouts_eq := h.hashPrevouts_eq
        hashSequence_eq := h.hashSequence_eq
        outpoint_eq := h.outpoint_eq
        sequence_eq := h.sequence_eq
        hashOutputs_eq := h.hashOutputs_eq
        locktime_eq := h.locktime_eq
        amount_eq := h.amount_eq }
  · exact
      { version_eq := h.version_eq
        hashPrevouts_eq := h.hashPrevouts_eq
        hashSequence_eq := h.hashSequence_eq
        outpoint_eq := h.outpoint_eq
        sequence_eq := h.sequence_eq
        hashOutputs_eq := h.hashOutputs_eq
        locktime_eq := h.locktime_eq
        amount_eq := h.amount_eq }
  · simpa using hne

/-- The 20-byte hash images and the 143/136-byte witness scripts of the BOLT 3
second-stage spend are explicit context fields.  `HtlcSpend.WellFormed` fixes
the 20-byte images and 33-byte keys; the scriptCode sizes are computed from
those inputs. -/
theorem hash160_image_boundary (s : HtlcSpend) (hw : s.WellFormed) :
    s.revocationKeyHash160.size = 20 ∧
      s.paymentHash160.size = 20 ∧
      s.remoteHtlcKey.bytes.size = 33 ∧
      s.localHtlcKey.bytes.size = 33 ∧
      s.successScriptCode.size = 143 ∧
      s.timeoutScriptCode.size = 136 := by
  exact ⟨hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2.1,
    HtlcSpend.successScriptCode_size s hw,
    HtlcSpend.timeoutScriptCode_size s hw⟩

/-! ## 6. Display-order txid boundary -/

/-- A wire transaction whose input outpoint already holds the asymmetric
32-byte internal-order txid `vectorAsymmetricTxid`. -/
def displayTx : Bitcoin.Data.Tx :=
  { version := 2
    vin := [{ prevout := ⟨vectorAsymmetricTxid, 0⟩,
              scriptSig := Script.empty, sequence := 0 }]
    vout := []
    locktime := 0
    witness := [[]] }

/-- The transaction-derived preimage with the outpoint replaced by its
**display-order** (byte-reversed) form.  Everything else still agrees. -/
def displayOrderPreimage : Bip143Preimage :=
  { Bip143Preimage.ofTx displayTx 0 ByteArray.empty 0x82 0 with
    outpointTxid := displayTxid vectorAsymmetricTxid }

/-- The internal-order preimage satisfies all eight hypotheses. -/
theorem internalOrderPreimage_fieldAgreement :
    FieldAgreement (Bip143Preimage.ofTx displayTx 0 ByteArray.empty 0x82 0)
      displayTx 0 (0 : Int) :=
  ofTx_satisfies_fieldAgreement displayTx 0 ByteArray.empty 0x82 0

/-- **Display order is not the wire order.**  Substituting the RPC/display
txid for the internal-order field violates the outpoint hypothesis; the
conversion `internalTxid` is mandatory before constructing the preimage.  The
preimage and the vendored encoder insert the field verbatim, never reversed. -/
theorem displayOrderPreimage_not_fieldAgreement :
    ¬ FieldAgreement displayOrderPreimage displayTx 0 (0 : Int) := by
  intro h
  have hout := h.outpoint_eq.1
  simp [displayOrderPreimage, displayTx, Bip143Preimage.ofTx] at hout
  exact displayTxid_not_identity_witness hout

/-- Consequently the display-order preimage is not the transaction-derived
preimage: the eight hypotheses are not silently satisfied by a reversed
txid. -/
theorem displayOrderPreimage_ne_ofTx :
    displayOrderPreimage ≠
      Bip143Preimage.ofTx displayTx 0 ByteArray.empty 0x82 0 := by
  intro h
  exact displayOrderPreimage_not_fieldAgreement
    (h ▸ internalOrderPreimage_fieldAgreement)

/-- The field at offset 68 of an arbitrary preimage is whatever txid bytes the
preimage records; the eight-field characterization fixes it to the wire field
and never reverses it. -/
theorem fieldAgreement_outpoint_verbatim (p : Bip143Preimage)
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Bitcoin.Data.Amount)
    (h : FieldAgreement p tx nIn amount) :
    p.outpointTxid =
      (tx.vin.getD nIn LnLean.Bitcoin.Sighash.dummyTxIn).prevout.hash :=
  h.outpoint_eq.1

/-! ## 7. The amount boundary: spent gross value, not produced value -/

/-- The amount recorded by the HTLC preimage is the gross spent HTLC value
`amountSat`, while the produced second-stage output pays
`successWire.valueSat = paidValueSat = amountSat - secondStageFeeSat`.  These
are distinct BIP 143 contexts; identifying them would change the committed
amount. -/
theorem vectorHtlcSpend_amount_is_gross :
    (vectorHtlcSpend.successPreimage 0x82).amountSat = 7000 ∧
      vectorHtlcSpend.successWire.valueSat = 3485 ∧
        (7000 : UInt64) ≠ 3485 := by
  decide

/-- The `HtlcSpend` amount is explicit: the preimage records `s.amountSat`
even though the produced output's `valueSat` is `s.paidValueSat`. -/
theorem htlcSpend_amount_context (s : HtlcSpend) (ht : UInt32) :
    (s.successPreimage ht).amountSat = s.amountSat ∧
      s.successWire.valueSat = s.paidValueSat ∧
        s.paidValueSat =
          UInt64.ofNat (s.amountSat.toNat - s.secondStageFeeSat) :=
  ⟨rfl, rfl, rfl⟩

/-! ## 8. Summary -/

/-- Bundled faithful reading of the lane.

1. The eight field hypotheses are exactly the transaction-derived preimage
   (plus the amount context).
2. Under them, the arbitrary preimage is byte-equal to the vendored BIP 143
   preimage, hence digest-equal, hence a signature over its digest transfers
   to the wire transaction.
3. Dropping `nLockTime` is a mechanized failure of that conclusion; dropping
   the amount hypothesis is a second independent failure.
4. The legacy `CommitmentSigned` projection still does not determine HTLC
   coverage; it pins only the signature/output count.
5. `scriptCode` is free context, so the 20-byte HASH160 images are explicit.
6. A display-order txid violates the outpoint hypothesis; the wire field is
   internal order.
7. The preimage amount is the gross spent value, not the produced output
   value. -/
theorem preimage_coverage_summary :
    (∀ (p : Bip143Preimage) (tx : Bitcoin.Data.Tx) (nIn : Nat)
        (amount : Bitcoin.Data.Amount),
        FieldAgreement p tx nIn amount ↔
          p = Bip143Preimage.ofTx tx nIn p.scriptCode p.sighashType
              p.amountSat ∧
            (p.amountSat.toNat : Int) = amount) ∧
      (∀ (p : Bip143Preimage) (tx : Bitcoin.Data.Tx) (nIn : Nat)
        (amount : Bitcoin.Data.Amount),
        FieldAgreement p tx nIn amount →
          bL p.preimageBytes =
            Bitcoin.SigHash.bip143MsgL tx nIn (bL p.scriptCode)
              p.sighashType amount) ∧
      (∀ (verify : PubKey → ByteArray → EcdsaSig → Bool) (pk : PubKey)
        (domain : ByteArray) (p : Bip143Preimage) (sig : EcdsaSig)
        (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Bitcoin.Data.Amount),
        FieldAgreement p tx nIn amount →
          PreimageSignatureCovers verify pk domain p sig →
            WireSignatureCovers verify pk domain tx nIn p.scriptCode
              p.sighashType amount sig) ∧
      (¬ FieldAgreement counterPreimageLocktime counterTx 0 (0 : Int) ∧
        bL counterPreimageLocktime.preimageBytes ≠
          Bitcoin.SigHash.bip143MsgL counterTx 0
            (bL counterPreimageLocktime.scriptCode)
            counterPreimageLocktime.sighashType (0 : Int)) ∧
      (¬ FieldAgreement counterPreimageAmount counterTx 0 (0 : Int) ∧
        bL counterPreimageAmount.preimageBytes ≠
          Bitcoin.SigHash.bip143MsgL counterTx 0
            (bL counterPreimageAmount.scriptCode)
            counterPreimageAmount.sighashType (0 : Int)) ∧
      (∃ f₁ f₂ : CommitmentSignedFull,
        f₁.toCommitmentSigned = f₂.toCommitmentSigned ∧
          f₁.htlcEntries.map SignedHtlcEntry.toCommitmentHtlcOutput ≠
            f₂.htlcEntries.map SignedHtlcEntry.toCommitmentHtlcOutput) ∧
      (¬ FieldAgreement displayOrderPreimage displayTx 0 (0 : Int)) ∧
      ((vectorHtlcSpend.successPreimage 0x82).amountSat = 7000 ∧
        vectorHtlcSpend.successWire.valueSat = 3485) :=
  ⟨fieldAgreement_iff_eq_ofTx_and_amount,
    fun _p _tx _nIn _amount h => h.bytes_eq,
    fun _verify _pk _domain _p _sig _tx _nIn _amount h hp =>
      wireSignatureCovers_of_preimage h hp,
    ⟨counterPreimageLocktime_not_fieldAgreement,
      counterPreimageLocktime_bytes_ne⟩,
    ⟨counterPreimageAmount_not_fieldAgreement,
      counterPreimageAmount_bytes_ne⟩,
    legacy_projection_not_determine_htlc_coverage,
    displayOrderPreimage_not_fieldAgreement,
    ⟨vectorHtlcSpend_amount_is_gross.1,
      vectorHtlcSpend_amount_is_gross.2.1⟩⟩

end LnLean.Proofs.Channel.PreimageCoverageTargets
