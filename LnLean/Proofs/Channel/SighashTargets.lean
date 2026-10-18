/-
# Commitment sighash targets — BOLT 3 serializer, `SighashProduces`, C3 binding (PR-02, PR-01)

**Catalog issues.**

* `PR-02` (P1): the legacy `CommitmentSigned` wire record has no data with
  which to determine what it covers, and the wave-4 `CommitmentSignedFull`
  record still carried the commitment digest and per-HTLC signed-data digest as
  *explicit data*.  There was no BOLT 3 sighash serializer and no C3
  verification, so `sigAt`/digests were supplied rather than derived.
* `PR-01` (P1): `FundingSigningLaw` / `KeyBinding` are explicit hypotheses; C3
  alone does not give signing completeness or key attribution.

**Result of this module.**

1. A BOLT 3-shaped commitment-transaction model (`CommitmentSighashView`) and a
   per-HTLC second-stage model (`HtlcSighashView`) with a deterministic field
   serializer (`commitmentPreimage`, `htlcPreimage`) covering the commitment
   number, obscured commitment number, funding outpoint and value, the output
   set, the HTLC set, the fee, the holder direction, the contest delay, the
   anchor flag, the feerate, and the second-stage fee.
2. Sighash digests `commitmentDigest` and `htlcDigest`, computed as
   `digest32 (sha256 (commitmentTag ++ preimage))`.  The tag is the existing
   `LnLean.Crypto.commitmentTag`, so a commitment sighash cannot be replayed in
   the funding or close domain.
3. An explicit `SignedBy` relation (verification in a named domain) and an
   explicit production relation `SighashProduces`: the full record's
   commitment digest, commitment signature, per-HTLC digests, per-HTLC
   signatures, and HTLC identification data are *equations* to the derived
   values.  `honestFull` is the derived record.
4. Determinism/derivation theorems: any two records satisfying
   `SighashProduces` for the same state and context agree on the digest,
   signature, entries, and indeed are the same record.  Under C3 a produced
   signature verifies for no digest other than the derived one, and a
   per-HTLC signature verifies for no other second-stage digest.
5. Connection to wave 4: `SighashProduces` plus `ProducedFrom` (and the two
   BOLT 3 value equations) yields the wave-4 coverage theorem together with the
   *computed* digest and the verified signature.  Conversely,
   `SighashProduces` plus state/digest coherence implies `ProducedFrom`, so the
   two relations compose.
6. An honest-signer/key-binding construction for the funding contract: one
   signing law serves both the funding and commitment domains
   (`CommitmentSigningLaw.ofFunding`); under `Crypto.KeyBinding` a produced
   funding signature is attributed to its key, and a funding signature cannot
   be replayed as a commitment signature over the same message.
7. Preserved legacy negatives: the wire record alone still determines neither
   coverage nor the HTLC set.  A new negative shows that `ProducedFrom` alone
   does *not* determine the digest: an explicit `SignedState` whose digest
   field is empty satisfies `ProducedFrom`, and its honest full record cannot
   satisfy `SighashProduces` for any model/context, because the derived digest
   is 32 bytes.  This makes the serializer relation load-bearing rather than a
   restatement.

## Scope

The serializer is a **structural** BOLT 3 model, not a bit-exact Bitcoin
transaction encoder.  It orders the fields in the BOLT 3 commitment order and
uses fixed-width little-endian naturals, one-byte tags, length-prefixed byte
strings, and a recursive HTLC list.  Scripts are opaque byte strings supplied
by the context; the model does not derive them from funding keys.  SHA-256
collision resistance in the model is injectivity on **32-byte preimages** only,
so two distinct preimages may share a digest; the module therefore proves
signature binding at the digest level and states view-level injectivity as the
remaining cryptographic gap rather than assuming it.  There is no secret-key
type: the signing law is keyed by the public key, the same idealization as
`LnLean.Protocol.Handshake.FundingSigningLaw`.

## Anchors

* BOLT 3 §"Commitment Transaction" (`03-transactions.md:83-353`): funding
  outpoint/value, `to_local`, `to_remote`, HTLC outputs, anchors, obscured
  commitment number, and the `nSequence`/`nLockTime` encoding.
* BOLT 3 §"Fees" (`:464-576`): commitment weight, feerate, floored fee.
* BOLT 2 §"Committing Updates So Far" (type 132): one commitment signature
  plus one signature per untrimmed HTLC output.
* Model: `LnLean/Protocol/Messages.lean` (`SignedHtlcEntry`,
  `CommitmentSignedFull`), `LnLean/Proofs/ProtocolWireTargets.lean`
  (`SignedHtlc`, `SignedState`, `ProducedFrom`, `commitment_signed_full_covers`),
  `LnLean/Crypto/Sig.lean` (`commitmentTag`, `verifyCommitment`,
  `verifyFunding_not_verifyCommitment`), `LnLean/Channel/Commitment.lean`
  (`commitmentOutputs`, `commitmentFee`),
  `LnLean/Proofs/ProtocolSigningTargets.lean` (`FundingSigningLaw`,
  `funding_signed_signing_contract`).
-/

import Bitcoin.Serialization.Interface
import LnLean.Bitcoin.Sighash
import LnLean.Protocol.Messages
import LnLean.Channel.Commitment
import LnLean.Channel.Fee
import LnLean.Crypto.Sig
import LnLean.Proofs.Channel.CommitmentTxProps
import LnLean.Proofs.Conservation
import LnLean.Proofs.ProtocolCoverageTargets
import LnLean.Proofs.ProtocolWireTargets
import LnLean.Proofs.ProtocolSigningTargets

namespace LnLean.Proofs.Channel.SighashTargets

set_option autoImplicit false

open LnLean
open LnLean.Protocol
open LnLean.Channel
open LnLean.Crypto
open LnLean.Proofs
open LnLean.Proofs.ProtocolWireTargets
open LnLean.Proofs.ProtocolCoverageTargets
open LnLean.Proofs.WaveE.E20

/-! ## 1. Serializer primitives -/

/-- Fixed-width eight-byte little-endian encoding of a natural number.  This
is the model's fixed-width integer encoding; it is deliberately simple and
total. -/
def natBytes (n : Nat) : ByteArray :=
  ByteArray.mk ((List.range 8).map
    (fun i => ((n / 256 ^ i) % 256).toUInt8)).toArray

/-- Length-prefixed byte string. -/
def bytesField (b : ByteArray) : ByteArray :=
  natBytes b.size ++ b

/-- Domain tag for a `to_local` output. -/
def outputTagToLocal : UInt8 := 0x01
/-- Domain tag for a `to_remote` output. -/
def outputTagToRemote : UInt8 := 0x02
/-- Domain tag for an HTLC output. -/
def outputTagHtlc : UInt8 := 0x03
/-- Domain tag for a local anchor output. -/
def outputTagLocalAnchor : UInt8 := 0x04
/-- Domain tag for a remote anchor output. -/
def outputTagRemoteAnchor : UInt8 := 0x05

/-- Serialize one commitment output.  Values are satoshis; the HTLC case tags
the direction so that offered and received outputs differ. -/
def commitmentOutputBytes : CommitmentOutput → ByteArray
  | .toLocal v => ByteArray.mk #[outputTagToLocal] ++ natBytes v
  | .toRemote v => ByteArray.mk #[outputTagToRemote] ++ natBytes v
  | .htlc d v =>
      ByteArray.mk #[outputTagHtlc] ++
        (match d with | .local => ByteArray.mk #[0x01] | .remote => ByteArray.mk #[0x02]) ++
        natBytes v
  | .localAnchor => ByteArray.mk #[outputTagLocalAnchor]
  | .remoteAnchor => ByteArray.mk #[outputTagRemoteAnchor]

/-- Serialize a direction. -/
def directionBytes : Direction → ByteArray
  | .local => ByteArray.mk #[0x01]
  | .remote => ByteArray.mk #[0x02]

/-- Serialize an HTLC lifecycle tag. -/
def htlcStateBytes : HTLCState → ByteArray
  | .offered => ByteArray.mk #[0x01]
  | .received => ByteArray.mk #[0x02]
  | .fulfilled => ByteArray.mk #[0x03]
  | .failed => ByteArray.mk #[0x04]
  | .removed => ByteArray.mk #[0x05]

/-- Serialize a boolean. -/
def boolBytes : Bool → ByteArray
  | true => ByteArray.mk #[0x01]
  | false => ByteArray.mk #[0x00]

/-- Concatenate a list of byte strings in order. -/
def concatBytes : List ByteArray → ByteArray
  | [] => ByteArray.empty
  | b :: t => b ++ concatBytes t

/-! ## 2. The commitment and HTLC sighash views -/

/-- The per-HTLC second-stage preimage fields.  `parentCommitmentNumber`
separates the same HTLC across commitment numbers; `htlcId` is a model-side
identifier (BOLT 3 does not put the numeric id in the second-stage transaction,
but the model needs it to distinguish two otherwise identical outputs). -/
structure HtlcSighashView where
  htlcId : Nat
  parentCommitmentNumber : Nat
  direction : Direction
  htlcState : HTLCState
  amountSat : Nat
  paymentHash : PaymentHash
  cltvExpiry : Height
  secondStageFeeSat : Nat
deriving Repr, BEq

/-- The BOLT 3 commitment-transaction preimage fields this model serializes.
`outputs` is the full commitment output list (`to_local`, `to_remote`, HTLCs,
anchors); `htlcs` is the signed HTLC set; `feeSat` is the commitment fee;
`holder` selects the local/remote transaction; `obscuredCommitmentNumber` is
the BOLT 3 XOR-obscured value carried in `nSequence`/`nLockTime`. -/
structure CommitmentSighashView where
  commitmentNumber : Nat
  obscuredCommitmentNumber : Nat
  fundingTxid : ByteArray
  fundingOutputIndex : Nat
  fundingValueSat : Nat
  fundingScript : ByteArray
  holder : Direction
  toLocalSat : Nat
  toRemoteSat : Nat
  outputs : List CommitmentOutput
  feeSat : Nat
  contestDelay : Nat
  anchorOutputs : Bool
  feeratePerKw : Nat
  htlcs : List HtlcSighashView
deriving Repr, BEq

/-- Serialize one per-HTLC second-stage preimage.  Field order: domain tag,
parent commitment number, HTLC id, direction, lifecycle tag, amount, payment
hash, CLTV expiry, second-stage fee. -/
def htlcPreimage (h : HtlcSighashView) : ByteArray :=
  ByteArray.mk #[0x20] ++
    natBytes h.parentCommitmentNumber ++
    natBytes h.htlcId ++
    directionBytes h.direction ++
    htlcStateBytes h.htlcState ++
    natBytes h.amountSat ++
    bytesField h.paymentHash.bytes ++
    natBytes h.cltvExpiry ++
    natBytes h.secondStageFeeSat

/-- Serialize the commitment preimage in BOLT 3 field order: version tag,
commitment number, obscured number, funding outpoint and value, funding script,
holder direction, balances, output set, fee, contest delay, anchor flag,
feerate, and the HTLC set. -/
def commitmentPreimage (v : CommitmentSighashView) : ByteArray :=
  ByteArray.mk #[0x02] ++
    natBytes v.commitmentNumber ++
    natBytes v.obscuredCommitmentNumber ++
    bytesField v.fundingTxid ++
    natBytes v.fundingOutputIndex ++
    natBytes v.fundingValueSat ++
    bytesField v.fundingScript ++
    directionBytes v.holder ++
    natBytes v.toLocalSat ++
    natBytes v.toRemoteSat ++
    natBytes v.outputs.length ++
    concatBytes (v.outputs.map commitmentOutputBytes) ++
    natBytes v.feeSat ++
    natBytes v.contestDelay ++
    boolBytes v.anchorOutputs ++
    natBytes v.feeratePerKw ++
    natBytes v.htlcs.length ++
    concatBytes (v.htlcs.map htlcPreimage)

/-- The commitment sighash digest.  The existing commitment domain tag
(`LnLean.Crypto.commitmentTag`) is prepended before hashing so that a
commitment preimage cannot be confused with a funding or close preimage. -/
def commitmentDigest (M : PrimitiveModel) (v : CommitmentSighashView) : ByteArray :=
  M.sha256 (commitmentTag ++ commitmentPreimage v)

/-- The per-HTLC second-stage sighash digest, in the same commitment domain and
bound to the parent commitment preimage so that an HTLC signature cannot be
moved to a different commitment number. -/
def htlcDigest (M : PrimitiveModel) (v : CommitmentSighashView)
    (h : HtlcSighashView) : ByteArray :=
  M.sha256 (commitmentTag ++ commitmentPreimage v ++ htlcPreimage h)

theorem commitmentDigest_size (M : PrimitiveModel) (v : CommitmentSighashView) :
    (commitmentDigest M v).size = 32 :=
  M.sha256_size _

theorem htlcDigest_size (M : PrimitiveModel) (v : CommitmentSighashView)
    (h : HtlcSighashView) : (htlcDigest M v h).size = 32 :=
  M.sha256_size _

/-! ## 3. `SignedBy` and the signing law -/

/-- Explicit signature verification in a named protocol domain.  The message
is prefixed with `domain`; for commitments the domain is
`LnLean.Crypto.commitmentTag`, matching `LnLean.Crypto.verifyCommitment`. -/
def SignedBy (M : PrimitiveModel) (pk : PubKey) (domain msg : ByteArray)
    (s : EcdsaSig) : Prop :=
  M.ecdsaVerify pk (domain ++ msg) s = true

/-- A signature over a commitment sighash digest in the commitment domain. -/
def CommitmentSignedBy (M : PrimitiveModel) (pk : PubKey)
    (v : CommitmentSighashView) (s : EcdsaSig) : Prop :=
  SignedBy M pk commitmentTag (commitmentDigest M v) s

/-- A signature over a per-HTLC second-stage digest in the commitment domain. -/
def HtlcSignedBy (M : PrimitiveModel) (pk : PubKey)
    (v : CommitmentSighashView) (h : HtlcSighashView) (s : EcdsaSig) : Prop :=
  SignedBy M pk commitmentTag (htlcDigest M v h) s

/-- `SignedBy` in the commitment domain is exactly the existing
`LnLean.Crypto.verifyCommitment` check on the message. -/
theorem signedBy_commitmentTag_iff (M : PrimitiveModel) (pk : PubKey)
    (msg : ByteArray) (s : EcdsaSig) :
    SignedBy M pk commitmentTag msg s ↔ verifyCommitment M pk msg s = true :=
  Iff.rfl

/-- The signing interface absent from `PrimitiveModel`, packaged for the
commitment domain.  `sign` is keyed by the public key because the model has no
secret-key type; `verifies` is signing correctness; `wire` records BOLT 1's
accepted signature shapes. -/
structure CommitmentSigningLaw (M : PrimitiveModel) where
  sign : PubKey → ByteArray → EcdsaSig
  verifies : ∀ (pk : PubKey) (msg : ByteArray),
    M.ecdsaVerify pk msg (sign pk msg) = true
  wire : ∀ (pk : PubKey) (msg : ByteArray),
    wireSigOK (sign pk msg).bytes = true

/-- One honest signer can serve both the funding and commitment domains: the
signing function is message-keyed, and the domain tags are part of the
message.  This is the bridge used by the funding/commitment contract below. -/
def CommitmentSigningLaw.ofFunding {M : PrimitiveModel}
    (law : LnLean.Protocol.Handshake.FundingSigningLaw M) :
    CommitmentSigningLaw M where
  sign := law.sign
  verifies := law.verifies
  wire := law.wire

/-! ## 4. Deriving a record from state and context -/

/-- The external commitment context: the BOLT 3 data that the channel state
does not carry.  `commitmentKey` is the signer key; the model has no
secret-key type, so the key is used directly by the signing law. -/
structure SighashContext where
  fundingTxid : ByteArray
  fundingOutputIndex : Nat
  fundingScript : ByteArray
  obscuredCommitmentNumber : Nat
  secondStageFeeSat : Nat
  commitmentKey : PubKey

/-- The per-HTLC view of one state HTLC.  The state's explicit
`signedDataDigest` is deliberately *not* read: that field is the data this
module replaces by a derived digest. -/
def htlcViewOfState (ctx : SighashContext) (st : SignedState)
    (h : SignedHtlc) : HtlcSighashView where
  htlcId := h.htlcId
  parentCommitmentNumber := st.commitmentNumber
  direction := h.direction
  htlcState := h.htlcState
  amountSat := h.amount.toSatFloor
  paymentHash := h.paymentHash
  cltvExpiry := h.cltvExpiry
  secondStageFeeSat := ctx.secondStageFeeSat

/-- The list of per-HTLC views of the state's HTLC set. -/
def htlcViewsOfState (ctx : SighashContext) (st : SignedState) :
    List HtlcSighashView :=
  st.htlcs.map (htlcViewOfState ctx st)

/-- The commitment sighash view determined by the state and context.  The
state's explicit commitment digest and per-HTLC signed-data digests are not
read; the outputs are the commitment's BOLT 3 output list. -/
def viewOfState (ctx : SighashContext) (st : SignedState) :
    CommitmentSighashView where
  commitmentNumber := st.commitmentNumber
  obscuredCommitmentNumber := ctx.obscuredCommitmentNumber
  fundingTxid := ctx.fundingTxid
  fundingOutputIndex := ctx.fundingOutputIndex
  fundingValueSat := st.fundingValueSat
  fundingScript := ctx.fundingScript
  holder := st.holder
  toLocalSat := st.toLocalSat
  toRemoteSat := st.toRemoteSat
  outputs := st.toCommitment.commitmentOutputs
  feeSat := st.feeSat
  contestDelay := st.contestDelay
  anchorOutputs := st.anchorOutputs
  feeratePerKw := st.feerate.msatPerKw
  htlcs := htlcViewsOfState ctx st

@[simp] theorem viewOfState_commitmentNumber (ctx : SighashContext)
    (st : SignedState) :
    (viewOfState ctx st).commitmentNumber = st.commitmentNumber := rfl

@[simp] theorem viewOfState_feeSat (ctx : SighashContext) (st : SignedState) :
    (viewOfState ctx st).feeSat = st.feeSat := rfl

@[simp] theorem viewOfState_holder (ctx : SighashContext) (st : SignedState) :
    (viewOfState ctx st).holder = st.holder := rfl

@[simp] theorem viewOfState_outputs (ctx : SighashContext) (st : SignedState) :
    (viewOfState ctx st).outputs = st.toCommitment.commitmentOutputs := rfl

@[simp] theorem viewOfState_htlcs (ctx : SighashContext) (st : SignedState) :
    (viewOfState ctx st).htlcs = htlcViewsOfState ctx st := rfl

/-- One signed entry derived from a state HTLC: identification data from the
state, digest and signature from the serializer and the signing law. -/
def entryOfSighash (M : PrimitiveModel) (law : CommitmentSigningLaw M)
    (ctx : SighashContext) (st : SignedState) (h : SignedHtlc) :
    SignedHtlcEntry where
  htlcId := h.htlcId
  amount := h.amount
  paymentHash := h.paymentHash
  direction := h.direction
  htlcState := h.htlcState
  cltvExpiry := h.cltvExpiry
  signedDataDigest := htlcDigest M (viewOfState ctx st) (htlcViewOfState ctx st h)
  signature := law.sign ctx.commitmentKey
    (commitmentTag ++ htlcDigest M (viewOfState ctx st) (htlcViewOfState ctx st h))

@[simp] theorem entryOfSighash_htlcId (M : PrimitiveModel)
    (law : CommitmentSigningLaw M) (ctx : SighashContext) (st : SignedState)
    (h : SignedHtlc) : (entryOfSighash M law ctx st h).htlcId = h.htlcId := rfl

@[simp] theorem entryOfSighash_digest (M : PrimitiveModel)
    (law : CommitmentSigningLaw M) (ctx : SighashContext) (st : SignedState)
    (h : SignedHtlc) :
    (entryOfSighash M law ctx st h).signedDataDigest =
      htlcDigest M (viewOfState ctx st) (htlcViewOfState ctx st h) := rfl

@[simp] theorem entryOfSighash_signature (M : PrimitiveModel)
    (law : CommitmentSigningLaw M) (ctx : SighashContext) (st : SignedState)
    (h : SignedHtlc) :
    (entryOfSighash M law ctx st h).signature =
      law.sign ctx.commitmentKey
        (commitmentTag ++
          htlcDigest M (viewOfState ctx st) (htlcViewOfState ctx st h)) := rfl

/-- The full record derived from a state and context.  Every field that the
wave-4 record supplied explicitly is now computed. -/
def honestFull (M : PrimitiveModel) (law : CommitmentSigningLaw M)
    (ctx : SighashContext) (st : SignedState) : CommitmentSignedFull where
  channelId := st.channelId
  commitmentNumber := st.commitmentNumber
  feePaid := ⟨st.feeSat⟩
  commitmentDigest := commitmentDigest M (viewOfState ctx st)
  commitmentSignature := law.sign ctx.commitmentKey
    (commitmentTag ++ commitmentDigest M (viewOfState ctx st))
  htlcEntries := st.htlcs.map (entryOfSighash M law ctx st)

@[simp] theorem honestFull_commitmentDigest (M : PrimitiveModel)
    (law : CommitmentSigningLaw M) (ctx : SighashContext) (st : SignedState) :
    (honestFull M law ctx st).commitmentDigest =
      commitmentDigest M (viewOfState ctx st) := rfl

@[simp] theorem honestFull_commitmentSignature (M : PrimitiveModel)
    (law : CommitmentSigningLaw M) (ctx : SighashContext) (st : SignedState) :
    (honestFull M law ctx st).commitmentSignature =
      law.sign ctx.commitmentKey
        (commitmentTag ++ commitmentDigest M (viewOfState ctx st)) := rfl

/-! ## 5. The explicit production relation -/

/-- **`SighashProduces`.**  A full `commitment_signed` record was produced
from the state under the serializer when:

* its channel id, commitment number, and fee are the state's;
* its commitment digest is the computed BOLT 3 sink digest;
* its commitment signature is the honest signature over that digest in the
  commitment domain;
* its signed HTLC entries are exactly the state's HTLCs with derived
  second-stage digests and derived signatures.

The relation is *defined* by these equations; no digest or signature is left
free. -/
structure SighashProduces (M : PrimitiveModel) (law : CommitmentSigningLaw M)
    (ctx : SighashContext) (st : SignedState) (f : CommitmentSignedFull) : Prop where
  channelId_eq : f.channelId = st.channelId
  commitmentNumber_eq : f.commitmentNumber = st.commitmentNumber
  feePaid_eq : f.feePaid.val = st.feeSat
  commitmentDigest_eq : f.commitmentDigest = commitmentDigest M (viewOfState ctx st)
  commitmentSignature_eq : f.commitmentSignature =
    law.sign ctx.commitmentKey
      (commitmentTag ++ commitmentDigest M (viewOfState ctx st))
  htlcEntries_eq : f.htlcEntries =
    st.htlcs.map (entryOfSighash M law ctx st)

/-- The derived record satisfies the production relation definitionally. -/
theorem honestFull_produces (M : PrimitiveModel) (law : CommitmentSigningLaw M)
    (ctx : SighashContext) (st : SignedState) :
    SighashProduces M law ctx st (honestFull M law ctx st) :=
  { channelId_eq := rfl
    commitmentNumber_eq := rfl
    feePaid_eq := rfl
    commitmentDigest_eq := rfl
    commitmentSignature_eq := rfl
    htlcEntries_eq := rfl }

/-- **Digests and signatures are derived, not arbitrary.**  Two full records
produced from the same state/context/model/signing law agree on the commitment
digest and on the commitment signature. -/
theorem SighashProduces.digest_unique {M : PrimitiveModel}
    {law : CommitmentSigningLaw M} {ctx : SighashContext} {st : SignedState}
    {f g : CommitmentSignedFull} (hf : SighashProduces M law ctx st f)
    (hg : SighashProduces M law ctx st g) :
    f.commitmentDigest = g.commitmentDigest ∧
      f.commitmentSignature = g.commitmentSignature := by
  constructor
  · rw [hf.commitmentDigest_eq, hg.commitmentDigest_eq]
  · rw [hf.commitmentSignature_eq, hg.commitmentSignature_eq]

/-- The signed HTLC entries are derived too: the entry list is a function of
the state, context, model, and signing law. -/
theorem SighashProduces.entries_unique {M : PrimitiveModel}
    {law : CommitmentSigningLaw M} {ctx : SighashContext} {st : SignedState}
    {f g : CommitmentSignedFull} (hf : SighashProduces M law ctx st f)
    (hg : SighashProduces M law ctx st g) :
    f.htlcEntries = g.htlcEntries := by
  rw [hf.htlcEntries_eq, hg.htlcEntries_eq]

/-- A produced record is the honest derived record: the relation determines
every field. -/
theorem SighashProduces.eq_honestFull {M : PrimitiveModel}
    {law : CommitmentSigningLaw M} {ctx : SighashContext} {st : SignedState}
    {f : CommitmentSignedFull} (h : SighashProduces M law ctx st f) :
    f = honestFull M law ctx st := by
  rcases f with ⟨cid, num, fee, dig, sig, entries⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have hfee : fee = ⟨st.feeSat⟩ := by
    cases fee with
    | mk v => exact congrArg Msat.mk h3
  cases h1
  cases h2
  cases hfee
  cases h4
  cases h5
  cases h6
  rfl

/-- The derived commitment digest has the state's commitment number and fee
bound into it (by construction of the view). -/
theorem commitmentDigest_derived (M : PrimitiveModel) (law : CommitmentSigningLaw M)
    (ctx : SighashContext) (st : SignedState) :
    (honestFull M law ctx st).commitmentDigest =
        commitmentDigest M (viewOfState ctx st) ∧
      (viewOfState ctx st).commitmentNumber = st.commitmentNumber ∧
      (viewOfState ctx st).feeSat = st.feeSat ∧
      (viewOfState ctx st).holder = st.holder :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## 6. C3 binding and domain separation -/

/-- **C3 binds the commitment signature to the derived digest.**  If the
signature of a produced record validates under the producing key for any
message `msg` in the commitment domain, that message is the derived digest.
This is the formal sense in which the signature is not free data. -/
theorem SighashProduces.signature_binds_digest {M : PrimitiveModel}
    (hC3 : EufCma M.ecdsaVerify) {law : CommitmentSigningLaw M}
    {ctx : SighashContext} {st : SignedState} {f : CommitmentSignedFull}
    (h : SighashProduces M law ctx st f) {msg : ByteArray}
    (hver : M.ecdsaVerify ctx.commitmentKey (commitmentTag ++ msg)
      f.commitmentSignature = true) :
    msg = commitmentDigest M (viewOfState ctx st) := by
  have hder : M.ecdsaVerify ctx.commitmentKey
      (commitmentTag ++ commitmentDigest M (viewOfState ctx st))
      f.commitmentSignature = true := by
    rw [h.commitmentSignature_eq]
    exact law.verifies _ _
  exact append_left_cancel (hC3 _ _ _ _ hver hder)

/-- **C3 binds a per-HTLC signature to the derived second-stage digest.** -/
theorem SighashProduces.htlc_signature_binds_digest {M : PrimitiveModel}
    (hC3 : EufCma M.ecdsaVerify) {law : CommitmentSigningLaw M}
    {ctx : SighashContext} {st : SignedState} {f : CommitmentSignedFull}
    (_h : SighashProduces M law ctx st f) {hh : SignedHtlc}
    (_hmem : hh ∈ st.htlcs) {msg : ByteArray}
    (hver : M.ecdsaVerify ctx.commitmentKey (commitmentTag ++ msg)
      (entryOfSighash M law ctx st hh).signature = true) :
    msg = htlcDigest M (viewOfState ctx st) (htlcViewOfState ctx st hh) := by
  have hder : M.ecdsaVerify ctx.commitmentKey
      (commitmentTag ++
        htlcDigest M (viewOfState ctx st) (htlcViewOfState ctx st hh))
      (entryOfSighash M law ctx st hh).signature = true := by
    exact law.verifies _ _
  exact append_left_cancel (hC3 _ _ _ _ hver hder)

/-- A produced commitment signature is a valid signature over the derived
digest in the commitment domain. -/
theorem SighashProduces.commitmentSignedBy {M : PrimitiveModel}
    {law : CommitmentSigningLaw M} {ctx : SighashContext} {st : SignedState}
    {f : CommitmentSignedFull} (h : SighashProduces M law ctx st f) :
    CommitmentSignedBy M ctx.commitmentKey (viewOfState ctx st)
      f.commitmentSignature := by
  unfold CommitmentSignedBy SignedBy
  rw [h.commitmentSignature_eq]
  exact law.verifies _ _

/-- Every derived HTLC entry's signature is valid over its derived digest. -/
theorem SighashProduces.entrySignedBy {M : PrimitiveModel}
    {law : CommitmentSigningLaw M} {ctx : SighashContext} {st : SignedState}
    {f : CommitmentSignedFull} (_h : SighashProduces M law ctx st f)
    (hh : SignedHtlc) (_hmem : hh ∈ st.htlcs) :
    HtlcSignedBy M ctx.commitmentKey (viewOfState ctx st)
      (htlcViewOfState ctx st hh)
      (entryOfSighash M law ctx st hh).signature := by
  unfold HtlcSignedBy SignedBy
  exact law.verifies _ _

/-- The digest list of the produced entries is exactly the derived list. -/
theorem SighashProduces.entries_digest {M : PrimitiveModel}
    {law : CommitmentSigningLaw M} {ctx : SighashContext} {st : SignedState}
    {f : CommitmentSignedFull} (h : SighashProduces M law ctx st f) :
    f.htlcEntries.map (fun e => e.signedDataDigest) =
      st.htlcs.map
        (fun hh => htlcDigest M (viewOfState ctx st) (htlcViewOfState ctx st hh)) := by
  rw [h.htlcEntries_eq, List.map_map]
  exact List.map_congr_left (fun hh _ => rfl)

/-- The produced entry count is the state's HTLC count. -/
theorem SighashProduces.entry_count {M : PrimitiveModel}
    {law : CommitmentSigningLaw M} {ctx : SighashContext} {st : SignedState}
    {f : CommitmentSignedFull} (h : SighashProduces M law ctx st f) :
    f.htlcEntries.length = st.htlcs.length := by
  rw [h.htlcEntries_eq, List.length_map]

/-- **Domain separation.**  A signature valid in the funding domain cannot
also validate as a commitment-domain signature over the same untagged
message.  So an honest funding signature is not a commitment signature. -/
theorem funding_signature_not_commitment_signature
    (M : PrimitiveModel) (hC3 : EufCma M.ecdsaVerify)
    {pk : PubKey} {msg : ByteArray} {sig : EcdsaSig}
    (hf : verifyFunding M pk msg sig = true)
    (hc : SignedBy M pk commitmentTag msg sig) : False := by
  exact verifyFunding_not_verifyCommitment M hC3 hf hc

/-! ## 7. Connection to `ProducedFrom` and the wave-4 coverage theorem -/

/-- Under `SighashProduces` the signed entries project exactly onto the
commitment's current HTLC outputs. -/
theorem SighashProduces.entries_map_output {M : PrimitiveModel}
    {law : CommitmentSigningLaw M} {ctx : SighashContext} {st : SignedState}
    {f : CommitmentSignedFull} (h : SighashProduces M law ctx st f) :
    f.htlcEntries.map SignedHtlcEntry.toCommitmentHtlcOutput =
      st.toCommitment.htlcs := by
  rw [h.htlcEntries_eq, List.map_map]
  rfl

/-- **Coverage derived from the serializer relation alone.**  A record
produced under `SighashProduces` covers exactly the state's HTLC set, pays the
BOLT 3 formula fee under the two value equations, carries the computed digest,
and its commitment signature verifies over that digest.  This does not use
`ProducedFrom`; the two relations are consistent and can be composed. -/
theorem SighashProduces.coverage {M : PrimitiveModel}
    {law : CommitmentSigningLaw M} {ctx : SighashContext} {st : SignedState}
    {f : CommitmentSignedFull} (h : SighashProduces M law ctx st f)
    (hcons : CommitmentConserved st.toCommitment)
    (hres : FeeIsFundingResidual st.feerate st.toCommitment) :
    f.htlcEntries.map SignedHtlcEntry.toCommitmentHtlcOutput =
        st.toCommitment.htlcs ∧
      f.toCommitmentSigned.htlcSignatures.length =
        st.toCommitment.htlcs.length ∧
      CoversHtlcOutputs f.toCommitmentSigned st.toCommitment ∧
      f.feePaid.val = (commitmentFee st.feerate st.toCommitment).val ∧
      f.commitmentNumber = st.toCommitment.commitmentNumber ∧
      f.commitmentDigest = commitmentDigest M (viewOfState ctx st) ∧
      CommitmentSignedBy M ctx.commitmentKey (viewOfState ctx st)
        f.commitmentSignature := by
  have hdesc : f.htlcEntries.map SignedHtlcEntry.toCommitmentHtlcOutput =
      st.toCommitment.htlcs := h.entries_map_output
  have hlen : f.toCommitmentSigned.htlcSignatures.length =
      st.toCommitment.htlcs.length := by
    rw [CommitmentSignedFull.toCommitmentSigned_htlcSignatures,
      h.htlcEntries_eq, List.length_map, List.length_map]
    simp
  have hfee : f.feePaid.val =
      (commitmentFee st.feerate st.toCommitment).val := by
    unfold CommitmentConserved at hcons
    unfold FeeIsFundingResidual at hres
    simp only [SignedState.toCommitment_feeSat] at hcons ⊢
    rw [h.feePaid_eq]
    omega
  have hcoversFee : waveE_e20_covers_fee st.feerate st.toCommitment := by
    unfold waveE_e20_covers_fee
    simp only [SignedState.toCommitment_feeSat]
    rw [← h.feePaid_eq]
    exact hfee
  refine ⟨hdesc, hlen, ?_, hfee, ?_, h.commitmentDigest_eq,
    h.commitmentSignedBy⟩
  · unfold CoversHtlcOutputs
    rw [hlen, Commitment.htlcOutputCount_commitmentOutputs]
  · rw [h.commitmentNumber_eq]
    rfl

/-- `SighashProduces` plus state/digest coherence implies the wave-4
`ProducedFrom` relation.  The per-HTLC signing family is the derived one.
This is the bridge that lets the serializer result compose with the already
proved coverage theorem instead of duplicating it. -/
theorem producedFrom_of_sighashProduces {M : PrimitiveModel}
    {law : CommitmentSigningLaw M} {ctx : SighashContext} {st : SignedState}
    {f : CommitmentSignedFull} (h : SighashProduces M law ctx st f)
    (hdig : st.commitmentDigest = commitmentDigest M (viewOfState ctx st))
    (hhtlc : ∀ hh ∈ st.htlcs,
      hh.signedDataDigest =
        htlcDigest M (viewOfState ctx st) (htlcViewOfState ctx st hh)) :
    ProducedFrom f st
      (fun hh => law.sign ctx.commitmentKey
        (commitmentTag ++
          htlcDigest M (viewOfState ctx st) (htlcViewOfState ctx st hh))) := by
  refine
    { channelId_eq := h.channelId_eq
      commitmentNumber_eq := h.commitmentNumber_eq
      feePaid_eq := h.feePaid_eq
      commitmentDigest_eq := ?_
      htlcEntries_eq := ?_ }
  · rw [h.commitmentDigest_eq, ← hdig]
  · rw [h.htlcEntries_eq]
    exact List.map_congr_left (fun hh hmem => by
      simp [entryOfSighash, SignedHtlc.toEntry, hhtlc hh hmem])

/-- **PR-02, positive direction with derived digests/signatures.**  If a full
record was produced under the serializer *and* satisfies the wave-4 production
relation (equivalently, under the coherence hypotheses of
`producedFrom_of_sighashProduces`), and the two BOLT 3 value equations hold,
then all wave-4 coverage conclusions hold, the commitment digest is the
computed BOLT 3 sink digest, and the commitment signature is valid over that
digest. -/
theorem commitment_signed_full_covers_of_sighash
    (M : PrimitiveModel) (law : CommitmentSigningLaw M)
    (ctx : SighashContext) (f : CommitmentSignedFull) (st : SignedState)
    (sigAt : SignedHtlc → EcdsaSig)
    (hsh : SighashProduces M law ctx st f)
    (hprod : ProducedFrom f st sigAt)
    (hcons : CommitmentConserved st.toCommitment)
    (hres : FeeIsFundingResidual st.feerate st.toCommitment) :
    (f.htlcEntries.map SignedHtlcEntry.toCommitmentHtlcOutput =
        st.toCommitment.htlcs ∧
      f.toCommitmentSigned.htlcSignatures.length =
        st.toCommitment.htlcs.length ∧
      CoversHtlcOutputs f.toCommitmentSigned st.toCommitment ∧
      f.feePaid.val = (commitmentFee st.feerate st.toCommitment).val ∧
      f.commitmentNumber = st.toCommitment.commitmentNumber ∧
      waveE_e20_commitment_signed_covers
        f.toCommitmentSigned st.feerate st.toCommitment) ∧
      f.commitmentDigest = commitmentDigest M (viewOfState ctx st) ∧
      CommitmentSignedBy M ctx.commitmentKey (viewOfState ctx st)
        f.commitmentSignature := by
  have hcov := commitment_signed_full_covers f st sigAt hprod hcons hres
  refine ⟨?_, hsh.commitmentDigest_eq, hsh.commitmentSignedBy⟩
  exact ⟨hcov.1, hcov.2.1, hcov.2.2.1, hcov.2.2.2.1,
    hcov.2.2.2.2.1, hcov.2.2.2.2.2.2.1⟩

/-- The exact catalog-shaped corollary with derived digests: an honestly
produced record covers the state's HTLC set, carries the computed digest, and
its signature verifies in the commitment domain. -/
theorem honest_commitment_signed_full_covers
    (M : PrimitiveModel) (law : CommitmentSigningLaw M)
    (ctx : SighashContext) (st : SignedState)
    (hcons : CommitmentConserved st.toCommitment)
    (hres : FeeIsFundingResidual st.feerate st.toCommitment) :
    (honestFull M law ctx st).htlcEntries.map
        SignedHtlcEntry.toCommitmentHtlcOutput = st.toCommitment.htlcs ∧
      (honestFull M law ctx st).feePaid.val =
        (commitmentFee st.feerate st.toCommitment).val ∧
      (honestFull M law ctx st).commitmentDigest =
        commitmentDigest M (viewOfState ctx st) ∧
      CommitmentSignedBy M ctx.commitmentKey (viewOfState ctx st)
        (honestFull M law ctx st).commitmentSignature := by
  have hcov := (honestFull_produces M law ctx st).coverage hcons hres
  exact ⟨hcov.1, hcov.2.2.2.1, rfl,
    (honestFull_produces M law ctx st).commitmentSignedBy⟩

/-! ## 8. Non-vacuity: the concrete wave-4 state -/

/-- The wave-4 concrete one-HTLC conserving state also satisfies the
serializer production relation: the honest record is derived from it. -/
theorem exampleSignedState_produces (M : PrimitiveModel)
    (law : CommitmentSigningLaw M) (ctx : SighashContext) :
    SighashProduces M law ctx exampleSignedState
      (honestFull M law ctx exampleSignedState) :=
  honestFull_produces M law ctx exampleSignedState

/-- The concrete state's derived digest is 32 bytes, and the honest record
carries it. -/
theorem exampleSignedState_honest_digest_size (M : PrimitiveModel)
    (law : CommitmentSigningLaw M) (ctx : SighashContext) :
    (honestFull M law ctx exampleSignedState).commitmentDigest.size = 32 :=
  commitmentDigest_size M (viewOfState ctx exampleSignedState)

/-! ## 9. The serializer relation is load-bearing; legacy negatives -/

/-- **`ProducedFrom` alone does not determine the digest.**  The wave-4
concrete state stores an empty `commitmentDigest`, and its honest wave-4
record copies that field, so it satisfies `ProducedFrom`.  The derived digest
is 32 bytes, so *no* `SighashProduces` relation can hold for that record.  Hence
the serializer relation genuinely adds the derivation, rather than restating
the wave-4 data relation. -/
theorem producedFrom_not_sighashProduces (M : PrimitiveModel)
    (law : CommitmentSigningLaw M) (ctx : SighashContext)
    (commitSig : EcdsaSig) (sigAt : SignedHtlc → EcdsaSig) :
    ¬ SighashProduces M law ctx exampleSignedState
        (commitmentSignedFullOfState exampleSignedState commitSig sigAt) := by
  intro h
  have hsize :
      (commitmentDigest M (viewOfState ctx exampleSignedState)).size = 32 :=
    commitmentDigest_size M _
  have hempty :
      (commitmentSignedFullOfState exampleSignedState commitSig sigAt).commitmentDigest =
        ByteArray.empty := rfl
  have heq : ByteArray.empty =
      commitmentDigest M (viewOfState ctx exampleSignedState) := by
    rw [← hempty, h.commitmentDigest_eq]
  have hsz := congrArg ByteArray.size heq
  rw [hsize] at hsz
  exact absurd hsz (by decide)

/-- The legacy wire record alone still cannot determine coverage: the wave-4
no-decoder theorem is preserved unchanged. -/
theorem legacy_wire_cannot_determine_coverage :
    ¬ ∃ g : CommitmentSigned → Commitment,
        ∀ (m : CommitmentSigned) (r : FeeRate),
          waveE_e20_commitment_signed_covers m r (g m) :=
  LnLean.Proofs.ProtocolWireTargets.legacy_wire_cannot_determine_coverage

/-- The legacy wire record alone still cannot select the HTLC set: the wave-4
counterexample is preserved unchanged. -/
theorem legacy_wire_cannot_select_htlc_set :
    ¬ ∃ g : CommitmentSigned → List CommitmentHTLCOutput,
        ∀ (m : CommitmentSigned) (c : Commitment),
          waveE_e20_covers_htlcs m c → c.htlcs = g m :=
  LnLean.Proofs.ProtocolWireTargets.legacy_wire_cannot_select_htlc_set

/-- A full record can satisfy `ProducedFrom` and still carry a digest that is
not the serialized one (the concrete empty-digest state).  This is the
mechanized complement of `producedFrom_of_sighashProduces`: the coherence
hypothesis there is not automatic. -/
theorem producedFrom_without_serialized_digest :
    ∃ (f : CommitmentSignedFull) (st : SignedState)
      (sigAt : SignedHtlc → EcdsaSig),
      ProducedFrom f st sigAt ∧ f.commitmentDigest = ByteArray.empty := by
  exact ⟨commitmentSignedFullOfState exampleSignedState ⟨ByteArray.empty⟩
      (fun _ => ⟨ByteArray.empty⟩), exampleSignedState,
      (fun _ => ⟨ByteArray.empty⟩),
      producedFrom_commitmentSignedFullOfState exampleSignedState
        ⟨ByteArray.empty⟩ (fun _ => ⟨ByteArray.empty⟩), rfl⟩

/-! ## 10. Funding contract: honest signer and key binding -/

/-- **One signer for funding and commitment.**  Given the wave-3
`FundingSigningLaw` and the independent `Crypto.KeyBinding` hypothesis:

* the honest `funding_signed` record is valid, its key is attributed to the
  producing key, and C3 fixes its funding transaction;
* the honest full commitment record is derived by the BOLT 3 serializer and
  its commitment signature verifies over the derived digest.

The signing law is the same object in both domains
(`CommitmentSigningLaw.ofFunding`); the domain tags keep the signatures apart.
The remaining hypotheses are exactly the two fields the wave-A record lacks
(the funding key and the funding transaction, supplied by the predicate) and
the explicit commitment context. -/
theorem funding_and_commitment_signing_contract
    (M : PrimitiveModel)
    (law : LnLean.Protocol.Handshake.FundingSigningLaw M)
    (hkb : KeyBinding M.ecdsaVerify)
    (channelId : ChannelId) (fundingKey : PubKey) (fundingTx : ByteArray)
    (ctx : SighashContext) (st : SignedState) :
    (let m := LnLean.Protocol.Handshake.honestFundingSigned law channelId
        fundingKey fundingTx
     wireSigOK m.signature.bytes = true ∧
       LnLean.Proofs.WaveE.E19.fundingSignedValid M fundingKey fundingTx m ∧
       (∀ fundingKey' : PubKey,
         LnLean.Proofs.WaveE.E19.fundingSignedValid M fundingKey' fundingTx m →
           fundingKey' = fundingKey) ∧
       (∀ fundingTx' : ByteArray,
         LnLean.Proofs.WaveE.E19.fundingSignedValid M fundingKey fundingTx' m →
           fundingTx' = fundingTx)) ∧
      SighashProduces M (CommitmentSigningLaw.ofFunding law) ctx st
        (honestFull M (CommitmentSigningLaw.ofFunding law) ctx st) ∧
      CommitmentSignedBy M ctx.commitmentKey (viewOfState ctx st)
        (honestFull M (CommitmentSigningLaw.ofFunding law) ctx st).commitmentSignature :=
  ⟨LnLean.Protocol.Handshake.funding_signed_signing_contract
      law hkb channelId fundingKey fundingTx,
    honestFull_produces M (CommitmentSigningLaw.ofFunding law) ctx st,
    (honestFull_produces M (CommitmentSigningLaw.ofFunding law) ctx st).commitmentSignedBy⟩

/-- C3 alone does not give signature-key attribution in a domain: the
single-message verifier is EUF-CMA and accepts one fixed tagged message under
two distinct keys.  This is the same separation that forces `KeyBinding` in
the funding and commitment contracts above. -/
theorem signedBy_attribution_not_from_eufCma (M₀ : PrimitiveModel)
    (msg : ByteArray) :
    ∃ (M : PrimitiveModel) (sig : EcdsaSig) (k₁ k₂ : PubKey),
      k₁ ≠ k₂ ∧
        EufCma M.ecdsaVerify ∧
        SignedBy M k₁ commitmentTag msg sig ∧
        SignedBy M k₂ commitmentTag msg sig := by
  let d₀ : ByteArray := commitmentTag ++ msg
  let M : PrimitiveModel :=
    LnLean.Protocol.Handshake.singleMessageEcdsaModel M₀ d₀
  let sig : EcdsaSig := ⟨ByteArray.empty⟩
  refine ⟨M, sig, ⟨ByteArray.empty⟩, ⟨ByteArray.mk #[0x00]⟩, ?_,
    M.ecdsa_eufCma, ?_, ?_⟩
  · intro hEq
    have hs : (⟨ByteArray.empty⟩ : PubKey).bytes.size =
        (⟨ByteArray.mk #[0x00]⟩ : PubKey).bytes.size :=
      congrArg (fun p : PubKey => p.bytes.size) hEq
    exact absurd hs (by decide)
  · unfold SignedBy
    show M.ecdsaVerify ⟨ByteArray.empty⟩ (commitmentTag ++ msg) sig = true
    simp [M, LnLean.Protocol.Handshake.singleMessageEcdsaModel,
      singleMessageVerify, d₀]
  · unfold SignedBy
    show M.ecdsaVerify ⟨ByteArray.mk #[0x00]⟩ (commitmentTag ++ msg) sig = true
    simp [M, LnLean.Protocol.Handshake.singleMessageEcdsaModel,
      singleMessageVerify, d₀]

/-! ## 11. Summary -/

/-- Bundled faithful reading of the lane.

1. The derived record always satisfies the serializer production relation.
2. Two records produced from one state agree on digest, signature, and
   entries; they are the same record.
3. Under C3, a produced signature validates for no message other than the
   derived digest.
4. Under the state/digest coherence hypotheses, the serializer relation
   implies the wave-4 `ProducedFrom` relation, so the coverage theorem applies.
5. The legacy no-decoder and no-selector negatives are retained.
6. `ProducedFrom` alone does not determine the digest. -/
theorem sighash_summary :
    (∀ (M : PrimitiveModel) (law : CommitmentSigningLaw M)
        (ctx : SighashContext) (st : SignedState),
        SighashProduces M law ctx st (honestFull M law ctx st)) ∧
      (∀ (M : PrimitiveModel) (law : CommitmentSigningLaw M)
        (ctx : SighashContext) (st : SignedState)
        (f g : CommitmentSignedFull),
        SighashProduces M law ctx st f →
        SighashProduces M law ctx st g →
        f.commitmentDigest = g.commitmentDigest ∧
          f.commitmentSignature = g.commitmentSignature ∧
          f.htlcEntries = g.htlcEntries) ∧
      (∀ (M : PrimitiveModel), EufCma M.ecdsaVerify →
        ∀ (law : CommitmentSigningLaw M) (ctx : SighashContext)
          (st : SignedState) (f : CommitmentSignedFull),
          SighashProduces M law ctx st f →
          ∀ msg : ByteArray,
            M.ecdsaVerify ctx.commitmentKey (commitmentTag ++ msg)
              f.commitmentSignature = true →
            msg = commitmentDigest M (viewOfState ctx st)) ∧
      (∀ (M : PrimitiveModel) (law : CommitmentSigningLaw M)
        (ctx : SighashContext) (st : SignedState) (f : CommitmentSignedFull),
        SighashProduces M law ctx st f →
        st.commitmentDigest = commitmentDigest M (viewOfState ctx st) →
        (∀ hh ∈ st.htlcs,
          hh.signedDataDigest =
            htlcDigest M (viewOfState ctx st) (htlcViewOfState ctx st hh)) →
        ProducedFrom f st
          (fun hh => law.sign ctx.commitmentKey
            (commitmentTag ++
              htlcDigest M (viewOfState ctx st) (htlcViewOfState ctx st hh)))) ∧
      (¬ ∃ g : CommitmentSigned → Commitment,
          ∀ (m : CommitmentSigned) (r : FeeRate),
            waveE_e20_commitment_signed_covers m r (g m)) ∧
      (¬ ∃ g : CommitmentSigned → List CommitmentHTLCOutput,
          ∀ (m : CommitmentSigned) (c : Commitment),
            waveE_e20_covers_htlcs m c → c.htlcs = g m) ∧
      (∃ (f : CommitmentSignedFull) (st : SignedState)
          (sigAt : SignedHtlc → EcdsaSig),
        ProducedFrom f st sigAt ∧ f.commitmentDigest = ByteArray.empty) :=
  ⟨honestFull_produces,
    fun _M _law _ctx _st _f _g hf hg =>
      ⟨(SighashProduces.digest_unique hf hg).1,
        (SighashProduces.digest_unique hf hg).2,
        SighashProduces.entries_unique hf hg⟩,
    fun _M hC3 _law _ctx _st _f h _msg hver =>
      SighashProduces.signature_binds_digest hC3 h hver,
    fun _M _law _ctx _st _f h hdig hhtlc =>
      producedFrom_of_sighashProduces h hdig hhtlc,
    legacy_wire_cannot_determine_coverage,
    legacy_wire_cannot_select_htlc_set,
    producedFrom_without_serialized_digest⟩

/-! ## 12. Exact BOLT 3 commitment/HTLC byte layout and refinement -/

open Bitcoin.Data
open Bitcoin.Serialization

/-! ### 12.1 Exact transaction and preimage layout -/

def exactU32 (x : UInt32) : ByteArray := Bitcoin.Data.serU32 x
def exactU64 (x : UInt64) : ByteArray := Bitcoin.Data.serU64 x
def exactCS (n : Nat) : ByteArray := Bitcoin.Data.compactSizeEnc n

theorem exactU32_size (x : UInt32) : (exactU32 x).size = 4 := by
  simp [exactU32, Bitcoin.Data.serU32]

theorem exactU64_size (x : UInt64) : (exactU64 x).size = 8 := by
  simp [exactU64, Bitcoin.Data.serU64]

theorem exactCS_size_zero : (exactCS 0).size = 1 := by
  simp [exactCS, Bitcoin.Data.compactSizeEnc, Bitcoin.Data.serU8]

structure ExactCommitmentOutput where
  output : CommitmentOutput
  scriptPubKey : ByteArray
deriving Repr, BEq

def ExactCommitmentOutput.toTxOut (o : ExactCommitmentOutput) : TxOut :=
  { value := (o.output.value : Int), scriptPubKey := ⟨o.scriptPubKey⟩ }

structure CommitmentWire where
  version : UInt32
  fundingTxid : ByteArray
  fundingOutputIndex : UInt32
  sequence : UInt32
  outputs : List ExactCommitmentOutput
  locktime : UInt32
deriving Repr, BEq

def CommitmentWire.toTx (w : CommitmentWire) : Tx :=
  { version := w.version.toInt32
    vin := [{ prevout := ⟨w.fundingTxid, w.fundingOutputIndex⟩,
              scriptSig := Script.empty, sequence := w.sequence }]
    vout := w.outputs.map ExactCommitmentOutput.toTxOut
    locktime := w.locktime
    witness := [[]] }

def CommitmentWire.txBytes (w : CommitmentWire) : ByteArray := Bitcoin.Data.serTx w.toTx

theorem hasWitness_toTx (w : CommitmentWire) : hasWitness w.toTx = false := by
  simp [CommitmentWire.toTx, Bitcoin.Serialization.hasWitness]

theorem txBytes_eq_encTxL (w : CommitmentWire) :
    bL w.txBytes = encTxL w.toTx := by
  simp [CommitmentWire.txBytes, Bitcoin.Serialization.encTxL, hasWitness_toTx]



def CommitmentWire.WellFormed (w : CommitmentWire) : Prop :=
  w.fundingTxid.size = 32 ∧
  w.outputs.length ≤ Bitcoin.Serialization.MAX_SIZE ∧
  (∀ o ∈ w.outputs, o.scriptPubKey.size ≤ Bitcoin.Serialization.MAX_SIZE ∧
     o.output.value < 9223372036854775808)

theorem CommitmentWire.wireDomain_toTx (w : CommitmentWire) (h : w.WellFormed) :
    Bitcoin.Serialization.wireDomain w.toTx := by
  obtain ⟨hhash, hlen, hout⟩ := h
  refine ⟨by simp [CommitmentWire.toTx], by simp [CommitmentWire.toTx], ?_, ?_, ?_, ?_, ?_⟩
  · have hv : w.toTx.vin.length = 1 := rfl
    rw [hv]
    decide
  · have hv : w.toTx.vout.length = w.outputs.length := by simp [CommitmentWire.toTx]
    rw [hv]
    exact hlen
  · intro i hi
    rw [CommitmentWire.toTx, List.mem_singleton] at hi
    subst hi
    exact ⟨hhash, by simp [Bitcoin.Data.Script.empty]⟩
  · intro o ho
    rw [CommitmentWire.toTx, List.mem_map] at ho
    obtain ⟨a, ha, rfl⟩ := ho
    obtain ⟨hsz, hval⟩ := hout a ha
    refine ⟨hsz, ?_, ?_⟩
    · exact Int.natCast_nonneg _
    · exact Int.ofNat_lt.mpr hval
  · intro s hs
    rw [CommitmentWire.toTx, List.mem_singleton] at hs
    subst hs
    exact ⟨by simp, by simp⟩

theorem CommitmentWire.txBytes_parse (w : CommitmentWire) (h : w.WellFormed) :
    Bitcoin.Serialization.decTxCore (Bitcoin.Serialization.bL w.txBytes) =
      .ok (w.toTx, []) := by
  rw [txBytes_eq_encTxL]
  simpa using Bitcoin.Serialization.decTxCore_encTxL w.toTx []
    (CommitmentWire.wireDomain_toTx w h)



def compactSizeWidth (n : Nat) : Nat :=
  if n < 0xfd then 1 else if n ≤ 0xffff then 3 else if n ≤ 0xffffffff then 5 else 9

theorem compactSizeEnc_size (n : Nat) :
    (Bitcoin.Data.compactSizeEnc n).size = compactSizeWidth n := by
  unfold Bitcoin.Data.compactSizeEnc compactSizeWidth
  by_cases h1 : n < 0xfd
  · simp [h1, Bitcoin.Data.serU8]
  · by_cases h2 : n ≤ 0xffff
    · simp [h1, h2, Bitcoin.Data.serU8, Bitcoin.Data.serU16]
    · by_cases h3 : n ≤ 0xffffffff
      · simp [h1, h2, h3, Bitcoin.Data.serU8, Bitcoin.Data.serU32]
      · simp [h1, h2, h3, Bitcoin.Data.serU8, Bitcoin.Data.serU64]

theorem foldl_append_size {α : Type} (l : List α) (f : α → ByteArray) (init : ByteArray) :
    (l.foldl (fun acc x => acc ++ f x) init).size =
      init.size + (l.map (fun x => (f x).size)).sum := by
  induction l generalizing init with
  | nil => simp
  | cons x xs ih =>
      simp [List.foldl_cons, ih, ByteArray.size_append, Nat.add_assoc]

def exactOutputBytes (o : ExactCommitmentOutput) : ByteArray :=
  Bitcoin.Data.serTxOut o.toTxOut

theorem exactOutputBytes_size (o : ExactCommitmentOutput) :
    (exactOutputBytes o).size =
      8 + compactSizeWidth o.scriptPubKey.size + o.scriptPubKey.size := by
  simp [exactOutputBytes, ExactCommitmentOutput.toTxOut, Bitcoin.Data.serTxOut,
    Bitcoin.Data.serU64, compactSizeEnc_size]

@[simp] theorem serTxOut_toTxOut_size (o : ExactCommitmentOutput) :
    (Bitcoin.Data.serTxOut o.toTxOut).size =
      8 + compactSizeWidth o.scriptPubKey.size + o.scriptPubKey.size := by
  simp [ExactCommitmentOutput.toTxOut, Bitcoin.Data.serTxOut,
    Bitcoin.Data.serU64, compactSizeEnc_size]

theorem map_serTxOut_size_eq (l : List ExactCommitmentOutput) :
    (l.map (fun o => (Bitcoin.Data.serTxOut o.toTxOut).size)).sum =
      (l.map (fun o => 8 + compactSizeWidth o.scriptPubKey.size +
        o.scriptPubKey.size)).sum := by
  induction l with
  | nil => rfl
  | cons o os _ => simp [serTxOut_toTxOut_size]

theorem CommitmentWire.txBytes_size (w : CommitmentWire) :
    w.txBytes.size =
      4 + 1 + w.fundingTxid.size + 4 + 1 + 4 +
        compactSizeWidth w.outputs.length +
        (w.outputs.map (fun o => 8 + compactSizeWidth o.scriptPubKey.size +
          o.scriptPubKey.size)).sum + 4 := by
  simp [CommitmentWire.txBytes, CommitmentWire.toTx, Bitcoin.Data.serTx,
    Bitcoin.Data.serTxIn, Bitcoin.Data.serU32,
    compactSizeEnc_size, foldl_append_size, ByteArray.size_append,
    Bitcoin.Data.Script.empty, compactSizeWidth, Nat.add_assoc]
  simp [Function.comp_def, compactSizeWidth, Nat.add_assoc]



def byteList (l : List UInt8) : ByteArray := l.toByteArray

def hash32 (b : UInt8) : ByteArray := byteList (List.replicate 32 b)

def vectorFundingTxid : ByteArray := hash32 0x11

def vectorOutput1 : ExactCommitmentOutput :=
  { output := .toRemote 1000
    scriptPubKey := byteList [0x00, 0x14] ++ byteList (List.replicate 20 0x22) }

def vectorOutput2 : ExactCommitmentOutput :=
  { output := .toLocal 2000
    scriptPubKey := byteList [0x00, 0x20] ++ byteList (List.replicate 32 0x33) }

def vectorWire : CommitmentWire :=
  { version := 2
    fundingTxid := vectorFundingTxid
    fundingOutputIndex := 0
    sequence := 0x80000000
    outputs := [vectorOutput1, vectorOutput2]
    locktime := 0x20000000 }

set_option maxRecDepth 10000 in
theorem vectorCommitmentTx :
    Bitcoin.Serialization.bL vectorWire.txBytes =
      [0x02, 0x00, 0x00, 0x00, 0x01] ++ List.replicate 32 0x11 ++
      [0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x80, 0x02,
       0xe8, 0x03, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x16, 0x00, 0x14] ++
      List.replicate 20 0x22 ++
      [0xd0, 0x07, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x22, 0x00, 0x20] ++
      List.replicate 32 0x33 ++
      [0x00, 0x00, 0x00, 0x20] := by
  decide

set_option maxRecDepth 10000 in
theorem vectorCommitmentTx_size : (Bitcoin.Serialization.bL vectorWire.txBytes).length = 125 := by
  decide



structure Bip143Preimage where
  version : UInt32
  hashPrevouts : ByteArray
  hashSequence : ByteArray
  outpointTxid : ByteArray
  outpointIndex : UInt32
  scriptCode : ByteArray
  amountSat : UInt64
  sequence : UInt32
  hashOutputs : ByteArray
  locktime : UInt32
  sighashType : UInt32
deriving Repr, BEq

def Bip143Preimage.preimageBytes (p : Bip143Preimage) : ByteArray :=
  exactU32 p.version ++ p.hashPrevouts ++ p.hashSequence ++
    p.outpointTxid ++ exactU32 p.outpointIndex ++
    exactCS p.scriptCode.size ++ p.scriptCode ++
    exactU64 p.amountSat ++ exactU32 p.sequence ++
    p.hashOutputs ++ exactU32 p.locktime ++ exactU32 p.sighashType

theorem Bip143Preimage.preimageBytes_size (p : Bip143Preimage)
    (hp : p.hashPrevouts.size = 32) (hq : p.hashSequence.size = 32)
    (ho : p.outpointTxid.size = 32) (hh : p.hashOutputs.size = 32) :
    p.preimageBytes.size =
      156 + compactSizeWidth p.scriptCode.size + p.scriptCode.size := by
  simp [Bip143Preimage.preimageBytes, exactU32_size, exactU64_size,
    exactCS, compactSizeEnc_size, hp, hq, ho, hh, ByteArray.size_append, Nat.add_assoc]
  omega

def exactSighashDigest (M : PrimitiveModel) (p : Bip143Preimage) : ByteArray :=
  M.sha256 (M.sha256 p.preimageBytes)

theorem exactSighashDigest_size (M : PrimitiveModel) (p : Bip143Preimage) :
    (exactSighashDigest M p).size = 32 :=
  M.sha256_size _

def vectorPreimage : Bip143Preimage :=
  { version := 2
    hashPrevouts := hash32 0xaa
    hashSequence := hash32 0xbb
    outpointTxid := hash32 0xcc
    outpointIndex := 0
    scriptCode := byteList [0x51]
    amountSat := 1000
    sequence := 0xffffffff
    hashOutputs := hash32 0xdd
    locktime := 0x20000000
    sighashType := 1 }

set_option maxRecDepth 10000 in
theorem vectorPreimage_bytes :
    Bitcoin.Serialization.bL vectorPreimage.preimageBytes =
      [0x02, 0x00, 0x00, 0x00] ++ List.replicate 32 0xaa ++
      List.replicate 32 0xbb ++ List.replicate 32 0xcc ++
      [0x00, 0x00, 0x00, 0x00, 0x01, 0x51,
       0xe8, 0x03, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
       0xff, 0xff, 0xff, 0xff] ++
      List.replicate 32 0xdd ++
      [0x00, 0x00, 0x00, 0x20, 0x01, 0x00, 0x00, 0x00] := by
  decide

set_option maxRecDepth 10000 in
theorem vectorPreimage_size :
    (Bitcoin.Serialization.bL vectorPreimage.preimageBytes).length = 158 := by
  decide

structure HtlcWire where
  version : UInt32
  commitmentTxid : ByteArray
  commitmentOutputIndex : UInt32
  sequence : UInt32
  valueSat : UInt64
  scriptPubKey : ByteArray
  locktime : UInt32
deriving Repr, BEq

def HtlcWire.toTx (h : HtlcWire) : Bitcoin.Data.Tx :=
  { version := h.version.toInt32
    vin := [{ prevout := ⟨h.commitmentTxid, h.commitmentOutputIndex⟩,
              scriptSig := Script.empty, sequence := h.sequence }]
    vout := [{ value := (h.valueSat.toNat : Int), scriptPubKey := ⟨h.scriptPubKey⟩ }]
    locktime := h.locktime
    witness := [[]] }

def HtlcWire.txBytes (h : HtlcWire) : ByteArray := Bitcoin.Data.serTx h.toTx

theorem hasWitness_toTx_htlc (h : HtlcWire) : hasWitness h.toTx = false := by
  simp [HtlcWire.toTx, Bitcoin.Serialization.hasWitness]

theorem HtlcWire.txBytes_eq_encTxL (h : HtlcWire) :
    bL h.txBytes = encTxL h.toTx := by
  simp [HtlcWire.txBytes, Bitcoin.Serialization.encTxL, hasWitness_toTx_htlc]

def HtlcWire.WellFormed (h : HtlcWire) : Prop :=
  h.commitmentTxid.size = 32 ∧
  h.scriptPubKey.size ≤ Bitcoin.Serialization.MAX_SIZE ∧
  h.valueSat < 9223372036854775808

theorem HtlcWire.wireDomain_toTx (h : HtlcWire) (hw : h.WellFormed) :
    Bitcoin.Serialization.wireDomain h.toTx := by
  obtain ⟨hhash, hsz, hval⟩ := hw
  refine ⟨by simp [HtlcWire.toTx], by simp [HtlcWire.toTx], ?_, ?_, ?_, ?_, ?_⟩
  · have hv : h.toTx.vin.length = 1 := rfl
    rw [hv]
    decide
  · have hv : h.toTx.vout.length = 1 := rfl
    rw [hv]
    decide
  · intro i hi
    rw [HtlcWire.toTx, List.mem_singleton] at hi
    subst hi
    exact ⟨hhash, by simp [Bitcoin.Data.Script.empty]⟩
  · intro o ho
    rw [HtlcWire.toTx, List.mem_singleton] at ho
    subst ho
    exact ⟨hsz, Int.natCast_nonneg _, Int.ofNat_lt.mpr hval⟩
  · intro s hs
    rw [HtlcWire.toTx, List.mem_singleton] at hs
    subst hs
    exact ⟨by simp, by simp⟩

theorem HtlcWire.txBytes_parse (h : HtlcWire) (hw : h.WellFormed) :
    Bitcoin.Serialization.decTxCore (Bitcoin.Serialization.bL h.txBytes) =
      .ok (h.toTx, []) := by
  rw [HtlcWire.txBytes_eq_encTxL]
  simpa using Bitcoin.Serialization.decTxCore_encTxL h.toTx []
    (HtlcWire.wireDomain_toTx h hw)

theorem HtlcWire.txBytes_size (h : HtlcWire) :
    h.txBytes.size =
      4 + 1 + h.commitmentTxid.size + 4 + 1 + 4 + 1 +
        8 + compactSizeWidth h.scriptPubKey.size + h.scriptPubKey.size + 4 := by
  simp [HtlcWire.txBytes, HtlcWire.toTx, Bitcoin.Data.serTx,
    Bitcoin.Data.serTxIn, Bitcoin.Data.serTxOut, Bitcoin.Data.serU32,
    Bitcoin.Data.serU64, Bitcoin.Data.Script.empty, compactSizeEnc_size,
    compactSizeWidth, ByteArray.size_append, Nat.add_assoc]
  omega

/-! ### 12.2 Refinement of the structural serializer

The structural serializer `commitmentPreimage` was written before the exact
BOLT 3 byte layout.  The bridge below is deliberately honest:

* `viewOfWire` maps a wire transaction plus the non-wire metadata into the
  existing `CommitmentSighashView`;
* the fields the structural view shares with the wire (funding outpoint,
  output values, obscured commitment number) are proved equal to the wire
  fields (`viewOfWire_*`, `viewOfWire_obscured`);
* `SharedEq` implies equality of structural preimages/digests, i.e. the
  structural serializer is a function of exactly those modelled fields;
* `structuralView_not_determine_scripts` proves the abstraction is strict:
  the structural view alone does not determine the wire bytes, because the
  output `scriptPubKey`s are dropped. -/
structure CommitmentMeta where
  commitmentNumber : Nat
  obscuredCommitmentNumber : Nat
  fundingValueSat : Nat
  fundingScript : ByteArray
  holder : Direction
  toLocalSat : Nat
  toRemoteSat : Nat
  feeSat : Nat
  contestDelay : Nat
  anchorOutputs : Bool
  feeratePerKw : Nat
  htlcs : List HtlcSighashView
deriving Repr, BEq

def viewOfWire (w : CommitmentWire) (m : CommitmentMeta) : CommitmentSighashView :=
  { commitmentNumber := m.commitmentNumber
    obscuredCommitmentNumber := m.obscuredCommitmentNumber
    fundingTxid := w.fundingTxid
    fundingOutputIndex := w.fundingOutputIndex.toNat
    fundingValueSat := m.fundingValueSat
    fundingScript := m.fundingScript
    holder := m.holder
    toLocalSat := m.toLocalSat
    toRemoteSat := m.toRemoteSat
    outputs := w.outputs.map (fun o => o.output)
    feeSat := m.feeSat
    contestDelay := m.contestDelay
    anchorOutputs := m.anchorOutputs
    feeratePerKw := m.feeratePerKw
    htlcs := m.htlcs }

@[simp] theorem viewOfWire_fundingTxid (w : CommitmentWire) (m : CommitmentMeta) :
    (viewOfWire w m).fundingTxid = w.fundingTxid := rfl

@[simp] theorem viewOfWire_fundingOutputIndex (w : CommitmentWire)
    (m : CommitmentMeta) :
    (viewOfWire w m).fundingOutputIndex = w.fundingOutputIndex.toNat := rfl

@[simp] theorem viewOfWire_outputs (w : CommitmentWire) (m : CommitmentMeta) :
    (viewOfWire w m).outputs = w.outputs.map (fun o => o.output) := rfl

@[simp] theorem viewOfWire_commitmentNumber (w : CommitmentWire)
    (m : CommitmentMeta) :
    (viewOfWire w m).commitmentNumber = m.commitmentNumber := rfl

@[simp] theorem viewOfWire_htlcs (w : CommitmentWire) (m : CommitmentMeta) :
    (viewOfWire w m).htlcs = m.htlcs := rfl

/-- The 48-bit BOLT 3 obscured commitment number recovered from the wire
`nSequence` (high 24 bits) and `nLockTime` (low 24 bits). -/
def obscuredOfWire (w : CommitmentWire) : Nat :=
  (w.sequence.toNat % 2 ^ 24) * 2 ^ 24 + (w.locktime.toNat % 2 ^ 24)

/-- The BOLT 3 bit layout of the obscured commitment number in the commitment
transaction: `nLockTime = 0x20000000 | low24` and
`nSequence = 0x80000000 | high24`. -/
def Obscures (w : CommitmentWire) (m : CommitmentMeta) : Prop :=
  m.obscuredCommitmentNumber < 2 ^ 48 ∧
  w.locktime.toNat = 0x20000000 + (m.obscuredCommitmentNumber % 2 ^ 24) ∧
  w.sequence.toNat = 0x80000000 + ((m.obscuredCommitmentNumber / 2 ^ 24) % 2 ^ 24)

theorem obscuredOfWire_eq_of_obscures (w : CommitmentWire) (m : CommitmentMeta)
    (h : Obscures w m) :
    obscuredOfWire w = m.obscuredCommitmentNumber % 2 ^ 48 := by
  obtain ⟨_, hl, hs⟩ := h
  unfold obscuredOfWire
  rw [hl, hs]
  omega

theorem viewOfWire_obscured (w : CommitmentWire) (m : CommitmentMeta)
    (h : Obscures w m) :
    (viewOfWire w m).obscuredCommitmentNumber = obscuredOfWire w := by
  show m.obscuredCommitmentNumber = obscuredOfWire w
  rw [obscuredOfWire_eq_of_obscures w m h, Nat.mod_eq_of_lt h.1]

/-- Two wires share all fields that the structural serializer models: the
funding outpoint and the sequence of output values.  Version, sequence,
locktime and the output scripts are *not* part of this relation. -/
def SharedEq (w₁ w₂ : CommitmentWire) : Prop :=
  w₁.fundingTxid = w₂.fundingTxid ∧
  w₁.fundingOutputIndex = w₂.fundingOutputIndex ∧
  w₁.outputs.map (fun o => o.output) = w₂.outputs.map (fun o => o.output)

theorem viewOfWire_eq_of_shared (w₁ w₂ : CommitmentWire) (m : CommitmentMeta)
    (h : SharedEq w₁ w₂) : viewOfWire w₁ m = viewOfWire w₂ m := by
  obtain ⟨htxid, hidx, hout⟩ := h
  simp [viewOfWire, htxid, hidx, hout]

theorem commitmentPreimage_eq_of_shared (w₁ w₂ : CommitmentWire)
    (m : CommitmentMeta) (h : SharedEq w₁ w₂) :
    commitmentPreimage (viewOfWire w₁ m) = commitmentPreimage (viewOfWire w₂ m) := by
  rw [viewOfWire_eq_of_shared w₁ w₂ m h]

theorem commitmentDigest_eq_of_shared (M : PrimitiveModel) (w₁ w₂ : CommitmentWire)
    (m : CommitmentMeta) (h : SharedEq w₁ w₂) :
    commitmentDigest M (viewOfWire w₁ m) = commitmentDigest M (viewOfWire w₂ m) := by
  simp [commitmentDigest, commitmentPreimage_eq_of_shared w₁ w₂ m h]

def vectorMeta : CommitmentMeta :=
  { commitmentNumber := 7
    obscuredCommitmentNumber := 0x123456789abc
    fundingValueSat := 3000
    fundingScript := byteList [0x00, 0x14] ++ byteList (List.replicate 20 0x44)
    holder := .local
    toLocalSat := 2000
    toRemoteSat := 1000
    feeSat := 0
    contestDelay := 144
    anchorOutputs := false
    feeratePerKw := 253
    htlcs := [] }

/-- Same transaction fields and output values, but a different `scriptPubKey`
on the first output. -/
def vectorWireShortScript : CommitmentWire :=
  { vectorWire with
    outputs := [{ vectorOutput1 with scriptPubKey := byteList [0x51] },
      vectorOutput2] }

theorem vectorView_eq :
    viewOfWire vectorWire vectorMeta = viewOfWire vectorWireShortScript vectorMeta := by
  simp [viewOfWire, vectorWire, vectorWireShortScript, vectorOutput1, vectorOutput2]

/-- The structural view is strictly coarser than the exact byte layout: two
wire transactions with the same structural view can serialize to different
bytes because output `scriptPubKey`s are not modelled by the structural view. -/
theorem structuralView_not_determine_scripts :
    ∃ (w₁ w₂ : CommitmentWire) (m : CommitmentMeta),
      viewOfWire w₁ m = viewOfWire w₂ m ∧ w₁.txBytes ≠ w₂.txBytes := by
  refine ⟨vectorWire, vectorWireShortScript, vectorMeta, vectorView_eq, ?_⟩
  intro hbytes
  have h₁ := CommitmentWire.txBytes_size vectorWire
  have h₂ := CommitmentWire.txBytes_size vectorWireShortScript
  rw [hbytes] at h₁
  simp [vectorWire, vectorWireShortScript, vectorOutput1, vectorOutput2,
    compactSizeWidth, byteList] at h₁ h₂
  omega

/-! ## 13. Preimage byte-equality with the vendored BIP 143 encoder -/

open Bitcoin.Serialization

set_option maxRecDepth 10000

/-- The `LnLean.Bitcoin.Sighash.Preimage` determined by an exact-wire
`Bip143Preimage`.  The outpoint txid is kept in consensus-internal byte order;
`amountSat` is lifted to the signed `Amount` of the sighash model. -/
def Bip143Preimage.toPreimage (p : Bip143Preimage) : LnLean.Bitcoin.Sighash.Preimage :=
  { version := p.version
    hashPrevouts := p.hashPrevouts
    hashSequence := p.hashSequence
    outpoint := ⟨p.outpointTxid, p.outpointIndex⟩
    scriptCode := p.scriptCode
    amount := (p.amountSat.toNat : Int)
    sequence := p.sequence
    hashOutputs := p.hashOutputs
    lockTime := p.locktime
    hashType := p.sighashType }

/-! ### 13.1 Field serializers agree with the vendored BIP 143 serializers -/

theorem bL_exactU32 (x : UInt32) :
    bL (exactU32 x) = Bitcoin.SigHash.serU32L x := by
  rw [exactU32, Bitcoin.Serialization.bL_serU32]
  rfl

theorem bL_exactU64 (x : UInt64) :
    bL (exactU64 x) = Bitcoin.SigHash.serU64L x := by
  rw [exactU64, Bitcoin.Serialization.bL_serU64]
  rfl

theorem bL_exactCS (n : Nat) :
    bL (exactCS n) = Bitcoin.Serialization.encCSL n := by
  rw [exactCS, Bitcoin.Serialization.bL_compactSizeEnc]

theorem serU64L_ofNat_toNat (x : UInt64) :
    Bitcoin.SigHash.serU64L (UInt64.ofInt (Int.ofNat x.toNat)) =
      Bitcoin.SigHash.serU64L x := by
  have hx : UInt64.ofInt (Int.ofNat x.toNat) = x := by
    unfold UInt64.ofInt
    have h1 : (0 : Int) ≤ (x.toNat : Int) := Int.natCast_nonneg _
    have h2 : (x.toNat : Int) < (2 : Int) ^ 64 := by
      exact_mod_cast x.toNat_lt
    have h3 : Int.ofNat x.toNat % (2 : Int) ^ 64 = Int.ofNat x.toNat :=
      Int.emod_eq_of_lt h1 h2
    rw [h3]
    have h4 : (Int.ofNat x.toNat).toNat = x.toNat := Int.toNat_natCast x.toNat
    rw [h4]
    exact UInt64.ofNat_toNat
  rw [hx]

/-! ### 13.2 The ten fields in consensus order -/

/-- The exact-wire preimage in the byte order of the vendored
`Bitcoin.SigHash.bip143MsgL`: version, `hashPrevouts`, `hashSequence`,
outpoint txid (internal order), outpoint index (LE), CompactSize scriptCode
length, scriptCode, amount (LE), sequence (LE), `hashOutputs`, locktime (LE),
hash type (LE).  All hash fields are inserted verbatim, never reversed. -/
theorem Bip143Preimage.preimageBytes_fields (p : Bip143Preimage) :
    bL p.preimageBytes =
      Bitcoin.SigHash.serU32L p.version ++ bL p.hashPrevouts ++
      bL p.hashSequence ++ bL p.outpointTxid ++
      Bitcoin.SigHash.serU32L p.outpointIndex ++
      Bitcoin.Serialization.encCSL p.scriptCode.size ++ bL p.scriptCode ++
      Bitcoin.SigHash.serU64L p.amountSat ++
      Bitcoin.SigHash.serU32L p.sequence ++ bL p.hashOutputs ++
      Bitcoin.SigHash.serU32L p.locktime ++ Bitcoin.SigHash.serU32L p.sighashType := by
  simp [Bip143Preimage.preimageBytes, bL_exactU32, bL_exactU64, bL_exactCS]

/-- Literal byte equality of the exact-wire preimage with the model encoder
`LnLean.Bitcoin.Sighash.encode`. -/
theorem Bip143Preimage.preimageBytes_eq_encode (p : Bip143Preimage) :
    bL p.preimageBytes = bL (LnLean.Bitcoin.Sighash.encode p.toPreimage) := by
  rw [Bip143Preimage.preimageBytes_fields]
  simp [Bip143Preimage.toPreimage, LnLean.Bitcoin.Sighash.encode,
    LnLean.Bitcoin.Sighash.bL_serU32LE, LnLean.Bitcoin.Sighash.bL_serU64LE,
    LnLean.Bitcoin.Sighash.bL_compactSize, LnLean.Bitcoin.Sighash.bL_serOutpoint,
    Bitcoin.SigHash.serOutpointL]
  exact (serU64L_ofNat_toNat p.amountSat).symm

/-- `ByteArray`-level form of `preimageBytes_eq_encode`. -/
theorem Bip143Preimage.preimageBytes_eq_encode_bytes (p : Bip143Preimage) :
    p.preimageBytes = LnLean.Bitcoin.Sighash.encode p.toPreimage :=
  bL_inj (Bip143Preimage.preimageBytes_eq_encode p)

/-! ### 13.3 Deriving the preimage from a transaction -/

/-- The exact-wire preimage computed from a transaction, mirroring
`LnLean.Bitcoin.Sighash.ofTx` but keeping the amount unsigned. -/
def Bip143Preimage.ofTx (tx : Bitcoin.Data.Tx) (nIn : Nat)
    (scriptCode : ByteArray) (ht : UInt32) (amountSat : UInt64) : Bip143Preimage :=
  { version := tx.version.toUInt32
    hashPrevouts := LnLean.Bitcoin.Sighash.hashPrevoutsOf tx ht
    hashSequence := LnLean.Bitcoin.Sighash.hashSequenceOf tx ht
    outpointTxid := (tx.vin.getD nIn LnLean.Bitcoin.Sighash.dummyTxIn).prevout.hash
    outpointIndex := (tx.vin.getD nIn LnLean.Bitcoin.Sighash.dummyTxIn).prevout.n
    scriptCode := scriptCode
    amountSat := amountSat
    sequence := (tx.vin.getD nIn LnLean.Bitcoin.Sighash.dummyTxIn).sequence
    hashOutputs := LnLean.Bitcoin.Sighash.hashOutputsOf tx nIn ht
    locktime := tx.locktime
    sighashType := ht }

theorem Bip143Preimage.toPreimage_ofTx (tx : Bitcoin.Data.Tx) (nIn : Nat)
    (scriptCode : ByteArray) (ht : UInt32) (amountSat : UInt64) :
    (Bip143Preimage.ofTx tx nIn scriptCode ht amountSat).toPreimage =
      LnLean.Bitcoin.Sighash.ofTx tx nIn scriptCode ht (amountSat.toNat : Int) := by
  simp [Bip143Preimage.ofTx, Bip143Preimage.toPreimage,
    LnLean.Bitcoin.Sighash.ofTx]

/-- The `hashPrevouts` field of a transaction-derived preimage is exactly the
vendored 32-byte sub-hash, in internal order (never reversed). -/
theorem Bip143Preimage.ofTx_hashPrevouts (tx : Bitcoin.Data.Tx) (nIn : Nat)
    (scriptCode : ByteArray) (ht : UInt32) (amountSat : UInt64) :
    bL (Bip143Preimage.ofTx tx nIn scriptCode ht amountSat).hashPrevouts =
      Bitcoin.SigHash.hashPrevoutsL tx ht := by
  simp [Bip143Preimage.ofTx, LnLean.Bitcoin.Sighash.bL_hashPrevoutsOf]

/-- The `hashSequence` field is exactly the vendored sub-hash. -/
theorem Bip143Preimage.ofTx_hashSequence (tx : Bitcoin.Data.Tx) (nIn : Nat)
    (scriptCode : ByteArray) (ht : UInt32) (amountSat : UInt64) :
    bL (Bip143Preimage.ofTx tx nIn scriptCode ht amountSat).hashSequence =
      Bitcoin.SigHash.hashSequenceL tx ht := by
  simp [Bip143Preimage.ofTx, LnLean.Bitcoin.Sighash.bL_hashSequenceOf]

/-- The `hashOutputs` field is exactly the vendored sub-hash. -/
theorem Bip143Preimage.ofTx_hashOutputs (tx : Bitcoin.Data.Tx) (nIn : Nat)
    (scriptCode : ByteArray) (ht : UInt32) (amountSat : UInt64) :
    bL (Bip143Preimage.ofTx tx nIn scriptCode ht amountSat).hashOutputs =
      Bitcoin.SigHash.hashOutputsL tx nIn ht := by
  simp [Bip143Preimage.ofTx, LnLean.Bitcoin.Sighash.bL_hashOutputsOf]

/-- **Byte equality with the vendored encoder.**  For a preimage derived from a
transaction, `Bip143Preimage.preimageBytes` is exactly the list produced by the
vendored `Bitcoin.SigHash.bip143MsgL` (the BIP 143 `SignatureHash` preimage). -/
theorem Bip143Preimage.preimageBytes_eq_bip143MsgL_ofTx
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (scriptCode : ByteArray) (ht : UInt32)
    (amountSat : UInt64) :
    bL (Bip143Preimage.ofTx tx nIn scriptCode ht amountSat).preimageBytes =
      Bitcoin.SigHash.bip143MsgL tx nIn (bL scriptCode) ht (amountSat.toNat : Int) := by
  rw [Bip143Preimage.preimageBytes_eq_encode, Bip143Preimage.toPreimage_ofTx]
  exact LnLean.Bitcoin.Sighash.bL_encode_ofTx tx nIn scriptCode ht (amountSat.toNat : Int)

/-- `ByteArray` form against the model encoder, for a transaction-derived
preimage. -/
theorem Bip143Preimage.preimageBytes_eq_encode_ofTx
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (scriptCode : ByteArray) (ht : UInt32)
    (amountSat : UInt64) :
    (Bip143Preimage.ofTx tx nIn scriptCode ht amountSat).preimageBytes =
      LnLean.Bitcoin.Sighash.encode
        (LnLean.Bitcoin.Sighash.ofTx tx nIn scriptCode ht (amountSat.toNat : Int)) := by
  rw [Bip143Preimage.preimageBytes_eq_encode_bytes, Bip143Preimage.toPreimage_ofTx]

/-- A BOLT 3 commitment-wire preimage: `nIn = 0` because `CommitmentWire.toTx`
has exactly one input. -/
def commitmentBip143Preimage (w : CommitmentWire) (scriptCode : ByteArray)
    (ht : UInt32) (amountSat : UInt64) : Bip143Preimage :=
  Bip143Preimage.ofTx w.toTx 0 scriptCode ht amountSat

/-- The wire outpoint, sequence, locktime and version are the ones that appear
in the BIP 143 preimage.  This is the script/outpoint byte-order tie to BOLT 3:
the funding txid is the wire `fundingTxid` in internal order, the index is the
wire `fundingOutputIndex` little-endian, and no reversal is inserted. -/
theorem commitmentBip143Preimage_wire_fields (w : CommitmentWire)
    (scriptCode : ByteArray) (ht : UInt32) (amountSat : UInt64) :
    (commitmentBip143Preimage w scriptCode ht amountSat).version = w.version ∧
    (commitmentBip143Preimage w scriptCode ht amountSat).outpointTxid = w.fundingTxid ∧
    (commitmentBip143Preimage w scriptCode ht amountSat).outpointIndex =
      w.fundingOutputIndex ∧
    (commitmentBip143Preimage w scriptCode ht amountSat).sequence = w.sequence ∧
    (commitmentBip143Preimage w scriptCode ht amountSat).locktime = w.locktime := by
  simp [commitmentBip143Preimage, Bip143Preimage.ofTx, CommitmentWire.toTx]

/-- The commitment-wire preimage is byte-equal to the vendored BIP 143
preimage of the exact wire transaction. -/
theorem commitmentBip143Preimage_eq_bip143MsgL (w : CommitmentWire)
    (scriptCode : ByteArray) (ht : UInt32) (amountSat : UInt64) :
    bL (commitmentBip143Preimage w scriptCode ht amountSat).preimageBytes =
      Bitcoin.SigHash.bip143MsgL w.toTx 0 (bL scriptCode) ht
        (amountSat.toNat : Int) :=
  Bip143Preimage.preimageBytes_eq_bip143MsgL_ofTx w.toTx 0 scriptCode ht amountSat

/-! ### 13.4 Digest equality -/

theorem dshaL_bL_eq_dsha (b : ByteArray) :
    Bitcoin.SigHash.dshaL (bL b) = LnLean.Bitcoin.Sighash.dsha b :=
  bL_inj (LnLean.Bitcoin.Sighash.bL_dsha b)

/-- The model digest of the bridged preimage is the vendored double-SHA-256 of
exactly the `preimageBytes` (hence of the same consensus byte order). -/
theorem Bip143Preimage.toPreimage_digest_eq_dshaL (p : Bip143Preimage) :
    LnLean.Bitcoin.Sighash.digest p.toPreimage =
      Bitcoin.SigHash.dshaL (bL p.preimageBytes) := by
  rw [LnLean.Bitcoin.Sighash.digest, Bip143Preimage.preimageBytes_eq_encode_bytes,
    dshaL_bL_eq_dsha]

/-- For an in-range transaction input, the digest of the bridged preimage is
exactly the vendored BIP 143 sighash. -/
theorem Bip143Preimage.digest_eq_sighashWitnessV0_ofTx
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (scriptCode : ByteArray) (ht : UInt32)
    (amountSat : UInt64) (h : nIn < tx.vin.length) :
    LnLean.Bitcoin.Sighash.digest
        (Bip143Preimage.ofTx tx nIn scriptCode ht amountSat).toPreimage =
      Bitcoin.SigHash.signatureHashBip143Impl tx nIn (bL scriptCode) ht
        (amountSat.toNat : Int) := by
  rw [Bip143Preimage.toPreimage_ofTx]
  have hle : ¬ tx.vin.length ≤ nIn := Nat.not_le.mpr h
  rw [← LnLean.Bitcoin.Sighash.sighashWitnessV0_eq_vendorImpl tx nIn scriptCode ht
    (amountSat.toNat : Int)]
  simp [LnLean.Bitcoin.Sighash.sighashWitnessV0, hle]

/-- The abstract `PrimitiveModel` digest agrees with the vendored hash exactly
when the model's `sha256` field is the vendored seam hash.  The hypothesis is
explicit: the model does not identify an arbitrary `M.sha256` with SHA-256. -/
theorem exactSighashDigest_eq_vendor_of_model (M : LnLean.Crypto.PrimitiveModel)
    (hM : ∀ b, M.sha256 b = Bitcoin.Crypto.Seam.sha256 b)
    (p : Bip143Preimage) :
    exactSighashDigest M p = Bitcoin.SigHash.dshaL (bL p.preimageBytes) := by
  have hb : Bitcoin.Serialization.bytesOfList (bL p.preimageBytes) = p.preimageBytes :=
    Bitcoin.Serialization.bytesOfList_bL p.preimageBytes
  simp [exactSighashDigest, Bitcoin.SigHash.dshaL, hM, hb,
    Bitcoin.Crypto.Seam.sha256d, Bitcoin.Crypto.Seam.sha256,
    Bitcoin.Crypto.Seam.Hash.sha256d]

/-- Under the same explicit seam hypothesis, the `PrimitiveModel` digest is
the model digest of the bridged preimage. -/
theorem exactSighashDigest_eq_digest_of_model (M : LnLean.Crypto.PrimitiveModel)
    (hM : ∀ b, M.sha256 b = Bitcoin.Crypto.Seam.sha256 b)
    (p : Bip143Preimage) :
    exactSighashDigest M p = LnLean.Bitcoin.Sighash.digest p.toPreimage := by
  rw [exactSighashDigest_eq_vendor_of_model M hM p,
    ← Bip143Preimage.toPreimage_digest_eq_dshaL p]

/-! ### 13.5 Byte-level vectors against the vendored encoder -/

/-- A commitment-wire preimage using `SIGHASH_NONE|ANYONECANPAY` (`0x82`), so
the three sub-hashes are the BIP 143 zero vector and the vendored encoder is
decidable byte-for-byte (no hashing needed to check the layout). -/
def vectorWirePreimage : Bip143Preimage :=
  commitmentBip143Preimage vectorWire vectorMeta.fundingScript 0x82 3000

theorem vectorWirePreimage_bytes :
    bL vectorWirePreimage.preimageBytes =
      [0x02, 0x00, 0x00, 0x00] ++ List.replicate 32 0x00 ++
      List.replicate 32 0x00 ++ List.replicate 32 0x11 ++
      [0x00, 0x00, 0x00, 0x00, 0x16, 0x00, 0x14] ++
      List.replicate 20 0x44 ++
      [0xb8, 0x0b, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
       0x00, 0x00, 0x00, 0x80] ++
      List.replicate 32 0x00 ++
      [0x00, 0x00, 0x00, 0x20, 0x82, 0x00, 0x00, 0x00] := by
  decide

theorem vectorWirePreimage_size :
    (bL vectorWirePreimage.preimageBytes).length = 179 := by
  decide

/-- The same 179 bytes from the vendored `bip143MsgL`.  This is the direct
byte-level check of `preimageBytes` against the vendored encoder on the
commitment-wire outpoint, scriptCode, amount, sequence and locktime. -/
theorem vectorWirePreimage_vendor_bytes :
    Bitcoin.SigHash.bip143MsgL vectorWire.toTx 0 (bL vectorMeta.fundingScript)
        0x82 3000 =
      [0x02, 0x00, 0x00, 0x00] ++ List.replicate 32 0x00 ++
      List.replicate 32 0x00 ++ List.replicate 32 0x11 ++
      [0x00, 0x00, 0x00, 0x00, 0x16, 0x00, 0x14] ++
      List.replicate 20 0x44 ++
      [0xb8, 0x0b, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
       0x00, 0x00, 0x00, 0x80] ++
      List.replicate 32 0x00 ++
      [0x00, 0x00, 0x00, 0x20, 0x82, 0x00, 0x00, 0x00] := by
  decide

/-- The two encoders agree on the vector (general theorem instantiation). -/
theorem vectorWirePreimage_vendor :
    bL vectorWirePreimage.preimageBytes =
      Bitcoin.SigHash.bip143MsgL vectorWire.toTx 0 (bL vectorMeta.fundingScript)
        0x82 3000 :=
  commitmentBip143Preimage_eq_bip143MsgL vectorWire vectorMeta.fundingScript 0x82 3000

/-- Byte slice of the vector showing the outpoint: 32-byte funding txid
(internal order, not reversed) followed by the 4-byte little-endian index. -/
theorem vectorWirePreimage_outpoint_bytes :
    ((bL vectorWirePreimage.preimageBytes).drop 68).take 36 =
      List.replicate 32 0x11 ++ [0x00, 0x00, 0x00, 0x00] := by
  decide

/-- Byte slice of the vector showing the scriptCode CompactSize prefix and the
first two program bytes.  `0x16 = 22` is the one-byte CompactSize for the
22-byte P2WSH funding scriptCode `0x00 0x14 ‖ 20×0x44`. -/
theorem vectorWirePreimage_scriptCode_bytes :
    ((bL vectorWirePreimage.preimageBytes).drop 104).take 3 =
      [0x16, 0x00, 0x14] := by
  decide

/-- A 253-byte scriptCode exercises the three-byte CompactSize path
(`0xfd 0xfd 0x00`). -/
def vectorLongScript : ByteArray := byteList (List.replicate 253 0x77)

def vectorLongPreimage : Bip143Preimage :=
  commitmentBip143Preimage vectorWire vectorLongScript 0x82 3000

theorem vectorLongPreimage_size :
    (bL vectorLongPreimage.preimageBytes).length = 412 := by
  decide

theorem vectorLongPreimage_scriptCode_prefix :
    ((bL vectorLongPreimage.preimageBytes).drop 104).take 3 =
      [0xfd, 0xfd, 0x00] := by
  decide

theorem vectorLongPreimage_vendor_prefix :
    ((Bitcoin.SigHash.bip143MsgL vectorWire.toTx 0 (bL vectorLongScript) 0x82
      3000).drop 104).take 3 = [0xfd, 0xfd, 0x00] := by
  decide

/-- The existing 158-byte vector is also produced by the model encoder
`LnLean.Bitcoin.Sighash.encode` (same consensus order). -/
theorem vectorPreimage_encode_bytes :
    bL (LnLean.Bitcoin.Sighash.encode vectorPreimage.toPreimage) =
      [0x02, 0x00, 0x00, 0x00] ++ List.replicate 32 0xaa ++
      List.replicate 32 0xbb ++ List.replicate 32 0xcc ++
      [0x00, 0x00, 0x00, 0x00, 0x01, 0x51,
       0xe8, 0x03, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
       0xff, 0xff, 0xff, 0xff] ++
      List.replicate 32 0xdd ++
      [0x00, 0x00, 0x00, 0x20, 0x01, 0x00, 0x00, 0x00] := by
  rw [← Bip143Preimage.preimageBytes_eq_encode]
  exact vectorPreimage_bytes


end LnLean.Proofs.Channel.SighashTargets
