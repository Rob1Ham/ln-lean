import Bitcoin.Data.Basic
import Bitcoin.Data.Script
import Bitcoin.Data.Tx
import LnLean.Basic.Core
import LnLean.Bitcoin.Seam

/-!
# LnLean.Bitcoin.Funding

English claim: a Lightning channel is funded by a single P2WSH output whose
witness script is the BOLT 3 `2 <funding_pubkey1> <funding_pubkey2>
2 OP_CHECKMULTISIG` script, with the two compressed funding keys in
lexicographic order.  Before the funding transaction confirms, the channel
uses a random *temporary* channel id; after confirmation the channel id is
the funding txid (the *final* channel id).  The model separates those two
roles in the type system, and states confirmation as a predicate over an L1
transaction output rather than proving L1 confirmation.

Anchors:
* BOLT 2, "The `open_channel` Message" and "The `funding_created` Message"
  (temporary channel id, funding satoshis, push_msat, funding keys).
* BOLT 3, "Funding Transaction Output" (`refs/bolts/03-transactions.md:75-83`
  at BOLT commit `1aadb719b4007c4cea0ba6e36b08c4fb53788dee`):
  the output is the P2WSH of `2 <pubkey1> <pubkey2> 2 OP_CHECKMULTISIG`.
* `refs/rust-lightning/lightning/src/ln/chan_utils.rs:849-866`
  (`make_funding_redeemscript`, and the key-ordering in
  `make_funding_redeemscript_from_slices`).
* `refs/rust-lightning/lightning/src/ln/channel.rs:348-362` (`channel_id`,
  `funding_txo`), `:2711-2725` (`get_funding_txo` and funding script), and
  `:4174`, `:4498-4499` (temporary id during negotiation).

Not modelled:
* SHA256 / HASH160.  `witnessScriptHash` is a parameter; the bridge
  `witnessScriptHash = SHA256(witnessScript)` is deliberately not asserted
  here (it belongs to the crypto workstream).
* L1 consensus and chain confirmation.  `FundingConfirmed` is a predicate
  over `Bitcoin.Data.Tx`; no theorem proves that a transaction is mined or
  that the output is spendable by the 2-of-2.
* Funding transaction construction, fee payment, and RBF.
* Script execution / signature checking.
-/

namespace LnLean.Bitcoin

set_option autoImplicit false

open Bitcoin.Data

/-! ## Channel identifiers: temporary versus final -/

/-- A 32-byte temporary channel id selected by the channel opener before the
funding txid is known (BOLT 2, `open_channel`).  Keeping this a distinct type
from `FinalChannelId` prevents the common bug of treating a pre-funding id as
a stable channel identifier. -/
structure TemporaryChannelId where
  id : ChannelId
deriving Repr, BEq

/-- The final channel id, equal to the funding txid once the funding output is
known (BOLT 2, `funding_created`/`funding_signed`). -/
structure FinalChannelId where
  id : ChannelId
deriving Repr, BEq

/-- The final channel id agrees with the funding outpoint's txid.  This is the
wire-level BOLT 2 rule; it is a predicate because txid byte order and hashing
belong to the L1/crypto seam. -/
def FinalChannelId.MatchesOutpoint (c : FinalChannelId) (o : OutPoint) : Prop :=
  c.id.bytes = o.hash

/-- Build the final channel id from a funding outpoint. -/
def FinalChannelId.fromFundingOutpoint (o : OutPoint) : FinalChannelId :=
  ⟨⟨o.hash⟩⟩

theorem FinalChannelId.fromFundingOutpoint_matches (o : OutPoint) :
    (FinalChannelId.fromFundingOutpoint o).MatchesOutpoint o := by
  rfl

/-! ## Funding parameters -/

/-- Parameters of the funding output.  `fundingSatoshis` is the L1 output
value (BOLT 2 `funding_satoshis`), while `pushMsat` is the initial amount the
funder gives the fundee (BOLT 2 `push_msat`).  The units are kept distinct
(`BtcAmount` versus `Msat`) to make conversion explicit. -/
structure FundingParams where
  fundingSatoshis : BtcAmount
  pushMsat : Msat
  localFundingKey : PubKey
  remoteFundingKey : PubKey
  /-- `SHA256(witnessScript)`, supplied by the crypto seam. -/
  witnessScriptHash : ByteArray
  temporaryChannelId : TemporaryChannelId
  finalChannelId? : Option FinalChannelId := none
deriving Repr

/-- Structural well-formedness: a non-negative in-range funding value, valid
compressed keys, a 32-byte witness-script hash, and `push_msat` no larger than
the channel value in millisatoshis. -/
def FundingParams.WellFormed (p : FundingParams) : Prop :=
  0 ≤ p.fundingSatoshis ∧
  p.fundingSatoshis ≤ Bitcoin.Data.MAX_MONEY ∧
  p.localFundingKey.Valid ∧
  p.remoteFundingKey.Valid ∧
  p.witnessScriptHash.size = 32 ∧
  (p.pushMsat.val : Int) ≤ p.fundingSatoshis * (Msat.MSAT_PER_SAT : Int)

/-- Lexicographic order on byte lists, used only to pick the BOLT 3 key
order.  The definition is total and computable; it is not a consensus
primitive. -/
def listLexLE : List UInt8 → List UInt8 → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs =>
      if a < b then true else if b < a then false else listLexLE as bs

/-- Return the two compressed funding keys in the lexicographic order required
by BOLT 3 (`pubkey1` lesser, `pubkey2` greater). -/
def orderedFundingKeys (a b : PubKey) : PubKey × PubKey :=
  if listLexLE a.bytes.toList b.bytes.toList then (a, b) else (b, a)

/-- The 2-of-2 funding witness script:
`OP_2 <pubkey1> <pubkey2> OP_2 OP_CHECKMULTISIG`. -/
def FundingParams.witnessScript (p : FundingParams) : Script :=
  let keys := orderedFundingKeys p.localFundingKey p.remoteFundingKey
  ⟨(ByteArray.empty.push 0x52)                     -- OP_2
     ++ pushData keys.1.bytes
     ++ pushData keys.2.bytes
     ++ (ByteArray.empty.push 0x52)                -- OP_2
     ++ (ByteArray.empty.push OP_CHECKMULTISIG)⟩

/-- Funding output script: P2WSH over `witnessScript`.  The hash is a
parameter, matching `LnLean.Bitcoin.fundingScriptPubKey`. -/
def FundingParams.fundingScriptPubKey (p : FundingParams) : Script :=
  LnLean.Bitcoin.fundingScriptPubKey p.witnessScriptHash

/-! ## The BOLT 3 witness script as a constructed object

`FundingParams.witnessScript` is a computed field, and `witnessScriptHash` is
an unconstrained stored field.  The structures below make the missing step
explicit and constructive: a `FundingScript` carries the key pair it was built
from together with the ordered pair and the script bytes, and a
`FundingNegotiation` carries the handshake-negotiated fields and *derives* the
P2WSH program as `H (witnessScript.bytes)`.  There is no way to build a
`FundingNegotiation.toFundingParams` record with an unrelated hash, so the
"hash link" of `LN-L1-001` becomes a definitional equality for constructed
parameters instead of an arbitrary hypothesis. -/

/-- The BOLT 3 2-of-2 funding witness script, carrying both the original
(local, remote) key orientation and the ordered pair actually serialized into
the script. -/
structure FundingScript where
  /-- The funding key contributed by this endpoint (`open_channel`). -/
  localFundingKey : PubKey
  /-- The funding key contributed by the peer (`accept_channel`). -/
  remoteFundingKey : PubKey
  /-- `pubkey1`: the lexicographically lesser of the two keys. -/
  firstFundingKey : PubKey
  /-- `pubkey2`: the lexicographically greater of the two keys. -/
  secondFundingKey : PubKey
  /-- `OP_2 <pubkey1> <pubkey2> OP_2 OP_CHECKMULTISIG`. -/
  witnessScript : Script
deriving Repr

namespace FundingScript

/-- Build the BOLT 3 funding witness script from an unordered key pair.  The
serialized key order is chosen by `orderedFundingKeys`; the original
orientation is retained so the record still identifies which endpoint
contributed which key. -/
def ofKeys (a b : PubKey) : FundingScript :=
  let keys := orderedFundingKeys a b
  { localFundingKey := a
    remoteFundingKey := b
    firstFundingKey := keys.1
    secondFundingKey := keys.2
    witnessScript :=
      ⟨(ByteArray.empty.push 0x52)                       -- OP_2
         ++ pushData keys.1.bytes
         ++ pushData keys.2.bytes
         ++ (ByteArray.empty.push 0x52)                  -- OP_2
         ++ (ByteArray.empty.push OP_CHECKMULTISIG)⟩ }

@[simp] theorem ofKeys_localFundingKey (a b : PubKey) :
    (ofKeys a b).localFundingKey = a := rfl

@[simp] theorem ofKeys_remoteFundingKey (a b : PubKey) :
    (ofKeys a b).remoteFundingKey = b := rfl

@[simp] theorem ofKeys_firstFundingKey (a b : PubKey) :
    (ofKeys a b).firstFundingKey =
      (orderedFundingKeys a b).1 := rfl

@[simp] theorem ofKeys_secondFundingKey (a b : PubKey) :
    (ofKeys a b).secondFundingKey =
      (orderedFundingKeys a b).2 := rfl

/-- The constructed script is exactly the BOLT 3 template over the ordered
pair, with the exact bytes a BOLT 3 verifier sees. -/
theorem ofKeys_witnessScript_bytes (a b : PubKey) :
    (ofKeys a b).witnessScript.bytes =
      (ByteArray.empty.push 0x52)
        ++ pushData (orderedFundingKeys a b).1.bytes
        ++ pushData (orderedFundingKeys a b).2.bytes
        ++ (ByteArray.empty.push 0x52)
        ++ (ByteArray.empty.push OP_CHECKMULTISIG) := rfl

/-- The first key of the constructed script is the first element of
`orderedFundingKeys`: the pair is ordered, not re-derived. -/
theorem ofKeys_orderedFirst (a b : PubKey) :
    (ofKeys a b).firstFundingKey = (orderedFundingKeys a b).1 := rfl

/-- The constructed script is definitionally the script that
`FundingParams.witnessScript` computes for the same key pair.  This is the
bridge between the constructor and the pre-existing `FundingParams` model; it
needs no hash assumption. -/
theorem ofKeys_witnessScript_eq_witnessScript (p : FundingParams) :
    (ofKeys p.localFundingKey p.remoteFundingKey).witnessScript =
      p.witnessScript := rfl

/-- The constructed script is a 2-of-2 multisig over exactly the two input
keys: abstract form, without committing to which key is serialized first.
The `TwoOfTwoScriptBytes` form of this statement lives in
`LnLean.Proofs.Bitcoin.FundingLinkTargets`, which can import the proof module
without creating a cycle. -/
theorem ofKeys_witnessScript_eq_ordered_pair (a b : PubKey) :
    (ofKeys a b).witnessScript.bytes =
      (ByteArray.empty.push 0x52)
        ++ pushData (ofKeys a b).firstFundingKey.bytes
        ++ pushData (ofKeys a b).secondFundingKey.bytes
        ++ (ByteArray.empty.push 0x52)
        ++ (ByteArray.empty.push OP_CHECKMULTISIG) := rfl

end FundingScript

/-- The funding-relevant data negotiated during BOLT 2 channel establishment,
from one endpoint's point of view.  `localFundingKey` is the `funding_pubkey`
offered in `open_channel`; `remoteFundingKey` is the peer's `funding_pubkey`
from `accept_channel`.  The P2WSH program is deliberately **not** a field: it
is derived from the witness script by `toFundingParams`. -/
structure FundingNegotiation where
  /-- BOLT 2 `funding_satoshis` (the L1 output value). -/
  fundingSatoshis : BtcAmount
  /-- BOLT 2 `push_msat` (the funder's initial gift, a split of capacity). -/
  pushMsat : Msat
  /-- This endpoint's funding key (`open_channel`). -/
  localFundingKey : PubKey
  /-- The peer's funding key (`accept_channel.funding_pubkey`). -/
  remoteFundingKey : PubKey
  /-- The temporary channel id used until the funding txid is known. -/
  temporaryChannelId : TemporaryChannelId
  /-- The final channel id, once the funding outpoint is known. -/
  finalChannelId? : Option FinalChannelId := none
deriving Repr

namespace FundingNegotiation

/-- The BOLT 3 witness script determined by the negotiated key pair. -/
def witnessScript (n : FundingNegotiation) : Script :=
  (FundingScript.ofKeys n.localFundingKey n.remoteFundingKey).witnessScript

/-- The ordered key pair actually serialized into the witness script. -/
def firstFundingKey (n : FundingNegotiation) : PubKey :=
  (orderedFundingKeys n.localFundingKey n.remoteFundingKey).1

/-- The second key of the ordered pair actually serialized into the script. -/
def secondFundingKey (n : FundingNegotiation) : PubKey :=
  (orderedFundingKeys n.localFundingKey n.remoteFundingKey).2

theorem witnessScript_eq_ofKeys (n : FundingNegotiation) :
    n.witnessScript =
      (FundingScript.ofKeys n.localFundingKey n.remoteFundingKey).witnessScript :=
  rfl

theorem firstFundingKey_pair (n : FundingNegotiation) :
    orderedFundingKeys n.localFundingKey n.remoteFundingKey =
      (n.firstFundingKey, n.secondFundingKey) := rfl

/-- **The construction of the funding parameters.**  The P2WSH program is
computed as `H (witnessScript.bytes)`; it is not accepted as an argument.
Specializing `H` to `PrimitiveModel.sha256` gives the BOLT 3 SHA-256 rule. -/
def toFundingParams (H : ByteArray → ByteArray) (n : FundingNegotiation) :
    FundingParams :=
  { fundingSatoshis := n.fundingSatoshis
    pushMsat := n.pushMsat
    localFundingKey := n.localFundingKey
    remoteFundingKey := n.remoteFundingKey
    witnessScriptHash := H n.witnessScript.bytes
    temporaryChannelId := n.temporaryChannelId
    finalChannelId? := n.finalChannelId? }

@[simp] theorem toFundingParams_fundingSatoshis (H : ByteArray → ByteArray)
    (n : FundingNegotiation) :
    (n.toFundingParams H).fundingSatoshis = n.fundingSatoshis := rfl

@[simp] theorem toFundingParams_pushMsat (H : ByteArray → ByteArray)
    (n : FundingNegotiation) :
    (n.toFundingParams H).pushMsat = n.pushMsat := rfl

@[simp] theorem toFundingParams_localFundingKey (H : ByteArray → ByteArray)
    (n : FundingNegotiation) :
    (n.toFundingParams H).localFundingKey = n.localFundingKey := rfl

@[simp] theorem toFundingParams_remoteFundingKey (H : ByteArray → ByteArray)
    (n : FundingNegotiation) :
    (n.toFundingParams H).remoteFundingKey = n.remoteFundingKey := rfl

@[simp] theorem toFundingParams_temporaryChannelId (H : ByteArray → ByteArray)
    (n : FundingNegotiation) :
    (n.toFundingParams H).temporaryChannelId = n.temporaryChannelId := rfl

@[simp] theorem toFundingParams_finalChannelId (H : ByteArray → ByteArray)
    (n : FundingNegotiation) :
    (n.toFundingParams H).finalChannelId? = n.finalChannelId? := rfl

/-- The constructed parameters compute exactly the constructor's witness
script.  This is the definitional equality that makes the hash link below
meaningful rather than circular. -/
@[simp] theorem toFundingParams_witnessScript (H : ByteArray → ByteArray)
    (n : FundingNegotiation) :
    (n.toFundingParams H).witnessScript = n.witnessScript := rfl

/-- **The hash link, by construction.**  The stored program of the constructed
parameters is `H` of the witness script bytes. -/
theorem toFundingParams_witnessScriptHash (H : ByteArray → ByteArray)
    (n : FundingNegotiation) :
    (n.toFundingParams H).witnessScriptHash =
      H (n.toFundingParams H).witnessScript.bytes :=
  rfl

/-- The constructed `scriptPubKey` is the P2WSH wrapper over the computed
program. -/
theorem toFundingParams_fundingScriptPubKey (H : ByteArray → ByteArray)
    (n : FundingNegotiation) :
    (n.toFundingParams H).fundingScriptPubKey =
      p2wsh (H (n.toFundingParams H).witnessScript.bytes) :=
  rfl

/-- The computed program is 32 bytes whenever `H` has 32-byte output. -/
theorem toFundingParams_witnessScriptHash_size (H : ByteArray → ByteArray)
    (hH : ∀ b : ByteArray, (H b).size = 32) (n : FundingNegotiation) :
    (n.toFundingParams H).witnessScriptHash.size = 32 := by
  simp [toFundingParams, hH]

/-- The constructed parameters are well formed whenever the negotiated
value/push bounds and the two key widths hold.  This removes `WellFormed` from
the construction boundary: it is derived from fields already present in the
negotiation and the key-validity facts the wire decoder checks. -/
theorem toFundingParams_wellFormed (H : ByteArray → ByteArray)
    (hH : ∀ b : ByteArray, (H b).size = 32) (n : FundingNegotiation)
    (hsat0 : 0 ≤ n.fundingSatoshis)
    (hsatMax : n.fundingSatoshis ≤ Bitcoin.Data.MAX_MONEY)
    (hlocal : n.localFundingKey.Valid)
    (hremote : n.remoteFundingKey.Valid)
    (hpush : (n.pushMsat.val : Int) ≤
      n.fundingSatoshis * (Msat.MSAT_PER_SAT : Int)) :
    (n.toFundingParams H).WellFormed := by
  unfold FundingParams.WellFormed
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hsat0
  · simpa using hsatMax
  · simpa using hlocal
  · simpa using hremote
  · exact toFundingParams_witnessScriptHash_size H hH n
  · simpa using hpush

end FundingNegotiation

/-- Build the L1 funding-output record from the parameters and the funding
txid/output index. -/
def FundingParams.toFundingOutput (p : FundingParams) (txid : ByteArray)
    (index : Nat) : FundingOutput :=
  { outpoint := LnLean.Bitcoin.fundingOutpoint txid index
    value := p.fundingSatoshis
    witnessScriptHash := p.witnessScriptHash }

/-- The funding outpoint is `(txid, index)`.  This is the module-local name
for the seam operation; the fully qualified name is
`LnLean.Bitcoin.Funding.fundingOutpoint`. -/
def Funding.fundingOutpoint (txid : ByteArray) (index : Nat) : OutPoint :=
  LnLean.Bitcoin.fundingOutpoint txid index

theorem Funding.fundingOutpoint_index (txid : ByteArray) (index : Nat) :
    (Funding.fundingOutpoint txid index).n = index.toUInt32 := by
  rfl

theorem Funding.fundingOutpoint_hash (txid : ByteArray) (index : Nat) :
    (Funding.fundingOutpoint txid index).hash = txid := by
  rfl

/-! ## Confirmation predicate -/

/-- The funding output is confirmed by transaction `tx` if `tx.vout[index]`
exists with the expected value and the expected P2WSH script.  This is a
*predicate*: L1 consensus and chain inclusion are out of scope. -/
def FundingConfirmed (p : FundingParams) (tx : Tx) (index : Nat) : Prop :=
  ∃ out : TxOut,
    tx.vout[index]? = some out ∧
    out.value = p.fundingSatoshis ∧
    out.scriptPubKey = p.fundingScriptPubKey

/-- The funding output is *spendable by the 2-of-2* with witness `witness` if
the L1 script interpreter accepts it.  `verify` is a parameter because the
L1 interpreter/signature bridge is not imported during wave A; this names the
missing bridge instead of asserting spendability. -/
def FundingSpendableBy2of2
    (verify : Script → WitnessStack → Tx → Bool)
    (p : FundingParams) (tx : Tx) (witness : WitnessStack) : Prop :=
  verify p.fundingScriptPubKey witness tx = true

/-- A confirmed funding output has exactly the funding value. -/
theorem FundingConfirmed.value_eq {p : FundingParams} {tx : Tx} {index : Nat}
    (h : FundingConfirmed p tx index) :
    ∃ out : TxOut,
      tx.vout[index]? = some out ∧ out.value = p.fundingSatoshis := by
  rcases h with ⟨out, hout, hvalue, _⟩
  exact ⟨out, hout, hvalue⟩

/-- A confirmed funding output has exactly the expected P2WSH script. -/
theorem FundingConfirmed.script_eq {p : FundingParams} {tx : Tx} {index : Nat}
    (h : FundingConfirmed p tx index) :
    ∃ out : TxOut,
      tx.vout[index]? = some out ∧ out.scriptPubKey = p.fundingScriptPubKey := by
  rcases h with ⟨out, hout, _, hscript⟩
  exact ⟨out, hout, hscript⟩

/-- The funding witness script has size 71 when both compressed keys are
33 bytes: 1 (OP_2) + 34 + 34 + 1 (OP_2) + 1 (OP_CHECKMULTISIG). -/
theorem FundingParams.witnessScript_size (p : FundingParams)
    (h1 : p.localFundingKey.bytes.size = 33)
    (h2 : p.remoteFundingKey.bytes.size = 33) :
    p.witnessScript.bytes.size = 71 := by
  simp only [FundingParams.witnessScript, orderedFundingKeys, pushData]
  split <;> simp [h1, h2]

/-- The funding `scriptPubKey` is 34 bytes when its witness-script hash is
32 bytes (BIP 141 P2WSH). -/
theorem FundingParams.fundingScriptPubKey_size (p : FundingParams)
    (h : p.witnessScriptHash.size = 32) :
    p.fundingScriptPubKey.bytes.size = 34 := by
  simpa [FundingParams.fundingScriptPubKey, LnLean.Bitcoin.fundingScriptPubKey]
    using LnLean.Bitcoin.p2wsh_size p.witnessScriptHash h

/-- A well-formed funding value is within Bitcoin `MoneyRange`.  This is the
L1-facing arithmetic fact every channel opener needs. -/
theorem FundingParams.wellFormed_moneyRange (p : FundingParams)
    (h : p.WellFormed) :
    Bitcoin.Data.MoneyRange p.fundingSatoshis = true := by
  rcases h with ⟨hnonneg, hmax, _⟩
  unfold Bitcoin.Data.MoneyRange
  simp [hnonneg, hmax]

/-- For a well-formed channel, the pushed amount does not exceed the channel
value in millisatoshis. -/
theorem FundingParams.wellFormed_push_le (p : FundingParams)
    (h : p.WellFormed) :
    (p.pushMsat.val : Int) ≤ p.fundingSatoshis * (Msat.MSAT_PER_SAT : Int) := by
  rcases h with ⟨_, _, _, _, _, hpush⟩
  exact hpush

end LnLean.Bitcoin
