import Bitcoin.Data.Basic
import Bitcoin.Data.Script
import Bitcoin.Data.Tx
import LnLean.Basic.Core
import LnLean.Bitcoin.Seam

/-!
# LnLean.Bitcoin.ScriptTemplates

English claim: the BOLT 3 commitment transaction output scripts are built from
the standard templates below.  `to_local` is the version-0 P2WSH whose witness
script has a revocation branch and a CSV-delayed local-payment branch;
`to_remote` is either P2WPKH (no anchors) or the one-block-CSV P2WSH witness
script (anchors); offered and received HTLC outputs are P2WSH witness scripts
containing the payment hash, the counterparty HTLC key, and (for received
HTLCs) the CLTV expiry; each party has a 330-sat keyed anchor output; and the
mutual-close output pays an arbitrary `shutdown` script.  `commitmentOutputs`
returns the four outputs of an anchors commitment with zero HTLCs and both
commitment outputs present.

Anchors:
* BOLT 3, "Funding Transaction Output" (`refs/bolts/03-transactions.md:75-83`
  at BOLT commit `1aadb719b4007c4cea0ba6e36b08c4fb53788dee`).
* BOLT 3, "`to_local` Output" (`:113-135`), "`to_remote` Output"
  (`:136-147`), "`to_local_anchor` and `to_remote_anchor` Output"
  (`:148-177`), "Offered HTLC Outputs" (`:201-251`), "Received HTLC Outputs"
  (`:253-300`).
* BOLT 3, "Legacy Closing Transaction" / "Closing Transaction" (`:386-410`).
* `refs/rust-lightning/lightning/src/ln/chan_utils.rs:687-700`
  (`get_revokeable_redeemscript`), `:706-713`
  (`get_countersigner_payment_script`), `:763-835`
  (`get_htlc_redeemscript_with_explicit_keys`), `:1009-1041`
  (`get_to_countersigner_keyed_anchor_redeemscript`,
  `get_keyed_anchor_redeemscript`), `:353` (`build_closing_transaction`).
* `refs/rust-lightning/lightning/src/ln/channel.rs:989`
  (`ANCHOR_OUTPUT_VALUE_SATOSHI = 330`).

Not modelled:
* SHA256 / RIPEMD160.  Script builders take the relevant 20-byte or 32-byte
  hash as a parameter; `CommitmentParams.HashesMatch` names the missing hash
  bridge but is not proved.
* Minimal script-number encoding for CSV/CLTV.  This scaffold encodes
  `to_self_delay` as a fixed 2-byte little-endian push and `cltv_expiry` as a
  fixed 4-byte little-endian push.  Hence the byte sizes of the HTLC scripts
  are not claimed to be bit-exact with BOLT 3's minimal encoding.
* BIP 69+CLTV output ordering, dust trimming, and fee deduction.  The output
  list is in template order, not transaction order.
* Script execution, signature checking, and spendability.
* The no-anchor `to_remote` P2WPKH variant is represented separately; the
  commitment-output list uses the anchor variant.
-/

namespace LnLean.Bitcoin

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Bitcoin.Data

/-! ## Opcodes not already exported by the seam -/

def OP_CHECKSIGVERIFY : UInt8 := 0xad
def OP_SWAP : UInt8 := 0x7c
def OP_SIZE : UInt8 := 0x82
def OP_IFDUP : UInt8 := 0x73
def OP_1 : UInt8 := 0x51
def OP_2 : UInt8 := 0x52
def OP_16 : UInt8 := 0x60

/-! ## Fixed-width little-endian script-number pushes -/

/-- Two-byte little-endian encoding of a relative timelock. -/
def pushUInt16LE (n : Nat) : ByteArray :=
  (ByteArray.empty.push n.toUInt8).push (n >>> 8).toUInt8

/-- Four-byte little-endian encoding of an absolute timelock. -/
def pushUInt32LE (n : Nat) : ByteArray :=
  (((ByteArray.empty.push n.toUInt8).push (n >>> 8).toUInt8).push
    (n >>> 16).toUInt8).push (n >>> 24).toUInt8

/-- `pushData` of a two-byte script number. -/
def pushScriptNum16 (n : Nat) : ByteArray := pushData (pushUInt16LE n)

/-- `pushData` of a four-byte script number. -/
def pushScriptNum32 (n : Nat) : ByteArray := pushData (pushUInt32LE n)

/-! ## Commitment output kinds -/

/-- The output kinds represented in this module.  The tags are a stable
structural discriminator used by the laws module; they are not wire values. -/
inductive OutputKind where
  | toLocal
  | toRemote
  | offeredHtlc
  | receivedHtlc
  | localAnchor
  | remoteAnchor
  | mutualClose
deriving Repr, DecidableEq, BEq

namespace OutputKind

/-- Stable structural tag for each output kind. -/
def tag : OutputKind → Nat
  | toLocal => 0
  | toRemote => 1
  | offeredHtlc => 2
  | receivedHtlc => 3
  | localAnchor => 4
  | remoteAnchor => 5
  | mutualClose => 6

end OutputKind

/-- A commitment (or closing) output: kind, satoshi value, and the L1
`scriptPubKey` produced by one of the templates below. -/
structure CommitmentOutput where
  kind : OutputKind
  value : BtcAmount
  scriptPubKey : Script
deriving Repr

/-! ## `to_local` (BOLT 3) -/

/-- `to_local` witness script:
`OP_IF <revocationpubkey> OP_ELSE <to_self_delay> OP_CSV OP_DROP
<local_delayedpubkey> OP_ENDIF OP_CHECKSIG`. -/
def toLocalWitnessScript (revocationKey delayedPaymentKey : PubKey)
    (toSelfDelay : Blocks) : Script :=
  ⟨(ByteArray.empty.push OP_IF)
     ++ pushData revocationKey.bytes
     ++ (ByteArray.empty.push OP_ELSE)
     ++ pushScriptNum16 toSelfDelay
     ++ (ByteArray.empty.push OP_CSV)
     ++ (ByteArray.empty.push OP_DROP)
     ++ pushData delayedPaymentKey.bytes
     ++ (ByteArray.empty.push OP_ENDIF)
     ++ (ByteArray.empty.push OP_CHECKSIG)⟩

/-- `to_local` output script: P2WSH over the `to_local` witness script. -/
def toLocalScriptPubKey (witnessScriptHash : ByteArray) : Script :=
  p2wsh witnessScriptHash

/-! ## `to_remote` (BOLT 3) -/

/-- `to_remote` witness script when anchors are negotiated:
`<remotepubkey> OP_CHECKSIGVERIFY OP_1 OP_CSV`. -/
def toRemoteWitnessScript (remotePaymentKey : PubKey) : Script :=
  ⟨pushData remotePaymentKey.bytes
     ++ (ByteArray.empty.push OP_CHECKSIGVERIFY)
     ++ (ByteArray.empty.push OP_1)
     ++ (ByteArray.empty.push OP_CSV)⟩

/-- `to_remote` output script with anchors: P2WSH over the one-block-CSV
witness script. -/
def toRemoteScriptPubKey (witnessScriptHash : ByteArray) : Script :=
  p2wsh witnessScriptHash

/-- `to_remote` output script without anchors: P2WPKH to the remote payment
key's HASH160 (BOLT 3 `:144-147`). -/
def toRemoteP2WPKHScriptPubKey (paymentKeyHash160 : ByteArray) : Script :=
  p2wpkh paymentKeyHash160

/-! ## Offered and received HTLC outputs (BOLT 3, anchor variant) -/

/-- Offered HTLC witness script, with the anchor (one-block CSV) branch.
The CLTV expiry is *not* in this output script; it is the locktime of the
HTLC-timeout transaction. -/
def offeredHtlcWitnessScript (revocationKeyHash160 paymentHash160 : ByteArray)
    (remoteHtlcKey localHtlcKey : PubKey) : Script :=
  ⟨(ByteArray.empty.push OP_DUP)
     ++ (ByteArray.empty.push OP_HASH160)
     ++ pushData revocationKeyHash160
     ++ (ByteArray.empty.push OP_EQUAL)
     ++ (ByteArray.empty.push OP_IF)
     ++ (ByteArray.empty.push OP_CHECKSIG)
     ++ (ByteArray.empty.push OP_ELSE)
     ++ pushData remoteHtlcKey.bytes
     ++ (ByteArray.empty.push OP_SWAP)
     ++ (ByteArray.empty.push OP_SIZE)
     ++ pushData (ByteArray.empty.push 32)
     ++ (ByteArray.empty.push OP_EQUAL)
     ++ (ByteArray.empty.push OP_NOTIF)
     ++ (ByteArray.empty.push OP_DROP)
     ++ (ByteArray.empty.push OP_2)
     ++ (ByteArray.empty.push OP_SWAP)
     ++ pushData localHtlcKey.bytes
     ++ (ByteArray.empty.push OP_2)
     ++ (ByteArray.empty.push OP_CHECKMULTISIG)
     ++ (ByteArray.empty.push OP_ELSE)
     ++ (ByteArray.empty.push OP_HASH160)
     ++ pushData paymentHash160
     ++ (ByteArray.empty.push OP_EQUALVERIFY)
     ++ (ByteArray.empty.push OP_CHECKSIG)
     ++ (ByteArray.empty.push OP_ENDIF)
     ++ (ByteArray.empty.push OP_1)
     ++ (ByteArray.empty.push OP_CSV)
     ++ (ByteArray.empty.push OP_DROP)
     ++ (ByteArray.empty.push OP_ENDIF)⟩

/-- Offered HTLC output script: P2WSH over the offered HTLC witness script. -/
def offeredHtlcScriptPubKey (witnessScriptHash : ByteArray) : Script :=
  p2wsh witnessScriptHash

/-- Received HTLC witness script, with the anchor (one-block CSV) branch.
This script contains the CLTV expiry in its timeout branch. -/
def receivedHtlcWitnessScript (revocationKeyHash160 paymentHash160 : ByteArray)
    (remoteHtlcKey localHtlcKey : PubKey) (cltvExpiry : Height) : Script :=
  ⟨(ByteArray.empty.push OP_DUP)
     ++ (ByteArray.empty.push OP_HASH160)
     ++ pushData revocationKeyHash160
     ++ (ByteArray.empty.push OP_EQUAL)
     ++ (ByteArray.empty.push OP_IF)
     ++ (ByteArray.empty.push OP_CHECKSIG)
     ++ (ByteArray.empty.push OP_ELSE)
     ++ pushData remoteHtlcKey.bytes
     ++ (ByteArray.empty.push OP_SWAP)
     ++ (ByteArray.empty.push OP_SIZE)
     ++ pushData (ByteArray.empty.push 32)
     ++ (ByteArray.empty.push OP_EQUAL)
     ++ (ByteArray.empty.push OP_IF)
     ++ (ByteArray.empty.push OP_HASH160)
     ++ pushData paymentHash160
     ++ (ByteArray.empty.push OP_EQUALVERIFY)
     ++ (ByteArray.empty.push OP_2)
     ++ (ByteArray.empty.push OP_SWAP)
     ++ pushData localHtlcKey.bytes
     ++ (ByteArray.empty.push OP_2)
     ++ (ByteArray.empty.push OP_CHECKMULTISIG)
     ++ (ByteArray.empty.push OP_ELSE)
     ++ (ByteArray.empty.push OP_DROP)
     ++ pushScriptNum32 cltvExpiry
     ++ (ByteArray.empty.push OP_CLTV)
     ++ (ByteArray.empty.push OP_DROP)
     ++ (ByteArray.empty.push OP_CHECKSIG)
     ++ (ByteArray.empty.push OP_ENDIF)
     ++ (ByteArray.empty.push OP_1)
     ++ (ByteArray.empty.push OP_CSV)
     ++ (ByteArray.empty.push OP_DROP)
     ++ (ByteArray.empty.push OP_ENDIF)⟩

/-- Received HTLC output script: P2WSH over the received HTLC witness
script. -/
def receivedHtlcScriptPubKey (witnessScriptHash : ByteArray) : Script :=
  p2wsh witnessScriptHash

/-! ## Keyed anchor outputs (BOLT 3, 330 sat) -/

/-- Keyed anchor witness script:
`<funding_pubkey> OP_CHECKSIG OP_IFDUP OP_NOTIF OP_16 OP_CSV OP_ENDIF`. -/
def anchorWitnessScript (fundingKey : PubKey) : Script :=
  ⟨pushData fundingKey.bytes
     ++ (ByteArray.empty.push OP_CHECKSIG)
     ++ (ByteArray.empty.push OP_IFDUP)
     ++ (ByteArray.empty.push OP_NOTIF)
     ++ (ByteArray.empty.push OP_16)
     ++ (ByteArray.empty.push OP_CSV)
     ++ (ByteArray.empty.push OP_ENDIF)⟩

/-- Keyed anchor output script: P2WSH over the anchor witness script. -/
def anchorScriptPubKey (witnessScriptHash : ByteArray) : Script :=
  p2wsh witnessScriptHash

/-! ## Mutual close output (BOLT 3 closing transaction) -/

/-- A mutual-close output pays the script given in the peer's `shutdown`
message.  BOLT 3 deliberately does not prescribe a script template here. -/
structure MutualCloseOutput where
  value : BtcAmount
  shutdownScriptPubKey : Script
deriving Repr

/-- Build a mutual-close output. -/
def mutualCloseOutput (value : BtcAmount) (shutdownScriptPubKey : Script) :
    MutualCloseOutput :=
  ⟨value, shutdownScriptPubKey⟩

/-- Convert the mutual-close output to an L1 `TxOut`. -/
def MutualCloseOutput.toTxOut (m : MutualCloseOutput) : TxOut :=
  ⟨m.value, m.shutdownScriptPubKey⟩

/-! ## Commitment parameters and the zero-HTLC output list -/

/-- Parameters needed to build the four anchor-commitment outputs with no
HTLCs.  The four `...Hash` fields are `SHA256` of the corresponding witness
script; `HashesMatch` is the missing bridge to the crypto model. -/
structure CommitmentParams where
  revocationKey : PubKey
  delayedPaymentKey : PubKey
  remotePaymentKey : PubKey
  localFundingKey : PubKey
  remoteFundingKey : PubKey
  toSelfDelay : Blocks
  toLocalValue : BtcAmount
  toRemoteValue : BtcAmount
  toLocalWitnessScriptHash : ByteArray
  toRemoteWitnessScriptHash : ByteArray
  localAnchorWitnessScriptHash : ByteArray
  remoteAnchorWitnessScriptHash : ByteArray
deriving Repr

/-- The hash fields really are SHA256 of the computed witness scripts.  This
is stated as a `Prop` because no SHA256 implementation is imported during
wave A; it names the missing crypto bridge rather than assuming it. -/
def CommitmentParams.HashesMatch (p : CommitmentParams)
    (sha256 : Script → ByteArray) : Prop :=
  p.toLocalWitnessScriptHash =
      sha256 (toLocalWitnessScript p.revocationKey p.delayedPaymentKey p.toSelfDelay) ∧
  p.toRemoteWitnessScriptHash =
      sha256 (toRemoteWitnessScript p.remotePaymentKey) ∧
  p.localAnchorWitnessScriptHash =
      sha256 (anchorWitnessScript p.localFundingKey) ∧
  p.remoteAnchorWitnessScriptHash =
      sha256 (anchorWitnessScript p.remoteFundingKey)

/-- The four outputs of an anchors commitment with zero HTLCs and both
commitment outputs present: `to_local`, `to_remote`, `to_local_anchor`, and
`to_remote_anchor`.  Ordering is template order; BIP 69+CLTV sorting is not
modelled. -/
def commitmentOutputs (p : CommitmentParams) : List CommitmentOutput :=
  [ { kind := .toLocal
      value := p.toLocalValue
      scriptPubKey := toLocalScriptPubKey p.toLocalWitnessScriptHash },
    { kind := .toRemote
      value := p.toRemoteValue
      scriptPubKey := toRemoteScriptPubKey p.toRemoteWitnessScriptHash },
    { kind := .localAnchor
      value := anchorValue
      scriptPubKey := anchorScriptPubKey p.localAnchorWitnessScriptHash },
    { kind := .remoteAnchor
      value := anchorValue
      scriptPubKey := anchorScriptPubKey p.remoteAnchorWitnessScriptHash } ]

/-! ## Structural size lemmas -/

/-- `to_local` witness script is 77 bytes for two 33-byte keys and a 2-byte
CSV push: 1 + 34 + 1 + 3 + 1 + 1 + 34 + 1 + 1. -/
theorem toLocalWitnessScript_size (revocationKey delayedPaymentKey : PubKey)
    (toSelfDelay : Blocks)
    (h1 : revocationKey.bytes.size = 33)
    (h2 : delayedPaymentKey.bytes.size = 33) :
    (toLocalWitnessScript revocationKey delayedPaymentKey toSelfDelay).bytes.size = 77 := by
  simp [toLocalWitnessScript, pushScriptNum16, pushUInt16LE, pushData, h1, h2]

/-- `to_remote` anchor witness script is 37 bytes: 34 + 1 + 1 + 1. -/
theorem toRemoteWitnessScript_size (remotePaymentKey : PubKey)
    (h : remotePaymentKey.bytes.size = 33) :
    (toRemoteWitnessScript remotePaymentKey).bytes.size = 37 := by
  simp [toRemoteWitnessScript, pushData, h]

/-- Anchor witness script is 40 bytes: 34 + 6 opcodes. -/
theorem anchorWitnessScript_size (fundingKey : PubKey)
    (h : fundingKey.bytes.size = 33) :
    (anchorWitnessScript fundingKey).bytes.size = 40 := by
  simp [anchorWitnessScript, pushData, h]

/-- The zero-HTLC anchor commitment has exactly four outputs. -/
theorem commitmentOutputs_length (p : CommitmentParams) :
    (commitmentOutputs p).length = 4 := by
  rfl

/-- The output kinds of the zero-HTLC anchor commitment, in template order. -/
theorem commitmentOutputs_kinds (p : CommitmentParams) :
    (commitmentOutputs p).map CommitmentOutput.kind =
      [.toLocal, .toRemote, .localAnchor, .remoteAnchor] := by
  rfl

/-- A mutual-close output carries the value supplied by the closing logic. -/
theorem mutualCloseOutput_value (value : BtcAmount) (script : Script) :
    (mutualCloseOutput value script).value = value := by
  rfl

end LnLean.Bitcoin
