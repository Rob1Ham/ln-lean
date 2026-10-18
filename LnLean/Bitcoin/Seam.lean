import Bitcoin.Data.Basic
import Bitcoin.Data.Script
import Bitcoin.Data.Tx
import LnLean.Basic.Core

/-!
# LnLean.Bitcoin.Seam

The bridge between the Lightning model and the existing `btc-lean` L1 model.

Rules:
* Never redefine a Bitcoin primitive here.  `Tx`, `TxOut`, `OutPoint`,
  `Script`, `Amount`, and `MoneyRange` are aliases into `Bitcoin.Data.*`.
* This file contains only the *Lightning-specific* uses of L1: funding
  output construction, commitment output scripts, anchor outputs, and the
  fee/weight constants from BOLT 3.
* Cryptographic functions that btc-lean exposes as interfaces (txid,
  sha256, signature verification) stay opaque here; the crypto workstream
  supplies their specs in `LnLean.Crypto.*`.

Anchors:
* BOLT 3 (commitment transactions), BOLT 5 (recommended fees).
* `rust-lightning/lightning/src/chain/chaininterface.rs` (fee estimator),
  `rust-lightning/lightning/src/ln/chan_utils.rs` (commitment scripts).
-/

namespace LnLean.Bitcoin

set_option autoImplicit false

open Bitcoin.Data

/-! ## Aliases into the L1 model -/

abbrev BtcAmount := Bitcoin.Data.Amount
abbrev OutPoint := Bitcoin.Data.OutPoint
abbrev TxIn := Bitcoin.Data.TxIn
abbrev TxOut := Bitcoin.Data.TxOut
abbrev Tx := Bitcoin.Data.Tx
abbrev Script := Bitcoin.Data.Script
abbrev WitnessStack := Bitcoin.Data.WitnessStack

/-- `MoneyRange` from Bitcoin consensus, re-exported so Lightning proofs can
use the same predicate as L1. -/
def moneyRange (a : BtcAmount) : Bool := Bitcoin.Data.MoneyRange a

/-- Funding outpoint: the L1 txid plus the output index. -/
def fundingOutpoint (txid : ByteArray) (index : Nat) : OutPoint :=
  ⟨txid, index.toUInt32⟩

theorem fundingOutpoint_index (txid : ByteArray) (index : Nat) :
    (fundingOutpoint txid index).n = index.toUInt32 := rfl

/-! ## Script building blocks (BOLT 3) -/

def OP_0 : UInt8 := 0x00
def OP_DUP : UInt8 := 0x76
def OP_HASH160 : UInt8 := 0xa9
def OP_EQUAL : UInt8 := 0x87
def OP_EQUALVERIFY : UInt8 := 0x88
def OP_CHECKSIG : UInt8 := 0xac
def OP_CHECKMULTISIG : UInt8 := 0xae
def OP_IF : UInt8 := 0x63
def OP_NOTIF : UInt8 := 0x64
def OP_ELSE : UInt8 := 0x67
def OP_ENDIF : UInt8 := 0x68
def OP_DROP : UInt8 := 0x75
def OP_CLTV : UInt8 := 0xb1
def OP_CSV : UInt8 := 0xb2

/-- Minimal push of a byte string.  Only the lengths used by Lightning
(20, 32, 33 bytes) are modelled; longer pushes are left to the L1 script
parser. -/
def pushData (b : ByteArray) : ByteArray :=
  (ByteArray.empty.push b.size.toUInt8) ++ b

/-- `OP_0 <32-byte-witness-program>` (BIP 141 P2WSH). -/
def p2wsh (program : ByteArray) : Script :=
  ⟨(ByteArray.empty.push OP_0).push 0x20 ++ program⟩

/-- `OP_0 <20-byte-hash>` (BIP 141 P2WPKH). -/
def p2wpkh (program : ByteArray) : Script :=
  ⟨(ByteArray.empty.push OP_0).push 0x14 ++ program⟩

/-- `OP_1 <32-byte-x-only-key>` (BIP 341 P2TR). -/
def p2tr (program : ByteArray) : Script :=
  ⟨(ByteArray.empty.push 0x51).push 0x20 ++ program⟩

theorem p2wsh_size (program : ByteArray) (h : program.size = 32) :
    (p2wsh program).bytes.size = 34 := by
  simp [p2wsh, h]

theorem p2wpkh_size (program : ByteArray) (h : program.size = 20) :
    (p2wpkh program).bytes.size = 22 := by
  simp [p2wpkh, h]

theorem p2tr_size (program : ByteArray) (h : program.size = 32) :
    (p2tr program).bytes.size = 34 := by
  simp [p2tr, h]

/-! ## Funding output (BOLT 2) -/

/-- The 2-of-2 funding script is P2WSH over the multisig witness script.
The caller supplies the witness-script hash; this layer deliberately does
not compute SHA256 (that is `LnLean.Crypto.Hash`). -/
def fundingScriptPubKey (witnessScriptHash : ByteArray) : Script :=
  p2wsh witnessScriptHash

/-- Value of the funding output, in satoshis. -/
structure FundingOutput where
  outpoint : OutPoint
  value : BtcAmount
  witnessScriptHash : ByteArray
deriving Repr

def FundingOutput.scriptPubKey (f : FundingOutput) : Script :=
  fundingScriptPubKey f.witnessScriptHash

theorem fundingOutput_moneyRange (f : FundingOutput) (h : moneyRange f.value = true) :
    Bitcoin.Data.MoneyRange f.value = true := h

/-! ## Commitment transaction outputs (BOLT 3) -/

/-- BOLT 3 anchor output value: 330 satoshis. -/
def anchorValue : BtcAmount := 330

theorem anchorValue_eq : anchorValue = 330 := rfl

/-- `to_local` output: `OP_CSV <csv> OP_DROP <revocation_pubkey> OP_CHECKSIG`.

This is the *flat one-branch seam fragment* retained for existing consumers
(`CommitmentBridge`, `D03`, ...).  It is **not** the BOLT 3 `to_local` witness
script: it has no `OP_IF`/`OP_ELSE` structure, no delayed-payment key, and it
encodes the delay as a single byte.  Use `toLocalScriptFull` for the faithful
two-branch model. -/
def toLocalScript (revocationPubKey : PubKey) (csv : Blocks) : Script :=
  ⟨pushData (ByteArray.mk #[csv.toUInt8])
     ++ (ByteArray.empty.push OP_CSV).push OP_DROP
     ++ pushData revocationPubKey.bytes
     ++ ByteArray.empty.push OP_CHECKSIG⟩

/-- Fixed-width two-byte little-endian push of the `to_local`
`to_self_delay`: `[0x02, d % 256, (d / 256) % 256]`.

BOLT 3 uses minimal `CScriptNum`; this model deliberately follows the
scaffold's fixed-width encoding (the same encoding as
`ScriptTemplates.pushScriptNum16`).  The value represented is exact for every
`d < 2^16`, which covers BOLT 2's `u16` `to_self_delay` field. -/
def toLocalDelayPush (csv : Blocks) : ByteArray :=
  pushData ((ByteArray.empty.push csv.toUInt8).push (csv >>> 8).toUInt8)

theorem toLocalDelayPush_size (csv : Blocks) :
    (toLocalDelayPush csv).size = 3 := by
  unfold toLocalDelayPush pushData
  simp

/-- The faithful BOLT 3 `to_local` witness script:

`OP_IF <revocationpubkey> OP_ELSE <to_self_delay> OP_CSV OP_DROP
 <local_delayedpubkey> OP_ENDIF OP_CHECKSIG`

The `OP_IF` branch is the revocation (penalty) path; the `OP_ELSE` branch is
the CSV-delayed local-payment path.  This is the witness script whose SHA-256
is the 32-byte P2WSH program of the `to_local` output. -/
def toLocalScriptFull (revocationPubKey delayedPaymentPubKey : PubKey)
    (csv : Blocks) : Script :=
  ⟨(ByteArray.empty.push OP_IF)
     ++ pushData revocationPubKey.bytes
     ++ (ByteArray.empty.push OP_ELSE)
     ++ toLocalDelayPush csv
     ++ (ByteArray.empty.push OP_CSV)
     ++ (ByteArray.empty.push OP_DROP)
     ++ pushData delayedPaymentPubKey.bytes
     ++ (ByteArray.empty.push OP_ENDIF)
     ++ (ByteArray.empty.push OP_CHECKSIG)⟩

/-- The full `to_local` witness script is 77 bytes for two 33-byte compressed
keys and the fixed three-byte delay push. -/
theorem toLocalScriptFull_size (revocationKey delayedPaymentKey : PubKey)
    (toSelfDelay : Blocks)
    (h1 : revocationKey.bytes.size = 33)
    (h2 : delayedPaymentKey.bytes.size = 33) :
    (toLocalScriptFull revocationKey delayedPaymentKey toSelfDelay).bytes.size = 77 := by
  simp [toLocalScriptFull, toLocalDelayPush, pushData, h1, h2]

/-- `to_remote` output: a plain P2WPKH to the remote party's payment key
(the BOLT 3 `to_remote` script is `<remotepubkey> OP_CHECKSIG`; both forms
occur depending on `option_anchor_outputs`; the scaffold models the
P2WPKH variant used by `rust-lightning` when anchors are negotiated). -/
def toRemoteScript (remotePaymentHash160 : ByteArray) : Script :=
  p2wpkh remotePaymentHash160

/-- HTLC-timeout / HTLC-success output script.  The full BOLT 3 script has
an `OP_IF` branch for the offerer and an `OP_ELSE` branch for the
recipient; the scaffold exposes the two branches separately so each can be
proved about without unfolding a large byte template. -/
def htlcBranchScript (paymentHash : PaymentHash) (cltv : Height)
    (counterpartyKey : PubKey) : Script :=
  ⟨(ByteArray.empty.push OP_IF)
     ++ (ByteArray.empty.push OP_HASH160).push 0x14  -- model-level marker
     ++ pushData paymentHash.bytes
     ++ (ByteArray.empty.push OP_EQUALVERIFY)
     ++ pushData (ByteArray.mk #[cltv.toUInt8])
     ++ (ByteArray.empty.push OP_CLTV).push OP_DROP
     ++ pushData counterpartyKey.bytes
     ++ (ByteArray.empty.push OP_CHECKSIG)
     ++ (ByteArray.empty.push OP_ELSE)
     ++ (ByteArray.empty.push OP_ENDIF)⟩

theorem htlcBranch_nonempty (ph : PaymentHash) (cltv : Height) (pk : PubKey) :
    (htlcBranchScript ph cltv pk).bytes.size > 0 := by
  simp [htlcBranchScript]

/-! ## Commitment weight constants (BOLT 3) -/

/-- Base commitment transaction weight before HTLCs for the non-anchor
variant (`BOLT 3`: 724; the anchor variant is 1124).  `Channel.Commitment`
carries the boolean variant explicitly. -/
def commitmentBaseWeight : Weight := ⟨724⟩

/-- Weight added per offered HTLC (`172`). -/
def htlcOfferedWeight : Weight := ⟨172⟩

/-- Weight added per received HTLC (`172`). -/
def htlcReceivedWeight : Weight := ⟨172⟩

theorem commitmentBaseWeight_pos : commitmentBaseWeight.val > 0 := by
  decide

end LnLean.Bitcoin
