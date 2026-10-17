import Bitcoin.Data.Basic
import Bitcoin.Data.Script
import Bitcoin.Data.Tx
import LnLean.Basic.Core
import LnLean.Bitcoin.Seam
import LnLean.Bitcoin.Funding
import LnLean.Bitcoin.ScriptTemplates

/-!
# LnLean.Bitcoin.Laws

English claim: the structural laws the channel model relies on are true of the
L1 seam: P2WSH/P2WPKH/P2TR `scriptPubKey`s have the BIP 141/341 sizes; the
anchor value is 330 satoshis; a well-formed funding value lies in Bitcoin
`MoneyRange`; the commitment output tags are injective (so `to_local`,
`to_remote`, HTLC, anchor, and mutual-close outputs are distinguishable by
kind); the zero-HTLC anchor commitment has four outputs; and the funding
outpoint projects its index and txid exactly as the L1 `OutPoint` fields.

Anchors:
* BOLT 3, "Funding Transaction Output" (`refs/bolts/03-transactions.md:75-83`
  at BOLT commit `1aadb719b4007c4cea0ba6e36b08c4fb53788dee`) and the anchor
  value (`:148-168`).
* BOLT 3, "Commitment Transaction Outputs" (`:103-177`) and the construction
  algorithm (`:708-736`).
* `refs/rust-lightning/lightning/src/ln/chan_utils.rs:849-866` (funding
  script), `:687-700`, `:763-835`, `:1009-1041` (commitment/anchor scripts).
* `refs/rust-lightning/lightning/src/ln/channel.rs:989`
  (`ANCHOR_OUTPUT_VALUE_SATOSHI = 330`) and `:348-362`
  (`channel_id`/`funding_txo`).

Not modelled:
* Cryptographic hashing: the P2WSH/`HASH160` programs are arbitrary byte
  strings of the right length; the laws do not say they are hashes of any
  particular witness script.
* L1 script semantics or spendability.
* BIP 69+CLTV ordering, dust trimming, fees, and the no-HTLC anchor-elision
  exception.
-/

namespace LnLean.Bitcoin

set_option autoImplicit false

open Bitcoin.Data

/-! ## BIP 141 / BIP 341 script sizes -/

/-- A P2WSH `scriptPubKey` is 34 bytes. -/
theorem p2wsh_script_size (program : ByteArray) (h : program.size = 32) :
    (p2wsh program).bytes.size = 34 := by
  simpa using LnLean.Bitcoin.p2wsh_size program h

/-- A P2WPKH `scriptPubKey` is 22 bytes. -/
theorem p2wpkh_script_size (program : ByteArray) (h : program.size = 20) :
    (p2wpkh program).bytes.size = 22 := by
  simpa using LnLean.Bitcoin.p2wpkh_size program h

/-- A P2TR `scriptPubKey` is 34 bytes. -/
theorem p2tr_script_size (program : ByteArray) (h : program.size = 32) :
    (p2tr program).bytes.size = 34 := by
  simpa using LnLean.Bitcoin.p2tr_size program h

/-- The commitment helper `toLocalScriptPubKey` is a P2WSH output. -/
theorem toLocalScriptPubKey_size (h : ByteArray) (hh : h.size = 32) :
    (toLocalScriptPubKey h).bytes.size = 34 := by
  simpa [toLocalScriptPubKey] using p2wsh_script_size h hh

/-- The anchored `to_remote` helper is a P2WSH output. -/
theorem toRemoteScriptPubKey_size (h : ByteArray) (hh : h.size = 32) :
    (toRemoteScriptPubKey h).bytes.size = 34 := by
  simpa [toRemoteScriptPubKey] using p2wsh_script_size h hh

/-- A keyed anchor output is a P2WSH output. -/
theorem anchorScriptPubKey_size (h : ByteArray) (hh : h.size = 32) :
    (anchorScriptPubKey h).bytes.size = 34 := by
  simpa [anchorScriptPubKey] using p2wsh_script_size h hh

/-! ## Anchor value -/

/-- BOLT 3 fixes the keyed anchor output at 330 satoshis. -/
theorem anchorValue_eq_330 : anchorValue = 330 := by
  rfl

/-- 330 satoshis is inside Bitcoin's `MoneyRange`. -/
theorem anchorValue_moneyRange : Bitcoin.Data.MoneyRange anchorValue = true := by
  unfold anchorValue
  decide

/-! ## Funding value and outpoint laws -/

/-- A well-formed funding value is in `MoneyRange`. -/
theorem funding_value_moneyRange (p : FundingParams) (h : p.WellFormed) :
    Bitcoin.Data.MoneyRange p.fundingSatoshis = true :=
  FundingParams.wellFormed_moneyRange p h

/-- The funding outpoint's output index is exactly the supplied index. -/
theorem fundingOutpoint_index_projection (txid : ByteArray) (index : Nat) :
    (Funding.fundingOutpoint txid index).n = index.toUInt32 := by
  rfl

/-- The funding outpoint's txid is exactly the supplied txid. -/
theorem fundingOutpoint_hash_projection (txid : ByteArray) (index : Nat) :
    (Funding.fundingOutpoint txid index).hash = txid := by
  rfl

/-- `Sorted` is not needed; the final channel id built from an outpoint
matches that outpoint by construction. -/
theorem finalChannelId_matches_fundingOutpoint (txid : ByteArray) (index : Nat) :
    (FinalChannelId.fromFundingOutpoint
      (Funding.fundingOutpoint txid index)).id.bytes = txid := by
  rfl

/-! ## Output-kind discrimination -/

/-- Output-kind tags are injective: different output kinds cannot collide. -/
theorem outputKind_tag_injective : Function.Injective OutputKind.tag := by
  intro a b h
  cases a <;> cases b <;> simp [OutputKind.tag] at h ⊢

/-- The `to_local` and `to_remote` constructors are distinct. -/
theorem outputKind_toLocal_ne_toRemote :
    OutputKind.toLocal ≠ OutputKind.toRemote := by
  decide

/-- The two anchor constructors are distinct. -/
theorem outputKind_localAnchor_ne_remoteAnchor :
    OutputKind.localAnchor ≠ OutputKind.remoteAnchor := by
  decide

/-- The mutual-close constructor is distinct from `to_local`. -/
theorem outputKind_mutualClose_ne_toLocal :
    OutputKind.mutualClose ≠ OutputKind.toLocal := by
  decide

/-! ## Commitment output-list laws -/

/-- The zero-HTLC anchor commitment has four outputs. -/
theorem commitmentOutputs_length_law (p : CommitmentParams) :
    (commitmentOutputs p).length = 4 :=
  commitmentOutputs_length p

/-- The output kinds of the zero-HTLC anchor commitment are exactly the four
modelled kinds, in template order. -/
theorem commitmentOutputs_kinds_law (p : CommitmentParams) :
    (commitmentOutputs p).map CommitmentOutput.kind =
      [.toLocal, .toRemote, .localAnchor, .remoteAnchor] :=
  commitmentOutputs_kinds p

end LnLean.Bitcoin
