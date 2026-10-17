import LnLean.Bitcoin.ScriptTemplates
import LnLean.Bitcoin.Seam

/-!
# LnLean.Proofs.Bitcoin.ScriptProps

English claim.  The BOLT 3 commitment-transaction output templates of
`LnLean.Bitcoin.ScriptTemplates` have the structural properties the protocol
relies on:

* `to_local` is the P2WSH witness script
  `OP_IF <revocationpubkey> OP_ELSE <to_self_delay> OP_CSV OP_DROP
  <local_delayedpubkey> OP_ENDIF OP_CHECKSIG`; it contains both keys and the
  CSV delay, and its byte length is fixed by the template (77 bytes for
  33-byte compressed keys under the scaffold's fixed-width delay push);
* `to_remote` is either the anchor variant
  `<remotepubkey> OP_CHECKSIGVERIFY OP_1 OP_CSV` (37 bytes, containing the
  remote payment key) or a P2WPKH to a 20-byte `HASH160` digest (22 bytes);
* the offered and received HTLC witness scripts contain the 20-byte
  payment-hash digest, both HTLC counterpary keys, and the revocation-key
  hash; the received script additionally contains the CLTV branch
  `<cltv_expiry> OP_CLTV OP_DROP`.  For 20-byte digests and 33-byte keys the
  offered script is 136 bytes and the received script is 143 bytes, so the
  two templates are distinguishable by length;
* the keyed anchor witness script contains the funding key and the 16-block
  CSV fallback; the two anchor outputs in `commitmentOutputs` both carry the
  BOLT 3 anchor value 330 sat;
* `commitmentOutputs` is a total, deterministic function; under the
  well-formedness predicate `ParamsWellFormed` (33-byte keys, 32-byte
  witness-script hashes) all four output scripts are 34-byte P2WSH
  programs;
* malformed key or hash lengths are rejected by `PubKey.Valid`,
  `PaymentHash.Valid`, and `ParamsWellFormed`;
* the commitment-number obscuring factor extracted from the last six bytes
  of a 32-byte digest is below `2^48`, so the XOR-obscured commitment
  number is below `2^48`, and the BOLT 3 locktime/sequence words have high
  bytes `0x20` / `0x80` with the appropriate low 24 bits.

BOLT sections (pinned at `refs/bolts` commit
`1aadb719b4007c4cea0ba6e36b08c4fb53788dee`): BOLT 3 "Commitment
Transaction Outputs", "`to_local` Output" (`03-transactions.md:113-135`),
"`to_remote` Output" (`:136-147`), "`to_local_anchor` and
`to_remote_anchor` Output" (`:148-177`), "Offered HTLC Outputs"
(`:201-251`), "Received HTLC Outputs" (`:253-300`), and "Commitment
Transaction" (`:90-112`).

`rust-lightning` anchors at pinned commit
`fe4900930c6bd5786ec4203274d7cf312776a5a6`:
`lightning/src/ln/chan_utils.rs:687` (`get_revokeable_redeemscript`),
`:704` (`get_countersigner_payment_script`), `:763`
(`get_htlc_redeemscript_with_explicit_keys`), `:1009`
(`get_to_countersigner_keyed_anchor_redeemscript`), `:1032`
(`get_keyed_anchor_redeemscript`), `:2014` and `:2244`
(`get_commitment_transaction_number_obscure_factor` and its use in
`build_inputs`), `lightning/src/ln/channel.rs:989`
(`ANCHOR_OUTPUT_VALUE_SATOSHI = 330`), and `lightning/src/ln/channel.rs:6270`
(`build_commitment_transaction`).

What is explicitly NOT modelled.

* SHA-256 and RIPEMD160 are not computed.  The script builders take the
  20-byte HTLC/revocation digests and the 32-byte witness-script hashes as
  parameters.  `CommitmentParams.HashesMatch` names the missing bridge to a
  hash implementation (assumptions C1/C2); it is not proved here.
* Script-number encoding is fixed-width: `pushScriptNum16` always writes a
  three-byte push and `pushScriptNum32` always writes a five-byte push.
  BOLT 3 uses minimal `CScriptNum` encoding, so the 77/136/143-byte sizes
  are sizes of the scaffold's encoding, not bit-exact sizes for every
  protocol value.  Minimal-encoding injectivity is left as an obligation.
* There is no script interpreter, signature checking, or spendability
  proof.  Statements about the revocation path, CSV enforcement, the CLTV
  path, and the anchor's anyone-can-spend-after-16-blocks fallback are
  template-level only.
* BIP 69+CLTV output ordering, dust trimming, fee deduction, HTLC output
  values, `shared_anchor`/`zero_fee_commitments`, and the mutual-close
  transaction are outside this module.  `commitmentOutputs` is an
  anchors-commitment list with zero HTLCs in template order.
* The model always emits both anchors in `commitmentOutputs`; BOLT 3 omits
  an anchor when the corresponding commitment output is absent/below dust.
* The commitment-number obscuring hash is an input byte array; only the
  extraction and bit-position facts are proved, not that the array is
  `SHA256(payment_basepoint_1 || payment_basepoint_2)`.

All byte-comparison claims below are about the exact `Script.bytes`
produced by the wave-A builders; the wave-A definitions are not modified.
-/

namespace LnLean.Proofs.Bitcoin.ScriptProps

set_option autoImplicit false
set_option maxHeartbeats 1000000

open LnLean LnLean.Bitcoin

/-! ## Byte containment -/

/-- `hay` contains `needle` as a contiguous byte substring. -/
def BytesContain (hay needle : ByteArray) : Prop :=
  ∃ pre post : ByteArray, hay = pre ++ needle ++ post

/-- A script contains a byte string. -/
def ScriptContains (s : Script) (needle : ByteArray) : Prop :=
  BytesContain s.bytes needle

/-- A script contains the minimal push of a public key. -/
def ScriptContainsKey (s : Script) (k : PubKey) : Prop :=
  ScriptContains s (pushData k.bytes)

/-- A script contains a single opcode byte. -/
def ScriptContainsOp (s : Script) (op : UInt8) : Prop :=
  ScriptContains s (ByteArray.empty.push op)

theorem pushData_size (b : ByteArray) : (pushData b).size = b.size + 1 := by
  simp [pushData, ByteArray.size_append]
  omega

/-! ## `to_local` (BOLT 3 `:113-135`) -/

/-- The `to_local` witness script pushes the revocation key in its `OP_IF`
penalty branch. -/
theorem toLocal_contains_revocationKey (revocationKey delayedPaymentKey : PubKey)
    (toSelfDelay : Blocks) :
    ScriptContainsKey (toLocalWitnessScript revocationKey delayedPaymentKey toSelfDelay)
      revocationKey := by
  refine ⟨ByteArray.empty.push OP_IF,
    ByteArray.empty.push OP_ELSE ++ pushScriptNum16 toSelfDelay ++
      ByteArray.empty.push OP_CSV ++ ByteArray.empty.push OP_DROP ++
      pushData delayedPaymentKey.bytes ++ ByteArray.empty.push OP_ENDIF ++
      ByteArray.empty.push OP_CHECKSIG, ?_⟩
  unfold toLocalWitnessScript
  simp only [ByteArray.append_assoc]

/-- The `to_local` witness script pushes the delayed local payment key in its
`OP_ELSE` branch. -/
theorem toLocal_contains_delayedPaymentKey (revocationKey delayedPaymentKey : PubKey)
    (toSelfDelay : Blocks) :
    ScriptContainsKey (toLocalWitnessScript revocationKey delayedPaymentKey toSelfDelay)
      delayedPaymentKey := by
  refine ⟨ByteArray.empty.push OP_IF ++ pushData revocationKey.bytes ++
      ByteArray.empty.push OP_ELSE ++ pushScriptNum16 toSelfDelay ++
      ByteArray.empty.push OP_CSV ++ ByteArray.empty.push OP_DROP,
    ByteArray.empty.push OP_ENDIF ++ ByteArray.empty.push OP_CHECKSIG, ?_⟩
  unfold toLocalWitnessScript
  simp only [ByteArray.append_assoc]

/-- The `to_local` witness script contains the encoded `to_self_delay`. -/
theorem toLocal_contains_csvDelay (revocationKey delayedPaymentKey : PubKey)
    (toSelfDelay : Blocks) :
    ScriptContains (toLocalWitnessScript revocationKey delayedPaymentKey toSelfDelay)
      (pushScriptNum16 toSelfDelay) := by
  refine ⟨ByteArray.empty.push OP_IF ++ pushData revocationKey.bytes ++
      ByteArray.empty.push OP_ELSE,
    ByteArray.empty.push OP_CSV ++ ByteArray.empty.push OP_DROP ++
      pushData delayedPaymentKey.bytes ++ ByteArray.empty.push OP_ENDIF ++
      ByteArray.empty.push OP_CHECKSIG, ?_⟩
  unfold toLocalWitnessScript
  simp only [ByteArray.append_assoc]

/-- The `to_local` witness script contains the CSV opcode. -/
theorem toLocal_contains_csvOpcode (revocationKey delayedPaymentKey : PubKey)
    (toSelfDelay : Blocks) :
    ScriptContainsOp (toLocalWitnessScript revocationKey delayedPaymentKey toSelfDelay)
      OP_CSV := by
  refine ⟨ByteArray.empty.push OP_IF ++ pushData revocationKey.bytes ++
      ByteArray.empty.push OP_ELSE ++ pushScriptNum16 toSelfDelay,
    ByteArray.empty.push OP_DROP ++ pushData delayedPaymentKey.bytes ++
      ByteArray.empty.push OP_ENDIF ++ ByteArray.empty.push OP_CHECKSIG, ?_⟩
  unfold toLocalWitnessScript
  simp only [ByteArray.append_assoc]

/-- The `to_local` witness script is 77 bytes for two 33-byte compressed keys
and the scaffold's three-byte delay push. -/
theorem toLocalWitnessScript_size_77 (revocationKey delayedPaymentKey : PubKey)
    (toSelfDelay : Blocks)
    (h1 : revocationKey.bytes.size = 33)
    (h2 : delayedPaymentKey.bytes.size = 33) :
    (toLocalWitnessScript revocationKey delayedPaymentKey toSelfDelay).bytes.size = 77 := by
  unfold toLocalWitnessScript pushScriptNum16 pushUInt16LE
  simp only [pushData_size, ByteArray.size_append, ByteArray.size_push,
    ByteArray.size_empty]
  omega

/-- The length of `to_local` is determined by the template alone: any two
33-byte keys and any delay give the same byte length. -/
theorem toLocalWitnessScript_size_determined
    (revocationKey delayedPaymentKey revocationKey' delayedPaymentKey' : PubKey)
    (toSelfDelay toSelfDelay' : Blocks)
    (h1 : revocationKey.bytes.size = 33)
    (h2 : delayedPaymentKey.bytes.size = 33)
    (h3 : revocationKey'.bytes.size = 33)
    (h4 : delayedPaymentKey'.bytes.size = 33) :
    (toLocalWitnessScript revocationKey delayedPaymentKey toSelfDelay).bytes.size =
      (toLocalWitnessScript revocationKey' delayedPaymentKey' toSelfDelay').bytes.size := by
  have hA := toLocalWitnessScript_size_77 revocationKey delayedPaymentKey toSelfDelay h1 h2
  have hB := toLocalWitnessScript_size_77 revocationKey' delayedPaymentKey' toSelfDelay' h3 h4
  omega

/-! ## `to_remote` (BOLT 3 `:136-147`) -/

/-- The anchor variant of `to_remote` pushes the remote payment key. -/
theorem toRemote_contains_remotePaymentKey (remotePaymentKey : PubKey) :
    ScriptContainsKey (toRemoteWitnessScript remotePaymentKey) remotePaymentKey := by
  refine ⟨ByteArray.empty,
    ByteArray.empty.push OP_CHECKSIGVERIFY ++ ByteArray.empty.push OP_1 ++
      ByteArray.empty.push OP_CSV, ?_⟩
  unfold toRemoteWitnessScript
  simp only [ByteArray.append_assoc, ByteArray.empty_append]

/-- The no-anchor `to_remote` P2WPKH script contains the 20-byte payment-key
hash as its witness program. -/
theorem toRemoteP2WPKH_contains_paymentKeyHash (paymentKeyHash160 : ByteArray) :
    ScriptContains (toRemoteP2WPKHScriptPubKey paymentKeyHash160)
      paymentKeyHash160 := by
  refine ⟨(ByteArray.empty.push OP_0).push 0x14, ByteArray.empty, ?_⟩
  unfold toRemoteP2WPKHScriptPubKey p2wpkh
  simp only [ByteArray.append_empty]

/-- The P2WPKH `to_remote` output script is 22 bytes for a 20-byte digest. -/
theorem toRemoteP2WPKHScriptPubKey_size (paymentKeyHash160 : ByteArray)
    (h : paymentKeyHash160.size = 20) :
    (toRemoteP2WPKHScriptPubKey paymentKeyHash160).bytes.size = 22 := by
  unfold toRemoteP2WPKHScriptPubKey
  exact p2wpkh_size paymentKeyHash160 h

/-- The anchor variant of `to_remote` is 37 bytes for a 33-byte key. -/
theorem toRemoteWitnessScript_size_37 (remotePaymentKey : PubKey)
    (h : remotePaymentKey.bytes.size = 33) :
    (toRemoteWitnessScript remotePaymentKey).bytes.size = 37 := by
  unfold toRemoteWitnessScript
  simp only [pushData_size, ByteArray.size_append, ByteArray.size_push,
    ByteArray.size_empty]
  omega

/-- The P2WSH anchor variant and the P2WPKH no-anchor variant cannot be the
same script when the key and digest have their protocol lengths. -/
theorem toRemote_templates_distinct (remotePaymentKey : PubKey)
    (paymentKeyHash160 : ByteArray)
    (hk : remotePaymentKey.bytes.size = 33)
    (hh : paymentKeyHash160.size = 20) :
    toRemoteWitnessScript remotePaymentKey ≠
      toRemoteP2WPKHScriptPubKey paymentKeyHash160 := by
  intro heq
  have hsize := congrArg (fun s : Script => s.bytes.size) heq
  rw [toRemoteWitnessScript_size_37 remotePaymentKey hk,
    toRemoteP2WPKHScriptPubKey_size paymentKeyHash160 hh] at hsize
  omega

/-! ## Offered HTLC (BOLT 3 `:201-251`) -/

/-- The offered HTLC witness script contains `OP_HASH160` and the 20-byte
payment-hash digest. -/
theorem offeredHtlc_contains_paymentHash (revocationKeyHash160 paymentHash160 : ByteArray)
    (remoteHtlcKey localHtlcKey : PubKey) :
    ScriptContains (offeredHtlcWitnessScript revocationKeyHash160 paymentHash160
        remoteHtlcKey localHtlcKey)
      (ByteArray.empty.push OP_HASH160 ++ pushData paymentHash160) := by
  refine ⟨ByteArray.empty.push OP_DUP ++ ByteArray.empty.push OP_HASH160 ++
      pushData revocationKeyHash160 ++ ByteArray.empty.push OP_EQUAL ++
      ByteArray.empty.push OP_IF ++ ByteArray.empty.push OP_CHECKSIG ++
      ByteArray.empty.push OP_ELSE ++ pushData remoteHtlcKey.bytes ++
      ByteArray.empty.push OP_SWAP ++ ByteArray.empty.push OP_SIZE ++
      pushData (ByteArray.empty.push 32) ++ ByteArray.empty.push OP_EQUAL ++
      ByteArray.empty.push OP_NOTIF ++ ByteArray.empty.push OP_DROP ++
      ByteArray.empty.push OP_2 ++ ByteArray.empty.push OP_SWAP ++
      pushData localHtlcKey.bytes ++ ByteArray.empty.push OP_2 ++
      ByteArray.empty.push OP_CHECKMULTISIG ++ ByteArray.empty.push OP_ELSE,
    ByteArray.empty.push OP_EQUALVERIFY ++ ByteArray.empty.push OP_CHECKSIG ++
      ByteArray.empty.push OP_ENDIF ++ ByteArray.empty.push OP_1 ++
      ByteArray.empty.push OP_CSV ++ ByteArray.empty.push OP_DROP ++
      ByteArray.empty.push OP_ENDIF, ?_⟩
  unfold offeredHtlcWitnessScript
  simp only [ByteArray.append_assoc]

/-- The offered HTLC witness script pushes the remote HTLC key. -/
theorem offeredHtlc_contains_remoteHtlcKey (revocationKeyHash160 paymentHash160 : ByteArray)
    (remoteHtlcKey localHtlcKey : PubKey) :
    ScriptContainsKey (offeredHtlcWitnessScript revocationKeyHash160 paymentHash160
        remoteHtlcKey localHtlcKey) remoteHtlcKey := by
  refine ⟨ByteArray.empty.push OP_DUP ++ ByteArray.empty.push OP_HASH160 ++
      pushData revocationKeyHash160 ++ ByteArray.empty.push OP_EQUAL ++
      ByteArray.empty.push OP_IF ++ ByteArray.empty.push OP_CHECKSIG ++
      ByteArray.empty.push OP_ELSE,
    ByteArray.empty.push OP_SWAP ++ ByteArray.empty.push OP_SIZE ++
      pushData (ByteArray.empty.push 32) ++ ByteArray.empty.push OP_EQUAL ++
      ByteArray.empty.push OP_NOTIF ++ ByteArray.empty.push OP_DROP ++
      ByteArray.empty.push OP_2 ++ ByteArray.empty.push OP_SWAP ++
      pushData localHtlcKey.bytes ++ ByteArray.empty.push OP_2 ++
      ByteArray.empty.push OP_CHECKMULTISIG ++ ByteArray.empty.push OP_ELSE ++
      ByteArray.empty.push OP_HASH160 ++ pushData paymentHash160 ++
      ByteArray.empty.push OP_EQUALVERIFY ++ ByteArray.empty.push OP_CHECKSIG ++
      ByteArray.empty.push OP_ENDIF ++ ByteArray.empty.push OP_1 ++
      ByteArray.empty.push OP_CSV ++ ByteArray.empty.push OP_DROP ++
      ByteArray.empty.push OP_ENDIF, ?_⟩
  unfold offeredHtlcWitnessScript
  simp only [ByteArray.append_assoc]

/-- The offered HTLC witness script pushes the local HTLC key. -/
theorem offeredHtlc_contains_localHtlcKey (revocationKeyHash160 paymentHash160 : ByteArray)
    (remoteHtlcKey localHtlcKey : PubKey) :
    ScriptContainsKey (offeredHtlcWitnessScript revocationKeyHash160 paymentHash160
        remoteHtlcKey localHtlcKey) localHtlcKey := by
  refine ⟨ByteArray.empty.push OP_DUP ++ ByteArray.empty.push OP_HASH160 ++
      pushData revocationKeyHash160 ++ ByteArray.empty.push OP_EQUAL ++
      ByteArray.empty.push OP_IF ++ ByteArray.empty.push OP_CHECKSIG ++
      ByteArray.empty.push OP_ELSE ++ pushData remoteHtlcKey.bytes ++
      ByteArray.empty.push OP_SWAP ++ ByteArray.empty.push OP_SIZE ++
      pushData (ByteArray.empty.push 32) ++ ByteArray.empty.push OP_EQUAL ++
      ByteArray.empty.push OP_NOTIF ++ ByteArray.empty.push OP_DROP ++
      ByteArray.empty.push OP_2 ++ ByteArray.empty.push OP_SWAP,
    ByteArray.empty.push OP_2 ++ ByteArray.empty.push OP_CHECKMULTISIG ++
      ByteArray.empty.push OP_ELSE ++ ByteArray.empty.push OP_HASH160 ++
      pushData paymentHash160 ++ ByteArray.empty.push OP_EQUALVERIFY ++
      ByteArray.empty.push OP_CHECKSIG ++ ByteArray.empty.push OP_ENDIF ++
      ByteArray.empty.push OP_1 ++ ByteArray.empty.push OP_CSV ++
      ByteArray.empty.push OP_DROP ++ ByteArray.empty.push OP_ENDIF, ?_⟩
  unfold offeredHtlcWitnessScript
  simp only [ByteArray.append_assoc]

/-- The offered HTLC witness script is 136 bytes when both digests are 20
bytes and both HTLC keys are 33 bytes. -/
theorem offeredHtlcWitnessScript_size (revocationKeyHash160 paymentHash160 : ByteArray)
    (remoteHtlcKey localHtlcKey : PubKey)
    (hr : revocationKeyHash160.size = 20)
    (hp : paymentHash160.size = 20)
    (hk1 : remoteHtlcKey.bytes.size = 33)
    (hk2 : localHtlcKey.bytes.size = 33) :
    (offeredHtlcWitnessScript revocationKeyHash160 paymentHash160
        remoteHtlcKey localHtlcKey).bytes.size = 136 := by
  unfold offeredHtlcWitnessScript
  simp only [pushData_size, ByteArray.size_append, ByteArray.size_push,
    ByteArray.size_empty]
  omega

/-! ## Received HTLC (BOLT 3 `:253-300`) -/

/-- The received HTLC witness script contains `OP_HASH160` and the 20-byte
payment-hash digest in its success branch. -/
theorem receivedHtlc_contains_paymentHash (revocationKeyHash160 paymentHash160 : ByteArray)
    (remoteHtlcKey localHtlcKey : PubKey) (cltvExpiry : Height) :
    ScriptContains (receivedHtlcWitnessScript revocationKeyHash160 paymentHash160
        remoteHtlcKey localHtlcKey cltvExpiry)
      (ByteArray.empty.push OP_HASH160 ++ pushData paymentHash160) := by
  refine ⟨ByteArray.empty.push OP_DUP ++ ByteArray.empty.push OP_HASH160 ++
      pushData revocationKeyHash160 ++ ByteArray.empty.push OP_EQUAL ++
      ByteArray.empty.push OP_IF ++ ByteArray.empty.push OP_CHECKSIG ++
      ByteArray.empty.push OP_ELSE ++ pushData remoteHtlcKey.bytes ++
      ByteArray.empty.push OP_SWAP ++ ByteArray.empty.push OP_SIZE ++
      pushData (ByteArray.empty.push 32) ++ ByteArray.empty.push OP_EQUAL ++
      ByteArray.empty.push OP_IF,
    ByteArray.empty.push OP_EQUALVERIFY ++ ByteArray.empty.push OP_2 ++
      ByteArray.empty.push OP_SWAP ++ pushData localHtlcKey.bytes ++
      ByteArray.empty.push OP_2 ++ ByteArray.empty.push OP_CHECKMULTISIG ++
      ByteArray.empty.push OP_ELSE ++ ByteArray.empty.push OP_DROP ++
      pushScriptNum32 cltvExpiry ++ ByteArray.empty.push OP_CLTV ++
      ByteArray.empty.push OP_DROP ++ ByteArray.empty.push OP_CHECKSIG ++
      ByteArray.empty.push OP_ENDIF ++ ByteArray.empty.push OP_1 ++
      ByteArray.empty.push OP_CSV ++ ByteArray.empty.push OP_DROP ++
      ByteArray.empty.push OP_ENDIF, ?_⟩
  unfold receivedHtlcWitnessScript
  simp only [ByteArray.append_assoc]

/-- The received HTLC witness script contains the CLTV branch
`<cltv_expiry> OP_CLTV OP_DROP`. -/
theorem receivedHtlc_contains_cltvBranch (revocationKeyHash160 paymentHash160 : ByteArray)
    (remoteHtlcKey localHtlcKey : PubKey) (cltvExpiry : Height) :
    ScriptContains (receivedHtlcWitnessScript revocationKeyHash160 paymentHash160
        remoteHtlcKey localHtlcKey cltvExpiry)
      (pushScriptNum32 cltvExpiry ++ ByteArray.empty.push OP_CLTV ++
        ByteArray.empty.push OP_DROP) := by
  refine ⟨ByteArray.empty.push OP_DUP ++ ByteArray.empty.push OP_HASH160 ++
      pushData revocationKeyHash160 ++ ByteArray.empty.push OP_EQUAL ++
      ByteArray.empty.push OP_IF ++ ByteArray.empty.push OP_CHECKSIG ++
      ByteArray.empty.push OP_ELSE ++ pushData remoteHtlcKey.bytes ++
      ByteArray.empty.push OP_SWAP ++ ByteArray.empty.push OP_SIZE ++
      pushData (ByteArray.empty.push 32) ++ ByteArray.empty.push OP_EQUAL ++
      ByteArray.empty.push OP_IF ++ ByteArray.empty.push OP_HASH160 ++
      pushData paymentHash160 ++ ByteArray.empty.push OP_EQUALVERIFY ++
      ByteArray.empty.push OP_2 ++ ByteArray.empty.push OP_SWAP ++
      pushData localHtlcKey.bytes ++ ByteArray.empty.push OP_2 ++
      ByteArray.empty.push OP_CHECKMULTISIG ++ ByteArray.empty.push OP_ELSE ++
      ByteArray.empty.push OP_DROP,
    ByteArray.empty.push OP_CHECKSIG ++ ByteArray.empty.push OP_ENDIF ++
      ByteArray.empty.push OP_1 ++ ByteArray.empty.push OP_CSV ++
      ByteArray.empty.push OP_DROP ++ ByteArray.empty.push OP_ENDIF, ?_⟩
  unfold receivedHtlcWitnessScript
  simp only [ByteArray.append_assoc]

/-- The received HTLC witness script is 143 bytes when both digests are 20
bytes and both HTLC keys are 33 bytes. -/
theorem receivedHtlcWitnessScript_size (revocationKeyHash160 paymentHash160 : ByteArray)
    (remoteHtlcKey localHtlcKey : PubKey) (cltvExpiry : Height)
    (hr : revocationKeyHash160.size = 20)
    (hp : paymentHash160.size = 20)
    (hk1 : remoteHtlcKey.bytes.size = 33)
    (hk2 : localHtlcKey.bytes.size = 33) :
    (receivedHtlcWitnessScript revocationKeyHash160 paymentHash160
        remoteHtlcKey localHtlcKey cltvExpiry).bytes.size = 143 := by
  unfold receivedHtlcWitnessScript pushScriptNum32 pushUInt32LE
  simp only [pushData_size, ByteArray.size_append, ByteArray.size_push,
    ByteArray.size_empty]
  omega

/-- The offered and received HTLC templates are distinguishable by length. -/
theorem htlcTemplates_distinct (revocationKeyHash160 paymentHash160 : ByteArray)
    (remoteHtlcKey localHtlcKey : PubKey) (cltvExpiry : Height)
    (hr : revocationKeyHash160.size = 20)
    (hp : paymentHash160.size = 20)
    (hk1 : remoteHtlcKey.bytes.size = 33)
    (hk2 : localHtlcKey.bytes.size = 33) :
    offeredHtlcWitnessScript revocationKeyHash160 paymentHash160
        remoteHtlcKey localHtlcKey ≠
      receivedHtlcWitnessScript revocationKeyHash160 paymentHash160
        remoteHtlcKey localHtlcKey cltvExpiry := by
  intro heq
  have hsize := congrArg (fun s : Script => s.bytes.size) heq
  rw [offeredHtlcWitnessScript_size revocationKeyHash160 paymentHash160
        remoteHtlcKey localHtlcKey hr hp hk1 hk2,
    receivedHtlcWitnessScript_size revocationKeyHash160 paymentHash160
        remoteHtlcKey localHtlcKey cltvExpiry hr hp hk1 hk2] at hsize
  omega

/-! ## Keyed anchor (BOLT 3 `:148-177`, 330 sat) -/

/-- The keyed anchor witness script pushes the funding key. -/
theorem anchor_contains_fundingKey (fundingKey : PubKey) :
    ScriptContainsKey (anchorWitnessScript fundingKey) fundingKey := by
  refine ⟨ByteArray.empty,
    ByteArray.empty.push OP_CHECKSIG ++ ByteArray.empty.push OP_IFDUP ++
      ByteArray.empty.push OP_NOTIF ++ ByteArray.empty.push OP_16 ++
      ByteArray.empty.push OP_CSV ++ ByteArray.empty.push OP_ENDIF, ?_⟩
  unfold anchorWitnessScript
  simp only [ByteArray.append_assoc, ByteArray.empty_append]

/-- The anchor witness script contains the `OP_16 OP_CSV` anyone-can-spend
fallback branch. -/
theorem anchor_contains_csv16 (fundingKey : PubKey) :
    ScriptContainsOp (anchorWitnessScript fundingKey) OP_16 := by
  refine ⟨pushData fundingKey.bytes ++ ByteArray.empty.push OP_CHECKSIG ++
      ByteArray.empty.push OP_IFDUP ++ ByteArray.empty.push OP_NOTIF,
    ByteArray.empty.push OP_CSV ++ ByteArray.empty.push OP_ENDIF, ?_⟩
  unfold anchorWitnessScript
  simp only [ByteArray.append_assoc]

/-- The keyed anchor witness script is 40 bytes for a 33-byte funding key. -/
theorem anchorWitnessScript_size_40 (fundingKey : PubKey)
    (h : fundingKey.bytes.size = 33) :
    (anchorWitnessScript fundingKey).bytes.size = 40 := by
  unfold anchorWitnessScript
  simp only [pushData_size, ByteArray.size_append, ByteArray.size_push,
    ByteArray.size_empty]
  omega

/-! ## `commitmentOutputs` structure and anchor values -/

/-- The zero-HTLC anchor commitment has exactly four outputs. -/
theorem commitmentOutputs_length_four (p : CommitmentParams) :
    (commitmentOutputs p).length = 4 := rfl

/-- The output kinds are in template order. -/
theorem commitmentOutputs_kinds_list (p : CommitmentParams) :
    (commitmentOutputs p).map CommitmentOutput.kind =
      [.toLocal, .toRemote, .localAnchor, .remoteAnchor] := rfl

/-- The output values are the two commitment values followed by the two
330-sat anchors. -/
theorem commitmentOutputs_values (p : CommitmentParams) :
    (commitmentOutputs p).map CommitmentOutput.value =
      [p.toLocalValue, p.toRemoteValue, anchorValue, anchorValue] := rfl

/-- The two anchor outputs are exactly the BOLT 3 330-sat outputs. -/
theorem commitmentOutputs_anchorValues (p : CommitmentParams) :
    (commitmentOutputs p).map (fun o => (o.kind, o.value)) =
      [(OutputKind.toLocal, p.toLocalValue),
       (OutputKind.toRemote, p.toRemoteValue),
       (OutputKind.localAnchor, 330),
       (OutputKind.remoteAnchor, 330)] := by
  rfl

/-- The output scripts are the four wave-A templates applied to the stored
witness-script hashes. -/
theorem commitmentOutputs_scripts (p : CommitmentParams) :
    (commitmentOutputs p).map CommitmentOutput.scriptPubKey =
      [toLocalScriptPubKey p.toLocalWitnessScriptHash,
       toRemoteScriptPubKey p.toRemoteWitnessScriptHash,
       anchorScriptPubKey p.localAnchorWitnessScriptHash,
       anchorScriptPubKey p.remoteAnchorWitnessScriptHash] := rfl

/-- `commitmentOutputs` is a total and deterministic output construction: the
list is uniquely determined by the parameters. -/
theorem commitmentOutputs_total_deterministic (p : CommitmentParams) :
    ∃ outs : List CommitmentOutput, commitmentOutputs p = outs ∧
      ∀ q : List CommitmentOutput, commitmentOutputs p = q → q = outs :=
  ⟨commitmentOutputs p, rfl, fun _ hq => hq.symm⟩

/-! ## Well-formedness and malformed key/hash rejection -/

/-- Structural well-formedness of the parameters used by `commitmentOutputs`:
every key is a 33-byte compressed key and every witness-script hash is 32
bytes.  This is the model's validity predicate for commitment output
construction; the cryptographic content of the keys/hashes is not checked. -/
def ParamsWellFormed (p : CommitmentParams) : Prop :=
  p.revocationKey.Valid ∧ p.delayedPaymentKey.Valid ∧ p.remotePaymentKey.Valid ∧
  p.localFundingKey.Valid ∧ p.remoteFundingKey.Valid ∧
  p.toLocalWitnessScriptHash.size = 32 ∧ p.toRemoteWitnessScriptHash.size = 32 ∧
  p.localAnchorWitnessScriptHash.size = 32 ∧
  p.remoteAnchorWitnessScriptHash.size = 32

theorem wellFormed_revocationKey (p : CommitmentParams) (h : ParamsWellFormed p) :
    p.revocationKey.bytes.size = 33 := by
  rcases h with ⟨h1, _, _, _, _, _, _, _, _⟩
  exact h1

theorem wellFormed_delayedPaymentKey (p : CommitmentParams) (h : ParamsWellFormed p) :
    p.delayedPaymentKey.bytes.size = 33 := by
  rcases h with ⟨_, h1, _, _, _, _, _, _, _⟩
  exact h1

theorem wellFormed_toLocalHash (p : CommitmentParams) (h : ParamsWellFormed p) :
    p.toLocalWitnessScriptHash.size = 32 := by
  rcases h with ⟨_, _, _, _, _, h1, _, _, _⟩
  exact h1

theorem wellFormed_toRemoteHash (p : CommitmentParams) (h : ParamsWellFormed p) :
    p.toRemoteWitnessScriptHash.size = 32 := by
  rcases h with ⟨_, _, _, _, _, _, h1, _, _⟩
  exact h1

theorem wellFormed_localAnchorHash (p : CommitmentParams) (h : ParamsWellFormed p) :
    p.localAnchorWitnessScriptHash.size = 32 := by
  rcases h with ⟨_, _, _, _, _, _, _, h1, _⟩
  exact h1

theorem wellFormed_remoteAnchorHash (p : CommitmentParams) (h : ParamsWellFormed p) :
    p.remoteAnchorWitnessScriptHash.size = 32 := by
  rcases h with ⟨_, _, _, _, _, _, _, _, h1⟩
  exact h1

/-- Under the validity predicate, the `to_local` witness script built from
the parameters is 77 bytes. -/
theorem wellFormed_toLocalWitnessScript_size (p : CommitmentParams)
    (h : ParamsWellFormed p) :
    (toLocalWitnessScript p.revocationKey p.delayedPaymentKey p.toSelfDelay).bytes.size = 77 :=
  toLocalWitnessScript_size_77 p.revocationKey p.delayedPaymentKey p.toSelfDelay
    (wellFormed_revocationKey p h) (wellFormed_delayedPaymentKey p h)

/-- Under the validity predicate, all four output scripts are 34-byte P2WSH
programs. -/
theorem wellFormed_outputScript_sizes (p : CommitmentParams) (h : ParamsWellFormed p) :
    ∀ o ∈ commitmentOutputs p, o.scriptPubKey.bytes.size = 34 := by
  intro o ho
  have h1 := wellFormed_toLocalHash p h
  have h2 := wellFormed_toRemoteHash p h
  have h3 := wellFormed_localAnchorHash p h
  have h4 := wellFormed_remoteAnchorHash p h
  simp only [commitmentOutputs, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl
  · exact p2wsh_size _ h1
  · exact p2wsh_size _ h2
  · exact p2wsh_size _ h3
  · exact p2wsh_size _ h4

/-- A 32-byte value is not a valid compressed public key. -/
def shortKey : PubKey := ⟨ByteArray.mk (List.replicate 32 0).toArray⟩

theorem shortKey_not_valid : ¬ shortKey.Valid := by
  unfold shortKey PubKey.Valid
  decide

/-- A 31-byte value is not a valid 32-byte witness-script hash. -/
def shortHash : ByteArray := ByteArray.mk (List.replicate 31 0).toArray

theorem shortHash_size : shortHash.size = 31 := by
  unfold shortHash
  decide

/-- A parameter record with a 32-byte revocation key is rejected by the
validity predicate. -/
theorem malformedKey_rejected (p : CommitmentParams) :
    ¬ ParamsWellFormed { p with revocationKey := shortKey } := by
  intro h
  have h1 := wellFormed_revocationKey _ h
  have h2 : shortKey.bytes.size = 32 := by
    unfold shortKey
    decide
  rw [h2] at h1
  omega

/-- A parameter record with a 31-byte `to_local` witness-script hash is
rejected by the validity predicate. -/
theorem malformedHash_rejected (p : CommitmentParams) :
    ¬ ParamsWellFormed { p with toLocalWitnessScriptHash := shortHash } := by
  intro h
  have h1 := wellFormed_toLocalHash _ h
  have h2 : shortHash.size = 31 := shortHash_size
  rw [h2] at h1
  omega

/-- `PaymentHash.Valid` rejects a digest whose byte length is not 32. -/
theorem malformedPaymentHash_rejected (h : PaymentHash) (hbad : h.bytes.size ≠ 32) :
    ¬ h.Valid := hbad

/-! ## Commitment-number obscuring (BOLT 3 `:90-112`) -/

/-- Byte `i` of a hash as a natural number (`0` if out of range). -/
def hashByte (h : ByteArray) (i : Nat) : Nat := (h.get! i).toNat

/-- The lower 48 bits of a 32-byte hash, laid out as in LDK's
`get_commitment_transaction_number_obscure_factor`: bytes 26 through 31 in
big-endian order. -/
def obscureFactor (h : ByteArray) : Nat :=
  hashByte h 26 * 2^40 + hashByte h 27 * 2^32 + hashByte h 28 * 2^24 +
  hashByte h 29 * 2^16 + hashByte h 30 * 2^8 + hashByte h 31

theorem obscureFactor_lt_two_pow_48 (h : ByteArray) : obscureFactor h < 2^48 := by
  have h26 := UInt8.toNat_lt (h.get! 26)
  have h27 := UInt8.toNat_lt (h.get! 27)
  have h28 := UInt8.toNat_lt (h.get! 28)
  have h29 := UInt8.toNat_lt (h.get! 29)
  have h30 := UInt8.toNat_lt (h.get! 30)
  have h31 := UInt8.toNat_lt (h.get! 31)
  unfold obscureFactor hashByte
  omega

/-- BOLT 3/LDK obscure `INITIAL_COMMITMENT_NUMBER - n` by XOR with the
48-bit factor. -/
def obscuredNumber (factor n : Nat) : Nat := factor ^^^ (2^48 - 1 - n)

theorem obscuredNumber_lt_two_pow_48 (factor n : Nat)
    (hf : factor < 2^48) (hn : n < 2^48) :
    obscuredNumber factor n < 2^48 := by
  exact Nat.xor_lt_two_pow hf (by omega)

/-- The commitment locktime word: upper byte `0x20`, low 24 bits from the
obscured number. -/
def commitmentLocktime (factor n : Nat) : Nat :=
  0x20 * 2^24 + (obscuredNumber factor n &&& 0xffffff)

/-- The commitment input sequence word: upper byte `0x80`, low 24 bits from
the obscured number. -/
def commitmentSequence (factor n : Nat) : Nat :=
  0x80 * 2^24 + obscuredNumber factor n / 2^24

/-- BOLT 3 fixes the locktime's upper byte to `0x20`. -/
theorem commitmentLocktime_highByte (factor n : Nat) :
    commitmentLocktime factor n / 2^24 = 0x20 := by
  unfold commitmentLocktime
  rw [Nat.mul_comm 0x20 (2^24), Nat.mul_add_div (by decide)]
  have hz : (obscuredNumber factor n &&& 0xffffff) / 2^24 = 0 :=
    Nat.div_eq_of_lt (Nat.and_lt_two_pow _ (by decide))
  rw [hz, Nat.add_zero]

/-- BOLT 3 puts the low 24 bits of the obscured number in the locktime. -/
theorem commitmentLocktime_low24 (factor n : Nat) :
    commitmentLocktime factor n &&& 0xffffff =
      obscuredNumber factor n &&& 0xffffff := by
  unfold commitmentLocktime
  rw [show (0xffffff : Nat) = 2^24 - 1 by decide]
  rw [Nat.and_two_pow_sub_one_eq_mod]
  rw [Nat.mul_comm 0x20 (2^24)]
  rw [Nat.add_comm (2^24 * _) _, Nat.add_mul_mod_self_left]
  rw [← Nat.and_two_pow_sub_one_eq_mod]
  rw [show (2^24 - 1 : Nat) = 0xffffff by decide]
  rw [Nat.and_assoc, Nat.and_self]

/-- BOLT 3 fixes the sequence's upper byte to `0x80`. -/
theorem commitmentSequence_highByte (factor n : Nat)
    (hf : factor < 2^48) (hn : n < 2^48) :
    commitmentSequence factor n / 2^24 = 0x80 := by
  unfold commitmentSequence
  rw [Nat.mul_comm 0x80 (2^24), Nat.mul_add_div (by decide)]
  have hlt : obscuredNumber factor n < 2^48 :=
    obscuredNumber_lt_two_pow_48 factor n hf hn
  have hr : obscuredNumber factor n / 2^24 < 2^24 := by
    rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 2^24)]
    have hpow : 2^24 * 2^24 = 2^48 := by decide
    rw [hpow]
    exact hlt
  have hz : obscuredNumber factor n / 2^24 / 2^24 = 0 := Nat.div_eq_of_lt hr
  rw [hz, Nat.add_zero]

/-- BOLT 3 puts the next 24 bits of the obscured number in the sequence. -/
theorem commitmentSequence_low24 (factor n : Nat) :
    commitmentSequence factor n &&& 0xffffff =
      (obscuredNumber factor n / 2^24) &&& 0xffffff := by
  unfold commitmentSequence
  rw [show (0xffffff : Nat) = 2^24 - 1 by decide]
  rw [Nat.and_two_pow_sub_one_eq_mod]
  rw [Nat.mul_comm 0x80 (2^24)]
  rw [Nat.add_comm (2^24 * _) _, Nat.add_mul_mod_self_left]
  rw [← Nat.and_two_pow_sub_one_eq_mod]

/-! ## Local helpers for the script-number and byte-string proofs -/

/-- The fixed-width four-byte little-endian encoding always has length four. -/
private theorem pushUInt32LE_size (n : Nat) : (pushUInt32LE n).size = 4 := by
  unfold pushUInt32LE
  simp

/-- `pushData` is injective when both payloads have the same length. -/
private theorem pushData_injective_of_size_eq {a b : ByteArray}
    (ha : a.size = b.size) (h : pushData a = pushData b) : a = b := by
  unfold pushData at h
  rw [ha] at h
  exact (ByteArray.append_right_inj (ByteArray.empty.push b.size.toUInt8)).mp h

/-! ## Open proof obligations -/

/-- `pushScriptNum32` is injective on values below `2^32`; this is the
missing ingredient for saying that the received-HTLC script binds the CLTV
expiry, and for the minimal script-number encoding bridge. -/
theorem pushScriptNum32_injective {a b : Nat} (ha : a < 2^32) (hb : b < 2^32)
    (h : pushScriptNum32 a = pushScriptNum32 b) : a = b := by
  -- OBLIGATION: LN-SCRIPT-001 The fixed-width four-byte little-endian push is injective on values below 2^32.
  have hx : pushUInt32LE a = pushUInt32LE b := by
    unfold pushScriptNum32 at h
    exact pushData_injective_of_size_eq
      (by rw [pushUInt32LE_size, pushUInt32LE_size]) h
  have hlist : (pushUInt32LE a).data.toList = (pushUInt32LE b).data.toList := by
    rw [hx]
  simp [pushUInt32LE] at hlist
  rcases hlist with ⟨e0, e1, e2, e3⟩
  have h0 : a % 256 = b % 256 := by
    have := congrArg UInt8.toNat e0
    simpa using this
  have h1 : (a / 256) % 256 = (b / 256) % 256 := by
    have := congrArg UInt8.toNat e1
    simpa [Nat.shiftRight_eq_div_pow] using this
  have h2 : (a / 65536) % 256 = (b / 65536) % 256 := by
    have := congrArg UInt8.toNat e2
    simpa [Nat.shiftRight_eq_div_pow] using this
  have h3 : (a / 16777216) % 256 = (b / 16777216) % 256 := by
    have := congrArg UInt8.toNat e3
    simpa [Nat.shiftRight_eq_div_pow] using this
  omega

/-- Distinct CLTV expiries (< 2^32) give distinct received-HTLC witness
scripts when all other parameters are held fixed. -/
theorem receivedHtlcWitnessScript_cltv_injective
    (revocationKeyHash160 paymentHash160 : ByteArray)
    (remoteHtlcKey localHtlcKey : PubKey) {c1 c2 : Height}
    (h1 : c1 < 2^32) (h2 : c2 < 2^32)
    (h : receivedHtlcWitnessScript revocationKeyHash160 paymentHash160
          remoteHtlcKey localHtlcKey c1 =
        receivedHtlcWitnessScript revocationKeyHash160 paymentHash160
          remoteHtlcKey localHtlcKey c2) : c1 = c2 := by
  -- OBLIGATION: LN-SCRIPT-002 Distinct CLTV expiries yield distinct received-HTLC witness scripts, so the script commits to the expiry.
  have hb : (receivedHtlcWitnessScript revocationKeyHash160 paymentHash160
          remoteHtlcKey localHtlcKey c1).bytes =
        (receivedHtlcWitnessScript revocationKeyHash160 paymentHash160
          remoteHtlcKey localHtlcKey c2).bytes := by
    rw [h]
  unfold receivedHtlcWitnessScript at hb
  simp only [ByteArray.append_assoc] at hb
  have hx : pushScriptNum32 c1 = pushScriptNum32 c2 := by
    simpa only [ByteArray.append_right_inj, ByteArray.append_left_inj] using hb
  exact pushScriptNum32_injective h1 h2 hx

/-- Distinct 20-byte payment-hash digests give distinct offered-HTLC witness
scripts when all other parameters are held fixed. -/
theorem offeredHtlcWitnessScript_paymentHash_injective
    (revocationKeyHash160 : ByteArray) (remoteHtlcKey localHtlcKey : PubKey)
    {h1 h2 : ByteArray} (hh1 : h1.size = 20) (hh2 : h2.size = 20)
    (h : offeredHtlcWitnessScript revocationKeyHash160 h1 remoteHtlcKey localHtlcKey =
        offeredHtlcWitnessScript revocationKeyHash160 h2 remoteHtlcKey localHtlcKey) :
    h1 = h2 := by
  -- OBLIGATION: LN-SCRIPT-003 Distinct 20-byte payment-hash digests yield distinct offered-HTLC witness scripts, so the script commits to the payment hash.
  have hb : (offeredHtlcWitnessScript revocationKeyHash160 h1 remoteHtlcKey localHtlcKey).bytes =
        (offeredHtlcWitnessScript revocationKeyHash160 h2 remoteHtlcKey localHtlcKey).bytes := by
    rw [h]
  unfold offeredHtlcWitnessScript at hb
  simp only [ByteArray.append_assoc] at hb
  have hx : pushData h1 = pushData h2 := by
    simpa only [ByteArray.append_right_inj, ByteArray.append_left_inj] using hb
  exact pushData_injective_of_size_eq (by omega) hx

end LnLean.Proofs.Bitcoin.ScriptProps
