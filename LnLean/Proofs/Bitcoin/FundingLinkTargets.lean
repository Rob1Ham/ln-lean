import LnLean.Protocol.Handshake
import LnLean.Proofs.Bitcoin.FundingScriptTargets
import LnLean.Crypto.Model

/-!
# Funding witness-script hash link from the handshake construction

**English claim (`L1-03`, `L1-05`).**  The BOLT 2 handshake fixes the funding
output: `open_channel` supplies the opener's `funding_pubkey`,
`accept_channel` supplies the acceptor's `funding_pubkey`, and the output is
the BOLT 3 P2WSH of

`OP_2 <pubkey1> <pubkey2> OP_2 OP_CHECKMULTISIG`.

`LnLean.Proofs.Bitcoin.FundingScriptTargets` proved the output shape only
under the explicit hypothesis

`FundingScriptHashLinked H p := p.witnessScriptHash = H p.witnessScript.bytes`

because `FundingParams` stores `witnessScriptHash` as a free field.  A
hypothesis is not a construction: nothing prevented a caller from pairing the
right 2-of-2 keys with an unrelated 32-byte program.

This module closes that gap for the handshake path.  `FundingNegotiation`
(`LnLean.Bitcoin.Funding`) is the handshake-derived record; it carries the two
funding keys and the value/push/temporary-id fields, but **not** the P2WSH
program.  `FundingNegotiation.toFundingParams H` *computes* the program as
`H (witnessScript.bytes)`.  Therefore:

* `toFundingParams_hash_linked` — the hash link of `LN-L1-001` holds by `rfl`
  for every constructed parameter set, for any `H`.  No hash hypothesis is
  assumed.
* `fundingScriptPubKey_eq_p2wsh_twoOfTwo_constructed` — the existing
  `FundingScriptTargets.fundingScriptPubKey_eq_p2wsh_twoOfTwo` conclusion now
  holds **unconditionally** (up to the choice of `H`) for constructed
  parameters.
* `acceptChannel_funding_link` — the same facts stated from a received
  `AcceptChannel`, whose `funding_pubkey` field is proved to be exactly the
  remote key used in the script.
* `toFundingParams_hash_linked_sha256` — the SHA-256 instance
  `H := M.sha256` of `PrimitiveModel`.  The construction says the stored
  program *is* `M.sha256` of the script bytes; it does not assume that
  `M.sha256` is the FIPS 180-4 function, which the model does not provide.

## The finite C1 admission is kept

The forward link is definitional, but the *reverse* direction (a revealed
script whose hash matches the output is the funding script) is still a
cryptographic statement.  This module keeps the finite pair admission

`CollisionFreeOn H x y := H x = H y → x = y`

from `FundingScriptTargets`, at the exact pair of the revealed script and the
constructed script.  It does **not** assume global SHA-256 injectivity, and it
does not use C1 (injectivity on 32-byte preimages), which
`c1_32_does_not_bind_funding_witnessScripts` shows is insufficient for
71-byte scripts.  `constructed_binds_twoOfTwo` is the constructed-parameter
form of `FundingScriptTargets.fundingScriptPubKey_binds_twoOfTwo`.

## What a handshake field does not determine

The witness script is determined by *both* funding keys.  `accept_channel`
carries only the remote key; the local key is an `open_channel` choice, and
`open_channel` is not a `Msg` constructor in this model (see
`LnLean.Protocol.Handshake`).  `acceptChannel_alone_does_not_determine_witnessScript`
mechanizes that limitation: one `accept_channel` record is compatible with two
distinct witness scripts, so the handshake message alone is not a function to
the script.  `Handshake.acceptReceived_of_sendFundingCreated` shows the
ordering side: the remote key is available before `funding_created` may be
sent.

The construction is also not authenticated at this layer: `AcceptChannel`
fields are only length-checked, and signature verification (C3) and the
Noise transport are out of scope.  `accept_channel.funding_pubkey` is the key
the peer *claims*; binding it to the signer is `PR-01`, not this lane.

## Anchors

* BOLT 2 §The `open_channel` Message (`funding_satoshis`, `push_msat`,
  `funding_pubkey`, temporary channel id) and §The `accept_channel` Message
  (`funding_pubkey`).
* BOLT 3 §Funding Transaction Output: P2WSH over
  `2 <pubkey1> <pubkey2> 2 OP_CHECKMULTISIG`.
* `refs/rust-lightning/lightning/src/ln/chan_utils.rs:847-866`
  (`make_funding_redeemscript`, key ordering) and
  `lightning/src/ln/channel.rs:2711-2725` (`get_funding_txo`).
-/

namespace LnLean.Proofs.Bitcoin.FundingLinkTargets

set_option autoImplicit false

open LnLean
open LnLean.Bitcoin
open LnLean.Crypto
open LnLean.Protocol
open LnLean.Proofs.Bitcoin.FundingScriptTargets

/-! ## The construction discharges the hash link -/

/-- **`L1-03`, primary result.**  The parameters built from a handshake
negotiation satisfy `FundingScriptHashLinked H` by construction: the stored
program is `H` of the witness script bytes.  The proof is `rfl`; there is no
hash hypothesis. -/
theorem toFundingParams_hash_linked (H : ByteArray → ByteArray)
    (n : FundingNegotiation) :
    FundingScriptHashLinked H (n.toFundingParams H) :=
  FundingNegotiation.toFundingParams_witnessScriptHash H n

/-- The SHA-256 instance of the construction: the stored program is exactly
`PrimitiveModel.sha256` of the BOLT 3 witness script bytes.  `M.sha256` is the
model's opaque SHA-256 interface, not a verified FIPS 180-4 implementation. -/
theorem toFundingParams_hash_linked_sha256 (M : PrimitiveModel)
    (n : FundingNegotiation) :
    FundingScriptHashLinked M.sha256 (n.toFundingParams M.sha256) :=
  toFundingParams_hash_linked M.sha256 n

/-- The constructed program is 32 bytes for any 32-byte-output `H`, hence in
particular for `PrimitiveModel.sha256` by `sha256_size`. -/
theorem toFundingParams_witnessScriptHash_size (H : ByteArray → ByteArray)
    (hH : ∀ b : ByteArray, (H b).size = 32) (n : FundingNegotiation) :
    (n.toFundingParams H).witnessScriptHash.size = 32 :=
  FundingNegotiation.toFundingParams_witnessScriptHash_size H hH n

/-- The SHA-256 instance of the width law. -/
theorem toFundingParams_witnessScriptHash_size_sha256 (M : PrimitiveModel)
    (n : FundingNegotiation) :
    (n.toFundingParams M.sha256).witnessScriptHash.size = 32 :=
  FundingNegotiation.toFundingParams_witnessScriptHash_size M.sha256
    M.sha256_size n

/-- The constructed `scriptPubKey` is literally `p2wsh (H witnessScript)`. -/
theorem toFundingParams_scriptPubKey_eq_p2wsh (H : ByteArray → ByteArray)
    (n : FundingNegotiation) :
    (n.toFundingParams H).fundingScriptPubKey =
      p2wsh (H (n.toFundingParams H).witnessScript.bytes) :=
  FundingNegotiation.toFundingParams_fundingScriptPubKey H n

/-! ## The BOLT 3 script is exactly the ordered 2-of-2 template -/

/-- The constructed witness script bytes are exactly
`TwoOfTwoScriptBytes first second` for the ordered key pair.  This is the
byte-level bridge from the constructor to the pre-existing
`TwoOfTwoScriptBytes` template; it is definitional. -/
theorem witnessScript_bytes_eq_TwoOfTwoScriptBytes (n : FundingNegotiation) :
    n.witnessScript.bytes =
      TwoOfTwoScriptBytes n.firstFundingKey n.secondFundingKey := rfl

/-- The constructor's script is a 2-of-2 multisig over exactly the two input
keys, in one of the two BOLT 3 orders.  This is the `FundingScript`-level
counterpart of `witnessScript_isTwoOfTwoScript`; it is stated here because
`Funding.lean` cannot import the proof module that defines
`TwoOfTwoScriptBytes`. -/
theorem ofKeys_witnessScript_isTwoOfTwo (a b : PubKey) :
    IsTwoOfTwoScript a b (FundingScript.ofKeys a b).witnessScript.bytes := by
  rcases LnLean.Proofs.Bitcoin.FundingProps.orderedFundingKeys_pair a b with
    h | h
  · left
    rw [FundingScript.ofKeys_witnessScript_bytes]
    simp [TwoOfTwoScriptBytes, h]
  · right
    rw [FundingScript.ofKeys_witnessScript_bytes]
    simp [TwoOfTwoScriptBytes, h]

/-- The constructed script's bytes are the ordered 2-of-2 template, stated at
the parameter level. -/
theorem toFundingParams_witnessScript_bytes_eq_TwoOfTwo (H : ByteArray →
    ByteArray) (n : FundingNegotiation) :
    (n.toFundingParams H).witnessScript.bytes =
      TwoOfTwoScriptBytes n.firstFundingKey n.secondFundingKey :=
  witnessScript_bytes_eq_TwoOfTwoScriptBytes n

/-- **`L1-03`, ordered form.**  For constructed parameters the funding output
is P2WSH over the exact ordered BOLT 3 2-of-2 script, without a hash
hypothesis. -/
theorem fundingScriptPubKey_eq_p2wsh_ordered (H : ByteArray → ByteArray)
    (n : FundingNegotiation) :
    (n.toFundingParams H).fundingScriptPubKey =
      p2wsh (H (TwoOfTwoScriptBytes n.firstFundingKey
        n.secondFundingKey)) := by
  rw [toFundingParams_scriptPubKey_eq_p2wsh]
  rw [FundingNegotiation.toFundingParams_witnessScript]
  rw [witnessScript_bytes_eq_TwoOfTwoScriptBytes]

/-- **`L1-03`, existing-target form.**  `FundingScriptTargets`'
`fundingScriptPubKey_eq_p2wsh_twoOfTwo` is recovered for constructed
parameters with the hash-link hypothesis discharged.  The disjunction records
the two possible BOLT 3 key orientations of the local/remote pair. -/
theorem fundingScriptPubKey_eq_p2wsh_twoOfTwo_constructed
    (H : ByteArray → ByteArray) (n : FundingNegotiation) :
    (n.toFundingParams H).fundingScriptPubKey =
        p2wsh (H (TwoOfTwoScriptBytes (n.toFundingParams H).localFundingKey
          (n.toFundingParams H).remoteFundingKey)) ∨
      (n.toFundingParams H).fundingScriptPubKey =
        p2wsh (H (TwoOfTwoScriptBytes (n.toFundingParams H).remoteFundingKey
          (n.toFundingParams H).localFundingKey)) :=
  fundingScriptPubKey_eq_p2wsh_twoOfTwo H _ (toFundingParams_hash_linked H n)

/-- The committed program itself is `H` of the ordered 2-of-2 bytes. -/
theorem witnessScriptHash_eq_hash_TwoOfTwo (H : ByteArray → ByteArray)
    (n : FundingNegotiation) :
    (n.toFundingParams H).witnessScriptHash =
      H (TwoOfTwoScriptBytes n.firstFundingKey n.secondFundingKey) := by
  rw [FundingNegotiation.toFundingParams_witnessScriptHash]
  rw [FundingNegotiation.toFundingParams_witnessScript]
  rw [witnessScript_bytes_eq_TwoOfTwoScriptBytes]

/-! ## Handshake-level form -/

/-- **`L1-03`, handshake form.**  A received `accept_channel` fixes the remote
funding key; together with the opener's local key it determines the witness
script, and the parameters built from it carry the hash link by construction.
The final conjunct is the existing `LN-L1-001` disjunction with the hash
hypothesis discharged. -/
theorem acceptChannel_funding_link (H : ByteArray → ByteArray)
    (m : AcceptChannel) (localFundingKey : PubKey)
    (fundingSatoshis : BtcAmount) (pushMsat : Msat)
    (temporaryChannelId : TemporaryChannelId) :
    let p := m.toFundingParams H localFundingKey fundingSatoshis pushMsat
      temporaryChannelId
    p.localFundingKey = localFundingKey ∧
      p.remoteFundingKey = m.fundingPubKey ∧
      p.witnessScriptHash = H p.witnessScript.bytes ∧
      (p.fundingScriptPubKey =
          p2wsh (H (TwoOfTwoScriptBytes p.localFundingKey
            p.remoteFundingKey)) ∨
        p.fundingScriptPubKey =
          p2wsh (H (TwoOfTwoScriptBytes p.remoteFundingKey
            p.localFundingKey))) := by
  dsimp only
  refine ⟨rfl, rfl, ?_, ?_⟩
  · exact toFundingParams_hash_linked H _
  · exact fundingScriptPubKey_eq_p2wsh_twoOfTwo_constructed H _

/-- Handshake form with `PrimitiveModel.sha256` and the width corollary. -/
theorem acceptChannel_funding_link_sha256 (M : PrimitiveModel)
    (m : AcceptChannel) (localFundingKey : PubKey)
    (fundingSatoshis : BtcAmount) (pushMsat : Msat)
    (temporaryChannelId : TemporaryChannelId) :
    let p := m.toFundingParams M.sha256 localFundingKey fundingSatoshis
      pushMsat temporaryChannelId
    p.remoteFundingKey = m.fundingPubKey ∧
      p.witnessScriptHash = M.sha256 p.witnessScript.bytes ∧
      p.witnessScriptHash.size = 32 := by
  dsimp only
  refine ⟨rfl, ?_, ?_⟩
  · exact toFundingParams_hash_linked_sha256 M _
  · exact toFundingParams_witnessScriptHash_size_sha256 M _

/-- Handshake form with the ordered key pair and no disjunction: the output is
P2WSH over exactly `TwoOfTwoScriptBytes first second`, where `first`/`second`
are the lexicographically ordered funding keys.  This is the strongest
handshake-level statement in this module. -/
theorem acceptChannel_funding_link_ordered (H : ByteArray → ByteArray)
    (m : AcceptChannel) (localFundingKey : PubKey)
    (fundingSatoshis : BtcAmount) (pushMsat : Msat)
    (temporaryChannelId : TemporaryChannelId) :
    let n := m.toFundingNegotiation localFundingKey fundingSatoshis pushMsat
      temporaryChannelId
    let p := n.toFundingParams H
    p.remoteFundingKey = m.fundingPubKey ∧
      p.witnessScriptHash =
        H (TwoOfTwoScriptBytes n.firstFundingKey n.secondFundingKey) ∧
      p.fundingScriptPubKey =
        p2wsh (H (TwoOfTwoScriptBytes n.firstFundingKey
          n.secondFundingKey)) := by
  dsimp only
  exact ⟨rfl, witnessScriptHash_eq_hash_TwoOfTwo H _,
    fundingScriptPubKey_eq_p2wsh_ordered H _⟩

/-! ## The L1 output and confirmed output -/

/-- The constructed L1 funding-output record commits to `H` of the witness
script. -/
theorem toFundingOutput_scriptPubKey_eq_p2wsh (H : ByteArray → ByteArray)
    (n : FundingNegotiation) (txid : ByteArray) (index : Nat) :
    ((n.toFundingParams H).toFundingOutput txid index).scriptPubKey =
      p2wsh (H (n.toFundingParams H).witnessScript.bytes) :=
  rfl

/-- A confirmed output of the constructed funding transaction has the exact
P2WSH byte shape `OP_0 <0x20> H(witnessScript.bytes)`.  No hash hypothesis:
the link is intrinsic to the construction. -/
theorem fundingConfirmed_script_commits_constructed
    (H : ByteArray → ByteArray) (n : FundingNegotiation)
    {tx : Tx} {index : Nat}
    (hc : FundingConfirmed (n.toFundingParams H) tx index) :
    ∃ out : TxOut,
      tx.vout[index]? = some out ∧
      out.scriptPubKey.bytes =
        (ByteArray.empty.push OP_0).push 0x20 ++
          H (n.toFundingParams H).witnessScript.bytes := by
  obtain ⟨out, hout, hscript⟩ := FundingConfirmed.script_eq hc
  refine ⟨out, hout, ?_⟩
  rw [hscript]
  rfl

/-- A confirmed constructed output commits to the ordered 2-of-2 script, in
byte form. -/
theorem fundingConfirmed_script_commits_TwoOfTwo
    (H : ByteArray → ByteArray) (n : FundingNegotiation)
    {tx : Tx} {index : Nat}
    (hc : FundingConfirmed (n.toFundingParams H) tx index) :
    ∃ out : TxOut,
      tx.vout[index]? = some out ∧
      out.scriptPubKey.bytes =
        (ByteArray.empty.push OP_0).push 0x20 ++
          H (TwoOfTwoScriptBytes n.firstFundingKey n.secondFundingKey) := by
  obtain ⟨out, hout, hbytes⟩ := fundingConfirmed_script_commits_constructed H n hc
  refine ⟨out, hout, ?_⟩
  rw [hbytes, FundingNegotiation.toFundingParams_witnessScript,
    witnessScript_bytes_eq_TwoOfTwoScriptBytes]

/-! ## Reverse binding: the finite C1 admission is kept -/

/-- **`L1-05`, constructed form.**  A script revealed against the constructed
funding output is the BOLT 3 2-of-2 witness script under the finite pair
admission `CollisionFreeOn`, exactly as in `FundingScriptTargets`.  The hash
link is no longer a hypothesis, but the cryptographic reverse direction still
is: this theorem does not assume global SHA-256 injectivity, and it does not
derive the admission from C1's 32-byte domain. -/
theorem constructed_binds_twoOfTwo (H : ByteArray → ByteArray)
    (n : FundingNegotiation) (hwf : (n.toFundingParams H).WellFormed)
    (revealed : ByteArray)
    (hrev : (n.toFundingParams H).fundingScriptPubKey = p2wsh (H revealed))
    (hc1 : CollisionFreeOn H revealed
      (n.toFundingParams H).witnessScript.bytes) :
    IsTwoOfTwoScript (n.toFundingParams H).localFundingKey
        (n.toFundingParams H).remoteFundingKey revealed ∧
      revealed.size = 71 :=
  fundingScriptPubKey_binds_twoOfTwo H _ hwf
    (toFundingParams_hash_linked H n) revealed hrev hc1

/-- Constructed form of the hash-level reverse binding. -/
theorem constructed_binds_witnessScript (H : ByteArray → ByteArray)
    (n : FundingNegotiation) (revealed : ByteArray)
    (hrev : (n.toFundingParams H).witnessScriptHash = H revealed)
    (hc1 : CollisionFreeOn H revealed
      (n.toFundingParams H).witnessScript.bytes) :
    revealed = (n.toFundingParams H).witnessScript.bytes :=
  fundingScriptHash_binds_witnessScript H _ (toFundingParams_hash_linked H n)
    revealed hrev hc1

/-- Two constructed parameter sets with equal output scripts commit to the
same witness script, under the finite pair admission. -/
theorem constructed_determine_witnessScript (H : ByteArray → ByteArray)
    (n m : FundingNegotiation)
    (heq : (n.toFundingParams H).fundingScriptPubKey =
      (m.toFundingParams H).fundingScriptPubKey)
    (hc1 : CollisionFreeOn H (n.toFundingParams H).witnessScript.bytes
      (m.toFundingParams H).witnessScript.bytes) :
    (n.toFundingParams H).witnessScript.bytes =
      (m.toFundingParams H).witnessScript.bytes :=
  fundingScriptPubKey_determines_witnessScript H _ _
    (toFundingParams_hash_linked H n) (toFundingParams_hash_linked H m)
    heq hc1

/-! ## Non-vacuity of the forward construction -/

private def key33 (b : UInt8) : ByteArray :=
  ByteArray.mk (List.replicate 33 b).toArray

private def pub33 (b : UInt8) : PubKey :=
  ⟨key33 b⟩

private theorem key33_size (b : UInt8) : (key33 b).size = 33 := by
  simp [key33, ByteArray.size]

private theorem pub33_valid (b : UInt8) : (pub33 b).Valid :=
  key33_size b

private def zeros32 : ByteArray :=
  ByteArray.mk (List.replicate 32 (0 : UInt8)).toArray

private theorem zeros32_size : zeros32.size = 32 := by
  simp [zeros32, ByteArray.size]

/-- The forward construction is satisfiable with a well-formed negotiation and
a 32-byte-output hash: the hash link, the width law, and `WellFormed` all hold
simultaneously.  The hash here is the constant zero function, which is enough
to refute vacuity of the construction itself; the reverse direction
additionally needs the pair admission, whose satisfiability is already
mechanized by `FundingScriptTargets.fundingScriptPair_assumptions_satisfiable`. -/
theorem constructed_forward_satisfiable :
    ∃ (H : ByteArray → ByteArray) (n : FundingNegotiation),
      (∀ b : ByteArray, (H b).size = 32) ∧
      (n.toFundingParams H).WellFormed ∧
      FundingScriptHashLinked H (n.toFundingParams H) := by
  let n : FundingNegotiation :=
    { fundingSatoshis := 0
      pushMsat := ⟨0⟩
      localFundingKey := pub33 0
      remoteFundingKey := pub33 0
      temporaryChannelId := ⟨⟨ByteArray.empty⟩⟩ }
  refine ⟨fun _ => zeros32, n, ?_, ?_, ?_⟩
  · intro _b
    exact zeros32_size
  · exact FundingNegotiation.toFundingParams_wellFormed (fun _ => zeros32)
      (fun _ => zeros32_size) n (by simp [n]) (by simp [n, Bitcoin.Data.MAX_MONEY,
        Bitcoin.Data.COIN]) (pub33_valid 0) (pub33_valid 0) (by simp [n])
  · exact toFundingParams_hash_linked (fun _ => zeros32) n

/-! ## What one handshake message does not determine -/

/-- A concrete `accept_channel` record.  Only `fundingPubKey` matters for the
funding script; the other fields are length-valid defaults, because no
well-formedness hypothesis is used by the non-determination result. -/
private def demoAccept (remote : PubKey) : AcceptChannel :=
  { temporaryChannelId := ⟨ByteArray.empty⟩
    dustLimitSatoshis := 0
    maxHtlcValueInFlightMsat := 0
    channelReserveSatoshis := 0
    htlcMinimumMsat := 0
    minimumDepth := 0
    toSelfDelay := 0
    maxAcceptedHtlcs := 0
    fundingPubKey := remote
    revocationBasepoint := remote
    paymentBasepoint := remote
    delayedPaymentBasepoint := remote
    htlcBasepoint := remote
    firstPerCommitmentPoint := remote }

/-- `getElem?` into the left summand of an append. -/
private theorem getElem?_append_lt (a b : ByteArray) (i : Nat) (h : i < a.size) :
    (a ++ b)[i]? = a[i]? := by
  rw [show (a ++ b)[i]? = (a ++ b).data[i]? from rfl,
      ByteArray.data_append, Array.getElem?_append,
      ite_eq_left (by simpa using h)]
  rw [show a[i]? = a.data[i]? from rfl]

/-- `getElem?` into the right summand of an append. -/
private theorem getElem?_append_ge (a b : ByteArray) (i : Nat) (h : a.size ≤ i) :
    (a ++ b)[i]? = b[i - a.size]? := by
  rw [show (a ++ b)[i]? = (a ++ b).data[i]? from rfl,
      ByteArray.data_append, Array.getElem?_append,
      ite_eq_right (by simpa using h)]
  rw [show b[i - a.size]? = b.data[i - a.size]? from rfl]
  rfl

/-- The first key of a constructed script starts at byte offset 2
(`OP_2`, push length, then the key). -/
private theorem ofKeys_getElem_two (a b : PubKey)
    (h : (orderedFundingKeys a b).1.bytes.size = 33) :
    (FundingScript.ofKeys a b).witnessScript.bytes[2]? =
      (orderedFundingKeys a b).1.bytes[0]? := by
  simp only [FundingScript.ofKeys]
  rw [getElem?_append_lt _ (ByteArray.empty.push OP_CHECKMULTISIG) 2
    (by simp [pushData, h] <;> omega)]
  rw [getElem?_append_lt _ (ByteArray.empty.push 0x52) 2
    (by simp [pushData, h] <;> omega)]
  rw [getElem?_append_lt _ (pushData (orderedFundingKeys a b).2.bytes) 2
    (by simp [pushData, h] <;> omega)]
  rw [getElem?_append_ge (ByteArray.empty.push 0x52) _ 2 (by simp)]
  show (pushData (orderedFundingKeys a b).1.bytes)[1]? = _
  simp only [pushData]
  rw [getElem?_append_ge
    (ByteArray.empty.push ((orderedFundingKeys a b).1.bytes.size).toUInt8) _ 1
    (by simp)]
  rfl

/-- The second key of a constructed (33-byte-key) script starts at byte offset
36: `OP_2`, push length, 33 key bytes, push length. -/
private theorem ofKeys_getElem_36 (a b : PubKey)
    (h1 : (orderedFundingKeys a b).1.bytes.size = 33)
    (h2 : 0 < (orderedFundingKeys a b).2.bytes.size) :
    (FundingScript.ofKeys a b).witnessScript.bytes[36]? =
      (orderedFundingKeys a b).2.bytes[0]? := by
  simp only [FundingScript.ofKeys]
  rw [getElem?_append_lt _ (ByteArray.empty.push OP_CHECKMULTISIG) 36
    (by simp [pushData, h1] <;> omega)]
  rw [getElem?_append_lt _ (ByteArray.empty.push 0x52) 36
    (by simp [pushData, h1] <;> omega)]
  rw [getElem?_append_ge
    (ByteArray.empty.push 0x52 ++ pushData (orderedFundingKeys a b).1.bytes) _ 36
    (by simp [pushData, h1])]
  have hsize :
      (ByteArray.empty.push 0x52 ++
        pushData (orderedFundingKeys a b).1.bytes).size = 35 := by
    simp [pushData, h1]
  rw [hsize]
  show (pushData (orderedFundingKeys a b).2.bytes)[1]? = _
  simp only [pushData]
  rw [getElem?_append_ge
    (ByteArray.empty.push ((orderedFundingKeys a b).2.bytes.size).toUInt8) _ 1
    (by simp)]
  rfl

private theorem key0_getElem_zero : (pub33 0).bytes[0]? = some 0 := by
  simp only [pub33, key33]
  decide

private theorem key1_getElem_zero : (pub33 1).bytes[0]? = some 1 := by
  simp only [pub33, key33]
  decide

/-- **Limit: `accept_channel` alone does not determine the witness script.**
The peer's `funding_pubkey` is one of the two keys; the script also needs the
opener's `open_channel` key, which is not a `Msg` field in this model.  One
`accept_channel` record is therefore compatible with distinct funding scripts,
so the handshake message is not by itself a function to the P2WSH program.
The local key is still supplied explicitly to `toFundingNegotiation`; what is
ruled out is pretending the message alone determines it. -/
theorem acceptChannel_alone_does_not_determine_witnessScript :
    ∃ (m : AcceptChannel) (k₁ k₂ : PubKey),
      (m.toFundingNegotiation k₁ 0 ⟨0⟩
          ⟨⟨ByteArray.empty⟩⟩).witnessScript.bytes ≠
        (m.toFundingNegotiation k₂ 0 ⟨0⟩
          ⟨⟨ByteArray.empty⟩⟩).witnessScript.bytes := by
  refine ⟨demoAccept (pub33 0), pub33 0, pub33 1, ?_⟩
  intro h
  have hsz (b : UInt8) : (pub33 b).bytes.size = 33 := by
    simp [pub33, key33, ByteArray.size]
  have hb0two :
      ((demoAccept (pub33 0)).toFundingNegotiation (pub33 0) 0 ⟨0⟩
          ⟨⟨ByteArray.empty⟩⟩).witnessScript.bytes[2]? = some 0 := by
    simp only [AcceptChannel.toFundingNegotiation,
      FundingNegotiation.witnessScript, demoAccept]
    rw [ofKeys_getElem_two _ _
      (by rw [LnLean.Proofs.Bitcoin.FundingProps.orderedFundingKeys_self]; exact hsz 0)]
    change (orderedFundingKeys (pub33 0) (pub33 0)).1.bytes[0]? = some 0
    rw [LnLean.Proofs.Bitcoin.FundingProps.orderedFundingKeys_self]
    exact key0_getElem_zero
  have hb0_36 :
      ((demoAccept (pub33 0)).toFundingNegotiation (pub33 0) 0 ⟨0⟩
          ⟨⟨ByteArray.empty⟩⟩).witnessScript.bytes[36]? = some 0 := by
    simp only [AcceptChannel.toFundingNegotiation,
      FundingNegotiation.witnessScript, demoAccept]
    rw [ofKeys_getElem_36 _ _
      (by rw [LnLean.Proofs.Bitcoin.FundingProps.orderedFundingKeys_self]; exact hsz 0)
      (by rw [LnLean.Proofs.Bitcoin.FundingProps.orderedFundingKeys_self]; rw [hsz 0]; omega)]
    change (orderedFundingKeys (pub33 0) (pub33 0)).2.bytes[0]? = some 0
    rw [LnLean.Proofs.Bitcoin.FundingProps.orderedFundingKeys_self]
    exact key0_getElem_zero
  rcases LnLean.Proofs.Bitcoin.FundingProps.orderedFundingKeys_pair (pub33 1) (pub33 0) with
    hord | hord
  · have hb1two :
        ((demoAccept (pub33 0)).toFundingNegotiation (pub33 1) 0 ⟨0⟩
            ⟨⟨ByteArray.empty⟩⟩).witnessScript.bytes[2]? = some 1 := by
      simp only [AcceptChannel.toFundingNegotiation,
        FundingNegotiation.witnessScript, demoAccept]
      rw [ofKeys_getElem_two _ _ (by rw [hord]; exact hsz 1)]
      change (orderedFundingKeys (pub33 1) (pub33 0)).1.bytes[0]? = some 1
      rw [hord]
      exact key1_getElem_zero
    have hEq := congrArg (fun x : ByteArray => x[2]?) h
    rw [hb0two, hb1two] at hEq
    exact absurd (Option.some.inj hEq) (by decide)
  · have hb1_36 :
        ((demoAccept (pub33 0)).toFundingNegotiation (pub33 1) 0 ⟨0⟩
            ⟨⟨ByteArray.empty⟩⟩).witnessScript.bytes[36]? = some 1 := by
      simp only [AcceptChannel.toFundingNegotiation,
        FundingNegotiation.witnessScript, demoAccept]
      rw [ofKeys_getElem_36 _ _
        (by rw [hord]; exact hsz 1)
        (by rw [hord]; change 0 < (pub33 1).bytes.size; rw [hsz 1]; omega)]
      change (orderedFundingKeys (pub33 1) (pub33 0)).2.bytes[0]? = some 1
      rw [hord]
      exact key1_getElem_zero
    have hEq := congrArg (fun x : ByteArray => x[36]?) h
    rw [hb0_36, hb1_36] at hEq
    exact absurd (Option.some.inj hEq) (by decide)

end LnLean.Proofs.Bitcoin.FundingLinkTargets
