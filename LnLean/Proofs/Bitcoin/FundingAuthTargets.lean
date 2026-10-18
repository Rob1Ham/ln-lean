import LnLean.Protocol.Handshake
import LnLean.Proofs.Bitcoin.FundingLinkTargets
import LnLean.Crypto.Model

/-!
# `open_channel` coverage and funding-key authentication (`L1-03`)

**English claim.**  BOLT 2 fixes the funding output during channel
establishment v1: the opener's `open_channel` supplies `funding_satoshis`,
`push_msat`, a temporary channel id, and its `funding_pubkey`; the acceptor's
`accept_channel` supplies the second `funding_pubkey`; and the funding output
is the BOLT 3 P2WSH of

`OP_2 <pubkey1> <pubkey2> OP_2 OP_CHECKMULTISIG`

with the keys in lexicographic order.  `LnLean.Proofs.Bitcoin.FundingLinkTargets`
proved that construction from `accept_channel` plus opener-side local values,
and left two gaps:

1. no `open_channel` message coverage — the opener's funding fields were
   explicit arguments, so the handshake message set did not determine the
   witness script (`acceptChannel_alone_does_not_determine_witnessScript`);
2. no funding-key authentication — `accept_channel.funding_pubkey` was only a
   claimed key, with no statement about what an output check binds.

This module closes (1) at the funding layer and proves the strongest faithful
statement for (2).

## What is constructed

`LnLean.Protocol.Handshake` (this lane's owned module) adds the additive
`OpenChannel` record, `OpenChannel.toFundingNegotiation`, and a separate
`FundingPhase`/`fundingStep` machine for the four funding messages.  The
existing ten-milestone `HandshakeState`, `HandshakeEvent`, and `handshakeStep`
are untouched.  The joint construction is definitionally the accept-only
construction with the opener's fields filled in:

`o.toFundingNegotiation a = a.toFundingNegotiation o.fundingPubKey o.fundingSatoshis o.pushMsat ⟨o.temporaryChannelId⟩`

so `openAccept_toFundingParams_eq_acceptChannel` shows the old hash link is
**not weakened** — it is the same `FundingNegotiation.toFundingParams`.

## Key authentication: what is proved

The construction does not contain a signature check, so no theorem can
conclude that a peer *owns* a key (that is `PR-01`/C3 and the secret-key model,
not `L1-03`).  The strongest structural statement that is actually true is:

* `openAccept_output_determines_key_set` — if two complete
  `open_channel`/`accept_channel` exchanges produce the **same funding output**
  and the abstract hash `H` is collision-free on the two witness scripts, then
  the two exchanges agreed on the **unordered funding-key set**.  Checking the
  output therefore detects any substitution of either funding key.  This is
  the operational meaning of funding-key authentication at the construction
  layer.
* `openAccept_both_keys_in_script` — both advertised keys occur literally in
  the 71-byte witness script, so a change of either key changes the script
  bytes and hence (through `H`) the output.
* `attributed_key_in_script` — if a transport attribution hypothesis identifies
  the sender's key with `open_channel.funding_pubkey`, then that authenticated
  key is the local key of the script and occurs in the script bytes.
* `same_message_distinct_senders` — mechanizes the scope boundary: an
  `OpenChannel` record carries no sender identity, so the record alone does not
  authenticate a peer.  Attribution has to come from the transport.

## The finite C1 admission is retained

The reverse direction is still cryptographic.  `openAccept_output_determines_key_set`
takes exactly `CollisionFreeOn H x y := H x = H y → x = y` at the two
constructed witness scripts.  It does **not** assume global SHA-256
injectivity, and it does not derive the 71-byte admission from C1's 32-byte
payment-preimage domain; `FundingScriptTargets.c1_32_does_not_bind_funding_witnessScripts`
remains the binding counterexample.

## What the output does not bind

`funding_output_ignores_fundingSatoshis`, `..._pushMsat`, and
`..._temporaryChannelId` show that the funding output commits only to the key
set.  Capacity, push amount, and the temporary channel id must be authenticated
by the messages or by the transport, not by the output script.  Together with
`same_message_distinct_senders` these are the honest limits of this layer.

## Anchors

* BOLT 2 §The `open_channel` Message (type 32): `temporary_channel_id`,
  `funding_satoshis`, `push_msat`, `funding_pubkey`.
* BOLT 2 §The `accept_channel` Message (type 33): `funding_pubkey`.
* BOLT 3 §Funding Transaction Output: P2WSH over
  `2 <pubkey1> <pubkey2> 2 OP_CHECKMULTISIG`, keys in lexicographic order.
* `refs/rust-lightning/lightning/src/ln/chan_utils.rs:847-866`
  (`make_funding_redeemscript`, key ordering).
-/

namespace LnLean.Proofs.Bitcoin.FundingAuthTargets

set_option autoImplicit false

open LnLean
open LnLean.Bitcoin
open LnLean.Protocol
open LnLean.Crypto
open LnLean.Proofs.Bitcoin.FundingScriptTargets
open LnLean.Proofs.Bitcoin.FundingLinkTargets

/-! ## The witness script determines its ordered key pair -/

/-- **Structural key injectivity of the BOLT 3 script.**  For 33-byte
compressed keys, equal witness-script bytes force equal *ordered* key pairs.
This is a serialization fact, not a cryptographic assumption: the two keys sit
at fixed byte offsets 2..34 and 36..68 of the 71-byte script. -/
theorem twoOfTwoScriptBytes_injective {a b c d : PubKey}
    (ha : a.bytes.size = 33) (hb : b.bytes.size = 33)
    (hc : c.bytes.size = 33) (hd : d.bytes.size = 33)
    (h : TwoOfTwoScriptBytes a b = TwoOfTwoScriptBytes c d) :
    a = c ∧ b = d := by
  have h3 : a.bytes.data.toList ++ (0x21 :: (b.bytes.data.toList ++ [0x52, 0xAE]))
      = c.bytes.data.toList ++ (0x21 :: (d.bytes.data.toList ++ [0x52, 0xAE])) := by
    simpa [TwoOfTwoScriptBytes, pushData, ha, hb, hc, hd,
      Array.toList_append, List.cons_append, OP_CHECKMULTISIG] using
      congrArg (fun x : ByteArray => x.data.toList) h
  have halen : a.bytes.data.toList.length = c.bytes.data.toList.length := by
    have : a.bytes.data.size = c.bytes.data.size := ha.trans hc.symm
    simpa using this
  obtain ⟨haeq, hrest⟩ := List.append_inj h3 halen
  have hab : a.bytes = c.bytes := ByteArray.ext (Array.toList_inj.mp haeq)
  have h5 : b.bytes.data.toList ++ [0x52, 0xAE]
      = d.bytes.data.toList ++ [0x52, 0xAE] := (List.cons.inj hrest).2
  have hblen : b.bytes.data.toList.length = d.bytes.data.toList.length := by
    have : b.bytes.data.size = d.bytes.data.size := hb.trans hd.symm
    simpa using this
  obtain ⟨hbeq, _⟩ := List.append_inj h5 hblen
  have hbb : b.bytes = d.bytes := ByteArray.ext (Array.toList_inj.mp hbeq)
  have hac : a = c := by cases a; cases c; simp_all
  have hbd : b = d := by cases b; cases d; simp_all
  exact ⟨hac, hbd⟩

/-- A key is one of the two ordered funding keys. -/
theorem key_mem_ordered (k l : PubKey) :
    k = (orderedFundingKeys k l).1 ∨ k = (orderedFundingKeys k l).2 := by
  rcases LnLean.Proofs.Bitcoin.FundingProps.orderedFundingKeys_pair k l with h | h <;>
    rw [h] <;> simp

/-- Equal ordered key pairs mean the two unordered key sets agree: either the
two endpoints kept their roles, or they swapped roles. -/
theorem key_set_eq_of_ordered_eq {o₁ a₁ o₂ a₂ : PubKey}
    (h : orderedFundingKeys o₁ a₁ = orderedFundingKeys o₂ a₂) :
    (o₁ = o₂ ∧ a₁ = a₂) ∨ (o₁ = a₂ ∧ a₁ = o₂) := by
  rcases LnLean.Proofs.Bitcoin.FundingProps.orderedFundingKeys_pair o₁ a₁ with hp₁ | hp₁ <;>
  rcases LnLean.Proofs.Bitcoin.FundingProps.orderedFundingKeys_pair o₂ a₂ with hp₂ | hp₂ <;>
  rw [hp₁, hp₂] at h <;>
  simp_all

/-! ## Both keys occur literally in the witness script -/

/-- A key's bytes occur as a contiguous window of a byte string.  This is the
syntactic form of "the script commits to this key". -/
def KeyInScript (s : ByteArray) (k : PubKey) : Prop :=
  ∃ pre post : ByteArray, s = pre ++ k.bytes ++ post

/-- The first key occurs in the BOLT 3 template. -/
theorem twoOfTwoScriptBytes_keyInScript_first (a b : PubKey) :
    KeyInScript (TwoOfTwoScriptBytes a b) a := by
  refine ⟨ByteArray.empty.push 0x52 ++
      ByteArray.empty.push a.bytes.size.toUInt8,
    ByteArray.empty.push b.bytes.size.toUInt8 ++ b.bytes ++
      ByteArray.empty.push 0x52 ++ ByteArray.empty.push OP_CHECKMULTISIG, ?_⟩
  simp [TwoOfTwoScriptBytes, pushData, ByteArray.append_assoc]

/-- The second key occurs in the BOLT 3 template. -/
theorem twoOfTwoScriptBytes_keyInScript_second (a b : PubKey) :
    KeyInScript (TwoOfTwoScriptBytes a b) b := by
  refine ⟨ByteArray.empty.push 0x52 ++
      ByteArray.empty.push a.bytes.size.toUInt8 ++ a.bytes ++
      ByteArray.empty.push b.bytes.size.toUInt8,
    ByteArray.empty.push 0x52 ++ ByteArray.empty.push OP_CHECKMULTISIG, ?_⟩
  simp [TwoOfTwoScriptBytes, pushData, ByteArray.append_assoc]

/-- **Both funding keys are committed by the witness script.**  The ordered
script contains both ordered keys; the pair lemma identifies which one is the
opener's and which one is the acceptor's. -/
theorem openAccept_both_keys_in_script (H : ByteArray → ByteArray)
    (o : OpenChannel) (a : AcceptChannel) :
    KeyInScript (o.toFundingParams H a).witnessScript.bytes o.fundingPubKey ∧
      KeyInScript (o.toFundingParams H a).witnessScript.bytes a.fundingPubKey := by
  have hscript : (o.toFundingParams H a).witnessScript.bytes =
      TwoOfTwoScriptBytes (o.toFundingNegotiation a).firstFundingKey
        (o.toFundingNegotiation a).secondFundingKey :=
    witnessScript_bytes_eq_TwoOfTwoScriptBytes _
  rcases LnLean.Proofs.Bitcoin.FundingProps.orderedFundingKeys_pair
    o.fundingPubKey a.fundingPubKey with hp | hp
  · have hf : (o.toFundingNegotiation a).firstFundingKey = o.fundingPubKey := by
      rw [FundingNegotiation.firstFundingKey]
      change (orderedFundingKeys o.fundingPubKey a.fundingPubKey).1 = o.fundingPubKey
      rw [hp]
    have hs : (o.toFundingNegotiation a).secondFundingKey = a.fundingPubKey := by
      rw [FundingNegotiation.secondFundingKey]
      change (orderedFundingKeys o.fundingPubKey a.fundingPubKey).2 = a.fundingPubKey
      rw [hp]
    constructor
    · rw [hscript, hf, hs]
      exact twoOfTwoScriptBytes_keyInScript_first _ _
    · rw [hscript, hf, hs]
      exact twoOfTwoScriptBytes_keyInScript_second _ _
  · have hf : (o.toFundingNegotiation a).firstFundingKey = a.fundingPubKey := by
      rw [FundingNegotiation.firstFundingKey]
      change (orderedFundingKeys o.fundingPubKey a.fundingPubKey).1 = a.fundingPubKey
      rw [hp]
    have hs : (o.toFundingNegotiation a).secondFundingKey = o.fundingPubKey := by
      rw [FundingNegotiation.secondFundingKey]
      change (orderedFundingKeys o.fundingPubKey a.fundingPubKey).2 = o.fundingPubKey
      rw [hp]
    constructor
    · rw [hscript, hf, hs]
      exact twoOfTwoScriptBytes_keyInScript_second _ _
    · rw [hscript, hf, hs]
      exact twoOfTwoScriptBytes_keyInScript_first _ _

/-! ## The joint `open_channel`/`accept_channel` construction -/

/-- **No weakening of the existing construction.**  The joint negotiation is
definitionally the accept-only `FundingNegotiation` with the opener's fields
supplied from `open_channel`.  Every `FundingLinkTargets` theorem therefore
applies to the joint construction unchanged. -/
theorem openAccept_toFundingParams_eq_acceptChannel
    (H : ByteArray → ByteArray) (o : OpenChannel) (a : AcceptChannel) :
    o.toFundingParams H a =
      a.toFundingParams H o.fundingPubKey o.fundingSatoshis o.pushMsat
        ⟨o.temporaryChannelId⟩ := rfl

/-- The joint construction's program is the hash of the BOLT 3 witness script,
by construction (no hash hypothesis). -/
theorem openAccept_hash_linked (H : ByteArray → ByteArray)
    (o : OpenChannel) (a : AcceptChannel) :
    FundingScriptHashLinked H (o.toFundingParams H a) :=
  FundingNegotiation.toFundingParams_witnessScriptHash H _

/-- **`L1-03`, ordered joint form.**  The funding output of a complete
`open_channel`/`accept_channel` exchange is the P2WSH of exactly the ordered
BOLT 3 2-of-2 script.  No disjunction, no hash hypothesis. -/
theorem openAccept_fundingScriptPubKey_eq_p2wsh_ordered
    (H : ByteArray → ByteArray) (o : OpenChannel) (a : AcceptChannel) :
    (o.toFundingParams H a).fundingScriptPubKey =
      p2wsh (H (TwoOfTwoScriptBytes (o.toFundingNegotiation a).firstFundingKey
        (o.toFundingNegotiation a).secondFundingKey)) := by
  change p2wsh (H (o.toFundingParams H a).witnessScript.bytes) =
    p2wsh (H (TwoOfTwoScriptBytes (o.toFundingNegotiation a).firstFundingKey
      (o.toFundingNegotiation a).secondFundingKey))
  rw [show (o.toFundingParams H a).witnessScript =
      (o.toFundingNegotiation a).witnessScript from rfl]
  rw [witnessScript_bytes_eq_TwoOfTwoScriptBytes]

/-- The joint construction's committed program is the hash of the ordered
2-of-2 bytes. -/
theorem openAccept_witnessScriptHash_eq_hash_TwoOfTwo
    (H : ByteArray → ByteArray) (o : OpenChannel) (a : AcceptChannel) :
    (o.toFundingParams H a).witnessScriptHash =
      H (TwoOfTwoScriptBytes (o.toFundingNegotiation a).firstFundingKey
        (o.toFundingNegotiation a).secondFundingKey) := by
  change H (o.toFundingParams H a).witnessScript.bytes =
    H (TwoOfTwoScriptBytes (o.toFundingNegotiation a).firstFundingKey
      (o.toFundingNegotiation a).secondFundingKey)
  rw [show (o.toFundingParams H a).witnessScript =
      (o.toFundingNegotiation a).witnessScript from rfl]
  rw [witnessScript_bytes_eq_TwoOfTwoScriptBytes]

/-- The SHA-256 instance of the joint construction, with the 32-byte width
law.  `M.sha256` is the model's opaque interface, not verified FIPS 180-4. -/
theorem openAccept_hash_linked_sha256 (M : PrimitiveModel)
    (o : OpenChannel) (a : AcceptChannel) :
    FundingScriptHashLinked M.sha256 (o.toFundingParams M.sha256 a) ∧
      (o.toFundingParams M.sha256 a).witnessScriptHash.size = 32 :=
  ⟨openAccept_hash_linked M.sha256 o a,
    FundingNegotiation.toFundingParams_witnessScriptHash_size M.sha256
      M.sha256_size _⟩

/-- The joint construction is well formed whenever the opener's value bounds
and both key widths hold. -/
theorem openAccept_wellFormed (H : ByteArray → ByteArray)
    (hH : ∀ b : ByteArray, (H b).size = 32) (o : OpenChannel)
    (a : AcceptChannel)
    (hsat0 : 0 ≤ o.fundingSatoshis)
    (hsatMax : o.fundingSatoshis ≤ Bitcoin.Data.MAX_MONEY)
    (hlocal : o.fundingPubKey.Valid)
    (hremote : a.fundingPubKey.Valid)
    (hpush : (o.pushMsat.val : Int) ≤
      o.fundingSatoshis * (Msat.MSAT_PER_SAT : Int)) :
    (o.toFundingParams H a).WellFormed :=
  FundingNegotiation.toFundingParams_wellFormed H hH _
    hsat0 hsatMax hlocal hremote hpush

/-! ## Funding-key authentication: the output determines the key set -/

/-- **Ordered-pair binding.**  Equal funding outputs plus the finite admission
force the two exchanges to have the same *ordered* key pair.  This is the
common core of `openAccept_output_determines_key_set`; it is stated separately
because the byte-level script injectivity result is reusable. -/
theorem openAccept_output_determines_ordered_keys
    (H : ByteArray → ByteArray)
    (o₁ : OpenChannel) (a₁ : AcceptChannel)
    (o₂ : OpenChannel) (a₂ : AcceptChannel)
    (hwf₁ : (o₁.toFundingParams H a₁).WellFormed)
    (hwf₂ : (o₂.toFundingParams H a₂).WellFormed)
    (heq : (o₁.toFundingParams H a₁).fundingScriptPubKey =
      (o₂.toFundingParams H a₂).fundingScriptPubKey)
    (hc1 : CollisionFreeOn H
      (o₁.toFundingParams H a₁).witnessScript.bytes
      (o₂.toFundingParams H a₂).witnessScript.bytes) :
    orderedFundingKeys o₁.fundingPubKey a₁.fundingPubKey =
      orderedFundingKeys o₂.fundingPubKey a₂.fundingPubKey := by
  have heq' : p2wsh (H (o₁.toFundingNegotiation a₁).witnessScript.bytes) =
      p2wsh (H (o₂.toFundingNegotiation a₂).witnessScript.bytes) := by
    simpa [FundingParams.fundingScriptPubKey,
      LnLean.Bitcoin.fundingScriptPubKey, OpenChannel.toFundingParams,
      FundingNegotiation.toFundingParams] using heq
  have hprog : H (o₁.toFundingParams H a₁).witnessScript.bytes =
      H (o₂.toFundingParams H a₂).witnessScript.bytes := by
    simpa [OpenChannel.toFundingParams,
      FundingNegotiation.toFundingParams_witnessScript] using p2wsh_injective heq' 
  have hs : (o₁.toFundingParams H a₁).witnessScript.bytes =
      (o₂.toFundingParams H a₂).witnessScript.bytes := hc1 hprog
  have ho₁ : o₁.fundingPubKey.bytes.size = 33 := by
    simpa [PubKey.Valid, OpenChannel.toFundingParams,
      OpenChannel.toFundingNegotiation] using hwf₁.2.2.1
  have ha₁ : a₁.fundingPubKey.bytes.size = 33 := by
    simpa [PubKey.Valid, OpenChannel.toFundingParams,
      OpenChannel.toFundingNegotiation] using hwf₁.2.2.2.1
  have ho₂ : o₂.fundingPubKey.bytes.size = 33 := by
    simpa [PubKey.Valid, OpenChannel.toFundingParams,
      OpenChannel.toFundingNegotiation] using hwf₂.2.2.1
  have ha₂ : a₂.fundingPubKey.bytes.size = 33 := by
    simpa [PubKey.Valid, OpenChannel.toFundingParams,
      OpenChannel.toFundingNegotiation] using hwf₂.2.2.2.1
  have hf₁ : (o₁.toFundingNegotiation a₁).firstFundingKey.bytes.size = 33 := by
    rw [FundingNegotiation.firstFundingKey]
    change (orderedFundingKeys o₁.fundingPubKey a₁.fundingPubKey).1.bytes.size = 33
    rcases LnLean.Proofs.Bitcoin.FundingProps.orderedFundingKeys_pair
      o₁.fundingPubKey a₁.fundingPubKey with h | h <;> rw [h]
    · exact ho₁
    · exact ha₁
  have hs₁ : (o₁.toFundingNegotiation a₁).secondFundingKey.bytes.size = 33 := by
    rw [FundingNegotiation.secondFundingKey]
    change (orderedFundingKeys o₁.fundingPubKey a₁.fundingPubKey).2.bytes.size = 33
    rcases LnLean.Proofs.Bitcoin.FundingProps.orderedFundingKeys_pair
      o₁.fundingPubKey a₁.fundingPubKey with h | h <;> rw [h]
    · exact ha₁
    · exact ho₁
  have hf₂ : (o₂.toFundingNegotiation a₂).firstFundingKey.bytes.size = 33 := by
    rw [FundingNegotiation.firstFundingKey]
    change (orderedFundingKeys o₂.fundingPubKey a₂.fundingPubKey).1.bytes.size = 33
    rcases LnLean.Proofs.Bitcoin.FundingProps.orderedFundingKeys_pair
      o₂.fundingPubKey a₂.fundingPubKey with h | h <;> rw [h]
    · exact ho₂
    · exact ha₂
  have hs₂ : (o₂.toFundingNegotiation a₂).secondFundingKey.bytes.size = 33 := by
    rw [FundingNegotiation.secondFundingKey]
    change (orderedFundingKeys o₂.fundingPubKey a₂.fundingPubKey).2.bytes.size = 33
    rcases LnLean.Proofs.Bitcoin.FundingProps.orderedFundingKeys_pair
      o₂.fundingPubKey a₂.fundingPubKey with h | h <;> rw [h]
    · exact ha₂
    · exact ho₂
  have hs' : (o₁.toFundingNegotiation a₁).witnessScript.bytes =
      (o₂.toFundingNegotiation a₂).witnessScript.bytes := by
    simpa [OpenChannel.toFundingParams, OpenChannel.toFundingNegotiation] using hs
  have hscript : TwoOfTwoScriptBytes (o₁.toFundingNegotiation a₁).firstFundingKey
        (o₁.toFundingNegotiation a₁).secondFundingKey =
      TwoOfTwoScriptBytes (o₂.toFundingNegotiation a₂).firstFundingKey
        (o₂.toFundingNegotiation a₂).secondFundingKey := by
    rw [witnessScript_bytes_eq_TwoOfTwoScriptBytes (o₁.toFundingNegotiation a₁),
      witnessScript_bytes_eq_TwoOfTwoScriptBytes (o₂.toFundingNegotiation a₂)] at hs'
    exact hs'
  obtain ⟨hf, hsnd⟩ :=
    twoOfTwoScriptBytes_injective hf₁ hs₁ hf₂ hs₂ hscript
  change orderedFundingKeys (o₁.toFundingNegotiation a₁).localFundingKey
      (o₁.toFundingNegotiation a₁).remoteFundingKey =
    orderedFundingKeys (o₂.toFundingNegotiation a₂).localFundingKey
      (o₂.toFundingNegotiation a₂).remoteFundingKey
  rw [FundingNegotiation.firstFundingKey_pair (o₁.toFundingNegotiation a₁),
    FundingNegotiation.firstFundingKey_pair (o₂.toFundingNegotiation a₂)]
  exact Prod.ext hf hsnd

/-- **`L1-03`, authentication result.**  Two complete funding exchanges that
produce the same funding output, under the finite pair-level collision-free
admission on `H`, agree on the unordered funding-key set.

Operationally: a party that compares the funding output with the one it
derived from the two messages detects any substitution of either funding key.
The conclusion is the *key set*, not an identity: binding a key to a peer still
needs transport attribution (see `attributed_key_in_script` and
`same_message_distinct_senders`). -/
theorem openAccept_output_determines_key_set
    (H : ByteArray → ByteArray)
    (o₁ : OpenChannel) (a₁ : AcceptChannel)
    (o₂ : OpenChannel) (a₂ : AcceptChannel)
    (hwf₁ : (o₁.toFundingParams H a₁).WellFormed)
    (hwf₂ : (o₂.toFundingParams H a₂).WellFormed)
    (heq : (o₁.toFundingParams H a₁).fundingScriptPubKey =
      (o₂.toFundingParams H a₂).fundingScriptPubKey)
    (hc1 : CollisionFreeOn H
      (o₁.toFundingParams H a₁).witnessScript.bytes
      (o₂.toFundingParams H a₂).witnessScript.bytes) :
    (o₁.fundingPubKey = o₂.fundingPubKey ∧
        a₁.fundingPubKey = a₂.fundingPubKey) ∨
      (o₁.fundingPubKey = a₂.fundingPubKey ∧
        a₁.fundingPubKey = o₂.fundingPubKey) :=
  key_set_eq_of_ordered_eq
    (openAccept_output_determines_ordered_keys H o₁ a₁ o₂ a₂ hwf₁ hwf₂ heq hc1)

/-- The same authentication result with the model's SHA-256 instance. -/
theorem openAccept_output_determines_key_set_sha256 (M : PrimitiveModel)
    (o₁ : OpenChannel) (a₁ : AcceptChannel)
    (o₂ : OpenChannel) (a₂ : AcceptChannel)
    (hwf₁ : (o₁.toFundingParams M.sha256 a₁).WellFormed)
    (hwf₂ : (o₂.toFundingParams M.sha256 a₂).WellFormed)
    (heq : (o₁.toFundingParams M.sha256 a₁).fundingScriptPubKey =
      (o₂.toFundingParams M.sha256 a₂).fundingScriptPubKey)
    (hc1 : CollisionFreeOn M.sha256
      (o₁.toFundingParams M.sha256 a₁).witnessScript.bytes
      (o₂.toFundingParams M.sha256 a₂).witnessScript.bytes) :
    (o₁.fundingPubKey = o₂.fundingPubKey ∧
        a₁.fundingPubKey = a₂.fundingPubKey) ∨
      (o₁.fundingPubKey = a₂.fundingPubKey ∧
        a₁.fundingPubKey = o₂.fundingPubKey) :=
  openAccept_output_determines_key_set M.sha256 o₁ a₁ o₂ a₂ hwf₁ hwf₂ heq hc1

/-! ## Transport attribution: what a key check does and does not give -/

/-- The transport-visible identity of a peer, represented by the public key the
Noise session authenticates.  This is a *model* of the identity, not a proved
Noise property (`docs/ASSUMPTIONS.md` §3). -/
structure PeerIdentity where
  key : PubKey

/-- A received `open_channel` with the transport's claimed sender.  The sender
is not a field of `OpenChannel`: it is attached by the receiving transport,
which is exactly the layer that has to authenticate it. -/
structure ReceivedOpen where
  sender : PeerIdentity
  message : OpenChannel

/-- The transport attribution hypothesis: the authenticated peer key is the
funding key the opener advertised.  This is the explicit input the construction
cannot supply (C3/Noise/key ownership is `PR-01`). -/
def OpenChannelAttributed (sender : PeerIdentity) (o : OpenChannel) : Prop :=
  sender.key = o.fundingPubKey

/-- **Conditional key authentication.**  Under transport attribution, the
authenticated peer key is literally the local funding key of the joint
construction and occurs in the witness script.  No other hypothesis is used. -/
theorem attributed_key_in_script (H : ByteArray → ByteArray)
    (sender : PeerIdentity) (o : OpenChannel) (a : AcceptChannel)
    (hattr : OpenChannelAttributed sender o) :
    sender.key = (o.toFundingNegotiation a).localFundingKey ∧
      KeyInScript (o.toFundingParams H a).witnessScript.bytes sender.key := by
  constructor
  · rw [hattr]
    rfl
  · rw [hattr]
    exact (openAccept_both_keys_in_script H o a).1

/-- The same authenticated key appears in the committed program: the output is
`p2wsh (H script)` and the script contains the key bytes. -/
theorem attributed_key_committed (H : ByteArray → ByteArray)
    (sender : PeerIdentity) (o : OpenChannel) (a : AcceptChannel)
    (hattr : OpenChannelAttributed sender o) :
    (o.toFundingParams H a).fundingScriptPubKey =
        p2wsh (H (o.toFundingParams H a).witnessScript.bytes) ∧
      KeyInScript (o.toFundingParams H a).witnessScript.bytes sender.key :=
  ⟨FundingNegotiation.toFundingParams_fundingScriptPubKey H _,
    attributed_key_in_script H sender o a hattr |>.2⟩

/-- **Scope boundary, mechanized.**  One `open_channel` record can be paired
with two distinct transport sender identities: the message type carries no
sender field, so nothing about the record determines the peer.  This is why
`attributed_key_in_script` takes attribution as an explicit hypothesis. -/
theorem same_message_distinct_senders :
    ∃ r₁ r₂ : ReceivedOpen,
      r₁.message = r₂.message ∧ r₁.sender ≠ r₂.sender := by
  let k₀ : PubKey := ⟨ByteArray.empty⟩
  let k₁ : PubKey := ⟨ByteArray.empty.push 0x01⟩
  let o : OpenChannel :=
    { temporaryChannelId := ⟨ByteArray.empty⟩
      fundingSatoshis := 0
      pushMsat := ⟨0⟩
      fundingPubKey := k₀ }
  refine ⟨⟨⟨k₀⟩, o⟩, ⟨⟨k₁⟩, o⟩, rfl, ?_⟩
  intro h
  have hk : k₀ = k₁ := congrArg PeerIdentity.key h
  have hb : (ByteArray.empty : ByteArray) = ByteArray.empty.push 0x01 :=
    congrArg PubKey.bytes hk
  have hsz := congrArg ByteArray.size hb
  simp at hsz

/-! ## Widths of the ordered keys -/

/-- The first serialized key is one of the two inputs, so it keeps their
33-byte width. -/
theorem firstFundingKey_size {n : LnLean.Bitcoin.FundingNegotiation}
    (hl : n.localFundingKey.bytes.size = 33)
    (hr : n.remoteFundingKey.bytes.size = 33) :
    n.firstFundingKey.bytes.size = 33 := by
  rw [LnLean.Bitcoin.FundingNegotiation.firstFundingKey]
  rcases LnLean.Proofs.Bitcoin.FundingProps.orderedFundingKeys_pair
    n.localFundingKey n.remoteFundingKey with h | h <;> rw [h]
  · exact hl
  · exact hr

/-- The second serialized key keeps the 33-byte width. -/
theorem secondFundingKey_size {n : LnLean.Bitcoin.FundingNegotiation}
    (hl : n.localFundingKey.bytes.size = 33)
    (hr : n.remoteFundingKey.bytes.size = 33) :
    n.secondFundingKey.bytes.size = 33 := by
  rw [LnLean.Bitcoin.FundingNegotiation.secondFundingKey]
  rcases LnLean.Proofs.Bitcoin.FundingProps.orderedFundingKeys_pair
    n.localFundingKey n.remoteFundingKey with h | h <;> rw [h]
  · exact hr
  · exact hl

/-! ## What the funding output does not commit to -/

/-- The output script ignores the channel value: `funding_satoshis` is not part
of the BOLT 3 witness script.  Capacity therefore has to be authenticated by
the messages or the funding transaction, not by the P2WSH output. -/
theorem funding_output_ignores_fundingSatoshis
    (H : ByteArray → ByteArray) (o : OpenChannel) (a : AcceptChannel)
    (v : BtcAmount) :
    (({ o with fundingSatoshis := v }).toFundingParams H a).fundingScriptPubKey =
      (o.toFundingParams H a).fundingScriptPubKey := rfl

/-- The output script ignores `push_msat`. -/
theorem funding_output_ignores_pushMsat
    (H : ByteArray → ByteArray) (o : OpenChannel) (a : AcceptChannel)
    (p : Msat) :
    (({ o with pushMsat := p }).toFundingParams H a).fundingScriptPubKey =
      (o.toFundingParams H a).fundingScriptPubKey := rfl

/-- The output script ignores the temporary channel id; it commits only to the
funding keys. -/
theorem funding_output_ignores_temporaryChannelId
    (H : ByteArray → ByteArray) (o : OpenChannel) (a : AcceptChannel)
    (c : ChannelId) :
    (({ o with temporaryChannelId := c }).toFundingParams H a).fundingScriptPubKey =
      (o.toFundingParams H a).fundingScriptPubKey := rfl

/-! ## Non-vacuity of the joint forward construction -/

private def key33 (b : UInt8) : ByteArray :=
  ByteArray.mk (List.replicate 33 b).toArray

private def pub33 (b : UInt8) : PubKey :=
  ⟨key33 b⟩

private theorem key33_size (b : UInt8) : (key33 b).size = 33 := by
  simp [key33, ByteArray.size]

private theorem pub33_valid (b : UInt8) : (pub33 b).Valid :=
  key33_size b

private theorem key0_getElem_zero : (pub33 0).bytes[0]? = some 0 := by
  simp only [pub33, key33]
  decide

private theorem key1_getElem_zero : (pub33 1).bytes[0]? = some 1 := by
  simp only [pub33, key33]
  decide

private theorem pub33_zero_ne_one : pub33 0 ≠ pub33 1 := by
  intro h
  have hb : (pub33 0).bytes = (pub33 1).bytes := congrArg PubKey.bytes h
  have h0 : (pub33 0).bytes[0]? = some (0 : UInt8) := key0_getElem_zero
  have h1 : (pub33 1).bytes[0]? = some (1 : UInt8) := key1_getElem_zero
  rw [hb] at h0
  rw [h0] at h1
  exact absurd (Option.some.inj h1) (by decide)

private def zeros32 : ByteArray :=
  ByteArray.mk (List.replicate 32 (0 : UInt8)).toArray

private theorem zeros32_size : zeros32.size = 32 := by
  simp [zeros32, ByteArray.size]

/-- A concrete funding-relevant `open_channel`. -/
private def demoOpen (key : PubKey) : OpenChannel :=
  { temporaryChannelId := ⟨ByteArray.empty⟩
    fundingSatoshis := 0
    pushMsat := ⟨0⟩
    fundingPubKey := key }

/-- A concrete `accept_channel`; as in `FundingLinkTargets`, only
`fundingPubKey` matters for the funding script. -/
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

/-- **The joint construction is satisfiable.**  A complete
`open_channel`/`accept_channel` exchange yields a well-formed funding
parameter set with a 32-byte-output hash and the hash link, all simultaneously.
The hash is the constant zero function; this refutes vacuity of the
construction, while the reverse direction additionally needs the finite pair
admission. -/
theorem openAccept_forward_satisfiable :
    ∃ (H : ByteArray → ByteArray) (o : OpenChannel) (a : AcceptChannel),
      (∀ b : ByteArray, (H b).size = 32) ∧
      (o.toFundingParams H a).WellFormed ∧
      FundingScriptHashLinked H (o.toFundingParams H a) := by
  let o : OpenChannel := demoOpen (pub33 0)
  let a : AcceptChannel := demoAccept (pub33 0)
  refine ⟨fun _ => zeros32, o, a, ?_, ?_, ?_⟩
  · intro _b
    exact zeros32_size
  · exact openAccept_wellFormed (fun _ => zeros32) (fun _ => zeros32_size) o a
      (by simp [o, demoOpen])
      (by simp [o, demoOpen, Bitcoin.Data.MAX_MONEY, Bitcoin.Data.COIN])
      (by simpa [o, demoOpen] using pub33_valid 0)
      (by simpa [a, demoAccept] using pub33_valid 0)
      (by simp [o, demoOpen])
  · exact openAccept_hash_linked (fun _ => zeros32) o a

/-! ## Symmetric limit: `open_channel` alone does not determine the script -/

/-- **Limit: `open_channel` alone does not determine the witness script.**
The opener's `funding_pubkey` is one of the two keys; the second key is the
acceptor's `accept_channel.funding_pubkey`, which is not an `OpenChannel`
field.  One `open_channel` record is therefore compatible with distinct
funding scripts.  This is the symmetric counterpart of
`FundingLinkTargets.acceptChannel_alone_does_not_determine_witnessScript`: the
joint construction needs both messages, and neither message alone is a
function to the P2WSH program. -/
theorem openChannel_alone_does_not_determine_witnessScript :
    ∃ (o : OpenChannel) (a₁ a₂ : AcceptChannel),
      (o.toFundingParams (fun b => b) a₁).witnessScript.bytes ≠
        (o.toFundingParams (fun b => b) a₂).witnessScript.bytes := by
  refine ⟨demoOpen (pub33 0), demoAccept (pub33 0), demoAccept (pub33 1), ?_⟩
  intro h
  have hsz (b : UInt8) : (pub33 b).bytes.size = 33 := key33_size b
  have hkeys : (demoOpen (pub33 0)).fundingPubKey.bytes.size = 33 := hsz 0
  have ha₁ : (demoAccept (pub33 0)).fundingPubKey.bytes.size = 33 := hsz 0
  have ha₂ : (demoAccept (pub33 1)).fundingPubKey.bytes.size = 33 := hsz 1
  have hscript : TwoOfTwoScriptBytes
        ((demoOpen (pub33 0)).toFundingNegotiation (demoAccept (pub33 0))).firstFundingKey
        ((demoOpen (pub33 0)).toFundingNegotiation (demoAccept (pub33 0))).secondFundingKey =
      TwoOfTwoScriptBytes
        ((demoOpen (pub33 0)).toFundingNegotiation (demoAccept (pub33 1))).firstFundingKey
        ((demoOpen (pub33 0)).toFundingNegotiation (demoAccept (pub33 1))).secondFundingKey := by
    have hs : ((demoOpen (pub33 0)).toFundingNegotiation
          (demoAccept (pub33 0))).witnessScript.bytes =
        ((demoOpen (pub33 0)).toFundingNegotiation
          (demoAccept (pub33 1))).witnessScript.bytes := h
    rw [witnessScript_bytes_eq_TwoOfTwoScriptBytes,
      witnessScript_bytes_eq_TwoOfTwoScriptBytes] at hs
    exact hs
  have hfirst₁ : ((demoOpen (pub33 0)).toFundingNegotiation
      (demoAccept (pub33 0))).firstFundingKey.bytes.size = 33 :=
    firstFundingKey_size hkeys ha₁
  have hsecond₁ : ((demoOpen (pub33 0)).toFundingNegotiation
      (demoAccept (pub33 0))).secondFundingKey.bytes.size = 33 :=
    secondFundingKey_size hkeys ha₁
  have hfirst₂ : ((demoOpen (pub33 0)).toFundingNegotiation
      (demoAccept (pub33 1))).firstFundingKey.bytes.size = 33 :=
    firstFundingKey_size hkeys ha₂
  have hsecond₂ : ((demoOpen (pub33 0)).toFundingNegotiation
      (demoAccept (pub33 1))).secondFundingKey.bytes.size = 33 :=
    secondFundingKey_size hkeys ha₂
  obtain ⟨hf, hs⟩ :=
    twoOfTwoScriptBytes_injective hfirst₁ hsecond₁ hfirst₂ hsecond₂ hscript
  have hpair : orderedFundingKeys (demoOpen (pub33 0)).fundingPubKey
        (demoAccept (pub33 0)).fundingPubKey =
      orderedFundingKeys (demoOpen (pub33 0)).fundingPubKey
        (demoAccept (pub33 1)).fundingPubKey := by
    change orderedFundingKeys
        ((demoOpen (pub33 0)).toFundingNegotiation
          (demoAccept (pub33 0))).localFundingKey
        ((demoOpen (pub33 0)).toFundingNegotiation
          (demoAccept (pub33 0))).remoteFundingKey =
      orderedFundingKeys
        ((demoOpen (pub33 0)).toFundingNegotiation
          (demoAccept (pub33 1))).localFundingKey
        ((demoOpen (pub33 0)).toFundingNegotiation
          (demoAccept (pub33 1))).remoteFundingKey
    rw [LnLean.Bitcoin.FundingNegotiation.firstFundingKey_pair,
      LnLean.Bitcoin.FundingNegotiation.firstFundingKey_pair]
    exact Prod.ext hf hs
  rcases key_set_eq_of_ordered_eq hpair with ⟨_, haeq⟩ | ⟨hoeq, _⟩
  · -- The two accept keys would be equal, but they are `pub33 0` and `pub33 1`.
    apply pub33_zero_ne_one
    exact haeq
  · -- Or the opener key would equal the second accept key.
    apply pub33_zero_ne_one
    exact hoeq

/-! ## Linking the phase machine back to the construction -/

/-- **Handshake phase link, opener side.**  Any negotiation exposed by the
opener's view of the funding phase comes from an actual sent `open_channel` and
an actual received `accept_channel`, and both of those keys occur literally in
the constructed witness script.  The proof composes
`FundingPhase.fundingPhase_opener_keys` with
`openAccept_both_keys_in_script`; it does not assume any signature check. -/
theorem fundingPhase_opener_negotiation_bound
    (H : ByteArray → ByteArray) {s : FundingPhase}
    {n : LnLean.Bitcoin.FundingNegotiation}
    (h : s.openerNegotiation? = some n) :
    ∃ (o : OpenChannel) (a : AcceptChannel),
      s.openSent = some o ∧ s.acceptReceived = some a ∧
      n = o.toFundingNegotiation a ∧
      n.localFundingKey = o.fundingPubKey ∧
      n.remoteFundingKey = a.fundingPubKey ∧
      KeyInScript (n.toFundingParams H).witnessScript.bytes o.fundingPubKey ∧
      KeyInScript (n.toFundingParams H).witnessScript.bytes a.fundingPubKey := by
  obtain ⟨o, a, hso, har, hn, hl, hr⟩ :=
    fundingPhase_opener_keys h
  subst hn
  exact ⟨o, a, hso, har, rfl, hl, hr,
    (openAccept_both_keys_in_script H o a).1,
    (openAccept_both_keys_in_script H o a).2⟩

/-- **Handshake phase link, acceptor side.** -/
theorem fundingPhase_acceptor_negotiation_bound
    (H : ByteArray → ByteArray) {s : FundingPhase}
    {n : LnLean.Bitcoin.FundingNegotiation}
    (h : s.acceptorNegotiation? = some n) :
    ∃ (o : OpenChannel) (a : AcceptChannel),
      s.openReceived = some o ∧ s.acceptSent = some a ∧
      n = o.toFundingNegotiation a ∧
      n.localFundingKey = o.fundingPubKey ∧
      n.remoteFundingKey = a.fundingPubKey ∧
      KeyInScript (n.toFundingParams H).witnessScript.bytes o.fundingPubKey ∧
      KeyInScript (n.toFundingParams H).witnessScript.bytes a.fundingPubKey := by
  obtain ⟨o, a, hro, has, hn, hl, hr⟩ :=
    fundingPhase_acceptor_keys h
  subst hn
  exact ⟨o, a, hro, has, rfl, hl, hr,
    (openAccept_both_keys_in_script H o a).1,
    (openAccept_both_keys_in_script H o a).2⟩

/-- **Both endpoints compute the same negotiation.**  If the opener's state
records `open_channel o` as sent and `accept_channel a` as received, and the
acceptor's state records the same two messages, the two exposed negotiations
are equal.  This is the phase-level agreement that the joint construction
relies on; the cryptographic authentication obligation is separate. -/
theorem opener_acceptor_negotiation_agree
    (sOpener sAcceptor : FundingPhase) (o : OpenChannel) (a : AcceptChannel)
    (hso : sOpener.openSent = some o) (har : sOpener.acceptReceived = some a)
    (hro : sAcceptor.openReceived = some o) (has : sAcceptor.acceptSent = some a) :
    sOpener.openerNegotiation? = sAcceptor.acceptorNegotiation? := by
  simp [FundingPhase.openerNegotiation?, FundingPhase.acceptorNegotiation?,
    hso, har, hro, has]

end LnLean.Proofs.Bitcoin.FundingAuthTargets
