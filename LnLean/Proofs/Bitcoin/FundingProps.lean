import LnLean.Basic.Core
import LnLean.Bitcoin.Seam
import LnLean.Bitcoin.Funding

/-!
# Funding output laws (B01)

**English claim.**  A Lightning channel is funded by one P2WSH output.  Its
witness script is BOLT 3's `2 <pubkey1> <pubkey2> 2 OP_CHECKMULTISIG`, with the
two *compressed* funding keys in lexicographic order, so it is exactly a
2-of-2 multisig over the two funding keys.  The P2WSH wrapper is
`OP_0 <0x20> SHA256(witnessScript)` and is 34 bytes; the witness script itself
is 71 bytes for well-formed (33-byte) keys.  The funding outpoint is the pair
`(funding_txid, output_index)` with the index stored as a `UInt32`, and a
`FundingConfirmed` output at that index carries exactly the funding value (in
satoshis) and, when the parameters are well formed, lies in Bitcoin
`MoneyRange`.  The final channel id is built from the funding txid alone; it
is therefore determined by the funding outpoint and is unchanged by a repeated
temporary-to-final transition.  Finally, channel capacity in millisatoshis is
`funding_satoshis * 1000`; `push_msat` is a *split* of that capacity, not an
addition to it (see the correction below).  Any witness accepted by the L1
interpreter for the funding `scriptPubKey` is, under an explicit interpreter
bridge hypothesis, exactly the 4-element 2-of-2 witness
`<> <sig1> <sig2> <witnessScript>`; the module does not prove the bridge for
real Bitcoin Script, nor ECDSA unforgeability, and therefore does not claim a
consensus-level "only the 2-of-2 can spend" theorem.

**BOLT sections.**  BOLT 2 §Definition of `channel_id`
(`refs/bolts/02-peer-protocol.md:59-77`), §The `open_channel` Message
(`:689-691` fields, `:723-729` temporary id and `funding_satoshis`/`push_msat`
semantics, `:803-808` sender requirements), §The `funding_created` Message
(`:643-651`).  BOLT 3 §Funding Transaction Output
(`refs/bolts/03-transactions.md:75-82`) for the exact 2-of-2 script and the
lexicographic key order.

**rust-lightning anchors (commit `fe4900930c6bd5786ec4203274d7cf312776a5a6`).**
* `lightning/src/ln/chan_utils.rs:847-855` — `make_funding_redeemscript`.
* `lightning/src/ln/chan_utils.rs:857-866` —
  `make_funding_redeemscript_from_slices`: compares the two serialized keys
  and emits `OP_2 <lesser> <greater> OP_2 OP_CHECKMULTISIG`.
* `lightning/src/ln/chan_utils.rs:1133-1145` — funding redeemscript built from
  the holder and counterparty funding pubkeys.
* `lightning/src/ln/channel.rs:2135-2153` — `funding_tx_constructed` sets
  `funding_outpoint`.
* `lightning/src/ln/channel.rs:2711-2725` — `get_funding_txo` and
  `get_funding_output` (value = `get_value_satoshis()`, script = P2WSH of the
  funding redeemscript).
* `lightning/src/ln/channel.rs:4001` — `channel_id` is replaced by the
  funding-derived id; `:4498-4499` — the temporary id is used as the channel
  id during negotiation.
* `lightning/src/ln/channel.rs:4217-4220` — `push_msat` is rejected when it
  exceeds the channel value (minus reserve) in millisatoshis.

**Corrections to the mission wording.**
* *"funding output value plus push amount equals the channel capacity"* is
  dimensionally wrong as stated: the output value is in satoshis while
  `push_msat` is in millisatoshis, and BOLT 2 makes `push_msat` a part of the
  capacity, not an extra contribution.  The corrected law is
  `capacity = (capacity - push_msat) + push_msat`, i.e. the funder's balance
  plus the pushed amount equals capacity, under the wave-A hypothesis
  `push_msat <= funding_satoshis * 1000` (`FundingParams.WellFormed`); this is
  `capacity_eq_funder_plus_push` below.  A second checked law
  (`capacity_independent_of_push`) shows that changing `push_msat` does not
  change capacity or the funding output value.
* *"the final channel id is derived from the funding txid"* follows the
  wave-A model (`FinalChannelId.MatchesOutpoint` compares only the txid).  BOLT
  2 actually mixes in the output index with a big-endian XOR
  (`02-peer-protocol.md:59-64`); the wave-A model has no XOR and this module
  therefore does not state the full BOLT 2 rule (recorded in `B01.md`).

**Explicitly NOT modelled.**  SHA-256 itself (the hash is a parameter; only a
conditional, collision-resistance-parameterised binding lemma is proved), L1
consensus, chain confirmation and reorgs, fee/RBF behaviour of the funding
transaction, concrete `OP_CHECKMULTISIG`/P2WSH execution, and ECDSA key
ownership/unforgeability (assumption C3).  The wave-A `ScriptInstr` parser has
no `OP_CHECKMULTISIG` constructor (`vendor/btc-lean-core/Bitcoin/Data/Script.lean:31-41`),
which is stated as an obligation rather than hidden.
-/

namespace LnLean.Proofs.Bitcoin
namespace FundingProps

set_option autoImplicit false

open LnLean
open LnLean.Bitcoin

/-! ## The 2-of-2 funding witness script -/

/-- The bytes between the leading `OP_2` and the trailing `OP_CHECKMULTISIG`:
the two key pushes in BOLT 3 order, followed by the second `OP_2`. -/
def orderedKeyPushes (p : FundingParams) : ByteArray :=
  let keys := orderedFundingKeys p.localFundingKey p.remoteFundingKey
  pushData keys.1.bytes ++ pushData keys.2.bytes ++ (ByteArray.empty.push 0x52)

/-- The witness script decomposed into its BOLT 3 prefix, key section, and
`OP_CHECKMULTISIG` suffix. -/
theorem witnessScript_bytes (p : FundingParams) :
    p.witnessScript.bytes =
      (ByteArray.empty.push 0x52) ++ orderedKeyPushes p
        ++ (ByteArray.empty.push OP_CHECKMULTISIG) := by
  simp [FundingParams.witnessScript, orderedKeyPushes, ByteArray.append_assoc]

/-- The witness script has the BOLT 3 shape: it starts with `OP_2`, ends with
`OP_CHECKMULTISIG`, and the middle section is the two key pushes. -/
theorem witnessScript_2of2_structure (p : FundingParams) :
    ∃ mid : ByteArray,
      p.witnessScript.bytes =
        (ByteArray.empty.push 0x52) ++ mid
          ++ (ByteArray.empty.push OP_CHECKMULTISIG) := by
  exact ⟨orderedKeyPushes p, witnessScript_bytes p⟩

/-- `orderedFundingKeys` returns the two supplied keys in one of the two
orders; it never invents or drops a key. -/
theorem orderedFundingKeys_pair (a b : PubKey) :
    orderedFundingKeys a b = (a, b) ∨ orderedFundingKeys a b = (b, a) := by
  unfold orderedFundingKeys
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The witness script is a 2-of-2 multisig over *exactly* the two funding
keys, in one of the two lexicographic orders required by BOLT 3. -/
theorem witnessScript_is_2of2_over_funding_keys (p : FundingParams) :
    p.witnessScript.bytes =
        (ByteArray.empty.push 0x52) ++ pushData p.localFundingKey.bytes
          ++ pushData p.remoteFundingKey.bytes
          ++ (ByteArray.empty.push 0x52)
          ++ (ByteArray.empty.push OP_CHECKMULTISIG)
    ∨ p.witnessScript.bytes =
        (ByteArray.empty.push 0x52) ++ pushData p.remoteFundingKey.bytes
          ++ pushData p.localFundingKey.bytes
          ++ (ByteArray.empty.push 0x52)
          ++ (ByteArray.empty.push OP_CHECKMULTISIG) := by
  rcases orderedFundingKeys_pair p.localFundingKey p.remoteFundingKey with h | h
  · left
    simp [FundingParams.witnessScript, h, ByteArray.append_assoc]
  · right
    simp [FundingParams.witnessScript, h, ByteArray.append_assoc]

/-- For well-formed parameters the witness script is 71 bytes:
`1 + 34 + 34 + 1 + 1` (BOLT 3, compressed 33-byte keys). -/
theorem witnessScript_size_of_wellFormed (p : FundingParams) (h : p.WellFormed) :
    p.witnessScript.bytes.size = 71 := by
  rcases h with ⟨-, -, hk1, hk2, -, -⟩
  exact FundingParams.witnessScript_size p hk1 hk2

/-! ## The P2WSH wrapper -/

/-- `fundingScriptPubKey` is `OP_0 <0x20> <witnessScriptHash>` (BIP 141). -/
theorem fundingScriptPubKey_is_p2wsh (p : FundingParams) :
    p.fundingScriptPubKey.bytes =
      (ByteArray.empty.push OP_0).push 0x20 ++ p.witnessScriptHash := rfl

/-- For well-formed parameters the funding `scriptPubKey` is exactly 34 bytes. -/
theorem fundingScriptPubKey_size_of_wellFormed (p : FundingParams)
    (h : p.WellFormed) : p.fundingScriptPubKey.bytes.size = 34 := by
  rcases h with ⟨-, -, -, -, h32, -⟩
  exact FundingParams.fundingScriptPubKey_size p h32

/-- Conditional commitment: if the stored `witnessScriptHash` really is the
SHA-256 of the funding witness script, and SHA-256 is collision resistant on
the modelled domain (assumption C1 as an explicit hypothesis), then any script
whose hash matches the P2WSH program is the funding witness script.  This is
the strongest "the output commits to the 2-of-2 script" statement the seam can
make without a crypto instantiation. -/
theorem p2wsh_program_binds_witnessScript
    (sha256 : ByteArray → ByteArray)
    (hcr : ∀ a b : ByteArray, sha256 a = sha256 b → a = b)
    (p : FundingParams) (revealed : ByteArray)
    (hcommit : p.witnessScriptHash = sha256 p.witnessScript.bytes)
    (hreveal : sha256 revealed = p.witnessScriptHash) :
    revealed = p.witnessScript.bytes := by
  apply hcr
  rw [hreveal, hcommit]

/-! ## Funding outpoint: txid and `UInt32` index -/

/-- The funding outpoint is definitionally the `(txid, UInt32 index)` pair. -/
theorem fundingOutpoint_pair (txid : ByteArray) (index : Nat) :
    LnLean.Bitcoin.Funding.fundingOutpoint txid index =
      (⟨txid, index.toUInt32⟩ : OutPoint) := rfl

/-- The outpoint's output index is the `UInt32` cast of the supplied index. -/
theorem fundingOutpoint_index_uint32 (txid : ByteArray) (index : Nat) :
    (LnLean.Bitcoin.Funding.fundingOutpoint txid index).n = index.toUInt32 := rfl

/-- Whatever the supplied `Nat`, the stored output index fits in 32 bits. -/
theorem fundingOutpoint_index_bounded (txid : ByteArray) (index : Nat) :
    (LnLean.Bitcoin.Funding.fundingOutpoint txid index).n.toNat < 2 ^ 32 :=
  UInt32.toNat_lt_size _

/-- Inside the `UInt32` range the index survives the cast: the outpoint does
not silently change an in-range output index. -/
theorem fundingOutpoint_index_of_lt {txid : ByteArray} {index : Nat}
    (h : index < 2 ^ 32) :
    (LnLean.Bitcoin.Funding.fundingOutpoint txid index).n.toNat = index := by
  show (index.toUInt32).toNat = index
  exact UInt32.toNat_ofNat_of_lt (by simpa using h)

/-! ## Confirmed funding output: value, script, range -/

/-- A confirmed funding output carries exactly the funding value, and that
value is in Bitcoin `MoneyRange` whenever the parameters are well formed. -/
theorem FundingConfirmed.value_and_moneyRange {p : FundingParams} {tx : Tx}
    {index : Nat} (hwf : p.WellFormed) (h : FundingConfirmed p tx index) :
    ∃ out : TxOut,
      tx.vout[index]? = some out ∧
      out.value = p.fundingSatoshis ∧
      Bitcoin.Data.MoneyRange out.value = true := by
  obtain ⟨out, hout, hvalue⟩ := FundingConfirmed.value_eq h
  refine ⟨out, hout, hvalue, ?_⟩
  rw [hvalue]
  exact FundingParams.wellFormed_moneyRange p hwf

/-- A confirmed funding output's script is the P2WSH wrapper over the stored
witness-script hash. -/
theorem FundingConfirmed.script_is_p2wsh {p : FundingParams} {tx : Tx}
    {index : Nat} (h : FundingConfirmed p tx index) :
    ∃ out : TxOut,
      tx.vout[index]? = some out ∧
      out.scriptPubKey.bytes =
        (ByteArray.empty.push OP_0).push 0x20 ++ p.witnessScriptHash := by
  obtain ⟨out, hout, hscript⟩ := FundingConfirmed.script_eq h
  refine ⟨out, hout, ?_⟩
  rw [hscript]
  exact fundingScriptPubKey_is_p2wsh p

/-- For well-formed parameters a confirmed funding output is exactly 34 bytes,
the BIP 141 P2WSH `scriptPubKey` size. -/
theorem FundingConfirmed.script_size {p : FundingParams} {tx : Tx} {index : Nat}
    (hwf : p.WellFormed) (h : FundingConfirmed p tx index) :
    ∃ out : TxOut,
      tx.vout[index]? = some out ∧ out.scriptPubKey.bytes.size = 34 := by
  obtain ⟨out, hout, hscript⟩ := FundingConfirmed.script_eq h
  refine ⟨out, hout, ?_⟩
  rw [hscript]
  exact fundingScriptPubKey_size_of_wellFormed p hwf

/-- Confirmation at `index` implies that the funding transaction really has
such an output index. -/
theorem FundingConfirmed.index_lt_length {p : FundingParams} {tx : Tx}
    {index : Nat} (h : FundingConfirmed p tx index) :
    index < tx.vout.length := by
  obtain ⟨out, hout, -, -⟩ := h
  exact (List.getElem?_eq_some_iff.mp hout).1

/-! ## Capacity versus `push_msat` -/

/-- Channel capacity in millisatoshis, computed from the L1 funding value.
It is an `Int` to mirror `BtcAmount`; `channelCapacityMsat_nonneg` recovers
non-negativity from `FundingParams.WellFormed`.  BOLT 2: capacity is
`funding_satoshis * 1000` msat, and `push_msat` is a part of it. -/
def channelCapacityMsat (p : FundingParams) : Int :=
  p.fundingSatoshis * (Msat.MSAT_PER_SAT : Int)

/-- Capacity is non-negative for well-formed parameters. -/
theorem channelCapacityMsat_nonneg (p : FundingParams) (h : p.WellFormed) :
    0 ≤ channelCapacityMsat p := by
  rcases h with ⟨h0, -, -, -, -, -⟩
  unfold channelCapacityMsat
  have h1000 : (0 : Int) ≤ (Msat.MSAT_PER_SAT : Int) := by
    unfold Msat.MSAT_PER_SAT
    decide
  exact Int.mul_nonneg h0 h1000

/-- BOLT 2's sender requirement `push_msat <= funding_satoshis * 1000` is
exactly the wave-A well-formedness conjunct. -/
theorem pushMsat_le_capacity (p : FundingParams) (h : p.WellFormed) :
    (p.pushMsat.val : Int) ≤ channelCapacityMsat p := by
  rcases h with ⟨-, -, -, -, -, hpush⟩
  simpa [channelCapacityMsat] using hpush

/-- Corrected "value plus push" law: capacity is the funder's remaining
balance plus the pushed amount.  (The literal mission wording added satoshis
to millisatoshis; see the module docstring.) -/
theorem capacity_eq_funder_plus_push (p : FundingParams) (h : p.WellFormed) :
    channelCapacityMsat p =
      (channelCapacityMsat p - (p.pushMsat.val : Int)) + (p.pushMsat.val : Int) := by
  rcases h with ⟨-, -, -, -, -, -⟩
  omega

/-- `push_msat` changes only the split, never the capacity or the funding
output value. -/
theorem capacity_independent_of_push (p : FundingParams) (q : Msat) :
    channelCapacityMsat { p with pushMsat := q } = channelCapacityMsat p := rfl

/-- Changing `push_msat` leaves the funding output value untouched. -/
theorem fundingValue_independent_of_push (p : FundingParams) (q : Msat) :
    ({ p with pushMsat := q } : FundingParams).fundingSatoshis
      = p.fundingSatoshis := rfl

/-- Capacity is bounded by 21M BTC expressed in millisatoshis (`Msat.MAX`)
for well-formed parameters.  This is arithmetic over the `Int` capacity
representation: `WellFormed` gives `fundingSatoshis ≤ MAX_MONEY = 21e6 * 1e8`,
and multiplying by `MSAT_PER_SAT = 1000` gives at most `21e6 * 1e8 * 1000`,
which is exactly `Msat.MAX`. -/
theorem channelCapacityMsat_le_MSAT_MAX (p : FundingParams) (h : p.WellFormed) :
    channelCapacityMsat p ≤ (Msat.MAX.val : Int) := by
  rcases h with ⟨-, hmax, -, -, -, -⟩
  have hmax' : p.fundingSatoshis ≤ (2100000000000000 : Int) := by
    unfold Bitcoin.Data.MAX_MONEY Bitcoin.Data.COIN at hmax
    exact hmax
  have hMAX : (Msat.MAX.val : Int) =
      (2100000000000000 : Int) * (Msat.MSAT_PER_SAT : Int) := by
    unfold Msat.MAX Msat.SAT_PER_BTC Msat.MSAT_PER_SAT
    decide
  have hmul : p.fundingSatoshis * (Msat.MSAT_PER_SAT : Int) ≤
      (2100000000000000 : Int) * (Msat.MSAT_PER_SAT : Int) :=
    Int.mul_le_mul_of_nonneg_right hmax' (by
      unfold Msat.MSAT_PER_SAT
      decide)
  unfold channelCapacityMsat
  rw [hMAX]
  exact hmul

/-! ## Temporary to final channel id -/

/-- The temporary-to-final transition: keep every funding parameter, but
record the final channel id derived from the funding outpoint. -/
def confirmFunding (p : FundingParams) (txid : ByteArray)
    (index : Nat) : FundingParams :=
  { p with
    finalChannelId? :=
      some (FinalChannelId.fromFundingOutpoint
        (LnLean.Bitcoin.Funding.fundingOutpoint txid index)) }

/-- After confirmation the recorded final channel id is the one derived from
the outpoint. -/
theorem confirm_finalChannelId (p : FundingParams) (txid : ByteArray)
    (index : Nat) :
    (confirmFunding p txid index).finalChannelId? =
      some (FinalChannelId.fromFundingOutpoint
        (LnLean.Bitcoin.Funding.fundingOutpoint txid index)) := rfl

/-- The final channel id of a confirmed channel is exactly the funding txid. -/
theorem confirm_finalChannelId_txid {p : FundingParams} {txid : ByteArray}
    {index : Nat} {c : FinalChannelId}
    (h : (confirmFunding p txid index).finalChannelId? = some c) :
    c.id.bytes = txid := by
  cases h
  rfl

/-- The final channel id is stable under repeating the temporary-to-final
transition (no drift once confirmed). -/
theorem confirm_stable (p : FundingParams) (txid : ByteArray) (index : Nat) :
    (confirmFunding (confirmFunding p txid index) txid index).finalChannelId? =
      (confirmFunding p txid index).finalChannelId? := by
  rw [confirm_finalChannelId, confirm_finalChannelId]

/-- Confirmation does not touch the funding value, the witness-script hash, or
the temporary id; only `finalChannelId?` changes. -/
theorem confirm_preserves_funding (p : FundingParams) (txid : ByteArray)
    (index : Nat) :
    (confirmFunding p txid index).fundingSatoshis = p.fundingSatoshis ∧
    (confirmFunding p txid index).witnessScriptHash = p.witnessScriptHash ∧
    (confirmFunding p txid index).temporaryChannelId = p.temporaryChannelId :=
  ⟨rfl, rfl, rfl⟩

/-- The final id is determined by the funding outpoint, not by the temporary
id: two channels confirmed on the same outpoint record the same final id. -/
theorem confirm_finalChannelId_deterministic (p q : FundingParams)
    (txid : ByteArray) (index : Nat) :
    (confirmFunding p txid index).finalChannelId? =
      (confirmFunding q txid index).finalChannelId? := by
  rw [confirm_finalChannelId, confirm_finalChannelId]

/-! ## Spend path: conditional 2-of-2-only predicate -/

/-- A signature checker: public key, signed message digest (the BIP 143-style
sighash supplied by the L1 layer), signature bytes. -/
abbrev SigCheck := PubKey → ByteArray → ByteArray → Bool

/-- The BOLT 3 funding witness: `<> <sig1> <sig2> <witnessScript>`.  The
leading empty element is the `OP_CHECKMULTISIG` dummy consumed by the
interpreter; `s1` and `s2` must verify under the two funding keys on the same
message. -/
def TwoOfTwoWitness (p : FundingParams) (check : SigCheck) (msg : ByteArray)
    (w : WitnessStack) : Prop :=
  ∃ s1 s2 : ByteArray,
    w = [ByteArray.empty, s1, s2, p.witnessScript.bytes] ∧
    check p.localFundingKey msg s1 = true ∧
    check p.remoteFundingKey msg s2 = true

/-- **Interpreter bridge (explicit hypothesis, not an assumption of the
development).**  The L1 verifier accepts a witness for the funding
`scriptPubKey` exactly when that witness is the BOLT 3 2-of-2 witness.  This is
a predicate over the L1 interpreter; establishing it for `btc-lean`'s concrete
`Script` semantics is out of scope (see `LN-FUND-001`). -/
def FundingSpendBridge (verify : Script → WitnessStack → Tx → Bool)
    (check : SigCheck) (p : FundingParams) (msg : ByteArray) : Prop :=
  ∀ (tx : Tx) (w : WitnessStack),
    verify p.fundingScriptPubKey w tx = true ↔ TwoOfTwoWitness p check msg w

/-- The conditional "only the 2-of-2 path" predicate: every accepted spend is
a 2-of-2 witness.  This is deliberately a predicate over an interpreter, not a
claim about Bitcoin consensus. -/
def SpendOnly2of2 (verify : Script → WitnessStack → Tx → Bool)
    (check : SigCheck) (p : FundingParams) (msg : ByteArray) : Prop :=
  FundingSpendBridge verify check p msg

/-- **Conditional spend-path theorem.**  Assuming the interpreter bridge, any
accepted spend of the funding output exhibits the exact BOLT 3 witness and two
signatures that verify under the two funding keys.  No hashlock, timelock, or
single-key branch can be accepted. -/
theorem fundingSpend_conditional_2of2_only
    {verify : Script → WitnessStack → Tx → Bool} {check : SigCheck}
    {p : FundingParams} {msg : ByteArray}
    (hbridge : SpendOnly2of2 verify check p msg)
    {tx : Tx} {w : WitnessStack}
    (hacc : verify p.fundingScriptPubKey w tx = true) :
    ∃ s1 s2 : ByteArray,
      w = [ByteArray.empty, s1, s2, p.witnessScript.bytes] ∧
      check p.localFundingKey msg s1 = true ∧
      check p.remoteFundingKey msg s2 = true :=
  (hbridge tx w).mp hacc

/-- The witness shape alone (without the signature checks): an accepted spend
must reveal the funding witness script as its last witness element. -/
theorem fundingSpend_reveals_witnessScript
    {verify : Script → WitnessStack → Tx → Bool} {check : SigCheck}
    {p : FundingParams} {msg : ByteArray}
    (hbridge : SpendOnly2of2 verify check p msg)
    {tx : Tx} {w : WitnessStack}
    (hacc : verify p.fundingScriptPubKey w tx = true) :
    ∃ s1 s2 : ByteArray,
      w = [ByteArray.empty, s1, s2, p.witnessScript.bytes] := by
  obtain ⟨s1, s2, hw, -, -⟩ :=
    fundingSpend_conditional_2of2_only hbridge hacc
  exact ⟨s1, s2, hw⟩

/-- btc-lean's `Script.parse` rejects the 2-of-2 funding witness script because
`ScriptInstr` has no `OP_CHECKMULTISIG` constructor
(`vendor/btc-lean-core/Bitcoin/Data/Script.lean:31-41`, `decodeOp` `:53-71`);
consequently the concrete interpreter bridge cannot yet be stated or proved.

**This statement is false as written, because it has no well-formedness
hypothesis.**  `FundingParams` allows arbitrary key byte arrays, and
`pushData` stores only `size.toUInt8` as the length byte.  If the first key is
empty and the second is the 79-byte array
`0x04 0xaa 0xaa 0xaa 0xaa 0x4b <73 bytes of 0xaa>`, the script is
`0x52 0x00 0x4f 0x04 0xaa 0xaa 0xaa 0xaa 0x4b ... 0x52 0xae` (84 bytes):
`0x00` is a zero-length push, the *length byte* `0x4f` of the second key
decodes as `OP_1NEGATE`, and the parser then decodes the key *contents* as
opcodes.  The `0x4b` at index 8 pushes 75 bytes, which swallows the trailing
`0x52 0xae` and makes the next parse index exactly `bytes.size` (= 84), so
`parse` returns `some [...]`, not `none`.  The intended claim — and the one
relevant to BOLT 3 — needs `p.WellFormed` (33-byte compressed keys), where the
byte string is the concrete 71-byte `0x52 0x21 <key1> 0x21 <key2> 0x52 0xae`
and the final `0xae` is decoded as an opcode.  See `agents/reports/C02.md` for
the evaluated counterexample; the statement is kept verbatim and remains an
obligation. -/
theorem witnessScript_parse_eq_none (p : FundingParams) :
    p.witnessScript.parse = none := by
  -- OBLIGATION: LN-FUND-001 the wave-A script parser rejects `OP_CHECKMULTISIG`.
  sorry

end FundingProps
end LnLean.Proofs.Bitcoin
