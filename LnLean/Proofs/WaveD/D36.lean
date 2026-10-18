import LnLean.Bitcoin.Funding
import LnLean.Bitcoin.ScriptTemplates
import LnLean.Proofs.Bitcoin.FundingProps

/-!
# D36 — Funding well-formedness / parser-safety invariant

English claim (parent obligation `LN-FUND-001`): the BOLT 3 funding witness
script `2 <pubkey1> <pubkey2> 2 OP_CHECKMULTISIG` is rejected by the wave-A
`Bitcoin.Data.Script.parse`, which has no `OP_CHECKMULTISIG` constructor.

The literal statement `FundingProps.witnessScript_parse_eq_none` quantifies
over all `FundingParams`.  That is false: `PubKey.bytes` is an unconstrained
`ByteArray` and `pushData` writes only `bytes.size.toUInt8` as the push-length
byte.  A key of 79 bytes therefore has length byte `0x4f` (`OP_1NEGATE`), so
the parser decodes the key body as opcodes; with suitable bytes the trailing
`OP_2 OP_CHECKMULTISIG` is swallowed as push data and parsing succeeds
(`waveD_d36_counterexample`).

What is true — and what this module adds — is a reusable enough hypothesis:
`FundingParams.ParserSafe` (full name
`LnLean.Proofs.WaveD.D36.FundingParams.ParserSafe`, named inside this module
because Wave-D modules may not import one another), requiring both funding
keys to be 33-byte compressed keys.  It is implied by the existing
`WellFormed` predicate (`waveD_d36_wellFormed_parserSafe`) and preserved by
the temporary-to-final channel-id transition.  Under it each key is a single
`0x21` direct push, the witness script is exactly 71 bytes
(`waveD_d36_parserSafe_witnessScript_size`), and the concrete parser rejects
it (`waveD_d36_parserSafe_parse_eq_none`).  Conversely, any accepted script
proves the parameter is not `ParserSafe`
(`waveD_d36_parse_ne_none_not_parserSafe`), so the invariant is genuinely
needed.

The corrected parse theorem reduces to
`FundingProps.witnessScript_parse_eq_none_of_wellFormed`: the parser only
reads the two key byte strings, so a `ParserSafe` parameter can be completed
with parser-neutral well-formed values (0 sat, 0 push, a 32-byte zero hash)
without changing the witness script.

The counterexample is kernel-checked with `decide` on the concrete
`ByteArray` (core `decide`, not `native_decide`).  This module uses no
`sorry`.

Anchors:
* BOLT 3, "Funding Transaction Output" (`refs/bolts/03-transactions.md:75-83`):
  the funding keys are compressed, 33-byte keys.
* `vendor/btc-lean-core/Bitcoin/Data/Script.lean:31-41` (`ScriptInstr` has no
  `OP_CHECKMULTISIG`) and `:53-71` (`decodeOp`).
* `LnLean/Bitcoin/Seam.lean:74-76` (`pushData` truncates the length to
  `UInt8`).
* `LnLean/Bitcoin/Funding.lean:99-105` (`FundingParams.WellFormed`).
-/

namespace LnLean.Proofs.WaveD.D36

open LnLean
open LnLean.Bitcoin

set_option autoImplicit false
set_option maxRecDepth 10000

/-! ## The reusable 33-byte-key invariant -/

/-- **Reusable parser-safety invariant for `FundingParams`.**  Both funding
keys are serialized as compressed secp256k1 keys (33 bytes).  This is exactly
the condition that makes `pushData` emit one `0x21` direct push per key, so it
is the natural guard for the concrete script parser.  It is weaker than
`FundingParams.WellFormed`: values, `push_msat`, and the witness-script hash
are not constrained. -/
def FundingParams.ParserSafe (p : FundingParams) : Prop :=
  p.localFundingKey.Valid ∧ p.remoteFundingKey.Valid

/-- `ParserSafe` is precisely "both key serializations are 33 bytes". -/
theorem waveD_d36_parserSafe_iff (p : FundingParams) :
    FundingParams.ParserSafe p ↔
      p.localFundingKey.bytes.size = 33 ∧ p.remoteFundingKey.bytes.size = 33 :=
  Iff.rfl

/-- Introduction rule for the invariant. -/
theorem waveD_d36_parserSafe_of_sizes (p : FundingParams)
    (h1 : p.localFundingKey.bytes.size = 33)
    (h2 : p.remoteFundingKey.bytes.size = 33) : FundingParams.ParserSafe p :=
  ⟨h1, h2⟩

/-- The local funding key is 33 bytes. -/
theorem waveD_d36_parserSafe_local (p : FundingParams) (h : FundingParams.ParserSafe p) :
    p.localFundingKey.bytes.size = 33 :=
  h.1

/-- The remote funding key is 33 bytes. -/
theorem waveD_d36_parserSafe_remote (p : FundingParams) (h : FundingParams.ParserSafe p) :
    p.remoteFundingKey.bytes.size = 33 :=
  h.2

/-- Existing structural well-formedness implies parser safety. -/
theorem waveD_d36_wellFormed_parserSafe (p : FundingParams) (h : p.WellFormed) :
    FundingParams.ParserSafe p := by
  rcases h with ⟨-, -, h1, h2, -, -⟩
  exact ⟨h1, h2⟩

/-! ## Parser-relevant consequences of the invariant -/

/-- Under `ParserSafe` each funding key is a 34-byte script push
(`0x21` followed by 33 key bytes). -/
theorem waveD_d36_parserSafe_pushData_size (p : FundingParams)
    (h : FundingParams.ParserSafe p) :
    (pushData p.localFundingKey.bytes).size = 34 ∧
    (pushData p.remoteFundingKey.bytes).size = 34 := by
  have h1 : p.localFundingKey.bytes.size = 33 := h.1
  have h2 : p.remoteFundingKey.bytes.size = 33 := h.2
  constructor <;> simp [pushData, h1, h2]

/-- Under `ParserSafe` the BOLT 3 witness script is the 71-byte string
`0x52 0x21 <key1> 0x21 <key2> 0x52 0xae`. -/
theorem waveD_d36_parserSafe_witnessScript_size (p : FundingParams)
    (h : FundingParams.ParserSafe p) :
    p.witnessScript.bytes.size = 71 :=
  FundingParams.witnessScript_size p h.1 h.2

/-- Lexicographic ordering preserves the invariant of both component keys. -/
theorem waveD_d36_orderedFundingKeys_parserSafe (p : FundingParams)
    (h : FundingParams.ParserSafe p) :
    (orderedFundingKeys p.localFundingKey p.remoteFundingKey).1.Valid ∧
    (orderedFundingKeys p.localFundingKey p.remoteFundingKey).2.Valid := by
  rcases LnLean.Proofs.Bitcoin.FundingProps.orderedFundingKeys_pair
      p.localFundingKey p.remoteFundingKey with hord | hord
  · rw [hord]
    exact ⟨h.1, h.2⟩
  · rw [hord]
    exact ⟨h.2, h.1⟩

/-- The temporary-to-final channel-id transition does not disturb parser
safety; it only updates `finalChannelId?`. -/
theorem waveD_d36_confirmFunding_parserSafe (p : FundingParams)
    (txid : ByteArray) (index : Nat) (h : FundingParams.ParserSafe p) :
    FundingParams.ParserSafe
      (LnLean.Proofs.Bitcoin.FundingProps.confirmFunding p txid index) :=
  h

/-! ## Corrected witness-script parse theorem -/

-- OBLIGATION: LN-WD-D36 corrected form is `FundingParams.ParserSafe p -> p.witnessScript.parse = none`; the unconditional form is refuted below

/-- A 32-byte zero hash, used only to complete parser-neutral parameters. -/
private def zeroHash : ByteArray := (List.replicate 32 (0 : UInt8)).toByteArray

private theorem zeroHash_size : zeroHash.size = 32 := by
  simp [zeroHash]

/-- Parser-neutral completion: replace every field the script parser does not
read (funding value, push amount, witness-script hash, final channel id) with
a well-formed default.  The two funding keys are untouched, so the witness
script is definitionally unchanged. -/
private def parserNeutralCompletion (p : FundingParams) : FundingParams :=
  { p with
    fundingSatoshis := 0
    pushMsat := ⟨0⟩
    witnessScriptHash := zeroHash
    finalChannelId? := none }

private theorem parserNeutralCompletion_witnessScript (p : FundingParams) :
    (parserNeutralCompletion p).witnessScript = p.witnessScript := rfl

private theorem parserNeutralCompletion_wellFormed (p : FundingParams)
    (h : FundingParams.ParserSafe p) : (parserNeutralCompletion p).WellFormed := by
  rcases h with ⟨h1, h2⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Int.le_refl 0
  · show (0 : Int) ≤ Bitcoin.Data.MAX_MONEY
    decide
  · exact h1
  · exact h2
  · exact zeroHash_size
  · show (0 : Int) ≤ 0 * (Msat.MSAT_PER_SAT : Int)
    simp

/-- **Corrected witness-script parse theorem.**  If both funding keys are
33-byte compressed keys, the concrete wave-A parser rejects the BOLT 3 2-of-2
funding witness script: it decodes `OP_2`, the two 33-byte direct pushes, and
the second `OP_2`, then fails on the trailing `OP_CHECKMULTISIG`, for which
`ScriptInstr` has no constructor. -/
theorem waveD_d36_parserSafe_parse_eq_none (p : FundingParams)
    (h : FundingParams.ParserSafe p) : p.witnessScript.parse = none := by
  have hwf : (parserNeutralCompletion p).WellFormed :=
    parserNeutralCompletion_wellFormed p h
  have hparse :=
    LnLean.Proofs.Bitcoin.FundingProps.witnessScript_parse_eq_none_of_wellFormed
      (parserNeutralCompletion p) hwf
  rwa [parserNeutralCompletion_witnessScript] at hparse

/-- `FundingParams.WellFormed` already contains the 33-byte-key condition, so
the corrected parse theorem holds for well-formed parameters as well. -/
theorem waveD_d36_wellFormed_parse_eq_none (p : FundingParams)
    (h : p.WellFormed) : p.witnessScript.parse = none :=
  waveD_d36_parserSafe_parse_eq_none p (waveD_d36_wellFormed_parserSafe p h)

/-- Contrapositive guard: a script that the parser accepts is *not*
`ParserSafe`, so the invariant is genuinely needed by the parse theorem. -/
theorem waveD_d36_parse_ne_none_not_parserSafe {p : FundingParams}
    (h : p.witnessScript.parse ≠ none) : ¬ FundingParams.ParserSafe p :=
  fun hs => h (waveD_d36_parserSafe_parse_eq_none p hs)

/-! ## Mechanized counterexample to the unconditional form

The unconditional statement is refuted by a parameter whose local funding key
is empty and whose remote funding key is 79 bytes.  `pushData` emits the
remote key's length byte `0x4f`, which `decodeOp` reads as `OP_1NEGATE`; the
key body then supplies two direct pushes (`0x4b` = 75 bytes and `0x04` = 4
bytes) that consume the rest of the script, including `OP_2` and
`OP_CHECKMULTISIG`, so the parser terminates successfully instead of hitting
the unsupported opcode. -/

/-- A 79-byte key: length byte `0x4f`, then a 75-byte push (`0x4b`), then a
4-byte push (`0x04`) covering the two remaining key bytes and the script
suffix. -/
private def cexKey : ByteArray :=
  ([0x4b] ++ List.replicate 75 (0x00 : UInt8) ++ [0x04]
    ++ List.replicate 2 (0x00 : UInt8)).toByteArray

private theorem cexKey_size : cexKey.size = 79 := by
  simp [cexKey]

/-- Counterexample parameters: empty local key, 79-byte remote key, and
otherwise arbitrary fields. -/
private def cexP : FundingParams :=
  { fundingSatoshis := 0
    pushMsat := ⟨0⟩
    localFundingKey := ⟨ByteArray.empty⟩
    remoteFundingKey := ⟨cexKey⟩
    witnessScriptHash := ByteArray.empty
    temporaryChannelId := ⟨⟨ByteArray.empty⟩⟩ }

private theorem cexP_not_parserSafe : ¬ FundingParams.ParserSafe cexP := by
  intro h
  have h1 : cexP.localFundingKey.bytes.size = 33 := h.1
  simp [cexP] at h1

private theorem parseWith_step (b : ByteArray) (i i' fuel : Nat)
    (acc : List Bitcoin.Data.ScriptInstr) (op : Bitcoin.Data.ScriptInstr)
    (hi : i < b.size) (hdec : Bitcoin.Data.decodeOp b i = some (op, i')) :
    Bitcoin.Data.Script.parse.parseWith b (fuel + 1) i acc
      = Bitcoin.Data.Script.parse.parseWith b fuel i' (op :: acc) := by
  have hni : ¬ b.size ≤ i := by omega
  simp [Bitcoin.Data.Script.parse.parseWith, hni, hdec]

private theorem cexP_parse_ne_none : cexP.witnessScript.parse ≠ none := by
  let B : ByteArray := ByteArray.empty.push 0x52
      ++ ByteArray.empty.push 0x00
      ++ (ByteArray.empty.push cexKey.size.toUInt8 ++ cexKey)
      ++ ByteArray.empty.push 0x52 ++ ByteArray.empty.push OP_CHECKMULTISIG
  have hbytes : cexP.witnessScript.bytes = B := by
    simp [B, FundingParams.witnessScript, pushData, cexP, orderedFundingKeys,
      listLexLE, cexKey_size]
  have hsize : B.size = 84 := by
    simp [B, cexKey_size]
  have d0 : Bitcoin.Data.decodeOp B 0 = some (.const 2, 1) := by decide
  have d1 : Bitcoin.Data.decodeOp B 1 = some (.push ByteArray.empty, 2) := by decide
  have d2 : Bitcoin.Data.decodeOp B 2 = some (.op1negate, 3) := by decide
  have d3 : Bitcoin.Data.decodeOp B 3 = some (.push (B.extract 4 79), 79) := by
    decide
  have d4 : Bitcoin.Data.decodeOp B 79 = some (.push (B.extract 80 84), 84) := by
    decide
  unfold Bitcoin.Data.Script.parse
  rw [hbytes, hsize]
  rw [parseWith_step B 0 1 83 [] (.const 2) (by rw [hsize]; omega) d0]
  rw [parseWith_step B 1 2 82 [.const 2] (.push ByteArray.empty)
    (by rw [hsize]; omega) d1]
  rw [parseWith_step B 2 3 81 [.push ByteArray.empty, .const 2] (.op1negate)
    (by rw [hsize]; omega) d2]
  rw [parseWith_step B 3 79 80 [.op1negate, .push ByteArray.empty, .const 2]
    (.push (B.extract 4 79)) (by rw [hsize]; omega) d3]
  rw [parseWith_step B 79 84 79
    [.push (B.extract 4 79), .op1negate, .push ByteArray.empty, .const 2]
    (.push (B.extract 80 84)) (by rw [hsize]; omega) d4]
  simp [Bitcoin.Data.Script.parse.parseWith, hsize]

/-- **The unconditional form is false.**  There is a `FundingParams` that is
not parser safe and whose funding witness script the concrete parser accepts
(non-`none` result). -/
theorem waveD_d36_counterexample :
    ∃ p : FundingParams, ¬ FundingParams.ParserSafe p ∧ p.witnessScript.parse ≠ none :=
  ⟨cexP, cexP_not_parserSafe, cexP_parse_ne_none⟩

/-- The blanket statement `∀ p, p.witnessScript.parse = none` is false for the
current model. -/
theorem waveD_d36_unconditional_parse_eq_none_false :
    ¬ (∀ p : FundingParams, p.witnessScript.parse = none) := by
  intro h
  obtain ⟨p, -, hp⟩ := waveD_d36_counterexample
  exact hp (h p)

end LnLean.Proofs.WaveD.D36
