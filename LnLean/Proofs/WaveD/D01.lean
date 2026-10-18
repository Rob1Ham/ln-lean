import LnLean.Bitcoin.Funding
import LnLean.Bitcoin.Laws
import LnLean.Bitcoin.ScriptTemplates
import LnLean.Bitcoin.Seam
import LnLean.Channel.Commitment
import LnLean.Channel.HTLC
import LnLean.Security.Model

/-!
# D01 — The funding output is P2WSH over the 2-of-2 funding witness script

Catalog: `LN-L1-001`; BOLT 2 §Channel Establishment v1, BOLT 3 §Funding
Transaction Output; rust-lightning `lightning/src/ln/chan_utils.rs:847`
(`make_funding_redeemscript`).

The model defines `FundingParams.fundingScriptPubKey` as
`LnLean.Bitcoin.fundingScriptPubKey p.witnessScriptHash`, i.e. the BIP 141
P2WSH wrapper `OP_0 <0x20> <witnessScriptHash>`, and defines
`FundingParams.witnessScript` as the BOLT 3 template
`OP_2 <pubkey1> <pubkey2> OP_2 OP_CHECKMULTISIG` with the funding keys in
lexicographic order.  This module proves:

* the funding `scriptPubKey` is exactly the P2WSH wrapper and is 34 bytes for
  a 32-byte witness program;
* the P2WSH wrapper is injective, so the witness program is determined by the
  output script;
* the witness script is exactly the 2-of-2 multisig template over the two
  funding keys (in one of the two orders), the keys are covered exactly, and
  the ordered pair is in the BOLT 3 lexicographic order;
* under the explicit crypto-bridge hypothesis that the stored hash really is
  `sha256` of `witnessScript` (and `sha256` is collision resistant), any
  revealed script hashing to the program is exactly the 2-of-2 witness script.

The hash linkage is a *parameter* in the model (`FundingParams` does not
require `witnessScriptHash = sha256 witnessScript`), so the full verbatim
claim is conditional on that missing bridge.  Without the bridge the
unconditional decomposition above is the strongest faithful statement.
-/

namespace LnLean.Proofs.WaveD.D01

set_option autoImplicit false

open LnLean
open LnLean.Bitcoin

-- OBLIGATION: LN-WD-D01

/-! ## P2WSH wrapper for the generic seam operation -/

/-- The catalog target is literally the BIP 141 P2WSH wrapper. -/
theorem waveD_d01_fundingScriptPubKey_is_p2wsh (program : ByteArray) :
    LnLean.Bitcoin.fundingScriptPubKey program = p2wsh program := rfl

/-- Byte-level shape `OP_0 0x20 <program>` of the funding output script. -/
theorem waveD_d01_fundingScriptPubKey_shape (program : ByteArray) :
    (LnLean.Bitcoin.fundingScriptPubKey program).bytes =
      (ByteArray.empty.push OP_0).push 0x20 ++ program := rfl

/-- A P2WSH output with a 32-byte program is 34 bytes (BIP 141). -/
theorem waveD_d01_fundingScriptPubKey_size (program : ByteArray)
    (h : program.size = 32) :
    (LnLean.Bitcoin.fundingScriptPubKey program).bytes.size = 34 :=
  p2wsh_size program h

/-- The P2WSH wrapper is injective: the script determines its witness
program.  This is the encoding-level commitment; it does not by itself say
that the program is the hash of a particular script. -/
theorem waveD_d01_p2wsh_injective {a b : ByteArray}
    (h : p2wsh a = p2wsh b) : a = b := by
  have hb : ((ByteArray.empty.push OP_0).push 0x20 ++ a)
      = ((ByteArray.empty.push OP_0).push 0x20 ++ b) := by
    simpa [p2wsh] using congrArg (fun s : Script => s.bytes) h
  exact (ByteArray.append_right_inj ((ByteArray.empty.push OP_0).push 0x20)).mp hb

/-- Any P2WSH script equal to the funding output fixes the witness program to
be the stored funding witness-script hash. -/
theorem waveD_d01_funding_program_unique (p : FundingParams) {program : ByteArray}
    (h : p.fundingScriptPubKey = p2wsh program) :
    program = p.witnessScriptHash := by
  have h' : p2wsh p.witnessScriptHash = p2wsh program := by
    simpa [FundingParams.fundingScriptPubKey,
      LnLean.Bitcoin.fundingScriptPubKey] using h
  exact (waveD_d01_p2wsh_injective h').symm

/-- A well-formed funding output script is 34 bytes. -/
theorem waveD_d01_fundingScriptPubKey_size_of_wellFormed (p : FundingParams)
    (h : p.WellFormed) : p.fundingScriptPubKey.bytes.size = 34 := by
  rcases h with ⟨-, -, -, -, h32, -⟩
  exact FundingParams.fundingScriptPubKey_size p h32

/-! ## The BOLT 3 witness script template -/

/-- `OP_2 <k1> <k2> OP_2 OP_CHECKMULTISIG`, parameterised by the serialized
key bytes.  `pushData` is the minimal direct push used by the model seam. -/
def waveD_d01_fundingWitnessTemplate (k1 k2 : ByteArray) : ByteArray :=
  (ByteArray.empty.push 0x52)
    ++ pushData k1
    ++ pushData k2
    ++ (ByteArray.empty.push 0x52)
    ++ (ByteArray.empty.push OP_CHECKMULTISIG)

/-- The model witness script is definitionally the template over the ordered
key bytes. -/
theorem waveD_d01_witnessScript_template (p : FundingParams) :
    p.witnessScript.bytes =
      waveD_d01_fundingWitnessTemplate
        (orderedFundingKeys p.localFundingKey p.remoteFundingKey).1.bytes
        (orderedFundingKeys p.localFundingKey p.remoteFundingKey).2.bytes := by
  rfl

/-- The witness script is exactly a 2-of-2 multisig over the two funding keys,
in one of the two orders.  This is the unconditional BOLT 3 shape claim. -/
theorem waveD_d01_witnessScript_is_2of2 (p : FundingParams) :
    p.witnessScript.bytes =
        waveD_d01_fundingWitnessTemplate p.localFundingKey.bytes
          p.remoteFundingKey.bytes
      ∨ p.witnessScript.bytes =
        waveD_d01_fundingWitnessTemplate p.remoteFundingKey.bytes
          p.localFundingKey.bytes := by
  have hpair : orderedFundingKeys p.localFundingKey p.remoteFundingKey =
      (p.localFundingKey, p.remoteFundingKey) ∨
      orderedFundingKeys p.localFundingKey p.remoteFundingKey =
      (p.remoteFundingKey, p.localFundingKey) := by
    unfold orderedFundingKeys
    split
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hpair with h | h
  · left
    simp [waveD_d01_witnessScript_template, h]
  · right
    simp [waveD_d01_witnessScript_template, h]

/-- The two ordered funding keys are exactly the two supplied keys: ordering
never invents, duplicates, or drops a key. -/
theorem waveD_d01_ordered_keys_cover (a b k : PubKey) :
    (k = (orderedFundingKeys a b).1 ∨ k = (orderedFundingKeys a b).2)
      ↔ k = a ∨ k = b := by
  have hpair : orderedFundingKeys a b = (a, b) ∨
      orderedFundingKeys a b = (b, a) := by
    unfold orderedFundingKeys
    split
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hpair with h | h
  · rw [h]
  · rw [h]
    exact ⟨fun hk => hk.elim Or.inr Or.inl,
      fun hk => hk.elim Or.inr Or.inl⟩

/-- `listLexLE` is total on byte lists: one of the two orientations succeeds.
This is the comparison used only to choose the BOLT 3 key order. -/
private theorem waveD_d01_listLexLE_total (a b : List UInt8) :
    listLexLE a b = true ∨ listLexLE b a = true := by
  induction a generalizing b with
  | nil => exact Or.inl rfl
  | cons x xs ih =>
    cases b with
    | nil => exact Or.inr rfl
    | cons y ys =>
      by_cases hxy : x < y
      · exact Or.inl (by simp [listLexLE, hxy])
      · by_cases hyx : y < x
        · exact Or.inr (by simp [listLexLE, hyx])
        · rcases ih ys with h | h
          · exact Or.inl (by simp [listLexLE, hxy, hyx, h])
          · exact Or.inr (by simp [listLexLE, hyx, hxy, h])

/-- The pair returned by `orderedFundingKeys` is in BOLT 3 lexicographic order:
the first serialized key is `<=` the second. -/
theorem waveD_d01_witnessScript_lex_order (a b : PubKey) :
    listLexLE (orderedFundingKeys a b).1.bytes.toList
      (orderedFundingKeys a b).2.bytes.toList = true := by
  by_cases h : listLexLE a.bytes.toList b.bytes.toList
  · simp [orderedFundingKeys, h]
  · rcases waveD_d01_listLexLE_total a.bytes.toList b.bytes.toList with ht | ht
    · exact absurd ht h
    · simpa [orderedFundingKeys, h] using ht

/-- For well-formed parameters (33-byte compressed keys) the 2-of-2 witness
script is 71 bytes: `1 + 34 + 34 + 1 + 1`. -/
theorem waveD_d01_witnessScript_size (p : FundingParams) (h : p.WellFormed) :
    p.witnessScript.bytes.size = 71 := by
  rcases h with ⟨-, -, h1, h2, -, -⟩
  exact FundingParams.witnessScript_size p h1 h2

/-! ## Hash commitment: the missing crypto bridge -/

/-- The model field that is *not* enforced by `FundingParams`: the stored
witness-script hash is the hash of the computed 2-of-2 witness script.  In a
faithful deployment it is an invariant of channel construction
(`make_funding_redeemscript` followed by `sha256`), but the wave-A model keeps
the hash as a parameter. -/
def waveD_d01_P2WSHCommits (sha256 : ByteArray → ByteArray)
    (p : FundingParams) : Prop :=
  p.witnessScriptHash = sha256 p.witnessScript.bytes

/-- Under the hash bridge, the funding output is P2WSH over the *computed*
2-of-2 witness script (rather than merely over an opaque 32-byte value). -/
theorem waveD_d01_funding_scriptPubKey_eq_p2wsh_sha256
    (sha256 : ByteArray → ByteArray) (p : FundingParams)
    (h : waveD_d01_P2WSHCommits sha256 p) :
    p.fundingScriptPubKey = p2wsh (sha256 p.witnessScript.bytes) := by
  unfold waveD_d01_P2WSHCommits at h
  simp [FundingParams.fundingScriptPubKey,
    LnLean.Bitcoin.fundingScriptPubKey, h]

/-- P2WSH binding: assuming the hash bridge and collision resistance of
`sha256`, any script whose hash matches the witness program is exactly the
funding witness script. -/
theorem waveD_d01_p2wsh_binds_witness
    (sha256 : ByteArray → ByteArray)
    (hcr : ∀ a b : ByteArray, sha256 a = sha256 b → a = b)
    (p : FundingParams) (hcommit : waveD_d01_P2WSHCommits sha256 p)
    {revealed : ByteArray}
    (hrev : sha256 revealed = p.witnessScriptHash) :
    revealed = p.witnessScript.bytes := by
  apply hcr
  rw [hrev]
  exact hcommit

/-- The full verbatim claim, conditional on the hash bridge and collision
resistance: a script revealed against the funding P2WSH output is exactly the
BOLT 3 2-of-2 multisig witness script over the two funding keys. -/
theorem waveD_d01_revealed_script_is_2of2
    (sha256 : ByteArray → ByteArray)
    (hcr : ∀ a b : ByteArray, sha256 a = sha256 b → a = b)
    (p : FundingParams) (hcommit : waveD_d01_P2WSHCommits sha256 p)
    {revealed : ByteArray}
    (hrev : sha256 revealed = p.witnessScriptHash) :
    revealed =
        waveD_d01_fundingWitnessTemplate p.localFundingKey.bytes
          p.remoteFundingKey.bytes
      ∨ revealed =
        waveD_d01_fundingWitnessTemplate p.remoteFundingKey.bytes
          p.localFundingKey.bytes := by
  rw [waveD_d01_p2wsh_binds_witness sha256 hcr p hcommit hrev]
  exact waveD_d01_witnessScript_is_2of2 p

/-! ## The confirmed funding output -/

/-- Every L1 funding output accepted by `FundingConfirmed` has exactly the
P2WSH script over the stored witness-script hash. -/
theorem waveD_d01_confirmed_script_is_p2wsh (p : FundingParams) {tx : Tx}
    {index : Nat} (h : FundingConfirmed p tx index) :
    ∃ out : TxOut,
      tx.vout[index]? = some out ∧
      out.scriptPubKey = p2wsh p.witnessScriptHash := by
  obtain ⟨out, hout, hscript⟩ := FundingConfirmed.script_eq h
  refine ⟨out, hout, ?_⟩
  rw [hscript]
  exact waveD_d01_fundingScriptPubKey_is_p2wsh p.witnessScriptHash

/-- Summary of the unconditional model-level content: the funding output is
the P2WSH wrapper and its witness script is the BOLT 3 2-of-2 template. -/
theorem waveD_d01_funding_output_structure (p : FundingParams) :
    p.fundingScriptPubKey = p2wsh p.witnessScriptHash ∧
      (p.witnessScript.bytes =
          waveD_d01_fundingWitnessTemplate p.localFundingKey.bytes
            p.remoteFundingKey.bytes
        ∨ p.witnessScript.bytes =
          waveD_d01_fundingWitnessTemplate p.remoteFundingKey.bytes
            p.localFundingKey.bytes) :=
  ⟨rfl, waveD_d01_witnessScript_is_2of2 p⟩

end LnLean.Proofs.WaveD.D01
