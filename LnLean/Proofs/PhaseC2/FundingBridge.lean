import LnLean.Proofs.Bitcoin.FundingProps

/-!
# Funding output spendability bridge (PC33)

**English claim.**  A Lightning funding output is a P2WSH output whose
committed witness script is BOLT 3's
`OP_2 <funding_pubkey1> <funding_pubkey2> OP_2 OP_CHECKMULTISIG`.
If both funding keys sign the same funding-transaction digest, then the
witness `<> <sig1> <sig2> <funding_witness_script>` is accepted for that
output by the L1 script semantics.  Conversely, every accepted witness is
exactly that 2-of-2 witness and contains both funding signatures.

The concrete script-semantics obligation is deliberately an explicit field
of `FundingSpendBridge`: the parsimonious wave-A parser
`Bitcoin.Data.Script.parse` has no `OP_CHECKMULTISIG` constructor
(`vendor/btc-lean-core/Bitcoin/Data/Script.lean:31-41`), and
`FundingProps.witnessScript_parse_eq_none_of_wellFormed` proves that it
rejects the funding witness script for well-formed parameters.  The vendored
`Bitcoin.Interpreter` does have a `checkMultiSig` opcode
(`vendor/btc-lean-core/Bitcoin/Interpreter/Defs.lean:1027-1090`), but
connecting its byte-level `verifyScript` to the BOLT 3 witness shape is a
separate, larger proof.  This module proves the composition from the bridge
and does not assert the bridge unconditionally.

**BOLT sections.**  BOLT 2 §The `open_channel` Message and §The
`funding_created`/`funding_signed` Messages; BOLT 3 §Funding Transaction
Output (`refs/bolts/03-transactions.md:75-83`, the 2-of-2 P2WSH script).

**rust-lightning anchors (commit `fe4900930c6bd5786ec4203274d7cf312776a5a6`).**
* `lightning/src/ln/chan_utils.rs:847-866` — `make_funding_redeemscript`
  and `make_funding_redeemscript_from_slices` (key ordering).
* `lightning/src/ln/channel.rs:2711-2725` — `get_funding_txo` and
  `get_funding_output` (P2WSH script, funding value).
* `lightning/src/ln/channel.rs:2107-2153` — `funding_signed` handling and
  funding outpoint construction.

**Explicitly NOT modelled.**  SHA-256 itself (the witness-script hash is a
parameter), ECDSA correctness/unforgeability (the signature checker is a
parameter; assumption C3), chain confirmation and reorgs, transaction
malleability/RBF, and the concrete byte-level interpreter run for
`OP_CHECKMULTISIG`.  What is proved is the exact conditional composition:
accepted-witness iff both funding signatures verify, and therefore a
funding output is spendable whenever both keys sign.
-/

namespace LnLean.Proofs.PhaseC2
namespace FundingBridge

set_option autoImplicit false

open LnLean
open LnLean.Bitcoin

/-! ## The BOLT 3 2-of-2 witness -/

/-- A signature checker: public key, signed digest (the funding sighash),
signature bytes. -/
abbrev SigCheck := PubKey → ByteArray → ByteArray → Bool

/-- The BOLT 3 funding witness `<> <sig1> <sig2> <witnessScript>`.
The leading empty element is the dummy consumed by `OP_CHECKMULTISIG`. -/
def twoOfTwoWitness (p : FundingParams) (s1 s2 : ByteArray) : WitnessStack :=
  [ByteArray.empty, s1, s2, p.witnessScript.bytes]

/-- Both funding keys sign the same funding-transaction digest. -/
def BothKeysSign (check : SigCheck) (p : FundingParams) (msg : ByteArray)
    (s1 s2 : ByteArray) : Prop :=
  check p.localFundingKey msg s1 = true ∧
  check p.remoteFundingKey msg s2 = true

/-- The witness reveals the 2-of-2 funding witness script as its last
element.  This is the witness-script half of the spend condition, separated
from the signature half. -/
def RevealsFundingScript (p : FundingParams) (w : WitnessStack) : Prop :=
  ∃ s1 s2 : ByteArray, w = twoOfTwoWitness p s1 s2

/-! ## The funding output built from funding parameters -/

/-- The `FundingOutput` that a set of funding parameters puts on chain at
`(txid, index)`. -/
def fundingOutputOfParams (p : FundingParams) (txid : ByteArray)
    (index : Nat) : FundingOutput :=
  p.toFundingOutput txid index

/-- Its script is exactly the P2WSH funding script of the parameters. -/
theorem fundingOutputOfParams_scriptPubKey (p : FundingParams)
    (txid : ByteArray) (index : Nat) :
    (fundingOutputOfParams p txid index).scriptPubKey =
      p.fundingScriptPubKey := rfl

/-- When the stored witness-script hash is really the SHA-256 of the BOLT 3
2-of-2 witness script, the funding output's `scriptPubKey` is literally the
P2WSH of that witness script (the hash function is a parameter, as in the
seam). -/
theorem fundingOutputOfParams_scriptPubKey_eq_p2wsh
    (sha256 : ByteArray → ByteArray) (p : FundingParams)
    (txid : ByteArray) (index : Nat)
    (hhash : p.witnessScriptHash = sha256 p.witnessScript.bytes) :
    (fundingOutputOfParams p txid index).scriptPubKey =
      LnLean.Bitcoin.p2wsh (sha256 p.witnessScript.bytes) := by
  rw [fundingOutputOfParams_scriptPubKey, FundingParams.fundingScriptPubKey,
    LnLean.Bitcoin.fundingScriptPubKey, hhash]

/-- Its committed hash is exactly the parameters' witness-script hash. -/
theorem fundingOutputOfParams_witnessScriptHash (p : FundingParams)
    (txid : ByteArray) (index : Nat) :
    (fundingOutputOfParams p txid index).witnessScriptHash =
      p.witnessScriptHash := rfl

/-- Its value is exactly `funding_satoshis`. -/
theorem fundingOutputOfParams_value (p : FundingParams)
    (txid : ByteArray) (index : Nat) :
    (fundingOutputOfParams p txid index).value = p.fundingSatoshis := rfl

/-- Its outpoint is the funding `(txid, index)` pair. -/
theorem fundingOutputOfParams_outpoint (p : FundingParams)
    (txid : ByteArray) (index : Nat) :
    (fundingOutputOfParams p txid index).outpoint =
      (⟨txid, index.toUInt32⟩ : OutPoint) := rfl

/-- The raw `scriptPubKey` bytes are `OP_0 <0x20> <witnessScriptHash>`
(BIP 141 P2WSH). -/
theorem fundingOutput_scriptPubKey_bytes (f : FundingOutput) :
    f.scriptPubKey.bytes =
      (ByteArray.empty.push OP_0).push 0x20 ++ f.witnessScriptHash := rfl

/-- A funding output over a 32-byte witness-script hash is exactly 34 bytes. -/
theorem fundingOutput_scriptPubKey_size (f : FundingOutput)
    (h : f.witnessScriptHash.size = 32) :
    f.scriptPubKey.bytes.size = 34 := by
  simpa [FundingOutput.scriptPubKey, LnLean.Bitcoin.fundingScriptPubKey]
    using LnLean.Bitcoin.p2wsh_size f.witnessScriptHash h

/-! ## The script-semantics bridge -/

/-- **Funding spend bridge.**  An explicit interface between a funding
`FundingOutput`, its funding parameters, and an L1 verifier.

* `hash_matches` says the output commits to the parameters' witness-script
  hash, so its `scriptPubKey` is the P2WSH of the BOLT 3 2-of-2 script.
* `script_semantics` is the script-semantics obligation: the verifier accepts
  exactly the BOLT 3 witness `<> <sig1> <sig2> <witnessScript>` with both
  signatures valid under the two funding keys.

The obligation is a field rather than a global postulate so the composition
below is unconditional in the development; a concrete instantiation still has to
prove `script_semantics` for the chosen byte-level interpreter
(`-- OBLIGATION: PC2-FUND-001`, see the module docstring). -/
structure FundingSpendBridge (f : FundingOutput) (p : FundingParams)
    (check : SigCheck) (msg : ByteArray) where
  /-- The L1 script verifier for this output. -/
  verify : Script → WitnessStack → Tx → Bool
  /-- The output is the P2WSH commitment to `p`'s witness script. -/
  hash_matches : f.witnessScriptHash = p.witnessScriptHash
  /-- The script-semantics obligation: accepted witnesses are exactly the
  BOLT 3 two-signature witnesses. -/
  script_semantics : ∀ (tx : Tx) (w : WitnessStack),
    verify p.fundingScriptPubKey w tx = true ↔
      ∃ s1 s2 : ByteArray,
        w = twoOfTwoWitness p s1 s2 ∧
        check p.localFundingKey msg s1 = true ∧
        check p.remoteFundingKey msg s2 = true

/-- The bridge's hash equality makes the concrete output script equal to the
parameters' P2WSH funding script. -/
theorem FundingSpendBridge.scriptPubKey_eq
    {f : FundingOutput} {p : FundingParams} {check : SigCheck}
    {msg : ByteArray} (hb : FundingSpendBridge f p check msg) :
    f.scriptPubKey = p.fundingScriptPubKey := by
  simp only [FundingOutput.scriptPubKey, FundingParams.fundingScriptPubKey,
    LnLean.Bitcoin.fundingScriptPubKey, LnLean.Bitcoin.p2wsh]
  rw [hb.hash_matches]

/-! ## Composition: signatures imply spendability -/

/-- **Core composition.**  If both funding keys sign the funding-transaction
digest, the verifier accepts the BOLT 3 2-of-2 witness for the P2WSH funding
script.  This is the forward direction of the bridge. -/
theorem FundingSpendBridge.spendable
    {f : FundingOutput} {p : FundingParams} {check : SigCheck}
    {msg : ByteArray} (hb : FundingSpendBridge f p check msg)
    (fundingTx : Tx) {s1 s2 : ByteArray}
    (hs : BothKeysSign check p msg s1 s2) :
    hb.verify p.fundingScriptPubKey (twoOfTwoWitness p s1 s2) fundingTx = true := by
  rcases hs with ⟨h1, h2⟩
  exact (hb.script_semantics fundingTx (twoOfTwoWitness p s1 s2)).mpr
    ⟨s1, s2, rfl, h1, h2⟩

/-- **Exact composition for a fixed witness.**  The verifier accepts
`<> <sig1> <sig2> <witnessScript>` if and only if both funding keys sign the
funding-transaction digest.  This is the two-way form of the bridge, not just
the forward implication. -/
theorem FundingSpendBridge.spendable_iff
    {f : FundingOutput} {p : FundingParams} {check : SigCheck}
    {msg : ByteArray} (hb : FundingSpendBridge f p check msg)
    (fundingTx : Tx) (s1 s2 : ByteArray) :
    hb.verify p.fundingScriptPubKey (twoOfTwoWitness p s1 s2) fundingTx = true ↔
      BothKeysSign check p msg s1 s2 := by
  constructor
  · intro h
    obtain ⟨s1', s2', hw, h1, h2⟩ :=
      (hb.script_semantics fundingTx (twoOfTwoWitness p s1 s2)).mp h
    have hs1 : s1 = s1' := by
      have hlen := congrArg (fun w : WitnessStack => w[1]?) hw
      simpa [twoOfTwoWitness] using hlen
    have hs2 : s2 = s2' := by
      have hlen := congrArg (fun w : WitnessStack => w[2]?) hw
      simpa [twoOfTwoWitness] using hlen
    rw [← hs1] at h1
    rw [← hs2] at h2
    exact ⟨h1, h2⟩
  · intro hs
    exact hb.spendable fundingTx hs

/-- **Funding-output spendability.**  The same witness is accepted for the
`FundingOutput` itself, because its `scriptPubKey` is the P2WSH of the 2-of-2
witness script. -/
theorem FundingSpendBridge.fundingOutput_spendable
    {f : FundingOutput} {p : FundingParams} {check : SigCheck}
    {msg : ByteArray} (hb : FundingSpendBridge f p check msg)
    (fundingTx : Tx) {s1 s2 : ByteArray}
    (hs : BothKeysSign check p msg s1 s2) :
    hb.verify f.scriptPubKey (twoOfTwoWitness p s1 s2) fundingTx = true := by
  rw [hb.scriptPubKey_eq]
  exact hb.spendable fundingTx hs

/-- The two-way spendability result for the concrete `FundingOutput`: its
`scriptPubKey` accepts the 2-of-2 witness exactly when both keys sign. -/
theorem FundingSpendBridge.fundingOutput_spendable_iff
    {f : FundingOutput} {p : FundingParams} {check : SigCheck}
    {msg : ByteArray} (hb : FundingSpendBridge f p check msg)
    (fundingTx : Tx) (s1 s2 : ByteArray) :
    hb.verify f.scriptPubKey (twoOfTwoWitness p s1 s2) fundingTx = true ↔
      BothKeysSign check p msg s1 s2 := by
  rw [hb.scriptPubKey_eq]
  exact hb.spendable_iff fundingTx s1 s2

/-- The spendability theorem specialised to the funding output constructed
from the funding parameters at `(txid, index)`. -/
theorem fundingOutputOfParams_spendable
    (p : FundingParams) (txid : ByteArray) (index : Nat)
    {check : SigCheck} {msg : ByteArray}
    (hb : FundingSpendBridge (fundingOutputOfParams p txid index) p check msg)
    (fundingTx : Tx) {s1 s2 : ByteArray}
    (hs : BothKeysSign check p msg s1 s2) :
    hb.verify (fundingOutputOfParams p txid index).scriptPubKey
      (twoOfTwoWitness p s1 s2) fundingTx = true :=
  hb.fundingOutput_spendable fundingTx hs

/-! ## Converse: accepted witnesses contain both signatures -/

/-- **Accepted-witness characterisation.**  Every witness accepted for the
funding script is the BOLT 3 2-of-2 witness, and both signatures verify under
the two funding keys.  No hashlock, timelock, or single-key branch is
accepted. -/
theorem FundingSpendBridge.accepted_witness
    {f : FundingOutput} {p : FundingParams} {check : SigCheck}
    {msg : ByteArray} (hb : FundingSpendBridge f p check msg)
    {fundingTx : Tx} {w : WitnessStack}
    (hacc : hb.verify p.fundingScriptPubKey w fundingTx = true) :
    ∃ s1 s2 : ByteArray,
      w = twoOfTwoWitness p s1 s2 ∧
      check p.localFundingKey msg s1 = true ∧
      check p.remoteFundingKey msg s2 = true :=
  (hb.script_semantics fundingTx w).mp hacc

/-- An accepted spend reveals the funding witness script as its last witness
element. -/
theorem FundingSpendBridge.accepted_reveals_script
    {f : FundingOutput} {p : FundingParams} {check : SigCheck}
    {msg : ByteArray} (hb : FundingSpendBridge f p check msg)
    {fundingTx : Tx} {w : WitnessStack}
    (hacc : hb.verify p.fundingScriptPubKey w fundingTx = true) :
    RevealsFundingScript p w := by
  obtain ⟨s1, s2, hw, -, -⟩ := hb.accepted_witness hacc
  exact ⟨s1, s2, hw⟩

/-- An accepted spend contains two signatures, one verifying under each
funding key. -/
theorem FundingSpendBridge.accepted_has_both_signatures
    {f : FundingOutput} {p : FundingParams} {check : SigCheck}
    {msg : ByteArray} (hb : FundingSpendBridge f p check msg)
    {fundingTx : Tx} {w : WitnessStack}
    (hacc : hb.verify p.fundingScriptPubKey w fundingTx = true) :
    ∃ s1 s2 : ByteArray, BothKeysSign check p msg s1 s2 := by
  obtain ⟨s1, s2, -, h1, h2⟩ := hb.accepted_witness hacc
  exact ⟨s1, s2, h1, h2⟩

/-- Accepted spends for the concrete `FundingOutput` satisfy the same
two-signature characterisation. -/
theorem FundingSpendBridge.fundingOutput_accepted_witness
    {f : FundingOutput} {p : FundingParams} {check : SigCheck}
    {msg : ByteArray} (hb : FundingSpendBridge f p check msg)
    {fundingTx : Tx} {w : WitnessStack}
    (hacc : hb.verify f.scriptPubKey w fundingTx = true) :
    ∃ s1 s2 : ByteArray,
      w = twoOfTwoWitness p s1 s2 ∧
      check p.localFundingKey msg s1 = true ∧
      check p.remoteFundingKey msg s2 = true := by
  rw [hb.scriptPubKey_eq] at hacc
  exact hb.accepted_witness hacc

/-! ## The concrete-parser gap that justifies the bridge field -/

/-- The wave-A `Bitcoin.Data.Script.parse` parser rejects the BOLT 3 funding
witness script for well-formed parameters (both keys 33 bytes), because its
`ScriptInstr` has no `OP_CHECKMULTISIG` constructor.  This is exactly why the
concrete script semantics is a field of `FundingSpendBridge` rather than a
theorem proved against `Script.parse`. -/
theorem fundingWitnessScript_legacyParser_rejects (p : FundingParams)
    (h : p.WellFormed) :
    p.witnessScript.parse = none :=
  LnLean.Proofs.Bitcoin.FundingProps.witnessScript_parse_eq_none_of_wellFormed p h

end FundingBridge
end LnLean.Proofs.PhaseC2
