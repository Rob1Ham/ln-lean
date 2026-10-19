import Bitcoin.TxValidation.Full
import LnLean.Proofs.Bitcoin.SighashBridgeTargets

/-!
# H30 — the funding 2-of-2 spend at `TxValidation.Full.txCheckerFor`

**English claim.**  The vendored full-transaction checker for input `nIn` of
`tx` spending a known `amount` (`Bitcoin.TxValidation.Full.txCheckerFor tx nIn
(some amount)`) performs, at witness-v0, exactly the concrete vendor ECDSA
verification `Bitcoin.Crypto.Ecdsa.Verify.verifyImpl` over the model's BIP 143
digest `LnLean.Bitcoin.Sighash.sighashWitnessV0`.  Feeding the BOLT 3 funding
witness (`[dummy, sig1, sig2, witnessScript]`) through the vendored P2WSH
verifier at that checker returns `.ok` when both ordered funding keys verify,
and returns `.fail .evalFalse` when the second signature is rejected under the
ordered second funding key.

## What is instantiated, not assumed

* `txCheckerFor_checkECDSASignature_eq_checkerOf` — the local equality lemma
  between the `txCheckerFor` wiring and the wave-6 `checkerOf` wiring.  Both
  are `ecdsaVerdict` over the same `verifyImpl`; they differ only in the
  sighash function, which `Sighash.sighashWitnessV0_eq_interface` identifies.
  The lemma is unconditional (the `isValidPubKey`/empty-signature gates are
  shared), so no checker-shaped hypothesis is introduced anywhere below.
* `txCheckerFor_consumes_model_digest` — for a valid pubkey and a non-empty
  signature, the checker's witness-v0 verdict *is*
  `verifyImpl (sig minus hashtype) pk (sighashWitnessV0 ... amount)`.  The
  spent `amount`, the outpoint/`nSequence` of input `nIn`, and the scriptCode
  are the preimage fields of that digest (`funding_digest_commits_outpoint`,
  `digest_commits_amount`, `digest_commits_scriptCode`).
* `funding_txCheckerFor_verify_and_spend` — positive branch: the vendored
  `verifyWitnessProgram` at `txCheckerFor tx nIn (some amount)` returns `.ok`,
  and the wave-4 model `P2WSHSpend` holds at the same checker with the same
  digest.
* `funding_txCheckerFor_wrongKey_rejected` — negative branch: a funding
  witness whose second signature is rejected under the ordered second funding
  key is rejected by the vendored verifier (`.fail .evalFalse`) and is not an
  accepting model spend.

## Scope (no unconditional consensus claim)

`nIn` is a real input index (the digest uses `tx.vin[nIn]`; the out-of-range
case is BIP 143's zero digest).  The spent `amount` is a context parameter: the
digest commits to it, but this module does not prove it equals the referenced
outpoint's value.  The ECDSA verification itself is the concrete vendored
`verifyImpl` (C3's executable instantiation), so no abstract verifier remains
on this path — but the signature hypotheses are still hypotheses (nothing here
*constructs* a valid signature).  The `scriptLane`/`txVerdictFull` wrapping
(`verifyScriptFull`, P2SH/cleanstack/flag plumbing) is **not** covered here;
`txCheckerFor` is the boundary of this lane.  Amount-missing (`none`) fails
closed at the ECDSA entry (`txCheckerFor_none_witnessV0_false`).

## Anchors

* BOLT 3 §Funding Transaction Output (`refs/bolts/03-transactions.md:75-83`).
* BIP 141 (P2WSH), BIP 143 (witness-v0 sighash), BIP 147 (NULLDUMMY).
* `vendor/btc-lean-core/Bitcoin/TxValidation/Full.lean` (`txCheckerFor`),
  `Bitcoin/Crypto/Ecdsa/Verify/Verify.lean` (`verifyImpl`),
  `Bitcoin/Interpreter/Defs.lean` (`verifyWitnessProgram`).
-/

namespace LnLean.Proofs.WaveH.H30

set_option autoImplicit false

open Bitcoin.Data
open Bitcoin.Crypto.Seam
open LnLean
open LnLean.Bitcoin.Sighash
open LnLean.Proofs.Bitcoin.SighashBridgeTargets
open LnLean.Proofs.Bitcoin.SpendTargets
open LnLean.Proofs.Bitcoin.InterpreterBridgeTargets

/-! ## The model digest at the `txCheckerFor` wiring -/

/-- The vendored witness-v0 sighash dispatch of the real checker
(`Bitcoin.Capstone.RealChecker.sighashDispatch`, i.e. `signatureHashBip143`)
is the model digest `sighashWitnessV0`. -/
theorem realChecker_sighashDispatch_witnessV0 (tx : Tx) (nIn : Nat)
    (amount : Amount) (scriptCode : ByteArray) (ht : UInt8) :
    Bitcoin.Capstone.RealChecker.sighashDispatch tx nIn amount scriptCode ht
        .witnessV0 =
      LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn scriptCode
        (UInt32.ofNat ht.toNat) amount :=
  (LnLean.Bitcoin.Sighash.sighashWitnessV0_eq_interface tx nIn scriptCode
    (UInt32.ofNat ht.toNat) amount).symm

/-- **Local equality lemma.**  At witness-v0, the ECDSA entry of
`txCheckerFor tx nIn (some amount)` and of the wave-6 `checkerOf verifyImpl tx
nIn amount` agree for *every* signature, pubkey and scriptCode.  Both are
`ecdsaVerdict verifyImpl _ true`, so the `isValidPubKey` and empty-signature
gates coincide; the only remaining difference is the sighash function, which
`realChecker_sighashDispatch_witnessV0` identifies with the model digest.

The lemma is unconditional: it does not assume pubkey validity, a non-empty
signature, or any property of `verifyImpl`. -/
theorem txCheckerFor_checkECDSASignature_eq_checkerOf
    (tx : Tx) (nIn : Nat) (amount : Amount)
    (sig pk scriptCode : ByteArray) (ed : Bitcoin.Crypto.Seam.ScriptExecutionData) :
    (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount)).base.checkECDSASignature sig pk scriptCode .witnessV0 ed =
      (LnLean.Proofs.Bitcoin.SighashBridgeTargets.checkerOf
          Bitcoin.Crypto.Ecdsa.Verify.verifyImpl tx nIn amount).base.checkECDSASignature sig pk scriptCode .witnessV0 ed := by
  rw [LnLean.Proofs.Bitcoin.SighashBridgeTargets.checkerOf_base]
  simp only [Bitcoin.TxValidation.Full.txCheckerFor,
    Bitcoin.Crypto.Seam.Entry.txCheckerOf_ecdsa,
    Bitcoin.Crypto.Seam.Entry.ecdsaEntry, Bitcoin.Crypto.Seam.Entry.ecdsaVerdict,
    LnLean.Proofs.Bitcoin.SighashBridgeTargets.sighashDispatch]
  rw [realChecker_sighashDispatch_witnessV0]
  rfl

/-- **The checker consumes the model digest.**  For a valid pubkey and a
non-empty signature, the `txCheckerFor` witness-v0 verdict is the concrete
vendor verifier applied to the signature body (minus its hashtype byte) and
the model BIP 143 digest.  The spent `amount` and the transaction/input
context are the digest's own preimage fields. -/
theorem txCheckerFor_consumes_model_digest
    (tx : Tx) (nIn : Nat) (amount : Amount)
    (sig pk scriptCode : ByteArray) (ed : Bitcoin.Crypto.Seam.ScriptExecutionData)
    (hpk : Bitcoin.Crypto.Seam.Der.isValidPubKey pk = true)
    (hne : 0 < sig.size) :
    (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount)).base.checkECDSASignature sig pk scriptCode .witnessV0 ed =
      Bitcoin.Crypto.Ecdsa.Verify.verifyImpl (sig.extract 0 (sig.size - 1)) pk
        (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn scriptCode
          (hashtypeOf sig) amount) := by
  rw [txCheckerFor_checkECDSASignature_eq_checkerOf]
  exact LnLean.Proofs.Bitcoin.SighashBridgeTargets.checker_consumes_model_digest
    Bitcoin.Crypto.Ecdsa.Verify.verifyImpl tx nIn amount sig pk scriptCode ed hpk hne

/-- The missing-amount (`none`) wiring fails closed at the witness-v0 ECDSA
entry: `hasAmount = false` and the witness-v0 branch is a reject, before any
`verifyImpl` call.  This is the amount premise of the positive theorem made
explicit as a negative. -/
theorem txCheckerFor_none_witnessV0_false
    (tx : Tx) (nIn : Nat) (sig pk scriptCode : ByteArray)
    (ed : Bitcoin.Crypto.Seam.ScriptExecutionData)
    (hpk : Bitcoin.Crypto.Seam.Der.isValidPubKey pk = true)
    (hne : 0 < sig.size) :
    (Bitcoin.TxValidation.Full.txCheckerFor tx nIn none).base.checkECDSASignature sig pk scriptCode .witnessV0 ed = false := by
  simp only [Bitcoin.TxValidation.Full.txCheckerFor, Option.getD_none,
    Option.isSome_none]
  rw [Bitcoin.Crypto.Seam.Entry.txCheckerOf_ecdsa]
  simp only [Bitcoin.Crypto.Seam.Entry.ecdsaEntry,
    Bitcoin.Crypto.Seam.Entry.ecdsaVerdict]
  rw [if_neg (by simp [hpk]), if_neg (by omega), if_pos (by simp)]

/-! ## The funding digest commits to the amount, outpoint and scriptCode -/

/-- The digest's preimage carries the `nIn`-th input's outpoint.  This is the
outpoint premise of the funding spend made explicit: the digest is bound to
the coin being spent, not only to the funding key set. -/
theorem funding_digest_commits_outpoint
    (tx : Tx) (nIn : Nat) (i : Bitcoin.Data.TxIn) (hout : tx.vin[nIn]? = some i)
    (scriptCode : ByteArray) (ht : UInt32) (amount : Amount) :
    (LnLean.Bitcoin.Sighash.ofTx tx nIn scriptCode ht amount).outpoint =
      i.prevout := by
  unfold LnLean.Bitcoin.Sighash.ofTx
  rw [List.getD_eq_getElem?_getD, hout]
  rfl

/-- The digest's preimage carries the spent amount (a committed field, not
hidden state). -/
theorem funding_digest_commits_amount (tx : Tx) (nIn : Nat)
    (scriptCode : ByteArray) (ht : UInt32) (amount : Amount) :
    (LnLean.Bitcoin.Sighash.ofTx tx nIn scriptCode ht amount).amount = amount :=
  rfl

/-- The digest's preimage carries the funding witness script as its
scriptCode (BIP 143 witness-v0 hashes the witness script directly). -/
theorem funding_digest_commits_scriptCode (tx : Tx) (nIn : Nat)
    (scriptCode : ByteArray) (ht : UInt32) (amount : Amount) :
    (LnLean.Bitcoin.Sighash.ofTx tx nIn scriptCode ht amount).scriptCode =
      scriptCode :=
  rfl

/-! ## Funding scriptCode and the concrete signature hypotheses -/

/-- The BOLT 3 funding witness script bytes, as the interpreter's opcode
serializer writes them. -/
def fundingScriptCode (a b : PubKey) : ByteArray :=
  Bitcoin.Script.Parser.serializeOpcodes (fundingOps a b)

/-- The digest committed by the funding spend for signature `sig`, the
ordered keys `a`/`b` and the spent `amount`. -/
def fundingDigest (tx : Tx) (nIn : Nat) (a b : PubKey) (sig : ByteArray)
    (amount : Amount) : ByteArray :=
  LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn (fundingScriptCode a b)
    (hashtypeOf sig) amount

/-- The concrete vendor ECDSA premise for one funding key: `verifyImpl` accepts
`sig`'s body under `pk` over the funding digest. -/
def FundingSigOK (tx : Tx) (nIn : Nat) (a b pk : PubKey) (sig : ByteArray)
    (amount : Amount) : Prop :=
  Bitcoin.Crypto.Ecdsa.Verify.verifyImpl (sig.extract 0 (sig.size - 1)) pk.bytes
    (fundingDigest tx nIn a b sig amount) = true

/-! ## Positive branch: the 2-of-2 funding spend at `txCheckerFor` -/

/-- **Positive funding spend at the real checker.**  Given

* a resolved `amount` (the `some amount` argument of `txCheckerFor`),
* the committed P2WSH program `program` (the 32-byte script hash) and the
  explicit hash link `program = SHA256(funding witness script)`,
* two valid, non-empty DER-sized signatures `s1`/`s2` (≤ 520 bytes) accepted by
  the concrete vendor verifier under the ordered funding keys `a`/`b` over the
  model BIP 143 digest,

the vendored P2WSH verifier at `txCheckerFor tx nIn (some amount)` returns
`.ok`, and the wave-4 model `P2WSHSpend` holds at the same checker.  The model
spend is stated with the digest of `s1` as its `msg`; the two signature
premises are exactly the two `verifyImpl` calls above (each signature carries
its own hashtype, hence its own digest). -/
theorem funding_txCheckerFor_verify_and_spend
    (tx : Tx) (nIn : Nat) (amount : Amount)
    (a b : PubKey) (s1 s2 dummy : ByteArray) (program : ByteArray)
    (ha : a.bytes.size = 33) (hb : b.bytes.size = 33)
    (hs1 : s1.size ≤ 520) (hs2 : s2.size ≤ 520) (hdu : dummy.size ≤ 520)
    (hpka : Bitcoin.Crypto.Seam.Der.isValidPubKey a.bytes = true)
    (hpkb : Bitcoin.Crypto.Seam.Der.isValidPubKey b.bytes = true)
    (hne1 : 0 < s1.size) (hne2 : 0 < s2.size)
    (hps : program.size = 32)
    (hprog : Bitcoin.Interpreter.hashSha256 (Bitcoin.Script.Parser.serializeOpcodes (fundingOps a b)) = program)
    (h1 : FundingSigOK tx nIn a b a s1 amount)
    (h2 : FundingSigOK tx nIn a b b s2 amount) :
    Bitcoin.Interpreter.verifyWitnessProgram 6
        [dummy, s1, s2, Bitcoin.Script.Parser.serializeOpcodes (fundingOps a b)] 0 program
        ({} : Bitcoin.Activation.ScriptFlags)
        ({} : Bitcoin.Interpreter.PolicyFlags)
        (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount)) false = .ok ∧
      LnLean.Proofs.Bitcoin.SpendTargets.P2WSHSpend
        (vendorLaws (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount))
          (Bitcoin.Script.Parser.serializeOpcodes (fundingOps a b)))
        (fundingDigest tx nIn a b s1 amount) program (Bitcoin.Script.Parser.serializeOpcodes (fundingOps a b))
        (fundingProg a b) [s2, s1, dummy] := by
  have hc1 : (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount)).base.checkECDSASignature s1 a.bytes (Bitcoin.Script.Parser.serializeOpcodes (fundingOps a b)) .witnessV0
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true := by
    rw [txCheckerFor_consumes_model_digest tx nIn amount s1 a.bytes
      (Bitcoin.Script.Parser.serializeOpcodes (fundingOps a b)) default hpka hne1]
    exact h1
  have hc2 : (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount)).base.checkECDSASignature s2 b.bytes (Bitcoin.Script.Parser.serializeOpcodes (fundingOps a b)) .witnessV0
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true := by
    rw [txCheckerFor_consumes_model_digest tx nIn amount s2 b.bytes
      (Bitcoin.Script.Parser.serializeOpcodes (fundingOps a b)) default hpkb hne2]
    exact h2
  have hagree := funding_interpreters_agree
    (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount))
    (fundingDigest tx nIn a b s1 amount) a b s1 s2 dummy ha hb hs1 hs2 hdu hc1 hc2
  refine ⟨?_, ?_⟩
  · exact verifyWitnessProgram_funding
      (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount))
      a b s1 s2 dummy program ha hb hs1 hs2 hdu hps hprog hc1 hc2
  · simpa only [hprog] using hagree.2


/-! ## Negative branch: a wrong-key second signature is rejected -/

/-- Vendored `OP_CHECKMULTISIG` for the funding stack with a rejected second
signature: the loop short-circuits to `false` (a failing signature consumes a
key without consuming a signature, so `nSigs > nKeys` ends the loop), the
argument-cleanup pop leaves the dummy item, and the opcode pushes the canonical
`false` (`vchFalse`, the empty element). -/
theorem checkMultiSig_two_of_two_bad_sig (chk : Bitcoin.Interpreter.ScriptChecker)
    (scriptCode a b s1 s2 dummy : ByteArray)
    (h2 : chk.base.checkECDSASignature s2 b scriptCode .witnessV0
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = false) :
    Bitcoin.Interpreter.stepBody.checkMultiSig
      { flags := ({} : Bitcoin.Activation.ScriptFlags),
        pol := ({} : Bitcoin.Interpreter.PolicyFlags), chk := chk,
        sv := .witnessV0, bytes := scriptCode,
        ed := (default : Bitcoin.Crypto.Seam.ScriptExecutionData) }
      0xae
      { stack := [ByteArray.mk #[0x02], b, a, ByteArray.mk #[0x02], s2, s1, dummy],
        alt := [], vf := [], opCount := 1, codeSep := 0, vwLeft := none }
    = Except.ok
        { stack := [ByteArray.empty], alt := [], vf := [], opCount := 3,
          codeSep := 0, vwLeft := none } := by
  simp [Bitcoin.Interpreter.stepBody.checkMultiSig,
    Bitcoin.Interpreter.cmsLoop, Bitcoin.Interpreter.cmsCleanup,
    Bitcoin.Interpreter.checkSigEncoding, Bitcoin.Interpreter.checkPubKeyEncoding,
    Bitcoin.Interpreter.topAt, h2, decodeNum_two,
    Bitcoin.Interpreter.MAX_PUBKEYS_PER_MULTISIG,
    Bitcoin.Interpreter.MAX_OPS_PER_SCRIPT, List.range_succ,
    Bitcoin.Interpreter.pushBoolV, Bitcoin.Interpreter.vchFalse]

/-- Vendored evaluation of the funding script with a rejected second
signature: the final stack is the canonical `false`. -/
theorem evalFrom_fundingWireOps_bad_sig (chk : Bitcoin.Interpreter.ScriptChecker)
    (scriptCode : ByteArray) (a b : PubKey) (s1 s2 dummy : ByteArray)
    (ha : a.bytes.size = 33) (hb : b.bytes.size = 33)
    (h2 : chk.base.checkECDSASignature s2 b.bytes scriptCode .witnessV0
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = false) :
    Bitcoin.Interpreter.evalFrom
      { flags := ({} : Bitcoin.Activation.ScriptFlags),
        pol := ({} : Bitcoin.Interpreter.PolicyFlags), chk := chk,
        sv := .witnessV0, bytes := scriptCode,
        ed := (default : Bitcoin.Crypto.Seam.ScriptExecutionData) }
      6 (fundingWireOps a b)
      { stack := [s2, s1, dummy], alt := [], vf := [], opCount := 0,
        codeSep := 0, vwLeft := none }
    = Except.ok
        { stack := [ByteArray.empty], alt := [], vf := [], opCount := 3,
          codeSep := 0, vwLeft := none } := by
  simp [fundingWireOps, Bitcoin.Interpreter.evalFrom,
    Bitcoin.Interpreter.stepChecked, Bitcoin.Interpreter.stepBody,
    Bitcoin.Interpreter.stepBody.dispatchOp,
    checkMultiSig_two_of_two_bad_sig chk scriptCode a.bytes b.bytes s1 s2 dummy h2,
    Bitcoin.Interpreter.disabledWire,
    Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE,
    encodeScriptNum_two,
    Bitcoin.Interpreter.MAX_OPS_PER_SCRIPT, Bitcoin.Interpreter.MAX_STACK_SIZE,
    ha, hb]

/-- `EvalScript` on the funding script bytes with a rejected second signature
leaves the canonical `false` stack. -/
theorem evalScriptBytes_funding_bad_sig (chk : Bitcoin.Interpreter.ScriptChecker)
    (a b : PubKey) (s1 s2 dummy : ByteArray)
    (ha : a.bytes.size = 33) (hb : b.bytes.size = 33)
    (h2 : chk.base.checkECDSASignature s2 b.bytes (Bitcoin.Script.Parser.serializeOpcodes (fundingOps a b))
      .witnessV0 (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = false) :
    Bitcoin.Interpreter.evalScriptBytes 6
      ({} : Bitcoin.Activation.ScriptFlags)
      ({} : Bitcoin.Interpreter.PolicyFlags)
      (Bitcoin.Script.Parser.serializeOpcodes (fundingOps a b)) [s2, s1, dummy] chk .witnessV0
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData)
    = Except.ok [ByteArray.empty] := by
  unfold Bitcoin.Interpreter.evalScriptBytes
  have hsz : (Bitcoin.Script.Parser.serializeOpcodes (fundingOps a b)).size = 71 := by
    simp [fundingOps, Bitcoin.Script.Parser.serializeOpcodes,
      Bitcoin.Script.Parser.serializeOpcode, Bitcoin.Script.Parser.pushBytesWire,
      Bitcoin.Script.Parser.lenBytes, ha, hb]
  rw [if_neg (by simp [hsz, Bitcoin.Interpreter.MAX_SCRIPT_SIZE])]
  rw [funding_parseWire a b ha hb]
  simp [Bitcoin.Interpreter.finalStack,
    evalFrom_fundingWireOps_bad_sig chk (Bitcoin.Script.Parser.serializeOpcodes (fundingOps a b)) a b s1 s2 dummy
      ha hb h2]

/-- The witness-script execution rejects the bad-second-signature funding
witness with `.fail .evalFalse` (the implicit witness cleanstack test). -/
theorem executeWitnessScript_funding_bad_sig (chk : Bitcoin.Interpreter.ScriptChecker)
    (a b : PubKey) (s1 s2 dummy : ByteArray) (vwSer : Int)
    (ha : a.bytes.size = 33) (hb : b.bytes.size = 33)
    (hs1 : s1.size ≤ 520) (hs2 : s2.size ≤ 520) (hdu : dummy.size ≤ 520)
    (h2 : chk.base.checkECDSASignature s2 b.bytes (Bitcoin.Script.Parser.serializeOpcodes (fundingOps a b))
      .witnessV0 (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = false) :
    Bitcoin.Interpreter.executeWitnessScript 6 [dummy, s1, s2] vwSer
      (Bitcoin.Script.Parser.serializeOpcodes (fundingOps a b)) ({} : Bitcoin.Activation.ScriptFlags)
      ({} : Bitcoin.Interpreter.PolicyFlags) chk .witnessV0 = .fail .evalFalse := by
  have hs1' : ¬ Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE < s1.size := by
    unfold Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE; omega
  have hs2' : ¬ Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE < s2.size := by
    unfold Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE; omega
  have hdu' : ¬ Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE < dummy.size := by
    unfold Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE; omega
  simp [Bitcoin.Interpreter.executeWitnessScript,
    Bitcoin.Interpreter.executeWitnessScript.runExec,
    evalScriptBytes_funding_bad_sig chk a b s1 s2 dummy ha hb h2,
    hs1', hs2', hdu', Bitcoin.Numeric.castToBool]
  decide

/-- The full P2WSH verifier rejects the wrong-key funding witness with
`.fail .evalFalse`. -/
theorem verifyWitnessProgram_funding_bad_sig (chk : Bitcoin.Interpreter.ScriptChecker)
    (a b : PubKey) (s1 s2 dummy : ByteArray) (program : ByteArray)
    (ha : a.bytes.size = 33) (hb : b.bytes.size = 33)
    (hs1 : s1.size ≤ 520) (hs2 : s2.size ≤ 520) (hdu : dummy.size ≤ 520)
    (hps : program.size = 32)
    (hprog : Bitcoin.Interpreter.hashSha256 (Bitcoin.Script.Parser.serializeOpcodes (fundingOps a b)) = program)
    (h2 : chk.base.checkECDSASignature s2 b.bytes (Bitcoin.Script.Parser.serializeOpcodes (fundingOps a b))
      .witnessV0 (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = false) :
    Bitcoin.Interpreter.verifyWitnessProgram 6
      [dummy, s1, s2, Bitcoin.Script.Parser.serializeOpcodes (fundingOps a b)] 0 program
      ({} : Bitcoin.Activation.ScriptFlags)
      ({} : Bitcoin.Interpreter.PolicyFlags) chk false = .fail .evalFalse := by
  simp [Bitcoin.Interpreter.verifyWitnessProgram, hps, hprog,
    byteArray_bne_self,
    executeWitnessScript_funding_bad_sig chk a b s1 s2 dummy
      (Bitcoin.Interpreter.witnessSerSize
        [dummy, s1, s2, Bitcoin.Script.Parser.serializeOpcodes (fundingOps a b)]) ha hb hs1 hs2 hdu h2]

/-- **Wrong-key negative at the real checker.**  If the first signature is
accepted under the ordered first funding key `a` and the second signature is
rejected by the concrete vendor verifier under the ordered second funding key
`b` (the wrong-key case: `s2` is not a signature by `b`), then

* the vendored P2WSH verifier at `txCheckerFor tx nIn (some amount)` returns
  `.fail .evalFalse`, and
* the model `Accepts` predicate is false for the same funding program.

The amount, outpoint, script-hash and signature premises are exactly those of
`funding_txCheckerFor_verify_and_spend`. -/
theorem funding_txCheckerFor_wrongKey_rejected
    (tx : Tx) (nIn : Nat) (amount : Amount)
    (a b : PubKey) (s1 s2 dummy : ByteArray) (program : ByteArray)
    (ha : a.bytes.size = 33) (hb : b.bytes.size = 33)
    (hs1 : s1.size ≤ 520) (hs2 : s2.size ≤ 520) (hdu : dummy.size ≤ 520)
    (hpka : Bitcoin.Crypto.Seam.Der.isValidPubKey a.bytes = true)
    (hpkb : Bitcoin.Crypto.Seam.Der.isValidPubKey b.bytes = true)
    (hne1 : 0 < s1.size) (hne2 : 0 < s2.size)
    (hps : program.size = 32)
    (hprog : Bitcoin.Interpreter.hashSha256 (Bitcoin.Script.Parser.serializeOpcodes (fundingOps a b)) = program)
    (h1 : FundingSigOK tx nIn a b a s1 amount)
    (h2bad : ¬ FundingSigOK tx nIn a b b s2 amount) :
    Bitcoin.Interpreter.verifyWitnessProgram 6
        [dummy, s1, s2, Bitcoin.Script.Parser.serializeOpcodes (fundingOps a b)] 0 program
        ({} : Bitcoin.Activation.ScriptFlags)
        ({} : Bitcoin.Interpreter.PolicyFlags)
        (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount)) false
      = .fail .evalFalse ∧
      ¬ Accepts
        (vendorLaws (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount))
          (Bitcoin.Script.Parser.serializeOpcodes (fundingOps a b)))
        (fundingDigest tx nIn a b s1 amount) (fundingProg a b) [s2, s1, dummy] := by
  have hc1 : (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount)).base.checkECDSASignature s1 a.bytes (Bitcoin.Script.Parser.serializeOpcodes (fundingOps a b)) .witnessV0
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true := by
    rw [txCheckerFor_consumes_model_digest tx nIn amount s1 a.bytes
      (Bitcoin.Script.Parser.serializeOpcodes (fundingOps a b)) default hpka hne1]
    exact h1
  have hc2 : (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount)).base.checkECDSASignature s2 b.bytes (Bitcoin.Script.Parser.serializeOpcodes (fundingOps a b)) .witnessV0
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = false := by
    rw [txCheckerFor_consumes_model_digest tx nIn amount s2 b.bytes
      (Bitcoin.Script.Parser.serializeOpcodes (fundingOps a b)) default hpkb hne2]
    have h2false : Bitcoin.Crypto.Ecdsa.Verify.verifyImpl
        (s2.extract 0 (s2.size - 1)) b.bytes
        (fundingDigest tx nIn a b s2 amount) = false := by
      cases hv : Bitcoin.Crypto.Ecdsa.Verify.verifyImpl
          (s2.extract 0 (s2.size - 1)) b.bytes
          (fundingDigest tx nIn a b s2 amount)
      · rfl
      · exact absurd hv h2bad
    exact h2false
  refine ⟨?_, ?_⟩
  · exact verifyWitnessProgram_funding_bad_sig
      (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount))
      a b s1 s2 dummy program ha hb hs1 hs2 hdu hps hprog hc2
  · have hsig : (vendorLaws
        (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount))
        (Bitcoin.Script.Parser.serializeOpcodes (fundingOps a b))).sigCheck b.bytes
        (fundingDigest tx nIn a b s1 amount) s2 = false := by
      simpa [vendorLaws] using hc2
    have hsig1 : (vendorLaws
        (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount))
        (Bitcoin.Script.Parser.serializeOpcodes (fundingOps a b))).sigCheck a.bytes
        (fundingDigest tx nIn a b s1 amount) s1 = true := by
      simpa [vendorLaws] using hc1
    exact not_accepts_funding_one_signature
      (vendorLaws (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount))
        (Bitcoin.Script.Parser.serializeOpcodes (fundingOps a b)))
      (fundingDigest tx nIn a b s1 amount) a b dummy s1 s2 hsig1 hsig

/-! ## Axiom pins -/

#print axioms txCheckerFor_checkECDSASignature_eq_checkerOf
#print axioms txCheckerFor_consumes_model_digest
#print axioms txCheckerFor_none_witnessV0_false
#print axioms funding_digest_commits_outpoint
#print axioms funding_txCheckerFor_verify_and_spend
#print axioms checkMultiSig_two_of_two_bad_sig
#print axioms evalFrom_fundingWireOps_bad_sig
#print axioms evalScriptBytes_funding_bad_sig
#print axioms executeWitnessScript_funding_bad_sig
#print axioms verifyWitnessProgram_funding_bad_sig
#print axioms funding_txCheckerFor_wrongKey_rejected

end LnLean.Proofs.WaveH.H30
