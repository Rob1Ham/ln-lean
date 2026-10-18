import Bitcoin.Crypto.Ecdsa.Verify
import Bitcoin.Capstone.RealChecker
import LnLean.Proofs.Bitcoin.SighashBridgeTargets
import LnLean.Proofs.Bitcoin.InterpreterRevocationTargets

/-!
# Sequence/context refinement for the `to_local` delayed branch

Wave 7 (lane `S7-L1-SEQUENCE`) companion of the vendored-interpreter bridges
`InterpreterBridgeTargets` (wave 5), `InterpreterRevocationTargets` (wave 6)
and `SighashBridgeTargets` (wave 6).  The earlier bridges state the delayed
`to_local` agreement under an abstract decoded `ScriptNum` `n`, an abstract
non-negativity proof, an abstract operand disable-bit proof, and the vendored
`checkSequenceDef`.  This module removes those abstraction layers for the
faithful BOLT 3 encoding:

* the two-byte little-endian `to_self_delay` payload `delayBytes csv` decodes
  (under the default, non-minimal-data policy) to exactly `(csv : Int)` for
  every `csv < 32768` (`decodeNum_delayBytes`);
* that decoded value is non-negative and has a clear operand disable bit;
* the vendored `checkSequenceDef` is characterized completely as
  “version ≥ 2 ∧ transaction disable bit clear ∧ same `TYPE_FLAG` domain ∧
  `csv ≤` the masked transaction sequence” (`checkSequenceDef_delay_iff`);
* the vendor’s full P2WSH verdict on the delayed witness is `.ok` **iff** the
  sequence check and the delayed-key ECDSA check both succeed
  (`toLocal_delayed_sequence_vendor_iff`), with a mechanized failure for the
  bad-signature case (`..._delayed_bad_sig`);
* the same equivalence is instantiated at the concrete checker
  `checkerOf Bitcoin.Crypto.Ecdsa.Verify.verifyImpl`, replacing the opaque
  ECDSA hypothesis by the explicit verifier call over the BIP 143 model
  digest (`toLocal_delayed_checkerOf_refinement`).

Policy and activation boundaries are also recorded: `decodeNum` depends on
the policy flags only through `minimalData`; with `minimalData = false`
(the default) every `csv < 32768` decodes; the consensus `csv` flag is on at
and above `CSV_HEIGHT`; and with `flags.csv = false` the `OP_CSV` dispatch is
a no-op.
-/

namespace LnLean.Proofs.Bitcoin.SequenceContextTargets

set_option autoImplicit false

open Bitcoin.Data
open Bitcoin.Activation
open Bitcoin.Script.Parser
open Bitcoin.Interpreter
open Bitcoin.Numeric
open LnLean
open LnLean.Bitcoin
open LnLean.Proofs.Bitcoin.SpendTargets
open LnLean.Proofs.Bitcoin.InterpreterBridgeTargets
open LnLean.Proofs.Bitcoin.InterpreterRevocationTargets
open LnLean.Proofs.Bitcoin.SighashBridgeTargets

/-! ## 1. Decoding the faithful two-byte delay -/

/-- The bytes of the fixed-width little-endian delay, as `Nat` digits in wire
order. -/
theorem bytesOf_delayBytes (csv : Nat) :
    bytesOf (delayBytes csv) = [csv % 256, (csv >>> 8) % 256] := by
  unfold delayBytes toLocalDelayBytes
  rw [bytesOf_push, bytesOf_push]
  simp [bytesOf, UInt8.toNat_ofNat']

/-- The sign-magnitude decoder reads the two-byte delay as the natural
`csv`, for every value below `2^15` (so the high byte is below `128` and is
not mistaken for a sign byte). -/
theorem setVchBE_delay (csv : Nat) (hcsv : csv < 32768) :
    setVchBE [(csv >>> 8) % 256, csv % 256] = (csv : Int) := by
  have hdiv : csv >>> 8 = csv / 256 := Nat.shiftRight_eq_div_pow csv 8
  have hd : (csv >>> 8) % 256 < 128 := by
    rw [hdiv]
    have h2 : csv / 256 % 256 = csv / 256 := Nat.mod_eq_of_lt (by omega)
    omega
  have hd' : (csv >>> 8) % 256 = csv / 256 := by
    rw [hdiv]
    exact Nat.mod_eq_of_lt (by omega)
  simp only [setVchBE, hd, ite_true, magOfBE, List.length_cons, List.length_nil,
    Nat.zero_add, Nat.reducePow, Nat.mul_one, Nat.add_zero]
  rw [hd']
  rw [show (csv / 256 * 256 + csv % 256) = csv by
    rw [Nat.mul_comm]
    exact Nat.div_add_mod csv 256]

/-- `decodeBE` succeeds on the reversed delay bytes and returns `csv`. -/
theorem decodeBE_delay (csv : Nat) (hcsv : csv < 32768) :
    decodeBE false 5 (bytesOf (delayBytes csv)).reverse = some (csv : Int) := by
  rw [bytesOf_delayBytes]
  have hlen : ([(csv >>> 8) % 256, csv % 256] : List Nat).length ≤ 5 := by simp
  rw [show (([csv % 256, (csv >>> 8) % 256] : List Nat).reverse) =
      [(csv >>> 8) % 256, csv % 256] by rfl]
  rw [decodeBE_some hlen (Or.inl rfl), setVchBE_delay csv hcsv]

/-- **Policy coverage.**  With `minimalData = false`, the CScriptNum decode of
the delay payload is exactly the original `csv`, with no other policy input
consumed.  This is the policy form of the delayed-branch decode hypothesis. -/
theorem decodeNum_delayBytes_of_minimalData_false (pol : PolicyFlags)
    (hmin : pol.minimalData = false) (csv : Nat) (hcsv : csv < 32768) :
    decodeNum pol (delayBytes csv) 5 = .ok (csv : Int) := by
  rw [decodeNum, decodeScriptNum, hmin, decodeBE_delay csv hcsv]

/-- Default-policy decode: the bridge hypotheses `n = (csv : Int)`,
`0 ≤ n`, and `n &&& disable = 0` are all derived below from `csv < 32768`
alone. -/
theorem decodeNum_delayBytes (csv : Nat) (hcsv : csv < 32768) :
    decodeNum ({} : PolicyFlags) (delayBytes csv) 5 = .ok (csv : Int) :=
  decodeNum_delayBytes_of_minimalData_false _ (by decide) csv hcsv

/-- `decodeNum` depends on the policy word only through `minimalData`. -/
theorem decodeNum_policy_congr (pol pol' : PolicyFlags)
    (h : pol.minimalData = pol'.minimalData) (b : ByteArray) (m : Nat) :
    decodeNum pol b m = decodeNum pol' b m := by
  simp [decodeNum, decodeScriptNum, h]

/-- The decoded delay is non-negative. -/
theorem nonneg_delay (csv : Nat) : 0 ≤ (csv : Int) := Int.natCast_nonneg csv

/-- The decoded delay has a clear BIP 68 operand disable bit. -/
theorem disableBit_delay (csv : Nat) (hcsv : csv < 32768) :
    Int.toNat (csv : Int) &&& SEQUENCE_LOCKTIME_DISABLE_FLAG = 0 := by
  rw [Int.toNat_natCast]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and]
  have hF : SEQUENCE_LOCKTIME_DISABLE_FLAG = 2 ^ 31 := by decide
  rw [hF, Nat.testBit_two_pow]
  by_cases hj : j = 31
  · subst hj
    have hc : csv.testBit 31 = false := by
      apply Nat.testBit_lt_two_pow
      have : 2 ^ 15 ≤ 2 ^ 31 := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    rw [hc]
    rfl
  · have h31 : ¬ (31 = j) := by omega
    rw [decide_eq_false h31]
    simp

/-! ## 2. Characterizing the vendored sequence check -/

/-- `csv < 2^15` is already inside the BIP 68 value/type mask. -/
theorem and_mask_delay (csv : Nat) (hcsv : csv < 32768) :
    csv &&& (SEQUENCE_LOCKTIME_TYPE_FLAG ||| SEQUENCE_LOCKTIME_MASK) = csv := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, Nat.testBit_or]
  have hT : SEQUENCE_LOCKTIME_TYPE_FLAG = 2 ^ 22 := by decide
  have hM : SEQUENCE_LOCKTIME_MASK = 2 ^ 16 - 1 := by decide
  rw [hT, hM]
  by_cases hj : j < 16
  · have hm : (2 ^ 16 - 1 : Nat).testBit j = true := by
      rw [Nat.testBit_two_pow_sub_one]; exact decide_eq_true hj
    simp [hm]
  · have hc : csv.testBit j = false := by
      apply Nat.testBit_lt_two_pow
      have h2j : 2 ^ 16 ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    have hMj : (2 ^ 16 - 1 : Nat).testBit j = false := by
      rw [Nat.testBit_two_pow_sub_one]
      exact decide_eq_false_iff_not.mpr (by omega)
    simp [hc, hMj]

/-- The final Boolean expression of `checkSequenceDef`, after substituting the
decoded operand, is exactly “the transaction is in the same BIP 68 domain and
`csv ≤ txMasked`”. -/
theorem step_abstract (t csv : Nat) (hdom : csv < SEQUENCE_LOCKTIME_TYPE_FLAG) :
    (if (!decide ((t < SEQUENCE_LOCKTIME_TYPE_FLAG ∧ csv < SEQUENCE_LOCKTIME_TYPE_FLAG) ∨
          (t ≥ SEQUENCE_LOCKTIME_TYPE_FLAG ∧ csv ≥ SEQUENCE_LOCKTIME_TYPE_FLAG))) = true then
      false
     else !decide (csv > t)) = decide (t < SEQUENCE_LOCKTIME_TYPE_FLAG ∧ csv ≤ t) := by
  by_cases ht : t < SEQUENCE_LOCKTIME_TYPE_FLAG
  · have hD : ((t < SEQUENCE_LOCKTIME_TYPE_FLAG ∧ csv < SEQUENCE_LOCKTIME_TYPE_FLAG) ∨
          (t ≥ SEQUENCE_LOCKTIME_TYPE_FLAG ∧ csv ≥ SEQUENCE_LOCKTIME_TYPE_FLAG)) := Or.inl ⟨ht, hdom⟩
    rw [decide_eq_true hD]
    simp only [Bool.not_true, Bool.false_eq_true, ite_false]
    by_cases hle : csv ≤ t
    · have hG : ¬ csv > t := by omega
      rw [decide_eq_false hG, decide_eq_true (show t < SEQUENCE_LOCKTIME_TYPE_FLAG ∧ csv ≤ t from ⟨ht, hle⟩)]
      rfl
    · have hG : csv > t := by omega
      rw [decide_eq_true hG]
      rw [decide_eq_false (show ¬(t < SEQUENCE_LOCKTIME_TYPE_FLAG ∧ csv ≤ t) from by
        intro h; exact hle h.2)]
      rfl
  · have hD : ¬ ((t < SEQUENCE_LOCKTIME_TYPE_FLAG ∧ csv < SEQUENCE_LOCKTIME_TYPE_FLAG) ∨
          (t ≥ SEQUENCE_LOCKTIME_TYPE_FLAG ∧ csv ≥ SEQUENCE_LOCKTIME_TYPE_FLAG)) := by
      intro h
      rcases h with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact ht h1
      · omega
    rw [decide_eq_false hD]
    simp only [Bool.not_false, ite_true]
    rw [decide_eq_false (show ¬(t < SEQUENCE_LOCKTIME_TYPE_FLAG ∧ csv ≤ t) from by
      intro h; exact ht h.1)]

/-- **Exact characterization of the vendored sequence check** for the faithful
delay decoding.  The vendor accepts the delay `csv` exactly when the
transaction version is at least 2, the transaction input’s disable bit is
clear, the masked transaction sequence lives in the height (`TYPE_FLAG = 0`)
domain, and the delay is at most that masked sequence. -/
theorem checkSequenceDef_delay_iff (env : LocktimeEnv) (csv : Nat)
    (hcsv : csv < 32768) :
    checkSequenceDef env (csv : Int) = true ↔
      (¬ env.txVersion < 2) ∧
      (env.txSequence.toNat &&& SEQUENCE_LOCKTIME_DISABLE_FLAG) = 0 ∧
      (env.txSequence.toNat &&& (SEQUENCE_LOCKTIME_TYPE_FLAG ||| SEQUENCE_LOCKTIME_MASK)) <
        SEQUENCE_LOCKTIME_TYPE_FLAG ∧
      csv ≤ (env.txSequence.toNat &&& (SEQUENCE_LOCKTIME_TYPE_FLAG ||| SEQUENCE_LOCKTIME_MASK)) := by
  have hnm : ((csv : Int).toNat &&& (SEQUENCE_LOCKTIME_TYPE_FLAG ||| SEQUENCE_LOCKTIME_MASK)) = csv := by
    rw [Int.toNat_natCast]; exact and_mask_delay csv hcsv
  have hdom : csv < SEQUENCE_LOCKTIME_TYPE_FLAG := by
    have hT : SEQUENCE_LOCKTIME_TYPE_FLAG = 2 ^ 22 := by decide
    omega
  have hstep := step_abstract
    (env.txSequence.toNat &&& (SEQUENCE_LOCKTIME_TYPE_FLAG ||| SEQUENCE_LOCKTIME_MASK)) csv hdom
  unfold checkSequenceDef
  dsimp only
  rw [hnm, hstep]
  by_cases hv : env.txVersion < 2
  · simp [hv]
  · by_cases hdis : (env.txSequence.toNat &&& SEQUENCE_LOCKTIME_DISABLE_FLAG) = 0
    · simp [hv, hdis]
    · simp [hv, hdis]

/-! ## 3. The bad-signature delayed branch at every vendor entry point -/

/-- With a valid sequence check but a rejected delayed-key signature, the
vendor still executes the delayed branch to completion and pushes the
canonical `false`. -/
theorem evalFrom_toLocalWireOps_delayed_bad_sig (chk : ScriptChecker)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (n : ScriptNum)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hdec : decodeNum ({} : PolicyFlags) (delayBytes csv) 5 = .ok n)
    (hnn : 0 ≤ n)
    (hdis : Int.toNat n &&& SEQUENCE_LOCKTIME_DISABLE_FLAG = 0)
    (hseq : checkSequenceDef chk.env n = true)
    (hsig : chk.base.checkECDSASignature sig delayedPaymentKey.bytes
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      .witnessV0 (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = false) :
    evalFrom
      { flags := ({ csv := true } : ScriptFlags), pol := ({} : PolicyFlags), chk := chk,
        sv := .witnessV0,
        bytes := serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv),
        ed := (default : Bitcoin.Crypto.Seam.ScriptExecutionData) }
      10 (toLocalWireOps revocationKey delayedPaymentKey csv)
      { stack := [ByteArray.empty, sig], alt := [], vf := [], opCount := 0,
        codeSep := 0, vwLeft := none }
    = Except.ok
        { stack := [ByteArray.empty], alt := [], vf := [], opCount := 6,
          codeSep := 0, vwLeft := none } := by
  simp [toLocalWireOps, evalFrom, stepChecked, stepBody, stepBody.dispatchOp,
    evalChecksigDispatch, evalChecksigPreTapscript, checkSigEncoding, checkPubKeyEncoding,
    Bitcoin.Numeric.castToBool, Bitcoin.Numeric.castToBoolList,
    Bitcoin.Numeric.bytesOf, delayBytes, topAt, pushBoolV, vchFalse, serU8, disabledWire,
    Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE, MAX_STACK_SIZE, MAX_OPS_PER_SCRIPT,
    toLocalDelayBytes_size, hdis, hseq, hsig, hr, hd]
  rw [show decodeNum ({} : PolicyFlags) (toLocalDelayBytes csv) 5 = .ok n by
    simpa [delayBytes] using hdec]
  have hnlt : ¬ n < 0 := Int.not_lt.mpr hnn
  simp [hnlt, hdis, hseq, hsig, Bitcoin.Numeric.castToBoolList, empty_push_eq]

/-- Bad-signature delayed branch at the `EvalScript` entry point. -/
theorem evalScriptBytes_toLocal_delayed_bad_sig (chk : ScriptChecker)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (n : ScriptNum)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hdec : decodeNum ({} : PolicyFlags) (delayBytes csv) 5 = .ok n)
    (hnn : 0 ≤ n)
    (hdis : Int.toNat n &&& SEQUENCE_LOCKTIME_DISABLE_FLAG = 0)
    (hseq : checkSequenceDef chk.env n = true)
    (hsig : chk.base.checkECDSASignature sig delayedPaymentKey.bytes
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      .witnessV0 (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = false) :
    evalScriptBytes 10 ({ csv := true } : ScriptFlags) ({} : PolicyFlags)
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      [ByteArray.empty, sig] chk .witnessV0
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData)
    = Except.ok [ByteArray.empty] := by
  unfold evalScriptBytes
  have hsz : (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)).size = 77 :=
    serializeOpcodes_toLocal_size revocationKey delayedPaymentKey csv hr hd
  rw [ite_eq_right (by simp [hsz, MAX_SCRIPT_SIZE])]
  rw [toLocal_parseWire revocationKey delayedPaymentKey csv hr hd]
  simp [finalStack,
    evalFrom_toLocalWireOps_delayed_bad_sig chk revocationKey delayedPaymentKey csv
      sig n hr hd hdec hnn hdis hseq hsig]

/-- Bad-signature delayed branch fails the witness-script truthiness test. -/
theorem executeWitnessScript_toLocal_delayed_bad_sig (chk : ScriptChecker)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (n : ScriptNum) (vwSer : Int)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hdec : decodeNum ({} : PolicyFlags) (delayBytes csv) 5 = .ok n)
    (hnn : 0 ≤ n)
    (hdis : Int.toNat n &&& SEQUENCE_LOCKTIME_DISABLE_FLAG = 0)
    (hseq : checkSequenceDef chk.env n = true)
    (hsig : chk.base.checkECDSASignature sig delayedPaymentKey.bytes
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      .witnessV0 (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = false) :
    executeWitnessScript 10 [sig, ByteArray.empty] vwSer
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      ({ csv := true } : ScriptFlags) ({} : PolicyFlags) chk .witnessV0
    = .fail .evalFalse := by
  have hsig' : ¬ Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE < sig.size := by
    unfold Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE; omega
  simp [executeWitnessScript, executeWitnessScript.runExec,
    evalScriptBytes_toLocal_delayed_bad_sig chk revocationKey delayedPaymentKey csv sig n
      hr hd hdec hnn hdis hseq hsig,
    hsig', Bitcoin.Numeric.castToBool]
  decide

/-- Full P2WSH rejection of the bad-signature delayed witness. -/
theorem verifyWitnessProgram_toLocal_delayed_bad_sig (chk : ScriptChecker)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (n : ScriptNum) (program : ByteArray)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hdec : decodeNum ({} : PolicyFlags) (delayBytes csv) 5 = .ok n)
    (hnn : 0 ≤ n)
    (hdis : Int.toNat n &&& SEQUENCE_LOCKTIME_DISABLE_FLAG = 0)
    (hseq : checkSequenceDef chk.env n = true)
    (hsig : chk.base.checkECDSASignature sig delayedPaymentKey.bytes
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      .witnessV0 (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = false)
    (hps : program.size = 32)
    (hprog : hashSha256
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)) = program) :
    verifyWitnessProgram 10
      [sig, ByteArray.empty,
        serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)]
      0 program ({ csv := true } : ScriptFlags) ({} : PolicyFlags) chk false
    = .fail .evalFalse := by
  simp [verifyWitnessProgram, hps, hprog, byteArray_bne_self,
    executeWitnessScript_toLocal_delayed_bad_sig chk revocationKey delayedPaymentKey
      csv sig n
      (witnessSerSize [sig, ByteArray.empty,
        serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)])
      hr hd hsigsz hdec hnn hdis hseq hsig]

/-! ## 4. Exact vendor acceptance criterion -/

/-- **Vendor acceptance iff sequence plus signature.**  The full vendored
P2WSH verdict on the delayed `to_local` witness is `.ok` exactly when the
vendored sequence check accepts the decoded delay and the delayed-key ECDSA
check succeeds.  Both failure directions are mechanized above: a failing
sequence check yields `.fail .unsatisfiedLocktime`; a failing signature with
an accepting sequence check yields `.fail .evalFalse`. -/
theorem toLocal_delayed_vendor_iff (chk : ScriptChecker)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (n : ScriptNum) (program : ByteArray)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hdec : decodeNum ({} : PolicyFlags) (delayBytes csv) 5 = .ok n)
    (hnn : 0 ≤ n)
    (hdis : Int.toNat n &&& SEQUENCE_LOCKTIME_DISABLE_FLAG = 0)
    (hps : program.size = 32)
    (hprog : hashSha256
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)) = program) :
    verifyWitnessProgram 10
      [sig, ByteArray.empty,
        serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)]
      0 program ({ csv := true } : ScriptFlags) ({} : PolicyFlags) chk false = .ok ↔
      (checkSequenceDef chk.env n = true ∧
        chk.base.checkECDSASignature sig delayedPaymentKey.bytes
          (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
          .witnessV0 (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true) := by
  constructor
  · intro hok
    by_cases hseq : checkSequenceDef chk.env n = true
    · by_cases hsig : chk.base.checkECDSASignature sig delayedPaymentKey.bytes
          (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
          .witnessV0 (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true
      · exact ⟨hseq, hsig⟩
      · have hsigf : chk.base.checkECDSASignature sig delayedPaymentKey.bytes
            (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
            .witnessV0 (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = false := by
          cases h : chk.base.checkECDSASignature sig delayedPaymentKey.bytes
            (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
            .witnessV0 (default : Bitcoin.Crypto.Seam.ScriptExecutionData) <;> simp_all
        have hbad := verifyWitnessProgram_toLocal_delayed_bad_sig chk revocationKey
          delayedPaymentKey csv sig n program hr hd hsigsz hdec hnn hdis hseq hsigf hps hprog
        rw [hbad] at hok
        exact absurd hok (by simp)
    · have hfalse : checkSequenceDef chk.env n = false := by
        cases h : checkSequenceDef chk.env n with
        | false => rfl
        | true => exact absurd h hseq
      have hfail := verifyWitnessProgram_toLocal_delayed_csv_false chk revocationKey
        delayedPaymentKey csv sig n program hr hd hsigsz hdec hnn hdis hfalse hps hprog
      rw [hfail] at hok
      exact absurd hok (by simp)
  · intro ⟨hseq, hsig⟩
    exact verifyWitnessProgram_toLocal_delayed chk revocationKey delayedPaymentKey csv
      sig n program hr hd hsigsz hdec hnn hdis hseq hsig hps hprog

/-- **Sequence-only vendor criterion.**  For the faithful encoding, no
abstract decode/range/disable-bit hypotheses are needed: `csv < 32768`
supplies all three, and acceptance is the vendored sequence check on
`(csv : Int)` together with the delayed-key signature. -/
theorem toLocal_delayed_sequence_vendor_iff (chk : ScriptChecker)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (program : ByteArray) (hcsv : csv < 32768)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hps : program.size = 32)
    (hprog : hashSha256
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)) = program) :
    verifyWitnessProgram 10
      [sig, ByteArray.empty,
        serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)]
      0 program ({ csv := true } : ScriptFlags) ({} : PolicyFlags) chk false = .ok ↔
      (checkSequenceDef chk.env (csv : Int) = true ∧
        chk.base.checkECDSASignature sig delayedPaymentKey.bytes
          (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
          .witnessV0 (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true) :=
  toLocal_delayed_vendor_iff chk revocationKey delayedPaymentKey csv sig (csv : Int) program
    hr hd hsigsz (decodeNum_delayBytes csv hcsv) (nonneg_delay csv)
    (disableBit_delay csv hcsv) hps hprog

/-- **Sequence/context refinement.**  The vendor accepts the delayed witness
exactly when the concrete transaction context satisfies every BIP 68/112
condition — version ≥ 2, input disable bit clear, height domain, and
`csv ≤` masked input sequence — and the delayed-key signature verifies. -/
theorem toLocal_delayed_sequence_context_refinement (chk : ScriptChecker)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (program : ByteArray) (hcsv : csv < 32768)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hps : program.size = 32)
    (hprog : hashSha256
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)) = program) :
    verifyWitnessProgram 10
      [sig, ByteArray.empty,
        serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)]
      0 program ({ csv := true } : ScriptFlags) ({} : PolicyFlags) chk false = .ok ↔
      ((¬ chk.env.txVersion < 2) ∧
        (chk.env.txSequence.toNat &&& SEQUENCE_LOCKTIME_DISABLE_FLAG) = 0 ∧
        (chk.env.txSequence.toNat &&&
            (SEQUENCE_LOCKTIME_TYPE_FLAG ||| SEQUENCE_LOCKTIME_MASK)) <
          SEQUENCE_LOCKTIME_TYPE_FLAG ∧
        csv ≤ (chk.env.txSequence.toNat &&&
            (SEQUENCE_LOCKTIME_TYPE_FLAG ||| SEQUENCE_LOCKTIME_MASK)) ∧
        chk.base.checkECDSASignature sig delayedPaymentKey.bytes
          (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
          .witnessV0 (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true) := by
  rw [toLocal_delayed_sequence_vendor_iff chk revocationKey delayedPaymentKey csv sig
    program hcsv hr hd hsigsz hps hprog]
  rw [checkSequenceDef_delay_iff chk.env csv hcsv]
  constructor
  · intro ⟨⟨a, b, c, d⟩, e⟩
    exact ⟨a, b, c, d, e⟩
  · intro ⟨a, b, c, d, e⟩
    exact ⟨⟨a, b, c, d⟩, e⟩

/-- **Sequence-level positive agreement.**  The wave-5 positive delayed-branch
bridge, with all decode/range/disable-bit hypotheses discharged by
`csv < 32768`: vendor `.ok` and the model `P2WSHSpend` with the sequence law
`vendorLawsCSV` at `(csv : Int)` hold simultaneously. -/
theorem toLocal_delayed_sequence_interpreters_agree (chk : ScriptChecker)
    (msg : ByteArray) (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (program : ByteArray) (hcsv : csv < 32768)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hps : program.size = 32)
    (hprog : hashSha256
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)) = program)
    (hseq : checkSequenceDef chk.env (csv : Int) = true)
    (hsig : chk.base.checkECDSASignature sig delayedPaymentKey.bytes
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      .witnessV0 (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true) :
    verifyWitnessProgram 10
        [sig, ByteArray.empty,
          serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)]
        0 program ({ csv := true } : ScriptFlags) ({} : PolicyFlags) chk false = .ok ∧
      P2WSHSpend (vendorLawsCSV chk
          (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)) (csv : Int))
        msg
        (hashSha256
          (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)))
        (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
        (toLocalProg revocationKey delayedPaymentKey csv) [zeroByte, sig] := by
  have hdec := decodeNum_delayBytes csv hcsv
  have hnn := nonneg_delay csv
  have hdis := disableBit_delay csv hcsv
  exact ⟨verifyWitnessProgram_toLocal_delayed chk revocationKey delayedPaymentKey
      csv sig (csv : Int) program hr hd hsigsz hdec hnn hdis hseq hsig hps hprog,
    toLocal_model_spend_delayed chk msg revocationKey delayedPaymentKey csv sig
      (csv : Int) hr hd hdec hnn hdis hseq hsig⟩

/-! ## 5. Concrete EC and transaction context -/

/-- **Concrete checker refinement.**  Instantiate the context refinement at
`checkerOf Bitcoin.Crypto.Ecdsa.Verify.verifyImpl tx nIn amount`: the
environment is the transaction-derived `locktimeEnvOf`, and the opaque ECDSA
hypothesis becomes the explicit lax secp256k1 verifier call over the BIP 143
model digest `sighashWitnessV0`.  The pubkey-validity and non-empty-signature
hypotheses are exactly the ones needed to reach the EC math through the
vendored seam adapter. -/
theorem toLocal_delayed_checkerOf_refinement
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (program : ByteArray) (hcsv : csv < 32768)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hps : program.size = 32)
    (hprog : hashSha256
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)) = program)
    (hpk : Bitcoin.Crypto.Seam.Der.isValidPubKey delayedPaymentKey.bytes = true)
    (hne : 0 < sig.size) :
    verifyWitnessProgram 10
      [sig, ByteArray.empty,
        serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)]
      0 program ({ csv := true } : ScriptFlags) ({} : PolicyFlags)
      (checkerOf Bitcoin.Crypto.Ecdsa.Verify.verifyImpl tx nIn amount) false = .ok ↔
      ((¬ tx.version < 2) ∧
        ((tx.vin.getD nIn dummyTxIn).sequence.toNat &&&
            SEQUENCE_LOCKTIME_DISABLE_FLAG) = 0 ∧
        ((tx.vin.getD nIn dummyTxIn).sequence.toNat &&&
            (SEQUENCE_LOCKTIME_TYPE_FLAG ||| SEQUENCE_LOCKTIME_MASK)) <
          SEQUENCE_LOCKTIME_TYPE_FLAG ∧
        csv ≤ ((tx.vin.getD nIn dummyTxIn).sequence.toNat &&&
            (SEQUENCE_LOCKTIME_TYPE_FLAG ||| SEQUENCE_LOCKTIME_MASK)) ∧
        Bitcoin.Crypto.Ecdsa.Verify.verifyImpl (sig.extract 0 (sig.size - 1))
          delayedPaymentKey.bytes
          (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn
            (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
            (hashtypeOf sig) amount) = true) := by
  rw [toLocal_delayed_sequence_context_refinement
    (checkerOf Bitcoin.Crypto.Ecdsa.Verify.verifyImpl tx nIn amount)
    revocationKey delayedPaymentKey csv sig program hcsv hr hd hsigsz hps hprog]
  simp only [checkerOf_env, locktimeEnvOf_txVersion, locktimeEnvOf_txSequence]
  rw [bridge_ecdsa_hypothesis_iff_model_verify
    Bitcoin.Crypto.Ecdsa.Verify.verifyImpl tx nIn amount sig
    delayedPaymentKey.bytes
    (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
    (default : Bitcoin.Crypto.Seam.ScriptExecutionData) hpk hne]

/-! ## 6. Policy and activation boundaries -/

/-- At and above `CSV_HEIGHT` the canonical block flag word enables CSV. -/
theorem getBlockScriptFlags_csv_of_csvHeight_le (height : UInt32)
    (h : CSV_HEIGHT ≤ height) :
    (getBlockScriptFlags height).csv = true := by
  unfold getBlockScriptFlags
  have hb : ((CSV_HEIGHT ≤ height) : Bool) = true := decide_eq_true h
  simp [hb]

/-- With `flags.csv = false` (pre-`CSV_HEIGHT` consensus), the `OP_CSV`
dispatch is a no-op on the state, independently of the decoded operand and
the transaction environment. -/
theorem dispatchOp_csv_disabled (ctx : Ctx) (st : State)
    (h : ctx.flags.csv = false) :
    stepBody.dispatchOp ctx { ast := .op ⟨0xb2, by decide⟩, wire := 0xb2, next := 0 }
      0xb2 (st.vf.all id) st = .ok st := by
  simp [stepBody.dispatchOp, h]

/-! ## 7. Transfer to the capstone real checker -/

/-- The model sighash dispatch coincides pointwise with the vendored
`RealChecker` dispatch: on witness-v0 both are the BIP 143 interface digest;
on every other signature version both are the legacy digest. -/
theorem sighashDispatch_eq_real (tx : Bitcoin.Data.Tx) (nIn : Nat)
    (amount : Amount) :
    sighashDispatch tx nIn amount =
      Bitcoin.Capstone.RealChecker.sighashDispatch tx nIn amount := by
  funext scriptCode ht sv
  cases sv with
  | base => rfl
  | witnessV0 =>
      simp [sighashDispatch, Bitcoin.Capstone.RealChecker.sighashDispatch,
        Bitcoin.Capstone.RealChecker.htToU32,
        LnLean.Bitcoin.Sighash.sighashWitnessV0_eq_interface]
  | taproot => rfl
  | tapscript => rfl

/-- For an in-range input, the model-digest checker `checkerOf verifyImpl` is
exactly the capstone `realCheckerOf`: both use the lax secp256k1 verifier and
the same transaction-derived locktime environment.  The dummy out-of-range
`TxIn` differs (sequence `0` versus `0xFFFFFFFF`), hence the hypothesis
`nIn < tx.vin.length`. -/
theorem checkerOf_eq_realCheckerOf (tx : Bitcoin.Data.Tx) (nIn : Nat)
    (amount : Amount) (hIn : nIn < tx.vin.length) :
    checkerOf Bitcoin.Crypto.Ecdsa.Verify.verifyImpl tx nIn amount =
      Bitcoin.Capstone.RealChecker.realCheckerOf tx nIn amount := by
  have hseq : (tx.vin.getD nIn dummyTxIn).sequence =
      (tx.vin.getD nIn Bitcoin.Capstone.RealChecker.dummyTxIn).sequence := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hIn]
    simp
  simp [checkerOf, Bitcoin.Capstone.RealChecker.realCheckerOf,
    Bitcoin.Capstone.RealChecker.realEcdsaEntry, locktimeEnvOf,
    sighashDispatch_eq_real, hseq, List.getElem?_eq_getElem hIn]

/-- **Real-checker refinement.**  Transfer the concrete checker refinement to
the capstone `realCheckerOf`, i.e. the actual lax secp256k1 wiring used by the
transaction-validity pipeline, for an in-range signing input. -/
theorem toLocal_delayed_realChecker_refinement
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount)
    (hIn : nIn < tx.vin.length)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (program : ByteArray) (hcsv : csv < 32768)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hps : program.size = 32)
    (hprog : hashSha256
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)) = program)
    (hpk : Bitcoin.Crypto.Seam.Der.isValidPubKey delayedPaymentKey.bytes = true)
    (hne : 0 < sig.size) :
    verifyWitnessProgram 10
      [sig, ByteArray.empty,
        serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)]
      0 program ({ csv := true } : ScriptFlags) ({} : PolicyFlags)
      (Bitcoin.Capstone.RealChecker.realCheckerOf tx nIn amount) false = .ok ↔
      ((¬ tx.version < 2) ∧
        ((tx.vin.getD nIn dummyTxIn).sequence.toNat &&&
            SEQUENCE_LOCKTIME_DISABLE_FLAG) = 0 ∧
        ((tx.vin.getD nIn dummyTxIn).sequence.toNat &&&
            (SEQUENCE_LOCKTIME_TYPE_FLAG ||| SEQUENCE_LOCKTIME_MASK)) <
          SEQUENCE_LOCKTIME_TYPE_FLAG ∧
        csv ≤ ((tx.vin.getD nIn dummyTxIn).sequence.toNat &&&
            (SEQUENCE_LOCKTIME_TYPE_FLAG ||| SEQUENCE_LOCKTIME_MASK)) ∧
        Bitcoin.Crypto.Ecdsa.Verify.verifyImpl (sig.extract 0 (sig.size - 1))
          delayedPaymentKey.bytes
          (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn
            (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
            (hashtypeOf sig) amount) = true) := by
  rw [← checkerOf_eq_realCheckerOf tx nIn amount hIn]
  exact toLocal_delayed_checkerOf_refinement tx nIn amount revocationKey
    delayedPaymentKey csv sig program hcsv hr hd hsigsz hps hprog hpk hne

end LnLean.Proofs.Bitcoin.SequenceContextTargets
