import Bitcoin.TxValidation.Full
import LnLean.Proofs.Bitcoin.SequenceContextTargets

/-!
# H04 — `scriptLaneTx` / `txVerdictFull` for a one-input delayed/revocation spend

This module closes the pipeline-level transfer left open by the wave-6/7
checker bridges.  It fixes one concrete one-input transaction, one concrete
prevout table and one concrete UTXO set, reduces the full `TxValidation.Full`
pipeline to the vendored P2WSH witness verifier at `standardScriptFlags`
(all seven flags true) and `PolicyFlags = {}`, and then proves the delayed
and revocation verdicts exactly against the checker-level side conditions:

* `checkSequenceDef`/`decodeNum` for the BIP 68/112 delay context;
* the vendored ECDSA verdict in the delayed-key or revocation-key slot;
* the DER-encoding side condition `isValidSigEncoding sig = true`, kept
  explicit so that the `dersig` flag never silently rejects a malformed
  signature in a "bad signature" theorem;
* the P2WSH program size/hash premises.

Every result is one-directional where the underlying computation is: the
`iff` theorems say the lane returns `some true` exactly when the concrete
checker signature entry is `true`.
-/

namespace LnLean.Proofs.WaveH.H04

open Bitcoin.Data Bitcoin.Activation Bitcoin.Consensus Bitcoin.Script.Parser
open Bitcoin.Interpreter Bitcoin.Numeric
open Bitcoin.Crypto.Seam (SigVersion ScriptExecutionData)
open Bitcoin.Ledger Bitcoin.TxValidation
open Bitcoin.TxValidation.Full (standardScriptFlags txVerdictFull scriptLaneTx scriptLane
  txCheckerFor pipelineFuel ScriptEntry tableSupplied tableAmountsKnown feeOk)
open LnLean LnLean.Bitcoin
open LnLean.Proofs.Bitcoin.SpendTargets
open LnLean.Proofs.Bitcoin.InterpreterBridgeTargets
open LnLean.Proofs.Bitcoin.InterpreterRevocationTargets
open LnLean.Proofs.Bitcoin.SequenceContextTargets
open LnLean.Proofs.Bitcoin.SighashBridgeTargets

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ## 1. The concrete one-input transaction, table and UTXO set -/

/-- A short non-null prevout (the hash is deliberately concrete so that the
transaction serialization and `isCoinBase` compute). -/
def probePrevout : Bitcoin.Data.OutPoint := ⟨List.toByteArray [1], 0⟩

/-- One input at `probePrevout`, empty scriptSig, a single empty output and
the supplied witness stack at index `0`. -/
def oneInputTx (w : Bitcoin.Data.WitnessStack) (seq : UInt32) : Bitcoin.Data.Tx :=
  { version := 2,
    vin := [{ prevout := probePrevout, scriptSig := Script.empty, sequence := seq }],
    vout := [{ value := 0, scriptPubKey := Script.empty }],
    locktime := 0,
    witness := [w] }

/-- The prevout table: every outpoint resolves to the P2WSH program with a
known amount. -/
def probeTable (program : ByteArray) (amount : Amount) :
    Bitcoin.Data.OutPoint → Option ScriptEntry :=
  fun _ => some ((p2wsh program).bytes, some amount)

/-- A UTXO set whose single entry is non-coinbase, matured and in range. -/
def probeUtxo : Bitcoin.Ledger.UtxoSet := fun _ => some ⟨0, 0, false, Script.empty⟩

theorem oneInputTx_checkTransaction (w : Bitcoin.Data.WitnessStack) (seq : UInt32) :
    checkTransaction (oneInputTx w seq) = none := by
  simp [checkTransaction, oneInputTx, probePrevout, txStrippedWeightL, serTxSize,
    serTx, serTxIn, serTxOut, serU8, serU16, serU32, serU64, compactSizeEnc, Script.empty,
    List.foldl, hasDupPrevouts, Tx.isCoinBase, OutPoint.isNull, MAX_BLOCK_WEIGHT,
    WITNESS_SCALE_FACTOR, Bitcoin.Consensus.checkTransaction.checkOutputs, MoneyRange,
    MAX_MONEY, COIN]

theorem oneInputTx_not_coinbase (w : Bitcoin.Data.WitnessStack) (seq : UInt32) :
    (oneInputTx w seq).isCoinBase = false := by
  simp [Tx.isCoinBase, oneInputTx, probePrevout, OutPoint.isNull]

theorem probeTable_supplied (program : ByteArray) (amount : Amount)
    (w : Bitcoin.Data.WitnessStack) (seq : UInt32) :
    tableSupplied (oneInputTx w seq) (probeTable program amount) = true := by
  simp [tableSupplied, oneInputTx, probeTable]

theorem probeTable_amountsKnown (program : ByteArray) (amount : Amount)
    (w : Bitcoin.Data.WitnessStack) (seq : UInt32) :
    tableAmountsKnown (oneInputTx w seq) (probeTable program amount) = true := by
  simp [tableAmountsKnown, oneInputTx, probeTable]

theorem probeUtxo_feeOk (w : Bitcoin.Data.WitnessStack) (seq : UInt32) (sh : UInt32) :
    feeOk (oneInputTx w seq) probeUtxo sh = true := by
  unfold feeOk
  simp [checkTxInputs, oneInputTx, probeUtxo, Tx.getValueOut, haveInputs, inputValuesLoop,
    coinMatured, MoneyRange, MAX_MONEY, COIN]

/-- With the stateless prefix, coinbase gate, table and fee slice all passing,
the full pipeline is exactly the script lane. -/
theorem txVerdictFull_oneInput (tx : Bitcoin.Data.Tx)
    (tbl : Bitcoin.Data.OutPoint → Option ScriptEntry)
    (u : Bitcoin.Ledger.UtxoSet) (sh : UInt32)
    (flags : ScriptFlags) (pol : PolicyFlags)
    (hct : checkTransaction tx = none) (hcb : tx.isCoinBase = false)
    (hts : tableSupplied tx tbl = true) (hta : tableAmountsKnown tx tbl = true)
    (hfee : feeOk tx u sh = true) :
    txVerdictFull tx tbl u sh flags pol = scriptLaneTx tx tbl flags pol := by
  simp [txVerdictFull, hct, hcb, hts, hta, hfee]

/-! ## 2. P2WSH decomposition of `verifyScriptFull` -/

def p2wshPrefix : ByteArray := (ByteArray.empty.push (0x00 : UInt8)).push (0x20 : UInt8)

theorem p2wsh_bytes_eq (program : ByteArray) :
    (p2wsh program).bytes = p2wshPrefix ++ program := rfl

theorem p2wshPrefix_size : p2wshPrefix.size = 2 := rfl

theorem prefix_get0 : (p2wshPrefix.get! 0).toNat = 0 := rfl

theorem prefix_get1 : (p2wshPrefix.get! 1).toNat = 0x20 := rfl

/-- `ByteArray.get!` commutes with an append when the index lands on the left
operand.  (`ByteArray.get!` only unfolds after `cases` on the structure.) -/
theorem get!_append_left' (a b : ByteArray) (i : Nat) (hi : i < a.size) :
    (a ++ b).get! i = a.get! i := by
  cases a with
  | mk ad =>
  cases b with
  | mk bd =>
  simp only [ByteArray.get!, ByteArray.data_append]
  rw [getElem!_def, getElem!_def]
  rw [Array.getElem?_append_left (xs := ad) (ys := bd) (hn := hi)]

theorem isWitnessProgram_p2wsh (program : ByteArray) (hp : program.size = 32) :
    isWitnessProgram (p2wsh program).bytes = some (0, program) := by
  have h0 : ((p2wshPrefix ++ program).get! 0).toNat = 0 := by
    rw [get!_append_left' _ _ _ (by simp [p2wshPrefix])]; exact prefix_get0
  have h1 : ((p2wshPrefix ++ program).get! 1).toNat = 0x20 := by
    rw [get!_append_left' _ _ _ (by simp [p2wshPrefix])]; exact prefix_get1
  have hsz : (p2wshPrefix ++ program).size = 34 := by simp [p2wshPrefix, hp]
  have hplen : ((p2wshPrefix ++ program).get! 1).toNat + 2 = 34 := by rw [h1]
  unfold isWitnessProgram
  rw [p2wsh_bytes_eq]
  simp only [hsz]
  rw [if_pos (by decide : 4 ≤ 34 ∧ 34 ≤ 42)]
  rw [if_pos (by rw [h0]; left; rfl)]
  rw [if_pos hplen]
  rw [if_pos (by rw [h0])]
  congr 1
  rw [ByteArray.extract_append_eq_right (show 2 = p2wshPrefix.size from p2wshPrefix_size.symm)
    (show 34 = p2wshPrefix.size + program.size by rw [p2wshPrefix_size, hp])]

theorem isPayToScriptHash_p2wsh (program : ByteArray) (hp : program.size = 32) :
    isPayToScriptHash (p2wsh program).bytes = false := by
  unfold isPayToScriptHash
  rw [p2wsh_bytes_eq]
  have hsz : (p2wshPrefix ++ program).size = 34 := by simp [p2wshPrefix, hp]
  simp [hsz]

theorem evalScriptBytes_empty (fuel : Nat) (flags : ScriptFlags) (pol : PolicyFlags)
    (chk : ScriptChecker) (sv : SigVersion) (ed : Bitcoin.Crypto.Seam.ScriptExecutionData)
    (hf : 0 < fuel) :
    evalScriptBytes fuel flags pol ByteArray.empty [] chk sv ed = .ok [] := by
  obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by omega⟩
  unfold evalScriptBytes
  simp [parseWire, parseWireFrom, finalStack, evalFrom]

theorem p2wsh_eq_serialize (program : ByteArray) (hp : program.size = 32) :
    (p2wsh program).bytes =
      serializeOpcodes [Opcode.pushBytes ByteArray.empty, Opcode.pushBytes program] := by
  have hser : serializeOpcodes [Opcode.pushBytes ByteArray.empty, Opcode.pushBytes program] =
      ([0].toByteArray ++ [32].toByteArray) ++ program := by
    simp [serializeOpcodes, serializeOpcode, pushBytesWire, lenBytes, hp]
    have hpush : ([0] : List UInt8).toByteArray.push 32 =
        [0].toByteArray ++ [32].toByteArray := by decide
    rw [hpush]
    rw [ByteArray.append_assoc]
  rw [hser]
  have h0 : ([0] : List UInt8).toByteArray = ByteArray.empty.push OP_0 := by decide
  have h32 : ([32] : List UInt8).toByteArray = ByteArray.empty.push (32 : UInt8) := by decide
  rw [h0, h32]
  have hprefix : (ByteArray.empty.push OP_0).push 32 =
      ByteArray.empty.push OP_0 ++ ByteArray.empty.push (32 : UInt8) := by decide
  rw [← hprefix]
  rfl

theorem parseWire_p2wsh (program : ByteArray) (hp : program.size = 32) :
    parseWire (p2wsh program).bytes =
      some [ { ast := Opcode.pushBytes ByteArray.empty, wire := 0, next := 1 },
             { ast := Opcode.pushBytes program, wire := 0x20, next := 34 } ] := by
  rw [p2wsh_eq_serialize program hp]
  rw [parseWire_serializeOpcodes]
  · simp [wireOpsFrom, serializeOpcode, pushBytesWire, lenBytes, wireOfAst, hp]
  · intro o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl
    · simp [opcodeWF]
    · show program.size ≤ Bitcoin.Script.Parser.MAX_SCRIPT_ELEMENT_SIZE
      rw [hp, Bitcoin.Script.Parser.MAX_SCRIPT_ELEMENT_SIZE]
      decide
  · intro o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl
    · exact firstByte_pushBytes_zero
    · exact firstByte_pushBytes_small program (by omega) (by omega)

theorem evalScriptBytes_p2wsh (fuel : Nat) (flags : ScriptFlags) (pol : PolicyFlags)
    (chk : ScriptChecker) (program : ByteArray) (hp : program.size = 32)
    (ed : Bitcoin.Crypto.Seam.ScriptExecutionData) (hf : 3 ≤ fuel) :
    evalScriptBytes fuel flags pol (p2wsh program).bytes [] chk .base ed
      = .ok [program, ByteArray.empty] := by
  obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 3 := ⟨fuel - 3, by omega⟩
  have hsz : (serializeOpcodes [Opcode.pushBytes ByteArray.empty, Opcode.pushBytes program]).size
      = 34 := by
    rw [← p2wsh_eq_serialize program hp]
    simp [p2wsh, hp]
  unfold evalScriptBytes
  rw [if_neg (by rw [p2wsh_eq_serialize program hp, hsz]; decide)]
  rw [parseWire_p2wsh program hp]
  simp [finalStack, evalFrom, stepChecked, stepBody, stepBody.dispatchOp,
    Opcode.pushBytes, checkMinimalPush, serializeOpcode, pushBytesWire, lenBytes, hp,
    disabledWire, Bitcoin.Script.Parser.MAX_SCRIPT_ELEMENT_SIZE,
    Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE, Bitcoin.Interpreter.MAX_STACK_SIZE]

/-- The P2WSH outer-script reduction: for a well-formed 32-byte program with
truthy bytes, `verifyScriptFull` at `standardScriptFlags` is exactly the
vendored witness-program check, with an empty scriptSig. -/
theorem verifyScriptFull_p2wsh (fuel : Nat) (pol : PolicyFlags)
    (program : ByteArray) (w : Bitcoin.Data.WitnessStack) (chk : ScriptChecker)
    (hp : program.size = 32) (htruth : Bitcoin.Numeric.castToBool program = true)
    (hf : 3 ≤ fuel) :
    verifyScriptFull fuel standardScriptFlags pol ByteArray.empty (p2wsh program).bytes w chk
      = verifyWitnessProgram fuel w 0 program standardScriptFlags pol chk false := by
  unfold verifyScriptFull
  simp only
  have hpre : (if pol.sigPushOnly = true then
      (match parseWire ByteArray.empty with
       | none => VerifyOutcome.fail ExecError.sigPushOnly
       | some ops => if (!isPushOnlyWire ops) = true then VerifyOutcome.fail ExecError.sigPushOnly
         else VerifyOutcome.ok)
      else VerifyOutcome.ok) = VerifyOutcome.ok := by
    split
    · simp [parseWire, parseWireFrom, isPushOnlyWire]
    · rfl
  cases hpre' : (if pol.sigPushOnly = true then
      (match parseWire ByteArray.empty with
       | none => VerifyOutcome.fail ExecError.sigPushOnly
       | some ops => if (!isPushOnlyWire ops) = true then VerifyOutcome.fail ExecError.sigPushOnly
         else VerifyOutcome.ok)
      else VerifyOutcome.ok) with
  | fail e => rw [hpre] at hpre'; cases hpre'
  | unjudged => rw [hpre] at hpre'; cases hpre'
  | ok =>
    simp only
    rw [evalScriptBytes_empty _ _ _ _ _ _ (by omega : 0 < fuel)]
    simp only
    rw [evalScriptBytes_p2wsh fuel standardScriptFlags pol chk program hp _ hf]
    simp only
    rw [if_neg (by simp [htruth])]
    simp only [standardScriptFlags]
    rw [isWitnessProgram_p2wsh program hp]
    simp only [ByteArray.size_empty, Option.isSome_some, reduceCtorEq, if_true]
    rw [if_neg (by decide : ¬ ((0 : Nat) ≠ 0))]
    cases hb : verifyWitnessProgram fuel w 0 program
        { p2sh := true, dersig := true, cltv := true, csv := true, nullDummy := true,
          witness := true, taproot := true } pol chk false with
    | ok =>
        simp [standardScriptFlags, isPayToScriptHash_p2wsh program hp,
          ByteArray.size_empty, htruth]
    | fail e => rfl
    | unjudged => rfl

/-- The concrete pipeline fuel of the one-input transaction is always at
least `3`, so the P2WSH outer script (two pushes) always evaluates. -/
theorem pipelineFuel_oneInput_ge_three (program : ByteArray)
    (w : Bitcoin.Data.WitnessStack) :
    3 ≤ pipelineFuel ByteArray.empty (p2wsh program).bytes w := by
  unfold pipelineFuel
  simp

/-- The same fuel is strictly larger than the nine executed opcodes of the
`to_local` script, so the vendored evaluator cannot hit fuel exhaustion. -/
theorem pipelineFuel_oneInput_gt_nine (program : ByteArray)
    (w : Bitcoin.Data.WitnessStack) :
    9 < pipelineFuel ByteArray.empty (p2wsh program).bytes w := by
  unfold pipelineFuel
  simp

/-- Fuel is inert once it strictly exceeds the opcode count: the evaluator
only distinguishes zero from positive fuel. -/
theorem evalFrom_fuel_eq_of_lt (ctx : Ctx) (ops : List WireOp) (st : State) :
    ∀ {f g : Nat}, ops.length < f → ops.length < g →
      evalFrom ctx f ops st = evalFrom ctx g ops st := by
  induction ops generalizing st with
  | nil =>
      intro f g hf hg
      cases f with
      | zero => omega
      | succ f =>
      cases g with
      | zero => omega
      | succ g =>
        simp [evalFrom]
  | cons op rest ih =>
      intro f g hf hg
      cases f with
      | zero => omega
      | succ f =>
      cases g with
      | zero => omega
      | succ g =>
        have hf' : rest.length < f := by
          simp only [List.length_cons] at hf; omega
        have hg' : rest.length < g := by
          simp only [List.length_cons] at hg; omega
        cases hstep : stepChecked ctx op st with
        | ok st' =>
            simp only [evalFrom, hstep]
            exact ih st' hf' hg'
        | error e =>
            simp only [evalFrom, hstep]

theorem toLocalWireOps_length (rk dpk : PubKey) (csv : Blocks) :
    (toLocalWireOps rk dpk csv).length = 9 := rfl

/-- `evalScriptBytes` on the concrete `to_local` script is inert in the fuel
above the nine executed opcodes. -/
theorem evalScriptBytes_toLocal_fuel_eq (F : Nat) (hF : 9 < F)
    (rk dpk : PubKey) (csv : Blocks) (st0 : Bitcoin.Interpreter.Stack)
    (chk : ScriptChecker) (sv : Bitcoin.Crypto.Seam.SigVersion)
    (ed : Bitcoin.Crypto.Seam.ScriptExecutionData)
    (hr : rk.bytes.size = 33) (hd : dpk.bytes.size = 33) :
    evalScriptBytes F standardScriptFlags ({} : PolicyFlags)
      (serializeOpcodes (toLocalOps rk dpk csv)) st0 chk sv ed
    = evalScriptBytes 10 standardScriptFlags ({} : PolicyFlags)
      (serializeOpcodes (toLocalOps rk dpk csv)) st0 chk sv ed := by
  have hsz : (serializeOpcodes (toLocalOps rk dpk csv)).size = 77 :=
    serializeOpcodes_toLocal_size rk dpk csv hr hd
  have hnot : ¬ ((sv = .base ∨ sv = .witnessV0) ∧
      Bitcoin.Interpreter.MAX_SCRIPT_SIZE <
        (serializeOpcodes (toLocalOps rk dpk csv)).size) := by
    simp [hsz, Bitcoin.Interpreter.MAX_SCRIPT_SIZE]
  simp only [evalScriptBytes, hnot, if_false, toLocal_parseWire rk dpk csv hr hd]
  congr 1
  exact evalFrom_fuel_eq_of_lt _ (toLocalWireOps rk dpk csv) _ (f := F) (g := 10)
    (by simpa [toLocalWireOps_length] using hF) (by decide : 9 < 10)

theorem executeWitnessScript_toLocal_fuel_eq (F : Nat) (hF : 9 < F)
    (rk dpk : PubKey) (csv : Blocks) (items : List ByteArray) (vwSer : Int)
    (chk : ScriptChecker) (hr : rk.bytes.size = 33) (hd : dpk.bytes.size = 33) :
    executeWitnessScript F items vwSer
      (serializeOpcodes (toLocalOps rk dpk csv)) standardScriptFlags ({} : PolicyFlags)
      chk .witnessV0
    = executeWitnessScript 10 items vwSer
      (serializeOpcodes (toLocalOps rk dpk csv)) standardScriptFlags ({} : PolicyFlags)
      chk .witnessV0 := by
  simp only [executeWitnessScript, executeWitnessScript.runExec]
  rw [evalScriptBytes_toLocal_fuel_eq F hF rk dpk csv items.reverse chk .witnessV0 _ hr hd]

theorem verifyWitnessProgram_toLocal_fuel_eq_delayed (F : Nat) (hF : 9 < F)
    (rk dpk : PubKey) (csv : Blocks) (sig : ByteArray) (program : ByteArray)
    (chk : ScriptChecker) (hr : rk.bytes.size = 33) (hd : dpk.bytes.size = 33)
    (hps : program.size = 32)
    (hprog : hashSha256 (serializeOpcodes (toLocalOps rk dpk csv)) = program) :
    verifyWitnessProgram F [sig, ByteArray.empty, serializeOpcodes (toLocalOps rk dpk csv)]
        0 program standardScriptFlags ({} : PolicyFlags) chk false
    = verifyWitnessProgram 10 [sig, ByteArray.empty, serializeOpcodes (toLocalOps rk dpk csv)]
        0 program standardScriptFlags ({} : PolicyFlags) chk false := by
  simp [verifyWitnessProgram, hps, hprog, byteArray_bne_self]
  rw [executeWitnessScript_toLocal_fuel_eq F hF rk dpk csv [sig, ByteArray.empty] _ chk hr hd]

theorem verifyWitnessProgram_toLocal_fuel_eq_revocation (F : Nat) (hF : 9 < F)
    (rk dpk : PubKey) (csv : Blocks) (sig : ByteArray) (program : ByteArray)
    (chk : ScriptChecker) (hr : rk.bytes.size = 33) (hd : dpk.bytes.size = 33)
    (hps : program.size = 32)
    (hprog : hashSha256 (serializeOpcodes (toLocalOps rk dpk csv)) = program) :
    verifyWitnessProgram F [sig, revocationSelector, serializeOpcodes (toLocalOps rk dpk csv)]
        0 program standardScriptFlags ({} : PolicyFlags) chk false
    = verifyWitnessProgram 10 [sig, revocationSelector, serializeOpcodes (toLocalOps rk dpk csv)]
        0 program standardScriptFlags ({} : PolicyFlags) chk false := by
  simp [verifyWitnessProgram, hps, hprog, byteArray_bne_self]
  rw [executeWitnessScript_toLocal_fuel_eq F hF rk dpk csv [sig, revocationSelector] _ chk hr hd]

/-! ## 3. Reducing `scriptLaneTx` on the concrete transaction -/

/-- One-input lane reduction: the whole script lane is the verdict of the
vendored P2WSH witness check at `standardScriptFlags`, threaded through the
same `.ok`/`.fail`/`.unjudged` translation as `scriptLane`. -/
theorem scriptLaneTx_oneInput_verify (program : ByteArray) (amount : Amount)
    (w : Bitcoin.Data.WitnessStack) (seq : UInt32)
    (hp : program.size = 32) (htruth : Bitcoin.Numeric.castToBool program = true)
    (outcome : VerifyOutcome)
    (h : verifyWitnessProgram
      (pipelineFuel ByteArray.empty (p2wsh program).bytes w)
      w 0 program standardScriptFlags ({} : PolicyFlags)
      (txCheckerFor (oneInputTx w seq) 0 (some amount)) false = outcome) :
    scriptLaneTx (oneInputTx w seq) (probeTable program amount) standardScriptFlags
        ({} : PolicyFlags)
      = (match outcome with
         | .ok => some true | .fail _ => some false | .unjudged => none) := by
  unfold scriptLaneTx
  simp only [scriptLane, oneInputTx, probeTable, Script.empty, List.getD_cons_zero]
  rw [verifyScriptFull_p2wsh _ _ program w _ hp htruth (pipelineFuel_oneInput_ge_three program w)]
  simp only [oneInputTx, Script.empty] at h ⊢
  cases outcome <;> simp_all

/-- `.ok` specialization of `scriptLaneTx_oneInput_verify`. -/
theorem scriptLaneTx_oneInput_ok (program : ByteArray) (amount : Amount)
    (w : Bitcoin.Data.WitnessStack) (seq : UInt32)
    (hp : program.size = 32) (htruth : Bitcoin.Numeric.castToBool program = true)
    (h : verifyWitnessProgram
      (pipelineFuel ByteArray.empty (p2wsh program).bytes w)
      w 0 program standardScriptFlags ({} : PolicyFlags)
      (txCheckerFor (oneInputTx w seq) 0 (some amount)) false = .ok) :
    scriptLaneTx (oneInputTx w seq) (probeTable program amount) standardScriptFlags
      ({} : PolicyFlags) = some true := by
  simpa using scriptLaneTx_oneInput_verify program amount w seq hp htruth .ok h

/-- `.fail` specialization of `scriptLaneTx_oneInput_verify`. -/
theorem scriptLaneTx_oneInput_fail (program : ByteArray) (amount : Amount)
    (w : Bitcoin.Data.WitnessStack) (seq : UInt32)
    (hp : program.size = 32) (htruth : Bitcoin.Numeric.castToBool program = true)
    (e : ExecError)
    (h : verifyWitnessProgram
      (pipelineFuel ByteArray.empty (p2wsh program).bytes w)
      w 0 program standardScriptFlags ({} : PolicyFlags)
      (txCheckerFor (oneInputTx w seq) 0 (some amount)) false = .fail e) :
    scriptLaneTx (oneInputTx w seq) (probeTable program amount) standardScriptFlags
      ({} : PolicyFlags) = some false := by
  simpa using scriptLaneTx_oneInput_verify program amount w seq hp htruth (.fail e) h

/-- The lane is `some true` exactly when the P2WSH witness check is `.ok`. -/
theorem scriptLaneTx_oneInput_ok_iff (program : ByteArray) (amount : Amount)
    (w : Bitcoin.Data.WitnessStack) (seq : UInt32)
    (hp : program.size = 32) (htruth : Bitcoin.Numeric.castToBool program = true) :
    scriptLaneTx (oneInputTx w seq) (probeTable program amount) standardScriptFlags
        ({} : PolicyFlags) = some true
      ↔ verifyWitnessProgram
          (pipelineFuel ByteArray.empty (p2wsh program).bytes w)
          w 0 program standardScriptFlags ({} : PolicyFlags)
          (txCheckerFor (oneInputTx w seq) 0 (some amount)) false = .ok := by
  constructor
  · intro hl
    cases hout : verifyWitnessProgram
        (pipelineFuel ByteArray.empty (p2wsh program).bytes w)
        w 0 program standardScriptFlags ({} : PolicyFlags)
        (txCheckerFor (oneInputTx w seq) 0 (some amount)) false with
    | ok => rfl
    | fail e =>
        have := scriptLaneTx_oneInput_fail program amount w seq hp htruth e hout
        rw [this] at hl
        cases hl
    | unjudged =>
        have := scriptLaneTx_oneInput_verify program amount w seq hp htruth .unjudged hout
        rw [this] at hl
        cases hl
  · intro hok
    exact scriptLaneTx_oneInput_ok program amount w seq hp htruth hok

/-! ## 4. The concrete checker's ECDSA entry -/

/-- For a nonempty, validly encoded signature and a valid public key, the
concrete `txCheckerFor` ECDSA slot is the vendored `verifyImpl` over the
BIP 143 witness-v0 digest of the same transaction/input. -/
theorem txCheckerFor_ecdsa_eq_verify (tx : Bitcoin.Data.Tx) (nIn : Nat)
    (amount : Amount) (sig pk code : ByteArray)
    (hpk : Bitcoin.Crypto.Seam.Der.isValidPubKey pk = true) (hne : 0 < sig.size) :
    (txCheckerFor tx nIn (some amount)).base.checkECDSASignature sig pk code .witnessV0
        (default : Bitcoin.Crypto.Seam.ScriptExecutionData)
      = Bitcoin.Crypto.Ecdsa.Verify.verifyImpl
          (sig.extract 0 (sig.size - 1)) pk
          (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn code (hashtypeOf sig) amount) := by
  simp only [txCheckerFor, Option.getD_some, Option.isSome_some]
  rw [Bitcoin.Crypto.Seam.Entry.txCheckerOf_ecdsa]
  rw [Bitcoin.Crypto.Seam.Entry.ecdsaEntry_pops_hashtype
    Bitcoin.Crypto.Ecdsa.Verify.verifyImpl
    (Bitcoin.Capstone.RealChecker.sighashDispatch tx nIn amount) true
    sig pk code .witnessV0 (default : Bitcoin.Crypto.Seam.ScriptExecutionData)
    hpk hne (by intro _; rfl)]
  simp only [Bitcoin.Capstone.RealChecker.sighashDispatch,
    Bitcoin.Capstone.RealChecker.htToU32,
    LnLean.Bitcoin.Sighash.sighashWitnessV0_eq_interface]
  rfl

/-! ## 5. Delayed branch: positive computation at `standardScriptFlags` -/

theorem evalFrom_delayed_std (chk : ScriptChecker)
    (rk dpk : PubKey) (csv : Blocks) (sig : ByteArray) (n : ScriptNum)
    (hr : rk.bytes.size = 33) (hd : dpk.bytes.size = 33)
    (hdec : decodeNum ({} : PolicyFlags) (delayBytes csv) 5 = .ok n)
    (hnn : 0 ≤ n) (hdis : Int.toNat n &&& SEQUENCE_LOCKTIME_DISABLE_FLAG = 0)
    (hseq : checkSequenceDef chk.env n = true)
    (hder : isValidSigEncoding sig = true)
    (hsig : chk.base.checkECDSASignature sig dpk.bytes
      (serializeOpcodes (toLocalOps rk dpk csv)) .witnessV0
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true) :
    evalFrom
      { flags := standardScriptFlags, pol := ({} : PolicyFlags), chk := chk, sv := .witnessV0,
        bytes := serializeOpcodes (toLocalOps rk dpk csv),
        ed := (default : Bitcoin.Crypto.Seam.ScriptExecutionData) }
      10 (toLocalWireOps rk dpk csv)
      { stack := [ByteArray.empty, sig], alt := [], vf := [], opCount := 0, codeSep := 0,
        vwLeft := none }
    = Except.ok
        { stack := [ByteArray.mk #[0x01]], alt := [], vf := [], opCount := 6,
          codeSep := 0, vwLeft := none } := by
  simp [standardScriptFlags, toLocalWireOps, evalFrom, stepChecked, stepBody, stepBody.dispatchOp,
    evalChecksigDispatch, evalChecksigPreTapscript, checkSigEncoding, checkPubKeyEncoding,
    Bitcoin.Numeric.castToBool, Bitcoin.Numeric.castToBoolList,
    Bitcoin.Numeric.bytesOf, delayBytes, topAt, pushBoolV, vchTrue, serU8, disabledWire,
    Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE, MAX_STACK_SIZE, MAX_OPS_PER_SCRIPT,
    toLocalDelayBytes_size, hdis, hseq, hder, hsig, hr, hd]
  rw [show decodeNum ({} : PolicyFlags) (toLocalDelayBytes csv) 5 = .ok n by
    simpa [delayBytes] using hdec]
  have hnlt : ¬ n < 0 := Int.not_lt.mpr hnn
  simp [hnlt, hdis, hseq, hder, hsig, Bitcoin.Numeric.castToBoolList, empty_push_eq]
  rfl

theorem evalScriptBytes_delayed_std (chk : ScriptChecker)
    (rk dpk : PubKey) (csv : Blocks) (sig : ByteArray) (n : ScriptNum)
    (hr : rk.bytes.size = 33) (hd : dpk.bytes.size = 33)
    (hdec : decodeNum ({} : PolicyFlags) (delayBytes csv) 5 = .ok n)
    (hnn : 0 ≤ n) (hdis : Int.toNat n &&& SEQUENCE_LOCKTIME_DISABLE_FLAG = 0)
    (hseq : checkSequenceDef chk.env n = true) (hder : isValidSigEncoding sig = true)
    (hsig : chk.base.checkECDSASignature sig dpk.bytes
      (serializeOpcodes (toLocalOps rk dpk csv)) .witnessV0
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true) :
    evalScriptBytes 10 standardScriptFlags ({} : PolicyFlags)
      (serializeOpcodes (toLocalOps rk dpk csv))
      [ByteArray.empty, sig] chk .witnessV0
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData)
    = Except.ok [ByteArray.mk #[0x01]] := by
  unfold evalScriptBytes
  have hsz : (serializeOpcodes (toLocalOps rk dpk csv)).size = 77 :=
    serializeOpcodes_toLocal_size rk dpk csv hr hd
  rw [if_neg (by simp [hsz, Bitcoin.Interpreter.MAX_SCRIPT_SIZE])]
  rw [toLocal_parseWire rk dpk csv hr hd]
  simp [finalStack, evalFrom_delayed_std chk rk dpk csv sig n hr hd hdec hnn hdis hseq hder hsig]

theorem executeWitnessScript_delayed_std (chk : ScriptChecker)
    (rk dpk : PubKey) (csv : Blocks) (sig : ByteArray) (n : ScriptNum) (vwSer : Int)
    (hr : rk.bytes.size = 33) (hd : dpk.bytes.size = 33) (hsigsz : sig.size ≤ 520)
    (hdec : decodeNum ({} : PolicyFlags) (delayBytes csv) 5 = .ok n)
    (hnn : 0 ≤ n) (hdis : Int.toNat n &&& SEQUENCE_LOCKTIME_DISABLE_FLAG = 0)
    (hseq : checkSequenceDef chk.env n = true) (hder : isValidSigEncoding sig = true)
    (hsig : chk.base.checkECDSASignature sig dpk.bytes
      (serializeOpcodes (toLocalOps rk dpk csv)) .witnessV0
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true) :
    executeWitnessScript 10 [sig, ByteArray.empty] vwSer
      (serializeOpcodes (toLocalOps rk dpk csv)) standardScriptFlags ({} : PolicyFlags)
      chk .witnessV0 = .ok := by
  have hsig' : ¬ Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE < sig.size := by
    unfold Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE; omega
  have hempty' : ¬ Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE < ByteArray.empty.size := by
    unfold Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE; decide
  simp [executeWitnessScript, executeWitnessScript.runExec,
    evalScriptBytes_delayed_std chk rk dpk csv sig n hr hd hdec hnn hdis hseq hder hsig,
    hsig', hempty', Bitcoin.Numeric.castToBool, Bitcoin.Numeric.castToBoolList]
  decide

theorem verifyWitnessProgram_delayed_std (chk : ScriptChecker)
    (rk dpk : PubKey) (csv : Blocks) (sig : ByteArray) (n : ScriptNum) (program : ByteArray)
    (hr : rk.bytes.size = 33) (hd : dpk.bytes.size = 33) (hsigsz : sig.size ≤ 520)
    (hdec : decodeNum ({} : PolicyFlags) (delayBytes csv) 5 = .ok n)
    (hnn : 0 ≤ n) (hdis : Int.toNat n &&& SEQUENCE_LOCKTIME_DISABLE_FLAG = 0)
    (hseq : checkSequenceDef chk.env n = true) (hder : isValidSigEncoding sig = true)
    (hsig : chk.base.checkECDSASignature sig dpk.bytes
      (serializeOpcodes (toLocalOps rk dpk csv)) .witnessV0
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true)
    (hps : program.size = 32)
    (hprog : hashSha256 (serializeOpcodes (toLocalOps rk dpk csv)) = program) :
    verifyWitnessProgram 10 [sig, ByteArray.empty, serializeOpcodes (toLocalOps rk dpk csv)]
      0 program standardScriptFlags ({} : PolicyFlags) chk false = .ok := by
  simp [verifyWitnessProgram, hps, hprog, byteArray_bne_self,
    executeWitnessScript_delayed_std chk rk dpk csv sig n
      (witnessSerSize [sig, ByteArray.empty, serializeOpcodes (toLocalOps rk dpk csv)])
      hr hd hsigsz hdec hnn hdis hseq hder hsig]

/-! ## 6. Revocation branch: positive computation at `standardScriptFlags` -/

theorem evalFrom_revocation_std (chk : ScriptChecker)
    (rk dpk : PubKey) (csv : Blocks) (sig : ByteArray)
    (hr : rk.bytes.size = 33) (hd : dpk.bytes.size = 33)
    (hder : isValidSigEncoding sig = true)
    (hsig : chk.base.checkECDSASignature sig rk.bytes
      (serializeOpcodes (toLocalOps rk dpk csv)) .witnessV0
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true) :
    evalFrom
      { flags := standardScriptFlags, pol := ({} : PolicyFlags), chk := chk, sv := .witnessV0,
        bytes := serializeOpcodes (toLocalOps rk dpk csv),
        ed := (default : Bitcoin.Crypto.Seam.ScriptExecutionData) }
      10 (toLocalWireOps rk dpk csv)
      { stack := [revocationSelector, sig], alt := [], vf := [], opCount := 0, codeSep := 0,
        vwLeft := none }
    = Except.ok
        { stack := [ByteArray.mk #[0x01]], alt := [], vf := [], opCount := 6,
          codeSep := 0, vwLeft := none } := by
  simp [standardScriptFlags, toLocalWireOps, evalFrom, stepChecked, stepBody, stepBody.dispatchOp,
    evalChecksigDispatch, evalChecksigPreTapscript, checkSigEncoding, checkPubKeyEncoding,
    topAt, pushBoolV, vchTrue, serU8, disabledWire,
    Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE, MAX_STACK_SIZE, MAX_OPS_PER_SCRIPT,
    toLocalDelayBytes_size, empty_push_mk, hder, hsig, hr, hd]

theorem evalScriptBytes_revocation_std (chk : ScriptChecker)
    (rk dpk : PubKey) (csv : Blocks) (sig : ByteArray)
    (hr : rk.bytes.size = 33) (hd : dpk.bytes.size = 33)
    (hder : isValidSigEncoding sig = true)
    (hsig : chk.base.checkECDSASignature sig rk.bytes
      (serializeOpcodes (toLocalOps rk dpk csv)) .witnessV0
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true) :
    evalScriptBytes 10 standardScriptFlags ({} : PolicyFlags)
      (serializeOpcodes (toLocalOps rk dpk csv))
      [revocationSelector, sig] chk .witnessV0
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData)
    = Except.ok [ByteArray.mk #[0x01]] := by
  unfold evalScriptBytes
  have hsz : (serializeOpcodes (toLocalOps rk dpk csv)).size = 77 :=
    serializeOpcodes_toLocal_size rk dpk csv hr hd
  rw [if_neg (by simp [hsz, Bitcoin.Interpreter.MAX_SCRIPT_SIZE])]
  rw [toLocal_parseWire rk dpk csv hr hd]
  simp [finalStack, evalFrom_revocation_std chk rk dpk csv sig hr hd hder hsig]

theorem executeWitnessScript_revocation_std (chk : ScriptChecker)
    (rk dpk : PubKey) (csv : Blocks) (sig : ByteArray) (vwSer : Int)
    (hr : rk.bytes.size = 33) (hd : dpk.bytes.size = 33) (hsigsz : sig.size ≤ 520)
    (hder : isValidSigEncoding sig = true)
    (hsig : chk.base.checkECDSASignature sig rk.bytes
      (serializeOpcodes (toLocalOps rk dpk csv)) .witnessV0
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true) :
    executeWitnessScript 10 [sig, revocationSelector] vwSer
      (serializeOpcodes (toLocalOps rk dpk csv)) standardScriptFlags ({} : PolicyFlags)
      chk .witnessV0 = .ok := by
  have hsig' : ¬ Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE < sig.size := by
    unfold Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE; omega
  simp [executeWitnessScript, executeWitnessScript.runExec,
    evalScriptBytes_revocation_std chk rk dpk csv sig hr hd hder hsig,
    hsig', Bitcoin.Numeric.castToBool]
  decide

theorem verifyWitnessProgram_revocation_std (chk : ScriptChecker)
    (rk dpk : PubKey) (csv : Blocks) (sig : ByteArray) (program : ByteArray)
    (hr : rk.bytes.size = 33) (hd : dpk.bytes.size = 33) (hsigsz : sig.size ≤ 520)
    (hder : isValidSigEncoding sig = true)
    (hsig : chk.base.checkECDSASignature sig rk.bytes
      (serializeOpcodes (toLocalOps rk dpk csv)) .witnessV0
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true)
    (hps : program.size = 32)
    (hprog : hashSha256 (serializeOpcodes (toLocalOps rk dpk csv)) = program) :
    verifyWitnessProgram 10 [sig, revocationSelector, serializeOpcodes (toLocalOps rk dpk csv)]
      0 program standardScriptFlags ({} : PolicyFlags) chk false = .ok := by
  simp [verifyWitnessProgram, hps, hprog, byteArray_bne_self,
    executeWitnessScript_revocation_std chk rk dpk csv sig
      (witnessSerSize [sig, revocationSelector, serializeOpcodes (toLocalOps rk dpk csv)])
      hr hd hsigsz hder hsig]

/-! ## 7. Negative computations at `standardScriptFlags`

The points below are the exact `evalFrom`/`evalScriptBytes`/`executeWitnessScript`
/`verifyWitnessProgram` failures.  The DER premise `hder` is explicit, so the
"bad signature" points are genuinely about the ECDSA verdict rather than the
`dersig` encoding gate. -/

theorem evalFrom_delayed_bad_sig_std (chk : ScriptChecker)
    (rk dpk : PubKey) (csv : Blocks) (sig : ByteArray) (n : ScriptNum)
    (hr : rk.bytes.size = 33) (hd : dpk.bytes.size = 33)
    (hdec : decodeNum ({} : PolicyFlags) (delayBytes csv) 5 = .ok n)
    (hnn : 0 ≤ n) (hdis : Int.toNat n &&& SEQUENCE_LOCKTIME_DISABLE_FLAG = 0)
    (hseq : checkSequenceDef chk.env n = true) (hder : isValidSigEncoding sig = true)
    (hsig : chk.base.checkECDSASignature sig dpk.bytes
      (serializeOpcodes (toLocalOps rk dpk csv)) .witnessV0
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = false) :
    evalFrom
      { flags := standardScriptFlags, pol := ({} : PolicyFlags), chk := chk, sv := .witnessV0,
        bytes := serializeOpcodes (toLocalOps rk dpk csv),
        ed := (default : Bitcoin.Crypto.Seam.ScriptExecutionData) }
      10 (toLocalWireOps rk dpk csv)
      { stack := [ByteArray.empty, sig], alt := [], vf := [], opCount := 0, codeSep := 0,
        vwLeft := none }
    = Except.ok
        { stack := [ByteArray.empty], alt := [], vf := [], opCount := 6,
          codeSep := 0, vwLeft := none } := by
  simp [standardScriptFlags, toLocalWireOps, evalFrom, stepChecked, stepBody, stepBody.dispatchOp,
    evalChecksigDispatch, evalChecksigPreTapscript, checkSigEncoding, checkPubKeyEncoding,
    Bitcoin.Numeric.castToBool, Bitcoin.Numeric.castToBoolList,
    Bitcoin.Numeric.bytesOf, delayBytes, topAt, pushBoolV, vchFalse, serU8, disabledWire,
    Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE, MAX_STACK_SIZE, MAX_OPS_PER_SCRIPT,
    toLocalDelayBytes_size, hdis, hseq, hder, hsig, hr, hd]
  rw [show decodeNum ({} : PolicyFlags) (toLocalDelayBytes csv) 5 = .ok n by
    simpa [delayBytes] using hdec]
  have hnlt : ¬ n < 0 := Int.not_lt.mpr hnn
  simp [hnlt, hdis, hseq, hder, hsig, Bitcoin.Numeric.castToBoolList, empty_push_eq]

theorem evalFrom_revocation_bad_sig_std (chk : ScriptChecker)
    (rk dpk : PubKey) (csv : Blocks) (sig : ByteArray)
    (hr : rk.bytes.size = 33) (hd : dpk.bytes.size = 33)
    (hder : isValidSigEncoding sig = true)
    (hsig : chk.base.checkECDSASignature sig rk.bytes
      (serializeOpcodes (toLocalOps rk dpk csv)) .witnessV0
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = false) :
    evalFrom
      { flags := standardScriptFlags, pol := ({} : PolicyFlags), chk := chk, sv := .witnessV0,
        bytes := serializeOpcodes (toLocalOps rk dpk csv),
        ed := (default : Bitcoin.Crypto.Seam.ScriptExecutionData) }
      10 (toLocalWireOps rk dpk csv)
      { stack := [revocationSelector, sig], alt := [], vf := [], opCount := 0, codeSep := 0,
        vwLeft := none }
    = Except.ok
        { stack := [ByteArray.empty], alt := [], vf := [], opCount := 6,
          codeSep := 0, vwLeft := none } := by
  simp [standardScriptFlags, toLocalWireOps, evalFrom, stepChecked, stepBody, stepBody.dispatchOp,
    evalChecksigDispatch, evalChecksigPreTapscript, checkSigEncoding, checkPubKeyEncoding,
    topAt, pushBoolV, vchFalse, serU8, disabledWire,
    Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE, MAX_STACK_SIZE, MAX_OPS_PER_SCRIPT,
    toLocalDelayBytes_size, empty_push_mk, hder, hsig, hr, hd]

theorem evalFrom_delayed_csv_false_std (chk : ScriptChecker)
    (rk dpk : PubKey) (csv : Blocks) (sig : ByteArray) (n : ScriptNum)
    (hr : rk.bytes.size = 33) (hd : dpk.bytes.size = 33)
    (hdec : decodeNum ({} : PolicyFlags) (delayBytes csv) 5 = .ok n)
    (hnn : 0 ≤ n) (hdis : Int.toNat n &&& SEQUENCE_LOCKTIME_DISABLE_FLAG = 0)
    (hseq : checkSequenceDef chk.env n = false) :
    evalFrom
      { flags := standardScriptFlags, pol := ({} : PolicyFlags), chk := chk, sv := .witnessV0,
        bytes := serializeOpcodes (toLocalOps rk dpk csv),
        ed := (default : Bitcoin.Crypto.Seam.ScriptExecutionData) }
      10 (toLocalWireOps rk dpk csv)
      { stack := [ByteArray.empty, sig], alt := [], vf := [], opCount := 0, codeSep := 0,
        vwLeft := none }
    = Except.error ExecError.unsatisfiedLocktime := by
  simp [standardScriptFlags, toLocalWireOps, evalFrom, stepChecked, stepBody, stepBody.dispatchOp,
    evalChecksigDispatch, evalChecksigPreTapscript, checkSigEncoding, checkPubKeyEncoding,
    Bitcoin.Numeric.castToBool, Bitcoin.Numeric.castToBoolList,
    Bitcoin.Numeric.bytesOf, delayBytes, topAt, pushBoolV, serU8, disabledWire,
    Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE, MAX_STACK_SIZE, MAX_OPS_PER_SCRIPT,
    toLocalDelayBytes_size, hdis, hseq, hr, hd]
  rw [show decodeNum ({} : PolicyFlags) (toLocalDelayBytes csv) 5 = .ok n by
    simpa [delayBytes] using hdec]
  have hnlt : ¬ n < 0 := Int.not_lt.mpr hnn
  simp [hnlt, hdis, hseq, Bitcoin.Numeric.castToBoolList, empty_push_eq]

/-! ### 7a. Lifting the delayed bad-signature result -/

theorem evalScriptBytes_delayed_bad_sig_std (chk : ScriptChecker)
    (rk dpk : PubKey) (csv : Blocks) (sig : ByteArray) (n : ScriptNum)
    (hr : rk.bytes.size = 33) (hd : dpk.bytes.size = 33)
    (hdec : decodeNum ({} : PolicyFlags) (delayBytes csv) 5 = .ok n)
    (hnn : 0 ≤ n) (hdis : Int.toNat n &&& SEQUENCE_LOCKTIME_DISABLE_FLAG = 0)
    (hseq : checkSequenceDef chk.env n = true) (hder : isValidSigEncoding sig = true)
    (hsig : chk.base.checkECDSASignature sig dpk.bytes
      (serializeOpcodes (toLocalOps rk dpk csv)) .witnessV0
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = false) :
    evalScriptBytes 10 standardScriptFlags ({} : PolicyFlags)
      (serializeOpcodes (toLocalOps rk dpk csv))
      [ByteArray.empty, sig] chk .witnessV0
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData)
    = Except.ok [ByteArray.empty] := by
  unfold evalScriptBytes
  have hsz : (serializeOpcodes (toLocalOps rk dpk csv)).size = 77 :=
    serializeOpcodes_toLocal_size rk dpk csv hr hd
  rw [if_neg (by simp [hsz, Bitcoin.Interpreter.MAX_SCRIPT_SIZE])]
  rw [toLocal_parseWire rk dpk csv hr hd]
  simp [finalStack, evalFrom_delayed_bad_sig_std chk rk dpk csv sig n hr hd hdec hnn hdis
    hseq hder hsig]

theorem executeWitnessScript_delayed_bad_sig_std (chk : ScriptChecker)
    (rk dpk : PubKey) (csv : Blocks) (sig : ByteArray) (n : ScriptNum) (vwSer : Int)
    (hr : rk.bytes.size = 33) (hd : dpk.bytes.size = 33) (hsigsz : sig.size ≤ 520)
    (hdec : decodeNum ({} : PolicyFlags) (delayBytes csv) 5 = .ok n)
    (hnn : 0 ≤ n) (hdis : Int.toNat n &&& SEQUENCE_LOCKTIME_DISABLE_FLAG = 0)
    (hseq : checkSequenceDef chk.env n = true) (hder : isValidSigEncoding sig = true)
    (hsig : chk.base.checkECDSASignature sig dpk.bytes
      (serializeOpcodes (toLocalOps rk dpk csv)) .witnessV0
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = false) :
    executeWitnessScript 10 [sig, ByteArray.empty] vwSer
      (serializeOpcodes (toLocalOps rk dpk csv)) standardScriptFlags ({} : PolicyFlags)
      chk .witnessV0 = .fail .evalFalse := by
  have hsig' : ¬ Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE < sig.size := by
    unfold Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE; omega
  have hempty' : ¬ Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE < ByteArray.empty.size := by
    unfold Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE; decide
  simp [executeWitnessScript, executeWitnessScript.runExec,
    evalScriptBytes_delayed_bad_sig_std chk rk dpk csv sig n hr hd hdec hnn hdis hseq hder hsig,
    hsig', hempty', Bitcoin.Numeric.castToBool, Bitcoin.Numeric.castToBoolList]
  decide

theorem verifyWitnessProgram_delayed_bad_sig_std (chk : ScriptChecker)
    (rk dpk : PubKey) (csv : Blocks) (sig : ByteArray) (n : ScriptNum) (program : ByteArray)
    (hr : rk.bytes.size = 33) (hd : dpk.bytes.size = 33) (hsigsz : sig.size ≤ 520)
    (hdec : decodeNum ({} : PolicyFlags) (delayBytes csv) 5 = .ok n)
    (hnn : 0 ≤ n) (hdis : Int.toNat n &&& SEQUENCE_LOCKTIME_DISABLE_FLAG = 0)
    (hseq : checkSequenceDef chk.env n = true) (hder : isValidSigEncoding sig = true)
    (hsig : chk.base.checkECDSASignature sig dpk.bytes
      (serializeOpcodes (toLocalOps rk dpk csv)) .witnessV0
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = false)
    (hps : program.size = 32)
    (hprog : hashSha256 (serializeOpcodes (toLocalOps rk dpk csv)) = program) :
    verifyWitnessProgram 10 [sig, ByteArray.empty, serializeOpcodes (toLocalOps rk dpk csv)]
      0 program standardScriptFlags ({} : PolicyFlags) chk false = .fail .evalFalse := by
  simp [verifyWitnessProgram, hps, hprog, byteArray_bne_self,
    executeWitnessScript_delayed_bad_sig_std chk rk dpk csv sig n
      (witnessSerSize [sig, ByteArray.empty, serializeOpcodes (toLocalOps rk dpk csv)])
      hr hd hsigsz hdec hnn hdis hseq hder hsig]

/-! ### 7b. Lifting the revocation bad-signature result -/

theorem evalScriptBytes_revocation_bad_sig_std (chk : ScriptChecker)
    (rk dpk : PubKey) (csv : Blocks) (sig : ByteArray)
    (hr : rk.bytes.size = 33) (hd : dpk.bytes.size = 33)
    (hder : isValidSigEncoding sig = true)
    (hsig : chk.base.checkECDSASignature sig rk.bytes
      (serializeOpcodes (toLocalOps rk dpk csv)) .witnessV0
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = false) :
    evalScriptBytes 10 standardScriptFlags ({} : PolicyFlags)
      (serializeOpcodes (toLocalOps rk dpk csv))
      [revocationSelector, sig] chk .witnessV0
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData)
    = Except.ok [ByteArray.empty] := by
  unfold evalScriptBytes
  have hsz : (serializeOpcodes (toLocalOps rk dpk csv)).size = 77 :=
    serializeOpcodes_toLocal_size rk dpk csv hr hd
  rw [if_neg (by simp [hsz, Bitcoin.Interpreter.MAX_SCRIPT_SIZE])]
  rw [toLocal_parseWire rk dpk csv hr hd]
  simp [finalStack, evalFrom_revocation_bad_sig_std chk rk dpk csv sig hr hd hder hsig]

theorem executeWitnessScript_revocation_bad_sig_std (chk : ScriptChecker)
    (rk dpk : PubKey) (csv : Blocks) (sig : ByteArray) (vwSer : Int)
    (hr : rk.bytes.size = 33) (hd : dpk.bytes.size = 33) (hsigsz : sig.size ≤ 520)
    (hder : isValidSigEncoding sig = true)
    (hsig : chk.base.checkECDSASignature sig rk.bytes
      (serializeOpcodes (toLocalOps rk dpk csv)) .witnessV0
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = false) :
    executeWitnessScript 10 [sig, revocationSelector] vwSer
      (serializeOpcodes (toLocalOps rk dpk csv)) standardScriptFlags ({} : PolicyFlags)
      chk .witnessV0 = .fail .evalFalse := by
  have hsig' : ¬ Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE < sig.size := by
    unfold Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE; omega
  simp [executeWitnessScript, executeWitnessScript.runExec,
    evalScriptBytes_revocation_bad_sig_std chk rk dpk csv sig hr hd hder hsig, hsig',
    Bitcoin.Numeric.castToBool]
  decide

theorem verifyWitnessProgram_revocation_bad_sig_std (chk : ScriptChecker)
    (rk dpk : PubKey) (csv : Blocks) (sig : ByteArray) (program : ByteArray)
    (hr : rk.bytes.size = 33) (hd : dpk.bytes.size = 33) (hsigsz : sig.size ≤ 520)
    (hder : isValidSigEncoding sig = true)
    (hsig : chk.base.checkECDSASignature sig rk.bytes
      (serializeOpcodes (toLocalOps rk dpk csv)) .witnessV0
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = false)
    (hps : program.size = 32)
    (hprog : hashSha256 (serializeOpcodes (toLocalOps rk dpk csv)) = program) :
    verifyWitnessProgram 10 [sig, revocationSelector, serializeOpcodes (toLocalOps rk dpk csv)]
      0 program standardScriptFlags ({} : PolicyFlags) chk false = .fail .evalFalse := by
  simp [verifyWitnessProgram, hps, hprog, byteArray_bne_self,
    executeWitnessScript_revocation_bad_sig_std chk rk dpk csv sig
      (witnessSerSize [sig, revocationSelector, serializeOpcodes (toLocalOps rk dpk csv)])
      hr hd hsigsz hder hsig]

/-! ### 7c. Lifting the failed-sequence result -/

theorem evalScriptBytes_delayed_csv_false_std (chk : ScriptChecker)
    (rk dpk : PubKey) (csv : Blocks) (sig : ByteArray) (n : ScriptNum)
    (hr : rk.bytes.size = 33) (hd : dpk.bytes.size = 33)
    (hdec : decodeNum ({} : PolicyFlags) (delayBytes csv) 5 = .ok n)
    (hnn : 0 ≤ n) (hdis : Int.toNat n &&& SEQUENCE_LOCKTIME_DISABLE_FLAG = 0)
    (hseq : checkSequenceDef chk.env n = false) :
    evalScriptBytes 10 standardScriptFlags ({} : PolicyFlags)
      (serializeOpcodes (toLocalOps rk dpk csv))
      [ByteArray.empty, sig] chk .witnessV0
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData)
    = Except.error ExecError.unsatisfiedLocktime := by
  unfold evalScriptBytes
  have hsz : (serializeOpcodes (toLocalOps rk dpk csv)).size = 77 :=
    serializeOpcodes_toLocal_size rk dpk csv hr hd
  rw [if_neg (by simp [hsz, Bitcoin.Interpreter.MAX_SCRIPT_SIZE])]
  rw [toLocal_parseWire rk dpk csv hr hd]
  simp [finalStack, evalFrom_delayed_csv_false_std chk rk dpk csv sig n hr hd hdec hnn hdis hseq]

theorem executeWitnessScript_delayed_csv_false_std (chk : ScriptChecker)
    (rk dpk : PubKey) (csv : Blocks) (sig : ByteArray) (n : ScriptNum) (vwSer : Int)
    (hr : rk.bytes.size = 33) (hd : dpk.bytes.size = 33) (hsigsz : sig.size ≤ 520)
    (hdec : decodeNum ({} : PolicyFlags) (delayBytes csv) 5 = .ok n)
    (hnn : 0 ≤ n) (hdis : Int.toNat n &&& SEQUENCE_LOCKTIME_DISABLE_FLAG = 0)
    (hseq : checkSequenceDef chk.env n = false) :
    executeWitnessScript 10 [sig, ByteArray.empty] vwSer
      (serializeOpcodes (toLocalOps rk dpk csv)) standardScriptFlags ({} : PolicyFlags)
      chk .witnessV0 = .fail .unsatisfiedLocktime := by
  have hsig' : ¬ Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE < sig.size := by
    unfold Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE; omega
  have hempty' : ¬ Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE < ByteArray.empty.size := by
    unfold Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE; decide
  simp [executeWitnessScript, executeWitnessScript.runExec,
    evalScriptBytes_delayed_csv_false_std chk rk dpk csv sig n hr hd hdec hnn hdis hseq,
    hsig', hempty']

theorem verifyWitnessProgram_delayed_csv_false_std (chk : ScriptChecker)
    (rk dpk : PubKey) (csv : Blocks) (sig : ByteArray) (n : ScriptNum) (program : ByteArray)
    (hr : rk.bytes.size = 33) (hd : dpk.bytes.size = 33) (hsigsz : sig.size ≤ 520)
    (hdec : decodeNum ({} : PolicyFlags) (delayBytes csv) 5 = .ok n)
    (hnn : 0 ≤ n) (hdis : Int.toNat n &&& SEQUENCE_LOCKTIME_DISABLE_FLAG = 0)
    (hseq : checkSequenceDef chk.env n = false)
    (hps : program.size = 32)
    (hprog : hashSha256 (serializeOpcodes (toLocalOps rk dpk csv)) = program) :
    verifyWitnessProgram 10 [sig, ByteArray.empty, serializeOpcodes (toLocalOps rk dpk csv)]
      0 program standardScriptFlags ({} : PolicyFlags) chk false
      = .fail .unsatisfiedLocktime := by
  simp [verifyWitnessProgram, hps, hprog, byteArray_bne_self,
    executeWitnessScript_delayed_csv_false_std chk rk dpk csv sig n
      (witnessSerSize [sig, ByteArray.empty, serializeOpcodes (toLocalOps rk dpk csv)])
      hr hd hsigsz hdec hnn hdis hseq]


/-! ### 7d. Arbitrary-fuel forms of the five headline computations

The pipeline's `pipelineFuel` is never literally `10`; these wrappers move
each verdict from the development fuel `10` to any `F > 9` (in particular
`F = pipelineFuel ...`, which is at least `62`). -/

theorem verifyWitnessProgram_delayed_std_fuel (F : Nat) (hF : 9 < F)
    (chk : ScriptChecker) (rk dpk : PubKey) (csv : Blocks) (sig : ByteArray)
    (n : ScriptNum) (program : ByteArray)
    (hr : rk.bytes.size = 33) (hd : dpk.bytes.size = 33) (hsigsz : sig.size ≤ 520)
    (hdec : decodeNum ({} : PolicyFlags) (delayBytes csv) 5 = .ok n)
    (hnn : 0 ≤ n) (hdis : Int.toNat n &&& SEQUENCE_LOCKTIME_DISABLE_FLAG = 0)
    (hseq : checkSequenceDef chk.env n = true) (hder : isValidSigEncoding sig = true)
    (hsig : chk.base.checkECDSASignature sig dpk.bytes
      (serializeOpcodes (toLocalOps rk dpk csv)) .witnessV0
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true)
    (hps : program.size = 32)
    (hprog : hashSha256 (serializeOpcodes (toLocalOps rk dpk csv)) = program) :
    verifyWitnessProgram F [sig, ByteArray.empty, serializeOpcodes (toLocalOps rk dpk csv)]
      0 program standardScriptFlags ({} : PolicyFlags) chk false = .ok := by
  rw [verifyWitnessProgram_toLocal_fuel_eq_delayed F hF rk dpk csv sig program chk
    hr hd hps hprog]
  exact verifyWitnessProgram_delayed_std chk rk dpk csv sig n program
    hr hd hsigsz hdec hnn hdis hseq hder hsig hps hprog

theorem verifyWitnessProgram_revocation_std_fuel (F : Nat) (hF : 9 < F)
    (chk : ScriptChecker) (rk dpk : PubKey) (csv : Blocks) (sig : ByteArray)
    (program : ByteArray)
    (hr : rk.bytes.size = 33) (hd : dpk.bytes.size = 33) (hsigsz : sig.size ≤ 520)
    (hder : isValidSigEncoding sig = true)
    (hsig : chk.base.checkECDSASignature sig rk.bytes
      (serializeOpcodes (toLocalOps rk dpk csv)) .witnessV0
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true)
    (hps : program.size = 32)
    (hprog : hashSha256 (serializeOpcodes (toLocalOps rk dpk csv)) = program) :
    verifyWitnessProgram F [sig, revocationSelector, serializeOpcodes (toLocalOps rk dpk csv)]
      0 program standardScriptFlags ({} : PolicyFlags) chk false = .ok := by
  rw [verifyWitnessProgram_toLocal_fuel_eq_revocation F hF rk dpk csv sig program chk
    hr hd hps hprog]
  exact verifyWitnessProgram_revocation_std chk rk dpk csv sig program
    hr hd hsigsz hder hsig hps hprog

theorem verifyWitnessProgram_delayed_bad_sig_std_fuel (F : Nat) (hF : 9 < F)
    (chk : ScriptChecker) (rk dpk : PubKey) (csv : Blocks) (sig : ByteArray)
    (n : ScriptNum) (program : ByteArray)
    (hr : rk.bytes.size = 33) (hd : dpk.bytes.size = 33) (hsigsz : sig.size ≤ 520)
    (hdec : decodeNum ({} : PolicyFlags) (delayBytes csv) 5 = .ok n)
    (hnn : 0 ≤ n) (hdis : Int.toNat n &&& SEQUENCE_LOCKTIME_DISABLE_FLAG = 0)
    (hseq : checkSequenceDef chk.env n = true) (hder : isValidSigEncoding sig = true)
    (hsig : chk.base.checkECDSASignature sig dpk.bytes
      (serializeOpcodes (toLocalOps rk dpk csv)) .witnessV0
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = false)
    (hps : program.size = 32)
    (hprog : hashSha256 (serializeOpcodes (toLocalOps rk dpk csv)) = program) :
    verifyWitnessProgram F [sig, ByteArray.empty, serializeOpcodes (toLocalOps rk dpk csv)]
      0 program standardScriptFlags ({} : PolicyFlags) chk false = .fail .evalFalse := by
  rw [verifyWitnessProgram_toLocal_fuel_eq_delayed F hF rk dpk csv sig program chk
    hr hd hps hprog]
  exact verifyWitnessProgram_delayed_bad_sig_std chk rk dpk csv sig n program
    hr hd hsigsz hdec hnn hdis hseq hder hsig hps hprog

theorem verifyWitnessProgram_revocation_bad_sig_std_fuel (F : Nat) (hF : 9 < F)
    (chk : ScriptChecker) (rk dpk : PubKey) (csv : Blocks) (sig : ByteArray)
    (program : ByteArray)
    (hr : rk.bytes.size = 33) (hd : dpk.bytes.size = 33) (hsigsz : sig.size ≤ 520)
    (hder : isValidSigEncoding sig = true)
    (hsig : chk.base.checkECDSASignature sig rk.bytes
      (serializeOpcodes (toLocalOps rk dpk csv)) .witnessV0
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = false)
    (hps : program.size = 32)
    (hprog : hashSha256 (serializeOpcodes (toLocalOps rk dpk csv)) = program) :
    verifyWitnessProgram F [sig, revocationSelector, serializeOpcodes (toLocalOps rk dpk csv)]
      0 program standardScriptFlags ({} : PolicyFlags) chk false = .fail .evalFalse := by
  rw [verifyWitnessProgram_toLocal_fuel_eq_revocation F hF rk dpk csv sig program chk
    hr hd hps hprog]
  exact verifyWitnessProgram_revocation_bad_sig_std chk rk dpk csv sig program
    hr hd hsigsz hder hsig hps hprog

theorem verifyWitnessProgram_delayed_csv_false_std_fuel (F : Nat) (hF : 9 < F)
    (chk : ScriptChecker) (rk dpk : PubKey) (csv : Blocks) (sig : ByteArray)
    (n : ScriptNum) (program : ByteArray)
    (hr : rk.bytes.size = 33) (hd : dpk.bytes.size = 33) (hsigsz : sig.size ≤ 520)
    (hdec : decodeNum ({} : PolicyFlags) (delayBytes csv) 5 = .ok n)
    (hnn : 0 ≤ n) (hdis : Int.toNat n &&& SEQUENCE_LOCKTIME_DISABLE_FLAG = 0)
    (hseq : checkSequenceDef chk.env n = false)
    (hps : program.size = 32)
    (hprog : hashSha256 (serializeOpcodes (toLocalOps rk dpk csv)) = program) :
    verifyWitnessProgram F [sig, ByteArray.empty, serializeOpcodes (toLocalOps rk dpk csv)]
      0 program standardScriptFlags ({} : PolicyFlags) chk false
      = .fail .unsatisfiedLocktime := by
  rw [verifyWitnessProgram_toLocal_fuel_eq_delayed F hF rk dpk csv sig program chk
    hr hd hps hprog]
  exact verifyWitnessProgram_delayed_csv_false_std chk rk dpk csv sig n program
    hr hd hsigsz hdec hnn hdis hseq hps hprog

/-! ## 8. Checker-level `iff` refinements at `standardScriptFlags` -/

/-- **Delayed refinement.**  With the DER premise explicit, the vendored P2WSH
verifier accepts the delayed witness exactly when the delayed-key ECDSA entry
of the concrete checker returns `true`.  The sequence context is fixed by
`hseq` (which can be discharged by `checkSequenceDef_delay_iff`). -/
theorem verifyWitnessProgram_delayed_std_iff (F : Nat) (hF : 9 < F)
    (chk : ScriptChecker) (rk dpk : PubKey) (csv : Blocks) (sig : ByteArray)
    (n : ScriptNum) (program : ByteArray)
    (hr : rk.bytes.size = 33) (hd : dpk.bytes.size = 33) (hsigsz : sig.size ≤ 520)
    (hdec : decodeNum ({} : PolicyFlags) (delayBytes csv) 5 = .ok n)
    (hnn : 0 ≤ n) (hdis : Int.toNat n &&& SEQUENCE_LOCKTIME_DISABLE_FLAG = 0)
    (hseq : checkSequenceDef chk.env n = true) (hder : isValidSigEncoding sig = true)
    (hps : program.size = 32)
    (hprog : hashSha256 (serializeOpcodes (toLocalOps rk dpk csv)) = program) :
    verifyWitnessProgram F [sig, ByteArray.empty, serializeOpcodes (toLocalOps rk dpk csv)]
        0 program standardScriptFlags ({} : PolicyFlags) chk false = .ok
      ↔ chk.base.checkECDSASignature sig dpk.bytes
          (serializeOpcodes (toLocalOps rk dpk csv)) .witnessV0
          (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true := by
  constructor
  · intro hok
    apply Classical.byContradiction
    intro hfalse
    have hfalse' : chk.base.checkECDSASignature sig dpk.bytes
        (serializeOpcodes (toLocalOps rk dpk csv)) .witnessV0
        (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = false := by
      simpa using hfalse
    have hfail := verifyWitnessProgram_delayed_bad_sig_std_fuel F hF chk rk dpk csv sig n
      program hr hd hsigsz hdec hnn hdis hseq hder hfalse' hps hprog
    rw [hfail] at hok
    cases hok
  · intro hsig
    exact verifyWitnessProgram_delayed_std_fuel F hF chk rk dpk csv sig n program
      hr hd hsigsz hdec hnn hdis hseq hder hsig hps hprog

/-- **Revocation refinement.**  Same shape for the revocation-key slot; no
sequence premise is consumed by the revocation branch. -/
theorem verifyWitnessProgram_revocation_std_iff (F : Nat) (hF : 9 < F)
    (chk : ScriptChecker) (rk dpk : PubKey) (csv : Blocks) (sig : ByteArray)
    (program : ByteArray)
    (hr : rk.bytes.size = 33) (hd : dpk.bytes.size = 33) (hsigsz : sig.size ≤ 520)
    (hder : isValidSigEncoding sig = true)
    (hps : program.size = 32)
    (hprog : hashSha256 (serializeOpcodes (toLocalOps rk dpk csv)) = program) :
    verifyWitnessProgram F [sig, revocationSelector, serializeOpcodes (toLocalOps rk dpk csv)]
        0 program standardScriptFlags ({} : PolicyFlags) chk false = .ok
      ↔ chk.base.checkECDSASignature sig rk.bytes
          (serializeOpcodes (toLocalOps rk dpk csv)) .witnessV0
          (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true := by
  constructor
  · intro hok
    apply Classical.byContradiction
    intro hfalse
    have hfalse' : chk.base.checkECDSASignature sig rk.bytes
        (serializeOpcodes (toLocalOps rk dpk csv)) .witnessV0
        (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = false := by
      simpa using hfalse
    have hfail := verifyWitnessProgram_revocation_bad_sig_std_fuel F hF chk rk dpk csv sig
      program hr hd hsigsz hder hfalse' hps hprog
    rw [hfail] at hok
    cases hok
  · intro hsig
    exact verifyWitnessProgram_revocation_std_fuel F hF chk rk dpk csv sig program
      hr hd hsigsz hder hsig hps hprog

/-! ## 9. Lane-level verdicts on the concrete transaction -/

theorem scriptLaneTx_oneInput_delayed_ok
    (rk dpk : PubKey) (csv : Blocks) (program : ByteArray) (amount : Amount)
    (sig : ByteArray) (seq : UInt32) (n : ScriptNum)
    (hr : rk.bytes.size = 33) (hd : dpk.bytes.size = 33) (hsigsz : sig.size ≤ 520)
    (hdec : decodeNum ({} : PolicyFlags) (delayBytes csv) 5 = .ok n)
    (hnn : 0 ≤ n) (hdis : Int.toNat n &&& SEQUENCE_LOCKTIME_DISABLE_FLAG = 0)
    (hseq : checkSequenceDef
      (txCheckerFor
        (oneInputTx [sig, ByteArray.empty, serializeOpcodes (toLocalOps rk dpk csv)] seq)
        0 (some amount)).env n = true)
    (hder : isValidSigEncoding sig = true)
    (hps : program.size = 32)
    (htruth : Bitcoin.Numeric.castToBool program = true)
    (hprog : hashSha256 (serializeOpcodes (toLocalOps rk dpk csv)) = program)
    (hsig : (txCheckerFor
        (oneInputTx [sig, ByteArray.empty, serializeOpcodes (toLocalOps rk dpk csv)] seq)
        0 (some amount)).base.checkECDSASignature sig dpk.bytes
        (serializeOpcodes (toLocalOps rk dpk csv)) .witnessV0
        (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true) :
    scriptLaneTx
      (oneInputTx [sig, ByteArray.empty, serializeOpcodes (toLocalOps rk dpk csv)] seq)
      (probeTable program amount) standardScriptFlags ({} : PolicyFlags) = some true := by
  apply scriptLaneTx_oneInput_ok _ _ _ _ hps htruth
  exact verifyWitnessProgram_delayed_std_fuel _ (pipelineFuel_oneInput_gt_nine program _)
    (txCheckerFor
      (oneInputTx [sig, ByteArray.empty, serializeOpcodes (toLocalOps rk dpk csv)] seq)
      0 (some amount))
    rk dpk csv sig n program hr hd hsigsz hdec hnn hdis hseq hder hsig hps hprog

theorem scriptLaneTx_oneInput_revocation_ok
    (rk dpk : PubKey) (csv : Blocks) (program : ByteArray) (amount : Amount)
    (sig : ByteArray) (seq : UInt32)
    (hr : rk.bytes.size = 33) (hd : dpk.bytes.size = 33) (hsigsz : sig.size ≤ 520)
    (hder : isValidSigEncoding sig = true)
    (hps : program.size = 32)
    (htruth : Bitcoin.Numeric.castToBool program = true)
    (hprog : hashSha256 (serializeOpcodes (toLocalOps rk dpk csv)) = program)
    (hsig : (txCheckerFor
        (oneInputTx [sig, revocationSelector, serializeOpcodes (toLocalOps rk dpk csv)] seq)
        0 (some amount)).base.checkECDSASignature sig rk.bytes
        (serializeOpcodes (toLocalOps rk dpk csv)) .witnessV0
        (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true) :
    scriptLaneTx
      (oneInputTx [sig, revocationSelector, serializeOpcodes (toLocalOps rk dpk csv)] seq)
      (probeTable program amount) standardScriptFlags ({} : PolicyFlags) = some true := by
  apply scriptLaneTx_oneInput_ok _ _ _ _ hps htruth
  exact verifyWitnessProgram_revocation_std_fuel _ (pipelineFuel_oneInput_gt_nine program _)
    (txCheckerFor
      (oneInputTx [sig, revocationSelector, serializeOpcodes (toLocalOps rk dpk csv)] seq)
      0 (some amount))
    rk dpk csv sig program hr hd hsigsz hder hsig hps hprog

theorem scriptLaneTx_oneInput_delayed_bad_sig
    (rk dpk : PubKey) (csv : Blocks) (program : ByteArray) (amount : Amount)
    (sig : ByteArray) (seq : UInt32) (n : ScriptNum)
    (hr : rk.bytes.size = 33) (hd : dpk.bytes.size = 33) (hsigsz : sig.size ≤ 520)
    (hdec : decodeNum ({} : PolicyFlags) (delayBytes csv) 5 = .ok n)
    (hnn : 0 ≤ n) (hdis : Int.toNat n &&& SEQUENCE_LOCKTIME_DISABLE_FLAG = 0)
    (hseq : checkSequenceDef
      (txCheckerFor
        (oneInputTx [sig, ByteArray.empty, serializeOpcodes (toLocalOps rk dpk csv)] seq)
        0 (some amount)).env n = true)
    (hder : isValidSigEncoding sig = true)
    (hps : program.size = 32)
    (htruth : Bitcoin.Numeric.castToBool program = true)
    (hprog : hashSha256 (serializeOpcodes (toLocalOps rk dpk csv)) = program)
    (hsig : (txCheckerFor
        (oneInputTx [sig, ByteArray.empty, serializeOpcodes (toLocalOps rk dpk csv)] seq)
        0 (some amount)).base.checkECDSASignature sig dpk.bytes
        (serializeOpcodes (toLocalOps rk dpk csv)) .witnessV0
        (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = false) :
    scriptLaneTx
      (oneInputTx [sig, ByteArray.empty, serializeOpcodes (toLocalOps rk dpk csv)] seq)
      (probeTable program amount) standardScriptFlags ({} : PolicyFlags) = some false := by
  apply scriptLaneTx_oneInput_fail _ _ _ _ hps htruth .evalFalse
  exact verifyWitnessProgram_delayed_bad_sig_std_fuel _ (pipelineFuel_oneInput_gt_nine program _)
    (txCheckerFor
      (oneInputTx [sig, ByteArray.empty, serializeOpcodes (toLocalOps rk dpk csv)] seq)
      0 (some amount))
    rk dpk csv sig n program hr hd hsigsz hdec hnn hdis hseq hder hsig hps hprog

theorem scriptLaneTx_oneInput_delayed_csv_false
    (rk dpk : PubKey) (csv : Blocks) (program : ByteArray) (amount : Amount)
    (sig : ByteArray) (seq : UInt32) (n : ScriptNum)
    (hr : rk.bytes.size = 33) (hd : dpk.bytes.size = 33) (hsigsz : sig.size ≤ 520)
    (hdec : decodeNum ({} : PolicyFlags) (delayBytes csv) 5 = .ok n)
    (hnn : 0 ≤ n) (hdis : Int.toNat n &&& SEQUENCE_LOCKTIME_DISABLE_FLAG = 0)
    (hseq : checkSequenceDef
      (txCheckerFor
        (oneInputTx [sig, ByteArray.empty, serializeOpcodes (toLocalOps rk dpk csv)] seq)
        0 (some amount)).env n = false)
    (hps : program.size = 32)
    (htruth : Bitcoin.Numeric.castToBool program = true)
    (hprog : hashSha256 (serializeOpcodes (toLocalOps rk dpk csv)) = program) :
    scriptLaneTx
      (oneInputTx [sig, ByteArray.empty, serializeOpcodes (toLocalOps rk dpk csv)] seq)
      (probeTable program amount) standardScriptFlags ({} : PolicyFlags) = some false := by
  apply scriptLaneTx_oneInput_fail _ _ _ _ hps htruth .unsatisfiedLocktime
  exact verifyWitnessProgram_delayed_csv_false_std_fuel _ (pipelineFuel_oneInput_gt_nine program _)
    (txCheckerFor
      (oneInputTx [sig, ByteArray.empty, serializeOpcodes (toLocalOps rk dpk csv)] seq)
      0 (some amount))
    rk dpk csv sig n program hr hd hsigsz hdec hnn hdis hseq hps hprog

theorem scriptLaneTx_oneInput_revocation_bad_sig
    (rk dpk : PubKey) (csv : Blocks) (program : ByteArray) (amount : Amount)
    (sig : ByteArray) (seq : UInt32)
    (hr : rk.bytes.size = 33) (hd : dpk.bytes.size = 33) (hsigsz : sig.size ≤ 520)
    (hder : isValidSigEncoding sig = true)
    (hps : program.size = 32)
    (htruth : Bitcoin.Numeric.castToBool program = true)
    (hprog : hashSha256 (serializeOpcodes (toLocalOps rk dpk csv)) = program)
    (hsig : (txCheckerFor
        (oneInputTx [sig, revocationSelector, serializeOpcodes (toLocalOps rk dpk csv)] seq)
        0 (some amount)).base.checkECDSASignature sig rk.bytes
        (serializeOpcodes (toLocalOps rk dpk csv)) .witnessV0
        (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = false) :
    scriptLaneTx
      (oneInputTx [sig, revocationSelector, serializeOpcodes (toLocalOps rk dpk csv)] seq)
      (probeTable program amount) standardScriptFlags ({} : PolicyFlags) = some false := by
  apply scriptLaneTx_oneInput_fail _ _ _ _ hps htruth .evalFalse
  exact verifyWitnessProgram_revocation_bad_sig_std_fuel _ (pipelineFuel_oneInput_gt_nine program _)
    (txCheckerFor
      (oneInputTx [sig, revocationSelector, serializeOpcodes (toLocalOps rk dpk csv)] seq)
      0 (some amount))
    rk dpk csv sig program hr hd hsigsz hder hsig hps hprog


/-- **Lane-level delayed refinement.**  On the concrete one-input transaction,
`scriptLaneTx = some true` is equivalent to the delayed-key ECDSA entry of the
pipeline checker.  All table, amount, flag, sequence, DER, program-size and
program-hash premises are explicit. -/
theorem scriptLaneTx_oneInput_delayed_iff
    (rk dpk : PubKey) (csv : Blocks) (program : ByteArray) (amount : Amount)
    (sig : ByteArray) (seq : UInt32) (n : ScriptNum)
    (hr : rk.bytes.size = 33) (hd : dpk.bytes.size = 33) (hsigsz : sig.size ≤ 520)
    (hdec : decodeNum ({} : PolicyFlags) (delayBytes csv) 5 = .ok n)
    (hnn : 0 ≤ n) (hdis : Int.toNat n &&& SEQUENCE_LOCKTIME_DISABLE_FLAG = 0)
    (hseq : checkSequenceDef
      (txCheckerFor
        (oneInputTx [sig, ByteArray.empty, serializeOpcodes (toLocalOps rk dpk csv)] seq)
        0 (some amount)).env n = true)
    (hder : isValidSigEncoding sig = true)
    (hps : program.size = 32)
    (htruth : Bitcoin.Numeric.castToBool program = true)
    (hprog : hashSha256 (serializeOpcodes (toLocalOps rk dpk csv)) = program) :
    scriptLaneTx
        (oneInputTx [sig, ByteArray.empty, serializeOpcodes (toLocalOps rk dpk csv)] seq)
        (probeTable program amount) standardScriptFlags ({} : PolicyFlags) = some true
      ↔ (txCheckerFor
          (oneInputTx [sig, ByteArray.empty, serializeOpcodes (toLocalOps rk dpk csv)] seq)
          0 (some amount)).base.checkECDSASignature sig dpk.bytes
          (serializeOpcodes (toLocalOps rk dpk csv)) .witnessV0
          (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true := by
  rw [scriptLaneTx_oneInput_ok_iff program amount
    [sig, ByteArray.empty, serializeOpcodes (toLocalOps rk dpk csv)] seq hps htruth]
  exact verifyWitnessProgram_delayed_std_iff _ (pipelineFuel_oneInput_gt_nine program _)
    (txCheckerFor
      (oneInputTx [sig, ByteArray.empty, serializeOpcodes (toLocalOps rk dpk csv)] seq)
      0 (some amount))
    rk dpk csv sig n program hr hd hsigsz hdec hnn hdis hseq hder hps hprog

/-- **Lane-level revocation refinement.**  Same shape for the revocation-key
slot, with no sequence premise. -/
theorem scriptLaneTx_oneInput_revocation_iff
    (rk dpk : PubKey) (csv : Blocks) (program : ByteArray) (amount : Amount)
    (sig : ByteArray) (seq : UInt32)
    (hr : rk.bytes.size = 33) (hd : dpk.bytes.size = 33) (hsigsz : sig.size ≤ 520)
    (hder : isValidSigEncoding sig = true)
    (hps : program.size = 32)
    (htruth : Bitcoin.Numeric.castToBool program = true)
    (hprog : hashSha256 (serializeOpcodes (toLocalOps rk dpk csv)) = program) :
    scriptLaneTx
        (oneInputTx [sig, revocationSelector, serializeOpcodes (toLocalOps rk dpk csv)] seq)
        (probeTable program amount) standardScriptFlags ({} : PolicyFlags) = some true
      ↔ (txCheckerFor
          (oneInputTx [sig, revocationSelector, serializeOpcodes (toLocalOps rk dpk csv)] seq)
          0 (some amount)).base.checkECDSASignature sig rk.bytes
          (serializeOpcodes (toLocalOps rk dpk csv)) .witnessV0
          (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true := by
  rw [scriptLaneTx_oneInput_ok_iff program amount
    [sig, revocationSelector, serializeOpcodes (toLocalOps rk dpk csv)] seq hps htruth]
  exact verifyWitnessProgram_revocation_std_iff _ (pipelineFuel_oneInput_gt_nine program _)
    (txCheckerFor
      (oneInputTx [sig, revocationSelector, serializeOpcodes (toLocalOps rk dpk csv)] seq)
      0 (some amount))
    rk dpk csv sig program hr hd hsigsz hder hps hprog

/-! ## 10. Full-pipeline verdicts -/

theorem txVerdictFull_oneInput_delayed_ok
    (rk dpk : PubKey) (csv : Blocks) (program : ByteArray) (amount : Amount)
    (sig : ByteArray) (seq : UInt32) (n : ScriptNum) (sh : UInt32)
    (hr : rk.bytes.size = 33) (hd : dpk.bytes.size = 33) (hsigsz : sig.size ≤ 520)
    (hdec : decodeNum ({} : PolicyFlags) (delayBytes csv) 5 = .ok n)
    (hnn : 0 ≤ n) (hdis : Int.toNat n &&& SEQUENCE_LOCKTIME_DISABLE_FLAG = 0)
    (hseq : checkSequenceDef
      (txCheckerFor
        (oneInputTx [sig, ByteArray.empty, serializeOpcodes (toLocalOps rk dpk csv)] seq)
        0 (some amount)).env n = true)
    (hder : isValidSigEncoding sig = true)
    (hps : program.size = 32)
    (htruth : Bitcoin.Numeric.castToBool program = true)
    (hprog : hashSha256 (serializeOpcodes (toLocalOps rk dpk csv)) = program)
    (hsig : (txCheckerFor
        (oneInputTx [sig, ByteArray.empty, serializeOpcodes (toLocalOps rk dpk csv)] seq)
        0 (some amount)).base.checkECDSASignature sig dpk.bytes
        (serializeOpcodes (toLocalOps rk dpk csv)) .witnessV0
        (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true) :
    txVerdictFull
      (oneInputTx [sig, ByteArray.empty, serializeOpcodes (toLocalOps rk dpk csv)] seq)
      (probeTable program amount) probeUtxo sh standardScriptFlags ({} : PolicyFlags)
      = some true := by
  rw [txVerdictFull_oneInput _ _ _ _ _ _
    (oneInputTx_checkTransaction _ _) (oneInputTx_not_coinbase _ _)
    (probeTable_supplied _ _ _ _) (probeTable_amountsKnown _ _ _ _) (probeUtxo_feeOk _ _ _)]
  exact scriptLaneTx_oneInput_delayed_ok rk dpk csv program amount sig seq n hr hd hsigsz
    hdec hnn hdis hseq hder hps htruth hprog hsig

theorem txVerdictFull_oneInput_revocation_ok
    (rk dpk : PubKey) (csv : Blocks) (program : ByteArray) (amount : Amount)
    (sig : ByteArray) (seq : UInt32) (sh : UInt32)
    (hr : rk.bytes.size = 33) (hd : dpk.bytes.size = 33) (hsigsz : sig.size ≤ 520)
    (hder : isValidSigEncoding sig = true)
    (hps : program.size = 32)
    (htruth : Bitcoin.Numeric.castToBool program = true)
    (hprog : hashSha256 (serializeOpcodes (toLocalOps rk dpk csv)) = program)
    (hsig : (txCheckerFor
        (oneInputTx [sig, revocationSelector, serializeOpcodes (toLocalOps rk dpk csv)] seq)
        0 (some amount)).base.checkECDSASignature sig rk.bytes
        (serializeOpcodes (toLocalOps rk dpk csv)) .witnessV0
        (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true) :
    txVerdictFull
      (oneInputTx [sig, revocationSelector, serializeOpcodes (toLocalOps rk dpk csv)] seq)
      (probeTable program amount) probeUtxo sh standardScriptFlags ({} : PolicyFlags)
      = some true := by
  rw [txVerdictFull_oneInput _ _ _ _ _ _
    (oneInputTx_checkTransaction _ _) (oneInputTx_not_coinbase _ _)
    (probeTable_supplied _ _ _ _) (probeTable_amountsKnown _ _ _ _) (probeUtxo_feeOk _ _ _)]
  exact scriptLaneTx_oneInput_revocation_ok rk dpk csv program amount sig seq hr hd hsigsz
    hder hps htruth hprog hsig

theorem txVerdictFull_oneInput_delayed_bad_sig
    (rk dpk : PubKey) (csv : Blocks) (program : ByteArray) (amount : Amount)
    (sig : ByteArray) (seq : UInt32) (n : ScriptNum) (sh : UInt32)
    (hr : rk.bytes.size = 33) (hd : dpk.bytes.size = 33) (hsigsz : sig.size ≤ 520)
    (hdec : decodeNum ({} : PolicyFlags) (delayBytes csv) 5 = .ok n)
    (hnn : 0 ≤ n) (hdis : Int.toNat n &&& SEQUENCE_LOCKTIME_DISABLE_FLAG = 0)
    (hseq : checkSequenceDef
      (txCheckerFor
        (oneInputTx [sig, ByteArray.empty, serializeOpcodes (toLocalOps rk dpk csv)] seq)
        0 (some amount)).env n = true)
    (hder : isValidSigEncoding sig = true)
    (hps : program.size = 32)
    (htruth : Bitcoin.Numeric.castToBool program = true)
    (hprog : hashSha256 (serializeOpcodes (toLocalOps rk dpk csv)) = program)
    (hsig : (txCheckerFor
        (oneInputTx [sig, ByteArray.empty, serializeOpcodes (toLocalOps rk dpk csv)] seq)
        0 (some amount)).base.checkECDSASignature sig dpk.bytes
        (serializeOpcodes (toLocalOps rk dpk csv)) .witnessV0
        (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = false) :
    txVerdictFull
      (oneInputTx [sig, ByteArray.empty, serializeOpcodes (toLocalOps rk dpk csv)] seq)
      (probeTable program amount) probeUtxo sh standardScriptFlags ({} : PolicyFlags)
      = some false := by
  rw [txVerdictFull_oneInput _ _ _ _ _ _
    (oneInputTx_checkTransaction _ _) (oneInputTx_not_coinbase _ _)
    (probeTable_supplied _ _ _ _) (probeTable_amountsKnown _ _ _ _) (probeUtxo_feeOk _ _ _)]
  exact scriptLaneTx_oneInput_delayed_bad_sig rk dpk csv program amount sig seq n hr hd hsigsz
    hdec hnn hdis hseq hder hps htruth hprog hsig

theorem txVerdictFull_oneInput_delayed_csv_false
    (rk dpk : PubKey) (csv : Blocks) (program : ByteArray) (amount : Amount)
    (sig : ByteArray) (seq : UInt32) (n : ScriptNum) (sh : UInt32)
    (hr : rk.bytes.size = 33) (hd : dpk.bytes.size = 33) (hsigsz : sig.size ≤ 520)
    (hdec : decodeNum ({} : PolicyFlags) (delayBytes csv) 5 = .ok n)
    (hnn : 0 ≤ n) (hdis : Int.toNat n &&& SEQUENCE_LOCKTIME_DISABLE_FLAG = 0)
    (hseq : checkSequenceDef
      (txCheckerFor
        (oneInputTx [sig, ByteArray.empty, serializeOpcodes (toLocalOps rk dpk csv)] seq)
        0 (some amount)).env n = false)
    (hps : program.size = 32)
    (htruth : Bitcoin.Numeric.castToBool program = true)
    (hprog : hashSha256 (serializeOpcodes (toLocalOps rk dpk csv)) = program) :
    txVerdictFull
      (oneInputTx [sig, ByteArray.empty, serializeOpcodes (toLocalOps rk dpk csv)] seq)
      (probeTable program amount) probeUtxo sh standardScriptFlags ({} : PolicyFlags)
      = some false := by
  rw [txVerdictFull_oneInput _ _ _ _ _ _
    (oneInputTx_checkTransaction _ _) (oneInputTx_not_coinbase _ _)
    (probeTable_supplied _ _ _ _) (probeTable_amountsKnown _ _ _ _) (probeUtxo_feeOk _ _ _)]
  exact scriptLaneTx_oneInput_delayed_csv_false rk dpk csv program amount sig seq n hr hd hsigsz
    hdec hnn hdis hseq hps htruth hprog

theorem txVerdictFull_oneInput_revocation_bad_sig
    (rk dpk : PubKey) (csv : Blocks) (program : ByteArray) (amount : Amount)
    (sig : ByteArray) (seq : UInt32) (sh : UInt32)
    (hr : rk.bytes.size = 33) (hd : dpk.bytes.size = 33) (hsigsz : sig.size ≤ 520)
    (hder : isValidSigEncoding sig = true)
    (hps : program.size = 32)
    (htruth : Bitcoin.Numeric.castToBool program = true)
    (hprog : hashSha256 (serializeOpcodes (toLocalOps rk dpk csv)) = program)
    (hsig : (txCheckerFor
        (oneInputTx [sig, revocationSelector, serializeOpcodes (toLocalOps rk dpk csv)] seq)
        0 (some amount)).base.checkECDSASignature sig rk.bytes
        (serializeOpcodes (toLocalOps rk dpk csv)) .witnessV0
        (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = false) :
    txVerdictFull
      (oneInputTx [sig, revocationSelector, serializeOpcodes (toLocalOps rk dpk csv)] seq)
      (probeTable program amount) probeUtxo sh standardScriptFlags ({} : PolicyFlags)
      = some false := by
  rw [txVerdictFull_oneInput _ _ _ _ _ _
    (oneInputTx_checkTransaction _ _) (oneInputTx_not_coinbase _ _)
    (probeTable_supplied _ _ _ _) (probeTable_amountsKnown _ _ _ _) (probeUtxo_feeOk _ _ _)]
  exact scriptLaneTx_oneInput_revocation_bad_sig rk dpk csv program amount sig seq hr hd hsigsz
    hder hps htruth hprog hsig

/-! ## 11. Consensus-height flag corollary -/

/-- At any non-exception mainnet height above the last buried deployment,
`getBlockScriptFlags` is exactly `standardScriptFlags`; hence every verdict
above holds at the consensus flag word for such a height. -/
theorem txVerdictFull_oneInput_delayed_ok_at_height
    (rk dpk : PubKey) (csv : Blocks) (program : ByteArray) (amount : Amount)
    (sig : ByteArray) (seq : UInt32) (n : ScriptNum) (sh height : UInt32)
    (hheight : Bitcoin.Activation.BIP147_HEIGHT < height)
    (hexc : height ∉ Bitcoin.Activation.EXCEPTION_HEIGHTS)
    (hr : rk.bytes.size = 33) (hd : dpk.bytes.size = 33) (hsigsz : sig.size ≤ 520)
    (hdec : decodeNum ({} : PolicyFlags) (delayBytes csv) 5 = .ok n)
    (hnn : 0 ≤ n) (hdis : Int.toNat n &&& SEQUENCE_LOCKTIME_DISABLE_FLAG = 0)
    (hseq : checkSequenceDef
      (txCheckerFor
        (oneInputTx [sig, ByteArray.empty, serializeOpcodes (toLocalOps rk dpk csv)] seq)
        0 (some amount)).env n = true)
    (hder : isValidSigEncoding sig = true)
    (hps : program.size = 32)
    (htruth : Bitcoin.Numeric.castToBool program = true)
    (hprog : hashSha256 (serializeOpcodes (toLocalOps rk dpk csv)) = program)
    (hsig : (txCheckerFor
        (oneInputTx [sig, ByteArray.empty, serializeOpcodes (toLocalOps rk dpk csv)] seq)
        0 (some amount)).base.checkECDSASignature sig dpk.bytes
        (serializeOpcodes (toLocalOps rk dpk csv)) .witnessV0
        (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true) :
    txVerdictFull
      (oneInputTx [sig, ByteArray.empty, serializeOpcodes (toLocalOps rk dpk csv)] seq)
      (probeTable program amount) probeUtxo sh (getBlockScriptFlags height)
      ({} : PolicyFlags) = some true := by
  rw [Bitcoin.Activation.flags_after_burial height hheight hexc]
  exact txVerdictFull_oneInput_delayed_ok rk dpk csv program amount sig seq n sh hr hd hsigsz
    hdec hnn hdis hseq hder hps htruth hprog hsig

end LnLean.Proofs.WaveH.H04
