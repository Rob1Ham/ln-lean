import Bitcoin.Interpreter.Defs
import LnLean.Proofs.Bitcoin.InterpreterBridgeTargets

/-!
# Vendor bridge for the `to_local` revocation branch

This module is the Wave-6 (lane `S6-L1-REVOKE`) companion of the Wave-5
bridge `LnLean.Proofs.Bitcoin.InterpreterBridgeTargets`.  Wave 5 connected
the BOLT 3 funding script and the **delayed** (`OP_ELSE`) branch of
`to_local` to the vendored interpreter in
`vendor/btc-lean-core/Bitcoin/Interpreter/Defs.lean`, but left the
**revocation** (`OP_IF` true) branch unmechanized at the vendor level.  This
module closes exactly that gap, without editing the Wave-5 file (it is
imported, not modified).

The BOLT 3 `to_local` witness script is

```text
OP_IF <revocationpubkey>
OP_ELSE <to_self_delay> OP_CSV OP_DROP <local_delayedpubkey>
OP_ENDIF OP_CHECKSIG
```

and the two witness shapes are

* revocation: `[<sig>, 0x01]` (machine stack `[0x01, sig]`), and
* delayed:    `[<sig>, <>]`    (machine stack `[<>, sig]`).

What is mechanized here:

* the vendored `evalFrom` computation of the **revocation** branch on the
  concrete `toLocalWireOps` list: `OP_IF` consumes the `0x01` selector,
  pushes the revocation key, `OP_ELSE` flips the execution flag, every
  opcode of the (unexecuted) delayed block is skipped by the vendored
  step function, `OP_ENDIF` closes the conditional, and `OP_CHECKSIG`
  verifies against the **revocation** key;
* the same computation lifted through `evalScriptBytes`,
  `executeWitnessScript` and `verifyWitnessProgram` (P2WSH), so a real
  `verifyWitnessProgram` returns `.ok` on the revocation witness;
* the model-side spend instantiated with `vendorLaws` (no CSV law is
  required on this branch), and a joint agreement theorem;
* **branch selection**: with the same signature, the `0x01` selector takes
  the revocation branch and does not consult `OP_CSV` at all, while the
  empty selector takes the delayed branch and fails with
  `unsatisfiedLocktime` when `checkSequenceDef` is false;
* **negative results**: (a) a wrong-key (non-revocation-key) signature
  makes the revocation branch push `false`, and the full P2WSH verifier
  returns `.fail .evalFalse`; (b) a valid revocation-key signature under
  the empty selector does not spend the output when the sequence check
  fails (`.fail .unsatisfiedLocktime`).

What is deliberately *not* claimed (the same boundary as Wave 5):

* BIP 143 sighash construction: the vendored checker receives the script
  code and `ScriptExecutionData`; the ECDSA calls remain explicit
  hypotheses.  A successful check means "the checker says this signature
  is valid for this script under its own sighash construction", not a
  proved cryptographic fact (assumption C3 in `docs/ASSUMPTIONS.md`);
* constructing the transaction/locktime environment: the revocation
  branch does not read `chk.env` at all, so no environment hypothesis
  appears in the positive revocation theorems.  The negative wrong-branch
  theorem does read `checkSequenceDef chk.env n`, and takes the decoded
  delay `n` and its non-negativity/disable-bit conditions as hypotheses,
  exactly as Wave 5 did;
* the converse direction (`verifyWitnessProgram = .ok` implies the model
  `P2WSHSpend`) and full `VerifyScript`/consensus acceptance.  The
  statements here are one-directional consequences plus concrete failure
  outcomes;
* any change to vendored sources.  This module is a client of the frozen
  vendor API.

Anchors:

* BOLT 3 §`to_local` Output (`refs/bolts/03-transactions.md:113-135`).
* BIP 141 (P2WSH), BIP 143 (sighash), BIP 112 (`OP_CSV`).
* `refs/rust-lightning/lightning/src/ln/chan_utils.rs:687-700`
  (`get_revokeable_redeemscript`).
-/

namespace LnLean.Proofs.Bitcoin.InterpreterRevocationTargets

set_option autoImplicit false

open Bitcoin.Data
open Bitcoin.Activation
open Bitcoin.Script.Parser
open Bitcoin.Interpreter
open LnLean
open LnLean.Bitcoin
open LnLean.Proofs.Bitcoin.FundingScriptTargets
open LnLean.Proofs.Bitcoin.SpendTargets
open LnLean.Proofs.Bitcoin.InterpreterBridgeTargets

/-! ## 1. The selector and the two witness shapes -/

/-- The revocation-branch selector: the canonical `0x01` stack element.
It is the model's `oneByte`, so the model and vendor stacks use the same
bytes. -/
def revocationSelector : ByteArray := ByteArray.mk #[0x01]

theorem revocationSelector_eq_oneByte : revocationSelector = oneByte := rfl

/-- The delayed-branch selector: the empty stack element (the model's
`zeroByte`). -/
theorem delayedSelector_eq_zeroByte :
    (ByteArray.empty : ByteArray) = zeroByte := rfl

@[simp] theorem castToBool_revocationSelector :
    Bitcoin.Numeric.castToBool revocationSelector = true := by decide

@[simp] theorem revocationSelector_size : revocationSelector.size = 1 := rfl

@[simp] theorem byteArray_mk_one_size : (ByteArray.mk #[0x01]).size = 1 := rfl

@[simp] theorem castToBool_empty_byteArray :
    Bitcoin.Numeric.castToBool (ByteArray.empty : ByteArray) = false := by decide

/-! ## 2. Vendor evaluation of the revocation branch -/

/-- **Vendor `evalFrom` computation for the `OP_IF` (revocation) branch of
`to_local`.**  The witness supplies the `0x01` selector and a signature, so
the machine starts with the selector on top.  The vendored machine takes
the true branch, pushes the revocation key, skips the entire `OP_ELSE`
block (`<delay> OP_CSV OP_DROP <delayed key>`) because the execution flag
is false, closes the conditional, and runs `OP_CHECKSIG` against the
revocation key.

The only non-computational input is the vendored ECDSA check.  In
particular this theorem has **no** delay-decode, sequence, locktime or
policy hypothesis: the revocation branch never reads the environment. -/
theorem evalFrom_toLocalWireOps_revocation (chk : ScriptChecker)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks) (sig : ByteArray)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsig : chk.base.checkECDSASignature sig revocationKey.bytes
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      .witnessV0 (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true) :
    evalFrom
      { flags := ({ csv := true } : ScriptFlags), pol := ({} : PolicyFlags), chk := chk,
        sv := .witnessV0,
        bytes := serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv),
        ed := (default : Bitcoin.Crypto.Seam.ScriptExecutionData) }
      10 (toLocalWireOps revocationKey delayedPaymentKey csv)
      { stack := [revocationSelector, sig], alt := [], vf := [], opCount := 0,
        codeSep := 0, vwLeft := none }
    = Except.ok
        { stack := [ByteArray.mk #[0x01]], alt := [], vf := [], opCount := 6,
          codeSep := 0, vwLeft := none } := by
  simp [toLocalWireOps, evalFrom, stepChecked, stepBody, stepBody.dispatchOp,
    evalChecksigDispatch, evalChecksigPreTapscript, checkSigEncoding, checkPubKeyEncoding,
    topAt, pushBoolV, vchTrue, serU8, disabledWire,
    Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE, MAX_STACK_SIZE, MAX_OPS_PER_SCRIPT,
    toLocalDelayBytes_size, empty_push_mk, hsig, hr, hd]

/-- The revocation branch at the `EvalScript` entry point. -/
theorem evalScriptBytes_toLocal_revocation (chk : ScriptChecker)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks) (sig : ByteArray)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsig : chk.base.checkECDSASignature sig revocationKey.bytes
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      .witnessV0 (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true) :
    evalScriptBytes 10 ({ csv := true } : ScriptFlags) ({} : PolicyFlags)
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      [revocationSelector, sig] chk .witnessV0
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData)
    = Except.ok [ByteArray.mk #[0x01]] := by
  unfold evalScriptBytes
  have hsz : (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)).size = 77 :=
    serializeOpcodes_toLocal_size revocationKey delayedPaymentKey csv hr hd
  rw [ite_eq_right (by simp [hsz, MAX_SCRIPT_SIZE])]
  rw [toLocal_parseWire revocationKey delayedPaymentKey csv hr hd]
  simp [finalStack,
    evalFrom_toLocalWireOps_revocation chk revocationKey delayedPaymentKey csv sig
      hr hd hsig]

/-- The revocation branch at the witness-script entry point. -/
theorem executeWitnessScript_toLocal_revocation (chk : ScriptChecker)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (vwSer : Int)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hsig : chk.base.checkECDSASignature sig revocationKey.bytes
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      .witnessV0 (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true) :
    executeWitnessScript 10 [sig, revocationSelector] vwSer
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      ({ csv := true } : ScriptFlags) ({} : PolicyFlags) chk .witnessV0 = .ok := by
  have hsig' : ¬ Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE < sig.size := by
    unfold Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE; omega
  simp [executeWitnessScript, executeWitnessScript.runExec,
    evalScriptBytes_toLocal_revocation chk revocationKey delayedPaymentKey csv sig
      hr hd hsig,
    hsig', Bitcoin.Numeric.castToBool]
  decide

/-- The revocation branch at the full P2WSH verifier: the real
`verifyWitnessProgram` returns `.ok` for the revocation witness
`[sig, 0x01, witnessScript]` whenever the vendored checker accepts the
revocation-key signature. -/
theorem verifyWitnessProgram_toLocal_revocation (chk : ScriptChecker)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (program : ByteArray)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hsig : chk.base.checkECDSASignature sig revocationKey.bytes
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      .witnessV0 (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true)
    (hps : program.size = 32)
    (hprog : hashSha256
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)) = program) :
    verifyWitnessProgram 10
      [sig, revocationSelector,
        serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)]
      0 program ({ csv := true } : ScriptFlags) ({} : PolicyFlags) chk false = .ok := by
  simp [verifyWitnessProgram, hps, hprog, byteArray_bne_self,
    executeWitnessScript_toLocal_revocation chk revocationKey delayedPaymentKey csv sig
      (witnessSerSize [sig, revocationSelector,
        serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)])
      hr hd hsigsz hsig]

/-! ## 3. Model-side revocation spend and agreement -/

/-- Model-side `P2WSHSpend` for the revocation branch, using the vendored
signature law `vendorLaws`.  No `csvOk` hypothesis appears: the model's
`exec_toLocal_revocation` never consults it, matching the vendor
computation above. -/
theorem toLocal_model_spend_revocation (chk : ScriptChecker) (msg : ByteArray)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks) (sig : ByteArray)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsig : chk.base.checkECDSASignature sig revocationKey.bytes
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      .witnessV0 (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true) :
    P2WSHSpend (vendorLaws chk
        (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)))
      msg
      (hashSha256 (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)))
      (toLocalScriptFull revocationKey delayedPaymentKey csv).bytes
      (toLocalProg revocationKey delayedPaymentKey csv) [oneByte, sig] := by
  have hsig' : (vendorLaws chk
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))).sigCheck
      revocationKey.bytes msg sig = true := by
    simpa [vendorLaws] using hsig
  have hbytes : (toLocalScriptFull revocationKey delayedPaymentKey csv).bytes =
      serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv) := by
    rw [← toLocalProg_serialize revocationKey delayedPaymentKey csv,
      toLocal_serialize_eq revocationKey delayedPaymentKey csv (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩
  · rw [hbytes]
    exact toLocal_serialize_eq revocationKey delayedPaymentKey csv (by omega) (by omega)
  · simp [vendorLaws, hbytes]
  · exact exec_toLocal_revocation
      (vendorLaws chk
        (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)))
      msg revocationKey delayedPaymentKey csv sig hsig'

/-- **Revocation-branch agreement (positive direction).**  The real
vendored P2WSH verifier returns `.ok`, and the Wave-4 model's
`P2WSHSpend` holds with `vendorLaws`, under the same vendored ECDSA
hypothesis.  The selector `oneByte` is shared by both stacks. -/
theorem toLocal_revocation_interpreters_agree (chk : ScriptChecker)
    (msg : ByteArray)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hsig : chk.base.checkECDSASignature sig revocationKey.bytes
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      .witnessV0 (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true) :
    verifyWitnessProgram 10
        [sig, revocationSelector,
          serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)]
        0
        (hashSha256 (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)))
        ({ csv := true } : ScriptFlags) ({} : PolicyFlags) chk false = .ok ∧
      P2WSHSpend (vendorLaws chk
          (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)))
        msg
        (hashSha256 (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)))
        (toLocalScriptFull revocationKey delayedPaymentKey csv).bytes
        (toLocalProg revocationKey delayedPaymentKey csv) [oneByte, sig] := by
  refine ⟨?_, ?_⟩
  · exact verifyWitnessProgram_toLocal_revocation chk revocationKey delayedPaymentKey
      csv sig _ hr hd hsigsz hsig (hashSha256_size _) rfl
  · exact toLocal_model_spend_revocation chk msg revocationKey delayedPaymentKey csv sig
      hr hd hsig

/-- The model-side spend is insensitive to the CSV law as well: for any
value `n`, the `vendorLawsCSV` instantiation still spends the revocation
branch, because `toLocalProg`'s revocation path never calls `csvOk`.
This is the model counterpart of the vendor fact that `OP_CSV` is never
executed on the true branch. -/
theorem toLocal_model_spend_revocation_csv_law (chk : ScriptChecker) (msg : ByteArray)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks) (sig : ByteArray)
    (n : Bitcoin.Numeric.ScriptNum)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsig : chk.base.checkECDSASignature sig revocationKey.bytes
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      .witnessV0 (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true) :
    P2WSHSpend (vendorLawsCSV chk
        (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)) n)
      msg
      (hashSha256 (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)))
      (toLocalScriptFull revocationKey delayedPaymentKey csv).bytes
      (toLocalProg revocationKey delayedPaymentKey csv) [oneByte, sig] := by
  have hsig' : (vendorLawsCSV chk
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)) n).sigCheck
      revocationKey.bytes msg sig = true := by
    simpa [vendorLawsCSV, vendorLaws] using hsig
  have hbytes : (toLocalScriptFull revocationKey delayedPaymentKey csv).bytes =
      serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv) := by
    rw [← toLocalProg_serialize revocationKey delayedPaymentKey csv,
      toLocal_serialize_eq revocationKey delayedPaymentKey csv (by omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩
  · rw [hbytes]
    exact toLocal_serialize_eq revocationKey delayedPaymentKey csv (by omega) (by omega)
  · simp [vendorLawsCSV, vendorLaws, hbytes]
  · exact exec_toLocal_revocation
      (vendorLawsCSV chk
        (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)) n)
      msg revocationKey delayedPaymentKey csv sig hsig'


/-! ## 4. Negative result: a wrong-key signature cannot use the revocation branch

The vendored `OP_CHECKSIG` on the true branch verifies against the
**revocation** key only.  If the checker rejects that pair, the branch
pushes the canonical `false` (the empty stack element); the P2WSH
witness verifier then requires a truthy cleanstack element and returns
`.fail .evalFalse`.  This is the mechanized "wrong key" outcome: a
signature that is valid under some other key — in the Lightning setting
the `local_delayedpubkey` — does not help, because the delayed key is
never pushed on this branch and the checker call above is the only
signature check the execution performs. -/

/-- The revocation branch pushes `false` when the vendored checker rejects
the revocation-key signature. -/
theorem evalFrom_toLocalWireOps_revocation_bad_sig (chk : ScriptChecker)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks) (sig : ByteArray)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsig : chk.base.checkECDSASignature sig revocationKey.bytes
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      .witnessV0 (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = false) :
    evalFrom
      { flags := ({ csv := true } : ScriptFlags), pol := ({} : PolicyFlags), chk := chk,
        sv := .witnessV0,
        bytes := serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv),
        ed := (default : Bitcoin.Crypto.Seam.ScriptExecutionData) }
      10 (toLocalWireOps revocationKey delayedPaymentKey csv)
      { stack := [revocationSelector, sig], alt := [], vf := [], opCount := 0,
        codeSep := 0, vwLeft := none }
    = Except.ok
        { stack := [ByteArray.empty], alt := [], vf := [], opCount := 6,
          codeSep := 0, vwLeft := none } := by
  simp [toLocalWireOps, evalFrom, stepChecked, stepBody, stepBody.dispatchOp,
    evalChecksigDispatch, evalChecksigPreTapscript, checkSigEncoding, checkPubKeyEncoding,
    topAt, pushBoolV, vchFalse, disabledWire,
    Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE, MAX_STACK_SIZE, MAX_OPS_PER_SCRIPT,
    toLocalDelayBytes_size, hsig, hr, hd]

/-- The wrong-key revocation branch at the `EvalScript` entry point:
the final stack is the canonical `false`. -/
theorem evalScriptBytes_toLocal_revocation_bad_sig (chk : ScriptChecker)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks) (sig : ByteArray)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsig : chk.base.checkECDSASignature sig revocationKey.bytes
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      .witnessV0 (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = false) :
    evalScriptBytes 10 ({ csv := true } : ScriptFlags) ({} : PolicyFlags)
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      [revocationSelector, sig] chk .witnessV0
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData)
    = Except.ok [ByteArray.empty] := by
  unfold evalScriptBytes
  have hsz : (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)).size = 77 :=
    serializeOpcodes_toLocal_size revocationKey delayedPaymentKey csv hr hd
  rw [ite_eq_right (by simp [hsz, MAX_SCRIPT_SIZE])]
  rw [toLocal_parseWire revocationKey delayedPaymentKey csv hr hd]
  simp [finalStack,
    evalFrom_toLocalWireOps_revocation_bad_sig chk revocationKey delayedPaymentKey csv sig
      hr hd hsig]

/-- The wrong-key revocation witness fails the witness-script evaluation
with `.evalFalse` (push `false`, then the implicit cleanstack truthiness
test). -/
theorem executeWitnessScript_toLocal_revocation_bad_sig (chk : ScriptChecker)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (vwSer : Int)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hsig : chk.base.checkECDSASignature sig revocationKey.bytes
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      .witnessV0 (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = false) :
    executeWitnessScript 10 [sig, revocationSelector] vwSer
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      ({ csv := true } : ScriptFlags) ({} : PolicyFlags) chk .witnessV0
    = .fail .evalFalse := by
  have hsig' : ¬ Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE < sig.size := by
    unfold Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE; omega
  simp [executeWitnessScript, executeWitnessScript.runExec,
    evalScriptBytes_toLocal_revocation_bad_sig chk revocationKey delayedPaymentKey csv sig
      hr hd hsig,
    hsig', Bitcoin.Numeric.castToBool]
  decide

/-- The full P2WSH verifier rejects the wrong-key revocation witness with
`.fail .evalFalse`. -/
theorem verifyWitnessProgram_toLocal_revocation_bad_sig (chk : ScriptChecker)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (program : ByteArray)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hsig : chk.base.checkECDSASignature sig revocationKey.bytes
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      .witnessV0 (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = false)
    (hps : program.size = 32)
    (hprog : hashSha256
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)) = program) :
    verifyWitnessProgram 10
      [sig, revocationSelector,
        serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)]
      0 program ({ csv := true } : ScriptFlags) ({} : PolicyFlags) chk false
    = .fail .evalFalse := by
  simp [verifyWitnessProgram, hps, hprog, byteArray_bne_self,
    executeWitnessScript_toLocal_revocation_bad_sig chk revocationKey delayedPaymentKey
      csv sig
      (witnessSerSize [sig, revocationSelector,
        serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)])
      hr hd hsigsz hsig]

/-- Model-side counterpart: with `vendorLaws`, a rejected revocation-key
signature does not yield an accepting model spend. -/
theorem not_accepts_toLocal_revocation_bad_sig_vendor (chk : ScriptChecker)
    (msg : ByteArray) (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray)
    (hsig : chk.base.checkECDSASignature sig revocationKey.bytes
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      .witnessV0 (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = false) :
    ¬ Accepts (vendorLaws chk
        (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)))
      msg (toLocalProg revocationKey delayedPaymentKey csv) [oneByte, sig] := by
  have hsig' : (vendorLaws chk
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))).sigCheck
      revocationKey.bytes msg sig = false := by
    simpa [vendorLaws] using hsig
  exact not_accepts_toLocal_revocation_bad_sig
    (vendorLaws chk
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)))
    msg revocationKey delayedPaymentKey csv sig hsig'

/-- **Wrong-key rejection, vendor and model together.**  The vendored P2WSH
verifier returns `.fail .evalFalse` and the model `Accepts` predicate is
false, under the same rejected revocation-key check. -/
theorem toLocal_revocation_wrong_key_rejected (chk : ScriptChecker)
    (msg : ByteArray) (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hsig : chk.base.checkECDSASignature sig revocationKey.bytes
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      .witnessV0 (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = false) :
    verifyWitnessProgram 10
        [sig, revocationSelector,
          serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)]
        0
        (hashSha256 (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)))
        ({ csv := true } : ScriptFlags) ({} : PolicyFlags) chk false
      = .fail .evalFalse ∧
      ¬ Accepts (vendorLaws chk
          (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)))
        msg (toLocalProg revocationKey delayedPaymentKey csv) [oneByte, sig] := by
  refine ⟨?_, ?_⟩
  · exact verifyWitnessProgram_toLocal_revocation_bad_sig chk revocationKey
      delayedPaymentKey csv sig _ hr hd hsigsz hsig (hashSha256_size _) rfl
  · exact not_accepts_toLocal_revocation_bad_sig_vendor chk msg revocationKey
      delayedPaymentKey csv sig hsig

/-- Checker-level key separation for one script code: every signature the
vendored checker accepts under the **delayed-payment** key is rejected
under the **revocation** key.

This is the explicit cryptographic hypothesis behind the "wrong key"
instantiation.  It is *not* proved here: it is what ECDSA key separation
gives except with negligible probability, and the tree has no
computational-cryptography model (`CR-01`).  Stated as a `Prop`, it is an
honest conditional input, not a hidden assumption. -/
def RevocationKeySeparated (chk : ScriptChecker) (scriptCode : ByteArray)
    (revocationKey delayedPaymentKey : PubKey) : Prop :=
  ∀ sig : ByteArray,
    chk.base.checkECDSASignature sig delayedPaymentKey.bytes scriptCode
      .witnessV0 (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true →
    chk.base.checkECDSASignature sig revocationKey.bytes scriptCode
      .witnessV0 (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = false

/-- **A delayed-key signature cannot spend via the revocation branch.**
Under `RevocationKeySeparated`, a signature the checker accepts for the
`local_delayedpubkey` is rejected on the `OP_IF` branch, so the vendored
P2WSH verifier returns `.fail .evalFalse` and the model does not accept.
This is the Lightning-meaningful wrong-key result: the selector is
`0x01`, but the signature belongs to the other branch's key. -/
theorem toLocal_revocation_delayed_key_sig_rejected (chk : ScriptChecker)
    (msg : ByteArray) (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hsep : RevocationKeySeparated chk
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      revocationKey delayedPaymentKey)
    (hdel : chk.base.checkECDSASignature sig delayedPaymentKey.bytes
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      .witnessV0 (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true) :
    verifyWitnessProgram 10
        [sig, revocationSelector,
          serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)]
        0
        (hashSha256 (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)))
        ({ csv := true } : ScriptFlags) ({} : PolicyFlags) chk false
      = .fail .evalFalse ∧
      ¬ Accepts (vendorLaws chk
          (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)))
        msg (toLocalProg revocationKey delayedPaymentKey csv) [oneByte, sig] := by
  have hrev := hsep sig hdel
  exact toLocal_revocation_wrong_key_rejected chk msg revocationKey delayedPaymentKey
    csv sig hr hd hsigsz hrev

/-! ## 5. Wrong branch: the empty selector cannot use the revocation key

With the **empty** selector the vendored machine executes the `OP_ELSE`
block, so the revocation key is never pushed and never checked.  The
delay is decoded and `OP_CSV` consults the vendored sequence check; when
`checkSequenceDef chk.env n` is false, execution errors with
`unsatisfiedLocktime` before any signature check.  A valid revocation-key
signature in the witness is therefore irrelevant on this branch. -/

/-- The empty selector takes the delayed branch, and a failing sequence
check makes vendor execution error with `unsatisfiedLocktime`. -/
theorem evalFrom_toLocalWireOps_delayed_csv_false (chk : ScriptChecker)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (n : Bitcoin.Numeric.ScriptNum)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hdec : decodeNum ({} : PolicyFlags) (delayBytes csv) 5 = .ok n)
    (hnn : 0 ≤ n)
    (hdis : Int.toNat n &&& SEQUENCE_LOCKTIME_DISABLE_FLAG = 0)
    (hseq : checkSequenceDef chk.env n = false) :
    evalFrom
      { flags := ({ csv := true } : ScriptFlags), pol := ({} : PolicyFlags), chk := chk,
        sv := .witnessV0,
        bytes := serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv),
        ed := (default : Bitcoin.Crypto.Seam.ScriptExecutionData) }
      10 (toLocalWireOps revocationKey delayedPaymentKey csv)
      { stack := [ByteArray.empty, sig], alt := [], vf := [], opCount := 0,
        codeSep := 0, vwLeft := none }
    = Except.error .unsatisfiedLocktime := by
  simp [toLocalWireOps, evalFrom, stepChecked, stepBody, stepBody.dispatchOp,
    evalChecksigDispatch, evalChecksigPreTapscript, checkSigEncoding, checkPubKeyEncoding,
    Bitcoin.Numeric.castToBool, Bitcoin.Numeric.castToBoolList,
    Bitcoin.Numeric.bytesOf, delayBytes, topAt, pushBoolV, vchTrue, serU8, disabledWire,
    Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE, MAX_STACK_SIZE, MAX_OPS_PER_SCRIPT,
    toLocalDelayBytes_size, hr, hd]
  rw [show decodeNum ({} : PolicyFlags) (toLocalDelayBytes csv) 5 = .ok n by
    simpa [delayBytes] using hdec]
  have hnlt : ¬ n < 0 := Int.not_lt.mpr hnn
  simp [hnlt, hdis, hseq]

/-- The same failure at the `EvalScript` entry point. -/
theorem evalScriptBytes_toLocal_delayed_csv_false (chk : ScriptChecker)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (n : Bitcoin.Numeric.ScriptNum)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hdec : decodeNum ({} : PolicyFlags) (delayBytes csv) 5 = .ok n)
    (hnn : 0 ≤ n)
    (hdis : Int.toNat n &&& SEQUENCE_LOCKTIME_DISABLE_FLAG = 0)
    (hseq : checkSequenceDef chk.env n = false) :
    evalScriptBytes 10 ({ csv := true } : ScriptFlags) ({} : PolicyFlags)
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      [ByteArray.empty, sig] chk .witnessV0
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData)
    = Except.error .unsatisfiedLocktime := by
  unfold evalScriptBytes
  have hsz : (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)).size = 77 :=
    serializeOpcodes_toLocal_size revocationKey delayedPaymentKey csv hr hd
  rw [ite_eq_right (by simp [hsz, MAX_SCRIPT_SIZE])]
  rw [toLocal_parseWire revocationKey delayedPaymentKey csv hr hd]
  simp [finalStack,
    evalFrom_toLocalWireOps_delayed_csv_false chk revocationKey delayedPaymentKey csv
      sig n hr hd hdec hnn hdis hseq]

/-- The same failure at the witness-script entry point: `.fail
.unsatisfiedLocktime`. -/
theorem executeWitnessScript_toLocal_delayed_csv_false (chk : ScriptChecker)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (n : Bitcoin.Numeric.ScriptNum) (vwSer : Int)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hdec : decodeNum ({} : PolicyFlags) (delayBytes csv) 5 = .ok n)
    (hnn : 0 ≤ n)
    (hdis : Int.toNat n &&& SEQUENCE_LOCKTIME_DISABLE_FLAG = 0)
    (hseq : checkSequenceDef chk.env n = false) :
    executeWitnessScript 10 [sig, ByteArray.empty] vwSer
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      ({ csv := true } : ScriptFlags) ({} : PolicyFlags) chk .witnessV0
    = .fail .unsatisfiedLocktime := by
  have hsig' : ¬ Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE < sig.size := by
    unfold Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE; omega
  simp [executeWitnessScript, executeWitnessScript.runExec,
    evalScriptBytes_toLocal_delayed_csv_false chk revocationKey delayedPaymentKey csv
      sig n hr hd hdec hnn hdis hseq,
    hsig']

/-- The full P2WSH verifier rejects the empty-selector witness with
`.fail .unsatisfiedLocktime` when the sequence check fails. -/
theorem verifyWitnessProgram_toLocal_delayed_csv_false (chk : ScriptChecker)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (n : Bitcoin.Numeric.ScriptNum) (program : ByteArray)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hdec : decodeNum ({} : PolicyFlags) (delayBytes csv) 5 = .ok n)
    (hnn : 0 ≤ n)
    (hdis : Int.toNat n &&& SEQUENCE_LOCKTIME_DISABLE_FLAG = 0)
    (hseq : checkSequenceDef chk.env n = false)
    (hps : program.size = 32)
    (hprog : hashSha256
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)) = program) :
    verifyWitnessProgram 10
      [sig, ByteArray.empty,
        serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)]
      0 program ({ csv := true } : ScriptFlags) ({} : PolicyFlags) chk false
    = .fail .unsatisfiedLocktime := by
  simp [verifyWitnessProgram, hps, hprog, byteArray_bne_self,
    executeWitnessScript_toLocal_delayed_csv_false chk revocationKey delayedPaymentKey
      csv sig n
      (witnessSerSize [sig, ByteArray.empty,
        serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)])
      hr hd hsigsz hdec hnn hdis hseq]

/-- Model-side counterpart: with `vendorLawsCSV` tied to the failing
sequence check, the delayed branch does not accept.  (`OP_CSV` errors in
the model, exactly as the vendored step does.) -/
theorem not_accepts_toLocal_delayed_csv_false (chk : ScriptChecker)
    (msg : ByteArray) (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (n : Bitcoin.Numeric.ScriptNum)
    (hseq : checkSequenceDef chk.env n = false) :
    ¬ Accepts (vendorLawsCSV chk
        (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)) n)
      msg (toLocalProg revocationKey delayedPaymentKey csv) [zeroByte, sig] := by
  have hcsv : (vendorLawsCSV chk
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)) n).csvOk
      (delayBytes csv) = false := by
    simpa [vendorLawsCSV, vendorLaws] using hseq
  have hnone := exec_toLocal_delayed_csv_fails
    (vendorLawsCSV chk
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)) n)
    msg revocationKey delayedPaymentKey csv sig hcsv
  intro h
  unfold Accepts at h
  rw [hnone] at h
  simp at h

/-- **Wrong-branch rejection, vendor and model together.** -/
theorem toLocal_delayed_csv_failure_agree (chk : ScriptChecker)
    (msg : ByteArray) (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (n : Bitcoin.Numeric.ScriptNum)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hdec : decodeNum ({} : PolicyFlags) (delayBytes csv) 5 = .ok n)
    (hnn : 0 ≤ n)
    (hdis : Int.toNat n &&& SEQUENCE_LOCKTIME_DISABLE_FLAG = 0)
    (hseq : checkSequenceDef chk.env n = false) :
    verifyWitnessProgram 10
        [sig, ByteArray.empty,
          serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)]
        0
        (hashSha256 (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)))
        ({ csv := true } : ScriptFlags) ({} : PolicyFlags) chk false
      = .fail .unsatisfiedLocktime ∧
      ¬ Accepts (vendorLawsCSV chk
          (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)) n)
        msg (toLocalProg revocationKey delayedPaymentKey csv) [zeroByte, sig] := by
  refine ⟨?_, ?_⟩
  · exact verifyWitnessProgram_toLocal_delayed_csv_false chk revocationKey
      delayedPaymentKey csv sig n _ hr hd hsigsz hdec hnn hdis hseq
      (hashSha256_size _) rfl
  · exact not_accepts_toLocal_delayed_csv_false chk msg revocationKey delayedPaymentKey
      csv sig n hseq

/-! ## 6. Branch selection from one script and one signature -/

/-- **Branch selection.**  For one `to_local` witness script and one
signature, the selector alone decides the branch:

* `revocationSelector` (`0x01`) yields vendor `.ok` on the revocation
  branch, independently of the sequence environment; and
* the empty selector yields `.fail .unsatisfiedLocktime` under a failing
  sequence check, even though the revocation-key signature is valid.

The two witnesses differ only in the selector item. -/
theorem toLocal_vendor_branch_selection (chk : ScriptChecker)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (n : Bitcoin.Numeric.ScriptNum) (program : ByteArray)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hdec : decodeNum ({} : PolicyFlags) (delayBytes csv) 5 = .ok n)
    (hnn : 0 ≤ n)
    (hdis : Int.toNat n &&& SEQUENCE_LOCKTIME_DISABLE_FLAG = 0)
    (hseq : checkSequenceDef chk.env n = false)
    (hsig : chk.base.checkECDSASignature sig revocationKey.bytes
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      .witnessV0 (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true)
    (hps : program.size = 32)
    (hprog : hashSha256
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)) = program) :
    verifyWitnessProgram 10
        [sig, revocationSelector,
          serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)]
        0 program ({ csv := true } : ScriptFlags) ({} : PolicyFlags) chk false = .ok ∧
      verifyWitnessProgram 10
        [sig, ByteArray.empty,
          serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)]
        0 program ({ csv := true } : ScriptFlags) ({} : PolicyFlags) chk false
        = .fail .unsatisfiedLocktime := by
  refine ⟨?_, ?_⟩
  · exact verifyWitnessProgram_toLocal_revocation chk revocationKey delayedPaymentKey
      csv sig program hr hd hsigsz hsig hps hprog
  · exact verifyWitnessProgram_toLocal_delayed_csv_false chk revocationKey
      delayedPaymentKey csv sig n program hr hd hsigsz hdec hnn hdis hseq hps hprog

end LnLean.Proofs.Bitcoin.InterpreterRevocationTargets
