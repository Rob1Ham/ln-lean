import Bitcoin.TxValidation.Full
import LnLean.Proofs.Bitcoin.SpendTargets
import LnLean.Proofs.Bitcoin.SequenceContextTargets

/-!
# H05 — The `minimalData` policy edge for the `to_local` delayed branch

Wave 8, lane `H05`; roadmap issues `L1-02`, `L1-07`, `MODEL-01`.

Wave 7's `SequenceContextTargets` characterized the vendored delayed-branch
verdict for the **default** policy word (`minimalData = false`) and recorded
that the scaffold's `to_local` script pushes the fixed-width two-byte
`to_self_delay` payload.  This module closes the resulting policy boundary:

* **Truthiness divergence (consensus-level, not fixable by a flag).**  The
  Wave-4 model's `truthy d := d.size ≠ 0` treats the all-zero selector
  `#[0x00]` as true, while the vendor's `Bitcoin.Numeric.castToBool` — Core's
  `CastToBool` — treats it as false.  The existing counterexample
  `SpendTargets.truthy_nonminimal_true` is kept unchanged and restated at the
  exact byte vector used below.  We prove the general soundness direction
  (`castToBool = true → truthy = true`), the two concrete divergences
  (`#[0x00]`, the negative zero `#[0x80]`), and — the substantive point — a
  **model/vendor branch-selection counterexample**: with the same witness and
  a valid revocation-key signature the model executes the `OP_IF`
  (revocation) branch, while the vendor casts `#[0x00]` to false and executes
  the `OP_ELSE` (delayed) branch, rejecting with
  `.fail .unsatisfiedLocktime` when the sequence check fails.  Witness
  elements are not opcode pushes, so `MINIMALDATA` cannot repair this
  divergence; only the model's truthiness can.

* **`MINIMALDATA` policy edge.**  The scaffold's fixed-width two-byte
  little-endian delay is not a minimal `CScriptNum` encoding for
  `csv < 128`: the numeric decoder under `minimalData = true` rejects it with
  `.scriptNum`, while the default policy decodes it to `csv`.  We prove the
  exact gate
  `decodeNum {minimalData := true} (delayBytes csv) 5 = .ok csv ↔ 128 ≤ csv`
  for `csv < 32768`, that the delay *push itself* is minimal
  (`checkMinimalPush` accepts it — the failure is numeric, not the BIP 146
  push rule), and the full vendored verdicts:
  - default policy (`{}`): `.ok` under the exact BIP 68/112 context and the
    delayed-key signature (the existing exact iff is re-exported);
  - `MINIMALDATA` with `csv ≥ 128`: `.ok` under the same context/signature
    hypotheses (so the flag is inert on that range);
  - `MINIMALDATA` with `csv < 128`: `.fail .scriptNum` before any sequence
    or signature check (the mechanized counterexample: the scaffold script is
    non-standard for delays below 128 under `MINIMALDATA`).

* **Policy tier.**  `TxValidation.Full.hasStandardNotMandatory` is `true` for
  `{minimalData := true}`, so this failure maps to `TX_NOT_STANDARD`, not to
  a consensus rejection.

The exact script-level context is named: `toLocalCtx` is the vendored `Ctx`
(`ScriptFlags` with `csv = true`, the given `PolicyFlags`, the witness-v0
script bytes and default execution data) and `toLocalInit` is the machine
state (head of stack = top).  `toLocalWireOps` / `toLocalOps` are the parsed
and canonical forms of the BOLT 3 witness script.  All proofs are symbolic
executions of the frozen vendor `stepBody`/`evalFrom`/`verifyWitnessProgram`;
no vendor source is changed.

Anchors: BOLT 3 §`to_local` Output (`refs/bolts/03-transactions.md:113-135`);
BIP 141 (P2WSH), BIP 112 (`OP_CSV`), BIP 146 (`MINIMALDATA`);
`vendor/btc-lean-core/Bitcoin/Interpreter/Defs.lean` (`castToBool`,
`checkMinimalPush`, `decodeNum`), `Bitcoin/Numeric/ScriptNum.lean`.
-/

namespace LnLean.Proofs.WaveH.H05

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
open LnLean.Proofs.Bitcoin.SequenceContextTargets

/-! ## 1. The two policy words and the exact script context -/

/-- The policy word with only `SCRIPT_VERIFY_MINIMALDATA` set (BIP 146's
policy bit, never a mainnet consensus bit).  All other policy bits are off,
so the only deviation from the block/default word is `minimalData`. -/
def minimalDataPolicy : PolicyFlags := { minimalData := true }

/-- The block/default word has `MINIMALDATA` off. -/
@[simp] theorem default_minimalData :
    (default : PolicyFlags).minimalData = false := rfl

/-- The `MINIMALDATA` word has the bit on. -/
@[simp] theorem minimalDataPolicy_minimalData :
    minimalDataPolicy.minimalData = true := rfl

/-- The two words are genuinely different. -/
theorem minimalDataPolicy_ne_default : minimalDataPolicy ≠ default := by
  decide

/-- The policy bits the delayed `to_local` path can consult, all off.  The
only policy bit that may differ between the block word and the `MINIMALDATA`
word is `minimalData`, and for this script it is inert whenever the CScriptNum
decode succeeds and the delay push is minimal. -/
def NeutralPolicy (pol : PolicyFlags) : Prop :=
  pol.minimalIf = false ∧ pol.nullFail = false ∧ pol.strictEnc = false ∧
    pol.lowS = false ∧ pol.witnessPubkeyType = false ∧
      pol.constScriptCode = false

/-- The block/default word is neutral. -/
theorem neutral_default : NeutralPolicy ({} : PolicyFlags) := by
  simp [NeutralPolicy]

/-- The `MINIMALDATA` word is neutral: all other policy bits stay off. -/
theorem neutral_minimalDataPolicy : NeutralPolicy minimalDataPolicy := by
  simp [NeutralPolicy, minimalDataPolicy]

/-- The two policy words whose delayed-branch verdicts this module
characterizes. -/
def IsDelayPolicy (pol : PolicyFlags) : Prop :=
  pol = ({} : PolicyFlags) ∨ pol = minimalDataPolicy

theorem isDelayPolicy_default : IsDelayPolicy ({} : PolicyFlags) := Or.inl rfl

theorem isDelayPolicy_minimalData : IsDelayPolicy minimalDataPolicy := Or.inr rfl

/-- The exact vendored execution context for the BOLT 3 `to_local` witness
script: witness-v0, `OP_CSV` consensus flag on, the supplied policy word, the
concrete checker, the canonical script bytes and default execution data. -/
def toLocalCtx (chk : ScriptChecker) (pol : PolicyFlags)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks) : Ctx :=
  { flags := ({ csv := true } : ScriptFlags)
    pol := pol
    chk := chk
    sv := .witnessV0
    bytes := serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)
    ed := (default : Bitcoin.Crypto.Seam.ScriptExecutionData) }

/-- The machine state for a witness whose last two items are the selector
`sel` and the signature `sig` (machine head = top of stack). -/
def toLocalInit (sel sig : ByteArray) : State :=
  { stack := [sel, sig], alt := [], vf := [], opCount := 0, codeSep := 0,
    vwLeft := none }

/-! ## 2. Truthiness: the kept counterexample and the general direction -/

/-- The non-minimal false encoding: a single zero byte.  Core's
`CastToBool` calls it false; the Wave-4 model's `truthy` calls it true. -/
def nonMinimalFalse : ByteArray := ByteArray.mk #[0x00]

/-- The negative-zero encoding: Core's `CastToBool` also calls it false. -/
def nonMinimalNegativeZero : ByteArray := ByteArray.mk #[0x80]

/-- **The existing counterexample, kept unchanged.**  This is exactly
`SpendTargets.truthy_nonminimal_true`, restated at `nonMinimalFalse` so the
counterexample is not weakened or silently replaced. -/
theorem truthy_nonminimal_true_kept : truthy nonMinimalFalse = true :=
  LnLean.Proofs.Bitcoin.SpendTargets.truthy_nonminimal_true

/-- The vendor/Core cast of the same bytes is false. -/
theorem castToBool_nonminimal_false :
    Bitcoin.Numeric.castToBool nonMinimalFalse = false := by
  decide

/-- The same fact at the unfolded constructor spelling, for `simp` after
`nonMinimalFalse` has been expanded. -/
@[simp] theorem castToBool_mk_zeroBytes :
    Bitcoin.Numeric.castToBool (ByteArray.mk #[0x00]) = false := by
  decide

/-- The divergence, as an inequality of the two truthiness predicates. -/
theorem truthy_ne_castToBool_nonminimal :
    truthy nonMinimalFalse ≠ Bitcoin.Numeric.castToBool nonMinimalFalse := by
  rw [truthy_nonminimal_true_kept, castToBool_nonminimal_false]
  decide

/-- The non-minimal false encoding is not the empty stack element (the
canonical false selector). -/
@[simp] theorem nonMinimalFalse_ne_empty :
    nonMinimalFalse ≠ (ByteArray.empty : ByteArray) := by
  decide

/-- The second false encoding: negative zero is true for the model. -/
theorem truthy_negative_zero_true :
    truthy nonMinimalNegativeZero = true := rfl

/-- ... and false for Core. -/
theorem castToBool_negative_zero_false :
    Bitcoin.Numeric.castToBool nonMinimalNegativeZero = false := by
  decide

/-- **Soundness direction.**  Core's cast is never more permissive than the
model: whenever the vendor calls an element true, the model does too.  Thus
the model's truthiness is an over-approximation, and every divergence is a
Core-false / model-true pair. -/
theorem castToBool_true_imp_truthy (b : ByteArray) :
    Bitcoin.Numeric.castToBool b = true → truthy b = true := by
  intro h
  unfold Bitcoin.Numeric.castToBool at h
  have hne : (Bitcoin.Numeric.bytesOf b).reverse ≠ [] := by
    intro hnil
    rw [hnil] at h
    simp [Bitcoin.Numeric.castToBoolList] at h
  have hsize : b.size ≠ 0 := by
    intro hb
    apply hne
    simp [Bitcoin.Numeric.bytesOf, hb]
  simp [truthy, hsize]

/-- Contrapositive form: a model-false element is Core-false. -/
theorem truthy_false_imp_castToBool_false (b : ByteArray) :
    truthy b = false → Bitcoin.Numeric.castToBool b = false := by
  intro h
  cases hc : Bitcoin.Numeric.castToBool b with
  | false => rfl
  | true =>
      exact absurd (castToBool_true_imp_truthy b hc) (by rw [h]; decide)

/-! ## 3. Model acceptance of the non-minimal revocation selector -/

/-- With the non-minimal selector `#[0x00]`, the model's `truthy` selects the
`OP_IF` (revocation) branch, exactly as for the canonical `0x01`.  This is
the model side of the divergence. -/
theorem exec_toLocal_nonminimal_selector_model
    (L : InterpreterLaws) (msg : ByteArray)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray)
    (h : L.sigCheck revocationKey.bytes msg sig = true) :
    execStmts L msg (toLocalProg revocationKey delayedPaymentKey csv)
      [nonMinimalFalse, sig] = some [oneByte] := by
  simp [toLocalProg, execStmts, execStmt, step, truthy_nonminimal_true_kept, h]

/-- Consequently the model's `Accepts` predicate accepts the non-minimal
revocation witness. -/
theorem accepts_toLocal_nonminimal_selector_model
    (L : InterpreterLaws) (msg : ByteArray)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray)
    (h : L.sigCheck revocationKey.bytes msg sig = true) :
    Accepts L msg (toLocalProg revocationKey delayedPaymentKey csv)
      [nonMinimalFalse, sig] := by
  unfold Accepts
  exact exec_toLocal_nonminimal_selector_model L msg revocationKey
    delayedPaymentKey csv sig h

/-! ## 4. The `MINIMALDATA` numeric gate on the fixed-width delay -/

/-- The two-byte delay push is itself a minimal *push*: `checkMinimalPush`
accepts opcode `2` with two data bytes.  The `MINIMALDATA` failure below is
therefore the `CScriptNum` minimality rule inside `OP_CSV`, not the BIP 146
push rule. -/
theorem checkMinimalPush_delayBytes (csv : Blocks) :
    checkMinimalPush (delayBytes csv) 2 = true := by
  simp [checkMinimalPush, delayBytes, toLocalDelayBytes_size]

/-- The same fact at the `toLocalDelayBytes` spelling used by the vendored
symbolic execution. -/
theorem checkMinimalPush_toLocalDelayBytes (csv : Blocks) :
    checkMinimalPush (toLocalDelayBytes csv) 2 = true := by
  simpa [delayBytes] using checkMinimalPush_delayBytes csv

/-- A concrete genuinely non-minimal *push*: one data byte `0x01` pushed with
opcode `1` instead of `OP_1`.  Included to separate the push rule from the
numeric rule exercised by `to_local`. -/
theorem checkMinimalPush_nonminimal_push :
    checkMinimalPush (ByteArray.mk #[0x01]) 1 = false := by
  decide

/-- Under `MINIMALDATA`, the fixed-width delay decodes to `.scriptNum` for
every `csv < 128`: the high byte is zero and the low byte is below `0x80`, so
the two-byte encoding is non-minimal for `CScriptNum`. -/
theorem decodeNum_delayBytes_minimalData_error (csv : Nat) (h : csv < 128) :
    decodeNum minimalDataPolicy (delayBytes csv) 5 = .error .scriptNum := by
  unfold decodeNum decodeScriptNum minimalDataPolicy
  rw [bytesOf_delayBytes]
  have hshift : csv >>> 8 = 0 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt (by omega)
  have hmod : csv % 256 = csv := Nat.mod_eq_of_lt (by omega)
  have hrev : ([(csv % 256), (csv >>> 8) % 256] : List Nat).reverse = [0, csv] := by
    rw [hshift, hmod]
    rfl
  rw [hrev]
  simp [decodeBE, minimalOkBE, h]

/-- Under `MINIMALDATA`, the fixed-width delay decodes to `csv` for every
`128 ≤ csv < 32768`: either the high byte is nonzero (minimal) or the low
byte carries the `0x80` sign bit (minimal). -/
theorem decodeNum_delayBytes_minimalData_ok (csv : Nat)
    (hlo : 128 ≤ csv) (hhi : csv < 32768) :
    decodeNum minimalDataPolicy (delayBytes csv) 5 = .ok (csv : Int) := by
  unfold decodeNum decodeScriptNum minimalDataPolicy
  rw [bytesOf_delayBytes]
  have hrev : ([(csv % 256), (csv >>> 8) % 256] : List Nat).reverse =
      [(csv >>> 8) % 256, csv % 256] := rfl
  rw [hrev]
  have hhighlt : (csv >>> 8) % 256 < 128 := by
    have hshift : csv >>> 8 = csv / 256 := Nat.shiftRight_eq_div_pow csv 8
    have hdivlt : csv / 256 < 256 :=
      (Nat.div_lt_iff_lt_mul (by decide : 0 < 256)).mpr (by omega)
    rw [hshift, Nat.mod_eq_of_lt hdivlt]
    exact (Nat.div_lt_iff_lt_mul (by decide : 0 < 256)).mpr (by omega)
  by_cases h0 : (csv >>> 8) % 256 = 0
  · have hshift : csv >>> 8 = csv / 256 := Nat.shiftRight_eq_div_pow csv 8
    have hdivlt : csv / 256 < 256 :=
      (Nat.div_lt_iff_lt_mul (by decide : 0 < 256)).mpr (by omega)
    have hzero : csv / 256 = 0 := by
      have h := h0
      rw [hshift, Nat.mod_eq_of_lt hdivlt] at h
      exact h
    have hlt : csv < 256 := by
      have : csv / 256 < 1 := by omega
      exact (Nat.div_lt_iff_lt_mul (by decide : 0 < 256)).mp this
    have hlow : 128 ≤ csv % 256 := by
      rw [Nat.mod_eq_of_lt hlt]
      exact hlo
    have hmin : minimalOkBE [0, csv % 256] = true := by
      rw [minimalOkBE]
      rw [if_pos rfl]
      simp [hlow]
    have hval : setVchBE [0, csv % 256] = (csv : Int) := by
      have hbytes : ([(0 : Nat), csv % 256] : List Nat) =
          [(csv >>> 8) % 256, csv % 256] := by rw [h0]
      rw [hbytes]
      exact setVchBE_delay csv hhi
    rw [h0]
    simp [decodeBE, hmin, hval]
  · have hne : (csv >>> 8) % 256 % 128 ≠ 0 := by
      rw [Nat.mod_eq_of_lt hhighlt]
      omega
    have hmin : minimalOkBE [(csv >>> 8) % 256, csv % 256] = true := by
      rw [minimalOkBE]
      rw [if_neg hne]
    simp [decodeBE, hmin, setVchBE_delay csv hhi]

/-- **The exact policy gate.**  For the faithful BOLT 3 delay range, the
`MINIMALDATA` decoder accepts the fixed-width encoding exactly when the delay
is at least 128.  This is the sharp boundary between the scaffold encoding
and Core's minimal `CScriptNum`. -/
theorem decodeNum_delayBytes_minimalData_iff (csv : Nat) (hhi : csv < 32768) :
    decodeNum minimalDataPolicy (delayBytes csv) 5 = .ok (csv : Int) ↔
      128 ≤ csv := by
  constructor
  · intro hok
    by_cases hlo : 128 ≤ csv
    · exact hlo
    · have herr := decodeNum_delayBytes_minimalData_error csv (by omega)
      rw [herr] at hok
      simp at hok
  · intro hlo
    exact decodeNum_delayBytes_minimalData_ok csv hlo hhi

/-- The default-policy decode (re-exported from wave 7). -/
theorem decodeNum_delayBytes_default (csv : Nat) (hcsv : csv < 32768) :
    decodeNum ({} : PolicyFlags) (delayBytes csv) 5 = .ok (csv : Int) :=
  LnLean.Proofs.Bitcoin.SequenceContextTargets.decodeNum_delayBytes csv hcsv

/-! ## 5. Vendored symbolic execution for the delayed branch -/

/-- **Positive delayed branch, default or `MINIMALDATA` policy.**  With the
empty selector, the vendored `OP_IF` takes the `OP_ELSE` branch, decodes the
delay, checks the sequence law, drops the delay and verifies the delayed key.
The only non-computational inputs are the decode, non-negativity,
disable-bit, sequence and signature facts. -/
theorem evalFrom_toLocal_delayed_ok
    (chk : ScriptChecker) (pol : PolicyFlags) (hpol : IsDelayPolicy pol)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (n : ScriptNum)
    (hr : revocationKey.bytes.size = 33)
    (hd : delayedPaymentKey.bytes.size = 33)
    (hdec : decodeNum pol (delayBytes csv) 5 = .ok n)
    (hnn : 0 ≤ n)
    (hdis : Int.toNat n &&& SEQUENCE_LOCKTIME_DISABLE_FLAG = 0)
    (hseq : checkSequenceDef chk.env n = true)
    (hsig : chk.base.checkECDSASignature sig delayedPaymentKey.bytes
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      .witnessV0 (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true) :
    evalFrom
      { flags := ({ csv := true } : ScriptFlags), pol := pol, chk := chk,
        sv := .witnessV0,
        bytes := serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv),
        ed := (default : Bitcoin.Crypto.Seam.ScriptExecutionData) }
      10 (toLocalWireOps revocationKey delayedPaymentKey csv)
      { stack := [ByteArray.empty, sig], alt := [], vf := [], opCount := 0,
        codeSep := 0, vwLeft := none }
    = Except.ok
        { stack := [ByteArray.mk #[0x01]], alt := [], vf := [], opCount := 6,
          codeSep := 0, vwLeft := none } := by
  rcases hpol with rfl | rfl
  · simp [toLocalWireOps, evalFrom, stepChecked,
      stepBody, stepBody.dispatchOp, evalChecksigDispatch,
      evalChecksigPreTapscript, checkSigEncoding, checkPubKeyEncoding,
      Bitcoin.Numeric.castToBool, Bitcoin.Numeric.castToBoolList,
      Bitcoin.Numeric.bytesOf, delayBytes, topAt, pushBoolV, vchTrue, serU8,
      disabledWire, Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE, MAX_STACK_SIZE,
      MAX_OPS_PER_SCRIPT, toLocalDelayBytes_size, hdis, hseq, hsig, hr, hd]
    rw [show decodeNum ({} : PolicyFlags) (toLocalDelayBytes csv) 5 = .ok n by
      simpa [delayBytes] using hdec]
    have hnlt : ¬ n < 0 := Int.not_lt.mpr hnn
    simp [hnlt, hdis, hseq, hsig, Bitcoin.Numeric.castToBoolList, empty_push_eq]
    rfl
  · simp [toLocalWireOps, evalFrom, stepChecked,
      stepBody, stepBody.dispatchOp, evalChecksigDispatch,
      evalChecksigPreTapscript, checkSigEncoding, checkPubKeyEncoding,
      Bitcoin.Numeric.castToBool, Bitcoin.Numeric.castToBoolList,
      Bitcoin.Numeric.bytesOf, delayBytes, topAt, pushBoolV, vchTrue, serU8,
      disabledWire, Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE, MAX_STACK_SIZE,
      MAX_OPS_PER_SCRIPT, toLocalDelayBytes_size, hdis, hseq, hsig, hr, hd,
      minimalDataPolicy, checkMinimalPush, checkMinimalPush_toLocalDelayBytes]
    rw [show decodeNum ({ minimalData := true } : PolicyFlags)
        (toLocalDelayBytes csv) 5 = .ok n by
      simpa [delayBytes, minimalDataPolicy] using hdec]
    have hnlt : ¬ n < 0 := Int.not_lt.mpr hnn
    simp [hnlt, hdis, hseq, hsig, Bitcoin.Numeric.castToBoolList, empty_push_eq]
    rfl

/-- **Delayed branch with the non-minimal `#[0x00]` selector and a failing
sequence check.**  The vendor casts the selector to false, so it takes the
`OP_ELSE` branch and errors with `.unsatisfiedLocktime`; the model instead
took the revocation branch (section 3).  This is the vendor half of the
divergence. -/
theorem evalFrom_toLocal_delayed_nonminimal_csv_false
    (chk : ScriptChecker)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (n : ScriptNum)
    (hr : revocationKey.bytes.size = 33)
    (hd : delayedPaymentKey.bytes.size = 33)
    (hdec : decodeNum ({} : PolicyFlags) (delayBytes csv) 5 = .ok n)
    (hnn : 0 ≤ n)
    (hdis : Int.toNat n &&& SEQUENCE_LOCKTIME_DISABLE_FLAG = 0)
    (hseq : checkSequenceDef chk.env n = false) :
    evalFrom
      { flags := ({ csv := true } : ScriptFlags), pol := ({} : PolicyFlags),
        chk := chk, sv := .witnessV0,
        bytes := serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv),
        ed := (default : Bitcoin.Crypto.Seam.ScriptExecutionData) }
      10 (toLocalWireOps revocationKey delayedPaymentKey csv)
      { stack := [nonMinimalFalse, sig], alt := [], vf := [], opCount := 0,
        codeSep := 0, vwLeft := none }
    = Except.error .unsatisfiedLocktime := by
  have hsel : Bitcoin.Numeric.castToBool nonMinimalFalse = false :=
    castToBool_nonminimal_false
  simp [toLocalWireOps, evalFrom, stepChecked,
    stepBody, stepBody.dispatchOp, evalChecksigDispatch,
    evalChecksigPreTapscript, checkSigEncoding, checkPubKeyEncoding,
    delayBytes, topAt, pushBoolV, vchTrue, serU8,
    disabledWire, Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE, MAX_STACK_SIZE,
    MAX_OPS_PER_SCRIPT, toLocalDelayBytes_size, hsel, hr, hd,
    nonMinimalFalse]
  rw [show decodeNum ({} : PolicyFlags) (toLocalDelayBytes csv) 5 = .ok n by
    simpa [delayBytes] using hdec]
  have hnlt : ¬ n < 0 := Int.not_lt.mpr hnn
  simp [hnlt, hdis, hseq]

/-- **Delayed branch under `MINIMALDATA` with a short delay.**  For
`csv < 128` the numeric decode of the fixed-width delay fails with
`.scriptNum` before `OP_CSV` can consult the sequence environment and before
the signature check.  This is the policy-gated counterexample at the
`evalFrom` level. -/
theorem evalFrom_toLocal_delayed_minimalData_error
    (chk : ScriptChecker)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray)
    (hr : revocationKey.bytes.size = 33)
    (hd : delayedPaymentKey.bytes.size = 33)
    (hcsv : csv < 128) :
    evalFrom
      { flags := ({ csv := true } : ScriptFlags), pol := minimalDataPolicy,
        chk := chk, sv := .witnessV0,
        bytes := serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv),
        ed := (default : Bitcoin.Crypto.Seam.ScriptExecutionData) }
      10 (toLocalWireOps revocationKey delayedPaymentKey csv)
      { stack := [ByteArray.empty, sig], alt := [], vf := [], opCount := 0,
        codeSep := 0, vwLeft := none }
    = Except.error .scriptNum := by
  simp [toLocalWireOps, evalFrom, stepChecked,
    stepBody, stepBody.dispatchOp, evalChecksigDispatch,
    evalChecksigPreTapscript, checkSigEncoding, checkPubKeyEncoding,
    Bitcoin.Numeric.castToBool, Bitcoin.Numeric.castToBoolList,
    Bitcoin.Numeric.bytesOf, delayBytes, topAt, pushBoolV, vchTrue, serU8,
    disabledWire, Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE, MAX_STACK_SIZE,
    MAX_OPS_PER_SCRIPT, toLocalDelayBytes_size, hr, hd,
    minimalDataPolicy, checkMinimalPush, checkMinimalPush_toLocalDelayBytes]
  rw [show decodeNum ({ minimalData := true } : PolicyFlags)
      (toLocalDelayBytes csv) 5 = .error .scriptNum by
    simpa [delayBytes, minimalDataPolicy] using
      decodeNum_delayBytes_minimalData_error csv hcsv]

/-! ## 6. Lifting the verdicts through the vendored P2WSH entry points -/

/-- Positive delayed branch at `EvalScript`'s byte entry. -/
theorem evalScriptBytes_toLocal_delayed_ok
    (chk : ScriptChecker) (pol : PolicyFlags) (hpol : IsDelayPolicy pol)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (n : ScriptNum)
    (hr : revocationKey.bytes.size = 33)
    (hd : delayedPaymentKey.bytes.size = 33)
    (hdec : decodeNum pol (delayBytes csv) 5 = .ok n)
    (hnn : 0 ≤ n)
    (hdis : Int.toNat n &&& SEQUENCE_LOCKTIME_DISABLE_FLAG = 0)
    (hseq : checkSequenceDef chk.env n = true)
    (hsig : chk.base.checkECDSASignature sig delayedPaymentKey.bytes
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      .witnessV0 (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true) :
    evalScriptBytes 10 ({ csv := true } : ScriptFlags) pol
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      [ByteArray.empty, sig] chk .witnessV0
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData)
    = Except.ok [ByteArray.mk #[0x01]] := by
  unfold evalScriptBytes
  have hsz : (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)).size = 77 :=
    serializeOpcodes_toLocal_size revocationKey delayedPaymentKey csv hr hd
  rw [if_neg (by simp [hsz, MAX_SCRIPT_SIZE])]
  rw [toLocal_parseWire revocationKey delayedPaymentKey csv hr hd]
  simp [finalStack,
    evalFrom_toLocal_delayed_ok chk pol hpol revocationKey delayedPaymentKey
      csv sig n hr hd hdec hnn hdis hseq hsig]

/-- Positive delayed branch at `ExecuteWitnessScript`. -/
theorem executeWitnessScript_toLocal_delayed_ok
    (chk : ScriptChecker) (pol : PolicyFlags) (hpol : IsDelayPolicy pol)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (n : ScriptNum) (vwSer : Int)
    (hr : revocationKey.bytes.size = 33)
    (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hdec : decodeNum pol (delayBytes csv) 5 = .ok n)
    (hnn : 0 ≤ n)
    (hdis : Int.toNat n &&& SEQUENCE_LOCKTIME_DISABLE_FLAG = 0)
    (hseq : checkSequenceDef chk.env n = true)
    (hsig : chk.base.checkECDSASignature sig delayedPaymentKey.bytes
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      .witnessV0 (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true) :
    executeWitnessScript 10 [sig, ByteArray.empty] vwSer
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      ({ csv := true } : ScriptFlags) pol chk .witnessV0 = .ok := by
  have hsig' : ¬ Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE < sig.size := by
    unfold Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE; omega
  have hempty' : ¬ Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE < ByteArray.empty.size := by
    unfold Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE; decide
  simp [executeWitnessScript, executeWitnessScript.runExec,
    evalScriptBytes_toLocal_delayed_ok chk pol hpol revocationKey
      delayedPaymentKey csv sig n hr hd hdec hnn hdis hseq hsig,
    hsig', hempty', Bitcoin.Numeric.castToBool, Bitcoin.Numeric.castToBoolList]
  decide

/-- Positive delayed branch at the full vendored P2WSH verifier. -/
theorem verifyWitnessProgram_toLocal_delayed_ok
    (chk : ScriptChecker) (pol : PolicyFlags) (hpol : IsDelayPolicy pol)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (n : ScriptNum) (program : ByteArray)
    (hr : revocationKey.bytes.size = 33)
    (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hdec : decodeNum pol (delayBytes csv) 5 = .ok n)
    (hnn : 0 ≤ n)
    (hdis : Int.toNat n &&& SEQUENCE_LOCKTIME_DISABLE_FLAG = 0)
    (hseq : checkSequenceDef chk.env n = true)
    (hsig : chk.base.checkECDSASignature sig delayedPaymentKey.bytes
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      .witnessV0 (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true)
    (hps : program.size = 32)
    (hprog : hashSha256
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)) = program) :
    verifyWitnessProgram 10
      [sig, ByteArray.empty,
        serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)]
      0 program ({ csv := true } : ScriptFlags) pol chk false = .ok := by
  simp [verifyWitnessProgram, hps, hprog, byteArray_bne_self,
    executeWitnessScript_toLocal_delayed_ok chk pol hpol revocationKey
      delayedPaymentKey csv sig n
      (witnessSerSize [sig, ByteArray.empty,
        serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)])
      hr hd hsigsz hdec hnn hdis hseq hsig]

/-- The non-minimal-selector sequence failure at `EvalScript`'s byte entry. -/
theorem evalScriptBytes_toLocal_delayed_nonminimal_csv_false
    (chk : ScriptChecker)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (n : ScriptNum)
    (hr : revocationKey.bytes.size = 33)
    (hd : delayedPaymentKey.bytes.size = 33)
    (hdec : decodeNum ({} : PolicyFlags) (delayBytes csv) 5 = .ok n)
    (hnn : 0 ≤ n)
    (hdis : Int.toNat n &&& SEQUENCE_LOCKTIME_DISABLE_FLAG = 0)
    (hseq : checkSequenceDef chk.env n = false) :
    evalScriptBytes 10 ({ csv := true } : ScriptFlags) ({} : PolicyFlags)
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      [nonMinimalFalse, sig] chk .witnessV0
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData)
    = Except.error .unsatisfiedLocktime := by
  unfold evalScriptBytes
  have hsz : (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)).size = 77 :=
    serializeOpcodes_toLocal_size revocationKey delayedPaymentKey csv hr hd
  rw [if_neg (by simp [hsz, MAX_SCRIPT_SIZE])]
  rw [toLocal_parseWire revocationKey delayedPaymentKey csv hr hd]
  simp [finalStack,
    evalFrom_toLocal_delayed_nonminimal_csv_false chk revocationKey
      delayedPaymentKey csv sig n hr hd hdec hnn hdis hseq]

/-- The non-minimal-selector sequence failure at `ExecuteWitnessScript`. -/
theorem executeWitnessScript_toLocal_delayed_nonminimal_csv_false
    (chk : ScriptChecker)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (n : ScriptNum) (vwSer : Int)
    (hr : revocationKey.bytes.size = 33)
    (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hnmsz : nonMinimalFalse.size ≤ 520)
    (hdec : decodeNum ({} : PolicyFlags) (delayBytes csv) 5 = .ok n)
    (hnn : 0 ≤ n)
    (hdis : Int.toNat n &&& SEQUENCE_LOCKTIME_DISABLE_FLAG = 0)
    (hseq : checkSequenceDef chk.env n = false) :
    executeWitnessScript 10 [sig, nonMinimalFalse] vwSer
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      ({ csv := true } : ScriptFlags) ({} : PolicyFlags) chk .witnessV0
    = .fail .unsatisfiedLocktime := by
  have hsig' : ¬ Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE < sig.size := by
    unfold Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE; omega
  have hnmsz' : ¬ Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE < nonMinimalFalse.size := by
    unfold Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE nonMinimalFalse; decide
  simp [executeWitnessScript, executeWitnessScript.runExec,
    evalScriptBytes_toLocal_delayed_nonminimal_csv_false chk revocationKey
      delayedPaymentKey csv sig n hr hd hdec hnn hdis hseq,
    hsig', hnmsz']

/-- The non-minimal-selector sequence failure at the full P2WSH verifier. -/
theorem verifyWitnessProgram_toLocal_delayed_nonminimal_csv_false
    (chk : ScriptChecker)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (n : ScriptNum) (program : ByteArray)
    (hr : revocationKey.bytes.size = 33)
    (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hnmsz : nonMinimalFalse.size ≤ 520)
    (hdec : decodeNum ({} : PolicyFlags) (delayBytes csv) 5 = .ok n)
    (hnn : 0 ≤ n)
    (hdis : Int.toNat n &&& SEQUENCE_LOCKTIME_DISABLE_FLAG = 0)
    (hseq : checkSequenceDef chk.env n = false)
    (hps : program.size = 32)
    (hprog : hashSha256
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)) = program) :
    verifyWitnessProgram 10
      [sig, nonMinimalFalse,
        serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)]
      0 program ({ csv := true } : ScriptFlags) ({} : PolicyFlags) chk false
    = .fail .unsatisfiedLocktime := by
  simp [verifyWitnessProgram, hps, hprog, byteArray_bne_self,
    executeWitnessScript_toLocal_delayed_nonminimal_csv_false chk revocationKey
      delayedPaymentKey csv sig n
      (witnessSerSize [sig, nonMinimalFalse,
        serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)])
      hr hd hsigsz hnmsz hdec hnn hdis hseq]

/-- **Mechanized divergence.**  The model's `truthy` accepts the non-minimal
`#[0x00]` witness through the revocation branch, while the vendored/Core
`castToBool` sends the same witness down the delayed branch and rejects it
with `.fail .unsatisfiedLocktime`.  The witness is identical; only the
truthiness law differs. -/
theorem toLocal_nonminimal_selector_model_vendor_divergence
    (chk : ScriptChecker) (msg : ByteArray)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (n : ScriptNum) (program : ByteArray)
    (hr : revocationKey.bytes.size = 33)
    (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hdec : decodeNum ({} : PolicyFlags) (delayBytes csv) 5 = .ok n)
    (hnn : 0 ≤ n)
    (hdis : Int.toNat n &&& SEQUENCE_LOCKTIME_DISABLE_FLAG = 0)
    (hseq : checkSequenceDef chk.env n = false)
    (hrev : chk.base.checkECDSASignature sig revocationKey.bytes
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      .witnessV0 (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true)
    (hps : program.size = 32)
    (hprog : hashSha256
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)) = program) :
    Accepts (vendorLaws chk
        (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)))
      msg (toLocalProg revocationKey delayedPaymentKey csv)
      [nonMinimalFalse, sig] ∧
      verifyWitnessProgram 10
        [sig, nonMinimalFalse,
          serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)]
        0 program ({ csv := true } : ScriptFlags) ({} : PolicyFlags) chk false
        = .fail .unsatisfiedLocktime := by
  refine ⟨?_, ?_⟩
  · apply accepts_toLocal_nonminimal_selector_model
    simpa [vendorLaws] using hrev
  · exact verifyWitnessProgram_toLocal_delayed_nonminimal_csv_false chk
      revocationKey delayedPaymentKey csv sig n program hr hd hsigsz
      (by unfold nonMinimalFalse; decide) hdec hnn hdis hseq hps hprog

/-! ## 7. The policy-gated full P2WSH verdicts -/

/-- **Default-policy result.**  With the block/default policy word and the
`OP_CSV` consensus flag on, the canonical delayed witness is accepted by the
vendored P2WSH verifier exactly under the BIP 68/112 context and the
delayed-key signature.  (This is the wave-7 exact characterization, restated
here as the default-policy baseline; the new `MINIMALDATA` results below are
stated relative to it.) -/
theorem toLocal_delayed_default_policy_iff
    (chk : ScriptChecker)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (program : ByteArray) (hcsv : csv < 32768)
    (hr : revocationKey.bytes.size = 33)
    (hd : delayedPaymentKey.bytes.size = 33)
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
  toLocal_delayed_sequence_vendor_iff chk revocationKey delayedPaymentKey csv
    sig program hcsv hr hd hsigsz hps hprog

/-- **`MINIMALDATA`, long delay: acceptance.**  For `128 ≤ csv < 32768` the
`MINIMALDATA` decode succeeds, so the verdict is the same as the default
policy: the canonical delayed witness is accepted under the exact sequence
context and delayed-key signature. -/
theorem toLocal_delayed_minimalData_accept
    (chk : ScriptChecker)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (program : ByteArray)
    (hlo : 128 ≤ csv) (hhi : csv < 32768)
    (hr : revocationKey.bytes.size = 33)
    (hd : delayedPaymentKey.bytes.size = 33)
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
      0 program ({ csv := true } : ScriptFlags) minimalDataPolicy chk false = .ok :=
  verifyWitnessProgram_toLocal_delayed_ok chk minimalDataPolicy
    isDelayPolicy_minimalData revocationKey delayedPaymentKey csv sig (csv : Int)
    program hr hd hsigsz
    (decodeNum_delayBytes_minimalData_ok csv hlo hhi)
    (Int.natCast_nonneg csv) (disableBit_delay csv hhi) hseq hsig hps hprog

/-- The `MINIMALDATA` rejection at `EvalScript`'s byte entry. -/
theorem evalScriptBytes_toLocal_delayed_minimalData_error
    (chk : ScriptChecker)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray)
    (hr : revocationKey.bytes.size = 33)
    (hd : delayedPaymentKey.bytes.size = 33)
    (hcsv : csv < 128) :
    evalScriptBytes 10 ({ csv := true } : ScriptFlags) minimalDataPolicy
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      [ByteArray.empty, sig] chk .witnessV0
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData)
    = Except.error .scriptNum := by
  unfold evalScriptBytes
  have hsz : (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)).size = 77 :=
    serializeOpcodes_toLocal_size revocationKey delayedPaymentKey csv hr hd
  rw [if_neg (by simp [hsz, MAX_SCRIPT_SIZE])]
  rw [toLocal_parseWire revocationKey delayedPaymentKey csv hr hd]
  simp [finalStack,
    evalFrom_toLocal_delayed_minimalData_error chk revocationKey
      delayedPaymentKey csv sig hr hd hcsv]

/-- **`MINIMALDATA`, short delay: the mechanized counterexample.**  For
`csv < 128` the fixed-width `to_self_delay` encoding is non-minimal as a
`CScriptNum`; the vendored verifier fails with `.fail .scriptNum` before it
can consult the sequence environment or the delayed-key signature. -/
theorem executeWitnessScript_toLocal_delayed_minimalData_error
    (chk : ScriptChecker)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (vwSer : Int)
    (hr : revocationKey.bytes.size = 33)
    (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hcsv : csv < 128) :
    executeWitnessScript 10 [sig, ByteArray.empty] vwSer
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      ({ csv := true } : ScriptFlags) minimalDataPolicy chk .witnessV0
    = .fail .scriptNum := by
  have hsig' : ¬ Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE < sig.size := by
    unfold Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE; omega
  have hempty' : ¬ Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE < ByteArray.empty.size := by
    unfold Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE; decide
  simp [executeWitnessScript, executeWitnessScript.runExec,
    evalScriptBytes_toLocal_delayed_minimalData_error chk revocationKey
      delayedPaymentKey csv sig hr hd hcsv, hsig', hempty']

/-- **The full P2WSH policy-gated rejection.** -/
theorem toLocal_delayed_minimalData_reject
    (chk : ScriptChecker)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (program : ByteArray)
    (hcsv : csv < 128)
    (hr : revocationKey.bytes.size = 33)
    (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hps : program.size = 32)
    (hprog : hashSha256
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)) = program) :
    verifyWitnessProgram 10
      [sig, ByteArray.empty,
        serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)]
      0 program ({ csv := true } : ScriptFlags) minimalDataPolicy chk false
      = .fail .scriptNum := by
  simp [verifyWitnessProgram, hps, hprog, byteArray_bne_self,
    executeWitnessScript_toLocal_delayed_minimalData_error chk revocationKey
      delayedPaymentKey csv sig
      (witnessSerSize [sig, ByteArray.empty,
        serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)])
      hr hd hsigsz hcsv]

/-! ## 8. Policy tier: `MINIMALDATA` is a standard-not-mandatory bit -/

/-- The `MINIMALDATA` word carries a `STANDARD_NOT_MANDATORY_VERIFY_FLAGS`
bit, so the failure maps to `TX_NOT_STANDARD`. -/
theorem hasStandardNotMandatory_minimalDataPolicy :
    Bitcoin.TxValidation.Full.hasStandardNotMandatory minimalDataPolicy = true :=
  rfl

/-- The default/block word carries none. -/
theorem hasStandardNotMandatory_default :
    Bitcoin.TxValidation.Full.hasStandardNotMandatory (default : PolicyFlags) = false :=
  rfl

/-- Consequently a `MINIMALDATA` script failure is a mempool-policy
rejection, not a consensus one. -/
theorem scriptFailKind_minimalDataPolicy :
    Bitcoin.TxValidation.Full.scriptFailKind minimalDataPolicy = .notStandard :=
  rfl

end LnLean.Proofs.WaveH.H05
