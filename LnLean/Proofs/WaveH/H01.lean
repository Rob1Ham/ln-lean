import Bitcoin.TxValidation.Full
import Bitcoin.Capstone.RealChecker
import LnLean.Proofs.Bitcoin.SequenceContextTargets

/-!
# H01 — Full-pipeline checker equivalence (`txCheckerFor` ↔ `realCheckerOf`)

Wave 8, lane `H01`; roadmap issues `L1-02` and `L1-07`.

Wave 7 (`SequenceContextTargets`) transferred the delayed `to_local`
refinement to `Bitcoin.Capstone.RealChecker.realCheckerOf`, but the actual
transaction-validity pipeline consumes
`Bitcoin.TxValidation.Full.txCheckerFor`.  This module closes that gap at the
checker level:

* `txCheckerFor_some_eq_realCheckerOf` proves the exact equality
  `txCheckerFor tx nIn (some amount) = realCheckerOf tx nIn amount` for every
  input index — the explicit `nIn < tx.vin.length` hypothesis is *not* needed,
  because both definitions use the same `dummyTxIn` stand-in for the sequence
  environment;
* `txCheckerFor_some_eq_realCheckerOf_of_lt` records the in-range form stated
  in the lane target;
* the only structural difference between the two `ScriptChecker`s is the
  Schnorr slot (`txCheckerOf` uses `schnorrVerdict verify (fun _ _ _ => none)`;
  `realEcdsaEntry` uses `ecdsaEntry`'s `fun _ _ _ _ => false`).  We prove the
  former is pointwise `false` (`schnorrVerdict_sighash_none_false`), so the
  checkers are equal, and we provide the `ScriptChecker`/`BaseSignatureChecker`
  extensionality lemmas used by the proof;
* the missing-data (`none`) state is characterized exactly: its base is
  `ecdsaEntry verifyImpl (sighashDispatch tx nIn 0) false`, its witness-v0
  ECDSA entry fails closed for *every* signature/pubkey/scriptCode
  (`txCheckerFor_none_ecdsa_witnessV0`), and its legacy/taproot ECDSA behavior
  agrees with the `some amount` checker
  (`txCheckerFor_none_ecdsa_eq_some_of_ne`), i.e. missing amount data only
  removes witness-v0 signatures;
* `txCheckerFor_some_consumes_model_digest` shows the full-pipeline checker
  hands the vendored verifier exactly the model BIP 143 digest.

No definition is assumed: every statement is proved from the vendor
`txCheckerFor`/`realCheckerOf`/`txCheckerOf`/`ecdsaEntry` definitions.
-/

namespace LnLean.Proofs.WaveH.H01

set_option autoImplicit false

open Bitcoin.Data
open Bitcoin.Activation
open Bitcoin.Interpreter
open Bitcoin.Script.Parser
open Bitcoin.Crypto.Seam
open Bitcoin.Crypto.Seam.Entry
open LnLean
open LnLean.Bitcoin
open LnLean.Proofs.Bitcoin.SpendTargets
open LnLean.Proofs.Bitcoin.InterpreterBridgeTargets
open LnLean.Proofs.Bitcoin.SighashBridgeTargets

/-! ## 1. The Schnorr slot of `txCheckerFor` is the fail-closed stub -/

/-- `schnorrVerdict` with a sighash function that always returns `none` is
pointwise `false`.  This is the exact shape of `txCheckerFor`'s Schnorr slot
(`fun _ _ _ => none`): the fail-closed X03/X04 stand-in. -/
theorem schnorrVerdict_sighash_none_false
    (verify : ByteArray → ByteArray → ByteArray → Bool)
    (sig pk : ByteArray) (v : SigVersion) (d : ScriptExecutionData) :
    schnorrVerdict verify (fun _ _ _ => none) sig pk v d = false := by
  unfold schnorrVerdict
  split
  · split
    · cases schnorrHashtype sig with
      | none => rfl
      | some p =>
          obtain ⟨body, ht⟩ := p
          rfl
    · rfl
  · rfl

/-- `txCheckerOf` with the fail-closed Schnorr sighash is exactly the ECDSA
adapter.  The ECDSA entry points are definitionally the same; the Schnorr entry
points agree because the first is pointwise `false` and the second is the
literal constant `false`. -/
theorem txCheckerOf_eq_ecdsaEntry_of_sighash_none
    (verify : ByteArray → ByteArray → ByteArray → Bool)
    (sighash : ByteArray → UInt8 → SigVersion → ByteArray)
    (hasAmount : Bool)
    (verifySchnorr : ByteArray → ByteArray → ByteArray → Bool) :
    txCheckerOf verify sighash hasAmount verifySchnorr (fun _ _ _ => none)
      = ecdsaEntry verify sighash hasAmount := by
  apply Bitcoin.Crypto.Seam.checker_eq_of_entry_eq
  · intro sig pk code v d
    rfl
  · intro sig pk v d
    exact schnorrVerdict_sighash_none_false verifySchnorr sig pk v d

/-! ## 2. Extensionality of the checker records -/

/-- A `ScriptChecker` is determined by its base checker and locktime
environment.  (The `ScriptChecker` structure has exactly these two fields.) -/
theorem scriptChecker_ext {c₁ c₂ : ScriptChecker}
    (hbase : c₁.base = c₂.base) (henv : c₁.env = c₂.env) : c₁ = c₂ := by
  rcases c₁ with ⟨b₁, e₁⟩
  rcases c₂ with ⟨b₂, e₂⟩
  have hb : b₁ = b₂ := hbase
  have he : e₁ = e₂ := henv
  rw [hb, he]

/-- A `BaseSignatureChecker` is determined by its two consensus entry
points.  This is the vendor `checker_eq_of_entry_eq`, restated in this
namespace for downstream lanes. -/
theorem baseChecker_ext {c₁ c₂ : BaseSignatureChecker}
    (h₁ : ∀ sig pk code v d,
      c₁.checkECDSASignature sig pk code v d =
        c₂.checkECDSASignature sig pk code v d)
    (h₂ : ∀ sig pk v d,
      c₁.checkSchnorrSignature sig pk v d =
        c₂.checkSchnorrSignature sig pk v d) :
    c₁ = c₂ :=
  Bitcoin.Crypto.Seam.checker_eq_of_entry_eq h₁ h₂

/-! ## 3. The base and environment of `txCheckerFor` -/

/-- The base checker of `txCheckerFor tx nIn (some amount)` is exactly the
real ECDSA adapter over the capstone sighash dispatch with the spent amount
known. -/
theorem txCheckerFor_some_base (tx : Bitcoin.Data.Tx) (nIn : Nat)
    (amount : Amount) :
    (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount)).base =
      ecdsaEntry Bitcoin.Crypto.Ecdsa.Verify.verifyImpl
        (Bitcoin.Capstone.RealChecker.sighashDispatch tx nIn amount) true := by
  unfold Bitcoin.TxValidation.Full.txCheckerFor
  exact txCheckerOf_eq_ecdsaEntry_of_sighash_none _ _ _ _

/-- The base checker in the missing-data (`none`) state: same verifier and
sighash dispatch, but `hasAmount = false` and the dummy amount `0`. -/
theorem txCheckerFor_none_base (tx : Bitcoin.Data.Tx) (nIn : Nat) :
    (Bitcoin.TxValidation.Full.txCheckerFor tx nIn none).base =
      ecdsaEntry Bitcoin.Crypto.Ecdsa.Verify.verifyImpl
        (Bitcoin.Capstone.RealChecker.sighashDispatch tx nIn 0) false := by
  unfold Bitcoin.TxValidation.Full.txCheckerFor
  exact txCheckerOf_eq_ecdsaEntry_of_sighash_none _ _ _ _

/-- The locktime environment of `txCheckerFor`, in both the `some` and `none`
cases.  It is the real transaction environment with `dummyTxIn` as the
out-of-range stand-in. -/
theorem txCheckerFor_env (tx : Bitcoin.Data.Tx) (nIn : Nat)
    (amount : Option Amount) :
    (Bitcoin.TxValidation.Full.txCheckerFor tx nIn amount).env =
      { txVersion := tx.version
        txLockTime := tx.locktime
        txSequence :=
          (tx.vin.getD nIn Bitcoin.Capstone.RealChecker.dummyTxIn).sequence } :=
  rfl

/-! ## 4. The main full-pipeline checker equality -/

/-- **Full-pipeline checker equivalence.**  For every input index and every
spent amount, the transaction-validity pipeline checker
`Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount)` is *equal* to
the capstone real checker `Bitcoin.Capstone.RealChecker.realCheckerOf tx nIn
amount`.

The equality is unconditional: both definitions use the same
`Bitcoin.Capstone.RealChecker.dummyTxIn` for the out-of-range sequence
environment, and the only entry-point difference (the Schnorr slot) is the
fail-closed `none`/`false` pair proved in §1. -/
theorem txCheckerFor_some_eq_realCheckerOf
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount) :
    Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount) =
      Bitcoin.Capstone.RealChecker.realCheckerOf tx nIn amount := by
  unfold Bitcoin.TxValidation.Full.txCheckerFor
  unfold Bitcoin.Capstone.RealChecker.realCheckerOf
  unfold Bitcoin.Capstone.RealChecker.realEcdsaEntry
  rw [txCheckerOf_eq_ecdsaEntry_of_sighash_none]
  rfl

/-- The in-range form stated in the lane target.  The `hIn` hypothesis is
retained for direct use by downstream refusal/refinement lanes; the equality
itself does not consume it. -/
theorem txCheckerFor_some_eq_realCheckerOf_of_lt
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount)
    (_hIn : nIn < tx.vin.length) :
    Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount) =
      Bitcoin.Capstone.RealChecker.realCheckerOf tx nIn amount :=
  txCheckerFor_some_eq_realCheckerOf tx nIn amount

/-- Base-checker projection of the main equality. -/
theorem txCheckerFor_some_base_eq_realCheckerOf_base
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount) :
    (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount)).base =
      (Bitcoin.Capstone.RealChecker.realCheckerOf tx nIn amount).base := by
  rw [txCheckerFor_some_eq_realCheckerOf]

/-- Environment projection of the main equality. -/
theorem txCheckerFor_some_env_eq_realCheckerOf_env
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount) :
    (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount)).env =
      (Bitcoin.Capstone.RealChecker.realCheckerOf tx nIn amount).env := by
  rw [txCheckerFor_some_eq_realCheckerOf]

/-! ## 5. Missing-data (`none`) behavior -/

/-- **Missing amount data fails every witness-v0 ECDSA check.**  In the
`none` state the full-pipeline checker sets `hasAmount = false`; the vendored
adapter's missing-data branch (`SWT-055`) then rejects *every* witness-v0
signature, with no pubkey or non-empty-signature premise.  This is the exact
`HandleMissingData` fail-closed behavior of the pipeline. -/
theorem txCheckerFor_none_ecdsa_witnessV0
    (tx : Bitcoin.Data.Tx) (nIn : Nat)
    (sig pk scriptCode : ByteArray) (d : ScriptExecutionData) :
    (Bitcoin.TxValidation.Full.txCheckerFor tx nIn none).base.checkECDSASignature
      sig pk scriptCode .witnessV0 d = false := by
  rw [txCheckerFor_none_base]
  change ecdsaVerdict Bitcoin.Crypto.Ecdsa.Verify.verifyImpl
    (Bitcoin.Capstone.RealChecker.sighashDispatch tx nIn 0) false
    .witnessV0 sig pk scriptCode = false
  unfold ecdsaVerdict
  split
  · rfl
  · split
    · rfl
    · simp

/-- The trick behind `txCheckerFor_none_ecdsa_witnessV0`, at the adapter
level: `ecdsaEntry ... false` rejects every witness-v0 signature
unconditionally.  (The vendor `SWT-055` theorem carries pubkey/signature
premises; those premises are in fact unnecessary for the verdict.) -/
theorem ecdsaEntry_hasAmount_false_witnessV0
    (verify : ByteArray → ByteArray → ByteArray → Bool)
    (sighash : ByteArray → UInt8 → SigVersion → ByteArray)
    (sig pk scriptCode : ByteArray) (d : ScriptExecutionData) :
    (ecdsaEntry verify sighash false).checkECDSASignature
      sig pk scriptCode .witnessV0 d = false := by
  change ecdsaVerdict verify sighash false .witnessV0 sig pk scriptCode = false
  unfold ecdsaVerdict
  split
  · rfl
  · split
    · rfl
    · simp

/-- On every non-witness-v0 signature version the capstone sighash dispatch
ignores the spent amount (it uses the legacy digest). -/
theorem sighashDispatch_amount_eq_of_ne
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (a a' : Amount)
    (scriptCode : ByteArray) (ht : UInt8) (v : SigVersion)
    (hv : v ≠ SigVersion.witnessV0) :
    Bitcoin.Capstone.RealChecker.sighashDispatch tx nIn a scriptCode ht v =
      Bitcoin.Capstone.RealChecker.sighashDispatch tx nIn a' scriptCode ht v := by
  cases v <;> simp_all [Bitcoin.Capstone.RealChecker.sighashDispatch]

/-- **Missing amount data only removes witness-v0 signatures.**  On every
other signature version the `none` checker and the `some amount` checker have
exactly the same ECDSA verdict. -/
theorem txCheckerFor_none_ecdsa_eq_some_of_ne
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount)
    (sig pk scriptCode : ByteArray) (v : SigVersion)
    (d : ScriptExecutionData) (hv : v ≠ SigVersion.witnessV0) :
    (Bitcoin.TxValidation.Full.txCheckerFor tx nIn none).base.checkECDSASignature
        sig pk scriptCode v d =
      (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount)).base.checkECDSASignature
        sig pk scriptCode v d := by
  rw [txCheckerFor_none_base, txCheckerFor_some_base]
  change ecdsaVerdict Bitcoin.Crypto.Ecdsa.Verify.verifyImpl
      (Bitcoin.Capstone.RealChecker.sighashDispatch tx nIn 0) false
      v sig pk scriptCode =
    ecdsaVerdict Bitcoin.Crypto.Ecdsa.Verify.verifyImpl
      (Bitcoin.Capstone.RealChecker.sighashDispatch tx nIn amount) true
      v sig pk scriptCode
  unfold ecdsaVerdict
  rw [sighashDispatch_amount_eq_of_ne tx nIn 0 amount scriptCode
    (sig[sig.size - 1]!) v hv]
  simp [hv]

/-- The `none` and `some amount` checkers have the same Schnorr behavior
(the same fail-closed stub) and the same locktime environment. -/
theorem txCheckerFor_none_schnorr_eq_some
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount)
    (sig pk : ByteArray) (v : SigVersion) (d : ScriptExecutionData) :
    (Bitcoin.TxValidation.Full.txCheckerFor tx nIn none).base.checkSchnorrSignature
        sig pk v d =
      (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount)).base.checkSchnorrSignature
        sig pk v d :=
  rfl

theorem txCheckerFor_none_env_eq_some
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount) :
    (Bitcoin.TxValidation.Full.txCheckerFor tx nIn none).env =
      (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount)).env :=
  rfl

/-! ## 6. The full-pipeline checker consumes the model digest -/

/-- **The pipeline checker's witness-v0 ECDSA check is the model BIP 143
digest check.**  For a valid pubkey and a non-empty signature, the checker
handed to the script lane computes `sighashWitnessV0` from the transaction
context and passes it, with the signature body, to the vendored verifier.
This is `SighashBridgeTargets.checker_consumes_model_digest` at the
`txCheckerFor` boundary, with no in-range hypothesis. -/
theorem txCheckerFor_some_consumes_model_digest
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount)
    (sig pk scriptCode : ByteArray) (d : ScriptExecutionData)
    (hpk : Bitcoin.Crypto.Seam.Der.isValidPubKey pk = true)
    (hne : 0 < sig.size) :
    (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount)).base.checkECDSASignature
        sig pk scriptCode .witnessV0 d =
      Bitcoin.Crypto.Ecdsa.Verify.verifyImpl (sig.extract 0 (sig.size - 1)) pk
        (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn scriptCode
          (hashtypeOf sig) amount) := by
  rw [txCheckerFor_some_base]
  rw [ecdsaEntry_pops_hashtype Bitcoin.Crypto.Ecdsa.Verify.verifyImpl
    (Bitcoin.Capstone.RealChecker.sighashDispatch tx nIn amount) true
    sig pk scriptCode .witnessV0 d hpk hne (by intro _; rfl)]
  simp only [Bitcoin.Capstone.RealChecker.sighashDispatch,
    Bitcoin.Capstone.RealChecker.htToU32, hashtypeOf]
  rw [LnLean.Bitcoin.Sighash.sighashWitnessV0_eq_interface]

/-! ## 7. Payoff: delayed `to_local` refinement at `txCheckerFor`

This corollary is the immediate downstream use of the equality; it is the
wave-7 `toLocal_delayed_realChecker_refinement` transported to the full
pipeline checker.  Lane `H02` owns the broader transfer, so this is recorded
as a compatibility corollary (same hypotheses, no new assumption). -/

/-- The delayed `to_local` refinement at the full transaction-validation
checker.  Identical to
`SequenceContextTargets.toLocal_delayed_realChecker_refinement` except that
the checker is `TxValidation.Full.txCheckerFor tx nIn (some amount)`. -/
theorem toLocal_delayed_txCheckerFor_refinement
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
      (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount)) false = .ok ↔
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
  rw [txCheckerFor_some_eq_realCheckerOf tx nIn amount]
  exact LnLean.Proofs.Bitcoin.SequenceContextTargets.toLocal_delayed_realChecker_refinement
    tx nIn amount hIn revocationKey
    delayedPaymentKey csv sig program hcsv hr hd hsigsz hps hprog hpk hne

end LnLean.Proofs.WaveH.H01

