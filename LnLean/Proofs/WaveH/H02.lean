/-
# H02 — delayed `to_local` refinement at `TxValidation.Full.txCheckerFor`
(L1-02, L1-07)

**Catalog issues.**

* `L1-02` (P0): the `to_local` CSV/revocation execution has a remaining
  transaction-validity transfer boundary.  Wave 7's
  `SequenceContextTargets.toLocal_delayed_checkerOf_refinement` and
  `toLocal_delayed_realChecker_refinement` characterize the vendored delayed
  witness exactly at `checkerOf verifyImpl` and at
  `Bitcoin.Capstone.RealChecker.realCheckerOf`, but the full transaction
  pipeline consumes `Bitcoin.TxValidation.Full.txCheckerFor tx nIn
  (some amount)`, which is a *different* `ScriptChecker` record (it carries
  the real BIP340 Schnorr entry).
* `L1-07` (P0): the vendored interpreter bridge has to reach
  `TxValidation.Full`/`txCheckerFor`, not only the capstone checker.

**Integration note.** H01 subsequently proves the whole-record equality
`txCheckerFor tx nIn (some amount) = realCheckerOf tx nIn amount` (the
fail-closed Schnorr slot is the only difference and is proved equal under the
`none` sighash).  The statements below that say no whole-record equality is
claimed are therefore superseded by H01; this module's delayed-branch
refinement remains valid and is the direct full-checker statement.

## Result of this module

1. `txCheckerFor_some_checkECDSA_eq_checkerOf`: for `some amount`, the ECDSA
   entry point of `txCheckerFor` is *exactly* the ECDSA entry point of
   `SighashBridgeTargets.checkerOf verifyImpl` (the checker used by the wave-7
   refinement).  The Schnorr field differs — `txCheckerFor` carries the real
   BIP340 verifier while `checkerOf` carries the fail-closed ECDSA stub — so
   this module does not rely on whole-record equality (H01 proves that
   equality separately); on witness-v0 P2WSH only the ECDSA entry is
   consulted.
2. `txCheckerFor_some_consumes_model_digest`: the concrete verifier call the
   checker makes on a witness-v0 signature is
   `verifyImpl (sig minus hashtype) pk (sighashWitnessV0 …)`.
3. `toLocal_delayed_txCheckerFor_refinement`: **the exact delayed-branch
   criterion at `txCheckerFor tx nIn (some amount)`**: the full P2WSH verdict
   is `.ok` iff the BIP 68/112 context is satisfied (version ≥ 2, input
   disable bit clear, height domain, `csv ≤` masked sequence) and the
   concrete lax-secp256k1 verifier accepts the BIP 143 model digest.  No
   `nIn < tx.vin.length` premise is needed: `txCheckerFor` and
   `realCheckerOf` use the *same* `RealChecker.dummyTxIn` totalization.
4. `toLocal_delayed_txCheckerFor_refinement_of_lt`: the same statement written
   with `SighashBridgeTargets.dummyTxIn` (the term used by the wave-7 source
   theorem) for an in-range input `nIn < tx.vin.length`.
5. `toLocal_delayed_txCheckerFor_iff_realChecker`: the transfer itself — on
   the exact delayed witness, the `txCheckerFor (some amount)` verdict is
   equivalent to the `realCheckerOf` verdict, for an in-range input.  Hence
   every delayed-branch result already proved for `realCheckerOf` lifts to the
   full transaction checker.
6. `toLocal_delayed_txCheckerFor_none_verdict` /
   `toLocal_delayed_txCheckerFor_none_not_ok`: the missing-data behavior.  For
   `amount = none` (the pipeline's `-1` sentinel / Core `HandleMissingData`)
   the witness-v0 ECDSA entry is `false` before any sighash is computed.  The
   verdict is exactly `.fail .unsatisfiedLocktime` when the sequence check
   rejects and `.fail .evalFalse` when it accepts, so the delayed witness can
   never reach `.ok`.

## Hypotheses / scope

* `csv < 32768` is the faithful fixed-width delay range; it discharges the
  `decodeNum`/non-negativity/disable-bit premises of the wave-5 bridge.
* 33-byte compressed keys, `sig.size ≤ 520`, and `program.size = 32` are the
  P2WSH witness-shape premises; `hprog` is the commitment of the witness
  script to the spent program.
* The clawback (revocation) key only enters through the witness script; the
  delayed branch checks the delayed-payment key.
* `hpk`/`hne` are the pubkey-validity/non-empty-signature gates the ECDSA
  adapter needs to reach the EC math (`checker_consumes_model_digest`).
* Positive-direction only: no consensus-spendability or unconditional
  transaction-validity claim.  The sequencer/activation/policy premises are
  the ones named in the statements (`flags.csv = true`, `pol = default`), and
  the `minimalData` / `csv ≥ 32768` policy edges remain lanes H05/H06.
- `some amount` is the fully-resolved prevout amount; `none` is the
  fail-closed missing-data state.

## Anchors

* BIP 68/112: version ≥ 2, disable bit clear, height domain, masked sequence
  comparison (`checkSequenceDef_delay_iff`, wave 7).
* BOLT 3 §"Commitment Transaction Outputs" (`to_local`) and the CSV contest
  delay.
* Model: `LnLean/Proofs/Bitcoin/SequenceContextTargets.lean` (wave-7 source
  refinement); `LnLean/Proofs/Bitcoin/SighashBridgeTargets.lean`
  (`checkerOf`, `checker_consumes_model_digest`).
* Vendor: `Bitcoin/TxValidation/Full.lean` (`txCheckerFor`,
  `ScriptEntry := ByteArray × Option Amount`), `Bitcoin/Capstone/RealChecker.lean`
  (`realCheckerOf`, `dummyTxIn`), `Bitcoin/Crypto/Seam/Entry.lean`
  (`txCheckerOf`, `ecdsaEntry`, `ecdsaVerdict`).
-/

import Bitcoin.TxValidation.Full
import LnLean.Proofs.Bitcoin.SequenceContextTargets

namespace LnLean.Proofs.WaveH.H02

set_option autoImplicit false

open Bitcoin.Data
open Bitcoin.Activation
open Bitcoin.Script.Parser
open Bitcoin.Interpreter
open Bitcoin.Numeric
open Bitcoin.Crypto.Seam.Entry
open LnLean
open LnLean.Bitcoin
open LnLean.Proofs.Bitcoin.SpendTargets
open LnLean.Proofs.Bitcoin.InterpreterBridgeTargets
open LnLean.Proofs.Bitcoin.InterpreterRevocationTargets
open LnLean.Proofs.Bitcoin.SighashBridgeTargets
open LnLean.Proofs.Bitcoin.SequenceContextTargets

/-! ## 1. Local checker equality (H01-style) -/

/-- **ECDSA-entry equality.**  For a fully-resolved amount, the ECDSA entry
point of the full pipeline checker `txCheckerFor tx nIn (some amount)` is
exactly the ECDSA entry point of the wave-7 bridge checker
`checkerOf verifyImpl tx nIn amount`.

The `txCheckerFor` base is `txCheckerOf …` (real ECDSA + real BIP340) while
`checkerOf` is an `ecdsaEntry` (real ECDSA + fail-closed Schnorr stub), so the
records are *not* equal.  On witness-v0 P2WSH the interpreter consults only
`checkECDSASignature` and the locktime environment, which are the two
components this theorem and the next identify. -/
theorem txCheckerFor_some_checkECDSA_eq_checkerOf
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount)
    (sig pk code : ByteArray) (v : Bitcoin.Crypto.Seam.SigVersion)
    (d : Bitcoin.Crypto.Seam.ScriptExecutionData) :
    (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount)).base.checkECDSASignature
        sig pk code v d =
      (checkerOf Bitcoin.Crypto.Ecdsa.Verify.verifyImpl tx nIn amount).base.checkECDSASignature
        sig pk code v d := by
  simp only [Bitcoin.TxValidation.Full.txCheckerFor, txCheckerOf_ecdsa, checkerOf,
    ecdsaEntry, Option.getD_some, Option.isSome_some]
  rw [show Bitcoin.Capstone.RealChecker.sighashDispatch tx nIn amount
      = LnLean.Proofs.Bitcoin.SighashBridgeTargets.sighashDispatch tx nIn amount from
      (sighashDispatch_eq_real tx nIn amount).symm]

/-- **Environment equality.**  For an in-range input, the full pipeline
checker's transaction environment is the wave-7 bridge environment.  The two
`dummyTxIn` values differ only in their out-of-range totalization (sequence
`0xFFFFFFFF` versus `0`), which `hIn` removes. -/
theorem txCheckerFor_some_env_eq_locktimeEnvOf
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount) (hIn : nIn < tx.vin.length) :
    (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount)).env =
      locktimeEnvOf tx nIn := by
  have hget : tx.vin.getD nIn Bitcoin.Capstone.RealChecker.dummyTxIn =
      tx.vin.getD nIn dummyTxIn := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hIn]
    simp
  simp only [Bitcoin.TxValidation.Full.txCheckerFor, locktimeEnvOf]
  rw [hget]

/-- The delayed witness consumes exactly the model digest through the full
pipeline checker.  This is `checker_consumes_model_digest` transferred along
the ECDSA-entry equality above. -/
theorem txCheckerFor_some_consumes_model_digest
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount)
    (sig pk scriptCode : ByteArray) (ed : Bitcoin.Crypto.Seam.ScriptExecutionData)
    (hpk : Bitcoin.Crypto.Seam.Der.isValidPubKey pk = true)
    (hne : 0 < sig.size) :
    (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount)).base.checkECDSASignature
        sig pk scriptCode .witnessV0 ed =
      Bitcoin.Crypto.Ecdsa.Verify.verifyImpl (sig.extract 0 (sig.size - 1)) pk
        (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn scriptCode
          (hashtypeOf sig) amount) := by
  rw [txCheckerFor_some_checkECDSA_eq_checkerOf]
  exact checker_consumes_model_digest Bitcoin.Crypto.Ecdsa.Verify.verifyImpl
    tx nIn amount sig pk scriptCode ed hpk hne

/-! ## 2. The transfer and the exact delayed criterion -/

/-- **Transfer of the delayed verdict.**  On the exact delayed `to_local`
witness, the full transaction checker `txCheckerFor tx nIn (some amount)`
returns `.ok` exactly when the capstone `realCheckerOf tx nIn amount` does.
This is the H01-style bridge between the pipeline checker and the wave-7
real-checker result; no whole-record equality is needed (the Schnorr fields
differ and are not consulted on witness-v0 P2WSH), and no index-range premise
is needed because both checkers read `RealChecker.dummyTxIn`. -/
theorem toLocal_delayed_txCheckerFor_iff_realChecker
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount)
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
        0 program ({ csv := true } : ScriptFlags) ({} : PolicyFlags)
        (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount)) false = .ok ↔
      verifyWitnessProgram 10
        [sig, ByteArray.empty,
          serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)]
        0 program ({ csv := true } : ScriptFlags) ({} : PolicyFlags)
        (Bitcoin.Capstone.RealChecker.realCheckerOf tx nIn amount) false = .ok := by
  rw [toLocal_delayed_sequence_context_refinement
        (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount))
        revocationKey delayedPaymentKey csv sig program hcsv hr hd hsigsz hps hprog,
      toLocal_delayed_sequence_context_refinement
        (Bitcoin.Capstone.RealChecker.realCheckerOf tx nIn amount)
        revocationKey delayedPaymentKey csv sig program hcsv hr hd hsigsz hps hprog]
  simp only [Bitcoin.TxValidation.Full.txCheckerFor,
    Bitcoin.Capstone.RealChecker.realCheckerOf,
    Bitcoin.Capstone.RealChecker.realEcdsaEntry,
    txCheckerOf_ecdsa, ecdsaEntry, Option.getD_some, Option.isSome_some]

/-- **Exact delayed criterion at the full transaction checker.**  The full
P2WSH verdict under `txCheckerFor tx nIn (some amount)` is `.ok` exactly when

* the transaction version is at least 2,
* the input's BIP 68 disable bit is clear,
* the masked input sequence is in the height domain, and
* `csv` is at most that masked sequence,

and the concrete lax-secp256k1 verifier accepts the BIP 143 model digest.

The sequence context is read through `RealChecker.dummyTxIn`, exactly the
`txCheckerFor` environment; no index-range premise is needed for this form. -/
theorem toLocal_delayed_txCheckerFor_refinement
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
      (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount)) false = .ok ↔
      ((¬ tx.version < 2) ∧
        ((tx.vin.getD nIn Bitcoin.Capstone.RealChecker.dummyTxIn).sequence.toNat &&&
            SEQUENCE_LOCKTIME_DISABLE_FLAG) = 0 ∧
        ((tx.vin.getD nIn Bitcoin.Capstone.RealChecker.dummyTxIn).sequence.toNat &&&
            (SEQUENCE_LOCKTIME_TYPE_FLAG ||| SEQUENCE_LOCKTIME_MASK)) <
          SEQUENCE_LOCKTIME_TYPE_FLAG ∧
        csv ≤ ((tx.vin.getD nIn Bitcoin.Capstone.RealChecker.dummyTxIn).sequence.toNat &&&
            (SEQUENCE_LOCKTIME_TYPE_FLAG ||| SEQUENCE_LOCKTIME_MASK)) ∧
        Bitcoin.Crypto.Ecdsa.Verify.verifyImpl (sig.extract 0 (sig.size - 1))
          delayedPaymentKey.bytes
          (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn
            (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
            (hashtypeOf sig) amount) = true) := by
  have h := toLocal_delayed_sequence_context_refinement
    (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount))
    revocationKey delayedPaymentKey csv sig program hcsv hr hd hsigsz hps hprog
  rw [h]
  have hsig' := txCheckerFor_some_consumes_model_digest tx nIn amount sig
    delayedPaymentKey.bytes
    (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
    (default : Bitcoin.Crypto.Seam.ScriptExecutionData) hpk hne
  rw [hsig']
  simp only [Bitcoin.TxValidation.Full.txCheckerFor]

/-- **In-range form of the exact delayed criterion.**  This is the wave-7
`toLocal_delayed_realChecker_refinement` statement with the checker replaced by
`TxValidation.Full.txCheckerFor tx nIn (some amount)`, and the sequence read
through the bridge's `dummyTxIn`.  For an in-range input the two totalizations
agree. -/
theorem toLocal_delayed_txCheckerFor_refinement_of_lt
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
  rw [toLocal_delayed_txCheckerFor_iff_realChecker tx nIn amount
        revocationKey delayedPaymentKey csv sig program hcsv hr hd hsigsz hps hprog,
      toLocal_delayed_realChecker_refinement tx nIn amount hIn
        revocationKey delayedPaymentKey csv sig program hcsv hr hd hsigsz hps hprog hpk hne]

/-! ## 3. Missing-data (`none`) behavior -/

/-- **Missing amount fails the witness-v0 ECDSA entry.**  With
`amount = none` the pipeline checker has `hasAmount = false`; the vendored
`ecdsaVerdict` then rejects every witness-v0 signature before computing a
sighash (`HandleMissingData`, SWT-055).  No pubkey/signature hypothesis is
needed for this failure. -/
theorem txCheckerFor_none_checkECDSA_witnessV0_false
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (sig pk scriptCode : ByteArray)
    (ed : Bitcoin.Crypto.Seam.ScriptExecutionData) :
    (Bitcoin.TxValidation.Full.txCheckerFor tx nIn none).base.checkECDSASignature
        sig pk scriptCode .witnessV0 ed = false := by
  simp [Bitcoin.TxValidation.Full.txCheckerFor, txCheckerOf_ecdsa, ecdsaEntry,
    ecdsaVerdict]

/-- **Exact missing-data verdict.**  With `amount = none`, the delayed
`to_local` witness verdict is fully characterized: if the vendored sequence
check rejects, execution stops at `OP_CSV` with `.fail .unsatisfiedLocktime`;
if it accepts, the missing-amount ECDSA entry rejects and the verdict is
`.fail .evalFalse`.  In particular `.ok` is unreachable. -/
theorem toLocal_delayed_txCheckerFor_none_verdict
    (tx : Bitcoin.Data.Tx) (nIn : Nat)
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
      0 program ({ csv := true } : ScriptFlags) ({} : PolicyFlags)
      (Bitcoin.TxValidation.Full.txCheckerFor tx nIn none) false =
      (match checkSequenceDef (Bitcoin.TxValidation.Full.txCheckerFor tx nIn none).env
          (csv : Int) with
       | true => .fail .evalFalse
       | false => .fail .unsatisfiedLocktime) := by
  cases hseq : checkSequenceDef (Bitcoin.TxValidation.Full.txCheckerFor tx nIn none).env
      (csv : Int) with
  | true =>
      simpa [hseq] using verifyWitnessProgram_toLocal_delayed_bad_sig
        (Bitcoin.TxValidation.Full.txCheckerFor tx nIn none)
        revocationKey delayedPaymentKey csv sig (csv : Int) program hr hd hsigsz
        (decodeNum_delayBytes csv hcsv) (nonneg_delay csv) (disableBit_delay csv hcsv)
        hseq (txCheckerFor_none_checkECDSA_witnessV0_false tx nIn sig delayedPaymentKey.bytes
          (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
          (default : Bitcoin.Crypto.Seam.ScriptExecutionData)) hps hprog
  | false =>
      simpa [hseq] using verifyWitnessProgram_toLocal_delayed_csv_false
        (Bitcoin.TxValidation.Full.txCheckerFor tx nIn none)
        revocationKey delayedPaymentKey csv sig (csv : Int) program hr hd hsigsz
        (decodeNum_delayBytes csv hcsv) (nonneg_delay csv) (disableBit_delay csv hcsv)
        hseq hps hprog

/-- **Missing-data negative.**  With `amount = none`, the delayed `to_local`
witness can never verify — regardless of the transaction's sequence context.
This is the fail-closed boundary the full pipeline relies on when a prevout
amount is absent. -/
theorem toLocal_delayed_txCheckerFor_none_not_ok
    (tx : Bitcoin.Data.Tx) (nIn : Nat)
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
      0 program ({ csv := true } : ScriptFlags) ({} : PolicyFlags)
      (Bitcoin.TxValidation.Full.txCheckerFor tx nIn none) false ≠ .ok := by
  rw [toLocal_delayed_txCheckerFor_none_verdict tx nIn revocationKey delayedPaymentKey
    csv sig program hcsv hr hd hsigsz hps hprog]
  cases hseq : checkSequenceDef (Bitcoin.TxValidation.Full.txCheckerFor tx nIn none).env
      (csv : Int) <;> simp

/-! ## 4. Axiom pins -/

section Pins

/-- info: 'LnLean.Proofs.WaveH.H02.txCheckerFor_some_checkECDSA_eq_checkerOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms txCheckerFor_some_checkECDSA_eq_checkerOf
/-- info: 'LnLean.Proofs.WaveH.H02.txCheckerFor_some_env_eq_locktimeEnvOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms txCheckerFor_some_env_eq_locktimeEnvOf
/-- info: 'LnLean.Proofs.WaveH.H02.txCheckerFor_some_consumes_model_digest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms txCheckerFor_some_consumes_model_digest
/-- info: 'LnLean.Proofs.WaveH.H02.toLocal_delayed_txCheckerFor_iff_realChecker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms toLocal_delayed_txCheckerFor_iff_realChecker
/-- info: 'LnLean.Proofs.WaveH.H02.toLocal_delayed_txCheckerFor_refinement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms toLocal_delayed_txCheckerFor_refinement
/-- info: 'LnLean.Proofs.WaveH.H02.toLocal_delayed_txCheckerFor_refinement_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms toLocal_delayed_txCheckerFor_refinement_of_lt
/-- info: 'LnLean.Proofs.WaveH.H02.txCheckerFor_none_checkECDSA_witnessV0_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms txCheckerFor_none_checkECDSA_witnessV0_false
/-- info: 'LnLean.Proofs.WaveH.H02.toLocal_delayed_txCheckerFor_none_verdict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms toLocal_delayed_txCheckerFor_none_verdict
/-- info: 'LnLean.Proofs.WaveH.H02.toLocal_delayed_txCheckerFor_none_not_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms toLocal_delayed_txCheckerFor_none_not_ok

end Pins

end LnLean.Proofs.WaveH.H02
