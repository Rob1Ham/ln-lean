import Bitcoin.TxValidation.Full
import LnLean.Proofs.Bitcoin.SequenceContextTargets

/-!
# H32 — the revocation `to_local` branch at `TxValidation.Full.txCheckerFor`

Wave 8 (lane `H32`, issues `L1-02`, `L1-07`).  The Wave-6 bridge
`InterpreterRevocationTargets` executes the BOLT 3 revocation (`OP_IF`)
branch of `to_local` against an **abstract** `ScriptChecker`, and the
Wave-7 module `SequenceContextTargets` removes the abstract decode/range
hypotheses of the delayed branch and transfers it to
`checkerOf Bitcoin.Crypto.Ecdsa.Verify.verifyImpl` and to
`Bitcoin.Capstone.RealChecker.realCheckerOf`.  Both stop one step short of
the pipeline checker `Bitcoin.TxValidation.Full.txCheckerFor`.

This module closes that step for the **revocation** branch:

* it identifies the ECDSA entry and the locktime environment of
  `txCheckerFor tx nIn (some amount)` with the model checker
  `checkerOf verifyImpl tx nIn amount` (the Schnorr slots differ, and are
  consensus-inert for a witness-v0 P2WSH ECDSA spend, so the results are
  stated directly at `txCheckerFor` rather than through an unsound
  whole-checker equality);
* it turns the opaque vendor `checkECDSASignature … = true` hypothesis into
  the explicit lax-secp256k1 call
  `Bitcoin.Crypto.Ecdsa.Verify.verifyImpl body revocationKey.bytes
    (sighashWitnessV0 tx nIn scriptCode (hashtypeOf sig) amount)`;
* it proves the positive revocation branch and the exact iff at
  `txCheckerFor` (`verifyWitnessProgram … = .ok ↔ verifyImpl … = true`),
  together with the model-side `P2WSHSpend` companion;
* it proves the wrong-key negative in two forms: a rejected verifier call
  and the Lightning-meaningful "signature valid for `local_delayedpubkey`
  cannot use the revocation branch" form under an explicit ECDSA key
  separation hypothesis (`EcdsaKeySeparated`, the `CR-01` boundary);
* it proves the wrong-branch negatives: the empty selector cannot use a
  valid revocation-key signature (it takes the `OP_ELSE` branch, which
  fails with `.unsatisfiedLocktime` when the BIP 68/112 context fails, or
  with `.evalFalse` when the delayed key check fails), and gives the
  selector-level branch-selection theorem at `txCheckerFor`;
* it proves the missing-data (`amount = none`) negative: the
  `HandleMissingData` fail-closed path makes the witness-v0 ECDSA entry
  `false`, so the revocation witness fails with `.evalFalse`.

Everything is one-directional or an exact vendor-valued characterization:
there is no consensus-acceptance claim, no BIP 143 cryptographic claim (the
digest is the model digest fed to the vendored verifier), and no assertion
that `verifyWitnessProgram = .ok` implies model acceptance in general.
`TxValidation.Full.scriptLane`/`txVerdictFull` composition is a separate
lane (`H04`).

Anchors: BOLT 3 §`to_local` Output (`refs/bolts/03-transactions.md:113-135`),
BIP 141/143/112, Core `interpreter.cpp:1701-1744`, and
`refs/rust-lightning/lightning/src/ln/chan_utils.rs:687-700`.
-/

namespace LnLean.Proofs.WaveH.H32

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Bitcoin.Data
open Bitcoin.Activation
open Bitcoin.Script.Parser
open Bitcoin.Interpreter
open Bitcoin.Numeric
open Bitcoin.Crypto.Seam
open LnLean
open LnLean.Bitcoin
open LnLean.Proofs.Bitcoin.SpendTargets
open LnLean.Proofs.Bitcoin.InterpreterBridgeTargets
open LnLean.Proofs.Bitcoin.InterpreterRevocationTargets
open LnLean.Proofs.Bitcoin.SighashBridgeTargets
open LnLean.Proofs.Bitcoin.SequenceContextTargets
open Bitcoin.TxValidation.Full

/-! ## 0. Local vocabulary -/

/-- The totalization `TxIn` used by `Full.txCheckerFor`'s environment
(`Bitcoin.Capstone.RealChecker.dummyTxIn`, sequence `0xFFFFFFFF`).  The
model `SighashBridgeTargets.dummyTxIn` uses sequence `0` instead; the two
agree on every in-range input, which is the `nIn < tx.vin.length` premise of
`txCheckerFor_some_env_eq_locktimeEnvOf` below. -/
def fullDummyTxIn : Bitcoin.Data.TxIn := Bitcoin.Capstone.RealChecker.dummyTxIn

/-- The BOLT 3 `to_local` witness script code.  Definitionally
`serializeOpcodes (toLocalOps …)`, the exact script bytes executed by the
vendored interpreter. -/
abbrev toLocalCode (revocationKey delayedPaymentKey : PubKey) (csv : Blocks) :
    ByteArray :=
  serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)

/-- The P2WSH program committed by the `to_local` witness script. -/
abbrev toLocalProgram (revocationKey delayedPaymentKey : PubKey) (csv : Blocks) :
    ByteArray :=
  hashSha256 (toLocalCode revocationKey delayedPaymentKey csv)

/-- Revocation witness shape `[<sig>, 0x01, <witnessScript>]`. -/
abbrev revocationWitness (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) : List ByteArray :=
  [sig, revocationSelector, toLocalCode revocationKey delayedPaymentKey csv]

/-- Delayed witness shape `[<sig>, <>, <witnessScript>]`. -/
abbrev delayedWitness (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) : List ByteArray :=
  [sig, ByteArray.empty, toLocalCode revocationKey delayedPaymentKey csv]

/-- The consensus flag word used throughout: BIP 112 CSV enabled. -/
abbrev toLocalFlags : ScriptFlags := { csv := true }

/-- The empty policy word: consensus defaults, no `minimalData`/cleanstack
policy bits. -/
abbrev noPolicy : PolicyFlags := {}

/-- The `to_local` program is 32 bytes, so a 32-byte program is exactly its
hash commitment. -/
theorem toLocalProgram_size (revocationKey delayedPaymentKey : PubKey) (csv : Blocks) :
    (toLocalProgram revocationKey delayedPaymentKey csv).size = 32 :=
  hashSha256_size _

/-! ## 1. The concrete checker: ECDSA entry and environment -/

/-- `txCheckerFor` at a **known** amount is the model checker on the ECDSA
entry: both are `ecdsaEntry verifyImpl` over the same BIP 143 dispatch with
`hasAmount = true`.  (The two checkers' Schnorr fields differ — the pipeline
installs the real BIP340 verifier, the model installs the Wave-3
fail-closed stub — so this is an ECDSA-entry equality, which is the only
entry a witness-v0 P2WSH script reaches.) -/
theorem txCheckerFor_some_base_ecdsa_eq (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount) :
    (txCheckerFor tx nIn (some amount)).base.checkECDSASignature =
      (checkerOf Bitcoin.Crypto.Ecdsa.Verify.verifyImpl tx nIn amount).base.checkECDSASignature := by
  funext sig pk code v ed
  simp only [txCheckerFor, Option.getD_some, Option.isSome_some,
    Bitcoin.Crypto.Seam.Entry.txCheckerOf, Bitcoin.Crypto.Seam.Entry.ecdsaEntry,
    LnLean.Proofs.Bitcoin.SighashBridgeTargets.checkerOf,
    Bitcoin.Crypto.Seam.Entry.ecdsaVerdict]
  rw [LnLean.Proofs.Bitcoin.SequenceContextTargets.sighashDispatch_eq_real tx nIn amount]

/-- The locktime environment of `txCheckerFor` reads exactly the
transaction fields, with the pipeline's totalization `TxIn`. -/
@[simp] theorem txCheckerFor_some_env_txVersion (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount) :
    (txCheckerFor tx nIn (some amount)).env.txVersion = tx.version := rfl

@[simp] theorem txCheckerFor_some_env_txLockTime (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount) :
    (txCheckerFor tx nIn (some amount)).env.txLockTime = tx.locktime := rfl

@[simp] theorem txCheckerFor_some_env_txSequence (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount) :
    (txCheckerFor tx nIn (some amount)).env.txSequence =
      (tx.vin.getD nIn fullDummyTxIn).sequence := rfl

/-- For an **in-range** input the pipeline environment is exactly the model
`locktimeEnvOf` environment.  This is where the two totalization stand-ins
(sequence `0xFFFFFFFF` versus `0`) are shown irrelevant. -/
theorem txCheckerFor_some_env_eq_locktimeEnvOf (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount)
    (hIn : nIn < tx.vin.length) :
    (txCheckerFor tx nIn (some amount)).env = locktimeEnvOf tx nIn := by
  have hseq : (tx.vin[nIn]?.getD Bitcoin.Capstone.RealChecker.dummyTxIn).sequence =
      (tx.vin[nIn]?.getD LnLean.Proofs.Bitcoin.SighashBridgeTargets.dummyTxIn).sequence := by
    rw [List.getElem?_eq_getElem hIn]
    rfl
  simp [txCheckerFor, locktimeEnvOf, hseq]

/-- **The concrete vendor ECDSA verifier behind `txCheckerFor`.**  For a
known amount, a valid pubkey header and a non-empty signature, the pipeline
checker's witness-v0 ECDSA entry is literally
`Bitcoin.Crypto.Ecdsa.Verify.verifyImpl` applied to the signature body, the
public key and the BIP 143 model digest over the exact script code, hash
type and spent amount. -/
theorem txCheckerFor_some_ecdsa (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount)
    (sig pk scriptCode : ByteArray) (ed : Bitcoin.Crypto.Seam.ScriptExecutionData)
    (hpk : Bitcoin.Crypto.Seam.Der.isValidPubKey pk = true) (hne : 0 < sig.size) :
    (txCheckerFor tx nIn (some amount)).base.checkECDSASignature sig pk scriptCode
        .witnessV0 ed =
      Bitcoin.Crypto.Ecdsa.Verify.verifyImpl (sig.extract 0 (sig.size - 1)) pk
        (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn scriptCode
          (hashtypeOf sig) amount) := by
  rw [txCheckerFor_some_base_ecdsa_eq tx nIn amount]
  exact checker_consumes_model_digest Bitcoin.Crypto.Ecdsa.Verify.verifyImpl tx nIn amount
    sig pk scriptCode ed hpk hne

/-- Iff form of `txCheckerFor_some_ecdsa`: the vendor hypothesis used by the
revocation bridge is exactly the concrete verifier call. -/
theorem txCheckerFor_some_ecdsa_iff (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount)
    (sig pk scriptCode : ByteArray) (ed : Bitcoin.Crypto.Seam.ScriptExecutionData)
    (hpk : Bitcoin.Crypto.Seam.Der.isValidPubKey pk = true) (hne : 0 < sig.size) :
    ((txCheckerFor tx nIn (some amount)).base.checkECDSASignature sig pk scriptCode
        .witnessV0 ed = true) ↔
      Bitcoin.Crypto.Ecdsa.Verify.verifyImpl (sig.extract 0 (sig.size - 1)) pk
        (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn scriptCode
          (hashtypeOf sig) amount) = true := by
  rw [txCheckerFor_some_ecdsa tx nIn amount sig pk scriptCode ed hpk hne]

/-- **Missing-data fail-closed (SWT-055).**  With `amount = none` the
pipeline checker runs the ECDSA seam adapter with `hasAmount = false`, so
every witness-v0 ECDSA call is `false` *before* the signature or the sighash
is looked at.  This is the exact `-1`-amount sentinel behaviour. -/
theorem txCheckerFor_none_ecdsa_false (tx : Bitcoin.Data.Tx) (nIn : Nat)
    (sig pk scriptCode : ByteArray) (ed : Bitcoin.Crypto.Seam.ScriptExecutionData) :
    (txCheckerFor tx nIn none).base.checkECDSASignature sig pk scriptCode
        .witnessV0 ed = false := by
  simp only [txCheckerFor, Option.getD_none, Option.isSome_none,
    Bitcoin.Crypto.Seam.Entry.txCheckerOf, Bitcoin.Crypto.Seam.Entry.ecdsaVerdict]
  by_cases hpk : Bitcoin.Crypto.Seam.Der.isValidPubKey pk = true
  · by_cases hs : sig.size = 0
    · simp [hpk, hs]
    · simp [hpk, hs]
  · simp [hpk]

/-! ## 2. Positive revocation branch at `txCheckerFor` -/

/-- **Positive revocation branch.**  With a known amount, a 32-byte P2WSH
program committed by the `to_local` script, and a revocation-key signature
accepted by the concrete vendored verifier over the BIP 143 model digest,
the pipeline checker's `verifyWitnessProgram` returns `.ok` on the
revocation witness `[sig, 0x01, script]`. -/
theorem txCheckerFor_revocation_ok
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig program : ByteArray)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hpk : Bitcoin.Crypto.Seam.Der.isValidPubKey revocationKey.bytes = true)
    (hne : 0 < sig.size)
    (hsig : Bitcoin.Crypto.Ecdsa.Verify.verifyImpl (sig.extract 0 (sig.size - 1))
      revocationKey.bytes
      (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn
        (toLocalCode revocationKey delayedPaymentKey csv) (hashtypeOf sig) amount) = true)
    (hps : program.size = 32)
    (hprog : toLocalProgram revocationKey delayedPaymentKey csv = program) :
    verifyWitnessProgram 10 (revocationWitness revocationKey delayedPaymentKey csv sig) 0
        program toLocalFlags noPolicy (txCheckerFor tx nIn (some amount)) false = .ok := by
  have hsig' : (txCheckerFor tx nIn (some amount)).base.checkECDSASignature sig
      revocationKey.bytes (toLocalCode revocationKey delayedPaymentKey csv) .witnessV0
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true := by
    rw [txCheckerFor_some_ecdsa tx nIn amount sig revocationKey.bytes
      (toLocalCode revocationKey delayedPaymentKey csv)
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData) hpk hne]
    exact hsig
  exact verifyWitnessProgram_toLocal_revocation (txCheckerFor tx nIn (some amount))
    revocationKey delayedPaymentKey csv sig program hr hd hsigsz hsig' hps hprog

/-- **Positive branch, vendor and model together.**  The pipeline checker's
P2WSH verifier returns `.ok`, and the Wave-4 model's `P2WSHSpend` holds for
the same witness under `vendorLaws (txCheckerFor …)`.  The model message is
left explicit; instantiating it with the BIP 143 digest gives the
signature-level composition. -/
theorem txCheckerFor_revocation_agree
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig program : ByteArray) (msg : ByteArray)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hpk : Bitcoin.Crypto.Seam.Der.isValidPubKey revocationKey.bytes = true)
    (hne : 0 < sig.size)
    (hsig : Bitcoin.Crypto.Ecdsa.Verify.verifyImpl (sig.extract 0 (sig.size - 1))
      revocationKey.bytes
      (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn
        (toLocalCode revocationKey delayedPaymentKey csv) (hashtypeOf sig) amount) = true)
    (hps : program.size = 32)
    (hprog : toLocalProgram revocationKey delayedPaymentKey csv = program) :
    verifyWitnessProgram 10 (revocationWitness revocationKey delayedPaymentKey csv sig) 0
        program toLocalFlags noPolicy (txCheckerFor tx nIn (some amount)) false = .ok ∧
      P2WSHSpend (vendorLaws (txCheckerFor tx nIn (some amount))
          (toLocalCode revocationKey delayedPaymentKey csv))
        msg (toLocalProgram revocationKey delayedPaymentKey csv)
        (toLocalScriptFull revocationKey delayedPaymentKey csv).bytes
        (toLocalProg revocationKey delayedPaymentKey csv) [oneByte, sig] := by
  have hsig' : (txCheckerFor tx nIn (some amount)).base.checkECDSASignature sig
      revocationKey.bytes (toLocalCode revocationKey delayedPaymentKey csv) .witnessV0
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true := by
    rw [txCheckerFor_some_ecdsa tx nIn amount sig revocationKey.bytes
      (toLocalCode revocationKey delayedPaymentKey csv)
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData) hpk hne]
    exact hsig
  rw [← hprog]
  exact toLocal_revocation_interpreters_agree (txCheckerFor tx nIn (some amount)) msg
    revocationKey delayedPaymentKey csv sig hr hd hsigsz hsig'

/-- A rejected concrete verifier call makes the revocation witness fail with
`.fail .evalFalse` at the pipeline checker. -/
theorem txCheckerFor_revocation_bad_sig_fail
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig program : ByteArray)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hpk : Bitcoin.Crypto.Seam.Der.isValidPubKey revocationKey.bytes = true)
    (hne : 0 < sig.size)
    (hsig : Bitcoin.Crypto.Ecdsa.Verify.verifyImpl (sig.extract 0 (sig.size - 1))
      revocationKey.bytes
      (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn
        (toLocalCode revocationKey delayedPaymentKey csv) (hashtypeOf sig) amount) = false)
    (hps : program.size = 32)
    (hprog : toLocalProgram revocationKey delayedPaymentKey csv = program) :
    verifyWitnessProgram 10 (revocationWitness revocationKey delayedPaymentKey csv sig) 0
        program toLocalFlags noPolicy (txCheckerFor tx nIn (some amount)) false
      = .fail .evalFalse := by
  have hsig' : (txCheckerFor tx nIn (some amount)).base.checkECDSASignature sig
      revocationKey.bytes (toLocalCode revocationKey delayedPaymentKey csv) .witnessV0
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = false := by
    rw [txCheckerFor_some_ecdsa tx nIn amount sig revocationKey.bytes
      (toLocalCode revocationKey delayedPaymentKey csv)
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData) hpk hne]
    exact hsig
  exact verifyWitnessProgram_toLocal_revocation_bad_sig (txCheckerFor tx nIn (some amount))
    revocationKey delayedPaymentKey csv sig program hr hd hsigsz hsig' hps hprog

/-- **Exact revocation-branch characterization at `txCheckerFor`.**  The
pipeline P2WSH verdict on the revocation witness is `.ok` exactly when the
concrete vendored ECDSA verifier accepts the revocation-key signature over
the BIP 143 model digest.  No sequence/locktime condition appears: the
`OP_IF` branch never reads the environment. -/
theorem txCheckerFor_revocation_ok_iff
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig program : ByteArray)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hpk : Bitcoin.Crypto.Seam.Der.isValidPubKey revocationKey.bytes = true)
    (hne : 0 < sig.size)
    (hps : program.size = 32)
    (hprog : toLocalProgram revocationKey delayedPaymentKey csv = program) :
    verifyWitnessProgram 10 (revocationWitness revocationKey delayedPaymentKey csv sig) 0
        program toLocalFlags noPolicy (txCheckerFor tx nIn (some amount)) false = .ok ↔
      Bitcoin.Crypto.Ecdsa.Verify.verifyImpl (sig.extract 0 (sig.size - 1))
        revocationKey.bytes
        (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn
          (toLocalCode revocationKey delayedPaymentKey csv)
          (hashtypeOf sig) amount) = true := by
  constructor
  · intro hok
    by_cases hv : Bitcoin.Crypto.Ecdsa.Verify.verifyImpl (sig.extract 0 (sig.size - 1))
        revocationKey.bytes
        (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn
          (toLocalCode revocationKey delayedPaymentKey csv) (hashtypeOf sig) amount) = true
    · exact hv
    · have hfalse : Bitcoin.Crypto.Ecdsa.Verify.verifyImpl
          (sig.extract 0 (sig.size - 1)) revocationKey.bytes
          (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn
            (toLocalCode revocationKey delayedPaymentKey csv)
            (hashtypeOf sig) amount) = false := by
        cases hval : Bitcoin.Crypto.Ecdsa.Verify.verifyImpl
            (sig.extract 0 (sig.size - 1)) revocationKey.bytes
            (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn
              (toLocalCode revocationKey delayedPaymentKey csv)
              (hashtypeOf sig) amount) with
        | false => rfl
        | true => exact absurd hval hv
      have hfail := txCheckerFor_revocation_bad_sig_fail tx nIn amount revocationKey
        delayedPaymentKey csv sig program hr hd hsigsz hpk hne hfalse hps hprog
      rw [hfail] at hok
      exact absurd hok (by simp)
  · intro hv
    exact txCheckerFor_revocation_ok tx nIn amount revocationKey delayedPaymentKey csv
      sig program hr hd hsigsz hpk hne hv hps hprog

/-! ## 3. Wrong-key negatives at `txCheckerFor` -/

/-- **Wrong-key rejection (vendor and model).**  A signature the concrete
verifier rejects under the revocation key makes the pipeline P2WSH verifier
return `.fail .evalFalse`, and the model `Accepts` predicate is false. -/
theorem txCheckerFor_revocation_wrong_key_rejected
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig program : ByteArray) (msg : ByteArray)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hpk : Bitcoin.Crypto.Seam.Der.isValidPubKey revocationKey.bytes = true)
    (hne : 0 < sig.size)
    (hsig : Bitcoin.Crypto.Ecdsa.Verify.verifyImpl (sig.extract 0 (sig.size - 1))
      revocationKey.bytes
      (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn
        (toLocalCode revocationKey delayedPaymentKey csv) (hashtypeOf sig) amount) = false)
    (hps : program.size = 32)
    (hprog : toLocalProgram revocationKey delayedPaymentKey csv = program) :
    verifyWitnessProgram 10 (revocationWitness revocationKey delayedPaymentKey csv sig) 0
        program toLocalFlags noPolicy (txCheckerFor tx nIn (some amount)) false
      = .fail .evalFalse ∧
      ¬ Accepts (vendorLaws (txCheckerFor tx nIn (some amount))
          (toLocalCode revocationKey delayedPaymentKey csv))
        msg (toLocalProg revocationKey delayedPaymentKey csv) [oneByte, sig] := by
  have hsig' : (txCheckerFor tx nIn (some amount)).base.checkECDSASignature sig
      revocationKey.bytes (toLocalCode revocationKey delayedPaymentKey csv) .witnessV0
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = false := by
    rw [txCheckerFor_some_ecdsa tx nIn amount sig revocationKey.bytes
      (toLocalCode revocationKey delayedPaymentKey csv)
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData) hpk hne]
    exact hsig
  rw [← hprog]
  exact toLocal_revocation_wrong_key_rejected (txCheckerFor tx nIn (some amount)) msg
    revocationKey delayedPaymentKey csv sig hr hd hsigsz hsig'

/-- **ECDSA key separation** (the explicit `CR-01` hypothesis).  Every
signature body the vendored verifier accepts under `accepted` is rejected
under `rejected`.  This is what secp256k1 key separation gives except with
negligible probability; it is not proved in this tree. -/
def EcdsaKeySeparated (verify : ByteArray → ByteArray → ByteArray → Bool)
    (accepted rejected : PubKey) : Prop :=
  ∀ (body digest : ByteArray),
    verify body accepted.bytes digest = true → verify body rejected.bytes digest = false

/-- **Wrong-key in the Lightning sense.**  If the verifier accepts the
signature under `local_delayedpubkey` and the two keys are separated, then
the same signature is rejected on the revocation branch: the pipeline P2WSH
verifier returns `.fail .evalFalse` and the model does not accept.  The
selector `0x01` alone does not move the output. -/
theorem txCheckerFor_revocation_delayed_key_sig_rejected
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig program : ByteArray) (msg : ByteArray)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hpk : Bitcoin.Crypto.Seam.Der.isValidPubKey revocationKey.bytes = true)
    (hne : 0 < sig.size)
    (hsep : EcdsaKeySeparated Bitcoin.Crypto.Ecdsa.Verify.verifyImpl
      delayedPaymentKey revocationKey)
    (hsigdel : Bitcoin.Crypto.Ecdsa.Verify.verifyImpl (sig.extract 0 (sig.size - 1))
      delayedPaymentKey.bytes
      (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn
        (toLocalCode revocationKey delayedPaymentKey csv) (hashtypeOf sig) amount) = true)
    (hps : program.size = 32)
    (hprog : toLocalProgram revocationKey delayedPaymentKey csv = program) :
    verifyWitnessProgram 10 (revocationWitness revocationKey delayedPaymentKey csv sig) 0
        program toLocalFlags noPolicy (txCheckerFor tx nIn (some amount)) false
      = .fail .evalFalse ∧
      ¬ Accepts (vendorLaws (txCheckerFor tx nIn (some amount))
          (toLocalCode revocationKey delayedPaymentKey csv))
        msg (toLocalProg revocationKey delayedPaymentKey csv) [oneByte, sig] := by
  have hrev : Bitcoin.Crypto.Ecdsa.Verify.verifyImpl (sig.extract 0 (sig.size - 1))
      revocationKey.bytes
      (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn
        (toLocalCode revocationKey delayedPaymentKey csv) (hashtypeOf sig) amount) = false :=
    hsep _ _ hsigdel
  exact txCheckerFor_revocation_wrong_key_rejected tx nIn amount revocationKey
    delayedPaymentKey csv sig program msg hr hd hsigsz hpk hne hrev hps hprog

/-- **Missing-data negative at `txCheckerFor`.**  With `amount = none` the
witness-v0 ECDSA entry fails closed, so the revocation witness fails with
`.fail .evalFalse` regardless of the signature.  The amount premise is not
optional: on witness-v0 P2WSH the pipeline cannot verify without it. -/
theorem txCheckerFor_none_revocation_fail
    (tx : Bitcoin.Data.Tx) (nIn : Nat)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig program : ByteArray)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hps : program.size = 32)
    (hprog : toLocalProgram revocationKey delayedPaymentKey csv = program) :
    verifyWitnessProgram 10 (revocationWitness revocationKey delayedPaymentKey csv sig) 0
        program toLocalFlags noPolicy (txCheckerFor tx nIn none) false
      = .fail .evalFalse := by
  have hsig' : (txCheckerFor tx nIn none).base.checkECDSASignature sig
      revocationKey.bytes (toLocalCode revocationKey delayedPaymentKey csv) .witnessV0
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = false :=
    txCheckerFor_none_ecdsa_false tx nIn sig revocationKey.bytes
      (toLocalCode revocationKey delayedPaymentKey csv)
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData)
  exact verifyWitnessProgram_toLocal_revocation_bad_sig (txCheckerFor tx nIn none)
    revocationKey delayedPaymentKey csv sig program hr hd hsigsz hsig' hps hprog

/-! ## 4. Wrong-branch negatives: the empty selector -/

/-- **The pipeline sequence check, characterized exactly.**  At
`txCheckerFor` the vendored `checkSequenceDef` reads the transaction version
and the signing input's sequence; for `csv < 32768` it accepts exactly the
BIP 68/112 context (version ≥ 2, input disable bit clear, height domain,
`csv ≤` masked input sequence). -/
theorem txCheckerFor_checkSequenceDef_iff (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount)
    (csv : Blocks) (hcsv : csv < 32768) :
    checkSequenceDef (txCheckerFor tx nIn (some amount)).env (csv : Int) = true ↔
      ((¬ tx.version < 2) ∧
        (((tx.vin.getD nIn fullDummyTxIn).sequence.toNat &&&
            SEQUENCE_LOCKTIME_DISABLE_FLAG) = 0) ∧
        (((tx.vin.getD nIn fullDummyTxIn).sequence.toNat &&&
            (SEQUENCE_LOCKTIME_TYPE_FLAG ||| SEQUENCE_LOCKTIME_MASK)) <
          SEQUENCE_LOCKTIME_TYPE_FLAG) ∧
        csv ≤ ((tx.vin.getD nIn fullDummyTxIn).sequence.toNat &&&
            (SEQUENCE_LOCKTIME_TYPE_FLAG ||| SEQUENCE_LOCKTIME_MASK))) := by
  simpa [txCheckerFor, fullDummyTxIn] using
    checkSequenceDef_delay_iff (txCheckerFor tx nIn (some amount)).env csv hcsv

/-- A concrete BIP 68/112 context failure makes the vendored sequence check
false. -/
theorem checkSequenceDef_delay_false_of_cases (env : LocktimeEnv) (csv : Nat)
    (hcsv : csv < 32768)
    (h : env.txVersion < 2 ∨
      (env.txSequence.toNat &&& SEQUENCE_LOCKTIME_DISABLE_FLAG) ≠ 0 ∨
      (env.txSequence.toNat &&&
          (SEQUENCE_LOCKTIME_TYPE_FLAG ||| SEQUENCE_LOCKTIME_MASK)) ≥
        SEQUENCE_LOCKTIME_TYPE_FLAG ∨
      (env.txSequence.toNat &&&
          (SEQUENCE_LOCKTIME_TYPE_FLAG ||| SEQUENCE_LOCKTIME_MASK)) < csv) :
    checkSequenceDef env (csv : Int) = false := by
  have hiff := checkSequenceDef_delay_iff env csv hcsv
  cases hval : checkSequenceDef env (csv : Int) with
  | false => rfl
  | true =>
      have P := hiff.mp hval
      exfalso
      rcases h with hver | hdis | hdom | hlt
      · exact P.1 hver
      · exact hdis P.2.1
      · exact absurd P.2.2.1 (by omega)
      · exact absurd P.2.2.2 (by omega)

/-- The same failure at `txCheckerFor`: an explicit version/disable-bit/
domain/delay failure implies the pipeline checker's sequence check is false. -/
theorem txCheckerFor_checkSequenceDef_false (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount)
    (csv : Blocks) (hcsv : csv < 32768)
    (h : tx.version < 2 ∨
      (((tx.vin.getD nIn fullDummyTxIn).sequence.toNat &&&
          SEQUENCE_LOCKTIME_DISABLE_FLAG) ≠ 0) ∨
      (((tx.vin.getD nIn fullDummyTxIn).sequence.toNat &&&
          (SEQUENCE_LOCKTIME_TYPE_FLAG ||| SEQUENCE_LOCKTIME_MASK)) ≥
        SEQUENCE_LOCKTIME_TYPE_FLAG) ∨
      (((tx.vin.getD nIn fullDummyTxIn).sequence.toNat &&&
          (SEQUENCE_LOCKTIME_TYPE_FLAG ||| SEQUENCE_LOCKTIME_MASK)) < csv)) :
    checkSequenceDef (txCheckerFor tx nIn (some amount)).env (csv : Int) = false := by
  refine checkSequenceDef_delay_false_of_cases
    (txCheckerFor tx nIn (some amount)).env csv hcsv ?_
  simpa [txCheckerFor, fullDummyTxIn] using h

/-- **Wrong-branch negative: failed sequence context.**  With the empty
selector the pipeline executes the `OP_ELSE` delayed block; when the
BIP 68/112 context fails, execution stops at `OP_CSV` with
`.unsatisfiedLocktime`, even if the witness carries a valid revocation-key
signature. -/
theorem txCheckerFor_delayed_csv_false
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig program : ByteArray) (hcsv : csv < 32768)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hfail : tx.version < 2 ∨
      (((tx.vin.getD nIn fullDummyTxIn).sequence.toNat &&&
          SEQUENCE_LOCKTIME_DISABLE_FLAG) ≠ 0) ∨
      (((tx.vin.getD nIn fullDummyTxIn).sequence.toNat &&&
          (SEQUENCE_LOCKTIME_TYPE_FLAG ||| SEQUENCE_LOCKTIME_MASK)) ≥
        SEQUENCE_LOCKTIME_TYPE_FLAG) ∨
      (((tx.vin.getD nIn fullDummyTxIn).sequence.toNat &&&
          (SEQUENCE_LOCKTIME_TYPE_FLAG ||| SEQUENCE_LOCKTIME_MASK)) < csv))
    (hps : program.size = 32)
    (hprog : toLocalProgram revocationKey delayedPaymentKey csv = program) :
    verifyWitnessProgram 10 (delayedWitness revocationKey delayedPaymentKey csv sig) 0
        program toLocalFlags noPolicy (txCheckerFor tx nIn (some amount)) false
      = .fail .unsatisfiedLocktime := by
  have hseq := txCheckerFor_checkSequenceDef_false tx nIn amount csv hcsv hfail
  exact verifyWitnessProgram_toLocal_delayed_csv_false (txCheckerFor tx nIn (some amount))
    revocationKey delayedPaymentKey csv sig (csv : Int) program hr hd hsigsz
    (decodeNum_delayBytes csv hcsv) (nonneg_delay csv) (disableBit_delay csv hcsv)
    hseq hps hprog

/-- **Exact delayed-branch characterization at `txCheckerFor`.**  With a
valid sequence context, the empty-selector delayed witness is `.ok` exactly
when the concrete vendored verifier accepts the `local_delayedpubkey`
signature over the BIP 143 model digest.  The context conjuncts are the
BIP 68/112 conditions, not an abstract sequence-check hypothesis. -/
theorem txCheckerFor_delayed_ok_iff
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig program : ByteArray) (hcsv : csv < 32768)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hpk : Bitcoin.Crypto.Seam.Der.isValidPubKey delayedPaymentKey.bytes = true)
    (hne : 0 < sig.size)
    (hps : program.size = 32)
    (hprog : toLocalProgram revocationKey delayedPaymentKey csv = program) :
    verifyWitnessProgram 10 (delayedWitness revocationKey delayedPaymentKey csv sig) 0
        program toLocalFlags noPolicy (txCheckerFor tx nIn (some amount)) false = .ok ↔
      ((¬ tx.version < 2) ∧
        (((tx.vin.getD nIn fullDummyTxIn).sequence.toNat &&&
            SEQUENCE_LOCKTIME_DISABLE_FLAG) = 0) ∧
        (((tx.vin.getD nIn fullDummyTxIn).sequence.toNat &&&
            (SEQUENCE_LOCKTIME_TYPE_FLAG ||| SEQUENCE_LOCKTIME_MASK)) <
          SEQUENCE_LOCKTIME_TYPE_FLAG) ∧
        csv ≤ ((tx.vin.getD nIn fullDummyTxIn).sequence.toNat &&&
            (SEQUENCE_LOCKTIME_TYPE_FLAG ||| SEQUENCE_LOCKTIME_MASK)) ∧
        Bitcoin.Crypto.Ecdsa.Verify.verifyImpl (sig.extract 0 (sig.size - 1))
          delayedPaymentKey.bytes
          (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn
            (toLocalCode revocationKey delayedPaymentKey csv)
            (hashtypeOf sig) amount) = true) := by
  rw [toLocal_delayed_sequence_context_refinement (txCheckerFor tx nIn (some amount))
    revocationKey delayedPaymentKey csv sig program hcsv hr hd hsigsz hps hprog]
  rw [txCheckerFor_some_ecdsa_iff tx nIn amount sig delayedPaymentKey.bytes
    (toLocalCode revocationKey delayedPaymentKey csv)
    (default : Bitcoin.Crypto.Seam.ScriptExecutionData) hpk hne]
  simp only [txCheckerFor_some_env_txVersion, txCheckerFor_some_env_txSequence]

/-- **Wrong-branch negative: the revocation key on the delayed branch.**
With a valid BIP 68/112 context and separated keys, a signature accepted
under the revocation key is rejected under `local_delayedpubkey`, so the
empty-selector witness fails with `.fail .evalFalse`.  The revocation key
cannot take the delayed path. -/
theorem txCheckerFor_delayed_revocation_key_sig_rejected
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig program : ByteArray) (hcsv : csv < 32768)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hpk : Bitcoin.Crypto.Seam.Der.isValidPubKey delayedPaymentKey.bytes = true)
    (hne : 0 < sig.size)
    (hctx : (¬ tx.version < 2) ∧
      (((tx.vin.getD nIn fullDummyTxIn).sequence.toNat &&&
          SEQUENCE_LOCKTIME_DISABLE_FLAG) = 0) ∧
      (((tx.vin.getD nIn fullDummyTxIn).sequence.toNat &&&
          (SEQUENCE_LOCKTIME_TYPE_FLAG ||| SEQUENCE_LOCKTIME_MASK)) <
        SEQUENCE_LOCKTIME_TYPE_FLAG) ∧
      csv ≤ ((tx.vin.getD nIn fullDummyTxIn).sequence.toNat &&&
          (SEQUENCE_LOCKTIME_TYPE_FLAG ||| SEQUENCE_LOCKTIME_MASK)))
    (hsep : EcdsaKeySeparated Bitcoin.Crypto.Ecdsa.Verify.verifyImpl
      revocationKey delayedPaymentKey)
    (hsigrev : Bitcoin.Crypto.Ecdsa.Verify.verifyImpl (sig.extract 0 (sig.size - 1))
      revocationKey.bytes
      (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn
        (toLocalCode revocationKey delayedPaymentKey csv) (hashtypeOf sig) amount) = true)
    (hps : program.size = 32)
    (hprog : toLocalProgram revocationKey delayedPaymentKey csv = program) :
    verifyWitnessProgram 10 (delayedWitness revocationKey delayedPaymentKey csv sig) 0
        program toLocalFlags noPolicy (txCheckerFor tx nIn (some amount)) false
      = .fail .evalFalse := by
  have hseq : checkSequenceDef (txCheckerFor tx nIn (some amount)).env (csv : Int)
      = true := by
    rw [txCheckerFor_checkSequenceDef_iff tx nIn amount csv hcsv]
    exact hctx
  have hdel : (txCheckerFor tx nIn (some amount)).base.checkECDSASignature sig
      delayedPaymentKey.bytes (toLocalCode revocationKey delayedPaymentKey csv) .witnessV0
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = false := by
    rw [txCheckerFor_some_ecdsa tx nIn amount sig delayedPaymentKey.bytes
      (toLocalCode revocationKey delayedPaymentKey csv)
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData) hpk hne]
    exact hsep _ _ hsigrev
  exact verifyWitnessProgram_toLocal_delayed_bad_sig (txCheckerFor tx nIn (some amount))
    revocationKey delayedPaymentKey csv sig (csv : Int) program hr hd hsigsz
    (decodeNum_delayBytes csv hcsv) (nonneg_delay csv) (disableBit_delay csv hcsv)
    hseq hdel hps hprog

/-! ## 5. Selector-level branch selection at `txCheckerFor` -/

/-- **Branch selection.**  For one `to_local` script, one signature accepted
under the revocation key, and a failing BIP 68/112 sequence context, the
0x01 selector yields vendor `.ok` on the revocation branch while the empty
selector yields `.fail .unsatisfiedLocktime` on the delayed branch.  The two
witnesses differ only in the selector item. -/
theorem txCheckerFor_toLocal_branch_selection
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig program : ByteArray) (hcsv : csv < 32768)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hpk : Bitcoin.Crypto.Seam.Der.isValidPubKey revocationKey.bytes = true)
    (hne : 0 < sig.size)
    (hsig : Bitcoin.Crypto.Ecdsa.Verify.verifyImpl (sig.extract 0 (sig.size - 1))
      revocationKey.bytes
      (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn
        (toLocalCode revocationKey delayedPaymentKey csv) (hashtypeOf sig) amount) = true)
    (hfail : tx.version < 2 ∨
      (((tx.vin.getD nIn fullDummyTxIn).sequence.toNat &&&
          SEQUENCE_LOCKTIME_DISABLE_FLAG) ≠ 0) ∨
      (((tx.vin.getD nIn fullDummyTxIn).sequence.toNat &&&
          (SEQUENCE_LOCKTIME_TYPE_FLAG ||| SEQUENCE_LOCKTIME_MASK)) ≥
        SEQUENCE_LOCKTIME_TYPE_FLAG) ∨
      (((tx.vin.getD nIn fullDummyTxIn).sequence.toNat &&&
          (SEQUENCE_LOCKTIME_TYPE_FLAG ||| SEQUENCE_LOCKTIME_MASK)) < csv))
    (hps : program.size = 32)
    (hprog : toLocalProgram revocationKey delayedPaymentKey csv = program) :
    verifyWitnessProgram 10 (revocationWitness revocationKey delayedPaymentKey csv sig) 0
        program toLocalFlags noPolicy (txCheckerFor tx nIn (some amount)) false = .ok ∧
      verifyWitnessProgram 10 (delayedWitness revocationKey delayedPaymentKey csv sig) 0
        program toLocalFlags noPolicy (txCheckerFor tx nIn (some amount)) false
        = .fail .unsatisfiedLocktime :=
  ⟨txCheckerFor_revocation_ok tx nIn amount revocationKey delayedPaymentKey csv sig
      program hr hd hsigsz hpk hne hsig hps hprog,
    txCheckerFor_delayed_csv_false tx nIn amount revocationKey delayedPaymentKey csv sig
      program hcsv hr hd hsigsz hfail hps hprog⟩

/-! ## 6. Summary at the pipeline boundary

The four results a downstream (`H04`) lane needs are:

* `txCheckerFor_some_ecdsa` / `txCheckerFor_some_ecdsa_iff` — the concrete
  vendored verifier behind the pipeline checker (amount known, pubkey valid,
  signature non-empty);
* `txCheckerFor_revocation_ok` / `txCheckerFor_revocation_ok_iff` — the
  positive revocation branch and its exact verifier-valued criterion;
* `txCheckerFor_revocation_wrong_key_rejected` /
  `txCheckerFor_revocation_delayed_key_sig_rejected` — the wrong-key
  negatives (rejected call, and delayed-key signature on the revocation
  branch under `EcdsaKeySeparated`);
* `txCheckerFor_delayed_csv_false` / `txCheckerFor_delayed_ok_iff` /
  `txCheckerFor_delayed_revocation_key_sig_rejected` — the wrong-branch
  negatives (failed sequence context, delayed branch criterion, revocation
  key on the delayed branch).

The remaining premises are explicit and unavoidable: `some amount` (or the
`none` fail-closed theorem), a 32-byte P2WSH program equal to
`hashSha256` of the `to_local` script, the CSV-enabled consensus flag word
with the empty policy word, a valid compressed-pubkey header, a non-empty
at-most-520-byte signature, and — for the Lightning wrong-key theorems —
the ECDSA key-separation hypothesis `EcdsaKeySeparated`.
-/

end LnLean.Proofs.WaveH.H32
