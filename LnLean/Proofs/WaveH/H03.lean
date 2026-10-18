import Bitcoin.TxValidation.Full
import LnLean.Proofs.Bitcoin.SequenceContextTargets

/-!
# H03 — revocation-branch verdicts at the full-checker boundary (`L1-02`, `L1-07`)

Wave 6 (`S6-L1-REVOKE`, `InterpreterRevocationTargets`) mechanized the
`to_local` revocation branch at the vendored `verifyWitnessProgram` with an
arbitrary `ScriptChecker`.  Wave 7 (`S7-L1-SEQUENCE`,
`SequenceContextTargets`) transferred the *delayed* branch to
`Bitcoin.Capstone.RealChecker.realCheckerOf` and to the concrete checker
`checkerOf Bitcoin.Crypto.Ecdsa.Verify.verifyImpl`.  The remaining transfer
recorded in `docs/OPEN-ISSUES.md` (`L1-02`/`L1-07`) is to the **full
transaction checker** of `Bitcoin.TxValidation.Full`:

```text
txCheckerFor tx nIn (some amount)
```

which is the checker the full `scriptLane`/`txVerdictFull` pipeline actually
hands to `verifyScriptFull`.

This module supplies:

* `txCheckerFor_some_eq_realCheckerOf` and
  `txCheckerFor_some_eq_checkerOf`: for `some amount` the full checker is
  literally the capstone real checker, and (for an in-range input) the
  model-digest checker used by the wave-6/7 refinements.
* `txCheckerFor_env_eq_locktimeEnvOf`: the locktime environment of the full
  checker is the transaction-derived environment for `nIn < tx.vin.length`.
* the **positive** revocation-branch theorem at `txCheckerFor`, in three
  forms: the vendored P2WSH verdict (`= .ok`), the joint vendor/model
  agreement (`verifyWitnessProgram = .ok ∧ P2WSHSpend ...`), and the concrete
  refinement where the opaque ECDSA hypothesis becomes a
  `Bitcoin.Crypto.Ecdsa.Verify.verifyImpl` call over the BIP 143 model digest
  `LnLean.Bitcoin.Sighash.sighashWitnessV0`.
* the **wrong-key negatives** at `txCheckerFor`: a rejected revocation-key
  check gives `.fail .evalFalse` and model non-acceptance; the
  delayed-key-signature case is derived from the explicit
  `RevocationKeySeparated` hypothesis; the concrete `verifyImpl = false` form
  is also given.
* the **wrong-branch negatives** at `txCheckerFor`: the empty selector takes
  the delayed branch, and a failing BIP 68/112 sequence check yields
  `.fail .unsatisfiedLocktime` even when the witness carries a valid
  revocation-key signature.  The decode/non-negativity/disable-bit premises
  are discharged from the faithful fixed-width encoding by `csv < 32768`.
* `toLocal_vendor_branch_selection_txCheckerFor`: with one witness script and
  one valid revocation-key signature, the selector alone selects between
  `.ok` (revocation) and `.fail .unsatisfiedLocktime` (delayed, failing
  sequence).

Scope, unchanged from the wave-6/7 bridges: the signature hypothesis is a
vendored EC verdict (assumption C3 in `docs/ASSUMPTIONS.md`), not a
cryptographic proof; the BIP 143 digest is constructed, but the spent amount,
the transaction and the flag/policy words are explicit inputs; the result is
one-directional (acceptance/rejection consequences), not an iff over all
consensus failure modes; the pipeline level `scriptLaneTx`/`txVerdictFull`
transfer is lane H04.
-/

namespace LnLean.Proofs.WaveH.H03

set_option autoImplicit false

open Bitcoin.Data
open Bitcoin.Activation
open Bitcoin.Script.Parser
open Bitcoin.Interpreter
open Bitcoin.Crypto.Seam
open Bitcoin.TxValidation.Full
open LnLean
open LnLean.Bitcoin
open LnLean.Proofs.Bitcoin.SpendTargets
open LnLean.Proofs.Bitcoin.InterpreterBridgeTargets
open LnLean.Proofs.Bitcoin.InterpreterRevocationTargets
open LnLean.Proofs.Bitcoin.SequenceContextTargets
open LnLean.Proofs.Bitcoin.SighashBridgeTargets

/-! ## 1. The full checker and the capstone/model checkers -/

/-- **`some amount` has the capstone real ECDSA entry.**  `txCheckerFor`
assembles the same real ECDSA entry, the same sighash dispatch and the same
transaction-derived environment as `RealChecker.realCheckerOf`; the `Option
Amount` wrappers reduce definitionally on `some amount`.  The Schnorr entry
differs (the capstone `realCheckerOf` carries the fail-closed stub, while
`txCheckerFor` carries the real BIP 340 verifier), so the full checkers are
not equal; everything in this module uses only the ECDSA entry and the
environment, and those agree pointwise. -/
theorem txCheckerFor_some_checkECDSA_eq_realCheckerOf
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount)
    (sig pk code : ByteArray) (sv : SigVersion)
    (ed : Bitcoin.Crypto.Seam.ScriptExecutionData) :
    (txCheckerFor tx nIn (some amount)).base.checkECDSASignature
        sig pk code sv ed =
      (Bitcoin.Capstone.RealChecker.realCheckerOf tx nIn amount).base.checkECDSASignature
        sig pk code sv ed := rfl

/-- The full checker and `realCheckerOf` have the same locktime environment
(for `some amount`), definitionally. -/
theorem txCheckerFor_some_env_eq_realCheckerOf
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount) :
    (txCheckerFor tx nIn (some amount)).env =
      (Bitcoin.Capstone.RealChecker.realCheckerOf tx nIn amount).env := rfl

/-- **`some amount` has the model-digest ECDSA entry**, for an in-range input.
This composes the pointwise capstone equality with the wave-7
`checkerOf_eq_realCheckerOf`; it is the bridge that exposes the BIP 143
model digest `sighashWitnessV0` behind the full checker. -/
theorem txCheckerFor_some_checkECDSA_eq_checkerOf
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount)
    (hIn : nIn < tx.vin.length)
    (sig pk code : ByteArray) (sv : SigVersion)
    (ed : Bitcoin.Crypto.Seam.ScriptExecutionData) :
    (txCheckerFor tx nIn (some amount)).base.checkECDSASignature
        sig pk code sv ed =
      (checkerOf Bitcoin.Crypto.Ecdsa.Verify.verifyImpl tx nIn amount).base.checkECDSASignature
        sig pk code sv ed := by
  rw [txCheckerFor_some_checkECDSA_eq_realCheckerOf,
    ← checkerOf_eq_realCheckerOf tx nIn amount hIn]

/-- **The full checker's locktime environment is the transaction
environment.**  For an in-range input both `getD` totalizations reduce to the
actual input's `nSequence`, so the environment of `txCheckerFor` is exactly
`locktimeEnvOf tx nIn`. -/
theorem txCheckerFor_env_eq_locktimeEnvOf (tx : Bitcoin.Data.Tx) (nIn : Nat)
    (amount : Amount) (hIn : nIn < tx.vin.length) :
    (txCheckerFor tx nIn (some amount)).env = locktimeEnvOf tx nIn := by
  simp [txCheckerFor, locktimeEnvOf, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hIn]

/-! ## 2. Positive revocation branch at `txCheckerFor` -/

/-- **Vendored acceptance of the revocation branch at the full checker.**
The witness `[sig, 0x01, witnessScript]` spends the P2WSH output whose
program is `hashSha256 witnessScript`; the vendored verifier accepts exactly
when the full checker's revocation-key ECDSA call succeeds.  No sequence,
locktime or policy premise appears: the `OP_IF` true branch never reads the
environment. -/
theorem verifyWitnessProgram_toLocal_revocation_txCheckerFor
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig program : ByteArray)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hsig : (txCheckerFor tx nIn (some amount)).base.checkECDSASignature
      sig revocationKey.bytes
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      .witnessV0 (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true)
    (hps : program.size = 32)
    (hprog : hashSha256
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)) = program) :
    verifyWitnessProgram 10
      [sig, revocationSelector,
        serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)]
      0 program ({ csv := true } : ScriptFlags) ({} : PolicyFlags)
      (txCheckerFor tx nIn (some amount)) false = .ok :=
  verifyWitnessProgram_toLocal_revocation
    (txCheckerFor tx nIn (some amount)) revocationKey delayedPaymentKey csv
    sig program hr hd hsigsz hsig hps hprog

/-- **Joint vendor/model acceptance at the full checker.**  The vendored
P2WSH verifier returns `.ok`, and the wave-4 model's `P2WSHSpend` holds with
the full checker's signature law.  The model digest is supplied as the
`msg` parameter; `vendorLaws` ignores it (the vendored checker constructs its
own BIP 143 digest). -/
theorem toLocal_revocation_txCheckerFor_agree
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hsig : (txCheckerFor tx nIn (some amount)).base.checkECDSASignature
      sig revocationKey.bytes
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      .witnessV0 (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true) :
    verifyWitnessProgram 10
        [sig, revocationSelector,
          serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)]
        0
        (hashSha256
          (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)))
        ({ csv := true } : ScriptFlags) ({} : PolicyFlags)
        (txCheckerFor tx nIn (some amount)) false = .ok ∧
      P2WSHSpend (vendorLaws (txCheckerFor tx nIn (some amount))
          (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)))
        (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn
          (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
          (hashtypeOf sig) amount)
        (hashSha256
          (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)))
        (toLocalScriptFull revocationKey delayedPaymentKey csv).bytes
        (toLocalProg revocationKey delayedPaymentKey csv) [oneByte, sig] :=
  toLocal_revocation_interpreters_agree
    (txCheckerFor tx nIn (some amount))
    (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      (hashtypeOf sig) amount)
    revocationKey delayedPaymentKey csv sig hr hd hsigsz hsig

/-- **Concrete revocation refinement at the full checker.**  The opaque
`checkECDSASignature` hypothesis is replaced by the explicit lax secp256k1
verifier `verifyImpl` over the BIP 143 model digest.  The pubkey-validity and
non-empty-signature hypotheses are exactly those needed by the vendored seam
adapter; `nIn < tx.vin.length` identifies the full checker with the
model-digest checker (`txCheckerFor_some_eq_checkerOf`). -/
theorem verifyWitnessProgram_toLocal_revocation_txCheckerFor_verifyImpl
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount)
    (hIn : nIn < tx.vin.length)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig program : ByteArray)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hpk : Bitcoin.Crypto.Seam.Der.isValidPubKey revocationKey.bytes = true)
    (hne : 0 < sig.size)
    (hsig : Bitcoin.Crypto.Ecdsa.Verify.verifyImpl
      (sig.extract 0 (sig.size - 1)) revocationKey.bytes
      (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn
        (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
        (hashtypeOf sig) amount) = true)
    (hps : program.size = 32)
    (hprog : hashSha256
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)) = program) :
    verifyWitnessProgram 10
      [sig, revocationSelector,
        serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)]
      0 program ({ csv := true } : ScriptFlags) ({} : PolicyFlags)
      (txCheckerFor tx nIn (some amount)) false = .ok := by
  refine verifyWitnessProgram_toLocal_revocation
    (txCheckerFor tx nIn (some amount))
    revocationKey delayedPaymentKey csv sig program hr hd hsigsz ?_ hps hprog
  rw [txCheckerFor_some_checkECDSA_eq_checkerOf tx nIn amount hIn]
  exact (bridge_ecdsa_hypothesis_iff_model_verify
    Bitcoin.Crypto.Ecdsa.Verify.verifyImpl tx nIn amount sig
    revocationKey.bytes
    (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
    (default : Bitcoin.Crypto.Seam.ScriptExecutionData) hpk hne).mpr hsig

/-! ## 3. Wrong-key negatives at `txCheckerFor` -/

/-- **A rejected revocation-key check fails the branch at the full checker.**
The vendored branch pushes the canonical `false`, and the P2WSH truthiness
test returns `.fail .evalFalse`. -/
theorem verifyWitnessProgram_toLocal_revocation_bad_sig_txCheckerFor
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig program : ByteArray)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hsig : (txCheckerFor tx nIn (some amount)).base.checkECDSASignature
      sig revocationKey.bytes
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      .witnessV0 (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = false)
    (hps : program.size = 32)
    (hprog : hashSha256
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)) = program) :
    verifyWitnessProgram 10
      [sig, revocationSelector,
        serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)]
      0 program ({ csv := true } : ScriptFlags) ({} : PolicyFlags)
      (txCheckerFor tx nIn (some amount)) false = .fail .evalFalse :=
  verifyWitnessProgram_toLocal_revocation_bad_sig
    (txCheckerFor tx nIn (some amount)) revocationKey delayedPaymentKey csv
    sig program hr hd hsigsz hsig hps hprog

/-- **Concrete wrong-key rejection at the full checker**: an explicit
`verifyImpl` rejection over the BIP 143 model digest produces `.fail
.evalFalse`. -/
theorem verifyWitnessProgram_toLocal_revocation_bad_sig_txCheckerFor_verifyImpl
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount)
    (hIn : nIn < tx.vin.length)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig program : ByteArray)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hpk : Bitcoin.Crypto.Seam.Der.isValidPubKey revocationKey.bytes = true)
    (hne : 0 < sig.size)
    (hsig : Bitcoin.Crypto.Ecdsa.Verify.verifyImpl
      (sig.extract 0 (sig.size - 1)) revocationKey.bytes
      (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn
        (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
        (hashtypeOf sig) amount) = false)
    (hps : program.size = 32)
    (hprog : hashSha256
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)) = program) :
    verifyWitnessProgram 10
      [sig, revocationSelector,
        serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)]
      0 program ({ csv := true } : ScriptFlags) ({} : PolicyFlags)
      (txCheckerFor tx nIn (some amount)) false = .fail .evalFalse := by
  have hiff := bridge_ecdsa_hypothesis_iff_model_verify
    Bitcoin.Crypto.Ecdsa.Verify.verifyImpl tx nIn amount sig
    revocationKey.bytes
    (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
    (default : Bitcoin.Crypto.Seam.ScriptExecutionData) hpk hne
  have hchk0 : (checkerOf Bitcoin.Crypto.Ecdsa.Verify.verifyImpl tx nIn amount).base.checkECDSASignature
      sig revocationKey.bytes
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      .witnessV0 (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = false := by
    cases h : (checkerOf Bitcoin.Crypto.Ecdsa.Verify.verifyImpl tx nIn amount).base.checkECDSASignature
        sig revocationKey.bytes
        (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
        .witnessV0 (default : Bitcoin.Crypto.Seam.ScriptExecutionData) with
    | false => rfl
    | true =>
        rw [hiff.mp h] at hsig
        exact absurd hsig (by decide)
  have hchk : (txCheckerFor tx nIn (some amount)).base.checkECDSASignature
      sig revocationKey.bytes
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      .witnessV0 (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = false := by
    rw [txCheckerFor_some_checkECDSA_eq_checkerOf tx nIn amount hIn]
    exact hchk0
  exact verifyWitnessProgram_toLocal_revocation_bad_sig
    (txCheckerFor tx nIn (some amount))
    revocationKey delayedPaymentKey csv sig program hr hd hsigsz hchk hps hprog

/-- **Joint wrong-key rejection at the full checker**: the vendored verifier
returns `.fail .evalFalse` and the model does not accept, under the same
rejected revocation-key check. -/
theorem toLocal_revocation_wrong_key_rejected_txCheckerFor
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (msg : ByteArray)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hsig : (txCheckerFor tx nIn (some amount)).base.checkECDSASignature
      sig revocationKey.bytes
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      .witnessV0 (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = false) :
    verifyWitnessProgram 10
        [sig, revocationSelector,
          serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)]
        0
        (hashSha256
          (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)))
        ({ csv := true } : ScriptFlags) ({} : PolicyFlags)
        (txCheckerFor tx nIn (some amount)) false = .fail .evalFalse ∧
      ¬ Accepts (vendorLaws (txCheckerFor tx nIn (some amount))
          (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)))
        msg (toLocalProg revocationKey delayedPaymentKey csv) [oneByte, sig] :=
  toLocal_revocation_wrong_key_rejected
    (txCheckerFor tx nIn (some amount)) msg revocationKey delayedPaymentKey csv
    sig hr hd hsigsz hsig

/-- **Concrete joint wrong-key rejection at the full checker**: an explicit
`verifyImpl` rejection over the BIP 143 model digest gives both the vendored
`.fail .evalFalse` and model non-acceptance. -/
theorem toLocal_revocation_wrong_key_rejected_txCheckerFor_verifyImpl
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount)
    (hIn : nIn < tx.vin.length)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (msg : ByteArray)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hpk : Bitcoin.Crypto.Seam.Der.isValidPubKey revocationKey.bytes = true)
    (hne : 0 < sig.size)
    (hsig : Bitcoin.Crypto.Ecdsa.Verify.verifyImpl
      (sig.extract 0 (sig.size - 1)) revocationKey.bytes
      (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn
        (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
        (hashtypeOf sig) amount) = false) :
    verifyWitnessProgram 10
        [sig, revocationSelector,
          serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)]
        0
        (hashSha256
          (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)))
        ({ csv := true } : ScriptFlags) ({} : PolicyFlags)
        (txCheckerFor tx nIn (some amount)) false = .fail .evalFalse ∧
      ¬ Accepts (vendorLaws (txCheckerFor tx nIn (some amount))
          (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)))
        msg (toLocalProg revocationKey delayedPaymentKey csv) [oneByte, sig] := by
  have hiff := bridge_ecdsa_hypothesis_iff_model_verify
    Bitcoin.Crypto.Ecdsa.Verify.verifyImpl tx nIn amount sig
    revocationKey.bytes
    (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
    (default : Bitcoin.Crypto.Seam.ScriptExecutionData) hpk hne
  have hchk0 : (checkerOf Bitcoin.Crypto.Ecdsa.Verify.verifyImpl tx nIn amount).base.checkECDSASignature
      sig revocationKey.bytes
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      .witnessV0 (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = false := by
    cases h : (checkerOf Bitcoin.Crypto.Ecdsa.Verify.verifyImpl tx nIn amount).base.checkECDSASignature
        sig revocationKey.bytes
        (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
        .witnessV0 (default : Bitcoin.Crypto.Seam.ScriptExecutionData) with
    | false => rfl
    | true =>
        rw [hiff.mp h] at hsig
        exact absurd hsig (by decide)
  have hchk : (txCheckerFor tx nIn (some amount)).base.checkECDSASignature
      sig revocationKey.bytes
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      .witnessV0 (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = false := by
    rw [txCheckerFor_some_checkECDSA_eq_checkerOf tx nIn amount hIn]
    exact hchk0
  exact toLocal_revocation_wrong_key_rejected_txCheckerFor tx nIn amount
    revocationKey delayedPaymentKey csv sig msg hr hd hsigsz hchk

/-- **A delayed-key signature cannot take the revocation branch at the full
checker.**  Under `RevocationKeySeparated`, a signature the full checker
accepts for the delayed key is rejected for the revocation key, so the
P2WSH verifier returns `.fail .evalFalse` and the model does not accept.
This is the Lightning-meaningful wrong-key case: the selector is `0x01`, but
the signature belongs to the other branch's key. -/
theorem toLocal_revocation_delayed_key_sig_rejected_txCheckerFor
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (msg : ByteArray)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hsep : RevocationKeySeparated (txCheckerFor tx nIn (some amount))
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      revocationKey delayedPaymentKey)
    (hdel : (txCheckerFor tx nIn (some amount)).base.checkECDSASignature
      sig delayedPaymentKey.bytes
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      .witnessV0 (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true) :
    verifyWitnessProgram 10
        [sig, revocationSelector,
          serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)]
        0
        (hashSha256
          (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)))
        ({ csv := true } : ScriptFlags) ({} : PolicyFlags)
        (txCheckerFor tx nIn (some amount)) false = .fail .evalFalse ∧
      ¬ Accepts (vendorLaws (txCheckerFor tx nIn (some amount))
          (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)))
        msg (toLocalProg revocationKey delayedPaymentKey csv) [oneByte, sig] :=
  toLocal_revocation_delayed_key_sig_rejected
    (txCheckerFor tx nIn (some amount)) msg revocationKey delayedPaymentKey csv
    sig hr hd hsigsz hsep hdel

/-! ## 4. Wrong-branch negatives at `txCheckerFor` -/

/-- **The empty selector cannot take the revocation branch at the full
checker.**  It executes the delayed block; a failing BIP 68/112 sequence
check errors with `.fail .unsatisfiedLocktime` before any signature check, so
a valid revocation-key signature in the witness is irrelevant.  The decode,
non-negativity and disable-bit premises are discharged from the faithful
two-byte encoding and `csv < 32768`. -/
theorem verifyWitnessProgram_toLocal_wrong_branch_txCheckerFor
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig program : ByteArray) (hcsv : csv < 32768)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hseq : checkSequenceDef (txCheckerFor tx nIn (some amount)).env
      (csv : Int) = false)
    (hps : program.size = 32)
    (hprog : hashSha256
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)) = program) :
    verifyWitnessProgram 10
      [sig, ByteArray.empty,
        serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)]
      0 program ({ csv := true } : ScriptFlags) ({} : PolicyFlags)
      (txCheckerFor tx nIn (some amount)) false = .fail .unsatisfiedLocktime :=
  verifyWitnessProgram_toLocal_delayed_csv_false
    (txCheckerFor tx nIn (some amount)) revocationKey delayedPaymentKey csv
    sig (csv : Int) program hr hd hsigsz
    (decodeNum_delayBytes csv hcsv) (nonneg_delay csv)
    (disableBit_delay csv hcsv) hseq hps hprog

/-- **Wrong-branch rejection from the transaction environment.**  For an
in-range input the sequence check can be stated on `locktimeEnvOf tx nIn`
instead of the checker record. -/
theorem verifyWitnessProgram_toLocal_wrong_branch_txCheckerFor_txEnv
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount)
    (hIn : nIn < tx.vin.length)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig program : ByteArray) (hcsv : csv < 32768)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hseq : checkSequenceDef (locktimeEnvOf tx nIn) (csv : Int) = false)
    (hps : program.size = 32)
    (hprog : hashSha256
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)) = program) :
    verifyWitnessProgram 10
      [sig, ByteArray.empty,
        serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)]
      0 program ({ csv := true } : ScriptFlags) ({} : PolicyFlags)
      (txCheckerFor tx nIn (some amount)) false = .fail .unsatisfiedLocktime := by
  refine verifyWitnessProgram_toLocal_wrong_branch_txCheckerFor tx nIn amount
    revocationKey delayedPaymentKey csv sig program hcsv hr hd hsigsz ?_ hps hprog
  rw [txCheckerFor_env_eq_locktimeEnvOf tx nIn amount hIn]
  exact hseq

/-- **Wrong-branch rejection from the explicit BIP 68/112 context.**  The
failure hypothesis is the negation of the exact sequence-context conjunction
(`checkSequenceDef_delay_iff`), stated on the transaction version and the
signing input's sequence.  This is the "wrong branch" condition in
consensus terms rather than an opaque `checkSequenceDef = false`. -/
theorem verifyWitnessProgram_toLocal_wrong_branch_txCheckerFor_context
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount)
    (hIn : nIn < tx.vin.length)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig program : ByteArray) (hcsv : csv < 32768)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hfail : ¬ ((¬ tx.version < 2) ∧
      ((tx.vin.getD nIn dummyTxIn).sequence.toNat &&&
          SEQUENCE_LOCKTIME_DISABLE_FLAG) = 0 ∧
      ((tx.vin.getD nIn dummyTxIn).sequence.toNat &&&
          (SEQUENCE_LOCKTIME_TYPE_FLAG ||| SEQUENCE_LOCKTIME_MASK)) <
        SEQUENCE_LOCKTIME_TYPE_FLAG ∧
      csv ≤ ((tx.vin.getD nIn dummyTxIn).sequence.toNat &&&
          (SEQUENCE_LOCKTIME_TYPE_FLAG ||| SEQUENCE_LOCKTIME_MASK))))
    (hps : program.size = 32)
    (hprog : hashSha256
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)) = program) :
    verifyWitnessProgram 10
      [sig, ByteArray.empty,
        serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)]
      0 program ({ csv := true } : ScriptFlags) ({} : PolicyFlags)
      (txCheckerFor tx nIn (some amount)) false = .fail .unsatisfiedLocktime := by
  have hiff := checkSequenceDef_delay_iff (locktimeEnvOf tx nIn) csv hcsv
  have hseq : checkSequenceDef (locktimeEnvOf tx nIn) (csv : Int) = false := by
    cases h : checkSequenceDef (locktimeEnvOf tx nIn) (csv : Int) with
    | false => rfl
    | true =>
        exact absurd (hiff.mp h) (by simpa [locktimeEnvOf] using hfail)
  exact verifyWitnessProgram_toLocal_wrong_branch_txCheckerFor_txEnv tx nIn amount
    hIn revocationKey delayedPaymentKey csv sig program hcsv hr hd hsigsz hseq hps hprog

/-- **Joint wrong-branch rejection at the full checker**: `.fail
.unsatisfiedLocktime` and model non-acceptance with the sequence law tied to
the same checker environment. -/
theorem toLocal_delayed_csv_failure_txCheckerFor
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (msg : ByteArray) (hcsv : csv < 32768)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hseq : checkSequenceDef (txCheckerFor tx nIn (some amount)).env
      (csv : Int) = false) :
    verifyWitnessProgram 10
        [sig, ByteArray.empty,
          serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)]
        0
        (hashSha256
          (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)))
        ({ csv := true } : ScriptFlags) ({} : PolicyFlags)
        (txCheckerFor tx nIn (some amount)) false = .fail .unsatisfiedLocktime ∧
      ¬ Accepts (vendorLawsCSV (txCheckerFor tx nIn (some amount))
          (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
          (csv : Int))
        msg (toLocalProg revocationKey delayedPaymentKey csv) [zeroByte, sig] := by
  refine ⟨?_, ?_⟩
  · exact verifyWitnessProgram_toLocal_wrong_branch_txCheckerFor tx nIn amount
      revocationKey delayedPaymentKey csv sig _ hcsv hr hd hsigsz hseq
      (hashSha256_size _) rfl
  · exact not_accepts_toLocal_delayed_csv_false
      (txCheckerFor tx nIn (some amount)) msg revocationKey delayedPaymentKey
      csv sig (csv : Int) hseq

/-! ## 5. Branch selection at the full checker -/

/-- **The selector alone decides the branch.**  For one `to_local` witness
script and one signature the full checker accepts, the `0x01` selector yields
vendor `.ok` on the revocation branch independently of the sequence
environment, while the empty selector yields `.fail .unsatisfiedLocktime`
under a failing sequence check.  The two witnesses differ only in the
selector item. -/
theorem toLocal_vendor_branch_selection_txCheckerFor
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig program : ByteArray) (hcsv : csv < 32768)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hseq : checkSequenceDef (txCheckerFor tx nIn (some amount)).env
      (csv : Int) = false)
    (hsig : (txCheckerFor tx nIn (some amount)).base.checkECDSASignature
      sig revocationKey.bytes
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      .witnessV0 (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true)
    (hps : program.size = 32)
    (hprog : hashSha256
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)) = program) :
    verifyWitnessProgram 10
        [sig, revocationSelector,
          serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)]
        0 program ({ csv := true } : ScriptFlags) ({} : PolicyFlags)
        (txCheckerFor tx nIn (some amount)) false = .ok ∧
      verifyWitnessProgram 10
        [sig, ByteArray.empty,
          serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)]
        0 program ({ csv := true } : ScriptFlags) ({} : PolicyFlags)
        (txCheckerFor tx nIn (some amount)) false = .fail .unsatisfiedLocktime := by
  refine ⟨?_, ?_⟩
  · exact verifyWitnessProgram_toLocal_revocation_txCheckerFor tx nIn amount
      revocationKey delayedPaymentKey csv sig program hr hd hsigsz
      hsig hps hprog
  · exact verifyWitnessProgram_toLocal_wrong_branch_txCheckerFor tx nIn amount
      revocationKey delayedPaymentKey csv sig program hcsv hr hd hsigsz hseq hps hprog


/-! ## Axiom pins -/

section Pins

/-- info: 'LnLean.Proofs.WaveH.H03.txCheckerFor_some_checkECDSA_eq_realCheckerOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms txCheckerFor_some_checkECDSA_eq_realCheckerOf
/-- info: 'LnLean.Proofs.WaveH.H03.txCheckerFor_some_checkECDSA_eq_checkerOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms txCheckerFor_some_checkECDSA_eq_checkerOf
/-- info: 'LnLean.Proofs.WaveH.H03.txCheckerFor_env_eq_locktimeEnvOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms txCheckerFor_env_eq_locktimeEnvOf
/-- info: 'LnLean.Proofs.WaveH.H03.verifyWitnessProgram_toLocal_revocation_txCheckerFor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms verifyWitnessProgram_toLocal_revocation_txCheckerFor
/-- info: 'LnLean.Proofs.WaveH.H03.toLocal_revocation_txCheckerFor_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms toLocal_revocation_txCheckerFor_agree
/-- info: 'LnLean.Proofs.WaveH.H03.verifyWitnessProgram_toLocal_revocation_txCheckerFor_verifyImpl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms verifyWitnessProgram_toLocal_revocation_txCheckerFor_verifyImpl
/-- info: 'LnLean.Proofs.WaveH.H03.verifyWitnessProgram_toLocal_revocation_bad_sig_txCheckerFor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms verifyWitnessProgram_toLocal_revocation_bad_sig_txCheckerFor
/-- info: 'LnLean.Proofs.WaveH.H03.verifyWitnessProgram_toLocal_revocation_bad_sig_txCheckerFor_verifyImpl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms verifyWitnessProgram_toLocal_revocation_bad_sig_txCheckerFor_verifyImpl
/-- info: 'LnLean.Proofs.WaveH.H03.toLocal_revocation_wrong_key_rejected_txCheckerFor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms toLocal_revocation_wrong_key_rejected_txCheckerFor
/-- info: 'LnLean.Proofs.WaveH.H03.toLocal_revocation_wrong_key_rejected_txCheckerFor_verifyImpl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms toLocal_revocation_wrong_key_rejected_txCheckerFor_verifyImpl
/-- info: 'LnLean.Proofs.WaveH.H03.toLocal_revocation_delayed_key_sig_rejected_txCheckerFor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms toLocal_revocation_delayed_key_sig_rejected_txCheckerFor
/-- info: 'LnLean.Proofs.WaveH.H03.verifyWitnessProgram_toLocal_wrong_branch_txCheckerFor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms verifyWitnessProgram_toLocal_wrong_branch_txCheckerFor
/-- info: 'LnLean.Proofs.WaveH.H03.verifyWitnessProgram_toLocal_wrong_branch_txCheckerFor_txEnv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms verifyWitnessProgram_toLocal_wrong_branch_txCheckerFor_txEnv
/-- info: 'LnLean.Proofs.WaveH.H03.verifyWitnessProgram_toLocal_wrong_branch_txCheckerFor_context' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms verifyWitnessProgram_toLocal_wrong_branch_txCheckerFor_context
/-- info: 'LnLean.Proofs.WaveH.H03.toLocal_delayed_csv_failure_txCheckerFor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms toLocal_delayed_csv_failure_txCheckerFor
/-- info: 'LnLean.Proofs.WaveH.H03.toLocal_vendor_branch_selection_txCheckerFor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms toLocal_vendor_branch_selection_txCheckerFor

end Pins

end LnLean.Proofs.WaveH.H03
