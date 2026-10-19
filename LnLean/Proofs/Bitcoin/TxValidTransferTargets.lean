import Bitcoin.TxValidation.Full
import Bitcoin.Crypto.Ecdsa.Verify
import Bitcoin.Ledger.Utxo
import Bitcoin.Capstone.RealChecker
import LnLean.Proofs.Bitcoin.SequenceContextTargets
import LnLean.Proofs.Bitcoin.InterpreterRevocationTargets

/-!
# `txCheckerFor` transfer for the delayed and revocation `to_local` branches

Wave 8 (lane `S8-L1-TXVALID`) closes the last transfer boundary named in
`docs/OPEN-ISSUES.md` (`L1-02`, `L1-07`) and in
`agents/reports/swarm7/S7-L1-SEQUENCE.md` §4.4: the wave-7 delayed/revocation
refinements were stated at `Bitcoin.Crypto.Seam.Entry.checkerOf` and
`Bitcoin.Capstone.RealChecker.realCheckerOf`, but the actual transaction
pipeline (`Bitcoin.TxValidation.Full`) builds its per-input checker with
`txCheckerFor tx nIn (amount : Option Amount)`.

## Main results

* `txCheckerFor_some_eq_realCheckerOf` — for a **known** spent amount,
  `txCheckerFor tx nIn (some amount)` is *exactly* `realCheckerOf tx nIn amount`
  as a `ScriptChecker` (same ECDSA entry, same locktime environment, and
  extensionally the same fail-closed Schnorr entry).  No input-range
  hypothesis is needed: the equality is at the level of the checker record.
* `txCheckerFor_some_ecdsa_witnessV0` — the witness-v0 ECDSA entry of
  `txCheckerFor` is the concrete `Bitcoin.Crypto.Ecdsa.Verify.verifyImpl` call
  over the model BIP 143 digest `sighashWitnessV0`, for a valid pubkey and a
  non-empty signature.
* `toLocal_delayed_txCheckerFor_refinement` — the exact sequence/context
  refinement of the delayed `to_local` branch, transferred to
  `txCheckerFor tx nIn (some amount)`.
* `toLocal_delayed_txCheckerFor_interpreters_agree` and
  `toLocal_revocation_txCheckerFor_interpreters_agree` — the positive
  vendor/model agreements with the `verifyImpl`/`sighashWitnessV0` hypothesis,
  i.e. the wave-5–7 bridges instantiated at the pipeline checker.
* `scriptLaneTx_true_all_ok_realChecker` and
  `txVerdictFull_accept_realChecker` — the tx-level transfer: whenever the
  pipeline's script lane (or the full pipeline) accepts, every input with a
  **known** amount was verified by `verifyScriptFull` at
  `realCheckerOf tx k amount`.
* `txCheckerFor_none_*` — the missing-amount boundary mechanized: with
  `amount = none` the checker's witness-v0 ECDSA entry is fail-closed
  (`HandleMissingData`), so the delayed and revocation witnesses cannot
  verify.  This is why the transfer is stated for `some amount`.
* `decodeNum_delayBytes_minimalData_true_of_128_le` /
  `decodeNum_delayBytes_minimalData_true_lt_128` and
  `toLocal_delayed_minimalData_true_scriptNum` — the `minimalData` policy
  edge: under `minimalData = true` the scaffold's fixed two-byte
  `to_self_delay` payload decodes exactly for `128 ≤ csv < 32768`, and is
  rejected as non-minimal (`.scriptNum`) for `csv < 128`.
* `decodeNum_delayBytes_high`, `decodeNum_delayBytes_32768` and
  `toLocal_delayed_high_negativeLocktime` — the `csv ≥ 32768` decode
  limitation: the fixed two-byte payload is a negative sign-magnitude
  `CScriptNum` there, so the vendored `OP_CSV` fails with
  `.negativeLocktime`.  At exactly `csv = 32768` the decoded value is
  negative zero, i.e. `0`, so the delay collapses to `0`; the rejection
  theorem therefore uses the strict bound `32768 < csv`.

## Scope (no unconditional consensus claim)

The statements remain **positive-direction** for the spend paths and
**conditional** on the explicit EC/context inputs, exactly as waves 5–7:

* the spent `amount` must be supplied (`some amount`); the digest commits to
  it (`SighashBridgeTargets.digest_commits_amount`) but this module does not
  prove that it equals the referenced outpoint's value;
* the ECDSA hypothesis is a concrete `verifyImpl` call, i.e. assumption C3's
  instantiation; no forgery-resistance claim is made;
* the delayed branch needs the BIP 68/112 context conjunction (version ≥ 2,
  input disable bit clear, height domain, `csv ≤` masked sequence) and the
  consensus `csv` flag; the revocation branch needs no sequence condition;
* the `minimalData` edge is stated for the exact `PolicyFlags` word
  `{ minimalData := true }`; the honest BOLT 3 script is minimally encoded,
  while this scaffold's `toLocalDelayBytes` is fixed-width, so the two agree
  in *value* only for payloads that are already minimal;
* `csv < 32768` is the faithful `CScriptNum` range of the fixed-width
  encoding; `32768 ≤ csv < 65536` is a mechanized rejection, not a
  modelling gap (the encoding, not the consensus rule, is the limitation).
  At `csv = 32768` the encoding yields `0`, so distinct delays `0` and
  `32768` collide; only `csv > 32768` yields `.negativeLocktime`.

No `VerifyScript`/full-consensus spendability is claimed: the bridge is at
`verifyWitnessProgram` (P2WSH), with default script flags and the caller's
policy word.
-/

namespace LnLean.Proofs.Bitcoin.TxValidTransferTargets

set_option autoImplicit false

open Bitcoin.Data
open Bitcoin.Activation
open Bitcoin.Script.Parser
open Bitcoin.Interpreter
open Bitcoin.Numeric
open Bitcoin.Crypto.Seam
open Bitcoin.Crypto.Seam.Entry
open LnLean
open LnLean.Bitcoin
open LnLean.Proofs.Bitcoin.SpendTargets
open LnLean.Proofs.Bitcoin.InterpreterBridgeTargets
open LnLean.Proofs.Bitcoin.InterpreterRevocationTargets
open LnLean.Proofs.Bitcoin.SequenceContextTargets
open LnLean.Proofs.Bitcoin.SighashBridgeTargets

/-! ## 1. The pipeline checker and the capstone real checker -/

/-- The Schnorr entry of `txCheckerFor` is fail-closed: `TxValidation.Full`
passes the BIP 342 sighash slot as `fun _ _ _ => none`, and `schnorrVerdict`
returns `false` whenever the BIP 342 sighash yields `none`.  Consequently the
Schnorr entry is extensionally the constant `false` of `realCheckerOf`. -/
theorem schnorrVerdict_failclosed
    (verify : ByteArray → ByteArray → ByteArray → Bool)
    (sig pk : ByteArray) (v : SigVersion) (d : ScriptExecutionData) :
    schnorrVerdict verify (fun _ _ _ => none) sig pk v d = false := by
  unfold schnorrVerdict
  split
  · split
    · split
      · rfl
      · rfl
    · rfl
  · rfl

/-- Two `BaseSignatureChecker`s with pointwise-equal entries are equal (the
record has only function fields). -/
theorem baseChecker_eq (a b : BaseSignatureChecker)
    (h1 : a.checkECDSASignature = b.checkECDSASignature)
    (h2 : a.checkSchnorrSignature = b.checkSchnorrSignature) : a = b := by
  cases a
  cases b
  simp_all

/-- **The checker equality.**  For a known spent amount, the transaction
pipeline's per-input checker is *exactly* the capstone `realCheckerOf`:
`(some amount).getD 0 = amount`, `(some amount).isSome = true`, the same
real ECDSA entry, the same transaction-derived `LocktimeEnv`, and both
Schnorr entries are fail-closed. -/
theorem txCheckerFor_some_eq_realCheckerOf (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount) :
    Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount) =
      Bitcoin.Capstone.RealChecker.realCheckerOf tx nIn amount := by
  unfold Bitcoin.TxValidation.Full.txCheckerFor
    Bitcoin.Capstone.RealChecker.realCheckerOf
    Bitcoin.Capstone.RealChecker.realEcdsaEntry
  simp only [Option.getD_some, Option.isSome_some]
  congr 1
  · apply baseChecker_eq
    · rfl
    · funext sig pk v d
      exact schnorrVerdict_failclosed Bitcoin.Crypto.Ecdsa.Verify.verifyImpl sig pk v d

/-- The pipeline checker coincides with the wave-6/7 model-digest checker
`checkerOf verifyImpl` for an in-range input.  The range hypothesis is only
needed because the model totalizations of `getD` use different dummy
`TxIn` sequences out of range (`0` versus `0xFFFFFFFF`). -/
theorem txCheckerFor_some_eq_checkerOf (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount)
    (hIn : nIn < tx.vin.length) :
    Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount) =
      checkerOf Bitcoin.Crypto.Ecdsa.Verify.verifyImpl tx nIn amount := by
  rw [txCheckerFor_some_eq_realCheckerOf]
  exact (checkerOf_eq_realCheckerOf tx nIn amount hIn).symm

/-- The transaction environment of the pipeline checker is the capstone
`LocktimeEnv`: version, locktime and the signing input's sequence. -/
theorem txCheckerFor_some_env (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount) :
    (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount)).env =
      { txVersion := tx.version
        txLockTime := tx.locktime
        txSequence := (tx.vin.getD nIn Bitcoin.Capstone.RealChecker.dummyTxIn).sequence } :=
  rfl

/-- **The witness-v0 ECDSA entry consumes the model digest.**  For a valid
pubkey and a non-empty signature, the pipeline checker's witness-v0 ECDSA
verdict is the concrete lax secp256k1 verifier applied to the BIP 143 model
digest (the signature body is the signature without its trailing hashtype
byte).  No input-range hypothesis is needed. -/
theorem txCheckerFor_some_ecdsa_witnessV0
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount)
    (sig pk code : ByteArray) (ed : ScriptExecutionData)
    (hpk : Bitcoin.Crypto.Seam.Der.isValidPubKey pk = true)
    (hne : 0 < sig.size) :
    (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount)).base.checkECDSASignature
        sig pk code .witnessV0 ed =
      Bitcoin.Crypto.Ecdsa.Verify.verifyImpl (sig.extract 0 (sig.size - 1)) pk
        (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn code (hashtypeOf sig) amount) := by
  rw [txCheckerFor_some_eq_realCheckerOf]
  simp only [Bitcoin.Capstone.RealChecker.realCheckerOf,
    Bitcoin.Capstone.RealChecker.realEcdsaEntry]
  rw [ecdsaEntry_pops_hashtype Bitcoin.Crypto.Ecdsa.Verify.verifyImpl
    (Bitcoin.Capstone.RealChecker.sighashDispatch tx nIn amount) true
    sig pk code .witnessV0 ed hpk hne (by intro _; rfl)]
  rw [← sighashDispatch_eq_real tx nIn amount]
  rfl

/-- If-and-only-if face of the digest bridge at the pipeline checker. -/
theorem txCheckerFor_some_ecdsa_witnessV0_iff
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount)
    (sig pk code : ByteArray) (ed : ScriptExecutionData)
    (hpk : Bitcoin.Crypto.Seam.Der.isValidPubKey pk = true)
    (hne : 0 < sig.size) :
    ((Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount)).base.checkECDSASignature
        sig pk code .witnessV0 ed = true) ↔
      Bitcoin.Crypto.Ecdsa.Verify.verifyImpl (sig.extract 0 (sig.size - 1)) pk
        (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn code (hashtypeOf sig) amount) = true := by
  rw [txCheckerFor_some_ecdsa_witnessV0 tx nIn amount sig pk code ed hpk hne]

/-! ## 2. The missing-amount boundary -/

/-- With `amount = none` (Core's `amount < 0` / `HandleMissingData` state),
the pipeline checker's witness-v0 ECDSA entry is fail-closed: even a valid
pubkey and a non-empty signature do not verify. -/
theorem txCheckerFor_none_ecdsa_witnessV0_false
    (tx : Bitcoin.Data.Tx) (nIn : Nat)
    (sig pk code : ByteArray) (ed : ScriptExecutionData)
    (hpk : Bitcoin.Crypto.Seam.Der.isValidPubKey pk = true)
    (hne : 0 < sig.size) :
    (Bitcoin.TxValidation.Full.txCheckerFor tx nIn none).base.checkECDSASignature
        sig pk code .witnessV0 ed = false := by
  unfold Bitcoin.TxValidation.Full.txCheckerFor
  simp only [Option.getD_none, Option.isSome_none]
  rw [txCheckerOf_ecdsa]
  exact ecdsaEntry_witnessV0_missing_amount_false Bitcoin.Crypto.Ecdsa.Verify.verifyImpl
    (Bitcoin.Capstone.RealChecker.sighashDispatch tx nIn 0) sig pk code ed hpk hne

/-- **Missing amount ⇒ the delayed branch cannot verify.**  With
`amount = none`, the wave-7 criterion
(`toLocal_delayed_sequence_vendor_iff`) would require the delayed-key ECDSA
check to be `true`, which is impossible because the witness-v0 entry is
fail-closed.  The honest delayed spend therefore needs the spent amount as
explicit context. -/
theorem txCheckerFor_none_delayed_not_ok
    (tx : Bitcoin.Data.Tx) (nIn : Nat)
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
      (Bitcoin.TxValidation.Full.txCheckerFor tx nIn none) false ≠ .ok := by
  intro hok
  have hiff := toLocal_delayed_sequence_vendor_iff
    (Bitcoin.TxValidation.Full.txCheckerFor tx nIn none)
    revocationKey delayedPaymentKey csv sig program hcsv hr hd hsigsz hps hprog
  rw [hiff] at hok
  have hfalse : (Bitcoin.TxValidation.Full.txCheckerFor tx nIn none).base.checkECDSASignature
      sig delayedPaymentKey.bytes
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      .witnessV0 (default : ScriptExecutionData) = false :=
    txCheckerFor_none_ecdsa_witnessV0_false tx nIn sig delayedPaymentKey.bytes
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      default hpk hne
  rw [hfalse] at hok
  exact Bool.false_ne_true hok.2

/-- Missing amount ⇒ the revocation branch fails with `.evalFalse` (the
`OP_CHECKSIG` pushes the canonical false and the P2WSH cleanstack rule
rejects it). -/
theorem txCheckerFor_none_revocation_fail
    (tx : Bitcoin.Data.Tx) (nIn : Nat)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (program : ByteArray)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hps : program.size = 32)
    (hprog : hashSha256
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)) = program)
    (hpk : Bitcoin.Crypto.Seam.Der.isValidPubKey revocationKey.bytes = true)
    (hne : 0 < sig.size) :
    verifyWitnessProgram 10
      [sig, revocationSelector,
        serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)]
      0 program ({ csv := true } : ScriptFlags) ({} : PolicyFlags)
      (Bitcoin.TxValidation.Full.txCheckerFor tx nIn none) false = .fail .evalFalse := by
  have hfalse : (Bitcoin.TxValidation.Full.txCheckerFor tx nIn none).base.checkECDSASignature
      sig revocationKey.bytes
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      .witnessV0 (default : ScriptExecutionData) = false :=
    txCheckerFor_none_ecdsa_witnessV0_false tx nIn sig revocationKey.bytes
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      default hpk hne
  exact verifyWitnessProgram_toLocal_revocation_bad_sig
    (Bitcoin.TxValidation.Full.txCheckerFor tx nIn none)
    revocationKey delayedPaymentKey csv sig program hr hd hsigsz hfalse hps hprog

/-! ## 3. Transfer of the delayed-branch refinement -/

/-- **Delayed `to_local` at the pipeline checker.**  The exact wave-7
sequence/context refinement, transferred to
`txCheckerFor tx nIn (some amount)` with no input-range hypothesis.
Vendor `.ok` is
equivalent to the full BIP 68/112 context (version ≥ 2, disable bit clear,
height domain, `csv ≤` masked sequence) together with the concrete
`verifyImpl` call over the model digest. -/
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
  rw [toLocal_delayed_sequence_context_refinement
    (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount))
    revocationKey delayedPaymentKey csv sig program hcsv hr hd hsigsz hps hprog]
  simp only [txCheckerFor_some_env]
  rw [txCheckerFor_some_ecdsa_witnessV0_iff tx nIn amount sig delayedPaymentKey.bytes
    (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
    (default : ScriptExecutionData) hpk hne]

/-- **Delayed positive agreement at the pipeline checker.**  Under the
explicit `verifyImpl` hypothesis over `sighashWitnessV0`, the vendored P2WSH
verifier returns `.ok`, the model `P2WSHSpend` holds with the sequence law
`vendorLawsCSV`, and the pipeline checker's ECDSA entry is `true`. -/
theorem toLocal_delayed_txCheckerFor_interpreters_agree
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (hcsv : csv < 32768)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hpk : Bitcoin.Crypto.Seam.Der.isValidPubKey delayedPaymentKey.bytes = true)
    (hne : 0 < sig.size)
    (hseq : checkSequenceDef
      (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount)).env
      (csv : Int) = true)
    (hsig : Bitcoin.Crypto.Ecdsa.Verify.verifyImpl (sig.extract 0 (sig.size - 1))
      delayedPaymentKey.bytes
      (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn
        (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
        (hashtypeOf sig) amount) = true) :
    verifyWitnessProgram 10
        [sig, ByteArray.empty,
          serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)]
        0
        (hashSha256
          (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)))
        ({ csv := true } : ScriptFlags) ({} : PolicyFlags)
        (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount)) false = .ok ∧
      P2WSHSpend (vendorLawsCSV
          (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount))
          (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
          (csv : Int))
        (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn
          (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
          (hashtypeOf sig) amount)
        (hashSha256
          (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)))
        (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
        (toLocalProg revocationKey delayedPaymentKey csv) [zeroByte, sig] ∧
      (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount)).base.checkECDSASignature
        sig delayedPaymentKey.bytes
        (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
        .witnessV0 (default : ScriptExecutionData) = true := by
  have hc : (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount)).base.checkECDSASignature
      sig delayedPaymentKey.bytes
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      .witnessV0 (default : ScriptExecutionData) = true := by
    rw [txCheckerFor_some_ecdsa_witnessV0 tx nIn amount sig delayedPaymentKey.bytes
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      default hpk hne]
    exact hsig
  have hbridge := toLocal_delayed_sequence_interpreters_agree
    (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount))
    (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      (hashtypeOf sig) amount)
    revocationKey delayedPaymentKey csv sig
    (hashSha256 (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)))
    hcsv hr hd hsigsz (hashSha256_size _) rfl hseq hc
  exact ⟨hbridge.1, hbridge.2, hc⟩

/-! ## 4. Transfer of the revocation-branch agreement -/

/-- **Revocation at the pipeline checker.**  The revocation selector never
consults `OP_CSV`, so no sequence hypothesis appears.  Under the explicit
`verifyImpl` call over the model digest on the revocation key, the vendored
P2WSH verifier returns `.ok`, the model `P2WSHSpend` holds with
`vendorLaws`, and the pipeline checker's ECDSA entry is `true`. -/
theorem toLocal_revocation_txCheckerFor_interpreters_agree
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hpk : Bitcoin.Crypto.Seam.Der.isValidPubKey revocationKey.bytes = true)
    (hne : 0 < sig.size)
    (hsig : Bitcoin.Crypto.Ecdsa.Verify.verifyImpl (sig.extract 0 (sig.size - 1))
      revocationKey.bytes
      (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn
        (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
        (hashtypeOf sig) amount) = true) :
    verifyWitnessProgram 10
        [sig, revocationSelector,
          serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)]
        0
        (hashSha256
          (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)))
        ({ csv := true } : ScriptFlags) ({} : PolicyFlags)
        (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount)) false = .ok ∧
      P2WSHSpend (vendorLaws
          (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount))
          (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)))
        (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn
          (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
          (hashtypeOf sig) amount)
        (hashSha256
          (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)))
        (toLocalScriptFull revocationKey delayedPaymentKey csv).bytes
        (toLocalProg revocationKey delayedPaymentKey csv) [oneByte, sig] ∧
      (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount)).base.checkECDSASignature
        sig revocationKey.bytes
        (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
        .witnessV0 (default : ScriptExecutionData) = true := by
  have hc : (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount)).base.checkECDSASignature
      sig revocationKey.bytes
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      .witnessV0 (default : ScriptExecutionData) = true := by
    rw [txCheckerFor_some_ecdsa_witnessV0 tx nIn amount sig revocationKey.bytes
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      default hpk hne]
    exact hsig
  have hbridge := toLocal_revocation_interpreters_agree
    (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount))
    (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      (hashtypeOf sig) amount)
    revocationKey delayedPaymentKey csv sig hr hd hsigsz hc
  exact ⟨hbridge.1, hbridge.2, hc⟩

/-- **Branch selection at the pipeline checker.**  For one witness script and
one signature, the selector alone decides: `revocationSelector` returns
`.ok` on the revocation branch regardless of the sequence environment, while
the empty selector returns `.fail .unsatisfiedLocktime` when the vendored
sequence check fails — even though the same signature is valid for the
revocation key. -/
theorem toLocal_vendor_branch_selection_txCheckerFor
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (program : ByteArray) (hcsv : csv < 32768)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hpk : Bitcoin.Crypto.Seam.Der.isValidPubKey revocationKey.bytes = true)
    (hne : 0 < sig.size)
    (hsig : Bitcoin.Crypto.Ecdsa.Verify.verifyImpl (sig.extract 0 (sig.size - 1))
      revocationKey.bytes
      (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn
        (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
        (hashtypeOf sig) amount) = true)
    (hseq : checkSequenceDef
      (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount)).env
      (csv : Int) = false)
    (hps : program.size = 32)
    (hprog : hashSha256
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)) = program) :
    verifyWitnessProgram 10
        [sig, revocationSelector,
          serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)]
        0 program ({ csv := true } : ScriptFlags) ({} : PolicyFlags)
        (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount)) false = .ok ∧
      verifyWitnessProgram 10
        [sig, ByteArray.empty,
          serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)]
        0 program ({ csv := true } : ScriptFlags) ({} : PolicyFlags)
        (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount)) false
        = .fail .unsatisfiedLocktime := by
  have hc : (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount)).base.checkECDSASignature
      sig revocationKey.bytes
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      .witnessV0 (default : ScriptExecutionData) = true := by
    rw [txCheckerFor_some_ecdsa_witnessV0 tx nIn amount sig revocationKey.bytes
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      default hpk hne]
    exact hsig
  exact toLocal_vendor_branch_selection
    (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount))
    revocationKey delayedPaymentKey csv sig (csv : Int) program hr hd hsigsz
    (decodeNum_delayBytes csv hcsv) (nonneg_delay csv) (disableBit_delay csv hcsv)
    hseq hc hps hprog

/-! ## 5. The `minimalData` policy edge -/

/-- The high byte of a delay below `2^15` is below `128`, so it is not read as
a sign byte. -/
theorem delayBytes_high_lt_128 (csv : Nat) (hcsv : csv < 32768) :
    (csv >>> 8) % 256 < 128 := by
  rw [Nat.shiftRight_eq_div_pow]
  have h2 : csv / 256 % 256 = csv / 256 := Nat.mod_eq_of_lt (by omega)
  omega

/-- For `128 ≤ csv < 32768`, the fixed two-byte payload is a *minimal*
`CScriptNum` encoding: either the high byte is nonzero and below `128`, or it
is zero and the low byte carries the sign bit (Core's second-byte rule). -/
theorem minimalOkBE_delayBytes (csv : Nat) (hcsv : csv < 32768)
    (h128 : 128 ≤ csv) :
    minimalOkBE [(csv >>> 8) % 256, csv % 256] = true := by
  have hlt := delayBytes_high_lt_128 csv hcsv
  by_cases h0 : (csv >>> 8) % 256 = 0
  · have hd : csv >>> 8 = csv / 256 := Nat.shiftRight_eq_div_pow csv 8
    have hlt256 : csv / 256 < 256 := by omega
    have hq : csv / 256 = 0 := by
      have hz : (csv / 256) % 256 = 0 := by rw [← hd]; exact h0
      rwa [Nat.mod_eq_of_lt hlt256] at hz
    have hcs : csv < 256 := by omega
    have hmod : csv % 256 = csv := Nat.mod_eq_of_lt (by omega)
    rw [h0, hmod]
    simp only [minimalOkBE, Nat.zero_mod, ite_true, decide_eq_true_eq]
    omega
  · have hmod : (csv >>> 8) % 256 % 128 ≠ 0 := by omega
    simp only [minimalOkBE, hmod, ite_false]

/-- Under `minimalData = true`, the fixed two-byte delay payload still decodes
to `csv` whenever `128 ≤ csv < 32768`. -/
theorem decodeNum_delayBytes_minimalData_true_of_128_le (pol : PolicyFlags)
    (hmin : pol.minimalData = true) (csv : Nat) (hcsv : csv < 32768)
    (h128 : 128 ≤ csv) :
    decodeNum pol (delayBytes csv) 5 = .ok (csv : Int) := by
  rw [decodeNum, decodeScriptNum, hmin, bytesOf_delayBytes]
  rw [show ([csv % 256, (csv >>> 8) % 256] : List Nat).reverse =
      [(csv >>> 8) % 256, csv % 256] by rfl]
  rw [decodeBE_some (by simp) (Or.inr (minimalOkBE_delayBytes csv hcsv h128))]
  change Except.ok (setVchBE [(csv >>> 8) % 256, csv % 256]) = Except.ok (csv : Int)
  rw [setVchBE_delay csv hcsv]

/-- For `csv < 128` the fixed two-byte payload has a leading zero byte in
big-endian order and a clear sign bit on the next byte, so it is **not**
minimal. -/
theorem minimalOkBE_delayBytes_lt_128 (csv : Nat) (h128 : csv < 128) :
    minimalOkBE [0, csv] = false := by
  simp only [minimalOkBE, Nat.zero_mod, ite_true, decide_eq_false_iff_not]
  omega

/-- A `decodeBE` call under the minimality requirement fails when the
minimal-encoding check fails. -/
theorem decodeBE_true_none_of_minimal (maxSize : Nat) (l : List Nat)
    (h : minimalOkBE l = false) : decodeBE true maxSize l = none := by
  unfold decodeBE
  by_cases hw : l.length > maxSize
  · simp [hw]
  · simp [hw, h]

/-- **The `minimalData` rejection for short delays.**  Under
`minimalData = true` and `csv < 128`, the scaffold's fixed two-byte
`to_self_delay` payload is non-minimal, so the vendored decode fails with
`.scriptNum`.  (BOLT 3 emits the minimal one-byte encoding for delays below
`128`; the fixed-width scaffold payload does not.) -/
theorem decodeNum_delayBytes_minimalData_true_lt_128 (pol : PolicyFlags)
    (hmin : pol.minimalData = true) (csv : Nat) (h128 : csv < 128) :
    decodeNum pol (delayBytes csv) 5 = .error .scriptNum := by
  have hbytes : bytesOf (delayBytes csv) = [csv, 0] := by
    rw [bytesOf_delayBytes]
    have h1 : csv % 256 = csv := Nat.mod_eq_of_lt (by omega)
    have h2 : (csv >>> 8) % 256 = 0 := by
      rw [Nat.shiftRight_eq_div_pow]
      have : csv / 256 = 0 := Nat.div_eq_of_lt (by omega)
      simp [this]
    rw [h1, h2]
  rw [decodeNum, decodeScriptNum, hmin, hbytes]
  rw [show ([csv, 0] : List Nat).reverse = [0, csv] by rfl]
  rw [decodeBE_true_none_of_minimal 5 [0, csv] (minimalOkBE_delayBytes_lt_128 csv h128)]

/-- A minimal two-byte push of the delay (size `2`, opcode `2`) passes the
`MINIMALDATA` push gate. -/
theorem checkMinimalPush_true_of_size {d : ByteArray} {n : Nat}
    (h : d.size = n) (h2 : 2 ≤ n) (h75 : n ≤ 75) :
    checkMinimalPush d n = true := by
  unfold checkMinimalPush
  rw [h]
  simp [show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≤ 75 by omega]

theorem checkMinimalPush_toLocalDelayBytes (csv : Blocks) :
    checkMinimalPush (toLocalDelayBytes csv) 2 = true :=
  checkMinimalPush_true_of_size (toLocalDelayBytes_size csv) (by omega) (by omega)

theorem checkMinimalPush_pubkey (k : PubKey) (hk : k.bytes.size = 33) :
    checkMinimalPush k.bytes 33 = true :=
  checkMinimalPush_true_of_size hk (by omega) (by omega)

theorem evalFrom_toLocalWireOps_delayed_scriptNum (chk : ScriptChecker)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hdec : decodeNum ({ minimalData := true } : PolicyFlags) (delayBytes csv) 5
      = .error .scriptNum) :
    evalFrom
      { flags := ({ csv := true } : ScriptFlags),
        pol := ({ minimalData := true } : PolicyFlags), chk := chk,
        sv := .witnessV0,
        bytes := serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv),
        ed := (default : Bitcoin.Crypto.Seam.ScriptExecutionData) }
      10 (toLocalWireOps revocationKey delayedPaymentKey csv)
      { stack := [ByteArray.empty, sig], alt := [], vf := [], opCount := 0,
        codeSep := 0, vwLeft := none }
    = Except.error .scriptNum := by
  simp [toLocalWireOps, evalFrom, stepChecked, stepBody, stepBody.dispatchOp,
    evalChecksigDispatch, evalChecksigPreTapscript, checkSigEncoding, checkPubKeyEncoding,
    Bitcoin.Numeric.castToBool, Bitcoin.Numeric.castToBoolList,
    Bitcoin.Numeric.bytesOf, delayBytes, topAt, pushBoolV, vchTrue, serU8, disabledWire,
    Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE, MAX_STACK_SIZE, MAX_OPS_PER_SCRIPT,
    toLocalDelayBytes_size, checkMinimalPush_toLocalDelayBytes, hr, hd]
  rw [show decodeNum ({ minimalData := true } : PolicyFlags) (toLocalDelayBytes csv) 5
      = .error .scriptNum by simpa [delayBytes] using hdec]

theorem evalScriptBytes_toLocal_delayed_scriptNum (chk : ScriptChecker)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hdec : decodeNum ({ minimalData := true } : PolicyFlags) (delayBytes csv) 5
      = .error .scriptNum) :
    evalScriptBytes 10 ({ csv := true } : ScriptFlags)
      ({ minimalData := true } : PolicyFlags)
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      [ByteArray.empty, sig] chk .witnessV0
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData)
    = Except.error .scriptNum := by
  unfold evalScriptBytes
  have hsz : (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)).size = 77 :=
    serializeOpcodes_toLocal_size revocationKey delayedPaymentKey csv hr hd
  rw [ite_eq_right (by simp [hsz, MAX_SCRIPT_SIZE])]
  rw [toLocal_parseWire revocationKey delayedPaymentKey csv hr hd]
  simp [finalStack,
    evalFrom_toLocalWireOps_delayed_scriptNum chk revocationKey delayedPaymentKey csv
      sig hr hd hdec]

theorem executeWitnessScript_toLocal_delayed_scriptNum (chk : ScriptChecker)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (vwSer : Int)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hdec : decodeNum ({ minimalData := true } : PolicyFlags) (delayBytes csv) 5
      = .error .scriptNum) :
    executeWitnessScript 10 [sig, ByteArray.empty] vwSer
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      ({ csv := true } : ScriptFlags) ({ minimalData := true } : PolicyFlags) chk .witnessV0
    = .fail .scriptNum := by
  have hsig' : ¬ Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE < sig.size := by
    unfold Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE; omega
  simp [executeWitnessScript, executeWitnessScript.runExec,
    evalScriptBytes_toLocal_delayed_scriptNum chk revocationKey delayedPaymentKey csv
      sig hr hd hdec, hsig']

theorem verifyWitnessProgram_toLocal_delayed_scriptNum (chk : ScriptChecker)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (program : ByteArray)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hdec : decodeNum ({ minimalData := true } : PolicyFlags) (delayBytes csv) 5
      = .error .scriptNum)
    (hps : program.size = 32)
    (hprog : hashSha256
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)) = program) :
    verifyWitnessProgram 10
      [sig, ByteArray.empty,
        serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)]
      0 program ({ csv := true } : ScriptFlags) ({ minimalData := true } : PolicyFlags)
      chk false = .fail .scriptNum := by
  simp [verifyWitnessProgram, hps, hprog, byteArray_bne_self,
    executeWitnessScript_toLocal_delayed_scriptNum chk revocationKey delayedPaymentKey
      csv sig
      (witnessSerSize [sig, ByteArray.empty,
        serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)])
      hr hd hsigsz hdec]

/-- **The `minimalData` rejection, at the full P2WSH verifier.**  With the
exact policy word `{ minimalData := true }` and `csv < 128`, the delayed
witness is rejected at the `OP_CSV` operand decode with `.fail .scriptNum`,
for the pipeline checker and any spent amount. -/
theorem toLocal_delayed_minimalData_true_scriptNum
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (program : ByteArray) (h128 : csv < 128)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hps : program.size = 32)
    (hprog : hashSha256
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)) = program) :
    verifyWitnessProgram 10
      [sig, ByteArray.empty,
        serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)]
      0 program ({ csv := true } : ScriptFlags)
      ({ minimalData := true } : PolicyFlags)
      (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount)) false
    = .fail .scriptNum := by
  exact verifyWitnessProgram_toLocal_delayed_scriptNum
    (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount))
    revocationKey delayedPaymentKey csv sig program hr hd hsigsz
    (decodeNum_delayBytes_minimalData_true_lt_128 _
      (by rfl) csv h128) hps hprog

/-! ### The positive side of the policy edge

Under `minimalData = true` the *value* decode succeeds for `128 ≤ csv`, and
the vendored script execution completes.  The proofs below are the wave-5
delayed-branch computation re-run at the exact policy word
`{ minimalData := true }`; only the push gate needed the new
`checkMinimalPush` lemmas (the default policy never enters that gate). -/

theorem evalFrom_toLocalWireOps_delayed_minimalData (chk : ScriptChecker)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (n : Bitcoin.Numeric.ScriptNum)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hdec : decodeNum ({ minimalData := true } : PolicyFlags) (delayBytes csv) 5 = .ok n)
    (hnn : 0 ≤ n)
    (hdis : Int.toNat n &&& SEQUENCE_LOCKTIME_DISABLE_FLAG = 0)
    (hseq : checkSequenceDef chk.env n = true)
    (hsig : chk.base.checkECDSASignature sig delayedPaymentKey.bytes
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      .witnessV0 (default : ScriptExecutionData) = true) :
    evalFrom
      { flags := ({ csv := true } : ScriptFlags),
        pol := ({ minimalData := true } : PolicyFlags), chk := chk,
        sv := .witnessV0,
        bytes := serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv),
        ed := (default : ScriptExecutionData) }
      10 (toLocalWireOps revocationKey delayedPaymentKey csv)
      { stack := [ByteArray.empty, sig], alt := [], vf := [], opCount := 0,
        codeSep := 0, vwLeft := none }
    = Except.ok
        { stack := [ByteArray.mk #[0x01]], alt := [], vf := [], opCount := 6,
          codeSep := 0, vwLeft := none } := by
  simp [toLocalWireOps, evalFrom, stepChecked, stepBody, stepBody.dispatchOp,
    evalChecksigDispatch, evalChecksigPreTapscript, checkSigEncoding, checkPubKeyEncoding,
    Bitcoin.Numeric.castToBool, Bitcoin.Numeric.castToBoolList,
    Bitcoin.Numeric.bytesOf, delayBytes, topAt, pushBoolV, vchTrue, serU8, disabledWire,
    Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE, MAX_STACK_SIZE, MAX_OPS_PER_SCRIPT,
    toLocalDelayBytes_size, checkMinimalPush_toLocalDelayBytes,
    checkMinimalPush_pubkey revocationKey hr,
    checkMinimalPush_pubkey delayedPaymentKey hd, hdis, hseq, hsig, hr, hd]
  rw [show decodeNum ({ minimalData := true } : PolicyFlags)
      (toLocalDelayBytes csv) 5 = .ok n by
    simpa [delayBytes] using hdec]
  have hnlt : ¬ n < 0 := Int.not_lt.mpr hnn
  simp [hnlt, hdis, hseq, hsig, Bitcoin.Numeric.castToBoolList, empty_push_eq]
  rfl

theorem evalScriptBytes_toLocal_delayed_minimalData (chk : ScriptChecker)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (n : Bitcoin.Numeric.ScriptNum)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hdec : decodeNum ({ minimalData := true } : PolicyFlags) (delayBytes csv) 5 = .ok n)
    (hnn : 0 ≤ n)
    (hdis : Int.toNat n &&& SEQUENCE_LOCKTIME_DISABLE_FLAG = 0)
    (hseq : checkSequenceDef chk.env n = true)
    (hsig : chk.base.checkECDSASignature sig delayedPaymentKey.bytes
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      .witnessV0 (default : ScriptExecutionData) = true) :
    evalScriptBytes 10 ({ csv := true } : ScriptFlags)
      ({ minimalData := true } : PolicyFlags)
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      [ByteArray.empty, sig] chk .witnessV0
      (default : ScriptExecutionData)
    = Except.ok [ByteArray.mk #[0x01]] := by
  unfold evalScriptBytes
  have hsz : (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)).size = 77 :=
    serializeOpcodes_toLocal_size revocationKey delayedPaymentKey csv hr hd
  rw [if_neg (by simp [hsz, MAX_SCRIPT_SIZE])]
  rw [toLocal_parseWire revocationKey delayedPaymentKey csv hr hd]
  simp [finalStack,
    evalFrom_toLocalWireOps_delayed_minimalData chk revocationKey delayedPaymentKey csv
      sig n hr hd hdec hnn hdis hseq hsig]

theorem executeWitnessScript_toLocal_delayed_minimalData (chk : ScriptChecker)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (n : Bitcoin.Numeric.ScriptNum) (vwSer : Int)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hdec : decodeNum ({ minimalData := true } : PolicyFlags) (delayBytes csv) 5 = .ok n)
    (hnn : 0 ≤ n)
    (hdis : Int.toNat n &&& SEQUENCE_LOCKTIME_DISABLE_FLAG = 0)
    (hseq : checkSequenceDef chk.env n = true)
    (hsig : chk.base.checkECDSASignature sig delayedPaymentKey.bytes
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      .witnessV0 (default : ScriptExecutionData) = true) :
    executeWitnessScript 10 [sig, ByteArray.empty] vwSer
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      ({ csv := true } : ScriptFlags) ({ minimalData := true } : PolicyFlags)
      chk .witnessV0 = .ok := by
  have hsig' : ¬ Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE < sig.size := by
    unfold Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE; omega
  have hempty' : ¬ Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE < ByteArray.empty.size := by
    unfold Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE; decide
  simp [executeWitnessScript, executeWitnessScript.runExec,
    evalScriptBytes_toLocal_delayed_minimalData chk revocationKey delayedPaymentKey
      csv sig n hr hd hdec hnn hdis hseq hsig,
    hsig', hempty', Bitcoin.Numeric.castToBool, Bitcoin.Numeric.castToBoolList]
  decide

theorem verifyWitnessProgram_toLocal_delayed_minimalData (chk : ScriptChecker)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (n : Bitcoin.Numeric.ScriptNum) (program : ByteArray)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hdec : decodeNum ({ minimalData := true } : PolicyFlags) (delayBytes csv) 5 = .ok n)
    (hnn : 0 ≤ n)
    (hdis : Int.toNat n &&& SEQUENCE_LOCKTIME_DISABLE_FLAG = 0)
    (hseq : checkSequenceDef chk.env n = true)
    (hsig : chk.base.checkECDSASignature sig delayedPaymentKey.bytes
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      .witnessV0 (default : ScriptExecutionData) = true)
    (hps : program.size = 32)
    (hprog : hashSha256
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)) = program) :
    verifyWitnessProgram 10
      [sig, ByteArray.empty,
        serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)]
      0 program ({ csv := true } : ScriptFlags)
      ({ minimalData := true } : PolicyFlags) chk false = .ok := by
  simp [verifyWitnessProgram, hps, hprog, byteArray_bne_self,
    executeWitnessScript_toLocal_delayed_minimalData chk revocationKey
      delayedPaymentKey csv sig n
      (witnessSerSize [sig, ByteArray.empty,
        serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)])
      hr hd hsigsz hdec hnn hdis hseq hsig]

/-- **The positive side of the `minimalData` edge at the pipeline checker.**
For `128 ≤ csv < 32768`, the fixed payload is minimal, the vendored verifier
returns `.ok` under `{ minimalData := true }`, the checker entry is the
`verifyImpl` call over the model digest, and the model `P2WSHSpend` holds. -/
theorem toLocal_delayed_minimalData_true_ok
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (program : ByteArray)
    (hcsv : csv < 32768) (h128 : 128 ≤ csv)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hps : program.size = 32)
    (hprog : hashSha256
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)) = program)
    (hpk : Bitcoin.Crypto.Seam.Der.isValidPubKey delayedPaymentKey.bytes = true)
    (hne : 0 < sig.size)
    (hseq : checkSequenceDef
      (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount)).env
      (csv : Int) = true)
    (hsig : Bitcoin.Crypto.Ecdsa.Verify.verifyImpl (sig.extract 0 (sig.size - 1))
      delayedPaymentKey.bytes
      (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn
        (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
        (hashtypeOf sig) amount) = true) :
    verifyWitnessProgram 10
        [sig, ByteArray.empty,
          serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)]
        0 program ({ csv := true } : ScriptFlags)
        ({ minimalData := true } : PolicyFlags)
        (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount)) false = .ok ∧
      P2WSHSpend (vendorLawsCSV
          (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount))
          (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
          (csv : Int))
        (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn
          (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
          (hashtypeOf sig) amount)
        (hashSha256
          (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)))
        (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
        (toLocalProg revocationKey delayedPaymentKey csv) [zeroByte, sig] := by
  have hc : (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount)).base.checkECDSASignature
      sig delayedPaymentKey.bytes
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      .witnessV0 (default : ScriptExecutionData) = true := by
    rw [txCheckerFor_some_ecdsa_witnessV0 tx nIn amount sig delayedPaymentKey.bytes
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      default hpk hne]
    exact hsig
  refine ⟨?_, ?_⟩
  · exact verifyWitnessProgram_toLocal_delayed_minimalData
      (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount))
      revocationKey delayedPaymentKey csv sig (csv : Int) program hr hd hsigsz
      (decodeNum_delayBytes_minimalData_true_of_128_le _ (by rfl) csv hcsv h128)
      (nonneg_delay csv) (disableBit_delay csv hcsv) hseq hc hps hprog
  · exact toLocal_model_spend_delayed
      (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount))
      (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn
        (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
        (hashtypeOf sig) amount)
      revocationKey delayedPaymentKey csv sig (csv : Int) hr hd
      (decodeNum_delayBytes csv hcsv) (nonneg_delay csv) (disableBit_delay csv hcsv)
      hseq hc

/-! ## 6. The `csv ≥ 32768` decode limitation -/

/-- For `32768 ≤ csv < 65536`, the fixed two-byte payload is read as the
*negative* sign-magnitude number `32768 - csv`. -/
theorem setVchBE_delay_high (csv : Nat) (hlo : 32768 ≤ csv) (hhi : csv < 65536) :
    setVchBE [(csv >>> 8) % 256, csv % 256] = (32768 : Int) - (csv : Int) := by
  have hd : csv >>> 8 = csv / 256 := Nat.shiftRight_eq_div_pow csv 8
  have hlt : csv / 256 < 256 := by omega
  have hmod : (csv >>> 8) % 256 = csv / 256 := by
    rw [hd]; exact Nat.mod_eq_of_lt hlt
  have hge : ¬ (csv / 256 < 128) := by omega
  rw [show ([(csv >>> 8) % 256, csv % 256] : List Nat) = [csv / 256, csv % 256] by
    rw [hmod]]
  simp only [setVchBE, hge, ite_false, magOfBE, List.length_cons, List.length_nil,
    Nat.zero_add, Nat.reducePow, Nat.mul_one, Nat.add_zero]
  have hdm : 256 * (csv / 256) + csv % 256 = csv := Nat.div_add_mod csv 256
  have h128 : 128 * 256 = 32768 := by decide
  omega

/-- For `32768 ≤ csv < 65536`, the default-policy decode of the fixed
two-byte delay is the negative number `32768 - csv`. -/
theorem decodeNum_delayBytes_high (csv : Nat) (hlo : 32768 ≤ csv) (hhi : csv < 65536) :
    decodeNum ({} : PolicyFlags) (delayBytes csv) 5 =
      .ok ((32768 : Int) - (csv : Int)) := by
  rw [decodeNum, decodeScriptNum, bytesOf_delayBytes]
  rw [show ([(csv % 256), (csv >>> 8) % 256] : List Nat).reverse =
      [(csv >>> 8) % 256, csv % 256] by rfl]
  rw [decodeBE_some (by simp) (Or.inl rfl)]
  change Except.ok (setVchBE [(csv >>> 8) % 256, csv % 256]) =
    Except.ok ((32768 : Int) - (csv : Int))
  rw [setVchBE_delay_high csv hlo hhi]

/-- At the boundary `csv = 32768` the sign bit is set but the magnitude is
zero, so the fixed encoding decodes to `0`: the delays `0` and `32768` are
indistinguishable.  Hence the strict bound in
`toLocal_delayed_high_negativeLocktime`. -/
theorem decodeNum_delayBytes_32768 :
    decodeNum ({} : PolicyFlags) (delayBytes 32768) 5 = .ok 0 := by
  have h := decodeNum_delayBytes_high 32768 (Nat.le_refl 32768) (by decide : 32768 < 65536)
  simpa using h

theorem evalFrom_toLocalWireOps_delayed_negative (chk : ScriptChecker)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (n : Bitcoin.Numeric.ScriptNum)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hdec : decodeNum ({} : PolicyFlags) (delayBytes csv) 5 = .ok n)
    (hn : n < 0) :
    evalFrom
      { flags := ({ csv := true } : ScriptFlags), pol := ({} : PolicyFlags), chk := chk,
        sv := .witnessV0,
        bytes := serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv),
        ed := (default : ScriptExecutionData) }
      10 (toLocalWireOps revocationKey delayedPaymentKey csv)
      { stack := [ByteArray.empty, sig], alt := [], vf := [], opCount := 0,
        codeSep := 0, vwLeft := none }
    = Except.error .negativeLocktime := by
  simp [toLocalWireOps, evalFrom, stepChecked, stepBody, stepBody.dispatchOp,
    evalChecksigDispatch, evalChecksigPreTapscript, checkSigEncoding, checkPubKeyEncoding,
    Bitcoin.Numeric.castToBool, Bitcoin.Numeric.castToBoolList,
    Bitcoin.Numeric.bytesOf, delayBytes, topAt, pushBoolV, vchTrue, serU8, disabledWire,
    Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE, MAX_STACK_SIZE, MAX_OPS_PER_SCRIPT,
    toLocalDelayBytes_size, hr, hd]
  rw [show decodeNum ({} : PolicyFlags) (toLocalDelayBytes csv) 5 = .ok n by
    simpa [delayBytes] using hdec]
  simp [hn]

theorem evalScriptBytes_toLocal_delayed_negative (chk : ScriptChecker)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (n : Bitcoin.Numeric.ScriptNum)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hdec : decodeNum ({} : PolicyFlags) (delayBytes csv) 5 = .ok n)
    (hn : n < 0) :
    evalScriptBytes 10 ({ csv := true } : ScriptFlags) ({} : PolicyFlags)
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      [ByteArray.empty, sig] chk .witnessV0
      (default : ScriptExecutionData)
    = Except.error .negativeLocktime := by
  unfold evalScriptBytes
  have hsz : (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)).size = 77 :=
    serializeOpcodes_toLocal_size revocationKey delayedPaymentKey csv hr hd
  rw [ite_eq_right (by simp [hsz, MAX_SCRIPT_SIZE])]
  rw [toLocal_parseWire revocationKey delayedPaymentKey csv hr hd]
  simp [finalStack,
    evalFrom_toLocalWireOps_delayed_negative chk revocationKey delayedPaymentKey csv
      sig n hr hd hdec hn]

theorem executeWitnessScript_toLocal_delayed_negative (chk : ScriptChecker)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (n : Bitcoin.Numeric.ScriptNum) (vwSer : Int)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hdec : decodeNum ({} : PolicyFlags) (delayBytes csv) 5 = .ok n)
    (hn : n < 0) :
    executeWitnessScript 10 [sig, ByteArray.empty] vwSer
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      ({ csv := true } : ScriptFlags) ({} : PolicyFlags) chk .witnessV0
    = .fail .negativeLocktime := by
  have hsig' : ¬ Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE < sig.size := by
    unfold Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE; omega
  simp [executeWitnessScript, executeWitnessScript.runExec,
    evalScriptBytes_toLocal_delayed_negative chk revocationKey delayedPaymentKey csv
      sig n hr hd hdec hn, hsig']

theorem verifyWitnessProgram_toLocal_delayed_negative (chk : ScriptChecker)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (n : Bitcoin.Numeric.ScriptNum) (program : ByteArray)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hdec : decodeNum ({} : PolicyFlags) (delayBytes csv) 5 = .ok n)
    (hn : n < 0)
    (hps : program.size = 32)
    (hprog : hashSha256
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)) = program) :
    verifyWitnessProgram 10
      [sig, ByteArray.empty,
        serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)]
      0 program ({ csv := true } : ScriptFlags) ({} : PolicyFlags) chk false
    = .fail .negativeLocktime := by
  simp [verifyWitnessProgram, hps, hprog, byteArray_bne_self,
    executeWitnessScript_toLocal_delayed_negative chk revocationKey delayedPaymentKey
      csv sig n
      (witnessSerSize [sig, ByteArray.empty,
        serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)])
      hr hd hsigsz hdec hn]

/-- **The `csv ≥ 32768` limitation at the pipeline checker.**  For a BOLT 2
`u16` delay in `[32768, 65536)`, the scaffold's fixed two-byte payload
decodes as a negative `CScriptNum`, so the vendored `OP_CSV` rejects it with
`.fail .negativeLocktime` — irrespective of the sequence environment and the
signature.  At exactly `csv = 32768` the sign-magnitude decoding is negative
zero, i.e. the delay collapses to `0` (see `decodeNum_delayBytes_32768`), so the
strict bound `32768 < csv` is what produces the negative locktime.  This is a
faithful rejection of the fixed-width *encoding*, not a
consensus-spendability result for BOLT 3 (whose script number encoding is
minimal). -/
theorem toLocal_delayed_high_negativeLocktime
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (program : ByteArray)
    (hlo : 32768 < csv) (hhi : csv < 65536)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hps : program.size = 32)
    (hprog : hashSha256
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)) = program) :
    verifyWitnessProgram 10
      [sig, ByteArray.empty,
        serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)]
      0 program ({ csv := true } : ScriptFlags) ({} : PolicyFlags)
      (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount)) false
    = .fail .negativeLocktime := by
  have hdec := decodeNum_delayBytes_high csv (Nat.le_of_lt hlo) hhi
  have hlt : (32768 : Int) < (csv : Int) := Int.ofNat_lt.mpr hlo
  have hn : ((32768 : Int) - (csv : Int)) < 0 := by omega
  exact verifyWitnessProgram_toLocal_delayed_negative
    (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount))
    revocationKey delayedPaymentKey csv sig ((32768 : Int) - (csv : Int)) program
    hr hd hsigsz hdec hn hps hprog

/-! ## 7. Tx-level transfer: the script lane and the full pipeline -/

/-- **The script lane runs the real checker.**  Whenever `scriptLaneTx`
accepts, every input whose resolved prevout carries a known amount was
verified by `verifyScriptFull` at `realCheckerOf tx k amount`.  This is the
vendor `scriptLaneTx_true_all_ok` composed with the checker equality. -/
theorem scriptLaneTx_true_all_ok_realChecker
    (tx : Bitcoin.Data.Tx) (tbl : Bitcoin.Data.OutPoint → Option Bitcoin.TxValidation.Full.ScriptEntry)
    (flags : ScriptFlags) (pol : PolicyFlags)
    (h : Bitcoin.TxValidation.Full.scriptLaneTx tx tbl flags pol = some true) :
    ∀ (k : Nat) (i : Bitcoin.Data.TxIn) (spk : ByteArray) (amount : Amount),
      tx.vin[k]? = some i → tbl i.prevout = some (spk, some amount) →
      verifyScriptFull
        (Bitcoin.TxValidation.Full.pipelineFuel i.scriptSig.bytes spk
          (tx.witness.getD k []))
        flags pol i.scriptSig.bytes spk (tx.witness.getD k [])
        (Bitcoin.Capstone.RealChecker.realCheckerOf tx k amount) = .ok := by
  intro k i spk amount hget htbl
  obtain ⟨spk', amt, htbl', hok⟩ :=
    Bitcoin.TxValidation.Full.scriptLaneTx_true_all_ok tx tbl flags pol h k i hget
  rw [htbl] at htbl'
  cases htbl'
  rw [txCheckerFor_some_eq_realCheckerOf] at hok
  exact hok

/-- **The full pipeline runs the real checker.**  If `txVerdictFull` accepts a
non-coinbase transaction, every input whose prevout carries a known amount
was verified by `verifyScriptFull` at `realCheckerOf`.  This composes
`txVerdictFull_accept_sound` with the script-lane transfer above.  It does not
claim that the pipeline's accept is consensus spendability (the fee/context
layers and the saturation caveats of the vendor pipeline remain). -/
theorem txVerdictFull_accept_realChecker
    (tx : Bitcoin.Data.Tx) (tbl : Bitcoin.Data.OutPoint → Option Bitcoin.TxValidation.Full.ScriptEntry)
    (u : Bitcoin.Ledger.UtxoSet) (spendHeight : UInt32)
    (flags : ScriptFlags) (pol : PolicyFlags)
    (h : Bitcoin.TxValidation.Full.txVerdictFull tx tbl u spendHeight flags pol
      = some true) :
    Bitcoin.Consensus.checkTransaction tx = none ∧
      (tx.isCoinBase = true ∨
        (Bitcoin.TxValidation.Full.tableSupplied tx tbl = true ∧
          (Bitcoin.TxValidation.Full.tableAmountsKnown tx tbl = false ∨
            Bitcoin.TxValidation.Full.feeOk tx u spendHeight = true) ∧
          ∀ (k : Nat) (i : Bitcoin.Data.TxIn) (spk : ByteArray) (amount : Amount),
            tx.vin[k]? = some i → tbl i.prevout = some (spk, some amount) →
            verifyScriptFull
              (Bitcoin.TxValidation.Full.pipelineFuel i.scriptSig.bytes spk
                (tx.witness.getD k []))
              flags pol i.scriptSig.bytes spk (tx.witness.getD k [])
              (Bitcoin.Capstone.RealChecker.realCheckerOf tx k amount) = .ok)) := by
  have hs := Bitcoin.TxValidation.Full.txVerdictFull_accept_sound
    tx tbl u spendHeight flags pol h
  refine ⟨hs.1, ?_⟩
  rcases hs.2 with hcb | ⟨hsup, hfee, hlane⟩
  · exact Or.inl hcb
  · exact Or.inr ⟨hsup, hfee,
      scriptLaneTx_true_all_ok_realChecker tx tbl flags pol hlane⟩

/-! ## 8. Summary

The pipeline checker `txCheckerFor tx nIn (some amount)` is exactly the
capstone `realCheckerOf tx nIn amount`, so the wave-7 sequence refinement and
the wave-6 revocation agreement hold at the checker the transaction pipeline
actually builds.  The two boundaries are mechanized rather than assumed:
missing amounts fail closed, `minimalData = true` rejects the short
fixed-width delay payload as non-minimal, and for `csv > 32768` the
fixed-width encoding decodes a negative locktime (while `csv = 32768`
collapses to `0`). -/

end LnLean.Proofs.Bitcoin.TxValidTransferTargets
