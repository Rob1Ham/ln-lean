/-
# H31 — the delayed `to_local` branch at `Bitcoin.TxValidation.Full.txCheckerFor`
(L1-02, L1-07)

**Catalog issues.**

* `L1-02` (P0): the `to_local` CSV/spend had a remaining transaction-validity
  transfer boundary.  Wave 7 (`SequenceContextTargets`) proved
  `toLocal_delayed_realChecker_refinement` at
  `Bitcoin.Capstone.RealChecker.realCheckerOf`, i.e. at the capstone block
  layer, but the *full* per-transaction pipeline
  (`Bitcoin.TxValidation.Full.txCheckerFor`, the checker `txVerdictFull`
  actually runs) was still unbridged.
* `L1-07` (P0): the vendored real interpreter is imported for the positive L1
  branches, but only up to `realCheckerOf`.

## Result of this module

1. `txCheckerFor_some_eq_realCheckerOf`: **the checker equality**.  For every
   transaction, input index and spent amount,
   `txCheckerFor tx nIn (some amount) = realCheckerOf tx nIn amount`.  The
   proof is local: `txCheckerFor` assembles the ECDSA *and* Schnorr entries via
   `txCheckerOf`, while `realCheckerOf` carries only `ecdsaEntry`; the Schnorr
   slots agree because `txCheckerFor`'s BIP 342 sighash is the fail-closed
   `fun _ _ _ => none` stand-in, so `schnorrVerdict` is constantly `false`
   (`schnorrVerdict_failClosed`), the same value `ecdsaEntry` puts in that
   slot.  Both share `Bitcoin.Capstone.RealChecker.dummyTxIn`, so **no**
   in-range hypothesis is needed for the equality itself.
2. `txCheckerFor_ecdsa_eq_model_verify` / `..._iff_model_verify`: the
   `txCheckerFor` witness-v0 ECDSA entry, with `some amount`, is exactly
   `Bitcoin.Crypto.Ecdsa.Verify.verifyImpl` over the BIP 143 model digest
   `LnLean.Bitcoin.Sighash.sighashWitnessV0` (the vendor's
   `sighashDispatch` at `WITNESS_V0` is the same BIP 143 hash).
3. `toLocal_delayed_txCheckerFor_sequence_context_refinement`: the generic
   vendor iff instantiated at `txCheckerFor tx nIn (some amount)` — acceptance
   iff the five BIP 68/112 context conditions and the checker's own
   delayed-key signature check hold.
4. `toLocal_delayed_txCheckerFor_refinement`: the same iff with the signature
   premise replaced by the **concrete vendor verifier**
   `Bitcoin.Crypto.Ecdsa.Verify.verifyImpl` over the BIP 143 digest.  This is
   `toLocal_delayed_realChecker_refinement` transferred to `txCheckerFor`.
   The sequence context is read from `tx.vin[nIn]` rather than through a
   `getD` totalization (`txCheckerFor_env_txSequence`), which is what makes the
   in-range premise `nIn < tx.vin.length` do real work.
5. The two directions as named corollaries:
   `toLocal_delayed_txCheckerFor_ok_of_context` (context + valid signature ⇒
   vendor `.ok`) and `toLocal_delayed_txCheckerFor_not_ok_of_bad_sig` (a
   rejected concrete verifier call ⇒ the branch is not `.ok`).
7. `getD_eq_getElem`, `txCheckerFor_env_txSequence_outOfRange`,
   `sighashDummy_sequence_outOfRange` and
   `txCheckerFor_env_txSequence_ne_sighashDummy_outOfRange`: the sequence-context
   plumbing, including the mechanized proof that the in-range premise is not
   removable (the two `getD` stand-ins differ out of range).
8. `txCheckerFor_none_ecdsa_false` and
   `toLocal_delayed_txCheckerFor_none_not_ok`: the **missing-data** state
   (`amount = none`, the corpus's `-1` sentinel) fails closed on a witness-v0
   `OP_CHECKSIG`, so the delayed witness can never be accepted without the
   spent amount — independently of the sequence context.

## Explicit premises (none of these is discharged here)

* `hcsv : csv < 32768` — the fixed-width two-byte delay must decode
  non-negatively (BIP 68 value range; `csv ≥ 32768` is tracked by lane H06).
* `hr`, `hd` — the revocation and delayed-payment keys are 33-byte compressed
  pubkeys, i.e. the exact serialized `to_local` script length is 77 bytes.
* `hsigsz : sig.size ≤ 520` — the witness-element consensus limit.
* `hprog : hashSha256 (serializeOpcodes ...) = program` — the P2WSH script
  hash premise: the spent output commits to the BOLT 3 `to_local` witness
  script.  The 32-byte program-size side condition is *derived* from it
  (`hashSha256_size`).
* `hpk` — the delayed key passes `Der.isValidPubKey`; `hne : 0 < sig.size` —
  non-empty signature.  Together they are exactly what is needed to reach the
  EC math through the seam adapter (`ecdsaEntry_pops_hashtype`).
* `hIn : nIn < tx.vin.length` — the signing input is in range.  It is used
  only to identify the sequence context across the two `dummyTxIn`
  totalizations (`LnLean.Bitcoin.Sighash.dummyTxIn` versus
  `Bitcoin.Capstone.RealChecker.dummyTxIn`), which differ out of range
  (`0` versus `0xFFFFFFFF`).
* `amount : Amount` is an explicit *spent-output* value, committed to by the
  BIP 143 preimage; this module does not claim it equals the value of the
  referenced outpoint.

## Flag / policy boundary

The script lane is the P2WSH witness path `verifyWitnessProgram` with the
consensus flag word `({ csv := true } : ScriptFlags)` and the default policy
word.  That literal word is the one wave 7 mechanized and is the *minimal*
consensus word for this branch: `OP_CSV` reads `flags.csv`, and with
`dersig = false` the `OP_CHECKSIG` encoding gate is inert (no BIP 66 DER
premise is needed).  A block-flags instantiation (`getBlockScriptFlags h`,
which sets `dersig`, `p2sh`, `witness`, ... for heights at/above the soft-fork
activations) would additionally need `isValidSigEncoding sig = true` for the
DER gate; that transfer is **not** mechanized here.  CSV activation itself is
`getBlockScriptFlags_csv_of_csvHeight_le` (wave 7).
-/

import Bitcoin.TxValidation.Full
import LnLean.Proofs.Bitcoin.SequenceContextTargets

namespace LnLean.Proofs.WaveH.H31

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
open LnLean.Proofs.Bitcoin.SighashBridgeTargets
open LnLean.Proofs.Bitcoin.SequenceContextTargets

/-! ## 1. The checker equality `txCheckerFor tx nIn (some amount) = realCheckerOf` -/

/-- The Schnorr slot of `txCheckerFor` is the fail-closed stand-in
(`sighashSchnorr = fun _ _ _ => none`), so the vendored `schnorrVerdict` is
constantly `false` — the very value `ecdsaEntry` puts in the same field.  This
is what makes the ECDSA-only `realCheckerOf` and the two-entry `txCheckerOf`
assembly the same checker. -/
theorem schnorrVerdict_failClosed (verify : ByteArray → ByteArray → ByteArray → Bool)
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

/-- **The full-pipeline checker is the capstone real checker.**  At a
supplied amount (`some amount`), `Bitcoin.TxValidation.Full.txCheckerFor`
— the per-input checker the `txVerdictFull` script lane runs — is *literally*
`Bitcoin.Capstone.RealChecker.realCheckerOf`, the checker wave 7 refined the
delayed `to_local` branch at.  Both use the lax secp256k1 verifier over the
same BIP 143/legacy sighash dispatch and the same transaction-derived
`LocktimeEnv`; the only difference is the Schnorr field, and there the
`txCheckerFor` BIP 342 slot is the fail-closed `none` stand-in, i.e.
extensionally `false`.

No in-range premise is needed: `txCheckerFor` and `realCheckerOf` both index
`tx.vin` with `Bitcoin.Capstone.RealChecker.dummyTxIn`. -/
theorem txCheckerFor_some_eq_realCheckerOf (tx : Bitcoin.Data.Tx) (nIn : Nat)
    (amount : Amount) :
    Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount) =
      Bitcoin.Capstone.RealChecker.realCheckerOf tx nIn amount := by
  have hbase :
      (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount)).base =
        (Bitcoin.Capstone.RealChecker.realCheckerOf tx nIn amount).base := by
    simp only [Bitcoin.TxValidation.Full.txCheckerFor,
      Bitcoin.Capstone.RealChecker.realCheckerOf,
      Bitcoin.Capstone.RealChecker.realEcdsaEntry,
      Bitcoin.Crypto.Seam.Entry.txCheckerOf,
      Bitcoin.Crypto.Seam.Entry.ecdsaEntry, Option.getD_some, Option.isSome_some]
    refine (Bitcoin.Crypto.Seam.BaseSignatureChecker.mk.injEq _ _ _ _).mpr ⟨rfl, ?_⟩
    funext sig pk v d
    exact schnorrVerdict_failClosed _ sig pk v d
  have henv :
      (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount)).env =
        (Bitcoin.Capstone.RealChecker.realCheckerOf tx nIn amount).env := rfl
  have hL : Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount) =
      Bitcoin.Interpreter.ScriptChecker.mk
        (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount)).base
        (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount)).env := rfl
  have hR : Bitcoin.Capstone.RealChecker.realCheckerOf tx nIn amount =
      Bitcoin.Interpreter.ScriptChecker.mk
        (Bitcoin.Capstone.RealChecker.realCheckerOf tx nIn amount).base
        (Bitcoin.Capstone.RealChecker.realCheckerOf tx nIn amount).env := rfl
  rw [hL, hR, hbase, henv]

/-- `getD` at an in-range index is the indexed input, for *any* stand-in.
This erases the totalization: the wave-5/7 statements index with
`LnLean.Bitcoin.Sighash.dummyTxIn` (sequence `0`) while the checker indexes
with `Bitcoin.Capstone.RealChecker.dummyTxIn` (sequence `0xFFFFFFFF`), and only
the in-range case identifies their `nSequence`.  The two stand-ins genuinely
differ out of range (`txCheckerFor_env_txSequence_ne_sighashDummy_outOfRange`),
which is why the transfer to `txCheckerFor` keeps `nIn < tx.vin.length`
explicit. -/
theorem getD_eq_getElem (tx : Bitcoin.Data.Tx) (nIn : Nat) (d : Bitcoin.Data.TxIn)
    (hIn : nIn < tx.vin.length) :
    tx.vin.getD nIn d = tx.vin[nIn] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hIn]
  rfl

/-- The `txCheckerFor` locktime environment carries the transaction version. -/
theorem txCheckerFor_env_txVersion (tx : Bitcoin.Data.Tx) (nIn : Nat)
    (amount : Amount) :
    (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount)).env.txVersion =
      tx.version := rfl

/-- The `txCheckerFor` locktime environment carries the transaction locktime. -/
theorem txCheckerFor_env_txLockTime (tx : Bitcoin.Data.Tx) (nIn : Nat)
    (amount : Amount) :
    (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount)).env.txLockTime =
      tx.locktime := rfl

/-- For an in-range input, the `txCheckerFor` sequence context is exactly the
signing input's `nSequence` — the BIP 68/112 field, read from `tx.vin[nIn]`
rather than from either `getD` stand-in. -/
theorem txCheckerFor_env_txSequence (tx : Bitcoin.Data.Tx) (nIn : Nat)
    (amount : Amount) (hIn : nIn < tx.vin.length) :
    (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount)).env.txSequence =
      tx.vin[nIn].sequence :=
  congrArg Bitcoin.Data.TxIn.sequence
    (getD_eq_getElem tx nIn Bitcoin.Capstone.RealChecker.dummyTxIn hIn)

/-- Out of range, the checker's sequence context is the `SEQUENCE_FINAL`
stand-in (`0xFFFFFFFF`) of `Bitcoin.Capstone.RealChecker.dummyTxIn`, not an
input's `nSequence`. -/
theorem txCheckerFor_env_txSequence_outOfRange (tx : Bitcoin.Data.Tx) (nIn : Nat)
    (amount : Amount) (h : tx.vin.length ≤ nIn) :
    (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount)).env.txSequence =
      0xFFFFFFFF := by
  show (tx.vin.getD nIn Bitcoin.Capstone.RealChecker.dummyTxIn).sequence = 0xFFFFFFFF
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

/-- Out of range, the wave-5/7 totalization reads sequence `0`. -/
theorem sighashDummy_sequence_outOfRange (tx : Bitcoin.Data.Tx) (nIn : Nat)
    (h : tx.vin.length ≤ nIn) :
    (tx.vin.getD nIn dummyTxIn).sequence = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

/-- **The in-range premise is not removable.**  Out of range the checker's
sequence context (`0xFFFFFFFF`) is *not* the sequence of the wave-7
totalization (`0`), so no statement about "the signing input's `nSequence`"
can be made without `nIn < tx.vin.length`. -/
theorem txCheckerFor_env_txSequence_ne_sighashDummy_outOfRange
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount)
    (h : tx.vin.length ≤ nIn) :
    (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount)).env.txSequence ≠
      (tx.vin.getD nIn dummyTxIn).sequence := by
  rw [txCheckerFor_env_txSequence_outOfRange tx nIn amount h,
    sighashDummy_sequence_outOfRange tx nIn h]
  decide

/-! ## 2. The concrete verifier over the BIP 143 model digest -/

/-- At `some amount` and `WITNESS_V0`, the `txCheckerFor` ECDSA entry is
exactly the vendored lax verifier `Bitcoin.Crypto.Ecdsa.Verify.verifyImpl`
applied to `sig` minus its hashtype byte, the delayed key, and the BIP 143
model digest `sighashWitnessV0` over the `to_local` script code and the spent
amount.  The vendor's `sighashDispatch` computes the same BIP 143 hash at
`WITNESS_V0`, and `hashtypeOf` is exactly the vendor's `htToU32` of the
popped byte. -/
theorem txCheckerFor_ecdsa_eq_model_verify (tx : Bitcoin.Data.Tx) (nIn : Nat)
    (amount : Amount) (sig pk scriptCode : ByteArray)
    (ed : Bitcoin.Crypto.Seam.ScriptExecutionData)
    (hpk : Bitcoin.Crypto.Seam.Der.isValidPubKey pk = true) (hne : 0 < sig.size) :
    (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount)).base.checkECDSASignature
        sig pk scriptCode .witnessV0 ed
      = Bitcoin.Crypto.Ecdsa.Verify.verifyImpl (sig.extract 0 (sig.size - 1)) pk
          (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn scriptCode
            (hashtypeOf sig) amount) := by
  rw [txCheckerFor_some_eq_realCheckerOf]
  show (ecdsaEntry Bitcoin.Crypto.Ecdsa.Verify.verifyImpl
      (Bitcoin.Capstone.RealChecker.sighashDispatch tx nIn amount)
      true).checkECDSASignature sig pk scriptCode .witnessV0 ed = _
  rw [ecdsaEntry_pops_hashtype Bitcoin.Crypto.Ecdsa.Verify.verifyImpl
    (Bitcoin.Capstone.RealChecker.sighashDispatch tx nIn amount) true
    sig pk scriptCode .witnessV0 ed hpk hne (by intro _; rfl)]
  simp [Bitcoin.Capstone.RealChecker.sighashDispatch,
    Bitcoin.Capstone.RealChecker.htToU32, hashtypeOf,
    LnLean.Bitcoin.Sighash.sighashWitnessV0_eq_interface]

/-- The iff face of the preceding equality: the checker's own witness-v0
signature premise is equivalent to the concrete verifier call over the model
digest. -/
theorem txCheckerFor_ecdsa_iff_model_verify (tx : Bitcoin.Data.Tx) (nIn : Nat)
    (amount : Amount) (sig pk scriptCode : ByteArray)
    (ed : Bitcoin.Crypto.Seam.ScriptExecutionData)
    (hpk : Bitcoin.Crypto.Seam.Der.isValidPubKey pk = true) (hne : 0 < sig.size) :
    ((Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount)).base.checkECDSASignature
        sig pk scriptCode .witnessV0 ed = true) ↔
      Bitcoin.Crypto.Ecdsa.Verify.verifyImpl (sig.extract 0 (sig.size - 1)) pk
        (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn scriptCode
          (hashtypeOf sig) amount) = true := by
  rw [txCheckerFor_ecdsa_eq_model_verify tx nIn amount sig pk scriptCode ed hpk hne]

/-! ## 3. The delayed branch iff at `txCheckerFor` -/

/-- **Vendored sequence-context iff at the full-pipeline checker.**  The
delayed `to_local` witness is accepted by `verifyWitnessProgram` with
`txCheckerFor tx nIn (some amount)` exactly when (i) the *checker's* delayed-key
signature check succeeds and (ii) the five sequence/context conditions hold:
transaction version ≥ 2, the signing input's disable bit is clear, the masked
sequence is in the height domain, and `csv` does not exceed the masked
sequence — all read from the exact signing input `tx.vin[nIn]`.

The only wave-5/7 side conditions kept are the ones about the delayed script
itself: `csv < 32768`, 33-byte keys, the witness-element size bound and the
P2WSH script hash (whose 32-byte program-size consequence is derived from
`hashSha256_size`). -/
theorem toLocal_delayed_txCheckerFor_sequence_context_refinement
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount)
    (hIn : nIn < tx.vin.length)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (program : ByteArray) (hcsv : csv < 32768)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hprog : hashSha256
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)) = program) :
    verifyWitnessProgram 10
      [sig, ByteArray.empty,
        serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)]
      0 program ({ csv := true } : ScriptFlags) ({} : PolicyFlags)
      (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount)) false = .ok ↔
      ((¬ tx.version < 2) ∧
        (tx.vin[nIn].sequence.toNat &&& SEQUENCE_LOCKTIME_DISABLE_FLAG) = 0 ∧
        (tx.vin[nIn].sequence.toNat &&&
            (SEQUENCE_LOCKTIME_TYPE_FLAG ||| SEQUENCE_LOCKTIME_MASK)) <
          SEQUENCE_LOCKTIME_TYPE_FLAG ∧
        csv ≤ (tx.vin[nIn].sequence.toNat &&&
            (SEQUENCE_LOCKTIME_TYPE_FLAG ||| SEQUENCE_LOCKTIME_MASK)) ∧
        (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount)).base.checkECDSASignature
          sig delayedPaymentKey.bytes
          (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
          .witnessV0 (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true) := by
  have h := toLocal_delayed_sequence_context_refinement
    (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount))
    revocationKey delayedPaymentKey csv sig program hcsv hr hd hsigsz
    (by rw [← hprog]; exact hashSha256_size _) hprog
  rw [txCheckerFor_env_txVersion tx nIn amount,
    txCheckerFor_env_txSequence tx nIn amount hIn] at h
  exact h

/-- **Delayed `to_local` refinement at `txCheckerFor` with the concrete vendor
ECDSA verifier.**  This is the statement of
`SequenceContextTargets.toLocal_delayed_realChecker_refinement` transported to
the checker the full transaction-validity pipeline actually runs
(`txCheckerFor tx nIn (some amount)`).  Mechanically the module composes wave
7's generic `toLocal_delayed_sequence_context_refinement` at `txCheckerFor`
with the digest identification `txCheckerFor_ecdsa_iff_model_verify`; that
identification is itself derived from the local checker equality
`txCheckerFor_some_eq_realCheckerOf`, which is what makes the two left-hand
sides — `realCheckerOf` and `txCheckerFor` — the same checker.

For an in-range signing input the branch is accepted exactly when the exact
BIP 68/112 sequence context holds and the vendored lax secp256k1 verifier
accepts `(sig minus hashtype, delayed key, BIP 143 digest)` over the `to_local`
script code and the spent amount. -/
theorem toLocal_delayed_txCheckerFor_refinement
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount)
    (hIn : nIn < tx.vin.length)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (program : ByteArray) (hcsv : csv < 32768)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
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
        (tx.vin[nIn].sequence.toNat &&& SEQUENCE_LOCKTIME_DISABLE_FLAG) = 0 ∧
        (tx.vin[nIn].sequence.toNat &&&
            (SEQUENCE_LOCKTIME_TYPE_FLAG ||| SEQUENCE_LOCKTIME_MASK)) <
          SEQUENCE_LOCKTIME_TYPE_FLAG ∧
        csv ≤ (tx.vin[nIn].sequence.toNat &&&
            (SEQUENCE_LOCKTIME_TYPE_FLAG ||| SEQUENCE_LOCKTIME_MASK)) ∧
        Bitcoin.Crypto.Ecdsa.Verify.verifyImpl (sig.extract 0 (sig.size - 1))
          delayedPaymentKey.bytes
          (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn
            (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
            (hashtypeOf sig) amount) = true) := by
  rw [toLocal_delayed_txCheckerFor_sequence_context_refinement tx nIn amount hIn
    revocationKey delayedPaymentKey csv sig program hcsv hr hd hsigsz hprog]
  rw [txCheckerFor_ecdsa_iff_model_verify tx nIn amount sig delayedPaymentKey.bytes
    (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
    (default : Bitcoin.Crypto.Seam.ScriptExecutionData) hpk hne]

/-! ## 4. The two directions, named -/

/-- **Acceptance.**  Exact sequence context plus a verified concrete ECDSA call
yields vendor `.ok` for the delayed branch at the full-pipeline checker. -/
theorem toLocal_delayed_txCheckerFor_ok_of_context
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount)
    (hIn : nIn < tx.vin.length)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (program : ByteArray) (hcsv : csv < 32768)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hprog : hashSha256
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)) = program)
    (hpk : Bitcoin.Crypto.Seam.Der.isValidPubKey delayedPaymentKey.bytes = true)
    (hne : 0 < sig.size)
    (hctx : (¬ tx.version < 2) ∧
      (tx.vin[nIn].sequence.toNat &&& SEQUENCE_LOCKTIME_DISABLE_FLAG) = 0 ∧
      (tx.vin[nIn].sequence.toNat &&&
          (SEQUENCE_LOCKTIME_TYPE_FLAG ||| SEQUENCE_LOCKTIME_MASK)) <
        SEQUENCE_LOCKTIME_TYPE_FLAG ∧
      csv ≤ (tx.vin[nIn].sequence.toNat &&&
          (SEQUENCE_LOCKTIME_TYPE_FLAG ||| SEQUENCE_LOCKTIME_MASK)) ∧
      Bitcoin.Crypto.Ecdsa.Verify.verifyImpl (sig.extract 0 (sig.size - 1))
        delayedPaymentKey.bytes
        (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn
          (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
          (hashtypeOf sig) amount) = true) :
    verifyWitnessProgram 10
      [sig, ByteArray.empty,
        serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)]
      0 program ({ csv := true } : ScriptFlags) ({} : PolicyFlags)
      (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount)) false = .ok :=
  (toLocal_delayed_txCheckerFor_refinement tx nIn amount hIn revocationKey
    delayedPaymentKey csv sig program hcsv hr hd hsigsz hprog hpk hne).mpr hctx

/-- **Rejection (concrete bad signature).**  If the vendored verifier rejects
the delayed-key signature over the BIP 143 digest, the delayed branch cannot be
accepted by the full-pipeline checker — whatever the sequence context. -/
theorem toLocal_delayed_txCheckerFor_not_ok_of_bad_sig
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount)
    (hIn : nIn < tx.vin.length)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (program : ByteArray) (hcsv : csv < 32768)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hprog : hashSha256
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)) = program)
    (hpk : Bitcoin.Crypto.Seam.Der.isValidPubKey delayedPaymentKey.bytes = true)
    (hne : 0 < sig.size)
    (hbad : Bitcoin.Crypto.Ecdsa.Verify.verifyImpl (sig.extract 0 (sig.size - 1))
      delayedPaymentKey.bytes
      (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn
        (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
        (hashtypeOf sig) amount) = false) :
    verifyWitnessProgram 10
      [sig, ByteArray.empty,
        serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)]
      0 program ({ csv := true } : ScriptFlags) ({} : PolicyFlags)
      (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount)) false ≠ .ok := by
  intro hok
  have hctx := (toLocal_delayed_txCheckerFor_refinement tx nIn amount hIn
    revocationKey delayedPaymentKey csv sig program hcsv hr hd hsigsz hprog
    hpk hne).mp hok
  rw [hbad] at hctx
  exact absurd hctx.2.2.2.2 (by simp)

/-! ## 5. The missing-data (`amount = none`) state fails closed -/

/-- With `amount = none` — the corpus's `-1` "amount omitted" sentinel, i.e.
the checker's `amount < 0` missing-data state — the `txCheckerFor` ECDSA entry
fails closed on a witness-v0 signature (`hasAmount = false` in the seam entry,
matching Core's `HandleMissingData`). -/
theorem txCheckerFor_none_ecdsa_false (tx : Bitcoin.Data.Tx) (nIn : Nat)
    (sig pk scriptCode : ByteArray) (ed : Bitcoin.Crypto.Seam.ScriptExecutionData)
    (hpk : Bitcoin.Crypto.Seam.Der.isValidPubKey pk = true) (hne : 0 < sig.size) :
    (Bitcoin.TxValidation.Full.txCheckerFor tx nIn none).base.checkECDSASignature
        sig pk scriptCode .witnessV0 ed = false := by
  simp only [Bitcoin.TxValidation.Full.txCheckerFor, Bitcoin.Crypto.Seam.Entry.txCheckerOf]
  exact ecdsaEntry_witnessV0_missing_amount_false Bitcoin.Crypto.Ecdsa.Verify.verifyImpl
    (Bitcoin.Capstone.RealChecker.sighashDispatch tx nIn 0) sig pk scriptCode ed hpk hne

/-- **Missing-data rejection.**  Without the spent amount the delayed witness is
never accepted by the full-pipeline checker, regardless of the sequence
context and of the signature bytes: the witness-v0 `OP_CHECKSIG` fails closed
before any EC math.  Supplying the spent amount is therefore a *necessary*
condition for the delayed branch, not a convenience. -/
theorem toLocal_delayed_txCheckerFor_none_not_ok
    (tx : Bitcoin.Data.Tx) (nIn : Nat)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (program : ByteArray) (hcsv : csv < 32768)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
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
  have hctx := (toLocal_delayed_sequence_context_refinement
    (Bitcoin.TxValidation.Full.txCheckerFor tx nIn none)
    revocationKey delayedPaymentKey csv sig program hcsv hr hd hsigsz
    (by rw [← hprog]; exact hashSha256_size _) hprog).mp hok
  have hfalse := txCheckerFor_none_ecdsa_false tx nIn sig delayedPaymentKey.bytes
    (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
    (default : Bitcoin.Crypto.Seam.ScriptExecutionData) hpk hne
  rw [hfalse] at hctx
  exact absurd hctx.2.2.2.2 (by simp)

/-! ## 6. Axiom pins -/

#print axioms schnorrVerdict_failClosed
#print axioms txCheckerFor_some_eq_realCheckerOf
#print axioms txCheckerFor_ecdsa_eq_model_verify
#print axioms toLocal_delayed_txCheckerFor_sequence_context_refinement
#print axioms toLocal_delayed_txCheckerFor_refinement
#print axioms toLocal_delayed_txCheckerFor_ok_of_context
#print axioms toLocal_delayed_txCheckerFor_not_ok_of_bad_sig
#print axioms txCheckerFor_none_ecdsa_false
#print axioms toLocal_delayed_txCheckerFor_none_not_ok
#print axioms txCheckerFor_env_txSequence_ne_sighashDummy_outOfRange

end LnLean.Proofs.WaveH.H31
