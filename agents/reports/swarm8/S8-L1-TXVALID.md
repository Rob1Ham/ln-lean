# S8-L1-TXVALID — `txCheckerFor` transfer, missing amount, `minimalData`, and `csv ≥ 32768`

**Lane:** `S8-L1-TXVALID` (`L1-02`, `L1-07` transfer boundary).
**Repository:** `/home/ubuntu/ln-lean-repair`
**Branch / base:** `repair/integrated` @ `3953c8c` (working tree; no Git writes).
**Verdict:** **proved for the assigned conditional scope / narrowed at two
modelling boundaries.**  For a **known** spent amount, the transaction
pipeline checker `Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount)`
is *exactly* `Bitcoin.Capstone.RealChecker.realCheckerOf tx nIn amount` as a
`ScriptChecker`, so the wave-6/7 revocation and delayed refinements transfer
verbatim.  The missing-amount case is mechanized as fail-closed, not assumed.
The `minimalData` and `csv ≥ 32768` edges are modeled as exact decode/verdict
results, including the previously unstated collapse at `csv = 32768`.

- Lane file (exclusive ownership, new):
  - `LnLean/Proofs/Bitcoin/TxValidTransferTargets.lean` — 1133 lines.
  - `agents/reports/swarm8/S8-L1-TXVALID.md` — this report.
- Not modified: `LnLean.lean`, `Obligations.lean`, `Traceability.lean`,
  `AxiomAudit.lean`, `SequenceContextTargets.lean`,
  `InterpreterRevocationTargets.lean`, `InterpreterBridgeTargets.lean`,
  `SighashBridgeTargets.lean`, shared docs/scripts, other lanes' files,
  `vendor/**`.  No Git write command was run.

## 1. Result in one paragraph

The wave-7 delayed refinement and the wave-6 revocation agreement were stated
at `Bitcoin.Crypto.Seam.Entry.checkerOf` / `Bitcoin.Capstone.RealChecker.realCheckerOf`,
but the actual pipeline builds
`Bitcoin.TxValidation.Full.txCheckerFor tx nIn amount?`.  This lane closes that
last transfer boundary.  The key structural fact is that the pipeline's ECDSA
entry is literally the capstone `realEcdsaEntry` (same `verifyImpl`,
`sighashDispatch`, `hashtypeOf`, transaction environment), the pipeline's
Schnorr entry is extensionally the constant `false` (the BIP 342 sighash slot
is `fun _ _ _ => none`), and `(some amount).getD 0 = amount`,
`(some amount).isSome = true`.  Hence
`txCheckerFor tx nIn (some amount) = realCheckerOf tx nIn amount` holds with
**no input-range hypothesis**; `hIn : nIn < tx.vin.length` is needed only when
composing with the wave-7 model checker `checkerOf`, because the two `getD`
totalizations use different out-of-range dummy `TxIn`s.  Missing amounts are
handled by the pipeline's existing fail-closed ECDSA entry, and the two policy
edges are proved at the exact P2WSH verifier: non-minimal short delay payloads
fail `.scriptNum`, and fixed-width payloads above `32768` fail
`.negativeLocktime` (with `csv = 32768` decoding to `0`, a genuine collision).

## 2. Exact theorem signatures

### 2.1 Checker equality and ECDSA entry

```lean
theorem txCheckerFor_some_eq_realCheckerOf (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount) :
    Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount) =
      Bitcoin.Capstone.RealChecker.realCheckerOf tx nIn amount

theorem txCheckerFor_some_ecdsa_witnessV0
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount)
    (sig pk code : ByteArray) (ed : ScriptExecutionData)
    (hpk : Bitcoin.Crypto.Seam.Der.isValidPubKey pk = true)
    (hne : 0 < sig.size) :
    (Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount)).base.checkECDSASignature
        sig pk code .witnessV0 ed =
      Bitcoin.Crypto.Ecdsa.Verify.verifyImpl (sig.extract 0 (sig.size - 1)) pk
        (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn code (hashtypeOf sig) amount)

theorem txCheckerFor_some_ecdsa_witnessV0_iff
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount)
    (sig pk code : ByteArray) (ed : ScriptExecutionData)
    (hpk : Bitcoin.Crypto.Seam.Der.isValidPubKey pk = true)
    (hne : 0 < sig.size) :
    ((Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some amount)).base.checkECDSASignature
        sig pk code .witnessV0 ed = true) ↔
      Bitcoin.Crypto.Ecdsa.Verify.verifyImpl (sig.extract 0 (sig.size - 1)) pk
        (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn code (hashtypeOf sig) amount) = true
```

Also proved: the pipeline/`checkerOf` equality (with `hIn`), the environment
equality, and the clause-level ECDSA equality.

### 2.2 Missing amount (`amount = none`)

```lean
theorem txCheckerFor_none_ecdsa_witnessV0_false
    (tx : Bitcoin.Data.Tx) (nIn : Nat)
    (sig pk code : ByteArray) (ed : ScriptExecutionData)
    (hpk : Bitcoin.Crypto.Seam.Der.isValidPubKey pk = true)
    (hne : 0 < sig.size) :
    (Bitcoin.TxValidation.Full.txCheckerFor tx nIn none).base.checkECDSASignature
        sig pk code .witnessV0 ed = false

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
      (Bitcoin.TxValidation.Full.txCheckerFor tx nIn none) false ≠ .ok

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
      (Bitcoin.TxValidation.Full.txCheckerFor tx nIn none) false = .fail .evalFalse
```

### 2.3 Delayed / revocation transfer

```lean
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
            (hashtypeOf sig) amount) = true)

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
        .witnessV0 (default : ScriptExecutionData) = true

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
        .witnessV0 (default : ScriptExecutionData) = true

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
        = .fail .unsatisfiedLocktime
```

### 2.4 `minimalData = true`

```lean
theorem decodeNum_delayBytes_minimalData_true_of_128_le (pol : PolicyFlags)
    (hmin : pol.minimalData = true) (csv : Nat) (hcsv : csv < 32768)
    (h128 : 128 ≤ csv) :
    decodeNum pol (delayBytes csv) 5 = .ok (csv : Int)

theorem decodeNum_delayBytes_minimalData_true_lt_128 (pol : PolicyFlags)
    (hmin : pol.minimalData = true) (csv : Nat) (h128 : csv < 128) :
    decodeNum pol (delayBytes csv) 5 = .error .scriptNum

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
    = .fail .scriptNum

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
        (toLocalProg revocationKey delayedPaymentKey csv) [zeroByte, sig]
```

The positive chain is also exposed at each lower layer
(`evalFrom_toLocalWireOps_delayed_minimalData`,
`evalScriptBytes_toLocal_delayed_minimalData`,
`executeWitnessScript_toLocal_delayed_minimalData`,
`verifyWitnessProgram_toLocal_delayed_minimalData`), and the rejection chain
at `evalFrom` / `evalScriptBytes` / `executeWitnessScript` /
`verifyWitnessProgram` levels.

### 2.5 `csv ≥ 32768`

```lean
theorem decodeNum_delayBytes_high (csv : Nat) (hlo : 32768 ≤ csv) (hhi : csv < 65536) :
    decodeNum ({} : PolicyFlags) (delayBytes csv) 5 =
      .ok ((32768 : Int) - (csv : Int))

theorem decodeNum_delayBytes_32768 :
    decodeNum ({} : PolicyFlags) (delayBytes 32768) 5 = .ok 0

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
    = .fail .negativeLocktime
```

### 2.6 Tx-level transfer

```lean
theorem scriptLaneTx_true_all_ok_realChecker
    (tx : Bitcoin.Data.Tx)
    (tbl : Bitcoin.Data.OutPoint → Option Bitcoin.TxValidation.Full.ScriptEntry)
    (flags : ScriptFlags) (pol : PolicyFlags)
    (h : Bitcoin.TxValidation.Full.scriptLaneTx tx tbl flags pol = some true) :
    ∀ (k : Nat) (i : Bitcoin.Data.TxIn) (spk : ByteArray) (amount : Amount),
      tx.vin[k]? = some i → tbl i.prevout = some (spk, some amount) →
      verifyScriptFull
        (Bitcoin.TxValidation.Full.pipelineFuel i.scriptSig.bytes spk
          (tx.witness.getD k []))
        flags pol i.scriptSig.bytes spk (tx.witness.getD k [])
        (Bitcoin.Capstone.RealChecker.realCheckerOf tx k amount) = .ok

theorem txVerdictFull_accept_realChecker
    (tx : Bitcoin.Data.Tx)
    (tbl : Bitcoin.Data.OutPoint → Option Bitcoin.TxValidation.Full.ScriptEntry)
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
              (Bitcoin.Capstone.RealChecker.realCheckerOf tx k amount) = .ok))
```

## 3. Build result

Prerequisite vendor build (its oleans had been removed from the shared
workspace):

```
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build Bitcoin.TxValidation.Full
# Build completed successfully (38 jobs).
```

Lane build:

```
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Proofs.Bitcoin.TxValidTransferTargets
# Build completed successfully (61 jobs).
```

Only vendor deprecation warnings (`if_pos` / `if_neg` renames) and a few
unused-`simp`-argument linter notes in the lane module; no errors.

## 4. Axiom result

`#print axioms` on every headline theorem, via a scratch file importing the
module:

```
txCheckerFor_some_eq_realCheckerOf                [propext, Classical.choice, Quot.sound]
txCheckerFor_some_ecdsa_witnessV0                 [propext, Classical.choice, Quot.sound]
txCheckerFor_none_delayed_not_ok                  [propext, Classical.choice, Quot.sound]
txCheckerFor_none_revocation_fail                 [propext, Classical.choice, Quot.sound]
toLocal_delayed_txCheckerFor_refinement           [propext, Classical.choice, Quot.sound]
toLocal_delayed_txCheckerFor_interpreters_agree   [propext, Classical.choice, Quot.sound]
toLocal_revocation_txCheckerFor_interpreters_agree[propext, Classical.choice, Quot.sound]
toLocal_vendor_branch_selection_txCheckerFor      [propext, Classical.choice, Quot.sound]
toLocal_delayed_minimalData_true_scriptNum        [propext, Classical.choice, Quot.sound]
toLocal_delayed_minimalData_true_ok               [propext, Classical.choice, Quot.sound]
decodeNum_delayBytes_32768                        [propext, Quot.sound]
toLocal_delayed_high_negativeLocktime             [propext, Classical.choice, Quot.sound]
scriptLaneTx_true_all_ok_realChecker              [propext, Classical.choice, Quot.sound]
txVerdictFull_accept_realChecker                  [propext, Classical.choice, Quot.sound]
```

All within the allowed set `{propext, Quot.sound, Classical.choice}`.

## 5. Forbidden-construct scan

```
grep -nE '\b(sorry|admit|native_decide|unsafe|implemented_by)\b' \
  LnLean/Proofs/Bitcoin/TxValidTransferTargets.lean      # no matches
grep -nE '^\s*(axiom|constant)\b|@\[implemented_by' \
  LnLean/Proofs/Bitcoin/TxValidTransferTargets.lean      # no matches
```

No new `axiom`, `constant`, `sorry`, `admit`, `native_decide`, `unsafe`, or
`@[implemented_by]` in the lane module.

## 6. Scope caveats (explicit)

1. **Positive direction only for spend paths.**  The `.ok` results are
   sufficiency statements under explicit hypotheses, not an unconditional
   consensus-spendability claim.  No `VerifyScript`-level or full-consensus
   theorem is stated; the bridge stops at `verifyWitnessProgram` (P2WSH).
2. **Known amount required.**  Every transfer statement uses
   `txCheckerFor tx nIn (some amount)`.  The imported digest bridge proves
   that the digest commits to `amount`
   (`SighashBridgeTargets.digest_commits_amount`), but this module does
   **not** prove that `amount` equals
   the referenced outpoint's value; that remains an application/UTXO-layer
   obligation.  With `none`, the pipeline checker is fail-closed: the delayed
   witness is never `.ok`, and the revocation witness is `.fail .evalFalse`
   (a fortiori not `.ok`).
3. **ECDSA hypothesis.**  The concrete hypothesis is a `verifyImpl` call over
   `LnLean.Bitcoin.Sighash.sighashWitnessV0 ... amount`, i.e. assumption C3's
   instantiation.  No forgery-resistance or key-ownership claim is made.
4. **Delayed context.**  The `↔` refinement no longer needs an input-range
   hypothesis: it is proved directly at the pipeline checker (whose `env`
   already uses the pipeline's own `Bitcoin.Capstone.RealChecker.dummyTxIn`),
   and the RHS is stated with that same dummy, so the statement is faithful
   even for an out-of-range `nIn` (a degenerate case).  The context condition
   spells out BIP 68/112: version ≥ 2, disable bit clear, height domain, and
   `csv ≤` masked sequence.  It is instantiated at the script-flags word
   `{ csv := true }` and the default policy `{}`; the consensus `csv` flag is
   therefore explicit, not proved globally.  The only theorem that still
   needs `hIn : nIn < tx.vin.length` is the auxiliary
   `txCheckerFor_some_eq_checkerOf`, because `checkerOf`'s environment uses
   the *other* dummy input out of range.
5. **`minimalData`.**  The edge is stated for the exact policy word
   `{ minimalData := true }`.  Positive decode/execution holds for
   `128 ≤ csv < 32768`; rejection `.scriptNum` holds for `csv < 128`.  The
   reason is that the scaffold's `toLocalDelayBytes` is fixed-width 2 bytes,
   whereas honest BOLT 3 emits a minimal `CScriptNum`; the two agree only on
   already-minimal payloads.  A full `↔` at parametric `minimalData = true`
   policy was **not** proved: it would require re-running every wave-5/6/7
   failure-direction proof at the parametric policy.  That is a scope
   boundary, not a hidden assumption.
6. **`csv` range.**  Default-policy decode is exact for `csv < 32768`.
   For `32768 < csv < 65536` the fixed-width payload decodes to
   `32768 - csv < 0`, so vendor `OP_CSV` yields `.fail .negativeLocktime`.
   At exactly `csv = 32768` the sign-magnitude byte is negative zero, i.e.
   the decoded value is `0`; distinct delays `0` and `32768` collide.  This
   is a limitation of the *encoding*, not a consensus rule, and it is
   mechanized as `decodeNum_delayBytes_32768` rather than papered over.
   The negative-locktime theorem therefore uses the strict bound
   `32768 < csv`.
7. **No Git writes, no shared-file edits.**  The working tree already
   contained other lanes' modifications; this lane added only the two owned
   files and did not touch them.

## 7. Integration steps (for the integrator)

1. Add the module to the library root (suggested one-line patch to
   `LnLean.lean`, which this lane did not edit):
   ```lean
   import LnLean.Proofs.Bitcoin.TxValidTransferTargets
   ```
2. Register the headline results in `Obligations.lean` / `Traceability.lean`
   under the existing `L1-02` and `L1-07` rows, using
   `txCheckerFor_some_eq_realCheckerOf` as the transfer lemma and
   `toLocal_delayed_txCheckerFor_refinement`,
   `toLocal_delayed_txCheckerFor_interpreters_agree`,
   `toLocal_revocation_txCheckerFor_interpreters_agree` as the branch
   witnesses.
3. Add the four boundary lemmas to the catalog where the wave-7 report
   listed open edges:
   `txCheckerFor_none_delayed_not_ok`,
   `txCheckerFor_none_revocation_fail`,
   `toLocal_delayed_minimalData_true_scriptNum`,
   `toLocal_delayed_high_negativeLocktime` (plus
   `decodeNum_delayBytes_32768` for the equality collision).
4. Re-run the aggregate axiom audit and the non-forbidden-construct scan over
   the integrated module set after the import is added.

## 8. Blockers

None for this lane.  The only operational issue was that the shared vendor
olean directory had been cleared; rebuilding `Bitcoin.TxValidation.Full`
under the shared lock restored it.  No proof obligation was abandoned as
blocked.

## 9. Catalog / roadmap recommendation (`L1-02`, `L1-07`)

Recommend closing `L1-02` as **narrowed/conditional-complete** and `L1-07` as
**proved for known-amount, in-range inputs**: the pipeline-to-capstone checker
identity is now exact, so the remaining `L1-02` gap is no longer a
checker-transfer gap but the application-layer equation “spent amount = UTXO
value” plus the usual EC assumption; state that explicitly in the catalog
rather than leaving `txCheckerFor` as an open transfer item.  For the roadmap,
the next highest-value step is a *policy-parametric* delayed-branch `↔`
(duplicating the wave-5/6/7 failure directions at an arbitrary `PolicyFlags`
with `minimalData` fixed), followed by replacing the scaffold's fixed-width
`toLocalDelayBytes` with the minimal BOLT 3 `CScriptNum` encoding so the
`csv ≥ 32768` and `csv < 128` boundaries disappear rather than remaining
documented encoding artifacts; only after that should the effort move to
`VerifyScript`/full-consensus layering (fees, UTXO commitments, and the
saturation caveats of the vendor pipeline).
