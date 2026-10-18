# S7-L1-SEQUENCE — sequence/context refinement for the `to_local` delayed branch

**Lane:** `S7-L1-SEQUENCE` (`L1-07`, `L1-08` follow-on).
**Repository:** `/home/ubuntu/ln-lean-repair`
**Base commit:** `3180581`
**Verdict:** complete for the assigned scope.  The faithful two-byte
`to_self_delay` encoding is decoded to `(csv : Int)`, its non-negativity and
operand disable-bit properties are proved, the vendored `checkSequenceDef` is
characterized exactly, and the vendored P2WSH verdict on the delayed
`to_local` witness is proved to be `.ok` **iff** the sequence/context
conditions and the delayed-key ECDSA check hold.  The result is instantiated
at the concrete lax secp256k1 checker `checkerOf verifyImpl` and transferred
to the capstone `realCheckerOf` for in-range inputs.  All bridge modules and
vendor sources are imported unchanged.

- Lane file (exclusive ownership, new):
  - `LnLean/Proofs/Bitcoin/SequenceContextTargets.lean` — 632 lines.
  - `agents/reports/swarm7/S7-L1-SEQUENCE.md` — this report.
- Not modified: `InterpreterBridgeTargets.lean`,
  `InterpreterRevocationTargets.lean`, `SighashBridgeTargets.lean`,
  `SpendTargets.lean`, `Seam.lean`, `LnLean.lean`, `Obligations.lean`,
  `Traceability.lean`, `AxiomAudit.lean`, `scripts/check-final.py`, shared
  docs/scripts, other lanes' files, `vendor/**`.  No Git write.

## 1. Result in one paragraph

Waves 5–6 state the delayed `to_local` agreement under an abstract decoded
`ScriptNum`, an abstract non-negativity proof, an abstract disable-bit proof,
and the vendored sequence check.  This lane removes those hypotheses for the
faithful BOLT 3 fixed-width encoding.  The payload
`delayBytes csv = [csv % 256, (csv >>> 8) % 256]` decodes under the default
non-minimal-data policy to exactly `(csv : Int)` for every `csv < 32768`;
that value is non-negative and has a clear BIP 68 operand disable bit.  The
vendored `checkSequenceDef` is then characterized completely:
`version ≥ 2`, the input disable bit is clear, the masked input sequence is
in the height domain (`< TYPE_FLAG`), and `csv ≤` that masked sequence.  On
the delayed witness, vendor `.ok` is equivalent to this context condition
together with the delayed-key ECDSA check, and both failure directions are
mechanized (`unsatisfiedLocktime` for a failing sequence, `evalFalse` for a
failing signature under a passing sequence).  At
`checkerOf Bitcoin.Crypto.Ecdsa.Verify.verifyImpl`, the ECDSA hypothesis is
replaced by the explicit verifier call over the BIP 143 model digest; at
`Bitcoin.Capstone.RealChecker.realCheckerOf` this is transferred for
`nIn < tx.vin.length`.

## 2. What is mechanized

### 2.1 Decoding and operand facts

```lean
theorem bytesOf_delayBytes (csv : Nat) :
    bytesOf (delayBytes csv) = [csv % 256, (csv >>> 8) % 256]

theorem setVchBE_delay (csv : Nat) (hcsv : csv < 32768) :
    setVchBE [(csv >>> 8) % 256, csv % 256] = (csv : Int)

theorem decodeBE_delay (csv : Nat) (hcsv : csv < 32768) :
    decodeBE false 5 (bytesOf (delayBytes csv)).reverse = some (csv : Int)

theorem decodeNum_delayBytes_of_minimalData_false (pol : PolicyFlags)
    (hmin : pol.minimalData = false) (csv : Nat) (hcsv : csv < 32768) :
    decodeNum pol (delayBytes csv) 5 = .ok (csv : Int)

theorem decodeNum_delayBytes (csv : Nat) (hcsv : csv < 32768) :
    decodeNum ({} : PolicyFlags) (delayBytes csv) 5 = .ok (csv : Int)

theorem decodeNum_policy_congr (pol pol' : PolicyFlags)
    (h : pol.minimalData = pol'.minimalData) (b : ByteArray) (m : Nat) :
    decodeNum pol b m = decodeNum pol' b m

theorem nonneg_delay (csv : Nat) : 0 ≤ (csv : Int)

theorem disableBit_delay (csv : Nat) (hcsv : csv < 32768) :
    Int.toNat (csv : Int) &&& SEQUENCE_LOCKTIME_DISABLE_FLAG = 0
```

`decodeNum_policy_congr` records that the policy word enters `decodeNum`
only through `minimalData`; the default policy has `minimalData = false`
definitionally, so `decodeNum_delayBytes` is unconditional in `csv < 32768`.

### 2.2 Exact sequence characterization

```lean
theorem and_mask_delay (csv : Nat) (hcsv : csv < 32768) :
    csv &&& (SEQUENCE_LOCKTIME_TYPE_FLAG ||| SEQUENCE_LOCKTIME_MASK) = csv

theorem step_abstract (t csv : Nat)
    (hdom : csv < SEQUENCE_LOCKTIME_TYPE_FLAG) :
    (if (!decide ((t < SEQUENCE_LOCKTIME_TYPE_FLAG ∧
            csv < SEQUENCE_LOCKTIME_TYPE_FLAG) ∨
          (t ≥ SEQUENCE_LOCKTIME_TYPE_FLAG ∧
            csv ≥ SEQUENCE_LOCKTIME_TYPE_FLAG))) = true then
      false
     else !decide (csv > t)) =
      decide (t < SEQUENCE_LOCKTIME_TYPE_FLAG ∧ csv ≤ t)

theorem checkSequenceDef_delay_iff (env : LocktimeEnv) (csv : Nat)
    (hcsv : csv < 32768) :
    checkSequenceDef env (csv : Int) = true ↔
      (¬ env.txVersion < 2) ∧
      (env.txSequence.toNat &&& SEQUENCE_LOCKTIME_DISABLE_FLAG) = 0 ∧
      (env.txSequence.toNat &&&
          (SEQUENCE_LOCKTIME_TYPE_FLAG ||| SEQUENCE_LOCKTIME_MASK)) <
        SEQUENCE_LOCKTIME_TYPE_FLAG ∧
      csv ≤ (env.txSequence.toNat &&&
          (SEQUENCE_LOCKTIME_TYPE_FLAG ||| SEQUENCE_LOCKTIME_MASK))
```

This is an iff, not a one-way implication: the context conjunction is exactly
the vendor predicate for the faithful decoding.

### 2.3 Bad-signature delayed branch (negative direction)

All four vendor entry points are mechanized with a rejected delayed-key
signature and an *accepting* sequence check:

```lean
theorem evalFrom_toLocalWireOps_delayed_bad_sig ...
    (hseq : checkSequenceDef chk.env n = true)
    (hsig : chk.base.checkECDSASignature sig delayedPaymentKey.bytes
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      .witnessV0 (default : ...) = false) :
    evalFrom ... = Except.ok
      { stack := [ByteArray.empty], alt := [], vf := [], opCount := 6,
        codeSep := 0, vwLeft := none }

theorem evalScriptBytes_toLocal_delayed_bad_sig ... :
    evalScriptBytes ... = Except.ok [ByteArray.empty]

theorem executeWitnessScript_toLocal_delayed_bad_sig ... :
    executeWitnessScript ... = .fail .evalFalse

theorem verifyWitnessProgram_toLocal_delayed_bad_sig ... :
    verifyWitnessProgram ... = .fail .evalFalse
```

The failing-sequence direction is imported from
`InterpreterRevocationTargets.verifyWitnessProgram_toLocal_delayed_csv_false`
(`.fail .unsatisfiedLocktime`) and is used in the iff proof.

### 2.4 Vendor acceptance criterion

```lean
theorem toLocal_delayed_vendor_iff (chk : ScriptChecker)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (n : ScriptNum) (program : ByteArray)
    (hr : revocationKey.bytes.size = 33)
    (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hdec : decodeNum ({} : PolicyFlags) (delayBytes csv) 5 = .ok n)
    (hnn : 0 ≤ n)
    (hdis : Int.toNat n &&& SEQUENCE_LOCKTIME_DISABLE_FLAG = 0)
    (hps : program.size = 32)
    (hprog : hashSha256
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)) = program) :
    verifyWitnessProgram 10
      [sig, ByteArray.empty,
        serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)]
      0 program ({ csv := true } : ScriptFlags) ({} : PolicyFlags) chk false = .ok ↔
      (checkSequenceDef chk.env n = true ∧
        chk.base.checkECDSASignature sig delayedPaymentKey.bytes
          (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
          .witnessV0 (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true)
```

Removing the decode/range/disable hypotheses:

```lean
theorem toLocal_delayed_sequence_vendor_iff (chk : ScriptChecker)
    ... (hcsv : csv < 32768) ... :
    verifyWitnessProgram ... = .ok ↔
      (checkSequenceDef chk.env (csv : Int) = true ∧
        chk.base.checkECDSASignature sig delayedPaymentKey.bytes
          (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
          .witnessV0 (default : ...) = true)
```

Expanding the sequence predicate:

```lean
theorem toLocal_delayed_sequence_context_refinement (chk : ScriptChecker)
    ... (hcsv : csv < 32768) ... :
    verifyWitnessProgram ... = .ok ↔
      ((¬ chk.env.txVersion < 2) ∧
        (chk.env.txSequence.toNat &&& SEQUENCE_LOCKTIME_DISABLE_FLAG) = 0 ∧
        (chk.env.txSequence.toNat &&&
            (SEQUENCE_LOCKTIME_TYPE_FLAG ||| SEQUENCE_LOCKTIME_MASK)) <
          SEQUENCE_LOCKTIME_TYPE_FLAG ∧
        csv ≤ (chk.env.txSequence.toNat &&&
            (SEQUENCE_LOCKTIME_TYPE_FLAG ||| SEQUENCE_LOCKTIME_MASK)) ∧
        chk.base.checkECDSASignature sig delayedPaymentKey.bytes
          (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
          .witnessV0 (default : ...) = true)
```

### 2.5 Positive agreement with the existing bridge

```lean
theorem toLocal_delayed_sequence_interpreters_agree (chk : ScriptChecker)
    (msg : ByteArray) ... (hcsv : csv < 32768) ...
    (hseq : checkSequenceDef chk.env (csv : Int) = true)
    (hsig : chk.base.checkECDSASignature sig delayedPaymentKey.bytes
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      .witnessV0 (default : ...) = true) :
    verifyWitnessProgram ... = .ok ∧
      P2WSHSpend (vendorLawsCSV chk
          (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
          (csv : Int))
        msg ... (toLocalProg revocationKey delayedPaymentKey csv) [zeroByte, sig]
```

This is the wave-5 positive delayed theorem with every decode hypothesis
discharged by `csv < 32768`.

### 2.6 Concrete EC and transaction context

```lean
theorem toLocal_delayed_checkerOf_refinement
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount) ...
    (hpk : Bitcoin.Crypto.Seam.Der.isValidPubKey delayedPaymentKey.bytes = true)
    (hne : 0 < sig.size) :
    verifyWitnessProgram ...
      (checkerOf Bitcoin.Crypto.Ecdsa.Verify.verifyImpl tx nIn amount) false = .ok ↔
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
            (hashtypeOf sig) amount) = true)

theorem sighashDispatch_eq_real (tx : Bitcoin.Data.Tx) (nIn : Nat)
    (amount : Amount) :
    sighashDispatch tx nIn amount =
      Bitcoin.Capstone.RealChecker.sighashDispatch tx nIn amount

theorem checkerOf_eq_realCheckerOf (tx : Bitcoin.Data.Tx) (nIn : Nat)
    (amount : Amount) (hIn : nIn < tx.vin.length) :
    checkerOf Bitcoin.Crypto.Ecdsa.Verify.verifyImpl tx nIn amount =
      Bitcoin.Capstone.RealChecker.realCheckerOf tx nIn amount

theorem toLocal_delayed_realChecker_refinement
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (amount : Amount)
    (hIn : nIn < tx.vin.length) ... :
    verifyWitnessProgram ...
      (Bitcoin.Capstone.RealChecker.realCheckerOf tx nIn amount) false = .ok ↔
      ((¬ tx.version < 2) ∧ ...the same context conjunction...
        Bitcoin.Crypto.Ecdsa.Verify.verifyImpl ... = true)
```

`sighashDispatch_eq_real` uses
`LnLean.Bitcoin.Sighash.sighashWitnessV0_eq_interface` on the witness-v0 arm;
the legacy arm is definitionally the same.  `checkerOf_eq_realCheckerOf`
needs `nIn < tx.vin.length` only because the two totalizations use different
dummy `TxIn` sequences (`0` versus `0xFFFFFFFF`) out of range.

### 2.7 Policy and activation boundaries

```lean
theorem getBlockScriptFlags_csv_of_csvHeight_le (height : UInt32)
    (h : CSV_HEIGHT ≤ height) :
    (getBlockScriptFlags height).csv = true

theorem dispatchOp_csv_disabled (ctx : Ctx) (st : State)
    (h : ctx.flags.csv = false) :
    stepBody.dispatchOp ctx
      { ast := .op ⟨0xb2, by decide⟩, wire := 0xb2, next := 0 }
      0xb2 (st.vf.all id) st = .ok st
```

`dispatchOp_csv_disabled` is the pre-`CSV_HEIGHT` NOP semantics of `OP_CSV`.
At and above `CSV_HEIGHT`, `getBlockScriptFlags` sets `csv := true`, so the
context refinement applies with consensus flags.

## 3. Build and audit evidence

Build (only the new module, shared lock, single thread):

```text
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Proofs.Bitcoin.SequenceContextTargets
```

Result:

```text
Build completed successfully (50 jobs).
EXIT=0
```

The dependency closure now includes `Bitcoin.Crypto.Ecdsa.Verify` and
`Bitcoin.Capstone.RealChecker` (no vendor source changes).

`#print axioms` on every public theorem reports only the allowed axioms
`propext`, `Quot.sound`, and `Classical.choice`.  Representative output:

```text
'...nonneg_delay' does not depend on any axioms
'...decodeNum_policy_congr' depends on axioms: [propext]
'...getBlockScriptFlags_csv_of_csvHeight_le' depends on axioms: [propext]
'...checkSequenceDef_delay_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'...toLocal_delayed_vendor_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'...toLocal_delayed_sequence_context_refinement'
  depends on axioms: [propext, Classical.choice, Quot.sound]
'...toLocal_delayed_checkerOf_refinement'
  depends on axioms: [propext, Classical.choice, Quot.sound]
'...toLocal_delayed_realChecker_refinement'
  depends on axioms: [propext, Classical.choice, Quot.sound]
```

Forbidden-construct scan of
`LnLean/Proofs/Bitcoin/SequenceContextTargets.lean`:

```text
grep -nE '\b(sorry|admit|native_decide|unsafe|implemented_by)\b' \
  LnLean/Proofs/Bitcoin/SequenceContextTargets.lean
# no matches
```

No `axiom`, `@[implemented_by]`, `unsafe`, or `native_decide` occurs.  The
only classical ingredient is `Classical.choice`, pulled in by the underlying
`Nat.testBit`/decidability lemmas; it is on the allowed list.

## 4. Scope caveats

1. **Range `csv < 32768`.**  This is the range in which the fixed two-byte
   little-endian payload is a non-negative sign-magnitude `CScriptNum`.
   BOLT 3's `to_self_delay` field is a `u16`, but for values `≥ 32768` the
   high byte sets the `CScriptNum` sign bit, the vendor decodes a negative
   number, and `OP_CSV` fails with `.negativeLocktime` before the sequence
   comparison.  This lane therefore states the accepting refinement for
   `csv < 32768`; the negative range is a faithful vendor rejection, not a
   modelling gap.  Widening to arbitrary `u16` would require a separate
   negative-number lemma; it is not claimed here.
2. **Minimal-data policy.**  The decode theorem is unconditional at the
   default policy (`minimalData = false`).  With `minimalData = true`, a
   one-byte value `csv < 256` is encoded non-minimally by the fixed-width
   scaffold, so decode may fail with `.scriptNum`; this is the scaffold's
   documented fixed-width encoding, not the BOLT 3 minimal push.  No claim is
   made for `minimalData = true`.
3. **Signature direction.**  The iff is about the **vendor** verdict and the
   opaque checker hypothesis.  The model-side `Accepts` predicate is linked
   in the positive direction by
   `toLocal_delayed_sequence_interpreters_agree`; a model-side
   `¬ Accepts` theorem for a rejected signature is not added here (the
   existing wave-6 module has the analogous theorem for the revocation
   branch and for a failing sequence check).
4. **`txCheckerFor` not instantiated.**  `Bitcoin.TxValidation.Full` was not
   imported (its dependency closure is much larger than this lane needs).
   `realCheckerOf` is the same ECDSA wiring that `txCheckerFor` uses; the
   remaining step is the ECDSA-field equality from `txCheckerOf_ecdsa` when
   the amount is `some amount`.  This is recorded as an integration step,
   not mechanized here.
5. **ECDSA hypotheses.**  The concrete refinement still assumes
   `isValidPubKey delayedPaymentKey.bytes = true` and `0 < sig.size`, which
   are exactly the side conditions needed to reach the EC math through the
   vendored seam adapter (DER strictness remains upstream in the
   interpreter's BIP 66 gate, as in the existing bridge).
6. **Context fields.**  The refinement reads only `tx.version` and the
   signing input's `sequence`; `tx.locktime` is not part of
   `checkSequenceDef` and therefore does not appear.

## 5. Integration steps (not performed; files are shared)

1. Add to `LnLean.lean`:
   `import LnLean.Proofs.Bitcoin.SequenceContextTargets`.
2. Register the module in `Traceability.lean` alongside
   `InterpreterBridgeTargets`, `InterpreterRevocationTargets`, and
   `SighashBridgeTargets`.
3. Add `#print axioms` entries in `AxiomAudit.lean` for the public theorems
   listed in §3 (especially `checkSequenceDef_delay_iff`,
   `toLocal_delayed_vendor_iff`,
   `toLocal_delayed_sequence_context_refinement`,
   `toLocal_delayed_checkerOf_refinement`, and
   `toLocal_delayed_realChecker_refinement`).
4. If an obligation/catalog entry is desired, point the CSV/sequence
   obligation at `toLocal_delayed_sequence_context_refinement`; it is the
   strongest context-level statement in this lane.
5. Optional follow-up: import `Bitcoin.TxValidation.Full` and derive the
   `txCheckerFor tx nIn (some amount)` variant from
   `toLocal_delayed_realChecker_refinement` plus
   `txCheckerOf_ecdsa`.

## 6. Blockers

None for the assigned scope.  The only deliberate omission is the
`txCheckerFor`/`Full` instantiation described in §4.4 and §5.5, which is an
integration-layer step rather than a missing proof ingredient.

## 7. Parent summary

`SequenceContextTargets.lean` builds cleanly (50 jobs, exit 0) and proves the
faithful decode `delayBytes csv ↦ (csv : Int)` for `csv < 32768`, the exact
`checkSequenceDef` context characterization, the vendor `.ok` iff
(sequence/context ∧ delayed-key ECDSA) criterion with both failure directions,
the positive model agreement, and concrete/real-checker refinements ending in
an explicit `Bitcoin.Crypto.Ecdsa.Verify.verifyImpl` call over
`sighashWitnessV0`.  Axioms are only `propext`, `Quot.sound`, and
`Classical.choice`; no forbidden constructs; no bridge or vendor file was
edited.  Remaining work is integration (imports/audit/catalog) and the
optional `txCheckerFor` transfer.
