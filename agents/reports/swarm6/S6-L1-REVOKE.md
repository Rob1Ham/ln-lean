# S6-L1-REVOKE — vendor bridge for the `to_local` revocation branch

**Lane:** `S6-L1-REVOKE` (`L1-02`, `L1-07`).
**Repository:** `/home/ubuntu/ln-lean-repair`
**Branch / base:** `repair/integrated` at `201a0a0` (wave-6 launch).
**Verdict:** complete for the assigned scope.  The BOLT 3 `to_local`
**revocation** branch is now executed end to end by the vendored interpreter
(`OP_IF` → push revocation key → `OP_ELSE` → skip delayed block `OP_CSV`/
`OP_DROP` → `OP_ENDIF` → `OP_CHECKSIG`), lifted through `evalScriptBytes`,
`executeWitnessScript` and `verifyWitnessProgram`, with a model-side
`P2WSHSpend` and an agreement theorem.  Branch selection is mechanized from
one script and one signature, and three negative results are proved:
wrong-key rejection (`evalFalse`), delayed-key-signature rejection on the
revocation branch (under an explicit key-separation hypothesis), and
wrong-branch rejection (`unsatisfiedLocktime`).  The Wave-5 delayed bridge and
funding bridge are imported unchanged; no vendored source was edited.  No
missing vendor opcode or dependency was found.

- Lane files (exclusive ownership, both new):
  - `LnLean/Proofs/Bitcoin/InterpreterRevocationTargets.lean` — 725 lines.
  - `agents/reports/swarm6/S6-L1-REVOKE.md` — this report.
- Not modified: `InterpreterBridgeTargets.lean`, `SpendTargets.lean`,
  `Seam.lean`, `LnLean.lean`, `Obligations.lean`, `Traceability.lean`,
  `AxiomAudit.lean`, `scripts/check-final.py`, shared docs/scripts, other
  lanes' files, `vendor/**`.  No Git write.
- The other modified/untracked files visible in `git status` belong to
  concurrent lanes and were left untouched.

## 1. Result in one paragraph

Wave 5 exercised the funding script and the `to_local` `OP_ELSE` (delayed)
branch through `Bitcoin.Interpreter.Defs`, but the `OP_IF` (revocation) branch
had only a model-level theorem in `SpendTargets`.  This lane adds the vendor
computation for the true branch.  On the concrete `toLocalWireOps` list, the
vendored `evalFrom` consumes the `0x01` selector (`OP_IF`), pushes the
revocation key, flips the execution flag (`OP_ELSE`), skips every opcode of
the delayed block while still charging the opcode budget, closes the
conditional (`OP_ENDIF`), and verifies the signature against the revocation
key (`OP_CHECKSIG`), ending at `.ok` with the canonical `true` on a clean
stack.  Because the true branch never reaches `OP_CSV`, the positive theorem
carries **no** delay-decode, sequence, locktime or policy hypothesis — only
the key-size and the vendored ECDSA hypothesis.  The corresponding P2WSH
`verifyWitnessProgram` returns `.ok`, and the model `P2WSHSpend` with
`vendorLaws` holds under the same ECDSA hypothesis.  Negative theorems show
that a rejected revocation-key signature yields `push false` and
`.fail .evalFalse`, and that the empty selector takes the delayed branch and
errors with `.fail .unsatisfiedLocktime` when `checkSequenceDef` is false,
even if the same signature is valid for the revocation key.

## 2. What is mechanized

### 2.1 Positive revocation path

- `evalFrom_toLocalWireOps_revocation`: full vendored `evalFrom` computation
  on `toLocalWireOps`, machine stack `[revocationSelector, sig]`, fuel `10`,
  final state `{ stack := [0x01], alt := [], vf := [], opCount := 6,
  codeSep := 0, vwLeft := none }`.
- `evalScriptBytes_toLocal_revocation`: the same through the SCRIPT_SIZE
  pre-check and `parseWire`, final stack `[0x01]`.
- `executeWitnessScript_toLocal_revocation`: witness items `[sig, 0x01]`,
  implicit cleanstack truthiness accepted, verdict `.ok`.
- `verifyWitnessProgram_toLocal_revocation`: P2WSH dispatch with witness
  `[sig, 0x01, witnessScript]`, verdict `.ok`.
- `toLocal_model_spend_revocation`: model `P2WSHSpend (vendorLaws chk sc)`
  for the revocation stack `[oneByte, sig]`.
- `toLocal_revocation_interpreters_agree`: vendor `.ok` ∧ model
  `P2WSHSpend`, same ECDSA hypothesis.
- `toLocal_model_spend_revocation_csv_law`: for any `n`, the model spend also
  holds with `vendorLawsCSV chk sc n` and **no** CSV hypothesis, because the
  revocation path of `toLocalProg` never calls `csvOk`.

### 2.2 Branch selection from one script and one signature

`toLocal_vendor_branch_selection` proves, for a fixed script, signature and
failing sequence check:

```text
verifyWitnessProgram 10 [sig, 0x01, script]   ... = .ok
verifyWitnessProgram 10 [sig, <>,   script]   ... = .fail .unsatisfiedLocktime
```

The witnesses differ only in the selector.  The `0x01` witness takes the
revocation branch and ignores `OP_CSV`/the sequence environment; the empty
witness takes the delayed branch, where `OP_CSV` reads
`checkSequenceDef chk.env n` and errors before any signature check.

### 2.3 Negative results

1. **Wrong key (`evalFalse`).**
   `evalFrom_toLocalWireOps_revocation_bad_sig` shows the true branch leaves
   the canonical `false` (`ByteArray.empty`) when the checker rejects the
   revocation-key pair; `executeWitnessScript_toLocal_revocation_bad_sig` and
   `verifyWitnessProgram_toLocal_revocation_bad_sig` show the full P2WSH
   verdicts are `.fail .evalFalse`.  `not_accepts_toLocal_revocation_bad_sig_vendor`
   gives the model `¬ Accepts`, and `toLocal_revocation_wrong_key_rejected`
   packages vendor failure with model non-acceptance.
2. **Delayed-key signature on the revocation branch.**
   `RevocationKeySeparated` is an explicit checker-level hypothesis (a
   signature accepted under `local_delayedpubkey` is rejected under
   `revocationpubkey`; this is what ECDSA key separation yields except with
   negligible probability — no computational model is claimed).  Under it,
   `toLocal_revocation_delayed_key_sig_rejected` proves that a checker-valid
   delayed-key signature is **rejected** by the `0x01` witness
   (`.fail .evalFalse`) and the model does not accept.
3. **Wrong branch (`unsatisfiedLocktime`).**
   `evalFrom_toLocalWireOps_delayed_csv_false`,
   `evalScriptBytes_toLocal_delayed_csv_false`,
   `executeWitnessScript_toLocal_delayed_csv_false` and
   `verifyWitnessProgram_toLocal_delayed_csv_false` prove the empty selector
   errors/fails when `checkSequenceDef chk.env n = false`; the model
   counterpart `not_accepts_toLocal_delayed_csv_false` uses
   `vendorLawsCSV` and `exec_toLocal_delayed_csv_fails`; and
   `toLocal_delayed_csv_failure_agree` packages both.

## 3. Exact signatures

Namespace: `LnLean.Proofs.Bitcoin.InterpreterRevocationTargets`.
`sc` below abbreviates
`serializeOpcodes (InterpreterBridgeTargets.toLocalOps revocationKey delayedPaymentKey csv)`;
`ed` abbreviates
`(default : Bitcoin.Crypto.Seam.ScriptExecutionData)`; `Req` abbreviates
`Key sizes 33/33`; `AcceptRev L := Accepts L msg (toLocalProg revocationKey delayedPaymentKey csv) [oneByte, sig]`.

Common hypothesis block (omitted below only where noted):

```lean
(chk : ScriptChecker) (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
(sig : ByteArray)
(hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
(hsig : chk.base.checkECDSASignature sig revocationKey.bytes
  sc .witnessV0 ed = true)
```

```lean
theorem evalFrom_toLocalWireOps_revocation
    (chk : ScriptChecker) (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (hr : revocationKey.bytes.size = 33)
    (hd : delayedPaymentKey.bytes.size = 33)
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
          codeSep := 0, vwLeft := none }

theorem evalScriptBytes_toLocal_revocation ... :
    evalScriptBytes 10 ({ csv := true } : ScriptFlags) ({} : PolicyFlags)
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      [revocationSelector, sig] chk .witnessV0
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData)
    = Except.ok [ByteArray.mk #[0x01]]

theorem executeWitnessScript_toLocal_revocation
    ... (vwSer : Int) ... (hsigsz : sig.size ≤ 520) ... :
    executeWitnessScript 10 [sig, revocationSelector] vwSer
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      ({ csv := true } : ScriptFlags) ({} : PolicyFlags) chk .witnessV0 = .ok

theorem verifyWitnessProgram_toLocal_revocation
    ... (sig program : ByteArray) ... (hsigsz : sig.size ≤ 520) ...
    (hps : program.size = 32)
    (hprog : hashSha256
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)) = program) :
    verifyWitnessProgram 10
      [sig, revocationSelector,
        serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)]
      0 program ({ csv := true } : ScriptFlags) ({} : PolicyFlags) chk false = .ok

theorem toLocal_model_spend_revocation
    (chk : ScriptChecker) (msg : ByteArray) ... :
    P2WSHSpend (vendorLaws chk
        (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)))
      msg
      (hashSha256 (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)))
      (toLocalScriptFull revocationKey delayedPaymentKey csv).bytes
      (toLocalProg revocationKey delayedPaymentKey csv) [oneByte, sig]

theorem toLocal_revocation_interpreters_agree
    (chk : ScriptChecker) (msg : ByteArray) ... (hsigsz : sig.size ≤ 520) ... :
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
        (toLocalProg revocationKey delayedPaymentKey csv) [oneByte, sig]

theorem toLocal_model_spend_revocation_csv_law
    (chk : ScriptChecker) (msg : ByteArray) ... (n : Bitcoin.Numeric.ScriptNum)
    (hr : ...) (hd : ...)
    (hsig : ... = true) :
    P2WSHSpend (vendorLawsCSV chk
        (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)) n)
      msg
      (hashSha256 (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)))
      (toLocalScriptFull revocationKey delayedPaymentKey csv).bytes
      (toLocalProg revocationKey delayedPaymentKey csv) [oneByte, sig]
```

Negative signatures (the hypothesis `hsig` is the same as above with `= false`
where stated):

```lean
theorem evalFrom_toLocalWireOps_revocation_bad_sig
    ... (hsig : chk.base.checkECDSASignature sig revocationKey.bytes
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      .witnessV0 (default : ...) = false) :
    evalFrom ... 10 (toLocalWireOps revocationKey delayedPaymentKey csv)
      { stack := [revocationSelector, sig], ... }
    = Except.ok { stack := [ByteArray.empty], ..., opCount := 6, ... }

theorem evalScriptBytes_toLocal_revocation_bad_sig ... :
    evalScriptBytes ... [revocationSelector, sig] ... = Except.ok [ByteArray.empty]

theorem executeWitnessScript_toLocal_revocation_bad_sig ... :
    executeWitnessScript 10 [sig, revocationSelector] vwSer ... = .fail .evalFalse

theorem verifyWitnessProgram_toLocal_revocation_bad_sig
    ... (hps : program.size = 32)
    (hprog : hashSha256
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)) = program) :
    verifyWitnessProgram 10
      [sig, revocationSelector, ...] 0 program
      ({ csv := true } : ScriptFlags) ({} : PolicyFlags) chk false = .fail .evalFalse

theorem not_accepts_toLocal_revocation_bad_sig_vendor
    (chk : ScriptChecker) (msg : ByteArray) ... (hsig : ... = false) :
    ¬ Accepts (vendorLaws chk (...)) msg (toLocalProg ...) [oneByte, sig]

theorem toLocal_revocation_wrong_key_rejected
    ... (hsigsz : sig.size ≤ 520) (hsig : ... = false) :
    verifyWitnessProgram 10 [sig, revocationSelector, ...] 0
      (hashSha256 (...)) ({ csv := true }) ({}) chk false
      = .fail .evalFalse ∧
    ¬ Accepts (vendorLaws chk (...)) msg (toLocalProg ...) [oneByte, sig]

def RevocationKeySeparated (chk : ScriptChecker) (scriptCode : ByteArray)
    (revocationKey delayedPaymentKey : PubKey) : Prop :=
  ∀ sig : ByteArray,
    chk.base.checkECDSASignature sig delayedPaymentKey.bytes scriptCode
      .witnessV0 (default : ...) = true →
    chk.base.checkECDSASignature sig revocationKey.bytes scriptCode
      .witnessV0 (default : ...) = false

theorem toLocal_revocation_delayed_key_sig_rejected
    ... (hsigsz : sig.size ≤ 520)
    (hsep : RevocationKeySeparated chk
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      revocationKey delayedPaymentKey)
    (hdel : chk.base.checkECDSASignature sig delayedPaymentKey.bytes
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      .witnessV0 (default : ...) = true) :
    verifyWitnessProgram 10 [sig, revocationSelector, ...] 0
      (hashSha256 (...)) ({ csv := true }) ({}) chk false
      = .fail .evalFalse ∧
    ¬ Accepts (vendorLaws chk (...)) msg (toLocalProg ...) [oneByte, sig]
```

Wrong branch:

```lean
theorem evalFrom_toLocalWireOps_delayed_csv_false
    ... (n : Bitcoin.Numeric.ScriptNum) (hr) (hd)
    (hdec : decodeNum ({} : PolicyFlags) (delayBytes csv) 5 = .ok n)
    (hnn : 0 ≤ n)
    (hdis : Int.toNat n &&& SEQUENCE_LOCKTIME_DISABLE_FLAG = 0)
    (hseq : checkSequenceDef chk.env n = false) :
    evalFrom ... 10 (toLocalWireOps revocationKey delayedPaymentKey csv)
      { stack := [ByteArray.empty, sig], ... }
    = Except.error .unsatisfiedLocktime

theorem evalScriptBytes_toLocal_delayed_csv_false ... :
    evalScriptBytes 10 ({ csv := true }) ({})
      (serializeOpcodes (toLocalOps ...)) [ByteArray.empty, sig] chk .witnessV0
      (default : ...) = Except.error .unsatisfiedLocktime

theorem executeWitnessScript_toLocal_delayed_csv_false ... :
    executeWitnessScript 10 [sig, ByteArray.empty] vwSer
      (serializeOpcodes (toLocalOps ...)) ({ csv := true }) ({}) chk .witnessV0
    = .fail .unsatisfiedLocktime

theorem verifyWitnessProgram_toLocal_delayed_csv_false
    ... (hdec) (hnn) (hdis) (hseq : checkSequenceDef chk.env n = false)
    (hps : program.size = 32)
    (hprog : hashSha256 (serializeOpcodes (toLocalOps ...)) = program) :
    verifyWitnessProgram 10
      [sig, ByteArray.empty, serializeOpcodes (toLocalOps ...)]
      0 program ({ csv := true }) ({}) chk false = .fail .unsatisfiedLocktime

theorem not_accepts_toLocal_delayed_csv_false
    (chk : ScriptChecker) (msg : ByteArray) ... (n : Bitcoin.Numeric.ScriptNum)
    (hseq : checkSequenceDef chk.env n = false) :
    ¬ Accepts (vendorLawsCSV chk (serializeOpcodes (toLocalOps ...)) n)
      msg (toLocalProg ...) [zeroByte, sig]

theorem toLocal_delayed_csv_failure_agree
    ... (hsigsz : sig.size ≤ 520)
    (hdec) (hnn) (hdis) (hseq : checkSequenceDef chk.env n = false) :
    verifyWitnessProgram 10 [sig, ByteArray.empty, ...] 0
      (hashSha256 (...)) ({ csv := true }) ({}) chk false
      = .fail .unsatisfiedLocktime ∧
    ¬ Accepts (vendorLawsCSV chk (...) n) msg (toLocalProg ...) [zeroByte, sig]
```

Branch selection:

```lean
theorem toLocal_vendor_branch_selection
    ... (hsigsz : sig.size ≤ 520)
    (hdec : decodeNum ({} : PolicyFlags) (delayBytes csv) 5 = .ok n)
    (hnn : 0 ≤ n)
    (hdis : Int.toNat n &&& SEQUENCE_LOCKTIME_DISABLE_FLAG = 0)
    (hseq : checkSequenceDef chk.env n = false)
    (hsig : chk.base.checkECDSASignature sig revocationKey.bytes
      (serializeOpcodes (toLocalOps ...)) .witnessV0 (default : ...) = true)
    (hps : program.size = 32)
    (hprog : hashSha256 (serializeOpcodes (toLocalOps ...)) = program) :
    verifyWitnessProgram 10 [sig, revocationSelector, ...] 0 program
      ({ csv := true }) ({}) chk false = .ok ∧
    verifyWitnessProgram 10 [sig, ByteArray.empty, ...] 0 program
      ({ csv := true }) ({}) chk false = .fail .unsatisfiedLocktime
```

Selector helpers (all `rfl`/`decide`; no axioms):

```lean
def revocationSelector : ByteArray := ByteArray.mk #[0x01]
theorem revocationSelector_eq_oneByte : revocationSelector = oneByte
theorem delayedSelector_eq_zeroByte : (ByteArray.empty : ByteArray) = zeroByte
theorem castToBool_revocationSelector : Bitcoin.Numeric.castToBool revocationSelector = true
theorem revocationSelector_size : revocationSelector.size = 1
theorem byteArray_mk_one_size : (ByteArray.mk #[0x01]).size = 1
theorem castToBool_empty_byteArray : Bitcoin.Numeric.castToBool ByteArray.empty = false
```

## 4. Build

Built only the owned module under the shared lock:

```bash
cd /home/ubuntu/ln-lean-repair
export PATH=/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Proofs.Bitcoin.InterpreterRevocationTargets
```

Result:

```text
✔ [32/32] Built LnLean.Proofs.Bitcoin.InterpreterRevocationTargets (1.1s)
Build completed successfully (32 jobs).
```

RC `0`.  `lake env lean` on the module reports **no warnings and no errors**
for the owned file.  The remaining warnings in the build log belong to the
imported Wave-5 bridge (unused `simp` arguments, deprecated `if_neg`, and the
deliberately-unused `hdec`/`hnn`/`hdis` in its model theorem); the bridge was
not edited.  No full `lake build` was run.

## 5. Axiom audit

```bash
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake env lean /tmp/opencode/axioms_s6rv.lean
```

`#print axioms` results:

```text
revocationSelector_eq_oneByte          does not depend on any axioms
castToBool_revocationSelector          does not depend on any axioms
evalFrom_toLocalWireOps_revocation     [propext, Classical.choice, Quot.sound]
evalScriptBytes_toLocal_revocation     [propext, Classical.choice, Quot.sound]
executeWitnessScript_toLocal_revocation [propext, Classical.choice, Quot.sound]
verifyWitnessProgram_toLocal_revocation [propext, Classical.choice, Quot.sound]
toLocal_model_spend_revocation         [propext, Classical.choice, Quot.sound]
toLocal_revocation_interpreters_agree  [propext, Classical.choice, Quot.sound]
toLocal_model_spend_revocation_csv_law [propext, Classical.choice, Quot.sound]
evalFrom_toLocalWireOps_revocation_bad_sig [propext, Classical.choice, Quot.sound]
evalScriptBytes_toLocal_revocation_bad_sig [propext, Classical.choice, Quot.sound]
executeWitnessScript_toLocal_revocation_bad_sig [propext, Classical.choice, Quot.sound]
verifyWitnessProgram_toLocal_revocation_bad_sig [propext, Classical.choice, Quot.sound]
not_accepts_toLocal_revocation_bad_sig_vendor [propext, Classical.choice, Quot.sound]
toLocal_revocation_wrong_key_rejected  [propext, Classical.choice, Quot.sound]
toLocal_revocation_delayed_key_sig_rejected [propext, Classical.choice, Quot.sound]
evalFrom_toLocalWireOps_delayed_csv_false [propext, Classical.choice, Quot.sound]
evalScriptBytes_toLocal_delayed_csv_false [propext, Classical.choice, Quot.sound]
executeWitnessScript_toLocal_delayed_csv_false [propext, Classical.choice, Quot.sound]
verifyWitnessProgram_toLocal_delayed_csv_false [propext, Classical.choice, Quot.sound]
not_accepts_toLocal_delayed_csv_false  [propext, Classical.choice, Quot.sound]
toLocal_delayed_csv_failure_agree      [propext, Classical.choice, Quot.sound]
toLocal_vendor_branch_selection        [propext, Classical.choice, Quot.sound]
```

Every result is a subset of the allowed `{propext, Quot.sound,
Classical.choice}`.  No new axiom.

## 6. Forbidden-construct scan

```bash
grep -nE "sorry|axiom|admit|native_decide|unsafe|implemented_by" \
  LnLean/Proofs/Bitcoin/InterpreterRevocationTargets.lean
```

Output: **none** (exit code 1, no matches).  The repo checker also strips
comments and applies `\b(axiom|native_decide|unsafe|admit)\b` /
`@\[implemented_by\]` / `\bsorry\b`; the module contains no such construct in
code or prose.

## 7. Missing vendor opcode / dependency / context — exact record

**Missing vendor opcode/dependency: none.**  `OP_IF` (0x63), `OP_ELSE`
(0x67), `OP_ENDIF` (0x68), `OP_CSV` (0xb2), `OP_DROP` (0x75) and
`OP_CHECKSIG` (0xac) are all present in
`vendor/btc-lean-core/Bitcoin/Interpreter/Defs.lean` and are exercised by the
computation.  The wire list, parser, printer, `evalFrom`, `evalScriptBytes`,
`executeWitnessScript` and the P2WSH branch of `verifyWitnessProgram` are the
existing vendored API; no vendor declaration was added or changed.

**Context assumptions retained (all explicit):**

1. **ECDSA checks are hypotheses.**  `hsig`/`hsig = false`/`hdel` are calls to
   the frozen `BaseSignatureChecker`; the BIP 143 sighash is constructed by
   the checker, not here.  This is assumption C3 in `docs/ASSUMPTIONS.md` and
   the `L1-08` boundary.
2. **Key sizes.**  `revocationKey.bytes.size = 33` and
   `delayedPaymentKey.bytes.size = 33` are needed to compute the fixed wire
   offsets and element sizes.  They are properties of real BOLT 3 compressed
   keys; no theorem derives them from `PubKey`.
3. **Flags/policy are pinned.**  Execution uses `ScriptFlags = { csv := true }`
   and `PolicyFlags = {}` (in particular `minimalIf = false`,
   `minimalData = false`, `nullFail = false`, `strictEnc = false`).  With
   `minimalIf` enabled, the `0x01` selector is still minimal; non-minimal
   truthy selectors are not covered.
4. **Wrong-branch hypotheses.**  The `unsatisfiedLocktime` theorems take the
   decoded delay `n`, `0 ≤ n`, the disable-bit test and
   `checkSequenceDef chk.env n = false`, exactly as Wave 5 did for the
   positive delayed branch.  `n`/`chk.env` are not constructed from a raw
   commitment transaction or input sequence.
5. **`RevocationKeySeparated` is a hypothesis, not a theorem.**  It is the
   checker-level form of ECDSA key separation for one script code and one
   key pair; the tree has no computational-cryptography model (`CR-01`).  No
   theorem claims that distinct Lightning keys are separated in the sense of
   this `Prop` without that hypothesis.
6. **Positive direction only.**  The agreement theorems prove vendor `.ok`
   from the model hypotheses; no converse ("vendor `.ok` implies model
   `P2WSHSpend`") and no full `VerifyScript`/consensus acceptance is claimed.
7. **No `FundingParams`/transaction construction.**  The script code and the
   P2WSH program are explicit byte strings; the revocation-key/delayed-key
   derivation from commitment parameters and the outpoint/witness assembly are
   outside this module.
8. **Fuel 10.**  The concrete computation uses fuel `10` for a 9-op script;
   the vendored fuel bound is not re-derived generically.

## 8. Integration steps (for the parent)

The lane could not edit shared files.  Exact changes:

1. `LnLean.lean` — add, after
   `import LnLean.Proofs.Bitcoin.InterpreterBridgeTargets`:

   ```lean
   import LnLean.Proofs.Bitcoin.InterpreterRevocationTargets
   ```

2. `LnLean/Proofs/Traceability.lean` — add
   `"LnLean.Proofs.Bitcoin.InterpreterRevocationTargets"` next to
   `"LnLean.Proofs.Bitcoin.InterpreterBridgeTargets"` in the module list.

3. `docs/OPEN-ISSUES.md` — suggested evidence text for `L1-02` / `L1-07`
   (keep both open: `L1-08` sighash/locktime construction and the vendor-level
   converse remain outside):

   > The vendored `to_local` revocation branch is now executed end to end
   > (`OP_IF`/`OP_ELSE`/`OP_ENDIF`/`OP_CHECKSIG`) by
   > `InterpreterRevocationTargets`.  `toLocal_revocation_interpreters_agree`
   > gives vendor `.ok` plus model `P2WSHSpend` under the vendored ECDSA check;
   > `toLocal_vendor_branch_selection` proves the selector chooses the branch
   > from one script and one signature; `toLocal_revocation_wrong_key_rejected`
   > (`evalFalse`) and `toLocal_delayed_csv_failure_agree`
   > (`unsatisfiedLocktime`) are the mechanized negatives.  The positive
   > revocation path needs no delay/sequence/locktime hypothesis.  Missing:
   > BIP 143 sighash/locktime construction, the vendor converse, and the
   > conditional key-separation hypothesis for the delayed-key-signature
   > instantiation.

4. Catalog rows (if a single declaration per row is wanted):
   - `L1-02` revocation evidence:
     `LnLean.Proofs.Bitcoin.InterpreterRevocationTargets.toLocal_revocation_interpreters_agree`.
   - Branch selection/negative evidence:
     `...toLocal_vendor_branch_selection`,
     `...toLocal_revocation_wrong_key_rejected`,
     `...toLocal_revocation_delayed_key_sig_rejected`,
     `...toLocal_delayed_csv_failure_agree`.
   - `L1-07` evidence: the same module plus the unchanged Wave-5
     `InterpreterBridgeTargets.toLocal_delayed_interpreters_agree` and
     `funding_interpreters_agree`.  Do not describe any of these as
     unconditional consensus spendability.

5. **No changes needed** in `InterpreterBridgeTargets.lean` or
   `SpendTargets.lean`.  The delayed-branch and funding bridges are imported
   unchanged; `#check` confirms
   `InterpreterBridgeTargets.toLocal_delayed_interpreters_agree` and
   `funding_interpreters_agree` still resolve through this module's import.

6. Axiom-audit registration: add the headline names above to
   `AxiomAudit.lean` if the parent tracks per-lane audits; all are
   `{propext, Quot.sound, Classical.choice}` or axiom-free.

## 9. Blockers

None for the owned scope.  The remaining gaps are the named boundaries:
BIP 143 sighash/locktime construction (`L1-08`, sibling lane
`S6-L1-SIGHASH`), the vendor-level converse and full `VerifyScript`
integration, and a computational key-separation model (`CR-01`).  They are
recorded as hypotheses above, not hidden assumptions.

## 10. Reproduction

```bash
cd /home/ubuntu/ln-lean-repair
export PATH=/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH

LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Proofs.Bitcoin.InterpreterRevocationTargets

grep -nE "sorry|axiom|admit|native_decide|unsafe|implemented_by" \
  LnLean/Proofs/Bitcoin/InterpreterRevocationTargets.lean

LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake env lean /tmp/opencode/axioms_s6rv.lean
```

Scratch audit files used (not part of the tree):
`/tmp/opencode/axioms_s6rv.lean`, `/tmp/opencode/axioms_s6rv2.lean`,
`/tmp/opencode/sigs_s6rv.lean`, `/tmp/opencode/sigs2_s6rv.lean`,
`/tmp/opencode/regress_s6rv.lean`.
