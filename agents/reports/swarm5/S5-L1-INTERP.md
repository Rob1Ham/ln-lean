# S5-L1-INTERP — bridge from `SpendTargets` to the vendored Bitcoin interpreter

**Lane:** `S5-L1-INTERP` (`L1-01`, `L1-02`, `L1-07`).
**Worktree:** `/home/ubuntu/ln-lean-repair`
**Verdict:** completed for the assigned scope, with an explicit narrow boundary.
The vendored interpreter (`Bitcoin.Interpreter.Defs`) builds and is now the
target of a new bridge module. The funding path is mechanised end to end; the
`to_local` delayed (`OP_ELSE`) path is mechanised through the full
`OP_IF`/`OP_ELSE`/`OP_ENDIF`/`OP_CSV`/`OP_DROP`/`OP_CHECKSIG` computation,
with the sequence-number decode and `LocktimeEnv` still supplied as explicit
hypotheses. No consensus-spendability claim is made beyond those hypotheses,
and no vendored file was edited.

- Lane files:
  - `LnLean/Proofs/Bitcoin/SpendTargets.lean` — delivered unchanged.
  - `LnLean/Proofs/Bitcoin/InterpreterBridgeTargets.lean` — new, 978 lines.
  - `agents/reports/swarm5/S5-L1-INTERP.md` — this report.
- Forbidden files, vendor sources, `LnLean.lean`, Obligations/Traceability/
  AxiomAudit, shared docs/scripts, and other lanes' files were not modified.
- No Git write was performed.

## 1. Result in one paragraph

The wave-4 `SpendTargets` model executes a structured program under abstract
`InterpreterLaws`; it had no connection to a real evaluator. This lane imports
the vendored `Bitcoin.Interpreter.Defs` API and proves, for the exact BOLT 3
scripts:

1. the model serializer `serializeStmts` equals the vendor canonical printer
   `Bitcoin.Script.Parser.serializeOpcodes` (`toLocal_serialize_eq`);
2. `parseWire` recovers the exact vendor `WireOp` list with the correct next
   byte offsets (`toLocal_parseWire`);
3. the vendor `evalFrom` computation for the funding 2-of-2 script, including
   `cmsLoop`, `cmsCleanup`, encoding checks, script-number decode and the
   P2WSH cleanstack path (`funding_interpreters_agree`);
4. the vendor `evalFrom`, `evalScriptBytes`, `executeWitnessScript` and
   `verifyWitnessProgram` computations for the `to_local` delayed branch
   (`toLocal_delayed_interpreters_agree`), under the same vendored ECDSA call
   and an explicit `checkSequenceDef chk.env n = true` hypothesis;
5. a model-side instantiation `vendorLawsCSV` whose `csvOk` is literally the
   vendored `checkSequenceDef chk.env n`, so the delayed-branch agreement uses
   one shared sequence law rather than two unrelated predicates.

The result is a **positive-direction correspondence**: the hypotheses that
prove the model's `P2WSHSpend` also make the real `verifyWitnessProgram` return
`.ok`. No converse (vendor `.ok` implies model acceptance) and no
negative-direction rejection theorem is claimed at the vendor level.

## 2. Files changed

| File | Change |
|---|---|
| `LnLean/Proofs/Bitcoin/InterpreterBridgeTargets.lean` | New bridge module. Imports `Bitcoin.Interpreter.Defs` and `LnLean.Proofs.Bitcoin.SpendTargets`; adds serialization, parsing, concrete wire lists, funding execution, `to_local` delayed execution, model instantiation and agreement theorems. |
| `agents/reports/swarm5/S5-L1-INTERP.md` | This report. |

`LnLean/Proofs/Bitcoin/SpendTargets.lean` is unchanged. The bridge is a client
of the frozen vendor API; no vendored declaration was modified.

## 3. What is mechanised

### 3.1 Serialization and parsing

- `serializeStmts (fundingProg a b) = serializeOpcodes (fundingOps a b)`.
- `serializeStmts (toLocalProg revocationKey delayedPaymentKey csv) =
  serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)`.
- `parseWire (serializeOpcodes (toLocalOps ...)) =
  some (toLocalWireOps ...)`, with the exact wire/AST/next-offset triples.
- The `to_local` script size is proved to be 77 bytes for 33-byte keys.

### 3.2 Funding execution

`funding_interpreters_agree` reduces the real
`verifyWitnessProgram 6 [dummy, s1, s2, script] 0 (hashSha256 script)
{} {} chk false` to `.ok`, and simultaneously proves the model's
`P2WSHSpend (vendorLaws chk script) msg (hashSha256 script) script
(fundingProg a b) [s2, s1, dummy]`.

The vendored `OP_CHECKMULTISIG` step is fully computed: `cmsLoop`,
`cmsCleanup`, encoding checks, the two script-number decodes and the two ECDSA
calls. The only cryptographic inputs are
`chk.base.checkECDSASignature s1 a.bytes script .witnessV0 default = true` and
the corresponding call for `s2`.

### 3.3 `to_local` delayed branch

The wire list starts with the empty selector on top and a signature below it:

```text
machine stack: [ByteArray.empty, sig]
```

The vendored machine executes `OP_IF` (takes the `OP_ELSE` path), pushes the
two-byte delay, runs `OP_CSV` with `flags.csv = true`, drops the delay, pushes
the delayed-payment key, closes the conditional, and runs `OP_CHECKSIG`.
The final state is proved to be

```text
{ stack := [0x01], alt := [], vf := [], opCount := 6, codeSep := 0, vwLeft := none }
```

with fuel `10`. Sequence decoding is not hidden: the theorems take

```lean
(hdec : decodeNum ({} : PolicyFlags) (delayBytes csv) 5 = .ok n)
(hnn  : 0 ≤ n)
(hdis : Int.toNat n &&& SEQUENCE_LOCKTIME_DISABLE_FLAG = 0)
(hseq : checkSequenceDef chk.env n = true)
```

as explicit inputs. These are decidable for concrete `csv` and a concrete
`LocktimeEnv`; the lane does not construct the environment from a transaction.

## 4. Exact signatures

Names are in
`LnLean.Proofs.Bitcoin.InterpreterBridgeTargets` unless qualified. `ScriptNum`
is `Bitcoin.Numeric.ScriptNum` (`Int`). The pretty-printer shows
`{} : PolicyFlags` as `{ }`.

### 4.1 Model law

```lean
def vendorLaws (chk : ScriptChecker) (scriptCode : ByteArray) : InterpreterLaws

def vendorLawsCSV (chk : ScriptChecker) (scriptCode : ByteArray)
    (n : Bitcoin.Numeric.ScriptNum) : InterpreterLaws
```

`vendorLaws` sets

```lean
sigCheck := fun pk _msg sig =>
  chk.base.checkECDSASignature sig pk scriptCode .witnessV0
    (default : Bitcoin.Crypto.Seam.ScriptExecutionData)
csvOk := fun _ => true
cltvOk := fun _ => true
sha256 := hashSha256
hash160 := hashRipemd160
```

`vendorLawsCSV` changes only `csvOk`:

```lean
{ vendorLaws chk scriptCode with csvOk := fun _ => checkSequenceDef chk.env n }
```

The model's `msg` parameter is intentionally unused by the signature law:
BIP 143 sighash construction remains with the caller/vendor checker.

### 4.2 Serialization, parsing and size

```lean
theorem serializeOpcodes_toLocal_size
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (hr : revocationKey.bytes.size = 33)
    (hd : delayedPaymentKey.bytes.size = 33) :
    (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)).size = 77

theorem toLocal_serialize_eq
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (hr : revocationKey.bytes.size ≤ 75)
    (hd : delayedPaymentKey.bytes.size ≤ 75) :
    serializeStmts (toLocalProg revocationKey delayedPaymentKey csv) =
      serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)

theorem toLocal_parseWire
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (hr : revocationKey.bytes.size = 33)
    (hd : delayedPaymentKey.bytes.size = 33) :
    parseWire (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)) =
      some (toLocalWireOps revocationKey delayedPaymentKey csv)
```

The funding analogues (`funding_serialize_eq`, `funding_parseWire`,
`fundingOps_wf`, `fundingProg_wf`) are in the same module.

### 4.3 Vendor execution, delayed branch

All five theorems share the key-size, decode/non-negativity/disable-bit,
sequence and delayed-key signature hypotheses. They differ only in the
execution entry point and the extra witness-size/program hypotheses.

```lean
theorem evalFrom_toLocalWireOps_delayed
    (chk : ScriptChecker) (revocationKey delayedPaymentKey : PubKey)
    (csv : Blocks) (sig : ByteArray) (n : Bitcoin.Numeric.ScriptNum)
    (hr : revocationKey.bytes.size = 33)
    (hd : delayedPaymentKey.bytes.size = 33)
    (hdec : decodeNum ({} : PolicyFlags) (delayBytes csv) 5 = .ok n)
    (hnn : 0 ≤ n)
    (hdis : Int.toNat n &&& SEQUENCE_LOCKTIME_DISABLE_FLAG = 0)
    (hseq : checkSequenceDef chk.env n = true)
    (hsig : chk.base.checkECDSASignature sig delayedPaymentKey.bytes
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      .witnessV0 (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true) :
    evalFrom
      { flags := ({ csv := true } : ScriptFlags), pol := ({} : PolicyFlags), chk := chk,
        sv := .witnessV0,
        bytes := serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv),
        ed := (default : Bitcoin.Crypto.Seam.ScriptExecutionData) }
      10 (toLocalWireOps revocationKey delayedPaymentKey csv)
      { stack := [ByteArray.empty, sig], alt := [], vf := [], opCount := 0,
        codeSep := 0, vwLeft := none }
    = Except.ok
        { stack := [ByteArray.mk #[0x01]], alt := [], vf := [], opCount := 6,
          codeSep := 0, vwLeft := none }

theorem evalScriptBytes_toLocal_delayed
    ... same hypotheses ... :
    evalScriptBytes 10 ({ csv := true } : ScriptFlags) ({} : PolicyFlags)
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      [ByteArray.empty, sig] chk .witnessV0
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData)
    = Except.ok [ByteArray.mk #[0x01]]

theorem executeWitnessScript_toLocal_delayed
    (vwSer : Int) (hsigsz : sig.size ≤ 520) ... :
    executeWitnessScript 10 [sig, ByteArray.empty] vwSer
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      ({ csv := true } : ScriptFlags) ({} : PolicyFlags) chk .witnessV0 = .ok

theorem verifyWitnessProgram_toLocal_delayed
    (program : ByteArray) (hps : program.size = 32)
    (hprog : hashSha256
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)) = program) ... :
    verifyWitnessProgram 10
      [sig, ByteArray.empty,
        serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)]
      0 program ({ csv := true } : ScriptFlags) ({} : PolicyFlags) chk false = .ok
```

Note the witness order: `executeWitnessScript` and `verifyWitnessProgram`
receive witness order `[sig, ByteArray.empty, script]`; `evalScriptBytes`
receives the reversed machine stack `[ByteArray.empty, sig]`, and
`evalFrom` starts with the selector on top.

### 4.4 Model-side spend and agreement

```lean
theorem toLocal_model_spend_delayed
    (chk : ScriptChecker) (msg : ByteArray)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (n : Bitcoin.Numeric.ScriptNum)
    (hr : revocationKey.bytes.size = 33)
    (hd : delayedPaymentKey.bytes.size = 33)
    (hdec : decodeNum ({} : PolicyFlags) (delayBytes csv) 5 = .ok n)
    (hnn : 0 ≤ n)
    (hdis : Int.toNat n &&& SEQUENCE_LOCKTIME_DISABLE_FLAG = 0)
    (hseq : checkSequenceDef chk.env n = true)
    (hsig : chk.base.checkECDSASignature sig delayedPaymentKey.bytes
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      .witnessV0 (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true) :
    P2WSHSpend (vendorLawsCSV chk
        (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)) n)
      msg
      (hashSha256 (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)))
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      (toLocalProg revocationKey delayedPaymentKey csv) [zeroByte, sig]

theorem toLocal_delayed_interpreters_agree
    (chk : ScriptChecker) (msg : ByteArray)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (n : Bitcoin.Numeric.ScriptNum)
    (hr : revocationKey.bytes.size = 33)
    (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hdec : decodeNum ({} : PolicyFlags) (delayBytes csv) 5 = .ok n)
    (hnn : 0 ≤ n)
    (hdis : Int.toNat n &&& SEQUENCE_LOCKTIME_DISABLE_FLAG = 0)
    (hseq : checkSequenceDef chk.env n = true)
    (hsig : chk.base.checkECDSASignature sig delayedPaymentKey.bytes
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      .witnessV0 (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true) :
    verifyWitnessProgram 10
        [sig, ByteArray.empty,
          serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)]
        0
        (hashSha256 (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)))
        ({ csv := true } : ScriptFlags) ({} : PolicyFlags) chk false = .ok ∧
      P2WSHSpend (vendorLawsCSV chk
          (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)) n)
        msg
        (hashSha256 (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)))
        (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
        (toLocalProg revocationKey delayedPaymentKey csv) [zeroByte, sig]
```

### 4.5 Funding agreement

```lean
theorem funding_interpreters_agree
    (chk : ScriptChecker) (msg : ByteArray)
    (a b : PubKey) (s1 s2 dummy : ByteArray)
    (ha : a.bytes.size = 33) (hb : b.bytes.size = 33)
    (hs1 : s1.size ≤ 520) (hs2 : s2.size ≤ 520) (hdu : dummy.size ≤ 520)
    (h1 : chk.base.checkECDSASignature s1 a.bytes
      (serializeOpcodes (fundingOps a b)) .witnessV0
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true)
    (h2 : chk.base.checkECDSASignature s2 b.bytes
      (serializeOpcodes (fundingOps a b)) .witnessV0
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true) :
    verifyWitnessProgram 6
        [dummy, s1, s2, serializeOpcodes (fundingOps a b)] 0
        (hashSha256 (serializeOpcodes (fundingOps a b)))
        ({} : ScriptFlags) ({} : PolicyFlags) chk false = .ok ∧
      P2WSHSpend (vendorLaws chk (serializeOpcodes (fundingOps a b))) msg
        (hashSha256 (serializeOpcodes (fundingOps a b)))
        (serializeOpcodes (fundingOps a b))
        (fundingProg a b) [s2, s1, dummy]
```

## 5. Build

Vendored module and the bridge were built under the shared lock:

```bash
cd /home/ubuntu/ln-lean-repair
export PATH=/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build Bitcoin.Interpreter.Defs
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Proofs.Bitcoin.InterpreterBridgeTargets
```

Results:

- `Bitcoin.Interpreter.Defs`: RC `0`.
- `LnLean.Proofs.Bitcoin.InterpreterBridgeTargets`: **RC `0`**,
  `Build completed successfully (31 jobs)`.
- Remaining diagnostics are linter warnings only: unused `simp` arguments in
  the `to_local` computation, one deprecated `if_neg` name, and unused
  decode/non-negativity hypotheses in `toLocal_model_spend_delayed` (kept so
  its hypothesis set matches the agreement theorem). No errors, no `sorry`.

No full `lake build` was run, as required by the lane rules.

## 6. Axiom audit

`#print axioms` was run from `/tmp/opencode/axioms_tl.lean` with
`lake env lean` against the built module. Results:

```text
serializeOpcodes_toLocal_size          [propext, Quot.sound]
funding_interpreters_agree             [propext, Classical.choice, Quot.sound]
evalFrom_toLocalWireOps_delayed        [propext, Classical.choice, Quot.sound]
evalScriptBytes_toLocal_delayed        [propext, Classical.choice, Quot.sound]
executeWitnessScript_toLocal_delayed   [propext, Classical.choice, Quot.sound]
verifyWitnessProgram_toLocal_delayed   [propext, Classical.choice, Quot.sound]
toLocal_model_spend_delayed            [propext, Classical.choice, Quot.sound]
toLocal_delayed_interpreters_agree     [propext, Classical.choice, Quot.sound]
```

Every result is a subset of the allowed
`{propext, Quot.sound, Classical.choice}`. No new axiom was introduced.

## 7. Forbidden-token scan

```bash
grep -nE "sorry|axiom|admit|native_decide|unsafe|implemented_by" \
  LnLean/Proofs/Bitcoin/SpendTargets.lean \
  LnLean/Proofs/Bitcoin/InterpreterBridgeTargets.lean
```

Output: `NONE`.

## 8. Scope caveats and exact remaining boundary

1. **`to_local` delay decode is a hypothesis.** The theorems do not derive
   `decodeNum ({} : PolicyFlags) (delayBytes csv) 5 = .ok n` from `csv`.
   For concrete `csv` it is decidable. Because `delayBytes` is a fixed-width
   two-byte **sign-magnitude** script number, a delay with the high bit set
   decodes negative; the bridge therefore assumes `0 ≤ n` explicitly. A
   derivation from raw `csv` should require `csv < 0x8000` (or change the
   delay encoding, which would be a model/seam decision outside this lane).
2. **Sequence environment is a hypothesis.** `hdis` and `hseq` are the
   vendored disable-bit test and `checkSequenceDef chk.env n = true`. The lane
   does not construct `chk.env` from a commitment transaction or witness.
3. **Flags are pinned.** The delayed execution uses
   `ScriptFlags = { csv := true }` and default `PolicyFlags` (in particular
   `minimalData = false`). `OP_CSV` with `flags.csv = false` would take the
   no-op branch and is not covered.
4. **Positive direction only.** The agreement theorem proves that the shared
   hypotheses yield both vendor `.ok` and model `P2WSHSpend`. It does not
   prove the converse, and it does not prove that a bad signature or a failing
   sequence check makes the vendor verifier fail. The model-side negative
   theorems in `SpendTargets` remain model-level statements.
5. **Funding uses default flags/policy.** The funding theorem uses
   `{} : ScriptFlags` and `{} : PolicyFlags`; it does not model DERSIG,
   NULLDUMMY or other policy gates. The two ECDSA calls are hypotheses, not
   proved cryptographic facts.
6. **BIP 143 sighash is not constructed.** `msg` is passed to the model's law
   but is unused by `vendorLaws`/`vendorLawsCSV`; the vendored checker receives
   the script code and `ScriptExecutionData` directly.
7. **Revocation branch is not vendor-mechanised.** The model already proves
   `toLocalOutput_revocation_spendable` in `SpendTargets`; this lane does not
   add a vendor `evalFrom` computation for the `OP_IF` true path.
8. **No consensus-spendability claim.** The result is a correspondence between
   one model execution and the vendored interpreter under explicit
   environment/cryptographic hypotheses. It is not a full `VerifyScript`
   consensus theorem, does not cover P2SH-wrapped witnesses, and does not
   derive the P2WSH program from `FundingParams`.
9. **Vendor API is frozen.** The module is a client of
   `Bitcoin.Interpreter.Defs`; no vendor source or generated file was changed.

## 9. Integration steps (for the parent)

1. **Root import.** Add to `LnLean.lean`, in the `LnLean.Proofs.Bitcoin`
   block:

   ```lean
   import LnLean.Proofs.Bitcoin.InterpreterBridgeTargets
   ```

   Place it after `LnLean.Proofs.Bitcoin.SpendTargets` (the bridge imports it).

2. **Traceability module list.** Add
   `"LnLean.Proofs.Bitcoin.InterpreterBridgeTargets"` next to
   `"LnLean.Proofs.Bitcoin.SpendTargets"` in
   `LnLean/Proofs/Traceability.lean`.

3. **Catalog / issue text.** The lane was forbidden from editing
   `Obligations.lean`, `Traceability.lean`, and `docs/OPEN-ISSUES.md`. For
   `L1-01`, `L1-02` and `L1-07`, recommended wording:

   > The vendored `Bitcoin.Interpreter.Defs` evaluator now builds. The
   > `SpendTargets` serializer and wire list are proved equal to the vendor
   > printer/parser, the funding 2-of-2 script is executed end to end by
   > `verifyWitnessProgram`, and the `to_local` delayed branch is executed
   > through `OP_IF`/`OP_CSV`/`OP_DROP`/`OP_CHECKSIG`. The remaining boundary
   > is explicit: decoded delay `n`, its non-negativity/disable-bit conditions,
   > the `LocktimeEnv`, and the ECDSA calls are hypotheses; the revocation
   > branch and BIP 143 sighash construction are not vendor-bridged.

   If a single catalog declaration is wanted, use
   `LnLean.Proofs.Bitcoin.InterpreterBridgeTargets.funding_interpreters_agree`
   for the funding row and
   `LnLean.Proofs.Bitcoin.InterpreterBridgeTargets.toLocal_delayed_interpreters_agree`
   for the delayed `to_local` row. Do not describe either as unconditional
   consensus spendability.

4. **No changes needed in `SpendTargets.lean`.** Its theorem names and
   signatures are preserved; the bridge only imports and instantiates them.

## 10. Reproduction

```bash
cd /home/ubuntu/ln-lean-repair
export PATH=/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH

LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Proofs.Bitcoin.InterpreterBridgeTargets

grep -nE "sorry|axiom|admit|native_decide|unsafe|implemented_by" \
  LnLean/Proofs/Bitcoin/SpendTargets.lean \
  LnLean/Proofs/Bitcoin/InterpreterBridgeTargets.lean

LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake env lean /tmp/opencode/axioms_tl.lean
```

## 11. Blockers

None for the owned scope. The remaining gaps are deliberate, named
boundaries: raw delay/environment construction, the vendor revocation branch,
BIP 143 sighash construction, and the absence of vendor-level negative
theorems. They are candidates for a follow-up lane; they are not hidden
assumptions in the statements above.
