# S6-L1-SIGHASH — BIP 143 witness-v0 model feeding the vendored-interpreter bridge

**Lane:** `S6-L1-SIGHASH` (`L1-08`, `L1-07`).
**Worktree:** `/home/ubuntu/ln-lean-repair`
**Verdict:** completed for the assigned scope. The BIP 143 witness-v0
preimage is modelled explicitly and proved byte-equal to the frozen vendored
implementation; the digest is then wired into the existing vendored-interpreter
bridge through the real `ecdsaEntry`, and the bridge's former opaque
`checkECDSASignature` hypothesis is proved equivalent to a verifier call over
that digest. No unconditional consensus-spendability claim is made.

- Lane files:
  - `LnLean/Bitcoin/Sighash.lean` — new, 545 lines.
  - `LnLean/Proofs/Bitcoin/SighashBridgeTargets.lean` — new, 366 lines.
  - `agents/reports/swarm6/S6-L1-SIGHASH.md` — this report.
- `InterpreterBridgeTargets.lean`, `SpendTargets.lean`, `LnLean.lean`,
  `Obligations.lean`, `Traceability.lean`, `AxiomAudit.lean`, shared docs,
  scripts, other lanes' files, and vendor sources were **not** modified.
- No Git write was performed.

## 1. Result in one paragraph

`LnLean.Bitcoin.Sighash` defines the ten BIP 143 witness-v0 preimage fields in
consensus order (`Preimage`), serializes them from scratch (`encode`), derives
the fields from a `Bitcoin.Data.Tx` (`ofTx`), hashes them with the vendored
seam hash (`digest`), and adds BIP 143's out-of-range-input guard
(`sighashWitnessV0`). The serializer and digest are proved byte-equal to
`Bitcoin.SigHash.bip143MsgL` / `signatureHashBip143Impl` and to the
interface-level `signatureHashBip143`
(`bL_encode_ofTx`, `sighashWitnessV0_eq_vendorImpl`,
`sighashWitnessV0_eq_interface`). `SighashBridgeTargets` builds the vendored
`ScriptChecker` for an input by combining the real `ecdsaEntry` with
`hasAmount := true`, a sighash dispatch (`.witnessV0 → model digest`, other
versions → vendored legacy), and a `LocktimeEnv` constructed from the
transaction's version, locktime and signing input's `nSequence`. For a
non-empty signature and valid pubkey it proves

```lean
(checkerOf verify tx nIn amount).base.checkECDSASignature
    sig pk scriptCode .witnessV0 ed
  = verify (sig.extract 0 (sig.size - 1)) pk
      (sighashWitnessV0 tx nIn scriptCode (hashtypeOf sig) amount)
```

(`checker_consumes_model_digest`), hence the bridge hypothesis is *equivalent*
to the model-digest verification
(`bridge_ecdsa_hypothesis_iff_model_verify`). The wave-5 funding and delayed
`to_local` agreement theorems are then instantiated at this checker
(`funding_sighash_interpreters_agree`,
`toLocal_sighash_interpreters_agree`), with the locktime/sequence environment
tied to the transaction fields by `sighash_commits_locktimeEnv`.

## 2. Files changed

| File | Change |
|---|---|
| `LnLean/Bitcoin/Sighash.lean` | New BIP 143 witness-v0 model: byte serializers, three sub-hashes, ten-field preimage, `ofTx`, `encode`, `digest`, guarded `sighashWitnessV0`, exact vendor-agreement theorems, and mechanized ANYONECANPAY/zero-sub-hash omissions. |
| `LnLean/Proofs/Bitcoin/SighashBridgeTargets.lean` | New bridge: hashtype extraction, transaction-derived `LocktimeEnv`, sighash dispatch, wired `ScriptChecker`, digest-consumption theorem, funding/`to_local` composition theorems and commitment projections. |
| `agents/reports/swarm6/S6-L1-SIGHASH.md` | This report. |

No vendor declaration was edited. The bridge is a client of
`Bitcoin.SigHash.Interface`, `Bitcoin.Crypto.Seam.Entry` and the wave-5
`InterpreterBridgeTargets` API.

## 3. What is mechanised

### 3.1 Byte serialization

The model has its own

```lean
serU32LE : UInt32 → ByteArray
serU64LE : UInt64 → ByteArray
compactSize : Nat → ByteArray
serOutpoint : OutPoint → ByteArray
serTxOut : TxOut → ByteArray
```

and proves each equal to the vendored BIP 143 serializer through the list view
`Bitcoin.Serialization.bL`:

```lean
bL_serU32LE, bL_serU64LE, bL_compactSize, bL_serOutpoint, bL_serTxOut,
bL_zeroHash, bL_dsha, length_bL
```

The fold/list identifications used by the sub-hashes are
`foldl_append_nil`, `bL_fold_serOutpoint`, `bL_fold_serU32` and
`bL_fold_serTxOut`.

### 3.2 The three sub-hashes and the documented omissions

```lean
hashPrevoutsOf (tx : Tx) (ht : UInt32) : ByteArray
hashSequenceOf (tx : Tx) (ht : UInt32) : ByteArray
hashOutputsOf  (tx : Tx) (nIn : Nat) (ht : UInt32) : ByteArray
```

are proved equal to `hashPrevoutsL`, `hashSequenceL` and `hashOutputsL`
(`bL_hashPrevoutsOf`, `bL_hashSequenceOf`, `bL_hashOutputsOf`).

BIP 143's omissions are positive lemmas, not hidden assumptions:

```lean
hashPrevoutsOf_eq_zero_of_acp
hashSequenceOf_eq_zero_of_acp
hashSequenceOf_eq_zero_of_single
hashSequenceOf_eq_zero_of_none
hashOutputsOf_eq_zero_of_none
hashOutputsOf_eq_zero_of_single_oor
```

The ANYONECANPAY omission is mechanized end to end:
`sighashWitnessV0_withVin_acp` proves that with the ACP bit set, replacing all
other inputs (same length, same `nIn` outpoint/sequence) leaves the digest
unchanged. The complementary `hashPrevoutsOf_of_acp_false` exposes the full
prevout fold when ACP is clear. No hash injectivity is claimed.

### 3.3 Ten-field preimage and vendor equality

`Preimage` contains, in consensus order, version, `hashPrevouts`,
`hashSequence`, outpoint, scriptCode, amount, sequence, `hashOutputs`,
locktime and hashtype. `encode` writes exactly those bytes, with CompactSize
for the scriptCode and 8-byte LE for the amount. `digest` is the vendored
seam `sha256d`.

The central byte-exactness results are:

```lean
bL_encode_ofTx
sighashWitnessV0_eq_vendorImpl
sighashWitnessV0_eq_interface
sighashWitnessV0_size
```

`sighashWitnessV0_eq_vendorImpl` is equality with the frozen vendored
`signatureHashBip143Impl`, i.e. the transliteration of Core's
`SignatureHash(WITNESS_V0)`. `sighashWitnessV0_eq_interface` is the same
statement at the `Bitcoin.SigHash.signatureHashBip143` interface used by the
checker wiring. `sighashWitnessV0_size` proves the digest is 32 bytes.

### 3.4 The wired checker and digest consumption

The bridge defines

```lean
hashtypeOf (sig : ByteArray) : UInt32
locktimeEnvOf (tx : Tx) (nIn : Nat) : LocktimeEnv
sighashDispatch (tx : Tx) (nIn : Nat) (amount : Amount) :
  ByteArray → UInt8 → SigVersion → ByteArray
checkerOf (verify : ByteArray → ByteArray → ByteArray → Bool)
  (tx : Tx) (nIn : Nat) (amount : Amount) : ScriptChecker
```

`hashtypeOf` widens the signature's last byte to the `UInt32` that the
vendored `SignatureHash` API takes. `locktimeEnvOf` uses
`tx.version`, `tx.locktime` and `(tx.vin.getD nIn dummyTxIn).sequence`;
`dummyTxIn` is shared with `LnLean.Bitcoin.Sighash` so the preimage projection
and the environment are definitionally aligned. `sighashDispatch` sends
`.witnessV0` to `sighashWitnessV0` and every other ECDSA-reachable version to
the vendored `signatureHashLegacy`. `checkerOf` is

```lean
{ base := ecdsaEntry verify (sighashDispatch tx nIn amount) true
  env  := locktimeEnvOf tx nIn }
```

The `true` amount flag records that the caller supplies the spent amount;
the missing-amount failure path (`SWT-055`) is therefore not reachable here.
The main theorem is `checker_consumes_model_digest`; its iff face
`bridge_ecdsa_hypothesis_iff_model_verify` is the exact interface used by the
composition theorems.

### 3.5 Funding and `to_local` composition

`funding_sighash_interpreters_agree` instantiates the wave-5
`funding_interpreters_agree` at `checkerOf verify tx nIn amount`, with both
signature hypotheses written as verifier calls over
`sighashWitnessV0 tx nIn (serializeOpcodes (fundingOps a b)) (hashtypeOf si)
amount`. It returns vendor `.ok`, the model `P2WSHSpend` with that digest as
`msg`, and the two wired checker hypotheses.

`toLocal_sighash_interpreters_agree` does the same for the delayed `to_local`
branch. Its sequence hypothesis is now

```lean
hseq : checkSequenceDef (locktimeEnvOf tx nIn) n = true
```

rather than an arbitrary environment, and its signature hypothesis is the
verifier call over the model digest on the `to_local` witness script.
`sighash_commits_locktimeEnv` proves the three fields read by the vendored
`OP_CSV`/`OP_CLTV` checker are exactly the version, locktime and sequence
fields that enter the BIP 143 preimage.

## 4. Exact signatures

Names are in `LnLean.Bitcoin.Sighash` unless qualified as
`SighashBridgeTargets`.

### 4.1 Model

```lean
structure Preimage where
  version : UInt32
  hashPrevouts : ByteArray
  hashSequence : ByteArray
  outpoint : OutPoint
  scriptCode : ByteArray
  amount : Amount
  sequence : UInt32
  hashOutputs : ByteArray
  lockTime : UInt32
  hashType : UInt32

def encode (p : Preimage) : ByteArray

def ofTx (tx : Tx) (nIn : Nat) (scriptCode : ByteArray)
    (ht : UInt32) (amount : Amount) : Preimage

def digest (p : Preimage) : ByteArray

def sighashWitnessV0 (tx : Tx) (nIn : Nat) (scriptCode : ByteArray)
    (ht : UInt32) (amount : Amount) : ByteArray
```

```lean
theorem bL_encode_ofTx (tx : Tx) (nIn : Nat) (scriptCode : ByteArray)
    (ht : UInt32) (amount : Amount) :
    Bitcoin.Serialization.bL (encode (ofTx tx nIn scriptCode ht amount)) =
      Bitcoin.SigHash.bip143MsgL tx nIn
        (Bitcoin.Serialization.bL scriptCode) ht amount

theorem sighashWitnessV0_eq_vendorImpl (tx : Tx) (nIn : Nat)
    (scriptCode : ByteArray) (ht : UInt32) (amount : Amount) :
    sighashWitnessV0 tx nIn scriptCode ht amount =
      Bitcoin.SigHash.signatureHashBip143Impl tx nIn
        (Bitcoin.Serialization.bL scriptCode) ht amount

theorem sighashWitnessV0_eq_interface (tx : Tx) (nIn : Nat)
    (scriptCode : ByteArray) (ht : UInt32) (amount : Amount) :
    sighashWitnessV0 tx nIn scriptCode ht amount =
      Bitcoin.SigHash.signatureHashBip143 tx nIn ⟨scriptCode⟩ ht amount

theorem sighashWitnessV0_size (tx : Tx) (nIn : Nat)
    (scriptCode : ByteArray) (ht : UInt32) (amount : Amount) :
    (sighashWitnessV0 tx nIn scriptCode ht amount).size = 32
```

```lean
theorem ofTx_withVin_acp (tx : Tx) (vin' : List TxIn) (nIn : Nat)
    (scriptCode : ByteArray) (ht : UInt32) (amount : Amount)
    (hacp : Bitcoin.SigHash.htAcp ht = true)
    (_hlen : vin'.length = tx.vin.length)
    (hinput : vin'.getD nIn dummyTxIn = tx.vin.getD nIn dummyTxIn) :
    ofTx (withVin tx vin') nIn scriptCode ht amount =
      ofTx tx nIn scriptCode ht amount

theorem sighashWitnessV0_withVin_acp (tx : Tx) (vin' : List TxIn)
    (nIn : Nat) (scriptCode : ByteArray) (ht : UInt32) (amount : Amount)
    (hacp : Bitcoin.SigHash.htAcp ht = true)
    (hlen : vin'.length = tx.vin.length)
    (hinput : vin'.getD nIn dummyTxIn = tx.vin.getD nIn dummyTxIn) :
    sighashWitnessV0 (withVin tx vin') nIn scriptCode ht amount =
      sighashWitnessV0 tx nIn scriptCode ht amount

theorem hashPrevoutsOf_of_acp_false (tx : Tx) (ht : UInt32)
    (h : Bitcoin.SigHash.htAcp ht = false) :
    hashPrevoutsOf tx ht =
      dsha (tx.vin.foldl (fun acc i => acc ++ serOutpoint i.prevout)
        ByteArray.empty)
```

### 4.2 Bridge

```lean
def hashtypeOf (sig : ByteArray) : UInt32
def locktimeEnvOf (tx : Tx) (nIn : Nat) : LocktimeEnv

def sighashDispatch (tx : Tx) (nIn : Nat) (amount : Amount) :
    ByteArray → UInt8 → SigVersion → ByteArray

def checkerOf (verify : ByteArray → ByteArray → ByteArray → Bool)
    (tx : Tx) (nIn : Nat) (amount : Amount) : ScriptChecker
```

```lean
theorem checker_consumes_model_digest
    (verify : ByteArray → ByteArray → ByteArray → Bool)
    (tx : Tx) (nIn : Nat) (amount : Amount)
    (sig pk scriptCode : ByteArray) (ed : ScriptExecutionData)
    (hpk : Bitcoin.Crypto.Seam.Der.isValidPubKey pk = true)
    (hne : 0 < sig.size) :
    (checkerOf verify tx nIn amount).base.checkECDSASignature
        sig pk scriptCode .witnessV0 ed =
      verify (sig.extract 0 (sig.size - 1)) pk
        (sighashWitnessV0 tx nIn scriptCode (hashtypeOf sig) amount)

theorem bridge_ecdsa_hypothesis_iff_model_verify
    (verify : ByteArray → ByteArray → ByteArray → Bool)
    (tx : Tx) (nIn : Nat) (amount : Amount)
    (sig pk scriptCode : ByteArray) (ed : ScriptExecutionData)
    (hpk : Bitcoin.Crypto.Seam.Der.isValidPubKey pk = true)
    (hne : 0 < sig.size) :
    ((checkerOf verify tx nIn amount).base.checkECDSASignature
        sig pk scriptCode .witnessV0 ed = true) ↔
      verify (sig.extract 0 (sig.size - 1)) pk
        (sighashWitnessV0 tx nIn scriptCode (hashtypeOf sig) amount) = true
```

`funding_sighash_interpreters_agree` has the same wave-5 hypotheses
(`ha`, `hb : key size = 33`; `hs1`, `hs2`, `hdu : size ≤ 520`) plus
`hpka`, `hpkb` (`isValidPubKey`) and `hne1`, `hne2` (`0 < sig.size`), and
replaces the two opaque checker hypotheses with

```lean
(h1 : verify (s1.extract 0 (s1.size - 1)) a.bytes
  (sighashWitnessV0 tx nIn (serializeOpcodes (fundingOps a b))
    (hashtypeOf s1) amount) = true)
(h2 : verify (s2.extract 0 (s2.size - 1)) b.bytes
  (sighashWitnessV0 tx nIn (serializeOpcodes (fundingOps a b))
    (hashtypeOf s2) amount) = true)
```

Its conclusion is the conjunction of vendor `.ok`, model `P2WSHSpend` with the
digest as `msg`, and the two wired `checkECDSASignature` results.

`toLocal_sighash_interpreters_agree` has the wave-5 key-size, delay-decoding,
non-negativity, disable-bit and `ScriptFlags := { csv := true }` hypotheses,
replaces `hseq` by `checkSequenceDef (locktimeEnvOf tx nIn) n = true`, and
replaces the opaque signature hypothesis by

```lean
(hsig : verify (sig.extract 0 (sig.size - 1)) delayedPaymentKey.bytes
  (sighashWitnessV0 tx nIn
    (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
    (hashtypeOf sig) amount) = true)
```

Its conclusion is the conjunction of vendor `.ok`, model `P2WSHSpend` with the
digest as `msg`, and the wired `checkECDSASignature` result.

Locktime/context linkage:

```lean
theorem sighash_commits_locktimeEnv (tx : Tx) (nIn : Nat)
    (scriptCode : ByteArray) (ht : UInt32) (amount : Amount) :
    (ofTx tx nIn scriptCode ht amount).version =
        (locktimeEnvOf tx nIn).txVersion.toUInt32 ∧
      (ofTx tx nIn scriptCode ht amount).lockTime =
        (locktimeEnvOf tx nIn).txLockTime ∧
      (ofTx tx nIn scriptCode ht amount).sequence =
        (locktimeEnvOf tx nIn).txSequence
```

Commitment projections:

```lean
theorem digest_commits_amount ...
theorem digest_commits_scriptCode ...
theorem digest_hashType_of_sig ...
```

## 5. Build

```bash
cd /home/ubuntu/ln-lean-repair
export PATH=/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Bitcoin.Sighash LnLean.Proofs.Bitcoin.SighashBridgeTargets
```

Result: **RC 0**, `Build completed successfully (40 jobs)`.

Both modules were also built separately earlier under the same lock
(`LnLean.Bitcoin.Sighash`: 22 jobs, RC 0; the bridge import closure: 40 jobs).
Remaining diagnostics are linter warnings only: deprecated `if_neg`/`if_pos`
names in the new model and pre-existing vendor warnings. There are no errors,
no `sorry`, and no new axioms.

No full `lake build` was run, as required by the lane rules.

## 6. Axiom audit

`#print axioms` was run under the shared lock with

```bash
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake env lean /tmp/opencode/axioms_sighash.lean
```

All audited declarations depend only on
`{propext, Classical.choice, Quot.sound}`:

```text
sighashWitnessV0_eq_vendorImpl
sighashWitnessV0_eq_interface
bL_encode_ofTx
sighashWitnessV0_size
sighashWitnessV0_withVin_acp
hashPrevoutsOf_of_acp_false
checker_consumes_model_digest
bridge_ecdsa_hypothesis_iff_model_verify
funding_sighash_interpreters_agree
toLocal_sighash_interpreters_agree
sighash_commits_locktimeEnv
digest_commits_amount
digest_commits_scriptCode
digest_hashType_of_sig
       → [propext, Classical.choice, Quot.sound]
```

No new axiom was introduced.

## 7. Forbidden-token scan

```bash
grep -nE '\b(sorry|admit|native_decide|unsafe|implemented_by)\b|@\[implemented_by|^[[:space:]]*axiom\b' \
  LnLean/Bitcoin/Sighash.lean \
  LnLean/Proofs/Bitcoin/SighashBridgeTargets.lean
```

Output: `SCAN CLEAN`.

## 8. Scope caveats and exact remaining boundary

1. **The EC verifier is an explicit parameter.** `checkerOf` and both
   composition theorems take
   `verify : ByteArray → ByteArray → ByteArray → Bool`. This lane does not
   instantiate it to a concrete secp256k1 implementation and does not prove
   signature unforgeability (assumption C3). The ECDSA calls in the
   composition theorems are consequences of the caller's `h1`/`h2`/`hsig`
   verifier hypotheses, not cryptographic facts proved here.
2. **The amount is explicit context.** `amount` is committed to by the
   preimage (`digest_commits_amount`), but the model does not prove that it
   equals the value of the output referenced by the outpoint. It is supplied
   by the caller, exactly as in the vendored checker API.
3. **P2WSH positive path only.** `verifyWitnessProgram` is used on the
   native P2WSH path, with default `ScriptFlags`/`PolicyFlags` for funding
   and `{ csv := true }` for the delayed `to_local` branch. P2SH-wrapped
   witnesses, DERSIG/NULLDUMMY and other policy gates, and script-flag
   variations are outside the result, as in wave 5.
4. **Positive direction only.** The composition theorems prove that the shared
   hypotheses yield vendor `.ok`, the model `P2WSHSpend`, and the wired
   checker results. They do not prove the converse (vendor `.ok` implies model
   acceptance), nor a vendor-level negative/rejection theorem. The negative
   theorems in `SpendTargets` remain model-level statements.
5. **The wave-5 model law still ignores its `msg` argument.** The existing
   `vendorLaws`/`vendorLawsCSV` `sigCheck` passes the scriptCode to the
   checker and ignores the model `msg`; this lane was forbidden to edit
   `InterpreterBridgeTargets.lean`. Consequently the composition theorems
   place the digest in the model `msg` position and independently prove that
   the *vendor checker* computes and consumes that same digest
   (`checker_consumes_model_digest`). They do not claim that the wave-5 model
   law itself binds `msg` to the signature check.
6. **Out-of-range inputs are totalized.** `sighashWitnessV0` returns the
   32-byte zero digest when `tx.vin.length ≤ nIn`, matching the vendored
   `signatureHashBip143Impl` guard. Core's corresponding case is an
   `assert`-guarded programming error; the bridge's liveness hypotheses always
   index a real input. `locktimeEnvOf` likewise uses the shared
   `Sighash.dummyTxIn` (sequence `0`) only as a `getD` totalization device.
7. **The locktime environment is constructed from fields, not from
   validity.** `locktimeEnvOf` uses `tx.version`, `tx.locktime` and the
   signing input's `nSequence`. The lane proves those are the same fields the
   BIP 143 preimage commits to, but does not prove that the transaction is
   consensus-valid, that `csv` corresponds to a real commitment, or that the
   signed input is the one the script expects.
8. **No independent BIP 143 vector is asserted.** The evidence for exactness
   is byte equality with the frozen vendored implementation
   (`signatureHashBip143Impl`, itself the vendored Core transliteration), not
   an external test-vector run. The vendored API is treated as the target and
   was not edited. The non-witness-v0 arm of `sighashDispatch` is the frozen
   vendored `signatureHashLegacy`, not a second independently modelled legacy
   digest; only witness-v0 is byte-modelled in this lane.
9. **Hash primitive is the vendored seam.** `digest` uses
   `Bitcoin.Crypto.Seam.sha256d`. The byte agreement is definitional at the
   seam; no collision resistance or hash injectivity is assumed or proved.
10. **No unconditional consensus spendability.** The result is a conditional
    correspondence between the model digest, the wired vendored checker, and
    the vendored interpreter under the named EC/context/flag hypotheses. It is
    not a full `VerifyScript` consensus theorem.

## 9. Integration steps (for the parent)

1. **Root imports.** In `LnLean.lean`, add

   ```lean
   import LnLean.Bitcoin.Sighash
   ```

   next to the other `LnLean.Bitcoin` imports (after `LnLean.Bitcoin.Seam`),
   and add

   ```lean
   import LnLean.Proofs.Bitcoin.SighashBridgeTargets
   ```

   in the `LnLean.Proofs.Bitcoin` block after
   `LnLean.Proofs.Bitcoin.InterpreterBridgeTargets`.

2. **Traceability module list.** Add
   `"LnLean.Bitcoin.Sighash"` and
   `"LnLean.Proofs.Bitcoin.SighashBridgeTargets"` to `lneanModules` in
   `LnLean/Proofs/Traceability.lean`.

3. **Catalog entries.** Suggested headline declarations:

   ```lean
   LnLean.Bitcoin.Sighash.sighashWitnessV0_eq_vendorImpl
   LnLean.Bitcoin.Sighash.sighashWitnessV0_eq_interface
   LnLean.Proofs.Bitcoin.SighashBridgeTargets.checker_consumes_model_digest
   LnLean.Proofs.Bitcoin.SighashBridgeTargets.funding_sighash_interpreters_agree
   LnLean.Proofs.Bitcoin.SighashBridgeTargets.toLocal_sighash_interpreters_agree
   ```

   Use `sighashWitnessV0_eq_vendorImpl` as the byte-exactness row and
   `checker_consumes_model_digest` as the digest-consumption row. Do not
   describe either as unconditional consensus spendability.

4. **`docs/OPEN-ISSUES.md` wording.** For `L1-08` (and the corresponding
   `L1-07` boundary text), recommend:

   > `LnLean.Bitcoin.Sighash` now constructs the BIP 143 witness-v0 preimage
   > from the transaction, input index, scriptCode, hashtype and spent amount,
   > and proves it byte-equal to the vendored `signatureHashBip143Impl` /
   > `signatureHashBip143`. `SighashBridgeTargets` wires that digest into the
   > vendored `ecdsaEntry` with `hasAmount := true` and proves the bridge's
   > `checkECDSASignature` hypothesis is equivalent to the verifier call over
   > `sighashWitnessV0`; the funding and delayed `to_local` agreement theorems
   > are instantiated at this checker, with `LocktimeEnv` derived from
   > `tx.version`, `tx.locktime` and the signing input's `nSequence`. The
   > remaining boundary is explicit: the concrete EC verifier, the outpoint
   > amount, policy/script flags, the P2WSH positive direction, and the
   > wave-5 model law's unused `msg` parameter.

   Keep `L1-08` open until the parent decides whether the EC verifier
   instantiation and negative-direction/consensus-validity context are in
   scope; the sighash construction itself is no longer an assumption.

5. **No changes needed in `InterpreterBridgeTargets.lean`.** Its theorem names
   and signatures are preserved; this lane only imports and instantiates them.

## 10. Reproduction

```bash
cd /home/ubuntu/ln-lean-repair
export PATH=/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH

LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Bitcoin.Sighash LnLean.Proofs.Bitcoin.SighashBridgeTargets

grep -nE '\b(sorry|admit|native_decide|unsafe|implemented_by)\b|@\[implemented_by|^[[:space:]]*axiom\b' \
  LnLean/Bitcoin/Sighash.lean \
  LnLean/Proofs/Bitcoin/SighashBridgeTargets.lean

LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake env lean /tmp/opencode/axioms_sighash.lean
```

## 11. Blockers

None for the owned scope. The remaining gaps are deliberate, named
boundaries: concrete EC verifier instantiation, amount/outpoint and
transaction-validity context, policy/flag coverage, the P2WSH positive
direction, and the wave-5 `vendorLaws` `msg` parameter. They are candidates
for a follow-up lane; they are not hidden assumptions in the statements above.
