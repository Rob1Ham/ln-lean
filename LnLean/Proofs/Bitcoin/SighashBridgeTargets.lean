import Bitcoin.Crypto.Seam.Der
import Bitcoin.Crypto.Seam.Entry
import Bitcoin.SigHash.Interface
import LnLean.Bitcoin.Sighash
import LnLean.Proofs.Bitcoin.InterpreterBridgeTargets

/-!
# Consuming the BIP 143 model digest in the vendored-interpreter bridge

This wave-6 module (lane `S6-L1-SIGHASH`) closes the sighash boundary named in
`agents/reports/swarm5/S5-L1-INTERP.md` §8 item 6 and in open issues `L1-07` /
`L1-08`.  The wave-5 bridge `InterpreterBridgeTargets` executed the BOLT 3
funding and `to_local` scripts through the vendored interpreter, but the
signature hypotheses were opaque:

```lean
chk.base.checkECDSASignature sig pk scriptCode .witnessV0 ed = true
```

with the BIP 143 digest supplied (or not) by the caller.  This module builds
the digest from transaction fields in `LnLean.Bitcoin.Sighash`, wires it into
the vendored ECDSA seam entry (`ecdsaEntry`), and proves that the bridge's
opaque hypothesis is exactly the verifier call over the model digest.

## Main results

* `checker_consumes_model_digest` — for a non-empty signature and a valid
  pubkey, the wired checker's witness-v0 ECDSA verdict is
  `verify (sig minus hashtype) pk (sighashWitnessV0 ...)`.  The digest is not a
  free parameter: it is computed from the transaction, input index,
  scriptCode, popped hashtype and spent amount.
* `bridge_ecdsa_hypothesis_iff_model_verify` — the bridge's signature
  hypothesis is *equivalent* to the model-level verification over that digest.
* `funding_sighash_interpreters_agree` — the wave-5 funding agreement theorem
  instantiated at the wired checker, with the model digest as the model
  `msg`.  It retains every wave-5 hypothesis (33-byte keys, witness-element
  sizes) and adds only the pubkey/signature-well-formedness inputs needed to
  reach the vendored checker's EC math.
* `toLocal_sighash_interpreters_agree` — the same for the delayed `to_local`
  branch.  The sequence environment is now *constructed* (`locktimeEnvOf`) from
  the transaction version, locktime and signing input's `nSequence`, so the
  wave-5 `hseq : checkSequenceDef chk.env n = true` hypothesis is a hypothesis
  about the real transaction context, not an arbitrary environment.
* `sighash_commits_locktimeEnv` — the BIP 143 preimage's version, `nLockTime`
  and `nSequence` fields are exactly the fields the vendored `OP_CSV` reads
  through `LocktimeEnv`.

## Scope (no unconditional consensus claim)

The EC verifier `verify` is an explicit parameter (assumption C3's concrete
instantiation is the caller's choice; this lane does not import the deep
curve implementation).  The spent `amount` is an explicit context parameter:
this module proves that it is committed to by the digest, not that it equals
the value of the referenced outpoint.  `verifyWitnessProgram` is the P2WSH
path of the vendored interpreter with default script flags and policy flags;
P2SH-wrapped witnesses, DERSIG/NULLDUMMY policy gates and the negative
direction (vendor failure ⇒ model rejection) remain outside the result, as in
wave 5.  There is no claim of unconditional consensus spendability.
-/

namespace LnLean.Proofs.Bitcoin.SighashBridgeTargets

set_option autoImplicit false

open Bitcoin.Data
open Bitcoin.Activation
open Bitcoin.Interpreter
open Bitcoin.Script.Parser
open Bitcoin.Crypto.Seam
open Bitcoin.Crypto.Seam.Entry
open LnLean
open LnLean.Bitcoin.Sighash
open LnLean.Proofs.Bitcoin.SpendTargets
open LnLean.Proofs.Bitcoin.InterpreterBridgeTargets

/-! ## Transaction context -/

/-- Inhabitant for `getD` on an out-of-range input index, shared with
`LnLean.Bitcoin.Sighash` so that the preimage projections and the locktime
environment use the same totalization term definitionally.  The bridge's
liveness hypotheses always index a real input; the value is only a
totalization device. -/
def dummyTxIn : TxIn := LnLean.Bitcoin.Sighash.dummyTxIn

/-- The low byte of a signature is the BIP 143 hashtype, widened to the
`UInt32` the vendored `SignatureHash` API takes (Core: `int nHashType`,
interpreter.cpp:1707-1712). -/
def hashtypeOf (sig : ByteArray) : UInt32 :=
  UInt32.ofNat (sig[sig.size - 1]!).toNat

/-- The vendored `LocktimeEnv` for input `nIn` of `tx`: transaction version,
transaction locktime, and the signing input's `nSequence`.  These are exactly
the three transaction fields `OP_CSV`/`OP_CLTV` read (IC-2). -/
def locktimeEnvOf (tx : Tx) (nIn : Nat) : LocktimeEnv :=
  { txVersion := tx.version
    txLockTime := tx.locktime
    txSequence := (tx.vin.getD nIn dummyTxIn).sequence }

@[simp] theorem locktimeEnvOf_txVersion (tx : Tx) (nIn : Nat) :
    (locktimeEnvOf tx nIn).txVersion = tx.version := rfl

@[simp] theorem locktimeEnvOf_txLockTime (tx : Tx) (nIn : Nat) :
    (locktimeEnvOf tx nIn).txLockTime = tx.locktime := rfl

@[simp] theorem locktimeEnvOf_txSequence (tx : Tx) (nIn : Nat) :
    (locktimeEnvOf tx nIn).txSequence = (tx.vin.getD nIn dummyTxIn).sequence := rfl

/-- The three context fields read by the vendored locktime/sequence checker
are exactly the three preimage fields the model commits to.  This is the
locktime half of the bridge: a valid `OP_CSV` delay is checked against the
same `nVersion`/`nLockTime`/`nSequence` values that enter the BIP 143
preimage (the preimage does **not** carry `nLockTime` for legacy scripts, but
BIP 143 witness-v0 does). -/
theorem sighash_commits_locktimeEnv (tx : Tx) (nIn : Nat)
    (scriptCode : ByteArray) (ht : UInt32) (amount : Amount) :
    (ofTx tx nIn scriptCode ht amount).version =
        (locktimeEnvOf tx nIn).txVersion.toUInt32 ∧
      (ofTx tx nIn scriptCode ht amount).lockTime =
        (locktimeEnvOf tx nIn).txLockTime ∧
      (ofTx tx nIn scriptCode ht amount).sequence =
        (locktimeEnvOf tx nIn).txSequence :=
  ⟨rfl, rfl, rfl⟩

/-! ## The wired checker -/

/-- The ECDSA sighash dispatch of the vendored `GenericTransactionSignatureChecker`
(interpreter.cpp:1718-1722): `WITNESS_V0 → BIP143`, otherwise legacy.  The
witness-v0 arm is this lane's model digest; the legacy arm is the vendored
legacy digest, so the checker is total and faithful for both ECDSA-reachable
signature versions.  Taproot/tapscript never reach `CheckECDSASignature` in
consensus; the legacy arm is a harmless totalization there. -/
def sighashDispatch (tx : Tx) (nIn : Nat) (amount : Amount) :
    ByteArray → UInt8 → SigVersion → ByteArray :=
  fun scriptCode ht sv =>
    match sv with
    | .witnessV0 =>
        LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn scriptCode
          (UInt32.ofNat ht.toNat) amount
    | _ =>
        Bitcoin.SigHash.signatureHashLegacy tx nIn ⟨scriptCode⟩
          (UInt32.ofNat ht.toNat)

/-- The vendored `ScriptChecker` for input `nIn`: the real ECDSA seam adapter
with `hasAmount = true` (the caller supplies the spent amount; SWT-055's
missing-data failure is therefore not on this path), the BIP 143 model
sighash dispatch, and the transaction-derived `LocktimeEnv`. -/
def checkerOf (verify : ByteArray → ByteArray → ByteArray → Bool)
    (tx : Tx) (nIn : Nat) (amount : Amount) : ScriptChecker :=
  { base := ecdsaEntry verify (sighashDispatch tx nIn amount) true
    env := locktimeEnvOf tx nIn }

theorem checkerOf_base (verify : ByteArray → ByteArray → ByteArray → Bool)
    (tx : Tx) (nIn : Nat) (amount : Amount) :
    (checkerOf verify tx nIn amount).base =
      ecdsaEntry verify (sighashDispatch tx nIn amount) true := rfl

theorem checkerOf_env (verify : ByteArray → ByteArray → ByteArray → Bool)
    (tx : Tx) (nIn : Nat) (amount : Amount) :
    (checkerOf verify tx nIn amount).env = locktimeEnvOf tx nIn := rfl

/-- The witness-v0 arm of the dispatch is the model's digest, definitionally. -/
theorem sighashDispatch_witnessV0 (tx : Tx) (nIn : Nat) (amount : Amount)
    (scriptCode : ByteArray) (sig : ByteArray) :
    sighashDispatch tx nIn amount scriptCode (sig[sig.size - 1]!) .witnessV0 =
      LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn scriptCode
        (hashtypeOf sig) amount := rfl

/-! ## The digest consumed by the bridge -/

/-- **The bridge's signature hypothesis is the model's digest verification.**
For a valid pubkey and a non-empty signature, the vendored witness-v0 ECDSA
entry computes exactly `sighashWitnessV0` from the transaction context and
hands it to the EC verifier together with the signature body (the signature
minus its hashtype byte).  This is the theorem that turns the wave-5 opaque
`checkECDSASignature` hypothesis into a statement about the model digest. -/
theorem checker_consumes_model_digest
    (verify : ByteArray → ByteArray → ByteArray → Bool)
    (tx : Tx) (nIn : Nat) (amount : Amount)
    (sig pk scriptCode : ByteArray) (ed : ScriptExecutionData)
    (hpk : Bitcoin.Crypto.Seam.Der.isValidPubKey pk = true)
    (hne : 0 < sig.size) :
    (checkerOf verify tx nIn amount).base.checkECDSASignature
        sig pk scriptCode .witnessV0 ed =
      verify (sig.extract 0 (sig.size - 1)) pk
        (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn scriptCode
          (hashtypeOf sig) amount) := by
  rw [checkerOf_base]
  rw [ecdsaEntry_pops_hashtype verify (sighashDispatch tx nIn amount) true
    sig pk scriptCode .witnessV0 ed hpk hne (by intro _; rfl)]
  rfl

/-- **If-and-only-if face of the bridge hypothesis.**  The wave-5 bridge's
`checkECDSASignature ... = true` premise for a witness-v0 signature is
equivalent to the explicit verifier call over the model digest.  This is the
exact interface the funding and `to_local` composition theorems below use. -/
theorem bridge_ecdsa_hypothesis_iff_model_verify
    (verify : ByteArray → ByteArray → ByteArray → Bool)
    (tx : Tx) (nIn : Nat) (amount : Amount)
    (sig pk scriptCode : ByteArray) (ed : ScriptExecutionData)
    (hpk : Bitcoin.Crypto.Seam.Der.isValidPubKey pk = true)
    (hne : 0 < sig.size) :
    ((checkerOf verify tx nIn amount).base.checkECDSASignature
        sig pk scriptCode .witnessV0 ed = true) ↔
      verify (sig.extract 0 (sig.size - 1)) pk
        (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn scriptCode
          (hashtypeOf sig) amount) = true := by
  rw [checker_consumes_model_digest verify tx nIn amount sig pk scriptCode ed hpk hne]

/-! ## Funding composition -/

/-- **Funding: the model digest drives the vendored interpreter.**  This is
`InterpreterBridgeTargets.funding_interpreters_agree` with the checker wired
to the BIP 143 model digest.  The two signature hypotheses are now explicit
EC verifier calls over `sighashWitnessV0` on the funding witness script.

The first two conjuncts are the wave-5 result: the vendored
`verifyWitnessProgram` returns `.ok`, and the model's `P2WSHSpend` holds with
the digest as its `msg`.  The last two conjuncts state that the bridge's own
ECDSA hypotheses are exactly those model-digest verifications. -/
theorem funding_sighash_interpreters_agree
    (verify : ByteArray → ByteArray → ByteArray → Bool)
    (tx : Tx) (nIn : Nat) (amount : Amount)
    (a b : PubKey) (s1 s2 dummy : ByteArray)
    (ha : a.bytes.size = 33) (hb : b.bytes.size = 33)
    (hs1 : s1.size ≤ 520) (hs2 : s2.size ≤ 520) (hdu : dummy.size ≤ 520)
    (hpka : Bitcoin.Crypto.Seam.Der.isValidPubKey a.bytes = true)
    (hpkb : Bitcoin.Crypto.Seam.Der.isValidPubKey b.bytes = true)
    (hne1 : 0 < s1.size) (hne2 : 0 < s2.size)
    (h1 : verify (s1.extract 0 (s1.size - 1)) a.bytes
      (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn
        (serializeOpcodes (fundingOps a b)) (hashtypeOf s1) amount) = true)
    (h2 : verify (s2.extract 0 (s2.size - 1)) b.bytes
      (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn
        (serializeOpcodes (fundingOps a b)) (hashtypeOf s2) amount) = true) :
    verifyWitnessProgram 6
        [dummy, s1, s2, serializeOpcodes (fundingOps a b)] 0
        (hashSha256 (serializeOpcodes (fundingOps a b)))
        ({} : ScriptFlags) ({} : PolicyFlags)
        (checkerOf verify tx nIn amount) false = .ok ∧
      P2WSHSpend (vendorLaws (checkerOf verify tx nIn amount)
          (serializeOpcodes (fundingOps a b)))
        (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn
          (serializeOpcodes (fundingOps a b)) (hashtypeOf s1) amount)
        (hashSha256 (serializeOpcodes (fundingOps a b)))
        (serializeOpcodes (fundingOps a b)) (fundingProg a b) [s2, s1, dummy] ∧
      (checkerOf verify tx nIn amount).base.checkECDSASignature s1 a.bytes
          (serializeOpcodes (fundingOps a b)) .witnessV0
          (default : ScriptExecutionData) = true ∧
      (checkerOf verify tx nIn amount).base.checkECDSASignature s2 b.bytes
          (serializeOpcodes (fundingOps a b)) .witnessV0
          (default : ScriptExecutionData) = true := by
  have hc1 : (checkerOf verify tx nIn amount).base.checkECDSASignature
      s1 a.bytes (serializeOpcodes (fundingOps a b)) .witnessV0
      (default : ScriptExecutionData) = true := by
    rw [checker_consumes_model_digest verify tx nIn amount s1 a.bytes
      (serializeOpcodes (fundingOps a b)) default hpka hne1]
    exact h1
  have hc2 : (checkerOf verify tx nIn amount).base.checkECDSASignature
      s2 b.bytes (serializeOpcodes (fundingOps a b)) .witnessV0
      (default : ScriptExecutionData) = true := by
    rw [checker_consumes_model_digest verify tx nIn amount s2 b.bytes
      (serializeOpcodes (fundingOps a b)) default hpkb hne2]
    exact h2
  have hbridge := funding_interpreters_agree (checkerOf verify tx nIn amount)
    (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn
      (serializeOpcodes (fundingOps a b)) (hashtypeOf s1) amount)
    a b s1 s2 dummy ha hb hs1 hs2 hdu hc1 hc2
  exact ⟨hbridge.1, hbridge.2, hc1, hc2⟩

/-! ## `to_local` delayed-branch composition -/

/-- **`to_local` delayed branch: transaction context + model digest.**  The
wave-5 `hseq` hypothesis is now `checkSequenceDef (locktimeEnvOf tx nIn) n`,
i.e. the vendored `OP_CSV` test against the transaction version, locktime and
signing input sequence.  The signature hypothesis is an explicit verifier
call over the model's BIP 143 digest on the `to_local` witness script.

The three conjuncts are: vendor `.ok`, the model `P2WSHSpend` with the digest
as `msg`, and the bridge's ECDSA hypothesis discharged by that digest. -/
theorem toLocal_sighash_interpreters_agree
    (verify : ByteArray → ByteArray → ByteArray → Bool)
    (tx : Tx) (nIn : Nat) (amount : Amount)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (n : Bitcoin.Numeric.ScriptNum)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hpk : Bitcoin.Crypto.Seam.Der.isValidPubKey delayedPaymentKey.bytes = true)
    (hne : 0 < sig.size)
    (hdec : decodeNum ({} : PolicyFlags) (delayBytes csv) 5 = .ok n)
    (hnn : 0 ≤ n)
    (hdis : Int.toNat n &&& SEQUENCE_LOCKTIME_DISABLE_FLAG = 0)
    (hseq : checkSequenceDef (locktimeEnvOf tx nIn) n = true)
    (hsig : verify (sig.extract 0 (sig.size - 1)) delayedPaymentKey.bytes
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
        (checkerOf verify tx nIn amount) false = .ok ∧
      P2WSHSpend (vendorLawsCSV (checkerOf verify tx nIn amount)
          (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)) n)
        (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn
          (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
          (hashtypeOf sig) amount)
        (hashSha256
          (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)))
        (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
        (toLocalProg revocationKey delayedPaymentKey csv) [zeroByte, sig] ∧
      (checkerOf verify tx nIn amount).base.checkECDSASignature sig
          delayedPaymentKey.bytes
          (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
          .witnessV0 (default : ScriptExecutionData) = true := by
  have hc : (checkerOf verify tx nIn amount).base.checkECDSASignature sig
      delayedPaymentKey.bytes
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      .witnessV0 (default : ScriptExecutionData) = true := by
    rw [checker_consumes_model_digest verify tx nIn amount sig
      delayedPaymentKey.bytes
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      default hpk hne]
    exact hsig
  have hbridge := toLocal_delayed_interpreters_agree
    (checkerOf verify tx nIn amount)
    (LnLean.Bitcoin.Sighash.sighashWitnessV0 tx nIn
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      (hashtypeOf sig) amount)
    revocationKey delayedPaymentKey csv sig n hr hd hsigsz hdec hnn hdis
    (by simpa [checkerOf] using hseq) hc
  exact ⟨hbridge.1, hbridge.2, hc⟩

/-! ## Scope boundaries as theorems -/

/-- The amount is a committed preimage field, so the digest is not
amount-agnostic: the preimage projection exposes it.  This is the strongest
statement available without a hash-injectivity assumption; it records *that*
the bridge's `amount` context parameter reaches the digest. -/
theorem digest_commits_amount (tx : Tx) (nIn : Nat) (scriptCode : ByteArray)
    (ht : UInt32) (amount : Amount) :
    (LnLean.Bitcoin.Sighash.ofTx tx nIn scriptCode ht amount).amount = amount :=
  rfl

/-- The scriptCode is a committed preimage field and is hashed as-is (BIP 143
witness-v0 uses the witness script directly; no `FindAndDelete`, no
`OP_CODESEPARATOR` splice).  The model's `ofTx` projection and the byte-level
`bL_encode_ofTx` make the placement explicit without claiming hash
injectivity. -/
theorem digest_commits_scriptCode (tx : Tx) (nIn : Nat) (scriptCode : ByteArray)
    (ht : UInt32) (amount : Amount) :
    (LnLean.Bitcoin.Sighash.ofTx tx nIn scriptCode ht amount).scriptCode =
      scriptCode :=
  rfl

/-- The digest's hashtype field is the popped signature byte, so the bridge's
verdict depends on the signature's trailing byte and not on hidden state. -/
theorem digest_hashType_of_sig (tx : Tx) (nIn : Nat) (scriptCode : ByteArray)
    (sig : ByteArray) (amount : Amount) :
    (LnLean.Bitcoin.Sighash.ofTx tx nIn scriptCode (hashtypeOf sig) amount).hashType =
      hashtypeOf sig :=
  rfl

end LnLean.Proofs.Bitcoin.SighashBridgeTargets
