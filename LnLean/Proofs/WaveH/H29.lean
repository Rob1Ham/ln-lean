import Bitcoin.Crypto.Ecdsa.Verify
import LnLean.Bitcoin.Sighash
import LnLean.Proofs.Bitcoin.SpendTargets
import LnLean.Proofs.Bitcoin.SighashBridgeTargets

/-!
# H29 — The model `sigCheck` law at the concrete vendored ECDSA verifier

Wave 8, lane `H29`; roadmap issues `L1-01` and `L1-07`.

Wave 4's `SpendTargets.InterpreterLaws` names the signature law as an opaque
field

```lean
sigCheck : ByteArray → ByteArray → ByteArray → Bool
```

and every funding / `to_local` execution theorem of waves 4–7 is conditional
on `L.sigCheck pk msg sig = true`.  Waves 6–7 shrank the gap twice: the
wave-6 `SighashBridgeTargets` proved that the *vendored seam* consumes the
model's BIP 143 digest (`checker_consumes_model_digest`), and wave 7's
`SequenceContextTargets` transferred the delayed `to_local` refinement to
`checkerOf Bitcoin.Crypto.Ecdsa.Verify.verifyImpl` (the real lax secp256k1
verifier).  What was still missing is the *law-level* identification: which
concrete `InterpreterLaws` instance does the model's `sigCheck` denote when the
message is the constructed digest, and what exactly must hold for the vendor
verifier to agree?

This module supplies that instance and the exact interface:

* `verifyImplLaws` — the concrete law: the signature check is
  `Bitcoin.Crypto.Ecdsa.Verify.verifyImpl (sigBody sig) pk msg`, i.e. the
  vendored lax secp256k1 verifier applied to the DER body (the BIP 143
  hash-type byte is the trailing byte, popped by the seam adapter) over the
  *given* message.  Unlike `InterpreterBridgeTargets.vendorLaws`, the message
  is consumed by the law rather than ignored: the law is therefore only
  faithful when its `msg` is the sighash of the signing input.
* `verifyImplLaws_sigCheck_eq_vendor_checker` — for the constructed BIP 143
  digest `sighashWitnessV0 tx nIn scriptCode (hashtypeOf sig) amount`, a valid
  pubkey (`Bitcoin.Crypto.Seam.Der.isValidPubKey pk = true`) and a non-empty
  signature, the law's verdict is *literally* the vendored checker's
  witness-v0 verdict
  `(checkerOf verifyImpl tx nIn amount).base.checkECDSASignature ...`.
  The message/sighash equation and the key-encoding premises are explicit.
* `verifyImplLaws_sigCheck_of_msg_eq` — the same identification with the
  digest supplied as a separate hypothesis `msg = sighashWitnessV0 ...`,
  so callers that build the digest elsewhere (e.g. the HTLC wire of `H09`)
  can reuse the interface unchanged.
* `vendorLaws_sigCheck_eq_verifyImpl` — the pre-existing wave-5/6 `vendorLaws`
  law is the same concrete verifier at the constructed digest, *and* it
  ignores its `msg` argument; this records exactly why waves 6–7 had to build
  the digest inside the checker.
* `accepts_funding_sigCheck` / `accepts_toLocal_delayed` — the converse
  extraction: model-level `Accepts` of the BOLT 3 funding program (resp. the
  delayed `to_local` branch) yields the two (resp. one) concrete
  `sigCheck` facts and the CSV fact.  These are the interface lemmas that let
  a model acceptance be handed to the vendored agreement theorems.
* `funding_verifyImplLaws_accepts_implies_vendor_ok` and
  `toLocal_delayed_verifyImplLaws_accepts_implies_vendor_ok` — therefore
  acceptance in the model at the concrete law implies the vendored
  `verifyWitnessProgram` returns `.ok`, for the funding 2-of-2 and delayed
  `to_local` programs, with the digest equations, 33-byte key sizes, witness
  element size bounds, `isValidPubKey`, decoded delay, non-negativity and
  disable-bit premises all explicit.
* Negative non-vacuity: `verifyImplLaws_sigCheck_empty_sig`,
  `verifyImplLaws_sigCheck_singleton` and
  `verifyImplLaws_sigCheck_empty_pk` are `false` by the vendor's own
  `verifyImpl_sig_nil` / `verifyImpl_pk_nil`; hence the instantiated law is not
  the constant-`true` law (`verifyImplLaws_sigCheck_ne_true`) and the funding
  program rejects an empty-signature witness
  (`not_accepts_funding_verifyImplLaws_empty_sigs`).

## What is *not* claimed (the missing link)

* **No positive EC witness is mechanized.**  `verifyImpl` performs 256-bit
  secp256k1 arithmetic; this module does not (and the kernel cannot cheaply)
  exhibit a concrete `(sig, pk, msg)` with `verifyImpl sig pk msg = true`.
  The positive direction therefore remains conditional on the verifier
  returning `true` — the exact algebraic face of assumption C3, now written at
  the vendor function instead of an abstract field.  `verifyImpl_sig_nil` is
  used only for the negative side.
* **No negative direction.**  The vendored agreement theorems are
  one-directional (`model ⇒ vendor .ok`); `vendor .ok ⇒ model Accepts` is not
  proved here and is not implied by any theorem in this tree.
* **DER strictness stays in the interpreter.**  `verifyImpl` is the *lax*
  parser (`parseDerLax`); BIP 66 strict-DER rejection is a script-flag gate
  above it (`ecdsaVerdict` / `isValidPubKey`), so the law here is the EC layer,
  not the policy layer.  `isValidPubKey pk = true` is the explicit key-encoding
  premise needed to pass the seam's `CPubKey::IsValid` gate.
* The spent `amount`, `scriptCode`, and input index remain explicit context
  parameters committed by the digest; nothing here proves they match the
  referenced outpoint's value or script.
* The model's `truthy` / 2-of-2-only `OP_CHECKMULTISIG` simplifications of
  `SpendTargets` are inherited unchanged.

## Anchors

* BIP 143 (signature hash for witness v0), BIP 66 (DER strictness), BIP 141
  (P2WSH), BIP 147 (NULLDUMMY).
* BOLT 3 §Funding Transaction Output and §`to_local` Output.
* `vendor/btc-lean-core/Bitcoin/Crypto/Ecdsa/Verify.lean:82` (`verifyImpl`),
  `:105` (`verifyImpl_sig_nil`), `:111` (`verifyImpl_pk_nil`).
* `vendor/btc-lean-core/Bitcoin/Crypto/Seam/Entry.lean:41` (`ecdsaVerdict`,
  hash-type pop and pubkey gate).
-/

namespace LnLean.Proofs.WaveH.H29

set_option autoImplicit false

open Bitcoin.Data
open Bitcoin.Activation
open Bitcoin.Script.Parser
open Bitcoin.Interpreter
open Bitcoin.Crypto.Seam
open LnLean
open LnLean.Bitcoin.Sighash
open LnLean.Proofs.Bitcoin.SpendTargets
open LnLean.Proofs.Bitcoin.InterpreterBridgeTargets
open LnLean.Proofs.Bitcoin.SighashBridgeTargets

/-! ## The DER signature body

`ecdsaVerdict` pops the BIP 143 hash-type byte before calling the EC verifier
(`sig.extract 0 (sig.size - 1)`, SWT-053).  The law below makes that step
explicit instead of hiding it inside the checker. -/

/-- The DER signature body: every byte except the trailing BIP 143 hash-type
byte.  For an empty signature this is `empty` (Nat subtraction saturates), which
is the value the vendor parser rejects. -/
def sigBody (sig : ByteArray) : ByteArray := sig.extract 0 (sig.size - 1)

@[simp] theorem sigBody_empty : sigBody ByteArray.empty = ByteArray.empty := by
  simp [sigBody]

theorem sigBody_singleton (x : UInt8) :
    sigBody (ByteArray.mk #[x]) = ByteArray.empty := by
  simp [sigBody]
  rfl

/-- The DER body of a non-empty signature has exactly one byte fewer. -/
theorem sigBody_size_of_pos (sig : ByteArray) (_h : 0 < sig.size) :
    (sigBody sig).size = sig.size - 1 := by
  simp [sigBody]

/-! ## The concrete `InterpreterLaws` instance -/

/-- **The model signature law at the vendored verifier.**  `sigCheck pk msg sig`
is `Bitcoin.Crypto.Ecdsa.Verify.verifyImpl` on the DER body, the pubkey
encoding and the *given* message.  The hash floor is the vendored
`hashSha256`/`hashRipemd160`, so the whole record is concrete.

`csvOk`/`cltvOk` are `true`: the funding program uses neither, and the delayed
`to_local` law is `verifyImplLawsCSV` below, which ties `csvOk` to the vendored
`checkSequenceDef`. -/
def verifyImplLaws : InterpreterLaws where
  sigCheck := fun pk msg sig =>
    Bitcoin.Crypto.Ecdsa.Verify.verifyImpl (sigBody sig) pk msg
  csvOk := fun _ => true
  cltvOk := fun _ => true
  sha256 := hashSha256
  hash160 := hashRipemd160

@[simp] theorem verifyImplLaws_sigCheck (pk msg sig : ByteArray) :
    verifyImplLaws.sigCheck pk msg sig =
      Bitcoin.Crypto.Ecdsa.Verify.verifyImpl (sigBody sig) pk msg := rfl

@[simp] theorem verifyImplLaws_sha256 (b : ByteArray) :
    verifyImplLaws.sha256 b = hashSha256 b := rfl

@[simp] theorem verifyImplLaws_hash160 (b : ByteArray) :
    verifyImplLaws.hash160 b = hashRipemd160 b := rfl

/-- The delayed-`to_local` variant: `csvOk` is the vendored sequence check for
one already-decoded `to_self_delay n`.  This is the law that matches
`InterpreterBridgeTargets.vendorLawsCSV`, but with the ECDSA field instantiated
at `verifyImpl` over the model message instead of a checker closure. -/
def verifyImplLawsCSV (tx : Tx) (nIn : Nat)
    (n : Bitcoin.Numeric.ScriptNum) : InterpreterLaws :=
  { verifyImplLaws with
    csvOk := fun _ => checkSequenceDef (locktimeEnvOf tx nIn) n }

@[simp] theorem verifyImplLawsCSV_sigCheck (tx : Tx) (nIn : Nat)
    (n : Bitcoin.Numeric.ScriptNum) (pk msg sig : ByteArray) :
    (verifyImplLawsCSV tx nIn n).sigCheck pk msg sig =
      Bitcoin.Crypto.Ecdsa.Verify.verifyImpl (sigBody sig) pk msg := rfl

@[simp] theorem verifyImplLawsCSV_csvOk (tx : Tx) (nIn : Nat)
    (n : Bitcoin.Numeric.ScriptNum) (d : ByteArray) :
    (verifyImplLawsCSV tx nIn n).csvOk d =
      checkSequenceDef (locktimeEnvOf tx nIn) n := rfl

/-! ## The law is the vendored one at the constructed BIP 143 digest -/

/-- **Headline bridge.**  For the constructed BIP 143 witness-v0 digest, a
pubkey that passes the vendored `CPubKey::IsValid` encoding gate, and a
non-empty signature, the model's `sigCheck` is *exactly* the vendored checker's
witness-v0 ECDSA verdict.  The digest is not a free parameter: it is
`sighashWitnessV0 tx nIn scriptCode (hashtypeOf sig) amount` (the trailing
signature byte selects the hash type), and the checker pops that byte before
handing the DER body to `verifyImpl`. -/
theorem verifyImplLaws_sigCheck_eq_vendor_checker
    (tx : Tx) (nIn : Nat) (amount : Amount)
    (scriptCode sig pk : ByteArray) (ed : ScriptExecutionData)
    (hpk : Bitcoin.Crypto.Seam.Der.isValidPubKey pk = true)
    (hne : 0 < sig.size) :
    verifyImplLaws.sigCheck pk
        (sighashWitnessV0 tx nIn scriptCode (hashtypeOf sig) amount) sig =
      (checkerOf Bitcoin.Crypto.Ecdsa.Verify.verifyImpl tx nIn amount).base.checkECDSASignature
        sig pk scriptCode .witnessV0 ed := by
  rw [verifyImplLaws_sigCheck,
    checker_consumes_model_digest Bitcoin.Crypto.Ecdsa.Verify.verifyImpl tx nIn amount
      sig pk scriptCode ed hpk hne]
  rfl

/-- Boolean form of the headline bridge: acceptance by the model law is
acceptance by the vendored checker, for the constructed digest. -/
theorem verifyImplLaws_sigCheck_true_iff_vendor_checker
    (tx : Tx) (nIn : Nat) (amount : Amount)
    (scriptCode sig pk : ByteArray) (ed : ScriptExecutionData)
    (hpk : Bitcoin.Crypto.Seam.Der.isValidPubKey pk = true)
    (hne : 0 < sig.size) :
    (verifyImplLaws.sigCheck pk
        (sighashWitnessV0 tx nIn scriptCode (hashtypeOf sig) amount) sig = true) ↔
      (checkerOf Bitcoin.Crypto.Ecdsa.Verify.verifyImpl tx nIn amount).base.checkECDSASignature
        sig pk scriptCode .witnessV0 ed = true := by
  rw [verifyImplLaws_sigCheck_eq_vendor_checker tx nIn amount scriptCode sig pk ed hpk hne]

/-- **Digest as an explicit premise.**  Callers that construct the digest
elsewhere (for example from the HTLC wire) state `msg = sighashWitnessV0 ...`
instead of inlining it.  This is the reusable form of the headline bridge. -/
theorem verifyImplLaws_sigCheck_of_msg_eq
    (tx : Tx) (nIn : Nat) (amount : Amount)
    (scriptCode sig pk msg : ByteArray) (ed : ScriptExecutionData)
    (hmsg : msg = sighashWitnessV0 tx nIn scriptCode (hashtypeOf sig) amount)
    (hpk : Bitcoin.Crypto.Seam.Der.isValidPubKey pk = true)
    (hne : 0 < sig.size) :
    verifyImplLaws.sigCheck pk msg sig =
      (checkerOf Bitcoin.Crypto.Ecdsa.Verify.verifyImpl tx nIn amount).base.checkECDSASignature
        sig pk scriptCode .witnessV0 ed := by
  rw [hmsg]
  exact verifyImplLaws_sigCheck_eq_vendor_checker tx nIn amount scriptCode sig pk ed hpk hne

/-- The BIP 143 hash type is the trailing signature byte, so the judge depends
on that byte and not on hidden state. -/
theorem hashtypeOf_eq_of_sig_eq (sig sig' : ByteArray)
    (h : sig = sig') : hashtypeOf sig = hashtypeOf sig' := by
  rw [h]

/-- The message the concrete law consumes has the vendor's 32-byte input
width (`bytesToNatBE msg % n` in `verifyImpl`); this records that the digest
is in the verifier's message domain rather than an arbitrary byte string. -/
theorem verifyImplLaws_digest_size (tx : Tx) (nIn : Nat) (scriptCode : ByteArray)
    (sig : ByteArray) (amount : Amount) :
    (sighashWitnessV0 tx nIn scriptCode (hashtypeOf sig) amount).size = 32 :=
  sighashWitnessV0_size tx nIn scriptCode (hashtypeOf sig) amount

/-! ## The pre-existing wave-5/6 `vendorLaws` is the same verifier -/

/-- **Why waves 6–7 built the digest inside the checker.**  The wave-5
`vendorLaws` signature field ignores the model's `msg` and asks the checker for
its witness-v0 verdict; instantiating that checker at `verifyImpl` shows the
field is the concrete verifier applied to
`sighashWitnessV0 ... (hashtypeOf sig) amount`, *independently of `msg`*.
So `vendorLaws` is faithful only when the model `msg` is that digest — which is
exactly what `verifyImplLaws` makes a premise. -/
theorem vendorLaws_sigCheck_eq_verifyImpl
    (tx : Tx) (nIn : Nat) (amount : Amount) (scriptCode pk msg sig : ByteArray)
    (hpk : Bitcoin.Crypto.Seam.Der.isValidPubKey pk = true)
    (hne : 0 < sig.size) :
    (vendorLaws (checkerOf Bitcoin.Crypto.Ecdsa.Verify.verifyImpl tx nIn amount)
        scriptCode).sigCheck pk msg sig =
      Bitcoin.Crypto.Ecdsa.Verify.verifyImpl (sigBody sig) pk
        (sighashWitnessV0 tx nIn scriptCode (hashtypeOf sig) amount) := by
  simp only [vendorLaws]
  simpa [sigBody] using
    (checker_consumes_model_digest Bitcoin.Crypto.Ecdsa.Verify.verifyImpl tx nIn amount
      sig pk scriptCode (default : ScriptExecutionData) hpk hne)

/-- At the constructed digest the two model laws coincide (the `msg` argument
is irrelevant to `vendorLaws`, and here it is the digest). -/
theorem vendorLaws_sigCheck_eq_verifyImplLaws
    (tx : Tx) (nIn : Nat) (amount : Amount) (scriptCode pk sig : ByteArray)
    (hpk : Bitcoin.Crypto.Seam.Der.isValidPubKey pk = true)
    (hne : 0 < sig.size) :
    (vendorLaws (checkerOf Bitcoin.Crypto.Ecdsa.Verify.verifyImpl tx nIn amount)
        scriptCode).sigCheck pk
        (sighashWitnessV0 tx nIn scriptCode (hashtypeOf sig) amount) sig =
      verifyImplLaws.sigCheck pk
        (sighashWitnessV0 tx nIn scriptCode (hashtypeOf sig) amount) sig := by
  rw [vendorLaws_sigCheck_eq_verifyImpl tx nIn amount scriptCode pk
    (sighashWitnessV0 tx nIn scriptCode (hashtypeOf sig) amount) sig hpk hne,
    verifyImplLaws_sigCheck]

/-! ## Negative, non-vacuous instances

The vendor's own structural theorems reject the empty and one-byte encodings
and the empty pubkey.  These are the concrete false instances of the law; the
positive direction stays conditional on the EC arithmetic (assumption C3), see
the module header. -/

@[simp] theorem verifyImplLaws_sigCheck_empty_sig (pk msg : ByteArray) :
    verifyImplLaws.sigCheck pk msg ByteArray.empty = false := by
  rw [verifyImplLaws_sigCheck, sigBody_empty,
    Bitcoin.Crypto.Ecdsa.Verify.verifyImpl_sig_nil]

/-- A one-byte "signature" is only a hash-type byte: the DER body is empty and
the vendor parser rejects it (this is why the seam's `sig.size = 0` reject and
the DER parse both matter). -/
theorem verifyImplLaws_sigCheck_singleton (x : UInt8) (pk msg : ByteArray) :
    verifyImplLaws.sigCheck pk msg (ByteArray.mk #[x]) = false := by
  rw [verifyImplLaws_sigCheck, sigBody_singleton,
    Bitcoin.Crypto.Ecdsa.Verify.verifyImpl_sig_nil]

@[simp] theorem verifyImplLaws_sigCheck_empty_pk (msg sig : ByteArray) :
    verifyImplLaws.sigCheck ByteArray.empty msg sig = false := by
  rw [verifyImplLaws_sigCheck,
    Bitcoin.Crypto.Ecdsa.Verify.verifyImpl_pk_nil]

/-- The instantiated law is not the constant-`true` law: an empty signature is
rejected for every pubkey and message. -/
theorem verifyImplLaws_sigCheck_ne_true :
    verifyImplLaws.sigCheck ≠ fun (_ _ _ : ByteArray) => true := by
  intro h
  have h' := congrFun (congrFun (congrFun h ByteArray.empty) ByteArray.empty)
    ByteArray.empty
  have hf : verifyImplLaws.sigCheck ByteArray.empty ByteArray.empty
      ByteArray.empty = false := verifyImplLaws_sigCheck_empty_sig _ _
  rw [hf] at h'
  exact Bool.false_ne_true h'

/-- The bare vendored verifier is not vacuously true, so the positive
hypotheses of the bridge theorems are not free. -/
theorem verifyImpl_not_trivial :
    ¬ ∀ (pk msg : ByteArray),
      Bitcoin.Crypto.Ecdsa.Verify.verifyImpl ByteArray.empty pk msg = true := by
  intro h
  have h' := h ByteArray.empty ByteArray.empty
  rw [Bitcoin.Crypto.Ecdsa.Verify.verifyImpl_sig_nil] at h'
  exact Bool.false_ne_true h'

/-! ## Extracting the concrete `sigCheck` facts from model acceptance -/

/-- A machine-level `bool` verdict equal to the canonical `true` element is
`true`. -/
theorem boolBytes_eq_oneByte {x : Bool} (h : boolBytes x = oneByte) : x = true := by
  cases x with
  | false => exact absurd h (by simp [boolBytes, zeroByte_ne_oneByte])
  | true => rfl

/-- A false *first* funding signature already makes the multisig step push
`false` (the existing `exec_funding_one_signature` covers `true`/`false`). -/
theorem exec_funding_first_bad (L : InterpreterLaws) (msg : ByteArray)
    (a b : PubKey) (dummy s1 s2 : ByteArray)
    (h1 : L.sigCheck a.bytes msg s1 = false) :
    execStmts L msg (fundingProg a b) [s2, s1, dummy] = some [zeroByte] := by
  simp [fundingProg, execStmts, execStmt, step, h1]

/-- **Funding acceptance exposes both signature checks.**  If the model
accepts the BOLT 3 2-of-2 funding program on the machine stack
`[sig2, sig1, dummy]`, then both ordered keys' `sigCheck`s hold over the same
message.  This is the converse of `exec_funding` used to feed a model
acceptance into the vendored agreement theorem. -/
theorem accepts_funding_sigCheck (L : InterpreterLaws) (msg : ByteArray)
    (a b : PubKey) (dummy s1 s2 : ByteArray)
    (h : Accepts L msg (fundingProg a b) [s2, s1, dummy]) :
    L.sigCheck a.bytes msg s1 = true ∧ L.sigCheck b.bytes msg s2 = true := by
  by_cases h1 : L.sigCheck a.bytes msg s1 = true
  · by_cases h2 : L.sigCheck b.bytes msg s2 = true
    · exact ⟨h1, h2⟩
    · exfalso
      have h2f : L.sigCheck b.bytes msg s2 = false := by
        cases hv : L.sigCheck b.bytes msg s2 <;> simp_all
      have h' : execStmts L msg (fundingProg a b) [s2, s1, dummy] = some [oneByte] := h
      rw [exec_funding_one_signature L msg a b dummy s1 s2 h1 h2f] at h'
      exact absurd h' (by simp [zeroByte_ne_oneByte])
  · exfalso
    have h1f : L.sigCheck a.bytes msg s1 = false := by
      cases hv : L.sigCheck a.bytes msg s1 <;> simp_all
    have h' : execStmts L msg (fundingProg a b) [s2, s1, dummy] = some [oneByte] := h
    rw [exec_funding_first_bad L msg a b dummy s1 s2 h1f] at h'
    exact absurd h' (by simp [zeroByte_ne_oneByte])

/-- **Delayed-branch acceptance exposes the CSV and signature checks.**  If the
model accepts the `to_local` program on `[selector = empty, sig]`, then the CSV
law holds on the delay element and the delayed key's `sigCheck` holds. -/
theorem accepts_toLocal_delayed (L : InterpreterLaws) (msg : ByteArray)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks) (sig : ByteArray)
    (h : Accepts L msg (toLocalProg revocationKey delayedPaymentKey csv)
      [zeroByte, sig]) :
    L.csvOk (delayBytes csv) = true ∧ L.sigCheck delayedPaymentKey.bytes msg sig = true := by
  by_cases hc : L.csvOk (delayBytes csv) = true
  · by_cases hs : L.sigCheck delayedPaymentKey.bytes msg sig = true
    · exact ⟨hc, hs⟩
    · exfalso
      have hsf : L.sigCheck delayedPaymentKey.bytes msg sig = false := by
        cases hv : L.sigCheck delayedPaymentKey.bytes msg sig <;> simp_all
      have hz : execStmts L msg (toLocalProg revocationKey delayedPaymentKey csv)
          [zeroByte, sig] = some [zeroByte] := by
        have hc' : L.csvOk (LnLean.Bitcoin.toLocalDelayBytes csv) = true := by simpa using hc
        simp [toLocalProg, execStmts, execStmt, step, hc', hsf]
      have h' : execStmts L msg (toLocalProg revocationKey delayedPaymentKey csv)
          [zeroByte, sig] = some [oneByte] := h
      rw [hz] at h'
      exact absurd h' (by simp [zeroByte_ne_oneByte])
  · exfalso
    have hcf : L.csvOk (delayBytes csv) = false := by
      cases hv : L.csvOk (delayBytes csv) <;> simp_all
    have hn := exec_toLocal_delayed_csv_fails L msg revocationKey delayedPaymentKey
      csv sig hcf
    have h' : execStmts L msg (toLocalProg revocationKey delayedPaymentKey csv)
        [zeroByte, sig] = some [oneByte] := h
    rw [hn] at h'
    exact absurd h' (by simp)

/-! ## Model acceptance ⇒ vendored acceptance, at the concrete verifier

The two theorems below are the sharp end of the lane: they take a *model*
acceptance at `verifyImplLaws`, the explicit digest equations, and the vendor
key/size/sequence premises, and conclude that the real fuel-bounded
`verifyWitnessProgram` returns `.ok`. -/

/-- **Funding 2-of-2: model acceptance at `verifyImplLaws` ⇒ vendor `.ok`.**
`D` is the model's message; the two digest equations say it is the BIP 143
witness-v0 digest of the funding witness script for each signature's hash type.
The remaining premises are exactly the wave-5/6 vendored agreement hypotheses
(key sizes, witness element bounds, `CPubKey::IsValid` encodings, non-empty
signatures). -/
theorem funding_verifyImplLaws_accepts_implies_vendor_ok
    (tx : Tx) (nIn : Nat) (amount : Amount)
    (a b : PubKey) (s1 s2 dummy : ByteArray) (D : ByteArray)
    (ha : a.bytes.size = 33) (hb : b.bytes.size = 33)
    (hs1 : s1.size ≤ 520) (hs2 : s2.size ≤ 520) (hdu : dummy.size ≤ 520)
    (hpka : Bitcoin.Crypto.Seam.Der.isValidPubKey a.bytes = true)
    (hpkb : Bitcoin.Crypto.Seam.Der.isValidPubKey b.bytes = true)
    (hne1 : 0 < s1.size) (hne2 : 0 < s2.size)
    (hD1 : D = sighashWitnessV0 tx nIn (serializeOpcodes (fundingOps a b))
      (hashtypeOf s1) amount)
    (hD2 : D = sighashWitnessV0 tx nIn (serializeOpcodes (fundingOps a b))
      (hashtypeOf s2) amount)
    (h : Accepts verifyImplLaws D (fundingProg a b) [s2, s1, dummy]) :
    verifyWitnessProgram 6
        [dummy, s1, s2, serializeOpcodes (fundingOps a b)] 0
        (hashSha256 (serializeOpcodes (fundingOps a b)))
        ({} : ScriptFlags) ({} : PolicyFlags)
        (checkerOf Bitcoin.Crypto.Ecdsa.Verify.verifyImpl tx nIn amount) false = .ok := by
  obtain ⟨h1, h2⟩ := accepts_funding_sigCheck verifyImplLaws D a b dummy s1 s2 h
  have h1' : Bitcoin.Crypto.Ecdsa.Verify.verifyImpl (sigBody s1) a.bytes
      (sighashWitnessV0 tx nIn (serializeOpcodes (fundingOps a b))
        (hashtypeOf s1) amount) = true := by
    have h1m : Bitcoin.Crypto.Ecdsa.Verify.verifyImpl (sigBody s1) a.bytes D = true := by
      simpa [verifyImplLaws] using h1
    rwa [← hD1]
  have h2' : Bitcoin.Crypto.Ecdsa.Verify.verifyImpl (sigBody s2) b.bytes
      (sighashWitnessV0 tx nIn (serializeOpcodes (fundingOps a b))
        (hashtypeOf s2) amount) = true := by
    have h2m : Bitcoin.Crypto.Ecdsa.Verify.verifyImpl (sigBody s2) b.bytes D = true := by
      simpa [verifyImplLaws] using h2
    rwa [← hD2]
  exact (funding_sighash_interpreters_agree
    Bitcoin.Crypto.Ecdsa.Verify.verifyImpl tx nIn amount a b s1 s2 dummy
    ha hb hs1 hs2 hdu hpka hpkb hne1 hne2 h1' h2').1

/-- **Delayed `to_local`: model acceptance at `verifyImplLawsCSV` ⇒ vendor
`.ok`.**  The CSV law is the vendored `checkSequenceDef` at the decoded delay;
`hD` is the BIP 143 digest equation for the `to_local` witness script; the
decode, non-negativity and disable-bit premises are the wave-7 sequence-context
inputs, not new assumptions. -/
theorem toLocal_delayed_verifyImplLaws_accepts_implies_vendor_ok
    (tx : Tx) (nIn : Nat) (amount : Amount)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (n : Bitcoin.Numeric.ScriptNum) (D : ByteArray)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hpk : Bitcoin.Crypto.Seam.Der.isValidPubKey delayedPaymentKey.bytes = true)
    (hne : 0 < sig.size)
    (hdec : decodeNum ({} : PolicyFlags) (delayBytes csv) 5 = .ok n)
    (hnn : 0 ≤ n)
    (hdis : Int.toNat n &&& SEQUENCE_LOCKTIME_DISABLE_FLAG = 0)
    (hD : D = sighashWitnessV0 tx nIn
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      (hashtypeOf sig) amount)
    (h : Accepts (verifyImplLawsCSV tx nIn n) D
      (toLocalProg revocationKey delayedPaymentKey csv) [zeroByte, sig]) :
    verifyWitnessProgram 10
        [sig, ByteArray.empty,
          serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)]
        0
        (hashSha256
          (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)))
        ({ csv := true } : ScriptFlags) ({} : PolicyFlags)
        (checkerOf Bitcoin.Crypto.Ecdsa.Verify.verifyImpl tx nIn amount) false = .ok := by
  obtain ⟨hcsv, hsig⟩ :=
    accepts_toLocal_delayed (verifyImplLawsCSV tx nIn n) D
      revocationKey delayedPaymentKey csv sig h
  have hseq : checkSequenceDef (locktimeEnvOf tx nIn) n = true := by
    simpa using hcsv
  have hsig' : Bitcoin.Crypto.Ecdsa.Verify.verifyImpl (sigBody sig)
      delayedPaymentKey.bytes
      (sighashWitnessV0 tx nIn
        (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
        (hashtypeOf sig) amount) = true := by
    have hsigD : Bitcoin.Crypto.Ecdsa.Verify.verifyImpl (sigBody sig)
        delayedPaymentKey.bytes D = true := by
      simpa [verifyImplLawsCSV] using hsig
    rwa [← hD]
  exact (toLocal_sighash_interpreters_agree
    Bitcoin.Crypto.Ecdsa.Verify.verifyImpl tx nIn amount revocationKey
    delayedPaymentKey csv sig n hr hd hsigsz hpk hne hdec hnn hdis hseq hsig').1

/-! ## A fully concrete negative at the law level -/

/-- With both signatures empty, the funding program cannot be accepted by the
concrete law: both `sigCheck`s are the vendor's `false`, so the multisig step
pushes `false`.  This is the `verifyImpl`-instantiated form of
`SpendTargets.exec_funding_one_signature`. -/
theorem not_accepts_funding_verifyImplLaws_empty_sigs
    (D : ByteArray) (a b : PubKey) (dummy : ByteArray) :
    ¬ Accepts verifyImplLaws D (fundingProg a b)
      [ByteArray.empty, ByteArray.empty, dummy] := by
  intro h
  obtain ⟨h1, _h2⟩ :=
    accepts_funding_sigCheck verifyImplLaws D a b dummy ByteArray.empty ByteArray.empty h
  have h1f : verifyImplLaws.sigCheck a.bytes D ByteArray.empty = false :=
    verifyImplLaws_sigCheck_empty_sig a.bytes D
  rw [h1f] at h1
  exact Bool.false_ne_true h1

/-- The same at the vendor checker level: the witness-v0 ECDSA verdict for an
empty signature is `false` (the seam rejects it before the EC math), matching
`verifyImplLaws_sigCheck_empty_sig`.  Note that this is a *checker*-level
negative: the vendored agreement theorems are one-directional, so no
`verifyWitnessProgram ... ≠ .ok` statement is claimed from it. -/
theorem vendor_checker_empty_sig_false
    (tx : Tx) (nIn : Nat) (amount : Amount) (pk scriptCode : ByteArray)
    (ed : ScriptExecutionData) :
    (checkerOf Bitcoin.Crypto.Ecdsa.Verify.verifyImpl tx nIn amount).base.checkECDSASignature
      ByteArray.empty pk scriptCode .witnessV0 ed = false := by
  simp [checkerOf, Bitcoin.Crypto.Seam.Entry.ecdsaEntry,
    Bitcoin.Crypto.Seam.Entry.ecdsaVerdict]

end LnLean.Proofs.WaveH.H29
