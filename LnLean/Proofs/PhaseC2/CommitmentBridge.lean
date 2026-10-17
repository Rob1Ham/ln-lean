import LnLean

/-!
# LnLean.Proofs.PhaseC2.CommitmentBridge

**English claim.**  The two main outputs of a BOLT 3 commitment transaction
have the following spend paths.

* `to_local` is a version-0 P2WSH output whose witness script is
  `OP_IF <revocationpubkey> OP_ELSE <to_self_delay> OP_CSV OP_DROP
  <local_delayedpubkey> OP_ENDIF OP_CHECKSIG`.  A spend is accepted either
  (i) through the `OP_IF` branch with a signature that verifies under the
  revocation key and **no** CSV delay, or (ii) through the `OP_ELSE` branch
  with a signature that verifies under the holder's delayed payment key,
  provided the spending input's `nSequence` is at least `to_self_delay`.
  Under the explicit interpreter bridge below, these are both necessary and
  sufficient conditions for an accepted spend of the P2WSH output.
* `to_remote` is the no-anchor P2WPKH output of
  `LnLean.Bitcoin.Seam.toRemoteScript`; an accepted spend reveals the remote
  payment key and a signature that verifies under that key.

The module proves the exact byte shape and length of both templates, the
template-level containment facts (revocation key, delayed payment key, CSV
delay, opcodes), and the conditional spendability composition.  The L1
interpreter is **not** formalised: its semantics are the explicit
`CommitmentSpendBridge` hypothesis (and, for the wave-A `toLocalScript`,
`SeamToLocalBridge`).  No consensus-level claim is made without that
hypothesis.

**BOLT sections.**
* BOLT 3 §`to_local` Output (`refs/bolts/03-transactions.md:113-135`): the
  two-branch witness script and the BIP 141 P2WSH wrapper.
* BOLT 3 §`to_remote` Output (`refs/bolts/03-transactions.md:136-147`): the
  P2WPKH no-anchor form modelled by `Seam.toRemoteScript`.
* BOLT 3 §`Commitment Transaction` (`03-transactions.md:83-112`) and BOLT 2
  §`to_self_delay` semantics (`02-peer-protocol.md:750-752`).

**rust-lightning anchors** at pinned commit
`fe4900930c6bd5786ec4203274d7cf312776a5a6`.
* `lightning/src/ln/chan_utils.rs:687-700`
  (`get_revokeable_redeemscript`, the `to_local` IF/ELSE script).
* `lightning/src/ln/chan_utils.rs:704-713`
  (`get_countersigner_payment_script`, the P2WPKH `to_remote` form).
* `lightning/src/ln/chan_utils.rs:1713-1740`
  (`CommitmentTransaction::new`, the output set) and
  `:1887-1945` (`insert_non_htlc_outputs`).
* `lightning/src/ln/channel.rs:6270` (`build_commitment_transaction`).

**What is explicitly NOT modelled.**
* Script execution, signature verification, and ECDSA unforgeability.  The
  bridge fields are the only interpreter semantics; establishing them for
  `btc-lean`'s concrete `Script.parse` is out of scope.  The wave-A parser
  does not even decode `OP_CSV` (`Bitcoin.Data.ScriptInstr` has no such
  constructor).
* SHA-256 and RIPEMD160/HASH160 are parameters (`sha256`, `hash160` in the
  bridge).  Only the conditional collision-resistance binding of the revealed
  witness script is proved.
* Signature hash construction (BIP 143), sighash flags, and witness
  malleability.  `msg` is an abstract digest supplied by the caller.
* Non-canonical branch selectors (truthy/falsy values other than `0x01` /
  `0x00`), clean-stack policy, and extra witness elements below the
  signature.  The model permits an arbitrary witness prefix `pre` but fixes
  the selector byte.
* The anchor variant of `to_remote` (`<remotepubkey> OP_CHECKSIGVERIFY OP_1
  OP_CSV`, `ScriptTemplates.toRemoteWitnessScript`) and HTLC outputs.
* Fee/weight, output ordering, and dust trimming; those are owned by
  `Proofs.Channel.CommitmentTxProps` and `Proofs.Bitcoin.WeightProps`.

**Model gap discovered.**  `LnLean.Bitcoin.Seam.toLocalScript` is
`<csv> OP_CSV OP_DROP <revocation_pubkey> OP_CHECKSIG`: it puts the CSV delay
on the *revocation* path and has no holder branch.  BOLT 3 instead gives the
revocation branch no delay and puts the delay on the holder branch.  The two
templates therefore have different lengths (39 vs 77 bytes for compressed
keys) and are not interchangeable; `seamToLocalScript_ne_bolt3` proves the
distinction.  The spendability result for BOLT 3 is stated about
`ScriptTemplates.toLocalWitnessScript`; the wave-A Seam template is treated
separately by `SeamToLocalBridge`.
-/

namespace LnLean.Proofs.PhaseC2

set_option autoImplicit false
set_option maxHeartbeats 1000000

open LnLean
open LnLean.Bitcoin
open LnLean.Proofs.Bitcoin.ScriptProps

/-! ## Byte-shape and size lemmas for the wave-A Seam templates -/

/-- Exact byte shape of `Seam.toLocalScript`. -/
theorem toLocalScript_bytes (revocationKey : PubKey) (csv : Blocks) :
    (toLocalScript revocationKey csv).bytes =
      pushData (ByteArray.mk #[csv.toUInt8])
        ++ (ByteArray.empty.push OP_CSV).push OP_DROP
        ++ pushData revocationKey.bytes
        ++ ByteArray.empty.push OP_CHECKSIG := rfl

/-- `Seam.toLocalScript` is 39 bytes for a 33-byte compressed key:
`2` (delay push) `+ 1` (`OP_CSV`) `+ 1` (`OP_DROP`) `+ 34` (key push)
`+ 1` (`OP_CHECKSIG`). -/
theorem toLocalScript_size (revocationKey : PubKey) (csv : Blocks)
    (hk : revocationKey.bytes.size = 33) :
    (toLocalScript revocationKey csv).bytes.size = 39 := by
  rw [toLocalScript_bytes]
  simp only [pushData_size, ByteArray.size_append, ByteArray.size_push,
    ByteArray.size_empty, hk]
  omega

/-- The wave-A `to_local` script contains the revocation key. -/
theorem toLocalScript_contains_revocationKey (revocationKey : PubKey)
    (csv : Blocks) :
    ScriptContainsKey (toLocalScript revocationKey csv) revocationKey := by
  refine ⟨pushData (ByteArray.mk #[csv.toUInt8])
      ++ (ByteArray.empty.push OP_CSV).push OP_DROP,
    ByteArray.empty.push OP_CHECKSIG, ?_⟩
  rw [toLocalScript_bytes]
  simp only [ByteArray.append_assoc]

/-- The wave-A `to_local` script contains the encoded CSV delay. -/
theorem toLocalScript_contains_csv (revocationKey : PubKey) (csv : Blocks) :
    ScriptContains (toLocalScript revocationKey csv)
      (pushData (ByteArray.mk #[csv.toUInt8])) := by
  refine ⟨ByteArray.empty,
    (ByteArray.empty.push OP_CSV).push OP_DROP ++ pushData revocationKey.bytes
      ++ ByteArray.empty.push OP_CHECKSIG, ?_⟩
  rw [toLocalScript_bytes]
  simp only [ByteArray.empty_append, ByteArray.append_assoc]

/-- The wave-A `to_local` script contains the `OP_CSV` opcode. -/
theorem toLocalScript_contains_csvOpcode (revocationKey : PubKey)
    (csv : Blocks) :
    ScriptContainsOp (toLocalScript revocationKey csv) OP_CSV := by
  refine ⟨pushData (ByteArray.mk #[csv.toUInt8]), ByteArray.empty.push OP_DROP
      ++ pushData revocationKey.bytes ++ ByteArray.empty.push OP_CHECKSIG, ?_⟩
  rw [toLocalScript_bytes]
  simp only [ByteArray.append_assoc]

/-- The wave-A `to_local` script contains the final `OP_CHECKSIG` opcode. -/
theorem toLocalScript_contains_checkSig (revocationKey : PubKey)
    (csv : Blocks) :
    ScriptContainsOp (toLocalScript revocationKey csv) OP_CHECKSIG := by
  exact ⟨pushData (ByteArray.mk #[csv.toUInt8])
      ++ (ByteArray.empty.push OP_CSV).push OP_DROP ++ pushData revocationKey.bytes,
    ByteArray.empty, by
      rw [toLocalScript_bytes]
      simp only [ByteArray.append_assoc, ByteArray.append_empty]⟩

/-- Exact byte shape of `Seam.toRemoteScript`: BIP 141 P2WPKH
`OP_0 <0x14> <program>`. -/
theorem toRemoteScript_bytes (remotePaymentHash160 : ByteArray) :
    (toRemoteScript remotePaymentHash160).bytes =
      (ByteArray.empty.push OP_0).push 0x14 ++ remotePaymentHash160 := rfl

/-- The no-anchor `to_remote` output script is 22 bytes for a 20-byte
HASH160 program. -/
theorem toRemoteScript_size (remotePaymentHash160 : ByteArray)
    (h : remotePaymentHash160.size = 20) :
    (toRemoteScript remotePaymentHash160).bytes.size = 22 := by
  simpa [toRemoteScript] using p2wpkh_size remotePaymentHash160 h

/-- The `to_remote` script contains the 20-byte payment-key hash. -/
theorem toRemoteScript_contains_program (remotePaymentHash160 : ByteArray) :
    ScriptContains (toRemoteScript remotePaymentHash160) remotePaymentHash160 := by
  refine ⟨(ByteArray.empty.push OP_0).push 0x14, ByteArray.empty, ?_⟩
  rw [toRemoteScript_bytes]
  simp only [ByteArray.append_empty]

/-! ## Exact shape and size of the BOLT 3 `to_local` witness script -/

/-- Exact byte shape of the BOLT 3 `to_local` witness script:
`OP_IF <revocationpubkey> OP_ELSE <to_self_delay> OP_CSV OP_DROP
<local_delayedpubkey> OP_ENDIF OP_CHECKSIG`. -/
theorem toLocalWitnessScript_bytes (revocationKey delayedPaymentKey : PubKey)
    (toSelfDelay : Blocks) :
    (toLocalWitnessScript revocationKey delayedPaymentKey toSelfDelay).bytes =
      ByteArray.empty.push OP_IF
        ++ pushData revocationKey.bytes
        ++ ByteArray.empty.push OP_ELSE
        ++ pushScriptNum16 toSelfDelay
        ++ ByteArray.empty.push OP_CSV
        ++ ByteArray.empty.push OP_DROP
        ++ pushData delayedPaymentKey.bytes
        ++ ByteArray.empty.push OP_ENDIF
        ++ ByteArray.empty.push OP_CHECKSIG := rfl

/-- The BOLT 3 `to_local` witness script is 77 bytes for two 33-byte
compressed keys and the scaffold's two-byte delay push. -/
theorem toLocalWitnessScript_size_77 (revocationKey delayedPaymentKey : PubKey)
    (toSelfDelay : Blocks)
    (hrev : revocationKey.bytes.size = 33)
    (hdel : delayedPaymentKey.bytes.size = 33) :
    (toLocalWitnessScript revocationKey delayedPaymentKey toSelfDelay).bytes.size = 77 :=
  LnLean.Bitcoin.toLocalWitnessScript_size revocationKey delayedPaymentKey
    toSelfDelay hrev hdel

/-- The BOLT 3 `to_local` script contains the revocation key in its `OP_IF`
branch. -/
theorem toLocalWitnessScript_contains_revocationKey
    (revocationKey delayedPaymentKey : PubKey) (toSelfDelay : Blocks) :
    ScriptContainsKey
      (toLocalWitnessScript revocationKey delayedPaymentKey toSelfDelay)
      revocationKey := by
  refine ⟨ByteArray.empty.push OP_IF,
    ByteArray.empty.push OP_ELSE ++ pushScriptNum16 toSelfDelay
      ++ ByteArray.empty.push OP_CSV ++ ByteArray.empty.push OP_DROP
      ++ pushData delayedPaymentKey.bytes ++ ByteArray.empty.push OP_ENDIF
      ++ ByteArray.empty.push OP_CHECKSIG, ?_⟩
  rw [toLocalWitnessScript_bytes]
  simp only [ByteArray.append_assoc]

/-- The BOLT 3 `to_local` script contains the holder's delayed payment key in
its `OP_ELSE` branch. -/
theorem toLocalWitnessScript_contains_delayedPaymentKey
    (revocationKey delayedPaymentKey : PubKey) (toSelfDelay : Blocks) :
    ScriptContainsKey
      (toLocalWitnessScript revocationKey delayedPaymentKey toSelfDelay)
      delayedPaymentKey := by
  refine ⟨ByteArray.empty.push OP_IF ++ pushData revocationKey.bytes
      ++ ByteArray.empty.push OP_ELSE ++ pushScriptNum16 toSelfDelay
      ++ ByteArray.empty.push OP_CSV ++ ByteArray.empty.push OP_DROP,
    ByteArray.empty.push OP_ENDIF ++ ByteArray.empty.push OP_CHECKSIG, ?_⟩
  rw [toLocalWitnessScript_bytes]
  simp only [ByteArray.append_assoc]

/-- The BOLT 3 `to_local` script contains the encoded `to_self_delay`. -/
theorem toLocalWitnessScript_contains_delay
    (revocationKey delayedPaymentKey : PubKey) (toSelfDelay : Blocks) :
    ScriptContains
      (toLocalWitnessScript revocationKey delayedPaymentKey toSelfDelay)
      (pushScriptNum16 toSelfDelay) := by
  refine ⟨ByteArray.empty.push OP_IF ++ pushData revocationKey.bytes
      ++ ByteArray.empty.push OP_ELSE,
    ByteArray.empty.push OP_CSV ++ ByteArray.empty.push OP_DROP
      ++ pushData delayedPaymentKey.bytes ++ ByteArray.empty.push OP_ENDIF
      ++ ByteArray.empty.push OP_CHECKSIG, ?_⟩
  rw [toLocalWitnessScript_bytes]
  simp only [ByteArray.append_assoc]

/-- The BOLT 3 `to_local` script contains the `OP_CSV` opcode. -/
theorem toLocalWitnessScript_contains_csvOpcode
    (revocationKey delayedPaymentKey : PubKey) (toSelfDelay : Blocks) :
    ScriptContainsOp
      (toLocalWitnessScript revocationKey delayedPaymentKey toSelfDelay)
      OP_CSV := by
  refine ⟨ByteArray.empty.push OP_IF ++ pushData revocationKey.bytes
      ++ ByteArray.empty.push OP_ELSE ++ pushScriptNum16 toSelfDelay,
    ByteArray.empty.push OP_DROP ++ pushData delayedPaymentKey.bytes
      ++ ByteArray.empty.push OP_ENDIF ++ ByteArray.empty.push OP_CHECKSIG, ?_⟩
  rw [toLocalWitnessScript_bytes]
  simp only [ByteArray.append_assoc]

/-- The two wave-A and BOLT 3 `to_local` templates are distinct for
well-formed compressed keys: the wave-A script is 39 bytes, the BOLT 3
two-branch script is 77 bytes.  This is the counterexample-free model-gap
statement: the Seam template cannot encode the holder branch at all. -/
theorem seamToLocalScript_ne_bolt3 (revocationKey delayedPaymentKey : PubKey)
    (csv toSelfDelay : Blocks)
    (hrev : revocationKey.bytes.size = 33)
    (hdel : delayedPaymentKey.bytes.size = 33) :
    toLocalScript revocationKey csv ≠
      toLocalWitnessScript revocationKey delayedPaymentKey toSelfDelay := by
  intro h
  have hs := congrArg (fun s : Script => s.bytes.size) h
  rw [toLocalScript_size revocationKey csv hrev,
    toLocalWitnessScript_size_77 revocationKey delayedPaymentKey toSelfDelay
      hrev hdel] at hs
  omega

/-! ## Conditional spendability model -/

/-- A signature checker: public key, signed message digest, signature bytes. -/
abbrev SigCheck := PubKey → ByteArray → ByteArray → Bool

/-- The two branches of the BOLT 3 `to_local` witness script. -/
inductive ToLocalBranch where
  /-- The `OP_IF` revocation branch: no CSV delay. -/
  | revocation
  /-- The `OP_ELSE` delayed holder branch. -/
  | delayed
deriving Repr, DecidableEq, BEq

/-- The canonical stack selector for each branch (`0x01` for `OP_IF`,
`0x00` for `OP_ELSE`). -/
def ToLocalBranch.selector : ToLocalBranch → ByteArray
  | .revocation => ByteArray.empty.push 0x01
  | .delayed => ByteArray.empty.push 0x00

/-- The witness stack layout of a `to_local` spend: an arbitrary prefix
(extra stack elements below the signature), the signature, the branch
selector, and the revealed witness script (BIP 141 P2WSH). -/
def ToLocalWitness (ws : Script) (branch : ToLocalBranch) (sig : ByteArray)
    (pre w : WitnessStack) : Prop :=
  w = pre ++ [sig, branch.selector, ws.bytes]

/-- The modelled spend conditions of the BOLT 3 `to_local` output: either a
revocation-key signature on the (undelayed) revocation branch, or a
holder-key signature on the delayed branch with `nSequence ≥ to_self_delay`. -/
def ToLocalSpend (ws : Script) (revocationKey delayedPaymentKey : PubKey)
    (toSelfDelay : Blocks) (check : SigCheck) (msg : ByteArray)
    (seq : UInt32) (w : WitnessStack) : Prop :=
  (∃ sig pre,
      ToLocalWitness ws .revocation sig pre w ∧
        check revocationKey msg sig = true) ∨
  (∃ sig pre,
      ToLocalWitness ws .delayed sig pre w ∧
        check delayedPaymentKey msg sig = true ∧
        toSelfDelay ≤ seq.toNat)

/-- The modelled spend condition of the no-anchor P2WPKH `to_remote` output:
the witness reveals the remote payment key and a signature that verifies
under it (the HASH160 commitment is carried by the bridge). -/
def ToRemoteSpend (remotePaymentKey : PubKey) (check : SigCheck)
    (msg : ByteArray) (w : WitnessStack) : Prop :=
  ∃ sig pre,
    w = pre ++ [sig, remotePaymentKey.bytes] ∧
      check remotePaymentKey msg sig = true

/-- The P2WSH output script for the BOLT 3 `to_local` witness script. -/
def toLocalP2wsh (sha256 : ByteArray → ByteArray) (revocationKey
    delayedPaymentKey : PubKey) (toSelfDelay : Blocks) : Script :=
  p2wsh (sha256
    (toLocalWitnessScript revocationKey delayedPaymentKey toSelfDelay).bytes)

/-- **Explicit L1 interpreter bridge for commitment outputs.**  It contains
(i) the P2WSH delegation from an output script to its revealed witness script,
(ii) soundness and completeness of the `to_local` branch semantics, and
(iii) soundness and completeness of the `to_remote` P2WPKH semantics.  These
are hypotheses about the interpreter, not facts proved about Bitcoin
consensus; `remoteProgram_eq` records that the modelled P2WPKH program is the
HASH160 of the remote key. -/
structure CommitmentSpendBridge
    (accepts : Script → WitnessStack → UInt32 → Bool)
    (acceptsWitnessScript : Script → WitnessStack → UInt32 → Bool)
    (sha256 hash160 : ByteArray → ByteArray)
    (check : SigCheck)
    (revocationKey delayedPaymentKey remotePaymentKey : PubKey)
    (toSelfDelay : Blocks) (msg : ByteArray)
    (remoteProgram : ByteArray) : Prop where
  /-- A P2WSH acceptance delegates to the revealed witness script. -/
  p2wsh_sound : ∀ (ws : Script) (w : WitnessStack) (seq : UInt32),
    accepts (p2wsh (sha256 ws.bytes)) w seq = true →
      acceptsWitnessScript ws w seq = true
  /-- A witness-script acceptance is accepted by the P2WSH output. -/
  p2wsh_complete : ∀ (ws : Script) (w : WitnessStack) (seq : UInt32),
    acceptsWitnessScript ws w seq = true →
      accepts (p2wsh (sha256 ws.bytes)) w seq = true
  /-- The P2WPKH program really commits to the remote payment key. -/
  remoteProgram_eq : remoteProgram = hash160 remotePaymentKey.bytes
  /-- `to_local` branch soundness. -/
  toLocal_sound : ∀ (w : WitnessStack) (seq : UInt32),
    acceptsWitnessScript
        (toLocalWitnessScript revocationKey delayedPaymentKey toSelfDelay)
        w seq = true →
      ToLocalSpend
        (toLocalWitnessScript revocationKey delayedPaymentKey toSelfDelay)
        revocationKey delayedPaymentKey toSelfDelay check msg seq w
  /-- `to_local` branch completeness. -/
  toLocal_complete : ∀ (w : WitnessStack) (seq : UInt32),
    ToLocalSpend
        (toLocalWitnessScript revocationKey delayedPaymentKey toSelfDelay)
        revocationKey delayedPaymentKey toSelfDelay check msg seq w →
      acceptsWitnessScript
        (toLocalWitnessScript revocationKey delayedPaymentKey toSelfDelay)
        w seq = true
  /-- `to_remote` soundness. -/
  toRemote_sound : ∀ (w : WitnessStack) (seq : UInt32),
    accepts (toRemoteScript remoteProgram) w seq = true →
      ToRemoteSpend remotePaymentKey check msg w
  /-- `to_remote` completeness. -/
  toRemote_complete : ∀ (w : WitnessStack) (seq : UInt32),
    ToRemoteSpend remotePaymentKey check msg w →
      accepts (toRemoteScript remoteProgram) w seq = true

/-- **`to_local` soundness (composition).**  Any spend of the P2WSH
`to_local` output accepted by the L1 interpreter (under the bridge) is either
a valid revocation-key signature on the undelayed revocation branch, or a
valid holder-key signature on the delayed branch with
`to_self_delay ≤ nSequence`. -/
theorem toLocal_spend_requires_revocation_or_delayed
    {accepts acceptsWitnessScript : Script → WitnessStack → UInt32 → Bool}
    {sha256 hash160 : ByteArray → ByteArray} {check : SigCheck}
    {revocationKey delayedPaymentKey remotePaymentKey : PubKey}
    {toSelfDelay : Blocks} {msg remoteProgram : ByteArray}
    (hb : CommitmentSpendBridge accepts acceptsWitnessScript sha256 hash160
      check revocationKey delayedPaymentKey remotePaymentKey toSelfDelay msg
      remoteProgram)
    {w : WitnessStack} {seq : UInt32}
    (hacc : accepts
      (toLocalP2wsh sha256 revocationKey delayedPaymentKey toSelfDelay)
      w seq = true) :
    (∃ sig pre,
        ToLocalWitness
          (toLocalWitnessScript revocationKey delayedPaymentKey toSelfDelay)
          .revocation sig pre w ∧
          check revocationKey msg sig = true) ∨
    (∃ sig pre,
        ToLocalWitness
          (toLocalWitnessScript revocationKey delayedPaymentKey toSelfDelay)
          .delayed sig pre w ∧
          check delayedPaymentKey msg sig = true ∧
          toSelfDelay ≤ seq.toNat) := by
  have hacc' : accepts
      (p2wsh (sha256
        (toLocalWitnessScript revocationKey delayedPaymentKey toSelfDelay).bytes))
      w seq = true := by
    simpa [toLocalP2wsh] using hacc
  exact hb.toLocal_sound w seq
    (hb.p2wsh_sound
      (toLocalWitnessScript revocationKey delayedPaymentKey toSelfDelay)
      w seq hacc')

/-- **`to_local` spendability (composition).**  Any modelled branch witness
is accepted by the P2WSH `to_local` output. -/
theorem toLocal_witness_spendable
    {accepts acceptsWitnessScript : Script → WitnessStack → UInt32 → Bool}
    {sha256 hash160 : ByteArray → ByteArray} {check : SigCheck}
    {revocationKey delayedPaymentKey remotePaymentKey : PubKey}
    {toSelfDelay : Blocks} {msg remoteProgram : ByteArray}
    (hb : CommitmentSpendBridge accepts acceptsWitnessScript sha256 hash160
      check revocationKey delayedPaymentKey remotePaymentKey toSelfDelay msg
      remoteProgram)
    {w : WitnessStack} {seq : UInt32}
    (h : ToLocalSpend
      (toLocalWitnessScript revocationKey delayedPaymentKey toSelfDelay)
      revocationKey delayedPaymentKey toSelfDelay check msg seq w) :
    accepts (toLocalP2wsh sha256 revocationKey delayedPaymentKey toSelfDelay)
      w seq = true := by
  have hws := hb.toLocal_complete w seq h
  simpa [toLocalP2wsh] using
    hb.p2wsh_complete
      (toLocalWitnessScript revocationKey delayedPaymentKey toSelfDelay)
      w seq hws

/-- The revocation branch is spendable with a valid revocation signature and
no CSV condition. -/
theorem toLocal_revocation_witness_spendable
    {accepts acceptsWitnessScript : Script → WitnessStack → UInt32 → Bool}
    {sha256 hash160 : ByteArray → ByteArray} {check : SigCheck}
    {revocationKey delayedPaymentKey remotePaymentKey : PubKey}
    {toSelfDelay : Blocks} {msg remoteProgram : ByteArray}
    (hb : CommitmentSpendBridge accepts acceptsWitnessScript sha256 hash160
      check revocationKey delayedPaymentKey remotePaymentKey toSelfDelay msg
      remoteProgram)
    {w : WitnessStack} {seq : UInt32}
    (h : ∃ sig pre,
      ToLocalWitness
        (toLocalWitnessScript revocationKey delayedPaymentKey toSelfDelay)
        .revocation sig pre w ∧
        check revocationKey msg sig = true) :
    accepts (toLocalP2wsh sha256 revocationKey delayedPaymentKey toSelfDelay)
      w seq = true :=
  toLocal_witness_spendable hb (Or.inl h)

/-- The delayed holder branch is spendable with a valid holder signature,
provided `nSequence ≥ to_self_delay`. -/
theorem toLocal_delayed_witness_spendable
    {accepts acceptsWitnessScript : Script → WitnessStack → UInt32 → Bool}
    {sha256 hash160 : ByteArray → ByteArray} {check : SigCheck}
    {revocationKey delayedPaymentKey remotePaymentKey : PubKey}
    {toSelfDelay : Blocks} {msg remoteProgram : ByteArray}
    (hb : CommitmentSpendBridge accepts acceptsWitnessScript sha256 hash160
      check revocationKey delayedPaymentKey remotePaymentKey toSelfDelay msg
      remoteProgram)
    {w : WitnessStack} {seq : UInt32}
    (h : ∃ sig pre,
      ToLocalWitness
        (toLocalWitnessScript revocationKey delayedPaymentKey toSelfDelay)
        .delayed sig pre w ∧
        check delayedPaymentKey msg sig = true ∧
        toSelfDelay ≤ seq.toNat) :
    accepts (toLocalP2wsh sha256 revocationKey delayedPaymentKey toSelfDelay)
      w seq = true :=
  toLocal_witness_spendable hb (Or.inr h)

/-- **`to_remote` soundness.**  Any spend of the P2WPKH `to_remote` output
accepted by the L1 interpreter (under the bridge) reveals the remote payment
key and a signature that verifies under it. -/
theorem toRemote_spend_requires_remote_signature
    {accepts acceptsWitnessScript : Script → WitnessStack → UInt32 → Bool}
    {sha256 hash160 : ByteArray → ByteArray} {check : SigCheck}
    {revocationKey delayedPaymentKey remotePaymentKey : PubKey}
    {toSelfDelay : Blocks} {msg remoteProgram : ByteArray}
    (hb : CommitmentSpendBridge accepts acceptsWitnessScript sha256 hash160
      check revocationKey delayedPaymentKey remotePaymentKey toSelfDelay msg
      remoteProgram)
    {w : WitnessStack} {seq : UInt32}
    (hacc : accepts (toRemoteScript remoteProgram) w seq = true) :
    ∃ sig pre,
      w = pre ++ [sig, remotePaymentKey.bytes] ∧
        check remotePaymentKey msg sig = true :=
  hb.toRemote_sound w seq hacc

/-- **`to_remote` spendability.**  Any witness revealing the remote key and a
valid remote signature is accepted by the `to_remote` output. -/
theorem toRemote_witness_spendable
    {accepts acceptsWitnessScript : Script → WitnessStack → UInt32 → Bool}
    {sha256 hash160 : ByteArray → ByteArray} {check : SigCheck}
    {revocationKey delayedPaymentKey remotePaymentKey : PubKey}
    {toSelfDelay : Blocks} {msg remoteProgram : ByteArray}
    (hb : CommitmentSpendBridge accepts acceptsWitnessScript sha256 hash160
      check revocationKey delayedPaymentKey remotePaymentKey toSelfDelay msg
      remoteProgram)
    {w : WitnessStack} {seq : UInt32}
    (h : ToRemoteSpend remotePaymentKey check msg w) :
    accepts (toRemoteScript remoteProgram) w seq = true :=
  hb.toRemote_complete w seq h

/-- Conditional P2WSH binding: under collision resistance of the (abstract)
SHA-256, a revealed witness script whose hash equals the `to_local` P2WSH
program is exactly the BOLT 3 `to_local` witness script. -/
theorem p2wsh_program_binds_toLocalWitnessScript
    (sha256 : ByteArray → ByteArray)
    (hcr : ∀ a b : ByteArray, sha256 a = sha256 b → a = b)
    (revocationKey delayedPaymentKey : PubKey) (toSelfDelay : Blocks)
    (revealed : ByteArray)
    (h : sha256 revealed =
      sha256
        (toLocalWitnessScript revocationKey delayedPaymentKey toSelfDelay).bytes) :
    revealed =
      (toLocalWitnessScript revocationKey delayedPaymentKey toSelfDelay).bytes :=
  hcr revealed _ h

/-! ## The wave-A `Seam.toLocalScript` boundary -/

/-- Spend condition of the wave-A `Seam.toLocalScript`: one revocation-key
signature after the CSV delay (no holder branch exists in that template). -/
def SeamToLocalSpend (revocationKey : PubKey) (csv : Blocks)
    (check : SigCheck) (msg : ByteArray) (seq : UInt32)
    (w : WitnessStack) : Prop :=
  ∃ sig pre,
    w = pre ++ [sig, (toLocalScript revocationKey csv).bytes] ∧
      check revocationKey msg sig = true ∧
      csv ≤ seq.toNat

/-- Explicit interpreter bridge for the wave-A `Seam.toLocalScript`. -/
structure SeamToLocalBridge (verify : Script → WitnessStack → UInt32 → Bool)
    (check : SigCheck) (revocationKey : PubKey) (csv : Blocks)
    (msg : ByteArray) : Prop where
  sound : ∀ (w : WitnessStack) (seq : UInt32),
    verify (toLocalScript revocationKey csv) w seq = true →
      SeamToLocalSpend revocationKey csv check msg seq w
  complete : ∀ (w : WitnessStack) (seq : UInt32),
    SeamToLocalSpend revocationKey csv check msg seq w →
      verify (toLocalScript revocationKey csv) w seq = true

/-- **Wave-A `to_local` soundness.**  Under `SeamToLocalBridge`, every accepted
spend reveals a revocation signature valid after the CSV delay.  This is the
strongest statement the wave-A template supports: it has no holder branch. -/
theorem seamToLocal_spend_requires_revocation_after_delay
    {verify : Script → WitnessStack → UInt32 → Bool} {check : SigCheck}
    {revocationKey : PubKey} {csv : Blocks} {msg : ByteArray}
    (hb : SeamToLocalBridge verify check revocationKey csv msg)
    {w : WitnessStack} {seq : UInt32}
    (hacc : verify (toLocalScript revocationKey csv) w seq = true) :
    ∃ sig pre,
      w = pre ++ [sig, (toLocalScript revocationKey csv).bytes] ∧
        check revocationKey msg sig = true ∧
        csv ≤ seq.toNat :=
  hb.sound w seq hacc

/-- **Wave-A `to_local` spendability.**  Under `SeamToLocalBridge`, a
revocation signature valid after the CSV delay is accepted. -/
theorem seamToLocal_witness_spendable
    {verify : Script → WitnessStack → UInt32 → Bool} {check : SigCheck}
    {revocationKey : PubKey} {csv : Blocks} {msg : ByteArray}
    (hb : SeamToLocalBridge verify check revocationKey csv msg)
    {w : WitnessStack} {seq : UInt32}
    (h : SeamToLocalSpend revocationKey csv check msg seq w) :
    verify (toLocalScript revocationKey csv) w seq = true :=
  hb.complete w seq h

/-! ## Composition with the commitment output list and a commitment tx -/

/-- The non-zero `to_local` output is a member of the commitment output list. -/
theorem commitmentOutputs_toLocal_mem (c : LnLean.Channel.Commitment)
    (h : c.toLocalSat ≠ 0) :
    LnLean.Channel.CommitmentOutput.toLocal c.toLocalSat ∈
      c.commitmentOutputs := by
  rw [LnLean.Channel.Commitment.commitmentOutputs_eq_decomposition]
  simp [LnLean.Channel.Commitment.toLocalOutputs, h]

/-- The non-zero `to_remote` output is a member of the commitment output
list. -/
theorem commitmentOutputs_toRemote_mem (c : LnLean.Channel.Commitment)
    (h : c.toRemoteSat ≠ 0) :
    LnLean.Channel.CommitmentOutput.toRemote c.toRemoteSat ∈
      c.commitmentOutputs := by
  rw [LnLean.Channel.Commitment.commitmentOutputs_eq_decomposition]
  simp [LnLean.Channel.Commitment.toRemoteOutputs, h]

/-- A concrete two-output commitment transaction for a zero-HTLC, no-anchor
commitment.  Output 0 is `to_local`, output 1 is `to_remote`, matching the
group order of `Commitment.commitmentOutputs`. -/
def zeroHtlcCommitmentTx (holder : Direction) (number funding toLocal fee
    toSelfDelay : Nat) (txid : ByteArray)
    (toLocalSPK toRemoteSPK : Script) : Tx :=
  let c := LnLean.Channel.zeroHtlcCommitment holder number funding toLocal fee
    toSelfDelay false
  { version := 2
    vin :=
      [ { prevout := fundingOutpoint txid 0
          scriptSig := Bitcoin.Data.Script.empty
          sequence := 0xFFFFFFFF } ]
    vout :=
      [ { value := (c.toLocalSat : BtcAmount), scriptPubKey := toLocalSPK },
        { value := (c.toRemoteSat : BtcAmount), scriptPubKey := toRemoteSPK } ]
    locktime := 0
    witness := [[]] }

/-- Output 0 of `zeroHtlcCommitmentTx` is the `to_local` output with the
supplied `scriptPubKey` and the commitment's `to_local` value. -/
theorem zeroHtlcCommitmentTx_toLocal_output (holder : Direction)
    (number funding toLocal fee toSelfDelay : Nat) (txid : ByteArray)
    (toLocalSPK toRemoteSPK : Script) :
    (zeroHtlcCommitmentTx holder number funding toLocal fee toSelfDelay txid
        toLocalSPK toRemoteSPK).vout[0]? =
      some { value := (toLocal : BtcAmount), scriptPubKey := toLocalSPK } := by
  simp [zeroHtlcCommitmentTx, LnLean.Channel.zeroHtlcCommitment]

/-- Output 1 of `zeroHtlcCommitmentTx` is the `to_remote` output with the
supplied `scriptPubKey` and the commitment's residual `to_remote` value. -/
theorem zeroHtlcCommitmentTx_toRemote_output (holder : Direction)
    (number funding toLocal fee toSelfDelay : Nat) (txid : ByteArray)
    (toLocalSPK toRemoteSPK : Script) :
    (zeroHtlcCommitmentTx holder number funding toLocal fee toSelfDelay txid
        toLocalSPK toRemoteSPK).vout[1]? =
      some { value := (funding - fee - toLocal : BtcAmount)
             scriptPubKey := toRemoteSPK } := by
  simp [zeroHtlcCommitmentTx, LnLean.Channel.zeroHtlcCommitment]

/-- **End-to-end `to_local` composition.**  If the commitment transaction's
first output carries the `to_local` P2WSH script and the L1 interpreter
accepts a spend of it, then the spend is either a revocation-key spend or a
delayed holder spend with `nSequence ≥ to_self_delay`. -/
theorem zeroHtlcCommitmentTx_toLocal_spend_requires
    {accepts acceptsWitnessScript : Script → WitnessStack → UInt32 → Bool}
    {sha256 hash160 : ByteArray → ByteArray} {check : SigCheck}
    {revocationKey delayedPaymentKey remotePaymentKey : PubKey}
    {toSelfDelay : Blocks} {msg remoteProgram : ByteArray}
    (hb : CommitmentSpendBridge accepts acceptsWitnessScript sha256 hash160
      check revocationKey delayedPaymentKey remotePaymentKey toSelfDelay msg
      remoteProgram)
    {holder : Direction} {number funding toLocal fee : Nat}
    {txid : ByteArray} {toRemoteSPK : Script}
    {w : WitnessStack} {seq : UInt32}
    (hspk : toLocalP2wsh sha256 revocationKey delayedPaymentKey toSelfDelay =
      (zeroHtlcCommitmentTx holder number funding toLocal fee toSelfDelay txid
        (toLocalP2wsh sha256 revocationKey delayedPaymentKey toSelfDelay)
        toRemoteSPK).vout[0]!.scriptPubKey)
    (hacc : accepts
      (zeroHtlcCommitmentTx holder number funding toLocal fee toSelfDelay txid
        (toLocalP2wsh sha256 revocationKey delayedPaymentKey toSelfDelay)
        toRemoteSPK).vout[0]!.scriptPubKey w seq = true) :
    (∃ sig pre,
        ToLocalWitness
          (toLocalWitnessScript revocationKey delayedPaymentKey toSelfDelay)
          .revocation sig pre w ∧
          check revocationKey msg sig = true) ∨
    (∃ sig pre,
        ToLocalWitness
          (toLocalWitnessScript revocationKey delayedPaymentKey toSelfDelay)
          .delayed sig pre w ∧
          check delayedPaymentKey msg sig = true ∧
          toSelfDelay ≤ seq.toNat) := by
  apply toLocal_spend_requires_revocation_or_delayed hb
  rwa [← hspk]

/-- **End-to-end `to_remote` composition.**  If the commitment transaction's
second output carries the `to_remote` P2WPKH script and the L1 interpreter
accepts a spend of it, then the witness reveals the remote payment key and a
signature that verifies under it. -/
theorem zeroHtlcCommitmentTx_toRemote_spend_requires
    {accepts acceptsWitnessScript : Script → WitnessStack → UInt32 → Bool}
    {sha256 hash160 : ByteArray → ByteArray} {check : SigCheck}
    {revocationKey delayedPaymentKey remotePaymentKey : PubKey}
    {toSelfDelay : Blocks} {msg remoteProgram : ByteArray}
    (hb : CommitmentSpendBridge accepts acceptsWitnessScript sha256 hash160
      check revocationKey delayedPaymentKey remotePaymentKey toSelfDelay msg
      remoteProgram)
    {holder : Direction} {number funding toLocal fee : Nat}
    {txid : ByteArray} {toLocalSPK : Script}
    {w : WitnessStack} {seq : UInt32}
    (hspk : toRemoteScript remoteProgram =
      (zeroHtlcCommitmentTx holder number funding toLocal fee toSelfDelay txid
        toLocalSPK (toRemoteScript remoteProgram)).vout[1]!.scriptPubKey)
    (hacc : accepts
      (zeroHtlcCommitmentTx holder number funding toLocal fee toSelfDelay txid
        toLocalSPK (toRemoteScript remoteProgram)).vout[1]!.scriptPubKey
      w seq = true) :
    ∃ sig pre,
      w = pre ++ [sig, remotePaymentKey.bytes] ∧
        check remotePaymentKey msg sig = true :=
  toRemote_spend_requires_remote_signature hb (by rwa [← hspk] at hacc; exact hacc)

end LnLean.Proofs.PhaseC2
