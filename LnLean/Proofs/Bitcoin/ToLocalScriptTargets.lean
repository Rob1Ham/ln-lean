import LnLean.Bitcoin.Seam
import LnLean.Bitcoin.ScriptTemplates
import LnLean.Proofs.Bitcoin.ScriptProps
import LnLean.Proofs.WaveD.D42
import LnLean.Proofs.WaveD.D43

/-!
# LnLean.Proofs.Bitcoin.ToLocalScriptTargets

English claim (`LN-L1-004`).  The BOLT 3 `to_local` commitment output carries
the CSV contest delay (`to_self_delay`) and the revocation key.

## Model change

The original seam definition `LnLean.Bitcoin.toLocalScript`

`<csv> OP_CSV OP_DROP <revocation_pubkey> OP_CHECKSIG`

is a flat one-branch fragment.  It is retained unchanged for existing
consumers (`PhaseC2.CommitmentBridge`, `WaveD.D03`, ...), but it is not the
BOLT 3 witness script.  This module works with the faithful two-branch seam
model added as `LnLean.Bitcoin.toLocalScriptFull`:

`OP_IF <revocation_pubkey> OP_ELSE <to_self_delay> OP_CSV OP_DROP
 <delayed_payment_pubkey> OP_ENDIF OP_CHECKSIG`.

`toLocalScriptFull_eq_template` proves that this seam definition is exactly the
wave-A BOLT 3 template `LnLean.Bitcoin.toLocalWitnessScript` in
`LnLean/Bitcoin/ScriptTemplates.lean`; the two models cannot drift.

## What is proved

At the level of exact `Script.bytes`:

* the two branches are contiguous: the `OP_IF` branch contains the pushed
  revocation key, and the `OP_ELSE` branch contains the delay push, `OP_CSV`,
  `OP_DROP`, and the pushed delayed-payment key
  (`toLocalScriptFull_decomp`, `toLocalScriptFull_contains_*`);
* a single bundled clause theorem
  (`toLocalScriptFull_carries_csv_and_revocationKey`) states both containment
  facts plus the `OP_CSV` opcode;
* the script *commits* to both values: for 33-byte revocation keys and delays
  below `2^16`, equal full scripts imply equal revocation keys and equal
  delays (`toLocalScriptFull_commits_delay_and_revocationKey`).  The delay
  encoding is injective on `[0, 2^16)`; the revocation key is selected by the
  fixed-size `OP_IF` push, so the result does not depend on the delayed-payment
  key;
* at the on-chain output level, if `sha256` is injective, equal P2WSH programs
  `p2wsh (sha256 (toLocalScriptFull ...))` imply equal revocation keys and
  equal delays (`toLocalScriptFull_p2wsh_commits_delay_and_revocationKey`);
* under the existing `CommitmentParams.HashesMatch` bridge, the `toLocal`
  member of `commitmentOutputs` is the P2WSH of the SHA-256 of the full
  two-branch witness script, and equal output scripts commit to both values
  (`commitmentOutputs_toLocal_fullWitnessProgram`,
  `commitmentOutputs_toLocal_commits_delay_and_revocationKey`);
* the legacy flat fragment is *not* the full script for protocol-sized keys
  (`toLocalScript_ne_toLocalScriptFull`), documenting why the old target had
  to be replaced rather than reinterpreted.

## Missing bridge (not assumed, not faked)

There is no script interpreter, signature checker, or sighash model in this
tree.  The theorems above are structural byte/containment/committment
statements.  The connection from `toLocalScriptFull` to the P2WSH program
still requires the existing parameterised `sha256` bridge
(`CommitmentParams.HashesMatch`); the padding/`P2WSH` size rules and Bitcoin
consensus are consumed from `btc-lean`.  Script execution (the `OP_IF`
revocation path and `OP_CSV` delay enforcement) remains outside this module.
`toLocalScriptFull` uses the scaffold's fixed-width two-byte delay push, not
minimal `CScriptNum`; the represented value is exact for every `d < 2^16`.

## References

* BOLT 3 "`to_local` Output" (`refs/bolts/03-transactions.md:113-135` at
  `1aadb719b4007c4cea0ba6e36b08c4fb53788dee`).
* BOLT 2 `to_self_delay` as a `u16` field (`02-peer-protocol.md:697`, `:921`).
* `rust-lightning/lightning/src/ln/chan_utils.rs:687`
  (`get_revokeable_redeemscript`) at
  `fe4900930c6bd5786ec4203274d7cf312776a5a6`.
-/

namespace LnLean.Proofs.Bitcoin.ToLocalScriptTargets

set_option autoImplicit false
set_option maxHeartbeats 1000000

open LnLean LnLean.Bitcoin
open LnLean.Proofs.Bitcoin.ScriptProps

/-! ## Agreement with the wave-A BOLT 3 template -/

/-- The seam's fixed-width delay push is exactly the wave-A
`pushScriptNum16`. -/
theorem toLocalDelayPush_eq_pushScriptNum16 (csv : Blocks) :
    toLocalDelayPush csv = pushScriptNum16 csv := rfl

/-- **The faithful seam model is the BOLT 3 template.**  The full two-branch
seam script is definitionally the wave-A `toLocalWitnessScript`, so all
existing byte-level results for the template apply to it and vice versa. -/
theorem toLocalScriptFull_eq_template (revocationKey delayedPaymentKey : PubKey)
    (toSelfDelay : Blocks) :
    toLocalScriptFull revocationKey delayedPaymentKey toSelfDelay =
      toLocalWitnessScript revocationKey delayedPaymentKey toSelfDelay := by
  unfold toLocalScriptFull toLocalWitnessScript toLocalDelayPush
    pushScriptNum16 pushUInt16LE
  rfl

/-! ## Branches of the full script -/

/-- The `OP_IF` revocation branch: `OP_IF <revocationpubkey>`. -/
def toLocalRevocationBranch (revocationKey : PubKey) : ByteArray :=
  (ByteArray.empty.push OP_IF) ++ pushData revocationKey.bytes

/-- The `OP_ELSE` CSV-delayed branch:
`OP_ELSE <to_self_delay> OP_CSV OP_DROP <delayed_payment_pubkey>`. -/
def toLocalDelayedBranch (delayedPaymentKey : PubKey) (toSelfDelay : Blocks) :
    ByteArray :=
  (ByteArray.empty.push OP_ELSE) ++ toLocalDelayPush toSelfDelay ++
    (ByteArray.empty.push OP_CSV) ++ (ByteArray.empty.push OP_DROP) ++
    pushData delayedPaymentKey.bytes

/-- The shared tail: `OP_ENDIF OP_CHECKSIG`. -/
def toLocalScriptTail : ByteArray :=
  (ByteArray.empty.push OP_ENDIF) ++ (ByteArray.empty.push OP_CHECKSIG)

/-- Exact two-branch decomposition of the full `to_local` witness script.
The revocation key occurs only in the `OP_IF` branch; the delay and the
delayed-payment key occur only in the `OP_ELSE` branch. -/
theorem toLocalScriptFull_decomp (revocationKey delayedPaymentKey : PubKey)
    (toSelfDelay : Blocks) :
    (toLocalScriptFull revocationKey delayedPaymentKey toSelfDelay).bytes =
      toLocalRevocationBranch revocationKey ++
        toLocalDelayedBranch delayedPaymentKey toSelfDelay ++
        toLocalScriptTail := by
  unfold toLocalScriptFull toLocalRevocationBranch toLocalDelayedBranch
    toLocalScriptTail
  simp only [ByteArray.append_assoc]

/-! ## Containment lemmas -/

/-- The `OP_IF` branch contains the minimal push of the revocation key. -/
theorem toLocalScriptFull_contains_revocationKey
    (revocationKey delayedPaymentKey : PubKey) (toSelfDelay : Blocks) :
    ScriptContainsKey
      (toLocalScriptFull revocationKey delayedPaymentKey toSelfDelay)
      revocationKey := by
  refine ⟨ByteArray.empty.push OP_IF,
    toLocalDelayedBranch delayedPaymentKey toSelfDelay ++ toLocalScriptTail, ?_⟩
  rw [toLocalScriptFull_decomp]
  simp only [toLocalRevocationBranch, ByteArray.append_assoc]

/-- The full script contains the encoded `to_self_delay` as a contiguous byte
substring. -/
theorem toLocalScriptFull_contains_delay
    (revocationKey delayedPaymentKey : PubKey) (toSelfDelay : Blocks) :
    ScriptContains
      (toLocalScriptFull revocationKey delayedPaymentKey toSelfDelay)
      (toLocalDelayPush toSelfDelay) := by
  refine ⟨toLocalRevocationBranch revocationKey ++
      (ByteArray.empty.push OP_ELSE),
    (ByteArray.empty.push OP_CSV) ++ (ByteArray.empty.push OP_DROP) ++
      pushData delayedPaymentKey.bytes ++ toLocalScriptTail, ?_⟩
  rw [toLocalScriptFull_decomp]
  unfold toLocalRevocationBranch toLocalDelayedBranch
  simp only [ByteArray.append_assoc]

/-- The full script contains the `OP_CSV` opcode, immediately after the delay
push. -/
theorem toLocalScriptFull_contains_csvOpcode
    (revocationKey delayedPaymentKey : PubKey) (toSelfDelay : Blocks) :
    ScriptContainsOp
      (toLocalScriptFull revocationKey delayedPaymentKey toSelfDelay) OP_CSV := by
  refine ⟨toLocalRevocationBranch revocationKey ++
      (ByteArray.empty.push OP_ELSE) ++ toLocalDelayPush toSelfDelay,
    (ByteArray.empty.push OP_DROP) ++ pushData delayedPaymentKey.bytes ++
      toLocalScriptTail, ?_⟩
  rw [toLocalScriptFull_decomp]
  unfold toLocalRevocationBranch toLocalDelayedBranch
  simp only [ByteArray.append_assoc]

/-- The full script contains `OP_DROP`, completing `<delay> OP_CSV OP_DROP`. -/
theorem toLocalScriptFull_contains_dropOpcode
    (revocationKey delayedPaymentKey : PubKey) (toSelfDelay : Blocks) :
    ScriptContainsOp
      (toLocalScriptFull revocationKey delayedPaymentKey toSelfDelay) OP_DROP := by
  refine ⟨toLocalRevocationBranch revocationKey ++
      (ByteArray.empty.push OP_ELSE) ++ toLocalDelayPush toSelfDelay ++
      (ByteArray.empty.push OP_CSV),
    pushData delayedPaymentKey.bytes ++ toLocalScriptTail, ?_⟩
  rw [toLocalScriptFull_decomp]
  unfold toLocalRevocationBranch toLocalDelayedBranch
  simp only [ByteArray.append_assoc]

/-- The `OP_ELSE` branch contains the pushed delayed-payment key. -/
theorem toLocalScriptFull_contains_delayedPaymentKey
    (revocationKey delayedPaymentKey : PubKey) (toSelfDelay : Blocks) :
    ScriptContainsKey
      (toLocalScriptFull revocationKey delayedPaymentKey toSelfDelay)
      delayedPaymentKey := by
  refine ⟨toLocalRevocationBranch revocationKey ++
      (ByteArray.empty.push OP_ELSE) ++ toLocalDelayPush toSelfDelay ++
      (ByteArray.empty.push OP_CSV) ++ (ByteArray.empty.push OP_DROP),
    toLocalScriptTail, ?_⟩
  rw [toLocalScriptFull_decomp]
  unfold toLocalDelayedBranch
  simp only [ByteArray.append_assoc]

/-- The shared tail contains `OP_CHECKSIG`. -/
theorem toLocalScriptFull_contains_checksig
    (revocationKey delayedPaymentKey : PubKey) (toSelfDelay : Blocks) :
    ScriptContainsOp
      (toLocalScriptFull revocationKey delayedPaymentKey toSelfDelay) OP_CHECKSIG := by
  refine ⟨toLocalRevocationBranch revocationKey ++
      toLocalDelayedBranch delayedPaymentKey toSelfDelay ++
      (ByteArray.empty.push OP_ENDIF),
    ByteArray.empty, ?_⟩
  rw [toLocalScriptFull_decomp]
  unfold toLocalScriptTail
  simp only [ByteArray.append_assoc, ByteArray.append_empty]

/-- **Both clauses, bundled.**  The full `to_local` witness script contains
the revocation key in its `OP_IF` branch, the CSV delay in its `OP_ELSE`
branch, and the `OP_CSV` opcode that enforces the contest delay. -/
theorem toLocalScriptFull_carries_csv_and_revocationKey
    (revocationKey delayedPaymentKey : PubKey) (toSelfDelay : Blocks) :
    ScriptContainsKey
        (toLocalScriptFull revocationKey delayedPaymentKey toSelfDelay)
        revocationKey ∧
      ScriptContains
        (toLocalScriptFull revocationKey delayedPaymentKey toSelfDelay)
        (toLocalDelayPush toSelfDelay) ∧
      ScriptContainsOp
        (toLocalScriptFull revocationKey delayedPaymentKey toSelfDelay) OP_CSV :=
  ⟨toLocalScriptFull_contains_revocationKey revocationKey delayedPaymentKey
      toSelfDelay,
   toLocalScriptFull_contains_delay revocationKey delayedPaymentKey toSelfDelay,
   toLocalScriptFull_contains_csvOpcode revocationKey delayedPaymentKey
      toSelfDelay⟩

/-! ## The delay encoding is injective on `[0, 2^16)` -/

/-- The seam's delay push is the wave-A `pushScriptNum16`, which is injective
on the BOLT 2 `u16` range. -/
theorem toLocalDelayPush_injective {d₁ d₂ : Nat}
    (h₁ : d₁ < 2^16) (h₂ : d₂ < 2^16)
    (h : toLocalDelayPush d₁ = toLocalDelayPush d₂) : d₁ = d₂ := by
  rw [toLocalDelayPush_eq_pushScriptNum16] at h
  exact LnLean.Proofs.WaveD.D42.waveD_d42_pushScriptNum16_injective h₁ h₂ h

/-! ## Commitment to the delay and the revocation key -/

/-- **The full `to_local` witness script commits to both values.**  For
33-byte compressed revocation keys and BOLT-valid delays, equal full scripts
imply equal revocation keys and equal delays.  The delayed-payment key and its
length are arbitrary: the delay push has a fixed width, so the delay is
recovered before the second key push. -/
theorem toLocalScriptFull_commits_delay_and_revocationKey
    {revocationKey revocationKey' delayedPaymentKey delayedPaymentKey' : PubKey}
    {toSelfDelay toSelfDelay' : Blocks}
    (hrev : revocationKey.bytes.size = 33)
    (hrev' : revocationKey'.bytes.size = 33)
    (hdelay : toSelfDelay < 2^16)
    (hdelay' : toSelfDelay' < 2^16)
    (h : toLocalScriptFull revocationKey delayedPaymentKey toSelfDelay =
      toLocalScriptFull revocationKey' delayedPaymentKey' toSelfDelay') :
    revocationKey = revocationKey' ∧ toSelfDelay = toSelfDelay' := by
  -- First read the revocation key out of the `OP_IF` branch.
  have hw : toLocalWitnessScript revocationKey delayedPaymentKey toSelfDelay =
      toLocalWitnessScript revocationKey' delayedPaymentKey' toSelfDelay' := by
    rw [← toLocalScriptFull_eq_template, ← toLocalScriptFull_eq_template]
    exact h
  have hk : revocationKey = revocationKey' :=
    LnLean.Proofs.WaveD.D43.waveD_d43_toLocal_revocationKey_injective
      hrev hrev' hw
  refine ⟨hk, ?_⟩
  -- With the revocation keys identified, cancel the fixed `OP_IF` prefix and
  -- read the fixed-width delay push out of the `OP_ELSE` branch.
  have hb : (toLocalScriptFull revocationKey delayedPaymentKey toSelfDelay).bytes =
      (toLocalScriptFull revocationKey' delayedPaymentKey' toSelfDelay').bytes :=
    congrArg (fun s : Script => s.bytes) h
  rw [hk] at hb
  rw [toLocalScriptFull_decomp, toLocalScriptFull_decomp] at hb
  have h1 : toLocalRevocationBranch revocationKey' ++
        (toLocalDelayedBranch delayedPaymentKey toSelfDelay ++ toLocalScriptTail) =
      toLocalRevocationBranch revocationKey' ++
        (toLocalDelayedBranch delayedPaymentKey' toSelfDelay' ++ toLocalScriptTail) := by
    simpa only [ByteArray.append_assoc] using hb
  have h2 : toLocalDelayedBranch delayedPaymentKey toSelfDelay ++ toLocalScriptTail =
      toLocalDelayedBranch delayedPaymentKey' toSelfDelay' ++ toLocalScriptTail :=
    (ByteArray.append_right_inj (toLocalRevocationBranch revocationKey')).mp h1
  have h3 : toLocalDelayedBranch delayedPaymentKey toSelfDelay =
      toLocalDelayedBranch delayedPaymentKey' toSelfDelay' :=
    (ByteArray.append_left_inj toLocalScriptTail).mp h2
  unfold toLocalDelayedBranch at h3
  have h4 : toLocalDelayPush toSelfDelay ++
        ((ByteArray.empty.push OP_CSV) ++
          ((ByteArray.empty.push OP_DROP) ++ pushData delayedPaymentKey.bytes)) =
      toLocalDelayPush toSelfDelay' ++
        ((ByteArray.empty.push OP_CSV) ++
          ((ByteArray.empty.push OP_DROP) ++ pushData delayedPaymentKey'.bytes)) :=
    (ByteArray.append_right_inj (ByteArray.empty.push OP_ELSE)).mp
      (by simpa only [ByteArray.append_assoc] using h3)
  have h5 : toLocalDelayPush toSelfDelay = toLocalDelayPush toSelfDelay' :=
    (ByteArray.append_eq_append_iff_of_size_eq_left
      (by rw [toLocalDelayPush_size, toLocalDelayPush_size])).mp h4 |>.1
  exact toLocalDelayPush_injective hdelay hdelay' h5

/-- Contrapositive form: distinct revocation keys or distinct BOLT-valid
delays give distinct full witness scripts. -/
theorem toLocalScriptFull_distinct_values_distinct_script
    {revocationKey revocationKey' delayedPaymentKey delayedPaymentKey' : PubKey}
    {toSelfDelay toSelfDelay' : Blocks}
    (hrev : revocationKey.bytes.size = 33)
    (hrev' : revocationKey'.bytes.size = 33)
    (hdelay : toSelfDelay < 2^16)
    (hdelay' : toSelfDelay' < 2^16)
    (hne : revocationKey ≠ revocationKey' ∨ toSelfDelay ≠ toSelfDelay') :
    toLocalScriptFull revocationKey delayedPaymentKey toSelfDelay ≠
      toLocalScriptFull revocationKey' delayedPaymentKey' toSelfDelay' := by
  intro h
  obtain ⟨hk, hd⟩ :=
    toLocalScriptFull_commits_delay_and_revocationKey hrev hrev' hdelay hdelay' h
  rcases hne with hne | hne
  · exact hne hk
  · exact hne hd

/-! ## P2WSH output-level commitment -/

/-- `p2wsh` is injective in its witness-program argument. -/
theorem p2wsh_injective {h₁ h₂ : ByteArray} (h : p2wsh h₁ = p2wsh h₂) :
    h₁ = h₂ := by
  have hb : (p2wsh h₁).bytes = (p2wsh h₂).bytes :=
    congrArg (fun s : Script => s.bytes) h
  unfold p2wsh at hb
  exact (ByteArray.append_right_inj ((ByteArray.empty.push OP_0).push 0x20)).mp hb

/-- **The P2WSH `to_local` output commits to both values.**  If the supplied
`sha256` is injective (the C1-style hash bridge), equal `to_local` output
programs over the full witness script imply equal revocation keys and equal
delays. -/
theorem toLocalScriptFull_p2wsh_commits_delay_and_revocationKey
    (sha256 : Script → ByteArray)
    (hsha : ∀ a b : Script, sha256 a = sha256 b → a = b)
    {revocationKey revocationKey' delayedPaymentKey delayedPaymentKey' : PubKey}
    {toSelfDelay toSelfDelay' : Blocks}
    (hrev : revocationKey.bytes.size = 33)
    (hrev' : revocationKey'.bytes.size = 33)
    (hdelay : toSelfDelay < 2^16)
    (hdelay' : toSelfDelay' < 2^16)
    (h : p2wsh (sha256
          (toLocalScriptFull revocationKey delayedPaymentKey toSelfDelay)) =
        p2wsh (sha256
          (toLocalScriptFull revocationKey' delayedPaymentKey' toSelfDelay'))) :
    revocationKey = revocationKey' ∧ toSelfDelay = toSelfDelay' := by
  have hprog : sha256 (toLocalScriptFull revocationKey delayedPaymentKey toSelfDelay) =
      sha256 (toLocalScriptFull revocationKey' delayedPaymentKey' toSelfDelay') :=
    p2wsh_injective h
  exact toLocalScriptFull_commits_delay_and_revocationKey hrev hrev' hdelay hdelay'
    (hsha _ _ hprog)

/-! ## The `commitmentOutputs` bridge -/

/-- The `to_local` member of `commitmentOutputs` is the P2WSH over the stored
witness-script hash. -/
theorem commitmentOutputs_toLocal_output (p : CommitmentParams) :
    ∃ o : CommitmentOutput, o ∈ commitmentOutputs p ∧
      o.kind = OutputKind.toLocal ∧
      o.scriptPubKey = toLocalScriptPubKey p.toLocalWitnessScriptHash := by
  refine ⟨⟨OutputKind.toLocal, p.toLocalValue,
    toLocalScriptPubKey p.toLocalWitnessScriptHash⟩, ?_, rfl, rfl⟩
  simp [commitmentOutputs]

/-- **The `to_local` commitment output is P2WSH over the full two-branch
script.**  Under the model's `HashesMatch` bridge, the `to_local` output is
exactly `p2wsh (sha256 (toLocalScriptFull revocationKey delayedPaymentKey
toSelfDelay))`. -/
theorem commitmentOutputs_toLocal_fullWitnessProgram
    (p : CommitmentParams) (sha256 : Script → ByteArray)
    (hp : p.HashesMatch sha256) :
    ∃ o : CommitmentOutput, o ∈ commitmentOutputs p ∧
      o.kind = OutputKind.toLocal ∧
      o.scriptPubKey = p2wsh (sha256
        (toLocalScriptFull p.revocationKey p.delayedPaymentKey p.toSelfDelay)) := by
  obtain ⟨o, ho, hk, hs⟩ := commitmentOutputs_toLocal_output p
  refine ⟨o, ho, hk, ?_⟩
  rw [hs, toLocalScriptPubKey, hp.1, toLocalScriptFull_eq_template]

/-- **The `to_local` commitment output commits to both values.**  Under an
injective `sha256` and the `HashesMatch` bridge, equal `to_local` output
scripts imply equal revocation keys and equal BOLT-valid delays. -/
theorem commitmentOutputs_toLocal_commits_delay_and_revocationKey
    (sha256 : Script → ByteArray)
    (hsha : ∀ a b : Script, sha256 a = sha256 b → a = b)
    (p q : CommitmentParams)
    (hp : p.HashesMatch sha256) (hq : q.HashesMatch sha256)
    (hpk : p.revocationKey.bytes.size = 33)
    (hqk : q.revocationKey.bytes.size = 33)
    (hpd : p.toSelfDelay < 2^16)
    (hqd : q.toSelfDelay < 2^16)
    (h : toLocalScriptPubKey p.toLocalWitnessScriptHash =
      toLocalScriptPubKey q.toLocalWitnessScriptHash) :
    p.revocationKey = q.revocationKey ∧ p.toSelfDelay = q.toSelfDelay := by
  have hhash : p.toLocalWitnessScriptHash = q.toLocalWitnessScriptHash := by
    unfold toLocalScriptPubKey at h
    exact p2wsh_injective h
  have hsh : sha256
        (toLocalWitnessScript p.revocationKey p.delayedPaymentKey p.toSelfDelay) =
      sha256
        (toLocalWitnessScript q.revocationKey q.delayedPaymentKey q.toSelfDelay) := by
    rw [← hp.1, ← hq.1]
    exact hhash
  have hw : toLocalWitnessScript p.revocationKey p.delayedPaymentKey p.toSelfDelay =
      toLocalWitnessScript q.revocationKey q.delayedPaymentKey q.toSelfDelay :=
    hsha _ _ hsh
  have hfull : toLocalScriptFull p.revocationKey p.delayedPaymentKey p.toSelfDelay =
      toLocalScriptFull q.revocationKey q.delayedPaymentKey q.toSelfDelay := by
    rw [toLocalScriptFull_eq_template, toLocalScriptFull_eq_template]
    exact hw
  exact toLocalScriptFull_commits_delay_and_revocationKey hpk hqk hpd hqd hfull

/-! ## The legacy flat fragment is not the full script -/

/-- A one-byte `ByteArray` literal has size one. -/
theorem oneByte_size (x : UInt8) : (ByteArray.mk #[x]).size = 1 := rfl

/-- Exact size of the retained flat seam fragment:
`6 + revocationKey.bytes.size`. -/
theorem toLocalScript_size (revocationKey : PubKey) (csv : Blocks) :
    (toLocalScript revocationKey csv).bytes.size = 6 + revocationKey.bytes.size := by
  simp [toLocalScript, pushData, ByteArray.size_append, oneByte_size]
  omega

/-- **Fidelity gap of the old target.**  For 33-byte compressed keys the flat
seam fragment is 39 bytes while the full BOLT 3 script is 77 bytes, so the two
definitions are not equal.  This is why `LN-L1-004` is retargeted to the full
model rather than reinterpreting `toLocalScript`. -/
theorem toLocalScript_ne_toLocalScriptFull
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (hrev : revocationKey.bytes.size = 33)
    (hdel : delayedPaymentKey.bytes.size = 33) :
    toLocalScript revocationKey csv ≠
      toLocalScriptFull revocationKey delayedPaymentKey csv := by
  intro h
  have hs := congrArg (fun s : Script => s.bytes.size) h
  rw [toLocalScript_size, toLocalScriptFull_size revocationKey delayedPaymentKey
    csv hrev hdel, hrev] at hs
  omega

end LnLean.Proofs.Bitcoin.ToLocalScriptTargets
