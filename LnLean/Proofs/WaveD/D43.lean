import LnLean.Bitcoin.ScriptTemplates
import LnLean.Channel.Commitment
import LnLean.Channel.Revocation
import LnLean.Channel.Types

/-!
# LnLean.Proofs.WaveD.D43 — `to_local` revocation-key decomposition

English claim (`LN-L1-004`).  The BOLT 3 `to_local` commitment output is a P2WSH
over the witness script

`OP_IF <revocationpubkey> OP_ELSE <to_self_delay> OP_CSV OP_DROP
<local_delayedpubkey> OP_ENDIF OP_CHECKSIG`.

This module proves, at the byte level of `LnLean.Bitcoin.toLocalWitnessScript`:

* the exact two-branch decomposition: the `OP_IF` branch is the pushed
  revocation key, and the `OP_ELSE` branch is the CSV delay followed by the
  pushed delayed-payment key;
* the witness script determines its revocation key: two `to_local` witness
  scripts over valid (33-byte) keys are equal only if their revocation keys are
  equal, with no hypothesis on the delayed-payment key or on the delay;
* the delayed-payment key occupies the other branch: it is not the key pushed
  after `OP_IF`, and interchanging the two key roles changes the script;
* consequently the P2WSH `to_local` output commits to the revocation key: under
  a collision-free `sha256` and the model's `CommitmentParams.HashesMatch`
  bridge, equal `toLocalScriptPubKey` programs imply equal revocation keys.

The revocation-key *derivation* itself is abstract in
`LnLean.Channel.Revocation`; the final theorem composes the script-level result
with that model's `RevocationScheme`/`Shachain` interfaces and names the two
missing derivation invariants it still needs.

No `sorry`, no axiom, no `native_decide`.
-/

namespace LnLean.Proofs.WaveD.D43

set_option autoImplicit false
set_option maxHeartbeats 1000000

open LnLean LnLean.Bitcoin

-- OBLIGATION: LN-WD-D43

/-! ## Byte-level helpers -/

/-- A `pushData` prefix is one byte longer than its payload. -/
theorem waveD_d43_pushData_size (b : ByteArray) : (pushData b).size = b.size + 1 := by
  simp [pushData, ByteArray.size_append]
  omega

/-- `pushData` is injective: the one-byte length prefix has the same size on
both sides, so the payloads can be cancelled. -/
theorem waveD_d43_pushData_injective {a b : ByteArray} (h : pushData a = pushData b) :
    a = b := by
  unfold pushData at h
  have hs : (ByteArray.empty.push a.size.toUInt8).size =
      (ByteArray.empty.push b.size.toUInt8).size := by simp
  exact (ByteArray.append_eq_append_iff_of_size_eq_left hs).mp h |>.2

/-! ## The two `to_local` branches -/

/-- The `OP_IF` branch: `OP_IF <revocationpubkey>`. -/
def waveD_d43_revocationBranch (revocationKey : PubKey) : ByteArray :=
  (ByteArray.empty.push OP_IF) ++ pushData revocationKey.bytes

/-- The fixed prefix of the `OP_ELSE` branch:
`OP_ELSE <to_self_delay> OP_CSV OP_DROP`. -/
def waveD_d43_delayedPrefix (toSelfDelay : Blocks) : ByteArray :=
  (ByteArray.empty.push OP_ELSE) ++ pushScriptNum16 toSelfDelay ++
    (ByteArray.empty.push OP_CSV) ++ (ByteArray.empty.push OP_DROP)

/-- The `OP_ELSE` branch: the CSV delay followed by the delayed-payment key. -/
def waveD_d43_delayedBranch (delayedPaymentKey : PubKey) (toSelfDelay : Blocks) :
    ByteArray :=
  waveD_d43_delayedPrefix toSelfDelay ++ pushData delayedPaymentKey.bytes

/-- The closing `OP_ENDIF OP_CHECKSIG` shared by both branches. -/
def waveD_d43_scriptTail : ByteArray :=
  (ByteArray.empty.push OP_ENDIF) ++ (ByteArray.empty.push OP_CHECKSIG)

/-- Exact branch decomposition of the BOLT 3 `to_local` witness script.  The
revocation key sits in the `OP_IF` branch; the delayed-payment key sits in the
`OP_ELSE` branch after the CSV delay. -/
theorem waveD_d43_toLocal_branch_decomposition
    (revocationKey delayedPaymentKey : PubKey) (toSelfDelay : Blocks) :
    (toLocalWitnessScript revocationKey delayedPaymentKey toSelfDelay).bytes =
      waveD_d43_revocationBranch revocationKey ++
        waveD_d43_delayedBranch delayedPaymentKey toSelfDelay ++
        waveD_d43_scriptTail := by
  simp [toLocalWitnessScript, waveD_d43_revocationBranch, waveD_d43_delayedBranch,
    waveD_d43_delayedPrefix, waveD_d43_scriptTail, ByteArray.append_assoc]

/-! ## The `to_local` witness script commits to the revocation key -/

/-- **Revocation-key injectivity.**  Two `to_local` witness scripts built from
valid 33-byte revocation keys are equal only if the revocation keys are equal.
This holds for *any* delayed-payment keys and *any* delays, so the revocation
key is the component selected by the `OP_IF` branch, not by the rest of the
script. -/
theorem waveD_d43_toLocal_revocationKey_injective
    {revocationKey revocationKey' delayedPaymentKey delayedPaymentKey' : PubKey}
    {toSelfDelay toSelfDelay' : Blocks}
    (hrev : revocationKey.bytes.size = 33)
    (hrev' : revocationKey'.bytes.size = 33)
    (h : toLocalWitnessScript revocationKey delayedPaymentKey toSelfDelay =
      toLocalWitnessScript revocationKey' delayedPaymentKey' toSelfDelay') :
    revocationKey = revocationKey' := by
  have hb : (toLocalWitnessScript revocationKey delayedPaymentKey toSelfDelay).bytes =
      (toLocalWitnessScript revocationKey' delayedPaymentKey' toSelfDelay').bytes :=
    congrArg (fun s : Script => s.bytes) h
  rw [waveD_d43_toLocal_branch_decomposition,
    waveD_d43_toLocal_branch_decomposition] at hb
  -- Cancel `OP_IF`, leaving the two revocation-key pushes at the head.
  have h1 : pushData revocationKey.bytes ++
        (waveD_d43_delayedBranch delayedPaymentKey toSelfDelay ++
          waveD_d43_scriptTail) =
      pushData revocationKey'.bytes ++
        (waveD_d43_delayedBranch delayedPaymentKey' toSelfDelay' ++
          waveD_d43_scriptTail) := by
    have hb' : (ByteArray.empty.push OP_IF) ++
          (pushData revocationKey.bytes ++
            (waveD_d43_delayedBranch delayedPaymentKey toSelfDelay ++
              waveD_d43_scriptTail)) =
        (ByteArray.empty.push OP_IF) ++
          (pushData revocationKey'.bytes ++
            (waveD_d43_delayedBranch delayedPaymentKey' toSelfDelay' ++
              waveD_d43_scriptTail)) := by
      simpa only [waveD_d43_revocationBranch, ByteArray.append_assoc] using hb
    exact (ByteArray.append_right_inj (ByteArray.empty.push OP_IF)).mp hb'
  have hs : (pushData revocationKey.bytes).size =
      (pushData revocationKey'.bytes).size := by
    simp [waveD_d43_pushData_size, hrev, hrev']
  have hp : pushData revocationKey.bytes = pushData revocationKey'.bytes :=
    (ByteArray.append_eq_append_iff_of_size_eq_left hs).mp h1 |>.1
  have hbytes : revocationKey.bytes = revocationKey'.bytes :=
    waveD_d43_pushData_injective hp
  cases revocationKey
  cases revocationKey'
  simpa using hbytes

/-- **Delayed-payment-key injectivity.**  With the revocation key and the CSV
delay held fixed, equal `to_local` witness scripts imply equal
delayed-payment keys.  This isolates the *other* branch: both keys are bound,
but in different branches and hence in different roles. -/
theorem waveD_d43_toLocal_delayedPaymentKey_injective
    (revocationKey : PubKey) {delayedPaymentKey delayedPaymentKey' : PubKey}
    {toSelfDelay : Blocks}
    (h : toLocalWitnessScript revocationKey delayedPaymentKey toSelfDelay =
      toLocalWitnessScript revocationKey delayedPaymentKey' toSelfDelay) :
    delayedPaymentKey = delayedPaymentKey' := by
  have hb : (toLocalWitnessScript revocationKey delayedPaymentKey toSelfDelay).bytes =
      (toLocalWitnessScript revocationKey delayedPaymentKey' toSelfDelay).bytes :=
    congrArg (fun s : Script => s.bytes) h
  rw [waveD_d43_toLocal_branch_decomposition,
    waveD_d43_toLocal_branch_decomposition] at hb
  have h1 : waveD_d43_delayedBranch delayedPaymentKey toSelfDelay ++
        waveD_d43_scriptTail =
      waveD_d43_delayedBranch delayedPaymentKey' toSelfDelay ++
        waveD_d43_scriptTail := by
    have hb' : waveD_d43_revocationBranch revocationKey ++
          (waveD_d43_delayedBranch delayedPaymentKey toSelfDelay ++
            waveD_d43_scriptTail) =
        waveD_d43_revocationBranch revocationKey ++
          (waveD_d43_delayedBranch delayedPaymentKey' toSelfDelay ++
            waveD_d43_scriptTail) := by
      simpa only [ByteArray.append_assoc] using hb
    exact (ByteArray.append_right_inj (waveD_d43_revocationBranch revocationKey)).mp hb'
  have h2 : waveD_d43_delayedBranch delayedPaymentKey toSelfDelay =
      waveD_d43_delayedBranch delayedPaymentKey' toSelfDelay :=
    (ByteArray.append_left_inj waveD_d43_scriptTail).mp h1
  unfold waveD_d43_delayedBranch at h2
  have h3 : pushData delayedPaymentKey.bytes = pushData delayedPaymentKey'.bytes :=
    (ByteArray.append_right_inj (waveD_d43_delayedPrefix toSelfDelay)).mp h2
  have hbytes : delayedPaymentKey.bytes = delayedPaymentKey'.bytes :=
    waveD_d43_pushData_injective h3
  cases delayedPaymentKey
  cases delayedPaymentKey'
  simpa using hbytes

/-! ## Role separation: the revocation key is not the delayed-payment key -/

/-- If the two keys differ, the delayed-payment key is *not* the key pushed in
the `OP_IF` branch.  The revocation branch is therefore selected by the
revocation key alone. -/
theorem waveD_d43_toLocal_revocationKey_not_delayedBranch
    (revocationKey delayedPaymentKey : PubKey) (toSelfDelay : Blocks)
    (hne : revocationKey ≠ delayedPaymentKey)
    (hrev : revocationKey.bytes.size = 33)
    (hdel : delayedPaymentKey.bytes.size = 33) :
    ¬ ∃ rest : ByteArray,
      (toLocalWitnessScript revocationKey delayedPaymentKey toSelfDelay).bytes =
        waveD_d43_revocationBranch delayedPaymentKey ++ rest := by
  rintro ⟨rest, hrest⟩
  rw [waveD_d43_toLocal_branch_decomposition] at hrest
  have hb' : (ByteArray.empty.push OP_IF) ++
        (pushData revocationKey.bytes ++
          (waveD_d43_delayedBranch delayedPaymentKey toSelfDelay ++
            waveD_d43_scriptTail)) =
      (ByteArray.empty.push OP_IF) ++ (pushData delayedPaymentKey.bytes ++ rest) := by
    simpa only [waveD_d43_revocationBranch, ByteArray.append_assoc] using hrest
  have h1 : pushData revocationKey.bytes ++
        (waveD_d43_delayedBranch delayedPaymentKey toSelfDelay ++
          waveD_d43_scriptTail) =
      pushData delayedPaymentKey.bytes ++ rest :=
    (ByteArray.append_right_inj (ByteArray.empty.push OP_IF)).mp hb'
  have hs : (pushData revocationKey.bytes).size =
      (pushData delayedPaymentKey.bytes).size := by
    simp [waveD_d43_pushData_size, hrev, hdel]
  have hp : pushData revocationKey.bytes = pushData delayedPaymentKey.bytes :=
    (ByteArray.append_eq_append_iff_of_size_eq_left hs).mp h1 |>.1
  have hbytes : revocationKey.bytes = delayedPaymentKey.bytes :=
    waveD_d43_pushData_injective hp
  apply hne
  cases revocationKey
  cases delayedPaymentKey
  simpa using hbytes

/-- Interchanging the revocation and delayed-payment key roles changes the
witness script whenever the keys differ.  Hence the two paths are not
interchangeable: the script commits to which key is revocable. -/
theorem waveD_d43_toLocal_role_swap_changes
    (revocationKey delayedPaymentKey : PubKey) (toSelfDelay : Blocks)
    (hne : revocationKey ≠ delayedPaymentKey)
    (hrev : revocationKey.bytes.size = 33)
    (hdel : delayedPaymentKey.bytes.size = 33) :
    toLocalWitnessScript revocationKey delayedPaymentKey toSelfDelay ≠
      toLocalWitnessScript delayedPaymentKey revocationKey toSelfDelay := by
  intro h
  exact hne (waveD_d43_toLocal_revocationKey_injective hrev hdel h)

/-! ## P2WSH commitment and the `CommitmentParams` bridge -/

/-- The P2WSH program is injective in its 32-byte witness-script hash: the
`OP_0 0x20` prefix is fixed. -/
theorem waveD_d43_p2wsh_injective {h h' : ByteArray}
    (heq : p2wsh h = p2wsh h') : h = h' := by
  have hb : (p2wsh h).bytes = (p2wsh h').bytes := congrArg (fun s : Script => s.bytes) heq
  unfold p2wsh at hb
  exact (ByteArray.append_right_inj ((ByteArray.empty.push OP_0).push 0x20)).mp hb

/-- **The `to_local` output commits to the revocation key.**  Composing the
witness-script injectivity with (i) P2WSH injectivity, (ii) a collision-free
`sha256`, and (iii) the model's `HashesMatch` bridge: equal `to_local` output
scripts imply equal revocation keys.  No condition is placed on the
delayed-payment keys or the delays. -/
theorem waveD_d43_toLocalScriptPubKey_commits_revocationKey
    (sha256 : Script → ByteArray)
    (hsha : ∀ a b : Script, sha256 a = sha256 b → a = b)
    (p q : CommitmentParams)
    (hp : p.HashesMatch sha256) (hq : q.HashesMatch sha256)
    (hpk : p.revocationKey.bytes.size = 33)
    (hqk : q.revocationKey.bytes.size = 33)
    (h : toLocalScriptPubKey p.toLocalWitnessScriptHash =
      toLocalScriptPubKey q.toLocalWitnessScriptHash) :
    p.revocationKey = q.revocationKey := by
  have hhash : p.toLocalWitnessScriptHash = q.toLocalWitnessScriptHash :=
    waveD_d43_p2wsh_injective h
  have hw : toLocalWitnessScript p.revocationKey p.delayedPaymentKey p.toSelfDelay =
      toLocalWitnessScript q.revocationKey q.delayedPaymentKey q.toSelfDelay := by
    apply hsha
    rw [← hp.1, ← hq.1]
    exact hhash
  exact waveD_d43_toLocal_revocationKey_injective hpk hqk hw

/-- Contrapositive form: distinct revocation keys give distinct `to_local`
output scripts under the same hash assumptions. -/
theorem waveD_d43_toLocal_distinct_revocationKeys_distinct_script
    (sha256 : Script → ByteArray)
    (hsha : ∀ a b : Script, sha256 a = sha256 b → a = b)
    (p q : CommitmentParams)
    (hp : p.HashesMatch sha256) (hq : q.HashesMatch sha256)
    (hpk : p.revocationKey.bytes.size = 33)
    (hqk : q.revocationKey.bytes.size = 33)
    (hne : p.revocationKey ≠ q.revocationKey) :
    toLocalScriptPubKey p.toLocalWitnessScriptHash ≠
      toLocalScriptPubKey q.toLocalWitnessScriptHash := by
  intro h
  exact hne
    (waveD_d43_toLocalScriptPubKey_commits_revocationKey sha256 hsha p q hp hq hpk hqk h)

/-- The `to_local` member of `commitmentOutputs` is exactly the P2WSH output
over `toLocalWitnessScriptHash`, so the previous theorems apply to the
commitment output list itself. -/
theorem waveD_d43_commitmentOutputs_toLocal_output (p : CommitmentParams) :
    ∃ o : CommitmentOutput, o ∈ commitmentOutputs p ∧ o.kind = OutputKind.toLocal ∧
      o.scriptPubKey = toLocalScriptPubKey p.toLocalWitnessScriptHash := by
  refine ⟨⟨OutputKind.toLocal, p.toLocalValue,
    toLocalScriptPubKey p.toLocalWitnessScriptHash⟩, ?_, rfl, rfl⟩
  simp [commitmentOutputs]

/-! ## Composing with the abstract revocation derivation

`LnLean.Channel.Revocation` deliberately keeps `RevocationScheme` opaque.  The
next theorem states the strongest consequence that does not fake a missing
field: equal `to_local` scripts force equal derived revocation keys; recovering
the *commitment number* additionally needs (a) validity of derived revocation
keys (33-byte compressed points) and (b) injectivity of `pointOf` on
per-commitment secrets, neither of which the model assumes. -/

/-- Equal `to_local` scripts determine the derived revocation key. -/
theorem waveD_d43_toLocal_commits_derived_revocationKey
    (scheme : LnLean.Channel.RevocationScheme) (base : PubKey)
    (s t : LnLean.Channel.PerCommitmentSecret)
    (delayedPaymentKey delayedPaymentKey' : PubKey)
    (toSelfDelay toSelfDelay' : Blocks)
    (hs : (LnLean.Channel.revocationPubkeyOfSecret scheme base s).key.bytes.size = 33)
    (ht : (LnLean.Channel.revocationPubkeyOfSecret scheme base t).key.bytes.size = 33)
    (h : toLocalWitnessScript
          (LnLean.Channel.revocationPubkeyOfSecret scheme base s).key
          delayedPaymentKey toSelfDelay =
        toLocalWitnessScript
          (LnLean.Channel.revocationPubkeyOfSecret scheme base t).key
          delayedPaymentKey' toSelfDelay') :
    (LnLean.Channel.revocationPubkeyOfSecret scheme base s).key =
      (LnLean.Channel.revocationPubkeyOfSecret scheme base t).key :=
  waveD_d43_toLocal_revocationKey_injective hs ht h

/-- **Conditional commitment-number binding.**  If derived revocation keys are
valid compressed points and `pointOf` is injective on per-commitment secrets,
then equal `to_local` scripts force equal commitment numbers (through shachain
injectivity).  The two extra hypotheses are exactly the missing fields of
`RevocationScheme`. -/
theorem waveD_d43_toLocal_commits_commitmentNumber
    (scheme : LnLean.Channel.RevocationScheme) (base : PubKey)
    (sh : LnLean.Channel.Shachain)
    {i j : Nat} (hi : i ≤ LnLean.Channel.MAX_COMMITMENT_NUMBER)
    (hj : j ≤ LnLean.Channel.MAX_COMMITMENT_NUMBER)
    (delayedPaymentKey : PubKey) (toSelfDelay : Blocks)
    (hkey : ∀ k, (LnLean.Channel.revocationPubkeyOfSecret scheme base
      (LnLean.Channel.revocationSecret sh k)).key.bytes.size = 33)
    (hpoint : ∀ {a b : LnLean.Channel.PerCommitmentSecret},
      scheme.pointOf a = scheme.pointOf b → a = b)
    (h : toLocalWitnessScript
          (LnLean.Channel.revocationPubkeyOfSecret scheme base
            (LnLean.Channel.revocationSecret sh i)).key
          delayedPaymentKey toSelfDelay =
        toLocalWitnessScript
          (LnLean.Channel.revocationPubkeyOfSecret scheme base
            (LnLean.Channel.revocationSecret sh j)).key
          delayedPaymentKey toSelfDelay) :
    i = j := by
  have hkkey : (LnLean.Channel.revocationPubkeyOfSecret scheme base
        (LnLean.Channel.revocationSecret sh i)).key =
      (LnLean.Channel.revocationPubkeyOfSecret scheme base
        (LnLean.Channel.revocationSecret sh j)).key :=
    waveD_d43_toLocal_revocationKey_injective (hkey i) (hkey j) h
  have hk : LnLean.Channel.revocationPubkeyOfSecret scheme base
        (LnLean.Channel.revocationSecret sh i) =
      LnLean.Channel.revocationPubkeyOfSecret scheme base
        (LnLean.Channel.revocationSecret sh j) := by
    cases hki : LnLean.Channel.revocationPubkeyOfSecret scheme base
        (LnLean.Channel.revocationSecret sh i) with
    | mk ki =>
      cases hkj : LnLean.Channel.revocationPubkeyOfSecret scheme base
          (LnLean.Channel.revocationSecret sh j) with
      | mk kj =>
        have hkk : ki = kj := by simpa [hki, hkj] using hkkey
        rw [hkk]
  have hp : scheme.pointOf (LnLean.Channel.revocationSecret sh i) =
      scheme.pointOf (LnLean.Channel.revocationSecret sh j) :=
    LnLean.Channel.deriveRevocationPubkey_injective scheme base hk
  have hsec : LnLean.Channel.revocationSecret sh i =
      LnLean.Channel.revocationSecret sh j := hpoint hp
  exact LnLean.Channel.revocationSecret_injective sh hi hj hsec

end LnLean.Proofs.WaveD.D43
