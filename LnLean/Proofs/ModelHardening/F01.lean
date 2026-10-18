import LnLean.Bitcoin.Funding
import LnLean.Bitcoin.ScriptTemplates
import LnLean.Proofs.Bitcoin.FundingProps
import LnLean.Crypto.Model

/-!
# F01 — Funding hash bridge

**English claim.**  A P2WSH funding output is supposed to commit to the BOLT 3
2-of-2 witness script `OP_2 <funding_pubkey1> <funding_pubkey2> OP_2
OP_CHECKMULTISIG` through `witnessScriptHash = SHA256(witnessScript.bytes)`.
The wave-A `FundingParams` record stores `witnessScriptHash` as a free,
unconstrained 32-byte field; `FundingParams.WellFormed` only checks its
*length*, not its *value*.  This module names the missing invariant
`FundingHashLinked`, proves the P2WSH binding conditional on it (plus an
idealized collision-resistance hypothesis on 71-byte funding scripts), and
mechanizes a counterexample showing that `WellFormed` does not imply the
invariant: two well-formed parameter records with the *same* funding keys and
therefore the *same* witness script can carry two different 32-byte hashes, so
no single `sha256` can be linked to both.

**Anchors.**  BOLT 3, "Funding Transaction Output"
(`refs/bolts/03-transactions.md:75-83` at BOLT commit
`1aadb719b4007c4cea0ba6e36b08c4fb53788dee`); BIP 141 (P2WSH);
`refs/rust-lightning/lightning/src/ln/chan_utils.rs:849-866`
(`make_funding_redeemscript`).

**Not modelled.**  A concrete SHA-256 implementation.  The hash and its
collision resistance stay explicit hypotheses.  L1 consensus, chain
confirmation, and script execution are out of scope, as in
`LnLean.Bitcoin.Funding`.
-/

namespace LnLean.Proofs.ModelHardening.F01

set_option autoImplicit false

open LnLean
open LnLean.Bitcoin

-- OBLIGATION: LN-WF-F01

/-! ## The missing hash-link invariant -/

/-- **The missing model field.**  The P2WSH program stored in a
`FundingParams` is the SHA-256 of the BOLT 3 funding witness script.  The
wave-A record does not require this equation; it must be supplied as a
hypothesis by every theorem that wants a real P2WSH commitment. -/
def FundingHashLinked (sha256 : ByteArray → ByteArray)
    (p : FundingParams) : Prop :=
  p.witnessScriptHash = sha256 p.witnessScript.bytes

/-- Idealised collision resistance restricted to the 71-byte BOLT 3 funding
witness scripts.  This is the precise assumption the P2WSH binding needs; it
is consistent with a real 32-byte hash, unlike full injectivity on arbitrary
byte strings. -/
def FundingScriptCollisionResistant (sha256 : ByteArray → ByteArray) : Prop :=
  ∀ a b : ByteArray, a.size = 71 → b.size = 71 →
    sha256 a = sha256 b → a = b

/-! ## Consequences of the link for the stored hash and funding script -/

/-- Under the link and the structural SHA-256 length law, the stored hash is
32 bytes.  This recovers the hash-length conjunct of `FundingParams.WellFormed`
from the link instead of assuming it. -/
theorem waveF_f01_witnessScriptHash_size_of_hashLinked
    (sha256 : ByteArray → ByteArray)
    (hsize : ∀ b : ByteArray, (sha256 b).size = 32)
    (p : FundingParams) (h : FundingHashLinked sha256 p) :
    p.witnessScriptHash.size = 32 := by
  rw [h]
  exact hsize _

/-- The funding `scriptPubKey` is exactly the P2WSH wrapper over
`SHA256(witnessScript.bytes)`, once the hash link is supplied. -/
theorem waveF_f01_hashLinked_program (sha256 : ByteArray → ByteArray)
    (p : FundingParams) (h : FundingHashLinked sha256 p) :
    p.fundingScriptPubKey =
      LnLean.Bitcoin.p2wsh (sha256 p.witnessScript.bytes) := by
  simpa [FundingParams.fundingScriptPubKey, LnLean.Bitcoin.fundingScriptPubKey]
    using congrArg LnLean.Bitcoin.p2wsh h

/-- Byte-level form of `waveF_f01_hashLinked_program`: the funding output
script is `OP_0 <0x20> SHA256(witnessScript.bytes)` (BIP 141). -/
theorem waveF_f01_hashLinked_scriptPubKey_bytes
    (sha256 : ByteArray → ByteArray) (p : FundingParams)
    (h : FundingHashLinked sha256 p) :
    p.fundingScriptPubKey.bytes =
      (ByteArray.empty.push OP_0).push 0x20 ++
        sha256 p.witnessScript.bytes := by
  rw [waveF_f01_hashLinked_program sha256 p h]
  rfl

/-! ## P2WSH funding-output binding -/

/-- `p2wsh` is injective on witness programs: the `OP_0 <0x20>` prefix is
fixed, so equal P2WSH scripts have equal programs. -/
theorem waveF_f01_p2wsh_injective {a b : ByteArray}
    (h : LnLean.Bitcoin.p2wsh a = LnLean.Bitcoin.p2wsh b) : a = b := by
  have hb : (ByteArray.empty.push OP_0).push 0x20 ++ a =
      (ByteArray.empty.push OP_0).push 0x20 ++ b := by
    simpa [LnLean.Bitcoin.p2wsh]
      using congrArg (fun s : Script => s.bytes) h
  exact (ByteArray.append_right_inj ((ByteArray.empty.push OP_0).push 0x20)).mp hb

/-- **P2WSH funding-output binding (hash level).**  If the funding output
commits to `witnessScriptHash`, the link holds, and SHA-256 is collision
resistant on 71-byte funding scripts, then any revealed witness script whose
hash matches the committed program is *exactly* the BOLT 3 2-of-2 funding
witness script.  The `revealed.size = 71` hypothesis is what a P2WSH spend of
this output reveals (a well-formed funding script has that size). -/
theorem waveF_f01_p2wsh_binds_witnessScript
    (sha256 : ByteArray → ByteArray)
    (hcr : FundingScriptCollisionResistant sha256)
    (p : FundingParams) (hwf : p.WellFormed)
    (hlink : FundingHashLinked sha256 p)
    (revealed : ByteArray)
    (hrevSize : revealed.size = 71)
    (hrev : p.witnessScriptHash = sha256 revealed) :
    revealed = p.witnessScript.bytes := by
  apply hcr revealed p.witnessScript.bytes hrevSize
    (LnLean.Proofs.Bitcoin.FundingProps.witnessScript_size_of_wellFormed p hwf)
  rw [← hrev, hlink]

/-- Corollary under the stronger, idealised full-injectivity assumption already
used by `FundingProps.p2wsh_program_binds_witnessScript`.  It needs no length
side conditions, at the cost of assuming injectivity on all byte strings. -/
theorem waveF_f01_p2wsh_binds_witnessScript_of_injective
    (sha256 : ByteArray → ByteArray)
    (hinj : ∀ a b : ByteArray, sha256 a = sha256 b → a = b)
    {p : FundingParams} (hlink : FundingHashLinked sha256 p)
    (revealed : ByteArray)
    (hrev : p.witnessScriptHash = sha256 revealed) :
    revealed = p.witnessScript.bytes := by
  apply hinj
  rw [← hrev, hlink]

/-- The `scriptPubKey` of every confirmed funding output is the P2WSH wrapper
over `SHA256(witnessScript.bytes)` whenever the hash link holds.  This is the
output-level content of "the funding output commits to the 2-of-2 script". -/
theorem waveF_f01_confirmed_script_commits_to_hash
    (sha256 : ByteArray → ByteArray) {p : FundingParams}
    (hlink : FundingHashLinked sha256 p) {tx : Tx} {index : Nat}
    (hc : FundingConfirmed p tx index) :
    ∃ out : TxOut,
      tx.vout[index]? = some out ∧
      out.scriptPubKey.bytes =
        (ByteArray.empty.push OP_0).push 0x20 ++
          sha256 p.witnessScript.bytes := by
  obtain ⟨out, hout, hscript⟩ := FundingConfirmed.script_eq hc
  refine ⟨out, hout, ?_⟩
  rw [hscript]
  exact waveF_f01_hashLinked_scriptPubKey_bytes sha256 p hlink

/-- **P2WSH funding-output binding (confirmed-output level).**  Given a
confirmed funding output, the hash link, and collision resistance on 71-byte
scripts, any witness program `SHA256(revealed)` that is the output's P2WSH
program forces `revealed` to be the BOLT 3 funding witness script. -/
theorem waveF_f01_confirmed_binds_witnessScript
    (sha256 : ByteArray → ByteArray)
    (hcr : FundingScriptCollisionResistant sha256)
    {p : FundingParams} (hwf : p.WellFormed)
    (hlink : FundingHashLinked sha256 p) {tx : Tx} {index : Nat}
    (hc : FundingConfirmed p tx index) {out : TxOut}
    (hout : tx.vout[index]? = some out) (revealed : ByteArray)
    (hrevSize : revealed.size = 71)
    (hrev : out.scriptPubKey = LnLean.Bitcoin.p2wsh (sha256 revealed)) :
    revealed = p.witnessScript.bytes := by
  obtain ⟨outC, houtC, hscriptC⟩ := FundingConfirmed.script_eq hc
  have hout_eq : out = outC := by
    have hsome : some out = some outC := hout.symm.trans houtC
    exact Option.some.inj hsome
  have hscriptOut : out.scriptPubKey = p.fundingScriptPubKey := by
    rw [hout_eq, hscriptC]
  have hprog : p.witnessScriptHash = sha256 revealed := by
    apply waveF_f01_p2wsh_injective
    calc
      LnLean.Bitcoin.p2wsh p.witnessScriptHash = p.fundingScriptPubKey := rfl
      _ = out.scriptPubKey := hscriptOut.symm
      _ = LnLean.Bitcoin.p2wsh (sha256 revealed) := hrev
  exact waveF_f01_p2wsh_binds_witnessScript sha256 hcr p hwf hlink revealed
    hrevSize hprog

/-- The linked hash is the hash of the BOLT 3 2-of-2 script in one of the two
key orders permitted by `orderedFundingKeys` / BOLT 3. -/
theorem waveF_f01_hashLinked_commits_to_2of2
    (sha256 : ByteArray → ByteArray) (p : FundingParams)
    (h : FundingHashLinked sha256 p) :
    p.witnessScriptHash = sha256
        ((ByteArray.empty.push 0x52) ++ pushData p.localFundingKey.bytes
          ++ pushData p.remoteFundingKey.bytes
          ++ (ByteArray.empty.push 0x52)
          ++ (ByteArray.empty.push OP_CHECKMULTISIG))
    ∨ p.witnessScriptHash = sha256
        ((ByteArray.empty.push 0x52) ++ pushData p.remoteFundingKey.bytes
          ++ pushData p.localFundingKey.bytes
          ++ (ByteArray.empty.push 0x52)
          ++ (ByteArray.empty.push OP_CHECKMULTISIG)) := by
  rcases LnLean.Proofs.Bitcoin.FundingProps.witnessScript_is_2of2_over_funding_keys p
    with hord | hord
  · left
    rw [h, hord]
  · right
    rw [h, hord]

/-! ## The invariant is not vacuous -/

/-- For every parameter record there is *some* hash function that links it:
the model's hash field is under-specified, not contradictory.  The
counterexample below is therefore about missing constraints, not about an
impossible predicate. -/
theorem waveF_f01_hashLinked_satisfiable (p : FundingParams) :
    ∃ sha256 : ByteArray → ByteArray, FundingHashLinked sha256 p := by
  refine ⟨fun b =>
    if b = p.witnessScript.bytes then p.witnessScriptHash else ByteArray.empty, ?_⟩
  unfold FundingHashLinked
  simp

/-! ## Counterexample: `WellFormed` does not imply the hash link -/

/-- 33 zero bytes: the structural length of a compressed public key.  This is
only a *length* witness; key validity in the wave-A model is length only. -/
def waveF_f01_cexKeyBytes : ByteArray :=
  ByteArray.mk (List.replicate 33 (0 : UInt8)).toArray

/-- 32 zero bytes. -/
def waveF_f01_cexZero32 : ByteArray :=
  ByteArray.mk (List.replicate 32 (0 : UInt8)).toArray

/-- 32 one bytes. -/
def waveF_f01_cexOne32 : ByteArray :=
  ByteArray.mk (List.replicate 32 (1 : UInt8)).toArray

theorem waveF_f01_cexKeyBytes_size : waveF_f01_cexKeyBytes.size = 33 := by
  decide

theorem waveF_f01_cexZero32_size : waveF_f01_cexZero32.size = 32 := by
  decide

theorem waveF_f01_cexOne32_size : waveF_f01_cexOne32.size = 32 := by
  decide

/-- A well-formed funding record family parameterised by the stored 32-byte
witness-script hash.  The two funding keys are identical, so the witness
script does not depend on the hash parameter. -/
def waveF_f01_cexParams (h : ByteArray) : FundingParams :=
  { fundingSatoshis := 0
    pushMsat := ⟨0⟩
    localFundingKey := ⟨waveF_f01_cexKeyBytes⟩
    remoteFundingKey := ⟨waveF_f01_cexKeyBytes⟩
    witnessScriptHash := h
    temporaryChannelId := ⟨⟨ByteArray.empty⟩⟩ }

theorem waveF_f01_cexParams_wellFormed (h : ByteArray) (hh : h.size = 32) :
    (waveF_f01_cexParams h).WellFormed := by
  unfold FundingParams.WellFormed
  simp only [waveF_f01_cexParams, hh]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · exact waveF_f01_cexKeyBytes_size
  · exact waveF_f01_cexKeyBytes_size
  · trivial
  · decide

/-- The witness script of the counterexample family does not depend on the
stored hash: both records have the same funding keys. -/
theorem waveF_f01_cexParams_witnessScript_eq (a b : ByteArray) :
    (waveF_f01_cexParams a).witnessScript =
      (waveF_f01_cexParams b).witnessScript := rfl

theorem waveF_f01_cexZero32_ne_one32 : waveF_f01_cexZero32 ≠ waveF_f01_cexOne32 := by
  intro h
  have hz : waveF_f01_cexZero32[0]? = some (0 : UInt8) := by decide
  have ho : waveF_f01_cexOne32[0]? = some (1 : UInt8) := by decide
  rw [h] at hz
  rw [ho] at hz
  exact absurd (Option.some.inj hz) (by decide)

/-- **No single `sha256` can link both records.**  They are both well formed
and share the same funding witness script, but store different 32-byte hashes;
the link equation would identify those hashes. -/
theorem waveF_f01_no_sha256_links_both_cex :
    ¬ ∃ sha256 : ByteArray → ByteArray,
        FundingHashLinked sha256 (waveF_f01_cexParams waveF_f01_cexZero32) ∧
        FundingHashLinked sha256 (waveF_f01_cexParams waveF_f01_cexOne32) := by
  rintro ⟨sha256, h0, h1⟩
  unfold FundingHashLinked at h0 h1
  have hws := waveF_f01_cexParams_witnessScript_eq
    waveF_f01_cexZero32 waveF_f01_cexOne32
  rw [← hws] at h1
  exact waveF_f01_cexZero32_ne_one32 (h0.trans h1.symm)

/-- **The current model does not imply the invariant.**  `WellFormed` is not
enough to conclude `FundingHashLinked sha256 p` for an arbitrary `sha256`; even
the two hash values are unconstrained.  This is the mechanized negative result
for `LN-FUND-HASH`. -/
theorem waveF_f01_wellFormed_not_implies_hashLinked :
    ¬ (∀ (sha256 : ByteArray → ByteArray) (p : FundingParams),
        p.WellFormed → FundingHashLinked sha256 p) := by
  intro hall
  have h0 : FundingHashLinked (fun _ => waveF_f01_cexZero32)
      (waveF_f01_cexParams waveF_f01_cexZero32) :=
    hall (fun _ => waveF_f01_cexZero32) (waveF_f01_cexParams waveF_f01_cexZero32)
      (waveF_f01_cexParams_wellFormed waveF_f01_cexZero32
        waveF_f01_cexZero32_size)
  have h1 : FundingHashLinked (fun _ => waveF_f01_cexZero32)
      (waveF_f01_cexParams waveF_f01_cexOne32) :=
    hall (fun _ => waveF_f01_cexZero32) (waveF_f01_cexParams waveF_f01_cexOne32)
      (waveF_f01_cexParams_wellFormed waveF_f01_cexOne32
        waveF_f01_cexOne32_size)
  exact waveF_f01_no_sha256_links_both_cex
    ⟨fun _ => waveF_f01_cexZero32, h0, h1⟩

end LnLean.Proofs.ModelHardening.F01
