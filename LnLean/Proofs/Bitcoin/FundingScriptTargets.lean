import LnLean.Proofs.Bitcoin.FundingProps
import LnLean.Crypto.Model

/-!
# Funding script targets: P2WSH over the BOLT 3 2-of-2 witness script

**English claim (catalog `LN-L1-001`).**  A Lightning funding output is a
Pay-to-Witness-Script-Hash (P2WSH, BIP 141) output whose committed witness
script is BOLT 3's

`OP_2 <funding_pubkey1> <funding_pubkey2> OP_2 OP_CHECKMULTISIG`

with the two *compressed* funding keys in lexicographic order.  The output
script is therefore

`OP_0 <0x20> SHA256(OP_2 <pk1> <pk2> OP_2 OP_CHECKMULTISIG)`.

This module states that connection at the level the tree actually models:

* **Unconditional structural half.**  `fundingScriptPubKey h` is the P2WSH
  wrapper `OP_0 <0x20> h`; it is 34 bytes for a 32-byte `h`; the P2WSH wrapper
  is injective, so the on-chain output determines its witness program; and
  `FundingParams.witnessScript` is exactly the BOLT 3 2-of-2 template over the
  two funding keys, in one of the two key orders.
* **Conditional hash half.**  Given the explicit missing invariant
  `FundingScriptHashLinked H p`, i.e. `p.witnessScriptHash =
  H p.witnessScript.bytes`, the funding `scriptPubKey` is literally
  `p2wsh (H <2-of-2 script bytes>)` (either key order), at both the
  `FundingParams`, `FundingOutput`, and confirmed-`TxOut` levels.
* **Reverse binding.**  A revealed script whose hash is the committed P2WSH
  program is exactly the funding witness script, under a *pair-level* C1
  admission `CollisionFreeOn H revealed p.witnessScript.bytes`.  This is the
  satisfiable form of collision resistance at the point of use.

## Assumptions C1 and C2

`docs/ASSUMPTIONS.md` states C1 as collision resistance of SHA-256 on the
**32-byte** payment-preimage domain:

```lean
CollisionResistant H :=
  ∀ x y, x.size = 32 → y.size = 32 → H x = H y → x = y
```

P2WSH hashes a **71-byte** funding witness script, not a 32-byte preimage.
The two domains are different, and this module does **not** silently reuse C1:

* `c1_32_does_not_bind_funding_witnessScripts` mechanizes the gap.  There is a
  function with 32-byte output that satisfies `Crypto.CollisionResistant`
  (because it is the identity on 32-byte inputs) yet collides on two distinct
  71-byte strings.  So C1 on the 32-byte domain alone cannot justify
  "SHA256 determines the revealed 71-byte witness script".
* Exact injectivity on all 71-byte strings (`CollisionResistantOn H 71`) is
  also *not* assumed here: together with a 32-byte output width it is
  impossible by pigeonhole (256^71 inputs, 256^32 outputs).  Assuming it would
  make the binding theorem vacuous for any real SHA-256.  The honest,
  non-vacuous form is the finite pair admission `CollisionFreeOn H x y`
  (`H x = H y → x = y`) for the one revealed script and the one constructed
  script.  This mirrors the finite-execution C8 admission for HMAC.
* `fundingScriptPair_assumptions_satisfiable` proves that the whole bundle
  (32-byte-output hash, two well-formed parameter sets, both hash links, and
  the pair C1 admission) is satisfiable with two *distinct* funding witness
  scripts.  The conditional half is therefore not vacuous.

C2 (`HASH160 = RIPEMD160(SHA256(x))` collision resistance) is **not used by
this target**.  P2WSH commits to a witness script with SHA-256; HASH160 is the
commitment used by P2WPKH outputs (for example the `to_remote` output), not by
the funding output.  `Hash160CollisionResistant` is recorded below only to
make the boundary explicit; no theorem in this module depends on it.

## The exact missing bridge

The model stores `FundingParams.witnessScriptHash` as a free 32-byte field.
`FundingParams.WellFormed` checks only its length, not its value.  Therefore
the step

`p.witnessScriptHash = SHA256(p.witnessScript.bytes)`

is a construction invariant that must be supplied by the channel-opening code
(`make_funding_redeemscript` followed by SHA-256 in rust-lightning), not a
theorem of the wave-A record.  It is the hypothesis `FundingScriptHashLinked`
below.  A concrete SHA-256 implementation, its computational
collision-resistance game, and a P2WSH/`OP_CHECKMULTISIG` interpreter run are
also outside the imported vendor interface: `Bitcoin.Data.Script.parse` has no
`OP_CHECKMULTISIG` constructor, and the vendored `Bitcoin.Interpreter` is not
connected to the BOLT 3 witness shape.  This module proves the output-format
and hash-commitment half; it does not claim consensus-level spendability.

## Anchors

* BOLT 3, "Funding Transaction Output"
  (`refs/bolts/03-transactions.md:75-83` at BOLT commit
  `1aadb719b4007c4cea0ba6e36b08c4fb53788dee`): the output is the P2WSH of
  `2 <pubkey1> <pubkey2> 2 OP_CHECKMULTISIG`.
* BIP 141: witness version 0 with a 32-byte program (`OP_0 <0x20> <program>`).
* `refs/rust-lightning/lightning/src/ln/chan_utils.rs:847-866`
  (`make_funding_redeemscript`, `make_funding_redeemscript_from_slices`) and
  `lightning/src/ln/channel.rs:2711-2725` (`get_funding_txo`).
-/

namespace LnLean.Proofs.Bitcoin.FundingScriptTargets

set_option autoImplicit false

open LnLean
open LnLean.Bitcoin
open LnLean.Crypto

/-! ## The BOLT 3 2-of-2 witness script -/

/-- The exact BOLT 3 funding witness-script bytes:
`OP_2 <a> <b> OP_2 OP_CHECKMULTISIG`, with both keys serialized as minimal
direct pushes.  BOLT 3 requires `a` and `b` to be the two compressed funding
keys in lexicographic order; `FundingParams.witnessScript` supplies that
order. -/
def TwoOfTwoScriptBytes (a b : PubKey) : ByteArray :=
  (ByteArray.empty.push 0x52)
    ++ pushData a.bytes
    ++ pushData b.bytes
    ++ (ByteArray.empty.push 0x52)
    ++ (ByteArray.empty.push OP_CHECKMULTISIG)

/-- A byte string is the BOLT 3 funding witness script for the two keys `a`
and `b`, allowing either order.  The disjunction is required because
`orderedFundingKeys` chooses the order from the serialized key bytes; both
orientations denote the same 2-of-2 multisig over the same key set. -/
abbrev IsTwoOfTwoScript (a b : PubKey) (s : ByteArray) : Prop :=
  s = TwoOfTwoScriptBytes a b ∨ s = TwoOfTwoScriptBytes b a

/-- The constructed witness script is 71 bytes when both keys are compressed
(33-byte) public keys: `1 + 34 + 34 + 1 + 1`. -/
theorem TwoOfTwoScriptBytes_size (a b : PubKey)
    (ha : a.bytes.size = 33) (hb : b.bytes.size = 33) :
    (TwoOfTwoScriptBytes a b).size = 71 := by
  simp [TwoOfTwoScriptBytes, pushData, ByteArray.size_append,
    ByteArray.size_push, ByteArray.size_empty, ha, hb]

/-- `FundingParams.witnessScript` is definitionally the BOLT 3 template over
the ordered key pair. -/
theorem witnessScript_eq_TwoOfTwoScriptBytes (p : FundingParams) :
    p.witnessScript.bytes =
      TwoOfTwoScriptBytes
        (orderedFundingKeys p.localFundingKey p.remoteFundingKey).1
        (orderedFundingKeys p.localFundingKey p.remoteFundingKey).2 := by
  rfl

/-- The constructed funding witness script is exactly a 2-of-2 multisig over
the two funding keys, in one of the two BOLT 3 orders.  This is the
unconditional "2-of-2 witness script" half of `LN-L1-001`. -/
theorem witnessScript_isTwoOfTwoScript (p : FundingParams) :
    IsTwoOfTwoScript p.localFundingKey p.remoteFundingKey
      p.witnessScript.bytes := by
  rcases LnLean.Proofs.Bitcoin.FundingProps.orderedFundingKeys_pair
    p.localFundingKey p.remoteFundingKey with h | h
  · left
    rw [witnessScript_eq_TwoOfTwoScriptBytes]
    simp [h]
  · right
    rw [witnessScript_eq_TwoOfTwoScriptBytes]
    simp [h]

/-- For well-formed funding parameters the constructed witness script is 71
bytes (33-byte compressed keys). -/
theorem witnessScript_size (p : FundingParams) (hwf : p.WellFormed) :
    p.witnessScript.bytes.size = 71 :=
  LnLean.Proofs.Bitcoin.FundingProps.witnessScript_size_of_wellFormed p hwf

/-! ## The P2WSH output wrapper -/

/-- A script is a witness-version-0 P2WSH output with witness program
`program`, i.e. `OP_0 <0x20> <program>` (BIP 141). -/
def IsP2WSHOutput (s : Script) (program : ByteArray) : Prop :=
  s.bytes = (ByteArray.empty.push OP_0).push 0x20 ++ program

/-- The seam's `fundingScriptPubKey` is literally the P2WSH wrapper. -/
theorem fundingScriptPubKey_is_p2wsh (program : ByteArray) :
    LnLean.Bitcoin.fundingScriptPubKey program = p2wsh program := rfl

/-- Byte-level shape of the seam funding script:
`OP_0 <0x20> <program>`. -/
theorem fundingScriptPubKey_bytes (program : ByteArray) :
    (LnLean.Bitcoin.fundingScriptPubKey program).bytes =
      (ByteArray.empty.push OP_0).push 0x20 ++ program := rfl

/-- The seam funding script is a P2WSH output whose program is its argument. -/
theorem fundingScriptPubKey_isP2WSHOutput (program : ByteArray) :
    IsP2WSHOutput (LnLean.Bitcoin.fundingScriptPubKey program) program := rfl

/-- A P2WSH output with a 32-byte program is exactly 34 bytes. -/
theorem fundingScriptPubKey_size (program : ByteArray)
    (h : program.size = 32) :
    (LnLean.Bitcoin.fundingScriptPubKey program).bytes.size = 34 :=
  LnLean.Bitcoin.p2wsh_size program h

/-- The P2WSH wrapper is injective on the witness program: equal output
scripts have equal programs.  This is an encoding fact, not a cryptographic
assumption, and it is what lets the on-chain script determine the committed
hash without any collision-resistance hypothesis. -/
theorem p2wsh_injective {a b : ByteArray} (h : p2wsh a = p2wsh b) : a = b := by
  have hb : (ByteArray.empty.push OP_0).push 0x20 ++ a =
      (ByteArray.empty.push OP_0).push 0x20 ++ b := by
    simpa [p2wsh] using congrArg (fun s : Script => s.bytes) h
  exact (ByteArray.append_right_inj ((ByteArray.empty.push OP_0).push 0x20)).mp hb

/-- `fundingScriptPubKey` is injective: the funding output determines its
witness-script hash. -/
theorem fundingScriptPubKey_injective {a b : ByteArray}
    (h : LnLean.Bitcoin.fundingScriptPubKey a =
      LnLean.Bitcoin.fundingScriptPubKey b) : a = b := by
  apply p2wsh_injective
  simpa [LnLean.Bitcoin.fundingScriptPubKey] using h

/-! ## The missing hash-link invariant -/

/-- **The explicit hash bridge.**  The P2WSH program stored in the funding
parameters is the hash `H` of the constructed BOLT 3 witness script.  This is
not a field of `FundingParams`; `WellFormed` only fixes the digest length.
Every theorem that identifies the output with `SHA256(witnessScript)` takes
this hypothesis. -/
def FundingScriptHashLinked (H : ByteArray → ByteArray)
    (p : FundingParams) : Prop :=
  p.witnessScriptHash = H p.witnessScript.bytes

/-- Under the hash link the funding `scriptPubKey` is the P2WSH output whose
program is `H (witnessScript.bytes)`. -/
theorem fundingScriptPubKey_eq_p2wsh_hash
    (H : ByteArray → ByteArray) (p : FundingParams)
    (hlink : FundingScriptHashLinked H p) :
    p.fundingScriptPubKey = p2wsh (H p.witnessScript.bytes) := by
  unfold FundingScriptHashLinked at hlink
  simp [FundingParams.fundingScriptPubKey,
    LnLean.Bitcoin.fundingScriptPubKey, hlink]

/-- Byte-level form: the output is exactly
`OP_0 <0x20> H(witnessScript.bytes)`. -/
theorem fundingScriptPubKey_bytes_eq_hash
    (H : ByteArray → ByteArray) (p : FundingParams)
    (hlink : FundingScriptHashLinked H p) :
    p.fundingScriptPubKey.bytes =
      (ByteArray.empty.push OP_0).push 0x20 ++ H p.witnessScript.bytes := by
  rw [fundingScriptPubKey_eq_p2wsh_hash H p hlink]
  rfl

/-- **Where the hash link meets the 2-of-2 script.**  The committed program is
the hash of the exact BOLT 3 2-of-2 bytes, in one of the two key orders. -/
theorem witnessScriptHash_eq_hash_twoOfTwo
    (H : ByteArray → ByteArray) (p : FundingParams)
    (hlink : FundingScriptHashLinked H p) :
    p.witnessScriptHash =
        H (TwoOfTwoScriptBytes p.localFundingKey p.remoteFundingKey) ∨
      p.witnessScriptHash =
        H (TwoOfTwoScriptBytes p.remoteFundingKey p.localFundingKey) := by
  unfold FundingScriptHashLinked at hlink
  rcases witnessScript_isTwoOfTwoScript p with h | h
  · left
    rw [hlink, h]
  · right
    rw [hlink, h]

/-- **Primary `LN-L1-001` target.**  Under the hash link, the funding output
is P2WSH over the constructed BOLT 3 2-of-2 witness script, in one of the two
key orders.  This is the exact model-level content of "the funding output is
P2WSH over the 2-of-2 funding witness script"; the hash link is the explicit
construction invariant that the wave-A record does not enforce. -/
theorem fundingScriptPubKey_eq_p2wsh_twoOfTwo
    (H : ByteArray → ByteArray) (p : FundingParams)
    (hlink : FundingScriptHashLinked H p) :
    p.fundingScriptPubKey =
        p2wsh (H (TwoOfTwoScriptBytes p.localFundingKey p.remoteFundingKey)) ∨
      p.fundingScriptPubKey =
        p2wsh (H (TwoOfTwoScriptBytes p.remoteFundingKey p.localFundingKey)) := by
  rcases witnessScript_isTwoOfTwoScript p with h | h
  · left
    rw [fundingScriptPubKey_eq_p2wsh_hash H p hlink, h]
  · right
    rw [fundingScriptPubKey_eq_p2wsh_hash H p hlink, h]

/-- Byte-level form of the primary target. -/
theorem fundingScriptPubKey_bytes_eq_twoOfTwo
    (H : ByteArray → ByteArray) (p : FundingParams)
    (hlink : FundingScriptHashLinked H p) :
    p.fundingScriptPubKey.bytes =
        (ByteArray.empty.push OP_0).push 0x20 ++
          H (TwoOfTwoScriptBytes p.localFundingKey p.remoteFundingKey) ∨
      p.fundingScriptPubKey.bytes =
        (ByteArray.empty.push OP_0).push 0x20 ++
          H (TwoOfTwoScriptBytes p.remoteFundingKey p.localFundingKey) := by
  rcases fundingScriptPubKey_eq_p2wsh_twoOfTwo H p hlink with h | h
  · left
    rw [h]
    rfl
  · right
    rw [h]
    rfl

/-! ## The L1 `FundingOutput` record -/

/-- The funding-output record's script is the P2WSH wrapper over its stored
hash. -/
theorem fundingOutput_scriptPubKey_eq_p2wsh (f : FundingOutput) :
    f.scriptPubKey = p2wsh f.witnessScriptHash := rfl

/-- Under a hash link to a supplied witness script, the funding-output record
is P2WSH over the hash of that script. -/
theorem fundingOutput_scriptPubKey_eq_p2wsh_hash
    (H : ByteArray → ByteArray) (f : FundingOutput) (witnessScript : ByteArray)
    (hlink : f.witnessScriptHash = H witnessScript) :
    f.scriptPubKey = p2wsh (H witnessScript) := by
  rw [fundingOutput_scriptPubKey_eq_p2wsh, hlink]

/-- Every output of a confirmed funding transaction has exactly the P2WSH
byte shape `OP_0 <0x20> H(<2-of-2 script>)`, in one of the two key orders. -/
theorem fundingConfirmed_script_commits_to_twoOfTwo
    (H : ByteArray → ByteArray) {p : FundingParams} {tx : Tx} {index : Nat}
    (hlink : FundingScriptHashLinked H p)
    (hc : FundingConfirmed p tx index) :
    ∃ out : TxOut,
      tx.vout[index]? = some out ∧
      (out.scriptPubKey.bytes =
          (ByteArray.empty.push OP_0).push 0x20 ++
            H (TwoOfTwoScriptBytes p.localFundingKey p.remoteFundingKey) ∨
       out.scriptPubKey.bytes =
          (ByteArray.empty.push OP_0).push 0x20 ++
            H (TwoOfTwoScriptBytes p.remoteFundingKey p.localFundingKey)) := by
  obtain ⟨out, hout, hscript⟩ := FundingConfirmed.script_eq hc
  refine ⟨out, hout, ?_⟩
  rw [hscript]
  rcases fundingScriptPubKey_eq_p2wsh_twoOfTwo H p hlink with h | h
  · left
    rw [h]
    rfl
  · right
    rw [h]
    rfl

/-! ## Reverse binding: the output determines the witness script

The reverse direction is where collision resistance enters.  It is stated as
the satisfiable pair admission `CollisionFreeOn`, not as global or 71-byte
injectivity, for the reasons in the module docstring. -/

/-- **C1 at the point of use.**  The hash function is collision-free on the
specific pair `(x, y)`.  This is a finite, satisfiable admission; it is the
P2WSH analogue of the finite-execution C8 HMAC contract. -/
def CollisionFreeOn (H : ByteArray → ByteArray) (x y : ByteArray) : Prop :=
  H x = H y → x = y

/-- Hash-level binding: if the committed program is `H revealed`, the link
holds, and `H` is collision-free on `(revealed, witnessScript)`, then the
revealed script *is* the constructed witness script.  No length side
condition is needed; when `p` is well formed the witness script is 71 bytes by
`witnessScript_size`. -/
theorem fundingScriptHash_binds_witnessScript
    (H : ByteArray → ByteArray) (p : FundingParams)
    (hlink : FundingScriptHashLinked H p) (revealed : ByteArray)
    (hrev : p.witnessScriptHash = H revealed)
    (hc1 : CollisionFreeOn H revealed p.witnessScript.bytes) :
    revealed = p.witnessScript.bytes := by
  apply hc1
  unfold FundingScriptHashLinked at hlink
  rw [← hrev, hlink]

/-- Script-level binding: if the funding output is the P2WSH wrapper over
`H revealed`, then `revealed` is the constructed funding witness script under
the pair C1 admission. -/
theorem fundingScriptPubKey_binds_witnessScript
    (H : ByteArray → ByteArray) (p : FundingParams)
    (hlink : FundingScriptHashLinked H p) (revealed : ByteArray)
    (hrev : p.fundingScriptPubKey = p2wsh (H revealed))
    (hc1 : CollisionFreeOn H revealed p.witnessScript.bytes) :
    revealed = p.witnessScript.bytes := by
  apply fundingScriptHash_binds_witnessScript H p hlink revealed ?_ hc1
  have hprog : p2wsh p.witnessScriptHash = p2wsh (H revealed) := by
    rw [show p2wsh p.witnessScriptHash = p.fundingScriptPubKey from rfl, hrev]
  exact p2wsh_injective hprog

/-- **Full reverse target.**  A script revealed against the funding P2WSH
output is exactly a BOLT 3 2-of-2 multisig over the two funding keys, in one
of the two orders, and (for well-formed parameters) it is 71 bytes.  The
hypotheses are the explicit hash link and the pair-level C1 admission. -/
theorem fundingScriptPubKey_binds_twoOfTwo
    (H : ByteArray → ByteArray) (p : FundingParams) (hwf : p.WellFormed)
    (hlink : FundingScriptHashLinked H p) (revealed : ByteArray)
    (hrev : p.fundingScriptPubKey = p2wsh (H revealed))
    (hc1 : CollisionFreeOn H revealed p.witnessScript.bytes) :
    IsTwoOfTwoScript p.localFundingKey p.remoteFundingKey revealed ∧
      revealed.size = 71 := by
  have heq : revealed = p.witnessScript.bytes :=
    fundingScriptPubKey_binds_witnessScript H p hlink revealed hrev hc1
  constructor
  · rw [heq]
    exact witnessScript_isTwoOfTwoScript p
  · rw [heq]
    exact witnessScript_size p hwf

/-- `FundingOutput`-level binding: the same theorem for the L1 record, without
reference to `FundingParams`. -/
theorem fundingOutput_binds_witnessScript
    (H : ByteArray → ByteArray) (f : FundingOutput)
    (witnessScript revealed : ByteArray)
    (hlink : f.witnessScriptHash = H witnessScript)
    (hrev : f.scriptPubKey = p2wsh (H revealed))
    (hc1 : CollisionFreeOn H revealed witnessScript) :
    revealed = witnessScript := by
  apply hc1
  have hprog : p2wsh (H revealed) = p2wsh (H witnessScript) := by
    rw [← hrev, fundingOutput_scriptPubKey_eq_p2wsh, hlink]
  exact p2wsh_injective hprog

/-! ## Determinism of the committed script -/

/-- Equal funding output scripts commit to the same witness program.  This is
purely structural: no hash assumption. -/
theorem fundingScriptPubKey_determines_hash {h₁ h₂ : ByteArray}
    (h : LnLean.Bitcoin.fundingScriptPubKey h₁ =
      LnLean.Bitcoin.fundingScriptPubKey h₂) : h₁ = h₂ := by
  apply p2wsh_injective
  simpa [LnLean.Bitcoin.fundingScriptPubKey] using h

/-- Two hash-linked funding parameter sets with the same output script have
the same 2-of-2 witness script, under the pair C1 admission. -/
theorem fundingScriptPubKey_determines_witnessScript
    (H : ByteArray → ByteArray) (p q : FundingParams)
    (hp : FundingScriptHashLinked H p) (hq : FundingScriptHashLinked H q)
    (heq : p.fundingScriptPubKey = q.fundingScriptPubKey)
    (hc1 : CollisionFreeOn H p.witnessScript.bytes q.witnessScript.bytes) :
    p.witnessScript.bytes = q.witnessScript.bytes := by
  apply hc1
  unfold FundingScriptHashLinked at hp hq
  rw [← hp, ← hq]
  apply fundingScriptPubKey_determines_hash
  simpa [FundingParams.fundingScriptPubKey,
    LnLean.Bitcoin.fundingScriptPubKey] using heq

/-- Confirmed-output form: two confirmed outputs in the same transaction with
equal `scriptPubKey` determine the same 2-of-2 witness script, under the pair
C1 admission.  The distinct indices and output witnesses make the statement
usable without assuming that the confirmed output is unique. -/
theorem confirmedFunding_determines_witnessScript
    (H : ByteArray → ByteArray) {p q : FundingParams} {tx : Tx} {i j : Nat}
    (hp : FundingScriptHashLinked H p) (hq : FundingScriptHashLinked H q)
    (hcp : FundingConfirmed p tx i) (hcq : FundingConfirmed q tx j)
    {op oq : TxOut}
    (hop : tx.vout[i]? = some op) (hoq : tx.vout[j]? = some oq)
    (hscript : op.scriptPubKey = oq.scriptPubKey)
    (hc1 : CollisionFreeOn H p.witnessScript.bytes q.witnessScript.bytes) :
    p.witnessScript.bytes = q.witnessScript.bytes := by
  obtain ⟨op', hop', hsp⟩ := FundingConfirmed.script_eq hcp
  obtain ⟨oq', hoq', hsq⟩ := FundingConfirmed.script_eq hcq
  have hopEq : op' = op := Option.some.inj (hop'.symm.trans hop)
  have hoqEq : oq' = oq := Option.some.inj (hoq'.symm.trans hoq)
  have hpq : p.fundingScriptPubKey = q.fundingScriptPubKey := by
    have hscripts : op'.scriptPubKey = oq'.scriptPubKey := by
      simpa [hopEq, hoqEq] using hscript
    rw [← hsp, ← hsq]
    exact hscripts
  exact fundingScriptPubKey_determines_witnessScript H p q hp hq hpq hc1

/-! ## C1 and C2 boundaries, mechanized -/

/-- Length-indexed collision resistance, used to state precisely what C1 does
and does not cover.  `CollisionResistantOn H 32` is definitionally the model's
C1 `Crypto.CollisionResistant H`. -/
abbrev CollisionResistantOn (H : ByteArray → ByteArray) (n : Nat) : Prop :=
  ∀ x y : ByteArray, x.size = n → y.size = n → H x = H y → x = y

/-- C1 is exactly the length-32 instance of length-indexed collision
resistance. -/
theorem collisionResistant_iff_collisionResistantOn_32
    (H : ByteArray → ByteArray) :
    LnLean.Crypto.CollisionResistant H ↔ CollisionResistantOn H 32 :=
  Iff.rfl

/-- C2's shape, recorded for scope.  The funding output is P2WSH, which uses
SHA-256, so no theorem here consumes HASH160 collision resistance.  C2 is
relevant to P2WPKH outputs such as `to_remote`, not to `LN-L1-001`. -/
abbrev Hash160CollisionResistant (H160 : ByteArray → ByteArray) : Prop :=
  ∀ x y : ByteArray, H160 x = H160 y → x = y

/-- A hash with 32-byte output that is injective on 32-byte inputs but maps
every other input to zero.  It witnesses the gap between C1's domain and the
71-byte funding-script domain. -/
def c1OnlyHash (x : ByteArray) : ByteArray :=
  if x.size = 32 then x else ByteArray.mk (List.replicate 32 (0 : UInt8)).toArray

theorem c1OnlyHash_size (x : ByteArray) : (c1OnlyHash x).size = 32 := by
  unfold c1OnlyHash
  split
  · assumption
  · simp [ByteArray.size]

theorem c1OnlyHash_collisionResistant :
    LnLean.Crypto.CollisionResistant c1OnlyHash := by
  intro x y hx hy h
  unfold c1OnlyHash at h
  simpa [hx, hy] using h

/-- **C1 does not bind 71-byte funding scripts by itself.**  There is a hash
with 32-byte output satisfying C1 (injectivity on 32-byte inputs) that
collides on two distinct 71-byte strings.  Hence the P2WSH reverse direction
needs the separate, pair-level admission `CollisionFreeOn`; it cannot be
derived from the model's 32-byte C1 field. -/
theorem c1_32_does_not_bind_funding_witnessScripts :
    ∃ H : ByteArray → ByteArray,
      (∀ b : ByteArray, (H b).size = 32) ∧
      LnLean.Crypto.CollisionResistant H ∧
      ∃ x y : ByteArray,
        x.size = 71 ∧ y.size = 71 ∧ x ≠ y ∧ H x = H y := by
  let z71 : ByteArray := ByteArray.mk (List.replicate 71 (0 : UInt8)).toArray
  let o71 : ByteArray := ByteArray.mk (List.replicate 71 (1 : UInt8)).toArray
  have hz : z71.size = 71 := by simp [z71, ByteArray.size]
  have ho : o71.size = 71 := by simp [o71, ByteArray.size]
  have hne : z71 ≠ o71 := by
    intro h
    have hzi : z71[0]? = some (0 : UInt8) := by decide
    have hoi : o71[0]? = some (1 : UInt8) := by decide
    rw [h] at hzi
    rw [hoi] at hzi
    exact absurd (Option.some.inj hzi) (by decide)
  refine ⟨c1OnlyHash, c1OnlyHash_size, c1OnlyHash_collisionResistant,
    z71, o71, hz, ho, hne, ?_⟩
  unfold c1OnlyHash
  rw [ite_eq_right (by rw [hz]; decide), ite_eq_right (by rw [ho]; decide)]

/-! ## The conditional bundle is not vacuous -/

/-- A concrete 32-byte-output hash that separates `sep` from every other
input.  It is used only to witness satisfiability. -/
def demoHash (sep : ByteArray) (x : ByteArray) : ByteArray :=
  if x = sep then ByteArray.mk (List.replicate 32 (1 : UInt8)).toArray
  else ByteArray.mk (List.replicate 32 (0 : UInt8)).toArray

theorem demoHash_size (sep x : ByteArray) : (demoHash sep x).size = 32 := by
  unfold demoHash
  split <;> simp [ByteArray.size]

theorem demoHash_self (sep : ByteArray) :
    demoHash sep sep = ByteArray.mk (List.replicate 32 (1 : UInt8)).toArray := by
  simp [demoHash]

theorem demoHash_ne (sep x : ByteArray) (h : x ≠ sep) :
    demoHash sep x = ByteArray.mk (List.replicate 32 (0 : UInt8)).toArray := by
  simp [demoHash, h]

/-- `demoHash sep` is collision-free on `(sep, x)` whenever `x ≠ sep`. -/
theorem demoHash_collisionFree (sep x : ByteArray) (h : x ≠ sep) :
    CollisionFreeOn (demoHash sep) sep x := by
  intro hcol
  exfalso
  rw [demoHash_self, demoHash_ne sep x h] at hcol
  have hzero : (ByteArray.mk (List.replicate 32 (0 : UInt8)).toArray)[0]?
      = some (0 : UInt8) := by decide
  have hone : (ByteArray.mk (List.replicate 32 (1 : UInt8)).toArray)[0]?
      = some (1 : UInt8) := by decide
  rw [← hcol] at hzero
  rw [hone] at hzero
  exact absurd (Option.some.inj hzero) (by decide)

/-- **Non-vacuity of the conditional bundle.**  There are two well-formed
funding parameter sets with *distinct* 2-of-2 witness scripts, a hash with
32-byte output, both hash links, and the pair C1 admission.  So the binding
theorem is not vacuous merely because its C1 hypothesis is unsatisfiable. -/
theorem fundingScriptPair_assumptions_satisfiable :
    ∃ (H : ByteArray → ByteArray) (p q : FundingParams),
      (∀ b : ByteArray, (H b).size = 32) ∧
      p.WellFormed ∧ q.WellFormed ∧
      FundingScriptHashLinked H p ∧ FundingScriptHashLinked H q ∧
      p.witnessScript.bytes ≠ q.witnessScript.bytes ∧
      CollisionFreeOn H p.witnessScript.bytes q.witnessScript.bytes := by
  let key33 (b : UInt8) : ByteArray :=
    ByteArray.mk (List.replicate 33 b).toArray
  let keyPub (b : UInt8) : PubKey := ⟨key33 b⟩
  let params33 (b : UInt8) (hash : ByteArray) : FundingParams :=
    { fundingSatoshis := 0
      pushMsat := ⟨0⟩
      localFundingKey := keyPub b
      remoteFundingKey := keyPub b
      witnessScriptHash := hash
      temporaryChannelId := ⟨⟨ByteArray.empty⟩⟩ }
  have hkey : ∀ b : UInt8, (key33 b).size = 33 := by
    intro b
    simp [key33, ByteArray.size]
  have hparamsWf : ∀ (b : UInt8) (hash : ByteArray), hash.size = 32 →
      (params33 b hash).WellFormed := by
    intro b hash hh
    unfold FundingParams.WellFormed
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [params33]
    · simp [params33, Bitcoin.Data.MAX_MONEY, Bitcoin.Data.COIN]
    · change (key33 b).size = 33
      exact hkey b
    · change (key33 b).size = 33
      exact hkey b
    · simpa [params33] using hh
    · simp [params33]
  have hws : ∀ (b : UInt8) (hash : ByteArray),
      (params33 b hash).witnessScript.bytes =
        (ByteArray.empty.push 0x52)
          ++ pushData (key33 b)
          ++ pushData (key33 b)
          ++ (ByteArray.empty.push 0x52)
          ++ (ByteArray.empty.push OP_CHECKMULTISIG) := by
    intro b hash
    simp [params33, FundingParams.witnessScript, keyPub,
      LnLean.Proofs.Bitcoin.FundingProps.orderedFundingKeys_self]
  have hne : (params33 0 (ByteArray.mk (List.replicate 32 (1 : UInt8)).toArray)).witnessScript.bytes ≠
      (params33 1 (ByteArray.mk (List.replicate 32 (0 : UInt8)).toArray)).witnessScript.bytes := by
    intro h
    have hp0 : (params33 0 (ByteArray.mk (List.replicate 32 (1 : UInt8)).toArray)).witnessScript.bytes[2]?
        = some (0 : UInt8) := by
      rw [hws]
      decide
    have hp1 : (params33 1 (ByteArray.mk (List.replicate 32 (0 : UInt8)).toArray)).witnessScript.bytes[2]?
        = some (1 : UInt8) := by
      rw [hws]
      decide
    rw [h] at hp0
    rw [hp1] at hp0
    exact absurd (Option.some.inj hp0) (by decide)
  let p : FundingParams :=
    params33 0 (ByteArray.mk (List.replicate 32 (1 : UInt8)).toArray)
  let q : FundingParams :=
    params33 1 (ByteArray.mk (List.replicate 32 (0 : UInt8)).toArray)
  let H : ByteArray → ByteArray := demoHash p.witnessScript.bytes
  have hpne : p.witnessScript.bytes ≠ q.witnessScript.bytes := hne
  have hqne : q.witnessScript.bytes ≠ p.witnessScript.bytes := hne.symm
  have hsz1 : (ByteArray.mk (List.replicate 32 (1 : UInt8)).toArray).size = 32 := by
    simp [ByteArray.size]
  have hsz0 : (ByteArray.mk (List.replicate 32 (0 : UInt8)).toArray).size = 32 := by
    simp [ByteArray.size]
  refine ⟨H, p, q, demoHash_size _, hparamsWf 0 _ hsz1,
    hparamsWf 1 _ hsz0, ?_, ?_, hpne, demoHash_collisionFree _ _ hqne⟩
  · unfold FundingScriptHashLinked
    change (params33 0 (ByteArray.mk (List.replicate 32 (1 : UInt8)).toArray)).witnessScriptHash =
      demoHash (params33 0 (ByteArray.mk (List.replicate 32 (1 : UInt8)).toArray)).witnessScript.bytes
        (params33 0 (ByteArray.mk (List.replicate 32 (1 : UInt8)).toArray)).witnessScript.bytes
    rw [demoHash_self]
  · unfold FundingScriptHashLinked
    change (params33 1 (ByteArray.mk (List.replicate 32 (0 : UInt8)).toArray)).witnessScriptHash =
      demoHash (params33 0 (ByteArray.mk (List.replicate 32 (1 : UInt8)).toArray)).witnessScript.bytes
        (params33 1 (ByteArray.mk (List.replicate 32 (0 : UInt8)).toArray)).witnessScript.bytes
    rw [demoHash_ne _ _ hqne]

end LnLean.Proofs.Bitcoin.FundingScriptTargets
