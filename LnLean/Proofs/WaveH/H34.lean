/-
# H34 — C1 does not bind 71-byte funding witness scripts (`L1-05`)

**Issue `L1-05` (P1).**  The model's assumption C1 is collision resistance of
SHA-256 on the **32-byte payment-preimage** domain
(`Crypto.CollisionResistant`).  A BOLT 3 funding output commits to
`SHA256` of a **71-byte** 2-of-2 witness script.  The two domains are different,
so C1 cannot be reused to conclude that the P2WSH program determines the
revealed script.  `FundingScriptTargets.c1_32_does_not_bind_funding_witnessScripts`
already mechanized the bare-function gap: there is a 32-byte-output function
satisfying C1 that collides on two distinct 71-byte strings.  The reverse
direction of `LN-L1-001` therefore keeps the finite pair admission
`CollisionFreeOn H revealed witnessScript`, and `FundingLinkTargets` keeps the
same admission for the handshake-constructed parameters.

## What this module adds

1. **A full `PrimitiveModel` counterexample, not a bare function.**
   `c1CollisionModel` inhabits the *entire* `PrimitiveModel` structure with
   `sha256 = c1OnlyHash`: the 32-byte C1 field holds, the 32-byte width field
   holds, and the remaining primitive fields are instantiated by trivial
   (but inhabitable) operations.  Hence no `PrimitiveModel` field forces
   injectivity on 71-byte inputs:
   `no_primitive_model_binds_71_byte_scripts`.
2. **A funding-output collision.**  Two *well-formed* `FundingParams` with
   **distinct** 71-byte BOLT 3 2-of-2 witness scripts store the same P2WSH
   program and therefore have the **same** `fundingScriptPubKey`
   (`c1_model_does_not_bind_funding_witnessScripts`).  Both records are
   hash-linked (`FundingScriptHashLinked M.sha256`) to their own witness
   scripts, so this is a genuine same-output / different-script collision in a
   model where C1 is true.
3. **A domain-separated script commitment.**
   `scriptCommitment H s := H (scriptDomainTag ++ s)` with a 32-byte tag.
   The closure theorem `scriptCommitment_binds_witnessScript` (and its
   `FundingNegotiation`/2-of-2 form `scriptCommitment_binds_twoOfTwo`) closes
   the intended construction *under the finite pair admission at the tagged
   preimages* — the same admission shape the tree already uses, with the hash
   argument instantiated at `scriptCommitment H`.  `scriptCommitment_hash_linked`
   shows the existing construction `FundingNegotiation.toFundingParams` accepts
   the separated commitment unchanged.
4. **Domain separation is structural, not cryptographic.**
   `scriptCommitment_preimage_ne_payment_preimage` proves the tagged script
   preimage (103 bytes for a 71-byte script) is never a 32-byte payment
   preimage, so the two uses cannot silently share the C1 domain.
   `c1_does_not_imply_script_commitment_injectivity` proves that C1 does not
   imply injectivity of the tagged commitment either; the closure is the
   explicit pair admission, never global or 71-byte injectivity.
   `scriptCommitment_pair_admission_satisfiable` shows the tagged pair
   admission is satisfiable, so the closure is not vacuous.

## What is *not* claimed

* No SHA-256 implementation, no computational collision-finding game, and no
  global or 71-byte injectivity.  `CollisionResistantOn H 71` is impossible
  for any 32-byte-output hash by pigeonhole and is not assumed anywhere.
* `c1CollisionModel` is an *admissible model*, not FIPS 180-4 SHA-256.  Its
  role is exactly to prove that the C1 *axiomatization* is insufficient; the
  result is a faithfulness statement about the model boundary, not a claim
  that real SHA-256 has a known collision.
* All existing finite `CollisionFreeOn` admissions
  (`FundingScriptTargets.fundingScriptPubKey_binds_witnessScript`,
  `FundingLinkTargets.constructed_binds_twoOfTwo`, and their companions) are
  imported and left unchanged; this module is additive.
-/

import LnLean.Proofs.Bitcoin.FundingLinkTargets
import LnLean.Proofs.Bitcoin.FundingScriptTargets
import LnLean.Crypto.Hash

namespace LnLean.Proofs.WaveH.H34

set_option autoImplicit false

open LnLean
open LnLean.Bitcoin
open LnLean.Crypto
open LnLean.Proofs.Bitcoin.FundingScriptTargets

/-! ## Concrete 33-byte keys and 71-byte BOLT 3 scripts -/

private def zeros32 : ByteArray :=
  ByteArray.mk (List.replicate 32 (0 : UInt8)).toArray

private theorem zeros32_size : zeros32.size = 32 := by
  simp [zeros32, ByteArray.size]

private def zeros (n : Nat) : ByteArray :=
  ByteArray.mk (List.replicate n (0 : UInt8)).toArray

private theorem zeros_size (n : Nat) : (zeros n).size = n := by
  simp [zeros, ByteArray.size]

private def keyBytes (b : UInt8) : ByteArray :=
  ByteArray.mk (List.replicate 33 b).toArray

private def pub (b : UInt8) : PubKey := ⟨keyBytes b⟩

private theorem keyBytes_size (b : UInt8) : (keyBytes b).size = 33 := by
  simp [keyBytes, ByteArray.size]

private theorem pub_valid (b : UInt8) : (pub b).Valid := keyBytes_size b

private theorem keyBytes_zero : (keyBytes 0)[0]? = some (0 : UInt8) := by
  simp only [keyBytes]
  decide

private theorem keyBytes_one : (keyBytes 1)[0]? = some (1 : UInt8) := by
  simp only [keyBytes]
  decide

/-! ## Byte-index helpers for the 2-of-2 template -/

private theorem getElem?_append_lt (a b : ByteArray) (i : Nat) (h : i < a.size) :
    (a ++ b)[i]? = a[i]? := by
  rw [show (a ++ b)[i]? = (a ++ b).data[i]? from rfl,
      ByteArray.data_append, Array.getElem?_append,
      ite_eq_left (by simpa using h)]
  rw [show a[i]? = a.data[i]? from rfl]

private theorem getElem?_append_ge (a b : ByteArray) (i : Nat) (h : a.size ≤ i) :
    (a ++ b)[i]? = b[i - a.size]? := by
  rw [show (a ++ b)[i]? = (a ++ b).data[i]? from rfl,
      ByteArray.data_append, Array.getElem?_append,
      ite_eq_right (by simpa using h)]
  rw [show b[i - a.size]? = b.data[i - a.size]? from rfl]
  rfl

/-- Byte 2 of the BOLT 3 template is the first byte of the first pushed key:
`OP_2`, push length `0x21`, then the key body. -/
private theorem twoOfTwo_getElem_two (a b : PubKey) (ha : a.bytes.size = 33) :
    (TwoOfTwoScriptBytes a b)[2]? = a.bytes[0]? := by
  simp only [TwoOfTwoScriptBytes, pushData]
  rw [getElem?_append_lt _ (ByteArray.empty.push OP_CHECKMULTISIG) 2 (by
    simp only [ByteArray.size_append, ByteArray.size_push, ByteArray.size_empty,
      ha]
    omega)]
  rw [getElem?_append_lt _ (ByteArray.empty.push 0x52) 2 (by
    simp only [ByteArray.size_append, ByteArray.size_push, ByteArray.size_empty,
      ha]
    omega)]
  rw [getElem?_append_lt _ (ByteArray.empty.push b.bytes.size.toUInt8 ++ b.bytes) 2
    (by
      simp only [ByteArray.size_append, ByteArray.size_push, ByteArray.size_empty,
        ha]
      omega)]
  rw [getElem?_append_ge (ByteArray.empty.push 0x52) _ 2 (by
    simp only [ByteArray.size_push, ByteArray.size_empty]
    omega)]
  rw [show 2 - (ByteArray.empty.push (0x52 : UInt8)).size = 1 from by simp]
  rw [getElem?_append_ge (ByteArray.empty.push a.bytes.size.toUInt8) a.bytes 1 (by
    simp only [ByteArray.size_push, ByteArray.size_empty]
    omega)]
  rw [show 1 - (ByteArray.empty.push a.bytes.size.toUInt8).size = 0 from by simp]

private theorem script0_size : (TwoOfTwoScriptBytes (pub 0) (pub 0)).size = 71 :=
  TwoOfTwoScriptBytes_size _ _ (keyBytes_size 0) (keyBytes_size 0)

private theorem script1_size : (TwoOfTwoScriptBytes (pub 1) (pub 1)).size = 71 :=
  TwoOfTwoScriptBytes_size _ _ (keyBytes_size 1) (keyBytes_size 1)

/-- Two distinct 71-byte BOLT 3 witness scripts: they differ at byte 2, the
first byte of the first pushed funding key. -/
private theorem script0_ne_script1 :
    TwoOfTwoScriptBytes (pub 0) (pub 0) ≠
      TwoOfTwoScriptBytes (pub 1) (pub 1) := by
  intro h
  have h0 : (TwoOfTwoScriptBytes (pub 0) (pub 0))[2]? = some (0 : UInt8) := by
    have h := twoOfTwo_getElem_two (pub 0) (pub 0) (keyBytes_size 0)
    rw [h]
    exact keyBytes_zero
  have h1 : (TwoOfTwoScriptBytes (pub 1) (pub 1))[2]? = some (1 : UInt8) := by
    have h := twoOfTwo_getElem_two (pub 1) (pub 1) (keyBytes_size 1)
    rw [h]
    exact keyBytes_one
  rw [h] at h0
  rw [h1] at h0
  exact absurd (Option.some.inj h0) (by decide)

/-! ## A full `PrimitiveModel` satisfying C1 -/

/-- `c1OnlyHash` maps every non-32-byte input to the all-zero 32-byte string. -/
private theorem c1OnlyHash_eq_zeros32_of_ne {x : ByteArray} (h : x.size ≠ 32) :
    c1OnlyHash x = zeros32 := by
  unfold c1OnlyHash zeros32
  rw [ite_eq_right h]

/-- **A complete primitive model whose SHA-256 satisfies C1 and collides on
71-byte inputs.**  The signature/verification, AEAD, KDF, ECDH and HMAC fields
are instantiated by trivial inhabiting functions; only the `sha256` field is
load-bearing for this lane.  This lifts the bare-function counterexample
`FundingScriptTargets.c1_32_does_not_bind_funding_witnessScripts` to the
`PrimitiveModel` boundary, which is where C1 is actually assumed. -/
def c1CollisionModel : PrimitiveModel where
  sha256 := c1OnlyHash
  hash160 := fun _ => zeros 20
  ecdsaVerify := fun _ _ _ => false
  schnorrVerify := fun _ _ _ => false
  ecdh := fun _ _ => zeros 32
  hkdf := fun _ _ _ => zeros 32
  aeadSeal := fun _ _ p => p
  aeadOpen := fun _ _ c => some c
  hmacSha256 := fun _ _ => zeros 32
  sha256_size := c1OnlyHash_size
  hash160_size := fun _ => zeros_size 20
  hmac_size := fun _ _ => zeros_size 32
  sha256_collisionResistant := c1OnlyHash_collisionResistant
  ecdsa_eufCma := by
    intro _pk _m1 _m2 _s h
    simp at h
  schnorr_eufCma := by
    intro _pk _m1 _m2 _s h
    simp at h
  aead_indCca := by
    refine ⟨?_, ?_⟩
    · intro _k _n _p
      rfl
    · intro _k _n c _p h
      exact (Option.some.inj h).symm

/-- The C1 field of the counterexample model holds. -/
theorem c1CollisionModel_collisionResistant :
    CollisionResistant c1CollisionModel.sha256 :=
  c1OnlyHash_collisionResistant

/-- The `sha256` field of the counterexample model is exactly `c1OnlyHash`. -/
theorem c1CollisionModel_sha256 : c1CollisionModel.sha256 = c1OnlyHash := rfl

/-- The width field of the counterexample model holds. -/
theorem c1CollisionModel_sha256_size (b : ByteArray) :
    (c1CollisionModel.sha256 b).size = 32 :=
  c1OnlyHash_size b

/-- **`L1-05`, model-level form.**  There is a `PrimitiveModel` satisfying C1
(and the 32-byte width field) with two distinct 71-byte BOLT 3 funding witness
scripts that have the same SHA-256 image.  This is the precise sense in which
C1 does not bind 71-byte scripts: the counterexample is fully inside the model,
not a bare-function artifact. -/
theorem c1_model_collides_on_71_byte_funding_scripts :
    ∃ (M : PrimitiveModel) (x y : ByteArray),
      CollisionResistant M.sha256 ∧
      x.size = 71 ∧ y.size = 71 ∧ x ≠ y ∧ M.sha256 x = M.sha256 y := by
  refine ⟨c1CollisionModel, TwoOfTwoScriptBytes (pub 0) (pub 0),
    TwoOfTwoScriptBytes (pub 1) (pub 1), c1OnlyHash_collisionResistant,
    script0_size, script1_size, script0_ne_script1, ?_⟩
  rw [c1CollisionModel_sha256]
  rw [c1OnlyHash_eq_zeros32_of_ne (by rw [script0_size]; decide),
    c1OnlyHash_eq_zeros32_of_ne (by rw [script1_size]; decide)]

/-- **No `PrimitiveModel` forces 71-byte injectivity.**  The universal
statement "every model's SHA-256 is injective on 71-byte strings" is false, by
the counterexample model above.  This is the formal boundary that forbids
deriving script binding from the C1 field. -/
theorem no_primitive_model_binds_71_byte_scripts :
    ¬ ∀ (M : PrimitiveModel) (x y : ByteArray),
        x.size = 71 → y.size = 71 → M.sha256 x = M.sha256 y → x = y := by
  intro h
  obtain ⟨M, x, y, -, hx, hy, hne, hcol⟩ :=
    c1_model_collides_on_71_byte_funding_scripts
  exact hne (h M x y hx hy hcol)

/-! ## The funding records themselves -/

/-- Funding parameters with one repeated 33-byte key and the all-zero P2WSH
program.  The witnessed program is the BOLT 3 template over `(pub b, pub b)`. -/
private def params (b : UInt8) : FundingParams :=
  { fundingSatoshis := 0
    pushMsat := ⟨0⟩
    localFundingKey := pub b
    remoteFundingKey := pub b
    witnessScriptHash := zeros32
    temporaryChannelId := ⟨⟨ByteArray.empty⟩⟩ }

private theorem params_witnessScript (b : UInt8) :
    (params b).witnessScript.bytes = TwoOfTwoScriptBytes (pub b) (pub b) := by
  rw [witnessScript_eq_TwoOfTwoScriptBytes]
  simp [params, LnLean.Proofs.Bitcoin.FundingProps.orderedFundingKeys_self]

private theorem params_witnessScript_size (b : UInt8) :
    (params b).witnessScript.bytes.size = 71 := by
  rw [params_witnessScript]
  exact TwoOfTwoScriptBytes_size _ _ (keyBytes_size b) (keyBytes_size b)

private theorem params_wellFormed (b : UInt8) : (params b).WellFormed := by
  unfold FundingParams.WellFormed
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [params]
  · simp [params, Bitcoin.Data.MAX_MONEY, Bitcoin.Data.COIN]
  · change (pub b).bytes.size = 33
    exact keyBytes_size b
  · change (pub b).bytes.size = 33
    exact keyBytes_size b
  · exact zeros32_size
  · simp [params]

/-- The all-zero program is `c1OnlyHash` of the 71-byte witness script, so the
counterexample records are hash-linked in the usual sense. -/
private theorem params_hash_linked (b : UInt8) :
    FundingScriptHashLinked c1OnlyHash (params b) := by
  unfold FundingScriptHashLinked
  show zeros32 = c1OnlyHash (params b).witnessScript.bytes
  rw [c1OnlyHash_eq_zeros32_of_ne (by
    rw [params_witnessScript_size]; decide)]

/-- **`L1-05`, funding-output form.**  In a `PrimitiveModel` satisfying C1, two
well-formed funding parameter sets have distinct 71-byte 2-of-2 witness scripts
and yet the *same* P2WSH `scriptPubKey`.  Both records are hash-linked, so this
is exactly the failure of "the funding output binds the revealed 71-byte
script".  It is a real collision in the model, not a re-statement of C1's
domain restriction. -/
theorem c1_model_does_not_bind_funding_witnessScripts :
    ∃ (M : PrimitiveModel) (p q : FundingParams),
      p.WellFormed ∧ q.WellFormed ∧
      p.witnessScript.bytes.size = 71 ∧
      q.witnessScript.bytes.size = 71 ∧
      p.witnessScript.bytes ≠ q.witnessScript.bytes ∧
      FundingScriptHashLinked M.sha256 p ∧
      FundingScriptHashLinked M.sha256 q ∧
      p.fundingScriptPubKey = q.fundingScriptPubKey := by
  refine ⟨c1CollisionModel, params 0, params 1, params_wellFormed 0,
    params_wellFormed 1, params_witnessScript_size 0,
    params_witnessScript_size 1, ?_, ?_, ?_, ?_⟩
  · rw [params_witnessScript 0, params_witnessScript 1]
    exact script0_ne_script1
  · simpa [c1CollisionModel] using params_hash_linked 0
  · simpa [c1CollisionModel] using params_hash_linked 1
  · rfl

/-- Corollary at the raw hash level: the C1 model has a 71-byte collision, so
the collision is not an artifact of the funding record's free program field. -/
theorem c1_model_sha256_collides_on_funding_scripts :
    ∃ x y : ByteArray,
      x.size = 71 ∧ y.size = 71 ∧ x ≠ y ∧
      c1CollisionModel.sha256 x = c1CollisionModel.sha256 y := by
  refine ⟨TwoOfTwoScriptBytes (pub 0) (pub 0),
    TwoOfTwoScriptBytes (pub 1) (pub 1), script0_size, script1_size,
    script0_ne_script1, ?_⟩
  rw [c1CollisionModel_sha256]
  rw [c1OnlyHash_eq_zeros32_of_ne (by rw [script0_size]; decide),
    c1OnlyHash_eq_zeros32_of_ne (by rw [script1_size]; decide)]

/-! ## A domain-separated script commitment -/

/-- A fixed 32-byte domain tag for funding-script commitments.  BOLT 3 has no
domain separator for the funding witness-script hash; this is a *model-side*
construction for the intended closure, not a wire change. -/
def scriptDomainTag : ByteArray :=
  ByteArray.mk (List.replicate 32 (0x01 : UInt8)).toArray

theorem scriptDomainTag_size : scriptDomainTag.size = 32 := by
  simp [scriptDomainTag, ByteArray.size]

/-- The domain-separated funding-script commitment:
`H (scriptDomainTag ++ scriptBytes)`.  Instantiating the existing construction
at this function costs nothing, since `FundingNegotiation.toFundingParams` is
already parameterized by the hash. -/
def scriptCommitment (H : ByteArray → ByteArray) (scriptBytes : ByteArray) :
    ByteArray :=
  H (scriptDomainTag ++ scriptBytes)

/-- The tagged preimage of a 71-byte script is 103 bytes, never 32. -/
theorem scriptCommitment_preimage_size (s : ByteArray) :
    (scriptDomainTag ++ s).size = 32 + s.size := by
  simp [ByteArray.size_append, scriptDomainTag_size]

/-- **Structural domain separation.**  A tagged funding-script preimage is
never a 32-byte payment preimage, so the C1 domain and the script-commitment
domain cannot silently coincide.  (This does not claim the *outputs* are
separated without a cryptographic assumption; it separates the preimage
spaces.) -/
theorem scriptCommitment_preimage_ne_payment_preimage
    (s : ByteArray) (pre : Preimage) (hs : s.size = 71) (hpre : pre.Valid) :
    scriptDomainTag ++ s ≠ pre.bytes := by
  intro h
  have hsz := congrArg ByteArray.size h
  rw [scriptCommitment_preimage_size, hs] at hsz
  have hp : pre.bytes.size = 32 := hpre
  rw [hp] at hsz
  omega

/-- The hash link is definitional for tagged constructed parameters: the
existing handshake construction already accepts the separated commitment. -/
theorem scriptCommitment_hash_linked (H : ByteArray → ByteArray)
    (n : FundingNegotiation) :
    FundingScriptHashLinked (scriptCommitment H)
      (n.toFundingParams (scriptCommitment H)) :=
  LnLean.Proofs.Bitcoin.FundingLinkTargets.toFundingParams_hash_linked
    (scriptCommitment H) n

/-- **Closure of the intended construction (hash-level form).**  If the stored
program is the domain-separated commitment of the witness script, the revealed
output commits to the separated commitment of `revealed`, and `H` is
collision-free on the *tagged* pair, then the revealed script is the funding
witness script.  The cryptographic hypothesis is exactly the finite pair
admission the tree already uses, instantiated at the tagged preimages; no
global or 71-byte injectivity is assumed. -/
theorem scriptCommitment_binds_witnessScript
    (H : ByteArray → ByteArray) (p : FundingParams) (revealed : ByteArray)
    (hlink : FundingScriptHashLinked (scriptCommitment H) p)
    (hrev : p.fundingScriptPubKey = p2wsh (scriptCommitment H revealed))
    (hpair : CollisionFreeOn H (scriptDomainTag ++ revealed)
      (scriptDomainTag ++ p.witnessScript.bytes)) :
    revealed = p.witnessScript.bytes :=
  fundingScriptPubKey_binds_witnessScript
    (scriptCommitment H) p hlink revealed hrev (by
      intro h
      have h' : H (scriptDomainTag ++ revealed) =
          H (scriptDomainTag ++ p.witnessScript.bytes) := h
      exact append_left_cancel (hpair h'))

/-- **Closure of the intended construction at the handshake boundary.**  The
constructed parameters use the separated commitment by definition, and the
existing `FundingLinkTargets.constructed_binds_twoOfTwo` theorem yields the
2-of-2 witness-script shape and the 71-byte width under the tagged finite pair
admission. -/
theorem scriptCommitment_binds_twoOfTwo
    (H : ByteArray → ByteArray) (n : FundingNegotiation)
    (hwf : (n.toFundingParams (scriptCommitment H)).WellFormed)
    (revealed : ByteArray)
    (hrev : (n.toFundingParams (scriptCommitment H)).fundingScriptPubKey =
      p2wsh (scriptCommitment H revealed))
    (hpair : CollisionFreeOn H (scriptDomainTag ++ revealed)
      (scriptDomainTag ++
        (n.toFundingParams (scriptCommitment H)).witnessScript.bytes)) :
    IsTwoOfTwoScript
        (n.toFundingParams (scriptCommitment H)).localFundingKey
        (n.toFundingParams (scriptCommitment H)).remoteFundingKey revealed ∧
      revealed.size = 71 :=
  LnLean.Proofs.Bitcoin.FundingLinkTargets.constructed_binds_twoOfTwo
    (scriptCommitment H) n hwf revealed hrev (by
      intro h
      have h' : H (scriptDomainTag ++ revealed) =
          H (scriptDomainTag ++
            (n.toFundingParams (scriptCommitment H)).witnessScript.bytes) := h
      exact append_left_cancel (hpair h'))

/-- **Tagging alone does not create injectivity.**  C1 does not imply
injectivity of the domain-separated commitment on 71-byte scripts either; the
counterexample model maps every 103-byte tagged preimage to zero.  The closure
above therefore rests on the explicit pair admission. -/
theorem c1_does_not_imply_script_commitment_injectivity :
    ¬ ∀ (M : PrimitiveModel) (x y : ByteArray),
        x.size = 71 → y.size = 71 →
        M.sha256 (scriptDomainTag ++ x) = M.sha256 (scriptDomainTag ++ y) →
        x = y := by
  intro h
  exact script0_ne_script1
    (h c1CollisionModel _ _ script0_size script1_size (by
      rw [c1CollisionModel_sha256]
      rw [c1OnlyHash_eq_zeros32_of_ne (by
          rw [scriptCommitment_preimage_size, script0_size]; decide),
        c1OnlyHash_eq_zeros32_of_ne (by
          rw [scriptCommitment_preimage_size, script1_size]; decide)]))

/-- **Non-vacuity of the tagged pair admission.**  There is a 32-byte-output
hash that is collision-free on the tagged pair of the two concrete scripts, so
the closure theorem's cryptographic hypothesis is satisfiable. -/
theorem scriptCommitment_pair_admission_satisfiable :
    ∃ H : ByteArray → ByteArray,
      (∀ b : ByteArray, (H b).size = 32) ∧
      CollisionFreeOn H
        (scriptDomainTag ++ TwoOfTwoScriptBytes (pub 0) (pub 0))
        (scriptDomainTag ++ TwoOfTwoScriptBytes (pub 1) (pub 1)) := by
  refine ⟨demoHash (scriptDomainTag ++ TwoOfTwoScriptBytes (pub 0) (pub 0)),
    fun b => demoHash_size _ b, ?_⟩
  exact demoHash_collisionFree _ _ (by
    intro h
    exact script0_ne_script1 (append_left_cancel h).symm)

/-! ## Boundary summary -/

/-- The two ingredients are independent, stated as one bundle: in the C1 model
the 32-byte payment domain behaves as C1 requires (the field itself), while the
71-byte funding-script domain already collides.  This is the exact `L1-05`
boundary: payment-hash binding and funding-script binding are different
assumptions. -/
theorem payment_binding_and_script_binding_are_independent :
    CollisionResistant c1CollisionModel.sha256 ∧
      (∃ x y : ByteArray,
        x.size = 71 ∧ y.size = 71 ∧ x ≠ y ∧
        c1CollisionModel.sha256 x = c1CollisionModel.sha256 y) ∧
      (∃ H : ByteArray → ByteArray,
        (∀ b : ByteArray, (H b).size = 32) ∧
        CollisionFreeOn H
          (scriptDomainTag ++ TwoOfTwoScriptBytes (pub 0) (pub 0))
          (scriptDomainTag ++ TwoOfTwoScriptBytes (pub 1) (pub 1))) :=
  ⟨c1CollisionModel_collisionResistant, c1_model_sha256_collides_on_funding_scripts,
    scriptCommitment_pair_admission_satisfiable⟩

end LnLean.Proofs.WaveH.H34
