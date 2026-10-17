/-
# LnLean.Proofs.Crypto.Sha256Props

**English claim.**  This module states and proves the *structural* laws of the
hash interface in `LnLean.Crypto.Model` / `LnLean.Crypto.Hash`:

1. `sha256` returns exactly 32 bytes and `hash160` exactly 20 bytes for every
   input (BOLT 1 fundamental types, BOLT 3 P2WPKH/P2WSH scripts);
2. hashing is deterministic and extensional on `ByteArray`: equal inputs give
   equal digests (no randomness is modelled);
3. for the modelled hash lock, `opensTo M ph pre` is equivalent to
   `M.sha256 pre.bytes = ph.bytes`; the `digest32` normalisation is the
   identity on the 32-byte image produced by `sha256_size`, so the forward
   direction is immediate from the definition;
4. collision resistance and preimage resistance are `Prop`-valued *fields* of
   `PrimitiveModel`, never axioms; every cryptographic conclusion is a
   conditional theorem naming the field as a hypothesis;
5. a payment hash commits to a preimage only under preimage resistance, in the
   global form (arbitrary preimages) and in the hash-lock form;
6. the BIP 340 tagged-hash encoding is domain separating *structurally*: the
   tag prefix `sha256(tag) || sha256(tag)` determines the tag once SHA-256 is
   injective.  The encoding-level statement (different hashed tags give
   different prefixes) is proved without any cryptographic assumption; at the
   digest level, equal tagged hashes of distinct tags yield an explicit
   SHA-256 collision witness rather than assuming global injectivity.

**BOLT sections.**
* BOLT 1 §Fundamental Types: `sha256` is a 32-byte SHA2-256 hash
  (`refs/bolts/01-messaging.md:254`).
* BOLT 2 §Adding an HTLC: `update_add_htlc` carries a 32-byte `payment_hash`
  (`refs/bolts/02-peer-protocol.md:2788`).
* BOLT 2 §Removing an HTLC: `update_fulfill_htlc` carries a 32-byte
  `payment_preimage` (`refs/bolts/02-peer-protocol.md:2925`) and the receiver
  rejects it unless it hashes to the HTLC's `payment_hash`
  (`refs/bolts/02-peer-protocol.md:3004-3005`).
* BOLT 3 §Deriving Keys: per-commitment key tweaks are SHA-256 digests
  (`refs/bolts/03-transactions.md:775-786`).
* BOLT PR "simple taproot" §Tagged Hash (BIP 340):
  `tagged_hash(tag, msg) = SHA256(SHA256(tag) || SHA256(tag) || msg)`
  (`refs/bolts/bolt-simple-taproot.md:140`).

**rust-lightning anchors (commit `fe49009`, local clone `refs/rust-lightning`).**
* `lightning-types/src/payment.rs:70-73` — `From<PaymentPreimage> for
  PaymentHash` is `Sha256::hash(preimage.0).to_byte_array()`.
* `lightning/src/ln/msgs.rs:746` — `UpdateAddHTLC.payment_hash` is a
  `PaymentHash`.
* `lightning/src/ln/msgs.rs:3553-3557` — `update_add_htlc` writes the
  `payment_hash` field.
* `lightning/src/ln/msgs.rs:3503-3506` — `update_fulfill_htlc` carries the
  `payment_preimage` field.
* `lightning/src/offers/merkle.rs:34-76` — `TaggedHash`, including
  `sha256::Hash::hash(tag.as_bytes())` and the BIP 340 `tagged_hash` call.
  (`util/sha256.rs` does not exist at this commit; the pinned
  implementation uses `bitcoin_hashes::sha256::Hash` throughout, as cited
  above.)

**Not modelled.**  The SHA-256 compression function, message schedule,
padding, concrete digest values and test vectors; RIPEMD160 internals;
length-extension behaviour; constant-time execution; computational security
games and reductions.  In particular, `CollisionResistant` and
`PreimageResistant` are exact algebraic over-approximations (injectivity), not
complexity-theoretic definitions, and no theorem below asserts a concrete hash
value or a hardness claim.

**Known interface defect (recorded, not repaired here).**  `PreimageResistant`
in `LnLean.Crypto.Model` is injectivity on *all* `ByteArray`, while
`sha256_size` forces every image to be 32 bytes.  A function from the (vast)
space of byte arrays into the finite set of 32-byte strings cannot be
injective, so the global field is not simultaneously satisfiable with
`sha256_size`.  This module makes that gap explicit as the proved theorem
`LN-CR-007` (`no_injective_hash_into_32_bytes`) and uses the field only in
explicitly conditional theorems.  The consistent hypothesis for Lightning's
32-byte payment preimages is `CollisionResistant`, already used by
`LnLean.Crypto.Hash.preimage_unique` and `paymentHash_commits`.  We do **not**
derive `False` from the defect and we do not weaken any stated theorem to hide
it; `LnLean/Crypto/Model.lean` is owned by another agent and is untouched.
-/

import LnLean.Basic.Core
import LnLean.Crypto.Model
import LnLean.Crypto.Hash

namespace LnLean.Proofs.Crypto

set_option autoImplicit false

open LnLean LnLean.Crypto

/-! ## 1. Byte widths: the BOLT 1 wire types -/

/-- `sha256` produces exactly 32 bytes on every input (BOLT 1 `sha256`). -/
theorem sha256_output_width (M : PrimitiveModel) (b : ByteArray) :
    (M.sha256 b).size = 32 :=
  M.sha256_size b

/-- `hash160` produces exactly 20 bytes on every input (BOLT 3 P2WPKH). -/
theorem hash160_output_width (M : PrimitiveModel) (b : ByteArray) :
    (M.hash160 b).size = 20 :=
  M.hash160_size b

/-- The total 32-byte normalisation `digest32` always produces 32 bytes, even
on malformed input. -/
theorem digest32_output_width (b : ByteArray) :
    (PrimitiveModel.digest32 b).size = 32 :=
  PrimitiveModel.digest32_size b

/-- A payment hash built by `paymentHashOf` is a 32-byte value. -/
theorem paymentHash_output_width (M : PrimitiveModel) (pre : Preimage) :
    (M.paymentHashOf pre).bytes.size = 32 :=
  M.paymentHashOf_valid pre

/-! ## 2. Determinism and extensionality -/

/-- Hashing is a function of the byte array: equal inputs have equal SHA-256
digests.  No randomness or oracle is modelled. -/
theorem sha256_extensional (M : PrimitiveModel) {x y : ByteArray} (h : x = y) :
    M.sha256 x = M.sha256 y :=
  congrArg M.sha256 h

/-- HASH160 is likewise deterministic and extensional. -/
theorem hash160_extensional (M : PrimitiveModel) {x y : ByteArray} (h : x = y) :
    M.hash160 x = M.hash160 y :=
  congrArg M.hash160 h

/-- Determinism stated as a two-argument function equality. -/
theorem sha256_deterministic (M : PrimitiveModel) (b : ByteArray) :
    M.sha256 b = M.sha256 b :=
  rfl

/-! ## 3. Hash locks are definitionally SHA-256 equality -/

/-- Because `sha256` always has the wire width 32, `digest32` is the identity
on its image.  Hence the hash-lock predicate is plain digest equality; no
cryptographic assumption is involved. -/
theorem opensTo_iff_sha256_eq (M : PrimitiveModel) (ph : PaymentHash)
    (pre : Preimage) :
    opensTo M ph pre ↔ M.sha256 pre.bytes = ph.bytes := by
  unfold opensTo
  rw [PrimitiveModel.digest32_of_size (M.sha256_size pre.bytes)]

/-- A satisfied hash lock exposes the SHA-256 preimage equation (BOLT 2
§Removing an HTLC, `refs/bolts/02-peer-protocol.md:3004-3005`). -/
theorem opensTo_implies_sha256 (M : PrimitiveModel) {ph : PaymentHash}
    {pre : Preimage} (h : opensTo M ph pre) :
    M.sha256 pre.bytes = ph.bytes :=
  (opensTo_iff_sha256_eq M ph pre).mp h

/-- Conversely, the SHA-256 equation opens the hash lock. -/
theorem sha256_eq_implies_opensTo (M : PrimitiveModel) {ph : PaymentHash}
    {pre : Preimage} (h : M.sha256 pre.bytes = ph.bytes) :
    opensTo M ph pre :=
  (opensTo_iff_sha256_eq M ph pre).mpr h

/-! ## 4. Cryptographic assumptions are structure fields, not axioms -/

/-- Collision resistance is obtained by projecting the `PrimitiveModel`
field `sha256_collisionResistant`.  This is an assumption supplied by the
interface, not an axiom of this module. -/
theorem collisionResistant_field (M : PrimitiveModel) :
    CollisionResistant M.sha256 :=
  M.sha256_collisionResistant

/-- Preimage resistance is likewise a projected `Prop` field. -/
theorem preimageResistant_field (M : PrimitiveModel) :
    PreimageResistant M.sha256 :=
  M.sha256_preimageResistant

/-- Global injectivity is stronger than collision resistance on the 32-byte
inputs: every theorem that only needs collision resistance can be derived from
the (stronger) preimage-resistance hypothesis.  The converse does not hold. -/
theorem collisionResistant_of_preimageResistant {H : ByteArray → ByteArray}
    (h : PreimageResistant H) : CollisionResistant H :=
  fun x y _ _ hxy => h x y hxy

/-! ## 5. Payment-hash commitment is conditional -/

/-- **Payment-hash commitment, global form.**  Under the interface's
preimage-resistance assumption, two preimages (not necessarily 32 bytes) with
the same payment hash are equal.  This is the formal content of "the payment
hash commits to the preimage"; no computational hardness is proved.  See the
module note: this hypothesis is stronger than the model can consistently
supply together with `sha256_size` (theorem `LN-CR-007`). -/
theorem paymentHash_commitment_of_preimageResistant (M : PrimitiveModel)
    (h : PreimageResistant M.sha256) {p q : Preimage}
    (hph : M.paymentHashOf p = M.paymentHashOf q) : p = q := by
  have hd : PrimitiveModel.digest32 (M.sha256 p.bytes) =
      PrimitiveModel.digest32 (M.sha256 q.bytes) :=
    congrArg PaymentHash.bytes hph
  have hp : PrimitiveModel.digest32 (M.sha256 p.bytes) = M.sha256 p.bytes :=
    PrimitiveModel.digest32_of_size (M.sha256_size p.bytes)
  have hq : PrimitiveModel.digest32 (M.sha256 q.bytes) = M.sha256 q.bytes :=
    PrimitiveModel.digest32_of_size (M.sha256_size q.bytes)
  have hsha : M.sha256 p.bytes = M.sha256 q.bytes := by
    rw [← hp, ← hq]
    exact hd
  have hbytes : p.bytes = q.bytes := h p.bytes q.bytes hsha
  cases p with
  | mk pb =>
    cases q with
    | mk qb =>
      simp only at hbytes
      rw [hbytes]

/-- **Hash-lock uniqueness.**  Two preimages that open the same payment hash
are equal under preimage resistance.  This is the commitment property consumed
by HTLC fulfilment (BOLT 2 §Removing an HTLC). -/
theorem opensTo_unique_of_preimageResistant (M : PrimitiveModel)
    (h : PreimageResistant M.sha256) {ph : PaymentHash} {p q : Preimage}
    (hp : opensTo M ph p) (hq : opensTo M ph q) : p = q := by
  have hp' : M.sha256 p.bytes = ph.bytes := opensTo_implies_sha256 M hp
  have hq' : M.sha256 q.bytes = ph.bytes := opensTo_implies_sha256 M hq
  have hsha : M.sha256 p.bytes = M.sha256 q.bytes := by
    rw [hp', hq']
  have hbytes : p.bytes = q.bytes := h p.bytes q.bytes hsha
  cases p with
  | mk pb =>
    cases q with
    | mk qb =>
      simp only at hbytes
      rw [hbytes]

/-! ## 6. HASH160 as a composition (assumption C2)

`PrimitiveModel` exposes `hash160_size` but has no collision-resistance field
for HASH160, and no RIPEMD160 operation.  The next definition and theorem
state the composition explicitly: if HASH160 decomposes as RIPEMD160 ∘
SHA-256 and both components are collision resistant on the relevant domains,
then HASH160 is collision resistant.  This is a conditional derivation, not a
new axiom, and it records the missing C2 field for the integrator. -/

/-- `hash160` decomposes as `ripemd160 ∘ sha256` for the supplied RIPEMD160
stand-in.  `PrimitiveModel` itself does not provide `ripemd160`, so this is a
hypothesis of the composition theorem below. -/
def Hash160Decomposition (M : PrimitiveModel)
    (ripemd160 : ByteArray → ByteArray) : Prop :=
  ∀ b : ByteArray, M.hash160 b = ripemd160 (M.sha256 b)

/-- Collision resistance of HASH160 follows from collision resistance of its
two components on the appropriate domains (32-byte SHA-256 output for
RIPEMD160, 32-byte input for SHA-256). -/
theorem hash160_collisionResistant_of_components (M : PrimitiveModel)
    (ripemd160 : ByteArray → ByteArray)
    (hdecomp : Hash160Decomposition M ripemd160)
    (hripemd : CollisionResistant ripemd160)
    (hsha : CollisionResistant M.sha256) {x y : ByteArray}
    (hx : x.size = 32) (hy : y.size = 32)
    (heq : M.hash160 x = M.hash160 y) : x = y := by
  have h1 : ripemd160 (M.sha256 x) = ripemd160 (M.sha256 y) := by
    simpa only [hdecomp x, hdecomp y] using heq
  have hs : M.sha256 x = M.sha256 y :=
    hripemd (M.sha256 x) (M.sha256 y)
      (M.sha256_size x) (M.sha256_size y) h1
  exact hsha x y hx hy hs

/-! ## 7. Tagged hashes and structural domain separation -/

/-- The BIP 340 tag prefix `SHA256(tag) || SHA256(tag)`
(`refs/bolts/bolt-simple-taproot.md:140`,
`refs/rust-lightning/lightning/src/offers/merkle.rs:73-76`). -/
def tagPrefix (M : PrimitiveModel) (tag : ByteArray) : ByteArray :=
  M.sha256 tag ++ M.sha256 tag

/-- The BIP 340 tagged hash `SHA256(SHA256(tag) || SHA256(tag) || msg)`. -/
def taggedHashSha256 (M : PrimitiveModel) (tag msg : ByteArray) : ByteArray :=
  M.sha256 (tagPrefix M tag ++ msg)

/-- The tag prefix is 64 bytes: two 32-byte SHA-256 outputs.  This is a
structural width fact, proved without any cryptographic assumption. -/
theorem tagPrefix_width (M : PrimitiveModel) (tag : ByteArray) :
    (tagPrefix M tag).size = 64 := by
  unfold tagPrefix
  rw [ByteArray.size_append, M.sha256_size]

/-- A tagged hash is a 32-byte digest, like any SHA-256 image. -/
theorem taggedHash_output_width (M : PrimitiveModel) (tag msg : ByteArray) :
    (taggedHashSha256 M tag msg).size = 32 :=
  M.sha256_size _

/-- Cancellation for two identical copies: if `a ++ a = b ++ b` and the two
arrays have the same size, then `a = b`.  This is pure `ByteArray`/`List`
structure, used to extract the tag hash from a tag prefix. -/
theorem append_self_cancel {a b : ByteArray} (hlen : a.size = b.size)
    (h : a ++ a = b ++ b) : a = b := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  have hlist : a.data.toList ++ a.data.toList = b.data.toList ++ b.data.toList := by
    simpa [ByteArray.data_append, Array.toList_append] using
      congrArg (fun x : ByteArray => x.data.toList) h
  have hlen' : a.data.toList.length = b.data.toList.length := by
    simpa using hlen
  exact (List.append_inj hlist hlen').1

/-- **Structural domain separation.**  If two tags have different SHA-256
images, their BIP 340 prefixes differ.  No collision-resistance or
preimage-resistance assumption is used: this is cancellation on the
`ByteArray` encoding. -/
theorem tagPrefix_separates_hashed_tags (M : PrimitiveModel) {t₁ t₂ : ByteArray}
    (h : M.sha256 t₁ ≠ M.sha256 t₂) : tagPrefix M t₁ ≠ tagPrefix M t₂ := by
  intro heq
  apply h
  exact append_self_cancel (by rw [M.sha256_size, M.sha256_size])
    (by simpa [tagPrefix] using heq)

/-- **Digest-level domain separation as a reduction.**  If two distinct tags
produce the same tagged digest for the same message, there is an explicit
SHA-256 collision: either on the tag images themselves, or on the two tagged
inputs.  This is the exact cryptographic content available from this model:
domain separation holds unless SHA-256 is broken, and no unsatisfiable
injectivity hypothesis is assumed.  The encoding-level half is the structural
lemma `tagPrefix_separates_hashed_tags`. -/
theorem taggedHash_collision_witness (M : PrimitiveModel) {t₁ t₂ msg : ByteArray}
    (htag : t₁ ≠ t₂) (heq : taggedHashSha256 M t₁ msg = taggedHashSha256 M t₂ msg) :
    ∃ x y : ByteArray, x ≠ y ∧ M.sha256 x = M.sha256 y := by
  by_cases hsha : M.sha256 t₁ = M.sha256 t₂
  · exact ⟨t₁, t₂, htag, hsha⟩
  · refine ⟨tagPrefix M t₁ ++ msg, tagPrefix M t₂ ++ msg, ?_, ?_⟩
    · intro hxy
      exact tagPrefix_separates_hashed_tags M hsha (append_right_cancel hxy)
    · simpa [taggedHashSha256] using heq

/-! ## 8. Interface defect: no injective hash into 32 bytes -/

/-! ### Counting helpers for `LN-CR-007`

A 32-byte digest has at most `257 ^ 32` possible values, while `ByteArray` has
infinitely many elements.  The helpers below make that finite bound usable
with Lean core arithmetic only:

* `encodeList` is a base-257 encoding of a byte list in which every digit is
  shifted by one.  No digit is zero, which removes the trailing-zero ambiguity
  of positional notation and makes the encoding injective on *all* byte lists;
* `unaryBytes i` is the `i`-byte string `0 ⋯ 0`, a family of pairwise distinct
  preimages indexed by `Nat`;
* `natPigeonhole` is the finite pigeonhole principle: an injective map from
  `{0, …, d-1}` into `{0, …, hi-1}` forces `d ≤ hi`.  It is proved by
  induction on `d`; the step removes the value `f d` from the codomain with
  the `skip` map `x ↦ if x < f d then x else x - 1`, which is injective off
  `f d`.
-/

/-- Base-257 encoding of a byte list with all digits shifted by one, so every
digit lies in `[1, 256]` and positional notation is unambiguous. -/
private def encodeList : List UInt8 → Nat
  | [] => 0
  | x :: xs => (x.toNat + 1) + 257 * encodeList xs

/-- The `i`-byte all-zero string.  Distinct indices give arrays of different
sizes, hence distinct `ByteArray`s. -/
private def unaryBytes (i : Nat) : ByteArray :=
  ByteArray.mk (Array.mk (List.replicate i (0 : UInt8)))

/-- Value-skipping map used by the pigeonhole induction step. -/
private def skip (v x : Nat) : Nat := if x < v then x else x - 1

private theorem encodeList_lt (l : List UInt8) : encodeList l < 257 ^ l.length := by
  induction l with
  | nil => simp [encodeList]
  | cons x xs IH =>
    have hx : x.toNat + 1 ≤ 256 := by have := UInt8.toNat_lt x; omega
    simp only [encodeList, List.length_cons, Nat.pow_succ']
    omega

private theorem encodeList_pos (x : UInt8) (xs : List UInt8) :
    0 < encodeList (x :: xs) := by
  simp only [encodeList]
  omega

/-- The base-257 encoding is injective: the low digit is recovered by `% 257`
and the rest by `/ 257`. -/
private theorem encodeList_inj : ∀ (l₁ l₂ : List UInt8),
    encodeList l₁ = encodeList l₂ → l₁ = l₂ := by
  intro l₁
  induction l₁ with
  | nil =>
    intro l₂ h
    cases l₂ with
    | nil => rfl
    | cons y ys =>
      have hp := encodeList_pos y ys
      simp only [encodeList] at h
      omega
  | cons x xs IH =>
    intro l₂ h
    cases l₂ with
    | nil =>
      have hp := encodeList_pos x xs
      simp only [encodeList] at h
      omega
    | cons y ys =>
      simp only [encodeList] at h
      have hxlt : x.toNat + 1 < 257 := by have := UInt8.toNat_lt x; omega
      have hylt : y.toNat + 1 < 257 := by have := UInt8.toNat_lt y; omega
      have hmod : (x.toNat + 1) % 257 = (y.toNat + 1) % 257 := by
        have hc := congrArg (fun n => n % 257) h
        simpa only [Nat.add_mul_mod_self_left] using hc
      rw [Nat.mod_eq_of_lt hxlt, Nat.mod_eq_of_lt hylt] at hmod
      have hxy : x = y := by
        apply UInt8.toNat_inj.mp
        omega
      have hdiv : encodeList xs = encodeList ys := by
        have h1 : ((x.toNat + 1) + 257 * encodeList xs) / 257 = encodeList xs := by
          rw [Nat.add_mul_div_left _ _ (by omega : 0 < 257), Nat.div_eq_of_lt hxlt]
          omega
        have h2 : ((y.toNat + 1) + 257 * encodeList ys) / 257 = encodeList ys := by
          rw [Nat.add_mul_div_left _ _ (by omega : 0 < 257), Nat.div_eq_of_lt hylt]
          omega
        have hc := congrArg (fun n => n / 257) h
        rw [h1, h2] at hc
        exact hc
      subst hxy
      rw [IH ys hdiv]

private theorem unaryBytes_size (i : Nat) : (unaryBytes i).size = i := by
  simp [unaryBytes, ByteArray.size, Array.size]

private theorem unaryBytes_inj {i j : Nat} (h : unaryBytes i = unaryBytes j) : i = j := by
  have := congrArg ByteArray.size h
  simpa [unaryBytes_size] using this

private theorem encode_size (a : ByteArray) : (a.data.toList).length = a.size := by
  rw [Array.length_toList, ByteArray.size_data]

/-- The list encoding is injective on `ByteArray`s. -/
private theorem encode_inj {a b : ByteArray}
    (h : encodeList a.data.toList = encodeList b.data.toList) : a = b := by
  apply ByteArray.ext
  exact Array.toList_inj.mp (encodeList_inj _ _ h)

private theorem skip_lt {v x hi : Nat} (hv : v < hi) (hx : x < hi) (hne : x ≠ v) :
    skip v x < hi - 1 := by
  unfold skip
  by_cases h : x < v
  · rw [ite_eq_left h]; omega
  · rw [ite_eq_right h]; omega

private theorem skip_inj {v x y : Nat} (hx : x ≠ v) (hy : y ≠ v)
    (h : skip v x = skip v y) : x = y := by
  unfold skip at h
  by_cases h1 : x < v <;> by_cases h2 : y < v
  · rw [ite_eq_left h1, ite_eq_left h2] at h; exact h
  · rw [ite_eq_left h1, ite_eq_right h2] at h; omega
  · rw [ite_eq_right h1, ite_eq_left h2] at h; omega
  · rw [ite_eq_right h1, ite_eq_right h2] at h; omega

/-- Finite pigeonhole principle over initial `Nat` segments. -/
private theorem natPigeonhole (d hi : Nat) (f : Nat → Nat)
    (hrange : ∀ i, i < d → f i < hi)
    (hinj : ∀ i j, i < d → j < d → f i = f j → i = j) : d ≤ hi := by
  induction d generalizing hi f with
  | zero => omega
  | succ d IH =>
    have hhi : 0 < hi := by have := hrange d (by omega); omega
    have hne : ∀ i, i < d → f i ≠ f d := by
      intro i hi' heq
      have := hinj i d (by omega) (by omega) heq
      omega
    have hrange' : ∀ i, i < d → skip (f d) (f i) < hi - 1 := fun i hi' =>
      skip_lt (hrange d (by omega)) (hrange i (by omega)) (hne i hi')
    have hinj' : ∀ i j, i < d → j < d →
        skip (f d) (f i) = skip (f d) (f j) → i = j := by
      intro i j hi' hj' heq
      exact hinj i j (by omega) (by omega) (skip_inj (hne i hi') (hne j hj') heq)
    have hle : d ≤ hi - 1 := IH (hi - 1) (fun i => skip (f d) (f i)) hrange' hinj'
    omega

/-- **No global injective hash into 32 bytes.**  A function from `ByteArray`
to the 32-byte strings cannot be injective: the domain has more elements than
the `2^256` possible 32-byte outputs.  Consequently the `PreimageResistant`
field of `PrimitiveModel` is not satisfiable together with `sha256_size`, and
the consistent hypothesis for payment preimages is `CollisionResistant` on
32-byte inputs.

The proof indexes `257 ^ 32 + 1` distinct preimages `unaryBytes i` and encodes
each 32-byte image as a natural number below `257 ^ 32`; injectivity of `H`
would make these encodings injective, contradicting `natPigeonhole`. -/
theorem no_injective_hash_into_32_bytes (H : ByteArray → ByteArray)
    (hsize : ∀ b : ByteArray, (H b).size = 32) :
    ¬ PreimageResistant H := by
  -- LN-CR-007 (closed by the counting argument below): `ByteArray` has more
  -- elements than the 2^256 possible 32-byte outputs, so no `H` with
  -- `(H b).size = 32` for all `b` is injective; the global `PreimageResistant`
  -- field of `PrimitiveModel` is therefore incompatible with `sha256_size`,
  -- and the consistent hypothesis is injectivity on 32-byte preimages.
  intro hinj
  let f : Nat → Nat := fun i => encodeList (H (unaryBytes i)).data.toList
  have hrange : ∀ i, i < 257 ^ 32 + 1 → f i < 257 ^ 32 := by
    intro i _
    have hlt := encodeList_lt (H (unaryBytes i)).data.toList
    have hlen : (H (unaryBytes i)).data.toList.length = 32 := by
      rw [encode_size, hsize]
    dsimp only [f]
    rw [hlen] at hlt
    exact hlt
  have hinj' : ∀ i j, i < 257 ^ 32 + 1 → j < 257 ^ 32 + 1 → f i = f j → i = j := by
    intro i j _ _ heq
    dsimp only [f] at heq
    exact unaryBytes_inj (hinj _ _ (encode_inj heq))
  have hle := natPigeonhole _ _ f hrange hinj'
  omega

/-- The interface defect as a statement about every `PrimitiveModel`. -/
theorem preimageResistant_vacuous (M : PrimitiveModel) :
    ¬ PreimageResistant M.sha256 :=
  no_injective_hash_into_32_bytes M.sha256 M.sha256_size

end LnLean.Proofs.Crypto
