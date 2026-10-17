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
`sha256_size`.  This module proves that gap as `LN-CR-007`
(`no_injective_hash_into_32_bytes`, by finite pigeonhole) and uses the field
only in explicitly conditional theorems.  The consistent hypothesis for Lightning's
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
supply together with `sha256_size` (obligation `LN-CR-007`). -/
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

/-! ## 8. No global injective hash into 32 bytes

The counting argument is formalised without `Fintype` or mathlib.  The first
helper enumerates all byte vectors of a given length by structural recursion;
the second identifies a `ByteArray` with its list of byte values.  Pigeonhole
is then `List.Nodup.length_le_of_subset` against `List.finRange`. -/

/-- All byte vectors of length `n`, represented as lists of `Fin 256` values.
The enumeration is complete (`mem_sha256PropsAllByteVectors`) but deliberately
not proved duplicate-free: completeness is all the counting argument needs. -/
private def sha256PropsAllByteVectors : Nat → List (List (Fin 256))
  | 0 => [[]]
  | n + 1 =>
      (sha256PropsAllByteVectors n).flatMap fun v =>
        (List.finRange 256).map fun b => b :: v

/-- Every list of `Fin 256` values of length `n` occurs in the enumeration. -/
private theorem mem_sha256PropsAllByteVectors :
    ∀ (l : List (Fin 256)) (n : Nat),
      l.length = n → l ∈ sha256PropsAllByteVectors n := by
  intro l n
  induction n generalizing l with
  | zero =>
      intro h
      cases l with
      | nil => simp [sha256PropsAllByteVectors]
      | cons a t => simp at h
  | succ n ih =>
      intro h
      cases l with
      | nil => simp at h
      | cons a t =>
          have ht : t.length = n := by simpa using h
          have htmem : t ∈ sha256PropsAllByteVectors n := ih t ht
          have hamem : a ∈ List.finRange 256 := by simp
          have hmap : a :: t ∈
              (List.finRange 256).map (fun b => b :: t) :=
            List.mem_map.mpr ⟨a, hamem, rfl⟩
          exact List.mem_flatMap.mpr ⟨t, htmem, hmap⟩

/-- The byte list of a `ByteArray`, with each byte viewed as `Fin 256`. -/
private def sha256PropsToListFin (b : ByteArray) : List (Fin 256) :=
  b.data.toList.map UInt8.toFin

/-- `sha256PropsToListFin` does not identify distinct byte arrays. -/
private theorem sha256PropsToListFin_inj :
    Function.Injective sha256PropsToListFin := by
  intro a b h
  unfold sha256PropsToListFin at h
  have h' : a.data = b.data := by
    rw [← Array.toList_inj]
    exact (List.map_inj_right
      (fun x y hxy => UInt8.toFin_inj.mp hxy)).mp h
  exact ByteArray.ext h'

/-- The all-zero byte array of length `n`. -/
private def sha256PropsZeros (n : Nat) : ByteArray :=
  (List.replicate n (0 : UInt8)).toByteArray

/-- The all-zero arrays have distinct lengths, hence are distinct inputs. -/
private theorem sha256PropsZeros_inj :
    Function.Injective sha256PropsZeros := by
  intro m n h
  have hsize : (sha256PropsZeros m).size = (sha256PropsZeros n).size :=
    congrArg ByteArray.size h
  simpa [sha256PropsZeros, List.size_toByteArray] using hsize

/-- Pigeonhole in the form needed here: there is no injection from
`Fin (n + 1)` into `Fin n`. -/
private theorem sha256PropsNotInjectiveFinSucc {n : Nat}
    (f : Fin (n + 1) → Fin n) : ¬ Function.Injective f := by
  intro hf
  let l := (List.finRange (n + 1)).map f
  have hnodup : l.Nodup := by
    dsimp [l]
    rw [List.nodup_iff_pairwise_ne]
    exact List.Pairwise.map f (fun a b hab heq => hab (hf heq))
      (List.nodup_iff_pairwise_ne.mp (List.nodup_finRange (n + 1)))
  have hsub : l ⊆ List.finRange n := by
    intro x hx
    simp only [l, List.mem_map] at hx
    obtain ⟨i, -, rfl⟩ := hx
    simp
  have hle := List.Nodup.length_le_of_subset hnodup hsub
  simp [l] at hle
  omega

/-- **No global injective hash into 32 bytes.**  A function from `ByteArray`
to the 32-byte strings cannot be injective: the domain has more elements than
the `2^256` possible 32-byte outputs.  Consequently the `PreimageResistant`
field of `PrimitiveModel` is not satisfiable together with `sha256_size`, and
the consistent hypothesis for payment preimages is `CollisionResistant` on
32-byte inputs.

The proof enumerates the finite set of 32-byte words and restricts `H` to the
`N + 1` distinct all-zero inputs, where `N` is the length of the enumeration.
Injectivity would give `N + 1` distinct outputs inside a list of length `N`,
contradicting `List.Nodup.length_le_of_subset`. -/
theorem no_injective_hash_into_32_bytes (H : ByteArray → ByteArray)
    (hsize : ∀ b : ByteArray, (H b).size = 32) :
    ¬ PreimageResistant H := by
  intro hpre
  let N := (sha256PropsAllByteVectors 32).length
  let f : Fin (N + 1) → List (Fin 256) :=
    fun i => sha256PropsToListFin (H (sha256PropsZeros i.val))
  have hf_inj : Function.Injective f := by
    intro i j hij
    have hH : H (sha256PropsZeros i.val) =
        H (sha256PropsZeros j.val) :=
      sha256PropsToListFin_inj hij
    have hz : sha256PropsZeros i.val = sha256PropsZeros j.val :=
      hpre _ _ hH
    exact Fin.ext (sha256PropsZeros_inj hz)
  have hnodup : ((List.finRange (N + 1)).map f).Nodup := by
    rw [List.nodup_iff_pairwise_ne]
    exact List.Pairwise.map f (fun a b hab heq => hab (hf_inj heq))
      (List.nodup_iff_pairwise_ne.mp (List.nodup_finRange (N + 1)))
  have hlen : ∀ i : Fin (N + 1), (f i).length = 32 := by
    intro i
    simp [f, sha256PropsToListFin, hsize (sha256PropsZeros i.val)]
  have hsub : (List.finRange (N + 1)).map f ⊆
      sha256PropsAllByteVectors 32 := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
    exact mem_sha256PropsAllByteVectors (f i) 32 (hlen i)
  have hle := List.Nodup.length_le_of_subset hnodup hsub
  simp [N] at hle
  omega

/-- The interface defect as a statement about every `PrimitiveModel`. -/
theorem preimageResistant_vacuous (M : PrimitiveModel) :
    ¬ PreimageResistant M.sha256 :=
  no_injective_hash_into_32_bytes M.sha256 M.sha256_size

end LnLean.Proofs.Crypto
