/-
# Hash locks and payment-hash commitments

**English claim.**  A hash-lock (HTLC) is opened by a preimage `pre` whose
SHA-256 digest equals the payment hash `ph`.  Payment hashes are 32-byte
commitments: if SHA-256 is collision resistant on 32-byte preimages, a
payment hash determines at most one valid preimage.  This is exactly the
"preimage soundness" premise used by the HTLC model; the cryptographic
direction is conditional on the model's assumption field and is never
asserted unconditionally.

**BOLT sections.**  BOLT 2 §`update_add_htlc`/`update_fulfill_htlc` (payment
hash and preimage), BOLT 4 (hash locks in onion errors).  BOLT 1 defines the
32-byte `sha256` wire type.

**rust-lightning anchors (commit fe49009).**
* `lightning-types/src/payment.rs:70-73` — `PaymentPreimage` is converted to
  `PaymentHash` by SHA-256.
* `lightning/src/ln/msgs.rs:3553` — `update_add_htlc` carries `payment_hash`;
  `:3503` — `update_fulfill_htlc` carries `payment_preimage`.
* `lightning/src/util/ser.rs:442-490` — the serialization layer that treats
  hashes as fixed 32-byte fields.

**Not modelled.**  SHA-256 compression, concrete hash values, length-extension
attacks, preimage search cost, and the HTLC script/`OP_SHA256` execution
(BOLT 3).  The model only exposes digest equality and the conditional
uniqueness theorem.
-/

import LnLean.Crypto.Model

namespace LnLean.Crypto

set_option autoImplicit false

open LnLean

/-- A preimage opens a payment hash when its 32-byte SHA-256 image equals the
hash.  `digest32` is the total 32-byte normalisation from `Crypto.Model`. -/
def opensTo (M : PrimitiveModel) (ph : PaymentHash) (pre : Preimage) : Prop :=
  PrimitiveModel.digest32 (M.sha256 pre.bytes) = ph.bytes

/-- The canonical payment hash of a preimage opens that preimage's hash lock. -/
theorem opensTo_paymentHashOf (M : PrimitiveModel) (pre : Preimage) :
    opensTo M (M.paymentHashOf pre) pre := rfl

/-- Hash-lock satisfaction is decidable, because `ByteArray` equality is. -/
instance opensToDecidable (M : PrimitiveModel) (ph : PaymentHash) (pre : Preimage) :
    Decidable (opensTo M ph pre) := by
  unfold opensTo
  infer_instance

/-- Unfold a hash lock when the SHA-256 image already has the correct size. -/
theorem opensTo_iff_sha256 (M : PrimitiveModel) (ph : PaymentHash) (pre : Preimage)
    (h : (M.sha256 pre.bytes).size = 32) :
    opensTo M ph pre ↔ M.sha256 pre.bytes = ph.bytes := by
  unfold opensTo
  rw [PrimitiveModel.digest32_of_size h]

/-- **Preimage uniqueness.**  Under the model's collision-resistance field, a
payment hash has at most one valid 32-byte preimage.  This is the formal
content of "a payment hash commits to a preimage"; no cryptographic hardness
is proved here. -/
theorem preimage_unique (M : PrimitiveModel) (h : CollisionResistant M.sha256)
    {ph : PaymentHash} {p q : Preimage}
    (hp : opensTo M ph p) (hq : opensTo M ph q)
    (hpv : p.Valid) (hqv : q.Valid) : p = q := by
  have hd : PrimitiveModel.digest32 (M.sha256 p.bytes) =
      PrimitiveModel.digest32 (M.sha256 q.bytes) := by
    rw [hp, hq]
  have hp' : PrimitiveModel.digest32 (M.sha256 p.bytes) = M.sha256 p.bytes :=
    PrimitiveModel.digest32_of_size (M.sha256_size p.bytes)
  have hq' : PrimitiveModel.digest32 (M.sha256 q.bytes) = M.sha256 q.bytes :=
    PrimitiveModel.digest32_of_size (M.sha256_size q.bytes)
  have hsha : M.sha256 p.bytes = M.sha256 q.bytes := by
    rw [← hp', ← hq']
    exact hd
  have h' : ∀ x y : ByteArray,
      x.size = 32 → y.size = 32 → M.sha256 x = M.sha256 y → x = y := h
  have hbytes : p.bytes = q.bytes :=
    h' p.bytes q.bytes hpv hqv hsha
  cases p with
  | mk pb =>
    cases q with
    | mk qb =>
      simp only at hbytes
      rw [hbytes]

/-- **Payment-hash commitment.**  Equal payment hashes of two valid preimages
imply equal preimages, conditional on collision resistance. -/
theorem paymentHash_commits (M : PrimitiveModel) (h : CollisionResistant M.sha256)
    {p q : Preimage} (hp : p.Valid) (hq : q.Valid)
    (hph : M.paymentHashOf p = M.paymentHashOf q) : p = q := by
  have hd : PrimitiveModel.digest32 (M.sha256 p.bytes) =
      PrimitiveModel.digest32 (M.sha256 q.bytes) :=
    congrArg PaymentHash.bytes hph
  have hp' : PrimitiveModel.digest32 (M.sha256 p.bytes) = M.sha256 p.bytes :=
    PrimitiveModel.digest32_of_size (M.sha256_size p.bytes)
  have hq' : PrimitiveModel.digest32 (M.sha256 q.bytes) = M.sha256 q.bytes :=
    PrimitiveModel.digest32_of_size (M.sha256_size q.bytes)
  have hsha : M.sha256 p.bytes = M.sha256 q.bytes := by
    rw [← hp', ← hq']
    exact hd
  have h' : ∀ x y : ByteArray,
      x.size = 32 → y.size = 32 → M.sha256 x = M.sha256 y → x = y := h
  have hbytes : p.bytes = q.bytes :=
    h' p.bytes q.bytes hp hq hsha
  cases p with
  | mk pb =>
    cases q with
    | mk qb =>
      simp only at hbytes
      rw [hbytes]

/-- A payment hash produced by `paymentHashOf` is a valid 32-byte hash. -/
theorem paymentHashOf_valid (M : PrimitiveModel) (pre : Preimage) :
    (M.paymentHashOf pre).Valid :=
  M.paymentHashOf_valid pre

end LnLean.Crypto
