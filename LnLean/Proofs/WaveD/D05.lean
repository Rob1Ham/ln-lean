/-
# D05 — Payment hashes are SHA-256 outputs (LN-CR-001)

**English claim.**  A BOLT 2 payment hash is a SHA-256 output: the sender
computes `payment_hash = SHA256(payment_preimage)` and the receiver settles
the HTLC only on presentation of a preimage with that digest.  The catalog
entry LN-CR-001 asks for this fact "relying on assumption C1 (collision and
preimage resistance)".

**What is actually true in the model.**  The two halves of the claim have
different trust requirements, and this module separates them:

* *Output-ness* is **structural**.  `PrimitiveModel.paymentHashOf` is defined
  as `digest32 (M.sha256 pre.bytes)`, and `sha256_size` makes `digest32` the
  identity on every SHA-256 image.  Hence every constructed payment hash is
  literally `M.sha256 pre.bytes`, and every payment hash that some preimage
  opens is in the range of `M.sha256`.  No cryptographic assumption is used
  (`waveD_d05_paymentHashOf_eq_sha256`,
  `waveD_d05_opensTo_iff_sha256_output`).
* *Binding* (a payment hash determines at most one preimage) is **conditional
  on C1**, specifically on `CollisionResistant M.sha256` over valid 32-byte
  payment preimages
  (`waveD_d05_paymentHashOf_commits`, `waveD_d05_opensTo_unique_of_collisionResistant`).
  The former global `sha256_preimageResistant` field has been removed from
  `PrimitiveModel`; it is not assumed here.  Global injectivity is impossible
  for any 32-byte-output hash
  (`LnLean.Proofs.Crypto.Sha256Props.preimageResistant_vacuous`), so the usable
  assumption is the 32-byte-domain collision resistance field.

**Negative result (model gap).**  The claim is *not* true of an arbitrary
`PaymentHash` value.  `PaymentHash` is a bare `ByteArray` wrapper, and
`LnLean.Protocol.wellFormed` for `update_add_htlc` checks lengths, channel ids,
signatures, amount, CLTV and onion size, but never checks that the 32-byte
`payment_hash` field is in the range of SHA-256 (indeed it does not even check
that it is 32 bytes).  A 33-byte hash can never be a SHA-256 image, so
`waveD_d05_wellFormed_message_with_non_output_hash` exhibits a well-formed
`update_add_htlc` carrying a hash that no preimage can open.  The protocol-level
statement therefore needs the range hypothesis, not just C1.

**BOLT sections.**
* BOLT 2 §Adding an HTLC (`refs/bolts/02-peer-protocol.md:2772-2790`):
  `update_add_htlc` carries a 32-byte `payment_hash`.
* BOLT 2 §Removing an HTLC (`refs/bolts/02-peer-protocol.md:2913-2955`):
  `update_fulfill_htlc` carries a 32-byte `payment_preimage`, accepted only if
  it hashes to the payment hash (`:3004-3005`).
* BOLT 1 §Fundamental Types (`refs/bolts/01-messaging.md:254`): `sha256` is a
  32-byte SHA2-256 digest.

**rust-lightning anchors (commit fe49009).**
* `lightning/src/ln/channel.rs:8370` — the `update_add_htlc` handling named by
  the catalog; `payment_hash` is copied into the HTLC record.
* `lightning-types/src/payment.rs:70-73` — `From<PaymentPreimage> for
  PaymentHash` is `Sha256::hash(preimage.0).to_byte_array()`.
* `lightning/src/ln/msgs.rs:3553-3557` — `update_add_htlc` serialises the
  `payment_hash` field.
* `lightning/src/ln/msgs.rs:3503-3506` — `update_fulfill_htlc` serialises the
  `payment_preimage` field.
-/

import LnLean.Crypto.Hash
import LnLean.Crypto.Model
import LnLean.Crypto.Sig
import LnLean.Wire.BigSize
import LnLean.Wire.TLV
import LnLean.Wire.Message
import LnLean.Protocol.Messages

namespace LnLean.Proofs.WaveD.D05

set_option autoImplicit false

open LnLean LnLean.Crypto LnLean.Protocol

-- OBLIGATION: LN-WD-D05

/-! ## 1. Output-ness is structural: constructed hashes are SHA-256 images -/

/-- `paymentHashOf` is exactly the SHA-256 image of the preimage.  The
`digest32` normalisation in `PrimitiveModel.paymentHashOf` disappears because
`sha256_size` already yields a 32-byte value. -/
theorem waveD_d05_paymentHashOf_eq_sha256 (M : PrimitiveModel) (pre : Preimage) :
    (M.paymentHashOf pre).bytes = M.sha256 pre.bytes := by
  unfold PrimitiveModel.paymentHashOf
  simp [PrimitiveModel.digest32_of_size (M.sha256_size pre.bytes)]

/-- Every payment hash produced by the model is in the range of `M.sha256`,
with the preimage's bytes as the explicit witness.  This is the formal content
of "payment hashes are SHA-256 outputs" for honestly constructed hashes; it
uses no cryptographic assumption. -/
theorem waveD_d05_paymentHashOf_is_sha256_output (M : PrimitiveModel)
    (pre : Preimage) :
    ∃ b : ByteArray, M.sha256 b = (M.paymentHashOf pre).bytes :=
  ⟨pre.bytes, (waveD_d05_paymentHashOf_eq_sha256 M pre).symm⟩

/-- A hash lock that is satisfied by some preimage is a SHA-256 output.  The
witness is the preimage that opens it. -/
theorem waveD_d05_opensTo_is_sha256_output (M : PrimitiveModel)
    {ph : PaymentHash} {pre : Preimage} (h : opensTo M ph pre) :
    ∃ b : ByteArray, M.sha256 b = ph.bytes := by
  refine ⟨pre.bytes, ?_⟩
  unfold opensTo at h
  rw [PrimitiveModel.digest32_of_size (M.sha256_size pre.bytes)] at h
  exact h

/-- **Range characterisation.**  A payment hash can be opened by some preimage
exactly when it is in the range of `M.sha256`.  The reverse direction embeds an
arbitrary range witness as a `Preimage`; the model does not require that
witness to be 32 bytes (`opensTo` only compares digests). -/
theorem waveD_d05_opensTo_iff_sha256_output (M : PrimitiveModel)
    (ph : PaymentHash) :
    (∃ pre : Preimage, opensTo M ph pre) ↔
      ∃ b : ByteArray, M.sha256 b = ph.bytes := by
  constructor
  · rintro ⟨_pre, h⟩
    exact waveD_d05_opensTo_is_sha256_output M h
  · rintro ⟨b, hb⟩
    refine ⟨⟨b⟩, ?_⟩
    unfold opensTo
    rw [PrimitiveModel.digest32_of_size (M.sha256_size b)]
    exact hb

/-- **Protocol consequence.**  If a payment hash is outside the range of
SHA-256, no `update_fulfill_htlc` preimage can ever settle it.  This is a
purely structural statement (a total function cannot return a value outside
its range), so it needs neither collision nor preimage resistance. -/
theorem waveD_d05_no_preimage_of_not_sha256_output (M : PrimitiveModel)
    {ph : PaymentHash} (h : ∀ b : ByteArray, M.sha256 b ≠ ph.bytes) :
    ∀ pre : Preimage, ¬ opensTo M ph pre := by
  intro pre hopen
  obtain ⟨b, hb⟩ := waveD_d05_opensTo_is_sha256_output M hopen
  exact h b hb

/-- Every SHA-256 image is a well-sized payment hash (`sha256_size`, BOLT 1). -/
theorem waveD_d05_sha256_output_valid (M : PrimitiveModel) (b : ByteArray) :
    (⟨M.sha256 b⟩ : PaymentHash).Valid :=
  M.sha256_size b

/-- The canonical payment hash of a preimage is a well-sized 32-byte value. -/
theorem waveD_d05_paymentHashOf_valid (M : PrimitiveModel) (pre : Preimage) :
    (M.paymentHashOf pre).Valid :=
  M.paymentHashOf_valid pre

/-! ## 2. The binding half: C1 (collision resistance) is required -/

/-- **Hash-lock uniqueness under C1.**  Two valid 32-byte preimages that open
the same payment hash are equal, assuming `CollisionResistant M.sha256` (the
32-byte form of assumption C1).  This is the commitment property consumed by
BOLT 2 §Removing an HTLC. -/
theorem waveD_d05_opensTo_unique_of_collisionResistant (M : PrimitiveModel)
    (hc : CollisionResistant M.sha256) {ph : PaymentHash} {p q : Preimage}
    (hp : opensTo M ph p) (hq : opensTo M ph q)
    (hpv : p.Valid) (hqv : q.Valid) : p = q :=
  preimage_unique M hc hp hq hpv hqv

/-- **Payment-hash commitment under C1.**  Equal canonical payment hashes of
valid preimages imply equal preimages.  Only the retained 32-byte-domain
`CollisionResistant` assumption is used; the removed global
`sha256_preimageResistant` field is not assumed.  This is an explicit interface
assumption, not a computational proof. -/
theorem waveD_d05_paymentHashOf_commits (M : PrimitiveModel)
    (hc : CollisionResistant M.sha256) {p q : Preimage}
    (hpv : p.Valid) (hqv : q.Valid)
    (hph : M.paymentHashOf p = M.paymentHashOf q) : p = q :=
  paymentHash_commits M hc hpv hqv hph

/-- Contrapositive form: distinct valid preimages have distinct payment
hashes under C1.  This is what prevents a sender from reusing one hash for two
different secrets. -/
theorem waveD_d05_paymentHashOf_ne (M : PrimitiveModel)
    (hc : CollisionResistant M.sha256) {p q : Preimage}
    (hpv : p.Valid) (hqv : q.Valid) (hne : p ≠ q) :
    M.paymentHashOf p ≠ M.paymentHashOf q := by
  intro heq
  exact hne (waveD_d05_paymentHashOf_commits M hc hpv hqv heq)

/-- Two `update_fulfill_htlc` messages that satisfy the same hash lock carry
the same preimage, under C1 and the BOLT 2 32-byte preimage width.  The
channel/HTLC identifiers are irrelevant to this cryptographic fact. -/
theorem waveD_d05_fulfil_preimage_unique (M : PrimitiveModel)
    (hc : CollisionResistant M.sha256) {ph : PaymentHash}
    {f g : UpdateFulfillHtlc}
    (hf : opensTo M ph f.paymentPreimage)
    (hg : opensTo M ph g.paymentPreimage)
    (hfv : f.paymentPreimage.Valid) (hgv : g.paymentPreimage.Valid) :
    f.paymentPreimage = g.paymentPreimage :=
  waveD_d05_opensTo_unique_of_collisionResistant M hc hf hg hfv hgv

/-! ## 3. The BOLT 2 `update_add_htlc` field -/

/-- If an `update_add_htlc` message was built from a preimage via
`paymentHashOf`, its wire `payment_hash` is a SHA-256 output. -/
theorem waveD_d05_updateAddHtlc_hash_is_sha256_output (M : PrimitiveModel)
    (m : UpdateAddHtlc) (pre : Preimage)
    (hm : m.paymentHash = M.paymentHashOf pre) :
    ∃ b : ByteArray, M.sha256 b = m.paymentHash.bytes := by
  rw [hm]
  exact waveD_d05_paymentHashOf_is_sha256_output M pre

/-- If the `payment_hash` field of an `update_add_htlc` is not a SHA-256
output, no `update_fulfill_htlc` preimage can open it. -/
theorem waveD_d05_updateAddHtlc_no_fulfil_of_not_output (M : PrimitiveModel)
    {add : UpdateAddHtlc}
    (hnot : ∀ b : ByteArray, M.sha256 b ≠ add.paymentHash.bytes) :
    ∀ f : UpdateFulfillHtlc, ¬ opensTo M add.paymentHash f.paymentPreimage := by
  intro f
  exact waveD_d05_no_preimage_of_not_sha256_output M hnot f.paymentPreimage

/-! ## 4. Negative result: well-formed messages may carry non-output hashes -/

/-- The all-zero byte string of length `n`. -/
def zeroBytes (n : Nat) : ByteArray :=
  ByteArray.mk (Array.mk (List.replicate n (0 : UInt8)))

@[simp] theorem zeroBytes_size (n : Nat) : (zeroBytes n).size = n := by
  simp [zeroBytes, ByteArray.size, Array.size]

/-- A 33-byte payment hash.  `PaymentHash` does not enforce `Valid`, and
`wellFormed` does not check the payment-hash width either. -/
def badPaymentHash : PaymentHash := ⟨zeroBytes 33⟩

/-- A 33-byte value is never the output of `M.sha256`, whose every output has
size 32. -/
theorem waveD_d05_badPaymentHash_not_sha256_output (M : PrimitiveModel) :
    ∀ b : ByteArray, M.sha256 b ≠ badPaymentHash.bytes := by
  intro b h
  have hsize := congrArg ByteArray.size h
  rw [M.sha256_size] at hsize
  simp [badPaymentHash, zeroBytes_size] at hsize

/-- The same value violates the BOLT 2 32-byte payment-hash width. -/
theorem waveD_d05_badPaymentHash_not_valid : ¬ badPaymentHash.Valid := by
  intro h
  have hsize : badPaymentHash.bytes.size = 32 := h
  simp [badPaymentHash, zeroBytes_size] at hsize

/-- A syntactically valid `update_add_htlc` (BOLT 2 type 128) carrying the
33-byte hash.  All fields required by `wellFormed` are chosen to satisfy their
checks: a 32-byte channel id, positive amount, small CLTV, and a 1366-byte
onion packet (the BOLT 4 packet size). -/
def badUpdateAddHtlc : UpdateAddHtlc :=
  { channelId := ⟨zeroBytes 32⟩
    htlcId := 0
    amountMsat := ⟨1000⟩
    paymentHash := badPaymentHash
    cltvExpiry := 100
    onionRoutingPacket := zeroBytes 1366 }

/-- The counterexample message passes the model's wire well-formedness
predicate.  `wellFormed` checks the channel id, public keys, signature sizes,
amount, CLTV and onion length, but not the payment-hash type. -/
theorem waveD_d05_badUpdateAddHtlc_wellFormed :
    wellFormed (.updateAddHtlc badUpdateAddHtlc) := by
  unfold wellFormed msgLength idsValid sigsValid semanticOk channelId? pubKeys signatures
  simp [badUpdateAddHtlc, zeroBytes_size, ChannelId.Valid]

/-- **The unconditional protocol claim is false.**  For every primitive model
there is a `wellFormed` `update_add_htlc` whose `payment_hash` is not a
SHA-256 output (and is not even 32 bytes).  Consequently LN-CR-001 cannot be
stated as "every payment hash in a well-formed `update_add_htlc` is a SHA-256
output" without adding the range hypothesis, and C1 alone does not supply it.
-/
theorem waveD_d05_wellFormed_message_with_non_output_hash (M : PrimitiveModel) :
    ∃ m : UpdateAddHtlc,
      wellFormed (.updateAddHtlc m) ∧
      ¬ m.paymentHash.Valid ∧
      ∀ b : ByteArray, M.sha256 b ≠ m.paymentHash.bytes :=
  ⟨badUpdateAddHtlc, waveD_d05_badUpdateAddHtlc_wellFormed,
    waveD_d05_badPaymentHash_not_valid,
    waveD_d05_badPaymentHash_not_sha256_output M⟩

/-- The range statement fails for arbitrary `PaymentHash` values in every
model: `badPaymentHash` is outside the image of `M.sha256`. -/
theorem waveD_d05_not_all_paymentHashes_are_sha256_outputs
    (M : PrimitiveModel) :
    ¬ ∀ ph : PaymentHash, ∃ b : ByteArray, M.sha256 b = ph.bytes := by
  intro hall
  obtain ⟨b, hb⟩ := hall badPaymentHash
  exact waveD_d05_badPaymentHash_not_sha256_output M b hb

end LnLean.Proofs.WaveD.D05
