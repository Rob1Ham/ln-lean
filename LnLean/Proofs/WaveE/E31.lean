import LnLean.Payment.HTLC
import LnLean.Payment.Invoice
import LnLean.Payment.Laws
import LnLean.Payment.MPP
import LnLean.Proofs.Payment.KeysendProps

/-!
# LnLean.Proofs.WaveE.E31

Catalog obligation `LN-PM-006`: *A keysend payment uses the sender-supplied
preimage as the payment preimage.*

## Reading of the claim

A keysend (spontaneous) payment has no BOLT 11 invoice.  The sender chooses a
32-byte preimage `p`, sets the HTLC's `payment_hash` to `sha256 p`, and carries
`p` in the final onion payload.  The recipient checks
`sha256 p == payment_hash` before accepting the payment (LDK
`InvalidKeysendPreimage`, `lightning/src/ln/onion_payment.rs:440-455`); the
value it later reveals in `update_fulfill_htlc` is exactly the preimage from
that payload, not a fresh or recipient-chosen value.

The wave-A payment layer already has a `Keysend` record
(`LnLean.Proofs.Payment.KeysendProps`) whose `Valid` predicate is precisely the
recipient check.  This module proves the binding law for that record:

1. a valid keysend's stored (sender-supplied) preimage hashes to the session's
   payment hash (`waveE_e31_sender_preimage_commits`), hence it satisfies
   `PaymentSession.preimageCommits`;
2. every preimage revealed along any settlement trace equals the sender's
   preimage and hashes to the payment hash
   (`waveE_e31_reveal_is_sender_preimage`,
   `waveE_e31_reveal_is_payment_preimage`);
3. once a pending keysend succeeds, `revealedPreimage` is exactly
   `some k.preimage` (`waveE_e31_success_reveals_sender_preimage`);
4. consequently any candidate preimage that matches the payment hash is the
   sender's preimage, provided the modelled hash is collision-free in the sense
   of `LnLean.Payment.CollisionFree`
   (`waveE_e31_preimage_unique_of_collision_free`).

Point 4 is the only step that needs a cryptographic premise.  Dropping it is
not sound in the abstract model: the constant hash function gives a checked
counterexample (`waveE_e31_preimage_binding_not_unconditional`).  The
operational claim (points 1--3) is unconditional because `revealedPreimage` is
defined from the record's own preimage field.

The exact catalog target name `LnLean.Payment.Keysend.preimage_binding` is also
provided at the end of the file.

BOLT anchor: BOLT 4 §Payload for the Last Node (keysend extension; the
`5482373484` TLV is `UNANCHORED` in the pinned BOLTs tree).  LDK anchor:
`lightning/src/ln/onion_payment.rs:454`.
-/

set_option autoImplicit false

namespace LnLean.Proofs.WaveE.E31

open LnLean
open LnLean.Payment

-- OBLIGATION: LN-WE-E31

/-! ## Structural binding -/

/-- The sender-supplied preimage of a valid keysend is a payment preimage: its
`sha256` is the session's `payment_hash`.  This is the recipient's
`InvalidKeysendPreimage` check read in the constructive direction. -/
theorem waveE_e31_sender_preimage_commits
    (sha256 : Preimage → PaymentHash) (k : Keysend) (hk : k.Valid sha256) :
    sha256 k.preimage = k.session.paymentHash :=
  hk.hashIsPreimage.symm

/-- The wave-A session commitment relation holds for a keysend: the session's
payment hash is the hash of the carried preimage. -/
theorem waveE_e31_preimage_commits
    (sha256 : Preimage → PaymentHash) (k : Keysend) (hk : k.Valid sha256) :
    PaymentSession.preimageCommits sha256 k.preimage k.session :=
  waveE_e31_sender_preimage_commits sha256 k hk

/-- Any preimage revealed by any settlement trace of a keysend is the
sender-supplied preimage.  Settlement cannot substitute another value. -/
theorem waveE_e31_reveal_is_sender_preimage
    (k : Keysend) (os : List PaymentState) {p : Preimage}
    (h : (k.applyOutcomes os).revealedPreimage = some p) :
    p = k.preimage :=
  Keysend.applyOutcomes_reveal_is_sender_preimage k os h

/-- A revealed preimage of a valid keysend is a payment preimage: it hashes to
the session's payment hash.  This is the operational content of "the keysend
uses the sender-supplied preimage as the payment preimage". -/
theorem waveE_e31_reveal_is_payment_preimage
    (sha256 : Preimage → PaymentHash) (k : Keysend) (hk : k.Valid sha256)
    (os : List PaymentState) {p : Preimage}
    (h : (k.applyOutcomes os).revealedPreimage = some p) :
    p = k.preimage ∧ sha256 p = k.session.paymentHash := by
  have hp : p = k.preimage := waveE_e31_reveal_is_sender_preimage k os h
  exact ⟨hp, by rw [hp, waveE_e31_sender_preimage_commits sha256 k hk]⟩

/-- A pending keysend that settles successfully reveals exactly the
sender-supplied preimage. -/
theorem waveE_e31_success_reveals_sender_preimage
    (k : Keysend) (hk : k.session.state = .pending) :
    (k.settle .succeeded).revealedPreimage = some k.preimage :=
  Keysend.settle_succeeded_reveals k hk

/-! ## Uniqueness among candidate preimages -/

/-- **Binding, conditional on the cryptographic premise.**  If the modelled
hash is collision-free (the idealised form of C1 used by the payment layer),
then every preimage that matches a valid keysend's payment hash is the
sender-supplied preimage.  In particular the recipient cannot be made to fulfil
with a different preimage. -/
theorem waveE_e31_preimage_unique_of_collision_free
    (sha256 : Preimage → PaymentHash) (hCF : CollisionFree sha256)
    {k : Keysend} (hk : k.Valid sha256) {p : Preimage}
    (hp : sha256 p = k.session.paymentHash) : p = k.preimage := by
  apply hCF
  rw [hp, waveE_e31_sender_preimage_commits sha256 k hk]

/-- The conditional uniqueness result phrased over settlement traces: under
collision-freeness, a revealed value is the sender's preimage and every
candidate preimage hitting the same payment hash equals it. -/
theorem waveE_e31_preimage_binding_of_collision_free
    (sha256 : Preimage → PaymentHash) (hCF : CollisionFree sha256)
    (k : Keysend) (hk : k.Valid sha256) :
    (∀ (os : List PaymentState) {p : Preimage},
        (k.applyOutcomes os).revealedPreimage = some p → p = k.preimage) ∧
      (∀ p : Preimage, sha256 p = k.session.paymentHash → p = k.preimage) := by
  refine ⟨?_, ?_⟩
  · intro os p hp
    exact waveE_e31_reveal_is_sender_preimage k os hp
  · intro p hp
    exact waveE_e31_preimage_unique_of_collision_free sha256 hCF hk hp

/-! ## The unconditional operational law -/

/-- **Catalog claim `LN-PM-006`, unconditional operational form.**  For a valid
keysend, the sender's preimage commits to the payment hash, and every preimage
revealed along any settlement trace is that same sender-supplied preimage and
hashes to the payment hash.  No cryptographic assumption is needed for this
direction: the model's `revealedPreimage` reads the record's own preimage
field, and `Valid` is exactly the recipient's hash check. -/
theorem waveE_e31_preimage_binding
    (sha256 : Preimage → PaymentHash) (k : Keysend) (hk : k.Valid sha256) :
    sha256 k.preimage = k.session.paymentHash ∧
      (∀ (os : List PaymentState) {p : Preimage},
        (k.applyOutcomes os).revealedPreimage = some p →
          p = k.preimage ∧ sha256 p = k.session.paymentHash) := by
  refine ⟨waveE_e31_sender_preimage_commits sha256 k hk, ?_⟩
  intro os p hp
  exact waveE_e31_reveal_is_payment_preimage sha256 k hk os hp

/-- A pending valid keysend, after successful settlement, has revealed exactly
the sender-supplied preimage and that value is a payment preimage. -/
theorem waveE_e31_successful_payment_uses_sender_preimage
    (sha256 : Preimage → PaymentHash) (k : Keysend) (hk : k.Valid sha256)
    (hpending : k.session.state = .pending) :
    (k.settle .succeeded).revealedPreimage = some k.preimage ∧
      sha256 k.preimage = k.session.paymentHash := by
  refine ⟨waveE_e31_success_reveals_sender_preimage k hpending, ?_⟩
  exact waveE_e31_sender_preimage_commits sha256 k hk

/-! ## The cryptographic premise is not derivable in the model -/

/-- The unconditional uniqueness form is false in the abstract model: the
constant hash function makes every preimage a candidate for the same payment
hash.  This is a checked counterexample, not a `sorry`, and it is why
`waveE_e31_preimage_unique_of_collision_free` carries `CollisionFree`
explicitly.  (The same phenomenon is recorded for INV-03 in
`LnLean.Proofs.Security.ThreatModelProps`.) -/
theorem waveE_e31_preimage_binding_not_unconditional :
    ¬ (∀ (sha256 : Preimage → PaymentHash) (k : Keysend),
        k.Valid sha256 → ∀ p : Preimage,
          sha256 p = k.session.paymentHash → p = k.preimage) := by
  intro hall
  let sha256 : Preimage → PaymentHash := fun _ => ⟨ByteArray.empty⟩
  let k : Keysend :=
    Keysend.create sha256 ⟨ByteArray.empty⟩ Msat.zero 0
  have hk : k.Valid sha256 := by
    refine ⟨rfl, ?_⟩
    simp [k, Keysend.create, Msat.zero, Msat.MAX]
  have hbad : (⟨ByteArray.mk #[1]⟩ : Preimage) = (⟨ByteArray.empty⟩ : Preimage) :=
    hall sha256 k hk ⟨ByteArray.mk #[1]⟩ rfl
  have hne : (⟨ByteArray.mk #[1]⟩ : Preimage) ≠ ⟨ByteArray.empty⟩ := by
    decide
  exact hne hbad

end LnLean.Proofs.WaveE.E31

/-! ## The exact catalog target -/

namespace LnLean.Payment

/-- The catalog target `LnLean.Payment.Keysend.preimage_binding` for
`LN-PM-006`.  See `waveE_e31_preimage_binding` for the full family and the
report for the exact reading. -/
theorem Keysend.preimage_binding
    (sha256 : Preimage → PaymentHash) (k : Keysend) (hk : k.Valid sha256) :
    sha256 k.preimage = k.session.paymentHash ∧
      (∀ (os : List PaymentState) {p : Preimage},
        (k.applyOutcomes os).revealedPreimage = some p →
          p = k.preimage ∧ sha256 p = k.session.paymentHash) :=
  LnLean.Proofs.WaveE.E31.waveE_e31_preimage_binding sha256 k hk

end LnLean.Payment
