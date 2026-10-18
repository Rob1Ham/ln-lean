/-
# E06 — Commitment signatures verify under the counterparty funding key

**Catalog claim (LN-CR-002).**  Commitment signatures verify under the
counterparty funding key, relying on assumption C3 (ECDSA EUF-CMA).
**BOLT anchor.**  BOLT 3 §Commitment Transaction Construction.
**rust-lightning anchor.**  `lightning/src/ln/chan_utils.rs:1450`.

This module connects the channel record (`Channel.Types`) to the
commitment-domain verifier of `Crypto.Sig`.  From the local endpoint's point of
view, a commitment transaction broadcast by the counterparty must carry a
signature over the BOLT 3 commitment sighash, checked against the
*counterparty's* funding public key (`remoteEndpoint.fundingPubKey`).  The
module:

1. defines that check as a total `Bool` predicate and proves its definitional
   seam (it is exactly `M.ecdsaVerify` on `commitmentTag ++ sighash` under the
   counterparty funding key);
2. proves, unconditionally from the model's `ecdsa_eufCma` field (assumption
   C3), that one accepted signature determines at most one commitment sighash,
   and hence cannot be replayed across commitment numbers when the sighash
   function separates them;
3. isolates the two extra properties the literal English sentence needs but
   the model does not contain: (a) *key attribution* — that acceptance under
   the counterparty key says something about the counterparty rather than an
   arbitrary key, which needs an explicit `KeyBinding` hypothesis because
   `EufCma` does not bind a signature to a key; and (b) *honest-signature
   completeness* — that a signature actually produced by the counterparty is
   accepted, which needs a signing function and a correctness law that
   `PrimitiveModel` does not provide;
4. mechanises a counterexample showing (a) is not derivable from C3: an
   EUF-CMA verifier that ignores its key exists.

**Not modelled.**  The BOLT 3 sighash serialization and tagged hashing, key
derivation from funding basepoints, secp256k1 signing/verification,
secret-key ownership, the 2-of-2 funding witness, and the per-HTLC signature
list.  The commitment sighash is passed to the predicate as an explicit
`ByteArray`.
-/

import LnLean.Crypto.Hash
import LnLean.Crypto.Model
import LnLean.Crypto.Sig
import LnLean.Wire.BigSize
import LnLean.Wire.TLV
import LnLean.Wire.Message
import LnLean.Channel.Types
import LnLean.Protocol.Messages

namespace LnLean.Proofs.WaveE.E06

set_option autoImplicit false

open LnLean
open LnLean.Crypto
open LnLean.Channel
open LnLean.Protocol

/-! ## The counterparty funding key and the commitment check -/

/-- The funding public key of the counterparty, from the local endpoint's
point of view.  BOLT 2 puts this key in the counterparty's `open_channel` /
`accept_channel`; BOLT 3 uses it to sign and to check both commitment
transactions. -/
def counterpartyFundingKey (c : Channel) : PubKey :=
  c.remoteEndpoint.fundingPubKey

/-- The local endpoint's own funding public key. -/
def localFundingKey (c : Channel) : PubKey :=
  c.localEndpoint.fundingPubKey

/-- **The commitment-signature check.**  A commitment signature is accepted
when the commitment-domain verifier (`Crypto.Sig.verifyCommitment`) accepts it
under the counterparty's funding key on the supplied commitment sighash. -/
def verifyCounterpartyCommitment (M : PrimitiveModel) (c : Channel)
    (sighash : ByteArray) (sig : EcdsaSig) : Bool :=
  verifyCommitment M (counterpartyFundingKey c) sighash sig

/-- The same check applied to the main signature field of a BOLT 2
`commitment_signed` message.  (`htlcSignatures` are a list paired with HTLC
transaction sighashes and are outside this module's scope.) -/
def verifyCommitmentSigned (M : PrimitiveModel) (c : Channel)
    (sighash : ByteArray) (m : CommitmentSigned) : Bool :=
  verifyCounterpartyCommitment M c sighash m.signature

/-- The two keys are the channel's two funding keys; this is a definitional
unfolding lemma used by the statements below. -/
theorem waveE_e06_keys_def (c : Channel) :
    counterpartyFundingKey c = c.remoteEndpoint.fundingPubKey ∧
      localFundingKey c = c.localEndpoint.fundingPubKey :=
  ⟨rfl, rfl⟩

/-! ## 1. Definitional seam: the check is `ecdsaVerify` under that key -/

/-- **Seam.**  The channel-level commitment check is exactly the model's ECDSA
verifier applied to the commitment-tagged sighash under the counterparty
funding key.  This is a checked (`rfl`) statement: there is no hidden key
selection, tag, or normalization between the catalog target
`LnLean.Crypto.Sig.ecdsaVerify` and the channel-level predicate. -/
theorem waveE_e06_counterparty_commitment_check_seam
    (M : PrimitiveModel) (c : Channel) (sighash : ByteArray)
    (sig : EcdsaSig) :
    verifyCounterpartyCommitment M c sighash sig =
      M.ecdsaVerify c.remoteEndpoint.fundingPubKey
        (commitmentTag ++ sighash) sig :=
  rfl

/-- The seam as an `iff`, for callers that reason propositionally. -/
theorem waveE_e06_counterparty_commitment_check_iff
    (M : PrimitiveModel) (c : Channel) (sighash : ByteArray)
    (sig : EcdsaSig) :
    verifyCounterpartyCommitment M c sighash sig = true ↔
      M.ecdsaVerify c.remoteEndpoint.fundingPubKey
        (commitmentTag ++ sighash) sig = true :=
  Iff.rfl

/-- Acceptance under the counterparty funding key exposes the exact primitive
call: the key is the counterparty's, the message is commitment-tagged, and the
signature is unchanged. -/
theorem waveE_e06_counterparty_commitment_accepts_iff
    (M : PrimitiveModel) (c : Channel) (sighash : ByteArray)
    (sig : EcdsaSig) :
    verifyCounterpartyCommitment M c sighash sig = true ↔
      M.ecdsaVerify (c.remoteEndpoint.fundingPubKey)
        (commitmentTag ++ sighash) sig = true :=
  Iff.rfl

/-- `commitment_signed` acceptance is the main-signature check. -/
theorem waveE_e06_commitment_signed_check_def
    (M : PrimitiveModel) (c : Channel) (sighash : ByteArray)
    (m : CommitmentSigned) :
    verifyCommitmentSigned M c sighash m =
      verifyCounterpartyCommitment M c sighash m.signature :=
  rfl

/-! ## 2. C3 (EUF-CMA) gives digest binding, unconditionally

`PrimitiveModel.ecdsa_eufCma` is a field, so no theorem below needs to assume
EUF-CMA: every model carries it.  The consequences are still conditional on
the model's idealised reading of EUF-CMA as exact message binding. -/

/-- **Commitment signatures bind the sighash.**  Under the counterparty
funding key, one signature cannot verify for two distinct commitment
sighashes.  This is assumption C3 consumed directly through
`verifyCommitment_message_bound`. -/
theorem waveE_e06_counterparty_commitment_sig_binds_digest
    (M : PrimitiveModel) (c : Channel) {sighash₁ sighash₂ : ByteArray}
    {sig : EcdsaSig}
    (h₁ : verifyCounterpartyCommitment M c sighash₁ sig = true)
    (h₂ : verifyCounterpartyCommitment M c sighash₂ sig = true) :
    sighash₁ = sighash₂ := by
  have h₁' : verifyCommitment M (counterpartyFundingKey c) sighash₁ sig = true :=
    h₁
  have h₂' : verifyCommitment M (counterpartyFundingKey c) sighash₂ sig = true :=
    h₂
  exact verifyCommitment_message_bound M M.ecdsa_eufCma h₁' h₂'

/-- **The same binding on the wire message.**  A received `commitment_signed`
whose main signature is accepted for two sighashes forces those sighashes to
coincide, so the message cannot be reinterpreted as signing a different
commitment transaction. -/
theorem waveE_e06_commitment_signed_sig_binds_digest
    (M : PrimitiveModel) (c : Channel) {sighash₁ sighash₂ : ByteArray}
    {m : CommitmentSigned}
    (h₁ : verifyCommitmentSigned M c sighash₁ m = true)
    (h₂ : verifyCommitmentSigned M c sighash₂ m = true) :
    sighash₁ = sighash₂ :=
  waveE_e06_counterparty_commitment_sig_binds_digest M c
    (sighash₁ := sighash₁) (sighash₂ := sighash₂) (sig := m.signature) h₁ h₂

/-- **A verified signature is false for every other sighash.**  This is the
"not merely does not succeed" form: at most one digest is accepted by a fixed
(signature, key) pair. -/
theorem waveE_e06_counterparty_commitment_other_digest_false
    (M : PrimitiveModel) (c : Channel) {sighash₁ sighash₂ : ByteArray}
    {sig : EcdsaSig}
    (h₁ : verifyCounterpartyCommitment M c sighash₁ sig = true)
    (hne : sighash₂ ≠ sighash₁) :
    verifyCounterpartyCommitment M c sighash₂ sig = false := by
  cases h₂ : verifyCounterpartyCommitment M c sighash₂ sig with
  | false => rfl
  | true =>
      exact absurd
        (waveE_e06_counterparty_commitment_sig_binds_digest M c h₂ h₁) hne

/-! ## 3. Anti-replay across commitment numbers

BOLT 3's commitment sighash depends on the commitment number (via the
obscuring factor and the transaction body).  The model does not contain that
serialization, so the dependency is an explicit injectivity hypothesis on a
supplied sighash family. -/

/-- **No replay across commitment numbers.**  If the supplied commitment
sighash separates commitment numbers, then one counterparty signature cannot
be accepted for two different numbers.  The only gap versus BOLT 3 is the
hypothesis `Function.Injective sighash`: the sighash construction itself is not
in `PrimitiveModel`. -/
theorem waveE_e06_counterparty_commitment_no_replay_across_numbers
    (M : PrimitiveModel) (c : Channel) (sighash : Nat → ByteArray)
    (hinj : Function.Injective sighash) {n m : Nat} {sig : EcdsaSig}
    (h₁ : verifyCounterpartyCommitment M c (sighash n) sig = true)
    (h₂ : verifyCounterpartyCommitment M c (sighash m) sig = true) :
    n = m :=
  hinj (waveE_e06_counterparty_commitment_sig_binds_digest M c h₁ h₂)

/-! ## 4. Key attribution needs more than C3

`EufCma` as defined in `Crypto.Model` quantifies over a key but only binds the
message: the same signature for the same message may verify under two keys.
The English claim names the *counterparty's* key, so an extra key-binding
hypothesis is required for any attribution statement. -/

/-- Explicit key binding for an ECDSA verifier: acceptance of one signature
and message under two keys forces the keys to be equal.  This is **not** the
model's `EufCma` field (see the counterexample below). -/
def KeyBinding (verify : PubKey → ByteArray → EcdsaSig → Bool) : Prop :=
  ∀ (pk₁ pk₂ : PubKey) (msg : ByteArray) (sig : EcdsaSig),
    verify pk₁ msg sig = true → verify pk₂ msg sig = true → pk₁ = pk₂

/-- Under explicit key binding, acceptance under both the counterparty and the
local funding key for the same sighash forces the two funding keys to be
equal. -/
theorem waveE_e06_counterparty_commitment_key_determinism
    (M : PrimitiveModel) (c : Channel) (hkb : KeyBinding M.ecdsaVerify)
    {sighash : ByteArray} {sig : EcdsaSig}
    (hremote : verifyCounterpartyCommitment M c sighash sig = true)
    (hlocal : verifyCommitment M (localFundingKey c) sighash sig = true) :
    counterpartyFundingKey c = localFundingKey c :=
  hkb (counterpartyFundingKey c) (localFundingKey c)
    (commitmentTag ++ sighash) sig hremote hlocal

/-- **A counterparty signature is not a local signature**, when the two
funding keys differ and key binding is assumed.  This is the precise form of
"under the counterparty funding key" that the model supports. -/
theorem waveE_e06_counterparty_commitment_sig_not_local
    (M : PrimitiveModel) (c : Channel) (hkb : KeyBinding M.ecdsaVerify)
    (hne : counterpartyFundingKey c ≠ localFundingKey c)
    {sighash : ByteArray} {sig : EcdsaSig}
    (hremote : verifyCounterpartyCommitment M c sighash sig = true) :
    verifyCommitment M (localFundingKey c) sighash sig = false := by
  cases hlocal : verifyCommitment M (localFundingKey c) sighash sig with
  | false => rfl
  | true =>
      exact absurd
        (waveE_e06_counterparty_commitment_key_determinism M c hkb hremote hlocal)
        hne

/-- **Counterexample: C3 does not imply key binding.**  A verifier that
accepts exactly one fixed digest and ignores both the key and the signature is
EUF-CMA, yet the same accepted (digest, signature) verifies under two distinct
public keys.  Therefore the key-attribution half of LN-CR-002 cannot be
derived from assumption C3 alone; it needs `KeyBinding` or an equivalent
model field. -/
def waveE_e06_single_digest_verify (d₀ : ByteArray) :
    PubKey → ByteArray → EcdsaSig → Bool :=
  fun _ m _ => decide (m = d₀)

/-- A single-digest verifier is EUF-CMA: two accepted messages are both the
fixed digest. -/
theorem waveE_e06_eufCma_single_digest (d₀ : ByteArray) :
    EufCma (waveE_e06_single_digest_verify d₀) := by
  intro pk m₁ m₂ s h₁ h₂
  simp only [waveE_e06_single_digest_verify, decide_eq_true_eq] at h₁ h₂
  rw [h₁, h₂]

/-- C3 alone does not give key binding: the single-digest verifier accepts
under two distinct public keys. -/
theorem waveE_e06_eufCma_not_keyBinding (d₀ : ByteArray) :
    ¬ KeyBinding (waveE_e06_single_digest_verify d₀) := by
  intro hkb
  have h₁ : waveE_e06_single_digest_verify d₀ ⟨ByteArray.empty⟩ d₀
      ⟨ByteArray.empty⟩ = true := by
    simp [waveE_e06_single_digest_verify]
  have h₂ : waveE_e06_single_digest_verify d₀ ⟨ByteArray.mk #[0x00]⟩ d₀
      ⟨ByteArray.empty⟩ = true := by
    simp [waveE_e06_single_digest_verify]
  have hEq : (⟨ByteArray.empty⟩ : PubKey) = ⟨ByteArray.mk #[0x00]⟩ :=
    hkb ⟨ByteArray.empty⟩ ⟨ByteArray.mk #[0x00]⟩ d₀ ⟨ByteArray.empty⟩ h₁ h₂
  have hs : (⟨ByteArray.empty⟩ : PubKey).bytes.size =
      (⟨ByteArray.mk #[0x00]⟩ : PubKey).bytes.size :=
    congrArg (fun p : PubKey => p.bytes.size) hEq
  exact absurd hs (by decide)

/-! ## 5. Honest-signature completeness needs a signing law

The model has no `ecdsaSign` operation and no correctness field saying that a
signature produced with a key is accepted by `ecdsaVerify`.  The literal
reading "commitment signatures verify" (every honest counterparty signature is
accepted) is therefore not provable from `PrimitiveModel`; the strongest
available form takes the signing law as an explicit hypothesis. -/

/-- A signing function together with the missing correctness law: every
signature it produces verifies under the corresponding public key.  The
secret key is not modelled, so `sign` is keyed directly by the public key. -/
def SigningCompleteness (M : PrimitiveModel)
    (sign : PubKey → ByteArray → EcdsaSig) : Prop :=
  ∀ (pk : PubKey) (msg : ByteArray), M.ecdsaVerify pk msg (sign pk msg) = true

/-- **Completeness, conditionally.**  If the model had a signing law, then the
counterparty's signature over a commitment sighash would be accepted by the
channel-level check under its funding key.  This is the exact added premise
needed for the positive direction of LN-CR-002. -/
theorem waveE_e06_counterparty_commitment_verifies_of_signing
    (M : PrimitiveModel) (sign : PubKey → ByteArray → EcdsaSig)
    (hsign : SigningCompleteness M sign) (c : Channel) (sighash : ByteArray) :
    verifyCounterpartyCommitment M c sighash
      (sign (counterpartyFundingKey c) (commitmentTag ++ sighash)) = true := by
  show M.ecdsaVerify (counterpartyFundingKey c) (commitmentTag ++ sighash)
    (sign (counterpartyFundingKey c) (commitmentTag ++ sighash)) = true
  exact hsign _ _

/-- The same completeness statement on the `commitment_signed` wrapper. -/
theorem waveE_e06_commitment_signed_verifies_of_signing
    (M : PrimitiveModel) (sign : PubKey → ByteArray → EcdsaSig)
    (hsign : SigningCompleteness M sign) (c : Channel) (sighash : ByteArray)
    (m : CommitmentSigned) :
    verifyCommitmentSigned M c sighash
      { m with
        signature := sign (counterpartyFundingKey c) (commitmentTag ++ sighash) } =
      true :=
  waveE_e06_counterparty_commitment_verifies_of_signing M sign hsign c sighash

/-! ## 6. Summary obligations -/

/-- Bundled reading of LN-CR-002: the channel-level commitment check uses the
counterparty funding key and the commitment domain; C3 gives digest binding;
the remaining attribution/completeness directions are exactly the hypotheses
named in this module. -/
theorem waveE_e06_summary
    (M : PrimitiveModel) (c : Channel) (sighash : ByteArray) (sig : EcdsaSig) :
    (verifyCounterpartyCommitment M c sighash sig = true ↔
        M.ecdsaVerify c.remoteEndpoint.fundingPubKey
          (commitmentTag ++ sighash) sig = true) ∧
      (∀ (sighash' : ByteArray),
        verifyCounterpartyCommitment M c sighash sig = true →
        verifyCounterpartyCommitment M c sighash' sig = true →
        sighash = sighash') ∧
      (KeyBinding M.ecdsaVerify →
        counterpartyFundingKey c ≠ localFundingKey c →
        verifyCounterpartyCommitment M c sighash sig = true →
        verifyCommitment M (localFundingKey c) sighash sig = false) :=
  ⟨waveE_e06_counterparty_commitment_check_iff M c sighash sig,
    fun _sighash' h h' =>
      waveE_e06_counterparty_commitment_sig_binds_digest M c h h',
    fun hkb hne h =>
      waveE_e06_counterparty_commitment_sig_not_local M c hkb hne h⟩

-- OBLIGATION: LN-WE-E06

end LnLean.Proofs.WaveE.E06
