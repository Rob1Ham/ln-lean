/-
# Secret-key/key-generation targets — `accept_channel.funding_pubkey` and the signer (PR-01)

**Catalog issue.**  `PR-01` (P1): `FundingSigningLaw` and `KeyBinding` are
hypotheses.  The existing signing interfaces are keyed directly by `PubKey`, so
"the honest signer" is an opaque function of the public key; there is no
secret-key or key-generation model, and the BOLT 2 `accept_channel`
`funding_pubkey` field is not connected to the key that actually signs.

**Result of this module.**

1. `LnLean.Crypto.KeyModel` supplies `SecretKey`, `KeyPair`, `KeyModel`
   (deterministic generation, secret-key signing, domain-scoped signing
   correctness), `Owns`, and `Signer`.  It is imported unchanged.
2. `AdvertisesKey K seed m` is the key-registration hypothesis that the peer's
   `accept_channel.funding_pubkey` is the public key generated from `seed`.
   Under it, the funding key used by the handshake negotiation
   (`AcceptChannel.toFundingNegotiation`) is the signer's generated key, and the
   honest `fundingTag`-domain signature verifies under
   `m.fundingPubKey`.
3. Under the existing, unchanged `LnLean.Proofs.WaveE.E06.KeyBinding`
   hypothesis, any public key that accepts that signature is
   `m.fundingPubKey`.  This is the sharpest attribution statement the model
   supports; it is not derived from C3.
4. A bridge shows the existing `FundingSigningLaw` contract still holds when a
   key model realises the law at the advertised key: the contract's signature
   is the secret key's signature, and every attribution/transaction-binding
   conclusion is preserved.
5. **Negative result.**  Key generation with two distinct key pairs, secret-key
   signing that is correct on the funding message, and C3 (`EufCma`) do *not*
   give key attribution: in a machine-checked counterexample the signature
   produced by the second key pair validates under the first key pair's public
   key, which is the `accept_channel.funding_pubkey` field.  The model also
   fails `KeyBinding`.  Hence `accept_channel.funding_pubkey` alone is not a
   proof of possession, and `KeyBinding` (or an equivalent registration game)
   remains a required hypothesis.
6. **Non-vacuity.**  A concrete pinned-key model satisfies C3, `KeyBinding`,
   the wire-shape predicate, the key model, and the attribution conclusion, so
   the positive contract is not vacuous.

**BOLT sections.**  BOLT 2 §The `open_channel` Message and §The
`accept_channel` Message (`funding_pubkey`), §The `funding_created` Message and
§The `funding_signed` Message; BOLT 1 §Lightning Message Format (`signature`).

**Not modelled.**  secp256k1 arithmetic, RFC 6979 nonces, seed entropy, key
storage, proof of possession, and a registration/ownership game.  The
`AdvertisesKey` link is an explicit hypothesis; this module proves what follows
from it and mechanises what does not follow without it.
-/

import LnLean.Crypto.KeyModel
import LnLean.Crypto.Sig
import LnLean.Protocol.Handshake
import LnLean.Proofs.Crypto.EcdsaProps
import LnLean.Proofs.ProtocolSigningTargets
import LnLean.Proofs.WaveE.E06

namespace LnLean.Proofs.Crypto.KeyModelTargets

set_option autoImplicit false

open LnLean
open LnLean.Crypto
open LnLean.Crypto.KeyModel
open LnLean.Protocol
open LnLean.Protocol.Handshake
open LnLean.Bitcoin
open LnLean.Proofs.WaveE.E19

/-! ## 1. Re-exported contract names -/

/-- The existing key-binding contract, re-exported under this module's
namespace.  It is the `LnLean.Proofs.WaveE.E06` definition, unchanged: accepting
one signature for one message under two keys forces the keys to be equal. -/
abbrev KeyBinding (verify : PubKey → ByteArray → EcdsaSig → Bool) : Prop :=
  LnLean.Proofs.WaveE.E06.KeyBinding verify

/-- The BOLT 3 wire-signature shape law for a key model.  It is separate from
`KeyModel` so that the model module stays free of proof-layer parsers. -/
def WireShaped {M : PrimitiveModel} (K : KeyModel M) : Prop :=
  ∀ (sk : SecretKey) (msg : ByteArray), wireSigOK (K.sign sk msg).bytes = true

/-! ## 2. The `accept_channel` funding key and the signer -/

/-- The `accept_channel` record that advertises `pk` as its funding key.  The
other fields are fixed to neutral values: the connection result below depends
only on `funding_pubkey`. -/
def acceptChannelWithFundingKey (pk : PubKey) : AcceptChannel where
  temporaryChannelId := ChannelId.zero
  dustLimitSatoshis := 0
  maxHtlcValueInFlightMsat := 0
  channelReserveSatoshis := 0
  htlcMinimumMsat := 0
  minimumDepth := 0
  toSelfDelay := 0
  maxAcceptedHtlcs := 0
  fundingPubKey := pk
  revocationBasepoint := pk
  paymentBasepoint := pk
  delayedPaymentBasepoint := pk
  htlcBasepoint := pk
  firstPerCommitmentPoint := pk

@[simp] theorem acceptChannelWithFundingKey_fundingPubKey (pk : PubKey) :
    (acceptChannelWithFundingKey pk).fundingPubKey = pk := rfl

/-- **Key registration.**  The peer's `accept_channel.funding_pubkey` is the
public key generated from `seed`.  This is the explicit hypothesis that the
wire field is the signer's advertised key; the negative result in §5 shows that
the field alone does not establish it. -/
def AdvertisesKey {M : PrimitiveModel} (K : KeyModel M) (seed : ByteArray)
    (m : AcceptChannel) : Prop :=
  m.fundingPubKey = K.publicOfSeed seed

/-- The advertised field is by definition the signer's generated key. -/
theorem advertisedKey_eq_generated {M : PrimitiveModel} (K : KeyModel M)
    (seed : ByteArray) (m : AcceptChannel) (h : AdvertisesKey K seed m) :
    m.fundingPubKey = K.publicOfSeed seed :=
  h

/-- The handshake negotiation reads the advertised key as `remoteFundingKey`;
under `AdvertisesKey` that field is exactly the signer's generated key. -/
theorem advertised_key_is_negotiation_key {M : PrimitiveModel} (K : KeyModel M)
    (seed : ByteArray) (m : AcceptChannel) (h : AdvertisesKey K seed m)
    (localFundingKey : PubKey) (fundingSatoshis : BtcAmount) (pushMsat : Msat)
    (temporaryChannelId : TemporaryChannelId) :
    (m.toFundingNegotiation localFundingKey fundingSatoshis pushMsat
      temporaryChannelId).remoteFundingKey = K.publicOfSeed seed := by
  rw [AcceptChannel.toFundingNegotiation_remoteFundingKey, h]

/-- **The signer's funding signature verifies under the advertised key.**  The
message is the funding-domain tagged transaction; the signature is produced by
the secret key generated from `seed`; correctness is the key model's domain
law at the funding message. -/
theorem funding_signature_valid_under_advertised_key {M : PrimitiveModel}
    (K : KeyModel M) (m : AcceptChannel) (seed : ByteArray)
    (h : AdvertisesKey K seed m) (fundingTx : ByteArray)
    (hdom : K.correctOn (fundingTag ++ fundingTx)) :
    M.ecdsaVerify m.fundingPubKey (fundingTag ++ fundingTx)
      (K.sign (K.secretOfSeed seed) (fundingTag ++ fundingTx)) = true := by
  rw [h]
  exact K.verifies_seed seed hdom

/-- **Attribution under the existing `KeyBinding` contract.**  If any key
accepts the signer's funding signature, it is the `accept_channel` funding key.
This is the key-attribution half; it consumes `KeyBinding` explicitly and does
not derive it from C3. -/
theorem funding_signature_attribution {M : PrimitiveModel} (K : KeyModel M)
    (hkb : KeyBinding M.ecdsaVerify) (m : AcceptChannel) (seed : ByteArray)
    (h : AdvertisesKey K seed m) (fundingTx : ByteArray)
    (hdom : K.correctOn (fundingTag ++ fundingTx)) {pk' : PubKey}
    (hver : M.ecdsaVerify pk' (fundingTag ++ fundingTx)
      (K.sign (K.secretOfSeed seed) (fundingTag ++ fundingTx)) = true) :
    pk' = m.fundingPubKey := by
  have hhonest :=
    funding_signature_valid_under_advertised_key K m seed h fundingTx hdom
  have hh : m.fundingPubKey = K.publicOfSeed seed := h
  have hhonest' : M.ecdsaVerify (K.publicOfSeed seed)
      (fundingTag ++ fundingTx)
      (K.sign (K.secretOfSeed seed) (fundingTag ++ fundingTx)) = true := by
    rw [hh] at hhonest
    exact hhonest
  have hEq : pk' = K.publicOfSeed seed :=
    hkb pk' (K.publicOfSeed seed) (fundingTag ++ fundingTx)
      (K.sign (K.secretOfSeed seed) (fundingTag ++ fundingTx)) hver hhonest'
  exact hEq.trans h.symm

/-- A wire-shaped key model produces a BOLT-accepted funding signature. -/
theorem funding_signature_wire_shape {M : PrimitiveModel} (K : KeyModel M)
    (hwire : WireShaped K) (seed : ByteArray) (fundingTx : ByteArray) :
    wireSigOK (K.sign (K.secretOfSeed seed)
      (fundingTag ++ fundingTx)).bytes = true :=
  hwire (K.secretOfSeed seed) (fundingTag ++ fundingTx)

/-! ## 3. Compatibility with the existing `FundingSigningLaw` contract -/

/-- A key model *realises* a `FundingSigningLaw` at a seed when the law's
signature at the generated public key is the secret-key signature.  This is the
exact missing link between the wave-A public-key-keyed interface and the
secret-key model. -/
structure RealisesFundingLaw {M : PrimitiveModel} (K : KeyModel M)
    (law : FundingSigningLaw M) (seed : ByteArray) : Prop where
  agrees : ∀ msg : ByteArray, law.sign (K.publicOfSeed seed) msg =
    K.sign (K.secretOfSeed seed) msg

/-- **The existing funding contract, grounded in a key model.**  Every
conclusion of `funding_signed_signing_contract` is preserved, and the record's
signature is identified with the secret key's signature.  The contract is not
weakened or restated: the proof invokes the existing theorem unchanged. -/
theorem funding_signed_contract_of_keyModel {M : PrimitiveModel} (K : KeyModel M)
    (law : FundingSigningLaw M) (seed : ByteArray)
    (hreal : RealisesFundingLaw K law seed)
    (hkb : KeyBinding M.ecdsaVerify) (channelId : ChannelId)
    (m : AcceptChannel) (h : AdvertisesKey K seed m) (fundingTx : ByteArray) :
    let s := honestFundingSigned law channelId m.fundingPubKey fundingTx
    s.signature = K.sign (K.secretOfSeed seed) (fundingTag ++ fundingTx) ∧
      fundingSignedValid M m.fundingPubKey fundingTx s ∧
      (∀ pk' : PubKey,
        fundingSignedValid M pk' fundingTx s → pk' = m.fundingPubKey) ∧
      (∀ tx' : ByteArray,
        fundingSignedValid M m.fundingPubKey tx' s → tx' = fundingTx) := by
  dsimp only
  have hc := funding_signed_signing_contract law hkb channelId m.fundingPubKey
    fundingTx
  dsimp only at hc
  obtain ⟨_, hvalid, hkey, htx⟩ := hc
  refine ⟨?_, hvalid, hkey, htx⟩
  show law.sign m.fundingPubKey (fundingTag ++ fundingTx) =
    K.sign (K.secretOfSeed seed) (fundingTag ++ fundingTx)
  rw [h]
  exact hreal.agrees (fundingTag ++ fundingTx)

/-! ## 4. Negative result: key generation and C3 do not attribute a signature -/

/-- The empty byte string and the one-byte zero string are distinct. -/
theorem byteArray_empty_ne_singleton :
    (ByteArray.empty : ByteArray) ≠ ByteArray.mk #[0x00] := by
  decide

/-- The one-byte zero string and the empty byte string are distinct. -/
theorem byteArray_singleton_ne_empty :
    (ByteArray.mk #[0x00] : ByteArray) ≠ ByteArray.empty := by
  decide

/-- A key model with two distinct generated pairs whose signatures are
identical: `sign` ignores the secret key and always returns the 64-byte
all-zero signature.  It is correct exactly on the single message `d₀`, which is
what the single-message verifier accepts. -/
def cheatKeyModel (M₀ : PrimitiveModel) (d₀ : ByteArray) :
    KeyModel (LnLean.Protocol.Handshake.singleMessageEcdsaModel M₀ d₀) where
  generate seed :=
    if seed.size = 0 then
      { secret := ⟨ByteArray.empty⟩, pubkey := ⟨ByteArray.empty⟩ }
    else
      { secret := ⟨ByteArray.mk #[0x00]⟩, pubkey := ⟨ByteArray.mk #[0x00]⟩ }
  sign _ _ := ⟨zeros 64⟩
  correctOn msg := msg = d₀
  verifies := by
    intro seed msg h
    simp [LnLean.Protocol.Handshake.singleMessageEcdsaModel, singleMessageVerify, h]

@[simp] theorem cheatKeyModel_public_empty (M₀ : PrimitiveModel)
    (d₀ : ByteArray) :
    (cheatKeyModel M₀ d₀).publicOfSeed ByteArray.empty =
      ⟨ByteArray.empty⟩ := by
  simp [KeyModel.publicOfSeed, cheatKeyModel]

@[simp] theorem cheatKeyModel_public_nonempty (M₀ : PrimitiveModel)
    (d₀ : ByteArray) :
    (cheatKeyModel M₀ d₀).publicOfSeed (ByteArray.mk #[0x00]) =
      ⟨ByteArray.mk #[0x00]⟩ := by
  simp only [KeyModel.publicOfSeed, cheatKeyModel]
  rw [ite_eq_right (by decide : ¬ (ByteArray.mk #[0x00] : ByteArray).size = 0)]

@[simp] theorem cheatKeyModel_secret_empty (M₀ : PrimitiveModel)
    (d₀ : ByteArray) :
    (cheatKeyModel M₀ d₀).secretOfSeed ByteArray.empty =
      ⟨ByteArray.empty⟩ := by
  simp [KeyModel.secretOfSeed, cheatKeyModel]

@[simp] theorem cheatKeyModel_secret_nonempty (M₀ : PrimitiveModel)
    (d₀ : ByteArray) :
    (cheatKeyModel M₀ d₀).secretOfSeed (ByteArray.mk #[0x00]) =
      ⟨ByteArray.mk #[0x00]⟩ := by
  simp only [KeyModel.secretOfSeed, cheatKeyModel]
  rw [ite_eq_right (by decide : ¬ (ByteArray.mk #[0x00] : ByteArray).size = 0)]

@[simp] theorem cheatKeyModel_sign (M₀ : PrimitiveModel) (d₀ : ByteArray)
    (sk : SecretKey) (msg : ByteArray) :
    (cheatKeyModel M₀ d₀).sign sk msg = ⟨zeros 64⟩ := rfl

/-- The single-message verifier does not bind keys: two distinct public keys
accept the same message and signature. -/
theorem singleMessageVerify_not_keyBinding (d₀ : ByteArray) :
    ¬ KeyBinding (singleMessageVerify d₀) := by
  intro hkb
  have h₁ : singleMessageVerify d₀ ⟨ByteArray.empty⟩ d₀
      ⟨ByteArray.empty⟩ = true := by
    simp [singleMessageVerify]
  have h₂ : singleMessageVerify d₀ ⟨ByteArray.mk #[0x00]⟩ d₀
      ⟨ByteArray.empty⟩ = true := by
    simp [singleMessageVerify]
  have hEq : (⟨ByteArray.empty⟩ : PubKey) = ⟨ByteArray.mk #[0x00]⟩ :=
    hkb ⟨ByteArray.empty⟩ ⟨ByteArray.mk #[0x00]⟩ d₀
      ⟨ByteArray.empty⟩ h₁ h₂
  have hs : (⟨ByteArray.empty⟩ : PubKey).bytes.size =
      (⟨ByteArray.mk #[0x00]⟩ : PubKey).bytes.size :=
    congrArg (fun p : PubKey => p.bytes.size) hEq
  exact absurd hs (by decide)

/-- **Key generation plus C3 does not give key attribution.**  For every base
model there are:

* a full `PrimitiveModel` satisfying `EufCma`;
* a `KeyModel` with two distinct generated key pairs `(sk₁, pk₁)` and
  `(sk₂, pk₂)`;
* an `accept_channel` message whose `funding_pubkey` is `pk₁`;
* a funding transaction on which the signer is correct;

such that the signature produced by `sk₂` is a valid funding signature under
`pk₁ = m.fundingPubKey`, and is in fact the same signature `sk₁` produces.
The model does not satisfy `KeyBinding`.  Therefore the `funding_pubkey` field
plus key generation plus C3 cannot attribute a signature to the expected key
pair; an ownership/registration hypothesis is required. -/
theorem key_generation_not_key_attribution (M₀ : PrimitiveModel) :
    ∃ (M : PrimitiveModel) (K : KeyModel M) (m : AcceptChannel)
      (seed₁ seed₂ : ByteArray) (fundingTx : ByteArray),
      K.publicOfSeed seed₁ ≠ K.publicOfSeed seed₂ ∧
        K.secretOfSeed seed₁ ≠ K.secretOfSeed seed₂ ∧
        EufCma M.ecdsaVerify ∧
        AdvertisesKey K seed₁ m ∧
        K.correctOn (fundingTag ++ fundingTx) ∧
        M.ecdsaVerify m.fundingPubKey (fundingTag ++ fundingTx)
          (K.sign (K.secretOfSeed seed₂) (fundingTag ++ fundingTx)) = true ∧
        K.sign (K.secretOfSeed seed₁) (fundingTag ++ fundingTx) =
          K.sign (K.secretOfSeed seed₂) (fundingTag ++ fundingTx) ∧
        ¬ KeyBinding M.ecdsaVerify := by
  let d₀ : ByteArray := fundingTag ++ ByteArray.empty
  let M : PrimitiveModel :=
    LnLean.Protocol.Handshake.singleMessageEcdsaModel M₀ d₀
  let K : KeyModel M := cheatKeyModel M₀ d₀
  let seed₁ : ByteArray := ByteArray.empty
  let seed₂ : ByteArray := ByteArray.mk #[0x00]
  let m : AcceptChannel := acceptChannelWithFundingKey (K.publicOfSeed seed₁)
  refine ⟨M, K, m, seed₁, seed₂, ByteArray.empty, ?_, ?_, M.ecdsa_eufCma,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro hEq
    have hs : (K.publicOfSeed seed₁).bytes.size =
        (K.publicOfSeed seed₂).bytes.size :=
      congrArg (fun p : PubKey => p.bytes.size) hEq
    simp [K, seed₁, seed₂, cheatKeyModel, byteArray_singleton_ne_empty] at hs
    exact absurd hs (by decide)
  · intro hEq
    have hs : (K.secretOfSeed seed₁).bytes.size =
        (K.secretOfSeed seed₂).bytes.size :=
      congrArg (fun sk : SecretKey => sk.bytes.size) hEq
    simp [K, seed₁, seed₂, cheatKeyModel, byteArray_singleton_ne_empty] at hs
    exact absurd hs (by decide)
  · show m.fundingPubKey = K.publicOfSeed seed₁
    rw [show m.fundingPubKey = K.publicOfSeed seed₁ from rfl]
  · show K.correctOn (fundingTag ++ ByteArray.empty)
    rfl
  · show M.ecdsaVerify m.fundingPubKey (fundingTag ++ ByteArray.empty)
      (K.sign (K.secretOfSeed seed₂) (fundingTag ++ ByteArray.empty)) = true
    simp [M, K, seed₁, seed₂, m, d₀,
      LnLean.Protocol.Handshake.singleMessageEcdsaModel, singleMessageVerify,
      acceptChannelWithFundingKey, cheatKeyModel]
  · show K.sign (K.secretOfSeed seed₁) (fundingTag ++ ByteArray.empty) =
      K.sign (K.secretOfSeed seed₂) (fundingTag ++ ByteArray.empty)
    simp [K, seed₁, seed₂, cheatKeyModel]
  · show ¬ KeyBinding M.ecdsaVerify
    exact singleMessageVerify_not_keyBinding d₀

/-! ## 5. Non-vacuity: a pinned-key witness -/

/-- A verifier that accepts exactly the fixed pair `(k₀, d₀)` and ignores the
signature bytes.  It is C3 and it is key-binding; it is a degenerate but
legitimate model. -/
def pinnedVerify (k₀ : PubKey) (d₀ : ByteArray) :
    PubKey → ByteArray → EcdsaSig → Bool :=
  fun pk msg _ => decide (pk.bytes = k₀.bytes ∧ msg = d₀)

theorem pinnedVerify_eufCma (k₀ : PubKey) (d₀ : ByteArray) :
    EufCma (pinnedVerify k₀ d₀) := by
  intro pk m₁ m₂ s h₁ h₂
  simp only [pinnedVerify, decide_eq_true_eq] at h₁ h₂
  rw [h₁.2, h₂.2]

theorem pinnedVerify_keyBinding (k₀ : PubKey) (d₀ : ByteArray) :
    KeyBinding (pinnedVerify k₀ d₀) := by
  intro pk₁ pk₂ msg sig h₁ h₂
  simp only [pinnedVerify, decide_eq_true_eq] at h₁ h₂
  have hb : pk₁.bytes = pk₂.bytes := h₁.1.trans h₂.1.symm
  cases pk₁
  cases pk₂
  simpa using hb

/-- Replace the ECDSA verifier of a base model by `pinnedVerify`; the
`EufCma` field is re-proved, so the result is a full `PrimitiveModel`. -/
def pinnedModel (M₀ : PrimitiveModel) (k₀ : PubKey) (d₀ : ByteArray) :
    PrimitiveModel :=
  { M₀ with
    ecdsaVerify := pinnedVerify k₀ d₀
    ecdsa_eufCma := pinnedVerify_eufCma k₀ d₀ }

/-- The pinned key model: one generated key pair per seed (all with the same
public key `k₀`), a constant wire-shaped signature, and completeness exactly on
`d₀`. -/
def pinnedKeyModel (M₀ : PrimitiveModel) (k₀ : PubKey) (d₀ : ByteArray) :
    KeyModel (pinnedModel M₀ k₀ d₀) where
  generate seed := { secret := ⟨seed⟩, pubkey := k₀ }
  sign _ _ := ⟨zeros 64⟩
  correctOn msg := msg = d₀
  verifies := by
    intro seed msg h
    show pinnedVerify k₀ d₀ k₀ msg ⟨zeros 64⟩ = true
    simp [pinnedVerify, h]

theorem pinnedKeyModel_wireShaped (M₀ : PrimitiveModel) (k₀ : PubKey)
    (d₀ : ByteArray) : WireShaped (pinnedKeyModel M₀ k₀ d₀) := by
  intro sk msg
  show wireSigOK (zeros 64) = true
  exact wireSigOK_accepts_compact64

/-- **The positive contract is not vacuous.**  There is a concrete model, key
model, wire-shape law, advertised `accept_channel` key, and funding message for
which C3, `KeyBinding`, key generation, signing correctness on the funding
message, and the attribution conclusion all hold. -/
theorem attribution_contract_nonvacuous (M₀ : PrimitiveModel) (k₀ : PubKey) :
    ∃ (M : PrimitiveModel) (K : KeyModel M) (m : AcceptChannel)
      (seed : ByteArray) (fundingTx : ByteArray),
      EufCma M.ecdsaVerify ∧
        KeyBinding M.ecdsaVerify ∧
        WireShaped K ∧
        AdvertisesKey K seed m ∧
        K.correctOn (fundingTag ++ fundingTx) ∧
        (∀ pk' : PubKey,
          M.ecdsaVerify pk' (fundingTag ++ fundingTx)
            (K.sign (K.secretOfSeed seed) (fundingTag ++ fundingTx)) = true →
          pk' = m.fundingPubKey) := by
  let d₀ : ByteArray := fundingTag ++ ByteArray.empty
  let M : PrimitiveModel := pinnedModel M₀ k₀ d₀
  let K : KeyModel M := pinnedKeyModel M₀ k₀ d₀
  let seed : ByteArray := ByteArray.empty
  let m : AcceptChannel := acceptChannelWithFundingKey k₀
  refine ⟨M, K, m, seed, ByteArray.empty, M.ecdsa_eufCma,
    pinnedVerify_keyBinding k₀ d₀, pinnedKeyModel_wireShaped M₀ k₀ d₀,
    ?_, ?_, ?_⟩
  · show m.fundingPubKey = K.publicOfSeed seed
    rfl
  · show K.correctOn (fundingTag ++ ByteArray.empty)
    rfl
  · intro pk' hver
    have hp : pk' = k₀ := by
      have hb : pk'.bytes = k₀.bytes := by
        simpa [M, K, seed, d₀, pinnedModel, pinnedKeyModel, pinnedVerify] using hver
      cases pk'
      cases k₀
      simpa using hb
    rw [hp]
    rfl

/-! ## 6. Why the total `FundingSigningLaw` bridge is strongly scoped -/

/-- `EufCma` plus total signing correctness makes the honest signature map
injective at each key: two equal signatures force equal messages.  This is the
reason a *total* correctness law is much stronger than the domain-scoped law of
`KeyModel`; combined with the bounded wire shapes below it is in tension with
the finiteness of 64/71--73-byte strings. -/
theorem fundingSigningLaw_sign_injective {M : PrimitiveModel}
    (law : FundingSigningLaw M) (pk : PubKey) :
    Function.Injective (law.sign pk) := by
  intro m₁ m₂ hsig
  exact M.ecdsa_eufCma pk m₁ m₂ (law.sign pk m₁)
    (law.verifies pk m₁) (by simpa [hsig] using law.verifies pk m₂)

/-- Every honest signature of a total `FundingSigningLaw` lies in the BOLT wire
size window: 64 bytes or 71--73 bytes. -/
theorem fundingSigningLaw_wire_bound {M : PrimitiveModel}
    (law : FundingSigningLaw M) (pk : PubKey) (msg : ByteArray) :
    (law.sign pk msg).bytes.size = 64 ∨
      (71 ≤ (law.sign pk msg).bytes.size ∧
        (law.sign pk msg).bytes.size ≤ 73) :=
  wireSigOK_size (law.wire pk msg)

/-! ## 7. Summary -/

/-- Bundled faithfully-scoped reading of `PR-01`:

1. under `AdvertisesKey`, the `accept_channel` funding key is the negotiation
   key and the signer's funding signature verifies under it;
2. under the existing `KeyBinding` contract, any accepting key is that key;
3. key generation + C3 alone do not give attribution (mechanised
   counterexample);
4. the positive contract has a concrete non-vacuous instance. -/
theorem key_model_summary :
    (∀ (M : PrimitiveModel) (K : KeyModel M) (seed : ByteArray)
        (m : AcceptChannel) (fundingTx : ByteArray),
        AdvertisesKey K seed m →
        K.correctOn (fundingTag ++ fundingTx) →
        M.ecdsaVerify m.fundingPubKey (fundingTag ++ fundingTx)
            (K.sign (K.secretOfSeed seed) (fundingTag ++ fundingTx)) = true) ∧
      (∀ (M : PrimitiveModel), KeyBinding M.ecdsaVerify →
        ∀ (K : KeyModel M) (seed : ByteArray) (m : AcceptChannel)
          (fundingTx : ByteArray),
          AdvertisesKey K seed m →
          K.correctOn (fundingTag ++ fundingTx) →
          ∀ pk' : PubKey,
            M.ecdsaVerify pk' (fundingTag ++ fundingTx)
              (K.sign (K.secretOfSeed seed) (fundingTag ++ fundingTx)) = true →
            pk' = m.fundingPubKey) ∧
      (∀ _M₀ : PrimitiveModel,
        ∃ (M : PrimitiveModel) (K : KeyModel M) (m : AcceptChannel)
          (seed₁ seed₂ : ByteArray) (fundingTx : ByteArray),
          K.publicOfSeed seed₁ ≠ K.publicOfSeed seed₂ ∧
            EufCma M.ecdsaVerify ∧
            AdvertisesKey K seed₁ m ∧
            M.ecdsaVerify m.fundingPubKey (fundingTag ++ fundingTx)
              (K.sign (K.secretOfSeed seed₂) (fundingTag ++ fundingTx)) = true ∧
            ¬ KeyBinding M.ecdsaVerify) ∧
      (∀ (_M₀ : PrimitiveModel) (_k₀ : PubKey),
        ∃ (M : PrimitiveModel) (K : KeyModel M) (m : AcceptChannel)
          (seed : ByteArray) (_fundingTx : ByteArray),
          EufCma M.ecdsaVerify ∧ KeyBinding M.ecdsaVerify ∧
            WireShaped K ∧ AdvertisesKey K seed m) :=
  ⟨fun _ _ _ _ _ h hdom =>
      funding_signature_valid_under_advertised_key _ _ _ h _ hdom,
    fun _ hkb _ _ _ _ h hdom _ hver =>
      funding_signature_attribution _ hkb _ _ h _ hdom hver,
    fun M₀ => by
      obtain ⟨M, K, m, s₁, s₂, tx, hp, _, he, ha, _hc, hv, _, hnk⟩ :=
        key_generation_not_key_attribution M₀
      exact ⟨M, K, m, s₁, s₂, tx, hp, he, ha, hv, hnk⟩,
    fun M₀ k₀ => by
      obtain ⟨M, K, m, s, tx, he, hkb, hw, ha, _, _⟩ :=
        attribution_contract_nonvacuous M₀ k₀
      exact ⟨M, K, m, s, tx, he, hkb, hw, ha⟩⟩

/-! ## 8. Stored `accept_channel` payload (wave 8)

Wave 8 adds `HandshakeState.acceptChannel?`, set by the payload-carrying
receive path `handshakeStepRecvAccept`.  The definition below records the exact
joint condition that the positive attribution contract needs; it is still an
explicit registration hypothesis, not a proof of possession.  The state-level
reachability and negative results are in
`LnLean.Proofs.Crypto.AcceptPayloadTargets`. -/

/-- A handshake state stores exactly the accept payload `m`, and that payload
advertises the key generated from `seed`. -/
def StoredAccept {M : PrimitiveModel} (K : KeyModel M) (seed : ByteArray)
    (s : HandshakeState) (m : AcceptChannel) : Prop :=
  s.acceptChannel? = some m ∧ AdvertisesKey K seed m

/-- The stored payload is the one named in `StoredAccept`. -/
theorem storedAccept_acceptChannel? {M : PrimitiveModel} {K : KeyModel M}
    {seed : ByteArray} {s : HandshakeState} {m : AcceptChannel}
    (h : StoredAccept K seed s m) :
    s.acceptChannel? = some m :=
  h.1

/-- The stored payload's `funding_pubkey` is the signer's generated key. -/
theorem storedAccept_fundingPubKey {M : PrimitiveModel} {K : KeyModel M}
    {seed : ByteArray} {s : HandshakeState} {m : AcceptChannel}
    (h : StoredAccept K seed s m) :
    m.fundingPubKey = K.publicOfSeed seed :=
  h.2

/-- **Attribution from a stored payload.**  Under the unchanged `KeyBinding`,
any key that accepts the signer's funding signature is the `funding_pubkey`
stored in the handshake state. -/
theorem storedAccept_attribution {M : PrimitiveModel} (K : KeyModel M)
    (hkb : KeyBinding M.ecdsaVerify) {seed : ByteArray}
    {s : HandshakeState} {m : AcceptChannel}
    (h : StoredAccept K seed s m) {fundingTx : ByteArray}
    (hdom : K.correctOn (fundingTag ++ fundingTx)) {pk' : PubKey}
    (hver : M.ecdsaVerify pk' (fundingTag ++ fundingTx)
      (K.sign (K.secretOfSeed seed) (fundingTag ++ fundingTx)) = true) :
    pk' = m.fundingPubKey :=
  funding_signature_attribution K hkb m seed h.2 fundingTx hdom hver

end LnLean.Proofs.Crypto.KeyModelTargets
