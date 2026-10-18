/-
# Protocol signing targets — `funding_signed` completeness and attribution

**Catalog row.**  `LN-PR-003`: "`funding_signed` carries a valid signature over
the funding transaction."

The existing wrapper `LnLean.Protocol.Handshake.funding_signed_valid`
(`LnLean/Proofs/ProtocolTargets.lean`) is only an `iff` characterization of the
checked predicate `WaveE.E19.fundingSignedValid`:

```lean
fundingSignedValid M fundingKey fundingTx m ↔
  wireSigOK m.signature.bytes = true ∧
    fundingSignedVerifies M fundingKey fundingTx m
```

That characterization leaves two things implicit.

1. **Signing completeness.**  Nothing says that a signature *produced by an
   honest signer* is accepted.  `PrimitiveModel` has no `ecdsaSign` operation
   and no correctness law; C3 (`EufCma`) is only message binding for a fixed
   key and signature.  It cannot manufacture an accepted signature.
2. **Key attribution.**  `FundingSigned` is `{ channelId, signature }`
   (`LnLean/Protocol/Messages.lean`).  It has **no funding-public-key field**
   and **no funding-transaction / signed-txid field**.  At the channel level
   BOLT 2 knows the expected key from `accept_channel.funding_pubkey`, but
   `HandshakeState` stores only boolean milestones and `handshakeStep`'s
   `sendFundingSigned` / `recvFundingSigned` events carry no message payload,
   so the model never connects a `FundingSigned` value to a key.  The exact
   missing fields are:
   * `fundingPubKey : PubKey` (or an equivalent `signerKey` attribution field)
     on the record/channel context, and
   * `fundingTx : ByteArray` (or BOLT 2's derived txid) on that context.
   `PrimitiveModel` additionally lacks `ecdsaSign` and its correctness law.

C3 alone gives neither.  `LnLean.Crypto.eufCma_not_keyBinding` and
`LnLean.Proofs.WaveE.E06.waveE_e06_eufCma_not_keyBinding` exhibit an EUF-CMA
verifier that ignores its key, and the final section of this module builds a
full `PrimitiveModel` around that verifier on which one wire-shaped
`funding_signed` verifies under two distinct keys.

## What this module adds

* `FundingSigningLaw M` — the missing signing interface: a signing function,
  a verification-correctness law, and a BOLT wire-shape law.
* `FundingSignedProducedBy law m key tx` — the explicit attribution
  certificate for the missing key/transaction fields: `m.signature` is exactly
  `law.sign key (fundingTag ++ tx)`.
* `funding_signed_valid_of_produced` — completeness: a record produced under
  `key` over `tx` is `fundingSignedValid` for `key` and `tx`.
* `funding_signed_attribution` — under the independent `Crypto.KeyBinding`
  hypothesis, any key under which that record validates equals the producing
  key.  This is the key-attribution half; it is *not* derived from C3.
* `funding_signed_binds_tx_of_produced` — C3 message binding then pins the
  funding transaction: a produced record cannot also validate over a different
  transaction.
* `funding_signed_signing_contract` — the bundled faithful contract.
* `honestFundingSigned_wellFormed` — the produced record is also wire
  well-formed when its channel id is 32 bytes.
* `funding_signed_attribution_not_from_eufCma` — the negative result that C3
  alone does not give key attribution for `funding_signed`.

**BOLT sections.**  BOLT 2 §The `funding_created` Message and §The
`funding_signed` Message; BOLT 1 §Lightning Message Format (`signature`).

**Not modelled.**  secp256k1 signing, RFC6979 nonces, DER encoding,
secret-key ownership, the BOLT 2 `funding_pubkey` channel state, and the BOLT 3
sighash/txid construction.  The signing function is keyed directly by the
public key, exactly as in `LnLean.Proofs.WaveE.E06.SigningCompleteness`; this
is an interface stand-in, not a claim that a public key can sign.
-/

import LnLean.Proofs.WaveE.E06
import LnLean.Proofs.WaveE.E19

set_option autoImplicit false

namespace LnLean.Protocol.Handshake

open LnLean
open LnLean.Protocol
open LnLean.Channel
open LnLean.Crypto
open LnLean.Proofs.WaveE.E19

/-! ## 1. The missing signing interface -/

/-- The signing interface that `PrimitiveModel` does not provide.

`sign` is keyed by the public key because the model has no secret-key type
(the same convention as `LnLean.Proofs.WaveE.E06.SigningCompleteness`).
`verifies` is the missing signing-correctness law, and `wire` records that an
honest signature has one of BOLT 1's two accepted representations.  Neither is
a consequence of `EufCma`: C3 binds a message to a signature under a fixed key;
it does not produce signatures. -/
structure FundingSigningLaw (M : PrimitiveModel) where
  /-- The honest signing operation, keyed by the signer's public key. -/
  sign : PubKey → ByteArray → EcdsaSig
  /-- Correctness: every honestly produced signature is accepted by the
  model's ECDSA verifier for the signed (tagged) message. -/
  verifies : ∀ (pk : PubKey) (msg : ByteArray),
    M.ecdsaVerify pk msg (sign pk msg) = true
  /-- Wire shape: every honestly produced signature is a BOLT 1 compact
  64-byte signature or a BOLT 3 71--73-byte DER envelope. -/
  wire : ∀ (pk : PubKey) (msg : ByteArray),
    wireSigOK (sign pk msg).bytes = true

/-- **The attribution certificate.**  A `funding_signed` record was produced
by `fundingKey` over `fundingTx` exactly when its signature is the honest
signature of the funding-tagged transaction under that key.

This predicate supplies the two fields the wave-A record lacks: the key
attribution and the funding-transaction identity.  It is a predicate over the
record, not a field of `FundingSigned`, so the wire type stays unchanged. -/
def FundingSignedProducedBy {M : PrimitiveModel} (law : FundingSigningLaw M)
    (m : FundingSigned) (fundingKey : PubKey) (fundingTx : ByteArray) : Prop :=
  m.signature = law.sign fundingKey (fundingTag ++ fundingTx)

/-- An honest `funding_signed` record, built by signing the funding-tagged
transaction under the counterparty funding key.  The channel id is explicit
because the wave-A record carries it but the signing law does not determine it. -/
def honestFundingSigned {M : PrimitiveModel} (law : FundingSigningLaw M)
    (channelId : ChannelId) (fundingKey : PubKey)
    (fundingTx : ByteArray) : FundingSigned where
  channelId := channelId
  signature := law.sign fundingKey (fundingTag ++ fundingTx)

/-- The honest record satisfies the attribution certificate definitionally. -/
theorem honestFundingSigned_produced {M : PrimitiveModel}
    (law : FundingSigningLaw M) (channelId : ChannelId)
    (fundingKey : PubKey) (fundingTx : ByteArray) :
    FundingSignedProducedBy law
      (honestFundingSigned law channelId fundingKey fundingTx)
      fundingKey fundingTx :=
  rfl

/-! ## 2. Completeness: produced signatures validate -/

/-- **Signing completeness for `funding_signed`.**  If a record was produced
under `fundingKey` over `fundingTx`, then it is `fundingSignedValid` under that
same key and transaction.  The two conjuncts are exactly the two extra laws of
`FundingSigningLaw`; no cryptographic assumption is consumed. -/
theorem funding_signed_valid_of_produced {M : PrimitiveModel}
    (law : FundingSigningLaw M) {m : FundingSigned} {fundingKey : PubKey}
    {fundingTx : ByteArray}
    (hprod : FundingSignedProducedBy law m fundingKey fundingTx) :
    fundingSignedValid M fundingKey fundingTx m := by
  rw [waveE_e19_funding_signed_valid_iff]
  constructor
  · rw [hprod]
    exact law.wire fundingKey (fundingTag ++ fundingTx)
  · show M.ecdsaVerify fundingKey (fundingTag ++ fundingTx) m.signature = true
    rw [hprod]
    exact law.verifies fundingKey (fundingTag ++ fundingTx)

/-- The honest record is valid over its funding transaction. -/
theorem funding_signed_valid_of_honest {M : PrimitiveModel}
    (law : FundingSigningLaw M) (channelId : ChannelId)
    (fundingKey : PubKey) (fundingTx : ByteArray) :
    fundingSignedValid M fundingKey fundingTx
      (honestFundingSigned law channelId fundingKey fundingTx) :=
  funding_signed_valid_of_produced law
    (honestFundingSigned_produced law channelId fundingKey fundingTx)

/-! ## 3. Key attribution and transaction binding -/

/-- **Key attribution for a produced record.**  Under the independent
`Crypto.KeyBinding` hypothesis, if the honest record validates under any
claimed key, that key is the producing key.  `KeyBinding` is *not* implied by
C3 (`LnLean.Crypto.eufCma_not_keyBinding`); it is the explicit extra model
field that the `FundingSigned` record lacks.

The proof uses completeness of the honest signature and then key binding on the
tagged funding message.  It does not claim that a valid signature proves the
signer owns the key in a computational sense; it proves that the key is unique
among the model's accepting keys. -/
theorem funding_signed_attribution {M : PrimitiveModel}
    (law : FundingSigningLaw M) (hkb : KeyBinding M.ecdsaVerify)
    {m : FundingSigned} {fundingKey fundingKey' : PubKey}
    {fundingTx : ByteArray}
    (hprod : FundingSignedProducedBy law m fundingKey fundingTx)
    (hvalid : fundingSignedValid M fundingKey' fundingTx m) :
    fundingKey' = fundingKey := by
  have hclaim : verifyFunding M fundingKey' fundingTx m.signature = true :=
    waveE_e19_funding_signed_valid_sound M fundingKey' fundingTx m hvalid
  have hhonest : verifyFunding M fundingKey fundingTx m.signature = true := by
    show M.ecdsaVerify fundingKey (fundingTag ++ fundingTx) m.signature = true
    rw [hprod]
    exact law.verifies fundingKey (fundingTag ++ fundingTx)
  exact hkb fundingKey' fundingKey (fundingTag ++ fundingTx)
    m.signature hclaim hhonest

/-- **Transaction binding for a produced record.**  The model's ECDSA
message-binding field (assumption C3) pins the funding transaction: a produced
record cannot also validate over a different transaction for the same key. -/
theorem funding_signed_binds_tx_of_produced {M : PrimitiveModel}
    (law : FundingSigningLaw M) {m : FundingSigned} {fundingKey : PubKey}
    {fundingTx fundingTx' : ByteArray}
    (hprod : FundingSignedProducedBy law m fundingKey fundingTx)
    (hvalid : fundingSignedValid M fundingKey fundingTx' m) :
    fundingTx' = fundingTx :=
  (waveE_e19_funding_signed_valid_binds_tx M M.ecdsa_eufCma
    (tx₁ := fundingTx) (tx₂ := fundingTx') (m := m)
    (fundingKey := fundingKey)
    (funding_signed_valid_of_produced law hprod) hvalid).symm

/-- **The bundled faithful contract for LN-PR-003.**  For an honest
`funding_signed` record produced by `fundingKey` over `fundingTx`:

1. it carries a BOLT-wire-shaped signature;
2. it is `fundingSignedValid` under `fundingKey` and `fundingTx`;
3. under `KeyBinding`, any key that also validates it is `fundingKey`;
4. under C3, any transaction that it also validates over is `fundingTx`.

Parts 1--2 are signing completeness; part 3 is key attribution; part 4 is the
already-proved C3 binding.  The contract is conditional on the explicit
signing law and on `KeyBinding`; it does not claim that C3 alone establishes
either. -/
theorem funding_signed_signing_contract {M : PrimitiveModel}
    (law : FundingSigningLaw M) (hkb : KeyBinding M.ecdsaVerify)
    (channelId : ChannelId) (fundingKey : PubKey) (fundingTx : ByteArray) :
    let m := honestFundingSigned law channelId fundingKey fundingTx
    wireSigOK m.signature.bytes = true ∧
      fundingSignedValid M fundingKey fundingTx m ∧
      (∀ fundingKey' : PubKey,
        fundingSignedValid M fundingKey' fundingTx m → fundingKey' = fundingKey) ∧
      (∀ fundingTx' : ByteArray,
        fundingSignedValid M fundingKey fundingTx' m → fundingTx' = fundingTx) := by
  dsimp only
  refine ⟨?_, funding_signed_valid_of_honest law channelId fundingKey fundingTx,
    ?_, ?_⟩
  · exact law.wire fundingKey (fundingTag ++ fundingTx)
  · intro fundingKey' hvalid
    exact funding_signed_attribution law hkb
      (honestFundingSigned_produced law channelId fundingKey fundingTx) hvalid
  · intro fundingTx' hvalid
    exact funding_signed_binds_tx_of_produced law
      (honestFundingSigned_produced law channelId fundingKey fundingTx) hvalid

/-- The contract instantiated at a channel's counterparty funding key.  This
is the form in which a local endpoint checks the received `funding_signed`:
the producing key is `LnLean.Proofs.WaveE.E06.counterpartyFundingKey c`. -/
theorem counterparty_funding_signed_signing_contract {M : PrimitiveModel}
    (law : FundingSigningLaw M) (hkb : KeyBinding M.ecdsaVerify)
    (c : Channel) (channelId : ChannelId) (fundingTx : ByteArray) :
    let m := honestFundingSigned law channelId
      (LnLean.Proofs.WaveE.E06.counterpartyFundingKey c) fundingTx
    wireSigOK m.signature.bytes = true ∧
      fundingSignedValid M
        (LnLean.Proofs.WaveE.E06.counterpartyFundingKey c) fundingTx m ∧
      (∀ fundingKey' : PubKey,
        fundingSignedValid M fundingKey' fundingTx m →
        fundingKey' = LnLean.Proofs.WaveE.E06.counterpartyFundingKey c) ∧
      (∀ fundingTx' : ByteArray,
        fundingSignedValid M
          (LnLean.Proofs.WaveE.E06.counterpartyFundingKey c) fundingTx' m →
        fundingTx' = fundingTx) :=
  funding_signed_signing_contract law hkb channelId
    (LnLean.Proofs.WaveE.E06.counterpartyFundingKey c) fundingTx

/-- **The honest record is well-formed.**  If the channel id has the BOLT 1
32-byte width, the honest `funding_signed` record passes the model's
`wellFormed` decoder predicate.  The signature-size conjunct comes from the
signing law's wire-shape law; `wellFormed` checks no cryptography. -/
theorem honestFundingSigned_wellFormed {M : PrimitiveModel}
    (law : FundingSigningLaw M) (channelId : ChannelId)
    (hcid : channelId.Valid) (fundingKey : PubKey) (fundingTx : ByteArray) :
    wellFormed (.fundingSigned
      (honestFundingSigned law channelId fundingKey fundingTx)) := by
  rw [waveE_e19_funding_signed_wellFormed_iff]
  refine ⟨hcid, ?_⟩
  change (law.sign fundingKey (fundingTag ++ fundingTx)).bytes.size ≤ 73
  rcases wireSigOK_size (law.wire fundingKey (fundingTag ++ fundingTx)) with
    h64 | ⟨_, h73⟩
  · omega
  · exact h73

/-! ## 4. C3 alone does not give attribution

The following negative result makes the independence of `KeyBinding` concrete
for this row.  It builds a full `PrimitiveModel` whose ECDSA verifier accepts
exactly one fixed tagged message and ignores both the key and the signature.
That verifier is EUF-CMA (two accepted messages are the same fixed message),
but a wire-shaped `funding_signed` validates under two distinct keys for the
same funding transaction.  Hence the key-attribution half of the contract
cannot be obtained from the model's `EufCma` field alone. -/

/-- Replace a model's ECDSA verifier with the single-message verifier
`singleMessageVerify d₀`, which ignores the key and the signature.  The
`ecdsa_eufCma` field is re-proved, so the result is a legitimate
`PrimitiveModel`. -/
def singleMessageEcdsaModel (M : PrimitiveModel) (d₀ : ByteArray) :
    PrimitiveModel where
  sha256 := M.sha256
  hash160 := M.hash160
  ecdsaVerify := singleMessageVerify d₀
  schnorrVerify := M.schnorrVerify
  ecdh := M.ecdh
  hkdf := M.hkdf
  aeadSeal := M.aeadSeal
  aeadOpen := M.aeadOpen
  hmacSha256 := M.hmacSha256
  sha256_size := M.sha256_size
  hash160_size := M.hash160_size
  hmac_size := M.hmac_size
  sha256_collisionResistant := M.sha256_collisionResistant
  ecdsa_eufCma := eufCma_singleMessage d₀
  schnorr_eufCma := M.schnorr_eufCma
  aead_indCca := M.aead_indCca

/-- A compact 64-byte signature that passes the BOLT wire parser. -/
def wireShapedFundingSig : EcdsaSig := ⟨zeros 64⟩

/-- **C3 does not imply key attribution for `funding_signed`.**  For every
base primitive model there is a full model `M` satisfying the `EufCma` field,
a wire-shaped `funding_signed` message `m`, a funding transaction, and two
distinct keys `k₁ ≠ k₂` such that `m` is `fundingSignedValid` under both keys
over the same transaction.

The message's signature is wire-shaped, and `m` validates only because the
verifier ignores keys.  This is the exact reason `KeyBinding` is a hypothesis
of `funding_signed_attribution` and of the bundled contract. -/
theorem funding_signed_attribution_not_from_eufCma (M₀ : PrimitiveModel) :
    ∃ (M : PrimitiveModel) (fundingTx : ByteArray) (m : FundingSigned)
      (k₁ k₂ : PubKey),
      k₁ ≠ k₂ ∧
        EufCma M.ecdsaVerify ∧
        fundingSignedValid M k₁ fundingTx m ∧
        fundingSignedValid M k₂ fundingTx m := by
  let d₀ : ByteArray := fundingTag ++ zeros 0
  let M : PrimitiveModel := singleMessageEcdsaModel M₀ d₀
  let m : FundingSigned :=
    { channelId := ⟨zeros 32⟩, signature := wireShapedFundingSig }
  refine ⟨M, zeros 0, m, ⟨ByteArray.empty⟩, ⟨ByteArray.mk #[0x00]⟩,
    ?_, M.ecdsa_eufCma, ?_, ?_⟩
  · intro hEq
    have hs : (⟨ByteArray.empty⟩ : PubKey).bytes.size =
        (⟨ByteArray.mk #[0x00]⟩ : PubKey).bytes.size :=
      congrArg (fun p : PubKey => p.bytes.size) hEq
    exact absurd hs (by decide)
  · rw [waveE_e19_funding_signed_valid_iff]
    refine ⟨?_, ?_⟩
    · exact wireSigOK_accepts_any_64 _ (by decide)
    · show M.ecdsaVerify ⟨ByteArray.empty⟩ (fundingTag ++ zeros 0)
        wireShapedFundingSig = true
      simp [M, singleMessageEcdsaModel, singleMessageVerify, d₀]
  · rw [waveE_e19_funding_signed_valid_iff]
    refine ⟨?_, ?_⟩
    · exact wireSigOK_accepts_any_64 _ (by decide)
    · show M.ecdsaVerify ⟨ByteArray.mk #[0x00]⟩ (fundingTag ++ zeros 0)
        wireShapedFundingSig = true
      simp [M, singleMessageEcdsaModel, singleMessageVerify, d₀]

end LnLean.Protocol.Handshake
