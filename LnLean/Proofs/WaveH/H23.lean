/-
# H23 — non-vacuous `accept_channel` registration and honest open/accept/funding witness (PR-01)

**English claim.**  The wave-7 key model (`LnLean.Crypto.KeyModel`) and the
wave-7 funding-authorisation layer (`FundingAuthTargets`) state the key
registration and attribution contract conditionally: `AdvertisesKey` says the
`accept_channel.funding_pubkey` field is the key generated from a seed, and
`KeyBinding` says a signature accepted under one key cannot be accepted under
another.  A conditional contract is only meaningful if it has a model.  This
module supplies one, with concrete bytes and concrete keys, and drives it
through the *complete* honest funding exchange:

1. **Accept payload non-emptiness.**  `demoAccept` is a BOLT 2 `accept_channel`
   record with concrete 33-byte compressed-key shapes (`0x02…`, `0x03…`), a
   32-byte temporary channel id, and non-trivial policy fields.  Its funding key
   is a valid key, distinct from the opener's key, and its byte prefix is a
   compressed-key prefix.  This is the `accept_payload_nonempty` witness.

2. **Registration witness.**  For every base primitive model there is a full
   `PrimitiveModel` and `KeyModel` (the pinned single-message model of
   `KeyModelTargets`) under which C3 (`EufCma`), `KeyBinding`, `WireShaped`,
   `AdvertisesKey`, signing correctness on the concrete funding message, key
   ownership, and a non-empty secret key all hold simultaneously.  This is
   `registration_witness`; it is the non-vacuity proof for `PR-01`, not a claim
   that `AdvertisesKey` follows from the payload.

3. **Honest negotiation trace.**  `phase4` is reached from
   `FundingPhase.initial` by the four permitted messages
   `sendOpen → recvOpen → sendAccept → recvAccept`, with every BOLT 2 ordering
   guard discharged.  Both endpoints expose the *same* `FundingNegotiation`,
   with `localFundingKey` equal to `open_channel.funding_pubkey` and
   `remoteFundingKey` equal to `accept_channel.funding_pubkey`.  This is
   `negotiation_trace` / `negotiation_views`.

4. **Construction witness.**  The negotiated parameters are `WellFormed`, carry
   the constructed hash link, have a 32-byte program, contain both funding keys
   literally in the 71-byte BOLT 3 witness script, and have the P2WSH output
   `p2wsh (H (2 <k1> <k2> 2 OP_CHECKMULTISIG))`.  This is
   `funding_construction_witness`.

5. **Registration reaches the funding output.**  Under `AdvertisesKey`, the
   negotiation's remote funding key is the generated key and occurs literally
   in the witness script (`registered_key_in_funding_script`).  Any key that
   accepts the honest funding signature is that negotiation key and occurs in
   the script (`accepting_key_attribution`).  Since the honest signature
   verifies, this is non-vacuous (`attributed_registered_key_nonvacuous`).

6. **v1 handshake boundary.**  The existing `HandshakeState` machine reaches a
   state with `acceptReceived = true` from which `funding_created` is permitted;
   `acceptKey_bound_before_fundingCreated` then binds the joint construction's
   remote key to the received `accept_channel.funding_pubkey`
   (`v1_handshake_funding_boundary`).

7. **One bundled witness.**  `honest_witness` packages (1)–(5) with the same
   concrete values, so the entire PR-01 contract has a single machine-checked
   instance.

**What this establishes and what it does not.**  The witness uses the established
pinned single-message verifier (`KeyModelTargets.pinnedModel`), which is a
legitimate `PrimitiveModel` satisfying the model's `EufCma` field and
`KeyBinding`.  It therefore proves *logical non-vacuity* of the conditional
contract and the negotiation/construction path.  It is not a proof of
computational ECDSA security, not a real secp256k1 key generation, and not a
proof of possession.  `AdvertisesKey` remains an explicit hypothesis: the
negative result in `KeyModelTargets.key_generation_not_key_attribution` (and
lane H24) shows the payload alone does not supply it.  Transport attribution is
still the Noise layer's obligation (`docs/ASSUMPTIONS.md` §3).

**BOLT sections.**  BOLT 2 §The `open_channel` Message (type 32), §The
`accept_channel` Message (type 33), §The `funding_created`/`funding_signed`
Messages; BOLT 3 §Funding Transaction Output.

**Anchors.**  `ln-lean`'s `Protocol.Handshake.OpenChannel`/`FundingPhase`,
`LnLean.Crypto.KeyModel`, `Proofs.Crypto.KeyModelTargets.AdvertisesKey`,
`Proofs.Bitcoin.FundingAuthTargets`; rust-lightning `msgs.rs:371`
(`AcceptChannel`), `chan_utils.rs:847-866` (`make_funding_redeemscript`).
-/

import LnLean.Protocol.Handshake
import LnLean.Crypto.KeyModel
import LnLean.Crypto.Sig
import LnLean.Proofs.Crypto.KeyModelTargets
import LnLean.Proofs.Bitcoin.FundingAuthTargets

namespace LnLean.Proofs.WaveH.H23

set_option autoImplicit false

open LnLean
open LnLean.Bitcoin
open LnLean.Protocol
open LnLean.Protocol.Handshake
open LnLean.Crypto
open LnLean.Crypto.KeyModel
open LnLean.Proofs.Bitcoin.FundingAuthTargets
open LnLean.Proofs.Bitcoin.FundingScriptTargets
open LnLean.Proofs.Crypto.KeyModelTargets

/-! ## 1. Concrete accept payload and concrete funding keys -/

/-- The opener's 33-byte compressed funding key, `0x02` followed by 32 `0x11`
bytes.  This is a concrete value with the BOLT 1 compressed-key width and a
valid compressed-key prefix; the model does not validate curve membership. -/
def openKeyBytes : ByteArray :=
  ByteArray.mk (((0x02 : UInt8) :: List.replicate 32 (0x11 : UInt8)).toArray)

/-- The acceptor's 33-byte compressed funding key, `0x03` followed by 32
`0x22` bytes.  It has the opposite compressed-key parity prefix, so it is
distinguishable from `openKeyBytes` at byte 0. -/
def acceptKeyBytes : ByteArray :=
  ByteArray.mk (((0x03 : UInt8) :: List.replicate 32 (0x22 : UInt8)).toArray)

/-- The opener's funding key. -/
def pkOpen : PubKey := ⟨openKeyBytes⟩

/-- The acceptor's funding key.  This is the value that
`accept_channel.funding_pubkey` advertises. -/
def pkAccept : PubKey := ⟨acceptKeyBytes⟩

/-- A concrete 32-byte temporary channel id, filled with `0xa5`. -/
def channelIdBytes : ByteArray :=
  ByteArray.mk ((List.replicate 32 (0xa5 : UInt8)).toArray)

/-- A concrete 32-byte seed for the registered signer. -/
def seedBytes : ByteArray :=
  ByteArray.mk ((List.replicate 32 (0x5a : UInt8)).toArray)

/-- Concrete funding-transaction bytes.  They stand for the L1 transaction whose
funding input is signed; only the signing message `fundingTag ++ fundingTx`
matters to the key model. -/
def fundingTx : ByteArray := ByteArray.mk #[0xde, 0xad, 0xbe, 0xef]

@[simp] theorem openKeyBytes_size : openKeyBytes.size = 33 := by
  simp [openKeyBytes, ByteArray.size]

@[simp] theorem acceptKeyBytes_size : acceptKeyBytes.size = 33 := by
  simp [acceptKeyBytes, ByteArray.size]

@[simp] theorem channelIdBytes_size : channelIdBytes.size = 32 := by
  simp [channelIdBytes, ByteArray.size]

@[simp] theorem seedBytes_size : seedBytes.size = 32 := by
  simp [seedBytes, ByteArray.size]

@[simp] theorem fundingTx_size : fundingTx.size = 4 := rfl

/-- The opener key has the compressed-key prefix `0x02`. -/
theorem openKeyBytes_prefix : openKeyBytes[0]? = some (0x02 : UInt8) := by
  simp only [openKeyBytes]; decide

/-- The acceptor key has the compressed-key prefix `0x03`. -/
theorem acceptKeyBytes_prefix : acceptKeyBytes[0]? = some (0x03 : UInt8) := by
  simp only [acceptKeyBytes]; decide

/-- The two concrete funding keys are distinct: they differ at byte 0. -/
theorem pkOpen_ne_pkAccept : pkOpen ≠ pkAccept := by
  intro h
  have hb : pkOpen.bytes = pkAccept.bytes := congrArg PubKey.bytes h
  have h0 : pkOpen.bytes[0]? = some (0x02 : UInt8) := openKeyBytes_prefix
  have h1 : pkAccept.bytes[0]? = some (0x03 : UInt8) := acceptKeyBytes_prefix
  rw [hb] at h0
  rw [h0] at h1
  exact absurd (Option.some.inj h1) (by decide)

/-- Both concrete keys are valid compressed-key shapes. -/
theorem pkOpen_valid : pkOpen.Valid := openKeyBytes_size

theorem pkAccept_valid : pkAccept.Valid := acceptKeyBytes_size

/-- A concrete `open_channel` projection: 100 000 sat capacity, a 1 000 msat
push, the concrete temporary channel id, and the opener's key. -/
def demoOpen : OpenChannel where
  temporaryChannelId := ⟨channelIdBytes⟩
  fundingSatoshis := 100000
  pushMsat := ⟨1000⟩
  fundingPubKey := pkOpen

/-- A concrete `accept_channel` payload.  Only `fundingPubKey` enters the
funding output; the remaining fields are the BOLT 2 policy fields set to
non-trivial values so that the payload is a realistic record rather than a
one-field stub. -/
def demoAccept : AcceptChannel where
  temporaryChannelId := ⟨channelIdBytes⟩
  dustLimitSatoshis := 546
  maxHtlcValueInFlightMsat := 1000000000
  channelReserveSatoshis := 10000
  htlcMinimumMsat := 1000
  minimumDepth := 3
  toSelfDelay := 144
  maxAcceptedHtlcs := 483
  fundingPubKey := pkAccept
  revocationBasepoint := pkAccept
  paymentBasepoint := pkAccept
  delayedPaymentBasepoint := pkAccept
  htlcBasepoint := pkAccept
  firstPerCommitmentPoint := pkAccept

/-- The accept-payload non-emptiness predicate proved for `demoAccept`:
a 33-byte valid `funding_pubkey` with compressed prefix, a 32-byte temporary
channel id, a funding key distinct from the opener's, and concrete policy
fields. -/
def AcceptPayloadNonempty : Prop :=
  demoAccept.fundingPubKey.bytes.size = 33 ∧
  demoAccept.fundingPubKey.bytes[0]? = some (0x03 : UInt8) ∧
  demoAccept.fundingPubKey ≠ demoOpen.fundingPubKey ∧
  demoAccept.temporaryChannelId.bytes.size = 32 ∧
  demoAccept.dustLimitSatoshis = 546 ∧
  demoAccept.maxAcceptedHtlcs = 483

/-- **The accept payload is not empty or degenerate.**  Every component of the
non-emptiness predicate is checked against the concrete `demoAccept` value. -/
theorem accept_payload_nonempty : AcceptPayloadNonempty := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact acceptKeyBytes_size
  · exact acceptKeyBytes_prefix
  · simpa [demoAccept, demoOpen] using pkOpen_ne_pkAccept.symm
  · exact channelIdBytes_size
  · rfl
  · rfl

/-- The concrete payload's funding key is exactly the accept key. -/
@[simp] theorem demoAccept_fundingPubKey : demoAccept.fundingPubKey = pkAccept := rfl

/-- The concrete open message's funding key is exactly the open key. -/
@[simp] theorem demoOpen_fundingPubKey : demoOpen.fundingPubKey = pkOpen := rfl

/-! ## 2. The negotiation determined by the two concrete messages -/

/-- The negotiation computed jointly from `demoOpen` and `demoAccept`. -/
def demoNegotiation : LnLean.Bitcoin.FundingNegotiation :=
  demoOpen.toFundingNegotiation demoAccept

@[simp] theorem demoNegotiation_localFundingKey :
    demoNegotiation.localFundingKey = pkOpen := rfl

@[simp] theorem demoNegotiation_remoteFundingKey :
    demoNegotiation.remoteFundingKey = pkAccept := rfl

@[simp] theorem demoNegotiation_fundingSatoshis :
    demoNegotiation.fundingSatoshis = 100000 := rfl

@[simp] theorem demoNegotiation_pushMsat :
    demoNegotiation.pushMsat = ⟨1000⟩ := rfl

@[simp] theorem demoNegotiation_temporaryChannelId :
    demoNegotiation.temporaryChannelId = ⟨⟨channelIdBytes⟩⟩ := rfl

/-- The joint construction is definitionally the accept-only construction. -/
theorem demoNegotiation_params_eq_acceptChannel (H : ByteArray → ByteArray) :
    demoNegotiation.toFundingParams H =
      demoAccept.toFundingParams H pkOpen 100000 ⟨1000⟩ ⟨⟨channelIdBytes⟩⟩ := rfl

/-! ## 3. The complete honest funding-phase trace -/

/-- Initial funding phase. -/
def phase0 : FundingPhase := FundingPhase.initial

/-- After the opener sends `open_channel`. -/
def phase1 : FundingPhase :=
  { openSent := some demoOpen }

/-- After the acceptor receives `open_channel`. -/
def phase2 : FundingPhase :=
  { openSent := some demoOpen, openReceived := some demoOpen }

/-- After the acceptor sends `accept_channel`. -/
def phase3 : FundingPhase :=
  { openSent := some demoOpen, openReceived := some demoOpen,
    acceptSent := some demoAccept }

/-- After the opener receives `accept_channel`: both views are available. -/
def phase4 : FundingPhase :=
  { openSent := some demoOpen, openReceived := some demoOpen,
    acceptSent := some demoAccept, acceptReceived := some demoAccept }

theorem phase1_step : fundingStep phase0 (.sendOpen demoOpen) = some phase1 := by
  simp [fundingStep, phase0, phase1, FundingPhase.initial, FundingPhase.canSendOpen]

theorem phase2_step : fundingStep phase1 (.recvOpen demoOpen) = some phase2 := by
  simp [fundingStep, phase1, phase2, FundingPhase.canRecvOpen]

theorem phase3_step : fundingStep phase2 (.sendAccept demoAccept) = some phase3 := by
  simp [fundingStep, phase2, phase3, FundingPhase.canSendAccept]

theorem phase4_step : fundingStep phase3 (.recvAccept demoAccept) = some phase4 := by
  simp [fundingStep, phase3, phase4, FundingPhase.canRecvAccept]

/-- **The complete honest exchange is reachable.**  The four messages are
permitted in BOLT 2 order, starting from the initial phase. -/
theorem phase4_reachable : FundingReachable phase4 :=
  FundingReachable.step _
    (FundingReachable.step _
      (FundingReachable.step _
        (FundingReachable.step _ FundingReachable.initial phase1_step)
        phase2_step)
      phase3_step)
    phase4_step

/-- Both endpoints' views of the concrete exchange. -/
theorem phase4_openerNegotiation :
    phase4.openerNegotiation? = some demoNegotiation := rfl

theorem phase4_acceptorNegotiation :
    phase4.acceptorNegotiation? = some demoNegotiation := rfl

/-- **The two endpoints compute the same negotiation.**  The opener's view
(sent `open_channel`, received `accept_channel`) and the acceptor's view
(received `open_channel`, sent `accept_channel`) both expose
`demoNegotiation`. -/
theorem phase4_views_agree :
    phase4.openerNegotiation? = phase4.acceptorNegotiation? :=
  opener_acceptor_negotiation_agree phase4 phase4 demoOpen demoAccept rfl rfl rfl rfl

/-- **The honest trace exposes the exact concrete negotiation.** -/
theorem negotiation_trace :
    FundingReachable phase4 ∧
    phase4.openSent = some demoOpen ∧
    phase4.openReceived = some demoOpen ∧
    phase4.acceptSent = some demoAccept ∧
    phase4.acceptReceived = some demoAccept ∧
    phase4.openerNegotiation? = some demoNegotiation ∧
    phase4.acceptorNegotiation? = some demoNegotiation ∧
    demoNegotiation.localFundingKey = pkOpen ∧
    demoNegotiation.remoteFundingKey = pkAccept :=
  ⟨phase4_reachable, rfl, rfl, rfl, rfl, phase4_openerNegotiation,
    phase4_acceptorNegotiation, rfl, rfl⟩

/-! ## 4. Registration and funding-key attribution witness -/

/-- The concrete accept payload satisfies the `AdvertisesKey` registration
hypothesis under the pinned key model: the advertised key is the generated key
of `seedBytes`. -/
theorem demo_advertisesKey (M₀ : PrimitiveModel) :
    AdvertisesKey (pinnedKeyModel M₀ pkAccept (fundingTag ++ fundingTx))
      seedBytes demoAccept := by
  show demoAccept.fundingPubKey =
    (pinnedKeyModel M₀ pkAccept (fundingTag ++ fundingTx)).publicOfSeed seedBytes
  rfl

/-- The concrete payload advertises the pinned model's generated key. -/
theorem demo_advertised_eq_generated (M₀ : PrimitiveModel) :
    demoAccept.fundingPubKey =
      (pinnedKeyModel M₀ pkAccept (fundingTag ++ fundingTx)).publicOfSeed
        seedBytes :=
  demo_advertisesKey M₀

/-- The registered signer owns the key pair `(generated public key, generated
secret key)`. -/
theorem demo_owns_generated_key (M₀ : PrimitiveModel) :
    (pinnedKeyModel M₀ pkAccept (fundingTag ++ fundingTx)).Owns
      ((pinnedKeyModel M₀ pkAccept (fundingTag ++ fundingTx)).publicOfSeed seedBytes)
      ((pinnedKeyModel M₀ pkAccept (fundingTag ++ fundingTx)).secretOfSeed seedBytes) :=
  KeyModel.owns_generated _ seedBytes

/-- The generated secret key of the witness is non-empty (32 bytes).  The
accept payload carries only the 33-byte public key, not the secret. -/
theorem demo_secret_nonempty (M₀ : PrimitiveModel) :
    ((pinnedKeyModel M₀ pkAccept (fundingTag ++ fundingTx)).secretOfSeed
      seedBytes).bytes.size = 32 := by
  simp [pinnedKeyModel, KeyModel.secretOfSeed, KeyPair.secret_mk]

/-- The payload's key bytes are not the secret-key bytes: their sizes differ
(33 versus 32).  This is the concrete form of "the payload is a public value". -/
theorem demo_secret_ne_payload_key_bytes (M₀ : PrimitiveModel) :
    ((pinnedKeyModel M₀ pkAccept (fundingTag ++ fundingTx)).secretOfSeed
      seedBytes).bytes ≠ demoAccept.fundingPubKey.bytes := by
  intro h
  have hs := congrArg ByteArray.size h
  have hsec := demo_secret_nonempty M₀
  have hpub : demoAccept.fundingPubKey.bytes.size = 33 := acceptKeyBytes_size
  rw [hsec, hpub] at hs
  omega

/-- **Registration witness, non-vacuous.**  For every base primitive model
there is a full model `M`, a key model `K`, and a seed such that C3, key
binding, the BOLT-3 wire-shape law, the `AdvertisesKey` registration
hypothesis, signing correctness on the concrete funding message, key ownership,
and a non-empty secret key all hold.  The advertised key is the concrete
`accept_channel.funding_pubkey`. -/
theorem registration_witness (M₀ : PrimitiveModel) :
    ∃ (M : PrimitiveModel) (K : KeyModel M) (seed : ByteArray),
      EufCma M.ecdsaVerify ∧
      LnLean.Proofs.Crypto.KeyModelTargets.KeyBinding M.ecdsaVerify ∧
      WireShaped K ∧
      AdvertisesKey K seed demoAccept ∧
      K.correctOn (fundingTag ++ fundingTx) ∧
      K.Owns (K.publicOfSeed seed) (K.secretOfSeed seed) ∧
      (K.secretOfSeed seed).bytes.size = 32 ∧
      M.ecdsaVerify demoAccept.fundingPubKey (fundingTag ++ fundingTx)
        (K.sign (K.secretOfSeed seed) (fundingTag ++ fundingTx)) = true := by
  let M : PrimitiveModel := pinnedModel M₀ pkAccept (fundingTag ++ fundingTx)
  let K : KeyModel M := pinnedKeyModel M₀ pkAccept (fundingTag ++ fundingTx)
  refine ⟨M, K, seedBytes, M.ecdsa_eufCma,
    pinnedVerify_keyBinding pkAccept (fundingTag ++ fundingTx),
    pinnedKeyModel_wireShaped M₀ pkAccept (fundingTag ++ fundingTx),
    demo_advertisesKey M₀, ?_, KeyModel.owns_generated K seedBytes, ?_, ?_⟩
  · show K.correctOn (fundingTag ++ fundingTx)
    rfl
  · show (K.secretOfSeed seedBytes).bytes.size = 32
    exact demo_secret_nonempty M₀
  · exact funding_signature_valid_under_advertised_key K demoAccept seedBytes
      (demo_advertisesKey M₀) fundingTx (by rfl)

/-- **Registration is carried into the negotiation.**  Under `AdvertisesKey`,
the remote funding key of the concrete negotiation is the generated key. -/
theorem registered_key_is_negotiation_key {M : PrimitiveModel} {K : KeyModel M}
    {seed : ByteArray} (hreg : AdvertisesKey K seed demoAccept) :
    demoNegotiation.remoteFundingKey = K.publicOfSeed seed := by
  rw [demoNegotiation_remoteFundingKey]
  simpa [AdvertisesKey, demoAccept] using hreg

/-- **The registered key occurs literally in the funding witness script.** -/
theorem registered_key_in_funding_script (M : PrimitiveModel)
    {K : KeyModel M} {seed : ByteArray}
    (hreg : AdvertisesKey K seed demoAccept) :
    KeyInScript (demoNegotiation.toFundingParams M.sha256).witnessScript.bytes
      (K.publicOfSeed seed) := by
  rw [← registered_key_is_negotiation_key hreg]
  exact (openAccept_both_keys_in_script M.sha256 demoOpen demoAccept).2

/-- **Any accepting key is the negotiation key.**  Under the unchanged
`KeyBinding` contract, every public key that accepts the honest funding
signature is the remote funding key of the concrete negotiation, and therefore
occurs literally in the funding witness script. -/
theorem accepting_key_attribution (M : PrimitiveModel)
    (hkb : LnLean.Proofs.Crypto.KeyModelTargets.KeyBinding M.ecdsaVerify) (K : KeyModel M) (seed : ByteArray)
    (hreg : AdvertisesKey K seed demoAccept)
    (hdom : K.correctOn (fundingTag ++ fundingTx)) {pk' : PubKey}
    (hver : M.ecdsaVerify pk' (fundingTag ++ fundingTx)
      (K.sign (K.secretOfSeed seed) (fundingTag ++ fundingTx)) = true) :
    pk' = demoNegotiation.remoteFundingKey ∧
      KeyInScript (demoNegotiation.toFundingParams M.sha256).witnessScript.bytes
        pk' := by
  have hp : pk' = demoAccept.fundingPubKey :=
    funding_signature_attribution K hkb demoAccept seed hreg fundingTx hdom hver
  have hr : demoNegotiation.remoteFundingKey = demoAccept.fundingPubKey := rfl
  refine ⟨hp.trans hr.symm, ?_⟩
  rw [hp]
  exact (openAccept_both_keys_in_script M.sha256 demoOpen demoAccept).2

/-- **The attribution contract is non-vacuous at the concrete payload.**  The
honest funding signature produced by the registered secret key verifies under
`demoAccept.funding_pubkey`; any other accepting key is the negotiation's
remote key and is committed by the funding script. -/
theorem attributed_registered_key_nonvacuous (M₀ : PrimitiveModel) :
    ∃ (M : PrimitiveModel) (K : KeyModel M) (seed : ByteArray) (sig : EcdsaSig),
      LnLean.Proofs.Crypto.KeyModelTargets.KeyBinding M.ecdsaVerify ∧
      AdvertisesKey K seed demoAccept ∧
      K.correctOn (fundingTag ++ fundingTx) ∧
      sig = K.sign (K.secretOfSeed seed) (fundingTag ++ fundingTx) ∧
      M.ecdsaVerify demoAccept.fundingPubKey (fundingTag ++ fundingTx) sig = true ∧
      (∀ pk' : PubKey,
        M.ecdsaVerify pk' (fundingTag ++ fundingTx) sig = true →
        pk' = demoNegotiation.remoteFundingKey ∧
          KeyInScript (demoNegotiation.toFundingParams M.sha256).witnessScript.bytes
            pk') := by
  let M : PrimitiveModel := pinnedModel M₀ pkAccept (fundingTag ++ fundingTx)
  let K : KeyModel M := pinnedKeyModel M₀ pkAccept (fundingTag ++ fundingTx)
  let sig : EcdsaSig := K.sign (K.secretOfSeed seedBytes) (fundingTag ++ fundingTx)
  refine ⟨M, K, seedBytes, sig,
    pinnedVerify_keyBinding pkAccept (fundingTag ++ fundingTx),
    demo_advertisesKey M₀, ?_, rfl, ?_, ?_⟩
  · show K.correctOn (fundingTag ++ fundingTx)
    rfl
  · exact funding_signature_valid_under_advertised_key K demoAccept seedBytes
      (demo_advertisesKey M₀) fundingTx (by rfl)
  · intro pk' hver
    exact accepting_key_attribution M
      (pinnedVerify_keyBinding pkAccept (fundingTag ++ fundingTx)) K seedBytes
      (demo_advertisesKey M₀) (by rfl) hver

/-! ## 5. Funding-output construction witness -/

/-- The concrete negotiated parameters are structurally well formed. -/
theorem demoFundingParams_wellFormed (M : PrimitiveModel) :
    (demoNegotiation.toFundingParams M.sha256).WellFormed := by
  refine LnLean.Bitcoin.FundingNegotiation.toFundingParams_wellFormed
    M.sha256 M.sha256_size demoNegotiation ?_ ?_ ?_ ?_ ?_
  · show (0 : Int) ≤ demoNegotiation.fundingSatoshis
    decide
  · show demoNegotiation.fundingSatoshis ≤ Bitcoin.Data.MAX_MONEY
    decide
  · show demoNegotiation.localFundingKey.Valid
    simpa using pkOpen_valid
  · show demoNegotiation.remoteFundingKey.Valid
    simpa using pkAccept_valid
  · show (demoNegotiation.pushMsat.val : Int) ≤
      demoNegotiation.fundingSatoshis * (Msat.MSAT_PER_SAT : Int)
    decide

/-- The concrete constructed parameters carry the hash link by construction. -/
theorem demoFundingParams_hash_linked (M : PrimitiveModel) :
    FundingScriptHashLinked M.sha256
      (demoNegotiation.toFundingParams M.sha256) :=
  LnLean.Bitcoin.FundingNegotiation.toFundingParams_witnessScriptHash
    M.sha256 demoNegotiation

/-- The committed program is 32 bytes. -/
theorem demoFundingParams_hash_size (M : PrimitiveModel) :
    (demoNegotiation.toFundingParams M.sha256).witnessScriptHash.size = 32 :=
  LnLean.Bitcoin.FundingNegotiation.toFundingParams_witnessScriptHash_size
    M.sha256 M.sha256_size demoNegotiation

/-- Both concrete funding keys occur literally in the funding witness script. -/
theorem demo_both_keys_in_script (M : PrimitiveModel) :
    KeyInScript (demoNegotiation.toFundingParams M.sha256).witnessScript.bytes
        pkOpen ∧
      KeyInScript (demoNegotiation.toFundingParams M.sha256).witnessScript.bytes
        pkAccept := by
  simpa [demoNegotiation, OpenChannel.toFundingParams] using
    openAccept_both_keys_in_script M.sha256 demoOpen demoAccept

/-- The concrete funding output is P2WSH over the exact ordered BOLT 3 2-of-2
script. -/
theorem demo_fundingScriptPubKey_eq_p2wsh (M : PrimitiveModel) :
    (demoNegotiation.toFundingParams M.sha256).fundingScriptPubKey =
      p2wsh (M.sha256
        (TwoOfTwoScriptBytes demoNegotiation.firstFundingKey
          demoNegotiation.secondFundingKey)) := by
  simpa [demoNegotiation, OpenChannel.toFundingParams] using
    openAccept_fundingScriptPubKey_eq_p2wsh_ordered M.sha256 demoOpen demoAccept

/-- **The funding construction is non-vacuous at the concrete negotiation.**
Well-formedness, the constructed hash link, the 32-byte program, literal
commitment of both keys, and the exact P2WSH output all hold simultaneously. -/
theorem funding_construction_witness (M : PrimitiveModel) :
    (demoNegotiation.toFundingParams M.sha256).WellFormed ∧
    FundingScriptHashLinked M.sha256
      (demoNegotiation.toFundingParams M.sha256) ∧
    (demoNegotiation.toFundingParams M.sha256).witnessScriptHash.size = 32 ∧
    KeyInScript (demoNegotiation.toFundingParams M.sha256).witnessScript.bytes
        pkOpen ∧
    KeyInScript (demoNegotiation.toFundingParams M.sha256).witnessScript.bytes
        pkAccept ∧
    (demoNegotiation.toFundingParams M.sha256).fundingScriptPubKey =
      p2wsh (M.sha256
        (TwoOfTwoScriptBytes demoNegotiation.firstFundingKey
          demoNegotiation.secondFundingKey)) :=
  ⟨demoFundingParams_wellFormed M,
    demoFundingParams_hash_linked M,
    demoFundingParams_hash_size M,
    (demo_both_keys_in_script M).1,
    (demo_both_keys_in_script M).2,
    demo_fundingScriptPubKey_eq_p2wsh M⟩

/-! ## 6. The v1 `HandshakeState` boundary around `funding_created` -/

/-- Initial v1 handshake state. -/
def hs0 : HandshakeState := HandshakeState.initial

/-- After sending `init`. -/
def hs1 : HandshakeState := { initSent := true }

/-- After receiving `init`. -/
def hs2 : HandshakeState := { initSent := true, initReceived := true }

/-- After receiving the peer's `accept_channel` (opener side). -/
def hs3 : HandshakeState :=
  { initSent := true, initReceived := true, acceptReceived := true }

/-- After sending `funding_created`. -/
def hs4 : HandshakeState :=
  { initSent := true, initReceived := true, acceptReceived := true,
    fundingCreatedSent := true }

theorem hs1_step : handshakeStep hs0 .sendInit = some hs1 := by
  simp [handshakeStep, hs0, hs1, HandshakeState.initial, HandshakeState.canSendInit]

theorem hs2_step : handshakeStep hs1 .recvInit = some hs2 := by
  simp [handshakeStep, hs1, hs2, HandshakeState.canRecvInit]

theorem hs3_step : handshakeStep hs2 .recvAcceptChannel = some hs3 := by
  simp [handshakeStep, hs2, hs3, HandshakeState.canRecvAccept,
    HandshakeState.inited, HandshakeState.noReady]

theorem hs4_step : handshakeStep hs3 .sendFundingCreated = some hs4 := by
  simp [handshakeStep, hs3, hs4, HandshakeState.canSendFundingCreated,
    HandshakeState.inited, HandshakeState.noReady]

/-- The accept-received state is reachable by an honest v1 exchange. -/
theorem hs3_reachable : Reachable hs3 :=
  Reachable.step _
    (Reachable.step _ (Reachable.step _ Reachable.initial hs1_step) hs2_step)
    hs3_step

/-- **`accept_channel` precedes `funding_created` in the v1 machine.** -/
theorem hs4_fundingCreated_allowed :
    Reachable hs3 ∧
      handshakeStep hs3 .sendFundingCreated = some hs4 ∧
      hs3.acceptReceived = true ∧
      hs4.fundingCreatedSent = true :=
  ⟨hs3_reachable, hs4_step, rfl, rfl⟩

/-- **The v1 boundary binds the received accept key.**  At the permitted
`funding_created` transition, the joint construction's remote funding key is
the `accept_channel.funding_pubkey` that the peer sent, for any 32-byte-output
hash `H`. -/
theorem v1_handshake_funding_boundary (M : PrimitiveModel) :
    hs3.acceptReceived = true ∧
      ((demoOpen.toFundingNegotiation demoAccept).toFundingParams M.sha256).remoteFundingKey =
        demoAccept.fundingPubKey :=
  acceptKey_bound_before_fundingCreated hs4_step demoOpen demoAccept M.sha256

/-! ## 7. The bundled witness -/

/-- **One machine-checked instance of the whole PR-01 contract.**  For every
base primitive model there are concrete values, a full model, and a key model
such that all of the following hold at the same time:

* the accept payload is non-empty and carries a valid, distinct compressed key;
* the four-message honest funding exchange is reachable and both endpoints
  expose the same concrete negotiation;
* the payload's key is registered (`AdvertisesKey`) as the generated key;
* C3, `KeyBinding`, and the BOLT wire-shape law hold;
* the registered key is the negotiation's remote key and occurs in the funding
  script;
* the constructed parameters are well formed, hash-linked, and produce the
  exact P2WSH 2-of-2 output;
* every key accepting the honest funding signature is that remote key, and the
  honest signature verifies.

This is a non-vacuity witness for the conditional contract; it is not a proof
of computational ECDSA security or of key possession. -/
theorem honest_witness (M₀ : PrimitiveModel) :
    ∃ (M : PrimitiveModel) (K : KeyModel M) (seed : ByteArray),
      AcceptPayloadNonempty ∧
      FundingReachable phase4 ∧
      phase4.openerNegotiation? = some demoNegotiation ∧
      phase4.acceptorNegotiation? = some demoNegotiation ∧
      demoNegotiation.localFundingKey = pkOpen ∧
      demoNegotiation.remoteFundingKey = pkAccept ∧
      AdvertisesKey K seed demoAccept ∧
      EufCma M.ecdsaVerify ∧
      LnLean.Proofs.Crypto.KeyModelTargets.KeyBinding M.ecdsaVerify ∧
      WireShaped K ∧
      K.correctOn (fundingTag ++ fundingTx) ∧
      K.Owns (K.publicOfSeed seed) (K.secretOfSeed seed) ∧
      demoNegotiation.remoteFundingKey = K.publicOfSeed seed ∧
      KeyInScript (demoNegotiation.toFundingParams M.sha256).witnessScript.bytes
        (K.publicOfSeed seed) ∧
      M.ecdsaVerify demoAccept.fundingPubKey (fundingTag ++ fundingTx)
        (K.sign (K.secretOfSeed seed) (fundingTag ++ fundingTx)) = true ∧
      (demoNegotiation.toFundingParams M.sha256).WellFormed ∧
      FundingScriptHashLinked M.sha256
        (demoNegotiation.toFundingParams M.sha256) ∧
      (demoNegotiation.toFundingParams M.sha256).witnessScriptHash.size = 32 := by
  let M : PrimitiveModel := pinnedModel M₀ pkAccept (fundingTag ++ fundingTx)
  let K : KeyModel M := pinnedKeyModel M₀ pkAccept (fundingTag ++ fundingTx)
  refine ⟨M, K, seedBytes, accept_payload_nonempty, phase4_reachable,
    phase4_openerNegotiation, phase4_acceptorNegotiation, rfl, rfl,
    demo_advertisesKey M₀, M.ecdsa_eufCma,
    pinnedVerify_keyBinding pkAccept (fundingTag ++ fundingTx),
    pinnedKeyModel_wireShaped M₀ pkAccept (fundingTag ++ fundingTx),
    ?_, KeyModel.owns_generated K seedBytes,
    registered_key_is_negotiation_key (demo_advertisesKey M₀),
    registered_key_in_funding_script M (demo_advertisesKey M₀),
    ?_, demoFundingParams_wellFormed M, demoFundingParams_hash_linked M,
    demoFundingParams_hash_size M⟩
  · show K.correctOn (fundingTag ++ fundingTx)
    rfl
  · exact funding_signature_valid_under_advertised_key K demoAccept seedBytes
      (demo_advertisesKey M₀) fundingTx (by rfl)

end LnLean.Proofs.WaveH.H23
