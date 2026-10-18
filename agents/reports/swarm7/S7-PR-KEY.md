# S7-PR-KEY — secret-key/key-generation model and `accept_channel.funding_pubkey`

**Lane:** `S7-PR-KEY`
**Issue:** `PR-01` (P1, open/partially mitigated)
**Worktree:** `/home/ubuntu/ln-lean-repair`
**Branch / base:** `repair/integrated` @ `3180581` (wave-7 launch; the roadmap
text points at `83d90b7` as the wave-6 gate)
**Toolchain:** `leanprover/lean4:v4.35.0`
**Owned files:** both new; no existing file edited

| File | Change |
|---|---|
| `LnLean/Crypto/KeyModel.lean` | **New** (209 lines): `SecretKey`, `KeyPair`, `KeyModel`, `Owns`, `Signer`. |
| `LnLean/Proofs/Crypto/KeyModelTargets.lean` | **New** (519 lines): `accept_channel` link, attribution contract, `FundingSigningLaw` compatibility bridge, counterexample, non-vacuity witness, summary bundle. |
| `agents/reports/swarm7/S7-PR-KEY.md` | This report. |

**Verdict.** PR-01 is narrowed from "`FundingSigningLaw`/`KeyBinding` are
hypotheses with no key model" to the following faithful contract:

1. a deterministic secret-key/key-generation model exists, with secret-key
   signing and domain-scoped correctness (`KeyModel`);
2. the BOLT 2 `accept_channel.funding_pubkey` field can be explicitly linked to
   the generated signer key (`AdvertisesKey K seed m`), and under that link the
   handshake negotiation's `remoteFundingKey` is the signer's key and the
   funding-domain signature verifies under `m.fundingPubKey`;
3. **key attribution is still conditional on the existing, unchanged
   `LnLean.Proofs.WaveE.E06.KeyBinding` hypothesis**;
4. a mechanized counterexample shows that key generation + secret-key signing +
   C3 (`EufCma`) do **not** imply attribution: one signature validates under two
   distinct `accept_channel` funding keys, and the model fails `KeyBinding`;
5. a concrete pinned-key witness shows the positive contract is non-vacuous.

C3 alone is *not* used as a key-attribution assumption anywhere in this lane.
The existing `FundingSigningLaw` and `KeyBinding` declarations are imported
unchanged; `KeyBinding` is re-exported under a local abbreviation only.

---

## 1. Model additions (`LnLean/Crypto/KeyModel.lean`)

Namespace `LnLean.Crypto`.  Imports only `LnLean.Crypto.Model`, so the model
module stays independent of the proof-layer wire parsers.

```lean
structure SecretKey where
  bytes : ByteArray
deriving Repr, BEq

structure KeyPair where
  secret : SecretKey
  pubkey : PubKey
deriving Repr, BEq

structure KeyModel (M : PrimitiveModel) where
  generate : ByteArray → KeyPair
  sign : SecretKey → ByteArray → EcdsaSig
  correctOn : ByteArray → Prop
  verifies : ∀ (seed : ByteArray) (msg : ByteArray), correctOn msg →
    M.ecdsaVerify (generate seed).pubkey msg (sign (generate seed).secret msg) =
      true

def KeyModel.publicOfSeed (K : KeyModel M) (seed : ByteArray) : PubKey
def KeyModel.secretOfSeed (K : KeyModel M) (seed : ByteArray) : SecretKey
theorem KeyModel.verifies_seed ...
def KeyModel.Total (K : KeyModel M) : Prop := ∀ msg, K.correctOn msg
theorem KeyModel.verifies_of_total ...
def KeyModel.Owns (K : KeyModel M) (pk : PubKey) (sk : SecretKey) : Prop :=
  ∃ seed, K.publicOfSeed seed = pk ∧ K.secretOfSeed seed = sk
theorem KeyModel.owns_generated ...
theorem KeyModel.owns_verifies ...

structure Signer (M : PrimitiveModel) where
  model : KeyModel M
  seed : ByteArray
def Signer.publicKey / Signer.secret / Signer.sign
theorem Signer.verifies / Signer.owns
```

**Why `correctOn` is a field.**  A *total* correctness law on all `ByteArray`
messages, together with `EufCma` and the BOLT wire shape, forces an injective
map from the countably infinite message space into the finite set of 64/71--73
byte strings.  `correctOn` is the honest model of a signer that is complete on
the protocol messages it is specified to sign.  This tension is mechanized in
§4 (`fundingSigningLaw_sign_injective`, `fundingSigningLaw_wire_bound`) and
discussed in §7.

**Not modelled.**  secp256k1 arithmetic, RFC 6979 nonce derivation, seed
entropy, key storage, proof of possession, and a registration/ownership game.
`generate` is a total function of a byte-string seed, not a randomised key
generation algorithm.

---

## 2. Exact signatures (`LnLean/Proofs/Crypto/KeyModelTargets.lean`)

Namespace `LnLean.Proofs.Crypto.KeyModelTargets`.  `open LnLean.Crypto.KeyModel`.

```lean
abbrev KeyBinding (verify : PubKey → ByteArray → EcdsaSig → Bool) : Prop :=
  LnLean.Proofs.WaveE.E06.KeyBinding verify

def WireShaped {M : PrimitiveModel} (K : KeyModel M) : Prop :=
  ∀ (sk : SecretKey) (msg : ByteArray), wireSigOK (K.sign sk msg).bytes = true

def acceptChannelWithFundingKey (pk : PubKey) : AcceptChannel
@[simp] theorem acceptChannelWithFundingKey_fundingPubKey (pk) :
    (acceptChannelWithFundingKey pk).fundingPubKey = pk

def AdvertisesKey {M : PrimitiveModel} (K : KeyModel M) (seed : ByteArray)
    (m : AcceptChannel) : Prop :=
  m.fundingPubKey = K.publicOfSeed seed

theorem advertisedKey_eq_generated (h : AdvertisesKey K seed m) :
    m.fundingPubKey = K.publicOfSeed seed

theorem advertised_key_is_negotiation_key
    (K : KeyModel M) (seed : ByteArray) (m : AcceptChannel)
    (h : AdvertisesKey K seed m) (localFundingKey : PubKey)
    (fundingSatoshis : BtcAmount) (pushMsat : Msat)
    (temporaryChannelId : TemporaryChannelId) :
    (m.toFundingNegotiation localFundingKey fundingSatoshis pushMsat
      temporaryChannelId).remoteFundingKey = K.publicOfSeed seed

theorem funding_signature_valid_under_advertised_key
    (K : KeyModel M) (m : AcceptChannel) (seed : ByteArray)
    (h : AdvertisesKey K seed m) (fundingTx : ByteArray)
    (hdom : K.correctOn (fundingTag ++ fundingTx)) :
    M.ecdsaVerify m.fundingPubKey (fundingTag ++ fundingTx)
      (K.sign (K.secretOfSeed seed) (fundingTag ++ fundingTx)) = true

theorem funding_signature_attribution
    (K : KeyModel M) (hkb : KeyBinding M.ecdsaVerify) (m : AcceptChannel)
    (seed : ByteArray) (h : AdvertisesKey K seed m) (fundingTx : ByteArray)
    (hdom : K.correctOn (fundingTag ++ fundingTx)) {pk' : PubKey}
    (hver : M.ecdsaVerify pk' (fundingTag ++ fundingTx)
      (K.sign (K.secretOfSeed seed) (fundingTag ++ fundingTx)) = true) :
    pk' = m.fundingPubKey

theorem funding_signature_wire_shape
    (K : KeyModel M) (hwire : WireShaped K) (seed fundingTx : ByteArray) :
    wireSigOK (K.sign (K.secretOfSeed seed)
      (fundingTag ++ fundingTx)).bytes = true

structure RealisesFundingLaw {M : PrimitiveModel} (K : KeyModel M)
    (law : FundingSigningLaw M) (seed : ByteArray) : Prop where
  agrees : ∀ msg, law.sign (K.publicOfSeed seed) msg =
    K.sign (K.secretOfSeed seed) msg

theorem funding_signed_contract_of_keyModel
    (K : KeyModel M) (law : FundingSigningLaw M) (seed : ByteArray)
    (hreal : RealisesFundingLaw K law seed)
    (hkb : KeyBinding M.ecdsaVerify) (channelId : ChannelId)
    (m : AcceptChannel) (h : AdvertisesKey K seed m) (fundingTx : ByteArray) :
    let s := honestFundingSigned law channelId m.fundingPubKey fundingTx
    s.signature = K.sign (K.secretOfSeed seed) (fundingTag ++ fundingTx) ∧
      fundingSignedValid M m.fundingPubKey fundingTx s ∧
      (∀ pk', fundingSignedValid M pk' fundingTx s → pk' = m.fundingPubKey) ∧
      (∀ tx', fundingSignedValid M m.fundingPubKey tx' s → tx' = fundingTx)

theorem fundingSigningLaw_sign_injective (law : FundingSigningLaw M)
    (pk : PubKey) : Function.Injective (law.sign pk)

theorem fundingSigningLaw_wire_bound (law : FundingSigningLaw M)
    (pk : PubKey) (msg : ByteArray) :
    (law.sign pk msg).bytes.size = 64 ∨
      (71 ≤ (law.sign pk msg).bytes.size ∧
        (law.sign pk msg).bytes.size ≤ 73)

theorem singleMessageVerify_not_keyBinding (d₀ : ByteArray) :
    ¬ KeyBinding (singleMessageVerify d₀)

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
        ¬ KeyBinding M.ecdsaVerify

theorem pinnedVerify_eufCma (k₀ d₀) : EufCma (pinnedVerify k₀ d₀)
theorem pinnedVerify_keyBinding (k₀ d₀) : KeyBinding (pinnedVerify k₀ d₀)

theorem attribution_contract_nonvacuous (M₀ : PrimitiveModel) (k₀ : PubKey) :
    ∃ (M : PrimitiveModel) (K : KeyModel M) (m : AcceptChannel)
      (seed : ByteArray) (fundingTx : ByteArray),
      EufCma M.ecdsaVerify ∧ KeyBinding M.ecdsaVerify ∧ WireShaped K ∧
        AdvertisesKey K seed m ∧ K.correctOn (fundingTag ++ fundingTx) ∧
        (∀ pk', M.ecdsaVerify pk' (fundingTag ++ fundingTx)
          (K.sign (K.secretOfSeed seed) (fundingTag ++ fundingTx)) = true →
          pk' = m.fundingPubKey)

theorem key_model_summary :
    (positive validity under `AdvertisesKey`) ∧
    (attribution under `KeyBinding`) ∧
    (counterexample for every base model) ∧
    (non-vacuous pinned instance for every base model and key)
```

The full `#check` output is the source of these signatures; the exact binder
order is preserved above.

---

## 3. Proof strategy

1. **No public-key-keyed signer.**  `KeyModel.sign` takes a `SecretKey`, and
   correctness is stated against `(generate seed).pubkey`, so the honest signer
   is a generated key pair instead of an opaque function of `PubKey`.
2. **Wire field kept out of the model.**  `WireShaped` is a proof-layer
   predicate over `wireSigOK`; `KeyModel` does not depend on the signature
   parser.  The positive contract takes `WireShaped` only when it needs the
   BOLT wire conclusion.
3. **Registration is explicit.**  `AdvertisesKey K seed m` is exactly
   `m.fundingPubKey = K.publicOfSeed seed`.  It is *not* derived from the
   handshake state: `HandshakeState` stores boolean milestones, not the
   `AcceptChannel` payload.  The positive theorems prove what follows from the
   link; §4 proves the link is not free.
4. **Attribution reuses `KeyBinding` unchanged.**  `funding_signature_attribution`
   applies `LnLean.Proofs.WaveE.E06.KeyBinding` to the honest signature and the
   accepting key, then rewrites through `AdvertisesKey`.  No new key-binding
   axiom or instance is introduced.
5. **The existing funding contract is not replaced.**  `funding_signed_contract_of_keyModel`
   invokes `funding_signed_signing_contract` unchanged and adds the equation
   `s.signature = K.sign sk (fundingTag ++ tx)`.  `RealisesFundingLaw` is the
   explicit link `law.sign (K.publicOfSeed seed) = K.sign (K.secretOfSeed seed)`.
6. **Counterexample construction.**  `cheatKeyModel` uses the single-message
   verifier from `LnLean.Proofs.Crypto.EcdsaProps` (which is `EufCma`), two
   seeds that generate two distinct key pairs, `sign _ _ := ⟨zeros 64⟩`
   (wire-shaped), and `correctOn msg := msg = d₀`.  The signature produced from
   seed₂ is the same 64-byte value as the one from seed₁ and validates under
   both public keys; the verifier ignores keys, so `KeyBinding` fails.
7. **Non-vacuity.**  `pinnedVerify k₀ d₀` accepts exactly `pk.bytes = k₀.bytes`
   and `msg = d₀`; it is `EufCma` and `KeyBinding`.  `pinnedKeyModel` generates
   every seed with public key `k₀`, signs with `zeros 64`, and is complete on
   `d₀`.  The attribution conclusion holds, so the conditional contract has a
   model.

---

## 4. Build and axiom results

Commands, under the shared lock, single Lean thread:

```sh
export PATH=/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
cd /home/ubuntu/ln-lean-repair

LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Crypto.KeyModel LnLean.Proofs.Crypto.KeyModelTargets
# ✔ [27/27] Built LnLean.Proofs.Crypto.KeyModelTargets (823ms)
# Build completed successfully (27 jobs).
# RC 0, 0 warnings.
```

A second build after `touch` reports no warnings (the earlier `if_neg`
deprecation was replaced with `ite_eq_right`; unused simp/variable warnings were
removed).  No full `lake build`, `collect-obligations.py`, `collect-anchors.py`,
or Git write was run.

`#print axioms` (scratch file `/tmp/opencode/s7_key_audit.lean`, run with
`lake env lean`):

| Declaration | Axioms |
|---|---|
| `KeyModel.verifies_seed` | none |
| `KeyModel.owns_verifies` | none |
| `Signer.verifies` | none |
| `Signer.owns` | none |
| `advertised_key_is_negotiation_key` | none |
| `funding_signature_valid_under_advertised_key` | none |
| `funding_signature_attribution` | none |
| `funding_signature_wire_shape` | `propext`, `Classical.choice`, `Quot.sound` |
| `funding_signed_contract_of_keyModel` | `propext`, `Classical.choice`, `Quot.sound` |
| `fundingSigningLaw_sign_injective` | `propext`, `Classical.choice`, `Quot.sound` |
| `fundingSigningLaw_wire_bound` | `propext`, `Classical.choice`, `Quot.sound` |
| `singleMessageVerify_not_keyBinding` | `propext`, `Quot.sound` |
| `key_generation_not_key_attribution` | `propext`, `Quot.sound` |
| `pinnedVerify_eufCma` | `propext`, `Quot.sound` |
| `pinnedVerify_keyBinding` | `propext`, `Quot.sound` |
| `attribution_contract_nonvacuous` | `propext`, `Classical.choice`, `Quot.sound` |
| `key_model_summary` | `propext`, `Classical.choice`, `Quot.sound` |

Only the three permitted axioms appear.  Seven audited declarations depend on
no axioms at all.

Forbidden-construct scan:

```sh
grep -nE '\b(sorry|axiom|admit|native_decide|unsafe)\b|implemented_by' \
  LnLean/Crypto/KeyModel.lean LnLean/Proofs/Crypto/KeyModelTargets.lean
# no matches
```

---

## 5. What is proved and what is not

### Proved (conditional on the named hypotheses)

* The advertised `accept_channel.funding_pubkey` is the signer's generated
  public key and the handshake negotiation's `remoteFundingKey`, under
  `AdvertisesKey`.
* The secret key's funding-domain signature validates under
  `m.fundingPubKey`, given correctness on the funding message.
* Under the unchanged `KeyBinding`, any key that accepts that signature is
  `m.fundingPubKey`.
* A wire-shaped key model yields a BOLT-accepted signature.
* The existing `FundingSigningLaw` contract is preserved, with the extra
  equation that its signature is the secret-key signature, under
  `RealisesFundingLaw`.
* Key generation + secret-key signing + C3 do **not** attribute a signature to
  the expected key pair (`key_generation_not_key_attribution`).
* The positive contract is non-vacuous (`attribution_contract_nonvacuous`).

### Not proved / not assumed

* `accept_channel.funding_pubkey` alone is not a proof of possession.  The
  negative result exhibits a model where the field is `pk₁`, but the signature
  that validates under it was produced by `sk₂` with `pk₂ ≠ pk₁`, and the
  signature is identical to the one `sk₁` produces.
* `HandshakeState` does not carry the received `AcceptChannel`, so
  `AdvertisesKey` cannot be derived from protocol state today; it is an
  external registration hypothesis.
* `KeyBinding` is not implied by `EufCma`; this is the same separation proved
  in `LnLean.Proofs.WaveE.E06` and `LnLean.Proofs.ProtocolSigningTargets`,
  retained here in key-model form.
* No computational key-generation/ownership game, no proof of possession, no
  secp256k1, no nonce model, no seed entropy.  `CR-01`/`SEC-01` remain
  unaffected.
* No `open_channel` model: the repo's `Handshake.lean` still represents the
  opener's fields as local values and reads the acceptor's key from
  `accept_channel` only.  This lane does not edit that file.

**Important scope caveat: the `FundingSigningLaw` bridge is compatibility, not
existence.**  A total `FundingSigningLaw` has an injective honest signature map
at each key (`fundingSigningLaw_sign_injective`) and every honest signature is
64 or 71--73 bytes (`fundingSigningLaw_wire_bound`).  An injection from the
infinite `ByteArray` message space into that finite wire set is impossible, so
the total-correctness + wire fields of `FundingSigningLaw` are in tension with
`EufCma`.  This lane does not edit or weaken the existing contract; it reports
the tension so that the parent does not read `funding_signed_contract_of_keyModel`
as evidence that a total signing law exists.  The non-vacuous PR-01 result is
the `KeyModel` contract and its witness, where correctness is domain-scoped.

---

## 6. Integration steps (parent / catalog owner)

1. **Root import.**  Add to `LnLean.lean`:
   `import LnLean.Crypto.KeyModel` and
   `import LnLean.Proofs.Crypto.KeyModelTargets` (this lane may not edit it).
2. **Axiom audit.**  Add the declarations in §4 to
   `LnLean/Proofs/AxiomAudit.lean`; expected set is the three permitted axioms
   only.
3. **Catalog target for `PR-01`.**  Recommended:
   * primary contract: `LnLean.Proofs.Crypto.KeyModelTargets.funding_signature_attribution`
     or the bundled `key_model_summary`;
   * non-vacuity / connection: `attribution_contract_nonvacuous` and
     `advertised_key_is_negotiation_key`;
   * negative: `key_generation_not_key_attribution`.
   Claim text must keep: "under an explicit key-registration hypothesis linking
   `accept_channel.funding_pubkey` to the generated signer key, and under the
   unchanged `KeyBinding`; C3 alone does not attribute a signature; the
   counterexample is mechanized."
4. **Roadmap.**  Update `PR-01` from "no secret-key model" to "secret-key/key
   generation model and `accept_channel.funding_pubkey` link proved
   conditionally; attribution still requires `KeyBinding` (or a
   registration/proof-of-possession game), and `HandshakeState` does not yet
   carry the `accept_channel` payload."
5. **Optional follow-up (outside this lane).**  Add an
   `acceptChannel? : Option AcceptChannel` (or equivalent payload) field to
   `HandshakeState` and set it in the `recvAcceptChannel` branch of
   `handshakeStep`; then an `AdvertisesKey` instance can be derived from the
   state plus a local key-ownership witness, instead of supplied externally.
   This requires editing `LnLean/Protocol/Handshake.lean`, which this lane does
   not own.
6. Do **not** delete or rewrite `LnLean/Proofs/ProtocolSigningTargets.lean` or
   `LnLean/Proofs/WaveE/E06.lean`; both remain the source of
   `FundingSigningLaw`/`KeyBinding` and are imported unchanged.

---

## 7. Scope caveats and blockers

| Missing item | Consequence | Status here |
|---|---|---|
| `accept_channel` payload in `HandshakeState` | `AdvertisesKey` is external, not derived from protocol state | Documented; §6.5 patch suggestion |
| Proof of possession / key-registration game | `funding_pubkey` can be any key; ownership is not proved | `key_generation_not_key_attribution` mechanizes the failure |
| `KeyBinding` from C3 | Attribution would be automatic | Not assumed; `KeyBinding` remains an explicit hypothesis |
| Total `FundingSigningLaw` consistency | Total correctness + wire shape + `EufCma` is in tension | Mechanized injectivity/bound; bridge marked compatibility-only |
| secp256k1 / RFC 6979 / DER | Signing is a model operation, not a concrete scheme | Outside the model, as in `Crypto/Sig.lean` |
| Computational ownership game | No advantage bound for key substitution | `CR-01`/`SEC-01` remain open |
| `open_channel` model | Opener's key is a local value | Out of scope for this lane (`L1-03`/`S7-L1-FUNDING-AUTH`) |

No blocker prevents the conditional theorems.  The blockers are exactly the
model fields and game interfaces that the faithful claim keeps explicit.

---

## 8. Final summary for the parent

`S7-PR-KEY` adds `LnLean/Crypto/KeyModel.lean` (secret keys, deterministic key
generation, secret-key signing with domain-scoped correctness, ownership, and
`Signer`) and `LnLean/Proofs/Crypto/KeyModelTargets.lean` (accept-channel key
link, attribution under the unchanged `KeyBinding`, `FundingSigningLaw`
compatibility bridge, mechanized attribution counterexample, and a non-vacuous
pinned witness).  Build: 27 jobs, RC 0, no warnings.  Axioms: only `propext`,
`Classical.choice`, `Quot.sound`; seven audited declarations use none.  No
`sorry`/`axiom`/`admit`/`native_decide`/`unsafe`/`implemented_by`.  PR-01 is
narrowed but not closed: key attribution still requires `KeyBinding`, and
`accept_channel.funding_pubkey` is linked to the signer only by the explicit
`AdvertisesKey` registration hypothesis because `HandshakeState` does not carry
the `accept_channel` payload.  The report also records the total
`FundingSigningLaw` consistency tension so the bridge is not over-read.
