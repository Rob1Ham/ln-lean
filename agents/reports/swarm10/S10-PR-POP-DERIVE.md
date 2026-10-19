# S10-PR-POP-DERIVE — a concrete challenge-response proof-of-possession protocol (`PR-01`)

**Lane:** `S10-PR-POP-DERIVE`
**Issue:** `PR-01` (P1: `FundingSigningLaw` and `KeyBinding` are hypotheses; the inherited PoP challenge encoding was non-injective and freshness was informal)
**Recommended catalog row:** `LN-PR-003`
**Branch:** `repair/integrated`
**Launch HEAD:** `7988c93` (base `9158592`; the working tree also contains parent commit `b6a7259` and other lanes' uncommitted files)
**Status:** complete — scoped build green, public-theorem axiom audit clean, forbidden-token scan clean, no shared files edited, no commit/push
**Owned files created:** `LnLean/Proofs/Crypto/PopProtocolTargets.lean` (967 lines), `agents/reports/swarm10/S10-PR-POP-DERIVE.md`
**Files edited outside the owned set:** none. No root import, `Obligations.lean`, `Traceability.lean`, `AxiomAudit.lean`, docs, or other lane edit.

---

## 1. Objective

Wave 9 reduced proof-of-possession to the explicit extraction laws
`PopSound`/`PopProducedBy` over the stored `accept_channel` payload, but it did
not model the challenge-response interaction itself. The inherited H22 signed
message was

```text
popTag ++ temporary_channel_id ++ challenge
```

whose split is not injective for variable-width fields
(`H22.popMessage_split_not_injective`), and freshness was only the informal
`Issued` predicate. This lane had to:

1. give a concrete verifier-issued challenge, session, and responder model over
   the existing `PrimitiveModel`/`KeyModel`/`Signer` vocabulary;
2. prove honest completeness against the advertised
   `accept_channel.funding_pubkey`;
3. derive as much of `PopSound`/`PopProducedBy`/`KeyBinding` as the model
   supports, using the weakest faithful laws;
4. mechanise the replay/forged-challenge negative and identify the exact
   hypothesis that prevents it;
5. exhibit a concrete non-vacuous witness and state the C3/Noise/key-ownership
   boundary.

## 2. Answer in one paragraph

A challenge is `(channelId, nonce)`. The signed message is
`popTag ++ channelId.bytes ++ nonce`; under the fixed-width discipline
`PopChallenge.Valid` (32-byte channel id and 32-byte nonce) the message is
genuinely injective, proved rather than assumed. The verifier's `accepts`
recomputes the message from the **session's** challenge and ignores the
response's claimed `challenge`; the honest signer echoes the challenge and signs
that message. Honest completeness against the advertised funding key follows
from the key model's `correctOn` domain; the session/response pair is an H22
`PopAccepted` transcript and, when the accept payload is stored, a wave-9
`StoredRegistration`. The weakest soundness
law used is `PopKeySoundOn`: an accepted response on an issued challenge yields
a secret key owned for the advertised public key — possession, not signature
provenance. The stronger `PopExtractionOn` additionally pins the signature to
the honest signature and derives H22 `PopSoundOn`/`PopSound` and wave-9
`PopProducedBy`; with the unchanged `KeyBinding` contract this yields funding-key
attribution. The sharp negatives are all mechanised: a verifier that trusts the
response's challenge replays across sessions; omitting the nonce permits replay;
dropping `Valid` makes the encoding collide, so even the session-bound verifier
accepts one response for two challenges; and reusing a challenge in a second
session replays by construction. `EufCma` + `Valid` + injectivity is exactly what
prevents cross-session replay (`no_cross_session_replay`). A concrete
`selfSigModel` witness shows the positive contract is non-vacuous. No real
signature scheme, secp256k1 arithmetic, computational EUF-CMA, or Noise
transport authentication is claimed.

## 3. Artifacts and model

Namespace: `LnLean.Proofs.Crypto.PopProtocolTargets`. Lean 4 core only (no
mathlib), `set_option autoImplicit false`, imports
`AcceptPayloadTargets`, `AttributionGameTargets`, `KeyModelTargets`,
`WaveH.H22`, and `Wire.BigSize`.

### 3.1 Structures and definitions

| Name | Kind | Meaning |
|---|---|---|
| `PopChallenge` | structure | Verifier-issued `channelId : ChannelId` and freshness `nonce : ByteArray`. |
| `PopChallenge.Valid` | def | `channelId.Valid ∧ nonce.size = 32`; the fixed-width discipline making the split recoverable. |
| `FreshOn Used c` | def | `c.Valid ∧ ¬ Used c`; the freshness discipline relative to already issued challenges. |
| `PopSession` | structure | Local `sessionId`, verifier `challenge`, and `expectedKey` to demonstrate. |
| `PopSession.Valid` | def | Validity of the session's challenge. |
| `PopResponse` | structure | Responder-claimed `challenge` (untrusted) and `signature`. |
| `challengeMessage c` | def | `popTag ++ c.channelId.bytes ++ c.nonce`. |
| `sessionOfKey pk c` | def | Session over a key and challenge. |
| `challengeOfAccept m nonce` | def | Challenge bound to `m.temporaryChannelId`. |
| `sessionOfAccept m nonce` | def | Session expecting `m.fundingPubKey` on the accept-bound challenge. |
| `sessionTranscript s r` | def | H22 `PopTranscript` view: `channelId`, `nonce`, signature. |
| `accepts M s r` | def | Session-bound verifier: verifies under `s.expectedKey` on `challengeMessage s.challenge`. |
| `honestResponse K seed c` | def | Echoes `c` and signs `challengeMessage c` with `K.secretOfSeed seed`. |
| `producedBy K sk c r` | def | `r.signature = K.sign sk (challengeMessage c)`. |
| `PopKeySoundOn M K Issued` | def | Accepted issued response ⇒ `∃ sk, K.Owns pk sk` (weakest law used). |
| `PopExtractionOn M K Issued` | def | Accepted issued response ⇒ honest seed/key/signature extraction (stronger). |
| `acceptsClaimed M s r` | def | Deliberately broken verifier that reads `r.challenge` instead of `s.challenge`. |
| `challengeMessageNoNonce c` | def | Deliberately broken message `popTag ++ c.channelId.bytes`. |
| `acceptsNoNonce M s r` | def | Deliberately broken verifier omitting the nonce. |
| `KeyBinding verify` | abbrev | Re-export of the unchanged `WaveE.E06.KeyBinding`. |

The response's `challenge` field is explicitly untrusted by `accepts`; it exists
so the unbound-verifier negative can be stated without changing the response
type.

### 3.2 Composition with wave 9

`sessionTranscript` is definitionally the H22 transcript, and
`popMessage_sessionTranscript` proves
`popMessage (sessionTranscript s r) = challengeMessage s.challenge`. Thus the new
interaction composes with the existing registration game rather than replacing
it. `StoredRegistration` and `PopProducedBy` are imported from
`AttributionGameTargets`; `PopSound`/`PopSoundOn`/`register` from H22. The
module introduces no parallel soundness game.

## 4. Exact claims and theorem names

All names are in `LnLean.Proofs.Crypto.PopProtocolTargets`.

### 4.1 Encoding injectivity and cross-session binding

* **`challengeMessage_injective_of_valid`** — two valid challenges with equal
  signed bytes are equal. Proved from fixed-width prefix cancellation; not a
  hash-collision assumption.
* **`accepts_challenge_bound`** — under `EufCma`, if one response is accepted by
  two sessions with the same expected key and both sessions are valid, the two
  challenges are equal.
* **`no_cross_session_replay`** — the positive counterpart: with valid sessions,
  equal expected keys, and distinct challenges, one response cannot be accepted
  by both.

### 4.2 Honest completeness

* `honestResponse_producedBy` — the honest response is exactly
  `producedBy K (K.secretOfSeed seed) c`.
* `honestResponse_accepts` — on `K.correctOn (challengeMessage c)`, the honest
  response is accepted by the session expecting `K.publicOfSeed seed`.
* **`advertised_honest_completeness`** — `AdvertisesKey K seed m` plus the
  domain condition implies acceptance by `sessionOfAccept m nonce`, i.e. under
  the advertised `funding_pubkey`.
* `advertised_honest_popAccepted` — the same pair is an H22 `PopAccepted`
  transcript under `m.fundingPubKey`.
* `honestResponse_registers` — H22 `register` returns the registered state.
* **`storedAccept_honest_registration`** — a stored accept payload plus an
  honest response on a fresh nonce is a wave-9 `StoredRegistration`.

### 4.3 Soundness: what is derived, from what

* `popKeySoundOn_of_extraction` — `PopExtractionOn` implies `PopKeySoundOn`.
* **`accepted_owns`** — accepted issued response plus `PopKeySoundOn` gives
  `∃ sk, K.Owns s.expectedKey sk`.
* `accepted_provenance` — under `PopExtractionOn`, acceptance identifies the seed
  and the honest signature.
* `popProducedBy_iff_producedBy` — the wave-9 transcript predicate is exactly the
  per-response production predicate.
* `accepted_popProducedBy` — extraction yields ownership plus wave-9
  `PopProducedBy` on the session transcript.
* **`accepted_key_unique`** — unchanged `KeyBinding` makes any key accepting the
  same session message/signature equal to `s.expectedKey`; no extraction law
  needed.
* **`accepted_funding_attribution`** — `PopKeySoundOn` + `KeyBinding` +
  `K.correctOn` for the funding domain yields an owned funding key, a verifying
  funding signature, and uniqueness of the funding recipient.

### 4.4 Derivation of the inherited `PopSound` layer

* **`popSoundOn_of_keySoundOn`** — key soundness on issued challenges implies
  H22 `PopSoundOn` on the corresponding transcripts.
* `popSoundOn_wellFormed_of_keySoundOn` — the valid-challenge restriction gives
  `PopSoundOn` on 32-byte/32-byte transcripts.
* **`popSound_of_keySoundOn`** — the unrestricted idealised form gives H22
  `PopSound`.
* **`popSound_iff_keySound`** — unrestricted `PopSound` is exactly unrestricted
  `PopKeySoundOn`.
* `accepted_stored_registration` — an accepted fresh session fills the wave-9
  `StoredRegistration` slot.
* **`accepted_stored_registration_attribution`** — constructs that registration
  and invokes the existing
  `AttributionGameTargets.stored_registration_funding_attribution`, with
  `PopSound` itself derived rather than assumed.

`KeyBinding` is **not** derived: `keySound_not_keyBinding` and
`keyBinding_completeness_not_keySound` show the three properties are logically
independent. The module only consumes the unchanged contract.

### 4.5 Sharp negatives and the preventing hypothesis

| Theorem | Counterexample | What it shows |
|---|---|---|
| **`unbound_replay_accepts`** | `acceptsClaimed` verifies `challengeMessage r.challenge`; an old response with `c₁` is accepted by the session whose challenge is `c₂` | The verifier must compare the response challenge with the session challenge, or recompute from the session challenge as `accepts` does. |
| **`nonceFree_replay_accepts`** | `challengeMessageNoNonce` omits the nonce; same channel id, distinct nonces, one signature accepted twice | The freshness nonce must be inside the signed bytes. |
| **`challengeMessage_not_injective_without_valid`** | `([0x61] , [0x62,0x63])` and `([0x61,0x62] , [0x63])` encode identically, both invalid | Fixed-width `Valid` is necessary for injectivity; this is the H22 split issue. |
| **`binding_fails_without_valid`** | The same colliding pair is accepted by the session-bound `accepts` for both challenges | `PopChallenge.Valid` is a necessary hypothesis of `accepts_challenge_bound`, not a convenience. |
| **`replay_of_same_challenge`** | If two sessions share a challenge and key, acceptance transfers | Session identity alone is not a separator. |
| **`repeated_challenge_replay`** | Two distinct session handles, the same valid challenge, one response accepted by both | `FreshOn`/never re-issuing a challenge is exactly the excluding discipline. |

The preventing hypotheses are therefore: (i) sign all of
`popTag ++ channelId ++ nonce`, (ii) enforce fixed-width `Valid`, (iii) verify
from the session challenge rather than the response claim, and (iv) issue each
challenge at most once (`FreshOn`).

### 4.6 Separation and non-vacuity

* **`keySound_not_provenance`** — the pinned verifier/key model accepts a
  one-byte signature that is not the honest all-zero signature of any owned key.
  Acceptance plus possession does not imply `PopProducedBy`/extraction.
* **`keySound_not_keyBinding`** — H22's two-key model has PoP key soundness but
  violates `KeyBinding`.
* **`keyBinding_completeness_not_keySound`** — `EufCma` + `KeyBinding` + total
  signing completeness do not imply PoP key soundness.
* **`protocol_nonvacuous`** — a concrete `selfSigModel`/`selfSigKeyModel` witness
  with `EufCma`, `KeyBinding`, a valid accept-bound challenge, an advertised
  funding key, an accepted honest response, `PopKeySoundOn`,
  `PopExtractionOn`, ownership, and funding-signature uniqueness.
* **`pop_protocol_summary`** — bundles the binding theorem, honest completeness,
  key soundness, extraction provenance, the unbound replay, the no-`Valid`
  replay, and the possession-without-provenance separation.

## 5. Validation

### 5.1 Scoped build

Command:

```sh
export PATH=/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Proofs.Crypto.PopProtocolTargets
```

Result:

```text
✔ [36/36] Built LnLean.Proofs.Crypto.PopProtocolTargets (940ms)
Build completed successfully (36 jobs).
```

No errors and no warnings from the owned module. Final line count: **967**.

### 5.2 Axiom audit

Every public theorem was audited with `#print axioms` from a temporary file
outside the repository. Allowed set: `propext`, `Quot.sound`,
`Classical.choice`.

| Theorem | Axioms |
|---|---|
| `challengeMessage_injective_of_valid` | `propext`, `Quot.sound` |
| `accepts_challenge_bound` | `propext`, `Quot.sound` |
| `no_cross_session_replay` | `propext`, `Quot.sound` |
| `honestResponse_producedBy` | none |
| `honestResponse_accepts` | none |
| `advertised_honest_completeness` | none |
| `advertised_honest_popAccepted` | none |
| `honestResponse_registers` | `propext`, `Quot.sound` |
| `storedAccept_honest_registration` | none |
| `popKeySoundOn_of_extraction` | none |
| `accepted_owns` | none |
| `accepted_provenance` | none |
| `popProducedBy_iff_producedBy` | `propext` |
| `accepted_popProducedBy` | `propext` |
| `accepted_key_unique` | none |
| `accepted_funding_attribution` | none |
| `popSoundOn_of_keySoundOn` | none |
| `popSoundOn_wellFormed_of_keySoundOn` | none |
| `popSound_of_keySoundOn` | none |
| `popSound_iff_keySound` | none |
| `accepted_stored_registration` | none |
| `accepted_stored_registration_attribution` | `propext`, `Quot.sound` |
| `keySound_not_provenance` | `propext`, `Quot.sound` |
| `keySound_not_keyBinding` | `propext`, `Quot.sound` |
| `keyBinding_completeness_not_keySound` | `propext`, `Quot.sound` |
| `unbound_replay_accepts` | `propext`, `Quot.sound` |
| `nonceFree_replay_accepts` | `propext`, `Quot.sound` |
| `challengeMessage_not_injective_without_valid` | `propext`, `Quot.sound` |
| `binding_fails_without_valid` | `propext`, `Quot.sound` |
| `replay_of_same_challenge` | none |
| `repeated_challenge_replay` | `propext`, `Quot.sound` |
| `protocol_nonvacuous` | `propext`, `Quot.sound` |
| `pop_protocol_summary` | `propext`, `Quot.sound` |

`Classical.choice` is not used; no axiom outside the allowed set appears.

### 5.3 Forbidden-token scan

The repo's `scripts/check.py` comment-stripping logic was applied to the owned
module. Result: **zero** matches for
`sorry|axiom|admit|native_decide|unsafe|@[implemented_by]`, and no
`OBLIGATION` marker is needed. The module contains no `admit`, no
`native_decide`, no `unsafe`, and no `@[implemented_by]`; it is Lean 4 core
only.

## 6. Precise remaining assumption boundary

This lane models the **algebraic** challenge-response protocol, not a deployed
signature scheme. The boundary is:

1. **C3 / `EufCma`.** `PrimitiveModel.ecdsa_eufCma` is the algebraic
   message-binding consequence of EUF-CMA: one key and one signature cannot
   verify on two different messages. It is not computational unforgeability and
   says nothing about key generation, hashing, or secp256k1.
2. **Key ownership.** `PopKeySoundOn` is an explicit knowledge-soundness law:
   accepted issued response ⇒ an owned secret key. `PopExtractionOn` is the
   stronger exact-signature law. Neither is derived from `EufCma`,
   `KeyBinding`, or signing completeness; the separation theorems show it.
   A real deployment must obtain one of them from the signature scheme and
   challenge hygiene.
3. **`KeyBinding`.** The module consumes the unchanged contract for funding-key
   attribution and does not derive it. The wave-9 `StoredAccept` and the
   `FundingSigningLaw` totality caveat are untouched.
4. **Noise / transport identity.** `accepts` authenticates *knowledge of the
   funding key over an authenticated challenge channel*. It does not model BOLT
   8 Noise, session establishment, peer identity, or message delivery. The
   challenge channel must be authenticated and freshly issued by the verifier;
   otherwise an active attacker can relay or substitute challenges. The protocol
   does not authenticate the peer's transport identity.
5. **No real cryptography.** No secp256k1 arithmetic, DER encoding, hash
   function, randomness, probability, or computational game is modelled. The
   nonce is an abstract byte string; `FreshOn` is a predicate on verifier
   behaviour, not a random-sampling guarantee.

For `PR-01`, the remaining work is therefore the production instantiation of the
challenge channel (authenticated Noise session + verifier-side nonce issuance)
and the cryptographic knowledge-soundness argument. The encoding, freshness
discipline, completeness, conditional soundness, wave-9 composition, replay
negatives, and non-vacuity are mechanised here.

## 7. Catalog integration recommendation (`LN-PR-003`)

The lane did not edit the catalog. Recommend the parent:

1. Add the module to the root import set (`LnLean.lean`):

   ```lean
   import LnLean.Proofs.Crypto.PopProtocolTargets
   ```

2. Append these exact targets to the `LN-PR-003` `leanTarget` string in
   `LnLean/Proofs/Obligations.lean` (and regenerate
   `agents/status/obligations.json`):

   ```text
   LnLean.Proofs.Crypto.PopProtocolTargets.challengeMessage_injective_of_valid;
   LnLean.Proofs.Crypto.PopProtocolTargets.accepts_challenge_bound;
   LnLean.Proofs.Crypto.PopProtocolTargets.no_cross_session_replay;
   LnLean.Proofs.Crypto.PopProtocolTargets.advertised_honest_completeness;
   LnLean.Proofs.Crypto.PopProtocolTargets.storedAccept_honest_registration;
   LnLean.Proofs.Crypto.PopProtocolTargets.accepted_owns;
   LnLean.Proofs.Crypto.PopProtocolTargets.accepted_funding_attribution;
   LnLean.Proofs.Crypto.PopProtocolTargets.popSound_of_keySoundOn;
   LnLean.Proofs.Crypto.PopProtocolTargets.accepted_stored_registration_attribution;
   LnLean.Proofs.Crypto.PopProtocolTargets.unbound_replay_accepts;
   LnLean.Proofs.Crypto.PopProtocolTargets.nonceFree_replay_accepts;
   LnLean.Proofs.Crypto.PopProtocolTargets.challengeMessage_not_injective_without_valid;
   LnLean.Proofs.Crypto.PopProtocolTargets.binding_fails_without_valid;
   LnLean.Proofs.Crypto.PopProtocolTargets.repeated_challenge_replay;
   LnLean.Proofs.Crypto.PopProtocolTargets.keySound_not_provenance;
   LnLean.Proofs.Crypto.PopProtocolTargets.protocol_nonvacuous;
   LnLean.Proofs.Crypto.PopProtocolTargets.pop_protocol_summary
   ```

3. Append to the `LN-PR-003` claim (after the existing final sentence):

   > A concrete challenge-response PoP protocol is modelled over the existing
   > key model: the signed message is `popTag ++ channelId ++ nonce`, fixed-width
   > validity makes the encoding injective, and the session-bound verifier
   > recomputes it from the verifier's challenge. Honest completeness against the
   > advertised funding key, wave-9 `StoredRegistration` composition, and
   > conditional funding attribution are proved. `PopKeySoundOn` (accepted issued
   > response ⇒ key ownership) is the weakest law used; `PopExtractionOn` derives
   > H22 `PopSound`/`PopSoundOn` and wave-9 `PopProducedBy`. Unbound-challenge,
   > nonce-free, no-`Valid`, and reused-challenge replay are mechanised
   > counterexamples, with `EufCma` + `Valid` + injectivity + freshness identified
   > as the preventing hypotheses. A non-vacuous witness is included; no real
   > signature scheme, computational EUF-CMA, or Noise transport authentication is
   > claimed.

4. Add the public theorems above to `AxiomAudit.lean`; all are
   `propext`/`Quot.sound`/none, so the allowed-axiom gate stays green.

5. Add the module to the `LN-PR-003` traceability target list in
   `LnLean/Proofs/Traceability.lean`.

This is a recommendation only. The lane did not edit `Obligations.lean`,
`Traceability.lean`, `AxiomAudit.lean`, `LnLean.lean`, docs, or any shared file,
and did not commit or push.
