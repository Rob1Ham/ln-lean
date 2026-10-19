# S9-PR-ATTRIBUTION — registration/PoP game over `StoredAccept` (PR-01)

## Objective

Model a registration / proof-of-possession (PoP) game on top of the stored
`accept_channel` payload (`StoredAccept`) and prove:

1. the strongest true key-attribution contract, conditional on the unchanged
   `KeyBinding` hypothesis plus explicit generation/signature hypotheses;
2. that storing a payload (and even accepting a PoP transcript) is not by
   itself proof of possession;
3. a mechanised counterexample showing that dropping `KeyBinding` breaks the
   attribution conclusion;
4. the totality / `FundingSigningLaw` boundary, without assuming a total
   signing law.

Lane base: `50e8b5c` on `repair/integrated`.  No shared file, Git state, or
other lane's artifact was modified.

## Artifact

- New module: `LnLean/Proofs/Crypto/AttributionGameTargets.lean`
- New report: `agents/reports/swarm9/S9-PR-ATTRIBUTION.md` (this file)

The module imports (does not edit) `AcceptPayloadTargets`, `KeyModelTargets`,
`WaveH/H21`, and `WaveH/H22`.  It reuses H22's exact PoP extraction law
`PopSound` and its transcript encoding, and specialises the game to the actual
handshake state predicate `StoredAccept`.

## Definitions added

| Name | Meaning |
|---|---|
| `KeyBinding` | Re-export of the unchanged `LnLean.Proofs.WaveE.E06.KeyBinding`; spelled locally to avoid the signature-layer `Crypto.KeyBinding` ambiguity. |
| `PopTranscript` | H22's PoP transcript (`channelId`, verifier-issued `challenge`, `signature`). |
| `popMessage` | H22's `popTag ++ channelId ++ challenge` signed bytes. |
| `PopAccepted M pk t` | H22's verifier predicate for a PoP transcript under `pk`. |
| `PopSound M K` | H22's exact extraction law: every accepted issued transcript yields a secret key owned for the advertised public key. |
| `StoredRegistration M K seed s m t` | The game transcript over state: `StoredAccept K seed s m`, `t.channelId = m.temporaryChannelId.bytes`, and `PopAccepted M m.fundingPubKey t`. |
| `PopProducedBy K sk t` | Explicit signature-provenance hypothesis: `t.signature = K.sign sk (popMessage t)`. |

## Exact claims (full theorem names)

All names are in
`LnLean.Proofs.Crypto.AttributionGameTargets`.

### State-level game

- `register_of_storedRegistration` — a `StoredRegistration` is exactly a
  successful executable H22 registration:
  `register M m t = some { accept := m, transcript := t }`.
- `storedRegistration_storedAccept`
- `storedRegistration_channelBound`
- `storedRegistration_popAccepted`

### Possession and attribution

- `stored_registration_owns_funding_key` — under `PopSound M K`, a stored
  registration yields `∃ sk, K.Owns m.fundingPubKey sk`.  This is the point
  where acceptance becomes possession; it is **not** derived from storage.
- `stored_registration_funding_attribution` — under `PopSound M K` and
  `KeyBinding M.ecdsaVerify`, a stored registration and domain-scoped
  correctness on the funding message yield an owned `sk` such that the honest
  funding signature verifies under `m.fundingPubKey` and every accepting key is
  `m.fundingPubKey`.
- `stored_pop_provenance_possession` — with explicit production
  `PopProducedBy K (K.secretOfSeed seed) t`, the stored key is owned by the
  generated secret key.
- `stored_pop_attribution` — the sharp signature-level contract: from
  `StoredAccept`, `PopProducedBy`, `K.correctOn (popMessage t)`, and
  `KeyBinding`, every key accepting the PoP signature is `m.fundingPubKey`.
- `stored_pop_attribution_contract` — bundled form of the three conclusions
  above (ownership, honest verification, full key attribution).

### Negative results

- `stored_payload_not_possession` — for every base primitive model there is a
  full `EufCma` model, a `PayloadReachable` state with `StoredAccept`, an
  accepted PoP transcript under the stored key, **and** the same transcript
  accepted under a second key that key generation cannot produce.  The theorem
  also proves `¬ PopSound M K` and `¬ KeyBinding M.ecdsaVerify`.  Thus storage
  plus registration acceptance alone does not establish possession or key
  uniqueness.
- `stored_payload_not_popSound` — storage-only corollary: a
  payload-reachable state can store an `accept_channel` in a model where the
  PoP extraction law fails.
- `stored_attribution_fails_without_keyBinding` — for every base model there
  is a payload-reachable stored `accept_channel` advertising `k₀`, a
  domain-correct honest funding signature from the stored seed, and a distinct
  key `k₁` under which the same signature verifies, with
  `¬ KeyBinding M.ecdsaVerify`.  This refutes the attribution conclusion when
  the `KeyBinding` premise is dropped.
- `stored_registration_contract_nonvacuous` — concrete witness satisfying C3,
  `PopSound`, `KeyBinding`, a stored registration, domain-scoped correctness,
  and the attribution conclusion.
- `attribution_game_summary` — bundled conjunction of the stored-game bridge,
  possession, conditional attribution, provenance contract, storage negative,
  key-binding counterexample, and non-vacuity.

## Validation

Environment:

```bash
export PATH=/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
```

Scoped build under the shared lock:

```bash
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Proofs.Crypto.AttributionGameTargets
```

Result:

```text
✔ [35/35] Built LnLean.Proofs.Crypto.AttributionGameTargets (893ms)
Build completed successfully (35 jobs).
```

Forbidden-token scan over the owned module:

```bash
grep -nE '\b(sorry|axiom|admit|native_decide|unsafe)\b|implemented_by' \
  LnLean/Proofs/Crypto/AttributionGameTargets.lean
```

Result: no matches.

Axiom audit (temporary `/tmp/opencode/check_attr_axioms.lean`, not committed):

```bash
lake env lean /tmp/opencode/check_attr_axioms.lean
```

Results:

```text
register_of_storedRegistration                 depends on [propext, Quot.sound]
stored_registration_owns_funding_key           depends on [propext, Quot.sound]
stored_registration_funding_attribution        depends on [propext, Quot.sound]
stored_pop_attribution                         no axioms
stored_pop_attribution_contract                no axioms
stored_payload_not_possession                  depends on [propext, Quot.sound]
stored_payload_not_popSound                    depends on [propext, Quot.sound]
stored_attribution_fails_without_keyBinding    depends on [propext, Quot.sound]
stored_registration_contract_nonvacuous        depends on [propext, Quot.sound]
attribution_game_summary                       depends on [propext, Quot.sound]
```

No `Classical.choice` was needed.  The audit stays within the allowed set
`propext`, `Quot.sound`, `Classical.choice`.

## Trust boundary / gaps

- `PopSound` is an algebraic extraction law, not a computational reduction.
  It is the exact missing knowledge-soundness premise for the registration
  game.  The module proves what follows from it and mechanises what fails
  without it.  A deployment must instantiate it from a knowledge-sound
  signature scheme plus challenge freshness.
- Challenge freshness is not modelled: H22's `PopSoundOn` records it as an
  explicit issue predicate; this module uses the unrestricted `PopSound`.
- `PopProducedBy` is explicit.  Verification alone never proves which secret
  key produced a signature; `KeyBinding` constrains the key for a fixed
  signature but does not supply provenance.
- `StoredAccept`'s `AdvertisesKey` link remains an explicit generation
  hypothesis.  `stored_registration_owns_funding_key` derives ownership only
  after `PopSound`; storage itself does not.
- The PoP transcript encoding (`popTag ++ channelId ++ challenge`) has no
  length prefixes; H22's `popMessage_split_not_injective` records the
  corresponding channel-binding caveat.  Ownership attribution does not depend
  on the split being injective.
- **Totality / `FundingSigningLaw` boundary.**  The game uses
  `KeyModel.correctOn` only at `popMessage t` and at
  `fundingTag ++ fundingTx`.  It does not assume `KeyModel.Total` or a total
  `FundingSigningLaw`; the totality tension mechanised by
  `KeyModelTargets.fundingSigningLaw_sign_injective` is unchanged.  Any
  consumer needing completeness on arbitrary bytes must discharge that
  separately.
- No secp256k1 arithmetic, nonce/seed entropy, Noise transport authentication,
  or probabilistic adversary is modelled.
- No core hook is needed.  All additions are in the owned module; the only
  integration requirement is to import it and register the target names.

## Catalog integration recommendation for `PR-01`

1. Add `import LnLean.Proofs.Crypto.AttributionGameTargets` to `LnLean.lean`
   (parent integration step; not done in this lane).
2. Extend the existing `PR-01` row rather than opening a new issue.  Suggested
   primary names:
   - `LnLean.Proofs.Crypto.AttributionGameTargets.stored_registration_funding_attribution`
   - `...stored_pop_attribution`
   - `...stored_payload_not_possession`
   - `...stored_attribution_fails_without_keyBinding`
   - `...attribution_game_summary`
3. Record the trust boundary text from this report: `PopSound` is an explicit
   extraction hypothesis, `PopProducedBy` is explicit provenance, and
   `KeyBinding` remains a hypothesis (not derived from C3).  Do **not** claim
   registration or storage is possession.
4. Add the same theorem names to obligations/traceability/audit in the parent
   integration commit.  `attribution_game_summary` is the convenient bundled
   catalog target; the three focused theorems above should remain listed so the
   negative and conditional boundaries are not hidden by the bundle.
5. No duplicate of H22 is needed: the catalog text should cite H22's
   `PopSound` and `pop_acceptance_not_possession` as dependencies, and this
   module as the state-level `StoredAccept` specialisation.

## Summary

- **Status:** lane complete.
- **Owned module:** `LnLean/Proofs/Crypto/AttributionGameTargets.lean`
- **Report:** `agents/reports/swarm9/S9-PR-ATTRIBUTION.md`
- **Build:** `lake build LnLean.Proofs.Crypto.AttributionGameTargets` → 35/35
  jobs, RC 0.
- **No forbidden constructs or axioms** outside `propext` / `Quot.sound`.
- **Key theorem names:**
  `register_of_storedRegistration`,
  `stored_registration_owns_funding_key`,
  `stored_registration_funding_attribution`,
  `stored_pop_provenance_possession`,
  `stored_pop_attribution`,
  `stored_pop_attribution_contract`,
  `stored_payload_not_possession`,
  `stored_payload_not_popSound`,
  `stored_attribution_fails_without_keyBinding`,
  `stored_registration_contract_nonvacuous`,
  `attribution_game_summary`.
- **Core patch required:** none.
