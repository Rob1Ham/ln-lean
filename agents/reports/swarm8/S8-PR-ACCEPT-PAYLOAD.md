# S8-PR-ACCEPT-PAYLOAD — `accept_channel?` storage and the key-attribution bridge

**Lane:** `S8-PR-ACCEPT-PAYLOAD`
**Issue:** `PR-01` (P1, open — registration bridge added; attribution still conditional)
**Worktree:** `/home/ubuntu/ln-lean-repair`
**Base:** `repair/integrated` (wave-8 launch `50d78ed`; current tree `60318ad`)
**Toolchain:** `leanprover/lean4:v4.35.0`
**Owned files:**

| File | Change |
|---|---|
| `LnLean/Protocol/Handshake.lean` | +325/−1: payload field, writer, payload machine, provenance/stability lemmas |
| `LnLean/Proofs/Crypto/KeyModelTargets.lean` | +42: `StoredAccept` and the stored-payload attribution bridge |
| `LnLean/Proofs/Crypto/AcceptPayloadTargets.lean` | **new**, 332 lines: storage facts, negotiation bridge, attribution contract, negative result, non-vacuity, summary |
| `agents/reports/swarm8/S8-PR-ACCEPT-PAYLOAD.md` | This report |

**Verdict.** PR-01's missing state connection is closed in the strongest form
that is true in this model:

1. `HandshakeState` now stores the received `accept_channel` payload in
   `acceptChannel?`, and the only writer is the payload-carrying receive step
   `handshakeStepRecvAccept`.
2. In the payload-reachable machine the stored payload is **exactly** the
   received payload, it has an actual receive transition as provenance, it is
   stable under all later steps, and the `acceptReceived` milestone holds iff a
   payload is stored.
3. Under the unchanged `LnLean.Proofs.WaveE.E06.KeyBinding` **and** the
   explicit `AdvertisesKey` link, the stored
   `acceptChannel.funding_pubkey` is the only key that can accept the signer's
   funding-domain signature; the same theorem exposes the handshake
   negotiation's `remoteFundingKey`.
4. Wave 7's negative result is preserved and lifted to a payload-reachable
   state: a stored `funding_pubkey = pk₁` can coexist with a validating
   signature produced by `sk₂`, with C3 (`EufCma`) true and `KeyBinding` false.
   **Payload registration is not proof of possession.**
5. C3 is never used to derive `KeyBinding` or attribution. `KeyBinding` and
   `AdvertisesKey` remain explicit hypotheses.

No `sorry`, `axiom`, `admit`, `native_decide`, `unsafe`, or
`@[implemented_by]`; all reported theorems use only `propext`, `Quot.sound`,
and `Classical.choice`.

---

## 1. Exact field and step changes

### 1.1 `HandshakeState` (`LnLean/Protocol/Handshake.lean`)

```lean
structure HandshakeState where
  ...
  acceptChannelSent : Bool := false
  acceptChannelReceived : Bool := false
  ...
  /-- The BOLT 2 `accept_channel` (type 33) payload this endpoint received,
  recorded by the payload-carrying receive path `handshakeStepRecvAccept`.
  `none` means no payload has been recorded. ... -/
  acceptChannel? : Option AcceptChannel := none
deriving Repr, BEq
```

* The field defaults to `none`; every pre-existing constructor and record
  update keeps compiling unchanged.
* **Integration note:** `DecidableEq` was removed from the deriving clause.
  `AcceptChannel`, `PubKey`, and `ChannelId` only derive `Repr`/`BEq` in the
  wire model, so the structure cannot derive `DecidableEq`. No theorem or
  executable path in the tree used decidable equality on `HandshakeState`;
  the full build confirms this. Milestone-flag equality remains available via
  `BEq`. Restoring `DecidableEq` would require adding it to those wire types,
  which is outside this lane.
* `recordAccept s a := { s with acceptChannel? := some a }` is the only
  payload writer. `forgetAcceptChannel s := { s with acceptChannel? := none }`
  is the projection used to compare the payload machine with the original
  milestone machine.

### 1.2 Receive step

`HandshakeEvent.recvAcceptChannel` stays **nullary**. Changing it to carry an
`AcceptChannel` would break every downstream `HandshakeEvent` match
(`LnLean.Protocol.Peer.receiveEvent?`, `WaveD/D18`, `WaveD/D21`, …). Instead
the payload is attached additively:

```lean
def handshakeStepRecvAccept (s : HandshakeState) (a : AcceptChannel) :
    Option HandshakeState :=
  match handshakeStep s .recvAcceptChannel with
  | some s' => some (s'.recordAccept a)
  | none => none
```

* `handshakeStep` itself is unchanged, so all existing milestone proofs and
  `Peer` matches are untouched.
* The send path deliberately does **not** write `acceptChannel?`: a locally
  chosen payload is not evidence about the peer (`sent_accept_does_not_store`).
* The payload machine rejects the bare `.plain .recvAcceptChannel` event, so a
  receive cannot set the milestone without recording a payload:

```lean
inductive HandshakePayloadEvent
  | plain (e : HandshakeEvent)
  | recvAccept (a : AcceptChannel)

def handshakePayloadStep ...
inductive PayloadReachable ...
```

### 1.3 Lemma inventory (state level)

| Declaration | Meaning |
|---|---|
| `handshakeStepRecvAccept_underlying` | payload receive = milestone receive followed by `recordAccept` |
| `acceptChannel?_of_handshakeStepRecvAccept` | recorded payload is exactly the one carried |
| `acceptReceived_of_handshakeStepRecvAccept` | payload receive sets the milestone |
| `handshakeStep_acceptChannel?_preserved` | ordinary milestone steps never change the field |
| `handshakeStep_acceptReceived_eq` | only `.recvAcceptChannel` changes `acceptReceived` |
| `sendAcceptChannel_acceptChannel?_preserved`, `sent_accept_does_not_store` | send path does not fabricate peer evidence |
| `handshakeStep_forgetAcceptChannel` | forgetting the payload commutes with one milestone step |
| `reachable_acceptChannel?_none` | original milestone-reachable states store no payload |
| `payloadReachable_forget_reachable` | payload-reachable states project to milestone-reachable states |
| `payloadReachable_acceptReceived_iff` | milestone set iff payload present |
| `payloadReachable_acceptReceived_payload` | milestone implies a stored payload exists |
| `payloadReachable_acceptChannel?_received` | stored payload implies the milestone |
| `payloadReachable_acceptChannel?_provenance` | every stored payload has a real receive transition |
| `payloadReachable_acceptChannel?_stable` | no later step replaces a stored payload |

### 1.4 Key-model layer (`KeyModelTargets.lean` §8)

```lean
def StoredAccept (K : KeyModel M) (seed : ByteArray)
    (s : HandshakeState) (m : AcceptChannel) : Prop :=
  s.acceptChannel? = some m ∧ AdvertisesKey K seed m
```

`storedAccept_acceptChannel?`, `storedAccept_fundingPubKey`, and
`storedAccept_attribution` project the two components and recover wave-7's
`funding_signature_attribution` under the unchanged `KeyBinding`.

---

## 2. Theorem signatures (new module `AcceptPayloadTargets.lean`)

Namespace `LnLean.Proofs.Crypto.AcceptPayloadTargets`; state lemmas live in
`LnLean.Protocol`.

```lean
theorem recvAccept_records_exact {s s' : HandshakeState} {a : AcceptChannel}
    (h : handshakeStepRecvAccept s a = some s') :
    s'.acceptChannel? = some a ∧ s'.acceptReceived = true

theorem payloadReachable_acceptPayload_exact {s : HandshakeState}
    {a : AcceptChannel} (h : PayloadReachable s) (ha : s.acceptChannel? = some a) :
    s.acceptReceived = true ∧
      ∃ s0 s1 : HandshakeState,
        PayloadReachable s0 ∧ handshakeStepRecvAccept s0 a = some s1

def acceptNegotiation? (s : HandshakeState) (localFundingKey : PubKey)
    (fundingSatoshis : BtcAmount) (pushMsat : Msat)
    (temporaryChannelId : TemporaryChannelId) :
    Option LnLean.Bitcoin.FundingNegotiation

theorem stored_accept_negotiation_remoteFundingKey {s : HandshakeState}
    {a : AcceptChannel} (_h : s.acceptChannel? = some a) ... :
    (a.toFundingNegotiation ...).remoteFundingKey = a.fundingPubKey

theorem stored_accept_negotiation_advertisedKey {M : PrimitiveModel}
    (K : KeyModel M) {seed : ByteArray} {s : HandshakeState}
    {a : AcceptChannel} (h : s.acceptChannel? = some a)
    (hadv : AdvertisesKey K seed a) ... :
    (a.toFundingNegotiation ...).remoteFundingKey = K.publicOfSeed seed

theorem stored_accept_payload_attribution {M : PrimitiveModel} (K : KeyModel M)
    (hkb : KeyBinding M.ecdsaVerify) {s : HandshakeState} {a : AcceptChannel}
    (hstore : s.acceptChannel? = some a) (seed : ByteArray)
    (hadv : AdvertisesKey K seed a) {fundingTx : ByteArray}
    (hdom : K.correctOn (fundingTag ++ fundingTx)) {pk' : PubKey}
    (hver : M.ecdsaVerify pk' (fundingTag ++ fundingTx)
      (K.sign (K.secretOfSeed seed) (fundingTag ++ fundingTx)) = true) :
    pk' = a.fundingPubKey

theorem reachable_stored_accept_attribution {M : PrimitiveModel}
    (K : KeyModel M) (hkb : KeyBinding M.ecdsaVerify) {s : HandshakeState}
    {a : AcceptChannel} (_hreach : PayloadReachable s) ... :
    pk' = a.fundingPubKey

theorem acceptPayload_not_proof_of_possession (M₀ : PrimitiveModel) :
    ∃ (M : PrimitiveModel) (K : KeyModel M) (s : HandshakeState)
      (a : AcceptChannel) (seed₁ seed₂ : ByteArray) (fundingTx : ByteArray),
      PayloadReachable s ∧ s.acceptChannel? = some a ∧
      s.acceptReceived = true ∧
      K.publicOfSeed seed₁ ≠ K.publicOfSeed seed₂ ∧
      K.secretOfSeed seed₁ ≠ K.secretOfSeed seed₂ ∧
      EufCma M.ecdsaVerify ∧ AdvertisesKey K seed₁ a ∧
      K.correctOn (fundingTag ++ fundingTx) ∧
      M.ecdsaVerify a.fundingPubKey (fundingTag ++ fundingTx)
        (K.sign (K.secretOfSeed seed₂) (fundingTag ++ fundingTx)) = true ∧
      K.sign (K.secretOfSeed seed₁) (fundingTag ++ fundingTx) =
        K.sign (K.secretOfSeed seed₂) (fundingTag ++ fundingTx) ∧
      ¬ KeyBinding M.ecdsaVerify

theorem stored_accept_contract_nonvacuous (M₀ : PrimitiveModel) (k₀ : PubKey) :
    ∃ (M : PrimitiveModel) (K : KeyModel M) (s : HandshakeState)
      (a : AcceptChannel) (seed : ByteArray) (fundingTx : ByteArray),
      PayloadReachable s ∧ s.acceptChannel? = some a ∧
      s.acceptReceived = true ∧ EufCma M.ecdsaVerify ∧
      KeyBinding M.ecdsaVerify ∧ WireShaped K ∧ AdvertisesKey K seed a ∧
      K.correctOn (fundingTag ++ fundingTx) ∧
      (∀ pk', M.ecdsaVerify pk' (fundingTag ++ fundingTx)
        (K.sign (K.secretOfSeed seed) (fundingTag ++ fundingTx)) = true →
        pk' = a.fundingPubKey)

theorem accept_payload_summary : ...  -- conjunction of (1), (3), (4) above
```

Witness states: `afterInit` (both `init` messages, no payload) and
`withAccept a` (payload received), with `afterInit_payloadReachable` and
`withAccept_payloadReachable a`.

---

## 3. Build result

Scoped:

```text
$ LEAN_NUM_THREADS=1 lake build LnLean.Proofs.Crypto.AcceptPayloadTargets
Build completed successfully (28 jobs), RC 0, no warnings.
```

Full build under the shared lock, after all lane edits in the working tree:

```text
$ LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock lake build
Build completed successfully (233 jobs).
RC=0
```

Only pre-existing unrelated warnings appear. `Peer.lean`,
`Protocol/HandshakeProps.lean`, `WaveD/D18`, `WaveD/D21`, and all other
downstream consumers still compile.

---

## 4. Axiom result

Measured with `#print axioms` in a scratch file under `lake env lean`
(`/tmp/opencode/accept_payload_axioms.lean`, not part of the tree):

| Theorem | Axioms |
|---|---|
| `recvAccept_records_exact` | `propext` |
| `payloadReachable_acceptReceived_iff` | `propext` |
| `payloadReachable_acceptChannel?_provenance` | `propext` |
| `payloadReachable_acceptChannel?_stable` | `propext` |
| `stored_accept_payload_attribution` | **none** |
| `acceptPayload_not_proof_of_possession` | `propext`, `Quot.sound` |
| `stored_accept_contract_nonvacuous` | `propext`, `Classical.choice`, `Quot.sound` |
| `accept_payload_summary` | `propext`, `Quot.sound` |
| `KeyModelTargets.storedAccept_attribution` | **none** |
| `handshakeStepRecvAccept_underlying` | `propext` |
| `payloadReachable_forget_reachable` | `propext` |

No undeclared axiom, no `sorryAx`, no compiler-trust dependency. The negative
result is especially cheap: it needs no `Classical.choice`.

---

## 5. Forbidden-construct scan

```text
$ grep -nE '\b(sorry|axiom|admit|native_decide|unsafe)\b|implemented_by' \
    LnLean/Protocol/Handshake.lean \
    LnLean/Proofs/Crypto/KeyModelTargets.lean \
    LnLean/Proofs/Crypto/AcceptPayloadTargets.lean
NO FORBIDDEN CONSTRUCTS
```

The scan reports no matches at all, including inside comments: the three files
contain none of these tokens.

---

## 6. Registration vs. proof-of-possession boundary

**What the field proves (registration):**

* The stored payload is **not user-supplied state**: it is set only by
  `handshakeStepRecvAccept`, and every stored payload in a payload-reachable
  state has a concrete receive transition as provenance
  (`payloadReachable_acceptChannel?_provenance`).
* The payload cannot be silently swapped: a later step preserves it
  (`payloadReachable_acceptChannel?_stable`), because a second receive is
  blocked by the `acceptReceived` guard.
* The boolean milestone and the payload agree
  (`payloadReachable_acceptReceived_iff`), and the original milestone-only
  machine stores nothing (`reachable_acceptChannel?_none`).
* The send path does not record local payloads (`sent_accept_does_not_store`).

**What the field does not prove (possession):**

`acceptPayload_not_proof_of_possession` constructs a payload-reachable state
with `acceptChannel? = some a`, where:

* `a.fundingPubKey = K.publicOfSeed seed₁` (`AdvertisesKey`);
* `K.secretOfSeed seed₂` produces a signature that validates under
  `a.fundingPubKey`;
* the two signatures are identical and the two key pairs are distinct;
* `EufCma M.ecdsaVerify` holds;
* `KeyBinding M.ecdsaVerify` fails.

So a correctly registered `funding_pubkey` may be a key whose secret is not
held by the advertiser. Attribution therefore still needs an explicit
`KeyBinding` hypothesis (or a real registration/possession game, not modelled
here). C3 is never used as that hypothesis.

**Modelled / not modelled.** Modelled: BOLT 2 type-33 payload storage,
milestone coupling, provenance, stability, funding negotiation projection,
conditional attribution, non-vacuity. Not modelled: secp256k1, nonces, seed
entropy, a trusted key-registration directory, proof of possession, and a
computational ownership game.

---

## 7. Integration steps (parent)

The lane did not edit shared files. The parent should apply the following.

1. **Root import.** Run `scripts/regen-root.sh` at integration time; it
   discovers every `LnLean/**/*.lean` file and will add:
   ```lean
   import LnLean.Proofs.Crypto.AcceptPayloadTargets
   ```
   If a hand patch is preferred, insert that line after
   `import LnLean.Proofs.Crypto.KeyModelTargets` in `LnLean.lean`. Do not
   otherwise edit the generated root by hand.

2. **Axiom audit** (`LnLean/Proofs/PhaseC3/AxiomAudit.lean`):
   * add `import LnLean.Proofs.Crypto.AcceptPayloadTargets`;
   * add `#print axioms` entries:
     ```lean
     #print axioms LnLean.Protocol.payloadReachable_acceptChannel?_provenance
     #print axioms LnLean.Proofs.Crypto.AcceptPayloadTargets.stored_accept_payload_attribution
     #print axioms LnLean.Proofs.Crypto.AcceptPayloadTargets.acceptPayload_not_proof_of_possession
     #print axioms LnLean.Proofs.Crypto.AcceptPayloadTargets.accept_payload_summary
     ```
   * append the same four names to `auditedTheorems` and bump
     `auditedTheorems_length` from `194` to `198`.
   * Optionally also audit `stored_accept_contract_nonvacuous`; in that case
     the length is `199`.

3. **Catalog** (`LnLean/Proofs/Obligations.lean`, row `LN-PR-003`): append the
   new targets to `leanTarget` and extend the claim:
   ```text
   ...; LnLean.Proofs.Crypto.AcceptPayloadTargets.stored_accept_payload_attribution;
   LnLean.Proofs.Crypto.AcceptPayloadTargets.acceptPayload_not_proof_of_possession
   ```
   Suggested claim clause: “`HandshakeState` records the received type-33
   payload with a real receive transition as provenance; under the unchanged
   `KeyBinding` and explicit `AdvertisesKey`, the stored `funding_pubkey` is the
   only accepting key, while a mechanised counterexample shows that
   registration is not proof of possession.” Status stays `.proved` because all
   targets are sorry-free; no new row is needed.

4. **Traceability** (`LnLean/Proofs/Traceability.lean`): add
   `LnLean.Proofs.Crypto.AcceptPayloadTargets` to the source-module list for the
   `LN-PR-003` row (currently the row lists `ProtocolSigningTargets`,
   `SighashTargets`, `KeyModelTargets`).

5. **Generated indexes / catalog counts:** regenerate normally after the
   import and catalog edits. The lane did not run `collect-obligations.py` or
   `collect-anchors.py`. Expect catalog counts to remain 48 proved / 79
   targets (target extension, not a new row), or adjust if the parent also adds
   a separate row.

6. **API note for downstream lanes:** `HandshakeState` no longer derives
   `DecidableEq`. Any new code that needs state equality must use `BEq` or
   compare fields. Search for `DecidableEq HandshakeState` before assuming it.

---

## 8. Blockers

**None.** The lane is proof-complete, builds cleanly, and has no forbidden
constructs.

Residual non-blocking boundaries (should be stated in the release notes, not
fixed here):

* `DecidableEq` on `HandshakeState` is gone (wire types lack it).
* `KeyBinding` and `AdvertisesKey` remain explicit hypotheses; no computational
  ownership/registration game is modelled.
* `HandshakeEvent.recvAcceptChannel` is still nullary; payload receipt uses the
  additive `handshakeStepRecvAccept` wrapper. Changing the event constructor
  would require coordinated edits to `Peer.lean` and every `HandshakeEvent`
  match, and is not necessary for the result.
* `funding_pubkey` attribution is one-directional: the stored key is the only
  accepting key *given* `KeyBinding`; the model does not prove that the peer
  actually holds the secret.

---

## 9. Catalog / roadmap recommendation for PR-01

**Status.** Keep `PR-01` **open**, but narrow it from “no payload field / no key
model” to “registration bridge delivered; ownership game still missing”.
Recommended roadmap row:

> `PR-01` | P1 | open (registration bridge; attribution conditional) |
> `AcceptPayloadTargets` adds `HandshakeState.acceptChannel?` with a single
> receive writer, exact-payload/provenance/stability laws, the unchanged
> `KeyBinding` attribution contract from a stored payload, a non-vacuous
> witness, and a lifted `accept_channel` counterexample showing registration is
> not proof of possession. | Remaining action: model a trusted registration /
> proof-of-possession game or a computational ownership reduction; keep
> `KeyBinding`/`AdvertisesKey` explicit until then.

**Wave 8 lane table.** Mark `S8-PR-ACCEPT-PAYLOAD` delivered and note the
additive wrapper deviation from “set it on `recvAcceptChannel`”: the nullary
event and `handshakeStep` are unchanged for compatibility, and the wrapper is
the only payload writer.

**Catalog.** Extend `LN-PR-003` as in §7.3; do **not** claim that C3 implies
key attribution, and do not remove the existing counterexample language. The
catalog status may stay `proved` because the conditional theorem and its
negative companion are both fully checked; “proved” here means “the stated
conditional contract is proved”, not “key ownership is established”.

**Next issue after PR-01.** If the project wants to close the ownership gap,
the honest next step is a new issue (not a silent strengthening of `PR-01`)
covering a registration/PoP game: a trusted directory or a possession proof in
`accept_channel`, plus a reduction from the game to `KeyBinding`. That is a
model extension, not a corollary of this lane.
