# S11 — Model non-vacuity audit

**Task.** Add a mechanized non-vacuity audit for the core catalog structures
and predicates, together with a report that records exactly what was audited,
what was proved empty, and what remains outside the audit.

**Owned deliverables.**

| Path | Status |
| --- | --- |
| `LnLean/Proofs/Model/NonVacuityTargets.lean` | new, 831 lines |
| `agents/reports/swarm11/S11-MODEL-NONVACUITY.md` | new, this report |

No existing Lean module, root import, catalog, traceability file, audit file,
documentation page, script, or test was modified.  No commit or push was made.

**Module namespace.** `LnLean.Proofs.Model.NonVacuityTargets` (line 68, closed
at line 831).

**One-sentence scope.** The module exhibits explicit values for a finite list
of core carrier structures and predicates, proves that several deliberately
vacuous interfaces have no accepting witness, and proves a registry soundness
theorem; it does **not** claim that the whole protocol, the whole catalog, or
every catalog theorem is non-vacuous.

---

## 1. Build and static checks

### 1.1 Scoped build

Command actually run:

```text
cd /home/ubuntu/ln-lean-repair && \
  LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Proofs.Model.NonVacuityTargets
```

Result:

```text
⚠ [90/90] Built LnLean.Proofs.Model.NonVacuityTargets (1.2s)
Build completed successfully (90 jobs).
```

The build emitted only non-fatal style warnings in this module: deprecation
warnings for `if_pos` / `if_neg` and one `unnecessarySimpa` suggestion.
There were no errors, no `sorry` warnings, and no declaration-level warnings
about missing proofs.

### 1.2 Forbidden-token scan

Command:

```text
grep -nE "sorry|admit|native_decide|unsafe|implemented_by|\baxiom\b" \
  LnLean/Proofs/Model/NonVacuityTargets.lean
```

Result: no matches (`CLEAN`).

The module therefore contains none of `sorry`, `admit`, `native_decide`,
`unsafe`, `@[implemented_by]`, or `axiom` declarations.

### 1.3 Axiom audit

An external audit file `/tmp/opencode/nonvacuity_axioms.lean` imports the
module and runs `#print axioms` on every public theorem (47 theorems).  It was
checked with:

```text
cd /home/ubuntu/ln-lean-repair && \
  lake env lean /tmp/opencode/nonvacuity_axioms.lean
```

Result: exit code `0`.  Every reported dependency is a subset of

```text
{ propext, Quot.sound, Classical.choice }
```

No theorem depends on `sorryAx`, no theorem depends on a user axiom, and no
theorem depends on an implementation-only constant.

The complete result table is reproduced in §5.

---

## 2. What "non-vacuity" means here

For a carrier type `T`, the audit records a term `t : T`.  This is an
`Inhabited`/existential statement at the Lean model interface.  It says that
the structure is not empty *as a type*.

For a predicate `P : T → Prop`, the audit records a pair `(t, h)` with
`h : P t`.  This says that the predicate has at least one witness.

Neither form implies any of the following:

1. that every value of the carrier satisfies the predicate;
2. that a catalog theorem quantified over all values is non-vacuous;
3. that a protocol execution reaches the witness;
4. that the witness is cryptographically meaningful outside the model.

Point 2 is made explicit by `witness_not_universal` (§7.3).  Point 3 is not
mechanized here because no execution engine is imported; it is listed as a
non-goal in §9.

---

## 3. Concrete audit infrastructure

The module is self-contained but imports the wave-9/10 target modules for
re-use (lines 52–66): `LnLean.Basic.Core`, `Channel.Types`,
`Channel.Commitment`, `Routing.Gossip`, `Protocol.Handshake`,
`Crypto.Model`, `Crypto.KeyModel`, `Crypto.Sig`, `Crypto.EcdsaProps`,
`Crypto.KeyModelTargets`, `Routing.NodeIdentityTargets`,
`Channel.CoverageWitnessTargets`, `Bitcoin.EcdsaBridgeTargets`,
`Bitcoin.EcdsaConcreteTargets`, and `Bitcoin.EcdsaDomainTargets`.

### 3.1 Audit keys

| Declaration | Line | Definition |
| --- | --- | --- |
| `key0` | 88 | `⟨ByteArray.empty⟩` |
| `key1` | 91 | `⟨ByteArray.mk #[0x01]⟩` |

`key0_ne_key1` (line 333) proves the two keys differ by comparing byte-array
sizes (`0` versus `1`).

### 3.2 Audit hash

`auditHash` (line 98) is the identity on 32-byte inputs and the all-zero
32-byte string otherwise.  `auditHash_size` (line 102) proves
`∀ b, (auditHash b).size = 32`; `auditHash_collisionResistant` (line 109)
proves `CollisionResistant auditHash`.  The second is a genuine proof: on
32-byte inputs the function is the identity.

### 3.3 Audit signature interface

`auditEcdsaVerify` (line 118) accepts exactly the empty message:

```lean
def auditEcdsaVerify (_pk : PubKey) (msg : ByteArray) (_sig : EcdsaSig) : Bool :=
  decide (msg = ByteArray.empty)
```

`auditSchnorrVerify` (line 131) is the same decision at type `SchnorrSig`.
`auditEcdsa_eufCma` (line 123) and `auditSchnorr_eufCma` (line 135) prove
`EufCma` for the two verifiers.  Both proofs use `of_decide_eq_true` to turn
acceptance into message equality.  This is the representative
signature-interface witness: the interface is inhabited **and** it accepts at
least one input.

### 3.4 Complete non-vacuous model

`auditModel` (line 144) is a total `PrimitiveModel`.  `sha256` is `auditHash`;
`hash160` and `hmacSha256` return zero strings of the required widths;
`ecdsaVerify`/`schnorrVerify` are the audit verifiers; `ecdh` and `hkdf` return
zero strings; `aeadSeal` is the identity and `aeadOpen` returns `some` of its
input, so both AEAD laws hold definitionally; the two C3 fields are
`auditEcdsa_eufCma` and `auditSchnorr_eufCma`.

`auditModel_accepts_empty` (line 168) proves the empty input is accepted, and
`auditModel_rejects_nonempty` (line 174) proves every non-empty input is
rejected.

### 3.5 Intentionally vacuous model

`vacuousEcdsaModel` (line 181) replaces a model's verifier by the constant
`false` function.  `vacuousEcdsaModel_eufCma` (line 189) still proves the C3
field, while `vacuousEcdsaModel_accepts_nothing` (line 194) proves no
`(pk, msg, sig)` is accepted.  Both models satisfy the same C3 interface,
while only `auditModel` has an accepted input.

---

## 4. Positive witnesses

### 4.1 Core structures

| # | Structure | Witness | Theorem | Line |
| --- | --- | --- | --- | --- |
| 1 | `Commitment` | `commitmentWitness` | `commitment_witness` | 217 |
| 2 | `CommitmentTx` | `commitmentTxWitness` | `commitmentTx_witness` | 239 |
| 3 | `GossipState` | `gossipStateWitness` | `gossipState_witness` | 254 |
| 4 | `OpenChannel` | `openChannelWitness` | `openChannel_witness` | 299 |
| 5 | `CoverageWitness` | `coverageWitnessWitness` | `coverageWitness_witness` | 325 |
| 6 | `RotationWitness` | `rotationWitnessWitness` | `rotationWitness_witness` | 349 |
| 7 | `HandshakeState` | `HandshakeState.initial` | `handshakeState_witness` | 359 |
| 8 | `PrimitiveModel` | `auditModel` | `primitiveModel_witness` | 367 |
| 9 | `KeyModel M` | `pinnedKeyModel auditModel key0 pinnedMessage` | `keyModel_witness` | 383 |
| 10 | `AcceptChannel` | `acceptChannelWithFundingKey key0` | `acceptChannel_witness` | 392 |

`KeyModel` is indexed by `M`, so its witness is the dependent existential in
`keyModel_witness`, not a global `Inhabited` instance.  `Inhabited` instances
are provided for `Commitment` (line 224), `CommitmentTx` (246), `GossipState`
(260), `OpenChannel` (305), `CoverageWitness` (329), `RotationWitness` (354),
`HandshakeState` (363), and `PrimitiveModel` (376).

#### Commitment details

`commitmentWitness` (line 205) has `fundingValueSat = 1000`,
`toLocalSat = 600`, `toRemoteSat = 300`, `feeSat = 100`, plus zero/false
defaults for the remaining fields.  `commitment_witness` proves the fields and
the conservation equation `600 + 300 + 100 = 1000` by `decide`.

`commitmentTxWitness` (line 229) pairs that commitment with explicit scripts
(`0x51`–`0x55`), `dustLimitSat = 0`, and the identity HTLC-script function.
`commitmentTx_witness` also proves `tx.toLocalOutput.isSome = true`.

#### Gossip details

`gossipStateWitness` (line 250) is the empty store, with all three lists
empty and `latestUpdateTimestamp = 0`.  `gossipNodeAnnouncement` (line 264)
is a node announcement for `key0`; `gossipStateNode` (line 274) stores exactly
that announcement; `gossipState_nodeAnnounced` (line 280) is the positive
`NodeAnnounced` witness.

#### Coverage and rotation details

`coverageEntry` (line 310) is one `SignedHtlcEntry` (id `1`, amount `1000`,
32-byte hash/digest, 64-byte signature); `coverageWitnessWitness` (line 321)
wraps it as a one-row witness, and the theorem proves
`w.entries.length = 1`.  `rotationWitnessWitness` (line 342) rotates
`key0 → key1` with 8-byte evidence and `distinct := key0_ne_key1`; the theorem
proves the ids and `w.Links key0 key1`.

### 4.2 `StoredAccept`

`storedAcceptState` (line 397) is `HandshakeState.initial` updated with

```text
acceptChannel? := some (acceptChannelWithFundingKey key0)
acceptReceived := true
```

`storedAccept_witness` (line 404) existentially quantifies the model, key
model, seed, handshake state, and accept payload, and proves

```lean
StoredAccept K seed s m ∧ s.acceptReceived = true
```

This is a predicate witness, not just an `Inhabited` structure witness.

### 4.3 Validity predicates

| Predicate | Witness theorem | Line | Witness value |
| --- | --- | --- | --- |
| `ChannelId.Valid` | `channelId_valid_witness` | 418 | `ChannelId.zero` |
| `PubKey.Valid` | `pubKey_valid_witness` | 422 | `⟨zeros 33⟩` |
| `PaymentHash.Valid` | `paymentHash_valid_witness` | 426 | `⟨zeros 32⟩` |
| `GossipSignature.Valid` | `gossipSignature_valid_witness` | 430 | `⟨zeros 64⟩` |

### 4.4 Positive digest domains

| Domain | Theorem | Line | Witness |
| --- | --- | --- | --- |
| `Canonical33` | `canonical33_witness` | 435 | `zeros 33` via `canonical33_zeros` |
| `CanonicalDigest32` | `canonical32_witness` | 439 | `zeros 32` via `canonical32_zeros` |
| `DigestBindsModOn Canonical33 fundingTag` | `canonicalDomain_binds` | 445 | `digestBindsModOn_canonical33 fundingTag` |

The third theorem is important for scope: the *untyped* `DigestBindsMod`
predicate is empty (§6), while the *typed* predicate on the canonical 33-byte
domain is non-vacuous.

### 4.5 Signature-interface witnesses

| Theorem | Line | Content |
| --- | --- | --- |
| `primitiveModel_witness` | 367 | a model with C3 and at least one accepted input |
| `keyModel_witness` | 383 | a generated key pair satisfying `Owns` |
| `eufCma_nonvacuous_witness` | 451 | a `verify` function satisfying C3 with an accepted input |
| `auditModel_accepts_empty` | 168 | the concrete accepted input |

`keyModel_witness` uses the wave-10 pinned key model:

```lean
pinnedModel auditModel key0 pinnedMessage
pinnedKeyModel auditModel key0 pinnedMessage
```

and the ownership lemma

```lean
LnLean.Crypto.KeyModel.owns_generated
```

applied at seed `ByteArray.empty`.  `pinnedMessage` (line 380) is
`fundingTag ++ ByteArray.empty`.

---

## 5. Per-theorem axiom audit

Legend: `P` = `propext`, `Q` = `Quot.sound`, `C` = `Classical.choice`.

| # | Public theorem | Axioms |
| --- | --- | --- |
| 1 | `auditHash_size` | P |
| 2 | `auditHash_collisionResistant` | none |
| 3 | `auditEcdsa_eufCma` | P, Q |
| 4 | `auditSchnorr_eufCma` | P, Q |
| 5 | `auditModel_accepts_empty` | P, Q |
| 6 | `auditModel_rejects_nonempty` | P, Q |
| 7 | `vacuousEcdsaModel_eufCma` | P |
| 8 | `vacuousEcdsaModel_accepts_nothing` | P |
| 9 | `commitment_witness` | none |
| 10 | `commitmentTx_witness` | P |
| 11 | `gossipState_witness` | none |
| 12 | `gossipState_nodeAnnounced` | P |
| 13 | `gossipStateWitness_not_nodeAnnounced` | P |
| 14 | `openChannel_witness` | none |
| 15 | `coverageWitness_witness` | none |
| 16 | `key0_ne_key1` | P, Q |
| 17 | `rotationWitness_witness` | P, Q |
| 18 | `handshakeState_witness` | none |
| 19 | `primitiveModel_witness` | P, Q |
| 20 | `keyModel_witness` | P, Q |
| 21 | `acceptChannel_witness` | none |
| 22 | `storedAccept_witness` | P, Q |
| 23 | `channelId_valid_witness` | none |
| 24 | `pubKey_valid_witness` | P |
| 25 | `paymentHash_valid_witness` | P |
| 26 | `gossipSignature_valid_witness` | P |
| 27 | `canonical33_witness` | P, Q |
| 28 | `canonical32_witness` | P, Q |
| 29 | `canonicalDomain_binds` | P, C, Q |
| 30 | `eufCma_nonvacuous_witness` | P, Q |
| 31 | `oneSigWire_no_empty_decode` | P, Q |
| 32 | `fundingTag_digestBindsMod_empty` | P, Q |
| 33 | `digestBindsMod_uninhabited` | P, C, Q |
| 34 | `nBytes33_not_canonical` | none |
| 35 | `bridgedFundingWitness_uninhabited` | P, C, Q |
| 36 | `withVendorEcdsa_funding_uninhabited` | P, C, Q |
| 37 | `withVendorEcdsa_accepts_nothing` | P, C, Q |
| 38 | `vendorVerify_no_acceptance_of_eufCma` | P, C, Q |
| 39 | `withVendorEcdsa_value_exists` | P, C, Q |
| 40 | `vacuous_nonvacuous_separation` | P, Q |
| 41 | `witness_not_universal` | P, C, Q |
| 42 | `witnessRegistry_length` | P, C, Q |
| 43 | `witnessRegistry_sound` | P, C, Q |
| 44 | `witnessRegistryIds_length` | P, C, Q |
| 45 | `witnessRegistryIds_nodup` | P, C, Q |
| 46 | `witnessRegistry_ne_nil` | P, C, Q |
| 47 | `witnessRegistry_ids_nodup` | P, C, Q |

47 public theorems.  The smallest dependency set is empty; the largest is the
allowed three-axiom set.

---

## 6. Negative and boundary witnesses

The audit contains more than the required three negative/boundary results.

### 6.1 A wire that cannot decode to the empty coverage list

`oneSigWire` (line 463) is a `CommitmentSigned` value with one signature and
one HTLC signature.  The theorem `oneSigWire_no_empty_decode` (line 470)
proves:

```lean
¬ ∃ w : CoverageWitness, decodeCoverage oneSigWire w = some []
```

Proof sketch, as mechanized:

1. If the wire HTLC count equals the witness row count, unfolding
   `decodeCoverage` yields `some (w.entries.map ...)`.
2. Injectivity of `some` makes the mapped list `[]`.
3. A mapped list is empty only if the source list is empty, so
   `w.entries.length = 0`.
4. The wire count is `1`, contradicting the equality from step 1.
5. If the counts differ, `decodeCoverage` is `none`, contradicting `some []`.

This is a boundary result about the decoder, not a claim that coverage is
impossible in general: `coverageWitness_witness` supplies a one-row witness
for the corresponding non-empty shape.

### 6.2 The empty gossip store announces no key

`gossipStateWitness_not_nodeAnnounced` (line 286) proves:

```lean
¬ NodeAnnounced gossipStateWitness key0
```

The proof destructs a hypothetical announcement list membership and simplifies
the empty store to `False`.

This is the same predicate that is positively witnessed on `gossipStateNode`
by `gossipState_nodeAnnounced`.  The pair is a concrete positive/negative
separation for `NodeAnnounced`.

### 6.3 The untyped funding-tag predicate is empty

| Theorem | Line | Statement |
| --- | --- | --- |
| `fundingTag_digestBindsMod_empty` | 488 | `¬ DigestBindsMod fundingTag` |
| `digestBindsMod_uninhabited` | 493 | `¬ ∃ tag, DigestBindsMod tag` |

Both reuse the imported wave-10 results
`not_digestBindsMod_fundingTag` and `no_digestBindsMod_anywhere`.
`digestBindsMod_uninhabited` is stronger: no tag whatsoever has a witness on
the untyped interface.

### 6.4 The canonical repair excludes the bad suffix

`nBytes33_not_canonical` (line 498) proves:

```lean
¬ Canonical33 nBytes33
```

This uses the imported `not_canonical33_nBytes33`.  It is the negative half of
the domain repair whose positive half is `canonical33_witness`.

### 6.5 The vendor bridge cannot fund

`BridgedFundingWitness` (line 503) is a structure with fields:

```text
model : PrimitiveModel
bridge : VendorEcdsaBridge model
key : PubKey
tx : ByteArray
sig : EcdsaSig
checked : verifyFundingChecked model key tx sig = true
```

`bridgedFundingWitness_uninhabited` (line 512) proves:

```lean
¬ Nonempty BridgedFundingWitness
```

The proof applies `bridged_model_totalReject` to obtain

```lean
w.model.ecdsaVerify w.key (fundingTag ++ w.tx) w.sig = false
```

and then rewrites `verifyFundingChecked` / `verifyFunding` in the `checked`
field until `false = true` is exposed.

This is the strongest negative form in the module: the structure is not merely
without a known witness; it has no inhabitant at all under the bridge.

---

## 7. Vacuity results for intentionally vacuous interfaces

### 7.1 `withVendorEcdsa`

The module reuses `withVendorEcdsa` from
`LnLean.Proofs.Bitcoin.EcdsaBridgeTargets` and proves four results:

| Theorem | Line | Statement |
| --- | --- | --- |
| `withVendorEcdsa_funding_uninhabited` | 524 | no `(key, tx, sig)` passes `verifyFundingChecked` at `withVendorEcdsa M₀ hEuf` |
| `withVendorEcdsa_accepts_nothing` | 535 | no `(pk, msg, sig)` is accepted by `(withVendorEcdsa M₀ hEuf).ecdsaVerify` |
| `vendorVerify_no_acceptance_of_eufCma` | 547 | `EufCma vendorVerify → ¬ ∃ pk msg sig, vendorVerify pk msg sig = true` |
| `withVendorEcdsa_value_exists` | 559 | the model value itself exists under `hEuf` |

The first three say that the verification relation is empty.  The fourth says
that the model *value* exists.  Together they record the precise situation:

```text
the model type is inhabited; the protocol relation at that model is empty.
```

This is exactly the vacuity that the catalog must not silently treat as a
positive assumption.

### 7.2 The local `vacuousEcdsaModel`

`vacuousEcdsaModel_accepts_nothing` (line 194) proves the constant-`false`
verifier accepts nothing for every model `M`.  Its companion
`vacuousEcdsaModel_eufCma` (line 189) proves that the C3 field still holds.
Thus C3 alone cannot distinguish a usable verifier from a total rejector.

### 7.3 Separation theorems

`vacuous_nonvacuous_separation` (line 569) proves the four-part conjunction:

1. `EufCma auditModel.ecdsaVerify`;
2. `auditModel` accepts at least one input;
3. `EufCma (vacuousEcdsaModel auditModel).ecdsaVerify`;
4. `vacuousEcdsaModel auditModel` accepts nothing.

`witness_not_universal` (line 585) proves:

```lean
(∃ c : Commitment, c.fundingValueSat = 1000) ∧
  (¬ ∃ tag : ByteArray, DigestBindsMod tag)
```

This is the scope statement in theorem form: a `Commitment` witness does not
repair an unrelated empty predicate, and by extension no single carrier
witness establishes non-vacuity of the catalog as a whole.

---

## 8. Witness registry

### 8.1 Types

`WitnessId` (line 593) is an inductive enumeration with 30 constructors and
derived `Repr`, `DecidableEq`, and `BEq`.

`WitnessKind` (line 627) classifies entries as:

```text
structure | predicate | positiveDomain | signatureInterface |
negativeBoundary | vacuity | separation
```

`AuditedWitness` (line 640) is a dependent record:

```lean
structure AuditedWitness where
  id : WitnessId
  kind : WitnessKind
  theoremName : String
  statement : Prop
  proof : statement
```

Because `proof : statement` is a field, a registry entry cannot exist without
a kernel-checked proof of its own proposition.  The registry is therefore not
a list of theorem names or strings; it is a sound dependent list.

### 8.2 Registry contents

`witnessRegistry` (line 649) has 30 entries.

| # | Id | Kind | Theorem | Line |
| --- | --- | --- | --- | --- |
| 1 | `commitment` | structure | `commitment_witness` | 217 |
| 2 | `commitmentTx` | structure | `commitmentTx_witness` | 239 |
| 3 | `gossipState` | structure | `gossipState_witness` | 254 |
| 4 | `gossipNodeAnnounced` | predicate | `gossipState_nodeAnnounced` | 280 |
| 5 | `openChannel` | structure | `openChannel_witness` | 299 |
| 6 | `coverageWitness` | structure | `coverageWitness_witness` | 325 |
| 7 | `coverageNoEmptyDecode` | negativeBoundary | `oneSigWire_no_empty_decode` | 470 |
| 8 | `rotationWitness` | structure | `rotationWitness_witness` | 349 |
| 9 | `handshakeState` | structure | `handshakeState_witness` | 359 |
| 10 | `primitiveModel` | structure | `primitiveModel_witness` | 367 |
| 11 | `keyModel` | structure | `keyModel_witness` | 383 |
| 12 | `acceptChannel` | structure | `acceptChannel_witness` | 392 |
| 13 | `storedAccept` | predicate | `storedAccept_witness` | 404 |
| 14 | `channelIdValid` | predicate | `channelId_valid_witness` | 418 |
| 15 | `pubKeyValid` | predicate | `pubKey_valid_witness` | 422 |
| 16 | `paymentHashValid` | predicate | `paymentHash_valid_witness` | 426 |
| 17 | `gossipSignatureValid` | predicate | `gossipSignature_valid_witness` | 430 |
| 18 | `canonical33` | positiveDomain | `canonical33_witness` | 435 |
| 19 | `canonical32` | positiveDomain | `canonical32_witness` | 439 |
| 20 | `canonicalBinding` | positiveDomain | `canonicalDomain_binds` | 445 |
| 21 | `eufCmaNonvacuous` | signatureInterface | `eufCma_nonvacuous_witness` | 451 |
| 22 | `gossipEmptyNoAnnouncement` | negativeBoundary | `gossipStateWitness_not_nodeAnnounced` | 286 |
| 23 | `fundingTagDigestEmpty` | negativeBoundary | `fundingTag_digestBindsMod_empty` | 488 |
| 24 | `digestBindsModEmpty` | negativeBoundary | `digestBindsMod_uninhabited` | 493 |
| 25 | `nBytes33NotCanonical` | negativeBoundary | `nBytes33_not_canonical` | 498 |
| 26 | `bridgedFundingEmpty` | vacuity | `bridgedFundingWitness_uninhabited` | 512 |
| 27 | `withVendorFundingEmpty` | vacuity | `withVendorEcdsa_funding_uninhabited` | 524 |
| 28 | `withVendorAcceptsNothing` | vacuity | `withVendorEcdsa_accepts_nothing` | 535 |
| 29 | `vacuousNonvacuous` | separation | `vacuous_nonvacuous_separation` | 569 |
| 30 | `scopeSeparation` | separation | `witness_not_universal` | 585 |

### 8.3 Registry theorems

| Theorem | Line | Statement |
| --- | --- | --- |
| `witnessRegistry_length` | 803 | `witnessRegistry.length = 30` |
| `witnessRegistry_sound` | 807 | `∀ e ∈ witnessRegistry, e.statement` |
| `witnessRegistryIds_length` | 816 | `witnessRegistryIds.length = 30` |
| `witnessRegistryIds_nodup` | 819 | `witnessRegistryIds.Nodup` |
| `witnessRegistry_ne_nil` | 823 | `witnessRegistry ≠ []` |
| `witnessRegistry_ids_nodup` | 827 | `(witnessRegistry.map (fun e => e.id)).Nodup` |

`witnessRegistry_sound` is the key theorem: it projects the proof field of
every entry.  `witnessRegistryIds_nodup` is decided by computation over the
30-constructor enumeration.  The id projection is defined at line 812.

### 8.4 Coverage of the requested core items

The requested minimum was at least 10 core structures/predicates, including
`Commitment`, `CommitmentTx`, `GossipState`, `OpenChannel`, `StoredAccept`,
`CoverageWitness`, `RotationWitness`, positive domains, and a representative
signature interface.

All of those items are present:

- structures 1–13 in the registry;
- positive domains 18–20;
- signature interface 21;
- validity predicates 14–17;
- negative boundary 7, 22–25;
- vacuity 26–28;
- separation 29–30.

---

## 9. Integration notes

### 9.1 Safe integration points

The module is standalone and has no root import.  It can be imported by a
future audit module without changing any existing file.  The intended public
surface is:

- `witnessRegistry` and `witnessRegistry_sound` for a registry view;
- `witnessRegistryIds_nodup` for id hygiene;
- the positive witness theorems for carrier/predicate existence;
- the negative/vacuity theorems for catalog warnings.

### 9.2 What downstream modules may conclude

A downstream module may conclude exactly the registered proposition.  For
example:

- `commitment_witness` gives a `Commitment` with the stated field values;
- `storedAccept_witness` gives a handshake state satisfying `StoredAccept`;
- `withVendorEcdsa_funding_uninhabited` says the vendor-funded relation has
  no witness;
- `digestBindsMod_uninhabited` says the untyped digest-binding predicate is
  empty.

A downstream module may **not** conclude:

- that every `Commitment` is conserved;
- that every `GossipState` announces a key;
- that `withVendorEcdsa` is a usable model (it is a value whose verifier
  rejects everything);
- that the catalog's universally quantified theorems are non-vacuous merely
  because their carrier types are inhabited.

### 9.3 Relation to other waves

The module reuses, without modifying: wave-10 `KeyModelTargets` for
`pinnedModel`, `pinnedKeyModel`, `acceptChannelWithFundingKey`, `StoredAccept`,
and `AdvertisesKey`; `NodeIdentityTargets` for `NodeAnnounced` and
`RotationWitness`; `CoverageWitnessTargets` for `CoverageWitness` and
`decodeCoverage`; `EcdsaBridgeTargets` / `EcdsaConcreteTargets` for
`VendorEcdsaBridge`, `withVendorEcdsa`, `vendorVerify`,
`verifyFundingChecked`, `withVendorEcdsa_no_funding`,
`withVendorEcdsa_totalReject`, `eufCma_vendorVerify_iff_totalReject`, and
`bridged_model_totalReject`; and `EcdsaDomainTargets` for `Canonical33`,
`CanonicalDigest32`, `DigestBindsModOn`, `canonical33_zeros`,
`canonical32_zeros`, `digestBindsModOn_canonical33`,
`no_digestBindsMod_anywhere`, and `not_canonical33_nBytes33`.  No transitive
declaration was redefined, renamed, or shadowed.

### 9.4 Suggested catalog annotation

If the catalog later records non-vacuity status, the registry is the natural
machine-readable source.  A catalog entry should reference both:

1. the `WitnessId`; and
2. the registered `statement`.

Recording only the theorem name would lose the distinction between a carrier
witness and a predicate witness.  Recording only "non-vacuous" would lose the
negative entries.

---

## 10. Limits and non-goals

The following are explicitly **not** mechanized:

1. **No protocol execution.**  There is no reachability proof from an initial
   state to a commitment, gossip, or funding event.  `Reachable` is only used
   for the initial handshake state.
2. **No secp256k1 arithmetic.**  `auditEcdsaVerify` is a message-bound decision
   procedure, not an ECDSA implementation.
3. **No real key generation.**  `pinnedKeyModel` is a wave-10 model-level
   construction; it does not generate cryptographically secure keys.
4. **No hash preimage/collision claims beyond the model.**  `auditHash` is
   injective on 32-byte inputs by construction, which is stronger than a
   computational collision-resistance assumption and is used only to inhabit
   the `CollisionResistant` field.
5. **No claim about every catalog theorem.**  The registry audits 30 named
   items out of the whole catalog.
6. **No claim that a carrier witness implies a theorem's hypotheses hold.**
   For example, `Commitment` being inhabited does not supply the side
   conditions of an arbitrary commitment theorem.
7. **No claim that `withVendorEcdsa` is unusable as a value.**  It is a value;
   what is empty is its verification/funding relation.
8. **No computational security game.**  C3 is the exact message-binding
   consequence used by the scaffold, not a probability statement.

---

## 11. Reproduction checklist

1. Build:

   ```text
   cd /home/ubuntu/ln-lean-repair && \
     LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
     lake build LnLean.Proofs.Model.NonVacuityTargets
   ```

   Expected: `Build completed successfully`.

2. Forbidden-token scan:

   ```text
   grep -nE "sorry|admit|native_decide|unsafe|implemented_by|\baxiom\b" \
     LnLean/Proofs/Model/NonVacuityTargets.lean
   ```

   Expected: no output.

3. Axiom audit:

   ```text
   cd /home/ubuntu/ln-lean-repair && \
     lake env lean /tmp/opencode/nonvacuity_axioms.lean
   ```

   Expected: exit `0`; only `propext`, `Quot.sound`, and
   `Classical.choice` (or no axioms) are listed.

4. Registry checks:

   ```text
   #check LnLean.Proofs.Model.NonVacuityTargets.witnessRegistry_length
   #check LnLean.Proofs.Model.NonVacuityTargets.witnessRegistry_sound
   ```

   Expected: `= 30` and `∀ e ∈ witnessRegistry, e.statement`.

---

## 12. Summary

- 47 public theorems, all axiom-clean within the allowed set.
- 30 registry entries, each carrying its own proposition and proof.
- 10 core structures plus `StoredAccept` and four validity predicates.
- 2 positive digest domains plus one typed binding theorem.
- 1 representative non-vacuous signature interface with an accepted input.
- 5 negative/boundary results (more than the required 3).
- 3 vacuity results for `withVendorEcdsa`, plus the local
  `vacuousEcdsaModel` separation and the `BridgedFundingWitness` emptiness
  theorem.
- 2 explicit separation/scope theorems.
- No existing file modified; no commit or push.
