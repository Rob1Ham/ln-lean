# S12-AUDIT-BARRIERS — adversarial audit of the open P0/P1 barriers

**Date:** 2026-10-19
**Repository:** `/home/ubuntu/ln-lean-repair`
**Branch:** `repair/integrated`
**Audited HEAD:** `5ddab4c` (status commit after the wave-11 code gate `6a48d41`)
**Mode:** read-only. No source edits, no full-tree build, no push, no catalog edit.
**Single artifact:** this file.

## 0. Bottom line

Nine issues were audited: `L1-01`, `L1-02`, `L1-03`, `L1-07`, `PR-01`, `PR-02`,
`RT-02`, `OPS-02`, `OPS-03`.

- **Zero of the nine are closed at model level.**
- **Two P0s are mechanically blocked by a kernel-checked impossibility at the
  current interface:** `L1-01` and `L1-07`. The concrete vendored verifier
  `verifyImpl` is invariant under zero-padding, and the `PrimitiveModel` type
  carries `ecdsa_eufCma`; consequently every `VendorEcdsaBridge` model rejects
  every input. Any claim of a “non-vacuous concrete EC bridge” at the current
  `ByteArray` message interface is therefore false, not merely unproved.
- **The other seven are externally blocked:** a concrete secp256k1
  implementation/assumption (`L1-02`, and the EC part of `L1-07`), a real
  Noise/AEAD implementation and key ownership (`L1-03`), an extraction-sound
  signature scheme (`PR-01`), a production coverage source or protocol
  extension (`PR-02`), address parsing/chain policy/gossip pipeline (`RT-02`),
  and maintainer release decisions (`OPS-02`, `OPS-03`).
- **The wave-11 modules are real and add genuine negative results**, but several
  headline-shaped theorems are definitional, carry the desired conclusion as a
  hypothesis, or are non-vacuous only in a toy model. The specific flags are in
  §4. The most important are:
  - `RotationCertificate.signed_implies_link` ignores its signature hypothesis;
  - `NoiseTransportTargets.toTransportSession` sets `established := true`, and
    the accepted-frame key-binding theorem does not use handshake soundness;
  - `HtlcAggregateTargets`' list identity is `rfl`, and its
    `DistinctCommitments` hypothesis is unused for that identity;
  - `NonVacuityTargets.witnessRegistry_sound` is projection of the proof stored
    in each registry entry;
  - `NodeCanonicalTargets.epoch_square_lifts_to_node_canonical_view` assumes the
    canonical invariant that node selection is supposed to establish.
- **Wave-13:** no proof lane can close a P0. The only clearly codeable P1 slice
  is `RT-02` BOLT 7 address parsing. A typed-digest model change for
  `L1-01`/`L1-07` is a genuine but risky model change, not a closure. The rest
  is external crypto, protocol design, or human release work.

## 1. Scope, method, and caveats

### 1.1 Documents read

- `docs/OPEN-ISSUES.md` (issue status/roadmap, wave-11 lane table)
- `docs/FINAL-STATUS.md` (catalog caveats, wave-11 module list, gate counts)
- `docs/RELEASE-CHECKLIST.md` (`OPS-02`/`OPS-03` conditions)
- `docs/LICENSE-DECISION.md` (license matrix; explicitly decision-pending)
- `LnLean/Proofs/Obligations.lean` (51-row catalog; issue ids are roadmap ids,
  **not** catalog ids)
- `LnLean/Proofs/PhaseC3/AxiomAudit.lean` (wave-11 imports and axiom pins)

### 1.2 Modules read statement-by-statement

Wave-11 modules:

- `LnLean/Proofs/Routing/NodeIdentityChainTargets.lean`
- `LnLean/Proofs/Protocol/NoiseTransportTargets.lean`
- `LnLean/Proofs/Channel/CoverageSourceTargets.lean`
- `LnLean/Proofs/Security/ChainFinalityTargets.lean`
- `LnLean/Proofs/Payment/InvoiceWireTargets.lean`
- `LnLean/Proofs/Channel/HtlcAggregateTargets.lean`
- `LnLean/Proofs/Model/NonVacuityTargets.lean`

Supporting modules for the issue table:

- `LnLean/Proofs/Bitcoin/EcdsaConcreteTargets.lean`
- `LnLean/Proofs/Bitcoin/EcdsaDomainTargets.lean`
- `LnLean/Proofs/Bitcoin/EcdsaBridgeTargets.lean`
- `LnLean/Proofs/Protocol/TransportAuthTargets.lean`
- `LnLean/Proofs/Crypto/PopProtocolTargets.lean`
- `LnLean/Proofs/Routing/NodeCanonicalTargets.lean`
- `LnLean/Proofs/Channel/CoverageWitnessTargets.lean`
- `LnLean/Proofs/Bitcoin/InterpreterBridgeTargets.lean`
- `LnLean/Proofs/Bitcoin/InterpreterRevocationTargets.lean`
- `LnLean/Proofs/Bitcoin/SequenceContextTargets.lean`
- `LnLean/Proofs/WaveH/H31.lean`
- `LnLean/Crypto/Model.lean`, `LnLean/Routing/Gossip.lean`

### 1.3 Verdict vocabulary

- **closed (model level):** the issue's stated obligation is discharged by a
  kernel-checked theorem at the model boundary, with no remaining explicit
  assumption beyond the documented trust boundary.
- **blocked:** the issue is not closed, and the audit identifies either (a) a
  kernel-checked theorem showing the current interface cannot satisfy it, or
  (b) an exact external object/decision that the tree does not contain.
- **tractable:** a wave can close the issue by code/model work alone, without a
  new cryptographic implementation, protocol change, or human decision.

### 1.4 Caveats

- I did **not** run `lake build`, `#print axioms`, or the gate scripts. The
  existence and statements below were read from source. The docs' gate claims
  (`312` jobs, `407` audited theorems, `51/51` catalog rows) are reported, not
  re-verified here.
- Line numbers are at HEAD `5ddab4c`. Status commits may move them.
- The working tree was already dirty when the audit began:
  `tests/conformance/rust-lightning/generate.py` and `live_probe.rs` were
  modified, and `agents/status/REPAIR.status` was untracked. Concurrent S12
  lanes added further uncommitted work during final verification; that later
  work is outside the audited HEAD and is recorded separately in §8, not relied
  on here.
- `docs/RELEASE-CHECKLIST.md:214` says `origin/main` is `100` commits behind;
  at this HEAD `git rev-list --count origin/main..6a48d41` is **102**. The
  checklist is stale on that number; the blocker itself is unchanged.
- Catalog rows and roadmap ids are not 1:1. For example, `L1-01`/`L1-07` are
  roadmap issues backed by catalog row `LN-L1-001`/`LN-L1-004`, while
  `LN-L1-002` is a different MoneyRange claim. Do not infer issue closure from
  a green `LN-*` row.

## 2. Verdict table

The “exact barrier” column is a compressed statement; §3 gives the full
conditional form for each blocked P0 and §4 audits the wave-11 evidence.

| Issue | Priority | Current status in docs | Verdict | Exact barrier | Evidence (theorem, `file:line`) |
|---|---|---|---|---|---|
| `L1-01` | P0 | open; EC bridge characterized, C3 forces total rejection | **blocked (mechanized impossibility)** | At the untyped `ByteArray` message interface, `verifyImpl` is zero-padding invariant, so `EufCma vendorVerify` holds iff `vendorVerify` rejects every triple. Since `PrimitiveModel` carries `ecdsa_eufCma`, every `VendorEcdsaBridge` model is total-rejecting; no non-vacuous bridged model exists. A faithful non-vacuous contract must use `ResidueBinding ∧ KeyBinding` on a canonical typed digest domain, plus a concrete secp256k1 verifier and the spent outpoint/amount/validity context. | `EcdsaConcreteTargets.verifyImpl_zeroPad` `LnLean/Proofs/Bitcoin/EcdsaConcreteTargets.lean:126`; `eufCma_vendorVerify_iff_totalReject` `:163`; `no_bridged_nontrivial_model` `:252`; `exists_bridged_model_iff_totalReject` `:265`; `VendorEcdsaContract` `:396`; `Crypto/Model.lean:118`; `EcdsaDomainTargets.not_digestBindsMod_any_tag` `LnLean/Proofs/Bitcoin/EcdsaDomainTargets.lean:281`; `no_digestBindsMod_anywhere` `:288`; `not_digestBindsModOn33_any_tag` `:301`; `digestBindsModOn_canonical32` `:438`; `residueBinding_vendor_funding_eq_of_canonical33` `:453`; `EcdsaBridgeTargets.VendorEcdsaBridge` `LnLean/Proofs/Bitcoin/EcdsaBridgeTargets.lean:124`; `fundingSignedValid_iff_vendor` `:295` |
| `L1-02` | P0 | open; `TxValidation.Full` transfer exact, known-amount/EC boundary | **blocked (external EC + amount input)** | For a known spent amount the full-pipeline `txCheckerFor` is definitionally the real checker, and the delayed `to_local` branch is exactly the BIP 68/112 sequence context plus `verifyImpl` acceptance of the BIP 143 digest over the spent amount. No `TxValidation.Full` transfer gap remains; the residual is a verified concrete secp256k1 implementation (or explicit computational assumption) for `verifyImpl`, the actual amount, and the in-range/transaction-validity context. | `H31.txCheckerFor_some_eq_realCheckerOf` `LnLean/Proofs/WaveH/H31.lean:149`; `toLocal_delayed_txCheckerFor_refinement` `:349`; `txCheckerFor_none_ecdsa_false` `:455`; `toLocal_delayed_txCheckerFor_none_not_ok` `:469`; `SequenceContextTargets.checkSequenceDef_delay_iff` `LnLean/Proofs/Bitcoin/SequenceContextTargets.lean:202`; `toLocal_delayed_sequence_context_refinement` `:427`; `checkerOf_eq_realCheckerOf` `:584`; `toLocal_delayed_realChecker_refinement` `:600` |
| `L1-03` | P1 | open; Noise-level binding added, C3/key ownership explicit | **blocked (external real Noise/AEAD + key ownership)** | `TransportAuthenticated` is only the flag `session.established = true`; `SessionKeyBinding` is definitionally `peerKey = wire.fundingPubKey`; the Noise bridge sets `established := true` unconditionally and derives `peerStatic` from the handshake record. Attribution is therefore peer/advertisement equality, not cryptographic authentication. Remaining: a real Noise_XK/AEAD implementation that authenticates the peer static key, C3, key ownership, and finite C1 funding admission. | `TransportAuthTargets.TransportAuthenticated` `LnLean/Proofs/Protocol/TransportAuthTargets.lean:150`; `SessionKeyBinding` `:164`; `envelopeAttributed_iff_sessionKeyBinding` `:188`; `transport_authenticated_attributed` `:211`; `transport_auth_not_from_wire` `:475`; `unattributed_delivery_exists` `:449`; `no_wire_sender_function` `:516`; `NoiseTransportTargets.NoiseDelivery.toTransportSession` `LnLean/Proofs/Protocol/NoiseTransportTargets.lean:574`; `toAuthenticatedDelivery_authenticated` `:594`; `sessionKeyBinding_iff_peerStatic_eq` `:599`; `accepted_frame_yields_sessionKeyBinding` `:619`; `Crypto/Model.lean:118` |
| `L1-07` | P0 | open; known-amount/EC boundary characterized | **blocked (same EC impossibility; positive-direction only)** | Positive funding/delayed/revocation branches execute through the vendored interpreter with a constructed BIP 143 context, but an unconditional `ConsensusSpendBridge` is not available: the concrete EC seam is the same zero-padding/C3 obstruction, and the model covers only positive-direction P2WSH with explicit amount, outpoint, and transaction-validity inputs. | `InterpreterBridgeTargets.funding_interpreters_agree` `LnLean/Proofs/Bitcoin/InterpreterBridgeTargets.lean:756`; `toLocal_delayed_interpreters_agree` `:948`; `InterpreterRevocationTargets.toLocal_revocation_interpreters_agree` `LnLean/Proofs/Bitcoin/InterpreterRevocationTargets.lean:259`; `EcdsaConcreteTargets.eufCma_vendorVerify_iff_totalReject` `LnLean/Proofs/Bitcoin/EcdsaConcreteTargets.lean:163`; `no_bridged_nontrivial_model` `:252`; `EcdsaBridgeTargets.fundingSignedValid_iff_vendor` `LnLean/Proofs/Bitcoin/EcdsaBridgeTargets.lean:295` |
| `PR-01` | P1 | open; PoP game proved, `KeyBinding` still explicit | **blocked (explicit extraction law; toy non-vacuity)** | `accepted_funding_attribution` requires `PopKeySoundOn`, `KeyBinding`, and `K.correctOn`; `PopKeySoundOn`/`PopExtractionOn` are definitions, not derived. `protocol_nonvacuous` instantiates them only in `selfSigModel`, where the “signature” is the message. Remaining: a real EUF-CMA signature scheme with key ownership, freshness, and replay resistance. | `PopProtocolTargets.PopKeySoundOn` `LnLean/Proofs/Crypto/PopProtocolTargets.lean:405`; `PopExtractionOn` `:415`; `accepted_funding_attribution` `:487`; `protocol_nonvacuous` `:834`; `WaveH/H22.selfSigVerify` `LnLean/Proofs/WaveH/H22.lean:696`; `selfSigModel` `:710`; `unbound_replay_accepts` `LnLean/Proofs/Crypto/PopProtocolTargets.lean:668`; `nonceFree_replay_accepts` `:696`; `challengeMessage_not_injective_without_valid` `:725`; `binding_fails_without_valid` `:758`; `repeated_challenge_replay` `:788` |
| `PR-02` | P1 | open; source characterization added, production source absent | **blocked (protocol/source external)** | `decodeCoverage` consumes a witness and checks only the signature count; the legacy wire cannot determine coverage. `CoverageSource` adds full-record, out-of-band, and extension sources; `extension_plus_wire_determines_coverage` is conditional on the proof-carrying `ExtensionBinds`, exact wire projection, and row count. Production coverage still needs an out-of-band/full-record source with provenance or a BOLT 2 protocol extension with a real encoding; neither is derivable from the existing wire. | `CoverageWitnessTargets.decodeCoverage` `LnLean/Proofs/Channel/CoverageWitnessTargets.lean:114`; `decodeCoverage_covers` `:164`; `no_legacy_only_coverage_decoder` `:223`; `no_legacy_only_witness_selector` `:239`; `wire_admits_distinct_coverage_witnesses` `:345`; `CoverageSourceTargets.ExtensionBinds` `LnLean/Proofs/Channel/CoverageSourceTargets.lean:324`; `TrustedOrigin` `:399`; `extension_plus_wire_determines_coverage` `:585`; `no_wire_determined_source` `:675`; `no_wire_source_selector` `:695`; `wire_admits_distinct_out_of_band_witnesses` `:714`; `wireCompatible_not_out_of_band_binding` `:769`; `no_wire_witness_authenticator` `:784` |
| `RT-02` | P1 | open; signed chain/re-signing/rate added, address parsing remains | **blocked; one tractable slice (address parsing)** | Node canonicalization, signed rotation certificates, transitive chains, re-signing, and replay/rate limits are modelled, but `RotationLink` is opaque evidence, `signed_implies_link` ignores its signature hypothesis, `message_eq_rotationMessage` is a structure projection, and the epoch-square lift assumes the `Nodup`/`CanonicalNodeAnnouncements` invariant of the raw fold. Address parsing (`NodeAnnouncement.addresses : List ByteArray`), chain-existence policy, and a production gossip/rotation pipeline remain outside the model. | `Gossip.NodeAnnouncement` `LnLean/Routing/Gossip.lean:200`; `addresses` field `:205`; unmodelled note `:61`; `NodeCanonicalTargets.reachableNodeCanonical_invariant` `LnLean/Proofs/Routing/NodeCanonicalTargets.lean:666`; `reachableNodeCanonical_node_replacement` `:1041`; `reachableNodeCanonical_rotation_keeps_both` `:1060`; `reachableNodeCanonical_equal_timestamp_tie_boundary` `:1114`; `no_canonical_node_preserving_raw_node_extension` `:1159`; `canonicalStoreView_does_not_canonicalise_nodes` `:1189`; `epoch_square_lifts_to_node_canonical_view` `:1278`; `NodeIdentityChainTargets.RotationCertificate.signed_implies_link` `LnLean/Proofs/Routing/NodeIdentityChainTargets.lean:170`; `message_eq_rotationMessage` `:187`; `rateFold_replay_rejected` `:849`; `opaque_link_not_authenticated` `:1106`; `distinct_hops_not_acyclic` `:1120`; `old_signature_does_not_authenticate_new_keys` `:1144`; `signature_preservation_not_universal` `:1157`; `opaque_link_not_imply_signed` `:1168` |
| `OPS-02` | P0 | open; decision support ready | **blocked (human legal decision)** | No `LICENSE`, `COPYING`, `NOTICE`, or `AUTHORS` at the repository root; GitHub reports the license as `None`. A maintainer must choose MIT, Apache-2.0, or dual MIT/Apache-2.0, confirm the copyright holder/authorized licensor, and add the license and third-party notices. An agent cannot invent either the grant or the copyright holder. | No theorem. `docs/RELEASE-CHECKLIST.md:184-207`; `docs/LICENSE-DECISION.md:3-5`, `:62-76`. Verified locally: none of the four files exists; `git tag -l` is empty. |
| `OPS-03` | P0 | open; checklist ready | **blocked (human release decision)** | No release tag. `origin/main` is `b891a59`, 102 commits behind code gate `6a48d41`, with `main` an ancestor of `HEAD`. A maintainer must choose PR vs direct merge, merge-commit vs fast-forward, tag name/version scheme, signed vs annotated, and whether the tag is cut on `main` or `repair/integrated`, then rerun the gate at the exact tag object and publish notes. | No theorem. `docs/RELEASE-CHECKLIST.md:211-270`; local `git tag -l` empty; `git rev-list --count origin/main..6a48d41` = `102`; `git merge-base --is-ancestor origin/main 6a48d41` succeeds. |

## 3. Strongest true remaining conditional form for each blocked P0

### 3.1 `L1-01` — the byte-level bridge is vacuous; the faithful contract is `ResidueBinding ∧ KeyBinding` on a typed/canonical domain

**What is actually proved (non-vacuous content).**

The concrete verifier is a total Boolean function over `(sig, pk, msg)` bytes.
The zero-padding fact is:

```text
verifyImpl_zeroPad : verifyImpl sig pk (zeroPad msg) = verifyImpl sig pk msg
```

at `LnLean/Proofs/Bitcoin/EcdsaConcreteTargets.lean:126`. From it the module
proves:

```text
eufCma_vendorVerify_iff_totalReject :
  EufCma vendorVerify ↔
    ∀ pk msg sig, vendorVerify pk msg sig = false
```

at `EcdsaConcreteTargets.lean:163`. Because `PrimitiveModel` has the field
`ecdsa_eufCma : EufCma ecdsaVerify` (`LnLean/Crypto/Model.lean:118`), a model
that satisfies `VendorEcdsaBridge` is forced to reject every input. This is
exactly `no_bridged_nontrivial_model` at `EcdsaConcreteTargets.lean:252`, and
`exists_bridged_model_iff_totalReject` at `:265` sharpens it to an iff.

**Consequence.** Every theorem whose only EC hypothesis is
`VendorEcdsaBridge M` — including `fundingSignedValid_iff_vendor`
(`LnLean/Proofs/Bitcoin/EcdsaBridgeTargets.lean:295`) and the wave-8 transfer
stack — is **true but vacuous for a non-rejecting verifier**. It cannot be cited
as evidence that a real funding signature is checked. This is the single most
important correction to the catalog narrative: `LN-L1-001` says the concrete
bridge is “characterized”, which is accurate, but a reader must not read the
conditional bridge theorems as non-vacuous.

**The strongest non-vacuous contract available in the tree.**

```text
VendorEcdsaContract := ResidueBinding vendorVerify ∧ KeyBinding vendorVerify
```

at `EcdsaConcreteTargets.lean:396`, where `ResidueBinding` means: any two
messages accepted by the same signature have the same
`bytesToNatBE msg % n`; `KeyBinding` means: any two keys that accept the same
message/signature are equal. Neither is byte-level `EufCma`.

The non-vacuous extraction result is domain-restricted. The general theorem is:

```text
digestBindsModOn_canonicalOfSize (tag) (k) :
  DigestBindsModOn (CanonicalOfSize k) tag
```

at `LnLean/Proofs/Bitcoin/EcdsaDomainTargets.lean:400`, with the 32-byte and
33-byte instances at `:428` and `:438`. `CanonicalOfSize k m` is
`m.size = k ∧ bytesToNatBE m < n` (`:352`). The funding-facing instance is
`residueBinding_vendor_funding_eq_of_canonical33` at `:453`, but its domain is
**exactly 33-byte messages**. A real funding transaction byte string is not 33
bytes. Therefore the catalog claim that this yields “conditional funding
extraction” is stronger than the theorem's scope: it yields extraction for an
abstract 33-byte payload, not for `fundingTag ++ tx` when `tx` is a real
transaction. The plausible typed instance is `CanonicalDigest32` at `:434`/`:438`,
i.e. a 32-byte BIP 143 digest that has already been checked to be `< n`; that
is a different interface from the current `verifyFunding` (`fundingTag ++ tx`).

**Exact remaining external requirement.** Choose one:

1. a concrete secp256k1 verifier whose accepted-message relation is
   `ResidueBinding` and whose key relation is `KeyBinding`, plus a canonical
   message encoding (typed 32-byte digest or a checked canonical 33-byte
   payload) that rejects non-reduced encodings; or
2. an explicit computational EUF-CMA assumption at a typed digest interface,
   with `KeyBinding` and key ownership supplied separately.

In both cases the spent outpoint, spent amount, and transaction-validity
context remain explicit inputs. None of these is in the tree.

### 3.2 `L1-02` — the transfer is complete; only the concrete verifier and amount remain

The strongest true conditional is the delayed-branch iff:

```text
toLocal_delayed_txCheckerFor_refinement
  (tx) (nIn) (amount) (hIn) ... :
  verifyWitnessProgram 10 [sig, empty, toLocalOps ...] ... 
    (txCheckerFor tx nIn (some amount)) false = .ok
  ↔
  (¬ tx.version < 2) ∧
  (sequence disable bit = 0) ∧
  (type/mask < type flag) ∧
  (csv ≤ sequence & mask) ∧
  verifyImpl (sig minus hashtype) delayedPaymentKey.bytes
    (sighashWitnessV0 tx nIn scriptCode hashtype amount) = true
```

at `LnLean/Proofs/WaveH/H31.lean:349`; the real-checker version is
`toLocal_delayed_realChecker_refinement` at
`LnLean/Proofs/Bitcoin/SequenceContextTargets.lean:600`. The full-pipeline
equality `txCheckerFor tx nIn (some amount) = realCheckerOf tx nIn amount` is
unconditional at `H31.lean:149`.

The missing-amount case is genuinely rejected, not silently accepted:

```text
toLocal_delayed_txCheckerFor_none_not_ok
```

at `H31.lean:469`, with the ECDSA fail-closed fact at `:455`.

**Exact remaining external requirement.** A verified concrete secp256k1
implementation/refinement for `verifyImpl` (or an explicit computational
assumption), the actual spent amount, and the in-range/transaction-validity
context. There is **no `TxValidation.Full` transfer gap** left; do not schedule
a wave to “close a transfer gap” that is already closed.

### 3.3 `L1-07` — positive-direction interpreter agreement, not an unconditional consensus bridge

The genuine positive-direction results are:

- `funding_interpreters_agree` at
  `LnLean/Proofs/Bitcoin/InterpreterBridgeTargets.lean:756` — the vendored
  P2WSH verifier returns `.ok` and the wave-4 model spends, **under the same
  two `chk.base.checkECDSASignature` hypotheses**;
- `toLocal_delayed_interpreters_agree` at `:948`;
- `toLocal_revocation_interpreters_agree` at
  `LnLean/Proofs/Bitcoin/InterpreterRevocationTargets.lean:259`.

All three are relative agreements between the vendored interpreter and the
model checker. They are not proofs that a real on-chain spend succeeds.

The unconditional `ConsensusSpendBridge` would need: all L1 branches (not only
the positive direction), a concrete EC verifier, a canonical digest interface,
and the transaction-validity/spent-amount context. The EC part is blocked by
the same `eufCma_vendorVerify_iff_totalReject`/`no_bridged_nontrivial_model`
obstruction as `L1-01`; the interpreter part is blocked by the missing
concrete EC refinement. Do not cite `fundingSignedValid_iff_vendor`
(`EcdsaBridgeTargets.lean:295`) as a non-vacuous consensus bridge.

### 3.4 `OPS-02` — the release conditional

There is no theorem here, and there should not be. The release is possible iff
a maintainer:

1. selects a license from the MIT/Apache-2.0/dual matrix in
   `docs/LICENSE-DECISION.md:62-76`;
2. confirms the copyright holder/authorized licensor — the tree's commit
   authorship is automation identities and there is no CLA/DCO/contributor
   policy (`docs/RELEASE-CHECKLIST.md:193-196`);
3. adds `LICENSE` (and `NOTICE` where required), including the `btc-lean` MIT,
   Bitcoin Core, `rust-lightning` dual-license, and CC-BY-4.0 BOLT notices
   (`docs/RELEASE-CHECKLIST.md:198-207`).

An agent must not invent the license or the copyright holder. This is a hard
blocker, not a proof obligation.

### 3.5 `OPS-03` — the tag/merge conditional

There is no theorem here either. The release is possible iff a maintainer
records all five choices in `docs/RELEASE-CHECKLIST.md:211-226`:

1. PR to `main` vs direct fast-forward;
2. merge commit vs fast-forward;
3. tag name/version scheme;
4. signed vs annotated tag;
5. tag on `main`'s merge commit vs on `repair/integrated`.

Then the pre-tag gate must be rerun at the exact commit whose object is tagged
(`docs/RELEASE-CHECKLIST.md:383` onward). At this HEAD no tag exists, and
`origin/main` is 102 commits behind the wave-11 code gate. A wave cannot close
this; only a maintainer can.

## 4. Non-vacuity / circularity audit of the seven wave-11 modules

The seven modules are the wave-11 additions listed in
`docs/FINAL-STATUS.md:121-135` and imported by
`LnLean/Proofs/PhaseC3/AxiomAudit.lean:103-109`. “Definitional” below means the
conclusion follows from a definition or a structure field, not that the theorem
is false. “Too strong” means the hypotheses already contain the hard part of
the conclusion, so the theorem cannot be read as establishing that hard part.

### 4.1 `NodeIdentityChainTargets`

**Genuine content.**

- `RotationChain.authenticated_comp` (`LnLean/Proofs/Routing/NodeIdentityChainTargets.lean:373`)
  and `authenticated_hop_links` (`:384`) compose verified hops.
- `acyclic_start_not_mem_tail` (`:345`) is a real list invariant.
- `NodeRateState.replay_rejected` (`:717`), `rateStep_replay_rejected` (`:805`),
  and `rateFold_replay_rejected` (`:849`) are substantive monotonicity/replay
  results.
- `nonvacuity_witness` (`:1092`) gives a signed certificate, an authenticated
  acyclic chain, and a rejected certificate.
- `distinct_hops_not_acyclic` (`:1120`), `hop_distinct_not_imply_acyclic`
  (`:1128`), `old_signature_does_not_authenticate_new_keys` (`:1144`),
  `signature_preservation_not_universal` (`:1157`), and
  `opaque_link_not_imply_signed` (`:1168`) are genuine negatives.

**Definitional / weak.**

- `RotationCertificate.signed_implies_link` (`:170`) has the form
  `c.Signed verify → RotationLink c.oldId c.newId` but **does not use the
  signature hypothesis** (`_h`). It constructs `c.toWitness` and proves
  `⟨c.toWitness, rfl, rfl⟩`. `RotationLink` is the wave-10 opaque witness
  relation; this theorem says “a certificate records two keys”, not “the old
  key authorised the new key”.
- `message_eq_rotationMessage` (`:187`) is exactly the structure field
  `c.message_eq`; it is a projection, not an encoding theorem.
- `toWitness_links` (`:165`) and `toWitness_mapKey_old` (`:192`) are `rfl`-level.

**Too strong / scope.**

- `Signed` is an unconstrained `SigVerifier` Bool; the module correctly keeps
  `opaque_link_not_authenticated` (`:1106`) to show a rejecting verifier admits
  opaque links but no signed certificate.
- The rate gate is a model-side sequence/timestamp policy, not a BOLT 7 wire
  validation theorem.
- `authenticated_comp` is conditional on `Signed` at every hop; it does not
  establish key ownership or that the verifier is a real signature scheme.

**Non-vacuity:** interface-level and real; the concrete keys/verifiers are
toy but explicitly labelled as such.

### 4.2 `NoiseTransportTargets`

**Genuine content.**

- `replay_rejected_with_freshness` (`LnLean/Proofs/Protocol/NoiseTransportTargets.lean:410`)
  and `replay_accepted_without_nonce_freshness` (`:884`) are a real
  freshness/replay pair.
- `accepted_frame_bound_to_peer` (`:460`) and `accepted_frame_peer_unique`
  (`:469`) are substantive **relative to** `NoiseHandshakeSound` and
  `AeadUnforgeable`.
- `accepted_frame_attributed_delivery` (`:632`) composes the binding with the
  routed funding witness.
- `noise_transport_nonvacuous` (`:1015`) and `concrete_accepted_frame_route`
  (`:1028`) give a concrete instance.
- `key_substitution_without_peer_binding` (`:870`), `looseCrypto_not_keyBinding`
  (`:877`), `acceptance_not_attribution` (`:905`),
  `noise_does_not_authenticate_payload` (`:919`), `noise_peer_not_from_wire`
  (`:933`), and `no_wire_session_binding_function` (`:951`) are genuine
  negatives.

**Definitional / weak.**

- `NoiseDelivery.toTransportSession` (`:574`) sets `established := true`
  unconditionally. Therefore `toAuthenticatedDelivery_authenticated` (`:594`)
  is `rfl`. `TransportAuthenticated` is a flag, not evidence a handshake
  occurred.
- `sessionKeyBinding_iff_peerStatic_eq` (`:599`) is `Iff.rfl`, because both
  sides reduce to `peerStatic = fundingPubKey`.
- `accepted_frame_yields_sessionKeyBinding` (`:619`) takes
  `_hS : NoiseHandshakeSound d.session` but **does not use it**; the conclusion
  follows from `hadv : peerStatic = fundingPubKey`. The `hS` parameter in
  `accepted_frame_attributed_delivery` is passed through but ultimately unused
  for attribution.
- `session_sendKey_peer` (`:229`) is `rfl` after unfolding `deriveKey`; the peer
  field is definitionally `h.peerStaticOf r`.

**Too strong / toy.**

- `strictCrypto` (`:512`) sets `produced := accept`, so
  `strictCrypto_unforgeable` (`:531`) and `strictCrypto_keyBinding` (`:540`)
  are true by construction. The comments say this explicitly; they are finite
  separation witnesses, not AEAD evidence.
- `AeadUnforgeable` and `AeadKeyBinding` are assumptions for general `C`; no
  C1/C3 derivation is claimed.

**Non-vacuity:** real at the interface, not cryptographic. The concrete demo
uses toy keys and a strict/loose MAC relation.

### 4.3 `CoverageSourceTargets`

**Genuine content.**

- `no_wire_determined_source` (`LnLean/Proofs/Channel/CoverageSourceTargets.lean:675`)
  and `no_wire_source_selector` (`:695`) are the strongest wire-only negatives
  at this interface.
- `wire_admits_distinct_out_of_band_witnesses` (`:714`),
  `wireCompatible_not_out_of_band_binding` (`:769`), and
  `no_wire_witness_authenticator` (`:784`) separate wire compatibility from
  provenance/authentication.
- `exampleExtension_nonvacuous` (`:842`), `mismatchedAmountExtension_not_binds`
  (`:876`), `mismatchedTagExtension_not_binds` (`:913`), and
  `emptyWire_rejects_extension` (`:940`) are concrete/rejection results.
- The field-necessity results (`:949`, `:970`, `:990`, `:1009`, `:1016`) are
  genuine.

**Definitional / weak.**

- `decodeSource_fullRecord_eq_decodeCoverage` (`:504`) and
  `decodeSource_outOfBand_eq_decodeCoverage` (`:527`) are `rfl`; the full
  record and out-of-band cases are the wave-10 witness decoder in disguise.
- `out_of_band_origin_irrelevant_to_decode` (`:759`) is `rfl`; the origin tag
  does not affect decoding.

**Too strong / conditional.**

- `ExtensionBinds` (`:324`) is a proof-carrying structure: same channel id plus
  `RowsBind` field-by-field agreement. `extension_plus_wire_determines_coverage`
  (`:585`) is therefore essentially “if the extension's rows already agree with
  the full record, decoding the extension returns the full record's coverage”.
  The hard part (deriving that agreement from the wire or signatures) is the
  hypothesis, not the conclusion. The module says this openly.
- `TrustedOrigin` (`:399`) is a policy tag (`localSigner`/`persistedTranscript`
  true, `untrustedPeer` false), not authentication.
- `ProtocolExtension` is a specification, not a BOLT 2 message/TLV; no wire
  encoding is claimed.

**Non-vacuity:** `exampleExtension_nonvacuous` is real, but it is a model
extension, not a production decoder.

### 4.4 `ChainFinalityTargets`

**Genuine content.**

- `bounded_depth_finality` (`LnLean/Proofs/Security/ChainFinalityTargets.lean:256`)
  is real prefix arithmetic: common ancestor + depth bound + confirmation at
  depth gives block equality.
- `confirmed_tx_not_reorged` (`:331`) and `unique_tip_finality` (`:362`) are
  correct wrappers.
- `depth_bound_necessary` (`:772`) and `deep_reorg_evicts` (`:748`) are a sharp
  counterexample; `smallTx_not_reorged` (`:597`) is a non-reflexive positive
  witness.

**Definitional / weak.**

- `Chain.WellFormed` (`:133`) is defined and proved for the small/deep chains,
  but `bounded_depth_finality` **does not require it**. The finality theorem is
  pure list-prefix arithmetic; well-formedness is not connected to the finality
  hypotheses.
- `sameChain_view_of_length_eq` (`:391`) proves `SameChain` from equal length
  and the same tip tag. `SameChain` only reads `height` and `tip`, so this
  bridge is much weaker than “same chain”; it is a view-level bridge, not a
  graph identity.
- `net01_eventual_delivery_instance` (`:874`) is static `List.Mem`/capability,
  not temporal liveness; `funding_created_eventually_delivered` (`:819`) is
  `List.Mem`. The module's own comments say this; the lane report says NET-01
  must remain open.

**Too strong / scope.**

- `UniqueCanonicalTip` (`:342`) includes “no longer member” and “equal-length
  members are the same chain”; `unique_tip_finality` uses it only for the
  length bound. That is fine, but it is a family hypothesis, not a consensus
  theorem.
- No PoW, chainwork, probability, transaction validity, timestamps, or live
  chain. The header says so.

**Non-vacuity:** the small and deep chains are concrete and well-formed; the
result is a finite-graph result, not a chain-consensus result.

### 4.5 `InvoiceWireTargets`

**Genuine content.**

- Scalar/field codecs: `decodeNat_encodeNat` (`LnLean/Proofs/Payment/InvoiceWireTargets.lean:164`),
  `decodeHop_encodeHop` (`:377`), `parseFields_printFields` (`:557`),
  `parse_print` (`:660`), and `print_injective` (`:679`) are real round-trip /
  injectivity results.
- `toInvoice_valid` (`:762`) and `ofInvoice_canonical` (`:780`) are real
  structural projections under their bounds.
- `constantZeroHash_collision` (`:1053`), `commitment_not_valid_preimage`
  (`:1071`), and `signature_not_payment` (`:1129`) are genuine algebraic
  counterexamples/separation results.

**Definitional / weak.**

- `invoiceCommits_iff` (`:971`) is `Iff.rfl`.
- `toInvoice_ofInvoice` (`:749`) is `cases i; rfl`.
- `paymentSecret_eq_iff_bytes` (`:999`) and `paymentHash_eq_iff_bytes` (`:1006`)
  are wrapper `cases` proofs; they are true but not deep.

**Too strong / scope.**

- `WireInvoice.Canonical` (`:608`) is length/bound conditions (32/32/33/65
  bytes, amount bound, timestamp bound, 64-bit expiry/CLTV, valid hops), not
  full BOLT 11 canonicality. There is no bech32/checksum/signable-digest
  construction.
- `ofInvoice_canonical` (`:780`) needs extra `expiry < 2^64` and
  `minFinalCltvExpiry < 2^64` hypotheses not present in `Invoice.Valid`.
- `toInvoice_valid` does **not** check a signature; `signature_not_payment`
  uses an always-accepting checker (`:1108`). This is honest but easy to
  overread.
- Payment-hash binding is the algebraic `hash p = paymentHash` relation only;
  `preimage_unique_of_injective` (`:986`) is conditional on `Function.Injective
  hash`, and no concrete SHA-256 or computational claim is made.

**Non-vacuity:** `witnessWire_canonical` (`:853`), `witness_parse` (`:869`),
and `witness_toInvoice_valid` (`:873`) are real; the codec is pre-bech32 by
design.

### 4.6 `HtlcAggregateTargets`

**Genuine content.**

- `aliasing_double_spend_witness` (`LnLean/Proofs/Channel/HtlcAggregateTargets.lean:547`),
  `no_spend_selector_on_aliased_aggregate` (`:559`), and
  `record_distinctness_not_spend_separation` (`:571`) are a real aliasing
  counterexample and separation.
- `duplicateAggregate_not_noDuplication` (`:812`) shows the no-duplication
  premise is load-bearing.
- `boundaryTx_not_funded` (`:850`) and `rejectedAggregate` (`:867`) reject a
  concrete underfunded aggregate; `fundedTx_ok` (`:879`) shows the rejection is
  not universal.
- `no_legacy_only_aggregate_coverage_decoder` (`:954`) and
  `legacy_wire_does_not_carry_aggregate_coverage` (`:970`) preserve the
  legacy-wire negative.

**Definitional / weak.**

- `coverage_eq_map` (`:306`), `perHtlcCoverage_eq_map` (`:309`), and
  `aggregateCoverage_eq_perHtlcCoverage` (`:315`) are `rfl`. `coverage` and
  `perHtlcCoverage` are the same map; the “aggregate = per-HTLC” list identity
  is definitional.
- `coverageValue_eq_sum` (`:328`) is a real list induction, but it is arithmetic
  over the same map.
- `funded_iff` (`:678`) is `Iff.rfl`; `requiredFee_val` (`:650`) is `rfl`.

**Too strong / not discharged.**

- `aggregate_coverage_projection` (`:370`) takes
  `_hcommit : a.DistinctCommitments` but **does not use it** for the list
  identity; the comment acknowledges this. The substantive separation use is in
  `distinct_commitments_separate` (`:388`).
- `NoDuplication` (`:288`) and `NoSpendAliasing` (`:298`) are explicit
  hypotheses over an arbitrary record list; the module does not derive them
  from a commitment/script construction.
- `aggregateOfFull` (`:918`) uses a constant empty script identity because the
  legacy record carries no script bytes. That is honest, but it means the
  aggregate coverage is not a real script projection.
- Fee/weight constants are parameters, not a consensus weight estimator.

**Non-vacuity:** `witnessAggregate_nonvacuous` (`:761`) and `fundedTx_ok`
(`:879`) are real; `aliasAggregate` is a genuine counterexample.

### 4.7 `NonVacuityTargets`

**Genuine content.**

- `withVendorEcdsa_accepts_nothing` (`LnLean/Proofs/Model/NonVacuityTargets.lean:535`),
  `withVendorEcdsa_funding_uninhabited` (`:524`), and
  `bridgedFundingWitness_uninhabited` (`:512`) are the substantive vacuity
  results; they are the model-level counterpart of §3.1.
- `digestBindsMod_uninhabited` (`:493`), `nBytes33_not_canonical` (`:498`), and
  `oneSigWire_no_empty_decode` (`:470`) are genuine negatives.
- `vacuous_nonvacuous_separation` (`:569`) and `witness_not_universal` (`:585`)
  correctly separate “a carrier type is inhabited” from “the relevant relation
  is inhabited”.

**Definitional / weak.**

- `witnessRegistry_sound` (`:807`) is literally `fun e _ => e.proof`. Each
  `AuditedWitness` stores its own `proof` field (`:640-645`), so soundness is
  by construction. This is a sound dependent list, not an independent audit
  that each catalog theorem is non-vacuous.
- `witnessRegistry_length` (`:803`) and `witnessRegistryIds_length` (`:816`) are
  `rfl`; `witnessRegistryIds_nodup` (`:819`) is `decide`.
- The registry covers **30 audited interface items**, not the 51 catalog rows;
  the module says so explicitly.

**Too strong / toy.**

- `auditEcdsa_eufCma` (`:123`) is a verifier that accepts only the empty
  message; `auditHash` (`:98`) is the identity on 32-byte inputs and zero
  elsewhere. `auditModel` (`:144`) is a toy `PrimitiveModel`.
  `auditModel_accepts_empty` (`:168`) and `eufCma_nonvacuous_witness` (`:451`)
  are real at the interface, not cryptographic.
- `protocol_nonvacuous` in `PopProtocolTargets` (`:834`) uses `selfSigModel`
  (`LnLean/Proofs/WaveH/H22.lean:710`), where the signature bytes are the
  message. It proves the PoP contract is inhabited in a toy model, not that a
  real signature scheme has `PopExtractionOn`.

**Non-vacuity:** honest and explicitly scoped; the registry's soundness is not
an independent check of the catalog.

### 4.8 Cross-cutting circularity assessment

No theorem was found that assumes its own conclusion in the strict logical
sense. The recurring weakness is **conclusion-shaped hypotheses**, not
circularity:

| Theorem | Why it is weaker than its name |
|---|---|
| `TransportAuthTargets.transport_authenticated_attributed` (`:211`) | `_hauth` is unused; attribution follows from `SessionKeyBinding`, which is definitionally the same equality as `EnvelopeAttributed`. |
| `NoiseTransportTargets.accepted_frame_yields_sessionKeyBinding` (`:619`) | `_hS` is unused; `SessionKeyBinding` follows from `hadv : peerStatic = fundingPubKey`. |
| `NodeIdentityChainTargets.signed_implies_link` (`:170`) | Signature hypothesis unused; `RotationLink` is the opaque witness relation. |
| `CoverageSourceTargets.extension_plus_wire_determines_coverage` (`:585`) | `ExtensionBinds` already contains the field agreement that determines coverage. |
| `NodeCanonicalTargets.epoch_square_lifts_to_node_canonical_view` (`:1278`) | Assumes `Nodup` and `CanonicalNodeAnnouncements` of the raw fold, i.e. the invariant node selection is meant to establish. |
| `HtlcAggregateTargets.aggregateCoverage_eq_perHtlcCoverage` (`:315`) | `rfl`; the two definitions are the same map. |
| `NonVacuityTargets.witnessRegistry_sound` (`:807`) | Each entry stores its proof; soundness is projection. |

## 5. Counterexamples and separation results preserved

I checked that the wave-11 modules did not remove or weaken the earlier
negatives. The following are present at HEAD and were read in place.

### 5.1 `L1-01` / `L1-07` EC and digest negatives

| Result | `file:line` | Content |
|---|---|---|
| `eufCma_vendorVerify_iff_totalReject` | `LnLean/Proofs/Bitcoin/EcdsaConcreteTargets.lean:163` | byte-level C3 ⇔ total rejection |
| `not_eufCma_vendorVerify_iff_accepts` | same file, after `:170` | ¬C3 ⇔ some acceptance |
| `no_bridged_nontrivial_model` | `:252` | no bridged model accepts anything |
| `exists_bridged_model_iff_totalReject` | `:265` | exact existence criterion |
| `withVendorEcdsa_no_funding` | `:303` | the wave-8 concrete model has no funding witness |
| `fundingTag_digest_collision_witness` | `:622` | concrete collision for the funding tag |
| `not_digestBindsMod_fundingTag` | `:616` | funding tag does not bind |
| `not_digestBindsMod_any_tag` | `LnLean/Proofs/Bitcoin/EcdsaDomainTargets.lean:281` | no fixed tag binds |
| `no_digestBindsMod_anywhere` | `:288` | no tag at all |
| `not_digestBindsModOn33_any_tag` | `:301` | fixed 33-byte length alone does not bind |
| `digest_collision_witness_any_tag` | `:294` | per-tag collision pair |
| `digest_domain_dichotomy` | `:478` | negative + canonical-33 positive + fixed-33 negative |
| `not_canonical33_nBytes33` | `:377` | the bad suffix is exactly excluded |

### 5.2 `L1-03` transport/session negatives

| Result | `file:line` | Content |
|---|---|---|
| `not_universal_sessionKeyBinding` | `LnLean/Proofs/Protocol/TransportAuthTargets.lean:440` | the binding law is not universal |
| `unattributed_delivery_exists` | `:449` | a transport-flagged delivery can fail attribution |
| `transport_auth_not_from_wire` | `:475` | wire alone does not authenticate |
| `no_wire_sender_function` | `:516` | no payload-only sender function |
| `no_wire_attribution_function` | `:537` | no payload-only attribution predicate |
| `authenticated_not_bound` | `:427` | authenticated ≠ bound |
| `key_substitution_without_peer_binding` | `LnLean/Proofs/Protocol/NoiseTransportTargets.lean:870` | peer substitution |
| `looseCrypto_not_keyBinding` | `:877` | loose crypto fails key binding |
| `replay_accepted_without_nonce_freshness` | `:884` | replay without freshness |
| `acceptance_not_attribution` | `:905` | acceptance ≠ attribution |
| `noise_does_not_authenticate_payload` | `:919` | same payload, two sessions, different attribution |
| `noise_peer_not_from_wire` | `:933` | no wire→peer function |
| `no_wire_session_binding_function` | `:951` | no wire→binding predicate |

### 5.3 `PR-01` PoP negatives

| Result | `file:line` | Content |
|---|---|---|
| `keySound_not_provenance` | `LnLean/Proofs/Crypto/PopProtocolTargets.lean:589` | key soundness does not give honest provenance |
| `keySound_not_keyBinding` | `:625` | key soundness does not give key binding |
| `keyBinding_completeness_not_keySound` | `:636` | completeness is not soundness |
| `unbound_replay_accepts` | `:668` | replay without challenge binding |
| `nonceFree_replay_accepts` | `:696` | replay without nonces |
| `challengeMessage_not_injective_without_valid` | `:725` | encoding injectivity needs `Valid` |
| `binding_fails_without_valid` | `:758` | binding fails without `Valid` |
| `repeated_challenge_replay` | `:788` | repeated-challenge replay |

### 5.4 `PR-02` coverage negatives

| Result | `file:line` | Content |
|---|---|---|
| `no_legacy_only_coverage_decoder` | `LnLean/Proofs/Channel/CoverageWitnessTargets.lean:223` | no wire-only decoder |
| `no_legacy_only_witness_selector` | `:239` | no wire-only witness selector |
| `amount_is_necessary` | `:276` | amount row is necessary |
| `wire_admits_distinct_coverage_witnesses` | `:345` | same wire, different witnesses |
| `wire_cannot_select_witness` | `:364` | wire cannot select |
| `no_wire_determined_source` | `LnLean/Proofs/Channel/CoverageSourceTargets.lean:675` | no wire-determined source |
| `no_wire_source_selector` | `:695` | no wire source selector |
| `wire_admits_distinct_out_of_band_witnesses` | `:714` | two trusted out-of-band witnesses differ |
| `wireCompatible_not_out_of_band_binding` | `:769` | compatibility ≠ binding |
| `no_wire_witness_authenticator` | `:784` | no wire-only authenticator |
| `mismatchedAmountExtension_not_binds` | `:876` | amount mismatch rejects |
| `mismatchedTagExtension_not_binds` | `:913` | tag mismatch rejects |
| `emptyWire_rejects_extension` | `:940` | empty wire rejects extension |

### 5.5 `RT-02` node/rotation negatives

| Result | `file:line` | Content |
|---|---|---|
| `reachableNodeCanonical_rotation_keeps_both` | `LnLean/Proofs/Routing/NodeCanonicalTargets.lean:1060` | rotation keeps two slots |
| `reachableNodeCanonical_equal_timestamp_tie_boundary` | `:1114` | equal timestamp is unrecoverable |
| `no_canonical_node_preserving_raw_node_extension` | `:1159` | raw extension cannot preserve canonicality |
| `canonicalStoreView_does_not_canonicalise_nodes` | `:1189` | canonical store view does not select nodes |
| `reachableNodeCanonical_node_slot_ignores_global_clock` | `:1206` | per-slot clock ≠ global clock |
| `raw_nonrefinement_preserved` | `:1225` | raw insertion is not a refinement |
| `opaque_link_not_authenticated` | `LnLean/Proofs/Routing/NodeIdentityChainTargets.lean:1106` | opaque witness is weaker than a signed cert |
| `distinct_hops_not_acyclic` | `:1120` | hop distinctness does not give acyclicity |
| `hop_distinct_not_imply_acyclic` | `:1128` | exact obstruction |
| `old_signature_does_not_authenticate_new_keys` | `:1144` | stale signature failure |
| `signature_preservation_not_universal` | `:1157` | signatures are not rewrite-invariant |
| `opaque_link_not_imply_signed` | `:1168` | opaque evidence cannot manufacture a signed cert |

### 5.6 `L1-06`/`NET-01` finality and static-delivery boundaries

| Result | `file:line` | Content |
|---|---|---|
| `deep_reorg_evicts` | `LnLean/Proofs/Security/ChainFinalityTargets.lean:748` | depth-two tx evicted by depth-three fork |
| `depth_bound_necessary` | `:772` | the bound is necessary |
| `smallTipTx_rejected` | `:624` | tip tx rejected at depth two |
| `smallTx_rejected_without_prefix` | `:638` | no common prefix, no retention |
| `deep_bound_violated` | `:731` | the concrete fork violates the bound |
| `funding_created_eventually_delivered` | `:819` | `List.Mem`, not temporal liveness |
| `dropped_route_not_delivered` | `:826` | dropped trace does not carry the message |
| `net01_eventual_delivery_instance` | `:874` | static capability, not fairness/liveness |

### 5.7 Invoice and aggregate negatives

| Result | `file:line` | Content |
|---|---|---|
| `constantZeroHash_collision` | `LnLean/Proofs/Payment/InvoiceWireTargets.lean:1053` | two preimages, one image |
| `commitment_not_valid_preimage` | `:1071` | commitment does not imply valid 32-byte preimage |
| `signature_not_payment` | `:1129` | verified invoice with no committing preimage |
| `signature_only_separates_verify_from_payment` | `:1141` | separation, no crypto claim |
| `malformed_parse_none` | `:898` | 31-byte hash rejected |
| `duplicateHash_parse_none` | `:922` | duplicate `p` rejected |
| `aliasing_double_spend_witness` | `LnLean/Proofs/Channel/HtlcAggregateTargets.lean:547` | one spend covers two distinct rows |
| `no_spend_selector_on_aliased_aggregate` | `:559` | no target→record selector |
| `record_distinctness_not_spend_separation` | `:571` | record identity ≠ target injectivity |
| `duplicateAggregate_not_noDuplication` | `:812` | duplication breaks the premise |
| `boundaryTx_not_funded` | `:850` | concrete underfunded aggregate |
| `no_legacy_only_aggregate_coverage_decoder` | `:954` | aggregate restatement of the legacy-wire negative |

### 5.8 Non-vacuity negatives

| Result | `file:line` | Content |
|---|---|---|
| `withVendorEcdsa_accepts_nothing` | `LnLean/Proofs/Model/NonVacuityTargets.lean:535` | vendored model accepts nothing |
| `withVendorEcdsa_funding_uninhabited` | `:524` | funding relation empty |
| `bridgedFundingWitness_uninhabited` | `:512` | bridged funding witness impossible |
| `digestBindsMod_uninhabited` | `:493` | no tag anywhere |
| `nBytes33_not_canonical` | `:498` | exact bad suffix excluded |
| `oneSigWire_no_empty_decode` | `:470` | one signature cannot decode to empty |
| `vacuous_nonvacuous_separation` | `:569` | same C3 field, one model empty |
| `witness_not_universal` | `:585` | carrier inhabitance ≠ predicate inhabitance |

## 6. Wave-13 recommendation

### 6.1 Do not schedule closure lanes for the P0s

- `L1-01` and `L1-07` cannot be closed at the current interface:
  `no_bridged_nontrivial_model` is a kernel-checked impossibility. A wave that
  tries to prove a non-vacuous `VendorEcdsaBridge` will either fail or produce
  another total-rejecting model. The only legitimate work is a **model change**
  (typed digest/canonical encoding) or an explicit computational assumption.
- `L1-02` has no transfer gap; the remaining work is a concrete secp256k1
  refinement or an assumption. Do not spend a wave re-proving the transfer.
- `OPS-02`/`OPS-03` are maintainer decisions. No agent lane.

### 6.2 The one clearly tractable P1 slice: `RT-02` address parsing

`NodeAnnouncement.addresses` is `List ByteArray` and address parsing is
explicitly unmodelled (`LnLean/Routing/Gossip.lean:61`, `:200-205`). A
wave-13 lane can add, without changing the core wire type:

1. a typed `NetAddr` model for BOLT 7 `netaddr`:
   IPv4, IPv6, Tor v2, Tor v3, and hostname (with length limits);
2. a parser/printer with round-trip on valid addresses and rejection of
   malformed/oversized prefixes;
3. a view from `List ByteArray` to `List NetAddr` that is used only by the
   canonicalization layer, not by the legacy `NodeAnnouncement` record;
4. concrete non-vacuity (at least one address of each supported type) and
   negative cases (wrong length, bad prefix, truncated payload);
5. preservation of the existing node/rotation negatives in §5.5.

**Acceptance criteria:** no `sorry`; round-trip for valid addresses; rejection
for malformed; no change to the BOLT 7 wire theorem claims; existing negatives
still compile. This narrows `RT-02` but **does not close it**: chain-existence
policy and a production gossip/rotation pipeline remain explicit external
requirements, and `RotationLink` remains opaque.

### 6.3 Optional high-risk model change: typed digest for `L1-01`/`L1-07`

If the maintainer wants a non-vacuous EC story, the wave should:

1. define a typed 32-byte digest interface (or a checked canonical 33-byte
   payload) distinct from the current `fundingTag ++ tx` byte string;
2. make `verifyFunding` consume that digest, with an explicit check that
   `bytesToNatBE digest < n` (or a rejection/retry rule);
3. state the contract as `ResidueBinding ∧ KeyBinding`, not `EufCma` at the
   byte level;
4. prove the canonical-domain extraction (`digestBindsModOn_canonical32`) and
   keep `not_digestBindsMod_any_tag` as the reason the untyped interface cannot
   work;
5. label the concrete secp256k1 implementation as an external assumption unless
   it is actually provided.

This is a **model change**, not a proof of the existing claim. It needs
maintainer sign-off because it changes the meaning of the funding signature
interface and the catalog scope note.

### 6.4 Not recommended as proof lanes

- `L1-03`: a real Noise_XK/AEAD implementation is external. A wave can add more
  finite models, but that repeats the current definitional/flag boundary.
- `PR-01`: `PopKeySoundOn`/`PopExtractionOn` require a real EUF-CMA signature
  scheme with key ownership; the current `selfSigModel` non-vacuity is a toy.
- `PR-02`: a production decoder is impossible from the legacy wire; a protocol
  extension is a spec/design change. A TLV codec lane would be legitimate only
  if the maintainer chooses that protocol change, and it must be labelled as a
  model/spec extension, not BOLT 2.
- `OPS-02`/`OPS-03`: maintainer tasks.

### 6.5 Gate discipline for any wave-13 work

- Use the current code gate `6a48d41` as the base, or record a new gate commit.
- Do not tag or merge until `OPS-02`/`OPS-03` decisions are recorded.
- Re-run the full gate at the exact tag object; the checklist's stale “100
  commits” line should be corrected to the actual count at that time.
- Keep the catalog scope notes explicit: `Canonical33` is a 33-byte domain and
  does not apply to real funding transaction byte strings; `VendorEcdsaBridge`
  is total-rejecting under `PrimitiveModel.ecdsa_eufCma`; `TransportAuthenticated`
  is a flag; `TrustedOrigin` is a policy tag; `witnessRegistry_sound` is a
  dependent-list projection.

## 7. Residual audit risks and open questions

1. **No build/axiom rerun.** This audit is source-level. The docs claim `312`
   jobs and `407` audited theorems; I did not reproduce them. A release audit
   should rerun the gate at the tag commit.
2. **Line drift.** All `file:line` citations are at HEAD `5ddab4c`. Status
   commits after the code gate may shift lines; theorem names are the stable
   identifiers.
3. **Catalog overstatement.** `LN-L1-001`'s claim includes “the 33-byte suffix
   instance and the 32-byte digest instance yielding conditional funding
   extraction.” The 33-byte instance is real but does not apply to real funding
   transaction bytes; the 32-byte instance applies to a digest-sized message,
   not the current `fundingTag ++ tx` interface. The catalog should either
   narrow the wording or add the typed-digest model change in §6.3.
4. **Non-vacuity registry scope.** `witnessRegistry_sound` is sound by
   construction and covers 30 interface items, not the 51 catalog rows. Do not
   cite it as a catalog-wide non-vacuity proof.
5. **`NET-01`.** `net01_eventual_delivery_instance` is static; do not cite it
   as protocol liveness. The lane report itself says NET-01 remains open.
6. **`L1-06`.** The finite-graph finality result is genuine, but it is not a
   PoW/probabilistic/live-chain result. The remaining obligation is
   `LN-CHAIN-REORG`; do not close it on the strength of the finite model.
7. **Release checklist drift.** The line `origin/main` “100 commits behind”
   (`docs/RELEASE-CHECKLIST.md:214`) is stale; the actual count is 102 at this
   HEAD. The tag/merge blocker is unaffected, but the checklist should be
   corrected before release.

## 8. Post-freeze working-tree addendum

This report is a snapshot of HEAD `5ddab4c`. Other S12 lanes were still writing
uncommitted files while the report was being finalized. At
`2026-10-19T17:17Z` the worktree contained at least the following artifacts that
are **not** part of the audited HEAD and are excluded from every verdict above:

- `LnLean/Proofs/Channel/CoverageConsumerTargets.lean` — an untracked,
  model-level consumer contract for `LN-PR-004`. It composes with
  `CoverageSource` and adds no production decoder or wire encoding. It does not
  change the `PR-02` verdict in §2: production coverage still requires an
  out-of-band/full-record source with an explicit binding law, or a protocol
  change.
- `LnLean/Proofs/Routing/NodeAddressTargets.lean` — an untracked, in-progress
  BOLT 7 address parser intended as the `RT-02` slice recommended in §6.2. At
  the snapshot it was not imported by `LnLean.lean`, and
  `decodeAddresses_not_sorted` still contained `sorry` (around `:912-913`), so
  the module's own header claim of “no `sorry`” was false at that moment. It
  cannot satisfy the §6.2 acceptance criteria until it is imported and rebuilt
  without `sorry`.
- Tracked worktree edits to `LnLean.lean`, `Obligations.lean`,
  `AxiomAudit.lean`, and the conformance fixtures/scripts. The local
  `AxiomAudit.lean` registry had grown to 415 entries at the snapshot; that is
  concurrent work, not the `407` audited at HEAD.

These artifacts may change or disappear before any commit. They are recorded
only to prevent a reader from mistaking in-flight files for audited evidence.
The audit conclusions and the wave-13 recommendation remain those of
§§2–7.
