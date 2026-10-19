# S10-L1-TRANSPORT-AUTH — transport authentication above `OpenChannelEnvelope`

**Lane:** `S10-L1-TRANSPORT-AUTH`
**Issue:** `L1-03`
**Recommended catalog row:** `LN-PR-001` (primary type-32 `open_channel` row)
**Branch:** `repair/integrated`
**Launch HEAD:** `7988c93` (base `9158592`)
**Status:** complete; scoped build, public-theorem axiom audit, and
forbidden-token scan clean
**Owned files created:** `LnLean/Proofs/Protocol/TransportAuthTargets.lean`,
`agents/reports/swarm10/S10-L1-TRANSPORT-AUTH.md`
**Files edited outside the owned set:** none. No commit, push, root import,
catalog, traceability, audit, or docs edit. Other lanes' working-tree changes
are present and untouched.

---

## 1. Objective

Wave 9 modelled the transport-delivered type-32 message as
`OpenChannelEnvelope` and defined `EnvelopeAttributed` as equality of the
transport key with the wire's advertised `funding_pubkey`. It then proved that
the routed protocol state and the funding construction ignore the sender. It
deliberately did **not** model what a transport authenticates, nor derive
attribution from any transport law.

This lane adds that layer additively above `OpenChannelEnvelope`:

1. model a transport session/authentication relation and an explicit
   session/key-binding law;
2. prove that transport authentication plus the binding law attributes a
   delivered `open_channel`, and compose that with the existing routed
   `open_channel` → `accept_channel` → `funding_created` witness;
3. retain the sharp negative that the wire payload alone does not authenticate
   a sender, including same-wire/different-session and missing-binding
   counterexamples;
4. exhibit a concrete non-vacuous session/delivery and state exactly what is
   still assumed (transport binding, C3/key ownership).

## 2. Answer in one paragraph

The transport layer is modelled as a `TransportSession` carrying an opaque
session id, a peer key, and an `established` flag. A delivery pairs that session
with the unchanged `OpenChannelWire`; its `envelope` attaches the session key as
`PeerIdentity`, so it is exactly a wave-9 `OpenChannelEnvelope`. The transport
supplies only `TransportAuthenticated d := d.session.established = true`. The
explicit law `SessionKeyBinding d := d.session.peerKey = d.wire.fundingPubKey`
is **not** supplied by the transport model and **not** derivable from the wire;
it is the key-binding assumption. Under both hypotheses the delivery is
`EnvelopeAttributed`, and it composes with the routed witness to reach
`funding_created`, a reachable `FundingPhase`, and the constructed P2WSH output.
The negative side is mechanized: for a fixed wire, two established sessions can
carry different keys, one satisfying the binding law and one not, so only one is
attributed. There is no function from the wire to the session key or to an
attribution verdict that is correct for every authenticated delivery. No Noise
implementation, signature check, or key-ownership theorem is claimed.

## 3. Exact model

Namespace:

```lean
LnLean.Proofs.Protocol.TransportAuthTargets
```

Definitions and structures:

```lean
structure TransportSession where
  sessionId : Nat
  peerKey : PubKey
  established : Bool

structure AuthenticatedDelivery where
  session : TransportSession
  wire : OpenChannelWire

namespace AuthenticatedDelivery
def envelope (d : AuthenticatedDelivery) : OpenChannelEnvelope where
  sender := ⟨d.session.peerKey⟩
  wire := d.wire
end AuthenticatedDelivery

def TransportAuthenticated (d : AuthenticatedDelivery) : Prop :=
  d.session.established = true

def SessionKeyBinding (d : AuthenticatedDelivery) : Prop :=
  d.session.peerKey = d.wire.fundingPubKey

structure SessionKeyBindingLaw where
  bound : ∀ d : AuthenticatedDelivery,
    TransportAuthenticated d → SessionKeyBinding d

structure AuthenticatedBinding (d : AuthenticatedDelivery) : Prop where
  authenticated : TransportAuthenticated d
  keyBound : SessionKeyBinding d
```

`TransportAuthenticated` is a session property; it cannot be changed by
replacing the payload (`transportAuthenticated_with_wire`). This is the whole of
what the model says the transport supplies. `SessionKeyBinding` is the explicit
trust boundary. `AuthenticatedBinding` bundles the two hypotheses for
composition.

## 4. Positive results

```lean
theorem envelopeAttributed_iff_sessionKeyBinding (d : AuthenticatedDelivery) :
    EnvelopeAttributed d.envelope ↔ SessionKeyBinding d

theorem envelopeAttributed_of_sessionKeyBinding (d : AuthenticatedDelivery)
    (hbind : SessionKeyBinding d) :
    EnvelopeAttributed d.envelope

theorem not_envelopeAttributed_of_not_sessionKeyBinding
    (d : AuthenticatedDelivery) (h : ¬ SessionKeyBinding d) :
    ¬ EnvelopeAttributed d.envelope

theorem transport_authenticated_attributed (d : AuthenticatedDelivery)
    (_hauth : TransportAuthenticated d) (hbind : SessionKeyBinding d) :
    EnvelopeAttributed d.envelope

theorem sessionKeyBindingLaw_attributed (law : SessionKeyBindingLaw)
    (d : AuthenticatedDelivery) (hauth : TransportAuthenticated d) :
    EnvelopeAttributed d.envelope

theorem authenticatedBinding_attributed {d : AuthenticatedDelivery}
    (h : AuthenticatedBinding d) : EnvelopeAttributed d.envelope
```

`attributed_envelope_wire` records that attribution does not replace or mutate
the wire. `authenticated_key_in_funding_script` composes the positive theorem
with the wave-9 key-in-script result, so the authenticated session key is the
local funding key and occurs literally in the constructed witness script.

Route composition:

```lean
theorem authenticated_delivery_reaches_fundingCreated
    (d : AuthenticatedDelivery) (a : AcceptChannel)
    (hauth : TransportAuthenticated d) (hbind : SessionKeyBinding d) :
    EnvelopeAttributed d.envelope ∧
      OpenRouteReachable (afterOpenRoute d.envelope) ∧
      ∃ s1 s2 : HandshakeState,
        handshakeStepRecvAccept (afterOpenRoute d.envelope).peer.handshake a =
            some s1 ∧
          handshakeStep s1 .sendFundingCreated = some s2 ∧
          s1.acceptChannel? = some a ∧
          s2.acceptReceived = true

theorem authenticated_open_reaches_funding
    (d : AuthenticatedDelivery) (a : AcceptChannel)
    (H : ByteArray → ByteArray)
    (hauth : TransportAuthenticated d) (hbind : SessionKeyBinding d) :
    EnvelopeAttributed d.envelope ∧
      OpenRouteReachable (afterOpenRoute d.envelope) ∧
      FundingReachable (acceptorPhaseAfter d.wire a) ∧
      FundingScriptHashLinked H (d.wire.toFundingParams H a) ∧
      (d.wire.toFundingParams H a).fundingScriptPubKey =
        p2wsh (H (TwoOfTwoScriptBytes
          (d.wire.toFundingNegotiation a).firstFundingKey
          (d.wire.toFundingNegotiation a).secondFundingKey))
```

These are the requested positive theorem and its composition with the wave-9
route. The authenticated route uses the unchanged `handshakeStepRecvAccept` and
`handshakeStep .sendFundingCreated`; no core file is patched.

## 5. Negative results

```lean
theorem wire_payload_does_not_determine_session_key :
    ∃ d₁ d₂ : AuthenticatedDelivery,
      d₁.wire = d₂.wire ∧
        TransportAuthenticated d₁ ∧ TransportAuthenticated d₂ ∧
        d₁.session.peerKey ≠ d₂.session.peerKey

theorem transport_auth_not_from_wire :
    ∃ d₁ d₂ : AuthenticatedDelivery,
      d₁.wire = d₂.wire ∧
        TransportAuthenticated d₁ ∧ TransportAuthenticated d₂ ∧
        EnvelopeAttributed d₁.envelope ∧
        ¬ EnvelopeAttributed d₂.envelope

theorem unattributed_delivery_exists :
    ∃ d : AuthenticatedDelivery,
      TransportAuthenticated d ∧ ¬ EnvelopeAttributed d.envelope

theorem authenticated_not_bound :
    ∃ d : AuthenticatedDelivery,
      TransportAuthenticated d ∧ ¬ SessionKeyBinding d

theorem not_universal_sessionKeyBinding :
    ¬ ∀ d : AuthenticatedDelivery,
        TransportAuthenticated d → SessionKeyBinding d

theorem no_session_binding_counterexample :
    ∃ d₁ d₂ : AuthenticatedDelivery,
      d₁.wire = d₂.wire ∧
        TransportAuthenticated d₁ ∧ TransportAuthenticated d₂ ∧
        SessionKeyBinding d₁ ∧ ¬ SessionKeyBinding d₂ ∧
        EnvelopeAttributed d₁.envelope ∧
        ¬ EnvelopeAttributed d₂.envelope

theorem no_wire_sender_function :
    ¬ ∃ f : OpenChannelWire → PubKey,
        ∀ d : AuthenticatedDelivery,
          TransportAuthenticated d → f d.wire = d.session.peerKey

theorem no_wire_attribution_function :
    ¬ ∃ f : OpenChannelWire → Prop,
        ∀ d : AuthenticatedDelivery,
          TransportAuthenticated d →
            (f d.wire ↔ EnvelopeAttributed d.envelope)
```

These are the sharp non-authentication results. `transport_auth_not_from_wire`
uses the *same* wire record in two established sessions; only the delivery whose
session key equals the advertised funding key is attributed.
`no_session_binding_counterexample` shows the binding law is the separating
hypothesis, not a consequence of authentication or well-formedness.
`no_wire_sender_function` and `no_wire_attribution_function` rule out reading
the sender or attribution back from the payload by any function.

Signature/PoP boundary:

```lean
theorem authenticated_delivery_no_signature (d : AuthenticatedDelivery) :
    signatures (.openChannel d.wire) = []

theorem advertised_key_independent_of_session_key (d : AuthenticatedDelivery)
    {k : PubKey} (hk : k.Valid) :
    ∃ d' : AuthenticatedDelivery,
      d'.session = d.session ∧
        d'.wire.fundingPubKey = k ∧
        wellFormed (.openChannel d'.wire)
```

The opening contributes no signature to the message signature list, and any
valid key can be advertised independently of the session key. Neither transport
authentication nor wire well-formedness is proof of possession.

## 6. Non-vacuity

```lean
def demoSession (b : UInt8) (established : Bool) : TransportSession
def demoDelivery (sessionByte wireByte : UInt8) (established : Bool) :
    AuthenticatedDelivery
def demoAttributedDelivery : AuthenticatedDelivery
def demoUnattributedDelivery : AuthenticatedDelivery

theorem demoAttributedDelivery_authenticated :
    TransportAuthenticated demoAttributedDelivery
theorem demoAttributedDelivery_bound :
    SessionKeyBinding demoAttributedDelivery
theorem demoAttributedDelivery_attributed :
    EnvelopeAttributed demoAttributedDelivery.envelope
theorem demoAttributedDelivery_wellFormed :
    wellFormed (.openChannel demoAttributedDelivery.wire)

theorem concrete_authenticated_delivery :
    ∃ d : AuthenticatedDelivery,
      wellFormed (.openChannel d.wire) ∧
        TransportAuthenticated d ∧ SessionKeyBinding d ∧
        EnvelopeAttributed d.envelope

theorem concrete_authenticated_route (a : AcceptChannel)
    (H : ByteArray → ByteArray) :
    ∃ d : AuthenticatedDelivery,
      TransportAuthenticated d ∧ SessionKeyBinding d ∧
        EnvelopeAttributed d.envelope ∧
        OpenRouteReachable (afterOpenRoute d.envelope) ∧
        FundingReachable (acceptorPhaseAfter d.wire a) ∧
        FundingScriptHashLinked H (d.wire.toFundingParams H a)
```

The witnesses use concrete 33-byte keys, the 32-byte zero channel id, a
well-formed type-32 record, an established session, and the wave-9 concrete
route. The unbound witness differs only in the session key, so the negative and
positive cases are genuinely populated.

## 7. Summary theorem

`transport_auth_summary` bundles:

1. authentication plus `SessionKeyBinding` implies `EnvelopeAttributed`;
2. every authenticated, key-bound delivery reaches the routed
   `funding_created` witness;
3. the same wire is attributed under one authenticated session and not another;
4. an authenticated but unattributed delivery exists;
5. no wire-only sender function exists;
6. the payload carries no signature.

## 8. Validation

Scoped build:

```text
$ export PATH=/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
$ LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
    lake build LnLean.Proofs.Protocol.TransportAuthTargets
✔ [22/22] Built LnLean.Proofs.Protocol.TransportAuthTargets (1.2s)
Build completed successfully (22 jobs).
```

Line count: **622**.

Public-theorem axiom audit (temporary `#print axioms` file over all 29 public
theorems; no repository audit file edited):

* axiom-free: `transportAuthenticated_with_wire`, `attributed_envelope_wire`,
  `demoAttributedDelivery_authenticated`, `demoAttributedDelivery_bound`,
  `demoUnattributedDelivery_authenticated`, `authenticated_not_bound`,
  `not_universal_sessionKeyBinding`,
  `wire_payload_does_not_determine_session_key`, `no_wire_sender_function`;
* `propext` only: the remaining positive, counterexample, and summary theorems;
* `propext` + `Quot.sound`: `authenticated_key_in_funding_script`;
* `propext` + `Quot.sound` + `Classical.choice`:
  `demoAttributedDelivery_wellFormed`, `concrete_authenticated_delivery`,
  `advertised_key_independent_of_session_key`.

Union of dependencies: `propext`, `Quot.sound`, `Classical.choice` — exactly
the allowed set. No disallowed dependency.

Forbidden-token scan over the owned Lean file:

```text
$ grep -nE "sorry|axiom|admit|native_decide|unsafe|@\[implemented_by\]" \
    LnLean/Proofs/Protocol/TransportAuthTargets.lean
NO_FORBIDDEN_TOKENS
```

## 9. What is still not derived

The remaining boundary is precise:

1. **`SessionKeyBinding` is assumed, not derived.** The model says the session
   is authenticated (`TransportAuthenticated`) and separately assumes the
   session key equals the advertised funding key. The wire has no sender field,
   and `no_wire_sender_function` shows no payload-only function can supply the
   session key. A real transport (Noise/BOLT 8) must establish the binding
   between the session's authenticated peer key and the advertised funding key;
   this module does not implement or verify that transport.
2. **Transport authentication is not attribution.** Even with two established
   sessions, the same wire can be attributed under one key and not another
   (`transport_auth_not_from_wire`). Authentication of *a session* does not
   authenticate *the sender of a particular type-32 payload* without the binding
   law.
3. **C3/key ownership remains `PR-01`.** `open_channel` carries no signature
   (`authenticated_delivery_no_signature`), and any valid funding key can be
   advertised independently of the session key
   (`advertised_key_independent_of_session_key`). Nothing here proves that the
   peer owns the secret key for `funding_pubkey`. That requires the
   secret-key/signing model and the explicit `KeyBinding`/PoP contract, not this
   transport-interface layer.
4. **No real transport is claimed.** `TransportSession.established` is an
   abstract Boolean. There is no Noise handshake, channel binding, key
   confirmation, or cryptographic reduction in this module.

`L1-03` therefore stays open: the additive transport interface and its positive
composition are proved, but transport key binding, C3/key ownership, and the
finite C1 funding-script admission remain explicit assumptions.

## 10. Catalog integration recommendation for `LN-PR-001`

Append the following targets to the `leanTarget` string of `LN-PR-001` in
`LnLean/Proofs/Obligations.lean` and to the mirrored `targetTable`,
`provedTable`, `provedDeclarations`, and `lneanModules` structures in
`LnLean/Proofs/Traceability.lean`:

```text
LnLean.Proofs.Protocol.TransportAuthTargets.transport_authenticated_attributed
LnLean.Proofs.Protocol.TransportAuthTargets.authenticated_delivery_reaches_fundingCreated
LnLean.Proofs.Protocol.TransportAuthTargets.authenticated_open_reaches_funding
LnLean.Proofs.Protocol.TransportAuthTargets.transport_auth_not_from_wire
LnLean.Proofs.Protocol.TransportAuthTargets.unattributed_delivery_exists
LnLean.Proofs.Protocol.TransportAuthTargets.no_session_binding_counterexample
LnLean.Proofs.Protocol.TransportAuthTargets.no_wire_sender_function
LnLean.Proofs.Protocol.TransportAuthTargets.transport_auth_summary
```

The first three are the positive interface and route composition; the next three
are the sharp no-auth/wrong-key counterexamples; the last two are the
payload-impossibility and bundled summary. Keep the row `proved` at the
model-level claim, but do not strengthen its wording to unconditional transport
authentication or key ownership.

Add `"LnLean.Proofs.Protocol.TransportAuthTargets"` to `lneanModules` beside
the existing `OpenChannelRoutingTargets` entry.

Root import recommendation (parent-owned file):

```lean
import LnLean.Proofs.Protocol.TransportAuthTargets
```

After the existing routing import in `LnLean.lean`.

Axiom-audit recommendation (`LnLean/Proofs/PhaseC3/AxiomAudit.lean`): import the
module and add `#print axioms` entries for at least the eight targets above.
All are clean under the allowed axioms.

Docs update: extend the `L1-03` row in `docs/OPEN-ISSUES.md` to record wave 10 —
transport session interface, explicit `SessionKeyBinding`, attributed delivery
composed with the routed funding witness, and the same-wire/two-session
counterexample. Keep the status open for transport key binding, C3/key
ownership, and the finite C1 admission; do not claim Noise or key ownership.

No new obligation id is recommended; `LN-PR-001` already carries the type-32
wire and routed evidence, and `LN-L1-001` remains the secondary funding row if
the P2WSH construction targets are mirrored.
