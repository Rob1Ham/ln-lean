# S9-L1-OPENCHANNEL-ROUTING — transport attribution and additive handshake routing for type-32 `open_channel`

**Lane:** `S9-L1-OPENCHANNEL-ROUTING`
**Issue:** `L1-03`
**Recommended catalog rows:** `LN-PR-001` (primary `open_channel` row), with
funding-side evidence optionally mirrored into `LN-L1-001`
**Branch / validation HEAD:** `repair/integrated` at `93fa943`
**Status:** complete (scoped build, axiom audit, and forbidden-token scan clean)
**Owned files created:** `LnLean/Proofs/Protocol/OpenChannelRoutingTargets.lean`,
`agents/reports/swarm9/S9-L1-OPENCHANNEL-ROUTING.md`
**Files edited outside the owned set:** none by this lane.  No Git write,
commit, or push.  Other lanes' working-tree changes are present and untouched.
No core patch was applied; the additive model in the owned module is sufficient
for the lane, and the integration recommendation is in §8.

---

## 1. Objective

Wave 8 added the exact type-32 wire record `OpenChannelWire`, the projection
`OpenChannelWire.toHandshakeOpenChannel`, and end-to-end reachability of the
separate `FundingPhase` machine.  It left three routing/attribution boundaries
explicit:

1. the `open_channel` payload carries no sender identity, so the transport,
   not the wire payload, must attribute the message to a peer;
2. `HandshakeState`/`handshakeStep` have no opening transition — the v1 machine
   absorbs the arrival of `open_channel` into the guard on `sendAcceptChannel`;
3. `Peer.receive` rejects `open_channel` unless a channel record already exists
   under the temporary channel id, which is impossible for the opening message.

The wave-9 question is whether a faithful, non-vacuous routing model can be
added **without changing** `Messages.lean`, `Handshake.lean`, or `Peer.lean`,
and whether the resulting model supports the positive path

```text
type-32 wire record -> Handshake.OpenChannel -> FundingPhase -> funding construction
```

while keeping a sharp boundary: wire payload, structural well-formedness, and
the funding hash link do **not** authenticate the sender, and the wire carries
no proof of key possession.

## 2. Answer in one paragraph

Yes.  The transport-delivered object is modelled as an `OpenChannelEnvelope`
(reusing `FundingAuthTargets.PeerIdentity`) carrying the unchanged wire record;
attribution is the explicit predicate `EnvelopeAttributed`, i.e. the transport
key equals the wire `funding_pubkey`.  Routing is added **additively**:
`OpenRouteState` wraps the unchanged `PeerState` and records at most one received
envelope; the `recvOpen` event is gated by the same pre-accept handshake
configuration that enables `accept_channel`, records the envelope, and leaves
`HandshakeState` unchanged.  From the connected initial state the lane proves a
concrete route through `open_channel`, `accept_channel`, and
`funding_created`, and composes the envelope projection with
`FundingPhase`/`acceptorPhaseAfter` to reach the hash-linked P2WSH funding
construction.  The negative side is mechanized rather than assumed: the same
payload is compatible with two different transport senders; one and the same
payload can be attributed to one peer and not another; an unattributed opening
is still routed; structural well-formedness and the funding hash link do not
imply attribution; and `open_channel` carries no signature.  Funding-key binding
is restated at the wire level under the finite `CollisionFreeOn` admission, and
the module proves that the model's 32-byte C1 does not bind 71-byte funding
witness scripts.  No core file was patched.

## 3. Exact claims

All declarations are in the namespace

```lean
LnLean.Proofs.Protocol.OpenChannelRoutingTargets
```

The prefix is omitted in the code snippets for readability; the full name of a
shown declaration is the namespace plus the shown name.  The summary theorem is
written out in full at the end of this section.

### 3.1 The transport envelope and the attribution hypothesis

```lean
structure OpenChannelEnvelope where
  sender : PeerIdentity
  wire : OpenChannelWire

def OpenChannelEnvelope.open (r : OpenChannelEnvelope) : OpenChannel :=
  r.wire.toHandshakeOpenChannel

def EnvelopeAttributed (r : OpenChannelEnvelope) : Prop :=
  OpenChannelAttributed r.sender r.wire.toHandshakeOpenChannel
```

```lean
@[simp] theorem OpenChannelEnvelope.open_eq (r : OpenChannelEnvelope) :
    r.open = r.wire.toHandshakeOpenChannel

theorem envelopeAttributed_iff (r : OpenChannelEnvelope) :
    EnvelopeAttributed r ↔ r.sender.key = r.wire.fundingPubKey

@[simp] theorem envelopeAttributed_pair (w : OpenChannelWire)
    (i : PeerIdentity) :
    EnvelopeAttributed ⟨i, w⟩ ↔ i.key = w.fundingPubKey

theorem attributed_wire_key_in_script (H : ByteArray → ByteArray)
    (r : OpenChannelEnvelope) (a : AcceptChannel)
    (hattr : EnvelopeAttributed r) :
    r.sender.key = (r.wire.toFundingNegotiation a).localFundingKey ∧
      KeyInScript (r.wire.toFundingParams H a).witnessScript.bytes r.sender.key

theorem exists_valid_pubKey_ne (k : PubKey) :
    ∃ k' : PubKey, k'.Valid ∧ k' ≠ k
```

`EnvelopeAttributed` is the lifted `FundingAuthTargets.OpenChannelAttributed`:
it is exactly equality of the transport-authenticated key and the advertised
wire funding key.  It does not hide a signature check.  Under this explicit
hypothesis, `attributed_wire_key_in_script` transports the wave-7 key-in-script
result through both the wire and handshake projections, for the **local**
funding key of the joint construction.

### 3.2 The non-attribution / forgery boundary

```lean
theorem wire_payload_does_not_determine_sender :
    ∃ r₁ r₂ : OpenChannelEnvelope,
      r₁.wire = r₂.wire ∧ r₁.sender ≠ r₂.sender

theorem same_wire_attributed_and_not :
    ∃ r₁ r₂ : OpenChannelEnvelope,
      r₁.wire = r₂.wire ∧ EnvelopeAttributed r₁ ∧ ¬ EnvelopeAttributed r₂

theorem wellFormed_wire_not_attributed (i : PeerIdentity) :
    ∃ w : OpenChannelWire,
      wellFormed (.openChannel w) ∧ ¬ EnvelopeAttributed ⟨i, w⟩

theorem hash_link_does_not_imply_attribution (H : ByteArray → ByteArray)
    (i : PeerIdentity) (a : AcceptChannel) :
    ∃ w : OpenChannelWire,
      wellFormed (.openChannel w) ∧
        FundingScriptHashLinked H (w.toFundingParams H a) ∧
        ¬ EnvelopeAttributed ⟨i, w⟩

theorem wire_carries_no_signature (w : OpenChannelWire) :
    signatures (.openChannel w) = []

theorem any_valid_key_advertisable {k : PubKey} (hk : k.Valid) :
    ∃ w : OpenChannelWire,
      wellFormed (.openChannel w) ∧ w.fundingPubKey = k
```

The first two theorems are the sharpest separation statements: the wire is
literally the same payload in both envelopes, and only the transport sender
distinguishes attribution.  `wellFormed_wire_not_attributed` holds for **every**
claimed sender; `hash_link_does_not_imply_attribution` adds the constructed
funding hash link as well.  `wire_carries_no_signature` is definitional:
`Msg.openChannel` contributes no entry to the message signature list.
`any_valid_key_advertisable` records the matching positive boundary: every
33-byte well-formed key can be advertised without a possession check.

### 3.3 The additive routing state and its laws

```lean
structure OpenRouteState where
  peer : PeerState
  received? : Option OpenChannelEnvelope := none

def OpenRouteState.initial : OpenRouteState

abbrev OpenRouteState.canRecvOpen (s : OpenRouteState) : Prop :=
  s.peer.transport = TransportState.up ∧
    s.peer.handshake.initSent = true ∧
    s.peer.handshake.initReceived = true ∧
    s.peer.handshake.acceptSent = false ∧
    s.peer.handshake.acceptReceived = false ∧
    s.peer.handshake.fundingCreatedSent = false ∧
    s.peer.handshake.fundingCreatedReceived = false ∧
    s.peer.handshake.fundingSignedSent = false ∧
    s.peer.handshake.fundingSignedReceived = false ∧
    s.peer.handshake.channelReadySent = false ∧
    s.peer.handshake.channelReadyReceived = false ∧
    s.received? = none

def OpenRouteState.observed (s : OpenRouteState) :
    PeerState × Option OpenChannelWire

inductive OpenRouteEvent where
  | plain (e : HandshakeEvent)
  | recvOpen (r : OpenChannelEnvelope)

def openRouteStep (s : OpenRouteState) :
    OpenRouteEvent → Option OpenRouteState

inductive OpenRouteReachable : OpenRouteState → Prop where
  | initial : OpenRouteReachable OpenRouteState.initial
  | step {s s' : OpenRouteState} (e : OpenRouteEvent) :
      OpenRouteReachable s → openRouteStep s e = some s' →
        OpenRouteReachable s'
```

The `plain` event runs the unchanged `handshakeStep` behind the unchanged
transport gate.  The `recvOpen` event requires `canRecvOpen`, records the
envelope in `received?`, and does not alter `peer`.  The receive rule is
deliberately **not** gated by `EnvelopeAttributed`; attribution remains a
transport-layer hypothesis.

Routing-step laws:

```lean
theorem openRouteStep_plain_received? {s s' : OpenRouteState}
    {e : HandshakeEvent} (h : openRouteStep s (.plain e) = some s') :
    s'.received? = s.received?

theorem openRouteStep_recvOpen_received? {s s' : OpenRouteState}
    {r : OpenChannelEnvelope} (h : openRouteStep s (.recvOpen r) = some s') :
    s'.received? = some r

theorem openRouteStep_recvOpen_peer {s s' : OpenRouteState}
    {r : OpenChannelEnvelope} (h : openRouteStep s (.recvOpen r) = some s') :
    s'.peer = s.peer

theorem openRouteStep_recvOpen_handshake {s s' : OpenRouteState}
    {r : OpenChannelEnvelope} (h : openRouteStep s (.recvOpen r) = some s') :
    s'.peer.handshake = s.peer.handshake

theorem canRecvOpen_of_recvOpen {s s' : OpenRouteState}
    {r : OpenChannelEnvelope} (h : openRouteStep s (.recvOpen r) = some s') :
    s.canRecvOpen

theorem openRouteStep_recvOpen_inited {s s' : OpenRouteState}
    {r : OpenChannelEnvelope} (h : openRouteStep s (.recvOpen r) = some s') :
    s.peer.handshake.initSent = true ∧
      s.peer.handshake.initReceived = true

theorem canSendAccept_of_canRecvOpen {s : OpenRouteState}
    (h : s.canRecvOpen) : s.peer.handshake.canSendAccept

theorem openRouteStep_recvOpen_canSendAccept {s s' : OpenRouteState}
    {r : OpenChannelEnvelope} (h : openRouteStep s (.recvOpen r) = some s') :
    s'.peer.handshake.canSendAccept

theorem openRouteStep_recvOpen_canRecvAccept {s s' : OpenRouteState}
    {r : OpenChannelEnvelope} (h : openRouteStep s (.recvOpen r) = some s') :
    s'.peer.handshake.canRecvAccept
```

Provenance, stability, and sender-blindness:

```lean
theorem openRouteReachable_received?_provenance {s : OpenRouteState}
    (h : OpenRouteReachable s) :
    ∀ {r : OpenChannelEnvelope}, s.received? = some r →
      ∃ s0 s1 : OpenRouteState,
        OpenRouteReachable s0 ∧ openRouteStep s0 (.recvOpen r) = some s1

theorem openRouteReachable_received?_stable {s s' : OpenRouteState}
    (_h : OpenRouteReachable s) {e : OpenRouteEvent}
    (hstep : openRouteStep s e = some s')
    {r : OpenChannelEnvelope} (hr : s.received? = some r) :
    s'.received? = some r

theorem openRouteStep_recvOpen_observed_ignores_sender
    {s s₁ s₂ : OpenRouteState} {i₁ i₂ : PeerIdentity} {w : OpenChannelWire}
    (h₁ : openRouteStep s (.recvOpen ⟨i₁, w⟩) = some s₁)
    (h₂ : openRouteStep s (.recvOpen ⟨i₂, w⟩) = some s₂) :
    s₁.observed = s₂.observed

theorem route_outcome_independent_of_attribution
    {s s₁ s₂ : OpenRouteState} {r₁ r₂ : OpenChannelEnvelope}
    (hw : r₁.wire = r₂.wire)
    (h₁ : openRouteStep s (.recvOpen r₁) = some s₁)
    (h₂ : openRouteStep s (.recvOpen r₂) = some s₂) :
    s₁.observed = s₂.observed

theorem unattributed_open_is_routed :
    ∃ (s : OpenRouteState) (r : OpenChannelEnvelope),
      OpenRouteReachable s ∧ s.received? = some r ∧ ¬ EnvelopeAttributed r
```

A recorded envelope has actual receive-step provenance and cannot be
overwritten by a later plain or receive step.  `observed` forgets the transport
sender and keeps only the peer state plus the wire record, so the routing
outcome is a function of the payload, not of attribution.
`unattributed_open_is_routed` proves non-vacuously that the receive rule does
not require the key binding.

### 3.4 Concrete route to `accept_channel` and `funding_created`

```lean
theorem canSendFundingCreated_after_recvAccept {s : HandshakeState}
    (h : s.canSendAccept) (a : AcceptChannel) :
    ({ s with acceptReceived := true, acceptChannel? := some a }).canSendFundingCreated

theorem handshake_recvAccept_then_fundingCreated {s : HandshakeState}
    (h : s.canSendAccept) (a : AcceptChannel) :
    ∃ s1 s2 : HandshakeState,
      handshakeStepRecvAccept s a = some s1 ∧
        handshakeStep s1 .sendFundingCreated = some s2 ∧
        s1.acceptChannel? = some a ∧
        s2.acceptReceived = true

theorem afterInitRoute_reachable : OpenRouteReachable afterInitRoute

theorem afterInitRoute_canRecvOpen : afterInitRoute.canRecvOpen

theorem afterOpenRoute_reachable (r : OpenChannelEnvelope) :
    OpenRouteReachable (afterOpenRoute r)

@[simp] theorem afterOpenRoute_received? (r : OpenChannelEnvelope) :
    (afterOpenRoute r).received? = some r

theorem afterOpenRoute_canSendAccept (r : OpenChannelEnvelope) :
    (afterOpenRoute r).peer.handshake.canSendAccept

theorem afterOpenRoute_canRecvAccept (r : OpenChannelEnvelope) :
    (afterOpenRoute r).peer.handshake.canRecvAccept

theorem openRoute_initial_to_fundingCreated (r : OpenChannelEnvelope)
    (a : AcceptChannel) :
    OpenRouteReachable (afterOpenRoute r) ∧
      ∃ s1 s2 : HandshakeState,
        handshakeStepRecvAccept (afterOpenRoute r).peer.handshake a = some s1 ∧
          handshakeStep s1 .sendFundingCreated = some s2 ∧
          s1.acceptChannel? = some a ∧
          s2.acceptReceived = true
```

`openRoute_initial_to_fundingCreated` is the non-vacuity witness for the
routing model.  It starts from the connected initial state, runs the two `init`
messages, receives an **arbitrary** envelope (attributed or not), records an
`accept_channel` payload, and enables `funding_created`, using the unchanged v1
handshake functions.  No opening transition is added to `HandshakeState`.

### 3.5 Wire -> `Handshake.OpenChannel` -> funding construction

```lean
def receivedPhase (w : OpenChannelWire) : FundingPhase

theorem receivedPhase_reachable (w : OpenChannelWire) :
    FundingReachable (receivedPhase w)

@[simp] theorem receivedPhase_openReceived (w : OpenChannelWire) :
    (receivedPhase w).openReceived = some w.toHandshakeOpenChannel

theorem routed_wire_projection (r : OpenChannelEnvelope) :
    r.open = r.wire.toHandshakeOpenChannel

theorem routed_open_to_funding_phase {s : OpenRouteState}
    (_h : OpenRouteReachable s) {r : OpenChannelEnvelope}
    (_hr : s.received? = some r) :
    FundingReachable (receivedPhase r.wire) ∧
      (receivedPhase r.wire).openReceived =
        some r.wire.toHandshakeOpenChannel

theorem routed_open_to_funding_construction {s : OpenRouteState}
    (_h : OpenRouteReachable s) {r : OpenChannelEnvelope}
    (_hr : s.received? = some r) (H : ByteArray → ByteArray)
    (a : AcceptChannel) :
    FundingReachable (acceptorPhaseAfter r.wire a) ∧
      (acceptorPhaseAfter r.wire a).acceptorNegotiation? =
        some (r.wire.toFundingNegotiation a) ∧
      FundingScriptHashLinked H (r.wire.toFundingParams H a) ∧
      (r.wire.toFundingParams H a).fundingScriptPubKey =
        p2wsh (H (TwoOfTwoScriptBytes
          (r.wire.toFundingNegotiation a).firstFundingKey
          (r.wire.toFundingNegotiation a).secondFundingKey))

theorem routed_open_accept_bound_before_fundingCreated
    {s : OpenRouteState} (_h : OpenRouteReachable s)
    {r : OpenChannelEnvelope} (_hr : s.received? = some r)
    {hs hs' : HandshakeState}
    (hstep : handshakeStep hs .sendFundingCreated = some hs')
    (a : AcceptChannel) (H : ByteArray → ByteArray) :
    hs.acceptReceived = true ∧
      ((r.wire.toFundingNegotiation a).toFundingParams H).remoteFundingKey =
        a.fundingPubKey
```

The routed wire projects to the exact `Handshake.OpenChannel` consumed by
`FundingPhase`.  The funding construction is hash-linked by definition, and the
output is P2WSH over the ordered BOLT 3 2-of-2 script.  The last theorem records
the handshake boundary: whenever `sendFundingCreated` is enabled, the accept
milestone is set and the remote funding key is exactly the recorded
`accept_channel.funding_pubkey`.

### 3.6 Finite C1 admission and the existing-API insufficiency

```lean
theorem wire_output_determines_key_set (H : ByteArray → ByteArray)
    (w₁ : OpenChannelWire) (a₁ : AcceptChannel)
    (w₂ : OpenChannelWire) (a₂ : AcceptChannel)
    (hwf₁ : (w₁.toFundingParams H a₁).WellFormed)
    (hwf₂ : (w₂.toFundingParams H a₂).WellFormed)
    (heq : (w₁.toFundingParams H a₁).fundingScriptPubKey =
      (w₂.toFundingParams H a₂).fundingScriptPubKey)
    (hc1 : CollisionFreeOn H
      (w₁.toFundingParams H a₁).witnessScript.bytes
      (w₂.toFundingParams H a₂).witnessScript.bytes) :
    (w₁.fundingPubKey = w₂.fundingPubKey ∧
        a₁.fundingPubKey = a₂.fundingPubKey) ∨
      (w₁.fundingPubKey = a₂.fundingPubKey ∧
        a₁.fundingPubKey = w₂.fundingPubKey)

theorem wire_binding_needs_FundingScript_C1 :
    ∃ H : ByteArray → ByteArray,
      (∀ b : ByteArray, (H b).size = 32) ∧
        LnLean.Crypto.CollisionResistant H ∧
        ∃ x y : ByteArray,
          x.size = 71 ∧ y.size = 71 ∧ x ≠ y ∧ H x = H y

theorem funding_output_independent_of_sender
    (H : ByteArray → ByteArray) (w : OpenChannelWire)
    (a : AcceptChannel) (i₁ i₂ : PeerIdentity) :
    (⟨i₁, w⟩ : OpenChannelEnvelope).wire.toFundingParams H a =
      (⟨i₂, w⟩ : OpenChannelEnvelope).wire.toFundingParams H a
```

`wire_output_determines_key_set` restates
`FundingAuthTargets.openAccept_output_determines_key_set` at the wire layer.
The conclusion is agreement on the **unordered** funding-key set, not on
identity or ordering.  The separate finite `CollisionFreeOn` admission is
necessary: `wire_binding_needs_FundingScript_C1` proves that a 32-byte-output
hash satisfying the model's `CollisionResistant` field can still collide on
distinct 71-byte witness scripts.  `funding_output_independent_of_sender` is
definitional: the funding output cannot be used to recover attribution.

The unchanged API's gaps are recorded, not patched:

```lean
theorem peer_receive_openChannel_requires_channel (s : PeerState)
    (w : OpenChannelWire)
    (hf : findChannel s w.temporaryChannelId = none) :
    receive s (.openChannel w) = none

theorem receive_openChannel_handshake_unchanged {s s' : PeerState}
    {w : OpenChannelWire} (h : receive s (.openChannel w) = some s') :
    s'.handshake = s.handshake

theorem no_handshake_event_for_openChannel (w : OpenChannelWire) :
    sendEvent? (.openChannel w) = none ∧
      receiveEvent? (.openChannel w) = none
```

`receive_openChannel_handshake_unchanged` says that even the existing
channel-record path does not record the opening payload in the handshake state.
`no_handshake_event_for_openChannel` proves there is no v1 handshake event for
the opening in either direction.  This is why the lane adds `recvOpen` in the
wrapper rather than claiming an existing `HandshakeState` transition.

### 3.7 Bundled summary

```lean
theorem LnLean.Proofs.Protocol.OpenChannelRoutingTargets.openChannel_routing_summary :
    (∀ r : OpenChannelEnvelope,
        r.open = r.wire.toHandshakeOpenChannel) ∧
      (∀ w : OpenChannelWire, FundingReachable (receivedPhase w)) ∧
      (∀ (H : ByteArray → ByteArray) (r : OpenChannelEnvelope)
          (a : AcceptChannel),
        FundingReachable (acceptorPhaseAfter r.wire a) ∧
          FundingScriptHashLinked H (r.wire.toFundingParams H a)) ∧
      (∃ r₁ r₂ : OpenChannelEnvelope,
        r₁.wire = r₂.wire ∧ EnvelopeAttributed r₁ ∧ ¬ EnvelopeAttributed r₂) ∧
      (∃ (s : OpenRouteState) (r : OpenChannelEnvelope),
        OpenRouteReachable s ∧ s.received? = some r ∧ ¬ EnvelopeAttributed r) ∧
      (∀ i : PeerIdentity,
        ∃ w : OpenChannelWire,
          wellFormed (.openChannel w) ∧ ¬ EnvelopeAttributed ⟨i, w⟩) ∧
      (∀ w : OpenChannelWire, signatures (.openChannel w) = [])
```

The conjunction bundles: exact projection, funding-phase reachability,
hash-linked funding construction, the same-wire/different-attribution witness,
the routed-unattributed witness, well-formed non-attribution for every claimed
sender, and the absence of a wire signature.

## 4. Artifacts

- `LnLean/Proofs/Protocol/OpenChannelRoutingTargets.lean` — 895 lines, new,
  untracked; 47 public theorems plus the definitions above.
- `agents/reports/swarm9/S9-L1-OPENCHANNEL-ROUTING.md` — this report.
- Not modified by this lane: `LnLean/Protocol/Messages.lean`,
  `LnLean/Protocol/Handshake.lean`, `LnLean/Protocol/Peer.lean`,
  `LnLean.lean`, `LnLean/Proofs/Obligations.lean`,
  `LnLean/Proofs/Traceability.lean`, `LnLean/Proofs/PhaseC3/AxiomAudit.lean`,
  catalog/docs, and Git state.  Other lanes' working-tree changes are present
  and untouched.

## 5. Validation

### 5.1 Scoped build

Exact command (shared lock, single thread, only the new module):

```bash
cd /home/ubuntu/ln-lean-repair
export PATH=/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Proofs.Protocol.OpenChannelRoutingTargets
```

Result at report time:

```text
Build completed successfully (21 jobs).
RC=0
```

No warnings, no errors, and no full `lake build` was run.

### 5.2 Axiom audit

All 47 public theorems were checked with `#print axioms` using the scratch audit
file `/tmp/opencode/AuditRouting.lean` under the same lock:

```bash
cd /home/ubuntu/ln-lean-repair
export PATH=/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake env lean /tmp/opencode/AuditRouting.lean
```

Result: `RC=0`, 47 theorem entries.  Every entry depends only on a subset of
`{propext, Quot.sound, Classical.choice}`.  Representative output:

```text
'...OpenChannelRoutingTargets.envelopeAttributed_iff' depends on axioms: [propext]
'...OpenChannelRoutingTargets.wire_payload_does_not_determine_sender' does not depend on any axioms
'...OpenChannelRoutingTargets.wire_output_determines_key_set' depends on axioms: [propext,
 Quot.sound]
'...OpenChannelRoutingTargets.openChannel_routing_summary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Five theorems depend on no axioms: `wire_payload_does_not_determine_sender`,
`routed_wire_projection`, `OpenChannelEnvelope.open_eq`,
`receivedPhase_openReceived`, and `afterOpenRoute_received?`.  No axiom outside the allowed set appears.

### 5.3 Forbidden-construct scan

```bash
cd /home/ubuntu/ln-lean-repair
grep -nE '\b(sorry|admit|axiom|native_decide|unsafe|implemented_by)\b' \
  LnLean/Proofs/Protocol/OpenChannelRoutingTargets.lean
# exit 1 (no matches)
```

No `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, or
`@[implemented_by]` is used.

### 5.4 Git state

`git status --short` at validation time shows this module and this report as
untracked, alongside other lanes' modifications.  This lane ran no `git add`,
`git commit`, or `git push`.

## 6. Gaps and trust boundary

1. **Attribution is a transport hypothesis, never derived.**  `sender` is the
   identity the transport claims for the delivery; `EnvelopeAttributed` is an
   explicit equality hypothesis.  The module proves no cryptographic
   authentication of the transport, no C3 reduction, and no
   delivery-attribution theorem.  A production integration must establish the
   envelope's sender at the authenticated transport layer.
2. **The wire carries no proof of possession.**  `wire_carries_no_signature`
   is definitional for `Msg.openChannel`.  `any_valid_key_advertisable` shows
   every structurally valid key can be advertised.  Key ownership remains the
   separate C3/`PR-01` obligation.
3. **`PubKey.Valid` and `wellFormed` are structural.**  In the model,
   `PubKey.Valid` is exactly the 33-byte size predicate, and
   `wellFormed (.openChannel w)` checks the temporary channel id and public-key
   lengths, not curve membership, semantic amount bounds, or ownership.  The
   boundary witnesses use model-valid byte strings, not real secp256k1 points.
4. **Structural well-formedness and the hash link do not authenticate.**
   `wellFormed_wire_not_attributed` and
   `hash_link_does_not_imply_attribution` are universal-in-the-sender
   counterexamples.  They must not be read as evidence that valid messages are
   attributable.
5. **The routing model is additive, not a core state-machine patch.**
   `OpenRouteState.recvOpen` records the envelope and leaves `HandshakeState`
   unchanged.  The v1 machine still has no opening milestone; the lane does not
   claim that `HandshakeState` itself routes `open_channel`.
   `OpenRouteState.initial` starts with the transport already `up` as an
   environment precondition, and the guard assumes both `init` messages and the
   pre-accept configuration.  There is no network scheduler, reordering, or
   adversarial delivery model.
6. **The receive rule deliberately does not check attribution.**
   `unattributed_open_is_routed` is a theorem, not a bug: the protocol state
   routes the payload, and attribution has to be enforced before or at the
   transport boundary.  Adding an `EnvelopeAttributed` guard to `recvOpen` would
   be a policy change and is not claimed.
7. **Funding reachability is model-level.**  `FundingReachable` and
   `acceptorPhaseAfter` are the separate wave-7/8 funding machine.  The lane
   proves the wire projection reaches the construction; it does not prove that a
   peer accepts the funding, that signatures are valid, or that the funding
   transaction is consensus-valid.
8. **The C1 admission is finite and pairwise.**  `wire_output_determines_key_set`
   needs `WellFormed` on both parameter sets, equality of the funding output,
   and `CollisionFreeOn H` at the two 71-byte witness scripts.  It is not global
   SHA-256 injectivity and says nothing about ordered key identity.
   `wire_binding_needs_FundingScript_C1` records that the 32-byte C1 field cannot
   replace this admission.
9. **No cryptographic or consensus upgrade.**  Nothing here proves `EufCma`,
   `KeyBinding`, a C3 reduction, proof of possession, unforgeability of
   `open_channel`, or unconditional consensus.  The positive direction remains
   model-level and conditional.

## 7. Core patch status

No core patch was applied.  The existing-API insufficiency is proved in §3.6:
`Peer.receive` needs a pre-existing channel record, the accepted path does not
record the opening payload in the handshake, and there is no `HandshakeEvent`
for `open_channel`.  The additive wrapper is sufficient to state and prove the
routing and attribution claims without changing the v1 handshake or peer
semantics.

A future **non-additive** integration would need a coordinated change to
`HandshakeState`/`Peer.receive` to store the opening and to expose it to the
peer state machine, plus corresponding updates to the obligation, traceability,
and axiom-audit artifacts.  That is outside this lane and was deliberately not
attempted.  The current module is the faithful, reviewable boundary.

## 8. Catalog integration recommendation for `L1-03`

`L1-03` is an open issue rather than a dedicated catalog id.  The closest
existing catalog row is `LN-PR-001` ("`open_channel` accepts a funding amount
only above the dust and minimum-channel bounds"), which already carries the
wave-8 `OpenChannelWire` targets; the funding-side row `LN-L1-001` is the
natural secondary location for the construction/reachability evidence.

**Primary `LN-PR-001` additions.**  Append these targets to the `leanTarget`
string in `LnLean/Proofs/Obligations.lean` (currently near line 263) and to the
four mirrored structures in `LnLean/Proofs/Traceability.lean`: `targetTable`
(near line 238), `provedTable` (near line 290), `provedDeclarations`, and
`lneanModules`:

```text
LnLean.Proofs.Protocol.OpenChannelRoutingTargets.openRoute_initial_to_fundingCreated
LnLean.Proofs.Protocol.OpenChannelRoutingTargets.openChannel_routing_summary
LnLean.Proofs.Protocol.OpenChannelRoutingTargets.unattributed_open_is_routed
LnLean.Proofs.Protocol.OpenChannelRoutingTargets.wire_payload_does_not_determine_sender
LnLean.Proofs.Protocol.OpenChannelRoutingTargets.wire_binding_needs_FundingScript_C1
```

The first is the positive non-vacuity witness; the summary bundles projection,
funding reachability, and the non-attribution boundary; the remaining three are
the sharp trust-boundary evidence.

**Optional `LN-L1-001` additions.**  If the funding row is used for the
wire-to-funding construction, add:

```text
LnLean.Proofs.Protocol.OpenChannelRoutingTargets.routed_open_to_funding_construction
LnLean.Proofs.Protocol.OpenChannelRoutingTargets.wire_output_determines_key_set
```

Do **not** change either row to "unconditional".  `L1-03` must remain open for
transport attribution/C3 and key ownership; the finite C1 admission must remain
explicit.

**Root import.**  In `LnLean.lean`, after line 131
(`import LnLean.Proofs.Protocol.OpenChannelWireTargets`), add:

```lean
import LnLean.Proofs.Protocol.OpenChannelRoutingTargets
```

**Traceability.**  In `LnLean/Proofs/Traceability.lean`, add the target/module
pairs for the five primary theorems to `targetTable`, `provedTable`, and
`provedDeclarations`, add the module string
`"LnLean.Proofs.Protocol.OpenChannelRoutingTargets"` to `lneanModules` beside
the existing `OpenChannelWireTargets` entry (near line 501), and keep all four
mirrored lists consistent.

**Axiom audit.**  In `LnLean/Proofs/PhaseC3/AxiomAudit.lean`, import the module
after line 88 and add `#print axioms` entries near line 352 for at least:

```text
LnLean.Proofs.Protocol.OpenChannelRoutingTargets.openRoute_initial_to_fundingCreated
LnLean.Proofs.Protocol.OpenChannelRoutingTargets.openChannel_routing_summary
LnLean.Proofs.Protocol.OpenChannelRoutingTargets.unattributed_open_is_routed
LnLean.Proofs.Protocol.OpenChannelRoutingTargets.wire_payload_does_not_determine_sender
LnLean.Proofs.Protocol.OpenChannelRoutingTargets.wire_binding_needs_FundingScript_C1
```

**Docs.**  Update the `L1-03` row in `docs/OPEN-ISSUES.md` to record wave 9:
additive `OpenRouteState`/`recvOpen` routing, envelope attribution as an
explicit hypothesis, the concrete `open_channel` -> `accept_channel` ->
`funding_created` witness, and the non-attribution/no-signature boundary.  Keep
the status open (for example, "open (transport attribution/C3; additive routing
proved)") and keep the next action focused on transport authentication,
`KeyBinding`, and the finite C1 admission.  Do not claim a core handshake patch.

**New obligation id.**  Not recommended.  A dedicated `LN-*` id would require
coordinated catalog, traceability, obligation, audit, and generated-doc edits;
the existing `LN-PR-001` and `LN-L1-001` evidence lists are sufficient.

## 9. Summary

- **Answer:** type-32 `open_channel` can be routed faithfully without patching
  `HandshakeState` or `Peer`, provided the transport envelope supplies
  attribution and the receive rule records the opening additively.  The wire
  payload itself does not determine or authenticate its sender.
- **Positive result:** `openRoute_initial_to_fundingCreated` proves a concrete
  route from the connected initial state through `open_channel`,
  `accept_channel`, and `funding_created`;
  `routed_open_to_funding_construction` composes the routed wire with
  `Handshake.OpenChannel` and `FundingPhase` to the hash-linked P2WSH funding
  construction.
- **Attribution boundary:** `wire_payload_does_not_determine_sender`,
  `same_wire_attributed_and_not`, `unattributed_open_is_routed`,
  `wellFormed_wire_not_attributed`,
  `hash_link_does_not_imply_attribution`, and `wire_carries_no_signature`.
- **Routing laws:** `openRouteStep_recvOpen_received?`,
  `openRouteStep_recvOpen_handshake`,
  `openRouteReachable_received?_provenance`,
  `openRouteReachable_received?_stable`,
  `openRouteStep_recvOpen_observed_ignores_sender`, and
  `route_outcome_independent_of_attribution`.
- **C1 boundary:** `wire_output_determines_key_set` under finite
  `CollisionFreeOn`; `wire_binding_needs_FundingScript_C1` shows the 32-byte C1
  field does not bind 71-byte witness scripts.
- **Full-name summary target:**
  `LnLean.Proofs.Protocol.OpenChannelRoutingTargets.openChannel_routing_summary`.
- **Files:** `LnLean/Proofs/Protocol/OpenChannelRoutingTargets.lean` (new, 895
  lines, 47 public theorems), `agents/reports/swarm9/S9-L1-OPENCHANNEL-ROUTING.md`
  (this report).
- **Validation:** scoped build 21/21, RC 0, no warnings; axiom audit of all 47
  public theorems within `{propext, Quot.sound, Classical.choice}`;
  forbidden-token scan clean.
- **Lane status:** **complete**.  No blocker.  Remaining work is integration
  (§8) and the explicit trust hypotheses in §6: transport authentication/C3,
  key ownership/`KeyBinding`, and the finite C1 admission.
