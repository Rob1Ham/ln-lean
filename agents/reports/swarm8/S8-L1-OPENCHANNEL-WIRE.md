# S8-L1-OPENCHANNEL-WIRE — type-32 `open_channel` wire coverage (`L1-03`)

> **Parent integration note (2026-10-18).** The lane's 313-byte constant was
> one 8-byte value field short. The parent corrected
> `Messages.msgLength`/`msgLength_openChannel` to **321** (287 fixed fields
> plus the standard 34-byte shutdown script; `chain_hash` and the TLV header
> are omitted). The historical 313/321 analysis below is retained as the lane
> record; the source now proves 321.

- Lane: `S8-L1-OPENCHANNEL-WIRE`
- Issue: `L1-03`
- Branch: `repair/integrated`
- Base: `3953c8c` (wave 8 launch), wave-7 code `b48d041`
- Date: 2026-10-18

## 1. Verdict

**Applied and green.**  `LnLean/Protocol/Messages.lean` now has a full modelled
BOLT 2 type-32 `open_channel` record (`OpenChannelWire`), the `Msg.openChannel`
and `MsgKind.openChannel` constructors, the type/decoder/length/identifier/key
cases, and the new proof module
`LnLean/Proofs/Protocol/OpenChannelWireTargets.lean`.  `Handshake.OpenChannel`
was **not** moved or duplicated: the new module projects `OpenChannelWire` onto
it and proves the projection, the funding construction, and the end-to-end
`FundingPhase` reachability.

The wave-7 patch's `Messages.lean` part is therefore applied, but `L1-03`
should stay **open** (wire coverage complete; authentication/transport and
handshake routing still open).  The exact 313-byte length is kept as the lane
and catalog specification; its arithmetic is inconsistent with the six
modelled 8-byte value fields (`321`), and that discrepancy is recorded in §3
and §9 for a parent decision.

No `Handshake.lean`, `LnLean.lean`, `Obligations.lean`, `Traceability.lean`,
`AxiomAudit.lean`, docs, or vendor files were edited.  No Git write command was
run.

## 2. Exact files changed

| File | Change |
|---|---|
| `LnLean/Protocol/Messages.lean` | Modified: `OpenChannelWire` record; `Msg.openChannel`; `MsgKind.openChannel`; `Msg.kind`, `wireType`, `kindOfType?`, `msgLength`, `channelId?`, `pubKeys` cases; four `[simp]` lemmas. |
| `LnLean/Proofs/Protocol/OpenChannelWireTargets.lean` | **New**: projection, funding construction, type/length/id/key laws, `FundingPhase` end-to-end, handshake/peer boundary. |
| `agents/reports/swarm8/S8-L1-OPENCHANNEL-WIRE.md` | This report. |

Owned downstream files (`LnLean/Protocol/Laws.lean`,
`LnLean/Proofs/Liveness.lean`,
`LnLean/Proofs/PhaseC3/PersistenceRecovery.lean`,
`LnLean/Proofs/Protocol/ErrorProps.lean`,
`LnLean/Proofs/Protocol/ChannelReestablishProps.lean`,
`LnLean/Proofs/WaveD/D21.lean`) **needed no source edits**.  Every one of their
`cases m`/`cases m.kind` matches already ends in a `_`/default branch, and the
new constructor is discharged by the existing `simp`/`omega`/`split` tactics.
They were rebuilt explicitly (140-job scoped build, RC 0) and by the full
build.  The general `Laws.lean` laws (`wireType_injective`,
`msgType_lt_65536`, `msgType_ne_zero`, `kindOfType?_msgType`, `msgLength_pos`)
also needed no edit and still prove over the new constructor.

No file outside the write set broke.  No downstream patch is required.

## 3. New constructor and length derivation

### 3.1 `OpenChannelWire` fields

The record carries the full modelled BOLT 2 v1 field set:

`temporaryChannelId`, `fundingSatoshis`, `pushMsat`, `dustLimitSatoshis`,
`maxHtlcValueInFlightMsat`, `channelReserveSatoshis`, `htlcMinimumMsat`,
`feeratePerKw`, `toSelfDelay`, `maxAcceptedHtlcs`, `fundingPubKey`,
`revocationBasepoint`, `paymentBasepoint`, `delayedPaymentBasepoint`,
`htlcBasepoint`, `firstPerCommitmentPoint`, `channelFlags`,
`shutdownScriptpubkey`.

`chain_hash` is omitted (network-wide connection parameter; no other message
models it).  `shutdownScriptpubkey` is the standard 34-byte P2WSH shutdown
script (`OP_0 <32-byte SHA-256>`) without TLV wrapping.

### 3.2 Constructor cases

- `MsgKind.openChannel` has `wireType = 32`.
- `kindOfType? 32 = some .openChannel`.
- `Msg.kind (.openChannel w) = .openChannel`.
- `msgLength (.openChannel w) = 313`.
- `channelId? (.openChannel w) = some w.temporaryChannelId`.
- `pubKeys (.openChannel w)` is the six-key list in BOLT 2 order:
  `fundingPubKey`, `revocationBasepoint`, `paymentBasepoint`,
  `delayedPaymentBasepoint`, `htlcBasepoint`, `firstPerCommitmentPoint`.

### 3.3 The 313 derivation and the 8-byte discrepancy

The lane-specified derivation is:

```text
temporary_channel_id                32
funding_satoshis                     8
push_msat                            8
dust_limit_satoshis                  8
max_htlc_value_in_flight_msat        8
channel_reserve_satoshis             8
htlc_minimum_msat                    8
feerate_per_kw                       4
to_self_delay                        2
max_accepted_htlcs                   2
6 points                        6 * 33 = 198
channel_flags                        1
shutdown_scriptpubkey (standard)    34
----------------------------------------
                                   321
```

`313` is obtained by the wave-7/8 prose expression
`32 + 8 + 8 + 8 + 8 + 8 + 4 + 2 + 2 + 6*33 + 1 + 34`, which counts **five**
8-byte fields.  `OpenChannelWire` has **six** (`funding_satoshis`, `push_msat`,
`dust_limit_satoshis`, `max_htlc_value_in_flight_msat`,
`channel_reserve_satoshis`, `htlc_minimum_msat`), so the literal field sum is
`321`; one 8-byte field is missing from the 313 expression.

For completeness, BOLT 2 v1 pins `shutdown_scriptpubkey` as TLV type 0, which
adds a 2-byte TLV header to the standard 34-byte script (`323` without
`chain_hash`), and the complete wire message including `chain_hash` is `355`.
The model deliberately uses the no-`chain_hash`, no-TLV convention, matching
the existing `msgLength` style.

**Decision made:** keep `313` as the lane and catalog specification, and record
the discrepancy here rather than silently changing the target.  The theorem
`msgLength_openChannel` is definitional over the model constant; it is **not** a
byte-serialization theorem.  The parent should either keep 313 as an explicitly
acknowledged model convention or correct it to 321 (modelled fields) / 323
(wire TLV) / 355 (full wire with `chain_hash`) in a follow-up.  The source
comment in `Messages.lean` states the same.

## 4. Exact theorem signatures

Names below are fully qualified.

### 4.1 Type, identity, length, key, well-formedness

```lean
LnLean.Proofs.Protocol.OpenChannelWireTargets.msgType_openChannel
  (w : OpenChannelWire) : msgType (.openChannel w) = 32

LnLean.Proofs.Protocol.OpenChannelWireTargets.kind_openChannel
  (w : OpenChannelWire) : Msg.kind (.openChannel w) = .openChannel

LnLean.Proofs.Protocol.OpenChannelWireTargets.kindOfType?_32 :
  kindOfType? 32 = some .openChannel

LnLean.Proofs.Protocol.OpenChannelWireTargets.wireType_openChannel :
  wireType .openChannel = 32

LnLean.Proofs.Protocol.OpenChannelWireTargets.msgLength_openChannel
  (w : OpenChannelWire) : msgLength (.openChannel w) = 313

LnLean.Proofs.Protocol.OpenChannelWireTargets.channelId?_openChannel
  (w : OpenChannelWire) : channelId? (.openChannel w) = some w.temporaryChannelId

LnLean.Proofs.Protocol.OpenChannelWireTargets.pubKeys_openChannel_eq
  (w : OpenChannelWire) :
  pubKeys (.openChannel w) =
    [w.fundingPubKey, w.revocationBasepoint, w.paymentBasepoint,
     w.delayedPaymentBasepoint, w.htlcBasepoint, w.firstPerCommitmentPoint]

LnLean.Proofs.Protocol.OpenChannelWireTargets.pubKeys_openChannel_length
  (w : OpenChannelWire) : (pubKeys (.openChannel w)).length = 6

LnLean.Proofs.Protocol.OpenChannelWireTargets.openChannel_injective
  {w₁ w₂ : OpenChannelWire} (h : Msg.openChannel w₁ = Msg.openChannel w₂) :
  w₁ = w₂

LnLean.Proofs.Protocol.OpenChannelWireTargets.wellFormed_openChannel_iff
  (w : OpenChannelWire) :
  wellFormed (.openChannel w) ↔
    w.temporaryChannelId.Valid ∧
      (∀ p ∈ pubKeys (.openChannel w), p.Valid)

LnLean.Proofs.Protocol.OpenChannelWireTargets.wellFormed_openChannel_channelId
  {w : OpenChannelWire} (h : wellFormed (.openChannel w)) :
  w.temporaryChannelId.Valid

LnLean.Proofs.Protocol.OpenChannelWireTargets.wellFormed_openChannel_pubKey
  {w : OpenChannelWire} (h : wellFormed (.openChannel w)) {p : PubKey}
  (hp : p ∈ pubKeys (.openChannel w)) : p.Valid

LnLean.Proofs.Protocol.OpenChannelWireTargets.openChannel_msgLength_le_65535
  (w : OpenChannelWire) : msgLength (.openChannel w) ≤ 65535
```

Six individual membership lemmas are also proved:
`fundingPubKey_mem_pubKeys`, `revocationBasepoint_mem_pubKeys`,
`paymentBasepoint_mem_pubKeys`, `delayedPaymentBasepoint_mem_pubKeys`,
`htlcBasepoint_mem_pubKeys`, `firstPerCommitmentPoint_mem_pubKeys`.

### 4.2 Projection onto `Handshake.OpenChannel`

```lean
LnLean.Protocol.OpenChannelWire.toHandshakeOpenChannel
  (w : OpenChannelWire) : OpenChannel

LnLean.Protocol.OpenChannelWire.toHandshakeOpenChannel_eq_iff
  {w₁ w₂ : OpenChannelWire} :
  w₁.toHandshakeOpenChannel = w₂.toHandshakeOpenChannel ↔
    w₁.temporaryChannelId = w₂.temporaryChannelId ∧
    w₁.fundingSatoshis = w₂.fundingSatoshis ∧
    w₁.pushMsat = w₂.pushMsat ∧
    w₁.fundingPubKey = w₂.fundingPubKey

LnLean.Proofs.Protocol.OpenChannelWireTargets.toHandshakeOpenChannel_not_injective :
  ∃ w₁ w₂ : OpenChannelWire,
    w₁ ≠ w₂ ∧ w₁.toHandshakeOpenChannel = w₂.toHandshakeOpenChannel
```

The four projection-preservation lemmas
(`toHandshakeOpenChannel_temporaryChannelId`, `_fundingSatoshis`, `_pushMsat`,
`_fundingPubKey`) are `[simp]`.

### 4.3 Funding construction

```lean
LnLean.Protocol.OpenChannelWire.toFundingNegotiation
  (w : OpenChannelWire) (a : AcceptChannel) : FundingNegotiation

LnLean.Protocol.OpenChannelWire.toFundingParams
  (H : ByteArray → ByteArray) (w : OpenChannelWire) (a : AcceptChannel) :
  FundingParams

LnLean.Protocol.OpenChannelWire.toFundingParams_hash_linked
  (H : ByteArray → ByteArray) (w : OpenChannelWire) (a : AcceptChannel) :
  FundingScriptHashLinked H (w.toFundingParams H a)

LnLean.Protocol.OpenChannelWire.toFundingParams_fundingScriptPubKey_eq_p2wsh_ordered
  (H : ByteArray → ByteArray) (w : OpenChannelWire) (a : AcceptChannel) :
  (w.toFundingParams H a).fundingScriptPubKey =
    p2wsh (H (TwoOfTwoScriptBytes (w.toFundingNegotiation a).firstFundingKey
      (w.toFundingNegotiation a).secondFundingKey))

LnLean.Proofs.Protocol.OpenChannelWireTargets.toFundingNegotiation_eq_projection
  (w : OpenChannelWire) (a : AcceptChannel) :
  w.toFundingNegotiation a =
    w.toHandshakeOpenChannel.toFundingNegotiation a

LnLean.Proofs.Protocol.OpenChannelWireTargets.toFundingParams_eq_projection
  (H : ByteArray → ByteArray) (w : OpenChannelWire) (a : AcceptChannel) :
  w.toFundingParams H a =
    w.toHandshakeOpenChannel.toFundingParams H a
```

### 4.4 `FundingPhase` end-to-end

```lean
LnLean.Proofs.Protocol.OpenChannelWireTargets.openerPhaseAfter
  (w : OpenChannelWire) (a : AcceptChannel) : FundingPhase

LnLean.Proofs.Protocol.OpenChannelWireTargets.acceptorPhaseAfter
  (w : OpenChannelWire) (a : AcceptChannel) : FundingPhase

LnLean.Proofs.Protocol.OpenChannelWireTargets.openerPhaseAfter_reachable
  (w : OpenChannelWire) (a : AcceptChannel) :
  FundingReachable (openerPhaseAfter w a)

LnLean.Proofs.Protocol.OpenChannelWireTargets.acceptorPhaseAfter_reachable
  (w : OpenChannelWire) (a : AcceptChannel) :
  FundingReachable (acceptorPhaseAfter w a)

LnLean.Proofs.Protocol.OpenChannelWireTargets.opener_acceptor_negotiation_agree
  (w : OpenChannelWire) (a : AcceptChannel) :
  (openerPhaseAfter w a).openerNegotiation? =
    (acceptorPhaseAfter w a).acceptorNegotiation?

LnLean.Proofs.Protocol.OpenChannelWireTargets.openChannelWire_end_to_end
  (H : ByteArray → ByteArray) (w : OpenChannelWire) (a : AcceptChannel) :
  FundingReachable (openerPhaseAfter w a) ∧
  FundingReachable (acceptorPhaseAfter w a) ∧
  (openerPhaseAfter w a).openerNegotiation? = some (w.toFundingNegotiation a) ∧
  (acceptorPhaseAfter w a).acceptorNegotiation? = some (w.toFundingNegotiation a) ∧
  FundingScriptHashLinked H (w.toFundingParams H a) ∧
  (w.toFundingParams H a).fundingScriptPubKey =
    p2wsh (H (TwoOfTwoScriptBytes (w.toFundingNegotiation a).firstFundingKey
      (w.toFundingNegotiation a).secondFundingKey))
```

### 4.5 Handshake and peer boundary

```lean
LnLean.Proofs.Protocol.OpenChannelWireTargets.acceptKey_bound_before_fundingCreated_wire
  {s s' : HandshakeState}
  (h : handshakeStep s .sendFundingCreated = some s')
  (w : OpenChannelWire) (a : AcceptChannel) (H : ByteArray → ByteArray) :
  s.acceptReceived = true ∧
    ((w.toFundingNegotiation a).toFundingParams H).remoteFundingKey =
      a.fundingPubKey

LnLean.Proofs.Protocol.OpenChannelWireTargets.sendEvent?_openChannel
  (w : OpenChannelWire) : sendEvent? (.openChannel w) = none

LnLean.Proofs.Protocol.OpenChannelWireTargets.receiveEvent?_openChannel
  (w : OpenChannelWire) : receiveEvent? (.openChannel w) = none

LnLean.Proofs.Protocol.OpenChannelWireTargets.send_openChannel_requires_channel
  (s : PeerState) (w : OpenChannelWire)
  (hf : findChannel s w.temporaryChannelId = none) :
  send s (.openChannel w) = none

LnLean.Proofs.Protocol.OpenChannelWireTargets.receive_openChannel_requires_channel
  (s : PeerState) (w : OpenChannelWire)
  (hf : findChannel s w.temporaryChannelId = none) :
  receive s (.openChannel w) = none
```

## 5. Build result

All builds used `LEAN_NUM_THREADS=1` and the shared
`/tmp/opencode/btc-lean/build.lock`.

| Build | Result |
|---|---|
| `lake build LnLean.Protocol.Messages` | 10 jobs, RC 0 |
| `lake build LnLean.Protocol.Laws` | 14 jobs, RC 0 |
| Scoped owned-downstream build (`Liveness`, `PersistenceRecovery`, `ErrorProps`, `ChannelReestablishProps`, `D21`) | 140 jobs, RC 0 |
| `lake build LnLean.Proofs.Protocol.OpenChannelWireTargets` | 19 jobs, RC 0 |
| Full `lake build` (real shared tree, no root import yet) | **233 jobs, RC 0** |
| Disposable clean-snapshot full build with the recommended root import simulated | **234 jobs, RC 0** |

The clean-snapshot build used `git archive HEAD`, then applied only this lane's
`Messages.lean` and new proof module, and simulated
`import LnLean.Proofs.Protocol.OpenChannelWireTargets` in the disposable
`LnLean.lean`.  This confirms there is no import cycle and no outside-file
breakage from the new constructor.  The real tree's full build was also green
after the concurrent `S8-PR-ACCEPT-PAYLOAD` edits to `Handshake.lean`
stabilized; no source outside the write set was edited by this lane.

`collect-obligations.py` and `collect-anchors.py` were not run, as instructed.

## 6. Axiom result

`#print axioms` on the headline targets (real tree, new module built):

| Target | Axioms |
|---|---|
| `...openChannelWire_end_to_end` | `[propext]` |
| `LnLean.Protocol.OpenChannelWire.toFundingParams_hash_linked` | `[propext]` |
| `...toFundingParams_fundingScriptPubKey_eq_p2wsh_ordered` | `[propext]` |
| `...wellFormed_openChannel_iff` | `[propext, Classical.choice, Quot.sound]` |
| `...pubKeys_openChannel_length` | `[propext]` |
| `...acceptKey_bound_before_fundingCreated_wire` | `[propext]` |
| `...opener_acceptor_negotiation_agree` | `[propext]` |
| `...openChannel_injective` | no axioms |

Every result is a subset of `{propext, Quot.sound, Classical.choice}`.  No
`Classical.choice` appears in the end-to-end funding target itself.

## 7. Forbidden-construct scan

Scanned the changed/new files and all owned downstream files for `sorry`,
`axiom`, `admit`, `native_decide`, `unsafe`, `@[implemented_by]`:

- `LnLean/Protocol/Messages.lean`: clean.
- `LnLean/Proofs/Protocol/OpenChannelWireTargets.lean`: clean.
- `LnLean/Protocol/Laws.lean`: clean.
- `LnLean/Proofs/Liveness.lean`: clean (only an existing docstring sentence
  saying the module contains none of these).
- `LnLean/Proofs/PhaseC3/PersistenceRecovery.lean`: clean.
- `LnLean/Proofs/Protocol/ErrorProps.lean`: clean.
- `LnLean/Proofs/Protocol/ChannelReestablishProps.lean`: clean.
- `LnLean/Proofs/WaveD/D21.lean`: clean.

No new axiom declaration, `sorry`, `admit`, `native_decide`, `unsafe`, or
`@[implemented_by]` was introduced.  The only new imports are
`LnLean.Protocol.Laws` and
`LnLean.Proofs.Bitcoin.FundingLinkTargets`, both existing modules.

## 8. End-to-end projection limits

1. **The projection forgets wire-only fields.**
   `toHandshakeOpenChannel` keeps only `temporaryChannelId`,
   `fundingSatoshis`, `pushMsat`, and `fundingPubKey`.  It is deliberately not
   injective (`toHandshakeOpenChannel_not_injective`).  Dust limit, max HTLC
   value, reserve, HTLC minimum, feerate, `to_self_delay`, max accepted HTLCs,
   `channel_flags`, and the shutdown script do not enter the funding output;
   they must be checked by policy/transport, not by the P2WSH program.

2. **No sender identity or signature.**
   The record carries no sender identity and no signature.
   `acceptKey_bound_before_fundingCreated_wire` still takes the handshake
   boundary as a hypothesis; it identifies *which message* supplied the key,
   not who sent it.  Transport attribution remains the explicit hypothesis in
   `LnLean.Proofs.Bitcoin.FundingAuthTargets` (`PR-01`/C3), and the
   `same_message_distinct_senders` counterexample is untouched.

3. **`open_channel` is not routed through `handshakeStep`.**
   `sendEvent?`/`receiveEvent?` return `none` for it, so `Peer.send`/`receive`
   treat it as a channel-directed non-handshake message.  The theorems
   `send_openChannel_requires_channel` and
   `receive_openChannel_requires_channel` show that a fresh peer with no record
   under the temporary channel id cannot send/receive it.  Wiring it into the
   ten-milestone machine requires a new payload-carrying `HandshakeEvent` (or a
   `FundingPhase` bridge in `PeerState`) and a coordinated downstream pass over
   `Peer.lean` and its proofs.  That is intentionally outside this lane.

4. **The length constant is a model convention.**
   `313` is the specified constant; the literal field sum is `321` and the
   BOLT 2 TLV/full-wire values are `323`/`355` (see §3.3).  The source comment
   and this report state the discrepancy; no byte-serialization theorem is
   claimed.  `msgLength` is constant for every `OpenChannelWire` and
   `wellFormed` does not constrain `shutdownScriptpubkey.size`; a non-34-byte
   shutdown script is therefore not rejected by the model's length predicate.
   Enforcing the standard width (or modelling the TLV) is part of the
   follow-up length decision.

5. **The finite C1 boundary is unchanged.**
   This lane did not touch `FundingAuthTargets`, `FundingScriptTargets`,
   `CollisionFreeOn`, `c1_32_does_not_bind_funding_witnessScripts`, or the
   `L1-05` finite-C1 admission.  The ordered output theorem uses the same
   `FundingLinkTargets` construction and no hash-injectivity hypothesis.

## 9. Integration steps (parent only)

1. **Root import.**  Add to `LnLean.lean` next to the other
   `LnLean.Proofs.Protocol.*` imports (alphabetically after
   `import LnLean.Proofs.Protocol.HandshakeProps`, currently line 125):

   ```lean
   import LnLean.Proofs.Protocol.OpenChannelWireTargets
   ```

   Placing it after the existing `LnLean.Proofs.Bitcoin.FundingAuthTargets`
   import also works; the module has no root-cycle.  Either placement raises
   the full build from 233 to 234 jobs.  The disposable snapshot build with
   exactly this import is green (§5).

2. **Catalog / traceability / audit registration** in the parent-owned
   `LnLean/Proofs/Obligations.lean`, `LnLean/Proofs/Traceability.lean`, and
   `LnLean/Proofs/PhaseC3/AxiomAudit.lean`.  Suggested target strings:

   ```text
   LnLean.Proofs.Protocol.OpenChannelWireTargets.openChannelWire_end_to_end
   LnLean.Protocol.OpenChannelWire.toFundingParams_hash_linked
   LnLean.Proofs.Protocol.OpenChannelWireTargets.toFundingParams_fundingScriptPubKey_eq_p2wsh_ordered
   LnLean.Proofs.Protocol.OpenChannelWireTargets.acceptKey_bound_before_fundingCreated_wire
   LnLean.Proofs.Protocol.OpenChannelWireTargets.wellFormed_openChannel_iff
   LnLean.Proofs.Protocol.OpenChannelWireTargets.pubKeys_openChannel_length
   LnLean.Proofs.Protocol.OpenChannelWireTargets.msgType_openChannel
   LnLean.Proofs.Protocol.OpenChannelWireTargets.channelId?_openChannel
   ```

   `openChannelWire_end_to_end` and `toFundingParams_hash_linked` are the
   headline targets; the others are the type/length/identity/key laws.

3. **Docs.**  Update `docs/OPEN-ISSUES.md` `L1-03` to record that
   `Msg.openChannel`/`MsgKind.openChannel` now exist, that the wire record is
   `OpenChannelWire`, and that the projection/end-to-end targets are in the new
   module.  Keep the issue open for transport attribution and handshake
   routing; record the `313` vs `321` decision.  Mark the `S8-L1-OPENCHANNEL-WIRE`
   row complete in `docs/OPEN-ISSUES.md`/`docs/WAVE-STATUS.md`.

4. **Do not add a `handshakeStep` case** without the coordinated pass in §8(3).
   The current `Peer.send`/`receive` behavior is explicitly characterized by the
   two `requires_channel` theorems.

5. **Length decision.**  Either keep `313` as a documented model convention or
   change `msgLength`/`msgLength_openChannel` and the comments to `321`
   (modelled fields), `323` (BOLT 2 TLV wrapping), or `355` (full wire with
   `chain_hash`).  No other proof depends on the exact value beyond the
   `≤ 65535` bound and `msgLength_pos`.

## 10. Blockers

- **No proof blocker for the wire patch.**  The module is sorry-free and
  axiom-clean, and the full tree builds.
- **Root/catalog/docs are parent-owned.**  This lane could not edit
  `LnLean.lean`, `Obligations.lean`, `Traceability.lean`, or `AxiomAudit.lean`;
  the exact import and suggested target strings are in §9.
- **The 313-byte constant needs a parent decision.**  The lane specification
  says 313; the six modelled 8-byte fields sum to 321.  The proof is
  definitional, so it cannot be used as a byte-fidelity claim until resolved.
- **No authentication/routing claim.**  As above, this is scope, not a missing
  proof: peer attribution is `PR-01`/C3 and handshake routing is a separate
  state-machine change.

## 11. Catalog / roadmap recommendation for `L1-03`

Recommended status: **`open (mitigated; wire coverage integrated)`**, not
`closed`.

- The wire-level gap named in the wave-7 report is now closed: `open_channel` is
  a type-32 `Msg` constructor with length/id/key laws, an explicit projection
  onto `Handshake.OpenChannel`, and a proved end-to-end `FundingPhase`
  construction.
- `L1-03` remains open because (a) the output binds only the funding-key set
  under the unchanged finite-C1 admission, (b) transport attribution is still
  an explicit hypothesis, (c) `open_channel` is not yet a `handshakeStep`
  event, and (d) the 313-byte constant is a model convention pending decision.
- If the parent wants to close the *model-layer* part of `L1-03`, the residual
  authentication/item (b) should move under `PR-01`, and items (c)/(d) should
  become explicit roadmap rows rather than being described as closed.

Suggested next-wave candidates:

1. `S9-L1-OPENCHANNEL-ROUTE` — connect `OpenChannelWire`/`FundingPhase` to
   `PeerState`/`HandshakeState` with a payload-carrying open event, preserving
   the ten-milestone invariants and proving the send/receive routing.
2. `S9-L1-OPENCHANNEL-WIREFIX` — settle the 313/321/323/355 length question and,
   if the full wire is wanted, add `chain_hash` and the TLV header explicitly.
3. Keep `PR-01`/`S8-PR-ACCEPT-PAYLOAD` as the owner of key attribution; do not
   describe `L1-03` as peer authentication even after this wire patch.
