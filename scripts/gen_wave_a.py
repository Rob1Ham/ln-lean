#!/usr/bin/env python3
"""Generate the 8 wave-A agent briefs."""
import pathlib

OUT = pathlib.Path("/home/ubuntu/ln-lean-stage/agents/briefs")
OUT.mkdir(parents=True, exist_ok=True)

COMMON = """You are {name}, one of eight scaffolding agents for `ln-lean`, a Lean 4
formal model of the Lightning Network built on the existing Bitcoin L1 model.

WORKDIR: /home/ubuntu/ln-lean  (all work happens there; this is the peer box)

READ FIRST, in this order:
1. docs/AGENT-PROTOCOL.md  (binding rules)
2. docs/CHARTER.md
3. docs/ARCHITECTURE.md
4. docs/ASSUMPTIONS.md
5. LnLean/Basic/Core.lean and LnLean/Bitcoin/Seam.lean

HARD RULES
- Write ONLY the files assigned to you below. Never edit another agent's
  file, LnLean.lean, lakefile.lean, lean-toolchain, docs/{{CHARTER,
  ARCHITECTURE,ASSUMPTIONS,AGENT-PROTOCOL}}.md, refs/**, or
  vendor/btc-lean-core/** (the Bitcoin L1 proofs are read-only; do not
  modify them).
- `set_option autoImplicit false` in every file.
- Model modules must be `sorry`-free. Do not use axiom/admit/native_decide/
  unsafe/@[implemented_by]. No mathlib.
- Every file starts with a docstring: English claim, BOLT section(s),
  rust-lightning path:line anchors at commit fe49009, and what is NOT
  modelled.
- A theorem statement must entail its English claim. If a claim is false,
  prove the corrected form and record the counterexample in a comment.
- Import only LnLean.Basic.Core, LnLean.Bitcoin.Seam, and Lean core /
  Bitcoin.Data.* modules during this wave. Do not import another agent's
  new module (avoids wave-A dependency races).
- Reference implementation: refs/rust-lightning/lightning/src/...
  Reference spec: refs/bolts/*.md. Cite exact files/lines.

BUILD (exact module, shared lock, never bare `lake build`):
  export PATH=/dev/shm/btc/elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
  cd /home/ubuntu/ln-lean
  flock -w 900 /tmp/ln-build.lock lake build LnLean.Your.Module

COMMIT (shared git lock):
  cd /home/ubuntu/ln-lean
  MSG="[{name}] <short description>" ./scripts/agent-commit.sh {name} <your paths...>

REPORT: agents/reports/{name}.md must contain (1) files + exact build RC,
(2) declaration table: name | statement | proved/obligation, (3) anchors,
(4) what remains open and the next smallest step, (5) reproduce commands.
Commit the report with your files. A report must not claim anything that is
not in the tree.

FINAL MESSAGE: <= 10 lines. Files, build RC, theorem count, obligations,
anything the integrator must merge.

MISSION
{body}
"""

BRIEFS = {}

BRIEFS["A1"] = """
Own: LnLean/Bitcoin/Funding.lean, LnLean/Bitcoin/ScriptTemplates.lean,
LnLean/Bitcoin/Laws.lean. (docs/SCOPE.md already exists; read it, do not
rewrite it unless a factual correction is needed.)

Build the L1 seam that every channel proof depends on:
- Funding.lean: `FundingParams` (funding satoshis, push msat, channel keys),
  `witnessScript` for the 2-of-2 funding output, `fundingScriptPubKey`,
  `FundingOutput`, `FundingConfirmed` predicate, `fundingOutpoint`.
  Distinguish temporary channel id from final channel id.
- ScriptTemplates.lean: BOLT 3 commitment output templates: `to_local`
  (revocation key + CSV), `to_remote` (payment key), `offered_htlc`,
  `received_htlc` (payment hash, CLTV, counterparty key), anchor output,
  and the mutual-close output. Model scripts as `Bitcoin.Data.Script`
  values built from byte templates. Include `scriptPubKey` functions and
  `commitmentOutputs` for a commitment with zero HTLCs.
- Laws.lean: prove the structural facts the model needs: P2WSH/P2WPKH/P2TR
  sizes, anchor value 330, funding output value within MoneyRange, distinct
  script tags/constructors for the output kinds, and `fundingOutpoint`
  index projection. Keep proofs small (`simp`, `rfl`, `decide`, `omega`).

At least 12 named declarations and 5 proved theorems. If a property is
interesting but needs an L1 semantic bridge (e.g. "this script is spendable
by the 2-of-2"), state it as a `def ... : Prop` with a docstring naming the
missing bridge; do not fake it.

Anchors: BOLT 3 sections 2-3; rust-lightning
lightning/src/ln/chan_utils.rs (commitment script builders),
lightning/src/ln/channel.rs (funding negotiation).
"""

BRIEFS["A2"] = """
Own: LnLean/Crypto/Model.lean, Hash.lean, Sig.lean, Noise.lean,
LnLean/Wire/BigSize.lean, TLV.lean, Message.lean.

Build the primitive interface and BOLT 1 framing:
- Crypto/Model.lean: a `PrimitiveModel` structure with `sha256`, `hash160`,
  `ecdsaVerify`, `schnorrVerify`, `ecdh`, `hkdf`, `aeadSeal`, `aeadOpen`,
  `hmacSha256`, plus assumed properties as `Prop` fields (no axioms):
  `CollisionResistant`, `PreimageResistant`, `EufCma`, `AeadIndCca`,
  `HmacPrf`. Define `digest32`, `paymentHashOf`, `commitmentSeed`.
- Crypto/Hash.lean: hash-lock predicate `opensTo ph pre` (defined via the
  model's sha256), collision-resistance interface, and the statement that a
  payment hash commits to a preimage. Prove structural lemmas (length,
  decidability); the cryptographic direction stays conditional.
- Crypto/Sig.lean: `verifyFunding`, `verifyCommitment`, `verifyClose`,
  signature domain separation tags, and an `AssumesEufCma` predicate.
- Crypto/Noise.lean: `NoiseState`, `HandshakePattern`, `transportEncrypt`,
  `transportDecrypt`; model the authenticated channel as an interface.
- Wire/BigSize.lean: BOLT 1 BigSize encode/decode over `ByteArray`/`Nat`;
  prove canonical-encoding bounds (`< 0xfd`, `<= 0xffff`, `<= 0xffffffff`),
  encoded length bounds, and `decode(encode n) = some n` if tractable.
- Wire/TLV.lean: `TLVRecord`, `TLVStream`, sorted/unique predicates,
  `decodeTLV`, `encodeTLV`; prove uniqueness of types and canonical order.
- Wire/Message.lean: `MessageType` (u16), `WireMessage` framing with length,
  `frame`/`unframe`, max message size, and type-255 extension rule.

At least 25 named declarations and 8 proved structural theorems. The AEAD
and signature correctness statements must be conditional on the model's
assumption fields, never asserted.

Anchors: BOLT 1 (wire framing, BigSize, TLV), BOLT 8 (Noise);
rust-lightning/lightning/src/ln/msgs.rs,
lightning/src/util/ser.rs, lightning/src/ln/peer_channel_encryptor.rs.
"""

BRIEFS["A3"] = """
Own: LnLean/Channel/Types.lean, State.lean, Commitment.lean, Fee.lean,
LnLean/Channel/Laws.lean.

Build the channel state machine and commitment arithmetic:
- Types.lean: `ChannelParams` (dust limit, reserve, to_self_delay,
  max_htlc_value, htlc_minimum, feerate), `Endpoint`, `Channel`
  (channel id, funding outpoint, phase, commitment numbers, balances,
  HTLC list), `Balance`, `CommitmentPair`, `Commitment`.
- State.lean: BOLT 2 lifecycle `ChannelPhase` transitions as an inductive
  relation `Step : Channel -> ProtocolEvent -> Channel -> Prop` covering
  open/accept/funding_signed/funding_locked/commitment_signed/revoke_and_ack/
  shutdown/closing_signed. Include `Reachable` (reflexive-transitive
  closure). Model invalid transitions as unprovable, not as a Boolean
  "reject" that hides them.
- Commitment.lean: `commitmentOutputs` (to_local, to_remote, HTLC outputs,
  anchors), `commitmentWeight` from BOLT 3 constants, `commitmentFee`,
  `totalOutputValue`, and the local/remote asymmetry.
- Fee.lean: `feeForWeight`, `feeSufficient`, `updateFee`, dust and reserve
  checks; prove monotonicity of fee in feerate and weight.
- Laws.lean: at least 6 proved theorems: zero-HTLC conservation
  (`sum outputs + fee = funding`), fee monotonicity, commitment number
  increments only on a valid step, phase progression, and reserve
  non-negativity. Use explicit hypotheses; `omega`/`simp` only.

At least 30 declarations. Keep the transition relation honest: do not
collapse distinct BOLT messages into one event if their effects differ.

Anchors: BOLT 2 sections 2-3, BOLT 3 section 2; rust-lightning
lightning/src/ln/channel.rs (channel state), channelmanager.rs,
lightning/src/ln/chan_utils.rs (fees, weights).
"""

BRIEFS["A4"] = """
Own: LnLean/Channel/HTLC.lean, Revocation.lean, Penalty.lean,
LnLean/Channel/HTLCLaws.lean.

Build the HTLC, revocation, and penalty model:
- HTLC.lean: `HTLC` (id, direction, amount msat, payment hash, cltv expiry,
  state), `HTLCState` lifecycle, `addHTLC`, `fulfillHTLC`, `failHTLC`,
  `timeoutHTLC`, `htlcOutputValue`, `isDust`, `htlcSet`.
- Revocation.lean: `PerCommitmentSecret`, `PerCommitmentPoint`,
  `RevocationKey`, `deriveRevocationPubkey` (opaque function + spec),
  `commitmentSeed`, `revocationSecret`, `isRevoked`, and the storage model
  for the last 2^48 secrets. Model the BOLT 3 shachain-style derivation as
  an abstract function with an injectivity/efficiency interface; do not
  pretend to implement the full shachain.
- Penalty.lean: `PenaltyTx` (inputs = both old outputs, outputs = one
  sweep), `penaltyValid` predicate, `breachDetected`, `punishable`.
  State the two penalty obligations as `Prop`s: every old commitment is
  punishable given its revocation secret and a timely L1 confirmation, and
  a punished commitment cannot also be spent by the breacher.
- HTLCLaws.lean: at least 8 proved structural theorems: fulfill requires a
  32-byte preimage, state transitions are acyclic in the expected order,
  amount is within the channel's max_htlc_value, CLTV is bounded, dust
  HTLCs have no output, and revocation secret length is 32.

At least 25 declarations. Cryptographic soundness (preimage, signature)
must be conditional, not asserted. If you need an L1 script-execution
bridge for the penalty statement, define the predicate and name the bridge.

Anchors: BOLT 2 sections 5.1-5.3, BOLT 3 sections 3-5, BOLT 5;
rust-lightning lightning/src/ln/chan_utils.rs,
lightning/src/ln/channel.rs (HTLC state, revocation storage).
"""

BRIEFS["A5"] = """
Own: LnLean/Protocol/Handshake.lean, Peer.lean, Messages.lean,
LnLean/Protocol/Laws.lean.

Build the BOLT 1/2 peer protocol model:
- Messages.lean: an inductive `Msg` covering `init`, `accept_channel`,
  `funding_created`, `funding_signed`, `channel_ready`, `shutdown`,
  `closing_signed`, `update_add_htlc`, `update_fulfill_htlc`,
  `update_fail_htlc`, `commitment_signed`, `revoke_and_ack`,
  `channel_reestablish`, `ping`, `pong`, `error`, `warning`. Include
  `msgType : Msg -> Nat`, `msgLength`, `wellFormed : Msg -> Prop`.
- Handshake.lean: `HandshakeState` (init sent/received, accept sent/received,
  funding created/signed, ready), `handshakeStep`, and the BOLT 2 ordering
  constraints. Model `channel_reestablish` fields: next_commitment_number,
  next_revocation_number, your_last_per_commitment_secret,
  my_current_per_commitment_point.
- Peer.lean: `PeerState` (identity, transport state, channels), `send`,
  `receive`, `resend`; model message loss/reordering as a relation, not a
  queue with hidden reliability.
- Laws.lean: at least 8 proved structural theorems: `msgType` injective on
  constructors, message length non-negative/bounded, `channel_ready` cannot
  precede `funding_signed`, reestablish numbers are monotone in the model,
  and every `Msg` has a unique wire type. Do not claim transport
  authentication; that is the Noise interface.

At least 30 declarations. Keep field names close to BOLT 2; cite the exact
message sections.

Anchors: BOLT 1 (message framing, ping/pong, error), BOLT 2 sections 2-4;
rust-lightning lightning/src/ln/msgs.rs,
lightning/src/ln/channelmanager.rs (reestablish handling).
"""

BRIEFS["A6"] = """
Own: LnLean/Routing/Graph.lean, Gossip.lean, Onion.lean, Route.lean,
LnLean/Routing/Laws.lean.

Build BOLT 4/7 routing and onion:
- Graph.lean: `NodeId`, `ChannelEdge` (short_channel_id, node ids, capacity,
  fees, cltv_delta, enabled), `Graph` as a finite map/list, `neighbors`,
  `findEdge`, `simplePaths`.
- Gossip.lean: `ChannelAnnellation` (announcement), `ChannelUpdate`,
  `NodeAnnouncement`, `GossipMessage`, signature predicates, timestamp
  monotonicity, and `applyGossip`.
- Route.lean: `Hop` (node, short_channel_id, fee_msat, cltv_delta),
  `Route` (hops, total amount, total fee, total cltv), `constructRoute`,
  `routeValid`; prove fee and CLTV accumulation laws.
- Onion.lean: `OnionHop`, `OnionPacket` (version, ephemeral key, routing
  info, HMAC), `peel`, `OnionPayload` (forward/final), `OnionError`.
  Model the Sphinx construction at the interface level: `sealLayer`,
  `openLayer`, and integrity conditional on HMAC. Prove structural bounds:
  layer count = hop count, payload sizes bounded, terminal detection.
- Laws.lean: at least 8 proved theorems: route non-empty, total fee =
  sum of hop fees, CLTV strictly increases, edge lookup soundness, gossip
  timestamp monotonicity, onion layer count, and error packet size bound.

At least 30 declarations. Do not assert onion privacy or HMAC security;
state them as named assumptions/interfaces.

Anchors: BOLT 4 (onion), BOLT 7 (gossip); rust-lightning
lightning/src/routing/gossip.rs, lightning/src/ln/onion_payment.rs,
lightning/src/ln/onion_utils.rs, lightning/src/routing/router.rs.
"""

BRIEFS["A7"] = """
Own: LnLean/Payment/Invoice.lean, HTLC.lean, MPP.lean,
LnLean/Payment/Laws.lean.

Build the payment and invoice layer:
- Invoice.lean: `Invoice` (network, amount msat option, payment hash,
  timestamp, expiry, description, payee, features, signature), `verify`
  predicate, `isExpired`, `amountSatisfies`, and BOLT 11 field tags.
- HTLC.lean: `PaymentSession` (payment hash, target amount, parts, state),
  `PaymentPart`, `PaymentState` (pending/succeeded/failed), `settle`.
- MPP.lean: `MPPPart` (channel, amount, cltv), `MPPPlan`, `sumParts`,
  `mppComplete`, `mppAtomic` (all parts succeed or all fail), and the
  `payment_secret` binding.
- Laws.lean: at least 8 proved theorems: invoice payment hash is 32 bytes,
  amount within Msat.MAX, expiry monotonicity, MPP part sum equals target
  when complete, no part exceeds target, payment secret binding is
  injective on the modeled field, and settle is idempotent.

At least 25 declarations. Do not model BOLT 11 bech32 encoding; that is a
future encoding obligation. Keep the payment hash/preimage relation
conditional on Crypto.Model where needed.

Anchors: BOLT 11 (invoice), BOLT 4 (final payload), BOLT 2 (payment
secret); rust-lightning lightning-invoice/src/lib.rs,
lightning/src/ln/outbound_payment.rs,
lightning/src/ln/inbound_payment.rs.
"""

BRIEFS["A8"] = """
Own: LnLean/Security/Model.lean, LnLean/Security/Invariants.lean,
LnLean/Proofs/Obligations.lean, docs/THEOREM-INDEX.md,
docs/TRACEABILITY.md, docs/ROADMAP.md.

Build the security model and the obligation catalog:
- Security/Model.lean: `Adversary` capabilities (network schedule,
  corruption, on-chain reorg, fee spikes), `SecurityGame`, `Winning`
  predicate, and `Assumption` records matching docs/ASSUMPTIONS.md C1-C8.
- Security/Invariants.lean: an `Invariant` structure (id, English claim,
  Lean predicate, anchor list) and the catalog of the protocol's core
  invariants: value conservation, no double spend, HTLC preimage, timeout
  safety, revocation/penalty, state monotonicity, route well-formedness,
  invoice consistency, MPP atomicity, liveness under partial synchrony.
- Proofs/Obligations.lean: `Obligation` structure (id, domain, claim,
  leanTarget, status, boltdoc, rlAnchor) and a `def obligations : List
  Obligation` with at least 40 entries covering all eight domains. Use
  `status := .statementOnly` for entries without a theorem. Do not use
  `sorry` in Security/*.lean; Proofs/Obligations.lean may contain theorem
  statements with `sorry` only with `-- OBLIGATION: LN-...` markers.
- docs/THEOREM-INDEX.md: table of the obligations with id, domain, claim,
  target module/declaration, status. State clearly that this is the
  scaffold index and wave B will add declarations.
- docs/TRACEABILITY.md: table id | BOLT section | rust-lightning
  path:line | Lean target | status. At least 40 rows.
- docs/ROADMAP.md: phase C plan: which obligations need mathlib, which
  need an L1 script bridge, which are crypto assumptions, and a suggested
  order of attack (conservation -> HTLC -> revocation -> routing ->
  liveness).

The catalog must be internally consistent: every id in the Lean list must
appear in both docs, and vice versa. Do not invent anchors; open
refs/rust-lightning and refs/bolts and cite real files/lines. If you cannot
find an anchor, mark it `UNANCHORED` honestly.

Anchors: all BOLTs; rust-lightning lightning/src/ln/channel.rs,
channelmanager.rs, chan_utils.rs, onion_payment.rs, routing/gossip.rs,
lightning-invoice/src/lib.rs.
"""

for name, body in BRIEFS.items():
    text = COMMON.format(name=name, body=body.strip())
    (OUT / f"{name}.md").write_text(text, encoding="utf-8")
    print(name, len(text))
