import LnLean.Protocol.Handshake
import LnLean.Protocol.Messages

/-!
# BOLT 2 channel-establishment handshake laws

## English claim

This module states and proves the ordering and wire-shape laws of BOLT 2's
legacy (v1) channel establishment over the wave-A `HandshakeState`,
`handshakeStep`, and `Msg` models:

1. `accept_channel` is reachable only after both `init` messages have been
   exchanged.  The wave-A model has no `open_channel` constructor, so the
   `open_channel` prerequisite is absorbed into `HandshakeState.canSendAccept`;
   the strongest expressible statement is the `init` prerequisite below.
2. `funding_created` is reachable only after the corresponding
   `accept_channel`, `funding_signed` only after `funding_created`, and
   `channel_ready` only after `funding_signed`.
3. A `channel_ready` message without a prior `funding_signed` is unreachable:
   both the transition guard and every reachable state rule it out.
4. The temporary channel id is used until the funding outpoint is fixed;
   `funding_created` still carries `temporary_channel_id` on the wire, while
   `funding_signed` and `channel_ready` carry the final `channel_id`, which is
   a function of the outpoint in `funding_created`.  The handshake transition
   that first makes the outpoint known is exactly `sendFundingCreated` or
   `recvFundingCreated`.
5. Two internally consistent `FundingAgreement`s whose `channel_ready`
   messages carry the same `channel_id` agree on the funding txid.  Full
   outpoint agreement is **not** provable in this model: `finalChannelId`
   deliberately omits the big-endian XOR with `funding_output_index`, so the
   output index is erased (see `finalChannelId` and §"What is NOT modelled").
6. Each handshake message constructor has a distinct BOLT wire type, and each
   handshake payload is bounded by BOLT 1's 65535-byte framing limit under the
   stated signature/feature-size hypotheses.

## BOLT sections

* BOLT 1 §"Lightning Message Format"
  (`refs/bolts/01-messaging.md:43-92`): two-byte type and the 65535-byte
  payload bound.
* BOLT 1 §"The `init` Message" (`refs/bolts/01-messaging.md:268-330`):
  `init` is the first Lightning message.
* BOLT 2 §"Channel Establishment v1"
  (`refs/bolts/02-peer-protocol.md:629-680`): the message order
  `open_channel`, `accept_channel`, `funding_created`, `funding_signed`,
  `channel_ready`, and the sentence that `temporary_channel_id` "is replaced
  by the `channel_id`, which is derived from the funding transaction"
  (`:675-680`).
* BOLT 2 §"The `accept_channel` Message" (`02-peer-protocol.md:907-966`).
* BOLT 2 §"The `funding_created` Message" (`02-peer-protocol.md:968-1007`):
  the outpoint and the requirement that `temporary_channel_id` match
  `open_channel`.
* BOLT 2 §"The `funding_signed` Message" (`02-peer-protocol.md:1009-1044`):
  "This message introduces the `channel_id`", derived by big-endian XOR of
  `funding_txid` and `funding_output_index`.
* BOLT 2 §"The `channel_ready` Message" (`02-peer-protocol.md:1046-1136`):
  both `channel_ready` messages are required before normal operation, and the
  sender must not send it unless the funding outpoint pays the agreed script.

## rust-lightning anchors (commit fe49009)

* `lightning/src/ln/msgs.rs:371` (`AcceptChannel`), `:403`
  (`FundingCreated`: `temporary_channel_id`, `funding_txid`,
  `funding_output_index`), `:420` (`FundingSigned`: `channel_id`), `:431`
  (`ChannelReady`: `channel_id`, `next_per_commitment_point`).
* `lightning/src/ln/wire.rs:518,522,526,530`: wire types 33, 34, 35, 36.
* `lightning/src/ln/channel.rs:16006` (`accept_channel` carries
  `temporary_channel_id`), `:15580` (`funding_created` carries
  `temporary_channel_id`), `:6818` (`funding_signed` carries
  `channel_id`), `:12242` (`channel_ready` carries `channel_id`).
* `lightning/src/ln/channel.rs:15613`: the local `funding_created` transition
  sets `self.context.channel_id = ChannelId::v1_from_funding_outpoint(...)`.
* `lightning/src/ln/types.rs:42-54`: `v1_from_funding_txid` copies the txid
  and XORs the output index into the last two bytes.
* `lightning/src/ln/channelmanager.rs:12405` (`internal_accept_channel`),
  `:12449` (`internal_funding_created`), `:12686` (`internal_funding_signed`),
  `:13108` (`internal_channel_ready`); the last rejects a `channel_ready` for
  an unfunded channel.

## What is NOT modelled

* `open_channel` is not a `Msg` constructor.  The event that would enable
  `accept_channel` is the environment fact absorbed into `canSendAccept`
  (`LnLean/Protocol/Messages.lean`, "What is NOT modelled").
* There is no two-endpoint execution log and no chain view.  Agreement is
  stated over explicit `FundingAgreement` records, not derived from a
  distributed run; `FundingConfirmed`/`minimum_depth` are not modelled.
* `finalChannelId` does **not** implement BOLT 2's big-endian XOR with
  `funding_output_index`; it keeps only the txid.  Consequently two
  `funding_created` messages that differ only in output index have the same
  modelled final id, and full outpoint agreement is a recorded gap rather
  than a theorem.
* Signature validity, commitment-transaction construction, feature
  negotiation, retransmission, and timeouts are outside this module.  The
  length statements are byte counts from `Messages.msgLength`; they are not
  a decoder or serialization proof.
-/

namespace LnLean.Protocol

set_option autoImplicit false

open LnLean

/-! ## Funding outpoint and the v1 channel-id derivation -/

/-- The two BOLT 2 `funding_created` fields that identify the funding output. -/
structure FundingOutpoint where
  txid : ByteArray
  outputIndex : Nat
deriving Repr, BEq, DecidableEq

/-- The outpoint components carried by a `funding_created` message. -/
def FundingCreated.outpoint (m : FundingCreated) : FundingOutpoint :=
  ⟨m.fundingTxid, m.fundingOutputIndex⟩

/-- Model of BOLT 2's v1 `channel_id` derivation.

BOLT 2 (`02-peer-protocol.md:1015-1028`) and LDK
(`lightning/src/ln/types.rs:42-54`) derive the id by copying `funding_txid`
and XORing `funding_output_index` into its last two bytes.  The wave-A wire
model deliberately does not compute that XOR (`Messages.lean`, "What is NOT
modelled"), so this function represents only the txid component.  The output
index is retained in `FundingOutpoint` but is not observable in the returned
`ChannelId`; see `parties_agree_on_funding_txid` and the module docstring. -/
def finalChannelId (o : FundingOutpoint) : ChannelId :=
  ⟨o.txid⟩

@[simp] theorem finalChannelId_bytes (o : FundingOutpoint) :
    (finalChannelId o).bytes = o.txid := rfl

/-- The modelled final id determines the funding txid.  This is the part of
outpoint agreement that survives the omitted output-index XOR. -/
theorem finalChannelId_injective {o₁ o₂ : FundingOutpoint}
    (h : finalChannelId o₁ = finalChannelId o₂) : o₁.txid = o₂.txid := by
  have hb := congrArg ChannelId.bytes h
  simpa [finalChannelId] using hb

/-! ## Wire-level id placement -/

/-- `accept_channel` carries the temporary id. -/
theorem acceptChannel_carries_temporaryId (m : AcceptChannel) :
    channelId? (.acceptChannel m) = some m.temporaryChannelId := rfl

/-- `funding_created` still carries the temporary id; the final id is derived
from the outpoint it announces. -/
theorem fundingCreated_carries_temporaryId (m : FundingCreated) :
    channelId? (.fundingCreated m) = some m.temporaryChannelId := rfl

/-- `funding_signed` carries the final `channel_id` introduced by BOLT 2. -/
theorem fundingSigned_carries_finalId (m : FundingSigned) :
    channelId? (.fundingSigned m) = some m.channelId := rfl

/-- `channel_ready` carries the final `channel_id`. -/
theorem channelReady_carries_finalId (m : ChannelReady) :
    channelId? (.channelReady m) = some m.channelId := rfl

/-- If `funding_signed` uses the id derived from the `funding_created`
outpoint, then its wire-level channel id is exactly that derived id.  This is
the wire-level "temporary id is replaced at the funding-created step" law:
`funding_created` itself is still temporary, and the next message switches. -/
theorem fundingSigned_uses_derived_id
    (fc : FundingCreated) (fs : FundingSigned)
    (h : fs.channelId = finalChannelId fc.outpoint) :
    channelId? (.fundingSigned fs) = some (finalChannelId fc.outpoint) := by
  simp only [channelId?]
  rw [h]

/-! ## A consistent funding exchange -/

/-- The three BOLT 2 messages that carry the funding agreement. -/
structure FundingAgreement where
  created : FundingCreated
  signed : FundingSigned
  ready : ChannelReady
deriving Repr, BEq

namespace FundingAgreement

/-- `funding_signed` derives its id from the `funding_created` outpoint, and
`channel_ready` reuses that same id. -/
def consistent (a : FundingAgreement) : Prop :=
  a.signed.channelId = finalChannelId a.created.outpoint ∧
  a.ready.channelId = a.signed.channelId

/-- Every consistent agreement's `channel_ready` refers to the outpoint
announced in `funding_created`. -/
theorem ready_refers_to_outpoint (a : FundingAgreement) (h : a.consistent) :
    a.ready.channelId = finalChannelId a.created.outpoint :=
  h.2.trans h.1

/-- The `channel_ready` id carries exactly the `funding_created` txid. -/
theorem ready_same_funding_txid (a : FundingAgreement) (h : a.consistent) :
    a.ready.channelId.bytes = a.created.fundingTxid := by
  rw [ready_refers_to_outpoint a h]
  rfl

/-- Conditional form of BOLT 2 outpoint agreement: if two consistent
agreements' `channel_ready` messages carry the same final id, then both sides
used the same funding txid.  The hypothesis `hid` is the two-party link that
the single-endpoint wave-A model cannot derive. -/
theorem parties_agree_on_funding_txid
    (a b : FundingAgreement) (ha : a.consistent) (hb : b.consistent)
    (hid : a.ready.channelId = b.ready.channelId) :
    a.created.fundingTxid = b.created.fundingTxid := by
  calc
    a.created.fundingTxid = a.ready.channelId.bytes :=
      (ready_same_funding_txid a ha).symm
    _ = b.ready.channelId.bytes := by rw [hid]
    _ = b.created.fundingTxid := ready_same_funding_txid b hb

end FundingAgreement

/-! ## Strengthened handshake ordering invariant -/

/-- The full BOLT 2 v1 ordering chain, stronger than the wave-A
`HandshakeState.Inv`: each milestone implies the milestone that must precede
it, and `accept_channel` implies both `init` messages.  The individual
`funding*Sent`/`funding*Received` directions are kept separate because the
two endpoints play opposite roles. -/
def OrderInv (s : HandshakeState) : Prop :=
  ((s.acceptSent = true ∨ s.acceptReceived = true) →
    (s.initSent = true ∧ s.initReceived = true)) ∧
  (s.fundingCreatedSent = true → s.acceptReceived = true) ∧
  (s.fundingCreatedReceived = true → s.acceptSent = true) ∧
  (s.fundingSignedSent = true → s.fundingCreatedReceived = true) ∧
  (s.fundingSignedReceived = true → s.fundingCreatedSent = true) ∧
  ((s.channelReadySent = true ∨ s.channelReadyReceived = true) →
    (s.fundingSignedSent = true ∨ s.fundingSignedReceived = true))

/-- The initial state satisfies the ordering chain. -/
theorem orderInv_initial : OrderInv HandshakeState.initial := by
  simp [OrderInv, HandshakeState.initial]

/-- Every permitted handshake step preserves the ordering chain. -/
theorem handshakeStep_orderInv {s s' : HandshakeState} {e : HandshakeEvent}
    (h : OrderInv s) (hs : handshakeStep s e = some s') : OrderInv s' := by
  rcases h with ⟨hacc, hfcS, hfcR, hfsS, hfsR, hcr⟩
  cases e <;>
    simp only [handshakeStep] at hs <;>
    (try split at hs) <;>
    (try rw [Option.some.injEq] at hs) <;>
    (try rw [← hs]) <;>
    simp_all [OrderInv, HandshakeState.canSendInit,
      HandshakeState.canRecvInit, HandshakeState.canSendAccept,
      HandshakeState.canRecvAccept, HandshakeState.canSendFundingCreated,
      HandshakeState.canRecvFundingCreated,
      HandshakeState.canSendFundingSigned,
      HandshakeState.canRecvFundingSigned,
      HandshakeState.canSendChannelReady,
      HandshakeState.canRecvChannelReady]

/-- Every reachable handshake state satisfies `OrderInv`. -/
theorem reachable_orderInv {s : HandshakeState} (h : Reachable s) :
    OrderInv s := by
  induction h with
  | initial => exact orderInv_initial
  | step e _ hstep ih => exact handshakeStep_orderInv ih hstep

/-! ## Reachable-state ordering theorems -/

/-- **Corrected `accept_channel` prerequisite.**  The wave-A model has no
`open_channel` message, so the strongest expressible claim is that a sent or
received `accept_channel` implies both `init` messages were exchanged.
`open_channel` is absorbed into `canSendAccept`; this is a documented model
gap, not a proof of the `open_channel` step itself. -/
theorem accept_channel_reachable_only_after_init {s : HandshakeState}
    (h : Reachable s)
    (ha : s.acceptSent = true ∨ s.acceptReceived = true) :
    s.initSent = true ∧ s.initReceived = true :=
  (reachable_orderInv h).1 ha

/-- The direct guard form: a permitted `accept_channel` send already requires
both `init` messages (`canSendAccept`'s first conjunct). -/
theorem sendAcceptChannel_guard {s : HandshakeState}
    (h : s.canSendAccept) : s.initSent = true ∧ s.initReceived = true :=
  h.1

/-- The direct guard form for receiving `accept_channel`. -/
theorem recvAcceptChannel_guard {s : HandshakeState}
    (h : s.canRecvAccept) : s.initSent = true ∧ s.initReceived = true :=
  h.1

/-- A reachable sent `funding_created` implies `accept_channel` was received. -/
theorem fundingCreatedSent_implies_acceptReceived {s : HandshakeState}
    (h : Reachable s) (hc : s.fundingCreatedSent = true) :
    s.acceptReceived = true :=
  (reachable_orderInv h).2.1 hc

/-- A reachable received `funding_created` implies `accept_channel` was sent. -/
theorem fundingCreatedReceived_implies_acceptSent {s : HandshakeState}
    (h : Reachable s) (hc : s.fundingCreatedReceived = true) :
    s.acceptSent = true :=
  (reachable_orderInv h).2.2.1 hc

/-- A reachable sent `funding_signed` implies `funding_created` was received. -/
theorem fundingSignedSent_implies_fundingCreatedReceived {s : HandshakeState}
    (h : Reachable s) (hs : s.fundingSignedSent = true) :
    s.fundingCreatedReceived = true :=
  (reachable_orderInv h).2.2.2.1 hs

/-- A reachable received `funding_signed` implies `funding_created` was sent. -/
theorem fundingSignedReceived_implies_fundingCreatedSent {s : HandshakeState}
    (h : Reachable s) (hs : s.fundingSignedReceived = true) :
    s.fundingCreatedSent = true :=
  (reachable_orderInv h).2.2.2.2.1 hs

/-- A reachable `channel_ready` (either direction) implies a `funding_signed`
in one direction or the other. -/
theorem channelReady_implies_fundingSigned {s : HandshakeState}
    (h : Reachable s)
    (hr : s.channelReadySent = true ∨ s.channelReadyReceived = true) :
    s.fundingSignedSent = true ∨ s.fundingSignedReceived = true :=
  (reachable_orderInv h).2.2.2.2.2 hr

/-- A reachable `channel_ready` implies that the funding outpoint was fixed by
a `funding_created` in one direction or the other.  This is the
handshake-level "outpoint known before `channel_ready`" law: whichever
`funding_signed` direction enabled the ready message, the matching
`funding_created` direction is already recorded in the state. -/
theorem channelReady_implies_fundingCreated {s : HandshakeState}
    (h : Reachable s)
    (hr : s.channelReadySent = true ∨ s.channelReadyReceived = true) :
    s.fundingCreatedSent = true ∨ s.fundingCreatedReceived = true := by
  rcases channelReady_implies_fundingSigned h hr with hfs | hfs
  · exact Or.inr (fundingSignedSent_implies_fundingCreatedReceived h hfs)
  · exact Or.inl (fundingSignedReceived_implies_fundingCreatedSent h hfs)

/-- **Unreachability of a bare `channel_ready`.**  A reachable state in which
`channel_ready` has been sent or received but neither `funding_signed` flag is
set is impossible. -/
theorem no_channelReady_without_fundingSigned {s : HandshakeState}
    (h : Reachable s)
    (hr : s.channelReadySent = true ∨ s.channelReadyReceived = true)
    (hmiss : s.fundingSignedSent = false ∧ s.fundingSignedReceived = false) :
    False := by
  rcases channelReady_implies_fundingSigned h hr with hs | hs <;> simp_all

/-- The transition guard itself: a successful `sendChannelReady` event
requires `funding_signed` to have been sent or received before the step. -/
theorem sendChannelReady_requires_fundingSigned {s s' : HandshakeState}
    (h : handshakeStep s .sendChannelReady = some s') :
    s.fundingSignedSent = true ∨ s.fundingSignedReceived = true := by
  by_cases hg : s.canSendChannelReady
  · exact hg.2.1
  · simp [handshakeStep, hg] at h

/-- The receive-side counterpart of
`sendChannelReady_requires_fundingSigned`. -/
theorem recvChannelReady_requires_fundingSigned {s s' : HandshakeState}
    (h : handshakeStep s .recvChannelReady = some s') :
    s.fundingSignedSent = true ∨ s.fundingSignedReceived = true := by
  by_cases hg : s.canRecvChannelReady
  · exact hg.2.1
  · simp [handshakeStep, hg] at h

/-- A successful `sendFundingSigned` requires `funding_created` to have been
received before the step. -/
theorem sendFundingSigned_requires_fundingCreated {s s' : HandshakeState}
    (h : handshakeStep s .sendFundingSigned = some s') :
    s.fundingCreatedReceived = true := by
  by_cases hg : s.canSendFundingSigned
  · exact hg.2.2.1
  · simp [handshakeStep, hg] at h

/-- A successful `recvFundingSigned` requires `funding_created` to have been
sent before the step. -/
theorem recvFundingSigned_requires_fundingCreated {s s' : HandshakeState}
    (h : handshakeStep s .recvFundingSigned = some s') :
    s.fundingCreatedSent = true := by
  by_cases hg : s.canRecvFundingSigned
  · exact hg.2.2.1
  · simp [handshakeStep, hg] at h

/-- A successful `sendFundingCreated` requires `accept_channel` to have been
received before the step. -/
theorem sendFundingCreated_requires_acceptReceived {s s' : HandshakeState}
    (h : handshakeStep s .sendFundingCreated = some s') :
    s.acceptReceived = true := by
  by_cases hg : s.canSendFundingCreated
  · exact hg.2.2.2.1
  · simp [handshakeStep, hg] at h

/-- A successful `recvFundingCreated` requires `accept_channel` to have been
sent before the step. -/
theorem recvFundingCreated_requires_acceptSent {s s' : HandshakeState}
    (h : handshakeStep s .recvFundingCreated = some s') :
    s.acceptSent = true := by
  by_cases hg : s.canRecvFundingCreated
  · exact hg.2.2.1
  · simp [handshakeStep, hg] at h

/-! ## Exact transition that introduces the funding outpoint -/

/-- The sent `funding_created` flag can be introduced only by the
`sendFundingCreated` event.  Together with the guard theorem, this is the
step at which the funding outpoint becomes known. -/
theorem fundingCreatedSent_introduced_only_by_send
    {s s' : HandshakeState} {e : HandshakeEvent}
    (h : handshakeStep s e = some s')
    (hnew : s'.fundingCreatedSent = true) (hold : s.fundingCreatedSent = false) :
    e = .sendFundingCreated := by
  cases e <;> simp only [handshakeStep] at h <;>
    (try split at h) <;>
    (try rw [Option.some.injEq] at h) <;>
    (try rw [← h] at hnew) <;>
    simp_all

/-- The received `funding_created` flag can be introduced only by the
`recvFundingCreated` event. -/
theorem fundingCreatedReceived_introduced_only_by_recv
    {s s' : HandshakeState} {e : HandshakeEvent}
    (h : handshakeStep s e = some s')
    (hnew : s'.fundingCreatedReceived = true)
    (hold : s.fundingCreatedReceived = false) :
    e = .recvFundingCreated := by
  cases e <;> simp only [handshakeStep] at h <;>
    (try split at h) <;>
    (try rw [Option.some.injEq] at h) <;>
    (try rw [← h] at hnew) <;>
    simp_all

/-! ## Wire type uniqueness and payload bounds -/

/-- The five handshake message types are pairwise distinct.  This is checked
by `decide` on the finite list of BOLT constants. -/
theorem handshake_wireTypes_nodup :
    ([wireType .init, wireType .acceptChannel, wireType .fundingCreated,
      wireType .fundingSigned, wireType .channelReady] : List Nat).Nodup := by
  decide

/-- The exact BOLT wire types of the handshake messages. -/
theorem handshake_wireTypes_eq :
    wireType .init = 16 ∧ wireType .acceptChannel = 33 ∧
    wireType .fundingCreated = 34 ∧ wireType .fundingSigned = 35 ∧
    wireType .channelReady = 36 := by
  decide

/-- Each handshake constructor's message has its expected wire type. -/
theorem handshake_msgType_eq
    (im : InitMsg) (ac : AcceptChannel) (fc : FundingCreated)
    (fs : FundingSigned) (cr : ChannelReady) :
    msgType (.init im) = 16 ∧ msgType (.acceptChannel ac) = 33 ∧
    msgType (.fundingCreated fc) = 34 ∧ msgType (.fundingSigned fs) = 35 ∧
    msgType (.channelReady cr) = 36 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Every handshake payload fits BOLT 1's two-byte length bound under the
explicit signature and feature-size hypotheses.  The constants are the
`Messages.msgLength` totals: `init` 4 + features, `accept_channel` 270,
`funding_created` 66 + signature, `funding_signed` 32 + signature,
`channel_ready` 65 or 75 with the optional alias TLV. -/
theorem handshake_lengths_bounded
    (im : InitMsg) (ac : AcceptChannel) (fc : FundingCreated)
    (fs : FundingSigned) (cr : ChannelReady)
    (hinit : im.globalfeatures.size + im.features.size ≤ 65531)
    (hfc : fc.signature.bytes.size ≤ 73)
    (hfs : fs.signature.bytes.size ≤ 73) :
    msgLength (.init im) ≤ 65535 ∧
    msgLength (.acceptChannel ac) ≤ 65535 ∧
    msgLength (.fundingCreated fc) ≤ 65535 ∧
    msgLength (.fundingSigned fs) ≤ 65535 ∧
    msgLength (.channelReady cr) ≤ 65535 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [msgLength]
    omega
  · simp [msgLength]
  · simp [msgLength, sigLen]
    omega
  · simp [msgLength, sigLen]
    omega
  · have hcr : msgLength (.channelReady cr) ≤ 75 := by
      simp only [msgLength]
      split <;> omega
    omega

end LnLean.Protocol
