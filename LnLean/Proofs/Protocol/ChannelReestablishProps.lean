import LnLean.Protocol.Peer
import LnLean.Channel.State

/-!
# LnLean.Proofs.Protocol.ChannelReestablishProps

## English claim

This module proves the reconnection/retransmission laws of BOLT 2 §"Message
Retransmission" over the wave-A model:

1. **Counter monotonicity.**  Along any finite sequence of
   `commitment_signed` / `revoke_and_ack` receipts (`ReestablishTrace`), the
   reported `next_commitment_number` and `next_revocation_number` are
   non-decreasing, and BOLT 2's consistency condition
   `next_revocation_number ≤ next_commitment_number` is preserved.
2. **A reestablish never moves a channel backwards.**  Receiving a
   `channel_reestablish` leaves the channel record's counters unchanged
   (`ChannelRecord.advanceReceived` is the identity on that message), and
   every later receipt is monotone.  The same statement is transported to
   `Channel.localCommitmentNumber` / `Channel.remoteCommitmentNumber` through
   the proposed bridge `countersOf`.
3. **Retransmission is counter-stable.**  Sending (and hence re-sending) a
   retained `commitment_signed` or `revoke_and_ack` does not advance either
   reported counter.  Only the receipt of a *new* `commitment_signed`
   advances `next_commitment_number`, and only a `revoke_and_ack` that is
   strictly behind the commitment counter advances
   `next_revocation_number` (the acknowledgement).
4. **`channel_ready` retransmission.**  At the BOLT 2 condition
   (`next_commitment_number = 1` on both sides) the retained `channel_ready`
   is exactly what `PeerState.resend` returns; after the channel is
   acknowledged (a commitment beyond number 1) that condition is false.
5. **Data-loss-protect fields.**  The two proof fields are present on every
   modelled `channel_reestablish`; the secret is required to be all zeroes
   exactly at `next_revocation_number = 0`.  The link to
   `Msg.semanticOk` / `Msg.wellFormed` is proved definitionally.
6. **Acceptance predicate.**  `ReestablishAccepted` is a `Prop` (not a
   `Bool`) spelling out BOLT 2's window: the peer's `next_commitment_number`
   must be our last sent commitment number or one greater, likewise for
   `next_revocation_number`, a lost `revoke_and_ack` may not be re-sent after
   `closing_signed`, and the counters must be consistent.  Stale, future,
   zero, and inconsistent reports are rejected.

## BOLT sections

* BOLT 2 §"Message Retransmission" (`refs/bolts/02-peer-protocol.md:3352`),
  message layout and counter semantics (`:3374-3395`), sender requirements
  (`:3449-3460`), the receiver decision table (`:3483-3517`), and the
  rationale that `next_commitment_number` starts at 1 and `channel_ready` is
  implicitly acknowledged by normal operation (`:3607-3616`).
* BOLT 2 §"The `channel_ready` Message" (`02-peer-protocol.md:1045-1048`):
  `channel_ready` is the current name of `funding_locked`.
* BOLT 1 §"Lightning Message Format" (`01-messaging.md:43-92`): two-byte
  type, four-byte type/length framing (`Msg.msgType`, `Msg.msgLength`).

## rust-lightning anchors (commit fe4900930c6bd5786ec4203274d7cf312776a5a6)

* `lightning/src/ln/channel.rs:10826` `Channel::channel_reestablish`;
  `:10845-10848` rejects `next_local_commitment_number = 0` and values
  `≥ INITIAL_COMMITMENT_NUMBER`.
* `lightning/src/ln/channel.rs:11088-11112` `required_revoke`: an inbound
  `next_remote_commitment_number` equal to `our_commitment_transaction`
  means no `revoke_and_ack` is owed; equal to one less means re-send the last
  one; anything else is a channel failure.
* `lightning/src/ln/channel.rs:11126-11134`
  `both_sides_on_initial_commitment_number`: `channel_ready` is re-sent only
  when both sides report `next_commitment_number = 1`.
* `lightning/src/ln/channel.rs:11187-11294` accepts
  `next_local_commitment_number` equal to the next counterparty commitment
  number or one less (reusing the same commitment number), and rejects
  older/future values.
* `lightning/src/ln/channel.rs:13135-13186` `get_channel_reestablish`:
  `next_local_commitment_number` is the next `commitment_signed` expected,
  `next_remote_commitment_number` the next `revoke_and_ack` expected;
  `:13147-13159` fills `your_last_per_commitment_secret`, using all zeroes
  when there is no previous secret.
* `lightning/src/ln/msgs.rs:939-960` `ChannelReestablish` field list.

## What is NOT modelled

* The wire encoding of the two counters (both are `u64` in BOLT 2 and `Nat`
  here); only `Msg.semanticOk`'s 48-bit bound is retained.  The model's
  `ReestablishFields.initial` starts at 0, while BOLT 2's rationale says the
  first reported `next_commitment_number` is 1 (`02-peer-protocol.md:3560`);
  the shift is a wave-A modelling choice recorded in `agents/reports/B18.md`.
* `DataLossProtect` is not an optional TLV in the pinned BOLT text: the two
  fields are mandatory in `channel_reestablish`.  The model therefore states
  presence of the fields rather than presence/absence of a TLV, and it does
  not prove that a secret received at index `k > 0` is non-zero (that would
  need the hash/secret assumptions C1/C6).  The exactness direction is
  available only conditionally (`dataLossSecretExact_of_lastSecret`).
* **Duplicate detection.**  `Msg.commitmentSigned` carries no commitment
  number, so `ChannelRecord.advanceReceived` cannot distinguish a fresh
  message from a retransmission; it advances on every receipt
  (`duplicate_commitmentSigned_advances_twice`).  `advanceReceivedNumbered`
  is a proved *refinement* showing the intended idempotent behaviour, not the
  wave-A model.
* The received `channel_reestablish` counters are not stored by
  `PeerState.receive`, so BOLT 2's "both sides report 1" test needs the
  explicit `ReconnectView` parameter.  `receive` also has no error/close
  result: rejection is the proposition `ReestablishRejected`, not a state
  transition.  Neither `PeerState` nor `Channel` has an error phase, so
  "fail the channel" is not modelled.
* `shutdown`/`closing_signed` retransmission, `next_funding`,
  `my_current_funding_locked`, `announcement_signatures`, and splicing are
  out of scope (`docs/ASSUMPTIONS.md` §3, two-party non-splicing channels).
-/

namespace LnLean.Proofs.Protocol

set_option autoImplicit false

open LnLean
open LnLean.Protocol
open LnLean.Channel

/-! ## 1. The reestablish counters are monotone across a reconnect -/

/-- Reflexive-transitive closure of `ReestablishStep`: any finite sequence of
`commitment_signed` / `revoke_and_ack` receipts between two reconnects. -/
inductive ReestablishTrace : ReestablishFields → ReestablishFields → Prop where
  | refl (r : ReestablishFields) : ReestablishTrace r r
  | step {a b c : ReestablishFields} :
      ReestablishTrace a b → ReestablishStep b c → ReestablishTrace a c

/-- `next_commitment_number` never decreases along a reestablish trace. -/
theorem reestablishTrace_commitment_monotone {a b : ReestablishFields}
    (h : ReestablishTrace a b) :
    a.nextCommitmentNumber ≤ b.nextCommitmentNumber := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ hs ih =>
      cases hs with
      | commitment _ =>
          exact Nat.le_trans ih (ReestablishFields.nextCommitment_le_afterCommitment _)
      | revocation _ =>
          exact Nat.le_trans ih
            (Nat.le_of_eq (by simp [ReestablishFields.afterRevocation]))

/-- `next_revocation_number` never decreases along a reestablish trace. -/
theorem reestablishTrace_revocation_monotone {a b : ReestablishFields}
    (h : ReestablishTrace a b) :
    a.nextRevocationNumber ≤ b.nextRevocationNumber := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ hs ih =>
      cases hs with
      | commitment _ =>
          exact Nat.le_trans ih
            (Nat.le_of_eq (by simp [ReestablishFields.afterCommitment]))
      | revocation _ =>
          exact Nat.le_trans ih (ReestablishFields.nextRevocation_le_afterRevocation _)

/-- BOLT 2's consistency condition survives every reestablish step: a
`revoke_and_ack` never gets ahead of the commitment it acknowledges. -/
theorem reestablishTrace_consistent {a b : ReestablishFields}
    (h : ReestablishTrace a b) (ha : a.consistent) : b.consistent := by
  induction h with
  | refl => exact ha
  | step _ hs ih =>
      cases hs with
      | commitment _ => exact ReestablishFields.afterCommitment_consistent ih
      | revocation hlt => exact ReestablishFields.afterRevocation_consistent ih hlt

/-! ## 2. A reestablish message never rewinds the channel -/

/-- Receiving a `channel_reestablish` is the identity on a channel record:
its counters are read, never applied.  This is the structural core of "a
reestablish never moves a channel to an earlier commitment". -/
@[simp] theorem advanceReceived_channelReestablish (c : ChannelRecord)
    (m : ChannelReestablish) :
    (c.advanceReceived (.channelReestablish m)).reestablish = c.reestablish := rfl

/-- A non-`commitment_signed` receipt does not move `next_commitment_number`. -/
theorem advanceReceived_nextCommitment_of_ne (c : ChannelRecord) (m : Msg)
    (hk : m.kind ≠ .commitmentSigned) :
    (c.advanceReceived m).reestablish.nextCommitmentNumber =
      c.reestablish.nextCommitmentNumber := by
  unfold ChannelRecord.advanceReceived
  split <;> simp_all [Msg.kind, ReestablishFields.afterRevocation]
  all_goals split <;> simp_all

/-- A non-`revoke_and_ack` receipt does not move `next_revocation_number`. -/
theorem advanceReceived_nextRevocation_of_ne (c : ChannelRecord) (m : Msg)
    (hk : m.kind ≠ .revokeAndAck) :
    (c.advanceReceived m).reestablish.nextRevocationNumber =
      c.reestablish.nextRevocationNumber := by
  unfold ChannelRecord.advanceReceived
  split <;> simp_all [Msg.kind, ReestablishFields.afterCommitment]
  all_goals split <;> simp_all [Msg.kind, ReestablishFields.afterCommitment]

/-- A receipt never lowers `next_commitment_number`. -/
theorem advanceReceived_nextCommitment_ge (c : ChannelRecord) (m : Msg) :
    c.reestablish.nextCommitmentNumber ≤
      (c.advanceReceived m).reestablish.nextCommitmentNumber := by
  cases m with
  | commitmentSigned x =>
      simp [ChannelRecord.advanceReceived, Msg.kind, ReestablishFields.afterCommitment]
  | revokeAndAck x =>
      by_cases h : c.reestablish.nextRevocationNumber < c.reestablish.nextCommitmentNumber
      · simp [ChannelRecord.advanceReceived, Msg.kind, ReestablishFields.afterRevocation, h]
      · simp [ChannelRecord.advanceReceived, Msg.kind, h]
  | _ => simp [ChannelRecord.advanceReceived, Msg.kind]

/-- A receipt never lowers `next_revocation_number`. -/
theorem advanceReceived_nextRevocation_ge (c : ChannelRecord) (m : Msg) :
    c.reestablish.nextRevocationNumber ≤
      (c.advanceReceived m).reestablish.nextRevocationNumber := by
  cases m with
  | revokeAndAck x =>
      by_cases h : c.reestablish.nextRevocationNumber < c.reestablish.nextCommitmentNumber
      · simp [ChannelRecord.advanceReceived, Msg.kind, ReestablishFields.afterRevocation, h]
      · simp [ChannelRecord.advanceReceived, Msg.kind, h]
  | _ => simp [ChannelRecord.advanceReceived, Msg.kind, ReestablishFields.afterCommitment]

/-- Any channel-directed message receipt is monotone in both reported
counters; in particular the receipt of a `channel_reestablish` (which is the
identity) is not an exception. -/
theorem advanceReceived_counters_monotone (c : ChannelRecord) (m : Msg) :
    c.reestablish.nextCommitmentNumber ≤
        (c.advanceReceived m).reestablish.nextCommitmentNumber ∧
      c.reestablish.nextRevocationNumber ≤
        (c.advanceReceived m).reestablish.nextRevocationNumber :=
  ⟨advanceReceived_nextCommitment_ge c m, advanceReceived_nextRevocation_ge c m⟩

/-- A list-level lookup lemma: mapping a list by a function that fixes every
element failing the predicate, and sends the found element to a value still
satisfying the predicate, preserves the lookup result. -/
private theorem List.find?_map_of_find?_eq_some {α : Type} (l : List α)
    (p : α → Bool) (g : α → α)
    (hoff : ∀ x, p x = false → g x = x)
    (c : α) (h : l.find? p = some c) (hon : p (g c) = true) :
    (l.map g).find? p = some (g c) := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
      by_cases ha : p a = true
      · have hac : a = c := by
          simpa [ha] using h
        subst c
        simp [hon]
      · have haf : p a = false := by
          simpa using ha
        have hg : g a = a := hoff a haf
        have htail : l.find? p = some c := by
          simpa [haf] using h
        calc
          ((a :: l).map g).find? p = (a :: l.map g).find? p := by
            rw [List.map_cons, hg]
          _ = (l.map g).find? p := by simp [haf]
          _ = some (g c) := ih htail

/-- Looking up a channel after `updateChannel` returns the updated record,
provided the update preserves the channel identifier of the found channel. -/
private theorem findChannel_updateChannel_of_channelId
    (s : PeerState) (cid : ChannelId) (f : ChannelRecord → ChannelRecord)
    (c : ChannelRecord) (h : findChannel s cid = some c)
    (hf : (f c).channelId = c.channelId) :
    findChannel (updateChannel s cid f) cid = some (f c) := by
  unfold findChannel updateChannel
  change (s.channels.map
      (fun x => if x.channelId == cid then f x else x)).find?
      (fun x => x.channelId == cid) = some (f c)
  have h' : s.channels.find? (fun x => x.channelId == cid) = some c := by
    simpa [findChannel] using h
  have hp : (c.channelId == cid) = true :=
    List.find?_some (p := fun x => x.channelId == cid) (a := c) h'
  have hgc : (if c.channelId == cid then f c else c) = f c := by simp [hp]
  have hmain := List.find?_map_of_find?_eq_some
      (l := s.channels) (p := fun x => x.channelId == cid)
      (g := fun x => if x.channelId == cid then f x else x)
      (by intro x hx; simp [hx]) c h' (by simp [hp, hf])
  simpa [hgc] using hmain

/-- A receipt never changes a channel's identifier. -/
private theorem advanceReceived_channelId (c : ChannelRecord) (m : Msg) :
    (c.advanceReceived m).channelId = c.channelId := by
  unfold ChannelRecord.advanceReceived
  split <;> (try split) <;> rfl

/-- The branch of `receive` taken by a non-handshake channel message. -/
private theorem receive_of_no_event
    (s s' : PeerState) (m : Msg) (cid : ChannelId) (c : ChannelRecord)
    (hrecv : receive s m = some s')
    (he : receiveEvent? m = none) (hc : channelId? m = some cid)
    (hf : findChannel s cid = some c) :
    s' = updateChannel s cid (fun _ => c.advanceReceived m) := by
  unfold receive at hrecv
  cases ht : s.transport <;> simp [ht, he, hc, hf] at hrecv
  exact hrecv.symm

/-- The branch of `receive` taken by a handshake message. -/
private theorem receive_of_event
    (s s' : PeerState) (m : Msg) (e : HandshakeEvent) (hs : HandshakeState)
    (hrecv : receive s m = some s')
    (he : receiveEvent? m = some e)
    (hstep : handshakeStep s.handshake e = some hs) :
    s' = { s with handshake := hs } := by
  unfold receive at hrecv
  cases ht : s.transport <;> simp [ht, he, hstep] at hrecv
  exact hrecv.symm

/-- **Reestablish receipt law.**  If `receive` accepts a
`channel_reestablish`, then the counters of the addressed channel are exactly
those it had before, hence not earlier. -/
theorem receive_channelReestablish_preserves_counters
    (s s' : PeerState) (m : ChannelReestablish) (c : ChannelRecord)
    (hrecv : receive s (.channelReestablish m) = some s')
    (hfind : findChannel s m.channelId = some c) :
    ∃ c', findChannel s' m.channelId = some c' ∧ c'.reestablish = c.reestablish := by
  have he : receiveEvent? (.channelReestablish m) = none := rfl
  have hc : channelId? (.channelReestablish m) = some m.channelId := rfl
  have hs' := receive_of_no_event s s' (.channelReestablish m) m.channelId c hrecv he hc hfind
  rw [hs']
  refine ⟨c.advanceReceived (.channelReestablish m), ?_, ?_⟩
  · exact findChannel_updateChannel_of_channelId s m.channelId
      (fun _ => c.advanceReceived (.channelReestablish m)) c hfind
      (advanceReceived_channelId c (.channelReestablish m))
  · exact advanceReceived_channelReestablish c m

/-! ## 3. Retransmission does not advance the counters -/

/-- Sending any message only updates the retained outbound copy; the
reestablish counters are untouched. -/
@[simp] theorem recordSent_reestablish (c : ChannelRecord) (m : Msg) :
    (c.recordSent m).reestablish = c.reestablish := by
  unfold ChannelRecord.recordSent
  split <;> rfl

/-- Outbound activity while waiting for one acknowledgement kind
`excluded`: retransmissions (retaining a message) and receipts of any other
message.  `OutboundActivity .commitmentSigned` is the interval between sending
a `commitment_signed` and receiving the next one; `OutboundActivity
.revokeAndAck` is the interval before the revocation acknowledgement. -/
inductive OutboundActivity (excluded : MsgKind) : ChannelRecord → ChannelRecord → Prop where
  | refl (c : ChannelRecord) : OutboundActivity excluded c c
  | send {a b : ChannelRecord} (h : OutboundActivity excluded a b) (m : Msg) :
      OutboundActivity excluded a (b.recordSent m)
  | recv {a b : ChannelRecord} (h : OutboundActivity excluded a b) (m : Msg)
      (hk : m.kind ≠ excluded) :
      OutboundActivity excluded a (b.advanceReceived m)

/-- **Retransmission law (commitment).**  While a channel only retransmits
retained messages and receives non-`commitment_signed` traffic, its reported
`next_commitment_number` is constant. -/
theorem outboundActivity_commitment_stable {a b : ChannelRecord}
    (h : OutboundActivity .commitmentSigned a b) :
    b.reestablish.nextCommitmentNumber = a.reestablish.nextCommitmentNumber := by
  induction h with
  | refl => rfl
  | send _ m ih =>
      rw [recordSent_reestablish]
      exact ih
  | recv _ m hk ih =>
      rw [advanceReceived_nextCommitment_of_ne _ _ hk]
      exact ih

/-- **Retransmission law (revocation).**  Symmetrically, the reported
`next_revocation_number` is constant until a `revoke_and_ack` arrives. -/
theorem outboundActivity_revocation_stable {a b : ChannelRecord}
    (h : OutboundActivity .revokeAndAck a b) :
    b.reestablish.nextRevocationNumber = a.reestablish.nextRevocationNumber := by
  induction h with
  | refl => rfl
  | send _ m ih =>
      rw [recordSent_reestablish]
      exact ih
  | recv _ m hk ih =>
      rw [advanceReceived_nextRevocation_of_ne _ _ hk]
      exact ih

/-- A `revoke_and_ack` strictly behind the commitment counter is the
acknowledgement: it advances only `next_revocation_number`. -/
theorem revokeAndAck_acknowledges (c : ChannelRecord) (m : RevokeAndAck)
    (h : c.reestablish.nextRevocationNumber < c.reestablish.nextCommitmentNumber) :
    (c.advanceReceived (.revokeAndAck m)).reestablish.nextRevocationNumber
        = c.reestablish.nextRevocationNumber + 1 ∧
      (c.advanceReceived (.revokeAndAck m)).reestablish.nextCommitmentNumber
        = c.reestablish.nextCommitmentNumber := by
  simp [ChannelRecord.advanceReceived, Msg.kind, ReestablishFields.afterRevocation, h]

/-- **Duplicate-detection gap, as a theorem.**  The wave-A
`advanceReceived` is not idempotent: replaying a `commitment_signed` advances
`next_commitment_number` a second time.  BOLT 2 deduplicates by the implicit
commitment number, which `Msg.commitmentSigned` does not carry. -/
theorem duplicate_commitmentSigned_advances_twice (c : ChannelRecord)
    (m : CommitmentSigned) :
    ((c.advanceReceived (.commitmentSigned m)).advanceReceived
        (.commitmentSigned m)).reestablish.nextCommitmentNumber
      = c.reestablish.nextCommitmentNumber + 2 := by
  simp [ChannelRecord.advanceReceived, Msg.kind, ReestablishFields.afterCommitment]

/-- A numbered refinement of `advanceReceived` for `commitment_signed`: the
counter advances only for the commitment number that is actually expected. -/
def advanceReceivedNumbered (c : ChannelRecord) (commitmentNumber : Nat) :
    ChannelRecord :=
  if commitmentNumber = c.reestablish.nextCommitmentNumber then
    { c with reestablish := c.reestablish.afterCommitment }
  else c

/-- The numbered refinement is idempotent, i.e. a retransmitted
`commitment_signed` is absorbed once the number has already been consumed. -/
theorem advanceReceivedNumbered_idempotent (c : ChannelRecord) (k : Nat) :
    advanceReceivedNumbered (advanceReceivedNumbered c k) k =
      advanceReceivedNumbered c k := by
  unfold advanceReceivedNumbered
  by_cases h : k = c.reestablish.nextCommitmentNumber
  · simp [h, ReestablishFields.afterCommitment]
  · simp [h]

/-- The numbered refinement still only moves the counter forward. -/
theorem advanceReceivedNumbered_monotone (c : ChannelRecord) (k : Nat) :
    c.reestablish.nextCommitmentNumber ≤
      (advanceReceivedNumbered c k).reestablish.nextCommitmentNumber := by
  unfold advanceReceivedNumbered
  split <;> simp [ReestablishFields.afterCommitment]

/-- A `receive` that is accepted cannot lower either counter of the addressed
channel record. -/
theorem receive_counters_monotone
    (s s' : PeerState) (m : Msg) (cid : ChannelId) (c : ChannelRecord)
    (hrecv : receive s m = some s') (hmsg : channelId? m = some cid)
    (hfind : findChannel s cid = some c) :
    ∃ c', findChannel s' cid = some c' ∧
      c.reestablish.nextCommitmentNumber ≤ c'.reestablish.nextCommitmentNumber ∧
      c.reestablish.nextRevocationNumber ≤ c'.reestablish.nextRevocationNumber := by
  by_cases he : receiveEvent? m = none
  · have hs' := receive_of_no_event s s' m cid c hrecv he hmsg hfind
    rw [hs']
    exact ⟨c.advanceReceived m,
      findChannel_updateChannel_of_channelId s cid (fun _ => c.advanceReceived m) c hfind
        (advanceReceived_channelId c m),
      (advanceReceived_counters_monotone c m).1,
      (advanceReceived_counters_monotone c m).2⟩
  · cases hstep : receiveEvent? m with
    | none => exact absurd hstep he
    | some e =>
        cases hhs : handshakeStep s.handshake e with
        | none =>
            have hr : receive s m = none := by
              cases ht : s.transport <;> simp [receive, ht, hstep, hhs]
            rw [hr] at hrecv
            exact absurd hrecv (by simp)
        | some hs =>
            have hs' := receive_of_event s s' m e hs hrecv hstep hhs
            rw [hs']
            exact ⟨c, by simpa [findChannel] using hfind, Nat.le_refl _, Nat.le_refl _⟩

/-! ## 4. The bridge to `Channel` commitment numbers -/

/-- The counters a loss-free reconnection would report for a channel:
`next_commitment_number = remoteCommitmentNumber + 1` (the next
`commitment_signed` we expect to receive) and
`next_revocation_number = localCommitmentNumber` (the next `revoke_and_ack`
we expect to receive).  This is the wave-A bridge alluded to in BOLT 2's
rationale; it is a proposed definition, not part of the wave-A model. -/
def countersOf (ch : Channel) : ReestablishFields where
  nextCommitmentNumber := ch.remoteCommitmentNumber + 1
  nextRevocationNumber := ch.localCommitmentNumber
  yourLastPerCommitmentSecret := ByteArray.empty
  myCurrentPerCommitmentPoint := ⟨ByteArray.empty⟩

/-- **A reconnect cannot report an earlier commitment.**  Any reachable
channel state has at least the commitment counters of its predecessor. -/
theorem reachable_counters_monotone {a b : Channel} (h : Reachable a b) :
    (countersOf a).nextCommitmentNumber ≤ (countersOf b).nextCommitmentNumber ∧
      (countersOf a).nextRevocationNumber ≤ (countersOf b).nextRevocationNumber := by
  have hc := Reachable.remoteCommitmentNumber_le h
  have hr := Reachable.localCommitmentNumber_le h
  constructor
  · change a.remoteCommitmentNumber + 1 ≤ b.remoteCommitmentNumber + 1
    omega
  · change a.localCommitmentNumber ≤ b.localCommitmentNumber
    omega

/-- Sending a `commitment_signed` strictly advances the reported commitment
number, so the subsequent reestablish names a strictly later commitment. -/
theorem commitmentSigned_counters_strict {a b : Channel}
    (h : Step a .commitmentSigned b) :
    (countersOf a).nextCommitmentNumber < (countersOf b).nextCommitmentNumber := by
  cases h with
  | commitmentSigned _ =>
      change a.remoteCommitmentNumber + 1 < (a.remoteCommitmentNumber + 1) + 1
      omega

/-- A `revoke_and_ack` receipt strictly advances the reported revocation
number. -/
theorem revokeAndAck_counters_strict {a b : Channel}
    (h : Step a .revokeAndAck b) :
    (countersOf a).nextRevocationNumber < (countersOf b).nextRevocationNumber := by
  cases h with
  | revokeAndAck _ =>
      change a.localCommitmentNumber < a.localCommitmentNumber + 1
      omega

/-- A normal-phase channel used only to exhibit the gap below. -/
def sampleKey : PubKey := ⟨ByteArray.empty⟩

def sampleParams : ChannelParams where
  dustLimitSat := 0
  channelReserveSat := 0
  toSelfDelay := 0
  maxHtlcValue := ⟨0⟩
  htlcMinimum := ⟨0⟩
  feerate := ⟨0⟩
  anchorOutputs := false

def sampleChannel : Channel where
  channelId := ⟨ByteArray.empty⟩
  funding := ⟨ByteArray.empty, 0⟩
  fundingValue := ⟨0⟩
  localEndpoint :=
    { nodeId := sampleKey, fundingPubKey := sampleKey, paymentBasepoint := sampleKey,
      delayedPaymentBasepoint := sampleKey, params := sampleParams }
  remoteEndpoint :=
    { nodeId := sampleKey, fundingPubKey := sampleKey, paymentBasepoint := sampleKey,
      delayedPaymentBasepoint := sampleKey, params := sampleParams }
  phase := .normal
  localCommitmentNumber := 0
  remoteCommitmentNumber := 0
  balance := { localBalance := ⟨0⟩, remoteBalance := ⟨0⟩ }
  htlcs := []

/-- **Model gap, as a theorem.**  `Step.revokeAndAck` has no dependence on a
preceding `commitment_signed`, so a reachable channel can violate BOLT 2's
`next_revocation_number ≤ next_commitment_number`.  The corrected bridge
statement is therefore conditional on that invariant. -/
theorem reachable_counters_inconsistent :
    ∃ a b : Channel, Reachable a b ∧ ¬ (countersOf b).consistent := by
  refine ⟨sampleChannel, { sampleChannel with localCommitmentNumber := 2 }, ?_, ?_⟩
  · have h1 : Step sampleChannel .revokeAndAck
        { sampleChannel with localCommitmentNumber := 1 } := by
      simpa [sampleChannel] using Step.revokeAndAck sampleChannel (by rfl)
    have h2 : Step { sampleChannel with localCommitmentNumber := 1 } .revokeAndAck
        { sampleChannel with localCommitmentNumber := 2 } := by
      simpa using Step.revokeAndAck { sampleChannel with localCommitmentNumber := 1 } (by rfl)
    exact Reachable.step (Reachable.of_step h1) h2
  · unfold countersOf ReestablishFields.consistent
    simp [sampleChannel]

/-! ## 5. `channel_ready` retransmission -/

/-- The two counters BOLT 2 compares before retransmitting `channel_ready`.
`PeerState` retains only the local side, so the peer's reported counter is an
explicit parameter. -/
structure ReconnectView where
  ourNextCommitmentNumber : Nat
  theirNextCommitmentNumber : Nat
deriving Repr, DecidableEq

/-- BOLT 2 (`02-peer-protocol.md:3487-3490`): retransmit `channel_ready`
exactly when both peers report `next_commitment_number = 1`. -/
def channelReadyMustBeResent (v : ReconnectView) : Prop :=
  v.ourNextCommitmentNumber = 1 ∧ v.theirNextCommitmentNumber = 1

theorem channelReadyMustBeResent_iff (v : ReconnectView) :
    channelReadyMustBeResent v ↔
      v.ourNextCommitmentNumber = 1 ∧ v.theirNextCommitmentNumber = 1 :=
  Iff.rfl

/-- Once a commitment beyond number 1 has been observed, the channel is in
normal operation and `channel_ready` must not be retransmitted
(`02-peer-protocol.md:3491-3493`). -/
theorem channelReady_not_resent_after_ack {v : ReconnectView}
    (h : 1 < v.ourNextCommitmentNumber) : ¬ channelReadyMustBeResent v := by
  simp [channelReadyMustBeResent]
  omega

/-- The retained `channel_ready` is returned verbatim by `lastSent`. -/
theorem lastSent_channelReady_of_pending (c : ChannelRecord) (m : Msg)
    (hl : c.lastChannelReady = some m) :
    c.lastSent .channelReady = some m := by
  simp [ChannelRecord.lastSent, hl]

/-- **`channel_ready` resend law.**  If a `channel_ready` is retained, then
`resend` yields exactly that message.  The BOLT *condition* for doing so is
`channelReadyMustBeResent`; `resend` itself is policy-free. -/
theorem resend_channelReady_of_pending (s : PeerState) (cid : ChannelId)
    (c : ChannelRecord) (m : Msg)
    (hfind : findChannel s cid = some c) (hl : c.lastChannelReady = some m) :
    resend s cid .channelReady = some m := by
  rw [resend_of_channel s cid .channelReady c hfind]
  exact lastSent_channelReady_of_pending c m hl

/-- The `ReconnectView` is necessary only because the received counters are
discarded: the local side of the test is already the record's counter. -/
theorem channelReady_resend_local_side (s : PeerState) (cid : ChannelId)
    (c : ChannelRecord) (m : Msg)
    (hfind : findChannel s cid = some c) (hl : c.lastChannelReady = some m)
    (hcounter : c.reestablish.nextCommitmentNumber = 1) :
    channelReadyMustBeResent
        { ourNextCommitmentNumber := c.reestablish.nextCommitmentNumber
          theirNextCommitmentNumber := 1 } ∧
      resend s cid .channelReady = some m :=
  ⟨⟨hcounter, rfl⟩, resend_channelReady_of_pending s cid c m hfind hl⟩

/-! ## 6. Data-loss-protect fields -/

/-- Both proof fields are mandatory in the pinned `channel_reestablish`. -/
def dataLossProtectPresent (r : ReestablishFields) : Prop :=
  r.yourLastPerCommitmentSecret.size = 32 ∧ r.myCurrentPerCommitmentPoint.Valid

/-- BOLT 2's `your_last_per_commitment_secret` rule
(`02-peer-protocol.md:3454-3458`): all zeroes when
`next_revocation_number = 0`. -/
def dataLossProtectOk (r : ReestablishFields) : Prop :=
  r.nextRevocationNumber = 0 → allZero r.yourLastPerCommitmentSecret = true

/-- The exact ("if and only if") form of the data-loss-protect secret rule.
Only the forward direction is imposed by BOLT 2; the converse needs the
received secret to be non-zero. -/
def dataLossSecretExact (r : ReestablishFields) : Prop :=
  r.nextRevocationNumber = 0 ↔ allZero r.yourLastPerCommitmentSecret = true

/-- A fresh channel carries a 32-byte secret and a 33-byte point. -/
theorem dataLossProtectPresent_initial :
    dataLossProtectPresent ReestablishFields.initial := by
  unfold dataLossProtectPresent ReestablishFields.initial PubKey.Valid
  decide

/-- The exact form implies BOLT 2's one-directional requirement. -/
theorem dataLossProtect_ok_of_exact {r : ReestablishFields}
    (h : dataLossSecretExact r) : dataLossProtectOk r :=
  fun hzero => h.mp hzero

/-- **Data-loss-protect exactness, conditionally.**  If the reported secret is
a genuine received secret (not all zeroes) and the counter is non-zero, the
"exactly when" form holds.  Non-zeroness of a revealed per-commitment secret
is a cryptographic fact (C1/C6), not a consequence of the counter. -/
theorem dataLossSecretExact_of_lastSecret (r : ReestablishFields) (secret : ByteArray)
    (hidx : r.nextRevocationNumber ≠ 0)
    (hsecret : r.yourLastPerCommitmentSecret = secret)
    (hnz : allZero secret = false) :
    dataLossSecretExact r := by
  unfold dataLossSecretExact
  rw [hsecret, hnz]
  simp [hidx]

/-- The data-loss-protect fields of the packed message are exactly the
record's fields, so `Msg.semanticOk` on a reestablish is precisely the 48-bit
bound plus `dataLossProtectOk`. -/
theorem toMsg_semanticOk_iff (cid : ChannelId) (r : ReestablishFields) :
    semanticOk (ReestablishFields.toMsg cid r) ↔
      (r.nextCommitmentNumber < TWO_POW_48 ∧
        r.nextRevocationNumber < TWO_POW_48 ∧ dataLossProtectOk r) :=
  Iff.rfl

/-- Packing counters into a message preserves them, so the monotonicity
statements above are statements about the values on the wire. -/
theorem toMsg_channelId (cid : ChannelId) (r : ReestablishFields) :
    channelId? (ReestablishFields.toMsg cid r) = some cid := rfl

/-! ## 7. The exact acceptance predicate -/

/-- The counters this side last put on the wire.  `closingSignedReceived`
records BOLT 2's exception: a lost `revoke_and_ack` is not re-sent after a
`closing_signed`. -/
structure SentCounters where
  lastCommitmentNumber : Nat
  lastRevocationNumber : Nat
  closingSignedReceived : Bool := false
deriving Repr, DecidableEq

/-- **BOLT 2's acceptance predicate**, stated as a `Prop`, not a `Bool`.

The peer's `next_commitment_number` must equal our last sent commitment
number (they missed the last `commitment_signed`, which we must retransmit
with the same number) or one greater (nothing was lost).  The same window
applies to `next_revocation_number`.  A zero commitment number fails the
channel, a lost `revoke_and_ack` is not re-sent after `closing_signed`, and
the two counters must be consistent. -/
def ReestablishAccepted (sent : SentCounters) (r : ReestablishFields) : Prop :=
  0 < r.nextCommitmentNumber ∧
    (r.nextCommitmentNumber = sent.lastCommitmentNumber ∨
      r.nextCommitmentNumber = sent.lastCommitmentNumber + 1) ∧
    (r.nextRevocationNumber = sent.lastRevocationNumber ∨
      r.nextRevocationNumber = sent.lastRevocationNumber + 1) ∧
    (r.nextRevocationNumber = sent.lastRevocationNumber →
      sent.closingSignedReceived = false) ∧
    r.consistent

/-- Rejection is the negation of the exact predicate. -/
def ReestablishRejected (sent : SentCounters) (r : ReestablishFields) : Prop :=
  ¬ ReestablishAccepted sent r

/-- Acceptance bounds the reported commitment number to the BOLT window. -/
theorem accepted_commitment_bounds {sent : SentCounters} {r : ReestablishFields}
    (h : ReestablishAccepted sent r) :
    sent.lastCommitmentNumber ≤ r.nextCommitmentNumber ∧
      r.nextCommitmentNumber ≤ sent.lastCommitmentNumber + 1 := by
  rcases h with ⟨_, hc, _, _, _⟩
  rcases hc with hc | hc <;> omega

/-- Acceptance implies the peer is not reporting an earlier commitment. -/
theorem accepted_not_earlier {sent : SentCounters} {r : ReestablishFields}
    (h : ReestablishAccepted sent r) :
    sent.lastCommitmentNumber ≤ r.nextCommitmentNumber :=
  (accepted_commitment_bounds h).1

/-- Acceptance implies the revocation window as well. -/
theorem accepted_revocation_bounds {sent : SentCounters} {r : ReestablishFields}
    (h : ReestablishAccepted sent r) :
    sent.lastRevocationNumber ≤ r.nextRevocationNumber ∧
      r.nextRevocationNumber ≤ sent.lastRevocationNumber + 1 := by
  rcases h with ⟨_, _, hr, _, _⟩
  rcases hr with hr | hr <;> omega

/-- A commitment number in the future of the window is rejected
(`channel.rs:11287-11294`, "future remote commitment transaction"). -/
theorem rejected_of_future {sent : SentCounters} {r : ReestablishFields}
    (h : sent.lastCommitmentNumber + 1 < r.nextCommitmentNumber) :
    ReestablishRejected sent r := by
  intro ha
  have hb := (accepted_commitment_bounds ha).2
  omega

/-- A commitment number behind the window is rejected
(`channel.rs:11277-11286`, "very old remote commitment transaction"). -/
theorem rejected_of_stale {sent : SentCounters} {r : ReestablishFields}
    (h : r.nextCommitmentNumber < sent.lastCommitmentNumber) :
    ReestablishRejected sent r := by
  intro ha
  have hb := (accepted_commitment_bounds ha).1
  omega

/-- `next_commitment_number = 0` is always rejected
(`channel.rs:10845-10848`, BOLT 2 `02-peer-protocol.md:3484-3486`). -/
theorem rejected_of_zero {sent : SentCounters} {r : ReestablishFields}
    (h : r.nextCommitmentNumber = 0) : ReestablishRejected sent r := by
  intro ha
  have hpos := ha.1
  omega

/-- Inconsistent numbers (`next_revocation_number > next_commitment_number`)
are rejected.  The predicate names the exact inequality rather than a Boolean
comparison. -/
theorem rejected_of_inconsistent_numbers {sent : SentCounters} {r : ReestablishFields}
    (h : r.nextCommitmentNumber < r.nextRevocationNumber) :
    ReestablishRejected sent r := by
  intro ha
  have hc : r.nextRevocationNumber ≤ r.nextCommitmentNumber := ha.2.2.2.2
  omega

/-- A lost `revoke_and_ack` must not be re-sent after `closing_signed`
(`02-peer-protocol.md:3503-3505`, `:3566-3569`). -/
theorem rejected_of_revoke_after_closing {sent : SentCounters} {r : ReestablishFields}
    (hlast : r.nextRevocationNumber = sent.lastRevocationNumber)
    (hclosed : sent.closingSignedReceived = true) : ReestablishRejected sent r := by
  intro ha
  have hfalse := ha.2.2.2.1 hlast
  rw [hclosed] at hfalse
  exact Bool.noConfusion hfalse

/-- **Retransmission decision.**  Within an accepted report, the last
`commitment_signed` must be retransmitted with the same number exactly when
the peer is one behind. -/
theorem accepted_needs_retransmit_iff {sent : SentCounters} {r : ReestablishFields}
    (h : ReestablishAccepted sent r) :
    r.nextCommitmentNumber = sent.lastCommitmentNumber ∨
      r.nextCommitmentNumber = sent.lastCommitmentNumber + 1 :=
  h.2.1

end LnLean.Proofs.Protocol
