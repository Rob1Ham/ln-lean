import LnLean.Proofs.Protocol.ChannelReestablishProps
import LnLean.Proofs.Liveness

/-!
# LnLean.Proofs.PhaseC2.ReestablishRange

## English claim

This module closes the quantitative side of BOLT 2 §"Message Retransmission"
for the wave-A peer model:

1. **Finite retransmission window.**  The messages a node may retransmit after
   a `channel_reestablish` are exactly the retained messages whose kind is
   accepted by `LnLean.Proofs.Liveness.retransmittable`.  That set is finite:
   it is enumerated by `retransmissionWindow`, which has length at most the
   explicit buffer capacity `retransmitBufferCapacity = 5`.
2. **The window is a subset of the recent-message buffer.**  Every eligible
   message occurs in `recentBuffer`, the explicit five-slot buffer made of
   the `Option Msg` fields of `ChannelRecord`.  This is the "one slot per
   retransmittable kind" buffer-size assumption, stated as a definition and
   proved for every record rather than assumed axiomatically.
3. **Reconnect preserves the window.**  Receiving any inbound message,
   including `channel_reestablish`, only changes the reestablish counters:
   `advanceReceived` leaves every `lastSent` slot untouched
   (`advanceReceived_lastSent`).  Consequently the window after any reconnect
   inbox is equal to the window before it, hence still bounded by five, and a
   retained `channel_ready` remains eligible
   (`reconnect_preserves_channelReady`).
4. **Counters are monotone across reconnect.**  Outbound retention
   (`recordSent`) does not change either counter, while every inbound receipt
   is non-decreasing in both counters (`advanceReceived_counters_monotone`).
   The resulting `ReconnectTrace` therefore cannot report an earlier
   commitment or revocation number.
5. **The accepted report has at most two retransmission candidates.**
   `ReestablishAccepted` restricts the peer's `next_commitment_number` and
   `next_revocation_number` to the last-sent value or one greater.  The
   `retransmitPlan` therefore contains at most one `commitment_signed` and at
   most one `revoke_and_ack`, both drawn from the five-slot buffer.

No statement in this module is conditional on an unproved bridge: the only
assumption made explicit is the buffer size, which is the number of retained
slots in `ChannelRecord`.

## BOLT sections (pinned BOLTs `1aadb71`)

* BOLT 2 §"Message Retransmission" (`refs/bolts/02-peer-protocol.md:3352-3635`):
  the `channel_reestablish` fields and counter semantics (`:3374-3395`);
  `channel_ready` retransmission (`:3487-3496`); reusing the same
  commitment number (`:3497-3505`); resending `revoke_and_ack`
  (`:3506-3517`); retransmitting `shutdown` (`:3589-3592`).
* BOLT 2 §"The `channel_ready` Message" (`02-peer-protocol.md:1045-1048`):
  `channel_ready` is the current name of `funding_locked`.
* BOLT 2 §"Committing Updates So Far" (`02-peer-protocol.md:3097-3120`):
  the `commitment_signed` / `revoke_and_ack` acknowledgement pairing whose
  counters the window is indexed by.

## rust-lightning anchors (commit fe4900930c6bd5786ec4203274d7cf312776a5a6)

* `lightning/src/ln/channel.rs:10826` `Channel::channel_reestablish`, the
  handler that decides what to retransmit; `:10845-10848` rejects a zero
  `next_local_commitment_number`.
* `lightning/src/ln/channel.rs:11088-11112` `required_revoke`: at most one
  `revoke_and_ack` is owed after a reconnect.
* `lightning/src/ln/channel.rs:11126-11134`
  `both_sides_on_initial_commitment_number`: the `channel_ready`
  retransmission test.
* `lightning/src/ln/channel.rs:11187-11294` accepts a commitment number equal
  to the next one or one less, and rejects older/future values.
* `lightning/src/ln/channel.rs:13135-13186` `get_channel_reestablish` fills
  the four reported counters.
* `lightning/src/ln/channelmanager.rs:17831` dispatches an inbound
  `channel_reestablish`.

## What is NOT modelled

* `ChannelRecord` keeps exactly one retained message per retransmittable kind.
  The capacity five is therefore a *model* bound, not a BOLT 2 wire bound: a
  real node may keep per-update data.  The module proves the consequences of
  the bound and names it in `retransmitBufferCapacity` /
  `bufferCapacity_eq_slots`.
* The received reestablish counters are not stored by `PeerState`, so the
  window is formulated over the local `ChannelRecord`; the `ReestablishAccepted`
  half uses the explicit `SentCounters` parameter of
  `LnLean.Proofs.Protocol.ChannelReestablishProps`.
* The model does not record *which* `commitment_signed` was last sent: the
  retained slot is a single message, so "reuse the same commitment number" is
  represented by the counter/acceptance predicates, not by a numbered queue.
* Relative ordering of a retransmitted `revoke_and_ack` and
  `commitment_signed` (BOLT 2 `:3511-3516`) is not modelled; `retransmitPlan`
  is a set/list, not a scheduled sequence.
* Splicing, `next_funding`, `announcement_signatures`, `closing_signed`
  retransmission, and error/close transitions are out of scope, as in
  `ChannelReestablishProps`.
-/

namespace LnLean.Proofs.PhaseC2

set_option autoImplicit false

open LnLean
open LnLean.Protocol
open LnLean.Proofs.Liveness
open LnLean.Proofs.Protocol

/-! ## 1. The retransmittable kinds and the explicit buffer capacity -/

/-- The five message kinds that BOLT 2 asks a node to retain and possibly
retransmit after reconnection: `funding_signed`, `channel_ready`,
`commitment_signed`, `revoke_and_ack`, and `shutdown`. -/
def retransmittableKinds : List MsgKind :=
  [.fundingSigned, .channelReady, .commitmentSigned, .revokeAndAck, .shutdown]

/-- The **explicit buffer-size assumption** of this module: `ChannelRecord`
exposes one retransmission slot for each of the five retransmittable kinds. -/
def retransmitBufferCapacity : Nat := 5

theorem retransmitBufferCapacity_eq_five : retransmitBufferCapacity = 5 := rfl

/-- The capacity is exactly the number of retransmittable kinds, so the
buffer-size assumption and the retransmission set have a common bound. -/
theorem bufferCapacity_eq_slots :
    retransmitBufferCapacity = retransmittableKinds.length := rfl

/-- `retransmittable` is exactly membership in the explicit kind list. -/
theorem retransmittable_iff_mem_kinds (k : MsgKind) :
    retransmittable k = true ↔ k ∈ retransmittableKinds := by
  cases k <;> simp [retransmittable, retransmittableKinds]

theorem retransmittableKinds_nodup : retransmittableKinds.Nodup := by
  decide

theorem retransmittableKinds_length : retransmittableKinds.length = 5 := rfl

/-! ## 2. The recent-message buffer and its size -/

/-- The explicit recent-message buffer: the five `Option Msg` slots of a
`ChannelRecord`, flattened.  This is the bounded store from which every
retransmission is drawn. -/
def recentBuffer (c : ChannelRecord) : List Msg :=
  [c.lastFundingSigned, c.lastChannelReady, c.lastCommitmentSigned,
    c.lastRevokeAndAck, c.lastShutdown].filterMap (fun o => o)

/-- The buffer-boundedness predicate.  It holds for every record: the bound is
structural, not an extra hypothesis. -/
def BufferBounded (c : ChannelRecord) : Prop :=
  (recentBuffer c).length ≤ retransmitBufferCapacity

/-- The recent-message buffer never holds more than the five modelled slots. -/
theorem recentBuffer_length_le (c : ChannelRecord) :
    (recentBuffer c).length ≤ retransmitBufferCapacity := by
  have h := List.length_filterMap_le (fun o : Option Msg => o)
    [c.lastFundingSigned, c.lastChannelReady, c.lastCommitmentSigned,
      c.lastRevokeAndAck, c.lastShutdown]
  simpa [recentBuffer, retransmitBufferCapacity] using h

/-- Every record satisfies the explicit buffer-size assumption. -/
theorem bufferBounded (c : ChannelRecord) : BufferBounded c :=
  recentBuffer_length_le c

/-- A message retained in a retransmittable slot is present in the recent
buffer.  This is the slot-to-buffer inclusion used by all later subset
statements. -/
theorem lastSent_mem_recentBuffer {c : ChannelRecord} {k : MsgKind} {m : Msg}
    (hk : retransmittable k = true) (h : c.lastSent k = some m) :
    m ∈ recentBuffer c := by
  rw [recentBuffer, List.mem_filterMap]
  refine ⟨some m, ?_, rfl⟩
  cases k <;>
    simp_all [retransmittable, ChannelRecord.lastSent]

/-! ## 3. The finite retransmission window -/

/-- The messages eligible for retransmission from a record: one per
retransmittable kind, in BOLT 2 order. -/
def retransmissionWindow (c : ChannelRecord) : List Msg :=
  retransmittableKinds.filterMap (fun k => c.lastSent k)

/-- Membership in the window is exactly "retained under a retransmittable
kind".  This is the bridge between the `retransmittable` predicate and the
bounded buffer. -/
theorem mem_retransmissionWindow_iff (c : ChannelRecord) (m : Msg) :
    m ∈ retransmissionWindow c ↔
      ∃ k, retransmittable k = true ∧ c.lastSent k = some m := by
  constructor
  · intro hm
    rw [retransmissionWindow, List.mem_filterMap] at hm
    obtain ⟨k, hk, hsk⟩ := hm
    exact ⟨k, (retransmittable_iff_mem_kinds k).2 hk, hsk⟩
  · rintro ⟨k, hk, hsk⟩
    rw [retransmissionWindow, List.mem_filterMap]
    exact ⟨k, (retransmittable_iff_mem_kinds k).1 hk, hsk⟩

/-- **The window is finite and bounded by the buffer capacity.** -/
theorem retransmissionWindow_length_le (c : ChannelRecord) :
    (retransmissionWindow c).length ≤ retransmitBufferCapacity := by
  have h := List.length_filterMap_le (fun k => c.lastSent k) retransmittableKinds
  simpa [retransmissionWindow, retransmitBufferCapacity, retransmittableKinds]
    using h

/-- **The eligible set is a subset of the recent-message buffer.** -/
theorem retransmissionWindow_subset_recentBuffer (c : ChannelRecord) :
    retransmissionWindow c ⊆ recentBuffer c := by
  intro m hm
  rw [mem_retransmissionWindow_iff] at hm
  obtain ⟨k, hk, hsk⟩ := hm
  exact lastSent_mem_recentBuffer hk hsk

/-- Existential form of finiteness: there is one explicit list containing
every eligible message and no more than `retransmitBufferCapacity` entries. -/
theorem exists_bounded_retransmissionWindow (c : ChannelRecord) :
    ∃ ws : List Msg,
      (∀ m, (∃ k, retransmittable k = true ∧ c.lastSent k = some m) → m ∈ ws) ∧
        ws.length ≤ retransmitBufferCapacity := by
  refine ⟨retransmissionWindow c, ?_, retransmissionWindow_length_le c⟩
  intro m hm
  exact (mem_retransmissionWindow_iff c m).2 hm

/-- Retaining a retransmittable outbound message puts it into the window, so
new retransmissions enter the bounded buffer by construction. -/
theorem recordSent_mem_retransmissionWindow (c : ChannelRecord) (m : Msg)
    (h : retransmittable m.kind = true) :
    m ∈ retransmissionWindow (c.recordSent m) := by
  rw [mem_retransmissionWindow_iff]
  exact ⟨m.kind, h, recordSent_lastSent c m h⟩

/-! ## 4. A `channel_reestablish` and an inbox preserve the window -/

/-- Receiving `channel_reestablish` does not change any retained slot, hence
does not change the retransmission window. -/
theorem channelReestablish_retransmissionWindow (c : ChannelRecord)
    (m : ChannelReestablish) :
    retransmissionWindow (c.advanceReceived (.channelReestablish m)) =
      retransmissionWindow c := by
  have h : (fun k => (c.advanceReceived (.channelReestablish m)).lastSent k) =
      (fun k => c.lastSent k) := by
    funext k
    exact advanceReceived_lastSent c (.channelReestablish m) k
  simp only [retransmissionWindow]
  rw [h]

/-- **A whole reconnect inbox preserves the window.**  Every inbound receipt
leaves all `lastSent` slots untouched (`foldl_advanceReceived_lastSent`). -/
theorem reconnect_retransmissionWindow_eq (c : ChannelRecord) (inbox : List Msg) :
    retransmissionWindow (inbox.foldl ChannelRecord.advanceReceived c) =
      retransmissionWindow c := by
  have h : (fun k => (inbox.foldl ChannelRecord.advanceReceived c).lastSent k) =
      (fun k => c.lastSent k) := by
    funext k
    exact foldl_advanceReceived_lastSent c inbox k
  simp only [retransmissionWindow]
  rw [h]

/-- Consequently the post-reconnect window is still bounded by the capacity. -/
theorem reconnect_retransmissionWindow_length_le (c : ChannelRecord)
    (inbox : List Msg) :
    (retransmissionWindow
        (inbox.foldl ChannelRecord.advanceReceived c)).length ≤
      retransmitBufferCapacity := by
  rw [reconnect_retransmissionWindow_eq]
  exact retransmissionWindow_length_le c

/-- A retained `channel_ready` survives any reconnect inbox and remains an
eligible retransmission. -/
theorem reconnect_preserves_channelReady_eligible (c : ChannelRecord) (m : Msg)
    (h : c.lastChannelReady = some m) (inbox : List Msg) :
    m ∈ retransmissionWindow (inbox.foldl ChannelRecord.advanceReceived c) := by
  rw [mem_retransmissionWindow_iff]
  refine ⟨.channelReady, rfl, ?_⟩
  rw [foldl_advanceReceived_lastSent]
  simpa [ChannelRecord.lastSent] using h

/-! ## 5. Counters are monotone across reconnect -/

/-- Outbound retention does not move either reported counter. -/
theorem recordSent_counters_eq (c : ChannelRecord) (m : Msg) :
    (c.recordSent m).reestablish.nextCommitmentNumber =
        c.reestablish.nextCommitmentNumber ∧
      (c.recordSent m).reestablish.nextRevocationNumber =
        c.reestablish.nextRevocationNumber := by
  have h := recordSent_reestablish c m
  rw [h]
  exact ⟨rfl, rfl⟩

/-- Any finite inbound inbox is monotone in both counters. -/
theorem foldl_advanceReceived_counters_monotone (c : ChannelRecord)
    (inbox : List Msg) :
    c.reestablish.nextCommitmentNumber ≤
        (inbox.foldl ChannelRecord.advanceReceived c).reestablish.nextCommitmentNumber ∧
      c.reestablish.nextRevocationNumber ≤
        (inbox.foldl ChannelRecord.advanceReceived c).reestablish.nextRevocationNumber := by
  induction inbox generalizing c with
  | nil => exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | cons m rest ih =>
      simp only [List.foldl_cons]
      have h1 := advanceReceived_counters_monotone c m
      have h2 := ih (c.advanceReceived m)
      exact ⟨Nat.le_trans h1.1 h2.1, Nat.le_trans h1.2 h2.2⟩

/-- A reconnect trace: any number of outbound retentions interleaved with
inbound receipts.  The `channel_reestablish` itself is one of the `recv`
steps, so the monotonicity below covers the reconnect boundary. -/
inductive ReconnectTrace : ChannelRecord → ChannelRecord → Prop where
  | refl (c : ChannelRecord) : ReconnectTrace c c
  | send {a b : ChannelRecord} (h : ReconnectTrace a b) (m : Msg) :
      ReconnectTrace a (b.recordSent m)
  | recv {a b : ChannelRecord} (h : ReconnectTrace a b) (m : Msg) :
      ReconnectTrace a (b.advanceReceived m)

/-- Transport of a counter bound through one outbound retention. -/
theorem counters_monotone_recordSent {a b : ChannelRecord} (m : Msg)
    (h : a.reestablish.nextCommitmentNumber ≤ b.reestablish.nextCommitmentNumber ∧
      a.reestablish.nextRevocationNumber ≤ b.reestablish.nextRevocationNumber) :
    a.reestablish.nextCommitmentNumber ≤
        (b.recordSent m).reestablish.nextCommitmentNumber ∧
      a.reestablish.nextRevocationNumber ≤
        (b.recordSent m).reestablish.nextRevocationNumber := by
  have hb := recordSent_reestablish b m
  exact ⟨by rw [hb]; exact h.1, by rw [hb]; exact h.2⟩

/-- Transport of a counter bound through one inbound receipt. -/
theorem counters_monotone_advanceReceived {a b : ChannelRecord} (m : Msg)
    (h : a.reestablish.nextCommitmentNumber ≤ b.reestablish.nextCommitmentNumber ∧
      a.reestablish.nextRevocationNumber ≤ b.reestablish.nextRevocationNumber) :
    a.reestablish.nextCommitmentNumber ≤
        (b.advanceReceived m).reestablish.nextCommitmentNumber ∧
      a.reestablish.nextRevocationNumber ≤
        (b.advanceReceived m).reestablish.nextRevocationNumber := by
  have hb := advanceReceived_counters_monotone b m
  exact ⟨Nat.le_trans h.1 hb.1, Nat.le_trans h.2 hb.2⟩

/-- **Sent/received counters are monotone across a reconnect.**  Sending
(retaining) keeps both counters equal; receiving never lowers either. -/
theorem reconnectTrace_counters_monotone {a b : ChannelRecord}
    (h : ReconnectTrace a b) :
    a.reestablish.nextCommitmentNumber ≤ b.reestablish.nextCommitmentNumber ∧
      a.reestablish.nextRevocationNumber ≤ b.reestablish.nextRevocationNumber := by
  induction h with
  | refl => exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | send _ m ih => exact counters_monotone_recordSent m ih
  | recv _ m ih => exact counters_monotone_advanceReceived m ih

/-! ## 6. The accepted report has at most two candidates -/

/-- The concrete retransmission decision: a `commitment_signed` is re-sent
when the peer reports the last-sent commitment number, and a `revoke_and_ack`
is re-sent when the peer reports the last-sent revocation number.  Both come
from the retained slots. -/
def retransmitPlan (c : ChannelRecord) (sent : SentCounters)
    (r : ReestablishFields) : List Msg :=
  (if r.nextCommitmentNumber = sent.lastCommitmentNumber then
      c.lastSent .commitmentSigned else none).toList ++
    (if r.nextRevocationNumber = sent.lastRevocationNumber then
      c.lastSent .revokeAndAck else none).toList

theorem retransmitPlan_length_le (c : ChannelRecord) (sent : SentCounters)
    (r : ReestablishFields) :
    (retransmitPlan c sent r).length ≤ 2 := by
  have h1 : (if r.nextCommitmentNumber = sent.lastCommitmentNumber then
      c.lastSent .commitmentSigned else none).toList.length ≤ 1 := by
    split <;> simp
  have h2 : (if r.nextRevocationNumber = sent.lastRevocationNumber then
      c.lastSent .revokeAndAck else none).toList.length ≤ 1 := by
    split <;> simp
  rw [retransmitPlan]
  simp only [List.length_append]
  omega

/-- Both candidates of a retransmission plan are in the recent buffer. -/
theorem retransmitPlan_subset_recentBuffer (c : ChannelRecord)
    (sent : SentCounters) (r : ReestablishFields) :
    retransmitPlan c sent r ⊆ recentBuffer c := by
  intro m hm
  simp only [retransmitPlan, List.mem_append, Option.mem_toList] at hm
  rcases hm with hm | hm
  · by_cases h : r.nextCommitmentNumber = sent.lastCommitmentNumber
    · simp only [h, ite_true] at hm
      exact lastSent_mem_recentBuffer (k := .commitmentSigned) (by rfl) hm
    · simp only [h, ite_false] at hm
      simp at hm
  · by_cases h : r.nextRevocationNumber = sent.lastRevocationNumber
    · simp only [h, ite_true] at hm
      exact lastSent_mem_recentBuffer (k := .revokeAndAck) (by rfl) hm
    · simp only [h, ite_false] at hm
      simp at hm

/-- **Finiteness of the accepted retransmission window.**  An accepted
`channel_reestablish` yields at most one `commitment_signed` and at most one
`revoke_and_ack`, both inside the five-slot buffer, and its commitment number
is one of the two numbers BOLT 2 allows. -/
theorem accepted_retransmitPlan_finite {c : ChannelRecord}
    {sent : SentCounters} {r : ReestablishFields}
    (h : ReestablishAccepted sent r) :
    (retransmitPlan c sent r).length ≤ 2 ∧
      retransmitPlan c sent r ⊆ recentBuffer c ∧
        (r.nextCommitmentNumber = sent.lastCommitmentNumber ∨
          r.nextCommitmentNumber = sent.lastCommitmentNumber + 1) :=
  ⟨retransmitPlan_length_le c sent r,
    retransmitPlan_subset_recentBuffer c sent r,
    accepted_needs_retransmit_iff h⟩

end LnLean.Proofs.PhaseC2
