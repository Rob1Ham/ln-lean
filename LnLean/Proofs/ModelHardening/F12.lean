import LnLean.Protocol.Peer
import LnLean.Protocol.Messages
import LnLean.Proofs.Protocol.ChannelReestablishProps

/-!
# LnLean.Proofs.ModelHardening.F12

## English claim

BOLT 2's retransmission protocol lets a peer resynchronize after a reconnect
without rolling acknowledged channel state backwards.  A `channel_reestablish`
reports the next `commitment_signed` and `revoke_and_ack` numbers the sender
expects; the receiver must reject a report that names state older than the
last counters it put on the wire, because every older message has already been
dropped from the retransmission buffer.

The wave-A model has no predicate for this condition.  This module supplies it
and proves the strongest statements available over the committed model:

1. **The invariant.**  `NoRollback sent r` says neither counter in a reported
   `ReestablishFields` is behind the corresponding last-sent counter.  It is
   the exact negation of `RollsBack` (`not_rollsBack_iff_noRollback`).
2. **BOLT 2's window implies the invariant.**  `ReestablishAccepted` allows
   the last sent number or its successor, so every accepted report satisfies
   `NoRollback` (`accepted_noRollback`).  A stale or future report is
   rejected (`accepted_not_rollsBack`).
3. **Receipts never roll the local state back.**  `receive` reads a
   `channel_reestablish` and does not apply it: the addressed record's
   counters are exactly unchanged (`receive_channelReestablish_noRollback`).
   Every other receipt is monotone, so no receipt lowers either counter
   (`receive_noRollback`).
4. **Retransmission is counter-stable.**  A reconnection interval consisting
   of re-sending retained messages and receiving the peer's reestablish leaves
   both counters exactly constant (`retransmitTrace_counters_eq`); more
   generally all channel activity is monotone
   (`channelActivity_counters_monotone`).
5. **The invariant is necessary.**  A consumer that adopted the peer's report
   (`adoptReported`) would roll back acknowledged state on a stale report
   (`adoptReported_rollsBack`); the guarded consumer `adoptGuarded` cannot
   (`adoptGuarded_noRollback`).  The model's `receive` itself accepts a stale
   report because it discards the reported counters
   (`receive_accepts_stale_report`).

## BOLT sections

* BOLT 2 §"Message Retransmission" (`refs/bolts/02-peer-protocol.md:3352`),
  field semantics (`:3374-3395`), sender requirements (`:3449-3460`), and the
  receiver decision table (`:3483-3517`): a peer's
  `next_commitment_number` must be one greater than the last sent commitment
  or equal to it (the last one is retransmitted); anything older is a
  protocol failure.
* BOLT 2 §"The `channel_ready` Message" (`02-peer-protocol.md:1045-1048`):
  `channel_ready` is the current name of `funding_locked`.

## rust-lightning anchors (commit fe4900930c6bd5786ec4203274d7cf312776a5a6)

* `lightning/src/ln/channel.rs:10826` `Channel::channel_reestablish`;
  `:10845-10848` rejects `next_local_commitment_number = 0` and future
  values; `:11187-11294` accepts only the last or next commitment number and
  treats anything older as "very old remote commitment transaction".
* `lightning/src/ln/channel.rs:13135-13186` `get_channel_reestablish`
  reports the next expected `commitment_signed` / `revoke_and_ack`.
* `lightning/src/ln/channel.rs:11088-11112` `required_revoke` decides whether
  a lost `revoke_and_ack` must be retransmitted.

## What is NOT modelled

* `PeerState.receive` does **not** check `ReestablishAccepted` and does not
  store the received counters.  Consequently a stale report is accepted by
  the transition system, but it cannot move local state because the counters
  are discarded.  The invariant in this module is a condition on a consumer
  (`adoptGuarded`); the model gap is mechanized by
  `receive_accepts_stale_report`.
* `commitment_signed` carries no commitment number, so `advanceReceived`
  cannot detect duplicate or stale retransmissions.  A replay advances the
  counter (proved in `ChannelReestablishProps`), which is a
  duplicate-detection gap rather than a rollback.
* `ChannelRecord.recordSent` overwrites the retained message unconditionally.
  The model has no message numbers with which to compare an old retained copy
  with a newer one, so the "retransmit the *right* unacknowledged message"
  half of the claim is not mechanizable here.
* `resend` is an explicit operation; no timer or retry scheduler is modelled.
* The `Channel`-level counters (`localCommitmentNumber`,
  `remoteCommitmentNumber`) are a separate view.  Their bridge to the
  reestablish counters (`countersOf`) is in
  `LnLean.Proofs.Protocol.ChannelReestablishProps`; this module works at the
  `ChannelRecord`/`ReestablishFields` layer where the report lives.
-/

-- OBLIGATION: LN-WF-F12

namespace LnLean.Proofs.ModelHardening.F12

set_option autoImplicit false

open LnLean
open LnLean.Protocol
open LnLean.Channel
open LnLean.Proofs.Protocol

/-! ## 1. The missing no-rollback invariant -/

/-- A report rolls back acknowledged state when it names a commitment or
revocation number strictly behind the counters this side last put on the
wire.  Such a number cannot be served by retransmission: BOLT 2 retains only
the last message of each kind. -/
def RollsBack (sent : SentCounters) (r : ReestablishFields) : Prop :=
  r.nextCommitmentNumber < sent.lastCommitmentNumber ∨
    r.nextRevocationNumber < sent.lastRevocationNumber

/-- The no-rollback invariant for `channel_reestablish`: the reported
commitment and revocation numbers are at least the last counters this side
sent.  `lastCommitmentNumber` is the last `commitment_signed` sent, which is
exactly the message BOLT 2 must retransmit when the peer reports equality;
the value is therefore a floor, not an acknowledgement of the last message. -/
def NoRollback (sent : SentCounters) (r : ReestablishFields) : Prop :=
  sent.lastCommitmentNumber ≤ r.nextCommitmentNumber ∧
    sent.lastRevocationNumber ≤ r.nextRevocationNumber

/-- `RollsBack` is the negation of the invariant. -/
theorem not_rollsBack_iff_noRollback (sent : SentCounters)
    (r : ReestablishFields) :
    ¬ RollsBack sent r ↔ NoRollback sent r := by
  unfold RollsBack NoRollback
  omega

/-- The invariant fails exactly when the report rolls state back. -/
theorem rollsBack_iff_not_noRollback (sent : SentCounters)
    (r : ReestablishFields) :
    RollsBack sent r ↔ ¬ NoRollback sent r := by
  unfold RollsBack NoRollback
  omega

/-- The invariant is monotone under the counter advancement performed by
receiving a `commitment_signed`. -/
theorem noRollback_afterCommitment {sent : SentCounters} {r : ReestablishFields}
    (h : NoRollback sent r) : NoRollback sent (ReestablishFields.afterCommitment r) := by
  unfold NoRollback at *
  simp [ReestablishFields.afterCommitment] at *
  omega

/-- The invariant is monotone under the counter advancement performed by
receiving an acknowledged `revoke_and_ack`. -/
theorem noRollback_afterRevocation {sent : SentCounters} {r : ReestablishFields}
    (h : NoRollback sent r) : NoRollback sent (ReestablishFields.afterRevocation r) := by
  unfold NoRollback at *
  simp [ReestablishFields.afterRevocation] at *
  omega

/-- Any receipt on a `ChannelRecord` preserves the invariant, because
`advanceReceived` is monotone in both counters.  This is the reusable
invariant-preservation lemma behind the receipt theorems below. -/
theorem noRollback_advanceReceived {sent : SentCounters} {c : ChannelRecord}
    (h : NoRollback sent c.reestablish) (m : Msg) :
    NoRollback sent (c.advanceReceived m).reestablish := by
  have hmono := advanceReceived_counters_monotone c m
  exact ⟨Nat.le_trans h.1 hmono.1, Nat.le_trans h.2 hmono.2⟩

/-! ## 2. BOLT 2's acceptance window implies the invariant -/

/-- **Accepted reports are not rollbacks.**  BOLT 2's acceptance predicate
already forces the peer's report into the window
`lastSent ≤ reported ≤ lastSent + 1`; the lower bound is precisely
`NoRollback`. -/
theorem accepted_noRollback {sent : SentCounters} {r : ReestablishFields}
    (h : ReestablishAccepted sent r) : NoRollback sent r :=
  ⟨accepted_not_earlier h, (accepted_revocation_bounds h).1⟩

/-- An accepted report does not roll state back, in the negative form used by
the receiver decision table. -/
theorem accepted_not_rollsBack {sent : SentCounters} {r : ReestablishFields}
    (h : ReestablishAccepted sent r) : ¬ RollsBack sent r :=
  (not_rollsBack_iff_noRollback sent r).2 (accepted_noRollback h)

/-! ## 3. A receipt never rolls the local channel record back -/

/-- **Reestablish receipt law, invariantly.**  Receiving a
`channel_reestablish` leaves the addressed record's counters exactly as they
were (the model reads the report but never applies it), so a record that
satisfied the no-rollback invariant still satisfies it. -/
theorem receive_channelReestablish_noRollback
    (s s' : PeerState) (m : ChannelReestablish) (c : ChannelRecord)
    (hrecv : receive s (.channelReestablish m) = some s')
    (hfind : findChannel s m.channelId = some c)
    (sent : SentCounters) (h : NoRollback sent c.reestablish) :
    ∃ c', findChannel s' m.channelId = some c' ∧
      NoRollback sent c'.reestablish := by
  rcases receive_channelReestablish_preserves_counters s s' m c hrecv hfind with
    ⟨c', hfind', hfields⟩
  exact ⟨c', hfind', by rw [hfields]; exact h⟩

/-- **Every receipt preserves the no-rollback invariant.**  For any accepted
channel-directed message, the addressed record's counters are non-decreasing,
so the floor established by `sent` remains a floor.  Reestablish is the
special case where the counters are in fact unchanged. -/
theorem receive_noRollback
    (s s' : PeerState) (m : Msg) (cid : ChannelId) (c : ChannelRecord)
    (hrecv : receive s m = some s') (hmsg : channelId? m = some cid)
    (hfind : findChannel s cid = some c)
    (sent : SentCounters) (h : NoRollback sent c.reestablish) :
    ∃ c', findChannel s' cid = some c' ∧ NoRollback sent c'.reestablish := by
  rcases receive_counters_monotone s s' m cid c hrecv hmsg hfind with
    ⟨c', hfind', hcommit, hrevoke⟩
  exact ⟨c', hfind', Nat.le_trans h.1 hcommit, Nat.le_trans h.2 hrevoke⟩

/-! ## 4. Retransmission is counter-stable -/

/-- A reconnection interval: retained messages are re-sent (which only
overwrites the retained copy) and the peer's `channel_reestablish` is
received (which is identity on the counters).  This is exactly the activity
BOLT 2 performs between reconnects. -/
inductive RetransmitTrace : ChannelRecord → ChannelRecord → Prop where
  | refl (c : ChannelRecord) : RetransmitTrace c c
  | send {a b : ChannelRecord} (h : RetransmitTrace a b) (m : Msg) :
      RetransmitTrace a (b.recordSent m)
  | reestablish {a b : ChannelRecord} (h : RetransmitTrace a b)
      (m : ChannelReestablish) :
      RetransmitTrace a (b.advanceReceived (.channelReestablish m))

/-- **Retransmission leaves both counters exactly constant.**  Re-sending a
retained message does not touch the reported counters, and receiving the
peer's reestablish reads but never applies the report. -/
theorem retransmitTrace_counters_eq {a b : ChannelRecord}
    (h : RetransmitTrace a b) :
    b.reestablish.nextCommitmentNumber = a.reestablish.nextCommitmentNumber ∧
      b.reestablish.nextRevocationNumber = a.reestablish.nextRevocationNumber := by
  induction h with
  | refl => exact ⟨rfl, rfl⟩
  | send _ m ih =>
      exact ⟨by simpa [recordSent_reestablish] using ih.1,
        by simpa [recordSent_reestablish] using ih.2⟩
  | reestablish _ m ih =>
      exact ⟨by simpa [advanceReceived_channelReestablish] using ih.1,
        by simpa [advanceReceived_channelReestablish] using ih.2⟩

/-- **Retransmission cannot roll back acknowledged state.**  If the invariant
held before a reconnection interval, it holds after it; in fact the reported
counters did not move at all. -/
theorem retransmitTrace_noRollback {a b : ChannelRecord}
    (h : RetransmitTrace a b) (sent : SentCounters)
    (ha : NoRollback sent a.reestablish) :
    NoRollback sent b.reestablish := by
  rcases retransmitTrace_counters_eq h with ⟨hc, hr⟩
  exact ⟨by rw [hc]; exact ha.1, by rw [hr]; exact ha.2⟩

/-! ## 5. The strongest unconditional form: all activity is monotone -/

/-- Any activity on a channel record: sending any message (which only updates
the retained copy) or receiving any message (which is monotone in both
counters).  Unlike `RetransmitTrace`, this includes fresh commitments, so it
is the strongest unconditional no-rollback statement over the wave-A model. -/
inductive ChannelActivity : ChannelRecord → ChannelRecord → Prop where
  | refl (c : ChannelRecord) : ChannelActivity c c
  | send {a b : ChannelRecord} (h : ChannelActivity a b) (m : Msg) :
      ChannelActivity a (b.recordSent m)
  | recv {a b : ChannelRecord} (h : ChannelActivity a b) (m : Msg) :
      ChannelActivity a (b.advanceReceived m)

/-- Every channel activity is non-decreasing in both reported counters. -/
theorem channelActivity_counters_monotone {a b : ChannelRecord}
    (h : ChannelActivity a b) :
    a.reestablish.nextCommitmentNumber ≤ b.reestablish.nextCommitmentNumber ∧
      a.reestablish.nextRevocationNumber ≤ b.reestablish.nextRevocationNumber := by
  induction h with
  | refl => exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | send _ m ih =>
      exact ⟨by simpa [recordSent_reestablish] using ih.1,
        by simpa [recordSent_reestablish] using ih.2⟩
  | recv _ m ih =>
      exact ⟨Nat.le_trans ih.1 (advanceReceived_counters_monotone _ m).1,
        Nat.le_trans ih.2 (advanceReceived_counters_monotone _ m).2⟩

/-- **Unconditional no-rollback for the model.**  No sequence of sends and
receipts can lower either reported counter below the acknowledged floor. -/
theorem channelActivity_noRollback {a b : ChannelRecord}
    (h : ChannelActivity a b) (sent : SentCounters)
    (ha : NoRollback sent a.reestablish) :
    NoRollback sent b.reestablish := by
  have hmono := channelActivity_counters_monotone h
  exact ⟨Nat.le_trans ha.1 hmono.1, Nat.le_trans ha.2 hmono.2⟩

/-- `RetransmitTrace` is a special case of general channel activity. -/
theorem retransmitTrace_activity {a b : ChannelRecord}
    (h : RetransmitTrace a b) : ChannelActivity a b := by
  induction h with
  | refl => exact ChannelActivity.refl a
  | send _ m ih => exact ChannelActivity.send ih m
  | reestablish _ m ih => exact ChannelActivity.recv ih (.channelReestablish m)

/-! ## 6. The invariant is necessary: a mechanized rollback counterexample -/

/-- The reestablish fields of an incoming message, for comparing a report
with the last-sent floor. -/
def reportFields (m : ChannelReestablish) : ReestablishFields where
  nextCommitmentNumber := m.nextCommitmentNumber
  nextRevocationNumber := m.nextRevocationNumber
  yourLastPerCommitmentSecret := m.yourLastPerCommitmentSecret
  myCurrentPerCommitmentPoint := m.myCurrentPerCommitmentPoint

/-- A naive reestablish consumer: copy the peer's reported counters into the
record.  `receive` deliberately does *not* do this in the wave-A model; the
definition exists to state what the invariant rules out. -/
def adoptReported (c : ChannelRecord) (r : ReestablishFields) : ChannelRecord :=
  { c with
    reestablish :=
      { c.reestablish with
        nextCommitmentNumber := r.nextCommitmentNumber
        nextRevocationNumber := r.nextRevocationNumber } }

/-- The invariant is decidable, so a consumer can branch on it. -/
instance decidableNoRollback (sent : SentCounters) (r : ReestablishFields) :
    Decidable (NoRollback sent r) := by
  unfold NoRollback
  infer_instance

/-- The guarded consumer: adopt the report only when the no-rollback
invariant holds, otherwise keep the local record. -/
def adoptGuarded (sent : SentCounters) (c : ChannelRecord)
    (r : ReestablishFields) : ChannelRecord :=
  if NoRollback sent r then adoptReported c r else c

/-- A ledger whose last sent commitment is 3 and last sent revocation is 2. -/
def sampleLedger : SentCounters where
  lastCommitmentNumber := 3
  lastRevocationNumber := 2
  closingSignedReceived := false

/-- A channel that has advanced to commitment 4 / revocation 3. -/
def sampleRecord : ChannelRecord where
  channelId := ⟨ByteArray.empty⟩
  reestablish :=
    { nextCommitmentNumber := 4
      nextRevocationNumber := 3
      yourLastPerCommitmentSecret := ByteArray.empty
      myCurrentPerCommitmentPoint := ⟨ByteArray.empty⟩ }

/-- A stale report: it names commitment 1 / revocation 0. -/
def staleReport : ReestablishFields where
  nextCommitmentNumber := 1
  nextRevocationNumber := 0
  yourLastPerCommitmentSecret := ByteArray.empty
  myCurrentPerCommitmentPoint := ⟨ByteArray.empty⟩

/-- The sample record satisfies the invariant against the sample ledger. -/
theorem sampleRecord_noRollback :
    NoRollback sampleLedger sampleRecord.reestablish := by
  unfold NoRollback sampleLedger sampleRecord
  decide

/-- The stale report is exactly a rollback of the sample ledger. -/
theorem staleReport_rollsBack : RollsBack sampleLedger staleReport := by
  unfold RollsBack sampleLedger staleReport
  decide

/-- The stale report does not satisfy the invariant. -/
theorem staleReport_not_noRollback : ¬ NoRollback sampleLedger staleReport :=
  (rollsBack_iff_not_noRollback sampleLedger staleReport).1 staleReport_rollsBack

/-- **Rollback counterexample.**  Adopting the stale report without the
invariant moves the channel from commitment 4 back to commitment 1. -/
theorem adoptReported_rollsBack :
    RollsBack sampleLedger (adoptReported sampleRecord staleReport).reestablish ∧
      (adoptReported sampleRecord staleReport).reestablish.nextCommitmentNumber <
        sampleRecord.reestablish.nextCommitmentNumber := by
  constructor
  · unfold RollsBack adoptReported sampleLedger sampleRecord staleReport
    decide
  · unfold adoptReported sampleRecord staleReport
    decide

/-- **The guard restores safety.**  Guarded adoption never lowers the
acknowledged floor, for any report and any record that already satisfies the
invariant. -/
theorem adoptGuarded_noRollback {sent : SentCounters} {c : ChannelRecord}
    {r : ReestablishFields} (hc : NoRollback sent c.reestablish) :
    NoRollback sent (adoptGuarded sent c r).reestablish := by
  unfold adoptGuarded
  by_cases h : NoRollback sent r
  · rw [ite_eq_left h]
    simpa [adoptReported, NoRollback] using h
  · rw [ite_eq_right h]
    exact hc

/-- **The only permitted rewind is the unacknowledged message.**  If the
record is inside BOLT 2's window (`at most one beyond the last sent
counter`), guarded adoption can lower the commitment counter by at most one:
the single `commitment_signed` that must be retransmitted.  Acknowledged
state, represented by the last-sent floor, is never crossed. -/
theorem adoptGuarded_commitment_rewind_at_most_one
    {sent : SentCounters} {c : ChannelRecord} {r : ReestablishFields}
    (hc : NoRollback sent c.reestablish)
    (hwindow : c.reestablish.nextCommitmentNumber ≤ sent.lastCommitmentNumber + 1)
    (hr : NoRollback sent r) :
    c.reestablish.nextCommitmentNumber ≤
      (adoptGuarded sent c r).reestablish.nextCommitmentNumber + 1 := by
  have hc1 : sent.lastCommitmentNumber ≤ c.reestablish.nextCommitmentNumber := hc.1
  have hr1 : sent.lastCommitmentNumber ≤ r.nextCommitmentNumber := hr.1
  unfold adoptGuarded
  by_cases h : NoRollback sent r
  · rw [ite_eq_left h]
    simp [adoptReported]
    omega
  · rw [ite_eq_right h]
    omega

/-- The revocation-counter form of
`adoptGuarded_commitment_rewind_at_most_one`. -/
theorem adoptGuarded_revocation_rewind_at_most_one
    {sent : SentCounters} {c : ChannelRecord} {r : ReestablishFields}
    (hc : NoRollback sent c.reestablish)
    (hwindow : c.reestablish.nextRevocationNumber ≤ sent.lastRevocationNumber + 1)
    (hr : NoRollback sent r) :
    c.reestablish.nextRevocationNumber ≤
      (adoptGuarded sent c r).reestablish.nextRevocationNumber + 1 := by
  have hc2 : sent.lastRevocationNumber ≤ c.reestablish.nextRevocationNumber := hc.2
  have hr2 : sent.lastRevocationNumber ≤ r.nextRevocationNumber := hr.2
  unfold adoptGuarded
  by_cases h : NoRollback sent r
  · rw [ite_eq_left h]
    simp [adoptReported]
    omega
  · rw [ite_eq_right h]
    omega

/-- A concrete peer with one channel at commitment 4 / revocation 3. -/
def samplePeer : PeerState where
  identity := ⟨ByteArray.empty⟩
  transport := .up
  handshake := HandshakeState.initial
  channels := [sampleRecord]

/-- The stale report as a wire message. -/
def staleMessage : ChannelReestablish where
  channelId := sampleRecord.channelId
  nextCommitmentNumber := staleReport.nextCommitmentNumber
  nextRevocationNumber := staleReport.nextRevocationNumber
  yourLastPerCommitmentSecret := staleReport.yourLastPerCommitmentSecret
  myCurrentPerCommitmentPoint := staleReport.myCurrentPerCommitmentPoint

/-- `findChannel` locates the sample record.  The computation is explicit
because `ChannelId` derives `BEq` rather than `DecidableEq`. -/
theorem samplePeer_findChannel :
    findChannel samplePeer sampleRecord.channelId = some sampleRecord := by
  unfold findChannel samplePeer
  have hbeq : (sampleRecord.channelId == sampleRecord.channelId) = true := by
    unfold sampleRecord
    change LnLean.instBEqChannelId.beq
      { bytes := ByteArray.empty } { bytes := ByteArray.empty } = true
    rw [LnLean.instBEqChannelId.beq]
    change ByteArray.beq ByteArray.empty ByteArray.empty = true
    rw [ByteArray.beq]
    simp
  simp [hbeq]

/-- `receive` accepts a `channel_reestablish` without consulting the
no-rollback invariant. -/
theorem receive_channelReestablish_accepts
    (s : PeerState) (m : ChannelReestablish) (c : ChannelRecord)
    (ht : s.transport = .up) (hf : findChannel s m.channelId = some c) :
    receive s (.channelReestablish m) =
      some (updateChannel s m.channelId
        (fun _ => c.advanceReceived (.channelReestablish m))) := by
  unfold receive
  rw [ht]
  simp [receiveEvent?, channelId?, hf]

/-- **Model gap, as a theorem.**  The transition system accepts a stale
report that `RollsBack` the last-sent counters, because it has no invariant
check.  The report is discarded rather than applied, so the local record does
not move; the danger is exactly a consumer that adopts it (previous theorem). -/
theorem receive_accepts_stale_report :
    ∃ s' : PeerState,
      receive samplePeer (.channelReestablish staleMessage) = some s' ∧
        findChannel samplePeer staleMessage.channelId = some sampleRecord ∧
          RollsBack sampleLedger (reportFields staleMessage) := by
  refine ⟨updateChannel samplePeer staleMessage.channelId
      (fun _ => sampleRecord.advanceReceived (.channelReestablish staleMessage)),
    ?_, ?_⟩
  · exact receive_channelReestablish_accepts samplePeer staleMessage sampleRecord
      rfl samplePeer_findChannel
  · exact ⟨samplePeer_findChannel, by
      unfold RollsBack reportFields staleMessage sampleLedger staleReport
      decide⟩

end LnLean.Proofs.ModelHardening.F12
