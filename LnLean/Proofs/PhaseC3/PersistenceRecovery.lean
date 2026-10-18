import LnLean

/-!
# LnLean.Proofs.PhaseC3.PersistenceRecovery

## English claim

This module models channel persistence as a **snapshot** of the values that a
restarted node must not lose: the two commitment counters
(`localCommitmentNumber`, `remoteCommitmentNumber`), the live HTLC set, and the
`channel_ready` ("ready") flag.  A crash/restart is described by a
`RecoveryPoint`: a history is split into a persisted prefix and an in-memory
suffix, and the snapshot is the persisted projection of the state after the
prefix.

The module proves:

1. **Replay is associative.**  Replaying `l₁ ++ l₂` is replaying `l₁` and then
   `l₂` (`replay_append`), and replaying the empty suffix is the identity.
2. **Restore then replay equals full replay.**  If a snapshot is *consistent*
   with the state after the persisted prefix, then restoring it and replaying
   the suffix yields exactly the counters, HTLC set, and ready flag of
   replaying the whole history (`restore_replay_suffix`,
   `RecoveryPoint.replays_full_history`).
3. **Recovery never rolls back.**  Replaying any suffix only increases the two
   counters and can only turn the ready flag from `false` to `true`
   (`replay_no_rollback`).  If the snapshot is consistent with a channel state
   that is `Reachable` from an earlier state, the snapshot counters dominate
   the earlier counters (`recovery_no_rollback_committed`).  Replaying inbound
   messages over the restored `ChannelRecord` never lowers either reported
   BOLT 2 counter (`recovery_no_rollback_reestablish`).
4. **Retransmission survives recovery.**  The `channel_ready` retained before
   the crash is still the message `lastSent` returns after restoring the
   snapshot and consuming any reconnect inbox
   (`recovery_retains_channelReady`).
5. **The consistency precondition is necessary.**  An inconsistent
   ("torn"/stale) snapshot can store a smaller commitment counter than the
   live channel (`inconsistent_snapshot_rolls_back`).

The snapshot-consistency precondition is the proposition
`Snapshot.Consistent s c r`, defined as `s = Snapshot.ofChannelRecord c r`; it
is an explicit hypothesis of every recovery theorem, never an axiom.  The
HTLC message-to-record effect is the explicit structure `HtlcEffect`, and the
durability assumption ("the snapshot was taken atomically after exactly the
persisted prefix") is the field `RecoveryPoint.consistent`.

## BOLT sections (pinned BOLTs `1aadb71`)

* BOLT 2 §"Message Retransmission", `refs/bolts/02-peer-protocol.md:3352-3635`:
  the four `channel_reestablish` counters (`:3374-3395`), the sender
  requirements (`:3449-3462`), and the receiver decision table
  (`:3483-3517`).
* BOLT 2 §"The `channel_ready` Message", `02-peer-protocol.md:1045-1048`:
  `channel_ready` is the current name of `funding_locked`; once both sides
  have sent it, the channel enters normal operation.
* BOLT 2 §"Data Loss Protect", `02-peer-protocol.md:3454-3459`: the
  last revealed per-commitment secret is reported when
  `next_revocation_number ≠ 0`.
* BOLT 5 §"Revoked Transaction Close Handling",
  `refs/bolts/05-onchain.md:1-120` (the on-chain state must be recoverable from
  persisted data); the module only uses the *off-chain* counter part.

## rust-lightning anchors (pinned commit `fe49009`)

* `lightning/src/chain/channelmonitor.rs:14`: channel monitor state
  "MUST be persisted to disk ... before progress can be made".
* `lightning/src/chain/channelmonitor.rs:1595` `write_chanmon_internal`:
  the serialization entry point for persisted monitor state.
* `lightning/src/ln/channel.rs:10826` `Channel::channel_reestablish` and
  `:13135` `get_channel_reestablish`: the receive/send halves of the counter
  protocol that the snapshot stores.
* `lightning/src/ln/channelmanager.rs:13994`
  `internal_channel_reestablish`: the dispatcher that resumes a channel after
  reconnect.
* `lightning/src/ln/channel.rs:11126-11134`
  `both_sides_on_initial_commitment_number`: the `channel_ready` resend
  condition.

## What is NOT modelled

* **Crash atomicity.**  `RecoveryPoint.consistent` is a hypothesis: the
  module proves the *consequence* of an atomic snapshot, not that a filesystem
  write is atomic.  A torn or stale snapshot is a distinct failure mode; it is
  exhibited by `inconsistent_snapshot_rolls_back`.
* **On-disk format and integrity.**  There is no serialization, checksum,
  version tag, or `channel_reestablish` wire parsing.  `Snapshot` is a Lean
  structure; `LnLean.Protocol.Messages` and `LnLean.Wire` own the wire layer.
* **Message-to-event bridge.**  `LnLean.Proofs.Liveness` explicitly does not
  map `Msg` to `ProtocolEvent`, so `ready = true` is not proved to imply
  `Channel.phase = normal`; `ready_snapshot_reaches_normal` states the
  conditional form with the bridge as a hypothesis.
* **HTLC identity.**  `HTLC` has no `htlcId` field (it is not in the wave-A
  record), so `HtlcEffect.fulfill` / `fail` are parameterized by the message
  id and may be coarse.  The refinement to "only the addressed HTLC changes"
  is recorded in the report as an obligation on the user of `HtlcEffect`.
* No timers, retransmission scheduling, fsync, watchtowers, or L1 recovery.
-/

namespace LnLean.Proofs.PhaseC3

set_option autoImplicit false

open LnLean
open LnLean.Channel
open LnLean.Protocol (ChannelRecord Msg MsgKind ReestablishFields
  CommitmentSigned RevokeAndAck UpdateAddHtlc)

/-! ## 1. The persisted projection

A snapshot is deliberately *small*: exactly the counters, the HTLC set, and
the ready flag.  Static channel data (funding outpoint, keys, parameters) is
assumed to be recovered from the channel announcement / `open_channel` replay
and is not part of this projection. -/

/-- The persisted projection of a channel and its peer record.  The ready
flag is `lastChannelReady.isSome`, i.e. "a `channel_ready` is retained for
retransmission" (BOLT 2 §"Message Retransmission"). -/
structure Persisted where
  /-- `Channel.localCommitmentNumber` at the snapshot point. -/
  localCommitmentNumber : Nat
  /-- `Channel.remoteCommitmentNumber` at the snapshot point. -/
  remoteCommitmentNumber : Nat
  /-- The live HTLC set at the snapshot point. -/
  htlcs : List HTLC
  /-- Whether a `channel_ready` is retained. -/
  ready : Bool
deriving Repr

namespace Persisted

/-- Project a live channel plus its peer record onto the persisted state. -/
def ofChannelRecord (c : Channel) (r : ChannelRecord) : Persisted where
  localCommitmentNumber := c.localCommitmentNumber
  remoteCommitmentNumber := c.remoteCommitmentNumber
  htlcs := c.htlcs
  ready := r.lastChannelReady.isSome

@[simp] theorem ofChannelRecord_local (c : Channel) (r : ChannelRecord) :
    (ofChannelRecord c r).localCommitmentNumber = c.localCommitmentNumber := rfl

@[simp] theorem ofChannelRecord_remote (c : Channel) (r : ChannelRecord) :
    (ofChannelRecord c r).remoteCommitmentNumber = c.remoteCommitmentNumber := rfl

@[simp] theorem ofChannelRecord_htlcs (c : Channel) (r : ChannelRecord) :
    (ofChannelRecord c r).htlcs = c.htlcs := rfl

@[simp] theorem ofChannelRecord_ready (c : Channel) (r : ChannelRecord) :
    (ofChannelRecord c r).ready = r.lastChannelReady.isSome := rfl

end Persisted

/-- A serialized snapshot of the persisted projection.  It has the same
fields as `Persisted`; keeping a separate structure makes the "take a
snapshot / restore a snapshot" boundary visible in theorem statements. -/
structure Snapshot where
  localCommitmentNumber : Nat
  remoteCommitmentNumber : Nat
  htlcs : List HTLC
  ready : Bool
deriving Repr

namespace Snapshot

/-- Take a snapshot of a persisted projection. -/
def ofPersisted (p : Persisted) : Snapshot where
  localCommitmentNumber := p.localCommitmentNumber
  remoteCommitmentNumber := p.remoteCommitmentNumber
  htlcs := p.htlcs
  ready := p.ready

/-- Take a snapshot directly from a live channel and its peer record. -/
def ofChannelRecord (c : Channel) (r : ChannelRecord) : Snapshot :=
  ofPersisted (Persisted.ofChannelRecord c r)

/-- Restore a snapshot to the persisted projection. -/
def restore (s : Snapshot) : Persisted where
  localCommitmentNumber := s.localCommitmentNumber
  remoteCommitmentNumber := s.remoteCommitmentNumber
  htlcs := s.htlcs
  ready := s.ready

/-- Restore the persisted counters and the HTLC set into a live channel.
Static fields, the phase, and the balances are left at their live values; the
snapshot never overwrites them. -/
def restoreChannel (s : Snapshot) (c : Channel) : Channel :=
  { c with
    localCommitmentNumber := s.localCommitmentNumber
    remoteCommitmentNumber := s.remoteCommitmentNumber
    htlcs := s.htlcs }

/-- Restore the ready flag into a peer record.  If the snapshot says "not
ready", any live retained `channel_ready` is dropped (a restarted node with
no persisted ready message must not pretend to have one); if it says "ready",
the live retained message is kept because the snapshot does not store the
wire bytes. -/
def restoreRecord (s : Snapshot) (r : ChannelRecord) : ChannelRecord :=
  { r with lastChannelReady := if s.ready then r.lastChannelReady else none }

/-- **Snapshot-consistency precondition.**  A snapshot is consistent with a
live channel/record pair exactly when it is the persisted projection of that
pair.  Every recovery theorem carries this as an explicit hypothesis. -/
def Consistent (s : Snapshot) (c : Channel) (r : ChannelRecord) : Prop :=
  s = ofChannelRecord c r

theorem consistent_iff (s : Snapshot) (c : Channel) (r : ChannelRecord) :
    s.Consistent c r ↔ s = ofChannelRecord c r := Iff.rfl

theorem consistent_local {s : Snapshot} {c : Channel} {r : ChannelRecord}
    (h : s.Consistent c r) :
    s.localCommitmentNumber = c.localCommitmentNumber := by
  rw [h]
  rfl

theorem consistent_remote {s : Snapshot} {c : Channel} {r : ChannelRecord}
    (h : s.Consistent c r) :
    s.remoteCommitmentNumber = c.remoteCommitmentNumber := by
  rw [h]
  rfl

theorem consistent_htlcs {s : Snapshot} {c : Channel} {r : ChannelRecord}
    (h : s.Consistent c r) : s.htlcs = c.htlcs := by
  rw [h]
  rfl

theorem consistent_ready {s : Snapshot} {c : Channel} {r : ChannelRecord}
    (h : s.Consistent c r) : s.ready = r.lastChannelReady.isSome := by
  rw [h]
  rfl

/-- A snapshot round-trips through its persisted projection. -/
theorem ofPersisted_restore (s : Snapshot) :
    ofPersisted s.restore = s := by
  cases s
  rfl

/-- Restoring a projection loses nothing. -/
@[simp] theorem restore_ofPersisted (p : Persisted) :
    (ofPersisted p).restore = p := rfl

/-- Restoring a consistent snapshot into the live channel is the identity on
the persisted fields. -/
theorem restoreChannel_of_consistent {s : Snapshot} {c : Channel}
    {r : ChannelRecord} (h : s.Consistent c r) :
    s.restoreChannel c = c := by
  subst h
  simp [restoreChannel, ofChannelRecord, ofPersisted,
    Persisted.ofChannelRecord]

/-- A record update that writes back the current value is the identity. -/
theorem ChannelRecord.update_lastChannelReady_self (r : ChannelRecord)
    (x : Option Msg) (h : r.lastChannelReady = x) :
    ({ r with lastChannelReady := x } : ChannelRecord) = r := by
  rw [← h]

/-- Restoring a consistent snapshot into the peer record is the identity. -/
theorem restoreRecord_of_consistent {s : Snapshot} {c : Channel}
    {r : ChannelRecord} (h : s.Consistent c r) :
    s.restoreRecord r = r := by
  subst h
  unfold restoreRecord ofChannelRecord ofPersisted
    Persisted.ofChannelRecord
  cases hr : r.lastChannelReady with
  | none => exact ChannelRecord.update_lastChannelReady_self r none hr
  | some m => exact ChannelRecord.update_lastChannelReady_self r (some m) hr

end Snapshot

/-! ## 2. Message replay

The HTLC part of a message effect is a parameter: `HTLC` does not carry an
`htlcId`, so the mapping from `update_*_htlc` messages to the live set is a
modelling bridge.  It is an explicit structure field, not an axiom. -/

/-- The modelled effect of the three HTLC messages on the persisted HTLC
set.  `ofAdd` builds the record inserted by `update_add_htlc`; `fulfill` and
`fail` receive the wire `htlcId`. -/
structure HtlcEffect where
  ofAdd : UpdateAddHtlc → HTLC
  fulfill : Nat → List HTLC → List HTLC
  fail : Nat → List HTLC → List HTLC

namespace HtlcEffect

/-- The natural coarse effect: an inbound add becomes a `received` HTLC and a
fulfil/fail rewrites the state of every live HTLC.  The latter is intentionally
coarse because the wave-A `HTLC` record has no identifier; see the module
docstring. -/
def basic : HtlcEffect where
  ofAdd := fun u =>
    { direction := Direction.remote
      amount := ⟨u.amountMsat.val⟩
      paymentHash := u.paymentHash
      cltvExpiry := u.cltvExpiry
      state := HTLCState.received }
  fulfill := fun _ hs => hs.map (fun h => { h with state := HTLCState.fulfilled })
  fail := fun _ hs => hs.map (fun h => { h with state := HTLCState.failed })

end HtlcEffect

/-- Apply one inbound message to the persisted projection.  Only messages
that change the persisted fields have an effect; all other traffic is
observationally irrelevant to recovery.  The phase guards of BOLT 2 are
assumed to have been checked by the peer layer before the message reaches
this executor. -/
def applyMsg (eff : HtlcEffect) (p : Persisted) : Msg → Persisted
  | .commitmentSigned _ =>
      { p with remoteCommitmentNumber := p.remoteCommitmentNumber + 1 }
  | .revokeAndAck _ =>
      { p with localCommitmentNumber := p.localCommitmentNumber + 1 }
  | .channelReady _ => { p with ready := true }
  | .updateAddHtlc u => { p with htlcs := p.htlcs ++ [eff.ofAdd u] }
  | .updateFulfillHtlc u => { p with htlcs := eff.fulfill u.htlcId p.htlcs }
  | .updateFailHtlc u => { p with htlcs := eff.fail u.htlcId p.htlcs }
  | _ => p

/-- Replay a finite list of inbound messages over a persisted projection. -/
def replay (eff : HtlcEffect) (msgs : List Msg) (p : Persisted) : Persisted :=
  msgs.foldl (applyMsg eff) p

@[simp] theorem replay_nil (eff : HtlcEffect) (p : Persisted) :
    replay eff [] p = p := rfl

theorem replay_cons (eff : HtlcEffect) (m : Msg) (ms : List Msg)
    (p : Persisted) :
    replay eff (m :: ms) p = replay eff ms (applyMsg eff p m) := rfl

/-- **Replay associativity.**  A history split into a prefix and a suffix
replays as the prefix followed by the suffix. -/
theorem replay_append (eff : HtlcEffect) (l₁ l₂ : List Msg) (p : Persisted) :
    replay eff (l₁ ++ l₂) p = replay eff l₂ (replay eff l₁ p) := by
  simp [replay, List.foldl_append]

/-- A one-message replay is exactly one effect step. -/
@[simp] theorem replay_singleton (eff : HtlcEffect) (m : Msg) (p : Persisted) :
    replay eff [m] p = applyMsg eff p m := by
  simp [replay]

/-! ## 3. Monotonicity: recovery cannot roll back -/

theorem applyMsg_local_ge (eff : HtlcEffect) (p : Persisted) (m : Msg) :
    p.localCommitmentNumber ≤ (applyMsg eff p m).localCommitmentNumber := by
  cases m <;> simp [applyMsg] <;> omega

theorem applyMsg_remote_ge (eff : HtlcEffect) (p : Persisted) (m : Msg) :
    p.remoteCommitmentNumber ≤ (applyMsg eff p m).remoteCommitmentNumber := by
  cases m <;> simp [applyMsg] <;> omega

theorem applyMsg_ready (eff : HtlcEffect) (p : Persisted) (m : Msg)
    (h : p.ready = true) : (applyMsg eff p m).ready = true := by
  cases m <;> simp [applyMsg, h]

/-- Replaying any suffix never lowers the local commitment counter. -/
theorem replay_local_ge (eff : HtlcEffect) (msgs : List Msg) (p : Persisted) :
    p.localCommitmentNumber ≤ (replay eff msgs p).localCommitmentNumber := by
  induction msgs generalizing p with
  | nil => simp
  | cons m ms ih =>
      simp only [replay, List.foldl_cons]
      exact Nat.le_trans (applyMsg_local_ge eff p m) (ih (applyMsg eff p m))

/-- Replaying any suffix never lowers the remote commitment counter. -/
theorem replay_remote_ge (eff : HtlcEffect) (msgs : List Msg) (p : Persisted) :
    p.remoteCommitmentNumber ≤ (replay eff msgs p).remoteCommitmentNumber := by
  induction msgs generalizing p with
  | nil => simp
  | cons m ms ih =>
      simp only [replay, List.foldl_cons]
      exact Nat.le_trans (applyMsg_remote_ge eff p m) (ih (applyMsg eff p m))

/-- A ready flag that is set before a replay stays set afterwards. -/
theorem replay_ready (eff : HtlcEffect) (msgs : List Msg) (p : Persisted)
    (h : p.ready = true) : (replay eff msgs p).ready = true := by
  induction msgs generalizing p with
  | nil => simpa using h
  | cons m ms ih =>
      simp only [replay, List.foldl_cons]
      exact ih (applyMsg eff p m) (applyMsg_ready eff p m h)

/-- **No-rollback bundle.**  Counters are monotone and the ready flag is
sticky in the `true` direction. -/
theorem replay_no_rollback (eff : HtlcEffect) (msgs : List Msg) (p : Persisted) :
    p.localCommitmentNumber ≤ (replay eff msgs p).localCommitmentNumber ∧
      p.remoteCommitmentNumber ≤ (replay eff msgs p).remoteCommitmentNumber ∧
      (p.ready = true → (replay eff msgs p).ready = true) :=
  ⟨replay_local_ge eff msgs p,
    replay_remote_ge eff msgs p,
    replay_ready eff msgs p⟩

/-! ## 4. Snapshot + suffix equals full history -/

/-- **Restore-and-replay theorem (hypothesis form).**  If `s` is the snapshot
of the state after the persisted prefix `pre`, then replaying `post` from the
restored snapshot is replaying `pre ++ post` from the initial state.  The
hypothesis `hcons` is the explicit snapshot-consistency precondition. -/
theorem restore_replay_suffix {eff : HtlcEffect} {init : Persisted}
    {pre post : List Msg} {s : Snapshot}
    (hcons : s = Snapshot.ofPersisted (replay eff pre init)) :
    replay eff post s.restore = replay eff (pre ++ post) init := by
  rw [hcons, Snapshot.restore_ofPersisted, ← replay_append]

/-- The recovered state has the same counters as the full replay. -/
theorem recover_counters_eq {eff : HtlcEffect} {init : Persisted}
    {pre post : List Msg} {s : Snapshot}
    (hcons : s = Snapshot.ofPersisted (replay eff pre init)) :
    (replay eff post s.restore).localCommitmentNumber =
        (replay eff (pre ++ post) init).localCommitmentNumber ∧
      (replay eff post s.restore).remoteCommitmentNumber =
        (replay eff (pre ++ post) init).remoteCommitmentNumber := by
  rw [restore_replay_suffix hcons]
  exact ⟨rfl, rfl⟩

/-- The recovered state has the same HTLC set as the full replay. -/
theorem recover_htlcs_eq {eff : HtlcEffect} {init : Persisted}
    {pre post : List Msg} {s : Snapshot}
    (hcons : s = Snapshot.ofPersisted (replay eff pre init)) :
    (replay eff post s.restore).htlcs =
      (replay eff (pre ++ post) init).htlcs := by
  rw [restore_replay_suffix hcons]

/-- The recovered state has the same ready flag as the full replay. -/
theorem recover_ready_eq {eff : HtlcEffect} {init : Persisted}
    {pre post : List Msg} {s : Snapshot}
    (hcons : s = Snapshot.ofPersisted (replay eff pre init)) :
    (replay eff post s.restore).ready =
      (replay eff (pre ++ post) init).ready := by
  rw [restore_replay_suffix hcons]

/-- Restoring a snapshot consistent with the persisted prefix cannot lower
the prefix's committed local counter. -/
theorem recovery_no_rollback_suffix {eff : HtlcEffect} {init : Persisted}
    {pre post : List Msg} {s : Snapshot}
    (hcons : s = Snapshot.ofPersisted (replay eff pre init)) :
    (replay eff pre init).localCommitmentNumber ≤
      (replay eff post s.restore).localCommitmentNumber := by
  have hle := replay_local_ge eff post s.restore
  rw [hcons, Snapshot.restore_ofPersisted] at hle ⊢
  exact hle

/-- **The persisted-recovery point.**  This is the explicit durability
bridge: `pre` is the part of the history that reached stable storage, `post`
is in memory at the crash, and `consistent` records that the snapshot is
exactly the persisted projection after the prefix. -/
structure RecoveryPoint (eff : HtlcEffect) (init : Persisted) where
  pre : List Msg
  post : List Msg
  snapshot : Snapshot
  /-- Atomic-snapshot assumption, as data rather than an axiom. -/
  consistent : snapshot = Snapshot.ofPersisted (replay eff pre init)

namespace RecoveryPoint

/-- **Main recovery theorem.**  Restart from the snapshot and replay the
in-memory suffix: the resulting persisted state is exactly the state obtained
by replaying the full history. -/
theorem replays_full_history {eff : HtlcEffect} {init : Persisted}
    (rp : RecoveryPoint eff init) :
    replay eff rp.post rp.snapshot.restore =
      replay eff (rp.pre ++ rp.post) init :=
  restore_replay_suffix rp.consistent

/-- Component form: both counters after recovery equal the full-history
counters. -/
theorem counters_eq {eff : HtlcEffect} {init : Persisted}
    (rp : RecoveryPoint eff init) :
    (replay eff rp.post rp.snapshot.restore).localCommitmentNumber =
        (replay eff (rp.pre ++ rp.post) init).localCommitmentNumber ∧
      (replay eff rp.post rp.snapshot.restore).remoteCommitmentNumber =
        (replay eff (rp.pre ++ rp.post) init).remoteCommitmentNumber :=
  recover_counters_eq rp.consistent

/-- Component form: the HTLC set after recovery equals the full-history
HTLC set. -/
theorem htlcs_eq {eff : HtlcEffect} {init : Persisted}
    (rp : RecoveryPoint eff init) :
    (replay eff rp.post rp.snapshot.restore).htlcs =
      (replay eff (rp.pre ++ rp.post) init).htlcs :=
  recover_htlcs_eq rp.consistent

/-- Component form: the ready flag after recovery equals the full-history
ready flag. -/
theorem ready_eq {eff : HtlcEffect} {init : Persisted}
    (rp : RecoveryPoint eff init) :
    (replay eff rp.post rp.snapshot.restore).ready =
      (replay eff (rp.pre ++ rp.post) init).ready :=
  recover_ready_eq rp.consistent

end RecoveryPoint

/-! ## 5. No rollback against a committed channel state -/

/-- **No rollback of a committed counter.**  If a snapshot is consistent with
a channel state `b` reachable from `a`, then neither commitment counter in `a`
is larger than the corresponding snapshot counter.  This is the theorem that
rules out restoring an old but *consistent* snapshot over a later state. -/
theorem recovery_no_rollback_committed {a b : Channel} {r : ChannelRecord}
    {s : Snapshot} (hreach : Reachable a b) (hcons : s.Consistent b r) :
    a.localCommitmentNumber ≤ s.localCommitmentNumber ∧
      a.remoteCommitmentNumber ≤ s.remoteCommitmentNumber := by
  have hl := Reachable.localCommitmentNumber_le hreach
  have hr := Reachable.remoteCommitmentNumber_le hreach
  rw [Snapshot.consistent_local hcons]
  rw [Snapshot.consistent_remote hcons]
  exact ⟨hl, hr⟩

/-- A snapshot is stale exactly when it misses a state reachable from it. -/
def Stale (s : Snapshot) (c : Channel) (r : ChannelRecord) : Prop :=
  s.Consistent c r ∧ ∃ c', Reachable c c' ∧
    c'.localCommitmentNumber > s.localCommitmentNumber

/-- A stale but consistent snapshot would roll the counter back; the
consistency precondition alone is therefore not enough across time.  The
recovery point must name the *latest* persisted prefix. -/
theorem stale_snapshot_rolls_back {s : Snapshot} {c : Channel}
    {r : ChannelRecord} (h : Stale s c r) :
    ∃ c', Reachable c c' ∧
      c'.localCommitmentNumber > s.localCommitmentNumber :=
  h.2

/-! ## 6. Replaying inbound messages over the restored peer record -/

/-- Replay a reconnect inbox over a `ChannelRecord`.  This is the same fold as
`LnLean.Proofs.Liveness.foldl_advanceReceived_lastSent`. -/
def recordReplay (inbox : List Msg) (r : ChannelRecord) : ChannelRecord :=
  inbox.foldl ChannelRecord.advanceReceived r

/-- Inbox replay is associative. -/
theorem recordReplay_append (l₁ l₂ : List Msg) (r : ChannelRecord) :
    recordReplay (l₁ ++ l₂) r = recordReplay l₂ (recordReplay l₁ r) := by
  simp [recordReplay, List.foldl_append]

/-- `advanceReceived` never touches the retained ready message. -/
theorem advanceReceived_lastChannelReady (r : ChannelRecord) (m : Msg) :
    (r.advanceReceived m).lastChannelReady = r.lastChannelReady := by
  unfold ChannelRecord.advanceReceived
  split
  · rfl
  · split <;> rfl
  · rfl

/-- Inbox replay never touches the retained ready message. -/
theorem recordReplay_lastChannelReady (inbox : List Msg) (r : ChannelRecord) :
    (recordReplay inbox r).lastChannelReady = r.lastChannelReady := by
  induction inbox generalizing r with
  | nil => rfl
  | cons m ms ih =>
      change (recordReplay ms (r.advanceReceived m)).lastChannelReady =
        r.lastChannelReady
      rw [ih (r.advanceReceived m), advanceReceived_lastChannelReady]

/-- Inbox replay never lowers the reported `next_commitment_number`. -/
theorem recordReplay_nextCommitment_ge (inbox : List Msg) (r : ChannelRecord) :
    r.reestablish.nextCommitmentNumber ≤
      (recordReplay inbox r).reestablish.nextCommitmentNumber := by
  induction inbox generalizing r with
  | nil => simp [recordReplay]
  | cons m ms ih =>
      simp only [recordReplay, List.foldl_cons]
      exact Nat.le_trans
        (LnLean.Proofs.Protocol.advanceReceived_nextCommitment_ge r m)
        (ih (r.advanceReceived m))

/-- Inbox replay never lowers the reported `next_revocation_number`. -/
theorem recordReplay_nextRevocation_ge (inbox : List Msg) (r : ChannelRecord) :
    r.reestablish.nextRevocationNumber ≤
      (recordReplay inbox r).reestablish.nextRevocationNumber := by
  induction inbox generalizing r with
  | nil => simp [recordReplay]
  | cons m ms ih =>
      simp only [recordReplay, List.foldl_cons]
      exact Nat.le_trans
        (LnLean.Proofs.Protocol.advanceReceived_nextRevocation_ge r m)
        (ih (r.advanceReceived m))

/-- **No rollback of the BOLT 2 reestablish counters.**  Restoring a snapshot
consistent with the crashed record and consuming any reconnect inbox leaves
both reported counters at or above the snapshot's record values. -/
theorem recovery_no_rollback_reestablish {s : Snapshot} {c : Channel}
    {r : ChannelRecord} (hcons : s.Consistent c r) (inbox : List Msg) :
    r.reestablish.nextCommitmentNumber ≤
        (recordReplay inbox (s.restoreRecord r)).reestablish.nextCommitmentNumber ∧
      r.reestablish.nextRevocationNumber ≤
        (recordReplay inbox (s.restoreRecord r)).reestablish.nextRevocationNumber := by
  rw [s.restoreRecord_of_consistent hcons]
  exact ⟨recordReplay_nextCommitment_ge inbox r,
    recordReplay_nextRevocation_ge inbox r⟩

/-- **Retransmission survives recovery.**  A `channel_ready` retained before
the crash is still exactly what `lastSent` returns after restoring the
snapshot and consuming the reconnect inbox.  This composes the persistence
layer with `LnLean.Proofs.Liveness.reconnect_preserves_channelReady`. -/
theorem recovery_retains_channelReady {s : Snapshot} {c : Channel}
    {r : ChannelRecord} (hcons : s.Consistent c r) (m : Msg)
    (hm : r.lastChannelReady = some m) (inbox : List Msg) :
    (recordReplay inbox (s.restoreRecord r)).lastSent MsgKind.channelReady =
      some m := by
  rw [s.restoreRecord_of_consistent hcons]
  simpa [recordReplay] using
    LnLean.Proofs.Liveness.reconnect_preserves_channelReady r m hm inbox

/-- After restoring a snapshot whose ready flag is set, the resulting record
still carries a concrete ready message. -/
theorem recovery_ready_message_exists {s : Snapshot} {c : Channel}
    {r : ChannelRecord} (hcons : s.Consistent c r) (hready : s.ready = true) :
    ∃ m : Msg, (s.restoreRecord r).lastChannelReady = some m := by
  have hsome : r.lastChannelReady.isSome = true := by
    rw [← Snapshot.consistent_ready hcons]
    exact hready
  rw [s.restoreRecord_of_consistent hcons]
  cases hr : r.lastChannelReady with
  | none => simp [hr] at hsome
  | some _ => exact ⟨_, rfl⟩

/-! ## 7. The precondition is necessary -/

/-- **A torn/stale snapshot is not harmless.**  If the snapshot is
inconsistent with the live channel it can carry a strictly smaller committed
counter.  This is why every theorem above assumes `Snapshot.Consistent`. -/
theorem inconsistent_snapshot_rolls_back :
    ∃ (c : Channel) (r : ChannelRecord) (s : Snapshot),
      ¬ s.Consistent c r ∧ s.localCommitmentNumber < c.localCommitmentNumber := by
  let c : Channel :=
    { LnLean.Proofs.Protocol.sampleChannel with localCommitmentNumber := 1 }
  let r : ChannelRecord :=
    { channelId := c.channelId, reestablish := ReestablishFields.initial }
  let s : Snapshot :=
    { localCommitmentNumber := 0, remoteCommitmentNumber := 0,
      htlcs := [], ready := false }
  refine ⟨c, r, s, ?_, by simp [s, c]⟩
  intro hcons
  have hl := Snapshot.consistent_local hcons
  simp [s, c] at hl

/-! ## 8. Bridges to the existing state machine -/

/-- The persisted effect of `commitment_signed` agrees with the protocol
`Step` that advances the remote commitment number. -/
theorem applyMsg_commitmentSigned_refines_step (eff : HtlcEffect) (c : Channel)
    (r : ChannelRecord) (m : CommitmentSigned)
    (hphase : c.phase = ChannelPhase.normal) :
    ∃ c', Step c ProtocolEvent.commitmentSigned c' ∧
      (applyMsg eff (Persisted.ofChannelRecord c r) (.commitmentSigned m)).remoteCommitmentNumber =
        c'.remoteCommitmentNumber :=
  ⟨{ c with remoteCommitmentNumber := c.remoteCommitmentNumber + 1 },
    Step.commitmentSigned c hphase, rfl⟩

/-- The persisted effect of `revoke_and_ack` agrees with the protocol `Step`
that advances the local commitment number. -/
theorem applyMsg_revokeAndAck_refines_step (eff : HtlcEffect) (c : Channel)
    (r : ChannelRecord) (m : RevokeAndAck)
    (hphase : c.phase = ChannelPhase.normal) :
    ∃ c', Step c ProtocolEvent.revokeAndAck c' ∧
      (applyMsg eff (Persisted.ofChannelRecord c r) (.revokeAndAck m)).localCommitmentNumber =
        c'.localCommitmentNumber :=
  ⟨{ c with localCommitmentNumber := c.localCommitmentNumber + 1 },
    Step.revokeAndAck c hphase, rfl⟩

/-- **Conditional ready-to-normal bridge.**  `LnLean.Proofs.Liveness` does not
map `Msg.channelReady` to `ProtocolEvent.fundingLocked`.  If a caller supplies
that bridge as the hypothesis `hbridge`, a ready snapshot completes lock-in
legally.  The bridge is a theorem hypothesis, never an axiom. -/
theorem ready_snapshot_reaches_normal (s : Snapshot) (c : Channel)
    (hbridge : s.ready = true → c.phase = ChannelPhase.awaitingLockin)
    (hready : s.ready = true) :
    ∃ c', Step c ProtocolEvent.fundingLocked c' ∧
      c'.phase = ChannelPhase.normal :=
  ⟨{ c with phase := ChannelPhase.normal },
    Step.fundingLocked c (hbridge hready), rfl⟩

/-! ## 9. HTLC-set replay laws -/

/-- An `update_add_htlc` appends exactly its modelled HTLC record. -/
theorem applyMsg_updateAddHtlc_htlcs (eff : HtlcEffect) (p : Persisted)
    (u : UpdateAddHtlc) :
    (applyMsg eff p (.updateAddHtlc u)).htlcs = p.htlcs ++ [eff.ofAdd u] := rfl

/-- Replaying a run of `update_add_htlc` messages appends exactly the
corresponding HTLC records, in order, and touches nothing else. -/
theorem replay_addHtlcs_htlcs (eff : HtlcEffect) (us : List UpdateAddHtlc)
    (p : Persisted) :
    (replay eff (us.map Msg.updateAddHtlc) p).htlcs =
      p.htlcs ++ us.map eff.ofAdd := by
  induction us generalizing p with
  | nil => simp
  | cons u us ih =>
      change (replay eff (us.map Msg.updateAddHtlc)
        (applyMsg eff p (.updateAddHtlc u))).htlcs =
          p.htlcs ++ (u :: us).map eff.ofAdd
      rw [ih]
      simp [applyMsg, List.append_assoc]

end LnLean.Proofs.PhaseC3
