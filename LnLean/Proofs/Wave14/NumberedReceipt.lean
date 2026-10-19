import LnLean.Proofs.Protocol.ChannelReestablishProps

/-!
# LnLean.Proofs.Wave14.NumberedReceipt

## English claim

This module adds an *additive* numbered receipt adapter for
`commitment_signed`.  `receiveNumbered?` takes the commitment number that the
caller claims the message carries; for the addressed channel it applies the
existing `LnLean.Proofs.Protocol.advanceReceivedNumbered` refinement.  A receipt whose
number is the expected `nextCommitmentNumber` advances the counter by one; a
receipt with any other number (a replay whose number was already consumed, or
a wrong/future number) leaves the whole `PeerState` unchanged and still returns
`some` state.  All non-`commitment_signed` messages are delegated unchanged to
`PeerState.receive`.

The headline consequences are:

* `receiveNumbered_idempotent`: a successful numbered `commitment_signed`
  receipt is absorbed by a second receipt with the same number;
* `replay_does_not_double_advance`: after a successful receipt the addressed
  channel's commitment counter is `k + 1`, and a replay leaves it there;
* `receiveNumbered_fresh_advances`, `receiveNumbered_duplicate_noop`, and
  `receiveNumbered_wrongNumber_noop`: the three cases required by the review
  (fresh, duplicate, wrong number);
* `receiveNumbered_eq_receive_of_expected`: when the supplied number is the
  expected one, the numbered adapter agrees with the old unnumbered `receive`.

## What this module does *not* claim

* **The wire does not carry the commitment number.**  `CommitmentSigned`
  (`LnLean.Protocol.Messages`) has only `channelId`, `signature`, and
  `htlcSignatures`.  The number is an explicit model parameter supplied at the
  receipt boundary, exactly as in LDK's internal commitment dance.  This is a
  model adapter, not a change to BOLT 2 bytes.
* **The old unnumbered path is retained.**  `PeerState.receive` and
  `ChannelRecord.advanceReceived` are not modified, and
  `duplicate_commitmentSigned_advances_twice`
  (`LnLean.Proofs.Protocol.ChannelReestablishProps`) remains the recorded
  counterexample: the wire-faithful old path advances `+2` on a replay.
  `old_path_still_double_advances` below instantiates that retained theorem.
* **No error result.**  A wrong/future number is not rejected with `none`; it
  is a no-op.  `PeerState` has no channel-failure phase, so "fail the channel"
  is outside this carrier.
* **Only the `commitment_signed` branch is numbered.**  Handshake and other
  channel messages delegate to `receive`; idempotence is claimed only for the
  numbered commitment receipt, not for handshake replay.
* `findChannel`/`updateChannel` semantics are inherited.  If a `PeerState`
  contained duplicate channel identifiers, `updateChannel` maps every match;
  the model does not prove identifier uniqueness.
-/

namespace LnLean.Proofs.Wave14

set_option autoImplicit false

open LnLean
open LnLean.Protocol
open LnLean.Proofs.Protocol

namespace NumberedReceipt

/-! ## The numbered receipt adapter -/

/-- Consume an inbound message with an explicit commitment number.

For `commitment_signed`, the addressed channel is advanced by
`advanceReceivedNumbered` exactly when the supplied number equals its current
`nextCommitmentNumber`; otherwise the peer state is returned literally
unchanged (an idempotent no-op for duplicates and wrong numbers).  Every other
message is delegated to the old unnumbered `receive`. -/
def receiveNumbered? (s : PeerState) (m : Msg) (commitmentNumber : Nat) :
    Option PeerState :=
  match s.transport with
  | .down => none
  | .up =>
      match m with
      | .commitmentSigned cm =>
          match findChannel s cm.channelId with
          | none => none
          | some c =>
              if commitmentNumber = c.reestablish.nextCommitmentNumber then
                some (updateChannel s cm.channelId
                  (fun _ => advanceReceivedNumbered c commitmentNumber))
              else
                some s
      | _ => receive s m

/-- Defining equation for the `commitment_signed` branch. -/
@[simp] theorem receiveNumbered?_commitmentSigned_eq
    (s : PeerState) (cm : CommitmentSigned) (k : Nat) :
    receiveNumbered? s (.commitmentSigned cm) k =
      match s.transport with
      | .down => none
      | .up =>
          match findChannel s cm.channelId with
          | none => none
          | some c =>
              if k = c.reestablish.nextCommitmentNumber then
                some (updateChannel s cm.channelId
                  (fun _ => advanceReceivedNumbered c k))
              else
                some s := rfl

/-- A down transport accepts nothing, as in `receive`. -/
theorem receiveNumbered?_down (s : PeerState) (m : Msg) (k : Nat)
    (h : s.transport = .down) : receiveNumbered? s m k = none := by
  unfold receiveNumbered?
  rw [h]

/-- Outside the numbered `commitment_signed` branch the adapter is exactly the
old `receive`. -/
theorem receiveNumbered?_of_not_commitmentSigned
    (s : PeerState) (m : Msg) (k : Nat)
    (ht : s.transport = .up) (hk : m.kind ≠ .commitmentSigned) :
    receiveNumbered? s m k = receive s m := by
  unfold receiveNumbered?
  rw [ht]
  cases m <;> simp [Msg.kind] at hk ⊢

/-! ## Record-level numbered refinement -/

/-- The numbered refinement preserves the channel identifier. -/
theorem advanceReceivedNumbered_channelId (c : ChannelRecord) (k : Nat) :
    (advanceReceivedNumbered c k).channelId = c.channelId := by
  unfold advanceReceivedNumbered
  split <;> rfl

/-- A fresh (expected) number advances the counter by exactly one. -/
theorem advanceReceivedNumbered_fresh (c : ChannelRecord) (k : Nat)
    (hk : k = c.reestablish.nextCommitmentNumber) :
    (advanceReceivedNumbered c k).reestablish.nextCommitmentNumber = k + 1 := by
  unfold advanceReceivedNumbered
  rw [ite_eq_left hk]
  simp [ReestablishFields.afterCommitment, hk]

/-- A number that is not the expected one leaves the record unchanged. -/
theorem advanceReceivedNumbered_wrong (c : ChannelRecord) (k : Nat)
    (hk : k ≠ c.reestablish.nextCommitmentNumber) :
    advanceReceivedNumbered c k = c := by
  unfold advanceReceivedNumbered
  rw [ite_eq_right hk]

/-- Replaying the same number does not advance a second time: the record-level
counter after two numbered receipts is the original counter plus one. -/
theorem advanceReceivedNumbered_replay (c : ChannelRecord) (k : Nat)
    (hk : k = c.reestablish.nextCommitmentNumber) :
    (advanceReceivedNumbered (advanceReceivedNumbered c k) k).reestablish.nextCommitmentNumber
      = c.reestablish.nextCommitmentNumber + 1 := by
  rw [advanceReceivedNumbered_idempotent]
  rw [advanceReceivedNumbered_fresh c k hk, hk]

/-! ## `findChannel` after `updateChannel` -/

/-- A list-level lookup lemma: mapping by a function that fixes every element
failing the predicate, and sends the found element to a value still satisfying
the predicate, preserves the lookup result.  (This is the same plumbing used
by `ChannelReestablishProps`; it is repeated privately so this module stays
additive.) -/
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

/-! ## Peer-state numbered receipt laws -/

/-- A fresh numbered receipt succeeds and applies the record refinement to the
addressed channel. -/
theorem receiveNumbered_some_of_expected
    (s : PeerState) (cm : CommitmentSigned) (k : Nat) (c : ChannelRecord)
    (ht : s.transport = .up)
    (hf : findChannel s cm.channelId = some c)
    (hk : k = c.reestablish.nextCommitmentNumber) :
    receiveNumbered? s (.commitmentSigned cm) k =
      some (updateChannel s cm.channelId
        (fun _ => advanceReceivedNumbered c k)) := by
  rw [receiveNumbered?_commitmentSigned_eq]
  rw [ht]
  simp only [hf]
  rw [ite_eq_left hk]

/-- **Fresh receipt.**  When the supplied number is the addressed channel's
expected `nextCommitmentNumber`, an accepted numbered receipt advances that
channel's commitment counter by one. -/
theorem receiveNumbered_fresh_advances
    (s s' : PeerState) (cm : CommitmentSigned) (k : Nat) (c : ChannelRecord)
    (ht : s.transport = .up)
    (hf : findChannel s cm.channelId = some c)
    (hk : k = c.reestablish.nextCommitmentNumber)
    (h : receiveNumbered? s (.commitmentSigned cm) k = some s') :
    ∃ c', findChannel s' cm.channelId = some c' ∧
      c'.reestablish.nextCommitmentNumber = k + 1 := by
  rw [receiveNumbered?_commitmentSigned_eq] at h
  rw [ht] at h
  simp only [hf] at h
  rw [ite_eq_left hk] at h
  have hs' : s' = updateChannel s cm.channelId
      (fun _ => advanceReceivedNumbered c k) :=
    (Option.some.inj h).symm
  subst s'
  refine ⟨advanceReceivedNumbered c k, ?_,
    advanceReceivedNumbered_fresh c k hk⟩
  exact findChannel_updateChannel_of_channelId s cm.channelId
    (fun _ => advanceReceivedNumbered c k) c hf
    (advanceReceivedNumbered_channelId c k)

/-- **Wrong-number receipt.**  If the supplied number is not the expected one
(including a number already consumed by an earlier receipt), the whole peer
state is returned unchanged. -/
theorem receiveNumbered_wrongNumber_noop
    (s : PeerState) (cm : CommitmentSigned) (k : Nat) (c : ChannelRecord)
    (ht : s.transport = .up)
    (hf : findChannel s cm.channelId = some c)
    (hk : k ≠ c.reestablish.nextCommitmentNumber) :
    receiveNumbered? s (.commitmentSigned cm) k = some s := by
  rw [receiveNumbered?_commitmentSigned_eq]
  rw [ht]
  simp only [hf]
  rw [ite_eq_right hk]

/-- **Idempotence.**  A successful numbered `commitment_signed` receipt is
absorbed by a replay carrying the same number. -/
theorem receiveNumbered_idempotent
    (s s' : PeerState) (cm : CommitmentSigned) (k : Nat)
    (h : receiveNumbered? s (.commitmentSigned cm) k = some s') :
    receiveNumbered? s' (.commitmentSigned cm) k = some s' := by
  rw [receiveNumbered?_commitmentSigned_eq] at h ⊢
  cases ht : s.transport with
  | down => simp [ht] at h
  | up =>
      simp only [ht] at h ⊢
      cases hf : findChannel s cm.channelId with
      | none => simp [hf] at h
      | some c =>
          simp only [hf] at h ⊢
          by_cases hk : k = c.reestablish.nextCommitmentNumber
          · rw [ite_eq_left hk] at h
            have hs' : s' = updateChannel s cm.channelId
                (fun _ => advanceReceivedNumbered c k) :=
              (Option.some.inj h).symm
            subst s'
            have hfind' : findChannel
                (updateChannel s cm.channelId
                  (fun _ => advanceReceivedNumbered c k)) cm.channelId =
                some (advanceReceivedNumbered c k) :=
              findChannel_updateChannel_of_channelId s cm.channelId
                (fun _ => advanceReceivedNumbered c k) c hf
                (advanceReceivedNumbered_channelId c k)
            have ht' : (updateChannel s cm.channelId
                (fun _ => advanceReceivedNumbered c k)).transport = .up := by
              simp [updateChannel, ht]
            have hne : ¬ (k =
                (advanceReceivedNumbered c k).reestablish.nextCommitmentNumber) := by
              intro hEq
              have hnext := advanceReceivedNumbered_fresh c k hk
              omega
            rw [ht', hfind']
            simp [hne]
          · rw [ite_eq_right hk] at h
            have hs' : s' = s := (Option.some.inj h).symm
            subst s'
            simp [ht, hf, hk]

/-- **Duplicate receipt is a no-op.**  After a successful fresh receipt, the
same number is no longer the expected one; a second receipt returns the same
state and the addressed counter remains `k + 1` (not `k + 2`). -/
theorem receiveNumbered_duplicate_noop
    (s s' : PeerState) (cm : CommitmentSigned) (k : Nat) (c : ChannelRecord)
    (ht : s.transport = .up)
    (hf : findChannel s cm.channelId = some c)
    (hk : k = c.reestablish.nextCommitmentNumber)
    (h : receiveNumbered? s (.commitmentSigned cm) k = some s') :
    receiveNumbered? s' (.commitmentSigned cm) k = some s' ∧
      (∀ c', findChannel s' cm.channelId = some c' →
        c'.reestablish.nextCommitmentNumber = k + 1) := by
  constructor
  · exact receiveNumbered_idempotent s s' cm k h
  · intro c' hc'
    obtain ⟨c0, h0, hnext⟩ :=
      receiveNumbered_fresh_advances s s' cm k c ht hf hk h
    rw [h0] at hc'
    have hc0 : c' = c0 := (Option.some.inj hc').symm
    rw [hc0]
    exact hnext

/-- **Replay does not double-advance.**  After a successful fresh receipt the
addressed counter is the old counter plus one, and a second numbered receipt
returns the same state.  This is the numbered counterpart of the retained
unnumbered counterexample `duplicate_commitmentSigned_advances_twice`. -/
theorem replay_does_not_double_advance
    (s s' : PeerState) (cm : CommitmentSigned) (k : Nat) (c : ChannelRecord)
    (ht : s.transport = .up)
    (hf : findChannel s cm.channelId = some c)
    (hk : k = c.reestablish.nextCommitmentNumber)
    (h : receiveNumbered? s (.commitmentSigned cm) k = some s') :
    receiveNumbered? s' (.commitmentSigned cm) k = some s' ∧
      (∀ c', findChannel s' cm.channelId = some c' →
        c'.reestablish.nextCommitmentNumber =
          c.reestablish.nextCommitmentNumber + 1) := by
  constructor
  · exact receiveNumbered_idempotent s s' cm k h
  · intro c' hc'
    obtain ⟨c0, h0, hnext⟩ :=
      receiveNumbered_fresh_advances s s' cm k c ht hf hk h
    rw [h0] at hc'
    have hc0 : c' = c0 := (Option.some.inj hc').symm
    rw [hc0]
    omega

/-- **Agreement with the old path on a fresh receipt.**  When the supplied
number is exactly the expected one, the numbered adapter has the same effect
as the retained unnumbered `receive`.  The two paths diverge only on a replay,
which is the counterexample this module keeps. -/
theorem receiveNumbered_eq_receive_of_expected
    (s : PeerState) (cm : CommitmentSigned) (k : Nat) (c : ChannelRecord)
    (ht : s.transport = .up)
    (hf : findChannel s cm.channelId = some c)
    (hk : k = c.reestablish.nextCommitmentNumber) :
    receiveNumbered? s (.commitmentSigned cm) k =
      receive s (.commitmentSigned cm) := by
  rw [receiveNumbered?_commitmentSigned_eq]
  rw [ht]
  simp only [hf]
  rw [ite_eq_left hk]
  unfold receive
  rw [ht]
  simp only [receiveEvent?, channelId?, hf]
  have hrec : c.advanceReceived (.commitmentSigned cm) =
      advanceReceivedNumbered c k := by
    simp [ChannelRecord.advanceReceived, advanceReceivedNumbered, Msg.kind, hk]
  rw [hrec]

/-! ## Concrete non-vacuity witnesses -/

/-- Concrete identifier used by the witnesses. -/
def sampleChannelId : ChannelId := ⟨ByteArray.empty⟩

/-- A concrete record whose expected commitment number is zero. -/
def sampleRecord : ChannelRecord where
  channelId := sampleChannelId
  reestablish := ReestablishFields.initial

/-- A concrete connected peer with one channel. -/
def samplePeer : PeerState where
  identity := ⟨ByteArray.empty⟩
  transport := .up
  handshake := HandshakeState.initial
  channels := [sampleRecord]

/-- A concrete `commitment_signed` for the sample channel. -/
def sampleCommitmentSigned : CommitmentSigned where
  channelId := sampleChannelId
  signature := ⟨ByteArray.empty⟩
  htlcSignatures := []

/-- `findChannel` locates the sample record.  `ChannelId` derives `BEq`
rather than `DecidableEq`, so the comparison is computed explicitly. -/
theorem samplePeer_findChannel :
    findChannel samplePeer sampleChannelId = some sampleRecord := by
  unfold findChannel samplePeer
  have hbeq : (sampleRecord.channelId == sampleChannelId) = true := by
    unfold sampleRecord sampleChannelId
    change LnLean.instBEqChannelId.beq
      { bytes := ByteArray.empty } { bytes := ByteArray.empty } = true
    rw [LnLean.instBEqChannelId.beq]
    change ByteArray.beq ByteArray.empty ByteArray.empty = true
    rw [ByteArray.beq]
    simp
  simp [hbeq]

/-- Fresh-case witness: the concrete expected number 0 advances the sample
channel from 0 to 1. -/
theorem samplePeer_fresh_witness :
    ∃ s' c',
      receiveNumbered? samplePeer (.commitmentSigned sampleCommitmentSigned) 0 = some s' ∧
      findChannel s' sampleChannelId = some c' ∧
      c'.reestablish.nextCommitmentNumber = 1 := by
  have hrecv : receiveNumbered? samplePeer
      (.commitmentSigned sampleCommitmentSigned) 0 =
      some (updateChannel samplePeer sampleChannelId
        (fun _ => advanceReceivedNumbered sampleRecord 0)) :=
    receiveNumbered_some_of_expected samplePeer sampleCommitmentSigned 0 sampleRecord
      rfl samplePeer_findChannel rfl
  have hfind : findChannel
      (updateChannel samplePeer sampleChannelId
        (fun _ => advanceReceivedNumbered sampleRecord 0)) sampleChannelId =
      some (advanceReceivedNumbered sampleRecord 0) :=
    findChannel_updateChannel_of_channelId samplePeer sampleChannelId
      (fun _ => advanceReceivedNumbered sampleRecord 0) sampleRecord
      samplePeer_findChannel (advanceReceivedNumbered_channelId sampleRecord 0)
  refine ⟨_, _, hrecv, hfind, ?_⟩
  rw [advanceReceivedNumbered_fresh sampleRecord 0 rfl]

/-- Duplicate-case witness: the second receipt with the same number 0 returns
the same state and the counter stays at 1 (not 2). -/
theorem samplePeer_duplicate_witness :
    ∃ s' c',
      receiveNumbered? samplePeer (.commitmentSigned sampleCommitmentSigned) 0 = some s' ∧
      findChannel s' sampleChannelId = some c' ∧
      receiveNumbered? s' (.commitmentSigned sampleCommitmentSigned) 0 = some s' ∧
      c'.reestablish.nextCommitmentNumber = 1 := by
  obtain ⟨s', c', hrecv, hfind, hnext⟩ := samplePeer_fresh_witness
  exact ⟨s', c', hrecv, hfind,
    receiveNumbered_idempotent samplePeer s' sampleCommitmentSigned 0 hrecv,
    hnext⟩

/-- Wrong-number witness: number 1 is not the expected number 0, so the state
is returned literally unchanged. -/
theorem samplePeer_wrongNumber_witness :
    receiveNumbered? samplePeer (.commitmentSigned sampleCommitmentSigned) 1 =
      some samplePeer :=
  receiveNumbered_wrongNumber_noop samplePeer sampleCommitmentSigned 1 sampleRecord
    rfl samplePeer_findChannel (by decide)

/-- The retained unnumbered path still exhibits the gap: replaying the same
`commitment_signed` advances the sample record by two.  This instantiates the
existing `duplicate_commitmentSigned_advances_twice` and does not replace it. -/
theorem old_path_still_double_advances :
    ((sampleRecord.advanceReceived (.commitmentSigned sampleCommitmentSigned)).advanceReceived
        (.commitmentSigned sampleCommitmentSigned)).reestablish.nextCommitmentNumber = 2 := by
  have h := duplicate_commitmentSigned_advances_twice sampleRecord sampleCommitmentSigned
  simpa [sampleRecord, ReestablishFields.initial] using h

/-! ## Axiom audit -/

#print axioms receiveNumbered_idempotent
#print axioms replay_does_not_double_advance
#print axioms receiveNumbered_some_of_expected
#print axioms receiveNumbered_fresh_advances
#print axioms receiveNumbered_duplicate_noop
#print axioms receiveNumbered_wrongNumber_noop
#print axioms receiveNumbered_eq_receive_of_expected
#print axioms advanceReceivedNumbered_replay
#print axioms samplePeer_fresh_witness
#print axioms samplePeer_duplicate_witness
#print axioms samplePeer_wrongNumber_witness
#print axioms old_path_still_double_advances

end NumberedReceipt

end LnLean.Proofs.Wave14
