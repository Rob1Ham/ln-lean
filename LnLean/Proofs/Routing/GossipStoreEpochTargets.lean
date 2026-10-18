import LnLean.Proofs.Routing.GossipRawRefinementTargets

/-!
# LnLean.Proofs.Routing.GossipStoreEpochTargets

Wave-8 lane `S8-MODEL-STORE-EPOCH`, open issue `RT-01`.

Wave 7 (`GossipRawRefinementTargets`) proved the one-step square

  `canonicalStoreView (applyGossip s m) = (applyGossipCanonicalStore verify s m).gossip`

on a canonical-shaped store, under the canonical admission gates and the raw
global clock.  That is a statement about one message, and it does not model the
store's *replacement history*: the canonical transition replaces an
announcement or a directional update slot, but the wave-7 store keeps no record
of which old record was superseded, nor of when.

This module supplies an explicit epoch layer:

* `StoreEpoch` packages the canonical store with an epoch counter, a typed
  replacement history, and an epoch-indexed view (`announcementEpoch`,
  `updateEpoch`) that records the epoch at which the currently stored record
  for each channel or directional slot was installed.
* `epochStep` is the canonical store transition with history/version
  bookkeeping.  A rejected message leaves the epoch and every view component
  unchanged; an admitted message increments the epoch and appends exactly one
  typed `ReplacementEvent` recording the incoming record and the exact list of
  old records removed by `insertReplacing` / `insertUpdateCanonical`.
* `epochFold` folds this transition over a message sequence.
* `epochFold_store_eq_foldl` is the unconditional square against the canonical
  transition: the epoch fold's latest store is literally the fold of
  `applyGossipCanonicalStore`.
* `epochFold_gossip_eq_canonicalStoreView_rawFold` is the sequence-level square
  against the raw store.  It holds under exactly three hypotheses: the initial
  epoch store is the canonical observation of the initial raw store, every
  message is canonically admitted at its epoch, and the raw global clock admits
  every update at the actual raw state.  Both remaining hypotheses are shown
  necessary by concrete sequences in §7 (rejected announcement versus clock
  boundary), and the wave-7 one-step boundary/impossibility results are
  re-exported unchanged.

What is **not** claimed:

* raw `applyGossip` still does **not** refine canonical admission; the
  sequence-level square above is a conditional observation statement, not a
  replacement of raw semantics;
* the epoch counter is a model-side version number, not a BOLT 7 wire field;
* node announcements are appended by both paths and are not canonicalised
  (the wave-6/7 `RT-02` caveat is unchanged);
* `SigVerifier` remains abstract and unforgeability remains assumption
  C3/C4/C8 in `docs/ASSUMPTIONS.md`;
* no network, liveness, chain, UTXO, or rate-limit claim is made.

No `sorry`, no `axiom`, no `admit`, no `native_decide`, no `unsafe`, no
`@[implemented_by]`.
-/

namespace LnLean.Proofs.Routing.GossipStoreEpochTargets

open LnLean.Routing
open LnLean.Routing.GossipProps
open LnLean.Proofs.Routing.GossipTargets
open LnLean.Proofs.Routing.GossipAttributionTargets
open LnLean.Proofs.Routing.GossipKeyConsistencyTargets
open LnLean.Proofs.Routing.GossipCanonicalTargets
open LnLean.Proofs.Routing.GossipRawRefinementTargets
open Classical

set_option autoImplicit false

/-! ## 1. A typed replacement history -/

/-- **One canonical store admission, recorded as a replacement event.**

The `epoch` is the store epoch *after* the admission.  `replaced` is the exact
list of stored records removed by the canonical insertion:
`replacedAnnouncements` for an announcement and `replacedUpdates` for a
directional slot.  A node announcement has no replacement list because both the
raw and canonical paths append it. -/
inductive ReplacementEvent where
  /-- An admitted `channel_announcement`, replacing `replaced` old records for
  the same `short_channel_id`. -/
  | announcement (epoch : Nat) (incoming : ChannelAnnellation)
      (replaced : List ChannelAnnellation)
  /-- An admitted `channel_update`, replacing `replaced` old records in the same
  `(short_channel_id, direction)` slot. -/
  | update (epoch : Nat) (incoming : ChannelUpdate)
      (replaced : List ChannelUpdate)
  /-- An admitted `node_announcement`, which appends and replaces nothing. -/
  | node (epoch : Nat) (announcement : NodeAnnouncement)

namespace ReplacementEvent

/-- The epoch at which the event was recorded. -/
def epoch : ReplacementEvent → Nat
  | .announcement k _ _ => k
  | .update k _ _ => k
  | .node k _ => k

/-- The incoming announcement of an announcement event, if any. -/
def incomingAnnouncement? : ReplacementEvent → Option ChannelAnnellation
  | .announcement _ a _ => some a
  | .update _ _ _ => none
  | .node _ _ => none

/-- The incoming update of an update event, if any. -/
def incomingUpdate? : ReplacementEvent → Option ChannelUpdate
  | .announcement _ _ _ => none
  | .update _ u _ => some u
  | .node _ _ => none

/-- The incoming node announcement of a node event, if any. -/
def incomingNode? : ReplacementEvent → Option NodeAnnouncement
  | .announcement _ _ _ => none
  | .update _ _ _ => none
  | .node _ n => some n

end ReplacementEvent

/-! ## 2. Epoch-indexed store and canonical epoch step -/

/-- **The epoch view of a canonical store.**

`epoch` is the number of admitted transitions since the initial state (a
model-side version, not a wire field).  `history` is newest-first.  The two
maps record the install epoch of the current record for a channel and for a
directional slot. -/
structure StoreEpoch where
  /-- The number of admitted transitions recorded so far. -/
  epoch : Nat
  /-- The current canonical store. -/
  store : CanonicalStore
  /-- The replacement history, newest first. -/
  history : List ReplacementEvent
  /-- Install epoch of the current announcement for a `short_channel_id`. -/
  announcementEpoch : ShortChannelId → Option Nat
  /-- Install epoch of the current update for a `(short_channel_id, direction)`
  slot. -/
  updateEpoch : ShortChannelId → Bool → Option Nat

namespace StoreEpoch

/-- The initial epoch state: empty store, epoch `0`, empty history, and no
installed records.  The registration map is arbitrary, matching the wave-6/7
empty-state convention. -/
def empty (nodeKeyOf : NodeId → PubKey) : StoreEpoch :=
  { epoch := 0
    store := { gossip := ⟨[], [], []⟩, nodeKeyOf := nodeKeyOf }
    history := []
    announcementEpoch := fun _ => none
    updateEpoch := fun _ _ => none }

/-- Set the install epoch of one channel's announcement. -/
def setAnnouncementEpoch (f : ShortChannelId → Option Nat)
    (a : ChannelAnnellation) (k : Nat) : ShortChannelId → Option Nat :=
  fun sc => if sc = a.shortChannelId then some k else f sc

/-- Set the install epoch of one directional update slot. -/
def setUpdateEpoch (f : ShortChannelId → Bool → Option Nat)
    (u : ChannelUpdate) (k : Nat) : ShortChannelId → Bool → Option Nat :=
  fun sc d => if sc = u.shortChannelId ∧ d = u.direction then some k else f sc d

/-- The event recorded by an admitted message. -/
def eventOf (e : StoreEpoch) (m : GossipMessage) : ReplacementEvent :=
  match m with
  | .channelAnnouncement a =>
      .announcement (e.epoch + 1) a
        (replacedAnnouncements a e.store.gossip.announcements)
  | .channelUpdate u =>
      .update (e.epoch + 1) u
        (replacedUpdates u e.store.gossip.updates)
  | .nodeAnnouncement n => .node (e.epoch + 1) n

/-- The epoch-indexed view after an admitted message. -/
def announcementEpochAfter (e : StoreEpoch) (m : GossipMessage) :
    ShortChannelId → Option Nat :=
  match m with
  | .channelAnnouncement a =>
      setAnnouncementEpoch e.announcementEpoch a (e.epoch + 1)
  | _ => e.announcementEpoch

/-- The per-slot version view after an admitted message. -/
def updateEpochAfter (e : StoreEpoch) (m : GossipMessage) :
    ShortChannelId → Bool → Option Nat :=
  match m with
  | .channelUpdate u => setUpdateEpoch e.updateEpoch u (e.epoch + 1)
  | _ => e.updateEpoch

end StoreEpoch

/-- A message rejected by the canonical gates leaves the canonical store
unchanged.  This is the contrapositive of the transition equations. -/
theorem applyGossipCanonicalStore_of_not_admitted (verify : SigVerifier)
    (cs : CanonicalStore) (m : GossipMessage)
    (h : ¬ CanonicalMessageAdmitted verify cs m) :
    applyGossipCanonicalStore verify cs m = cs := by
  cases m with
  | channelAnnouncement a =>
      exact applyGossipCanonicalStore_announcement_of_rejected verify cs a h
  | channelUpdate u =>
      exact applyGossipCanonicalStore_update_of_rejected verify cs u h
  | nodeAnnouncement n =>
      exact applyGossipCanonicalStore_node_of_invalid verify cs n h

/-- **Canonical epoch step.**  A message admitted by the canonical store
transition increments the epoch, records one typed replacement event, updates
the version view, and takes the canonical store step.  A rejected message is a
complete no-op. -/
noncomputable def epochStep (verify : SigVerifier) (e : StoreEpoch)
    (m : GossipMessage) : StoreEpoch :=
  if CanonicalMessageAdmitted verify e.store m then
    { epoch := e.epoch + 1
      store := applyGossipCanonicalStore verify e.store m
      history := e.eventOf m :: e.history
      announcementEpoch := e.announcementEpochAfter m
      updateEpoch := e.updateEpochAfter m }
  else e

namespace StoreEpoch

/-- The event recorded by `epochStep` is `eventOf`. -/
theorem epochStep_history_of_admitted {verify : SigVerifier} {e : StoreEpoch}
    {m : GossipMessage} (h : CanonicalMessageAdmitted verify e.store m) :
    (epochStep verify e m).history = e.eventOf m :: e.history := by
  simp [epochStep, h]

/-- An admitted message increments the epoch. -/
theorem epochStep_epoch_of_admitted {verify : SigVerifier} {e : StoreEpoch}
    {m : GossipMessage} (h : CanonicalMessageAdmitted verify e.store m) :
    (epochStep verify e m).epoch = e.epoch + 1 := by
  simp [epochStep, h]

/-- A rejected message is a complete no-op. -/
theorem epochStep_of_rejected {verify : SigVerifier} {e : StoreEpoch}
    {m : GossipMessage} (h : ¬ CanonicalMessageAdmitted verify e.store m) :
    epochStep verify e m = e := by
  simp [epochStep, h]

/-- The store component of an epoch step is exactly the canonical store
transition. -/
theorem epochStep_store (verify : SigVerifier) (e : StoreEpoch)
    (m : GossipMessage) :
    (epochStep verify e m).store = applyGossipCanonicalStore verify e.store m := by
  unfold epochStep
  split
  · rfl
  · rename_i h
    rw [applyGossipCanonicalStore_of_not_admitted verify e.store m h]

/-- The epoch never decreases. -/
theorem epochStep_epoch_ge (verify : SigVerifier) (e : StoreEpoch)
    (m : GossipMessage) : e.epoch ≤ (epochStep verify e m).epoch := by
  unfold epochStep
  split <;> simp

/-- An epoch step either keeps the epoch or increments it by one. -/
theorem epochStep_epoch_eq_self_or_succ (verify : SigVerifier) (e : StoreEpoch)
    (m : GossipMessage) :
    (epochStep verify e m).epoch = e.epoch ∨
      (epochStep verify e m).epoch = e.epoch + 1 := by
  unfold epochStep
  split <;> simp

/-- The epoch increments exactly on canonical admission. -/
theorem epochStep_epoch_eq_succ_iff (verify : SigVerifier) (e : StoreEpoch)
    (m : GossipMessage) :
    (epochStep verify e m).epoch = e.epoch + 1 ↔
      CanonicalMessageAdmitted verify e.store m := by
  unfold epochStep
  split
  · rename_i h
    exact ⟨fun _ => h, fun _ => rfl⟩
  · rename_i h
    refine ⟨?_, fun hg => absurd hg h⟩
    intro hc
    exact absurd hc.symm (Nat.succ_ne_self e.epoch)

/-- The history length and the epoch counter agree whenever they agree in the
initial state.  This is the exact "one admitted step, one recorded event"
correspondence. -/
theorem epochStep_history_length (verify : SigVerifier) (e : StoreEpoch)
    (m : GossipMessage) (hlen : e.history.length = e.epoch) :
    (epochStep verify e m).history.length = (epochStep verify e m).epoch := by
  unfold epochStep
  split
  · simp [hlen]
  · exact hlen

/-- The epoch step preserves canonical selector shape. -/
theorem epochStep_shape (verify : SigVerifier) (e : StoreEpoch)
    (m : GossipMessage) (hshape : CanonicalStoreShape e.store.gossip)
    (hgate : CanonicalMessageAdmitted verify e.store m) :
    CanonicalStoreShape (epochStep verify e m).store.gossip := by
  rw [epochStep_store]
  exact canonicalStoreShape_applyGossipCanonicalStore verify e.store m hshape hgate

/-- The new event is either absent (rejection) or exactly one cons. -/
theorem epochStep_history_cases (verify : SigVerifier) (e : StoreEpoch)
    (m : GossipMessage) :
    (epochStep verify e m).history = e.history ∨
      ∃ ev : ReplacementEvent, (epochStep verify e m).history = ev :: e.history := by
  unfold epochStep
  split
  · exact Or.inr ⟨_, rfl⟩
  · exact Or.inl rfl

end StoreEpoch

/-! ## 3. Folding the epoch transition over a sequence -/

/-- Fold the canonical epoch transition over a message sequence. -/
noncomputable def epochFold (verify : SigVerifier) (e : StoreEpoch)
    (msgs : List GossipMessage) : StoreEpoch :=
  msgs.foldl (fun e m => epochStep verify e m) e

/-- Fold the raw store transition over a message sequence. -/
def rawFold (s : GossipState) (msgs : List GossipMessage) : GossipState :=
  msgs.foldl (fun s m => applyGossip s m) s

/-- Every message in the sequence is canonically admitted at the epoch reached
by the prefix before it. -/
def EpochAdmittedAlong (verify : SigVerifier) (e : StoreEpoch) :
    List GossipMessage → Prop
  | [] => True
  | m :: ms =>
      CanonicalMessageAdmitted verify e.store m ∧
        EpochAdmittedAlong verify (epochStep verify e m) ms

/-- Every update in the raw sequence is admitted by the raw global clock at the
actual raw state reached by the prefix before it.  Announcements and node
announcements are always appended by `applyGossip`. -/
def RawAdmittedAlong : GossipState → List GossipMessage → Prop
  | _, [] => True
  | s, m :: ms =>
      RawClockAdmits s m ∧ RawAdmittedAlong (applyGossip s m) ms

namespace StoreEpoch

/-- **The unconditional epoch/canonical square.**  The latest store of the
epoch fold is literally the canonical transition folded over the same messages.
History and version bookkeeping do not change the store component. -/
theorem epochFold_store_eq_foldl (verify : SigVerifier) (e : StoreEpoch)
    (msgs : List GossipMessage) :
    (epochFold verify e msgs).store =
      msgs.foldl (fun cs m => applyGossipCanonicalStore verify cs m) e.store := by
  induction msgs generalizing e with
  | nil => rfl
  | cons m ms ih =>
      change (epochFold verify (epochStep verify e m) ms).store =
        List.foldl (fun cs m => applyGossipCanonicalStore verify cs m)
          (applyGossipCanonicalStore verify e.store m) ms
      rw [ih (epochStep verify e m), epochStep_store]

/-- The epoch fold extends the initial history by a (possibly empty) newer
prefix. -/
theorem epochFold_history_extends (verify : SigVerifier) (e : StoreEpoch)
    (msgs : List GossipMessage) :
    ∃ newer, (epochFold verify e msgs).history = newer ++ e.history := by
  induction msgs generalizing e with
  | nil => exact ⟨[], by simp [epochFold]⟩
  | cons m ms ih =>
      rcases ih (epochStep verify e m) with ⟨newer, hnewer⟩
      rcases epochStep_history_cases verify e m with hsame | ⟨ev, hev⟩
      · refine ⟨newer, ?_⟩
        simpa [epochFold, hsame] using hnewer
      · refine ⟨newer ++ [ev], ?_⟩
        rw [show epochFold verify e (m :: ms) =
          epochFold verify (epochStep verify e m) ms by rfl]
        rw [hnewer, hev, List.append_assoc]
        rfl

/-- The epoch counter is monotone along the fold. -/
theorem epochFold_epoch_ge (verify : SigVerifier) (e : StoreEpoch)
    (msgs : List GossipMessage) : e.epoch ≤ (epochFold verify e msgs).epoch := by
  induction msgs generalizing e with
  | nil => simp [epochFold]
  | cons m ms ih =>
      exact Nat.le_trans (epochStep_epoch_ge verify e m)
        (ih (epochStep verify e m))

/-- The epoch counter never exceeds the initial epoch plus the sequence
length. -/
theorem epochFold_epoch_le (verify : SigVerifier) (e : StoreEpoch)
    (msgs : List GossipMessage) :
    (epochFold verify e msgs).epoch ≤ e.epoch + msgs.length := by
  induction msgs generalizing e with
  | nil => simp [epochFold]
  | cons m ms ih =>
      change (epochFold verify (epochStep verify e m) ms).epoch ≤
        e.epoch + (m :: ms).length
      have hstep : (epochStep verify e m).epoch ≤ e.epoch + 1 := by
        rcases epochStep_epoch_eq_self_or_succ verify e m with h | h <;> omega
      have hih := ih (epochStep verify e m)
      simp only [List.length_cons]
      omega

/-- The epoch fold preserves canonical selector shape under the per-step
admission gates. -/
theorem epochFold_shape (verify : SigVerifier) (e : StoreEpoch)
    (msgs : List GossipMessage) (hshape : CanonicalStoreShape e.store.gossip)
    (hadm : EpochAdmittedAlong verify e msgs) :
    CanonicalStoreShape (epochFold verify e msgs).store.gossip := by
  induction msgs generalizing e with
  | nil => simpa [epochFold] using hshape
  | cons m ms ih =>
      rcases hadm with ⟨hgate, hrest⟩
      exact ih (epochStep verify e m)
        (epochStep_shape verify e m hshape hgate) hrest

/-- The history length and the epoch counter agree for a fold started in a
state where they agree. -/
theorem epochFold_history_length (verify : SigVerifier) (e : StoreEpoch)
    (msgs : List GossipMessage) (hlen : e.history.length = e.epoch) :
    (epochFold verify e msgs).history.length = (epochFold verify e msgs).epoch := by
  induction msgs generalizing e with
  | nil => simpa [epochFold] using hlen
  | cons m ms ih =>
      exact ih (epochStep verify e m) (epochStep_history_length verify e m hlen)

/-- For the empty initial state, the epoch is exactly the number of recorded
replacement events. -/
theorem epochFold_empty_history_length (verify : SigVerifier)
    (nodeKeyOf : NodeId → PubKey) (msgs : List GossipMessage) :
    (epochFold verify (empty nodeKeyOf) msgs).history.length =
      (epochFold verify (empty nodeKeyOf) msgs).epoch :=
  epochFold_history_length verify (empty nodeKeyOf) msgs rfl

end StoreEpoch

/-! ## 4. The epoch-indexed view is sound and bounded -/

namespace StoreEpoch

/-- **The version view is sound.**  A channel (respectively directional slot)
has an install epoch exactly when the current canonical store holds a record
for it.  This is what makes the maps a view of the store rather than a
detached log. -/
def ViewConsistent (e : StoreEpoch) : Prop :=
  (∀ sc : ShortChannelId,
      e.announcementEpoch sc ≠ none ↔
        ∃ a ∈ e.store.gossip.announcements, a.shortChannelId = sc) ∧
    (∀ (sc : ShortChannelId) (d : Bool),
      e.updateEpoch sc d ≠ none ↔
        ∃ u ∈ e.store.gossip.updates,
          u.shortChannelId = sc ∧ u.direction = d)

/-- **Every install epoch is in the past.**  No version label refers to a
future epoch. -/
def ViewBounded (e : StoreEpoch) : Prop :=
  (∀ (sc : ShortChannelId) (k : Nat),
      e.announcementEpoch sc = some k → k ≤ e.epoch) ∧
    (∀ (sc : ShortChannelId) (d : Bool) (k : Nat),
      e.updateEpoch sc d = some k → k ≤ e.epoch)

/-- Membership in a versioned announcement map, unfolded. -/
theorem setAnnouncementEpoch_ne_none_iff
    (f : ShortChannelId → Option Nat) (a : ChannelAnnellation) (k : Nat)
    (sc : ShortChannelId) :
    setAnnouncementEpoch f a k sc ≠ none ↔
      sc = a.shortChannelId ∨ f sc ≠ none := by
  unfold setAnnouncementEpoch
  by_cases h : sc = a.shortChannelId <;> simp [h]

/-- Membership in a versioned update-slot map, unfolded. -/
theorem setUpdateEpoch_ne_none_iff
    (f : ShortChannelId → Bool → Option Nat) (u : ChannelUpdate) (k : Nat)
    (sc : ShortChannelId) (d : Bool) :
    setUpdateEpoch f u k sc d ≠ none ↔
      (sc = u.shortChannelId ∧ d = u.direction) ∨ f sc d ≠ none := by
  unfold setUpdateEpoch
  by_cases h : sc = u.shortChannelId ∧ d = u.direction <;> simp [h]

/-- A set announcement epoch either is the new epoch or an old value. -/
theorem setAnnouncementEpoch_some_cases
    {f : ShortChannelId → Option Nat} {a : ChannelAnnellation} {k : Nat}
    {sc : ShortChannelId} {j : Nat}
    (h : setAnnouncementEpoch f a k sc = some j) :
    (sc = a.shortChannelId ∧ j = k) ∨
      (sc ≠ a.shortChannelId ∧ f sc = some j) := by
  unfold setAnnouncementEpoch at h
  by_cases hs : sc = a.shortChannelId
  · left
    have hkj : k = j := by simpa [hs] using h
    exact ⟨hs, hkj.symm⟩
  · right
    exact ⟨hs, by simpa [hs] using h⟩

/-- A set update epoch either is the new epoch or an old value. -/
theorem setUpdateEpoch_some_cases
    {f : ShortChannelId → Bool → Option Nat} {u : ChannelUpdate} {k : Nat}
    {sc : ShortChannelId} {d : Bool} {j : Nat}
    (h : setUpdateEpoch f u k sc d = some j) :
    ((sc = u.shortChannelId ∧ d = u.direction) ∧ j = k) ∨
      (¬ (sc = u.shortChannelId ∧ d = u.direction) ∧ f sc d = some j) := by
  unfold setUpdateEpoch at h
  by_cases hs : sc = u.shortChannelId ∧ d = u.direction
  · left
    have hkj : k = j := by simpa [hs] using h
    exact ⟨hs, hkj.symm⟩
  · right
    exact ⟨hs, by simpa [hs] using h⟩

/-- The initial epoch view is consistent: the empty store has no records and
the maps are everywhere `none`. -/
theorem empty_viewConsistent (nodeKeyOf : NodeId → PubKey) :
    (empty nodeKeyOf).ViewConsistent := by
  constructor
  · intro sc
    simp [empty]
  · intro sc d
    simp [empty]

/-- The initial epoch view is bounded. -/
theorem empty_viewBounded (nodeKeyOf : NodeId → PubKey) :
    (empty nodeKeyOf).ViewBounded := by
  constructor
  · intro sc k hk
    simp [empty] at hk
  · intro sc d k hk
    simp [empty] at hk

/-- **A canonical epoch step preserves version-view soundness.**  An admitted
announcement installs a version for its channel and leaves the update slots
alone; an admitted update installs a version for its slot and leaves the
channels alone; a node announcement changes neither; a rejected message is a
no-op. -/
theorem epochStep_viewConsistent (verify : SigVerifier) (e : StoreEpoch)
    (m : GossipMessage) (h : e.ViewConsistent) :
    (epochStep verify e m).ViewConsistent := by
  rcases h with ⟨hann, hupd⟩
  by_cases hgate : CanonicalMessageAdmitted verify e.store m
  · cases m with
    | channelAnnouncement a =>
        have hgate' : a.signaturesValid verify ∧ a.node1 ≠ a.node2 ∧
            e.store.gossip.CompatibleWithStore a ∧
              UpdatesAuthorizedBy e.store.gossip a := hgate
        have hstore : (epochStep verify e (.channelAnnouncement a)).store.gossip =
            { e.store.gossip with
              announcements := insertReplacing a e.store.gossip.announcements } := by
          rw [epochStep_store,
            applyGossipCanonicalStore_announcement_of_admitted verify e.store a hgate']
        have hannmap : (epochStep verify e (.channelAnnouncement a)).announcementEpoch =
            setAnnouncementEpoch e.announcementEpoch a (e.epoch + 1) := by
          simp [epochStep, hgate, announcementEpochAfter]
        have hupdmap : (epochStep verify e (.channelAnnouncement a)).updateEpoch =
            e.updateEpoch := by
          simp [epochStep, hgate, updateEpochAfter]
        constructor
        · intro sc
          constructor
          · intro hsome
            rw [hannmap, setAnnouncementEpoch_ne_none_iff] at hsome
            rcases hsome with hsc | hold
            · refine ⟨a, ?_, hsc.symm⟩
              rw [hstore]
              exact mem_insertReplacing_iff.mpr (Or.inl rfl)
            · by_cases hsame : sc = a.shortChannelId
              · refine ⟨a, ?_, hsame.symm⟩
                rw [hstore]
                exact mem_insertReplacing_iff.mpr (Or.inl rfl)
              · rcases (hann sc).mp hold with ⟨b, hb, hbsc⟩
                refine ⟨b, ?_, hbsc⟩
                rw [hstore]
                exact mem_insertReplacing_of_mem_of_ne hb
                  (by intro hbsc'; exact hsame (hbsc.symm.trans hbsc'))
          · rintro ⟨b, hb, hbsc⟩
            rw [hannmap, setAnnouncementEpoch_ne_none_iff]
            rw [hstore] at hb
            rcases mem_insertReplacing_iff.mp hb with hba | ⟨hbl, hbne⟩
            · left
              exact hbsc.symm.trans
                (congrArg ChannelAnnellation.shortChannelId hba)
            · right
              have hsc_ne : sc ≠ a.shortChannelId := by
                intro hsc
                exact hbne (hbsc.trans hsc)
              have hold : e.announcementEpoch sc ≠ none :=
                (hann sc).mpr ⟨b, hbl, hbsc⟩
              simpa [hsc_ne] using hold
        · intro sc d
          have hupdates : (epochStep verify e (.channelAnnouncement a)).store.gossip.updates =
              e.store.gossip.updates := by
            rw [hstore]
          simpa [hupdmap, hupdates] using hupd sc d
    | channelUpdate u =>
        have hgate' : u.signatureValid verify ∧
            e.store.gossip.updateKeyAnnouncedDirectional u ∧
              UpdateSupersedes u e.store.gossip.updates := hgate
        have hstore : (epochStep verify e (.channelUpdate u)).store.gossip =
            { e.store.gossip with
              updates := insertUpdateCanonical u e.store.gossip.updates } := by
          rw [epochStep_store,
            applyGossipCanonicalStore_update_of_admitted verify e.store u hgate']
        have hannmap : (epochStep verify e (.channelUpdate u)).announcementEpoch =
            e.announcementEpoch := by
          simp [epochStep, hgate, announcementEpochAfter]
        have hupdmap : (epochStep verify e (.channelUpdate u)).updateEpoch =
            setUpdateEpoch e.updateEpoch u (e.epoch + 1) := by
          simp [epochStep, hgate, updateEpochAfter]
        constructor
        · intro sc
          have hanns : (epochStep verify e (.channelUpdate u)).store.gossip.announcements =
              e.store.gossip.announcements := by
            rw [hstore]
          simpa [hannmap, hanns] using hann sc
        · intro sc d
          constructor
          · intro hsome
            rw [hupdmap, setUpdateEpoch_ne_none_iff] at hsome
            by_cases hsame : sc = u.shortChannelId ∧ d = u.direction
            · refine ⟨u, ?_, hsame.1.symm, hsame.2.symm⟩
              rw [hstore]
              exact mem_insertUpdateCanonical_iff.mpr (Or.inl rfl)
            · rcases hsome with hsame' | hold
              · exact absurd hsame' hsame
              · rcases (hupd sc d).mp hold with ⟨v, hv, hvsc, hvd⟩
                refine ⟨v, ?_, hvsc, hvd⟩
                rw [hstore]
                refine mem_insertUpdateCanonical_iff.mpr (Or.inr ⟨hv, ?_⟩)
                by_cases hvsc' : v.shortChannelId = u.shortChannelId
                · right
                  intro hvd'
                  exact hsame ⟨hvsc.symm.trans hvsc', hvd.symm.trans hvd'⟩
                · left
                  exact hvsc'
          · rintro ⟨v, hv, hvsc, hvd⟩
            rw [hupdmap, setUpdateEpoch_ne_none_iff]
            rw [hstore] at hv
            rcases mem_insertUpdateCanonical_iff.mp hv with hvu | ⟨hvl, hvne⟩
            · left
              refine ⟨hvsc.symm.trans
                  (congrArg ChannelUpdate.shortChannelId hvu),
                hvd.symm.trans (congrArg ChannelUpdate.direction hvu)⟩
            · right
              have hnot : ¬ (sc = u.shortChannelId ∧ d = u.direction) := by
                rintro ⟨hsc, hdir⟩
                rcases hvne with hscne | hdirne
                · exact hscne (hvsc.trans hsc)
                · exact hdirne (hvd.trans hdir)
              have hold : e.updateEpoch sc d ≠ none :=
                (hupd sc d).mpr ⟨v, hvl, hvsc, hvd⟩
              simpa [hnot] using hold
    | nodeAnnouncement n =>
        have hgate' : n.signatureValid verify := hgate
        have hstore : (epochStep verify e (.nodeAnnouncement n)).store.gossip =
            { e.store.gossip with
              nodeAnnouncements := n :: e.store.gossip.nodeAnnouncements } := by
          rw [epochStep_store,
            applyGossipCanonicalStore_node_of_valid verify e.store n hgate']
        have hannmap : (epochStep verify e (.nodeAnnouncement n)).announcementEpoch =
            e.announcementEpoch := by
          simp [epochStep, hgate, announcementEpochAfter]
        have hupdmap : (epochStep verify e (.nodeAnnouncement n)).updateEpoch =
            e.updateEpoch := by
          simp [epochStep, hgate, updateEpochAfter]
        constructor
        · intro sc
          have hanns : (epochStep verify e (.nodeAnnouncement n)).store.gossip.announcements =
              e.store.gossip.announcements := by
            rw [hstore]
          simpa [hannmap, hanns] using hann sc
        · intro sc d
          have hupdates : (epochStep verify e (.nodeAnnouncement n)).store.gossip.updates =
              e.store.gossip.updates := by
            rw [hstore]
          simpa [hupdmap, hupdates] using hupd sc d
  · rw [epochStep_of_rejected (verify := verify) (e := e) (m := m) hgate]
    exact ⟨hann, hupd⟩

/-- **A canonical epoch step preserves version bounds.**  New labels are the
new epoch; inherited labels were already bounded by the old epoch, which the
epoch counter never decreases. -/
theorem epochStep_viewBounded (verify : SigVerifier) (e : StoreEpoch)
    (m : GossipMessage) (h : e.ViewBounded) :
    (epochStep verify e m).ViewBounded := by
  rcases h with ⟨hann, hupd⟩
  by_cases hgate : CanonicalMessageAdmitted verify e.store m
  · have hepoch : (epochStep verify e m).epoch = e.epoch + 1 :=
      epochStep_epoch_of_admitted hgate
    cases m with
    | channelAnnouncement a =>
        have hannmap : (epochStep verify e (.channelAnnouncement a)).announcementEpoch =
            setAnnouncementEpoch e.announcementEpoch a (e.epoch + 1) := by
          simp [epochStep, hgate, announcementEpochAfter]
        have hupdmap : (epochStep verify e (.channelAnnouncement a)).updateEpoch =
            e.updateEpoch := by
          simp [epochStep, hgate, updateEpochAfter]
        constructor
        · intro sc j hj
          rw [hannmap] at hj
          rcases setAnnouncementEpoch_some_cases hj with ⟨_, rfl⟩ | ⟨_, hold⟩
          · omega
          · have := hann sc j hold
            omega
        · intro sc d j hj
          rw [hupdmap] at hj
          have := hupd sc d j hj
          omega
    | channelUpdate u =>
        have hannmap : (epochStep verify e (.channelUpdate u)).announcementEpoch =
            e.announcementEpoch := by
          simp [epochStep, hgate, announcementEpochAfter]
        have hupdmap : (epochStep verify e (.channelUpdate u)).updateEpoch =
            setUpdateEpoch e.updateEpoch u (e.epoch + 1) := by
          simp [epochStep, hgate, updateEpochAfter]
        constructor
        · intro sc j hj
          rw [hannmap] at hj
          have := hann sc j hj
          omega
        · intro sc d j hj
          rw [hupdmap] at hj
          rcases setUpdateEpoch_some_cases hj with ⟨_, rfl⟩ | ⟨_, hold⟩
          · omega
          · have := hupd sc d j hold
            omega
    | nodeAnnouncement n =>
        have hannmap : (epochStep verify e (.nodeAnnouncement n)).announcementEpoch =
            e.announcementEpoch := by
          simp [epochStep, hgate, announcementEpochAfter]
        have hupdmap : (epochStep verify e (.nodeAnnouncement n)).updateEpoch =
            e.updateEpoch := by
          simp [epochStep, hgate, updateEpochAfter]
        constructor
        · intro sc j hj
          rw [hannmap] at hj
          have := hann sc j hj
          omega
        · intro sc d j hj
          rw [hupdmap] at hj
          have := hupd sc d j hj
          omega
  · rw [epochStep_of_rejected (verify := verify) (e := e) (m := m) hgate]
    exact ⟨hann, hupd⟩

/-- The epoch fold preserves version-view soundness. -/
theorem epochFold_viewConsistent (verify : SigVerifier) (e : StoreEpoch)
    (msgs : List GossipMessage) (h : e.ViewConsistent) :
    (epochFold verify e msgs).ViewConsistent := by
  induction msgs generalizing e with
  | nil => simpa [epochFold] using h
  | cons m ms ih =>
      exact ih (epochStep verify e m) (epochStep_viewConsistent verify e m h)

/-- The epoch fold preserves version bounds. -/
theorem epochFold_viewBounded (verify : SigVerifier) (e : StoreEpoch)
    (msgs : List GossipMessage) (h : e.ViewBounded) :
    (epochFold verify e msgs).ViewBounded := by
  induction msgs generalizing e with
  | nil => simpa [epochFold] using h
  | cons m ms ih =>
      exact ih (epochStep verify e m) (epochStep_viewBounded verify e m h)

/-- **Every stored announcement has an install epoch.**  In the final store of
an epoch fold that started from a sound and bounded version view, each current
announcement's channel has a recorded install epoch, and that epoch is no later
than the final epoch. -/
theorem epochFold_stored_announcement_has_install_epoch
    (verify : SigVerifier) (e : StoreEpoch) (msgs : List GossipMessage)
    (hcons : e.ViewConsistent) (hbound : e.ViewBounded) :
    ∀ a ∈ (epochFold verify e msgs).store.gossip.announcements,
      ∃ k, (epochFold verify e msgs).announcementEpoch a.shortChannelId = some k ∧
        k ≤ (epochFold verify e msgs).epoch := by
  intro a ha
  have hc := epochFold_viewConsistent verify e msgs hcons
  have hb := epochFold_viewBounded verify e msgs hbound
  have hsome : (epochFold verify e msgs).announcementEpoch a.shortChannelId ≠ none :=
    (hc.1 a.shortChannelId).mpr ⟨a, ha, rfl⟩
  cases hmap : (epochFold verify e msgs).announcementEpoch a.shortChannelId with
  | none => exact absurd hmap hsome
  | some k => exact ⟨k, rfl, hb.1 a.shortChannelId k hmap⟩

/-- **Every stored update has an install epoch.**  The per-slot version view is
sound and bounded on the final store. -/
theorem epochFold_stored_update_has_install_epoch
    (verify : SigVerifier) (e : StoreEpoch) (msgs : List GossipMessage)
    (hcons : e.ViewConsistent) (hbound : e.ViewBounded) :
    ∀ u ∈ (epochFold verify e msgs).store.gossip.updates,
      ∃ k, (epochFold verify e msgs).updateEpoch u.shortChannelId u.direction =
          some k ∧ k ≤ (epochFold verify e msgs).epoch := by
  intro u hu
  have hc := epochFold_viewConsistent verify e msgs hcons
  have hb := epochFold_viewBounded verify e msgs hbound
  have hsome : (epochFold verify e msgs).updateEpoch u.shortChannelId u.direction ≠
      none :=
    (hc.2 u.shortChannelId u.direction).mpr ⟨u, hu, rfl, rfl⟩
  cases hmap : (epochFold verify e msgs).updateEpoch u.shortChannelId u.direction with
  | none => exact absurd hmap hsome
  | some k => exact ⟨k, rfl, hb.2 u.shortChannelId u.direction k hmap⟩

/-- For the empty initial state, every stored announcement has a bounded
install epoch.  This is the non-vacuous version-view statement used by the
realistic sequence below. -/
theorem epochFold_empty_stored_announcement_has_install_epoch
    (verify : SigVerifier) (nodeKeyOf : NodeId → PubKey)
    (msgs : List GossipMessage) :
    ∀ a ∈ (epochFold verify (empty nodeKeyOf) msgs).store.gossip.announcements,
      ∃ k, (epochFold verify (empty nodeKeyOf) msgs).announcementEpoch
          a.shortChannelId = some k ∧
        k ≤ (epochFold verify (empty nodeKeyOf) msgs).epoch :=
  epochFold_stored_announcement_has_install_epoch verify (empty nodeKeyOf) msgs
    (empty_viewConsistent nodeKeyOf) (empty_viewBounded nodeKeyOf)

/-- For the empty initial state, every stored update has a bounded install
epoch. -/
theorem epochFold_empty_stored_update_has_install_epoch
    (verify : SigVerifier) (nodeKeyOf : NodeId → PubKey)
    (msgs : List GossipMessage) :
    ∀ u ∈ (epochFold verify (empty nodeKeyOf) msgs).store.gossip.updates,
      ∃ k, (epochFold verify (empty nodeKeyOf) msgs).updateEpoch
          u.shortChannelId u.direction = some k ∧
        k ≤ (epochFold verify (empty nodeKeyOf) msgs).epoch :=
  epochFold_stored_update_has_install_epoch verify (empty nodeKeyOf) msgs
    (empty_viewConsistent nodeKeyOf) (empty_viewBounded nodeKeyOf)

end StoreEpoch

/-! ## 5. Sequence-level refinement against the raw fold -/

/-- Full-store observation of a raw announcement step: the canonical view
replaces the channel record and leaves the other components selected as
before.  This is the whole-store form of the wave-7 component lemma. -/
theorem canonicalStoreView_applyGossip_announcement (s : GossipState)
    (a : ChannelAnnellation) :
    canonicalStoreView (applyGossip s (.channelAnnouncement a)) =
      { canonicalStoreView s with
        announcements := insertReplacing a (canonicalStoreView s).announcements } := by
  cases s with
  | mk ann upd node =>
      simp [canonicalStoreView, applyGossip, selectAnnouncements_cons]

/-- Full-store observation of a raw update step.  The raw global clock of the
*raw* store, not the canonical per-slot gate, is the branch condition. -/
theorem canonicalStoreView_applyGossip_update (s : GossipState)
    (u : ChannelUpdate) :
    canonicalStoreView (applyGossip s (.channelUpdate u)) =
      if s.latestUpdateTimestamp < u.timestamp then
        { canonicalStoreView s with
          updates := insertUpdateCanonical u (canonicalStoreView s).updates }
      else canonicalStoreView s := by
  cases s with
  | mk ann upd node =>
      by_cases h : latestTimestamp upd < u.timestamp <;>
        simp [canonicalStoreView, applyGossip, GossipState.applyUpdate,
          GossipState.latestUpdateTimestamp, h, selectUpdates_cons]

/-- Full-store observation of a raw node-announcement step.  Node records are
not selected or replaced. -/
theorem canonicalStoreView_applyGossip_node (s : GossipState)
    (n : NodeAnnouncement) :
    canonicalStoreView (applyGossip s (.nodeAnnouncement n)) =
      { canonicalStoreView s with
        nodeAnnouncements := n :: (canonicalStoreView s).nodeAnnouncements } := by
  cases s with
  | mk ann upd node =>
      simp [canonicalStoreView, applyGossip]

/-- **The sequence-level epoch/raw square.**

If the initial epoch store is the canonical observation of the initial raw
store, every message is canonically admitted at the epoch reached by the
prefix, and the raw global clock admits every update at the corresponding raw
state, then the epoch fold's latest gossip store is exactly the canonical
observation of the raw fold.

The hypotheses are exact:

* dropping `hobs` changes the initial comparison;
* dropping `hadm` lets a raw append survive a canonical rejection (see
  `realistic_rejected_conflict_breaks_refinement`);
* dropping `hraw` lets the canonical per-slot gate accept an update that the
  raw global clock ignores (see `clock_boundary_sequence_breaks_refinement`).

No canonical-shape hypothesis on `s` is needed: the epoch store is canonical by
construction, and the observation equations above are whole-store shape laws
for an arbitrary raw store. -/
theorem epochFold_gossip_eq_canonicalStoreView_rawFold
    (verify : SigVerifier) (e : StoreEpoch) (s : GossipState)
    (msgs : List GossipMessage)
    (hobs : e.store.gossip = canonicalStoreView s)
    (hadm : EpochAdmittedAlong verify e msgs)
    (hraw : RawAdmittedAlong s msgs) :
    (epochFold verify e msgs).store.gossip =
      canonicalStoreView (rawFold s msgs) := by
  induction msgs generalizing e s with
  | nil => simpa [epochFold, rawFold] using hobs
  | cons m ms ih =>
      rcases hadm with ⟨hgate, hrest⟩
      rcases hraw with ⟨hclock, hrawrest⟩
      have hobs' : (epochStep verify e m).store.gossip =
          canonicalStoreView (applyGossip s m) := by
        cases m with
        | channelAnnouncement a =>
            have hgate' : a.signaturesValid verify ∧ a.node1 ≠ a.node2 ∧
                e.store.gossip.CompatibleWithStore a ∧
                  UpdatesAuthorizedBy e.store.gossip a := hgate
            rw [StoreEpoch.epochStep_store,
              applyGossipCanonicalStore_announcement_of_admitted verify e.store a hgate']
            rw [canonicalStoreView_applyGossip_announcement, ← hobs]
        | channelUpdate u =>
            have hgate' : u.signatureValid verify ∧
                e.store.gossip.updateKeyAnnouncedDirectional u ∧
                  UpdateSupersedes u e.store.gossip.updates := hgate
            have hclock' : s.latestUpdateTimestamp < u.timestamp := hclock
            rw [StoreEpoch.epochStep_store,
              applyGossipCanonicalStore_update_of_admitted verify e.store u hgate']
            rw [canonicalStoreView_applyGossip_update, ite_eq_left hclock', ← hobs]
        | nodeAnnouncement n =>
            have hgate' : n.signatureValid verify := hgate
            rw [StoreEpoch.epochStep_store,
              applyGossipCanonicalStore_node_of_valid verify e.store n hgate']
            rw [canonicalStoreView_applyGossip_node, ← hobs]
      have hfold := ih (epochStep verify e m) (applyGossip s m) hobs' hrest hrawrest
      change (epochFold verify (epochStep verify e m) ms).store.gossip =
        canonicalStoreView (rawFold (applyGossip s m) ms)
      exact hfold

end LnLean.Proofs.Routing.GossipStoreEpochTargets
