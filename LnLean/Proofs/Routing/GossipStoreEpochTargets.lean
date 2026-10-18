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
  necessary by concrete sequences in §7 and §8 (rejected announcement versus
  clock boundary), and the wave-7 one-step boundary/impossibility results are
  re-exported unchanged in §6.

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

/-! ## 6. Preserved wave-7 results -/

/-- Wave-7 boundary, re-exported under the wave-8 namespace.  Canonical
per-slot admission is strictly weaker than the raw global clock. -/
theorem canonical_admission_strictly_weaker_than_raw_clock :
    ∃ (verify : SigVerifier) (cs : CanonicalStore) (u : ChannelUpdate),
      ReachableCanonicalStore verify cs ∧
        CanonicalMessageAdmitted verify cs (.channelUpdate u) ∧
          ¬ RawClockAdmits cs.gossip (.channelUpdate u) ∧
            (applyGossipCanonicalStore verify cs (.channelUpdate u)).gossip.updates =
              u :: cs.gossip.updates ∧
              applyGossip cs.gossip (.channelUpdate u) = cs.gossip ∧
                u ∉ cs.gossip.updates :=
  GossipRawRefinementTargets.canonical_admission_strictly_weaker_than_raw_clock

/-- Wave-7 impossibility, re-exported under the wave-8 namespace: no raw
append extension of `channel_announcement` can preserve canonicality. -/
theorem no_canonical_preserving_raw_announcement_extension :
    ¬ ∃ F : GossipState → GossipMessage → GossipState,
      (∀ (s : GossipState) (a : ChannelAnnellation),
        F s (.channelAnnouncement a) = applyGossip s (.channelAnnouncement a)) ∧
      (∀ s : GossipState, CanonicalAnnouncements s.announcements →
        ∀ m : GossipMessage,
          CanonicalAnnouncements (F s m).announcements) :=
  GossipRawRefinementTargets.no_canonical_preserving_raw_announcement_extension

/-- Wave-7 raw conflict counterexample, preserved unchanged. -/
theorem raw_conflicting_announcement_counterexample_preserved :
    ∃ (s : GossipState) (a : ChannelAnnellation),
      ¬ CanonicalAnnouncements
        (applyGossip s (.channelAnnouncement a)).announcements :=
  GossipRawRefinementTargets.raw_conflicting_announcement_counterexample_preserved

/-- Wave-7 ambiguity counterexample without a canonical selector, preserved
unchanged. -/
theorem ambiguous_without_canonical_preserved :
    ∃ (s : GossipState) (u v : ChannelUpdate),
      ¬ CanonicalAnnouncements s.announcements ∧
        u.shortChannelId = v.shortChannelId ∧ u.direction = v.direction ∧
          s.updateKeyAnnouncedDirectional u ∧
            s.updateKeyAnnouncedDirectional v ∧ u.signingKey ≠ v.signingKey :=
  GossipRawRefinementTargets.ambiguous_without_canonical_preserved

/-- Wave-7 canonical rejection of the conflicting re-announcement, preserved
unchanged. -/
theorem canonical_conflicting_announcement_rejection_preserved :
    ∃ (verify : SigVerifier) (cs : CanonicalNetwork)
      (a : ChannelAnnellation),
      ReachableCanonical verify cs ∧
        ¬ cs.gossip.CompatibleWithStore a ∧
          admitGossipCanonical verify cs (.channelAnnouncement a) = cs :=
  GossipRawRefinementTargets.canonical_conflicting_announcement_rejection_preserved

/-! ## 7. A concrete realistic sequence -/

private def acceptAll : SigVerifier := fun _ _ _ => true
private def kA : PubKey := ⟨ByteArray.mk #[1]⟩
private def kB : PubKey := ⟨ByteArray.empty⟩
private def kC : PubKey := ⟨ByteArray.mk #[1, 2]⟩
private def nA : NodeId := ⟨0⟩
private def nB : NodeId := ⟨1⟩
private def nC : NodeId := ⟨2⟩
private def nD : NodeId := ⟨3⟩
private def sc1 : ShortChannelId := ⟨1, 2, 3⟩
private def sc2 : ShortChannelId := ⟨4, 5, 6⟩
private def emptySig : GossipSignature := ⟨ByteArray.empty⟩
private def mkAnn (scid : ShortChannelId) (u v : NodeId) (ka kb : PubKey)
    (cap : Nat) : ChannelAnnellation :=
  { shortChannelId := scid
    node1 := u
    node2 := v
    nodeKey1 := ka
    nodeKey2 := kb
    bitcoinKey1 := ka
    bitcoinKey2 := kb
    capacitySat := cap
    digest := ByteArray.empty
    nodeSignature1 := emptySig
    nodeSignature2 := emptySig
    bitcoinSignature1 := emptySig
    bitcoinSignature2 := emptySig }
private def mkUpd (scid : ShortChannelId) (ts : Nat) (k : PubKey) :
    ChannelUpdate :=
  { shortChannelId := scid
    timestamp := ts
    messageFlags := 0
    channelFlags := 0
    cltvDelta := 1
    htlcMinimumMsat := Msat.zero
    feeBaseMsat := Msat.zero
    feeProportionalMillionths := 0
    htlcMaximumMsat := Msat.MAX
    signingKey := k
    digest := ByteArray.empty
    signature := emptySig }
private theorem nA_ne_nB : nA ≠ nB := by decide
private theorem nC_ne_nD : nC ≠ nD := by decide
private theorem nA_ne_nC : nA ≠ nC := by decide
private theorem nA_ne_nD : nA ≠ nD := by decide
private theorem nB_ne_nC : nB ≠ nC := by decide
private theorem nB_ne_nD : nB ≠ nD := by decide
private theorem sc1_ne_sc2 : sc1 ≠ sc2 := by decide
private def annA : ChannelAnnellation := mkAnn sc1 nA nB kA kB 1000
private def annB : ChannelAnnellation := mkAnn sc2 nC nD kC kB 2000
private def annA' : ChannelAnnellation := mkAnn sc1 nA nB kA kB 1500
private def annConflict : ChannelAnnellation := mkAnn sc1 nA nB kC kB 1000
private def u0 : ChannelUpdate := mkUpd sc1 10 kA
private def u1 : ChannelUpdate := mkUpd sc1 20 kA
private def v0 : ChannelUpdate := mkUpd sc2 30 kC
private def uStale : ChannelUpdate := mkUpd sc1 15 kA
private theorem kA_ne_kC : kA ≠ kC := by
  intro h
  have hs := congrArg (fun k => k.bytes.size) h
  have h1 : kA.bytes.size = 1 := by decide
  have h2 : kC.bytes.size = 2 := by decide
  rw [h1, h2] at hs
  omega
private theorem sc2_ne_sc1 : sc2 ≠ sc1 := fun h => sc1_ne_sc2 h.symm
private theorem u0_direction_eq_u1 : u0.direction = u1.direction := by rfl
private theorem u0_scid_eq_u1 : u0.shortChannelId = u1.shortChannelId := rfl
private theorem kC_ne_kA : kC ≠ kA := fun h => kA_ne_kC h.symm
private theorem annConflict_ne_annA : annConflict ≠ annA := by
  intro h
  have hk := congrArg ChannelAnnellation.nodeKey1 h
  exact kC_ne_kA (by simpa [annA, annConflict, mkAnn] using hk)
private theorem u0_ne_v0 : u0 ≠ v0 := by
  intro h
  have hs := congrArg ChannelUpdate.shortChannelId h
  exact sc1_ne_sc2 (by simpa [u0, v0, mkUpd] using hs)
private theorem annA_scid : annA.shortChannelId = sc1 := rfl
private theorem annB_scid : annB.shortChannelId = sc2 := rfl
private theorem annA'_scid : annA'.shortChannelId = sc1 := rfl
private theorem nC_ne_nA : nC ≠ nA := fun h => nA_ne_nC h.symm
private theorem nD_ne_nA : nD ≠ nA := fun h => nA_ne_nD h.symm
private theorem nC_ne_nB : nC ≠ nB := fun h => nB_ne_nC h.symm
private theorem nB_ne_nA : nB ≠ nA := fun h => nA_ne_nB h.symm
private def nodeAnn : NodeAnnouncement :=
  { nodeId := kA
    timestamp := 40
    rgbColor := ByteArray.empty
    alias := ByteArray.empty
    addresses := []
    digest := ByteArray.empty
    signature := emptySig }
private def nodeKeyOf0 : NodeId → PubKey := fun _ => kB
private noncomputable def rE0 : StoreEpoch := StoreEpoch.empty nodeKeyOf0
private noncomputable def rE1 : StoreEpoch :=
  epochStep acceptAll rE0 (.channelAnnouncement annA)
private noncomputable def rE2 : StoreEpoch :=
  epochStep acceptAll rE1 (.channelAnnouncement annB)
private noncomputable def rE3 : StoreEpoch :=
  epochStep acceptAll rE2 (.channelUpdate u0)

private theorem gateA : CanonicalMessageAdmitted acceptAll rE0.store
    (.channelAnnouncement annA) := by
  simp [CanonicalMessageAdmitted, rE0, StoreEpoch.empty,
    ChannelAnnellation.signaturesValid, signatureValid, acceptAll, annA, mkAnn,
    GossipState.CompatibleWithStore, UpdatesAuthorizedBy, nA_ne_nB]

private theorem rE1_ann : rE1.store.gossip.announcements = [annA] := by
  rw [rE1, StoreEpoch.epochStep_store,
    applyGossipCanonicalStore_announcement_of_admitted acceptAll rE0.store annA gateA]
  simp [rE0, StoreEpoch.empty, insertReplacing]

private theorem rE1_upd : rE1.store.gossip.updates = [] := by
  rw [rE1, StoreEpoch.epochStep_store,
    applyGossipCanonicalStore_announcement_of_admitted acceptAll rE0.store annA gateA]
  simp [rE0, StoreEpoch.empty]

private theorem gateB : CanonicalMessageAdmitted acceptAll rE1.store
    (.channelAnnouncement annB) := by
  simp [CanonicalMessageAdmitted, ChannelAnnellation.signaturesValid,
    signatureValid, acceptAll, annA, annB, mkAnn, GossipState.CompatibleWithStore,
    UpdatesAuthorizedBy, rE1_ann, rE1_upd, nC_ne_nD,
    nA_ne_nC, nA_ne_nD, nB_ne_nC, nB_ne_nD]

private theorem rE2_ann : rE2.store.gossip.announcements = [annB, annA] := by
  rw [rE2, StoreEpoch.epochStep_store,
    applyGossipCanonicalStore_announcement_of_admitted acceptAll rE1.store annB gateB]
  simp [rE1_ann, insertReplacing, annA, annB, mkAnn, sc1_ne_sc2]

private theorem rE2_upd : rE2.store.gossip.updates = [] := by
  rw [rE2, StoreEpoch.epochStep_store,
    applyGossipCanonicalStore_announcement_of_admitted acceptAll rE1.store annB gateB]
  simp [rE1_upd]

private theorem gateU0 : CanonicalMessageAdmitted acceptAll rE2.store
    (.channelUpdate u0) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [ChannelUpdate.signatureValid, signatureValid, acceptAll, u0, mkUpd]
  · refine GossipState.updateKeyAnnouncedDirectional_of_mem (a := annA) ?_ rfl ?_
    · rw [rE2_ann]; simp
    · rw [ChannelUpdate.direction_of_channelFlags_zero (by rfl : u0.channelFlags = 0)]
      exact ChannelAnnellation.attributesKeyForDirection_node1 annA
  · intro v hv
    rw [rE2_upd] at hv
    simp at hv

private theorem rE3_ann : rE3.store.gossip.announcements = [annB, annA] := by
  rw [rE3, StoreEpoch.epochStep_store,
    applyGossipCanonicalStore_update_of_admitted acceptAll rE2.store u0 gateU0]
  exact rE2_ann

private theorem rE3_upd : rE3.store.gossip.updates = [u0] := by
  rw [rE3, StoreEpoch.epochStep_store,
    applyGossipCanonicalStore_update_of_admitted acceptAll rE2.store u0 gateU0]
  simp [rE2_upd, insertUpdateCanonical]

private noncomputable def rE4 : StoreEpoch :=
  epochStep acceptAll rE3 (.channelUpdate u1)
private noncomputable def rE5 : StoreEpoch :=
  epochStep acceptAll rE4 (.channelUpdate v0)
private noncomputable def rE6 : StoreEpoch :=
  epochStep acceptAll rE5 (.channelAnnouncement annA')
private noncomputable def rE7 : StoreEpoch :=
  epochStep acceptAll rE6 (.channelAnnouncement annConflict)
private noncomputable def rE8 : StoreEpoch :=
  epochStep acceptAll rE7 (.channelUpdate uStale)
private noncomputable def rE9 : StoreEpoch :=
  epochStep acceptAll rE8 (.nodeAnnouncement nodeAnn)

private theorem gateU1 : CanonicalMessageAdmitted acceptAll rE3.store
    (.channelUpdate u1) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [ChannelUpdate.signatureValid, signatureValid, acceptAll]
  · refine GossipState.updateKeyAnnouncedDirectional_of_mem (a := annA) ?_ rfl ?_
    · rw [rE3_ann]; simp
    · rw [ChannelUpdate.direction_of_channelFlags_zero (by rfl : u1.channelFlags = 0)]
      exact ChannelAnnellation.attributesKeyForDirection_node1 annA
  · intro v hv hscid hdir
    rw [rE3_upd] at hv
    simp only [List.mem_singleton] at hv
    subst v
    simp [u0, u1, mkUpd]

private theorem rE4_ann : rE4.store.gossip.announcements = [annB, annA] := by
  rw [rE4, StoreEpoch.epochStep_store,
    applyGossipCanonicalStore_update_of_admitted acceptAll rE3.store u1 gateU1]
  exact rE3_ann

private theorem rE4_upd : rE4.store.gossip.updates = [u1] := by
  rw [rE4, StoreEpoch.epochStep_store,
    applyGossipCanonicalStore_update_of_admitted acceptAll rE3.store u1 gateU1]
  simp [rE3_upd, insertUpdateCanonical, u0_scid_eq_u1, u0_direction_eq_u1]

private theorem gateV0 : CanonicalMessageAdmitted acceptAll rE4.store
    (.channelUpdate v0) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [ChannelUpdate.signatureValid, signatureValid, acceptAll]
  · refine GossipState.updateKeyAnnouncedDirectional_of_mem (a := annB) ?_ rfl ?_
    · rw [rE4_ann]; simp
    · rw [ChannelUpdate.direction_of_channelFlags_zero (by rfl : v0.channelFlags = 0)]
      exact ChannelAnnellation.attributesKeyForDirection_node1 annB
  · intro v hv hscid hdir
    rw [rE4_upd] at hv
    simp only [List.mem_singleton] at hv
    subst v
    exact absurd hscid sc1_ne_sc2

private theorem rE5_ann : rE5.store.gossip.announcements = [annB, annA] := by
  rw [rE5, StoreEpoch.epochStep_store,
    applyGossipCanonicalStore_update_of_admitted acceptAll rE4.store v0 gateV0]
  exact rE4_ann

private theorem rE5_upd : rE5.store.gossip.updates = [v0, u1] := by
  rw [rE5, StoreEpoch.epochStep_store,
    applyGossipCanonicalStore_update_of_admitted acceptAll rE4.store v0 gateV0]
  simp [rE4_upd, insertUpdateCanonical, u1, v0, mkUpd, sc1_ne_sc2]

private theorem gateA' : CanonicalMessageAdmitted acceptAll rE5.store
    (.channelAnnouncement annA') := by
  simp [CanonicalMessageAdmitted, ChannelAnnellation.signaturesValid,
    signatureValid, acceptAll, annA, annA', annB, mkAnn,
    GossipState.CompatibleWithStore, UpdatesAuthorizedBy, rE5_ann, rE5_upd,
    u1, v0, mkUpd, ChannelUpdate.direction,
    ChannelAnnellation.attributesKeyForDirection, nA_ne_nB,
    nA_ne_nC, nA_ne_nD, nB_ne_nC, nB_ne_nD, nC_ne_nA, nD_ne_nA,
    nC_ne_nB, nB_ne_nA, sc1_ne_sc2, sc2_ne_sc1]

private theorem rE6_ann : rE6.store.gossip.announcements = [annA', annB] := by
  rw [rE6, StoreEpoch.epochStep_store,
    applyGossipCanonicalStore_announcement_of_admitted acceptAll rE5.store annA' gateA']
  simp [rE5_ann, insertReplacing, annA, annA', annB, mkAnn, sc1_ne_sc2,
    sc2_ne_sc1]

private theorem rE6_upd : rE6.store.gossip.updates = [v0, u1] := by
  rw [rE6, StoreEpoch.epochStep_store,
    applyGossipCanonicalStore_announcement_of_admitted acceptAll rE5.store annA' gateA']
  exact rE5_upd

private theorem rE6_node : rE6.store.gossip.nodeAnnouncements = [] := by
  rw [rE6, StoreEpoch.epochStep_store,
    applyGossipCanonicalStore_announcement_of_admitted acceptAll rE5.store annA' gateA']
  rw [rE5, StoreEpoch.epochStep_store,
    applyGossipCanonicalStore_update_of_admitted acceptAll rE4.store v0 gateV0]
  rw [rE4, StoreEpoch.epochStep_store,
    applyGossipCanonicalStore_update_of_admitted acceptAll rE3.store u1 gateU1]
  rw [rE3, StoreEpoch.epochStep_store,
    applyGossipCanonicalStore_update_of_admitted acceptAll rE2.store u0 gateU0]
  rw [rE2, StoreEpoch.epochStep_store,
    applyGossipCanonicalStore_announcement_of_admitted acceptAll rE1.store annB gateB]
  rw [rE1, StoreEpoch.epochStep_store,
    applyGossipCanonicalStore_announcement_of_admitted acceptAll rE0.store annA gateA]
  simp [rE0, StoreEpoch.empty]

private theorem notGateConflict : ¬ CanonicalMessageAdmitted acceptAll rE6.store
    (.channelAnnouncement annConflict) := by
  intro h
  rcases h with ⟨_, _, hcompat, _⟩
  have hmem : annA' ∈ rE6.store.gossip.announcements := by
    rw [rE6_ann]; simp
  have hkey := (hcompat annA' hmem).1 rfl
  exact kA_ne_kC (by simpa [annA', annConflict, mkAnn] using hkey)

private theorem rE7_eq : rE7 = rE6 := by
  rw [rE7, StoreEpoch.epochStep_of_rejected (verify := acceptAll) (e := rE6)
    (m := .channelAnnouncement annConflict) notGateConflict]

private theorem notGateStale : ¬ CanonicalMessageAdmitted acceptAll rE6.store
    (.channelUpdate uStale) := by
  intro h
  rcases h with ⟨_, _, hsup⟩
  have hmem : u1 ∈ rE6.store.gossip.updates := by
    rw [rE6_upd]; simp
  have hdir : u1.direction = uStale.direction := by
    simp [u1, uStale, mkUpd, ChannelUpdate.direction]
  have hlt := hsup u1 hmem rfl hdir
  simp [u1, uStale, mkUpd] at hlt

private theorem rE8_eq : rE8 = rE7 := by
  rw [rE8, StoreEpoch.epochStep_of_rejected (verify := acceptAll) (e := rE7)
    (m := .channelUpdate uStale) (by rw [rE7_eq]; exact notGateStale)]

private theorem gateNode : CanonicalMessageAdmitted acceptAll rE6.store
    (.nodeAnnouncement nodeAnn) := by
  simp [CanonicalMessageAdmitted, NodeAnnouncement.signatureValid,
    signatureValid, acceptAll]

private theorem rE9_ann : rE9.store.gossip.announcements = [annA', annB] := by
  rw [rE9, StoreEpoch.epochStep_store, rE8_eq, rE7_eq,
    applyGossipCanonicalStore_node_of_valid acceptAll rE6.store nodeAnn gateNode]
  exact rE6_ann

private theorem rE9_upd : rE9.store.gossip.updates = [v0, u1] := by
  rw [rE9, StoreEpoch.epochStep_store, rE8_eq, rE7_eq,
    applyGossipCanonicalStore_node_of_valid acceptAll rE6.store nodeAnn gateNode]
  exact rE6_upd

private theorem rE9_node : rE9.store.gossip.nodeAnnouncements = [nodeAnn] := by
  rw [rE9, StoreEpoch.epochStep_store, rE8_eq, rE7_eq,
    applyGossipCanonicalStore_node_of_valid acceptAll rE6.store nodeAnn gateNode]
  simp [rE6_node]

private theorem rE1_epoch : rE1.epoch = 1 := by
  rw [rE1, StoreEpoch.epochStep_epoch_of_admitted (verify := acceptAll) (e := rE0)
    (m := .channelAnnouncement annA) gateA]
  rfl

private theorem rE2_epoch : rE2.epoch = 2 := by
  rw [rE2, StoreEpoch.epochStep_epoch_of_admitted (verify := acceptAll) (e := rE1)
    (m := .channelAnnouncement annB) gateB, rE1_epoch]

private theorem rE3_epoch : rE3.epoch = 3 := by
  rw [rE3, StoreEpoch.epochStep_epoch_of_admitted (verify := acceptAll) (e := rE2)
    (m := .channelUpdate u0) gateU0, rE2_epoch]

private theorem rE4_epoch : rE4.epoch = 4 := by
  rw [rE4, StoreEpoch.epochStep_epoch_of_admitted (verify := acceptAll) (e := rE3)
    (m := .channelUpdate u1) gateU1, rE3_epoch]

private theorem rE5_epoch : rE5.epoch = 5 := by
  rw [rE5, StoreEpoch.epochStep_epoch_of_admitted (verify := acceptAll) (e := rE4)
    (m := .channelUpdate v0) gateV0, rE4_epoch]

private theorem rE6_epoch : rE6.epoch = 6 := by
  rw [rE6, StoreEpoch.epochStep_epoch_of_admitted (verify := acceptAll) (e := rE5)
    (m := .channelAnnouncement annA') gateA', rE5_epoch]

private theorem rE7_epoch : rE7.epoch = 6 := by
  rw [rE7_eq, rE6_epoch]

private theorem rE8_epoch : rE8.epoch = 6 := by
  rw [rE8_eq, rE7_epoch]

private theorem rE9_epoch : rE9.epoch = 7 := by
  rw [rE9, StoreEpoch.epochStep_epoch_of_admitted (verify := acceptAll) (e := rE8)
    (m := .nodeAnnouncement nodeAnn) gateNode, rE8_epoch]

private theorem rE1_history : rE1.history =
    [ReplacementEvent.announcement 1 annA []] := by
  rw [rE1, StoreEpoch.epochStep_history_of_admitted (verify := acceptAll) (e := rE0)
    (m := .channelAnnouncement annA) gateA]
  simp [StoreEpoch.eventOf, rE0, StoreEpoch.empty, replacedAnnouncements]

private theorem rE2_history : rE2.history =
    ReplacementEvent.announcement 2 annB [] :: rE1.history := by
  rw [rE2, StoreEpoch.epochStep_history_of_admitted (verify := acceptAll) (e := rE1)
    (m := .channelAnnouncement annB) gateB]
  simp [StoreEpoch.eventOf, rE1_ann, replacedAnnouncements, annA, annB, mkAnn,
    sc1_ne_sc2, rE1_epoch]

private theorem rE3_history : rE3.history =
    ReplacementEvent.update 3 u0 [] :: rE2.history := by
  rw [rE3, StoreEpoch.epochStep_history_of_admitted (verify := acceptAll) (e := rE2)
    (m := .channelUpdate u0) gateU0]
  simp [StoreEpoch.eventOf, rE2_upd, replacedUpdates, rE2_epoch]

private theorem rE4_history : rE4.history =
    ReplacementEvent.update 4 u1 [u0] :: rE3.history := by
  rw [rE4, StoreEpoch.epochStep_history_of_admitted (verify := acceptAll) (e := rE3)
    (m := .channelUpdate u1) gateU1]
  simp [StoreEpoch.eventOf, rE3_upd, replacedUpdates, u0_scid_eq_u1,
    u0_direction_eq_u1, rE3_epoch]

private theorem rE5_history : rE5.history =
    ReplacementEvent.update 5 v0 [] :: rE4.history := by
  rw [rE5, StoreEpoch.epochStep_history_of_admitted (verify := acceptAll) (e := rE4)
    (m := .channelUpdate v0) gateV0]
  simp [StoreEpoch.eventOf, rE4_upd, replacedUpdates, u1, v0, mkUpd, sc1_ne_sc2,
    rE4_epoch]

private theorem rE6_history : rE6.history =
    ReplacementEvent.announcement 6 annA' [annA] :: rE5.history := by
  rw [rE6, StoreEpoch.epochStep_history_of_admitted (verify := acceptAll) (e := rE5)
    (m := .channelAnnouncement annA') gateA']
  simp [StoreEpoch.eventOf, rE5_ann, replacedAnnouncements, annA_scid,
    annB_scid, annA'_scid, sc2_ne_sc1, rE5_epoch]

private theorem rE9_history : rE9.history =
    [ReplacementEvent.node 7 nodeAnn,
     ReplacementEvent.announcement 6 annA' [annA],
     ReplacementEvent.update 5 v0 [],
     ReplacementEvent.update 4 u1 [u0],
     ReplacementEvent.update 3 u0 [],
     ReplacementEvent.announcement 2 annB [],
     ReplacementEvent.announcement 1 annA []] := by
  rw [rE9, StoreEpoch.epochStep_history_of_admitted (verify := acceptAll) (e := rE8)
      (m := .nodeAnnouncement nodeAnn) gateNode,
    rE8_eq, rE7_eq, rE6_history, rE5_history, rE4_history, rE3_history,
    rE2_history, rE1_history]
  simp [StoreEpoch.eventOf, rE8_epoch, rE6_epoch]


private def admittedMsgs : List GossipMessage :=
  [.channelAnnouncement annA, .channelAnnouncement annB,
   .channelUpdate u0, .channelUpdate u1, .channelUpdate v0,
   .channelAnnouncement annA', .nodeAnnouncement nodeAnn]

private noncomputable def admittedEpoch : StoreEpoch :=
  epochFold acceptAll rE0 admittedMsgs

private theorem rE9_eq_node : rE9 = epochStep acceptAll rE6
    (.nodeAnnouncement nodeAnn) := by
  rw [rE9, rE8_eq, rE7_eq]

private theorem admittedEpoch_eq : admittedEpoch = rE9 := by
  rw [rE9_eq_node]
  rfl

private theorem admittedAlong : EpochAdmittedAlong acceptAll rE0 admittedMsgs := by
  refine ⟨gateA, ?_⟩
  change EpochAdmittedAlong acceptAll rE1
    [.channelAnnouncement annB, .channelUpdate u0, .channelUpdate u1,
     .channelUpdate v0, .channelAnnouncement annA', .nodeAnnouncement nodeAnn]
  refine ⟨gateB, ?_⟩
  change EpochAdmittedAlong acceptAll rE2
    [.channelUpdate u0, .channelUpdate u1, .channelUpdate v0,
     .channelAnnouncement annA', .nodeAnnouncement nodeAnn]
  refine ⟨gateU0, ?_⟩
  change EpochAdmittedAlong acceptAll rE3
    [.channelUpdate u1, .channelUpdate v0, .channelAnnouncement annA',
     .nodeAnnouncement nodeAnn]
  refine ⟨gateU1, ?_⟩
  change EpochAdmittedAlong acceptAll rE4
    [.channelUpdate v0, .channelAnnouncement annA', .nodeAnnouncement nodeAnn]
  refine ⟨gateV0, ?_⟩
  change EpochAdmittedAlong acceptAll rE5
    [.channelAnnouncement annA', .nodeAnnouncement nodeAnn]
  refine ⟨gateA', ?_⟩
  change EpochAdmittedAlong acceptAll rE6 [.nodeAnnouncement nodeAnn]
  exact ⟨gateNode, trivial⟩

private theorem admittedRaw : RawAdmittedAlong ⟨[], [], []⟩ admittedMsgs := by
  simp [RawAdmittedAlong, RawClockAdmits, admittedMsgs, rawFold, applyGossip,
    GossipState.applyUpdate, GossipState.latestUpdateTimestamp, latestTimestamp,
    u0, u1, v0, mkUpd]

private theorem admittedSquare :
    admittedEpoch.store.gossip =
      canonicalStoreView (rawFold ⟨[], [], []⟩ admittedMsgs) := by
  exact epochFold_gossip_eq_canonicalStoreView_rawFold acceptAll rE0 ⟨[], [], []⟩
    admittedMsgs (by simp [rE0, StoreEpoch.empty, canonicalStoreView])
    admittedAlong admittedRaw

private theorem rE9_empty_view : canonicalStoreView ⟨[], [], []⟩ =
    rE0.store.gossip := by
  simp [rE0, StoreEpoch.empty, canonicalStoreView]

private theorem admittedSquare_final :
    rE9.store.gossip =
      canonicalStoreView (rawFold ⟨[], [], []⟩ admittedMsgs) := by
  rw [← admittedEpoch_eq]
  exact admittedSquare

/-! ## 8. Divergence witnesses -/

-- Conflict sequence
private def conflictMsgs : List GossipMessage :=
  [.channelAnnouncement annA, .channelAnnouncement annConflict]

private noncomputable def conflictEpoch : StoreEpoch :=
  epochFold acceptAll rE0 conflictMsgs

private theorem notGateConflict_rE1 : ¬ CanonicalMessageAdmitted acceptAll rE1.store
    (.channelAnnouncement annConflict) := by
  intro h
  rcases h with ⟨_, _, hcompat, _⟩
  have hmem : annA ∈ rE1.store.gossip.announcements := by
    rw [rE1_ann]; simp
  have hkey := (hcompat annA hmem).1 rfl
  exact kA_ne_kC (by simpa [annA, annConflict, mkAnn] using hkey)

private theorem conflictEpoch_ann : conflictEpoch.store.gossip.announcements = [annA] := by
  change (epochStep acceptAll rE1 (.channelAnnouncement annConflict)).store.gossip.announcements =
    [annA]
  rw [StoreEpoch.epochStep_of_rejected (verify := acceptAll) (e := rE1)
    (m := .channelAnnouncement annConflict) notGateConflict_rE1]
  exact rE1_ann

private theorem conflictRawView_ann :
    (canonicalStoreView (rawFold ⟨[], [], []⟩ conflictMsgs)).announcements =
      [annConflict] := by
  simp [canonicalStoreView, rawFold, applyGossip, conflictMsgs, selectAnnouncements,
    insertReplacing, annA, annConflict, mkAnn, annA_scid]

private theorem conflictSquare_fails :
    conflictEpoch.store.gossip ≠
      canonicalStoreView (rawFold ⟨[], [], []⟩ conflictMsgs) := by
  intro h
  have hann := congrArg (fun s => s.announcements) h
  rw [conflictEpoch_ann, conflictRawView_ann] at hann
  have hann' : annA = annConflict := by simpa using hann
  exact annConflict_ne_annA hann'.symm

private theorem conflict_not_admitted :
    ¬ EpochAdmittedAlong acceptAll rE0 conflictMsgs := by
  intro h
  exact notGateConflict_rE1 h.2.1

private theorem conflictRawAdmitted : RawAdmittedAlong ⟨[], [], []⟩ conflictMsgs := by
  simp [RawAdmittedAlong, RawClockAdmits, conflictMsgs]

-- Clock sequence
private def clockMsgs : List GossipMessage :=
  [.channelAnnouncement annA, .channelAnnouncement annB,
   .channelUpdate v0, .channelUpdate u0]

private noncomputable def cE0 : StoreEpoch := rE0
private noncomputable def cE1 : StoreEpoch := rE1
private noncomputable def cE2 : StoreEpoch := rE2
private noncomputable def cE3 : StoreEpoch := epochStep acceptAll rE2 (.channelUpdate v0)
private noncomputable def cE4 : StoreEpoch := epochStep acceptAll cE3 (.channelUpdate u0)

private theorem gateV0_c : CanonicalMessageAdmitted acceptAll rE2.store
    (.channelUpdate v0) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [ChannelUpdate.signatureValid, signatureValid, acceptAll]
  · refine GossipState.updateKeyAnnouncedDirectional_of_mem (a := annB) ?_ rfl ?_
    · rw [rE2_ann]; simp
    · rw [ChannelUpdate.direction_of_channelFlags_zero (by rfl : v0.channelFlags = 0)]
      exact ChannelAnnellation.attributesKeyForDirection_node1 annB
  · intro v hv hscid hdir
    rw [rE2_upd] at hv
    simp at hv

private theorem cE3_ann : cE3.store.gossip.announcements = [annB, annA] := by
  rw [cE3, StoreEpoch.epochStep_store,
    applyGossipCanonicalStore_update_of_admitted acceptAll rE2.store v0 gateV0_c]
  exact rE2_ann

private theorem cE3_upd : cE3.store.gossip.updates = [v0] := by
  rw [cE3, StoreEpoch.epochStep_store,
    applyGossipCanonicalStore_update_of_admitted acceptAll rE2.store v0 gateV0_c]
  simp [rE2_upd, insertUpdateCanonical]

private theorem gateU0_c : CanonicalMessageAdmitted acceptAll cE3.store
    (.channelUpdate u0) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [ChannelUpdate.signatureValid, signatureValid, acceptAll]
  · refine GossipState.updateKeyAnnouncedDirectional_of_mem (a := annA) ?_ rfl ?_
    · rw [cE3_ann]; simp
    · rw [ChannelUpdate.direction_of_channelFlags_zero (by rfl : u0.channelFlags = 0)]
      exact ChannelAnnellation.attributesKeyForDirection_node1 annA
  · intro v hv hscid hdir
    rw [cE3_upd] at hv
    simp only [List.mem_singleton] at hv
    subst v
    exact absurd hscid sc2_ne_sc1

private theorem cE4_upd : cE4.store.gossip.updates = [u0, v0] := by
  rw [cE4, StoreEpoch.epochStep_store,
    applyGossipCanonicalStore_update_of_admitted acceptAll cE3.store u0 gateU0_c]
  simp [cE3_upd, insertUpdateCanonical, v0, u0, mkUpd, sc2_ne_sc1]

private theorem clockAlong : EpochAdmittedAlong acceptAll rE0 clockMsgs := by
  refine ⟨gateA, ?_⟩
  change EpochAdmittedAlong acceptAll rE1
    [.channelAnnouncement annB, .channelUpdate v0, .channelUpdate u0]
  refine ⟨gateB, ?_⟩
  change EpochAdmittedAlong acceptAll cE2 [.channelUpdate v0, .channelUpdate u0]
  refine ⟨gateV0_c, ?_⟩
  change EpochAdmittedAlong acceptAll cE3 [.channelUpdate u0]
  exact ⟨gateU0_c, trivial⟩

private theorem clockRaw_not_admitted :
    ¬ RawClockAdmits (rawFold ⟨[], [], []⟩
      [.channelAnnouncement annA, .channelAnnouncement annB, .channelUpdate v0])
      (.channelUpdate u0) := by
  simp [RawClockAdmits, rawFold, applyGossip, GossipState.applyUpdate,
    GossipState.latestUpdateTimestamp, latestTimestamp, v0, u0, mkUpd]

private theorem clock_not_raw :
    ¬ RawAdmittedAlong ⟨[], [], []⟩ clockMsgs := by
  intro h
  exact clockRaw_not_admitted h.2.2.2.1

private theorem clockCanonicalView_upd :
    (canonicalStoreView (rawFold ⟨[], [], []⟩ clockMsgs)).updates = [v0] := by
  simp [canonicalStoreView, rawFold, applyGossip, clockMsgs, selectUpdates,
    insertUpdateCanonical, GossipState.applyUpdate,
    GossipState.latestUpdateTimestamp, latestTimestamp, v0, u0, mkUpd]

private theorem clockSquare_fails :
    (epochFold acceptAll rE0 clockMsgs).store.gossip ≠
      canonicalStoreView (rawFold ⟨[], [], []⟩ clockMsgs) := by
  intro h
  have hupd := congrArg (fun s => s.updates) h
  change cE4.store.gossip.updates = _ at hupd
  rw [cE4_upd, clockCanonicalView_upd] at hupd
  have hneq : u0 = v0 := by simpa using hupd
  exact u0_ne_v0 hneq

/-! ## 9. Public witness statements -/

/-- A concrete nine-message sequence: announce two channels, install and then
supersede a directional update, install an update on the other channel,
re-announce the first channel, reject a conflicting re-announcement, reject a
stale update, and append a node announcement.

The final epoch is `7` (seven admissions, two rejections).  The history is
newest-first and records the exact replaced record for each supersession. -/
theorem realistic_epoch_store_history :
    ∃ (verify : SigVerifier) (e : StoreEpoch) (a a' b : ChannelAnnellation)
      (u0 u1 v0 : ChannelUpdate) (n : NodeAnnouncement),
      e.epoch = 7 ∧
      e.store.gossip.announcements = [a', b] ∧
      e.store.gossip.updates = [v0, u1] ∧
      e.store.gossip.nodeAnnouncements = [n] ∧
      e.history = [ReplacementEvent.node 7 n,
                   ReplacementEvent.announcement 6 a' [a],
                   ReplacementEvent.update 5 v0 [],
                   ReplacementEvent.update 4 u1 [u0],
                   ReplacementEvent.update 3 u0 [],
                   ReplacementEvent.announcement 2 b [],
                   ReplacementEvent.announcement 1 a []] ∧
      e.history.length = 7 := by
  refine ⟨acceptAll, rE9, annA, annA', annB, u0, u1, v0, nodeAnn,
    rE9_epoch, rE9_ann, rE9_upd, rE9_node, rE9_history, ?_⟩
  rw [rE9_history]
  rfl

/-- The realistic history records both required supersessions: the same-slot
update replacement and the channel re-announcement replacement. -/
theorem realistic_history_records_supersession :
    ∃ (verify : SigVerifier) (e : StoreEpoch) (a a' : ChannelAnnellation)
      (u0 u1 : ChannelUpdate),
      ReplacementEvent.update 4 u1 [u0] ∈ e.history ∧
        ReplacementEvent.announcement 6 a' [a] ∈ e.history := by
  refine ⟨acceptAll, rE9, annA, annA', u0, u1, ?_, ?_⟩
  · rw [rE9_history]; simp
  · rw [rE9_history]; simp

/-- The two rejected messages are complete no-ops: the epoch stays at `6`
through both, and the epoch store is literally unchanged. -/
theorem realistic_rejected_messages_do_not_increment_epoch :
    ∃ (verify : SigVerifier) (eBefore eConflict eStale : StoreEpoch)
      (a : ChannelAnnellation) (u : ChannelUpdate),
      eBefore.epoch = 6 ∧ eConflict.epoch = 6 ∧ eStale.epoch = 6 ∧
        eConflict = eBefore ∧ eStale = eBefore := by
  exact ⟨acceptAll, rE6, rE7, rE8, annConflict, uStale,
    rE6_epoch, rE7_epoch, rE8_epoch, rE7_eq, by rw [rE8_eq, rE7_eq]⟩

/-- The all-admitted subsequence of the realistic sequence satisfies the
sequence-level epoch/raw square.  Its seven messages are individually admitted
by the canonical gates and by the raw global clock. -/
theorem realistic_admitted_sequence_square :
    ∃ (verify : SigVerifier) (e : StoreEpoch) (s : GossipState)
      (msgs : List GossipMessage),
      msgs.length = 7 ∧
      e.store.gossip = canonicalStoreView s ∧
      EpochAdmittedAlong verify e msgs ∧
      RawAdmittedAlong s msgs ∧
      (epochFold verify e msgs).store.gossip =
        canonicalStoreView (rawFold s msgs) := by
  exact ⟨acceptAll, rE0, ⟨[], [], []⟩, admittedMsgs, rfl,
    by simp [rE0, StoreEpoch.empty, canonicalStoreView], admittedAlong,
    admittedRaw, admittedSquare⟩

/-- Dropping only the canonical-admission hypothesis breaks the square: the
conflicting re-announcement is appended by raw `applyGossip` but rejected by the
canonical store.  All other hypotheses (initial observation and raw admission)
hold. -/
theorem realistic_rejected_conflict_breaks_refinement :
    ∃ (verify : SigVerifier) (e : StoreEpoch) (s : GossipState)
      (msgs : List GossipMessage),
      e.store.gossip = canonicalStoreView s ∧
      RawAdmittedAlong s msgs ∧
      ¬ EpochAdmittedAlong verify e msgs ∧
      (epochFold verify e msgs).store.gossip ≠
        canonicalStoreView (rawFold s msgs) := by
  exact ⟨acceptAll, rE0, ⟨[], [], []⟩, conflictMsgs,
    by simp [rE0, StoreEpoch.empty, canonicalStoreView], conflictRawAdmitted,
    conflict_not_admitted, conflictSquare_fails⟩

/-- Dropping only the raw-clock hypothesis breaks the square: after a stored
update at timestamp `30`, a canonically admitted per-slot update at timestamp
`10` is ignored by the raw global clock.  All other hypotheses (initial
observation and canonical admission) hold. -/
theorem clock_boundary_sequence_breaks_refinement :
    ∃ (verify : SigVerifier) (e : StoreEpoch) (s : GossipState)
      (msgs : List GossipMessage),
      e.store.gossip = canonicalStoreView s ∧
      EpochAdmittedAlong verify e msgs ∧
      ¬ RawAdmittedAlong s msgs ∧
      (epochFold verify e msgs).store.gossip ≠
        canonicalStoreView (rawFold s msgs) := by
  exact ⟨acceptAll, rE0, ⟨[], [], []⟩, clockMsgs,
    by simp [rE0, StoreEpoch.empty, canonicalStoreView], clockAlong,
    clock_not_raw, clockSquare_fails⟩

end LnLean.Proofs.Routing.GossipStoreEpochTargets
