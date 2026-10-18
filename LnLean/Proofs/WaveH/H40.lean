import LnLean.Proofs.Routing.GossipRawRefinementTargets

/-!
# H40 — epoch/replacement refinement of the canonical wrapper (RT-01, RT-02)

Wave-8 lane `H40`, issues `RT-01` / `RT-02`.

Wave 7 (`GossipRawRefinementTargets`) proved the **one-step** refinement
square: on a canonically shaped store, when the canonical admission gates hold
and the raw global clock admits the message,

  `canonicalStoreView (applyGossip cs.gossip m) =
     (applyGossipCanonicalStore verify cs m).gossip`.

The open question for this lane was the **sequence** version over a realistic
replacement/epoch trajectory: gossip is delivered as a finite schedule of
messages, not one at a time, and a production store advances a clock/epoch on
every delivery.  This module answers it exactly.

## 1. Sequence semantics

* `runRaw s msgs` folds raw `applyGossip` over a delivered message list.
* `runCanonical verify cs msgs` folds `applyGossipCanonicalStore` over the
  same list.
* `CanonicalGatesHold verify cs msgs` is the *state-relative* admission
  premise: every message passes `CanonicalMessageAdmitted` at the canonical
  state reached by the preceding messages.
* `RawClockHolds s msgs` is the corresponding raw-clock premise: every message
  is admitted by the raw global clock at the raw state reached by the
  preceding messages.

## 2. The exact sequence projection square

`canonicalStoreView_runRaw_eq_runCanonical` proves

  `canonicalStoreView (runRaw cs.gossip msgs) =
     (runCanonical verify cs msgs).gossip`

from four exactly stated premises:

1. `CanonicalStoreShape cs.gossip` — the initial store is already in canonical
   selector shape (wave 7: every canonically reachable store is);
2. `UpdatesDescending cs.gossip.updates` — the raw update list is
   timestamp-descending (newest first), which makes the raw global clock equal
   to the clock of its canonical observation
   (`latestTimestamp_selectUpdates_eq_of_descending`);
3. `CanonicalGatesHold verify cs msgs` — canonical admission at every step;
4. `RawClockHolds cs.gossip msgs` — raw-clock admission at every step.

The clock premise is *not* removable: `raw_clock_obstruction` and
`clock_premise_necessary` mechanise the wave-7 boundary witness at the
sequence level.  A canonically reachable store admits a per-slot update that
the raw global clock rejects, so the square fails with only the canonical
gates.

## 3. Epoch model

`EpochStore` carries the canonical store, the last delivered epoch number, and
an explicit epoch clock.  `EpochEvent` is one `(epoch, message)` delivery.

* `EpochStrictlyAdvances clock msgs` is the real-time premise: every delivered
  update's timestamp is strictly greater than the current epoch clock; other
  messages leave the clock unchanged.  This is the exact "replacement/epoch
  sequence" assumption.  It *derives* the raw clock premise
  (`rawClockHolds_of_epochStrict`) and bounds the raw clock
  (`latestUpdateTimestamp_le_clockRun`).
* `EpochChainFrom` / `EpochMonotone` state non-decreasing epoch numbers.
* `RealisticEpochSequence verify k events` bundles: monotone epochs, strictly
  advancing update timestamps, and canonical admission for every event.

`realisticEpochSequence_projection_square` is the headline corollary: for
every realistic epoch sequence, the canonical epoch run projects exactly onto
the canonical observation of the raw run.

`EpochReachable`, `runEpoch_store_reachable`, and the projection lemmas
transport **all** wave-7 canonical reachable invariants
(`CanonicalStoreAdmitted`: stored-announcement validity, direction-keyed
update attribution, node-key consistency, canonical announcements, per-slot
update uniqueness, canonical selector shape) to every epoch run.

## 4. Preserved negative results

The raw non-refinement counterexample
(`raw_applyGossip_accepts_conflicting_announcement`) is re-exported unchanged.
No `applyGossip`, `GossipState.applyUpdate`, `canonicalStoreView`, wave-6/7
definition or theorem is modified.

## Scope

* `SigVerifier` stays abstract; no unforgeability claim is made.
* The epoch clock is a transport/wall-clock model, not BOLT 7's exact
  "greater than the previous `channel_update`" rule at the global layer; the
  per-slot canonical gate is the BOLT 7 rule, and the epoch premise is the
  extra ordering that makes raw and canonical runs comparable.
* The raw store is still append-only and non-canonical; the theorem is about
  the canonical *observation* of its run, not about a change to raw insertion.
* No network, liveness, chain, or rate-limit claim.

No `sorry`, no `axiom`, no `admit`, no `native_decide`, no `unsafe`, no
`@[implemented_by]`.
-/

namespace LnLean.Proofs.WaveH.H40

open LnLean.Routing
open LnLean.Proofs.Routing.GossipTargets
open LnLean.Proofs.Routing.GossipAttributionTargets
open LnLean.Proofs.Routing.GossipKeyConsistencyTargets
open LnLean.Proofs.Routing.GossipCanonicalTargets
open LnLean.Proofs.Routing.GossipRawRefinementTargets
open Classical

set_option autoImplicit false

/-! ## 1. Sequence semantics -/

/-- Fold the raw, append-only gossip transition over a delivered message list. -/
def runRaw : GossipState → List GossipMessage → GossipState
  | s, [] => s
  | s, m :: ms => runRaw (applyGossip s m) ms

/-- Fold the canonicalising store transition over a delivered message list. -/
noncomputable def runCanonical (verify : SigVerifier) :
    CanonicalStore → List GossipMessage → CanonicalStore
  | cs, [] => cs
  | cs, m :: ms => runCanonical verify (applyGossipCanonicalStore verify cs m) ms

@[simp] theorem runRaw_nil (s : GossipState) : runRaw s [] = s := rfl

@[simp] theorem runRaw_cons (s : GossipState) (m : GossipMessage)
    (ms : List GossipMessage) :
    runRaw s (m :: ms) = runRaw (applyGossip s m) ms := rfl

@[simp] theorem runCanonical_nil (verify : SigVerifier) (cs : CanonicalStore) :
    runCanonical verify cs [] = cs := rfl

@[simp] theorem runCanonical_cons (verify : SigVerifier) (cs : CanonicalStore)
    (m : GossipMessage) (ms : List GossipMessage) :
    runCanonical verify cs (m :: ms) =
      runCanonical verify (applyGossipCanonicalStore verify cs m) ms := rfl

/-- Canonical admission holds at every prefix of the sequence. -/
def CanonicalGatesHold (verify : SigVerifier) (cs : CanonicalStore) :
    List GossipMessage → Prop
  | [] => True
  | m :: ms => CanonicalMessageAdmitted verify cs m ∧
      CanonicalGatesHold verify (applyGossipCanonicalStore verify cs m) ms

/-- The raw global clock admits every prefix of the sequence. -/
def RawClockHolds (s : GossipState) : List GossipMessage → Prop
  | [] => True
  | m :: ms => RawClockAdmits s m ∧ RawClockHolds (applyGossip s m) ms

/-! ## 2. Timestamp-descending raw update lists -/

/-- The raw update list is strictly timestamp-descending (newest first).  Raw
insertion maintains this whenever it actually inserts; it is the shape that
makes the raw global clock equal to the clock of the canonical observation. -/
def UpdatesDescending (l : List ChannelUpdate) : Prop :=
  l.Pairwise (fun a b => b.timestamp < a.timestamp)

theorem updatesDescending_nil : UpdatesDescending ([] : List ChannelUpdate) :=
  List.Pairwise.nil

theorem updatesDescending_cons_iff {u : ChannelUpdate} {l : List ChannelUpdate} :
    UpdatesDescending (u :: l) ↔
      (∀ v ∈ l, v.timestamp < u.timestamp) ∧ UpdatesDescending l :=
  List.pairwise_cons

/-- The fold of `max` is unchanged when every element is at most the
accumulator. -/
theorem foldl_max_eq_of_forall_le {l : List ChannelUpdate} {t : Timestamp}
    (h : ∀ v ∈ l, v.timestamp ≤ t) :
    l.foldl (fun acc u => max acc u.timestamp) t = t := by
  induction l generalizing t with
  | nil => rfl
  | cons u us ih =>
      simp only [List.foldl_cons]
      rw [Nat.max_eq_left (h u (by simp))]
      exact ih (fun v hv => h v (List.mem_cons_of_mem _ hv))

/-- The fold of `max` stays below `t` when the accumulator and every element
are at most `t`. -/
theorem foldl_max_le_of_forall_le {l : List ChannelUpdate} {a t : Timestamp}
    (ha : a ≤ t) (h : ∀ v ∈ l, v.timestamp ≤ t) :
    l.foldl (fun acc u => max acc u.timestamp) a ≤ t := by
  induction l generalizing a with
  | nil => exact ha
  | cons u us ih =>
      simp only [List.foldl_cons]
      exact ih (Nat.max_le.mpr ⟨ha, h u (by simp)⟩)
        (fun v hv => h v (List.mem_cons_of_mem _ hv))

/-- Unfolding `latestTimestamp` at a cons. -/
theorem latestTimestamp_cons (u : ChannelUpdate) (l : List ChannelUpdate) :
    latestTimestamp (u :: l) =
      l.foldl (fun acc v => max acc v.timestamp) u.timestamp := by
  simp [latestTimestamp, Nat.max_eq_right (Nat.zero_le u.timestamp)]

/-- On a descending list the newest timestamp is the head's. -/
theorem latestTimestamp_eq_of_descending {u : ChannelUpdate}
    {l : List ChannelUpdate} (h : UpdatesDescending (u :: l)) :
    latestTimestamp (u :: l) = u.timestamp := by
  rw [latestTimestamp_cons]
  exact foldl_max_eq_of_forall_le
    (fun v hv => Nat.le_of_lt ((updatesDescending_cons_iff.mp h).1 v hv))

/-- A list whose timestamps are all at most `t` has latest timestamp at most
`t`. -/
theorem latestTimestamp_le_of_forall_le {l : List ChannelUpdate} {t : Timestamp}
    (h : ∀ v ∈ l, v.timestamp ≤ t) : latestTimestamp l ≤ t := by
  unfold latestTimestamp
  exact foldl_max_le_of_forall_le (Nat.zero_le t) h

/-- A strictly newer raw update keeps the descending shape. -/
theorem updatesDescending_applyUpdate {s : GossipState} {u : ChannelUpdate}
    (h : UpdatesDescending s.updates)
    (hnew : s.latestUpdateTimestamp < u.timestamp) :
    UpdatesDescending (s.applyUpdate u).updates := by
  rw [GossipState.applyUpdate_new s u hnew]
  rw [updatesDescending_cons_iff]
  exact ⟨fun v hv => Nat.lt_of_le_of_lt (mem_timestamp_le_latest hv) hnew, h⟩

/-- Announcements and node announcements leave the raw update list unchanged,
and an admitted update preserves the descending shape. -/
theorem updatesDescending_applyGossip {s : GossipState} {m : GossipMessage}
    (h : UpdatesDescending s.updates) (hclock : RawClockAdmits s m) :
    UpdatesDescending (applyGossip s m).updates := by
  cases m with
  | channelAnnouncement a => simpa [applyGossip] using h
  | channelUpdate u => exact updatesDescending_applyUpdate h hclock
  | nodeAnnouncement n => simpa [applyGossip] using h

/-- An admitted raw update becomes the newest stored record. -/
theorem latestUpdateTimestamp_applyUpdate_new {s : GossipState} {u : ChannelUpdate}
    (h : s.latestUpdateTimestamp < u.timestamp) :
    (s.applyUpdate u).latestUpdateTimestamp = u.timestamp := by
  have hupd : (s.applyUpdate u).updates = u :: s.updates :=
    GossipState.applyUpdate_new s u h
  show latestTimestamp (s.applyUpdate u).updates = u.timestamp
  rw [hupd, latestTimestamp_cons]
  exact foldl_max_eq_of_forall_le
    (fun v hv => Nat.le_of_lt (Nat.lt_of_le_of_lt (mem_timestamp_le_latest hv) h))

/-- **The canonical observation preserves the raw global clock on descending
stores.**  The head-most record of every directional slot is kept, and the raw
head is the newest record, so selection cannot lower the maximum timestamp. -/
theorem latestTimestamp_selectUpdates_eq_of_descending :
    ∀ {l : List ChannelUpdate}, UpdatesDescending l →
      latestTimestamp (selectUpdates l) = latestTimestamp l
  | [], _ => rfl
  | u :: l, h => by
      have hraw : latestTimestamp (u :: l) = u.timestamp :=
        latestTimestamp_eq_of_descending h
      have hmem : u ∈ selectUpdates (u :: l) := by
        rw [selectUpdates_cons]
        exact mem_insertUpdateCanonical_iff.mpr (Or.inl rfl)
      have hle : latestTimestamp (selectUpdates (u :: l)) ≤ u.timestamp := by
        apply latestTimestamp_le_of_forall_le
        intro v hv
        have hv' : v ∈ u :: l := mem_selectUpdates hv
        have := mem_timestamp_le_latest hv'
        rwa [hraw] at this
      have hge : u.timestamp ≤ latestTimestamp (selectUpdates (u :: l)) :=
        mem_timestamp_le_latest hmem
      rw [hraw]
      exact Nat.le_antisymm hle hge

/-- On a descending raw store, raw and canonical-observation clocks agree on
every message.  This is the clock-agreement premise isolated exactly. -/
theorem rawClockAdmits_canonicalStoreView_iff_of_descending {s : GossipState}
    (h : UpdatesDescending s.updates) (m : GossipMessage) :
    RawClockAdmits s m ↔ RawClockAdmits (canonicalStoreView s) m := by
  cases m with
  | channelAnnouncement a => exact Iff.rfl
  | channelUpdate u =>
      show latestTimestamp s.updates < u.timestamp ↔
        latestTimestamp (selectUpdates s.updates) < u.timestamp
      rw [latestTimestamp_selectUpdates_eq_of_descending h]
  | nodeAnnouncement n => exact Iff.rfl

/-- Full-state form of a successful raw update. -/
theorem applyGossip_update_new (s : GossipState) (u : ChannelUpdate)
    (h : s.latestUpdateTimestamp < u.timestamp) :
    applyGossip s (.channelUpdate u) = { s with updates := u :: s.updates } := by
  show (if s.latestUpdateTimestamp < u.timestamp then
      { s with updates := u :: s.updates } else s) =
    { s with updates := u :: s.updates }
  rw [ite_eq_left h]

/-- **Observation commutes with one raw step.**  Observing a raw step is the
same as observing it after first observing the store, provided the raw and
observed clocks agree.  This is the functorial form used for the sequence
induction; the announcement branch uses selector idempotence, the update
branch the clock agreement. -/
theorem canonicalStoreView_applyGossip_comp (s : GossipState) (m : GossipMessage)
    (hclock : RawClockAdmits s m ↔ RawClockAdmits (canonicalStoreView s) m) :
    canonicalStoreView (applyGossip s m) =
      canonicalStoreView (applyGossip (canonicalStoreView s) m) := by
  cases s with
  | mk ann upd node =>
    cases m with
    | channelAnnouncement a =>
        simp [canonicalStoreView, applyGossip, selectAnnouncements_cons,
          selectAnnouncements_idempotent, selectUpdates_idempotent]
    | nodeAnnouncement n =>
        simp [canonicalStoreView, applyGossip, selectAnnouncements_idempotent,
          selectUpdates_idempotent]
    | channelUpdate u =>
        by_cases h : (⟨ann, upd, node⟩ : GossipState).latestUpdateTimestamp <
            u.timestamp
        · have hobs : (canonicalStoreView ⟨ann, upd, node⟩).latestUpdateTimestamp <
              u.timestamp := hclock.mp h
          rw [applyGossip_update_new _ u h, applyGossip_update_new _ u hobs]
          simp [canonicalStoreView, selectUpdates_cons, selectUpdates_idempotent,
            selectAnnouncements_idempotent]
        · have hobs : ¬ (canonicalStoreView ⟨ann, upd, node⟩).latestUpdateTimestamp <
              u.timestamp := fun hc => h (hclock.mpr hc)
          rw [applyGossip_stale_update _ _ (Nat.le_of_not_lt h),
            applyGossip_stale_update _ _ (Nat.le_of_not_lt hobs)]
          simp [canonicalStoreView, selectUpdates_idempotent,
            selectAnnouncements_idempotent]

/-! ## 3. The epoch clock -/

/-- The epoch clock after one delivery: an update advances it to the update's
timestamp; every other message leaves it unchanged. -/
def advanceClock (clock : Timestamp) : GossipMessage → Timestamp
  | .channelUpdate u => u.timestamp
  | _ => clock

/-- Folding of the epoch clock over a delivered message list. -/
def clockRun (clock : Timestamp) (msgs : List GossipMessage) : Timestamp :=
  msgs.foldl advanceClock clock

@[simp] theorem clockRun_nil (clock : Timestamp) : clockRun clock [] = clock := rfl

@[simp] theorem clockRun_cons (clock : Timestamp) (m : GossipMessage)
    (ms : List GossipMessage) :
    clockRun clock (m :: ms) = clockRun (advanceClock clock m) ms := rfl

/-- **The realistic replacement/epoch premise.**  Every delivered update is
strictly newer than the current epoch clock; announcements and node
announcements leave the clock unchanged.  This is the exact ordering premise
under which a raw append-only run and a per-slot canonical run are
comparable. -/
def EpochStrictlyAdvances (clock : Timestamp) : List GossipMessage → Prop
  | [] => True
  | .channelUpdate u :: ms => clock < u.timestamp ∧
      EpochStrictlyAdvances u.timestamp ms
  | .channelAnnouncement _ :: ms => EpochStrictlyAdvances clock ms
  | .nodeAnnouncement _ :: ms => EpochStrictlyAdvances clock ms

/-- The epoch clock never goes backwards under the strict-advance premise. -/
theorem clockRun_monotone_of_epochStrict {clock : Timestamp}
    {msgs : List GossipMessage} (h : EpochStrictlyAdvances clock msgs) :
    clock ≤ clockRun clock msgs := by
  induction msgs generalizing clock with
  | nil => exact Nat.le_refl clock
  | cons m ms ih =>
      cases m with
      | channelUpdate u =>
          rw [clockRun_cons]
          exact Nat.le_trans (Nat.le_of_lt h.1) (ih h.2)
      | channelAnnouncement a =>
          simpa [advanceClock] using ih h
      | nodeAnnouncement n =>
          simpa [advanceClock] using ih h

/-- **The strict epoch premise derives the raw clock premise.**  If the raw
store's latest timestamp is at most the epoch clock, then every delivered
message is admitted by the raw global clock. -/
theorem rawClockHolds_of_epochStrict (s : GossipState) (msgs : List GossipMessage)
    (clock : Timestamp) (hle : s.latestUpdateTimestamp ≤ clock)
    (hstrict : EpochStrictlyAdvances clock msgs) :
    RawClockHolds s msgs := by
  induction msgs generalizing s clock with
  | nil => trivial
  | cons m ms ih =>
      cases m with
      | channelUpdate u =>
          have hlt : s.latestUpdateTimestamp < u.timestamp :=
            Nat.lt_of_le_of_lt hle hstrict.1
          refine ⟨hlt, ?_⟩
          apply ih (applyGossip s (.channelUpdate u)) u.timestamp
          · have hnew : (applyGossip s (.channelUpdate u)).latestUpdateTimestamp =
                u.timestamp := by
              simpa [applyGossip] using
                latestUpdateTimestamp_applyUpdate_new (s := s) (u := u) hlt
            rw [hnew]
            exact Nat.le_refl _
          · exact hstrict.2
      | channelAnnouncement a =>
          exact ⟨trivial, ih (applyGossip s (.channelAnnouncement a)) clock
            (by simpa [applyGossip, GossipState.latestUpdateTimestamp] using hle)
            hstrict⟩
      | nodeAnnouncement n =>
          exact ⟨trivial, ih (applyGossip s (.nodeAnnouncement n)) clock
            (by simpa [applyGossip, GossipState.latestUpdateTimestamp] using hle)
            hstrict⟩

/-- **The epoch clock dominates the raw clock.**  Along a strictly advancing
sequence the raw store's latest timestamp never exceeds the epoch clock. -/
theorem latestUpdateTimestamp_le_clockRun (s : GossipState)
    (msgs : List GossipMessage) (clock : Timestamp)
    (hle : s.latestUpdateTimestamp ≤ clock)
    (hstrict : EpochStrictlyAdvances clock msgs) :
    (runRaw s msgs).latestUpdateTimestamp ≤ clockRun clock msgs := by
  induction msgs generalizing s clock with
  | nil => exact hle
  | cons m ms ih =>
      cases m with
      | channelUpdate u =>
          have hlt : s.latestUpdateTimestamp < u.timestamp :=
            Nat.lt_of_le_of_lt hle hstrict.1
          have hnew : (applyGossip s (.channelUpdate u)).latestUpdateTimestamp =
              u.timestamp := by
            simpa [applyGossip] using
              latestUpdateTimestamp_applyUpdate_new (s := s) (u := u) hlt
          rw [runRaw_cons, clockRun_cons]
          exact ih (applyGossip s (.channelUpdate u)) u.timestamp
            (by rw [hnew]; exact Nat.le_refl _) hstrict.2
      | channelAnnouncement a =>
          rw [runRaw_cons, clockRun_cons]
          exact ih (applyGossip s (.channelAnnouncement a)) clock
            (by simpa [applyGossip, GossipState.latestUpdateTimestamp] using hle)
            hstrict
      | nodeAnnouncement n =>
          rw [runRaw_cons, clockRun_cons]
          exact ih (applyGossip s (.nodeAnnouncement n)) clock
            (by simpa [applyGossip, GossipState.latestUpdateTimestamp] using hle)
            hstrict

/-! ## 4. The exact sequence projection square -/

/-- **Sequence refinement, general raw starting state.**  If the raw store's
canonical observation is the canonical store, the raw update list is
descending, every canonical gate holds along the canonical run, and the raw
global clock admits every message along the raw run, then observing the whole
raw run is the canonical run. -/
theorem canonicalStoreView_runRaw_eq_runCanonical_aux
    (verify : SigVerifier) (cs : CanonicalStore) (raw : GossipState)
    (msgs : List GossipMessage)
    (hview : canonicalStoreView raw = cs.gossip)
    (hshape : CanonicalStoreShape cs.gossip)
    (hdesc : UpdatesDescending raw.updates)
    (hgates : CanonicalGatesHold verify cs msgs)
    (hclock : RawClockHolds raw msgs) :
    canonicalStoreView (runRaw raw msgs) = (runCanonical verify cs msgs).gossip := by
  induction msgs generalizing cs raw with
  | nil => exact hview
  | cons m ms ih =>
      have hgate : CanonicalMessageAdmitted verify cs m := hgates.1
      have hclockm : RawClockAdmits raw m := hclock.1
      have hagree : RawClockAdmits raw m ↔
          RawClockAdmits (canonicalStoreView raw) m :=
        rawClockAdmits_canonicalStoreView_iff_of_descending hdesc m
      have hclockcs : RawClockAdmits cs.gossip m := by
        rw [← hview]
        exact hagree.mp hclockm
      have hview' : canonicalStoreView (applyGossip raw m) =
          (applyGossipCanonicalStore verify cs m).gossip := by
        rw [canonicalStoreView_applyGossip_comp raw m hagree, hview]
        exact canonicalStoreView_applyGossip_eq_canonicalStore verify cs m
          hshape hgate hclockcs
      rw [runRaw_cons, runCanonical_cons]
      exact ih (applyGossipCanonicalStore verify cs m) (applyGossip raw m) hview'
        (canonicalStoreShape_applyGossipCanonicalStore verify cs m hshape hgate)
        (updatesDescending_applyGossip hdesc hclockm) hgates.2 hclock.2

/-- **The exact projection square over a replacement sequence, with the raw
clock premise stated directly.** -/
theorem canonicalStoreView_runRaw_eq_runCanonical_of_rawClock
    (verify : SigVerifier) (cs : CanonicalStore) (msgs : List GossipMessage)
    (hshape : CanonicalStoreShape cs.gossip)
    (hdesc : UpdatesDescending cs.gossip.updates)
    (hgates : CanonicalGatesHold verify cs msgs)
    (hclock : RawClockHolds cs.gossip msgs) :
    canonicalStoreView (runRaw cs.gossip msgs) = (runCanonical verify cs msgs).gossip :=
  canonicalStoreView_runRaw_eq_runCanonical_aux verify cs cs.gossip msgs
    ((canonicalStoreView_eq_self_iff cs.gossip).mpr hshape) hshape hdesc hgates hclock

/-- **The exact projection square over a realistic replacement/epoch
sequence.**  The epoch premise `EpochStrictlyAdvances` derives the raw clock
premise, so the only dynamic assumption is the strict epoch ordering plus the
canonical admission gates at every step. -/
theorem canonicalStoreView_runRaw_eq_runCanonical
    (verify : SigVerifier) (cs : CanonicalStore) (msgs : List GossipMessage)
    (hshape : CanonicalStoreShape cs.gossip)
    (hdesc : UpdatesDescending cs.gossip.updates)
    (hgates : CanonicalGatesHold verify cs msgs)
    (hstrict : EpochStrictlyAdvances cs.gossip.latestUpdateTimestamp msgs) :
    canonicalStoreView (runRaw cs.gossip msgs) = (runCanonical verify cs msgs).gossip :=
  canonicalStoreView_runRaw_eq_runCanonical_of_rawClock verify cs msgs hshape hdesc
    hgates
    (rawClockHolds_of_epochStrict cs.gossip msgs cs.gossip.latestUpdateTimestamp
      (Nat.le_refl _) hstrict)

/-! ## 5. The epoch store and epoch reachability -/

/-- A canonical store plus the delivery epoch state: the last epoch number and
the explicit epoch clock. -/
structure EpochStore where
  /-- The canonical store at this epoch. -/
  store : CanonicalStore
  /-- The epoch number of the last delivered event. -/
  epoch : Nat
  /-- The greatest delivered update timestamp so far. -/
  clock : Timestamp

/-- One epoch delivery: a message presented at an epoch number. -/
structure EpochEvent where
  /-- The delivery epoch number. -/
  epoch : Nat
  /-- The delivered gossip message. -/
  message : GossipMessage

/-- Apply one epoch delivery to the canonical store and clock. -/
noncomputable def applyGossipEpoch (verify : SigVerifier) (es : EpochStore)
    (e : EpochEvent) : EpochStore :=
  { store := applyGossipCanonicalStore verify es.store e.message
    epoch := e.epoch
    clock := advanceClock es.clock e.message }

/-- Fold epoch deliveries over an initial epoch store. -/
noncomputable def runEpoch (verify : SigVerifier) :
    EpochStore → List EpochEvent → EpochStore
  | es, [] => es
  | es, e :: evs => runEpoch verify (applyGossipEpoch verify es e) evs

@[simp] theorem runEpoch_nil (verify : SigVerifier) (es : EpochStore) :
    runEpoch verify es [] = es := rfl

@[simp] theorem runEpoch_cons (verify : SigVerifier) (es : EpochStore)
    (e : EpochEvent) (evs : List EpochEvent) :
    runEpoch verify es (e :: evs) =
      runEpoch verify (applyGossipEpoch verify es e) evs := rfl

/-- The empty epoch store with an arbitrary initial registration map. -/
def EpochInitial (nodeKeyOf : NodeId → PubKey) : EpochStore :=
  { store := { gossip := ⟨[], [], []⟩, nodeKeyOf := nodeKeyOf },
    epoch := 0, clock := 0 }

/-- Non-decreasing epoch numbers from a lower bound. -/
def EpochChainFrom (epoch : Nat) : List EpochEvent → Prop
  | [] => True
  | e :: evs => epoch ≤ e.epoch ∧ EpochChainFrom e.epoch evs

/-- A monotone epoch schedule. -/
def EpochMonotone (events : List EpochEvent) : Prop :=
  EpochChainFrom 0 events

/-- The final epoch is at least every earlier epoch. -/
theorem epochChainFrom_le_final (verify : SigVerifier) (es : EpochStore)
    (events : List EpochEvent) (h : EpochChainFrom es.epoch events) :
    es.epoch ≤ (runEpoch verify es events).epoch := by
  induction events generalizing es with
  | nil => exact Nat.le_refl es.epoch
  | cons e evs ih =>
      exact Nat.le_trans h.1 (ih (applyGossipEpoch verify es e) h.2)

/-- The epoch run's store is the canonical run over the event messages. -/
theorem runEpoch_store_eq_runCanonical (verify : SigVerifier) (es : EpochStore)
    (events : List EpochEvent) :
    (runEpoch verify es events).store =
      runCanonical verify es.store (events.map EpochEvent.message) := by
  induction events generalizing es with
  | nil => rfl
  | cons e evs ih =>
      show (runEpoch verify (applyGossipEpoch verify es e) evs).store = _
      rw [ih (applyGossipEpoch verify es e)]
      rfl

/-- The epoch run's clock is the folded epoch clock. -/
theorem runEpoch_clock_eq_clockRun (verify : SigVerifier) (es : EpochStore)
    (events : List EpochEvent) :
    (runEpoch verify es events).clock =
      clockRun es.clock (events.map EpochEvent.message) := by
  induction events generalizing es with
  | nil => rfl
  | cons e evs ih =>
      show (runEpoch verify (applyGossipEpoch verify es e) evs).clock = _
      rw [ih (applyGossipEpoch verify es e)]
      rfl

/-- The epoch run's store is reachable whenever the initial store is. -/
theorem runEpoch_store_reachable_of_reachable (verify : SigVerifier)
    {es : EpochStore} (h : ReachableCanonicalStore verify es.store)
    (events : List EpochEvent) :
    ReachableCanonicalStore verify (runEpoch verify es events).store := by
  induction events generalizing es with
  | nil => exact h
  | cons e evs ih =>
      show ReachableCanonicalStore verify
        (runEpoch verify (applyGossipEpoch verify es e) evs).store
      exact ih (ReachableCanonicalStore.step (m := e.message) h)

/-- Every epoch run from the empty store is canonically reachable. -/
theorem runEpoch_store_reachable (verify : SigVerifier) (k : NodeId → PubKey)
    (events : List EpochEvent) :
    ReachableCanonicalStore verify (runEpoch verify (EpochInitial k) events).store :=
  runEpoch_store_reachable_of_reachable verify
    (ReachableCanonicalStore.empty k) events

/-- An epoch store reachable from the empty store by epoch deliveries. -/
def EpochReachable (verify : SigVerifier) (es : EpochStore) : Prop :=
  ∃ (k : NodeId → PubKey) (events : List EpochEvent),
    runEpoch verify (EpochInitial k) events = es

theorem epochReachable_store_reachable {verify : SigVerifier} {es : EpochStore}
    (h : EpochReachable verify es) :
    ReachableCanonicalStore verify es.store := by
  rcases h with ⟨k, events, rfl⟩
  exact runEpoch_store_reachable verify k events

/-! ### All wave-7 canonical invariants transfer to epoch states -/

/-- Every epoch-reachable store satisfies the full wave-7 canonical store
invariant (validity, directional attribution, node keys, canonicality,
per-slot uniqueness). -/
theorem epochReachable_invariant {verify : SigVerifier} {es : EpochStore}
    (h : EpochReachable verify es) :
    CanonicalStoreAdmitted verify es.store :=
  reachableCanonicalStore_invariant (epochReachable_store_reachable h)

theorem epochReachable_store_valid {verify : SigVerifier} {es : EpochStore}
    (h : EpochReachable verify es) :
    StoreAnnouncementsValid verify es.store.gossip :=
  (epochReachable_invariant h).storeValid

theorem epochReachable_updates_directional {verify : SigVerifier}
    {es : EpochStore} (h : EpochReachable verify es) :
    StoreUpdatesDirectionallyAttributed verify es.store.gossip :=
  (epochReachable_invariant h).updatesAttributed

theorem epochReachable_nodeKeyConsistent {verify : SigVerifier}
    {es : EpochStore} (h : EpochReachable verify es) :
    GossipState.NodeKeyConsistent es.store.nodeKeyOf es.store.gossip :=
  (epochReachable_invariant h).nodeKeys

theorem epochReachable_canonical {verify : SigVerifier} {es : EpochStore}
    (h : EpochReachable verify es) :
    CanonicalAnnouncements es.store.gossip.announcements :=
  (epochReachable_invariant h).canonical

theorem epochReachable_updates_slotUnique {verify : SigVerifier}
    {es : EpochStore} (h : EpochReachable verify es) :
    UpdatesSlotUnique es.store.gossip.updates :=
  (epochReachable_invariant h).updatesSlotUnique

theorem epochReachable_shape {verify : SigVerifier} {es : EpochStore}
    (h : EpochReachable verify es) :
    CanonicalStoreShape es.store.gossip :=
  reachableCanonicalStore_shape (epochReachable_store_reachable h)

/-- No ambiguous direction-key attribution in an epoch-reachable store. -/
theorem epochReachable_attribution_unique {verify : SigVerifier}
    {es : EpochStore} (h : EpochReachable verify es)
    {u v : ChannelUpdate} (hu : u ∈ es.store.gossip.updates)
    (hv : v ∈ es.store.gossip.updates)
    (hscid : u.shortChannelId = v.shortChannelId)
    (hdir : u.direction = v.direction) :
    u.signingKey = v.signingKey :=
  canonical_directional_attribution_unique
    (epochReachable_canonical h) hscid hdir
    (epochReachable_updates_directional h u hu).2
    (epochReachable_updates_directional h v hv).2

/-- Every epoch run from the empty store satisfies the canonical invariant. -/
theorem runEpoch_invariant (verify : SigVerifier) (k : NodeId → PubKey)
    (events : List EpochEvent) :
    CanonicalStoreAdmitted verify (runEpoch verify (EpochInitial k) events).store :=
  reachableCanonicalStore_invariant (runEpoch_store_reachable verify k events)

/-! ## 6. Realistic replacement/epoch sequences -/

/-- A realistic gossip delivery schedule: monotone epoch numbers, strictly
advancing update timestamps, and canonical admission at every step. -/
def RealisticEpochSequence (verify : SigVerifier) (k : NodeId → PubKey)
    (events : List EpochEvent) : Prop :=
  EpochMonotone events ∧
    EpochStrictlyAdvances 0 (events.map EpochEvent.message) ∧
      CanonicalGatesHold verify (EpochInitial k).store
        (events.map EpochEvent.message)

/-- **The headline projection square.**  For every realistic replacement/epoch
sequence, the canonical epoch run projects exactly onto the canonical
observation of the raw append-only run. -/
theorem realisticEpochSequence_projection_square (verify : SigVerifier)
    (k : NodeId → PubKey) (events : List EpochEvent)
    (h : RealisticEpochSequence verify k events) :
    canonicalStoreView
        (runRaw (EpochInitial k).store.gossip
          (events.map EpochEvent.message)) =
      (runEpoch verify (EpochInitial k) events).store.gossip := by
  rcases h with ⟨_hmono, hstrict, hgates⟩
  rw [runEpoch_store_eq_runCanonical]
  exact canonicalStoreView_runRaw_eq_runCanonical verify (EpochInitial k).store
    (events.map EpochEvent.message)
    (by simp [EpochInitial, CanonicalStoreShape])
    (by simp [EpochInitial, UpdatesDescending])
    hgates
    (by simpa [EpochInitial, GossipState.latestUpdateTimestamp, latestTimestamp_nil] using hstrict)

/-- The epoch number never decreases along a realistic sequence. -/
theorem realisticEpochSequence_epoch_monotone (verify : SigVerifier)
    (k : NodeId → PubKey) (events : List EpochEvent)
    (h : RealisticEpochSequence verify k events) :
    (EpochInitial k).epoch ≤ (runEpoch verify (EpochInitial k) events).epoch :=
  epochChainFrom_le_final verify (EpochInitial k) events h.1

/-- The epoch clock never goes backwards along a realistic sequence. -/
theorem realisticEpochSequence_clock_monotone (verify : SigVerifier)
    (k : NodeId → PubKey) (events : List EpochEvent)
    (h : RealisticEpochSequence verify k events) :
    (EpochInitial k).clock ≤ (runEpoch verify (EpochInitial k) events).clock := by
  rw [runEpoch_clock_eq_clockRun]
  exact clockRun_monotone_of_epochStrict h.2.1

/-- The epoch clock dominates the raw store's global clock. -/
theorem realisticEpochSequence_clock_dominates_raw (verify : SigVerifier)
    (k : NodeId → PubKey) (events : List EpochEvent)
    (h : RealisticEpochSequence verify k events) :
    (runRaw (EpochInitial k).store.gossip
        (events.map EpochEvent.message)).latestUpdateTimestamp ≤
      (runEpoch verify (EpochInitial k) events).clock := by
  rw [runEpoch_clock_eq_clockRun]
  exact latestUpdateTimestamp_le_clockRun _ _ _
    (by simp [EpochInitial, GossipState.latestUpdateTimestamp,
      latestTimestamp_nil]) h.2.1

/-- Every realistic sequence ends in a store with the full canonical invariant. -/
theorem realisticEpochSequence_invariant (verify : SigVerifier)
    (k : NodeId → PubKey) (events : List EpochEvent)
    (_h : RealisticEpochSequence verify k events) :
    CanonicalStoreAdmitted verify (runEpoch verify (EpochInitial k) events).store :=
  runEpoch_invariant verify k events

/-! ## 7. The sharp obstruction: the clock premise is not removable -/

/-- **The wave-7 boundary witness refutes the gate-only square.**  There is a
canonically reachable (hence canonically shaped) store and a canonically
admitted update that the raw global clock rejects; observing the raw step is
therefore *not* the canonical step.  This is
`canonical_admission_strictly_weaker_than_raw_clock` restated as a failed
projection square. -/
theorem raw_clock_obstruction :
    ∃ (verify : SigVerifier) (cs : CanonicalStore) (m : GossipMessage),
      CanonicalStoreShape cs.gossip ∧
        CanonicalMessageAdmitted verify cs m ∧
          ¬ RawClockAdmits cs.gossip m ∧
            canonicalStoreView (applyGossip cs.gossip m) ≠
              (applyGossipCanonicalStore verify cs m).gossip := by
  rcases canonical_admission_strictly_weaker_than_raw_clock with
    ⟨verify, cs, u, hreach, hgate, hclock, hcanon, hraw, hnotmem⟩
  have hshape : CanonicalStoreShape cs.gossip :=
    reachableCanonicalStore_shape hreach
  have hleft : canonicalStoreView (applyGossip cs.gossip (.channelUpdate u)) =
      cs.gossip := by
    rw [hraw, (canonicalStoreView_eq_self_iff cs.gossip).mpr hshape]
  refine ⟨verify, cs, .channelUpdate u, hshape, hgate, hclock, ?_⟩
  intro heq
  rw [hleft] at heq
  have hmem : u ∈ (applyGossipCanonicalStore verify cs (.channelUpdate u)).gossip.updates := by
    rw [hcanon]
    exact List.mem_cons_self ..
  exact hnotmem (heq.symm ▸ hmem)

/-- **No gate-only sequence square.**  Canonical admission at every step is not
enough: the raw global clock premise (or the strict epoch premise that derives
it) is necessary for the sequence projection square. -/
theorem clock_premise_necessary :
    ¬ ∀ (verify : SigVerifier) (cs : CanonicalStore) (msgs : List GossipMessage),
        CanonicalStoreShape cs.gossip →
          CanonicalGatesHold verify cs msgs →
            canonicalStoreView (runRaw cs.gossip msgs) =
              (runCanonical verify cs msgs).gossip := by
  intro hsquare
  rcases canonical_admission_strictly_weaker_than_raw_clock with
    ⟨verify, cs, u, hreach, hgate, hclock, hcanon, hraw, hnotmem⟩
  have hshape : CanonicalStoreShape cs.gossip :=
    reachableCanonicalStore_shape hreach
  have hsq := hsquare verify cs [.channelUpdate u] hshape ⟨hgate, trivial⟩
  have hleft : canonicalStoreView (runRaw cs.gossip [.channelUpdate u]) =
      cs.gossip := by
    show canonicalStoreView (applyGossip cs.gossip (.channelUpdate u)) = cs.gossip
    rw [hraw, (canonicalStoreView_eq_self_iff cs.gossip).mpr hshape]
  rw [hleft] at hsq
  have hmem : u ∈ (runCanonical verify cs [.channelUpdate u]).gossip.updates := by
    show u ∈ (applyGossipCanonicalStore verify cs (.channelUpdate u)).gossip.updates
    rw [hcanon]
    exact List.mem_cons_self ..
  exact hnotmem (hsq.symm ▸ hmem)

/-- The same obstruction stated for an epoch schedule: with only the canonical
gates, the projection square over a one-event schedule fails, so the strict
epoch clock premise (equivalently the raw clock premise) is exactly the missing
epoch/clock condition. -/
theorem epochClock_premise_necessary :
    ∃ (verify : SigVerifier) (es : EpochStore) (events : List EpochEvent),
      CanonicalStoreShape es.store.gossip ∧
        CanonicalGatesHold verify es.store (events.map EpochEvent.message) ∧
          ¬ EpochStrictlyAdvances es.clock (events.map EpochEvent.message) ∧
            canonicalStoreView
                (runRaw es.store.gossip (events.map EpochEvent.message)) ≠
              (runEpoch verify es events).store.gossip := by
  rcases canonical_admission_strictly_weaker_than_raw_clock with
    ⟨verify, cs, u, hreach, hgate, hclock, hcanon, hraw, hnotmem⟩
  have hshape : CanonicalStoreShape cs.gossip :=
    reachableCanonicalStore_shape hreach
  let es : EpochStore :=
    { store := cs, epoch := 0, clock := cs.gossip.latestUpdateTimestamp }
  let events : List EpochEvent := [⟨0, .channelUpdate u⟩]
  refine ⟨verify, es, events, ?_, ⟨hgate, trivial⟩, ?_, ?_⟩
  · exact hshape
  · intro hstrict
    exact hclock hstrict.1
  · intro heq
    have hleft : canonicalStoreView
        (runRaw es.store.gossip (events.map EpochEvent.message)) = cs.gossip := by
      show canonicalStoreView (applyGossip cs.gossip (.channelUpdate u)) = cs.gossip
      rw [hraw, (canonicalStoreView_eq_self_iff cs.gossip).mpr hshape]
    rw [hleft] at heq
    have hmem : u ∈ (runEpoch verify es events).store.gossip.updates := by
      show u ∈ (applyGossipCanonicalStore verify cs (.channelUpdate u)).gossip.updates
      rw [hcanon]
      exact List.mem_cons_self ..
    exact hnotmem (heq.symm ▸ hmem)

/-! ## 8. Preserved negative results -/

/-- Raw `applyGossip` still accepts a conflicting announcement.  The wave-4/5
counterexample is re-exported unchanged: the epoch refinement does not alter
raw insertion. -/
theorem raw_conflicting_announcement_counterexample_preserved :
    ∃ (s : GossipState) (a : ChannelAnnellation),
      ¬ CanonicalAnnouncements
        (applyGossip s (.channelAnnouncement a)).announcements :=
  raw_applyGossip_accepts_conflicting_announcement

/-- Without a canonical selector, conflicting announcements remain ambiguous:
the wave-5 counterexample, unchanged. -/
theorem ambiguous_without_canonical_preserved :
    ∃ (s : GossipState) (u v : ChannelUpdate),
      ¬ CanonicalAnnouncements s.announcements ∧
        u.shortChannelId = v.shortChannelId ∧ u.direction = v.direction ∧
          s.updateKeyAnnouncedDirectional u ∧
            s.updateKeyAnnouncedDirectional v ∧ u.signingKey ≠ v.signingKey :=
  conflicting_announcements_ambiguous_without_canonical

/-! ## 9. A concrete realistic epoch/replacement witness -/

private def acceptAll : SigVerifier := fun _ _ _ => true

/-- Byte length 1. -/
private def key1 : PubKey := ⟨ByteArray.mk #[1]⟩

/-- Byte length 0. -/
private def key2 : PubKey := ⟨ByteArray.empty⟩

private def nodeA : NodeId := ⟨0⟩

private def nodeB : NodeId := ⟨1⟩

private def sampleScid : ShortChannelId := ⟨1, 2, 3⟩

private def emptySig : GossipSignature := ⟨ByteArray.empty⟩

private def mkAnn (capacity : Nat) (k1 k2 : PubKey) : ChannelAnnellation :=
  { shortChannelId := sampleScid
    node1 := nodeA
    node2 := nodeB
    nodeKey1 := k1
    nodeKey2 := k2
    bitcoinKey1 := k1
    bitcoinKey2 := k2
    capacitySat := capacity
    digest := ByteArray.empty
    nodeSignature1 := emptySig
    nodeSignature2 := emptySig
    bitcoinSignature1 := emptySig
    bitcoinSignature2 := emptySig }

/-- The reference announcement: `nodeA ↦ key1`, `nodeB ↦ key2`. -/
private def ann : ChannelAnnellation := mkAnn 1000 key1 key2

private def mkUpd (timestamp : Nat) (k : PubKey) : ChannelUpdate :=
  { shortChannelId := sampleScid
    timestamp := timestamp
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

/-- Direction-0 update, timestamp 1. -/
private def u0 : ChannelUpdate := mkUpd 1 key1

/-- Direction-0 update, timestamp 2; supersedes `u0`. -/
private def u1 : ChannelUpdate := mkUpd 2 key1

private theorem ann_valid : ann.signaturesValid acceptAll := by
  simp [ChannelAnnellation.signaturesValid, signatureValid, acceptAll]

private theorem u0_valid : u0.signatureValid acceptAll := by
  simp [ChannelUpdate.signatureValid, signatureValid, acceptAll]

private theorem u1_valid : u1.signatureValid acceptAll := by
  simp [ChannelUpdate.signatureValid, signatureValid, acceptAll]

private theorem nodeA_ne_nodeB : nodeA ≠ nodeB := by
  intro h
  exact Nat.noConfusion (congrArg NodeId.index h)

private def epochStart : EpochStore := EpochInitial (fun _ => key2)

private theorem start_compatible (a : ChannelAnnellation) :
    epochStart.store.gossip.CompatibleWithStore a := by
  intro b hb
  simp [epochStart, EpochInitial] at hb

private theorem start_authorizes (a : ChannelAnnellation) :
    UpdatesAuthorizedBy epochStart.store.gossip a := by
  intro u hu
  simp [epochStart, EpochInitial] at hu

private theorem ann_gate :
    CanonicalMessageAdmitted acceptAll epochStart.store (.channelAnnouncement ann) :=
  ⟨ann_valid, by simpa [ann, mkAnn] using nodeA_ne_nodeB,
    start_compatible ann, start_authorizes ann⟩

private noncomputable def storeAnn : CanonicalStore :=
  applyGossipCanonicalStore acceptAll epochStart.store (.channelAnnouncement ann)

private theorem storeAnn_announcements : storeAnn.gossip.announcements = [ann] := by
  rw [storeAnn, applyGossipCanonicalStore_announcement_of_admitted acceptAll
    epochStart.store ann ann_gate]
  simp [epochStart, EpochInitial, insertReplacing]

private theorem storeAnn_updates : storeAnn.gossip.updates = [] := by
  rw [storeAnn, applyGossipCanonicalStore_announcement_of_admitted acceptAll
    epochStart.store ann ann_gate]
  simp [epochStart, EpochInitial]

/-- Direction-keyed attribution depends only on the stored announcement list. -/
private theorem attributed_of_announcements (s : GossipState)
    (hann : s.announcements = [ann]) (u : ChannelUpdate)
    (hu : u.shortChannelId = sampleScid) (hflags : u.channelFlags = 0)
    (hkey : u.signingKey = key1) :
    s.updateKeyAnnouncedDirectional u := by
  refine GossipState.updateKeyAnnouncedDirectional_of_mem (a := ann) ?_ ?_ ?_
  · rw [hann]
    exact List.mem_singleton_self ann
  · simp [ann, mkAnn, hu]
  · rw [ChannelUpdate.direction_of_channelFlags_zero hflags]
    simp [ChannelAnnellation.attributesKeyForDirection, ann, mkAnn, hkey]

private theorem storeAnn_attributed (u : ChannelUpdate)
    (hu : u.shortChannelId = sampleScid) (hflags : u.channelFlags = 0)
    (hkey : u.signingKey = key1) :
    storeAnn.gossip.updateKeyAnnouncedDirectional u :=
  attributed_of_announcements storeAnn.gossip storeAnn_announcements u hu hflags hkey

private theorem storeAnn_supersedes_u0 : UpdateSupersedes u0 storeAnn.gossip.updates := by
  intro v hv
  rw [storeAnn_updates] at hv
  simp at hv

private theorem u0_gate :
    CanonicalMessageAdmitted acceptAll storeAnn (.channelUpdate u0) :=
  ⟨u0_valid, storeAnn_attributed u0 rfl rfl rfl, storeAnn_supersedes_u0⟩

private noncomputable def storeU0 : CanonicalStore :=
  applyGossipCanonicalStore acceptAll storeAnn (.channelUpdate u0)

private theorem storeU0_updates : storeU0.gossip.updates = [u0] := by
  rw [storeU0, applyGossipCanonicalStore_update_of_admitted acceptAll storeAnn u0 u0_gate]
  simp [storeAnn_updates, insertUpdateCanonical]

private theorem storeU0_announcements : storeU0.gossip.announcements = [ann] := by
  rw [storeU0, applyGossipCanonicalStore_update_of_admitted acceptAll storeAnn u0 u0_gate]
  simp [storeAnn_announcements]

private theorem storeU0_supersedes_u1 : UpdateSupersedes u1 storeU0.gossip.updates := by
  intro v hv _hscid _hdir
  rw [storeU0_updates] at hv
  simp only [List.mem_singleton] at hv
  subst v
  simp [u0, u1, mkUpd]

private theorem u1_gate :
    CanonicalMessageAdmitted acceptAll storeU0 (.channelUpdate u1) :=
  ⟨u1_valid, attributed_of_announcements storeU0.gossip storeU0_announcements
      u1 rfl rfl rfl, storeU0_supersedes_u1⟩

private noncomputable def storeU1 : CanonicalStore :=
  applyGossipCanonicalStore acceptAll storeU0 (.channelUpdate u1)

private theorem storeU1_updates : storeU1.gossip.updates = [u1] := by
  rw [storeU1, applyGossipCanonicalStore_update_of_admitted acceptAll storeU0 u1 u1_gate]
  simp [storeU0_updates, insertUpdateCanonical, u0, u1, mkUpd,
    ChannelUpdate.direction]

private theorem u0_ne_u1 : u0 ≠ u1 := by
  intro h
  have ht := congrArg ChannelUpdate.timestamp h
  simp [u0, u1, mkUpd] at ht

/-- Announcement, then the timestamp-1 update, then the timestamp-2 update. -/
private def epochEvents : List EpochEvent :=
  [⟨0, .channelAnnouncement ann⟩, ⟨1, .channelUpdate u0⟩,
    ⟨2, .channelUpdate u1⟩]

private theorem runEpoch_epochEvents_store :
    (runEpoch acceptAll (EpochInitial (fun _ => key2)) epochEvents).store = storeU1 := by
  simp [epochEvents, runEpoch, applyGossipEpoch, epochStart, storeAnn, storeU0, storeU1]

private theorem epochEvents_realistic :
    RealisticEpochSequence acceptAll (fun _ => key2) epochEvents := by
  refine ⟨?_, ?_, ?_⟩
  · simp [EpochMonotone, EpochChainFrom, epochEvents]
  · simp [EpochStrictlyAdvances, epochEvents, u0, u1, mkUpd]
  · simp only [CanonicalGatesHold, epochEvents, List.map_cons, List.map_nil]
    exact ⟨ann_gate, u0_gate, u1_gate, trivial⟩

/-- The realistic schedule has a concrete, non-vacuous instance: a channel
announcement followed by two strictly newer updates in the same directional
slot.  The canonical epoch run keeps only the newest update, while the raw
append-only run retains both; the projection square witnesses the intended
replacement behaviour. -/
theorem realisticEpochSequence_witness :
    ∃ (verify : SigVerifier) (k : NodeId → PubKey) (events : List EpochEvent),
      RealisticEpochSequence verify k events ∧ events ≠ [] ∧
        (runEpoch verify (EpochInitial k) events).store.gossip.updates = [u1] ∧
          u0 ∉ (runEpoch verify (EpochInitial k) events).store.gossip.updates := by
  refine ⟨acceptAll, (fun _ => key2), epochEvents, epochEvents_realistic, ?_, ?_, ?_⟩
  · simp [epochEvents]
  · rw [runEpoch_epochEvents_store, storeU1_updates]
  · rw [runEpoch_epochEvents_store, storeU1_updates]
    simp [u0_ne_u1]

private theorem runRaw_epochEvents_updates :
    (runRaw (EpochInitial (fun _ => key2)).store.gossip
      (epochEvents.map EpochEvent.message)).updates = [u1, u0] := by
  simp [epochEvents, runRaw, applyGossip, EpochInitial, u0, u1, mkUpd,
    GossipState.applyUpdate, GossipState.latestUpdateTimestamp, latestTimestamp]

end LnLean.Proofs.WaveH.H40
