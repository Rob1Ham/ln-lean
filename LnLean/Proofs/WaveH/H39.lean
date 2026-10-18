import LnLean.Proofs.Routing.GossipRawRefinementTargets

/-!
# H39 — gossip-store epochs and replacement semantics (`RT-01`, `RT-02`)

Wave-8 lane `H39`.  Open issues `RT-01` (gossip key attribution / canonical
wrapper) and `RT-02` (canonical-store invariants).

## What this module adds

Waves 6 and 7 gave the canonical gossip store

* `CanonicalStore` — the wave-A `GossipState` plus the explicit
  `NodeId → PubKey` registration map
  (`LnLean.Proofs.Routing.GossipRawRefinementTargets`);
* `applyGossipCanonicalStore` — the canonicalising admission transition
  (signature-gated, registration-gated, per-slot replacement);
* `ReachableCanonicalStore` and `CanonicalStoreAdmitted` — the reachable
  invariants (valid announcements, direction-attributed updates,
  `NodeKeyConsistent`, one announcement per channel, one update per
  directional slot).

Neither module models a store *epoch*: the store is a state, not a history, and
replacement is only observable by comparing states before and after a step.
This module adds that layer **additively**, over the unchanged canonical store:

* `StoreEpoch := Nat` is the model-side epoch of a store.
* `EpochStore` is `CanonicalStore` plus the current epoch and two *epoch logs*:
  `annStamps` for `channel_announcement` slots (keyed by
  `short_channel_id`) and `updStamps` for `channel_update` slots (keyed by
  `UpdateSlot = (short_channel_id, direction)`).
* `lookupStamp` reads the head-most (newest) log entry for a key, so the *stamp*
  of a slot is the epoch at which that slot was last written.
* `epochStep` is the epoch-carrying store step: it is
  `applyGossipCanonicalStore` on the store component, it increments the epoch
  exactly on a message the canonical gates admit, and it writes the new epoch
  into the log entry of the replaced slot.

## Exact epoch semantics (normative)

For a store `e`, a message `m` and a verifier `verify`:

1. **Store projection.**
   `(epochStep verify e m).store = applyGossipCanonicalStore verify e.store m`.
   The epoch layer therefore adds *no* admission power and removes none:
   accepted and rejected messages are exactly the canonical ones.
2. **Epoch.** `(epochStep verify e m).epoch` is `e.epoch + 1` when
   `CanonicalMessageAdmitted verify e.store m` holds and `e.epoch` otherwise.
   The epoch is thus the number of *admissions* since the initial store, not a
   content hash.  It is possible for an admitted message to leave the store
   content unchanged (re-announcing the identical head record is the witness
   `epoch_admission_gossip_noop_witness`); the epoch still advances, because
   the step was admitted.  This is stated, not hidden.
3. **Replacement stamps.** An admitted `channel_announcement` for
   `a.shortChannelId` prepends `(a.shortChannelId, e.epoch + 1)` to `annStamps`;
   an admitted `channel_update` for `u` prepends
   `((u.shortChannelId, u.direction), e.epoch + 1)` to `updStamps`; every other
   accepted step leaves both logs untouched (a node announcement writes no
   channel slot).  Consequently the stamp of a replaced slot is strictly larger
   than the previous stamp of that slot (`annStamp_strict_of_epochStep_announcement`,
   `updStamp_strict_of_epochStep_update`), and no slot stamp ever decreases
   (`annStamp_mono`, `updStamp_mono`).
4. **Store sequence.** `StoreSequence := List GossipMessage`;
   `runEpochSteps` folds `epochStep` over a sequence and
   `runCanonicalStoreSteps` folds `applyGossipCanonicalStore` over it.  The
   projection `runEpochSteps_store` says the epoch run erases to the canonical
   run.  `AdmittedAlong` is the predicate "every message is admitted at the
   point it is applied"; on such a sequence the final epoch is exactly
   `e.epoch + ms.length` (`runEpochSteps_epoch_eq_of_admitted`), and in general
   the epoch is monotone and grows by at most one per message.

## Relation to BOLT 7 replacement

The epoch layer does not replace the BOLT 7 rules; it records them.  For an
admitted update, the canonical per-slot gate `UpdateSupersedes` is exactly the
BOLT 7 timestamp rule, so every stored update in the replaced slot has a
strictly older `timestamp` (`epochStep_update_requires_newer_timestamp`).  For
an admitted announcement, replacement drops the previous record for the same
`short_channel_id` (`epochStep_announcement_old_record_gone`), which is the
canonical replacement `insertReplacing`, not raw append.

## Preserved negative results

The raw store is untouched.  `raw_applyGossip` remains append-only and is still
*not* a function refinement of canonical admission: this module re-exports
`no_canonical_preserving_raw_announcement_extension`
(`raw_nonrefinement_preserved`) and the per-slot/global-clock boundary witness
`canonical_admission_strictly_weaker_than_raw_clock`
(`raw_clock_boundary_preserved`) unchanged.  No theorem below identifies the raw
and canonical transitions.

## What is **not** modelled

* The epoch is a model-side bookkeeping value, not a BOLT 7 wire field.  BOLT 7
  has no store epoch; the real replacement clock is the per-direction
  `timestamp` (plus local wall-clock policy outside the spec).  An epoch must
  therefore never be read as an on-chain or wire fact.
* The epoch logs are histories, so they grow with the number of admitted
  channel messages.  No compaction, persistence, crash recovery, or
  authenticated-log claim is made.
* `SigVerifier` remains abstract (assumptions C3/C4/C8); no unforgeability is
  claimed.
* No network, liveness, chain-hash, UTXO, or rate-limit claim.

No `sorry`, no `axiom`, no `admit`, no `native_decide`, no `unsafe`, no
`@[implemented_by]`.
-/

namespace LnLean.Proofs.WaveH.H39

open LnLean.Routing
open LnLean.Proofs.Routing.GossipCanonicalTargets
open LnLean.Proofs.Routing.GossipRawRefinementTargets
open LnLean.Proofs.Routing.GossipTargets
open LnLean.Proofs.Routing.GossipKeyConsistencyTargets
open Classical

set_option autoImplicit false

/-! ## 1. Epochs, slots and stamp logs -/

/-- Model-side store epoch.  A `Nat` that counts admitted store steps; see the
module docstring for the exact semantics and for why it is not a wire field. -/
abbrev StoreEpoch := Nat

/-- A directional `channel_update` slot: BOLT 7 keys updates by
`(short_channel_id, direction)`, where `direction` is the decoded
`channel_flags` bit 0. -/
structure UpdateSlot where
  /-- The channel. -/
  scid : ShortChannelId
  /-- The decoded BOLT 7 direction bit. -/
  direction : Bool
deriving Repr, BEq, DecidableEq

/-- Head-most stamp for `k` in an epoch log.  Logs are newest-first, so the
head-most entry for a key is the epoch at which that slot was last written. -/
def lookupStamp {α : Type} [DecidableEq α] (k : α) :
    List (α × StoreEpoch) → Option StoreEpoch
  | [] => none
  | (k', t) :: rest => if k' = k then some t else lookupStamp k rest

@[simp] theorem lookupStamp_nil {α : Type} [DecidableEq α] (k : α) :
    lookupStamp k ([] : List (α × StoreEpoch)) = none := rfl

/-- The head entry is the current stamp. -/
theorem lookupStamp_cons_self {α : Type} [DecidableEq α] (k : α)
    (t : StoreEpoch) (rest : List (α × StoreEpoch)) :
    lookupStamp k ((k, t) :: rest) = some t := by
  simp [lookupStamp]

/-- A head entry for another key does not shadow the requested key. -/
theorem lookupStamp_cons_of_ne {α : Type} [DecidableEq α] {k k' : α}
    (h : k' ≠ k) (t : StoreEpoch) (rest : List (α × StoreEpoch)) :
    lookupStamp k ((k', t) :: rest) = lookupStamp k rest := by
  simp [lookupStamp, h]

/-- Every stamp found in a log is bounded by any bound that bounds the whole
log. -/
theorem lookupStamp_le_of_forall {α : Type} [DecidableEq α] {k : α}
    {l : List (α × StoreEpoch)} {t : StoreEpoch} {B : StoreEpoch}
    (h : lookupStamp k l = some t) (hb : ∀ p ∈ l, p.2 ≤ B) : t ≤ B := by
  induction l with
  | nil => simp at h
  | cons p rest ih =>
      obtain ⟨k', t'⟩ := p
      by_cases hk : k' = k
      · subst k'
        rw [lookupStamp_cons_self] at h
        have ht : t' = t := by simpa using h
        subst t
        exact hb (k, t') (List.mem_cons_self ..)
      · rw [lookupStamp_cons_of_ne hk] at h
        exact ih h (fun q hq => hb q (List.mem_cons_of_mem _ hq))

/-! ## 2. The epoch store -/

/-- The canonical store plus its model-side epoch and the two write-stamp logs.
The `store` field is exactly the wave-7 `CanonicalStore`; nothing in the epoch
layer changes it. -/
structure EpochStore where
  /-- The canonical gossip store and registration map. -/
  store : CanonicalStore
  /-- The current store epoch (number of admissions since the initial store). -/
  epoch : StoreEpoch
  /-- Write-stamp log for `channel_announcement` slots, newest first. -/
  annStamps : List (ShortChannelId × StoreEpoch)
  /-- Write-stamp log for `channel_update` slots, newest first. -/
  updStamps : List (UpdateSlot × StoreEpoch)

namespace EpochStore

/-- The epoch at which the announcement slot `scid` was last written, if any. -/
def annStamp (e : EpochStore) (scid : ShortChannelId) : Option StoreEpoch :=
  lookupStamp scid e.annStamps

/-- The epoch at which the update slot `s` was last written, if any. -/
def updStamp (e : EpochStore) (s : UpdateSlot) : Option StoreEpoch :=
  lookupStamp s e.updStamps

end EpochStore

/-- Both stamp logs are bounded by the store's own epoch.  This is the basic
epoch invariant: no slot can claim to have been written in the future. -/
def StampBounded (e : EpochStore) : Prop :=
  (∀ p ∈ e.annStamps, p.2 ≤ e.epoch) ∧ (∀ p ∈ e.updStamps, p.2 ≤ e.epoch)

/-- An announcement slot stamp is bounded by the store epoch. -/
theorem annStamp_le_epoch {e : EpochStore} (hb : StampBounded e)
    {scid : ShortChannelId} {t : StoreEpoch} (h : e.annStamp scid = some t) :
    t ≤ e.epoch :=
  lookupStamp_le_of_forall h hb.1

/-- An update slot stamp is bounded by the store epoch. -/
theorem updStamp_le_epoch {e : EpochStore} (hb : StampBounded e)
    {s : UpdateSlot} {t : StoreEpoch} (h : e.updStamp s = some t) :
    t ≤ e.epoch :=
  lookupStamp_le_of_forall h hb.2

/-! ## 3. The epoch-carrying store step -/

/-- **The epoch-carrying canonical store step.**

* the store component is exactly `applyGossipCanonicalStore`;
* an admitted message increments the epoch and stamps the slot it writes;
* a rejected message is a no-op on the whole `EpochStore`, epoch and logs
  included.

The definition is `noncomputable` only because the canonical admission gates
compare keys (`Classical.propDecidable`); it is a deterministic function of the
message and the state. -/
noncomputable def epochStep (verify : SigVerifier) (e : EpochStore) :
    GossipMessage → EpochStore
  | .channelAnnouncement a =>
      if CanonicalMessageAdmitted verify e.store (.channelAnnouncement a) then
        { store := applyGossipCanonicalStore verify e.store (.channelAnnouncement a)
          epoch := e.epoch + 1
          annStamps := (a.shortChannelId, e.epoch + 1) :: e.annStamps
          updStamps := e.updStamps }
      else e
  | .channelUpdate u =>
      if CanonicalMessageAdmitted verify e.store (.channelUpdate u) then
        { store := applyGossipCanonicalStore verify e.store (.channelUpdate u)
          epoch := e.epoch + 1
          annStamps := e.annStamps
          updStamps := (⟨u.shortChannelId, u.direction⟩, e.epoch + 1) :: e.updStamps }
      else e
  | .nodeAnnouncement n =>
      if CanonicalMessageAdmitted verify e.store (.nodeAnnouncement n) then
        { store := applyGossipCanonicalStore verify e.store (.nodeAnnouncement n)
          epoch := e.epoch + 1
          annStamps := e.annStamps
          updStamps := e.updStamps }
      else e

/-- **Semantics, part 1: the store projection.**  The epoch layer is exactly the
canonical store layer, message by message. -/
theorem epochStep_store (verify : SigVerifier) (e : EpochStore)
    (m : GossipMessage) :
    (epochStep verify e m).store = applyGossipCanonicalStore verify e.store m := by
  cases m with
  | channelAnnouncement a =>
      by_cases h : CanonicalMessageAdmitted verify e.store (.channelAnnouncement a)
      · have hh : a.signaturesValid verify ∧ a.node1 ≠ a.node2 ∧
            e.store.gossip.CompatibleWithStore a ∧
              UpdatesAuthorizedBy e.store.gossip a := h
        simp only [epochStep, applyGossipCanonicalStore]
        rw [if_pos h, if_pos hh]
      · have hh : ¬ (a.signaturesValid verify ∧ a.node1 ≠ a.node2 ∧
            e.store.gossip.CompatibleWithStore a ∧
              UpdatesAuthorizedBy e.store.gossip a) := h
        simp only [epochStep, applyGossipCanonicalStore]
        rw [if_neg h, if_neg hh]
  | channelUpdate u =>
      by_cases h : CanonicalMessageAdmitted verify e.store (.channelUpdate u)
      · have hh : u.signatureValid verify ∧
            e.store.gossip.updateKeyAnnouncedDirectional u ∧
              UpdateSupersedes u e.store.gossip.updates := h
        simp only [epochStep, applyGossipCanonicalStore]
        rw [if_pos h, if_pos hh]
      · have hh : ¬ (u.signatureValid verify ∧
            e.store.gossip.updateKeyAnnouncedDirectional u ∧
              UpdateSupersedes u e.store.gossip.updates) := h
        simp only [epochStep, applyGossipCanonicalStore]
        rw [if_neg h, if_neg hh]
  | nodeAnnouncement n =>
      by_cases h : CanonicalMessageAdmitted verify e.store (.nodeAnnouncement n)
      · have hh : n.signatureValid verify := h
        simp only [epochStep, applyGossipCanonicalStore]
        rw [if_pos h, if_pos hh]
      · have hh : ¬ n.signatureValid verify := h
        simp only [epochStep, applyGossipCanonicalStore]
        rw [if_neg h, if_neg hh]

/-- A rejected message is a no-op on the whole epoch store. -/
theorem epochStep_eq_self_of_rejected (verify : SigVerifier) (e : EpochStore)
    (m : GossipMessage) (h : ¬ CanonicalMessageAdmitted verify e.store m) :
    epochStep verify e m = e := by
  cases m with
  | channelAnnouncement a => simp [epochStep, h]
  | channelUpdate u => simp [epochStep, h]
  | nodeAnnouncement n => simp [epochStep, h]

/-- An admitted message increments the epoch. -/
theorem epochStep_epoch_succ_of_admitted (verify : SigVerifier) (e : EpochStore)
    (m : GossipMessage) (h : CanonicalMessageAdmitted verify e.store m) :
    (epochStep verify e m).epoch = e.epoch + 1 := by
  cases m with
  | channelAnnouncement a => simp [epochStep, h]
  | channelUpdate u => simp [epochStep, h]
  | nodeAnnouncement n => simp [epochStep, h]

/-- A rejected message leaves the epoch unchanged. -/
theorem epochStep_epoch_of_rejected (verify : SigVerifier) (e : EpochStore)
    (m : GossipMessage) (h : ¬ CanonicalMessageAdmitted verify e.store m) :
    (epochStep verify e m).epoch = e.epoch := by
  rw [epochStep_eq_self_of_rejected verify e m h]

/-- The epoch after a step is the old epoch or its successor: the epoch grows by
at most one per message. -/
theorem epochStep_epoch_eq_or_succ (verify : SigVerifier) (e : EpochStore)
    (m : GossipMessage) :
    (epochStep verify e m).epoch = e.epoch ∨
      (epochStep verify e m).epoch = e.epoch + 1 := by
  by_cases h : CanonicalMessageAdmitted verify e.store m
  · exact Or.inr (epochStep_epoch_succ_of_admitted verify e m h)
  · exact Or.inl (epochStep_epoch_of_rejected verify e m h)

/-- The epoch never decreases. -/
theorem epochStep_epoch_ge (verify : SigVerifier) (e : EpochStore)
    (m : GossipMessage) : e.epoch ≤ (epochStep verify e m).epoch := by
  rcases epochStep_epoch_eq_or_succ verify e m with h | h
  · rw [h]; exact Nat.le_refl e.epoch
  · rw [h]; exact Nat.le_succ e.epoch

/-- The epoch grows by at most one per step. -/
theorem epochStep_epoch_le_succ (verify : SigVerifier) (e : EpochStore)
    (m : GossipMessage) : (epochStep verify e m).epoch ≤ e.epoch + 1 := by
  rcases epochStep_epoch_eq_or_succ verify e m with h | h
  · rw [h]; exact Nat.le_succ e.epoch
  · rw [h]; exact Nat.le_refl (e.epoch + 1)

/-- **Semantics, part 2.**  A step that changes the store content must have
passed the canonical admission gates.  (The converse fails only in the benign
re-announcement case recorded by `epoch_admission_gossip_noop_witness`.) -/
theorem epochStep_store_change_requires_admitted (verify : SigVerifier)
    (e : EpochStore) (m : GossipMessage)
    (h : (epochStep verify e m).store ≠ e.store) :
    CanonicalMessageAdmitted verify e.store m := by
  apply Classical.byContradiction
  intro hc
  exact h (by rw [epochStep_eq_self_of_rejected verify e m hc])

/-- **The exact epoch step semantics**, packaged.  The store is the canonical
step; admission increments the epoch; rejection is the identity. -/
theorem epochStep_semantics (verify : SigVerifier) (e : EpochStore)
    (m : GossipMessage) :
    (epochStep verify e m).store = applyGossipCanonicalStore verify e.store m ∧
      ((CanonicalMessageAdmitted verify e.store m →
          (epochStep verify e m).epoch = e.epoch + 1) ∧
        (¬ CanonicalMessageAdmitted verify e.store m → epochStep verify e m = e)) :=
  ⟨epochStep_store verify e m,
    epochStep_epoch_succ_of_admitted verify e m,
    epochStep_eq_self_of_rejected verify e m⟩

/-! ### 3.1 Branch equations -/

/-- Equation for an admitted announcement step. -/
theorem epochStep_announcement_admitted_eq (verify : SigVerifier)
    (e : EpochStore) (a : ChannelAnnellation)
    (h : CanonicalMessageAdmitted verify e.store (.channelAnnouncement a)) :
    epochStep verify e (.channelAnnouncement a) =
      { store := applyGossipCanonicalStore verify e.store (.channelAnnouncement a)
        epoch := e.epoch + 1
        annStamps := (a.shortChannelId, e.epoch + 1) :: e.annStamps
        updStamps := e.updStamps } := by
  simp [epochStep, h]

/-- Equation for an admitted update step. -/
theorem epochStep_update_admitted_eq (verify : SigVerifier) (e : EpochStore)
    (u : ChannelUpdate)
    (h : CanonicalMessageAdmitted verify e.store (.channelUpdate u)) :
    epochStep verify e (.channelUpdate u) =
      { store := applyGossipCanonicalStore verify e.store (.channelUpdate u)
        epoch := e.epoch + 1
        annStamps := e.annStamps
        updStamps := (⟨u.shortChannelId, u.direction⟩, e.epoch + 1) :: e.updStamps } := by
  simp [epochStep, h]

/-- Equation for an admitted node-announcement step. -/
theorem epochStep_node_admitted_eq (verify : SigVerifier) (e : EpochStore)
    (n : NodeAnnouncement)
    (h : CanonicalMessageAdmitted verify e.store (.nodeAnnouncement n)) :
    epochStep verify e (.nodeAnnouncement n) =
      { store := applyGossipCanonicalStore verify e.store (.nodeAnnouncement n)
        epoch := e.epoch + 1
        annStamps := e.annStamps
        updStamps := e.updStamps } := by
  simp [epochStep, h]

/-! ### 3.2 Slot stamps written by a step -/

/-- An admitted announcement writes its channel slot at the new epoch. -/
theorem annStamp_epochStep_announcement_admitted (verify : SigVerifier)
    (e : EpochStore) (a : ChannelAnnellation)
    (h : CanonicalMessageAdmitted verify e.store (.channelAnnouncement a)) :
    (epochStep verify e (.channelAnnouncement a)).annStamp a.shortChannelId =
      some (e.epoch + 1) := by
  simp [EpochStore.annStamp, epochStep, h, lookupStamp]

/-- A step that does not target `k` leaves `k`'s announcement stamp unchanged. -/
theorem annStamp_epochStep_announcement_of_ne (verify : SigVerifier)
    (e : EpochStore) (a : ChannelAnnellation) {k : ShortChannelId}
    (hk : a.shortChannelId ≠ k) :
    (epochStep verify e (.channelAnnouncement a)).annStamp k = e.annStamp k := by
  by_cases h : CanonicalMessageAdmitted verify e.store (.channelAnnouncement a)
  · simp [EpochStore.annStamp, epochStep, h, lookupStamp, hk]
  · rw [epochStep_eq_self_of_rejected verify e _ h]

/-- An admitted update writes its directional slot at the new epoch. -/
theorem updStamp_epochStep_update_admitted (verify : SigVerifier)
    (e : EpochStore) (u : ChannelUpdate)
    (h : CanonicalMessageAdmitted verify e.store (.channelUpdate u)) :
    (epochStep verify e (.channelUpdate u)).updStamp
        ⟨u.shortChannelId, u.direction⟩ = some (e.epoch + 1) := by
  simp [EpochStore.updStamp, epochStep, h, lookupStamp]

/-- A step that does not target `s` leaves `s`'s update stamp unchanged. -/
theorem updStamp_epochStep_update_of_ne (verify : SigVerifier)
    (e : EpochStore) (u : ChannelUpdate) {s : UpdateSlot}
    (hs : (⟨u.shortChannelId, u.direction⟩ : UpdateSlot) ≠ s) :
    (epochStep verify e (.channelUpdate u)).updStamp s = e.updStamp s := by
  by_cases h : CanonicalMessageAdmitted verify e.store (.channelUpdate u)
  · simp [EpochStore.updStamp, epochStep, h, lookupStamp, hs]
  · rw [epochStep_eq_self_of_rejected verify e _ h]

/-- The update branch never touches announcement stamps. -/
theorem annStamp_epochStep_update (verify : SigVerifier) (e : EpochStore)
    (u : ChannelUpdate) :
    (epochStep verify e (.channelUpdate u)).annStamp = e.annStamp := by
  funext k
  by_cases h : CanonicalMessageAdmitted verify e.store (.channelUpdate u)
  · simp [EpochStore.annStamp, epochStep, h]
  · rw [epochStep_eq_self_of_rejected verify e _ h]

/-- The node-announcement branch never touches announcement stamps. -/
theorem annStamp_epochStep_node (verify : SigVerifier) (e : EpochStore)
    (n : NodeAnnouncement) :
    (epochStep verify e (.nodeAnnouncement n)).annStamp = e.annStamp := by
  funext k
  by_cases h : CanonicalMessageAdmitted verify e.store (.nodeAnnouncement n)
  · simp [EpochStore.annStamp, epochStep, h]
  · rw [epochStep_eq_self_of_rejected verify e _ h]

/-- The announcement branch never touches update stamps. -/
theorem updStamp_epochStep_announcement (verify : SigVerifier) (e : EpochStore)
    (a : ChannelAnnellation) :
    (epochStep verify e (.channelAnnouncement a)).updStamp = e.updStamp := by
  funext s
  by_cases h : CanonicalMessageAdmitted verify e.store (.channelAnnouncement a)
  · simp [EpochStore.updStamp, epochStep, h]
  · rw [epochStep_eq_self_of_rejected verify e _ h]

/-- The node-announcement branch never touches update stamps. -/
theorem updStamp_epochStep_node (verify : SigVerifier) (e : EpochStore)
    (n : NodeAnnouncement) :
    (epochStep verify e (.nodeAnnouncement n)).updStamp = e.updStamp := by
  funext s
  by_cases h : CanonicalMessageAdmitted verify e.store (.nodeAnnouncement n)
  · simp [EpochStore.updStamp, epochStep, h]
  · rw [epochStep_eq_self_of_rejected verify e _ h]

/-! ## 4. The bounded-stamp invariant is preserved -/

/-- Every epoch step preserves `StampBounded`: the newly written stamp is the
new epoch, and all older stamps are bounded by the old epoch. -/
theorem stampBounded_epochStep (verify : SigVerifier) (e : EpochStore)
    (m : GossipMessage) (hb : StampBounded e) :
    StampBounded (epochStep verify e m) := by
  cases m with
  | channelAnnouncement a =>
      by_cases h : CanonicalMessageAdmitted verify e.store (.channelAnnouncement a)
      · simp only [epochStep, if_pos h]
        change (∀ p ∈ (a.shortChannelId, e.epoch + 1) :: e.annStamps,
            p.2 ≤ e.epoch + 1) ∧
          (∀ p ∈ e.updStamps, p.2 ≤ e.epoch + 1)
        refine ⟨?_, ?_⟩
        · intro p hp
          rcases List.mem_cons.mp hp with rfl | hp
          · exact Nat.le_refl (e.epoch + 1)
          · exact Nat.le_trans (hb.1 p hp) (Nat.le_succ e.epoch)
        · intro p hp
          exact Nat.le_trans (hb.2 p hp) (Nat.le_succ e.epoch)
      · rw [epochStep_eq_self_of_rejected verify e _ h]
        exact hb
  | channelUpdate u =>
      by_cases h : CanonicalMessageAdmitted verify e.store (.channelUpdate u)
      · simp only [epochStep, if_pos h]
        change (∀ p ∈ e.annStamps, p.2 ≤ e.epoch + 1) ∧
          (∀ p ∈ (⟨u.shortChannelId, u.direction⟩, e.epoch + 1) :: e.updStamps,
            p.2 ≤ e.epoch + 1)
        refine ⟨?_, ?_⟩
        · intro p hp
          exact Nat.le_trans (hb.1 p hp) (Nat.le_succ e.epoch)
        · intro p hp
          rcases List.mem_cons.mp hp with rfl | hp
          · exact Nat.le_refl (e.epoch + 1)
          · exact Nat.le_trans (hb.2 p hp) (Nat.le_succ e.epoch)
      · rw [epochStep_eq_self_of_rejected verify e _ h]
        exact hb
  | nodeAnnouncement n =>
      by_cases h : CanonicalMessageAdmitted verify e.store (.nodeAnnouncement n)
      · simp only [epochStep, if_pos h]
        change (∀ p ∈ e.annStamps, p.2 ≤ e.epoch + 1) ∧
          (∀ p ∈ e.updStamps, p.2 ≤ e.epoch + 1)
        refine ⟨?_, ?_⟩
        · intro p hp
          exact Nat.le_trans (hb.1 p hp) (Nat.le_succ e.epoch)
        · intro p hp
          exact Nat.le_trans (hb.2 p hp) (Nat.le_succ e.epoch)
      · rw [epochStep_eq_self_of_rejected verify e _ h]
        exact hb

/-! ## 5. Monotonicity of slot stamps -/

/-- **No announcement slot stamp decreases.**  If `k` had stamp `t` before the
step and `t'` after it, then `t ≤ t'`. -/
theorem annStamp_mono (verify : SigVerifier) (e : EpochStore)
    (m : GossipMessage) (hb : StampBounded e) {k : ShortChannelId}
    {t t' : StoreEpoch} (h : e.annStamp k = some t)
    (h' : (epochStep verify e m).annStamp k = some t') : t ≤ t' := by
  cases m with
  | channelAnnouncement a =>
      by_cases hg : CanonicalMessageAdmitted verify e.store (.channelAnnouncement a)
      · by_cases hk : a.shortChannelId = k
        · subst hk
          rw [annStamp_epochStep_announcement_admitted verify e a hg] at h'
          cases h'
          exact Nat.le_trans (annStamp_le_epoch hb h) (Nat.le_succ e.epoch)
        · rw [annStamp_epochStep_announcement_of_ne verify e a hk] at h'
          rw [h] at h'
          cases h'
          exact Nat.le_refl t
      · rw [epochStep_eq_self_of_rejected verify e _ hg] at h'
        rw [h] at h'
        cases h'
        exact Nat.le_refl t
  | channelUpdate u =>
      rw [annStamp_epochStep_update verify e u] at h'
      rw [h] at h'
      cases h'
      exact Nat.le_refl t
  | nodeAnnouncement n =>
      rw [annStamp_epochStep_node verify e n] at h'
      rw [h] at h'
      cases h'
      exact Nat.le_refl t

/-- **No update slot stamp decreases.** -/
theorem updStamp_mono (verify : SigVerifier) (e : EpochStore)
    (m : GossipMessage) (hb : StampBounded e) {s : UpdateSlot}
    {t t' : StoreEpoch} (h : e.updStamp s = some t)
    (h' : (epochStep verify e m).updStamp s = some t') : t ≤ t' := by
  cases m with
  | channelAnnouncement a =>
      rw [updStamp_epochStep_announcement verify e a] at h'
      rw [h] at h'
      cases h'
      exact Nat.le_refl t
  | channelUpdate u =>
      by_cases hg : CanonicalMessageAdmitted verify e.store (.channelUpdate u)
      · by_cases hs : (⟨u.shortChannelId, u.direction⟩ : UpdateSlot) = s
        · subst hs
          rw [updStamp_epochStep_update_admitted verify e u hg] at h'
          cases h'
          exact Nat.le_trans (updStamp_le_epoch hb h) (Nat.le_succ e.epoch)
        · rw [updStamp_epochStep_update_of_ne verify e u hs] at h'
          rw [h] at h'
          cases h'
          exact Nat.le_refl t
      · rw [epochStep_eq_self_of_rejected verify e _ hg] at h'
        rw [h] at h'
        cases h'
        exact Nat.le_refl t
  | nodeAnnouncement n =>
      rw [updStamp_epochStep_node verify e n] at h'
      rw [h] at h'
      cases h'
      exact Nat.le_refl t

/-- **An admitted announcement strictly increases its own slot stamp.** -/
theorem annStamp_strict_of_epochStep_announcement (verify : SigVerifier)
    (e : EpochStore) (a : ChannelAnnellation) (hb : StampBounded e)
    (hg : CanonicalMessageAdmitted verify e.store (.channelAnnouncement a))
    {t : StoreEpoch} (h : e.annStamp a.shortChannelId = some t) :
    ∃ t', (epochStep verify e (.channelAnnouncement a)).annStamp a.shortChannelId =
        some t' ∧ t < t' := by
  refine ⟨e.epoch + 1, annStamp_epochStep_announcement_admitted verify e a hg, ?_⟩
  exact Nat.lt_of_le_of_lt (annStamp_le_epoch hb h) (Nat.lt_succ_self e.epoch)

/-- **An admitted update strictly increases its own directional-slot stamp.** -/
theorem updStamp_strict_of_epochStep_update (verify : SigVerifier)
    (e : EpochStore) (u : ChannelUpdate) (hb : StampBounded e)
    (hg : CanonicalMessageAdmitted verify e.store (.channelUpdate u))
    {t : StoreEpoch} (h : e.updStamp ⟨u.shortChannelId, u.direction⟩ = some t) :
    ∃ t', (epochStep verify e (.channelUpdate u)).updStamp
        ⟨u.shortChannelId, u.direction⟩ = some t' ∧ t < t' := by
  refine ⟨e.epoch + 1, updStamp_epochStep_update_admitted verify e u hg, ?_⟩
  exact Nat.lt_of_le_of_lt (updStamp_le_epoch hb h) (Nat.lt_succ_self e.epoch)

/-! ## 6. Relation to the BOLT 7 replacement rules -/

/-- **An epoch replacement of an update slot is a BOLT 7 timestamp
replacement.**  Every stored update already in the replaced directional slot has
a strictly older `timestamp`. -/
theorem epochStep_update_requires_newer_timestamp (verify : SigVerifier)
    (e : EpochStore) (u : ChannelUpdate)
    (h : CanonicalMessageAdmitted verify e.store (.channelUpdate u))
    {v : ChannelUpdate} (hv : v ∈ e.store.gossip.updates)
    (hscid : v.shortChannelId = u.shortChannelId)
    (hdir : v.direction = u.direction) : v.timestamp < u.timestamp :=
  h.2.2 v hv hscid hdir

/-- An admitted announcement replaces (does not append to) its channel record. -/
theorem epochStep_announcement_replaces (verify : SigVerifier)
    (e : EpochStore) (a : ChannelAnnellation)
    (h : CanonicalMessageAdmitted verify e.store (.channelAnnouncement a)) :
    (epochStep verify e (.channelAnnouncement a)).store.gossip.announcements =
      insertReplacing a e.store.gossip.announcements := by
  rw [epochStep_announcement_admitted_eq verify e a h,
    applyGossipCanonicalStore_announcement_of_admitted verify e.store a h]

/-- **Announcement replacement drops the previous record for the channel.**  A
distinct stored record with the same `short_channel_id` is gone after the
admitted replacement. -/
theorem epochStep_announcement_old_record_gone (verify : SigVerifier)
    (e : EpochStore) (a : ChannelAnnellation)
    (h : CanonicalMessageAdmitted verify e.store (.channelAnnouncement a))
    {b : ChannelAnnellation} (hb : b ∈ e.store.gossip.announcements)
    (hscid : b.shortChannelId = a.shortChannelId) (hne : b ≠ a) :
    b ∉ (epochStep verify e (.channelAnnouncement a)).store.gossip.announcements := by
  rw [epochStep_announcement_replaces verify e a h]
  intro hmem
  rcases mem_insertReplacing_iff.mp hmem with hba | ⟨_, hdiff⟩
  · exact hne hba
  · exact hdiff hscid

/-! ## 7. Store sequences -/

/-- A finite gossip store sequence. -/
abbrev StoreSequence := List GossipMessage

/-- Fold the canonical store step over a sequence. -/
noncomputable def runCanonicalStoreSteps (verify : SigVerifier) (cs : CanonicalStore) :
    StoreSequence → CanonicalStore
  | [] => cs
  | m :: ms => runCanonicalStoreSteps verify (applyGossipCanonicalStore verify cs m) ms

/-- Fold the epoch-carrying store step over a sequence. -/
noncomputable def runEpochSteps (verify : SigVerifier) (e : EpochStore) :
    StoreSequence → EpochStore
  | [] => e
  | m :: ms => runEpochSteps verify (epochStep verify e m) ms

/-- Every message of the sequence is admitted at the point it is applied. -/
def AdmittedAlong (verify : SigVerifier) : EpochStore → StoreSequence → Prop
  | _, [] => True
  | e, m :: ms =>
      CanonicalMessageAdmitted verify e.store m ∧
        AdmittedAlong verify (epochStep verify e m) ms

@[simp] theorem runEpochSteps_nil (verify : SigVerifier) (e : EpochStore) :
    runEpochSteps verify e [] = e := rfl

@[simp] theorem runCanonicalStoreSteps_nil (verify : SigVerifier)
    (cs : CanonicalStore) : runCanonicalStoreSteps verify cs [] = cs := rfl

/-- Unfolding of the epoch run at a cons. -/
theorem runEpochSteps_cons (verify : SigVerifier) (e : EpochStore)
    (m : GossipMessage) (ms : StoreSequence) :
    runEpochSteps verify e (m :: ms) =
      runEpochSteps verify (epochStep verify e m) ms := rfl

/-- Unfolding of the canonical run at a cons. -/
theorem runCanonicalStoreSteps_cons (verify : SigVerifier) (cs : CanonicalStore)
    (m : GossipMessage) (ms : StoreSequence) :
    runCanonicalStoreSteps verify cs (m :: ms) =
      runCanonicalStoreSteps verify (applyGossipCanonicalStore verify cs m) ms := rfl

/-- **The epoch run erases to the canonical run.**  Sequence-level form of
`epochStep_store`. -/
theorem runEpochSteps_store (verify : SigVerifier) (e : EpochStore)
    (ms : StoreSequence) :
    (runEpochSteps verify e ms).store = runCanonicalStoreSteps verify e.store ms := by
  induction ms generalizing e with
  | nil => rfl
  | cons m ms ih =>
      rw [runEpochSteps_cons, runCanonicalStoreSteps_cons,
        ih (epochStep verify e m), epochStep_store]

/-- The epoch is monotone along any store sequence. -/
theorem runEpochSteps_epoch_ge (verify : SigVerifier) (e : EpochStore)
    (ms : StoreSequence) : e.epoch ≤ (runEpochSteps verify e ms).epoch := by
  induction ms generalizing e with
  | nil => exact Nat.le_refl e.epoch
  | cons m ms ih =>
      rw [runEpochSteps_cons]
      exact Nat.le_trans (epochStep_epoch_ge verify e m) (ih (epochStep verify e m))

/-- The epoch grows by at most one per message: after `n` messages it is at most
`e.epoch + n`. -/
theorem runEpochSteps_epoch_le (verify : SigVerifier) (e : EpochStore)
    (ms : StoreSequence) :
    (runEpochSteps verify e ms).epoch ≤ e.epoch + ms.length := by
  induction ms generalizing e with
  | nil => simp
  | cons m ms ih =>
      rw [runEpochSteps_cons]
      have h1 := epochStep_epoch_le_succ verify e m
      have h2 := ih (epochStep verify e m)
      calc
        (runEpochSteps verify (epochStep verify e m) ms).epoch
            ≤ (epochStep verify e m).epoch + ms.length := h2
        _ ≤ (e.epoch + 1) + ms.length := Nat.add_le_add_right h1 _
        _ = e.epoch + (m :: ms).length := by
          simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- **Exact epoch count on a fully admitted sequence.**  If every message is
admitted when applied, the final epoch is exactly `e.epoch + ms.length`.  This
is the precise statement of "the epoch is the number of admissions". -/
theorem runEpochSteps_epoch_eq_of_admitted (verify : SigVerifier)
    (e : EpochStore) (ms : StoreSequence) (h : AdmittedAlong verify e ms) :
    (runEpochSteps verify e ms).epoch = e.epoch + ms.length := by
  induction ms generalizing e with
  | nil => simp
  | cons m ms ih =>
      rcases h with ⟨hg, hrest⟩
      rw [runEpochSteps_cons]
      have h' := ih (epochStep verify e m) hrest
      rw [h', epochStep_epoch_succ_of_admitted verify e m hg]
      simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- The bounded-stamp invariant holds along any store sequence. -/
theorem runEpochSteps_stampBounded (verify : SigVerifier) (e : EpochStore)
    (ms : StoreSequence) (hb : StampBounded e) :
    StampBounded (runEpochSteps verify e ms) := by
  induction ms generalizing e with
  | nil => exact hb
  | cons m ms ih =>
      rw [runEpochSteps_cons]
      exact ih (epochStep verify e m) (stampBounded_epochStep verify e m hb)

/-- A slot that had a stamp keeps a stamp after any one step. -/
theorem annStamp_epochStep_exists (verify : SigVerifier) (e : EpochStore)
    (m : GossipMessage) {k : ShortChannelId} {t : StoreEpoch}
    (h : e.annStamp k = some t) :
    ∃ t', (epochStep verify e m).annStamp k = some t' := by
  cases m with
  | channelAnnouncement a =>
      by_cases hg : CanonicalMessageAdmitted verify e.store (.channelAnnouncement a)
      · by_cases hk : a.shortChannelId = k
        · subst hk
          exact ⟨_, annStamp_epochStep_announcement_admitted verify e a hg⟩
        · exact ⟨t, by rw [annStamp_epochStep_announcement_of_ne verify e a hk]; exact h⟩
      · exact ⟨t, by rw [epochStep_eq_self_of_rejected verify e _ hg]; exact h⟩
  | channelUpdate u =>
      exact ⟨t, by rw [annStamp_epochStep_update verify e u]; exact h⟩
  | nodeAnnouncement n =>
      exact ⟨t, by rw [annStamp_epochStep_node verify e n]; exact h⟩

/-- A slot that had an update stamp keeps one after any one step. -/
theorem updStamp_epochStep_exists (verify : SigVerifier) (e : EpochStore)
    (m : GossipMessage) {s : UpdateSlot} {t : StoreEpoch}
    (h : e.updStamp s = some t) :
    ∃ t', (epochStep verify e m).updStamp s = some t' := by
  cases m with
  | channelAnnouncement a =>
      exact ⟨t, by rw [updStamp_epochStep_announcement verify e a]; exact h⟩
  | channelUpdate u =>
      by_cases hg : CanonicalMessageAdmitted verify e.store (.channelUpdate u)
      · by_cases hs : (⟨u.shortChannelId, u.direction⟩ : UpdateSlot) = s
        · subst hs
          exact ⟨_, updStamp_epochStep_update_admitted verify e u hg⟩
        · exact ⟨t, by rw [updStamp_epochStep_update_of_ne verify e u hs]; exact h⟩
      · exact ⟨t, by rw [epochStep_eq_self_of_rejected verify e _ hg]; exact h⟩
  | nodeAnnouncement n =>
      exact ⟨t, by rw [updStamp_epochStep_node verify e n]; exact h⟩

/-- **No announcement slot stamp decreases along a store sequence.** -/
theorem runEpochSteps_annStamp_mono (verify : SigVerifier) (e : EpochStore)
    (ms : StoreSequence) (hb : StampBounded e) {k : ShortChannelId}
    {t t' : StoreEpoch} (h : e.annStamp k = some t)
    (h' : (runEpochSteps verify e ms).annStamp k = some t') : t ≤ t' := by
  induction ms generalizing e t t' with
  | nil => rw [runEpochSteps_nil] at h'; rw [h] at h'; cases h'; exact Nat.le_refl t
  | cons m ms ih =>
      rw [runEpochSteps_cons] at h'
      obtain ⟨tmid, hmid⟩ := annStamp_epochStep_exists verify e m h
      have hstep := annStamp_mono verify e m hb h hmid
      have hb' := stampBounded_epochStep verify e m hb
      have htail := ih (epochStep verify e m) hb' hmid h'
      exact Nat.le_trans hstep htail

/-- **No update slot stamp decreases along a store sequence.** -/
theorem runEpochSteps_updStamp_mono (verify : SigVerifier) (e : EpochStore)
    (ms : StoreSequence) (hb : StampBounded e) {s : UpdateSlot}
    {t t' : StoreEpoch} (h : e.updStamp s = some t)
    (h' : (runEpochSteps verify e ms).updStamp s = some t') : t ≤ t' := by
  induction ms generalizing e t t' with
  | nil => rw [runEpochSteps_nil] at h'; rw [h] at h'; cases h'; exact Nat.le_refl t
  | cons m ms ih =>
      rw [runEpochSteps_cons] at h'
      obtain ⟨tmid, hmid⟩ := updStamp_epochStep_exists verify e m h
      have hstep := updStamp_mono verify e m hb h hmid
      have hb' := stampBounded_epochStep verify e m hb
      have htail := ih (epochStep verify e m) hb' hmid h'
      exact Nat.le_trans hstep htail

/-! ## 8. Reachable epoch stores -/

/-- Epoch stores reachable from the empty store (any initial registration map)
by finitely many `epochStep`s. -/
inductive ReachableEpochStore (verify : SigVerifier) : EpochStore → Prop
  | empty (nodeKeyOf : NodeId → PubKey) :
      ReachableEpochStore verify
        { store := { gossip := ⟨[], [], []⟩, nodeKeyOf := nodeKeyOf }
          epoch := 0, annStamps := [], updStamps := [] }
  | step {e : EpochStore} {m : GossipMessage} :
      ReachableEpochStore verify e →
        ReachableEpochStore verify (epochStep verify e m)

/-- **The epoch layer adds no reachable states at the store level.**  Every
reachable epoch store projects to a reachable canonical store. -/
theorem reachableEpochStore_store_reachable {verify : SigVerifier}
    {e : EpochStore} (h : ReachableEpochStore verify e) :
    ReachableCanonicalStore verify e.store := by
  induction h with
  | empty nodeKeyOf => exact ReachableCanonicalStore.empty nodeKeyOf
  | step _ ih =>
      rw [epochStep_store]
      exact ReachableCanonicalStore.step ih

/-- Every reachable epoch store has bounded slot stamps. -/
theorem reachableEpochStore_stampBounded {verify : SigVerifier}
    {e : EpochStore} (h : ReachableEpochStore verify e) : StampBounded e := by
  induction h with
  | empty nodeKeyOf =>
      refine ⟨?_, ?_⟩ <;> (intro p hp; simp at hp)
  | step _ ih => exact stampBounded_epochStep verify _ _ ih

/-- Every reachable epoch store carries the full canonical store invariant. -/
theorem reachableEpochStore_invariant {verify : SigVerifier}
    {e : EpochStore} (h : ReachableEpochStore verify e) :
    CanonicalStoreAdmitted verify e.store :=
  reachableCanonicalStore_invariant (reachableEpochStore_store_reachable h)

/-- The stored announcements of a reachable epoch store are valid. -/
theorem reachableEpochStore_store_valid {verify : SigVerifier}
    {e : EpochStore} (h : ReachableEpochStore verify e) :
    StoreAnnouncementsValid verify e.store.gossip :=
  (reachableEpochStore_invariant h).storeValid

/-- One announcement per channel in a reachable epoch store. -/
theorem reachableEpochStore_canonical {verify : SigVerifier}
    {e : EpochStore} (h : ReachableEpochStore verify e) :
    CanonicalAnnouncements e.store.gossip.announcements :=
  (reachableEpochStore_invariant h).canonical

/-- One update per directional slot in a reachable epoch store. -/
theorem reachableEpochStore_updates_slotUnique {verify : SigVerifier}
    {e : EpochStore} (h : ReachableEpochStore verify e) :
    UpdatesSlotUnique e.store.gossip.updates :=
  (reachableEpochStore_invariant h).updatesSlotUnique

/-- The registration map of a reachable epoch store is consistent. -/
theorem reachableEpochStore_nodeKeyConsistent {verify : SigVerifier}
    {e : EpochStore} (h : ReachableEpochStore verify e) :
    GossipState.NodeKeyConsistent e.store.nodeKeyOf e.store.gossip :=
  (reachableEpochStore_invariant h).nodeKeys

/-! ## 9. The raw-store negative results are preserved unchanged -/

/-- The raw store still has no canonical-preserving announcement extension.
This is the wave-7 impossibility, re-exported: the epoch layer does not change
`applyGossip` and does not make raw append canonical. -/
theorem raw_nonrefinement_preserved :
    ¬ ∃ F : GossipState → GossipMessage → GossipState,
      (∀ (s : GossipState) (a : ChannelAnnellation),
        F s (.channelAnnouncement a) = applyGossip s (.channelAnnouncement a)) ∧
      (∀ s : GossipState, CanonicalAnnouncements s.announcements →
        ∀ m : GossipMessage,
          CanonicalAnnouncements (F s m).announcements) :=
  no_canonical_preserving_raw_announcement_extension

/-- The raw global clock is still strictly stronger than the canonical per-slot
gate: a canonically admitted update can be ignored by `GossipState.applyUpdate`.
Re-exported unchanged from wave 7. -/
theorem raw_clock_boundary_preserved :
    ∃ (verify : SigVerifier) (cs : CanonicalStore) (u : ChannelUpdate),
      ReachableCanonicalStore verify cs ∧
        CanonicalMessageAdmitted verify cs (.channelUpdate u) ∧
          ¬ RawClockAdmits cs.gossip (.channelUpdate u) ∧
            (applyGossipCanonicalStore verify cs (.channelUpdate u)).gossip.updates =
              u :: cs.gossip.updates ∧
              applyGossip cs.gossip (.channelUpdate u) = cs.gossip ∧
                u ∉ cs.gossip.updates :=
  canonical_admission_strictly_weaker_than_raw_clock

/-- Raw `applyGossip` still accepts conflicting announcements; the epoch model
does not touch the raw transition. -/
theorem raw_conflicting_announcement_preserved :
    ∃ (s : GossipState) (a : ChannelAnnellation),
      ¬ CanonicalAnnouncements
        (applyGossip s (.channelAnnouncement a)).announcements :=
  raw_applyGossip_accepts_conflicting_announcement

/-! ## 10. Concrete witnesses -/

private def acceptAll : SigVerifier := fun _ _ _ => true

/-- Byte length 1. -/
private def kA : PubKey := ⟨ByteArray.mk #[1]⟩

/-- Byte length 0. -/
private def kB : PubKey := ⟨ByteArray.empty⟩

private def nA : NodeId := ⟨0⟩

private def nB : NodeId := ⟨1⟩

private def sc1 : ShortChannelId := ⟨1, 2, 3⟩

private def emptySig : GossipSignature := ⟨ByteArray.empty⟩

private def mkAnn (u v : NodeId) (ka kb : PubKey) (cap : Nat) :
    ChannelAnnellation :=
  { shortChannelId := sc1
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

/-- Channel `sc1`: `nA ↦ kA`, `nB ↦ kB`. -/
private def ann1 : ChannelAnnellation := mkAnn nA nB kA kB 1000

private def mkUpd (ts : Nat) (k : PubKey) : ChannelUpdate :=
  { shortChannelId := sc1
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

/-- Direction-0 update, timestamp 1, signed by `kA`. -/
private def u0 : ChannelUpdate := mkUpd 1 kA

/-- Direction-0 update, timestamp 2, signed by `kA`; supersedes `u0`. -/
private def u1 : ChannelUpdate := mkUpd 2 kA

private theorem ann1_valid : ann1.signaturesValid acceptAll := by
  simp [ChannelAnnellation.signaturesValid, signatureValid, acceptAll]

private theorem u0_valid : u0.signatureValid acceptAll := by
  simp [ChannelUpdate.signatureValid, signatureValid, acceptAll]

private theorem u1_valid : u1.signatureValid acceptAll := by
  simp [ChannelUpdate.signatureValid, signatureValid, acceptAll]

private theorem nA_ne_nB : nA ≠ nB := by decide

private theorem ann1_nodes_ne : ann1.node1 ≠ ann1.node2 := by
  simpa [ann1, mkAnn] using nA_ne_nB

private def e0 : EpochStore :=
  { store := { gossip := ⟨[], [], []⟩, nodeKeyOf := fun _ => kB }
    epoch := 0, annStamps := [], updStamps := [] }

private theorem e0_compat (a : ChannelAnnellation) :
    e0.store.gossip.CompatibleWithStore a := by
  intro b hb
  simp [e0] at hb

private theorem e0_auth (a : ChannelAnnellation) :
    UpdatesAuthorizedBy e0.store.gossip a := by
  intro u hu
  simp [e0] at hu

private theorem e0_announcement_gate :
    CanonicalMessageAdmitted acceptAll e0.store (.channelAnnouncement ann1) :=
  ⟨ann1_valid, ann1_nodes_ne, e0_compat ann1, e0_auth ann1⟩

/-- After the first announcement: epoch 1, channel slot stamped at 1. -/
private noncomputable def e1 : EpochStore :=
  epochStep acceptAll e0 (.channelAnnouncement ann1)

private theorem e1_store_eq :
    e1.store =
      { gossip := { e0.store.gossip with
          announcements := insertReplacing ann1 e0.store.gossip.announcements }
        nodeKeyOf := bindNodeKeys e0.store.nodeKeyOf ann1 } := by
  rw [e1, epochStep_announcement_admitted_eq acceptAll e0 ann1
      e0_announcement_gate,
    applyGossipCanonicalStore_announcement_of_admitted acceptAll e0.store ann1
      e0_announcement_gate]

private theorem e1_announcements : e1.store.gossip.announcements = [ann1] := by
  rw [e1_store_eq]
  simp [e0, insertReplacing]

private theorem e1_updates : e1.store.gossip.updates = [] := by
  rw [e1_store_eq]
  simp [e0]

private theorem e1_epoch : e1.epoch = 1 := by
  rw [e1, epochStep_announcement_admitted_eq acceptAll e0 ann1
    e0_announcement_gate]
  simp [e0]

private theorem e1_annStamp : e1.annStamp sc1 = some 1 := by
  show e1.annStamp ann1.shortChannelId = some 1
  rw [e1, annStamp_epochStep_announcement_admitted acceptAll e0 ann1
    e0_announcement_gate]
  simp [e0]

private theorem e1_stampBounded : StampBounded e1 :=
  stampBounded_epochStep acceptAll e0 (.channelAnnouncement ann1) (by
    refine ⟨?_, ?_⟩ <;> (intro p hp; simp [e0] at hp))

private theorem e1_attributed_u0 :
    e1.store.gossip.updateKeyAnnouncedDirectional u0 := by
  refine GossipState.updateKeyAnnouncedDirectional_of_mem (a := ann1) ?_ rfl ?_
  · rw [e1_announcements]
    exact List.mem_singleton_self ann1
  · rw [ChannelUpdate.direction_of_channelFlags_zero (by rfl : u0.channelFlags = 0)]
    simpa [ann1, mkAnn, u0, mkUpd] using
      (ChannelAnnellation.attributesKeyForDirection_node1 ann1)

private theorem e1_supersedes_u0 : UpdateSupersedes u0 e1.store.gossip.updates := by
  intro v hv
  rw [e1_updates] at hv
  simp at hv

private theorem e1_update_gate :
    CanonicalMessageAdmitted acceptAll e1.store (.channelUpdate u0) :=
  ⟨u0_valid, e1_attributed_u0, e1_supersedes_u0⟩

/-- After the first update: epoch 2, direction-0 slot stamped at 2. -/
private noncomputable def e2 : EpochStore :=
  epochStep acceptAll e1 (.channelUpdate u0)

private theorem e2_store_eq :
    e2.store =
      { gossip := { e1.store.gossip with
          updates := insertUpdateCanonical u0 e1.store.gossip.updates }
        nodeKeyOf := e1.store.nodeKeyOf } := by
  rw [e2, epochStep_update_admitted_eq acceptAll e1 u0 e1_update_gate,
    applyGossipCanonicalStore_update_of_admitted acceptAll e1.store u0
      e1_update_gate]

private theorem e2_announcements : e2.store.gossip.announcements = [ann1] := by
  rw [e2_store_eq]
  simpa using e1_announcements

private theorem e2_updates : e2.store.gossip.updates = [u0] := by
  rw [e2_store_eq]
  simp [e1_updates, insertUpdateCanonical]

private theorem e2_epoch : e2.epoch = 2 := by
  rw [e2, epochStep_update_admitted_eq acceptAll e1 u0 e1_update_gate]
  simp [e1_epoch]

private theorem e2_updStamp :
    e2.updStamp ⟨sc1, false⟩ = some 2 := by
  show e2.updStamp ⟨u0.shortChannelId, u0.direction⟩ = some 2
  rw [e2, updStamp_epochStep_update_admitted acceptAll e1 u0 e1_update_gate,
    e1_epoch]

private theorem e2_stampBounded : StampBounded e2 :=
  stampBounded_epochStep acceptAll e1 (.channelUpdate u0) e1_stampBounded

private theorem e2_attributed_u1 :
    e2.store.gossip.updateKeyAnnouncedDirectional u1 := by
  refine GossipState.updateKeyAnnouncedDirectional_of_mem (a := ann1) ?_ rfl ?_
  · rw [e2_announcements]
    exact List.mem_singleton_self ann1
  · rw [ChannelUpdate.direction_of_channelFlags_zero (by rfl : u1.channelFlags = 0)]
    simpa [ann1, mkAnn, u1, mkUpd] using
      (ChannelAnnellation.attributesKeyForDirection_node1 ann1)

private theorem e2_supersedes_u1 : UpdateSupersedes u1 e2.store.gossip.updates := by
  intro v hv _hscid _hdir
  rw [e2_updates] at hv
  simp only [List.mem_singleton] at hv
  subst v
  simp [u0, u1, mkUpd]

private theorem e2_update_gate :
    CanonicalMessageAdmitted acceptAll e2.store (.channelUpdate u1) :=
  ⟨u1_valid, e2_attributed_u1, e2_supersedes_u1⟩

/-- After the superseding update: epoch 3, direction-0 slot stamped at 3. -/
private noncomputable def e3 : EpochStore :=
  epochStep acceptAll e2 (.channelUpdate u1)

private theorem e3_store_eq :
    e3.store =
      { gossip := { e2.store.gossip with
          updates := insertUpdateCanonical u1 e2.store.gossip.updates }
        nodeKeyOf := e2.store.nodeKeyOf } := by
  rw [e3, epochStep_update_admitted_eq acceptAll e2 u1 e2_update_gate,
    applyGossipCanonicalStore_update_of_admitted acceptAll e2.store u1
      e2_update_gate]

private theorem e3_updates : e3.store.gossip.updates = [u1] := by
  rw [e3_store_eq]
  simp [e2_updates, insertUpdateCanonical, u0, u1, mkUpd, ChannelUpdate.direction]

private theorem e3_epoch : e3.epoch = 3 := by
  rw [e3, epochStep_update_admitted_eq acceptAll e2 u1 e2_update_gate]
  simp [e2_epoch]

private theorem e3_updStamp : e3.updStamp ⟨sc1, false⟩ = some 3 := by
  show e3.updStamp ⟨u1.shortChannelId, u1.direction⟩ = some 3
  rw [e3, updStamp_epochStep_update_admitted acceptAll e2 u1 e2_update_gate,
    e2_epoch]

private theorem e2_reachable : ReachableEpochStore acceptAll e2 := by
  change ReachableEpochStore acceptAll
    (epochStep acceptAll (epochStep acceptAll e0 (.channelAnnouncement ann1))
      (.channelUpdate u0))
  exact ReachableEpochStore.step
    (ReachableEpochStore.step
      (ReachableEpochStore.empty (fun _ => kB)))

/-- **Epoch replacement is real in a reachable epoch store.**  `e2` is reachable,
its direction-0 slot for `sc1` is stamped at epoch 2 and stores `u0`; applying
the superseding `u1` keeps the same slot, raises its stamp to 3 and stores `u1`
instead. -/
theorem epoch_update_replacement_witness :
    ∃ (verify : SigVerifier) (e : EpochStore) (s : UpdateSlot)
      (t t' : StoreEpoch),
      ReachableEpochStore verify e ∧
        e.updStamp s = some t ∧ t < t' ∧
          (epochStep verify e (.channelUpdate u1)).updStamp s = some t' ∧
            s.scid = sc1 ∧ s.direction = false ∧
              e.store.gossip.updates = [u0] ∧
                (epochStep verify e (.channelUpdate u1)).store.gossip.updates = [u1] := by
  refine ⟨acceptAll, e2, ⟨sc1, false⟩, 2, 3, e2_reachable, e2_updStamp, by decide,
    ?_, rfl, rfl, e2_updates, ?_⟩
  · show (epochStep acceptAll e2 (.channelUpdate u1)).updStamp
      ⟨u1.shortChannelId, u1.direction⟩ = some 3
    rw [updStamp_epochStep_update_admitted acceptAll e2 u1 e2_update_gate, e2_epoch]
  · show (epochStep acceptAll e2 (.channelUpdate u1)).store.gossip.updates = [u1]
    rw [epochStep_update_admitted_eq acceptAll e2 u1 e2_update_gate,
      applyGossipCanonicalStore_update_of_admitted acceptAll e2.store u1
        e2_update_gate]
    simp [e2_updates, insertUpdateCanonical, u0, u1, mkUpd, ChannelUpdate.direction]

/-- The epoch of the witness store is its slot stamp plus the number of
remaining slots: `e2.epoch = 2`.  (Stated separately so the arithmetic is
visible.) -/
theorem epoch_update_replacement_witness_epoch :
    e2.epoch = 2 ∧ e3.epoch = 3 :=
  ⟨e2_epoch, e3_epoch⟩

/-- A gossip store is unchanged by rewriting its announcement list to its own
value. -/
private theorem gossipState_with_announcements_eq_self {s : GossipState}
    {l : List ChannelAnnellation} (h : s.announcements = l) :
    { s with announcements := l } = s := by
  cases s with
  | mk ann upd node => simp_all

/-- **An admitted re-announcement of the identical head record leaves the
gossip content unchanged but still advances the epoch.**  This is the honest
boundary of the "epoch = admissions" semantics: the epoch is not a content
hash, and no theorem claims it is. -/
theorem epoch_admission_gossip_noop_witness :
    ∃ (verify : SigVerifier) (e : EpochStore),
      ReachableEpochStore verify e ∧
        CanonicalMessageAdmitted verify e.store (.channelAnnouncement ann1) ∧
          (epochStep verify e (.channelAnnouncement ann1)).epoch = e.epoch + 1 ∧
            (epochStep verify e (.channelAnnouncement ann1)).store.gossip =
              e.store.gossip := by
  have hcompat : e1.store.gossip.CompatibleWithStore ann1 := by
    intro b hb
    rw [e1_announcements] at hb
    simp only [List.mem_singleton] at hb
    subst b
    exact ⟨fun _ => rfl, fun h => absurd h.symm ann1_nodes_ne,
      fun h => absurd h ann1_nodes_ne, fun _ => rfl⟩
  have hauth : UpdatesAuthorizedBy e1.store.gossip ann1 := by
    intro u hu
    rw [e1_updates] at hu
    simp at hu
  have hgate : CanonicalMessageAdmitted acceptAll e1.store
      (.channelAnnouncement ann1) :=
    ⟨ann1_valid, ann1_nodes_ne, hcompat, hauth⟩
  refine ⟨acceptAll, e1, ReachableEpochStore.step
    (ReachableEpochStore.empty (fun _ => kB)), hgate, ?_, ?_⟩
  · show (epochStep acceptAll e1 (.channelAnnouncement ann1)).epoch = e1.epoch + 1
    exact epochStep_epoch_succ_of_admitted acceptAll e1 _ hgate
  · show (epochStep acceptAll e1 (.channelAnnouncement ann1)).store.gossip =
      e1.store.gossip
    have hann : insertReplacing ann1 e1.store.gossip.announcements = [ann1] := by
      rw [e1_announcements]
      simp [insertReplacing]
    rw [epochStep_announcement_admitted_eq acceptAll e1 ann1 hgate,
      applyGossipCanonicalStore_announcement_of_admitted acceptAll e1.store ann1
        hgate,
      hann]
    exact gossipState_with_announcements_eq_self e1_announcements

/-- The store sequence of the concrete run: announce `sc1`, then `u0`, then the
superseding `u1`. -/
private def seq : StoreSequence :=
  [.channelAnnouncement ann1, .channelUpdate u0, .channelUpdate u1]

private theorem seq_admitted : AdmittedAlong acceptAll e0 seq := by
  unfold seq
  simp only [AdmittedAlong]
  exact ⟨e0_announcement_gate, e1_update_gate, e2_update_gate, trivial⟩

/-- **Sequence-level epoch semantics, concretely.**  The three-message run is
fully admitted, so its epoch is exactly `0 + 3 = 3`; and its store is exactly the
canonical store run over the same sequence. -/
theorem epoch_sequence_of_three_admissions :
    (runEpochSteps acceptAll e0 seq).epoch = 3 ∧
      (runEpochSteps acceptAll e0 seq).store =
        runCanonicalStoreSteps acceptAll e0.store seq := by
  have h : (runEpochSteps acceptAll e0 seq).epoch = e0.epoch + seq.length :=
    runEpochSteps_epoch_eq_of_admitted acceptAll e0 seq seq_admitted
  have hlen : seq.length = 3 := rfl
  have hepoch0 : e0.epoch = 0 := rfl
  refine ⟨?_, runEpochSteps_store acceptAll e0 seq⟩
  rw [h, hlen, hepoch0]

/-! ## 11. Axiom audit for the headline results -/

#print axioms epochStep_semantics
#print axioms epochStep_store_change_requires_admitted
#print axioms stampBounded_epochStep
#print axioms annStamp_mono
#print axioms updStamp_mono
#print axioms annStamp_strict_of_epochStep_announcement
#print axioms updStamp_strict_of_epochStep_update
#print axioms epochStep_update_requires_newer_timestamp
#print axioms epochStep_announcement_old_record_gone
#print axioms runEpochSteps_store
#print axioms runEpochSteps_epoch_eq_of_admitted
#print axioms runEpochSteps_annStamp_mono
#print axioms reachableEpochStore_store_reachable
#print axioms reachableEpochStore_invariant
#print axioms raw_nonrefinement_preserved
#print axioms epoch_update_replacement_witness
#print axioms epoch_admission_gossip_noop_witness
#print axioms epoch_sequence_of_three_admissions

end LnLean.Proofs.WaveH.H39
