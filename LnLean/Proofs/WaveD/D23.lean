import LnLean.Routing.Gossip
import LnLean.Routing.Graph
import LnLean.Proofs.Routing.GossipProps

/-!
# LnLean.Proofs.WaveD.D23

Catalog obligation `LN-RT-002` (BOLT 7, "The `channel_update` Message"):

> A newer `channel_update` replaces an older one only if its timestamp is
> greater.

The catalog names a Lean target `LnLean.Routing.Gossip.update_monotone`.
No declaration with that name exists in the model; the model's relevant
store operation is `GossipState.applyUpdate` (a global timestamp clock) and
the per-channel replacement operation is
`LnLean.Routing.GossipProps.ChannelView.applyUpdate`.  This module proves
the obligation as a family of theorems over both operations:

* `waveD_d23_update_monotone` — the model's named monotonicity law: the
  newest stored timestamp never decreases.
* `waveD_d23_applyUpdate_clock_eq_max` — the exact new clock:
  `max oldClock u.timestamp`.
* `waveD_d23_clock_advances_iff` — the clock advances under `applyUpdate`
  **iff** `u.timestamp` is strictly greater than the old clock.
* `waveD_d23_changes_iff_newer` — the store changes **iff** the update is
  strictly newer; consequently a change is possible only if the timestamp
  is greater (`waveD_d23_replace_requires_greater`).
* `waveD_d23_greater_replaces` — a strictly newer update is installed at
  the head and becomes the clock.
* `waveD_d23_older_after_newer_noop`,
  `waveD_d23_older_than_stored_noop` — once a newer update is present,
  every older-or-equal update is a no-op.
* `waveD_d23_view_replacement_iff` — per channel, a replacement happens
  **iff** the `short_channel_id` matches and the timestamp is strictly
  greater.  This is the exact BOLT 7 per-direction rule, with the clock
  satisfying `waveD_d23_view_clock_advances_iff`.
* `waveD_d23_view_older_noop` and
  `waveD_d23_view_older_after_newer_noop` — stale updates do not replace
  the current state (the latter for a newer update that matched the same
  channel).

The model's global store is append-only and keys updates only by time, not
by `(short_channel_id, direction)`; the per-channel exact rule therefore
lives in the existing committed proof module `GossipProps`.  The global
clock is conservative: it may advance for an update on another channel
(see `waveD_d23_other_channel_advances_store_clock`), which never permits
an older timestamp to replace a newer one.

Everything here is proved without `sorry`, `axiom`, `admit`,
`native_decide`, `unsafe`, `@[implemented_by]`, or Mathlib.

BOLT anchor: BOLT 7, "The `channel_update` Message" (a `channel_update`
MUST NOT be accepted if its `timestamp` is not greater than the stored
one).  Catalog LDK anchors: `lightning/src/routing/gossip.rs:906`
(`pub struct ChannelUpdateInfo`, whose `last_update` field is the stored
timestamp) and `:422` (`NetworkGraph::handle_network_update`, an update
ingress point); the actual replacement comparison is in
`NetworkGraph::update_channel_internal` around `:2533`/`:2538`.
-/

namespace LnLean.Proofs.WaveD.D23

open LnLean.Routing
open LnLean.Routing.GossipProps

set_option autoImplicit false

-- OBLIGATION: LN-WD-D23

/-! ## Folding helper -/

/-- The `latestTimestamp` fold, generalised over its initial accumulator:
folding `max` over a list is the maximum of the accumulator and the fold
started at zero. -/
theorem waveD_d23_foldl_max_eq (l : List ChannelUpdate) (a : Nat) :
    l.foldl (fun acc u => max acc u.timestamp) a =
      max a (l.foldl (fun acc u => max acc u.timestamp) 0) := by
  induction l generalizing a with
  | nil => simp
  | cons u us ih =>
    simp only [List.foldl_cons]
    rw [ih (max a u.timestamp)]
    rw [ih (max 0 u.timestamp)]
    rw [Nat.max_eq_right (Nat.zero_le u.timestamp), Nat.max_assoc]

/-- The latest timestamp of a non-empty list, in `max` form. -/
theorem waveD_d23_latestTimestamp_cons (u : ChannelUpdate)
    (l : List ChannelUpdate) :
    latestTimestamp (u :: l) = max u.timestamp (latestTimestamp l) := by
  change l.foldl (fun acc u => max acc u.timestamp) (max 0 u.timestamp) =
    max u.timestamp (l.foldl (fun acc u => max acc u.timestamp) 0)
  rw [waveD_d23_foldl_max_eq l (max 0 u.timestamp)]
  rw [Nat.max_eq_right (Nat.zero_le u.timestamp)]

/-! ## The store-level clock -/

/-- **Exact store clock after an update.**  The newest timestamp of
`s.applyUpdate u` is the maximum of the old clock and `u.timestamp`. -/
theorem waveD_d23_applyUpdate_clock_eq_max (s : GossipState)
    (u : ChannelUpdate) :
    (s.applyUpdate u).latestUpdateTimestamp =
      max s.latestUpdateTimestamp u.timestamp := by
  unfold GossipState.applyUpdate
  split
  · rename_i h
    unfold GossipState.latestUpdateTimestamp
    rw [waveD_d23_latestTimestamp_cons, Nat.max_comm]
  · rename_i h
    exact (Nat.max_eq_left (Nat.le_of_not_lt h)).symm

/-- **Monotonicity.**  Applying a `channel_update` never lowers the newest
stored timestamp.  This is the law the catalog calls `update_monotone`. -/
theorem waveD_d23_update_monotone (s : GossipState) (u : ChannelUpdate) :
    s.latestUpdateTimestamp ≤ (s.applyUpdate u).latestUpdateTimestamp :=
  GossipState.latestUpdateTimestamp_applyUpdate_ge s u

/-- **The clock advances exactly when the update is newer.** -/
theorem waveD_d23_clock_advances_iff (s : GossipState)
    (u : ChannelUpdate) :
    s.latestUpdateTimestamp < (s.applyUpdate u).latestUpdateTimestamp ↔
      s.latestUpdateTimestamp < u.timestamp := by
  rw [waveD_d23_applyUpdate_clock_eq_max]
  constructor
  · intro h
    by_cases hle : u.timestamp ≤ s.latestUpdateTimestamp
    · rw [Nat.max_eq_left hle] at h
      exact (Nat.lt_irrefl s.latestUpdateTimestamp h).elim
    · exact Nat.lt_of_not_le hle
  · intro h
    rw [Nat.max_eq_right (Nat.le_of_lt h)]
    exact h

/-- **Only a greater timestamp can replace.**  If `applyUpdate` changes the
store at all, the incoming timestamp is strictly greater than the stored
clock. -/
theorem waveD_d23_replace_requires_greater (s : GossipState)
    (u : ChannelUpdate) (h : s.applyUpdate u ≠ s) :
    s.latestUpdateTimestamp < u.timestamp := by
  by_cases hle : u.timestamp ≤ s.latestUpdateTimestamp
  · exact absurd (GossipState.applyUpdate_stale s u hle) h
  · exact Nat.lt_of_not_le hle

/-- **A greater timestamp does replace.**  A strictly newer update is
stored at the head of the update list and becomes the new clock. -/
theorem waveD_d23_greater_replaces (s : GossipState) (u : ChannelUpdate)
    (h : s.latestUpdateTimestamp < u.timestamp) :
    (s.applyUpdate u).updates = u :: s.updates ∧
      (s.applyUpdate u).latestUpdateTimestamp = u.timestamp := by
  refine ⟨GossipState.applyUpdate_new s u h, ?_⟩
  rw [waveD_d23_applyUpdate_clock_eq_max]
  exact Nat.max_eq_right (Nat.le_of_lt h)

/-- **The store changes iff the timestamp is strictly greater.**  This is
the precise form of "replaces only if its timestamp is greater" for the
model's global gossip store. -/
theorem waveD_d23_changes_iff_newer (s : GossipState)
    (u : ChannelUpdate) :
    s.applyUpdate u ≠ s ↔ s.latestUpdateTimestamp < u.timestamp := by
  constructor
  · exact waveD_d23_replace_requires_greater s u
  · intro h
    intro heq
    have hnew := (waveD_d23_greater_replaces s u h).1
    rw [heq] at hnew
    have hlen := congrArg List.length hnew
    simp only [List.length_cons] at hlen
    omega

/-- A strictly newer update makes every older-or-equal subsequent update a
no-op: an older timestamp cannot overwrite the newer one. -/
theorem waveD_d23_older_after_newer_noop (s : GossipState)
    (u v : ChannelUpdate) (h : v.timestamp ≤ u.timestamp) :
    (s.applyUpdate u).applyUpdate v = s.applyUpdate u := by
  apply GossipState.applyUpdate_stale
  rw [waveD_d23_applyUpdate_clock_eq_max]
  exact Nat.le_trans h (Nat.le_max_right _ _)

/-- If an older-or-equal update `v` is already stored, then `u` with
`u.timestamp ≤ v.timestamp` is a no-op on the store. -/
theorem waveD_d23_older_than_stored_noop (s : GossipState)
    (u v : ChannelUpdate) (hv : v ∈ s.updates)
    (h : u.timestamp ≤ v.timestamp) :
    s.applyUpdate u = s := by
  apply GossipState.applyUpdate_stale
  exact Nat.le_trans h (mem_timestamp_le_latest hv)

/-- The global store clock can advance for an update on a *different*
channel, because `GossipState` keeps one global clock rather than one per
`(short_channel_id, direction)`.  This is a documented model weakness; it
does not weaken the timestamp replacement rule. -/
theorem waveD_d23_other_channel_advances_store_clock
    (s : GossipState) (u : ChannelUpdate)
    (h : s.latestUpdateTimestamp < u.timestamp) :
    s.latestUpdateTimestamp < (s.applyUpdate u).latestUpdateTimestamp :=
  (waveD_d23_clock_advances_iff s u).mpr h

/-! ## The per-channel replacement rule -/

/-- **Per-channel clock monotonicity.**  A view's timestamp never
decreases. -/
theorem waveD_d23_view_clock_monotone (v : ChannelView)
    (u : ChannelUpdate) :
    v.timestamp ≤ (v.applyUpdate u).timestamp :=
  ChannelView.applyUpdate_timestamp_ge v u

/-- **Per-channel replacement requires a greater timestamp.**  If applying
`u` changes the channel view, then `u.timestamp` is strictly greater than
the view's stored timestamp. -/
theorem waveD_d23_view_replace_requires_greater (v : ChannelView)
    (u : ChannelUpdate) (h : v.applyUpdate u ≠ v) :
    v.timestamp < u.timestamp := by
  by_cases hle : u.timestamp ≤ v.timestamp
  · exact absurd (ChannelView.applyUpdate_stale v u hle) h
  · exact Nat.lt_of_not_le hle

/-- **A matched, strictly newer update replaces the view.** -/
theorem waveD_d23_view_newer_replaces (v : ChannelView)
    (u : ChannelUpdate) (hscid : v.scid = u.shortChannelId)
    (h : v.timestamp < u.timestamp) :
    v.applyUpdate u ≠ v := by
  intro heq
  have hts := ChannelView.applyUpdate_newer_timestamp v u hscid h
  rw [heq] at hts
  rw [hts] at h
  exact Nat.lt_irrefl _ h

/-- **Exact per-channel replacement rule.**  A view is replaced iff the
update names the same channel and has a strictly greater timestamp. -/
theorem waveD_d23_view_replacement_iff (v : ChannelView)
    (u : ChannelUpdate) :
    v.applyUpdate u ≠ v ↔
      v.scid = u.shortChannelId ∧ v.timestamp < u.timestamp := by
  constructor
  · intro hne
    by_cases hguard : v.scid = u.shortChannelId ∧ v.timestamp < u.timestamp
    · exact hguard
    · exact absurd (ChannelView.applyUpdate_self_of_not v u hguard) hne
  · rintro ⟨hscid, hlt⟩
    exact waveD_d23_view_newer_replaces v u hscid hlt

/-- **Per-channel clock advances iff the update is newer on that channel.** -/
theorem waveD_d23_view_clock_advances_iff (v : ChannelView)
    (u : ChannelUpdate) :
    v.timestamp < (v.applyUpdate u).timestamp ↔
      v.scid = u.shortChannelId ∧ v.timestamp < u.timestamp := by
  constructor
  · intro h
    have hne : v.applyUpdate u ≠ v := by
      intro heq
      rw [heq] at h
      exact Nat.lt_irrefl _ h
    exact (waveD_d23_view_replacement_iff v u).mp hne
  · rintro ⟨hscid, hlt⟩
    rw [ChannelView.applyUpdate_newer_timestamp v u hscid hlt]
    exact hlt

/-- **Stale updates do not replace a channel view.** -/
theorem waveD_d23_view_older_noop (v : ChannelView) (u : ChannelUpdate)
    (h : u.timestamp ≤ v.timestamp) :
    v.applyUpdate u = v :=
  ChannelView.applyUpdate_stale v u h

/-- Once a newer update has been applied to a view, an older-or-equal
update is a no-op. -/
theorem waveD_d23_view_older_after_newer_noop (v : ChannelView)
    (u w : ChannelUpdate) (hscid : v.scid = u.shortChannelId)
    (hnew : v.timestamp < u.timestamp)
    (h : w.timestamp ≤ u.timestamp) :
    (v.applyUpdate u).applyUpdate w = v.applyUpdate u := by
  apply ChannelView.applyUpdate_stale
  rw [ChannelView.applyUpdate_newer_timestamp v u hscid hnew]
  exact h

/-- With a matching `short_channel_id`, the view clock after `applyUpdate`
is exactly `max oldClock u.timestamp`.  (Without the match the update is a
no-op, so a global `max` would be wrong per channel.) -/
theorem waveD_d23_view_clock_eq_max_of_scid (v : ChannelView)
    (u : ChannelUpdate) (hscid : v.scid = u.shortChannelId) :
    (v.applyUpdate u).timestamp = max v.timestamp u.timestamp := by
  unfold ChannelView.applyUpdate
  split
  · rename_i h
    change u.timestamp = max v.timestamp u.timestamp
    exact (Nat.max_eq_right (Nat.le_of_lt h.2)).symm
  · rename_i h
    have hle : u.timestamp ≤ v.timestamp := by
      by_cases hlt : v.timestamp < u.timestamp
      · exact absurd ⟨hscid, hlt⟩ h
      · exact Nat.le_of_not_lt hlt
    change v.timestamp = max v.timestamp u.timestamp
    exact (Nat.max_eq_left hle).symm

end LnLean.Proofs.WaveD.D23
