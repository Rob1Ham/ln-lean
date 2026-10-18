import LnLean.Channel.HTLC

/-!
# Channel-wide (direction-tagged) HTLC id uniqueness — `HT-01`

Catalog row `LN-HT-004` is the per-sender statement
`LnLean.Channel.HTLC.dir_id_unique`.  That is the faithful BOLT 2 wire-level
claim: `update_add_htlc.id` is allocated from one counter per sender, both
counters are `Nat` in `HtlcBook` (`nextLocalId`, `nextRemoteId`), and both start
at zero.  The literal channel-wide wording is therefore false for the bare
`HTLCRecord.id`: `HtlcBook.cross_direction_duplicate` is a reachable book whose
live ids are `[0, 0]`, and the conditional global form still needs
`HtlcBook.CrossDisjoint` (`HTLC.id_unique_of_reachable_cross`).

This module supplies the missing channel-wide namespace instead of assuming
cross-direction disjointness:

* `HTLCTag = Direction × Nat` and `HTLCRecord.tag r = (r.direction, r.id)` are
  defined additively in `LnLean.Channel.HTLC`;
* `HtlcBook.liveTags` is the tagged id list of the live HTLC set;
* `reachable_tagged_id_unique` proves that on every book built by the allocator
  a tagged id determines the live record, **with no `CrossDisjoint` premise**;
* `reachable_liveTags_nodup` proves the tagged list is pairwise distinct;
* `crossBook_duplicate_distinct_tags` exhibits the old duplicate pair (both
  id `0`, different directions) and proves their *tagged* ids differ;
* `cross_direction_duplicate_tagged` connects these facts to the retained
  counterexample: the same reachable book has `¬ liveHtlcIdsNodup` for the bare
  ids and `liveTags.Nodup` for the tagged ids.

## Why `Direction × Nat` and not a single `Nat`

The two counters are independent `Nat`s, so `(direction, id)` retains all the
information in the state; `tag_fst`/`tag_snd` show the projections.  The tag is
a *model-side namespace*, not a BOLT 2 wire encoding: BOLT 2 sends only the
per-sender `id`, and a receiver interprets it together with the message
direction.  A single-`Nat` encoding (for example `2 * id` for local and
`2 * id + 1` for remote) is also injective, but it is not part of the protocol
and would be an unnecessary re-encoding.  The pair is the faithful reading and
is used throughout.

The tag does not replace the per-sender counter API.  `HTLC.dir_id_unique`,
`HTLC.id_unique_of_reachable_cross`, `addHTLC`, `HtlcBook.allocate`,
`HtlcBook.insert`, and `HtlcBook.add` are unchanged.  `tagged_uniqueness_implies_dir_unique`
also shows that the tagged theorem recovers the per-sender one.

## Scope caveats

* This is a namespace view over the existing record fields.  It does not change
  the wire type, the counters, or the allocator.
* It does not claim that BOLT 2 ids are globally unique on the wire; they are
  not.  It claims that `(direction, id)` is a faithful channel-wide identifier,
  which is exactly the information a channel endpoint has.
* The uniqueness is over `HtlcBook.Reachable`, i.e. books constructed by
  `HtlcBook.insert` or a successful `HtlcBook.add`.  An arbitrary hand-built
  `HTLCRecord` list is still unconstrained, as before.
* `HTLCRecord` can be instantiated with a duplicate direction/id pair by a
  caller who bypasses the allocator; that is why the `Reachable` (or `WF`)
  hypothesis is not removable for this representation.
-/

namespace LnLean.Channel

open LnLean

set_option autoImplicit false

namespace HtlcBook

/-- **Channel-wide tagged id uniqueness over reachable books.**  In a book built
by the BOLT 2 allocator, two live records with the same direction-tagged id are
the same record.  There is no `CrossDisjoint` hypothesis: the direction
component of the tag supplies the cross-sender separation. -/
theorem reachable_tagged_id_unique {b : HtlcBook} (hb : b.Reachable) :
    ∀ r1 ∈ htlcSet b.records, ∀ r2 ∈ htlcSet b.records,
      r1.tag = r2.tag → r1 = r2 :=
  tagged_id_unique_of_wf b (reachable_wf hb)

/-- The live direction-tagged ids of every reachable book are pairwise
distinct.  This is the channel-wide replacement for
`liveIds_nodup_of_cross`, with no cross-direction assumption. -/
theorem reachable_liveTags_nodup {b : HtlcBook} (hb : b.Reachable) :
    b.liveTags.Nodup :=
  liveTags_nodup_of_wf b (reachable_wf hb)

/-- `HTLCRecord.tag` is injective on the live subtype of a reachable book.  This
is the function-level form of `reachable_tagged_id_unique`. -/
theorem reachable_tag_injective {b : HtlcBook} (hb : b.Reachable) :
    Function.Injective
      (fun r : {r : HTLCRecord // r ∈ htlcSet b.records} => r.1.tag) := by
  rintro ⟨r1, h1⟩ ⟨r2, h2⟩ htag
  exact Subtype.ext (reachable_tagged_id_unique hb r1 h1 r2 h2 htag)

/-- Tagged uniqueness implies per-sender id uniqueness.  Thus the new namespace
does not weaken the existing wire-level theorem: it is a strict refinement of
the information in the bare per-sender id. -/
theorem tagged_uniqueness_implies_dir_unique {b : HtlcBook}
    (h : ∀ r1 ∈ htlcSet b.records, ∀ r2 ∈ htlcSet b.records,
      r1.tag = r2.tag → r1 = r2) (dir : Direction) :
    ∀ r1 ∈ b.liveOf dir, ∀ r2 ∈ b.liveOf dir, r1.id = r2.id → r1 = r2 := by
  intro r1 h1 r2 h2 hid
  have hd1 : r1.direction = dir :=
    of_decide_eq_true (List.mem_filter.mp h1).2
  have hd2 : r2.direction = dir :=
    of_decide_eq_true (List.mem_filter.mp h2).2
  have htag : r1.tag = r2.tag := by
    rw [HTLCRecord.tag_eq_iff]
    exact ⟨by rw [hd1, hd2], hid⟩
  exact h r1 (List.mem_filter.mp h1).1 r2 (List.mem_filter.mp h2).1 htag

/-- The reachable form of `tagged_uniqueness_implies_dir_unique`: the tagged
theorem recovers `HTLC.dir_id_unique` without using an id-distinctness
hypothesis. -/
theorem reachable_dir_unique_via_tags {b : HtlcBook} (hb : b.Reachable)
    (dir : Direction) :
    ∀ r1 ∈ b.liveOf dir, ∀ r2 ∈ b.liveOf dir, r1.id = r2.id → r1 = r2 :=
  tagged_uniqueness_implies_dir_unique (reachable_tagged_id_unique hb) dir

/-! ### The whole record list of a reachable book

`HtlcBook` has no settle/remove operation: `insert` and `add` only prepend a
fresh live record.  Hence every record in a reachable book is live, and the
tagged uniqueness above can be read over `b.records` as well as over
`htlcSet b.records`.  This second form is the literal "every record in the
book has a globally unique tagged id" statement. -/

/-- Every record of a reachable book is live. -/
theorem reachable_all_live {b : HtlcBook} (hb : b.Reachable) :
    ∀ r ∈ b.records, r.isLive = true := by
  induction hb with
  | empty =>
      intro r hr
      simp [empty] at hr
  | insert hb dir amount ph cltv ih =>
      intro x hx
      unfold insert at hx
      rw [push_records] at hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact allocate_isLive _ dir amount ph cltv
      · exact ih x hx
  | add hb maxHtlcValue dir amount ph cltv ok ih =>
      intro x hx
      obtain ⟨r0, hadd, hb'⟩ := add_ok _ maxHtlcValue dir amount ph cltv _ ok
      rw [hb', push_records] at hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact addHTLC_isLive maxHtlcValue _ _ dir amount ph cltv x hadd
      · exact ih x hx

/-- In a reachable book the live set is the whole record list. -/
theorem reachable_htlcSet_eq_records {b : HtlcBook} (hb : b.Reachable) :
    htlcSet b.records = b.records :=
  List.filter_eq_self.mpr (reachable_all_live hb)

/-- The tagged ids of the entire record list of a reachable book are pairwise
distinct. -/
theorem reachable_taggedIds_nodup {b : HtlcBook} (hb : b.Reachable) :
    (taggedIds b.records).Nodup := by
  have h := reachable_liveTags_nodup hb
  unfold liveTags at h
  rwa [reachable_htlcSet_eq_records hb] at h

/-- Tagged id uniqueness over every record of a reachable book. -/
theorem reachable_tagged_id_unique_all {b : HtlcBook} (hb : b.Reachable) :
    ∀ r1 ∈ b.records, ∀ r2 ∈ b.records, r1.tag = r2.tag → r1 = r2 := by
  intro r1 h1 r2 h2 htag
  have hset := reachable_htlcSet_eq_records hb
  exact reachable_tagged_id_unique hb r1 (by rw [hset]; exact h1)
    r2 (by rw [hset]; exact h2) htag

/-! ### The retained cross-direction counterexample, seen through tags -/

/-- The live tagged ids of `crossBook`: the remote record has id `0` and the
local record has id `0`, but the tags differ in their first component. -/
theorem crossBook_liveTags :
    crossBook.liveTags = [(Direction.remote, 0), (Direction.local, 0)] := by
  unfold HtlcBook.liveTags taggedIds
  rw [crossBook_records]
  decide

/-- The tagged ids of the counterexample book are pairwise distinct even though
its bare live ids are `[0, 0]`. -/
theorem crossBook_liveTags_nodup : crossBook.liveTags.Nodup := by
  rw [crossBook_liveTags]
  decide

/-- **The old duplicate becomes two distinct tagged ids.**  `crossBook` contains
two distinct live records with the same bare id (`0`) and different directions;
their direction-tagged ids are distinct.  This is the local form of the repair:
the counterexample is preserved, not hidden. -/
theorem crossBook_duplicate_distinct_tags :
    ∃ r1 ∈ htlcSet crossBook.records, ∃ r2 ∈ htlcSet crossBook.records,
      r1 ≠ r2 ∧ r1.id = r2.id ∧ r1.tag ≠ r2.tag := by
  refine
    ⟨{ id := 0, direction := .remote, amountMsat := ⟨2000⟩,
        paymentHash := sampleHash, cltvExpiry := 600, state := .received },
     ?_,
     { id := 0, direction := .local, amountMsat := ⟨1000⟩,
        paymentHash := sampleHash, cltvExpiry := 500, state := .offered },
     ?_, ?_, rfl, ?_⟩
  · simp [crossBook_records, htlcSet, HTLCRecord.isLive, HTLCState.isLive]
  · simp [crossBook_records, htlcSet, HTLCRecord.isLive, HTLCState.isLive]
  · decide
  · decide

/-- `crossBook` does *not* satisfy the old `CrossDisjoint` premise: it is the
mechanized witness that per-sender counters do not imply it. -/
theorem crossBook_not_crossDisjoint : ¬ crossBook.CrossDisjoint := by
  intro hc
  have h := hc
    { id := 0, direction := .local, amountMsat := ⟨1000⟩,
      paymentHash := sampleHash, cltvExpiry := 500, state := .offered }
    (by simp [crossBook_records, htlcSet, HTLCRecord.isLive, HTLCState.isLive])
    { id := 0, direction := .remote, amountMsat := ⟨2000⟩,
      paymentHash := sampleHash, cltvExpiry := 600, state := .received }
    (by simp [crossBook_records, htlcSet, HTLCRecord.isLive, HTLCState.isLive])
    rfl rfl
  exact h rfl

/-- **The tagged repair and the old counterexample coexist.**  The same
well-formed book has a duplicate bare live id (the retained
`cross_direction_duplicate` fact) and pairwise distinct tagged live ids.
No `CrossDisjoint` assumption is used for the tagged half. -/
theorem cross_direction_duplicate_tagged :
    crossBook.WF ∧ ¬ liveHtlcIdsNodup crossBook.records ∧
      crossBook.liveTags.Nodup :=
  ⟨cross_direction_duplicate.1, cross_direction_duplicate.2,
    crossBook_liveTags_nodup⟩

/-- The counterexample with the duplicate pair made explicit. -/
theorem cross_direction_duplicate_tagged_pair :
    crossBook.WF ∧ ¬ liveHtlcIdsNodup crossBook.records ∧
      crossBook.liveTags.Nodup ∧
      (∃ r1 ∈ htlcSet crossBook.records, ∃ r2 ∈ htlcSet crossBook.records,
        r1 ≠ r2 ∧ r1.id = r2.id ∧ r1.tag ≠ r2.tag) :=
  ⟨cross_direction_duplicate.1, cross_direction_duplicate.2,
    crossBook_liveTags_nodup, crossBook_duplicate_distinct_tags⟩

/-- A reachable book whose bare ids are not globally unique but whose tagged ids
are.  This is the exact sense in which the direction-tagged namespace closes
`HT-01` without a `CrossDisjoint` assumption. -/
theorem reachable_cross_direction_duplicate_tagged :
    ∃ b : HtlcBook, b.Reachable ∧ ¬ liveHtlcIdsNodup b.records ∧
      b.liveTags.Nodup :=
  ⟨crossBook, crossBook_reachable, cross_direction_duplicate.2,
    crossBook_liveTags_nodup⟩

/-- The counterexample book is reachable, violates `CrossDisjoint`, and still
has pairwise distinct tagged ids.  This isolates the point of the tagged
namespace: `CrossDisjoint` is not needed once the sender is part of the id. -/
theorem tagged_namespace_without_cross :
    crossBook.Reachable ∧ ¬ crossBook.CrossDisjoint ∧
      crossBook.liveTags.Nodup :=
  ⟨crossBook_reachable, crossBook_not_crossDisjoint,
    crossBook_liveTags_nodup⟩

end HtlcBook

/-- The tag is deliberately not injective as a function on *all* records: it
forgets the amount, payment hash, expiry, and lifecycle state.  Injectivity is
a property of the live set of a reachable book, where allocation determines the
record's other fields (`HtlcBook.reachable_tagged_id_unique`).  This theorem
records the exact scope boundary rather than leaving it implicit. -/
theorem tag_not_injective_on_records :
    ¬ Function.Injective (HTLCRecord.tag : HTLCRecord → HTLCTag) := by
  intro hinj
  let a : HTLCRecord :=
    { id := 0, direction := .local, amountMsat := ⟨1⟩,
      paymentHash := ⟨ByteArray.empty⟩, cltvExpiry := 0, state := .offered }
  let b : HTLCRecord :=
    { id := 0, direction := .local, amountMsat := ⟨2⟩,
      paymentHash := ⟨ByteArray.empty⟩, cltvExpiry := 0, state := .offered }
  have htag : a.tag = b.tag := rfl
  have hab : a = b := hinj htag
  have hamt : a.amountMsat = b.amountMsat := congrArg HTLCRecord.amountMsat hab
  have hval : (1 : Nat) = 2 := by simpa [a, b] using congrArg Msat.val hamt
  omega

/-! ## Catalog-facing aliases -/

namespace HTLC

/-- Catalog-facing global form of `LN-HT-004`: in every book built by the BOLT 2
allocator, the direction-tagged id determines the live record.  No
`CrossDisjoint` premise. -/
theorem tagged_id_unique_of_reachable {b : HtlcBook} (hb : b.Reachable) :
    ∀ r1 ∈ htlcSet b.records, ∀ r2 ∈ htlcSet b.records,
      r1.tag = r2.tag → r1 = r2 :=
  HtlcBook.reachable_tagged_id_unique hb

/-- Catalog-facing global no-duplicate form: the live tagged ids of a reachable
book are pairwise distinct. -/
theorem tagged_ids_nodup_of_reachable {b : HtlcBook} (hb : b.Reachable) :
    b.liveTags.Nodup :=
  HtlcBook.reachable_liveTags_nodup hb

/-- Catalog-facing no-duplicate form over the whole record list of a reachable
book (the live set is the whole list there). -/
theorem tagged_ids_nodup_of_reachable_records {b : HtlcBook}
    (hb : b.Reachable) : (taggedIds b.records).Nodup :=
  HtlcBook.reachable_taggedIds_nodup hb

/-- Catalog-facing uniqueness form over every record of a reachable book. -/
theorem tagged_id_unique_of_reachable_records {b : HtlcBook}
    (hb : b.Reachable) :
    ∀ r1 ∈ b.records, ∀ r2 ∈ b.records, r1.tag = r2.tag → r1 = r2 :=
  HtlcBook.reachable_tagged_id_unique_all hb

/-- Catalog-facing counterexample connection: the old duplicate pair is two
distinct tagged ids. -/
theorem cross_direction_duplicate_distinct_tags :
    ∃ r1 ∈ htlcSet HtlcBook.crossBook.records,
      ∃ r2 ∈ htlcSet HtlcBook.crossBook.records,
        r1 ≠ r2 ∧ r1.id = r2.id ∧ r1.tag ≠ r2.tag :=
  HtlcBook.crossBook_duplicate_distinct_tags

/-- Catalog-facing coexistence theorem: bare-id non-uniqueness and tagged-id
uniqueness hold for the same reachable book. -/
theorem cross_direction_duplicate_tagged :
    HtlcBook.crossBook.WF ∧
      ¬ liveHtlcIdsNodup HtlcBook.crossBook.records ∧
        HtlcBook.crossBook.liveTags.Nodup :=
  HtlcBook.cross_direction_duplicate_tagged

end HTLC

end LnLean.Channel
