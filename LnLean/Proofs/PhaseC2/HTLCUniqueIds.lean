import LnLean.Channel.HTLCLaws

/-!
# LnLean.Proofs.PhaseC2.HTLCUniqueIds

English claim.  BOLT 2 gives every `update_add_htlc` a 64-bit `id`; a node
MUST NOT reuse an id within one channel, and an id is unique within the
channel's live HTLC set.  This module proves the list-level id laws of the
model in `LnLean.Channel.HTLC`:

* if all ids in a list of `HTLCRecord`s are pairwise distinct, then consing a
  record whose id is *fresh* (does not occur in the list) preserves
  `List.Nodup` of the id sequence; freshness is stated explicitly and is also
  shown to be *necessary* (a duplicate id breaks `Nodup`);
* removing every record with a given id preserves `List.Nodup` of ids, both in
  the full list and in the live subset `htlcSet`; after the removal the id does
  not occur at all, so it is free for a later *explicit* add;
* once an id is absent from the live set, no sequence of list updates
  consisting of removals and record additions can make it live again unless
  one of those updates is an explicit `add` of a record carrying that id;
* the model's unchecked `addHTLC` does not inspect the existing id set, so a
  checked wrapper `addHTLCChecked` is provided: it rejects an id already
  present and otherwise conses the record produced by `addHTLC`.  A successful
  checked add preserves `List.Nodup` of ids, and hence keeps the live-set ids
  pairwise distinct (catalogue claim `LN-HT-004`).

BOLT sections.
* BOLT 2 §Adding an HTLC (`update_add_htlc`):
  `refs/bolts/02-peer-protocol.md:2772` (the message fields, including `id`),
  `:2783` (message type).
* BOLT 2 §Removing an HTLC (`update_fulfill_htlc` / `update_fail_htlc`):
  `refs/bolts/02-peer-protocol.md:2913`; removal of the settled record frees
  its id (`:2944` covers `update_fail_htlc`).

rust-lightning anchors (pinned commit `fe49009`).
* `lightning/src/ln/channel.rs:8370` (`update_add_htlc` handling; the id check
  lives next to the amount and CLTV checks).
* `lightning/src/ln/chan_utils.rs:716` (`HTLCOutputInCommitment`, the
  commitment-level view of an HTLC).

What is explicitly NOT modelled.
* No wire encoding of the `id` counter, no per-direction counter split, and no
  `channel_update` retransmission semantics.  An id is just a `Nat`, and
  decidable equality on it is the only structure used.
* The model's `addHTLC` takes no existing list, so uniqueness cannot be a
  theorem about `addHTLC` alone.  The checked wrapper is a proof-level list
  operation; it does not change `LnLean.Channel.HTLC`.
* The update script `Op` records only `add` (cons) and `remove` (filter by
  id).  In-place state changes (`fulfillHTLC`, `failHTLC`, `timeoutHTLC`,
  `removeHTLC`) are treated as the removal of a record from the live set: this
  module proves that a removed id is absent, but does not model the list
  replacement that performs an in-place settlement (that belongs to
  `LnLean.Proofs.Channel.HTLCProps` and the commitment modules).
* No linearity or resource bound: the number of adds is unbounded, so id
  exhaustion/reuse after `2^64` updates is out of scope.
-/

namespace LnLean.Proofs.PhaseC2.HTLCUniqueIds

open LnLean LnLean.Channel

set_option autoImplicit false

/-! ## Id sequences and freshness -/

/-- The BOLT 2 `id` sequence of a list of HTLCs, in list order. -/
def ids (hs : List HTLCRecord) : List Nat := hs.map HTLCRecord.id

/-- All ids in the full HTLC list (live and settled) are pairwise distinct. -/
def idsNodup (hs : List HTLCRecord) : Prop := (ids hs).Nodup

/-- The ids of the live HTLCs, i.e. of `htlcSet hs`. -/
def liveIds (hs : List HTLCRecord) : List Nat := (htlcSet hs).map HTLCRecord.id

/-- The ids of the live HTLC set are pairwise distinct (`LN-HT-004`). -/
def liveIdsNodup (hs : List HTLCRecord) : Prop := (liveIds hs).Nodup

/-- Freshness precondition: the record's id does not occur in the list. -/
def FreshId (h : HTLCRecord) (hs : List HTLCRecord) : Prop := h.id ∉ ids hs

/-- A record is fresh for the *live* set when its id is not live. -/
def FreshLiveId (h : HTLCRecord) (hs : List HTLCRecord) : Prop := h.id ∉ liveIds hs

/-- List-level `update_add_htlc` acceptance: cons the record. -/
def addToSet (h : HTLCRecord) (hs : List HTLCRecord) : List HTLCRecord := h :: hs

/-- List-level removal: drop every record carrying `id` (whether live or
settled).  Removing an absent id is the identity. -/
def removeById (id : Nat) (hs : List HTLCRecord) : List HTLCRecord :=
  hs.filter (fun x => decide (x.id ≠ id))

@[simp] theorem ids_nil : ids [] = [] := rfl

@[simp] theorem ids_cons (h : HTLCRecord) (hs : List HTLCRecord) :
    ids (h :: hs) = h.id :: ids hs := rfl

theorem mem_ids_iff (x : Nat) (hs : List HTLCRecord) :
    x ∈ ids hs ↔ ∃ h ∈ hs, h.id = x := by
  unfold ids
  exact List.mem_map

theorem id_mem_ids_self (h : HTLCRecord) (hs : List HTLCRecord) (hm : h ∈ hs) :
    h.id ∈ ids hs :=
  (mem_ids_iff h.id hs).2 ⟨h, hm, rfl⟩

/-- The freshness precondition, unfolded to a pointwise form. -/
theorem freshId_iff (h : HTLCRecord) (hs : List HTLCRecord) :
    FreshId h hs ↔ ∀ x ∈ hs, x.id ≠ h.id := by
  unfold FreshId
  rw [mem_ids_iff]
  constructor
  · rintro hnot x hx heq
    exact hnot ⟨x, hx, heq⟩
  · rintro hne ⟨x, hx, heq⟩
    · exact hne x hx heq

/-- Freshness is exactly absence from the full id list, restated for a bare
id. -/
theorem not_mem_ids_iff (id : Nat) (hs : List HTLCRecord) :
    id ∉ ids hs ↔ ∀ x ∈ hs, x.id ≠ id := by
  rw [mem_ids_iff]
  constructor
  · rintro hnot x hx heq
    exact hnot ⟨x, hx, heq⟩
  · rintro hne ⟨x, hx, heq⟩
    exact hne x hx heq

/-! ## Adding a fresh record preserves id distinctness -/

theorem idsNodup_cons_iff (h : HTLCRecord) (hs : List HTLCRecord) :
    idsNodup (h :: hs) ↔ FreshId h hs ∧ idsNodup hs := by
  unfold idsNodup FreshId
  rw [ids_cons, List.nodup_cons]

/-- The freshness precondition is necessary as well as sufficient: an add
preserves `Nodup` exactly when the added id is fresh. -/
theorem idsNodup_add_iff (h : HTLCRecord) (hs : List HTLCRecord) :
    idsNodup (addToSet h hs) ↔ FreshId h hs ∧ idsNodup hs := by
  unfold addToSet
  exact idsNodup_cons_iff h hs

/-- Adding an HTLC with an id not already present preserves `List.Nodup` of
ids.  This is the main add law; the freshness premise is explicit. -/
theorem idsNodup_add (h : HTLCRecord) (hs : List HTLCRecord)
    (hnd : idsNodup hs) (hfresh : FreshId h hs) :
    idsNodup (addToSet h hs) :=
  (idsNodup_add_iff h hs).2 ⟨hfresh, hnd⟩

/-- Conversely, if the extended list has distinct ids, the added id was fresh. -/
theorem freshId_of_idsNodup_add (h : HTLCRecord) (hs : List HTLCRecord)
    (hnd : idsNodup (addToSet h hs)) : FreshId h hs :=
  ((idsNodup_add_iff h hs).1 hnd).1

/-- Re-adding an id already present necessarily destroys `List.Nodup`: the
freshness premise cannot be dropped. -/
theorem add_duplicate_breaks_idsNodup (h : HTLCRecord) (hs : List HTLCRecord)
    (hmem : h.id ∈ ids hs) : ¬ idsNodup (addToSet h hs) := by
  intro hnd
  exact (((idsNodup_add_iff h hs).1 hnd).1) hmem

theorem liveIds_cons_live (h : HTLCRecord) (hs : List HTLCRecord)
    (hl : h.isLive = true) : liveIds (h :: hs) = h.id :: liveIds hs := by
  unfold liveIds htlcSet
  simp [hl]

/-- Adding a record with a live-fresh id keeps the ids of the live set
pairwise distinct.  Freshness relative to the *live* set is required: a record
whose id is already live but settled (or a non-live record duplicated) would
otherwise violate the claim. -/
theorem liveIdsNodup_add (h : HTLCRecord) (hs : List HTLCRecord)
    (hnd : liveIdsNodup hs) (hfresh : FreshLiveId h hs) :
    liveIdsNodup (addToSet h hs) := by
  unfold liveIdsNodup at hnd ⊢
  unfold addToSet
  by_cases hl : h.isLive = true
  · rw [liveIds_cons_live h hs hl]
    exact List.nodup_cons.2 ⟨hfresh, hnd⟩
  · have hf : h.isLive = false := by
      cases hb : h.isLive <;> simp_all
    unfold liveIds htlcSet at hnd ⊢
    simp [hf]
    exact hnd

/-! ## Removal preserves id distinctness and frees the id -/

theorem mem_removeById_iff (x : HTLCRecord) (id : Nat) (hs : List HTLCRecord) :
    x ∈ removeById id hs ↔ x ∈ hs ∧ x.id ≠ id := by
  unfold removeById
  rw [List.mem_filter]
  simp

theorem ids_removeById (id : Nat) (hs : List HTLCRecord) :
    ids (removeById id hs) = (ids hs).filter (fun x => decide (x ≠ id)) := by
  unfold ids removeById
  induction hs with
  | nil => rfl
  | cons h t ih =>
      by_cases hid : h.id = id
      · simpa [hid, decide_not] using ih
      · simpa [hid, decide_not] using ih

/-- Removing an id preserves `List.Nodup` of the remaining ids. -/
theorem idsNodup_removeById (id : Nat) (hs : List HTLCRecord)
    (hnd : idsNodup hs) : idsNodup (removeById id hs) := by
  unfold idsNodup
  rw [ids_removeById]
  exact hnd.filter (fun x => decide (x ≠ id))

/-- After `removeById`, the removed id is absent from the full id list. -/
theorem id_not_mem_ids_removeById (id : Nat) (hs : List HTLCRecord) :
    id ∉ ids (removeById id hs) := by
  rw [ids_removeById]
  simp

/-- Removal only deletes ids; it never introduces one. -/
theorem mem_ids_removeById_of_mem {id x : Nat} {hs : List HTLCRecord}
    (hm : x ∈ ids (removeById id hs)) : x ∈ ids hs := by
  obtain ⟨h, hh, hid⟩ := (mem_ids_iff x (removeById id hs)).1 hm
  exact (mem_ids_iff x hs).2 ⟨h, (mem_removeById_iff h id hs).1 hh |>.1, hid⟩

/-! ## The live set -/

theorem mem_liveIds_iff (x : Nat) (hs : List HTLCRecord) :
    x ∈ liveIds hs ↔ ∃ h ∈ htlcSet hs, h.id = x := by
  unfold liveIds
  exact List.mem_map

/-- Every live id is an id of the full list. -/
theorem liveIds_subset_ids {x : Nat} {hs : List HTLCRecord}
    (hm : x ∈ liveIds hs) : x ∈ ids hs := by
  obtain ⟨h, hh, hid⟩ := (mem_liveIds_iff x hs).1 hm
  exact (mem_ids_iff x hs).2 ⟨h, (List.mem_filter.mp hh).1, hid⟩

theorem liveIdsNodup_of_idsNodup (hs : List HTLCRecord)
    (hnd : idsNodup hs) : liveIdsNodup hs := by
  unfold liveIdsNodup liveIds idsNodup ids htlcSet at *
  exact (List.filter_sublist.map HTLCRecord.id).nodup hnd

theorem htlcSet_removeById_comm (id : Nat) (hs : List HTLCRecord) :
    htlcSet (removeById id hs) = removeById id (htlcSet hs) := by
  unfold htlcSet removeById
  rw [List.filter_filter, List.filter_filter]
  congr 1
  funext x
  exact Bool.and_comm _ _

theorem liveIds_removeById (id : Nat) (hs : List HTLCRecord) :
    liveIds (removeById id hs) =
      (liveIds hs).filter (fun x => decide (x ≠ id)) := by
  unfold liveIds
  rw [htlcSet_removeById_comm]
  exact ids_removeById id (htlcSet hs)

/-- Removing an id preserves distinctness of the live ids. -/
theorem liveIdsNodup_removeById (id : Nat) (hs : List HTLCRecord)
    (hnd : liveIdsNodup hs) : liveIdsNodup (removeById id hs) := by
  unfold liveIdsNodup
  rw [liveIds_removeById]
  exact List.filter_sublist.nodup hnd

/-- Removal only deletes live ids; it never introduces one. -/
theorem mem_liveIds_removeById_of_mem {id x : Nat} {hs : List HTLCRecord}
    (hm : x ∈ liveIds (removeById id hs)) : x ∈ liveIds hs := by
  unfold liveIds at *
  rw [htlcSet_removeById_comm] at hm
  obtain ⟨h, hh, hid⟩ := List.mem_map.1 hm
  exact List.mem_map.2
    ⟨h, (mem_removeById_iff h id (htlcSet hs)).1 hh |>.1, hid⟩

/-- After `removeById`, the removed id is absent from the live ids. -/
theorem id_not_mem_liveIds_removeById (id : Nat) (hs : List HTLCRecord) :
    id ∉ liveIds (removeById id hs) := by
  intro hm
  obtain ⟨h, hmem, hid⟩ := (mem_liveIds_iff id (removeById id hs)).1 hm
  have hx : h ∈ removeById id hs := (List.mem_filter.mp hmem).1
  exact (mem_removeById_iff h id hs).1 hx |>.2 hid

/-! ## Update scripts: an id can only reappear through an explicit add -/

/-- One list-level update in the model's vocabulary: accept a record (cons),
or remove every record with an id. -/
inductive Op where
  | add (h : HTLCRecord)
  | remove (id : Nat)
deriving Repr

/-- Apply one update to an HTLC list. -/
def applyOp (op : Op) (hs : List HTLCRecord) : List HTLCRecord :=
  match op with
  | .add h => addToSet h hs
  | .remove id => removeById id hs

/-- Apply a finite script of updates, left to right. -/
def applyOps (ops : List Op) (hs : List HTLCRecord) : List HTLCRecord :=
  ops.foldl (fun acc op => applyOp op acc) hs

@[simp] theorem applyOps_nil (hs : List HTLCRecord) : applyOps [] hs = hs := rfl

theorem applyOps_cons (op : Op) (ops : List Op) (hs : List HTLCRecord) :
    applyOps (op :: ops) hs = applyOps ops (applyOp op hs) := rfl

/-- An id absent from the starting full id list can only occur after a script
of updates if some update in the script is an explicit `add` of a record with
that id. -/
theorem mem_ids_applyOps_requires_add {id : Nat} {hs : List HTLCRecord}
    {ops : List Op} (hnot : id ∉ ids hs) (hmem : id ∈ ids (applyOps ops hs)) :
    ∃ op ∈ ops, ∃ h : HTLCRecord, op = .add h ∧ h.id = id := by
  induction ops generalizing hs with
  | nil => exact absurd hmem hnot
  | cons op ops ih =>
      rw [applyOps_cons] at hmem
      cases op with
      | add h =>
          by_cases hid : h.id = id
          · exact ⟨.add h, by simp, h, rfl, hid⟩
          · have hnot' : id ∉ ids (h :: hs) := by
              intro hm
              rw [ids_cons] at hm
              rcases List.mem_cons.mp hm with heq | hmem'
              · exact hid heq.symm
              · exact hnot hmem'
            obtain ⟨o, ho, h', hoh, hid'⟩ := ih hnot' hmem
            exact ⟨o, List.mem_cons_of_mem _ ho, h', hoh, hid'⟩
      | remove rid =>
          have hnot' : id ∉ ids (removeById rid hs) := by
            intro hm
            exact hnot (mem_ids_removeById_of_mem hm)
          obtain ⟨o, ho, h', hoh, hid'⟩ := ih hnot' hmem
          exact ⟨o, List.mem_cons_of_mem _ ho, h', hoh, hid'⟩

/-- Live-level form: if every added record is live, an id absent from the live
ids of the starting list can reappear in the live set only via an explicit add
of a live record carrying that id. -/
theorem mem_liveIds_applyOps_requires_add {id : Nat} {hs : List HTLCRecord}
    {ops : List Op}
    (hlive : ∀ op ∈ ops, ∀ h : HTLCRecord, op = .add h → h.isLive = true)
    (hnot : id ∉ liveIds hs) (hmem : id ∈ liveIds (applyOps ops hs)) :
    ∃ op ∈ ops, ∃ h : HTLCRecord, op = .add h ∧ h.id = id := by
  induction ops generalizing hs with
  | nil => exact absurd hmem hnot
  | cons op ops ih =>
      rw [applyOps_cons] at hmem
      cases op with
      | add h =>
          have hh_live : h.isLive = true := hlive _ (by simp) h rfl
          by_cases hid : h.id = id
          · exact ⟨.add h, by simp, h, rfl, hid⟩
          · have hnot' : id ∉ liveIds (h :: hs) := by
              intro hm
              rw [liveIds_cons_live h hs hh_live] at hm
              rcases List.mem_cons.mp hm with heq | hmem'
              · exact hid heq.symm
              · exact hnot hmem'
            obtain ⟨o, ho, h', hoh, hid'⟩ :=
              ih (fun o ho h hoh => hlive o (List.mem_cons_of_mem _ ho) h hoh)
                hnot' hmem
            exact ⟨o, List.mem_cons_of_mem _ ho, h', hoh, hid'⟩
      | remove rid =>
          have hnot' : id ∉ liveIds (removeById rid hs) := by
            intro hm
            exact hnot (mem_liveIds_removeById_of_mem hm)
          obtain ⟨o, ho, h', hoh, hid'⟩ :=
            ih (fun o ho h hoh => hlive o (List.mem_cons_of_mem _ ho) h hoh)
              hnot' hmem
          exact ⟨o, List.mem_cons_of_mem _ ho, h', hoh, hid'⟩

/-- Corollary: a script that never adds the id keeps the id out of the full id
list. -/
theorem id_not_mem_ids_applyOps_of_no_add {id : Nat} {hs : List HTLCRecord}
    {ops : List Op}
    (hno : ∀ op ∈ ops, ∀ h : HTLCRecord, op = .add h → h.id ≠ id)
    (hnot : id ∉ ids hs) : id ∉ ids (applyOps ops hs) := by
  intro hmem
  obtain ⟨op, hop, h, hoh, hid⟩ := mem_ids_applyOps_requires_add hnot hmem
  exact (hno op hop h hoh) hid

/-- The mission's non-reuse statement: after removing an id from the list, no
script of updates that never explicitly adds that id can make it live again. -/
theorem removed_id_no_reappearance (id : Nat) (hs : List HTLCRecord)
    (ops : List Op)
    (hno : ∀ op ∈ ops, ∀ h : HTLCRecord, op = .add h → h.id ≠ id) :
    id ∉ liveIds (applyOps ops (removeById id hs)) := by
  intro hmem
  exact id_not_mem_ids_applyOps_of_no_add hno
    (id_not_mem_ids_removeById id hs) (liveIds_subset_ids hmem)

/-! ## A checked `addHTLC` wrapper -/

/-- Accept `update_add_htlc` against the current list: the id must be fresh
(the model's `addHTLC` itself takes no list), and the model transition must
succeed.  On success the new record is consed. -/
def addHTLCChecked (maxHtlcValue currentTotal : Msat) (id : Nat)
    (dir : Direction) (amount : Msat) (ph : PaymentHash) (cltv : Height)
    (hs : List HTLCRecord) : Result (List HTLCRecord) :=
  if id ∈ ids hs then
    .error ⟨.update, ByteArray.empty⟩
  else
    (addHTLC maxHtlcValue currentTotal id dir amount ph cltv).map
      (fun h => h :: hs)

/-- A successful checked add had a fresh id. -/
theorem addHTLCChecked_fresh (maxHtlcValue currentTotal : Msat) (id : Nat)
    (dir : Direction) (amount : Msat) (ph : PaymentHash) (cltv : Height)
    (hs hs' : List HTLCRecord)
    (ok : addHTLCChecked maxHtlcValue currentTotal id dir amount ph cltv hs = .ok hs') :
    id ∉ ids hs := by
  unfold addHTLCChecked at ok
  split at ok
  · simp at ok
  · assumption

/-- The checked wrapper rejects a duplicate id without consulting `addHTLC`. -/
theorem addHTLCChecked_rejects_duplicate (maxHtlcValue currentTotal : Msat)
    (id : Nat) (dir : Direction) (amount : Msat) (ph : PaymentHash)
    (cltv : Height) (hs : List HTLCRecord) (hmem : id ∈ ids hs) :
    addHTLCChecked maxHtlcValue currentTotal id dir amount ph cltv hs =
      .error ⟨.update, ByteArray.empty⟩ := by
  unfold addHTLCChecked
  simp [hmem]

/-- A successful unchecked `addHTLC` builds a record whose id is exactly the
requested id, so the checked wrapper can compare it against the freshness
guard. -/
theorem addHTLC_id (maxHtlcValue currentTotal : Msat) (id : Nat)
    (dir : Direction) (amount : Msat) (ph : PaymentHash) (cltv : Height)
    (h : HTLCRecord)
    (ok : addHTLC maxHtlcValue currentTotal id dir amount ph cltv = .ok h) :
    h.id = id := by
  unfold addHTLC at ok
  split at ok
  · simp only [Result.ok.injEq] at ok
    subst ok
    rfl
  · simp at ok

/-- If the model's add succeeds and the id is fresh, the checked add succeeds
and conses the new record. -/
theorem addHTLCChecked_ok (maxHtlcValue currentTotal : Msat) (id : Nat)
    (dir : Direction) (amount : Msat) (ph : PaymentHash) (cltv : Height)
    (h : HTLCRecord) (hs : List HTLCRecord) (hnot : id ∉ ids hs)
    (ok : addHTLC maxHtlcValue currentTotal id dir amount ph cltv = .ok h) :
    addHTLCChecked maxHtlcValue currentTotal id dir amount ph cltv hs = .ok (h :: hs) := by
  unfold addHTLCChecked
  simp [hnot, ok, Result.map]

/-- Exact success characterization of the checked wrapper. -/
theorem addHTLCChecked_sound (maxHtlcValue currentTotal : Msat) (id : Nat)
    (dir : Direction) (amount : Msat) (ph : PaymentHash) (cltv : Height)
    (hs hs' : List HTLCRecord)
    (ok : addHTLCChecked maxHtlcValue currentTotal id dir amount ph cltv hs = .ok hs') :
    id ∉ ids hs ∧ ∃ h : HTLCRecord,
      addHTLC maxHtlcValue currentTotal id dir amount ph cltv = .ok h ∧
        hs' = h :: hs := by
  unfold addHTLCChecked at ok
  split at ok
  · simp at ok
  · rename_i hnot
    refine ⟨hnot, ?_⟩
    cases hres : addHTLC maxHtlcValue currentTotal id dir amount ph cltv with
    | ok h =>
        rw [hres] at ok
        simp only [Result.map, Result.ok.injEq] at ok
        exact ⟨h, rfl, ok.symm⟩
    | error e =>
        rw [hres] at ok
        simp [Result.map] at ok

/-- The checked add preserves `List.Nodup` of ids: this is the freshness law
for the model's `addHTLC`, with the freshness obligation discharged by the
wrapper's guard. -/
theorem addHTLCChecked_idsNodup (maxHtlcValue currentTotal : Msat) (id : Nat)
    (dir : Direction) (amount : Msat) (ph : PaymentHash) (cltv : Height)
    (hs hs' : List HTLCRecord) (hnd : idsNodup hs)
    (ok : addHTLCChecked maxHtlcValue currentTotal id dir amount ph cltv hs = .ok hs') :
    idsNodup hs' := by
  obtain ⟨hnot, h, hok, rfl⟩ :=
    addHTLCChecked_sound maxHtlcValue currentTotal id dir amount ph cltv hs hs' ok
  have hfresh : FreshId h hs := by
    unfold FreshId
    rwa [addHTLC_id maxHtlcValue currentTotal id dir amount ph cltv h hok]
  exact idsNodup_add h hs hnd hfresh

/-- Consequently a successful checked add keeps the live-set ids pairwise
distinct (`LN-HT-004`, relative to an already distinct list). -/
theorem addHTLCChecked_liveIdsNodup (maxHtlcValue currentTotal : Msat) (id : Nat)
    (dir : Direction) (amount : Msat) (ph : PaymentHash) (cltv : Height)
    (hs hs' : List HTLCRecord) (hnd : idsNodup hs)
    (ok : addHTLCChecked maxHtlcValue currentTotal id dir amount ph cltv hs = .ok hs') :
    liveIdsNodup hs' :=
  liveIdsNodup_of_idsNodup hs'
    (addHTLCChecked_idsNodup maxHtlcValue currentTotal id dir amount ph cltv hs hs' hnd ok)

/-! ## `removeHTLC` keeps the id, so settlement does not recycle it silently -/

/-- A settled record removed by the model transition keeps its BOLT 2 id; the
transition changes the lifecycle state only. -/
theorem removeHTLC_id (h h' : HTLCRecord) (ok : removeHTLC h = .ok h') :
    h'.id = h.id := by
  rw [removeHTLC_ok_state h h' ok]

/-- A removed record is not live, hence absent from `htlcSet`. -/
theorem removeHTLC_not_live (h h' : HTLCRecord) (ok : removeHTLC h = .ok h') :
    h'.isLive = false := by
  rw [removeHTLC_ok_state h h' ok]
  simp [HTLCRecord.isLive]

/-! ## Checked counterexample: the unchecked model cannot enforce freshness -/

/-- Concrete evidence that `addHTLC` performs no id check: two calls with the
same id both succeed in the model (the guard mentions only amount, in-flight
total, and CLTV).  Hence id uniqueness must be imposed by the caller, which is
what `addHTLCChecked` does. -/
theorem addHTLC_accepts_reused_id :
    (addHTLC ⟨1000⟩ ⟨0⟩ 7 .local ⟨1⟩ ⟨ByteArray.empty⟩ 0).isOk = true ∧
      (addHTLC ⟨1000⟩ ⟨0⟩ 7 .local ⟨1⟩ ⟨ByteArray.empty⟩ 0).isOk = true :=
  ⟨rfl, rfl⟩

/-- Two copies of the same record do not have distinct ids. -/
theorem duplicate_record_not_idsNodup (r : HTLCRecord) :
    ¬ idsNodup (r :: r :: []) := by
  intro hnd
  have hmem : r.id ∈ ids [r] := by
    exact id_mem_ids_self r [r] (by simp)
  exact (add_duplicate_breaks_idsNodup r [r] hmem) hnd

end LnLean.Proofs.PhaseC2.HTLCUniqueIds
