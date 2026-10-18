import LnLean.Channel.HTLC
import LnLean.Channel.HTLCLaws
import LnLean.Channel.Commitment
import LnLean.Channel.Revocation
import LnLean.Channel.Penalty
import LnLean.Channel.Types

/-!
# LnLean.Proofs.WaveD.D16

English claim (catalog `LN-HT-004`).  An HTLC id is unique within the live HTLC
set of a channel.

What the model actually provides.  `LnLean.Channel.HTLC` models one HTLCRecord
with a BOLT 2 `id : Nat`, and `htlcSet` filters a list of records down to the
live ones.  The transition `addHTLC` takes the `id` as a *caller-supplied*
argument and has no access to the channel's current HTLC set or to an id
counter, so it cannot by itself reject a repeated id.  The catalog claim is
therefore a channel-level invariant, not a theorem about `addHTLC` alone.

BOLT 2 §Adding an HTLC (`refs/bolts/02-peer-protocol.md:2838-2843`) supplies
exactly the missing discipline: "for the first HTLC it offers: MUST set `id` to
0.  MUST increase the value of `id` by 1 for each successive offer", and the
`id` MUST NOT be reset to 0 after `revoke_and_ack`.  These obligations are per
sender.  rust-lightning keeps two independent counters,
`next_holder_htlc_id` and `next_counterparty_htlc_id`
(`lightning/src/ln/channel.rs:3719-3720`), enforces
`next_counterparty_htlc_id == msg.htlc_id` on receipt
(`lightning/src/ln/channel.rs:8392`), and increments the matching counter when
the local side adds an HTLC (`lightning/src/ln/channel.rs:14670-14682`).

Consequences formalized below.

* Conditional global form: if the ids of the live HTLCs of a channel are
  pairwise distinct (`LiveIdsDistinct`), then a live HTLC is determined by its
  id (`waveD_d16_id_unique`).
* Per-sender form: the same uniqueness holds inside one direction, which is
  the shape actually guaranteed by the BOLT 2 counter rule
  (`waveD_d16_dir_id_unique`).
* Counter model: `HtlcBook` adds the two missing per-direction counters, and
  `waveD_d16_push_preserves_inv` proves that allocating at the counter and
  incrementing it preserves counter freshness and per-direction id
  distinctness (`waveD_d16_push_dir_id_unique`).
* Negative results: the unconditional global claim is false in the record
  model (`waveD_d16_id_unique_counterexample`) and is not implied by the BOLT 2
  per-sender rule, because both endpoints start their own counter at 0
  (`waveD_d16_bolt_allows_cross_direction_duplicate`).

BOLT anchors.
* BOLT 2 §Adding an HTLC: `refs/bolts/02-peer-protocol.md:2772` (message and
  `u64 id` field), `:2838-2843` (first id 0, increment by one, no reset).
* BOLT 2 §Removing an HTLC: `refs/bolts/02-peer-protocol.md:2913` (`id` keys the
  fulfill/fail message).

rust-lightning anchors (commit fe49009).
* `lightning/src/ln/channel.rs:8370` (`update_add_htlc` entry point).
* `lightning/src/ln/channel.rs:8392` (received id must equal the expected
  counterparty counter).
* `lightning/src/ln/channel.rs:14670-14682` (outgoing id taken from
  `next_holder_htlc_id`, then incremented).
* `lightning/src/ln/channel.rs:3719-3720` (the two independent counters).

Not modelled here: the channel ledger that owns the counters; wire framing of
`u64`; reconnection replay ("MUST ignore a repeated `id` value after a
reconnection"); and the case of a 64-bit counter wrap (excluded by the
BOLT 2 monotonicity rule for any realistic channel lifetime).
-/

namespace LnLean.Proofs.WaveD.D16

open LnLean LnLean.Channel

set_option autoImplicit false

/-! ## Live-id predicates -/

/-- The ids of the live HTLCs of a channel list, in list order. -/
def liveIds (hs : List HTLCRecord) : List Nat :=
  (htlcSet hs).map HTLCRecord.id

/-- The ids of the live HTLCs in one direction.  BOLT 2 assigns ids with one
monotone counter per sender, so this is the set over which the protocol rule
gives uniqueness. -/
def dirLiveSet (dir : Direction) (hs : List HTLCRecord) : List HTLCRecord :=
  (htlcSet hs).filter (fun h => decide (h.direction = dir))

def dirLiveIds (dir : Direction) (hs : List HTLCRecord) : List Nat :=
  (dirLiveSet dir hs).map HTLCRecord.id

/-- The live HTLC ids of the channel are pairwise distinct. -/
def LiveIdsDistinct (hs : List HTLCRecord) : Prop := (liveIds hs).Nodup

/-- The live HTLC ids of one direction are pairwise distinct. -/
def DirIdsDistinct (dir : Direction) (hs : List HTLCRecord) : Prop :=
  (dirLiveIds dir hs).Nodup

/-- Id uniqueness as a relational property: two live HTLCs with the same id are
the same record. -/
def LiveIdUnique (hs : List HTLCRecord) : Prop :=
  ∀ h1 ∈ htlcSet hs, ∀ h2 ∈ htlcSet hs, h1.id = h2.id → h1 = h2

/-- Id uniqueness restricted to one sender direction. -/
def DirIdUnique (dir : Direction) (hs : List HTLCRecord) : Prop :=
  ∀ h1 ∈ dirLiveSet dir hs, ∀ h2 ∈ dirLiveSet dir hs,
    h1.id = h2.id → h1 = h2

/-! ## The core list lemma -/

/-- If the ids of a list of records are distinct, then membership plus equality
of ids determines the record.  This is the combinatorial content of id
uniqueness; the channel-level theorems below instantiate it with `htlcSet` or
`dirLiveSet`. -/
theorem eq_of_id_eq_of_nodup {l : List HTLCRecord}
    (hnd : (l.map HTLCRecord.id).Nodup) :
    ∀ h1 ∈ l, ∀ h2 ∈ l, h1.id = h2.id → h1 = h2 := by
  induction l with
  | nil =>
      intro h1 hm1
      simp at hm1
  | cons x xs ih =>
      have hnd' : (x.id :: xs.map HTLCRecord.id).Nodup := by
        simpa using hnd
      have hx : x.id ∉ xs.map HTLCRecord.id := (List.nodup_cons.mp hnd').1
      have htail : (xs.map HTLCRecord.id).Nodup := (List.nodup_cons.mp hnd').2
      intro h1 hm1 h2 hm2 hid
      simp only [List.mem_cons] at hm1 hm2
      rcases hm1 with rfl | hm1
      · rcases hm2 with rfl | hm2
        · rfl
        · exact absurd (List.mem_map.mpr ⟨h2, hm2, hid.symm⟩) hx
      · rcases hm2 with rfl | hm2
        · exact absurd (List.mem_map.mpr ⟨h1, hm1, hid⟩) hx
        · exact ih htail h1 hm1 h2 hm2 hid

/-! ## Conditional id uniqueness (the faithful form of `LN-HT-004`) -/

-- OBLIGATION: LN-WD-D16

/-- **Catalog `LN-HT-004`, conditional form.**  If the live HTLC ids of a
channel are pairwise distinct, then every live HTLC is determined by its id.
The hypothesis `LiveIdsDistinct` is exactly the channel invariant that the
record model does not maintain by itself. -/
theorem waveD_d16_id_unique (hs : List HTLCRecord)
    (hnd : LiveIdsDistinct hs) : LiveIdUnique hs :=
  eq_of_id_eq_of_nodup hnd

/-- Per-direction form: uniqueness inside one sender's id space.  This is the
form guaranteed by BOLT 2's "increase `id` by 1 for each successive offer". -/
theorem waveD_d16_dir_id_unique (dir : Direction) (hs : List HTLCRecord)
    (hnd : DirIdsDistinct dir hs) : DirIdUnique dir hs :=
  eq_of_id_eq_of_nodup hnd

/-! ## The two BOLT 2 id counters -/

/-- A channel-level HTLC book: the live/settled record list together with the
two per-sender id counters required by BOLT 2.  rust-lightning calls them
`next_holder_htlc_id` and `next_counterparty_htlc_id`
(`lightning/src/ln/channel.rs:3719-3720`). -/
structure HtlcBook where
  htlcs : List HTLCRecord
  nextLocalId : Nat
  nextRemoteId : Nat
deriving Repr

/-- The next id of a direction. -/
def HtlcBook.nextId (b : HtlcBook) : Direction → Nat
  | .local => b.nextLocalId
  | .remote => b.nextRemoteId

/-- Every live HTLC's id is strictly below its sender's counter. -/
def HtlcBook.counterFresh (b : HtlcBook) : Prop :=
  ∀ h ∈ htlcSet b.htlcs, h.id < b.nextId h.direction

/-- The channel invariant: counter freshness plus per-direction id
distinctness.  This is the channel-level state that the single-record model
omits. -/
def HtlcBook.Inv (b : HtlcBook) : Prop :=
  b.counterFresh ∧
    DirIdsDistinct .local b.htlcs ∧ DirIdsDistinct .remote b.htlcs

/-- Allocate a fresh HTLCRecord at the sender's counter.  This is the id
discipline of BOLT 2 §Adding an HTLC: the first offer has id 0 and each
successive offer increments by one. -/
def HtlcBook.allocate (b : HtlcBook) (dir : Direction) (amount : Msat)
    (ph : PaymentHash) (cltv : Height) : HTLCRecord :=
  { id := b.nextId dir
    direction := dir
    amountMsat := amount
    paymentHash := ph
    cltvExpiry := cltv
    state := match dir with
      | .local => .offered
      | .remote => .received }

/-- Add the freshly allocated HTLCRecord and increment the corresponding
counter, leaving the other sender's counter untouched. -/
def HtlcBook.push (b : HtlcBook) (dir : Direction) (amount : Msat)
    (ph : PaymentHash) (cltv : Height) : HtlcBook :=
  { htlcs := b.allocate dir amount ph cltv :: b.htlcs
    nextLocalId := match dir with
      | .local => b.nextLocalId + 1
      | .remote => b.nextLocalId
    nextRemoteId := match dir with
      | .local => b.nextRemoteId
      | .remote => b.nextRemoteId + 1 }

theorem allocate_id (b : HtlcBook) (dir : Direction) (amount : Msat)
    (ph : PaymentHash) (cltv : Height) :
    (b.allocate dir amount ph cltv).id = b.nextId dir := rfl

theorem allocate_direction (b : HtlcBook) (dir : Direction) (amount : Msat)
    (ph : PaymentHash) (cltv : Height) :
    (b.allocate dir amount ph cltv).direction = dir := rfl

theorem allocate_isLive (b : HtlcBook) (dir : Direction) (amount : Msat)
    (ph : PaymentHash) (cltv : Height) :
    (b.allocate dir amount ph cltv).isLive = true := by
  cases dir <;> rfl

theorem push_nextId_same (b : HtlcBook) (dir : Direction) (amount : Msat)
    (ph : PaymentHash) (cltv : Height) :
    (b.push dir amount ph cltv).nextId dir = b.nextId dir + 1 := by
  cases dir <;> rfl

theorem push_nextId_other (b : HtlcBook) (dir e : Direction) (amount : Msat)
    (ph : PaymentHash) (cltv : Height) (hne : e ≠ dir) :
    (b.push dir amount ph cltv).nextId e = b.nextId e := by
  cases dir <;> cases e <;> simp_all [HtlcBook.push, HtlcBook.nextId]

/-- Fresh allocation at the counter keeps every existing id below its counter. -/
theorem waveD_d16_push_counterFresh (b : HtlcBook) (hfresh : b.counterFresh)
    (dir : Direction) (amount : Msat) (ph : PaymentHash) (cltv : Height) :
    (b.push dir amount ph cltv).counterFresh := by
  intro h hm
  have hsplit : htlcSet (b.allocate dir amount ph cltv :: b.htlcs) =
      b.allocate dir amount ph cltv :: htlcSet b.htlcs := by
    simp [htlcSet, allocate_isLive]
  have hm' : h ∈ b.allocate dir amount ph cltv :: htlcSet b.htlcs := by
    simpa [HtlcBook.push, hsplit] using hm
  simp only [List.mem_cons] at hm'
  rcases hm' with rfl | hm'
  · cases dir <;>
      simp [HtlcBook.push, HtlcBook.nextId, HtlcBook.allocate] <;> omega
  · by_cases hdir : h.direction = dir
    · have hlt : h.id < b.nextId dir := by
        have := hfresh h hm'
        simpa [hdir] using this
      have hnext : (b.push dir amount ph cltv).nextId h.direction =
          b.nextId dir + 1 := by
        rw [hdir]
        exact push_nextId_same b dir amount ph cltv
      rw [hnext]
      omega
    · have hnext : (b.push dir amount ph cltv).nextId h.direction =
          b.nextId h.direction :=
        push_nextId_other b dir h.direction amount ph cltv hdir
      rw [hnext]
      exact hfresh h hm'

theorem dirLiveSet_cons_same (dir : Direction) (r : HTLCRecord)
    (hs : List HTLCRecord) (hr : r.isLive = true) (hd : r.direction = dir) :
    dirLiveSet dir (r :: hs) = r :: dirLiveSet dir hs := by
  unfold dirLiveSet htlcSet
  simp [hr, hd]

theorem dirLiveSet_cons_other (dir : Direction) (r : HTLCRecord)
    (hs : List HTLCRecord) (hr : r.isLive = true) (hd : r.direction ≠ dir) :
    dirLiveSet dir (r :: hs) = dirLiveSet dir hs := by
  unfold dirLiveSet htlcSet
  simp [hr, hd]

/-- Adding at the counter preserves distinctness inside the sender's
direction: the new id is the counter value, and every existing id in that
direction is strictly below it. -/
theorem waveD_d16_push_dirIdsDistinct (b : HtlcBook) (hfresh : b.counterFresh)
    (dir : Direction) (amount : Msat) (ph : PaymentHash) (cltv : Height)
    (hnd : DirIdsDistinct dir b.htlcs) :
    DirIdsDistinct dir (b.push dir amount ph cltv).htlcs := by
  unfold DirIdsDistinct dirLiveIds at *
  have hset : dirLiveSet dir (b.push dir amount ph cltv).htlcs =
      b.allocate dir amount ph cltv :: dirLiveSet dir b.htlcs := by
    rw [show (b.push dir amount ph cltv).htlcs =
      b.allocate dir amount ph cltv :: b.htlcs from rfl]
    exact dirLiveSet_cons_same dir _ _ (allocate_isLive _ _ _ _ _) rfl
  rw [hset, List.map_cons, List.nodup_cons]
  refine ⟨?_, hnd⟩
  rw [List.mem_map]
  rintro ⟨x, hx, hxid⟩
  have hxset : x ∈ htlcSet b.htlcs := (List.mem_filter.mp hx).1
  have hxdir : x.direction = dir := of_decide_eq_true (List.mem_filter.mp hx).2
  have hxlt : x.id < b.nextId dir := by
    have := hfresh x hxset
    simpa [hxdir] using this
  have hrid : (b.allocate dir amount ph cltv).id = b.nextId dir := allocate_id _ _ _ _ _
  rw [hrid] at hxid
  omega

/-- Adding in one direction leaves the other direction's distinctness
untouched. -/
theorem waveD_d16_push_dirIdsDistinct_other (b : HtlcBook)
    (dir' : Direction) (hnd : DirIdsDistinct dir' b.htlcs)
    (dir : Direction) (amount : Msat) (ph : PaymentHash) (cltv : Height)
    (hne : dir' ≠ dir) :
    DirIdsDistinct dir' (b.push dir amount ph cltv).htlcs := by
  unfold DirIdsDistinct dirLiveIds at *
  have hset : dirLiveSet dir' (b.push dir amount ph cltv).htlcs =
      dirLiveSet dir' b.htlcs := by
    rw [show (b.push dir amount ph cltv).htlcs =
      b.allocate dir amount ph cltv :: b.htlcs from rfl]
    exact dirLiveSet_cons_other dir' _ _ (allocate_isLive _ _ _ _ _) (by
      rw [allocate_direction]
      exact fun h => hne h.symm)
  rw [hset]
  exact hnd

/-- The channel invariant is preserved by a counter-based add. -/
theorem waveD_d16_push_preserves_inv (b : HtlcBook) (hinv : b.Inv)
    (dir : Direction) (amount : Msat) (ph : PaymentHash) (cltv : Height) :
    (b.push dir amount ph cltv).Inv := by
  refine ⟨waveD_d16_push_counterFresh b hinv.1 dir amount ph cltv, ?_, ?_⟩
  · by_cases h : dir = .local
    · subst h
      exact waveD_d16_push_dirIdsDistinct b hinv.1 .local amount ph cltv hinv.2.1
    · exact waveD_d16_push_dirIdsDistinct_other b .local hinv.2.1 dir amount ph cltv
        (fun he => h he.symm)
  · by_cases h : dir = .remote
    · subst h
      exact waveD_d16_push_dirIdsDistinct b hinv.1 .remote amount ph cltv hinv.2.2
    · exact waveD_d16_push_dirIdsDistinct_other b .remote hinv.2.2 dir amount ph cltv
        (fun he => h he.symm)

/-- Consequently, after a counter-based add, the live ids of that direction
are unique. -/
theorem waveD_d16_push_dir_id_unique (b : HtlcBook) (hinv : b.Inv)
    (dir : Direction) (amount : Msat) (ph : PaymentHash) (cltv : Height) :
    DirIdUnique dir (b.push dir amount ph cltv).htlcs := by
  have hnd : DirIdsDistinct dir (b.push dir amount ph cltv).htlcs := by
    by_cases h : dir = .local
    · subst h
      exact waveD_d16_push_dirIdsDistinct b hinv.1 .local amount ph cltv hinv.2.1
    · by_cases h' : dir = .remote
      · subst h'
        exact waveD_d16_push_dirIdsDistinct b hinv.1 .remote amount ph cltv hinv.2.2
      · exfalso
        cases dir <;> simp_all
  exact waveD_d16_dir_id_unique dir _ hnd

/-- The empty book satisfies the channel invariant. -/
theorem waveD_d16_empty_inv : (⟨[], 0, 0⟩ : HtlcBook).Inv := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [HtlcBook.counterFresh, DirIdsDistinct, dirLiveIds, dirLiveSet, htlcSet]

/-! ## Negative results: the model alone does not give the unconditional claim -/

/-- A concrete payment hash used by the counterexamples. -/
def sampleHash : PaymentHash := ⟨ByteArray.empty⟩

/-- First HTLC of the local sender, id 0. -/
def dupLocal : HTLCRecord :=
  { id := 0
    direction := .local
    amountMsat := ⟨1000⟩
    paymentHash := sampleHash
    cltvExpiry := 500
    state := .offered }

/-- First HTLC of the remote sender, also id 0.  BOLT 2 assigns id 0 to the
first HTLC of *each* sender, so this pair is protocol-conforming; it shows that
id uniqueness across the whole live set needs a cross-direction disjointness
assumption that the record model does not have. -/
def dupRemote : HTLCRecord :=
  { id := 0
    direction := .remote
    amountMsat := ⟨2000⟩
    paymentHash := sampleHash
    cltvExpiry := 600
    state := .received }

/-- The unconditional global claim is false in the record model: a live set may
contain two distinct records with the same id. -/
theorem waveD_d16_id_unique_counterexample :
    ¬ LiveIdUnique [dupLocal, dupRemote] := by
  intro huniq
  have hm1 : dupLocal ∈ htlcSet [dupLocal, dupRemote] := by
    simp [htlcSet, dupLocal, dupRemote, HTLCRecord.isLive, HTLCState.isLive]
  have hm2 : dupRemote ∈ htlcSet [dupLocal, dupRemote] := by
    simp [htlcSet, dupLocal, dupRemote, HTLCRecord.isLive, HTLCState.isLive]
  have hid : dupLocal.id = dupRemote.id := rfl
  have heq := huniq dupLocal hm1 dupRemote hm2 hid
  exact absurd heq (by decide)

/-- Equivalently, no unconditional theorem of the shape
`∀ hs, LiveIdUnique hs` can hold in this model. -/
theorem waveD_d16_id_unique_unconditional_false :
    ¬ (∀ hs : List HTLCRecord, LiveIdUnique hs) := by
  intro hall
  exact waveD_d16_id_unique_counterexample (hall [dupLocal, dupRemote])

/-- Even the BOLT 2 per-sender increment discipline does not make the *global*
live set id-unique: the two endpoints own independent counters that both start
at 0.  The faithful claim is the per-direction one. -/
theorem waveD_d16_bolt_allows_cross_direction_duplicate :
    ∃ hs : List HTLCRecord,
      dupLocal ∈ htlcSet hs ∧ dupRemote ∈ htlcSet hs ∧
      dupLocal.id = dupRemote.id ∧ dupLocal ≠ dupRemote := by
  refine ⟨[dupLocal, dupRemote], ?_, ?_, rfl, ?_⟩
  · simp [htlcSet, dupLocal, dupRemote, HTLCRecord.isLive, HTLCState.isLive]
  · simp [htlcSet, dupLocal, dupRemote, HTLCRecord.isLive, HTLCState.isLive]
  · decide

/-- The model's `addHTLC` has no channel set and no id counter in its
arguments, so it cannot reject a repeated id.  Two successful adds with the
same id but different amounts produce distinct live records. -/
def addDupA : HTLCRecord :=
  { id := 0
    direction := .local
    amountMsat := ⟨1000⟩
    paymentHash := sampleHash
    cltvExpiry := 500
    state := .offered }

def addDupB : HTLCRecord :=
  { id := 0
    direction := .local
    amountMsat := ⟨2000⟩
    paymentHash := sampleHash
    cltvExpiry := 500
    state := .offered }

theorem waveD_d16_addHTLC_allows_duplicate_id :
    addHTLC ⟨100000⟩ ⟨0⟩ 0 .local ⟨1000⟩ sampleHash 500 = .ok addDupA ∧
    addHTLC ⟨100000⟩ ⟨0⟩ 0 .local ⟨2000⟩ sampleHash 500 = .ok addDupB ∧
    addDupA ≠ addDupB ∧ addDupA.id = addDupB.id := by
  refine ⟨?_, ?_, ?_, rfl⟩
  · simp [addHTLC, addDupA, MAX_CLTV_EXPIRY]
  · simp [addHTLC, addDupB, MAX_CLTV_EXPIRY]
  · decide

/-- The two records produced above are both live and both carry id 0, so the
model's add transition does not maintain `LiveIdsDistinct`. -/
theorem waveD_d16_addHTLC_breaks_liveIdsDistinct :
    addDupA.isLive = true ∧ addDupB.isLive = true ∧
      addDupA.id = addDupB.id ∧ addDupA ≠ addDupB := by
  refine ⟨by decide, by decide, rfl, by decide⟩

end LnLean.Proofs.WaveD.D16
