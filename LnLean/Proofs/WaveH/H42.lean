import LnLean.Proofs.Routing.GossipRawRefinementTargets

/-!
# H42 — raw-extension impossibility at a gossip epoch boundary (`RT-01`)

**English claim.**  Wave 7 (`GossipRawRefinementTargets`) proved that raw
`applyGossip` has no canonical refinement as a function and that no transition
keeping raw append semantics for `channel_announcement` can preserve
`CanonicalAnnouncements`.  This lane lifts that result to an explicit *epoch
boundary*: a store is tagged with an epoch counter, and a boundary step consumes
a whole batch of gossip messages and advances the epoch.  The boundary operator
may inspect the epoch counter and the entire batch, so it is strictly more
powerful than the step-by-step wave-7 operator.  The impossibility survives.

## Exact boundary condition

For one raw announcement append,

  `CanonicalAnnouncements (applyGossip s (.channelAnnouncement a)).announcements`

holds **iff** the store is already canonical and every stored record with the
incoming `short_channel_id` is *literally* the incoming record
(`canonicalAnnouncements_applyGossip_announcement_iff`).  Raw append has no
replacement or rejection step: a genuinely new record for an existing channel
always breaks canonicality, while canonical admission replaces the record.

## Sharp conditional refinement

`BoundaryAdmissible` records, for every message of a boundary batch, the
canonical admission gate, the raw clock gate, and freshness.  Under that
predicate the raw fold and the canonical fold agree exactly
(`rawBoundaryExtension_eq_canonical_of_admissible`), and the canonical fold
preserves canonical reachability
(`canonicalBoundaryExtension_reachable`).  This is the strongest true
refinement on the common domain.

## Boundary witness and impossibility

`epoch_boundary_witness` exhibits a canonically reachable epoch-1 store with one
announcement.  At the next boundary, canonical admission rejects a conflicting
re-announcement (a no-op), while raw extension appends it and breaks
`CanonicalAnnouncements`.  `no_canonical_preserving_raw_boundary_extension`
proves that no boundary operator — even one that sees the epoch and the whole
batch — can both implement raw announcement appending and preserve canonicality.

All wave-4/5/6/7 raw counterexamples are re-exported unchanged.

No forbidden proof escapes: no `sorry`, no `axiom`, no `admit`, no
`native_decide`, and no `unsafe` or implementation-bypass attributes.
-/

namespace LnLean.Proofs.WaveH.H42

open LnLean.Routing
open LnLean.Proofs.Routing.GossipCanonicalTargets
open LnLean.Proofs.Routing.GossipRawRefinementTargets
open Classical

set_option autoImplicit false

/-! ## 1. Epoch-tagged stores and boundary extensions -/

/-- A gossip store tagged with an epoch counter and the explicit node-key
registration map of the canonical wrapper. -/
structure EpochStore where
  /-- The raw gossip store. -/
  gossip : GossipState
  /-- The explicit `NodeId → PubKey` registration map. -/
  nodeKeyOf : NodeId → PubKey
  /-- The current epoch.  Boundary steps advance it by one. -/
  epoch : Nat

namespace EpochStore

/-- Forget the epoch tag, recovering the wave-7 canonical store. -/
def toCanonicalStore (es : EpochStore) : CanonicalStore :=
  { gossip := es.gossip, nodeKeyOf := es.nodeKeyOf }

end EpochStore

/-- Raw fold of a boundary batch: messages are applied in list order with
`applyGossip`, so announcements and node announcements are prepended and an
update is admitted only by the single global timestamp clock. -/
def rawBoundaryStore (s : GossipState) (msgs : List GossipMessage) :
    GossipState :=
  msgs.foldl applyGossip s

/-- Raw epoch-boundary extension.  The operator sees the whole batch and the
epoch, but preserves raw append semantics on the gossip store. -/
def rawBoundaryExtension (es : EpochStore) (msgs : List GossipMessage) :
    EpochStore :=
  { gossip := rawBoundaryStore es.gossip msgs
    nodeKeyOf := es.nodeKeyOf
    epoch := es.epoch + 1 }

/-- Canonical fold of a boundary batch over the wave-7 canonical store
transition. -/
noncomputable def canonicalBoundaryStore (verify : SigVerifier)
    (cs : CanonicalStore) (msgs : List GossipMessage) : CanonicalStore :=
  msgs.foldl (fun cs m => applyGossipCanonicalStore verify cs m) cs

/-- Canonical epoch-boundary extension.  It advances the epoch and applies the
canonical admission policy to every message of the batch. -/
noncomputable def canonicalBoundaryExtension (verify : SigVerifier)
    (es : EpochStore) (msgs : List GossipMessage) : EpochStore :=
  { gossip := (canonicalBoundaryStore verify es.toCanonicalStore msgs).gossip
    nodeKeyOf := (canonicalBoundaryStore verify es.toCanonicalStore msgs).nodeKeyOf
    epoch := es.epoch + 1 }

@[simp] theorem rawBoundaryStore_nil (s : GossipState) :
    rawBoundaryStore s [] = s := rfl

@[simp] theorem rawBoundaryStore_cons (s : GossipState) (m : GossipMessage)
    (ms : List GossipMessage) :
    rawBoundaryStore s (m :: ms) = rawBoundaryStore (applyGossip s m) ms :=
  rfl

@[simp] theorem canonicalBoundaryStore_nil (verify : SigVerifier)
    (cs : CanonicalStore) :
    canonicalBoundaryStore verify cs [] = cs := rfl

@[simp] theorem canonicalBoundaryStore_cons (verify : SigVerifier)
    (cs : CanonicalStore) (m : GossipMessage) (ms : List GossipMessage) :
    canonicalBoundaryStore verify cs (m :: ms) =
      canonicalBoundaryStore verify (applyGossipCanonicalStore verify cs m) ms :=
  rfl

@[simp] theorem rawBoundaryExtension_gossip (es : EpochStore)
    (msgs : List GossipMessage) :
    (rawBoundaryExtension es msgs).gossip = rawBoundaryStore es.gossip msgs :=
  rfl

@[simp] theorem rawBoundaryExtension_epoch (es : EpochStore)
    (msgs : List GossipMessage) :
    (rawBoundaryExtension es msgs).epoch = es.epoch + 1 := rfl

@[simp] theorem canonicalBoundaryExtension_gossip (verify : SigVerifier)
    (es : EpochStore) (msgs : List GossipMessage) :
    (canonicalBoundaryExtension verify es msgs).gossip =
      (canonicalBoundaryStore verify es.toCanonicalStore msgs).gossip :=
  rfl

@[simp] theorem canonicalBoundaryExtension_epoch (verify : SigVerifier)
    (es : EpochStore) (msgs : List GossipMessage) :
    (canonicalBoundaryExtension verify es msgs).epoch = es.epoch + 1 := rfl

/-! ## 2. The exact single-boundary condition for raw announcements -/

/-- **Exact canonicality condition for a raw announcement append.**  Appending
`a` to a raw store preserves `CanonicalAnnouncements` iff the store was already
canonical and every stored record with `a`'s `short_channel_id` is literally
`a`.  A genuinely new record for an existing channel — in particular any
replacement with different keys, capacity, or signatures — breaks canonicality.
There is no freshness-only or replacement-only reading: raw append can preserve
canonicality only by duplicating an identical record. -/
theorem canonicalAnnouncements_cons_iff (a : ChannelAnnellation)
    (l : List ChannelAnnellation) :
    CanonicalAnnouncements (a :: l) ↔
      CanonicalAnnouncements l ∧
        ∀ b ∈ l, b.shortChannelId = a.shortChannelId → b = a := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro x hx y hy hscid
      exact h x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy) hscid
    · intro b hb hscid
      exact (h a (List.mem_cons_self ..) b (List.mem_cons_of_mem _ hb) hscid.symm).symm
  · rintro ⟨hc, hdup⟩ x hx y hy hscid
    rcases List.mem_cons.mp hx with hx' | hx'
    · subst x
      rcases List.mem_cons.mp hy with hy' | hy'
      · subst y
        rfl
      · exact (hdup y hy' hscid.symm).symm
    · rcases List.mem_cons.mp hy with hy' | hy'
      · subst y
        exact hdup x hx' hscid
      · exact hc x hx' y hy' hscid

/-- **Exact single-boundary condition.**  Raw `applyGossip` on a
`channel_announcement` preserves canonicality exactly when every stored
same-channel record is the incoming record itself. -/
theorem canonicalAnnouncements_applyGossip_announcement_iff
    (s : GossipState) (a : ChannelAnnellation) :
    CanonicalAnnouncements (applyGossip s (.channelAnnouncement a)).announcements ↔
      CanonicalAnnouncements s.announcements ∧
        ∀ b ∈ s.announcements, b.shortChannelId = a.shortChannelId → b = a := by
  simpa [applyGossip] using canonicalAnnouncements_cons_iff a s.announcements

/-- Freshness is the sufficient special case of the exact condition: a raw
append of a channel id not already stored preserves canonicality. -/
theorem canonicalAnnouncements_applyGossip_announcement_of_fresh
    (s : GossipState) (a : ChannelAnnellation)
    (hcanon : CanonicalAnnouncements s.announcements)
    (hfresh : ∀ b ∈ s.announcements, b.shortChannelId ≠ a.shortChannelId) :
    CanonicalAnnouncements (applyGossip s (.channelAnnouncement a)).announcements :=
  (canonicalAnnouncements_applyGossip_announcement_iff s a).mpr
    ⟨hcanon, fun b hb hscid => absurd hscid (hfresh b hb)⟩

/-- **Why canonical admission cannot be preserved by an arbitrary raw
extension.**  If a stored record for the incoming channel is a different
record, raw appending the incoming announcement necessarily breaks
canonicality.  The witness `b` is the boundary conflict. -/
theorem raw_announcement_boundary_cannot_preserve_conflict
    (s : GossipState) (a b : ChannelAnnellation)
    (hb : b ∈ s.announcements)
    (hscid : b.shortChannelId = a.shortChannelId)
    (hne : b ≠ a) :
    ¬ CanonicalAnnouncements (applyGossip s (.channelAnnouncement a)).announcements := by
  intro h
  exact hne
    (((canonicalAnnouncements_applyGossip_announcement_iff s a).mp h).2 b hb hscid)

/-! ## 3. The sharp conditional refinement over a whole boundary batch -/

/-- **Stepwise admissibility of a boundary batch.**  For every message, the
canonical admission gate holds at the canonical state, the raw global clock
admits it, and it is fresh for the raw store.  This is exactly the common
domain on which raw insertion and canonical admission coincide. -/
def BoundaryAdmissible (verify : SigVerifier) :
    GossipState → CanonicalStore → List GossipMessage → Prop
  | _s, _cs, [] => True
  | s, cs, m :: ms =>
      CanonicalMessageAdmitted verify cs m ∧
        RawClockAdmits s m ∧
        FreshMessage s m ∧
        BoundaryAdmissible verify (applyGossip s m)
          (applyGossipCanonicalStore verify cs m) ms

/-- **Batch refinement.**  If the raw and canonical states start in sync and
every message of the boundary batch is canonically admitted, raw-clock
admitted, and fresh, then the raw fold and the canonical fold have the same
gossip store.  The induction carries the step equality supplied by the wave-7
theorem `applyGossip_eq_canonicalStore_of_fresh`. -/
theorem rawBoundaryStore_eq_canonical_of_admissible
    {verify : SigVerifier} {s : GossipState} {cs : CanonicalStore}
    {msgs : List GossipMessage} (hstate : s = cs.gossip)
    (hadm : BoundaryAdmissible verify s cs msgs) :
    rawBoundaryStore s msgs = (canonicalBoundaryStore verify cs msgs).gossip := by
  induction msgs generalizing s cs with
  | nil =>
      simpa [rawBoundaryStore, canonicalBoundaryStore] using hstate
  | cons m ms ih =>
      change CanonicalMessageAdmitted verify cs m ∧ RawClockAdmits s m ∧
        FreshMessage s m ∧ BoundaryAdmissible verify (applyGossip s m)
          (applyGossipCanonicalStore verify cs m) ms at hadm
      rcases hadm with ⟨hgate, hclock, hfresh, htail⟩
      have hclock' : RawClockAdmits cs.gossip m := hstate ▸ hclock
      have hfresh' : FreshMessage cs.gossip m := hstate ▸ hfresh
      have hstep : applyGossip s m =
          (applyGossipCanonicalStore verify cs m).gossip := by
        rw [hstate]
        exact applyGossip_eq_canonicalStore_of_fresh verify cs m hgate hclock' hfresh'
      rw [rawBoundaryStore_cons, canonicalBoundaryStore_cons]
      exact ih hstep htail

/-- **Epoch-boundary refinement.**  On a raw store in canonical state shape
with a stepwise-admissible batch, the raw boundary extension and the canonical
boundary extension have the same gossip store.  This is the sharpest true
refinement at the epoch boundary: it is conditional exactly on the gates that
raw insertion lacks. -/
theorem rawBoundaryExtension_eq_canonical_of_admissible
    {verify : SigVerifier} {es : EpochStore} {msgs : List GossipMessage}
    (hadm : BoundaryAdmissible verify es.gossip es.toCanonicalStore msgs) :
    (rawBoundaryExtension es msgs).gossip =
      (canonicalBoundaryExtension verify es msgs).gossip :=
  rawBoundaryStore_eq_canonical_of_admissible rfl hadm

/-- The canonical boundary fold preserves canonical reachability: a reachable
epoch store remains reachable after any canonical batch. -/
theorem canonicalBoundaryStore_reachable (verify : SigVerifier)
    (cs : CanonicalStore) (msgs : List GossipMessage)
    (h : ReachableCanonicalStore verify cs) :
    ReachableCanonicalStore verify (canonicalBoundaryStore verify cs msgs) := by
  induction msgs generalizing cs with
  | nil => simpa [canonicalBoundaryStore] using h
  | cons m ms ih =>
      rw [canonicalBoundaryStore_cons]
      exact ih (applyGossipCanonicalStore verify cs m)
        (ReachableCanonicalStore.step h)

/-- The canonical epoch-boundary extension preserves canonical reachability. -/
theorem canonicalBoundaryExtension_reachable {verify : SigVerifier}
    {es : EpochStore} (msgs : List GossipMessage)
    (h : ReachableCanonicalStore verify es.toCanonicalStore) :
    ReachableCanonicalStore verify
      (canonicalBoundaryExtension verify es msgs).toCanonicalStore := by
  simpa [canonicalBoundaryExtension, EpochStore.toCanonicalStore] using
    canonicalBoundaryStore_reachable verify es.toCanonicalStore msgs h

/-! ## 4. Concrete boundary witness -/

private def acceptAll : SigVerifier := fun _ _ _ => true

/-- Byte length 1. -/
private def kA : PubKey := ⟨ByteArray.mk #[1]⟩

/-- Byte length 0. -/
private def kB : PubKey := ⟨ByteArray.empty⟩

/-- Byte length 2. -/
private def kC : PubKey := ⟨ByteArray.mk #[1, 2]⟩

private def nA : NodeId := ⟨0⟩

private def nB : NodeId := ⟨1⟩

/-- The single channel used by the boundary witness. -/
private def sc1 : ShortChannelId := ⟨1, 2, 3⟩

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

/-- The initial announcement: node `nA` is registered to key `kA`. -/
private def ann1 : ChannelAnnellation := mkAnn sc1 nA nB kA kB 1000

/-- A conflicting re-announcement of the same channel that rebinds `nA` from
`kA` to `kC`. -/
private def annConflict : ChannelAnnellation := mkAnn sc1 nA nB kC kB 1000

private theorem ann1_valid : ann1.signaturesValid acceptAll := by
  simp [ChannelAnnellation.signaturesValid, signatureValid, acceptAll]

private theorem nA_ne_nB : nA ≠ nB := by
  decide

private theorem kC_ne_kA : kC ≠ kA := by
  intro h
  have hs := congrArg (fun k => k.bytes.size) h
  have h1 : kC.bytes.size = 2 := by decide
  have h2 : kA.bytes.size = 1 := by decide
  rw [h1, h2] at hs
  omega

private theorem annConflict_ne_ann1 : annConflict ≠ ann1 := by
  intro h
  have hk := congrArg ChannelAnnellation.nodeKey1 h
  exact kC_ne_kA (by simpa [ann1, annConflict, mkAnn] using hk)

private def emptyGossip : GossipState := ⟨[], [], []⟩

/-- The epoch-0 store before any boundary message. -/
private def e0 : EpochStore :=
  { gossip := emptyGossip, nodeKeyOf := fun _ => kB, epoch := 0 }

private theorem e0_compat (a : ChannelAnnellation) :
    e0.toCanonicalStore.gossip.CompatibleWithStore a := by
  intro b hb
  simp [e0, emptyGossip, EpochStore.toCanonicalStore] at hb

private theorem e0_auth (a : ChannelAnnellation) :
    UpdatesAuthorizedBy e0.toCanonicalStore.gossip a := by
  intro u hu
  simp [e0, emptyGossip, EpochStore.toCanonicalStore] at hu

private theorem ann1_gate :
    CanonicalMessageAdmitted acceptAll e0.toCanonicalStore
      (.channelAnnouncement ann1) :=
  ⟨ann1_valid, by simpa [ann1, mkAnn] using nA_ne_nB,
    e0_compat ann1, e0_auth ann1⟩

/-- The canonical store after admitting `ann1` at the epoch-0 boundary. -/
private noncomputable def cs1 : CanonicalStore :=
  applyGossipCanonicalStore acceptAll e0.toCanonicalStore
    (.channelAnnouncement ann1)

private theorem cs1_announcements : cs1.gossip.announcements = [ann1] := by
  rw [cs1, applyGossipCanonicalStore_announcement_of_admitted acceptAll
    e0.toCanonicalStore ann1 ann1_gate]
  simp [e0, emptyGossip, EpochStore.toCanonicalStore, insertReplacing]

/-- The canonically reachable epoch-1 store holding exactly `ann1`. -/
private noncomputable def e1 : EpochStore :=
  { gossip := cs1.gossip, nodeKeyOf := cs1.nodeKeyOf, epoch := 1 }

private theorem e1_announcements : e1.gossip.announcements = [ann1] :=
  cs1_announcements

private theorem e1_reachable :
    ReachableCanonicalStore acceptAll e1.toCanonicalStore := by
  show ReachableCanonicalStore acceptAll cs1
  exact ReachableCanonicalStore.step
    (ReachableCanonicalStore.empty (fun _ => kB))

private theorem e1_compat_annConflict :
    ¬ e1.gossip.CompatibleWithStore annConflict := by
  intro hc
  have hmem : ann1 ∈ e1.gossip.announcements := by
    rw [e1_announcements]
    exact List.mem_singleton_self ann1
  have hkey : ann1.nodeKey1 = annConflict.nodeKey1 := (hc ann1 hmem).1 rfl
  exact kC_ne_kA hkey.symm

private theorem annConflict_gate_fails :
    ¬ CanonicalMessageAdmitted acceptAll e1.toCanonicalStore
      (.channelAnnouncement annConflict) := by
  rintro ⟨_, _, hcompat, _⟩
  exact e1_compat_annConflict
    (by simpa [EpochStore.toCanonicalStore] using hcompat)

/-! ## 5. The two boundary outcomes for the conflicting announcement -/

/-- At the epoch-1 boundary the canonical path rejects the conflicting
re-announcement: the gossip store is unchanged. -/
private theorem canonicalBoundary_rejects_annConflict :
    (canonicalBoundaryExtension acceptAll e1
      [GossipMessage.channelAnnouncement annConflict]).gossip = e1.gossip := by
  have hgate : ¬ (annConflict.signaturesValid acceptAll ∧
      annConflict.node1 ≠ annConflict.node2 ∧
      e1.toCanonicalStore.gossip.CompatibleWithStore annConflict ∧
      UpdatesAuthorizedBy e1.toCanonicalStore.gossip annConflict) := by
    simpa [CanonicalMessageAdmitted] using annConflict_gate_fails
  rw [show (canonicalBoundaryExtension acceptAll e1
        [GossipMessage.channelAnnouncement annConflict]).gossip =
      (applyGossipCanonicalStore acceptAll e1.toCanonicalStore
        (.channelAnnouncement annConflict)).gossip by
    simp [canonicalBoundaryExtension, canonicalBoundaryStore]]
  rw [applyGossipCanonicalStore_announcement_of_rejected acceptAll
    e1.toCanonicalStore annConflict hgate]
  rfl

/-- At the same boundary the raw path appends the conflicting record. -/
private theorem rawBoundary_appends_annConflict :
    (rawBoundaryExtension e1
      [GossipMessage.channelAnnouncement annConflict]).gossip.announcements =
        [annConflict, ann1] := by
  simp [rawBoundaryExtension, rawBoundaryStore, applyGossip, e1_announcements]

/-- The raw boundary store is not canonical. -/
private theorem rawBoundary_not_canonical :
    ¬ CanonicalAnnouncements
      (rawBoundaryExtension e1
        [GossipMessage.channelAnnouncement annConflict]).gossip.announcements := by
  rw [rawBoundary_appends_annConflict]
  intro hc
  exact annConflict_ne_ann1 (hc annConflict (by simp) ann1 (by simp) rfl)

/-- **Exact boundary witness.**  There is a canonically reachable epoch-1 store
with one announcement such that, at the next boundary, canonical admission of a
conflicting re-announcement is a no-op while the raw extension appends it and
breaks `CanonicalAnnouncements`.  The boundary is `e1.epoch = 1`; the witness
announcement is `annConflict`. -/
theorem epoch_boundary_witness :
    ∃ (verify : SigVerifier) (es : EpochStore) (a : ChannelAnnellation),
      ReachableCanonicalStore verify es.toCanonicalStore ∧
        es.epoch = 1 ∧
          (canonicalBoundaryExtension verify es
            [GossipMessage.channelAnnouncement a]).gossip = es.gossip ∧
            (rawBoundaryExtension es
              [GossipMessage.channelAnnouncement a]).gossip ≠ es.gossip ∧
              ¬ CanonicalAnnouncements
                (rawBoundaryExtension es
                  [GossipMessage.channelAnnouncement a]).gossip.announcements := by
  refine ⟨acceptAll, e1, annConflict, e1_reachable, rfl,
    canonicalBoundary_rejects_annConflict, ?_, rawBoundary_not_canonical⟩
  intro h
  have hann : annConflict = ann1 := by
    have hcongr := congrArg GossipState.announcements h
    rw [rawBoundary_appends_annConflict, e1_announcements] at hcongr
    simp at hcongr
  exact annConflict_ne_ann1 hann

/-- **General epoch-boundary conflict obstruction.**  At any epoch boundary, raw
appending an announcement whose channel already has a different stored record
breaks canonicality.  No epoch counter or batch context can repair this,
because the raw announcement projection is fixed by append semantics. -/
theorem epoch_boundary_raw_announcement_breaks_canonicality
    (es : EpochStore) (a b : ChannelAnnellation)
    (hb : b ∈ es.gossip.announcements)
    (hscid : b.shortChannelId = a.shortChannelId)
    (hne : b ≠ a) :
    ¬ CanonicalAnnouncements
      (rawBoundaryExtension es
        [GossipMessage.channelAnnouncement a]).gossip.announcements := by
  simpa [rawBoundaryExtension, rawBoundaryStore, applyGossip] using
    raw_announcement_boundary_cannot_preserve_conflict es.gossip a b hb hscid hne

/-! ## 6. Non-vacuity of the positive boundary refinement -/

private theorem e0_ann1_admissible :
    BoundaryAdmissible acceptAll e0.gossip e0.toCanonicalStore
      [GossipMessage.channelAnnouncement ann1] := by
  refine ⟨ann1_gate, trivial, ?_, trivial⟩
  intro b hb
  simp [e0, emptyGossip] at hb

/-- **Non-vacuous epoch-boundary refinement.**  A fresh announcement at the
epoch-0 boundary is admitted by both paths, and the extensions agree on the
gossip store. -/
theorem epoch_boundary_refinement_witness :
    ∃ (verify : SigVerifier) (es : EpochStore) (msgs : List GossipMessage),
      msgs ≠ [] ∧
        (rawBoundaryExtension es msgs).gossip =
          (canonicalBoundaryExtension verify es msgs).gossip ∧
        (rawBoundaryExtension es msgs).epoch = es.epoch + 1 := by
  refine ⟨acceptAll, e0, [GossipMessage.channelAnnouncement ann1], by simp,
    rawBoundaryExtension_eq_canonical_of_admissible e0_ann1_admissible, rfl⟩

/-! ## 7. Impossibility at the epoch boundary -/

/-- **No canonical-preserving raw boundary extension.**  Even when a boundary
operator sees the epoch counter and the entire batch, it cannot both implement
raw announcement appending and preserve `CanonicalAnnouncements`.  The
counterexample is the two-message batch `[ann1, annConflict]` from the empty
epoch-0 store: raw appending stores both distinct records for `sc1`, while
canonicality demands at most one. -/
theorem no_canonical_preserving_raw_boundary_extension :
    ¬ ∃ F : EpochStore → List GossipMessage → EpochStore,
        (∀ (es : EpochStore) (msgs : List GossipMessage),
          (F es msgs).gossip.announcements =
            (rawBoundaryExtension es msgs).gossip.announcements) ∧
        (∀ (es : EpochStore),
          CanonicalAnnouncements es.gossip.announcements →
            ∀ msgs : List GossipMessage,
              CanonicalAnnouncements (F es msgs).gossip.announcements) := by
  rintro ⟨F, hraw, hpres⟩
  let es : EpochStore :=
    { gossip := ⟨[], [], []⟩, nodeKeyOf := fun _ => kB, epoch := 0 }
  have hempty : CanonicalAnnouncements es.gossip.announcements := by
    intro a ha
    simp [es] at ha
  have hcanon := hpres es hempty
    [GossipMessage.channelAnnouncement ann1,
     GossipMessage.channelAnnouncement annConflict]
  have hlist :
      (F es [GossipMessage.channelAnnouncement ann1,
        GossipMessage.channelAnnouncement annConflict]).gossip.announcements =
        [annConflict, ann1] := by
    rw [hraw]
    simp [rawBoundaryExtension, rawBoundaryStore, applyGossip, es]
  rw [hlist] at hcanon
  exact annConflict_ne_ann1 (hcanon annConflict (by simp) ann1 (by simp) rfl)

/-- Adding the requirement that the boundary operator advances the epoch does
not restore a canonical-preserving raw extension. -/
theorem no_epoch_advancing_canonical_preserving_raw_boundary_extension :
    ¬ ∃ F : EpochStore → List GossipMessage → EpochStore,
        (∀ (es : EpochStore) (msgs : List GossipMessage),
          (F es msgs).gossip.announcements =
            (rawBoundaryExtension es msgs).gossip.announcements) ∧
        (∀ (es : EpochStore) (msgs : List GossipMessage),
          (F es msgs).epoch = es.epoch + 1) ∧
        (∀ (es : EpochStore),
          CanonicalAnnouncements es.gossip.announcements →
            ∀ msgs : List GossipMessage,
              CanonicalAnnouncements (F es msgs).gossip.announcements) := by
  rintro ⟨F, hraw, _hepoch, hpres⟩
  exact no_canonical_preserving_raw_boundary_extension ⟨F, hraw, hpres⟩

/-! ## 8. Preserved raw non-refinement counterexamples -/

/-- The wave-7 raw announcement counterexample is unchanged. -/
theorem raw_announcement_nonrefinement_counterexample_preserved :
    ∃ (s : GossipState) (a : ChannelAnnellation),
      ¬ CanonicalAnnouncements
        (applyGossip s (.channelAnnouncement a)).announcements :=
  raw_conflicting_announcement_counterexample_preserved

/-- The wave-7 single-step impossibility is unchanged. -/
theorem raw_extension_impossibility_preserved :
    ¬ ∃ F : GossipState → GossipMessage → GossipState,
        (∀ (s : GossipState) (a : ChannelAnnellation),
          F s (.channelAnnouncement a) = applyGossip s (.channelAnnouncement a)) ∧
        (∀ s : GossipState, CanonicalAnnouncements s.announcements →
          ∀ m : GossipMessage,
            CanonicalAnnouncements (F s m).announcements) :=
  no_canonical_preserving_raw_announcement_extension

/-- The wave-7 per-slot/global-clock boundary witness is unchanged. -/
theorem canonical_raw_clock_boundary_preserved :
    ∃ (verify : SigVerifier) (cs : CanonicalStore) (u : ChannelUpdate),
      ReachableCanonicalStore verify cs ∧
        CanonicalMessageAdmitted verify cs (.channelUpdate u) ∧
          ¬ RawClockAdmits cs.gossip (.channelUpdate u) ∧
            (applyGossipCanonicalStore verify cs (.channelUpdate u)).gossip.updates =
              u :: cs.gossip.updates ∧
              applyGossip cs.gossip (.channelUpdate u) = cs.gossip ∧
                u ∉ cs.gossip.updates :=
  canonical_admission_strictly_weaker_than_raw_clock

/-! ## 9. Axiom pins -/

/-- info: 'LnLean.Proofs.WaveH.H42.canonicalAnnouncements_applyGossip_announcement_iff' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms canonicalAnnouncements_applyGossip_announcement_iff
/-- info: 'LnLean.Proofs.WaveH.H42.rawBoundaryExtension_eq_canonical_of_admissible' depends on axioms: [propext, choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rawBoundaryExtension_eq_canonical_of_admissible
/-- info: 'LnLean.Proofs.WaveH.H42.epoch_boundary_witness' depends on axioms: [propext, choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms epoch_boundary_witness
/-- info: 'LnLean.Proofs.WaveH.H42.no_canonical_preserving_raw_boundary_extension' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_canonical_preserving_raw_boundary_extension

end LnLean.Proofs.WaveH.H42
