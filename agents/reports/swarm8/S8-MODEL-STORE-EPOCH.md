# S8-MODEL-STORE-EPOCH — explicit store epochs and replacement history

**Lane:** `S8-MODEL-STORE-EPOCH`
**Issue:** `RT-01` (raw insertion vs canonical admission/store path)
**Worktree:** `/home/ubuntu/ln-lean-repair`
**Toolchain:** `leanprover/lean4:v4.35.0` (Lean `4.35.0`, no Mathlib)
**Owned files changed:**

* `LnLean/Routing/Gossip.lean` — additive only, `179` inserted / `0` deleted
  (replacement-removal accounting primitives; captured in integration commit
  `9bafdab`),
* `LnLean/Proofs/Routing/GossipStoreEpochTargets.lean` — new, `1658` lines
  (`918` lines captured in `9bafdab`; `740` additional lines in the current
  worktree for the witnesses and re-exports),
* `agents/reports/swarm8/S8-MODEL-STORE-EPOCH.md` — this report.

No Git write was performed by this lane. No shared file (`LnLean.lean`,
`Obligations.lean`, `Traceability.lean`, `AxiomAudit.lean`, other docs/lane
files, vendor sources) was edited by this lane. The import/wiring visible in
those files was performed by the wave-8 integrator in `9bafdab`.

## 1. Verdict

`RT-01` stays **closed**, and the strongest true statement is a *conditional
sequence-level observation square*, not a refinement of raw `applyGossip`.

The wave-7 result is preserved exactly: raw `applyGossip` appends every
announcement and every update, has no signature/registration/per-slot gate, and
compares only one global timestamp. It therefore cannot refine canonical
admission as a function. Wave 8 adds the missing **store epoch / replacement
history** model:

* `ReplacementEvent` records one canonical admission as `announcement`,
  `update`, or `node`, including the exact list of old records removed by
  `insertReplacing` / `insertUpdateCanonical`;
* `StoreEpoch` packages the canonical store, a monotone epoch counter, a
  newest-first history, and two version views (`announcementEpoch`,
  `updateEpoch`);
* `epochStep` is the canonical store step with this bookkeeping. An admitted
  message increments the epoch, records exactly one event, and installs the
  current version; a rejected message is a **complete no-op**;
* `epochFold` folds `epochStep` over a message sequence.

The main theorem is

```lean
theorem epochFold_gossip_eq_canonicalStoreView_rawFold
    (verify : SigVerifier) (e : StoreEpoch) (s : GossipState)
    (msgs : List GossipMessage)
    (hobs : e.store.gossip = canonicalStoreView s)
    (hadm : EpochAdmittedAlong verify e msgs)
    (hraw : RawAdmittedAlong s msgs) :
    (epochFold verify e msgs).store.gossip =
      canonicalStoreView (rawFold s msgs)
```

The three hypotheses are exact: §5 gives concrete sequences showing `hadm`
cannot be dropped (a raw-appended conflicting announcement survives a canonical
rejection), and another showing `hraw` cannot be dropped (a canonical per-slot
admission is ignored by the raw global clock). `hobs` is the initial-state
comparison; dropping it changes the statement at the empty prefix.

What is **not** claimed:

* raw `applyGossip` still does **not** refine canonical admission, and no
  theorem identifies the two transitions;
* the epoch counter is a model-side version number, **not** a BOLT 7 wire field;
* node announcements are appended by both paths and are not canonicalised
  (`RT-02` is unchanged);
* `SigVerifier` remains abstract; unforgeability remains assumptions C3/C4/C8 in
  `docs/ASSUMPTIONS.md`;
* no network, liveness, chain, UTXO, or rate-limit claim is made.

## 2. Required build

Command (exactly the lane-prescribed form):

```sh
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Proofs.Routing.GossipStoreEpochTargets
```

Result:

```text
⚠ [14/14] Built LnLean.Proofs.Routing.GossipStoreEpochTargets (1.0s)
Build completed successfully (14 jobs).
RC=0
```

The only warnings in the dependency closure are the pre-existing `if_pos` /
`if_neg` deprecations in `LnLean/Proofs/Routing/GossipProps.lean`. The new
module and the additive section of `LnLean/Routing/Gossip.lean` produce no
warnings. No full `lake build` was run.

## 3. Exact signatures

Namespace: `LnLean.Proofs.Routing.GossipStoreEpochTargets`. The `StoreEpoch`
helper namespace is `LnLean.Proofs.Routing.GossipStoreEpochTargets.StoreEpoch`.
The additive list primitives are in `LnLean.Routing`.

### 3.1 Typed replacement history

```lean
inductive ReplacementEvent where
  | announcement (epoch : Nat) (incoming : ChannelAnnellation)
      (replaced : List ChannelAnnellation)
  | update (epoch : Nat) (incoming : ChannelUpdate)
      (replaced : List ChannelUpdate)
  | node (epoch : Nat) (announcement : NodeAnnouncement)

namespace ReplacementEvent
def epoch : ReplacementEvent → Nat
def incomingAnnouncement? : ReplacementEvent → Option ChannelAnnellation
def incomingUpdate? : ReplacementEvent → Option ChannelUpdate
def incomingNode? : ReplacementEvent → Option NodeAnnouncement
end ReplacementEvent
```

The `replaced` field is exactly `replacedAnnouncements a l` or
`replacedUpdates u l`, so the history records *what* was superseded, not only
the resulting store.

### 3.2 Epoch store and canonical epoch step

```lean
structure StoreEpoch where
  epoch : Nat
  store : CanonicalStore
  history : List ReplacementEvent
  announcementEpoch : ShortChannelId → Option Nat
  updateEpoch : ShortChannelId → Bool → Option Nat

namespace StoreEpoch
def empty (nodeKeyOf : NodeId → PubKey) : StoreEpoch
def setAnnouncementEpoch (f : ShortChannelId → Option Nat)
    (a : ChannelAnnellation) (k : Nat) : ShortChannelId → Option Nat
def setUpdateEpoch (f : ShortChannelId → Bool → Option Nat)
    (u : ChannelUpdate) (k : Nat) : ShortChannelId → Bool → Option Nat
def eventOf (e : StoreEpoch) (m : GossipMessage) : ReplacementEvent
def announcementEpochAfter (e : StoreEpoch) (m : GossipMessage) :
    ShortChannelId → Option Nat
def updateEpochAfter (e : StoreEpoch) (m : GossipMessage) :
    ShortChannelId → Bool → Option Nat
end StoreEpoch

noncomputable def epochStep (verify : SigVerifier) (e : StoreEpoch)
    (m : GossipMessage) : StoreEpoch
```

`epochStep` increments `epoch`, conses one `eventOf` event, updates the views,
and takes `applyGossipCanonicalStore` when
`CanonicalMessageAdmitted verify e.store m`; otherwise it returns `e`
definitionally.

### 3.3 Folding and admission-along-sequence predicates

```lean
noncomputable def epochFold (verify : SigVerifier) (e : StoreEpoch)
    (msgs : List GossipMessage) : StoreEpoch

def rawFold (s : GossipState) (msgs : List GossipMessage) : GossipState

def EpochAdmittedAlong (verify : SigVerifier) (e : StoreEpoch) :
    List GossipMessage → Prop

def RawAdmittedAlong : GossipState → List GossipMessage → Prop
```

`EpochAdmittedAlong` is prefix-relative: each message is admitted at the epoch
store reached by the preceding prefix. `RawAdmittedAlong` likewise checks the
raw global clock at the actual raw state reached by the prefix.

### 3.4 Step and fold laws

```lean
theorem epochStep_history_of_admitted {verify : SigVerifier} {e : StoreEpoch}
    {m : GossipMessage} (h : CanonicalMessageAdmitted verify e.store m) :
    (epochStep verify e m).history = e.eventOf m :: e.history

theorem epochStep_epoch_of_admitted {verify : SigVerifier} {e : StoreEpoch}
    {m : GossipMessage} (h : CanonicalMessageAdmitted verify e.store m) :
    (epochStep verify e m).epoch = e.epoch + 1

theorem epochStep_of_rejected {verify : SigVerifier} {e : StoreEpoch}
    {m : GossipMessage} (h : ¬ CanonicalMessageAdmitted verify e.store m) :
    epochStep verify e m = e

theorem epochStep_store (verify : SigVerifier) (e : StoreEpoch)
    (m : GossipMessage) :
    (epochStep verify e m).store = applyGossipCanonicalStore verify e.store m

theorem epochStep_epoch_eq_succ_iff (verify : SigVerifier) (e : StoreEpoch)
    (m : GossipMessage) :
    (epochStep verify e m).epoch = e.epoch + 1 ↔
      CanonicalMessageAdmitted verify e.store m

theorem epochFold_store_eq_foldl (verify : SigVerifier) (e : StoreEpoch)
    (msgs : List GossipMessage) :
    (epochFold verify e msgs).store =
      msgs.foldl (fun cs m => applyGossipCanonicalStore verify cs m) e.store

theorem epochFold_history_extends (verify : SigVerifier) (e : StoreEpoch)
    (msgs : List GossipMessage) :
    ∃ newer, (epochFold verify e msgs).history = newer ++ e.history

theorem epochFold_history_length (verify : SigVerifier) (e : StoreEpoch)
    (msgs : List GossipMessage) (hlen : e.history.length = e.epoch) :
    (epochFold verify e msgs).history.length = (epochFold verify e msgs).epoch

theorem epochFold_empty_history_length (verify : SigVerifier)
    (nodeKeyOf : NodeId → PubKey) (msgs : List GossipMessage) :
    (epochFold verify (empty nodeKeyOf) msgs).history.length =
      (epochFold verify (empty nodeKeyOf) msgs).epoch
```

Also available: `epochStep_epoch_ge`,
`epochStep_epoch_eq_self_or_succ`, `epochStep_history_length`,
`epochStep_shape`, `epochStep_history_cases`, `epochFold_epoch_ge`,
`epochFold_epoch_le`, `epochFold_shape`.

### 3.5 Version-view soundness and boundedness

```lean
def ViewConsistent (e : StoreEpoch) : Prop
def ViewBounded (e : StoreEpoch) : Prop

theorem empty_viewConsistent (nodeKeyOf : NodeId → PubKey) :
    (empty nodeKeyOf).ViewConsistent
theorem empty_viewBounded (nodeKeyOf : NodeId → PubKey) :
    (empty nodeKeyOf).ViewBounded

theorem epochStep_viewConsistent (verify : SigVerifier) (e : StoreEpoch)
    (m : GossipMessage) (h : e.ViewConsistent) :
    (epochStep verify e m).ViewConsistent
theorem epochStep_viewBounded (verify : SigVerifier) (e : StoreEpoch)
    (m : GossipMessage) (h : e.ViewBounded) :
    (epochStep verify e m).ViewBounded

theorem epochFold_viewConsistent (verify : SigVerifier) (e : StoreEpoch)
    (msgs : List GossipMessage) (h : e.ViewConsistent) :
    (epochFold verify e msgs).ViewConsistent
theorem epochFold_viewBounded (verify : SigVerifier) (e : StoreEpoch)
    (msgs : List GossipMessage) (h : e.ViewBounded) :
    (epochFold verify e msgs).ViewBounded

theorem epochFold_stored_announcement_has_install_epoch
    (verify : SigVerifier) (e : StoreEpoch) (msgs : List GossipMessage)
    (hcons : e.ViewConsistent) (hbound : e.ViewBounded) :
    ∀ a ∈ (epochFold verify e msgs).store.gossip.announcements,
      ∃ k, (epochFold verify e msgs).announcementEpoch a.shortChannelId = some k ∧
        k ≤ (epochFold verify e msgs).epoch

theorem epochFold_stored_update_has_install_epoch
    (verify : SigVerifier) (e : StoreEpoch) (msgs : List GossipMessage)
    (hcons : e.ViewConsistent) (hbound : e.ViewBounded) :
    ∀ u ∈ (epochFold verify e msgs).store.gossip.updates,
      ∃ k, (epochFold verify e msgs).updateEpoch u.shortChannelId u.direction =
          some k ∧ k ≤ (epochFold verify e msgs).epoch
```

The `empty`-state corollaries
`epochFold_empty_stored_announcement_has_install_epoch` and
`epochFold_empty_stored_update_has_install_epoch` are the non-vacuous forms.

### 3.6 Whole-store observation laws and the sequence square

```lean
theorem canonicalStoreView_applyGossip_announcement (s : GossipState)
    (a : ChannelAnnellation) :
    canonicalStoreView (applyGossip s (.channelAnnouncement a)) =
      { canonicalStoreView s with
        announcements := insertReplacing a (canonicalStoreView s).announcements }

theorem canonicalStoreView_applyGossip_update (s : GossipState)
    (u : ChannelUpdate) :
    canonicalStoreView (applyGossip s (.channelUpdate u)) =
      if s.latestUpdateTimestamp < u.timestamp then
        { canonicalStoreView s with
          updates := insertUpdateCanonical u (canonicalStoreView s).updates }
      else canonicalStoreView s

theorem canonicalStoreView_applyGossip_node (s : GossipState)
    (n : NodeAnnouncement) :
    canonicalStoreView (applyGossip s (.nodeAnnouncement n)) =
      { canonicalStoreView s with
        nodeAnnouncements := n :: (canonicalStoreView s).nodeAnnouncements }

theorem epochFold_gossip_eq_canonicalStoreView_rawFold
    (verify : SigVerifier) (e : StoreEpoch) (s : GossipState)
    (msgs : List GossipMessage)
    (hobs : e.store.gossip = canonicalStoreView s)
    (hadm : EpochAdmittedAlong verify e msgs)
    (hraw : RawAdmittedAlong s msgs) :
    (epochFold verify e msgs).store.gossip =
      canonicalStoreView (rawFold s msgs)
```

No `CanonicalStoreShape s` hypothesis is needed. The epoch store is canonical
by construction, and the observation laws are whole-store shape laws for an
arbitrary raw store.

## 4. Concrete realistic sequence

The module constructs a private nine-message witness sequence:

1. announce channel `sc1`,
2. announce channel `sc2`,
3. update `u0` on `sc1`, timestamp `10`,
4. update `u1` on `sc1`, timestamp `20` (same slot; supersedes `u0`),
5. update `v0` on `sc2`, timestamp `30`,
6. re-announce `sc1` (`annA'`), replacing `annA`,
7. a conflicting re-announcement of `sc1` (rebinds the node key) — **rejected**,
8. a stale update on `sc1` (`uStale`, timestamp `15` < stored `20`) —
   **rejected**,
9. a node announcement.

The public witness statements are:

```lean
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
      e.history.length = 7

theorem realistic_history_records_supersession :
    ∃ (verify : SigVerifier) (e : StoreEpoch) (a a' : ChannelAnnellation)
      (u0 u1 : ChannelUpdate),
      ReplacementEvent.update 4 u1 [u0] ∈ e.history ∧
        ReplacementEvent.announcement 6 a' [a] ∈ e.history

theorem realistic_rejected_messages_do_not_increment_epoch :
    ∃ (verify : SigVerifier) (eBefore eConflict eStale : StoreEpoch)
      (a : ChannelAnnellation) (u : ChannelUpdate),
      eBefore.epoch = 6 ∧ eConflict.epoch = 6 ∧ eStale.epoch = 6 ∧
        eConflict = eBefore ∧ eStale = eBefore

theorem realistic_admitted_sequence_square :
    ∃ (verify : SigVerifier) (e : StoreEpoch) (s : GossipState)
      (msgs : List GossipMessage),
      msgs.length = 7 ∧
      e.store.gossip = canonicalStoreView s ∧
      EpochAdmittedAlong verify e msgs ∧
      RawAdmittedAlong s msgs ∧
      (epochFold verify e msgs).store.gossip =
        canonicalStoreView (rawFold s msgs)
```

Thus the two rejected messages leave the epoch at `6`, the node announcement
takes it to `7`, and the all-admitted subsequence satisfies the sequence-level
square.

## 5. Divergence witnesses: each hypothesis is necessary

### 5.1 Dropping `hadm`: rejected conflicting announcement

```lean
theorem realistic_rejected_conflict_breaks_refinement :
    ∃ (verify : SigVerifier) (e : StoreEpoch) (s : GossipState)
      (msgs : List GossipMessage),
      e.store.gossip = canonicalStoreView s ∧
      RawAdmittedAlong s msgs ∧
      ¬ EpochAdmittedAlong verify e msgs ∧
      (epochFold verify e msgs).store.gossip ≠
        canonicalStoreView (rawFold s msgs)
```

The witness is `[channel_announcement annA, channel_announcement annConflict]`.
Raw `applyGossip` appends both, so `canonicalStoreView` selects the newer
conflicting record; the canonical epoch fold rejects it and keeps `annA`.
Initial observation and raw admission both hold, so `hadm` is the only failed
hypothesis.

### 5.2 Dropping `hraw`: per-slot admission beyond the global clock

```lean
theorem clock_boundary_sequence_breaks_refinement :
    ∃ (verify : SigVerifier) (e : StoreEpoch) (s : GossipState)
      (msgs : List GossipMessage),
      e.store.gossip = canonicalStoreView s ∧
      EpochAdmittedAlong verify e msgs ∧
      ¬ RawAdmittedAlong s msgs ∧
      (epochFold verify e msgs).store.gossip ≠
        canonicalStoreView (rawFold s msgs)
```

The witness is `[annA, annB, v0 (sc2, timestamp 30), u0 (sc1, timestamp 10)]`.
`u0` is canonically admitted because its own directional slot is empty, so the
canonical fold stores `[u0, v0]`. The raw global clock is already `30`, so raw
`applyUpdate` ignores `u0` and raw `canonicalStoreView` shows only `[v0]`.
Initial observation and canonical admission both hold, so `hraw` is the only
failed hypothesis.

These two witnesses are the sequence-level counterparts of the preserved wave-7
one-step boundary/impossibility results.

## 6. Preserved wave-7 results

All wave-7 theorems keep their exact statements. The module re-exports them
under the wave-8 namespace:

```lean
theorem canonical_admission_strictly_weaker_than_raw_clock
theorem no_canonical_preserving_raw_announcement_extension
theorem raw_conflicting_announcement_counterexample_preserved
theorem ambiguous_without_canonical_preserved
theorem canonical_conflicting_announcement_rejection_preserved
```

Consequences preserved:

* raw `applyGossip` is still **not** a refinement of canonical admission;
* the per-slot/global-clock boundary is still a strict separation;
* no raw-append extension of `channel_announcement` can preserve
  `CanonicalAnnouncements` from the empty store;
* conflicting announcements are still accepted by raw `applyGossip` and remain
  ambiguous without a canonical selector;
* the canonical path still rejects the conflicting re-announcement.

No existing theorem was weakened, renamed, or removed. The additions to
`LnLean/Routing/Gossip.lean` are list primitives only:
`replacedAnnouncements`, `replacedUpdates`, their membership/soundness/nodup/
subsingleton/empty laws, and
`mem_insertReplacing_iff_not_replaced` /
`mem_insertUpdateCanonical_iff_not_replaced`. They do not change
`applyGossip`, `GossipState.applyUpdate`, `applyUpdateAttributed`,
`applyUpdateDirected`, `dedupAnnouncements`, `insertReplacing`,
`insertUpdateCanonical`, or any existing statement.

## 7. Axiom audit

`#print axioms` was run from an external audit file importing the module. The
audited declarations are:

```text
epochFold_gossip_eq_canonicalStoreView_rawFold
StoreEpoch.epochFold_store_eq_foldl
StoreEpoch.epochFold_viewConsistent
StoreEpoch.epochFold_viewBounded
StoreEpoch.epochFold_stored_announcement_has_install_epoch
StoreEpoch.epochFold_stored_update_has_install_epoch
realistic_epoch_store_history
realistic_history_records_supersession
realistic_rejected_messages_do_not_increment_epoch
realistic_admitted_sequence_square
realistic_rejected_conflict_breaks_refinement
clock_boundary_sequence_breaks_refinement
canonical_admission_strictly_weaker_than_raw_clock
no_canonical_preserving_raw_announcement_extension
raw_conflicting_announcement_counterexample_preserved
ambiguous_without_canonical_preserved
canonical_conflicting_announcement_rejection_preserved
```

Every result depends only on a subset of:

```text
propext
Quot.sound
Classical.choice
```

No `sorryAx`, no user `axiom`, and no other axiom was reported.

## 8. Forbidden-construct scan

A comment-stripped scan of the two owned Lean files for

```text
sorry | axiom | admit | native_decide | unsafe | @[implemented_by]
```

reports **0 code occurrences** in:

* `LnLean/Proofs/Routing/GossipStoreEpochTargets.lean`,
* `LnLean/Routing/Gossip.lean`.

The module docstring mentions the forbidden names only in prose ("No `sorry`,
no `axiom`, …"), which is not a code occurrence. The build confirms that the
module contains no `sorry` (a `sorry` would emit a declaration warning).

## 9. Hypotheses and model boundaries

### 9.1 Why the sequence square is the strongest true statement

The square is an *observation* statement:

> if the epoch store starts as the canonical observation of the raw store, and
> every message is canonically admitted, and the raw global clock admits every
> update at the actual raw state, then the epoch fold's latest store is exactly
> the canonical observation of the raw fold.

It does not assert that raw `applyGossip` and canonical admission agree. The
canonical gate set is strictly stronger than raw acceptance in some dimensions
(signature, registration, per-slot supersession) and strictly weaker in one
dimension (the raw global clock), so an unconditional equality is false in both
directions. The two witnesses in §5 isolate the two failure modes.

### 9.2 Version view

`ViewConsistent` says a channel or directional slot has an install epoch exactly
when the current store holds a record for it. `ViewBounded` says no install
epoch is in the future. Both are preserved by `epochStep` and `epochFold`.
Consequently, every stored record in a non-empty fold has a bounded install
epoch. This makes the epoch maps a genuine view of the store rather than a
detached log.

### 9.3 Out of scope

* Epochs are **not** encoded on the wire; BOLT 7 has no such field.
* Node announcements remain append-only on both paths (`RT-02`).
* The signature model is abstract; `SigVerifier` is an uninterpreted predicate.
* No liveness, chain, UTXO, or rate-limit property is proved.

## 10. Integration steps

1. `LnLean/Routing/Gossip.lean` gains only the replacement-removal primitives;
   it builds with `lake build LnLean.Routing.Gossip` (7 jobs).
2. `LnLean/Proofs/Routing/GossipStoreEpochTargets.lean` imports
   `GossipRawRefinementTargets` and builds with 14 jobs.
3. The wave-8 integrator already added
   `import LnLean.Proofs.Routing.GossipStoreEpochTargets` at `LnLean.lean:141`
   and registered the two main theorems in `Obligations.lean`,
   `Traceability.lean`, and `PhaseC3/AxiomAudit.lean` (commit `9bafdab`).
   This lane did not edit those files.
4. Downstream code should use `epochStep` / `epochFold` for canonical history,
   and `ViewConsistent` / `ViewBounded` when it needs install-epoch soundness.
   The `replaced` lists are suitable as an audit/supersession log.
5. The current worktree contains 740 additional lines beyond `9bafdab`
   (§6–§9: preserved aliases, concrete witnesses, public statements); a
   follow-up integration commit is required to capture them. This lane does not
   perform Git writes.

## 11. Blockers

None.

Caveats, not blockers:

* no full `lake build` was run; the lane build is the prescribed module target;
* the epoch counter is model-side, not a wire field;
* `RT-02` (node-announcement canonicalisation) remains open by design;
* signature unforgeability remains an assumption, not a theorem.

## 12. RT-01 recommendation

**Keep `RT-01` closed.** The lane supplies the strongest true refinement
statement available for the current raw/canonical model:

* a canonical replacement-history and epoch API,
* an unconditional epoch/canonical store square,
* a conditional sequence-level epoch/raw observation square,
* exact necessity witnesses for the two nontrivial hypotheses,
* preserved wave-7 non-refinement, boundary, and impossibility results.

Do **not** reopen `RT-01` to ask for an unconditional raw `applyGossip`
refinement: wave 7 proved that false, and the wave-8 divergence witnesses show
the sequence-level version would be false too. Any future work should target
`RT-02` (node announcements), a wire-level versioning design, or a stronger
signature model, not a weakening of the raw semantics.
