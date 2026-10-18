# S4-HTLC-GLOBAL — direction-tagged channel-wide HTLC ids (`HT-01`)

**Lane:** `S4-HTLC-GLOBAL`
**Repository:** `/home/ubuntu/ln-lean-repair`
**Branch:** `repair/integrated` (base `47189fe`)
**Files written/edited (within lane ownership):**
* `LnLean/Channel/HTLC.lean` — **195 added, 0 removed** (purely additive)
* `LnLean/Proofs/Channel/HtlcGlobalIdTargets.lean` — new
* this report

No catalog, traceability, root-import, axiom-audit, docs, scripts, or other
lanes' files were edited.

## Verdict

`HT-01` is addressed at the model level by adding the faithful channel-wide
namespace `HTLCTag = Direction × Nat` with `HTLCRecord.tag r = (r.direction,
r.id)`. For every book built by the BOLT 2 allocator (`HtlcBook.Reachable`), the
tagged map is injective on the live HTLC set and the live tagged-id list is
pairwise distinct, **with no `CrossDisjoint` assumption**.  Because a reachable
book contains only live records, the same statement also holds over the whole
`b.records` list (`reachable_tagged_id_unique_all`,
`reachable_taggedIds_nodup`).

The existing per-sender and conditional results are untouched:
`HTLC.dir_id_unique`, `HTLC.id_unique_of_reachable_cross`,
`HtlcBook.cross_direction_duplicate`,
`HtlcBook.reachable_cross_direction_duplicate`,
`liveHtlcIdsNodup_unconditional_false`, and
`addHTLC_same_id_distinct_amounts_ok` still have exactly their old signatures
and proofs. `git diff --numstat` for `HTLC.lean` is `195 0`.

## Exact signatures

### Namespace definitions (in `LnLean/Channel/HTLC.lean`)

```lean
LnLean.Channel.HTLCTag : Type
-- definitionally: Direction × Nat

LnLean.Channel.HTLCRecord.tag (r : HTLCRecord) : HTLCTag
-- definitionally: (r.direction, r.id)

LnLean.Channel.HTLCRecord.tag_eq_iff {r1 r2 : HTLCRecord} :
  r1.tag = r2.tag ↔ r1.direction = r2.direction ∧ r1.id = r2.id

LnLean.Channel.HTLCRecord.direction_eq_of_tag_eq {r1 r2 : HTLCRecord}
  (h : r1.tag = r2.tag) : r1.direction = r2.direction

LnLean.Channel.HTLCRecord.id_eq_of_tag_eq {r1 r2 : HTLCRecord}
  (h : r1.tag = r2.tag) : r1.id = r2.id

LnLean.Channel.HTLCRecord.tag_ne_of_direction_ne {r1 r2 : HTLCRecord}
  (h : r1.direction ≠ r2.direction) : r1.tag ≠ r2.tag

LnLean.Channel.HTLCRecord.tag_ne_of_id_ne {r1 r2 : HTLCRecord}
  (h : r1.id ≠ r2.id) : r1.tag ≠ r2.tag

LnLean.Channel.taggedIds (hs : List HTLCRecord) : List HTLCTag
LnLean.Channel.HtlcBook.liveTags (b : HtlcBook) : List HTLCTag
LnLean.Channel.HtlcBook.liveTagsOf (b : HtlcBook) (dir : Direction) : List HTLCTag
```

Supporting injectivity/Nodup API:

```lean
LnLean.Channel.nodup_map_of_inj_on {α β : Type} {l : List α} {f : α → β}
  (hl : l.Nodup) (hinj : ∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) :
  (l.map f).Nodup

LnLean.Channel.nodup_of_map_id_nodup {l : List HTLCRecord}
  (h : (l.map HTLCRecord.id).Nodup) : l.Nodup

LnLean.Channel.eq_of_tag_eq_of_dir_nodup (l : List HTLCRecord)
  (hnd : ∀ dir : Direction,
    ((l.filter (fun r => decide (r.direction = dir))).map HTLCRecord.id).Nodup) :
  ∀ r1 ∈ l, ∀ r2 ∈ l, r1.tag = r2.tag → r1 = r2

LnLean.Channel.HtlcBook.liveOf_nodup (b : HtlcBook) (hb : b.WF) (dir : Direction) :
  (b.liveOf dir).Nodup

LnLean.Channel.HtlcBook.htlcSet_nodup_of_wf (b : HtlcBook) (hb : b.WF) :
  (htlcSet b.records).Nodup
```

### Main theorems (in `LnLean/Proofs/Channel/HtlcGlobalIdTargets.lean`)

```lean
-- allocator-invariant form
LnLean.Channel.HtlcBook.tagged_id_unique_of_wf (b : HtlcBook) (hb : b.WF) :
  ∀ r1 ∈ htlcSet b.records, ∀ r2 ∈ htlcSet b.records,
    r1.tag = r2.tag → r1 = r2

LnLean.Channel.HtlcBook.liveTags_nodup_of_wf (b : HtlcBook) (hb : b.WF) :
  b.liveTags.Nodup

-- the deliverable: unconditional over Reachable, no CrossDisjoint
LnLean.Channel.HtlcBook.reachable_tagged_id_unique {b : HtlcBook} (hb : b.Reachable) :
  ∀ r1 ∈ htlcSet b.records, ∀ r2 ∈ htlcSet b.records,
    r1.tag = r2.tag → r1 = r2

LnLean.Channel.HtlcBook.reachable_liveTags_nodup {b : HtlcBook} (hb : b.Reachable) :
  b.liveTags.Nodup

-- subtype/function form
LnLean.Channel.HtlcBook.reachable_tag_injective {b : HtlcBook} (hb : b.Reachable) :
  Function.Injective
    (fun r : {r : HTLCRecord // r ∈ htlcSet b.records} => r.1.tag)

-- the tagged result recovers the old per-sender theorem
LnLean.Channel.HtlcBook.tagged_uniqueness_implies_dir_unique {b : HtlcBook}
  (h : ∀ r1 ∈ htlcSet b.records, ∀ r2 ∈ htlcSet b.records,
    r1.tag = r2.tag → r1 = r2)
  (dir : Direction) :
  ∀ r1 ∈ b.liveOf dir, ∀ r2 ∈ b.liveOf dir, r1.id = r2.id → r1 = r2

LnLean.Channel.HtlcBook.reachable_dir_unique_via_tags {b : HtlcBook}
  (hb : b.Reachable) (dir : Direction) :
  ∀ r1 ∈ b.liveOf dir, ∀ r2 ∈ b.liveOf dir, r1.id = r2.id → r1 = r2
```

The whole record list (reachable books contain only live records, since
`HtlcBook` has no settle/remove operation):

```lean
LnLean.Channel.HtlcBook.reachable_all_live {b : HtlcBook} (hb : b.Reachable) :
  ∀ r ∈ b.records, r.isLive = true

LnLean.Channel.HtlcBook.reachable_htlcSet_eq_records {b : HtlcBook}
  (hb : b.Reachable) : htlcSet b.records = b.records

LnLean.Channel.HtlcBook.reachable_taggedIds_nodup {b : HtlcBook}
  (hb : b.Reachable) : (taggedIds b.records).Nodup

LnLean.Channel.HtlcBook.reachable_tagged_id_unique_all {b : HtlcBook}
  (hb : b.Reachable) :
  ∀ r1 ∈ b.records, ∀ r2 ∈ b.records, r1.tag = r2.tag → r1 = r2
```

### Cross-counterexample connection

```lean
LnLean.Channel.HtlcBook.crossBook_liveTags :
  HtlcBook.crossBook.liveTags =
    [(Direction.remote, 0), (Direction.local, 0)]

LnLean.Channel.HtlcBook.crossBook_liveTags_nodup :
  HtlcBook.crossBook.liveTags.Nodup

LnLean.Channel.HtlcBook.crossBook_duplicate_distinct_tags :
  ∃ r1 ∈ htlcSet HtlcBook.crossBook.records,
    ∃ r2 ∈ htlcSet HtlcBook.crossBook.records,
      r1 ≠ r2 ∧ r1.id = r2.id ∧ r1.tag ≠ r2.tag

LnLean.Channel.HtlcBook.crossBook_not_crossDisjoint :
  ¬ HtlcBook.crossBook.CrossDisjoint

LnLean.Channel.HtlcBook.cross_direction_duplicate_tagged :
  HtlcBook.crossBook.WF ∧
    ¬ liveHtlcIdsNodup HtlcBook.crossBook.records ∧
      HtlcBook.crossBook.liveTags.Nodup

LnLean.Channel.HtlcBook.cross_direction_duplicate_tagged_pair :
  HtlcBook.crossBook.WF ∧
    ¬ liveHtlcIdsNodup HtlcBook.crossBook.records ∧
      HtlcBook.crossBook.liveTags.Nodup ∧
        (∃ r1 ∈ htlcSet HtlcBook.crossBook.records,
          ∃ r2 ∈ htlcSet HtlcBook.crossBook.records,
            r1 ≠ r2 ∧ r1.id = r2.id ∧ r1.tag ≠ r2.tag)

LnLean.Channel.HtlcBook.reachable_cross_direction_duplicate_tagged :
  ∃ b : HtlcBook, b.Reachable ∧ ¬ liveHtlcIdsNodup b.records ∧
    b.liveTags.Nodup

LnLean.Channel.HtlcBook.tagged_namespace_without_cross :
  HtlcBook.crossBook.Reachable ∧
    ¬ HtlcBook.crossBook.CrossDisjoint ∧
      HtlcBook.crossBook.liveTags.Nodup
```

### Scope theorem (why `Reachable` is required)

```lean
LnLean.Channel.tag_not_injective_on_records :
  ¬ Function.Injective (HTLCRecord.tag : HTLCRecord → HTLCTag)
```

`tag` deliberately forgets amount, payment hash, expiry, and state. The tagged
uniqueness result is therefore about the live set of a reachable/well-formed
book, not about arbitrary hand-built records.

### Catalog-facing aliases (still in the new proof module)

```lean
LnLean.Channel.HTLC.tagged_id_unique_of_reachable {b : HtlcBook} (hb : b.Reachable) :
  ∀ r1 ∈ htlcSet b.records, ∀ r2 ∈ htlcSet b.records,
    r1.tag = r2.tag → r1 = r2

LnLean.Channel.HTLC.tagged_ids_nodup_of_reachable {b : HtlcBook} (hb : b.Reachable) :
  b.liveTags.Nodup

LnLean.Channel.HTLC.tagged_ids_nodup_of_reachable_records {b : HtlcBook}
  (hb : b.Reachable) : (taggedIds b.records).Nodup

LnLean.Channel.HTLC.tagged_id_unique_of_reachable_records {b : HtlcBook}
  (hb : b.Reachable) :
  ∀ r1 ∈ b.records, ∀ r2 ∈ b.records, r1.tag = r2.tag → r1 = r2

LnLean.Channel.HTLC.cross_direction_duplicate_distinct_tags :
  ∃ r1 ∈ htlcSet HtlcBook.crossBook.records,
    ∃ r2 ∈ htlcSet HtlcBook.crossBook.records,
      r1 ≠ r2 ∧ r1.id = r2.id ∧ r1.tag ≠ r2.tag

LnLean.Channel.HTLC.cross_direction_duplicate_tagged :
  HtlcBook.crossBook.WF ∧
    ¬ liveHtlcIdsNodup HtlcBook.crossBook.records ∧
      HtlcBook.crossBook.liveTags.Nodup
```

## Proof strategy

1. **Namespace.** `tag r = (r.direction, r.id)` is a projection of existing
   fields. `tag_eq_iff` decomposes tag equality into direction and id equality.
2. **Per-sender injectivity.** `eq_of_tag_eq_of_dir_nodup` uses the two
   per-direction `Nodup` id lists (from `WF`) and the existing list lemma
   `eq_of_id_eq_of_htlcIds_nodup`.
3. **Record-level `Nodup`.** `htlcSet_nodup_of_wf` proves the live record list
   has no duplicate record: per-sender `Nodup` rules out duplicates within a
   sender, and a local/remote pair cannot be the same record because a record
   has one direction. The direction-filter permutation lemma
   (`htlc_filter_direction_perm`) transports this to `htlcSet`.
4. **Tagged `Nodup`.** `nodup_map_of_inj_on` combines the record-level `Nodup`
   with tag injectivity. `liveTags_nodup_of_wf` is the allocator-invariant form.
5. **Reachable form.** `reachable_wf` turns the constructor trace into `WF`;
   `reachable_tagged_id_unique` / `reachable_liveTags_nodup` therefore quantify
   only over `b.Reachable`, with no `CrossDisjoint` and no id-distinctness
   hypothesis.
6. **Whole record list.** `reachable_all_live` (induction on the constructor
   trace: both `insert` and `add` only prepend an allocated live record) and
   `reachable_htlcSet_eq_records` (the live filter is the identity) transport
   the live-set result to `b.records`; hence
   `reachable_tagged_id_unique_all` and `reachable_taggedIds_nodup`.
7. **Counterexample.** `crossBook_liveTags` computes the two tags
   `(.remote, 0)` and `(.local, 0)`. They differ even though both bare ids are
   `0`; `crossBook_duplicate_distinct_tags` exhibits the same two live records
   as the old duplicate pair but with distinct tags. `cross_direction_duplicate`
   is reused (not reproved) for the bare-id non-uniqueness half.

## Build result

Toolchain: `/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0`.
All builds used the shared lock and `LEAN_NUM_THREADS=1`.

| Command | Result |
|---|---|
| `lake build LnLean.Channel.HTLC` | `Build completed successfully (9 jobs)`, RC 0 |
| `lake build LnLean.Proofs.Channel.HtlcGlobalIdTargets` | `Build completed successfully (10 jobs)`, RC 0 |
| final combined `lake build LnLean.Channel.HTLC LnLean.Proofs.Channel.HtlcGlobalIdTargets` | `Build completed successfully (10 jobs)`, RC 0 |
| `lake build LnLean.Channel.HTLCLaws LnLean.Proofs.Channel.HTLCProps LnLean.Proofs.WaveD.D16 LnLean.Proofs.Common LnLean.Proofs.PhaseC2.HTLCUniqueIds` | `Build completed successfully (140 jobs)`, RC 0 |
| `lake build LnLean.Proofs.PhaseC3.AxiomAudit` (direct downstream of `HTLC`) | `Build completed successfully (86 jobs)`, RC 0 |

The downstream build includes `LnLean.Proofs.Obligations` and
`LnLean.Proofs.Traceability` and completed RC 0. The only warnings came from an
unrelated lane's `LnLean.Proofs.Routing.GossipProps` (`if_pos`/`if_neg`
deprecations), not from these files.

No full `lake build`, `collect-obligations.py`, or Git write command was run.

## Axiom result

`#print axioms` was run on **all 42 new theorems** (18 in
`LnLean/Channel/HTLC.lean`, 24 in the new target module). Results:

* `does not depend on any axioms` (10): `tag_fst`, `tag_snd`, `tag_eq_iff`,
  `direction_eq_of_tag_eq`, `id_eq_of_tag_eq`, `tag_congr`,
  `tag_ne_of_direction_ne`, `tag_ne_of_id_ne`, `crossBook_liveTags`,
  `crossBook_liveTags_nodup`.
* `depends on axioms: [propext]` (4): `tagged_uniqueness_implies_dir_unique`,
  `crossBook_not_crossDisjoint`, `tagged_namespace_without_cross`,
  `reachable_all_live`.
* All remaining 28 new theorems: `[propext, Quot.sound]`.

No new declaration depends on `sorryAx`, `Classical.choice`,
`Lean.ofReduceBool`, `implemented_by`, or any other axiom.

## Forbidden-construct scan

```sh
grep -nE "sorry|admit|native_decide|unsafe|implemented_by|^axiom | axiom " \
  LnLean/Channel/HTLC.lean \
  LnLean/Proofs/Channel/HtlcGlobalIdTargets.lean
```

Result: **no matches** in either file.

## Retained API / counterexample check

`git diff --numstat -- LnLean/Channel/HTLC.lean` → `195 0`; there are no
deleted lines. In particular these are byte-for-byte unchanged and still build:

```lean
LnLean.Channel.HTLC.dir_id_unique
LnLean.Channel.HTLC.id_unique_of_reachable_cross
LnLean.Channel.HtlcBook.cross_direction_duplicate
LnLean.Channel.HtlcBook.reachable_cross_direction_duplicate
LnLean.Channel.liveHtlcIdsNodup_unconditional_false
LnLean.Channel.addHTLC_same_id_distinct_amounts_ok
```

`cross_direction_duplicate` is also *used* by the new theorem
`cross_direction_duplicate_tagged`, so the counterexample remains visible from
the new positive result rather than being hidden.

## Model/protocol choice

* **Both counters are `Nat`.** `HtlcBook.nextLocalId` and
  `HtlcBook.nextRemoteId` are independent `Nat`s, both start at `0`, and
  `allocate`/`push` advance exactly one of them. `(direction, id)` therefore
  retains every bit of the allocator state relevant to identity.
* **Is a tagged id the right BOLT 2 interpretation?** For an endpoint, yes:
  `update_add_htlc.id` is per sender and is interpreted together with the
  message direction (`refs/bolts/02-peer-protocol.md:2838-2843`); rust-lightning
  mirrors that with `next_holder_htlc_id` / `next_counterparty_htlc_id`
  (`lightning/src/ln/channel.rs:3719-3720`). The channel-wide identity is the
  pair, not the bare `id`.
* **This is not a new wire format.** BOLT 2 sends only the per-sender id. A
  single-`Nat` encoding (e.g. `2*id` for local, `2*id+1` for remote) is also
  injective, but it is an implementation choice with no BOLT wire meaning. The
  model uses the pair and documents it as a namespace view.
* **No cross-channel id.** The namespace is channel-wide, not network-wide;
  a channel identifier is not part of `HtlcBook` and `HT-01` does not need one.
* **No cryptographic or MPP identity claim.** The tag identifies the HTLC
  slot; it is not a payment hash, preimage, or MPP set id.

## Scope caveats

1. The global theorem is unconditional over `HtlcBook.Reachable` (equivalently
   `WF`), not over arbitrary `HTLCRecord` lists. An arbitrary list can still
   contain duplicate records; `tag_not_injective_on_records` makes the boundary
   explicit.
2. The tag is a model-side projection. A caller that constructs `HTLCRecord`
   directly, bypassing `HtlcBook.allocate`, can still produce duplicate
   direction/id pairs. The allocator is the protocol-faithful constructor.
3. The theorem is intra-channel and does not add a channel id. Two different
   channels can share tagged ids.
4. The per-sender counter semantics are unchanged; the new theorem refines,
   rather than replaces, `HTLC.dir_id_unique`. The catalog's existing narrowed
   wording and conditional `CrossDisjoint` form remain valid.
5. No claim is made about wire encoding, BigSize/TLV, or rust-lightning
   serialization; this is a state-model namespace only.

## Integration steps (parent-owned files; not edited here)

1. **Root import.** Add the new module to the generated root, preferably by
   running `scripts/regen-root.sh`, which should add:

   ```lean
   import LnLean.Proofs.Channel.HtlcGlobalIdTargets
   ```

   in alphabetical position near the other `LnLean.Proofs.Channel` imports in
   `LnLean.lean`.

2. **Obligations (`LN-HT-004`).** Extend the existing narrowed row rather than
   replacing the per-sender target:

   ```lean
   claim := "An HTLC id is unique among the live HTLCs of one sender in a channel; the direction-tagged channel-wide id (direction, id) is unique over every reachable book; the bare global form holds only under explicit cross-direction disjointness.",
   leanTarget := "LnLean.Channel.HTLC.dir_id_unique; LnLean.Channel.HTLC.id_unique_of_reachable_cross; LnLean.Channel.HTLC.tagged_id_unique_of_reachable; LnLean.Channel.HTLC.tagged_ids_nodup_of_reachable; LnLean.Channel.HTLC.cross_direction_duplicate_tagged",
   ```

3. **Traceability.** Add the new declarations to the target→module maps and the
   module list (`LnLean/Proofs/Traceability.lean`):

   ```lean
   , ⟨"LnLean.Channel.HTLC.tagged_id_unique_of_reachable", "LnLean.Proofs.Channel.HtlcGlobalIdTargets"⟩
   , ⟨"LnLean.Channel.HTLC.tagged_ids_nodup_of_reachable", "LnLean.Proofs.Channel.HtlcGlobalIdTargets"⟩
   , ⟨"LnLean.Channel.HTLC.cross_direction_duplicate_tagged", "LnLean.Proofs.Channel.HtlcGlobalIdTargets"⟩
   ```

   and append `"LnLean.Proofs.Channel.HtlcGlobalIdTargets"` to the module list.

4. **Axiom audit.** Add

   ```lean
   import LnLean.Proofs.Channel.HtlcGlobalIdTargets
   ```

   to `LnLean/Proofs/PhaseC3/AxiomAudit.lean` and (optionally) the three
   `#print axioms` lines for the catalog-facing aliases. The measured results
   are `[propext, Quot.sound]`, so they meet the audit policy.

5. **Roadmap.** Close or narrow `HT-01` in `docs/OPEN-ISSUES.md`, recording
   `tagged_id_unique_of_reachable`, `reachable_liveTags_nodup`,
   `cross_direction_duplicate_tagged`, and the retained
   `cross_direction_duplicate`. Recommended wording: “Global uniqueness is
   false for the bare BOLT 2 per-sender id; it holds unconditionally for the
   direction-tagged namespace over reachable books.”

6. **Generated indexes.** Re-run the parent's usual index generation
   (`collect-obligations.py` / anchor collection) only in the integration pass;
   this lane did not run them.

## Blockers

None for the claimed result. The only non-removable limitation is the one the
issue itself describes: BOLT 2 has no channel-wide bare id, so the channel-wide
claim is necessarily about the tagged `(direction, id)` namespace. That is now
mechanized, together with the proof that the old duplicate remains a duplicate
of bare ids while becoming two distinct tagged ids.
