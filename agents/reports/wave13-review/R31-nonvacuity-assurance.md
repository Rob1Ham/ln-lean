# R31 — Non-vacuity, traceability, axiom, and assumption review
**Status:** read-only review
**Pins:** LDK Node `fa123fed131e27ecc420b77fa7086fcf1ddaebb8`, LDK Server `c17dc11dde38f88c53457039ddf30c6b90a63ba2`
**Review branch:** `repair/integrated` at `f7f062817c185cd70004bb26c652deb99c6fd4bd` (no branch, commit, or non-report file changes made)

## 1. Scope and current Lean surface

This lane reviews the assurance surface of the 51-row catalog, not protocol
coverage in general. The question is whether the current gate counts,
traceability tables, axiom audit, and non-vacuity registry actually support the
claims made for them, and whether the ID-indexed `Traceability` refactor left
unchecked metadata paths.

The short answer is:

* The gate counts **target occurrences**, not unique declarations. The catalog
  has 51 `proved` rows, **294 target occurrences, 282 unique declarations, and
  12 duplicate ECDSA declarations** shared by `LN-L1-001` and `LN-L1-004`.
* The axiom audit contains **393 `#print axioms` commands and 435 registry
  names**. 72 of the 282 unique catalog targets are not printed at all, and 35
  are not even in the registry.
* The ID-indexed `Traceability` refactor made the catalog-to-table target text
  check kernel-enforced, but it did **not** tie `declIds` to declaration names
  or modules, and the two Markdown tables are still literal copies whose IDs
  (not claim/target columns) are checked.
* Several `.proved` rows are definitional restatements or hypothesis
  re-exports. `LN-SEC-004` is the clearest case: the theorem is exactly its
  hypothesis. `ThreatModelProps` nonetheless states that the ten-invariant
  catalog "contains no predicate that is assumed rather than proved", while
  5/10 invariant proofs are identity/projection terms.
* The 30-entry non-vacuity registry is honest about its scope, but only 4 of its
  entries name a catalog target by basename. There is no theorem mapping the
  registry to the 282 unique catalog targets.

### 1.1 Current gate surface

| Artifact | Current shape | What is actually enforced |
|---|---|---|
| `LnLean/Proofs/Obligations.lean` | 51 rows; 8 domains; `leanTarget` is a semicolon-separated list | `check-catalog.py --audit` resolves every target to a declaration and rejects `sorry`/`axiom` targets (`scripts/check-catalog.py:495-560`) |
| `LnLean/Proofs/Traceability.lean` | `targetTable` (51 entries), `provedTable` (51 entries, 294 `declIds` references), `provedDeclarations` (282 entries, IDs `0..281`) | target text equality to the catalog (`:830-833`), non-empty `declIds` (`:855-857`), IDs exist in the snapshot (`:860-866`), every snapshot ID is used (`:868-873`), IDs contiguous (`:881-883`) |
| `LnLean/Proofs/PhaseC3/AxiomAudit.lean` | 393 `#print axioms` commands (`:117-570`); `auditedTheorems` registry with 435 names (`:579-1016`); `auditedTheorems_length = 435` (`:1018`) | only that the registry literal has length 435; no theorem or script ties the registry to the print commands |
| `LnLean/Proofs/Model/NonVacuityTargets.lean` | 30-entry `witnessRegistry` (`:649-801`); `witnessRegistry_sound` (`:807-809`) | each entry stores its own proof and soundness is a dependent-list projection; scope warning at `:4-10` and `:39-42` |
| `LnLean/Proofs/Security/ThreatModelProps.lean` | 10 `inv*_proved` theorems (`:622-660`), `catalog_predicates_discharged` (`:666-667`) | only the length of `coreInvariants`, not the strength or distinctness of the ten proofs |

### 1.2 The ID-indexed refactor

Commit `b6a7259` ("[WAVE10] derive traceability tables from the catalog and
source map") changed `provedTable` from a list of target strings to
`ProvedEntry` records carrying `targetIndex : Nat` and `declIds : List Nat`
(`LnLean/Proofs/Traceability.lean:119-127`, `:281-333`). This made target-list
comparison cheaper and removed a large duplicated string list. It did not add a
kernel link from a declaration ID to the target text or to the target's module
list:

* `proved_decls_in_snapshot` only checks that each `declId` occurs somewhere in
  `provedDeclarations` (`:860-866`).
* `proved_decl_modules_lnean` only checks each declaration module against the
  fixed `lneanModules` list (`:892-894`), not against
  `TargetEntry.modules` for the target it supposedly implements.
* `target_modules_lnean` only checks target modules against `lneanModules`
  (`:841-845`).
* The file's own docstring says the `modules`/`area`/`number` fields are not
  parsed by Lean and that the intended external parse check is a script
  (`:70-80`). No current script parses `targetTable`; `rg -n
  'targetTable|provedDeclarations|provedTable' scripts/` returns no hits.

The two stale docstrings below are evidence that this metadata layer already
drifts:

* `proved_declarations_nodup` is documented as "no duplicate declaration name"
  but proves `(provedDeclarations.map (fun p => p.id)).Nodup` (`:875-877`).
* `proved_row_count` is documented as "Exactly 48 rows are `proved`" but proves
  `.length = 51` (`:898-900`).

### 1.3 Rows examined closely

| Row | Target(s) | Shape of the proof |
|---|---|---|
| `LN-CH-004` (`Obligations.lean:193`) | `LnLean.Security.advance_monotone` | `s.commitmentNumber ≤ s.advance.commitmentNumber`; `advance` is a canned `+1` (`Invariants.lean:319-325`) |
| `LN-HT-005` (`:252`) | `LnLean.Security.revoked_commitment_is_old` | projection of `Revoked := commitmentNumber < currentCommitment` (`Invariants.lean:261-271`) |
| `LN-HT-006` (`:258`) | `LnLean.Security.breach_penalty_spends_both` | second conjunct of `Punishable` (`Invariants.lean:292-301`) |
| `LN-PR-002` (`:274`) | `LnLean.Protocol.Handshake.channel_ready_gate` | `s.ready = true ↔ channelReadySent ∧ channelReadyReceived`; `ready` is exactly the conjunction (`Handshake.lean:113-130`; alias at `D18.lean:329-337`) |
| `LN-RT-001` (`:317`) | `LnLean.Security.Route.wellFormed_{connected,capacity,nonempty}` | three projections of `Route.WellFormed` (`Invariants.lean:356-380`) |
| `LN-SEC-004` (`:426`) | `LnLean.Security.partial_synchrony_delivers` | `hps m hm`; `PartiallySynchronous` is definitionally the conclusion (`Invariants.lean:481-492`) |
| `LN-SEC-007` (`:449`) | the eight `NonVacuityTargets` headline targets | 30-entry registry; `witnessRegistry_sound` is a registry projection (`NonVacuityTargets.lean:649-809`) |

### 1.4 Scope exclusions

This lane does not re-audit crypto assumptions (`C1`-`C8`), does not propose a
splice model, and does not run a full build. Splicing is covered by R25; the
splice row in §3 is a boundary statement, not a new model proposal. No code,
catalog, docs, or script file is edited by this lane.

## 2. LDK datapoints (with `file:line`)

LDK Node and LDK Server expose a stricter readiness notion than the Lean
handshake model. The relevant public surface is:

| Datapoint | Evidence | What it establishes |
|---|---|---|
| Funding confirmation fields | `ldk-node/src/types.rs:555-561` (`confirmations_required`, `confirmations`) | Readiness depends on a funding-confirmation threshold selected by the fundee. |
| `is_channel_ready` | `ldk-node/src/types.rs:564-568` | "both parties have exchanged `channel_ready` messages, and the channel is not currently being shut down"; the two messages are exchanged "upon independently verifying that the required confirmations count ... has been reached". |
| `is_usable` | `ldk-node/src/types.rs:569-573` | Strict superset of `is_channel_ready`: also requires the peer to be connected and the channel not to be negotiating shutdown. |
| `ChannelReady` event | `ldk-node/src/event.rs:272-293` | Emitted for a new channel and for an existing channel "spliced and ... ready with the new funding output"; `funding_txo` is the current funding output. |
| `splice_in` API | `ldk-node/src/lib.rs:1806-1837`, `:1949-1956` | Splice-in requires a channel whose funding outpoint exists ("channel not yet ready" otherwise); the API is explicitly experimental. |
| Per-direction channel records | `ldk-node/src/graph.rs:64-72` | A `ChannelInfo` has independent `one_to_two` and `two_to_one` `ChannelUpdateInfo` records. |
| Per-direction update fields | `ldk-node/src/graph.rs:95-109` | `last_update : u32` and `enabled : bool` are per direction; `enabled` is "whether the channel can be currently used for payments (in this one direction)". |
| Usable-channel wait | `ldk-server/e2e-tests/src/lib.rs:920-944` | The e2e harness waits for `is_usable`, periodically mines blocks to trigger chain sync, and prints both `is_ready` and `is_usable` on timeout. |
| Readiness filter | `ldk-server/ldk-server/src/main.rs:361-366` | Server metrics/readiness collection filters on `channel.is_channel_ready`. |
| Probing filter | `ldk-node/src/probing.rs:603` | Probe selection filters on `c.is_usable && c.short_channel_id.is_some()`. |

The important negative datapoint is that LDK does **not** promise bounded message
delivery after a GST. The Lean anchor for `LN-SEC-004`
(`docs/TRACEABILITY.md:63`) points at
`refs/rust-lightning/lightning/src/ln/channelmanager.rs:17831`, which is
`handle_channel_reestablish`, i.e. the retransmission path, not a partial
synchrony guarantee. The BOLT 1 "Lightning Message Format" label on that row is
also semantically unrelated to delivery timing.

## 3. Gap matrix

| Behavior | Lean status | LDK evidence | Gap / counterexample | Priority |
|---|---|---|---|---|
| Both `channel_ready` messages are necessary for `ready` | **Covered faithfully at flag level** (`Handshake.ready_iff`, `D18.channel_ready_gate`) | `types.rs:564-568` | The model's `ready` is not LDK `is_channel_ready` (no confirmation depth) and not `is_usable` (no peer connectivity / shutdown). The claim is true only for the two booleans. | P1 |
| Funding confirmation depth gates readiness | **Missing** | `types.rs:555-568`; server e2e mines blocks at `e2e-tests/src/lib.rs:926-944` | `HandshakeState` has no `confirmations`/`requiredConfirmations` fields (`Handshake.lean:78-95`); the module's "What is NOT modelled" list omits the depth gate entirely. A state with both flags set is `ready` even at depth 0. | P1 |
| Peer connectivity and shutdown negotiation gate usability | **Missing** | `types.rs:569-573`; `probing.rs:603`; `main.rs:361-366` | No `peerConnected` or `shuttingDown` field exists. `channel_ready_gate` says nothing about the LDK `is_usable` strict superset. | P1 |
| `ChannelReady` after a splice, with a new funding outpoint | **Unmodelled / external** | `event.rs:272-293`; `lib.rs:1949-1956`; see R25 §1.3 | The model has a single `funding` field and no splice lifecycle. `channel_ready_gate` must not be cited as a splice-readiness theorem. | P2 |
| Per-direction `channel_update` replacement by strict timestamp | **Covered faithfully** in the canonical layer | `graph.rs:64-72`, `:95-98` | `GossipCanonicalTargets` keys by `(short_channel_id, direction)` and uses strict-timestamp supersession; the raw `Gossip.applyUpdate` remains a global append-only clock, which is documented (`Gossip.lean:281-294`). | P2 |
| BOLT 7 `enabled`/disable flag suppresses one direction | **Missing / partially covered** | `graph.rs:99-100` | `Gossip.ChannelUpdate` stores raw `channelFlags` and explicitly "does not decode individual bits" (`Gossip.lean:150-157`). No theorem relates the disable bit to routability. | P2 |
| After GST every message is delivered within delta | **Partially covered — hypothesis restatement (circular)** | No LDK bounded-delivery guarantee; the cited anchor is `handle_channel_reestablish` (`channelmanager.rs:17831`) | `PartiallySynchronous` is definitionally `∀ m, gst ≤ m.send → DeliveredWithin m (m.send+delta)` (`Invariants.lean:481-486`); the theorem is `hps m hm` (`:488-492`). Counterexample without the hypothesis: `latency := fun _ => none`. | P0 (claim/relabel) |
| A committed update never decreases the commitment number | **Partially covered — definitional** | No LDK transition is modelled for `advance` | `advance` is `{ s with commitmentNumber := s.commitmentNumber + 1 }` (`Invariants.lean:317-321`); `advance_monotone` is `Nat.le_succ` (`:323-325`). No `ChannelState` witness is registered. | P2 |
| A well-formed route is non-empty, connected, capacity-feasible | **Partially covered — definitional** | `router.rs:825`, `:2797` (anchors only) | The three targets are the three conjuncts of `Route.WellFormed` (`Invariants.lean:356-380`). No `Route` witness is registered. | P2 |
| A punishable breach spends both commitment outputs | **Partially covered — definitional** | `channel.rs:9471`, `channelmonitor.rs:5079` (anchors only) | `Punishable` literally contains `PenaltyTx.SpendsBoth ...` (`Invariants.lean:292-301`); `breach_penalty_spends_both` is `h.2`. | P2 |
| A revoked commitment is strictly older than the current one | **Partially covered — definitional** | `chan_utils.rs:518` (anchor only) | `Revoked := commitmentNumber < currentCommitment` (`Invariants.lean:261-264`); the theorem is `Nat.ne_of_lt h`. | P2 |
| "294 targets" means 294 unique declarations | **Contradicted** | N/A (internal count) | 294 is the number of target **occurrences**; 282 are unique. The 12 duplicates are exactly `EcdsaConcreteTargets`/`EcdsaDomainTargets` names shared by `LN-L1-001` and `LN-L1-004` (`Obligations.lean:80-88`, `:98-108`; `provedTable` rows `0` and `3`; `proved_declaration_ids_contiguous` asserts `List.range 282`). | P0 |
| "435 audited theorems" | **Contradicted** | N/A (internal count) | 393 `#print axioms` commands; 42 registry names are not printed; 35 unique catalog targets are absent from the registry and 72 are not printed. `auditedTheorems_length` checks only the 435-name literal. | P0 |
| Every `proved` row's `declIds` name that row's target declarations | **Missing** | N/A (internal traceability) | `proved_decls_in_snapshot` only checks ID membership; it never compares `DeclEntry.text` with `TargetEntry.text` or `DeclEntry.module` with `TargetEntry.modules`. Current data happens to pass both comparisons (0 mismatches), but no kernel check preserves that. | P0 |
| Markdown `claim`/`target` columns mirror the catalog | **Missing** | N/A (internal traceability) | `theoremIndexIds`/`traceabilityIds` are literal ID copies (`Traceability.lean:717-741`); the file docstring admits they "cannot prove that a copy matches the current file on disk" (`:83-87`). No script parses the claim/target columns. | P1 |
| Anchors are semantically relevant, not merely present | **Missing** | `verify-anchors.py:1-52` | The checker only verifies file existence and `line ≤ file length`; `LN-SEC-004` points at `handle_channel_reestablish`. The `unanchored_rows=2` count is a false positive: `verify-anchors.py:34-35` counts any line containing `UNANCHORED`, including two prose lines (`docs/TRACEABILITY.md:11`, `:74`). | P1 |

## 4. Proposed targets

The targets below are ordered by assurance value. T1-T3 close the largest
observable blind spots without changing any theorem statement. T4-T6 are small
strengthenings. T7 is an optional additive model extension. T8 is a pure
non-vacuity witness.

### T1. `LnLean.Proofs.Traceability.proved_declIds_match_target_declIds` (P0)

**Statement shape**

```lean
-- Add `declIds : List Nat` to `TargetEntry` (or keep a parallel
-- `targetDeclIds : List (List Nat)` table).  Populate it with a generator
-- that splits the catalog's semicolon-separated `leanTarget`; do not
-- hand-edit it.
theorem proved_declIds_match_target_declIds :
    provedTable.all (fun e =>
      match targetTable.get? e.targetIndex with
      | some t => decide (e.declIds = t.declIds)
      | none => false) = true := by
  decide
```

**Hypotheses:** none. The table is data; the theorem is a kernel check.

**Non-vacuity witness:** the current 51 rows and 294 references. A Python
comparison confirms the current `provedTable` references and the target
component names are already aligned (0 mismatches), so this target should pass
immediately after the generated field is populated.

**Why it is faithful:** it makes the generated target declaration list the
single source of truth for each row, rather than a second hand-transcribed list
that can drift. The generator, not the kernel, performs the string split; the
kernel then checks the row table against the generated list. It does not parse
strings in the kernel, so it does not hit the `String.splitOn` limitation
documented at `Traceability.lean:70-78`.

**Fidelity risk / feasibility / type:** low risk; medium feasibility (51-row
mechanical update); metadata strengthening, not a model extension. If adding a
field to `TargetEntry` is too invasive, a parallel `targetDeclIds` table is
acceptable but must also be generated from the catalog.

### T2. `LnLean.Proofs.Traceability.proved_decl_modules_match_target` (P0)

**Statement shape**

```lean
theorem proved_decl_modules_match_target :
    provedTable.all (fun e =>
      e.declIds.all (fun id =>
        match provedDeclarations.find? (fun d => d.id = id),
              targetTable.get? e.targetIndex with
        | some d, some t => decide (d.module ∈ t.modules)
        | _, _ => false)) = true := by
  decide
```

**Hypotheses:** none.

**Non-vacuity witness:** the current table; a Python check finds 0 module
mismatches across all 294 references. The theorem is therefore true now and
guards future edits.

**Why it is faithful:** `TargetEntry.modules` is supposed to be the module list
for the target's declarations. The current checks only compare both sides to a
fixed `lneanModules` whitelist (`:841-845`, `:892-894`), so a target could list
module A while its declaration lives in module B and both checks would pass.

**Fidelity risk / feasibility / type:** low risk; high feasibility; metadata
strengthening. Do not replace `proved_declaration_modules_lnean`; keep it as a
coarse whitelist check.

### T3. `LnLean.Proofs.PhaseC3.AxiomAudit.catalog_targets_subset_audited` (P0)

**Statement shape**

```lean
/-- Generated from the 282 unique catalog target names, not hand-edited. -/
def catalogTargetNames : List Lean.Name := [ ... ]

theorem catalog_targets_subset_audited :
    catalogTargetNames.all (fun n => auditedTheorems.contains n) = true := by
  decide
```

**Hypotheses:** none. The target forces every unique catalog target to be in
the axiom-audit registry. It currently fails: 35 names are absent, including
`LnLean.Protocol.Handshake.channel_ready_gate`,
`LnLean.Security.partial_synchrony_delivers`,
`LnLean.Security.advance_monotone`, the three `Route.wellFormed_*` targets, and
`LnLean.Routing.Gossip.update_monotone`.

**Non-vacuity witness:** after adding the 35 names, all 282 are present. The
list itself is the witness; a generated-list equality theorem should accompany
it so the list cannot be silently shortened.

**Why it is faithful:** the audit claim is "every catalog target has been
axiom-checked". Today the registry and the `#print axioms` block are two
independent hand-maintained lists. This target closes the registry side. A
companion script must close the print side because Lean cannot inspect command
syntax.

**Companion checker (required for the full claim):** extend
`scripts/check-catalog.py` (or add `scripts/check-axiom-audit.py`) to parse
`#print axioms <name>` lines from `AxiomAudit.lean` and assert:

1. the print set has no duplicates;
2. every `catalogTargetNames` entry appears in the print set;
3. every registry name appears in the print set (or is explicitly marked as a
   non-target dependency).

Without step 2, adding 35 names to the registry still leaves 72 catalog targets
unprinted. Adding the 35 names also requires updating `auditedTheorems_length`
from 435 to 470; do not change the theorem to a weaker bound.

**Fidelity risk / feasibility / type:** low risk (adding audit lines is safe);
high feasibility (42 missing print commands, 35 missing registry names);
audit metadata, not a model extension.

### T4. `LnLean.Proofs.Traceability.catalog_target_counts` (P1)

**Statement shape**

```lean
/-- 294 semicolon-separated target occurrences, generated from the catalog. -/
def targetOccurrenceTable : List String := [ ... ]

theorem catalog_target_occurrences : targetOccurrenceTable.length = 294 := rfl
theorem catalog_unique_targets : targetOccurrenceTable.dedup.length = 282 := by
  decide
theorem duplicate_targets_eq_ecdsa :
    targetOccurrenceTable.length - targetOccurrenceTable.dedup.length = 12 := by
  decide
```

**Hypotheses:** none.

**Non-vacuity witness:** the generated 294-entry list; `dedup` yields 282.

**Why it is faithful:** it records the two counts in the kernel and stops
"294 targets" from being read as 294 unique declarations. The 12 duplicates are
the ECDSA declarations shared by `LN-L1-001` and `LN-L1-004`; keep both rows
because they make different funding/to_local script claims that share the ECDSA
seam targets.

**Fidelity risk / feasibility / type:** low risk; medium feasibility (generated
294-entry table; `dedup` on strings is reducible but may need the file's higher
recursion budget); metadata.

### T5. `LnLean.Security.partial_synchrony_not_tautological` (P1)

**Statement shape**

```lean
theorem partial_synchrony_not_tautological :
    ¬ ∀ (s : Schedule) (m : Message), s.DeliveredWithin m (m.send + 0) := by
  intro h
  rcases h ⟨fun _ => none⟩ ⟨0, 0⟩ with ⟨d, hd, _⟩
  simp at hd

theorem partial_synchrony_unit_witness :
    PartiallySynchronous 0 1 ⟨fun _ => some 0⟩ := by
  intro m _
  exact ⟨0, rfl, Nat.zero_le _⟩
```

**Hypotheses:** none. The first theorem is a separation result: without the
partial-synchrony hypothesis, the conclusion is false.

**Non-vacuity witness:** the schedule `latency := fun _ => none` falsifies the
conclusion; the schedule `latency := fun _ => some 0` satisfies
`PartiallySynchronous 0 1`.

**Why it is faithful:** it makes the status of `LN-SEC-004` explicit. The
existing theorem is a legitimate definitional projection, but it is not a
liveness result; the separation theorem prevents a reader from treating the
definition as a proved delivery guarantee.

**Fidelity risk / feasibility / type:** low risk; high feasibility; statement
clarification. Do not delete `partial_synchrony_delivers`; keep it as the
definitional unpacking and relabel the catalog row (or add a scope note).

### T6. `LnLean.Protocol.Handshake.ready_reachable` (P1)

**Statement shape**

```lean
theorem ready_reachable :
    ∃ s : HandshakeState, Reachable s ∧ s.ready = true := by
  -- Witness run: sendInit; recvInit; recvAcceptChannel;
  -- sendFundingCreated; recvFundingSigned; sendChannelReady;
  -- recvChannelReady.
  ...
```

**Hypotheses:** none.

**Non-vacuity witness:** the explicit run above, using the funder-side guards
in `Handshake.lean:164-190`. Each step is deterministic and closed by
`decide`/`rfl`.

**Why it is faithful:** `channel_ready_gate` is a characterization whose
left-to-right direction is definitional. Without a reachable state satisfying
`ready`, the row's non-vacuity is unproved. The existing
`NonVacuityTargets.handshakeState_witness` only witnesses a reachable state
with `ready = false` (`NonVacuityTargets.lean:692-696`), so it does not cover
this claim.

**Fidelity risk / feasibility / type:** low risk; high feasibility; witness,
not a model extension.

### T7. `LnLean.Protocol.Handshake.usable_requires_ready_connected_confirmed` (P1, additive model extension)

**Statement shape**

```lean
structure ChannelReadiness where
  ready : Bool
  confirmations : Nat
  requiredConfirmations : Nat
  peerConnected : Bool
  shuttingDown : Bool

def ChannelReadiness.Usable (r : ChannelReadiness) : Prop :=
  r.ready = true ∧ r.requiredConfirmations ≤ r.confirmations ∧
    r.peerConnected = true ∧ r.shuttingDown = false

theorem usable_requires_ready_connected_confirmed
    (r : ChannelReadiness) (h : r.Usable) :
    r.ready = true ∧ r.requiredConfirmations ≤ r.confirmations ∧
      r.peerConnected = true ∧ r.shuttingDown = false := h

theorem ready_not_usable_without_confirmation :
    ∃ r : ChannelReadiness,
      r.ready = true ∧ r.confirmations < r.requiredConfirmations ∧ ¬ r.Usable := by
  refine ⟨⟨true, 0, 6, true, false⟩, rfl, by decide, ?_⟩
  simp [ChannelReadiness.Usable]
```

**Hypotheses:** `Usable` (the new predicate). The first theorem is
definitional by design; its purpose is to make the LDK gate explicit, not to
prove a substantive protocol property. The substantive content is the
separation theorem.

**Non-vacuity witness:** `{ ready := true, confirmations := 6,
requiredConfirmations := 6, peerConnected := true, shuttingDown := false }`
satisfies `Usable`; `{ ready := true, confirmations := 0,
requiredConfirmations := 6, peerConnected := true, shuttingDown := false }`
satisfies `ready` but not `Usable`.

**Why it is faithful:** it mirrors the three additional clauses in
`ldk-node/src/types.rs:564-573` (confirmation threshold, peer connectivity, no
shutdown) without changing the existing `HandshakeState.ready` bit. This is an
additive model extension; `channel_ready_gate` remains the BOLT 2 flag-level
statement.

**Fidelity risk / feasibility / type:** medium risk if it is allowed to
redefine `ready`; enforce that it does not. Medium feasibility (new structure
plus two short proofs); model extension. Defer unless the maintainer wants an
LDK-shaped readiness slice in wave 13.

### T8. `LnLean.Proofs.Model.NonVacuityTargets.route_wellFormed_witness` (P2)

**Statement shape**

```lean
theorem route_wellFormed_witness :
    ∃ r : Route, r.WellFormed := by
  refine ⟨⟨[⟨0, 1, ⟨1000⟩, 40⟩, ⟨1, 2, ⟨1000⟩, 40⟩], ⟨1000⟩⟩, ?_⟩
  simp [Route.WellFormed, Route.Connected]
```

**Hypotheses:** none.

**Non-vacuity witness:** the two-hop route with 1000 msat per hop and 1000 msat
carried.

**Why it is faithful:** `LN-RT-001`'s three targets are projections of
`Route.WellFormed`; a witness shows the predicate is inhabited. Register it in
`witnessRegistry` and update the length theorem from 30 to 31.

**Fidelity risk / feasibility / type:** low risk; high feasibility; witness.
Keep the existing `LN-RT-001` projections, but do not present them as a route
construction theorem.

## 5. Assumptions, counterexamples, and non-vacuity risks

### 5.1 Assumption-shaped rows must stay visible

* `PartiallySynchronous` is an explicit network assumption
  (`docs/ASSUMPTIONS.md:111-116`). `LN-SEC-004` is its definitional
  re-export. Do **not** strengthen the definition or delete the theorem;
  relabel the row (or add a scope note) so it is not counted as a proved
  liveness guarantee. The new separation theorem T5 preserves the assumption
  boundary.
* `Route.WellFormed`, `Breach.Punishable`, `RevocationState.Revoked`, and
  `Invoice.Consistent` are definitions. The corresponding `.proved` rows are
  definitional unpackings. They are useful interface lemmas, but they do not
  establish the BOLT 3/BOLT 5/BOLT 7 property for a real construction. No
  `ChannelState` or `Route` witness is registered in the non-vacuity registry.
  The catalog has only `.proved`/`.statementOnly` status; it cannot currently
  mark "definitional". A scope-note convention (or a future `definitional`
  status) is needed before "N proved targets" is used as a coverage metric.

### 5.2 The ten-invariant "discharged" claim is overstated

`ThreatModelProps.lean:662-667` says the catalog "contains no predicate that is
assumed rather than proved", but the ten proofs include five
identity/projection terms:

| Invariant | Proof term | Why it is not substantive |
|---|---|---|
| `INV-05` | `fun _b h => h` (`:638-640`) | `Punishable` contains the conclusion. |
| `INV-06` | `advance_monotone` (`:642-644`) | `advance` is a canned `+1`. |
| `INV-07` | `fun _r h => h` (`:646-648`) | `WellFormed` is the conjunction being proved. |
| `INV-08` | `fun _inv _ph _amt _cltv h => h` (`:650-652`) | `Consistent` contains the conclusion. |
| `INV-10` | `partial_synchrony_delivers` (`:658-660`) | The predicate is the network assumption. |

The prior report `agents/reports/B29.md:112-134` already labels these rows
"projection", "definitional", and "the network assumption itself". The code
docstring did not carry that qualification forward. Correct the docstring; do
not change the proofs.

### 5.3 Non-vacuity registry coverage is curated, not catalog-wide

`NonVacuityTargets` explicitly warns that it does not prove every catalog row
non-vacuous (`:4-10`, `:39-42`). The current registry has 30 entries; by
basename, only 4 entries name a catalog target
(`withVendorEcdsa_funding_uninhabited`, `withVendorEcdsa_accepts_nothing`,
`vacuous_nonvacuous_separation`, `witness_not_universal`). There is no theorem
mapping registry IDs to catalog IDs, so the true coverage is not machine-known.
Do not read `witnessRegistry_length = 30` as "30 catalog rows are non-vacuous".

Preserve the existing negative results:
`withVendorEcdsa_accepts_nothing`, `withVendorEcdsa_funding_uninhabited`,
`vacuous_nonvacuous_separation`, `witness_not_universal`,
`bridged_model_totalReject`, and `no_bridged_nontrivial_model`. They are the
model's honest vacuity witnesses, not defects to be removed.

### 5.4 Axiom-audit coverage must not be inferred from the registry length

`auditedTheorems_length = 435` is a statement about a hand-written list. The
actual `#print axioms` block has 393 commands. The exact coverage is:

* 282 unique catalog targets;
* 247 in `auditedTheorems`;
* 210 printed;
* 72 not printed;
* 35 absent from the registry entirely;
* 42 registry names not printed (the 37 catalog names in the registry but not
  printed, plus 5 non-catalog names).

Adding the 35 missing names to the registry is safe, but the print side must be
extended too. Do not "fix" the count by trimming the registry to 393; that would
silently drop 35 catalog targets.

### 5.5 Traceability must not be strengthened by weakening theorems

None of T1-T6, T8 changes an existing theorem statement. T7 is additive and
must not alter `HandshakeState.ready` or `channel_ready_gate`; redefining
`ready` to include confirmation/connectivity would silently change the meaning
of every existing `ready` theorem and make the traceability table claim a
different proposition. If a future slice wants a single `Usable` notion, version
it as a new predicate, not as a replacement for `ready`.

### 5.6 Count semantics and duplicate rows

The 12 duplicate ECDSA targets are shared intentionally by `LN-L1-001` and
`LN-L1-004`; the rows make different funding-output and `to_local` script
claims and both depend on the same ECDSA seam. Do not deduplicate the catalog
rows. Instead, state both counts (294 occurrences, 282 unique declarations) and
keep the duplicate list explicit.

### 5.7 Anchor checks are existence-only

`verify-anchors.py` checks only path existence and `line ≤ file length`
(`:43-52`). A real but semantically unrelated line passes. `LN-SEC-004` is the
concrete case: `channelmanager.rs:17831` is
`handle_channel_reestablish`, not a partial-synchrony guarantee. The
`unanchored_rows=2` output is also a checker artifact: `:34-35` counts any line
containing the string `UNANCHORED`, including the two prose lines in
`docs/TRACEABILITY.md:11` and `:74`. Fix the checker to parse the table cell,
not the whole line, and add a manual semantic-review note for rows whose anchor
is only topically related.

## 6. Wave-13 recommendation

**Verdict: implement the P0 metadata/audit targets; defer the model extensions;
treat the LDK behavior gaps as external/unmodelled.**

| Slice | Recommendation | Reason |
|---|---|---|
| T1, T2 (traceability declIds/module correspondence) | **Implement now** | Pure kernel checks over existing data; current data passes both; closes the refactor's main blind spot. |
| T3 (catalog targets subset of axiom audit) + print-manifest checker | **Implement now** | 35 catalog targets are completely unaudited and 72 are unprinted; this is the largest assurance gap and requires no model change. |
| T4 (count semantics) | **Implement now or with T3** | Small generated table; prevents "294 targets" from being read as unique coverage. |
| T5 (partial-synchrony separation) | **Implement now** | A short lemma and witness; makes the `LN-SEC-004` assumption boundary explicit without changing the existing theorem. |
| T6 (reachable ready witness) | **Implement now** | Small constructive run; directly supports `LN-PR-002` non-vacuity. |
| T7 (LDK-shaped `Usable`) | **Defer** | Additive model extension; needs maintainer approval and must not redefine `ready`. The existing flag-level theorem is faithful to BOLT 2, just not to LDK `is_usable`. |
| T8 (Route witness) | **Defer or bundle with T7** | Witness only; no new protocol content, but it closes the `LN-RT-001` non-vacuity gap. |
| LDK confirmation depth, peer connectivity, shutdown gate | **External / unmodelled** | These are gaps in the model's readiness surface, not proof gaps in `channel_ready_gate`. Document them as scope boundaries. |
| Splice `ChannelReady` / new funding outpoint | **External / unmodelled** | Already covered by R25's model-extension barrier; do not claim it here. |
| BOLT 7 `enabled` bit semantics | **Defer** | The raw flag is stored but not decoded; a faithful slice needs a new `disabled` predicate and routing-suppression theorem. |
| Docs/gate corrections (`435`, `294`, stale docstrings, `ThreatModelProps` "no predicate assumed", anchor prose count) | **Implement with the P0 slice** | These are claim-accuracy fixes, not model changes; leaving them would continue to overstate coverage. |

No wave-13 proof lane should attempt a new Noise/PoP/coverage/splice model to
"close" these gaps. The LDK-derived behaviors are external to the current
single-funding, boolean-handshake model. The safe lane is the metadata and
audit strengthening above.

## 7. Evidence and commands

### 7.1 Repository state

```text
$ git rev-parse --abbrev-ref HEAD
repair/integrated
$ git rev-parse HEAD
f7f062817c185cd70004bb26c652deb99c6fd4bd
$ git show --stat b6a7259
 LnLean/Proofs/Traceability.lean | 179 ++++++++++++++++++++--------------------
 1 file changed, 91 insertions(+), 88 deletions(-)
```

### 7.2 Gate reproduction

```text
$ python3 scripts/check-catalog.py --audit --no-candidates
summary: rows=51 proved=51 statementOnly=0 targets=294 unresolved=0 \
  proved_failures=0 duplicate_ids=0 candidates=0 declarations=11898
OK: every catalog target resolves exactly and every proved row is sorry-free.

$ python3 scripts/verify-anchors.py
anchors=313 bad=0 unanchored_rows=2
verify-anchors: OK
```

The `unanchored_rows=2` value is the prose false positive described in §5.7;
there are no actual `UNANCHORED` table cells.

### 7.3 Counts used in this report

```text
$ python3 - <<'PY'
import re
lines = open('LnLean/Proofs/PhaseC3/AxiomAudit.lean').read().splitlines()
i = [n for n,l in enumerate(lines) if l.startswith('def auditedTheorems')][0]
j = [n for n,l in enumerate(lines) if l.startswith('theorem auditedTheorems_length')][0]
reg = []
for l in lines[i:j]:
    reg += re.findall(chr(96) + r'([A-Za-z0-9_.]+)', l)
prints = [re.search(r'#print axioms\s+(\S+)', l).group(1)
          for l in lines if l.startswith('#print axioms')]

ob = open('LnLean/Proofs/Obligations.lean').read()
targets = []
for t in re.findall(r'leanTarget\s*:=\s*"(.*?)"', ob, re.S):
    targets += [x.strip() for x in t.split(';') if x.strip()]
T = set(targets)
print('prints', len(prints), 'registry', len(reg))
print('occurrences', len(targets), 'unique', len(T))
print('catalog_not_printed', len(T - set(prints)))
print('catalog_not_registry', len(T - set(reg)))
print('catalog_printed', len(T & set(prints)))
print('catalog_in_registry', len(T & set(reg)))
print('registry_not_printed', len(set(reg) - set(prints)))
PY
prints 393 registry 435
occurrences 294 unique 282
catalog_not_printed 72
catalog_not_registry 35
catalog_printed 210
catalog_in_registry 247
registry_not_printed 42
```

The `provedTable` reference count is independent evidence for the same split:

```text
$ python3 - <<'PY'
import re
s = open('LnLean/Proofs/Traceability.lean').read()
start = s.index('def provedTable')
end = s.index('def provedDeclarations')
rows = re.findall(r'\u27e8(\d+),\s*\[([0-9, ]*)\]', s[start:end])
ids = [int(x) for _, l in rows for x in l.split(',') if x.strip()]
print('rows', len(rows), 'refs', len(ids), 'unique', len(set(ids)))
PY
rows 51 refs 294 unique 282
```

The 12 duplicate names are exactly the ECDSA declarations in
`provedDeclarations` IDs 7-18:

```text
LnLean.Proofs.Bitcoin.EcdsaConcreteTargets.eufCma_vendorVerify_iff_totalReject
LnLean.Proofs.Bitcoin.EcdsaConcreteTargets.bridged_model_totalReject
LnLean.Proofs.Bitcoin.EcdsaConcreteTargets.exists_bridged_model_iff_totalReject
LnLean.Proofs.Bitcoin.EcdsaConcreteTargets.withVendorEcdsa_no_funding
LnLean.Proofs.Bitcoin.EcdsaConcreteTargets.not_digestBindsMod_fundingTag
LnLean.Proofs.Bitcoin.EcdsaDomainTargets.not_digestBindsMod_any_tag
LnLean.Proofs.Bitcoin.EcdsaDomainTargets.no_digestBindsMod_anywhere
LnLean.Proofs.Bitcoin.EcdsaDomainTargets.not_digestBindsModOn33_any_tag
LnLean.Proofs.Bitcoin.EcdsaDomainTargets.digestBindsModOn_canonical33
LnLean.Proofs.Bitcoin.EcdsaDomainTargets.digestBindsModOn_canonical32
LnLean.Proofs.Bitcoin.EcdsaDomainTargets.residueBinding_vendor_funding_eq_of_canonical33
LnLean.Proofs.Bitcoin.EcdsaDomainTargets.digest_domain_dichotomy
```

### 7.4 Source checks

```text
$ rg -n 'partial_synchrony_delivers|def PartiallySynchronous' \
    LnLean/Security/Invariants.lean
483:def PartiallySynchronous (gst delta : Nat) (s : Schedule) : Prop :=
488:theorem partial_synchrony_delivers ...

$ rg -n 'theorem advance_monotone|def ChannelState.advance|theorem Route.wellFormed' \
    LnLean/Security/Invariants.lean
319:def ChannelState.advance ...
323:theorem advance_monotone ...
367:theorem Route.wellFormed_connected ...
372:theorem Route.wellFormed_capacity ...
378:theorem Route.wellFormed_nonempty ...

$ rg -n 'theorem proved_decl|theorem proved_row_count|theorem no_unanchored_rows' \
    LnLean/Proofs/Traceability.lean
855:theorem proved_rows_have_decls ...
861:theorem proved_decls_in_snapshot ...
874:theorem proved_declarations_nodup ...
879:theorem proved_declaration_ids_contiguous ...
896:theorem proved_row_count ...
910:theorem no_unanchored_rows ...

$ rg -n 'invRevocationPenalty_proved|invRouteWellFormed_proved|invPartialSynchrony_proved|catalog_predicates_discharged' \
    LnLean/Proofs/Security/ThreatModelProps.lean
638:theorem invRevocationPenalty_proved ...
646:theorem invRouteWellFormed_proved ...
658:theorem invPartialSynchrony_proved ...
666:theorem catalog_predicates_discharged ...

$ rg -n 'is_channel_ready|is_usable|confirmations_required' \
    /tmp/opencode/ldk-refs/ldk-node/src/types.rs
557:pub confirmations_required ...
561:pub confirmations ...
568:pub is_channel_ready: bool,
573:pub is_usable: bool,

$ rg -n 'ChannelReady|spliced' /tmp/opencode/ldk-refs/ldk-node/src/event.rs
276: - An existing channel has been spliced ...
277: ChannelReady { ...
293: funding_txo: Option<OutPoint>,

$ rg -n 'pub fn splice_in|Experimental API' /tmp/opencode/ldk-refs/ldk-node/src/lib.rs
1949: # Experimental API
1953: pub fn splice_in(

$ rg -n 'one_to_two|two_to_one|pub last_update|pub enabled' \
    /tmp/opencode/ldk-refs/ldk-node/src/graph.rs
68: pub one_to_two: Option<ChannelUpdateInfo>,
72: pub two_to_one: Option<ChannelUpdateInfo>,
98: pub last_update: u32,
100: pub enabled: bool,
```

The `LN-SEC-004` anchor was checked directly:

```text
$ sed -n '17831p' refs/rust-lightning/lightning/src/ln/channelmanager.rs
fn handle_channel_reestablish(
```

### 7.5 Files read

* `docs/AGENT-PROTOCOL.md`, `docs/OPEN-ISSUES.md`, `docs/THEOREM-INDEX.md`,
  `docs/TRACEABILITY.md`, `docs/ASSUMPTIONS.md`, `docs/WAVE-STATUS.md`,
  `docs/FINAL-STATUS.md`, `agents/TODO-REPAIR.md`.
* `agents/reports/swarm12/S12-POST-INTEGRATION-AUDIT.md`,
  `agents/reports/swarm12/S12-AUDIT-BARRIERS.md`, `agents/reports/B29.md`.
* `LnLean/Proofs/Obligations.lean`, `LnLean/Proofs/Traceability.lean`,
  `LnLean/Proofs/PhaseC3/AxiomAudit.lean`,
  `LnLean/Proofs/Model/NonVacuityTargets.lean`,
  `LnLean/Proofs/Security/ThreatModelProps.lean`,
  `LnLean/Security/Invariants.lean`, `LnLean/Protocol/Handshake.lean`,
  `LnLean/Proofs/WaveD/D18.lean`, `LnLean/Routing/Gossip.lean`,
  `LnLean/Proofs/Routing/GossipCanonicalTargets.lean`,
  `LnLean/Proofs/Routing/GossipStoreEpochTargets.lean`,
  `LnLean/Proofs/WaveD/D14.lean`.
* `scripts/check-catalog.py`, `scripts/verify-anchors.py`,
  `scripts/check-wave-a.py`.
* Pinned LDK refs: `ldk-node/src/types.rs`, `ldk-node/src/event.rs`,
  `ldk-node/src/graph.rs`, `ldk-node/src/lib.rs`,
  `ldk-node/src/probing.rs`, `ldk-server/e2e-tests/src/lib.rs`,
  `ldk-server/ldk-server/src/main.rs`,
  `refs/rust-lightning/lightning/src/ln/channelmanager.rs`.
