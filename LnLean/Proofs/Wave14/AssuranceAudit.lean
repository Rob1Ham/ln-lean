import LnLean.Proofs.Traceability
import LnLean.Proofs.PhaseC3.AxiomAudit

/-!
# LnLean.Proofs.Wave14.AssuranceAudit

Assurance reconciliation surface for wave 14 (review gap `REV-05` / R32 §4 T8).

The repository has three hand-maintained views of the proof surface:

* the obligation catalog in `LnLean.Proofs.Obligations`, whose `leanTarget`
  strings contain **294 target occurrences** but only **282 unique declaration
  names**;
* the `#print axioms` commands and the `auditedTheorems` registry in
  `LnLean.Proofs.PhaseC3.AxiomAudit`, currently **423 print commands** over
  **465 registry names**;
* the transcribed `targetTable` / `provedTable` / `provedDeclarations` tables
  in `LnLean.Proofs.Traceability`, currently 51 target rows, 51 proved rows,
  and 282 declaration rows.

This module records only facts that are true of that surface.  It deliberately
does **not** state the proposed full membership theorem

```
∀ t ∈ catalogTargetNames, t ∈ auditedTheorems
```

because that statement is false on the current tree: the strict checker
`scripts/check-assurance-coverage.py` reports 35 unique catalog targets absent
from `auditedTheorems` (and 72 absent from the `#print axioms` set, 42 registry
names with no print command).  Stating the membership theorem here, or
weakening it to a sample while naming it as catalog-wide, would hide the gap.
Instead the module provides:

* named count facts: 51 catalog rows, 282 declarations in the transcribed
  manifest, and 465 registry names;
* a **sampled** subset lemma over an explicit nine-name manifest that is
  genuinely contained in `auditedTheorems`;
* a **sampled** absence lemma over five catalog targets that are genuinely
  absent from `auditedTheorems`, together with a proof that those five strings
  still occur in the 282-name catalog manifest.

The full-set reconciliation (which names to print or add, and the 5 stale
registry-only names) is a source edit for the integrator, described in
`agents/reports/wave14/W14-ASSURANCE.md`; this module does not edit the shared
catalog, audit, or traceability files.

## Boundary (do not overclaim)

Lean cannot inspect its own `#print axioms` transcript from this module.  The
theorems below reason about the *registry list* and the *transcribed manifest*;
they do not prove that a proof was actually printed, that the printed output is
axiom-clean, or that the transcribed tables match the Markdown files on disk.
Those checks are the runtime job of `scripts/check-assurance-coverage.py`.
The sampled subset/absence lemmas are witnesses of the manifest shape, not a
catalog-wide coverage theorem.

This module is additive: it imports the existing modules and changes no
catalog row, audit entry, traceability table, or existing theorem.
-/

namespace LnLean.Proofs.Wave14.AssuranceAudit

open LnLean.Proofs
open LnLean.Proofs.Traceability

set_option autoImplicit false
set_option maxRecDepth 8000

/-! ## Named count facts -/

/-- The transcribed catalog manifest: the 282 declaration names recorded by
`provedDeclarations`, in snapshot order.  This is the unique-target view of the
catalog, not its 294 occurrence view. -/
def catalogTargetManifest : List String :=
  provedDeclarations.map (fun p => p.text)

/-- The catalog has 51 rows (the row count, not the occurrence count). -/
theorem catalog_row_count : obligations.length = 51 :=
  obligations_length

/-- The transcribed snapshot has 282 declaration rows. -/
theorem provedDeclarations_length : provedDeclarations.length = 282 := by
  have h := congrArg List.length proved_declaration_ids_contiguous
  simpa using h

/-- The unique-target manifest therefore has 282 entries. -/
theorem catalogTargetManifest_length : catalogTargetManifest.length = 282 := by
  simpa [catalogTargetManifest] using provedDeclarations_length

/-- The registry list has 465 names.  This is the list length, not the number
of `#print axioms` commands (currently 423). -/
theorem registry_length : auditedTheorems.length = 465 :=
  auditedTheorems_length

/-! ## A sampled subset of the registry -/

/-- Nine representative catalog declarations that the current registry does
contain.  The sample spans L1, channel, Bitcoin, protocol, liveness, routing,
payment, HTLC aggregate, and non-vacuity modules; it is explicitly a sample,
not the full catalog. -/
def auditedSampleManifest : List Lean.Name :=
  [ `LnLean.Proofs.conserved_no_value_creation,
    `LnLean.Channel.Commitment.outputs_nonnegative,
    `LnLean.Proofs.Bitcoin.commitmentBaseWeight_model_target,
    `LnLean.Protocol.Handshake.open_bounds,
    `LnLean.Proofs.Liveness.penalty_economical,
    `LnLean.Proofs.Routing.GossipTargets.gossip_graph_only_valid_announcements,
    `LnLean.Proofs.Payment.InvoiceWireTargets.parse_print,
    `LnLean.Proofs.Channel.HtlcAggregate.Aggregate.coverageValue_eq_sum,
    `LnLean.Proofs.Model.NonVacuityTargets.witnessRegistry_ne_nil ]

/-- The sampled manifest has nine entries. -/
theorem auditedSampleManifest_length : auditedSampleManifest.length = 9 := rfl

/-- Every sampled name is in the registry.  This is a finite membership proof;
it does not assert catalog-wide inclusion. -/
theorem auditedSampleManifest_subset :
    ∀ n ∈ auditedSampleManifest, n ∈ auditedTheorems := by
  decide

/-- A single named witness from the sample, usable as a non-vacuity check. -/
theorem conserved_target_audited :
    `LnLean.Proofs.conserved_no_value_creation ∈ auditedTheorems := by
  decide

/-! ## A sampled witness of the current registry gap -/

/-- Five unique catalog targets that are absent from `auditedTheorems` on the
current tree.  These are the concrete witnesses that the full membership
theorem is false; the runtime checker reports the complete 35-name set. -/
def unregisteredSampleManifest : List Lean.Name :=
  [ `LnLean.Bitcoin.anchorValue_eq,
    `LnLean.Payment.MPP.running_total_bound,
    `LnLean.Proofs.Conservation.global_conservation,
    `LnLean.Protocol.Peer.reestablish_no_rollback,
    `LnLean.Routing.Onion.peel_deterministic ]

/-- The absence sample has five entries. -/
theorem unregisteredSampleManifest_length :
    unregisteredSampleManifest.length = 5 := rfl

/-- Every sampled name is absent from the registry.  This records the gap
honestly instead of weakening the catalog-wide theorem. -/
theorem unregisteredSampleManifest_not_audited :
    ∀ n ∈ unregisteredSampleManifest, n ∉ auditedTheorems := by
  decide

/-- The same five names as strings, for membership in the transcribed
catalog manifest. -/
def unregisteredSampleStrings : List String :=
  [ "LnLean.Bitcoin.anchorValue_eq",
    "LnLean.Payment.MPP.running_total_bound",
    "LnLean.Proofs.Conservation.global_conservation",
    "LnLean.Protocol.Peer.reestablish_no_rollback",
    "LnLean.Routing.Onion.peel_deterministic" ]

/-- The five absent-from-registry names are nevertheless catalog targets, so
the absence is a gap in the audit registry rather than stale catalog text. -/
theorem unregisteredSampleStrings_in_catalog :
    ∀ s ∈ unregisteredSampleStrings, s ∈ catalogTargetManifest := by
  decide

/-- Combined non-vacuity witness: one sampled target is audited, while one
sampled target is both a catalog target and unregistered. -/
theorem sampled_audited_and_unregistered :
    `LnLean.Proofs.conserved_no_value_creation ∈ auditedTheorems ∧
      "LnLean.Bitcoin.anchorValue_eq" ∈ catalogTargetManifest ∧
      `LnLean.Bitcoin.anchorValue_eq ∉ auditedTheorems := by
  refine ⟨?_, ?_, ?_⟩
  · exact conserved_target_audited
  · decide
  · decide

/-! ## Axiom audit -/

#print axioms catalog_row_count
#print axioms provedDeclarations_length
#print axioms catalogTargetManifest_length
#print axioms registry_length
#print axioms auditedSampleManifest_length
#print axioms auditedSampleManifest_subset
#print axioms conserved_target_audited
#print axioms unregisteredSampleManifest_length
#print axioms unregisteredSampleManifest_not_audited
#print axioms unregisteredSampleStrings_in_catalog
#print axioms sampled_audited_and_unregistered

end LnLean.Proofs.Wave14.AssuranceAudit
