# W14-ASSURANCE — catalog / axiom-audit / traceability reconciliation

**Lane:** `W14-ASSURANCE` (Wave 14, branch `wave-14/16`, base `a331b71`).
**Status:** scripts and Lean module are green locally; the shared-source
reconciliation is **not applied** and remains the integrator's edit.

## 1. Scope

Build the assurance reconciliation surface for review gap `REV-05`
(R32 §4 T8, §6.2 `W13-ASSURANCE`; `docs/OPEN-ISSUES.md` row `REV-05`), without
editing the shared catalog, audit, or traceability files, and without making
the repository gate depend on the new checker.

Delivered:

* a deterministic, offline parser/checker for the three sources, with
  `--report`, `--strict`, and `--self-test`;
* a small Lean manifest/membership module that records only facts true on the
  current tree, including sampled witnesses of the registry gap;
* this report with the exact integrator edits.

## 2. Owned files

Only these files were created or modified:

* `scripts/check-assurance-coverage.py`
* `LnLean/Proofs/Wave14/AssuranceAudit.lean`
* `agents/reports/wave14/W14-ASSURANCE.md`

No other file was written. In particular, `AxiomAudit.lean`,
`Traceability.lean`, `Obligations.lean`, `LnLean.lean`, `lakefile.lean`,
`scripts/check-final.py`, `docs/`, the catalog, and CI were not edited.

## 3. Checker

`scripts/check-assurance-coverage.py` reads the three sources as text and
performs these checks.

1. **Catalog.** Parses 51 `id` / `leanTarget` / `status` rows, counts target
   **occurrences** (semicolon-separated names) and unique names, and reports
   duplicate names with the catalog row ids that share them.
2. **Audit.** Parses every `#print axioms <name>` command and the
   `auditedTheorems` literal, and compares the parsed registry length with the
   `auditedTheorems_length` literal.
3. **Coverage.** Reports unique catalog targets missing from the print set and
   from the registry.
4. **Reverse direction.** Reports registry names with no print command and
   printed names absent from the registry, so the two sets can be reconciled to
   equality rather than to a one-way subset.
5. **Traceability.** Where the transcribed tables permit checking, enforces:
   * the catalog's `leanTarget` sequence equals `targetTable`'s text sequence;
   * for every `provedTable` row, the target text splits into exactly the
     `provedDeclarations` names named by its `declIds`, in order;
   * the target's `modules` list equals those declarations' `module` fields, in
     order;
   * declaration ids are exactly `0..281`, every declaration is used, and the
     `targetTable` / `provedTable` lengths match the catalog.
   It also checks that the 282 snapshot names are exactly the unique catalog
   targets.

Modes:

```sh
python3 scripts/check-assurance-coverage.py --report     # rc 0, prints everything
python3 scripts/check-assurance-coverage.py --strict     # rc 1 on any finding
python3 scripts/check-assurance-coverage.py --self-test  # in-memory negative fixture
```

`--self-test` runs a synthetic green fixture, removes one `#print axioms`
line in memory, and mutates one `provedDeclarations` module in memory. It
asserts the green fixture has zero findings and both mutations are detected
(including a nonzero strict result). It never writes a file.

## 4. Actual current counts (from the worktree)

`--report` was run from `/home/ubuntu/ln-lean-waveh` at base `a331b71`:

| Measure | Actual |
|---|---:|
| Catalog rows | 51 |
| Catalog statuses | `proved=51`, `statementOnly=0` |
| Target occurrences | **294** |
| Unique target declarations | **282** |
| Duplicate target names | **12** (all shared by `LN-L1-001` and `LN-L1-004`) |
| `#print axioms` commands | **393** |
| `auditedTheorems` registry names | **435** |
| `auditedTheorems_length` literal | 435 (matches parsed) |
| Unique catalog targets missing from print set | **72** |
| Unique catalog targets missing from registry | **35** |
| Registry names with no print command | **42** |
| Printed names absent from registry | **0** |
| `targetTable` / `provedTable` / `provedDeclarations` | 51 / 51 / 282 |
| Catalog-vs-`targetTable` text mismatches | **0** |
| Target-vs-declaration text mismatches | **0** |
| Target-vs-declaration module mismatches | **0** |
| Structural traceability mismatches | **0** |
| Catalog targets absent from `provedDeclarations` | **0** |
| `provedDeclarations` names absent from catalog | **0** |
| Strict findings | **149** (`72 + 35 + 42`; traceability contributes 0) |

The 42 registry-only names decompose as 37 catalog targets that are in the
registry but unprinted, plus 5 non-catalog names.  The 72 missing-print names
are the union of those 37 and the 35 names absent from the registry.

`--strict` exits 1 on the current tree by design. `--self-test` exits 0 with:

```text
self-test: PASS
  green fixture: 0 findings
  removed #print axioms C.c: detected
  provedDeclarations module mutation: detected
```

The checker was **not** added to `scripts/check-final.py` or CI. The parent
should wire it only after the registry/print reconciliation below.

## 5. Lean module

`LnLean.Proofs.Wave14.AssuranceAudit` imports `LnLean.Proofs.Traceability` and
`LnLean.Proofs.PhaseC3.AxiomAudit`; it imports no other Wave 14 lane.

### Headline definitions and theorems

```lean
def catalogTargetManifest : List String :=
  provedDeclarations.map (fun p => p.text)

theorem catalog_row_count : obligations.length = 51

theorem provedDeclarations_length : provedDeclarations.length = 282

theorem catalogTargetManifest_length : catalogTargetManifest.length = 282

theorem registry_length : auditedTheorems.length = 435

def auditedSampleManifest : List Lean.Name := [ -- nine names
  `LnLean.Proofs.conserved_no_value_creation,
  `LnLean.Channel.Commitment.outputs_nonnegative,
  `LnLean.Proofs.Bitcoin.commitmentBaseWeight_model_target,
  `LnLean.Protocol.Handshake.open_bounds,
  `LnLean.Proofs.Liveness.penalty_economical,
  `LnLean.Proofs.Routing.GossipTargets.gossip_graph_only_valid_announcements,
  `LnLean.Proofs.Payment.InvoiceWireTargets.parse_print,
  `LnLean.Proofs.Channel.HtlcAggregate.Aggregate.coverageValue_eq_sum,
  `LnLean.Proofs.Model.NonVacuityTargets.witnessRegistry_ne_nil ]

theorem auditedSampleManifest_length : auditedSampleManifest.length = 9

theorem auditedSampleManifest_subset :
    ∀ n ∈ auditedSampleManifest, n ∈ auditedTheorems

theorem conserved_target_audited :
    `LnLean.Proofs.conserved_no_value_creation ∈ auditedTheorems

def unregisteredSampleManifest : List Lean.Name := [
  `LnLean.Bitcoin.anchorValue_eq,
  `LnLean.Payment.MPP.running_total_bound,
  `LnLean.Proofs.Conservation.global_conservation,
  `LnLean.Protocol.Peer.reestablish_no_rollback,
  `LnLean.Routing.Onion.peel_deterministic ]

theorem unregisteredSampleManifest_length :
    unregisteredSampleManifest.length = 5

theorem unregisteredSampleManifest_not_audited :
    ∀ n ∈ unregisteredSampleManifest, n ∉ auditedTheorems

def unregisteredSampleStrings : List String := [ -- the same five as strings
  "LnLean.Bitcoin.anchorValue_eq",
  "LnLean.Payment.MPP.running_total_bound",
  "LnLean.Proofs.Conservation.global_conservation",
  "LnLean.Protocol.Peer.reestablish_no_rollback",
  "LnLean.Routing.Onion.peel_deterministic" ]

theorem unregisteredSampleStrings_in_catalog :
    ∀ s ∈ unregisteredSampleStrings, s ∈ catalogTargetManifest

theorem sampled_audited_and_unregistered :
    `LnLean.Proofs.conserved_no_value_creation ∈ auditedTheorems ∧
      "LnLean.Bitcoin.anchorValue_eq" ∈ catalogTargetManifest ∧
      `LnLean.Bitcoin.anchorValue_eq ∉ auditedTheorems
```

The proposed full theorem
`∀ t ∈ catalogTargetNames, t ∈ auditedTheorems` is **not stated**, because it
is false on the current tree. The sampled absence theorem and the script's
35-name report are the honest witness of that gap. The module docstring records
this boundary explicitly.

### Non-vacuity

* `conserved_target_audited` exhibits an audited name that is really in the
  435-name list.
* `unregisteredSampleManifest_not_audited` exhibits five names really absent
  from that list.
* `unregisteredSampleStrings_in_catalog` proves those five are nevertheless
  catalog targets, so the absence is a registry gap, not stale catalog text.
* `sampled_audited_and_unregistered` combines one positive and one negative
  witness in a single theorem.
* The script has a green fixture (zero findings) and two injected faults that
  it detects; a checker that could never fail would not pass `--self-test`.

## 6. Build and axiom audit

Command (scoped module, shared lock, no network):

```sh
cd /home/ubuntu/ln-lean-waveh
export PATH=/dev/shm/btc/elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
LEAN_NUM_THREADS=1 flock -w 3600 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Proofs.Wave14.AssuranceAudit
```

Result:

```text
Build completed successfully (195 jobs).
```

`#print axioms` output for the headline theorems:

| Theorem | Axioms |
|---|---|
| `catalog_row_count` | none |
| `provedDeclarations_length` | `propext` |
| `catalogTargetManifest_length` | `propext` |
| `registry_length` | none |
| `auditedSampleManifest_length` | none |
| `auditedSampleManifest_subset` | `propext`, `Quot.sound` |
| `conserved_target_audited` | `propext`, `Quot.sound` |
| `unregisteredSampleManifest_length` | none |
| `unregisteredSampleManifest_not_audited` | `propext`, `Quot.sound` |
| `unregisteredSampleStrings_in_catalog` | `propext` |
| `sampled_audited_and_unregistered` | `propext`, `Quot.sound` |

All are within the permitted `propext` / `Quot.sound` /
`Classical.choice` policy; no `sorry`, `axiom`, `admit`, `native_decide`,
`unsafe`, or `implemented_by` is used.

## 7. Review gap status

**Narrowed, not closed.** `REV-05` / R32 G20 is now measurable and
reproducible: the checker reports every count and every set difference, and the
traceability text/module equality is enforced where the transcribed tables
permit it. `REV-05` remains open until the integrator applies the shared-source
edits in §8 and wires `--strict`; on the current tree the gate correctly fails
with 149 findings.

G21 (traceability ID-only check) is narrowed: the script now checks text and
module equality, and finds 0 mismatches in the current data. It is not a kernel
theorem because Lean cannot parse the long `String` target fields in this
module (`Traceability.lean` already documents that limitation).

Still external / not addressed here:

* the 5 stale non-catalog registry names need an owner decision (print or
  remove);
* anchor relevance (`G22`) is not checked by this script;
* the docs/Lean claim labels for `partial_synchrony_delivers`,
  `channel_ready_gate`, etc. (`G18`/`G19`, `REV-06`) are not changed here;
* the checker cannot prove that Lean's actual transcript was axiom-clean; it
  parses the source commands, while the existing `AxiomAudit` build is the
  axiom-cleanliness check.

## 8. Integrator changes (stated, not applied)

### 8.1 Audit file

To make print set and registry set equal and cover all 282 unique catalog
targets, the integrator must edit
`LnLean/Proofs/PhaseC3/AxiomAudit.lean` as follows.

**A. Add 35 catalog targets to `auditedTheorems` and print each one**
(these are both absent from the registry and unprinted):

```text
LnLean.Bitcoin.anchorValue_eq
LnLean.Bitcoin.fundingOutput_moneyRange
LnLean.Channel.Reserve.bounds
LnLean.Payment.Invoice.payment_secret_match
LnLean.Payment.Invoice.signature_valid
LnLean.Payment.Keysend.preimage_binding
LnLean.Payment.MPP.running_total_bound
LnLean.Proofs.Channel.HtlcAggregate.Aggregate.distinct_commitments_separate
LnLean.Proofs.Channel.HtlcAggregate.distinctCommitments_separate_witness
LnLean.Proofs.Conservation.global_conservation
LnLean.Proofs.Liveness.watchtower_bridge
LnLean.Proofs.Routing.NodeIdentityChainTargets.opaque_link_not_imply_signed
LnLean.Proofs.Security.safety_async
LnLean.Protocol.Handshake.channel_ready_gate
LnLean.Protocol.Peer.reestablish_no_rollback
LnLean.Routing.Gossip.update_monotone
LnLean.Routing.Onion.hmac_sound
LnLean.Routing.Onion.peel_deterministic
LnLean.Routing.Route.cltv_accumulates
LnLean.Security.HtlcRecord.fail_only_after_expiry
LnLean.Security.HtlcRecord.fulfill_sound
LnLean.Security.Invoice.consistent_amount
LnLean.Security.Invoice.consistent_hash
LnLean.Security.L1Ledger.spend_preserves_noDoubleSpend
LnLean.Security.Ledger.step_conserves
LnLean.Security.MppPayment.settle_requires_sum
LnLean.Security.Route.wellFormed_capacity
LnLean.Security.Route.wellFormed_connected
LnLean.Security.Route.wellFormed_nonempty
LnLean.Security.advance_monotone
LnLean.Security.breach_penalty_spends_both
LnLean.Security.partial_synchrony_delivers
LnLean.Security.revoked_commitment_is_old
LnLean.Wire.Message.decode_length
LnLean.Wire.decode_encode
```

**B. Add `#print axioms` commands for the 37 catalog targets already in the
registry but unprinted:**

```text
LnLean.Proofs.Bitcoin.EcdsaConcreteTargets.bridged_model_totalReject
LnLean.Proofs.Bitcoin.EcdsaConcreteTargets.eufCma_vendorVerify_iff_totalReject
LnLean.Proofs.Bitcoin.EcdsaConcreteTargets.exists_bridged_model_iff_totalReject
LnLean.Proofs.Bitcoin.EcdsaConcreteTargets.not_digestBindsMod_fundingTag
LnLean.Proofs.Bitcoin.EcdsaConcreteTargets.withVendorEcdsa_no_funding
LnLean.Proofs.Channel.PreimageCoverageTargets.FieldAgreement.bytes_eq
LnLean.Proofs.Channel.PreimageCoverageTargets.FieldAgreement.digest_eq_vendor
LnLean.Proofs.Channel.PreimageCoverageTargets.counterPreimageAmount_bytes_ne
LnLean.Proofs.Channel.PreimageCoverageTargets.counterPreimageLocktime_bytes_ne
LnLean.Proofs.Channel.PreimageCoverageTargets.displayOrderPreimage_not_fieldAgreement
LnLean.Proofs.Channel.PreimageCoverageTargets.fieldAgreement_iff_eq_ofTx_and_amount
LnLean.Proofs.Channel.PreimageCoverageTargets.fieldAgreement_scriptCode_free
LnLean.Proofs.Channel.PreimageCoverageTargets.hash160_image_boundary
LnLean.Proofs.Channel.PreimageCoverageTargets.legacy_projection_not_determine_htlc_coverage
LnLean.Proofs.Channel.PreimageCoverageTargets.preimage_coverage_summary
LnLean.Proofs.Channel.PreimageCoverageTargets.vectorHtlcSpend_amount_is_gross
LnLean.Proofs.Channel.PreimageCoverageTargets.wireSignatureCovers_of_preimage
LnLean.Proofs.Crypto.AttributionGameTargets.attribution_game_summary
LnLean.Proofs.Crypto.AttributionGameTargets.stored_attribution_fails_without_keyBinding
LnLean.Proofs.Crypto.AttributionGameTargets.stored_payload_not_possession
LnLean.Proofs.Crypto.AttributionGameTargets.stored_pop_attribution
LnLean.Proofs.Crypto.AttributionGameTargets.stored_registration_funding_attribution
LnLean.Proofs.Protocol.OpenChannelRoutingTargets.openChannel_routing_summary
LnLean.Proofs.Protocol.OpenChannelRoutingTargets.openRoute_initial_to_fundingCreated
LnLean.Proofs.Protocol.OpenChannelRoutingTargets.unattributed_open_is_routed
LnLean.Proofs.Protocol.OpenChannelRoutingTargets.wire_binding_needs_FundingScript_C1
LnLean.Proofs.Protocol.OpenChannelRoutingTargets.wire_payload_does_not_determine_sender
LnLean.Proofs.Routing.NodeCanonicalTargets.applyGossipNodeCanonical_node_of_admitted
LnLean.Proofs.Routing.NodeCanonicalTargets.canonicalNodeStoreView_nodeCanonical
LnLean.Proofs.Routing.NodeCanonicalTargets.canonicalStoreView_does_not_canonicalise_nodes
LnLean.Proofs.Routing.NodeCanonicalTargets.epoch_square_lifts_to_node_canonical_view
LnLean.Proofs.Routing.NodeCanonicalTargets.no_canonical_node_preserving_raw_node_extension
LnLean.Proofs.Routing.NodeCanonicalTargets.raw_nonrefinement_preserved
LnLean.Proofs.Routing.NodeCanonicalTargets.reachableNodeCanonical_equal_timestamp_tie_boundary
LnLean.Proofs.Routing.NodeCanonicalTargets.reachableNodeCanonical_node_replacement
LnLean.Proofs.Routing.NodeCanonicalTargets.reachableNodeCanonical_node_slot_ignores_global_clock
LnLean.Proofs.Routing.NodeCanonicalTargets.reachableNodeCanonical_rotation_keeps_both
```

**C. Resolve the 5 registry names with no print command and no catalog row.**
Choose one policy and record it:

* print them and keep them, or
* remove them as stale registry entries.

```text
LnLean.Proofs.Conformance.Diff.diff_msg_channel_ready_frame_prefix
LnLean.Proofs.Conformance.Diff.diff_msg_channel_ready_header
LnLean.Proofs.Conformance.Diff.diff_msg_channel_ready_length
LnLean.Proofs.Conformance.Diff.diff_msg_channel_ready_payload
LnLean.Proofs.Conformance.Diff.diff_msg_channel_ready_transport
```

**D. Update the literal.** After A + B and either policy in C, the registry and
print sets both have **470** names if the five are printed, or **465** if they
are removed. Change

```lean
theorem auditedTheorems_length : auditedTheorems.length = 435 := rfl
```

to the chosen number and rebuild `LnLean.Proofs.PhaseC3.AxiomAudit`.
The `#print axioms` count becomes 470 or 465 respectively.

**E. Root import.** Regenerate the root with `scripts/regen-root.sh` so
`LnLean.Proofs.Wave14.AssuranceAudit` is imported. Do not hand-edit
`LnLean.lean`.

### 8.2 Traceability equality

The current data has 0 text/module mismatches, so no table content needs to
change. Enforce the equality in the runtime gate, not by weakening the Lean
theorem:

* keep `proved_decls_in_snapshot` (ID membership) as is;
* add `python3 scripts/check-assurance-coverage.py --strict` to the final
  checker/CI **after** §8.1 is applied;
* the equality checked is: for every `provedTable` row `(targetIndex, declIds)`,
  `targetTable[targetIndex].text` split on `;` equals the ordered list of
  `provedDeclarations[declId].text`, and `targetTable[targetIndex].modules`
  equals the ordered list of `provedDeclarations[declId].module`.

A kernel version of that equality is not feasible with the current import
restriction: `Traceability.lean` documents that `String.splitOn`/`startsWith`
do not reduce in the kernel and `native_decide` is forbidden. The script is the
intended enforcement point.

### 8.3 Docs wording

Apply these wording fixes; do not regenerate history.

* `LnLean/Proofs/Obligations.lean:76`: change
  `The 48-obligation catalog: six entries per domain.` to
  `The 51-obligation catalog: six entries per domain, with the extra
  aggregate/audit rows.`
* `docs/TRACEABILITY.md:112-113`: change `now with **294 resolved targets**`
  to `now with **294 target occurrences (282 unique declarations)**`.
* Any current summary that says only "294 resolved targets" should say
  "294 target occurrences (282 unique declarations)". The summary in
  `docs/THEOREM-INDEX.md:11` and `docs/FINAL-STATUS.md:9-10` already uses the
  occurrence/unique wording; keep that form.
* Keep `docs/FINAL-STATUS.md:193` as the model: `393 print commands over a
  435-name registry` is not `435 audited theorems`.
* No catalog row or declaration is added/removed by this lane.

## 9. Confirmation

No shared or other-lane file was edited. The only writes are the three owned
paths in §2. No `git add`, `git commit`, `git push`, or branch switch was run.
No bare `lake build` or full gate was run; the only build was the scoped
`LnLean.Proofs.Wave14.AssuranceAudit` command in §6.

## 10. Post-integration update (parent, `f0a3c07`)

The parent added 30 representative Wave 14 headline declarations to
`AxiomAudit` (16 imports and 30 `#print axioms` commands plus matching registry
entries). The current assurance surface is therefore:

- `#print axioms` commands: **423**;
- `auditedTheorems` registry names: **465**;
- `auditedTheorems_length`: **465**;
- catalog targets still unprinted: **72**;
- catalog targets still absent from the registry: **35**;
- registry-only names: **42**;
- traceability text/module mismatches: **0**.

`scripts/check-assurance-coverage.py --report` is RC 0;
`--strict` remains RC 1 on the unchanged 72/35 gap, which is expected and is the
intended blocking signal once the missing prints/registry entries are added.
`--self-test` remains RC 0. The catalog docstring was corrected to
`The 51-row catalog: ...` rather than the exact wording proposed in §8.3; the
meaning is the same. No other lane-owned file was changed by the parent.
