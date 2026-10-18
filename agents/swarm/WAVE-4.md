# Wave 4 — open-issue attack plan (complete)

**Status:** complete and integrated at `26ced90`. The eight lanes reported; the parent
added six modules to the root and axiom audit, strengthened `LN-HT-004` and
`LN-PR-004`, and reached the 188-job gate. Reports are in
`agents/reports/swarm4/`.

**Base commit:** `80bad41` (`[STATUS] record proof-wave 3 gate HEAD`)
**Branch:** `repair/integrated`
**Catalog:** 48 proved / 0 statementOnly / 0 unresolved
**Full build at base:** 182 jobs, RC 0
**Roadmap:** `docs/OPEN-ISSUES.md`
**Protocol:** `docs/SWARM-LOOP.md`

Wave 3 closed the catalog. Wave 4 does **not** chase catalog rows. It attacks
the non-catalog gaps that block a credible release or a stronger bridge. Eight
lanes run in parallel with exclusive files. No lane commits, pushes, edits
`LnLean.lean`, `Obligations.lean`, `Traceability.lean`, `AxiomAudit.lean`, or
the shared docs; the parent integrates and records the gate.

## Lanes

| Lane | Issue(s) | Owned files | Deliverable / acceptance |
|---|---|---|---|
| `S4-L1-SPEND` | `L1-01`, `L1-02` | `LnLean/Bitcoin/Seam.lean`, `LnLean/Proofs/Bitcoin/SpendTargets.lean`, report | A faithful script-spend bridge or a precisely scoped conditional spend theorem. Preserve all existing seam signatures. If execution semantics are absent, define the minimal interpreter relation in the new proof module and prove the strongest true statement; do not claim consensus spendability. |
| `S4-VENDOR-CI` | `OPS-01` | `.github/workflows/ci.yml`, `scripts/fetch-vendor.sh`, `scripts/verify-vendor.sh`, report | Reproducible vendor provisioning path or an explicit, tested fallback. CI must remain valid YAML and must not claim a build it cannot run. Do not edit `docs/OPEN-ISSUES.md`. |
| `S4-CONFORMANCE` | `CONF-01` | `tests/conformance/**`, `scripts/check-conformance.py`, `LnLean/Proofs/ConformanceTargets.lean`, report | Concrete BOLT/rust-lightning conformance vectors for BigSize/TLV (and another wire encoding if cheap), a Python runner, and Lean `decide` theorems for the vector expectations. State clearly that this is vector conformance, not a full implementation test. |
| `S4-PR-WIRE` | `PR-02` | `LnLean/Protocol/Messages.lean`, `LnLean/Proofs/ProtocolWireTargets.lean`, report | Additive `CommitmentSignedFull` (commitment number, per-HTLC entries, fee/digest as appropriate) plus projection and conditional coverage theorems. Keep existing `CommitmentSigned` and all current imports working. |
| `S4-HTLC-GLOBAL` | `HT-01` | `LnLean/Channel/HTLC.lean`, `LnLean/Proofs/Channel/HtlcGlobalIdTargets.lean`, report | Direction-tagged/channel-wide id namespace with global uniqueness over reachable books, plus a theorem that the old cross-direction duplicate becomes distinct tagged ids. Preserve the existing per-sender and counterexample results. |
| `S4-FEE-DUST` | `CH-01`, `CH-02` | `LnLean/Proofs/Channel/CommitmentIntegrationTargets.lean`, report | New-module definitions/theorems for second-stage fee, dust/trim, and a refinement/legacy-view relation to `CommitmentTx.outputs`. If the relation needs a core change, prove what is possible and state the exact integration step. Do not edit `Commitment.lean`. |
| `S4-GOSSIP-ATTR` | `RT-01` | `LnLean/Routing/Gossip.lean`, `LnLean/Proofs/Routing/GossipAttributionTargets.lean`, report | Additive key-attribution/admission path (`updateKeyAnnounced` or equivalent) and a theorem that reachable admitted graph edges have the announced update key. Preserve raw `applyGossip` and its existing theorems. |
| `S4-RELEASE` | `OPS-02`, `OPS-03` | `docs/RELEASE-CHECKLIST.md`, `docs/LICENSE-DECISION.md`, report | Release checklist, license decision matrix (no license choice), tag/PR plan, and a truthful public-CI note. Do not create `LICENSE`, tag, merge, or push. |

## Lane rules

- Read `docs/OPEN-ISSUES.md`, `docs/ASSUMPTIONS.md`, `docs/THEOREM-INDEX.md`,
  the relevant prior reports, and the owned modules first.
- No `sorry`, `axiom`, `admit`, `native_decide`, `unsafe`, or
  `@[implemented_by]`. Allowed axioms: `propext`, `Quot.sound`,
  `Classical.choice`.
- Preserve mechanized counterexamples and strongest true conditional forms.
  A narrowed/blocked result is acceptable and valuable; a fake proof is not.
- Build only your module(s) under the shared lock:
  `LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock lake build <Module>`.
- Do not run the full `lake build`, `collect-obligations.py`, `collect-anchors.py`,
  or any Git write command.
- Report exact signatures, build result, axiom result, forbidden-construct
  scan, scope caveats, integration steps, and blockers in
  `agents/reports/swarm4/S4-<LANE>.md`.
- If a requested change would touch a forbidden shared file, implement the
  additive part in your owned module and report the exact integration patch.
