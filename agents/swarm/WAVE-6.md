# Wave 6 — residual L1, encoding, state-machine, and conformance gaps

**Status:** complete — all eight lanes integrated in the proof-wave 6
checkpoint.

**Launch commit:** `201a0a0` (`[STATUS] define and launch wave 6 residual lanes`)
**Branch:** `repair/integrated`
**Catalog at launch:** 48 proved / 0 statementOnly / 67 targets
**Full build at launch:** 204 jobs, RC 0
**Result:** 48 proved / 0 statementOnly / 73 targets; 218-job build; 163
audited theorems. Reports are under `agents/reports/swarm6/`.
**Roadmap:** `docs/OPEN-ISSUES.md`
**Protocol:** `docs/SWARM-LOOP.md`

Wave 5 added eight modules and strengthened five rows to 67 targets. Wave 6
attacks the gaps exposed by that work: BIP 143 sighash/locktime, the vendor
revocation branch, literal gross/net `Types.lean` fields, bit-exact BOLT 3
preimages, digest-to-view binding, the commitment dance, gossip invariant
derivation, and live transport/fixture conformance.

Eight lanes run in parallel with exclusive files. No lane commits, pushes,
edits `LnLean.lean`, `Obligations.lean`, `Traceability.lean`,
`AxiomAudit.lean`, the shared catalog, or docs owned by another lane; the
parent integrates and records the gate.

## Lanes

| Lane | Issue(s) | Owned files | Deliverable / acceptance |
|---|---|---|---|
| `S6-L1-SIGHASH` | `L1-08`, `L1-07` | new `LnLean/Bitcoin/Sighash.lean`, new `LnLean/Proofs/Bitcoin/SighashBridgeTargets.lean`, report | Model the BIP 143 witness-v0 preimage fields and a sighash constructor; prove the model digest is consumed by the existing bridge under an explicit signature/context law. Do not edit `InterpreterBridgeTargets.lean`; import it. If exact consensus serialization is out of scope, prove the strongest structural refinement and state every missing byte/context item. |
| `S6-L1-REVOKE` | `L1-02`, `L1-07` | new `LnLean/Proofs/Bitcoin/InterpreterRevocationTargets.lean`, report | Vendor-mechanize the `to_local` revocation branch through `OP_IF`/`OP_ELSE`/`OP_ENDIF`/`OP_CHECKSIG` or the strongest achievable path; prove branch selection and at least one negative/wrong-key or wrong-branch result. Do not edit the wave-5 bridge; import it. Record any missing vendor opcode/dependency exactly. |
| `S6-CH-TYPES` | `CH-04`, `CH-03` | `LnLean/Channel/Types.lean`, `LnLean/Channel/Commitment.lean`, new `LnLean/Proofs/Channel/CommitmentTypesTargets.lean`, report | Apply the recorded gross/net record-field patch with defaults where needed, switch the dust test to net, migrate the construction sites in the owned files, and prove the canonical refinement/effective-fee accounting at the new field boundary. Report any construction site outside ownership rather than silently changing it. |
| `S6-PR-BITEXACT` | `PR-05`, `PR-02` | `LnLean/Proofs/Channel/SighashTargets.lean`, report | Add an exact BOLT 3 commitment/HTLC preimage byte layout for the modelled fields and prove the structural serializer refines it; keep the existing `SighashProduces` API and negative results. If scripts/outpoints cannot be parsed without new context, model them as explicit serialized inputs and state the boundary. |
| `S6-PR-VIEWBIND` | `PR-06`, `PR-02` | new `LnLean/Proofs/Channel/SighashViewBindingTargets.lean`, report | Model a domain-separated commitment or an explicit collision-resistance/injectivity hypothesis, and prove digest binding to the commitment/HTLC view under it. Do not assume global SHA-256 injectivity. Keep a mechanized counterexample showing why digest binding alone is insufficient. |
| `S6-MODEL-DANCE` | `MODEL-03`, `MODEL-02` | `LnLean/Channel/State.lean`, new `LnLean/Proofs/Channel/CommitmentDanceTargets.lean`, report | Add additive `commitment_signed`/`revoke_and_ack` transitions (or an equivalent explicit dance layer) without breaking existing `Step`/liveness/liquidity folds; prove reachable-state invariants such as no stale commitment, revocation ordering, and balance/ledger preservation. Keep the existing unguarded-add counterexample. |
| `S6-GOSSIP-DERIVE` | `RT-02`, `RT-01` | `LnLean/Routing/Gossip.lean`, new `LnLean/Proofs/Routing/GossipCanonicalTargets.lean`, report | Define a canonicalizing admission/store transition and prove it establishes `NodeKeyConsistent` and `CanonicalAnnouncements` for reachable states, including update supersession/key rotation where modelled. Preserve raw `applyGossip` and all wave-4/5 counterexamples. |
| `S6-CONF-LIVE` | `CONF-03`, `CONF-02` | `LnLean/Wire/Message.lean`, `LnLean/Proofs/ConformanceDiffTargets.lean`, `tests/conformance/**`, `scripts/check-conformance.py`, report | Promote the transport frame/length model into `LnLean/Wire/Message.lean` with the same theorem names, keep the offline fixtures green, and add a deterministic pinned fixture-generation/verification path for rust-lightning. Do not claim a live `cargo test` run unless it actually succeeds. |

## Lane rules

- Read `docs/OPEN-ISSUES.md`, `docs/ASSUMPTIONS.md`, `docs/THEOREM-INDEX.md`,
  the wave-5 reports, and the owned modules first.
- No `sorry`, `axiom`, `admit`, `native_decide`, `unsafe`, or
  `@[implemented_by]`. Allowed axioms: `propext`, `Quot.sound`,
  `Classical.choice`.
- Preserve mechanized counterexamples and strongest true conditional forms.
  A narrowed/blocked result is acceptable and valuable; a fake proof is not.
- Build only your module(s) under the shared lock:
  `LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock lake build <Module>`.
- Do not run the full `lake build`, `collect-obligations.py`,
  `collect-anchors.py`, or any Git write command.
- Report exact signatures, build result, axiom result, forbidden-construct
  scan, scope caveats, integration steps, and blockers in
  `agents/reports/swarm6/S6-<LANE>.md`.
- If a requested change would touch a forbidden shared file, implement the
  additive part in your owned module and report the exact integration patch.


## Wave 6 result

All eight lanes returned and were integrated. The catalog strengthened four
existing rows (`LN-L1-001`, `LN-L1-004`, `LN-CH-003`, `LN-PR-004`) from 67 to
73 resolved targets. The exact lane results, scope boundaries, and files are
recorded in `docs/OPEN-ISSUES.md` and `docs/WAVE-STATUS.md`. The residual gaps
are the wave-7 candidates: decoded sequence/policy context, exact BIP 143
preimage equality, legacy commitment-consumer migration, folding the
update/dance layers, raw gossip-store refinement, live cargo conformance,
`open_channel`/funding-key authentication, and a secret-key/signer model.
