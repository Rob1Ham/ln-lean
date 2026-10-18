# Swarm Loop

This is the operating loop for the proof swarm. It is deliberately a
parent-orchestrated loop, not a background daemon: an OpenCode parent selects a
wave, launches child agents, integrates their disjoint results, runs the gate,
commits/pushes, updates `docs/OPEN-ISSUES.md`, and launches the next wave.

## Invariants

- Work only on `repair/integrated`; push non-force to
  `rob1ham/ln-lean`; never overwrite `main` or another worker's branch.
- `vendor/btc-lean-core` is read-only. Do not edit vendor sources.
- No `sorry`, `axiom`, `admit`, `native_decide`, `unsafe`, or
  `@[implemented_by]` in model/proof modules. `sorry` is permitted only under
  `LnLean/Proofs/` with an `-- OBLIGATION:` marker, and the current tree has
  zero actual `sorry` terms.
- Allowed axioms: `propext`, `Quot.sound`, `Classical.choice`.
- No fake proofs. If a claim is false, keep the mechanized counterexample and
  the strongest true conditional/admitted-step theorem. Reword the catalog
  claim if the literal claim is refuted.
- Each lane owns disjoint files. Shared files (`LnLean.lean`,
  `Obligations.lean`, `Traceability.lean`, `scripts/check-final.py`, docs) are
  integrator-owned unless a lane is explicitly assigned them.
- Build under the shared lock:
  `LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock lake build`.
- Do not use box 2 or batch sleep/poll loops. Lanes report; the parent works on
  non-overlapping integration tasks until notifications arrive.

## Wave cycle

### 1. Select

Read `docs/OPEN-ISSUES.md`. Pick up to eight lanes, preferring P0/P1 issues
with a concrete theorem or artifact. Every lane must have:

- an issue id;
- a measurable deliverable (theorem, model extension, CI artifact, doc);
- exclusive files;
- a report path `agents/reports/swarmN/S<N>-<LANE>.md`;
- a fallback: what to report if the faithful result is impossible.

### 2. Launch

Spawn `general` agents in background with the full repository context. Each
prompt must include:

```text
Repo: /home/ubuntu/ln-lean-repair
Branch: repair/integrated at <base-commit>
Read: docs/OPEN-ISSUES.md, docs/THEOREM-INDEX.md, docs/ASSUMPTIONS.md,
      agents/reports/ (relevant prior lanes), and the owned modules.
Goal: <issue id and exact deliverable>
Owned files: <exact list>
Forbidden: shared catalog/root/docs/Git, other lanes' files, vendor edits,
           full `lake build`, `collect-obligations.py`.
Policy: no sorry/axiom/admit/native_decide/unsafe/implemented_by; only
        propext, Quot.sound, Classical.choice. Keep counterexamples.
Build: scoped module build under the lock above.
Report: exact signatures, build/axiom results, scope caveats, blockers,
        and recommended catalog/doc change.
```

The parent must not duplicate a running lane's files or topic.

### 3. Integrate

When lanes return:

1. Read every report and inspect the diff.
2. Reject or narrow any lane that proved a tautology, silently assumed its
   conclusion, or changed a shared file outside ownership.
3. Add root imports only for modules that build and are intended to ship.
4. Update `Obligations.lean` status/targets/claims and source comments.
5. Regenerate the transcribed tables in `Traceability.lean`; update
   `proved_row_count`, `statement_only_row_count`, module lists, and declarations.
6. Extend `AxiomAudit` with the new headline targets and update its length
   theorem.
7. Update `EXPECTED_LEAN_FILES`, `docs/THEOREM-INDEX.md`,
   `docs/TRACEABILITY.md`, `docs/OPEN-ISSUES.md`, `docs/WAVE-STATUS.md`,
   `docs/FINAL-STATUS.md`, README counts, and generated indexes.
8. Run the gate.

### 4. Gate

```sh
export PATH=/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock lake build
python3 scripts/check-catalog.py --audit
./scripts/check.sh
python3 scripts/check-final.py
python3 scripts/verify-anchors.py
./scripts/verify-vendor.sh
grep -RInE '^[[:space:]]*sorry[[:space:]]*$' LnLean --include='*.lean' || true
```

The `grep` must return no matches. `check-catalog.py --audit` must be RC 0.
If any gate fails, do not commit the failing state; repair or drop the lane.

### 5. Commit and push

Use a proof commit and a status commit, or one combined commit if small:

```sh
git add <exact files>
git commit -m "[PROOF] <wave> ..."
git add README.md docs agents/reports
git commit -m "[STATUS] record <wave> gate and open issues"
git push origin repair/integrated
```

No `--force`. Confirm `git status --short` is clean except the pre-existing
untracked `agents/status/REPAIR.status`.

### 6. Update and repeat

Update `docs/OPEN-ISSUES.md`:

- mark closed issues with the commit and theorem/artifact;
- add new gaps discovered by the wave;
- write the next wave's lane table and base commit;
- record the gate evidence.

Then select the next eight lanes. Stop the loop only when the maintainer asks,
the remaining issues are research-only, or the gate cannot be kept green.

## Lane report template

```markdown
# S<N>-<LANE> — <issue id>

**Base:** <commit>
**Verdict:** proved / narrowed / refuted / blocked / artifact-only

## Deliverables
- <file> — <change>

## Exact result
```lean
<theorem signatures or artifact description>
```

## Build / axioms
- command:
- result:
- `#print axioms`:
- forbidden constructs:

## Scope caveats
- <explicit model/assumption boundary>

## Catalog / roadmap recommendation
- <target, status, claim rewording, issue closure>

## Blockers
- <exact missing model or bridge>
```

## Current wave

Wave 3 is complete: 48/48 catalog rows are proved, full build 182 jobs, strict
catalog audit green. Wave 4 is running from base `47189fe` (plan:
`agents/swarm/WAVE-4.md`). It targets the non-catalog gaps: L1 spendability,
vendor/CI, conformance, wire completeness, global HTLC ids, fee/dust
integration, gossip attribution, and release packaging. Results will be
integrated under the gate below, then this section will name the next wave.

## Why this is not a fully autonomous daemon

The Lean build is serialized and the integration requires judgment about
faithfulness, shared files, and catalog wording. The loop is therefore
parent-orchestrated with background child agents. A future harness can replace
the parent with a scheduler, but it must preserve the same gates and the
non-force, disjoint-file rules.
