# Two-wave execution plan

## Wave A — 8 model agents (parallel)

Each agent creates its owned model modules, compiles them, and commits.
Wave A is intentionally independent: every domain module imports only
`LnLean.Basic.Core` and `LnLean.Bitcoin.Seam`. Cross-domain vocabulary is
duplicated only where necessary and is reconciled by the obligation layer.

Acceptance for Wave A:

1. every owned `.lean` file exists and builds with
   `flock -w 900 /tmp/ln-build.lock lake build <Module>`;
2. no `sorry`, `axiom`, `native_decide`, or `unsafe` in a model module;
3. each file has the required docstring (English claim, BOLT, LDK anchor,
   non-goals) and `set_option autoImplicit false`;
4. a report at `agents/reports/<A>.md` states files, build RCs, declarations,
   anchors, and open items;
5. the agent commits only its own paths with `[LN-Ax]`.

## Wave B — 32 proof-scaffold agents (parallel)

Every B file is under `LnLean/Proofs/`, imports the Wave A modules it needs,
and states concrete theorem/obligation propositions. `sorry` is permitted,
but only with `-- OBLIGATION: LN-<area>-<number> <English claim>` on the same
or immediately preceding line.

Acceptance for Wave B:

1. the owned file builds by name under the shared build lock;
2. every `sorry` has an obligation marker;
3. the file states at least 6 non-trivial obligations/theorems, with at least
   one checked structural lemma where the model makes it cheap;
4. a report at `agents/reports/<B>.md` lists declarations, status, anchors,
   and the next smallest proof step;
5. the agent commits only its own paths with `[LN-Bxx]`.

The integrator then regenerates `LnLean.lean`, runs `scripts/check.sh`, builds
the full library, and writes the consolidated theorem index.
