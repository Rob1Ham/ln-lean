# Agent Protocol (wave A and wave B)

You are one of several agents working in the **same git worktree** on the
peer box. Read this file before writing anything.

## Place and tools

* Work only in `/home/ubuntu/ln-lean`.
* Lean toolchain:
  `export PATH=/dev/shm/btc/elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH`
* References (read-only): `refs/rust-lightning`, `refs/bolts`,
  `vendor/btc-lean-core`.
* Never edit `vendor/`, `refs/`, `LnLean.lean`, `lakefile.lean`,
  `lean-toolchain`, `docs/{CHARTER,ARCHITECTURE,ASSUMPTIONS,AGENT-PROTOCOL}.md`,
  or another agent's files.

## Builds

Build only your exact module, under the shared lock:

```sh
export PATH=/dev/shm/btc/elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
cd /home/ubuntu/ln-lean
flock -w 900 /tmp/ln-build.lock lake build LnLean.Your.Module
```

Do not run a bare `lake build` in the repo root. Do not run builds in the
background. If the lock times out, report it rather than killing another
agent's build.

## Lean rules

* `set_option autoImplicit false` at the top of every new file.
* Model modules must be `sorry`-free.
* `sorry` is allowed only in `LnLean/Proofs/**`, and only on the same line
  as, or immediately after, an `-- OBLIGATION: <id> <claim>` comment.
* No `axiom`, `native_decide`, `unsafe`, `@[implemented_by]`, or `admit`.
* No mathlib. If a proof needs it, state the theorem and mark it as an
  obligation instead.
* Every file starts with a module docstring containing:
  - the English claim of the module;
  - BOLT section(s);
  - `rust-lightning` `path:line` anchors at the pinned commit;
  - what is explicitly *not* modelled.
* A theorem statement must entail its English claim. If the claim is false,
  prove the corrected statement and record the counterexample in a comment.
  Never silently weaken a statement to make it go through.

## Commits

Commit your own files with:

```sh
cd /home/ubuntu/ln-lean
MSG="[LN-A1] foundation modules" ./scripts/agent-commit.sh LN-A1 \
  LnLean/Basic/Amount.lean docs/SCOPE.md agents/reports/A1.md
```

The script takes the shared git lock. Do not push, pull, or rebase. Do not
commit files you do not own. If the index is locked, the script waits; do
not retry in a tight loop.

## Reports

Write `agents/reports/<NAME>.md` with:

1. the files you created and their exact build verdicts (module, RC);
2. a table of declarations: name, statement, proved / `sorry` + obligation id;
3. the BOLT/rust-lightning anchors you used;
4. what remains open, and the next smallest step;
5. the exact commands to reproduce your build.

Commit the report in the same commit as (or immediately after) your Lean
files. A report that claims a theorem not present in the tree is a
protocol violation.

## Scope discipline

One agent, one bounded mission. If a mission grows beyond its assigned
files, stop and record the extra work as an obligation in your report
instead of editing someone else's module. The fleet's failure mode is
long uncommitted exploration, not insufficient scope.

## Final message

Your final chat message must be at most 10 lines: files, build RC, number
of obligations, and anything the integrator must merge.
