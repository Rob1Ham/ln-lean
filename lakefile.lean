import Lake
open Lake DSL

/-!
# ln-lean — Lightning Network formal model and proof scaffold

This workspace is intentionally split the same way as `btc-lean`:

* `LnLean/`        — executable model, definitions, and theorem statements.
* `vendor/btc-lean-core` — the existing Bitcoin L1 model, consumed as a
  path dependency.  Lightning never re-defines Bitcoin transaction or
  script primitives locally; it imports `Bitcoin.Data.*`.

Dependency policy (see `docs/ASSUMPTIONS.md`):

* No mathlib in the scaffold.  The model is plain Lean 4 so that a clean
  `lake build` is fast and every agent can verify its own module.
* `sorry` is permitted only in `LnLean/Proofs/**` and only alongside an
  `-- OBLIGATION:` marker.  Model modules must be `sorry`-free.
* No new `axiom` declarations, no `native_decide`, no `unsafe`.
-/

package «lnlean» where
  description := "ln-lean: formal model and proof scaffold for the Lightning Network on top of btc-lean"

require «core» from "vendor/btc-lean-core"

@[default_target]
lean_lib LnLean where
  roots := #[`LnLean]
