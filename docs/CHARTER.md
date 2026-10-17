# ln-lean Charter

**Status:** scaffold phase (wave A: 8 agents; wave B: 32 agents).
**Owner:** integrator (orchestrator on `sensitive-isolated-box`).
**Execution host:** `sensitive-isolated-box-2` (172.31.96.235, 48 vCPU, 185 GiB).
**L1 dependency:** `btc-lean` `spec/core` (Bitcoin consensus model).
**L2 reference:** `lightningdevkit/rust-lightning` at a pinned commit.

## 1. What this repository is

`ln-lean` is a machine-checked formal model of the Lightning Network, built as
a layered extension of the existing Bitcoin L1 formalization in `btc-lean`.
It is **not** a re-implementation of `rust-lightning`; it is a mathematical
model whose definitions are anchored to BOLT specifications and to
`rust-lightning` source locations, and whose theorems state the safety and
liveness properties the protocol is supposed to have.

The repository has two jobs:

1. **Executable model.** Definitions for amounts, wire messages, channel
   state, commitment transactions, HTLCs, revocation, onion routing, gossip,
   invoices, and payment flow. These definitions are plain Lean 4 and must
   compile without `sorry`.
2. **Proof surface.** A named obligation for every property that matters,
   with theorem statements and proofs where tractable in the scaffold phase.
   Unproved statements carry `-- OBLIGATION: LN-...` and are listed in
   `docs/THEOREM-INDEX.md` and `docs/TRACEABILITY.md`.

## 2. Non-goals (scaffold phase)

* A complete proof of Lightning safety. The scaffold establishes the module
  graph, the definitions, the obligation catalog, and the proof interfaces.
* A bit-exact implementation of BOLT wire serialization. The model is
  close enough to state protocol properties; differential conformance is a
  later phase.
* A model of the Bitcoin P2P layer, mempool policy, or fee estimation
  beyond the interfaces Lightning consumes.
* Multi-party channel factories, splicing, or eltoo. These are explicitly
  out of scope until the base channel model is closed.

## 3. Layering

```
BOLT 1/2/3/4/5/7/11/12
        │
        ▼
LnLean.Protocol / Wire        messages, features, handshake
LnLean.Channel                state machine, commitments, HTLC, revocation
LnLean.Routing                gossip graph, route construction, onion
LnLean.Payment               invoices, payment sessions, MPP
        │
        ▼
LnLean.Bitcoin.Seam           funding/commitment scripts, anchors, weights
        │
        ▼
btc-lean Bitcoin.Data.*       Tx, TxOut, OutPoint, Script, Amount, MoneyRange
```

Dependencies point downward only. A module may import its own layer and the
layers below it. Cross-domain imports are allowed only through
`LnLean.Basic.Core` and `LnLean.Bitcoin.Seam` during wave A; wave B may import
the wave-A modules in the same domain.

## 4. Trust boundary and assumptions

The model is parameterized by cryptographic primitives. We do **not** prove
SHA-256 collision resistance, ECDSA/Schnorr unforgeability, or the
indistinguishability of ChaCha20-Poly1305. Instead:

* `LnLean.Crypto.Model` declares a structure of primitive operations and
  their assumed properties as `Prop`s.
* Every theorem that depends on a primitive assumption names it explicitly
  (e.g. `h_collision : CollisionResistant H`).
* The L1 seam trusts `btc-lean`'s transaction and script semantics. The
  exact commit of `vendor/btc-lean-core` is recorded in
  `docs/ASSUMPTIONS.md` and `vendor/btc-lean-core/COMMIT`.

The network is asynchronous and reliable-delivery is **not** assumed.
Message loss, reordering, and partition are modelled as adversarial
schedules. Liveness theorems therefore carry fairness/partial-synchrony
hypotheses; safety theorems do not.

## 5. Honesty rules

1. A theorem's statement must entail its English claim. A same-named
   theorem that proves something weaker is a finding, not a proof.
2. `sorry` is allowed only in `LnLean/Proofs/**` and only with an
   `-- OBLIGATION:` marker naming the claim and its traceability id.
3. No `axiom`, no `native_decide`, no `unsafe`, no `@[implemented_by]` in
   model or proof modules.
4. If a claimed property is false, prove the corrected statement and record
   the counterexample. Never silently weaken.
5. Every definition and theorem carries an anchor: BOLT section, and/or
   `rust-lightning` `path:line` at the pinned commit.

## 6. Phases

| Phase | Agents | Deliverable | Gate |
|---|---|---|---|
| A | 8 | Foundation modules, domain models, obligation catalog, traceability | `lake build` green; every model module `sorry`-free |
| B | 32 | One focused module + proof statements per agent; obligation inventory | `lake build` green; every `sorry` has an obligation id; index regenerated |
| C (future) | — | Close obligations, add mathlib where needed, differential tests | no `sorry` in agreed core; axiom audit |

## 7. Success criteria for this scaffold

* A clean checkout builds on the peer with `lake build` and no errors.
* `docs/THEOREM-INDEX.md` lists every theorem declaration and its status.
* `docs/TRACEABILITY.md` maps every obligation to a BOLT section and a
  `rust-lightning` location.
* `docs/ASSUMPTIONS.md` states exactly what is trusted.
* The 40 agent reports exist and agree with the artifact (no report claims
  a theorem that is not in the tree).

## 8. Coordination

All agent work happens on the peer. The orchestrator owns `LnLean.lean`,
`lakefile.lean`, this charter, and integration commits. Agents own only the
paths assigned in `agents/OWNERSHIP.md` and must commit with
`scripts/agent-commit.sh`. Builds take the shared lock
`/tmp/ln-build.lock`; git takes `/tmp/ln-git.lock`.
