# W14-READY — additive channel readiness carrier

**Lane:** W14-READY (Wave 14)
**Worktree:** `/home/ubuntu/ln-lean-waveh`
**Branch:** `wave-14/16`
**Base:** `a331b71`
**Status:** complete; scoped build green (17 jobs).

## 1. Scope

Close/narrow Wave-13 review gap **G19** / `REV-06` and R32 §5.3 item 9:
`channel_ready_gate` is the conjunction of the two handshake flags, not a
claim of LDK channel readiness or usability. This lane adds an **additive**
operational-readiness carrier with explicit confirmation depth, peer
connectivity, shutdown, and splice-pending fields, proves that the two-flag
gate does **not** imply that carrier, and proves the positive direction from
the carrier back to the existing gate.

What was deliberately not done:

- `LnLean.Protocol.Handshake.channel_ready_gate` is not redefined or weakened.
  It is imported from `LnLean.Proofs.WaveD.D18` and cited by the positive
  theorem.
- `HandshakeState`, `HandshakeEvent`, `handshakeStep`, `Reachable`,
  `channelReady_reachable_without_fundingSigned`, and the entire handshake
  path are unchanged. This module only imports them.
- No existing predicate, theorem, module, catalog row, script, or docs file was
  edited.

## 2. Owned files

Only these paths were created or modified:

- `LnLean/Proofs/Wave14/ReadyUsefulness.lean`
- `agents/reports/wave14/W14-READY.md`

No shared file, root import, audit registry, catalog, docs, script, or other
lane's Lean module/report was edited.

## 3. Headline definitions and exact statements

All declarations live in namespace
`LnLean.Proofs.Wave14.ReadyUsefulness` and import only
`LnLean.Proofs.WaveD.D18` (which supplies `HandshakeState`,
`channel_ready_gate`, and the existing handshake development).

Carrier definitions:

```lean
structure Readiness where
  handshake : HandshakeState
  confirmations : Nat
  minConfirmations : Nat
  peerConnected : Bool
  shutdownStarted : Bool
  splicePending : Bool

abbrev Readiness.confirmed (r : Readiness) : Prop :=
  r.minConfirmations ≤ r.confirmations

abbrev Readiness.usable (r : Readiness) : Prop :=
  r.handshake.ready = true ∧
    r.confirmed ∧
    r.peerConnected = true ∧
    r.shutdownStarted = false ∧
    r.splicePending = false

structure UsableChannel where
  readiness : Readiness
  ready : readiness.handshake.ready = true
  confirmed : readiness.confirmed
  connected : readiness.peerConnected = true
  notShuttingDown : readiness.shutdownStarted = false
  noSplicePending : readiness.splicePending = false
```

The positive direction (cites the existing catalog theorem, does not
re-derive it):

```lean
theorem usable_implies_channel_ready_gate (u : UsableChannel) :
    u.readiness.handshake.ready = true ∧
      (u.readiness.handshake.channelReadySent = true ∧
        u.readiness.handshake.channelReadyReceived = true)

theorem usable_implies_both_flags (u : UsableChannel) :
    u.readiness.handshake.channelReadySent = true ∧
      u.readiness.handshake.channelReadyReceived = true
```

`usable_implies_channel_ready_gate` is proved by
`LnLean.Protocol.Handshake.channel_ready_gate u.readiness.handshake`; it is
the exact two-flag consequence of the retained catalog theorem.
`usable_implies_both_flags` is its flag projection.

The negative direction, one theorem per independent field:

```lean
theorem ready_zeroConfirmations_not_usable :
    ∃ r : Readiness,
      r.handshake.ready = true ∧ ¬ r.confirmed ∧ ¬ r.usable

theorem ready_disconnected_not_usable :
    ∃ r : Readiness,
      r.handshake.ready = true ∧ r.peerConnected = false ∧ ¬ r.usable

theorem ready_shutdown_not_usable :
    ∃ r : Readiness,
      r.handshake.ready = true ∧ r.shutdownStarted = true ∧ ¬ r.usable

theorem ready_splicePending_not_usable :
    ∃ r : Readiness,
      r.handshake.ready = true ∧ r.splicePending = true ∧ ¬ r.usable
```

The headline separation, with both flags true and two independent failures
(confirmation depth and peer connectivity):

```lean
theorem channel_ready_gate_not_usable :
    ∃ r : Readiness,
      r.handshake.ready = true ∧
        r.handshake.channelReadySent = true ∧
        r.handshake.channelReadyReceived = true ∧
        r.confirmations = 0 ∧
        r.peerConnected = false ∧
        ¬ r.usable
```

The uniform form shows this is not an artefact of one handshake literal; every
state satisfying the two-flag gate can be extended to an unusable record:

```lean
theorem exists_unusable_extension_of_ready (s : HandshakeState)
    (h : s.ready = true) :
    ∃ r : Readiness,
      r.handshake = s ∧ r.handshake.ready = true ∧ ¬ r.usable
```

## 4. Concrete non-vacuity witnesses and the theorems that use them

Helpers:

```lean
def twoFlagHandshake : HandshakeState :=
  { HandshakeState.initial with
      channelReadySent := true
      channelReadyReceived := true }

def witnessReadiness (confirmations : Nat) (peerConnected : Bool)
    (shutdownStarted : Bool) (splicePending : Bool) : Readiness :=
  { handshake := twoFlagHandshake
    confirmations := confirmations
    minConfirmations := 6
    peerConnected := peerConnected
    shutdownStarted := shutdownStarted
    splicePending := splicePending }
```

Negative witnesses:

- `witnessReadiness 0 true false false` — both flags true, peer connected, but
  `confirmations = 0 < 6 = minConfirmations`. Used by
  `ready_zeroConfirmations_not_usable`.
- `witnessReadiness 6 false false false` — both flags true and confirmed, but
  `peerConnected = false`. Used by `ready_disconnected_not_usable`.
- `witnessReadiness 6 true true false` — both flags true, confirmed and
  connected, but `shutdownStarted = true`. Used by
  `ready_shutdown_not_usable`.
- `witnessReadiness 6 true false true` — both flags true, confirmed and
  connected, but `splicePending = true`. Used by
  `ready_splicePending_not_usable`.
- `witnessReadiness 0 false false false` — the combined headline witness:
  both flags true, `confirmations = 0`, `peerConnected = false`. Used by
  `channel_ready_gate_not_usable`.

Positive witness:

```lean
def usableWitness : UsableChannel where
  readiness := witnessReadiness 6 true false false
  ready := rfl
  confirmed := by decide
  connected := rfl
  notShuttingDown := rfl
  noSplicePending := rfl
```

`usableWitness` has six confirmations against a required six, a connected
peer, no shutdown, and no pending splice. It is used by
`usableWitness_usable` (the carrier's `usable` predicate holds),
`usableWitness_both_flags` (applies the positive gate theorem to an inhabited
`UsableChannel`), and `usableChannel_witness`:

```lean
theorem usableChannel_witness :
    ∃ u : UsableChannel,
      u.readiness.handshake.ready = true ∧
        u.readiness.confirmed ∧
        u.readiness.confirmations = 6 ∧
        u.readiness.minConfirmations = 6 ∧
        u.readiness.peerConnected = true ∧
        u.readiness.shutdownStarted = false ∧
        u.readiness.splicePending = false
```

This proves `UsableChannel` is inhabited and that `usable` is not an
always-false predicate.

## 5. Build command and result

```sh
cd /home/ubuntu/ln-lean-waveh
export PATH=/dev/shm/btc/elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
LEAN_NUM_THREADS=1 flock -w 3600 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Proofs.Wave14.ReadyUsefulness
```

Result:

```text
ℹ [17/17] Built LnLean.Proofs.Wave14.ReadyUsefulness (684ms)
Build completed successfully (17 jobs).
```

No `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, or
`@[implemented_by]` occurs in the module. Only the scoped module build was
run; no bare `lake build`, full gate, or network command was run.

## 6. `#print axioms` output

The module ends with:

```lean
#print axioms usable_implies_channel_ready_gate
#print axioms usable_implies_both_flags
#print axioms ready_zeroConfirmations_not_usable
#print axioms ready_disconnected_not_usable
#print axioms ready_shutdown_not_usable
#print axioms ready_splicePending_not_usable
#print axioms channel_ready_gate_not_usable
#print axioms exists_unusable_extension_of_ready
#print axioms usableWitness_usable
#print axioms usableWitness_both_flags
#print axioms usableChannel_witness
```

Build output:

```text
info: LnLean/Proofs/Wave14/ReadyUsefulness.lean:308:0: 'LnLean.Proofs.Wave14.ReadyUsefulness.usable_implies_channel_ready_gate' depends on axioms: [propext]
info: LnLean/Proofs/Wave14/ReadyUsefulness.lean:309:0: 'LnLean.Proofs.Wave14.ReadyUsefulness.usable_implies_both_flags' depends on axioms: [propext]
info: LnLean/Proofs/Wave14/ReadyUsefulness.lean:310:0: 'LnLean.Proofs.Wave14.ReadyUsefulness.ready_zeroConfirmations_not_usable' does not depend on any axioms
info: LnLean/Proofs/Wave14/ReadyUsefulness.lean:311:0: 'LnLean.Proofs.Wave14.ReadyUsefulness.ready_disconnected_not_usable' does not depend on any axioms
info: LnLean/Proofs/Wave14/ReadyUsefulness.lean:312:0: 'LnLean.Proofs.Wave14.ReadyUsefulness.ready_shutdown_not_usable' does not depend on any axioms
info: LnLean/Proofs/Wave14/ReadyUsefulness.lean:313:0: 'LnLean.Proofs.Wave14.ReadyUsefulness.ready_splicePending_not_usable' does not depend on any axioms
info: LnLean/Proofs/Wave14/ReadyUsefulness.lean:314:0: 'LnLean.Proofs.Wave14.ReadyUsefulness.channel_ready_gate_not_usable' does not depend on any axioms
info: LnLean/Proofs/Wave14/ReadyUsefulness.lean:315:0: 'LnLean.Proofs.Wave14.ReadyUsefulness.exists_unusable_extension_of_ready' depends on axioms: [propext]
info: LnLean/Proofs/Wave14/ReadyUsefulness.lean:316:0: 'LnLean.Proofs.Wave14.ReadyUsefulness.usableWitness_usable' does not depend on any axioms
info: LnLean/Proofs/Wave14/ReadyUsefulness.lean:317:0: 'LnLean.Proofs.Wave14.ReadyUsefulness.usableWitness_both_flags' depends on axioms: [propext]
info: LnLean/Proofs/Wave14/ReadyUsefulness.lean:318:0: 'LnLean.Proofs.Wave14.ReadyUsefulness.usableChannel_witness' does not depend on any axioms
```

Every audited declaration is within the allowed
`propext` / `Quot.sound` / `Classical.choice` set; no `sorryAx` appears.

## 7. Review gap closed or narrowed

**G19 / `REV-06`, `channel_ready` readiness half — narrowed, not fully
closed.**

- The two-flag `channel_ready_gate` now has an explicit, named operational
  counterpart: `Readiness` plus `UsableChannel`.
- `channel_ready_gate_not_usable` records the exact defect with a concrete
  record: both flags true, `confirmations = 0`, `peerConnected = false`, and
  not usable.
- `exists_unusable_extension_of_ready` shows the separation is uniform over
  every ready handshake state, not just the chosen literal.
- The four per-field separation theorems show that confirmation depth, peer
  connectivity, shutdown, and splice-pending are independent constraints;
  none follows from the two flags.
- `usable_implies_both_flags` proves the retained catalog gate still holds of
  every usable channel, so the new carrier is a strengthening, not a
  replacement.
- `usableChannel_witness` proves the carrier is non-vacuous.

**What remains narrow / external:**

- Confirmation depth is an arithmetic `Nat` comparison. There is no Bitcoin
  chain, SPV proof, reorg model, or zero-confirmation policy. The value `6` is
  a witness choice, not a claimed BOLT constant; real callers must supply the
  negotiated `minimum_depth`.
- Peer connectivity is a `Bool`, not Noise authentication, liveness, or
  message delivery.
- Shutdown is a flag only. BOLT 2 permits `shutdown` before `channel_ready`
  (`refs/bolts/02-peer-protocol.md:2150-2152`), which this carrier records but
  does not model as a closing handshake.
- `splicePending` is a caller-declared gate only. Splice funding mutation,
  quiescence, dual funding, and commitment-version semantics remain out of
  scope (R32 G16/G26); a `false` flag is not a splice-safety proof.
- `LnLean.Protocol.Peer.receive` still does not consult `ready`; this module
  does not claim a peer-layer operational-message gate.

## 8. Shared-file changes for the integrator (stated, not applied)

1. **Root import:** add `import LnLean.Proofs.Wave14.ReadyUsefulness` through
   the Wave 14 aggregator / `scripts/regen-root.sh`. This lane did not edit
   `LnLean.lean`.
2. **Axiom audit registry:** if Wave 14 headlines are enrolled in
   `LnLean/Proofs/PhaseC3/AxiomAudit.lean`, add the eleven names listed in §6
   and matching `#print axioms` lines. Expected result: no axioms or
   `[propext]` only.
3. **Catalog / docs wording:** update the `REV-06` / G19 row to distinguish
   the retained two-flag `channel_ready_gate` from the new
   `LnLean.Proofs.Wave14.ReadyUsefulness` carrier, and do not cite
   `channel_ready_gate` as `is_channel_ready`, `is_usable`, or splice
   readiness. The integrator owns `docs/OPEN-ISSUES.md`, the catalog, and
   `Obligations.lean`.
4. **Optional docstring note:** `D18.channel_ready_gate` could point future
   readers at this module for the operational-readiness distinction. This lane
   did not edit `D18.lean` or any existing module.

## 9. Ownership confirmation

No shared or other-lane file was edited. Only the two owned paths in §2 were
written. No `git add`, `git commit`, `git push`, `git switch`, or other Git
write command was run. No network command was run. The existing
`channelReady_reachable_without_fundingSigned` theorem and handshake path were
imported unchanged, not modified.
