# W14-DELIVERY — non-circular delivery model (G18 / REV-06 / NET-01, model half)

**Lane:** `W14-DELIVERY` (Wave 14, branch `wave-14/16`, base `a331b71`).
**Scope:** additive model-level separation of an explicit delivery oracle from
`LnLean.Security.PartiallySynchronous`. The old definitions and
`partial_synchrony_delivers` are retained unchanged. This lane narrows G18 and
the Lean/model half of `NET-01`; it does not claim probabilistic liveness, a
real scheduler, or a bridge from `NetworkSchedule`.

## 1. Owned files

- `LnLean/Proofs/Wave14/DeliveryModel.lean` (created)
- `agents/reports/wave14/W14-DELIVERY.md` (this report)

No other file was created, modified, or deleted. `LnLean/Security/Invariants.lean`,
`LnLean/Proofs/Security/ThreatModelProps.lean`, `LnLean.lean`,
`lakefile.lean`, `AxiomAudit.lean`, `Traceability.lean`, `Obligations.lean`,
`docs/`, the catalog, `vendor/`, `refs/`, scripts, tests, and other lanes'
files are untouched. `git status` shows only the untracked
`LnLean/Proofs/Wave14/` and `agents/reports/wave14/` directories (shared with
the other Wave-14 lanes) and the pre-existing untracked
`agents/swarm/WAVE-14.md`.

Module namespace: `LnLean.Proofs.Wave14.DeliveryModel`; imports
`LnLean.Security.Invariants` (`Schedule`, `Message`,
`PartiallySynchronous`, `partial_synchrony_delivers`).

## 2. Carrier definitions

```lean
structure DeliveryOracle where
  deliver : Message → Option Nat

namespace DeliveryOracle

def DeliveredWithin (o : DeliveryOracle) (m : Message) (t : Nat) : Prop :=
  ∃ d : Nat, o.deliver m = some d ∧ d ≤ t

def EventuallyDelivered (o : DeliveryOracle) (m : Message) : Prop :=
  ∃ t : Nat, o.DeliveredWithin m t

def BoundedDeliveryAfter (o : DeliveryOracle) (gst delta : Nat) : Prop :=
  ∀ m : Message, gst ≤ m.send → o.DeliveredWithin m (m.send + delta)

def toSchedule (o : DeliveryOracle) : Schedule := ⟨o.deliver⟩
def ofSchedule (s : Schedule) : DeliveryOracle := ⟨s.latency⟩

end DeliveryOracle

structure DeliveryModel where
  gst : Nat
  delta : Nat
  oracle : DeliveryOracle
  bounded : oracle.BoundedDeliveryAfter gst delta
```

`DeliveryModel.bounded` is a *field*: the delivery assumption is data that a
consumer must supply, not a theorem about all schedules.

## 3. Headline theorems (exact statements)

```lean
theorem DeliveryOracle.eventuallyDelivered_of_bounded {o : DeliveryOracle}
    {gst delta : Nat} (h : o.BoundedDeliveryAfter gst delta) (m : Message)
    (hm : gst ≤ m.send) : o.EventuallyDelivered m

theorem DeliveryOracle.partiallySynchronous_iff_boundedDelivery
    (s : Schedule) (gst delta : Nat) :
    PartiallySynchronous gst delta s ↔
      (ofSchedule s).BoundedDeliveryAfter gst delta

theorem DeliveryOracle.toSchedule_partiallySynchronous {o : DeliveryOracle}
    {gst delta : Nat} (h : o.BoundedDeliveryAfter gst delta) :
    PartiallySynchronous gst delta o.toSchedule

theorem DeliveryModel.eventuallyDelivered (M : DeliveryModel) (m : Message)
    (hm : M.gst ≤ m.send) : M.oracle.EventuallyDelivered m

theorem DeliveryModel.partiallySynchronous (M : DeliveryModel) :
    PartiallySynchronous M.gst M.delta M.oracle.toSchedule

theorem DeliveryModel.eventuallyDelivered_of_partiallySynchronous
    (s : Schedule) (gst delta : Nat) (h : PartiallySynchronous gst delta s)
    (m : Message) (hm : gst ≤ m.send) :
    (DeliveryOracle.ofSchedule s).EventuallyDelivered m
```

Positive instances:

```lean
def zeroDelayOracle : DeliveryOracle := ⟨fun _ => some 0⟩
theorem zeroDelay_bounded (gst delta : Nat) :
    zeroDelayOracle.BoundedDeliveryAfter gst delta
theorem zeroDelayModel_eventually (m : Message) :
    zeroDelayModel.oracle.EventuallyDelivered m

def constantDelayOracle (d : Nat) : DeliveryOracle := ⟨fun _ => some d⟩
theorem constantDelay_bounded (d gst delta : Nat) (h : d ≤ delta) :
    (constantDelayOracle d).BoundedDeliveryAfter gst delta
theorem constantDelayModel_eventually (d : Nat) (m : Message) :
    (constantDelayModel d).oracle.EventuallyDelivered m
```

Negative instance and non-unconditionality:

```lean
def noDeliveryOracle : DeliveryOracle := ⟨fun _ => none⟩
theorem noDelivery_not_deliveredWithin (m : Message) (t : Nat) :
    ¬ noDeliveryOracle.DeliveredWithin m t
theorem noDelivery_not_eventually (m : Message) :
    ¬ noDeliveryOracle.EventuallyDelivered m
theorem noDelivery_not_bounded (gst delta : Nat) :
    ¬ noDeliveryOracle.BoundedDeliveryAfter gst delta

def noDeliverySchedule : Schedule := ⟨fun _ => none⟩
theorem noDeliverySchedule_not_partiallySynchronous (gst delta : Nat) :
    ¬ PartiallySynchronous gst delta noDeliverySchedule
theorem partial_synchrony_not_universal :
    ¬ ∀ s : Schedule, PartiallySynchronous 0 0 s
theorem deliveredWithin_not_unconditional (gst delta : Nat) :
    ¬ ∀ (s : Schedule) (m : Message), gst ≤ m.send →
      s.DeliveredWithin m (m.send + delta)
```

What the identification buys: `partiallySynchronous_iff_boundedDelivery` is
definitional (`Iff.rfl`) and is deliberately labelled as such — it makes the
G18 circularity auditable. The non-circular content is
`DeliveryModel.eventuallyDelivered` and
`eventuallyDelivered_of_partiallySynchronous`, which derive an existential
delivery result from the bundled assumption instead of returning it.
`deliveredWithin_not_unconditional` proves the old conclusion is false without
a hypothesis, so `partial_synchrony_delivers` cannot be restated
unconditionally in this carrier.

## 4. Non-vacuity witnesses

- `witnessMessage : Message := ⟨10, 42⟩`.
- `witness_zeroDelay_delivered`:
  `zeroDelayOracle.DeliveredWithin witnessMessage 17`.
- `witness_zeroDelay_eventually`:
  `zeroDelayModel.oracle.EventuallyDelivered witnessMessage`.
- `witness_constantDelay_delivered`:
  `(constantDelayOracle 3).DeliveredWithin witnessMessage 3 ∧
   (constantDelayModel 3).oracle.EventuallyDelivered witnessMessage`.
- `witness_noDelivery_never`:
  `noDeliveryOracle.deliver witnessMessage = none ∧
   ¬ noDeliveryOracle.EventuallyDelivered witnessMessage`.
- `witness_models_differ`: the same message is delivered by
  `zeroDelayOracle` at deadline 17 and not delivered by `noDeliveryOracle`,
  so the positive and negative carriers are concretely distinct and neither
  is empty.

All witness theorems are fully proved; the positive witnesses use the
zero-delay and delay-3 instances, and the negative witness uses the explicit
`none` oracle/schedule.

## 5. Build command and result

```sh
cd /home/ubuntu/ln-lean-waveh
export PATH=/dev/shm/btc/elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
LEAN_NUM_THREADS=1 flock -w 3600 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Proofs.Wave14.DeliveryModel
```

Result: `Build completed successfully (10 jobs).`

## 6. `#print axioms` output

The module ends with the following audit commands; the build printed:

```text
'LnLean.Proofs.Wave14.DeliveryModel.DeliveryOracle.eventuallyDelivered_of_bounded' does not depend on any axioms
'LnLean.Proofs.Wave14.DeliveryModel.DeliveryOracle.partiallySynchronous_iff_boundedDelivery' does not depend on any axioms
'LnLean.Proofs.Wave14.DeliveryModel.DeliveryModel.eventuallyDelivered' does not depend on any axioms
'LnLean.Proofs.Wave14.DeliveryModel.DeliveryModel.eventuallyDelivered_of_partiallySynchronous' does not depend on any axioms
'LnLean.Proofs.Wave14.DeliveryModel.zeroDelay_bounded' does not depend on any axioms
'LnLean.Proofs.Wave14.DeliveryModel.zeroDelayModel_eventually' does not depend on any axioms
'LnLean.Proofs.Wave14.DeliveryModel.constantDelay_bounded' depends on axioms: [propext, Quot.sound]
'LnLean.Proofs.Wave14.DeliveryModel.constantDelayModel_eventually' depends on axioms: [propext, Quot.sound]
'LnLean.Proofs.Wave14.DeliveryModel.noDelivery_not_bounded' depends on axioms: [propext]
'LnLean.Proofs.Wave14.DeliveryModel.noDeliverySchedule_not_partiallySynchronous' depends on axioms: [propext]
'LnLean.Proofs.Wave14.DeliveryModel.partial_synchrony_not_universal' depends on axioms: [propext]
'LnLean.Proofs.Wave14.DeliveryModel.deliveredWithin_not_unconditional' depends on axioms: [propext]
'LnLean.Proofs.Wave14.DeliveryModel.witness_models_differ' depends on axioms: [propext]
```

Only `propext`, `Quot.sound`, and no axioms appear; neither `Classical.choice`
nor any forbidden axiom is used. No `sorry`, `axiom`, `admit`,
`native_decide`, `unsafe`, or `@[implemented_by]` occurs.

## 7. Gap closed or narrowed

- **G18 (definitional/restatement) — narrowed, not erased.** The old
  `PartiallySynchronous` and `partial_synchrony_delivers` remain exactly as
  they were, so the catalog row is still a hypothesis restatement and must be
  worded that way. What is added is (a) an explicit oracle carrier with a
  bound as data, (b) a genuine bounded-delivery → eventual-delivery
  derivation, (c) a definitional identification of the old hypothesis with
  the oracle bound, (d) positive finite-delay instances, and (e) a retained
  `latency := fun _ => none` counterexample plus
  `deliveredWithin_not_unconditional`, which together show the old hypothesis
  cannot be dropped.
- **`REV-06` — narrowed.** The "reword docs or add a non-circular model"
  choice now has a model artifact for the delivery half; the wording change
  is still an integrator action (see §8). `channel_ready_gate` and
  `stale_snapshot_rolls_back` are untouched and remain other lanes' gaps.
- **`NET-01` — partially addressed at model level.** The module supplies one
  concrete eventual-delivery instance (delay 0 and fixed finite delay) as the
  issue requested. It does **not** state an adversarial schedule/fairness
  model for LN-SEC-003/005/006, and it does not bridge
  `NetworkSchedule.delivery` (`ThreatModelProps.lean:858-860`). `NET-01` stays
  open for the scheduler/adversary half.
- **Boundary:** these are statements about an oracle function over abstract
  `Message`s with a caller-supplied `gst`/`delta`. They are not probabilistic
  liveness, not a real network, and not a claim that any implementation
  delivers. No production `Schedule` is changed or re-pointed.

## 8. Shared-file changes for the integrator (not applied)

1. **Root import:** add `import LnLean.Proofs.Wave14.DeliveryModel` to the
   Wave-14 aggregate/root (the generated root is integrator-owned; do not
   hand-edit `LnLean.lean` in this lane).
2. **Axiom audit:** add the thirteen headline names printed in §6 to
   `LnLean/Proofs/PhaseC3/AxiomAudit.lean` and its `auditedTheorems` registry,
   or register the module's `#print axioms` output through the Wave-14
   assurance process. Expected result is `none`/`[propext]`/
   `[propext, Quot.sound]` only.
3. **Catalog / docs wording:** G18's row and the `REV-06` text should now say
   that `partial_synchrony_delivers` is a hypothesis restatement and must not
   be cited as liveness; cite
   `LnLean.Proofs.Wave14.DeliveryModel.DeliveryModel.eventuallyDelivered`
   and `...deliveredWithin_not_unconditional` as the non-circular model pair.
   `NET-01` should remain open for the adversary/`NetworkSchedule` bridge.
4. **Catalog row (if a new row is desired):** a row for the delivery model
   would target
   `LnLean.Proofs.Wave14.DeliveryModel.DeliveryModel.eventuallyDelivered`
   and `...deliveredWithin_not_unconditional`; do not re-mark the old
   `partial_synchrony_delivers` row as an unconditional liveness result.
5. **No change** to `LnLean/Security/Invariants.lean`,
   `ThreatModelProps.lean`, `ScheduleBridge`, or the old theorem is required
   or permitted by this lane.

## 9. Confirmation

Confirmed: only `LnLean/Proofs/Wave14/DeliveryModel.lean` and
`agents/reports/wave14/W14-DELIVERY.md` were written. No shared file, catalog,
docs, script, test, vendor/refs tree, or other lane's module/report was
edited. No Git write command was run; the branch remains `wave-14/16` at
`a331b71` plus untracked files.
