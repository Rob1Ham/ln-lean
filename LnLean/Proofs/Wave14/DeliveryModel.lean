import LnLean.Security.Invariants

/-!
# LnLean.Proofs.Wave14.DeliveryModel

Wave-14 lane `W14-DELIVERY` (review gap G18 / `REV-06` / `NET-01`).

## The defect

`LnLean.Security.PartiallySynchronous` (`LnLean/Security/Invariants.lean:483-484`)
is *defined* as

```lean
∀ m : Message, gst ≤ m.send → s.DeliveredWithin m (m.send + delta)
```

and `partial_synchrony_delivers` (`:488-491`) is exactly `hps m hm`.  The
catalog therefore proves a hypothesis restatement, not unconditional liveness:
`Schedule` permits `latency := fun _ => none`, under which no message is ever
delivered.  The old theorem is true, but it cannot be cited as a network
liveness theorem.  `ScheduleBridge` (`ThreatModelProps.lean:858-860`) records
that the timed schedule is not yet tied to the adversary's `NetworkSchedule`
either; this lane does not close that gap.

## What this module adds (additive only)

* `DeliveryOracle` — an explicit `deliver : Message → Option Nat` carrier with
  `DeliveredWithin`, `EventuallyDelivered`, and the bounded-delivery assumption
  `BoundedDeliveryAfter`.
* `DeliveryModel` — an oracle bundled with a global-stabilisation time `gst`
  and a finite delay `delta`, so the assumption is a field and cannot be
  confused with a theorem.
* `DeliveryModel.eventuallyDelivered` — the delivery conclusion is derived from
  the bundled assumption (existential, not a restatement).
* `partiallySynchronous_iff_boundedDelivery` — the old hypothesis is
  definitionally the explicit bounded-delivery assumption; the conversion goes
  through `DeliveryOracle.ofSchedule` / `toSchedule`.
* Positive instances: `zeroDelayOracle` (delay 0) and
  `constantDelayOracle d` (fixed finite delay `d ≤ delta`), each with a
  `DeliveryModel` and concrete witnesses.
* Negative instance: `noDeliveryOracle := ⟨fun _ => none⟩` and
  `noDeliverySchedule`, proving `¬ EventuallyDelivered`,
  `¬ BoundedDeliveryAfter`, and `¬ PartiallySynchronous`.  Hence the old
  hypothesis cannot be dropped.
* `deliveredWithin_not_unconditional` — the conclusion of
  `partial_synchrony_delivers` fails for an arbitrary `Schedule`, so the old
  theorem is necessarily conditional.

The old definitions, `partial_synchrony_delivers`, and `ScheduleBridge` are
retained unchanged.

## Boundaries

* This is a **model-level** statement about an oracle function.  It does not
  claim probabilistic liveness, an actual network scheduler, message
  authenticity, or that any implementation ever delivers a message.
* `gst` and `delta` are caller-supplied naturals.  The module does not derive
  them from a real network, and it does not connect `deliver` to
  `NetworkSchedule.delivery` (`ThreatModelProps.lean`); that remains the
  `ScheduleBridge` obligation.
* The positive instances are existence/non-vacuity witnesses, not claims that
  the real Internet satisfies delay 0 or any fixed bound.
-/

namespace LnLean.Proofs.Wave14.DeliveryModel

set_option autoImplicit false

open LnLean.Security

/-! ## The explicit delivery oracle -/

/-- An explicit delivery oracle: `deliver m = some d` means that message `m`
is delivered after `d` time units; `deliver m = none` means it is never
delivered.  This is deliberately the same shape as `Schedule.latency`, but the
oracle is a first-class object so an assumption about it can be named. -/
structure DeliveryOracle where
  deliver : Message → Option Nat

namespace DeliveryOracle

/-- `m` is delivered by time `t` under the oracle. -/
def DeliveredWithin (o : DeliveryOracle) (m : Message) (t : Nat) : Prop :=
  ∃ d : Nat, o.deliver m = some d ∧ d ≤ t

/-- `m` is delivered at some finite time under the oracle. -/
def EventuallyDelivered (o : DeliveryOracle) (m : Message) : Prop :=
  ∃ t : Nat, o.DeliveredWithin m t

/-- Bounded delivery after global stabilisation: every message sent at or
after `gst` is delivered within `delta` of its send time.  This is the explicit
form of the old `PartiallySynchronous` hypothesis. -/
def BoundedDeliveryAfter (o : DeliveryOracle) (gst delta : Nat) : Prop :=
  ∀ m : Message, gst ≤ m.send → o.DeliveredWithin m (m.send + delta)

/-- **Bounded delivery implies eventual delivery.**  Unlike
`partial_synchrony_delivers`, this consumes a bundled assumption and produces
the existential conclusion. -/
theorem eventuallyDelivered_of_bounded {o : DeliveryOracle} {gst delta : Nat}
    (h : o.BoundedDeliveryAfter gst delta) (m : Message)
    (hm : gst ≤ m.send) : o.EventuallyDelivered m := by
  obtain ⟨d, hd, hle⟩ := h m hm
  exact ⟨m.send + delta, d, hd, hle⟩

/-- An oracle is a timed schedule: the conversion keeps `deliver` as
`latency`. -/
def toSchedule (o : DeliveryOracle) : Schedule :=
  ⟨o.deliver⟩

/-- A timed schedule is an oracle: the conversion keeps `latency` as
`deliver`. -/
def ofSchedule (s : Schedule) : DeliveryOracle :=
  ⟨s.latency⟩

@[simp] theorem toSchedule_latency (o : DeliveryOracle) :
    o.toSchedule.latency = o.deliver := rfl

@[simp] theorem ofSchedule_deliver (s : Schedule) :
    (ofSchedule s).deliver = s.latency := rfl

/-- `DeliveredWithin` is preserved by both conversions. -/
theorem toSchedule_deliveredWithin_iff (o : DeliveryOracle) (m : Message)
    (t : Nat) : o.toSchedule.DeliveredWithin m t ↔ o.DeliveredWithin m t :=
  Iff.rfl

/-- `DeliveredWithin` is preserved by both conversions. -/
theorem ofSchedule_deliveredWithin_iff (s : Schedule) (m : Message) (t : Nat) :
    (ofSchedule s).DeliveredWithin m t ↔ s.DeliveredWithin m t :=
  Iff.rfl

/-- **An explicit bounded oracle yields the old partial-synchrony
conclusion.**  This is the forward direction of the definitional
identification below. -/
theorem toSchedule_partiallySynchronous {o : DeliveryOracle} {gst delta : Nat}
    (h : o.BoundedDeliveryAfter gst delta) :
    PartiallySynchronous gst delta o.toSchedule := by
  intro m hm
  exact h m hm

/-- **The old hypothesis is exactly a bounded-delivery assumption.**  This
theorem makes the circularity auditable: `PartiallySynchronous gst delta s`
adds no content beyond bounded delivery in the oracle language. -/
theorem partiallySynchronous_iff_boundedDelivery (s : Schedule) (gst delta : Nat) :
    PartiallySynchronous gst delta s ↔
      (ofSchedule s).BoundedDeliveryAfter gst delta :=
  Iff.rfl

end DeliveryOracle

/-! ## A bundled delivery model -/

/-- A delivery model packages an oracle with its stabilisation time and delay.
The assumption is a field, so downstream users must consume it explicitly. -/
structure DeliveryModel where
  gst : Nat
  delta : Nat
  oracle : DeliveryOracle
  bounded : oracle.BoundedDeliveryAfter gst delta

namespace DeliveryModel

/-- The delivery conclusion derived from the bundled assumption. -/
theorem eventuallyDelivered (M : DeliveryModel) (m : Message)
    (hm : M.gst ≤ m.send) : M.oracle.EventuallyDelivered m :=
  M.oracle.eventuallyDelivered_of_bounded M.bounded m hm

/-- Every bundled model satisfies the old `PartiallySynchronous` predicate on
its converted schedule.  The converse would require choosing the model fields
from the hypothesis; `ofScheduleModel` below performs that construction. -/
theorem partiallySynchronous (M : DeliveryModel) :
    PartiallySynchronous M.gst M.delta M.oracle.toSchedule :=
  M.oracle.toSchedule_partiallySynchronous M.bounded

/-- Promote an old `PartiallySynchronous` hypothesis to an explicit model.
This is the only place the old hypothesis is consumed; the model then carries
it as data. -/
def ofScheduleModel (s : Schedule) (gst delta : Nat)
    (h : PartiallySynchronous gst delta s) : DeliveryModel where
  gst := gst
  delta := delta
  oracle := DeliveryOracle.ofSchedule s
  bounded := fun m hm => h m hm

@[simp] theorem ofScheduleModel_gst (s : Schedule) (gst delta : Nat)
    (h : PartiallySynchronous gst delta s) :
    (ofScheduleModel s gst delta h).gst = gst := rfl

@[simp] theorem ofScheduleModel_delta (s : Schedule) (gst delta : Nat)
    (h : PartiallySynchronous gst delta s) :
    (ofScheduleModel s gst delta h).delta = delta := rfl

/-- **The old hypothesis yields eventual delivery in the explicit model.**
This is the non-circular consequence: given the assumption, the model proves
an existential delivery result; the assumption is not returned unchanged. -/
theorem eventuallyDelivered_of_partiallySynchronous (s : Schedule) (gst delta : Nat)
    (h : PartiallySynchronous gst delta s) (m : Message) (hm : gst ≤ m.send) :
    (DeliveryOracle.ofSchedule s).EventuallyDelivered m :=
  (ofScheduleModel s gst delta h).eventuallyDelivered m hm

end DeliveryModel

/-! ## Positive instance: delay 0 -/

/-- The oracle that delivers every message immediately. -/
def zeroDelayOracle : DeliveryOracle :=
  ⟨fun _ => some 0⟩

/-- Every message is delivered by every deadline under `zeroDelayOracle`. -/
theorem zeroDelay_deliveredWithin (m : Message) (t : Nat) :
    zeroDelayOracle.DeliveredWithin m t :=
  ⟨0, rfl, Nat.zero_le t⟩

/-- `zeroDelayOracle` satisfies bounded delivery for any `gst` and `delta`. -/
theorem zeroDelay_bounded (gst delta : Nat) :
    zeroDelayOracle.BoundedDeliveryAfter gst delta :=
  fun m _ => zeroDelay_deliveredWithin m (m.send + delta)

/-- Every message is eventually delivered under `zeroDelayOracle`. -/
theorem zeroDelay_eventually (m : Message) :
    zeroDelayOracle.EventuallyDelivered m :=
  ⟨0, zeroDelay_deliveredWithin m 0⟩

/-- A concrete immediate-delivery model. -/
def zeroDelayModel : DeliveryModel :=
  { gst := 0
    delta := 0
    oracle := zeroDelayOracle
    bounded := zeroDelay_bounded 0 0 }

/-- The bundled model really yields eventual delivery. -/
theorem zeroDelayModel_eventually (m : Message) :
    zeroDelayModel.oracle.EventuallyDelivered m :=
  zeroDelayModel.eventuallyDelivered m (Nat.zero_le m.send)

/-! ## Positive instance: a fixed finite delay -/

/-- The oracle that delivers every message after exactly `d` time units. -/
def constantDelayOracle (d : Nat) : DeliveryOracle :=
  ⟨fun _ => some d⟩

/-- A message is delivered by any deadline at least `d`. -/
theorem constantDelay_deliveredWithin (d : Nat) (m : Message) (t : Nat)
    (h : d ≤ t) : (constantDelayOracle d).DeliveredWithin m t :=
  ⟨d, rfl, h⟩

/-- A constant delay `d ≤ delta` is a bounded-delivery oracle. -/
theorem constantDelay_bounded (d gst delta : Nat) (h : d ≤ delta) :
    (constantDelayOracle d).BoundedDeliveryAfter gst delta := by
  intro m _
  exact constantDelay_deliveredWithin d m (m.send + delta) (by omega)

/-- Every message is eventually delivered under a constant finite delay. -/
theorem constantDelay_eventually (d : Nat) (m : Message) :
    (constantDelayOracle d).EventuallyDelivered m :=
  ⟨d, constantDelay_deliveredWithin d m d (Nat.le_refl d)⟩

/-- A concrete fixed-delay model with `gst = 0` and `delta = d`. -/
def constantDelayModel (d : Nat) : DeliveryModel :=
  { gst := 0
    delta := d
    oracle := constantDelayOracle d
    bounded := constantDelay_bounded d 0 d (Nat.le_refl d) }

/-- The fixed-delay model yields eventual delivery for every message. -/
theorem constantDelayModel_eventually (d : Nat) (m : Message) :
    (constantDelayModel d).oracle.EventuallyDelivered m :=
  (constantDelayModel d).eventuallyDelivered m (Nat.zero_le m.send)

/-! ## Negative instance: no delivery -/

/-- The oracle that never delivers anything. -/
def noDeliveryOracle : DeliveryOracle :=
  ⟨fun _ => none⟩

@[simp] theorem noDelivery_deliver (m : Message) :
    noDeliveryOracle.deliver m = none := rfl

/-- Nothing is delivered by any deadline under `noDeliveryOracle`. -/
theorem noDelivery_not_deliveredWithin (m : Message) (t : Nat) :
    ¬ noDeliveryOracle.DeliveredWithin m t := by
  rintro ⟨d, hd, _⟩
  simp [noDeliveryOracle] at hd

/-- Nothing is eventually delivered under `noDeliveryOracle`. -/
theorem noDelivery_not_eventually (m : Message) :
    ¬ noDeliveryOracle.EventuallyDelivered m := by
  rintro ⟨t, ht⟩
  exact noDelivery_not_deliveredWithin m t ht

/-- `noDeliveryOracle` is not a bounded-delivery oracle for any parameters. -/
theorem noDelivery_not_bounded (gst delta : Nat) :
    ¬ noDeliveryOracle.BoundedDeliveryAfter gst delta := by
  intro h
  exact noDelivery_not_deliveredWithin ⟨gst, 0⟩ (gst + delta)
    (h ⟨gst, 0⟩ (Nat.le_refl gst))

/-- The old timed schedule with `latency := fun _ => none`.  This is the
counterexample named in R32 §5.1 and it is retained here. -/
def noDeliverySchedule : Schedule :=
  ⟨fun _ => none⟩

/-- No message is delivered by any deadline in `noDeliverySchedule`. -/
theorem noDeliverySchedule_not_deliveredWithin (m : Message) (t : Nat) :
    ¬ noDeliverySchedule.DeliveredWithin m t := by
  rintro ⟨d, hd, _⟩
  simp [noDeliverySchedule] at hd

/-- **The old `PartiallySynchronous` hypothesis is not unconditional.**  For
every `gst` and `delta`, `noDeliverySchedule` refutes it. -/
theorem noDeliverySchedule_not_partiallySynchronous (gst delta : Nat) :
    ¬ PartiallySynchronous gst delta noDeliverySchedule := by
  intro h
  exact noDeliverySchedule_not_deliveredWithin ⟨gst, 0⟩ (gst + delta)
    (h ⟨gst, 0⟩ (Nat.le_refl gst))

/-- There is no schedule that is partially synchronous for all parameters. -/
theorem partial_synchrony_not_universal :
    ¬ ∀ s : Schedule, PartiallySynchronous 0 0 s := by
  intro h
  exact noDeliverySchedule_not_partiallySynchronous 0 0 (h noDeliverySchedule)

/-- **The conclusion of `partial_synchrony_delivers` is not unconditional.**
For any `gst` and `delta` there is a schedule and a message sent after `gst`
that is not delivered within `delta`.  Hence the old theorem *must* carry its
hypothesis; it cannot be restated without one. -/
theorem deliveredWithin_not_unconditional (gst delta : Nat) :
    ¬ ∀ (s : Schedule) (m : Message), gst ≤ m.send →
      s.DeliveredWithin m (m.send + delta) := by
  intro h
  exact noDeliverySchedule_not_partiallySynchronous gst delta
    (fun m hm => h noDeliverySchedule m hm)

/-! ## Concrete non-vacuity witnesses -/

/-- A concrete message: sent at time 10, tag 42. -/
def witnessMessage : Message :=
  ⟨10, 42⟩

/-- The zero-delay oracle really delivers `witnessMessage`, at deadline 17. -/
theorem witness_zeroDelay_delivered :
    zeroDelayOracle.DeliveredWithin witnessMessage 17 :=
  zeroDelay_deliveredWithin witnessMessage 17

/-- The zero-delay model really eventually delivers `witnessMessage`. -/
theorem witness_zeroDelay_eventually :
    zeroDelayModel.oracle.EventuallyDelivered witnessMessage :=
  zeroDelayModel_eventually witnessMessage

/-- A fixed delay of 3 delivers `witnessMessage` by deadline 3, and the
`constantDelayModel 3` is a genuine model. -/
theorem witness_constantDelay_delivered :
    (constantDelayOracle 3).DeliveredWithin witnessMessage 3 ∧
      (constantDelayModel 3).oracle.EventuallyDelivered witnessMessage :=
  ⟨constantDelay_deliveredWithin 3 witnessMessage 3 (Nat.le_refl 3),
   constantDelayModel_eventually 3 witnessMessage⟩

/-- The negative witness is inhabited and refutes delivery: `witnessMessage`
is never delivered by `noDeliveryOracle`. -/
theorem witness_noDelivery_never :
    noDeliveryOracle.deliver witnessMessage = none ∧
      ¬ noDeliveryOracle.EventuallyDelivered witnessMessage :=
  ⟨rfl, noDelivery_not_eventually witnessMessage⟩

/-- The same message is delivered by the zero-delay oracle and not by the
no-delivery oracle, so the two models are concretely distinct. -/
theorem witness_models_differ :
    zeroDelayOracle.DeliveredWithin witnessMessage 17 ∧
      ¬ noDeliveryOracle.DeliveredWithin witnessMessage 17 :=
  ⟨witness_zeroDelay_delivered,
   noDelivery_not_deliveredWithin witnessMessage 17⟩

/-! ## Axiom audit -/

#print axioms DeliveryOracle.eventuallyDelivered_of_bounded
#print axioms DeliveryOracle.partiallySynchronous_iff_boundedDelivery
#print axioms DeliveryModel.eventuallyDelivered
#print axioms DeliveryModel.eventuallyDelivered_of_partiallySynchronous
#print axioms zeroDelay_bounded
#print axioms zeroDelayModel_eventually
#print axioms constantDelay_bounded
#print axioms constantDelayModel_eventually
#print axioms noDelivery_not_bounded
#print axioms noDeliverySchedule_not_partiallySynchronous
#print axioms partial_synchrony_not_universal
#print axioms deliveredWithin_not_unconditional
#print axioms witness_models_differ

end LnLean.Proofs.Wave14.DeliveryModel
