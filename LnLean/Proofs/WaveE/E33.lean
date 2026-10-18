import LnLean.Security.Invariants
import LnLean.Security.Model

/-!
# LnLean.Proofs.WaveE.E33

English claim (catalog `LN-SEC-003`).  *Safety holds under an asynchronous
adversarial schedule, without a fairness hypothesis.*

What this module proves.  The wave-A model represents a protocol execution as
a `SecurityGame`: a total transition function `step : State → Adversary → Nat →
State`, an initial state, and a bad-event predicate.  Safety is
`Secure g := ∀ n, ¬ g.bad (g.run n)`, i.e. no finite horizon reaches `bad`.

1. **Safety by invariant induction (`waveE_e33_secure_of_invariant`).**  If a
   state predicate `Safe` holds initially, is preserved by `step` for *every*
   adversary and every step index, and implies the negation of `bad`, then the
   game is `Secure`.  No condition on `NetworkSchedule.delivery`,
   `partition`, `maxDelay`, `reorders`, or `dropsMessages` occurs in the
   statement: this is exactly "safety needs no fairness hypothesis".
2. **An asynchronous channel network (`asyncChannelGame`).**  The state is a
   `Ledger` (the four-bucket value model of `LnLean.Security.Invariants`) plus
   a queue of `ChannelMsg`s (`update_add_htlc` / fulfil / fail / fee as
   `LedgerOp`s).  At step `n`, the head message is applied only if
   `Adversary.schedule.delivery n dst = true` and the pair `(src, dst)` is not
   partitioned; otherwise the queue is unchanged, modelling a message delayed
   beyond the horizon.  Arbitrary delivery, partition, delay, loss, and
   reordering are all in scope because the theorem quantifies over every
   `Adversary` and every initial queue.  Every available ledger transition
   preserves value conservation (`Ledger.step_conserves`), and an unavailable
   transition is a stutter, so `Ledger.Conserves` is inductive and the game is
   `Secure` for every adversary.
3. **Order irrelevance (`waveE_e33_applyAll_conserves`).**  Any finite list of
   ledger operations, applied in any order with availability checks, preserves
   conservation.  This is the local reason reordering cannot break safety.
4. **Separation from liveness (`waveE_e33_lossy_liveness_fails`).**  A schedule
   that never delivers (and a fully partitioned one) makes no progress at all,
   so no liveness property holds, yet the safety theorem still applies.  Thus
   fairness is needed for liveness, not for safety.
5. **Arbitrary schedule fields (`waveE_e33_no_fairness_needed`).**  The
   headline is restated with the four schedule fields and the two Boolean
   refinements as universally quantified parameters, so a reader can see that
   none of them is assumed fair, bounded, or eventually-delivering.

What is NOT modelled.  `SecurityGame.step` is still an unconstrained field;
this module supplies one concrete asynchronous instance (the ledger game) and
a generic induction principle, not a refinement of the real
`channelmanager.rs` state machine.  The adversary is a network adversary: the
corruption set is empty in the example adversaries, because the protected
event here is ledger conservation rather than a per-node payment event.  The
`NetworkSchedule` type has no reordering chooser, so reordering is represented
by an arbitrary initial queue order; the order-irrelevance lemma plus the
`∀ queue` quantification make that representation complete for safety.

BOLT 2 §"Message Retransmission"; `channelmanager.rs:17831`
(`handle_channel_reestablish`).  No `sorry`, `axiom`, `admit`, `native_decide`,
`unsafe`, or `@[implemented_by]` is used.
-/

namespace LnLean.Proofs.WaveE.E33

open LnLean.Security

set_option autoImplicit false

-- OBLIGATION: LN-WE-E33

/-! ## 1. Invariant induction over an arbitrary adversarial run -/

/-- **Safety by induction on the horizon.**  If `Safe` holds initially and is
preserved by the transition under every adversary and every step index, then
`Safe` holds at every finite horizon.  The schedule never appears: this is the
generic form of "safety is a closed property". -/
theorem waveE_e33_run_invariant {State : Type} (g : SecurityGame State)
    (Safe : State → Prop) (hinit : Safe g.init)
    (hstep : ∀ (s : State) (a : Adversary) (n : Nat), Safe s →
      Safe (g.step s a n)) :
    ∀ n : Nat, Safe (g.run n) := by
  intro n
  induction n with
  | zero => simpa using hinit
  | succ k ih =>
      rw [SecurityGame.run_succ]
      exact hstep (g.run k) g.adversary k ih

/-- **A game is secure when `bad` is excluded by an inductive invariant.**
Quantification is over all adversaries, hence over every asynchronous schedule,
with no fairness, bounded-delay, or eventual-delivery hypothesis. -/
theorem waveE_e33_secure_of_invariant {State : Type} (g : SecurityGame State)
    (Safe : State → Prop) (hinit : Safe g.init)
    (hstep : ∀ (s : State) (a : Adversary) (n : Nat), Safe s →
      Safe (g.step s a n))
    (hbad : ∀ s : State, g.bad s → ¬ Safe s) :
    Secure g := by
  intro n hb
  exact hbad (g.run n) hb (waveE_e33_run_invariant g Safe hinit hstep n)

/-! ## 2. An asynchronous channel network -/

/-- A protocol message in flight: a ledger transition with a sender and a
recipient.  BOLT 2 `update_add_htlc`, `update_fulfill_htlc`,
`update_fail_htlc` and `update_fee` are all `LedgerOp`s. -/
structure ChannelMsg where
  src : NodeId
  dst : NodeId
  op : LedgerOp
deriving Repr

/-- The asynchronous state: the value ledger and the queue of messages that
the adversary has not delivered before the horizon. -/
structure AsyncChannelState where
  ledger : Ledger
  queue : List ChannelMsg
deriving Repr

/-- A message is deliverable at step `n` when the adversary's bit is set and
the two endpoints are not partitioned.  The model's `partition` field is
symmetric by convention. -/
def delivered (a : Adversary) (n : Nat) (m : ChannelMsg) : Bool :=
  a.schedule.delivery n m.dst && (a.schedule.partition m.src m.dst == false)

/-- One asynchronous step.  The adversary schedules at most the head message:
if it is deliverable, its ledger operation is applied when available and the
message is dequeued; if not, the whole state stutters (the message is delayed
beyond the horizon).  A rejected operation is a stutter via `Option.getD`. -/
def asyncStep (s : AsyncChannelState) (a : Adversary) (n : Nat) :
    AsyncChannelState :=
  match s.queue with
  | [] => s
  | m :: rest =>
      if delivered a n m then
        { ledger := (s.ledger.step m.op).getD s.ledger, queue := rest }
      else
        s

/-- The empty-queue equation of `asyncStep` (definitional). -/
theorem asyncStep_nil (l : Ledger) (a : Adversary) (n : Nat) :
    asyncStep ⟨l, []⟩ a n = ⟨l, []⟩ := rfl

/-- The non-empty-queue equation of `asyncStep` (definitional). -/
theorem asyncStep_cons (l : Ledger) (m : ChannelMsg) (rest : List ChannelMsg)
    (a : Adversary) (n : Nat) :
    asyncStep ⟨l, m :: rest⟩ a n =
      if delivered a n m then
        { ledger := (l.step m.op).getD l, queue := rest }
      else
        { ledger := l, queue := m :: rest } := rfl

/-- **Every single transition preserves conservation.**  Whether the message is
delivered or delayed, and whether the operation is available or rejected,
`local + remote + in-flight + fee = funding` is preserved. -/
theorem waveE_e33_getD_step_conserves (l : Ledger) (op : LedgerOp)
    (h : l.Conserves) : ((l.step op).getD l).Conserves := by
  cases hstep : l.step op with
  | none => simpa [hstep] using h
  | some l' => simpa [hstep] using Ledger.step_conserves l l' op h hstep

/-- **The asynchronous step preserves conservation.** -/
theorem waveE_e33_asyncStep_conserves (s : AsyncChannelState) (a : Adversary)
    (n : Nat) (h : s.ledger.Conserves) : (asyncStep s a n).ledger.Conserves := by
  rcases s with ⟨l, q⟩
  cases q with
  | nil => simpa [asyncStep_nil] using h
  | cons m rest =>
      rw [asyncStep_cons]
      split
      · exact waveE_e33_getD_step_conserves l m.op h
      · exact h

/-- The game induced by an asynchronous channel state.  The bad event is
precisely a loss of value conservation. -/
def asyncChannelGame (init : AsyncChannelState) (a : Adversary) :
    SecurityGame AsyncChannelState where
  adversary := a
  init := init
  step := fun s a' n => asyncStep s a' n
  bad := fun s => ¬ s.ledger.Conserves
  honest := []

/-- **LN-SEC-003, headline.**  Safety (value conservation) holds for every
adversary, every initial queue order, and every finite horizon.  There is no
fairness, partial-synchrony, bounded-delay, or eventual-delivery hypothesis. -/
theorem waveE_e33_safety_async (init : AsyncChannelState)
    (hinit : init.ledger.Conserves) (a : Adversary) :
    Secure (asyncChannelGame init a) := by
  apply waveE_e33_secure_of_invariant
    (Safe := fun s : AsyncChannelState => s.ledger.Conserves)
  · exact hinit
  · intro s a' n hs
    exact waveE_e33_asyncStep_conserves s a' n hs
  · intro s hb hs
    exact hb hs

/-- The conservation invariant at every horizon of every asynchronous run. -/
theorem waveE_e33_run_conserves (init : AsyncChannelState)
    (hinit : init.ledger.Conserves) (a : Adversary) (n : Nat) :
    ((asyncChannelGame init a).run n).ledger.Conserves :=
  waveE_e33_run_invariant (asyncChannelGame init a)
    (fun s : AsyncChannelState => s.ledger.Conserves) hinit
    (fun s a' n hs => waveE_e33_asyncStep_conserves s a' n hs) n

/-! ## 3. Any order of operations preserves conservation -/

/-- Apply a list of ledger operations in the given order, stuttering on an
unavailable operation. -/
def applyAll (ops : List LedgerOp) (l : Ledger) : Ledger :=
  ops.foldl (fun l op => (l.step op).getD l) l

/-- **Order irrelevance for safety.**  Any finite sequence of protocol
transitions, in any order, preserves value conservation.  Reordering or
dropping messages therefore cannot break the invariant. -/
theorem waveE_e33_applyAll_conserves (ops : List LedgerOp) (l : Ledger)
    (h : l.Conserves) : (applyAll ops l).Conserves := by
  induction ops generalizing l with
  | nil => simpa [applyAll] using h
  | cons op rest ih =>
      exact ih ((l.step op).getD l) (waveE_e33_getD_step_conserves l op h)

/-! ## 4. Concrete adversarial schedules -/

/-- A schedule that delivers nothing: every message is delayed beyond the
horizon.  `reorders` and `dropsMessages` are set adversarially. -/
def lossySchedule : NetworkSchedule where
  delivery := fun _ _ => false
  partition := fun _ _ => false
  maxDelay := 0
  reorders := true
  dropsMessages := true

/-- A schedule that delivers everything at every step, in queue order.  This is
the strongest delivery schedule; it still permits an arbitrary initial queue
order, and the safety theorem covers it. -/
def chaoticSchedule : NetworkSchedule where
  delivery := fun _ _ => true
  partition := fun _ _ => false
  maxDelay := 0
  reorders := true
  dropsMessages := false

/-- A schedule that declares every pair partitioned, whatever the delivery
bits say. -/
def fullyPartitionedSchedule : NetworkSchedule where
  delivery := fun _ _ => true
  partition := fun _ _ => true
  maxDelay := 1000000
  reorders := true
  dropsMessages := false

/-- A network adversary with no node corruption, no reorg budget, and zero
fees, used as the common record for the schedule examples. -/
def baseAdversary : Adversary where
  schedule := chaoticSchedule
  corruption := .none
  corrupted := []
  reorgDepth := 0
  reorgBudget := 0
  fees := { base := ⟨0⟩, atHeight := fun _ => ⟨0⟩, spikeAt := none }
  learnsPreimages := false
  adaptive := false

def lossyAdversary : Adversary := { baseAdversary with schedule := lossySchedule }
def chaoticAdversary : Adversary := { baseAdversary with schedule := chaoticSchedule }
def fullyPartitionedAdversary : Adversary :=
  { baseAdversary with schedule := fullyPartitionedSchedule }

/-- Under the lossy schedule every step is a stutter. -/
theorem waveE_e33_lossy_step_stutters (s : AsyncChannelState) (n : Nat) :
    asyncStep s lossyAdversary n = s := by
  rcases s with ⟨l, q⟩
  cases q with
  | nil => rfl
  | cons m rest =>
      simp [asyncStep, lossyAdversary, baseAdversary, lossySchedule, delivered]

/-- Hence the lossy run is constantly the initial state. -/
theorem waveE_e33_lossy_run_eq (init : AsyncChannelState) (n : Nat) :
    (asyncChannelGame init lossyAdversary).run n = init := by
  induction n with
  | zero => rfl
  | succ k ih =>
      rw [SecurityGame.run_succ, ih]
      exact waveE_e33_lossy_step_stutters init k

/-- Under a fully partitioned schedule every step is also a stutter. -/
theorem waveE_e33_partitioned_step_stutters (s : AsyncChannelState) (n : Nat) :
    asyncStep s fullyPartitionedAdversary n = s := by
  rcases s with ⟨l, q⟩
  cases q with
  | nil => rfl
  | cons m rest =>
      simp [asyncStep, fullyPartitionedAdversary, baseAdversary,
        fullyPartitionedSchedule, delivered]

/-- Under the chaotic schedule the head message is always dequeued. -/
theorem waveE_e33_chaotic_step_queue (s : AsyncChannelState) (n : Nat) :
    (asyncStep s chaoticAdversary n).queue = s.queue.drop 1 := by
  rcases s with ⟨l, q⟩
  cases q with
  | nil => rfl
  | cons m rest =>
      simp [asyncStep, chaoticAdversary, baseAdversary, chaoticSchedule, delivered]

/-- Under the chaotic schedule, after `n` steps exactly the first `n` messages
have been consumed. -/
theorem waveE_e33_chaotic_run_queue (init : AsyncChannelState) (n : Nat) :
    ((asyncChannelGame init chaoticAdversary).run n).queue = init.queue.drop n := by
  induction n with
  | zero => rfl
  | succ k ih =>
      rw [SecurityGame.run_succ]
      change (asyncStep ((asyncChannelGame init chaoticAdversary).run k)
        chaoticAdversary k).queue = init.queue.drop (k + 1)
      rw [waveE_e33_chaotic_step_queue, ih]
      simp [List.drop_drop]

/-- The chaotic schedule really delivers every queued message: after
`queue.length` steps the queue is empty.  Safety is therefore not vacuous on
this instance. -/
theorem waveE_e33_chaotic_delivers_all (init : AsyncChannelState) :
    ((asyncChannelGame init chaoticAdversary).run init.queue.length).queue = [] := by
  rw [waveE_e33_chaotic_run_queue]
  simp

/-- A conserving starting ledger: 1000 msat local, nothing elsewhere. -/
def genesisLedger : Ledger where
  funding := ⟨1000⟩
  localBalance := ⟨1000⟩
  remoteBalance := ⟨0⟩
  inFlight := ⟨0⟩
  fee := ⟨0⟩

theorem waveE_e33_genesisLedger_conserves : genesisLedger.Conserves := by
  simp [genesisLedger, Ledger.Conserves, Ledger.total]

/-- An `update_add_htlc` for 100 msat from node 0 to node 1. -/
def exampleMsg : ChannelMsg where
  src := 0
  dst := 1
  op := .addHtlc ⟨100⟩

def lossyInit : AsyncChannelState where
  ledger := genesisLedger
  queue := [exampleMsg]

/-! ## 5. Safety holds where liveness fails -/

/-- A run has made progress when its message queue is empty. -/
def asyncProgress (s : AsyncChannelState) : Prop := s.queue = []

/-- **Fairness is needed for liveness, not for safety.**  There is an
asynchronous run whose safety invariant holds at every horizon while its queue
never empties, so no progress/liveness property is true. -/
theorem waveE_e33_lossy_liveness_fails :
    ∃ (init : AsyncChannelState) (a : Adversary),
      init.ledger.Conserves ∧ Secure (asyncChannelGame init a) ∧
        (∀ n : Nat, ¬ asyncProgress ((asyncChannelGame init a).run n)) := by
  refine ⟨lossyInit, lossyAdversary, waveE_e33_genesisLedger_conserves, ?_, ?_⟩
  · exact waveE_e33_safety_async lossyInit waveE_e33_genesisLedger_conserves
      lossyAdversary
  · intro n h
    have hrun := waveE_e33_lossy_run_eq lossyInit n
    rw [hrun] at h
    simp [asyncProgress, lossyInit] at h

/-- The partitioned run has the same separation: safety holds, progress never
happens. -/
theorem waveE_e33_partitioned_liveness_fails :
    ∃ (init : AsyncChannelState) (a : Adversary),
      init.ledger.Conserves ∧ Secure (asyncChannelGame init a) ∧
        (∀ n : Nat, ¬ asyncProgress ((asyncChannelGame init a).run n)) := by
  refine ⟨lossyInit, fullyPartitionedAdversary,
    waveE_e33_genesisLedger_conserves, ?_, ?_⟩
  · exact waveE_e33_safety_async lossyInit waveE_e33_genesisLedger_conserves
      fullyPartitionedAdversary
  · intro n h
    have hstut : ∀ k : Nat,
        (asyncChannelGame lossyInit fullyPartitionedAdversary).run k = lossyInit := by
      intro k
      induction k with
      | zero => rfl
      | succ j ih =>
          rw [SecurityGame.run_succ, ih]
          exact waveE_e33_partitioned_step_stutters lossyInit j
    rw [hstut n] at h
    simp [asyncProgress, lossyInit] at h

/-- **No fairness hypothesis appears.**  The headline is re-derived with the
four schedule fields and the two Boolean refinements universally quantified:
any delivery function, any partition relation, any delay bound, and any
reordering/loss flags still give `Secure`. -/
theorem waveE_e33_no_fairness_needed
    (delivery : Nat → NodeId → Bool) (partition : NodeId → NodeId → Bool)
    (maxDelay : Nat) (reorders dropsMessages : Bool)
    (init : AsyncChannelState) (hinit : init.ledger.Conserves) :
    Secure (asyncChannelGame init
      { baseAdversary with
        schedule :=
          { delivery := delivery
            partition := partition
            maxDelay := maxDelay
            reorders := reorders
            dropsMessages := dropsMessages } }) :=
  waveE_e33_safety_async init hinit _

/-- The chaotic run is non-vacuous: the example `update_add_htlc` is delivered
and moves 100 msat from the local balance into the in-flight bucket while the
total is unchanged. -/
theorem waveE_e33_chaotic_inflight_after_one :
    ((asyncChannelGame lossyInit chaoticAdversary).run 1).ledger.inFlight.val = 100 := by
  rw [show (asyncChannelGame lossyInit chaoticAdversary).run 1 =
      (asyncStep lossyInit chaoticAdversary 0) from rfl]
  simp [asyncStep, lossyInit, genesisLedger, exampleMsg, chaoticAdversary,
    baseAdversary, chaoticSchedule, delivered, Ledger.step]

end LnLean.Proofs.WaveE.E33
