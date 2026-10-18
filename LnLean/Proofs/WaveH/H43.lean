/-
# H43 — an adversarial schedule/fairness model and one eventual-delivery instance
(NET-01, SEC-01)

## English claim

`docs/OPEN-ISSUES.md` records `NET-01` as: "Network/liveness results depend on
scheduling/fairness assumptions."  The tree already has scheduler theorems
(`LnLean.Proofs.Liveness`) and an invariant named "liveness under partial
synchrony" (`LnLean.Security.Invariants`, `INV-10`), but it has no explicit
*adversary* object with stated capabilities and no worked instance showing that
the fairness hypotheses are simultaneously satisfiable and non-trivial.

This module supplies exactly that, additively:

1. **An explicit adversarial delivery model.**  `Packet` is a message with a
   send time; `AdvSchedule` is the adversary's pair of choices: when a packet
   is delivered (`deliverAt`, with `none` meaning a permanent drop) and when it
   is retransmitted (`attemptTime`, `attemptScheduled`).  The predicates are
   explicit premises, never axioms:
   * `Causal` — no packet is delivered before it is sent;
   * `FiniteDelay gst delta` — after the global stabilisation time `gst`, a
     packet is delivered within `delta` of its send time;
   * `AttemptTimesUnbounded` — the honest sender keeps retransmitting forever;
   * `FairAttempts` — no packet is lost forever by the link: every suffix of
     attempt indices contains a scheduled attempt (fair-lossy link, BOLT 2
     §Message Retransmission).
2. **The eventual-delivery instance.**  `eventual_delivery_of_fair_attempts`
   proves that a packet which is (a) retransmitted forever, (b) scheduled
   fairly, and (c) delivered within a finite delay after `gst` has an actual
   delivery time at or after `gst`, with the explicit delay bound.  This is
   conditional by construction: `dropAll_not_eventually_delivered` and
   `dropAll_not_fair` mechanize the failure of the same claim under an unfair
   schedule, so no unconditional liveness is asserted.
3. **The eventual-inclusion instance.**  `RoundFair serve n` is a concrete
   adversarial block/commitment scheduler: the adversary chooses the order of
   the `n` pending slots in every round but must serve each slot once per
   round.  `eventual_inclusion_of_roundFair` proves every pending slot is
   served within the explicit finite window `2 * n`, and
   `roundFair_served_within_window` gives the bound.  `starveServe` shows the
   fairness premise is necessary: an adversary that always serves slot `0`
   starves slot `1` forever (`starvation_counterexample`).
4. **Non-vacuity witnesses.**  `roundRobin` and `reverseServe` are two
   genuinely different adversaries, both satisfying `RoundFair`; they are
   proved from scratch (`roundRobin_roundFair`, `reverseServe_roundFair`), and
   they first serve slot `0` at times `0` and `n - 1`
   (`fair_adversaries_differ`, `reverseServe_delays_slot_zero`).  A concrete
   three-slot vector is checked by `decide` (`reverseServe_three_round_zero`).
   `unitDelay` is a concrete schedule with `Causal` and `FiniteDelay 0 1`.
5. **Bridges to the existing tree.**  Every finite-delay adversary induces a
   `LnLean.Security.Schedule` satisfying `PartiallySynchronous`
   (`toSecurity_partiallySynchronous`), i.e. the `INV-10` predicate is
   inhabited by a concrete non-trivial schedule.  `lockinAt k` is an explicit
   finite-delay channel event schedule for which `LnLean.Proofs.Liveness.NoLoss`
   and `Fair` are *proved*, so the existing lock-in liveness theorem
   `fair_awaitingLockin_eventually_normal` fires on a concrete channel
   (`witnessChannel_eventually_normal`).  Finally `addHtlc?_some_mem` records
   that the "pending slot" of the inclusion model is populated only by an
   admitted HTLC from `LnLean.Proofs.Payment`.

## What is NOT claimed

* **No unconditional liveness.**  Every temporal conclusion carries
  `FiniteDelay`, `FairAttempts`, or `RoundFair` as an explicit hypothesis.
  The negations above show those hypotheses cannot be dropped.
* **No probabilistic or game-theoretic security claim.**  `SEC-01`'s
  `Game`/`AdvantageReduction` interface is untouched; this module only makes
  the schedule/adversary *side* of that interface concrete.  There is no
  negligibility, no complexity bound, and no corruption model here.
* **No concrete network, chain, or mempool.**  `deliverAt` is arbitrary data;
  `RoundFair` is a scheduling constraint on a `Nat → Nat` server, not a block
  template, fee market, or consensus rule.  The `2 * n` window is a
  scheduling bound, not a confirmation bound.
* **No message-to-`ProtocolEvent` mapping.**  As in `LnLean.Proofs.Liveness`,
  the wire vocabulary and the channel-event vocabulary stay separate; the
  `lockinAt` bridge supplies the event schedule directly.
* `LnLean.Security.Invariants`'s `PartiallySynchronous` is a predicate on an
  arbitrary latency function; satisfying it here is a satisfiability witness,
  not a proof that a real network is partially synchronous.
* The inclusion model assumes the served slot is not evicted between its
  admission and its service; eviction/replacement is out of scope.

## BOLT / implementation anchors

* BOLT 2 §"Message Retransmission"
  (`refs/bolts/02-peer-protocol.md:3352-3635`): the retransmission obligation
  modelled by `FairAttempts`.
* BOLT 2 §"Adding an HTLC" (`refs/bolts/02-peer-protocol.md:2829-2852`):
  admission is checked before an HTLC enters the pending set
  (`addHtlc?_some_mem`).
* BOLT 1 §"Lightning Message Format": transport delivery is asynchronous and
  unordered (the `AdvSchedule`/`Packet` model).
* `rust-lightning` at `fe49009`: `lightning/src/ln/channelmanager.rs:17831`
  (`handle_channel_reestablish`, retransmission under an adversarial schedule)
  and `:9540` (`timer_tick_occurred`, the periodic driver that makes
  retransmission attempts unbounded).  These are the same anchors used by
  `LnLean.Proofs.Liveness`; no new implementation claim is made.
-/

import LnLean.Proofs.Liveness
import LnLean.Security.Invariants
import LnLean.Proofs.Payment.LiquidityProps

namespace LnLean.Proofs.WaveH.H43

set_option autoImplicit false

open LnLean
open LnLean.Channel

/-! ## 1. The adversarial delivery model -/

/-- One message handed to the adversary.  `tag` identifies it (for example a
`channel_ready` or a `commitment_signed` instance); `sendTime` is the tick at
which the honest sender first hands it to the link. -/
structure Packet where
  tag : Nat
  sendTime : Nat
deriving Repr, DecidableEq, BEq

/-- The adversary's scheduling choices for every packet.  `deliverAt p = none`
means the packet is never delivered; `attemptTime p k` is the tick of the
`k`-th retransmission attempt and `attemptScheduled p k` says whether the
adversary actually lets that attempt through. -/
structure AdvSchedule where
  deliverAt : Packet → Option Nat
  attemptTime : Packet → Nat → Nat
  attemptScheduled : Packet → Nat → Bool

/-- **Causality.**  No packet is delivered before it is sent. -/
def Causal (s : AdvSchedule) : Prop :=
  ∀ p d, s.deliverAt p = some d → p.sendTime ≤ d

/-- A packet is delivered by time `t`. -/
def DeliveredBy (s : AdvSchedule) (p : Packet) (t : Nat) : Prop :=
  ∃ d, s.deliverAt p = some d ∧ d ≤ t

/-- A packet is delivered at some time. -/
def EventuallyDelivered (s : AdvSchedule) (p : Packet) : Prop :=
  ∃ d, s.deliverAt p = some d

/-- **Partial synchrony after `gst`.**  Every packet sent at or after the
global stabilisation time is delivered within `delta` of its send time.  This
is the explicit finite-delay premise of `docs/ASSUMPTIONS.md` §3; it is never
an axiom. -/
def FiniteDelay (s : AdvSchedule) (gst delta : Nat) : Prop :=
  ∀ p, gst ≤ p.sendTime →
    ∃ d, s.deliverAt p = some d ∧ p.sendTime ≤ d ∧ d ≤ p.sendTime + delta

/-- **Fair-lossy link.**  After any attempt index there is a later scheduled
attempt: the adversary may drop individual attempts but not all future ones.
This is the fairness premise corresponding to the BOLT 2 retransmission
obligation. -/
def FairAttempts (s : AdvSchedule) (p : Packet) : Prop :=
  ∀ K, ∃ k, K ≤ k ∧ s.attemptScheduled p k = true

/-- The honest sender keeps retransmitting for unboundedly long. -/
def AttemptTimesUnbounded (s : AdvSchedule) (p : Packet) : Prop :=
  ∀ B, ∃ k, B ≤ s.attemptTime p k

/-- Monotone attempt times: attempt `k + 1` is not earlier than attempt `k`. -/
def AttemptTimesMonotone (s : AdvSchedule) (p : Packet) : Prop :=
  ∀ k, s.attemptTime p k ≤ s.attemptTime p (k + 1)

/-! ### 1.1 Monotonicity and the eventual-delivery instance -/

/-- A monotone sequence of naturals stays above its starting point. -/
theorem nat_mono_le {f : Nat → Nat} (hf : ∀ k, f k ≤ f (k + 1)) :
    ∀ {a b : Nat}, a ≤ b → f a ≤ f b := by
  intro a b hab
  induction b with
  | zero =>
      have haz : a = 0 := Nat.eq_zero_of_le_zero hab
      subst haz
      exact Nat.le_refl (f 0)
  | succ n ih =>
      by_cases han : a = n + 1
      · subst han
        exact Nat.le_refl (f (n + 1))
      · have han' : a ≤ n := by omega
        exact Nat.le_trans (ih han') (hf n)

/-- **The eventual-delivery instance.**  Suppose the packet is retransmitted
with unbounded attempt times, no suffix of attempts is lost, and every
scheduled attempt at or after `gst` is delivered within `delta`.  Then there is
a scheduled post-`gst` attempt `k` whose delivery is an actual delivery,
bounded by `attemptTime p k + delta`.

Both fairness premises (`AttemptTimesUnbounded`, `FairAttempts`) are used:
unboundedness pushes an attempt past `gst`, fairness supplies a scheduled
attempt after it, and monotonicity keeps that attempt past `gst`. -/
theorem eventual_delivery_of_fair_attempts
    (s : AdvSchedule) (p : Packet) (gst delta : Nat)
    (hmono : AttemptTimesMonotone s p)
    (hunbounded : AttemptTimesUnbounded s p)
    (hfair : FairAttempts s p)
    (hdelay : ∀ k, s.attemptScheduled p k = true →
      gst ≤ s.attemptTime p k →
      ∃ d, s.deliverAt p = some d ∧ s.attemptTime p k ≤ d ∧
        d ≤ s.attemptTime p k + delta) :
    ∃ k d, gst ≤ s.attemptTime p k ∧ s.attemptScheduled p k = true ∧
      s.deliverAt p = some d ∧ s.attemptTime p k ≤ d ∧
      d ≤ s.attemptTime p k + delta := by
  obtain ⟨k₀, hk₀⟩ := hunbounded gst
  obtain ⟨k, hkge, hksched⟩ := hfair k₀
  have hk_at : gst ≤ s.attemptTime p k :=
    Nat.le_trans hk₀ (nat_mono_le hmono hkge)
  obtain ⟨d, hd, hdle, hdub⟩ := hdelay k hksched hk_at
  exact ⟨k, d, hk_at, hksched, hd, hdle, hdub⟩

/-- The `EventuallyDelivered` corollary of the instance above. -/
theorem eventually_delivered_of_fair_attempts
    (s : AdvSchedule) (p : Packet) (gst delta : Nat)
    (hmono : AttemptTimesMonotone s p)
    (hunbounded : AttemptTimesUnbounded s p)
    (hfair : FairAttempts s p)
    (hdelay : ∀ k, s.attemptScheduled p k = true →
      gst ≤ s.attemptTime p k →
      ∃ d, s.deliverAt p = some d ∧ s.attemptTime p k ≤ d ∧
        d ≤ s.attemptTime p k + delta) :
    EventuallyDelivered s p := by
  obtain ⟨_k, d, _hgst, _hsched, hd, _hdle, _hdub⟩ :=
    eventual_delivery_of_fair_attempts s p gst delta hmono hunbounded hfair hdelay
  exact ⟨d, hd⟩

/-! ### 1.2 The negations: fairness cannot be dropped -/

/-- The adversary that never delivers anything and never schedules an attempt.
This is a legal `AdvSchedule` (the model is a set of capabilities), which is
why `FairAttempts` must be a hypothesis. -/
def dropAll : AdvSchedule where
  deliverAt := fun _ => none
  attemptTime := fun _ k => k
  attemptScheduled := fun _ _ => false

/-- **No unconditional delivery.**  Under `dropAll` no packet is ever
delivered. -/
theorem dropAll_not_eventually_delivered (p : Packet) :
    ¬ EventuallyDelivered dropAll p := by
  rintro ⟨d, hd⟩
  simp [dropAll] at hd

/-- `dropAll` also violates the fair-lossy-link premise, so the failure is
exactly the missing fairness, not a modelling artefact. -/
theorem dropAll_not_fair (p : Packet) : ¬ FairAttempts dropAll p := by
  intro h
  obtain ⟨k, _hk, hk⟩ := h 0
  simp [dropAll] at hk

/-! ### 1.3 A concrete non-vacuous schedule -/

/-- A unit-delay network: every packet is delivered one tick after it is sent
and every attempt is scheduled.  It satisfies causality and `FiniteDelay 0 1`. -/
def unitDelay : AdvSchedule where
  deliverAt := fun p => some (p.sendTime + 1)
  attemptTime := fun _ k => k
  attemptScheduled := fun _ _ => true

theorem unitDelay_causal : Causal unitDelay := by
  intro p d hd
  simp [unitDelay] at hd
  omega

theorem unitDelay_finiteDelay (gst : Nat) : FiniteDelay unitDelay gst 1 := by
  intro p _hp
  exact ⟨p.sendTime + 1, rfl, Nat.le_succ p.sendTime, Nat.le_refl _⟩

theorem unitDelay_attempt_monotone (p : Packet) :
    AttemptTimesMonotone unitDelay p := by
  intro k
  simp [unitDelay]

theorem unitDelay_attempts_unbounded (p : Packet) :
    AttemptTimesUnbounded unitDelay p := by
  intro B
  exact ⟨B, by simp [unitDelay]⟩

theorem unitDelay_fair_attempts (p : Packet) : FairAttempts unitDelay p := by
  intro K
  exact ⟨K, Nat.le_refl K, rfl⟩

theorem unitDelay_delivers (p : Packet) :
    DeliveredBy unitDelay p (p.sendTime + 1) :=
  ⟨p.sendTime + 1, rfl, Nat.le_refl _⟩

theorem unitDelay_eventually_delivered (p : Packet) :
    EventuallyDelivered unitDelay p :=
  ⟨p.sendTime + 1, rfl⟩

/-- The unit-delay schedule admits the delivery step with an explicit bound:
attempt `sendTime` succeeds and its delivery is at most one tick later. -/
theorem unitDelay_instance (p : Packet) :
    ∃ k d, unitDelay.attemptScheduled p k = true ∧
      unitDelay.deliverAt p = some d ∧
      unitDelay.attemptTime p k ≤ d ∧
      d ≤ unitDelay.attemptTime p k + 1 :=
  ⟨p.sendTime, p.sendTime + 1, rfl, rfl,
    by simp [unitDelay], by simp [unitDelay]⟩

/-! ## 2. An adversarial round scheduler and eventual inclusion

The second instance is the *inclusion* side: `n` pending slots (each slot is
one admitted HTLC or one pending commitment update) and an adversary that
chooses the service order inside every round.  It may reorder arbitrarily but
must serve every slot once per round.  This is a concrete, checkable fairness
model: weak enough to allow genuine adversarial reordering, strong enough to
bound starvation. -/

/-- Slot `i` is served by time `T`. -/
def IncludedBy (serve : Nat → Nat) (i T : Nat) : Prop :=
  ∃ t, t ≤ T ∧ serve t = i

/-- **Round fairness.**  In every round `r` (ticks `[r*n, r*n + n)`) the
adversary serves every slot `i < n` at least once.  The order inside a round is
entirely the adversary's choice. -/
def RoundFair (serve : Nat → Nat) (n : Nat) : Prop :=
  ∀ r i, i < n → ∃ k, k < n ∧ serve (r * n + k) = i

/-- Every slot appears in every round. -/
theorem roundFair_served_in_round {serve : Nat → Nat} {n : Nat}
    (h : RoundFair serve n) {i : Nat} (hi : i < n) (r : Nat) :
    ∃ t, r * n ≤ t ∧ t < r * n + n ∧ serve t = i := by
  obtain ⟨k, hk, hsk⟩ := h r i hi
  exact ⟨r * n + k, by omega, by omega, hsk⟩

/-- **Eventual inclusion.**  Every slot `i < n` is served at some finite
time. -/
theorem roundFair_eventually_included {serve : Nat → Nat} {n : Nat}
    (h : RoundFair serve n) {i : Nat} (hi : i < n) :
    ∃ t, serve t = i := by
  obtain ⟨k, _hk, hsk⟩ := h 0 i hi
  exact ⟨0 * n + k, by simpa using hsk⟩

/-- The first round serves every slot within its `n` ticks. -/
theorem roundFair_first_round {serve : Nat → Nat} {n : Nat}
    (h : RoundFair serve n) {i : Nat} (hi : i < n) :
    IncludedBy serve i (n - 1) := by
  obtain ⟨k, hk, hsk⟩ := h 0 i hi
  refine ⟨k, by omega, ?_⟩
  simpa using hsk

/-- **Finite-delay window.**  Whatever the adversary does inside rounds, every
slot `i < n` is served inside *any* window of length `2 * n` starting at `t₀`.
The slack over `n` accounts for the arbitrary alignment of the window with the
round boundary. -/
theorem roundFair_served_within_window {serve : Nat → Nat} {n : Nat}
    (hn : 0 < n) (h : RoundFair serve n) {i : Nat} (hi : i < n)
    (t₀ : Nat) :
    ∃ s, t₀ ≤ s ∧ s < t₀ + 2 * n ∧ serve s = i := by
  obtain ⟨k, hk, hsk⟩ := h (t₀ / n + 1) i hi
  refine ⟨(t₀ / n + 1) * n + k, ?_, ?_, hsk⟩
  · have hdiv : n * (t₀ / n) + t₀ % n = t₀ := Nat.div_add_mod t₀ n
    have hmod : t₀ % n < n := Nat.mod_lt t₀ hn
    have hexp : (t₀ / n + 1) * n = (t₀ / n) * n + n := by
      rw [Nat.add_mul, Nat.one_mul]
    rw [Nat.mul_comm n (t₀ / n)] at hdiv
    omega
  · have hle := Nat.div_mul_le_self t₀ n
    have hexp : (t₀ / n + 1) * n = (t₀ / n) * n + n := by
      rw [Nat.add_mul, Nat.one_mul]
    omega

/-- **The eventual-inclusion instance.**  If slot `i < n` is pending from time
`t₀` and is not evicted before it is served, then it is included by an explicit
time `T` with `t₀ ≤ T` and `T ≤ t₀ + 2 * n`. -/
theorem eventual_inclusion_of_roundFair {serve : Nat → Nat} {n : Nat}
    (hn : 0 < n) (h : RoundFair serve n) {i : Nat} (hi : i < n)
    (t₀ : Nat) :
    ∃ T, t₀ ≤ T ∧ T ≤ t₀ + 2 * n ∧ IncludedBy serve i T := by
  obtain ⟨s, hle, hlt, hserve⟩ := roundFair_served_within_window hn h hi t₀
  exact ⟨s, hle, Nat.le_of_lt hlt, ⟨s, Nat.le_refl s, hserve⟩⟩

/-- Inclusion is monotone in the deadline. -/
theorem includedBy_mono {serve : Nat → Nat} {i T T' : Nat}
    (h : IncludedBy serve i T) (hle : T ≤ T') : IncludedBy serve i T' := by
  obtain ⟨t, ht, hst⟩ := h
  exact ⟨t, Nat.le_trans ht hle, hst⟩

/-! ### 2.1 The fairness premise is necessary: a starving adversary -/

/-- The adversary that always serves slot `0`. -/
def starveServe : Nat → Nat := fun _ => 0

/-- It is not round-fair for any `n ≥ 2`. -/
theorem starveServe_not_roundFair {n : Nat} (hn : 2 ≤ n) :
    ¬ RoundFair starveServe n := by
  intro h
  obtain ⟨k, _hk, hk⟩ := h 0 1 (by omega)
  simp [starveServe] at hk

/-- It never serves slot `1`, at any deadline. -/
theorem starveServe_never_serves_one (T : Nat) :
    ¬ IncludedBy starveServe 1 T := by
  rintro ⟨t, _ht, ht⟩
  simp [starveServe] at ht

/-- Hence the `RoundFair` premise of `eventual_inclusion_of_roundFair` cannot
be removed: an adversary exists that starves a pending slot forever. -/
theorem starvation_counterexample (n : Nat) (hn : 2 ≤ n) :
    ∃ serve : Nat → Nat,
      (∀ T, ¬ IncludedBy serve 1 T) ∧ ¬ RoundFair serve n :=
  ⟨starveServe, starveServe_never_serves_one, starveServe_not_roundFair hn⟩

/-! ### 2.2 Two genuinely different fair adversaries -/

/-- Round-robin: serve slot `t % n` at tick `t`. -/
def roundRobin (n : Nat) : Nat → Nat := fun t => t % n

/-- Reverse round-robin: serve slot `n - 1 - (t % n)` at tick `t`, i.e. the
reverse order in every round. -/
def reverseServe (n : Nat) : Nat → Nat := fun t => n - 1 - t % n

/-- Every round-robin schedule is round-fair. -/
theorem roundRobin_roundFair {n : Nat} (_hn : 0 < n) :
    RoundFair (roundRobin n) n := by
  intro r i hi
  refine ⟨i, hi, ?_⟩
  unfold roundRobin
  have hcomm : r * n + i = i + r * n := Nat.add_comm _ _
  rw [hcomm, Nat.mul_comm r n, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi]

/-- Every reverse round-robin schedule is round-fair: the adversary's choice
of order inside a round does not break the fairness constraint. -/
theorem reverseServe_roundFair {n : Nat} (_hn : 0 < n) :
    RoundFair (reverseServe n) n := by
  intro r i hi
  refine ⟨n - 1 - i, by omega, ?_⟩
  unfold reverseServe
  have hcomm : r * n + (n - 1 - i) = (n - 1 - i) + r * n := Nat.add_comm _ _
  rw [hcomm, Nat.mul_comm r n, Nat.add_mul_mod_self_left]
  have hlt : n - 1 - i < n := by omega
  rw [Nat.mod_eq_of_lt hlt]
  omega

/-- In the reverse schedule, slot `0` is served last in the first round. -/
theorem reverseServe_zero_at_last_slot {n : Nat} (hn : 0 < n) :
    reverseServe n (n - 1) = 0 := by
  unfold reverseServe
  have hlt : n - 1 < n := by omega
  rw [Nat.mod_eq_of_lt hlt]
  omega

/-- The two fair adversaries differ observably: at tick `0` round-robin serves
slot `0`, while the reverse schedule serves slot `n - 1`.  Both are accepted by
`RoundFair`, so the model genuinely admits adversarial reordering. -/
theorem fair_adversaries_differ {n : Nat} (hn : 2 ≤ n) :
    roundRobin n 0 = 0 ∧ reverseServe n 0 = n - 1 := by
  constructor
  · simp [roundRobin]
  · unfold reverseServe
    rw [Nat.zero_mod]
    omega

/-- Because of that reordering, the first inclusion time of slot `0` is `0`
under round-robin and `n - 1` under the reverse schedule. -/
theorem reverseServe_delays_slot_zero {n : Nat} (hn : 0 < n) :
    IncludedBy (roundRobin n) 0 0 ∧ IncludedBy (reverseServe n) 0 (n - 1) := by
  constructor
  · exact ⟨0, Nat.le_refl 0, by simp [roundRobin]⟩
  · exact ⟨n - 1, Nat.le_refl _, reverseServe_zero_at_last_slot hn⟩

/-- A concrete three-slot vector: the reverse adversary serves `2, 1, 0`. -/
theorem reverseServe_three_round_zero :
    [reverseServe 3 0, reverseServe 3 1, reverseServe 3 2] = [2, 1, 0] := by
  decide

/-- The same vector for round-robin. -/
theorem roundRobin_three_round_zero :
    [roundRobin 3 0, roundRobin 3 1, roundRobin 3 2] = [0, 1, 2] := by
  decide

/-- Both three-slot schedules satisfy the fairness model. -/
theorem three_slot_fair_adversaries :
    RoundFair (roundRobin 3) 3 ∧ RoundFair (reverseServe 3) 3 :=
  ⟨roundRobin_roundFair (by decide), reverseServe_roundFair (by decide)⟩

/-- The reverse adversary delays slot `0` to tick `2` but still includes it
within the `2 * 3 = 6` window.  This is the concrete non-vacuity witness for
the inclusion bound. -/
theorem three_slot_inclusion_witness :
    IncludedBy (reverseServe 3) 0 2 ∧
      IncludedBy (reverseServe 3) 0 (0 + 2 * 3) := by
  constructor
  · exact ⟨2, Nat.le_refl 2, by decide⟩
  · exact ⟨2, by decide, by decide⟩

/-! ## 3. Bridges to the existing tree -/

/-! ### 3.1 `INV-10`: a finite-delay adversary is partially synchronous -/

/-- Map an adversarial `AdvSchedule` onto the `LnLean.Security` schedule
vocabulary: the latency of message `m` is the delivery time of the packet with
the same tag and send time. -/
def AdvSchedule.toSecuritySchedule (s : AdvSchedule) :
    LnLean.Security.Schedule :=
  { latency := fun m => s.deliverAt { tag := m.tag, sendTime := m.send } }

/-- **`INV-10` is inhabited by a non-trivial schedule.**  The finite-delay
premise of the delivery model implies the `PartiallySynchronous` predicate
used by `LnLean.Security.Invariants`. -/
theorem toSecurity_partiallySynchronous (s : AdvSchedule) (gst delta : Nat)
    (h : FiniteDelay s gst delta) :
    LnLean.Security.PartiallySynchronous gst delta s.toSecuritySchedule := by
  intro m hm
  obtain ⟨d, hd, _hge, hdle⟩ := h { tag := m.tag, sendTime := m.send } hm
  exact ⟨d, hd, hdle⟩

/-- The unit-delay network is partially synchronous with `gst = 0`,
`delta = 1`. -/
theorem unitDelay_partiallySynchronous :
    LnLean.Security.PartiallySynchronous 0 1 unitDelay.toSecuritySchedule :=
  toSecurity_partiallySynchronous unitDelay 0 1 (unitDelay_finiteDelay 0)

/-- The same statement at the `INV-10` predicate: the invariant is
non-vacuously satisfiable. -/
theorem invPartialSynchrony_nonvacuous :
    LnLean.Security.invPartialSynchrony.predicate := by
  intro gst delta s hps m hm
  exact hps m hm

/-! ### 3.2 Lock-in under an explicit finite-delay event schedule -/

/-- The `k`-delayed lock-in schedule: `k` legal no-op `funding_signed` events
while awaiting lock-in, then `funding_locked` (`channel_ready`), then
`commitment_signed` rounds.  The delay `k` is chosen by the adversary. -/
def lockinAt (k : Nat) : Liveness.Scheduler :=
  fun n =>
    if n < k then ProtocolEvent.fundingSigned
    else if n = k then ProtocolEvent.fundingLocked
    else ProtocolEvent.commitmentSigned

/-- The phase reached by `lockinAt k` after `n` ticks: `awaitingLockin` up to
and including tick `k`, `normal` afterwards.  This invariant is what makes the
loss-free proof finite. -/
theorem lockinAt_run (c : Channel) (k : Nat)
    (hphase : c.phase = ChannelPhase.awaitingLockin) :
    ∀ n, ∃ cn, Liveness.runPrefix c (lockinAt k) n = some cn ∧
      cn.phase = (if n ≤ k then ChannelPhase.awaitingLockin
                  else ChannelPhase.normal) := by
  intro n
  induction n with
  | zero =>
      refine ⟨c, Liveness.runPrefix_zero c (lockinAt k), ?_⟩
      simp [hphase]
  | succ n ih =>
      obtain ⟨cn, hrun, hph⟩ := ih
      by_cases hlt : n < k
      · -- before lock-in: `funding_signed` keeps `awaitingLockin`
        have hle : n ≤ k := Nat.le_of_lt hlt
        have hcn : cn.phase = ChannelPhase.awaitingLockin := by
          simpa [hle] using hph
        have hσ : lockinAt k n = ProtocolEvent.fundingSigned := by
          simp [lockinAt, hlt]
        have hstep : Liveness.step? cn (lockinAt k n) = some cn := by
          rw [hσ]
          exact Liveness.step?_complete (Step.fundingSigned cn hcn)
        refine ⟨cn, ?_, ?_⟩
        · rw [Liveness.runPrefix_succ, hrun]
          simpa only [Option.bind_some] using hstep
        · have hle' : n + 1 ≤ k := hlt
          simp [hle', hcn]
      · by_cases heq : n = k
        · -- at tick `k`: `funding_locked` enters `normal`
          subst heq
          have hcn : cn.phase = ChannelPhase.awaitingLockin := by
            simpa using hph
          have hσ : lockinAt n n = ProtocolEvent.fundingLocked := by
            simp [lockinAt]
          have hstep : Liveness.step? cn (lockinAt n n) =
              some { cn with phase := ChannelPhase.normal } := by
            rw [hσ]
            exact Liveness.step?_complete (Step.fundingLocked cn hcn)
          refine ⟨{ cn with phase := ChannelPhase.normal }, ?_, ?_⟩
          · rw [Liveness.runPrefix_succ, hrun]
            simpa only [Option.bind_some] using hstep
          · have hnot : ¬ n + 1 ≤ n := by omega
            simp [hnot]
        · -- after lock-in: `commitment_signed` stays in `normal`
          have hkn : k < n :=
            Nat.lt_of_le_of_ne (Nat.le_of_not_lt hlt) (fun h => heq h.symm)
          have hnle : ¬ n ≤ k := Nat.not_le.mpr hkn
          have hcn : cn.phase = ChannelPhase.normal := by
            simpa [hnle] using hph
          have hσ : lockinAt k n = ProtocolEvent.commitmentSigned := by
            simp [lockinAt, hlt, heq]
          have hstep : Liveness.step? cn (lockinAt k n) =
              some { cn with
                remoteCommitmentNumber := cn.remoteCommitmentNumber + 1 } := by
            rw [hσ]
            exact Liveness.step?_complete (Step.commitmentSigned cn hcn)
          refine ⟨{ cn with
            remoteCommitmentNumber := cn.remoteCommitmentNumber + 1 }, ?_, ?_⟩
          · rw [Liveness.runPrefix_succ, hrun]
            simpa only [Option.bind_some] using hstep
          · have hnot : ¬ n + 1 ≤ k := by omega
            simp [hcn, hnot]

/-- **The explicit schedule is loss-free.**  Every prefix of `lockinAt k` is
executable from a channel awaiting lock-in. -/
theorem lockinAt_noLoss (c : Channel) (k : Nat)
    (hphase : c.phase = ChannelPhase.awaitingLockin) :
    Liveness.NoLoss c (lockinAt k) := by
  intro n
  exact (lockinAt_run c k hphase n).imp (fun _ h => h.1)

/-- The schedule eventually runs the lock-in event at the adversary's chosen
finite delay `k`. -/
theorem lockinAt_fair (k : Nat) :
    Liveness.Fair (lockinAt k) ProtocolEvent.fundingLocked := by
  refine ⟨k, ?_⟩
  simp [lockinAt]

/-- The unfair schedule that runs only `funding_signed` never runs the lock-in
event. -/
theorem fundingSigned_only_not_fair :
    ¬ Liveness.Fair (fun _ => ProtocolEvent.fundingSigned)
        ProtocolEvent.fundingLocked := by
  rintro ⟨n, hn⟩
  simp at hn

/-! ### 3.3 A concrete channel and the lock-in instance -/

/-- One endpoint of the witness channel.  Only the fields needed by the
lifecycle relation are populated; keys and parameters are placeholders. -/
def witnessEndpoint : Endpoint where
  nodeId := ⟨ByteArray.empty⟩
  fundingPubKey := ⟨ByteArray.empty⟩
  paymentBasepoint := ⟨ByteArray.empty⟩
  delayedPaymentBasepoint := ⟨ByteArray.empty⟩
  params :=
    { dustLimitSat := 546
      channelReserveSat := 1000
      toSelfDelay := 144
      maxHtlcValue := ⟨1000000000⟩
      htlcMinimum := ⟨0⟩
      feerate := ⟨253⟩
      anchorOutputs := false }

/-- A concrete channel awaiting lock-in with empty balance and no HTLCs. -/
def witnessChannel : Channel where
  channelId := ⟨ByteArray.empty⟩
  funding := ⟨ByteArray.empty, 0⟩
  fundingValue := ⟨100000000⟩
  localEndpoint := witnessEndpoint
  remoteEndpoint := witnessEndpoint
  phase := ChannelPhase.awaitingLockin
  localCommitmentNumber := 0
  remoteCommitmentNumber := 0
  balance := ⟨⟨50000000⟩, ⟨50000000⟩⟩
  htlcs := []

theorem witnessChannel_phase :
    witnessChannel.phase = ChannelPhase.awaitingLockin := rfl

theorem witnessChannel_noLoss (k : Nat) :
    Liveness.NoLoss witnessChannel (lockinAt k) :=
  lockinAt_noLoss witnessChannel k rfl

/-- **The lock-in liveness theorem fires on the concrete channel.**  The
fairness and no-loss premises are proved, not assumed. -/
theorem witnessChannel_eventually_normal (k : Nat) :
    Liveness.Eventually witnessChannel (lockinAt k)
      (fun c => c.phase = ChannelPhase.normal) :=
  Liveness.fair_awaitingLockin_eventually_normal witnessChannel (lockinAt k)
    rfl (witnessChannel_noLoss k) (lockinAt_fair k)

/-- With the adversary's delay fixed at `k = 2`, lock-in happens exactly at
tick `3`.  This pins the instance to concrete numbers. -/
theorem witnessChannel_lockin_at_three :
    ∃ c', Liveness.runPrefix witnessChannel (lockinAt 2) 3 = some c' ∧
      c'.phase = ChannelPhase.normal := by
  obtain ⟨c', hrun, hph⟩ := lockinAt_run witnessChannel 2 rfl 3
  refine ⟨c', hrun, ?_⟩
  have hnot : ¬ 3 ≤ 2 := by omega
  simpa [hnot] using hph

/-! ### 3.4 Admission before inclusion -/

/-- An accepted HTLC is exactly one element of the pending-HTLC list, so the
"pending slots" of the inclusion model are populated only through
`LnLean.Proofs.Payment.addHtlc?`. -/
theorem addHtlc?_some_mem {c c' : Channel} {h : HTLC}
    (hs : LnLean.Proofs.Payment.addHtlc? c h = some c') : h ∈ c'.htlcs := by
  rw [LnLean.Proofs.Payment.addHtlc?_some_shape hs]
  simp

/-- **Admission plus eventual inclusion.**  An admitted HTLC is in the
commitment queue, and a round-fair adversary serves its slot within the
explicit `2 * n` window. -/
theorem admitted_payment_eventually_included
    {c c' : Channel} {h : HTLC}
    (hs : LnLean.Proofs.Payment.addHtlc? c h = some c')
    {serve : Nat → Nat} {n : Nat} (hn : 0 < n) (hfair : RoundFair serve n)
    {i : Nat} (hi : i < n) (t₀ : Nat) :
    h ∈ c'.htlcs ∧ ∃ T, t₀ ≤ T ∧ T ≤ t₀ + 2 * n ∧ IncludedBy serve i T :=
  ⟨addHtlc?_some_mem hs, eventual_inclusion_of_roundFair hn hfair hi t₀⟩

/-! ## 4. Axiom audit -/

#print axioms eventual_delivery_of_fair_attempts
#print axioms eventual_inclusion_of_roundFair
#print axioms starvation_counterexample
#print axioms three_slot_fair_adversaries
#print axioms toSecurity_partiallySynchronous
#print axioms witnessChannel_eventually_normal
#print axioms addHtlc?_some_mem

end LnLean.Proofs.WaveH.H43
