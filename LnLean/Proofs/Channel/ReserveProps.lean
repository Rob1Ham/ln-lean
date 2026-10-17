import LnLean.Channel.Fee
import LnLean.Channel.State
import LnLean.Channel.Types

/-!
# LnLean.Proofs.Channel.ReserveProps

English claim.  This module states the reserve and dust laws of a BOLT 2
channel against the wave-A model in `LnLean.Channel.{Types,State,Fee}`:

1. A channel reserve is a natural number, hence non-negative, and it is at
   most the channel capacity once the opening handshake has enforced that
   bound.  The bound is *not* unconditional: the counterexample
   `reserve_not_always_within_capacity` shows a `ChannelParams` with a
   reserve larger than the capacity, so the law is stated under the
   predicate `ReserveWithinCapacity`.
2. If both advertised reserves are met in a channel state, every legal
   `Step` preserves them; a modelled local balance drop (the arithmetic core
   of `update_add_htlc`) also preserves the local reserve when the amount is
   guarded by `reserve * 1000 + amount <= localBalance`.  The current `Step`
   relation never changes balances, so the operational update constructor is
   still an obligation (`LN-CH-101`); its unconditional ledger equation is
   false under truncated subtraction, with the corrected conditional form
   `committed_update_preserves_ledger_of_le` and a checked counterexample.
3. Commitment outputs are trimmed by the owner's dust limit: every kept
   output has value at least the limit and every dropped output is recorded
   explicitly in `dustDroppedOutputs` as dust.  Anchor outputs are fixed at
   330 satoshis and are not dust whenever the limit is at most 330.
4. The maximum HTLC value is at most the funding value and at least the HTLC
   minimum, under the handshake predicate `HtlcBoundsHold`.
5. The settled channel ledger conserves value: `local + remote + fee =
   funding`, and the same equation is preserved by every legal `Step`.
   Commitment-level conservation is stated with dust: kept outputs plus
   explicitly dropped dust plus the fee equals the funding value whenever the
   gross output sum plus the fee does.
6. A commitment whose holder output is below the holder's reserve is invalid:
   `CommitmentValid` includes `CommitmentReserveOk`, so a reserve violation
   contradicts validity.

BOLT sections.
* BOLT 2 §2 `open_channel` / `accept_channel` fields
  (`02-peer-protocol.md:680-760`, `:907-960`): `dust_limit_satoshis`,
  `channel_reserve_satoshis`, `max_htlc_value_in_flight_msat`,
  `htlc_minimum_msat`.  The reserve/dust ordering requirements are at
  `:811`, `:869-872`, `:950-959`; the reserve rationale is at `:884-896`.
* BOLT 2 §3 `update_add_htlc` reserve and exposure checks
  (`02-peer-protocol.md:2739-2750` is the dust-exposure discussion; the
  reserve requirement is quoted in the LDK check below).
* BOLT 3 §2 `Commitment Transaction` and `Trimmed Outputs`
  (`03-transactions.md:83-353`, especially `:307-354`) and §5 `Dust Limits`
  (`03-transactions.md:583-620`).

rust-lightning anchors at `fe4900930c6bd5786ec4203274d7cf312776a5a6`.
* `lightning/src/ln/channel.rs:4211-4217`: a peer's
  `channel_reserve_satoshis` must be no greater than the channel value.
* `lightning/src/ln/channel.rs:4223-4232`: the dust limit must be below the
  channel value and `htlc_minimum_msat` below the full channel value.
* `lightning/src/ln/channel.rs:4339-4360`: the local reserve must be at
  least the dust limit and strictly below the channel value.
* `lightning/src/ln/channel.rs:2697-2705` (`get_htlc_maximum_msat`): the
  per-HTLC maximum is
  `min((funding - counterparty_reserve - holder_reserve) * 1000,
       max_htlc_value_in_flight_msat)`.
* `lightning/src/ln/channel.rs:5880-5891`: an accepted remote HTLC must
  leave the counterparty above `holder_selected_channel_reserve_satoshis`.
* `lightning/src/ln/channel.rs:2484-2493` (`get_available_balances`) and
  `:6552` (`get_available_balances_for_scope`) are the reserve-aware balance
  accessors; the scaffold states the arithmetic, not the fee estimator.

What is NOT modelled.
* The full `update_add_htlc` / `update_fulfill_htlc` transition.  `Step` in
  `LnLean.Channel.State` changes only phase, commitment counters, and the
  feerate; it does not move value into `htlcs`.  Therefore statements about
  "any modelled update" are restricted to `Step`, and the balance-changing
  case is the explicit obligation `LN-CH-101`.  The unconditional ledger
  equation fails because `spendLocalBalance` truncates; the corrected form
  requires `amount.val <= localBalance.val` and is proved as
  `committed_update_preserves_ledger_of_le`.
* The net-of-second-stage-fee HTLC dust test.  BOLT 3 trims an HTLC when
  `amount - htlc_fee < dust_limit`; this module trims on the gross
  `amountSat` value, matching `LnLean.Channel.Fee.isDust`.  The proved
  counterexample `gross_dust_rule_insufficient` records the gap.
* Bitcoin Core relay policy, fee estimation, anchor child-pays-for-parent,
  and the exact second-stage HTLC weights/fees (BOLT 5, HTLC workstream).
* Wire validation of `channel_reserve_satoshis`, `dust_limit_satoshis`, and
  `max_htlc_value_in_flight_msat`; they are predicates here, not decoded
  fields.
-/

namespace LnLean.Proofs.Channel

set_option autoImplicit false

open LnLean
open LnLean.Channel

/-! ## 1. Reserve accounting -/

/-- The reserve the local endpoint must keep.  BOLT 2: the *peer* advertises
`channel_reserve_satoshis`, so from the local point of view the applicable
value is the remote endpoint's parameter. -/
def localReserveSat (c : Channel) : Nat :=
  c.remoteEndpoint.params.channelReserveSat

/-- The reserve the remote endpoint must keep, as advertised by the local
endpoint. -/
def remoteReserveSat (c : Channel) : Nat :=
  c.localEndpoint.params.channelReserveSat

/-- The opening handshake bound: each advertised reserve is at most the
channel capacity.  BOLT 2 enforces this at `open_channel`/`accept_channel`;
the model records it as a predicate because `ChannelParams` itself does not
carry the funding value. -/
def ReserveWithinCapacity (c : Channel) : Prop :=
  localReserveSat c ≤ c.fundingValueSat ∧
    remoteReserveSat c ≤ c.fundingValueSat

/-- Both parties' balances meet the reserve the other party advertised. -/
def ReserveInvariant (c : Channel) : Prop :=
  reserveSatisfied c.balance (localReserveSat c) ∧
    remoteReserveSat c ≤ c.balance.remoteSat

/-- The HTLC bounds checked at channel opening: `htlc_minimum_msat` is at
most `max_htlc_value_in_flight_msat`, and the latter is at most the channel
capacity. -/
def HtlcBoundsHold (p : ChannelParams) (capacity : Msat) : Prop :=
  p.htlcMinimum.val ≤ p.maxHtlcValue.val ∧
    p.maxHtlcValue.val ≤ capacity.val

/-- The channel is well formed when both endpoints' HTLC bounds hold against
the funding value. -/
def ChannelHtlcBounds (c : Channel) : Prop :=
  HtlcBoundsHold c.localEndpoint.params c.fundingValue ∧
    HtlcBoundsHold c.remoteEndpoint.params c.fundingValue

/-- A reserve is a natural number, so it is non-negative. -/
theorem reserve_nonneg (p : ChannelParams) : 0 ≤ p.channelReserveSat :=
  Nat.zero_le _

/-- Under the opening bound, the local reserve is non-negative and at most
the channel capacity. -/
theorem reserve_nonneg_and_within_capacity (c : Channel)
    (h : ReserveWithinCapacity c) :
    0 ≤ localReserveSat c ∧ localReserveSat c ≤ c.fundingValueSat :=
  ⟨Nat.zero_le _, h.1⟩

/-- The remote reserve satisfies the same bound under the same predicate. -/
theorem remoteReserve_within_capacity (c : Channel)
    (h : ReserveWithinCapacity c) :
    0 ≤ remoteReserveSat c ∧ remoteReserveSat c ≤ c.fundingValueSat :=
  ⟨Nat.zero_le _, h.2⟩

/-- The bound is *not* a theorem of `ChannelParams` alone: a reserve larger
than the capacity is representable.  BOLT 2 therefore has to reject it during
the opening handshake. -/
theorem reserve_not_always_within_capacity :
    ∃ (p : ChannelParams) (capacity : Nat), capacity < p.channelReserveSat := by
  refine ⟨{ dustLimitSat := 0
            channelReserveSat := 1000
            toSelfDelay := 0
            maxHtlcValue := ⟨0⟩
            htlcMinimum := ⟨0⟩
            feerate := ⟨0⟩
            anchorOutputs := false }, 0, ?_⟩
  decide

/-- Every legal `Step` preserves the opening reserve bound, because a step
changes neither the funding value nor any reserve parameter (the fee update
changes only `feerate`). -/
theorem step_preserves_reserveWithinCapacity {c c' : Channel}
    {e : ProtocolEvent} (h : Step c e c')
    (hc : ReserveWithinCapacity c) : ReserveWithinCapacity c' := by
  rcases hc with ⟨hl, hr⟩
  cases h <;>
    simpa [ReserveWithinCapacity, localReserveSat, remoteReserveSat,
      Channel.fundingValueSat] using And.intro hl hr

/-- Every legal `Step` preserves both reserve balances.  This is the exact
content of "a party's balance is at least its reserve after a modelled
update": `Step` leaves the balance untouched. -/
theorem step_preserves_reserveInvariant {c c' : Channel}
    {e : ProtocolEvent} (h : Step c e c')
    (hc : ReserveInvariant c) : ReserveInvariant c' := by
  rcases hc with ⟨hl, hr⟩
  cases h <;>
    simpa [ReserveInvariant, localReserveSat, remoteReserveSat,
      reserveSatisfied, Balance.localSat, Balance.remoteSat] using
      And.intro hl hr

/-! ## 2. A modelled balance drop (the arithmetic core of `update_add_htlc`) -/

/-- Drop `amountMsat` from the local balance.  This is the balance effect a
future `update_add_htlc` constructor would have; it is kept here as a named
operation so the reserve arithmetic is testable without pretending that
`State.Step` already models the message. -/
def spendLocalBalance (b : Balance) (amountMsat : Nat) : Balance :=
  { b with localBalance := ⟨b.localBalance.val - amountMsat⟩ }

/-- Drop `amountMsat` from the remote balance. -/
def spendRemoteBalance (b : Balance) (amountMsat : Nat) : Balance :=
  { b with remoteBalance := ⟨b.remoteBalance.val - amountMsat⟩ }

/-- Spending from the local balance preserves the local reserve whenever the
post-spend balance is still at least `reserve * 1000` msat. -/
theorem spendLocal_preserves_reserve {b : Balance} {reserve amountMsat : Nat}
    (h : reserve * Msat.MSAT_PER_SAT + amountMsat ≤ b.localBalance.val) :
    reserveSatisfied (spendLocalBalance b amountMsat) reserve := by
  have h' : reserve * 1000 + amountMsat ≤ b.localBalance.val := by
    simpa [Msat.MSAT_PER_SAT] using h
  show reserve ≤ (b.localBalance.val - amountMsat) / 1000
  rw [Nat.le_div_iff_mul_le (by decide : 0 < 1000)]
  exact Nat.le_sub_of_add_le' (by simpa [Nat.add_comm] using h')

/-- Symmetric statement for the remote balance. -/
theorem spendRemote_preserves_remoteReserve {b : Balance}
    {reserve amountMsat : Nat}
    (h : reserve * Msat.MSAT_PER_SAT + amountMsat ≤ b.remoteBalance.val) :
    reserve ≤ (spendRemoteBalance b amountMsat).remoteSat := by
  have h' : reserve * 1000 + amountMsat ≤ b.remoteBalance.val := by
    simpa [Msat.MSAT_PER_SAT] using h
  show reserve ≤ (b.remoteBalance.val - amountMsat) / 1000
  rw [Nat.le_div_iff_mul_le (by decide : 0 < 1000)]
  exact Nat.le_sub_of_add_le' (by simpa [Nat.add_comm] using h')

/-- If a balance drop is guarded by the reserve arithmetic, the channel's
`ReserveInvariant` survives.  The remote balance is untouched. -/
theorem balanceDrop_preserves_reserveInvariant {c c' : Channel}
    {amountMsat : Nat}
    (hdrop : c' = { c with
      balance := spendLocalBalance c.balance amountMsat })
    (hc : ReserveInvariant c)
    (h : localReserveSat c * Msat.MSAT_PER_SAT + amountMsat ≤
      c.balance.localBalance.val) :
    ReserveInvariant c' := by
  subst c'
  rcases hc with ⟨hl, hr⟩
  refine ⟨?_, ?_⟩
  · simpa [ReserveInvariant, localReserveSat] using
      (spendLocal_preserves_reserve (b := c.balance)
        (reserve := localReserveSat c) (amountMsat := amountMsat) h)
  · simpa [ReserveInvariant, remoteReserveSat, Balance.remoteSat,
      spendLocalBalance] using hr

/-! ## 3. HTLC bounds -/

/-- `htlc_minimum_msat` is at most `max_htlc_value_in_flight_msat`. -/
theorem htlcMinimum_le_maxHtlc {p : ChannelParams} {capacity : Msat}
    (h : HtlcBoundsHold p capacity) :
    p.htlcMinimum.val ≤ p.maxHtlcValue.val :=
  h.1

/-- `max_htlc_value_in_flight_msat` is at most the channel capacity. -/
theorem maxHtlc_le_capacity {p : ChannelParams} {capacity : Msat}
    (h : HtlcBoundsHold p capacity) :
    p.maxHtlcValue.val ≤ capacity.val :=
  h.2

/-- Both conclusions at once, for the local endpoint. -/
theorem local_htlc_bounds {c : Channel} (h : ChannelHtlcBounds c) :
    c.localEndpoint.params.htlcMinimum.val ≤
        c.localEndpoint.params.maxHtlcValue.val ∧
      c.localEndpoint.params.maxHtlcValue.val ≤ c.fundingValue.val :=
  h.1

/-- Both conclusions at once, for the remote endpoint. -/
theorem remote_htlc_bounds {c : Channel} (h : ChannelHtlcBounds c) :
    c.remoteEndpoint.params.htlcMinimum.val ≤
        c.remoteEndpoint.params.maxHtlcValue.val ∧
      c.remoteEndpoint.params.maxHtlcValue.val ≤ c.fundingValue.val :=
  h.2

/-- `Step` preserves the HTLC bounds: only `feerate` can change. -/
theorem step_preserves_channelHtlcBounds {c c' : Channel}
    {e : ProtocolEvent} (h : Step c e c')
    (hc : ChannelHtlcBounds c) : ChannelHtlcBounds c' := by
  rcases hc with ⟨hl, hr⟩
  cases h <;>
    simpa [ChannelHtlcBounds, HtlcBoundsHold] using And.intro hl hr

/-- The LDK `get_htlc_maximum_msat` bound: if the two reserves fit inside
the funding value, a per-HTLC maximum no larger than the remaining value is
also no larger than the funding value. -/
theorem maxHtlc_le_funding_of_ldk_bound {funding localReserve remoteReserve
    maxInflight : Nat}
    (hfit : localReserve + remoteReserve ≤ funding)
    (h : maxInflight ≤
      (funding - localReserve - remoteReserve) * Msat.MSAT_PER_SAT) :
    maxInflight ≤ funding * Msat.MSAT_PER_SAT := by
  have hsub : funding - localReserve - remoteReserve ≤ funding := by omega
  have hmul : (funding - localReserve - remoteReserve) * Msat.MSAT_PER_SAT ≤
      funding * Msat.MSAT_PER_SAT :=
    Nat.mul_le_mul_right _ hsub
  exact Nat.le_trans h hmul

/-! ## 4. Dust trimming -/

/-- The candidate outputs of a commitment before dust trimming: the two
non-HTLC outputs and one output per HTLC record.  Anchors are handled
separately because BOLT 3 adds them at a fixed 330 satoshis. -/
def candidateOutputs (k : Commitment) : List CommitmentOutput :=
  [CommitmentOutput.toLocal k.toLocalSat,
   CommitmentOutput.toRemote k.toRemoteSat] ++
    k.htlcs.map (fun h => CommitmentOutput.htlc h.direction h.amountSat)

/-- Keep one output when it is not below the dust limit. -/
def trimOutput (dust : Nat) (o : CommitmentOutput) : Option CommitmentOutput :=
  if o.value < dust then none else some o

/-- Record one output as dust when it is below the dust limit. -/
def dropOutput (dust : Nat) (o : CommitmentOutput) : Option CommitmentOutput :=
  if o.value < dust then some o else none

/-- The outputs that survive the owner's dust limit. -/
def dustTrimmedOutputs (dust : Nat) (k : Commitment) : List CommitmentOutput :=
  (candidateOutputs k).filterMap (trimOutput dust)

/-- The outputs that are explicitly recorded as dust and therefore not
created.  They become additional fee in BOLT 3. -/
def dustDroppedOutputs (dust : Nat) (k : Commitment) : List CommitmentOutput :=
  (candidateOutputs k).filterMap (dropOutput dust)

/-- The value of an output list. -/
def outputSum : List CommitmentOutput → Nat
  | [] => 0
  | o :: t => o.value + outputSum t

/-- The anchor portion of a commitment, in satoshis. -/
def anchorValueOf (k : Commitment) : Nat :=
  if k.anchorOutputs then 2 * anchorOutputSat else 0

/-- Membership in the kept list is exactly "candidate output and not below
the dust limit". -/
theorem mem_dustTrimmedOutputs {dust : Nat} {k : Commitment}
    {o : CommitmentOutput} :
    o ∈ dustTrimmedOutputs dust k ↔
      o ∈ candidateOutputs k ∧ ¬ o.value < dust := by
  unfold dustTrimmedOutputs
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨a, ha, ht⟩
    unfold trimOutput at ht
    split at ht
    · simp at ht
    · rename_i hge
      simp only [Option.some.injEq] at ht
      cases ht
      exact ⟨ha, hge⟩
  · rintro ⟨ha, hge⟩
    exact ⟨o, ha, by simp [trimOutput, hge]⟩

/-- Membership in the dropped list is exactly "candidate output and below
the dust limit": the model records dust rather than silently discarding it. -/
theorem mem_dustDroppedOutputs {dust : Nat} {k : Commitment}
    {o : CommitmentOutput} :
    o ∈ dustDroppedOutputs dust k ↔
      o ∈ candidateOutputs k ∧ o.value < dust := by
  unfold dustDroppedOutputs
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨a, ha, ht⟩
    unfold dropOutput at ht
    split at ht
    · rename_i hlt
      simp only [Option.some.injEq] at ht
      cases ht
      exact ⟨ha, hlt⟩
    · simp at ht
  · rintro ⟨ha, hlt⟩
    exact ⟨o, ha, by simp [dropOutput, hlt]⟩

/-- No kept output is below the dust limit. -/
theorem dustTrimmedOutputs_not_dust (dust : Nat) (k : Commitment) :
    ∀ o, o ∈ dustTrimmedOutputs dust k → ¬ isDust dust o.value := by
  intro o ho
  have h := (mem_dustTrimmedOutputs (dust := dust) (k := k) (o := o)).1 ho
  simpa [isDust] using h.2

/-- Every dropped output is explicitly dust. -/
theorem dustDroppedOutputs_are_dust (dust : Nat) (k : Commitment) :
    ∀ o, o ∈ dustDroppedOutputs dust k → isDust dust o.value := by
  intro o ho
  have h := (mem_dustDroppedOutputs (dust := dust) (k := k) (o := o)).1 ho
  simpa [isDust] using h.2

/-- Every candidate output is either kept or explicitly recorded as dust. -/
theorem candidateOutputs_kept_or_dropped (dust : Nat) (k : Commitment) :
    ∀ o, o ∈ candidateOutputs k →
      o ∈ dustTrimmedOutputs dust k ∨ o ∈ dustDroppedOutputs dust k := by
  intro o ho
  by_cases h : o.value < dust
  · right
    exact (mem_dustDroppedOutputs (dust := dust) (k := k) (o := o)).2
      ⟨ho, h⟩
  · left
    exact (mem_dustTrimmedOutputs (dust := dust) (k := k) (o := o)).2
      ⟨ho, h⟩

/-- An anchor output is not dust whenever the owner's limit is at most the
fixed 330-satoshi anchor value. -/
theorem anchorOutput_not_dust {dust : Nat} (h : dust ≤ anchorOutputSat) :
    ¬ isDust dust anchorOutputSat := by
  simp [isDust]
  omega

/-- Under `dust ≤ reserve ≤ toLocal`, the holder's `to_local` output is not
trimmed.  This links the reserve and dust laws: the reserve floor is above
the dust floor, so meeting the reserve also keeps the output economical. -/
theorem toLocal_kept_of_reserve {dust reserve : Nat} {k : Commitment}
    (hd : dust ≤ reserve) (hr : reserve ≤ k.toLocalSat) :
    CommitmentOutput.toLocal k.toLocalSat ∈ dustTrimmedOutputs dust k := by
  apply (mem_dustTrimmedOutputs (dust := dust) (k := k)
    (o := CommitmentOutput.toLocal k.toLocalSat)).2
  constructor
  · simp [candidateOutputs]
  · simp [CommitmentOutput.value]
    omega

/-- Kept plus explicitly dropped values are exactly the candidate values. -/
theorem outputSum_filterMap_trim_drop (dust : Nat) :
    ∀ l : List CommitmentOutput,
      outputSum (l.filterMap (trimOutput dust)) +
        outputSum (l.filterMap (dropOutput dust)) = outputSum l := by
  intro l
  induction l with
  | nil => rfl
  | cons o t ih =>
      by_cases h : o.value < dust
      · simp [List.filterMap, trimOutput, dropOutput, h, outputSum]
        omega
      · simp [List.filterMap, trimOutput, dropOutput, h, outputSum]
        omega

/-- Dust trimming conserves the total value when the explicitly dropped dust
is counted together with the kept outputs: nothing is created or destroyed,
it is only moved to the fee bucket. -/
theorem dust_trim_conservation (dust : Nat) (k : Commitment) :
    outputSum (dustTrimmedOutputs dust k) +
      outputSum (dustDroppedOutputs dust k) = outputSum (candidateOutputs k) := by
  unfold dustTrimmedOutputs dustDroppedOutputs
  exact outputSum_filterMap_trim_drop dust (candidateOutputs k)

/-- Commitment conservation after dust trimming.  If the gross output sum,
the anchors, and the fee equal the funding value, then the kept outputs plus
the explicitly recorded dust plus the anchors and fee still equal it. -/
theorem commitment_conservation_with_dust (dust : Nat) (k : Commitment)
    (h : outputSum (candidateOutputs k) + anchorValueOf k + k.feeSat =
      k.fundingValueSat) :
    outputSum (dustTrimmedOutputs dust k) +
        outputSum (dustDroppedOutputs dust k) + anchorValueOf k + k.feeSat =
      k.fundingValueSat := by
  rw [dust_trim_conservation]
  exact h

/-- Counterexample to the gross dust rule for HTLCs.  BOLT 3 compares
`amount - htlc_fee` against the dust limit; with gross comparison this model
can keep an output that the net rule trims.  This is recorded as a gap, not
hidden by a false theorem. -/
theorem gross_dust_rule_insufficient :
    ∃ (h : CommitmentHTLCOutput) (dust fee : Nat),
      h.amountSat - fee < dust ∧ ¬ isDust dust h.amountSat := by
  refine ⟨{ direction := Direction.local
            amountSat := 1000
            cltvExpiry := 0
            state := HTLCState.offered }, 950, 100, ?_⟩
  show 1000 - 100 < 950 ∧ ¬ (1000 < 950)
  decide

/-! ## 5. Commitment validity under a reserve violation -/

/-- The reserve that applies to a commitment output: the holder's own
`to_local` must satisfy the reserve advertised by the *other* endpoint. -/
def commitmentReserveSat (c : Channel) (k : Commitment) : Nat :=
  match k.holder with
  | .local => localReserveSat c
  | .remote => remoteReserveSat c

/-- The holder's `to_local` output meets the applicable reserve. -/
def CommitmentReserveOk (c : Channel) (k : Commitment) : Prop :=
  commitmentReserveSat c k ≤ k.toLocalSat

/-- A commitment is valid when its holder output meets the reserve, its
funding value agrees with the channel, and every created output is above the
owner's dust limit. -/
def CommitmentValid (c : Channel) (dust : Nat) (k : Commitment) : Prop :=
  CommitmentReserveOk c k ∧
    k.fundingValueSat = c.fundingValueSat ∧
      (∀ o, o ∈ dustTrimmedOutputs dust k → ¬ isDust dust o.value)

/-- A valid commitment meets the reserve. -/
theorem commitmentValid_reserve {c : Channel} {dust : Nat} {k : Commitment}
    (h : CommitmentValid c dust k) : CommitmentReserveOk c k :=
  h.1

/-- A valid commitment creates no sub-dust output. -/
theorem commitmentValid_no_dust_output {c : Channel} {dust : Nat}
    {k : Commitment} (h : CommitmentValid c dust k) :
    ∀ o, o ∈ dustTrimmedOutputs dust k → ¬ isDust dust o.value :=
  h.2.2

/-- A reserve violation makes the corresponding commitment invalid.  This is
the interface form of the BOLT 2/LDK rule: the reserve check is part of
validity, not an optional post-hoc warning. -/
theorem reserve_violation_invalidates_commitment {c : Channel} {dust : Nat}
    {k : Commitment} (h : ¬ CommitmentReserveOk c k) :
    ¬ CommitmentValid c dust k :=
  fun hv => h hv.1

/-- If the commitment is valid and its holder is the local node, the local
`to_local` output is at least the local reserve. -/
theorem commitmentValid_local_toLocal_ge {c : Channel} {dust : Nat}
    {k : Commitment} (h : CommitmentValid c dust k) (hh : k.holder = .local) :
    localReserveSat c ≤ k.toLocalSat := by
  have hres := h.1
  simpa [CommitmentReserveOk, commitmentReserveSat, hh] using hres

/-- If the commitment is valid and its holder is the remote node, the remote
`to_local` output is at least the remote reserve. -/
theorem commitmentValid_remote_toLocal_ge {c : Channel} {dust : Nat}
    {k : Commitment} (h : CommitmentValid c dust k) (hh : k.holder = .remote) :
    remoteReserveSat c ≤ k.toLocalSat := by
  have hres := h.1
  simpa [CommitmentReserveOk, commitmentReserveSat, hh] using hres

/-! ## 6. Channel-level value conservation -/

/-- The settled channel ledger: local plus remote plus fee equals the
funding value.  Fees are in millisatoshis, like all channel balances. -/
def ValueConserved (c : Channel) (fee : Msat) : Prop :=
  c.balance.total.val + fee.val = c.fundingValue.val

/-- Unfolding `ValueConserved` gives the componentwise equation. -/
theorem valueConserved_iff (c : Channel) (fee : Msat) :
    ValueConserved c fee ↔
      c.balance.localBalance.val + c.balance.remoteBalance.val + fee.val =
        c.fundingValue.val := by
  simp [ValueConserved, Balance.total_val]

/-- Every legal `Step` preserves settled value conservation. -/
theorem step_preserves_valueConservation {c c' : Channel}
    {e : ProtocolEvent} (h : Step c e c') {fee : Msat}
    (hc : ValueConserved c fee) : ValueConserved c' fee := by
  cases h <;> simpa [ValueConserved] using hc

/-- The pending HTLC value in a channel: the sum of the offered and received
HTLC amounts.  This is the ledger bucket a real `update_add_htlc` would move
value into. -/
def htlcInFlightValue (c : Channel) : Nat :=
  ((c.htlcs.filter (fun h =>
      h.state = HTLCState.offered ∨ h.state = HTLCState.received)).map
    (fun h => h.amount.val)).sum

/-- The arithmetic core of adding one pending local HTLC: appending an
`offered` record contributes exactly its amount to `htlcInFlightValue`. -/
theorem inFlightSum_append_offered (l : List HTLC) (amount : Msat) :
    (((l ++
        ([{ direction := Direction.local
            amount := amount
            paymentHash := ⟨ByteArray.empty⟩
            cltvExpiry := 0
            state := HTLCState.offered }] : List HTLC)).filter
      (fun h => h.state = HTLCState.offered ∨ h.state = HTLCState.received)).map
        (fun h => h.amount.val)).sum =
      (((l.filter
        (fun h => h.state = HTLCState.offered ∨ h.state = HTLCState.received)).map
          (fun h => h.amount.val)).sum + amount.val) := by
  simp [List.filter_append, List.map_append, List.sum_append]

/-- When the spent amount fits inside the settled local balance, the total
ledger drops by exactly that amount; this is where the non-truncation
precondition is used. -/
theorem spendLocalBalance_total_val {b : Balance} {amountMsat : Nat}
    (h : amountMsat ≤ b.localBalance.val) :
    (spendLocalBalance b amountMsat).total.val = b.total.val - amountMsat := by
  simp [spendLocalBalance, Balance.total_val]
  omega

/-- Next model extension: add BOLT 2 `update_add_htlc` (a local balance drop
plus a new pending HTLC) to `Channel.Step` and prove that the
settled-plus-in-flight ledger is preserved.  The current `Step` relation
changes neither balances nor HTLCs, so this cannot be derived from the wave-A
transition relation yet.  The unconditional statement is also false as
written, because `spendLocalBalance` uses truncated `Nat` subtraction; see
`committed_update_preserves_ledger_counterexample` and the corrected
`committed_update_preserves_ledger_of_le` below. -/
theorem committed_update_preserves_ledger (c c' : Channel) (fee : Msat)
    (amount : Msat)
    (h_old : c.balance.total.val + htlcInFlightValue c + fee.val =
      c.fundingValue.val)
    (h_step : c' = { c with
      balance := spendLocalBalance c.balance amount.val
      htlcs := c.htlcs ++
        [{ direction := Direction.local
           amount := amount
           paymentHash := ⟨ByteArray.empty⟩
           cltvExpiry := 0
           state := HTLCState.offered }] }) :
    c'.balance.total.val + htlcInFlightValue c' + fee.val =
      c'.fundingValue.val := by
  -- The unconditional statement is false: `spendLocalBalance` truncates at
  -- zero, so an added HTLC may exceed the settled local balance.
  -- OBLIGATION: LN-CH-101 missing bridge: no `Step`/`update_add_htlc`
  -- constructor supplies `amount.val ≤ c.balance.localBalance.val`; the
  -- truncated subtraction makes the unconditional ledger equation false.
  sorry

/-- Corrected committed-update ledger.  The unconditional
`committed_update_preserves_ledger` cannot hold for arbitrary `amount`,
because `spendLocalBalance` is truncated subtraction: an HTLC larger than the
settled local balance would add in-flight value without removing settled
value.  Under the BOLT 2 funding precondition that the added HTLC fits in the
settled local balance, the update conserves settled plus in-flight value. -/
theorem committed_update_preserves_ledger_of_le (c c' : Channel) (fee : Msat)
    (amount : Msat)
    (h_fits : amount.val ≤ c.balance.localBalance.val)
    (h_old : c.balance.total.val + htlcInFlightValue c + fee.val =
      c.fundingValue.val)
    (h_step : c' = { c with
      balance := spendLocalBalance c.balance amount.val
      htlcs := c.htlcs ++
        [{ direction := Direction.local
           amount := amount
           paymentHash := ⟨ByteArray.empty⟩
           cltvExpiry := 0
           state := HTLCState.offered }] }) :
    c'.balance.total.val + htlcInFlightValue c' + fee.val =
      c'.fundingValue.val := by
  subst c'
  unfold htlcInFlightValue at h_old ⊢
  rw [spendLocalBalance_total_val h_fits, inFlightSum_append_offered]
  simp only [Balance.total_val] at h_old ⊢
  omega

/-- Counterexample to the unconditional `committed_update_preserves_ledger`.
The channel has zero settled balances and zero funding value; adding a
1-msat local HTLC leaves the total settled balance at zero by truncated
subtraction, so the successor has `0 + 1 + 0 ≠ 0`.  This is why the corrected
theorem carries `amount.val ≤ c.balance.localBalance.val`. -/
theorem committed_update_preserves_ledger_counterexample :
    ∃ (c c' : Channel) (fee amount : Msat),
      c.balance.total.val + htlcInFlightValue c + fee.val = c.fundingValue.val ∧
      c' = { c with
        balance := spendLocalBalance c.balance amount.val
        htlcs := c.htlcs ++
          [{ direction := Direction.local
             amount := amount
             paymentHash := ⟨ByteArray.empty⟩
             cltvExpiry := 0
             state := HTLCState.offered }] } ∧
      c'.balance.total.val + htlcInFlightValue c' + fee.val ≠
        c'.fundingValue.val := by
  let p : ChannelParams := { dustLimitSat := 0
                             channelReserveSat := 0
                             toSelfDelay := 0
                             maxHtlcValue := ⟨0⟩
                             htlcMinimum := ⟨0⟩
                             feerate := ⟨0⟩
                             anchorOutputs := false }
  let e : Endpoint := { nodeId := ⟨ByteArray.empty⟩
                        fundingPubKey := ⟨ByteArray.empty⟩
                        paymentBasepoint := ⟨ByteArray.empty⟩
                        delayedPaymentBasepoint := ⟨ByteArray.empty⟩
                        params := p }
  let c : Channel := { channelId := ⟨ByteArray.empty⟩
                       funding := ⟨ByteArray.empty, 0⟩
                       fundingValue := ⟨0⟩
                       localEndpoint := e
                       remoteEndpoint := e
                       phase := ChannelPhase.negotiating
                       localCommitmentNumber := 0
                       remoteCommitmentNumber := 0
                       balance := { localBalance := ⟨0⟩, remoteBalance := ⟨0⟩ }
                       htlcs := [] }
  let amount : Msat := ⟨1⟩
  let fee : Msat := ⟨0⟩
  let c' : Channel := { c with
    balance := spendLocalBalance c.balance amount.val
    htlcs := c.htlcs ++
      [{ direction := Direction.local
         amount := amount
         paymentHash := ⟨ByteArray.empty⟩
         cltvExpiry := 0
         state := HTLCState.offered }] }
  refine ⟨c, c', fee, amount, ?_, rfl, ?_⟩
  · simp [c, fee, htlcInFlightValue, Balance.total_val]
  · simp [c', c, fee, amount, spendLocalBalance, htlcInFlightValue,
      Balance.total_val]

end LnLean.Proofs.Channel
