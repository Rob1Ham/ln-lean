import LnLean.Proofs.Conservation

/-!
# LnLean.Proofs.PhaseC2.GlobalConservation

English claim.  A ledger of Lightning channels never creates value.  Each
channel is represented by its current commitment transaction, and an entry
is conserving when the BOLT 3 balance equation holds for it:

  `totalOutputValue + feeSat = fundingValueSat`.

The ledger's total value is the sum of the channels' emitted output values and
its total fee is the sum of their commitment fees.  If every channel is
conserving, then the ledger's total value plus total fee equals the sum of the
channels' funding values; in particular total value never exceeds total
funding.  A step that replaces one channel by a conserving transition which
keeps the same funding value leaves the ledger's total value plus total fee
unchanged.  The total also decomposes over `append` and `cons`.

BOLT sections.
* BOLT 3 §2 `Commitment Transaction` (`refs/bolts/03-transactions.md:83-353`):
  the output value equation `funding = outputs + fee`.
* BOLT 3 §4 `Fees` (`refs/bolts/03-transactions.md:464-576`).
* BOLT 2 `closing_signed` (`refs/bolts/02-peer-protocol.md:2411-2501`).

rust-lightning anchors at `fe4900930c6bd5786ec4203274d7cf312776a5a6`.
* `lightning/src/ln/chan_utils.rs:716-744` (`HTLCOutputInCommitment`, the
  floored satoshi amount used in the value sum).
* `lightning/src/ln/chan_utils.rs:1614` (`struct CommitmentTransaction`).
* `lightning/src/ln/channel.rs:1546` (`struct Channel`, one funding value per
  channel).

This module reuses the single-commitment result
`LnLean.Proofs.conserved_no_value_creation` and the channel-ledger account
`LnLean.Proofs.ChannelLedger`, but keeps the multi-channel layer additive:
channels are independent, so global conservation is the sum of the
per-channel equations.

What is NOT modelled.
* Ownership of channels, routing between them, and cross-channel HTLC
  settlement.  A multi-channel step is local to one ledger entry.
* Splicing and channel resizing, which would change a channel's funding
  value; the step theorem therefore requires the funding value to be
  preserved.
* Wire encoding, signatures, and L1 transaction construction.
-/

namespace LnLean.Proofs.PhaseC2

open LnLean
open LnLean.Channel
open LnLean.Proofs (CommitmentConserved)

set_option autoImplicit false

/-! ## The multi-channel ledger -/

/-- A ledger of channels, each represented by its current commitment
transaction. -/
structure MultiChannelLedger where
  channels : List Commitment
deriving Repr, DecidableEq, BEq

namespace MultiChannelLedger

/-- Sum of the emitted output values of every channel. -/
def totalValue (m : MultiChannelLedger) : Nat :=
  (m.channels.map Commitment.totalOutputValue).sum

/-- Sum of the commitment fees of every channel. -/
def totalFee (m : MultiChannelLedger) : Nat :=
  (m.channels.map Commitment.feeSat).sum

/-- Sum of the funding values of every channel. -/
def totalFunding (m : MultiChannelLedger) : Nat :=
  (m.channels.map Commitment.fundingValueSat).sum

/-- Every channel in the ledger satisfies its BOLT 3 balance equation. -/
def AllConserved (m : MultiChannelLedger) : Prop :=
  ∀ c, c ∈ m.channels → CommitmentConserved c

/-- The empty ledger. -/
def empty : MultiChannelLedger :=
  { channels := [] }

/-- Prepend one channel to a ledger. -/
def cons (c : Commitment) (m : MultiChannelLedger) : MultiChannelLedger :=
  { channels := c :: m.channels }

/-- Concatenate two ledgers. -/
def append (m₁ m₂ : MultiChannelLedger) : MultiChannelLedger :=
  { channels := m₁.channels ++ m₂.channels }

/-- Replace one channel, identified by the decomposition
`channels = before ++ c :: after`, by `step c`. -/
def stepChannel (_m : MultiChannelLedger)
    (before after : List Commitment) (c : Commitment)
    (step : Commitment → Commitment) : MultiChannelLedger :=
  { channels := before ++ step c :: after }

/-! ## Additive decomposition -/

/-- The sum of a mapped list split at one distinguished element. -/
theorem sum_map_append_cons (f : Commitment → Nat)
    (before after : List Commitment) (c : Commitment) :
    ((before ++ c :: after).map f).sum =
      (before.map f).sum + f c + (after.map f).sum := by
  simp [List.map_append, List.sum_append]
  omega

theorem totalValue_nil : (empty : MultiChannelLedger).totalValue = 0 := rfl

theorem totalFee_nil : (empty : MultiChannelLedger).totalFee = 0 := rfl

theorem totalFunding_nil : (empty : MultiChannelLedger).totalFunding = 0 := rfl

@[simp] theorem totalValue_cons (c : Commitment)
    (m : MultiChannelLedger) :
    (cons c m).totalValue = c.totalOutputValue + m.totalValue := by
  simp [cons, totalValue]

@[simp] theorem totalFee_cons (c : Commitment)
    (m : MultiChannelLedger) :
    (cons c m).totalFee = c.feeSat + m.totalFee := by
  simp [cons, totalFee]

@[simp] theorem totalFunding_cons (c : Commitment)
    (m : MultiChannelLedger) :
    (cons c m).totalFunding = c.fundingValueSat + m.totalFunding := by
  simp [cons, totalFunding]

@[simp] theorem totalValue_append (m₁ m₂ : MultiChannelLedger) :
    (append m₁ m₂).totalValue = m₁.totalValue + m₂.totalValue := by
  simp [append, totalValue, List.map_append, List.sum_append]

@[simp] theorem totalFee_append (m₁ m₂ : MultiChannelLedger) :
    (append m₁ m₂).totalFee = m₁.totalFee + m₂.totalFee := by
  simp [append, totalFee, List.map_append, List.sum_append]

@[simp] theorem totalFunding_append (m₁ m₂ : MultiChannelLedger) :
    (append m₁ m₂).totalFunding = m₁.totalFunding + m₂.totalFunding := by
  simp [append, totalFunding, List.map_append, List.sum_append]

/-- The total splits exactly at the distinguished channel of a
`before ++ c :: after` decomposition. -/
theorem totalValue_eq_segments (m : MultiChannelLedger)
    (before after : List Commitment) (c : Commitment)
    (hmem : m.channels = before ++ c :: after) :
    m.totalValue =
      (before.map Commitment.totalOutputValue).sum +
        c.totalOutputValue +
        (after.map Commitment.totalOutputValue).sum := by
  unfold totalValue
  rw [hmem, sum_map_append_cons]

theorem totalFee_eq_segments (m : MultiChannelLedger)
    (before after : List Commitment) (c : Commitment)
    (hmem : m.channels = before ++ c :: after) :
    m.totalFee =
      (before.map Commitment.feeSat).sum + c.feeSat +
        (after.map Commitment.feeSat).sum := by
  unfold totalFee
  rw [hmem, sum_map_append_cons]

theorem totalFunding_eq_segments (m : MultiChannelLedger)
    (before after : List Commitment) (c : Commitment)
    (hmem : m.channels = before ++ c :: after) :
    m.totalFunding =
      (before.map Commitment.fundingValueSat).sum + c.fundingValueSat +
        (after.map Commitment.fundingValueSat).sum := by
  unfold totalFunding
  rw [hmem, sum_map_append_cons]

/-! ## Conservation of the additive totals -/

/-- Conserved channels make the ledger totals add up to the total funding. -/
theorem totalValue_add_totalFee_eq_totalFunding
    (m : MultiChannelLedger) (h : m.AllConserved) :
    m.totalValue + m.totalFee = m.totalFunding := by
  cases m with
  | mk channels =>
      induction channels with
      | nil =>
          simp [totalValue, totalFee, totalFunding]
      | cons c cs ih =>
          have hc : CommitmentConserved c := h c (by simp)
          have hcs : (MultiChannelLedger.mk cs).AllConserved := by
            intro x hx
            exact h x (by simp [hx])
          have ih' := ih hcs
          unfold CommitmentConserved at hc
          simp [totalValue, totalFee, totalFunding] at ih' ⊢
          omega

/-- **No value creation across the ledger**: total emitted value cannot
exceed total funding when every channel is conserving. -/
theorem multiLedger_total_le_funding (m : MultiChannelLedger)
    (h : m.AllConserved) :
    m.totalValue ≤ m.totalFunding := by
  have hEq := totalValue_add_totalFee_eq_totalFunding m h
  omega

/-- Conservation is stable under `cons`. -/
theorem AllConserved_cons {c : Commitment} {m : MultiChannelLedger}
    (hc : CommitmentConserved c) (hm : m.AllConserved) :
    (cons c m).AllConserved := by
  intro x hx
  rcases List.mem_cons.mp hx with h | h
  · subst h
    exact hc
  · exact hm x h

/-- Conservation is stable under `append`. -/
theorem AllConserved_append {m₁ m₂ : MultiChannelLedger}
    (h₁ : m₁.AllConserved) (h₂ : m₂.AllConserved) :
    (append m₁ m₂).AllConserved := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact h₁ x h
  · exact h₂ x h

/-! ## A conserved step on one channel -/

/-- A transition `c → c'` conserves when it keeps the channel's funding value
and the target commitment satisfies the BOLT 3 balance equation. -/
def ConservedTransition (c c' : Commitment) : Prop :=
  c'.fundingValueSat = c.fundingValueSat ∧ CommitmentConserved c'

/-- **No value creation for a one-channel step.**  If every channel in the
ledger is conserved, and the step replaces exactly one channel `c` by a
conserving `step c` with the same funding value, then the ledger's total
value plus total fees is unchanged.

The step is located by the decomposition `channels = before ++ c :: after`,
so no index bookkeeping or `List.get` default is needed. -/
theorem multiLedger_no_value_creation
    (m : MultiChannelLedger) (before after : List Commitment)
    (c : Commitment) (step : Commitment → Commitment)
    (hmem : m.channels = before ++ c :: after)
    (hall : m.AllConserved)
    (htrans : ConservedTransition c (step c)) :
    (stepChannel m before after c step).totalValue +
        (stepChannel m before after c step).totalFee =
      m.totalValue + m.totalFee := by
  rcases htrans with ⟨hfund, hstep⟩
  have hc : CommitmentConserved c := hall c (by rw [hmem]; simp)
  have hvOld := totalValue_eq_segments m before after c hmem
  have hfOld := totalFee_eq_segments m before after c hmem
  have hvNew := totalValue_eq_segments
    (stepChannel m before after c step) before after (step c) (by rfl)
  have hfNew := totalFee_eq_segments
    (stepChannel m before after c step) before after (step c) (by rfl)
  unfold CommitmentConserved at hc hstep
  rw [hvNew, hfNew, hvOld, hfOld]
  omega

/-- A step that keeps the funding value keeps the ledger's total funding. -/
theorem stepChannel_totalFunding (m : MultiChannelLedger)
    (before after : List Commitment) (c : Commitment)
    (step : Commitment → Commitment)
    (hmem : m.channels = before ++ c :: after)
    (hfund : (step c).fundingValueSat = c.fundingValueSat) :
    (stepChannel m before after c step).totalFunding = m.totalFunding := by
  have hNew := totalFunding_eq_segments
    (stepChannel m before after c step) before after (step c) (by rfl)
  have hOld := totalFunding_eq_segments m before after c hmem
  rw [hNew, hOld, hfund]

/-- The same step also cannot push the new ledger above the old total
funding. -/
theorem multiLedger_step_total_le_funding
    (m : MultiChannelLedger) (before after : List Commitment)
    (c : Commitment) (step : Commitment → Commitment)
    (hmem : m.channels = before ++ c :: after)
    (hall : m.AllConserved)
    (htrans : ConservedTransition c (step c)) :
    (stepChannel m before after c step).totalValue ≤ m.totalFunding := by
  have hcons : (stepChannel m before after c step).AllConserved := by
    intro x hx
    rw [stepChannel] at hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hall x (by rw [hmem]; exact List.mem_append.mpr (Or.inl hx))
    · rcases List.mem_cons.mp hx with hx | hx
      · subst hx
        exact htrans.2
      · exact hall x (by rw [hmem]; exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ hx)))
  have hle := multiLedger_total_le_funding _ hcons
  have hft := stepChannel_totalFunding m before after c step hmem htrans.1
  omega

/-- The append decomposition of the conservation equation: appending a
conserving ledger adds its value and fee to both sides. -/
theorem totalValue_add_totalFee_append
    (m₁ m₂ : MultiChannelLedger)
    (h₁ : m₁.AllConserved) (h₂ : m₂.AllConserved) :
    (append m₁ m₂).totalValue + (append m₁ m₂).totalFee =
      m₁.totalFunding + m₂.totalFunding := by
  rw [totalValue_append, totalFee_append]
  have hEq₁ := totalValue_add_totalFee_eq_totalFunding m₁ h₁
  have hEq₂ := totalValue_add_totalFee_eq_totalFunding m₂ h₂
  omega

/-- The cons decomposition of the conservation equation. -/
theorem totalValue_add_totalFee_cons
    (c : Commitment) (m : MultiChannelLedger)
    (hc : CommitmentConserved c) (hm : m.AllConserved) :
    (cons c m).totalValue + (cons c m).totalFee =
      c.fundingValueSat + m.totalFunding := by
  rw [totalValue_cons, totalFee_cons]
  have hEq := totalValue_add_totalFee_eq_totalFunding m hm
  unfold CommitmentConserved at hc
  omega

end MultiChannelLedger

end LnLean.Proofs.PhaseC2

/-! ## Catalog target `LN-SEC-002`

The catalog target is `LnLean.Proofs.Conservation.global_conservation`, but the
multi-channel ledger and its additive totals are defined in
`LnLean.Proofs.PhaseC2.MultiChannelLedger` (above), and importing this module
from `LnLean.Proofs.Conservation` would create an import cycle
(`Conservation` is imported here).  We therefore place the exact target in this
file and reopen the `LnLean.Proofs.Conservation` namespace, so the fully
qualified name exists exactly as catalogued.

Scope note: this statement covers every channel in the ledger
(`MultiChannelLedger.channels`).  It does **not** model an L1 spend set; the
`MultiChannelLedger` has no UTXO/spend component.  Consequently the theorem
covers the "all channels" half of the catalog wording only.  The L1 spend
ledger is modelled separately (e.g. `LnLean.Security.L1Ledger` and
`LnLean.Proofs.WaveD.D32`), not here. -/

namespace LnLean.Proofs.Conservation

open LnLean.Proofs.PhaseC2

/-- **Global conservation across a multi-channel ledger.**  If every channel
in `m` satisfies the BOLT 3 balance equation
(`totalOutputValue + feeSat = fundingValueSat`), then the ledger's emitted
value plus its commitment fees equals its total funding.  In particular no
finite collection of conserving channels creates value. -/
theorem global_conservation (m : MultiChannelLedger) (h : m.AllConserved) :
    m.totalValue + m.totalFee = m.totalFunding :=
  MultiChannelLedger.totalValue_add_totalFee_eq_totalFunding m h

end LnLean.Proofs.Conservation
