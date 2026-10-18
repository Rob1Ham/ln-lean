import LnLean.Security.Invariants
import LnLean.Security.Model
import LnLean.Bitcoin.Laws
import LnLean.Channel.Laws
import LnLean.Routing.Laws
import LnLean.Proofs.Conservation

/-!
# D32 — Across all channels and the L1 spend set, total value is conserved

Catalog: `LN-SEC-002`.  BOLT 3 §Commitment Transaction.  LDK anchor
`lightning/src/ln/chan_utils.rs:716` (`HTLCOutputInCommitment` and
`to_bitcoin_amount`, the satoshi-denominated commitment outputs).

The wave-A model proves per-commitment conservation
(`LnLean.Proofs.Conservation.CommitmentConserved`) and a per-channel bound
(`ledger_no_value_creation`), but it has no *global* statement over a finite
set of channels and it has no value-bearing L1 spend set: `L1Ledger`
(`LnLean.Security.Invariants`) records spent outpoints and a height, not
satoshi amounts.  This module supplies the missing aggregate vocabulary and
proves the global accounting equation.

The model built here has three layers.

1. **L1 spend set, with values.**  `L1Spend` adds the three satoshi fields
   of one L1 spend (`inputValueSat`, `outputValueSat`, `feeSat`) to the
   `OutRef` that the existing `L1Ledger` already records.
   `L1Spend.Conserves` is `input = output + fee`, the BOLT 3 / BOLT 5
   value equation for a transaction.  `L1SpendSet` is a finite list of
   such spends and keeps the `Nodup` no-double-spend predicate, so the
   `LN-SEC-001` result applies unchanged to its outpoints
   (`waveD_d32_spendSet_toL1_noDoubleSpend`).
2. **Channel accounts.**  A `ChannelAccount` binds one funding outpoint to
   the commitment the channel will broadcast (`current`) and the full list
   of commitments the model built for it (`history`).  `Conserved` says
   every commitment in `history` spends this channel's funding value and
   conserves value, and `current` is in `history`.
3. **Network.**  A `Network` pairs a finite list of channel accounts with
   an L1 spend set.  `L1SpendsChannels` is the bridge: the L1 spend set's
   outpoints and input values are exactly the channels' funding outpoints
   and funding values, in the same order.  This is the only modelling link
   that the existing model cannot state, because `L1Ledger` carries no
   values; it is an explicit hypothesis of the global theorem, not a
   primitive declaration or an unproved assumption in the logic.

Main results (`waveD_d32_global_conservation` and companions):

* the sum over all channels of `current.totalOutputValue + current.feeSat`
  equals the sum of all channel funding values;
* the sum over the L1 spend set of `outputValueSat + feeSat` equals the sum
  of its `inputValueSat`;
* because the L1 input values are the channel funding values, the two
  aggregates are equal: total value emitted by every channel commitment is
  exactly the total value emitted by the L1 spend set, and neither creates
  value;
* every individual commitment of every channel emits at most the total
  funding value across the network;
* adding a conserving channel or a conserving L1 spend preserves the
  equations and the no-double-spend predicate.

What is NOT modelled.  Transaction serialisation, script execution,
outpoint-to-value lookup on chain (the value is a field of `L1Spend`
rather than a UTXO-set query), fees paid to miners as an entity distinct
from `feeSat`, extra L1 spends that do not correspond to a channel funding
outpoint (these conserve individually by `L1Spend.Conserves`), and the
multiplicity of historical commitments.  `history` is used only for the
"no historical commitment creates value" bound; the aggregate equation
uses the single `current` commitment per channel so that one funding
output is counted exactly once.
-/

namespace LnLean.Proofs.WaveD.D32

open LnLean
open LnLean.Channel
open LnLean.Security

set_option autoImplicit false

-- OBLIGATION: LN-WD-D32

/-! ## Generic list-sum lemmas -/

/-- A member of a list of naturals is at most the list's sum. -/
private theorem nat_le_sum_of_mem {x : Nat} {xs : List Nat} (h : x ∈ xs) :
    x ≤ xs.sum := by
  induction xs with
  | nil => cases h
  | cons y ys ih =>
      rcases List.mem_cons.mp h with hxy | hmem
      · subst y
        simp only [List.sum_cons]
        omega
      · have hle := ih hmem
        simp only [List.sum_cons]
        omega

/-! ## The L1 spend set, with satoshi values -/

/-- One L1 spend as seen by the value ledger: the outpoint it consumes, the
value that outpoint carried, the value of its outputs, and its fee.  This
extends `LnLean.Security.OutRef` (the outpoint vocabulary of `LN-SEC-001`)
with the amounts that `L1Ledger` does not record. -/
structure L1Spend where
  /-- The consumed outpoint, in the `LN-SEC-001` vocabulary. -/
  spentOutpoint : OutRef
  /-- The value of the consumed outpoint, in satoshis. -/
  inputValueSat : Nat
  /-- The sum of the transaction's output values, in satoshis. -/
  outputValueSat : Nat
  /-- The miner fee, in satoshis. -/
  feeSat : Nat
deriving Repr, DecidableEq, BEq

/-- The value equation of one L1 spend: inputs equal outputs plus fee. -/
def L1Spend.Conserves (s : L1Spend) : Prop :=
  s.inputValueSat = s.outputValueSat + s.feeSat

/-- A finite L1 spend set.  This is the value-carrying refinement of
`LnLean.Security.L1Ledger`: the outpoints and their `Nodup` discipline are
those of `LN-SEC-001`, and the amounts make the conservation claim
expressible. -/
structure L1SpendSet where
  spends : List L1Spend
deriving Repr, DecidableEq, BEq

/-- The outpoints consumed by the spend set. -/
def L1SpendSet.spentOutpoints (s : L1SpendSet) : List OutRef :=
  s.spends.map L1Spend.spentOutpoint

/-- No outpoint is consumed twice.  This is exactly `L1Ledger.NoDoubleSpend`
on the projected outpoints. -/
def L1SpendSet.NoDoubleSpend (s : L1SpendSet) : Prop :=
  s.spentOutpoints.Nodup

/-- Total input value consumed by the spend set. -/
def L1SpendSet.totalInput (s : L1SpendSet) : Nat :=
  (s.spends.map L1Spend.inputValueSat).sum

/-- Total value emitted by the spend set's outputs. -/
def L1SpendSet.totalOutput (s : L1SpendSet) : Nat :=
  (s.spends.map L1Spend.outputValueSat).sum

/-- Total fee paid by the spend set. -/
def L1SpendSet.totalFee (s : L1SpendSet) : Nat :=
  (s.spends.map L1Spend.feeSat).sum

/-- Every spend in the set conserves value. -/
def L1SpendSet.AllConserved (s : L1SpendSet) : Prop :=
  ∀ x ∈ s.spends, x.Conserves

/-- Add one spend to the set. -/
def L1SpendSet.add (s : L1SpendSet) (x : L1Spend) : L1SpendSet :=
  { spends := x :: s.spends }

/-- Project the spend set onto the outpoint-only L1 ledger of `LN-SEC-001`. -/
def L1SpendSet.toL1Ledger (s : L1SpendSet) (height : Height) : L1Ledger :=
  { spent := s.spentOutpoints, height := height }

/-- The value equation sums over an arbitrary finite list of conserving
spends. -/
private theorem l1_spends_conserved_aux (spends : List L1Spend)
    (h : ∀ x ∈ spends, x.Conserves) :
    (spends.map L1Spend.inputValueSat).sum =
      (spends.map L1Spend.outputValueSat).sum +
        (spends.map L1Spend.feeSat).sum := by
  induction spends with
  | nil => simp
  | cons x t ih =>
      have hx : x.Conserves := h x List.mem_cons_self
      have ht : ∀ y ∈ t, y.Conserves :=
        fun y hy => h y (List.mem_cons_of_mem x hy)
      have hi := ih ht
      unfold L1Spend.Conserves at hx
      simp only [List.map_cons, List.sum_cons]
      omega

/-- **The value equation sums over the L1 spend set.**  If every spend
conserves, then the total input value equals total output value plus total
fee. -/
theorem waveD_d32_l1SpendSet_conserved (s : L1SpendSet)
    (h : s.AllConserved) :
    s.totalInput = s.totalOutput + s.totalFee := by
  unfold L1SpendSet.AllConserved at h
  unfold L1SpendSet.totalInput L1SpendSet.totalOutput L1SpendSet.totalFee
  exact l1_spends_conserved_aux s.spends h

/-- **No L1 spend set creates value.**  Emitted output value never exceeds
consumed input value. -/
theorem waveD_d32_l1SpendSet_no_value_creation (s : L1SpendSet)
    (h : s.AllConserved) :
    s.totalOutput ≤ s.totalInput := by
  have hsum := waveD_d32_l1SpendSet_conserved s h
  omega

/-- Adding a conserving spend preserves value conservation. -/
theorem waveD_d32_l1SpendSet_add_conserved (s : L1SpendSet) (x : L1Spend)
    (hs : s.AllConserved) (hx : x.Conserves) :
    (s.add x).AllConserved := by
  intro y hy
  rcases List.mem_cons.mp hy with rfl | hmem
  · exact hx
  · exact hs y hmem

/-- **Adding a fresh, conserving spend preserves no-double-spend.**  This is
the value-bearing version of `L1Ledger.spend_preserves_noDoubleSpend`
(`LN-SEC-001`). -/
theorem waveD_d32_l1SpendSet_add_noDoubleSpend (s : L1SpendSet)
    (x : L1Spend) (hfresh : x.spentOutpoint ∉ s.spentOutpoints)
    (h : s.NoDoubleSpend) :
    (s.add x).NoDoubleSpend := by
  unfold L1SpendSet.NoDoubleSpend L1SpendSet.spentOutpoints at *
  simp only [L1SpendSet.add, List.map_cons]
  exact List.nodup_cons.mpr ⟨hfresh, h⟩

/-- The projected outpoint ledger inherits the no-double-spend predicate. -/
theorem waveD_d32_spendSet_toL1_noDoubleSpend (s : L1SpendSet)
    (height : Height) (h : s.NoDoubleSpend) :
    (s.toL1Ledger height).NoDoubleSpend :=
  h

/-! ## One channel's account -/

/-- One channel as seen by the global accounting: the funding outpoint it
consumes, the commitment it will broadcast, and every commitment the model
has built for it.  `ChannelLedger` in `LnLean.Proofs.Conservation` stores
only the funding value and the commitment list; the outpoint and the
distinguished current commitment are added here so the channel can be
matched against the L1 spend set and counted exactly once. -/
structure ChannelAccount where
  /-- The channel's funding outpoint, in the `LN-SEC-001` vocabulary. -/
  fundingOutpoint : OutRef
  /-- The commitment the channel will broadcast. -/
  current : Commitment
  /-- Every commitment the model has built for this channel. -/
  history : List Commitment

/-- The channel's funding value, read from the current commitment.  This is
the same `fundingValueSat` field that `CommitmentConserved` uses, so the
channel account and the commitment equation cannot disagree definitionally. -/
def ChannelAccount.fundingValueSat (a : ChannelAccount) : Nat :=
  a.current.fundingValueSat

/-- The channel is conserved when its current commitment is one of the
commitments built for it, and every built commitment spends this channel's
funding value and conserves value. -/
def ChannelAccount.Conserved (a : ChannelAccount) : Prop :=
  a.current ∈ a.history ∧
    ∀ c ∈ a.history,
      c.fundingValueSat = a.current.fundingValueSat ∧
        CommitmentConserved c

/-- The value emitted by the channel's current commitment. -/
def ChannelAccount.currentOutputs (a : ChannelAccount) : Nat :=
  a.current.totalOutputValue

/-- The fee of the channel's current commitment. -/
def ChannelAccount.currentFee (a : ChannelAccount) : Nat :=
  a.current.feeSat

/-- **A conserved channel's current commitment conserves value at the
channel's funding value.** -/
theorem waveD_d32_channelAccount_conserved (a : ChannelAccount)
    (h : a.Conserved) :
    a.currentOutputs + a.currentFee = a.fundingValueSat := by
  unfold ChannelAccount.Conserved at h
  have hall := h.2 a.current h.1
  exact hall.2

/-- The outpoint-and-value view used by the wave-A `ChannelLedger`.  This
lets the global result below reuse `LnLean.Proofs.Conservation`'s
`ledger_no_value_creation` without redefining the channel ledger. -/
def ChannelAccount.toLedger (a : ChannelAccount) :
    LnLean.Proofs.ChannelLedger :=
  { fundingValueSat := a.fundingValueSat
    commitments := a.history }

/-- **A conserved account is a conserving wave-A `ChannelLedger`.**  The
`ChannelAccount` vocabulary refines, rather than replaces,
`LnLean.Proofs.ChannelLedger`. -/
theorem waveD_d32_channelAccount_toLedger_allConserved (a : ChannelAccount)
    (h : a.Conserved) : a.toLedger.AllConserved := by
  intro c hc
  unfold ChannelAccount.Conserved at h
  exact h.2 c hc

/-- A conserved account's current commitment cannot emit more than the
channel's funding value. -/
theorem waveD_d32_channelAccount_outputs_le_funding (a : ChannelAccount)
    (h : a.Conserved) :
    a.current.totalOutputValue ≤ a.fundingValueSat := by
  have hc := waveD_d32_channelAccount_conserved a h
  unfold ChannelAccount.currentOutputs ChannelAccount.currentFee at hc
  omega

/-! ## A network of channels and an L1 spend set -/

/-- A closed value system: a finite list of channel accounts together with
the L1 spend set that settles their funding outputs. -/
structure Network where
  channels : List ChannelAccount
  l1 : L1SpendSet

/-- Every channel in the network is conserved. -/
def Network.AllConserved (n : Network) : Prop :=
  ∀ a ∈ n.channels, a.Conserved

/-- Total funding value across all channels. -/
def Network.totalFunding (n : Network) : Nat :=
  (n.channels.map ChannelAccount.fundingValueSat).sum

/-- Total value emitted by the channels' current commitments. -/
def Network.totalCurrentOutputs (n : Network) : Nat :=
  (n.channels.map ChannelAccount.currentOutputs).sum

/-- Total commitment fee across the channels' current commitments. -/
def Network.totalCurrentFees (n : Network) : Nat :=
  (n.channels.map ChannelAccount.currentFee).sum

/-- The bridge between the two ledgers: the L1 spend set consumes exactly
the channels' funding outpoints, with exactly the channels' funding values,
in the same order.  `L1Ledger` has no value field, so this link is stated
as an explicit hypothesis of the global theorem rather than derived. -/
def Network.L1SpendsChannels (n : Network) : Prop :=
  n.l1.spends.map L1Spend.spentOutpoint =
      n.channels.map ChannelAccount.fundingOutpoint ∧
    n.l1.spends.map L1Spend.inputValueSat =
      n.channels.map ChannelAccount.fundingValueSat

/-- Add one channel to the network. -/
def Network.addChannel (n : Network) (a : ChannelAccount) : Network :=
  { n with channels := a :: n.channels }

/-- Add one channel and the L1 spend that consumes its funding output. -/
def Network.addChannelWithSpend (n : Network) (a : ChannelAccount)
    (x : L1Spend) : Network :=
  { channels := a :: n.channels, l1 := n.l1.add x }

/-- The channel aggregate equation over an arbitrary finite list of
channels. -/
private theorem channel_list_value_conserved (chs : List ChannelAccount)
    (h : ∀ a ∈ chs, a.Conserved) :
    (chs.map (fun a => a.current.totalOutputValue)).sum +
        (chs.map (fun a => a.current.feeSat)).sum =
      (chs.map (fun a => a.fundingValueSat)).sum := by
  induction chs with
  | nil => simp
  | cons a t ih =>
      have ha : a.Conserved := h a List.mem_cons_self
      have ht : ∀ b ∈ t, b.Conserved :=
        fun b hb => h b (List.mem_cons_of_mem a hb)
      have hhead : a.current.totalOutputValue + a.current.feeSat =
          a.fundingValueSat := by
        have hc := waveD_d32_channelAccount_conserved a ha
        simpa [ChannelAccount.currentOutputs, ChannelAccount.currentFee] using hc
      have htail := ih ht
      simp only [List.map_cons, List.sum_cons]
      omega

/-- **The channel aggregate equation.**  The sum of every channel's current
commitment outputs plus its fee equals the sum of the channel funding
values. -/
theorem waveD_d32_network_value_conserved (n : Network)
    (h : n.AllConserved) :
    n.totalCurrentOutputs + n.totalCurrentFees = n.totalFunding := by
  unfold Network.AllConserved at h
  unfold Network.totalCurrentOutputs Network.totalCurrentFees
    Network.totalFunding
  exact channel_list_value_conserved n.channels h

/-- **The L1 inputs are exactly the channel funding values.** -/
theorem waveD_d32_totalFunding_eq_l1Input (n : Network)
    (h : n.L1SpendsChannels) :
    n.totalFunding = n.l1.totalInput := by
  unfold Network.L1SpendsChannels at h
  unfold Network.totalFunding L1SpendSet.totalInput
  rw [h.2]

/-- **Global conservation across all channels and the L1 spend set.**  If
every channel is conserved, every L1 spend conserves, and the L1 spend set
consumes exactly the channel funding outputs, then

`sum of channel outputs + channel fees = sum of L1 outputs + L1 fees`.

This is the global form of the BOLT 3 value equation: the value recorded by
the off-chain channel commitments is exactly the value recorded by the L1
spend set, with no creation on either side. -/
theorem waveD_d32_global_conservation (n : Network)
    (hch : n.AllConserved) (hl1 : n.l1.AllConserved)
    (hbridge : n.L1SpendsChannels) :
    n.totalCurrentOutputs + n.totalCurrentFees =
      n.l1.totalOutput + n.l1.totalFee := by
  have hchan := waveD_d32_network_value_conserved n hch
  have hl1 := waveD_d32_l1SpendSet_conserved n.l1 hl1
  have hfund := waveD_d32_totalFunding_eq_l1Input n hbridge
  rw [hchan, hfund]
  exact hl1

/-- **Global no-value-creation.**  The value emitted by all channel
commitments is bounded by the value emitted by the L1 spend set. -/
theorem waveD_d32_global_no_value_creation (n : Network)
    (hch : n.AllConserved) (hl1 : n.l1.AllConserved)
    (hbridge : n.L1SpendsChannels) :
    n.totalCurrentOutputs ≤ n.l1.totalOutput + n.l1.totalFee := by
  have h := waveD_d32_global_conservation n hch hl1 hbridge
  omega

/-- **Global no-value-creation, input form.**  The value emitted by all
channel commitments is bounded by the total L1 input value. -/
theorem waveD_d32_global_outputs_le_l1Input (n : Network)
    (hch : n.AllConserved) (hl1 : n.l1.AllConserved)
    (hbridge : n.L1SpendsChannels) :
    n.totalCurrentOutputs ≤ n.l1.totalInput := by
  have hno := waveD_d32_l1SpendSet_no_value_creation n.l1 hl1
  have hcap := waveD_d32_global_no_value_creation n hch hl1 hbridge
  have hsum := waveD_d32_l1SpendSet_conserved n.l1 hl1
  omega

/-- **No single commitment emits more than the total funding value.**  For
any channel of a conserved network and any commitment in its history, the
commitment's outputs are bounded by the network-wide funding total. -/
theorem waveD_d32_commitment_outputs_le_total_funding (n : Network)
    (h : n.AllConserved) {a : ChannelAccount} (ha : a ∈ n.channels)
    {c : Commitment} (hc : c ∈ a.history) :
    c.totalOutputValue ≤ n.totalFunding := by
  unfold Network.AllConserved at h
  have hcons := h a ha
  unfold ChannelAccount.Conserved at hcons
  have hall := hcons.2 c hc
  have hout : c.totalOutputValue ≤ a.fundingValueSat := by
    have hc' : CommitmentConserved c := hall.2
    unfold CommitmentConserved at hc'
    unfold ChannelAccount.fundingValueSat
    omega
  have hle : a.fundingValueSat ≤ n.totalFunding := by
    unfold Network.totalFunding ChannelAccount.fundingValueSat
    apply nat_le_sum_of_mem
    exact List.mem_map.mpr ⟨a, ha, rfl⟩
  omega

/-! ## Add/remove-style structural lemmas -/

/-- Adding a conserved channel to a conserved network preserves the channel
aggregate equation, and hence global conservation once the L1 bridge is
extended accordingly. -/
theorem waveD_d32_network_addChannel_conserved (n : Network)
    (a : ChannelAccount) (hn : n.AllConserved) (ha : a.Conserved) :
    (n.addChannel a).AllConserved := by
  intro b hb
  rcases List.mem_cons.mp hb with rfl | hmem
  · exact ha
  · exact hn b hmem

/-- **Adding a conserving channel and its L1 funding spend preserves the
global equation.**  The new channel's funding value is added to both sides:
the channel aggregate and the L1 aggregate each grow by
`a.fundingValueSat`.  The old bridge is extended by the new spend, whose
outpoint and value are those of the new channel; the enlarged bridge is
derived rather than assumed. -/
theorem waveD_d32_l1SpendsChannels_add (n : Network) (a : ChannelAccount)
    (x : L1Spend) (hbridge : n.L1SpendsChannels)
    (hxout : x.spentOutpoint = a.fundingOutpoint)
    (hxval : x.inputValueSat = a.fundingValueSat) :
    (n.addChannelWithSpend a x).L1SpendsChannels := by
  unfold Network.L1SpendsChannels at hbridge ⊢
  unfold Network.addChannelWithSpend L1SpendSet.add
  simp only [List.map_cons]
  rw [hxout]
  constructor
  · rw [hbridge.1]
  · rw [hxval, hbridge.2]

/-- **Adding a conserving channel and its L1 funding spend preserves the
global equation.** -/
theorem waveD_d32_global_conservation_add_channel (n : Network)
    (a : ChannelAccount) (x : L1Spend)
    (hn : n.AllConserved) (ha : a.Conserved)
    (hl1 : n.l1.AllConserved) (hx : x.Conserves)
    (hbridge : n.L1SpendsChannels)
    (hxout : x.spentOutpoint = a.fundingOutpoint)
    (hxval : x.inputValueSat = a.fundingValueSat) :
    (n.addChannelWithSpend a x).totalCurrentOutputs +
        (n.addChannelWithSpend a x).totalCurrentFees =
      (n.addChannelWithSpend a x).l1.totalOutput +
        (n.addChannelWithSpend a x).l1.totalFee := by
  have hch : (n.addChannelWithSpend a x).AllConserved := by
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hmem
    · exact ha
    · exact hn b hmem
  have hl1' : (n.addChannelWithSpend a x).l1.AllConserved :=
    waveD_d32_l1SpendSet_add_conserved n.l1 x hl1 hx
  have hbr := waveD_d32_l1SpendsChannels_add n a x hbridge hxout hxval
  exact waveD_d32_global_conservation (n.addChannelWithSpend a x) hch hl1' hbr

/-! ## The canonical L1 spend set of a finite channel list

The bridge hypothesis `L1SpendsChannels` is needed when the L1 spend set is
supplied independently.  When the spend set is *built from* the channels
(one L1 funding spend per channel), the bridge holds definitionally, and the
global equation becomes unconditional in the channel hypotheses. -/

/-- The canonical network of a finite list of channels: the L1 spend set has
exactly one spend per channel, consuming that channel's funding outpoint
with that channel's funding value and emitting exactly its current
commitment's outputs and fee. -/
def Network.ofChannels (chs : List ChannelAccount) : Network :=
  { channels := chs
    l1 :=
      { spends := chs.map fun a : ChannelAccount =>
          { spentOutpoint := a.fundingOutpoint
            inputValueSat := a.fundingValueSat
            outputValueSat := a.current.totalOutputValue
            feeSat := a.current.feeSat } } }

/-- The canonical spend set satisfies the bridge by construction. -/
theorem waveD_d32_ofChannels_l1SpendsChannels (chs : List ChannelAccount) :
    (Network.ofChannels chs).L1SpendsChannels := by
  unfold Network.L1SpendsChannels Network.ofChannels
  simp [List.map_map]

/-- The canonical spend set conserves exactly when the channels do. -/
theorem waveD_d32_ofChannels_l1_conserved (chs : List ChannelAccount)
    (h : ∀ a ∈ chs, a.Conserved) :
    (Network.ofChannels chs).l1.AllConserved := by
  intro x hx
  unfold Network.ofChannels at hx
  simp only [List.mem_map] at hx
  rcases hx with ⟨a, ha, rfl⟩
  have hc := waveD_d32_channelAccount_conserved a (h a ha)
  unfold ChannelAccount.currentOutputs ChannelAccount.currentFee at hc
  unfold L1Spend.Conserves
  dsimp only
  omega

/-- **Unconditional global conservation for a finite channel list and its
canonical L1 spend set.**  If every channel conserves value, then the total
value emitted by the channels' current commitments equals the total value
emitted by the L1 spend set built from those channels, and neither side
creates value. -/
theorem waveD_d32_ofChannels_global_conservation (chs : List ChannelAccount)
    (h : ∀ a ∈ chs, a.Conserved) :
    (Network.ofChannels chs).totalCurrentOutputs +
        (Network.ofChannels chs).totalCurrentFees =
      (Network.ofChannels chs).l1.totalOutput +
        (Network.ofChannels chs).l1.totalFee :=
  waveD_d32_global_conservation (Network.ofChannels chs) h
    (waveD_d32_ofChannels_l1_conserved chs h)
    (waveD_d32_ofChannels_l1SpendsChannels chs)

/-- **Unconditional global no-value-creation for a finite channel list and
its canonical L1 spend set.** -/
theorem waveD_d32_ofChannels_no_value_creation (chs : List ChannelAccount)
    (h : ∀ a ∈ chs, a.Conserved) :
    (Network.ofChannels chs).totalCurrentOutputs ≤
      (Network.ofChannels chs).l1.totalOutput +
        (Network.ofChannels chs).l1.totalFee :=
  waveD_d32_global_no_value_creation (Network.ofChannels chs) h
    (waveD_d32_ofChannels_l1_conserved chs h)
    (waveD_d32_ofChannels_l1SpendsChannels chs)

/-! ## A checked concrete network -/

/-- A 100000-satoshi channel commitment. -/
def demoCommitmentA : Commitment :=
  { holder := Direction.local
    commitmentNumber := 0
    fundingValueSat := 100000
    toLocalSat := 60000
    toRemoteSat := 39000
    htlcs := []
    feeSat := 1000
    contestDelay := 144
    anchorOutputs := false }

/-- A 50000-satoshi channel commitment. -/
def demoCommitmentB : Commitment :=
  { holder := Direction.remote
    commitmentNumber := 0
    fundingValueSat := 50000
    toLocalSat := 20000
    toRemoteSat := 29500
    htlcs := []
    feeSat := 500
    contestDelay := 144
    anchorOutputs := false }

/-- Two channels, funding outpoints (1,0) and (2,0). -/
def demoChannelA : ChannelAccount :=
  { fundingOutpoint := ⟨1, 0⟩
    current := demoCommitmentA
    history := [demoCommitmentA] }

def demoChannelB : ChannelAccount :=
  { fundingOutpoint := ⟨2, 0⟩
    current := demoCommitmentB
    history := [demoCommitmentB] }

/-- The L1 spend set consuming exactly the two funding outputs. -/
def demoL1 : L1SpendSet :=
  { spends :=
      [ { spentOutpoint := ⟨1, 0⟩
          inputValueSat := 100000
          outputValueSat := 99000
          feeSat := 1000 }
      , { spentOutpoint := ⟨2, 0⟩
          inputValueSat := 50000
          outputValueSat := 49500
          feeSat := 500 } ] }

/-- The demo network. -/
def demoNetwork : Network :=
  { channels := [demoChannelA, demoChannelB]
    l1 := demoL1 }

theorem waveD_d32_demo_channelA_conserved : demoChannelA.Conserved := by
  unfold ChannelAccount.Conserved
  constructor
  · simp [demoChannelA]
  · intro c hc
    simp [demoChannelA] at hc
    subst c
    exact ⟨rfl, by unfold CommitmentConserved; decide⟩

theorem waveD_d32_demo_channelB_conserved : demoChannelB.Conserved := by
  unfold ChannelAccount.Conserved
  constructor
  · simp [demoChannelB]
  · intro c hc
    simp [demoChannelB] at hc
    subst c
    exact ⟨rfl, by unfold CommitmentConserved; decide⟩

theorem waveD_d32_demo_network_conserved : demoNetwork.AllConserved := by
  intro a ha
  simp [demoNetwork] at ha
  rcases ha with rfl | rfl
  · exact waveD_d32_demo_channelA_conserved
  · exact waveD_d32_demo_channelB_conserved

theorem waveD_d32_demo_l1_conserved : demoL1.AllConserved := by
  intro x hx
  simp [demoL1] at hx
  rcases hx with rfl | rfl <;> (unfold L1Spend.Conserves; decide)

theorem waveD_d32_demo_l1SpendsChannels : demoNetwork.L1SpendsChannels := by
  unfold Network.L1SpendsChannels
  decide

/-- The concrete global equation holds numerically:
`(99000 + 49500) + (1000 + 500) = 148500 + 1500`. -/
theorem waveD_d32_concrete_global_conservation :
    demoNetwork.totalCurrentOutputs + demoNetwork.totalCurrentFees =
      demoL1.totalOutput + demoL1.totalFee :=
  waveD_d32_global_conservation demoNetwork waveD_d32_demo_network_conserved
    waveD_d32_demo_l1_conserved waveD_d32_demo_l1SpendsChannels

/-- The concrete totals, checked by evaluation. -/
theorem waveD_d32_concrete_totals :
    demoNetwork.totalCurrentOutputs = 148500 ∧
      demoNetwork.totalCurrentFees = 1500 ∧
      demoL1.totalOutput = 148500 ∧
      demoL1.totalFee = 1500 := by
  decide

end LnLean.Proofs.WaveD.D32
