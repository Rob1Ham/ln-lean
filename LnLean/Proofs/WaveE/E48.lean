import LnLean.Channel.Commitment
import LnLean.Channel.HTLC
import LnLean.Channel.Types

/-!
# Wave-E E48 — commitment output ordering (`LN-CH-003`)

Parent claim (`LnLean.Proofs.Obligations`, entry `LN-CH-003`):

> Commitment outputs are ordered by value then script, and dust HTLCs are
> trimmed.

BOLT 3 (`03-transactions.md`, pinned BOLT commit
`1aadb719b4007c4cea0ba6e36b08c4fb53788dee`), § *Transaction Output
Ordering*:

> Outputs in transactions are always sorted according to:
> * first according to their value, smallest first (in whole satoshis, note
>   that for HTLC outputs, the millisatoshi part must be ignored)
> * followed by `scriptpubkey`, comparing the common-length prefix
>   lexicographically as if by `memcmp`, then selecting the shorter script
>   (if they differ in length),
> * finally, for HTLC outputs, in increasing `cltv_expiry` order.

and § *Commitment Transaction Construction*: "Sort the outputs into
BIP 69+CLTV order."

## What the model actually does

`LnLean.Channel.Commitment.commitmentOutputs` concatenates four blocks in a
**fixed constructor order** and never sorts:

`to_local ++ to_remote ++ (htlcs in channel-list order) ++ anchors`.

The channel list is the update/insertion order of the HTLCs, not the value
order.  Consequently the model's list is *not* value-ordered in general.
`commitmentOutputs` returns the **pre-sort multiset** of outputs; the BOLT 3
value ordering is a property of the sorted transaction view, which the model
does not build.

## What can and cannot be stated

Two key components of the BOLT 3 rule are absent from the model:

* `CommitmentOutput` carries no `scriptPubKey`, so the "then script" key is
  not expressible.
* `CommitmentOutput.htlc` stores only `direction` and `valueSat`; it drops
  the HTLC's `cltvExpiry`, so the third key ("increasing `cltv_expiry`") is
  not expressible either.

Therefore this module proves:

* the value-ordering predicate and the fact that `commitmentOutputs` is not
  value-ordered in general (a general theorem plus two mechanized
  counterexamples, one realistic `to_local > to_remote` case and one
  unsorted-HTLC case);
* a complete characterization of *when* the model's fixed order happens to
  be value-ordered (no anchors: `to_local ≤ to_remote ≤ every HTLC value`
  and the HTLC list itself non-decreasing);
* the precise failure with anchors: value ordering would force every
  non-anchor output to be at most 330 sat (the anchor value) — i.e. only
  dust-sized outputs, incompatible with a funded channel;
* an unconditional, BOLT 3-shaped positive result: a value-sorted
  permutation of the model's outputs exists and can be produced by
  `List.mergeSort`; it is a permutation of `commitmentOutputs` and is
  value-ordered.  This is the strongest form available without the missing
  script/cltv fields.

No `sorry`, no new axiom, no Mathlib.
-/

namespace LnLean.Proofs.WaveE.E48

open LnLean LnLean.Channel

set_option autoImplicit false

-- OBLIGATION: LN-WE-E48

/-! ## The value half of BOLT 3 output ordering -/

/-- A list of commitment outputs is value-ordered when values are
non-decreasing, i.e. `a` before `b` implies `value a ≤ value b`.  This is the
first key of the BOLT 3 ordering (whole satoshis, smallest first). -/
def ValueOrdered (l : List CommitmentOutput) : Prop :=
  l.Pairwise (fun a b => a.value ≤ b.value)

theorem waveE_e48_valueOrdered_nil : ValueOrdered [] := by
  simp [ValueOrdered]

theorem waveE_e48_valueOrdered_singleton (o : CommitmentOutput) :
    ValueOrdered [o] := by
  simp [ValueOrdered]

/-- Value ordering is preserved by taking a sublist. -/
theorem waveE_e48_valueOrdered_sublist {l l' : List CommitmentOutput}
    (h : List.Sublist l' l) (hv : ValueOrdered l) : ValueOrdered l' :=
  hv.sublist h

/-- Value ordering is preserved by mapping values: the value projection of a
value-ordered output list is a non-decreasing `Nat` list. -/
theorem waveE_e48_valueOrdered_map_value {l : List CommitmentOutput}
    (hv : ValueOrdered l) : (l.map CommitmentOutput.value).Pairwise (· ≤ ·) := by
  simpa [ValueOrdered] using hv.map CommitmentOutput.value (fun _ _ h => h)

/-! ## Decomposition of the model's output list

These are definitional equalities: they fix the exact order the model
implements (four fixed blocks, HTLCs in channel-list order, anchors last). -/

/-- The HTLC block of `commitmentOutputs`: the HTLC outputs in the order in
which the HTLCs appear in the commitment record. -/
def waveE_e48_htlcSegment (c : Commitment) : List CommitmentOutput :=
  c.htlcs.map (fun h => CommitmentOutput.htlc h.direction h.amountSat)

/-- The anchor block of `commitmentOutputs`. -/
def waveE_e48_anchorSegment (c : Commitment) : List CommitmentOutput :=
  if c.anchorOutputs then [CommitmentOutput.localAnchor,
                            CommitmentOutput.remoteAnchor] else []

/-- The model's output list, split into its four blocks. -/
theorem waveE_e48_commitmentOutputs_decompose (c : Commitment) :
    c.commitmentOutputs =
      (if c.toLocalSat = 0 then [] else [CommitmentOutput.toLocal c.toLocalSat]) ++
      (if c.toRemoteSat = 0 then [] else [CommitmentOutput.toRemote c.toRemoteSat]) ++
      waveE_e48_htlcSegment c ++
      waveE_e48_anchorSegment c := rfl

/-- The HTLC block is exactly the map of the channel's HTLC list, so the
model preserves the channel (update) order and performs no sort. -/
theorem waveE_e48_htlcSegment_eq (c : Commitment) :
    waveE_e48_htlcSegment c = c.htlcs.map (fun h => CommitmentOutput.htlc h.direction h.amountSat) := rfl

/-- The values in the HTLC block are exactly the HTLC satoshi amounts, in the
same order. -/
theorem waveE_e48_htlcSegment_values (c : Commitment) :
    ((waveE_e48_htlcSegment c).map CommitmentOutput.value) =
      c.htlcs.map (fun h => h.amountSat) :=
  LnLean.Channel.map_htlcOutput_value c

/-- With both `to_local` and `to_remote` present, the model's list starts
with those two outputs, in that order, followed by the HTLC and anchor
blocks. -/
theorem waveE_e48_commitmentOutputs_cons (c : Commitment)
    (hl : c.toLocalSat ≠ 0) (hr : c.toRemoteSat ≠ 0) :
    c.commitmentOutputs =
      CommitmentOutput.toLocal c.toLocalSat ::
      CommitmentOutput.toRemote c.toRemoteSat ::
      (waveE_e48_htlcSegment c ++ waveE_e48_anchorSegment c) := by
  rw [waveE_e48_commitmentOutputs_decompose]
  simp [hl, hr]

/-- The anchors, when present, are the final two outputs. -/
theorem waveE_e48_anchors_suffix (c : Commitment) (ha : c.anchorOutputs = true) :
    ∃ pre : List CommitmentOutput,
      c.commitmentOutputs =
        pre ++ [CommitmentOutput.localAnchor, CommitmentOutput.remoteAnchor] := by
  refine ⟨(if c.toLocalSat = 0 then [] else [CommitmentOutput.toLocal c.toLocalSat]) ++
      (if c.toRemoteSat = 0 then [] else [CommitmentOutput.toRemote c.toRemoteSat]) ++
      waveE_e48_htlcSegment c, ?_⟩
  simp [waveE_e48_commitmentOutputs_decompose, waveE_e48_anchorSegment, ha,
    List.append_assoc]

/-! ## The model's fixed order is not value-ordered

These are the negative results: the parent claim read as a statement about
`commitmentOutputs` itself is false. -/

/-- If both commitment outputs are present and `to_local` is worth more than
`to_remote`, the model's output list violates value ordering. -/
theorem waveE_e48_not_valueOrdered_of_toLocal_gt_toRemote
    (c : Commitment) (hl : c.toLocalSat ≠ 0) (hr : c.toRemoteSat ≠ 0)
    (h : c.toRemoteSat < c.toLocalSat) :
    ¬ ValueOrdered c.commitmentOutputs := by
  intro hv
  unfold ValueOrdered at hv
  rw [waveE_e48_commitmentOutputs_cons c hl hr, List.pairwise_cons,
    List.pairwise_cons] at hv
  have hle : c.toLocalSat ≤ c.toRemoteSat :=
    hv.1 (CommitmentOutput.toRemote c.toRemoteSat) (by simp)
  omega

/-- A realistic commitment: a funded local side larger than the remote side.
Its model output list is `[to_local 1000, to_remote 500]`, which is not
value-ordered, although it is a perfectly well-formed commitment record. -/
def waveE_e48_counterexample_balances : Commitment :=
  { holder := .local
    commitmentNumber := 0
    fundingValueSat := 1500
    toLocalSat := 1000
    toRemoteSat := 500
    htlcs := []
    feeSat := 0
    contestDelay := 144
    anchorOutputs := false }

theorem waveE_e48_counterexample_balances_outputs :
    waveE_e48_counterexample_balances.commitmentOutputs =
      [CommitmentOutput.toLocal 1000, CommitmentOutput.toRemote 500] := by
  decide

theorem waveE_e48_counterexample_balances_not_valueOrdered :
    ¬ ValueOrdered waveE_e48_counterexample_balances.commitmentOutputs := by
  rw [waveE_e48_counterexample_balances_outputs]
  unfold ValueOrdered
  simp [List.pairwise_cons, CommitmentOutput.value]

/-- A commitment with two untrimmed HTLCs in the order `1000, 500`: the model
emits the HTLC outputs in channel-list order, so the list is not
value-ordered even when the two balance outputs are absent. -/
def waveE_e48_counterexample_htlc_order : Commitment :=
  { holder := .local
    commitmentNumber := 0
    fundingValueSat := 1500
    toLocalSat := 0
    toRemoteSat := 0
    htlcs :=
      [ { direction := .local, amountSat := 1000, cltvExpiry := 100,
          state := .offered }
      , { direction := .remote, amountSat := 500, cltvExpiry := 101,
          state := .received } ]
    feeSat := 0
    contestDelay := 144
    anchorOutputs := false }

theorem waveE_e48_counterexample_htlc_order_outputs :
    waveE_e48_counterexample_htlc_order.commitmentOutputs =
      [CommitmentOutput.htlc .local 1000, CommitmentOutput.htlc .remote 500] := by
  decide

theorem waveE_e48_counterexample_htlc_order_not_valueOrdered :
    ¬ ValueOrdered waveE_e48_counterexample_htlc_order.commitmentOutputs := by
  rw [waveE_e48_counterexample_htlc_order_outputs]
  unfold ValueOrdered
  simp [List.pairwise_cons, CommitmentOutput.value]

/-- With anchors on, value ordering of the model's list caps every non-anchor
output at the anchor value (330 sat), because the anchors are emitted last.
This is the general negative result behind the balance counterexample. -/
theorem waveE_e48_valueOrdered_before_anchor
    (c : Commitment) (ha : c.anchorOutputs = true)
    (hv : ValueOrdered c.commitmentOutputs) (o : CommitmentOutput)
    (ho : o ∈ (if c.toLocalSat = 0 then [] else
          [CommitmentOutput.toLocal c.toLocalSat]) ++
        (if c.toRemoteSat = 0 then [] else
          [CommitmentOutput.toRemote c.toRemoteSat]) ++
        waveE_e48_htlcSegment c) :
    o.value ≤ 330 := by
  have hd : c.commitmentOutputs =
      ((if c.toLocalSat = 0 then [] else
          [CommitmentOutput.toLocal c.toLocalSat]) ++
        (if c.toRemoteSat = 0 then [] else
          [CommitmentOutput.toRemote c.toRemoteSat]) ++
        waveE_e48_htlcSegment c) ++
      [CommitmentOutput.localAnchor, CommitmentOutput.remoteAnchor] := by
    simp [waveE_e48_commitmentOutputs_decompose, waveE_e48_anchorSegment, ha,
      List.append_assoc]
  have hv' : (((if c.toLocalSat = 0 then [] else
          [CommitmentOutput.toLocal c.toLocalSat]) ++
        (if c.toRemoteSat = 0 then [] else
          [CommitmentOutput.toRemote c.toRemoteSat]) ++
        waveE_e48_htlcSegment c) ++
      [CommitmentOutput.localAnchor, CommitmentOutput.remoteAnchor]).Pairwise
        (fun a b => a.value ≤ b.value) := by
    rw [← hd]
    exact hv
  obtain ⟨_, _, hcross⟩ := List.pairwise_append.mp hv'
  have := hcross o ho CommitmentOutput.localAnchor (by simp)
  simpa [CommitmentOutput.value, anchorOutputSat] using this

/-- With anchors, a present `to_remote` is capped at 330 sat by value
ordering of the model's fixed order. -/
theorem waveE_e48_valueOrdered_toRemote_le_anchor
    (c : Commitment) (hr : c.toRemoteSat ≠ 0) (ha : c.anchorOutputs = true)
    (hv : ValueOrdered c.commitmentOutputs) : c.toRemoteSat ≤ 330 := by
  have ho : CommitmentOutput.toRemote c.toRemoteSat ∈
      (if c.toLocalSat = 0 then [] else
          [CommitmentOutput.toLocal c.toLocalSat]) ++
        (if c.toRemoteSat = 0 then [] else
          [CommitmentOutput.toRemote c.toRemoteSat]) ++
        waveE_e48_htlcSegment c := by
    simp [hr]
  have := waveE_e48_valueOrdered_before_anchor c ha hv
    (CommitmentOutput.toRemote c.toRemoteSat) ho
  simpa [CommitmentOutput.value] using this

/-- With anchors, every untrimmed HTLC output is capped at 330 sat by value
ordering of the model's fixed order. -/
theorem waveE_e48_valueOrdered_htlc_le_anchor
    (c : Commitment) (ha : c.anchorOutputs = true)
    (hv : ValueOrdered c.commitmentOutputs) :
    ∀ v ∈ c.htlcs.map (fun h => h.amountSat), v ≤ 330 := by
  intro v hvmem
  obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hvmem
  have ho : CommitmentOutput.htlc h.direction h.amountSat ∈
      (if c.toLocalSat = 0 then [] else
          [CommitmentOutput.toLocal c.toLocalSat]) ++
        (if c.toRemoteSat = 0 then [] else
          [CommitmentOutput.toRemote c.toRemoteSat]) ++
        waveE_e48_htlcSegment c := by
    exact List.mem_append_right _ (List.mem_map.mpr ⟨h, hh, rfl⟩)
  have := waveE_e48_valueOrdered_before_anchor c ha hv
    (CommitmentOutput.htlc h.direction h.amountSat) ho
  simpa [CommitmentOutput.value] using this

/-- Anchored counterexample: a present `to_remote` of 5000 sat makes the
model's output list non-value-ordered as soon as anchors are emitted. -/
theorem waveE_e48_not_valueOrdered_of_anchor_lt_toRemote
    (c : Commitment) (hr : c.toRemoteSat ≠ 0) (ha : c.anchorOutputs = true)
    (h : 330 < c.toRemoteSat) :
    ¬ ValueOrdered c.commitmentOutputs := by
  intro hv
  have := waveE_e48_valueOrdered_toRemote_le_anchor c hr ha hv
  omega

/-! ## Exactly when the model's fixed order is value-ordered -/

/-- Forward direction: value ordering forces `to_local ≤ to_remote`. -/
theorem waveE_e48_valueOrdered_toLocal_le_toRemote
    (c : Commitment) (hl : c.toLocalSat ≠ 0) (hr : c.toRemoteSat ≠ 0)
    (hv : ValueOrdered c.commitmentOutputs) : c.toLocalSat ≤ c.toRemoteSat := by
  unfold ValueOrdered at hv
  rw [waveE_e48_commitmentOutputs_cons c hl hr, List.pairwise_cons,
    List.pairwise_cons] at hv
  have := hv.1 (CommitmentOutput.toRemote c.toRemoteSat) (by simp)
  simpa [CommitmentOutput.value] using this

/-- Forward direction: value ordering forces `to_remote ≤` every HTLC amount,
because the HTLC block follows `to_remote`. -/
theorem waveE_e48_valueOrdered_toRemote_le_htlc
    (c : Commitment) (hl : c.toLocalSat ≠ 0) (hr : c.toRemoteSat ≠ 0)
    (hv : ValueOrdered c.commitmentOutputs) :
    ∀ v ∈ c.htlcs.map (fun h => h.amountSat), c.toRemoteSat ≤ v := by
  unfold ValueOrdered at hv
  rw [waveE_e48_commitmentOutputs_cons c hl hr, List.pairwise_cons,
    List.pairwise_cons] at hv
  intro v hvmem
  obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hvmem
  have hmem : CommitmentOutput.htlc h.direction h.amountSat ∈
      waveE_e48_htlcSegment c ++ waveE_e48_anchorSegment c :=
    List.mem_append_left _ (List.mem_map.mpr ⟨h, hh, rfl⟩)
  have := hv.2.1 (CommitmentOutput.htlc h.direction h.amountSat) hmem
  simpa [CommitmentOutput.value] using this

/-- Forward direction: value ordering forces the HTLC amounts, in channel
order, to be non-decreasing. -/
theorem waveE_e48_valueOrdered_htlc_pairwise
    (c : Commitment) (hl : c.toLocalSat ≠ 0) (hr : c.toRemoteSat ≠ 0)
    (hv : ValueOrdered c.commitmentOutputs) :
    c.htlcs.Pairwise (fun a b => a.amountSat ≤ b.amountSat) := by
  unfold ValueOrdered at hv
  rw [waveE_e48_commitmentOutputs_cons c hl hr, List.pairwise_cons,
    List.pairwise_cons] at hv
  have hH : (waveE_e48_htlcSegment c ++ waveE_e48_anchorSegment c).Pairwise
      (fun a b : CommitmentOutput => a.value ≤ b.value) := hv.2.2
  have hH' : (waveE_e48_htlcSegment c).Pairwise
      (fun a b : CommitmentOutput => a.value ≤ b.value) :=
    (List.pairwise_append.mp hH).1
  simpa [waveE_e48_htlcSegment, CommitmentOutput.value] using
    (List.pairwise_map.mp hH')

/-- Reverse direction: the three value conditions are enough to make the
model's own (unsorted) output list value-ordered, provided no anchors are
emitted. -/
theorem waveE_e48_valueOrdered_of_model_order
    (c : Commitment) (hl : c.toLocalSat ≠ 0) (hr : c.toRemoteSat ≠ 0)
    (ha : c.anchorOutputs = false)
    (h1 : c.toLocalSat ≤ c.toRemoteSat)
    (h2 : ∀ v ∈ c.htlcs.map (fun h => h.amountSat), c.toRemoteSat ≤ v)
    (h3 : c.htlcs.Pairwise (fun a b => a.amountSat ≤ b.amountSat)) :
    ValueOrdered c.commitmentOutputs := by
  rw [waveE_e48_commitmentOutputs_cons c hl hr]
  unfold ValueOrdered
  have ha' : waveE_e48_anchorSegment c = [] := by
    simp [waveE_e48_anchorSegment, ha]
  rw [ha', List.append_nil]
  have hH : (waveE_e48_htlcSegment c).Pairwise
      (fun a b : CommitmentOutput => a.value ≤ b.value) := by
    unfold waveE_e48_htlcSegment
    exact List.pairwise_map.mpr (by simpa [CommitmentOutput.value] using h3)
  refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ hH)
  · intro a' ha'
    rcases List.mem_cons.mp ha' with rfl | hmem
    · simpa [CommitmentOutput.value] using h1
    · obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hmem
      have := h2 h.amountSat (List.mem_map.mpr ⟨h, hh, rfl⟩)
      have := Nat.le_trans h1 this
      simpa [CommitmentOutput.value] using this
  · intro a' ha'
    obtain ⟨h, hh, rfl⟩ := List.mem_map.mp ha'
    have := h2 h.amountSat (List.mem_map.mpr ⟨h, hh, rfl⟩)
    simpa [CommitmentOutput.value] using this

/-- Complete characterization (no anchors): the model's fixed order
`to_local, to_remote, HTLCs in channel order` is value-ordered **iff**
`to_local ≤ to_remote ≤` every HTLC amount and the HTLC amounts are
non-decreasing in channel order. -/
theorem waveE_e48_valueOrdered_iff_model_order
    (c : Commitment) (hl : c.toLocalSat ≠ 0) (hr : c.toRemoteSat ≠ 0)
    (ha : c.anchorOutputs = false) :
    ValueOrdered c.commitmentOutputs ↔
      c.toLocalSat ≤ c.toRemoteSat ∧
      (∀ v ∈ c.htlcs.map (fun h => h.amountSat), c.toRemoteSat ≤ v) ∧
      c.htlcs.Pairwise (fun a b => a.amountSat ≤ b.amountSat) := by
  constructor
  · intro hv
    exact ⟨waveE_e48_valueOrdered_toLocal_le_toRemote c hl hr hv,
      waveE_e48_valueOrdered_toRemote_le_htlc c hl hr hv,
      waveE_e48_valueOrdered_htlc_pairwise c hl hr hv⟩
  · rintro ⟨h1, h2, h3⟩
    exact waveE_e48_valueOrdered_of_model_order c hl hr ha h1 h2 h3

/-! ## The positive, BOLT 3-shaped result: a value-sorted view exists

The model never builds the sorted transaction, but sorting its output list by
value is unconditional, is a permutation of the original list, and yields a
value-ordered list.  The script and `cltv_expiry` tie-breaks of BOLT 3 are
not modelled, so this is exactly the value half of the rule. -/

/-- The BOLT 3 value comparison, as a `Bool` (whole satoshis, smallest
first). -/
def waveE_e48_valueLe (a b : CommitmentOutput) : Bool :=
  decide (a.value ≤ b.value)

theorem waveE_e48_valueLe_trans (a b c : CommitmentOutput)
    (hab : waveE_e48_valueLe a b = true)
    (hbc : waveE_e48_valueLe b c = true) :
    waveE_e48_valueLe a c = true := by
  simp only [waveE_e48_valueLe, decide_eq_true_eq] at hab hbc ⊢
  exact Nat.le_trans hab hbc

theorem waveE_e48_valueLe_total (a b : CommitmentOutput) :
    (waveE_e48_valueLe a b || waveE_e48_valueLe b a) = true := by
  by_cases h : a.value ≤ b.value
  · simp [waveE_e48_valueLe, h]
  · have h' : b.value ≤ a.value := Nat.le_of_not_le h
    simp [waveE_e48_valueLe, h, h']

/-- Sort the model's output list by the BOLT 3 value key (smallest first). -/
def waveE_e48_valueSortedOutputs (c : Commitment) : List CommitmentOutput :=
  c.commitmentOutputs.mergeSort waveE_e48_valueLe

theorem waveE_e48_valueSortedOutputs_perm (c : Commitment) :
    (waveE_e48_valueSortedOutputs c).Perm c.commitmentOutputs :=
  List.mergeSort_perm _ _

theorem waveE_e48_valueSortedOutputs_ordered (c : Commitment) :
    ValueOrdered (waveE_e48_valueSortedOutputs c) := by
  unfold ValueOrdered waveE_e48_valueSortedOutputs
  exact (List.pairwise_mergeSort waveE_e48_valueLe_trans waveE_e48_valueLe_total
    c.commitmentOutputs).imp (fun {_ _} h => by
      simpa [waveE_e48_valueLe, decide_eq_true_eq] using h)

/-- Unconditional existence: every commitment's model output list has a
value-ordered permutation, witnessed explicitly by
`waveE_e48_valueSortedOutputs`. -/
theorem waveE_e48_exists_valueOrdered_perm (c : Commitment) :
    ∃ l : List CommitmentOutput, l.Perm c.commitmentOutputs ∧ ValueOrdered l :=
  ⟨waveE_e48_valueSortedOutputs c,
    waveE_e48_valueSortedOutputs_perm c,
    waveE_e48_valueSortedOutputs_ordered c⟩

/-- The sorted view preserves the total value of the model's outputs (sorting
is a permutation, so in particular membership and counts are unchanged). -/
theorem waveE_e48_valueSortedOutputs_mem_iff (c : Commitment)
    (o : CommitmentOutput) :
    o ∈ waveE_e48_valueSortedOutputs c ↔ o ∈ c.commitmentOutputs :=
  (waveE_e48_valueSortedOutputs_perm c).mem_iff

end LnLean.Proofs.WaveE.E48
