import LnLean.Channel.Commitment
import LnLean.Channel.Fee
import LnLean.Channel.HTLC
import LnLean.Channel.HTLCLaws
import LnLean.Channel.Laws
import LnLean.Channel.Penalty
import LnLean.Channel.Revocation
import LnLean.Channel.State
import LnLean.Channel.Types

/-!
# LnLean.Proofs.WaveD.D12

Catalog obligation `LN-CH-003`: *commitment outputs are ordered by value then
script, and dust HTLCs are trimmed* (BOLT 3 §Transaction Output Ordering and
§Trimmed Outputs; LDK `lightning/src/ln/chan_utils.rs:1985`).

## What the model actually provides

`LnLean.Channel.Commitment.commitmentOutputs` emits output groups in the fixed
order

`to_local, to_remote, HTLC outputs in input order, local_anchor, remote_anchor`

and trims only zero-valued `to_local`/`to_remote` outputs.  It does **not**
sort, and `LnLean.Channel.CommitmentOutput` carries neither a `scriptPubKey`
nor the HTLC `cltvExpiry`, so the BOLT key `(value, script, cltv_expiry)` is not
representable on the model's output type.  The ordering half of `LN-CH-003` is
therefore false of the model as written, not merely unproved.  The file proves
the mechanized counterexample `waveD_d12_commitmentOutputs_not_value_sorted`
and the information-loss result `waveD_d12_cltv_tiebreak_not_recoverable`.

The dust half is represented in two places: `isDustHTLC` in
`LnLean.Channel.HTLC` implements BOLT 3's `amount - second_stage_fee <
dust_limit_satoshis` test, while `commitmentOutputs` itself has no dust filter.
`waveD_d12_zero_value_htlc_emitted` shows that a zero-valued HTLC output is
still emitted, so the fixing is a separate filter.  The positive lemmas below
define that filter over `HTLCRecord`s and prove that a record's output is
present exactly when the record is not dust
(`waveD_d12_htlc_output_present_iff`), that no dust output and no sub-limit
output is ever emitted (`waveD_d12_dust_output_absent`,
`waveD_d12_htlcOutput_value_ge_dust`), and that the construction refines
`commitmentOutputs` (`waveD_d12_trimHTLCs_outputs`).

The strongest true conditional ordering statement is
`waveD_d12_output_ordering_conditional`: once each output is externally tagged
with its BOLT key (value, script rank, CLTV), a `mergeSort` by that key
permutes the list and satisfies all three comparison criteria.  The external
tag is exactly the missing model data; `scriptRank` stands for the position of
the output's `scriptPubKey` in BOLT's memcmp order, and the model's
`Commitment.commitmentOutputs` cannot supply it.

BOLT anchors.
* BOLT 3 §Transaction Output Ordering (`refs/bolts/03-transactions.md:54-67`):
  ascending value (whole satoshis, ignoring the msat part of HTLCs), then
  `scriptpubkey` by common-prefix memcmp with shorter first, then increasing
  `cltv_expiry` for HTLC outputs.
* BOLT 3 §Trimmed Outputs (`refs/bolts/03-transactions.md:305-354`): an HTLC
  output is omitted iff `amount - second_stage_fee < dust_limit_satoshis`.
* LDK `lightning/src/ln/chan_utils.rs:1757-1770` (`is_left_greater`) and
  `:1985-2020` (`build_sorted_htlc_outputs`): HTLC outputs sorted by value,
  then script, then expiry (with an extra `payment_hash` fallback used only
  for fuzz-mode determinism); non-HTLC outputs are inserted by value then
  script in `build_outputs_and_htlcs` (`:1835-1885`).  The Lean key below
  models BOLT's three keys; the fuzz-only hash fallback is omitted.
-/

namespace LnLean.Proofs.WaveD.D12

set_option autoImplicit false

open LnLean LnLean.Channel

/-! ## 1.  The model's output list is not value-ordered -/

/-- A legal commitment record whose two non-anchor output values are 500 and
200 satoshis, in the fixed `to_local, to_remote` group order. -/
def unsortedCommitment : Commitment :=
  { holder := .local
    commitmentNumber := 0
    fundingValueSat := 700
    toLocalSat := 500
    toRemoteSat := 200
    htlcs := []
    feeSat := 0
    contestDelay := 0
    anchorOutputs := false }

/-- **Counterexample to the ordering half.**  `commitmentOutputs` emits
`to_local` before `to_remote`, so a larger `to_local` precedes a smaller
`to_remote`; the emitted value list is `[500, 200]`, not nondecreasing. -/
theorem waveD_d12_commitmentOutputs_not_value_sorted :
    ¬ (unsortedCommitment.commitmentOutputs.map CommitmentOutput.value).Pairwise
        (· ≤ ·) := by
  simp [unsortedCommitment, Commitment.commitmentOutputs, CommitmentOutput.value]

/-- The unconditional ordering claim fails: there is a commitment whose
emitted output values are not sorted ascending. -/
theorem waveD_d12_output_ordering_fails :
    ¬ (∀ c : Commitment,
        (c.commitmentOutputs.map CommitmentOutput.value).Pairwise (· ≤ ·)) := by
  intro h
  exact waveD_d12_commitmentOutputs_not_value_sorted (h unsortedCommitment)

/-- Concrete form of the counterexample: a legal commitment whose output
values are not nondecreasing. -/
theorem waveD_d12_exists_unsorted_commitment :
    ∃ c : Commitment,
      ¬ (c.commitmentOutputs.map CommitmentOutput.value).Pairwise (· ≤ ·) :=
  ⟨unsortedCommitment, waveD_d12_commitmentOutputs_not_value_sorted⟩

/-! ### The CLTV tiebreak is erased by `CommitmentOutput` -/

/-- An HTLC output with a chosen direction, value, expiry, and lifecycle
state. -/
def mkHtlcOutput (dir : Direction) (amountSat : Nat) (cltv : Height)
    (state : HTLCState) : CommitmentHTLCOutput :=
  { direction := dir, amountSat := amountSat, cltvExpiry := cltv, state := state }

/-- Two commitments that differ only in the *order and expiry* of two
same-value HTLC outputs. -/
def cltvOrderLeft : Commitment :=
  { holder := .local
    commitmentNumber := 0
    fundingValueSat := 2000
    toLocalSat := 0
    toRemoteSat := 0
    htlcs := [mkHtlcOutput .local 1000 10 .offered,
              mkHtlcOutput .local 1000 20 .offered]
    feeSat := 0
    contestDelay := 0
    anchorOutputs := false }

def cltvOrderRight : Commitment :=
  { cltvOrderLeft with
    htlcs := [mkHtlcOutput .local 1000 20 .offered,
              mkHtlcOutput .local 1000 10 .offered] }

/-- **Information loss.**  BOLT 3 orders equal-value equal-script HTLCs by
increasing `cltv_expiry`, but `CommitmentOutput.htlc` records only direction
and value.  These two commitments have different HTLC expiry orders yet the
same `commitmentOutputs`, so no function of the model's output list can
recover the CLTV tiebreak. -/
theorem waveD_d12_cltv_tiebreak_not_recoverable :
    cltvOrderLeft.htlcs ≠ cltvOrderRight.htlcs ∧
      cltvOrderLeft.commitmentOutputs = cltvOrderRight.commitmentOutputs := by
  constructor
  · decide
  · rfl

/-! ## 2.  A BOLT-3 sort key and the conditional ordering theorem -/

/-- The BOLT 3 output-ordering key.  `scriptRank` is a stand-in for the
position of the output's `scriptPubKey` in BOLT's common-prefix memcmp order
(the model has no script bytes on `CommitmentOutput`); `cltvExpiry` is `0` for
non-HTLC outputs, which is harmless because the CLTV component is only
consulted when value and script rank are equal. -/
structure OutputSortKey where
  valueSat : Nat
  scriptRank : Nat
  cltvExpiry : Nat
deriving Repr, DecidableEq, BEq

/-- Lexicographic BOLT order: value, then script, then CLTV expiry. -/
def OutputSortKey.Le (a b : OutputSortKey) : Prop :=
  a.valueSat < b.valueSat ∨
    (a.valueSat = b.valueSat ∧
      (a.scriptRank < b.scriptRank ∨
        (a.scriptRank = b.scriptRank ∧ a.cltvExpiry ≤ b.cltvExpiry)))

instance : DecidableRel OutputSortKey.Le := fun a b => by
  unfold OutputSortKey.Le
  infer_instance

theorem OutputSortKey.le_refl (a : OutputSortKey) : a.Le a := by
  unfold OutputSortKey.Le
  omega

theorem OutputSortKey.le_trans {a b c : OutputSortKey} (hab : a.Le b)
    (hbc : b.Le c) : a.Le c := by
  unfold OutputSortKey.Le at *
  omega

theorem OutputSortKey.le_total (a b : OutputSortKey) : a.Le b ∨ b.Le a := by
  unfold OutputSortKey.Le
  omega

/-- The value component is the primary key. -/
theorem OutputSortKey.value_le_of_le {a b : OutputSortKey} (h : a.Le b) :
    a.valueSat ≤ b.valueSat := by
  unfold OutputSortKey.Le at h
  omega

/-- On equal value, the script component is the secondary key. -/
theorem OutputSortKey.scriptRank_le_of_le {a b : OutputSortKey} (h : a.Le b)
    (hv : a.valueSat = b.valueSat) : a.scriptRank ≤ b.scriptRank := by
  unfold OutputSortKey.Le at h
  omega

/-- On equal value and equal script, CLTV expiry is the tertiary key. -/
theorem OutputSortKey.cltv_le_of_le {a b : OutputSortKey} (h : a.Le b)
    (hv : a.valueSat = b.valueSat) (hs : a.scriptRank = b.scriptRank) :
    a.cltvExpiry ≤ b.cltvExpiry := by
  unfold OutputSortKey.Le at h
  omega

/-- Sort a commitment-output list by externally supplied BOLT keys.  This is
the repaired construction: `Commitment.commitmentOutputs` itself does not
sort. -/
def sortByKey (key : CommitmentOutput → OutputSortKey)
    (l : List CommitmentOutput) : List CommitmentOutput :=
  l.mergeSort (fun a b => decide (OutputSortKey.Le (key a) (key b)))

theorem sortByKey_perm (key : CommitmentOutput → OutputSortKey)
    (l : List CommitmentOutput) : (sortByKey key l).Perm l :=
  List.mergeSort_perm l _

theorem sortByKey_pairwise (key : CommitmentOutput → OutputSortKey)
    (l : List CommitmentOutput) :
    (sortByKey key l).Pairwise (fun a b => OutputSortKey.Le (key a) (key b)) := by
  have h := List.pairwise_mergeSort
    (le := fun a b => decide (OutputSortKey.Le (key a) (key b)))
    (by
      intro a b c hab hbc
      exact decide_eq_true
        (OutputSortKey.le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc)))
    (by
      intro a b
      by_cases hab : OutputSortKey.Le (key a) (key b)
      · simp [decide_eq_true hab]
      · rcases OutputSortKey.le_total (key a) (key b) with h | h
        · exact absurd h hab
        · simp [decide_eq_false hab, decide_eq_true h])
    l
  exact h.imp (fun {a b} hab => of_decide_eq_true hab)

/-- The sorted list satisfies all three BOLT criteria pairwise: value is
nondecreasing; on equal value, script rank is nondecreasing; and on equal
value and script, CLTV expiry is nondecreasing. -/
theorem sortByKey_pairwise_components (key : CommitmentOutput → OutputSortKey)
    (l : List CommitmentOutput) :
    (sortByKey key l).Pairwise (fun a b =>
      (key a).valueSat ≤ (key b).valueSat ∧
        ((key a).valueSat = (key b).valueSat →
          (key a).scriptRank ≤ (key b).scriptRank) ∧
        ((key a).valueSat = (key b).valueSat →
          (key a).scriptRank = (key b).scriptRank →
            (key a).cltvExpiry ≤ (key b).cltvExpiry)) := by
  refine (sortByKey_pairwise key l).imp ?_
  intro a b hab
  exact ⟨OutputSortKey.value_le_of_le hab,
    fun hv => OutputSortKey.scriptRank_le_of_le hab hv,
    fun hv hs => OutputSortKey.cltv_le_of_le hab hv hs⟩

/-- Value component of the conditional ordering theorem. -/
theorem sortByKey_values_sorted (key : CommitmentOutput → OutputSortKey)
    (hval : ∀ o : CommitmentOutput, (key o).valueSat = o.value)
    (l : List CommitmentOutput) :
    ((sortByKey key l).map CommitmentOutput.value).Pairwise (· ≤ ·) := by
  rw [List.pairwise_map]
  refine (sortByKey_pairwise key l).imp ?_
  intro a b hab
  have h := OutputSortKey.value_le_of_le hab
  simpa [hval a, hval b] using h

/-- **Conditional ordering theorem.**  If every output is tagged with its BOLT
key and the value component of the tag is the output's satoshi value, then
`sortByKey` returns a permutation of the list whose values are nondecreasing
and whose equal-value prefixes are ordered by script rank and then CLTV.  The
tag `key` is exactly the data the model lacks: `CommitmentOutput` has no
script bytes and no HTLC expiry. -/
theorem waveD_d12_output_ordering_conditional
    (key : CommitmentOutput → OutputSortKey)
    (hval : ∀ o : CommitmentOutput, (key o).valueSat = o.value)
    (l : List CommitmentOutput) :
    (sortByKey key l).Perm l ∧
      (sortByKey key l).Pairwise (fun a b => OutputSortKey.Le (key a) (key b)) ∧
      ((sortByKey key l).map CommitmentOutput.value).Pairwise (· ≤ ·) := by
  exact ⟨sortByKey_perm key l, sortByKey_pairwise key l,
    sortByKey_values_sorted key hval l⟩

/-! ### Value-only sorting of an existing output list -/

/-- Sort an output list by satoshi value alone. -/
def sortByValue (l : List CommitmentOutput) : List CommitmentOutput :=
  l.mergeSort (fun a b => decide (a.value ≤ b.value))

theorem sortByValue_perm (l : List CommitmentOutput) : (sortByValue l).Perm l :=
  List.mergeSort_perm l _

/-- The value-only repair of any output list, including
`Commitment.commitmentOutputs`, is nondecreasing in value. -/
theorem sortByValue_sorted (l : List CommitmentOutput) :
    (sortByValue l).Pairwise (fun a b => a.value ≤ b.value) := by
  have h := List.pairwise_mergeSort
    (le := fun a b => decide (a.value ≤ b.value))
    (by
      intro a b c hab hbc
      exact decide_eq_true
        (Nat.le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc)))
    (by
      intro a b
      by_cases hab : a.value ≤ b.value
      · simp [decide_eq_true hab]
      · rcases Nat.le_total a.value b.value with h | h
        · exact absurd h hab
        · simp [decide_eq_false hab, decide_eq_true h])
    l
  exact h.imp (fun {a b} hab => of_decide_eq_true hab)

/-- The repaired list's value sequence is nondecreasing. -/
theorem sortByValue_values_sorted (l : List CommitmentOutput) :
    ((sortByValue l).map CommitmentOutput.value).Pairwise (· ≤ ·) := by
  rw [List.pairwise_map]
  exact sortByValue_sorted l

/-- Applying the value-only repair to a commitment's output list is a
value-sorted permutation of the model's fixed-order list. -/
theorem waveD_d12_commitmentOutputs_value_sort (c : Commitment) :
    (sortByValue c.commitmentOutputs).Perm c.commitmentOutputs ∧
      ((sortByValue c.commitmentOutputs).map CommitmentOutput.value).Pairwise
        (· ≤ ·) :=
  ⟨sortByValue_perm _, sortByValue_values_sorted _⟩

/-! ## 3.  Dust trimming of HTLC outputs -/

/-- Project an `HTLCRecord` onto the commitment-output record, charging the
direction-dependent second-stage fee exactly as BOLT 3 does. -/
def CommitmentHTLCOutput.ofRecord (timeoutFeeSat successFeeSat : Nat)
    (h : HTLCRecord) : CommitmentHTLCOutput :=
  { direction := h.direction
    amountSat := htlcOutputValue h timeoutFeeSat successFeeSat
    cltvExpiry := h.cltvExpiry
    state := h.state }

/-- The HTLC records that survive BOLT 3's dust test. -/
def survivingHTLCs (dustLimitSat timeoutFeeSat successFeeSat : Nat)
    (hs : List HTLCRecord) : List HTLCRecord :=
  hs.filter (fun h => hasOutput h dustLimitSat timeoutFeeSat successFeeSat)

/-- The HTLC group of a commitment output list after BOLT 3 trimming. -/
def htlcOutputsOf (dustLimitSat timeoutFeeSat successFeeSat : Nat)
    (hs : List HTLCRecord) : List CommitmentOutput :=
  (survivingHTLCs dustLimitSat timeoutFeeSat successFeeSat hs).map
    (fun h => CommitmentOutput.htlc h.direction
      (htlcOutputValue h timeoutFeeSat successFeeSat))

/-- Mapping the projected HTLC records back to `CommitmentOutput`s is the same
as mapping the surviving records directly with the second-stage-fee-adjusted
value. -/
theorem map_ofRecord_eq (timeoutFeeSat successFeeSat : Nat)
    (hs : List HTLCRecord) :
    (hs.map (CommitmentHTLCOutput.ofRecord timeoutFeeSat successFeeSat)).map
        (fun h => CommitmentOutput.htlc h.direction h.amountSat) =
      hs.map (fun h => CommitmentOutput.htlc h.direction
        (htlcOutputValue h timeoutFeeSat successFeeSat)) := by
  rw [List.map_map]
  rfl

/-- Replace a commitment's HTLC group by the trimmed projection of a record
list, leaving `to_local`, `to_remote`, and the anchors untouched. -/
def trimCommitmentHTLCs (c : Commitment) (dustLimitSat timeoutFeeSat
    successFeeSat : Nat) (hs : List HTLCRecord) : Commitment :=
  { c with
    htlcs := (survivingHTLCs dustLimitSat timeoutFeeSat successFeeSat hs).map
      (CommitmentHTLCOutput.ofRecord timeoutFeeSat successFeeSat) }

/-- Membership in the surviving set is exactly "present in the input and not
dust". -/
theorem waveD_d12_mem_survivingHTLCs {dustLimitSat timeoutFeeSat successFeeSat : Nat}
    {hs : List HTLCRecord} {h : HTLCRecord} :
    h ∈ survivingHTLCs dustLimitSat timeoutFeeSat successFeeSat hs ↔
      h ∈ hs ∧ hasOutput h dustLimitSat timeoutFeeSat successFeeSat = true := by
  simp [survivingHTLCs, List.mem_filter]

/-- A dust HTLC is trimmed: it is not in the surviving set. -/
theorem waveD_d12_dust_htlc_trimmed {dustLimitSat timeoutFeeSat successFeeSat : Nat}
    {hs : List HTLCRecord} {h : HTLCRecord}
    (hd : isDustHTLC h dustLimitSat timeoutFeeSat successFeeSat = true) :
    h ∉ survivingHTLCs dustLimitSat timeoutFeeSat successFeeSat hs := by
  simp [survivingHTLCs, List.mem_filter, hasOutput, hd]

/-- A non-dust HTLC is kept. -/
theorem waveD_d12_nonDust_htlc_kept {dustLimitSat timeoutFeeSat successFeeSat : Nat}
    {hs : List HTLCRecord} {h : HTLCRecord} (hmem : h ∈ hs)
    (hd : isDustHTLC h dustLimitSat timeoutFeeSat successFeeSat = false) :
    h ∈ survivingHTLCs dustLimitSat timeoutFeeSat successFeeSat hs := by
  simp [survivingHTLCs, List.mem_filter, hasOutput, hd, hmem]

/-- Every surviving HTLC's on-chain value is at least the dust limit. -/
theorem waveD_d12_surviving_value_ge_dust
    {dustLimitSat timeoutFeeSat successFeeSat : Nat} {hs : List HTLCRecord}
    {h : HTLCRecord}
    (hmem : h ∈ survivingHTLCs dustLimitSat timeoutFeeSat successFeeSat hs) :
    dustLimitSat ≤ htlcOutputValue h timeoutFeeSat successFeeSat := by
  have hout := (waveD_d12_mem_survivingHTLCs.1 hmem).2
  exact (hasOutput_iff h dustLimitSat timeoutFeeSat successFeeSat).1 hout

/-- Membership in the trimmed HTLC output group. -/
theorem waveD_d12_mem_htlcOutputsOf
    {dustLimitSat timeoutFeeSat successFeeSat : Nat} {hs : List HTLCRecord}
    {o : CommitmentOutput} :
    o ∈ htlcOutputsOf dustLimitSat timeoutFeeSat successFeeSat hs ↔
      ∃ h ∈ survivingHTLCs dustLimitSat timeoutFeeSat successFeeSat hs,
        CommitmentOutput.htlc h.direction
          (htlcOutputValue h timeoutFeeSat successFeeSat) = o := by
  simp [htlcOutputsOf, List.mem_map]

/-- **No dust output is generated.**  Every output in the trimmed HTLC group
has value at least `dust_limit_satoshis`. -/
theorem waveD_d12_htlcOutput_value_ge_dust
    {dustLimitSat timeoutFeeSat successFeeSat : Nat} {hs : List HTLCRecord}
    {o : CommitmentOutput}
    (ho : o ∈ htlcOutputsOf dustLimitSat timeoutFeeSat successFeeSat hs) :
    dustLimitSat ≤ o.value := by
  obtain ⟨h, hh, rfl⟩ := waveD_d12_mem_htlcOutputsOf.1 ho
  simpa [CommitmentOutput.value] using
    waveD_d12_surviving_value_ge_dust hh

/-- The trimmed HTLC group has exactly one output per surviving record. -/
theorem waveD_d12_htlcOutputsOf_length
    (dustLimitSat timeoutFeeSat successFeeSat : Nat) (hs : List HTLCRecord) :
    (htlcOutputsOf dustLimitSat timeoutFeeSat successFeeSat hs).length =
      (survivingHTLCs dustLimitSat timeoutFeeSat successFeeSat hs).length := by
  simp [htlcOutputsOf]

/-- A non-dust HTLC record in the input produces its output. -/
theorem waveD_d12_nonDust_output_mem
    {dustLimitSat timeoutFeeSat successFeeSat : Nat} {hs : List HTLCRecord}
    {h : HTLCRecord} (hmem : h ∈ hs)
    (hd : isDustHTLC h dustLimitSat timeoutFeeSat successFeeSat = false) :
    CommitmentOutput.htlc h.direction
        (htlcOutputValue h timeoutFeeSat successFeeSat) ∈
      htlcOutputsOf dustLimitSat timeoutFeeSat successFeeSat hs := by
  rw [waveD_d12_mem_htlcOutputsOf]
  exact ⟨h, waveD_d12_nonDust_htlc_kept hmem hd, rfl⟩

/-- **Exact per-HTLC trimming criterion.**  For an HTLC record present in the
input, BOLT 3's output is in the trimmed HTLC group exactly when the record is
not dust.  This is the "MUST NOT contain the dust output / otherwise MUST
generate it" pair from `03-transactions.md:333-346`, on the model's
`isDustHTLC` test. -/
theorem waveD_d12_htlc_output_present_iff
    {dustLimitSat timeoutFeeSat successFeeSat : Nat} {hs : List HTLCRecord}
    {h : HTLCRecord} (hmem : h ∈ hs) :
    CommitmentOutput.htlc h.direction
        (htlcOutputValue h timeoutFeeSat successFeeSat) ∈
      htlcOutputsOf dustLimitSat timeoutFeeSat successFeeSat hs ↔
        isDustHTLC h dustLimitSat timeoutFeeSat successFeeSat = false := by
  constructor
  · intro hout
    have hge := waveD_d12_htlcOutput_value_ge_dust hout
    change dustLimitSat ≤
      (CommitmentOutput.htlc h.direction
        (htlcOutputValue h timeoutFeeSat successFeeSat)).value at hge
    rw [CommitmentOutput.value] at hge
    cases hb : isDustHTLC h dustLimitSat timeoutFeeSat successFeeSat with
    | false => rfl
    | true =>
        exfalso
        have hlt := (isDust_iff h dustLimitSat timeoutFeeSat successFeeSat).1 hb
        omega
  · intro hd
    exact waveD_d12_nonDust_output_mem hmem hd

/-- A dust HTLC's output is absent from the trimmed group, even if another
record would project to the same direction and value. -/
theorem waveD_d12_dust_output_absent
    {dustLimitSat timeoutFeeSat successFeeSat : Nat} {hs : List HTLCRecord}
    {h : HTLCRecord}
    (hd : isDustHTLC h dustLimitSat timeoutFeeSat successFeeSat = true) :
    CommitmentOutput.htlc h.direction
        (htlcOutputValue h timeoutFeeSat successFeeSat) ∉
      htlcOutputsOf dustLimitSat timeoutFeeSat successFeeSat hs := by
  intro hout
  have hge := waveD_d12_htlcOutput_value_ge_dust hout
  change dustLimitSat ≤
    (CommitmentOutput.htlc h.direction
      (htlcOutputValue h timeoutFeeSat successFeeSat)).value at hge
  rw [CommitmentOutput.value] at hge
  have hlt := (isDust_iff h dustLimitSat timeoutFeeSat successFeeSat).1 hd
  omega

/-- The number of HTLC outputs equals the number of non-dust HTLC records. -/
theorem waveD_d12_htlcOutputsOf_length_eq_filter
    (dustLimitSat timeoutFeeSat successFeeSat : Nat) (hs : List HTLCRecord) :
    (htlcOutputsOf dustLimitSat timeoutFeeSat successFeeSat hs).length =
      (hs.filter (fun h =>
        hasOutput h dustLimitSat timeoutFeeSat successFeeSat)).length :=
  waveD_d12_htlcOutputsOf_length _ _ _ _

/-- The trimmed commitment's output list is the model's fixed group order with
the HTLC group replaced by `htlcOutputsOf`. -/
theorem waveD_d12_trimHTLCs_outputs
    (dustLimitSat timeoutFeeSat successFeeSat : Nat) (c : Commitment)
    (hs : List HTLCRecord) :
    (trimCommitmentHTLCs c dustLimitSat timeoutFeeSat successFeeSat hs).commitmentOutputs =
      (if c.toLocalSat = 0 then [] else
        [CommitmentOutput.toLocal c.toLocalSat]) ++
      (if c.toRemoteSat = 0 then [] else
        [CommitmentOutput.toRemote c.toRemoteSat]) ++
      htlcOutputsOf dustLimitSat timeoutFeeSat successFeeSat hs ++
      (if c.anchorOutputs then
        [CommitmentOutput.localAnchor, CommitmentOutput.remoteAnchor] else []) := by
  simp only [trimCommitmentHTLCs, Commitment.commitmentOutputs]
  rw [map_ofRecord_eq]
  simp only [htlcOutputsOf]
  rfl

/-! ### The model emits a zero-valued (dust) HTLC output -/

/-- A commitment with one zero-valued HTLC output. -/
def zeroValueHtlcCommitment : Commitment :=
  { holder := .local
    commitmentNumber := 0
    fundingValueSat := 1000
    toLocalSat := 1000
    toRemoteSat := 0
    htlcs := [mkHtlcOutput .local 0 0 .offered]
    feeSat := 0
    contestDelay := 0
    anchorOutputs := false }

/-- **Counterexample to unconditional dust trimming.**
`commitmentOutputs` emits the zero-valued HTLC output verbatim; no dust filter
is applied. -/
theorem waveD_d12_zero_value_htlc_emitted :
    CommitmentOutput.htlc .local 0 ∈ zeroValueHtlcCommitment.commitmentOutputs := by
  simp [zeroValueHtlcCommitment, Commitment.commitmentOutputs, mkHtlcOutput]

/-- The same zero-valued HTLC is dust under BOLT 3's test for every positive
dust limit and every second-stage fee: its output value is `0 - fee = 0`, which
is below the limit.  (The standard P2WPKH limit is
`DUST_LIMIT_P2WPKH = 546`.) -/
theorem waveD_d12_zero_value_htlc_is_dust (ph : PaymentHash)
    (dustLimitSat timeoutFeeSat successFeeSat : Nat) (hd : 0 < dustLimitSat) :
    isDustHTLC
      { id := 0, direction := .local, amountMsat := ⟨0⟩, paymentHash := ph,
        cltvExpiry := 0, state := .offered }
      dustLimitSat timeoutFeeSat successFeeSat = true := by
  simp [isDustHTLC, htlcOutputValue, Msat.toSatFloor, hd]

/-- Consequently, `commitmentOutputs` alone does not establish the dust half
of `LN-CH-003`; the separate `survivingHTLCs` filter is required. -/
theorem waveD_d12_dust_trimming_requires_filter :
    ∃ c : Commitment, ∃ h ∈ c.htlcs,
      h.amountSat = 0 ∧
        CommitmentOutput.htlc h.direction h.amountSat ∈ c.commitmentOutputs :=
  ⟨zeroValueHtlcCommitment, mkHtlcOutput .local 0 0 .offered,
    by simp [zeroValueHtlcCommitment], rfl,
    waveD_d12_zero_value_htlc_emitted⟩

/-! ## 4.  Obligation marker -/

-- OBLIGATION: LN-WD-D12
-- The catalog target `LnLean.Channel.Commitment.output_ordering` asserts
-- (a) BOLT 3 value/script/CLTV ordering of commitment outputs and
-- (b) trimming of dust HTLCs.
-- (a) is false of `Commitment.commitmentOutputs` as modelled (see
--     `waveD_d12_output_ordering_fails`) and its script/CLTV key is not
--     representable on `CommitmentOutput` (see
--     `waveD_d12_cltv_tiebreak_not_recoverable`); the conditional repair is
--     `waveD_d12_output_ordering_conditional`.
-- (b) holds for the `survivingHTLCs`/`htlcOutputsOf` construction over
--     `HTLCRecord` (see `waveD_d12_dust_htlc_trimmed`,
--     `waveD_d12_nonDust_htlc_kept`, `waveD_d12_htlcOutput_value_ge_dust`)
--     but not for `Commitment.commitmentOutputs` alone (see
--     `waveD_d12_dust_trimming_requires_filter`).

end LnLean.Proofs.WaveD.D12
