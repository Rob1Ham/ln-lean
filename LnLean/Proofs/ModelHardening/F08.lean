import LnLean.Channel.Commitment
import LnLean.Channel.HTLC
import LnLean.Channel.Types

/-!
# LnLean.Proofs.ModelHardening.F08

English claim.  BOLT 3 does not leave the order of a commitment
transaction's outputs free: after the output *set* has been computed (balances,
untrimmed HTLCs, anchors) the construction must

> Sort the outputs into BIP 69+CLTV order.

That order is the lexicographic order on the triple

1. output value in whole satoshis (the millisatoshi part of an HTLC is
   ignored),
2. `scriptpubkey` (common-prefix `memcmp`, shorter script first),
3. for HTLC outputs with equal value and equal script, increasing
   `cltv_expiry`.

`LnLean.Channel.Commitment.commitmentOutputs` instead emits the outputs in the
fixed document order `to_local, to_remote, HTLCs, anchors`, and its
`CommitmentOutput` type does not even carry the HTLC `cltv_expiry` that the
third key needs.  This module fills that gap:

* `OutputEntry` annotates a `CommitmentOutput` with its CLTV expiry, and
  `waveF_f08_commitmentOutputEntries` is the document order at that
  resolution (`waveF_f08_commitmentOutputEntries_map_output` recovers the
  existing `commitmentOutputs`).
* `OutputKey` and `OutputKey.lexLeProp` are the BOLT 3 value-then-script,
  then CLTV key.  Script bytes are not part of the model, so the predicate is
  parameterized by an abstract script rank `script : CommitmentOutput → Nat`;
  `waveF_f08_scriptRank` is a canonical kind-level instance (HTLC
  scripts of one direction share a rank, and the CLTV key orders them).
* `Bip69CltvSorted` is the sortedness predicate and `bip69Sort` is the
  construction that sorts the document entries with `List.mergeSort`.
  `bip69Sort_sorted` proves the construction satisfies the predicate for
  *every* script rank, and `bip69Sort_perm` proves that sorting neither drops
  nor duplicates an output.
* The fixed document order is *not* BIP 69+CLTV sorted:
  `waveF_f08_commitmentOutputEntries_not_sorted_of_toLocal_gt_toRemote` proves
  that any commitment whose non-zero `to_local` exceeds its non-zero
  `to_remote` is mis-ordered for every script rank, and
  `waveF_f08_documentOrder_not_bip69` packages a concrete witness.
  `waveF_f08_cltvExpiry_not_visible_in_commitmentOutputs` shows the existing
  output list cannot distinguish two HTLCs that differ only in `cltv_expiry`,
  so the CLTV key genuinely is missing from the model.

BOLT sections.
* BOLT 3 `Transaction Output Ordering` (`03-transactions.md:54-59`): value,
  then scriptpubkey, then `cltv_expiry`; rationale at `:61-66`.
* BOLT 3 `Commitment Transaction Construction` (`03-transactions.md:727-734`):
  build the output set, then sort into BIP 69+CLTV order.

rust-lightning anchors at `fe4900930c6bd5786ec4203274d7cf312776a5a6`.
* `lightning/src/ln/chan_utils.rs:1752-1779` (`is_left_greater`: compares
  value, then scriptpubkey, then `cltv_expiry`, then payment hash as a
  fuzzing-only tie-break).
* `lightning/src/ln/chan_utils.rs:1831-1878`
  (`build_outputs_and_htlcs`: sorts HTLC outputs, then binary-inserts the
  non-HTLC outputs by value and scriptpubkey).
* `lightning/src/ln/chan_utils.rs:1979-2015` (`build_sorted_htlc_outputs`:
  insertion sort over HTLC outputs).
* `lightning/src/ln/chan_utils.rs:1781-1785` (the verifier rejects a
  commitment whose HTLC outputs are not in this order).

What is NOT modelled.
* Scriptpubkey bytes, payment hashes, funding/payment keys.  `CommitmentOutput`
  only records the output *kind* and value, so the middle ordering key is an
  abstract `Nat` rank.  The positive sorting theorem is proved for every rank
  assignment; the negative result is independent of it.
* Payment-hash tie-breaking for equal value, equal script, equal CLTV
  (LDK-only fuzzing fallback), the obscured commitment number, signatures, and
  `nSequence`.
* The single-anchor exception and dust trimming, which decide the output set
  but not its order.
-/

namespace LnLean.Proofs.ModelHardening.F08

open LnLean
open LnLean.Channel
open scoped List

set_option autoImplicit false

-- OBLIGATION: LN-WF-F08

/-! ## Outputs at CLTV resolution -/

/-- A commitment output together with the CLTV expiry that BOLT 3 uses as the
last ordering key.  Non-HTLC outputs have no CLTV, recorded here as `0`. -/
structure OutputEntry where
  /-- The output itself, at the resolution of `CommitmentOutput`. -/
  output : CommitmentOutput
  /-- `cltv_expiry` of an HTLC output; `0` for every other kind. -/
  cltvExpiry : Height
deriving Repr, DecidableEq, BEq

namespace OutputEntry

/-- A non-HTLC output, which carries no CLTV expiry. -/
def ofOutput (o : CommitmentOutput) : OutputEntry :=
  { output := o, cltvExpiry := 0 }

/-- An HTLC output, carrying the `cltv_expiry` needed by the final key. -/
def ofHtlc (h : CommitmentHTLCOutput) : OutputEntry :=
  { output := .htlc h.direction h.amountSat, cltvExpiry := h.cltvExpiry }

@[simp] theorem ofOutput_output (o : CommitmentOutput) :
    (ofOutput o).output = o := rfl

@[simp] theorem ofOutput_cltvExpiry (o : CommitmentOutput) :
    (ofOutput o).cltvExpiry = 0 := rfl

@[simp] theorem ofHtlc_output (h : CommitmentHTLCOutput) :
    (ofHtlc h).output = .htlc h.direction h.amountSat := rfl

@[simp] theorem ofHtlc_cltvExpiry (h : CommitmentHTLCOutput) :
    (ofHtlc h).cltvExpiry = h.cltvExpiry := rfl

end OutputEntry

/-- The document order of `Commitment.commitmentOutputs`, annotated with the
CLTV expiry of each HTLC.  This is the *unsorted* output set that BOLT 3 then
requires to be sorted; `waveF_f08_commitmentOutputEntries_map_output` shows
that forgetting the CLTV annotation recovers the existing model output list. -/
def waveF_f08_commitmentOutputEntries (c : Commitment) : List OutputEntry :=
  (if c.toLocalSat = 0 then [] else
      [OutputEntry.ofOutput (.toLocal c.toLocalSat)]) ++
  (if c.toRemoteSat = 0 then [] else
      [OutputEntry.ofOutput (.toRemote c.toRemoteSat)]) ++
  c.htlcs.map OutputEntry.ofHtlc ++
  (if c.anchorOutputs then
      [OutputEntry.ofOutput .localAnchor, OutputEntry.ofOutput .remoteAnchor]
    else [])

/-- The CLTV-annotated document order has exactly the existing output list as
its underlying `CommitmentOutput` sequence. -/
theorem waveF_f08_commitmentOutputEntries_map_output (c : Commitment) :
    (waveF_f08_commitmentOutputEntries c).map OutputEntry.output =
      c.commitmentOutputs := by
  by_cases hL : c.toLocalSat = 0 <;>
  by_cases hR : c.toRemoteSat = 0 <;>
  by_cases hA : c.anchorOutputs = true <;>
  simp [waveF_f08_commitmentOutputEntries, Commitment.commitmentOutputs, hL, hR, hA,
    OutputEntry.ofHtlc_output, List.map_map]

/-- The annotation adds no outputs: the two lists have the same length. -/
theorem waveF_f08_commitmentOutputEntries_length (c : Commitment) :
    (waveF_f08_commitmentOutputEntries c).length = c.commitmentOutputs.length := by
  rw [← waveF_f08_commitmentOutputEntries_map_output, List.length_map]

/-- With two non-zero balances the document order starts with `to_local`
followed by `to_remote`.  This is the prefix that BIP 69 reorders. -/
theorem waveF_f08_commitmentOutputEntries_cons (c : Commitment)
    (hL : c.toLocalSat ≠ 0) (hR : c.toRemoteSat ≠ 0) :
    waveF_f08_commitmentOutputEntries c =
      OutputEntry.ofOutput (.toLocal c.toLocalSat) ::
        OutputEntry.ofOutput (.toRemote c.toRemoteSat) ::
          (c.htlcs.map OutputEntry.ofHtlc ++
            (if c.anchorOutputs then
                [OutputEntry.ofOutput .localAnchor,
                 OutputEntry.ofOutput .remoteAnchor]
              else [])) := by
  simp [waveF_f08_commitmentOutputEntries, hL, hR]

/-! ## The BOLT 3 ordering key -/

/-- The canonical kind-level script rank used when only the output kind is
known.  Distinct output kinds have distinct scripts; two HTLCs of the same
direction share a rank because their payment hashes (and therefore their
scripts) are absent from the model. -/
def waveF_f08_scriptRank : CommitmentOutput → Nat
  | .toLocal _ => 0
  | .toRemote _ => 1
  | .htlc .local _ => 2
  | .htlc .remote _ => 3
  | .localAnchor => 4
  | .remoteAnchor => 5

@[simp] theorem waveF_f08_scriptRank_toLocal (v : Nat) :
    waveF_f08_scriptRank (CommitmentOutput.toLocal v) = 0 := rfl

@[simp] theorem waveF_f08_scriptRank_toRemote (v : Nat) :
    waveF_f08_scriptRank (CommitmentOutput.toRemote v) = 1 := rfl

@[simp] theorem waveF_f08_scriptRank_htlc_local (v : Nat) :
    waveF_f08_scriptRank (CommitmentOutput.htlc .local v) = 2 := rfl

@[simp] theorem waveF_f08_scriptRank_htlc_remote (v : Nat) :
    waveF_f08_scriptRank (CommitmentOutput.htlc .remote v) = 3 := rfl

/-- The three BOLT 3 ordering components: value, script, CLTV expiry. -/
structure OutputKey where
  /-- Value in whole satoshis (the msat part is ignored). -/
  valueSat : Nat
  /-- Abstract rank of the `scriptpubkey`; equal ranks mean equal scripts. -/
  scriptRank : Nat
  /-- `cltv_expiry`, the final tie-break for HTLC outputs. -/
  cltvExpiry : Nat
deriving Repr, DecidableEq, BEq

/-- The BOLT 3 sort key of an output entry under a script rank assignment. -/
def OutputEntry.key (script : CommitmentOutput → Nat) (e : OutputEntry) : OutputKey :=
  { valueSat := e.output.value
    scriptRank := script e.output
    cltvExpiry := e.cltvExpiry }

namespace OutputKey

/-- BOLT 3 value-then-script-then-CLTV comparison, as a proposition.  The
CLTV component is consulted only when both value and script are equal. -/
def lexLeProp (a b : OutputKey) : Prop :=
  a.valueSat < b.valueSat ∨
    (a.valueSat = b.valueSat ∧
      (a.scriptRank < b.scriptRank ∨
        (a.scriptRank = b.scriptRank ∧ a.cltvExpiry ≤ b.cltvExpiry)))

/-- `lexLeProp` is decidable, so it can drive `List.mergeSort`. -/
instance instDecidableLexLeProp (a b : OutputKey) : Decidable (a.lexLeProp b) := by
  unfold lexLeProp
  infer_instance

/-- Boolean form of `lexLeProp`, suitable for `List.mergeSort`. -/
def lexLe (a b : OutputKey) : Bool := decide (a.lexLeProp b)

@[simp] theorem lexLe_eq_true {a b : OutputKey} :
    (a.lexLe b = true) ↔ a.lexLeProp b := by
  simp [lexLe]

/-- The BOLT 3 key order is transitive. -/
theorem lexLeProp_trans (a b c : OutputKey)
    (hab : a.lexLeProp b) (hbc : b.lexLeProp c) : a.lexLeProp c := by
  unfold lexLeProp at *
  omega

/-- The BOLT 3 key order is reflexive. -/
theorem lexLeProp_refl (a : OutputKey) : a.lexLeProp a := by
  unfold lexLeProp
  omega

/-- The BOLT 3 key order is total. -/
theorem lexLeProp_total (a b : OutputKey) : a.lexLeProp b ∨ b.lexLeProp a := by
  unfold lexLeProp
  omega

theorem lexLe_trans {a b c : OutputKey}
    (hab : a.lexLe b = true) (hbc : b.lexLe c = true) : a.lexLe c = true := by
  rw [lexLe_eq_true] at hab hbc ⊢
  exact lexLeProp_trans _ _ _ hab hbc

theorem lexLe_total (a b : OutputKey) : (a.lexLe b || b.lexLe a) = true := by
  rw [Bool.or_eq_true, lexLe_eq_true, lexLe_eq_true]
  exact lexLeProp_total a b

/-- When value and script agree, the BOLT 3 order is exactly the CLTV order. -/
theorem lexLeProp_iff_cltv_of_value_script_eq {a b : OutputKey}
    (hv : a.valueSat = b.valueSat) (hs : a.scriptRank = b.scriptRank) :
    (a.lexLeProp b ↔ a.cltvExpiry ≤ b.cltvExpiry) := by
  unfold lexLeProp
  omega

end OutputKey

/-! ## The predicate and the sorted construction -/

/-- `Bip69CltvSorted script l` is the BOLT 3 `Transaction Output Ordering`
predicate: consecutive entries are non-decreasing under value, then script,
then (for HTLCs) `cltv_expiry`. -/
def Bip69CltvSorted (script : CommitmentOutput → Nat) (l : List OutputEntry) : Prop :=
  l.Pairwise (fun a b =>
    OutputKey.lexLeProp (OutputEntry.key script a) (OutputEntry.key script b))

/-- Sort the document entries into BIP 69+CLTV order. -/
def bip69Sort (script : CommitmentOutput → Nat) (l : List OutputEntry) : List OutputEntry :=
  l.mergeSort (fun a b => OutputKey.lexLe (OutputEntry.key script a) (OutputEntry.key script b))

/-- **The sorted-output construction satisfies BOLT 3 ordering**, for every
script rank assignment. -/
theorem bip69Sort_sorted (script : CommitmentOutput → Nat) (l : List OutputEntry) :
    Bip69CltvSorted script (bip69Sort script l) := by
  have h := List.pairwise_mergeSort
    (le := fun a b : OutputEntry =>
      OutputKey.lexLe (OutputEntry.key script a) (OutputEntry.key script b))
    (fun _ _ _ hab hbc => OutputKey.lexLe_trans hab hbc)
    (fun a b => OutputKey.lexLe_total (OutputEntry.key script a) (OutputEntry.key script b))
    l
  simpa [Bip69CltvSorted, bip69Sort, OutputKey.lexLe_eq_true] using h

/-- Sorting preserves the multiset of outputs: nothing is dropped or added. -/
theorem bip69Sort_perm (script : CommitmentOutput → Nat) (l : List OutputEntry) :
    bip69Sort script l ~ l := by
  simpa [bip69Sort] using
    (List.mergeSort_perm (l := l)
      (le := fun a b : OutputEntry =>
      OutputKey.lexLe (OutputEntry.key script a) (OutputEntry.key script b)))

/-- Sorting does not change the number of outputs. -/
theorem bip69Sort_length (script : CommitmentOutput → Nat) (l : List OutputEntry) :
    (bip69Sort script l).length = l.length := by
  simp [bip69Sort]

/-- Sorting an already sorted list is the identity. -/
theorem bip69Sort_idempotent (script : CommitmentOutput → Nat) (l : List OutputEntry)
    (h : Bip69CltvSorted script l) : bip69Sort script l = l := by
  refine List.mergeSort_of_pairwise (l := l)
    (le := fun a b : OutputEntry =>
      OutputKey.lexLe (OutputEntry.key script a) (OutputEntry.key script b)) ?_
  simpa [Bip69CltvSorted, OutputKey.lexLe_eq_true] using h

/-- On a two-element list the construction is the expected conditional swap. -/
theorem bip69Sort_pair (script : CommitmentOutput → Nat) (a b : OutputEntry) :
    bip69Sort script [a, b] =
      if OutputKey.lexLe (OutputEntry.key script a) (OutputEntry.key script b) then [a, b] else [b, a] := by
  simp [bip69Sort, List.mergeSort_pair]

/-- A sorted list has non-decreasing output values: the primary BOLT 3 key. -/
theorem Bip69CltvSorted.value_mono {script : CommitmentOutput → Nat}
    {l : List OutputEntry} (h : Bip69CltvSorted script l) :
    (l.map (fun e => e.output.value)).Pairwise (· ≤ ·) := by
  refine h.map (fun e => e.output.value) ?_
  intro a b hab
  simp only [OutputEntry.key, OutputKey.lexLeProp] at hab
  omega

/-- The sorted construction for a whole commitment. -/
def waveF_f08_bip69Outputs (script : CommitmentOutput → Nat) (c : Commitment) :
    List OutputEntry :=
  bip69Sort script (waveF_f08_commitmentOutputEntries c)

/-- Every commitment's sorted construction satisfies BOLT 3 ordering. -/
theorem waveF_f08_bip69Outputs_sorted (script : CommitmentOutput → Nat) (c : Commitment) :
    Bip69CltvSorted script (waveF_f08_bip69Outputs script c) :=
  bip69Sort_sorted script (waveF_f08_commitmentOutputEntries c)

/-- The sorted construction is a permutation of the document output set. -/
theorem waveF_f08_bip69Outputs_perm (script : CommitmentOutput → Nat) (c : Commitment) :
    waveF_f08_bip69Outputs script c ~ waveF_f08_commitmentOutputEntries c :=
  bip69Sort_perm script (waveF_f08_commitmentOutputEntries c)

/-- Consequently the sorted output *values* are a permutation of the document
output values. -/
theorem waveF_f08_bip69Outputs_map_output_perm (script : CommitmentOutput → Nat)
    (c : Commitment) :
    (waveF_f08_bip69Outputs script c).map OutputEntry.output ~ c.commitmentOutputs := by
  rw [← waveF_f08_commitmentOutputEntries_map_output]
  exact (waveF_f08_bip69Outputs_perm script c).map OutputEntry.output

/-- The canonical construction, using the kind-level script rank. -/
theorem waveF_f08_bip69Outputs_scriptRank_sorted (c : Commitment) :
    Bip69CltvSorted waveF_f08_scriptRank
      (waveF_f08_bip69Outputs waveF_f08_scriptRank c) :=
  waveF_f08_bip69Outputs_sorted waveF_f08_scriptRank c

/-! ## Concrete checks of the predicate -/

/-- A value-ordered list of three different output kinds is sorted. -/
theorem waveF_f08_sorted_three_entry_example :
    Bip69CltvSorted waveF_f08_scriptRank
      [{ output := .toRemote 300, cltvExpiry := 0 },
       { output := .htlc .local 400, cltvExpiry := 500 },
       { output := .toLocal 500, cltvExpiry := 0 }] := by
  simp [Bip69CltvSorted, OutputEntry.key, OutputKey.lexLeProp, CommitmentOutput.value] <;> omega

/-- Equal value and equal script: increasing CLTV is required. -/
theorem waveF_f08_sorted_cltv_tiebreak_example :
    Bip69CltvSorted waveF_f08_scriptRank
      [{ output := .htlc .local 400, cltvExpiry := 100 },
       { output := .htlc .local 400, cltvExpiry := 200 }] := by
  simp [Bip69CltvSorted, OutputEntry.key, OutputKey.lexLeProp, CommitmentOutput.value] <;> omega

/-- Equal value and equal script in decreasing CLTV order is rejected. -/
theorem waveF_f08_unsorted_cltv_tiebreak_example :
    ¬ Bip69CltvSorted waveF_f08_scriptRank
      [{ output := .htlc .local 400, cltvExpiry := 200 },
       { output := .htlc .local 400, cltvExpiry := 100 }] := by
  simp [Bip69CltvSorted, OutputEntry.key, OutputKey.lexLeProp, CommitmentOutput.value] <;> omega

/-! ## The fixed document order is not BIP 69+CLTV sorted -/

/-- Prefix/subsequence form: in a sorted list, the first element of any
two-element sublist precedes the second. -/
theorem waveF_f08_bip69Sorted_pair_of_sublist {script : CommitmentOutput → Nat}
    {a b : OutputEntry} {l : List OutputEntry}
    (hs : Bip69CltvSorted script l) (h : [a, b] <+ l) :
    OutputKey.lexLeProp (OutputEntry.key script a) (OutputEntry.key script b) :=
  hs.forall_sublist h

/-- Whenever both balances are non-zero and `to_remote` is smaller,
`waveF_f08_commitmentOutputEntries` puts the larger `to_local` first,
violating the value key for **every** script rank assignment. -/
theorem waveF_f08_commitmentOutputEntries_not_sorted_of_toLocal_gt_toRemote
    (script : CommitmentOutput → Nat) (c : Commitment)
    (hL : c.toLocalSat ≠ 0) (hR : c.toRemoteSat ≠ 0)
    (hlt : c.toRemoteSat < c.toLocalSat) :
    ¬ Bip69CltvSorted script (waveF_f08_commitmentOutputEntries c) := by
  intro hs
  have hsub : [OutputEntry.ofOutput (.toLocal c.toLocalSat),
      OutputEntry.ofOutput (.toRemote c.toRemoteSat)] <+
        waveF_f08_commitmentOutputEntries c := by
    rw [waveF_f08_commitmentOutputEntries_cons c hL hR]
    exact ((List.nil_sublist _).cons_cons _).cons_cons _
  have hrel := waveF_f08_bip69Sorted_pair_of_sublist hs hsub
  simp [OutputEntry.key, OutputKey.lexLeProp, CommitmentOutput.value] at hrel
  omega

/-- A concrete commitment in document order: `to_local = 1000` precedes
`to_remote = 500`. -/
def waveF_f08_descendingCommitment : Commitment :=
  { holder := .local
    commitmentNumber := 0
    fundingValueSat := 1500
    toLocalSat := 1000
    toRemoteSat := 500
    htlcs := []
    feeSat := 0
    contestDelay := 0
    anchorOutputs := false }

theorem waveF_f08_descendingCommitment_entries :
    waveF_f08_commitmentOutputEntries waveF_f08_descendingCommitment =
      [{ output := .toLocal 1000, cltvExpiry := 0 },
       { output := .toRemote 500, cltvExpiry := 0 }] := rfl

/-- The witness fails BIP 69+CLTV ordering for every script rank. -/
theorem waveF_f08_descendingCommitment_not_sorted (script : CommitmentOutput → Nat) :
    ¬ Bip69CltvSorted script
      (waveF_f08_commitmentOutputEntries waveF_f08_descendingCommitment) :=
  waveF_f08_commitmentOutputEntries_not_sorted_of_toLocal_gt_toRemote script
    waveF_f08_descendingCommitment
    (by simp [waveF_f08_descendingCommitment])
    (by simp [waveF_f08_descendingCommitment])
    (by simp [waveF_f08_descendingCommitment])

/-- **Negative result**: there is a commitment whose fixed document order is
not the BIP 69+CLTV order under any script rank assignment.  Sorting is
therefore not a no-op on the model's output construction. -/
theorem waveF_f08_documentOrder_not_bip69 :
    ∃ c : Commitment, ∀ script : CommitmentOutput → Nat,
      ¬ Bip69CltvSorted script (waveF_f08_commitmentOutputEntries c) :=
  ⟨waveF_f08_descendingCommitment, waveF_f08_descendingCommitment_not_sorted⟩

/-! ## The CLTV component is invisible to `commitmentOutputs` -/

/-- A one-HTLC commitment used to exhibit the missing CLTV field. -/
def waveF_f08_oneHtlcCommitment (cltv : Height) : Commitment :=
  { holder := .local
    commitmentNumber := 0
    fundingValueSat := 2000
    toLocalSat := 1000
    toRemoteSat := 500
    htlcs := [{ direction := .local
                amountSat := 400
                cltvExpiry := cltv
                state := .offered }]
    feeSat := 0
    contestDelay := 0
    anchorOutputs := false }

/-- Two commitments can have the same `commitmentOutputs` while their HTLC
lists differ only in `cltv_expiry`. -/
theorem waveF_f08_cltvExpiry_not_visible_in_commitmentOutputs :
    ∃ c c' : Commitment,
      c.commitmentOutputs = c'.commitmentOutputs ∧ c.htlcs ≠ c'.htlcs := by
  refine ⟨waveF_f08_oneHtlcCommitment 100, waveF_f08_oneHtlcCommitment 200, ?_, ?_⟩
  · simp [Commitment.commitmentOutputs, waveF_f08_oneHtlcCommitment]
  · simp [waveF_f08_oneHtlcCommitment]

/-- The CLTV-annotated entries, unlike `commitmentOutputs`, do distinguish the
two commitments; the sorted construction can therefore order them differently. -/
theorem waveF_f08_cltvExpiry_changes_commitmentOutputEntries :
    waveF_f08_commitmentOutputEntries (waveF_f08_oneHtlcCommitment 100) ≠
      waveF_f08_commitmentOutputEntries (waveF_f08_oneHtlcCommitment 200) := by
  decide

end LnLean.Proofs.ModelHardening.F08
