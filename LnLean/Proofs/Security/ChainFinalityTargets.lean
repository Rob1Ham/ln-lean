import LnLean.Proofs.Security.ReorgTargets

/-!
# LnLean.Proofs.Security.ChainFinalityTargets

**English claim (catalog `LN-L1-003`, issue `L1-06`).**  A transaction or
output confirmed sufficiently deep on the canonical chain is not removed by a
reorganisation whose depth is bounded and whose competing chain shares the
relevant common prefix.  The bound is necessary: an unbounded (or merely
larger) reorg has a concrete counterexample.

`LnLean.Proofs.Security.ReorgTargets` states the conditional preservation
result over an abstract `ChainView`/`Reorg` pair and keeps `SameChain`,
`InCommonPrefix`, `Observations.SafeAt`, and `Observations.OutOfReachOf` as
explicit hypotheses.  This module supplies the missing L1 graph object:

* a concrete `Block`/`Chain` graph whose list position is the block height,
  with a `parent` pointer and a finite `WellFormed` linkage predicate;
* `Chain.PrefixOf` and `Chain.CommonAncestor`, the graph-level replacement for
  the unmodelled common-prefix arithmetic;
* `Chain.ConfirmedAtDepth`, the confirmation notion expressed as
  `d < length - height`, and `Chain.depth`, the number of blocks above a
  height;
* a bounded-depth finality theorem (`bounded_depth_finality`,
  `confirmed_tx_not_reorged`) and its family form over a unique canonical tip
  (`unique_tip_finality`);
* a direct transfer from the existing `reorgSurvives`, `InCommonPrefix`, and
  `OutOfReachOf` predicates into block-prefix statements;
* a small concrete chain with a non-vacuous surviving transaction and two
  rejection cases; and
* a deep-fork counterexample (`deep_reorg_evicts`,
  `depth_bound_necessary`) showing that dropping the depth bound breaks the
  conclusion.

The model is deliberately finite and structural.  It does not contain proof
of work, chainwork comparison, transaction validity, timestamps, or a
probabilistic reorg process.  `Block.hash` and `Block.parent` are natural
numbers: the graph shape is faithful, the hash primitive is not.  Consequently
the result is about *which blocks a competing chain retains*, not about
consensus validity or double-spend economics.  That remaining boundary is the
same `LN-CHAIN-REORG` obligation recorded by `ReorgTargets`.

BOLT 5 §"HTLC Output Handling" (`05-onchain.md:300-304`, `:467-471`) is the
protocol source for the anti-reorg delay.  LDK's `ANTI_REORG_DELAY = 6`
(`lightning/src/chain/channelmonitor.rs:347`) is the constant already modelled
by `ReorgTargets.antiReorgDelay`; this file does not change it.
-/

namespace LnLean.Proofs.Security.ChainFinalityTargets

open LnLean
open LnLean.Security
open LnLean.Proofs.Security.ReorgTargets

set_option autoImplicit false

/-! ## 1. Blocks and chains as a finite graph -/

/-- A block in the graph.  `hash` is an opaque natural-number identity (not a
cryptographic hash), `parent` is the parent identity, and `height` is the
height claimed by the block.  Linkage and height agreement are imposed by
`Chain.WellFormed`, not by the structure. -/
structure Block where
  hash : Nat
  parent : Option Nat
  height : Nat
deriving Repr, DecidableEq, BEq

/-- A chain is a list of blocks whose list index is the height.  Keeping the
index explicit avoids a total `height → block` function and makes every
concrete witness finite. -/
structure Chain where
  blocks : List Block
deriving Repr, DecidableEq

namespace Chain

/-- Number of blocks in the chain. -/
def length (c : Chain) : Nat := c.blocks.length

/-- The block at height `h`, if the chain reaches that height. -/
def blockAt (c : Chain) (h : Nat) : Option Block := c.blocks[h]?

/-- Height of the chain tip.  Empty chains have tip height `0` by truncated
subtraction; all finality statements below also assume a nonempty chain. -/
def tipHeight (c : Chain) : Nat := c.length - 1

/-- Confirmations of the block at height `h`, including the block itself.
A block at the tip has one confirmation. -/
def confirmations (c : Chain) (h : Nat) : Nat := c.length - h

/-- Number of blocks strictly above height `h` (the usual "confirmation
depth" of an output in that block). -/
def depth (c : Chain) (h : Nat) : Nat := c.length - 1 - h

/-- The block at height `h` is confirmed at depth `d`: it has at least `d + 1`
confirmations.  This is the exact hypothesis consumed by the finality theorem
below. -/
def ConfirmedAtDepth (c : Chain) (h d : Nat) : Prop :=
  d < c.confirmations h

/-- `a` is a prefix of `c`: the two chains agree on every height below
`a.length`.  This is the graph-level common-prefix object. -/
def PrefixOf (a c : Chain) : Prop :=
  ∃ rest : List Block, c.blocks = a.blocks ++ rest

/-- `a` is a common ancestor of `c` and `c'`. -/
def CommonAncestor (a c c' : Chain) : Prop :=
  PrefixOf a c ∧ PrefixOf a c'

/-- The chains agree on all heights below `p`.  This is the height-indexed
reading of a shared prefix of length `p`. -/
def SharesPrefix (c c' : Chain) (p : Nat) : Prop :=
  ∀ h : Nat, h < p → c.blockAt h = c'.blockAt h

/-- A reorg from `c` to `c'` stays within depth `d` when the two chains agree
on the prefix `c.length - d`.  In particular, a depth-`d` reorg may replace
only the last `d` blocks of `c`. -/
def ReorgWithin (c c' : Chain) (d : Nat) : Prop :=
  SharesPrefix c c' (c.length - d)

/-- Structural well-formedness: the first block is the genesis block
(`parent = none`, height `0`) and every later block points at its predecessor
and has the next height. -/
def LinksFrom : Option Nat → Nat → List Block → Prop
  | _, _, [] => True
  | parent, height, b :: rest =>
      b.parent = parent ∧ b.height = height ∧
        LinksFrom (some b.hash) (height + 1) rest

/-- A chain is well formed when its blocks are a finite linked spine starting
at genesis. -/
def WellFormed (c : Chain) : Prop :=
  LinksFrom none 0 c.blocks

@[simp] theorem length_mk (blocks : List Block) :
    length ⟨blocks⟩ = blocks.length := rfl

@[simp] theorem blockAt_mk (blocks : List Block) (h : Nat) :
    blockAt ⟨blocks⟩ h = blocks[h]? := rfl

/-- Prefix inclusion is reflexive. -/
theorem prefixOf_refl (c : Chain) : PrefixOf c c :=
  ⟨[], by simp⟩

/-- Prefix inclusion is transitive. -/
theorem prefixOf_trans {a b c : Chain}
    (hab : PrefixOf a b) (hbc : PrefixOf b c) : PrefixOf a c := by
  rcases hab with ⟨r₁, hb⟩
  rcases hbc with ⟨r₂, hc⟩
  refine ⟨r₁ ++ r₂, ?_⟩
  rw [hc, hb]
  simp [List.append_assoc]

/-- A prefix is never longer than the chain that extends it. -/
theorem length_le_of_prefix {a c : Chain} (hp : PrefixOf a c) :
    a.length ≤ c.length := by
  rcases hp with ⟨rest, hc⟩
  have hlen : c.length = a.length + rest.length := by
    simpa [length, List.length_append] using congrArg List.length hc
  omega

/-- A prefix agrees with its extension at every height below its own length.
This is the block-level content of `CommonAncestor`. -/
theorem blockAt_eq_of_prefix {a c : Chain} {h : Nat}
    (hp : PrefixOf a c) (hh : h < a.length) :
    c.blockAt h = a.blockAt h := by
  rcases hp with ⟨rest, hc⟩
  change c.blocks[h]? = a.blocks[h]?
  rw [hc]
  have hh' : h < a.blocks.length := by
    simpa [length] using hh
  simp [List.getElem?_append, hh']

/-- Common ancestry is symmetric in its two descendants. -/
theorem commonAncestor_comm {a c c' : Chain}
    (h : CommonAncestor a c c') : CommonAncestor a c' c :=
  ⟨h.2, h.1⟩

/-- Every chain is its own common ancestor with itself. -/
theorem commonAncestor_refl (c : Chain) : CommonAncestor c c c :=
  ⟨prefixOf_refl c, prefixOf_refl c⟩

/-- Common ancestry transfers from a shorter prefix to a longer one. -/
theorem commonAncestor_mono {a b c c' : Chain}
    (hab : PrefixOf a b) (h : CommonAncestor b c c') :
    CommonAncestor a c c' :=
  ⟨prefixOf_trans hab h.1, prefixOf_trans hab h.2⟩

/-- Sharing a prefix is reflexive. -/
theorem sharesPrefix_refl (c : Chain) (p : Nat) : SharesPrefix c c p :=
  fun _ _ => rfl

/-- Sharing a longer prefix implies sharing every shorter one. -/
theorem sharesPrefix_mono {c c' : Chain} {p q : Nat}
    (hpq : p ≤ q) (h : SharesPrefix c c' q) : SharesPrefix c c' p :=
  fun hh hlt => h hh (Nat.lt_of_lt_of_le hlt hpq)

/-- A common ancestor of length at least `p` makes the chains share the
height-`p` prefix. -/
theorem sharesPrefix_of_commonAncestor {a c c' : Chain} {p : Nat}
    (h : CommonAncestor a c c') (hap : p ≤ a.length) :
    SharesPrefix c c' p := by
  intro hh hlt
  have hha : hh < a.length := Nat.lt_of_lt_of_le hlt hap
  rw [blockAt_eq_of_prefix h.1 hha, blockAt_eq_of_prefix h.2 hha]

/-- Confirmation depth is the usual depth-above plus one. -/
theorem confirmations_eq_depth_add_one {c : Chain} {h : Nat}
    (hh : h < c.length) :
    c.confirmations h = c.depth h + 1 := by
  unfold confirmations depth
  omega

/-- Being confirmed at depth `d` is equivalent to having `d` blocks above the
height. -/
theorem confirmedAtDepth_iff_depth_le {c : Chain} {h d : Nat}
    (hh : h < c.length) :
    ConfirmedAtDepth c h d ↔ d ≤ c.depth h := by
  unfold ConfirmedAtDepth confirmations depth
  omega

/-- A confirmed block height is inside the chain. -/
theorem lt_length_of_confirmedAtDepth {c : Chain} {h d : Nat}
    (hconf : ConfirmedAtDepth c h d) : h < c.length := by
  unfold ConfirmedAtDepth confirmations at hconf
  omega

/-- A confirmed block lies below the prefix left by any depth-`e` reorg for
every `e ≤ d`. -/
theorem lt_length_sub_of_confirmedAtDepth {c : Chain} {h d : Nat}
    (hconf : ConfirmedAtDepth c h d) : h < c.length - d := by
  unfold ConfirmedAtDepth confirmations at hconf
  omega

/-- Confirmation is monotone in the depth bound. -/
theorem confirmedAtDepth_mono {c : Chain} {h d d' : Nat}
    (hdd : d' ≤ d) (hconf : ConfirmedAtDepth c h d) :
    ConfirmedAtDepth c h d' := by
  unfold ConfirmedAtDepth confirmations at hconf ⊢
  omega

end Chain

/-! ## 2. Bounded-depth finality on the graph -/

/-- **Bounded-depth finality (block form).**  Let `a` be a common ancestor of
the canonical chain `c` and a competing chain `c'`.  If the reorg removes at
most `d` canonical blocks (`c.length - a.length ≤ d`) and the block at height
`h` is confirmed at depth `d` on `c`, then the competing chain contains the
same block at height `h`.

The arithmetic is the whole content: confirmation at depth `d` gives
`h < c.length - d`, the depth bound gives `c.length - d ≤ a.length`, and the
common ancestor gives equality at every height below `a.length`. -/
theorem bounded_depth_finality {a c c' : Chain} {h d : Nat}
    (hanc : Chain.CommonAncestor a c c')
    (hdepth : c.length - a.length ≤ d)
    (hconf : c.ConfirmedAtDepth h d) :
    c.blockAt h = c'.blockAt h := by
  have hlt : h < c.length - d :=
    Chain.lt_length_sub_of_confirmedAtDepth hconf
  have hac : a.length ≤ c.length :=
    Chain.length_le_of_prefix hanc.1
  have hle : c.length - d ≤ a.length := by
    omega
  have ha : h < a.length := Nat.lt_of_lt_of_le hlt hle
  rw [Chain.blockAt_eq_of_prefix hanc.1 ha,
    Chain.blockAt_eq_of_prefix hanc.2 ha]

/-- The bounded-depth theorem is symmetric in the two descendants. -/
theorem bounded_depth_finality_symm {a c c' : Chain} {h d : Nat}
    (hanc : Chain.CommonAncestor a c c')
    (hdepth : c.length - a.length ≤ d)
    (hconf : c.ConfirmedAtDepth h d) :
    c'.blockAt h = c.blockAt h :=
  (bounded_depth_finality hanc hdepth hconf).symm

/-- The same statement in the height-indexed `ReorgWithin` form.  A depth-`d`
reorg agrees with the canonical chain below the common prefix; a block
confirmed at depth `d` lies inside that prefix. -/
theorem bounded_depth_finality_of_reorgWithin {c c' : Chain} {h d : Nat}
    (hwithin : c.ReorgWithin c' d)
    (hconf : c.ConfirmedAtDepth h d) :
    c.blockAt h = c'.blockAt h := by
  have hlt : h < c.length - d :=
    Chain.lt_length_sub_of_confirmedAtDepth hconf
  exact hwithin h hlt

/-! ## 3. Transactions and unique canonical tips -/

/-- A transaction/output commitment confirmed in a particular block.  `txid`
and `blockHash` are opaque identities. -/
structure ConfirmedTx where
  txid : Nat
  blockHash : Nat
  height : Nat
deriving Repr, DecidableEq

namespace ConfirmedTx

/-- The transaction is on the chain: the block at its height exists and has
the recorded hash. -/
def OnChain (t : ConfirmedTx) (c : Chain) : Prop :=
  ∃ b : Block, c.blockAt t.height = some b ∧ b.hash = t.blockHash

/-- Equality of the block at the transaction's height transfers confirmation
to the second chain. -/
theorem onChain_of_blockAt_eq {t : ConfirmedTx} {c c' : Chain}
    (ht : t.OnChain c)
    (heq : c.blockAt t.height = c'.blockAt t.height) :
    t.OnChain c' := by
  rcases ht with ⟨b, hb, hhash⟩
  exact ⟨b, by rw [← heq]; exact hb, hhash⟩

/-- Confirmation is preserved by an equality of the underlying block. -/
theorem onChain_congr {t : ConfirmedTx} {c c' : Chain}
    (heq : c'.blockAt t.height = c.blockAt t.height) :
    t.OnChain c ↔ t.OnChain c' := by
  constructor
  · intro ht
    exact onChain_of_blockAt_eq ht heq.symm
  · intro ht
    exact onChain_of_blockAt_eq ht heq

end ConfirmedTx

/-- **Transaction finality.**  A transaction confirmed at depth `d` on the
canonical chain is still present on every competing chain that shares the
common ancestor `a` and whose reorg depth is at most `d`. -/
theorem confirmed_tx_not_reorged {a c c' : Chain} {t : ConfirmedTx} {d : Nat}
    (ht : t.OnChain c)
    (hanc : Chain.CommonAncestor a c c')
    (hdepth : c.length - a.length ≤ d)
    (hconf : c.ConfirmedAtDepth t.height d) :
    t.OnChain c' :=
  ConfirmedTx.onChain_of_blockAt_eq ht
    (bounded_depth_finality hanc hdepth hconf)

/-- A unique canonical tip in a finite family: the canonical chain is a
member, no member is longer, and equal-length members are the same chain. -/
def UniqueCanonicalTip (chains : List Chain) (c : Chain) : Prop :=
  c ∈ chains ∧
    ∀ c' ∈ chains,
      c'.length ≤ c.length ∧ (c'.length = c.length → c'.blocks = c.blocks)

/-- Equal-length members of a unique-tip family are the canonical chain. -/
theorem unique_canonical_tip_eq {chains : List Chain} {c c' : Chain}
    (hcanon : UniqueCanonicalTip chains c) (hc' : c' ∈ chains)
    (hlen : c'.length = c.length) : c'.blocks = c.blocks :=
  (hcanon.2 c' hc').2 hlen

/-- No member of a unique-tip family is longer than the canonical chain. -/
theorem canonical_tip_max_length {chains : List Chain} {c c' : Chain}
    (hcanon : UniqueCanonicalTip chains c) (hc' : c' ∈ chains) :
    c'.length ≤ c.length :=
  (hcanon.2 c' hc').1

/-- **Finality at a unique canonical tip.**  The family hypothesis is used to
identify the canonical tip and rule out a longer competing chain; the actual
retention argument is the bounded-depth theorem. -/
theorem unique_tip_finality {chains : List Chain} {a c c' : Chain}
    {t : ConfirmedTx} {d : Nat}
    (hcanon : UniqueCanonicalTip chains c)
    (hc' : c' ∈ chains)
    (ht : t.OnChain c)
    (hanc : Chain.CommonAncestor a c c')
    (hdepth : c.length - a.length ≤ d)
    (hconf : c.ConfirmedAtDepth t.height d) :
    t.OnChain c' ∧ c'.length ≤ c.length :=
  ⟨confirmed_tx_not_reorged ht hanc hdepth hconf,
   canonical_tip_max_length hcanon hc'⟩

/-! ## 4. Transfer from `ReorgTargets`' abstract predicates -/

/-- A fixed non-cryptographic tip tag used when a `Chain` is viewed through the
existing `ChainView` record. -/
def chainTipTag : ByteArray := ByteArray.mk #[0xA5]

/-- View a graph chain as the abstract `ChainView` used by `ReorgTargets`. -/
def Chain.view (c : Chain) (tip : ByteArray) (lastReorg : Option Reorg) :
    ChainView :=
  { height := c.tipHeight, tip := tip, lastReorg := lastReorg }

@[simp] theorem view_height (c : Chain) (tip : ByteArray)
    (lastReorg : Option Reorg) :
    (c.view tip lastReorg).height = c.tipHeight := rfl

/-- Two chains of the same length present the same tip height and therefore
satisfy `SameChain` when they use the same tip tag. -/
theorem sameChain_view_of_length_eq {c c' : Chain} {tip : ByteArray}
    {lastReorg lastReorg' : Option Reorg} (hlen : c.length = c'.length) :
    SameChain (c.view tip lastReorg) (c'.view tip lastReorg') := by
  unfold SameChain Chain.view Chain.tipHeight
  constructor
  · rw [hlen]
  · rfl

/-- Same-chain survival judgements transfer between equal-length graph views.
This is the `SameChain` bridge used by `reorg_preserves_channel_safety`. -/
theorem sameChain_survival_transfer {c c' : Chain} {tip : ByteArray}
    {r : Reorg} {h : Nat} (hlen : c.length = c'.length) :
    reorgSurvives r (c.view tip none).height h ↔
      reorgSurvives r (c'.view tip none).height h :=
  survives_congr_of_sameChain (sameChain_view_of_length_eq hlen)

/-- The existing `reorgSurvives` predicate is exactly the graph-level prefix
test `h < c.length - r.depth`. -/
theorem reorgSurvives_iff_chain_prefix {c : Chain} {r : Reorg} {h : Nat}
    (hne : 0 < c.length) :
    reorgSurvives r c.tipHeight h ↔ h < c.length - r.depth := by
  unfold reorgSurvives confirmationCount Chain.tipHeight
  have htip : c.length - 1 + 1 = c.length := Nat.sub_add_cancel hne
  rw [htip]
  omega

/-- The existing `InCommonPrefix` predicate is exactly "the block height lies
inside the prefix left after a depth-`r.depth` reorg". -/
theorem inCommonPrefix_iff_chain_prefix {c : Chain} {r : Reorg} {h : Nat}
    (hne : 0 < c.length) :
    InCommonPrefix (c.view chainTipTag none) r h ↔
      h < c.length - r.depth := by
  rw [inCommonPrefix_iff_survives, view_height]
  exact reorgSurvives_iff_chain_prefix hne

/-- **`ReorgTargets` finality bridge.**  The existing `reorgSurvives`
hypothesis, together with a common ancestor whose length covers the unremoved
suffix, gives block equality. -/
theorem finality_from_reorgSurvives {a c c' : Chain} {r : Reorg} {h : Nat}
    (hanc : Chain.CommonAncestor a c c')
    (hdepth : c.length - a.length ≤ r.depth)
    (hne : 0 < c.length)
    (hsurv : reorgSurvives r c.tipHeight h) :
    c.blockAt h = c'.blockAt h := by
  have hlt : h < c.length - r.depth :=
    (reorgSurvives_iff_chain_prefix (c := c) (r := r) (h := h) hne).mp hsurv
  have hac : a.length ≤ c.length := Chain.length_le_of_prefix hanc.1
  have hle : c.length - r.depth ≤ a.length := by
    omega
  have ha : h < a.length := Nat.lt_of_lt_of_le hlt hle
  rw [Chain.blockAt_eq_of_prefix hanc.1 ha,
    Chain.blockAt_eq_of_prefix hanc.2 ha]

/-- `Observations.OutOfReachOf` is exactly the pointwise graph-depth bound on
the fact list.  The explicit `OutOfReachOf` hypothesis is preserved, not
replaced. -/
theorem outOfReachOf_iff_chain_prefix {o : Observations} {c : Chain}
    {r : Reorg} (hne : 0 < c.length) :
    o.OutOfReachOf (c.view chainTipTag none) r ↔
      ∀ e ∈ o.facts, e.height < c.length - r.depth := by
  constructor
  · intro hreach e he
    have hlt : r.depth < e.confirmations c.tipHeight := by
      have h := hreach e he
      simpa [OnchainFact.confirmations] using h
    have hconf : reorgSurvives r c.tipHeight e.height := hlt
    exact (reorgSurvives_iff_chain_prefix (c := c) (r := r) (h := e.height)
      hne).mp hconf
  · intro hdepth e he
    have hlt : e.height < c.length - r.depth := hdepth e he
    have hconf : reorgSurvives r c.tipHeight e.height :=
      (reorgSurvives_iff_chain_prefix (c := c) (r := r) (h := e.height)
        hne).mpr hlt
    simpa [Observations.OutOfReachOf, OnchainFact.confirmations]
      using hconf

/-- **`ReorgTargets` bridge.**  If a reorg is out of reach of every observation
fact (`OutOfReachOf`) and the graph chains share a common ancestor whose
length exceeds the removed suffix, then every fact block is unchanged. -/
theorem retained_fact_of_commonAncestor_depth {o : Observations}
    {a c c' : Chain} {r : Reorg} {e : OnchainFact}
    (hanc : Chain.CommonAncestor a c c')
    (hdepth : c.length - a.length ≤ r.depth)
    (hne : 0 < c.length)
    (hreach : o.OutOfReachOf (c.view chainTipTag none) r)
    (he : e ∈ o.facts) :
    c.blockAt e.height = c'.blockAt e.height := by
  have hconf : reorgSurvives r c.tipHeight e.height := by
    have hlt : r.depth < e.confirmations c.tipHeight := by
      simpa [Observations.OutOfReachOf, OnchainFact.confirmations]
        using hreach e he
    exact hlt
  exact finality_from_reorgSurvives hanc hdepth hne hconf

/-- **Composed retention and finality.**  The existing
`reorg_retains_of_depth_bound` gives ledger retention; the graph theorem gives
block-level finality under the same explicit hypotheses. -/
theorem chain_finality_and_retention {o : Observations} {a c c' : Chain}
    {r : Reorg}
    (hanc : Chain.CommonAncestor a c c')
    (hdepth : c.length - a.length ≤ r.depth)
    (hne : 0 < c.length)
    (hreach : o.OutOfReachOf (c.view chainTipTag none) r) :
    Retains o (o.applyReorgAt c.tipHeight r) ∧
      ∀ e ∈ o.facts, c.blockAt e.height = c'.blockAt e.height := by
  have hview : (c.view chainTipTag none).height = c.tipHeight := rfl
  have hret : Retains o (o.applyReorgAt (c.view chainTipTag none).height r) :=
    reorg_retains_of_depth_bound hreach
  refine ⟨?_, ?_⟩
  · simpa [hview] using hret
  · intro e he
    exact retained_fact_of_commonAncestor_depth hanc hdepth hne hreach he

/-! ## 5. Small concrete chain: a surviving transaction and rejections -/

/-- Compact block constructor. -/
def blk (hash : Nat) (parent : Option Nat) (height : Nat) : Block :=
  { hash := hash, parent := parent, height := height }

/-- A three-block canonical chain with hashes `100`, `101`, `102`. -/
def smallChain : Chain :=
  { blocks :=
      [blk 100 none 0,
       blk 101 (some 100) 1,
       blk 102 (some 101) 2] }

/-- A competing chain that shares the first two blocks and replaces the tip. -/
def smallAlt : Chain :=
  { blocks :=
      [blk 100 none 0,
       blk 101 (some 100) 1,
       blk 202 (some 101) 2] }

/-- The two-block common prefix of `smallChain` and `smallAlt`. -/
def smallPrefix : Chain :=
  { blocks :=
      [blk 100 none 0,
       blk 101 (some 100) 1] }

/-- A transaction confirmed in the genesis block. -/
def smallTx : ConfirmedTx :=
  { txid := 7, blockHash := 100, height := 0 }

/-- A transaction confirmed at the tip (height two). -/
def smallTipTx : ConfirmedTx :=
  { txid := 8, blockHash := 102, height := 2 }

/-- A chain with an unrelated genesis block. -/
def otherChain : Chain :=
  { blocks :=
      [blk 900 none 0,
       blk 901 (some 900) 1,
       blk 902 (some 901) 2] }

/-- The small canonical chain has the expected length. -/
theorem smallChain_length : smallChain.length = 3 := rfl

/-- The alternative tip block differs from the canonical tip. -/
theorem smallAlt_tip_hash : (smallAlt.blockAt 2).map Block.hash = some 202 := by
  simp [Chain.blockAt, smallAlt, blk]

/-- The small canonical chain is structurally well formed. -/
theorem smallChain_wellFormed : smallChain.WellFormed := by
  simp [Chain.WellFormed, Chain.LinksFrom, smallChain, blk]

/-- The alternative chain is structurally well formed. -/
theorem smallAlt_wellFormed : smallAlt.WellFormed := by
  simp [Chain.WellFormed, Chain.LinksFrom, smallAlt, blk]

/-- The unrelated chain is structurally well formed as well. -/
theorem otherChain_wellFormed : otherChain.WellFormed := by
  simp [Chain.WellFormed, Chain.LinksFrom, otherChain, blk]

/-- The two-block prefix really is a prefix of the canonical chain. -/
theorem smallPrefix_prefix_smallChain : smallPrefix.PrefixOf smallChain := by
  refine ⟨[blk 102 (some 101) 2], ?_⟩
  simp [smallPrefix, smallChain, blk]

/-- The two-block prefix really is a prefix of the alternative chain. -/
theorem smallPrefix_prefix_smallAlt : smallPrefix.PrefixOf smallAlt := by
  refine ⟨[blk 202 (some 101) 2], ?_⟩
  simp [smallPrefix, smallAlt, blk]

/-- The two chains share a concrete common ancestor of length two. -/
theorem small_commonAncestor :
    Chain.CommonAncestor smallPrefix smallChain smallAlt :=
  ⟨smallPrefix_prefix_smallChain, smallPrefix_prefix_smallAlt⟩

/-- The reorg removes exactly one canonical block, which is below the depth
bound two. -/
theorem small_chain_depthBound : smallChain.length - smallPrefix.length ≤ 2 := by
  decide

/-- The genesis transaction is confirmed at depth two (`3 - 0 = 3 > 2`). -/
theorem smallTx_confirmedAtDepth : smallChain.ConfirmedAtDepth 0 2 := by
  simp [Chain.ConfirmedAtDepth, Chain.confirmations, Chain.length, smallChain]

/-- The genesis transaction is on the canonical chain. -/
theorem smallTx_onChain : smallTx.OnChain smallChain := by
  refine ⟨blk 100 none 0, ?_, rfl⟩
  simp [Chain.blockAt, smallChain, smallTx, blk]

/-- **Non-vacuous positive instance.**  The genesis transaction survives a
one-block tip replacement because it is confirmed at depth two and the reorg
is within the bound.  The competing chain is not equal to the canonical chain,
so this is not the reflexive case. -/
theorem smallTx_not_reorged : smallTx.OnChain smallAlt :=
  confirmed_tx_not_reorged smallTx_onChain small_commonAncestor
    small_chain_depthBound smallTx_confirmedAtDepth

/-- The competing chain is genuinely different from the canonical chain. -/
theorem smallAlt_ne_smallChain : smallAlt ≠ smallChain := by
  intro h
  have htip : (smallAlt.blockAt 2).map Block.hash =
      (smallChain.blockAt 2).map Block.hash := by
    rw [h]
  rw [smallAlt_tip_hash] at htip
  simp [Chain.blockAt, smallChain, blk] at htip

/-- The tip transaction is on the canonical chain. -/
theorem smallTipTx_onChain : smallTipTx.OnChain smallChain := by
  refine ⟨blk 102 (some 101) 2, ?_, rfl⟩
  simp [Chain.blockAt, smallChain, smallTipTx, blk]

/-- The tip transaction has only one confirmation, so it is not confirmed at
depth two. -/
theorem smallTipTx_not_confirmedAtDepth :
    ¬ smallChain.ConfirmedAtDepth 2 2 := by
  simp [Chain.ConfirmedAtDepth, Chain.confirmations, Chain.length, smallChain]

/-- **Rejection at the tip.**  The depth-two hypothesis fails exactly for the
transaction at the tip, and the competing chain really does not contain it.
This is the concrete negative counterpart of `smallTx_not_reorged`. -/
theorem smallTipTx_rejected :
    ¬ smallTipTx.OnChain smallAlt ∧
      ¬ smallChain.ConfirmedAtDepth smallTipTx.height 2 := by
  refine ⟨?_, smallTipTx_not_confirmedAtDepth⟩
  intro h
  rcases h with ⟨b, hb, hhash⟩
  have hb' : some (blk 202 (some 101) 2) = some b := by
    simpa [Chain.blockAt, smallAlt, blk, smallTipTx] using hb
  have hbeq : b = blk 202 (some 101) 2 := (Option.some.inj hb').symm
  subst b
  simp [blk, smallTipTx] at hhash

/-- **Rejection of the prefix hypothesis.**  Without a common ancestor, the
same genesis transaction can be absent from an unrelated chain. -/
theorem smallTx_rejected_without_prefix : ¬ smallTx.OnChain otherChain := by
  intro h
  rcases h with ⟨b, hb, hhash⟩
  have hb' : some (blk 900 none 0) = some b := by
    simpa [Chain.blockAt, otherChain, blk, smallTx] using hb
  have hbeq : b = blk 900 none 0 := (Option.some.inj hb').symm
  subst b
  simp [blk, smallTx] at hhash

/-- The small witness is non-vacuous: a transaction survives, a tip
transaction is rejected, and an unrelated-prefix transaction is rejected. -/
theorem small_witness_summary :
    smallTx.OnChain smallAlt ∧
      ¬ smallTipTx.OnChain smallAlt ∧
      ¬ smallTx.OnChain otherChain ∧
      smallChain.WellFormed ∧ smallAlt.WellFormed ∧
      otherChain.WellFormed :=
  ⟨smallTx_not_reorged, smallTipTx_rejected.1,
   smallTx_rejected_without_prefix, smallChain_wellFormed,
   smallAlt_wellFormed, otherChain_wellFormed⟩

/-! ## 6. Deep reorg: the bound is necessary -/

/-- A six-block canonical chain with hashes `100` through `105`. -/
def deepChain : Chain :=
  { blocks :=
      [blk 100 none 0,
       blk 101 (some 100) 1,
       blk 102 (some 101) 2,
       blk 103 (some 102) 3,
       blk 104 (some 103) 4,
       blk 105 (some 104) 5] }

/-- A competing chain that forks at height three and replaces the last three
blocks. -/
def deepFork : Chain :=
  { blocks :=
      [blk 100 none 0,
       blk 101 (some 100) 1,
       blk 102 (some 101) 2,
       blk 203 (some 102) 3,
       blk 204 (some 203) 4,
       blk 205 (some 204) 5] }

/-- The three-block common prefix of the deep fork. -/
def deepPrefix : Chain :=
  { blocks :=
      [blk 100 none 0,
       blk 101 (some 100) 1,
       blk 102 (some 101) 2] }

/-- A transaction confirmed in block `103` at height three. -/
def deepTx : ConfirmedTx :=
  { txid := 42, blockHash := 103, height := 3 }

/-- The deep canonical chain is structurally well formed. -/
theorem deepChain_wellFormed : deepChain.WellFormed := by
  simp [Chain.WellFormed, Chain.LinksFrom, deepChain, blk]

/-- The forked chain is structurally well formed. -/
theorem deepFork_wellFormed : deepFork.WellFormed := by
  simp [Chain.WellFormed, Chain.LinksFrom, deepFork, blk]

/-- The deep prefix really is shared. -/
theorem deep_commonAncestor : Chain.CommonAncestor deepPrefix deepChain deepFork := by
  constructor
  · refine ⟨[blk 103 (some 102) 3, blk 104 (some 103) 4,
      blk 105 (some 104) 5], ?_⟩
    simp [deepPrefix, deepChain, blk]
  · refine ⟨[blk 203 (some 102) 3, blk 204 (some 203) 4,
      blk 205 (some 204) 5], ?_⟩
    simp [deepPrefix, deepFork, blk]

/-- The fork removes three canonical blocks. -/
theorem deep_reorg_depth : deepChain.length - deepPrefix.length = 3 := by
  simp [Chain.length, deepChain, deepPrefix]

/-- The transaction is on the canonical chain. -/
theorem deepTx_onChain : deepTx.OnChain deepChain := by
  refine ⟨blk 103 (some 102) 3, ?_, rfl⟩
  simp [Chain.blockAt, deepChain, deepTx, blk]

/-- The transaction has three confirmations, so it is confirmed at depth two
but not at depth three. -/
theorem deepTx_confirmedAtDepth : deepChain.ConfirmedAtDepth 3 2 := by
  simp [Chain.ConfirmedAtDepth, Chain.confirmations, Chain.length, deepChain]

/-- Three confirmations are not enough for depth three. -/
theorem deepTx_not_confirmedAtDepth_three :
    ¬ deepChain.ConfirmedAtDepth 3 3 := by
  simp [Chain.ConfirmedAtDepth, Chain.confirmations, Chain.length, deepChain]

/-- The depth-two bound excludes this fork: `3 ≤ 2` is false. -/
theorem deep_bound_violated : ¬ (deepChain.length - deepPrefix.length ≤ 2) := by
  simp [Chain.length, deepChain, deepPrefix]

/-- The transaction is absent from the forked chain. -/
theorem deepTx_not_on_fork : ¬ deepTx.OnChain deepFork := by
  intro h
  rcases h with ⟨b, hb, hhash⟩
  have hb' : some (blk 203 (some 102) 3) = some b := by
    simpa [Chain.blockAt, deepFork, blk, deepTx] using hb
  have hbeq : b = blk 203 (some 102) 3 := (Option.some.inj hb').symm
  subst b
  simp [blk, deepTx] at hhash

/-- **Deep-reorg counterexample.**  A transaction confirmed at depth two is
evicted by a depth-three fork.  The depth-two hypothesis of the finality
theorem fails, so this is not a contradiction: it is exactly why the bound is
needed. -/
theorem deep_reorg_evicts :
    deepTx.OnChain deepChain ∧
      deepChain.ConfirmedAtDepth deepTx.height 2 ∧
      ¬ deepTx.OnChain deepFork ∧
      ¬ (deepChain.length - deepPrefix.length ≤ 2) :=
  ⟨deepTx_onChain, deepTx_confirmedAtDepth, deepTx_not_on_fork,
   deep_bound_violated⟩

/-- At depth three the finality hypothesis would hold (three confirmations,
`3 < 3` is false), so the counterexample is at the exact boundary rather than
below it. -/
theorem deep_boundary_is_sharp :
    deepChain.confirmations deepTx.height = 3 ∧
      deepChain.depth deepTx.height = 2 ∧
      deepChain.length - deepPrefix.length = 3 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [Chain.confirmations, Chain.depth, Chain.length, deepChain, deepPrefix,
      deepTx]

/-- **The depth bound is necessary.**  There are chains `a`, `c`, `c'`, a
transaction `t`, and a bound `d` such that `t` is confirmed at depth `d` on
`c` and `a` is a common ancestor, but `c`'s suffix is longer than `d` and `t`
is absent from `c'`.  This is the negation of the finality conclusion with the
depth hypothesis removed. -/
theorem depth_bound_necessary :
    ∃ (a c c' : Chain) (t : ConfirmedTx) (d : Nat),
      Chain.CommonAncestor a c c' ∧
        t.OnChain c ∧
        c.ConfirmedAtDepth t.height d ∧
        ¬ (c.length - a.length ≤ d) ∧
        ¬ t.OnChain c' :=
  ⟨deepPrefix, deepChain, deepFork, deepTx, 2, deep_commonAncestor,
   deepTx_onChain, deepTx_confirmedAtDepth, deep_bound_violated,
   deepTx_not_on_fork⟩

/-- The concrete deep fork is the sharp witness for the depth bound: it is
well formed, it is deeper than the bound, and it evicts an otherwise confirmed
transaction. -/
theorem deep_witness_summary :
    deepChain.WellFormed ∧ deepFork.WellFormed ∧
      deepChain.length = 6 ∧ deepFork.length = 6 ∧
      deepChain.length - deepPrefix.length = 3 ∧
      ¬ deepTx.OnChain deepFork :=
  ⟨deepChain_wellFormed, deepFork_wellFormed,
   by simp [Chain.length, deepChain],
   by simp [Chain.length, deepFork],
   deep_reorg_depth, deepTx_not_on_fork⟩

/-! ## 7. NET-01: one concrete eventual-delivery instance -/

/-- Lightning messages used by the funding route.  The constructors are
model-level tags, not wire encodings. -/
inductive MessageKind where
  | openChannel
  | acceptChannel
  | fundingCreated
  | channelReady
deriving Repr, DecidableEq, BEq

/-- A message is eventually delivered when it occurs in the trace.  This is the
smallest honest liveness object in the tree: it records which messages a
schedule eventually carries, without claiming when they are carried. -/
def EventuallyDelivered (trace : List MessageKind) (m : MessageKind) : Prop :=
  List.Mem m trace

/-- The concrete funding route. -/
def fundingRoute : List MessageKind :=
  [MessageKind.openChannel, MessageKind.acceptChannel,
   MessageKind.fundingCreated]

/-- The concrete route eventually carries `funding_created`. -/
theorem funding_created_eventually_delivered :
    EventuallyDelivered fundingRoute MessageKind.fundingCreated := by
  unfold EventuallyDelivered fundingRoute
  exact List.Mem.tail MessageKind.openChannel
    (List.Mem.tail MessageKind.acceptChannel (List.Mem.head []))

/-- A dropped-message trace does not carry `funding_created`. -/
theorem dropped_route_not_delivered :
    ¬ EventuallyDelivered [MessageKind.openChannel, MessageKind.acceptChannel]
      MessageKind.fundingCreated := by
  unfold EventuallyDelivered
  intro h
  cases h with
  | tail _ h' =>
      cases h' with
      | tail _ h'' => cases h''

/-- A schedule that delivers every message.  `delivery` is a static
capability in `LnLean.Security.Model`, so this is the fair/no-drop instance,
not a temporal fairness assumption. -/
def alwaysDelivers : NetworkSchedule :=
  { delivery := fun _ _ => true
    partition := fun _ _ => false
    maxDelay := 0
    reorders := false
    dropsMessages := false }

/-- A schedule that drops every message. -/
def neverDelivers : NetworkSchedule :=
  { delivery := fun _ _ => false
    partition := fun _ _ => false
    maxDelay := 0
    reorders := false
    dropsMessages := true }

/-- Static eventual-delivery capability: every message may reach every node. -/
def EventualDelivery (s : NetworkSchedule) : Prop :=
  ∀ (m : Nat) (n : NodeId), s.delivery m n = true

/-- The no-drop schedule satisfies the eventual-delivery predicate. -/
theorem alwaysDelivers_eventual : EventualDelivery alwaysDelivers := by
  intro m n
  rfl

/-- The dropping schedule does not. -/
theorem neverDelivers_not_eventual : ¬ EventualDelivery neverDelivers := by
  intro h
  have hbad : neverDelivers.delivery 0 0 = true := h 0 0
  simp [neverDelivers] at hbad

/-- The concrete NET-01 instance: the funding route reaches `funding_created`
under the no-drop schedule, while a dropping schedule fails already at the
capability level.  This does **not** prove protocol liveness: the next
obligation is a step-indexed retransmission model whose fairness predicate is
strong enough to derive `EventuallyDelivered` from a fair schedule. -/
theorem net01_eventual_delivery_instance :
    EventualDelivery alwaysDelivers ∧
      ¬ EventualDelivery neverDelivers ∧
      EventuallyDelivered fundingRoute MessageKind.fundingCreated ∧
      ¬ EventuallyDelivered [MessageKind.openChannel, MessageKind.acceptChannel]
        MessageKind.fundingCreated :=
  ⟨alwaysDelivers_eventual, neverDelivers_not_eventual,
   funding_created_eventually_delivered, dropped_route_not_delivered⟩

end LnLean.Proofs.Security.ChainFinalityTargets
