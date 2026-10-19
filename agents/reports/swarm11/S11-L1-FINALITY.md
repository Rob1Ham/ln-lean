# S11-L1-FINALITY — explicit block/chain finality model for `L1-06`

**Lane:** `S11-L1-FINALITY`
**Branch:** `repair/integrated`
**Owned Lean file:** `LnLean/Proofs/Security/ChainFinalityTargets.lean`
**Owned report:** `agents/reports/swarm11/S11-L1-FINALITY.md`
**Issues:** `L1-06` (`LN-L1-003`), optional `NET-01`

No existing Lean file, root import, catalog, traceability file, audit list,
docs, scripts, or tests were edited. Nothing was committed or pushed.

## 1. Result

`L1-06` previously observed that `ReorgTargets.reorg_preserves_channel_safety`
was conditional on `SameChain` and on the abstract confirmation arithmetic in
`InCommonPrefix`/`Observations.OutOfReachOf`, with no block-level chain object
behind those predicates. This lane adds the missing finite graph model and
proves the finality statement directly on it.

The new module provides:

1. a concrete `Block`/`Chain` graph (`height`, `parent`, `hash`, linked-spine
   `WellFormed`, `PrefixOf`, `CommonAncestor`, `SharesPrefix`, `ReorgWithin`);
2. a bounded-depth finality theorem for a block
   (`bounded_depth_finality`) and for a transaction/output commitment
   (`confirmed_tx_not_reorged`), plus the unique-canonical-tip family form
   (`unique_tip_finality`);
3. a sharp deep-reorg counterexample (`deep_reorg_evicts`) and the
   counterexample that the depth bound is necessary
   (`depth_bound_necessary`);
4. a small concrete chain with a non-vacuous surviving transaction
   (`smallTx_not_reorged`), two rejection cases
   (`smallTipTx_rejected`, `smallTx_rejected_without_prefix`), and a
   compact summary (`small_witness_summary`);
5. direct transfers from the existing `SameChain`, `InCommonPrefix`,
   `reorgSurvives`, and `Observations.OutOfReachOf` predicates into
   graph-level prefix statements, without restating their hypotheses; and
6. one small `NET-01` eventual-delivery instance, explicitly labelled as a
   static capability result rather than protocol liveness.

There is no `LnLean/Bitcoin/ChainTargets.lean` in this tree. The L1 directory
`LnLean/Bitcoin/` contains `Funding`, `Laws`, `ScriptTemplates`, `Seam`, and
`Sighash`, but no block/chain graph. The vendored `Bitcoin.Chain.Basic` exposes
only `BlockHeader` and compact-target arithmetic. Consequently the graph in
this module is new and self-contained; it does not claim to refine a nonexistent
`LnLean.Bitcoin.Chain` module.

## 2. Graph model

| Item | Line | Meaning |
|---|---:|---|
| `Block` | 63 | `hash : Nat`, `parent : Option Nat`, `height : Nat`. Hash and parent identities are abstract natural numbers, not cryptographic hashes. |
| `Chain` | 72 | finite list of blocks; list position is the block height. |
| `Chain.length` | 79 | number of blocks. |
| `Chain.blockAt` | 82 | `c.blocks[h]?`; the only block lookup. |
| `Chain.tipHeight` | 86 | `length - 1`. |
| `Chain.confirmations` | 90 | `length - h`; the block at `h` counts itself. |
| `Chain.depth` | 94 | `length - 1 - h`; blocks strictly above `h`. |
| `Chain.ConfirmedAtDepth` | 99 | `d < c.confirmations h`, i.e. at least `d + 1` confirmations / depth at least `d`. |
| `Chain.PrefixOf` | 104 | `∃ rest, c.blocks = a.blocks ++ rest`. |
| `Chain.CommonAncestor` | 108 | one prefix of both descendants. |
| `Chain.SharesPrefix` | 113 | pointwise equality below a length. |
| `Chain.ReorgWithin` | 119 | `SharesPrefix c c' (c.length - d)`, i.e. a reorg removing at most the last `d` blocks. |
| `Chain.WellFormed` | 133 | linked spine: genesis has `parent = none` and height `0`; every later block points at its predecessor with the next height. |

`Chain.WellFormed` is a structural property of the finite witnesses. The core
finality theorem does **not** assume it: finality is a prefix/depth statement.
Well-formedness is proved for every concrete witness
(`smallChain_wellFormed`, `smallAlt_wellFormed`, `otherChain_wellFormed`,
`deepChain_wellFormed`, `deepFork_wellFormed`).

## 3. Main theorems

| Theorem | Line | Statement |
|---|---:|---|
| `bounded_depth_finality` | 256 | If `a` is a common ancestor of `c` and `c'`, `c.length - a.length ≤ d`, and `c` confirms height `h` at depth `d`, then `c.blockAt h = c'.blockAt h`. |
| `bounded_depth_finality_symm` | 272 | Symmetric block equality. |
| `bounded_depth_finality_of_reorgWithin` | 282 | The same result in the height-indexed `ReorgWithin` form. |
| `confirmed_tx_not_reorged` | 331 | A `ConfirmedTx` at depth `d` on `c` remains `OnChain` in `c'` under the same common-ancestor/depth hypotheses. |
| `unique_tip_finality` | 362 | Family form over `UniqueCanonicalTip`: the transaction remains on the canonical chain's competitor and the competitor is no longer than the canonical chain. |
| `unique_canonical_tip_eq` | 348 | Equal-length members of the unique-tip family have the canonical block list. |
| `canonical_tip_max_length` | 354 | No family member is longer than the canonical chain. |

The arithmetic core is three lemmas:

* `Chain.lt_length_of_confirmedAtDepth` (line 224);
* `Chain.lt_length_sub_of_confirmedAtDepth` (line 231);
* `Chain.confirmedAtDepth_iff_depth_le` (line 217).

The proof of `bounded_depth_finality` is:

```text
ConfirmedAtDepth c h d
  ⇒ h < c.length - d
  ⇒ h < a.length                 (using c.length - a.length ≤ d)
  ⇒ c.blockAt h = a.blockAt h    (a is a prefix of c)
  ⇒ c'.blockAt h = a.blockAt h   (a is a prefix of c')
  ⇒ c.blockAt h = c'.blockAt h
```

## 4. Non-vacuity witness

The small chain is three blocks (`100`, `101`, `102`); `smallAlt` replaces
only the tip with `202`; `smallPrefix` is the two-block common prefix.

| Fact | Theorem | Line |
|---|---|---:|
| Canonical chain length | `smallChain_length` | 546 |
| Tip hash of the fork | `smallAlt_tip_hash` | 549 |
| Shared prefix | `small_commonAncestor` | 575 |
| Reorg removes one block, bound is two | `small_chain_depthBound` | 581 |
| Genesis transaction at depth two | `smallTx_confirmedAtDepth` | 585 |
| Genesis transaction on canonical chain | `smallTx_onChain` | 589 |
| **Survives the one-block tip replacement** | `smallTx_not_reorged` | 597 |
| Fork is distinct from canonical chain | `smallAlt_ne_smallChain` | 602 |

This witness is not reflexive: `smallAlt ≠ smallChain`, and the transaction
is still present on `smallAlt`.

Rejection cases:

* `smallTipTx_onChain` (line 611) + `smallTipTx_not_confirmedAtDepth`
  (line 617): a transaction at the tip has one confirmation, not depth two.
* `smallTipTx_rejected` (line 624): that tip transaction is absent from
  `smallAlt`; both the conclusion and the failed depth hypothesis are recorded.
* `smallTx_rejected_without_prefix` (line 638): the same genesis transaction
  is absent from `otherChain`, a well-formed chain with an unrelated genesis
  block. This shows the common-prefix hypothesis is load-bearing.
* `small_witness_summary` (line 649): conjunction of the positive, negative,
  and well-formedness facts.

## 5. Deep-reorg counterexample and necessity

`deepChain` is a six-block spine `100`…`105`; `deepFork` shares the first
three blocks and replaces heights three through five with `203`…`205`;
`deepPrefix` is the three-block common ancestor. `deepTx` is confirmed in
block `103` at height three.

| Fact | Theorem | Line |
|---|---|---:|
| Canonical chain well formed | `deepChain_wellFormed` | 694 |
| Fork well formed | `deepFork_wellFormed` | 698 |
| Three-block common ancestor | `deep_commonAncestor` | 702 |
| Fork removes three canonical blocks | `deep_reorg_depth` | 712 |
| Transaction at depth two | `deepTx_confirmedAtDepth` | 722 |
| Transaction is not at depth three | `deepTx_not_confirmedAtDepth_three` | 726 |
| Bound `2` is violated | `deep_bound_violated` | 731 |
| Transaction absent from fork | `deepTx_not_on_fork` | 735 |
| **Depth-two transaction evicted by depth-three fork** | `deep_reorg_evicts` | 748 |
| Exact boundary: 3 confirmations, depth 2, reorg 3 | `deep_boundary_is_sharp` | 759 |
| **No depth bound ⇒ conclusion false** | `depth_bound_necessary` | 772 |

`depth_bound_necessary` has the form

```lean
∃ (a c c' : Chain) (t : ConfirmedTx) (d : Nat),
  Chain.CommonAncestor a c c' ∧
  t.OnChain c ∧
  c.ConfirmedAtDepth t.height d ∧
  ¬ (c.length - a.length ≤ d) ∧
  ¬ t.OnChain c'
```

This is the exact counterexample to the unconditional reading: the
transaction is confirmed at the stated depth and has a common ancestor, but
the removed suffix is longer than the depth bound and the transaction is gone
from the fork. The bound in `bounded_depth_finality` is therefore necessary,
not a convenience hypothesis.

## 6. Connection to `ReorgTargets` and preserved hypotheses

The existing abstract predicates are not redefined. They are characterized by
the graph model:

| Existing predicate | Bridge theorem | Line |
|---|---|---:|
| `SameChain` | `sameChain_view_of_length_eq` | 391 |
| `SameChain` → survival agreement | `sameChain_survival_transfer` | 401 |
| `reorgSurvives` | `reorgSurvives_iff_chain_prefix` | 409 |
| `InCommonPrefix` | `inCommonPrefix_iff_chain_prefix` | 419 |
| `reorgSurvives` → block equality | `finality_from_reorgSurvives` | 429 |
| `Observations.OutOfReachOf` | `outOfReachOf_iff_chain_prefix` | 447 |
| `OutOfReachOf` + common ancestor → per-fact block equality | `retained_fact_of_commonAncestor_depth` | 470 |
| retention + finality composed | `chain_finality_and_retention` | 488 |

`chain_finality_and_retention` is the direct replacement for the abstract
catalog statement at the graph level:

```lean
Retains o (o.applyReorgAt c.tipHeight r) ∧
∀ e ∈ o.facts, c.blockAt e.height = c'.blockAt e.height
```

under the preserved hypotheses

```lean
Chain.CommonAncestor a c c'
c.length - a.length ≤ r.depth
0 < c.length
o.OutOfReachOf (c.view chainTipTag none) r
```

The nonempty-chain hypothesis is only needed to identify
`Chain.tipHeight + 1` with `c.length` in the `ReorgTargets` arithmetic. The
ledger-retention conjunct still comes from the existing
`ReorgTargets.reorg_retains_of_depth_bound`; this lane does not duplicate or
weaken it.

## 7. `NET-01` optional instance

The `NET-01` addition is deliberately small and explicitly scoped:

| Item | Line |
|---|---:|
| `MessageKind` | 800 |
| `EventuallyDelivered` | 810 |
| `fundingRoute` | 814 |
| `funding_created_eventually_delivered` | 819 |
| `dropped_route_not_delivered` | 826 |
| `alwaysDelivers` | 839 |
| `neverDelivers` | 847 |
| `EventualDelivery` | 855 |
| `alwaysDelivers_eventual` | 859 |
| `neverDelivers_not_eventual` | 864 |
| `net01_eventual_delivery_instance` | 874 |

This is a concrete eventual-delivery capability instance: a no-drop schedule
carries `open_channel → accept_channel → funding_created`, while a drop-all
schedule does not. It does **not** prove protocol liveness. `NetworkSchedule`
has no time or retry index (`delivery : Nat → NodeId → Bool` is a static
capability relation), so a real liveness theorem needs a step-indexed
retransmission model and a fairness predicate. The exact next obligation is
recorded in §10.

## 8. Verification

### Build

Exact command:

```sh
cd /home/ubuntu/ln-lean-repair && \
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Proofs.Security.ChainFinalityTargets
```

Result:

```text
✔ [12/12] Built LnLean.Proofs.Security.ChainFinalityTargets (2.2s)
Build completed successfully (12 jobs).
RC=0
```

No warnings remain from the final build.

### Forbidden-token scan

Scan over the new Lean file:

```sh
grep -nE '\b(axiom|native_decide|unsafe|admit|sorry)\b|@\[implemented_by\]' \
  LnLean/Proofs/Security/ChainFinalityTargets.lean
```

Result: **no matches**. The file contains no `sorry`, `axiom`, `admit`,
`native_decide`, `unsafe`, or `@[implemented_by]`.

`python3 scripts/check.py` also reports:

```text
files=272 obligations=82 sorry_in_proofs=0
check: OK
```

The lane did not duplicate the existing `LN-L1-003` obligation marker, so the
obligation-id check stays green without editing `ReorgTargets.lean`.

### Axiom audit

A temporary audit file imported the module and ran `#print axioms` on all 68
public theorem declarations (`/tmp/opencode/cf_audit.lean`). Result:
68/68 audited, no errors. The only axiom sets observed were:

```text
does not depend on any axioms       10 theorems
[propext]                            ...
[propext, Quot.sound]                ...
[propext, Quot.sound, Classical.choice]  ...
```

No theorem depends on any axiom outside the permitted
`propext`, `Quot.sound`, `Classical.choice` set. No `sorryAx` or other
unexpected constant appears. The `Classical.choice` occurrences come from
decidable arithmetic/proof automation in the concrete witness section, not
from a classical existence assumption in the finality statement.

## 9. Assumptions and explicit boundaries

The module states the following assumptions in types rather than hiding them:

1. **Common ancestor.** Finality is relative to
   `Chain.CommonAncestor a c c'`. The theorem does not derive a common
   ancestor from a consensus rule.
2. **Bounded removed suffix.** `c.length - a.length ≤ d`. This is the
   graph-level form of "the reorg stays within depth `d`."
3. **Confirmation depth.** `c.ConfirmedAtDepth t.height d`, i.e.
   `d < c.length - t.height`. For `d = 0`, one confirmation suffices.
4. **Nonempty canonical chain** for the `ReorgTargets` bridges
   (`0 < c.length`). Empty chains have truncated subtraction and are outside
   the intended use.
5. **Unique canonical tip** for `unique_tip_finality`: the canonical chain is
   in the finite family, no member is longer, and equal-length members are
   the same block list. The finality conclusion itself still depends only on
   the prefix/death bound; the uniqueness hypothesis rules out a longer
   competing tip in the family statement.
6. **No cryptographic hash claim.** `Block.hash : Nat` is an opaque identity.
   The result is about graph retention, not collision resistance.
7. **No consensus/PoW/transaction-validity claim.** The model has no
   chainwork, proof of work, timestamps, transaction validity, fee market, or
   double-spend economics. Actual theft after a deep reorg remains the
   separate `LN-CHAIN-REORG` obligation, exactly as in `ReorgTargets`.
8. **No probabilistic model.** There is no reorg probability or
   polynomial-time adversary; this is a structural conditional theorem.

The "output" form is represented by `ConfirmedTx.OnChain`. `ConfirmedTx`
records `txid`, `blockHash`, and `height`; it is a transaction/output
commitment at a block height, not a full `Bitcoin.Data.Tx` or script-spend
proof. This is faithful to `LN-L1-003`'s retention question but does not add
consensus validity.

## 10. Recommended target list for `LN-L1-003` / `LN-L1-006` / `NET-01`

### `LN-L1-003` / `L1-06`

The catalog row can be strengthened with:

* `ChainFinalityTargets.bounded_depth_finality`
* `ChainFinalityTargets.confirmed_tx_not_reorged`
* `ChainFinalityTargets.unique_tip_finality`
* `ChainFinalityTargets.depth_bound_necessary`
* `ChainFinalityTargets.deep_reorg_evicts`
* `ChainFinalityTargets.smallTx_not_reorged`
* `ChainFinalityTargets.smallTipTx_rejected`
* `ChainFinalityTargets.smallTx_rejected_without_prefix`
* `ChainFinalityTargets.chain_finality_and_retention`
* `ChainFinalityTargets.outOfReachOf_iff_chain_prefix`

Recommended catalog wording to add: "A finite linked block graph with a
common ancestor supplies the missing L1 chain object; a transaction confirmed
at depth `d` survives every competing chain whose removed canonical suffix is
at most `d`, and a depth-`d+1` fork has a concrete counterexample. The
graph result is connected to the existing `SameChain`/`InCommonPrefix`/
`OutOfReachOf` hypotheses, which remain explicit."

`L1-06` can move from **open (conditional)** to **closed for the finite graph
model**, provided the catalog keeps the following scope note: no PoW,
chainwork, transaction-validity, probabilistic, or live-chain claim is made.
The remaining real-chain obligation stays `LN-CHAIN-REORG`.

### `NET-01`

The optional instance supports only the static eventual-delivery vocabulary:

* `ChainFinalityTargets.net01_eventual_delivery_instance`
* `ChainFinalityTargets.funding_created_eventually_delivered`
* `ChainFinalityTargets.dropped_route_not_delivered`
* `ChainFinalityTargets.alwaysDelivers_eventual`

`NET-01` should remain **open**. Exact next obligation: replace the static
`NetworkSchedule.delivery` capability with a step-indexed trace/retransmission
relation and a fairness predicate over steps, then prove

```text
fair schedule ⇒ every funding-route message is eventually delivered
              ⇒ the peer reaches the next protocol state
```

with an explicit adversarial scheduling model. The current `delivery` field
has no time index, so `net01_eventual_delivery_instance` must not be cited as
protocol liveness.

### Integration notes for the parent

1. Add a root import for
   `LnLean.Proofs.Security.ChainFinalityTargets` when integrating the lane
   (this lane did not edit the root import).
2. Add the target list above to the catalog/traceability update for
   `LN-L1-003`; keep `LN-CHAIN-REORG` and the no-PoW/no-probability caveats
   visible.
3. Add the module to the axiom-audit theorem list if the gate enumerates
   theorem names explicitly; all 68 public theorems are already checked here.
4. Do not cite `NET-01` as closed. The static instance is evidence for the
   delivery vocabulary only.

## Appendix: complete public theorem inventory

All declarations below are in
`LnLean.Proofs.Security.ChainFinalityTargets` (names inside `namespace Chain`
and `namespace ConfirmedTx` are shown with the namespace prefix).

| Line | Theorem |
|---:|---|
| 143 | `Chain.prefixOf_refl` |
| 147 | `Chain.prefixOf_trans` |
| 156 | `Chain.length_le_of_prefix` |
| 165 | `Chain.blockAt_eq_of_prefix` |
| 176 | `Chain.commonAncestor_comm` |
| 181 | `Chain.commonAncestor_refl` |
| 185 | `Chain.commonAncestor_mono` |
| 191 | `Chain.sharesPrefix_refl` |
| 195 | `Chain.sharesPrefix_mono` |
| 201 | `Chain.sharesPrefix_of_commonAncestor` |
| 209 | `Chain.confirmations_eq_depth_add_one` |
| 217 | `Chain.confirmedAtDepth_iff_depth_le` |
| 224 | `Chain.lt_length_of_confirmedAtDepth` |
| 231 | `Chain.lt_length_sub_of_confirmedAtDepth` |
| 237 | `Chain.confirmedAtDepth_mono` |
| 256 | `bounded_depth_finality` |
| 272 | `bounded_depth_finality_symm` |
| 282 | `bounded_depth_finality_of_reorgWithin` |
| 309 | `ConfirmedTx.onChain_of_blockAt_eq` |
| 317 | `ConfirmedTx.onChain_congr` |
| 331 | `confirmed_tx_not_reorged` |
| 348 | `unique_canonical_tip_eq` |
| 354 | `canonical_tip_max_length` |
| 362 | `unique_tip_finality` |
| 391 | `sameChain_view_of_length_eq` |
| 401 | `sameChain_survival_transfer` |
| 409 | `reorgSurvives_iff_chain_prefix` |
| 419 | `inCommonPrefix_iff_chain_prefix` |
| 429 | `finality_from_reorgSurvives` |
| 447 | `outOfReachOf_iff_chain_prefix` |
| 470 | `retained_fact_of_commonAncestor_depth` |
| 488 | `chain_finality_and_retention` |
| 546 | `smallChain_length` |
| 549 | `smallAlt_tip_hash` |
| 553 | `smallChain_wellFormed` |
| 557 | `smallAlt_wellFormed` |
| 561 | `otherChain_wellFormed` |
| 565 | `smallPrefix_prefix_smallChain` |
| 570 | `smallPrefix_prefix_smallAlt` |
| 575 | `small_commonAncestor` |
| 581 | `small_chain_depthBound` |
| 585 | `smallTx_confirmedAtDepth` |
| 589 | `smallTx_onChain` |
| 597 | `smallTx_not_reorged` |
| 602 | `smallAlt_ne_smallChain` |
| 611 | `smallTipTx_onChain` |
| 617 | `smallTipTx_not_confirmedAtDepth` |
| 624 | `smallTipTx_rejected` |
| 638 | `smallTx_rejected_without_prefix` |
| 649 | `small_witness_summary` |
| 694 | `deepChain_wellFormed` |
| 698 | `deepFork_wellFormed` |
| 702 | `deep_commonAncestor` |
| 712 | `deep_reorg_depth` |
| 716 | `deepTx_onChain` |
| 722 | `deepTx_confirmedAtDepth` |
| 726 | `deepTx_not_confirmedAtDepth_three` |
| 731 | `deep_bound_violated` |
| 735 | `deepTx_not_on_fork` |
| 748 | `deep_reorg_evicts` |
| 759 | `deep_boundary_is_sharp` |
| 772 | `depth_bound_necessary` |
| 786 | `deep_witness_summary` |
| 819 | `funding_created_eventually_delivered` |
| 826 | `dropped_route_not_delivered` |
| 859 | `alwaysDelivers_eventual` |
| 864 | `neverDelivers_not_eventual` |
| 874 | `net01_eventual_delivery_instance` |

**Total:** 68 public theorems, 0 `sorry`, 0 forbidden constructs, 68/68
axiom-audited with only `propext`, `Quot.sound`, and `Classical.choice`.
