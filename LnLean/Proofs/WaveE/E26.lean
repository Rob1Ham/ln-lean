import LnLean.Routing.Gossip
import LnLean.Routing.Graph
import LnLean.Routing.Laws
import LnLean.Routing.Onion
import LnLean.Routing.Route

/-!
# Wave-E E26 — CLTV expiry accumulates by each hop's `cltv_expiry_delta`

Catalog: `LN-RT-005` — "The CLTV expiry at each hop increases by at least
that hop's `cltv_expiry_delta`."

BOLT anchors: BOLT 4 §Payload for the Last Node (`outgoing_cltv_value` is
the incoming expiry minus the forwarding node's delta); BOLT 7 §HTLC Fees
(`cltv_expiry_delta` is a per-direction field of the `channel_update`).

Model reading.  A `Route` is a list of hops in sender-to-recipient order.
The model stores only the per-hop delta (`Hop.cltvDelta`); the absolute
expiry values are not stored.  Therefore the expiry on the HTLC arriving at
hop `i`, when the recipient's expiry is `finalExpiry`, is the suffix sum

`incomingExpiry r finalExpiry i = finalExpiry + Σ_{j ≥ i} delta_j`,

which is exactly `Route.endExpiry finalExpiry` on the route suffix starting
at `i` (`Route.endExpiry` is the left fold `acc + delta`).  The per-hop law
is then: for `i < r.hops.length`,

`incomingExpiry r finalExpiry i = incomingExpiry r finalExpiry (i+1) + delta_i`,

i.e. crossing hop `i` lowers the required expiry by exactly its
`cltv_expiry_delta`; equivalently, read upstream, the expiry increases by at
least that delta.  No positivity hypothesis is needed for the "at least"
claim, because `cltvDelta : Nat` is non-negative.  Strictness for positive
deltas is a corollary.

`-- OBLIGATION:` marker below is the unique one for this module; the file
is complete and contains no unfinished proof.
-/

namespace LnLean.Proofs.WaveE.E26

open LnLean.Routing

set_option autoImplicit false

-- OBLIGATION: LN-WE-E26

/-! ## Expiry at a hop -/

/-- The CLTV expiry that must appear on the HTLC arriving at hop `i` of `r`,
when the recipient's final expiry is `finalExpiry`.

This is the model's `Route.endExpiry` applied to the suffix of the route
from hop `i` onwards: `endExpiry` folds `acc + hop.cltvDelta` over the hop
list.  For `i = 0` it is the sender-side expiry; for `i = r.hops.length` it
is `finalExpiry` (the recipient's expiry). -/
def incomingExpiry (r : Route) (finalExpiry i : Nat) : Nat :=
  (r.hops.drop i).foldl (fun acc h => acc + h.cltvDelta) finalExpiry

/-- `incomingExpiry` is the final expiry plus the sum of the deltas of the
hops from `i` onwards.  This is the `foldl_add_eq_sum` law of the model. -/
theorem waveE_e26_incomingExpiry_eq_sum (r : Route) (finalExpiry i : Nat) :
    incomingExpiry r finalExpiry i =
      finalExpiry + ((r.hops.drop i).map Hop.cltvDelta).sum :=
  Route.foldl_add_eq_sum (r.hops.drop i) finalExpiry

/-- At the start of the route, `incomingExpiry` is the model's `endExpiry`.
This ties the per-hop statement to the committed route-level accumulation
function. -/
@[simp] theorem waveE_e26_incomingExpiry_zero (r : Route) (finalExpiry : Nat) :
    incomingExpiry r finalExpiry 0 = r.endExpiry finalExpiry := by
  simp [incomingExpiry, Route.endExpiry]

/-- Past the last hop there is nothing left to add: the required expiry is
the recipient's final expiry. -/
@[simp] theorem waveE_e26_incomingExpiry_length (r : Route)
    (finalExpiry : Nat) :
    incomingExpiry r finalExpiry r.hops.length = finalExpiry := by
  simp [incomingExpiry]

/-- **Main law (exact form).**  For every hop `i` of a route, the expiry on
the HTLC arriving at hop `i` is the expiry on the HTLC arriving at the next
hop plus hop `i`'s `cltv_expiry_delta`.  Read from the recipient back
towards the sender, the expiry increases by exactly that delta. -/
theorem waveE_e26_cltv_accumulates_exact (r : Route) (finalExpiry : Nat)
    (i : Nat) (hi : i < r.hops.length) :
    incomingExpiry r finalExpiry i =
      incomingExpiry r finalExpiry (i + 1) + (r.hops[i]'hi).cltvDelta := by
  rw [waveE_e26_incomingExpiry_eq_sum, waveE_e26_incomingExpiry_eq_sum,
    List.drop_eq_getElem_cons hi]
  simp only [List.map_cons, List.sum_cons]
  omega

/-- **Main law (at-least form), catalog `LN-RT-005`.**  The CLTV expiry at
hop `i` is at least the expiry at the next hop plus hop `i`'s
`cltv_expiry_delta`.  No positivity hypothesis is required: `cltvDelta` is a
natural number, so the exact-step equality already gives the lower bound. -/
theorem waveE_e26_cltv_accumulates (r : Route) (finalExpiry : Nat)
    (i : Nat) (hi : i < r.hops.length) :
    incomingExpiry r finalExpiry (i + 1) + (r.hops[i]'hi).cltvDelta ≤
      incomingExpiry r finalExpiry i :=
  Nat.le_of_eq (waveE_e26_cltv_accumulates_exact r finalExpiry i hi).symm

/-- The sender-side expiry is the final expiry plus the route's total CLTV
delta.  This generalizes the model's zero-start `endExpiry_zero_eq_totalCltv`
to an arbitrary final expiry. -/
theorem waveE_e26_incomingExpiry_zero_eq_final_add_totalCltv (r : Route)
    (finalExpiry : Nat) :
    incomingExpiry r finalExpiry 0 = finalExpiry + r.totalCltv := by
  simp [Route.endExpiry, Route.totalCltv, Route.foldl_add_eq_sum]

/-- The expiry required at any hop is at least the recipient's final expiry:
accumulating non-negative deltas never lowers it. -/
theorem waveE_e26_incomingExpiry_ge_final (r : Route) (finalExpiry i : Nat) :
    finalExpiry ≤ incomingExpiry r finalExpiry i := by
  rw [waveE_e26_incomingExpiry_eq_sum]
  exact Nat.le_add_right _ _

/-- For a positive `cltv_expiry_delta`, one hop strictly increases the
expiry when read upstream. -/
theorem waveE_e26_cltv_step_strict (r : Route) (finalExpiry : Nat)
    (i : Nat) (hi : i < r.hops.length)
    (hpos : 0 < (r.hops[i]'hi).cltvDelta) :
    incomingExpiry r finalExpiry (i + 1) < incomingExpiry r finalExpiry i := by
  rw [waveE_e26_cltv_accumulates_exact r finalExpiry i hi]
  omega

/-- With every delta positive, the expiry strictly increases between any two
upstream indices: for `i < j`, the expiry at hop `i` is strictly larger than
at hop `j`.  This is the strict monotonicity corollary of the per-hop law. -/
theorem waveE_e26_cltv_strict_anti (r : Route) (finalExpiry : Nat)
    (hpos : ∀ h ∈ r.hops, 0 < h.cltvDelta) {i j : Nat}
    (hij : i < j) (hj : j ≤ r.hops.length) :
    incomingExpiry r finalExpiry j < incomingExpiry r finalExpiry i := by
  induction j with
  | zero => omega
  | succ j ih =>
    by_cases hEq : i = j
    · subst i
      exact waveE_e26_cltv_step_strict r finalExpiry j (by omega)
        (hpos _ (List.getElem_mem (by omega)))
    · have hij' : i < j := by omega
      have hj' : j ≤ r.hops.length := by omega
      have hstep : incomingExpiry r finalExpiry (j + 1) <
          incomingExpiry r finalExpiry j :=
        waveE_e26_cltv_step_strict r finalExpiry j (by omega)
          (hpos _ (List.getElem_mem (by omega)))
      exact Nat.lt_trans hstep (ih hij' hj')

/-! ## Bridge to the constructed route -/

/-- A hop built from a channel edge carries exactly that edge's
`cltv_expiry_delta`, so the per-hop law above is the BOLT 7 `channel_update`
field. -/
theorem waveE_e26_constructRoute_getElem_cltvDelta
    (path : List (ChannelEdge × Msat)) (amountMsat : Msat) (i : Nat)
    (hi : i < (constructRoute path amountMsat).hops.length) :
    ((constructRoute path amountMsat).hops[i]'hi).cltvDelta =
      (path[i]'(by simpa [constructRoute] using hi)).1.cltvDelta := by
  simp [constructRoute, List.getElem_map]

/-- Per-hop law specialized to a route constructed from a candidate path:
the expiry at hop `i` of the constructed route is the next hop's expiry plus
the `cltv_expiry_delta` of the underlying channel edge. -/
theorem waveE_e26_constructed_cltv_accumulates
    (path : List (ChannelEdge × Msat)) (amountMsat : Msat)
    (finalExpiry i : Nat)
    (hi : i < (constructRoute path amountMsat).hops.length) :
    incomingExpiry (constructRoute path amountMsat) finalExpiry i =
      incomingExpiry (constructRoute path amountMsat) finalExpiry (i + 1) +
        (path[i]'(by simpa [constructRoute] using hi)).1.cltvDelta := by
  rw [waveE_e26_cltv_accumulates_exact _ _ _ hi,
    waveE_e26_constructRoute_getElem_cltvDelta]

end LnLean.Proofs.WaveE.E26
