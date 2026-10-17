import LnLean.Routing.Route
import LnLean.Routing.Graph

/-!
# LnLean.Proofs.PhaseC2.CltvAccumulation

English claim.

For a BOLT 4 route `r` (`LnLean.Routing.Route`):

1. `Route.totalCltv` and `Route.endExpiry` are monotone in the hop list:
   prepending a hop or appending a route never decreases either quantity,
   and both components of a concatenation are bounded by the concatenation.
2. Prepending a hop with `0 < cltvDelta`, or appending a route containing
   such a hop, *strictly* increases `Route.totalCltv` and `Route.endExpiry`.
3. For a candidate path, `constructRoute` satisfies

   `(constructRoute path amount).endExpiry start
      = start + sum of the path's edge cltvDelta`s`,

   and the same sum is `(constructRoute path amount).totalCltv`.  In words:
   the constructed CLTV is the start height plus the sum of hop deltas.
4. Reversing a route reverses the accumulation order.  Since natural-number
   addition is commutative, the *final* expiry and the total delta are
   invariant under reversal
   (`endExpiry_reverse`, `totalCltv_reverse`); the order itself is exposed
   by `endExpiry_reverse_append` (concatenation flips) and by
   `endExpiry_reverse_appendHop` (an appended hop is accumulated first
   after reversal).  This is the correct orientation: `Route.endExpiry` is a
   left fold from `start`, so it adds deltas in list order, while the BOLT 4
   sender-side expiry is read right-to-left from the recipient; the present
   module proves the list-order algebra and does not claim a per-edge
   direction that the wave-A definition does not encode.

BOLT sections.

* BOLT 4, "Payloads" (`04-onion-routing.md:195-243`): `outgoing_cltv_value`
  increases by the forwarding node's delta at every hop.
* BOLT 7, "The `channel_update` Message" (`07-routing-gossip.md:454-457`):
  `cltv_expiry_delta`; and `:1031-1047`: the route CLTV is the sum of the
  hop deltas plus the final delta.

`rust-lightning` anchors at the pinned commit
`fe4900930c6bd5786ec4203274d7cf312776a5a6`.

* `lightning/src/routing/router.rs:90` — `RouteHop::cltv_expiry_delta`.
* `lightning/src/routing/router.rs:150` — `Route` (hop list and totals).
* `lightning/src/routing/router.rs:657` — per-hop CLTV delta used when
  building paths.
* `lightning/src/ln/onion_utils.rs:1050` — `build_onion_payloads` copies
  each hop's delta into `outgoing_cltv_value`.

What is **not** modelled.

* The final recipient's `min_final_cltv_expiry_delta` (the route-level sum
  here is over hop deltas only; adding the final delta is a separate
  additive offset).
* Integer overflow / block-height bounds: `Nat` addition is unbounded, so
  no `u32` truncation is claimed.  In particular no theorem here asserts
  that `start + totalCltv` fits a BOLT 4 wire integer.
* Fee/amount accumulation (see `LnLean.Routing.Route`), path optimality,
  liquidity, route blinding, MPP, and per-hop expiry *decrease* downstream;
  the latter is a right-to-left reading and is stated only as prose above.
-/

namespace LnLean.Proofs.PhaseC2

open LnLean.Routing

set_option autoImplicit false

/-! ## Auxiliary route constructions -/

/-- The route with the hop order reversed and the amount unchanged. -/
def reverseRoute (r : Route) : Route where
  hops := r.hops.reverse
  amountMsat := r.amountMsat

/-- The one-hop route carrying `amountMsat`. -/
def singletonRoute (h : Hop) (amountMsat : Msat) : Route where
  hops := [h]
  amountMsat := amountMsat

/-- Append one hop.  This is the appended-hop form used by the strict
monotonicity theorems; `Route.append` keeps the second route's amount, so
the appended singleton carries the same amount as `r`. -/
def appendHop (r : Route) (h : Hop) : Route :=
  r.append (singletonRoute h r.amountMsat)

@[simp] theorem reverseRoute_hops (r : Route) :
    (reverseRoute r).hops = r.hops.reverse := rfl

@[simp] theorem reverseRoute_amountMsat (r : Route) :
    (reverseRoute r).amountMsat = r.amountMsat := rfl

@[simp] theorem singletonRoute_hops (h : Hop) (amountMsat : Msat) :
    (singletonRoute h amountMsat).hops = [h] := rfl

@[simp] theorem singletonRoute_amountMsat (h : Hop) (amountMsat : Msat) :
    (singletonRoute h amountMsat).amountMsat = amountMsat := rfl

@[simp] theorem appendHop_hops (r : Route) (h : Hop) :
    (appendHop r h).hops = r.hops ++ [h] := rfl

@[simp] theorem appendHop_amountMsat (r : Route) (h : Hop) :
    (appendHop r h).amountMsat = r.amountMsat := rfl

theorem reverseRoute_involutive (r : Route) :
    reverseRoute (reverseRoute r) = r := by
  cases r with
  | mk hops amountMsat => simp [reverseRoute]

/-! ## Elementary accumulation identities -/

/-- The end expiry is the start height plus the total CLTV delta. -/
theorem endExpiry_eq_start_add_totalCltv (r : Route) (start : Nat) :
    r.endExpiry start = start + r.totalCltv := by
  simp [Route.endExpiry, Route.totalCltv, Route.foldl_add_eq_sum]

/-- A later start height gives a later (weakly larger) end expiry. -/
theorem endExpiry_mono_start (r : Route) {s t : Nat} (h : s ≤ t) :
    r.endExpiry s ≤ r.endExpiry t := by
  rw [endExpiry_eq_start_add_totalCltv, endExpiry_eq_start_add_totalCltv]
  omega

/-- Prepending a hop shifts the start height by that hop's delta. -/
theorem endExpiry_cons_eq (h : Hop) (r : Route) (start : Nat) :
    (r.cons h).endExpiry start = start + h.cltvDelta + r.totalCltv := by
  have hstep : (r.cons h).endExpiry start = r.endExpiry (start + h.cltvDelta) := by
    simp [Route.cons, Route.endExpiry, List.foldl_cons]
  rw [hstep, endExpiry_eq_start_add_totalCltv]

/-- Prepending a hop adds exactly that hop's delta to the total. -/
theorem totalCltv_cons_eq (h : Hop) (r : Route) :
    (r.cons h).totalCltv = h.cltvDelta + r.totalCltv :=
  Route.totalCltv_cons h r

/-- Appending a hop adds exactly that hop's delta to the total. -/
theorem appendHop_totalCltv (r : Route) (h : Hop) :
    (appendHop r h).totalCltv = r.totalCltv + h.cltvDelta := by
  rw [appendHop, Route.totalCltv_append]
  simp [singletonRoute, Route.totalCltv]

/-- Appending a hop adds exactly that hop's delta to the end expiry. -/
theorem appendHop_endExpiry (r : Route) (h : Hop) (start : Nat) :
    (appendHop r h).endExpiry start = r.endExpiry start + h.cltvDelta := by
  rw [appendHop, Route.endExpiry_append]
  have hsingle : (singletonRoute h r.amountMsat).endExpiry (r.endExpiry start) =
      r.endExpiry start + h.cltvDelta := by
    simp [singletonRoute, Route.endExpiry]
  rw [hsingle]

/-! ## Monotonicity in the hop list -/

/-- Prepending a hop never decreases the total CLTV delta. -/
theorem totalCltv_cons_le (h : Hop) (r : Route) :
    r.totalCltv ≤ (r.cons h).totalCltv := by
  rw [totalCltv_cons_eq]
  omega

/-- Prepending a hop with positive delta strictly increases the total. -/
theorem totalCltv_cons_strict (h : Hop) (r : Route) (hpos : 0 < h.cltvDelta) :
    r.totalCltv < (r.cons h).totalCltv := by
  rw [totalCltv_cons_eq]
  omega

/-- The left summand is bounded by the concatenated total. -/
theorem totalCltv_append_le_left (r₁ r₂ : Route) :
    r₁.totalCltv ≤ (r₁.append r₂).totalCltv := by
  rw [Route.totalCltv_append]
  omega

/-- The right summand is bounded by the concatenated total. -/
theorem totalCltv_append_le_right (r₁ r₂ : Route) :
    r₂.totalCltv ≤ (r₁.append r₂).totalCltv := by
  rw [Route.totalCltv_append]
  omega

/-- Appending a route with at least one positive delta strictly increases
the total. -/
theorem totalCltv_append_strict_right (r₁ r₂ : Route)
    (hne : r₂.hops ≠ [])
    (hpos : ∀ h ∈ r₂.hops, 0 < h.cltvDelta) :
    r₁.totalCltv < (r₁.append r₂).totalCltv := by
  rw [Route.totalCltv_append]
  have hsum : 0 < r₂.totalCltv := by
    have hstrict := Route.endExpiry_gt' r₂ 0 hne hpos
    rwa [Route.endExpiry_zero_eq_totalCltv] at hstrict
  omega

/-- Appending one positive-delta hop strictly increases the total. -/
theorem totalCltv_appendHop_strict (r : Route) (h : Hop)
    (hpos : 0 < h.cltvDelta) :
    r.totalCltv < (appendHop r h).totalCltv := by
  rw [appendHop_totalCltv]
  omega

/-- Prepending a hop never decreases the end expiry. -/
theorem endExpiry_cons_le (h : Hop) (r : Route) (start : Nat) :
    r.endExpiry start ≤ (r.cons h).endExpiry start := by
  rw [endExpiry_cons_eq, endExpiry_eq_start_add_totalCltv]
  omega

/-- Prepending a positive-delta hop strictly increases the end expiry. -/
theorem endExpiry_cons_strict (h : Hop) (r : Route) (start : Nat)
    (hpos : 0 < h.cltvDelta) :
    r.endExpiry start < (r.cons h).endExpiry start := by
  rw [endExpiry_cons_eq, endExpiry_eq_start_add_totalCltv]
  omega

/-- The left route's end expiry is bounded by the concatenated end expiry. -/
theorem endExpiry_append_le_left (r₁ r₂ : Route) (start : Nat) :
    r₁.endExpiry start ≤ (r₁.append r₂).endExpiry start := by
  rw [Route.endExpiry_append, endExpiry_eq_start_add_totalCltv r₂ (r₁.endExpiry start)]
  omega

/-- The right route's end expiry (from the same start) is bounded by the
concatenated end expiry. -/
theorem endExpiry_append_le_right (r₁ r₂ : Route) (start : Nat) :
    r₂.endExpiry start ≤ (r₁.append r₂).endExpiry start := by
  rw [Route.endExpiry_append]
  exact endExpiry_mono_start r₂ (by
    rw [endExpiry_eq_start_add_totalCltv]
    omega)

/-- Appending a route whose hops are all positive strictly increases the
end expiry. -/
theorem endExpiry_append_strict_right (r₁ r₂ : Route) (start : Nat)
    (hne : r₂.hops ≠ [])
    (hpos : ∀ h ∈ r₂.hops, 0 < h.cltvDelta) :
    r₁.endExpiry start < (r₁.append r₂).endExpiry start := by
  rw [Route.endExpiry_append]
  exact Route.endExpiry_gt' r₂ (r₁.endExpiry start) hne hpos

/-- Appending one positive-delta hop strictly increases the end expiry. -/
theorem endExpiry_appendHop_strict (r : Route) (h : Hop) (start : Nat)
    (hpos : 0 < h.cltvDelta) :
    r.endExpiry start < (appendHop r h).endExpiry start := by
  rw [appendHop_endExpiry]
  omega

/-! ## Constructed routes -/

/-- Mapping a candidate path to hops and then reading the hop delta is the
same as reading the edge delta directly. -/
theorem map_constructRoute_cltvDelta (path : List (ChannelEdge × Msat)) :
    (path.map fun ea => Hop.ofEdge ea.1 ea.2).map Hop.cltvDelta =
      path.map fun ea => ea.1.cltvDelta := by
  induction path with
  | nil => rfl
  | cons ea rest ih => simp [Hop.ofEdge]

/-- The total CLTV of a constructed route is the sum of the candidate
path's edge deltas. -/
theorem constructRoute_totalCltv (path : List (ChannelEdge × Msat))
    (amountMsat : Msat) :
    (constructRoute path amountMsat).totalCltv =
      (path.map fun ea => ea.1.cltvDelta).sum := by
  simpa [constructRoute, Route.totalCltv] using
    congrArg List.sum (map_constructRoute_cltvDelta path)

/-- **Constructed CLTV is the start height plus the sum of hop deltas.** -/
theorem constructRoute_endExpiry (path : List (ChannelEdge × Msat))
    (amountMsat : Msat) (start : Nat) :
    (constructRoute path amountMsat).endExpiry start =
      start + (path.map fun ea => ea.1.cltvDelta).sum := by
  rw [endExpiry_eq_start_add_totalCltv, constructRoute_totalCltv]

/-- Constructed end expiry written with the constructed route's own
`totalCltv`. -/
theorem constructRoute_endExpiry_eq_start_add_totalCltv
    (path : List (ChannelEdge × Msat)) (amountMsat : Msat) (start : Nat) :
    (constructRoute path amountMsat).endExpiry start =
      start + (constructRoute path amountMsat).totalCltv :=
  endExpiry_eq_start_add_totalCltv (constructRoute path amountMsat) start

/-- A non-empty candidate path all of whose edge deltas are positive has a
positive constructed total CLTV. -/
theorem constructRoute_totalCltv_pos (path : List (ChannelEdge × Msat))
    (amountMsat : Msat) (hne : path ≠ [])
    (hpos : ∀ p ∈ path, 0 < p.1.cltvDelta) :
    0 < (constructRoute path amountMsat).totalCltv := by
  rw [constructRoute_totalCltv]
  induction path with
  | nil => exact absurd rfl hne
  | cons ea rest ih =>
    by_cases hrest : rest = []
    · subst hrest
      simpa using hpos ea (by simp)
    · have hpos' : ∀ p ∈ rest, 0 < p.1.cltvDelta := by
        intro p hp
        exact hpos p (List.mem_cons_of_mem _ hp)
      have hrec := ih hrest hpos'
      simp only [List.map_cons, List.sum_cons]
      omega

/-- A non-empty candidate path with positive deltas strictly raises the
start height. -/
theorem constructRoute_endExpiry_strict (path : List (ChannelEdge × Msat))
    (amountMsat : Msat) (start : Nat) (hne : path ≠ [])
    (hpos : ∀ p ∈ path, 0 < p.1.cltvDelta) :
    start < (constructRoute path amountMsat).endExpiry start := by
  rw [constructRoute_endExpiry]
  have hsum := constructRoute_totalCltv_pos path amountMsat hne hpos
  rw [constructRoute_totalCltv] at hsum
  omega

/-- Constructed hops concatenate with the candidate path. -/
theorem constructRoute_append_hops (p₁ p₂ : List (ChannelEdge × Msat))
    (amountMsat : Msat) :
    (constructRoute (p₁ ++ p₂) amountMsat).hops =
      (constructRoute p₁ amountMsat).hops ++
        (constructRoute p₂ amountMsat).hops := by
  simp [constructRoute]

/-- Constructed total CLTV is additive over candidate-path concatenation. -/
theorem constructRoute_totalCltv_append (p₁ p₂ : List (ChannelEdge × Msat))
    (amountMsat : Msat) :
    (constructRoute (p₁ ++ p₂) amountMsat).totalCltv =
      (constructRoute p₁ amountMsat).totalCltv +
        (constructRoute p₂ amountMsat).totalCltv := by
  rw [constructRoute_totalCltv, constructRoute_totalCltv,
    constructRoute_totalCltv]
  simp [List.map_append, List.sum_append]

/-- Appending a non-empty positive-delta path suffix strictly increases the
constructed total CLTV. -/
theorem constructRoute_totalCltv_append_strict
    (p₁ p₂ : List (ChannelEdge × Msat)) (amountMsat : Msat)
    (hne : p₂ ≠ []) (hpos : ∀ p ∈ p₂, 0 < p.1.cltvDelta) :
    (constructRoute p₁ amountMsat).totalCltv <
      (constructRoute (p₁ ++ p₂) amountMsat).totalCltv := by
  rw [constructRoute_totalCltv_append]
  have hpos₂ := constructRoute_totalCltv_pos p₂ amountMsat hne hpos
  omega

/-- Constructed end expiry composes over candidate-path concatenation. -/
theorem constructRoute_endExpiry_append
    (p₁ p₂ : List (ChannelEdge × Msat)) (amountMsat : Msat) (start : Nat) :
    (constructRoute (p₁ ++ p₂) amountMsat).endExpiry start =
      (constructRoute p₂ amountMsat).endExpiry
        ((constructRoute p₁ amountMsat).endExpiry start) := by
  rw [constructRoute_endExpiry, constructRoute_endExpiry,
    constructRoute_endExpiry]
  simp [List.map_append, List.sum_append]
  omega

/-- Appending a non-empty positive-delta path suffix strictly increases the
constructed end expiry. -/
theorem constructRoute_endExpiry_append_strict
    (p₁ p₂ : List (ChannelEdge × Msat)) (amountMsat : Msat) (start : Nat)
    (hne : p₂ ≠ []) (hpos : ∀ p ∈ p₂, 0 < p.1.cltvDelta) :
    (constructRoute p₁ amountMsat).endExpiry start <
      (constructRoute (p₁ ++ p₂) amountMsat).endExpiry start := by
  rw [constructRoute_endExpiry_append,
    constructRoute_endExpiry p₂ amountMsat
      ((constructRoute p₁ amountMsat).endExpiry start)]
  have hpos₂ := constructRoute_totalCltv_pos p₂ amountMsat hne hpos
  rw [constructRoute_totalCltv] at hpos₂
  omega

/-! ## Reversal and accumulation order -/

/-- Reversing the hop list preserves the total CLTV delta. -/
theorem totalCltv_reverse (r : Route) :
    (reverseRoute r).totalCltv = r.totalCltv := by
  simp [reverseRoute, Route.totalCltv, List.map_reverse, List.sum_reverse]

/-- Reversing the hop list preserves the final expiry from a fixed start. -/
theorem endExpiry_reverse (r : Route) (start : Nat) :
    (reverseRoute r).endExpiry start = r.endExpiry start := by
  rw [endExpiry_eq_start_add_totalCltv (reverseRoute r) start,
    totalCltv_reverse r, endExpiry_eq_start_add_totalCltv r start]

/-- List-level form: folding `acc + delta` is invariant under reversal. -/
theorem foldl_add_reverse_eq (hops : List Hop) (start : Nat) :
    hops.reverse.foldl (fun acc h => acc + h.cltvDelta) start =
      hops.foldl (fun acc h => acc + h.cltvDelta) start := by
  rw [Route.foldl_add_eq_sum, Route.foldl_add_eq_sum]
  simp [List.map_reverse, List.sum_reverse]

/-- Concatenation flips under reversal.  Reading the reversed route
accumulates `r₂` first and `r₁` second. -/
theorem endExpiry_reverse_append (r₁ r₂ : Route) (start : Nat) :
    (reverseRoute (r₁.append r₂)).endExpiry start =
      (reverseRoute r₁).endExpiry ((reverseRoute r₂).endExpiry start) := by
  simp [reverseRoute, Route.append, Route.endExpiry, List.foldl_append]

/-- Prepending to a route becomes appending to the reversed route. -/
theorem reverseRoute_cons (h : Hop) (r : Route) :
    reverseRoute (r.cons h) = appendHop (reverseRoute r) h := by
  cases r with
  | mk hops amountMsat =>
    simp [reverseRoute, appendHop, singletonRoute, Route.cons, Route.append]

/-- Appending to a route becomes prepending to the reversed route. -/
theorem reverseRoute_appendHop (r : Route) (h : Hop) :
    reverseRoute (appendHop r h) = (reverseRoute r).cons h := by
  cases r with
  | mk hops amountMsat =>
    simp [reverseRoute, appendHop, singletonRoute, Route.cons, Route.append]

/-- An appended hop is accumulated *last* after reversal too: the reversed
route's end expiry is the original hop's delta added at the end. -/
theorem endExpiry_reverse_appendHop (r : Route) (h : Hop) (start : Nat) :
    (reverseRoute (appendHop r h)).endExpiry start =
      h.cltvDelta + (reverseRoute r).endExpiry start := by
  rw [reverseRoute_appendHop, endExpiry_cons_eq,
    endExpiry_eq_start_add_totalCltv (reverseRoute r) start]
  omega

/-- Symmetrically, a hop prepended to the original route is the first hop
of the reversed route and is accumulated first. -/
theorem endExpiry_reverse_cons (h : Hop) (r : Route) (start : Nat) :
    (reverseRoute (r.cons h)).endExpiry start =
      (reverseRoute r).endExpiry (start + h.cltvDelta) := by
  rw [reverseRoute_cons, appendHop_endExpiry,
    endExpiry_eq_start_add_totalCltv (reverseRoute r) (start + h.cltvDelta),
    endExpiry_eq_start_add_totalCltv (reverseRoute r) start]
  omega

end LnLean.Proofs.PhaseC2
