import LnLean.Routing.Graph

/-!
# LnLean.Routing.Route

BOLT 4 routes: a list of hops, each with the node reached, the
`short_channel_id` used, the fee charged, and the CLTV delta.

English claim of this module:

* `Hop` is one BOLT 4 route hop (`node_id`, `short_channel_id`,
  `fee_msat`, `cltv_expiry_delta`).
* `Route` is a non-empty list of hops plus the amount carried; its total
  fee is the sum of the per-hop fees, its total CLTV delta is the sum of the
  per-hop deltas, and its final expiry starting from `start` is the left
  fold of `start + delta` over the hops.
* `constructRoute` turns a path of `(ChannelEdge, amount)` pairs into a
  route whose hop count equals the path length and which is non-empty
  whenever the path is.
* `routeValid g r` requires the route to be non-empty and every hop to be
  backed by an enabled edge of `g` with the same `short_channel_id` and the
  hop's node as the edge destination.
* Fee and CLTV accumulation are *additive* and preserved by route
  concatenation; a strictly positive per-hop delta makes the accumulated
  expiry strictly increase.

BOLT sections:

* BOLT 4, "Routing" / "Route" (a route is a sequence of `(short_channel_id,
  node_id, fee, cltv_expiry_delta)` hops).
* BOLT 4, "Payloads" (`amt_to_forward` and `outgoing_cltv_value` decrease
  along the route; the final node receives the payment amount).
* BOLT 7, "The `channel_update` Message" (`fee_base_msat`,
  `fee_proportional_millionths`, `cltv_expiry_delta`).

`rust-lightning` anchors (pinned commit `fe4900930c6bd5786ec4203274d7cf312776a5a6`;
line numbers are anchored to the symbol, see `agents/reports/A6.md` for the
pin-verification caveat):

* `lightning/src/routing/router.rs:90` — `pub struct RouteHop` (fields
  `pubkey`, `channel_features`, `node_features`, `short_channel_id`,
  `channel_config`, `msat_fee`, `cltv_expiry_delta`).
* `lightning/src/routing/router.rs:150` — `pub struct Route` with
  `paths: Vec<Vec<RouteHop>>`, `get_total_fees`, and `get_total_amount`.
* `lightning/src/routing/router.rs:3110` — `Router::find_route`, which
  constructs the hop list and accumulates fees backwards from the payee.
* `lightning/src/ln/onion_utils.rs:1050` — `build_onion_payloads`, which
  copies each hop's fee and CLTV delta into the onion payload.

What is **not** modelled:

* Liquidity, capacity checks, and `htlc_maximum_msat`.
* The backwards fee computation with the amount at each hop.  `Hop.ofEdge`
  applies the proportional fee to the amount supplied for that hop; the
  caller chooses the amounts.  A full `find_route` needs the amount
  decreasing towards the payee, which is an obligation (`LN-ROUTE-FEE`).
* MPP splitting, route hints, route blinding, and the receiver's
  `min_final_cltv_expiry_delta`.
* Path optimality.  `constructRoute` validates a candidate path; it does
  not search for one.
-/

namespace LnLean.Routing

set_option autoImplicit false

/-! ## Hops -/

/-- One hop of a BOLT 4 route.

`node` is the node reached by this hop (the destination of
`shortChannelId`); the source of the route is implicit in the first edge.
`feeMsat` is the fee charged by this hop's forwarding node. -/
structure Hop where
  node : NodeId
  shortChannelId : ShortChannelId
  feeMsat : Msat
  cltvDelta : Nat
deriving Repr, DecidableEq, BEq

namespace Hop

/-- The BOLT 7 fee formula for this direction:
`fee_base_msat + ceil(amount_msat * fee_proportional_millionths / 1_000_000)`.

BOLT 7: "fee_proportional_millionths ... the amount paid is
`amount_msat * fee_proportional_millionths / 1000000`".  BOLT 7 leaves the
integer rounding of the division to the implementation.  This model rounds
the proportional term *up* (a conservative over-estimate for the payer) and
proves only the lower bound `fee >= fee_base`; it does **not** claim that
the rounded value matches `rust-lightning`'s arithmetic. -/
def ofEdge (e : ChannelEdge) (amountMsat : Msat) : Hop :=
  { node := e.node2
    shortChannelId := e.shortChannelId
    feeMsat := ⟨e.feeBaseMsat.val +
      (amountMsat.val * e.feeProportionalMillionths + 999999) / 1000000⟩
    cltvDelta := e.cltvDelta }

@[simp] theorem ofEdge_node (e : ChannelEdge) (a : Msat) :
    (ofEdge e a).node = e.node2 := rfl

@[simp] theorem ofEdge_scid (e : ChannelEdge) (a : Msat) :
    (ofEdge e a).shortChannelId = e.shortChannelId := rfl

@[simp] theorem ofEdge_cltvDelta (e : ChannelEdge) (a : Msat) :
    (ofEdge e a).cltvDelta = e.cltvDelta := rfl

/-- The computed fee is at least the advertised base fee. -/
theorem ofEdge_fee_ge_base (e : ChannelEdge) (a : Msat) :
    e.feeBaseMsat.val ≤ (ofEdge e a).feeMsat.val := by
  simp only [ofEdge]
  exact Nat.le_add_right _ _

/-- The expiry after forwarding this hop.  BOLT 4: the incoming CLTV is the
outgoing one plus `cltv_expiry_delta`. -/
def expiryAfter (h : Hop) (cltv : Nat) : Nat := cltv + h.cltvDelta

/-- A positive `cltv_expiry_delta` strictly increases the expiry. -/
theorem expiryAfter_strict (h : Hop) (cltv : Nat) (hpos : 0 < h.cltvDelta) :
    cltv < h.expiryAfter cltv := by
  simp only [expiryAfter]
  omega

end Hop

/-! ## Routes -/

/-- A BOLT 4 route.  The totals are derived functions over `hops`, so the
route cannot carry an inconsistent cached total. -/
structure Route where
  hops : List Hop
  amountMsat : Msat
deriving Repr, DecidableEq, BEq

namespace Route

/-- Total amount carried by the route (the payment amount). -/
def totalAmount (r : Route) : Msat := r.amountMsat

/-- Sum of the per-hop fees. -/
def totalFee (r : Route) : Msat :=
  ⟨(r.hops.map fun h => h.feeMsat.val).sum⟩

/-- Sum of the per-hop CLTV deltas. -/
def totalCltv (r : Route) : Nat :=
  (r.hops.map Hop.cltvDelta).sum

/-- Accumulated expiry at the end of the route, starting from `start`. -/
def endExpiry (r : Route) (start : Nat) : Nat :=
  r.hops.foldl (fun acc h => acc + h.cltvDelta) start

/-- A route is non-empty.  This is the BOLT 4 requirement that a payment
has at least one hop; it also rules out the degenerate "route to self". -/
def NonEmpty (r : Route) : Prop := r.hops ≠ []

/-- Concatenate two routes; the resulting amount is the second route's
amount (the first route carries the same payment to the join node). -/
def append (r₁ r₂ : Route) : Route :=
  { hops := r₁.hops ++ r₂.hops, amountMsat := r₂.amountMsat }

/-- Prepend one hop. -/
def cons (h : Hop) (r : Route) : Route :=
  { r with hops := h :: r.hops }

@[simp] theorem totalAmount_append (r₁ r₂ : Route) :
    (r₁.append r₂).totalAmount = r₂.totalAmount := rfl

/-- Fees add under concatenation. -/
theorem totalFee_append (r₁ r₂ : Route) :
    (r₁.append r₂).totalFee.val = r₁.totalFee.val + r₂.totalFee.val := by
  simp [append, totalFee, List.sum_append]

/-- Prepending a hop adds exactly that hop's fee. -/
theorem totalFee_cons (h : Hop) (r : Route) :
    (r.cons h).totalFee.val = h.feeMsat.val + r.totalFee.val := by
  simp [cons, totalFee, List.sum_cons]

/-- CLTV deltas add under concatenation. -/
theorem totalCltv_append (r₁ r₂ : Route) :
    (r₁.append r₂).totalCltv = r₁.totalCltv + r₂.totalCltv := by
  simp [append, totalCltv, List.sum_append]

/-- Prepending a hop adds exactly that hop's CLTV delta. -/
theorem totalCltv_cons (h : Hop) (r : Route) :
    (r.cons h).totalCltv = h.cltvDelta + r.totalCltv := by
  simp [cons, totalCltv, List.sum_cons]

/-- The accumulated expiry composes under concatenation. -/
theorem endExpiry_append (r₁ r₂ : Route) (start : Nat) :
    (r₁.append r₂).endExpiry start = r₂.endExpiry (r₁.endExpiry start) := by
  simp [append, endExpiry, List.foldl_append]

/-- Folding `acc + delta` equals `start + sum(deltas)`. -/
theorem foldl_add_eq_sum (hops : List Hop) (start : Nat) :
    hops.foldl (fun acc h => acc + h.cltvDelta) start =
      start + (hops.map Hop.cltvDelta).sum := by
  induction hops generalizing start with
  | nil => simp
  | cons h t ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih]
    omega

/-- The end expiry from zero is the total CLTV delta. -/
theorem endExpiry_zero_eq_totalCltv (r : Route) :
    r.endExpiry 0 = r.totalCltv := by
  simp [endExpiry, totalCltv, foldl_add_eq_sum]

/-- **CLTV strictly increases along a non-empty route** whose every hop has
a positive `cltv_expiry_delta`.  This is the accumulation form of the
per-hop law `Hop.expiryAfter_strict`. -/
theorem endExpiry_gt (hops : List Hop) (start : Nat) (hne : hops ≠ [])
    (hpos : ∀ h ∈ hops, 0 < h.cltvDelta) :
    start < hops.foldl (fun acc h => acc + h.cltvDelta) start := by
  induction hops generalizing start with
  | nil => exact absurd rfl hne
  | cons h t ih =>
    simp only [List.foldl_cons]
    by_cases ht : t = []
    · subst ht
      simp only [List.foldl_nil]
      have hh : 0 < h.cltvDelta := hpos h (by simp)
      omega
    · have hpos' : ∀ x ∈ t, 0 < x.cltvDelta := by
        intro x hx
        exact hpos x (List.mem_cons_of_mem _ hx)
      have hstep : start < start + h.cltvDelta := by
        have hh : 0 < h.cltvDelta := hpos h (by simp)
        omega
      exact Nat.lt_trans hstep (ih (start + h.cltvDelta) ht hpos')

/-- Route-level form of `endExpiry_gt`. -/
theorem endExpiry_gt' (r : Route) (start : Nat) (hne : r.NonEmpty)
    (hpos : ∀ h ∈ r.hops, 0 < h.cltvDelta) :
    start < r.endExpiry start :=
  endExpiry_gt r.hops start hne hpos

/-- A single hop's CLTV delta is at most the sum of all hop deltas. -/
theorem cltvDelta_le_sum {l : List Hop} {h : Hop} (hh : h ∈ l) :
    h.cltvDelta ≤ (l.map Hop.cltvDelta).sum := by
  induction l with
  | nil => simp at hh
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp hh with rfl | hmem
    · exact Nat.le_add_right _ _
    · have hle := ih hmem
      omega

/-- A single hop's CLTV delta is covered by the route's total CLTV delta. -/
theorem cltvDelta_le_totalCltv (r : Route) {h : Hop} (hh : h ∈ r.hops) :
    h.cltvDelta ≤ r.totalCltv := by
  simpa [totalCltv] using cltvDelta_le_sum hh

/-- **CLTV expiry accumulates by each hop's `cltv_expiry_delta`**
(catalog target `LnLean.Routing.Route.cltv_accumulates`, `LN-RT-005`).

Three facts, all without any positivity hypothesis (deltas are natural
numbers):

* the final expiry starting at `start` is exactly `start` plus the route's
  total CLTV delta: `start + r.totalCltv = r.endExpiry start`;
* every hop's `cltvDelta` is at most `r.totalCltv`, so the accumulated total
  covers each individual hop's delta;
* the prefix/step form: after taking `i` hops the expiry is `E`, and taking
  hop `i` next yields exactly `E + r.hops[i].cltvDelta`.  Hence the expiry at
  each hop increases by *at least* that hop's `cltv_expiry_delta` (in fact
  exactly it).  The step is an equality, which directly implies the catalog's
  "at least" wording. -/
theorem cltv_accumulates (r : Route) (start : Nat) :
    start + r.totalCltv = r.endExpiry start ∧
      (∀ h ∈ r.hops, h.cltvDelta ≤ r.totalCltv) ∧
      (∀ (i : Nat) (hi : i < r.hops.length),
        (r.hops.take i).foldl (fun acc h => acc + h.cltvDelta) start +
            (r.hops[i]'hi).cltvDelta =
          (r.hops.take (i + 1)).foldl (fun acc h => acc + h.cltvDelta) start) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [endExpiry, foldl_add_eq_sum, totalCltv]
  · intro h hh
    exact cltvDelta_le_totalCltv r hh
  · intro i hi
    rw [← List.take_append_getElem hi, List.foldl_append]
    simp

end Route

/-! ## Construction and validity -/

/-- Build a route from a candidate path.  Each element pairs a directed
edge with the amount carried over it; the hop's fee is computed from that
amount by `Hop.ofEdge`. -/
def constructRoute (path : List (ChannelEdge × Msat)) (amountMsat : Msat) :
    Route :=
  { hops := path.map fun ea => Hop.ofEdge ea.1 ea.2
    amountMsat := amountMsat }

@[simp] theorem constructRoute_hops (path : List (ChannelEdge × Msat))
    (amountMsat : Msat) :
    (constructRoute path amountMsat).hops =
      path.map (fun ea => Hop.ofEdge ea.1 ea.2) := rfl

/-- The hop count equals the candidate-path length. -/
theorem constructRoute_length (path : List (ChannelEdge × Msat))
    (amountMsat : Msat) :
    (constructRoute path amountMsat).hops.length = path.length := by
  simp [constructRoute]

/-- A non-empty candidate path yields a non-empty route. -/
theorem constructRoute_nonempty (e : ChannelEdge × Msat)
    (path : List (ChannelEdge × Msat)) (amountMsat : Msat) :
    (constructRoute (e :: path) amountMsat).hops ≠ [] := by
  simp [constructRoute]

/-- The total fee of a constructed route is the sum of its hop fees. -/
theorem constructRoute_totalFee (path : List (ChannelEdge × Msat))
    (amountMsat : Msat) :
    (constructRoute path amountMsat).totalFee.val =
      ((path.map fun ea => Hop.ofEdge ea.1 ea.2).map
        fun h => h.feeMsat.val).sum := rfl

/-- A route is valid in a graph when it is non-empty and every hop is backed
by an enabled graph edge with the same `short_channel_id`, ending at the
hop's node.  This is the graph-level check performed by
`rust-lightning`'s router before a payment is sent. -/
def routeValid (g : Graph) (r : Route) : Prop :=
  r.NonEmpty ∧ ∀ h ∈ r.hops, ∃ e ∈ g.edges,
    e.enabled = true ∧ e.shortChannelId = h.shortChannelId ∧ e.node2 = h.node

/-- Validity entails non-emptiness. -/
theorem routeValid_nonempty {g : Graph} {r : Route} (h : routeValid g r) :
    r.NonEmpty := h.1

/-- **Edge lookup soundness at the route level.**  Every hop of a valid
route has an enabled backing edge in the graph. -/
theorem routeValid_edge_sound {g : Graph} {r : Route} (h : routeValid g r) :
    ∀ hop ∈ r.hops, ∃ e ∈ g.edges,
      e.enabled = true ∧ e.shortChannelId = hop.shortChannelId ∧
        e.node2 = hop.node := h.2

/-- A candidate path whose edges are enabled members of `g` constructs a
valid route. -/
theorem constructRoute_valid (g : Graph) (path : List (ChannelEdge × Msat))
    (amountMsat : Msat) (hne : path ≠ [])
    (hmem : ∀ p ∈ path, p.1 ∈ g.edges)
    (hen : ∀ p ∈ path, p.1.enabled = true) :
    routeValid g (constructRoute path amountMsat) := by
  constructor
  · simp [Route.NonEmpty, constructRoute, hne]
  · intro h hh
    simp only [constructRoute_hops] at hh
    rcases List.mem_map.mp hh with ⟨⟨e, a⟩, hp, rfl⟩
    exact ⟨e, hmem (e, a) hp, hen (e, a) hp, rfl, rfl⟩

/-- `findEdge` witnesses are enough to validate a one-edge route: the
engineered counterpart of `Graph.findEdge_sound`. -/
theorem findEdge_route_valid (g : Graph) (fromNode toNode : NodeId)
    (amountMsat : Msat) (e : ChannelEdge)
    (h : g.findEdge fromNode toNode = some e) :
    routeValid g (constructRoute [(e, amountMsat)] amountMsat) := by
  apply constructRoute_valid
  · simp
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst hp
    exact (Graph.findEdge_sound h).1
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst hp
    exact (Graph.findEdge_sound h).2.1

end LnLean.Routing
