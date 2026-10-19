import LnLean.Routing.Route

/-!
# LnLean.Proofs.Wave14.RouteFeeCapacity

Additive route fee-rounding and capacity/min-max usability layer for the
Wave-13 review gaps G13/G14 (`REV-07` fee rounding; `REV-04`/G14 capacity),
R32 §3 G13/G14 and §4 T4's boundary note.

**Nothing in this module changes an existing carrier.**  In particular:

* `LnLean.Routing.Hop.ofEdge` still rounds the proportional term **up** and
  keeps its old docstring and its consumers (`Hop.ofEdge_node`,
  `Hop.ofEdge_fee_ge_base`, `Route.constructRoute_*`,
  `Route.routeValid_edge_sound`, `Route.constructRoute_valid`, ...);
* `LnLean.Routing.Route.routeValid` is untouched (it remains the per-hop
  predicate);
* `LnLean.Proofs.Routing.RouteBlindingProps.ofEdge_rounding_counterexample`
  is retained unchanged in its own module; this file does not import or
  restate it as a replacement.

## Fee rounding (G13 / `REV-07`)

BOLT 7 leaves integer rounding of
`amount_msat * fee_proportional_millionths / 1000000` to the
implementation.  `rust-lightning`'s router truncates (LDK datapoint D3,
`lightning/src/routing/router.rs:2639-2642`), whereas `Hop.ofEdge` uses the
ceiling `(x + 999999) / 1000000`.  The additive function
`Hop.ofEdgeFloor` is the truncating counterpart.  It is a *separate* function,
not a redefinition of `ofEdge`.

`floor_vs_ceiling_separates` gives a concrete amount where the two disagree:
with `fee_base_msat = 0`, `fee_proportional_millionths = 1000` and
`amount_msat = 1500`, the proportional product is `1_500_000`, so the
truncating fee is `1` and `ofEdge`'s ceiling fee is `2`.  This is a
floor/ceiling separation, not a claim that LDK's full router arithmetic (which
also handles base fees, path-level amounts, and fee spillover) is reproduced.

## Capacity and HTLC min/max usability (G14)

`LnLean.Routing.ChannelEdge` carries `capacitySat` but no
`htlc_minimum_msat` or `htlc_maximum_msat`.  `EdgeCapacity` is an **additive
carrier**, not a replacement for `ChannelEdge`: it wraps one directed edge and
adds the three BOLT 7 quantities `capacityMsat`, `htlcMinimumMsat`, and
`htlcMaximumMsat`.  `capacityOfEdgeMsat` converts the existing `capacitySat`
field (1 sat = 1000 msat); callers that already have a BOLT 7
`ChannelUpdate.htlcMinimumMsat`/`htlcMaximumMsat` can supply them directly.

`edgeUsableFor` is the per-edge amount test: lower bound, upper HTLC bound, and
channel-capacity bound.  `routeCapacityValid` lifts it to a route by zipping
the route's hops with one capacity edge and one *per-hop carried amount* each.
The explicit amount list matters: BOLT 4 carries a different (larger) amount
on each upstream hop because each hop adds its fee, so a single route-level
amount is not enough for an end-to-end capacity claim.

**Boundaries.**  This layer checks advertised ranges only.  It does not model
in-flight HTLC value, channel reserve, commitment fees, dust exposure, path
scoring, route hints, MPP splitting, or the backwards fee/amount propagation
of `find_route`; it is not a liquidity oracle and does not claim that an
accepted route will succeed.  It also does not re-derive the BOLT 7
`channel_update` signatures; the min/max values are caller-supplied
advertisements.
-/

namespace LnLean.Proofs.Wave14.RouteFeeCapacity

set_option autoImplicit false

open LnLean
open LnLean.Routing

/-! ## Truncating (floor) fee -/

namespace Hop

/-- The BOLT 7 forward fee with the proportional term **truncated**:
`fee_base_msat + amount_msat * fee_proportional_millionths / 1000000`.

This is the additive counterpart of `Hop.ofEdge` (which rounds the
proportional term up).  It does not replace `ofEdge`: the ceiling form has
existing consumers and Theorems, and `ofEdge_rounding_counterexample` records
why an exact inverse identity cannot be claimed for it. -/
def ofEdgeFloor (e : ChannelEdge) (amountMsat : Msat) : Hop :=
  { node := e.node2
    shortChannelId := e.shortChannelId
    feeMsat :=
      ⟨e.feeBaseMsat.val +
        amountMsat.val * e.feeProportionalMillionths / 1000000⟩
    cltvDelta := e.cltvDelta }

@[simp] theorem ofEdgeFloor_node (e : ChannelEdge) (a : Msat) :
    (ofEdgeFloor e a).node = e.node2 := rfl

@[simp] theorem ofEdgeFloor_scid (e : ChannelEdge) (a : Msat) :
    (ofEdgeFloor e a).shortChannelId = e.shortChannelId := rfl

@[simp] theorem ofEdgeFloor_cltvDelta (e : ChannelEdge) (a : Msat) :
    (ofEdgeFloor e a).cltvDelta = e.cltvDelta := rfl

/-- The truncating fee is never larger than `ofEdge`'s ceiling fee.  The
difference is at most the one-msat rounding step; the separation theorem below
exhibits a case where it is exactly one. -/
theorem ofEdgeFloor_fee_le_ofEdge_fee (e : ChannelEdge) (a : Msat) :
    (ofEdgeFloor e a).feeMsat.val ≤ (Hop.ofEdge e a).feeMsat.val := by
  simp only [ofEdgeFloor, Hop.ofEdge]
  exact Nat.add_le_add_left
    (Nat.div_le_div_right (Nat.le_add_right _ 999999)) _

/-- The truncating fee is the base fee plus the truncated proportional term. -/
theorem ofEdgeFloor_fee_eq (e : ChannelEdge) (a : Msat) :
    (ofEdgeFloor e a).feeMsat.val =
      e.feeBaseMsat.val +
        a.val * e.feeProportionalMillionths / 1000000 := rfl

end Hop

/-! ## Concrete fee-rounding separation -/

/-- An edge with no base fee and a 1000 ppm proportional rate, used to show
the floor/ceiling gap without base-fee noise. -/
def feeWitnessEdge : ChannelEdge :=
  { shortChannelId := ⟨1, 2, 3⟩
    node1 := ⟨0⟩
    node2 := ⟨1⟩
    capacitySat := 100
    feeBaseMsat := ⟨0⟩
    feeProportionalMillionths := 1000
    cltvDelta := 40
    enabled := true }

/-- **Floor vs ceiling separation, concrete.**  For `amount_msat = 1500` and
the 1000 ppm edge, the truncated proportional fee is `1` while `Hop.ofEdge`
returns `2`.  `ofEdge` rounds up; the floor result is strictly smaller.  This
does **not** alter `ofEdge` or its counterexample module. -/
theorem floor_vs_ceiling_separates :
    (Hop.ofEdge feeWitnessEdge ⟨1500⟩).feeMsat.val = 2 ∧
      (Hop.ofEdgeFloor feeWitnessEdge ⟨1500⟩).feeMsat.val = 1 ∧
      (Hop.ofEdgeFloor feeWitnessEdge ⟨1500⟩).feeMsat.val <
        (Hop.ofEdge feeWitnessEdge ⟨1500⟩).feeMsat.val := by
  decide

/-- The separation theorem in difference form: the ceiling is exactly one
msat above the floor for the witness amount. -/
theorem floor_ceiling_gap_eq_one :
    (Hop.ofEdge feeWitnessEdge ⟨1500⟩).feeMsat.val =
      (Hop.ofEdgeFloor feeWitnessEdge ⟨1500⟩).feeMsat.val + 1 := by
  decide

/-! ## Additive capacity carrier -/

/-- An **additive** per-edge capacity carrier.  It wraps one directed
`ChannelEdge` (which already has `capacitySat` but no HTLC min/max fields) and
adds the BOLT 7 `capacity_msat`, `htlc_minimum_msat`, and
`htlc_maximum_msat` used by route admission.

This is not a replacement for `ChannelEdge`: `Graph`, `findEdge`,
`routeValid`, and `constructRoute` continue to use `ChannelEdge` unchanged. -/
structure EdgeCapacity where
  /-- The directed edge this advertisement applies to. -/
  edge : ChannelEdge
  /-- BOLT 7 channel capacity in millisatoshis. -/
  capacityMsat : Msat
  /-- BOLT 7 `htlc_minimum_msat` for this direction. -/
  htlcMinimumMsat : Msat
  /-- BOLT 7 `htlc_maximum_msat` for this direction. -/
  htlcMaximumMsat : Msat
deriving Repr, DecidableEq, BEq

/-- The existing `ChannelEdge.capacitySat` converted to millisatoshis.  This
is the only capacity figure already present on `ChannelEdge`; the min/max
fields remain caller-supplied advertisements in `EdgeCapacity`. -/
def capacityOfEdgeMsat (e : ChannelEdge) : Msat :=
  ⟨e.capacitySat * Msat.MSAT_PER_SAT⟩

@[simp] theorem capacityOfEdgeMsat_val (e : ChannelEdge) :
    (capacityOfEdgeMsat e).val = e.capacitySat * Msat.MSAT_PER_SAT := rfl

/-- **Per-edge amount usability.**  An amount is usable over `c` exactly when
it is at least `htlc_minimum_msat`, at most `htlc_maximum_msat`, and at most
the channel capacity.  All three bounds are on the same (msat) scale.

This is a necessary advertised-range test only.  It says nothing about
in-flight value, reserve, fees, dust, or whether the peer will actually
forward. -/
def edgeUsableFor (c : EdgeCapacity) (amount : Msat) : Prop :=
  c.htlcMinimumMsat.val ≤ amount.val ∧
    amount.val ≤ c.htlcMaximumMsat.val ∧
    amount.val ≤ c.capacityMsat.val

theorem edgeUsableFor_min {c : EdgeCapacity} {a : Msat}
    (h : edgeUsableFor c a) : c.htlcMinimumMsat.val ≤ a.val := h.1

theorem edgeUsableFor_max {c : EdgeCapacity} {a : Msat}
    (h : edgeUsableFor c a) : a.val ≤ c.htlcMaximumMsat.val := h.2.1

theorem edgeUsableFor_capacity {c : EdgeCapacity} {a : Msat}
    (h : edgeUsableFor c a) : a.val ≤ c.capacityMsat.val := h.2.2

/-- **Above `htlc_maximum_msat` is rejected.**  Any amount strictly above the
advertised maximum fails `edgeUsableFor`, independently of the other bounds. -/
theorem amount_above_htlcMaximum_rejected (c : EdgeCapacity) (a : Msat)
    (h : c.htlcMaximumMsat.val < a.val) : ¬ edgeUsableFor c a := by
  intro hu
  exact Nat.not_le_of_lt h (edgeUsableFor_max hu)

/-- **Above channel capacity is rejected.**  Any amount strictly above the
advertised capacity fails `edgeUsableFor`, independently of `htlc_max`. -/
theorem amount_above_capacity_rejected (c : EdgeCapacity) (a : Msat)
    (h : c.capacityMsat.val < a.val) : ¬ edgeUsableFor c a := by
  intro hu
  exact Nat.not_le_of_lt h (edgeUsableFor_capacity hu)

/-- **Below `htlc_minimum_msat` is rejected.**  Any amount strictly below the
advertised minimum fails `edgeUsableFor`. -/
theorem amount_below_htlcMinimum_rejected (c : EdgeCapacity) (a : Msat)
    (h : a.val < c.htlcMinimumMsat.val) : ¬ edgeUsableFor c a := by
  intro hu
  exact Nat.not_le_of_lt h (edgeUsableFor_min hu)

/-- The three-bounds test is exactly the conjunction, so a caller can build
usability from the individual comparisons. -/
theorem edgeUsableFor_iff (c : EdgeCapacity) (a : Msat) :
    edgeUsableFor c a ↔
      c.htlcMinimumMsat.val ≤ a.val ∧
        a.val ≤ c.htlcMaximumMsat.val ∧
        a.val ≤ c.capacityMsat.val := Iff.rfl

/-- Decidability of the advertised-range test, so concrete witnesses can be
closed by computation. -/
instance edgeUsableForDecidable (c : EdgeCapacity) (a : Msat) :
    Decidable (edgeUsableFor c a) := by
  unfold edgeUsableFor
  infer_instance

/-! ## Concrete capacity witnesses -/

/-- A capacity advertisement whose maximum is below capacity, so the
`htlc_maximum_msat` rejection can be tested without the capacity bound also
firing. -/
def narrowCapacityEdge : EdgeCapacity :=
  { edge := feeWitnessEdge
    capacityMsat := ⟨100000⟩
    htlcMinimumMsat := ⟨1000⟩
    htlcMaximumMsat := ⟨80000⟩ }

/-- A capacity advertisement whose maximum is above capacity, so the capacity
rejection can be tested without the `htlc_maximum_msat` bound also firing. -/
def wideCapacityEdge : EdgeCapacity :=
  { edge := feeWitnessEdge
    capacityMsat := ⟨100000⟩
    htlcMinimumMsat := ⟨1000⟩
    htlcMaximumMsat := ⟨200000⟩ }

/-- **In-range amount accepted.**  `50_000 msat` lies between the advertised
minimum `1_000` and both upper bounds (`80_000` max, `100_000` capacity), and
`edgeUsableFor` accepts it.  The inequality witnesses are included so the
acceptance is not vacuous. -/
theorem in_range_amount_accepted :
    edgeUsableFor narrowCapacityEdge ⟨50000⟩ ∧
      0 < (50000 : Nat) ∧
      narrowCapacityEdge.htlcMinimumMsat.val < 50000 ∧
      50000 < narrowCapacityEdge.htlcMaximumMsat.val ∧
      50000 < narrowCapacityEdge.capacityMsat.val := by
  decide

/-- **Above `htlc_maximum_msat` rejected.**  `90_000 msat` is still below
capacity (`100_000`) but exceeds the advertised maximum (`80_000`), so it is
rejected for the HTLC maximum and not for capacity. -/
theorem above_htlcMaximum_rejected_concrete :
    ¬ edgeUsableFor narrowCapacityEdge ⟨90000⟩ ∧
      (90000 : Nat) ≤ narrowCapacityEdge.capacityMsat.val ∧
      narrowCapacityEdge.htlcMaximumMsat.val < 90000 := by
  decide

/-- **Above channel capacity rejected.**  `150_000 msat` is within the
advertised HTLC range (`≤ 200_000`) but above capacity (`100_000`), so it is
rejected for capacity and not for the HTLC maximum. -/
theorem above_capacity_rejected_concrete :
    ¬ edgeUsableFor wideCapacityEdge ⟨150000⟩ ∧
      (150000 : Nat) ≤ wideCapacityEdge.htlcMaximumMsat.val ∧
      wideCapacityEdge.capacityMsat.val < 150000 := by
  decide

/-- **Below `htlc_minimum_msat` rejected.**  `500 msat` is positive and below
capacity but below the advertised minimum (`1_000`), so it is rejected. -/
theorem below_htlcMinimum_rejected_concrete :
    ¬ edgeUsableFor narrowCapacityEdge ⟨500⟩ ∧
      0 < (500 : Nat) ∧
      (500 : Nat) < narrowCapacityEdge.htlcMinimumMsat.val := by
  decide

/-! ## Route-level capacity usability -/

/-- **Route capacity validity.**  The route is paired with one capacity edge
and one carried amount per hop.  The two length equalities ensure every hop is
covered, and the zipped test requires each hop's carried amount to satisfy the
corresponding edge's advertised minimum, maximum, and capacity, with the
hop's `short_channel_id` matching the edge.

The per-hop amount list is explicit because BOLT 4 carries a different
(upstream-larger) amount on each hop; checking only `r.amountMsat` would not
be an end-to-end capacity claim.  This predicate is still advertised-range
only: no in-flight, reserve, fee, dust, or scoring model. -/
def routeCapacityValid (r : Route) (ces : List EdgeCapacity)
    (amounts : List Msat) : Prop :=
  ces.length = r.hops.length ∧
    amounts.length = r.hops.length ∧
      ∀ p ∈ ces.zip (r.hops.zip amounts),
        edgeUsableFor p.1 p.2.2 ∧
          p.1.edge.shortChannelId = p.2.1.shortChannelId

/-- Decidability of route capacity validity (finite zipped list). -/
instance routeCapacityValidDecidable (r : Route) (ces : List EdgeCapacity)
    (amounts : List Msat) : Decidable (routeCapacityValid r ces amounts) := by
  unfold routeCapacityValid
  infer_instance

/-- A valid route-capacity assignment imparts per-hop usability. -/
theorem routeCapacityValid_usable {r : Route} {ces : List EdgeCapacity}
    {amounts : List Msat} (h : routeCapacityValid r ces amounts) :
    ∀ p ∈ ces.zip (r.hops.zip amounts), edgeUsableFor p.1 p.2.2 :=
  fun p hp => (h.2.2 p hp).1

/-- A valid route-capacity assignment matches each capacity edge's
`short_channel_id` to its hop. -/
theorem routeCapacityValid_scid {r : Route} {ces : List EdgeCapacity}
    {amounts : List Msat} (h : routeCapacityValid r ces amounts) :
    ∀ p ∈ ces.zip (r.hops.zip amounts),
      p.1.edge.shortChannelId = p.2.1.shortChannelId :=
  fun p hp => (h.2.2 p hp).2

/-- A single-hop route with an in-range amount is capacity-valid. -/
theorem routeCapacityValid_single_hop_accepts :
    routeCapacityValid
      (constructRoute [(feeWitnessEdge, ⟨50000⟩)] ⟨50000⟩)
      [narrowCapacityEdge] [⟨50000⟩] := by
  decide

/-- The same single-hop route with `90_000 msat` is rejected: the amount
exceeds the edge's `htlc_maximum_msat` (`80_000`). -/
theorem routeCapacityValid_single_hop_rejects_above_max :
    ¬ routeCapacityValid
      (constructRoute [(feeWitnessEdge, ⟨90000⟩)] ⟨90000⟩)
      [narrowCapacityEdge] [⟨90000⟩] := by
  decide

/-- The same single-hop route with `150_000 msat` is rejected when the edge
advertises capacity `100_000`, even though its `htlc_maximum_msat` is
`200_000`.  This isolates capacity rejection at the route level. -/
theorem routeCapacityValid_single_hop_rejects_above_capacity :
    ¬ routeCapacityValid
      (constructRoute [(feeWitnessEdge, ⟨150000⟩)] ⟨150000⟩)
      [wideCapacityEdge] [⟨150000⟩] := by
  decide

/-- An amount below `htlc_minimum_msat` also makes the single-hop route
capacity-invalid. -/
theorem routeCapacityValid_single_hop_rejects_below_min :
    ¬ routeCapacityValid
      (constructRoute [(feeWitnessEdge, ⟨500⟩)] ⟨500⟩)
      [narrowCapacityEdge] [⟨500⟩] := by
  decide

/-! ## Axiom audit -/

#print axioms floor_vs_ceiling_separates
#print axioms Hop.ofEdgeFloor_fee_le_ofEdge_fee
#print axioms amount_above_htlcMaximum_rejected
#print axioms amount_above_capacity_rejected
#print axioms amount_below_htlcMinimum_rejected
#print axioms in_range_amount_accepted
#print axioms routeCapacityValid_single_hop_accepts
#print axioms routeCapacityValid_single_hop_rejects_above_max

end LnLean.Proofs.Wave14.RouteFeeCapacity
