import LnLean

/-!
# LnLean.Proofs.PhaseC3.CrossChannelRouting

English claim of this module.  A *valid multi-hop payment plan* is a
non-empty candidate path of directed channel edges, one amount per edge, and
explicit graph, capacity, liquidity, connectivity, and CLTV preconditions.
For such a plan:

* at every forwarding hop the amount carried over the hop plus that hop's
  advertised fee equals the amount arriving over the previous hop
  (`BackwardConserves`, `FeasiblePath.conservation_at`);
* the total fee of the route built by `constructRoute` is the sum of the
  per-hop fees (`FeasiblePath.total_fee_eq_sum`);
* the sender's outgoing amount equals the final amount plus the fees of all
  forwarding hops, and is consequently bounded by the final amount plus the
  route's total fee (`FeasiblePath.sender_eq_last_add_forwardFees`,
  `backwardConserves_sender_add_origin_eq_last_add_totalFee`);
* the sender's amount is at most the sum of the amounts carried by the hops
  (`FeasiblePath.sender_le_sum_forward`), and no hop carries more than the
  sender sent (`FeasiblePath.amount_le_sender`);
* a positive `cltv_expiry_delta` at each hop makes the accumulated CLTV
  expiry strictly increase at every hop and over the whole route
  (`FeasiblePath.cltv_strict_at_each_hop`, `FeasiblePath.endExpiry_gt`);
* the route built from a feasible plan is `routeValid` in the graph and is
  non-empty (`FeasiblePath.route_valid`, `FeasiblePath.route_nonempty`).

The fee and amount data are composed with the existing route model in
`LnLean.Routing.Route`: `constructRoute` supplies the hops, `Hop.ofEdge`
supplies each advertised fee, `Route.totalFee` is defined as the sum of hop
fees, and `Route.endExpiry_gt'` supplies the strict CLTV increase.  The new
content of this module is the per-hop amount schedule (the backwards fee
computation that `LnLean.Routing.Route` deliberately leaves as an
obligation, `LN-ROUTE-FEE`) and the cross-channel graph/liquidity bridges.

BOLT sections:

* BOLT 4 §Payloads: for a non-final node `amt_to_forward` includes the
  origin's computed fee for the receiving peer, and the forwarding check is
  `incoming amount_msat - fee >= amt_to_forward`
  (`refs/bolts/04-onion-routing.md:228-230`, `:337`).
* BOLT 4 §Payloads: `outgoing_cltv_value = cltv_expiry -
  cltv_expiry_delta`; positive deltas accumulate along the route
  (`refs/bolts/04-onion-routing.md:338`,
  `refs/bolts/07-routing-gossip.md:1031-1047`).
* BOLT 7 §The `channel_update` Message: per-direction `fee_base_msat`,
  `fee_proportional_millionths`, `cltv_expiry_delta`, and `disable`
  (`refs/bolts/07-routing-gossip.md:454-457`, `:520-527`).
* BOLT 7 §HTLC Fees: `fee_base_msat + (amount_to_forward *
  fee_proportional_millionths / 1000000)`
  (`refs/bolts/07-routing-gossip.md:975-981`).
* BOLT 7 §Graph: a public channel has a `capacity` in satoshis and two
  directions, each with its own update.

`rust-lightning` anchors at pinned commit
`fe4900930c6bd5786ec4203274d7cf312776a5a6`:

* `lightning/src/routing/router.rs:657` — `pub struct RouteHop`
  (`fee_msat`, `cltv_expiry_delta`); its `fee_msat` is documented as the fee
  for use of the next channel, which is why the first hop's own advertised
  fee is treated separately here.
* `lightning/src/routing/router.rs:776-783` — `Path::fee_msat`, which
  excludes the last hop's full payment value from the fee sum.
* `lightning/src/routing/router.rs:845-849` — `Route::get_total_fees`.
* `lightning/src/routing/router.rs:3110` — `Router::find_route`, the
  backwards fee and CLTV accumulation this module models abstractly.
* `lightning/src/ln/onion_utils.rs:1050` — `build_onion_payloads`, which
  copies each hop's fee and CLTV delta into the onion payload.
* `lightning/src/ln/channel.rs:2697-2703` and
  `lightning/src/ln/channel.rs:6552-6605` — the outbound-capacity/liquidity
  inputs used by the explicit liquidity precondition
  (`availableOutbound` in `LnLean.Proofs.Payment.LiquidityProps`).

What is explicitly **not** modelled:

* The exact `rust-lightning` attribution convention for `RouteHop.fee_msat`.
  `LnLean.Routing.Route.Hop` stores the fee advertised by the edge used to
  reach the hop, so the first hop's fee is the sender's own channel policy
  and is not paid by the sender.  The module proves both the route-level
  total-fee identity and the sender/forwarding-fee identity separately.
* Onion construction, HMACs, ephemeral keys, and payload encryption.
* Route search/optimality, MPP splitting, route hints, route blinding,
  `min_final_cltv_expiry_delta`, and fee rounding against LDK.
* Deriving liquidity from `LnLean.Channel.State`.  `LiquidityModel` is an
  explicit parameter; it is a bridge record, never an axiom.
* HTLC minimum/maximum, `max_accepted_htlcs`, dust, and commitment fees.
-/

namespace LnLean.Proofs.PhaseC3

open LnLean
open LnLean.Routing

set_option autoImplicit false

/-! ## The fee/amount model for a candidate path -/

/-- The advertised fee of one candidate-path element, computed by
`Hop.ofEdge` from the amount supplied for that edge.  This is the same fee
that appears in the hop of `constructRoute` at the same position. -/
def hopFee (p : ChannelEdge × Msat) : Nat :=
  (Hop.ofEdge p.1 p.2).feeMsat.val

@[simp] theorem hopFee_mk (e : ChannelEdge) (a : Msat) :
    hopFee (e, a) = (Hop.ofEdge e a).feeMsat.val := rfl

/-- The computed fee is at least the advertised base fee. -/
theorem hopFee_ge_base (p : ChannelEdge × Msat) :
    p.1.feeBaseMsat.val ≤ hopFee p :=
  Hop.ofEdge_fee_ge_base p.1 p.2

/-- **Backwards amount conservation.**  The list is the candidate path, with
the amount carried over each edge.  For consecutive edges `p` then `q`, the
amount on `p` is the amount on `q` plus the fee advertised for `q`; this is
BOLT 4's `incoming amount_msat - fee >= amt_to_forward` with the computed
route using equality.  A one-hop path has no forwarding node and therefore
no conservation constraint. -/
def BackwardConserves : List (ChannelEdge × Msat) → Prop
  | [] => True
  | [_] => True
  | p :: q :: rest => p.2.val = q.2.val + hopFee q ∧
      BackwardConserves (q :: rest)

/-- Consecutive candidate edges meet at a node: the destination of one edge
is the source of the next.  `routeValid` checks each hop against the graph
but not this cross-channel link, so it is an explicit precondition here. -/
def Connected : List (ChannelEdge × Msat) → Prop
  | [] => True
  | [_] => True
  | p :: q :: rest => p.1.node2 = q.1.node1 ∧ Connected (q :: rest)

/-- The amounts carried by the hops, in order.  This is the "forward
amount" list: the first entry is the sender's outgoing amount. -/
def forwardAmounts (path : List (ChannelEdge × Msat)) : List Nat :=
  path.map fun p => p.2.val

/-- Sum of the amounts carried by the hops. -/
def sumForward (path : List (ChannelEdge × Msat)) : Nat :=
  (forwardAmounts path).sum

/-- The sender's outgoing amount: the amount supplied for the first edge. -/
def senderAmount : List (ChannelEdge × Msat) → Msat
  | [] => Msat.zero
  | p :: _ => p.2

/-- The amount received at the end of the path. -/
def lastAmount : List (ChannelEdge × Msat) → Nat
  | [] => 0
  | [p] => p.2.val
  | _ :: q :: rest => lastAmount (q :: rest)

/-- The fees actually paid by the sender: every hop fee except the origin
hop's own advertised policy (the sender does not charge itself). -/
def forwardFeeTotal (path : List (ChannelEdge × Msat)) : Nat :=
  ((path.drop 1).map hopFee).sum

@[simp] theorem forwardAmounts_nil : forwardAmounts [] = [] := rfl

@[simp] theorem forwardAmounts_cons (p : ChannelEdge × Msat)
    (ps : List (ChannelEdge × Msat)) :
    forwardAmounts (p :: ps) = p.2.val :: forwardAmounts ps := rfl

@[simp] theorem sumForward_nil : sumForward [] = 0 := rfl

@[simp] theorem sumForward_cons (p : ChannelEdge × Msat)
    (ps : List (ChannelEdge × Msat)) :
    sumForward (p :: ps) = p.2.val + sumForward ps := by
  simp [sumForward, forwardAmounts]

@[simp] theorem senderAmount_nil : senderAmount [] = Msat.zero := rfl

@[simp] theorem senderAmount_cons (p : ChannelEdge × Msat)
    (ps : List (ChannelEdge × Msat)) : senderAmount (p :: ps) = p.2 := rfl

@[simp] theorem lastAmount_nil : lastAmount [] = 0 := rfl

@[simp] theorem lastAmount_singleton (p : ChannelEdge × Msat) :
    lastAmount [p] = p.2.val := rfl

@[simp] theorem lastAmount_cons_cons (p q : ChannelEdge × Msat)
    (rest : List (ChannelEdge × Msat)) :
    lastAmount (p :: q :: rest) = lastAmount (q :: rest) := rfl

@[simp] theorem backwardConserves_nil : BackwardConserves [] := trivial

@[simp] theorem backwardConserves_singleton (p : ChannelEdge × Msat) :
    BackwardConserves [p] := trivial

theorem backwardConserves_cons_cons (p q : ChannelEdge × Msat)
    (rest : List (ChannelEdge × Msat)) :
    BackwardConserves (p :: q :: rest) ↔
      (p.2.val = q.2.val + hopFee q ∧ BackwardConserves (q :: rest)) :=
  Iff.rfl

@[simp] theorem connected_nil : Connected [] := trivial

@[simp] theorem connected_singleton (p : ChannelEdge × Msat) : Connected [p] := trivial

theorem connected_cons_cons (p q : ChannelEdge × Msat)
    (rest : List (ChannelEdge × Msat)) :
    Connected (p :: q :: rest) ↔
      (p.1.node2 = q.1.node1 ∧ Connected (q :: rest)) :=
  Iff.rfl

/-! ## Conservation at every hop -/

/-- Every adjacent pair in a conserving path satisfies the hop equation.
This is the indexed form of `BackwardConserves`. -/
theorem backwardConserves_get : ∀ (path : List (ChannelEdge × Msat)),
    BackwardConserves path →
    ∀ (i : Nat) (hi : i + 1 < path.length),
      (path.get ⟨i, Nat.lt_of_succ_lt hi⟩).2.val =
        (path.get ⟨i + 1, hi⟩).2.val +
          hopFee (path.get ⟨i + 1, hi⟩)
  | [], _ => by
      intro i hi
      simp at hi
  | [p], _ => by
      intro i hi
      simp at hi
  | p :: q :: rest, h => by
      intro i hi
      cases i with
      | zero =>
          simpa using h.1
      | succ i =>
          have hi' : i + 1 < (q :: rest).length := by simpa using hi
          have htail := backwardConserves_get (q :: rest) h.2 i hi'
          simpa using htail

/-- Pointwise form for a path of at least two edges. -/
theorem backwardConserves_pair {p q : ChannelEdge × Msat}
    {rest : List (ChannelEdge × Msat)}
    (h : BackwardConserves (p :: q :: rest)) :
    p.2.val = q.2.val + hopFee q := h.1

/-- Every hop after the first carries at most the amount the sender sent. -/
theorem backwardConserves_forall_le_head :
    ∀ (p : ChannelEdge × Msat) (rest : List (ChannelEdge × Msat)),
      BackwardConserves (p :: rest) →
      ∀ q ∈ rest, q.2.val ≤ p.2.val
  | p, [], h, q, hq => by simp at hq
  | p, [q], h, x, hx => by
      have hpq : q.2.val ≤ p.2.val := by
        have := h.1
        omega
      simp only [List.mem_singleton] at hx
      subst hx
      exact hpq
  | p, q :: r :: rest, h, x, hx => by
      have hpq : q.2.val ≤ p.2.val := by
        have := h.1
        omega
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact hpq
      · have htail := backwardConserves_forall_le_head q (r :: rest) h.2 x hx'
        omega

/-! ## Telescoping the fees -/

/-- The amount supplied for the first edge equals the final amount plus the
sum of all *forwarding* fees.  The first hop's own advertised fee is not
paid by the sender and is deliberately excluded. -/
theorem backwardConserves_sender_eq_last_add_feeSum (p : ChannelEdge × Msat) :
    ∀ (rest : List (ChannelEdge × Msat)),
      BackwardConserves (p :: rest) →
      p.2.val = lastAmount (p :: rest) + (rest.map hopFee).sum
  | [], _ => by simp
  | [q], h => by
      have h1 : p.2.val = q.2.val + hopFee q := h.1
      simpa using h1
  | q :: r :: rest, h => by
      have h1 : p.2.val = q.2.val + hopFee q := h.1
      have h2 := backwardConserves_sender_eq_last_add_feeSum q (r :: rest) h.2
      have hmap : ((q :: r :: rest).map hopFee).sum =
          hopFee q + ((r :: rest).map hopFee).sum := by simp
      have hlast : lastAmount (p :: q :: r :: rest) = lastAmount (q :: r :: rest) := rfl
      rw [hlast, hmap]
      omega

/-- Plan-level form of the telescoping identity, using the explicit
forwarding-fee total. -/
theorem backwardConserves_sender_eq_last_add_fees (p : ChannelEdge × Msat)
    (rest : List (ChannelEdge × Msat))
    (h : BackwardConserves (p :: rest)) :
    p.2.val = lastAmount (p :: rest) + forwardFeeTotal (p :: rest) := by
  have htel := backwardConserves_sender_eq_last_add_feeSum p rest h
  have hft : forwardFeeTotal (p :: rest) = (rest.map hopFee).sum := by
    simp [forwardFeeTotal]
  rw [hft]
  exact htel

/-- The route-level `totalFee` is exactly the sum of the per-hop fees of the
candidate path. -/
theorem constructRoute_totalFee_eq_sum_hopFee
    (path : List (ChannelEdge × Msat)) (amount : Msat) :
    (constructRoute path amount).totalFee.val = (path.map hopFee).sum := by
  rw [constructRoute_totalFee]
  simp only [List.map_map]
  rfl

/-- **Fee decomposition.**  The sender's outgoing amount plus the origin
hop's advertised fee equals the final amount plus `Route.totalFee`.  This
is the exact form in which the route's sum-of-hop-fees total relates to the
sender's outlay: `totalFee` includes the origin hop's own policy, which the
sender does not pay. -/
theorem backwardConserves_sender_add_origin_eq_last_add_totalFee
    (p : ChannelEdge × Msat) (rest : List (ChannelEdge × Msat))
    (amount : Msat) (h : BackwardConserves (p :: rest)) :
    p.2.val + hopFee p =
      lastAmount (p :: rest) +
        (constructRoute (p :: rest) amount).totalFee.val := by
  have hsend := backwardConserves_sender_eq_last_add_fees p rest h
  have hfee := constructRoute_totalFee_eq_sum_hopFee (p :: rest) amount
  have hft : forwardFeeTotal (p :: rest) = (rest.map hopFee).sum := by
    simp [forwardFeeTotal]
  have hmap : (List.map hopFee (p :: rest)).sum =
      hopFee p + (rest.map hopFee).sum := by simp
  rw [hfee, hmap]
  omega

/-- List-level form of `sender_eq_last_add_forwardFees`. -/
theorem senderAmount_eq_last_add_fees_of_conserves
    (path : List (ChannelEdge × Msat)) (hne : path ≠ [])
    (h : BackwardConserves path) :
    (senderAmount path).val = lastAmount path + forwardFeeTotal path := by
  cases path with
  | nil => exact absurd rfl hne
  | cons p rest => exact backwardConserves_sender_eq_last_add_fees p rest h

/-- List-level form of the sender/total-fee bound. -/
theorem senderAmount_le_last_add_totalFee_of_conserves
    (path : List (ChannelEdge × Msat)) (amount : Msat)
    (hne : path ≠ []) (h : BackwardConserves path) :
    (senderAmount path).val ≤
      lastAmount path + (constructRoute path amount).totalFee.val := by
  cases path with
  | nil => exact absurd rfl hne
  | cons p rest =>
      have hd := backwardConserves_sender_add_origin_eq_last_add_totalFee
        p rest amount h
      change p.2.val ≤ lastAmount (p :: rest) +
        (constructRoute (p :: rest) amount).totalFee.val
      omega

/-- List-level form of `sender_le_sum_forward`. -/
theorem senderAmount_le_sumForward_of_nonempty
    (path : List (ChannelEdge × Msat)) (hne : path ≠ []) :
    (senderAmount path).val ≤ sumForward path := by
  cases path with
  | nil => exact absurd rfl hne
  | cons p rest =>
      show p.2.val ≤ (p.2.val :: (rest.map fun x => x.2.val)).sum
      rw [List.sum_cons]
      omega

/-- List-level form of `amount_le_sender`. -/
theorem amount_le_sender_of_conserves
    (path : List (ChannelEdge × Msat)) (h : BackwardConserves path)
    (hne : path ≠ []) {q : ChannelEdge × Msat} (hq : q ∈ path) :
    q.2.val ≤ (senderAmount path).val := by
  cases path with
  | nil => exact absurd rfl hne
  | cons p rest =>
      rcases List.mem_cons.mp hq with rfl | hq'
      · simp
      · exact backwardConserves_forall_le_head p rest h q hq'

/-! ## The liquidity/capacity model -/

/-- An explicit liquidity model for a routing graph.  `availableMsat e` is
the amount the source of directed edge `e` can forward over it, i.e. the
route-relevant `outbound_capacity_msat` of the corresponding channel
(`LnLean.Proofs.Payment.LiquidityProps.availableOutbound`).  The field
`withinCapacity` is the BOLT 7 capacity bridge: advertised liquidity can
never exceed the channel's announced capacity.  It is a structure field, not
an axiom. -/
structure LiquidityModel where
  availableMsat : ChannelEdge → Nat
  withinCapacity : ∀ e : ChannelEdge,
    availableMsat e ≤ e.capacitySat * Msat.MSAT_PER_SAT

/-- A feasible multi-hop payment plan.  Every precondition is explicit:
graph membership, enabled directions, cross-channel connectivity, positive
CLTV deltas, BOLT 7 capacity, and source-node liquidity. -/
structure FeasiblePath (g : Graph) (L : LiquidityModel) where
  /-- The candidate path: one directed edge plus the amount carried over it
  per hop. -/
  path : List (ChannelEdge × Msat)
  /-- BOLT 4 routes are non-empty. -/
  nonempty : path ≠ []
  /-- The backwards fee/amount conservation law. -/
  conserved : BackwardConserves path
  /-- Consecutive edges share an endpoint. -/
  connected : Connected path
  /-- Every edge is an announced edge of the graph. -/
  mem_edges : ∀ p ∈ path, p.1 ∈ g.edges
  /-- Every direction used by the route is enabled. -/
  enabled : ∀ p ∈ path, p.1.enabled = true
  /-- Every hop has a positive `cltv_expiry_delta`. -/
  cltvPositive : ∀ p ∈ path, 0 < p.1.cltvDelta
  /-- BOLT 7 capacity: the forwarded amount fits the announced channel
  capacity, in millisatoshis. -/
  capacity : ∀ p ∈ path, p.2.val ≤ p.1.capacitySat * Msat.MSAT_PER_SAT
  /-- Liquidity: the forwarding source can fund the amount it forwards. -/
  liquidity : ∀ p ∈ path, p.2.val ≤ L.availableMsat p.1

namespace FeasiblePath

variable {g : Graph} {L : LiquidityModel}

/-- The BOLT 4 route built from the plan's candidate path.  Its amount is
the sender's outgoing amount. -/
def route (plan : FeasiblePath g L) : Route :=
  constructRoute plan.path (senderAmount plan.path)

@[simp] theorem route_hops (plan : FeasiblePath g L) :
    plan.route.hops = plan.path.map (fun p => Hop.ofEdge p.1 p.2) := rfl

@[simp] theorem route_amount (plan : FeasiblePath g L) :
    plan.route.amountMsat = senderAmount plan.path := rfl

/-- The constructed route is valid in the graph. -/
theorem route_valid (plan : FeasiblePath g L) : routeValid g plan.route :=
  constructRoute_valid g plan.path (senderAmount plan.path)
    plan.nonempty plan.mem_edges plan.enabled

/-- A valid plan constructs a non-empty route. -/
theorem route_nonempty (plan : FeasiblePath g L) : plan.route.NonEmpty :=
  routeValid_nonempty plan.route_valid

/-- The route's hop list is non-empty. -/
theorem route_hops_ne_nil (plan : FeasiblePath g L) : plan.route.hops ≠ [] :=
  plan.route_nonempty

/-- **Conservation at every hop.**  For each indexed hop `i+1`, the amount
on hop `i` equals the amount on hop `i+1` plus hop `i+1`'s fee. -/
theorem conservation_at (plan : FeasiblePath g L) (i : Nat)
    (hi : i + 1 < plan.path.length) :
    (plan.path.get ⟨i, Nat.lt_of_succ_lt hi⟩).2.val =
      (plan.path.get ⟨i + 1, hi⟩).2.val +
        hopFee (plan.path.get ⟨i + 1, hi⟩) :=
  backwardConserves_get plan.path plan.conserved i hi

/-- **Adjacent-hop conservation**, in pair form. -/
theorem conservation_pair (plan : FeasiblePath g L)
    {p q : ChannelEdge × Msat} {rest : List (ChannelEdge × Msat)}
    (hp : plan.path = p :: q :: rest) :
    p.2.val = q.2.val + hopFee q := by
  have h := plan.conserved
  rw [hp] at h
  exact h.1

/-- Consecutive edges meet at a node. -/
theorem connectivity_pair (plan : FeasiblePath g L)
    {p q : ChannelEdge × Msat} {rest : List (ChannelEdge × Msat)}
    (hp : plan.path = p :: q :: rest) :
    p.1.node2 = q.1.node1 := by
  have h := plan.connected
  rw [hp] at h
  exact h.1

/-- The route's total fee is the sum of the per-hop fees. -/
theorem total_fee_eq_sum (plan : FeasiblePath g L) :
    plan.route.totalFee.val = (plan.path.map hopFee).sum :=
  constructRoute_totalFee_eq_sum_hopFee plan.path (senderAmount plan.path)

/-- The sender's amount equals the final amount plus the forwarding fees. -/
theorem sender_eq_last_add_forwardFees (plan : FeasiblePath g L) :
    (senderAmount plan.path).val =
      lastAmount plan.path + forwardFeeTotal plan.path :=
  senderAmount_eq_last_add_fees_of_conserves plan.path plan.nonempty plan.conserved

/-- The sender's amount is at most the final amount plus the route's total
fee.  (`totalFee` includes the origin hop's policy; the strict identity is
`backwardConserves_sender_add_origin_eq_last_add_totalFee`.) -/
theorem sender_le_last_add_totalFee (plan : FeasiblePath g L) :
    (senderAmount plan.path).val ≤
      lastAmount plan.path + plan.route.totalFee.val :=
  senderAmount_le_last_add_totalFee_of_conserves plan.path
    (senderAmount plan.path) plan.nonempty plan.conserved

/-- The sender's amount is at most the sum of the amounts carried by the
hops (the forward amounts).  The first hop carries exactly the sender's
amount and all amounts are non-negative. -/
theorem sender_le_sum_forward (plan : FeasiblePath g L) :
    (senderAmount plan.path).val ≤ sumForward plan.path :=
  senderAmount_le_sumForward_of_nonempty plan.path plan.nonempty

/-- No hop carries more than the sender's outgoing amount. -/
theorem amount_le_sender (plan : FeasiblePath g L) {q : ChannelEdge × Msat}
    (hq : q ∈ plan.path) :
    q.2.val ≤ (senderAmount plan.path).val :=
  amount_le_sender_of_conserves plan.path plan.conserved plan.nonempty hq

/-- Liquidity precondition at a hop. -/
theorem liquidity_bound (plan : FeasiblePath g L) {p : ChannelEdge × Msat}
    (hp : p ∈ plan.path) : p.2.val ≤ L.availableMsat p.1 :=
  plan.liquidity p hp

/-- Capacity precondition at a hop, in millisatoshis. -/
theorem capacity_bound (plan : FeasiblePath g L) {p : ChannelEdge × Msat}
    (hp : p ∈ plan.path) : p.2.val ≤ p.1.capacitySat * Msat.MSAT_PER_SAT :=
  plan.capacity p hp

/-- Capacity follows from the liquidity precondition and the BOLT 7
capacity bridge carried by `LiquidityModel`.  This shows that the explicit
capacity field is compatible with the advertised liquidity bound rather
than an extra economic assumption. -/
theorem capacity_of_liquidity (plan : FeasiblePath g L) {p : ChannelEdge × Msat}
    (hp : p ∈ plan.path) : p.2.val ≤ p.1.capacitySat * Msat.MSAT_PER_SAT :=
  Nat.le_trans (plan.liquidity p hp) (L.withinCapacity p.1)

/-- Every constructed hop has a positive CLTV delta. -/
theorem hop_cltv_positive (plan : FeasiblePath g L) :
    ∀ h ∈ plan.route.hops, 0 < h.cltvDelta := by
  intro h hh
  rw [route_hops] at hh
  rcases List.mem_map.mp hh with ⟨p, hp, rfl⟩
  simpa using plan.cltvPositive p hp

/-- **CLTV increases strictly at every hop** when the hop's delta is
positive. -/
theorem cltv_strict_at_each_hop (plan : FeasiblePath g L) (start : Nat) :
    ∀ h ∈ plan.route.hops, start < h.expiryAfter start := by
  intro h hh
  exact Hop.expiryAfter_strict h start (plan.hop_cltv_positive h hh)

/-- **The accumulated expiry strictly increases over the whole route.** -/
theorem endExpiry_gt (plan : FeasiblePath g L) (start : Nat) :
    start < plan.route.endExpiry start :=
  Route.endExpiry_gt' plan.route start plan.route_nonempty plan.hop_cltv_positive

end FeasiblePath

/-- Route-level restatement: any graph-valid route is non-empty.  This is
the composition of `routeValid` with the representation invariant of
`Route`. -/
theorem valid_route_nonempty {g : Graph} {r : Route} (h : routeValid g r) :
    r.NonEmpty :=
  routeValid_nonempty h

/-! ## Strict increase of a prefix expiry

`Route.endExpiry_gt` proves the whole-route increase.  The following
stronger statement shows the accumulated expiry increases when any single
positive-delta hop is appended to any prefix, i.e. at every hop. -/

/-- Appending one positive-delta hop strictly increases the accumulated
expiry, for an arbitrary prefix. -/
theorem expiry_prefix_cons_strict (pre : List Hop) (h : Hop) (start : Nat)
    (hpos : 0 < h.cltvDelta) :
    pre.foldl (fun acc h => acc + h.cltvDelta) start <
      (pre ++ [h]).foldl (fun acc h => acc + h.cltvDelta) start := by
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  omega

/-- The same statement in the middle of a route: the expiry before a hop is
strictly below the expiry after that hop. -/
theorem expiry_at_hop_strict (pre : List Hop) (h : Hop) (suffix : List Hop)
    (start : Nat) (hpos : 0 < h.cltvDelta) :
    pre.foldl (fun acc h => acc + h.cltvDelta) start <
      (pre ++ h :: suffix).foldl (fun acc h => acc + h.cltvDelta) start := by
  rw [List.foldl_append]
  have hstep : pre.foldl (fun acc h => acc + h.cltvDelta) start <
      pre.foldl (fun acc h => acc + h.cltvDelta) start + h.cltvDelta := by
    omega
  have hsum := Route.foldl_add_eq_sum (h :: suffix)
    (pre.foldl (fun acc h => acc + h.cltvDelta) start)
  rw [hsum]
  simp only [List.map_cons, List.sum_cons]
  omega

/-! ## A concrete non-vacuous witness -/

/-- One enabled, one-satoshi-capacity demo channel with a 40-block CLTV
delta and a zero advertised fee. -/
def demoEdge : ChannelEdge where
  shortChannelId := ⟨1, 0, 0⟩
  node1 := ⟨0⟩
  node2 := ⟨1⟩
  capacitySat := 1
  feeBaseMsat := Msat.zero
  feeProportionalMillionths := 0
  cltvDelta := 40
  enabled := true

/-- The demo graph contains the single enabled direction. -/
def demoGraph : Graph := ⟨[demoEdge], []⟩

/-- Advertised liquidity equals the BOLT 7 capacity in millisatoshis. -/
def demoLiquidity : LiquidityModel where
  availableMsat := fun e => e.capacitySat * Msat.MSAT_PER_SAT
  withinCapacity := fun _ => Nat.le_refl _

/-- A one-hop plan sending 1000 msat over the demo channel. -/
def demoPlan : FeasiblePath demoGraph demoLiquidity where
  path := [(demoEdge, ⟨1000⟩)]
  nonempty := by simp
  conserved := by simp [BackwardConserves]
  connected := by simp [Connected]
  mem_edges := by simp [demoGraph]
  enabled := by simp [demoEdge]
  cltvPositive := by simp [demoEdge]
  capacity := by simp [demoEdge, Msat.MSAT_PER_SAT]
  liquidity := by simp [demoLiquidity, demoEdge, Msat.MSAT_PER_SAT]

/-- The demo plan is non-vacuously feasible and constructs a graph-valid,
non-empty route. -/
theorem demoPlan_route_valid :
    routeValid demoGraph demoPlan.route ∧ demoPlan.route.NonEmpty :=
  ⟨demoPlan.route_valid, demoPlan.route_nonempty⟩

/-- The demo route's CLTV accumulates its positive delta. -/
theorem demoPlan_cltv_increases :
    100 < demoPlan.route.endExpiry 100 :=
  demoPlan.endExpiry_gt 100

end LnLean.Proofs.PhaseC3
