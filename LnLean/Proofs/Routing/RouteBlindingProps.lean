import LnLean.Routing.Route
import LnLean.Routing.Onion

/-!
# LnLean.Proofs.Routing.RouteBlindingProps

Route-construction laws and a structural model of BOLT 4 route blinding.

## English claim

For a BOLT 4 route (`LnLean.Routing.Route`):

1. **Non-emptiness and distinct channels.**  A route is non-empty and, as a
   separate selection invariant, its hops use pairwise distinct
   `short_channel_id`s.  `constructRoute` preserves both properties of its
   candidate path.  Non-emptiness is part of `routeValid`; distinctness is
   *not*, so it is stated as the independent predicate `Route.WellFormed`.
2. **No hidden fee.**  `Route.totalFee` is definitionally the sum of the
   per-hop `feeMsat` fields, and equals the left fold that adds each hop's
   declared fee.  There is no other contribution.
3. **CLTV arithmetic.**  The total CLTV offset is the sum of the hop
   `cltvDelta`s plus the final recipient delta
   (`Route.totalCltvWithFinal`).  The sender's HTLC expiry for hop `i`,
   given the expiry `finalExpiry` at the recipient, is
   `cltvAt finalExpiry i = finalExpiry + sum of deltas from i onwards`.
   It strictly *decreases* downstream and therefore strictly *increases*
   when read from the recipient back to the sender.  This direction is
   stated explicitly; the wave-A `Route.endExpiry` adds deltas in the
   forward list order and is not used as a per-edge expiry claim here.
4. **Amount arithmetic.**  With the final amount `r.amountMsat`, the amount
   carried on hop `i` is `r.amountMsat + sum of fees from i onwards`
   (`Route.amountAt`); in particular the sender's amount is the final amount
   plus the total fee, and each hop's amount is the next hop's amount plus
   that hop's fee.
5. **Route blinding.**  A `BlindedPath` carries, on the wire, only
   `first_node_id`, `first_path_key`, and for each hop a `blinded_node_id`
   and an `encrypted_recipient_data` blob.  The real node id and the relay
   terms are creator-side data (the terms are inside
   `encrypted_recipient_data`).  The projection `BlindedHop.exposed` is
   independent of both the real node id and the plaintext terms, so the
   sender-facing view hides them.  Mapping the same terms through either
   the real or the blinded node selector yields routes with identical total
   fee, total CLTV, and per-hop amount schedule: blinding changes identities,
   not fee/CLTV arithmetic.
6. **A rounding gap.**  `Hop.ofEdge` rounds the proportional fee *up*.
   BOLT 4's sender-side inverse formula rounds down; the two do not compose
   exactly at small amounts.  A checked counterexample is recorded below
   (`ofEdge_rounding_counterexample`) instead of claiming an identity that
   is false.

## BOLT sections

* BOLT 4, "Route Blinding":
  `refs/bolts/04-onion-routing.md:442` (subtype `blinded_path`),
  `:449-457` (wire fields `first_node_id`, `first_path_key`, `num_hops`,
  `blinded_node_id`, `encrypted_recipient_data`),
  `:507-509` (blinded node id derivation),
  `:521-527` (sender prepends payloads and encrypts to blinded ids),
  `:585-598` (padding, dummy hops, recipient-specified fees/expiry and
  `payment_constraints`).
* BOLT 4, "Payloads": `refs/bolts/04-onion-routing.md:195-243`
  (`amt_to_forward`, `outgoing_cltv_value`, and their monotonicity along a
  route), and `:321-328` (the blinded `payment_relay` amount/CLTV
  calculation).
* BOLT 7, "The `channel_update` Message":
  `refs/bolts/07-routing-gossip.md:454-457` (`fee_base_msat`,
  `fee_proportional_millionths`, `cltv_expiry_delta`), `:981` (the fee
  formula), and `:1031-1047` (route CLTV is the sum of the deltas plus the
  final delta).

## `rust-lightning` anchors

Pinned commit `fe4900930c6bd5786ec4203274d7cf312776a5a6`.

* `lightning/src/routing/router.rs:657` — `RouteHop` (`pubkey`,
  `short_channel_id`, `fee_msat`, `cltv_expiry_delta`).  Note that LDK puts
  the whole final value (not a fee) in the last hop's `fee_msat`; our
  `Hop.feeMsat` is a fee on every hop, so the anchor is structural only.
* `lightning/src/routing/router.rs:825` — `Route`;
  `:845` `get_total_fees`; `:857` `get_total_amount`.
* `lightning/src/routing/router.rs:1051` — `RouteParameters`.
* `lightning/src/routing/router.rs:2782` — `find_route`.
* `lightning/src/blinded_path/mod.rs:101` — `BlindedHop`
  (`blinded_node_id`, `encrypted_payload`).
* `lightning/src/blinded_path/payment.rs:43` — `BlindedPayInfo`
  (`fee_base_msat`, `fee_proportional_millionths`, `cltv_expiry_delta`);
  `:82` `BlindedPaymentPath`.
* `lightning/src/ln/onion_utils.rs:471` — `build_onion_payloads`.

## What is explicitly *not* modelled

* ECDH (assumption C5), HKDF (C6), ChaCha20-Poly1305 (C7), and HMAC (C8).
  There is no blinding function, no `rho_i` key, and no AEAD.  `exposed`
  only proves that the *type* of the wire view omits certain fields; it does
  not prove computational unlinkability of blinded node ids.
* The TLV encoding of `encrypted_recipient_data` and the onion payload.
  `shortChannelId` and the relay terms are creator-side fields in this
  model; BOLT 4 actually carries the `short_channel_id` inside the encrypted
  data (type 6) and the relay terms in `payment_relay`.
* Route search (`find_route`), path optimality, liquidity, capacity,
  `htlc_minimum_msat`/`htlc_maximum_msat`, MPP splitting, route hints, and
  the receiver's `min_final_cltv_expiry_delta` policy.
* The consistency between `Hop.feeMsat` and the amount used in
  `Hop.ofEdge`: wave A lets the caller choose the amounts independently, so
  a route can contain fee fields not computed from the amount carried.
  `routeValid` does not check this.
* Dummy-hop padding and the `num_hops` privacy argument: the model has no
  dummy-hop flag.  A path can still be padded by appending hops, but the
  observation that padding hides the real length is not formalized.
* Node public-key identities: `NodeId` is an opaque index, `PubKey` is a
  byte array.
-/

namespace LnLean.Routing

set_option autoImplicit false

/-! ## 1. Short-channel-id distinctness -/

/-- The `short_channel_id` sequence of a hop list, in route order. -/
def scidsOf (hops : List Hop) : List ShortChannelId :=
  hops.map Hop.shortChannelId

/-- A hop list uses each `short_channel_id` at most once.  This is a
route-selection invariant, not a consequence of `routeValid`: the reverse
direction of a BOLT 7 channel has the same `short_channel_id`, so a route
may legitimately (but wastefully) traverse a channel twice. -/
def ScidsDistinct (hops : List Hop) : Prop := (scidsOf hops).Nodup

@[simp] theorem scidsOf_nil : scidsOf [] = [] := rfl

@[simp] theorem scidsOf_cons (h : Hop) (t : List Hop) :
    scidsOf (h :: t) = h.shortChannelId :: scidsOf t := rfl

/-- Unfolding distinctness at the head of a hop list. -/
theorem scidsDistinct_cons {h : Hop} {t : List Hop} :
    ScidsDistinct (h :: t) ↔
      h.shortChannelId ∉ scidsOf t ∧ ScidsDistinct t := by
  simp [ScidsDistinct]

/-- The tail of a distinct hop list is distinct. -/
theorem scidsDistinct_tail {h : Hop} {t : List Hop}
    (hd : ScidsDistinct (h :: t)) : ScidsDistinct t :=
  (scidsDistinct_cons.mp hd).2

/-- A two-hop list is distinct exactly when the two channel ids differ. -/
theorem scidsDistinct_pair {a b : Hop}
    (h : a.shortChannelId ≠ b.shortChannelId) : ScidsDistinct [a, b] := by
  simp [ScidsDistinct, h]

/-- **Pairwise form of distinctness.**  Two different positions in a
distinct route cannot carry the same `short_channel_id`.  This is the
mission's "each hop has a distinct short_channel_id", stated at the level of
indices. -/
theorem scidsDistinct_getElem_ne {hops : List Hop} (hd : ScidsDistinct hops)
    {i j : Nat} (hi : i < hops.length) (hj : j < hops.length) (hij : i ≠ j) :
    (hops[i]'hi).shortChannelId ≠ (hops[j]'hj).shortChannelId := by
  intro heq
  have hmap : (scidsOf hops)[i]'(by simpa [scidsOf] using hi) =
      (scidsOf hops)[j]'(by simpa [scidsOf] using hj) := by
    simpa [scidsOf] using heq
  exact hij (hd.getElem_inj.mp hmap)

/-- A route is *well formed* when it is non-empty and uses pairwise distinct
channels.  This packages the two route-construction requirements of the
mission. -/
def Route.WellFormed (r : Route) : Prop :=
  r.NonEmpty ∧ ScidsDistinct r.hops

theorem route_wellFormed_iff (r : Route) :
    r.WellFormed ↔ r.hops ≠ [] ∧ (scidsOf r.hops).Nodup :=
  Iff.rfl

/-- `constructRoute` preserves distinctness of the candidate path's channel
ids. -/
theorem constructRoute_scidsDistinct (path : List (ChannelEdge × Msat))
    (amountMsat : Msat)
    (h : (path.map fun ea => ea.1.shortChannelId).Nodup) :
    ScidsDistinct (constructRoute path amountMsat).hops := by
  have hmap : (constructRoute path amountMsat).hops.map Hop.shortChannelId =
      path.map (fun ea => ea.1.shortChannelId) := by
    simp [constructRoute, List.map_map, Function.comp_def]
  unfold ScidsDistinct scidsOf
  rw [hmap]
  exact h

/-- **Construction law.**  A non-empty candidate path with distinct channel
ids yields a well-formed route.  The hop count is the path length by
`Route.constructRoute_length`. -/
theorem constructRoute_wellFormed (path : List (ChannelEdge × Msat))
    (amountMsat : Msat) (hne : path ≠ [])
    (hscid : (path.map fun ea => ea.1.shortChannelId).Nodup) :
    (constructRoute path amountMsat).WellFormed := by
  constructor
  · simpa [Route.NonEmpty, constructRoute] using hne
  · exact constructRoute_scidsDistinct path amountMsat hscid

/-! ## 2. Fee arithmetic: the total is the sum of the hops' fees -/

/-- The total fee is the sum of the declared per-hop fees.  This is the
"no hidden fee" statement: there is no other additive contribution. -/
theorem Route.totalFee_eq_sum (r : Route) :
    r.totalFee.val = (r.hops.map fun h => h.feeMsat.val).sum := rfl

/-- A left fold that adds each declared fee equals the starting value plus
the sum of the fees. -/
theorem foldl_add_fees (hops : List Hop) (start : Nat) :
    hops.foldl (fun acc h => acc + h.feeMsat.val) start =
      start + (hops.map fun h => h.feeMsat.val).sum := by
  induction hops generalizing start with
  | nil => simp
  | cons h t ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih]
    omega

/-- The total fee is exactly the left fold over the hop list, so no fee can
be introduced outside the hop records. -/
theorem Route.totalFee_eq_foldl (r : Route) :
    r.totalFee.val =
      r.hops.foldl (fun acc h => acc + h.feeMsat.val) 0 := by
  show (r.hops.map fun h => h.feeMsat.val).sum =
    r.hops.foldl (fun acc h => acc + h.feeMsat.val) 0
  rw [foldl_add_fees]
  simp

/-- Prepending a hop adds exactly that hop's declared fee. -/
theorem Route.totalFee_cons_exact (h : Hop) (r : Route) :
    (r.cons h).totalFee.val = h.feeMsat.val + r.totalFee.val :=
  Route.totalFee_cons h r

/-- The BOLT 7 forward fee is monotone in the amount: a larger amount never
produces a smaller fee.  This is the arithmetic behind backwards fee
accumulation. -/
theorem ofEdge_fee_mono (e : ChannelEdge) {a b : Msat} (h : a.val ≤ b.val) :
    (Hop.ofEdge e a).feeMsat.val ≤ (Hop.ofEdge e b).feeMsat.val := by
  simp only [Hop.ofEdge]
  have hm : a.val * e.feeProportionalMillionths ≤
      b.val * e.feeProportionalMillionths := Nat.mul_le_mul_right _ h
  have hd : (a.val * e.feeProportionalMillionths + 999999) / 1000000 ≤
      (b.val * e.feeProportionalMillionths + 999999) / 1000000 :=
    Nat.div_le_div_right (c := 1000000) (Nat.add_le_add_right hm 999999)
  omega

/-- **Rounding gap, checked.**  There are base/rate/amount values for which
BOLT 4's inverse formula (which rounds down) produces a forwarded amount
whose `Hop.ofEdge` ceiling-rounded fee exceeds the incoming amount.  With
`base = 0`, `ppm = 1000`, `incoming = 1000` the formula forwards `1000` and
`ofEdge` charges `ceil(1000 * 1000 / 1e6) = 1`, i.e. one msat too much.
This is why the module does not claim the inverse identity; see the report.
-/
theorem ofEdge_rounding_counterexample :
    ∃ (base ppm incoming : Nat),
      let forwarded :=
        ((incoming - base) * 1000000 + 1000000 + ppm - 1) / (1000000 + ppm)
      incoming < forwarded + base + (forwarded * ppm + 999999) / 1000000 := by
  refine ⟨0, 1000, 1000, ?_⟩
  decide

/-! ## 3. CLTV arithmetic -/

/-- The CLTV expiry that the sender must put on the HTLC arriving at hop
`i`, given the expiry `finalExpiry` at the recipient:
`finalExpiry + sum of the deltas of hops i, i+1, ..., n-1`.

This decreases downstream: crossing hop `i` subtracts `delta_i` from the
outgoing expiry (BOLT 4, `outgoing_cltv_value`).  Read from the recipient
back towards the sender it strictly increases when every delta is
positive. -/
def Route.cltvAt (r : Route) (finalExpiry : Nat) (i : Nat) : Nat :=
  finalExpiry + ((r.hops.drop i).map Hop.cltvDelta).sum

/-- The total CLTV offset: all hop deltas plus the final recipient delta.
This is BOLT 7's route-level sum (`refs/bolts/07-routing-gossip.md:1031-1047`)
with the final `min_final_cltv_expiry_delta` made explicit. -/
def Route.totalCltvWithFinal (r : Route) (finalDelta : Nat) : Nat :=
  r.totalCltv + finalDelta

/-- The decomposition "sum of hop deltas plus final delta". -/
theorem Route.totalCltvWithFinal_eq (r : Route) (finalDelta : Nat) :
    r.totalCltvWithFinal finalDelta =
      (r.hops.map Hop.cltvDelta).sum + finalDelta := rfl

/-- Prepending a hop adds its delta to the total, with the final delta
carried unchanged. -/
theorem Route.totalCltvWithFinal_cons (h : Hop) (r : Route)
    (finalDelta : Nat) :
    (r.cons h).totalCltvWithFinal finalDelta =
      h.cltvDelta + r.totalCltvWithFinal finalDelta := by
  simp only [Route.totalCltvWithFinal, Route.totalCltv_cons]
  omega

/-- The sender's expiry from a route height and a final delta is the height
plus the total CLTV offset. -/
theorem Route.cltvAt_zero_eq_height_add_total (r : Route) (height finalDelta : Nat) :
    r.cltvAt (height + finalDelta) 0 =
      height + r.totalCltvWithFinal finalDelta := by
  simp only [Route.cltvAt, Route.totalCltvWithFinal, Route.totalCltv,
    List.drop_zero]
  omega

/-- The sender's expiry at hop `0` is the final expiry plus the total hop
delta. -/
theorem Route.cltvAt_zero (r : Route) (finalExpiry : Nat) :
    r.cltvAt finalExpiry 0 = finalExpiry + r.totalCltv := by
  simp [Route.cltvAt, Route.totalCltv]

/-- Past the last hop the expiry is exactly the recipient's expiry. -/
theorem Route.cltvAt_length (r : Route) (finalExpiry : Nat) :
    r.cltvAt finalExpiry r.hops.length = finalExpiry := by
  simp [Route.cltvAt]

/-- **Per-hop CLTV step.**  The expiry at hop `i` is the expiry at hop
`i + 1` plus hop `i`'s delta. -/
theorem Route.cltvAt_succ (r : Route) (finalExpiry : Nat) (i : Nat)
    (hi : i < r.hops.length) :
    r.cltvAt finalExpiry i =
      r.cltvAt finalExpiry (i + 1) + (r.hops[i]'hi).cltvDelta := by
  unfold Route.cltvAt
  rw [List.drop_eq_getElem_cons hi]
  simp only [List.map_cons, List.sum_cons]
  omega

/-- One step downstream strictly lowers the required expiry. -/
theorem Route.cltvAt_step_lt (r : Route) (finalExpiry : Nat)
    (hpos : ∀ h ∈ r.hops, 0 < h.cltvDelta) {i : Nat}
    (hi : i < r.hops.length) :
    r.cltvAt finalExpiry (i + 1) < r.cltvAt finalExpiry i := by
  rw [Route.cltvAt_succ r finalExpiry i hi]
  have hh : 0 < (r.hops[i]'hi).cltvDelta := hpos _ (List.getElem_mem hi)
  omega

/-- Auxiliary form of `cltvAt_strict_anti` with `i` quantified inside the
induction motive. -/
theorem Route.cltvAt_strict_anti_aux (r : Route) (finalExpiry : Nat)
    (hpos : ∀ h ∈ r.hops, 0 < h.cltvDelta) :
    ∀ j, j ≤ r.hops.length → ∀ i, i < j →
      r.cltvAt finalExpiry j < r.cltvAt finalExpiry i := by
  intro j
  induction j with
  | zero =>
    intro _hj i hij
    omega
  | succ j ih =>
    intro hj i hij
    by_cases hEq : i = j
    · subst i
      exact Route.cltvAt_step_lt r finalExpiry hpos (by omega : j < r.hops.length)
    · have hij' : i < j := by omega
      have hj' : j ≤ r.hops.length := by omega
      exact Nat.lt_trans
        (Route.cltvAt_step_lt r finalExpiry hpos (by omega : j < r.hops.length))
        (ih hj' i hij')

/-- **Strict monotonicity from the recipient back to the sender.**  If every
hop has a positive `cltv_expiry_delta` and `i < j`, then the expiry required
at hop `i` (upstream) is strictly larger than the expiry required at hop
`j` (downstream).  Equivalently, the expiry strictly decreases along the
forward route direction. -/
theorem Route.cltvAt_strict_anti (r : Route) (finalExpiry : Nat)
    (hpos : ∀ h ∈ r.hops, 0 < h.cltvDelta)
    {i j : Nat} (hij : i < j) (hj : j ≤ r.hops.length) :
    r.cltvAt finalExpiry j < r.cltvAt finalExpiry i :=
  Route.cltvAt_strict_anti_aux r finalExpiry hpos j hj i hij

/-! ## 4. Amount arithmetic -/

/-- Fees charged on hop `i` and all downstream hops, in sender order. -/
def Route.downstreamFee (r : Route) (i : Nat) : Nat :=
  ((r.hops.drop i).map fun h => h.feeMsat.val).sum

/-- The amount carried on hop `i` when the recipient receives
`r.amountMsat`: the final amount plus the fees of hop `i` and all hops after
it.  The amount decreases downstream by exactly one hop fee. -/
def Route.amountAt (r : Route) (i : Nat) : Nat :=
  r.amountMsat.val + r.downstreamFee i

/-- Definitional form of "amount at a hop = final amount + downstream fees". -/
theorem Route.amountAt_eq_final_add_downstream (r : Route) (i : Nat) :
    r.amountAt i = r.amountMsat.val +
      ((r.hops.drop i).map fun h => h.feeMsat.val).sum := rfl

/-- **No hidden fee at the sender.**  The sender's amount is the amount the
recipient receives plus the sum of the per-hop fees. -/
theorem Route.amountAt_zero (r : Route) :
    r.amountAt 0 = r.amountMsat.val + r.totalFee.val := by
  simp [Route.amountAt, Route.downstreamFee, Route.totalFee]

/-- **Per-hop amount step.**  The amount on hop `i` is the amount on hop
`i + 1` plus hop `i`'s fee. -/
theorem Route.amountAt_succ (r : Route) (i : Nat)
    (hi : i < r.hops.length) :
    r.amountAt i = r.amountAt (i + 1) + (r.hops[i]'hi).feeMsat.val := by
  unfold Route.amountAt Route.downstreamFee
  rw [List.drop_eq_getElem_cons hi]
  simp only [List.map_cons, List.sum_cons]
  omega

/-- The amount on the last hop is the final amount plus that hop's fee. -/
theorem Route.amountAt_last (r : Route) (hne : r.hops ≠ []) :
    r.amountAt (r.hops.length - 1) =
      r.amountMsat.val + (r.hops.getLast hne).feeMsat.val := by
  have hpos : 0 < r.hops.length := List.length_pos_iff.mpr hne
  have hi : r.hops.length - 1 < r.hops.length := by omega
  have hnil : r.hops.drop (r.hops.length - 1 + 1) = [] := by
    rw [Nat.sub_add_cancel (by omega : 1 ≤ r.hops.length)]
    exact List.drop_eq_nil_of_le (Nat.le_refl _)
  have hlast : r.hops[r.hops.length - 1]'hi = r.hops.getLast hne := by
    simpa using List.getElem_length_sub_one_eq_getLast hi
  unfold Route.amountAt Route.downstreamFee
  rw [List.drop_eq_getElem_cons hi, hnil]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [hlast]
  omega

/-! ## 5. Route blinding: exposed fields and preserved arithmetic -/

/-- The plaintext relay terms of a blinded hop: BOLT 4's `payment_relay`
(`fee_base_msat`, `fee_proportional_millionths`, `cltv_expiry_delta`), of
which this model keeps the resulting msat fee and the CLTV delta.  These are
carried inside `encrypted_recipient_data`, not in the `blinded_path` wire
record. -/
structure BlindedTerms where
  feeMsat : Msat
  cltvDelta : Nat
deriving Repr, DecidableEq, BEq

/-- One hop of a BOLT 4 `blinded_path`.

* `blindedNodeId` and `encryptedRecipientData` are the wire fields
  (`blinded_path_hop` in BOLT 4).
* `realNode`, `shortChannelId`, and `terms` are creator-side data.  The
  `short_channel_id` and the relay terms live inside
  `encryptedRecipientData` in the real protocol; the model keeps them as
  fields so that the arithmetic can be stated.
* `first_node_id` and `first_path_key` live on `BlindedPath`. -/
structure BlindedHop where
  realNode : NodeId
  blindedNodeId : NodeId
  shortChannelId : ShortChannelId
  terms : BlindedTerms
  encryptedRecipientData : ByteArray
deriving Repr, BEq

namespace BlindedHop

/-- The sender-visible wire view of a blinded hop: only the blinded node id
and the encrypted recipient data.  The real node id, channel id, and
plaintext relay terms are absent. -/
def exposed (h : BlindedHop) : NodeId × ByteArray :=
  (h.blindedNodeId, h.encryptedRecipientData)

/-- **Non-interference in the real node id.**  Two hops that agree on the
wire fields but differ in the real node id have the same exposed view. -/
theorem exposed_realNode_irrelevant (n₁ n₂ : NodeId) (blinded : NodeId)
    (scid : ShortChannelId) (terms : BlindedTerms) (enc : ByteArray) :
    (⟨n₁, blinded, scid, terms, enc⟩ : BlindedHop).exposed =
      (⟨n₂, blinded, scid, terms, enc⟩ : BlindedHop).exposed := rfl

/-- **Non-interference in the plaintext relay terms.**  The wire view does
not expose the fee or the CLTV delta; they are authenticated inside
`encryptedRecipientData` (not modelled cryptographically). -/
theorem exposed_terms_irrelevant (n blinded : NodeId) (scid : ShortChannelId)
    (t₁ t₂ : BlindedTerms) (enc : ByteArray) :
    (⟨n, blinded, scid, t₁, enc⟩ : BlindedHop).exposed =
      (⟨n, blinded, scid, t₂, enc⟩ : BlindedHop).exposed := rfl

end BlindedHop

/-- A BOLT 4 blinded path.  The wire record is
`(introduction, firstPathKey, hops.map exposed)`; `amountMsat` is the
payment amount as in `Route`. -/
structure BlindedPath where
  introduction : NodeId
  firstPathKey : PubKey
  hops : List BlindedHop
  amountMsat : Msat
deriving Repr, BEq

namespace BlindedPath

/-- The sender-visible wire view of the path: introduction node, first path
key, and the exposed hop records.  The real node ids and plaintext terms are
not part of this type. -/
def exposedWire (b : BlindedPath) :
    NodeId × PubKey × List (NodeId × ByteArray) :=
  (b.introduction, b.firstPathKey, b.hops.map BlindedHop.exposed)

/-- **Path-level non-interference.**  The wire view depends only on the
introduction node, the first path key, and the exposed hop records.  Two
paths that agree on those fields have the same wire view, whatever their
real node ids, plaintext terms, or payment amount. -/
theorem exposedWire_eq_of_exposed_hops (b₁ b₂ : BlindedPath)
    (hi : b₁.introduction = b₂.introduction)
    (hk : b₁.firstPathKey = b₂.firstPathKey)
    (hh : b₁.hops.map BlindedHop.exposed =
      b₂.hops.map BlindedHop.exposed) :
    b₁.exposedWire = b₂.exposedWire := by
  simp [BlindedPath.exposedWire, hi, hk, hh]

/-- Reinterpret a blinded path as a wave-A `Route`, selecting either the real
or the blinded node id for each hop.  The fee, CLTV delta, and amount come
from the same `terms` and `amountMsat` in both cases. -/
def toRouteUsing (b : BlindedPath) (sel : BlindedHop → NodeId) : Route :=
  { hops := b.hops.map fun h =>
      { node := sel h
        shortChannelId := h.shortChannelId
        feeMsat := h.terms.feeMsat
        cltvDelta := h.terms.cltvDelta }
    amountMsat := b.amountMsat }

/-- The route an observer/sender could reconstruct from the blinded path: hop
destinations are blinded node ids. -/
def toBlindedRoute (b : BlindedPath) : Route :=
  b.toRouteUsing BlindedHop.blindedNodeId

/-- The creator's unblinded route: hop destinations are the real node ids. -/
def toRealRoute (b : BlindedPath) : Route :=
  b.toRouteUsing BlindedHop.realNode

/-- **Fee preservation.**  The blinded route's total fee is the sum of the
plaintext terms, independent of which node selector is used. -/
theorem toRouteUsing_totalFee (b : BlindedPath) (sel : BlindedHop → NodeId) :
    (b.toRouteUsing sel).totalFee.val =
      (b.hops.map fun h => h.terms.feeMsat.val).sum := by
  simp [BlindedPath.toRouteUsing, Route.totalFee, List.map_map,
    Function.comp_def]

/-- **CLTV preservation.**  The blinded route's total CLTV delta is the sum
of the plaintext terms, independent of the node selector. -/
theorem toRouteUsing_totalCltv (b : BlindedPath) (sel : BlindedHop → NodeId) :
    (b.toRouteUsing sel).totalCltv =
      (b.hops.map fun h => h.terms.cltvDelta).sum := by
  simp [BlindedPath.toRouteUsing, Route.totalCltv, List.map_map,
    Function.comp_def]

/-- The amount schedule of a `toRouteUsing` interpretation depends only on
the plaintext terms, not on the node selector. -/
theorem toRouteUsing_downstreamFee (b : BlindedPath) (sel : BlindedHop → NodeId)
    (i : Nat) :
    (b.toRouteUsing sel).downstreamFee i =
      ((b.hops.map fun h => h.terms.feeMsat.val).drop i).sum := by
  simp [BlindedPath.toRouteUsing, Route.downstreamFee, List.map_map,
    Function.comp_def]

/-- The channel-id sequence of a `toRouteUsing` interpretation depends only
on the channels, not on the node selector. -/
theorem toRouteUsing_scidsOf (b : BlindedPath) (sel : BlindedHop → NodeId) :
    scidsOf (b.toRouteUsing sel).hops =
      b.hops.map fun h => h.shortChannelId := by
  simp [BlindedPath.toRouteUsing, scidsOf, List.map_map, Function.comp_def]

/-- **Blinding preserves the fee arithmetic.**  Real and blinded routes have
the same total fee. -/
theorem blinded_real_totalFee_val (b : BlindedPath) :
    (b.toBlindedRoute).totalFee.val = (b.toRealRoute).totalFee.val := by
  unfold BlindedPath.toBlindedRoute BlindedPath.toRealRoute
  rw [toRouteUsing_totalFee b BlindedHop.blindedNodeId,
      toRouteUsing_totalFee b BlindedHop.realNode]

theorem blinded_real_totalFee (b : BlindedPath) :
    (b.toBlindedRoute).totalFee = (b.toRealRoute).totalFee :=
  congrArg Msat.mk (blinded_real_totalFee_val b)

/-- **Blinding preserves the CLTV arithmetic.**  Real and blinded routes have
the same total CLTV delta. -/
theorem blinded_real_totalCltv (b : BlindedPath) :
    (b.toBlindedRoute).totalCltv = (b.toRealRoute).totalCltv := by
  unfold BlindedPath.toBlindedRoute BlindedPath.toRealRoute
  rw [toRouteUsing_totalCltv b BlindedHop.blindedNodeId,
      toRouteUsing_totalCltv b BlindedHop.realNode]

/-- The payment amount is the same in the real and blinded interpretations. -/
theorem blinded_real_amountMsat (b : BlindedPath) :
    (b.toBlindedRoute).amountMsat = (b.toRealRoute).amountMsat := rfl

/-- **Blinding preserves the per-hop amount schedule.**  For every hop index,
the amount carried is the same in the real and blinded interpretations. -/
theorem blinded_real_amountAt (b : BlindedPath) (i : Nat) :
    (b.toBlindedRoute).amountAt i = (b.toRealRoute).amountAt i := by
  unfold BlindedPath.toBlindedRoute BlindedPath.toRealRoute Route.amountAt
  rw [toRouteUsing_downstreamFee b BlindedHop.blindedNodeId i,
      toRouteUsing_downstreamFee b BlindedHop.realNode i]
  rfl

/-- A non-empty blinded path yields a non-empty route. -/
theorem blindedRoute_nonempty {b : BlindedPath} (hne : b.hops ≠ []) :
    (b.toBlindedRoute).NonEmpty := by
  simp [BlindedPath.toBlindedRoute, BlindedPath.toRouteUsing,
    Route.NonEmpty, hne]

/-- Distinctness of channel ids is the same in the real and blinded
interpretations, since blinding changes node identities, not channels. -/
theorem blindedRoute_distinctScids_iff (b : BlindedPath) :
    ScidsDistinct (b.toBlindedRoute).hops ↔
      ScidsDistinct (b.toRealRoute).hops := by
  unfold BlindedPath.toBlindedRoute BlindedPath.toRealRoute ScidsDistinct
  rw [toRouteUsing_scidsOf b BlindedHop.blindedNodeId,
      toRouteUsing_scidsOf b BlindedHop.realNode]

end BlindedPath

/-! ## 6. Checked concrete facts

These are kernel-checked (`decide`) on a small finite route, with no
unproved placeholder.
The route has three hops on channels `(100,1,0)`, `(100,1,1)`, `(100,2,0)`,
fees `10, 20, 30` msat, and deltas `5, 6, 7`.
-/

/-- A small concrete hop constructor for the checked examples. -/
def exampleHop (node block tx output fee delta : Nat) : Hop :=
  { node := ⟨node⟩
    shortChannelId := ⟨block, tx, output⟩
    feeMsat := ⟨fee⟩
    cltvDelta := delta }

/-- The three-hop example route: final amount 1000 msat. -/
def exampleRoute : Route :=
  { hops := [exampleHop 0 100 1 0 10 5,
             exampleHop 1 100 1 1 20 6,
             exampleHop 2 100 2 0 30 7]
    amountMsat := ⟨1000⟩ }

/-- The example route's components: non-empty and channel ids distinct. -/
theorem example_wellFormed_unfolded :
    exampleRoute.hops ≠ [] ∧ (scidsOf exampleRoute.hops).Nodup := by
  decide

/-- The example route is well formed: non-empty and channel ids distinct. -/
theorem example_wellFormed : exampleRoute.WellFormed :=
  (route_wellFormed_iff exampleRoute).mpr example_wellFormed_unfolded

/-- The total fee is exactly `10 + 20 + 30 = 60` msat. -/
theorem example_totalFee : exampleRoute.totalFee = ⟨60⟩ := by
  decide

/-- The total CLTV offset including a final delta of 9 is `5+6+7+9 = 27`. -/
theorem example_totalCltvWithFinal :
    exampleRoute.totalCltvWithFinal 9 = 27 := by
  decide

/-- The sender's expiry with recipient expiry 800 is `800 + 5 + 6 + 7 = 818`. -/
theorem example_cltvAt_zero : exampleRoute.cltvAt 800 0 = 818 := by
  decide

/-- The expiry required at the last hop is `800 + 7 = 807`. -/
theorem example_cltvAt_last :
    exampleRoute.cltvAt 800 (exampleRoute.hops.length - 1) = 807 := by
  decide

/-- Upstream expiry 818 is strictly larger than downstream expiry 807: the
checkable instance of `Route.cltvAt_strict_anti`. -/
theorem example_cltv_upstream :
    exampleRoute.cltvAt 800 2 < exampleRoute.cltvAt 800 0 := by
  decide

/-- The sender's amount is the final 1000 msat plus the 60 msat fee. -/
theorem example_senderAmount : exampleRoute.amountAt 0 = 1060 := by
  decide

/-- The amount on the last hop is `1000 + 30 = 1030`. -/
theorem example_amountAt_last :
    exampleRoute.amountAt (exampleRoute.hops.length - 1) = 1030 := by
  decide

end LnLean.Routing
