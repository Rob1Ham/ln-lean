import LnLean.Basic.Core
import LnLean.Channel.HTLC

/-!
# LnLean.Proofs.Channel.HTLCProps

English claim.  This module states the lifecycle laws of one Lightning HTLC as
it is modelled in `LnLean.Channel.HTLC`, from the point of view of one channel
endpoint:

* a successful `fulfillHTLC` carries a preimage of exactly 32 bytes whose
  image under the caller-supplied hash function is the HTLC's payment hash
  (the cryptographic premise is a hypothesis, never an axiom);
* the only successful lifecycle outcomes reachable from a live (in
  particular, an `offered`) HTLC are `fulfilled` and `failed` — including
  the on-chain timeout, which additionally requires an offered HTLC and a
  chain height at or past `cltv_expiry`; `fulfilled` and `failed` are
  mutually exclusive; a pre-settlement HTLC cannot be removed directly;
* an added HTLC is positive, fits under `max_htlc_value_in_flight_msat`, and
  its amount lies in `[htlc_minimum_msat, max_htlc_value_in_flight_msat]`
  under the explicit precondition `htlc_minimum_msat ≤ amount` (the model's
  `addHTLC` does not take the minimum, see the counterexample below);
* an added HTLC has `cltv_expiry < 500000000`; an offered HTLC can only time
  out at or after its expiry, hence an HTLC with `height < cltv_expiry`
  cannot be timed out at that height.  The model does not itself compare
  `cltv_expiry` with the current height at add time (see the gap note);
* a dust HTLC has no commitment output but is still a member of the live
  HTLC set;
* adding an HTLC and then removing its id restores the original list whenever
  the id does not already occur, and in particular whenever the ids in the
  extended set are distinct.

BOLT sections.
* BOLT 2 §Adding an HTLC (`update_add_htlc`): `refs/bolts/02-peer-protocol.md:2783`
  (message type), `:2822` (`amount_msat > 0`), `:2823`
  (`amount_msat >= htlc_minimum_msat`), `:2824`
  (`cltv_expiry < 500000000`), `:2828-2831`
  (`max_htlc_value_in_flight_msat`).
* BOLT 2 §Removing an HTLC (`update_fulfill_htlc`, `update_fail_htlc`):
  `refs/bolts/02-peer-protocol.md:2921` (message type), `:2925`
  (`32*byte payment_preimage`), `:3004-3006` (the preimage MUST SHA256-hash
  to the HTLC `payment_hash`), `:2944` (`update_fail_htlc`), `:2965-2975`
  (an HTLC SHOULD be failed once it has timed out).
* BOLT 3 §Commitment Transaction Outputs:
  `refs/bolts/03-transactions.md:110` (trimming rule),
  `:199` (offered HTLC output), `:305` (trimmed outputs), `:330-350`
  (MUST NOT produce an HTLC output below `dust_limit_satoshis`),
  `:360` (timeout locktime is `cltv_expiry`), `:367`
  (`amount_msat / 1000`, rounding down).

rust-lightning anchors at pinned commit `fe49009`.
* `lightning/src/ln/chan_utils.rs:716` (`HTLCOutputInCommitment`;
  `transaction_output_index : Option<u32>` is `None` for a trimmed output).
* `lightning/src/ln/chan_utils.rs:739` (`to_bitcoin_amount`, `amount_msat / 1000`).
* `lightning/src/ln/chan_utils.rs:875` (`build_htlc_transaction`),
  `:899` (`lock_time = cltv_expiry` iff `htlc.offered`).
* `lightning/src/ln/chan_utils.rs:919` (`build_htlc_output` subtracts the
  second-stage fee).
* `lightning/src/ln/channel.rs:8368` (`update_add_htlc`),
  `:8389` (reject amount below `holder_htlc_minimum_msat`),
  `:8395` (reject `cltv_expiry >= 500000000`),
  `:11932` (forwarding requires `cltv_expiry >= outgoing_cltv + delta`).

What is explicitly NOT modelled.
* No concrete SHA-256 and no collision-resistance axiom.  Preimage soundness
  is a transition guard; preimage *uniqueness* is stated conditionally on an
  injectivity hypothesis `hcoll`, which is the shape of assumption C1.
* `addHTLC` has no `htlc_minimum_msat` argument; the lower-bound theorem is
  conditional and a concrete counterexample shows the gap.
* `addHTLC` has no current-height argument; "expiry strictly in the future"
  is only available as a hypothesis at timeout time, not at add time.
* No wire encoding, onion payload, MPP, per-commitment orientation flip,
  fee estimation, or value conservation across the commitment (that belongs
  to the commitment/conservation modules).  `HTLCState.removed` is treated as
  the terminal bookkeeping state.
* The list operations below (`addToSet`, `removeFromSet`) are a proof-level
  abstraction of the channel's HTLC set; they are not imported from, and do
  not change, the model module.

Obligation ids.  Catalog `LN-HT-001` is `LN-HTLC-001` here; `LN-HT-002` is
`LN-HTLC-007`; `LN-HT-004` is `LN-HTLC-009`.
-/

namespace LnLean.Proofs.Channel.HTLCProps

open LnLean LnLean.Channel

set_option autoImplicit false

/-! ## The HTLC set as a list -/

/-- The commitment's HTLC set after accepting `h`.  The model keeps the
insertion order; ordering is irrelevant to the laws below. -/
def addToSet (h : HTLC) (hs : List HTLC) : List HTLC := h :: hs

/-- Remove the HTLC with the given BOLT 2 `id` from the set.  Removing an id
that is absent is the identity (unlike `removeHTLC`, which is a state
transition on one record). -/
def removeFromSet (id : Nat) (hs : List HTLC) : List HTLC :=
  hs.filter (fun x => decide (x.id ≠ id))

/-- All BOLT 2 ids in the list are pairwise distinct. -/
def idsDistinct (hs : List HTLC) : Prop := (hs.map HTLC.id).Nodup

theorem removeFromSet_of_forall_ne (id : Nat) (hs : List HTLC)
    (h : ∀ x ∈ hs, x.id ≠ id) : removeFromSet id hs = hs := by
  unfold removeFromSet
  rw [List.filter_eq_self]
  intro x hx
  exact decide_eq_true_iff.mpr (h x hx)

theorem removeFromSet_add_self (h : HTLC) (hs : List HTLC) :
    removeFromSet h.id (addToSet h hs) = removeFromSet h.id hs := by
  simp [removeFromSet, addToSet]

/-- Adding an HTLC and removing its id restores the original set, provided the
id is fresh for the original set. -/
theorem add_remove_restores (h : HTLC) (hs : List HTLC)
    (hfresh : ∀ x ∈ hs, x.id ≠ h.id) :
    removeFromSet h.id (addToSet h hs) = hs := by
  rw [removeFromSet_add_self]
  exact removeFromSet_of_forall_ne h.id hs hfresh

theorem idsDistinct_cons {h : HTLC} {hs : List HTLC}
    (hnd : idsDistinct (h :: hs)) : ∀ x ∈ hs, x.id ≠ h.id := by
  intro x hx heq
  have hmem : h.id ∈ hs.map HTLC.id := List.mem_map.mpr ⟨x, hx, heq⟩
  exact (List.nodup_cons.mp hnd).1 hmem

/-- The distinct-id form of the add/remove round trip: if the ids of
`h :: hs` are distinct, adding `h` and removing `h.id` yields `hs` exactly. -/
theorem add_remove_restores_of_idsDistinct (h : HTLC) (hs : List HTLC)
    (hnd : idsDistinct (addToSet h hs)) :
    removeFromSet h.id (addToSet h hs) = hs :=
  add_remove_restores h hs (idsDistinct_cons (h := h) (hs := hs) hnd)

theorem idsDistinct_addToSet {h : HTLC} {hs : List HTLC}
    (hnd : idsDistinct hs) (hfresh : ∀ x ∈ hs, x.id ≠ h.id) :
    idsDistinct (addToSet h hs) := by
  unfold idsDistinct addToSet at *
  rw [List.map_cons, List.nodup_cons]
  refine ⟨?_, hnd⟩
  rw [List.mem_map]
  rintro ⟨x, hx, heq⟩
  exact hfresh x hx heq

/-! ## Fulfillment: a 32-byte preimage that hashes to the payment hash -/

theorem fulfill_live (hashFn : ByteArray → ByteArray) {h h' : HTLC} {p : Preimage}
    (ok : fulfillHTLC hashFn h p = .ok h') : h.isLive = true := by
  unfold fulfillHTLC at ok
  split at ok
  · rename_i hl
    exact hl
  · simp at ok

/-- Every successful fulfillment reveals a 32-byte preimage (BOLT 2's
`32*byte payment_preimage` field). -/
theorem fulfill_preimage_valid (hashFn : ByteArray → ByteArray) {h h' : HTLC}
    {p : Preimage} (ok : fulfillHTLC hashFn h p = .ok h') : p.Valid :=
  (fulfillHTLC_hash hashFn h h' p ok).1

/-- Every successful fulfillment satisfies the hash equation.  This is the
conditional cryptographic law: `hashFn` is supplied by the caller and the
equation is part of the transition guard. -/
theorem fulfill_hash_matches (hashFn : ByteArray → ByteArray) {h h' : HTLC}
    {p : Preimage} (ok : fulfillHTLC hashFn h p = .ok h') :
    hashFn p.bytes = h.paymentHash.bytes :=
  (fulfillHTLC_hash hashFn h h' p ok).2

/-- Conversely, a live HTLC plus a 32-byte preimage with a matching hash is
accepted. -/
theorem fulfill_succeeds (hashFn : ByteArray → ByteArray) (h : HTLC) (p : Preimage)
    (hl : h.isLive = true) (hlen : p.bytes.size = 32)
    (hhash : hashFn p.bytes = h.paymentHash.bytes) :
    ∃ h', fulfillHTLC hashFn h p = .ok h' := by
  refine ⟨{ h with state := .fulfilled }, ?_⟩
  simp [fulfillHTLC, hl, hlen, hhash]

/-- A successful fulfillment sets the state to `fulfilled`. -/
theorem fulfill_result_fulfilled (hashFn : ByteArray → ByteArray) (h h' : HTLC)
    (p : Preimage) (ok : fulfillHTLC hashFn h p = .ok h') :
    h'.state = .fulfilled := by
  rw [fulfillHTLC_state hashFn h h' p ok]

/-- Conditional preimage uniqueness: if the hash function is injective (the
formal shape of assumption C1), two preimages that both fulfill the same HTLC
are equal.  The injectivity premise is explicit and is not an axiom. -/
theorem fulfill_preimage_unique (hashFn : ByteArray → ByteArray)
    (hcoll : ∀ a b : ByteArray, hashFn a = hashFn b → a = b)
    {h h1 h2 : HTLC} {p1 p2 : Preimage}
    (ok1 : fulfillHTLC hashFn h p1 = .ok h1)
    (ok2 : fulfillHTLC hashFn h p2 = .ok h2) :
    p1 = p2 := by
  have e1 := (fulfillHTLC_hash hashFn h h1 p1 ok1).2
  have e2 := (fulfillHTLC_hash hashFn h h2 p2 ok2).2
  have hb : p1.bytes = p2.bytes := hcoll p1.bytes p2.bytes (by rw [e1, e2])
  cases p1
  cases p2
  simp_all

/-! ## Failure and timeout -/

theorem fail_live (h h' : HTLC) (ok : failHTLC h = .ok h') : h.isLive = true := by
  unfold failHTLC at ok
  split at ok
  · rename_i hl
    exact hl
  · simp at ok

theorem fail_state (h h' : HTLC) (ok : failHTLC h = .ok h') :
    h' = { h with state := .failed } := by
  unfold failHTLC at ok
  split at ok
  · simp only [Result.ok.injEq] at ok
    exact ok.symm
  · simp at ok

theorem fail_result_failed (h h' : HTLC) (ok : failHTLC h = .ok h') :
    h'.state = .failed := by
  rw [fail_state h h' ok]

/-- An on-chain timeout additionally requires an offered HTLC and a chain
height at or past `cltv_expiry`. -/
theorem timeout_requires_offered_and_expiry (height : Height) (h h' : HTLC)
    (ok : timeoutHTLC height h = .ok h') :
    h.direction = .local ∧ h.cltvExpiry ≤ height :=
  ⟨timeoutHTLC_direction height h h' ok, timeoutHTLC_expiry height h h' ok⟩

theorem timeout_state (height : Height) (h h' : HTLC)
    (ok : timeoutHTLC height h = .ok h') :
    h' = { h with state := .failed } := by
  unfold timeoutHTLC at ok
  split at ok
  · simp only [Result.ok.injEq] at ok
    exact ok.symm
  · simp at ok

theorem timeout_result_failed (height : Height) (h h' : HTLC)
    (ok : timeoutHTLC height h = .ok h') : h'.state = .failed := by
  rw [timeout_state height h h' ok]

/-- An offered HTLC can only time out at or after its expiry, hence at a
height strictly below the expiry the timeout transition is rejected. -/
theorem timeout_before_expiry (height : Height) (h : HTLC)
    (hgt : height < h.cltvExpiry) :
    timeoutHTLC height h = .error ⟨.expiryTooSoon, ByteArray.empty⟩ := by
  simp [timeoutHTLC, Nat.not_le.mpr hgt]

/-- At or after the expiry, a live offered HTLC times out successfully. -/
theorem timeout_at_expiry (height : Height) (h : HTLC) (hl : h.isLive = true)
    (hd : h.direction = .local) (he : h.cltvExpiry ≤ height) :
    ∃ h', timeoutHTLC height h = .ok h' ∧ h'.state = .failed := by
  refine ⟨{ h with state := .failed }, ?_, rfl⟩
  simp [timeoutHTLC, hl, hd, he]

/-! ## Terminal states -/

theorem fulfilled_ne_failed : HTLCState.fulfilled ≠ HTLCState.failed := by
  decide

/-- `fulfilled` and `failed` are mutually exclusive as states of one HTLC. -/
theorem fulfilled_failed_exclusive (h : HTLC) :
    ¬ (h.state = .fulfilled ∧ h.state = .failed) := by
  rintro ⟨h1, h2⟩
  exact fulfilled_ne_failed (h1.symm.trans h2)

/-- A settled HTLC is no longer live. -/
theorem settled_not_live (h : HTLC)
    (hs : h.state = .fulfilled ∨ h.state = .failed) : h.isLive = false := by
  rcases hs with h | h <;> simp [HTLC.isLive, h]

/-- An `offered` HTLC is live. -/
theorem offered_isLive (h : HTLC) (ho : h.state = .offered) : h.isLive = true := by
  rw [HTLC.isLive, ho]
  rfl

/-- Every successful settlement (fulfill, fail, or timeout) of a live HTLC
lands in `fulfilled` or `failed`.  Combined with `remove_not_settled`, this
says that those are the only terminal transitions available to an offered
HTLC. -/
theorem settlement_terminal (hashFn : ByteArray → ByteArray) (height : Height)
    {h h' : HTLC}
    (hres : (∃ p, fulfillHTLC hashFn h p = .ok h') ∨
      failHTLC h = .ok h' ∨ timeoutHTLC height h = .ok h') :
    h'.state = .fulfilled ∨ h'.state = .failed := by
  rcases hres with ⟨p, hp⟩ | hf | ht
  · exact Or.inl (fulfill_result_fulfilled hashFn h h' p hp)
  · exact Or.inr (fail_result_failed h h' hf)
  · exact Or.inr (timeout_result_failed height h h' ht)

/-- A pre-settlement (`offered` or `received`) HTLC cannot be removed
directly: removal is only defined for `fulfilled` and `failed`. -/
theorem remove_not_settled (h : HTLC)
    (hs : h.state = .offered ∨ h.state = .received) :
    removeHTLC h = .error ⟨.update, ByteArray.empty⟩ := by
  rcases hs with h | h <;> simp [removeHTLC, h]

/-! ## Amount bounds -/

/-- The channel's advertised amount band for an HTLC. -/
def amountWithinBounds (minMsat maxMsat : Msat) (h : HTLC) : Prop :=
  minMsat.val ≤ h.amountMsat.val ∧ h.amountMsat.val ≤ maxMsat.val

theorem add_guard (maxHtlcValue currentTotal : Msat) (id : Nat)
    (dir : Direction) (amount : Msat) (ph : PaymentHash) (cltv : Height)
    (h : HTLC) (ok : addHTLC maxHtlcValue currentTotal id dir amount ph cltv = .ok h) :
    0 < amount.val ∧ currentTotal.val + amount.val ≤ maxHtlcValue.val ∧
      cltv < MAX_CLTV_EXPIRY := by
  unfold addHTLC at ok
  split at ok
  · assumption
  · simp at ok

theorem add_amountMsat_eq (maxHtlcValue currentTotal : Msat) (id : Nat)
    (dir : Direction) (amount : Msat) (ph : PaymentHash) (cltv : Height)
    (h : HTLC) (ok : addHTLC maxHtlcValue currentTotal id dir amount ph cltv = .ok h) :
    h.amountMsat = amount := by
  unfold addHTLC at ok
  split at ok
  · simp only [Result.ok.injEq] at ok
    subst ok
    rfl
  · simp at ok

theorem add_cltvExpiry_eq (maxHtlcValue currentTotal : Msat) (id : Nat)
    (dir : Direction) (amount : Msat) (ph : PaymentHash) (cltv : Height)
    (h : HTLC) (ok : addHTLC maxHtlcValue currentTotal id dir amount ph cltv = .ok h) :
    h.cltvExpiry = cltv := by
  unfold addHTLC at ok
  split at ok
  · simp only [Result.ok.injEq] at ok
    subst ok
    rfl
  · simp at ok

/-- An accepted HTLC has a strictly positive amount (BOLT 2 MUST). -/
theorem add_amount_pos (maxHtlcValue currentTotal : Msat) (id : Nat)
    (dir : Direction) (amount : Msat) (ph : PaymentHash) (cltv : Height)
    (h : HTLC) (ok : addHTLC maxHtlcValue currentTotal id dir amount ph cltv = .ok h) :
    0 < h.amountMsat.val := by
  have hg := add_guard maxHtlcValue currentTotal id dir amount ph cltv h ok
  have ha := add_amountMsat_eq maxHtlcValue currentTotal id dir amount ph cltv h ok
  rw [ha]
  exact hg.1

/-- An accepted HTLC fits under `max_htlc_value_in_flight_msat`, even on its
own (the running total is non-negative). -/
theorem add_amount_le_max (maxHtlcValue currentTotal : Msat) (id : Nat)
    (dir : Direction) (amount : Msat) (ph : PaymentHash) (cltv : Height)
    (h : HTLC) (ok : addHTLC maxHtlcValue currentTotal id dir amount ph cltv = .ok h) :
    h.amountMsat.val ≤ maxHtlcValue.val := by
  have hg := add_guard maxHtlcValue currentTotal id dir amount ph cltv h ok
  have ha := add_amountMsat_eq maxHtlcValue currentTotal id dir amount ph cltv h ok
  rw [ha]
  omega

/-- Amount-band law.  The lower bound is an explicit hypothesis because the
model's `addHTLC` has no `htlc_minimum_msat` parameter; see the counterexample
`addHTLC_ignores_htlc_minimum`. -/
theorem add_amount_within_bounds (minMsat maxHtlcValue currentTotal : Msat)
    (id : Nat) (dir : Direction) (amount : Msat) (ph : PaymentHash)
    (cltv : Height) (h : HTLC)
    (hmin : minMsat.val ≤ amount.val)
    (ok : addHTLC maxHtlcValue currentTotal id dir amount ph cltv = .ok h) :
    amountWithinBounds minMsat maxHtlcValue h := by
  have hg := add_guard maxHtlcValue currentTotal id dir amount ph cltv h ok
  have ha := add_amountMsat_eq maxHtlcValue currentTotal id dir amount ph cltv h ok
  exact ⟨by rw [ha]; exact hmin, by rw [ha]; omega⟩

/-- Checked structural counterexample: `addHTLC` accepts a 1 msat HTLC even
though a channel with `htlc_minimum_msat = 10` would reject it.  This records
the lower-bound gap in the model rather than asserting a false bound. -/
theorem addHTLC_ignores_htlc_minimum :
    (addHTLC ⟨100⟩ ⟨0⟩ 7 .local ⟨1⟩ ⟨ByteArray.empty⟩ 0).isOk = true := rfl

/-! ## CLTV bounds -/

/-- An accepted HTLC's expiry is below the BOLT 2 maximum 500000000. -/
theorem add_cltv_lt_model_max (maxHtlcValue currentTotal : Msat) (id : Nat)
    (dir : Direction) (amount : Msat) (ph : PaymentHash) (cltv : Height)
    (h : HTLC) (ok : addHTLC maxHtlcValue currentTotal id dir amount ph cltv = .ok h) :
    h.cltvExpiry < MAX_CLTV_EXPIRY := by
  have hg := add_guard maxHtlcValue currentTotal id dir amount ph cltv h ok
  have hc := add_cltvExpiry_eq maxHtlcValue currentTotal id dir amount ph cltv h ok
  rw [hc]
  exact hg.2.2

/-- An offered HTLC whose expiry is strictly in the future cannot be timed
out at the current height.  The "strictly in the future" premise is supplied
by the caller: `addHTLC` does not take the current height. -/
theorem offered_future_expiry_not_timed_out (height : Height) (h : HTLC)
    (hfut : height < h.cltvExpiry) :
    timeoutHTLC height h = .error ⟨.expiryTooSoon, ByteArray.empty⟩ :=
  timeout_before_expiry height h hfut

/-! ## Dust -/

/-- A dust HTLC has no commitment output (BOLT 3 trimming). -/
theorem dust_output_absent (h : HTLC) (dustLimit t s : Nat)
    (hd : isDust h dustLimit t s = true) : hasOutput h dustLimit t s = false := by
  simp [hasOutput, hd]

/-- A dust HTLC has no output but is still in the live HTLC set (provided it
is live): trimming removes the on-chain output, not the protocol-level HTLC. -/
theorem dust_no_output_but_in_set (h : HTLC) (hs : List HTLC)
    (dustLimit t s : Nat)
    (hd : isDust h dustLimit t s = true) (hm : h ∈ hs) (hl : h.isLive = true) :
    h ∈ htlcSet hs ∧ hasOutput h dustLimit t s = false := by
  refine ⟨?_, dust_output_absent h dustLimit t s hd⟩
  unfold htlcSet
  exact List.mem_filter.mpr ⟨hm, hl⟩

/-! ## In-flight value and open list laws -/

/-- The total in-flight value after adding an HTLC. -/
theorem totalHtlcValue_addToSet (h : HTLC) (hs : List HTLC) :
    totalHtlcValue (addToSet h hs) = h.amountMsat.val + totalHtlcValue hs := by
  simp [addToSet, totalHtlcValue]

/-- Removing an id and filtering to live HTLCs commute: removal preserves the
live set, and a settled HTLC is never live. -/
theorem htlcSet_removeFromSet_comm (id : Nat) (hs : List HTLC) :
    htlcSet (removeFromSet id hs) = removeFromSet id (htlcSet hs) := by
  -- OBLIGATION: LN-HTLC-010 Removing an HTLC id commutes with filtering to the live HTLC set.
  sorry

/-- A pointwise amount bound yields a bound on the total in-flight value. -/
theorem totalHtlcValue_le_length_mul (hs : List HTLC) (m : Nat)
    (hbound : ∀ h ∈ hs, h.amountMsat.val ≤ m) :
    totalHtlcValue hs ≤ hs.length * m := by
  -- OBLIGATION: LN-HTLC-011 The in-flight value of a finite HTLC set is at most its size times any pointwise amount bound.
  sorry

end LnLean.Proofs.Channel.HTLCProps
