import LnLean.Basic.Core
import LnLean.Bitcoin.Seam

/-!
# LnLean.Channel.HTLC

English claim.  This module models a single HTLCRecord inside a channel and the
state transitions that the BOLT 2 update messages induce: an HTLCRecord is added
in the `offered` or `received` state, is settled either by a fulfillment
(a 32-byte preimage whose SHA-256 equals the payment hash) or by a failure
(including an on-chain timeout), and is finally removed.  The on-chain value
of an HTLCRecord output is the millisatoshi amount rounded down to satoshis minus
the BOLT 3 second-stage fee; amounts below the dust limit produce no output
at all.

BOLT anchors.
* BOLT 2 (adding an HTLCRecord, `update_add_htlc`): `refs/bolts/02-peer-protocol.md:2772`
  (amount in msat, `payment_hash`, `cltv_expiry`, `id`; amount must be
  positive, `cltv_expiry < 500000000`, total in flight bounded by
  `max_htlc_value_in_flight_msat`).
* BOLT 2 (removing an HTLCRecord, `update_fulfill_htlc` / `update_fail_htlc`):
  `refs/bolts/02-peer-protocol.md:2913` (32-byte `payment_preimage`; the
  preimage must hash to the HTLCRecord payment hash).
* BOLT 3 (offered/received HTLCRecord outputs and trimming):
  `refs/bolts/03-transactions.md:199`, `:251`, `:305`.
* BOLT 5 (revoked-close handling of HTLCRecord outputs):
  `refs/bolts/05-onchain.md:510`.

rust-lightning anchors (commit fe49009).
* `lightning/src/ln/chan_utils.rs:716` (`HTLCOutputInCommitment`:
  `offered`, `amount_msat`, `cltv_expiry`, `payment_hash`,
  `transaction_output_index`).
* `lightning/src/ln/chan_utils.rs:735` (`to_bitcoin_amount`, amount / 1000).
* `lightning/src/ln/chan_utils.rs:875` (`build_htlc_transaction`; locktime is
  `cltv_expiry` for an offered HTLCRecord).
* `lightning/src/ln/channel.rs:9444` (a peer-supplied
  `per_commitment_secret` is length-checked on the wire; the analogous
  preimage length is fixed by the BOLT 2 message format).

Not modelled.
* No wire encoding/decoding (BigSize/TLV framing is another module).
* No onion payload, no MPP semantics, no per-commitment orientation flip:
  `Direction.local` is "offered by us" and `Direction.remote` is "received
  by us" throughout.
* SHA-256 is an uninterpreted function supplied by the caller.  Preimage
  soundness is therefore *conditional* on `hashFn p.bytes = paymentHash`
  and is never asserted.
* No fee estimation: the two second-stage fees are parameters.
-/

namespace LnLean.Channel

open LnLean

set_option autoImplicit false

/-! ## Protocol constants -/

/-- BOLT 2: a sending node MUST set `cltv_expiry` less than 500000000.
`refs/bolts/02-peer-protocol.md:2824`. -/
def MAX_CLTV_EXPIRY : Height := 500000000

/-- BOLT 3 default `dust_limit_satoshis` for a P2WPKH output (546 sat).
`refs/bolts/03-transactions.md:583`. -/
def DUST_LIMIT_P2WPKH : Nat := 546

/-- BOLT 2 caps `max_accepted_htlcs` at 483 so that one penalty transaction
can spend the whole commitment. `refs/bolts/02-peer-protocol.md:2889`. -/
def MAX_ACCEPTED_HTLCS : Nat := 483

/-! ## The HTLCRecord record -/

/-- One HTLCRecord inside a channel, from the local endpoint's point of view.
Anchored at `HTLCOutputInCommitment`
(`lightning/src/ln/chan_utils.rs:716`) plus the BOLT 2 `id` and state. -/
structure HTLCRecord where
  /-- BOLT 2 `update_add_htlc.id`; a 64-bit counter in the protocol. -/
  id : Nat
  /-- `local` = offered by us, `remote` = received by us. -/
  direction : Direction
  /-- The millisatoshi amount (`amount_msat` on the wire). -/
  amountMsat : Msat
  /-- `sha256(preimage)` of the payment (`payment_hash`). -/
  paymentHash : PaymentHash
  /-- Absolute block height at which the HTLCRecord expires (`cltv_expiry`). -/
  cltvExpiry : Height
  /-- Lifecycle state. -/
  state : HTLCState
deriving Repr, DecidableEq, BEq

end LnLean.Channel

namespace LnLean
namespace HTLCState

/-- The two pre-settlement states.  Only these can be fulfilled, failed, or
timed out. -/
def isLive : HTLCState → Bool
  | .offered => true
  | .received => true
  | .fulfilled => false
  | .failed => false
  | .removed => false

/-- A rank that strictly increases along the expected lifecycle
`offered/received -> fulfilled/failed -> removed`.  It is the acyclicity
measure used in `LnLean.Channel.HTLCLaws`. -/
def rank : HTLCState → Nat
  | .offered => 0
  | .received => 0
  | .fulfilled => 1
  | .failed => 1
  | .removed => 2

@[simp] theorem isLive_offered : isLive .offered = true := rfl
@[simp] theorem isLive_received : isLive .received = true := rfl
@[simp] theorem isLive_fulfilled : isLive .fulfilled = false := rfl
@[simp] theorem isLive_failed : isLive .failed = false := rfl
@[simp] theorem isLive_removed : isLive .removed = false := rfl

theorem isLive_iff (s : HTLCState) : isLive s = true ↔ s = .offered ∨ s = .received := by
  cases s <;> simp

/-- Terminal states are exactly the non-live ones. -/
theorem not_isLive_iff (s : HTLCState) :
    isLive s = false ↔ s = .fulfilled ∨ s = .failed ∨ s = .removed := by
  cases s <;> simp

end HTLCState
end LnLean

namespace LnLean.Channel

/-- An HTLCRecord is live while it is still in either pre-settlement state. -/
def HTLCRecord.isLive (h : HTLCRecord) : Bool := h.state.isLive

/-- The HTLCs of a commitment that still have (or may still create) an
output: the unresolved set.  This is the list-level counterpart of
`HTLCOutputInCommitment` entries with `transaction_output_index.is_some`. -/
def htlcSet (hs : List HTLCRecord) : List HTLCRecord := hs.filter HTLCRecord.isLive

/-- Total value in flight, in millisatoshis. -/
def totalHtlcValue (hs : List HTLCRecord) : Nat := (hs.map (fun h => h.amountMsat.val)).sum

/-! ## On-chain output value and dust -/

/-- BOLT 3 charges the HTLCRecord-timeout fee to an offered HTLCRecord and the
HTLCRecord-success fee to a received HTLCRecord (`03-transactions.md:319`).  From our
point of view an offered HTLCRecord is `Direction.local`. -/
def secondStageFee (dir : Direction) (timeoutFeeSat successFeeSat : Nat) : Nat :=
  match dir with
  | .local => timeoutFeeSat
  | .remote => successFeeSat

/-- The value of the commitment output for `h`, in satoshis:
`floor(amount_msat / 1000) - second_stage_fee`, with saturating Nat
subtraction.  Anchor: `lightning/src/ln/chan_utils.rs:744`
(`Amount::from_sat(self.amount_msat / 1000)`) and `:922` (`build_htlc_output`
subtracts the second-stage fee). -/
def htlcOutputValue (h : HTLCRecord) (timeoutFeeSat successFeeSat : Nat) : Nat :=
  Msat.toSatFloor h.amountMsat - secondStageFee h.direction timeoutFeeSat successFeeSat

/-- BOLT 3 trimming rule: the HTLCRecord output is absent iff amount minus the
second-stage fee is *less than* `dust_limit_satoshis`
(`refs/bolts/03-transactions.md:330`).  Equality is not dust. -/
def isDustHTLC (h : HTLCRecord) (dustLimitSat timeoutFeeSat successFeeSat : Nat) : Bool :=
  decide (htlcOutputValue h timeoutFeeSat successFeeSat < dustLimitSat)

/-- The output is present exactly when the HTLCRecord is not dust. -/
def hasOutput (h : HTLCRecord) (dustLimitSat timeoutFeeSat successFeeSat : Nat) : Bool :=
  !isDustHTLC h dustLimitSat timeoutFeeSat successFeeSat

theorem secondStageFee_local (timeout success : Nat) :
    secondStageFee .local timeout success = timeout := rfl

theorem secondStageFee_remote (timeout success : Nat) :
    secondStageFee .remote timeout success = success := rfl

/-- Rounding to satoshis and subtracting a fee never increases the value. -/
theorem htlcOutputValue_le (h : HTLCRecord) (t s : Nat) :
    htlcOutputValue h t s ≤ Msat.toSatFloor h.amountMsat :=
  Nat.sub_le _ _

theorem htlcOutputValue_le_msat (h : HTLCRecord) (t s : Nat) :
    htlcOutputValue h t s ≤ h.amountMsat.val :=
  Nat.le_trans (htlcOutputValue_le h t s) (Msat.toSatFloor_le h.amountMsat)

theorem isDust_iff (h : HTLCRecord) (d t s : Nat) :
    isDustHTLC h d t s = true ↔ htlcOutputValue h t s < d := by
  unfold isDustHTLC
  exact decide_eq_true_iff

theorem hasOutput_iff (h : HTLCRecord) (d t s : Nat) :
    hasOutput h d t s = true ↔ d ≤ htlcOutputValue h t s := by
  unfold hasOutput isDustHTLC
  rw [Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_lt]

/-! ## The offered / received / trimmed amount partition

`HTLCRecord` carries no balance, fee, or funding value, so the catalog claim
`LN-HT-003` cannot be stated here in its balance-and-fee form.  What the model
does determine is the HTLC half of that claim: the live HTLC value splits
exactly into the offered, received, and trimmed buckets.  A future channel
ledger (a `Balance` with a fee and a `fundingValue`, as in
`LnLean.Channel.Types`) can wrap that identity with the non-HTLC part; the
hypothesis of `htlcValue_conservation_of_ledger` is exactly that missing
ledger. -/

/-- The live HTLCs whose commitment output survives the dust test. -/
def htlcUntrimmed (dustLimit timeoutFee successFee : Nat)
    (hs : List HTLCRecord) : List HTLCRecord :=
  (htlcSet hs).filter (fun h => !isDustHTLC h dustLimit timeoutFee successFee)

/-- The untrimmed HTLCs offered by the local endpoint. -/
def htlcOffered (dustLimit timeoutFee successFee : Nat)
    (hs : List HTLCRecord) : List HTLCRecord :=
  (htlcUntrimmed dustLimit timeoutFee successFee hs).filter
    (fun h => decide (h.direction = Direction.local))

/-- The untrimmed HTLCs received by the local endpoint. -/
def htlcReceived (dustLimit timeoutFee successFee : Nat)
    (hs : List HTLCRecord) : List HTLCRecord :=
  (htlcUntrimmed dustLimit timeoutFee successFee hs).filter
    (fun h => decide (h.direction = Direction.remote))

/-- The live HTLCs whose output is trimmed.  BOLT 3 adds the value of a
trimmed output to the commitment fee (`refs/bolts/03-transactions.md:305`). -/
def htlcTrimmed (dustLimit timeoutFee successFee : Nat)
    (hs : List HTLCRecord) : List HTLCRecord :=
  (htlcSet hs).filter (fun h => isDustHTLC h dustLimit timeoutFee successFee)

/-- Filtering offered and received records covers the list, up to
permutation.  Every `Direction` is either `local` or `remote`. -/
theorem htlc_filter_direction_perm (l : List HTLCRecord) :
    List.Perm
      (l.filter (fun h => decide (h.direction = Direction.local)) ++
        l.filter (fun h => decide (h.direction = Direction.remote))) l := by
  have hcomp :
      (fun h : HTLCRecord => !decide (h.direction = Direction.local)) =
        (fun h => decide (h.direction = Direction.remote)) := by
    funext h
    cases h.direction <;> rfl
  simpa [hcomp] using
    List.filter_append_perm
      (fun h : HTLCRecord => decide (h.direction = Direction.local)) l

/-- **Offered / received / trimmed partition.**  For any HTLC list, the three
BOLT 3 buckets cover the live set exactly, up to permutation.  The statement is
about `htlcSet hs`, so settled and removed records are excluded. -/
theorem htlcSet_partition_perm (dustLimit timeoutFee successFee : Nat)
    (hs : List HTLCRecord) :
    List.Perm
      (htlcOffered dustLimit timeoutFee successFee hs ++
        htlcReceived dustLimit timeoutFee successFee hs ++
        htlcTrimmed dustLimit timeoutFee successFee hs) (htlcSet hs) := by
  have hdir :
      List.Perm
        (htlcOffered dustLimit timeoutFee successFee hs ++
          htlcReceived dustLimit timeoutFee successFee hs)
        (htlcUntrimmed dustLimit timeoutFee successFee hs) := by
    unfold htlcOffered htlcReceived
    exact htlc_filter_direction_perm _
  have hdust :
      List.Perm
        (htlcUntrimmed dustLimit timeoutFee successFee hs ++
          htlcTrimmed dustLimit timeoutFee successFee hs) (htlcSet hs) := by
    unfold htlcUntrimmed htlcTrimmed
    simpa using List.filter_append_perm
      (fun h : HTLCRecord => !isDustHTLC h dustLimit timeoutFee successFee)
      (htlcSet hs)
  exact (hdir.append_right _).trans hdust

/-- The live HTLC value splits exactly into the offered, received, and trimmed
amounts.  `List.sum` is permutation-invariant, so the permutation form of
`htlcSet_partition_perm` is enough. -/
theorem totalHtlcValue_partition (dustLimit timeoutFee successFee : Nat)
    (hs : List HTLCRecord) :
    totalHtlcValue (htlcSet hs) =
      totalHtlcValue (htlcOffered dustLimit timeoutFee successFee hs) +
        totalHtlcValue (htlcReceived dustLimit timeoutFee successFee hs) +
        totalHtlcValue (htlcTrimmed dustLimit timeoutFee successFee hs) := by
  have hp := htlcSet_partition_perm dustLimit timeoutFee successFee hs
  have hsum := (hp.map (fun h : HTLCRecord => h.amountMsat.val)).sum_nat
  rw [List.map_append, List.map_append, List.sum_append, List.sum_append] at hsum
  unfold totalHtlcValue
  exact hsum.symm

/-- **Arithmetic content of `LN-HT-003`, with the missing ledger explicit.**
`ledger` is the catalog's "balances and fee" total.  This module has no
`Balance`, `fee`, or `fundingValue` field, so `hledger` is an explicit
channel-ledger invariant rather than a theorem about the model.  Under it the
offered, received, and trimmed amounts plus the ledger equal the funding value.
The claim is false without `hledger` (see the counterexample in
`LnLean.Proofs.WaveD.D15`); the satoshi and commitment-fee form lives there
too. -/
theorem htlcValue_conservation_of_ledger
    (dustLimit timeoutFee successFee ledger funding : Nat)
    (hs : List HTLCRecord)
    (hledger : ledger + totalHtlcValue (htlcSet hs) = funding) :
    ledger + totalHtlcValue (htlcOffered dustLimit timeoutFee successFee hs) +
        totalHtlcValue (htlcReceived dustLimit timeoutFee successFee hs) +
        totalHtlcValue (htlcTrimmed dustLimit timeoutFee successFee hs) =
      funding := by
  have hpart := totalHtlcValue_partition dustLimit timeoutFee successFee hs
  omega

/-- For one HTLC whose second-stage fee is covered, the commitment output value
plus the withheld second-stage fee is exactly the floored amount.  This is the
per-output BOLT 3 rule that a fee-aware conservation target wraps with the
balance/funding ledger. -/
theorem htlcOutputValue_add_secondStageFee (h : HTLCRecord)
    (timeoutFee successFee : Nat)
    (hfee : secondStageFee h.direction timeoutFee successFee ≤
      Msat.toSatFloor h.amountMsat) :
    htlcOutputValue h timeoutFee successFee +
        secondStageFee h.direction timeoutFee successFee =
      Msat.toSatFloor h.amountMsat := by
  unfold htlcOutputValue
  exact Nat.sub_add_cancel hfee

/-- A non-dust HTLC can pay its second-stage fee.  A positive dust limit is
needed: the output value is the floored amount minus the fee, and the output is
untrimmed only when that value reaches the dust limit. -/
theorem secondStageFee_le_of_not_dust (dustLimit timeoutFee successFee : Nat)
    (hdust : 0 < dustLimit) {h : HTLCRecord}
    (hnd : isDustHTLC h dustLimit timeoutFee successFee = false) :
    secondStageFee h.direction timeoutFee successFee ≤
      Msat.toSatFloor h.amountMsat := by
  have hhas : hasOutput h dustLimit timeoutFee successFee = true := by
    unfold hasOutput
    simp [hnd]
  have hge := (hasOutput_iff h dustLimit timeoutFee successFee).1 hhas
  unfold htlcOutputValue at hge
  omega

/-! ## Transitions -/

/-- BOLT 2 `update_add_htlc`.  The guard is the conjunction of the sending
node's MUSTs: a positive amount, total value in flight not exceeding the
counterparty's `max_htlc_value_in_flight_msat`, and
`cltv_expiry < 500000000`.
Anchors: `refs/bolts/02-peer-protocol.md:2822-2831`. -/
def addHTLC (maxHtlcValue currentTotal : Msat) (id : Nat) (dir : Direction)
    (amount : Msat) (ph : PaymentHash) (cltv : Height) : Result HTLCRecord :=
  if 0 < amount.val ∧ currentTotal.val + amount.val ≤ maxHtlcValue.val ∧
      cltv < MAX_CLTV_EXPIRY then
    .ok
      { id := id
        direction := dir
        amountMsat := amount
        paymentHash := ph
        cltvExpiry := cltv
        state := match dir with
          | .local => .offered
          | .remote => .received }
  else
    .error ⟨.update, ByteArray.empty⟩

/-- `update_fulfill_htlc`: a live HTLCRecord may be settled by a preimage that is
32 bytes long and hashes to the payment hash.  Both conditions are part of
the model's transition guard; the hash condition is the *conditional*
cryptographic part.  Anchors: `refs/bolts/02-peer-protocol.md:2920` and
`:3004`. -/
def fulfillHTLC (hashFn : ByteArray → ByteArray) (h : HTLCRecord) (p : Preimage) :
    Result HTLCRecord :=
  if h.isLive then
    if decide (p.bytes.size = 32 ∧ hashFn p.bytes = h.paymentHash.bytes) then
      .ok { h with state := .fulfilled }
    else
      .error ⟨.invalidOnion, ByteArray.empty⟩
  else
    .error ⟨.update, ByteArray.empty⟩

/-- `update_fail_htlc`: a live HTLCRecord may be failed (route failure, malformed
onion, or a local policy failure).  `refs/bolts/02-peer-protocol.md:2944`. -/
def failHTLC (h : HTLCRecord) : Result HTLCRecord :=
  if h.isLive then
    .ok { h with state := .failed }
  else
    .error ⟨.update, ByteArray.empty⟩

/-- On-chain timeout of an offered HTLCRecord.  BOLT 2: an HTLCRecord SHOULD be failed
once it has timed out; the HTLCRecord-timeout transaction can only be built after
`cltv_expiry`, and only for an offered HTLCRecord whose locktime is the expiry.
Anchors: `refs/bolts/02-peer-protocol.md:2974`,
`refs/bolts/03-transactions.md:355`,
`lightning/src/ln/chan_utils.rs:889` (`lock_time` =
`htlc.cltv_expiry` iff `htlc.offered`). -/
def timeoutHTLC (height : Height) (h : HTLCRecord) : Result HTLCRecord :=
  if h.isLive ∧ h.direction = .local ∧ h.cltvExpiry ≤ height then
    .ok { h with state := .failed }
  else
    .error ⟨.expiryTooSoon, ByteArray.empty⟩

/-- Remove a settled HTLCRecord from the commitment set.  Only a settled
(`fulfilled` or `failed`) HTLCRecord can be removed; `removed` is idempotent-free:
a second removal is rejected. -/
def removeHTLC (h : HTLCRecord) : Result HTLCRecord :=
  if h.state = .fulfilled ∨ h.state = .failed then
    .ok { h with state := .removed }
  else
    .error ⟨.update, ByteArray.empty⟩

/-! ## Basic facts about transitions (the lifecycle laws live in
`LnLean.Channel.HTLCLaws`). -/

theorem addHTLC_state_local (max cur : Msat) (id : Nat) (amt : Msat)
    (ph : PaymentHash) (cltv : Height) (h : HTLCRecord)
    (ok : addHTLC max cur id .local amt ph cltv = .ok h) :
    h.state = .offered := by
  unfold addHTLC at ok
  split at ok
  · simp only [Result.ok.injEq] at ok
    subst ok
    rfl
  · simp at ok

theorem addHTLC_state_remote (max cur : Msat) (id : Nat) (amt : Msat)
    (ph : PaymentHash) (cltv : Height) (h : HTLCRecord)
    (ok : addHTLC max cur id .remote amt ph cltv = .ok h) :
    h.state = .received := by
  unfold addHTLC at ok
  split at ok
  · simp only [Result.ok.injEq] at ok
    subst ok
    rfl
  · simp at ok

theorem fulfillHTLC_hash (hashFn : ByteArray → ByteArray) (h h' : HTLCRecord)
    (p : Preimage) (ok : fulfillHTLC hashFn h p = .ok h') :
    p.Valid ∧ hashFn p.bytes = h.paymentHash.bytes := by
  unfold fulfillHTLC at ok
  split at ok
  · split at ok
    · rename_i hg
      have hg' : p.bytes.size = 32 ∧
          hashFn p.bytes = h.paymentHash.bytes := of_decide_eq_true hg
      exact ⟨hg'.1, hg'.2⟩
    · simp at ok
  · simp at ok

theorem fulfillHTLC_state (hashFn : ByteArray → ByteArray) (h h' : HTLCRecord)
    (p : Preimage) (ok : fulfillHTLC hashFn h p = .ok h') :
    h' = { h with state := .fulfilled } := by
  unfold fulfillHTLC at ok
  split at ok
  · split at ok
    · simp only [Result.ok.injEq] at ok
      exact ok.symm
    · simp at ok
  · simp at ok

theorem timeoutHTLC_expiry (height : Height) (h h' : HTLCRecord)
    (ok : timeoutHTLC height h = .ok h') : h.cltvExpiry ≤ height := by
  unfold timeoutHTLC at ok
  split at ok
  · rename_i hg
    exact hg.2.2
  · simp at ok

theorem timeoutHTLC_direction (height : Height) (h h' : HTLCRecord)
    (ok : timeoutHTLC height h = .ok h') : h.direction = .local := by
  unfold timeoutHTLC at ok
  split at ok
  · rename_i hg
    exact hg.2.1
  · simp at ok

theorem removeHTLC_ok_state (h h' : HTLCRecord) (ok : removeHTLC h = .ok h') :
    h' = { h with state := .removed } := by
  unfold removeHTLC at ok
  split at ok
  · simp only [Result.ok.injEq] at ok
    exact ok.symm
  · simp at ok

/-! ## Live-set id uniqueness

`HTLCRecord.id` is the BOLT 2 `update_add_htlc.id`.  The model's `addHTLC`
takes the id from the caller and never sees the current list, so no theorem
about `addHTLC` alone can establish uniqueness; the catalog claim `LN-HT-004`
is a list invariant.  The strongest facts available in this module are:

* `liveHtlcIdsNodup_add` — consing a record with a fresh live id preserves
  pairwise distinctness of the live ids (freshness is needed only when the
  added record is itself live);
* `liveHtlcIdsNodup_addHTLC` — the same for the record produced by a
  successful model `addHTLC`, whose id is the caller's id;
* `liveHtlcIdsNodup_filter` — any record filter preserves live-id
  distinctness, which covers dropping settled records and removal by id;
* `liveHtlcIdsNodup_unique` — pairwise distinctness gives the relational
  uniqueness property the catalog states.

The unconditional claim is false in this model: `liveHtlcIdsNodup_unconditional_false`
exhibits a live list with two distinct records carrying the same id.  That is
protocol-conforming because BOLT 2 allocates ids from one counter per sender,
and `HTLCRecord` has neither a counter nor a distinctness field.  The
channel-level allocator `HtlcBook` below supplies those counters and proves
per-sender uniqueness from construction (`HtlcBook.reachable_liveOf_id_unique`);
the global form additionally needs `HtlcBook.CrossDisjoint`, which the
per-sender counters do not imply (`HtlcBook.reachable_cross_direction_duplicate`).
-/

/-- The BOLT 2 ids of a list of HTLC records, in list order. -/
def htlcIds (hs : List HTLCRecord) : List Nat := hs.map HTLCRecord.id

/-- The ids of the live HTLC set, in list order. -/
def liveHtlcIds (hs : List HTLCRecord) : List Nat :=
  (htlcSet hs).map HTLCRecord.id

/-- The live HTLC ids are pairwise distinct. -/
def liveHtlcIdsNodup (hs : List HTLCRecord) : Prop := (liveHtlcIds hs).Nodup

theorem mem_htlcIds_iff (x : Nat) (hs : List HTLCRecord) :
    x ∈ htlcIds hs ↔ ∃ h ∈ hs, h.id = x := by
  unfold htlcIds
  exact List.mem_map

theorem mem_liveHtlcIds_iff (x : Nat) (hs : List HTLCRecord) :
    x ∈ liveHtlcIds hs ↔ ∃ h ∈ htlcSet hs, h.id = x := by
  unfold liveHtlcIds
  exact List.mem_map

/-- Every live id is an id of the full record list. -/
theorem liveHtlcIds_subset_htlcIds (hs : List HTLCRecord) :
    ∀ x ∈ liveHtlcIds hs, x ∈ htlcIds hs := by
  intro x hx
  unfold liveHtlcIds at hx
  obtain ⟨h, hh, hid⟩ := List.mem_map.1 hx
  unfold htlcIds
  exact List.mem_map.2 ⟨h, (List.mem_filter.mp hh).1, hid⟩

/-- Distinct ids on the full list imply distinct ids on the live set. -/
theorem liveHtlcIdsNodup_of_htlcIds_nodup (hs : List HTLCRecord)
    (hnd : (htlcIds hs).Nodup) : liveHtlcIdsNodup hs := by
  unfold liveHtlcIdsNodup liveHtlcIds htlcIds htlcSet at *
  exact (List.filter_sublist.map HTLCRecord.id).nodup hnd

theorem htlcSet_cons_live (h : HTLCRecord) (hs : List HTLCRecord)
    (hl : h.isLive = true) : htlcSet (h :: hs) = h :: htlcSet hs := by
  unfold htlcSet
  simp [hl]

theorem htlcSet_cons_not_live (h : HTLCRecord) (hs : List HTLCRecord)
    (hl : h.isLive = false) : htlcSet (h :: hs) = htlcSet hs := by
  unfold htlcSet
  simp [hl]

theorem liveHtlcIds_cons_live (h : HTLCRecord) (hs : List HTLCRecord)
    (hl : h.isLive = true) :
    liveHtlcIds (h :: hs) = h.id :: liveHtlcIds hs := by
  unfold liveHtlcIds
  rw [htlcSet_cons_live h hs hl, List.map_cons]

theorem liveHtlcIds_cons_not_live (h : HTLCRecord) (hs : List HTLCRecord)
    (hl : h.isLive = false) : liveHtlcIds (h :: hs) = liveHtlcIds hs := by
  unfold liveHtlcIds
  rw [htlcSet_cons_not_live h hs hl]

/-- Consing one record preserves pairwise distinctness of the live ids when
its id is fresh for the live set.  Freshness is required only when the added
record is live, which is the strongest insert law available for the unchecked
transition. -/
theorem liveHtlcIdsNodup_add (h : HTLCRecord) (hs : List HTLCRecord)
    (hnd : liveHtlcIdsNodup hs) (hfresh : h.id ∉ liveHtlcIds hs) :
    liveHtlcIdsNodup (h :: hs) := by
  unfold liveHtlcIdsNodup at hnd ⊢
  by_cases hl : h.isLive = true
  · rw [liveHtlcIds_cons_live h hs hl]
    exact List.nodup_cons.2 ⟨hfresh, hnd⟩
  · have hf : h.isLive = false := by
      cases hb : h.isLive <;> simp_all
    rw [liveHtlcIds_cons_not_live h hs hf]
    exact hnd

/-- Any record filter preserves pairwise distinctness of the live ids.
Instances include dropping settled records and removing every record with a
given id. -/
theorem liveHtlcIdsNodup_filter (p : HTLCRecord → Bool)
    (hs : List HTLCRecord) (hnd : liveHtlcIdsNodup hs) :
    liveHtlcIdsNodup (hs.filter p) := by
  unfold liveHtlcIdsNodup liveHtlcIds htlcSet at hnd ⊢
  rw [List.filter_filter]
  have hcomm : (fun a : HTLCRecord => HTLCRecord.isLive a && p a) =
      (fun a => p a && HTLCRecord.isLive a) := by
    funext a
    exact Bool.and_comm _ _
  rw [hcomm, ← List.filter_filter (p := p) (q := HTLCRecord.isLive)]
  exact (List.filter_sublist.map HTLCRecord.id).nodup hnd

/-- Removing every record with a given id preserves live-id distinctness. -/
theorem liveHtlcIdsNodup_removeId (id : Nat) (hs : List HTLCRecord)
    (hnd : liveHtlcIdsNodup hs) :
    liveHtlcIdsNodup (hs.filter (fun h => decide (h.id ≠ id))) :=
  liveHtlcIdsNodup_filter (fun h => decide (h.id ≠ id)) hs hnd

/-- If the ids of a record list are distinct, membership plus equality of ids
determines the record.  This is the combinatorial core of id uniqueness. -/
theorem eq_of_id_eq_of_htlcIds_nodup {l : List HTLCRecord}
    (hnd : (l.map HTLCRecord.id).Nodup) :
    ∀ h1 ∈ l, ∀ h2 ∈ l, h1.id = h2.id → h1 = h2 := by
  induction l with
  | nil =>
      intro h1 hm1
      simp at hm1
  | cons x xs ih =>
      have hnd' : (x.id :: xs.map HTLCRecord.id).Nodup := by
        simpa using hnd
      have hx : x.id ∉ xs.map HTLCRecord.id := (List.nodup_cons.mp hnd').1
      have htail : (xs.map HTLCRecord.id).Nodup :=
        (List.nodup_cons.mp hnd').2
      intro h1 hm1 h2 hm2 hid
      simp only [List.mem_cons] at hm1 hm2
      rcases hm1 with rfl | hm1
      · rcases hm2 with rfl | hm2
        · rfl
        · exact absurd (List.mem_map.mpr ⟨h2, hm2, hid.symm⟩) hx
      · rcases hm2 with rfl | hm2
        · exact absurd (List.mem_map.mpr ⟨h1, hm1, hid⟩) hx
        · exact ih htail h1 hm1 h2 hm2 hid

/-- Pairwise distinctness of the live ids gives the relational uniqueness
property: within the live set an id determines the record.  The converse is
not claimed, because a list may contain the same record twice. -/
theorem liveHtlcIdsNodup_unique (hs : List HTLCRecord)
    (hnd : liveHtlcIdsNodup hs) :
    ∀ h1 ∈ htlcSet hs, ∀ h2 ∈ htlcSet hs, h1.id = h2.id → h1 = h2 := by
  unfold liveHtlcIdsNodup liveHtlcIds at hnd
  exact eq_of_id_eq_of_htlcIds_nodup hnd

/-- The model's `addHTLC` returns the caller-supplied id, so the freshness
guard needed for uniqueness has to be discharged by the caller: `addHTLC` does
not inspect the current record list. -/
theorem addHTLC_id (maxHtlcValue currentTotal : Msat) (id : Nat)
    (dir : Direction) (amount : Msat) (ph : PaymentHash) (cltv : Height)
    (h : HTLCRecord)
    (ok : addHTLC maxHtlcValue currentTotal id dir amount ph cltv = .ok h) :
    h.id = id := by
  unfold addHTLC at ok
  split at ok
  · simp only [Result.ok.injEq] at ok
    subst ok
    rfl
  · simp at ok

/-- The record produced by a successful `addHTLC` is live. -/
theorem addHTLC_isLive (maxHtlcValue currentTotal : Msat) (id : Nat)
    (dir : Direction) (amount : Msat) (ph : PaymentHash) (cltv : Height)
    (h : HTLCRecord)
    (ok : addHTLC maxHtlcValue currentTotal id dir amount ph cltv = .ok h) :
    h.isLive = true := by
  cases dir
  · have hs := addHTLC_state_local maxHtlcValue currentTotal id amount ph cltv h ok
    simp [HTLCRecord.isLive, hs, HTLCState.isLive]
  · have hs := addHTLC_state_remote maxHtlcValue currentTotal id amount ph cltv h ok
    simp [HTLCRecord.isLive, hs, HTLCState.isLive]

/-- Inserting the record produced by a successful model add preserves live-id
distinctness when the caller's id is fresh.  The freshness premise cannot be
dropped: `addHTLC` accepts a reused id (two adds with the same id both succeed
in the model). -/
theorem liveHtlcIdsNodup_addHTLC
    (maxHtlcValue currentTotal : Msat) (id : Nat) (dir : Direction)
    (amount : Msat) (ph : PaymentHash) (cltv : Height)
    (h : HTLCRecord) (hs : List HTLCRecord)
    (ok : addHTLC maxHtlcValue currentTotal id dir amount ph cltv = .ok h)
    (hnd : liveHtlcIdsNodup hs) (hfresh : id ∉ liveHtlcIds hs) :
    liveHtlcIdsNodup (h :: hs) := by
  have hid : h.id = id :=
    addHTLC_id maxHtlcValue currentTotal id dir amount ph cltv h ok
  exact liveHtlcIdsNodup_add h hs hnd (by simpa [hid] using hfresh)

/-- `addHTLC` performs no id check: two adds carrying the same id but
different amounts both succeed.  Freshness therefore has to come from the
caller or from a channel record that owns the id counters. -/
theorem addHTLC_same_id_distinct_amounts_ok :
    (addHTLC ⟨1000⟩ ⟨0⟩ 7 .local ⟨1⟩ ⟨ByteArray.empty⟩ 0).isOk = true ∧
      (addHTLC ⟨1000⟩ ⟨0⟩ 7 .local ⟨2⟩ ⟨ByteArray.empty⟩ 0).isOk = true :=
  ⟨rfl, rfl⟩

/-- **The unconditional catalog claim is false in this model.**  Two distinct
live records may carry the same id: BOLT 2 allocates from one counter per
sender, and `HTLCRecord` has no counter and no distinctness field. -/
theorem liveHtlcIdsNodup_unconditional_false :
    ¬ (∀ hs : List HTLCRecord, liveHtlcIdsNodup hs) := by
  intro hall
  let a : HTLCRecord :=
    { id := 0
      direction := Direction.local
      amountMsat := ⟨1000⟩
      paymentHash := ⟨ByteArray.empty⟩
      cltvExpiry := 0
      state := .offered }
  let b : HTLCRecord :=
    { id := 0
      direction := Direction.remote
      amountMsat := ⟨2000⟩
      paymentHash := ⟨ByteArray.empty⟩
      cltvExpiry := 0
      state := .received }
  have h := hall [a, b]
  have hids : liveHtlcIds [a, b] = [0, 0] := by
    decide
  unfold liveHtlcIdsNodup at h
  rw [hids] at h
  simp at h

/-! ## Catalog-named targets for `LN-HT-003` and `LN-HT-004`

The catalog writes the module name `HTLC` as if it were a namespace, so the
exact targets are `LnLean.Channel.HTLC.amount_conservation` and
`LnLean.Channel.HTLC.id_unique`.  The nested namespace below supplies those
names without changing any earlier declaration.

Both theorems restate H01's results with the same explicit hypotheses; neither
premise is discharged by the bare record list.  In particular:

* `amount_conservation` still takes the channel-ledger invariant as a
  hypothesis because `HTLCRecord` has no balance, fee, or funding field;
* `id_unique` still takes live-id distinctness as a hypothesis because the
  unconditional global claim is false (`liveHtlcIdsNodup_unconditional_false`).
  The allocator API added below discharges the per-sender form from
  construction (`dir_id_unique`); the global form needs `CrossDisjoint`. -/

namespace HTLC

/-- Catalog target `LN-HT-003`: offered, received, and trimmed HTLC amounts plus
the channel ledger equal the funding value.

This is exactly `htlcValue_conservation_of_ledger`.  `ledger` stands for the
catalog's balances plus fee, and `hledger` is an explicit channel-ledger
invariant, not a consequence of this module: `HTLCRecord` carries no balance,
fee, or funding value.  The identity is false without `hledger` (the checked
counterexample is `waveD_d15_without_balance_invariant_false` in
`LnLean.Proofs.WaveD.D15`). -/
theorem amount_conservation
    (dustLimit timeoutFee successFee ledger funding : Nat)
    (hs : List HTLCRecord)
    (hledger : ledger + totalHtlcValue (htlcSet hs) = funding) :
    ledger + totalHtlcValue (htlcOffered dustLimit timeoutFee successFee hs) +
        totalHtlcValue (htlcReceived dustLimit timeoutFee successFee hs) +
        totalHtlcValue (htlcTrimmed dustLimit timeoutFee successFee hs) =
      funding :=
  htlcValue_conservation_of_ledger dustLimit timeoutFee successFee ledger funding
    hs hledger

/-- Catalog target `LN-HT-004`: within the live HTLC set an id determines the
record.

This is exactly `liveHtlcIdsNodup_unique`.  The hypothesis `hnd` is the live-id
distinctness invariant; it is not automatic.  The model allows two distinct live
records with the same id (`liveHtlcIdsNodup_unconditional_false`), and
`addHTLC` performs no id check (`addHTLC_same_id_distinct_amounts_ok`), so the
unconditional catalog wording is not claimed here.

This declaration is retained unchanged for compatibility.  The construction-based
replacement is `HTLC.dir_id_unique` (per sender, unconditional over
`HtlcBook.Reachable`); the global conditional form is
`HTLC.id_unique_of_reachable_cross`. -/
theorem id_unique (hs : List HTLCRecord)
    (hnd : liveHtlcIdsNodup hs) :
    ∀ h1 ∈ htlcSet hs, ∀ h2 ∈ htlcSet hs, h1.id = h2.id → h1 = h2 :=
  liveHtlcIdsNodup_unique hs hnd

end HTLC

/-! ## A channel-level id allocator for `LN-HT-004`

`addHTLC` alone cannot enforce id uniqueness: it takes the id from the caller
and never sees the channel's record list.  BOLT 2 §Adding an HTLC supplies the
missing discipline — the first HTLC of a sender has id 0 and each successive
offer increments it by one (`refs/bolts/02-peer-protocol.md:2838-2843`) — and
rust-lightning implements it with the two counters `next_holder_htlc_id` and
`next_counterparty_htlc_id` (`lightning/src/ln/channel.rs:3719-3720`).

`HtlcBook` below adds exactly those two per-sender counters to the record list.
`allocate` takes the id from the sender's counter, `push` inserts a record and
advances that counter, and `add` runs the existing `addHTLC` guard with the
allocated id.  The invariant `HtlcBook.WF` is established for the empty book
(`empty_wf`) and preserved by insertion (`push_wf`, `insert_wf`, `add_wf`), so
it is a property of every reachable book, not an assumption about an arbitrary
list.

The counter bound in `WF` does real work: `nextId_not_mem_liveIdsOf` derives
from it that the next allocation cannot collide with a live id of the same
sender.  Per-sender uniqueness (`liveIdsOf_nodup`, `liveOf_id_unique`) follows
unconditionally.  Global uniqueness across directions does **not**: both
senders start at 0, so a local and a remote HTLC may carry the same id.
`cross_direction_duplicate` is the checked counterexample; the global form
needs the explicit `CrossDisjoint` premise (`liveIds_nodup_of_cross`,
`live_id_unique_of_cross`). -/

/-- A channel's HTLC record list together with the two BOLT 2 per-sender id
counters.  `records` may still contain settled records, exactly as in the
existing list model; only the live ones matter for id uniqueness. -/
structure HtlcBook where
  /-- All HTLC records of the channel. -/
  records : List HTLCRecord
  /-- BOLT 2 id counter for HTLCs we offer. -/
  nextLocalId : Nat
  /-- BOLT 2 id counter for HTLCs we receive. -/
  nextRemoteId : Nat
deriving Repr

namespace HtlcBook

/-- The empty book: no records, both counters at zero. -/
def empty : HtlcBook := ⟨[], 0, 0⟩

/-- The next id of one sender. -/
def nextId (b : HtlcBook) : Direction → Nat
  | .local => b.nextLocalId
  | .remote => b.nextRemoteId

/-- The live records of one sender, most recently added first. -/
def liveOf (b : HtlcBook) (dir : Direction) : List HTLCRecord :=
  (htlcSet b.records).filter (fun r => decide (r.direction = dir))

/-- The live ids of one sender, most recently added first. -/
def liveIdsOf (b : HtlcBook) (dir : Direction) : List Nat :=
  (b.liveOf dir).map HTLCRecord.id

/-- The live ids of the whole channel, the list `liveHtlcIds` of the existing
model. -/
def liveIds (b : HtlcBook) : List Nat :=
  (htlcSet b.records).map HTLCRecord.id

/-- Total value currently in flight; this is the `currentTotal` argument of
`addHTLC`. -/
def totalInFlight (b : HtlcBook) : Msat :=
  ⟨totalHtlcValue (htlcSet b.records)⟩

/-- Allocate the sender's next id and build the corresponding live record.
This is the BOLT 2 rule: the id is the counter, and the initial state is
`offered` for a local HTLC and `received` for a remote one. -/
def allocate (b : HtlcBook) (dir : Direction) (amount : Msat)
    (ph : PaymentHash) (cltv : Height) : HTLCRecord :=
  { id := b.nextId dir
    direction := dir
    amountMsat := amount
    paymentHash := ph
    cltvExpiry := cltv
    state := match dir with
      | .local => .offered
      | .remote => .received }

/-- Insert `r`, which must belong to `dir`, and advance that sender's counter.
The other sender's counter is untouched. -/
def push (b : HtlcBook) (dir : Direction) (r : HTLCRecord) : HtlcBook :=
  match dir with
  | .local =>
      { records := r :: b.records
        nextLocalId := b.nextLocalId + 1
        nextRemoteId := b.nextRemoteId }
  | .remote =>
      { records := r :: b.records
        nextLocalId := b.nextLocalId
        nextRemoteId := b.nextRemoteId + 1 }

/-- Allocate and insert in one step.  This is the id-allocation API: the id is
not caller-supplied, so a live id of the same sender can never be reused. -/
def insert (b : HtlcBook) (dir : Direction) (amount : Msat)
    (ph : PaymentHash) (cltv : Height) : HtlcBook :=
  b.push dir (b.allocate dir amount ph cltv)

/-- The guarded insertion through the existing model transition: `addHTLC` is
run with the counter-allocated id and the book's current in-flight total.
A rejected add leaves both the records and the counters unchanged. -/
def add (b : HtlcBook) (maxHtlcValue : Msat) (dir : Direction)
    (amount : Msat) (ph : PaymentHash) (cltv : Height) : Result HtlcBook :=
  match addHTLC maxHtlcValue b.totalInFlight (b.nextId dir) dir amount ph cltv with
  | .ok r => .ok (b.push dir r)
  | .error e => .error e

/-- The channel invariant: each sender's live ids lie strictly below that
sender's next counter, and are pairwise distinct within the sender.

The `bound_*` fields are what make the next allocation fresh; the `nodup_*`
fields are an inductive invariant that `empty_wf` establishes and
`push_wf`/`add_wf` preserve.  Neither field mentions uniqueness across senders,
which would be false (see `cross_direction_duplicate`). -/
structure WF (b : HtlcBook) : Prop where
  /-- Every live local id is below the local counter. -/
  bound_local : ∀ r ∈ htlcSet b.records, r.direction = .local →
    r.id < b.nextLocalId
  /-- Every live remote id is below the remote counter. -/
  bound_remote : ∀ r ∈ htlcSet b.records, r.direction = .remote →
    r.id < b.nextRemoteId
  /-- The live local ids are pairwise distinct. -/
  nodup_local : (b.liveIdsOf .local).Nodup
  /-- The live remote ids are pairwise distinct. -/
  nodup_remote : (b.liveIdsOf .remote).Nodup

/-! ### Basic projections of the allocator -/

theorem push_records (b : HtlcBook) (dir : Direction) (r : HTLCRecord) :
    (b.push dir r).records = r :: b.records := by
  cases dir <;> rfl

theorem push_nextId_same (b : HtlcBook) (dir : Direction) (r : HTLCRecord) :
    (b.push dir r).nextId dir = b.nextId dir + 1 := by
  cases dir <;> rfl

theorem push_nextId_other (b : HtlcBook) (dir dir' : Direction)
    (r : HTLCRecord) (hne : dir' ≠ dir) :
    (b.push dir r).nextId dir' = b.nextId dir' := by
  cases dir <;> cases dir' <;> simp_all [push, nextId]

theorem allocate_id (b : HtlcBook) (dir : Direction) (amount : Msat)
    (ph : PaymentHash) (cltv : Height) :
    (b.allocate dir amount ph cltv).id = b.nextId dir := rfl

theorem allocate_direction (b : HtlcBook) (dir : Direction) (amount : Msat)
    (ph : PaymentHash) (cltv : Height) :
    (b.allocate dir amount ph cltv).direction = dir := rfl

theorem allocate_isLive (b : HtlcBook) (dir : Direction) (amount : Msat)
    (ph : PaymentHash) (cltv : Height) :
    (b.allocate dir amount ph cltv).isLive = true := by
  cases dir <;> rfl

theorem insert_nextId_same (b : HtlcBook) (dir : Direction) (amount : Msat)
    (ph : PaymentHash) (cltv : Height) :
    (b.insert dir amount ph cltv).nextId dir = b.nextId dir + 1 :=
  push_nextId_same b dir (b.allocate dir amount ph cltv)

theorem insert_nextId_other (b : HtlcBook) (dir dir' : Direction)
    (amount : Msat) (ph : PaymentHash) (cltv : Height) (hne : dir' ≠ dir) :
    (b.insert dir amount ph cltv).nextId dir' = b.nextId dir' :=
  push_nextId_other b dir dir' (b.allocate dir amount ph cltv) hne

theorem insert_liveOf_same (b : HtlcBook) (dir : Direction) (amount : Msat)
    (ph : PaymentHash) (cltv : Height) :
    (b.insert dir amount ph cltv).liveOf dir =
      b.allocate dir amount ph cltv :: b.liveOf dir := by
  unfold insert
  unfold liveOf
  rw [push_records]
  rw [htlcSet_cons_live _ _ (allocate_isLive b dir amount ph cltv)]
  simp [allocate_direction]

theorem insert_liveIdsOf_same (b : HtlcBook) (dir : Direction) (amount : Msat)
    (ph : PaymentHash) (cltv : Height) :
    (b.insert dir amount ph cltv).liveIdsOf dir =
      b.nextId dir :: b.liveIdsOf dir := by
  unfold liveIdsOf
  rw [insert_liveOf_same, List.map_cons, allocate_id]

/-! ### The counter bound supplies freshness -/

/-- Every live id of a sender is strictly below that sender's next counter.
This is the part of the invariant that the allocator uses to rule out a
collision at the next allocation. -/
theorem liveIdsOf_lt_next (b : HtlcBook) (hb : b.WF) (dir : Direction) :
    ∀ x ∈ b.liveIdsOf dir, x < b.nextId dir := by
  cases dir
  · intro x hx
    unfold liveIdsOf liveOf at hx
    obtain ⟨r, hr, hid⟩ := List.mem_map.mp hx
    obtain ⟨hrlive, hrdir⟩ := List.mem_filter.mp hr
    have hdir : r.direction = .local := of_decide_eq_true hrdir
    have hlt := hb.bound_local r hrlive hdir
    simpa [hid, nextId] using hlt
  · intro x hx
    unfold liveIdsOf liveOf at hx
    obtain ⟨r, hr, hid⟩ := List.mem_map.mp hx
    obtain ⟨hrlive, hrdir⟩ := List.mem_filter.mp hr
    have hdir : r.direction = .remote := of_decide_eq_true hrdir
    have hlt := hb.bound_remote r hrlive hdir
    simpa [hid, nextId] using hlt

/-- The sender's next id is fresh for that sender's live set. -/
theorem nextId_not_mem_liveIdsOf (b : HtlcBook) (hb : b.WF) (dir : Direction) :
    b.nextId dir ∉ b.liveIdsOf dir := by
  intro hmem
  exact Nat.lt_irrefl _ (liveIdsOf_lt_next b hb dir _ hmem)

/-! ### Preservation of the invariant -/

theorem liveIdsOf_push_same (b : HtlcBook) (dir : Direction)
    (r : HTLCRecord) (hlive : r.isLive = true)
    (hdir : r.direction = dir) :
    (b.push dir r).liveIdsOf dir = r.id :: b.liveIdsOf dir := by
  cases dir
  · unfold liveIdsOf liveOf
    rw [push_records, htlcSet_cons_live r b.records hlive]
    simp [hdir]
  · unfold liveIdsOf liveOf
    rw [push_records, htlcSet_cons_live r b.records hlive]
    simp [hdir]

theorem liveIdsOf_push_other (b : HtlcBook) (dir dir' : Direction)
    (r : HTLCRecord) (hlive : r.isLive = true) (hne : r.direction ≠ dir') :
    (b.push dir r).liveIdsOf dir' = b.liveIdsOf dir' := by
  cases dir
  · unfold liveIdsOf liveOf
    rw [push_records, htlcSet_cons_live r b.records hlive]
    simp [hne]
  · unfold liveIdsOf liveOf
    rw [push_records, htlcSet_cons_live r b.records hlive]
    simp [hne]

/-- Inserting a freshly allocated record at the sender's counter preserves the
channel invariant.  This is where the bound does its work: the new id equals
the counter, so it is not among the old live ids. -/
theorem push_wf (b : HtlcBook) (hb : b.WF) (dir : Direction)
    (r : HTLCRecord) (hlive : r.isLive = true)
    (hdir : r.direction = dir) (hid : r.id = b.nextId dir) :
    (b.push dir r).WF := by
  cases dir
  · -- local insertion
    have hrid : r.id = b.nextLocalId := by
      simpa [nextId] using hid
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x hx hxdir
      rw [push_records] at hx
      rw [htlcSet_cons_live r b.records hlive] at hx
      rcases List.mem_cons.mp hx with hxr | hx
      · rw [hxr]
        show r.id < b.nextLocalId + 1
        omega
      · exact Nat.lt_trans (hb.bound_local x hx hxdir) (Nat.lt_succ_self _)
    · intro x hx hxdir
      rw [push_records] at hx
      rw [htlcSet_cons_live r b.records hlive] at hx
      rcases List.mem_cons.mp hx with hxr | hx
      · rw [hxr, hdir] at hxdir
        exact absurd hxdir (by decide)
      · exact hb.bound_remote x hx hxdir
    · rw [liveIdsOf_push_same b .local r hlive hdir, List.nodup_cons]
      exact ⟨by rw [hrid]; simpa [nextId] using nextId_not_mem_liveIdsOf b hb .local,
        hb.nodup_local⟩
    · rw [liveIdsOf_push_other b .local .remote r hlive (by rw [hdir]; decide)]
      exact hb.nodup_remote
  · -- remote insertion
    have hrid : r.id = b.nextRemoteId := by
      simpa [nextId] using hid
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x hx hxdir
      rw [push_records] at hx
      rw [htlcSet_cons_live r b.records hlive] at hx
      rcases List.mem_cons.mp hx with hxr | hx
      · rw [hxr, hdir] at hxdir
        exact absurd hxdir (by decide)
      · exact hb.bound_local x hx hxdir
    · intro x hx hxdir
      rw [push_records] at hx
      rw [htlcSet_cons_live r b.records hlive] at hx
      rcases List.mem_cons.mp hx with hxr | hx
      · rw [hxr]
        show r.id < b.nextRemoteId + 1
        omega
      · exact Nat.lt_trans (hb.bound_remote x hx hxdir) (Nat.lt_succ_self _)
    · rw [liveIdsOf_push_other b .remote .local r hlive (by rw [hdir]; decide)]
      exact hb.nodup_local
    · rw [liveIdsOf_push_same b .remote r hlive hdir, List.nodup_cons]
      exact ⟨by rw [hrid]; simpa [nextId] using nextId_not_mem_liveIdsOf b hb .remote,
        hb.nodup_remote⟩

theorem insert_wf (b : HtlcBook) (hb : b.WF) (dir : Direction)
    (amount : Msat) (ph : PaymentHash) (cltv : Height) :
    (b.insert dir amount ph cltv).WF := by
  unfold insert
  exact push_wf b hb dir (b.allocate dir amount ph cltv)
    (allocate_isLive b dir amount ph cltv)
    (allocate_direction b dir amount ph cltv)
    (allocate_id b dir amount ph cltv)

theorem empty_wf : empty.WF := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [empty, htlcSet, liveIdsOf, liveOf]

/-! ### Guarded insertion through `addHTLC` -/

theorem addHTLC_direction (maxHtlcValue currentTotal : Msat) (id : Nat)
    (dir : Direction) (amount : Msat) (ph : PaymentHash) (cltv : Height)
    (r : HTLCRecord)
    (ok : addHTLC maxHtlcValue currentTotal id dir amount ph cltv = .ok r) :
    r.direction = dir := by
  unfold addHTLC at ok
  split at ok
  · simp only [Result.ok.injEq] at ok
    subst ok
    rfl
  · simp at ok

/-- A successful guarded add is exactly a push of the record produced by
`addHTLC` at the sender's counter. -/
theorem add_ok (b : HtlcBook) (maxHtlcValue : Msat) (dir : Direction)
    (amount : Msat) (ph : PaymentHash) (cltv : Height) (b' : HtlcBook)
    (ok : b.add maxHtlcValue dir amount ph cltv = .ok b') :
    ∃ r, addHTLC maxHtlcValue b.totalInFlight (b.nextId dir) dir amount ph
        cltv = .ok r ∧
      b' = b.push dir r := by
  unfold add at ok
  split at ok
  · rename_i r hstep
    simp only [Result.ok.injEq] at ok
    exact ⟨r, hstep, ok.symm⟩
  · simp at ok

/-- A successful guarded add preserves the channel invariant. -/
theorem add_wf (b : HtlcBook) (hb : b.WF) (maxHtlcValue : Msat)
    (dir : Direction) (amount : Msat) (ph : PaymentHash) (cltv : Height)
    (b' : HtlcBook)
    (ok : b.add maxHtlcValue dir amount ph cltv = .ok b') :
    b'.WF := by
  obtain ⟨r, hadd, rfl⟩ := add_ok b maxHtlcValue dir amount ph cltv b' ok
  have hlive := addHTLC_isLive maxHtlcValue b.totalInFlight (b.nextId dir)
    dir amount ph cltv r hadd
  have hid := addHTLC_id maxHtlcValue b.totalInFlight (b.nextId dir)
    dir amount ph cltv r hadd
  have hdir := addHTLC_direction maxHtlcValue b.totalInFlight (b.nextId dir)
    dir amount ph cltv r hadd
  exact push_wf b hb dir r hlive hdir hid

/-- A successful guarded add advances the sender's counter by one. -/
theorem add_nextId_same (b : HtlcBook) (maxHtlcValue : Msat) (dir : Direction)
    (amount : Msat) (ph : PaymentHash) (cltv : Height) (b' : HtlcBook)
    (ok : b.add maxHtlcValue dir amount ph cltv = .ok b') :
    b'.nextId dir = b.nextId dir + 1 := by
  obtain ⟨r, _, rfl⟩ := add_ok b maxHtlcValue dir amount ph cltv b' ok
  exact push_nextId_same b dir r

/-- A successful guarded add prepends exactly the record that `allocate`
describes. -/
theorem add_records (b : HtlcBook) (maxHtlcValue : Msat) (dir : Direction)
    (amount : Msat) (ph : PaymentHash) (cltv : Height) (b' : HtlcBook)
    (ok : b.add maxHtlcValue dir amount ph cltv = .ok b') :
    b'.records = b.allocate dir amount ph cltv :: b.records := by
  obtain ⟨r, hadd, rfl⟩ := add_ok b maxHtlcValue dir amount ph cltv b' ok
  rw [push_records]
  congr 1
  unfold addHTLC at hadd
  split at hadd
  · simp only [Result.ok.injEq] at hadd
    subst hadd
    rfl
  · simp at hadd
/-- Books reachable from the empty book by the allocator: either a
counter-based insertion or a successful guarded add.  This is a *constructor
trace*, so a theorem over `Reachable` does not assume uniqueness or any other
state invariant. -/
inductive Reachable : HtlcBook → Prop where
  | empty : Reachable empty
  | insert {b : HtlcBook} (hb : Reachable b) (dir : Direction) (amount : Msat)
      (ph : PaymentHash) (cltv : Height) :
      Reachable (b.insert dir amount ph cltv)
  | add {b : HtlcBook} (hb : Reachable b) (maxHtlcValue : Msat)
      (dir : Direction) (amount : Msat) (ph : PaymentHash) (cltv : Height)
      {b' : HtlcBook} (ok : b.add maxHtlcValue dir amount ph cltv = .ok b') :
      Reachable b'

/-- Every reachable book satisfies the allocator invariant.  This is the
induction that turns `empty_wf` and `insert_wf`/`add_wf` into a property of
constructed states. -/
theorem reachable_wf {b : HtlcBook} (h : b.Reachable) : b.WF := by
  induction h with
  | empty => exact empty_wf
  | insert hb dir amount ph cltv ih => exact insert_wf _ ih dir amount ph cltv
  | add hb maxHtlcValue dir amount ph cltv ok ih =>
      exact add_wf _ ih maxHtlcValue dir amount ph cltv _ ok

/-! ### Per-sender uniqueness -/

theorem liveIdsOf_nodup (b : HtlcBook) (hb : b.WF) (dir : Direction) :
    (b.liveIdsOf dir).Nodup := by
  cases dir
  · exact hb.nodup_local
  · exact hb.nodup_remote

/-- **Per-sender id uniqueness.**  In a well-formed book, an id determines the
record among the live HTLCs of one sender.  This is the BOLT 2 per-sender id
rule, and it is proved from the allocator invariant rather than assumed on an
arbitrary list. -/
theorem liveOf_id_unique (b : HtlcBook) (hb : b.WF) (dir : Direction) :
    ∀ r1 ∈ b.liveOf dir, ∀ r2 ∈ b.liveOf dir, r1.id = r2.id → r1 = r2 := by
  have hnd : ((b.liveOf dir).map HTLCRecord.id).Nodup := by
    simpa [liveIdsOf] using liveIdsOf_nodup b hb dir
  exact eq_of_id_eq_of_htlcIds_nodup hnd

/-! ### Global uniqueness needs cross-direction disjointness -/

/-- No live local id equals a live remote id.  BOLT 2's per-sender counters do
not imply this: both senders start at 0
(`cross_direction_duplicate`). -/
def CrossDisjoint (b : HtlcBook) : Prop :=
  ∀ r1 ∈ htlcSet b.records, ∀ r2 ∈ htlcSet b.records,
    r1.direction = .local → r2.direction = .remote → r1.id ≠ r2.id

/-- With cross-direction disjointness, the live ids of the whole channel are
pairwise distinct.  The per-sender parts come from `WF`; `CrossDisjoint`
supplies exactly the missing cross-sender part. -/
theorem liveIds_nodup_of_cross (b : HtlcBook) (hb : b.WF)
    (hc : b.CrossDisjoint) : b.liveIds.Nodup := by
  have hlocal : (b.liveIdsOf .local).Nodup := hb.nodup_local
  have hremote : (b.liveIdsOf .remote).Nodup := hb.nodup_remote
  have hdisj : ∀ x ∈ b.liveIdsOf .local, ∀ y ∈ b.liveIdsOf .remote, x ≠ y := by
    intro x hx y hy hxy
    unfold liveIdsOf liveOf at hx hy
    obtain ⟨r1, hr1, hid1⟩ := List.mem_map.mp hx
    obtain ⟨r2, hr2, hid2⟩ := List.mem_map.mp hy
    have h1 := List.mem_filter.mp hr1
    have h2 := List.mem_filter.mp hr2
    have hd1 : r1.direction = .local := of_decide_eq_true h1.2
    have hd2 : r2.direction = .remote := of_decide_eq_true h2.2
    have hxy' : r1.id = r2.id := by rw [hid1, hid2]; exact hxy
    exact hc r1 h1.1 r2 h2.1 hd1 hd2 hxy'
  have happ : (b.liveIdsOf .local ++ b.liveIdsOf .remote).Nodup :=
    List.nodup_append.mpr ⟨hlocal, hremote, hdisj⟩
  have hperm : List.Perm (b.liveIdsOf .local ++ b.liveIdsOf .remote)
      b.liveIds := by
    unfold liveIdsOf liveIds liveOf
    simpa [List.map_append] using
      (htlc_filter_direction_perm (htlcSet b.records)).map HTLCRecord.id
  exact hperm.nodup happ

/-- The global form of `LN-HT-004`, under the explicit cross-direction
disjointness premise.  The premise is not a consequence of the per-sender
counters; see `cross_direction_duplicate`. -/
theorem live_id_unique_of_cross (b : HtlcBook) (hb : b.WF)
    (hc : b.CrossDisjoint) :
    ∀ r1 ∈ htlcSet b.records, ∀ r2 ∈ htlcSet b.records,
      r1.id = r2.id → r1 = r2 :=
  eq_of_id_eq_of_htlcIds_nodup (by simpa [liveIds] using liveIds_nodup_of_cross b hb hc)

/-! ### The faithful counterexample: two senders may both use id 0 -/

/-- Payment hash used by the counterexample. -/
def sampleHash : PaymentHash := ⟨ByteArray.empty⟩

/-- A well-formed book after one local and one remote add.  BOLT 2 gives each
sender id 0 for its first HTLC, so the two live records share an id even though
every allocation was fresh for its own sender. -/
def crossBook : HtlcBook :=
  (empty.insert .local ⟨1000⟩ sampleHash 500).insert .remote ⟨2000⟩ sampleHash 600

theorem crossBook_wf : crossBook.WF := by
  unfold crossBook
  exact insert_wf
    (HtlcBook.empty.insert .local ⟨1000⟩ sampleHash 500)
    (insert_wf HtlcBook.empty HtlcBook.empty_wf .local ⟨1000⟩ sampleHash 500)
    .remote ⟨2000⟩ sampleHash 600

theorem crossBook_records :
    crossBook.records =
      [{ id := 0
         direction := .remote
         amountMsat := ⟨2000⟩
         paymentHash := sampleHash
         cltvExpiry := 600
         state := .received },
       { id := 0
         direction := .local
         amountMsat := ⟨1000⟩
         paymentHash := sampleHash
         cltvExpiry := 500
         state := .offered }] := rfl

theorem crossBook_liveIds : crossBook.liveIds = [0, 0] := by
  unfold HtlcBook.liveIds
  rw [crossBook_records]
  decide

/-- The book built by two successful allocations has a duplicate live id
across the two senders.  This is why the global wording of `LN-HT-004` cannot
be promoted as an unconditional theorem about the faithful allocator. -/
theorem crossBook_not_liveHtlcIdsNodup :
    ¬ liveHtlcIdsNodup crossBook.records := by
  unfold liveHtlcIdsNodup
  have h : liveHtlcIds crossBook.records = [0, 0] := crossBook_liveIds
  rw [h]
  simp

theorem crossBook_duplicate_pair :
    ∃ r1 ∈ htlcSet crossBook.records, ∃ r2 ∈ htlcSet crossBook.records,
      r1 ≠ r2 ∧ r1.id = r2.id := by
  refine
    ⟨{ id := 0, direction := .remote, amountMsat := ⟨2000⟩,
        paymentHash := sampleHash, cltvExpiry := 600, state := .received },
     ?_,
     { id := 0, direction := .local, amountMsat := ⟨1000⟩,
        paymentHash := sampleHash, cltvExpiry := 500, state := .offered },
     ?_, ?_, rfl⟩
  · simp [crossBook_records, htlcSet, HTLCRecord.isLive, HTLCState.isLive]
  · simp [crossBook_records, htlcSet, HTLCRecord.isLive, HTLCState.isLive]
  · decide

/-- The allocator is faithful but its live set need not be globally id-unique:
the two senders' independent counters both start at 0. -/
theorem cross_direction_duplicate :
    crossBook.WF ∧ ¬ liveHtlcIdsNodup crossBook.records :=
  ⟨crossBook_wf, crossBook_not_liveHtlcIdsNodup⟩

/-- The empty book is well formed and has no live ids. -/
theorem empty_liveIds : empty.liveIds = [] := rfl

theorem crossBook_reachable : crossBook.Reachable :=
  Reachable.insert
    (Reachable.insert Reachable.empty .local ⟨1000⟩ sampleHash 500)
    .remote ⟨2000⟩ sampleHash 600

/-- **Even reachable books need not be globally id-unique.**  The two senders'
independent counters both start at 0, so the allocator itself produces two live
records with id 0.  This is the precise reason the global wording of
`LN-HT-004` cannot be promoted unconditionally. -/
theorem reachable_cross_direction_duplicate :
    ∃ b : HtlcBook, b.Reachable ∧ ¬ liveHtlcIdsNodup b.records :=
  ⟨crossBook, crossBook_reachable, crossBook_not_liveHtlcIdsNodup⟩

/-- **Per-sender uniqueness for every constructed book.**  The hypothesis is
only a constructor trace of allocations, not an id-distinctness invariant. -/
theorem reachable_liveOf_id_unique {b : HtlcBook} (h : b.Reachable)
    (dir : Direction) :
    ∀ r1 ∈ b.liveOf dir, ∀ r2 ∈ b.liveOf dir, r1.id = r2.id → r1 = r2 :=
  liveOf_id_unique b (reachable_wf h) dir

end HtlcBook

/-! ## Catalog-named target for the narrowed `LN-HT-004`

The narrow theorem below is the faithful reading of "an HTLC id is unique
within the live HTLC set of a channel": BOLT 2 ids are per sender, and this is
exactly `HtlcBook.reachable_liveOf_id_unique` (or `liveOf_id_unique` once the
allocator invariant is in hand).  The original global target
`LnLean.Channel.HTLC.id_unique` is retained above and still takes the
uniqueness invariant as a hypothesis; the new API proves that invariant from
allocation for a reachable book. -/

namespace HTLC

/-- Catalog target `LN-HT-004` (per-sender form): in a book built by the
allocator, an id determines the record among the live HTLCs of one sender.
There is no id-distinctness hypothesis. -/
theorem dir_id_unique {b : HtlcBook} (hb : b.Reachable) (dir : Direction) :
    ∀ r1 ∈ b.liveOf dir, ∀ r2 ∈ b.liveOf dir, r1.id = r2.id → r1 = r2 :=
  HtlcBook.reachable_liveOf_id_unique hb dir

/-- The same per-sender uniqueness from the allocator invariant, for callers
that already hold `WF`. -/
theorem dir_id_unique_of_wf (b : HtlcBook) (hb : b.WF) (dir : Direction) :
    ∀ r1 ∈ b.liveOf dir, ∀ r2 ∈ b.liveOf dir, r1.id = r2.id → r1 = r2 :=
  HtlcBook.liveOf_id_unique b hb dir

/-- Global form of `LN-HT-004` under explicit cross-direction disjointness.
The literal unconditional global claim is refuted by
`HtlcBook.cross_direction_duplicate`. -/
theorem id_unique_of_cross (b : HtlcBook) (hb : b.WF)
    (hc : b.CrossDisjoint) :
    ∀ r1 ∈ htlcSet b.records, ∀ r2 ∈ htlcSet b.records,
      r1.id = r2.id → r1 = r2 :=
  HtlcBook.live_id_unique_of_cross b hb hc

/-- The global conditional form for every constructed book: a constructor
trace plus cross-direction disjointness (not a consequence of the allocator)
gives global uniqueness. -/
theorem id_unique_of_reachable_cross {b : HtlcBook} (hb : b.Reachable)
    (hc : b.CrossDisjoint) :
    ∀ r1 ∈ htlcSet b.records, ∀ r2 ∈ htlcSet b.records,
      r1.id = r2.id → r1 = r2 :=
  HtlcBook.live_id_unique_of_cross b (HtlcBook.reachable_wf hb) hc

end HTLC

/-! ## Direction-tagged channel-wide identifiers

BOLT 2 numbers `update_add_htlc.id` independently for each sender: the wire
value is a per-sender counter (`refs/bolts/02-peer-protocol.md:2838-2843`), not
a channel-wide identifier.  The existing record therefore has to be read
together with `direction`; that is exactly what the per-sender theorem
`HTLC.dir_id_unique` does, while the literal channel-wide form needs
`HtlcBook.CrossDisjoint` (`cross_direction_duplicate` shows why).

This section adds the missing namespace explicitly.  `HTLCTag` is
`Direction × Nat`, and `HTLCRecord.tag` maps a record to `(direction, id)`.
This is a *view* of the existing fields, not a new wire encoding: it does not
change `HTLCRecord`, `addHTLC`, either per-sender counter, `HtlcBook`'s public
API, or any theorem above.  Under this namespace the channel-wide uniqueness
claim becomes a property of every well-formed (and hence every reachable) book
without `CrossDisjoint`: the first component separates the two independent
counters, and `WF` supplies per-sender id distinctness.  The reachability form
and the `crossBook` connection live in
`LnLean.Proofs.Channel.HtlcGlobalIdTargets`.

Both BOLT 2 counters are `Nat` in this model (`HtlcBook.nextLocalId`,
`HtlcBook.nextRemoteId`), so the tag loses no information: `(direction, id)`
determines both the sender and every bit of that sender's counter value.  A
single-`Nat` encoding such as `2 * id` / `2 * id + 1` is also injective, but it
is a model-side encoding with no BOLT 2 wire meaning; the pair is the faithful
representation and is the one used below. -/

/-- A channel-wide HTLC identifier: the sender (`Direction.local` = offered by
us, `Direction.remote` = received by us) together with that sender's BOLT 2
`update_add_htlc.id`. -/
abbrev HTLCTag : Type := Direction × Nat

namespace HTLCRecord

/-- The direction-tagged, channel-wide identifier of a record.  It is the
faithful reading of "HTLC id" for a whole channel; the bare `id` field is only
unique per sender. -/
def tag (r : HTLCRecord) : HTLCTag := (r.direction, r.id)

@[simp] theorem tag_fst (r : HTLCRecord) : r.tag.1 = r.direction := rfl

@[simp] theorem tag_snd (r : HTLCRecord) : r.tag.2 = r.id := rfl

theorem tag_eq_iff {r1 r2 : HTLCRecord} :
    r1.tag = r2.tag ↔ r1.direction = r2.direction ∧ r1.id = r2.id := by
  constructor
  · intro h
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  · rintro ⟨hdir, hid⟩
    unfold tag
    rw [hdir, hid]

theorem direction_eq_of_tag_eq {r1 r2 : HTLCRecord} (h : r1.tag = r2.tag) :
    r1.direction = r2.direction :=
  (tag_eq_iff.mp h).1

theorem id_eq_of_tag_eq {r1 r2 : HTLCRecord} (h : r1.tag = r2.tag) :
    r1.id = r2.id :=
  (tag_eq_iff.mp h).2

theorem tag_congr {r1 r2 : HTLCRecord} (h : r1 = r2) : r1.tag = r2.tag :=
  congrArg tag h

theorem tag_ne_of_direction_ne {r1 r2 : HTLCRecord}
    (h : r1.direction ≠ r2.direction) : r1.tag ≠ r2.tag :=
  fun htag => h (direction_eq_of_tag_eq htag)

theorem tag_ne_of_id_ne {r1 r2 : HTLCRecord} (h : r1.id ≠ r2.id) :
    r1.tag ≠ r2.tag :=
  fun htag => h (id_eq_of_tag_eq htag)

end HTLCRecord

/-- The direction-tagged identifiers of a record list, in list order. -/
def taggedIds (hs : List HTLCRecord) : List HTLCTag :=
  hs.map HTLCRecord.tag

theorem mem_taggedIds_iff {t : HTLCTag} {hs : List HTLCRecord} :
    t ∈ taggedIds hs ↔ ∃ r ∈ hs, r.tag = t := by
  unfold taggedIds
  exact List.mem_map

/-- Mapping an already duplicate-free list under a function that is injective
on that list preserves `Nodup`. -/
theorem nodup_map_of_inj_on {α β : Type} {l : List α} {f : α → β}
    (hl : l.Nodup) (hinj : ∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) :
    (l.map f).Nodup := by
  rw [List.nodup_iff_eq_of_getElem_eq] at hl ⊢
  intro i j hi hj heq
  have hi' : i < l.length := by simpa using hi
  have hj' : j < l.length := by simpa using hj
  have heq' : f l[i] = f l[j] := by simpa using heq
  exact hl i j hi' hj'
    (hinj l[i] (List.getElem_mem hi') l[j] (List.getElem_mem hj') heq')

/-- A record list whose ids are pairwise distinct has no duplicate records. -/
theorem nodup_of_map_id_nodup {l : List HTLCRecord}
    (h : (l.map HTLCRecord.id).Nodup) : l.Nodup := by
  rw [List.nodup_iff_eq_of_getElem_eq] at h ⊢
  intro i j hi hj heq
  exact h i j (by simpa using hi) (by simpa using hj)
    (by simpa using congrArg HTLCRecord.id heq)

/-- Per-sender id distinctness makes the tagged map injective on the list.
The direction component of the tag is what supplies the cross-sender part, so
no `CrossDisjoint` premise appears. -/
theorem eq_of_tag_eq_of_dir_nodup (l : List HTLCRecord)
    (hnd : ∀ dir : Direction,
      ((l.filter (fun r => decide (r.direction = dir))).map HTLCRecord.id).Nodup) :
    ∀ r1 ∈ l, ∀ r2 ∈ l, r1.tag = r2.tag → r1 = r2 := by
  intro r1 h1 r2 h2 htag
  have hdir : r1.direction = r2.direction :=
    HTLCRecord.direction_eq_of_tag_eq htag
  have hid : r1.id = r2.id := HTLCRecord.id_eq_of_tag_eq htag
  have h1f : r1 ∈ l.filter (fun r => decide (r.direction = r1.direction)) :=
    List.mem_filter.mpr ⟨h1, by simp⟩
  have h2f : r2 ∈ l.filter (fun r => decide (r.direction = r1.direction)) :=
    List.mem_filter.mpr ⟨h2, by simp [hdir]⟩
  exact eq_of_id_eq_of_htlcIds_nodup (hnd r1.direction) r1 h1f r2 h2f hid

namespace HtlcBook

/-- The direction-tagged ids of the live HTLC set.  This is the channel-wide
counterpart of `liveIds`, which projects only the per-sender id. -/
def liveTags (b : HtlcBook) : List HTLCTag :=
  taggedIds (htlcSet b.records)

/-- The direction-tagged ids of one sender's live HTLCs. -/
def liveTagsOf (b : HtlcBook) (dir : Direction) : List HTLCTag :=
  (b.liveOf dir).map HTLCRecord.tag

theorem mem_liveTags_iff {t : HTLCTag} {b : HtlcBook} :
    t ∈ b.liveTags ↔ ∃ r ∈ htlcSet b.records, r.tag = t := by
  unfold liveTags taggedIds
  exact List.mem_map

theorem mem_liveTagsOf_iff {t : HTLCTag} {b : HtlcBook} {dir : Direction} :
    t ∈ b.liveTagsOf dir ↔ ∃ r ∈ b.liveOf dir, r.tag = t := by
  unfold liveTagsOf
  exact List.mem_map

/-- A sender's live records have no duplicate record. -/
theorem liveOf_nodup (b : HtlcBook) (hb : b.WF) (dir : Direction) :
    (b.liveOf dir).Nodup := by
  have h := liveIdsOf_nodup b hb dir
  unfold liveIdsOf at h
  exact nodup_of_map_id_nodup h

/-- The live record list of a well-formed book has no duplicate record.  The
per-sender `Nodup` fields rule out a local duplicate and a remote duplicate;
the two direction filters are disjoint because a record has one direction. -/
theorem htlcSet_nodup_of_wf (b : HtlcBook) (hb : b.WF) :
    (htlcSet b.records).Nodup := by
  have hlocal := liveOf_nodup b hb .local
  have hremote := liveOf_nodup b hb .remote
  have hdisj : ∀ a ∈ b.liveOf .local, ∀ c ∈ b.liveOf .remote, a ≠ c := by
    intro a ha c hc hac
    have hda : a.direction = .local :=
      of_decide_eq_true (List.mem_filter.mp ha).2
    have hdc : c.direction = .remote :=
      of_decide_eq_true (List.mem_filter.mp hc).2
    have hdir : a.direction = c.direction := by rw [hac]
    rw [hda, hdc] at hdir
    exact absurd hdir (by decide)
  have happ : (b.liveOf .local ++ b.liveOf .remote).Nodup :=
    List.nodup_append.mpr ⟨hlocal, hremote, hdisj⟩
  have hperm : List.Perm (b.liveOf .local ++ b.liveOf .remote)
      (htlcSet b.records) := by
    simpa [liveOf] using htlc_filter_direction_perm (htlcSet b.records)
  exact hperm.nodup happ

/-- **Channel-wide tagged uniqueness from the allocator invariant.**  In a
well-formed book a direction-tagged id determines the live record, with no
cross-direction assumption.  The first component of the tag is exactly the
cross-sender separation that `CrossDisjoint` used to supply for the bare id. -/
theorem tagged_id_unique_of_wf (b : HtlcBook) (hb : b.WF) :
    ∀ r1 ∈ htlcSet b.records, ∀ r2 ∈ htlcSet b.records,
      r1.tag = r2.tag → r1 = r2 := by
  refine eq_of_tag_eq_of_dir_nodup (htlcSet b.records) ?_
  intro dir
  cases dir
  · simpa [liveIdsOf, liveOf] using hb.nodup_local
  · simpa [liveIdsOf, liveOf] using hb.nodup_remote

/-- The live direction-tagged ids of a well-formed book are pairwise distinct.
This is the channel-wide form of `liveIdsOf_nodup`; unlike `liveIds_nodup_of_cross`
it needs no `CrossDisjoint` field. -/
theorem liveTags_nodup_of_wf (b : HtlcBook) (hb : b.WF) :
    b.liveTags.Nodup := by
  unfold liveTags taggedIds
  exact nodup_map_of_inj_on (htlcSet_nodup_of_wf b hb)
    (tagged_id_unique_of_wf b hb)

end HtlcBook

end LnLean.Channel
