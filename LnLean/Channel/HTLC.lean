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
and `HTLCRecord` has neither a counter nor a distinctness field.  A faithful
exact target therefore requires a channel/ledger record carrying the per-sender
counters (as in `LnLean.Proofs.WaveD.D16`) or a `Nodup` invariant on the state.
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
premise is discharged by the model.  In particular:

* `amount_conservation` still takes the channel-ledger invariant as a
  hypothesis because `HTLCRecord` has no balance, fee, or funding field;
* `id_unique` still takes live-id distinctness as a hypothesis because the
  unconditional claim is false (`liveHtlcIdsNodup_unconditional_false`). -/

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
unconditional catalog wording is not claimed here. -/
theorem id_unique (hs : List HTLCRecord)
    (hnd : liveHtlcIdsNodup hs) :
    ∀ h1 ∈ htlcSet hs, ∀ h2 ∈ htlcSet hs, h1.id = h2.id → h1 = h2 :=
  liveHtlcIdsNodup_unique hs hnd

end HTLC

end LnLean.Channel
