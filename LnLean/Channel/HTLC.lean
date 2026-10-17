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

end LnLean.Channel
