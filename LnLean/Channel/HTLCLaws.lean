import LnLean.Basic.Core
import LnLean.Bitcoin.Seam
import LnLean.Channel.HTLC
import LnLean.Channel.Revocation
import LnLean.Channel.Penalty

/-!
# LnLean.Channel.HTLCLaws

English claim.  The HTLCRecord lifecycle has the following structural laws:
a successful fulfillment carries a 32-byte preimage that hashes to the
payment hash; state transitions strictly increase the lifecycle rank
`offered/received < fulfilled/failed < removed`, hence the transition
relation is acyclic; an added HTLCRecord has a positive amount, fits under
`max_htlc_value_in_flight_msat`, and has `cltv_expiry < 500000000`; a dust
HTLCRecord has no commitment output; and every per-commitment secret is 32 bytes.

All statements are unconditional except the preimage/hash law, which is
conditional on the caller-supplied `hashFn` producing the HTLCRecord's payment
hash (the cryptographic premise is an explicit hypothesis of the model's
transition guard, never a global assumption).

BOLT anchors.
* BOLT 2 adding an HTLCRecord: `refs/bolts/02-peer-protocol.md:2772`
  (positive amount, total in flight, `cltv_expiry < 500000000`).
* BOLT 2 removing an HTLCRecord: `refs/bolts/02-peer-protocol.md:2913`
  (32-byte `payment_preimage`, hash check).
* BOLT 3 trimmed outputs: `refs/bolts/03-transactions.md:305`.
* BOLT 3 per-commitment secrets: `refs/bolts/03-transactions.md:828`.

rust-lightning anchors (commit fe49009).
* `lightning/src/ln/chan_utils.rs:716` (`HTLCOutputInCommitment`).
* `lightning/src/ln/chan_utils.rs:735` (msat to sat conversion).
* `lightning/src/ln/chan_utils.rs:339` (`build_commitment_secret`).
* `lightning/src/ln/channel.rs:9444` (32-byte secret parsing).

Not modelled.
* No concrete SHA-256: the preimage law is conditional on `hashFn`.
* No signature/script verification; see `LnLean.Channel.Penalty` for the
  named L1 bridge.
* The obligation catalogue ids are recorded in the report; this file is a
  model module and therefore carries no open proof placeholders.
-/

namespace LnLean.Channel

open LnLean

set_option autoImplicit false

/-! ## The transition relation -/

/-- The expected HTLCRecord lifecycle as a relation over one HTLCRecord.  Only live
HTLCs can be settled; timeout additionally needs an offered (`local`)
direction and a chain height at or past `cltv_expiry`; removal needs a
settled state.  The relation is parameterized by the hash function and the
chain height, so no transition silently assumes a primitive. -/
inductive HTLCTrans (hashFn : ByteArray → ByteArray) (height : Height) :
    HTLCRecord → HTLCRecord → Prop where
  | fulfill {h : HTLCRecord} {p : Preimage}
      (hlive : h.isLive = true)
      (hmatch : decide (p.bytes.size = 32 ∧ hashFn p.bytes = h.paymentHash.bytes) = true) :
      HTLCTrans hashFn height h { h with state := .fulfilled }
  | fail {h : HTLCRecord}
      (hlive : h.isLive = true) :
      HTLCTrans hashFn height h { h with state := .failed }
  | timeout {h : HTLCRecord}
      (hlive : h.isLive = true)
      (hlocal : h.direction = .local)
      (hexpiry : h.cltvExpiry ≤ height) :
      HTLCTrans hashFn height h { h with state := .failed }
  | removeFulfilled {h : HTLCRecord}
      (hstate : h.state = .fulfilled) :
      HTLCTrans hashFn height h { h with state := .removed }
  | removeFailed {h : HTLCRecord}
      (hstate : h.state = .failed) :
      HTLCTrans hashFn height h { h with state := .removed }

/-! ## Law 1: every transition strictly increases the lifecycle rank -/

/-- The rank strictly increases along every transition.  This single measure
yields acyclicity and the expected order of the lifecycle. -/
theorem HTLCTrans.rank_lt {hashFn : ByteArray → ByteArray} {height : Height}
    {h h' : HTLCRecord} (t : HTLCTrans hashFn height h h') :
    h.state.rank < h'.state.rank := by
  cases t with
  | fulfill hlive hmatch =>
      cases hs : h.state <;> simp [HTLCRecord.isLive, hs, HTLCState.rank] at hlive ⊢
  | fail hlive =>
      cases hs : h.state <;> simp [HTLCRecord.isLive, hs, HTLCState.rank] at hlive ⊢
  | timeout hlive hlocal hexpiry =>
      cases hs : h.state <;> simp [HTLCRecord.isLive, hs, HTLCState.rank] at hlive ⊢
  | removeFulfilled hstate =>
      rw [hstate]
      simp [HTLCState.rank]
  | removeFailed hstate =>
      rw [hstate]
      simp [HTLCState.rank]

/-- No state transition returns to its starting HTLCRecord: the lifecycle is
irreflexive. -/
theorem HTLCTrans.irrefl {hashFn : ByteArray → ByteArray} {height : Height}
    {h : HTLCRecord} (t : HTLCTrans hashFn height h h) : False := by
  have hlt := t.rank_lt
  omega

/-- Along any nonempty chain of transitions the rank strictly increases. -/
theorem HTLCTrans.transGen_rank_lt {hashFn : ByteArray → ByteArray} {height : Height}
    {h h' : HTLCRecord} (t : Relation.TransGen (HTLCTrans hashFn height) h h') :
    h.state.rank < h'.state.rank := by
  induction t with
  | single s => exact s.rank_lt
  | tail _ s ih => exact Nat.lt_trans ih s.rank_lt

/-- The lifecycle has no cycles at all, not merely no self-loop. -/
theorem HTLCTrans.no_cycle {hashFn : ByteArray → ByteArray} {height : Height}
    {h : HTLCRecord} (t : Relation.TransGen (HTLCTrans hashFn height) h h) : False := by
  have hlt := HTLCTrans.transGen_rank_lt t
  omega

/-- A removed HTLCRecord has no outgoing transition.  This is the terminal state
of the lifecycle. -/
theorem no_transition_from_removed {hashFn : ByteArray → ByteArray} {height : Height}
    {h h' : HTLCRecord} (t : HTLCTrans hashFn height h h') (hs : h.state = .removed) :
    False := by
  have hlt := t.rank_lt
  rw [hs] at hlt
  cases hh : h'.state <;> simp [HTLCState.rank, hh] at hlt

/-! ## Law 2: fulfillment requires a 32-byte preimage -/

/-- A successful `fulfillHTLC` carries a preimage of exactly 32 bytes. -/
theorem fulfill_requires_32_byte_preimage (hashFn : ByteArray → ByteArray)
    {h h' : HTLCRecord} {p : Preimage} (ok : fulfillHTLC hashFn h p = .ok h') :
    p.bytes.size = 32 :=
  (fulfillHTLC_hash hashFn h h' p ok).1

/-- A successful `fulfillHTLC` reveals a preimage that hashes to the HTLCRecord's
payment hash.  This is the conditional cryptographic law: it is part of the
transition guard, and the caller chooses `hashFn`. -/
theorem fulfill_hash_matches (hashFn : ByteArray → ByteArray)
    {h h' : HTLCRecord} {p : Preimage} (ok : fulfillHTLC hashFn h p = .ok h') :
    hashFn p.bytes = h.paymentHash.bytes :=
  (fulfillHTLC_hash hashFn h h' p ok).2

/-- The same two facts for the relational transition guard. -/
theorem HTLCTrans.fulfill_preimage {hashFn : ByteArray → ByteArray}
    {h : HTLCRecord} (p : Preimage) (hmatch : decide (p.bytes.size = 32 ∧
      hashFn p.bytes = h.paymentHash.bytes) = true) :
    p.bytes.size = 32 ∧ hashFn p.bytes = h.paymentHash.bytes := by
  exact of_decide_eq_true hmatch

/-! ## Law 3: `addHTLC` bounds -/

/-- Every successful `addHTLC` satisfies the BOLT 2 sending-node MUSTs. -/
theorem addHTLC_guard (maxHtlcValue currentTotal : Msat) (id : Nat)
    (dir : Direction) (amount : Msat) (ph : PaymentHash) (cltv : Height)
    (h : HTLCRecord) (ok : addHTLC maxHtlcValue currentTotal id dir amount ph cltv = .ok h) :
    0 < amount.val ∧ currentTotal.val + amount.val ≤ maxHtlcValue.val ∧
      cltv < MAX_CLTV_EXPIRY := by
  unfold addHTLC at ok
  split at ok
  · rename_i hg
    exact hg
  · simp at ok

/-- An added HTLCRecord has a strictly positive amount (BOLT 2:
"MUST offer `amount_msat` greater than 0"). -/
theorem addHTLC_amount_pos (maxHtlcValue currentTotal : Msat) (id : Nat)
    (dir : Direction) (amount : Msat) (ph : PaymentHash) (cltv : Height)
    (h : HTLCRecord) (ok : addHTLC maxHtlcValue currentTotal id dir amount ph cltv = .ok h) :
    0 < amount.val :=
  (addHTLC_guard maxHtlcValue currentTotal id dir amount ph cltv h ok).1

/-- An added HTLCRecord fits the channel's `max_htlc_value_in_flight_msat`: the
running total plus this HTLCRecord does not exceed the limit. -/
theorem addHTLC_total_le_max (maxHtlcValue currentTotal : Msat) (id : Nat)
    (dir : Direction) (amount : Msat) (ph : PaymentHash) (cltv : Height)
    (h : HTLCRecord) (ok : addHTLC maxHtlcValue currentTotal id dir amount ph cltv = .ok h) :
    currentTotal.val + amount.val ≤ maxHtlcValue.val :=
  (addHTLC_guard maxHtlcValue currentTotal id dir amount ph cltv h ok).2.1

/-- In particular the single HTLCRecord amount is within the channel limit. -/
theorem addHTLC_amount_le_max (maxHtlcValue currentTotal : Msat) (id : Nat)
    (dir : Direction) (amount : Msat) (ph : PaymentHash) (cltv : Height)
    (h : HTLCRecord) (ok : addHTLC maxHtlcValue currentTotal id dir amount ph cltv = .ok h) :
    amount.val ≤ maxHtlcValue.val := by
  have hg := addHTLC_total_le_max maxHtlcValue currentTotal id dir amount ph cltv h ok
  omega

/-- An added HTLCRecord's CLTV expiry is strictly below the BOLT 2 maximum. -/
theorem addHTLC_cltv_bounded (maxHtlcValue currentTotal : Msat) (id : Nat)
    (dir : Direction) (amount : Msat) (ph : PaymentHash) (cltv : Height)
    (h : HTLCRecord) (ok : addHTLC maxHtlcValue currentTotal id dir amount ph cltv = .ok h) :
    cltv < MAX_CLTV_EXPIRY :=
  (addHTLC_guard maxHtlcValue currentTotal id dir amount ph cltv h ok).2.2

/-- The direction-to-state mapping of a successful add. -/
theorem addHTLC_offered (maxHtlcValue currentTotal : Msat) (id : Nat)
    (amount : Msat) (ph : PaymentHash) (cltv : Height) (h : HTLCRecord)
    (ok : addHTLC maxHtlcValue currentTotal id .local amount ph cltv = .ok h) :
    h.state = .offered :=
  addHTLC_state_local maxHtlcValue currentTotal id amount ph cltv h ok

theorem addHTLC_received (maxHtlcValue currentTotal : Msat) (id : Nat)
    (amount : Msat) (ph : PaymentHash) (cltv : Height) (h : HTLCRecord)
    (ok : addHTLC maxHtlcValue currentTotal id .remote amount ph cltv = .ok h) :
    h.state = .received :=
  addHTLC_state_remote maxHtlcValue currentTotal id amount ph cltv h ok

/-! ## Law 4: dust HTLCs have no output -/

/-- A dust HTLCRecord has no commitment output. -/
theorem dust_no_output (h : HTLCRecord) (dustLimit t s : Nat)
    (hd : isDustHTLC h dustLimit t s = true) :
    hasOutput h dustLimit t s = false := by
  simp [hasOutput, hd]

/-- Dually, a non-dust HTLCRecord has an output. -/
theorem nonDust_has_output (h : HTLCRecord) (dustLimit t s : Nat)
    (hd : isDustHTLC h dustLimit t s = false) :
    hasOutput h dustLimit t s = true := by
  simp [hasOutput, hd]

/-- A dust HTLCRecord's output value is strictly below `dust_limit_satoshis`, which
is the BOLT 3 trimming condition. -/
theorem dust_value_lt (h : HTLCRecord) (dustLimit t s : Nat)
    (hd : isDustHTLC h dustLimit t s = true) :
    htlcOutputValue h t s < dustLimit :=
  (isDust_iff h dustLimit t s).1 hd

/-- A non-dust output is at least the dust limit. -/
theorem nonDust_value_ge (h : HTLCRecord) (dustLimit t s : Nat)
    (hd : isDustHTLC h dustLimit t s = false) :
    dustLimit ≤ htlcOutputValue h t s := by
  have := (hasOutput_iff h dustLimit t s).1 (nonDust_has_output h dustLimit t s hd)
  exact this

/-! ## Law 5: revocation secrets are 32 bytes -/

/-- Every per-commitment secret produced by the shachain is 32 bytes. -/
theorem revocation_secret_length_32 (sh : Shachain) (idx : Nat) :
    (revocationSecret sh idx).bytes.size = 32 :=
  revocationSecret_size sh idx

/-- Distinct valid commitment numbers have distinct secrets. -/
theorem revocation_secret_distinct (sh : Shachain) {i j : Nat}
    (hi : i ≤ MAX_COMMITMENT_NUMBER) (hj : j ≤ MAX_COMMITMENT_NUMBER)
    (h : revocationSecret sh i = revocationSecret sh j) : i = j :=
  revocationSecret_injective sh hi hj h

/-- Revealing a secret revokes its commitment. -/
theorem revoked_after_provide (st : RevocationStore) (idx : Nat)
    (s : PerCommitmentSecret) (hidx : idx < COMMITMENT_SECRET_COUNT) :
    isRevoked (provideSecret st idx s hidx) idx :=
  isRevoked_provide_self st idx s hidx

/-- Revocation is monotone: revealing a later secret never restores an
earlier commitment. -/
theorem revoked_monotone (st : RevocationStore) {i : Nat}
    (s : PerCommitmentSecret) (idx : Nat) (hidx : idx < COMMITMENT_SECRET_COUNT)
    (h : isRevoked st i) : isRevoked (provideSecret st idx s hidx) i :=
  isRevoked_provide_mono st s idx hidx h

/-! ## Law 6: the live-HTLCRecord set -/

/-- Every member of `htlcSet` is live. -/
theorem htlcSet_sound (hs : List HTLCRecord) {h : HTLCRecord} (hm : h ∈ htlcSet hs) :
    h.isLive = true := by
  unfold htlcSet at hm
  exact (List.mem_filter.mp hm).2

/-- Filtering to live HTLCs cannot increase the count. -/
theorem htlcSet_length_le (hs : List HTLCRecord) : (htlcSet hs).length ≤ hs.length := by
  unfold htlcSet
  exact List.length_filter_le _ _

end LnLean.Channel
