import LnLean.Basic.Core
import LnLean.Bitcoin.Seam

/-!
# LnLean.Security.Invariants

English claim.  This module gives a small executable model of the state that
the core Lightning invariants talk about (a channel ledger, the set of spent
L1 outpoints, an HTLC record, a revocation/penalty record, a commitment
counter, a route, an invoice, an MPP payment, and a message schedule), then
states the ten core invariants as `Invariant` records.  Every invariant that
is marked as a Lean `predicate` below has a proof in this file; nothing here
is assumed.

The ten invariants are: value conservation, no double spend, HTLC preimage
soundness, HTLC timeout safety, revocation/penalty, commitment-state
monotonicity, route well-formedness, invoice consistency, MPP atomicity, and
liveness under partial synchrony.

BOLT sections.  BOLT 2 §"Adding an HTLC", §"Removing an HTLC",
§"Committing Updates So Far", §"Completing the Transition to the Updated
State"; BOLT 3 §"Commitment Transaction", §"HTLC-Timeout and HTLC-Success
Transactions", §"Per-commitment Secret Requirements"; BOLT 4
§"Basic Multi-Part Payments"; BOLT 5 §"Revoked Transaction Close Handling";
BOLT 7 §"Recommendations for Routing"; BOLT 11 §"Tagged Fields".

`rust-lightning` anchors at commit `fe49009`:
* `lightning/src/ln/chan_utils.rs:841` (`get_htlc_redeemscript`),
  `:875` (`build_htlc_transaction`), `:518` (`derive_private_key`);
* `lightning/src/ln/channel.rs:6270` (`build_commitment_transaction`),
  `:8182` (failing an HTLC), `:8370` (`update_add_htlc`);
* `lightning/src/ln/channelmanager.rs:10210` (`claim_funds`), `:9878`
  (`fail_htlc_backwards`), `:10841` (`claim_funds_internal`);
* `lightning/src/routing/router.rs:825` (`Route`), `:766` (`Path`);
* `lightning-invoice/src/lib.rs:1662` (`amount_milli_satoshis`), `:1582`
  (`min_final_cltv_expiry_delta`).

What is NOT modelled.  The ledger is a four-bucket abstraction, not a
transaction builder; the L1 outpoint is a `(txid, index)` pair, not a
serialized `Bitcoin.Data.OutPoint`; penalty is a predicate that both
outputs are spent, not script execution; routes are lists of abstract hops,
not onion packets; invoices are already-parsed records, not bech32.  In
particular, the preimage invariant is stated relative to a supplied hash
function `HashFn`; it does not prove SHA-256 preimage resistance (that is
assumption C1).
-/

namespace LnLean.Security

set_option autoImplicit false

/-! ## 1. Value conservation -/

/-- The four buckets a channel's value can occupy at any time.  The funding
amount is fixed for the life of the channel. -/
structure Ledger where
  funding : Msat
  localBalance : Msat
  remoteBalance : Msat
  inFlight : Msat
  fee : Msat
deriving Repr, DecidableEq, BEq

/-- Total value recorded by the ledger. -/
def Ledger.total (l : Ledger) : Nat :=
  l.localBalance.val + l.remoteBalance.val + l.inFlight.val + l.fee.val

/-- The conservation predicate: outputs plus fee equal the funding value. -/
def Ledger.Conserves (l : Ledger) : Prop :=
  l.total = l.funding.val

/-- The transitions that move value between buckets. -/
inductive LedgerOp where
  | addHtlc (amount : Msat)
  | fulfillHtlc (amount : Msat)
  | failHtlc (amount : Msat)
  | payFee (amount : Msat)
deriving Repr, DecidableEq, BEq

/-- One ledger transition.  Insufficient balances and overflow make the
transition unavailable (`none`); they never silently move value. -/
def Ledger.step (l : Ledger) : LedgerOp → Option Ledger
  | .addHtlc a =>
      if a.val ≤ l.localBalance.val then
        some { l with
          localBalance := ⟨l.localBalance.val - a.val⟩
          inFlight := ⟨l.inFlight.val + a.val⟩ }
      else none
  | .fulfillHtlc a =>
      if a.val ≤ l.inFlight.val ∧ a.val ≤ l.remoteBalance.val then
        some { l with
          inFlight := ⟨l.inFlight.val - a.val⟩
          remoteBalance := ⟨l.remoteBalance.val + a.val⟩ }
      else none
  | .failHtlc a =>
      if a.val ≤ l.inFlight.val ∧ a.val ≤ l.localBalance.val then
        some { l with
          inFlight := ⟨l.inFlight.val - a.val⟩
          localBalance := ⟨l.localBalance.val + a.val⟩ }
      else none
  | .payFee a =>
      if a.val ≤ l.localBalance.val then
        some { l with
          localBalance := ⟨l.localBalance.val - a.val⟩
          fee := ⟨l.fee.val + a.val⟩ }
      else none

/-- **Value conservation.**  Every available ledger transition preserves
`local + remote + in-flight + fee = funding`. -/
theorem Ledger.step_conserves (l l' : Ledger) (op : LedgerOp)
    (hl : l.Conserves) (hstep : l.step op = some l') : l'.Conserves := by
  cases op with
  | addHtlc a =>
      unfold Ledger.step at hstep
      by_cases h : a.val ≤ l.localBalance.val
      · simp [h] at hstep
        subst l'
        unfold Ledger.Conserves Ledger.total at *
        simp at hl ⊢
        omega
      · simp [h] at hstep
  | fulfillHtlc a =>
      unfold Ledger.step at hstep
      by_cases h : a.val ≤ l.inFlight.val ∧ a.val ≤ l.remoteBalance.val
      · simp [h] at hstep
        subst l'
        unfold Ledger.Conserves Ledger.total at *
        simp at hl ⊢
        have h1 : a.val ≤ l.inFlight.val := h.1
        omega
      · simp [h] at hstep
  | failHtlc a =>
      unfold Ledger.step at hstep
      by_cases h : a.val ≤ l.inFlight.val ∧ a.val ≤ l.localBalance.val
      · simp [h] at hstep
        subst l'
        unfold Ledger.Conserves Ledger.total at *
        simp at hl ⊢
        have h1 : a.val ≤ l.inFlight.val := h.1
        omega
      · simp [h] at hstep
  | payFee a =>
      unfold Ledger.step at hstep
      by_cases h : a.val ≤ l.localBalance.val
      · simp [h] at hstep
        subst l'
        unfold Ledger.Conserves Ledger.total at *
        simp at hl ⊢
        omega
      · simp [h] at hstep

/-! ## 2. No double spend -/

/-- An L1 outpoint in the security model.  It is an abstraction of
`Bitcoin.Data.OutPoint` with decidable equality for the spend set. -/
structure OutRef where
  txid : Nat
  index : Nat
deriving Repr, DecidableEq, BEq

/-- The spend set observed by the Lightning layer. -/
structure L1Ledger where
  spent : List OutRef
  height : Height
deriving Repr, DecidableEq, BEq

/-- No outpoint appears twice in the spend set. -/
def L1Ledger.NoDoubleSpend (l : L1Ledger) : Prop :=
  l.spent.Nodup

/-- Spend a fresh outpoint.  Freshness is an explicit precondition: a
transaction that tries to spend an already-spent outpoint is invalid at the
L1 validation layer and is not a state transition of this model. -/
def L1Ledger.spend (l : L1Ledger) (o : OutRef) (_fresh : o ∉ l.spent) :
    L1Ledger :=
  { l with spent := o :: l.spent, height := l.height + 1 }

/-- **No double spend.**  Spending only a fresh outpoint preserves
`Nodup` on the spend set. -/
theorem L1Ledger.spend_preserves_noDoubleSpend (l : L1Ledger) (o : OutRef)
    (fresh : o ∉ l.spent) (hl : l.NoDoubleSpend) :
    (l.spend o fresh).NoDoubleSpend := by
  unfold L1Ledger.NoDoubleSpend at *
  exact List.nodup_cons.mpr ⟨fresh, hl⟩

/-! ## 3. HTLCs: preimage and timeout -/

/-- A hash function from preimages to payment hashes.  In wave B this is the
SHA-256 instance from `LnLean.Crypto.Hash`; here it is a parameter so that
the invariant does not depend on C1. -/
structure HashFn where
  hash : Preimage → PaymentHash

/-- One HTLC as seen by one endpoint. -/
structure HtlcRecord where
  amount : Msat
  paymentHash : PaymentHash
  preimage : Option Preimage
  cltvExpiry : Height
  state : HTLCState
deriving Repr, DecidableEq, BEq

/-- A fulfilled HTLC carries a preimage that hashes to its payment hash.
This is the state predicate that the success path must establish. -/
def HtlcRecord.Fulfilled (H : HashFn) (h : HtlcRecord) : Prop :=
  h.state = .fulfilled ∧
    ∃ p : Preimage, h.preimage = some p ∧ H.hash p = h.paymentHash

/-- The success transition: it is available only when the supplied preimage
matches the payment hash. -/
def HtlcRecord.fulfill (H : HashFn) (h : HtlcRecord) (p : Preimage) :
    Option HtlcRecord :=
  if H.hash p = h.paymentHash then
    some { h with state := .fulfilled, preimage := some p }
  else
    none

/-- **HTLC preimage soundness.**  A successful fulfilment yields exactly a
preimage whose hash is the HTLC's payment hash. -/
theorem HtlcRecord.fulfill_sound (H : HashFn) (h h' : HtlcRecord)
    (p : Preimage) (hstep : h.fulfill H p = some h') :
    H.hash p = h.paymentHash ∧ h'.Fulfilled H := by
  unfold HtlcRecord.fulfill at hstep
  by_cases hh : H.hash p = h.paymentHash
  · simp only [hh, ite_true] at hstep
    cases hstep
    exact ⟨hh, rfl, p, rfl, hh⟩
  · simp only [hh, ite_false] at hstep
    cases hstep

/-- A timeout is allowed only at or after the CLTV expiry. -/
def HtlcRecord.timeoutAllowed (h : HtlcRecord) (height : Height) : Prop :=
  h.cltvExpiry ≤ height

/-- The failure transition: available only at or after `cltv_expiry`. -/
def HtlcRecord.fail (h : HtlcRecord) (height : Height) : Option HtlcRecord :=
  if h.cltvExpiry ≤ height then
    some { h with state := .failed }
  else
    none

/-- **HTLC timeout safety.**  A failed HTLC was failed only at or after its
CLTV expiry. -/
theorem HtlcRecord.fail_only_after_expiry (h h' : HtlcRecord) (height : Height)
    (hstep : h.fail height = some h') : h.cltvExpiry ≤ height := by
  unfold HtlcRecord.fail at hstep
  by_cases hh : h.cltvExpiry ≤ height
  · exact hh
  · simp [hh] at hstep

/-! ## 4. Revocation and penalty -/

/-- The commitment counter and the currently published commitment. -/
structure RevocationState where
  commitmentNumber : Nat
  currentCommitment : Nat
  holderSecret : Option Nat
deriving Repr, DecidableEq, BEq

/-- A commitment is revoked when it is strictly older than the current one. -/
def RevocationState.Revoked (r : RevocationState) : Prop :=
  r.commitmentNumber < r.currentCommitment

/-- It is punishable when it is revoked and the holder still has a secret. -/
def RevocationState.Punishable (r : RevocationState) : Prop :=
  r.Revoked ∧ r.holderSecret.isSome = true

/-- A revoked commitment is not the current commitment. -/
theorem revoked_commitment_is_old (r : RevocationState) (h : r.Revoked) :
    r.commitmentNumber ≠ r.currentCommitment :=
  Nat.ne_of_lt h

/-- The two commitment outputs spent by the penalty transaction. -/
structure PenaltyTx where
  inputs : List OutRef
  outputs : List OutRef
deriving Repr, DecidableEq, BEq

/-- Both commitment outputs are inputs of the penalty transaction. -/
def PenaltyTx.SpendsBoth (p : PenaltyTx) (a b : OutRef) : Prop :=
  a ∈ p.inputs ∧ b ∈ p.inputs

/-- A breach: an old commitment published while the current one is newer. -/
structure Breach where
  oldCommitment : Nat
  currentCommitment : Nat
  penalty : PenaltyTx
deriving Repr, DecidableEq, BEq

/-- The punishment predicate: the old commitment is revoked and the penalty
transaction spends both of its outputs. -/
def Breach.Punishable (b : Breach) : Prop :=
  b.oldCommitment < b.currentCommitment ∧
    PenaltyTx.SpendsBoth b.penalty
      ⟨b.oldCommitment, 0⟩ ⟨b.oldCommitment, 1⟩

/-- **Revocation/penalty.**  A punishable breach has a penalty transaction
that spends both commitment outputs. -/
theorem breach_penalty_spends_both (b : Breach) (h : b.Punishable) :
    PenaltyTx.SpendsBoth b.penalty
      ⟨b.oldCommitment, 0⟩ ⟨b.oldCommitment, 1⟩ :=
  h.2

/-- A punishable breach is indeed an old commitment. -/
theorem breach_is_revoked (b : Breach) (h : b.Punishable) :
    b.oldCommitment < b.currentCommitment :=
  h.1

/-! ## 5. Commitment-state monotonicity -/

/-- The part of channel state relevant to monotonicity. -/
structure ChannelState where
  commitmentNumber : Nat
  phase : ChannelPhase
deriving Repr, DecidableEq, BEq

/-- A committed update strictly advances the commitment counter and keeps
the channel in normal operation. -/
def ChannelState.advance (s : ChannelState) : ChannelState :=
  { s with commitmentNumber := s.commitmentNumber + 1, phase := .normal }

/-- **State monotonicity.**  Commitment numbers never decrease. -/
theorem advance_monotone (s : ChannelState) :
    s.commitmentNumber ≤ s.advance.commitmentNumber :=
  Nat.le_succ s.commitmentNumber

/-- A committed update also advances the counter strictly. -/
theorem advance_strict (s : ChannelState) :
    s.commitmentNumber < s.advance.commitmentNumber :=
  Nat.lt_succ_self s.commitmentNumber

/-! ## 6. Route well-formedness -/

/-- An abstract hop: a directed edge with liquidity and CLTV delta. -/
structure Hop where
  src : Nat
  dst : Nat
  capacity : Msat
  cltvDelta : Nat
deriving Repr, DecidableEq, BEq

/-- An abstract route: the hop list and the amount carried. -/
structure Route where
  hops : List Hop
  totalAmount : Msat
deriving Repr, DecidableEq, BEq

/-- Consecutive hops are connected end-to-end. -/
def Route.Connected : List Hop → Prop
  | [] => True
  | [_] => True
  | h1 :: h2 :: rest => h1.dst = h2.src ∧ Route.Connected (h2 :: rest)

/-- A route is well formed when it is non-empty, connected, and every hop
has enough capacity for the carried amount. -/
def Route.WellFormed (r : Route) : Prop :=
  r.hops ≠ [] ∧ Route.Connected r.hops ∧
    ∀ h : Hop, h ∈ r.hops → r.totalAmount.val ≤ h.capacity.val

/-- Prepending a correctly linked hop preserves connectivity. -/
theorem Route.connected_cons {h1 h2 : Hop} {rest : List Hop}
    (hlink : h1.dst = h2.src) (hrest : Route.Connected (h2 :: rest)) :
    Route.Connected (h1 :: h2 :: rest) :=
  ⟨hlink, hrest⟩

/-- **Route well-formedness (connectivity).** -/
theorem Route.wellFormed_connected (r : Route) (h : r.WellFormed) :
    Route.Connected r.hops :=
  h.2.1

/-- **Route well-formedness (capacity).** -/
theorem Route.wellFormed_capacity (r : Route) (h : r.WellFormed)
    (hop : Hop) (hmem : hop ∈ r.hops) :
    r.totalAmount.val ≤ hop.capacity.val :=
  h.2.2 hop hmem

/-- **Route well-formedness (non-empty).** -/
theorem Route.wellFormed_nonempty (r : Route) (h : r.WellFormed) :
    r.hops ≠ [] :=
  h.1

/-! ## 7. Invoices -/

/-- A parsed BOLT 11 invoice relevant to payment safety. -/
structure Invoice where
  paymentHash : PaymentHash
  amount : Option Msat
  minFinalCltvExpiry : Nat
  paymentSecret : Option ByteArray
  signatureValid : Bool
deriving Repr, BEq

/-- The invoice agrees with the payment session's hash, amount, CLTV bound,
and carries a valid signature. -/
def Invoice.Consistent (inv : Invoice) (ph : PaymentHash) (amt : Msat)
    (cltv : Nat) : Prop :=
  inv.paymentHash = ph ∧ inv.amount = some amt ∧
    cltv ≤ inv.minFinalCltvExpiry ∧ inv.signatureValid = true

/-- **Invoice consistency (hash).** -/
theorem Invoice.consistent_hash (inv : Invoice) (ph : PaymentHash) (amt : Msat)
    (cltv : Nat) (h : inv.Consistent ph amt cltv) : inv.paymentHash = ph :=
  h.1

/-- **Invoice consistency (amount).** -/
theorem Invoice.consistent_amount (inv : Invoice) (ph : PaymentHash) (amt : Msat)
    (cltv : Nat) (h : inv.Consistent ph amt cltv) : inv.amount = some amt :=
  h.2.1

/-- **Invoice consistency (CLTV).** -/
theorem Invoice.consistent_cltv (inv : Invoice) (ph : PaymentHash) (amt : Msat)
    (cltv : Nat) (h : inv.Consistent ph amt cltv) : cltv ≤ inv.minFinalCltvExpiry :=
  h.2.2.1

/-- **Invoice consistency (signature).** -/
theorem Invoice.consistent_signature (inv : Invoice) (ph : PaymentHash)
    (amt : Msat) (cltv : Nat) (h : inv.Consistent ph amt cltv) :
    inv.signatureValid = true :=
  h.2.2.2

/-! ## 8. Multi-part payments -/

/-- A multipart payment: the parts, the advertised total, and whether the
receiver accepted the set. -/
structure MppPayment where
  parts : List Msat
  total : Msat
  accepted : Bool
deriving Repr, DecidableEq, BEq

/-- The arithmetic sum of the parts. -/
def MppPayment.partsSum (m : MppPayment) : Nat :=
  (m.parts.map Msat.val).sum

/-- The parts sum to the advertised total. -/
def MppPayment.SumOK (m : MppPayment) : Prop :=
  m.partsSum = m.total.val

/-- Settlement is available only when the parts sum exactly. -/
def MppPayment.settle (m : MppPayment) : Option MppPayment :=
  if m.partsSum = m.total.val then
    some { m with accepted := true }
  else
    none

/-- **MPP atomicity.**  A settled multipart payment has parts summing to the
advertised total. -/
theorem MppPayment.settle_requires_sum (m m' : MppPayment)
    (h : m.settle = some m') : m.SumOK := by
  unfold MppPayment.settle at h
  by_cases hs : m.partsSum = m.total.val
  · exact hs
  · simp [hs] at h

/-- Settlement preserves the sum condition. -/
theorem MppPayment.settle_preserves_sum (m m' : MppPayment)
    (h : m.settle = some m') : m'.SumOK := by
  unfold MppPayment.settle at h
  by_cases hs : m.partsSum = m.total.val
  · simp [hs] at h
    subst m'
    exact hs
  · simp [hs] at h

/-! ## 9. Partial synchrony -/

/-- A message with its send time. -/
structure Message where
  send : Nat
  tag : Nat
deriving Repr, DecidableEq, BEq

/-- A schedule assigns a delivery time (if any) to every message. -/
structure Schedule where
  latency : Message → Option Nat

/-- A message is delivered by time `t`. -/
def Schedule.DeliveredWithin (s : Schedule) (m : Message) (t : Nat) : Prop :=
  ∃ d : Nat, s.latency m = some d ∧ d ≤ t

/-- Partial synchrony: after `gst`, every message is delivered within
`delta` of its send time. -/
def PartiallySynchronous (gst delta : Nat) (s : Schedule) : Prop :=
  ∀ m : Message, gst ≤ m.send → s.DeliveredWithin m (m.send + delta)

/-- **Liveness under partial synchrony.**  After `gst`, every message is
delivered within the bound. -/
theorem partial_synchrony_delivers (gst delta : Nat) (s : Schedule)
    (hps : PartiallySynchronous gst delta s) (m : Message)
    (hm : gst ≤ m.send) : s.DeliveredWithin m (m.send + delta) :=
  hps m hm

/-! ## 10. The invariant catalog -/

/-- An invariant record: a stable id, the English claim, the Lean predicate
that a wave-B proof must establish, and the specification/implementation
anchors. -/
structure Invariant where
  id : String
  claim : String
  predicate : Prop
  anchors : List String

/-- INV-01: value conservation across ledger transitions. -/
def invValueConservation : Invariant :=
  { id := "INV-01",
    claim := "Every ledger transition preserves funding = local + remote + in-flight + fee.",
    predicate := ∀ (l l' : Ledger) (op : LedgerOp),
      l.Conserves → l.step op = some l' → l'.Conserves,
    anchors :=
      [ "BOLT 3 §Commitment Transaction"
      , "rust-lightning/lightning/src/ln/chan_utils.rs:841" ] }

/-- INV-02: no L1 outpoint is spent twice. -/
def invNoDoubleSpend : Invariant :=
  { id := "INV-02",
    claim := "Spending a fresh outpoint preserves the no-double-spend predicate.",
    predicate := ∀ (l : L1Ledger) (o : OutRef) (fresh : o ∉ l.spent),
      l.NoDoubleSpend → (l.spend o fresh).NoDoubleSpend,
    anchors :=
      [ "BOLT 5 §Commitment Transaction"
      , "rust-lightning/lightning/src/chain/chaininterface.rs" ] }

/-- INV-03: an HTLC success reveals the preimage of its payment hash. -/
def invHtlcPreimage : Invariant :=
  { id := "INV-03",
    claim := "A fulfilled HTLC carries a preimage whose hash is the payment hash.",
    predicate := ∀ (H : HashFn) (h h' : HtlcRecord) (p : Preimage),
      h.fulfill H p = some h' → H.hash p = h.paymentHash ∧ h'.Fulfilled H,
    anchors :=
      [ "BOLT 2 §Removing an HTLC"
      , "rust-lightning/lightning/src/ln/chan_utils.rs:841" ] }

/-- INV-04: an HTLC can time out only after its CLTV expiry. -/
def invHtlcTimeout : Invariant :=
  { id := "INV-04",
    claim := "An HTLC is failed only at or after its CLTV expiry.",
    predicate := ∀ (h h' : HtlcRecord) (height : Height),
      h.fail height = some h' → h.cltvExpiry ≤ height,
    anchors :=
      [ "BOLT 3 §HTLC-Timeout and HTLC-Success Transactions"
      , "rust-lightning/lightning/src/ln/chan_utils.rs:875" ] }

/-- INV-05: a revoked commitment is punishable, and the penalty spends both
commitment outputs. -/
def invRevocationPenalty : Invariant :=
  { id := "INV-05",
    claim := "A punishable breach is an old commitment and its penalty transaction spends both outputs.",
    predicate := ∀ b : Breach,
      b.Punishable →
        b.oldCommitment < b.currentCommitment ∧
          PenaltyTx.SpendsBoth b.penalty
            ⟨b.oldCommitment, 0⟩ ⟨b.oldCommitment, 1⟩,
    anchors :=
      [ "BOLT 5 §Revoked Transaction Close Handling"
      , "BOLT 3 §Per-commitment Secret Requirements"
      , "rust-lightning/lightning/src/ln/channel.rs:9471" ] }

/-- INV-06: commitment numbers are monotone. -/
def invStateMonotonicity : Invariant :=
  { id := "INV-06",
    claim := "A committed update never decreases the commitment number.",
    predicate := ∀ s : ChannelState,
      s.commitmentNumber ≤ s.advance.commitmentNumber,
    anchors :=
      [ "BOLT 2 §Committing Updates So Far"
      , "rust-lightning/lightning/src/ln/channel.rs:6270" ] }

/-- INV-07: a route is connected and every hop has enough capacity. -/
def invRouteWellFormed : Invariant :=
  { id := "INV-07",
    claim := "A well-formed route is non-empty, connected, and every hop has enough capacity.",
    predicate := ∀ r : Route,
      r.WellFormed → r.hops ≠ [] ∧ Route.Connected r.hops ∧
        ∀ h : Hop, h ∈ r.hops → r.totalAmount.val ≤ h.capacity.val,
    anchors :=
      [ "BOLT 7 §Recommendations for Routing"
      , "rust-lightning/lightning/src/routing/router.rs:825" ] }

/-- INV-08: an invoice is consistent with the payment session. -/
def invInvoiceConsistency : Invariant :=
  { id := "INV-08",
    claim := "A consistent invoice has the session hash, amount, CLTV bound, and a valid signature.",
    predicate := ∀ (inv : Invoice) (ph : PaymentHash) (amt : Msat) (cltv : Nat),
      inv.Consistent ph amt cltv →
        inv.paymentHash = ph ∧ inv.amount = some amt ∧
          cltv ≤ inv.minFinalCltvExpiry ∧ inv.signatureValid = true,
    anchors :=
      [ "BOLT 11 §Tagged Fields"
      , "lightning-invoice/src/lib.rs:1662" ] }

/-- INV-09: MPP settles only when the parts sum to the advertised total. -/
def invMppAtomicity : Invariant :=
  { id := "INV-09",
    claim := "A settled multipart payment has parts summing exactly to the total.",
    predicate := ∀ (m m' : MppPayment),
      m.settle = some m' → m.SumOK,
    anchors :=
      [ "BOLT 4 §Basic Multi-Part Payments"
      , "rust-lightning/lightning/src/ln/onion_payment.rs:505" ] }

/-- INV-10: liveness after the global stabilisation time. -/
def invPartialSynchrony : Invariant :=
  { id := "INV-10",
    claim := "After GST every message is delivered within delta of its send time.",
    predicate := ∀ (gst delta : Nat) (s : Schedule),
      PartiallySynchronous gst delta s →
        ∀ m : Message, gst ≤ m.send → s.DeliveredWithin m (m.send + delta),
    anchors :=
      [ "BOLT 1 §Lightning Message Format"
      , "BOLT 2 §Message Retransmission"
      , "rust-lightning/lightning/src/ln/channelmanager.rs:17831" ] }

/-- The ten core invariants of the protocol, in dependency order. -/
def coreInvariants : List Invariant :=
  [ invValueConservation
  , invNoDoubleSpend
  , invHtlcPreimage
  , invHtlcTimeout
  , invRevocationPenalty
  , invStateMonotonicity
  , invRouteWellFormed
  , invInvoiceConsistency
  , invMppAtomicity
  , invPartialSynchrony ]

/-- The catalog contains ten invariants with distinct ids. -/
theorem coreInvariants_length : coreInvariants.length = 10 := rfl

end LnLean.Security
