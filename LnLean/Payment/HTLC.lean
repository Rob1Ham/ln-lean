import LnLean.Payment.Invoice

/-!
# LnLean.Payment.HTLC

English claim.  A Lightning payment is tracked as a session keyed by its
payment hash.  The session has a target amount in millisatoshis, a list of
parts (each carrying its amount, CLTV expiry, and per-part state), and a
coarse session state: `pending`, `succeeded`, or `failed`.  `settle` moves a
pending session to a terminal state once and only once; a terminal session is
absorbing, so settling again (with any outcome) cannot change it.  This is the
model of LDK's outbound payment state machine, reduced to the three states
that matter for the payment theorems.

BOLT sections.
* BOLT 2 `update_add_htlc` (amount, `payment_hash`, `cltv_expiry`) and
  `update_fulfill_htlc` / `update_fail_htlc` (terminal outcomes).
* BOLT 4 "Final Node" (payment hash lookup and fulfilment) and
  "Final Payload" (`amt_to_forward`, `outgoing_cltv_value`).
* BOLT 11 `p` field (the payment hash that keys the session).

BOLT line anchors (pinned BOLTs commit
1aadb719b4007c4cea0ba6e36b08c4fb53788dee).
* `refs/bolts/02-peer-protocol.md:2772-2790` `update_add_htlc`
  (`amount_msat`, `payment_hash`, `cltv_expiry`).
* `refs/bolts/02-peer-protocol.md:2921-2955` `update_fulfill_htlc` /
  `update_fail_htlc`.
* `refs/bolts/04-onion-routing.md:185-230` `payload` TLV types.
* `refs/bolts/04-onion-routing.md:355-410` HTLC-set requirements.
* `refs/bolts/04-onion-routing.md:1528-1545` final-node checks.
* `refs/bolts/11-payment-encoding.md:133-163` `p` tag.

rust-lightning anchors (commit fe4900930c6bd5786ec4203274d7cf312776a5a6).
* `lightning/src/ln/outbound_payment.rs:88` `PendingOutboundPayment`.
* `lightning/src/ln/outbound_payment.rs:124` `Retryable` carries
  `payment_hash`, `payment_secret`, `pending_amt_msat`, `total_msat`.
* `lightning/src/ln/outbound_payment.rs:164` `Fulfilled` terminal state.
* `lightning/src/ln/outbound_payment.rs:320` `mark_fulfilled`.
* `lightning/src/ln/outbound_payment.rs:333` `mark_abandoned`.
* `lightning/src/ln/outbound_payment.rs:505` `PaymentAttempts`.
* `lightning/src/ln/outbound_payment.rs:596` `PaymentSendFailure`.
* `lightning/src/ln/inbound_payment.rs:391` `verify` (payment hash/secret).
* `lightning/src/ln/inbound_payment.rs:506` `total_msat` lower bound.
* `lightning/src/ln/onion_payment.rs:329` `FinalOnionHopData` construction.

Not modelled.
* Channel-level HTLC scripts and revocation.  `PaymentPart` records the
  economic facts only; the channel machine is a separate module.
* Retry strategies, routing fees, and per-attempt failure reasons.  A part
  is abstractly `pending`/`succeeded`/`failed`.
* The preimage is not stored in the session.  `preimageCommits` is
  conditional on a SHA-256 function supplied by `LnLean.Crypto.Model` (C1).
* MPP composition and atomicity are in `LnLean.Payment.MPP`.
-/

namespace LnLean.Payment

set_option autoImplicit false

open LnLean

/-! ## States and parts -/

/-- Coarse payment state.  `pending` is the only non-terminal state. -/
inductive PaymentState where
  | pending
  | succeeded
  | failed
deriving Repr, DecidableEq, BEq, Inhabited

namespace PaymentState

/-- Terminal states cannot be left by `settle`. -/
def isTerminal : PaymentState → Prop
  | .pending => False
  | .succeeded => True
  | .failed => True

/-- The successful outcome. -/
def isSuccess : PaymentState → Prop
  | .succeeded => True
  | _ => False

theorem not_pending_of_terminal {s : PaymentState} (h : s.isTerminal) :
    s ≠ .pending := by
  cases s <;> simp [isTerminal] at h ⊢

end PaymentState

/-- One part of a payment.  `index` is the sender's part number, `amount` is
the part's `amt_to_forward`, and `cltvExpiry` is the absolute CLTV value in
the `update_add_htlc` that carries it. -/
structure PaymentPart where
  index : Nat
  amount : Msat
  cltvExpiry : Height
  state : PaymentState := .pending
deriving Repr, DecidableEq, BEq

/-- A payment session: the BOLT 11 payment hash, the total target, the parts
sent so far, and the session state. -/
structure PaymentSession where
  paymentHash : PaymentHash
  target : Msat
  parts : List PaymentPart
  state : PaymentState := .pending
deriving Repr

namespace PaymentSession

/-- Sum of the part amounts, in millisatoshis (as a `Nat` so that the
theorems do not need an overflow precondition). -/
def partAmountSum : PaymentSession → Nat
  | s => s.parts.foldl (fun acc p => acc + p.amount.val) 0

/-- Number of parts still awaiting an outcome. -/
def pendingPartCount (s : PaymentSession) : Nat :=
  (s.parts.filter (fun p => p.state == .pending)).length

/-- A session is settled successfully exactly when every part has succeeded
and the session itself is `succeeded`. -/
def allPartsSucceeded (s : PaymentSession) : Prop :=
  s.state = .succeeded ∧ ∀ p ∈ s.parts, p.state = .succeeded

/-- Conditional preimage relation for a session: the supplied hash of `pre`
is the session's payment hash.  The hash function is a parameter so that the
payment module does not depend on `LnLean.Crypto.Model` in wave A. -/
def preimageCommits (sha256 : Preimage → PaymentHash) (pre : Preimage)
    (s : PaymentSession) : Prop :=
  sha256 pre = s.paymentHash

/-- Settle a pending session to `outcome`.  A terminal session is absorbing:
the transition is a no-op, which is the model's idempotence property.  This
deliberately does not check the preimage; that is a channel/crypto premise,
recorded by `preimageCommits`. -/
def settle (s : PaymentSession) (outcome : PaymentState) : PaymentSession :=
  if s.state = .pending then { s with state := outcome } else s

/-- If the session is pending and the outcome is terminal, `settle` installs
that terminal state. -/
theorem settle_pending_terminal (s : PaymentSession) (outcome : PaymentState)
    (hs : s.state = .pending) (_ho : outcome.isTerminal) :
    (settle s outcome).state = outcome := by
  unfold settle
  simp [hs]

/-- Settling a terminal session changes nothing, for any requested outcome. -/
theorem settle_terminal (s : PaymentSession) (outcome : PaymentState)
    (hs : s.state.isTerminal) :
    settle s outcome = s := by
  have hne : s.state ≠ .pending := PaymentState.not_pending_of_terminal hs
  unfold settle
  simp [hne]

/-- The success constructor used by the payment layer. -/
def succeed (s : PaymentSession) : PaymentSession := settle s .succeeded

/-- The failure constructor used by the payment layer. -/
def fail (s : PaymentSession) : PaymentSession := settle s .failed

end PaymentSession

end LnLean.Payment
