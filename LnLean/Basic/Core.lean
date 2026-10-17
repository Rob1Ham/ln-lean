import Bitcoin.Data.Basic

/-!
# LnLean.Basic.Core

Shared, domain-neutral vocabulary for the Lightning model.

Everything that more than one workstream needs lives here.  Domain modules
must import this file rather than re-declaring amounts, identifiers, or
protocol error types.

Anchors:
* BOLT 1 (base protocol), BOLT 2 (channel establishment), BOLT 7 (gossip),
  BOLT 11 (invoices).
* `rust-lightning/lightning-types/src/lib.rs` (amounts, channel ids),
  `rust-lightning/lightning/src/ln/channelmanager.rs`.
-/

namespace LnLean

set_option autoImplicit false

/-! ## Amounts: millisatoshis -/

/-- A non-negative amount in millisatoshis.  Lightning's wire amounts are
`tu64` millisatoshis (BOLT 2, `update_add_htlc`); Bitcoin L1 amounts are
integer satoshis.  Keeping the unit in the type prevents the classic
1000x conversion bug. -/
structure Msat where
  val : Nat
deriving Repr, DecidableEq, BEq, Inhabited, Ord

namespace Msat

/-- `1 sat = 1000 msat`. -/
def MSAT_PER_SAT : Nat := 1000

/-- `1 BTC = 100_000_000 sat`. -/
def SAT_PER_BTC : Nat := 100000000

/-- The maximum representable amount: 21M BTC in msat. -/
def MAX : Msat := ⟨21000000 * SAT_PER_BTC * MSAT_PER_SAT⟩

def zero : Msat := ⟨0⟩

def ofSat (s : Nat) : Msat := ⟨s * MSAT_PER_SAT⟩

/-- Floor division to satoshis.  Commitment outputs are sat-denominated, so
the protocol always rounds *down* when converting an HTLC amount. -/
def toSatFloor (m : Msat) : Nat := m.val / MSAT_PER_SAT

/-- Ceiling division to satoshis (used only where the spec explicitly
requires rounding up, e.g. fee checks). -/
def toSatCeil (m : Msat) : Nat := (m.val + MSAT_PER_SAT - 1) / MSAT_PER_SAT

/-- Checked addition; `none` means the amount would exceed 21M BTC. -/
def add? (a b : Msat) : Option Msat :=
  let v := a.val + b.val
  if v ≤ MAX.val then some ⟨v⟩ else none

/-- Monotone subtraction; `none` means underflow. -/
def sub? (a b : Msat) : Option Msat :=
  if b.val ≤ a.val then some ⟨a.val - b.val⟩ else none

theorem ofSat_toSatFloor (s : Nat) : toSatFloor (ofSat s) = s := by
  simp [toSatFloor, ofSat, MSAT_PER_SAT]

theorem toSatFloor_mul_le (m : Msat) : toSatFloor m * MSAT_PER_SAT ≤ m.val := by
  simpa [toSatFloor, MSAT_PER_SAT] using Nat.div_mul_le_self m.val MSAT_PER_SAT

theorem toSatFloor_le (m : Msat) : toSatFloor m ≤ m.val := by
  have h := toSatFloor_mul_le m
  omega

theorem ofSat_injective {a b : Nat} (h : ofSat a = ofSat b) : a = b := by
  have := congrArg Msat.val h
  simpa [ofSat, MSAT_PER_SAT] using this

theorem add?_zero (a : Msat) : add? a zero = some a := by
  unfold add? zero MAX
  simp

theorem sub?_self (a : Msat) : sub? a a = some zero := by
  unfold sub? zero
  simp

end Msat

/-! ## Heights, times, and weights -/

/-- Block height. -/
abbrev Height := Nat

/-- Unix time in seconds. -/
abbrev Timestamp := Nat

/-- Relative timelock in blocks (`OP_CSV`). -/
abbrev Blocks := Nat

/-- A transaction weight in weight units (BIP 141). -/
structure Weight where
  val : Nat
deriving Repr, DecidableEq, BEq, Inhabited, Ord

/-- A feerate in millisatoshis per 1000 weight units.  BOLT 2 uses
`feerate_per_kw` as an integer. -/
structure FeeRate where
  msatPerKw : Nat
deriving Repr, DecidableEq, BEq, Inhabited

namespace FeeRate

/-- Fee for a transaction of the given weight, rounded up. -/
def fee (r : FeeRate) (w : Weight) : Msat :=
  ⟨(r.msatPerKw * w.val + 999) / 1000⟩

theorem fee_nonneg (r : FeeRate) (w : Weight) : 0 ≤ (fee r w).val :=
  Nat.zero_le _

end FeeRate

/-! ## Identifiers -/

/-- A 32-byte channel identifier.  BOLT 2: `channel_id` is the funding
txid (or a temporary id during negotiation). -/
structure ChannelId where
  bytes : ByteArray
deriving Repr, BEq

def ChannelId.Valid (c : ChannelId) : Prop := c.bytes.size = 32

def ChannelId.zero : ChannelId :=
  ⟨(List.replicate 32 (0 : UInt8)).toArray⟩

theorem ChannelId.zero_valid : ChannelId.zero.Valid := by
  simp [ChannelId.Valid, ChannelId.zero]

/-- BOLT 7 `short_channel_id`: 24 bits block, 24 bits tx index, 16 bits
output index, packed as `block << 40 | tx << 16 | output`. -/
structure ShortChannelId where
  block : Nat
  txIndex : Nat
  outputIndex : Nat
deriving Repr, DecidableEq, BEq, Inhabited

namespace ShortChannelId

def Valid (s : ShortChannelId) : Prop :=
  s.block < 16777216 ∧ s.txIndex < 16777216 ∧ s.outputIndex < 65536

/-- Packed wire representation (BOLT 7). -/
def toU64 (s : ShortChannelId) : Nat :=
  s.block * 1099511627776 + s.txIndex * 65536 + s.outputIndex

theorem toU64_lt_of_valid (s : ShortChannelId) (h : s.Valid) :
    s.toU64 < 281474976710656 := by
  rcases h with ⟨h1, h2, h3⟩
  unfold toU64
  omega

end ShortChannelId

/-- A compressed secp256k1 public key (33 bytes on the wire). -/
structure PubKey where
  bytes : ByteArray
deriving Repr, BEq

def PubKey.Valid (p : PubKey) : Prop := p.bytes.size = 33

/-- A 32-byte payment hash (`sha256(preimage)`). -/
structure PaymentHash where
  bytes : ByteArray
deriving Repr, BEq, DecidableEq

def PaymentHash.Valid (h : PaymentHash) : Prop := h.bytes.size = 32

/-- A 32-byte payment preimage. -/
structure Preimage where
  bytes : ByteArray
deriving Repr, BEq, DecidableEq

def Preimage.Valid (p : Preimage) : Prop := p.bytes.size = 32

/-- A 64-byte BIP 340 Schnorr signature. -/
structure SchnorrSig where
  bytes : ByteArray
deriving Repr, BEq

def SchnorrSig.Valid (s : SchnorrSig) : Prop := s.bytes.size = 64

/-- A DER-encoded ECDSA signature (BOLT 2 uses this on the wire). -/
structure EcdsaSig where
  bytes : ByteArray
deriving Repr, BEq

/-- A 32-byte chain hash (`genesis_block_hash`). -/
structure ChainHash where
  bytes : ByteArray
deriving Repr, BEq

def ChainHash.Valid (c : ChainHash) : Prop := c.bytes.size = 32

/-- The genesis hash used by the Bitcoin mainnet chain. -/
def ChainHash.bitcoinMainnet : ChainHash :=
  ⟨ByteArray.mk #[0x00,0x00,0x00,0x00,0x00,0x19,0xd6,0x68,
     0x9c,0x08,0x5a,0xe1,0x65,0x83,0x1e,0x93,
     0x4f,0xf7,0x63,0xae,0x46,0xa2,0xa6,0xc1,
     0x72,0xb3,0xf1,0xb6,0x0a,0x8c,0xe2,0x6f]⟩

/-! ## Direction and HTLC lifecycle -/

/-- From the point of view of one channel endpoint. -/
inductive Direction where
  | local
  | remote
deriving Repr, DecidableEq, BEq

def Direction.flip : Direction → Direction
  | .local => .remote
  | .remote => .local

@[simp] theorem Direction.flip_flip (d : Direction) : d.flip.flip = d := by
  cases d <;> rfl

/-- The state of one HTLC inside a commitment transaction.  `removed` is the
post-settlement state, kept distinct from `failed` so that proofs can talk
about outputs that no longer exist. -/
inductive HTLCState where
  | offered
  | received
  | fulfilled
  | failed
  | removed
deriving Repr, DecidableEq, BEq

/-- Coarse channel lifecycle (BOLT 2 + BOLT 3). -/
inductive ChannelPhase where
  | negotiating
  | awaitingLockin
  | normal
  | shuttingDown
  | closed
deriving Repr, DecidableEq, BEq

/-! ## Protocol results and errors -/

/-- BOLT 1 `error` / `warning` classes used by the scaffold. -/
inductive ErrorCode where
  | protocol
  | funding
  | update
  | permanentChannelFailure
  | temporaryChannelFailure
  | expiryTooSoon
  | amountBelowMinimum
  | feeInsufficient
  | incorrectCltvExpiry
  | unknownNextPeer
  | invalidOnion
  | invalidOnionHmac
  | invalidOnionKey
  | internal
deriving Repr, DecidableEq, BEq

structure ProtocolError where
  code : ErrorCode
  data : ByteArray := ByteArray.empty
deriving Repr

/-- A small result type with a Lightning error payload. -/
inductive Result (α : Type) where
  | ok (value : α)
  | error (err : ProtocolError)
deriving Repr

namespace Result

def isOk : Result α → Bool
  | .ok _ => true
  | .error _ => false

def map (f : α → β) : Result α → Result β
  | .ok a => .ok (f a)
  | .error e => .error e

theorem map_ok (f : α → β) (a : α) : map f (.ok a) = .ok (f a) := rfl

end Result

/-! ## Small arithmetic helpers used across domains -/

/-- `ceilDiv a b` for positive `b`. -/
def ceilDiv (a b : Nat) : Nat := (a + b - 1) / b

theorem ceilDiv_le_iff {a b c : Nat} (hb : 0 < b) :
    ceilDiv a b ≤ c ↔ a ≤ c * b := by
  unfold ceilDiv
  omega

end LnLean
