import LnLean.Basic.Core
import LnLean.Bitcoin.Seam

/-!
# LnLean.Channel.Types

English claim.  This module fixes the vocabulary of a single Lightning
channel as seen from one endpoint: the negotiated parameters, the two
endpoints, the satoshi balances, the HTLCs, the channel record with its
commitment counters and phase, the commitment transaction record, and the
pair of local/remote commitments.  It introduces no transition relation and
no arithmetic law; `State`, `Commitment`, `Fee`, and `Laws` build on it.

BOLT sections.
* BOLT 2 §2 (`open_channel` / `accept_channel` fields, lines 680-760 and
  907-960 of `02-peer-protocol.md` at the pinned BOLT commit): dust limit,
  channel reserve, `to_self_delay`, `max_htlc_value_in_flight_msat`,
  `htlc_minimum_msat`, and `feerate_per_kw`.
* BOLT 2 §3 (`commitment_signed`, `revoke_and_ack`, `shutdown`,
  `closing_signed`, lines 3097-3265 and 2136-2460).
* BOLT 3 §2 (`Commitment Transaction`, lines 83-353): the holder of a
  commitment transaction owns `to_local`; the counterparty owns
  `to_remote`; each party's `to_local` output is CSV-delayed by the
  counterparty's `to_self_delay`.

rust-lightning anchors at `fe4900930c6bd5786ec4203274d7cf312776a5a6`.
* `lightning/src/ln/channel.rs:1546` (`struct Channel`), `:1552`
  (`enum ChannelPhase`), `:799` (`enum ChannelState`), `:725-731`
  (local/remote shutdown flags), `:1546-1610` (channel context accessors).
* `lightning/src/ln/chan_utils.rs:1614` (`struct CommitmentTransaction`),
  `:1713` (`CommitmentTransaction::new`), `:1887-1945`
  (`insert_non_htlc_outputs`: anchors and zero-value output trimming).
* `lightning/src/ln/channelmanager.rs:1-120` (module imports; the manager
  owns channels but no state record is defined here).

What is NOT modelled.
* Wire encoding of the BOLT messages, signatures, and per-commitment
  secrets (the `Wire`, `Crypto`, and `Revocation` workstreams own those).
* Transaction construction and script bytes (`LnLean.Bitcoin.Seam` owns the
  script templates; `Commitment` here is value arithmetic only).
* Multi-party channels, splicing, dual funding, zero-fee commitments, and
  Taproot-native channels.
* The lifetime of an individual HTLC (add/fulfil/fail/timeout) is the HTLC
  workstream; here an HTLC is a record and a state tag.
-/

namespace LnLean.Channel

set_option autoImplicit false

open LnLean

/-! ## Funding outpoint -/

/-- A Lightning funding outpoint, kept in a form with decidable equality so
that channel records can be compared.  BOLT 2 uses the funding txid and the
output index directly; `toL1` bridges to the `btc-lean` `OutPoint` in
`LnLean.Bitcoin.Seam`. -/
structure FundingOutpoint where
  txid : ByteArray
  index : Nat
deriving Repr, DecidableEq, BEq

/-- The L1 outpoint spent by every commitment transaction. -/
def FundingOutpoint.toL1 (f : FundingOutpoint) : Bitcoin.OutPoint :=
  Bitcoin.fundingOutpoint f.txid f.index

theorem FundingOutpoint.toL1_index (f : FundingOutpoint) :
    (f.toL1).n = f.index.toUInt32 := rfl

/-! ## Negotiated parameters (BOLT 2 §2) -/

/-- The parameters one endpoint advertises in `open_channel` /
`accept_channel`.  Amounts are satoshis because BOLT 2 carries
`dust_limit_satoshis` and `channel_reserve_satoshis` as `u64` sat values;
the HTLC bounds are `Msat` because BOLT 2 carries them as millisatoshis. -/
structure ChannelParams where
  /-- `dust_limit_satoshis`: outputs below this are trimmed. -/
  dustLimitSat : Nat
  /-- `channel_reserve_satoshis`: the minimum balance kept on this side. -/
  channelReserveSat : Nat
  /-- `to_self_delay`: CSV blocks imposed on the *other* side's `to_local`. -/
  toSelfDelay : Nat
  /-- `max_htlc_value_in_flight_msat`. -/
  maxHtlcValue : Msat
  /-- `htlc_minimum_msat`. -/
  htlcMinimum : Msat
  /-- `feerate_per_kw`, in millisatoshis per 1000 weight units. -/
  feerate : FeeRate
  /-- `option_anchors` negotiated for this channel. -/
  anchorOutputs : Bool
deriving Repr, DecidableEq, BEq

/-- The dust limit as an L1 amount. -/
def ChannelParams.dustLimitAmount (p : ChannelParams) : Bitcoin.BtcAmount :=
  (p.dustLimitSat : Int)

/-- The reserve as an L1 amount. -/
def ChannelParams.reserveAmount (p : ChannelParams) : Bitcoin.BtcAmount :=
  (p.channelReserveSat : Int)

/-- BOLT 2 requires `channel_reserve_satoshis >= dust_limit_satoshis`; this
is the predicate that both the opener and the accepter must satisfy. -/
def ChannelParams.ReserveAtLeastDust (p : ChannelParams) : Prop :=
  p.dustLimitSat ≤ p.channelReserveSat

/-! ## Endpoints -/

/-- One side of a channel.  The key fields are present because commitment
key derivation and `to_remote` scripts need them; key *derivation* and
signature checking are not modelled here. -/
structure Endpoint where
  nodeId : PubKey
  fundingPubKey : PubKey
  paymentBasepoint : PubKey
  delayedPaymentBasepoint : PubKey
  params : ChannelParams
deriving Repr

/-! ## Balances and HTLCs -/

/-- The two off-chain balances from the local endpoint's point of view. -/
structure Balance where
  localBalance : Msat
  remoteBalance : Msat
deriving Repr, DecidableEq, BEq

/-- Local balance in whole satoshis, rounded down (BOLT 3 §2 requires
commitment output amounts to be whole satoshis). -/
def Balance.localSat (b : Balance) : Nat := b.localBalance.toSatFloor

/-- Remote balance in whole satoshis, rounded down. -/
def Balance.remoteSat (b : Balance) : Nat := b.remoteBalance.toSatFloor

/-- Total off-chain value. -/
def Balance.total (b : Balance) : Msat := ⟨b.localBalance.val + b.remoteBalance.val⟩

theorem Balance.total_val (b : Balance) : b.total.val = b.localBalance.val + b.remoteBalance.val := rfl

/-- An HTLC as it appears in the channel state.  `direction` is relative to
the local endpoint: `local` means the local node offered it. -/
structure HTLC where
  direction : Direction
  amount : Msat
  paymentHash : PaymentHash
  cltvExpiry : Height
  state : HTLCState
deriving Repr, BEq

/-- An HTLC is still part of the commitment if it has not been removed. -/
def HTLC.isPending (h : HTLC) : Prop :=
  h.state = HTLCState.offered ∨ h.state = HTLCState.received

/-- The satoshi value of an HTLC after BOLT 3 rounding. -/
def HTLC.amountSat (h : HTLC) : Nat := h.amount.toSatFloor

/-! ## The channel record -/

/-- A channel from the local endpoint's perspective.  The phase lives in
`LnLean.ChannelPhase` (`Basic.Core`); the transition relation is in
`State.lean`, deliberately not a Boolean `reject` function. -/
structure Channel where
  channelId : ChannelId
  funding : FundingOutpoint
  fundingValue : Msat
  localEndpoint : Endpoint
  remoteEndpoint : Endpoint
  phase : ChannelPhase
  /-- Counter for the commitment transaction the local node would broadcast. -/
  localCommitmentNumber : Nat
  /-- Counter for the commitment transaction the remote node would broadcast. -/
  remoteCommitmentNumber : Nat
  balance : Balance
  htlcs : List HTLC
deriving Repr

/-- The funding value in satoshis (floor; BOLT 3 works in satoshis). -/
def Channel.fundingValueSat (c : Channel) : Nat := c.fundingValue.toSatFloor

/-! ## Commitment transaction records -/

/-- An HTLC output that survives trimming on a commitment transaction. -/
structure CommitmentHTLCOutput where
  direction : Direction
  amountSat : Nat
  cltvExpiry : Height
  state : HTLCState
deriving Repr, DecidableEq, BEq

/-- The BOLT 3 anchor output value: 330 satoshis per anchor. -/
def anchorOutputSat : Nat := 330

theorem anchorOutputSat_eq : anchorOutputSat = 330 := rfl

/-- The non-HTLC outputs of a commitment transaction.  Values are in
satoshis; a zero-valued output is not emitted (BOLT 3 trims to dust). -/
inductive CommitmentOutput where
  | toLocal (valueSat : Nat)
  | toRemote (valueSat : Nat)
  | htlc (direction : Direction) (valueSat : Nat)
  | localAnchor
  | remoteAnchor
deriving Repr, DecidableEq, BEq

/-- The satoshi value carried by one commitment output. -/
def CommitmentOutput.value : CommitmentOutput → Nat
  | .toLocal v => v
  | .toRemote v => v
  | .htlc _ v => v
  | .localAnchor => anchorOutputSat
  | .remoteAnchor => anchorOutputSat

/-- A commitment transaction record.  `holder` is the party that broadcasts
it, so `toLocal` is the holder's output (BOLT 3 names the holder "local").
`contestDelay` is the CSV delay on that output: it is the *counterparty's*
`to_self_delay`, which is the source of the local/remote asymmetry. -/
structure Commitment where
  holder : Direction
  commitmentNumber : Nat
  fundingValueSat : Nat
  toLocalSat : Nat
  toRemoteSat : Nat
  htlcs : List CommitmentHTLCOutput
  feeSat : Nat
  contestDelay : Nat
  anchorOutputs : Bool
deriving Repr, DecidableEq, BEq

/-- Both commitment transactions of the channel. -/
structure CommitmentPair where
  localCommitment : Commitment
  remoteCommitment : Commitment
deriving Repr, DecidableEq, BEq

end LnLean.Channel
