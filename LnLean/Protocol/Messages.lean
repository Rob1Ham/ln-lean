import LnLean.Basic.Core

/-!
# LnLean.Protocol.Messages

## English claim

This module gives a typed model of the seventeen BOLT 1/2 messages that the
scaffold's peer protocol uses.  Each constructor carries the fields that the
ordering and length laws need, `msgType` returns the BOLT message type, and
`wellFormed` is the decoder-acceptance predicate: a message is well formed
when its computed payload length fits BOLT 1's two-byte framing bound, its
channel identifiers and public keys have the required wire sizes, its
signatures are DER-sized, and its semantic side conditions hold.

## BOLT sections

* BOLT 1 §"Lightning Message Format" (`refs/bolts/01-messaging.md:43-92`):
  two-byte type, payload bounded by 65535 bytes.
* BOLT 1 §"The `init` Message" (`01-messaging.md:268-330`): type 16.
* BOLT 1 §"The `error` and `warning` Messages" (`01-messaging.md:345-420`):
  types 17 and 1.
* BOLT 1 §"The `ping` and `pong` Messages" (`01-messaging.md:422-505`):
  types 18 and 19, `num_pong_bytes < 65532`.
* BOLT 2 §"Channel Establishment v1" (`02-peer-protocol.md:629-1136`):
  `accept_channel` (33), `funding_created` (34), `funding_signed` (35),
  `channel_ready` (36).
* BOLT 2 §"Closing Initiation: `shutdown`" (`02-peer-protocol.md:2136-2192`)
  and §"Legacy Closing Negotiation: `closing_signed`"
  (`02-peer-protocol.md:2411-2520`): types 38 and 39.
* BOLT 2 §"Adding an HTLC" (`02-peer-protocol.md:2772-2840`),
  §"Removing an HTLC" (`02-peer-protocol.md:2913-2960`),
  §"Committing Updates So Far" (`02-peer-protocol.md:3097-3120`),
  §"Completing the Transition" (`02-peer-protocol.md:3206-3235`):
  types 128, 130, 131, 132, 133.
* BOLT 2 §"Message Retransmission" (`02-peer-protocol.md:3357-3405`):
  `channel_reestablish` type 136.

## rust-lightning anchors (commit fe49009)

* `lightning/src/ln/msgs.rs:111` `Init`; `:131` `ErrorMessage`; `:149`
  `WarningMessage`; `:166` `Ping`; `:179` `Pong`; `:371` `AcceptChannel`;
  `:403` `FundingCreated`; `:420` `FundingSigned`; `:431` `ChannelReady`;
  `:635` `Shutdown`; `:662` `ClosingSigned`; `:738` `UpdateAddHTLC`;
  `:820` `UpdateFulfillHTLC`; `:865` `UpdateFailHTLC`; `:893`
  `CommitmentSigned`; `:908` `RevokeAndACK`; `:939` `ChannelReestablish`.
* `lightning/src/ln/wire.rs:494` (`Init` type 16), `:498` (`error` 17),
  `:502` (`warning` 1), `:506` (`ping` 18), `:510` (`pong` 19), `:518`
  (`accept_channel` 33), `:522` (`funding_created` 34), `:526`
  (`funding_signed` 35), `:530` (`channel_ready` 36), `:534` (`shutdown`
  38), `:538` (`closing_signed` 39), `:615` (`update_add_htlc` 128), `:619`
  (`update_fulfill_htlc` 130), `:623` (`update_fail_htlc` 131), `:631`
  (`commitment_signed` 132), `:635` (`revoke_and_ack` 133), `:643`
  (`channel_reestablish` 136).

## What is NOT modelled

* `open_channel` / `open_channel2` are deliberately absent from `Msg`; the
  handshake model starts from `init` and takes the arrival of the opening
  message as the environment transition that enables `accept_channel`
  (`docs/ARCHITECTURE.md` lists the scaffold's two-party scope).
* TLV extension streams are not parsed.  Optional fields are represented by
  `Option` and their TLV overhead is included only where it affects lengths.
* Wire byte serialization is not bit-exact (charter §2).  The DER signature
  length is taken from the supplied bytes, not re-encoded.
* `channel_id` derivation by XOR of txid and output index is not computed;
  the identifier is an opaque 32-byte value with a size predicate.
* Signatures are not verified.  `wellFormed` only checks their length; the
  cryptographic assumptions C3/C4 live in `docs/ASSUMPTIONS.md`.
-/

namespace LnLean.Protocol

set_option autoImplicit false

open LnLean

/-! ## Message payload structures -/

/-- BOLT 1 `init` (type 16).  The `networks` and `remote_addr` TLVs are not
modelled. -/
structure InitMsg where
  globalfeatures : ByteArray := ByteArray.empty
  features : ByteArray := ByteArray.empty
deriving Repr, BEq

/-- BOLT 2 `accept_channel` (type 33).  Field names follow BOLT 2 verbatim
apart from Lean's lower camel case. -/
structure AcceptChannel where
  temporaryChannelId : ChannelId
  dustLimitSatoshis : Nat
  maxHtlcValueInFlightMsat : Nat
  channelReserveSatoshis : Nat
  htlcMinimumMsat : Nat
  minimumDepth : Nat
  toSelfDelay : Nat
  maxAcceptedHtlcs : Nat
  fundingPubKey : PubKey
  revocationBasepoint : PubKey
  paymentBasepoint : PubKey
  delayedPaymentBasepoint : PubKey
  htlcBasepoint : PubKey
  firstPerCommitmentPoint : PubKey
deriving Repr, BEq

/-- BOLT 2 `funding_created` (type 34). -/
structure FundingCreated where
  temporaryChannelId : ChannelId
  fundingTxid : ByteArray
  fundingOutputIndex : Nat
  signature : EcdsaSig
deriving Repr, BEq

/-- BOLT 2 `funding_signed` (type 35). -/
structure FundingSigned where
  channelId : ChannelId
  signature : EcdsaSig
deriving Repr, BEq

/-- BOLT 2 `channel_ready` (type 36).  `shortChannelIdAlias` is the optional
`alias` TLV. -/
structure ChannelReady where
  channelId : ChannelId
  secondPerCommitmentPoint : PubKey
  shortChannelIdAlias : Option Nat
deriving Repr, BEq

/-- BOLT 2 `shutdown` (type 38). -/
structure Shutdown where
  channelId : ChannelId
  scriptpubkey : ByteArray
deriving Repr, BEq

/-- BOLT 2 `closing_signed` (type 39).  `feeRange` is the optional
`closing_signed_tlvs` fee-range record. -/
structure ClosingSigned where
  channelId : ChannelId
  feeSatoshis : Nat
  signature : EcdsaSig
  feeRange : Option (Nat × Nat)
deriving Repr, BEq

/-- BOLT 2 `update_add_htlc` (type 128). -/
structure UpdateAddHtlc where
  channelId : ChannelId
  htlcId : Nat
  amountMsat : Msat
  paymentHash : PaymentHash
  cltvExpiry : Nat
  onionRoutingPacket : ByteArray
deriving Repr, BEq

/-- BOLT 2 `update_fulfill_htlc` (type 130). -/
structure UpdateFulfillHtlc where
  channelId : ChannelId
  htlcId : Nat
  paymentPreimage : Preimage
deriving Repr, BEq

/-- BOLT 2 `update_fail_htlc` (type 131). -/
structure UpdateFailHtlc where
  channelId : ChannelId
  htlcId : Nat
  reason : ByteArray
deriving Repr, BEq

/-- BOLT 2 `commitment_signed` (type 132). -/
structure CommitmentSigned where
  channelId : ChannelId
  signature : EcdsaSig
  htlcSignatures : List EcdsaSig
deriving Repr, BEq

/-- BOLT 2 `revoke_and_ack` (type 133). -/
structure RevokeAndAck where
  channelId : ChannelId
  perCommitmentSecret : ByteArray
  nextPerCommitmentPoint : PubKey
deriving Repr, BEq

/-- BOLT 2 `channel_reestablish` (type 136).  The four mandatory protocol
fields are named exactly as BOLT 2 names them; the `next_funding` and
`my_current_funding_locked` TLVs are not modelled. -/
structure ChannelReestablish where
  channelId : ChannelId
  nextCommitmentNumber : Nat
  nextRevocationNumber : Nat
  yourLastPerCommitmentSecret : ByteArray
  myCurrentPerCommitmentPoint : PubKey
deriving Repr, BEq

/-- BOLT 1 `ping` (type 18). -/
structure Ping where
  numPongBytes : Nat
  ignored : ByteArray
deriving Repr, BEq

/-- BOLT 1 `pong` (type 19). -/
structure Pong where
  ignored : ByteArray
deriving Repr, BEq

/-- BOLT 1 `error` (type 17). -/
structure ErrorMsg where
  channelId : ChannelId
  data : ByteArray
deriving Repr, BEq

/-- BOLT 1 `warning` (type 1). -/
structure WarningMsg where
  channelId : ChannelId
  data : ByteArray
deriving Repr, BEq

/-- The modelled wire message. -/
inductive Msg where
  | init (m : InitMsg)
  | acceptChannel (m : AcceptChannel)
  | fundingCreated (m : FundingCreated)
  | fundingSigned (m : FundingSigned)
  | channelReady (m : ChannelReady)
  | shutdown (m : Shutdown)
  | closingSigned (m : ClosingSigned)
  | updateAddHtlc (m : UpdateAddHtlc)
  | updateFulfillHtlc (m : UpdateFulfillHtlc)
  | updateFailHtlc (m : UpdateFailHtlc)
  | commitmentSigned (m : CommitmentSigned)
  | revokeAndAck (m : RevokeAndAck)
  | channelReestablish (m : ChannelReestablish)
  | ping (m : Ping)
  | pong (m : Pong)
  | error (m : ErrorMsg)
  | warning (m : WarningMsg)
deriving Repr, BEq

/-- Constructor tag of a message, forgetting payload data. -/
inductive MsgKind where
  | init
  | acceptChannel
  | fundingCreated
  | fundingSigned
  | channelReady
  | shutdown
  | closingSigned
  | updateAddHtlc
  | updateFulfillHtlc
  | updateFailHtlc
  | commitmentSigned
  | revokeAndAck
  | channelReestablish
  | ping
  | pong
  | error
  | warning
deriving Repr, DecidableEq, BEq, Inhabited

namespace Msg

/-- The constructor tag of a message. -/
def kind : Msg → MsgKind
  | .init _ => .init
  | .acceptChannel _ => .acceptChannel
  | .fundingCreated _ => .fundingCreated
  | .fundingSigned _ => .fundingSigned
  | .channelReady _ => .channelReady
  | .shutdown _ => .shutdown
  | .closingSigned _ => .closingSigned
  | .updateAddHtlc _ => .updateAddHtlc
  | .updateFulfillHtlc _ => .updateFulfillHtlc
  | .updateFailHtlc _ => .updateFailHtlc
  | .commitmentSigned _ => .commitmentSigned
  | .revokeAndAck _ => .revokeAndAck
  | .channelReestablish _ => .channelReestablish
  | .ping _ => .ping
  | .pong _ => .pong
  | .error _ => .error
  | .warning _ => .warning

end Msg

/-- BOLT wire type of a constructor.  These are the `Encode::TYPE`
constants from `lightning/src/ln/wire.rs`. -/
def wireType : MsgKind → Nat
  | .init => 16
  | .acceptChannel => 33
  | .fundingCreated => 34
  | .fundingSigned => 35
  | .channelReady => 36
  | .shutdown => 38
  | .closingSigned => 39
  | .updateAddHtlc => 128
  | .updateFulfillHtlc => 130
  | .updateFailHtlc => 131
  | .commitmentSigned => 132
  | .revokeAndAck => 133
  | .channelReestablish => 136
  | .ping => 18
  | .pong => 19
  | .error => 17
  | .warning => 1

/-- The BOLT message type of a message. -/
def msgType (m : Msg) : Nat := wireType m.kind

/-- Decode a wire type to its constructor.  `none` is an unknown type; the
model has no custom-message constructor. -/
def kindOfType? : Nat → Option MsgKind
  | 1 => some .warning
  | 16 => some .init
  | 17 => some .error
  | 18 => some .ping
  | 19 => some .pong
  | 33 => some .acceptChannel
  | 34 => some .fundingCreated
  | 35 => some .fundingSigned
  | 36 => some .channelReady
  | 38 => some .shutdown
  | 39 => some .closingSigned
  | 128 => some .updateAddHtlc
  | 130 => some .updateFulfillHtlc
  | 131 => some .updateFailHtlc
  | 132 => some .commitmentSigned
  | 133 => some .revokeAndAck
  | 136 => some .channelReestablish
  | _ => none

/-! ## Payload length -/

/-- Byte length of a DER signature as supplied.  BOLT 2's `signature` is a
DER-encoded ECDSA signature; the scaffold does not re-encode it. -/
def sigLen (s : EcdsaSig) : Nat := s.bytes.size

/-- Total bytes of a list of DER signatures. -/
def sigListLen (ss : List EcdsaSig) : Nat :=
  ss.foldl (fun acc s => acc + s.bytes.size) 0

/-- Computed payload length in bytes, excluding the two-byte type field.
Every constant is the sum of the fixed-width fields of the corresponding
BOLT message section; variable fields use their actual byte length. -/
def msgLength : Msg → Nat
  | .init m => 4 + m.globalfeatures.size + m.features.size
  | .acceptChannel _ => 270
  | .fundingCreated m => 66 + sigLen m.signature
  | .fundingSigned m => 32 + sigLen m.signature
  | .channelReady m => 65 + (match m.shortChannelIdAlias with | none => 0 | some _ => 10)
  | .shutdown m => 32 + m.scriptpubkey.size
  | .closingSigned m =>
      40 + sigLen m.signature + (match m.feeRange with | none => 0 | some _ => 18)
  | .updateAddHtlc m => 84 + m.onionRoutingPacket.size
  | .updateFulfillHtlc _ => 72
  | .updateFailHtlc m => 42 + m.reason.size
  | .commitmentSigned m => 34 + sigLen m.signature + sigListLen m.htlcSignatures
  | .revokeAndAck _ => 97
  | .channelReestablish _ => 113
  | .ping m => 4 + m.ignored.size
  | .pong m => 2 + m.ignored.size
  | .error m => 34 + m.data.size
  | .warning m => 34 + m.data.size

/-! ## Identifier and signature extraction -/

/-- The channel identifier carried by a message, if any.  `init`, `ping` and
`pong` are connection-level messages and carry none. -/
def channelId? : Msg → Option ChannelId
  | .init _ => none
  | .acceptChannel m => some m.temporaryChannelId
  | .fundingCreated m => some m.temporaryChannelId
  | .fundingSigned m => some m.channelId
  | .channelReady m => some m.channelId
  | .shutdown m => some m.channelId
  | .closingSigned m => some m.channelId
  | .updateAddHtlc m => some m.channelId
  | .updateFulfillHtlc m => some m.channelId
  | .updateFailHtlc m => some m.channelId
  | .commitmentSigned m => some m.channelId
  | .revokeAndAck m => some m.channelId
  | .channelReestablish m => some m.channelId
  | .ping _ => none
  | .pong _ => none
  | .error m => some m.channelId
  | .warning m => some m.channelId

/-- All public keys carried by a message. -/
def pubKeys : Msg → List PubKey
  | .acceptChannel m =>
      [m.fundingPubKey, m.revocationBasepoint, m.paymentBasepoint,
       m.delayedPaymentBasepoint, m.htlcBasepoint, m.firstPerCommitmentPoint]
  | .channelReady m => [m.secondPerCommitmentPoint]
  | .revokeAndAck m => [m.nextPerCommitmentPoint]
  | .channelReestablish m => [m.myCurrentPerCommitmentPoint]
  | _ => []

/-- All ECDSA signatures carried by a message. -/
def signatures : Msg → List EcdsaSig
  | .fundingCreated m => [m.signature]
  | .fundingSigned m => [m.signature]
  | .closingSigned m => [m.signature]
  | .commitmentSigned m => m.signature :: m.htlcSignatures
  | _ => []

/-- All-zero check for a 32-byte secret field (BOLT 2 requires the all-zero
value in `channel_reestablish` when `next_revocation_number` is zero). -/
def allZero (b : ByteArray) : Bool := b.toList.all (fun x => x == 0)

/-! ## Well-formedness -/

/-- 48-bit commitment-number bound from BOLT 2 §"Message Retransmission". -/
def TWO_POW_48 : Nat := 281474976710656

/-- Semantic side conditions that are not length or size constraints. -/
def semanticOk : Msg → Prop
  | .updateAddHtlc m =>
      0 < m.amountMsat.val ∧ m.cltvExpiry < 500000000 ∧
      m.onionRoutingPacket.size = 1366
  | .ping m => m.numPongBytes < 65532
  | .pong m => m.ignored.size ≤ 65533
  | .channelReestablish m =>
      m.nextCommitmentNumber < TWO_POW_48 ∧
      m.nextRevocationNumber < TWO_POW_48 ∧
      (m.nextRevocationNumber = 0 → allZero m.yourLastPerCommitmentSecret = true)
  | _ => True

/-- Channel ids have 32 bytes and every public key has 33 bytes. -/
def idsValid (m : Msg) : Prop :=
  (∀ c, channelId? m = some c → c.Valid) ∧
  (∀ p ∈ pubKeys m, p.Valid)

/-- Every DER signature is at most 73 bytes. -/
def sigsValid (m : Msg) : Prop :=
  ∀ s ∈ signatures m, s.bytes.size ≤ 73

/-- Decoder acceptance.  `msgLength m ≤ 65535` is BOLT 1's two-byte length
bound; the remaining conjuncts are the size and semantic checks. -/
def wellFormed (m : Msg) : Prop :=
  msgLength m ≤ 65535 ∧ idsValid m ∧ sigsValid m ∧ semanticOk m

/-! ## Small definitional lemmas -/

@[simp] theorem msgType_eq_wireType_kind (m : Msg) :
    msgType m = wireType m.kind := rfl

@[simp] theorem msgLength_ping (m : Ping) :
    msgLength (.ping m) = 4 + m.ignored.size := rfl

@[simp] theorem msgLength_pong (m : Pong) :
    msgLength (.pong m) = 2 + m.ignored.size := rfl

@[simp] theorem msgLength_acceptChannel (m : AcceptChannel) :
    msgLength (.acceptChannel m) = 270 := rfl

theorem msgLength_updateAddHtlc (m : UpdateAddHtlc)
    (h : m.onionRoutingPacket.size = 1366) :
    msgLength (.updateAddHtlc m) = 1450 := by
  simp [msgLength, h]

theorem wellFormed_length {m : Msg} (h : wellFormed m) :
    msgLength m ≤ 65535 := h.1

theorem wellFormed_channelId {m : Msg} {c : ChannelId}
    (h : wellFormed m) (hc : channelId? m = some c) : c.Valid :=
  h.2.1.1 c hc

theorem wellFormed_pubKey {m : Msg} {p : PubKey}
    (h : wellFormed m) (hp : p ∈ pubKeys m) : p.Valid :=
  h.2.1.2 p hp

theorem wellFormed_signature {m : Msg} {s : EcdsaSig}
    (h : wellFormed m) (hs : s ∈ signatures m) : s.bytes.size ≤ 73 :=
  h.2.2.1 s hs

end LnLean.Protocol
