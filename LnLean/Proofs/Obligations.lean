import LnLean.Basic.Core
import LnLean.Bitcoin.Seam

/-!
# LnLean.Proofs.Obligations

English claim.  This module is the machine-readable obligation catalog: one
record for every property the scaffold commits to tracking.  It does not
prove the obligations.  A record whose `status` is `.proved` names a theorem
that exists in this tree (`LnLean.Security.Invariants`, or a wave-D/wave-E
module such as `LnLean.Proofs.WaveD.D14`); every other record is
`.statementOnly` and names the declaration that wave B must add.  The catalog covers all eight
domains: L1 seam, crypto/wire, channel/commitment, HTLC/revocation, peer
protocol, routing/onion, payments, and security/liveness.

BOLT sections.  BOLT 1--5, 7, 9, 11 (and the keysend extension noted where
applicable).

`rust-lightning` anchors at commit `fe49009` (every row also carries its own
`path:line`): `lightning/src/ln/channel.rs:8370` (`update_add_htlc`),
`lightning/src/ln/channelmanager.rs:10210` (`claim_funds`),
`lightning/src/ln/chan_utils.rs:841` (`get_htlc_redeemscript`),
`lightning/src/ln/onion_payment.rs:505` (`peel_payment_onion`),
`lightning/src/routing/gossip.rs:906` (`ChannelUpdateInfo`),
`lightning/src/routing/router.rs:825` (`Route`),
`lightning-invoice/src/lib.rs:1662` (`amount_milli_satoshis`), plus
`chain/channelmonitor.rs:5079` and `util/ser.rs:442` where the property is
outside the listed hot files.

What is NOT modelled.  Obligation records are metadata, not proofs.  A
`.statementOnly` row is a promise about a future declaration; the string in
`leanTarget` is deliberately not resolved by Lean, so a stale target cannot
make this file fail to build.  `docs/THEOREM-INDEX.md` and
`docs/TRACEABILITY.md` are generated from this list by hand and must be kept
in sync; `obligations_length` only checks the row count.
-/

namespace LnLean.Proofs

set_option autoImplicit false

/-- The eight work domains of the scaffold. -/
inductive Domain where
  | l1
  | cryptoWire
  | channel
  | htlcRevocation
  | protocol
  | routing
  | payment
  | security
deriving Repr, DecidableEq, BEq

/-- `proved` means a theorem with the named target exists in the tree.
`statementOnly` means no theorem exists yet; the claim is tracked in the
index and traceability tables. -/
inductive ObligationStatus where
  | proved
  | statementOnly
deriving Repr, DecidableEq, BEq

/-- One tracked obligation.  `leanTarget` is a human-readable fully
qualified declaration name (existing or planned); `boltdoc` names the BOLT
section; `rlAnchor` is a `path:line` anchor at the pinned rust-lightning
commit.  `UNANCHORED` is used only when no real location exists. -/
structure Obligation where
  id : String
  domain : Domain
  claim : String
  leanTarget : String
  status : ObligationStatus
  boltdoc : String
  rlAnchor : String
deriving Repr, DecidableEq, BEq

/-- The 48-obligation catalog: six entries per domain. -/
def obligations : List Obligation :=
  [
  -- Foundations / L1 (6)
  { id := "LN-L1-001", domain := .l1,
    claim := "The funding output is P2WSH over the 2-of-2 funding witness script.",
    leanTarget := "LnLean.Bitcoin.fundingScriptPubKey",
    status := .statementOnly,
    boltdoc := "BOLT 2 §Channel Establishment v1; BOLT 3 §Funding Transaction Output",
    rlAnchor := "lightning/src/ln/chan_utils.rs:847" },
  { id := "LN-L1-002", domain := .l1,
    claim := "If the seam MoneyRange predicate holds for a funding output, the btc-lean L1 MoneyRange predicate holds.",
    leanTarget := "LnLean.Bitcoin.fundingOutput_moneyRange",
    status := .proved,
    boltdoc := "BOLT 2 §The open_channel Message",
    rlAnchor := "lightning/src/ln/channel.rs:2683" },
  { id := "LN-L1-003", domain := .l1,
    claim := "Channel safety is preserved for reorgs within the adversary's depth budget, and deep reorgs are a separate failure mode.",
    leanTarget := "LnLean.Security.Adversary.reorgAllowed",
    status := .statementOnly,
    boltdoc := "BOLT 5 §Commitment Transaction",
    rlAnchor := "lightning/src/chain/channelmonitor.rs:514" },
  { id := "LN-L1-004", domain := .l1,
    claim := "The to_local commitment output carries the CSV contest delay and the revocation key.",
    leanTarget := "LnLean.Bitcoin.toLocalScript",
    status := .statementOnly,
    boltdoc := "BOLT 3 §to_local Output",
    rlAnchor := "lightning/src/ln/chan_utils.rs:687" },
  { id := "LN-L1-005", domain := .l1,
    claim := "An anchor output is worth exactly 330 satoshis.",
    leanTarget := "LnLean.Bitcoin.anchorValue_eq",
    status := .proved,
    boltdoc := "BOLT 3 §to_local_anchor and to_remote_anchor Output",
    rlAnchor := "lightning/src/ln/channel.rs:989" },
  { id := "LN-L1-006", domain := .l1,
    claim := "The commitment base weight is the BOLT 3 constant 724 before HTLC outputs.",
    leanTarget := "LnLean.Bitcoin.commitmentBaseWeight",
    status := .statementOnly,
    boltdoc := "BOLT 3 §Expected Weight of the Commitment Transaction",
    rlAnchor := "lightning/src/ln/chan_utils.rs:281" },

  -- Crypto / wire (6)
  { id := "LN-CR-001", domain := .cryptoWire,
    claim := "Payment hashes are SHA-256 outputs, relying on assumption C1 (collision and preimage resistance).",
    leanTarget := "LnLean.Crypto.Hash.sha256",
    status := .statementOnly,
    boltdoc := "BOLT 2 §Adding an HTLC",
    rlAnchor := "lightning/src/ln/channel.rs:8370" },
  { id := "LN-CR-002", domain := .cryptoWire,
    claim := "Commitment signatures verify under the counterparty funding key, relying on assumption C3 (ECDSA EUF-CMA).",
    leanTarget := "LnLean.Crypto.Sig.ecdsaVerify",
    status := .statementOnly,
    boltdoc := "BOLT 3 §Commitment Transaction Construction",
    rlAnchor := "lightning/src/ln/chan_utils.rs:1450" },
  { id := "LN-CR-003", domain := .cryptoWire,
    claim := "Onion integrity checks are HMAC-SHA256 tags, relying on assumption C8 (HMAC PRF).",
    leanTarget := "LnLean.Crypto.Hash.hmacSha256",
    status := .statementOnly,
    boltdoc := "BOLT 4 §Packet Structure",
    rlAnchor := "lightning/src/ln/onion_payment.rs:505" },
  { id := "LN-CR-004", domain := .cryptoWire,
    claim := "BigSize encoding and decoding are inverse on canonical encodings.",
    leanTarget := "LnLean.Wire.decode_encode",
    status := .proved,
    boltdoc := "BOLT 1 §Fundamental Types; BOLT 1 Appendix A",
    rlAnchor := "lightning/src/util/ser.rs:442" },
  { id := "LN-CR-005", domain := .cryptoWire,
    claim := "A TLV stream is strictly sorted by type and has no duplicate types.",
    leanTarget := "LnLean.Wire.TLVStream.WellFormed",
    status := .statementOnly,
    boltdoc := "BOLT 1 §Type-Length-Value Format",
    rlAnchor := "lightning/src/util/ser.rs:369" },
  { id := "LN-CR-006", domain := .cryptoWire,
    claim := "A Lightning message frame's declared length matches the payload actually consumed.",
    leanTarget := "LnLean.Wire.Message.decode_length",
    status := .statementOnly,
    boltdoc := "BOLT 1 §Lightning Message Format",
    rlAnchor := "lightning/src/ln/peer_handler.rs:331" },

  -- Channel / commitment (6)
  { id := "LN-CH-001", domain := .channel,
    claim := "Every ledger transition preserves funding = local + remote + in-flight + fee.",
    leanTarget := "LnLean.Security.Ledger.step_conserves",
    status := .proved,
    boltdoc := "BOLT 3 §Commitment Transaction",
    rlAnchor := "lightning/src/ln/chan_utils.rs:716" },
  { id := "LN-CH-002", domain := .channel,
    claim := "No commitment output has a negative value and the output sum stays within the funding value.",
    leanTarget := "LnLean.Channel.Commitment.outputs_nonnegative",
    status := .statementOnly,
    boltdoc := "BOLT 3 §Commitment Transaction Outputs",
    rlAnchor := "lightning/src/ln/chan_utils.rs:1908" },
  { id := "LN-CH-003", domain := .channel,
    claim := "Commitment outputs are ordered by value then script, and dust HTLCs are trimmed.",
    leanTarget := "LnLean.Channel.Commitment.output_ordering",
    status := .statementOnly,
    boltdoc := "BOLT 3 §Transaction Output Ordering; BOLT 3 §Trimmed Outputs",
    rlAnchor := "lightning/src/ln/chan_utils.rs:1985" },
  { id := "LN-CH-004", domain := .channel,
    claim := "A committed update never decreases the commitment number.",
    leanTarget := "LnLean.Security.advance_monotone",
    status := .proved,
    boltdoc := "BOLT 2 §Committing Updates So Far",
    rlAnchor := "lightning/src/ln/channel.rs:6270" },
  { id := "LN-CH-005", domain := .channel,
    claim := "A commitment with an insufficient feerate for its weight is rejected before signing.",
    leanTarget := "LnLean.Channel.Fee.feeInsufficient",
    status := .statementOnly,
    boltdoc := "BOLT 3 §Fees; BOLT 5 §Commitment Transaction",
    rlAnchor := "lightning/src/ln/channel.rs:3721" },
  { id := "LN-CH-006", domain := .channel,
    claim := "HTLC exposure and channel reserve bounds are respected by admissible updates.",
    leanTarget := "LnLean.Channel.Reserve.bounds",
    status := .proved,
    boltdoc := "BOLT 2 §Bounding exposure to trimmed in-flight HTLCs",
    rlAnchor := "lightning/src/ln/channel.rs:4223" },

  -- HTLC / revocation (6)
  { id := "LN-HT-001", domain := .htlcRevocation,
    claim := "A fulfilled HTLC carries a preimage whose hash is the payment hash.",
    leanTarget := "LnLean.Security.HtlcRecord.fulfill_sound",
    status := .proved,
    boltdoc := "BOLT 2 §Removing an HTLC",
    rlAnchor := "lightning/src/ln/channel.rs:8640; lightning/src/ln/chan_utils.rs:841" },
  { id := "LN-HT-002", domain := .htlcRevocation,
    claim := "An HTLC is failed only at or after its CLTV expiry.",
    leanTarget := "LnLean.Security.HtlcRecord.fail_only_after_expiry",
    status := .proved,
    boltdoc := "BOLT 3 §HTLC-Timeout and HTLC-Success Transactions",
    rlAnchor := "lightning/src/ln/chan_utils.rs:875; lightning/src/ln/channel.rs:8671" },
  { id := "LN-HT-003", domain := .htlcRevocation,
    claim := "Offered, received, and trimmed HTLC amounts plus balances and fee equal the funding value.",
    leanTarget := "LnLean.Channel.HTLC.amount_conservation",
    status := .statementOnly,
    boltdoc := "BOLT 2 §Adding an HTLC",
    rlAnchor := "lightning/src/ln/chan_utils.rs:716" },
  { id := "LN-HT-004", domain := .htlcRevocation,
    claim := "An HTLC id is unique within the live HTLC set of a channel.",
    leanTarget := "LnLean.Channel.HTLC.id_unique",
    status := .statementOnly,
    boltdoc := "BOLT 2 §Adding an HTLC",
    rlAnchor := "lightning/src/ln/channel.rs:8370" },
  { id := "LN-HT-005", domain := .htlcRevocation,
    claim := "A revoked commitment is strictly older than the current commitment and cannot be the current one.",
    leanTarget := "LnLean.Security.revoked_commitment_is_old",
    status := .proved,
    boltdoc := "BOLT 3 §Per-commitment Secret Requirements",
    rlAnchor := "lightning/src/ln/chan_utils.rs:518" },
  { id := "LN-HT-006", domain := .htlcRevocation,
    claim := "A punishable breach has a penalty transaction that spends both commitment outputs.",
    leanTarget := "LnLean.Security.breach_penalty_spends_both",
    status := .proved,
    boltdoc := "BOLT 5 §Revoked Transaction Close Handling",
    rlAnchor := "lightning/src/ln/channel.rs:9471; lightning/src/chain/channelmonitor.rs:5079" },

  -- Protocol / peer (6)
  { id := "LN-PR-001", domain := .protocol,
    claim := "open_channel accepts a funding amount only above the dust and minimum-channel bounds.",
    leanTarget := "LnLean.Protocol.Handshake.open_bounds",
    status := .statementOnly,
    boltdoc := "BOLT 2 §The open_channel Message",
    rlAnchor := "lightning/src/ln/channelmanager.rs:17521" },
  { id := "LN-PR-002", domain := .protocol,
    claim := "The channel enters normal operation only after both channel_ready messages.",
    leanTarget := "LnLean.Protocol.Handshake.channel_ready_gate",
    status := .proved,
    boltdoc := "BOLT 2 §The channel_ready Message",
    rlAnchor := "lightning/src/ln/channelmanager.rs:17614" },
  { id := "LN-PR-003", domain := .protocol,
    claim := "funding_signed carries a valid signature over the funding transaction.",
    leanTarget := "LnLean.Protocol.Handshake.funding_signed_valid",
    status := .statementOnly,
    boltdoc := "BOLT 2 §The funding_signed Message",
    rlAnchor := "lightning/src/ln/channel.rs:2107" },
  { id := "LN-PR-004", domain := .protocol,
    claim := "commitment_signed covers exactly the current HTLC set and fee.",
    leanTarget := "LnLean.Protocol.Messages.commitment_signed_covers",
    status := .statementOnly,
    boltdoc := "BOLT 2 §Committing Updates So Far",
    rlAnchor := "lightning/src/ln/channel.rs:2386; lightning/src/ln/channel.rs:6270" },
  { id := "LN-PR-005", domain := .protocol,
    claim := "channel_reestablish retransmits unacknowledged updates without rolling state back.",
    leanTarget := "LnLean.Protocol.Peer.reestablish_no_rollback",
    status := .statementOnly,
    boltdoc := "BOLT 2 §Message Retransmission",
    rlAnchor := "lightning/src/ln/channelmanager.rs:17831; lightning/src/ln/channel.rs:10826" },
  { id := "LN-PR-006", domain := .protocol,
    claim := "Negotiated channel features are the intersection of both peers' supported features.",
    leanTarget := "LnLean.Protocol.Handshake.feature_intersection",
    status := .statementOnly,
    boltdoc := "BOLT 9 §Features; BOLT 2 §Defined Channel Types",
    rlAnchor := "lightning/src/ln/channel.rs:4702" },

  -- Routing / onion (6)
  { id := "LN-RT-001", domain := .routing,
    claim := "A well-formed route is non-empty, connected end-to-end, and every hop has enough capacity.",
    leanTarget := "LnLean.Security.Route.wellFormed_connected; LnLean.Security.Route.wellFormed_capacity; LnLean.Security.Route.wellFormed_nonempty",
    status := .proved,
    boltdoc := "BOLT 7 §Recommendations for Routing",
    rlAnchor := "lightning/src/routing/router.rs:825; lightning/src/routing/router.rs:2797" },
  { id := "LN-RT-002", domain := .routing,
    claim := "A newer channel_update replaces an older one only if its timestamp is greater.",
    leanTarget := "LnLean.Routing.Gossip.update_monotone",
    status := .statementOnly,
    boltdoc := "BOLT 7 §The channel_update Message",
    rlAnchor := "lightning/src/routing/gossip.rs:906; lightning/src/routing/gossip.rs:422" },
  { id := "LN-RT-003", domain := .routing,
    claim := "Peeling one onion layer exposes the next hop or a terminal payload, never both.",
    leanTarget := "LnLean.Routing.Onion.peel_deterministic",
    status := .statementOnly,
    boltdoc := "BOLT 4 §Onion Decryption",
    rlAnchor := "lightning/src/ln/onion_payment.rs:505" },
  { id := "LN-RT-004", domain := .routing,
    claim := "An onion layer with an invalid HMAC is rejected rather than forwarded.",
    leanTarget := "LnLean.Routing.Onion.hmac_sound",
    status := .statementOnly,
    boltdoc := "BOLT 4 §Packet Structure",
    rlAnchor := "lightning/src/ln/onion_payment.rs:505" },
  { id := "LN-RT-005", domain := .routing,
    claim := "The CLTV expiry at each hop increases by at least that hop's cltv_expiry_delta.",
    leanTarget := "LnLean.Routing.Route.cltv_accumulates",
    status := .statementOnly,
    boltdoc := "BOLT 4 §Payload for the Last Node; BOLT 7 §HTLC Fees",
    rlAnchor := "lightning/src/routing/router.rs:657" },
  { id := "LN-RT-006", domain := .routing,
    claim := "The gossip graph contains only channels with valid announcement signatures.",
    leanTarget := "LnLean.Routing.Gossip.announcement_valid",
    status := .statementOnly,
    boltdoc := "BOLT 7 §The channel_announcement Message",
    rlAnchor := "lightning/src/routing/gossip.rs:515; lightning/src/routing/gossip.rs:1012" },

  -- Payments (6)
  { id := "LN-PM-001", domain := .payment,
    claim := "A consistent invoice has the payment session's hash and amount.",
    leanTarget := "LnLean.Security.Invoice.consistent_hash; LnLean.Security.Invoice.consistent_amount",
    status := .proved,
    boltdoc := "BOLT 11 §Tagged Fields",
    rlAnchor := "lightning-invoice/src/lib.rs:1662; lightning-invoice/src/lib.rs:1473" },
  { id := "LN-PM-002", domain := .payment,
    claim := "A BOLT 11 invoice signature is valid for the payee node key.",
    leanTarget := "LnLean.Payment.Invoice.signature_valid",
    status := .statementOnly,
    boltdoc := "BOLT 11 §Data Part; BOLT 11 §Payer / Payee Interactions",
    rlAnchor := "lightning-invoice/src/lib.rs:272; lightning-invoice/src/lib.rs:588" },
  { id := "LN-PM-003", domain := .payment,
    claim := "The final onion payload's payment secret matches the invoice's payment secret.",
    leanTarget := "LnLean.Payment.Invoice.payment_secret_match",
    status := .proved,
    boltdoc := "BOLT 4 §Payload for the Last Node; BOLT 11 §Tagged Fields",
    rlAnchor := "lightning-invoice/src/lib.rs:1195; lightning/src/ln/onion_payment.rs:856" },
  { id := "LN-PM-004", domain := .payment,
    claim := "A settled multipart payment has parts summing exactly to the advertised total.",
    leanTarget := "LnLean.Security.MppPayment.settle_requires_sum",
    status := .proved,
    boltdoc := "BOLT 4 §Basic Multi-Part Payments",
    rlAnchor := "lightning/src/ln/onion_payment.rs:856" },
  { id := "LN-PM-005", domain := .payment,
    claim := "During MPP collection, each additional part keeps the running total at or below total_msat.",
    leanTarget := "LnLean.Payment.MPP.running_total_bound",
    status := .statementOnly,
    boltdoc := "BOLT 4 §Basic Multi-Part Payments",
    rlAnchor := "lightning/src/ln/onion_payment.rs:857" },
  { id := "LN-PM-006", domain := .payment,
    claim := "A keysend payment uses the sender-supplied preimage as the payment preimage.",
    leanTarget := "LnLean.Payment.Keysend.preimage_binding",
    status := .proved,
    boltdoc := "BOLT 4 §Payload for the Last Node (keysend extension)",
    rlAnchor := "lightning/src/ln/onion_payment.rs:454" },

  -- Security / liveness (6)
  { id := "LN-SEC-001", domain := .security,
    claim := "Spending a fresh L1 outpoint preserves the no-double-spend predicate.",
    leanTarget := "LnLean.Security.L1Ledger.spend_preserves_noDoubleSpend",
    status := .proved,
    boltdoc := "BOLT 5 §Commitment Transaction",
    rlAnchor := "lightning/src/chain/channelmonitor.rs:5079" },
  { id := "LN-SEC-002", domain := .security,
    claim := "Across all channels and the L1 spend set, total value is conserved.",
    leanTarget := "LnLean.Proofs.Conservation.global_conservation",
    status := .statementOnly,
    boltdoc := "BOLT 3 §Commitment Transaction",
    rlAnchor := "lightning/src/ln/chan_utils.rs:716" },
  { id := "LN-SEC-003", domain := .security,
    claim := "Safety holds under an asynchronous adversarial schedule (without a fairness hypothesis).",
    leanTarget := "LnLean.Proofs.Security.safety_async",
    status := .statementOnly,
    boltdoc := "BOLT 2 §Message Retransmission",
    rlAnchor := "lightning/src/ln/channelmanager.rs:17831" },
  { id := "LN-SEC-004", domain := .security,
    claim := "After GST every message is delivered within delta of its send time.",
    leanTarget := "LnLean.Security.partial_synchrony_delivers",
    status := .proved,
    boltdoc := "BOLT 1 §Lightning Message Format",
    rlAnchor := "lightning/src/ln/channelmanager.rs:17831" },
  { id := "LN-SEC-005", domain := .security,
    claim := "A penalty transaction remains economical under the modelled fee spike.",
    leanTarget := "LnLean.Proofs.Liveness.penalty_economical",
    status := .statementOnly,
    boltdoc := "BOLT 5 §Revoked Transaction Close Handling",
    rlAnchor := "lightning/src/chain/chaininterface.rs:350" },
  { id := "LN-SEC-006", domain := .security,
    claim := "A breach is punished if some party has the revocation secret and a timely L1 transaction, given a live watchtower.",
    leanTarget := "LnLean.Proofs.Liveness.watchtower_bridge",
    status := .statementOnly,
    boltdoc := "BOLT 5 §Revoked Transaction Close Handling",
    rlAnchor := "lightning/src/chain/channelmonitor.rs:5079" }
  ]

/-- The catalog has exactly 48 rows. -/
theorem obligations_length : obligations.length = 48 := rfl

end LnLean.Proofs
