# Traceability: obligation to BOLT and rust-lightning

**Status:** proof-wave traceability. The table has 48 rows, one for each id in
`LnLean/Proofs/Obligations.lean` and `docs/THEOREM-INDEX.md`; 29 are `proved`
and 19 remain `statement-only` after the eight-lane proof round.

Anchors are at pinned commit `fe4900930c6bd5786ec4203274d7cf312776a5a6`
for rust-lightning and `1aadb719b4007c4cea0ba6e36b08c4fb53788dee` for the
BOLTs. `path:line` values were checked to exist in the pinned tree; a missing
anchor is written `UNANCHORED` rather than guessed. No row in this catalog
currently needs that marker.

| Id | BOLT section | rust-lightning path:line | Lean target | Status |
|---|---|---|---|---|
| `LN-L1-001` | BOLT 2 §Channel Establishment v1; BOLT 3 §Funding Transaction Output | `lightning/src/ln/chan_utils.rs:847` | `LnLean.Bitcoin.fundingScriptPubKey` | statement-only |
| `LN-L1-002` | BOLT 2 §The open_channel Message | `lightning/src/ln/channel.rs:2683` | `LnLean.Bitcoin.fundingOutput_moneyRange` | proved |
| `LN-L1-003` | BOLT 5 §Commitment Transaction | `lightning/src/chain/channelmonitor.rs:514` | `LnLean.Security.Adversary.reorgAllowed` | statement-only |
| `LN-L1-004` | BOLT 3 §to_local Output | `lightning/src/ln/chan_utils.rs:687` | `LnLean.Bitcoin.toLocalScript` | statement-only |
| `LN-L1-005` | BOLT 3 §to_local_anchor and to_remote_anchor Output | `lightning/src/ln/channel.rs:989` | `LnLean.Bitcoin.anchorValue_eq` | proved |
| `LN-L1-006` | BOLT 3 §Expected Weight of the Commitment Transaction | `lightning/src/ln/chan_utils.rs:281` | `LnLean.Bitcoin.commitmentBaseWeight` | statement-only |
| `LN-CR-001` | BOLT 2 §Adding an HTLC | `lightning/src/ln/channel.rs:8370` | `LnLean.Crypto.Hash.sha256` | statement-only |
| `LN-CR-002` | BOLT 3 §Commitment Transaction Construction | `lightning/src/ln/chan_utils.rs:1450` | `LnLean.Crypto.Sig.ecdsaVerify` | statement-only |
| `LN-CR-003` | BOLT 4 §Packet Structure | `lightning/src/ln/onion_payment.rs:505` | `LnLean.Crypto.Hash.hmacSha256` | statement-only |
| `LN-CR-004` | BOLT 1 §Fundamental Types; BOLT 1 Appendix A | `lightning/src/util/ser.rs:442` | `LnLean.Wire.decode_encode` | proved |
| `LN-CR-005` | BOLT 1 §Type-Length-Value Format | `lightning/src/util/ser.rs:369` | `LnLean.Wire.TLVStream.WellFormed` | statement-only |
| `LN-CR-006` | BOLT 1 §Lightning Message Format | `lightning/src/ln/peer_handler.rs:331` | `LnLean.Wire.Message.decode_length` | proved |
| `LN-CH-001` | BOLT 3 §Commitment Transaction | `lightning/src/ln/chan_utils.rs:716` | `LnLean.Security.Ledger.step_conserves` | proved |
| `LN-CH-002` | BOLT 3 §Commitment Transaction Outputs | `lightning/src/ln/chan_utils.rs:1908` | `LnLean.Channel.Commitment.outputs_nonnegative` | statement-only |
| `LN-CH-003` | BOLT 3 §Transaction Output Ordering; BOLT 3 §Trimmed Outputs | `lightning/src/ln/chan_utils.rs:1985` | `LnLean.Channel.Commitment.output_ordering` | statement-only |
| `LN-CH-004` | BOLT 2 §Committing Updates So Far | `lightning/src/ln/channel.rs:6270` | `LnLean.Security.advance_monotone` | proved |
| `LN-CH-005` | BOLT 3 §Fees; BOLT 5 §Commitment Transaction | `lightning/src/ln/channel.rs:3721` | `LnLean.Channel.Fee.feeInsufficient` | statement-only |
| `LN-CH-006` | BOLT 2 §Bounding exposure to trimmed in-flight HTLCs | `lightning/src/ln/channel.rs:4223` | `LnLean.Channel.Reserve.bounds` | proved |
| `LN-HT-001` | BOLT 2 §Removing an HTLC | `lightning/src/ln/channel.rs:8640; lightning/src/ln/chan_utils.rs:841` | `LnLean.Security.HtlcRecord.fulfill_sound` | proved |
| `LN-HT-002` | BOLT 3 §HTLC-Timeout and HTLC-Success Transactions | `lightning/src/ln/chan_utils.rs:875; lightning/src/ln/channel.rs:8671` | `LnLean.Security.HtlcRecord.fail_only_after_expiry` | proved |
| `LN-HT-003` | BOLT 2 §Adding an HTLC | `lightning/src/ln/chan_utils.rs:716` | `LnLean.Channel.HTLC.amount_conservation` | statement-only |
| `LN-HT-004` | BOLT 2 §Adding an HTLC | `lightning/src/ln/channel.rs:8370` | `LnLean.Channel.HTLC.id_unique` | statement-only |
| `LN-HT-005` | BOLT 3 §Per-commitment Secret Requirements | `lightning/src/ln/chan_utils.rs:518` | `LnLean.Security.revoked_commitment_is_old` | proved |
| `LN-HT-006` | BOLT 5 §Revoked Transaction Close Handling | `lightning/src/ln/channel.rs:9471; lightning/src/chain/channelmonitor.rs:5079` | `LnLean.Security.breach_penalty_spends_both` | proved |
| `LN-PR-001` | BOLT 2 §The open_channel Message | `lightning/src/ln/channelmanager.rs:17521` | `LnLean.Protocol.Handshake.open_bounds` | statement-only |
| `LN-PR-002` | BOLT 2 §The channel_ready Message | `lightning/src/ln/channelmanager.rs:17614` | `LnLean.Protocol.Handshake.channel_ready_gate` | proved |
| `LN-PR-003` | BOLT 2 §The funding_signed Message | `lightning/src/ln/channel.rs:2107` | `LnLean.Protocol.Handshake.funding_signed_valid` | statement-only |
| `LN-PR-004` | BOLT 2 §Committing Updates So Far | `lightning/src/ln/channel.rs:2386; lightning/src/ln/channel.rs:6270` | `LnLean.Protocol.Messages.commitment_signed_covers` | statement-only |
| `LN-PR-005` | BOLT 2 §Message Retransmission | `lightning/src/ln/channelmanager.rs:17831; lightning/src/ln/channel.rs:10826` | `LnLean.Protocol.Peer.reestablish_no_rollback` | proved |
| `LN-PR-006` | BOLT 9 §Features; BOLT 2 §Defined Channel Types | `lightning/src/ln/channel.rs:4702` | `LnLean.Protocol.Handshake.feature_intersection` | statement-only |
| `LN-RT-001` | BOLT 7 §Recommendations for Routing | `lightning/src/routing/router.rs:825; lightning/src/routing/router.rs:2797` | `LnLean.Security.Route.wellFormed_connected; LnLean.Security.Route.wellFormed_capacity; LnLean.Security.Route.wellFormed_nonempty` | proved |
| `LN-RT-002` | BOLT 7 §The channel_update Message | `lightning/src/routing/gossip.rs:906; lightning/src/routing/gossip.rs:422` | `LnLean.Routing.Gossip.update_monotone` | proved |
| `LN-RT-003` | BOLT 4 §Onion Decryption | `lightning/src/ln/onion_payment.rs:505` | `LnLean.Routing.Onion.peel_deterministic` | proved |
| `LN-RT-004` | BOLT 4 §Packet Structure | `lightning/src/ln/onion_payment.rs:505` | `LnLean.Routing.Onion.hmac_sound` | proved |
| `LN-RT-005` | BOLT 4 §Payload for the Last Node; BOLT 7 §HTLC Fees | `lightning/src/routing/router.rs:657` | `LnLean.Routing.Route.cltv_accumulates` | proved |
| `LN-RT-006` | BOLT 7 §The channel_announcement Message | `lightning/src/routing/gossip.rs:515; lightning/src/routing/gossip.rs:1012` | `LnLean.Routing.Gossip.announcement_valid` | statement-only |
| `LN-PM-001` | BOLT 11 §Tagged Fields | `lightning-invoice/src/lib.rs:1662; lightning-invoice/src/lib.rs:1473` | `LnLean.Security.Invoice.consistent_hash; LnLean.Security.Invoice.consistent_amount` | proved |
| `LN-PM-002` | BOLT 11 §Data Part; BOLT 11 §Payer / Payee Interactions | `lightning-invoice/src/lib.rs:272; lightning-invoice/src/lib.rs:588` | `LnLean.Payment.Invoice.signature_valid` | proved |
| `LN-PM-003` | BOLT 4 §Payload for the Last Node; BOLT 11 §Tagged Fields | `lightning-invoice/src/lib.rs:1195; lightning/src/ln/onion_payment.rs:856` | `LnLean.Payment.Invoice.payment_secret_match` | proved |
| `LN-PM-004` | BOLT 4 §Basic Multi-Part Payments | `lightning/src/ln/onion_payment.rs:856` | `LnLean.Security.MppPayment.settle_requires_sum` | proved |
| `LN-PM-005` | BOLT 4 §Basic Multi-Part Payments | `lightning/src/ln/onion_payment.rs:857` | `LnLean.Payment.MPP.running_total_bound` | proved |
| `LN-PM-006` | BOLT 4 §Payload for the Last Node (keysend extension) | `lightning/src/ln/onion_payment.rs:454` | `LnLean.Payment.Keysend.preimage_binding` | proved |
| `LN-SEC-001` | BOLT 5 §Commitment Transaction | `lightning/src/chain/channelmonitor.rs:5079` | `LnLean.Security.L1Ledger.spend_preserves_noDoubleSpend` | proved |
| `LN-SEC-002` | BOLT 3 §Commitment Transaction | `lightning/src/ln/chan_utils.rs:716` | `LnLean.Proofs.Conservation.global_conservation` | proved |
| `LN-SEC-003` | BOLT 2 §Message Retransmission | `lightning/src/ln/channelmanager.rs:17831` | `LnLean.Proofs.Security.safety_async` | proved |
| `LN-SEC-004` | BOLT 1 §Lightning Message Format | `lightning/src/ln/channelmanager.rs:17831` | `LnLean.Security.partial_synchrony_delivers` | proved |
| `LN-SEC-005` | BOLT 5 §Revoked Transaction Close Handling | `lightning/src/chain/chaininterface.rs:350` | `LnLean.Proofs.Liveness.penalty_economical` | statement-only |
| `LN-SEC-006` | BOLT 5 §Revoked Transaction Close Handling | `lightning/src/chain/channelmonitor.rs:5079` | `LnLean.Proofs.Liveness.watchtower_bridge` | proved |

**Proof-wave scope notes.** The promoted rows `LN-PR-005`, `LN-RT-002` through
`LN-RT-005`, `LN-CR-006`, `LN-PM-002`, `LN-PM-005`, and `LN-SEC-002/003/006`
name exact, sorry-free declarations. Some keep explicit model hypotheses:
`LN-PM-002` is a projection from `Invoice.verify` (ECDSA remains assumption
C3); `LN-RT-004` is the checked `openLayer` path (raw `peel` bypasses HMAC, with
the D25 counterexample preserved); `LN-SEC-002` covers the multi-channel ledger
but not an L1 spend set; `LN-SEC-003` is conditional on the four explicit
`Assumptions P`; and `LN-SEC-006` requires a watchtower report, not merely
`live`. See `docs/THEOREM-INDEX.md` and the lane reports.

## Anchor policy

* A row may carry two anchors when the property spans a state-machine check and a cryptographic/script helper (for example `channel.rs` and `chan_utils.rs`).

* `BOLT 9` is cited only for feature negotiation (`LN-PR-006`); keysend is not a BOLT and is marked as an extension in `LN-PM-006`.

* `UNANCHORED` would mean no real source line was found. It is not used here; if a future edit cannot support an anchor, the row must say so instead of inventing a line.

