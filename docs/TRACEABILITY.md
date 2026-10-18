# Traceability: obligation to BOLT and rust-lightning

**Status:** proof-wave traceability. The table has 48 rows, one for each id in
`LnLean/Proofs/Obligations.lean` and `docs/THEOREM-INDEX.md`; 48 are `proved`,
0 remain `statement-only`, and the catalog resolves 73 targets after
proof-wave 6.

Anchors are at pinned commit `fe4900930c6bd5786ec4203274d7cf312776a5a6`
for rust-lightning and `1aadb719b4007c4cea0ba6e36b08c4fb53788dee` for the
BOLTs. `path:line` values were checked to exist in the pinned tree; a missing
anchor is written `UNANCHORED` rather than guessed. No row in this catalog
currently needs that marker.

| Id | BOLT section | rust-lightning path:line | Lean target | Status |
|---|---|---|---|---|
| `LN-L1-001` | BOLT 2 §Channel Establishment v1; BOLT 3 §Funding Transaction Output | `lightning/src/ln/chan_utils.rs:847` | `LnLean.Proofs.Bitcoin.FundingScriptTargets.fundingScriptPubKey_eq_p2wsh_twoOfTwo; LnLean.Proofs.Bitcoin.FundingLinkTargets.fundingScriptPubKey_eq_p2wsh_ordered; LnLean.Proofs.Bitcoin.InterpreterBridgeTargets.funding_interpreters_agree; LnLean.Proofs.Bitcoin.SighashBridgeTargets.funding_sighash_interpreters_agree` | proved |
| `LN-L1-002` | BOLT 2 §The open_channel Message | `lightning/src/ln/channel.rs:2683` | `LnLean.Bitcoin.fundingOutput_moneyRange` | proved |
| `LN-L1-003` | BOLT 5 §Commitment Transaction | `lightning/src/chain/channelmonitor.rs:514` | `LnLean.Proofs.Security.ReorgTargets.reorg_preserves_channel_safety; LnLean.Proofs.Security.ReorgTargets.deep_reorg_separate_failure_mode` | proved |
| `LN-L1-004` | BOLT 3 §to_local Output | `lightning/src/ln/chan_utils.rs:687` | `LnLean.Proofs.Bitcoin.ToLocalScriptTargets.toLocalScriptFull_carries_csv_and_revocationKey; LnLean.Proofs.Bitcoin.ToLocalScriptTargets.toLocalScriptFull_commits_delay_and_revocationKey; LnLean.Proofs.Bitcoin.ToLocalScriptTargets.commitmentOutputs_toLocal_commits_delay_and_revocationKey; LnLean.Proofs.Bitcoin.InterpreterBridgeTargets.toLocal_delayed_interpreters_agree; LnLean.Proofs.Bitcoin.InterpreterRevocationTargets.toLocal_revocation_interpreters_agree; LnLean.Proofs.Bitcoin.SighashBridgeTargets.toLocal_sighash_interpreters_agree` | proved |
| `LN-L1-005` | BOLT 3 §to_local_anchor and to_remote_anchor Output | `lightning/src/ln/channel.rs:989` | `LnLean.Bitcoin.anchorValue_eq` | proved |
| `LN-L1-006` | BOLT 3 §Expected Weight of the Commitment Transaction | `lightning/src/ln/chan_utils.rs:281` | `LnLean.Proofs.Bitcoin.commitmentBaseWeight_model_target` | proved |
| `LN-CR-001` | BOLT 2 §Adding an HTLC | `lightning/src/ln/channel.rs:8370` | `LnLean.Crypto.Hash.paymentHash_sha256_contract` | proved |
| `LN-CR-002` | BOLT 3 §Commitment Transaction Construction | `lightning/src/ln/chan_utils.rs:1450` | `LnLean.Crypto.Sig.commitmentSig_contract` | proved |
| `LN-CR-003` | BOLT 4 §Packet Structure | `lightning/src/ln/onion_payment.rs:505` | `LnLean.Crypto.Hash.onionHmacTag_size_and_bindsOn` | proved |
| `LN-CR-004` | BOLT 1 §Fundamental Types; BOLT 1 Appendix A | `lightning/src/util/ser.rs:442` | `LnLean.Wire.decode_encode` | proved |
| `LN-CR-005` | BOLT 1 §Type-Length-Value Format | `lightning/src/util/ser.rs:369` | `LnLean.Wire.TLVStream.wellFormed_iff_pairwise; LnLean.Wire.TLVStream.wellFormed_record_type_unique` | proved |
| `LN-CR-006` | BOLT 1 §Lightning Message Format | `lightning/src/ln/peer_handler.rs:331` | `LnLean.Wire.Message.decode_length` | proved |
| `LN-CH-001` | BOLT 3 §Commitment Transaction | `lightning/src/ln/chan_utils.rs:716` | `LnLean.Security.Ledger.step_conserves` | proved |
| `LN-CH-002` | BOLT 3 §Commitment Transaction Outputs | `lightning/src/ln/chan_utils.rs:1908` | `LnLean.Channel.Commitment.outputs_nonnegative` | proved |
| `LN-CH-003` | BOLT 3 §Transaction Output Ordering; BOLT 3 §Trimmed Outputs | `lightning/src/ln/chan_utils.rs:1985` | `LnLean.Channel.Commitment.output_ordering; LnLean.Channel.CommitmentTx.migratedFrom_outputsNet_perm_commitmentOutputs; LnLean.Proofs.Channel.CommitmentTypes.CommitmentTx.migrateNet_canonicalOutputs_eq_commitmentOutputs` | proved |
| `LN-CH-004` | BOLT 2 §Committing Updates So Far | `lightning/src/ln/channel.rs:6270` | `LnLean.Security.advance_monotone` | proved |
| `LN-CH-005` | BOLT 3 §Fees; BOLT 5 §Commitment Transaction | `lightning/src/ln/channel.rs:3721` | `LnLean.Channel.Fee.commitmentSigningGate_rejected_iff_insufficient; LnLean.Channel.Fee.commitmentSigningGate_rejected_iff_no_checkedSigning` | proved |
| `LN-CH-006` | BOLT 2 §Bounding exposure to trimmed in-flight HTLCs | `lightning/src/ln/channel.rs:4223` | `LnLean.Channel.Reserve.bounds` | proved |
| `LN-HT-001` | BOLT 2 §Removing an HTLC | `lightning/src/ln/channel.rs:8640; lightning/src/ln/chan_utils.rs:841` | `LnLean.Security.HtlcRecord.fulfill_sound` | proved |
| `LN-HT-002` | BOLT 3 §HTLC-Timeout and HTLC-Success Transactions | `lightning/src/ln/chan_utils.rs:875; lightning/src/ln/channel.rs:8671` | `LnLean.Security.HtlcRecord.fail_only_after_expiry` | proved |
| `LN-HT-003` | BOLT 2 §Adding an HTLC | `lightning/src/ln/chan_utils.rs:716` | `LnLean.Channel.HTLC.amount_conservation` | proved |
| `LN-HT-004` | BOLT 2 §Adding an HTLC | `lightning/src/ln/channel.rs:8370` | `LnLean.Channel.HTLC.dir_id_unique; LnLean.Channel.HTLC.id_unique_of_reachable_cross; LnLean.Channel.HTLC.tagged_id_unique_of_reachable; LnLean.Channel.HTLC.tagged_ids_nodup_of_reachable; LnLean.Channel.HTLC.cross_direction_duplicate_tagged` | proved |
| `LN-HT-005` | BOLT 3 §Per-commitment Secret Requirements | `lightning/src/ln/chan_utils.rs:518` | `LnLean.Security.revoked_commitment_is_old` | proved |
| `LN-HT-006` | BOLT 5 §Revoked Transaction Close Handling | `lightning/src/ln/channel.rs:9471; lightning/src/chain/channelmonitor.rs:5079` | `LnLean.Security.breach_penalty_spends_both` | proved |
| `LN-PR-001` | BOLT 2 §The open_channel Message | `lightning/src/ln/channelmanager.rs:17521` | `LnLean.Protocol.Handshake.open_bounds` | proved |
| `LN-PR-002` | BOLT 2 §The channel_ready Message | `lightning/src/ln/channelmanager.rs:17614` | `LnLean.Protocol.Handshake.channel_ready_gate` | proved |
| `LN-PR-003` | BOLT 2 §The funding_signed Message | `lightning/src/ln/channel.rs:2107` | `LnLean.Protocol.Handshake.funding_signed_signing_contract; LnLean.Proofs.Channel.SighashTargets.funding_and_commitment_signing_contract` | proved |
| `LN-PR-004` | BOLT 2 §Committing Updates So Far | `lightning/src/ln/channel.rs:2386; lightning/src/ln/channel.rs:6270` | `LnLean.Proofs.ProtocolWireTargets.commitment_signed_full_covers_exact; LnLean.Proofs.ProtocolWireTargets.protocol_wire_summary; LnLean.Proofs.Channel.SighashTargets.SighashProduces.coverage; LnLean.Proofs.Channel.SighashViewBindingTargets.commitmentSignature_binds_viewOfState; LnLean.Proofs.Channel.SighashTargets.CommitmentWire.txBytes_parse` | proved |
| `LN-PR-005` | BOLT 2 §Message Retransmission | `lightning/src/ln/channelmanager.rs:17831; lightning/src/ln/channel.rs:10826` | `LnLean.Protocol.Peer.reestablish_no_rollback` | proved |
| `LN-PR-006` | BOLT 9 §Features; BOLT 2 §Defined Channel Types | `lightning/src/ln/channel.rs:4702` | `LnLean.Protocol.Handshake.feature_intersection` | proved |
| `LN-RT-001` | BOLT 7 §Recommendations for Routing | `lightning/src/routing/router.rs:825; lightning/src/routing/router.rs:2797` | `LnLean.Security.Route.wellFormed_connected; LnLean.Security.Route.wellFormed_capacity; LnLean.Security.Route.wellFormed_nonempty` | proved |
| `LN-RT-002` | BOLT 7 §The channel_update Message | `lightning/src/routing/gossip.rs:906; lightning/src/routing/gossip.rs:422` | `LnLean.Routing.Gossip.update_monotone` | proved |
| `LN-RT-003` | BOLT 4 §Onion Decryption | `lightning/src/ln/onion_payment.rs:505` | `LnLean.Routing.Onion.peel_deterministic` | proved |
| `LN-RT-004` | BOLT 4 §Packet Structure | `lightning/src/ln/onion_payment.rs:505` | `LnLean.Routing.Onion.hmac_sound` | proved |
| `LN-RT-005` | BOLT 4 §Payload for the Last Node; BOLT 7 §HTLC Fees | `lightning/src/routing/router.rs:657` | `LnLean.Routing.Route.cltv_accumulates` | proved |
| `LN-RT-006` | BOLT 7 §The channel_announcement Message | `lightning/src/routing/gossip.rs:515; lightning/src/routing/gossip.rs:1012` | `LnLean.Proofs.Routing.GossipTargets.gossip_graph_only_valid_announcements` | proved |
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
| `LN-SEC-005` | BOLT 5 §Revoked Transaction Close Handling | `lightning/src/chain/chaininterface.rs:350` | `LnLean.Proofs.Liveness.penalty_economical` | proved |
| `LN-SEC-006` | BOLT 5 §Revoked Transaction Close Handling | `lightning/src/chain/channelmonitor.rs:5079` | `LnLean.Proofs.Liveness.watchtower_bridge` | proved |

**Proof-wave scope notes.** The promoted rows `LN-PR-001/005`,
`LN-PR-006`, `LN-RT-002` through `LN-RT-005`, `LN-CR-001/002/003`,
`LN-CR-006`, `LN-CH-002`, `LN-HT-003`, `LN-PM-002`, `LN-PM-005`, and
`LN-SEC-002/003/005/006` name exact, sorry-free declarations. Some keep
explicit model hypotheses:
`LN-CR-001` covers constructed/opened hashes and C1 uniqueness (the universal
range reading is refuted by D05); `LN-CR-002` is C3 binding plus funding/close
domain separation, not signing completeness or key attribution; `LN-CR-003`
is 32-byte output plus finite-execution C8 binding, not global HMAC PRF;
`LN-CH-002` uses the BOLT 3 balance equation; `LN-HT-003` uses the explicit
ledger invariant; `LN-PM-002` is a projection from `Invoice.verify` (ECDSA
remains assumption C3); `LN-RT-004` is the checked `openLayer` path (raw `peel`
bypasses HMAC, with the D25 counterexample preserved); `LN-SEC-002` covers the
multi-channel ledger but not an L1 spend set; `LN-SEC-003` is conditional on
the four explicit `Assumptions P`; `LN-SEC-005` is the bounded-schedule
theorem; and `LN-SEC-006` requires a watchtower report, not merely `live`.
`LN-PR-006` uses the support-set intersection under BOLT 1 survival, not raw
bitwise AND. See `docs/THEOREM-INDEX.md` and the lane reports.

**Proof-wave 3/5/6 scope notes.** The strengthened rows name exact,
sorry-free theorems: `LN-L1-001` combines the handshake-constructed hash link,
positive-direction vendored interpreter execution, and the constructed BIP 143
digest/locktime bridge; `LN-L1-003` keeps the common-tip and bounded-depth
hypotheses explicit and retains a deep-reorg failure mode; `LN-L1-004` adds the
vendored delayed and revocation `to_local` branches plus the sighash bridge,
while ECDSA/policy/decoded-sequence context remains explicit; `LN-L1-006`
distinguishes the BOLT 3 fee-basis constants from literal serialization weight
and proves the 8 WU anchor gap; `LN-CR-005` is the exact pairwise-sorted
characterization; `LN-CH-003` adds the five-field gross/net record layer, the
arbitrary-dust canonical permutation/refinement, and effective-fee accounting
while D12 still refutes the legacy function; `LN-CH-005` is the exact fee-gate
characterization; `LN-HT-004` is per-sender uniqueness plus the explicit
`CrossDisjoint` global form (the literal global claim is refuted); `LN-PR-003`
is conditional on `FundingSigningLaw` and `KeyBinding`; `LN-PR-004` adds exact
BOLT 3 transaction wire layouts, a structural preimage serializer, C3 digest
binding, and conditional view binding, with full preimage byte equality and
wire-only negative results retained; and `LN-RT-006` covers reachable
signature-gated gossip states, while raw `applyGossip` remains unfiltered and
G19 key attribution is separate.

## Anchor policy

* A row may carry two anchors when the property spans a state-machine check and a cryptographic/script helper (for example `channel.rs` and `chan_utils.rs`).

* `BOLT 9` is cited only for feature negotiation (`LN-PR-006`); keysend is not a BOLT and is marked as an extension in `LN-PM-006`.

* `UNANCHORED` would mean no real source line was found. It is not used here; if a future edit cannot support an anchor, the row must say so instead of inventing a line.

