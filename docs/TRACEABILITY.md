# Traceability: obligation to BOLT and rust-lightning

**Status:** proof-wave traceability. The table has 48 rows, one for each id in
`LnLean/Proofs/Obligations.lean` and `docs/THEOREM-INDEX.md`; 48 are `proved`,
0 remain `statement-only`, and the catalog resolves 198 targets after
proof-wave 10.

Anchors are at pinned commit `fe4900930c6bd5786ec4203274d7cf312776a5a6`
for rust-lightning and `1aadb719b4007c4cea0ba6e36b08c4fb53788dee` for the
BOLTs. `path:line` values were checked to exist in the pinned tree; a missing
anchor is written `UNANCHORED` rather than guessed. No row in this catalog
currently needs that marker.

| Id | BOLT section | rust-lightning path:line | Lean target | Status |
|---|---|---|---|---|
| `LN-L1-001` | BOLT 2 §Channel Establishment v1; BOLT 3 §Funding Transaction Output | `lightning/src/ln/chan_utils.rs:847` | LnLean.Proofs.Bitcoin.FundingScriptTargets.fundingScriptPubKey_eq_p2wsh_twoOfTwo; LnLean.Proofs.Bitcoin.FundingLinkTargets.fundingScriptPubKey_eq_p2wsh_ordered; LnLean.Proofs.Bitcoin.InterpreterBridgeTargets.funding_interpreters_agree; LnLean.Proofs.Bitcoin.SighashBridgeTargets.funding_sighash_interpreters_agree; LnLean.Proofs.Bitcoin.FundingAuthTargets.openAccept_hash_linked; LnLean.Proofs.Bitcoin.EcdsaBridgeTargets.fundingSignedValid_iff_vendor; LnLean.Proofs.Bitcoin.EcdsaBridgeTargets.funding_sighash_interpreters_agree_vendor; LnLean.Proofs.Bitcoin.EcdsaConcreteTargets.eufCma_vendorVerify_iff_totalReject; LnLean.Proofs.Bitcoin.EcdsaConcreteTargets.bridged_model_totalReject; LnLean.Proofs.Bitcoin.EcdsaConcreteTargets.exists_bridged_model_iff_totalReject; LnLean.Proofs.Bitcoin.EcdsaConcreteTargets.withVendorEcdsa_no_funding; LnLean.Proofs.Bitcoin.EcdsaConcreteTargets.not_digestBindsMod_fundingTag; LnLean.Proofs.Bitcoin.EcdsaDomainTargets.not_digestBindsMod_any_tag; LnLean.Proofs.Bitcoin.EcdsaDomainTargets.no_digestBindsMod_anywhere; LnLean.Proofs.Bitcoin.EcdsaDomainTargets.not_digestBindsModOn33_any_tag; LnLean.Proofs.Bitcoin.EcdsaDomainTargets.digestBindsModOn_canonical33; LnLean.Proofs.Bitcoin.EcdsaDomainTargets.digestBindsModOn_canonical32; LnLean.Proofs.Bitcoin.EcdsaDomainTargets.residueBinding_vendor_funding_eq_of_canonical33; LnLean.Proofs.Bitcoin.EcdsaDomainTargets.digest_domain_dichotomy | proved |
| `LN-L1-002` | BOLT 2 §The open_channel Message | `lightning/src/ln/channel.rs:2683` | `LnLean.Bitcoin.fundingOutput_moneyRange` | proved |
| `LN-L1-003` | BOLT 5 §Commitment Transaction | `lightning/src/chain/channelmonitor.rs:514` | `LnLean.Proofs.Security.ReorgTargets.reorg_preserves_channel_safety; LnLean.Proofs.Security.ReorgTargets.deep_reorg_separate_failure_mode` | proved |
| `LN-L1-004` | BOLT 3 §to_local Output | `lightning/src/ln/chan_utils.rs:687` | LnLean.Proofs.Bitcoin.ToLocalScriptTargets.toLocalScriptFull_carries_csv_and_revocationKey; LnLean.Proofs.Bitcoin.ToLocalScriptTargets.toLocalScriptFull_commits_delay_and_revocationKey; LnLean.Proofs.Bitcoin.ToLocalScriptTargets.commitmentOutputs_toLocal_commits_delay_and_revocationKey; LnLean.Proofs.Bitcoin.InterpreterBridgeTargets.toLocal_delayed_interpreters_agree; LnLean.Proofs.Bitcoin.InterpreterRevocationTargets.toLocal_revocation_interpreters_agree; LnLean.Proofs.Bitcoin.SighashBridgeTargets.toLocal_sighash_interpreters_agree; LnLean.Proofs.Bitcoin.SequenceContextTargets.toLocal_delayed_realChecker_refinement; LnLean.Proofs.Bitcoin.TxValidTransferTargets.txCheckerFor_some_eq_realCheckerOf; LnLean.Proofs.Bitcoin.TxValidTransferTargets.toLocal_delayed_txCheckerFor_refinement; LnLean.Proofs.Bitcoin.EcdsaBridgeTargets.model_verify_eq_realChecker_seam; LnLean.Proofs.Bitcoin.EcdsaBridgeTargets.toLocal_revocation_interpreters_agree_vendor; LnLean.Proofs.Bitcoin.EcdsaConcreteTargets.eufCma_vendorVerify_iff_totalReject; LnLean.Proofs.Bitcoin.EcdsaConcreteTargets.bridged_model_totalReject; LnLean.Proofs.Bitcoin.EcdsaConcreteTargets.exists_bridged_model_iff_totalReject; LnLean.Proofs.Bitcoin.EcdsaConcreteTargets.withVendorEcdsa_no_funding; LnLean.Proofs.Bitcoin.EcdsaConcreteTargets.not_digestBindsMod_fundingTag; LnLean.Proofs.Bitcoin.EcdsaDomainTargets.not_digestBindsMod_any_tag; LnLean.Proofs.Bitcoin.EcdsaDomainTargets.no_digestBindsMod_anywhere; LnLean.Proofs.Bitcoin.EcdsaDomainTargets.not_digestBindsModOn33_any_tag; LnLean.Proofs.Bitcoin.EcdsaDomainTargets.digestBindsModOn_canonical33; LnLean.Proofs.Bitcoin.EcdsaDomainTargets.digestBindsModOn_canonical32; LnLean.Proofs.Bitcoin.EcdsaDomainTargets.residueBinding_vendor_funding_eq_of_canonical33; LnLean.Proofs.Bitcoin.EcdsaDomainTargets.digest_domain_dichotomy | proved |
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
| `LN-CH-003` | BOLT 3 §Transaction Output Ordering; BOLT 3 §Trimmed Outputs | `lightning/src/ln/chan_utils.rs:1985` | `LnLean.Channel.Commitment.output_ordering; LnLean.Channel.CommitmentTx.migratedFrom_outputsNet_perm_commitmentOutputs; LnLean.Proofs.Channel.CommitmentTypes.CommitmentTx.migrateNet_canonicalOutputs_eq_commitmentOutputs; LnLean.Proofs.Channel.CommitmentConsumer.migratedConsumerOutputs_eq_consumerOutputs_of_migrated; LnLean.Proofs.Channel.CommitmentConsumerSites.commitment_signed_full_covers_migrated; LnLean.Proofs.Channel.CommitmentConsumerSites.migratedConsumerOutputs_eq_viewOfState_outputs; LnLean.Proofs.Channel.CommitmentConsumerSites.viewOfState_outputs_perm_netConsumerOutputs` | proved |
| `LN-CH-004` | BOLT 2 §Committing Updates So Far | `lightning/src/ln/channel.rs:6270` | `LnLean.Security.advance_monotone` | proved |
| `LN-CH-005` | BOLT 3 §Fees; BOLT 5 §Commitment Transaction | `lightning/src/ln/channel.rs:3721` | `LnLean.Channel.Fee.commitmentSigningGate_rejected_iff_insufficient; LnLean.Channel.Fee.commitmentSigningGate_rejected_iff_no_checkedSigning` | proved |
| `LN-CH-006` | BOLT 2 §Bounding exposure to trimmed in-flight HTLCs | `lightning/src/ln/channel.rs:4223` | `LnLean.Channel.Reserve.bounds` | proved |
| `LN-HT-001` | BOLT 2 §Removing an HTLC | `lightning/src/ln/channel.rs:8640; lightning/src/ln/chan_utils.rs:841` | `LnLean.Security.HtlcRecord.fulfill_sound` | proved |
| `LN-HT-002` | BOLT 3 §HTLC-Timeout and HTLC-Success Transactions | `lightning/src/ln/chan_utils.rs:875; lightning/src/ln/channel.rs:8671` | `LnLean.Security.HtlcRecord.fail_only_after_expiry` | proved |
| `LN-HT-003` | BOLT 2 §Adding an HTLC | `lightning/src/ln/chan_utils.rs:716` | `LnLean.Channel.HTLC.amount_conservation` | proved |
| `LN-HT-004` | BOLT 2 §Adding an HTLC | `lightning/src/ln/channel.rs:8370` | `LnLean.Channel.HTLC.dir_id_unique; LnLean.Channel.HTLC.id_unique_of_reachable_cross; LnLean.Channel.HTLC.tagged_id_unique_of_reachable; LnLean.Channel.HTLC.tagged_ids_nodup_of_reachable; LnLean.Channel.HTLC.cross_direction_duplicate_tagged` | proved |
| `LN-HT-005` | BOLT 3 §Per-commitment Secret Requirements | `lightning/src/ln/chan_utils.rs:518` | `LnLean.Security.revoked_commitment_is_old` | proved |
| `LN-HT-006` | BOLT 5 §Revoked Transaction Close Handling | `lightning/src/ln/channel.rs:9471; lightning/src/chain/channelmonitor.rs:5079` | `LnLean.Security.breach_penalty_spends_both` | proved |
| `LN-PR-001` | BOLT 2 §The open_channel Message | `lightning/src/ln/channelmanager.rs:17521` | LnLean.Protocol.Handshake.open_bounds; LnLean.Proofs.Protocol.OpenChannelWireTargets.openChannelWire_end_to_end; LnLean.Protocol.OpenChannelWire.toFundingParams_hash_linked; LnLean.Proofs.Protocol.OpenChannelWireTargets.acceptKey_bound_before_fundingCreated_wire; LnLean.Proofs.Protocol.OpenChannelRoutingTargets.openRoute_initial_to_fundingCreated; LnLean.Proofs.Protocol.OpenChannelRoutingTargets.openChannel_routing_summary; LnLean.Proofs.Protocol.OpenChannelRoutingTargets.unattributed_open_is_routed; LnLean.Proofs.Protocol.OpenChannelRoutingTargets.wire_payload_does_not_determine_sender; LnLean.Proofs.Protocol.OpenChannelRoutingTargets.wire_binding_needs_FundingScript_C1; LnLean.Proofs.Protocol.TransportAuthTargets.transport_authenticated_attributed; LnLean.Proofs.Protocol.TransportAuthTargets.authenticated_delivery_reaches_fundingCreated; LnLean.Proofs.Protocol.TransportAuthTargets.authenticated_open_reaches_funding; LnLean.Proofs.Protocol.TransportAuthTargets.transport_auth_not_from_wire; LnLean.Proofs.Protocol.TransportAuthTargets.unattributed_delivery_exists; LnLean.Proofs.Protocol.TransportAuthTargets.no_session_binding_counterexample; LnLean.Proofs.Protocol.TransportAuthTargets.no_wire_sender_function; LnLean.Proofs.Protocol.TransportAuthTargets.transport_auth_summary | proved |
| `LN-PR-002` | BOLT 2 §The channel_ready Message | `lightning/src/ln/channelmanager.rs:17614` | `LnLean.Protocol.Handshake.channel_ready_gate` | proved |
| `LN-PR-003` | BOLT 2 §The funding_signed Message | `lightning/src/ln/channel.rs:2107` | LnLean.Protocol.Handshake.funding_signed_signing_contract; LnLean.Proofs.Channel.SighashTargets.funding_and_commitment_signing_contract; LnLean.Proofs.Crypto.KeyModelTargets.funding_signature_attribution; LnLean.Proofs.Crypto.AcceptPayloadTargets.stored_accept_payload_attribution; LnLean.Proofs.Crypto.AcceptPayloadTargets.acceptPayload_not_proof_of_possession; LnLean.Proofs.Crypto.AttributionGameTargets.stored_registration_funding_attribution; LnLean.Proofs.Crypto.AttributionGameTargets.stored_pop_attribution; LnLean.Proofs.Crypto.AttributionGameTargets.stored_payload_not_possession; LnLean.Proofs.Crypto.AttributionGameTargets.stored_attribution_fails_without_keyBinding; LnLean.Proofs.Crypto.AttributionGameTargets.attribution_game_summary; LnLean.Proofs.Crypto.PopProtocolTargets.challengeMessage_injective_of_valid; LnLean.Proofs.Crypto.PopProtocolTargets.accepts_challenge_bound; LnLean.Proofs.Crypto.PopProtocolTargets.no_cross_session_replay; LnLean.Proofs.Crypto.PopProtocolTargets.advertised_honest_completeness; LnLean.Proofs.Crypto.PopProtocolTargets.storedAccept_honest_registration; LnLean.Proofs.Crypto.PopProtocolTargets.accepted_owns; LnLean.Proofs.Crypto.PopProtocolTargets.accepted_funding_attribution; LnLean.Proofs.Crypto.PopProtocolTargets.popSound_of_keySoundOn; LnLean.Proofs.Crypto.PopProtocolTargets.accepted_stored_registration_attribution; LnLean.Proofs.Crypto.PopProtocolTargets.unbound_replay_accepts; LnLean.Proofs.Crypto.PopProtocolTargets.nonceFree_replay_accepts; LnLean.Proofs.Crypto.PopProtocolTargets.challengeMessage_not_injective_without_valid; LnLean.Proofs.Crypto.PopProtocolTargets.binding_fails_without_valid; LnLean.Proofs.Crypto.PopProtocolTargets.repeated_challenge_replay; LnLean.Proofs.Crypto.PopProtocolTargets.keySound_not_provenance; LnLean.Proofs.Crypto.PopProtocolTargets.protocol_nonvacuous; LnLean.Proofs.Crypto.PopProtocolTargets.pop_protocol_summary | proved |
| `LN-PR-004` | BOLT 2 §Committing Updates So Far | `lightning/src/ln/channel.rs:2386; lightning/src/ln/channel.rs:6270` | LnLean.Proofs.ProtocolWireTargets.commitment_signed_full_covers_exact; LnLean.Proofs.ProtocolWireTargets.protocol_wire_summary; LnLean.Proofs.Channel.SighashTargets.SighashProduces.coverage; LnLean.Proofs.Channel.SighashViewBindingTargets.commitmentSignature_binds_viewOfState; LnLean.Proofs.Channel.SighashTargets.CommitmentWire.txBytes_parse; LnLean.Proofs.Channel.SighashTargets.Bip143Preimage.preimageBytes_eq_bip143MsgL_ofTx; LnLean.Proofs.Channel.SighashTargets.commitmentBip143Preimage_eq_bip143MsgL; LnLean.Proofs.Channel.HtlcPreimageTargets.htlcBip143Preimage_eq_bip143MsgL; LnLean.Proofs.Channel.HtlcPreimageTargets.HtlcSpend.successPreimage_eq_bip143MsgL; LnLean.Proofs.Channel.HtlcPreimageTargets.HtlcSpend.timeoutPreimage_eq_bip143MsgL; LnLean.Proofs.Channel.HtlcPreimageTargets.htlc_preimage_target_summary; LnLean.Proofs.Channel.PreimageCoverageTargets.fieldAgreement_iff_eq_ofTx_and_amount; LnLean.Proofs.Channel.PreimageCoverageTargets.FieldAgreement.bytes_eq; LnLean.Proofs.Channel.PreimageCoverageTargets.FieldAgreement.digest_eq_vendor; LnLean.Proofs.Channel.PreimageCoverageTargets.wireSignatureCovers_of_preimage; LnLean.Proofs.Channel.PreimageCoverageTargets.counterPreimageLocktime_bytes_ne; LnLean.Proofs.Channel.PreimageCoverageTargets.counterPreimageAmount_bytes_ne; LnLean.Proofs.Channel.PreimageCoverageTargets.legacy_projection_not_determine_htlc_coverage; LnLean.Proofs.Channel.PreimageCoverageTargets.fieldAgreement_scriptCode_free; LnLean.Proofs.Channel.PreimageCoverageTargets.hash160_image_boundary; LnLean.Proofs.Channel.PreimageCoverageTargets.displayOrderPreimage_not_fieldAgreement; LnLean.Proofs.Channel.PreimageCoverageTargets.vectorHtlcSpend_amount_is_gross; LnLean.Proofs.Channel.PreimageCoverageTargets.preimage_coverage_summary; LnLean.Proofs.Channel.CoverageWitnessTargets.decodeCoverage_canonical; LnLean.Proofs.Channel.CoverageWitnessTargets.decodeCoverage_covers; LnLean.Proofs.Channel.CoverageWitnessTargets.no_legacy_only_coverage_decoder; LnLean.Proofs.Channel.CoverageWitnessTargets.no_legacy_only_witness_selector; LnLean.Proofs.Channel.CoverageWitnessTargets.wire_admits_distinct_coverage_witnesses; LnLean.Proofs.Channel.CoverageWitnessTargets.amount_is_necessary; LnLean.Proofs.Channel.CoverageWitnessTargets.toCommitmentHtlcOutput_eq_iff; LnLean.Proofs.Channel.CoverageWitnessTargets.coverage_witness_summary | proved |
| `LN-PR-005` | BOLT 2 §Message Retransmission | `lightning/src/ln/channelmanager.rs:17831; lightning/src/ln/channel.rs:10826` | `LnLean.Protocol.Peer.reestablish_no_rollback` | proved |
| `LN-PR-006` | BOLT 9 §Features; BOLT 2 §Defined Channel Types | `lightning/src/ln/channel.rs:4702` | `LnLean.Protocol.Handshake.feature_intersection` | proved |
| `LN-RT-001` | BOLT 7 §Recommendations for Routing | `lightning/src/routing/router.rs:825; lightning/src/routing/router.rs:2797` | `LnLean.Security.Route.wellFormed_connected; LnLean.Security.Route.wellFormed_capacity; LnLean.Security.Route.wellFormed_nonempty` | proved |
| `LN-RT-002` | BOLT 7 §The channel_update Message | `lightning/src/routing/gossip.rs:906; lightning/src/routing/gossip.rs:422` | LnLean.Routing.Gossip.update_monotone; LnLean.Proofs.Routing.GossipStoreEpochTargets.epochFold_gossip_eq_canonicalStoreView_rawFold; LnLean.Routing.replacedUpdates_timestamp_lt; LnLean.Proofs.Routing.GossipStoreEpochTargets.StoreEpoch.epochFold_store_eq_foldl; LnLean.Proofs.Routing.NodeCanonicalTargets.reachableNodeCanonical_node_replacement; LnLean.Proofs.Routing.NodeCanonicalTargets.reachableNodeCanonical_rotation_keeps_both; LnLean.Proofs.Routing.NodeCanonicalTargets.reachableNodeCanonical_equal_timestamp_tie_boundary; LnLean.Proofs.Routing.NodeCanonicalTargets.no_canonical_node_preserving_raw_node_extension; LnLean.Proofs.Routing.NodeCanonicalTargets.canonicalStoreView_does_not_canonicalise_nodes; LnLean.Proofs.Routing.NodeCanonicalTargets.reachableNodeCanonical_node_slot_ignores_global_clock; LnLean.Proofs.Routing.NodeCanonicalTargets.raw_nonrefinement_preserved; LnLean.Proofs.Routing.NodeCanonicalTargets.epoch_square_lifts_to_node_canonical_view; LnLean.Proofs.Routing.NodeCanonicalTargets.canonicalNodeStoreView_nodeCanonical; LnLean.Proofs.Routing.NodeCanonicalTargets.applyGossipNodeCanonical_node_of_admitted; LnLean.Proofs.Routing.NodeIdentityTargets.canonical_distinct_nodes_no_oriented_store_link; LnLean.Proofs.Routing.NodeIdentityTargets.no_store_function_selects_both_rotation_worlds; LnLean.Proofs.Routing.NodeIdentityTargets.concrete_intended_rotation_not_storeOnly; LnLean.Proofs.Routing.NodeIdentityTargets.rotation_preserves_wireMember; LnLean.Proofs.Routing.NodeIdentityTargets.rotation_not_signature_preserving; LnLean.Proofs.Routing.NodeIdentityTargets.channelAnnouncement_admitted_of_wireMember; LnLean.Proofs.Routing.NodeIdentityTargets.missing_endpoint_channel_admitted; LnLean.Proofs.Routing.NodeIdentityTargets.wireMember_applyGossipNodeCanonical; LnLean.Proofs.Routing.NodeIdentityTargets.graphBacked_of_nodeKeyConsistent | proved |
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

**Proof-wave 3/5/6/7 scope notes.** The strengthened rows name exact,
sorry-free theorems: `LN-L1-001` combines the handshake-constructed hash link,
the joint open/accept construction, positive-direction vendored interpreter
execution, and the constructed BIP 143 digest/locktime bridge; `LN-L1-003`
keeps the common-tip and bounded-depth hypotheses explicit and retains a
deep-reorg failure mode; `LN-L1-004` adds the vendored delayed and revocation
`to_local` branches, the sighash bridge, and the exact decoded BIP 68/112
sequence-context refinement, while ECDSA, `TxValidation.Full`, and policy edges
remain explicit; `LN-L1-006` distinguishes the BOLT 3 fee-basis constants from
literal serialization weight and proves the 8 WU anchor gap; `LN-CR-005` is the
exact pairwise-sorted characterization; `LN-CH-003` adds the five-field
gross/net record layer, the arbitrary-dust canonical permutation/refinement,
effective-fee accounting, and the normal-form consumer migration, while D12
still refutes the legacy function; `LN-CH-005` is the exact fee-gate
characterization; `LN-HT-004` is per-sender uniqueness plus the explicit
`CrossDisjoint` global form (the literal global claim is refuted); `LN-PR-003`
is conditional on `FundingSigningLaw` and `KeyBinding`, with the secret-key
model and the generation-not-attribution counterexample; `LN-PR-004` adds exact
BOLT 3 transaction wire layouts, a structural preimage serializer, commitment-
wire byte equality with the vendor encoder, C3 digest binding, and conditional
view binding, with the HTLC-wire instantiation and wire-only negative results
retained; and `LN-RT-006` covers reachable signature-gated gossip states, while
raw `applyGossip` remains unfiltered and is proved not to refine canonical
admission; the canonical-store wrapper is the supported path.

## Anchor policy

* A row may carry two anchors when the property spans a state-machine check and a cryptographic/script helper (for example `channel.rs` and `chan_utils.rs`).

* `BOLT 9` is cited only for feature negotiation (`LN-PR-006`); keysend is not a BOLT and is marked as an extension in `LN-PM-006`.

* `UNANCHORED` would mean no real source line was found. It is not used here; if a future edit cannot support an anchor, the row must say so instead of inventing a line.



**Proof-wave 8 scope notes.** The strengthened rows name exact, sorry-free
targets added by the wave-8 lanes: `LN-L1-001` adds the conditional
`VendorEcdsaBridge` transfer and funding-sighash agreement; `LN-L1-004` adds
the exact known-amount `txCheckerFor`/`realCheckerOf` transfer and the
delayed/revocation branch transfers; `LN-PR-001` adds the type-32
`open_channel` wire path and funding projection; `LN-PR-003` adds accept-payload
storage/provenance and the negative proof-of-possession result;
`LN-PR-004` adds HTLC second-stage preimage byte equality and scriptCode
synthesis; `LN-CH-003` adds the proof-layer consumer adapter; and `LN-RT-002`
adds the epoch/replacement-history square. The catalog remains 48 rows with
142 resolved targets at that gate. See `docs/THEOREM-INDEX.md` and
`agents/reports/swarm8/`.

Proof-wave 10 adds five proof modules, keeps the catalog at 48 rows, and
strengthens the same six rows to **198 resolved targets**. The new evidence is
`EcdsaDomainTargets` in `LN-L1-001`/`LN-L1-004`, `TransportAuthTargets` in
`LN-PR-001`, `PopProtocolTargets` in `LN-PR-003`, `CoverageWitnessTargets` in
`LN-PR-004`, and `NodeIdentityTargets` in `LN-RT-002`; `CONF-01` adds the live
`open_channel` row. See `agents/reports/swarm10/` and the wave-10 notes in
`docs/THEOREM-INDEX.md`.
