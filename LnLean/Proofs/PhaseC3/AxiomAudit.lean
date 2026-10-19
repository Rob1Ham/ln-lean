/-
  PC45 — machine-checked dependency audit of the headline theorems.

  Every theorem below is a headline result of the model.  The `#print axioms`
  commands make Lean report the transitive foundational dependencies of each
  proof.
  Policy for this audit:

  * Any dependency that records an unproved obligation is a failure.
  * `propext`, `Quot.sound`, and `Classical.choice` are the permitted
    classical axioms.

  This module is proof-complete: it adds no foundational declarations and
  uses no compiler-trust escape hatches.
-/

import LnLean.Proofs.Conservation
import LnLean.Channel.Commitment
import LnLean.Channel.HTLC
import LnLean.Proofs.CryptoTargets
import LnLean.Proofs.ProtocolTargets
import LnLean.Proofs.Channel.HTLCProps
import LnLean.Proofs.Channel.RevocationProps
import LnLean.Proofs.Channel.PenaltyProps
import LnLean.Proofs.Channel.BreachProps
import LnLean.Proofs.Channel.StateMachineProps
import LnLean.Proofs.Routing.GossipProps
import LnLean.Proofs.Routing.GraphProps
import LnLean.Proofs.Routing.OnionProps
import LnLean.Proofs.Payment.MPPProps
import LnLean.Proofs.Payment.InvoiceProps
import LnLean.Proofs.Liveness
import LnLean.Proofs.Wire.TLVProps
import LnLean.Proofs.Crypto.EcdsaProps
import LnLean.Proofs.Bitcoin.ScriptProps
import LnLean.Proofs.Bitcoin.FundingProps
import LnLean.Proofs.Bitcoin.FundingScriptTargets
import LnLean.Proofs.Bitcoin.ToLocalScriptTargets
import LnLean.Proofs.Bitcoin.WeightTargets
import LnLean.Proofs.Channel.CommitmentOrderTargets
import LnLean.Proofs.Channel.FeeTargets
import LnLean.Proofs.ProtocolCoverageTargets
import LnLean.Proofs.ProtocolSigningTargets
import LnLean.Proofs.Routing.GossipTargets
import LnLean.Proofs.Security.ReorgTargets
import LnLean.Proofs.Bitcoin.SpendTargets
import LnLean.Proofs.Channel.CommitmentIntegrationTargets
import LnLean.Proofs.Channel.HtlcGlobalIdTargets
import LnLean.Proofs.ConformanceTargets
import LnLean.Proofs.ProtocolWireTargets
import LnLean.Proofs.Routing.GossipAttributionTargets
import LnLean.Proofs.Wire.TLVTargets
import LnLean.Proofs.Bitcoin.InterpreterBridgeTargets
import LnLean.Proofs.Channel.CommitmentGrossNetTargets
import LnLean.Proofs.Channel.SighashTargets
import LnLean.Proofs.ConformanceDiffTargets
import LnLean.Proofs.Channel.StateTransitionTargets
import LnLean.Proofs.Bitcoin.FundingLinkTargets
import LnLean.Proofs.Routing.GossipKeyConsistencyTargets
import LnLean.Proofs.Security.SecurityGameTargets
import LnLean.Bitcoin.Sighash
import LnLean.Proofs.Bitcoin.SighashBridgeTargets
import LnLean.Proofs.Bitcoin.InterpreterRevocationTargets
import LnLean.Proofs.Channel.CommitmentTypesTargets
import LnLean.Proofs.Channel.SighashViewBindingTargets
import LnLean.Proofs.Channel.CommitmentDanceTargets
import LnLean.Proofs.Routing.GossipCanonicalTargets
import LnLean.Proofs.Bitcoin.SequenceContextTargets
import LnLean.Proofs.Channel.CommitmentConsumerTargets
import LnLean.Proofs.Channel.ProtocolEventFoldTargets
import LnLean.Proofs.Routing.GossipRawRefinementTargets
import LnLean.Proofs.Bitcoin.FundingAuthTargets
import LnLean.Proofs.Crypto.KeyModelTargets
import LnLean.Proofs.WaveH.H01
import LnLean.Proofs.WaveH.H04
import LnLean.Proofs.WaveH.H07
import LnLean.Proofs.WaveH.H08
import LnLean.Proofs.WaveH.H09
import LnLean.Proofs.WaveH.H13
import LnLean.Proofs.WaveH.H30
import LnLean.Proofs.WaveH.H33
import LnLean.Proofs.WaveH.H34
import LnLean.Proofs.WaveH.H39
import LnLean.Proofs.WaveH.H43
import LnLean.Proofs.WaveH.H45
import LnLean.Proofs.Bitcoin.EcdsaBridgeTargets
import LnLean.Proofs.Bitcoin.TxValidTransferTargets
import LnLean.Proofs.Protocol.OpenChannelWireTargets
import LnLean.Proofs.Crypto.AcceptPayloadTargets
import LnLean.Proofs.Channel.HtlcPreimageTargets
import LnLean.Proofs.Channel.CommitmentConsumerSitesTargets
import LnLean.Proofs.Routing.GossipStoreEpochTargets
import LnLean.Proofs.Bitcoin.EcdsaConcreteTargets
import LnLean.Proofs.Protocol.OpenChannelRoutingTargets
import LnLean.Proofs.Crypto.AttributionGameTargets
import LnLean.Proofs.Channel.PreimageCoverageTargets
import LnLean.Proofs.Routing.NodeCanonicalTargets
import LnLean.Proofs.Bitcoin.EcdsaDomainTargets
import LnLean.Proofs.Protocol.TransportAuthTargets
import LnLean.Proofs.Crypto.PopProtocolTargets
import LnLean.Proofs.Channel.CoverageWitnessTargets
import LnLean.Proofs.Routing.NodeIdentityTargets
import LnLean.Proofs.Routing.NodeIdentityChainTargets
import LnLean.Proofs.Protocol.NoiseTransportTargets
import LnLean.Proofs.Channel.CoverageSourceTargets
import LnLean.Proofs.Security.ChainFinalityTargets
import LnLean.Proofs.Payment.InvoiceWireTargets
import LnLean.Proofs.Channel.HtlcAggregateTargets
import LnLean.Proofs.Model.NonVacuityTargets

set_option autoImplicit false

/-! ## 1. Conservation -/

#print axioms LnLean.Proofs.conserved_no_value_creation
#print axioms LnLean.Proofs.ledger_no_value_creation
#print axioms LnLean.Proofs.penaltySweep_conserved
#print axioms LnLean.Proofs.trace_conserved
#print axioms LnLean.Proofs.settleHTLCOutputAt_conserved

/-! ## 2. HTLC lifecycle -/

#print axioms LnLean.Proofs.Channel.HTLCProps.fulfill_succeeds
#print axioms LnLean.Proofs.Channel.HTLCProps.fulfilled_failed_exclusive
#print axioms LnLean.Proofs.Channel.HTLCProps.settlement_terminal
#print axioms LnLean.Proofs.Channel.HTLCProps.dust_no_output_but_in_set

/-! ## 3. Revocation and penalty -/

#print axioms LnLean.Channel.deriveRevocationPubkey_point_injective
#print axioms LnLean.Channel.no_secret_reuse
#print axioms LnLean.Channel.old_revoked_by_revealed_secret
#print axioms LnLean.Proofs.Channel.penaltyValid_sweep_eq_total_sub_fee
#print axioms LnLean.Proofs.Channel.not_penaltyValid_of_window_closed
#print axioms LnLean.Channel.current_commitment_not_punishable

/-! ## 4. Channel state machine -/

#print axioms LnLean.Channel.step_allowedPhaseTransition
#print axioms LnLean.Channel.step_phaseRank_monotone
#print axioms LnLean.Channel.step_deterministic
#print axioms LnLean.Channel.step_preserves_identity
#print axioms LnLean.Channel.trace_to_normal_contains_fundingLocked

/-! ## 5. Gossip and graph -/

#print axioms LnLean.Routing.GossipProps.viewGraph_wellFormed
#print axioms LnLean.Routing.GossipProps.uniqueBindings_applyUpdate
#print axioms LnLean.Routing.GossipProps.announcement_materialises_wellFormed
#print axioms LnLean.Routing.findEdge_noSelfLoop
#print axioms LnLean.Routing.simplePaths_walk

/-! ## 6. Onion routing -/

#print axioms LnLean.Routing.sealRoute_peelExactly_final
#print axioms LnLean.Routing.peelExactly_layerCount
#print axioms LnLean.Routing.wireSize_eq_1366
#print axioms LnLean.Routing.recorded_error_bounded

/-! ## 7. Multipart payments -/

#print axioms LnLean.Payment.MPPProps.mppComplete_sum_eq_target
#print axioms LnLean.Payment.MPPProps.mppComplete_no_part_exceeds_target
#print axioms LnLean.Payment.MPPProps.settleParts_allOrNothing_succeeded
#print axioms LnLean.Payment.MPPProps.allOrNothing_no_mixed

/-! ## 8. Invoices -/

#print axioms LnLean.Payment.valid_paymentHash_size
#print axioms LnLean.Payment.decodeSemantic_valid
#print axioms LnLean.Payment.verify_iff_valid_and_check
#print axioms LnLean.Payment.verify_authorized_under_assumption

/-! ## 9. Liveness -/

#print axioms LnLean.Proofs.Liveness.fair_awaitingLockin_eventually_normal
#print axioms LnLean.Proofs.Liveness.awaitingLockin_reaches_normal
#print axioms LnLean.Proofs.Liveness.pending_htlc_eventually_resolved
#print axioms LnLean.Proofs.Liveness.reconnect_preserves_channelReady

/-! ## 10. TLV and BigSize -/

#print axioms LnLean.Wire.decodeTLV_encodeTLV
#print axioms LnLean.Wire.encode_size_eq
#print axioms LnLean.Wire.decodeBigSize_encodeBigSize

/-! ## 11. ECDSA / signature domain separation -/

#print axioms LnLean.Crypto.verifyFundingChecked_sound
#print axioms LnLean.Crypto.no_cross_domain_reuse_funding_commitment
#print axioms LnLean.Crypto.derFullOK_imp_wireSigOK

/-! ## 12. Script templates -/

#print axioms LnLean.Proofs.Bitcoin.ScriptProps.toRemote_templates_distinct
#print axioms LnLean.Proofs.Bitcoin.ScriptProps.htlcTemplates_distinct
#print axioms LnLean.Proofs.Bitcoin.ScriptProps.toLocal_contains_revocationKey

/-! ## 13. Funding -/

#print axioms LnLean.Proofs.Bitcoin.FundingProps.witnessScript_is_2of2_over_funding_keys
#print axioms LnLean.Proofs.Bitcoin.FundingProps.FundingConfirmed.script_is_p2wsh
#print axioms LnLean.Proofs.Bitcoin.FundingProps.confirm_preserves_funding
#print axioms LnLean.Proofs.Bitcoin.FundingProps.fundingSpend_conditional_2of2_only

/-! ## 14. Proof-wave 2 catalog targets -/

#print axioms LnLean.Crypto.Hash.paymentHash_sha256_contract
#print axioms LnLean.Crypto.Sig.commitmentSig_contract
#print axioms LnLean.Crypto.Hash.onionHmacTag_size_and_bindsOn
#print axioms LnLean.Channel.Commitment.outputs_nonnegative
#print axioms LnLean.Channel.HTLC.amount_conservation
#print axioms LnLean.Protocol.Handshake.open_bounds
#print axioms LnLean.Protocol.Handshake.feature_intersection
#print axioms LnLean.Proofs.Liveness.penalty_economical

/-! ## 16. Proof-wave 3 catalog targets -/

#print axioms LnLean.Proofs.Bitcoin.FundingScriptTargets.fundingScriptPubKey_eq_p2wsh_twoOfTwo
#print axioms LnLean.Proofs.Security.ReorgTargets.reorg_preserves_channel_safety
#print axioms LnLean.Proofs.Security.ReorgTargets.deep_reorg_separate_failure_mode
#print axioms LnLean.Proofs.Bitcoin.ToLocalScriptTargets.toLocalScriptFull_carries_csv_and_revocationKey
#print axioms LnLean.Proofs.Bitcoin.ToLocalScriptTargets.toLocalScriptFull_commits_delay_and_revocationKey
#print axioms LnLean.Proofs.Bitcoin.ToLocalScriptTargets.commitmentOutputs_toLocal_commits_delay_and_revocationKey
#print axioms LnLean.Proofs.Bitcoin.commitmentBaseWeight_model_target
#print axioms LnLean.Wire.TLVStream.wellFormed_iff_pairwise
#print axioms LnLean.Wire.TLVStream.wellFormed_record_type_unique
#print axioms LnLean.Channel.Commitment.output_ordering
#print axioms LnLean.Channel.Fee.commitmentSigningGate_rejected_iff_insufficient
#print axioms LnLean.Channel.Fee.commitmentSigningGate_rejected_iff_no_checkedSigning
#print axioms LnLean.Channel.HTLC.dir_id_unique
#print axioms LnLean.Channel.HTLC.id_unique_of_reachable_cross
#print axioms LnLean.Protocol.Handshake.funding_signed_signing_contract
#print axioms LnLean.Proofs.ProtocolCoverageTargets.commitment_signed_covers_exact_of_state
#print axioms LnLean.Proofs.Routing.GossipTargets.gossip_graph_only_valid_announcements

/-! ## 17. Wave 4 open-issue targets -/

#print axioms LnLean.Proofs.Bitcoin.SpendTargets.fundingOutput_spendable_output
#print axioms LnLean.Proofs.Bitcoin.SpendTargets.fundingConfirmed_spendable_output
#print axioms LnLean.Proofs.Bitcoin.SpendTargets.toLocalOutput_revocation_spendable_output
#print axioms LnLean.Proofs.Bitcoin.SpendTargets.toLocalOutput_delayed_spendable_output
#print axioms LnLean.Proofs.Bitcoin.SpendTargets.commitmentOutputs_toLocal_delayed_spendable
#print axioms LnLean.Proofs.Bitcoin.SpendTargets.fundingSpendableBy2of2_of_both_sign
#print axioms LnLean.Proofs.Channel.CommitmentIntegration.legacyOutputs_perm_commitmentOutputs
#print axioms LnLean.Proofs.Channel.CommitmentIntegration.bolt3CommitmentOfRecords_conservation
#print axioms LnLean.Proofs.Channel.CommitmentIntegration.dust_trimming_not_perm
#print axioms LnLean.Channel.HTLC.tagged_id_unique_of_reachable
#print axioms LnLean.Channel.HTLC.tagged_ids_nodup_of_reachable
#print axioms LnLean.Channel.HTLC.cross_direction_duplicate_tagged
#print axioms LnLean.Proofs.ProtocolWireTargets.commitment_signed_full_covers_exact
#print axioms LnLean.Proofs.ProtocolWireTargets.protocol_wire_summary
#print axioms LnLean.Proofs.ProtocolWireTargets.legacy_wire_cannot_determine_coverage
#print axioms LnLean.Proofs.ProtocolWireTargets.projection_forgets_fee_and_number
#print axioms LnLean.Proofs.Routing.GossipAttributionTargets.gossip_graph_edges_update_attributed
#print axioms LnLean.Proofs.Routing.GossipAttributionTargets.gossip_graph_edges_update_key_endpoint
#print axioms LnLean.Proofs.Routing.GossipAttributionTargets.raw_applyGossip_accepts_unannounced_update
#print axioms LnLean.Proofs.Conformance.bigsize_encode_one_byte_high
#print axioms LnLean.Proofs.Conformance.bigsize_decode_eight_byte_high
#print axioms LnLean.Proofs.Conformance.tlv_unknown_even_12_admission

/-! ## 18. Wave 5 bridge and completeness targets -/

#print axioms LnLean.Proofs.Bitcoin.InterpreterBridgeTargets.funding_interpreters_agree
#print axioms LnLean.Proofs.Bitcoin.InterpreterBridgeTargets.toLocal_delayed_interpreters_agree
#print axioms LnLean.Proofs.Bitcoin.InterpreterBridgeTargets.toLocal_serialize_eq
#print axioms LnLean.Proofs.Bitcoin.InterpreterBridgeTargets.funding_serialize_eq
#print axioms LnLean.Channel.CommitmentTx.migratedFrom_outputsNet_perm_commitmentOutputs
#print axioms LnLean.Channel.CommitmentTx.migratedFrom_conservation
#print axioms LnLean.Channel.CommitmentTx.migratedFrom_effectiveFee_eq
#print axioms LnLean.Proofs.Channel.CommitmentGrossNet.d12_output_ordering_fails
#print axioms LnLean.Proofs.Channel.SighashTargets.SighashProduces.coverage
#print axioms LnLean.Proofs.Channel.SighashTargets.sighash_summary
#print axioms LnLean.Proofs.Channel.SighashTargets.funding_and_commitment_signing_contract
#print axioms LnLean.Proofs.Channel.SighashTargets.producedFrom_not_sighashProduces
#print axioms LnLean.Proofs.Conformance.Diff.Transport.transportFrame_size
#print axioms LnLean.Wire.Transport.unframeTransport_transportFrame
#print axioms LnLean.Proofs.Conformance.Diff.payload_decoder_rejects_transport_frame
#print axioms LnLean.Proofs.Conformance.Diff.diff_bigsize_decode_65535
#print axioms LnLean.Proofs.Channel.StateTransitionTargets.updateStep_preserves_ledger
#print axioms LnLean.Proofs.Channel.StateTransitionTargets.updateStep_preserves_reserve
#print axioms LnLean.Proofs.Channel.StateTransitionTargets.committedAdd_eq_updateAddHtlc
#print axioms LnLean.Proofs.Channel.StateTransitionTargets.affordableAdd_implies_e37
#print axioms LnLean.Proofs.Bitcoin.FundingLinkTargets.fundingScriptPubKey_eq_p2wsh_ordered
#print axioms LnLean.Proofs.Bitcoin.FundingLinkTargets.acceptChannel_funding_link_ordered
#print axioms LnLean.Proofs.Routing.GossipKeyConsistencyTargets.gossip_graph_edges_directional_key_endpoint
#print axioms LnLean.Proofs.Routing.GossipKeyConsistencyTargets.canonical_directional_attribution_unique
#print axioms LnLean.Proofs.Routing.GossipKeyConsistencyTargets.conflicting_announcements_ambiguous_without_canonical
#print axioms LnLean.Proofs.Security.Limits.EventReduction.secure
#print axioms LnLean.Proofs.Security.Limits.AdvantageReduction.bound
#print axioms LnLean.Proofs.Security.Limits.composite_bound
#print axioms LnLean.Proofs.Security.Limits.algebraic_c1_no_collision
#print axioms LnLean.Proofs.Security.Limits.algebraic_c3_no_binding_failure
#print axioms LnLean.Proofs.Security.Limits.algebraic_c8_no_tag_collision
#print axioms LnLean.Proofs.Security.Limits.secure_game_unbounded_advantage

/-! ## 19. Wave 6 sighash, revocation, commitment, and canonical gossip targets -/

#print axioms LnLean.Bitcoin.Sighash.sighashWitnessV0_eq_vendorImpl
#print axioms LnLean.Bitcoin.Sighash.sighashWitnessV0_eq_interface
#print axioms LnLean.Bitcoin.Sighash.sighashWitnessV0_size
#print axioms LnLean.Proofs.Bitcoin.SighashBridgeTargets.checker_consumes_model_digest
#print axioms LnLean.Proofs.Bitcoin.SighashBridgeTargets.funding_sighash_interpreters_agree
#print axioms LnLean.Proofs.Bitcoin.SighashBridgeTargets.toLocal_sighash_interpreters_agree
#print axioms LnLean.Proofs.Bitcoin.SighashBridgeTargets.digest_commits_scriptCode
#print axioms LnLean.Proofs.Bitcoin.InterpreterRevocationTargets.toLocal_revocation_interpreters_agree
#print axioms LnLean.Proofs.Bitcoin.InterpreterRevocationTargets.toLocal_revocation_wrong_key_rejected
#print axioms LnLean.Proofs.Bitcoin.InterpreterRevocationTargets.toLocal_revocation_delayed_key_sig_rejected
#print axioms LnLean.Proofs.Bitcoin.InterpreterRevocationTargets.toLocal_delayed_csv_failure_agree
#print axioms LnLean.Proofs.Channel.CommitmentTypes.Commitment.migrateNet_conservation
#print axioms LnLean.Proofs.Channel.CommitmentTypes.CommitmentTx.migrateNet_outputsNet_perm_commitmentOutputs
#print axioms LnLean.Proofs.Channel.CommitmentTypes.CommitmentTx.migrateNet_canonicalOutputs_eq_commitmentOutputs
#print axioms LnLean.Proofs.Channel.CommitmentTypes.Commitment.effectiveFee_eq_feeSat_add_trimmedTotalSat
#print axioms LnLean.Proofs.Channel.SighashTargets.CommitmentWire.txBytes_parse
#print axioms LnLean.Proofs.Channel.SighashTargets.exactSighashDigest_size
#print axioms LnLean.Proofs.Channel.SighashTargets.commitmentDigest_eq_of_shared
#print axioms LnLean.Proofs.Channel.SighashTargets.vectorCommitmentTx_size
#print axioms LnLean.Proofs.Channel.SighashTargets.Bip143Preimage.preimageBytes_size
#print axioms LnLean.Proofs.Channel.SighashViewBindingTargets.commitmentSignature_binds_view
#print axioms LnLean.Proofs.Channel.SighashViewBindingTargets.commitmentSignature_binds_viewOfState
#print axioms LnLean.Proofs.Channel.SighashViewBindingTargets.htlcSignature_binds_htlcView
#print axioms LnLean.Proofs.Channel.SighashViewBindingTargets.digest_binding_not_view_binding
#print axioms LnLean.Proofs.Channel.CommitmentDanceTargets.danceReachable_revoked_never_current
#print axioms LnLean.Proofs.Channel.CommitmentDanceTargets.danceReachable_preserves_ledger
#print axioms LnLean.Proofs.Channel.CommitmentDanceTargets.dance_round_closes
#print axioms LnLean.Proofs.Routing.GossipCanonicalTargets.reachableCanonical_nodeKeyConsistent
#print axioms LnLean.Proofs.Routing.GossipCanonicalTargets.reachableCanonical_directional_key_endpoint
#print axioms LnLean.Proofs.Routing.GossipCanonicalTargets.reachableCanonical_attribution_unique

/-! ## 20. Wave 7 sequence, preimage, consumer, fold, gossip, key, and funding targets -/

#print axioms LnLean.Proofs.Bitcoin.SequenceContextTargets.checkSequenceDef_delay_iff
#print axioms LnLean.Proofs.Bitcoin.SequenceContextTargets.toLocal_delayed_sequence_context_refinement
#print axioms LnLean.Proofs.Bitcoin.SequenceContextTargets.toLocal_delayed_realChecker_refinement
#print axioms LnLean.Proofs.Bitcoin.SequenceContextTargets.toLocal_delayed_sequence_interpreters_agree
#print axioms LnLean.Proofs.Bitcoin.SequenceContextTargets.verifyWitnessProgram_toLocal_delayed_bad_sig
#print axioms LnLean.Proofs.Channel.SighashTargets.Bip143Preimage.preimageBytes_eq_encode_bytes
#print axioms LnLean.Proofs.Channel.SighashTargets.Bip143Preimage.preimageBytes_eq_bip143MsgL_ofTx
#print axioms LnLean.Proofs.Channel.SighashTargets.commitmentBip143Preimage_eq_bip143MsgL
#print axioms LnLean.Proofs.Channel.SighashTargets.vectorWirePreimage_vendor
#print axioms LnLean.Proofs.Channel.CommitmentConsumer.netConsumerOutputs_perm_migratedConsumerOutputs
#print axioms LnLean.Proofs.Channel.CommitmentConsumer.migratedConsumerOutputs_eq_consumerOutputs_of_migrated
#print axioms LnLean.Proofs.Channel.CommitmentConsumer.coversMigratedOutputs_iff_legacy_of_migrated
#print axioms LnLean.Proofs.Channel.CommitmentConsumer.legacyCoverage_not_preserved_by_net_migration
#print axioms LnLean.Proofs.Channel.ProtocolEventFoldTargets.guardedStep_iff_step_and_guards
#print axioms LnLean.Proofs.Channel.ProtocolEventFoldTargets.danceStep_iff_guardedStep
#print axioms LnLean.Proofs.Channel.ProtocolEventFoldTargets.guardedUpdateReachable_preserves_ordered
#print axioms LnLean.Proofs.Channel.ProtocolEventFoldTargets.guardedUpdateReachable_current_not_revoked
#print axioms LnLean.Proofs.Channel.ProtocolEventFoldTargets.literal_round_fold_refuted
#print axioms LnLean.Proofs.Channel.ProtocolEventFoldTargets.literal_revoke_fold_refuted
#print axioms LnLean.Proofs.Channel.ProtocolEventFoldTargets.fold_cannot_both_preserve_balance_and_carry_add
#print axioms LnLean.Proofs.Routing.GossipRawRefinementTargets.applyGossipCanonicalStore_gossip_toNetwork
#print axioms LnLean.Proofs.Routing.GossipRawRefinementTargets.reachableCanonicalStore_invariant
#print axioms LnLean.Proofs.Routing.GossipRawRefinementTargets.canonical_admission_strictly_weaker_than_raw_clock
#print axioms LnLean.Proofs.Routing.GossipRawRefinementTargets.no_canonical_preserving_raw_announcement_extension
#print axioms LnLean.Proofs.Bitcoin.FundingAuthTargets.openAccept_hash_linked
#print axioms LnLean.Proofs.Bitcoin.FundingAuthTargets.openAccept_output_determines_key_set
#print axioms LnLean.Proofs.Bitcoin.FundingAuthTargets.same_message_distinct_senders
#print axioms LnLean.Proofs.Crypto.KeyModelTargets.funding_signature_attribution
#print axioms LnLean.Proofs.Crypto.KeyModelTargets.key_generation_not_key_attribution
#print axioms LnLean.Proofs.Crypto.KeyModelTargets.attribution_contract_nonvacuous
#print axioms LnLean.Proofs.Crypto.KeyModelTargets.fundingSigningLaw_sign_injective
#print axioms LnLean.Proofs.Bitcoin.EcdsaBridgeTargets.fundingSignedValid_iff_vendor
#print axioms LnLean.Proofs.Bitcoin.EcdsaBridgeTargets.funding_sighash_interpreters_agree_vendor
#print axioms LnLean.Proofs.Bitcoin.TxValidTransferTargets.txCheckerFor_some_eq_realCheckerOf
#print axioms LnLean.Proofs.Bitcoin.TxValidTransferTargets.toLocal_delayed_txCheckerFor_refinement
#print axioms LnLean.Proofs.Bitcoin.EcdsaBridgeTargets.model_verify_eq_realChecker_seam
#print axioms LnLean.Proofs.Bitcoin.EcdsaBridgeTargets.toLocal_revocation_interpreters_agree_vendor
#print axioms LnLean.Proofs.Protocol.OpenChannelWireTargets.openChannelWire_end_to_end
#print axioms LnLean.Protocol.OpenChannelWire.toFundingParams_hash_linked
#print axioms LnLean.Proofs.Protocol.OpenChannelWireTargets.acceptKey_bound_before_fundingCreated_wire
#print axioms LnLean.Proofs.Crypto.AcceptPayloadTargets.stored_accept_payload_attribution
#print axioms LnLean.Proofs.Crypto.AcceptPayloadTargets.acceptPayload_not_proof_of_possession
#print axioms LnLean.Proofs.Channel.HtlcPreimageTargets.htlcBip143Preimage_eq_bip143MsgL
#print axioms LnLean.Proofs.Channel.HtlcPreimageTargets.HtlcSpend.successPreimage_eq_bip143MsgL
#print axioms LnLean.Proofs.Channel.HtlcPreimageTargets.HtlcSpend.timeoutPreimage_eq_bip143MsgL
#print axioms LnLean.Proofs.Channel.HtlcPreimageTargets.htlc_preimage_target_summary
#print axioms LnLean.Proofs.Channel.CommitmentConsumerSites.commitment_signed_full_covers_migrated
#print axioms LnLean.Proofs.Channel.CommitmentConsumerSites.migratedConsumerOutputs_eq_viewOfState_outputs
#print axioms LnLean.Proofs.Channel.CommitmentConsumerSites.viewOfState_outputs_perm_netConsumerOutputs
#print axioms LnLean.Proofs.Routing.GossipStoreEpochTargets.epochFold_gossip_eq_canonicalStoreView_rawFold
#print axioms LnLean.Routing.replacedUpdates_timestamp_lt
#print axioms LnLean.Proofs.Routing.GossipStoreEpochTargets.StoreEpoch.epochFold_store_eq_foldl

/-! ## 21. Wave 8 headline targets -/

#print axioms LnLean.Proofs.WaveH.H01.txCheckerFor_some_eq_realCheckerOf
#print axioms LnLean.Proofs.WaveH.H04.scriptLaneTx_oneInput_ok_iff
#print axioms LnLean.Proofs.WaveH.H07.htlcBip143Preimage_eq_bip143MsgL
#print axioms LnLean.Proofs.WaveH.H08.htlcWirePreimage_eq_bip143MsgL
#print axioms LnLean.Proofs.WaveH.H09.htlcBip143Preimage_digest_eq_signatureHashBip143Impl
#print axioms LnLean.Proofs.WaveH.H13.fixedPayloadLength_eq_319
#print axioms LnLean.Proofs.WaveH.H30.funding_txCheckerFor_verify_and_spend
#print axioms LnLean.Proofs.WaveH.H33.h33_anchor_weight_target
#print axioms LnLean.Proofs.WaveH.H34.c1_model_collides_on_71_byte_funding_scripts
#print axioms LnLean.Proofs.WaveH.H39.epochStep_semantics
#print axioms LnLean.Proofs.WaveH.H43.eventual_delivery_of_fair_attempts
#print axioms LnLean.Proofs.WaveH.H45.channel_reorg_preserves

/-! ## 22. Wave 10 headline targets -/

#print axioms LnLean.Proofs.Bitcoin.EcdsaDomainTargets.not_digestBindsMod_any_tag
#print axioms LnLean.Proofs.Bitcoin.EcdsaDomainTargets.no_digestBindsMod_anywhere
#print axioms LnLean.Proofs.Bitcoin.EcdsaDomainTargets.not_digestBindsModOn33_any_tag
#print axioms LnLean.Proofs.Bitcoin.EcdsaDomainTargets.digestBindsModOn_canonical33
#print axioms LnLean.Proofs.Bitcoin.EcdsaDomainTargets.digestBindsModOn_canonical32
#print axioms LnLean.Proofs.Bitcoin.EcdsaDomainTargets.residueBinding_vendor_funding_eq_of_canonical33
#print axioms LnLean.Proofs.Bitcoin.EcdsaDomainTargets.digest_domain_dichotomy
#print axioms LnLean.Proofs.Protocol.TransportAuthTargets.transport_authenticated_attributed
#print axioms LnLean.Proofs.Protocol.TransportAuthTargets.authenticated_delivery_reaches_fundingCreated
#print axioms LnLean.Proofs.Protocol.TransportAuthTargets.authenticated_open_reaches_funding
#print axioms LnLean.Proofs.Protocol.TransportAuthTargets.transport_auth_not_from_wire
#print axioms LnLean.Proofs.Protocol.TransportAuthTargets.unattributed_delivery_exists
#print axioms LnLean.Proofs.Protocol.TransportAuthTargets.no_session_binding_counterexample
#print axioms LnLean.Proofs.Protocol.TransportAuthTargets.no_wire_sender_function
#print axioms LnLean.Proofs.Protocol.TransportAuthTargets.transport_auth_summary
#print axioms LnLean.Proofs.Crypto.PopProtocolTargets.challengeMessage_injective_of_valid
#print axioms LnLean.Proofs.Crypto.PopProtocolTargets.accepts_challenge_bound
#print axioms LnLean.Proofs.Crypto.PopProtocolTargets.no_cross_session_replay
#print axioms LnLean.Proofs.Crypto.PopProtocolTargets.advertised_honest_completeness
#print axioms LnLean.Proofs.Crypto.PopProtocolTargets.storedAccept_honest_registration
#print axioms LnLean.Proofs.Crypto.PopProtocolTargets.accepted_owns
#print axioms LnLean.Proofs.Crypto.PopProtocolTargets.accepted_funding_attribution
#print axioms LnLean.Proofs.Crypto.PopProtocolTargets.popSound_of_keySoundOn
#print axioms LnLean.Proofs.Crypto.PopProtocolTargets.accepted_stored_registration_attribution
#print axioms LnLean.Proofs.Crypto.PopProtocolTargets.unbound_replay_accepts
#print axioms LnLean.Proofs.Crypto.PopProtocolTargets.nonceFree_replay_accepts
#print axioms LnLean.Proofs.Crypto.PopProtocolTargets.challengeMessage_not_injective_without_valid
#print axioms LnLean.Proofs.Crypto.PopProtocolTargets.binding_fails_without_valid
#print axioms LnLean.Proofs.Crypto.PopProtocolTargets.repeated_challenge_replay
#print axioms LnLean.Proofs.Crypto.PopProtocolTargets.keySound_not_provenance
#print axioms LnLean.Proofs.Crypto.PopProtocolTargets.protocol_nonvacuous
#print axioms LnLean.Proofs.Crypto.PopProtocolTargets.pop_protocol_summary
#print axioms LnLean.Proofs.Channel.CoverageWitnessTargets.decodeCoverage_canonical
#print axioms LnLean.Proofs.Channel.CoverageWitnessTargets.decodeCoverage_covers
#print axioms LnLean.Proofs.Channel.CoverageWitnessTargets.no_legacy_only_coverage_decoder
#print axioms LnLean.Proofs.Channel.CoverageWitnessTargets.no_legacy_only_witness_selector
#print axioms LnLean.Proofs.Channel.CoverageWitnessTargets.wire_admits_distinct_coverage_witnesses
#print axioms LnLean.Proofs.Channel.CoverageWitnessTargets.amount_is_necessary
#print axioms LnLean.Proofs.Channel.CoverageWitnessTargets.toCommitmentHtlcOutput_eq_iff
#print axioms LnLean.Proofs.Channel.CoverageWitnessTargets.coverage_witness_summary
#print axioms LnLean.Proofs.Routing.NodeIdentityTargets.canonical_distinct_nodes_no_oriented_store_link
#print axioms LnLean.Proofs.Routing.NodeIdentityTargets.no_store_function_selects_both_rotation_worlds
#print axioms LnLean.Proofs.Routing.NodeIdentityTargets.concrete_intended_rotation_not_storeOnly
#print axioms LnLean.Proofs.Routing.NodeIdentityTargets.rotation_preserves_wireMember
#print axioms LnLean.Proofs.Routing.NodeIdentityTargets.rotation_not_signature_preserving
#print axioms LnLean.Proofs.Routing.NodeIdentityTargets.channelAnnouncement_admitted_of_wireMember
#print axioms LnLean.Proofs.Routing.NodeIdentityTargets.missing_endpoint_channel_admitted
#print axioms LnLean.Proofs.Routing.NodeIdentityTargets.wireMember_applyGossipNodeCanonical
#print axioms LnLean.Proofs.Routing.NodeIdentityTargets.graphBacked_of_nodeKeyConsistent
#print axioms LnLean.Proofs.Conformance.Diff.diff_msg_open_channel_payload
#print axioms LnLean.Proofs.Conformance.Diff.diff_msg_open_channel_length
#print axioms LnLean.Proofs.Conformance.Diff.diff_msg_open_channel_transport
#print axioms LnLean.Proofs.Conformance.Diff.diff_msg_open_channel_header
#print axioms LnLean.Proofs.Conformance.Diff.diff_msg_open_channel_frame_prefix

#print axioms LnLean.Proofs.Security.ChainFinalityTargets.bounded_depth_finality
#print axioms LnLean.Proofs.Security.ChainFinalityTargets.confirmed_tx_not_reorged
#print axioms LnLean.Proofs.Security.ChainFinalityTargets.unique_tip_finality
#print axioms LnLean.Proofs.Security.ChainFinalityTargets.depth_bound_necessary
#print axioms LnLean.Proofs.Security.ChainFinalityTargets.deep_reorg_evicts
#print axioms LnLean.Proofs.Security.ChainFinalityTargets.chain_finality_and_retention
#print axioms LnLean.Proofs.Routing.NodeIdentityChainTargets.RotationCertificate.signed_implies_link
#print axioms LnLean.Proofs.Routing.NodeIdentityChainTargets.RotationChain.authenticated_comp
#print axioms LnLean.Proofs.Routing.NodeIdentityChainTargets.RotationChain.authenticated_hop_links
#print axioms LnLean.Proofs.Routing.NodeIdentityChainTargets.RotationChain.acyclic_start_not_mem_tail
#print axioms LnLean.Proofs.Routing.NodeIdentityChainTargets.distinct_hops_not_acyclic
#print axioms LnLean.Proofs.Routing.NodeIdentityChainTargets.opaque_link_not_authenticated
#print axioms LnLean.Proofs.Routing.NodeIdentityChainTargets.ResignedChannel.wireMember
#print axioms LnLean.Proofs.Routing.NodeIdentityChainTargets.SignedResignation.admitted
#print axioms LnLean.Proofs.Routing.NodeIdentityChainTargets.old_signature_does_not_authenticate_new_keys
#print axioms LnLean.Proofs.Routing.NodeIdentityChainTargets.signature_preservation_not_universal
#print axioms LnLean.Proofs.Routing.NodeIdentityChainTargets.NodeRateState.replay_rejected
#print axioms LnLean.Proofs.Routing.NodeIdentityChainTargets.rateFold_replay_rejected
#print axioms LnLean.Proofs.Routing.NodeIdentityChainTargets.nonvacuity_witness
#print axioms LnLean.Proofs.Protocol.NoiseTransportTargets.accepted_frame_bound_to_peer
#print axioms LnLean.Proofs.Protocol.NoiseTransportTargets.sessionKeyBinding_iff_peerStatic_eq
#print axioms LnLean.Proofs.Protocol.NoiseTransportTargets.accepted_frame_yields_sessionKeyBinding
#print axioms LnLean.Proofs.Protocol.NoiseTransportTargets.accepted_frame_attributed_delivery
#print axioms LnLean.Proofs.Protocol.NoiseTransportTargets.accepted_frame_reaches_fundingCreated
#print axioms LnLean.Proofs.Protocol.NoiseTransportTargets.replay_rejected_with_freshness
#print axioms LnLean.Proofs.Protocol.NoiseTransportTargets.replay_accepted_without_nonce_freshness
#print axioms LnLean.Proofs.Protocol.NoiseTransportTargets.key_substitution_without_peer_binding
#print axioms LnLean.Proofs.Protocol.NoiseTransportTargets.acceptance_not_attribution
#print axioms LnLean.Proofs.Protocol.NoiseTransportTargets.noise_does_not_authenticate_payload
#print axioms LnLean.Proofs.Protocol.NoiseTransportTargets.no_wire_session_binding_function
#print axioms LnLean.Proofs.Protocol.NoiseTransportTargets.noise_transport_nonvacuous
#print axioms LnLean.Proofs.Protocol.NoiseTransportTargets.noise_transport_summary
#print axioms LnLean.Proofs.Channel.CoverageSourceTargets.decodeSource_fullRecord_exact
#print axioms LnLean.Proofs.Channel.CoverageSourceTargets.decodeSource_outOfBand_canonical
#print axioms LnLean.Proofs.Channel.CoverageSourceTargets.decodeSource_extensionOfFull_canonical
#print axioms LnLean.Proofs.Channel.CoverageSourceTargets.extension_plus_wire_determines_coverage
#print axioms LnLean.Proofs.Channel.CoverageSourceTargets.no_wire_determined_source
#print axioms LnLean.Proofs.Channel.CoverageSourceTargets.no_wire_source_selector
#print axioms LnLean.Proofs.Channel.CoverageSourceTargets.wire_admits_distinct_out_of_band_witnesses
#print axioms LnLean.Proofs.Channel.CoverageSourceTargets.wireCompatible_not_out_of_band_binding
#print axioms LnLean.Proofs.Channel.CoverageSourceTargets.no_wire_witness_authenticator
#print axioms LnLean.Proofs.Channel.CoverageSourceTargets.coverage_source_summary
#print axioms LnLean.Proofs.Payment.InvoiceWireTargets.parse_print_paymentHash
#print axioms LnLean.Proofs.Payment.InvoiceWireTargets.wire_paymentHash_binding
#print axioms LnLean.Proofs.Payment.InvoiceWireTargets.preimage_unique_of_injective
#print axioms LnLean.Proofs.Payment.InvoiceWireTargets.preimage_determines_hash
#print axioms LnLean.Proofs.Payment.InvoiceWireTargets.paymentHash_eq_iff_bytes
#print axioms LnLean.Proofs.Payment.InvoiceWireTargets.signature_not_payment
#print axioms LnLean.Proofs.Payment.InvoiceWireTargets.signatureOnly_verifies
#print axioms LnLean.Proofs.Payment.InvoiceWireTargets.signatureOnly_no_preimage
#print axioms LnLean.Proofs.Payment.InvoiceWireTargets.signature_only_separates_verify_from_payment
#print axioms LnLean.Proofs.Payment.InvoiceWireTargets.paymentSecret_eq_iff_bytes
#print axioms LnLean.Proofs.Payment.InvoiceWireTargets.parse_print_paymentSecret
#print axioms LnLean.Proofs.Payment.InvoiceWireTargets.wire_paymentSecret_binding
#print axioms LnLean.Proofs.Payment.InvoiceWireTargets.toInvoice_valid
#print axioms LnLean.Proofs.Channel.HtlcAggregate.Aggregate.aggregate_coverage_projection
#print axioms LnLean.Proofs.Channel.HtlcAggregate.Aggregate.coverageValue_eq_sum
#print axioms LnLean.Proofs.Channel.HtlcAggregate.no_double_spend_of_noAliasing
#print axioms LnLean.Proofs.Channel.HtlcAggregate.same_spend_distinct_records_imp_aliasing
#print axioms LnLean.Proofs.Channel.HtlcAggregate.aliasing_double_spend_witness
#print axioms LnLean.Proofs.Channel.HtlcAggregate.AggregateTx.weight_eq
#print axioms LnLean.Proofs.Channel.HtlcAggregate.AggregateTx.not_funded_of_output_add_fee_gt
#print axioms LnLean.Proofs.Channel.HtlcAggregate.no_legacy_only_aggregate_coverage_decoder
#print axioms LnLean.Proofs.Payment.InvoiceWireTargets.parseFields_printFields
#print axioms LnLean.Proofs.Payment.InvoiceWireTargets.parse_print
#print axioms LnLean.Proofs.Payment.InvoiceWireTargets.print_injective
#print axioms LnLean.Proofs.Payment.InvoiceWireTargets.witness_parse
#print axioms LnLean.Proofs.Payment.InvoiceWireTargets.malformed_parse_none
#print axioms LnLean.Proofs.Payment.InvoiceWireTargets.duplicateHash_parse_none
#print axioms LnLean.Proofs.Payment.InvoiceWireTargets.decodeHop_encodeHop
#print axioms LnLean.Proofs.Payment.InvoiceWireTargets.encodeHop_size
#print axioms LnLean.Proofs.Model.NonVacuityTargets.witnessRegistry_sound
#print axioms LnLean.Proofs.Model.NonVacuityTargets.witnessRegistry_length
#print axioms LnLean.Proofs.Model.NonVacuityTargets.witnessRegistry_ids_nodup
#print axioms LnLean.Proofs.Model.NonVacuityTargets.withVendorEcdsa_accepts_nothing
#print axioms LnLean.Proofs.Model.NonVacuityTargets.withVendorEcdsa_funding_uninhabited
#print axioms LnLean.Proofs.Model.NonVacuityTargets.vacuous_nonvacuous_separation
#print axioms LnLean.Proofs.Model.NonVacuityTargets.witness_not_universal
#print axioms LnLean.Proofs.Model.NonVacuityTargets.witnessRegistry_ne_nil
#print axioms LnLean.Proofs.Conformance.Diff.diff_msg_accept_channel_length
#print axioms LnLean.Proofs.Conformance.Diff.diff_msg_accept_channel_transport
#print axioms LnLean.Proofs.Conformance.Diff.diff_msg_accept_channel_header
#print axioms LnLean.Proofs.Conformance.Diff.diff_msg_accept_channel_frame_prefix
#print axioms LnLean.Proofs.Conformance.Diff.diff_msg_accept_channel_payload

/-! ## 15. Registry

  The registry is a plain list of fully-qualified names.  Keeping it in the
  same module as the `#print axioms` commands lets the length proof below
  fail if the audit list and the commands drift apart.
-/

def auditedTheorems : List Lean.Name :=
  [ `LnLean.Proofs.conserved_no_value_creation,
    `LnLean.Proofs.ledger_no_value_creation,
    `LnLean.Proofs.penaltySweep_conserved,
    `LnLean.Proofs.trace_conserved,
    `LnLean.Proofs.settleHTLCOutputAt_conserved,
    `LnLean.Proofs.Channel.HTLCProps.fulfill_succeeds,
    `LnLean.Proofs.Channel.HTLCProps.fulfilled_failed_exclusive,
    `LnLean.Proofs.Channel.HTLCProps.settlement_terminal,
    `LnLean.Proofs.Channel.HTLCProps.dust_no_output_but_in_set,
    `LnLean.Channel.deriveRevocationPubkey_point_injective,
    `LnLean.Channel.no_secret_reuse,
    `LnLean.Channel.old_revoked_by_revealed_secret,
    `LnLean.Proofs.Channel.penaltyValid_sweep_eq_total_sub_fee,
    `LnLean.Proofs.Channel.not_penaltyValid_of_window_closed,
    `LnLean.Channel.current_commitment_not_punishable,
    `LnLean.Channel.step_allowedPhaseTransition,
    `LnLean.Channel.step_phaseRank_monotone,
    `LnLean.Channel.step_deterministic,
    `LnLean.Channel.step_preserves_identity,
    `LnLean.Channel.trace_to_normal_contains_fundingLocked,
    `LnLean.Routing.GossipProps.viewGraph_wellFormed,
    `LnLean.Routing.GossipProps.uniqueBindings_applyUpdate,
    `LnLean.Routing.GossipProps.announcement_materialises_wellFormed,
    `LnLean.Routing.findEdge_noSelfLoop,
    `LnLean.Routing.simplePaths_walk,
    `LnLean.Routing.sealRoute_peelExactly_final,
    `LnLean.Routing.peelExactly_layerCount,
    `LnLean.Routing.wireSize_eq_1366,
    `LnLean.Routing.recorded_error_bounded,
    `LnLean.Payment.MPPProps.mppComplete_sum_eq_target,
    `LnLean.Payment.MPPProps.mppComplete_no_part_exceeds_target,
    `LnLean.Payment.MPPProps.settleParts_allOrNothing_succeeded,
    `LnLean.Payment.MPPProps.allOrNothing_no_mixed,
    `LnLean.Payment.valid_paymentHash_size,
    `LnLean.Payment.decodeSemantic_valid,
    `LnLean.Payment.verify_iff_valid_and_check,
    `LnLean.Payment.verify_authorized_under_assumption,
    `LnLean.Proofs.Liveness.fair_awaitingLockin_eventually_normal,
    `LnLean.Proofs.Liveness.awaitingLockin_reaches_normal,
    `LnLean.Proofs.Liveness.pending_htlc_eventually_resolved,
    `LnLean.Proofs.Liveness.reconnect_preserves_channelReady,
    `LnLean.Wire.decodeTLV_encodeTLV,
    `LnLean.Wire.encode_size_eq,
    `LnLean.Wire.decodeBigSize_encodeBigSize,
    `LnLean.Crypto.verifyFundingChecked_sound,
    `LnLean.Crypto.no_cross_domain_reuse_funding_commitment,
    `LnLean.Crypto.derFullOK_imp_wireSigOK,
    `LnLean.Proofs.Bitcoin.ScriptProps.toRemote_templates_distinct,
    `LnLean.Proofs.Bitcoin.ScriptProps.htlcTemplates_distinct,
    `LnLean.Proofs.Bitcoin.ScriptProps.toLocal_contains_revocationKey,
    `LnLean.Proofs.Bitcoin.FundingProps.witnessScript_is_2of2_over_funding_keys,
    `LnLean.Proofs.Bitcoin.FundingProps.FundingConfirmed.script_is_p2wsh,
    `LnLean.Proofs.Bitcoin.FundingProps.confirm_preserves_funding,
    `LnLean.Proofs.Bitcoin.FundingProps.fundingSpend_conditional_2of2_only,
    `LnLean.Crypto.Hash.paymentHash_sha256_contract,
    `LnLean.Crypto.Sig.commitmentSig_contract,
    `LnLean.Crypto.Hash.onionHmacTag_size_and_bindsOn,
    `LnLean.Channel.Commitment.outputs_nonnegative,
    `LnLean.Channel.HTLC.amount_conservation,
    `LnLean.Protocol.Handshake.open_bounds,
    `LnLean.Protocol.Handshake.feature_intersection,
    `LnLean.Proofs.Liveness.penalty_economical,
    `LnLean.Proofs.Bitcoin.FundingScriptTargets.fundingScriptPubKey_eq_p2wsh_twoOfTwo,
    `LnLean.Proofs.Security.ReorgTargets.reorg_preserves_channel_safety,
    `LnLean.Proofs.Security.ReorgTargets.deep_reorg_separate_failure_mode,
    `LnLean.Proofs.Bitcoin.ToLocalScriptTargets.toLocalScriptFull_carries_csv_and_revocationKey,
    `LnLean.Proofs.Bitcoin.ToLocalScriptTargets.toLocalScriptFull_commits_delay_and_revocationKey,
    `LnLean.Proofs.Bitcoin.ToLocalScriptTargets.commitmentOutputs_toLocal_commits_delay_and_revocationKey,
    `LnLean.Proofs.Bitcoin.commitmentBaseWeight_model_target,
    `LnLean.Wire.TLVStream.wellFormed_iff_pairwise,
    `LnLean.Wire.TLVStream.wellFormed_record_type_unique,
    `LnLean.Channel.Commitment.output_ordering,
    `LnLean.Channel.Fee.commitmentSigningGate_rejected_iff_insufficient,
    `LnLean.Channel.Fee.commitmentSigningGate_rejected_iff_no_checkedSigning,
    `LnLean.Channel.HTLC.dir_id_unique,
    `LnLean.Channel.HTLC.id_unique_of_reachable_cross,
    `LnLean.Protocol.Handshake.funding_signed_signing_contract,
    `LnLean.Proofs.ProtocolCoverageTargets.commitment_signed_covers_exact_of_state,
    `LnLean.Proofs.Routing.GossipTargets.gossip_graph_only_valid_announcements,
    `LnLean.Proofs.Bitcoin.SpendTargets.fundingOutput_spendable_output,
    `LnLean.Proofs.Bitcoin.SpendTargets.fundingConfirmed_spendable_output,
    `LnLean.Proofs.Bitcoin.SpendTargets.toLocalOutput_revocation_spendable_output,
    `LnLean.Proofs.Bitcoin.SpendTargets.toLocalOutput_delayed_spendable_output,
    `LnLean.Proofs.Bitcoin.SpendTargets.commitmentOutputs_toLocal_delayed_spendable,
    `LnLean.Proofs.Bitcoin.SpendTargets.fundingSpendableBy2of2_of_both_sign,
    `LnLean.Proofs.Channel.CommitmentIntegration.legacyOutputs_perm_commitmentOutputs,
    `LnLean.Proofs.Channel.CommitmentIntegration.bolt3CommitmentOfRecords_conservation,
    `LnLean.Proofs.Channel.CommitmentIntegration.dust_trimming_not_perm,
    `LnLean.Channel.HTLC.tagged_id_unique_of_reachable,
    `LnLean.Channel.HTLC.tagged_ids_nodup_of_reachable,
    `LnLean.Channel.HTLC.cross_direction_duplicate_tagged,
    `LnLean.Proofs.ProtocolWireTargets.commitment_signed_full_covers_exact,
    `LnLean.Proofs.ProtocolWireTargets.protocol_wire_summary,
    `LnLean.Proofs.ProtocolWireTargets.legacy_wire_cannot_determine_coverage,
    `LnLean.Proofs.ProtocolWireTargets.projection_forgets_fee_and_number,
    `LnLean.Proofs.Routing.GossipAttributionTargets.gossip_graph_edges_update_attributed,
    `LnLean.Proofs.Routing.GossipAttributionTargets.gossip_graph_edges_update_key_endpoint,
    `LnLean.Proofs.Routing.GossipAttributionTargets.raw_applyGossip_accepts_unannounced_update,
    `LnLean.Proofs.Conformance.bigsize_encode_one_byte_high,
    `LnLean.Proofs.Conformance.bigsize_decode_eight_byte_high,
    `LnLean.Proofs.Conformance.tlv_unknown_even_12_admission,
    `LnLean.Proofs.Bitcoin.InterpreterBridgeTargets.funding_interpreters_agree,
    `LnLean.Proofs.Bitcoin.InterpreterBridgeTargets.toLocal_delayed_interpreters_agree,
    `LnLean.Proofs.Bitcoin.InterpreterBridgeTargets.toLocal_serialize_eq,
    `LnLean.Proofs.Bitcoin.InterpreterBridgeTargets.funding_serialize_eq,
    `LnLean.Channel.CommitmentTx.migratedFrom_outputsNet_perm_commitmentOutputs,
    `LnLean.Channel.CommitmentTx.migratedFrom_conservation,
    `LnLean.Channel.CommitmentTx.migratedFrom_effectiveFee_eq,
    `LnLean.Proofs.Channel.CommitmentGrossNet.d12_output_ordering_fails,
    `LnLean.Proofs.Channel.SighashTargets.SighashProduces.coverage,
    `LnLean.Proofs.Channel.SighashTargets.sighash_summary,
    `LnLean.Proofs.Channel.SighashTargets.funding_and_commitment_signing_contract,
    `LnLean.Proofs.Channel.SighashTargets.producedFrom_not_sighashProduces,
    `LnLean.Proofs.Conformance.Diff.Transport.transportFrame_size,
    `LnLean.Wire.Transport.unframeTransport_transportFrame,
    `LnLean.Proofs.Conformance.Diff.payload_decoder_rejects_transport_frame,
    `LnLean.Proofs.Conformance.Diff.diff_bigsize_decode_65535,
    `LnLean.Proofs.Channel.StateTransitionTargets.updateStep_preserves_ledger,
    `LnLean.Proofs.Channel.StateTransitionTargets.updateStep_preserves_reserve,
    `LnLean.Proofs.Channel.StateTransitionTargets.committedAdd_eq_updateAddHtlc,
    `LnLean.Proofs.Channel.StateTransitionTargets.affordableAdd_implies_e37,
    `LnLean.Proofs.Bitcoin.FundingLinkTargets.fundingScriptPubKey_eq_p2wsh_ordered,
    `LnLean.Proofs.Bitcoin.FundingLinkTargets.acceptChannel_funding_link_ordered,
    `LnLean.Proofs.Routing.GossipKeyConsistencyTargets.gossip_graph_edges_directional_key_endpoint,
    `LnLean.Proofs.Routing.GossipKeyConsistencyTargets.canonical_directional_attribution_unique,
    `LnLean.Proofs.Routing.GossipKeyConsistencyTargets.conflicting_announcements_ambiguous_without_canonical,
    `LnLean.Proofs.Security.Limits.EventReduction.secure,
    `LnLean.Proofs.Security.Limits.AdvantageReduction.bound,
    `LnLean.Proofs.Security.Limits.composite_bound,
    `LnLean.Proofs.Security.Limits.algebraic_c1_no_collision,
    `LnLean.Proofs.Security.Limits.algebraic_c3_no_binding_failure,
    `LnLean.Proofs.Security.Limits.algebraic_c8_no_tag_collision,
    `LnLean.Proofs.Security.Limits.secure_game_unbounded_advantage,
    `LnLean.Bitcoin.Sighash.sighashWitnessV0_eq_vendorImpl,
    `LnLean.Bitcoin.Sighash.sighashWitnessV0_eq_interface,
    `LnLean.Bitcoin.Sighash.sighashWitnessV0_size,
    `LnLean.Proofs.Bitcoin.SighashBridgeTargets.checker_consumes_model_digest,
    `LnLean.Proofs.Bitcoin.SighashBridgeTargets.funding_sighash_interpreters_agree,
    `LnLean.Proofs.Bitcoin.SighashBridgeTargets.toLocal_sighash_interpreters_agree,
    `LnLean.Proofs.Bitcoin.SighashBridgeTargets.digest_commits_scriptCode,
    `LnLean.Proofs.Bitcoin.InterpreterRevocationTargets.toLocal_revocation_interpreters_agree,
    `LnLean.Proofs.Bitcoin.InterpreterRevocationTargets.toLocal_revocation_wrong_key_rejected,
    `LnLean.Proofs.Bitcoin.InterpreterRevocationTargets.toLocal_revocation_delayed_key_sig_rejected,
    `LnLean.Proofs.Bitcoin.InterpreterRevocationTargets.toLocal_delayed_csv_failure_agree,
    `LnLean.Proofs.Channel.CommitmentTypes.Commitment.migrateNet_conservation,
    `LnLean.Proofs.Channel.CommitmentTypes.CommitmentTx.migrateNet_outputsNet_perm_commitmentOutputs,
    `LnLean.Proofs.Channel.CommitmentTypes.CommitmentTx.migrateNet_canonicalOutputs_eq_commitmentOutputs,
    `LnLean.Proofs.Channel.CommitmentTypes.Commitment.effectiveFee_eq_feeSat_add_trimmedTotalSat,
    `LnLean.Proofs.Channel.SighashTargets.CommitmentWire.txBytes_parse,
    `LnLean.Proofs.Channel.SighashTargets.exactSighashDigest_size,
    `LnLean.Proofs.Channel.SighashTargets.commitmentDigest_eq_of_shared,
    `LnLean.Proofs.Channel.SighashTargets.vectorCommitmentTx_size,
    `LnLean.Proofs.Channel.SighashTargets.Bip143Preimage.preimageBytes_size,
    `LnLean.Proofs.Channel.SighashViewBindingTargets.commitmentSignature_binds_view,
    `LnLean.Proofs.Channel.SighashViewBindingTargets.commitmentSignature_binds_viewOfState,
    `LnLean.Proofs.Channel.SighashViewBindingTargets.htlcSignature_binds_htlcView,
    `LnLean.Proofs.Channel.SighashViewBindingTargets.digest_binding_not_view_binding,
    `LnLean.Proofs.Channel.CommitmentDanceTargets.danceReachable_revoked_never_current,
    `LnLean.Proofs.Channel.CommitmentDanceTargets.danceReachable_preserves_ledger,
    `LnLean.Proofs.Channel.CommitmentDanceTargets.dance_round_closes,
    `LnLean.Proofs.Routing.GossipCanonicalTargets.reachableCanonical_nodeKeyConsistent,
    `LnLean.Proofs.Routing.GossipCanonicalTargets.reachableCanonical_directional_key_endpoint,
    `LnLean.Proofs.Routing.GossipCanonicalTargets.reachableCanonical_attribution_unique,
    `LnLean.Proofs.Bitcoin.SequenceContextTargets.checkSequenceDef_delay_iff,
    `LnLean.Proofs.Bitcoin.SequenceContextTargets.toLocal_delayed_sequence_context_refinement,
    `LnLean.Proofs.Bitcoin.SequenceContextTargets.toLocal_delayed_realChecker_refinement,
    `LnLean.Proofs.Bitcoin.SequenceContextTargets.toLocal_delayed_sequence_interpreters_agree,
    `LnLean.Proofs.Bitcoin.SequenceContextTargets.verifyWitnessProgram_toLocal_delayed_bad_sig,
    `LnLean.Proofs.Channel.SighashTargets.Bip143Preimage.preimageBytes_eq_encode_bytes,
    `LnLean.Proofs.Channel.SighashTargets.Bip143Preimage.preimageBytes_eq_bip143MsgL_ofTx,
    `LnLean.Proofs.Channel.SighashTargets.commitmentBip143Preimage_eq_bip143MsgL,
    `LnLean.Proofs.Channel.SighashTargets.vectorWirePreimage_vendor,
    `LnLean.Proofs.Channel.CommitmentConsumer.netConsumerOutputs_perm_migratedConsumerOutputs,
    `LnLean.Proofs.Channel.CommitmentConsumer.migratedConsumerOutputs_eq_consumerOutputs_of_migrated,
    `LnLean.Proofs.Channel.CommitmentConsumer.coversMigratedOutputs_iff_legacy_of_migrated,
    `LnLean.Proofs.Channel.CommitmentConsumer.legacyCoverage_not_preserved_by_net_migration,
    `LnLean.Proofs.Channel.ProtocolEventFoldTargets.guardedStep_iff_step_and_guards,
    `LnLean.Proofs.Channel.ProtocolEventFoldTargets.danceStep_iff_guardedStep,
    `LnLean.Proofs.Channel.ProtocolEventFoldTargets.guardedUpdateReachable_preserves_ordered,
    `LnLean.Proofs.Channel.ProtocolEventFoldTargets.guardedUpdateReachable_current_not_revoked,
    `LnLean.Proofs.Channel.ProtocolEventFoldTargets.literal_round_fold_refuted,
    `LnLean.Proofs.Channel.ProtocolEventFoldTargets.literal_revoke_fold_refuted,
    `LnLean.Proofs.Channel.ProtocolEventFoldTargets.fold_cannot_both_preserve_balance_and_carry_add,
    `LnLean.Proofs.Routing.GossipRawRefinementTargets.applyGossipCanonicalStore_gossip_toNetwork,
    `LnLean.Proofs.Routing.GossipRawRefinementTargets.reachableCanonicalStore_invariant,
    `LnLean.Proofs.Routing.GossipRawRefinementTargets.canonical_admission_strictly_weaker_than_raw_clock,
    `LnLean.Proofs.Routing.GossipRawRefinementTargets.no_canonical_preserving_raw_announcement_extension,
    `LnLean.Proofs.Bitcoin.FundingAuthTargets.openAccept_hash_linked,
    `LnLean.Proofs.Bitcoin.FundingAuthTargets.openAccept_output_determines_key_set,
    `LnLean.Proofs.Bitcoin.FundingAuthTargets.same_message_distinct_senders,
    `LnLean.Proofs.Crypto.KeyModelTargets.funding_signature_attribution,
    `LnLean.Proofs.Crypto.KeyModelTargets.key_generation_not_key_attribution,
    `LnLean.Proofs.Crypto.KeyModelTargets.attribution_contract_nonvacuous,
    `LnLean.Proofs.Crypto.KeyModelTargets.fundingSigningLaw_sign_injective,
    `LnLean.Proofs.WaveH.H01.txCheckerFor_some_eq_realCheckerOf,
    `LnLean.Proofs.WaveH.H04.scriptLaneTx_oneInput_ok_iff,
    `LnLean.Proofs.WaveH.H07.htlcBip143Preimage_eq_bip143MsgL,
    `LnLean.Proofs.WaveH.H08.htlcWirePreimage_eq_bip143MsgL,
    `LnLean.Proofs.WaveH.H09.htlcBip143Preimage_digest_eq_signatureHashBip143Impl,
    `LnLean.Proofs.WaveH.H13.fixedPayloadLength_eq_319,
    `LnLean.Proofs.WaveH.H30.funding_txCheckerFor_verify_and_spend,
    `LnLean.Proofs.WaveH.H33.h33_anchor_weight_target,
    `LnLean.Proofs.WaveH.H34.c1_model_collides_on_71_byte_funding_scripts,
    `LnLean.Proofs.WaveH.H39.epochStep_semantics,
    `LnLean.Proofs.WaveH.H43.eventual_delivery_of_fair_attempts,
    `LnLean.Proofs.WaveH.H45.channel_reorg_preserves,
    `LnLean.Proofs.Bitcoin.EcdsaBridgeTargets.fundingSignedValid_iff_vendor,
    `LnLean.Proofs.Bitcoin.EcdsaBridgeTargets.funding_sighash_interpreters_agree_vendor,
    `LnLean.Proofs.Bitcoin.TxValidTransferTargets.txCheckerFor_some_eq_realCheckerOf,
    `LnLean.Proofs.Bitcoin.TxValidTransferTargets.toLocal_delayed_txCheckerFor_refinement,
    `LnLean.Proofs.Bitcoin.EcdsaBridgeTargets.model_verify_eq_realChecker_seam,
    `LnLean.Proofs.Bitcoin.EcdsaBridgeTargets.toLocal_revocation_interpreters_agree_vendor,
    `LnLean.Proofs.Protocol.OpenChannelWireTargets.openChannelWire_end_to_end,
    `LnLean.Protocol.OpenChannelWire.toFundingParams_hash_linked,
    `LnLean.Proofs.Protocol.OpenChannelWireTargets.acceptKey_bound_before_fundingCreated_wire,
    `LnLean.Proofs.Crypto.AcceptPayloadTargets.stored_accept_payload_attribution,
    `LnLean.Proofs.Crypto.AcceptPayloadTargets.acceptPayload_not_proof_of_possession,
    `LnLean.Proofs.Channel.HtlcPreimageTargets.htlcBip143Preimage_eq_bip143MsgL,
    `LnLean.Proofs.Channel.HtlcPreimageTargets.HtlcSpend.successPreimage_eq_bip143MsgL,
    `LnLean.Proofs.Channel.HtlcPreimageTargets.HtlcSpend.timeoutPreimage_eq_bip143MsgL,
    `LnLean.Proofs.Channel.HtlcPreimageTargets.htlc_preimage_target_summary,
    `LnLean.Proofs.Channel.CommitmentConsumerSites.commitment_signed_full_covers_migrated,
    `LnLean.Proofs.Channel.CommitmentConsumerSites.migratedConsumerOutputs_eq_viewOfState_outputs,
    `LnLean.Proofs.Channel.CommitmentConsumerSites.viewOfState_outputs_perm_netConsumerOutputs,
    `LnLean.Proofs.Routing.GossipStoreEpochTargets.epochFold_gossip_eq_canonicalStoreView_rawFold,
    `LnLean.Routing.replacedUpdates_timestamp_lt,
    `LnLean.Proofs.Routing.GossipStoreEpochTargets.StoreEpoch.epochFold_store_eq_foldl,
    `LnLean.Proofs.Bitcoin.EcdsaConcreteTargets.eufCma_vendorVerify_iff_totalReject,
    `LnLean.Proofs.Bitcoin.EcdsaConcreteTargets.bridged_model_totalReject,
    `LnLean.Proofs.Bitcoin.EcdsaConcreteTargets.exists_bridged_model_iff_totalReject,
    `LnLean.Proofs.Bitcoin.EcdsaConcreteTargets.withVendorEcdsa_no_funding,
    `LnLean.Proofs.Bitcoin.EcdsaConcreteTargets.not_digestBindsMod_fundingTag,
    `LnLean.Proofs.Protocol.OpenChannelRoutingTargets.openRoute_initial_to_fundingCreated,
    `LnLean.Proofs.Protocol.OpenChannelRoutingTargets.openChannel_routing_summary,
    `LnLean.Proofs.Protocol.OpenChannelRoutingTargets.unattributed_open_is_routed,
    `LnLean.Proofs.Protocol.OpenChannelRoutingTargets.wire_payload_does_not_determine_sender,
    `LnLean.Proofs.Protocol.OpenChannelRoutingTargets.wire_binding_needs_FundingScript_C1,
    `LnLean.Proofs.Crypto.AttributionGameTargets.stored_registration_funding_attribution,
    `LnLean.Proofs.Crypto.AttributionGameTargets.stored_pop_attribution,
    `LnLean.Proofs.Crypto.AttributionGameTargets.stored_payload_not_possession,
    `LnLean.Proofs.Crypto.AttributionGameTargets.stored_attribution_fails_without_keyBinding,
    `LnLean.Proofs.Crypto.AttributionGameTargets.attribution_game_summary,
    `LnLean.Proofs.Channel.PreimageCoverageTargets.fieldAgreement_iff_eq_ofTx_and_amount,
    `LnLean.Proofs.Channel.PreimageCoverageTargets.FieldAgreement.bytes_eq,
    `LnLean.Proofs.Channel.PreimageCoverageTargets.FieldAgreement.digest_eq_vendor,
    `LnLean.Proofs.Channel.PreimageCoverageTargets.wireSignatureCovers_of_preimage,
    `LnLean.Proofs.Channel.PreimageCoverageTargets.counterPreimageLocktime_bytes_ne,
    `LnLean.Proofs.Channel.PreimageCoverageTargets.counterPreimageAmount_bytes_ne,
    `LnLean.Proofs.Channel.PreimageCoverageTargets.legacy_projection_not_determine_htlc_coverage,
    `LnLean.Proofs.Channel.PreimageCoverageTargets.fieldAgreement_scriptCode_free,
    `LnLean.Proofs.Channel.PreimageCoverageTargets.hash160_image_boundary,
    `LnLean.Proofs.Channel.PreimageCoverageTargets.displayOrderPreimage_not_fieldAgreement,
    `LnLean.Proofs.Channel.PreimageCoverageTargets.vectorHtlcSpend_amount_is_gross,
    `LnLean.Proofs.Channel.PreimageCoverageTargets.preimage_coverage_summary,
    `LnLean.Proofs.Routing.NodeCanonicalTargets.reachableNodeCanonical_node_replacement,
    `LnLean.Proofs.Routing.NodeCanonicalTargets.reachableNodeCanonical_rotation_keeps_both,
    `LnLean.Proofs.Routing.NodeCanonicalTargets.reachableNodeCanonical_equal_timestamp_tie_boundary,
    `LnLean.Proofs.Routing.NodeCanonicalTargets.no_canonical_node_preserving_raw_node_extension,
    `LnLean.Proofs.Routing.NodeCanonicalTargets.canonicalStoreView_does_not_canonicalise_nodes,
    `LnLean.Proofs.Routing.NodeCanonicalTargets.reachableNodeCanonical_node_slot_ignores_global_clock,
    `LnLean.Proofs.Routing.NodeCanonicalTargets.raw_nonrefinement_preserved,
    `LnLean.Proofs.Routing.NodeCanonicalTargets.epoch_square_lifts_to_node_canonical_view,
    `LnLean.Proofs.Routing.NodeCanonicalTargets.canonicalNodeStoreView_nodeCanonical,
    `LnLean.Proofs.Routing.NodeCanonicalTargets.applyGossipNodeCanonical_node_of_admitted,
    `LnLean.Proofs.Conformance.Diff.diff_msg_channel_ready_payload,
    `LnLean.Proofs.Conformance.Diff.diff_msg_channel_ready_length,
    `LnLean.Proofs.Conformance.Diff.diff_msg_channel_ready_transport,
    `LnLean.Proofs.Conformance.Diff.diff_msg_channel_ready_header,
    `LnLean.Proofs.Conformance.Diff.diff_msg_channel_ready_frame_prefix,
    `LnLean.Proofs.Bitcoin.EcdsaDomainTargets.not_digestBindsMod_any_tag,
    `LnLean.Proofs.Bitcoin.EcdsaDomainTargets.no_digestBindsMod_anywhere,
    `LnLean.Proofs.Bitcoin.EcdsaDomainTargets.not_digestBindsModOn33_any_tag,
    `LnLean.Proofs.Bitcoin.EcdsaDomainTargets.digestBindsModOn_canonical33,
    `LnLean.Proofs.Bitcoin.EcdsaDomainTargets.digestBindsModOn_canonical32,
    `LnLean.Proofs.Bitcoin.EcdsaDomainTargets.residueBinding_vendor_funding_eq_of_canonical33,
    `LnLean.Proofs.Bitcoin.EcdsaDomainTargets.digest_domain_dichotomy,
    `LnLean.Proofs.Protocol.TransportAuthTargets.transport_authenticated_attributed,
    `LnLean.Proofs.Protocol.TransportAuthTargets.authenticated_delivery_reaches_fundingCreated,
    `LnLean.Proofs.Protocol.TransportAuthTargets.authenticated_open_reaches_funding,
    `LnLean.Proofs.Protocol.TransportAuthTargets.transport_auth_not_from_wire,
    `LnLean.Proofs.Protocol.TransportAuthTargets.unattributed_delivery_exists,
    `LnLean.Proofs.Protocol.TransportAuthTargets.no_session_binding_counterexample,
    `LnLean.Proofs.Protocol.TransportAuthTargets.no_wire_sender_function,
    `LnLean.Proofs.Protocol.TransportAuthTargets.transport_auth_summary,
    `LnLean.Proofs.Crypto.PopProtocolTargets.challengeMessage_injective_of_valid,
    `LnLean.Proofs.Crypto.PopProtocolTargets.accepts_challenge_bound,
    `LnLean.Proofs.Crypto.PopProtocolTargets.no_cross_session_replay,
    `LnLean.Proofs.Crypto.PopProtocolTargets.advertised_honest_completeness,
    `LnLean.Proofs.Crypto.PopProtocolTargets.storedAccept_honest_registration,
    `LnLean.Proofs.Crypto.PopProtocolTargets.accepted_owns,
    `LnLean.Proofs.Crypto.PopProtocolTargets.accepted_funding_attribution,
    `LnLean.Proofs.Crypto.PopProtocolTargets.popSound_of_keySoundOn,
    `LnLean.Proofs.Crypto.PopProtocolTargets.accepted_stored_registration_attribution,
    `LnLean.Proofs.Crypto.PopProtocolTargets.unbound_replay_accepts,
    `LnLean.Proofs.Crypto.PopProtocolTargets.nonceFree_replay_accepts,
    `LnLean.Proofs.Crypto.PopProtocolTargets.challengeMessage_not_injective_without_valid,
    `LnLean.Proofs.Crypto.PopProtocolTargets.binding_fails_without_valid,
    `LnLean.Proofs.Crypto.PopProtocolTargets.repeated_challenge_replay,
    `LnLean.Proofs.Crypto.PopProtocolTargets.keySound_not_provenance,
    `LnLean.Proofs.Crypto.PopProtocolTargets.protocol_nonvacuous,
    `LnLean.Proofs.Crypto.PopProtocolTargets.pop_protocol_summary,
    `LnLean.Proofs.Channel.CoverageWitnessTargets.decodeCoverage_canonical,
    `LnLean.Proofs.Channel.CoverageWitnessTargets.decodeCoverage_covers,
    `LnLean.Proofs.Channel.CoverageWitnessTargets.no_legacy_only_coverage_decoder,
    `LnLean.Proofs.Channel.CoverageWitnessTargets.no_legacy_only_witness_selector,
    `LnLean.Proofs.Channel.CoverageWitnessTargets.wire_admits_distinct_coverage_witnesses,
    `LnLean.Proofs.Channel.CoverageWitnessTargets.amount_is_necessary,
    `LnLean.Proofs.Channel.CoverageWitnessTargets.toCommitmentHtlcOutput_eq_iff,
    `LnLean.Proofs.Channel.CoverageWitnessTargets.coverage_witness_summary,
    `LnLean.Proofs.Routing.NodeIdentityTargets.canonical_distinct_nodes_no_oriented_store_link,
    `LnLean.Proofs.Routing.NodeIdentityTargets.no_store_function_selects_both_rotation_worlds,
    `LnLean.Proofs.Routing.NodeIdentityTargets.concrete_intended_rotation_not_storeOnly,
    `LnLean.Proofs.Routing.NodeIdentityTargets.rotation_preserves_wireMember,
    `LnLean.Proofs.Routing.NodeIdentityTargets.rotation_not_signature_preserving,
    `LnLean.Proofs.Routing.NodeIdentityTargets.channelAnnouncement_admitted_of_wireMember,
    `LnLean.Proofs.Routing.NodeIdentityTargets.missing_endpoint_channel_admitted,
    `LnLean.Proofs.Routing.NodeIdentityTargets.wireMember_applyGossipNodeCanonical,
    `LnLean.Proofs.Routing.NodeIdentityTargets.graphBacked_of_nodeKeyConsistent,
    `LnLean.Proofs.Conformance.Diff.diff_msg_open_channel_payload,
    `LnLean.Proofs.Conformance.Diff.diff_msg_open_channel_length,
    `LnLean.Proofs.Conformance.Diff.diff_msg_open_channel_transport,
    `LnLean.Proofs.Conformance.Diff.diff_msg_open_channel_header,
    `LnLean.Proofs.Conformance.Diff.diff_msg_open_channel_frame_prefix,
    `LnLean.Proofs.Security.ChainFinalityTargets.bounded_depth_finality,
    `LnLean.Proofs.Security.ChainFinalityTargets.confirmed_tx_not_reorged,
    `LnLean.Proofs.Security.ChainFinalityTargets.unique_tip_finality,
    `LnLean.Proofs.Security.ChainFinalityTargets.depth_bound_necessary,
    `LnLean.Proofs.Security.ChainFinalityTargets.deep_reorg_evicts,
    `LnLean.Proofs.Security.ChainFinalityTargets.chain_finality_and_retention,
    `LnLean.Proofs.Routing.NodeIdentityChainTargets.RotationCertificate.signed_implies_link,
    `LnLean.Proofs.Routing.NodeIdentityChainTargets.RotationChain.authenticated_comp,
    `LnLean.Proofs.Routing.NodeIdentityChainTargets.RotationChain.authenticated_hop_links,
    `LnLean.Proofs.Routing.NodeIdentityChainTargets.RotationChain.acyclic_start_not_mem_tail,
    `LnLean.Proofs.Routing.NodeIdentityChainTargets.distinct_hops_not_acyclic,
    `LnLean.Proofs.Routing.NodeIdentityChainTargets.opaque_link_not_authenticated,
    `LnLean.Proofs.Routing.NodeIdentityChainTargets.ResignedChannel.wireMember,
    `LnLean.Proofs.Routing.NodeIdentityChainTargets.SignedResignation.admitted,
    `LnLean.Proofs.Routing.NodeIdentityChainTargets.old_signature_does_not_authenticate_new_keys,
    `LnLean.Proofs.Routing.NodeIdentityChainTargets.signature_preservation_not_universal,
    `LnLean.Proofs.Routing.NodeIdentityChainTargets.NodeRateState.replay_rejected,
    `LnLean.Proofs.Routing.NodeIdentityChainTargets.rateFold_replay_rejected,
    `LnLean.Proofs.Routing.NodeIdentityChainTargets.nonvacuity_witness,
    `LnLean.Proofs.Protocol.NoiseTransportTargets.accepted_frame_bound_to_peer,
    `LnLean.Proofs.Protocol.NoiseTransportTargets.sessionKeyBinding_iff_peerStatic_eq,
    `LnLean.Proofs.Protocol.NoiseTransportTargets.accepted_frame_yields_sessionKeyBinding,
    `LnLean.Proofs.Protocol.NoiseTransportTargets.accepted_frame_attributed_delivery,
    `LnLean.Proofs.Protocol.NoiseTransportTargets.accepted_frame_reaches_fundingCreated,
    `LnLean.Proofs.Protocol.NoiseTransportTargets.replay_rejected_with_freshness,
    `LnLean.Proofs.Protocol.NoiseTransportTargets.replay_accepted_without_nonce_freshness,
    `LnLean.Proofs.Protocol.NoiseTransportTargets.key_substitution_without_peer_binding,
    `LnLean.Proofs.Protocol.NoiseTransportTargets.acceptance_not_attribution,
    `LnLean.Proofs.Protocol.NoiseTransportTargets.noise_does_not_authenticate_payload,
    `LnLean.Proofs.Protocol.NoiseTransportTargets.no_wire_session_binding_function,
    `LnLean.Proofs.Protocol.NoiseTransportTargets.noise_transport_nonvacuous,
    `LnLean.Proofs.Protocol.NoiseTransportTargets.noise_transport_summary,
    `LnLean.Proofs.Channel.CoverageSourceTargets.decodeSource_fullRecord_exact,
    `LnLean.Proofs.Channel.CoverageSourceTargets.decodeSource_outOfBand_canonical,
    `LnLean.Proofs.Channel.CoverageSourceTargets.decodeSource_extensionOfFull_canonical,
    `LnLean.Proofs.Channel.CoverageSourceTargets.extension_plus_wire_determines_coverage,
    `LnLean.Proofs.Channel.CoverageSourceTargets.no_wire_determined_source,
    `LnLean.Proofs.Channel.CoverageSourceTargets.no_wire_source_selector,
    `LnLean.Proofs.Channel.CoverageSourceTargets.wire_admits_distinct_out_of_band_witnesses,
    `LnLean.Proofs.Channel.CoverageSourceTargets.wireCompatible_not_out_of_band_binding,
    `LnLean.Proofs.Channel.CoverageSourceTargets.no_wire_witness_authenticator,
    `LnLean.Proofs.Channel.CoverageSourceTargets.coverage_source_summary,
    `LnLean.Proofs.Payment.InvoiceWireTargets.parse_print_paymentHash,
    `LnLean.Proofs.Payment.InvoiceWireTargets.wire_paymentHash_binding,
    `LnLean.Proofs.Payment.InvoiceWireTargets.preimage_unique_of_injective,
    `LnLean.Proofs.Payment.InvoiceWireTargets.preimage_determines_hash,
    `LnLean.Proofs.Payment.InvoiceWireTargets.paymentHash_eq_iff_bytes,
    `LnLean.Proofs.Payment.InvoiceWireTargets.signature_not_payment,
    `LnLean.Proofs.Payment.InvoiceWireTargets.signatureOnly_verifies,
    `LnLean.Proofs.Payment.InvoiceWireTargets.signatureOnly_no_preimage,
    `LnLean.Proofs.Payment.InvoiceWireTargets.signature_only_separates_verify_from_payment,
    `LnLean.Proofs.Payment.InvoiceWireTargets.paymentSecret_eq_iff_bytes,
    `LnLean.Proofs.Payment.InvoiceWireTargets.parse_print_paymentSecret,
    `LnLean.Proofs.Payment.InvoiceWireTargets.wire_paymentSecret_binding,
    `LnLean.Proofs.Payment.InvoiceWireTargets.toInvoice_valid,
    `LnLean.Proofs.Channel.HtlcAggregate.Aggregate.aggregate_coverage_projection,
    `LnLean.Proofs.Channel.HtlcAggregate.Aggregate.coverageValue_eq_sum,
    `LnLean.Proofs.Channel.HtlcAggregate.no_double_spend_of_noAliasing,
    `LnLean.Proofs.Channel.HtlcAggregate.same_spend_distinct_records_imp_aliasing,
    `LnLean.Proofs.Channel.HtlcAggregate.aliasing_double_spend_witness,
    `LnLean.Proofs.Channel.HtlcAggregate.AggregateTx.weight_eq,
    `LnLean.Proofs.Channel.HtlcAggregate.AggregateTx.not_funded_of_output_add_fee_gt,
    `LnLean.Proofs.Channel.HtlcAggregate.no_legacy_only_aggregate_coverage_decoder,
    `LnLean.Proofs.Payment.InvoiceWireTargets.parseFields_printFields,
    `LnLean.Proofs.Payment.InvoiceWireTargets.parse_print,
    `LnLean.Proofs.Payment.InvoiceWireTargets.print_injective,
    `LnLean.Proofs.Payment.InvoiceWireTargets.witness_parse,
    `LnLean.Proofs.Payment.InvoiceWireTargets.malformed_parse_none,
    `LnLean.Proofs.Payment.InvoiceWireTargets.duplicateHash_parse_none,
    `LnLean.Proofs.Payment.InvoiceWireTargets.decodeHop_encodeHop,
    `LnLean.Proofs.Payment.InvoiceWireTargets.encodeHop_size,
    `LnLean.Proofs.Model.NonVacuityTargets.witnessRegistry_sound,
    `LnLean.Proofs.Model.NonVacuityTargets.witnessRegistry_length,
    `LnLean.Proofs.Model.NonVacuityTargets.witnessRegistry_ids_nodup,
    `LnLean.Proofs.Model.NonVacuityTargets.withVendorEcdsa_accepts_nothing,
    `LnLean.Proofs.Model.NonVacuityTargets.withVendorEcdsa_funding_uninhabited,
    `LnLean.Proofs.Model.NonVacuityTargets.vacuous_nonvacuous_separation,
    `LnLean.Proofs.Model.NonVacuityTargets.witness_not_universal,
    `LnLean.Proofs.Model.NonVacuityTargets.witnessRegistry_ne_nil,
    `LnLean.Proofs.Conformance.Diff.diff_msg_accept_channel_length,
    `LnLean.Proofs.Conformance.Diff.diff_msg_accept_channel_transport,
    `LnLean.Proofs.Conformance.Diff.diff_msg_accept_channel_header,
    `LnLean.Proofs.Conformance.Diff.diff_msg_accept_channel_frame_prefix,
    `LnLean.Proofs.Conformance.Diff.diff_msg_accept_channel_payload,
    ]

set_option maxRecDepth 6000 in
theorem auditedTheorems_length : auditedTheorems.length = 407 := rfl
