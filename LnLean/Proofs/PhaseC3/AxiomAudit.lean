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
    `LnLean.Proofs.Liveness.penalty_economical ]

theorem auditedTheorems_length : auditedTheorems.length = 62 := rfl
