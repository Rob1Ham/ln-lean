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
    claim := "The funding output is P2WSH over the constructed 2-of-2 funding witness script; the handshake construction derives the witness-script hash link, the vendored interpreter executes the funding script, and the BIP 143 witness-v0 digest/locktime context is constructed and consumed by the vendor checker under explicit signature laws; the joint open/accept construction proves the same hash link.",
    leanTarget := "LnLean.Proofs.Bitcoin.FundingScriptTargets.fundingScriptPubKey_eq_p2wsh_twoOfTwo; LnLean.Proofs.Bitcoin.FundingLinkTargets.fundingScriptPubKey_eq_p2wsh_ordered; LnLean.Proofs.Bitcoin.InterpreterBridgeTargets.funding_interpreters_agree; LnLean.Proofs.Bitcoin.SighashBridgeTargets.funding_sighash_interpreters_agree; LnLean.Proofs.Bitcoin.FundingAuthTargets.openAccept_hash_linked; LnLean.Proofs.Bitcoin.EcdsaBridgeTargets.fundingSignedValid_iff_vendor; LnLean.Proofs.Bitcoin.EcdsaBridgeTargets.funding_sighash_interpreters_agree_vendor",
    status := .proved,
    boltdoc := "BOLT 2 §Channel Establishment v1; BOLT 3 §Funding Transaction Output",
    rlAnchor := "lightning/src/ln/chan_utils.rs:847" },
  { id := "LN-L1-002", domain := .l1,
    claim := "If the seam MoneyRange predicate holds for a funding output, the btc-lean L1 MoneyRange predicate holds.",
    leanTarget := "LnLean.Bitcoin.fundingOutput_moneyRange",
    status := .proved,
    boltdoc := "BOLT 2 §The open_channel Message",
    rlAnchor := "lightning/src/ln/channel.rs:2683" },
  { id := "LN-L1-003", domain := .l1,
    claim := "Under a common chain tip and the adversary's bounded reorg-depth budget, channel safety is preserved; deep reorgs are a separate failure mode.",
    leanTarget := "LnLean.Proofs.Security.ReorgTargets.reorg_preserves_channel_safety; LnLean.Proofs.Security.ReorgTargets.deep_reorg_separate_failure_mode",
    status := .proved,
    boltdoc := "BOLT 5 §Commitment Transaction",
    rlAnchor := "lightning/src/chain/channelmonitor.rs:514" },
  { id := "LN-L1-004", domain := .l1,
    claim := "The full BOLT 3 to_local witness script carries the CSV contest delay and the revocation key, the commitment output commits to both, and both the delayed and revocation branches execute through the vendored interpreter with a constructed BIP 143 digest/locktime context; the decoded BIP 68/112 sequence context is characterized exactly and transferred to the real checker, while EC/key-separation/signature hypotheses remain.",
    leanTarget := "LnLean.Proofs.Bitcoin.ToLocalScriptTargets.toLocalScriptFull_carries_csv_and_revocationKey; LnLean.Proofs.Bitcoin.ToLocalScriptTargets.toLocalScriptFull_commits_delay_and_revocationKey; LnLean.Proofs.Bitcoin.ToLocalScriptTargets.commitmentOutputs_toLocal_commits_delay_and_revocationKey; LnLean.Proofs.Bitcoin.InterpreterBridgeTargets.toLocal_delayed_interpreters_agree; LnLean.Proofs.Bitcoin.InterpreterRevocationTargets.toLocal_revocation_interpreters_agree; LnLean.Proofs.Bitcoin.SighashBridgeTargets.toLocal_sighash_interpreters_agree; LnLean.Proofs.Bitcoin.SequenceContextTargets.toLocal_delayed_realChecker_refinement; LnLean.Proofs.Bitcoin.TxValidTransferTargets.txCheckerFor_some_eq_realCheckerOf; LnLean.Proofs.Bitcoin.TxValidTransferTargets.toLocal_delayed_txCheckerFor_refinement; LnLean.Proofs.Bitcoin.EcdsaBridgeTargets.model_verify_eq_realChecker_seam; LnLean.Proofs.Bitcoin.EcdsaBridgeTargets.toLocal_revocation_interpreters_agree_vendor",
    status := .proved,
    boltdoc := "BOLT 3 §to_local Output",
    rlAnchor := "lightning/src/ln/chan_utils.rs:687" },
  { id := "LN-L1-005", domain := .l1,
    claim := "An anchor output is worth exactly 330 satoshis.",
    leanTarget := "LnLean.Bitcoin.anchorValue_eq",
    status := .proved,
    boltdoc := "BOLT 3 §to_local_anchor and to_remote_anchor Output",
    rlAnchor := "lightning/src/ln/channel.rs:989" },
  { id := "LN-L1-006", domain := .l1,
    claim := "The commitment base weight is the BOLT 3 fee-basis constant 724 before HTLC outputs, 1124 with anchors, plus 172 per untrimmed HTLC, with the anchor serialization gap explicit.",
    leanTarget := "LnLean.Proofs.Bitcoin.commitmentBaseWeight_model_target",
    status := .proved,
    boltdoc := "BOLT 3 §Expected Weight of the Commitment Transaction",
    rlAnchor := "lightning/src/ln/chan_utils.rs:281" },

  -- Crypto / wire (6)
  -- Retarget note (proof wave 2): the original target was the `PrimitiveModel`
  -- field `sha256`, not a theorem.  The faithful contract is that constructed
  -- and opened payment hashes are SHA-256 images, with C1 giving uniqueness of
  -- a valid 32-byte preimage.  The universal "every payment hash is a SHA-256
  -- output" reading is false (D05's well-formed 33-byte counterexample).
  { id := "LN-CR-001", domain := .cryptoWire,
    claim := "Constructed and opened payment hashes are SHA-256 outputs; under assumption C1 (collision resistance on the 32-byte preimage domain), a payment hash determines at most one valid preimage.",
    leanTarget := "LnLean.Crypto.Hash.paymentHash_sha256_contract",
    status := .proved,
    boltdoc := "BOLT 2 §Adding an HTLC",
    rlAnchor := "lightning/src/ln/channel.rs:8370" },
  -- Retarget note: the original target was the `ecdsaVerify` field.  The
  -- faithful C3 contract is message binding plus funding/close domain
  -- separation.  "Honest signatures verify" needs a signing-completeness law
  -- (E06), and key attribution needs `KeyBinding`; neither follows from C3.
  { id := "LN-CR-002", domain := .cryptoWire,
    claim := "Under assumption C3 (ECDSA EUF-CMA), a commitment-domain signature binds its untagged message uniquely and cannot verify in the funding or close signing domain.",
    leanTarget := "LnLean.Crypto.Sig.commitmentSig_contract",
    status := .proved,
    boltdoc := "BOLT 3 §Commitment Transaction Construction",
    rlAnchor := "lightning/src/ln/chan_utils.rs:1450" },
  -- Retarget note: the original target was the `hmacSha256` field.  The true
  -- claim is structural 32-byte output plus C8 `HmacBindsOn` for one execution;
  -- a global HMAC PRF claim is refuted by D07's `hmacPrf_vacuous`.
  { id := "LN-CR-003", domain := .cryptoWire,
    claim := "Onion HMAC-SHA256 tags are 32 bytes; under the finite-execution C8 admission, an authentic tag determines the hop payloads uniquely among the messages of that execution.",
    leanTarget := "LnLean.Crypto.Hash.onionHmacTag_size_and_bindsOn",
    status := .proved,
    boltdoc := "BOLT 4 §Packet Structure",
    rlAnchor := "lightning/src/ln/onion_payment.rs:505" },
  { id := "LN-CR-004", domain := .cryptoWire,
    claim := "BigSize encoding and decoding are inverse on canonical encodings.",
    leanTarget := "LnLean.Wire.decode_encode",
    status := .proved,
    boltdoc := "BOLT 1 §Fundamental Types; BOLT 1 Appendix A",
    rlAnchor := "lightning/src/util/ser.rs:442" },
  { id := "LN-CR-005", domain := .cryptoWire,
    claim := "A TLV stream is well formed exactly when its types are pairwise strictly increasing, and well-formed streams have no duplicate record types.",
    leanTarget := "LnLean.Wire.TLVStream.wellFormed_iff_pairwise; LnLean.Wire.TLVStream.wellFormed_record_type_unique",
    status := .proved,
    boltdoc := "BOLT 1 §Type-Length-Value Format",
    rlAnchor := "lightning/src/util/ser.rs:369" },
  { id := "LN-CR-006", domain := .cryptoWire,
    claim := "A Lightning message frame's declared length matches the payload actually consumed.",
    leanTarget := "LnLean.Wire.Message.decode_length",
    status := .proved,
    boltdoc := "BOLT 1 §Lightning Message Format",
    rlAnchor := "lightning/src/ln/peer_handler.rs:331" },

  -- Channel / commitment (6)
  { id := "LN-CH-001", domain := .channel,
    claim := "Every ledger transition preserves funding = local + remote + in-flight + fee.",
    leanTarget := "LnLean.Security.Ledger.step_conserves",
    status := .proved,
    boltdoc := "BOLT 3 §Commitment Transaction",
    rlAnchor := "lightning/src/ln/chan_utils.rs:716" },
  -- Scope note: nonnegativity is unconditional; the funding bound is proved
  -- under the BOLT 3 balance equation
  -- `totalOutputValue + feeSat = fundingValueSat` (D46 refutes the bare bound).
  { id := "LN-CH-002", domain := .channel,
    claim := "No commitment output has a negative value and the output sum stays within the funding value.",
    leanTarget := "LnLean.Channel.Commitment.outputs_nonnegative",
    status := .proved,
    boltdoc := "BOLT 3 §Commitment Transaction Outputs",
    rlAnchor := "lightning/src/ln/chan_utils.rs:1908" },
  -- Scope note: proved for the rich `CommitmentTx` model with explicit
  -- scriptPubKey, owner dust limit, and deterministic (value, script, CLTV)
  -- sorting.  D12 still refutes the unconditional legacy
  -- `commitmentOutputs` reading; the legacy function is unchanged.
  { id := "LN-CH-003", domain := .channel,
    claim := "In the rich commitment-output model, outputs are sorted by value, script, and CLTV, and dust HTLCs are trimmed; the five-field gross/net record layer proves the canonical commitment refinement, migration conservation, and effective fee at arbitrary dust, while the legacy output function remains refuted by D12; the consumer migration preserves the legacy list only in the BOLT 3 survivor normal form, and the no-trim counterexample is retained.",
    leanTarget := "LnLean.Channel.Commitment.output_ordering; LnLean.Channel.CommitmentTx.migratedFrom_outputsNet_perm_commitmentOutputs; LnLean.Proofs.Channel.CommitmentTypes.CommitmentTx.migrateNet_canonicalOutputs_eq_commitmentOutputs; LnLean.Proofs.Channel.CommitmentConsumer.migratedConsumerOutputs_eq_consumerOutputs_of_migrated; LnLean.Proofs.Channel.CommitmentConsumerSites.commitment_signed_full_covers_migrated; LnLean.Proofs.Channel.CommitmentConsumerSites.migratedConsumerOutputs_eq_viewOfState_outputs; LnLean.Proofs.Channel.CommitmentConsumerSites.viewOfState_outputs_perm_netConsumerOutputs",
    status := .proved,
    boltdoc := "BOLT 3 §Transaction Output Ordering; BOLT 3 §Trimmed Outputs",
    rlAnchor := "lightning/src/ln/chan_utils.rs:1985" },
  { id := "LN-CH-004", domain := .channel,
    claim := "A committed update never decreases the commitment number.",
    leanTarget := "LnLean.Security.advance_monotone",
    status := .proved,
    boltdoc := "BOLT 2 §Committing Updates So Far",
    rlAnchor := "lightning/src/ln/channel.rs:6270" },
  { id := "LN-CH-005", domain := .channel,
    claim := "A commitment is rejected before signing exactly when its feerate is insufficient for its weight, equivalently when no checked commitment_signed step exists in the normal phase.",
    leanTarget := "LnLean.Channel.Fee.commitmentSigningGate_rejected_iff_insufficient; LnLean.Channel.Fee.commitmentSigningGate_rejected_iff_no_checkedSigning",
    status := .proved,
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
  -- Scope note: `ledger` is the modelled balances/fee total; the partition
  -- theorem requires `ledger + totalHtlcValue (htlcSet hs) = funding`.
  { id := "LN-HT-003", domain := .htlcRevocation,
    claim := "Offered, received, and trimmed HTLC amounts plus balances and fee equal the funding value.",
    leanTarget := "LnLean.Channel.HTLC.amount_conservation",
    status := .proved,
    boltdoc := "BOLT 2 §Adding an HTLC",
    rlAnchor := "lightning/src/ln/chan_utils.rs:716" },
  -- Scope note: BOLT 2 ids are per-sender; both counters start at zero.  The
  -- unconditional untagged global claim is refuted by
  -- `HtlcBook.reachable_cross_direction_duplicate`, so the row keeps
  -- per-sender uniqueness, the explicit `CrossDisjoint` untagged form, and a
  -- direction-tagged namespace that is globally unique without that
  -- assumption.
  { id := "LN-HT-004", domain := .htlcRevocation,
    claim := "An HTLC id is unique among the live HTLCs of one sender; a direction-tagged id is globally unique, while the untagged global claim needs explicit cross-direction disjointness.",
    leanTarget := "LnLean.Channel.HTLC.dir_id_unique; LnLean.Channel.HTLC.id_unique_of_reachable_cross; LnLean.Channel.HTLC.tagged_id_unique_of_reachable; LnLean.Channel.HTLC.tagged_ids_nodup_of_reachable; LnLean.Channel.HTLC.cross_direction_duplicate_tagged",
    status := .proved,
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
  -- Scope note: proved in the D17 acceptor model; the wrapper in
  -- `LnLean.Proofs.ProtocolTargets` restates its accepted-open bounds.
  { id := "LN-PR-001", domain := .protocol,
    claim := "open_channel accepts a funding amount only above the dust and minimum-channel bounds.",
    leanTarget := "LnLean.Protocol.Handshake.open_bounds; LnLean.Proofs.Protocol.OpenChannelWireTargets.openChannelWire_end_to_end; LnLean.Protocol.OpenChannelWire.toFundingParams_hash_linked; LnLean.Proofs.Protocol.OpenChannelWireTargets.acceptKey_bound_before_fundingCreated_wire",
    status := .proved,
    boltdoc := "BOLT 2 §The open_channel Message",
    rlAnchor := "lightning/src/ln/channelmanager.rs:17521" },
  { id := "LN-PR-002", domain := .protocol,
    claim := "The channel enters normal operation only after both channel_ready messages.",
    leanTarget := "LnLean.Protocol.Handshake.channel_ready_gate",
    status := .proved,
    boltdoc := "BOLT 2 §The channel_ready Message",
    rlAnchor := "lightning/src/ln/channelmanager.rs:17614" },
  -- Scope note: conditional on an explicit `FundingSigningLaw` (signing
  -- correctness plus wire shape) and `KeyBinding`.  C3/EUF-CMA alone gives
  -- transaction/message binding, not signing completeness or key attribution;
  -- the lane includes a counterexample showing that gap.
  { id := "LN-PR-003", domain := .protocol,
    claim := "Under an explicit signing law and key-binding hypothesis, funding_signed carries a valid signature over the funding transaction and attributes it to the funding key; one joint contract also covers commitment_signed, while C3 alone gives neither; a secret-key model proves attribution under the unchanged KeyBinding and mechanizes why key generation alone does not attribute.",
    leanTarget := "LnLean.Protocol.Handshake.funding_signed_signing_contract; LnLean.Proofs.Channel.SighashTargets.funding_and_commitment_signing_contract; LnLean.Proofs.Crypto.KeyModelTargets.funding_signature_attribution; LnLean.Proofs.Crypto.AcceptPayloadTargets.stored_accept_payload_attribution; LnLean.Proofs.Crypto.AcceptPayloadTargets.acceptPayload_not_proof_of_possession",
    status := .proved,
    boltdoc := "BOLT 2 §The funding_signed Message",
    rlAnchor := "lightning/src/ln/channel.rs:2107" },
  -- Scope note: derived from the `CommitmentSignedFull` `ProducedFrom`
  -- relation and the BOLT 3 commitment value equations.  The legacy wire
  -- record alone cannot determine the HTLC set or fee; the lane proves that
  -- negative result and includes an honest covering construction.  There is
  -- still no BOLT 3 sighash serializer or C3 derivation of the digests.
  { id := "LN-PR-004", domain := .protocol,
    claim := "Under a BOLT 3-shaped serializer with an exact transaction wire layout, an explicit signing law, and the commitment value equations, commitment_signed covers exactly the current HTLC set and fee and its digest/signatures are derived under C3; digest binding implies view binding only under explicit collision-free/serialization hypotheses, and the wire record alone determines neither; the commitment-wire preimage is byte-equal to the vendored BIP 143 encoder, with the HTLC instantiation still open.",
    leanTarget := "LnLean.Proofs.ProtocolWireTargets.commitment_signed_full_covers_exact; LnLean.Proofs.ProtocolWireTargets.protocol_wire_summary; LnLean.Proofs.Channel.SighashTargets.SighashProduces.coverage; LnLean.Proofs.Channel.SighashViewBindingTargets.commitmentSignature_binds_viewOfState; LnLean.Proofs.Channel.SighashTargets.CommitmentWire.txBytes_parse; LnLean.Proofs.Channel.SighashTargets.Bip143Preimage.preimageBytes_eq_bip143MsgL_ofTx; LnLean.Proofs.Channel.SighashTargets.commitmentBip143Preimage_eq_bip143MsgL; LnLean.Proofs.Channel.HtlcPreimageTargets.htlcBip143Preimage_eq_bip143MsgL; LnLean.Proofs.Channel.HtlcPreimageTargets.HtlcSpend.successPreimage_eq_bip143MsgL; LnLean.Proofs.Channel.HtlcPreimageTargets.HtlcSpend.timeoutPreimage_eq_bip143MsgL; LnLean.Proofs.Channel.HtlcPreimageTargets.htlc_preimage_target_summary",
    status := .proved,
    boltdoc := "BOLT 2 §Committing Updates So Far",
    rlAnchor := "lightning/src/ln/channel.rs:2386; lightning/src/ln/channel.rs:6270" },
  { id := "LN-PR-005", domain := .protocol,
    claim := "channel_reestablish retransmits unacknowledged updates without rolling state back.",
    leanTarget := "LnLean.Protocol.Peer.reestablish_no_rollback",
    status := .proved,
    boltdoc := "BOLT 2 §Message Retransmission",
    rlAnchor := "lightning/src/ln/channelmanager.rs:17831; lightning/src/ln/channel.rs:10826" },
  -- Scope note: support-set intersection (`featureIntersection`) under BOLT 1's
  -- survival hypothesis, not the raw bitwise AND of feature vectors (false).
  { id := "LN-PR-006", domain := .protocol,
    claim := "Negotiated channel features are the intersection of both peers' supported features.",
    leanTarget := "LnLean.Protocol.Handshake.feature_intersection",
    status := .proved,
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
    leanTarget := "LnLean.Routing.Gossip.update_monotone; LnLean.Proofs.Routing.GossipStoreEpochTargets.epochFold_gossip_eq_canonicalStoreView_rawFold; LnLean.Routing.replacedUpdates_timestamp_lt; LnLean.Proofs.Routing.GossipStoreEpochTargets.StoreEpoch.epochFold_store_eq_foldl",
    status := .proved,
    boltdoc := "BOLT 7 §The channel_update Message",
    rlAnchor := "lightning/src/routing/gossip.rs:906; lightning/src/routing/gossip.rs:422" },
  { id := "LN-RT-003", domain := .routing,
    claim := "Peeling one onion layer exposes the next hop or a terminal payload, never both.",
    leanTarget := "LnLean.Routing.Onion.peel_deterministic",
    status := .proved,
    boltdoc := "BOLT 4 §Onion Decryption",
    rlAnchor := "lightning/src/ln/onion_payment.rs:505" },
  -- Scope note: this target is the checked `openLayer` path.  Raw `peel`
  -- bypasses HMAC; the D25 counterexample is retained.
  { id := "LN-RT-004", domain := .routing,
    claim := "An onion layer with an invalid HMAC is rejected rather than forwarded.",
    leanTarget := "LnLean.Routing.Onion.hmac_sound",
    status := .proved,
    boltdoc := "BOLT 4 §Packet Structure",
    rlAnchor := "lightning/src/ln/onion_payment.rs:505" },
  { id := "LN-RT-005", domain := .routing,
    claim := "The CLTV expiry at each hop increases by at least that hop's cltv_expiry_delta.",
    leanTarget := "LnLean.Routing.Route.cltv_accumulates",
    status := .proved,
    boltdoc := "BOLT 4 §Payload for the Last Node; BOLT 7 §HTLC Fees",
    rlAnchor := "lightning/src/routing/router.rs:657" },
  { id := "LN-RT-006", domain := .routing,
    claim := "In every reachable signature-gated gossip state, every graph edge is backed by a stored announcement whose four BOLT 7 signatures verify; raw applyGossip remains unfiltered.",
    leanTarget := "LnLean.Proofs.Routing.GossipTargets.gossip_graph_only_valid_announcements",
    status := .proved,
    boltdoc := "BOLT 7 §The channel_announcement Message",
    rlAnchor := "lightning/src/routing/gossip.rs:515; lightning/src/routing/gossip.rs:1012" },

  -- Payments (6)
  { id := "LN-PM-001", domain := .payment,
    claim := "A consistent invoice has the payment session's hash and amount.",
    leanTarget := "LnLean.Security.Invoice.consistent_hash; LnLean.Security.Invoice.consistent_amount",
    status := .proved,
    boltdoc := "BOLT 11 §Tagged Fields",
    rlAnchor := "lightning-invoice/src/lib.rs:1662; lightning-invoice/src/lib.rs:1473" },
  -- Scope note: this is a model-level projection from `Invoice.verify`;
  -- ECDSA unforgeability and key binding remain assumption C3.
  { id := "LN-PM-002", domain := .payment,
    claim := "A BOLT 11 invoice signature is valid for the payee node key.",
    leanTarget := "LnLean.Payment.Invoice.signature_valid",
    status := .proved,
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
    status := .proved,
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
  -- Scope note: `global_conservation` covers the multi-channel ledger only.
  -- The L1 spend-set half is modelled separately in D32 and is not asserted.
  { id := "LN-SEC-002", domain := .security,
    claim := "Across all channels and the L1 spend set, total value is conserved.",
    leanTarget := "LnLean.Proofs.Conservation.global_conservation",
    status := .proved,
    boltdoc := "BOLT 3 §Commitment Transaction",
    rlAnchor := "lightning/src/ln/chan_utils.rs:716" },
  -- Scope note: the theorem keeps the four explicit `Assumptions P`; it does
  -- not use a fairness hypothesis.
  { id := "LN-SEC-003", domain := .security,
    claim := "Safety holds under an asynchronous adversarial schedule (without a fairness hypothesis).",
    leanTarget := "LnLean.Proofs.Security.safety_async",
    status := .proved,
    boltdoc := "BOLT 2 §Message Retransmission",
    rlAnchor := "lightning/src/ln/channelmanager.rs:17831" },
  { id := "LN-SEC-004", domain := .security,
    claim := "After GST every message is delivered within delta of its send time.",
    leanTarget := "LnLean.Security.partial_synchrony_delivers",
    status := .proved,
    boltdoc := "BOLT 1 §Lightning Message Format",
    rlAnchor := "lightning/src/ln/channelmanager.rs:17831" },
  -- Scope note: bounded-schedule theorem (`FeeScheduleBounded`); the
  -- unconditional spike claim is refuted by D34's counterexamples.
  { id := "LN-SEC-005", domain := .security,
    claim := "A penalty transaction remains economical under the modelled fee spike.",
    leanTarget := "LnLean.Proofs.Liveness.penalty_economical",
    status := .proved,
    boltdoc := "BOLT 5 §Revoked Transaction Close Handling",
    rlAnchor := "lightning/src/chain/chaininterface.rs:350" },
  -- Scope note: the exact target requires `wt.reports` (which implies live);
  -- `wt.live` alone is insufficient (E35 counterexample).
  { id := "LN-SEC-006", domain := .security,
    claim := "A breach is punished if some party has the revocation secret and a timely L1 transaction, given a live watchtower.",
    leanTarget := "LnLean.Proofs.Liveness.watchtower_bridge",
    status := .proved,
    boltdoc := "BOLT 5 §Revoked Transaction Close Handling",
    rlAnchor := "lightning/src/chain/channelmonitor.rs:5079" }
  ]

/-- The catalog has exactly 48 rows. -/
theorem obligations_length : obligations.length = 48 := rfl

end LnLean.Proofs
