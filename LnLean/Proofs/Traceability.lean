import LnLean.Proofs.Obligations

/-!
# LnLean.Proofs.Traceability

English claim.  The obligation catalog in `LnLean.Proofs.Obligations` is
*structurally consistent*, and its id sequence agrees with the two
hand-maintained traceability tables:

1. every row has a non-empty id, English claim, BOLT section, and
   `rust-lightning` anchor (`obligations_rows_well_formed`);
2. ids are pairwise distinct (`obligations_ids_nodup`) and equal, in order,
   to the ids of `docs/THEOREM-INDEX.md` and `docs/TRACEABILITY.md`
   (`catalog_ids_match_theorem_index`, `catalog_ids_match_traceability`);
3. the transcribed id table uses only the eight area codes and the numeric
   suffixes `1..6`, six rows per code (`id_areas_known`,
   `id_numbers_in_range`, `id_six_per_area`);
4. every status and every domain is one of the model's enumerations, and the
   catalog covers all eight domains (`obligations_statuses_enumerated`,
   `obligations_domains_enumerated`, `every_domain_used`);
5. the catalog has 48 rows, `48` marked `proved` and `0` marked
   `statementOnly`, matching the summary table of `docs/THEOREM-INDEX.md`
   (`obligations_count_ge_40`, `proved_row_count`,
   `statement_only_row_count`);
6. every `leanTarget` is non-empty, equals an entry of a transcribed target
   table, and every module in that table is one of a fixed list of
   `LnLean.*` modules (`obligations_targets_in_table`,
   `target_modules_lnean`);
7. every `proved` row names at least one declaration, all named declarations
   occur in the 61-name snapshot `provedDeclarations`, no snapshot name
   is unused, and every snapshot declaration lives in a module from
   `lneanModules` (`proved_rows_have_decls`, `proved_decls_in_snapshot`,
   `proved_snapshot_all_used`, `proved_declaration_modules_lnean`).  This is
   a structural check over the catalog; it is *not* a kernel proof of any
   target declaration;
8. no anchor uses the `UNANCHORED` fallback (`no_unanchored_rows`).

BOLT sections.  The catalog spans BOLT 1 (fundamental types, message format),
BOLT 2 (channel establishment, HTLCs, committing updates, retransmission),
BOLT 3 (commitment transaction, output ordering, per-commitment secrets),
BOLT 4 (onion packet structure and decryption), BOLT 5 (revoked close
handling), BOLT 7 (gossip and routing), BOLT 9 (features), and BOLT 11
(invoices).  This module proves no protocol behaviour itself; the anchors
below are the catalog rows' anchors.

`rust-lightning` anchors at commit `fe4900930c6bd5786ec4203274d7cf312776a5a6`
(the pinned commit in `refs/PINNED.md`), representative rows:
`lightning/src/ln/chan_utils.rs:847` (`make_funding_redeemscript`),
`lightning/src/ln/channel.rs:8370` (`update_add_htlc`),
`lightning/src/ln/channelmanager.rs:10210` (`claim_funds`),
`lightning/src/ln/onion_payment.rs:505` (`peel_payment_onion`),
`lightning/src/routing/gossip.rs:906` (`ChannelUpdateInfo`),
`lightning/src/routing/router.rs:825` (`Route`),
`lightning-invoice/src/lib.rs:1662` (`amount_milli_satoshis`),
`lightning/src/util/ser.rs:442` (`BigSize`),
`lightning/src/chain/channelmonitor.rs:5079`
(`check_spend_counterparty_transaction`).

What is NOT modelled.
* `claim` and `leanTarget` are `String`s.  There is no interpretation from a
  claim string to a `Prop`, so no theorem here entails an English claim, and
  no theorem says that a named declaration has the type the claim describes.
* Lean cannot reflect over its own environment from this module, and the
  allowed import set is only `LnLean.Proofs.Obligations`, so
  `provedDeclarations` is a *transcribed* snapshot of the declarations in
  `LnLean/Bitcoin/Seam.lean`, `LnLean/Security/Model.lean`,
  `LnLean/Security/Invariants.lean`, `LnLean/Wire/BigSize.lean`,
  `LnLean/Proofs/WaveD/D14.lean`,
  `LnLean/Proofs/WaveD/D18.lean`, `LnLean/Proofs/WaveD/D29.lean`, and
  `LnLean/Proofs/WaveE/E31.lean`, not an environment query.
* The kernel does not reduce the `String` operations needed to parse names
  (`String.splitOn`, `String.startsWith`, `String.isEmpty` are extern or
  partial and get stuck), and `native_decide` is forbidden.  This file
  therefore does *not* parse strings: it compares whole strings for equality
  (which does reduce) and carries the intended parse in the tables `idTable`,
  `targetTable`, `provedTable`, and `provedDeclarations`.  The claim that a
  table's `area`/`number`/`modules` fields are the true parse of its `text`
  field is checked externally with a script, not by Lean.
* `rlAnchor` strings are only checked for non-emptiness and against the
  `UNANCHORED` sentinel.  That each cited `path:line` exists in the pinned
  tree was checked externally (`python3` line-count check plus `sed` spot
  checks); it is not a Lean theorem.
* `theoremIndexIds` and `traceabilityIds` are literal copies of the Markdown
  tables.  The theorems below prove that the catalog and both copies agree;
  they cannot prove that a copy matches the current file on disk.  The
  report records the external comparison.
* No claim is made that `statementOnly` rows are true.
-/

namespace LnLean.Proofs.Traceability

open LnLean.Proofs

set_option autoImplicit false

-- The catalog's claim and target strings are long; reducing the 48-row checks
-- in the kernel needs a deeper recursion budget than the default.
set_option maxRecDepth 10000

/-! ## Transcribed table record types -/

/-- One catalog id, together with the parse used for the shape checks:
`area` is the two-or-three letter area code and `number` is the numeric
suffix (001 is stored as 1). -/
structure IdEntry where
  text : String
  area : String
  number : Nat
deriving Repr, DecidableEq

/-- One `leanTarget` string and the modules its (one or more) declaration
names live in. -/
structure TargetEntry where
  text : String
  modules : List String
deriving Repr, DecidableEq

/-- One `proved` row's target string and the declarations it names. -/
structure ProvedEntry where
  target : String
  decls : List String
deriving Repr, DecidableEq

/-- One declaration named by a `proved` row, with its defining module. -/
structure DeclEntry where
  text : String
  module : String
deriving Repr, DecidableEq

/-! ## Structural predicates -/

/-- Structural well-formedness of one catalog row: the four string fields are
non-empty.  The domain field is an inductive value, so it is never absent;
`domains_exhaustive` records that the enumeration covers the whole type. -/
def RowWellFormed (o : Obligation) : Prop :=
  o.id ≠ "" ∧ o.claim ≠ "" ∧ o.boltdoc ≠ "" ∧ o.rlAnchor ≠ ""

/-- Executable version of `RowWellFormed`.  It uses only `decide` on string
equality, which reduces in the kernel; `String.isEmpty` does not. -/
def rowWellFormed (o : Obligation) : Bool :=
  decide (o.id ≠ "") && decide (o.claim ≠ "") &&
    decide (o.boltdoc ≠ "") && decide (o.rlAnchor ≠ "")

/-- The two statuses the model enumerates. -/
def statuses : List ObligationStatus := [.proved, .statementOnly]

/-- The eight work domains, in constructor order. -/
def domains : List Domain :=
  [.l1, .cryptoWire, .channel, .htlcRevocation, .protocol, .routing, .payment, .security]

/-- The eight area codes used by obligation ids (one per domain). -/
def idAreas : List String := ["L1", "CR", "CH", "HT", "PR", "RT", "PM", "SEC"]

/-! ## Transcribed data

These tables are literal copies of the catalog's structure.  They exist
because the kernel cannot parse the strings; see "What is NOT modelled". -/

/-- Ids with their area code and numeric suffix. -/
def idTable : List IdEntry :=
  [ ⟨"LN-L1-001", "L1", 1⟩
  , ⟨"LN-L1-002", "L1", 2⟩
  , ⟨"LN-L1-003", "L1", 3⟩
  , ⟨"LN-L1-004", "L1", 4⟩
  , ⟨"LN-L1-005", "L1", 5⟩
  , ⟨"LN-L1-006", "L1", 6⟩
  , ⟨"LN-CR-001", "CR", 1⟩
  , ⟨"LN-CR-002", "CR", 2⟩
  , ⟨"LN-CR-003", "CR", 3⟩
  , ⟨"LN-CR-004", "CR", 4⟩
  , ⟨"LN-CR-005", "CR", 5⟩
  , ⟨"LN-CR-006", "CR", 6⟩
  , ⟨"LN-CH-001", "CH", 1⟩
  , ⟨"LN-CH-002", "CH", 2⟩
  , ⟨"LN-CH-003", "CH", 3⟩
  , ⟨"LN-CH-004", "CH", 4⟩
  , ⟨"LN-CH-005", "CH", 5⟩
  , ⟨"LN-CH-006", "CH", 6⟩
  , ⟨"LN-HT-001", "HT", 1⟩
  , ⟨"LN-HT-002", "HT", 2⟩
  , ⟨"LN-HT-003", "HT", 3⟩
  , ⟨"LN-HT-004", "HT", 4⟩
  , ⟨"LN-HT-005", "HT", 5⟩
  , ⟨"LN-HT-006", "HT", 6⟩
  , ⟨"LN-PR-001", "PR", 1⟩
  , ⟨"LN-PR-002", "PR", 2⟩
  , ⟨"LN-PR-003", "PR", 3⟩
  , ⟨"LN-PR-004", "PR", 4⟩
  , ⟨"LN-PR-005", "PR", 5⟩
  , ⟨"LN-PR-006", "PR", 6⟩
  , ⟨"LN-RT-001", "RT", 1⟩
  , ⟨"LN-RT-002", "RT", 2⟩
  , ⟨"LN-RT-003", "RT", 3⟩
  , ⟨"LN-RT-004", "RT", 4⟩
  , ⟨"LN-RT-005", "RT", 5⟩
  , ⟨"LN-RT-006", "RT", 6⟩
  , ⟨"LN-PM-001", "PM", 1⟩
  , ⟨"LN-PM-002", "PM", 2⟩
  , ⟨"LN-PM-003", "PM", 3⟩
  , ⟨"LN-PM-004", "PM", 4⟩
  , ⟨"LN-PM-005", "PM", 5⟩
  , ⟨"LN-PM-006", "PM", 6⟩
  , ⟨"LN-SEC-001", "SEC", 1⟩
  , ⟨"LN-SEC-002", "SEC", 2⟩
  , ⟨"LN-SEC-003", "SEC", 3⟩
  , ⟨"LN-SEC-004", "SEC", 4⟩
  , ⟨"LN-SEC-005", "SEC", 5⟩
  , ⟨"LN-SEC-006", "SEC", 6⟩
  ]

/-- Each catalog `leanTarget` string with the modules its names live in. -/
def targetTable : List TargetEntry :=
  [ ⟨"LnLean.Proofs.Bitcoin.FundingScriptTargets.fundingScriptPubKey_eq_p2wsh_twoOfTwo", ["LnLean.Proofs.Bitcoin.FundingScriptTargets"]⟩
  , ⟨"LnLean.Bitcoin.fundingOutput_moneyRange", ["LnLean.Bitcoin.Seam"]⟩
  , ⟨"LnLean.Proofs.Security.ReorgTargets.reorg_preserves_channel_safety; LnLean.Proofs.Security.ReorgTargets.deep_reorg_separate_failure_mode", ["LnLean.Proofs.Security.ReorgTargets", "LnLean.Proofs.Security.ReorgTargets"]⟩
  , ⟨"LnLean.Proofs.Bitcoin.ToLocalScriptTargets.toLocalScriptFull_carries_csv_and_revocationKey; LnLean.Proofs.Bitcoin.ToLocalScriptTargets.toLocalScriptFull_commits_delay_and_revocationKey; LnLean.Proofs.Bitcoin.ToLocalScriptTargets.commitmentOutputs_toLocal_commits_delay_and_revocationKey", ["LnLean.Proofs.Bitcoin.ToLocalScriptTargets", "LnLean.Proofs.Bitcoin.ToLocalScriptTargets", "LnLean.Proofs.Bitcoin.ToLocalScriptTargets"]⟩
  , ⟨"LnLean.Bitcoin.anchorValue_eq", ["LnLean.Bitcoin.Seam"]⟩
  , ⟨"LnLean.Proofs.Bitcoin.commitmentBaseWeight_model_target", ["LnLean.Proofs.Bitcoin.WeightTargets"]⟩
  , ⟨"LnLean.Crypto.Hash.paymentHash_sha256_contract", ["LnLean.Proofs.CryptoTargets"]⟩
  , ⟨"LnLean.Crypto.Sig.commitmentSig_contract", ["LnLean.Proofs.CryptoTargets"]⟩
  , ⟨"LnLean.Crypto.Hash.onionHmacTag_size_and_bindsOn", ["LnLean.Proofs.CryptoTargets"]⟩
  , ⟨"LnLean.Wire.decode_encode", ["LnLean.Wire.BigSize"]⟩
  , ⟨"LnLean.Wire.TLVStream.wellFormed_iff_pairwise; LnLean.Wire.TLVStream.wellFormed_record_type_unique", ["LnLean.Proofs.Wire.TLVTargets", "LnLean.Proofs.Wire.TLVTargets"]⟩
  , ⟨"LnLean.Wire.Message.decode_length", ["LnLean.Wire.Message"]⟩
  , ⟨"LnLean.Security.Ledger.step_conserves", ["LnLean.Security.Invariants"]⟩
  , ⟨"LnLean.Channel.Commitment.outputs_nonnegative", ["LnLean.Channel.Commitment"]⟩
  , ⟨"LnLean.Channel.Commitment.output_ordering", ["LnLean.Proofs.Channel.CommitmentOrderTargets"]⟩
  , ⟨"LnLean.Security.advance_monotone", ["LnLean.Security.Invariants"]⟩
  , ⟨"LnLean.Channel.Fee.commitmentSigningGate_rejected_iff_insufficient; LnLean.Channel.Fee.commitmentSigningGate_rejected_iff_no_checkedSigning", ["LnLean.Proofs.Channel.FeeTargets", "LnLean.Proofs.Channel.FeeTargets"]⟩
  , ⟨"LnLean.Channel.Reserve.bounds", ["LnLean.Proofs.WaveD.D14"]⟩
  , ⟨"LnLean.Security.HtlcRecord.fulfill_sound", ["LnLean.Security.Invariants"]⟩
  , ⟨"LnLean.Security.HtlcRecord.fail_only_after_expiry", ["LnLean.Security.Invariants"]⟩
  , ⟨"LnLean.Channel.HTLC.amount_conservation", ["LnLean.Channel.HTLC"]⟩
  , ⟨"LnLean.Channel.HTLC.dir_id_unique; LnLean.Channel.HTLC.id_unique_of_reachable_cross; LnLean.Channel.HTLC.tagged_id_unique_of_reachable; LnLean.Channel.HTLC.tagged_ids_nodup_of_reachable; LnLean.Channel.HTLC.cross_direction_duplicate_tagged", ["LnLean.Channel.HTLC", "LnLean.Channel.HTLC", "LnLean.Proofs.Channel.HtlcGlobalIdTargets", "LnLean.Proofs.Channel.HtlcGlobalIdTargets", "LnLean.Proofs.Channel.HtlcGlobalIdTargets"]⟩
  , ⟨"LnLean.Security.revoked_commitment_is_old", ["LnLean.Security.Invariants"]⟩
  , ⟨"LnLean.Security.breach_penalty_spends_both", ["LnLean.Security.Invariants"]⟩
  , ⟨"LnLean.Protocol.Handshake.open_bounds", ["LnLean.Proofs.ProtocolTargets"]⟩
  , ⟨"LnLean.Protocol.Handshake.channel_ready_gate", ["LnLean.Proofs.WaveD.D18"]⟩
  , ⟨"LnLean.Protocol.Handshake.funding_signed_signing_contract", ["LnLean.Proofs.ProtocolSigningTargets"]⟩
  , ⟨"LnLean.Proofs.ProtocolWireTargets.commitment_signed_full_covers_exact; LnLean.Proofs.ProtocolWireTargets.protocol_wire_summary", ["LnLean.Proofs.ProtocolWireTargets", "LnLean.Proofs.ProtocolWireTargets"]⟩
  , ⟨"LnLean.Protocol.Peer.reestablish_no_rollback", ["LnLean.Protocol.Peer"]⟩
  , ⟨"LnLean.Protocol.Handshake.feature_intersection", ["LnLean.Proofs.ProtocolTargets"]⟩
  , ⟨"LnLean.Security.Route.wellFormed_connected; LnLean.Security.Route.wellFormed_capacity; LnLean.Security.Route.wellFormed_nonempty", ["LnLean.Security.Invariants", "LnLean.Security.Invariants", "LnLean.Security.Invariants"]⟩
  , ⟨"LnLean.Routing.Gossip.update_monotone", ["LnLean.Routing.Gossip"]⟩
  , ⟨"LnLean.Routing.Onion.peel_deterministic", ["LnLean.Routing.Onion"]⟩
  , ⟨"LnLean.Routing.Onion.hmac_sound", ["LnLean.Routing.Onion"]⟩
  , ⟨"LnLean.Routing.Route.cltv_accumulates", ["LnLean.Routing.Route"]⟩
  , ⟨"LnLean.Proofs.Routing.GossipTargets.gossip_graph_only_valid_announcements", ["LnLean.Proofs.Routing.GossipTargets"]⟩
  , ⟨"LnLean.Security.Invoice.consistent_hash; LnLean.Security.Invoice.consistent_amount", ["LnLean.Security.Invariants", "LnLean.Security.Invariants"]⟩
  , ⟨"LnLean.Payment.Invoice.signature_valid", ["LnLean.Payment.Invoice"]⟩
  , ⟨"LnLean.Payment.Invoice.payment_secret_match", ["LnLean.Proofs.WaveD.D29"]⟩
  , ⟨"LnLean.Security.MppPayment.settle_requires_sum", ["LnLean.Security.Invariants"]⟩
  , ⟨"LnLean.Payment.MPP.running_total_bound", ["LnLean.Payment.MPP"]⟩
  , ⟨"LnLean.Payment.Keysend.preimage_binding", ["LnLean.Proofs.WaveE.E31"]⟩
  , ⟨"LnLean.Security.L1Ledger.spend_preserves_noDoubleSpend", ["LnLean.Security.Invariants"]⟩
  , ⟨"LnLean.Proofs.Conservation.global_conservation", ["LnLean.Proofs.Conservation"]⟩
  , ⟨"LnLean.Proofs.Security.safety_async", ["LnLean.Proofs.Security"]⟩
  , ⟨"LnLean.Security.partial_synchrony_delivers", ["LnLean.Security.Invariants"]⟩
  , ⟨"LnLean.Proofs.Liveness.penalty_economical", ["LnLean.Proofs.Liveness"]⟩
  , ⟨"LnLean.Proofs.Liveness.watchtower_bridge", ["LnLean.Proofs.Liveness"]⟩
  ]

/-- The 48 `proved` rows' targets and the declarations each names. -/
def provedTable : List ProvedEntry :=
  [⟨"LnLean.Proofs.Bitcoin.FundingScriptTargets.fundingScriptPubKey_eq_p2wsh_twoOfTwo", ["LnLean.Proofs.Bitcoin.FundingScriptTargets.fundingScriptPubKey_eq_p2wsh_twoOfTwo"]⟩
  , ⟨"LnLean.Bitcoin.fundingOutput_moneyRange", ["LnLean.Bitcoin.fundingOutput_moneyRange"]⟩
  , ⟨"LnLean.Proofs.Security.ReorgTargets.reorg_preserves_channel_safety; LnLean.Proofs.Security.ReorgTargets.deep_reorg_separate_failure_mode", ["LnLean.Proofs.Security.ReorgTargets.reorg_preserves_channel_safety", "LnLean.Proofs.Security.ReorgTargets.deep_reorg_separate_failure_mode"]⟩
  , ⟨"LnLean.Proofs.Bitcoin.ToLocalScriptTargets.toLocalScriptFull_carries_csv_and_revocationKey; LnLean.Proofs.Bitcoin.ToLocalScriptTargets.toLocalScriptFull_commits_delay_and_revocationKey; LnLean.Proofs.Bitcoin.ToLocalScriptTargets.commitmentOutputs_toLocal_commits_delay_and_revocationKey", ["LnLean.Proofs.Bitcoin.ToLocalScriptTargets.toLocalScriptFull_carries_csv_and_revocationKey", "LnLean.Proofs.Bitcoin.ToLocalScriptTargets.toLocalScriptFull_commits_delay_and_revocationKey", "LnLean.Proofs.Bitcoin.ToLocalScriptTargets.commitmentOutputs_toLocal_commits_delay_and_revocationKey"]⟩
  , ⟨"LnLean.Bitcoin.anchorValue_eq", ["LnLean.Bitcoin.anchorValue_eq"]⟩
  , ⟨"LnLean.Proofs.Bitcoin.commitmentBaseWeight_model_target", ["LnLean.Proofs.Bitcoin.commitmentBaseWeight_model_target"]⟩
  , ⟨"LnLean.Crypto.Hash.paymentHash_sha256_contract", ["LnLean.Crypto.Hash.paymentHash_sha256_contract"]⟩
  , ⟨"LnLean.Crypto.Sig.commitmentSig_contract", ["LnLean.Crypto.Sig.commitmentSig_contract"]⟩
  , ⟨"LnLean.Crypto.Hash.onionHmacTag_size_and_bindsOn", ["LnLean.Crypto.Hash.onionHmacTag_size_and_bindsOn"]⟩
  , ⟨"LnLean.Wire.decode_encode", ["LnLean.Wire.decode_encode"]⟩
  , ⟨"LnLean.Wire.TLVStream.wellFormed_iff_pairwise; LnLean.Wire.TLVStream.wellFormed_record_type_unique", ["LnLean.Wire.TLVStream.wellFormed_iff_pairwise", "LnLean.Wire.TLVStream.wellFormed_record_type_unique"]⟩
  , ⟨"LnLean.Wire.Message.decode_length", ["LnLean.Wire.Message.decode_length"]⟩
  , ⟨"LnLean.Security.Ledger.step_conserves", ["LnLean.Security.Ledger.step_conserves"]⟩
  , ⟨"LnLean.Channel.Commitment.outputs_nonnegative", ["LnLean.Channel.Commitment.outputs_nonnegative"]⟩
  , ⟨"LnLean.Channel.Commitment.output_ordering", ["LnLean.Channel.Commitment.output_ordering"]⟩
  , ⟨"LnLean.Security.advance_monotone", ["LnLean.Security.advance_monotone"]⟩
  , ⟨"LnLean.Channel.Fee.commitmentSigningGate_rejected_iff_insufficient; LnLean.Channel.Fee.commitmentSigningGate_rejected_iff_no_checkedSigning", ["LnLean.Channel.Fee.commitmentSigningGate_rejected_iff_insufficient", "LnLean.Channel.Fee.commitmentSigningGate_rejected_iff_no_checkedSigning"]⟩
  , ⟨"LnLean.Channel.Reserve.bounds", ["LnLean.Channel.Reserve.bounds"]⟩
  , ⟨"LnLean.Security.HtlcRecord.fulfill_sound", ["LnLean.Security.HtlcRecord.fulfill_sound"]⟩
  , ⟨"LnLean.Security.HtlcRecord.fail_only_after_expiry", ["LnLean.Security.HtlcRecord.fail_only_after_expiry"]⟩
  , ⟨"LnLean.Channel.HTLC.amount_conservation", ["LnLean.Channel.HTLC.amount_conservation"]⟩
  , ⟨"LnLean.Channel.HTLC.dir_id_unique; LnLean.Channel.HTLC.id_unique_of_reachable_cross; LnLean.Channel.HTLC.tagged_id_unique_of_reachable; LnLean.Channel.HTLC.tagged_ids_nodup_of_reachable; LnLean.Channel.HTLC.cross_direction_duplicate_tagged", ["LnLean.Channel.HTLC.dir_id_unique", "LnLean.Channel.HTLC.id_unique_of_reachable_cross", "LnLean.Channel.HTLC.tagged_id_unique_of_reachable", "LnLean.Channel.HTLC.tagged_ids_nodup_of_reachable", "LnLean.Channel.HTLC.cross_direction_duplicate_tagged"]⟩
  , ⟨"LnLean.Security.revoked_commitment_is_old", ["LnLean.Security.revoked_commitment_is_old"]⟩
  , ⟨"LnLean.Security.breach_penalty_spends_both", ["LnLean.Security.breach_penalty_spends_both"]⟩
  , ⟨"LnLean.Protocol.Handshake.open_bounds", ["LnLean.Protocol.Handshake.open_bounds"]⟩
  , ⟨"LnLean.Protocol.Handshake.channel_ready_gate", ["LnLean.Protocol.Handshake.channel_ready_gate"]⟩
  , ⟨"LnLean.Protocol.Handshake.funding_signed_signing_contract", ["LnLean.Protocol.Handshake.funding_signed_signing_contract"]⟩
  , ⟨"LnLean.Proofs.ProtocolWireTargets.commitment_signed_full_covers_exact; LnLean.Proofs.ProtocolWireTargets.protocol_wire_summary", ["LnLean.Proofs.ProtocolWireTargets.commitment_signed_full_covers_exact", "LnLean.Proofs.ProtocolWireTargets.protocol_wire_summary"]⟩
  , ⟨"LnLean.Protocol.Peer.reestablish_no_rollback", ["LnLean.Protocol.Peer.reestablish_no_rollback"]⟩
  , ⟨"LnLean.Protocol.Handshake.feature_intersection", ["LnLean.Protocol.Handshake.feature_intersection"]⟩
  , ⟨"LnLean.Security.Route.wellFormed_connected; LnLean.Security.Route.wellFormed_capacity; LnLean.Security.Route.wellFormed_nonempty", ["LnLean.Security.Route.wellFormed_connected", "LnLean.Security.Route.wellFormed_capacity", "LnLean.Security.Route.wellFormed_nonempty"]⟩
  , ⟨"LnLean.Routing.Gossip.update_monotone", ["LnLean.Routing.Gossip.update_monotone"]⟩
  , ⟨"LnLean.Routing.Onion.peel_deterministic", ["LnLean.Routing.Onion.peel_deterministic"]⟩
  , ⟨"LnLean.Routing.Onion.hmac_sound", ["LnLean.Routing.Onion.hmac_sound"]⟩
  , ⟨"LnLean.Routing.Route.cltv_accumulates", ["LnLean.Routing.Route.cltv_accumulates"]⟩
  , ⟨"LnLean.Proofs.Routing.GossipTargets.gossip_graph_only_valid_announcements", ["LnLean.Proofs.Routing.GossipTargets.gossip_graph_only_valid_announcements"]⟩
  , ⟨"LnLean.Security.Invoice.consistent_hash; LnLean.Security.Invoice.consistent_amount", ["LnLean.Security.Invoice.consistent_hash", "LnLean.Security.Invoice.consistent_amount"]⟩
  , ⟨"LnLean.Payment.Invoice.signature_valid", ["LnLean.Payment.Invoice.signature_valid"]⟩
  , ⟨"LnLean.Payment.Invoice.payment_secret_match", ["LnLean.Payment.Invoice.payment_secret_match"]⟩
  , ⟨"LnLean.Security.MppPayment.settle_requires_sum", ["LnLean.Security.MppPayment.settle_requires_sum"]⟩
  , ⟨"LnLean.Payment.MPP.running_total_bound", ["LnLean.Payment.MPP.running_total_bound"]⟩
  , ⟨"LnLean.Payment.Keysend.preimage_binding", ["LnLean.Payment.Keysend.preimage_binding"]⟩
  , ⟨"LnLean.Security.L1Ledger.spend_preserves_noDoubleSpend", ["LnLean.Security.L1Ledger.spend_preserves_noDoubleSpend"]⟩
  , ⟨"LnLean.Proofs.Conservation.global_conservation", ["LnLean.Proofs.Conservation.global_conservation"]⟩
  , ⟨"LnLean.Proofs.Security.safety_async", ["LnLean.Proofs.Security.safety_async"]⟩
  , ⟨"LnLean.Security.partial_synchrony_delivers", ["LnLean.Security.partial_synchrony_delivers"]⟩
  , ⟨"LnLean.Proofs.Liveness.penalty_economical", ["LnLean.Proofs.Liveness.penalty_economical"]⟩
  , ⟨"LnLean.Proofs.Liveness.watchtower_bridge", ["LnLean.Proofs.Liveness.watchtower_bridge"]⟩
  ]

/-- Every declaration named by a `proved` row, transcribed from the model
modules (`LnLean/Wire/Message`, `LnLean/Protocol/Peer`, the routing modules,
`LnLean/Payment/Invoice`, `LnLean/Payment/MPP`), the foundational
`LnLean/Bitcoin/Seam`, `LnLean/Security/Invariants`, `LnLean/Wire/BigSize`,
and the proof modules `LnLean.Proofs.Conservation`,
`LnLean.Proofs.ProtocolTargets`, `LnLean.Proofs.CryptoTargets`,
`LnLean.Proofs.PhaseC2.GlobalConservation`,
`LnLean.Proofs.PhaseC3.SecurityGame`, `LnLean.Proofs.Liveness`, and
`LnLean.Proofs.WaveD.D14`, `D18`, `D29`, `LnLean.Proofs.WaveE.E31`.  Adding a
`proved` row with an unlisted target makes `proved_decls_in_snapshot` fail,
which is the intended maintenance signal. -/
def provedDeclarations : List DeclEntry :=
  [ ⟨"LnLean.Bitcoin.fundingOutput_moneyRange", "LnLean.Bitcoin.Seam"⟩
  , ⟨"LnLean.Bitcoin.anchorValue_eq", "LnLean.Bitcoin.Seam"⟩
  , ⟨"LnLean.Crypto.Hash.paymentHash_sha256_contract", "LnLean.Proofs.CryptoTargets"⟩
  , ⟨"LnLean.Crypto.Sig.commitmentSig_contract", "LnLean.Proofs.CryptoTargets"⟩
  , ⟨"LnLean.Crypto.Hash.onionHmacTag_size_and_bindsOn", "LnLean.Proofs.CryptoTargets"⟩
  , ⟨"LnLean.Wire.decode_encode", "LnLean.Wire.BigSize"⟩
  , ⟨"LnLean.Security.Ledger.step_conserves", "LnLean.Security.Invariants"⟩
  , ⟨"LnLean.Channel.Commitment.outputs_nonnegative", "LnLean.Channel.Commitment"⟩
  , ⟨"LnLean.Security.advance_monotone", "LnLean.Security.Invariants"⟩
  , ⟨"LnLean.Channel.Reserve.bounds", "LnLean.Proofs.WaveD.D14"⟩
  , ⟨"LnLean.Security.HtlcRecord.fulfill_sound", "LnLean.Security.Invariants"⟩
  , ⟨"LnLean.Security.HtlcRecord.fail_only_after_expiry", "LnLean.Security.Invariants"⟩
  , ⟨"LnLean.Channel.HTLC.amount_conservation", "LnLean.Channel.HTLC"⟩
  , ⟨"LnLean.Security.revoked_commitment_is_old", "LnLean.Security.Invariants"⟩
  , ⟨"LnLean.Security.breach_penalty_spends_both", "LnLean.Security.Invariants"⟩
  , ⟨"LnLean.Protocol.Handshake.channel_ready_gate", "LnLean.Proofs.WaveD.D18"⟩
  , ⟨"LnLean.Protocol.Handshake.open_bounds", "LnLean.Proofs.ProtocolTargets"⟩
  , ⟨"LnLean.Protocol.Handshake.feature_intersection", "LnLean.Proofs.ProtocolTargets"⟩
  , ⟨"LnLean.Security.Route.wellFormed_connected", "LnLean.Security.Invariants"⟩
  , ⟨"LnLean.Security.Route.wellFormed_capacity", "LnLean.Security.Invariants"⟩
  , ⟨"LnLean.Security.Route.wellFormed_nonempty", "LnLean.Security.Invariants"⟩
  , ⟨"LnLean.Security.Invoice.consistent_hash", "LnLean.Security.Invariants"⟩
  , ⟨"LnLean.Security.Invoice.consistent_amount", "LnLean.Security.Invariants"⟩
  , ⟨"LnLean.Payment.Invoice.payment_secret_match", "LnLean.Proofs.WaveD.D29"⟩
  , ⟨"LnLean.Security.MppPayment.settle_requires_sum", "LnLean.Security.Invariants"⟩
  , ⟨"LnLean.Payment.Keysend.preimage_binding", "LnLean.Proofs.WaveE.E31"⟩
  , ⟨"LnLean.Security.L1Ledger.spend_preserves_noDoubleSpend", "LnLean.Security.Invariants"⟩
  , ⟨"LnLean.Security.partial_synchrony_delivers", "LnLean.Security.Invariants"⟩
  , ⟨"LnLean.Proofs.Liveness.penalty_economical", "LnLean.Proofs.Liveness"⟩
  , ⟨"LnLean.Wire.Message.decode_length", "LnLean.Wire.Message"⟩
  , ⟨"LnLean.Protocol.Peer.reestablish_no_rollback", "LnLean.Protocol.Peer"⟩
  , ⟨"LnLean.Routing.Gossip.update_monotone", "LnLean.Routing.Gossip"⟩
  , ⟨"LnLean.Routing.Onion.peel_deterministic", "LnLean.Routing.Onion"⟩
  , ⟨"LnLean.Routing.Onion.hmac_sound", "LnLean.Routing.Onion"⟩
  , ⟨"LnLean.Routing.Route.cltv_accumulates", "LnLean.Routing.Route"⟩
  , ⟨"LnLean.Payment.Invoice.signature_valid", "LnLean.Payment.Invoice"⟩
  , ⟨"LnLean.Payment.MPP.running_total_bound", "LnLean.Payment.MPP"⟩
  , ⟨"LnLean.Proofs.Conservation.global_conservation", "LnLean.Proofs.PhaseC2.GlobalConservation"⟩
  , ⟨"LnLean.Proofs.Security.safety_async", "LnLean.Proofs.PhaseC3.SecurityGame"⟩
  , ⟨"LnLean.Proofs.Liveness.watchtower_bridge", "LnLean.Proofs.Liveness"⟩
  , ⟨"LnLean.Proofs.Bitcoin.FundingScriptTargets.fundingScriptPubKey_eq_p2wsh_twoOfTwo", "LnLean.Proofs.Bitcoin.FundingScriptTargets"⟩
  , ⟨"LnLean.Proofs.Security.ReorgTargets.reorg_preserves_channel_safety", "LnLean.Proofs.Security.ReorgTargets"⟩
  , ⟨"LnLean.Proofs.Security.ReorgTargets.deep_reorg_separate_failure_mode", "LnLean.Proofs.Security.ReorgTargets"⟩
  , ⟨"LnLean.Proofs.Bitcoin.ToLocalScriptTargets.toLocalScriptFull_carries_csv_and_revocationKey", "LnLean.Proofs.Bitcoin.ToLocalScriptTargets"⟩
  , ⟨"LnLean.Proofs.Bitcoin.ToLocalScriptTargets.toLocalScriptFull_commits_delay_and_revocationKey", "LnLean.Proofs.Bitcoin.ToLocalScriptTargets"⟩
  , ⟨"LnLean.Proofs.Bitcoin.ToLocalScriptTargets.commitmentOutputs_toLocal_commits_delay_and_revocationKey", "LnLean.Proofs.Bitcoin.ToLocalScriptTargets"⟩
  , ⟨"LnLean.Proofs.Bitcoin.commitmentBaseWeight_model_target", "LnLean.Proofs.Bitcoin.WeightTargets"⟩
  , ⟨"LnLean.Wire.TLVStream.wellFormed_iff_pairwise", "LnLean.Proofs.Wire.TLVTargets"⟩
  , ⟨"LnLean.Wire.TLVStream.wellFormed_record_type_unique", "LnLean.Proofs.Wire.TLVTargets"⟩
  , ⟨"LnLean.Channel.Commitment.output_ordering", "LnLean.Proofs.Channel.CommitmentOrderTargets"⟩
  , ⟨"LnLean.Channel.Fee.commitmentSigningGate_rejected_iff_insufficient", "LnLean.Proofs.Channel.FeeTargets"⟩
  , ⟨"LnLean.Channel.Fee.commitmentSigningGate_rejected_iff_no_checkedSigning", "LnLean.Proofs.Channel.FeeTargets"⟩
  , ⟨"LnLean.Channel.HTLC.dir_id_unique", "LnLean.Channel.HTLC"⟩
  , ⟨"LnLean.Channel.HTLC.id_unique_of_reachable_cross", "LnLean.Channel.HTLC"⟩
  , ⟨"LnLean.Protocol.Handshake.funding_signed_signing_contract", "LnLean.Proofs.ProtocolSigningTargets"⟩
  , ⟨"LnLean.Proofs.Routing.GossipTargets.gossip_graph_only_valid_announcements", "LnLean.Proofs.Routing.GossipTargets"⟩
  , ⟨"LnLean.Channel.HTLC.tagged_id_unique_of_reachable", "LnLean.Proofs.Channel.HtlcGlobalIdTargets"⟩
  , ⟨"LnLean.Channel.HTLC.tagged_ids_nodup_of_reachable", "LnLean.Proofs.Channel.HtlcGlobalIdTargets"⟩
  , ⟨"LnLean.Channel.HTLC.cross_direction_duplicate_tagged", "LnLean.Proofs.Channel.HtlcGlobalIdTargets"⟩
  , ⟨"LnLean.Proofs.ProtocolWireTargets.commitment_signed_full_covers_exact", "LnLean.Proofs.ProtocolWireTargets"⟩
  , ⟨"LnLean.Proofs.ProtocolWireTargets.protocol_wire_summary", "LnLean.Proofs.ProtocolWireTargets"⟩
  ]

/-- Modules named by the catalog, all of them under `LnLean`. -/
def lneanModules : List String :=
  [ "LnLean.Bitcoin.Seam"
  , "LnLean.Security.Model"
  , "LnLean.Crypto.Hash"
  , "LnLean.Crypto.Sig"
  , "LnLean.Wire.BigSize"
  , "LnLean.Wire.TLV"
  , "LnLean.Wire.Message"
  , "LnLean.Security.Invariants"
  , "LnLean.Channel.Commitment"
  , "LnLean.Channel.Fee"
  , "LnLean.Channel.Reserve"
  , "LnLean.Channel.HTLC"
  , "LnLean.Protocol.Handshake"
  , "LnLean.Protocol.Messages"
  , "LnLean.Protocol.Peer"
  , "LnLean.Routing.Gossip"
  , "LnLean.Routing.Onion"
  , "LnLean.Routing.Route"
  , "LnLean.Payment.Invoice"
  , "LnLean.Payment.MPP"
  , "LnLean.Payment.Keysend"
  , "LnLean.Proofs.Conservation"
  , "LnLean.Proofs.ProtocolTargets"
  , "LnLean.Proofs.CryptoTargets"
  , "LnLean.Proofs.PhaseC2.GlobalConservation"
  , "LnLean.Proofs.Security"
  , "LnLean.Proofs.PhaseC3.SecurityGame"
  , "LnLean.Proofs.Liveness"
  , "LnLean.Proofs.WaveD.D14"
  , "LnLean.Proofs.WaveD.D18"
  , "LnLean.Proofs.WaveD.D29"
  , "LnLean.Proofs.WaveE.E31"
  , "LnLean.Proofs.Bitcoin.FundingScriptTargets"
  , "LnLean.Proofs.Bitcoin.ToLocalScriptTargets"
  , "LnLean.Proofs.Bitcoin.WeightTargets"
  , "LnLean.Proofs.Channel.CommitmentOrderTargets"
  , "LnLean.Proofs.Channel.FeeTargets"
  , "LnLean.Proofs.ProtocolCoverageTargets"
  , "LnLean.Proofs.ProtocolSigningTargets"
  , "LnLean.Proofs.Routing.GossipTargets"
  , "LnLean.Proofs.Security.ReorgTargets"
  , "LnLean.Proofs.Wire.TLVTargets"
  , "LnLean.Proofs.Bitcoin.SpendTargets"
  , "LnLean.Proofs.Channel.CommitmentIntegrationTargets"
  , "LnLean.Proofs.Channel.HtlcGlobalIdTargets"
  , "LnLean.Proofs.ConformanceTargets"
  , "LnLean.Proofs.ProtocolWireTargets"
  , "LnLean.Proofs.Routing.GossipAttributionTargets"
  ]

/-- The 48 ids of `docs/THEOREM-INDEX.md`, in table order. -/
def theoremIndexIds : List String :=
  [ "LN-L1-001", "LN-L1-002", "LN-L1-003", "LN-L1-004", "LN-L1-005", "LN-L1-006"
  , "LN-CR-001", "LN-CR-002", "LN-CR-003", "LN-CR-004", "LN-CR-005", "LN-CR-006"
  , "LN-CH-001", "LN-CH-002", "LN-CH-003", "LN-CH-004", "LN-CH-005", "LN-CH-006"
  , "LN-HT-001", "LN-HT-002", "LN-HT-003", "LN-HT-004", "LN-HT-005", "LN-HT-006"
  , "LN-PR-001", "LN-PR-002", "LN-PR-003", "LN-PR-004", "LN-PR-005", "LN-PR-006"
  , "LN-RT-001", "LN-RT-002", "LN-RT-003", "LN-RT-004", "LN-RT-005", "LN-RT-006"
  , "LN-PM-001", "LN-PM-002", "LN-PM-003", "LN-PM-004", "LN-PM-005", "LN-PM-006"
  , "LN-SEC-001", "LN-SEC-002", "LN-SEC-003", "LN-SEC-004", "LN-SEC-005"
  , "LN-SEC-006" ]

/-- The 48 ids of `docs/TRACEABILITY.md`, in table order. -/
def traceabilityIds : List String :=
  [ "LN-L1-001", "LN-L1-002", "LN-L1-003", "LN-L1-004", "LN-L1-005", "LN-L1-006"
  , "LN-CR-001", "LN-CR-002", "LN-CR-003", "LN-CR-004", "LN-CR-005", "LN-CR-006"
  , "LN-CH-001", "LN-CH-002", "LN-CH-003", "LN-CH-004", "LN-CH-005", "LN-CH-006"
  , "LN-HT-001", "LN-HT-002", "LN-HT-003", "LN-HT-004", "LN-HT-005", "LN-HT-006"
  , "LN-PR-001", "LN-PR-002", "LN-PR-003", "LN-PR-004", "LN-PR-005", "LN-PR-006"
  , "LN-RT-001", "LN-RT-002", "LN-RT-003", "LN-RT-004", "LN-RT-005", "LN-RT-006"
  , "LN-PM-001", "LN-PM-002", "LN-PM-003", "LN-PM-004", "LN-PM-005", "LN-PM-006"
  , "LN-SEC-001", "LN-SEC-002", "LN-SEC-003", "LN-SEC-004", "LN-SEC-005"
  , "LN-SEC-006" ]

/-! ## Enumeration lemmas -/

/-- The domain enumeration covers every constructor of `Domain`. -/
theorem domains_exhaustive (d : Domain) : d ∈ domains := by
  cases d <;> simp [domains]

/-- The status enumeration covers every constructor of `ObligationStatus`. -/
theorem statuses_exhaustive (s : ObligationStatus) : s ∈ statuses := by
  cases s <;> simp [statuses]

/-- The executable well-formedness test is exactly the structural predicate. -/
theorem rowWellFormed_iff (o : Obligation) :
    rowWellFormed o = true ↔ RowWellFormed o := by
  simp [rowWellFormed, RowWellFormed, Bool.and_eq_true, and_assoc]

/-! ## Catalog checks -/

/-- Every catalog row has a non-empty id, English claim, BOLT section, and
anchor. -/
theorem obligations_rows_well_formed : obligations.all rowWellFormed = true := by
  decide

/-- Consequently, `RowWellFormed` holds of every row. -/
theorem obligations_rows_well_formed' (o : Obligation) (h : o ∈ obligations) :
    RowWellFormed o := by
  have hcheck : rowWellFormed o = true :=
    (List.all_eq_true.mp obligations_rows_well_formed) o h
  exact (rowWellFormed_iff o).mp hcheck

/-- Catalog ids are pairwise distinct. -/
theorem obligations_ids_nodup : (obligations.map (fun o => o.id)).Nodup := by
  decide

/-- The catalog's id sequence equals the transcribed id table. -/
theorem obligations_ids_in_table :
    obligations.map (fun o => o.id) = idTable.map (fun e => e.text) := by
  decide

/-- Every transcribed id uses one of the eight area codes. -/
theorem id_areas_known :
    idTable.all (fun e => decide (e.area ∈ idAreas)) = true := by
  decide

/-- Every transcribed id has a numeric suffix in `1..6`. -/
theorem id_numbers_in_range :
    idTable.all (fun e => decide (1 ≤ e.number ∧ e.number ≤ 6)) = true := by
  decide

/-- Each of the eight area codes occurs exactly six times. -/
theorem id_six_per_area :
    idAreas.all (fun a => (idTable.filter (fun e => decide (e.area = a))).length = 6) = true := by
  decide

/-- The area codes are pairwise distinct. -/
theorem id_areas_nodup : idAreas.Nodup := by
  decide

/-- Every status is one of the two enumerated statuses. -/
theorem obligations_statuses_enumerated :
    obligations.all (fun o => statuses.contains o.status) = true := by
  decide

/-- Every domain is one of the eight enumerated domains. -/
theorem obligations_domains_enumerated :
    obligations.all (fun o => domains.contains o.domain) = true := by
  decide

/-- The catalog has at least 40 rows (it has 48). -/
theorem obligations_count_ge_40 : 40 ≤ obligations.length := by
  decide

/-- The catalog covers exactly eight distinct domains. -/
theorem obligations_domain_count :
    (obligations.map (fun o => o.domain)).eraseDups.length = 8 := by
  decide

/-- Every one of the eight domains occurs in the catalog. -/
theorem every_domain_used :
    domains.all (fun d => (obligations.map (fun o => o.domain)).contains d) = true := by
  decide

/-! ## Target checks -/

/-- Every row has a non-empty `leanTarget`. -/
theorem obligations_targets_nonempty :
    obligations.all (fun o => decide (o.leanTarget ≠ "")) = true := by
  decide

/-- The catalog's `leanTarget` sequence equals the transcribed target table. -/
theorem obligations_targets_in_table :
    obligations.map (fun o => o.leanTarget) = targetTable.map (fun e => e.text) := by
  decide

/-- Every target lists at least one module. -/
theorem target_modules_nonempty :
    targetTable.all (fun e => decide (e.modules ≠ [])) = true := by
  decide

/-- Every module referred to by a target is one of the fixed `LnLean.*`
modules. -/
theorem target_modules_lnean :
    targetTable.all
      (fun e => e.modules.all (fun m => decide (m ∈ lneanModules))) = true := by
  decide

/-! ## `proved` rows -/

/-- The 48 `proved` rows' target strings equal the transcribed table. -/
theorem proved_rows_in_table :
    (obligations.filter (fun o => o.status == .proved)).map (fun o => o.leanTarget) =
      provedTable.map (fun e => e.target) := by
  decide

/-- Every `proved` row names at least one declaration. -/
theorem proved_rows_have_decls :
    provedTable.all (fun e => decide (e.decls ≠ [])) = true := by
  decide

/-- Every declaration named by a `proved` row occurs in the snapshot. -/
theorem proved_decls_in_snapshot :
    provedTable.all
      (fun e => e.decls.all
        (fun d => provedDeclarations.any (fun p => decide (p.text = d)))) = true := by
  decide

/-- Every snapshot declaration is used by some `proved` row (no stale
entries). -/
theorem proved_snapshot_all_used :
    provedDeclarations.all
      (fun p => provedTable.any
        (fun e => e.decls.any (fun d => decide (d = p.text)))) = true := by
  decide

/-- The snapshot contains no duplicate declaration name. -/
theorem proved_declarations_nodup :
    (provedDeclarations.map (fun p => p.text)).Nodup := by
  decide

/-- Every declaration in the snapshot lives in a module from
`lneanModules`. -/
theorem proved_declaration_modules_lnean :
    provedDeclarations.all (fun p => decide (p.module ∈ lneanModules)) = true := by
  decide

/-- Exactly 48 rows are `proved`, matching the `docs/THEOREM-INDEX.md`
summary table. -/
theorem proved_row_count :
    (obligations.filter (fun o => o.status == .proved)).length = 48 := by
  decide

/-- Exactly 0 rows are `statementOnly`, matching the
`docs/THEOREM-INDEX.md` summary table. -/
theorem statement_only_row_count :
    (obligations.filter (fun o => o.status == .statementOnly)).length = 0 := by
  decide

/-- No row uses the `UNANCHORED` fallback, matching the anchor policy in
`docs/TRACEABILITY.md`. -/
theorem no_unanchored_rows :
    obligations.all (fun o => decide (o.rlAnchor ≠ "UNANCHORED")) = true := by
  decide

/-! ## Agreement with the two Markdown tables -/

/-- The id sequence of the Lean catalog equals the id sequence of
`docs/THEOREM-INDEX.md`. -/
theorem catalog_ids_match_theorem_index :
    obligations.map (fun o => o.id) = theoremIndexIds := by
  decide

/-- The id sequence of the Lean catalog equals the id sequence of
`docs/TRACEABILITY.md`. -/
theorem catalog_ids_match_traceability :
    obligations.map (fun o => o.id) = traceabilityIds := by
  decide

/-- The two Markdown tables agree with each other on ids. -/
theorem index_ids_match_traceability : theoremIndexIds = traceabilityIds := by
  decide

/-! ## Small witnesses

These guard against a well-formedness predicate that accepts everything or
nothing. -/

/-- A concrete row that satisfies all four non-emptiness requirements. -/
def sampleRow : Obligation :=
  { id := "LN-L1-001"
    domain := .l1
    claim := "The funding output is P2WSH over the 2-of-2 funding witness script."
    leanTarget := "LnLean.Bitcoin.fundingScriptPubKey"
    status := .statementOnly
    boltdoc := "BOLT 2 §Channel Establishment v1"
    rlAnchor := "lightning/src/ln/chan_utils.rs:847" }

/-- The witness row is well formed. -/
theorem sampleRow_wellFormed : RowWellFormed sampleRow := by
  exact (rowWellFormed_iff sampleRow).mp (by decide)

/-- An empty id makes a row ill formed. -/
theorem emptyId_not_wellFormed : ¬ RowWellFormed { sampleRow with id := "" } := by
  intro h
  have h' : rowWellFormed { sampleRow with id := "" } = true :=
    (rowWellFormed_iff _).mpr h
  have h'' : rowWellFormed { sampleRow with id := "" } = false := by decide
  rw [h''] at h'
  cases h'

/-- `statuses` has two elements. -/
theorem statuses_length : statuses.length = 2 := rfl

/-- `domains` has eight elements. -/
theorem domains_length : domains.length = 8 := rfl

/-- `lneanModules` has no duplicates. -/
theorem lneanModules_nodup : lneanModules.Nodup := by
  decide

end LnLean.Proofs.Traceability
