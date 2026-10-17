#!/usr/bin/env python3
"""Generate the 32 wave-B proof-scaffold briefs.

Every B file lives under LnLean/Proofs/, so `sorry` is legal there under the
repository's obligation-marker rule.  The briefs deliberately tell each agent
to read the actual wave-A modules before choosing declaration names: wave A
is allowed to choose the final field/function names, and a proof scaffold
must bind to the model that exists, not to a guess.
"""
import pathlib

OUT = pathlib.Path("/home/ubuntu/ln-lean/agents/briefs")
OUT.mkdir(parents=True, exist_ok=True)

COMMON = """You are {name}, one of 32 proof-scaffold agents for `ln-lean`, a Lean 4
formal model of the Lightning Network built on the existing Bitcoin L1 model.

WORKDIR: /home/ubuntu/ln-lean  (all work happens there; this is the peer box)

READ FIRST, in this order:
1. docs/AGENT-PROTOCOL.md  (binding rules)
2. docs/ARCHITECTURE.md and docs/ASSUMPTIONS.md
3. agents/OWNERSHIP.md and agents/WAVE-PLAN.md
4. Your wave-A modules (listed below), plus LnLean/Basic/Core.lean and
   LnLean/Bitcoin/Seam.lean as needed.
5. refs/bolts and refs/rust-lightning at the pinned commits in refs/PINNED.md.

HARD RULES
- Write ONLY:
    {path}
    agents/reports/{name}.md
  Never edit another agent's file, LnLean.lean, lakefile.lean,
  lean-toolchain, docs/{{CHARTER,ARCHITECTURE,ASSUMPTIONS,AGENT-PROTOCOL}}.md,
  refs/**, or vendor/btc-lean-core/**. The L1 snapshot is read-only.
- The file is under LnLean/Proofs/, so `sorry` is allowed, but ONLY with a
  marker on the same line or the immediately preceding line:
      -- OBLIGATION: LN-<AREA>-<NNN> <English claim>
  No `axiom`, `admit`, `native_decide`, `unsafe`, `@[implemented_by]`, or
  mathlib. Every file needs `set_option autoImplicit false`.
- Start the file with a module docstring: English claim, BOLT section(s),
  rust-lightning `path:line` anchors at the pinned commit, and what is
  explicitly NOT modelled.
- Import only the wave-A modules listed below (plus Lean core and
  Bitcoin.Data.*). Do not import another wave-B module.
- State at least 6 non-trivial obligations/theorems. At least one must be a
  checked structural lemma (rfl/simp/omega/decide on a small finite fact);
  the rest may be `sorry` with markers. Do not overclaim: if a statement is
  false or cannot be expressed with the current model, state the corrected
  or conditional version and record the gap in your report.
- Read the actual wave-A files before writing. If a field or function has a
  different name than this brief guesses, use the real one.

BUILD (exact module, shared lock, never bare `lake build`):
  export PATH=/dev/shm/btc/elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
  cd /home/ubuntu/ln-lean
  flock -w 900 /tmp/ln-build.lock lake build {module}

COMMIT (shared git lock, only your two paths):
  cd /home/ubuntu/ln-lean
  MSG="[{name}] {short}" ./scripts/agent-commit.sh {name} \\
    {path} agents/reports/{name}.md

REPORT: agents/reports/{name}.md must contain (1) the file and exact build
RC, (2) a declaration table: name | statement | proved / sorry+obligation id,
(3) BOLT and rust-lightning anchors used, (4) what remains open and the
next smallest proof step, (5) exact reproduce commands. A report must not
claim anything that is not in the tree.

FINAL MESSAGE: <= 10 lines. File, build RC, theorem/obligation count, and
anything the integrator must merge or repair.

MISSION
{body}
"""

# name: (path, module, imports, short, body)
B = {}

B["B01"] = (
    "LnLean/Proofs/Bitcoin/FundingProps.lean",
    "LnLean.Proofs.Bitcoin.FundingProps",
    "LnLean.Bitcoin.Funding, LnLean.Bitcoin.Seam, LnLean.Basic.Core",
    "funding output laws",
    """
Prove the funding-output seam:
- the funding witness script is 2-of-2 over the two funding keys and its
  SHA-256/P2WSH wrapper has the expected 34-byte scriptPubKey;
- `fundingOutpoint` is the (txid, index) pair and the index is a `UInt32`;
- a `FundingConfirmed` output carries exactly the funding value and is in
  `MoneyRange`;
- the final channel id is derived from the funding txid and is stable under
  the temporary -> final transition;
- funding output value plus push amount equals the channel capacity under
  the model's hypotheses;
- a funding output cannot be spent by anyone other than the 2-of-2 path
  (state this as a conditional predicate over the L1 interpreter, not as a
  proved consensus theorem).
Anchor to BOLT 2 sections 2-3 and LDK `lightning/src/ln/chan_utils.rs`
(`build_funding_script`/funding output construction) and
`lightning/src/ln/channel.rs`.
""")

B["B02"] = (
    "LnLean/Proofs/Bitcoin/ScriptProps.lean",
    "LnLean.Proofs.Bitcoin.ScriptProps",
    "LnLean.Bitcoin.ScriptTemplates, LnLean.Bitcoin.Seam",
    "commitment scripts",
    """
Prove the BOLT 3 commitment script templates:
- `to_local` contains the revocation key and the CSV delay, and its script
  length is determined by the template;
- `to_remote` is a P2WPKH/P2WSH template with the remote payment key;
- offered and received HTLC templates contain the payment hash, the CLTV
  branch and the counterparty key; the two templates are distinguishable;
- the anchor output script and value are the BOLT 3 anchor constants;
- output construction is deterministic and total on well-formed keys/hashes;
- a malformed key/hash length is rejected by the model's validity predicate.
Anchor to BOLT 3 section 2 and LDK `lightning/src/ln/chan_utils.rs`
(`get_commitment_transaction_number_obscure_factor`,
`build_commitment_transaction`, script template helpers).
""")

B["B03"] = (
    "LnLean/Proofs/Bitcoin/AnchorProps.lean",
    "LnLean.Proofs.Bitcoin.AnchorProps",
    "LnLean.Bitcoin.Funding, LnLean.Bitcoin.Laws, LnLean.Bitcoin.Seam",
    "anchor output laws",
    """
Prove the anchor-output rules:
- an anchor output has value 330 sat and there are at most two anchors in a
  commitment;
- anchor outputs are present exactly when the anchor feature is negotiated;
- the anchor script is the model's P2WSH/P2WPKH anchor template;
- an anchor is spendable only by the party that owns the corresponding
  commitment (state as a predicate over the L1 script semantics);
- anchor value is excluded from the fee calculation in the model's stated
  way, or the exact inclusion rule is recorded;
- the anchor output does not change the to_local/to_remote conservation
  equation except through the fee term.
Anchor to BOLT 3 anchor-output section and LDK `lightning/src/ln/chan_utils.rs`
(anchor script and `ANCHOR_OUTPUT_VALUE`).
""")

B["B04"] = (
    "LnLean/Proofs/Bitcoin/WeightProps.lean",
    "LnLean.Proofs.Bitcoin.WeightProps",
    "LnLean.Bitcoin.Laws, LnLean.Bitcoin.Seam, LnLean.Basic.Core",
    "weight and fee formulas",
    """
Prove the BOLT 3 weight arithmetic:
- base commitment weight is 724 for the modelled anchor variant and each
  offered/received HTLC adds 172;
- `commitmentWeight n` is monotone in the HTLC count and strictly positive;
- the fee is `ceil(feerate * weight / 1000)` (or the model's exact rounding)
  and is monotone in both feerate and weight;
- the commitment fee cannot exceed the funding value under the model's
  well-formedness hypotheses;
- adding an HTLC never decreases the commitment weight;
- the weight formula agrees with the model's `commitmentWeight` definition.
Anchor to BOLT 3 commitment-weight constants and LDK
`lightning/src/ln/chan_utils.rs` (`commitment_tx_base_weight`,
`commitment_tx_htlc_weight`).
""")

B["B05"] = (
    "LnLean/Proofs/Crypto/Sha256Props.lean",
    "LnLean.Proofs.Crypto.Sha256Props",
    "LnLean.Crypto.Hash, LnLean.Crypto.Model, LnLean.Basic.Core",
    "hash interface laws",
    """
Prove the structural hash laws:
- `sha256` returns a 32-byte value for every input; `hash160` returns 20;
- hashing is deterministic and extensional on the model's byte arrays;
- a hash-lock `opensTo h pre` implies `sha256 pre = h` (definitional);
- collision resistance and preimage resistance are *assumptions* recorded
  as `Prop` fields of the primitive model, never axioms;
- a payment hash commits to a preimage only under the preimage-resistance
  assumption; state that conditional theorem;
- domain-separated tagged hashes produce different tags for different
  domains (structural, not cryptographic).
Anchor to BOLT 1/2 and LDK `lightning/src/util/sha256.rs` or the pinned
`bitcoin_hashes` usage; record the exact path/line you use.
""")

B["B06"] = (
    "LnLean/Proofs/Crypto/EcdsaProps.lean",
    "LnLean.Proofs.Crypto.EcdsaProps",
    "LnLean.Crypto.Sig, LnLean.Crypto.Model, LnLean.Basic.Core",
    "ECDSA seam laws",
    """
Prove the ECDSA seam:
- `verifyFunding`, `verifyCommitment`, and `verifyClose` are deterministic
  Bool-valued predicates with distinct domain tags;
- a 64/71-73-byte DER signature representation is accepted only by the
  model's parser predicate;
- verification success is conditional on the `AssumesEufCma` field; do not
  assert unforgeability;
- changing the message, key, or domain tag changes the verification
  statement (state the structural injectivity/inequality you can prove);
- the funding/commitment/close tags are pairwise distinct;
- a signature cannot be reused across domains without the corresponding
  verification predicate.
Anchor to BOLT 2/3 and LDK `lightning/src/ln/chan_utils.rs` and
`lightning/src/util/message_signing.rs`; cite the pinned lines.
""")

B["B07"] = (
    "LnLean/Proofs/Crypto/SchnorrProps.lean",
    "LnLean.Proofs.Crypto.SchnorrProps",
    "LnLean.Crypto.Sig, LnLean.Crypto.Model, LnLean.Basic.Core",
    "Schnorr seam laws",
    """
Prove the BIP 340 seam:
- a Schnorr signature is 64 bytes and an x-only public key is 32 bytes;
- verification is deterministic and conditional on the `AssumesEufCma`
  field;
- key-path and script-path verification use distinct tagged hashes;
- the taproot output key is bound to the internal key and merkle root by
  the model's tweak function;
- changing the taproot merkle root changes the output key commitment
  (structural injectivity under the model's hash assumption);
- no claim of cryptographic unforgeability without the assumption.
Anchor to BOLT 3 taproot and LDK's Schnorr/taproot seam (use
`refs/rust-lightning` and `refs/bolts`; cite exact lines).
""")

B["B08"] = (
    "LnLean/Proofs/Wire/TLVProps.lean",
    "LnLean.Proofs.Wire.TLVProps",
    "LnLean.Wire.BigSize, LnLean.Wire.TLV, LnLean.Wire.Message",
    "BigSize/TLV laws",
    """
Prove the BOLT 1 framing laws:
- `decodeBigSize (encodeBigSize n) = some n` on the model's domain;
- canonical BigSize encodings use the shortest form and respect the
  `<0xfd`, `<=0xffff`, `<=0xffffffff` boundaries;
- encoded length is bounded by 9 bytes and monotone in the value;
- TLV types are unique and strictly increasing in a canonical stream;
- `decodeTLV (encodeTLV xs) = some xs` for canonical sorted unique `xs`;
- the TLV stream length and message frame length are bounded by the
  model's maximum; unframing a framed message round-trips.
Anchor to BOLT 1 (BigSize, TLV, message framing) and LDK
`lightning/src/util/ser.rs` and `lightning/src/ln/msgs.rs`.
""")

B["B09"] = (
    "LnLean/Proofs/Channel/CommitmentTxProps.lean",
    "LnLean.Proofs.Channel.CommitmentTxProps",
    "LnLean.Channel.Commitment, LnLean.Channel.Types, LnLean.Bitcoin.Seam",
    "commitment transaction laws",
    """
Prove the commitment-transaction construction:
- the zero-HTLC commitment has exactly the modelled to_local, to_remote and
  anchor outputs;
- the sum of output values plus the commitment fee equals the funding value
  under the model's hypotheses;
- local and remote commitments are not symmetric (fee owner, CSV delay,
  output ordering); state the exact asymmetry;
- adding an HTLC adds exactly one HTLC output unless it is dust;
- the commitment number is part of the tx construction and changes only on
  a valid state transition;
- output ordering is deterministic.
Anchor to BOLT 3 section 2 and LDK `lightning/src/ln/chan_utils.rs`
(`build_commitment_transaction`).
""")

B["B10"] = (
    "LnLean/Proofs/Channel/StateMachineProps.lean",
    "LnLean.Proofs.Channel.StateMachineProps",
    "LnLean.Channel.State, LnLean.Channel.Types",
    "channel state machine laws",
    """
Prove the channel state machine:
- every `Step` preserves the phase order (negotiating -> awaitingLockin ->
  normal -> shuttingDown -> closed) or stays in the same phase;
- `Reachable` is reflexive-transitive and closed under `Step`;
- commitment numbers never decrease and increment exactly on the modelled
  commitment/revocation events;
- a closed channel has no outgoing step;
- `channel_ready` is unreachable before `funding_signed`;
- the transition relation is deterministic where the model says so, and
  genuinely relational where multiple messages are legal.
Anchor to BOLT 2 sections 2-3 and LDK `lightning/src/ln/channel.rs`.
""")

B["B11"] = (
    "LnLean/Proofs/Channel/FeeProps.lean",
    "LnLean.Proofs.Channel.FeeProps",
    "LnLean.Channel.Fee, LnLean.Channel.Commitment, LnLean.Basic.Core",
    "fee laws",
    """
Prove the fee arithmetic:
- `feeForWeight` is monotone in feerate and weight and non-negative;
- `feeSufficient` is equivalent to the model's `fee >= required` predicate;
- an `updateFee` that passes the sufficiency check never lowers the fee
  below the required amount;
- the commitment fee is exactly the fee computed from its weight and
  feerate;
- dust and reserve checks are preserved by a fee update that passes them;
- fee cannot exceed the funding value under well-formedness.
Anchor to BOLT 2 section 3 and BOLT 3; LDK `lightning/src/ln/chan_utils.rs`
and `lightning/src/ln/channel.rs`.
""")

B["B12"] = (
    "LnLean/Proofs/Channel/ReserveProps.lean",
    "LnLean.Proofs.Channel.ReserveProps",
    "LnLean.Channel.Fee, LnLean.Channel.State, LnLean.Channel.Types",
    "reserve and dust laws",
    """
Prove the reserve/dust rules:
- channel reserve is non-negative and at most the channel capacity;
- a party's balance after any modelled update is at least its reserve;
- an output below the dust limit is not created (or is explicitly recorded
  as dust in the model);
- the maximum HTLC value is at most the channel capacity and at least the
  HTLC minimum;
- the sum of balances plus fees equals the funding value;
- a reserve violation makes the corresponding commitment invalid.
Anchor to BOLT 2 section 2 and LDK `lightning/src/ln/channel.rs`.
""")

B["B13"] = (
    "LnLean/Proofs/Channel/HTLCProps.lean",
    "LnLean.Proofs.Channel.HTLCProps",
    "LnLean.Channel.HTLC, LnLean.Basic.Core",
    "HTLC lifecycle laws",
    """
Prove the HTLC lifecycle:
- `fulfillHTLC` requires a 32-byte preimage whose hash matches the payment
  hash (conditional on the hash assumption);
- `offered -> fulfilled` and `offered -> failed/timeout` are the only
  terminal transitions; fulfilled and failed are mutually exclusive;
- an HTLC amount is within `[htlc_minimum, max_htlc_value]`;
- the CLTV expiry is bounded by the model's maximum and strictly greater
  than the current height for an offered HTLC;
- a dust HTLC has no commitment output but remains in the HTLC set;
- adding then removing an HTLC restores the original set (where the ids are
  distinct).
Anchor to BOLT 2 sections 5.1-5.3 and BOLT 3 section 3; LDK
`lightning/src/ln/channel.rs` and `chan_utils.rs`.
""")

B["B14"] = (
    "LnLean/Proofs/Channel/RevocationProps.lean",
    "LnLean.Proofs.Channel.RevocationProps",
    "LnLean.Channel.Revocation, LnLean.Basic.Core",
    "revocation laws",
    """
Prove the revocation structure:
- a per-commitment secret and point are 32 bytes;
- the commitment seed determines the secret/point through the model's
  derivation function (definitional);
- the revocation key derivation is a function of the secret/point and is
  injective under the model's stated assumption;
- old and current commitment numbers yield different secrets;
- the storage model holds at most 2^48 secrets and never reuses one;
- a revealed old secret marks exactly the corresponding old commitment as
  revoked, not the current one.
Anchor to BOLT 3 section 3 and LDK `lightning/src/ln/chan_utils.rs`
(`derive_Revocation_...`, per-commitment secret storage).
""")

B["B15"] = (
    "LnLean/Proofs/Channel/PenaltyProps.lean",
    "LnLean.Proofs.Channel.PenaltyProps",
    "LnLean.Channel.Penalty, LnLean.Channel.Revocation, LnLean.Bitcoin.Seam",
    "penalty transaction laws",
    """
Prove the penalty transaction:
- a penalty transaction spends both punishable old outputs and pays one
  sweep output;
- `penaltyValid` implies the revocation secret is the one for the breached
  commitment;
- the penalty output value is the input value minus a non-negative fee;
- the penalty transaction is only valid before the breacher's CSV/CLTV
  window closes (state the exact predicate);
- a punished commitment cannot also be spent by the breacher under the
  model's no-double-spend predicate;
- the penalty path does not require the honest party's current commitment
  key.
Anchor to BOLT 5 and LDK `lightning/src/ln/chan_utils.rs` penalty helpers
and `lightning/src/chain/channelmonitor.rs`.
""")

B["B16"] = (
    "LnLean/Proofs/Channel/BreachProps.lean",
    "LnLean.Proofs.Channel.BreachProps",
    "LnLean.Channel.Penalty, LnLean.Channel.HTLC, LnLean.Channel.State",
    "breach and punishment laws",
    """
Prove the breach model:
- `breachDetected` fires exactly when a revoked commitment is confirmed;
- a breach is punishable iff the honest party holds the revocation secret
  and can confirm the penalty transaction within the window;
- if the breach is punished, the breacher's claimed output is unavailable;
- a current (non-revoked) commitment is not punishable by the penalty path;
- the penalty value is at least the breached output value minus the
  penalty fee (state the economic bound as a `Prop` with explicit
  hypotheses);
- no breach is detectable after the revocation window without an
  additional watchtower assumption.
Anchor to BOLT 5 and LDK `lightning/src/chain/channelmonitor.rs`.
""")

B["B17"] = (
    "LnLean/Proofs/Protocol/HandshakeProps.lean",
    "LnLean.Proofs.Protocol.HandshakeProps",
    "LnLean.Protocol.Handshake, LnLean.Protocol.Messages",
    "handshake laws",
    """
Prove the open/accept/funding handshake:
- `accept_channel` is reachable only after `open_channel`;
- `funding_created` precedes `funding_signed`, which precedes
  `channel_ready`;
- the temporary channel id is replaced by the final channel id exactly at
  the funding-created step;
- both parties agree on the funding outpoint before `channel_ready`;
- a `channel_ready` without a prior `funding_signed` is unreachable;
- each handshake message has a unique wire type and a bounded length.
Anchor to BOLT 2 section 2 and LDK `lightning/src/ln/channelmanager.rs` and
`lightning/src/ln/msgs.rs`.
""")

B["B18"] = (
    "LnLean/Proofs/Protocol/ChannelReestablishProps.lean",
    "LnLean.Proofs.Protocol.ChannelReestablishProps",
    "LnLean.Protocol.Peer, LnLean.Channel.State",
    "reestablish laws",
    """
Prove the reestablish model:
- `next_commitment_number` and `next_revocation_number` are monotone across
  a reconnect;
- a reestablish message never moves a channel to an earlier commitment;
- retransmission of a lost commitment_signed/revoke_and_ack preserves the
  channel's commitment number until the peer acknowledges it;
- `channel_ready` is resent after reconnect if it was not acknowledged;
- `data_loss_protect` fields are present exactly when the model says so;
- a reestablish with inconsistent numbers is rejected (state the exact
  predicate; do not hide it behind a Boolean).
Anchor to BOLT 2 section 4 and LDK `lightning/src/ln/channel.rs`
(`channel_reestablish` handling).
""")

B["B19"] = (
    "LnLean/Proofs/Protocol/FeaturesProps.lean",
    "LnLean.Proofs.Protocol.FeaturesProps",
    "LnLean.Protocol.Messages, LnLean.Basic.Core",
    "feature negotiation laws",
    """
Prove the feature-bit model:
- required/optional feature pairs are encoded as adjacent even/odd bits;
- a required feature implies the corresponding optional feature;
- unknown odd features are ignored, unknown even features are rejected
  (state the model's exact rule);
- negotiation is the intersection of the two feature vectors and is
  commutative;
- `option_static_remotekey` and the anchor feature gate the corresponding
  script templates;
- the feature vector is bounded by the wire length.
Anchor to BOLT 9 and LDK `lightning/src/ln/features.rs`.
""")

B["B20"] = (
    "LnLean/Proofs/Protocol/ErrorProps.lean",
    "LnLean.Proofs.Protocol.ErrorProps",
    "LnLean.Protocol.Messages, LnLean.Basic.Core",
    "error/warning laws",
    """
Prove the error handling model:
- an `error` message carries a channel id and a bounded data field;
- a `warning` does not change channel state, while an `error` moves the
  channel to a closed/failed state;
- the error code is one of the model's enumerated codes;
- an error for an unknown channel is not silently applied to another
  channel (channel-id scoping);
- the error data length is bounded by the wire maximum;
- a protocol error cannot be both a warning and a fatal error.
Anchor to BOLT 1 error/warning sections and LDK
`lightning/src/ln/msgs.rs` and `channelmanager.rs`.
""")

B["B21"] = (
    "LnLean/Proofs/Routing/GraphProps.lean",
    "LnLean.Proofs.Routing.GraphProps",
    "LnLean.Routing.Graph",
    "gossip graph laws",
    """
Prove the routing graph:
- `findEdge` returns an edge only if the short_channel_id is present;
- `neighbors` is symmetric on the modelled undirected graph;
- a channel edge has two distinct node ids (no self-loop);
- capacity is positive and fees/CLTV are non-negative;
- a simple path has no repeated node and is non-empty;
- the graph is finite (the model's list/map representation);
- an edge lookup is deterministic.
Anchor to BOLT 7 and LDK `lightning/src/routing/gossip.rs`.
""")

B["B22"] = (
    "LnLean/Proofs/Routing/GossipProps.lean",
    "LnLean.Proofs.Routing.GossipProps",
    "LnLean.Routing.Gossip, LnLean.Routing.Graph",
    "gossip update laws",
    """
Prove the gossip application model:
- `applyGossip` is deterministic and preserves graph well-formedness;
- a channel_update with an older timestamp does not replace a newer one;
- a disabled edge remains in the graph but is not selectable;
- a node announcement cannot change an existing node id;
- a channel announcement binds the short_channel_id to the two node ids;
- signatures are checked by the model's conditional predicate, not
  assumed valid.
Anchor to BOLT 7 and LDK `lightning/src/routing/gossip.rs`.
""")

B["B23"] = (
    "LnLean/Proofs/Routing/OnionProps.lean",
    "LnLean.Proofs.Routing.OnionProps",
    "LnLean.Routing.Onion, LnLean.Basic.Core",
    "onion laws",
    """
Prove the onion structure:
- the number of onion layers equals the number of hops;
- `peel` reduces the layer count by one and preserves the payload shape;
- a final payload is reached exactly at the last hop;
- the onion packet size is bounded by the BOLT 4 maximum;
- HMAC verification is conditional on the model's HMAC assumption;
- an error packet's size is bounded and its origin hop is recorded.
Do NOT claim onion privacy or unlinkability.
Anchor to BOLT 4 and LDK `lightning/src/ln/onion_utils.rs` and
`onion_payment.rs`.
""")

B["B24"] = (
    "LnLean/Proofs/Routing/RouteBlindingProps.lean",
    "LnLean.Proofs.Routing.RouteBlindingProps",
    "LnLean.Routing.Route, LnLean.Routing.Onion",
    "route construction laws",
    """
Prove route construction:
- a route is non-empty and each hop has a distinct short_channel_id;
- the total fee is the sum of hop fees (no hidden fee);
- the total CLTV is the sum of hop CLTV deltas plus the final delta;
- CLTV is strictly increasing along the route;
- the amount at each hop is the final amount plus the downstream fees;
- a blinded route hides the node ids but preserves the same fee/CLTV
  arithmetic (state the exposed fields).
Anchor to BOLT 4 (route blinding) and BOLT 7; LDK
`lightning/src/routing/router.rs` and `blinded_path`.
""")

B["B25"] = (
    "LnLean/Proofs/Payment/InvoiceProps.lean",
    "LnLean.Proofs.Payment.InvoiceProps",
    "LnLean.Payment.Invoice, LnLean.Basic.Core",
    "invoice laws",
    """
Prove the invoice model:
- the payment hash is 32 bytes;
- the amount, when present, is at most `Msat.MAX` and positive;
- expiry is monotone: an invoice valid at time t is valid at any earlier
  time (within the same timestamp domain);
- `amountSatisfies` accepts exactly the modelled amount relation;
- the invoice network and payee are preserved by parsing;
- the signature check is conditional on the crypto assumption; no bech32
  encoding theorem is claimed.
Anchor to BOLT 11 and LDK `lightning-invoice/src/lib.rs`.
""")

B["B26"] = (
    "LnLean/Proofs/Payment/MPPProps.lean",
    "LnLean.Proofs.Payment.MPPProps",
    "LnLean.Payment.MPP, LnLean.Payment.HTLC",
    "multipart payment laws",
    """
Prove the MPP model:
- when `mppComplete` holds, the sum of part amounts equals the target;
- no part exceeds the target amount;
- all parts share the payment hash and payment secret;
- MPP atomicity: either all parts settle or none does (state the exact
  all-or-nothing predicate over the model's part set);
- duplicate parts do not double-count;
- settling an already-settled part is idempotent.
Anchor to BOLT 4/2 and LDK `lightning/src/ln/outbound_payment.rs` and
`inbound_payment.rs`.
""")

B["B27"] = (
    "LnLean/Proofs/Payment/KeysendProps.lean",
    "LnLean.Proofs.Payment.KeysendProps",
    "LnLean.Payment.HTLC, LnLean.Payment.Invoice",
    "keysend laws",
    """
Prove the keysend model:
- a keysend payment has no invoice and carries a preimage chosen by the
  sender;
- the payment hash is `sha256 preimage` under the model's hash function
  (conditional on the hash assumption);
- the amount and CLTV bounds are the same as an invoiced payment;
- the preimage is revealed only on settlement;
- keysend and invoice payments cannot be confused in the payment session
  state;
- a failed keysend does not consume the preimage.
Keysend is not a BOLT; cite the LDK implementation and mark the anchor
`UNANCHORED` if no specification line exists.
""")

B["B28"] = (
    "LnLean/Proofs/Payment/LiquidityProps.lean",
    "LnLean.Proofs.Payment.LiquidityProps",
    "LnLean.Payment.MPP, LnLean.Channel.State",
    "liquidity bounds",
    """
Prove the liquidity model:
- a party's balance is non-negative and at least its reserve;
- the sum of the two balances plus fees equals the channel capacity;
- the inbound/outbound liquidity is the complement of the balance;
- an MPP plan's total amount does not exceed the available outbound
  liquidity;
- no single HTLC exceeds `max_htlc_value`;
- a payment that would violate the reserve is rejected, not silently
  truncated.
Anchor to BOLT 2 and LDK `lightning/src/ln/channel.rs`.
""")

B["B29"] = (
    "LnLean/Proofs/Security/ThreatModelProps.lean",
    "LnLean.Proofs.Security.ThreatModelProps",
    "LnLean.Security.Model, LnLean.Security.Invariants",
    "threat-model laws",
    """
Prove the threat-model structure:
- the adversary's capabilities are exactly the fields of `Adversary`
  (network schedule, corruption, reorg, fee spike);
- `Winning` is a predicate over a `SecurityGame` trace, not an axiom;
- every `Invariant` in the catalog names the assumptions it needs;
- assumption C1-C8 from docs/ASSUMPTIONS.md map to fields of the primitive
  model;
- an invariant that needs a crypto assumption is not claimed
  unconditionally;
- the security game's winning condition is monotone in adversary power
  (a stronger adversary cannot lose a winning position).
Anchor to docs/ASSUMPTIONS.md and the BOLT security considerations; cite
real LDK paths/lines for the implementation-side claims.
""")

B["B30"] = (
    "LnLean/Proofs/Conservation.lean",
    "LnLean.Proofs.Conservation",
    "LnLean.Channel.Commitment, LnLean.Channel.HTLC, LnLean.Bitcoin.Seam, LnLean.Basic.Core",
    "value conservation",
    """
Prove global value conservation:
- for every modelled commitment, sum(outputs) + fee = funding value;
- adding an HTLC preserves the equation (the HTLC output replaces the
  corresponding balance, and dust is handled explicitly);
- fulfilling or failing an HTLC preserves the equation;
- a mutual close preserves the equation with the closing fee;
- a penalty transaction preserves the equation with the penalty fee;
- no step creates value out of nothing (the central LN safety invariant).
Anchor to BOLT 3 and BOLT 5; LDK `lightning/src/ln/chan_utils.rs` and
`channelmonitor.rs`.
""")

B["B31"] = (
    "LnLean/Proofs/Liveness.lean",
    "LnLean.Proofs.Liveness",
    "LnLean.Channel.State, LnLean.Protocol.Peer, LnLean.Basic.Core",
    "liveness under fairness",
    """
State and prove the liveness scaffold:
- under fair message scheduling, a channel in `awaitingLockin` eventually
  reaches `normal` if both parties follow the protocol;
- a pending HTLC eventually resolves (fulfil, fail, or timeout) under
  eventual delivery and honest timers;
- a disconnect/reestablish does not permanently strand a channel;
- a shutdown eventually reaches `closed` if both parties cooperate;
- these are conditional on the fairness/partial-synchrony assumptions;
  state them explicitly, do not assert them as axioms.
Anchor to BOLT 2 sections 2-4 and LDK `lightning/src/ln/channelmanager.rs`.
""")

B["B32"] = (
    "LnLean/Proofs/Traceability.lean",
    "LnLean.Proofs.Traceability",
    "LnLean.Proofs.Obligations",
    "traceability laws",
    """
Prove the traceability catalog's consistency:
- every `Obligation` has a non-empty id, domain, English claim, and anchor;
- obligation ids are unique in the catalog;
- every status is one of the model's enumerated statuses;
- every obligation with a `leanTarget` names a module under `LnLean`;
- the catalog has at least 40 entries and covers at least 8 domains;
- an obligation marked `proved` has a corresponding declaration name
  (this is a structural check over the catalog, not a kernel proof of the
  target);
- the index in docs/THEOREM-INDEX.md and the Lean list agree on ids.
Anchor to the BOLT/LDK rows in `LnLean/Proofs/Obligations.lean` and
`docs/TRACEABILITY.md`.
""")

for name, (path, module, imports, short, body) in B.items():
    text = COMMON.format(
        name=name, path=path, module=module, short=short, body=body.strip()
    )
    text = text.replace("{imports}", imports)
    # Insert the import list after the READ FIRST block, before HARD RULES.
    marker = "HARD RULES\n"
    text = text.replace(marker, f"YOUR WAVE-A IMPORTS\n{imports}\n\n{marker}", 1)
    (OUT / f"{name}.md").write_text(text, encoding="utf-8")
    print(name, len(text))
