# Ownership

Agents may write only the paths assigned to them. Everything else is
read-only. `LnLean.lean`, `lakefile.lean`, `lean-toolchain`, `vendor/`,
`refs/`, and the four normative docs (`CHARTER`, `ARCHITECTURE`,
`ASSUMPTIONS`, `AGENT-PROTOCOL`) are integrator-owned.

The L1 snapshot in `vendor/btc-lean-core` is **read-only**. It is a copy of
the Bitcoin model, not a place to add Lightning definitions.

## Wave A — 8 scaffolding agents

| Agent | Owns | Mission |
|---|---|---|
| A1 | `LnLean/Bitcoin/{Funding,ScriptTemplates,Laws}.lean`, `docs/SCOPE.md` | L1 seam: funding output, commitment script templates, anchor/weight laws |
| A2 | `LnLean/Crypto/{Model,Hash,Sig,Noise}.lean`, `LnLean/Wire/{BigSize,TLV,Message}.lean` | primitive interface + BOLT 1 framing |
| A3 | `LnLean/Channel/{Types,State,Commitment,Fee,Laws}.lean` | channel state machine and commitment arithmetic |
| A4 | `LnLean/Channel/{HTLC,Revocation,Penalty,HTLCLaws}.lean` | HTLC lifecycle, revocation, penalty |
| A5 | `LnLean/Protocol/{Handshake,Peer,Messages,Laws}.lean` | BOLT 1/2 peer protocol |
| A6 | `LnLean/Routing/{Graph,Gossip,Onion,Route,Laws}.lean` | BOLT 4/7 routing and onion |
| A7 | `LnLean/Payment/{Invoice,HTLC,MPP,Laws}.lean` | BOLT 11 payments and MPP |
| A8 | `LnLean/Security/{Model,Invariants}.lean`, `LnLean/Proofs/Obligations.lean`, `docs/{THEOREM-INDEX,TRACEABILITY,ROADMAP}.md` | threat model, obligation catalog, traceability |

## Wave B — 32 proof-scaffold agents

All Wave B files live under `LnLean/Proofs/`. This keeps the invariant that
`sorry` is legal only in `LnLean/Proofs/**`, where every use carries an
`-- OBLIGATION: LN-...` marker.

| Agent | Owns | Proof target |
|---|---|---|
| B01 | `LnLean/Proofs/Bitcoin/FundingProps.lean` | funding output, 2-of-2, confirmation seam |
| B02 | `LnLean/Proofs/Bitcoin/ScriptProps.lean` | commitment script templates |
| B03 | `LnLean/Proofs/Bitcoin/AnchorProps.lean` | anchor outputs and fee ownership |
| B04 | `LnLean/Proofs/Bitcoin/WeightProps.lean` | commitment/HTLC weight formulas |
| B05 | `LnLean/Proofs/Crypto/Sha256Props.lean` | hash model laws |
| B06 | `LnLean/Proofs/Crypto/EcdsaProps.lean` | ECDSA verification seam |
| B07 | `LnLean/Proofs/Crypto/SchnorrProps.lean` | BIP 340 verification seam |
| B08 | `LnLean/Proofs/Wire/TLVProps.lean` | BigSize/TLV round-trip and canonical form |
| B09 | `LnLean/Proofs/Channel/CommitmentTxProps.lean` | commitment transaction construction |
| B10 | `LnLean/Proofs/Channel/StateMachineProps.lean` | legal transitions, reachability |
| B11 | `LnLean/Proofs/Channel/FeeProps.lean` | fee computation and monotonicity |
| B12 | `LnLean/Proofs/Channel/ReserveProps.lean` | reserve and dust limits |
| B13 | `LnLean/Proofs/Channel/HTLCProps.lean` | HTLC add/fulfil/fail/timeout |
| B14 | `LnLean/Proofs/Channel/RevocationProps.lean` | per-commitment secrets |
| B15 | `LnLean/Proofs/Channel/PenaltyProps.lean` | penalty transaction |
| B16 | `LnLean/Proofs/Channel/BreachProps.lean` | old-state breach and punishment |
| B17 | `LnLean/Proofs/Protocol/HandshakeProps.lean` | open/accept/funding_signed flow |
| B18 | `LnLean/Proofs/Protocol/ChannelReestablishProps.lean` | reestablish and retransmission |
| B19 | `LnLean/Proofs/Protocol/FeaturesProps.lean` | feature-bit negotiation |
| B20 | `LnLean/Proofs/Protocol/ErrorProps.lean` | error/warning handling |
| B21 | `LnLean/Proofs/Routing/GraphProps.lean` | gossip graph invariants |
| B22 | `LnLean/Proofs/Routing/GossipProps.lean` | channel_update application |
| B23 | `LnLean/Proofs/Routing/OnionProps.lean` | onion layer/peel laws |
| B24 | `LnLean/Proofs/Routing/RouteBlindingProps.lean` | route blinding and CLTV |
| B25 | `LnLean/Proofs/Payment/InvoiceProps.lean` | BOLT 11 invoice parsing |
| B26 | `LnLean/Proofs/Payment/MPPProps.lean` | multipart payment sum |
| B27 | `LnLean/Proofs/Payment/KeysendProps.lean` | keysend/preimage handling |
| B28 | `LnLean/Proofs/Payment/LiquidityProps.lean` | balance/liquidity bounds |
| B29 | `LnLean/Proofs/Security/ThreatModelProps.lean` | adversary capabilities |
| B30 | `LnLean/Proofs/Conservation.lean` | global value conservation |
| B31 | `LnLean/Proofs/Liveness.lean` | liveness under fair scheduling |
| B32 | `LnLean/Proofs/Traceability.lean` | obligation → anchor index |
