# Ownership

Agents may write only the paths assigned to them. Everything else is
read-only. `LnLean.lean`, `lakefile.lean`, `lean-toolchain`, `vendor/`,
`refs/`, and the four normative docs (`CHARTER`, `ARCHITECTURE`,
`ASSUMPTIONS`, `AGENT-PROTOCOL`) are integrator-owned.

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

| Agent | Owns |
|---|---|
| B01 | `LnLean/Bitcoin/FundingProps.lean` |
| B02 | `LnLean/Bitcoin/ScriptProps.lean` |
| B03 | `LnLean/Bitcoin/Anchor.lean` |
| B04 | `LnLean/Bitcoin/Weight.lean` |
| B05 | `LnLean/Crypto/Sha256Props.lean` |
| B06 | `LnLean/Crypto/EcdsaProps.lean` |
| B07 | `LnLean/Crypto/SchnorrProps.lean` |
| B08 | `LnLean/Wire/TLVProps.lean` |
| B09 | `LnLean/Channel/CommitmentTx.lean` |
| B10 | `LnLean/Channel/StateMachine.lean` |
| B11 | `LnLean/Channel/FeeProps.lean` |
| B12 | `LnLean/Channel/Reserve.lean` |
| B13 | `LnLean/Channel/HTLCProps.lean` |
| B14 | `LnLean/Channel/RevocationProps.lean` |
| B15 | `LnLean/Channel/PenaltyProps.lean` |
| B16 | `LnLean/Channel/Breach.lean` |
| B17 | `LnLean/Protocol/HandshakeProps.lean` |
| B18 | `LnLean/Protocol/ChannelReestablish.lean` |
| B19 | `LnLean/Protocol/Features.lean` |
| B20 | `LnLean/Protocol/ErrorProps.lean` |
| B21 | `LnLean/Routing/GraphProps.lean` |
| B22 | `LnLean/Routing/GossipProps.lean` |
| B23 | `LnLean/Routing/OnionProps.lean` |
| B24 | `LnLean/Routing/RouteBlinding.lean` |
| B25 | `LnLean/Payment/InvoiceProps.lean` |
| B26 | `LnLean/Payment/MPPProps.lean` |
| B27 | `LnLean/Payment/Keysend.lean` |
| B28 | `LnLean/Payment/Liquidity.lean` |
| B29 | `LnLean/Security/ThreatModel.lean` |
| B30 | `LnLean/Proofs/Conservation.lean` |
| B31 | `LnLean/Proofs/Liveness.lean` |
| B32 | `LnLean/Proofs/Traceability.lean` |
