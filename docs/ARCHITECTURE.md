# Architecture

## 1. Package layout

```
ln-lean/
  lakefile.lean                  package «lnlean», requires «core»
  lean-toolchain                 leanprover/lean4:v4.35.0
  LnLean.lean                    integrator-owned root (regenerated)
  LnLean/
    Basic/Core.lean              amounts, ids, direction, errors, result
    Bitcoin/Seam.lean            L1 aliases, funding/commitment scripts
    Crypto/                      hash, signatures, noise, primitive model
    Wire/                        BigSize, TLV, message framing
    Channel/                     state machine, commitments, HTLC, penalty
    Protocol/                    handshake, peer, feature bits, errors
    Routing/                     graph, gossip, route construction, onion
    Payment/                     invoices, MPP, keysend, liquidity
    Security/                    threat model, invariant catalog
    Proofs/                      theorem statements / obligation modules
  docs/                          charter, architecture, assumptions, indices
  agents/                        ownership, briefs, reports
  refs/rust-lightning/           pinned reference clone (not built)
  refs/bolts/                    BOLT markdown (reference)
  vendor/btc-lean-core/          L1 model (path dependency)
  scripts/                       build, commit, root regeneration
```

## 2. Module dependency rules

* `Basic.Core` imports only `Bitcoin.Data.Basic`.
* `Bitcoin.Seam` imports `Basic.Core` and `Bitcoin.Data.{Basic,Script,Tx}`.
* Wave-A domain modules import **only** `Basic.Core` and `Bitcoin.Seam`.
  This keeps the eight wave-A builds independent.
* Wave-B modules may additionally import wave-A modules in their own
  domain, and `LnLean.Crypto.Model` for primitive assumptions.
* `Proofs.*` may import anything below it. It must not be imported by a
  model module.
* No cycles. No module imports `LnLean.lean`.

## 3. Domain map

| Domain | Wave-A module(s) | Wave-B modules |
|---|---|---|
| Foundations / L1 | `Basic/Core`, `Bitcoin/Seam` | `Basic/{Sats,Msat}`, `Bitcoin/{Funding,ScriptTemplates}` |
| Crypto / wire | `Crypto/Model`, `Crypto/{Hash,Sig,Noise}`, `Wire/{BigSize,TLV,Message}` | `Crypto/{Sha256,Ecdsa,Schnorr}`, `Wire/{TLV,BigSize}Props` |
| Channel / commitment | `Channel/{Types,State,Commitment,Fee}` | `Channel/{CommitmentTx,StateMachine,Fee,Reserve}` |
| HTLC / revocation | `Channel/{HTLC,Revocation,Penalty}` | `Channel/{HTLCLifecycle,Revocation,Penalty,Breach}` |
| Protocol / peer | `Protocol/{Handshake,Peer,Messages}` | `Protocol/{Handshake,ChannelReestablish,Features,Errors}` |
| Routing / onion | `Routing/{Graph,Gossip,Onion,Sphinx}` | `Routing/{Graph,Gossip,Onion,RouteBlinding}` |
| Payments | `Payment/{Invoice,HTLC,MPP}` | `Payment/{Invoice,MPP,Keysend,Liquidity}` |
| Security / proofs | `Security/{Model,Invariants}`, `Proofs/Obligations` | `Security/Invariants`, `Proofs/{Conservation,Liveness,Traceability}` |

## 4. Core modelling decisions

### 4.1 Amounts

`Msat` is a `Nat` wrapper; `FeeRate` is msat per 1000 weight units. L1
amounts are `Bitcoin.Data.Amount = Int` satoshis, re-exported as
`LnLean.Bitcoin.BtcAmount`. All conversions are explicit and have floor/ceil
variants.

### 4.2 Channel state

A channel is a record of two endpoints, a funding outpoint, a current
commitment number, two commitment balances, a list of HTLCs, and a phase.
The transition relation is a *relation*, not a function: several messages
can be valid in one state, and invalid transitions must be provably
unreachable rather than silently rejected.

### 4.3 Commitments

`Commitment` records the two `to_local`/`to_remote` values and the HTLC
outputs. The model distinguishes *local* and *remote* commitment
transactions because they are not symmetric (fee ownership, CSV delays,
HTLC ordering). Value conservation is stated per commitment:

```
sum(outputs) + fee = funding_value
```

### 4.4 HTLCs

An HTLC carries direction, amount, payment hash, CLTV expiry, and state.
The two central safety statements are:

* **Preimage soundness:** a fulfilled HTLC reveals a preimage whose hash is
  the payment hash.
* **Timeout safety:** an offered HTLC can be failed on-chain only after its
  CLTV expiry (and the corresponding CSV conditions for the commitment).

### 4.5 Revocation

Each commitment has a per-commitment point and secret. Publishing an old
commitment is punished by a revocation transaction that spends both
outputs. The model states punishment as a predicate over the old
commitment's secrets and the current state, not as a concrete script
execution.

### 4.6 Onion

The onion model is layered: a packet is a list of encrypted hops with an
HMAC per layer. `peel` returns either the next packet or a terminal
payload. Integrity is conditional on the HMAC assumption; length and
layer-count bounds are proved structurally.

### 4.7 Wire

`BigSize` is the BOLT 1 variable-length integer. TLV streams are sorted by
type with unique types. Message framing uses a 2-byte type and a 2-byte
length (extended by `option_support_large_channel` where modelled).

## 5. Reference pinning

* `refs/rust-lightning` is cloned at the commit recorded in
  `refs/rust-lightning/COMMIT`. Key files:
  `lightning/src/ln/channel.rs`, `channelmanager.rs`, `chan_utils.rs`,
  `onion_payment.rs`, `routing/gossip.rs`, `lightning-invoice/src/lib.rs`,
  `lightning-types/src/lib.rs`.
* `refs/bolts` is cloned at the commit recorded in `refs/bolts/COMMIT`.
* `vendor/btc-lean-core` is copied from the local `btc-lean/spec/core` at
  the commit recorded in `vendor/btc-lean-core/COMMIT`.

Agents must cite `path:line` for any behavioural claim taken from these
references. A missing citation is treated as an unproven claim.

## 6. Build and integration

```
export PATH=/dev/shm/btc/elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
cd /home/ubuntu/ln-lean
flock -w 900 /tmp/ln-build.lock lake build LnLean.Channel.Commitment
```

The integrator regenerates `LnLean.lean` with `scripts/regen-root.sh` after
each wave, then runs a whole-library build. A wave is accepted only when:

1. every owned module builds;
2. `scripts/check.sh` reports zero model `sorry`s and zero forbidden
   constructs;
3. every report exists and matches the tree.
