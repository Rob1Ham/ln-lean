# Scope

## In scope

| Area | Model | Primary obligations |
|---|---|---|
| Amounts | msat/sat, fees, reserves | no unit confusion; conservation |
| Wire | BigSize, TLV, message framing | bounds, round-trip, unique/sorted TLV |
| Crypto seam | hash, ECDSA, Schnorr, ECDH, AEAD | conditional on named assumptions |
| Channel lifecycle | open, lock-in, normal, shutdown, close | state reachability, no invalid transition |
| Commitments | local/remote commitment tx | value conservation, fee correctness |
| HTLCs | add, fulfill, fail, timeout | preimage soundness, timeout safety |
| Revocation | per-commitment secrets, penalty | old state punishable; no double-spend |
| Protocol | handshake, reestablish, features | message validity, resend safety |
| Routing | gossip graph, route construction | route well-formedness, fee/CLTV monotonicity |
| Onion | layered packet, peel | layer bound, integrity conditional on HMAC |
| Payments | invoices, MPP, keysend | hash/amount consistency, MPP sum |
| Security | threat model, invariant catalog | explicit assumptions, no hidden axioms |

## Out of scope for the scaffold

* Bit-exact BOLT serialization and differential conformance (future phase C).
* Splicing, dual funding, channel factories, eltoo, Taproot-native channels.
* BOLT 12 offers and blinded paths beyond a stub interface.
* Watchtower implementation and economics.
* Bitcoin P2P, mempool policy, package relay, fee estimation.
* Proving the cryptographic primitives themselves.
* A verified implementation extracted to Rust.

## Boundary with `btc-lean`

`btc-lean` owns Bitcoin transaction structure, script parsing/execution,
sighash, and L1 consensus. `ln-lean` owns everything above the funding
output: channel construction, off-chain updates, HTLC semantics, revocation,
routing, and payment flow. The seam is `LnLean.Bitcoin.Seam`; it aliases L1
types and constructs the Lightning-specific scripts, but does not redefine
L1 semantics.
