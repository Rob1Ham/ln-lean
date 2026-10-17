# Assumptions and Trusted Computing Base

This file is normative. Any theorem whose proof depends on an assumption
below must name that assumption as a hypothesis. An unlisted assumption is a
bug in the formalization, not a convenience.

## 1. Cryptographic assumptions

We model, but do not prove, the following primitives. `LnLean.Crypto.Model`
declares them as an interface structure; concrete instantiations can be
supplied by the L1 model or by an extracted implementation.

| Id | Primitive | Assumed property | Used by |
|---|---|---|---|
| C1 | SHA-256 | collision resistance; preimage resistance | commitments, payment hashes, onion |
| C2 | HASH160 = RIPEMD160(SHA256(x)) | collision resistance | P2WPKH scripts |
| C3 | secp256k1 ECDSA | existential unforgeability under chosen message | funding, mutual close |
| C4 | BIP 340 Schnorr | existential unforgeability under chosen message | taproot channels (future) |
| C5 | ECDH on secp256k1 | computational Diffie-Hellman | onion shared secrets, Noise |
| C6 | HKDF-SHA256 | pseudorandomness | key derivation |
| C7 | ChaCha20-Poly1305 | IND-CCA + integrity | onion layers |
| C8 | HMAC-SHA256 | PRF / unforgeability | onion integrity, gossip auth |

Formal shape (see `LnLean/Crypto/Model.lean`):

```lean
structure PrimitiveModel where
  sha256 : ByteArray → ByteArray
  ecdsaVerify : PubKey → ByteArray → EcdsaSig → Bool
  schnorrVerify : PubKey → ByteArray → SchnorrSig → Bool
  ecdh : ByteArray → PubKey → ByteArray
  hkdf : ByteArray → ByteArray → Nat → ByteArray
  aeadSeal : ByteArray → ByteArray → ByteArray → ByteArray
  aeadOpen : ByteArray → ByteArray → ByteArray → Option ByteArray
  -- assumed properties are Props, not axioms:
  sha256_collisionResistant : Prop
  ecdsa_eufCma : Prop
  schnorr_eufCma : Prop
  aead_cca : Prop
```

A theorem may take `(M : PrimitiveModel)` and hypotheses such as
`M.sha256_collisionResistant`. This keeps the proof conditional and makes
the assumption visible at the point of use.

## 2. Bitcoin L1 assumptions

Lightning does not re-prove Bitcoin consensus. It consumes `btc-lean`'s
model:

* Transaction structure, output values, and `MoneyRange`: `Bitcoin.Data.*`.
* Script semantics at the level needed for funding/commitment outputs:
  `Bitcoin.Data.Script`, `Bitcoin.Interpreter.*` (interface only).
* A funding transaction is confirmable if it pays the expected P2WSH output
  and satisfies L1 consensus. The scaffold does **not** prove confirmation;
  it takes `FundingConfirmed` as a predicate/hypothesis.
* The chain can reorganize. Channel safety theorems must be read relative
  to the chain tip observed by both parties; deep-reorg behaviour is a
  separate obligation (`LN-CHAIN-REORG`).
* Fee estimation and package relay are outside the model. Commitment fee
  is a parameter, and the `feeInsufficient` check is modelled as a
  precondition.

Pinned L1 model: `vendor/btc-lean-core/COMMIT`.

## 3. Network assumptions

* Asynchronous, adversarial message scheduling.
* No reliable delivery, no ordering, no bounded delay by default.
* Messages are authenticated by the Noise transport; the model treats the
  transport as an ideal authenticated channel with a peer identity.
* Liveness theorems may assume *partial synchrony*: after a global
  stabilization time `GST`, every message is delivered within `Δ`. This is
  always an explicit hypothesis.
* The model has at most two participants per channel. Multiparty channels
  are out of scope.

## 4. Economic and policy assumptions

* Both parties are rational enough to broadcast the latest commitment when
  they are online; the model proves *what happens if they do*, not that
  they will.
* Watchtowers are modelled as an optional external service with a
  `Watchtower` interface. A breach is punishable if *some* party has the
  revocation secret and a timely L1 transaction; the scaffold does not
  prove that a watchtower is live.
* Dust limits, minimum channel sizes, and reserve requirements are
  parameters, not constants, except where BOLT 2 fixes them.
* On-chain fee spikes can make a penalty transaction uneconomical. This is
  an explicit liveness assumption (`LN-PENALTY-ECON`), not a safety
  assumption.

## 5. Specification references

* BOLT 1: base protocol, wire framing, BigSize, TLV, Noise.
* BOLT 2: channel establishment, `channel_reestablish`, commitment updates.
* BOLT 3: commitment transaction format, output scripts, weights.
* BOLT 4: onion routing, error packets.
* BOLT 5: recommendations for on-chain transaction fees.
* BOLT 7: gossip, `channel_announcement`, `channel_update`.
* BOLT 11: invoices.
* BOLT 12: offers (out of scope for this scaffold, listed as future work).

Pinned BOLT clone: `refs/bolts/COMMIT`.
Pinned implementation: `refs/rust-lightning/COMMIT`.

## 6. Trusted computing base (TCB)

The Lean kernel and its standard library. `btc-lean`'s L1 definitions.
The eight primitive assumptions C1–C8. Nothing else.

In particular, the following are **not** in the TCB:

* `rust-lightning`: it is a reference for behaviour, never an oracle in a
  proof.
* The differential test runner (future phase): tests provide evidence, not
  proof.
* Agent reports: they are documentation, not evidence. The artifact is the
  Lean tree.

## 7. What "proved" means here

A theorem is *proved* when it is `sorry`-free and its axiom set is a subset
of `{propext, Classical.choice, Quot.sound}` plus the explicitly named
primitive hypotheses. The scaffold phase does not yet enforce the axiom
audit in CI; it does enforce:

* zero `sorry` in model modules;
* every `sorry` in `Proofs/**` has an `-- OBLIGATION:` marker;
* `scripts/check.sh` exits non-zero on `axiom`, `native_decide`, `unsafe`,
  or an unmarked `sorry`.
