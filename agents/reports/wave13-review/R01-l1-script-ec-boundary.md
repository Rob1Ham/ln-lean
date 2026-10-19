# R01 — L1 script, interpreter, and EC-verifier boundary

**Status:** read-only review
**Pins:** LDK Node `fa123fed131e27ecc420b77fa7086fcf1ddaebb8`, LDK Server `c17dc11dde38f88c53457039ddf30c6b90a63ba2`
**Scope:** catalog rows `LN-L1-001` / `LN-L1-004` and open issues `L1-01`, `L1-02`, `L1-07`. This report scopes work; it does not implement it.

## 1. Scope and current Lean surface

The three issues are coupled but not identical. `L1-01` is the funding P2WSH/2-of-2
path and its EC/domain seam. `L1-02` is the `to_local` delayed/revocation spend
with CSV/BIP 68/112 and a known spent amount. `L1-07` is the interpreter
integration claim that covers those branches. The catalog already states the
central qualification:

* `LN-L1-001` says the positive interpreter path is conditional, the concrete
  `VendorEcdsaBridge` is total-rejecting under C3, and the canonical domain is
  an abstract 33-byte/32-byte interface, not the real `fundingTag ++ tx` bytes
  (`docs/THEOREM-INDEX.md:37`, scope note at `:135`).
* `LN-L1-004` says the containment and known-amount pipeline transfers are
  complete, while concrete EC, key separation, and spent context remain
  hypotheses (`docs/THEOREM-INDEX.md:40`, `:137`).
* `L1-01`, `L1-02`, and `L1-07` are listed as blocked in
  `docs/OPEN-ISSUES.md:47`, `:48`, and `:53`; the EC obstruction is stated
  explicitly and `L1-02` says no `TxValidation.Full` transfer gap remains.

The current Lean surface is:

1. **Script/interpreter model.**
   `P2WSHSpend` is an explicit model predicate (`LnLean/Proofs/Bitcoin/SpendTargets.lean:276`).
   `ConsensusSpendBridge` is an explicit `Prop`, not a proved instance
   (`SpendTargets.lean:635`). The model truthiness limitation is preserved as
   `truthy_nonminimal_true` (`SpendTargets.lean:716`).
   Positive-direction agreement with the vendored interpreter is
   `funding_interpreters_agree` (`InterpreterBridgeTargets.lean:756`) and
   `toLocal_delayed_interpreters_agree` (`InterpreterBridgeTargets.lean:948`);
   the revocation branch is `toLocal_revocation_interpreters_agree`
   (`InterpreterRevocationTargets.lean:259`). These are relative agreements, not
   consensus spendability.

2. **BIP 143 digest and amount context.**
   `sighashDispatch` and `checkerOf` wire the model digest into the vendored
   ECDSA entry (`SighashBridgeTargets.lean:132`, `:147`).
   `checker_consumes_model_digest` identifies the exact verifier call
   (`SighashBridgeTargets.lean:176`). `funding_sighash_interpreters_agree`
   (`:220`) and `toLocal_sighash_interpreters_agree` (`:280`) take `tx`, `nIn`,
   and `amount` as explicit parameters. `digest_commits_amount`
   (`:342`) proves only that the amount is a preimage field, not that it equals
   the referenced outpoint's value.

3. **Transaction-pipeline transfer.**
   For a known amount, `txCheckerFor_some_eq_realCheckerOf` is exact
   (`TxValidTransferTargets.lean:140`). Missing amount is fail-closed
   (`:213`). The delayed branch is refined against the pipeline checker at
   `:302`, with the real-checker version at
   `SequenceContextTargets.lean:600`. `txVerdictFull_accept_realChecker`
   transfers full-pipeline acceptance to `realCheckerOf` for every input whose
   resolved prevout has a known amount (`TxValidTransferTargets.lean:1096`).

4. **Concrete EC seam.**
   `vendorVerify` and `VendorEcdsaBridge` are defined at
   `EcdsaBridgeTargets.lean:113` and `:124`; `verifyImpl_eq_model` is the
   argument-order transfer at `:133`; `fundingSignedValid_iff_vendor` is at
   `:295`. The concrete obstruction is:

   * `verifyImpl_zeroPad : verifyImpl sig pk (zeroPad msg) = verifyImpl sig pk msg`
     (`EcdsaConcreteTargets.lean:126`);
   * `eufCma_vendorVerify_iff_totalReject`
     (`EcdsaConcreteTargets.lean:163`);
   * `bridged_model_totalReject` (`:231`), `no_bridged_nontrivial_model`
     (`:252`), and `exists_bridged_model_iff_totalReject` (`:265`);
   * `withVendorEcdsa_no_funding` (`:303`) shows the wave-8 concrete model has
     no accepted funding signature.

   The strongest faithful contract is `ResidueBinding ∧ KeyBinding`
   (`EcdsaConcreteTargets.lean:367`, `:396`), not byte-level `EufCma`.
   `DigestBindsMod` is defined at `:564`; it is false for the funding tag
   (`:616`) and for every tag (`EcdsaDomainTargets.lean:281`, `:288`), even at
   fixed 33-byte length (`:301`). The canonical repair is
   `CanonicalOfSize` / `Canonical33` / `CanonicalDigest32`
   (`EcdsaDomainTargets.lean:352`, `:428`, `:434`), with
   `digestBindsModOn_canonical32` at `:438`,
   `residueBinding_vendor_funding_eq_of_canonical33` at `:453`, and
   `digest_domain_dichotomy` at `:478`.

The important scope consequence is already mechanized: there is no non-vacuous
`VendorEcdsaBridge` at the current untyped `ByteArray` interface. The current
`verifyFunding` adds a compact stand-in tag (`LnLean/Crypto/Sig.lean:24-28`,
`:42`, `:76`), which is not the real BOLT/BIP 143 encoding. The model's
`PrimitiveModel.ecdsa_eufCma` field (`LnLean/Crypto/Model.lean:118`) is what
turns the bridge into total rejection.

## 2. LDK datapoints (with `file:line`)

### 2.1 Channel-funding construction gives script/value context, not a script verifier

`FundingGenerationReady` carries `channel_value_satoshis` and an opaque
`output_script` (`/tmp/opencode/ldk-refs/ldk-node/src/event.rs:806-836`). The
handler converts the value to `Amount` and calls
`create_funding_transaction(output_script.clone(), channel_amount, ...)`
(`event.rs:825-836`). That function adds the recipient with the exact script and
amount, builds a BDK PSBT, signs it, and extracts the transaction
(`/tmp/opencode/ldk-refs/ldk-node/src/wallet/mod.rs:1704-1750`). The event
handler then locates the funding output by matching both script and value
(`event.rs:845-852`).

This is a concrete `(script, value, vout)` construction boundary, but it is not
a concrete `verifyWitnessProgram` or a 2-of-2 spend. The wallet's descriptor is
BIP84 (`/tmp/opencode/ldk-refs/ldk-node/src/builder.rs:1761-1762`), so the
wallet-owned inputs being signed are P2WPKH, not the BOLT 3 funding P2WSH. The
node does not interpret `output_script` as `OP_2 <pk1> <pk2> OP_2
OP_CHECKMULTISIG`; it trusts LDK's script bytes and only enforces the output
pairing. The 2-of-2 output is spent later through LDK's channel/sweeper paths,
not through this wallet transaction-builder path.

### 2.2 On-chain send checks address/amount, signs owned UTXOs, and delegates acceptance

`parse_and_validate_address` re-parses the address and calls
`require_network(self.config.network)`
(`wallet/mod.rs:2162-2167`). `send_to_address` starts by validating the
address, then builds either an exact-amount recipient or an all-funds drain
(`wallet/mod.rs:2170-2191`). It signs with `locked_wallet.sign`, extracts the
transaction, and calls `self.broadcaster.broadcast(tx)`
(`wallet/mod.rs:2291-2316`).

`sign_owned_inputs` constructs a PSBT and only fills inputs whose
`previous_output` is in `locked_wallet.list_output()` (`wallet/mod.rs:2545-2562`).
It sets `trust_witness_utxo = true` (`:2564-2565`). `sign_psbt_inner` does the
same (`:2586-2593`). The comment explains that LDK does not populate
`non_witness_utxo`, so BDK must trust the witness UTXO (`:2589-2593`). That is
an operational UTXO/amount context, but it is not exported as a verified table
and it is not a local script check.

The actual chain acceptance is delegated: the bitcoind backend serializes the
transaction and calls `sendrawtransaction`
(`/tmp/opencode/ldk-refs/ldk-node/src/chain/bitcoind.rs:924-930`). The
broadcaster is a queue/package layer, not a script interpreter
(`/tmp/opencode/ldk-refs/ldk-node/src/tx_broadcaster.rs:20-35`). A search of
`ldk-node/src` and `ldk-server/ldk-server/src` for `verify_script`,
`verifyScript`, or a local script-validation call found no such verifier; the
only script-related error is `InvalidScriptPubKey`
(`ldk-node/src/error.rs:124`). This supports the conclusion that LDK Node is
not a concrete L1 consensus/script verifier.

### 2.3 Channel-output sweeps are delegated to `OutputSweeper`

`SpendableOutputs` is handled by
`self.output_sweeper.track_spendable_outputs(outputs, ...)`
(`/tmp/opencode/ldk-refs/ldk-node/src/event.rs:1682-1691`). The wallet is not
the signer of the `to_local`/revocation path. The event path does not expose a
per-input amount table or a script-checker result that the Lean model could
consume. Thus `to_local` execution in the model is not mirrored by the LDK Node
on-chain wallet, even though LDK itself has the real sweep logic internally.

### 2.4 `sign_message`/`verify_signature` are message-signing APIs, not a BIP 143 verifier

`WalletKeysManager::sign_message` and `verify_signature` delegate to
`lightning::util::message_signing` with the node secret key
(`/tmp/opencode/ldk-refs/ldk-node/src/wallet/mod.rs:4013-4023`; public wrappers at
`ldk-node/src/lib.rs:2535-2542`). LDK Server exposes the same operations through
`handle_sign_message_request` (`ldk-server/src/api/sign_message.rs:17-23`) and
`handle_verify_signature_request`
(`ldk-server/src/api/verify_signature.rs:20-30`). The latter parses a public key
and returns a Boolean for an arbitrary message; it does not take a script, a
BIP 143 preimage, or a spent amount. It therefore cannot instantiate
`Bitcoin.Crypto.Ecdsa.Verify.verifyImpl` for the funding/`to_local` digest
seam.

### 2.5 LDK Server adds input validation, not script verification

The on-chain send handler parses the address, requires the configured network,
parses the fee rate, requires an exact amount or all funds, and calls
`send_to_address`/`send_all_to_address`
(`/tmp/opencode/ldk-refs/ldk-server/ldk-server/src/api/onchain_send.rs:25-43`).
`require_amount` and `parse_fee_rate` reject missing/zero/invalid amounts
(`ldk-server/src/api/mod.rs:67-84`). `onchain_receive` only returns a fresh
wallet address (`onchain_receive.rs:17-23`). `onchain_bump_fee` only parses a
payment id/fee rate and calls RBF (`onchain_bump_fee.rs:18-24`). None of these
paths supplies a concrete ECDSA verifier, a spent-outpoint table, or a
`verifyWitnessProgram` result.

### 2.6 What LDK does **not** give the Lean lane

The pinned paths give useful **operational context**:

* exact output script/value construction for channel funding;
* wallet-owned UTXO selection and address/network validation for on-chain
  sends;
* a concrete message-signing API;
* delegation of transaction acceptance to bitcoind/`sendrawtransaction`.

They do **not** give:

* a concrete secp256k1 verifier at the BIP 143 digest interface;
* a proof that the `amount` parameter equals the referenced prevout's value;
* a concrete `to_local`/funding P2WSH verifier exposed by the wallet;
* the negative direction of `ConsensusSpendBridge`;
* the real BOLT/BIP 143 funding-signature encoding.

## 3. Gap matrix

| Behavior | Lean status | LDK evidence | Gap / counterexample | Priority |
|---|---|---|---|---|
| Funding output is exactly the channel script and value | **Partially covered.** `FundingScriptTargets.fundingScriptPubKey_eq_p2wsh_twoOfTwo` (`:265`) and `FundingConfirmed` (`LnLean/Bitcoin/Funding.lean:395-399`) are conditional on a matching `TxOut`. | `event.rs:806-852`; `wallet/mod.rs:1704-1750` | No Lean theorem links a concrete LDK-built transaction to `FundingConfirmed`; the wallet only matches script/value and does not interpret 2-of-2 semantics. | P1 |
| Funding 2-of-2 witness executes through the vendored interpreter | **Partially covered.** `funding_interpreters_agree` (`InterpreterBridgeTargets.lean:756`) is positive-direction under two ECDSA checks and size hypotheses. | LDK wallet descriptor is BIP84 (`builder.rs:1761-1762`); funding output is not a wallet-owned descriptor output. | No concrete EC verifier; no negative direction; the wallet path never spends the 2-of-2 output. | P0 |
| BIP 143 funding digest and spent amount are wired to ECDSA | **Partially covered.** `funding_sighash_interpreters_agree` (`SighashBridgeTargets.lean:220`) builds `sighashWitnessV0` from `tx`, `nIn`, `scriptCode`, and `amount`. | LDK exposes no raw `(sig,pk,digest) -> Bool` API; `sign_message` is generic (`wallet/mod.rs:4013-4023`). | `verify` is an explicit parameter; `digest_commits_amount` (`SighashBridgeTargets.lean:342`) does not prove amount provenance. | P0 |
| Funding signature binds the actual transaction bytes | **Contradicted as a closure claim.** `not_digestBindsMod_fundingTag` (`EcdsaConcreteTargets.lean:616`), `not_digestBindsMod_any_tag` (`EcdsaDomainTargets.lean:281`), `no_digestBindsMod_anywhere` (`:288`), `not_digestBindsModOn33_any_tag` (`:301`). | No LDK-side domain encoding is exposed; `fundingTag` is a compact stand-in (`LnLean/Crypto/Sig.lean:42`, `:76`). | `verifyImpl_zeroPad` plus `eufCma_vendorVerify_iff_totalReject` force total rejection at this interface; fixed length alone does not repair it. | P0 |
| `to_local` delayed branch through the vendored interpreter | **Partially covered.** `toLocal_delayed_interpreters_agree` (`InterpreterBridgeTargets.lean:948`); pipeline refinement `toLocal_delayed_txCheckerFor_refinement` (`TxValidTransferTargets.lean:302`). | `SpendableOutputs` delegates to `OutputSweeper` (`event.rs:1682-1691`), not the wallet. | Actual delay/amount/outpoint context is external; positive direction only. | P0 |
| `to_local` revocation branch | **Partially covered.** `toLocal_revocation_interpreters_agree` (`InterpreterRevocationTargets.lean:259`); pipeline version at `TxValidTransferTargets.lean:407`. | Same `OutputSweeper` delegation; no exposed amount/script checker. | Concrete EC and actual context remain; negative direction not claimed. | P1 |
| Known spent amount yields the real checker | **Covered faithfully at the checker level.** `txCheckerFor_some_eq_realCheckerOf` (`TxValidTransferTargets.lean:140`) is unconditional for a supplied amount; `txVerdictFull_accept_realChecker` (`:1096`) transfers full-pipeline acceptance. | Wallet uses owned UTXOs and trusts witness UTXO (`wallet/mod.rs:2545-2593`); amount table is not exported. | The theorem is exact, but `amount` is an input, not a verified chain fact. Do not call this end-to-end consensus spendability. | P0 |
| Missing amount is rejected | **Covered faithfully.** `txCheckerFor_none_ecdsa_witnessV0_false` (`:213`), `txCheckerFor_none_delayed_not_ok` (`:232`), `txCheckerFor_none_revocation_fail` (`:266`). | Server requires an exact/all-funds amount (`onchain_send.rs:35-43`; `mod.rs:67-74`). | The fail-closed boundary is model-level; LDK's operational amount presence is not a proof of value correctness. | P1 |
| Actual spent outpoint and amount are linked to the transaction | **Missing / external.** No Lean theorem equates the `amount` argument with the referenced prevout. | `sign_owned_inputs` maps only wallet-owned outpoints (`wallet/mod.rs:2545-2562`); `trust_witness_utxo = true` (`:2564-2565`, `:2586-2593`). | No exported UTXO table/proof; the signer trusts the witness UTXO. This is the largest non-EC context gap. | P0 |
| Concrete secp256k1 verifier | **Missing / external.** `VendorEcdsaBridge` is an explicit hypothesis (`EcdsaBridgeTargets.lean:124`); `no_bridged_nontrivial_model` (`EcdsaConcreteTargets.lean:252`). | Only generic message signing is exposed (`wallet/mod.rs:4013-4023`; server `sign_message.rs:17-23`, `verify_signature.rs:20-30`). | No concrete non-vacuous bridge at `ByteArray`; C3 forces total rejection. | P0 |
| Address/network/amount validation | **Unmodelled / external for L1.** No L1 address model in the current surface. | `wallet/mod.rs:2162-2167`; server `onchain_send.rs:25-43`; `mod.rs:76-84`. | Useful precondition, not a substitute for script/EC verification. | P2 |
| Model truthiness matches Core | **Contradicted.** `truthy_nonminimal_true : truthy (ByteArray.mk #[0x00]) = true` (`SpendTargets.lean:716`). | No LDK path changes the model's truthiness. | Core's `cast_to_bool` rejects `#[0x00]`; this is why no theorem here may be read as consensus validation. | P1 |
| Negative direction of `ConsensusSpendBridge` | **Missing.** `ConsensusSpendBridge` is only a `Prop` (`SpendTargets.lean:635`); no instance is proved. | `sendrawtransaction` delegates acceptance (`chain/bitcoind.rs:924-930`). | Positive-direction agreements do not imply the `↔`; all branches and a concrete EC verifier would be needed. | P0 |
| P2SH/P2WSH flags, DERSIG, policy edges | **Partially covered / external.** Default flags and positive P2WSH only; `minimalData`/CSV edges are mechanized in `TxValidTransferTargets`. | LDK wallet path uses standard transaction construction, not a script-flag harness. | No concrete consensus-flag refinement; `P2SH`-wrapped witnesses and negative policy paths remain outside. | P2 |

## 4. Proposed targets

The targets below are **proposals**. They are deliberately split between
model-level assembly, a typed-digest model extension, and an external
assumption. None of them is an implementation of the current unresolved claim.

### T1 — `LnLean.Proofs.Bitcoin.SpentContextTargets.SpentOutputContext` (P1, model extension, feasible)

**Statement shape.**

```lean
structure SpentOutputContext (tx : Bitcoin.Data.Tx) (nIn : Nat) where
  outpoint : Bitcoin.Data.OutPoint
  value : Amount
  scriptPubKey : ByteArray
  hIn : nIn < tx.vin.length
  hPrev : (tx.vin.getD nIn Bitcoin.Capstone.RealChecker.dummyTxIn).prevout = outpoint

theorem spentOutputContext_checker_eq_realChecker
    {tx : Bitcoin.Data.Tx} {nIn : Nat}
    (ctx : SpentOutputContext tx nIn) :
    Bitcoin.TxValidation.Full.txCheckerFor tx nIn (some ctx.value) =
      Bitcoin.Capstone.RealChecker.realCheckerOf tx nIn ctx.value
```

A second projection should state
`(sighashWitnessV0 tx nIn scriptCode ht ctx.value).amount = ctx.value`, reusing
`digest_commits_amount`.

**Hypotheses.** The context record itself, `nIn < tx.vin.length`, and the prevout
equality. No new cryptographic law.

**Non-vacuity witness.** A one-input concrete transaction and a one-entry
prevout table in the style of `LnLean/Proofs/WaveH/H04.lean` (`oneInputTx`,
`probeTable`, `probeUtxo`) inhabit the structure; the checker equality is then
`rfl`/`txCheckerFor_some_eq_realCheckerOf`. This is a model witness, not a
claim that LDK produced the transaction.

**Why faithful.** It makes the previously implicit `(outpoint, amount,
scriptPubKey)` context a first-class object and reuses the already-proved
known-amount equality. It does not add an assumption.

**Fidelity risk.** Medium: the record can be instantiated with arbitrary
values. It must be described as a context contract, not as evidence that the
wallet selected or validated that outpoint. It must not be used to derive
`ConsensusSpendBridge`.

**Preserves.** `txCheckerFor_some_eq_realCheckerOf` and all known-amount
transfer theorems are unchanged; T1 only instantiates them.

### T2 — `LnLean.Proofs.Bitcoin.FundingContextTargets.FundingSpendContext` (P1, model extension, feasible)

**Statement shape.**

```lean
structure FundingSpendContext where
  params : FundingParams
  fundingTx : Bitcoin.Data.Tx
  fundingTxid : ByteArray
  fundingVout : Nat
  spendTx : Bitcoin.Data.Tx
  nIn : Nat
  hTxid : fundingTxid = Bitcoin.DataLaws.txid fundingTx
  hConfirmed : FundingConfirmed params fundingTx fundingVout
  hIn : nIn < spendTx.vin.length
  hPrev : (spendTx.vin.getD nIn Bitcoin.Capstone.RealChecker.dummyTxIn).prevout =
    LnLean.Bitcoin.fundingOutpoint fundingTxid fundingVout

theorem fundingSpendContext_checker
    (ctx : FundingSpendContext) :
    Bitcoin.TxValidation.Full.txCheckerFor ctx.spendTx ctx.nIn
        (some ctx.params.fundingSatoshis) =
      Bitcoin.Capstone.RealChecker.realCheckerOf ctx.spendTx ctx.nIn
        ctx.params.fundingSatoshis
```

**Hypotheses.** `FundingConfirmed` (`LnLean/Bitcoin/Funding.lean:395-399`),
input range, prevout equality, and the explicit `fundingTxid` equation using
`Bitcoin.DataLaws.txid` (`vendor/btc-lean-core/Bitcoin/DataLaws/Interface.lean:262`).
Keeping the txid explicit avoids inventing a new hash or silently trusting a
display-order byte string.

**Non-vacuity witness.** Construct `fundingTx` with one output
`{ value := params.fundingSatoshis, scriptPubKey := params.fundingScriptPubKey }`,
set `fundingTxid := Bitcoin.DataLaws.txid fundingTx`, and build `spendTx` with
one input at `(fundingTxid, 0)`; choose two 33-byte keys and any `csv`.
`FundingConfirmed` and `hTxid` are then `rfl`. Signature acceptance is not
asserted by T2.

**Why faithful.** It captures exactly the context LDK supplies operationally
at `event.rs:806-852` while making clear that the model, not LDK, is the source
of the context proof.

**Fidelity risk.** Medium: `FundingConfirmed` is a predicate, and a context
record is not a chain-inclusion proof. The target must not claim that the
funding transaction is confirmed or that the 2-of-2 witness verifies.

**Preserves.** `funding_interpreters_agree`, `funding_sighash_interpreters_agree`,
and the known-amount checker equality are unchanged.

### T3 — `LnLean.Proofs.Bitcoin.ToLocalContextTargets.ToLocalSpendContext` (P1, model extension, feasible)

**Statement shape.**

```lean
structure ToLocalSpendContext where
  spendTx : Bitcoin.Data.Tx
  nIn : Nat
  outpoint : Bitcoin.Data.OutPoint
  value : Amount
  revocationKey delayedPaymentKey : PubKey
  csv : Blocks
  program : ByteArray
  hIn : nIn < spendTx.vin.length
  hPrev : (spendTx.vin.getD nIn Bitcoin.Capstone.RealChecker.dummyTxIn).prevout = outpoint
  hcsv : csv < 32768
  hprog : hashSha256
    (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)) = program

theorem toLocalSpendContext_delayed_refinement
    (ctx : ToLocalSpendContext) (sig : ByteArray) ... :
    verifyWitnessProgram 10
      [sig, ByteArray.empty,
        serializeOpcodes (toLocalOps ctx.revocationKey ctx.delayedPaymentKey ctx.csv)]
      0 ctx.program ({ csv := true } : ScriptFlags) ({} : PolicyFlags)
      (Bitcoin.TxValidation.Full.txCheckerFor ctx.spendTx ctx.nIn (some ctx.value))
      false = .ok ↔
    (sequence-context conjunction ∧
      Bitcoin.Crypto.Ecdsa.Verify.verifyImpl
        (sig.extract 0 (sig.size - 1)) ctx.delayedPaymentKey.bytes
        (LnLean.Bitcoin.Sighash.sighashWitnessV0 ctx.spendTx ctx.nIn
          (serializeOpcodes (toLocalOps ctx.revocationKey ctx.delayedPaymentKey ctx.csv))
          (hashtypeOf sig) ctx.value) = true)
```

The statement is the `TxValidTransferTargets.lean:302` refinement with the
context fields projected. The sequence conjunct is exactly the one at
`:318-325`.

**Hypotheses.** `hIn`, `hPrev`, `hcsv`, `hprog`, the 33-byte key sizes,
signature size, valid delayed key, and nonempty signature—the same hypotheses
as the existing theorem, plus the explicit outpoint context.

**Non-vacuity witness.** Use the concrete one-input `H04` transaction with a
`toLocalOps`-derived program and `csv < 32768`; `hIn`/`hprog` are decidable.
The signature-side branch remains conditional on an explicit `verifyImpl`
witness, which the tree does not currently exhibit. State that limitation
instead of pretending the EC branch is non-vacuous.

**Why faithful.** It records the actual amount/delay/script context and leaves
the BIP 68/112 and EC obligations visible. It does not import LDK's sweeper
logic as a theorem.

**Fidelity risk.** Medium: same context-record risk as T1/T2, plus the
`toLocalOps` scaffold's fixed-width delay encoding limitations (already
documented at `TxValidTransferTargets.lean` scope, especially `minimalData`
and `csv = 32768`).

**Preserves.** The existing delayed/revocation pipeline theorems are unchanged.

### T4 — `LnLean.Proofs.Bitcoin.EcdsaTypedDigestTargets.CanonicalFundingDigest` (P0, model extension requiring maintainer approval, medium-high feasibility)

**Statement shape.**

```lean
structure CanonicalFundingDigest where
  bytes : ByteArray
  hsize : bytes.size = 32
  hbound : bytesToNatBE bytes < n

def verifyFundingDigest (M : PrimitiveModel) (pk : PubKey)
    (d : CanonicalFundingDigest) (sig : EcdsaSig) : Bool :=
  M.ecdsaVerify pk d.bytes sig

theorem canonicalFundingDigest_binds
    {M : PrimitiveModel} (h : ResidueBinding M.ecdsaVerify)
    {pk : PubKey} {d₁ d₂ : CanonicalFundingDigest} {sig : EcdsaSig}
    (h₁ : verifyFundingDigest M pk d₁ sig = true)
    (h₂ : verifyFundingDigest M pk d₂ sig = true) :
    d₁ = d₂
```

The proof is the 32-byte canonical-domain argument already in
`digestBindsModOn_canonical32` (`EcdsaDomainTargets.lean:438`), transported to
the digest structure: equal residues plus both values `< n` and both lengths
32 imply equal bytes (`bytesToNatBE_injective_of_size_eq`).

**Hypotheses.** `ResidueBinding M.ecdsaVerify`; both digests canonical; the two
accepted signatures. `KeyBinding` is independent and should be stated
separately if the full `VendorEcdsaContract` is used.

**Non-vacuity witness.** `canonical32_zeros` is `CanonicalDigest32 (zeros 32)`
(`EcdsaDomainTargets.lean:443`). For acceptance, the abstract `pointVerify`
witness in `contract_consistent_with_acceptance`
(`EcdsaConcreteTargets.lean:543`) supplies `ResidueBinding` and an accepted
triple. This is a model-level non-vacuity witness, not a claim about
`vendorVerify`.

**Why faithful.** It is the exact algebraic repair the tree already identifies:
a fixed-size, value-`< n` domain. It makes the type distinction impossible to
erase: a caller cannot pass an arbitrary transaction-length byte string as a
canonical digest.

**Fidelity risk.** High. This **changes the funding-signature interface** from
`fundingTag ++ tx` to a 32-byte digest. It is faithful only if the digest
preimage still includes the BOLT domain tag and all BIP 143 fields. It must not
be advertised as closing the real funding seam: it proves digest-level binding,
not transaction-byte binding.

**Preserves / does not weaken.** The negative theorems remain:
`verifyImpl_zeroPad`, `eufCma_vendorVerify_iff_totalReject`,
`no_bridged_nontrivial_model`, `withVendorEcdsa_no_funding`,
`not_digestBindsMod_any_tag`, and `not_digestBindsModOn33_any_tag` are the reason
the old interface cannot be repaired by a tag. If adopted, the old
`verifyFunding`/`fundingSignedValid_iff_vendor` statements must be renamed or
scoped rather than silently reinterpreted.

### T5 — `LnLean.Proofs.Bitcoin.EcdsaTypedDigestTargets.FundingDigestBindsTx` (P0, **external assumption**, not feasible as a theorem)

**Statement shape.**

```lean
def FundingDigestBindsTx (digestOfTx : Bitcoin.Data.Tx → CanonicalFundingDigest) : Prop :=
  ∀ tx₁ tx₂ : Bitcoin.Data.Tx,
    digestOfTx tx₁ = digestOfTx tx₂ → tx₁ = tx₂

theorem canonicalFundingDigest_binds_tx
    (h : FundingDigestBindsTx digestOfTx)
    {tx₁ tx₂ : Bitcoin.Data.Tx}
    (hdig : digestOfTx tx₁ = digestOfTx tx₂) :
    tx₁ = tx₂
```

**Hypotheses.** An explicit, named computational collision-resistance
assumption on the **funding preimage domain**, plus a deterministic
`digestOfTx` built from the BIP 143 preimage. The existing
`CollisionResistant` is not enough: it only quantifies over 32-byte inputs
(`LnLean/Crypto/Model.lean:56-57`), while transaction preimages are longer and
variable-length. Global `PreimageResistant` is explicitly retained only as a
hypothesis and is not a `PrimitiveModel` field (`Model.lean:59-66`); using it
would be a strong, possibly vacuous assumption.

**Non-vacuity witness.** A single-transaction domain, or a toy identity digest,
is a structural witness only. There is no real BIP 143 collision-resistance
witness in the tree. This is precisely why T5 is external and must not be
presented as proved.

**Why faithful.** It names the missing link between digest-level binding and
transaction-byte binding instead of hiding it inside a tag or a `ByteArray`
equality.

**Fidelity risk.** Very high: if stated as a global injectivity axiom it is
false/vacuous for a 32-byte hash; if stated computationally it is an assumption,
not a theorem. It must not weaken `EufCma` or replace it with an unlabeled
`ResidueBinding`.

**Preserves.** It leaves all negative counterexamples intact. It does not
strengthen `VendorEcdsaBridge` or claim a concrete secp256k1 implementation.

### T6 — `LnLean.Proofs.Bitcoin.SpendTargets.PositiveConsensusSpendBridge` (P2, model extension, feasible)

**Statement shape.**

```lean
def PositiveConsensusSpendBridge
    (verify : Script → WitnessStack → Bitcoin.Data.Tx → Bool)
    (L : InterpreterLaws) (msg : ByteArray) : Prop :=
  ∀ (vtx : Bitcoin.Data.Tx) (program witnessScript : ByteArray)
      (prog : List Stmt) (st : Stack),
    serializeStmts prog = witnessScript →
    L.sha256 witnessScript = program →
    Accepts L msg prog st →
    verify (p2wsh program) (st.reverse ++ [witnessScript]) vtx = true

def scriptVerifyVia (chk : ScriptChecker) ... :
    Script → WitnessStack → Bitcoin.Data.Tx → Bool := ...

theorem funding_positiveConsensusSpendBridge ... :
    PositiveConsensusSpendBridge (scriptVerifyVia chk ...) L msg
```

The funding and delayed instances should be obtained by wrapping the vendored
`verifyWitnessProgram` result as a Bool and applying
`funding_interpreters_agree` / `toLocal_delayed_interpreters_agree`; the
revocation instance should use `toLocal_revocation_interpreters_agree`.
`vendorVerify` is *not* the right function here: it is the model-order
`(pk,msg,sig)` ECDSA verifier (`EcdsaBridgeTargets.lean:113`), not a script
verifier.

**Hypotheses.** Exactly the existing positive-direction hypotheses: witness
serialization, hash link, `Accepts`, and the branch-specific ECDSA/size/sequence
premises.

**Non-vacuity witness.** The same conditional witnesses as
`funding_interpreters_agree` and `toLocal_delayed_interpreters_agree`; this
target packages them, so it is non-vacuous exactly when those theorems are.

**Why faithful.** It states the one direction that is actually proved and makes
the absence of the reverse direction explicit. `ConsensusSpendBridge` remains
untouched and unproved.

**Fidelity risk.** Low. The only risk is naming: `Positive...` must not be cited
as `ConsensusSpendBridge`, and it must not be used to claim negative-direction
or consensus completeness.

**Preserves.** `ConsensusSpendBridge` and all existing positive-direction
theorems are unchanged; no assumption is hidden.

### T7 — `LnLean.Proofs.Bitcoin.EcdsaTypedDigestTargets.canonicalDigestContract_acceptance_witness` (P2, model-level non-vacuity, feasible)

**Statement shape.**

```lean
theorem canonicalDigestContract_acceptance_witness :
    ∃ (verify : PubKey → ByteArray → EcdsaSig → Bool)
      (pk : PubKey) (d : CanonicalFundingDigest) (sig : EcdsaSig),
      ResidueBinding verify ∧ KeyBinding verify ∧
        verify pk d.bytes sig = true
```

Use the abstract `pointVerify` witness already isolated by
`contract_consistent_with_acceptance` (`EcdsaConcreteTargets.lean:543`) and
`canonical32_zeros` (`EcdsaDomainTargets.lean:443`) for the digest.

**Hypotheses.** None beyond the abstract witness; this is a consistency result,
not a vendor theorem.

**Non-vacuity witness.** `pointVerify` accepts at least one triple
(`contract_consistent_with_acceptance`) and `CanonicalDigest32 (zeros 32)` is
inhabited.

**Why faithful.** It prevents the typed-digest proposal from being dismissed as
structurally vacuous, while explicitly not claiming that `verifyImpl` accepts
anything.

**Fidelity risk.** Low, provided the result is labelled abstract. It must never
be combined with `withVendorEcdsa`; that construction is total-rejecting
(`withVendorEcdsa_no_funding`, `EcdsaConcreteTargets.lean:303`).

**Preserves.** `withVendorEcdsa_no_funding` remains the concrete-model
counterexample; T7 is only an abstract consistency witness.

## 5. Assumptions, counterexamples, and non-vacuity risks

The following must be preserved verbatim; they are load-bearing:

* `verifyImpl_zeroPad` (`EcdsaConcreteTargets.lean:126`) — the vendor verifier
  cannot distinguish a message from a zero-padded one.
* `eufCma_vendorVerify_iff_totalReject` (`:163`) — C3 at the vendor verifier is
  exactly total rejection.
* `bridged_model_totalReject` (`:231`), `no_bridged_nontrivial_model` (`:252`),
  `exists_bridged_model_iff_totalReject` (`:265`).
* `withVendorEcdsa_no_funding` (`:303`) — the wave-8 concrete model has no
  accepted funding signature; do not cite it as a non-vacuous instance.
* `not_digestBindsMod_fundingTag` (`:616`), `not_digestBindsMod_any_tag`
  (`EcdsaDomainTargets.lean:281`), `no_digestBindsMod_anywhere` (`:288`),
  `not_digestBindsModOn33_any_tag` (`:301`).
* `truthy_nonminimal_true` (`SpendTargets.lean:716`) — the model accepts
  `#[0x00]` while Core does not; no theorem here is consensus validation.
* `contract_consistent_with_acceptance` (`EcdsaConcreteTargets.lean:543`) —
  `ResidueBinding ∧ KeyBinding` is not structurally vacuous, but its witness is
  the abstract `pointVerify`, not `verifyImpl`.

No target above replaces `EufCma` with `ResidueBinding` silently. T4 requires
`ResidueBinding` explicitly. T5 is explicitly an external assumption. T1–T3 and
T6–T7 add records/definitions or instantiate existing theorems.

The main **hidden-assumption traps** are:

1. Treating `txCheckerFor tx nIn (some amount)` as if `amount` were proved equal
   to the referenced outpoint. It is not; `digest_commits_amount` only exposes
   the preimage field.
2. Treating `FundingConfirmed` as chain inclusion. It is a predicate over a
   supplied `Tx`.
3. Treating the LDK wallet's BIP84/P2WPKH path or its `sign_message` API as a
   concrete 2-of-2/BIP 143 verifier. It is neither.
4. Using `CollisionResistant` on 32-byte inputs to prove arbitrary transaction
   binding. That is a scope error (`Model.lean:56-57`).
5. Using the canonical 33-byte theorem for real funding transactions. The
   theorem is about an abstract 33-byte payload, as `THEOREM-INDEX.md:135`
   already says.
6. Replacing `fundingTag ++ tx` with a 32-byte digest without a maintainer
   decision. That changes the meaning of `verifyFunding`, `fundingSignedValid`,
   and the catalog scope note.

## 6. Wave-13 recommendation

**No safe wave-13/14 proof lane closes `L1-01`, `L1-02`, or `L1-07`.**

* `L1-01`/`L1-07` are mechanically blocked at the current untyped `ByteArray`
  interface: `no_bridged_nontrivial_model` is a kernel-checked impossibility,
  not an unfinished proof. A lane that tries to prove a non-vacuous
  `VendorEcdsaBridge` will either fail or produce another total-rejecting model.
* `L1-02` has no `TxValidation.Full` transfer gap. Its residual requirement is
  a concrete secp256k1 verifier (or explicit computational assumption) plus the
  actual spent amount/outpoint and transaction-validity context.
* The pinned LDK Node/Server paths do not supply the missing verifier. They
  supply operational context (exact funding output script/value, wallet-owned
  UTXO selection, address/network checks, generic message signing) and delegate
  transaction acceptance to bitcoind. That is useful evidence for a context
  contract, not a concrete L1 script bridge.

The only legitimate next steps are:

1. **Human/maintainer decision:** approve or reject the typed-digest model
   extension (T4/T5). If approved, it is a new interface and the old
   `verifyFunding` statements must be renamed or re-scoped. It still does not
   prove a concrete secp256k1 verifier. **Top proposed target: T4**, because it
   addresses the central untyped-`ByteArray` blocker without pretending to
   prove secp256k1; it is explicitly not a safe implementation target until the
   maintainer approves the interface change.
2. **External assumption record:** state the concrete secp256k1 refinement,
   spent-outpoint/amount provenance, and transaction-validity context as
   explicit external requirements. Do not add a global injectivity axiom.
3. **Optional low-risk model packaging (only if explicitly scoped):** T1–T3,
   T6, and T7 can be implemented as model-level context/assembly targets. They
   improve traceability and non-vacuity but do **not** close the P0 issues and
   must not be reported as closure.

**Recommendation:** defer the P0 closures; treat the concrete EC, amount/
outpoint, and consensus pieces as external; do not implement a fake
`VendorEcdsaBridge` or a concrete secp256k1 bridge in wave 13/14.

## 7. Evidence and commands

Pins reproduced read-only:

```sh
git -C /tmp/opencode/ldk-refs/ldk-node rev-parse HEAD
# fa123fed131e27ecc420b77fa7086fcf1ddaebb8
git -C /tmp/opencode/ldk-refs/ldk-server rev-parse HEAD
# c17dc11dde38f88c53457039ddf30c6b90a63ba2
```

Lean/declaration inspection (read-only):

```sh
rg -n "LN-L1-001|LN-L1-004|L1-01|L1-02|L1-07" \
  docs/THEOREM-INDEX.md docs/TRACEABILITY.md docs/OPEN-ISSUES.md
rg -n "theorem|def |structure " LnLean/Proofs/Bitcoin/*.lean
nl -ba LnLean/Proofs/Bitcoin/EcdsaConcreteTargets.lean
nl -ba LnLean/Proofs/Bitcoin/EcdsaDomainTargets.lean
nl -ba LnLean/Proofs/Bitcoin/TxValidTransferTargets.lean
nl -ba LnLean/Proofs/Bitcoin/SpendTargets.lean
```

LDK inspection (read-only):

```sh
nl -ba /tmp/opencode/ldk-refs/ldk-node/src/event.rs | sed -n '800,860p'
nl -ba /tmp/opencode/ldk-refs/ldk-node/src/wallet/mod.rs | sed -n '1700,1760p'
nl -ba /tmp/opencode/ldk-refs/ldk-node/src/wallet/mod.rs | sed -n '2160,2320p'
nl -ba /tmp/opencode/ldk-refs/ldk-node/src/wallet/mod.rs | sed -n '2540,2620p'
nl -ba /tmp/opencode/ldk-refs/ldk-node/src/wallet/mod.rs | sed -n '4000,4025p'
nl -ba /tmp/opencode/ldk-refs/ldk-node/src/chain/bitcoind.rs | sed -n '920,935p'
nl -ba /tmp/opencode/ldk-refs/ldk-server/ldk-server/src/api/onchain_send.rs
nl -ba /tmp/opencode/ldk-refs/ldk-server/ldk-server/src/api/sign_message.rs
nl -ba /tmp/opencode/ldk-refs/ldk-server/ldk-server/src/api/verify_signature.rs
rg -n "verify_script|verifyScript|check_signature" \
  /tmp/opencode/ldk-refs/ldk-node/src /tmp/opencode/ldk-refs/ldk-server/ldk-server/src
# no local script-verifier call was found in either public path
```

No cargo tests, no network fetches, and no whole-tree build were run. Only this
report was written.
