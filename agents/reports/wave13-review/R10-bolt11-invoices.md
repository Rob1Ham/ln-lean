# R10 — BOLT 11 invoice parse/create/sign/verify/expiry

**Status:** read-only review
**Pins:** LDK Node `fa123fed131e27ecc420b77fa7086fcf1ddaebb8`, LDK Server `c17dc11dde38f88c53457039ddf30c6b90a63ba2`

## 1. Scope and current Lean surface

This lane covers the BOLT 11 invoice from human-readable prefix through
bech32 data part, tagged fields, signable digest, signature, expiry, and the
LDK receive/send/claim/fail lifecycle. The current Lean surface is a
**semantic invoice record plus a pre-bech32 field-list codec**, not an invoice
parser or signer.

| Layer | Main declarations | What it actually claims | What it does not claim |
|---|---|---|---|
| Semantic record | `Invoice` (`LnLean/Payment/Invoice.lean:197-210`), `Network`/`hrpPrefix` (`:99-123`), `Tag`/`Tag.code` (`:295-326`), `Tag.fixedDataLength` (`:328-345`) | Network token, optional `Msat` amount, hash, timestamp, relative expiry, `d`/`h` description, mandatory payee key, three feature booleans, 65-byte signature, mandatory payment secret, CLTV floor; tag numbers are injective and fit five bits | No HRP decimal amount, no bech32 string, no data-part bytes, no digest, no real signature, no fallback/metadata fields |
| Validity / verify / expiry | `Invoice.Valid` (`:238-247`), `Invoice.verify` (`:252-256`), `Invoice.isExpired` (`:226-227`), `Invoice.amountSatisfies` (`:277-280`), `InvoiceSignature.recoveryIdInRange` (`:173`) | Structural lengths, `Msat.MAX`, 35-bit timestamp, 32-byte `h`; `verify = Valid ∧ sigCheck payee (digest i) sig`; expiry `expiresAt < now`; BOLT 4 `a ≤ paid ≤ 2a` window | `Valid` has no signature check, no payment-secret/feature coupling, no positivity, no recovery-id conjunct; `digest` and `sigCheck` are parameters; `recoveryIdInRange` is defined but never used |
| Invoice laws | `LnLean/Proofs/Payment/InvoiceProps.lean`: `valid_*` projections (`:111-150`), `exists_valid_zero_amount` (`:210-212`), `AmountPositive` (`:216-219`), `validAt*` (`:265-295`), `decodeSemantic` (`:343-362`), `InvoiceSignatureAssumption` (`:454-467`) | Projections from validity, expiry monotonicity, a zero-amount counterexample, a semantic decoder from a raw field record, conditional signature authorization | No encoding/digest theorem; `AmountPositive` is a separate predicate, not part of `Valid`; signature law is conditional on an explicitly assumed verifier |
| Pre-bech32 wire codec | `LnLean/Proofs/Payment/InvoiceWireTargets.lean`: `RouteHintHop` (`:258-264`), `featureBits` (`:206-210`), `encodeFeatures` (`:237-238`), `printFields` (`:500-505`), `parseFields` (`:519-543`), `parse_print` (`:660-661`), `print_injective` (`:679-681`), `parse_print_paymentHash` (`:686-688`), `wire_paymentHash_binding` (`:1020-1021`), `signature_not_payment` (`:1129-1136`) | Canonical fixed-order `p,s,n,x,c,9,r*` (the module writes `f` for the `9` field); round trip/injectivity on canonical records; malformed and duplicate-`p` rejection; hash/secret projection; signature acceptance is not payment evidence | Pre-bech32 only; fixed 18-byte route hop; fixed 8-byte `x`/`c`; fixed 4-byte features; no fallback/`m`/`d` payload; no payee recovery; no digest |
| Canonical parser study | `LnLean/Proofs/PhaseC3/InvoiceParser.lean`: `expiryWidth` (`:221-226`), `ExpiryCanonical` (`:296-297`), `TagList` (`:534-536`), `parse_encode` (`:559-560`), `roundtrip_needs_canonicality` (`:608-612`) | Four-tag subset (`p,s,x,d` flow) with minimum-width expiry, list round trip, and an explicit non-canonical counterexample | Not connected to `InvoiceWireTargets`; expiry codecs disagree; no HRP/bech32/digest |
| Binding / secret | `LnLean/Proofs/PhaseC2/InvoiceBinding.lean`: `ExactPayment` (`:92-94`), `amountSatisfies_pins_of_le` (`:109-110`), `preimageCommits_unique` (`:184-185`), expiry monotonicity (`:258-295`); `LnLean/Proofs/WaveD/D29.lean:394-398`; `LnLean/Security/Invariants.lean:385-409` | Amount pinning under a bound, conditional preimage uniqueness, payment-secret match for an accepted final payload, separate `Security.Invoice` record with `signatureValid : Bool` | `Security.Invoice` is a five-field abstraction never linked to `Payment.Invoice`; no wire-level amount-preservation theorem from the codec; no inbound claim state |
| Payment lifecycle | `PaymentSession` (`LnLean/Payment/HTLC.lean:102-107`), `PaymentSession.settle` (`:136-137`), `settle_terminal` (`:148-153`) | Coarse `pending`/`succeeded`/`failed`; terminal absorption | No payment id, kind, preimage, claim amount, or claim/fail guards; `settle` explicitly does not check the preimage (`:132-135`) |

Catalog rows and the declarations actually cited by the catalog:

* `LN-PM-001` — "A consistent invoice has the payment session's hash and
  amount." `leanTarget` names `LnLean.Security.Invoice.consistent_hash`
  (`Security/Invariants.lean:401-403`), `consistent_amount` (`:406-408`), plus
  the `InvoiceWireTargets` hash/preimage family (`parse_print_paymentHash`,
  `wire_paymentHash_binding`, `preimage_unique_of_injective`,
  `preimage_determines_hash`, `paymentHash_eq_iff_bytes`). The projection is
  from the **separate** `Security.Invoice` record (`:385-391`), whose
  `signatureValid` is an unconstrained `Bool`; it is not linked to
  `LnLean.Payment.Invoice`. There is no wire-level amount-preservation
  theorem (`parse_print_amount`/`wire_amount_binding`); only the standalone
  `decodeAmount_encodeAmount_none`/`_some` codecs (`:186-202`) exist.
* `LN-PM-002` — "A BOLT 11 invoice signature is valid for the payee node key."
  `Invoice.signature_valid` (`Invoice.lean:267-271`) is exactly the second
  conjunct of `verify`. `signatureOnly_verifies`
  (`InvoiceWireTargets.lean:1108-1110`) instantiates `digest := fun _ =>
  ByteArray.empty` and `sigCheck := fun _ _ _ => true`, so the catalog row is a
  model-level projection, not a statement about a real invoice encoding.
* `LN-PM-003` — `Invoice.payment_secret_match`
  (`D29.lean:394-398`) is conditional on `p.acceptedBy i`; the unconditional
  form is refuted by `waveD_d29_unconditional_claim_false`
  (`D29.lean:374-380`, after the `acceptedBy` lemmas at `:191-230`).
* `LN-PM-007` — the pre-bech32 field-list codec: `parseFields_printFields`,
  `parse_print`, `print_injective`, `witness_parse`, `malformed_parse_none`,
  `duplicateHash_parse_none`, `decodeHop_encodeHop`, `encodeHop_size`
  (`InvoiceWireTargets.lean:557-568`, `:660-661`, `:679-681`, `:869-871`,
  `:898-900`, `:922-924`, `:377-379`, `:372-374`). The row's own claim
  explicitly disclaims bech32/HRP/checksum and signable-digest coverage.

Three scope facts drive the gap analysis:

1. **`Invoice.verify` does not see an encoding.** `digest : Invoice →
   ByteArray` can ignore the invoice, and `sigCheck` is unconstrained. The
   signature-separation counterexamples are deliberately retained and must not
   be weakened.
2. **The wire codec is a canonical field list, not BOLT 11's data part.**
   `WireInvoice` (`:586-597`) requires `p,s,n,x,c,9,r*` in fixed order with
   `n` mandatory, while BOLT 11 makes `n/x/c` optional, makes `r` conditional
   on the absence of a public channel, and requires exactly one `p`, one `s`,
   and exactly one of `d`/`h`.
3. **Two codecs disagree.** `InvoiceWireTargets` uses fixed-width
   `encodeNat` (8 bytes) for `x`/`c` and 4-byte features, while
   `PhaseC3.InvoiceParser` requires minimum-width expiry
   (`expiryWidth`, `ExpiryCanonical`). Both cannot be faithful to BOLT 11's
   minimum-`data_length` writer rule.

## 2. LDK datapoints (with `file:line`)

LDK clones are under `/tmp/opencode/ldk-refs/`; `rust-lightning` and BOLT refs
are under `refs/` in this repository. Pin note: LDK Server `c17dc11` depends on
LDK Node `179b4b263762155a7ff515ddad7e757a80807fd5`
(`ldk-server/ldk-server/Cargo.toml:16`), not the pinned `fa123fe`. The pinned
`fa123fe` `claim_for_id` takes `(payment_id, preimage)`
(`ldk-node/src/payment/bolt11.rs:424-426`), while LDK Server calls
`(payment_id, claimable_amount_msat, preimage)`
(`ldk-server/ldk-server/src/api/bolt11_claim_for_id.rs:33-34`). Any claim-amount
conclusion is a Server-version datapoint, not a pinned-Node API fact.

### 2.1 Create / receive

* `ldk-node/src/payment/bolt11.rs:567-580` `receive_for_hash`; `:612-618`
  `receive_variable_amount`; `:640-645`
  `receive_variable_amount_for_hash`; `:593-607`
  `receive_for_hash_with_min_final_cltv_expiry_delta`. Invoices are created by
  LDK's `Bolt11Invoice` builder, not by local field assembly.
* `ldk-node/src/payment/bolt11.rs:554-556`, `:627-629`, `:692-694`,
  `:771-773`: callers **must never reuse a payment hash**; LDK Node does not
  detect or reject reuse. Duplicate-payment-hash rejection is therefore an
  external caller obligation, not a modeled transition.
* `ldk-server/ldk-server/src/api/bolt11_receive.rs:22-36`: amount-ful and
  variable-amount receive both return the invoice string plus payment hash and
  payment secret. This is the concrete create surface the Lean model lacks.

### 2.2 Send / amount policy

* `ldk-node/src/payment/bolt11.rs:202-217` `send_internal`: derives
  `payment_id` from the payment hash and rejects a duplicate when the stored
  payment is `Pending` or `Succeeded`.
* `:221-228` uses `invoice.payment_secret()` and
  `amount_msat.or_else(|| invoice.amount_milli_satoshis())`; a zero-amount
  invoice with no explicit amount is rejected.
* `:335-355` `send_using_amount`: rejects only `amount_msat <
  invoice_amount_msat`. It does **not** enforce BOLT 4's upper `2a` bound.
  `LnLean.Payment.Invoice.amountSatisfies` is the stricter `a ≤ paid ≤ 2a`
  window; this is a payer-policy difference, not a Lean contradiction.
* `ldk-server/ldk-server/src/api/bolt11_send.rs:26-42`: parses with
  `Bolt11Invoice::from_str` and dispatches to `send` / `send_using_amount`.

### 2.3 Decode surface

* `ldk-server/ldk-server/src/api/decode_invoice.rs:21-26` parses with
  `Bolt11Invoice::from_str`; `:29-104` returns destination, payment hash,
  amount, timestamp, expiry, direct/hashed description, first fallback
  address, `min_final_cltv_expiry_delta`, payment secret, route hints (each hop
  includes `node_id`), feature string, currency, payment metadata, and
  `is_expired`. This is the field list the Lean model should be compared
  against; absence of a field here is a real gap, not a naming difference.

### 2.4 Claim / fail lifecycle

* `ldk-node/src/payment/bolt11.rs:424-465` `claim_for_id`: requires the node
  to be running, the payment id to be known, the kind to be `Bolt11`, and
  `SHA256(preimage) == stored payment_hash`; only then `claim_funds`.
  Wrong id, non-Bolt11 kind, and wrong preimage all return errors.
* `:477-532` `fail_for_id`: requires a known Bolt11 payment, marks the store
  record `Failed`, then `fail_htlc_backwards(payment_hash)`.
* `ldk-server/e2e-tests/tests/e2e.rs:2079-2095`: wrong preimage and
  insufficient `claimable_amount_msat` claims are rejected with
  `InvalidRequestError`. `:2157-2162`: failing an unknown payment id is
  rejected. The amount check belongs to the Server's pinned Node revision, not
  to `fa123fe`.
* The current `PaymentSession.settle` (`LnLean/Payment/HTLC.lean:136-137`)
  has none of these guards; its docstring explicitly defers the preimage check
  to a caller premise.

### 2.5 BOLT 11 parse / signature / expiry (pinned rust-lightning)

Repository-pinned supplementary source is
`refs/rust-lightning` at `fe4900930c6bd5786ec4203274d7cf312776a5a6`; this is a
different `lightning-invoice` revision than LDK Node's dependency
`d7a980641c6325ddda5072a0f470ef8392676cf5` (`ldk-node/Cargo.toml:91`), so
treat these as normative datapoints, not as the exact code linked into the
pinned Node.

* **HRP amount.** `lightning-invoice/src/de.rs:420-439` parses the currency,
  decimal amount, and SI prefix; `:425` accepts any `u64` (including `0`) and
  `:431-435` checks multiplier overflow. The BOLT writer rules are at
  `refs/bolts/11-payment-encoding.md:65-75`: positive decimal integer, no
  leading zeros, `p` multiplier requires last decimal `0`.
* **Bech32 envelope.** `de.rs:392-415` `CheckedHrpstring::new::<Bolt11Bech32>`
  and `ser.rs:182-196` `with_checksum::<bech32::Bech32>`: charset, HRP
  expansion, checksum, and case are handled by the bech32 layer before any
  invoice field is seen.
* **Data part and digest.** `lib.rs:1092-1119` `hash_from_parts` hashes the HRP
  bytes then the zero-padded, signature-excluded data-part bytes with SHA-256;
  `lib.rs:1127-1129` `signable_hash`; `lib.rs:1312-1314` stores it at parse
  time. BOLT 11 states the same construction at
  `refs/bolts/11-payment-encoding.md:110-124`.
* **Tag widths.** BOLT 11 `:133-163`: `p`/`s`/`h` 52 groups, `n` 53 groups,
  `x`/`c` minimum `data_length`, `f` version-dependent, `r` a sequence of
  51-byte hops. `r`'s 51-byte layout and `src_node_id` are explicit at
  `de.rs:700-741`; the hop decode requires `bytes.len() % 51 == 0`.
* **Field counts.** `lib.rs:1322-1352` requires exactly one `p`, exactly one
  `d` or `h`; `lib.rs:1357-1373` requires exactly one `s`. `lib.rs:1385-1408`
  requires a `9` field that supports `payment_secret` and has no
  `requires_unknown_bits`; `lib.rs:1376-1383` rejects non-whole-millisatoshi
  amounts. `from_signed` check order is `:1442-1450`
  (`check_field_counts`, `check_feature_bits`, `check_signature`,
  `check_amount`).
* **Signature.** `lib.rs:1017-1038` recovers or verifies against the explicit
  `n` key; `de.rs:474-488` decodes the 64-byte compact signature plus recovery
  id and rejects an invalid recovery id via `RecoveryId::from_i32`.
  `lib.rs:588` is the `Bolt11InvoiceSignature` wrapper.
* **Payee key.** `lib.rs:1514-1525` `get_payee_pub_key`: prefer explicit `n`,
  otherwise recover from the signature. BOLT 11 `:187-188` makes `n` optional
  exactly because recovery is expected.
* **Expiry.** `lib.rs:1529-1531` `expires_at` uses `checked_add` and returns
  `None` on overflow; `:1534-1538` defaults to 3600; `:1573-1578`
  `would_expire` uses strict `<` with an overflow sentinel. BOLT 11 `:350-359`
  says the payer SHOULD NOT pay and the payee SHOULD NOT accept after
  `timestamp + expiry`.
* **Fallback.** `lib.rs:1597-1611` maps SegWit v0–16 programs, P2PKH 17, and
  P2SH 18 to addresses and silently drops unknown versions; `de.rs:660-693`
  enforces program length 2–40 and the 20/32-byte hash lengths. BOLT 11
  `:189-192` permits one or more `f` fields and says the payer uses the first
  understood one.
* **Features.** `lightning-types/src/features.rs:464-472` defines
  `VariableLengthOnion` from odd bit 9, so the optional bit is 9 and the
  required/even bit is 8; `:486-495` `PaymentSecret` uses odd 15 / even 14;
  `:497-506` `BasicMPP` uses odd 17 / even 16. The macro contract is `:408-410`,
  and `requires_feature`/`supports_feature` are `:320-332`.
* **Route hints.** `de.rs:700-741` decodes a 51-byte hop as
  `src_node_id[33] || scid[8] || fee_base[4] || fee_prop[4] || cltv[2]`, and
  `lib.rs:1623-1636` returns the hint list in invoice order.

## 3. Gap matrix

| Behavior | Lean status | LDK evidence | Gap / counterexample | Priority |
|---|---|---|---|---|
| HRP network prefix | **partial** | `de.rs:420-439`; `decode_invoice.rs:29-32` | `Network.hrpPrefix`/`networkOfPrefix` cover four tokens, but the string is a token in a `WireHeader`, not a parsed bech32 HRP; no `lnbc`+amount+multiplier grammar | P1 |
| Bech32 charset/checksum/case | **missing** | `de.rs:392-415`; `ser.rs:182-196` | No charset map, GF(32) checksum, HRP expansion, or mixed-case rejection. `WireInvoice` starts *after* the envelope. | P0 |
| Signable digest (HRP bytes + padded data part) | **missing** | `lib.rs:1092-1129`; BOLT 11 `:110-124` | `Invoice.verify` takes `digest : Invoice → ByteArray`; no theorem relates it to an encoding. `signatureOnly_verifies` uses `fun _ => empty`. | P0 |
| Compact signature tied to payee/digest | **partial / external** | `lib.rs:1017-1038`, `:1412-1418`; `de.rs:474-488` | Only the second conjunct of `verify` with an unconstrained `sigCheck`; no recovery-id check in `Valid` (`recoveryIdInRange` unused at `Invoice.lean:173`); `signature_not_payment` is retained. | P0 |
| Optional `n` + payee recovery | **missing** | `lib.rs:1514-1525`; BOLT 11 `:187-188` | Core `Invoice.payee` is mandatory (`Invoice.lean:204`), so the no-`n` recovery path cannot be represented; no explicit-vs-recovered distinction. | P2 |
| HRP amount positivity/canonicality/multipliers | **missing** | BOLT 11 `:65-75`; `de.rs:420-439`; `lib.rs:1376-1383` | `Valid` accepts `some 0` (`exists_valid_zero_amount`, `InvoiceProps.lean:210-212`); no leading-zero rule, decimal parser, `m/u/n/p` multipliers, or `p`-last-digit rule. LDK accepts numeric `0`, so do not claim LDK enforces positivity. | P1 |
| 35-bit timestamp | **covered** | BOLT 11 `:104-108`; `de.rs:441-457`; `lib.rs:132-137` | `MAX_TIMESTAMP` and `Valid.timestampBound` match. No bech32 7-group decode, but the semantic bound is faithful. | — |
| Exactly one `p` / `s` / (`d` or `h`) | **partial** | `lib.rs:1322-1373`; BOLT 11 `:165-172` | Wire codec requires `p,s` positionally and rejects duplicates; `d`/`h` is carried out of band (`toInvoice` takes it as an argument), so the exactly-one rule is only enforced by the `InvoiceDescription` sum type at the core level, not by the wire parser. | P1 |
| `x`/`c` minimum `data_length` | **contradicted** | BOLT 11 `:180-186`; `PhaseC3/InvoiceParser.lean:221-297` | `InvoiceWireTargets.expiryField`/`minFinalCltvField` use fixed 8-byte `encodeNat` (`:421-424`), while `PhaseC3` proves minimum-width expiry. The fixed encoder violates "no leading 0 field-elements". | P1 |
| `9` feature bits: pairing, minimal width, unknown bits | **partial / contradicted** | `features.rs:300-343`, `:464-506`; `lib.rs:1385-1408`; BOLT 11 `:202-206`, `:303-326`; BOLT 9 `:11-14`, `:64-80` | BOLT 9/LDK use **even = required, odd = optional** (payment_secret 14/15, var_onion 8/9, basic_mpp 16/17). `featureBits` sets only the even/required bits 14/16/8, and `featuresOfBits` ignores the odd/optional bits, so an invoice advertising optional `payment_secret` (bit 15) decodes as `paymentSecretRequired = false`, losing the supported/optional distinction; the codec uses a fixed 4-byte payload, has no "both bits set" normalization, and no unknown-required rejection. | P1 |
| `f` fallback addresses | **missing** | `lib.rs:1597-1611`; `de.rs:660-693`; BOLT 11 `:189-192` | `Tag.fallback` exists only as numeric tag 9; no fallback variant in `Invoice`/`WireInvoice`; no SegWit version/program lengths, P2PKH/P2SH, unknown-version skip, or first-understood ordering. | P1 |
| `m` payment metadata | **missing** | `decode_invoice.rs:84`; BOLT 11 `:148-149` | `Tag.paymentMetadata` is numeric only; no field or accessor. Metadata semantics/size limit are absent. | P2 |
| `r` private route hops | **partial / contradicted** | `de.rs:700-741`; `lib.rs:1623-1636`; BOLT 11 `:155-160` | `RouteHintHop` is 18 bytes (`InvoiceWireTargets.lean:258-264`, `encodeHop_size:372-374`) and **omits the 33-byte `src_node_id`**; BOLT/LDK require 51 bytes. Flat list, no per-hint grouping/preference semantics. Prior S11 report already flagged this boundary. | P0 |
| `d`/`h` description payload | **partial** | `lib.rs:1322-1352`; BOLT 11 `:147-151` | `InvoiceDescription` models the sum type, but the wire codec omits `d`/`h`; `toInvoice` takes the description as an explicit argument. No UTF-8 validation or 639-byte `d` limit. | P1 |
| Expiry semantics | **covered / partial** | `lib.rs:1529-1578`; BOLT 11 `:344-359` | `isExpired = expiresAt < now` matches `would_expire`; defaults 3600/18 match. Missing: LDK's `checked_add` overflow fallback (model uses `Nat`), and any inbound receive-time rejection (`SHOULD NOT accept`). | P1 |
| Create / sign | **missing** | `bolt11.rs:567-645`; `lib.rs:948-1001` | No constructor from fields to a signed bech32 invoice; no `sign` with a secret key; no digest to sign. `toInvoice` is a projection from an already-built wire record. | P0 |
| Decode surface | **partial** | `decode_invoice.rs:29-104` | Lean exposes semantic fields but not fallback, metadata, currency string, feature string, or `is_expired` derived from a real parse. | P1 |
| Send amount policy | **partial / divergent** | `bolt11.rs:221-228`, `:335-355` | Lean `amountSatisfies` is `a ≤ paid ≤ 2a`; LDK `send_using_amount` enforces only `invoice_amount ≤ paid`. Both are modeled propositions, but neither is connected to the other or to an actual send transition. | P2 |
| Inbound claim (preimage/amount) | **missing** | `bolt11.rs:424-465`; `e2e.rs:2079-2095` | `PaymentSession.settle` (`HTLC.lean:136-137`) has no id, kind, preimage, or amount guard; any outcome can be installed. | P1 |
| Inbound fail / unknown id | **missing** | `bolt11.rs:477-532`; `e2e.rs:2157-2162` | No fail transition, no known-id/kind check, no store update, no backward-fail event. | P1 |
| Duplicate payment hash / id reuse | **partial / external** | `bolt11.rs:207-217`, `:554-556` | Wire duplicate `p` is rejected (`duplicateHash_parse_none`); payment-hash reuse is explicitly undetected by LDK Node and is an external caller obligation. | P2 |
| Payment-secret binding | **partial** | BOLT 11 `:146`; `D29.lean:394-398` | Conditional on `acceptedBy`; the core `Invoice.Valid` does not require the `9` field to advertise `payment_secret`, and the wire codec records only the even/required bit, so an optional payment-secret advertisement (bit 15) is not represented. | P1 |

## 4. Proposed targets

All names below are **new** declarations. None strengthens `Invoice.Valid`,
`Invoice.verify`, `Security.Invoice.Consistent`, or replaces an existing
theorem. Each target is a model extension unless marked external.

### T1 — Concrete data-part encoder and signable digest (P0)

**Name.** `LnLean.Proofs.Payment.InvoiceEncoding.hrpBytes`,
`dataPartBytes`, `signableDigest`, with
`signableDigest_eq_hash_from_parts`.

**Statement shape.**

```lean
/-- `hrpBytes` renders the canonical HRP, including the T4 amount grammar. -/
def hrpBytes (w : WireInvoice) : ByteArray := ...

/-- Data-part bytes excluding the 65-byte signature, zero-padded to a byte. -/
def dataPartBytes (w : WireInvoice) : ByteArray := ...

def signableDigest (sha256 : ByteArray → ByteArray) (w : WireInvoice) : ByteArray :=
  sha256 (hrpBytes w ++ dataPartBytes w)

theorem signableDigest_congr {w w' : WireInvoice}
    (h : hrpBytes w ++ dataPartBytes w = hrpBytes w' ++ dataPartBytes w') :
    signableDigest sha256 w = signableDigest sha256 w' := by
  simp [signableDigest, h]

/-- The encoding is injective on canonical invoices; proved from the field
lemmas, not assumed. -/
theorem encoding_injective {w w' : WireInvoice}
    (hw : w.Canonical) (hw' : w'.Canonical)
    (h : hrpBytes w ++ dataPartBytes w = hrpBytes w' ++ dataPartBytes w') :
    w = w' := ...

theorem signableDigest_covers_amount {w w' : WireInvoice}
    (hw : w.Canonical) (hw' : w'.Canonical) (ha : w.amount ≠ w'.amount) :
    hrpBytes w ++ dataPartBytes w ≠ hrpBytes w' ++ dataPartBytes w' := ...
```

**Hypotheses.** `w.Canonical` for the width lemmas; SHA-256 is an explicit
parameter (do not import `Crypto.Model` into the payment layer). The
field-coverage lemmas are structural and do not need collision resistance.
`hrpBytes` consumes T4's canonical amount renderer; if T4 is deferred, the
first cut should restrict T1 to amount-less invoices rather than invent a
second HRP grammar.

**Non-vacuity.** `witnessWire` (`InvoiceWireTargets.lean:838-851`) already
round-trips; use it to instantiate `signableDigest` and show two different
amounts yield different pre-hash byte strings. The digest itself is a concrete
byte string, so the witness is checkable by `decide`/`rfl`.

**Why faithful.** `lib.rs:1092-1119` hashes HRP bytes followed by the padded,
signature-excluded data part; BOLT 11 `:110-124` specifies the same. This is
the missing object the current `digest` parameter abstracts.

**Priority/fidelity/feasibility.** P0; high fidelity to the byte construction;
medium feasibility (byte concatenation and 5-to-8-bit padding are computable,
but bech32 field-element encoding must be modeled, not imported).

### T2 — Signature binds the encoded invoice (P0)

**Name.** `LnLean.Proofs.Payment.InvoiceEncoding.verifyEncoding`,
`verifyEncoding_binds_digest`, `verifyEncoding_binds_invoice`.

**Statement shape.**

```lean
def verifyEncoding (sha256 : ByteArray → ByteArray)
    (sigCheck : PubKey → ByteArray → InvoiceSignature → Bool)
    (w : WireInvoice) : Prop :=
  w.Canonical ∧ sigCheck w.payee (signableDigest sha256 w) w.signature = true

/-- Message binding is the EUF-CMA consequence, not an axiom about SHA-256. -/
theorem verifyEncoding_binds_digest
    (hEuf : LnLean.Crypto.EufCma sigCheck)
    {w w' : WireInvoice} (h : verifyEncoding sha256 sigCheck w)
    (h' : verifyEncoding sha256 sigCheck w') (hkey : w.payee = w'.payee)
    (hsig : w.signature = w'.signature) :
    signableDigest sha256 w = signableDigest sha256 w' :=
  hEuf w.payee _ _ _ h.2 (by simpa [hkey, hsig] using h'.2)

/-- With a collision-resistant SHA-256 and the T1 injectivity lemma. -/
theorem verifyEncoding_binds_invoice
    (hsize : ∀ b : ByteArray, (sha256 b).size = 32)
    (hCR : LnLean.Crypto.CollisionResistant sha256)
    (hEuf : LnLean.Crypto.EufCma sigCheck)
    {w w' : WireInvoice} (h : verifyEncoding sha256 sigCheck w)
    (h' : verifyEncoding sha256 sigCheck w') (hkey : w.payee = w'.payee)
    (hsig : w.signature = w'.signature) : w = w' :=
  encoding_injective h.1 h'.1
    (hCR _ _ (hsize _) (hsize _)
      (verifyEncoding_binds_digest hEuf h h' hkey hsig))
```

**Hypotheses.** `EufCma sigCheck` (`LnLean/Crypto/Model.lean:71-75`) and
`CollisionResistant sha256` (`:56-57`) are explicit; the encoding injectivity
is proved from T1's field-coverage lemmas, not assumed. Different keys are out
of scope (key binding is C3).

**Non-vacuity.** `signatureOnlyInvoice` plus the always-accepting checker shows
that the old `verify` can be satisfied without any digest structure; it is the
negative witness that must be preserved. T2's positive witness must use a
concrete `sigCheck` that accepts the witness digest and rejects a mutated one.
Keep `signature_not_payment` (`InvoiceWireTargets.lean:1129-1136`) unchanged.

**Why faithful.** This is the theorem `LN-PM-002` currently approximates. It
makes the digest an encoding object and keeps unforgeability explicit. It does
not claim real secp256k1.

**Priority/fidelity/feasibility.** P0; high fidelity; medium feasibility
(depends on T1; the `EufCma` form already exists).

### T3 — 51-byte route-hint hop with `src_node_id` (P0/P1)

**Name.** `LnLean.Proofs.Payment.InvoiceRouteHints.RouteHintHop51`,
`encodeHop51`, `decodeHop51`, `decodeHop51_encodeHop51`, `encodeHop51_size`.

**Statement shape.**

```lean
structure RouteHintHop51 where
  srcNodeId : PubKey            -- 33 bytes
  channel : ShortChannelId      -- 8 bytes
  feeBaseMsat : Nat             -- 4 bytes
  feeProportionalMillionths : Nat -- 4 bytes
  cltvExpiryDelta : Nat         -- 2 bytes

def encodeHop51 (h : RouteHintHop51) : ByteArray := ...
theorem encodeHop51_size (h : RouteHintHop51) : (encodeHop51 h).size = 51 := ...
theorem decodeHop51_encodeHop51 {h : RouteHintHop51} (hh : h.Valid) :
    decodeHop51 (encodeHop51 h) = some h := ...
theorem decodeHop51_rejects_non_multiple {b : ByteArray}
    (h : b.size % 51 ≠ 0) : decodeHop51 b = none := ...
```

**Hypotheses.** `h.Valid` = 33-byte key plus the existing 32/32/16-bit bounds.
The 18-byte `RouteHintHop` and all its theorems are retained for compatibility;
they are explicitly reclassified as an abbreviated model.

**Non-vacuity.** A hop with `payeeBytes` (`33` bytes) and the existing
`witnessHop` numeric fields round-trips. The non-multiple rejection is
witnessed by a 50-byte array.

**Why faithful.** BOLT 11 `:155-160` and `de.rs:700-741` fix 51 bytes with a
leading 33-byte pubkey; the current 18-byte model cannot represent the field
the Server exposes as `node_id` (`decode_invoice.rs:48-64`).

**Priority/fidelity/feasibility.** P0 for the field-fidelity lane (the current
theorem is misleadingly named `encodeHop`); high fidelity; high feasibility
(additive codec).

### T4 — HRP amount grammar and canonicality (P1)

**Name.** `LnLean.Proofs.Payment.InvoiceHrp.Multiplier`,
`parseHrpAmount`, `renderHrpAmount`, `hrpAmountCanonical`,
`renderHrpAmount_canonical`, `parse_renderHrpAmount`,
`zero_amount_not_canonical`.

**Statement shape.**

```lean
inductive Multiplier | none | milli | micro | nano | pico

def parseHrpAmount (s : String) : Option (Option Msat) := ...
def renderHrpAmount (a : Option Msat) : String := ...
def hrpAmountCanonical (s : String) : Prop :=
  -- nonempty ⇒ positive decimal, no leading 0, pico last digit 0
  ...

theorem renderHrpAmount_canonical (a : Option Msat) :
    hrpAmountCanonical (renderHrpAmount a) := ...
theorem parse_renderHrpAmount (a : Option Msat) :
    parseHrpAmount (renderHrpAmount a) = some a := ...
theorem zero_amount_not_canonical : ¬ hrpAmountCanonical "0" := ...
theorem empty_amount_is_none : parseHrpAmount "" = some none := ...
```

**Hypotheses.** None beyond the decimal/multiplier grammar; the arithmetic
must show the pico-to-msat conversion is integral. The existing
`exists_valid_zero_amount` is **retained** and cited to show that the new
predicate, not `Valid`, carries positivity.

**Non-vacuity.** `"100n"` parses to `some (Msat.ofSat 10)` (10,000 msat);
`""` parses to `some none`; `"0"` is rejected by `hrpAmountCanonical` while
`parseHrpAmount "0"` may still return `some (some 0)` to mirror LDK's
permissive reader. That split is the point: reader permissiveness vs writer
canonicality.

**Why faithful.** BOLT 11 `:65-75` states the writer rules; `de.rs:420-439`
shows the reader's decimal/multiplier parse and overflow check. Do **not**
claim LDK rejects zero: `lib.rs:1376-1383` only rejects imprecise amounts.

**Priority/fidelity/feasibility.** P1; high fidelity; medium feasibility
(string/decimal reasoning, but no bech32 dependency).

### T5 — BOLT 9 feature pairing and minimal-width `9` field (P1)

**Name.** `LnLean.Proofs.Payment.InvoiceFeaturesBolt9.requiredBit`,
`optionalBit`, `modeledKnown`, `featurePairWellFormed`,
`decodeFeatureBits`, `bothBits_treated_required`,
`unknownRequired_rejected`, `featureBits_minimalWidth`.

**Statement shape.**

```lean
/-- BOLT 9: even bit = required, odd bit = optional. -/
def requiredBit (b : Nat) : Nat := 2 * b
def optionalBit (b : Nat) : Nat := 2 * b + 1

/-- The three modelled BOLT 11 bases: var_onion 8/9, payment_secret 14/15,
basic_mpp 16/17. -/
def knownFeatureBase : Nat → Prop
  | 4 => True | 7 => True | 8 => True | _ => False

/-- `known` is the full BOLT 9 table in a production decoder; the three
bases below are this lane's modelled subset. -/
def modeledKnown : Nat → Bool
  | 4 => true | 7 => true | 8 => true | _ => false

def featurePairWellFormed (known : Nat → Bool) (n : Nat) : Prop :=
  (∀ b, n.testBit (requiredBit b) = true →
          n.testBit (optionalBit b) = false) ∧
  (∀ b, n.testBit (requiredBit b) = true → known b = true) ∧
  (∀ b, n.testBit (optionalBit b) = true → known b = true)

theorem payment_secret_required_is_bit14 :
    requiredBit 7 = 14 ∧ optionalBit 7 = 15 := by decide
theorem variable_length_onion_required_is_bit8 :
    requiredBit 4 = 8 ∧ optionalBit 4 = 9 := by decide
theorem basic_mpp_required_is_bit16 :
    requiredBit 8 = 16 ∧ optionalBit 8 = 17 := by decide

/-- BOLT 9: if both bits in a pair are set, the receiver treats it as required. -/
def effectiveRequired (n : Nat) (b : Nat) : Bool :=
  n.testBit (requiredBit b) || n.testBit (optionalBit b)

theorem bothBits_treated_required (n : Nat) (b : Nat)
    (h : n.testBit (optionalBit b) = true) :
    effectiveRequired n b = true := by
  simp [effectiveRequired, h]

theorem unknownRequired_rejected (n : Nat)
    (h : n.testBit (requiredBit 9) = true) :  -- bit 18, not in modeledKnown
    ¬ featurePairWellFormed modeledKnown n := ...
```

**Hypotheses.** The core `InvoiceFeatures` is retained; add a separate
wire-level `FeatureVector` rather than reinterpreting the three booleans. The
decoder distinguishes required (even) from optional (odd), rejects a vector
that sets both bits of a pair, rejects unknown **required** bits, and ignores
unknown optional bits. This matches BOLT 9 `:64-80` and LDK's
`requires_feature`/`supports_feature` (`features.rs:320-332`).
`modeledKnown` is only the lane's three-feature subset; a production decoder
must instantiate `featurePairWellFormed` with the full BOLT 9 table, so the
`unknownRequired_rejected` theorem must not be read as "bits 18+ are invalid
in general".

**Non-vacuity.** A vector with bits 8, 14, and 16 set (all required) is
well-formed; a vector with bits 14 and 15 set (both in the payment-secret
pair) is rejected; a vector with only bit 15 set decodes as
supported-but-not-required. The old `featureBits_injective`
(`InvoiceWireTargets.lean:229-231`) is evidence only for the old collapsed
model, not for pairing.

**Why faithful.** BOLT 9 `:11-14` and `:64-80` define even=required,
odd=optional and forbid setting both; `features.rs:300-343` implements exactly
that split. BOLT 11 `:202-206` and `:303-326` require a BOLT 9-compliant `9`
field. The current model is not "wrong bit" so much as **collapsed**: it records
only the required bit and ignores the optional bit entirely.

**Priority/fidelity/feasibility.** P1; high fidelity; medium-high feasibility
(`Nat.testBit` and a width function are straightforward; minimal-width is
`Nat.log2`-style arithmetic).

### T6 — Optional `n` and payee resolution (P2, partially external)

**Name.** `LnLean.Proofs.Payment.InvoicePayee.PayeeSource`,
`resolvePayee`, `resolvePayee_prefers_explicit`,
`resolvePayee_recovered`, `recover_payee_external`.

**Statement shape.**

```lean
inductive PayeeSource where
  | explicit (pk : PubKey)
  | recovered (pk : PubKey)
  | absent

def resolvePayee : Option PubKey → Option PubKey → Option PayeeSource
  | some pk, _ => some (.explicit pk)
  | none, some pk => some (.recovered pk)
  | none, none => none

theorem resolvePayee_prefers_explicit (pk qk : PubKey) :
    resolvePayee (some pk) (some qk) = some (.explicit pk) := rfl
theorem resolvePayee_recovered (qk : PubKey) :
    resolvePayee none (some qk) = some (.recovered qk) := rfl
```

**Hypotheses.** The actual secp256k1 recovery is an **external** function
`recover : PubKey → ByteArray → InvoiceSignature → Option PubKey` supplied
with a soundness contract tying it to `sigCheck`. Do not prove that recovery
succeeds; prove only the resolution policy.

**Non-vacuity.** The explicit branch is `rfl`; the recovered branch is
witnessed by any 33-byte key. The `absent` branch must be shown reachable,
otherwise `get_payee_pub_key`'s `expect` is unjustified — this is a useful
negative witness.

**Why faithful.** `lib.rs:1514-1525` prefers `n` and otherwise recovers; BOLT
11 `:187-188` says recovery is the reason `n` is optional. The core model's
mandatory `payee` is the gap.

**Priority/fidelity/feasibility.** P2; high fidelity for the policy, but the
cryptographic branch is external; low-risk feasibility if kept policy-only.

### T7 — Fallback address decoder (P1)

**Name.** `LnLean.Proofs.Payment.InvoiceFallback.Fallback`,
`decodeFallback`, `decodeFallback_encodeFallback`,
`fallback_segwit_program_length`, `fallback_unknown_version_skipped`,
`first_understood_fallback`.

**Statement shape.**

```lean
inductive Fallback where
  | segwit (version : Fin 17) (program : ByteArray)
  | p2pkh (hash : ByteArray)
  | p2sh (hash : ByteArray)

def decodeFallback (version : Nat) (program : ByteArray) : Option Fallback :=
  if h : version ≤ 16 then
    if 2 ≤ program.size ∧ program.size ≤ 40 then
      some (.segwit ⟨version, by omega⟩ program) else none
  else if version = 17 then
    if program.size = 20 then some (.p2pkh program) else none
  else if version = 18 then
    if program.size = 32 then some (.p2sh program) else none
  else none

theorem fallback_unknown_version_skipped {v : Nat} {p : ByteArray}
    (h : 18 < v) : decodeFallback v p = none := ...
theorem first_understood_fallback (fs : List Fallback) :
    firstUnderstood fs = ... := ...
```

**Hypotheses.** Version is a 5-bit value; program lengths as above. The
"skip unknown" behavior is modeled as `none`, and the list-level
`firstUnderstood` ignores `none`, matching `filter_map` in
`lib.rs:1597-1611`.

**Non-vacuity.** A v0 20-byte program, a v1 32-byte program, a 20-byte P2PKH,
and a 32-byte P2SH all decode; a v19 value returns `none` (skipped), and a
v0 41-byte program is rejected (`de.rs:668-676`).

**Why faithful.** BOLT 11 `:189-192` plus `de.rs:660-693`. The current model
has only the numeric tag.

**Priority/fidelity/feasibility.** P1; high fidelity; medium-high feasibility
(additive inductive type and length arithmetic).

### T8 — Inbound claim/fail guards (P1 model extension, channel mechanics external)

**Name.** `LnLean.Proofs.Payment.InboundClaim.InboundPayment`,
`claimForId`, `failForId`, `claim_rejects_wrong_preimage`,
`claim_rejects_insufficient_amount`, `fail_rejects_unknown_id`,
`claim_rejects_terminal`.

**Statement shape.** Keep the new record separate from `PaymentSession` to
avoid changing existing MPP/keysend theorems:

```lean
inductive PaymentKind where
  | bolt11 (hash : PaymentHash)
  | other

structure InboundPayment where
  id : PaymentId
  kind : PaymentKind
  claimableAmount : Msat
  state : PaymentState := .pending

inductive ClaimError
  | unknownId | wrongKind | alreadySettled | wrongPreimage | amountTooLow

def claimForId (sha256 : Preimage → PaymentHash) (p : InboundPayment)
    (id : PaymentId) (amount : Msat) (pre : Preimage) :
    Except ClaimError InboundPayment :=
  match p.kind with
  | .other => .error .wrongKind
  | .bolt11 hash =>
      if p.id ≠ id then .error .unknownId
      else if p.state.isTerminal then .error .alreadySettled
      else if sha256 pre ≠ hash then .error .wrongPreimage
      else if amount.val < p.claimableAmount.val then .error .amountTooLow
      else .ok { p with state := .succeeded }

theorem claim_rejects_wrong_preimage {p : InboundPayment} {hash : PaymentHash}
    (hk : p.kind = .bolt11 hash) (hpend : p.state = .pending)
    (h : sha256 pre ≠ hash) :
    claimForId sha256 p p.id p.claimableAmount pre = .error .wrongPreimage := ...
theorem claim_rejects_insufficient_amount {p : InboundPayment} {hash : PaymentHash}
    (hk : p.kind = .bolt11 hash) (hpend : p.state = .pending)
    (hp : sha256 pre = hash) (h : amount.val < p.claimableAmount.val) :
    claimForId sha256 p p.id amount pre = .error .amountTooLow := ...
theorem claim_rejects_terminal {p : InboundPayment} {hash : PaymentHash}
    (hk : p.kind = .bolt11 hash) (h : p.state.isTerminal) :
    claimForId sha256 p p.id p.claimableAmount pre = .error .alreadySettled := ...

def failForId (p : InboundPayment) (id : PaymentId) :
    Except ClaimError InboundPayment :=
  if p.id ≠ id then .error .unknownId
  else match p.kind with
    | .other => .error .wrongKind
    | .bolt11 _ =>
        if p.state.isTerminal then .error .alreadySettled
        else .ok { p with state := .failed }

theorem fail_rejects_unknown_id {p : InboundPayment} {id : PaymentId}
    (h : p.id ≠ id) : failForId p id = .error .unknownId := ...
```

**Hypotheses.** `sha256` is the explicit C1 hash parameter, as in
`Invoice.preimageCommits` (`Invoice.lean:285-286`). The amount comparison uses
the Server's `claimable_amount_msat` semantics; it is a **Server-version**
datapoint (`bolt11_claim_for_id.rs:33-34`), not a pinned-Node one.

**Non-vacuity.** A witness with `pre` such that `sha256 pre = hash` (use the
toy hash from the existing `PrimitiveModel` witness) claims successfully; the
wrong-preimage and low-amount branches are `rfl`/`decide`. Keep
`settle_terminal` (`HTLC.lean:148-153`) as the coarse-state absorption result
and show the new record's terminal behavior separately.

**Why faithful.** `bolt11.rs:424-465` (known id, Bolt11 kind, SHA-256 preimage
equality), `:477-532` (fail store + backward fail), and
`e2e.rs:2079-2095`, `:2157-2162` (rejection cases). Actual HTLC acceptance and
`claim_funds`/`fail_htlc_backwards` channel effects remain external.

**Priority/fidelity/feasibility.** P1; high fidelity for the guard predicate;
medium feasibility as a new record, but **defer integration** into
`PaymentSession` and the channel layer to a separate lane.

### Target summary

| Target | Priority | Kind | Fidelity risk | Feasibility |
|---|---|---|---|---|
| T1 digest/data part | P0 | model extension | low (byte construction is explicit) | medium |
| T2 signature binds encoding | P0 | extension + explicit `EufCma`/C1 hypotheses | low if hypotheses stay explicit | medium |
| T3 51-byte route hop | P0 | model extension | low | high |
| T4 HRP amount grammar | P1 | model extension | medium (reader vs writer permissiveness) | medium |
| T5 BOLT 9 feature pairing | P1 | model extension | low | medium-high |
| T6 optional `n` / recovery policy | P2 | extension + external recovery | medium (external branch) | high for policy |
| T7 fallback decoder | P1 | model extension | low | medium-high |
| T8 inbound claim/fail | P1 | model extension + external channel effects | medium (Server/Node pin seam) | medium |

## 5. Assumptions, counterexamples, and non-vacuity risks

### Must be preserved verbatim

* `exists_valid_zero_amount` (`InvoiceProps.lean:210-212`) with
  `zeroAmountInvoice` (`:181-192`): `Valid` does **not** imply positivity.
  T4 adds a separate predicate; it must not rewrite `Valid`.
* `signature_not_payment` (`InvoiceWireTargets.lean:1129-1136`),
  `signature_only_separates_verify_from_payment` (`:1141-1147`), and
  `signatureOnly_verifies` (`:1108-1110`): signature acceptance under an
  unconstrained checker is not payment evidence. T2 must keep that checker as
  a negative witness, not assume `sigCheck` is always sound.
* `roundtrip_needs_canonicality` (`PhaseC3/InvoiceParser.lean:608-612`) and
  `malformed_parse_none` / `duplicateHash_parse_none`
  (`InvoiceWireTargets.lean:898-900`, `:922-924`): non-canonical widths and
  duplicate `p` are rejected; no round-trip theorem may drop the canonicality
  hypothesis.
* `preimage_unique_of_injective` (`InvoiceWireTargets.lean:986-988`) and
  `commitment_not_valid_preimage` (`:1071-1075`): uniqueness is conditional on
  injectivity; a 31-byte preimage can still satisfy the algebraic image
  relation. Do not turn this into unconditional SHA-256 injectivity.
* `waveD_d29_unconditional_claim_false` (`D29.lean:374-380`): the unconditional
  payment-secret claim is false; keep `acceptedBy` as a hypothesis.
* `settle_terminal` (`HTLC.lean:148-153`): terminal absorption is a coarse
  state theorem; T8 must not cite it as preimage/amount validation.

### Assumptions that must stay explicit

* **C1 (SHA-256 collision resistance)** — `CollisionResistant`
  (`Crypto/Model.lean:56-57`), only for 32-byte inputs; not global
  injectivity.
* **C3 (ECDSA EUF-CMA/key binding)** — `EufCma`
  (`Crypto/Model.lean:71-75`) is the message-binding consequence. Real
  secp256k1 recovery, key ownership, and unforgeability remain external.
* **Pin seam** — LDK Server's `claim_for_id` amount argument comes from Node
  `179b4b2`, not pinned Node `fa123fe`; do not present the amount check as a
  pinned-Node behavior. Cite `Cargo.toml:16` and the Server handler together.
* **Reader/writer asymmetry** — LDK's HRP reader accepts numeric `0`; BOLT 11
  imposes writer positivity/canonicality. T4 must model both sides separately,
  not assert that LDK rejects zero.

### Non-vacuity risks in the proposals

* T1/T2 must not define `signableDigest` as a constant or as `ByteArray.empty`.
  The witness must show two distinct canonical invoices with distinct
  pre-hash byte strings, and the positive signature witness must use a checker
  that is not `fun _ _ _ => true`.
* T3 must not silently reinterpret the existing 18-byte `encodeHop` as a
  51-byte encoding. Keep both names; the old one becomes an abbreviated model.
* T5 must not reinterpret the old collapsed codec as a full BOLT 9 vector.
  Keep `InvoiceFeatures` and add a separate `FeatureVector`; prove
  even=required/odd=optional and the "both bits set" normalization explicitly.
  Do not claim the old `featureBits` shows BOLT 9 pairing.
* T8 must not claim that `Except` guards imply channel-level safety. The
  `claim_funds`/`fail_htlc_backwards` effects, HTLC acceptance, and store
  atomicity are external.

### Contradiction to record, not repair silently

`InvoiceWireTargets.expiryField`/`minFinalCltvField` (fixed 8-byte
`encodeNat`, `:421-424`) contradict `PhaseC3.InvoiceParser.expiryWidth`
(minimum width, `:221-226`) and BOLT 11's minimum-`data_length` rule
(`refs/bolts/11-payment-encoding.md:180-186`). A future lane must pick one
canonical width and either re-prove or retire the old codec; do not add a
third width. The same applies to `featuresField` (fixed 4 bytes,
`InvoiceWireTargets.lean:425`) versus BOLT 11's minimum-width `9` field.

## 6. Wave-13 recommendation

**Recommendation: IMPLEMENT a bounded model-extension lane, and DEFER the
lifecycle integration; treat the cryptographic and channel layers as
external.**

* **Implement in wave 13/14 (bounded):** T1 + T2 as one lane
  (`InvoiceEncoding`), then T3 and T5 as field-fidelity additions, then T4 and
  T7 if budget allows. These are additive, source-grounded, and can reuse the
  existing `WireInvoice`, `witnessWire`, and `RouteHintHop` machinery.
* **Defer:** T8's integration into `PaymentSession`/channel state. The guard
  predicate can be implemented as a standalone `InboundClaim` module, but
  claiming it as end-to-end receive safety would overstate the model. T6's
  recovery branch should stay policy-only until a concrete secp256k1 bridge
  exists.
* **External/human barrier:** real bech32 library equivalence, real SHA-256
  collision resistance, real ECDSA recovery/EUF-CMA/key binding, node-level
  invoice interop, and production `claim_funds`/`fail_htlc_backwards` channel
  mechanics. None should become an axiom; each is an explicit hypothesis or a
  documented gap.
* **Do not** strengthen `Invoice.Valid` or `Invoice.verify` in place, and do
  not delete the zero-amount, signature-separation, or canonicality
  counterexamples. New predicates (`hrpAmountCanonical`,
  `verifyEncoding`, `featurePairWellFormed`, `InboundPayment`) keep the old
  results intact and make the new assumptions visible.
* **Top target:** T2 (`verifyEncoding_binds_invoice`), built on T1. It closes
  the largest semantic hole in `LN-PM-002` while keeping EUF-CMA/C1 explicit.

## 7. Evidence and commands

Read-only inspection only. No Lean, docs, scripts, tests, vendor, or other lane
reports were edited; no branch, commit, or push was made; no full-tree build
was run.

Pins verified from the pinned clones:

```sh
git -C /tmp/opencode/ldk-refs/ldk-node rev-parse HEAD
# fa123fed131e27ecc420b77fa7086fcf1ddaebb8
git -C /tmp/opencode/ldk-refs/ldk-server rev-parse HEAD
# c17dc11dde38f88c53457039ddf30c6b90a63ba2
rg -n 'ldk-node = ' /tmp/opencode/ldk-refs/ldk-server/ldk-server/Cargo.toml
# rev = "179b4b263762155a7ff515ddad7e757a80807fd5"
```

Lean surface inspected:

```sh
rg -n 'structure Valid|def verify|def amountSatisfies|def isExpired|def recoveryIdInRange' \
  LnLean/Payment/Invoice.lean
rg -n 'theorem |def |structure ' LnLean/Proofs/Payment/InvoiceWireTargets.lean
rg -n 'theorem |def |structure ' LnLean/Proofs/Payment/InvoiceProps.lean
rg -n 'theorem |def |structure ' LnLean/Proofs/PhaseC3/InvoiceParser.lean
rg -n 'theorem |def |structure ' LnLean/Proofs/PhaseC2/InvoiceBinding.lean
rg -n 'structure Invoice|def Invoice.Consistent' LnLean/Security/Invariants.lean
rg -n 'structure PaymentSession|def settle|def preimageCommits' LnLean/Payment/HTLC.lean
rg -n 'LN-PM-00[1-7]' LnLean/Proofs/Obligations.lean
```

LDK behavior inspected:

```sh
rg -n 'fn claim_for_id|fn fail_for_id|fn send_internal|send_using_amount|reuse' \
  /tmp/opencode/ldk-refs/ldk-node/src/payment/bolt11.rs
sed -n '400,540p' /tmp/opencode/ldk-refs/ldk-node/src/payment/bolt11.rs
sed -n '1,120p' /tmp/opencode/ldk-refs/ldk-server/ldk-server/src/api/decode_invoice.rs
sed -n '1,60p' /tmp/opencode/ldk-refs/ldk-server/ldk-server/src/api/bolt11_receive.rs
sed -n '1,60p' /tmp/opencode/ldk-refs/ldk-server/ldk-server/src/api/bolt11_send.rs
sed -n '1,60p' /tmp/opencode/ldk-refs/ldk-server/ldk-server/src/api/bolt11_claim_for_id.rs
sed -n '1,50p' /tmp/opencode/ldk-refs/ldk-server/ldk-server/src/api/bolt11_fail_for_id.rs
sed -n '2060,2175p' /tmp/opencode/ldk-refs/ldk-server/e2e-tests/tests/e2e.rs
```

Normative/supplementary sources inspected:

```sh
rg -n 'fn hash_from_parts|fn signable_hash|fn check_field_counts|fn check_payment_secret|fn check_amount|fn check_feature_bits|fn check_signature|fn from_signed|fn expires_at|fn would_expire|fn fallback_addresses|fn route_hints|fn amount_milli_satoshis|recover_payee' \
  refs/rust-lightning/lightning-invoice/src/lib.rs
rg -n 'CheckedHrpstring|fn from_str|51|Fallback|RecoveryId' \
  refs/rust-lightning/lightning-invoice/src/de.rs
rg -n 'impl Display|with_checksum' refs/rust-lightning/lightning-invoice/src/ser.rs
rg -n 'define_feature!|PaymentSecret,|BasicMPP,|VariableLengthOnion,' \
  refs/rust-lightning/lightning-types/src/features.rs
sed -n '45,210p' refs/bolts/11-payment-encoding.md
sed -n '300,365p' refs/bolts/11-payment-encoding.md
```

Catalog/traceability cross-checks:

```sh
sed -n '355,405p' LnLean/Proofs/Obligations.lean
rg -n 'LN-PM-001|LN-PM-002|LN-PM-003|LN-PM-007' \
  docs/THEOREM-INDEX.md docs/TRACEABILITY.md
rg -n 'S11-PAY-INVOICE|invoice' agents/TODO-REPAIR.md docs/OPEN-ISSUES.md
```
