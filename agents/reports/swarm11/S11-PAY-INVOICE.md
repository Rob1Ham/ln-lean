# S11-PAY-INVOICE — canonical BOLT 11 invoice wire targets

**Lane:** `S11-PAY-INVOICE`  
**Branch:** `repair/integrated`  
**Module:** `LnLean/Proofs/Payment/InvoiceWireTargets.lean` (new, 1147 lines)  
**Report:** `agents/reports/swarm11/S11-PAY-INVOICE.md`  
**Catalog context:** `LN-PM-001`–`LN-PM-006`; recommendation for a new
wire-codec row in §7.

## 1. Scope

This lane owns exactly one new Lean module and this report.  It does not edit
root imports, the obligation catalog, traceability, audit lists, docs,
scripts, or tests, and it does not commit or push.  The module imports only
`LnLean.Payment.Invoice` and `LnLean.Wire.BigSize`; it is self-contained and
builds directly as a Lake target.

The module adds a **pre-bech32** serialization layer for the semantic BOLT 11
invoice model:

1. canonical scalar codecs for the network prefix, amount, fixed-width
   integers, feature bitfield, and a route-hint hop;
2. a canonical field-list record with the fixed order
   `p, s, n, x, c, f, r*`;
3. `print`/`parse` round trip and injectivity for canonical wire invoices;
4. projection to and from the core `LnLean.Payment.Invoice` record;
5. payment-hash/payment-secret binding through the codec;
6. an exact hash-image counterexample and a signature-vs-payment
   counterexample;
7. concrete valid and malformed witnesses.

It does **not** model bech32/charset encoding, the checksum, HRP string
parsing, the BOLT 11 signable-digest bytes, recoverable ECDSA, UTF-8
description encoding, amount multipliers/decimal rendering, or cryptographic
preimage resistance.  `parse`/`print` operate on a canonical field list, not
on an encoded invoice string.

## 2. Model design

### 2.1 Header and fields

`WireHeader` (line 570) carries the HRP token, optional millisatoshi amount,
35-bit timestamp, and opaque 65-byte signature.  `WireRecord` (line 578) is a
header plus a `List WireField`; `WireField` (line 395) is a numeric BOLT tag
plus an opaque byte payload.

The fixed field order is defined by `printFields` (line 500):

```text
p, s, n, x, c, f, r*
```

with tags `p = 1`, `s = 16`, `n = 19`, `x = 6`, `c = 24`, `f/9 = 5`, and
`r = 3`.  `parseFields` (line 519) accepts exactly that order: tags and
fixed lengths are checked by the per-field parsers, the first six fields are
mandatory, and every remaining field must parse as an `r` hop.  Duplicate or
extra non-`r` fields therefore fail.

`WireInvoice` (line 586) contains every core invoice field except the
description, plus a flat list of route hints.  The description is supplied to
`toInvoice` as an explicit argument.  `WireInvoice.Canonical` (line 608) is
the serialization premise: 32-byte `p` and `s`, 33-byte `n`, 65-byte
signature, amount within `Msat.MAX`, timestamp within `MAX_TIMESTAMP`, 64-bit
bounds on `x` and `c`, and every route hint valid.

### 2.2 Scalar codecs

* Prefixes are the four modelled BOLT 11 network prefixes.  Unknown prefixes
  are rejected by `networkOfPrefix`.
* `encodeNat`/`decodeNat` are canonical 8-byte big-endian integers.
* `encodeAmount` is empty for an absent amount and eight bytes for a present
  amount.
* `encodeFeatures` is a canonical four-byte bitfield using bit 8
  (`var_onion_optin`), bit 14 (`payment_secret`), and bit 16 (`basic_mpp`).
  BOLT 9's optional/mandatory pairing is collapsed to one bit per modelled
  boolean and is a documented gap.
* `RouteHintHop` is a **flat additive hop model**:
  `channel : ShortChannelId`, `feeBaseMsat`, `feeProportionalMillionths`,
  `cltvExpiryDelta`.  The canonical hop payload is 18 bytes,
  `scid(64) | fee_base(32) | fee_prop(32) | cltv(16)`.

**Important route-hint boundary.**  This 18-byte hop is not the BOLT 11
51-byte `r` hop encoding: the BOLT hop also carries the 33-byte node pubkey,
and BOLT 11 groups hops into route hints with preference ordering.  This lane
proves the internal codec for a hop record and a flat hop list only.  It does
not claim exact BOLT `r` byte compatibility, route grouping, or preference
ordering.

### 2.3 Projection to the core model

`ofInvoice` (line 731) embeds a core invoice with no route hints.  `toInvoice`
(line 740) projects back with an explicit description.  `DescriptionShape`
(line 755) records only the wire-relevant condition: a hash description has a
32-byte digest; a direct description is unconstrained because UTF-8 is out of
scope.

## 3. Key results

| Result | Name | Line |
|---|---|---:|
| Prefix round trip | `networkOfPrefix_prefixOf` | 144 |
| Prefix injectivity | `prefixOf_injective` | 150 |
| `Nat` codec round trip | `decodeNat_encodeNat` | 164 |
| Feature payload round trip | `decodeFeatures_encodeFeatures` | 244 |
| Short-channel-id round trip | `scidOfU64_toU64` | 283 |
| Hop codec round trip | `decodeHop_encodeHop` | 377 |
| Field-list round trip | `parseFields_printFields` | 557 |
| Full wire round trip | `parse_print` | 660 |
| Print injectivity | `print_injective` | 679 |
| Projection round trip | `toInvoice_ofInvoice` | 749 |
| Wire projects to valid core invoice | `toInvoice_valid` | 762 |
| Core invoice embeds canonically | `ofInvoice_canonical` | 780 |
| Concrete witness round trip | `witness_parse` | 869 |
| Concrete witness projects valid | `witness_toInvoice_valid` | 873 |
| 31-byte `p` is rejected | `malformed_parse_none` | 898 |
| Duplicate `p` is rejected | `duplicateHash_parse_none` | 922 |
| Preimage uniqueness under injectivity | `preimage_unique_of_injective` | 986 |
| Secret binding survives codec | `wire_paymentSecret_binding` | 1014 |
| Hash binding survives codec | `wire_paymentHash_binding` | 1020 |
| Hash collision without injectivity | `constantZeroHash_collision` | 1053 |
| Commitment is not preimage validity | `commitment_not_valid_preimage` | 1071 |
| Signature-only invoice verifies | `signatureOnly_verifies` | 1108 |
| Signature-only invoice has no preimage | `signatureOnly_no_preimage` | 1115 |
| Signature acceptance is not payment | `signature_not_payment` | 1129 |
| Bundled signature/payment separation | `signature_only_separates_verify_from_payment` | 1141 |

### 3.1 Canonical round trip

`parseFields_printFields` (line 557) is the field-level serialization
theorem.  `parse_print` (line 660) is the full record theorem:

```text
w.Canonical -> parse (print w) = some w
```

`print_injective` (line 679) derives injectivity from the round trip.
`parse_print_paymentHash`, `parse_print_paymentSecret`, `parse_print_payee`,
`parse_print_expiry`, `parse_print_features`, and
`parse_print_routeHints` (lines 686–721) project each parsed field back to the
printed value.

The parser is deliberately exact: the six fixed fields must be present in
order, fixed lengths are checked, and everything after them must be an `r`
field.  It is not a full validating parser: `parse` does not re-check the
amount bound, the 35-bit timestamp, or the signature length.  Those are
conditions in `WireInvoice.Canonical`, which is an explicit hypothesis of the
round-trip theorem rather than an output of `parse`.

### 3.2 Projection

`toInvoice_ofInvoice` (line 749) proves the core embedding is a section of
the projection.  `toInvoice_valid` (line 762) takes canonical wire data plus
`DescriptionShape d` and proves `(toInvoice w d).Valid`.  This is structural
validity only; no signature check is performed or implied.

`ofInvoice_canonical` (line 780) requires two explicit `Nat` bounds,
`expiry < 2^64` and `minFinalCltvExpiry < 2^64`, because the core model stores
them as unbounded `Nat`.  `parse_print_ofInvoice` and
`toInvoice_parse_print_ofInvoice` (lines 791, 798) lift the round trip through
the embedding.

### 3.3 Binding and the hash-image boundary

`invoiceCommits_iff` (line 971) is definitional equality:
`InvoiceCommits hash p i ↔ hash p = i.paymentHash`.  `preimage_determines_hash`
(line 978) proves a preimage determines its hash without any cryptographic
hypothesis.  `preimage_unique_of_injective` (line 986) proves uniqueness of
the preimage **only under `Function.Injective hash`**.  No SHA-256 or
computational security claim is made.

`paymentSecret_eq_iff_bytes` and `paymentHash_eq_iff_bytes` (lines 999, 1006)
identify record equality with byte equality.  `wire_paymentSecret_binding` and
`wire_paymentHash_binding` (lines 1014, 1020) show the parsed record carries
the printed secret/hash.

## 4. Counterexamples and witnesses

### 4.1 Concrete valid witness

`witnessWire` (line 838) is mainnet, 250000 sat, timestamp 1700000000,
32-byte `p`/`s`, 33-byte payee, 65-byte signature, expiry 3600, min final
CLTV 18, feature bits `paymentSecretRequired = true`,
`basicMpp = false`, `variableLengthOnion = true`, and one route hint
(`witnessHop`, line 827: block 800000, tx 3, output 1, 1000 msat base,
100 ppm, 144-block CLTV).

`witnessWire_canonical` (line 853) proves canonicality;
`witness_parse` (line 869) proves the full round trip; and
`witness_toInvoice_valid` (line 873) proves the projection with a hashed
description digest is a valid core invoice.  `witness_signature_size`
(line 879) records the 65-byte signature.

### 4.2 Malformed witnesses

* `malformedWire` (line 888) is the witness with a 31-byte `p`.
  `malformedWire_not_canonical` (line 891) proves it violates canonicality,
  and `malformed_parse_none` (line 898) proves
  `parse (print malformedWire) = none`.
* `duplicateHashRecord` (line 915) appends a second `p` field after the
  canonical fields.  `duplicateHash_parse_none` (line 922) proves parsing
  fails, because the extra `p` is not a valid `r` tail.  The helper
  `parseRouteHintField_paymentHashField` (line 905) and `parseHints_two_bad`
  (line 909) expose the rejection mechanism.

### 4.3 Hash-image counterexamples

`constantZeroHash` (line 1038) is the constant function returning
`zeroPaymentHash`.  It is a legitimate `Preimage → PaymentHash` function but
is not injective:

* `constantZeroHash_not_injective` (line 1045);
* `constantZeroHash_collision` (line 1053): two distinct preimages,
  `0x00…` and `0x01…`, commit to the same image;
* `shortPreimage_not_valid` (line 1065) and
  `commitment_not_valid_preimage` (line 1071): a 31-byte preimage still
  satisfies the algebraic commitment relation, so commitment does not imply
  canonical preimage validity.

These are exact algebraic counterexamples, not claims about SHA-256.

### 4.4 Signature is not payment

`signatureOnlyInvoice` (line 1080) is structurally valid with payment hash
`onePaymentHash` (`0x01…`).  `signatureOnly_verifies` (line 1108) proves

```text
Invoice.verify (fun _ => ByteArray.empty) (fun _ _ _ => true) signatureOnlyInvoice
```

using an always-accepting checker and a constant digest.  Because
`constantZeroHash` always returns `zeroPaymentHash` (`0x00…`), which differs
from `onePaymentHash`, `signatureOnly_no_preimage` (line 1115) proves no
preimage commits.  `signature_not_payment` (line 1129) existentializes the
digest and checker; `signature_only_separates_verify_from_payment`
(line 1141) bundles the verified invoice with the absence of payment
evidence.

This separates the model's `Invoice.verify` predicate from
`InvoiceCommits`.  It does **not** claim a real ECDSA verifier would accept a
forged signature, and it does not prove signature unforgeability.  The
checker is an unconstrained parameter, exactly as in `Invoice.verify`.

## 5. Assumptions and explicit limitations

* **Canonicality is an input.**  `parse_print` and `toInvoice_valid` require
  `WireInvoice.Canonical`.  The parser enforces field order, tags, and fixed
  payload lengths, but `parse` itself does not enforce amount/timestamp/
  signature canonicality.
* **Injectivity for preimage uniqueness.**  `preimage_unique_of_injective`
  requires `Function.Injective hash`.  Without it, the constant-zero hash
  gives a collision.  No computational preimage resistance is claimed.
* **Description is out of band.**  `toInvoice` takes `InvoiceDescription`
  explicitly.  Direct-description UTF-8 validation is not modelled; only the
  32-byte `h` digest condition is encoded in `DescriptionShape`.
* **Route hints are a flat hop list.**  The 18-byte hop codec omits the BOLT
  11 hop pubkey (33 bytes) and does not model route grouping or preference
  order.  Do not read these theorems as exact BOLT `r` byte compatibility.
* **No bech32/checksum/digest.**  The HRP is a token, not a decoded bech32
  string.  The signable digest and the encoded invoice string are not
  constructed.
* **No cryptographic signature claim.**  `Invoice.verify` keeps the checker
  and digest as parameters.  The signature counterexample is about the model
  predicate only.
* **Core `Nat` bounds.**  `ofInvoice_canonical` needs explicit 64-bit bounds
  on `expiry` and `minFinalCltvExpiry` because the core model does not bound
  them.

## 6. Build and audits

Build command (lane requirement):

```text
cd /home/ubuntu/ln-lean-repair
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Proofs.Payment.InvoiceWireTargets
```

Result: **success**, `Build completed successfully (8 jobs).`  RC `0`; no
errors or warnings surfaced by the build.

Forbidden-token scan on the new module:

```text
grep -nE 'sorry|axiom|admit|native_decide|unsafe|implemented_by' \
  LnLean/Proofs/Payment/InvoiceWireTargets.lean
```

Result: **0 hits** (`NO_FORBIDDEN_TOKENS`).

Axiom audit: every one of the **74** public theorem declarations was audited
with `#print axioms` in a temporary file importing the module.  All 74
printed successfully.  Observed sets are subsets of
`{propext, Quot.sound, Classical.choice}`:

| Axiom set | Count |
|---|---:|
| none | 18 |
| `{propext}` | 20 |
| `{propext, Quot.sound}` | 35 |
| `{propext, Classical.choice, Quot.sound}` | 1 |

The only theorem using `Classical.choice` is `prefixOf_injective` (line 150).
No unexpected axioms or constants were observed.

Representative audit results:

```text
parse_print                         [propext, Quot.sound]
print_injective                     [propext, Quot.sound]
toInvoice_valid                     []
toInvoice_ofInvoice                 []
wire_paymentSecret_binding          [propext, Quot.sound]
wire_paymentHash_binding            [propext, Quot.sound]
witness_parse                       [propext, Quot.sound]
malformed_parse_none                [propext]
duplicateHash_parse_none            [propext, Quot.sound]
signature_not_payment               [propext, Quot.sound]
signature_only_separates_verify_from_payment
                                    [propext, Quot.sound]
```

## 7. Recommended catalog targets

These are recommendations only; no catalog, traceability, or audit file was
edited by this lane.

* **`LN-PM-001` (payment hash/preimage relation):**
  `parse_print`, `parse_print_paymentHash`, `wire_paymentHash_binding`,
  `preimage_unique_of_injective`, `preimage_determines_hash`.
* **`LN-PM-002` (verification vs. payment evidence):**
  `signature_not_payment`, `signatureOnly_verifies`,
  `signatureOnly_no_preimage`,
  `signature_only_separates_verify_from_payment`.
* **`LN-PM-003` (payment secret binding):**
  `paymentSecret_eq_iff_bytes`, `parse_print_paymentSecret`,
  `wire_paymentSecret_binding`, `toInvoice_valid`.
* **New wire-codec row (suggested):**
  `parseFields_printFields`, `parse_print`, `print_injective`,
  `witness_parse`, `malformed_parse_none`, `duplicateHash_parse_none`,
  `decodeHop_encodeHop`.

The route-hint results should be catalogued under the new wire row with the
flat-hop/18-byte limitation stated explicitly; they should not be attached to
a claim of exact BOLT 11 `r` byte encoding.

## 8. Integration notes

* The module builds directly; no root import was added, per lane rules.
* Integration only needs an import of
  `LnLean.Proofs.Payment.InvoiceWireTargets` from the appropriate root or
  aggregate module in a later integration lane.
* The module has no dependency on the crypto layer or on the existing
  `InvoiceProps`/`InvoiceParser` modules beyond the core invoice model and
  `BigSize` byte helpers.
* File length is 1147 lines, above the soft 400–750 target, because the lane
  also carries a 74-theorem inventory, concrete witnesses, and the
  signature/hash counterexamples.

## 9. Theorem inventory

All names below are in namespace
`LnLean.Proofs.Payment.InvoiceWireTargets` unless shown with a `WireInvoice.`
prefix.  There are **74** public theorem declarations.

### §1 scalar codecs and helper arithmetic

| Line | Theorem |
|---:|---|
| 120 | `div_add_mul` |
| 126 | `mod_add_mul` |
| 144 | `networkOfPrefix_prefixOf` |
| 150 | `prefixOf_injective` |
| 164 | `decodeNat_encodeNat` |
| 186 | `decodeAmount_encodeAmount_none` |
| 193 | `decodeAmount_encodeAmount_some` |
| 218 | `featureBits_lt` |
| 223 | `featuresOfBits_featureBits` |
| 229 | `featureBits_injective` |
| 244 | `decodeFeatures_encodeFeatures` |

### §2 route-hint hop codec

| Line | Theorem |
|---:|---|
| 283 | `scidOfU64_toU64` |
| 323 | `hopPacked_lt` |
| 333 | `decode_hopPacked` |
| 372 | `encodeHop_size` |
| 377 | `decodeHop_encodeHop` |

### §3 field parsers and field-list codec

| Line | Theorem |
|---:|---|
| 445 | `parsePaymentHashField_print` |
| 450 | `parsePaymentSecretField_print` |
| 455 | `parsePayeeField_print` |
| 460 | `parseNatField_print` |
| 467 | `parseFeaturesField_print` |
| 472 | `parseRouteHintField_print` |
| 545 | `parseHints_print` |
| 557 | `parseFields_printFields` |

### §4 full record codec

| Line | Theorem |
|---:|---|
| 619 | `WireInvoice.fieldsOf_canonical` |
| 653 | `parseHeader_printHeader` |
| 660 | `parse_print` |
| 679 | `print_injective` |
| 686 | `parse_print_paymentHash` |
| 693 | `parse_print_paymentSecret` |
| 700 | `parse_print_payee` |
| 707 | `parse_print_expiry` |
| 714 | `parse_print_features` |
| 721 | `parse_print_routeHints` |

### §5 core-model projection

| Line | Theorem |
|---:|---|
| 749 | `toInvoice_ofInvoice` |
| 762 | `toInvoice_valid` |
| 780 | `ofInvoice_canonical` |
| 791 | `parse_print_ofInvoice` |
| 798 | `toInvoice_parse_print_ofInvoice` |

### §6 concrete witness

| Line | Theorem |
|---:|---|
| 819 | `hashBytes_size` |
| 820 | `secretBytes_size` |
| 821 | `payeeBytes_size` |
| 822 | `sigBytes_size` |
| 823 | `descriptionDigest_size` |
| 833 | `witnessHop_valid` |
| 853 | `witnessWire_canonical` |
| 869 | `witness_parse` |
| 873 | `witness_toInvoice_valid` |
| 879 | `witness_signature_size` |

### §7 malformed witnesses

| Line | Theorem |
|---:|---|
| 885 | `shortHashBytes_size` |
| 891 | `malformedWire_not_canonical` |
| 898 | `malformed_parse_none` |
| 905 | `parseRouteHintField_paymentHashField` |
| 909 | `parseHints_two_bad` |
| 922 | `duplicateHash_parse_none` |

### §8 hash/secret binding and hash-image counterexamples

| Line | Theorem |
|---:|---|
| 971 | `invoiceCommits_iff` |
| 978 | `preimage_determines_hash` |
| 986 | `preimage_unique_of_injective` |
| 992 | `no_preimage_iff_not_in_image` |
| 999 | `paymentSecret_eq_iff_bytes` |
| 1006 | `paymentHash_eq_iff_bytes` |
| 1014 | `wire_paymentSecret_binding` |
| 1020 | `wire_paymentHash_binding` |
| 1033 | `zeroPaymentHash_ne_one` |
| 1040 | `zeroBytes_ne_oneBytes` |
| 1045 | `constantZeroHash_not_injective` |
| 1053 | `constantZeroHash_collision` |
| 1065 | `shortPreimage_not_valid` |
| 1071 | `commitment_not_valid_preimage` |

### §9 signature vs. payment

| Line | Theorem |
|---:|---|
| 1094 | `signatureOnlyInvoice_valid` |
| 1108 | `signatureOnly_verifies` |
| 1115 | `signatureOnly_no_preimage` |
| 1129 | `signature_not_payment` |
| 1141 | `signature_only_separates_verify_from_payment` |

## 10. Completion statement

The lane artifacts are complete and build cleanly.  The claims are sound at
the stated boundary: a pre-bech32 canonical field-list codec, conditional
hash injectivity, and a model-level separation of signature acceptance from
payment evidence.  The module does not claim exact BOLT 11 route-hint byte
encoding, bech32/checksum/digest construction, or computational security.
