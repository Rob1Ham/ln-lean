# R11 — BOLT 12 offers, invoice requests, refunds, and payer proofs
**Status:** read-only review
**Pins:** LDK Node `fa123fed131e27ecc420b77fa7086fcf1ddaebb8`, LDK Server `c17dc11dde38f88c53457039ddf30c6b90a63ba2`
**Review branch:** `repair/integrated` (no branch, commit, or non-report file changes made)

## 1. Scope and current Lean surface

This lane covers the BOLT 12 offer / invoice-request / invoice / payer-proof
surface, plus the LDK refund extension, as exposed by LDK Node and LDK Server.
It does not re-review BOLT 11 encoding (`LN-PM-001`–`007`), BOLT 4 onion
processing (`R09`), route blinding as a BOLT 4 wire format, async
payments/static invoices, trampoline, or unified BOLT 12 (lane `R12`). Those
surfaces appear only where they constrain a BOLT 12 claim.

The short verdict is: **there is no BOLT 12 model in `ln-lean` at all.** There
is no `Offer`, `InvoiceRequest`, `Bolt12Invoice`, `PayerProof`, `Refund`, or
BOLT 12 Merkle-tree declaration. `rg` over `LnLean/` finds only the English
word "Offered" in BOLT 3 HTLC contexts. The documentation is explicit:

* `docs/SCOPE.md:24` — "BOLT 12 offers and blinded paths beyond a stub
  interface" are out of scope. No stub interface exists anywhere in the tree.
* `docs/ASSUMPTIONS.md:144` — "BOLT 12: offers (out of scope for this
  scaffold, listed as future work)."
* `LnLean/Payment/Invoice.lean:98` — "BOLT 12 offers are out of scope."

`docs/ANCHORS-GENERATED.md:131` nevertheless lists
`LnLean/Payment/Invoice.lean` as a `BOLT 12` anchor. That is a **false
positive**: the only BOLT 12 token in that file is the out-of-scope sentence
at `:98`. It is not coverage and must not be cited as such.

The current claim surface is 51 catalog rows
(`docs/THEOREM-INDEX.md`), none of which is BOLT 12. The payment rows
`LN-PM-001`–`007` (`THEOREM-INDEX.md:74-80`) are BOLT 11 or BOLT 11
field-list claims. In particular:

* `LN-PM-002` uses a **65-byte recoverable-ECDSA** `InvoiceSignature`
  (`Invoice.lean:163-169`), not BOLT 12's 64-byte BIP-340 `bip340sig`.
* `LN-PM-007` is a pre-bech32 BOLT 11 field-list model; it does not cover
  `lno`/`lnr`/`lnp` or the BOLT 12 TLV streams.
* `LN-PM-003` is a BOLT 4 final-payload / BOLT 11 payment-secret claim, not a
  BOLT 12 invoice-request or invoice claim.

### 1.1 Reusable substrate only

| Substrate | Location | What it gives / what it does not |
|---|---|---|
| Generic TLV records and streams | `LnLean/Wire/TLV.lean:36-96` | `TLVRecord`, `TLVStream`, BigSize framing, `Sorted`/`Unique`/`WellFormed`. No known-type length validation, no even/odd policy, no BOLT 12 schema (`TLV.lean:7-12`, `:25-28`). |
| TLV parser | `LnLean/Wire/TLV.lean:190-215` | Total `Option`-valued `decodeTLV`. The full parser round-trip is **not** proved (`:7-12`). |
| Hash / preimage | `LnLean/Crypto/Hash.lean:38-41`, `:54-57` | `opensTo M ph pre := digest32 (M.sha256 pre.bytes) = ph.bytes`; `opensTo_iff_sha256`. This is reusable for `invoice_payment_hash`, but it is only a hash-lock relation. |
| Primitive model | `LnLean/Crypto/Model.lean:101-125` | C1 `CollisionResistant` is quantified over **32-byte inputs only** (`:52-57`). C4 `EufCma` means one signature cannot verify for two distinct messages under one key (`:68-73`); it does not prove key ownership or unforgeability. |
| BIP-340 tagged hash | `LnLean/Proofs/Crypto/SchnorrProps.lean:254-262` | `taggedHash` and `taggedHash_size`. No BOLT 12 tag table, no Merkle tree. |
| Tagged-hash domain separation | `LnLean/Proofs/Crypto/Sha256Props.lean:265-329` | `tagPrefix_width`, `tagPrefix_separates_hashed_tags`, `taggedHash_collision_witness`. The last is a reduction requiring an explicit SHA-256 collision; it is not an unconditional separation theorem. |
| Schnorr message binding | `LnLean/Proofs/Crypto/SchnorrProps.lean:190-196` | `schnorr_message_bound` under `AssumesEufCma`. `acceptsAll_not_eufCma` (`:219-230`) shows formatting laws alone are insufficient. |
| BOLT 11 invoice record | `LnLean/Payment/Invoice.lean:197-210`, `:252-272` | A BOLT 11 record and a **projection** `signature_valid` over an unconstrained `sigCheck`. Not a BOLT 12 invoice, not a signature-soundness theorem. |
| BOLT 11 field codec | `LnLean/Proofs/Payment/InvoiceWireTargets.lean` | Pre-bech32 BOLT 11 field-list parse/print; `signatureOnly_verifies` / `signatureOnly_no_preimage` (`:1108-1145`) keep signature validity separate from payment. |
| Structural blinded path | `LnLean/Proofs/Routing/RouteBlindingProps.lean:437-487` | Creator-side `BlindedHop`/`BlindedPath` with `hops : List BlindedHop`. It has no `num_hops` wire field, no ECDH, no onion-message path, and no reply-path semantics. |
| Core wire types | `LnLean/Basic/Core.lean:162-187`, `:195-199` | `PubKey.Valid` is only a 33-byte size check; `SchnorrSig.Valid` is only a 64-byte size check; `ChainHash` is a 32-byte holder. None validates a secp256k1 point or a real signature. |

Consequently, the only honest status for every BOLT 12-specific behavior in
this report is **missing** or **unmodelled/external**, with a small number of
**partially covered** primitive-level rows. The rest of this document supplies
the LDK/spec datapoints, the gap matrix, and a bounded target set.

## 2. LDK datapoints (with `file:line`)

All LDK citations are read-only inspection of the pinned clones. Two
provenance caveats matter:

* LDK Node pins rust-lightning `d7a980641c6325ddda5072a0f470ef8392676cf5`
  (`ldk-node/Cargo.toml:89-98`), while the local `refs/rust-lightning` clone is
  `fe4900930c6bd5786ec4203274d7cf312776a5a6`. The rust-lightning line anchors
  below are therefore **behavioral anchors, not exact dependency line
  numbers**.
* LDK Server pins LDK Node
  `179b4b263762155a7ff515ddad7e757a80807fd5`
  (`ldk-server/Cargo.toml:16`), not the `fa123fed` checkout. The server's
  e2e tests exercise that dependency. The server API surface is stable for the
  behaviors cited, but the distinction is recorded rather than hidden.

### 2.1 Offer creation and send-side amount/quantity (LDK Node)

* `ldk-node/src/payment/bolt12.rs:233-267` — `receive_inner(amount_msat,
  description, expiry_secs, quantity)`. An optional `expiry_secs` is converted
  to an **absolute** expiry using `SystemTime::now()` (`:241-246`);
  `offer_builder.amount_msats(amount_msat).description(...)` sets the amount
  and description (`:248-249`); `quantity == 0` is rejected with
  `InvalidQuantity` (`:251-259`); otherwise `Quantity::Bounded` is set.
* `ldk-node/src/payment/bolt12.rs:518-539` — `receive_variable_amount` builds a
  zero-amount offer with the same absolute-expiry conversion.
* `ldk-node/src/payment/bolt12.rs:297-322` — `send` rejects a zero-amount offer
  with `InvalidOffer` and tells the caller to use `send_using_amount`
  (`:312-321`).
* `ldk-node/src/payment/bolt12.rs:126-151` —
  `send_using_amount_inner`. A non-bitcoin `Amount::Currency` is rejected with
  `UnsupportedCurrency` (`:137-144`); `amount_msat < offer_amount_msat` is
  rejected with `InvalidAmount` (`:146-151`). Overpayment is allowed; the test
  at `tests/integration_tests_rust.rs:4744-4752` confirms that
  `offer_amount - 10_000` fails while `offer_amount + 10_000` succeeds.
* `ldk-node/src/payment/bolt12.rs:158-172` and `:329-334` — payment dispatch to
  `pay_for_offer_from_hrn`, `pay_for_offer_with_quantity`, or `pay_for_offer`.
  The invoice is not known at send time: the stored `PaymentKind::Bolt12Offer`
  has `hash: None, preimage: None, secret: None, offer_id: offer.id()`
  (`:184-191`, `:346-353`).
* `ldk-node/tests/integration_tests_rust.rs:4644-4735` —
  `simple_bolt12_send_receive` creates a 100,000,000 msat offer with
  `Quantity::Bounded(1)`, pays it, receives `Event::PaymentSuccessful` with a
  `bolt12_invoice`, and after settlement asserts the outbound `hash`/`preimage`
  are present and `offer_id == offer.id()`. This is the concrete witness that
  BOLT 12 send is a request/response flow, not a single signed message.

### 2.2 Receive/decode policy (LDK Server)

* `ldk-server/src/api/bolt12_receive.rs:19-43` — fixed amount dispatches to
  `receive`; variable amount with `quantity` is rejected with
  `InvalidRequestError` ("quantity can only be set for fixed-amount offers");
  variable amount without quantity dispatches to `receive_variable_amount`.
  The response returns `offer` (string) and `offer_id` (hex).
* `ldk-server/src/api/bolt12_send.rs:20-45` — parses the offer string, then
  dispatches `amount_msat = None` to `send` and `Some` to
  `send_using_amount`.
* `ldk-server/src/api/decode_offer.rs:31-130` — exposes `offer_id`,
  `description`, `issuer`, amount (bitcoin msat or ISO-4217 currency),
  `issuer_signing_pubkey`, `absolute_expiry`, quantity
  (`One`/`Bounded`/`Unbounded`), `paths` (`introduction_node`,
  `blinding_point`, `num_hops`), `features`, `chains`, `metadata`, and
  `is_expired`. It does not expose the raw TLV stream, the offer signature (an
  offer has none), or any payer-side reader decision.
* `ldk-server/e2e-tests/tests/e2e.rs:325-352` — `test_cli_bolt12_receive`
  checks the `lno` prefix, `offer.id().0 == offer_id`, and rejects `quantity`
  on a variable-amount offer.
* `ldk-server/e2e-tests/tests/e2e.rs:354-415` — `test_cli_decode_offer`
  checks `is_expired = false`, a regtest chain, at least one blinded path with
  `num_hops > 0`, an empty feature map, a variable amount with no amount, and a
  fixed 50,000 sat amount decoding to 50,000,000 msat.
* `ldk-server/e2e-tests/tests/e2e.rs:1249-1271` — `test_cli_bolt12_send`
  sends to a variable-amount offer with an explicit amount.
* `ldk-server/e2e-tests/tests/e2e.rs:1273-1319` — `test_cli_bolt12_refund`
  checks the `lnr` prefix, 5,000,000 msat amount, quantity 1, payer note, and
  that the received payment's refund `hash` equals the invoice `payment_hash`.

### 2.3 Invoice request / invoice behavior

The public LDK Node/Server API does **not** expose a general `InvoiceRequest`
or `Bolt12Invoice` decoder. `send` delegates to
`ChannelManager::pay_for_offer*` (`bolt12.rs:158-172`, `:329-334`), and the
invoice is delivered later inside `Event::PaymentSuccessful.bolt12_invoice`
(`bolt12.rs:426-444`; test `integration_tests_rust.rs:4653-4678`). The only
invoice input in the reviewed server surface is the hex invoice passed to
`create_payer_proof`, which is parsed with `Bolt12Invoice::try_from`
(`bolt12_create_payer_proof.rs:35-42`). The spec-level request/invoice checks
therefore live behind rust-lightning and are not directly testable from these
APIs.

One consequence is important for the replay question: rust-lightning uses
`payer_metadata` for **stateless invoice verification**
(`refs/rust-lightning/lightning/src/offers/offer.rs:278-283`, `:787-798`), not
as a public "reject duplicate metadata" policy. The replay rule must be taken
from BOLT 12, not inferred from an LDK API.

### 2.4 Payer proofs

* `ldk-node/src/payment/bolt12.rs:64-87` — `PayerProofOptions`: a proof always
  commits to the payer id, payment hash, and issuer signing pubkey, and
  discloses invoice features when present; `note`, offer description, offer
  issuer, invoice amount, invoice creation timestamp, and extra TLV types are
  opt-in.
* `ldk-node/src/payment/bolt12.rs:426-444` — doc contract: inputs are taken
  straight from `Event::PaymentSuccessful` (`payment_id`, `payment_preimage`,
  `bolt12_invoice`); nothing is read from the payment store; static-invoice /
  async payments cannot be proven this way.
* `ldk-node/src/payment/bolt12.rs:445-505` — `create_payer_proof` calls
  `prove_payer_derived(payment_preimage, &expanded_key, payment_id, &secp_ctx)`
  (`:453-457`), applies the disclosure options, and `build_and_sign()`s.
* `ldk-node/tests/integration_tests_rust.rs:4680-4696` — builds a proof from the
  event, asserts the preimage is embedded, the invoice amount and note are
  present, the offer description is disclosed, and the undisclosed offer issuer
  and invoice creation timestamp are absent.
* `ldk-server/src/api/bolt12_create_payer_proof.rs:22-60` — parses a 32-byte
  hex preimage and a hex BOLT 12 invoice, builds the options, and calls the
  node method. `ldk-server/e2e-tests/tests/e2e.rs:1321-1368` exercises the same
  path through the CLI; it asserts only that the resulting `payer_proof` string
  is non-empty.
* rust-lightning construction checks:
  `refs/rust-lightning/lightning/src/offers/payer_proof.rs:280-300` (explicit
  builder) and `:310-326` (derived builder) both reject
  `PreimageMismatch` when `SHA256(preimage) != invoice.payment_hash()`.
* rust-lightning verification checks (`payer_proof.rs:902-928`): recompute the
  preimage hash (`:902-906`), verify the invoice signature under
  `invoice_node_id` (`:908-915`), and verify `proof_signature` under
  `invreq_payer_id` (`:917-926`). Missing required fields are rejected
  (`:1041-1096` in the spec anchor below).
* Provenance: LDK explicitly calls payer proofs an extension from BOLT 12 PR
  1295 (`payer_proof.rs:10-18`). The pinned BOLT text does contain the
  `payer_proof` section (`refs/bolts/12-offer-encoding.md:910-1096`), so the
  formalization should cite the pinned text **and** record the LDK provenance;
  it must not claim that LDK's implementation defines the normative semantics.

### 2.5 Refunds (LDK extension, not normative BOLT 12)

* `ldk-node/src/payment/bolt12.rs:562-633` — `initiate_refund(amount_msat,
  expiry_secs, quantity, payer_note, route_parameters)` converts a relative
  expiry to `now + expiry_secs` (`:578-580`), builds a `Refund`, and stores a
  `PaymentKind::Bolt12Refund`.
* `ldk-node/src/payment/bolt12.rs:541-560` — `request_refund_payment(refund)`
  calls `ChannelManager::request_refund_payment` and returns a `Bolt12Invoice`
  "for informational purposes only" (`:543-544`).
* `ldk-server/src/api/bolt12_refund.rs:23-31` — `validate_refund_expiry`
  rejects `expiry_secs == 0` with `InvalidRequestError`. This is **LDK Server
  policy**, not a BOLT 12 `MUST`.
* `ldk-server/src/api/bolt12_refund.rs:33-58` — send-refund parses the refund
  string; receive-refund returns the invoice `payment_hash`.
* `refs/rust-lightning/lightning/src/offers/refund.rs:10-18` — a `Refund` is
  "an offer for money" and "an `InvoiceRequest` produced *not* in response to
  an `Offer`". `:897` sets `BECH32_HRP = "lnr"`.
* `refs/bolts/12-offer-encoding.md:55-58` describes only the
  merchant-pays-user flow (ATM/refund) at the scenario level; the pinned BOLT
  text has no `lnr` TLV stream. The `lnr` encoding is therefore an LDK
  extension. This is a scope fact, not a defect.

### 2.6 BOLT 12 spec anchors

* Payment flows, including merchant-pays-user/refund:
  `refs/bolts/12-offer-encoding.md:40-70`.
* bech32-style encoding and omitted trailing checksum: `:100-108`.
* Signature calculation: BIP-340, tag `"lightning" || messagename || fieldname`,
  `msg` = Merkle root: `:120-136`.
* Merkle leaves (`LnLeaf`, `LnNonce` using the numerically-first TLV entry),
  inner nodes `H("LnBranch", lesser || greater)`, TLV-ascending order, uneven
  power-of-two handling: `:138-149`.
* Offer TLV fields (types 2–22): `:196-233`.
* Offer writer requirements (TLV ranges, amount/description/currency,
  expiry, quantity, issuer/paths): `:237-286`.
* Offer reader requirements (ranges, unknown even features, chains, amount,
  currency, issuer/paths, `num_hops > 0`, expiry, onion-message dispatch):
  `:288-326`.
* Invoice-request TLV fields (types 0–91, 240): `:389-478`.
* Invoice-request writer requirements (copy all offer fields, unpredictable
  `invreq_metadata`, transient `invreq_payer_id`, amount/quantity, signature):
  `:462-503`.
* Invoice-request reader requirements (payer id + metadata, ranges, unknown
  even features, signature, path arrival, offer match, quantity, expected
  amount, chain, BIP 353 name): `:505-556`.
* Invoice-request replay rationale (caller makes metadata unpredictable and
  unique; returning a previous invoice is optional): `:815-821`.
* Invoice TLV fields (types 0–239, 240): `:584-703`.
* Invoice writer requirements (copy request fields, `invoice_amount`,
  `invoice_payment_hash = SHA256(preimage)`, `invoice_node_id`, signature,
  default 7200 s expiry, paths/blindedpay): `:719-759`.
* Invoice reader requirements (required fields, expiry, paths/blindedpay,
  exact response-field match, node id, signature, MPP): `:760-813`.
* Payer-proof TLV fields and requirements: `:910-1096`; the preimage check is
  `:1066-1086`, especially `:1069`.

### 2.7 Datapoints derived from the sources

1. BOLT 12 is wholly unmodelled in Lean; the only BOLT 12 token in `LnLean/`
   is an out-of-scope comment.
2. Offer admission is a static set of writer/reader rules. LDK enforces most
   of them inside builders/parsers; the public API does not expose the raw
   decisions, so a Lean model must encode the spec rules directly, not an API
   trace.
3. LDK Server forbids `quantity` on a variable-amount offer
   (`bolt12_receive.rs:29-36`), while BOLT 12 discusses `offer_quantity_max`
   independently of `offer_amount`. The server rule is policy, not a spec
   `MUST`; do not encode it as one.
4. LDK Node rejects zero-amount offers in `send` and rejects underpayment in
   `send_using_amount`; BOLT 12's writer rule is `invreq_amount >= expected
   amount` and its reader rule rejects `invreq_amount < expected amount`
   (`:536-539`). The API behavior is consistent with the spec, but the spec
   also permits overpayment.
5. Replay is not rejection. BOLT 12 says: if `offer_issuer_id` is present and
   `invreq_metadata` is identical to a previous `invoice_request`, the reader
   **MAY** reply with the previous invoice; otherwise it **MUST NOT**
   (`:515-518`). Fresh metadata must never receive a previous invoice.
6. An invoice in response to a request must copy all non-signature request
   fields (`:725-729`) and the payer must reject a response whose request-range
   fields do not exactly match (`:784-790`); `invoice_payment_hash` is
   `SHA256(payment_preimage)` (`:731-732`).
7. A payer proof binds a preimage to `invoice_payment_hash`, the invoice
   signature to `invoice_node_id`, and the proof signature to
   `invreq_payer_id` (`:1041-1096`; LDK `payer_proof.rs:902-928`). It proves
   possession of a preimage and two signatures, not a real-world identity.
8. `lnr` refunds are an LDK/rust-lightning extension (`refund.rs:10-18`,
   `:897`), not a normative BOLT 12 stream in the pinned text.
9. `OfferId` is LDK-specific: `TaggedHash` with tag `"LDK Offer ID"` over the
   offer TLV stream (`refs/rust-lightning/lightning/src/offers/offer.rs:120-136`,
   `:716-719`). It is not a BOLT 12 wire field.
10. bech32/HRP, omitted checksums, onion-message reply paths, blinded-path
    ECDH, currency conversion, and wall-clock expiry are external to the Lean
    model.

## 3. Gap matrix

Statuses: **covered faithfully**, **partially covered**, **missing**,
**contradicted** (with a witness), **unmodelled/external**. A "missing" row is
not automatically a false theorem; it is a completeness/fidelity gap for any
claim that cites the existing model as BOLT 12 support.

| Behavior | Lean status | LDK / BOLT evidence | Gap / counterexample | Priority |
|---|---|---|---|---|
| Offer TLV schema (types 2–22: chains, metadata, currency, amount, description, features, expiry, paths, issuer, quantity, issuer id) | missing | BOLT `:196-233`; LDK builder `bolt12.rs:233-267`; decode `decode_offer.rs:31-130` | No `Offer` record and no BOLT 12 TLV schema. Generic `Wire.TLV` has no known-type map or value widths. | P1 |
| Offer writer rules (TLV ranges, amount > 0, amount ⇒ description, currency ⇒ amount, expiry, quantity non-zero, issuer/paths) | missing | BOLT `:237-286` | No writer, no range check, no amount/currency relationship. LDK's builder enforces some of these but is not a model. | P1 |
| Offer reader admission (range, unknown even features, chains, amount/description, currency/amount, issuer/paths, `num_hops > 0`, expiry, onion dispatch) | missing | BOLT `:288-326`; LDK `decode_offer.rs:31-130` (field exposure only) | No reader predicate. `decode_offer` returns fields and `is_expired`; it does not prove admission. | **P0** |
| Fixed vs zero-amount offer semantics | missing | BOLT `:240-256`; LDK `bolt12.rs:297-322`, `:518-539`; e2e `e2e.rs:354-415` | No amount-mode model. LDK rejects `send` on a zero-amount offer and requires `send_using_amount`. | P1 |
| Quantity semantics (`offer_quantity_max`, non-zero, request bounds) | missing | BOLT `:274-282`, `:526-534`; LDK `bolt12.rs:251-259`; server `bolt12_receive.rs:29-36` | No quantity field or bound. Note the server's "quantity only with fixed amount" rule is policy, not BOLT 12. | P1 |
| Invoice-request TLV schema (types 0–91, 240) | missing | BOLT `:389-478` | No `InvoiceRequest` record. `invreq_metadata` (type 0), `invreq_payer_id` (88), and `signature` (240) do not exist. | **P0** |
| Invoice-request writer (copy offer fields, unpredictable metadata, transient payer id, amount/quantity, signature) | missing | BOLT `:462-503`; LDK dispatch `bolt12.rs:158-172` | No writer and no metadata unpredictability model. `invreq_metadata` generation is an external RNG assumption. | **P0** |
| Invoice-request reader (required payer id + metadata, ranges, unknown even features, signature, offer match, path arrival, quantity, expected amount, chain, BIP 353) | missing | BOLT `:505-556` | No reader predicate. The signature check is not connected to `schnorr_message_bound`. | **P0** |
| Replay / response freshness for identical `invreq_metadata` | missing | BOLT `:515-518` | A naive "replay is rejected" model would be **contradicted**: identical metadata + `offer_issuer_id` may reuse the previous invoice; fresh metadata must not. | **P0** |
| Invoice TLV schema and writer (copy request, amount, payment hash, node id, signature, 7200 s default expiry, paths/blindedpay) | missing | BOLT `:584-759`; LDK event `bolt12.rs:426-444` | No `Bolt12Invoice` record, no field copying, no `invoice_node_id` rule, no `SHA256(preimage)` writer rule. | **P0** |
| Invoice reader checks (required fields, expiry, paths/blindedpay, exact request-field match, node id, signature, MPP) | missing | BOLT `:760-813` | No reader predicate. `Invoice.Valid` is BOLT 11 and its signature is 65-byte ECDSA (`Invoice.lean:169`), not BOLT 12 BIP-340. | **P0** |
| Payer-proof TLV schema and required-field presence | missing | BOLT `:926-1096`; LDK `bolt12.rs:64-87`, `:445-505` | No `PayerProof` record; no `invreq_metadata`-exclusion rule, no omitted-marker/leaf-hash fields. | P1 |
| Payer-proof preimage binding | partially covered (primitive only) | BOLT `:1066-1086`; LDK `payer_proof.rs:280-300`, `:310-326`, `:902-906` | `opensTo` (`Hash.lean:38-41`) can express `SHA256(preimage) = payment_hash`, but no BOLT 12 proof record uses it. | **P0** |
| Payer-proof invoice/proof signature binding | partially covered (primitive only) | BOLT `:1041-1096`; LDK `payer_proof.rs:908-926` | `schnorr_message_bound` (`SchnorrProps.lean:190-196`) gives message equality under `AssumesEufCma`; no BOLT 12 proof uses it. Do not claim payer identity. | **P0** |
| BOLT 12 Merkle tree / selective disclosure | missing | BOLT `:138-149`; rust-lightning `merkle.rs:163-252` | No tree, no leaf/nonce/branch hashing, no sibling sort. `MerkleRootValid` (`SchnorrProps.lean:267-269`) is only a 32-byte BIP-341 root, not a tree. C1 covers only 32-byte inputs, while branch inputs are 64 bytes. | P2 (external assumption) |
| BOLT 12 signature tag construction and cross-form domain separation | partially covered | BOLT `:126-136`; `SchnorrProps.lean:254-262`; `Sha256Props.lean:265-329` | `taggedHash` exists, but there is no `"lightning"||messagename||fieldname` table and no cross-form lemma. `taggedHash_collision_witness` is same-message only. | P2 |
| `OfferId` as a spec-derived offer identifier | unmodelled/external (and contradicted if claimed as wire identity) | `offer.rs:120-136`, `:716-719` | LDK's `OfferId` is `TaggedHash("LDK Offer ID", TLV stream)`, not a BOLT 12 field. `offer.id()` is an LDK bookkeeping key. | P1 (anti-overclaim) |
| bech32/HRP `lno`/`lnr`/`lnp` and omitted trailing checksum | unmodelled/external | BOLT `:100-108`; e2e `e2e.rs:325-352`, `:1273-1319` | No BOLT 12 HRP or bech32 codec. `InvoiceWireTargets` is pre-bech32 BOLT 11 only (`LN-PM-007`). | P2 |
| Blinded paths, onion-message reply path, and final blinded node id | unmodelled/external | BOLT `:322-326`, `:519-524`, `:741-745`; `RouteBlindingProps.lean:437-487` | Structural `BlindedPath` has no `num_hops` wire field, ECDH, onion message, or reply path. Path-arrival evidence is external. | P2 |
| Refund (`lnr`) flow | unmodelled/external (LDK extension) | `refund.rs:10-18`, `:897`; `bolt12.rs:541-633`; `bolt12_refund.rs:23-58` | Pinned BOLT text has only the merchant-pays-user scenario (`:55-58`), no `lnr` stream. Server expiry > 0 is policy, not spec. | P2 |
| Unknown even/odd feature and TLV policy | missing | BOLT `:292-298`, `:509-514`, `:766-769`; `Wire/TLV.lean:25-28` | `Wire.TLV` explicitly does not model even/odd or known-type policy. | P1 |
| Clock, expiry, currency conversion, and metadata randomness | unmodelled/external | BOLT `:319-320`, `:761-775`; LDK `bolt12.rs:241-246`, `:526-531` | No wall clock, no ISO-4217 oracle, no RNG model. The Lean target must take `now` and expected amounts as parameters. | P2 |
| Documentation anchor for BOLT 12 | contradicted | `docs/ANCHORS-GENERATED.md:131` vs `LnLean/Payment/Invoice.lean:98` | The anchor is generated from the out-of-scope sentence; it falsely implies BOLT 12 coverage. | P1 (docs) |

## 4. Proposed targets

The targets below are **statement shapes for wave-14 scoping**, not claims
that they compile as written. Each is classified as a **model extension**, an
**external assumption**, or both. No target is proof-only: there is no
existing BOLT 12 semantics to derive from the current tree.

Priorities are relative to a decision to model BOLT 12. Under the current
documented scope (`SCOPE.md:24`, `ASSUMPTIONS.md:144`, `Invoice.lean:98`) the
whole lane is out of scope; the P0/P1 labels identify what a bounded lane must
do first if the scope decision is made.

All names are proposed under a new module
`LnLean/Proofs/Payment/Bolt12Targets.lean`; no such module exists.

### T1 — `LnLean.Proofs.Payment.Bolt12Targets.offer_admission_sound`

**Priority:** P0 within the lane. **Classification:** model extension.
**Fidelity risk:** medium (must separate BOLT `MUST`s from LDK Server/Node
policy; currency and chain handling are easy to over-model). **Feasibility:**
high; it is a record plus an executable checker over the generic TLV stream.

**Statement shape:**

```lean
structure OfferView where
  chains : List ChainHash
  metadata : Option ByteArray
  currency : Option String
  amountMsat : Option Nat
  description : Option String
  features : ByteArray
  absoluteExpiry : Option Nat
  paths : List BlindedPath
  issuer : Option String
  quantityMax : Option Nat
  issuerId : Option PubKey
  rawTypes : List Nat

/-- Executable reader checks; defined by recursion over the decoded TLV list,
    not by conjoining the conclusion. -/
def checkOffer (supportedChains : List ChainHash) (now : Nat)
    (o : OfferView) : Bool := ...

theorem offer_admission_sound
    {supportedChains : List ChainHash} {now : Nat} {o : OfferView}
    (h : checkOffer supportedChains now o = true) :
    (∀ t ∈ o.rawTypes, (1 ≤ t ∧ t ≤ 79) ∨
      (1000000000 ≤ t ∧ t ≤ 1999999999)) ∧
    (o.amountMsat.isSome → o.description.isSome) ∧
    (∀ a, o.amountMsat = some a → 0 < a) ∧
    (o.currency.isSome → o.amountMsat.isSome) ∧
    (o.chains = [] → bitcoin ∈ supportedChains) ∧
    (o.chains ≠ [] → ∃ c ∈ o.chains, c ∈ supportedChains) ∧
    (o.issuerId.isSome ∨ ¬ o.paths.isEmpty) ∧
    (∀ p ∈ o.paths, 0 < p.hops.length) ∧
    (∀ e, o.absoluteExpiry = some e → now ≤ e) ∧
    noUnknownEvenOfferFeature o.features
```

**Hypotheses:** the decoded offer comes from a `TLVStream.WellFormed` stream
(`TLV.lean:90-96`); `supportedChains` is the node's chain policy; `now` is a
parameter (no clock model); `noUnknownEvenOfferFeature` is a new predicate over
a feature bitmap; `BlindedPath` is a wrapper that exposes `hops.length` because
`RouteBlindingProps.BlindedPath` has no `num_hops` wire field. Currency
conversion is **not** required in T1: restrict to bitcoin-denominated offers
(`currency = none`) and leave ISO-4217 as external.

**Non-vacuity witness:** a bitcoin offer with `amountMsat = some 100_000_000`,
`description = some "asdf"`, `quantityMax = some 1`, `chains = [regtest]`, one
non-empty path, and `issuerId = some pk` is accepted. This mirrors
`integration_tests_rust.rs:4644-4651` and `e2e.rs:354-415`.
**Negative witnesses:** `amountMsat = some 0` rejected; `amountMsat = some a`
with `description = none` rejected; `currency = some c` with
`amountMsat = none` rejected; `issuerId = none` and `paths = []` rejected;
`absoluteExpiry = some e` with `e < now` rejected; a path with zero hops
rejected; an unknown even feature bit rejected.

**Why faithful:** it is a direct transcription of the BOLT 12 reader rules
(`:288-326`) and the offer writer rules that the reader relies on
(`:237-286`). It does not claim that LDK Server's "quantity only with fixed
amount" rule (`bolt12_receive.rs:29-36`) is a BOLT 12 rule.

**Preservation:** do not define `checkOffer` as the conjunction it is supposed
to prove, and do not reuse `Invoice.Valid` (BOLT 11) as an offer admission
predicate.

### T2 — `LnLean.Proofs.Payment.Bolt12Targets.invoiceRequest_admission_sound`

**Priority:** P0 within the lane. **Classification:** model extension.
**Fidelity risk:** high (exact offer-field match, path arrival, quantity, and
expected amount are all easy to weaken accidentally). **Feasibility:** medium;
needs a `SchnorrSig` verification relation but can reuse the T1 `OfferView`.

**Statement shape:**

```lean
structure InvoiceRequestView where
  metadata : Option ByteArray
  payerId : Option PubKey
  chain : Option ChainHash
  amountMsat : Option Nat
  features : ByteArray
  quantity : Option Nat
  payerNote : Option String
  bip353Name : Option (String × String)
  offerFields : OfferView
  signature : Option SchnorrSig
  arrivedVia : Option BlindedPath
  rawTypes : List Nat

def checkInvoiceRequest (M : PrimitiveModel)
    (supportedChains : List ChainHash) (now : Nat)
    (knownOffer : OfferView) (req : InvoiceRequestView) : Bool := ...

theorem invoiceRequest_admission_sound
    {M : PrimitiveModel} {supportedChains : List ChainHash}
    {now : Nat} {knownOffer : OfferView} {req : InvoiceRequestView}
    (h : checkInvoiceRequest M supportedChains now knownOffer req = true) :
    req.metadata.isSome ∧ req.payerId.isSome ∧
    req.rawTypesInRange ∧
    (req.chain = none → bitcoin ∈ supportedChains) ∧
    (∀ c, req.chain = some c → c ∈ supportedChains) ∧
    (∀ p ∈ knownOffer.paths,
      req.arrivedVia = some p ∨ knownOffer.paths = []) ∧
    req.offerFields = knownOffer ∧
    (∀ e, knownOffer.absoluteExpiry = some e → now ≤ e) ∧
    quantityOk knownOffer req ∧
    amountOk knownOffer req ∧
    M.schnorrVerify req.payerId.get
      (bolt12Tag .invoiceRequest .signature (merkleRoot req)) req.signature.get = true
```

where `quantityOk` enforces: `offer_quantity_max` present ⇒ `invreq_quantity`
present; if `offer_quantity_max = some n` and `n > 0`, then
`0 < quantity ≤ n`; if `offer_quantity_max = none`, then `quantity = none`.
`amountOk` enforces: if `offer_amount` is present, `invreq_amount ≥ expected`
(with `expected = offer_amount * quantity` for bitcoin-only offers); otherwise
`invreq_amount` is present. `req.rawTypesInRange` is the 0–159 /
1,000,000,000–2,999,999,999 range rule.

**Hypotheses:** `knownOffer` has already passed T1 and is unexpired; the
request's offer fields are **exactly** equal (not merely amount-equal); the
signature is checked with `M.schnorrVerify` over the BOLT 12 tagged hash;
`merkleRoot req` is an explicit BOLT 12 digest supplied by the TLV/Merkle codec
(T2 does not prove the root construction; T6 is deferred); `arrivedVia` is
supplied by the transport layer, not derived; currency conversion is excluded
(bitcoin-only offers); `bip353Name` is checked only for the ASCII character set,
if modelled at all.

**Non-vacuity witness:** the request implicitly created by
`integration_tests_rust.rs:4644-4651` (100,000,000 msat, quantity 1, payer note
"Test", valid signature, arrived via a valid offer path) is accepted.
**Negative witnesses:** missing `metadata` rejected; missing `payerId`
rejected; wrong signature rejected; `offerFields` differing in `metadata` or
`amountMsat` rejected; `quantity = 0` or `quantity > max` rejected;
`invreq_amount < expected` rejected; `offer_amount = none` with no
`invreq_amount` rejected; a request that arrived via a non-offer path is
ignored; a non-ASCII BIP 353 name rejected.

**Why faithful:** it transcribes the invoice-request reader
(`:505-556`) and the writer preconditions it checks (`:462-503`). The exact
offer-field match is the spec's stateless-offer rule, not an implementation
shortcut.

**Preservation:** do not let `request.offerFields = knownOffer` be true by
construction (e.g. by storing only the fields the checker reads); the negative
witnesses must be expressible. Do not assume the signature verifies; it is a
checked conjunct with `M.schnorrVerify`, and `EufCma` remains a hypothesis, not
a source of key ownership.

### T3 — `LnLean.Proofs.Payment.Bolt12Targets.invoiceResponse_binding_and_freshness`

**Priority:** P0 within the lane. **Classification:** model extension.
**Fidelity risk:** high (the replay allowance is the easiest BOLT 12 rule to
state incorrectly). **Feasibility:** high once T2 exists; it is a small state
machine plus field-equality predicates.

**Statement shape:**

```lean
inductive Response
  | fresh (inv : Bolt12InvoiceView)
  | replay (previous : Bolt12InvoiceView)
  | reject

def respond (seen : List ByteArray) (req : InvoiceRequestView)
    (previous : Option Bolt12InvoiceView) : Response := ...

theorem respond_replay_only_if_seen_and_issuer
    {seen : List ByteArray} {req : InvoiceRequestView}
    {previous inv : Bolt12InvoiceView}
    (h : respond seen req (some previous) = .replay inv) :
    (∃ m, req.metadata = some m ∧ m ∈ seen) ∧
    req.offerFields.issuerId.isSome

theorem respond_fresh_metadata_not_replay
    {seen : List ByteArray} {req : InvoiceRequestView}
    {previous : Bolt12InvoiceView}
    (hmeta : ∀ m, req.metadata = some m → m ∉ seen) :
    respond seen req (some previous) ≠ .replay previous

theorem respond_binds_request_fields
    {seen : List ByteArray} {req : InvoiceRequestView}
    {inv : Bolt12InvoiceView}
    (h : respond seen req none = .fresh inv) :
    inv.requestFields = req.offerFields ∧
    inv.metadata = req.metadata ∧
    (∀ pk, req.offerFields.issuerId = some pk → inv.invoiceNodeId = pk) ∧
    (req.offerFields.issuerId = none →
      ∃ p, req.arrivedVia = some p ∧
        inv.invoiceNodeId = finalBlindedNode p) ∧
    inv.invoiceAmountMsat = expectedAmount req
```

**Hypotheses:** `seen` is the set/list of previously observed
`invreq_metadata` values; `previous` is the previously issued invoice, if any;
`req.metadata` is present (T2 guarantees it); `offer_issuer_id` is the
`offerFields.issuerId`; the response's `requestFields` are the 0–159 /
1,000,000,000–2,999,999,999 range. The model must **not** assume that
`seen` contains every request ever received; it is an explicit parameter.

**Non-vacuity witness:** `seen = []`, fresh metadata, no previous invoice →
`.fresh inv` with `inv.requestFields = req.offerFields`. `seen = [m]`,
`issuerId = some pk`, `req.metadata = m` → `.replay previous` is permitted.
**Negative witnesses:** `seen = [m]`, `issuerId = none`, `req.metadata = m` →
`.replay` is impossible; fresh metadata `m' ∉ seen` → `.replay previous` is
impossible; a response with a mismatched `invoice_amount` or `invoice_node_id`
is rejected by the reader predicate.

**Why faithful:** BOLT 12 `:515-518` says exactly "if `offer_issuer_id` is
present, and `invreq_metadata` is identical to a previous `invoice_request`:
MAY simply reply with the previous invoice; otherwise: MUST NOT reply with a
previous invoice." The rationale at `:815-821` adds that the caller is
responsible for making `invreq_metadata` unpredictable and unique, and that
such caching is optional. The field-copy and node-id rules are `:725-745` and
`:784-790`.

**Preservation:** do **not** state "replay is rejected" or "`invreq_metadata`
is globally unique." Do not make `respond` always return `.reject` to make the
theorems vacuous; the fresh witness and the replay witness must both be
inhabited. Do not encode a wall-clock expiry here; `now` is a parameter.

### T4 — `LnLean.Proofs.Payment.Bolt12Targets.payerProof_binding`

**Priority:** P0 within the lane. **Classification:** model extension plus
external assumptions C1/C4. **Fidelity risk:** medium (the proof proves
possession, not identity; selective disclosure is a separate concern).
**Feasibility:** high-medium; the preimage and signature predicates already
exist, and the Merkle reconstruction can be an explicit parameter.

**Statement shape:**

```lean
structure PayerProofView where
  payerId : PubKey
  paymentHash : PaymentHash
  invoiceNodeId : PubKey
  invoiceSignature : SchnorrSig
  preimage : Preimage
  proofSignature : SchnorrSig
  omitted : List Nat
  leafHashes : List ByteArray
  missingHashes : List ByteArray
  proofNote : Option String

def checkPayerProof (M : PrimitiveModel)
    (invoiceRoot : ByteArray) (p : PayerProofView) : Bool :=
  p.requiredFieldsPresent &&
  p.omittedMarkersWellFormed &&
  opensTo M p.paymentHash p.preimage &&
  M.schnorrVerify p.invoiceNodeId
    (bolt12Tag .invoice .signature invoiceRoot) p.invoiceSignature &&
  M.schnorrVerify p.payerId (proofRoot p) p.proofSignature

theorem payerProof_binding
    {M : PrimitiveModel} {invoiceRoot : ByteArray} {p : PayerProofView}
    (h : checkPayerProof M invoiceRoot p = true) :
    (M.sha256 p.preimage.bytes).size = 32 ∧
    M.sha256 p.preimage.bytes = p.paymentHash.bytes ∧
    M.schnorrVerify p.invoiceNodeId
      (bolt12Tag .invoice .signature invoiceRoot) p.invoiceSignature = true ∧
    M.schnorrVerify p.payerId (proofRoot p) p.proofSignature = true
```

**Hypotheses:** `invoiceRoot` is the Merkle root reconstructed from the
invoice / selective-disclosure data (T6 or an external verifier supplies it;
T4 does not prove reconstruction completeness); `proofRoot p` is the BOLT 12
proof Merkle root over the included payer-proof TLVs (also supplied by the
codec/T6, not reconstructed here); `p.requiredFieldsPresent`
covers `invreq_payer_id`, `invoice_payment_hash`, `invoice_node_id`,
`signature`, `proof_preimage`, `proof_missing_hashes`, `proof_leaf_hashes`,
and `proof_signature` (`:1066-1086`); `omittedMarkersWellFormed` covers strict
ascending order, no 0, ranges, and no included-TLV numbers; `opensTo` uses
`Hash.lean:38-41`; the two signature checks use `M.schnorrVerify` and the
BOLT 12 proof tag table (T5).

**Non-vacuity witness:** the proof built in
`integration_tests_rust.rs:4680-4696` (preimage from
`Event::PaymentSuccessful`, invoice amount disclosed, description disclosed,
issuer/timestamp omitted) satisfies the predicate with the corresponding
`invoiceRoot`. **Negative witnesses:** a preimage whose SHA-256 differs from
`paymentHash` rejected (LDK `payer_proof.rs:902-906`); missing
`proof_preimage` rejected; malformed omitted markers rejected; an invalid
invoice signature rejected; an invalid `proof_signature` rejected.

**Why faithful:** the reader rules at `:1066-1086` and LDK's checks at
`payer_proof.rs:902-928` are exactly these conjuncts. The theorem deliberately
does **not** conclude "the payer paid" or "the payer is this human"; it
concludes only that the supplied preimage opens the invoice payment hash and
that two signatures verify under the claimed keys.

**Preservation:** do not derive T4 from `Invoice.signature_valid`
(`Invoice.lean:267-272`): that is a BOLT 11 projection over an unconstrained
`sigCheck`. Keep `acceptsAll_not_eufCma` (`SchnorrProps.lean:219-230`) and the
`signatureOnly_*` witnesses (`InvoiceWireTargets.lean:1108-1145`) visible.

### T5 — `LnLean.Proofs.Payment.Bolt12Targets.bolt12Tag_table_separates`

**Priority:** P2. **Classification:** model extension (finite table) using the
existing tagged-hash substrate. **Fidelity risk:** low for the fixed table;
high if generalized to arbitrary tag strings. **Feasibility:** high.

**Statement shape:**

```lean
inductive SignedForm | invoiceRequest | invoice | payerProof
inductive SignedField | signature | proofSignature

def bolt12Tag : SignedForm → SignedField → ByteArray := ...

theorem bolt12Tag_injective :
    Function.Injective (fun x : SignedForm × SignedField => bolt12Tag x.1 x.2)

theorem bolt12Tag_cross_form_collision_witness
    {M : PrimitiveModel} {f₁ f₂ : SignedForm} {g₁ g₂ : SignedField}
    {m₁ m₂ : ByteArray}
    (htag : bolt12Tag f₁ g₁ ≠ bolt12Tag f₂ g₂)
    (heq : M.sha256 (tagPrefix M (bolt12Tag f₁ g₁) ++ m₁) =
           M.sha256 (tagPrefix M (bolt12Tag f₂ g₂) ++ m₂)) :
    ∃ x y : ByteArray, x ≠ y ∧ M.sha256 x = M.sha256 y
```

**Hypotheses:** tags are the literal 9-byte `"lightning"` followed by the
fixed message name and field name (`:126-136`); the table is only the forms in
the pinned text (`invoice_request`, `invoice`, `payer_proof`); `m₁`/`m₂` are
the corresponding Merkle roots. The second theorem is a reduction, not an
unconditional separation result: it exhibits a SHA-256 collision on distinct
inputs, which C1 does not cover because the inputs are not 32 bytes.

**Non-vacuity witness:** the four tag byte strings for
`(invoice_request, signature)`, `(invoice, signature)`,
`(payer_proof, signature)`, and `(payer_proof, proof_signature)` are pairwise
distinct by `decide`. **Negative witness:** a hypothetical tag formed by
ambiguous concatenation outside the fixed table is not covered; the theorem
must not claim general prefix-freedom.

**Why faithful:** `:120-136` defines the tag exactly. The existing
`taggedHash_collision_witness` (`Sha256Props.lean:316-329`) covers the
same-message case; T5 generalizes it to two messages and records the extra
collision surface. This target is small enough to fold into T4 if a separate
module is undesirable.

**Preservation:** do not claim "tagged hashes are injective" or "C1 proves
domain separation." C1 quantifies only over 32-byte inputs; the tag prefix is
64 bytes and the tagged input is longer.

### T6 — `LnLean.Proofs.Payment.Bolt12Targets.merkleRoot_ordered`

**Priority:** P2, and **not recommended for implementation in wave 13/14**
without a new documented assumption. **Classification:** model extension plus
a **new external assumption**. **Fidelity risk:** high (leaf order, nonce
construction, signature exclusion, uneven trees, sibling sorting).
**Feasibility:** medium for the computation; the binding theorem needs a
64-byte-input branch-hash assumption that the current TCB does not have.

**Statement shape:**

```lean
structure Leaf where
  tlvType : Nat
  value : ByteArray

def merkleRoot? (firstTlv : Nat) (ls : List Leaf) : Option ByteArray := ...

theorem merkleRoot_deterministic {firstTlv : Nat} {ls : List Leaf} :
    merkleRoot? firstTlv ls = merkleRoot? firstTlv ls := rfl

theorem merkleRoot_permutation_needs_branch_binding
    {M : PrimitiveModel} (hbr : BranchBinding M)
    {firstTlv : Nat} {ls ls' : List Leaf}
    (hperm : ls.Perm ls') (hne : ls ≠ ls') :
    merkleRoot? firstTlv ls ≠ merkleRoot? firstTlv ls'
```

**Hypotheses:** leaves are the non-signature TLVs in TLV-ascending order;
each leaf is `H("LnLeaf", tlv)` paired with a nonce
`H("LnNonce" || first-tlv, type)` (`:138-149`); inner nodes are
`H("LnBranch", lesser-SHA256 || greater-SHA256)`; `BranchBinding M` is an
explicit new assumption that SHA-256 is collision-resistant on the 64-byte
branch inputs (and on the longer tagged inputs). The current
`CollisionResistant` (`Model.lean:52-57`) covers only 32-byte inputs and cannot
discharge this.

**Non-vacuity witness:** a one-leaf tree and a two-leaf tree with distinct
leaves, both accepted by `merkleRoot?`; the root is a 32-byte value.
**Negative witness:** a permutation of two distinct leaves is **not** proved
equal; the theorem requires `BranchBinding` and must not be restated
unconditionally. Do not use the existing `MerkleRootValid`
(`SchnorrProps.lean:267-269`); it is only a BIP-341 32-byte root predicate.

**Why faithful:** the computation mirrors BOLT 12 `:138-149` and
rust-lightning `offers/merkle.rs:163-252` (including the sibling sort at
`:242-252`). The target is listed to make the missing assumption explicit, not
to claim selective-disclosure soundness.

**Preservation:** do **not** add a `branch_collisionResistant` field to
`PrimitiveModel` silently. That would change C1–C8 and every consumer of the
TCB. If this target is pursued, it needs a new documented assumption (e.g.
`C9-BOLT12-MERKLE`) and an explicit statement that it is not derived from C1.

### T7 — `LnLean.Proofs.Payment.Bolt12Targets.refundExtension_scope`

**Priority:** P2 (defer). **Classification:** unmodelled/external; at most an
LDK-extension model, **not** BOLT 12. **Fidelity risk:** high (the flow is
non-normative in the pinned text). **Feasibility:** low-medium; the payment
binding needs the full invoice/payment state.

**Statement shape:**

```lean
structure RefundView where
  amountMsat : Nat
  absoluteExpiry : Nat
  quantity : Option Nat
  payerNote : Option String
  payerMetadata : ByteArray
  signingPubkey : PubKey
  hrp : String

def checkRefundExtension (r : RefundView) : Bool :=
  r.hrp = "lnr" && 0 < r.amountMsat && 0 < r.absoluteExpiry && ...

theorem refundExtension_structural_binding
    {r : RefundView} (h : checkRefundExtension r = true) :
    r.hrp = "lnr" ∧ 0 < r.amountMsat ∧ 0 < r.absoluteExpiry
```

**Hypotheses:** the `lnr` HRP and the expiry policy are explicitly labelled
LDK extension/server policy (`refund.rs:897`, `bolt12_refund.rs:23-31`); the
payment-hash/preimage binding is **not** proved here because it requires the
invoice and settlement state.

**Non-vacuity witness:** the e2e refund of 5,000,000 msat with expiry 3600 and
quantity 1 (`e2e.rs:1298-1305`). **Negative witness:** expiry 0 is rejected by
the server policy (`bolt12_refund.rs:23-31`), but this is not a BOLT 12
counterexample; label it as policy.

**Why faithful:** it models only what the LDK extension actually guarantees at
the structural level. It does not present `lnr` as a BOLT 12 wire stream.

**Preservation:** do **not** add `Refund` to a BOLT 12 catalog row. Do not
claim the server's `expiry > 0` rule is a BOLT 12 `MUST`.

## 5. Assumptions, counterexamples, and non-vacuity risks

### 5.1 Counterexamples that must remain visible

| Witness | Location | Why it matters |
|---|---|---|
| `signatureOnly_verifies` | `InvoiceWireTargets.lean:1108-1111` | A BOLT 11 invoice verifies under a constant digest and always-true `sigCheck`; signature validity is not payment. |
| `signatureOnly_no_preimage` | `InvoiceWireTargets.lean:1115-1118` | The same invoice has no preimage under a constant hash; do not infer payment from verification. |
| `signature_only_separates_verify_from_payment` | `InvoiceWireTargets.lean:1141-1145` | Mechanizes the separation; T4 must not collapse it. |
| `acceptsAll_not_eufCma` | `SchnorrProps.lean:219-230` | 64-byte signature formatting plus an always-accepting verifier is not EUF-CMA. |
| `preimageResistant_vacuous` | `Sha256Props.lean:511` | A global injective `PreimageResistant` is uninhabited for a 32-byte output; do not use it as a BOLT 12 assumption. |
| `taggedHash_collision_witness` | `Sha256Props.lean:316-329` | Tagged-hash separation is a collision reduction, not an unconditional injectivity theorem. It is same-message only. |
| `tagPrefix_separates_hashed_tags` | `Sha256Props.lean:302-308` | Structural separation of prefixes, conditional on distinct tag digests. |
| `TLVStream.WellFormed` / parser caveat | `TLV.lean:7-12`, `:90-96`, `:196-215` | Sorted/unique is modelled, but the full parser round-trip is not proved. Do not treat a decoded offer as a wire-conformance result. |
| `OfferId` tag | `offer.rs:120-136`, `:716-719` | LDK-specific `"LDK Offer ID"` tagged hash, not a BOLT 12 field. |
| `ANCHORS-GENERATED.md:131` | docs | False BOLT 12 anchor generated from an out-of-scope sentence. |

### 5.2 Assumptions that must stay explicit

1. **C1 — SHA-256 collision resistance on 32-byte inputs**
   (`Model.lean:52-57`). It supports preimage uniqueness for `opensTo`
   (`Hash.lean:38-41`) but does **not** cover BOLT 12's 64-byte Merkle branch
   inputs or arbitrary-length tagged-hash inputs.
2. **C4 — BIP-340 Schnorr EUF-CMA** (`Model.lean:68-73`,
   `Sig.lean:93-96`). It gives message binding under one key; it does not give
   key ownership, key derivation correctness, or payer identity.
3. **Tagged-hash binding.** `taggedHash` is a function
   (`SchnorrProps.lean:254-262`); its output is 32 bytes. Domain separation is
   only a reduction (`Sha256Props.lean:302-329`), not a theorem that distinct
   BOLT 12 forms cannot collide.
4. **Expanded-key derivation.** `create_payer_proof` uses
   `keys_manager.get_expanded_key()` (`bolt12.rs:453-457`) and
   `prove_payer_derived` (`payer_proof.rs:310-326`). The derivation is an
   external secp256k1/HD fact; no Lean model exists.
5. **Unpredictable `invreq_metadata`.** BOLT 12 requires an unpredictable
   series of bytes (`:494`). Freshness/replay safety depends on this RNG fact.
6. **Clock and expiry.** LDK converts relative expiry with
   `SystemTime::now()` (`bolt12.rs:241-246`, `:526-531`, `:578-580`); BOLT 12
   compares against `invoice_created_at` plus a relative expiry or 7200 s
   (`:761-775`). A Lean target must take `now` as a parameter; it must not
   assume a synchronized clock.
7. **bech32/HRP and omitted checksum.** `lno`/`lnr`/`lnp` and the omitted
   six-character checksum (`:100-108`) are external encoding facts. Lean has
   no BOLT 12 bech32 codec; `LN-PM-007` is a pre-bech32 BOLT 11 field-list.
8. **Onion-message transport and blinded paths.** BOLT 12 sends requests and
   invoices over onion messages and binds them to blinded paths
   (`:322-326`, `:519-524`, `:741-745`). `RouteBlindingProps` is structural
   only; it has no ECDH, `num_hops` wire field, or reply-path semantics.
9. **Currency conversion.** BOLT 12 allows non-bitcoin `offer_currency` and
   requires conversion to `invreq_chain` (`:536-539`); LDK rejects unsupported
   currencies (`bolt12.rs:137-144`). An ISO-4217/price oracle is external.
   T1/T2 deliberately restrict to bitcoin-denominated offers.
10. **LDK policy is not BOLT 12.** `quantity` only with fixed amount
    (`bolt12_receive.rs:29-36`), zero-amount `send` rejection
    (`bolt12.rs:297-322`), and refund expiry > 0 (`bolt12_refund.rs:23-31`)
    are implementation/server policies, not spec `MUST`s.

### 5.3 Claims that must not be strengthened or hidden

* **Do not claim "BOLT 12 support"** from the existing tree. The only BOLT 12
  token in `LnLean/` is an out-of-scope comment (`Invoice.lean:98`).
* **Do not claim "replay is rejected."** BOLT 12 permits reusing the previous
  invoice for identical `invreq_metadata` when `offer_issuer_id` is present
  (`:515-518`); only the "otherwise" branch forbids a previous invoice. T3
  must preserve both the replay and fresh witnesses.
* **Do not claim refunds are normative BOLT 12.** `lnr` is an LDK extension
  (`refund.rs:10-18`, `:897`); the pinned spec has only the merchant-pays-user
  scenario (`:55-58`).
* **Do not claim a payer proof proves who paid** in a real-world sense. It
  proves possession of a preimage and two verifying signatures under claimed
  keys; key ownership and identity are outside the model.
* **Do not derive Merkle/selective-disclosure binding from C1.** C1 is
  32-byte-input collision resistance; BOLT 12 branch inputs are 64 bytes.
  Adding a branch-hash assumption is a TCB change (new C9), not a lemma.
* **Do not treat `OfferId` as a BOLT 12 wire identity.** It is
  `TaggedHash("LDK Offer ID", TLV stream)` (`offer.rs:120-136`), and
  `offer.id()` is used for LDK bookkeeping (`:716-719`; `bolt12.rs:184-191`).
* **Do not reuse `Invoice.signature_valid` as BOLT 12 signature soundness.**
  It is a BOLT 11 projection over an unconstrained `sigCheck`
  (`Invoice.lean:252-272`), and its signature is 65-byte recoverable ECDSA
  (`:163-169`), not 64-byte BIP-340.
* **Do not add a BOLT 12 catalog row** merely because this report proposes
  targets. The catalog records obligations and their proved targets
  (`docs/THEOREM-INDEX.md:1-15`), not scoping statements; do not turn an
  assumption into a theorem by rewording it (`docs/OPEN-ISSUES.md:26-27`).
* **Do not encode LDK Server policy as BOLT 12.** In particular, the
  fixed-amount/quantity coupling and refund-expiry positivity are not in the
  spec reader rules.
* **Do not "fix" `docs/ANCHORS-GENERATED.md:131` from this lane.** It is a
  generated documentation artifact owned by the docs pipeline; flag it to the
  parent instead.

### 5.4 Non-vacuity plan for the new targets

* **T1:** positive bitcoin offer with 100,000,000 msat, description, quantity
  1, one path, issuer id; negatives for zero amount, missing description,
  currency without amount, no issuer/paths, expired, zero-hop path, unknown
  even feature.
* **T2:** positive request from the LDK integration test shape; negatives for
  missing metadata/payer id, bad signature, mismatched offer fields, quantity
  out of bounds, underpayment, missing `invreq_amount` when `offer_amount` is
  absent, wrong arrival path, non-ASCII BIP 353 name.
* **T3:** positive fresh response; positive replay with issuer id and seen
  metadata; negatives for replay without issuer id and replay with fresh
  metadata. The state machine must not be total-reject.
* **T4:** positive proof from `integration_tests_rust.rs:4680-4696`;
  negatives for preimage mismatch, missing required field, malformed omitted
  markers, bad invoice signature, bad proof signature.
* **T5:** four pairwise-distinct fixed tags by `decide`; a collision-witness
  theorem that does not assert unconditional separation.
* **T6:** one-leaf and two-leaf roots; a permutation witness that is only
  proved under `BranchBinding` (or is explicitly left unproved).
* **T7:** structural `lnr` witness (5,000,000 msat, expiry 3600, quantity 1);
  expiry 0 as a server-policy negative, not a BOLT 12 rule.

## 6. Wave-13 recommendation

**Recommendation: implement a narrow T1–T4 lane only after an explicit scope
decision; fold T5 into T4 as a lemma; defer T6–T7; treat the rest as external.**

The reasons are:

1. **Scope is the first barrier.** Three documents state BOLT 12 is out of
   scope (`SCOPE.md:24`, `ASSUMPTIONS.md:144`, `Invoice.lean:98`). A wave
   cannot both leave those statements in place and claim BOLT 12 coverage. If
   the parent wants this lane, the scope decision must be recorded first; this
   report does not edit scope docs.
2. **The bounded slice is real and useful.** Offer admission (T1),
   invoice-request admission (T2), response binding/freshness (T3), and
   payer-proof binding (T4) can be stated over explicit records, reuse
   `Wire.TLV`, `Crypto.Hash.opensTo`, and the BIP-340/Schnorr substrate, and
   do not require a BOLT 12 wire codec. They close the most error-prone
   semantic gap: replay/freshness and preimage/signature binding.
3. **Merkle/selective disclosure is not ready.** The current C1 cannot
   discharge 64-byte branch hashing, and the model has no tree. T6 would
   require a new documented assumption (a TCB change), so it should be a
   separate decision, not an implementation detail.
4. **Refunds are an extension.** `lnr` is an LDK/rust-lightning extension, not
   a normative BOLT 12 stream in the pinned text. T7 should not be mixed into
   a BOLT 12 row.
5. **The external boundary is large.** bech32/HRP, onion-message transport,
   blinded-path ECDH, clock, currency conversion, and `invreq_metadata` RNG
   are all external. The lane must state them as assumptions, not model them
   by convenience.

If the parent greenlights the lane, the concrete plan is:

* Add `LnLean/Proofs/Payment/Bolt12Targets.lean` with `OfferView`,
  `InvoiceRequestView`, `Bolt12InvoiceView`, `PayerProofView`, the executable
  checkers, and T1–T4. Keep `Proven`/`Statement-only` distinctions explicit;
  do not add catalog rows until the declarations compile and are proved.
* Add a new gap ID such as `B12-01` to `docs/OPEN-ISSUES.md` ("BOLT 12
  offer/invoice-request/invoice/payer-proof surface unmodelled"), with
  sub-notes for Merkle (`B12-01a`) and refunds (`B12-01b`) if the parent wants
  them tracked separately. No BOLT 12 row exists today.
* Leave T5 as a lemma inside T4, defer T6 until a branch-hash assumption is
  accepted, and defer T7 or file it under an LDK-extension note.
* Ask the docs owner to correct `ANCHORS-GENERATED.md:131`; do not edit it
  here.

**Parent choice:** `implement` the narrow T1–T4 lane if the scope decision is
made; otherwise `defer` the whole lane and record the external/human barrier.
Merkle/selective disclosure and refunds are `external`/deferred in either case.

## 7. Evidence and commands

Read-only inspection performed in `/home/ubuntu/ln-lean-repair` on
`repair/integrated`. No Lean, docs, scripts, tests, vendor, or other lanes'
reports were edited. No `lake build`, `cargo test`, or network fetch was run.

Pin verification:

```sh
git -C /tmp/opencode/ldk-refs/ldk-node rev-parse HEAD
# fa123fed131e27ecc420b77fa7086fcf1ddaebb8
git -C /tmp/opencode/ldk-refs/ldk-server rev-parse HEAD
# c17dc11dde38f88c53457039ddf30c6b90a63ba2
git -C refs/rust-lightning rev-parse HEAD
# fe4900930c6bd5786ec4203274d7cf312776a5a6
```

Lean surface checks:

```sh
rg -n "^(structure|inductive|def|abbrev|class) (Offer|InvoiceRequest|Bolt12Invoice|PayerProof|Refund|BlindedMessagePath|Merkle)" LnLean
# only LnLean/Proofs/Crypto/SchnorrProps.lean:267:def MerkleRootValid
# (a BIP-341 32-byte root predicate, not a BOLT 12 tree)
rg -n "Bolt12|bolt12|BOLT12" LnLean
# no matches
rg -n "Offer|InvoiceRequest|payer_proof|PayerProof|Refund|BOLT 12" LnLean --glob '*.lean'
# only "Offered" HTLC/BOLT 3 prose and Invoice.lean:98 (out of scope)
```

Documentation anchors:

```sh
rg -n "BOLT 12" docs/SCOPE.md docs/ASSUMPTIONS.md \
  LnLean/Payment/Invoice.lean docs/ANCHORS-GENERATED.md
# docs/SCOPE.md:24
# docs/ASSUMPTIONS.md:144
# LnLean/Payment/Invoice.lean:98
# docs/ANCHORS-GENERATED.md:131  (false positive)
```

LDK datapoints were read with `sed -n` / `rg -n` from:

* `/tmp/opencode/ldk-refs/ldk-node/src/payment/bolt12.rs`
* `/tmp/opencode/ldk-refs/ldk-node/tests/integration_tests_rust.rs`
* `/tmp/opencode/ldk-refs/ldk-node/Cargo.toml`
* `/tmp/opencode/ldk-refs/ldk-server/ldk-server/src/api/bolt12_send.rs`
* `/tmp/opencode/ldk-refs/ldk-server/ldk-server/src/api/bolt12_receive.rs`
* `/tmp/opencode/ldk-refs/ldk-server/ldk-server/src/api/bolt12_refund.rs`
* `/tmp/opencode/ldk-refs/ldk-server/ldk-server/src/api/bolt12_create_payer_proof.rs`
* `/tmp/opencode/ldk-refs/ldk-server/ldk-server/src/api/decode_offer.rs`
* `/tmp/opencode/ldk-refs/ldk-server/e2e-tests/tests/e2e.rs`
* `/tmp/opencode/ldk-refs/ldk-server/ldk-server/Cargo.toml`
* `refs/bolts/12-offer-encoding.md`
* `refs/rust-lightning/lightning/src/offers/payer_proof.rs`
* `refs/rust-lightning/lightning/src/offers/refund.rs`
* `refs/rust-lightning/lightning/src/offers/offer.rs`
* `refs/rust-lightning/lightning/src/offers/merkle.rs`

Lean substrate was read with `sed -n` / `rg -n` from:

* `LnLean/Wire/TLV.lean`
* `LnLean/Crypto/Model.lean`
* `LnLean/Crypto/Sig.lean`
* `LnLean/Crypto/Hash.lean`
* `LnLean/Proofs/Crypto/SchnorrProps.lean`
* `LnLean/Proofs/Crypto/Sha256Props.lean`
* `LnLean/Basic/Core.lean`
* `LnLean/Payment/Invoice.lean`
* `LnLean/Proofs/Payment/InvoiceWireTargets.lean`
* `LnLean/Proofs/Routing/RouteBlindingProps.lean`
* `docs/THEOREM-INDEX.md`
* `docs/OPEN-ISSUES.md`
* `agents/reports/swarm12/S12-POST-INTEGRATION-AUDIT.md` (`:55`: no new
  tractable P0/P1 proof lane was found in wave 12)

No claim in this report is backed by a differential test, a cargo run, or a
new Lean declaration. The report is a scoping artifact, not proof evidence.
