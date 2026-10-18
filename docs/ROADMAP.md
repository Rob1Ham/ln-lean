# Phase C Roadmap

**Status:** historical Phase-C plan, written after the wave-A scaffold. The
current counts live in `docs/THEOREM-INDEX.md`: after the proof-wave round the
tree has 48 tracked obligations (`LN-L1-*`, `LN-CR-*`, `LN-CH-*`, `LN-HT-*`,
`LN-PR-*`, `LN-RT-*`, `LN-PM-*`, `LN-SEC-*`), of which 29 are `proved` and 19
remain `statement-only`. The phase descriptions below remain the work
breakdown for the remaining rows; some individual row statuses in the prose
are older than the proof-wave promotions and should be read against the index.

This roadmap separates four kinds of work, because they have very different
costs:

1. **Mathlib work.** Finite sums, lists with decidable equality, and
   arithmetic over `Nat`/`Int` are already available in Lean core, but a
   full global conservation theorem over a list of channels needs ordered
   finite maps and sum lemmas. Phase C may add mathlib for these. Until
   then, the obligations stay parameterized over the concrete list model.
2. **L1 script bridge.** Properties about output scripts, CSV/CLTV, and
   penalty spends must be connected to `Bitcoin.Data.Script` and the
   `btc-lean` interpreter interface. This is a *bridge*, not a re-proof of
   Bitcoin consensus.
3. **Crypto assumptions.** C1--C8 remain hypotheses, never axioms. Phase C
   should make each use site name the assumption explicitly and add an axiom
   audit that prints the hypothesis set.
4. **Protocol/liveness proofs.** These need a fairness or partial-synchrony
   hypothesis and a model of message retransmission; they should come after
   the safety invariants are closed.

## 1. What needs mathlib

| Obligation(s) | Why mathlib helps | Fallback without mathlib |
|---|---|---|
| `LN-SEC-002` global conservation | Sums over a finite map of channels, with add/remove lemmas | Keep the list-of-ledgers model and prove by `List` induction |
| `LN-CH-002`, `LN-CH-003` commitment output algebra | Sorted lists, `Finset` sums, `Nat`/`Int` casts | Prove per-commitment with `List.sum` and `omega` |
| `LN-HT-003` HTLC amount conservation | Partition offered/received/trimmed sets | Model the partition as three explicit lists |
| `LN-PM-005` MPP running-total bound | Prefix sums and `List.scanl` lemmas | State over an explicit accumulator function |
| `LN-RT-005` CLTV accumulation | Folds over hop lists with `Nat` addition | Induct on the hop list |
| `LN-SEC-003` asynchronous safety | Invariant induction over an arbitrary schedule | Already finite-horizon in `SecurityGame`; prove by `Nat` induction |

Rule: do **not** add mathlib to the scaffold build. Add it only in a phase-C
branch after the existing 48-row build stays green, and keep the model
modules importable without it where possible.

## 2. What needs the L1 script bridge

These rows mention scripts or on-chain spends and should be proved against
`LnLean.Bitcoin.Seam` plus the `btc-lean` script interface, not against a
byte-string pattern match.

| Obligation(s) | Bridge target |
|---|---|
| `LN-L1-001` funding P2WSH | `LnLean.Bitcoin.fundingScriptPubKey`, `p2wsh`, witness-script hash |
| `LN-L1-004` `to_local` CSV/revocation | `LnLean.Bitcoin.toLocalScript` and `OP_CSV` semantics |
| `LN-L1-006` commitment base weight | BOLT 3 weight constants and `FeeRate.fee` |
| `LN-CH-002`, `LN-CH-003` output values/order | commitment output construction and sorting |
| `LN-CH-005` fee sufficiency | `FeeRate.fee` plus the `feeInsufficient` precondition |
| `LN-HT-002` timeout path | HTLC-timeout script and CLTV check |
| `LN-HT-006`, `LN-SEC-001`, `LN-SEC-005` penalty/double-spend/economics | penalty transaction inputs and both commitment outputs |
| `LN-SEC-006` watchtower bridge | `Watchtower` interface plus a timely L1 transaction hypothesis |

The bridge must keep the L1 assumptions from `docs/ASSUMPTIONS.md` §2
explicit: funding confirmation, common chain tip, and no deep reorg.

## 3. What stays a cryptographic assumption

No phase-C proof should try to prove these; they stay as named hypotheses on
the theorem.

| Assumption | Rows that depend on it |
|---|---|
| C1 SHA-256 collision/preimage resistance | `LN-CR-001`, `LN-HT-001`, `LN-PM-001`, `LN-PM-006` |
| C2 HASH160 collision resistance | `LN-L1-001`, `LN-CH-003` (P2WPKH/P2WSH scripts) |
| C3 ECDSA EUF-CMA | `LN-CR-002`, `LN-PR-003`, `LN-PM-002` |
| C4 Schnorr EUF-CMA | taproot-channel rows (future; not in the 48) |
| C5 ECDH | onion shared secrets, Noise (supporting `LN-RT-003`, `LN-RT-004`) |
| C6 HKDF-SHA256 | key derivation for `LN-RT-003`, `LN-RT-004` |
| C7 ChaCha20-Poly1305 | onion confidentiality (`LN-RT-003`) |
| C8 HMAC-SHA256 | `LN-CR-003`, `LN-RT-004`, gossip authentication (`LN-RT-006`) |

`LnLean.Security.Model.CryptoAssumptions` already records C1--C8 as
`Prop`-valued fields, and `CryptoAssumptions.toList` gives the metadata
catalog. Phase C should add one theorem-level use site per assumption so the
axiom audit can show exactly which primitive is assumed.

## 4. Suggested order of attack

The dependency order is **conservation -> HTLC -> revocation -> routing ->
liveness**. Each step should leave the build green and update
`docs/THEOREM-INDEX.md` / `docs/TRACEABILITY.md` in the same commit.

### Step 1: conservation

1. `LN-CH-001` is already proved for the four-bucket ledger. Lift it to the
   commitment view (`LN-CH-002`, `LN-CH-003`) and then to the global ledger
   (`LN-SEC-002`).
2. Keep `LN-CH-005` (fee) and `LN-CH-006` (reserve/dust) as preconditions on
   the transition relation; prove that rejected transitions cannot change the
   four buckets.
3. Next smallest step: add a `CommitmentView` with `toLocal`, `toRemote`,
   in-flight HTLCs, and fee, and prove
   `sum(outputs) + fee = funding` by list induction.

### Step 2: HTLC lifecycle

1. `LN-HT-001` and `LN-HT-002` are proved in the abstract record. Connect
   them to the wire messages (`LN-PR-004`) and to the HTLC script
   (`LN-HT-002`, bridge above).
2. Prove `LN-HT-003` (amount conservation) and `LN-HT-004` (unique id) over
   the live HTLC set.
3. Next smallest step: define the live-HTLC set as a `List` with a
   `Nodup` invariant on ids, then prove add/fulfil/fail preserve it.

### Step 3: revocation and penalty

1. `LN-HT-005` and `LN-HT-006` are proved as predicates. Connect them to
   per-commitment secret derivation (`chan_utils.rs:518`) and to the penalty
   transaction's two inputs.
2. Prove that a revoked commitment cannot be the current commitment and that
   the penalty path is available whenever the secret is known
   (`LN-SEC-005`, `LN-SEC-006`).
3. Next smallest step: add the per-commitment point/secret pair to
   `RevocationState` and prove the published point determines the old
   commitment number.

### Step 4: routing and onion

1. `LN-RT-001` is proved for the abstract route. Connect it to
   `get_route`/`Route` and prove `LN-RT-005` (CLTV accumulation) by list
   induction.
2. Prove `LN-RT-002` (`channel_update` timestamp monotonicity) and
   `LN-RT-006` (announcement validation), then the onion layer laws
   `LN-RT-003`/`LN-RT-004` under C7/C8.
3. Next smallest step: define `Route.cltvExpiryAt` as a fold and prove it is
   monotone along a connected route.

### Step 5: liveness

1. `LN-SEC-004` is proved for the abstract schedule. Add the message
   retransmission model (`LN-PR-005`) and prove that after GST a pending
   update is eventually delivered.
2. Prove `LN-SEC-003` (safety under an arbitrary asynchronous schedule) as a
   separate invariant, without the fairness hypothesis.
3. Keep `LN-SEC-005`/`LN-SEC-006` as economic assumptions: fee spikes and
   watchtower liveness are not safety theorems.
4. Next smallest step: instantiate `PartiallySynchronous` with a concrete
   `channel_reestablish` retransmission schedule and prove eventual delivery
   of one pending commitment.

## 5. Phase-C exit criteria

* All 48 ids have either a `sorry`-free theorem or an explicit, documented
  assumption/`UNANCHORED` status; no silent weakening.
* `docs/THEOREM-INDEX.md` and `docs/TRACEABILITY.md` are regenerated from the
  Lean catalog and agree on ids, statuses, and targets.
* An axiom audit shows only the Lean kernel axioms plus the named C1--C8
  hypotheses at each use site.
* The L1 bridge names its confirmation and reorg hypotheses; it does not
  re-prove Bitcoin consensus.
* A clean checkout builds the phase-C target with the shared lock, and every
  report matches the tree.
