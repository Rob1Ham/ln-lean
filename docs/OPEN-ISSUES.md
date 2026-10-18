# Open Issues and Swarm Roadmap

**Status:** living roadmap after proof-wave 3.
**Branch:** `repair/integrated`.
**Base commit:** `47189fe` (wave 4 launch; proof-wave 3 code at `0c99c92`).
**Catalog gate:** 48/48 rows `proved`, 0 `statement-only`, 0 unresolved.
**Full build:** 182 jobs, RC 0.
**Rule:** this file is updated by every wave. Closed issues keep their id and
get a `closed` row; new gaps get a new id in the same wave that discovers them.

The catalog is green, but the catalog is a model-level claim. The issues below
are the remaining distance between this tree and a credible public release or
a full Lightning verification claim. Do not turn an assumption into a theorem
by rewording it; add the missing model or keep the scope note.

## Priority summary

| Priority | Meaning | Current issues |
|---|---|---|
| **P0** | Blocks a public release or a reproducible build | `OPS-01`, `OPS-02`, `OPS-03` |
| **P0** | Blocks any claim of spendable L1 scripts | `L1-01`, `L1-02`, `L1-03` |
| **P1** | Major model/verification gap; codeable in a wave | `L1-04`, `L1-05`, `PR-01`, `PR-02`, `CH-01`, `CH-02`, `HT-01`, `RT-01` |
| **P2** | Longer-term research / conformance / network assumptions | `CR-01`, `L1-06`, `NET-01`, `CONF-01`, `MODEL-01`, `MODEL-02`, `SEC-01` |

## Open issues

| Id | Priority | Status | Issue | Evidence / current boundary | Next action |
|---|---|---|---|---|---|
| `OPS-01` | P0 | open | Public CI cannot run the full build | `vendor/btc-lean-core` is gitignored and its pinned snapshot `f950806` is not in public `btc-lean` history; CI skip-gates the build | Choose a vendor packaging policy: commit a checksummed snapshot, fetch a public ancestor, or publish a separate vendor artifact; then remove the skip gate |
| `OPS-02` | P0 | open | No `LICENSE` | No license file in the tree | Maintainer chooses the license and adds `LICENSE`; do not let an agent invent one |
| `OPS-03` | P0 | open | No release tag and `main` is behind | `origin/main` is old; `repair/integrated` is the active branch; no tag | Decide PR/merge path to `main`, cut a signed/annotated tag, and publish release notes |
| `L1-01` | P0 | open | P2WSH / `OP_CHECKMULTISIG` spendability is not bridged | `LN-L1-001` proves the output format and hash commitment; no interpreter or consensus-spend theorem | Build a P2WSH/`OP_CHECKMULTISIG` bridge against the vendored script interface, or prove the strongest conditional spend theorem with explicit interpreter semantics |
| `L1-02` | P0 | open | `to_local` CSV/revocation script is structural only | `LN-L1-004` proves the full two-branch byte template and commitment; `OP_IF`, `OP_CSV`, `OP_DROP`, `OP_CHECKSIG` have no execution semantics | Add script execution/CSV/signature semantics or a formal interpreter bridge; keep the structural theorem |
| `L1-03` | P1 | open | `FundingScriptHashLinked` is a construction invariant | `LN-L1-001` assumes `witnessScriptHash = H(witnessScript.bytes)`; the model does not construct it end-to-end | Add the funding-state constructor that establishes the link, or derive it from the funding handshake |
| `L1-04` | P1 | open | Anchor weight has an 8 WU spec/serialization gap | `LN-L1-006` proves `serializedAnchorWeight + 8 = 1124 + 172*k`; witness serialization and the Appendix A `count_tx_out` discrepancy remain | Model the missing witness/CompactSize bytes or document the negotiated fee-basis interpretation permanently |
| `L1-05` | P1 | open | C1 is 32-byte payment-preimage collision resistance, not 71-byte script injectivity | `c1_32_does_not_bind_funding_witnessScripts`; the P2WSH reverse direction uses a finite pair-level `CollisionFreeOn` admission | Keep the finite admission and add a construction lemma for the actual revealed script; do not assume global injectivity |
| `L1-06` | P2 | open | Reorg result is conditional on common tip and bounded depth | `LN-L1-003` keeps `SameChain`, common-prefix arithmetic, and `OutOfReachOf` explicit; deep reorgs have a separate failure mode | Connect the hypotheses to the L1 chain model or leave the conditional theorem as the deliverable |
| `CR-01` | P2 | open | No computational cryptographic reductions | C1/C3/C8 are exact algebraic laws; no collision-finding, EUF-CMA, PRF, or advantage bounds | Write a limits document and, if desired, a separate computational-security development; do not claim reductions from the algebraic model |
| `PR-01` | P1 | open | `FundingSigningLaw` / `KeyBinding` are hypotheses | `LN-PR-003` proves validity and attribution only under explicit signing correctness and key binding; C3 alone is insufficient | Construct an honest signer in the primitive model and connect `accept_channel.funding_pubkey` to the signer key |
| `PR-02` | P1 | open | `CommitmentSigned` wire record lacks data for wire-only coverage | `LN-PR-004` needs per-output signed data and commitment value equations; commitment number/digest, per-HTLC sighash, HTLC identifiers/amounts, and fee are absent | Extend the wire/state model with commitment number/digest and per-HTLC signed fields; prove coverage without the bridge hypotheses |
| `CH-01` | P1 | open | Rich `CommitmentTx` model is not the legacy consumer path | `LN-CH-003` is proved for `CommitmentTx`; legacy `Commitment.commitmentOutputs` remains unsorted/unfiltered and is refuted by D12 | Migrate legacy consumers to the rich model or prove a refinement theorem from `CommitmentTx` to the legacy view |
| `CH-02` | P1 | open | Second-stage fee and dust trimming are not integrated end-to-end | The rich model and D12 cover trimming; second-stage fee computation and the single-anchor exception remain documented integration work | Add the second-stage fee function and prove conservation/trimming through the full commitment construction |
| `HT-01` | P1 | open | Global HTLC id uniqueness is false under BOLT 2 per-sender counters | `LN-HT-004` is per-sender (`dir_id_unique`); global form needs `CrossDisjoint`; `reachable_cross_direction_duplicate` is a counterexample | Add a direction-tagged or channel-wide id namespace if a global claim is required, or keep the per-sender semantics |
| `RT-01` | P1 | open | Gossip key attribution and raw insertion are separate | `LN-RT-006` covers reachable `admitGossip` states; raw `applyGossip` is unfiltered; G19 key attribution is not proved | Add `updateKeyAnnounced`/`KeyAttribution` to admission and prove the graph/view invariant over it |
| `NET-01` | P2 | open | Network/liveness results depend on scheduling/fairness assumptions | `LN-SEC-003` keeps four `Assumptions P`; `LN-SEC-005` uses `FeeScheduleBounded`; `LN-SEC-006` requires a watchtower report | State the adversarial schedule/fairness model explicitly and prove one concrete eventual-delivery instance |
| `CONF-01` | P2 | open | No differential conformance against BOLT vectors or rust-lightning | The tree has model tests and anchors, not a conformance runner | Add a conformance-vector lane for wire/TLV/BigSize/commitment encodings and compare against pinned fixtures |
| `MODEL-01` | P2 | open | No script interpreter / consensus semantics | Scripts are byte templates; sighash, witness, and signature execution are outside the model | Treat as a separate L1 bridge project; do not claim script spendability from the byte templates |
| `MODEL-02` | P2 | open | HTLC state-machine coverage is partial | `LN-CH-101`: no `Step.update_add_htlc` constructor; E37 models affordability on successor functions | Add the missing transition or explicitly scope the state machine to the modelled transitions |
| `SEC-01` | P2 | open | No end-to-end game-based security proof for the full protocol | The tree has invariant, conservation, and conditional security theorems, not a cryptographic game reduction | Keep separate from catalog cleanup; define the game and assumptions before claiming a reduction |

## Wave 4 lanes

These are the eight lanes launched after the proof-wave 3 checkpoint. Each lane
owns disjoint files and writes a report under `agents/reports/swarm4/`.

| Lane | Issue(s) | Scope | Owned files |
|---|---|---|---|
| `S4-L1-SPEND` | `L1-01`, `L1-02` | P2WSH/`OP_CHECKMULTISIG` and `to_local` execution bridge; conditional spend theorems if the interpreter is incomplete | `LnLean/Bitcoin/Seam.lean`, new `LnLean/Proofs/Bitcoin/SpendTargets.lean` |
| `S4-VENDOR-CI` | `OPS-01` | Make the public CI build reproducible: vendor artifact policy, checksums, skip-gate removal, docs | `.github/workflows/ci.yml`, `scripts/`, `docs/OPEN-ISSUES.md` (OPS-01 only), vendor policy docs |
| `S4-CONFORMANCE` | `CONF-01` | Add BOLT/rust-lightning conformance fixtures for wire/TLV/BigSize/commitment encodings | `tests/conformance/`, `scripts/`, new `LnLean/Proofs/ConformanceTargets.lean` |
| `S4-PR-WIRE` | `PR-02` | Extend `CommitmentSigned`/commitment state with number/digest/per-HTLC signed data; remove bridge assumptions where possible | `LnLean/Protocol/Messages.lean`, new `LnLean/Proofs/ProtocolWireTargets.lean` |
| `S4-HTLC-GLOBAL` | `HT-01` | Direction-tagged/channel-wide id model and global uniqueness, or a scoped refinement theorem | `LnLean/Channel/HTLC.lean`, new `LnLean/Proofs/Channel/HtlcGlobalIdTargets.lean` |
| `S4-FEE-DUST` | `CH-01`, `CH-02` | Second-stage fee, dust/trim, refinement from `CommitmentTx` to legacy consumers | `LnLean/Channel/Commitment.lean`, new `LnLean/Proofs/Channel/CommitmentIntegrationTargets.lean` |
| `S4-GOSSIP-ATTR` | `RT-01` | `updateKeyAnnounced`/`KeyAttribution` in gossip admission; raw-store guard | `LnLean/Routing/Gossip.lean`, new `LnLean/Proofs/Routing/GossipAttributionTargets.lean` |
| `S4-RELEASE` | `OPS-02`, `OPS-03` | License/tag/PR/release-note preparation; no license choice without maintainer approval | `README.md`, `docs/`, `.github/`, release notes |

## Wave update protocol

1. At the start of a wave, the parent updates this file with the selected lane
   table and the base commit.
2. Each lane gets exclusive files and a report path; lanes do not touch
   `Obligations.lean`, `Traceability.lean`, root imports, Git history, or the
   shared catalog unless explicitly assigned.
3. A lane that cannot prove the target must record the exact missing model or
   assumption and retain a counterexample/negative theorem. A blocked lane is a
   successful result if it narrows the gap faithfully.
4. The parent integrates only faithful, sorry-free results. It updates the
   catalog, traceability, generated indexes, this roadmap, and the gate record
   in one commit.
5. The gate is: full build, strict `check-catalog --audit`, `check.sh`,
   `check-final.py`, `verify-anchors.py`, `verify-vendor.sh`, and the exact
   `sorry` scan.
6. Push non-force to `origin/repair/integrated`; never overwrite `main` or
   another worker's branch.
7. Close issues in this file with the commit and theorem names. Add new gaps
   discovered by the wave in the same update. Then launch the next wave.

## Current gate evidence

| Check | Result |
|---|---|
| `lake build` | 182 jobs, RC 0 |
| `check-catalog.py --audit` | 48 proved / 0 statement-only / 0 unresolved / 0 proved failures |
| `check-catalog.py --allow-planned` | 48/0/0 planned, RC 0 |
| `check.sh` | `files=176 obligations=82 sorry_in_proofs=0`, RC 0 |
| `check-final.py` | 176 Lean files, 174 root imports, RC 0 |
| `verify-anchors.py` | 299 anchors, 0 bad, 2 unanchored rows, RC 0 |
| `verify-vendor.sh` | 119 files, RC 0 |
| Axiom audit | 79 audited theorems; only `propext`, `Quot.sound`, `Classical.choice` |
