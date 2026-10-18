# Wave status

`ln-lean` is a Lean 4 formal-model and proof **scaffold** for the Lightning
Network.  It is layered on a read-only snapshot of the existing `btc-lean`
Bitcoin L1 model.  It is not a completed proof of Lightning.

## Waves

| Wave | Agents | Purpose | Output |
|---|---:|---|---|
| A | 8 | executable model modules, one per domain | `LnLean/{Bitcoin,Crypto,Wire,Channel,Protocol,Routing,Payment,Security}/` |
| B | 32 | proof statements and obligation markers | `LnLean/Proofs/**` |
| C | 16 | close the remaining proof obligations, one file per agent | `wave-c/235` |
| D | 48 | independent proof attempts for 48 catalog targets | `wave-d/48` |
| E | 48 | second independent attempt for the same 48 targets | `wave-e/48` |
| F | 16 | model-hardening invariants and counterexamples | `wave-f/16` |
| G | 32 | read-only pairwise and cross-cutting audits | `wave-g/audit` |

Waves A, B, C, D, E and F are complete.  Wave G is complete at **32/32**
reports.  The final sparse tree is branch `final/integrated`, based on
`a9f8d87`.

## Final integrated status

- Lean files: **132** (69 base + 33 Wave-D + 15 Wave-E + 15 ModelHardening)
- Root imports: **132**
- Selected D/E slots: **48/48**, exactly one whole-file version per slot
- Selected F modules: **15** (`F10` excluded)
- Obligation markers: **95**, 0 duplicate ids
- Catalog rows: **48** (13 `proved`, 35 `statementOnly`)
- Real `sorry` sites: **15**
- Exact/final full build: **140 jobs, RC 0**
- Vendor snapshot: **OK, 119 files**
- Anchors: **288 checked, 0 bad**
- `check.sh`: **OK**
- Final selection manifest: `agents/status/FINAL-SELECTION.md`

The selection keeps D14 and excludes E14 because both declare
`LnLean.Channel.Reserve.bounds` with incompatible statements.  It keeps E37
(no `sorry`), E39 (guarded capacity), and E40 (one marked `sorry` plus a
proved conditional/iff companion).  D41–D48 and E45/E48 are annex/refinement
modules, not second closures of their catalog IDs.

## Open obligations

The final tree deliberately keeps the false or underspecified unconditional
statements, each with an adjacent marker and a proved conditional or
counterexample companion:

| Site | Marker | Reason |
|---|---|---|
| `FundingProps` | `LN-FUND-001` | false without the well-formed/range hypothesis |
| `ReserveProps` | `LN-CH-101` | false without an affordability guard |
| `GossipProps` | `LN-GOSSIP-001` … `003` | raw gossip admission is unconstrained |
| `WaveE/E40` | `LN-WE-E40` | false unconditional signature-length admission |
| `F03` | `LN-WF-F03` | commitment conservation/anchor model gap |
| `F04` | `LN-WF-F04` | legacy anchor debit overfunds |
| `F05` | `LN-WF-F05` | unannounced gossip update keys |
| `F06` | `LN-WF-F06` | zero-capacity gossip admission |
| `F07` | `LN-WF-F07` | missing length-respecting verifier contract |
| `F09` | `LN-WF-F09` | dust trimming and fee accounting |
| `F13` | `LN-WF-F13` | invoice preimage binding |
| `F14` | `LN-WF-F14` | MPP running-total bound |
| `F15` | `LN-WF-F15` | settlement preimage reveal |

The catalog's 13 proved rows are against the small security models.  A
statement-only row is a tracked future theorem, not a result.

## Known non-closures

These targets are recorded as conditional, negative, or blocked, not closed:

- `LN-L1-004`: `toLocalScript` is a flat seam fragment, not the full BOLT 3
  two-branch witness script.
- `LN-PR-004`: both D20/E20 are negative/conditional.
- `LN-SEC-003`: the named catalog declaration does not exist.
- `LN-SEC-005`: D34's at-stake field is post-fee; the uneconomical-penalty
  counterexample is withdrawn.
- `LN-CH-101`: there is no `Step.update_add_htlc` constructor; E37 models the
  affordability arithmetic on successor functions.
- `LN-GOSSIP-002`: the raw `applyGossip` path remains unguarded; E39 proves
  the guarded store result.
- `LN-FUND-001` and `LN-GOSSIP-001/003`: the base Wave-C `sorry` sites remain.

## Reproduce

```sh
export PATH=/dev/shm/btc/elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
cd /home/ubuntu/ln-lean-final

python3 scripts/check-final.py
./scripts/verify-vendor.sh
python3 scripts/verify-anchors.py
./scripts/check.sh
./scripts/regen-root.sh
flock -w 1800 /tmp/ln-build.lock lake build
python3 scripts/collect-obligations.py
python3 scripts/collect-anchors.py
```

## Integrity

* `vendor/btc-lean-core/` is a snapshot of `btc-lean` `spec/core` at
  `f95080638ae571a3664f4f41b9b6f6b4cfa7c5eb`.  Source files are mode
  `0444`; `vendor/VENDOR-SHA256` is versioned and checked by
  `scripts/verify-vendor.sh`.  The Bitcoin L1 proofs are not copied or
  modified.
* `refs/rust-lightning` is pinned at
  `fe4900930c6bd5786ec4203274d7cf312776a5a6`.
* `refs/bolts` is pinned at
  `1aadb719b4007c4cea0ba6e36b08c4fb53788dee`.

## Honest status

An obligation is a named claim, not a proof.  A module may contain
`sorry` only under `LnLean/Proofs/` and only with a
`-- OBLIGATION: LN-...` marker (or the structured catalog in
`LnLean/Proofs/Obligations.lean`).  Cryptographic correctness is
conditional on the `Prop` fields in the primitive model; it is never
asserted as an axiom.  `docs/THEOREM-INDEX.md` and
`docs/OBLIGATIONS-GENERATED.md` are the status views.
