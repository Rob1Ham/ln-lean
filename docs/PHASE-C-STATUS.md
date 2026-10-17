# Phase C status — first closure wave

**Branch:** `phase-c` (based on `b891a59`, merged into `main`)
**Worktree:** `/home/ubuntu/ln-lean-phasec`
**Agents:** PC01–PC16, one disjoint file each
**Gate:** full `lake build` green (77 jobs); `scripts/check.sh` OK

## Result

The first phase-C wave reduced the proof-side `sorry` count from **25 to 5**.
No model module (`LnLean/` outside `LnLean/Proofs/`) contains a `sorry`. The
five remaining sites are *not* missing arithmetic: each is an unconditional
statement that is **false in the wave-A model**, and each already has a
machine-checked counterexample plus the strongest true conditional form in
the same file.

| File | Before | After | Note |
|---|---:|---:|---|
| `Proofs/Conservation.lean` | 1 | 0 | erase-based settlement conservation |
| `Proofs/Bitcoin/FundingProps.lean` | 2 | 1 | refuted unconditional parse claim retained with counterexample + `_of_wellFormed` |
| `Proofs/Bitcoin/AnchorProps.lean` | 2 | 0 | anchor script/key injectivity |
| `Proofs/Bitcoin/ScriptProps.lean` | 3 | 0 | script-number/payment-hash/CLTV injectivity |
| `Proofs/Wire/TLVProps.lean` | 1 | 0 | canonical TLV round-trip |
| `Proofs/Crypto/Sha256Props.lean` | 1 | 0 | finite-image hash cardinality |
| `Proofs/Crypto/EcdsaProps.lean` | 2 | 0 | DER envelope/length refinement |
| `Proofs/Channel/HTLCProps.lean` | 2 | 0 | live-set commutation and total bound |
| `Proofs/Channel/ReserveProps.lean` | 1 | 1 | refuted unconditional ledger update retained with counterexample + `_of_le` |
| `Proofs/Channel/StateMachineProps.lean` | 1 | 0 | funding-locked path invariant |
| `Proofs/Protocol/ChannelReestablishProps.lean` | 2 | 0 | counter preservation and monotonicity |
| `Proofs/Protocol/FeaturesProps.lean` | 1 | 0 | intersection preserves acceptance |
| `Proofs/Routing/GraphProps.lean` | 1 | 0 | simple paths are walks |
| `Proofs/Routing/GossipProps.lean` | 3 | 3 | three refuted admission claims retained with counterexamples + conditional replacements |
| `Proofs/Payment/MPPProps.lean` | 1 | 0 | MPP running total |
| `Proofs/Payment/KeysendProps.lean` | 1 | 0 | keysend consistency |
| **Total** | **25** | **5** | |

## The five remaining sites

These are model-repair items, not proof-search items:

1. `FundingProps.witnessScript_parse_eq_none` — needs `p.WellFormed`
   (33-byte funding keys); counterexample and conditional proof present.
2. `ReserveProps.committed_update_preserves_ledger` — needs the
   non-truncation precondition on the local balance; counterexample and
   conditional proof present.
3. `GossipProps.accepted_update_signing_key_announced` — the wave-A model
   does not tie `signingKey` to the announcement; counterexample present.
4. `GossipProps.bindChannel_capacity_positive` — capacity is unconstrained
   in the wave-A admission predicate; counterexample present.
5. `GossipProps.accepted_update_signature_length` — signature verification
   is an abstract predicate with no length consequence; counterexample
   present.

Phase-C2 (`branch phase-c2`) repairs these claims by removing the refuted
unconditional statements while keeping the counterexamples and conditional
theorems, and adds independent proof modules for conservation, HTLC
partitioning, revocation/penalty, routing, MPP, liveness, and the four L1
script bridges.

## Reproduce

```sh
export PATH=/dev/shm/btc/elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
cd /home/ubuntu/ln-lean-phasec
flock -w 900 /tmp/ln-build.lock lake build
./scripts/check.sh
grep -Rho '\bsorry\b' LnLean --include='*.lean' | wc -l   # 5
```

Reports for every file are in `agents/reports/PC01.md` … `PC16.md`.
