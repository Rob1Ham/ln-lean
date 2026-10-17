# Phase-C3 lanes — end-to-end and security compositions

Third lane from the second box, disjoint from `phase-c` and `phase-c2`.

* Worktree: `/home/ubuntu/ln-lean-phasec3`
* Branch: `phase-c3`, based on `phase-c`
* New namespace: `LnLean/Proofs/PhaseC3/`
* No edits to existing files, `LnLean.lean`, `lakefile.lean`, `docs/`,
  `refs/`, or `vendor/`.

Each agent owns one new module and one report. The goal is composition, not
re-proving the wave-A/C lemmas: import the existing theorems and prove the
end-to-end or adversary-level statement, making every bridge hypothesis an
explicit structure field or theorem hypothesis.

| Agent | Output | Goal |
|---|---|---|
| PC37 | `PhaseC3/EndToEndConservation.lean` | L1 funding value + channel ledger + payment settlement conserves total value |
| PC38 | `PhaseC3/WatchtowerBreach.lean` | breach detection + penalty + timely L1 confirmation prevents loss |
| PC39 | `PhaseC3/FeeWeightDust.lean` | fee/weight/dust bounds imply non-negative, bounded commitment outputs |
| PC40 | `PhaseC3/InvoiceParser.lean` | BOLT 11 tag encode/decode round-trip on the modelled subset |
| PC41 | `PhaseC3/OnionError.lean` | failure-packet length, parse, and HMAC-binding composition |
| PC42 | `PhaseC3/PersistenceRecovery.lean` | persisted channel recovery preserves counters and ready state |
| PC43 | `PhaseC3/SecurityGame.lean` | an adversary win implies a primitive/L1 assumption failure |
| PC44 | `PhaseC3/CrossChannelRouting.lean` | a valid multi-hop route conserves amount/fee and increases CLTV |

`sorry` is allowed only with an adjacent `-- OBLIGATION: PC3-...` marker. At
least one named theorem per module must be fully proved. Reports go to
`agents/reports/PCxx.md`.
