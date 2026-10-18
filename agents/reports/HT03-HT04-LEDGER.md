# HT03-HT04-LEDGER — exact catalog targets and their scope

**Lane:** HT-LEDGER
**Repository:** `/home/ubuntu/ln-lean-repair`
**Branch:** `repair/integrated`
**HEAD at work start:** `0caec3d` (`[STATUS] clarify remote-ref provenance`)
**Lean file touched:** `LnLean/Channel/HTLC.lean`
**Report:** `agents/reports/HT03-HT04-LEDGER.md`
**Date:** 2026-10-18

## 1. Result

The two catalog target names now exist and are proved:

| Row | Catalog `leanTarget` | Declared as | Availability |
|---|---|---|---|
| `LN-HT-003` | `LnLean.Channel.HTLC.amount_conservation` | exact name | proved, ledger-conditional |
| `LN-HT-004` | `LnLean.Channel.HTLC.id_unique` | exact name | proved, `Nodup`-conditional |

Both are direct restatements of H01's theorems:

* `LnLean.Channel.HTLC.amount_conservation` is exactly
  `LnLean.Channel.htlcValue_conservation_of_ledger`.
* `LnLean.Channel.HTLC.id_unique` is exactly
  `LnLean.Channel.liveHtlcIdsNodup_unique`.

The hypotheses were not weakened, hidden, or moved into the statement text.
This is intentionally an exact-name exposure of H01, not a new unconditional
claim.  Neither theorem is a tautology: each has a substantive conservation /
uniqueness conclusion, and each keeps the invariant it needs as a named
hypothesis.

## 2. Change to `LnLean/Channel/HTLC.lean`

Additive only; all earlier declarations and comments are unchanged.  The two
declarations are placed in a nested `namespace HTLC` at the end of the file so
that the catalog strings with the module name as a namespace resolve literally.
No `namespace HTLC` existed before, and no earlier name changed.

### 2.1 `LN-HT-003`

```lean
namespace HTLC

theorem amount_conservation
    (dustLimit timeoutFee successFee ledger funding : Nat)
    (hs : List HTLCRecord)
    (hledger : ledger + totalHtlcValue (htlcSet hs) = funding) :
    ledger + totalHtlcValue (htlcOffered dustLimit timeoutFee successFee hs) +
        totalHtlcValue (htlcReceived dustLimit timeoutFee successFee hs) +
        totalHtlcValue (htlcTrimmed dustLimit timeoutFee successFee hs) =
      funding :=
  htlcValue_conservation_of_ledger dustLimit timeoutFee successFee ledger funding
    hs hledger
```

`ledger` is the catalog's "balances and fee" total.  `hledger` is the explicit
channel-ledger invariant that the module cannot derive: `HTLCRecord` has no
balance, fee, or funding field, and `LnLean.Channel.HTLC` defines no channel
record owning them.  The docstring says this and points at the checked
counterexample `waveD_d15_without_balance_invariant_false` in
`LnLean.Proofs.WaveD.D15`, where the equation fails if the ledger premise is
dropped.

### 2.2 `LN-HT-004`

```lean
theorem id_unique (hs : List HTLCRecord)
    (hnd : liveHtlcIdsNodup hs) :
    ∀ h1 ∈ htlcSet hs, ∀ h2 ∈ htlcSet hs, h1.id = h2.id → h1 = h2 :=
  liveHtlcIdsNodup_unique hs hnd

end HTLC
```

`hnd` is the live-id distinctness invariant.  It is not automatic in this
model: `liveHtlcIdsNodup_unconditional_false` constructs two distinct live
records with id `0`, and `addHTLC_same_id_distinct_amounts_ok` shows that
`addHTLC` accepts a reused id.  Both counterexamples remain in the file
untouched.  The docstring therefore does not claim the unconditional catalog
wording.

## 3. Verification

All commands were run from `/home/ubuntu/ln-lean-repair` with

```bash
export PATH=/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock <command>
```

One Lean process at a time; `lake build -j1` was not used (this Lake rejects
`-j`).

| Command | RC | Output |
|---|---|---|
| `lake env lean LnLean/Channel/HTLC.lean` | 0 | no diagnostics |
| `lake build LnLean.Channel.HTLC` | 0 | `✔ [9/9] Built LnLean.Channel.HTLC (835ms)` / `Build completed successfully (9 jobs).` |

A scratch file outside the repository,
`/tmp/opencode/btc-lean/HT03HT04Check.lean`, contains the `#check` and
`#print axioms` commands:

```lean
import LnLean.Channel.HTLC

#check LnLean.Channel.HTLC.amount_conservation
#check LnLean.Channel.HTLC.id_unique
#print axioms LnLean.Channel.HTLC.amount_conservation
#print axioms LnLean.Channel.HTLC.id_unique
#check LnLean.Channel.liveHtlcIdsNodup_unconditional_false
#print axioms LnLean.Channel.liveHtlcIdsNodup_unconditional_false
```

`lake env lean /tmp/opencode/btc-lean/HT03HT04Check.lean` returned **RC 0** with
the following output (verbatim):

```text
LnLean.Channel.HTLC.amount_conservation (dustLimit timeoutFee successFee ledger funding : Nat)
  (hs : List LnLean.Channel.HTLCRecord)
  (hledger : ledger + LnLean.Channel.totalHtlcValue (LnLean.Channel.htlcSet hs) = funding) :
  ledger + LnLean.Channel.totalHtlcValue (LnLean.Channel.htlcOffered dustLimit timeoutFee successFee hs) +
        LnLean.Channel.totalHtlcValue (LnLean.Channel.htlcReceived dustLimit timeoutFee successFee hs) +
      LnLean.Channel.totalHtlcValue (LnLean.Channel.htlcTrimmed dustLimit timeoutFee successFee hs) =
    funding
LnLean.Channel.HTLC.id_unique (hs : List LnLean.Channel.HTLCRecord) (hnd : LnLean.Channel.liveHtlcIdsNodup hs)
  (h1 : LnLean.Channel.HTLCRecord) :
  h1 ∈ LnLean.Channel.htlcSet hs →
    ∀ (h2 : LnLean.Channel.HTLCRecord), h2 ∈ LnLean.Channel.htlcSet hs → h1.id = h2.id → h1 = h2
'LnLean.Channel.HTLC.amount_conservation' depends on axioms: [propext, Quot.sound]
'LnLean.Channel.HTLC.id_unique' depends on axioms: [propext, Quot.sound]
LnLean.Channel.liveHtlcIdsNodup_unconditional_false :
  ¬∀ (hs : List LnLean.Channel.HTLCRecord), LnLean.Channel.liveHtlcIdsNodup hs
'LnLean.Channel.liveHtlcIdsNodup_unconditional_false' depends on axioms: [propext]
```

The axiom reports contain only Lean's standard `propext` and `Quot.sound`;
there is no `sorryAx`, and no `Classical.choice`.

Token scan of `LnLean/Channel/HTLC.lean` for `sorry`, `axiom`, `admit`,
`native_decide`, `unsafe`, and `implemented_by` returns no matches.

`git diff -- LnLean/Channel/HTLC.lean` contains only the additive block shown in
§2.  `git status` also lists `LnLean/Channel/Commitment.lean`,
`LnLean/Proofs/Liveness.lean`, and `agents/status/REPAIR.status` as dirty; those
belong to other lanes and were not touched.  No add, commit, push, or revert was
performed.

## 4. Scope caveats

Both caveats are part of the delivered statements, not footnotes:

1. **`amount_conservation` is not a balance/fee/funding theorem about the
   model.**  The model has no such fields, so the ledger premise
   `hledger : ledger + totalHtlcValue (htlcSet hs) = funding` is assumed.  The
   theorem proves only that, given the ledger invariant, the live HTLC value
   partitions into offered + received + trimmed and stays within `funding`.
   Removing `hledger` makes the claim false (D15 counterexample).
2. **`id_unique` is not unconditional uniqueness.**  The live-id distinctness
   invariant `hnd : liveHtlcIdsNodup hs` is assumed.  The unconditional claim is
   false: two distinct live records may carry the same id, and `addHTLC` does
   not check for freshness.  Establishing `hnd` needs a channel record with
   per-sender id counters or an explicit state invariant, neither of which is in
   this module.

## 5. Promotion verdict

| Row | Verdict | Reasoning |
|---|---|---|
| `LN-HT-003` | **not promotion-ready as worded; conditional target proved** | The exact name now resolves and is proved, but only under the explicit ledger hypothesis. The catalog wording says "plus balances and fee equal the funding value" as an unconditional channel fact. Since `HTLCRecord` has no balance/fee/funding field, promoting to `status := .proved` would overstate the model. Keep `statementOnly` unless the claim is explicitly reworded as ledger-conditional or the row is repointed at D15's commitment model. |
| `LN-HT-004` | **not promotion-ready as worded; conditional target proved** | The exact name now resolves and is proved under `liveHtlcIdsNodup`. The catalog wording asserts uniqueness without a hypothesis, which is false in this model (same-id live records are constructible). Keep `statementOnly` unless the claim is reworded to include live-id distinctness, restricted to per-direction uniqueness, or repointed at D16's counter model. |

No catalog file was edited in this lane, so the statuses remain
`statementOnly`.  The delivered value is that the exact catalog names now exist,
compile, and carry their true hypotheses transparently; they can be promoted
only together with a claim rewording or a model extension that discharges the
hypotheses.
