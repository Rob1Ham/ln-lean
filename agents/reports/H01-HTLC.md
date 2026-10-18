# H01-HTLC — LN-HT-003 / LN-HT-004 proof lane

**Lane:** H01-HTLC
**Repository:** `/home/ubuntu/ln-lean-repair`
**Branch:** `repair/integrated`
**Lean file touched:** `LnLean/Channel/HTLC.lean`
**Report:** `agents/reports/H01-HTLC.md`
**Date:** 2026-10-18

## 1. Scope and result

The two catalog rows are:

| Row | Catalog claim | Catalog `leanTarget` | Current status |
|---|---|---|---|
| `LN-HT-003` | Offered, received, and trimmed HTLC amounts plus balances and fee equal the funding value. | `LnLean.Channel.HTLC.amount_conservation` | `statementOnly` |
| `LN-HT-004` | An HTLC id is unique within the live HTLC set of a channel. | `LnLean.Channel.HTLC.id_unique` | `statementOnly` |

Neither exact target was added. Both claims are **not unconditionally true in
the current model**, so adding the catalog names would make a later
`status := .proved` change unsound:

* `HTLCRecord` has no balance, fee, or funding field. The model module also has
  no channel/ledger record that owns them.
* `HTLCRecord` has no id counter and the state has no distinctness invariant.
  `List HTLCRecord` may contain two distinct live records with the same id, and
  BOLT 2's actual rule (one monotone counter per sender) permits that shape.

Instead the model module gained fresh-name theorems that are the strongest
true statements in the existing vocabulary. They are intended as the exact
HTLC-level lemmas a future ledger/counter extension will wrap.

**Verdicts:** `LN-HT-003` = **model-gap**; `LN-HT-004` = **model-gap**
(unconditional form false, conditional/list invariant proved). Neither row is
promotion-ready. Details in §7.

Naming note: the catalog writes `LnLean.Channel.HTLC.amount_conservation`, but
`HTLC` is the *module* name. A declaration placed in this module is
`LnLean.Channel.amount_conservation`, because the file opens
`namespace LnLean.Channel`. The same applies to `id_unique`
(`LnLean.Channel.id_unique`). No `namespace HTLC` exists or was introduced.

## 2. What the model provides

`LnLean/Channel/HTLC.lean` contains:

* `HTLCRecord` with `id : Nat`, `direction`, `amountMsat : Msat`,
  `paymentHash`, `cltvExpiry`, `state`;
* `htlcSet hs = hs.filter HTLCRecord.isLive`;
* `totalHtlcValue hs = (hs.map (fun h => h.amountMsat.val)).sum`;
* `htlcOutputValue`, `secondStageFee`, `isDustHTLC`, `hasOutput`;
* `addHTLC`, `fulfillHTLC`, `failHTLC`, `timeoutHTLC`, `removeHTLC`.

It imports only `LnLean.Basic.Core` and `LnLean.Bitcoin.Seam`. `Balance`,
`Channel`, and `Commitment` live in `LnLean.Channel.Types`; that module does not
import `HTLC.lean`, so the layering permits a future import, but it was not
needed for the fresh-name results below and was deliberately not added.

`addHTLC` takes the id as a caller-supplied argument and never receives the
existing record list. `removeHTLC` changes only the lifecycle tag; there is no
list-level "replace this record" operation in this module.

## 3. LN-HT-003 — amount partition and the missing ledger

### 3.1 Why no exact theorem

The catalog wording mentions **balances**, **fee**, and the **funding value**.
None is a field of `HTLCRecord`, and `LnLean.Channel.HTLC` defines no record
that binds a `List HTLCRecord` to them. Any unconditional equation in this
module would therefore be fabricated.

`LnLean.Proofs.WaveD.D15` already proves the conditional commitment-level
statement `waveD_d15_amount_conservation` over an explicit `Balance`, a
`Commitment`, and the invariant
`b.localBalance.val + b.remoteBalance.val + htlcAmountSum (htlcSet hs) = funding.val`.
D15 also proves
`waveD_d15_without_balance_invariant_false`, a checked counterexample showing
the equation fails when that invariant is dropped. Those results are
proof-level and conditional; they do not justify an unconditional
`LnLean.Channel.amount_conservation`.

### 3.2 Added definitions (fresh names)

```lean
def htlcUntrimmed (dustLimit timeoutFee successFee : Nat)
    (hs : List HTLCRecord) : List HTLCRecord :=
  (htlcSet hs).filter (fun h => !isDustHTLC h dustLimit timeoutFee successFee)

def htlcOffered (dustLimit timeoutFee successFee : Nat)
    (hs : List HTLCRecord) : List HTLCRecord :=
  (htlcUntrimmed dustLimit timeoutFee successFee hs).filter
    (fun h => decide (h.direction = Direction.local))

def htlcReceived (dustLimit timeoutFee successFee : Nat)
    (hs : List HTLCRecord) : List HTLCRecord :=
  (htlcUntrimmed dustLimit timeoutFee successFee hs).filter
    (fun h => decide (h.direction = Direction.remote))

def htlcTrimmed (dustLimit timeoutFee successFee : Nat)
    (hs : List HTLCRecord) : List HTLCRecord :=
  (htlcSet hs).filter (fun h => isDustHTLC h dustLimit timeoutFee successFee)
```

### 3.3 Added theorems

```lean
theorem htlc_filter_direction_perm (l : List HTLCRecord) :
    List.Perm
      (l.filter (fun h => decide (h.direction = Direction.local)) ++
        l.filter (fun h => decide (h.direction = Direction.remote))) l

theorem htlcSet_partition_perm (dustLimit timeoutFee successFee : Nat)
    (hs : List HTLCRecord) :
    List.Perm
      (htlcOffered dustLimit timeoutFee successFee hs ++
        htlcReceived dustLimit timeoutFee successFee hs ++
        htlcTrimmed dustLimit timeoutFee successFee hs) (htlcSet hs)

theorem totalHtlcValue_partition (dustLimit timeoutFee successFee : Nat)
    (hs : List HTLCRecord) :
    totalHtlcValue (htlcSet hs) =
      totalHtlcValue (htlcOffered dustLimit timeoutFee successFee hs) +
        totalHtlcValue (htlcReceived dustLimit timeoutFee successFee hs) +
        totalHtlcValue (htlcTrimmed dustLimit timeoutFee successFee hs)

theorem htlcValue_conservation_of_ledger
    (dustLimit timeoutFee successFee ledger funding : Nat)
    (hs : List HTLCRecord)
    (hledger : ledger + totalHtlcValue (htlcSet hs) = funding) :
    ledger + totalHtlcValue (htlcOffered dustLimit timeoutFee successFee hs) +
        totalHtlcValue (htlcReceived dustLimit timeoutFee successFee hs) +
        totalHtlcValue (htlcTrimmed dustLimit timeoutFee successFee hs) =
      funding

theorem htlcOutputValue_add_secondStageFee (h : HTLCRecord)
    (timeoutFee successFee : Nat)
    (hfee : secondStageFee h.direction timeoutFee successFee ≤
      Msat.toSatFloor h.amountMsat) :
    htlcOutputValue h timeoutFee successFee +
        secondStageFee h.direction timeoutFee successFee =
      Msat.toSatFloor h.amountMsat

theorem secondStageFee_le_of_not_dust (dustLimit timeoutFee successFee : Nat)
    (hdust : 0 < dustLimit) {h : HTLCRecord}
    (hnd : isDustHTLC h dustLimit timeoutFee successFee = false) :
    secondStageFee h.direction timeoutFee successFee ≤
      Msat.toSatFloor h.amountMsat
```

### 3.4 Proof approach

* `htlc_filter_direction_perm` is `List.filter_append_perm` with the complement
  of `direction = local` rewritten to `direction = remote` by case analysis on
  `Direction`.
* `htlcSet_partition_perm` concatenates the direction split of
  `htlcUntrimmed` with the dust split of `htlcSet`; both are `List.Perm`
  statements, so the result follows by `Perm.append_right` and `Perm.trans`.
* `totalHtlcValue_partition` maps `amountMsat.val` over the permutation and
  applies `List.Perm.sum_nat`; the definitional unfolding of
  `totalHtlcValue` is the only rewriting needed.
* `htlcValue_conservation_of_ledger` is `omega` over the partition identity;
  **the only non-model ingredient is the explicitly named hypothesis
  `hledger`**.
* `htlcOutputValue_add_secondStageFee` is `Nat.sub_add_cancel` on
  `htlcOutputValue = floor(amount) - fee`.
* `secondStageFee_le_of_not_dust` turns `isDust = false` into
  `dustLimit ≤ htlcOutputValue` via `hasOutput_iff`, then uses
  `0 < dustLimit` and `omega`.

## 4. LN-HT-004 — live-set id uniqueness

### 4.1 Why no exact theorem

The unconditional statement is false in the model:

```lean
theorem liveHtlcIdsNodup_unconditional_false :
    ¬ (∀ hs : List HTLCRecord, liveHtlcIdsNodup hs)
```

The proof instantiates a live local record with id `0` and a live remote record
with id `0`; `liveHtlcIds` is `[0, 0]`, so `Nodup` fails. This is not an
artificial model artifact: BOLT 2 assigns ids with one counter per sender, and
both counters start at 0. rust-lightning keeps `next_holder_htlc_id` and
`next_counterparty_htlc_id` separately. Therefore the protocol-faithful claim is
**per-direction** uniqueness, not global uniqueness. Even a per-sender counter
extension (as in `LnLean.Proofs.WaveD.D16`) proves per-direction uniqueness;
global uniqueness additionally needs a cross-direction disjointness assumption.

`addHTLC` also performs no id check. This is proved in the model module:

```lean
theorem addHTLC_same_id_distinct_amounts_ok :
    (addHTLC ⟨1000⟩ ⟨0⟩ 7 .local ⟨1⟩ ⟨ByteArray.empty⟩ 0).isOk = true ∧
      (addHTLC ⟨1000⟩ ⟨0⟩ 7 .local ⟨2⟩ ⟨ByteArray.empty⟩ 0).isOk = true
```

A theorem of the form "`Nodup` implies `Nodup`" was not added. The useful
content is the invariant and its preservation.

### 4.2 Added definitions

```lean
def htlcIds (hs : List HTLCRecord) : List Nat := hs.map HTLCRecord.id

def liveHtlcIds (hs : List HTLCRecord) : List Nat :=
  (htlcSet hs).map HTLCRecord.id

def liveHtlcIdsNodup (hs : List HTLCRecord) : Prop := (liveHtlcIds hs).Nodup
```

### 4.3 Added theorems

```lean
theorem mem_htlcIds_iff (x : Nat) (hs : List HTLCRecord) :
    x ∈ htlcIds hs ↔ ∃ h ∈ hs, h.id = x

theorem mem_liveHtlcIds_iff (x : Nat) (hs : List HTLCRecord) :
    x ∈ liveHtlcIds hs ↔ ∃ h ∈ htlcSet hs, h.id = x

theorem liveHtlcIds_subset_htlcIds (hs : List HTLCRecord) :
    ∀ x ∈ liveHtlcIds hs, x ∈ htlcIds hs

theorem liveHtlcIdsNodup_of_htlcIds_nodup (hs : List HTLCRecord)
    (hnd : (htlcIds hs).Nodup) : liveHtlcIdsNodup hs

theorem htlcSet_cons_live (h : HTLCRecord) (hs : List HTLCRecord)
    (hl : h.isLive = true) : htlcSet (h :: hs) = h :: htlcSet hs

theorem htlcSet_cons_not_live (h : HTLCRecord) (hs : List HTLCRecord)
    (hl : h.isLive = false) : htlcSet (h :: hs) = htlcSet hs

theorem liveHtlcIds_cons_live (h : HTLCRecord) (hs : List HTLCRecord)
    (hl : h.isLive = true) :
    liveHtlcIds (h :: hs) = h.id :: liveHtlcIds hs

theorem liveHtlcIds_cons_not_live (h : HTLCRecord) (hs : List HTLCRecord)
    (hl : h.isLive = false) : liveHtlcIds (h :: hs) = liveHtlcIds hs

theorem liveHtlcIdsNodup_add (h : HTLCRecord) (hs : List HTLCRecord)
    (hnd : liveHtlcIdsNodup hs) (hfresh : h.id ∉ liveHtlcIds hs) :
    liveHtlcIdsNodup (h :: hs)

theorem liveHtlcIdsNodup_filter (p : HTLCRecord → Bool)
    (hs : List HTLCRecord) (hnd : liveHtlcIdsNodup hs) :
    liveHtlcIdsNodup (hs.filter p)

theorem liveHtlcIdsNodup_removeId (id : Nat) (hs : List HTLCRecord)
    (hnd : liveHtlcIdsNodup hs) :
    liveHtlcIdsNodup (hs.filter (fun h => decide (h.id ≠ id)))

theorem eq_of_id_eq_of_htlcIds_nodup {l : List HTLCRecord}
    (hnd : (l.map HTLCRecord.id).Nodup) :
    ∀ h1 ∈ l, ∀ h2 ∈ l, h1.id = h2.id → h1 = h2

theorem liveHtlcIdsNodup_unique (hs : List HTLCRecord)
    (hnd : liveHtlcIdsNodup hs) :
    ∀ h1 ∈ htlcSet hs, ∀ h2 ∈ htlcSet hs, h1.id = h2.id → h1 = h2

theorem addHTLC_id (maxHtlcValue currentTotal : Msat) (id : Nat)
    (dir : Direction) (amount : Msat) (ph : PaymentHash) (cltv : Height)
    (h : HTLCRecord)
    (ok : addHTLC maxHtlcValue currentTotal id dir amount ph cltv = .ok h) :
    h.id = id

theorem addHTLC_isLive (maxHtlcValue currentTotal : Msat) (id : Nat)
    (dir : Direction) (amount : Msat) (ph : PaymentHash) (cltv : Height)
    (h : HTLCRecord)
    (ok : addHTLC maxHtlcValue currentTotal id dir amount ph cltv = .ok h) :
    h.isLive = true

theorem liveHtlcIdsNodup_addHTLC
    (maxHtlcValue currentTotal : Msat) (id : Nat) (dir : Direction)
    (amount : Msat) (ph : PaymentHash) (cltv : Height)
    (h : HTLCRecord) (hs : List HTLCRecord)
    (ok : addHTLC maxHtlcValue currentTotal id dir amount ph cltv = .ok h)
    (hnd : liveHtlcIdsNodup hs) (hfresh : id ∉ liveHtlcIds hs) :
    liveHtlcIdsNodup (h :: hs)

theorem addHTLC_same_id_distinct_amounts_ok :
    (addHTLC ⟨1000⟩ ⟨0⟩ 7 .local ⟨1⟩ ⟨ByteArray.empty⟩ 0).isOk = true ∧
      (addHTLC ⟨1000⟩ ⟨0⟩ 7 .local ⟨2⟩ ⟨ByteArray.empty⟩ 0).isOk = true

theorem liveHtlcIdsNodup_unconditional_false :
    ¬ (∀ hs : List HTLCRecord, liveHtlcIdsNodup hs)
```

### 4.4 Proof approach

* `htlcSet_cons_live` / `htlcSet_cons_not_live` are the two cases of the
  `List.filter` cons rule, using the `Bool` value of `h.isLive`.
* `liveHtlcIdsNodup_add` case-splits on whether the added record is live. In
  the live case it is `List.nodup_cons`; in the non-live case the live set is
  unchanged (`liveHtlcIds_cons_not_live`), so no freshness is needed. This is
  the strongest insert invariant possible without a checked wrapper.
* `liveHtlcIdsNodup_filter` commutes the two filters (`List.filter_filter`),
  rewrites `isLive && p` to `p && isLive` by `Bool.and_comm`, and applies
  `List.filter_sublist.nodup` on the live set. Removal by id
  (`liveHtlcIdsNodup_removeId`) is the instance
  `p = fun h => decide (h.id ≠ id)`.
* `eq_of_id_eq_of_htlcIds_nodup` is induction on the list, mirroring the
  standard `Nodup` decomposition. `liveHtlcIdsNodup_unique` instantiates it on
  `htlcSet hs`.
* `liveHtlcIdsNodup_addHTLC` composes `addHTLC_id` with
  `liveHtlcIdsNodup_add`; this is the direct connection between the model's
  `addHTLC` and the live-id invariant. `addHTLC_isLive` is derived from the
  existing `addHTLC_state_local` / `addHTLC_state_remote`.
* The negative result evaluates `liveHtlcIds [a, b] = [0, 0]` by `decide` and
  contradicts `Nodup`.

No proof-only `addHTLCChecked` (from
`LnLean.Proofs.PhaseC2.HTLCUniqueIds`) is imported or referenced.

## 5. Verification

### 5.1 Lean checks

Run from `/home/ubuntu/ln-lean-repair` under the single-build lock,
`LEAN_NUM_THREADS=1`:

| Command | RC |
|---|---|
| `lake env lean LnLean/Channel/HTLC.lean` | 0 |
| `lake build LnLean.Channel.HTLC` | 0 (`✔ [9/9] Built LnLean.Channel.HTLC`) |
| `lake env lean LnLean/Proofs/WaveD/D15.lean` | 0 |
| `lake env lean LnLean/Proofs/WaveD/D16.lean` | 0 |
| `lake env lean LnLean/Proofs/PhaseC2/HTLCUniqueIds.lean` | 0 |
| `lake build LnLean.Channel.HTLCLaws` | 0 (`12 jobs`) |
| `lake build LnLean.Proofs.Channel.HTLCProps` | 0 (`10 jobs`) |

The prescribed `lake build -j1 LnLean.Channel.HTLC` is rejected by this
toolchain's Lake (`Lake version 5.0.0-src`, Lean 4.35.0: `error: unknown short
option '-j'`). The equivalent serial build without `-j1` was used and
succeeded. Only one Lean process was run at a time.

`grep` over `LnLean/Channel/HTLC.lean` for `sorry`, `axiom`, `admit`,
`native_decide`, `unsafe`, `implemented_by` returns no matches.

### 5.2 `#check` evidence

Scratch files were created in `/tmp/opencode/btc-lean` (outside the
repository):

* `/tmp/opencode/btc-lean/H01Check.lean` — `#check` for every declaration
  listed in §3.2–4.3. Result: RC 0, all names resolve in
  `LnLean.Channel`.
* `/tmp/opencode/btc-lean/H01Absent.lean` — `#check` for
  `LnLean.Channel.HTLC.amount_conservation` and
  `LnLean.Channel.HTLC.id_unique`. Result: RC 1 with
  `unknownIdentifier`, confirming that neither exact target exists (this is
  intentional; see §1 and §7).

### 5.3 Files changed

* `LnLean/Channel/HTLC.lean` (only Lean file touched)
* `agents/reports/H01-HTLC.md` (this report)

No git add/commit/push or branch operation was performed. Other dirty Lean
files shown by `git status` belong to other lanes and were not touched.

## 6. Model extension required for an exact target

### LN-HT-003

An exact `amount_conservation` needs a record that binds:

1. a `Balance` (or two `Msat` balances), a fee, and a `fundingValue`;
2. the current `List HTLCRecord` (or its live subset);
3. the invariant `balance.local + balance.remote + totalHtlcValue (htlcSet hs) = funding`
   (and, for the fee form, a relation between fee, trimmed value, and withheld
   second-stage fees).

`LnLean.Channel.Types.Channel` is close but not sufficient: its `htlcs` field is
`List HTLC` (the `Types.HTLC` record, which has no `id`), and it has no fee
field. `LnLean.Proofs.WaveD.D15` supplies a proof-level `commitmentOf` bridge
and the conditional theorem `waveD_d15_amount_conservation`; promoting the row
requires either adopting that commitment-level target or adding an equivalent
ledger record to the model. The arithmetic core needed by either route is
already proved here (`totalHtlcValue_partition`,
`htlcValue_conservation_of_ledger`,
`htlcOutputValue_add_secondStageFee`,
`secondStageFee_le_of_not_dust`).

### LN-HT-004

An exact `id_unique` needs one of:

1. a channel record with per-sender id counters and an invariant saying every
   live id is below its sender's counter, plus per-direction distinctness
   (`LnLean.Proofs.WaveD.D16`'s `HtlcBook` is exactly this proof-level model);
2. a state invariant carrying `liveHtlcIdsNodup` as a field of the channel
   record and transitions that preserve it; or
3. a **weaker per-direction catalog claim**: uniqueness inside one sender's id
   space, which is what BOLT 2 actually mandates.

Option 1 or 2 would still need a cross-direction disjointness assumption for
the *global* claim, because both senders start at id 0.

## 7. Promotion verdict

| Row | Verdict | Reasoning |
|---|---|---|
| `LN-HT-003` | **model-gap** (conditional-only at best) | No balance/fee/funding field or ledger record in `LnLean.Channel.HTLC`. The partition and ledger-relative identity are proved, but the exact claim is false without an explicit ledger invariant (checked counterexample in `D15`). Keep `status := .statementOnly`; do not point the row at a conditional theorem as if it were unconditional. |
| `LN-HT-004` | **model-gap** (unconditional form false) | `HTLCRecord` has no counter or distinctness field; `addHTLC` accepts a reused id; two live records with id 0 are constructible. The list invariants (fresh insert, filter/removal, uniqueness from `Nodup`) are proved, but they are hypotheses, not model guarantees. Keep `status := .statementOnly`, and consider rewording the claim to per-direction uniqueness or crediting `D16`'s counter model. |

No row is promotion-ready on this branch. The added theorems are sound,
`sorry`-free, and usable as the HTLC-level base for a future model extension.
