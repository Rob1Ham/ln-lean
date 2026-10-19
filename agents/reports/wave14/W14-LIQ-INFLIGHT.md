# W14-LIQ-INFLIGHT — directional pending-only in-flight repair

## 1. Lane and scope

**Lane:** `W14-LIQ-INFLIGHT` (Wave 14).
**Scope:** T2 / G02–G04 from `agents/reports/wave13-review/R32-synthesis.md`
§4 T2 and the Wave-13 review rows `REV-01` in `docs/OPEN-ISSUES.md`.
**Base:** `a331b71`, branch `wave-14/16`, worktree `/home/ubuntu/ln-lean-waveh`.

The lane adds a directional, pending-only in-flight carrier:

* `pendingHtlcValueInDirection` sums only `offered`/`received` HTLCs in one
  direction; terminal `fulfilled`/`failed`/`removed` entries are excluded.
* `WithinInFlightDirectional` is the BOLT 2 directional cap test.
* `AffordableAddDirectional` combines that cap with the existing correct
  positive-amount, `cltv_expiry`, `htlc_minimum_msat`, offered-balance, and
  receiver-reserve guards.  It reuses `State.offeringReserveSat`; it does not
  introduce or duplicate the separate reserve-direction repair.

No existing definition was changed.

## 2. Owned files

* `LnLean/Proofs/Wave14/LiquidityInFlight.lean`
* `agents/reports/wave14/W14-LIQ-INFLIGHT.md`

No other file was edited.

## 3. Headline definitions and theorems

All names are in namespace
`LnLean.Proofs.Wave14.LiquidityInFlight`.

### 3.1 `pendingHtlcValueInDirection`

```lean
def pendingHtlcValueInDirection (c : Channel) (dir : Direction) : Nat :=
  pendingHtlcValueInDirectionList dir c.htlcs
```

with

```lean
def pendingHtlcValueInDirectionList (dir : Direction) (hs : List HTLC) : Nat :=
  ((hs.filter (fun h =>
      (h.state = HTLCState.offered ∨ h.state = HTLCState.received) ∧
      h.direction = dir)).map
    (fun h => h.amount.val)).sum
```

`dir` is the offering direction: `.local` means the local endpoint offered
the HTLC; `.remote` means the remote endpoint offered it.

### 3.2 `WithinInFlightDirectional`

```lean
def WithinInFlightDirectional (c : Channel) (dir : Direction)
    (amount : Msat) : Prop :=
  pendingHtlcValueInDirection c dir + amount.val ≤
    (receiverParams c dir).maxHtlcValue.val
```

`receiverParams c dir` is the endpoint receiving the offered HTLC, exactly as
in the existing `AffordableAdd` carrier.

### 3.3 `AffordableAddDirectional`

```lean
structure AffordableAddDirectional (c : Channel) (dir : Direction)
    (amount : Msat) (cltvExpiry : Height) : Prop where
  positive : 0 < amount.val
  cltvBelowMaximum : cltvExpiry < MAX_CLTV_EXPIRY
  atLeastHtlcMinimum : (receiverParams c dir).htlcMinimum.val ≤ amount.val
  fitsOffered : amount.val ≤ (offeredBalance c dir).val
  leavesReserve :
    offeringReserveSat c dir * Msat.MSAT_PER_SAT + amount.val ≤
      (offeredBalance c dir).val
  withinInFlightDirectional : WithinInFlightDirectional c dir amount
```

The reserve field is the already-correct receiver-advertised side
(`State.offeringReserveSat`).  This lane did not add a reserve definition.

### 3.4 `directional_inFlight_separates` (G02)

```lean
theorem directional_inFlight_separates :
    ∃ (c : Channel) (dir : Direction) (amount : Msat),
      WithinInFlightDirectional c dir amount ∧
      ¬ (pendingHtlcValueOf c + amount.val ≤
          (receiverParams c dir).maxHtlcValue.val)
```

### 3.5 `terminal_htlc_excluded_witness` (G03)

```lean
theorem terminal_htlc_excluded_witness :
    ∃ (c : Channel) (amount : Msat),
      WithinInFlightDirectional c .local amount ∧
      ¬ (LnLean.Proofs.Payment.sumByDirection .local c.htlcs + amount.val ≤
          (receiverParams c .local).maxHtlcValue.val)
```

### 3.6 `directionalAdmission_separates_pooled` (strict full-guard separation)

```lean
theorem directionalAdmission_separates_pooled :
    ∃ (c : Channel) (dir : Direction) (amount : Msat) (cltv : Height),
      AffordableAddDirectional c dir amount cltv ∧
      ¬ AffordableAdd c dir amount cltv
```

### 3.7 `updateAddHtlc_preserves_directionalCap`

```lean
theorem updateAddHtlc_preserves_directionalCap
    (c : Channel) (dir : Direction) (amount : Msat) (ph : PaymentHash)
    (cltv : Height) (h : AffordableAddDirectional c dir amount cltv) :
    pendingHtlcValueInDirection (updateAddHtlc c dir amount ph cltv) dir ≤
      (receiverParams c dir).maxHtlcValue.val
```

Supporting append facts:

```lean
theorem pendingHtlcValueInDirection_updateAddHtlc_same
    (c : Channel) (dir : Direction) (amount : Msat) (ph : PaymentHash)
    (cltv : Height) :
    pendingHtlcValueInDirection (updateAddHtlc c dir amount ph cltv) dir =
      pendingHtlcValueInDirection c dir + amount.val

theorem pendingHtlcValueInDirection_updateAddHtlc_other
    (c : Channel) (dir dir' : Direction) (amount : Msat) (ph : PaymentHash)
    (cltv : Height) (hne : dir' ≠ dir) :
    pendingHtlcValueInDirection (updateAddHtlc c dir amount ph cltv) dir' =
      pendingHtlcValueInDirection c dir'
```

### 3.8 Compatibility with the old pooled predicate

```lean
theorem pendingHtlcValueInDirection_le_pendingHtlcValueOf
    (c : Channel) (dir : Direction) :
    pendingHtlcValueInDirection c dir ≤ pendingHtlcValueOf c

theorem affordableAdd_toDirectional {c : Channel} {dir : Direction}
    {amount : Msat} {cltvExpiry : Height}
    (h : AffordableAdd c dir amount cltvExpiry) :
    AffordableAddDirectional c dir amount cltvExpiry
```

The old `AffordableAdd` therefore implies the new directional guard.  The
separation theorem above shows the converse fails on a concrete state.  The old
pooled predicate is **conservative but not BOLT-2-faithful**; it is retained
with its existing meaning.

## 4. Concrete non-vacuity witnesses

### 4.1 G02: remote pending 600, local add 500, cap 1000

`separationChannel` is

* local endpoint: reserve 0, in-flight cap 0 (irrelevant for a local offer);
* remote endpoint: reserve 0, in-flight cap 1000;
* local balance 1000 msat, remote balance 700 msat;
* `htlcs = [remote 600 received]`.

Then:

* `separationChannel_pending_local : pendingHtlcValueInDirection
  separationChannel .local = 0`;
* `separationChannel_pending_pooled : pendingHtlcValueOf separationChannel =
  600`;
* `directional_inFlight_separates` uses `separationChannel`, `.local`,
  `⟨500⟩`: directional accepts (`0 + 500 ≤ 1000`), pooled rejects
  (`600 + 500 > 1000`).

`directional_witness_affordable` proves the **full** new guard for the same
state, and `directionalAdmission_separates_pooled` uses it to show that the old
`AffordableAdd` rejects the same add.  This establishes both non-vacuity and a
strict separation, not merely a hypothesis restatement.

### 4.2 G03: settled 600 excluded, local add 500, cap 1000

`terminalChannel` is identical except that its HTLC is
`local 600 fulfilled`.

Then:

* `terminalChannel_pending_local : pendingHtlcValueInDirection
  terminalChannel .local = 0`;
* `terminalChannel_sumByDirection_local :
  LnLean.Proofs.Payment.sumByDirection .local terminalChannel.htlcs = 600`;
* `terminal_htlc_excluded_witness` accepts under the directional/pending-only
  rule (`0 + 500 ≤ 1000`) while rejecting under the old state-blind
  `sumByDirection` total (`600 + 500 > 1000`).

`terminal_witness_affordable` shows the full new guard is also inhabited for
this state.

### 4.3 Post-add value

`separationChannel_after_add_value` applies the preservation arithmetic to the
concrete state:

```lean
pendingHtlcValueInDirection
    (updateAddHtlc separationChannel .local ⟨500⟩ ⟨ByteArray.empty⟩ 0)
    .local = 500
```

## 5. Build command and result

```sh
cd /home/ubuntu/ln-lean-waveh
export PATH=/dev/shm/btc/elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
LEAN_NUM_THREADS=1 flock -w 3600 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Proofs.Wave14.LiquidityInFlight
```

Result:

```
ℹ [16/16] Built LnLean.Proofs.Wave14.LiquidityInFlight (755ms)
Build completed successfully (16 jobs).
```

There are no warnings and no `sorry`, `admit`, `axiom` declaration,
`native_decide`, `unsafe`, or `@[implemented_by]`.

## 6. `#print axioms` output

The module ends with the following commands:

```lean
#print axioms pendingHtlcValueInDirection_le_pendingHtlcValueOf
#print axioms affordableAdd_toDirectional
#print axioms directional_inFlight_separates
#print axioms terminal_htlc_excluded_witness
#print axioms directionalAdmission_separates_pooled
#print axioms updateAddHtlc_preserves_directionalCap
```

Build output:

```
'LnLean.Proofs.Wave14.LiquidityInFlight.pendingHtlcValueInDirection_le_pendingHtlcValueOf'
  depends on axioms: [propext, Quot.sound]
'LnLean.Proofs.Wave14.LiquidityInFlight.affordableAdd_toDirectional'
  depends on axioms: [propext, Quot.sound]
'LnLean.Proofs.Wave14.LiquidityInFlight.directional_inFlight_separates'
  depends on axioms: [propext, Quot.sound]
'LnLean.Proofs.Wave14.LiquidityInFlight.terminal_htlc_excluded_witness'
  depends on axioms: [propext, Quot.sound]
'LnLean.Proofs.Wave14.LiquidityInFlight.directionalAdmission_separates_pooled'
  depends on axioms: [propext, Quot.sound]
'LnLean.Proofs.Wave14.LiquidityInFlight.updateAddHtlc_preserves_directionalCap'
  depends on axioms: [propext, Quot.sound]
```

Every result is within the permitted
`propext` / `Quot.sound` / `Classical.choice` set; `Classical.choice` is not
needed.  The witnesses `directional_witness_affordable` and
`terminal_witness_affordable` are ordinary definitions/terms and introduce no
axioms.

## 7. Review gap closed or narrowed

* **G02 (directional in-flight cap): closed on the additive carrier.**  The new
  directional, pending-only predicate has a concrete state where it accepts
  and the old pooled predicate rejects.  `affordableAdd_toDirectional` records
  the conservative direction of the old predicate.
* **G03 (terminal HTLCs counted): narrowed with a witness.**  The new sum
  excludes `fulfilled`/`failed`/`removed` entries; the concrete terminal
  witness separates it from the old state-blind `sumByDirection`.  The old
  `LiquidityProps.sumByDirection` definition is deliberately untouched and
  still counts terminal entries.
* **G04 (full BOLT 2 add guard): narrowed.**  `AffordableAddDirectional`
  carries the positive-amount, CLTV, `htlc_minimum_msat`, offered-balance,
  reserve, and directional in-flight guards in one predicate, and
  `updateAddHtlc_preserves_directionalCap` proves the cap is preserved after
  `Channel.updateAddHtlc`.

What remains external or narrow:

* The existing consumers are **not silently changed**.  `AffordableAdd`,
  `AffordableAdd.withinInFlight`, `pendingHtlcValueOf`,
  `LiquidityProps.sumByDirection`, `LiquidityProps.addHtlc?`,
  `WaveD.D14.inFlightMsat`, and `WaveE.E37.pendingValue` keep their old
  meaning.  In particular `addHtlc?` still counts terminal HTLCs and still
  omits the positive/CLTV/minimum guards.  Any production consumer must be
  switched to `AffordableAddDirectional` by an integrator or a later lane.
* `AffordableAddDirectional` is a pre-state predicate; it is not a new
  `UpdateStep` constructor.  Adding a constructor to the existing relation
  would change an existing inductive and is outside this lane's ownership.
* The carrier is the `Channel` record only: no wire encoding, no commitment
  round, no fee/dust deduction, and no `max_accepted_htlcs` counter.
* The reserve-endpoint direction (G01 / the separate `W14-LIQ-RESERVE` lane) is
  not addressed here.  This module uses the already-correct
  `State.offeringReserveSat`.
* No LDK capacity equality is claimed.  The directional cap is a value cap on
  the model record, not a full `get_available_balances_for_scope` equality.

## 8. Shared-file changes for the integrator

Not applied by this lane:

1. Regenerate the root with `scripts/regen-root.sh` so that
   `LnLean.Proofs.Wave14.LiquidityInFlight` is imported by `LnLean.lean`.
2. Add audit entries / `#print axioms` coverage for the six headline names
   listed in §6 in `LnLean/Proofs/PhaseC3/AxiomAudit.lean` and the registry,
   as required by the assurance lane.
3. Update the `AffordableAdd` docstring in `LnLean/Channel/State.lean` to say
   that its pooled `withinInFlight` is *conservative but not BOLT-2-faithful*
   and that `AffordableAddDirectional` is the directional replacement.  This
   lane did not edit that shared file.
4. Optionally add a catalog/docs row for the additive carrier.  Do not
   replace `pendingHtlcValueOf`, `AffordableAdd.withinInFlight`,
   `LiquidityProps.sumByDirection`, `D14.inFlightMsat`, or
   `E37.pendingValue`; all retained counterexamples still depend on them.
5. If the project wants the new guard to be a protocol transition, add a
   separate adapter theorem or a new relation; do not add a constructor to the
   existing `UpdateStep` without reviewing its preservation theorems.

## 9. Ownership confirmation

Only the two owned files were created/modified:

* `LnLean/Proofs/Wave14/LiquidityInFlight.lean`
* `agents/reports/wave14/W14-LIQ-INFLIGHT.md`

No shared file (`LnLean.lean`, `lakefile.lean`, `scripts/check-final.py`,
`AxiomAudit.lean`, `Traceability.lean`, `Obligations.lean`, docs, catalog,
vendor, refs) and no other lane's module or report was edited.  No Git write
command was run.
