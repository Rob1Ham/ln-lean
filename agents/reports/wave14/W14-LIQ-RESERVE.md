# W14-LIQ-RESERVE — additive reserve-direction repair

**Lane:** W14-LIQ-RESERVE (Wave 14)
**Worktree:** `/home/ubuntu/ln-lean-waveh`
**Branch:** `wave-14/16`
**Base:** `a331b71`
**Status:** complete; scoped build green.

## 1. Scope

Implement the additive reserve-direction repair from R32 §4 T1 / gap G01
(`REV-01`) **without changing any existing declaration**. The legacy carrier
`LnLean.Proofs.Payment.LiquidityProps.reserveMsat` reads the local endpoint's
advertised `channel_reserve_satoshis`. Under BOLT 2 that field is the reserve
the *peer* must keep, so the legacy reading is inverted for local outbound
(`refs/bolts/02-peer-protocol.md:730-741`, `:884-887`; LDK datapoint D1,
`refs/rust-lightning/lightning/src/ln/channel.rs:6552-6605`).

This lane adds corrected reserve and capacity functions, proves the legacy
reading auditable, and proves a concrete separation witness. It does not
redefine `reserveMsat`, `remoteReserveMsat`, `reserveOf`, `MeetsReserve`,
`availableOutbound`, `planFits`, or `addHtlc?`. It also does not add an
admission function: the directional in-flight / full-guard repair is the
separate `W13-LIQ` in-flight lane, and this module deliberately stays on the
reserve direction.

## 2. Owned files

Only these files were created or modified:

- `LnLean/Proofs/Wave14/LiquidityReserve.lean`
- `agents/reports/wave14/W14-LIQ-RESERVE.md`

No shared file, root import, audit file, catalog file, script, docs file, or
other lane's Lean module/report was edited.

## 3. Headline definitions and exact statements

All declarations live in namespace
`LnLean.Proofs.Wave14.LiquidityReserve` and import
`LnLean.Proofs.Payment.LiquidityProps` (which supplies `Channel`,
`ChannelParams`, `Msat`, `Direction`, `reserveMsat`, `availableOutbound`, and
`outboundLiquidity`).

```lean
def localReserveMsat (c : Channel) : Nat :=
  c.remoteEndpoint.params.channelReserveSat * Msat.MSAT_PER_SAT

def remoteReserveMsatCorrected (c : Channel) : Nat :=
  c.localEndpoint.params.channelReserveSat * Msat.MSAT_PER_SAT

def availableOutboundCorrected (c : Channel) : Nat :=
  outboundLiquidity c - localReserveMsat c

def availableInboundCorrected (c : Channel) : Nat :=
  inboundLiquidity c - remoteReserveMsatCorrected c
```

The actual reserve field is `ChannelParams.channelReserveSat : Nat` (a
satoshi value), so the sketch in R32 §4 T1 matches the declarations exactly;
no type adaptation was needed. Both corrected capacity functions return `Nat`
in millisatoshis, matching `availableOutbound`/`availableInbound`.

Headline theorems:

```lean
theorem reserveMsat_eq_localEndpoint (c : Channel) :
    reserveMsat c =
      c.localEndpoint.params.channelReserveSat * Msat.MSAT_PER_SAT

theorem availableOutboundCorrected_eq_availableOutbound_of_reserve_eq
    (c : Channel)
    (h : c.localEndpoint.params.channelReserveSat =
      c.remoteEndpoint.params.channelReserveSat) :
    availableOutboundCorrected c = availableOutbound c

theorem availableOutboundCorrected_le_outboundLiquidity (c : Channel) :
    availableOutboundCorrected c ≤ outboundLiquidity c

theorem availableInboundCorrected_le_inboundLiquidity (c : Channel) :
    availableInboundCorrected c ≤ inboundLiquidity c
```

```lean
theorem reserve_direction_separates :
    ∃ c : Channel,
      c.localEndpoint.params.channelReserveSat = 0 ∧
      c.remoteEndpoint.params.channelReserveSat = 1 ∧
      reserveMsat c = 0 ∧
      localReserveMsat c = Msat.MSAT_PER_SAT ∧
      availableOutbound c = 1000 ∧
      availableOutboundCorrected c = 0

theorem corrected_outbound_nonempty :
    ∃ c : Channel,
      localReserveMsat c = 0 ∧
      remoteReserveMsatCorrected c = 0 ∧
      availableOutboundCorrected c = 1000 ∧
      0 < availableOutboundCorrected c
```

`reserveMsat_eq_localEndpoint` is definitional (`rfl`); it makes the inverted
legacy side explicit so the old carrier is auditable rather than silently
reinterpreted. `availableOutboundCorrected_eq_availableOutbound_of_reserve_eq`
shows the repair changes only direction: on a symmetric channel the corrected
and legacy values coincide.

**Upper-bound boundary (explicit in the module docstring and in the two bound
theorems).** `availableOutboundCorrected` subtracts exactly one reserve. It
still omits BOLT 3 commitment fees, anchor output values, dust exposure, and
in-flight HTLC value, so it is an upper bound on spendable outbound capacity,
not LDK's `outbound_capacity_msat` equality. The same boundary applies to
`availableInboundCorrected`.

## 4. Concrete non-vacuity witness and the theorem that uses it

Witness definition:

```lean
def witnessChannel (localReserveSat remoteReserveSat localBalanceMsat
    remoteBalanceMsat : Nat) : Channel
```

It builds a `Channel` with the requested endpoint reserves and balances, no
HTLCs, phase `normal`, both commitment counters 0, and empty byte-array
identifiers/keys.

Witness A: `witnessChannel 0 1 1000 0`

- local endpoint advertised reserve 0 sat, remote endpoint advertised reserve
  1 sat;
- local balance 1000 msat, remote balance 0 msat, `htlcs = []`;
- hence legacy `reserveMsat = 0`, `availableOutbound = 1000`;
- corrected `localReserveMsat = 1 * 1000 = 1000`,
  `availableOutboundCorrected = 1000 - 1000 = 0`.

This is exactly the required separation: the legacy reading reports 1000 msat
spendable, the BOLT-2-direction reading reports 0. It is the witness for
`reserve_direction_separates` (closed by `decide`).

Witness B: `witnessChannel 0 0 1000 0`

- both advertisements 0 sat, local balance 1000 msat, no HTLCs;
- `localReserveMsat = 0`, `remoteReserveMsatCorrected = 0`,
  `availableOutboundCorrected = 1000 > 0`.

It is the witness for `corrected_outbound_nonempty`, showing the corrected
capacity/predicate is inhabited and positive rather than vacuously always
zero.

## 5. Build command and result

```sh
cd /home/ubuntu/ln-lean-waveh
export PATH=/dev/shm/btc/elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
LEAN_NUM_THREADS=1 flock -w 3600 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Proofs.Wave14.LiquidityReserve
```

Result:

```text
ℹ [16/16] Built LnLean.Proofs.Wave14.LiquidityReserve (661ms)
Build completed successfully (16 jobs).
```

No `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, or
`@[implemented_by]` occurs in the module. Only the scoped module build was
run; no bare `lake build`, full gate, or network command was run.

## 6. `#print axioms` output

The module ends with the following commands:

```lean
#print axioms reserveMsat_eq_localEndpoint
#print axioms availableOutboundCorrected_eq_availableOutbound_of_reserve_eq
#print axioms availableOutboundCorrected_le_outboundLiquidity
#print axioms availableInboundCorrected_le_inboundLiquidity
#print axioms reserve_direction_separates
#print axioms corrected_outbound_nonempty
```

Build output:

```text
info: LnLean/Proofs/Wave14/LiquidityReserve.lean:226:0: 'LnLean.Proofs.Wave14.LiquidityReserve.reserveMsat_eq_localEndpoint' does not depend on any axioms
info: LnLean/Proofs/Wave14/LiquidityReserve.lean:227:0: 'LnLean.Proofs.Wave14.LiquidityReserve.availableOutboundCorrected_eq_availableOutbound_of_reserve_eq' does not depend on any axioms
info: LnLean/Proofs/Wave14/LiquidityReserve.lean:228:0: 'LnLean.Proofs.Wave14.LiquidityReserve.availableOutboundCorrected_le_outboundLiquidity' does not depend on any axioms
info: LnLean/Proofs/Wave14/LiquidityReserve.lean:229:0: 'LnLean.Proofs.Wave14.LiquidityReserve.availableInboundCorrected_le_inboundLiquidity' does not depend on any axioms
info: LnLean/Proofs/Wave14/LiquidityReserve.lean:230:0: 'LnLean.Proofs.Wave14.LiquidityReserve.reserve_direction_separates' does not depend on any axioms
info: LnLean/Proofs/Wave14/LiquidityReserve.lean:231:0: 'LnLean.Proofs.Wave14.LiquidityReserve.corrected_outbound_nonempty' does not depend on any axioms
```

All six audited declarations are axiom-free, within the allowed
`propext` / `Quot.sound` / `Classical.choice` set.

## 7. Review gap closed or narrowed

**G01 / `REV-01`, reserve-direction half — narrowed, not fully closed.**

- The correct BOLT 2 reserve direction now exists as named, documented
  definitions (`localReserveMsat`, `remoteReserveMsatCorrected`) and as
  corrected outbound/inbound capacities.
- The legacy inverted reading is made auditable by
  `reserveMsat_eq_localEndpoint`.
- `reserve_direction_separates` records the live defect with a concrete
  channel: legacy outbound 1000 msat versus corrected outbound 0 msat when the
  peer advertises a 1-sat reserve.
- `corrected_outbound_nonempty` proves the corrected value is inhabited and
  positive.

**What remains narrow / external:**

- `addHtlc?`, `reserveOf .local`, `MeetsReserve`, `availableOutbound`, and
  `planFits` still use the inverted legacy reserve. A consumer must explicitly
  switch to the `*Corrected` names; no existing consumer is rewired by this
  additive module.
- No corrected admission predicate is added here. Removing the live unsound
  acceptance (the 1000-msat `addHtlc?` acceptance in the witness channel)
  requires the in-flight/full-guard lane or a follow-up consumer change that
  uses these corrected values.
- The corrected quantities remain upper bounds: fees, anchors, dust, and
  in-flight value are omitted. No LDK capacity equality is claimed.
- The inbound direction is defined and bounded but is not exercised by a
  separation witness; G01's reported counterexample is the outbound one.

## 8. Shared-file changes for the integrator (stated, not applied)

1. **Root import:** add
   `import LnLean.Proofs.Wave14.LiquidityReserve` through the Wave 14
   aggregator / `scripts/regen-root.sh`. This lane did not edit `LnLean.lean`.
2. **Axiom audit registry:** if Wave 14 headlines are enrolled in
   `LnLean/Proofs/PhaseC3/AxiomAudit.lean`, add these six names and matching
   `#print axioms` lines:
   `reserveMsat_eq_localEndpoint`,
   `availableOutboundCorrected_eq_availableOutbound_of_reserve_eq`,
   `availableOutboundCorrected_le_outboundLiquidity`,
   `availableInboundCorrected_le_inboundLiquidity`,
   `reserve_direction_separates`,
   `corrected_outbound_nonempty`.
   Expected audit result: no axioms.
3. **Catalog / docs:** update the `REV-01` row (and any catalog row that cites
   `reserveMsat`/`availableOutbound` as BOLT-2-faithful) to point at
   `LnLean.Proofs.Wave14.LiquidityReserve` and to state that the legacy
   carriers remain inverted until consumers switch.
4. **Docstring correction in the existing module (recommended, not applied):**
   `LiquidityProps.reserveMsat` should eventually carry a docstring saying its
   reserve side is inverted/legacy and pointing at `localReserveMsat`. Per the
   ownership contract this lane did not edit `LiquidityProps.lean`.

## 9. Ownership confirmation

No shared or other-lane file was edited. Only the two owned paths in §2 were
written. No `git add`, `git commit`, `git push`, `git switch`, or other Git
write command was run. No network command was run.
